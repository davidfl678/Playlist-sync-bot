#!/usr/bin/env python3
"""Synchronize new YouTube playlist entries to music-service playlists.

The program is intentionally headless. Configuration and credentials come from
environment variables (or a local .env file for development), and durable state
is written atomically to ``synced_history.json``.

Important compatibility notes:
* YouTube playlist discovery uses yt-dlp without an API key first, then falls
  back automatically to YouTube Data API v3 when yt-dlp fails or returns empty.
* Spotify ``sp_dc`` authentication uses Spotify's private Web Player flow. The
  Web Player's rotating TOTP material is discovered from its current JavaScript
  bundle instead of being hardcoded.
* Audiomack's documented write API uses OAuth 1.0a. For compatibility with the
  requested configuration, ``AUDIOMACK_TOKEN`` is also tried as a web-session
  bearer/cookie token, but OAuth 1.0a environment variables are strongly
  preferred (see ``AudiomackClient``).
* Deezer support uses the unofficial ARL-authenticated Pipe GraphQL client and
  is optional by design.
"""

from __future__ import annotations

import ast
import asyncio
import hashlib
import hmac
import html
import json
import logging
import os
import re
import struct
import time
import unicodedata
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from email.utils import parsedate_to_datetime
from pathlib import Path
from threading import Lock
from typing import Any, Iterable, Mapping, Sequence
from urllib.parse import unquote, urljoin, urlparse

import requests
from dotenv import load_dotenv
from rapidfuzz import fuzz
from requests import Response
from requests_oauthlib import OAuth1

load_dotenv()

LOG = logging.getLogger("playlist_sync")
HISTORY_PATH = Path(os.getenv("SYNC_HISTORY_PATH", "synced_history.json"))
DEFAULT_YT_PLAYLIST_ID = "PLUZA3HbIj2IfyaRs6YrcctsjQO8vPCUHE"
DEFAULT_SOUNDCLOUD_CLIENT_ID = "KKzJxmw11tYpCs6T24P4uUYhqmjalG6M"
SUCCESS_STATUSES = frozenset({"synced", "already_present"})


# ---------------------------------------------------------------------------
# Exceptions and common data structures
# ---------------------------------------------------------------------------


class SyncError(RuntimeError):
    """Base class for controlled, safe-to-log synchronization errors."""


class ConfigurationError(SyncError):
    """Raised when required configuration is absent or malformed."""


class AuthenticationError(SyncError):
    """Raised for an expired/rejected cookie, token, or API credential."""


class PlatformAPIError(SyncError):
    """Raised for a non-authentication platform API failure."""


class RateLimitError(PlatformAPIError):
    """Raised after bounded HTTP 429 retries have been exhausted."""

    def __init__(self, platform: str, retry_after: float | None = None) -> None:
        self.platform = platform
        self.retry_after = retry_after
        detail = (
            f"; server requested another {retry_after:.0f}s delay"
            if retry_after is not None
            else ""
        )
        super().__init__(f"{platform}: rate limit persisted after retries{detail}")


def environment_value(*names: str, default: str = "") -> str:
    """Return the first non-empty normalized environment value.

    GitHub emits an empty string for an unavailable secret. This helper also
    tolerates accidental surrounding whitespace, UTF-8 BOMs, and a single pair
    of quotes copied into a secret value. Credential contents are never logged.
    """

    for name in names:
        raw = os.getenv(name)
        if raw is None:
            continue
        value = raw.lstrip("\ufeff").strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
            value = value[1:-1].strip()
        if value and value.casefold() not in {"none", "null", "undefined"}:
            return value
    return default.strip()


@dataclass(frozen=True, slots=True)
class SourceTrack:
    video_id: str
    original_title: str
    title: str
    artist: str
    position: int  # One-based YouTube playlist position.


@dataclass(frozen=True, slots=True)
class YouTubePageItem:
    """A playlist item used for cursor detection, optionally with usable metadata."""

    video_id: str
    position: int
    track: SourceTrack | None


@dataclass(frozen=True, slots=True)
class YouTubePage:
    items: tuple[YouTubePageItem, ...]
    next_page_token: str
    request_page_token: str


@dataclass(frozen=True, slots=True)
class SourceScan:
    """Result of an incremental YouTube source scan."""

    new_tracks: tuple[SourceTrack, ...]
    state: dict[str, Any]
    inspected_items: int
    mode: str
    state_changed: bool


@dataclass(frozen=True, slots=True)
class Candidate:
    target_id: str
    title: str
    artist: str
    uri: str = ""


@dataclass(frozen=True, slots=True)
class SyncResult:
    status: str
    target_id: str = ""
    score: float | None = None
    detail: str = ""


@dataclass(frozen=True, slots=True)
class Config:
    yt_api_key: str
    yt_playlist_id: str
    spotify_sp_dc: str
    spotify_playlist_id: str
    soundcloud_token: str
    soundcloud_client_id: str
    soundcloud_playlist_id: str
    audiomack_token: str
    audiomack_playlist_id: str
    deezer_arl: str
    deezer_playlist_id: str
    telegram_bot_token: str
    telegram_chat_id: str
    yt_start_index: int
    match_threshold: float

    @classmethod
    def from_environment(cls) -> "Config":
        try:
            start_index = max(1, int(environment_value("YT_START_INDEX", default="51")))
            threshold = min(
                100.0,
                max(0.0, float(environment_value("MATCH_THRESHOLD", default="78"))),
            )
        except ValueError as exc:
            raise ConfigurationError(
                "YT_START_INDEX must be an integer and MATCH_THRESHOLD must be numeric"
            ) from exc

        return cls(
            # YT_API_KEY remains a backward-compatible local alias; the GitHub
            # workflow uses the canonical YOUTUBE_API_KEY secret name.
            yt_api_key=environment_value("YOUTUBE_API_KEY", "YT_API_KEY"),
            yt_playlist_id=environment_value(
                "YT_PLAYLIST_ID", default=DEFAULT_YT_PLAYLIST_ID
            ),
            spotify_sp_dc=environment_value("SPOTIFY_SP_DC"),
            spotify_playlist_id=environment_value(
                "SPOTIFY_PLAYLIST_ID", default="1G84VxuubZb4cofjVmk40D"
            ),
            soundcloud_token=environment_value("SOUNDCLOUD_OAUTH_TOKEN"),
            soundcloud_client_id=environment_value(
                "SOUNDCLOUD_CLIENT_ID", default=DEFAULT_SOUNDCLOUD_CLIENT_ID
            ),
            soundcloud_playlist_id=environment_value("SOUNDCLOUD_PLAYLIST_ID"),
            audiomack_token=environment_value("AUDIOMACK_TOKEN"),
            audiomack_playlist_id=environment_value("AUDIOMACK_PLAYLIST_ID"),
            deezer_arl=environment_value("DEEZER_ARL", "DEEZER_ARL_TOKEN"),
            deezer_playlist_id=environment_value(
                "DEEZER_PLAYLIST_ID", "DEEZER_TARGET_PLAYLIST_ID"
            ),
            telegram_bot_token=environment_value("TELEGRAM_BOT_TOKEN"),
            telegram_chat_id=environment_value("TELEGRAM_CHAT_ID"),
            yt_start_index=start_index,
            match_threshold=threshold,
        )


# ---------------------------------------------------------------------------
# HTTP pacing, retries, and Telegram
# ---------------------------------------------------------------------------


class APIPacer:
    """Guarantee a minimum delay between outbound API request starts."""

    def __init__(self, delay_seconds: float = 2.0) -> None:
        self.delay_seconds = max(0.0, delay_seconds)
        self._last_request_at = 0.0
        self._lock = Lock()

    def wait(self) -> None:
        with self._lock:
            elapsed = time.monotonic() - self._last_request_at
            remaining = self.delay_seconds - elapsed
            if remaining > 0:
                time.sleep(remaining)
            self._last_request_at = time.monotonic()


class HTTPClient:
    """Small requests wrapper with pacing, bounded retries, and safe errors."""

    RETRYABLE_READ_STATUSES = frozenset({500, 502, 503, 504})

    def __init__(self, pacer: APIPacer) -> None:
        self.pacer = pacer
        self.session = requests.Session()
        self.session.headers.update(
            {
                "User-Agent": (
                    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/131.0 Safari/537.36"
                ),
                "Accept": "application/json",
            }
        )

    @staticmethod
    def _retry_after_seconds(value: str, fallback: float, maximum: float) -> float:
        if value:
            try:
                return min(max(float(value), 0.0), maximum)
            except ValueError:
                try:
                    requested_at = parsedate_to_datetime(value)
                    delay = requested_at.timestamp() - time.time()
                    return min(max(delay, 0.0), maximum)
                except (TypeError, ValueError, OverflowError):
                    pass
        return min(max(fallback, 0.0), maximum)

    def request(
        self,
        method: str,
        url: str,
        *,
        platform: str,
        expected: Iterable[int] | None = None,
        timeout: float = 30.0,
        retry_reads: bool = True,
        **kwargs: Any,
    ) -> Response:
        method = method.upper()
        expected_codes = set(expected or range(200, 300))
        can_retry_read = retry_reads and method in {"GET", "HEAD"}
        try:
            max_rate_limit_retries = max(
                0,
                int(environment_value("HTTP_429_RETRIES", default="3")),
            )
            maximum_retry_delay = max(
                1.0,
                float(environment_value("HTTP_MAX_RETRY_DELAY", default="60")),
            )
        except ValueError:
            max_rate_limit_retries = 3
            maximum_retry_delay = 60.0

        rate_limit_retries = 0
        read_retries = 0
        last_retry_after: float | None = None
        while True:
            self.pacer.wait()
            try:
                response = self.session.request(method, url, timeout=timeout, **kwargs)
            except (requests.Timeout, requests.ConnectionError) as exc:
                if can_retry_read and read_retries < 2:
                    read_retries += 1
                    time.sleep(min(2**read_retries, 8))
                    continue
                raise PlatformAPIError(
                    f"{platform}: network request failed after retries"
                ) from exc
            except requests.RequestException as exc:
                raise PlatformAPIError(f"{platform}: HTTP request could not be sent") from exc

            if response.status_code in expected_codes:
                return response
            if response.status_code in {401, 403}:
                raise AuthenticationError(
                    f"{platform}: authentication rejected (HTTP {response.status_code})"
                )
            if response.status_code == 429:
                fallback = 2 ** (rate_limit_retries + 1)
                last_retry_after = self._retry_after_seconds(
                    response.headers.get("Retry-After", ""),
                    fallback,
                    maximum_retry_delay,
                )
                if rate_limit_retries < max_rate_limit_retries:
                    rate_limit_retries += 1
                    LOG.warning(
                        "%s rate limited (HTTP 429); retry %d/%d in %.1fs",
                        platform,
                        rate_limit_retries,
                        max_rate_limit_retries,
                        last_retry_after,
                    )
                    time.sleep(last_retry_after)
                    continue
                raise RateLimitError(platform, last_retry_after)
            if (
                response.status_code in self.RETRYABLE_READ_STATUSES
                and can_retry_read
                and read_retries < 2
            ):
                read_retries += 1
                time.sleep(min(2**read_retries, 8))
                continue
            raise PlatformAPIError(
                f"{platform}: API request failed (HTTP {response.status_code})"
            )

    @staticmethod
    def json(response: Response, platform: str) -> Any:
        try:
            return response.json()
        except (ValueError, requests.JSONDecodeError) as exc:
            raise PlatformAPIError(f"{platform}: API returned invalid JSON") from exc


try:
    _delay = float(environment_value("API_DELAY_SECONDS", default="2"))
except ValueError:
    _delay = 2.0
PACER = APIPacer(_delay)
HTTP = HTTPClient(PACER)


def send_telegram_alert(message: str) -> bool:
    """Send a best-effort Telegram message without ever exposing credentials."""

    token = environment_value("TELEGRAM_BOT_TOKEN")
    chat_id = environment_value("TELEGRAM_CHAT_ID")
    if not token or not chat_id:
        LOG.error("Telegram alert skipped: TELEGRAM_BOT_TOKEN/CHAT_ID not configured")
        return False

    # Telegram limits sendMessage text to 4096 characters.
    text = message[:4000]
    try:
        HTTP.request(
            "POST",
            f"https://api.telegram.org/bot{token}/sendMessage",
            platform="Telegram",
            expected={200},
            retry_reads=False,
            data={"chat_id": chat_id, "text": text, "disable_web_page_preview": True},
        )
        return True
    except SyncError as exc:
        LOG.error("Telegram alert delivery failed: %s", exc)
        return False


# ---------------------------------------------------------------------------
# Metadata cleanup and fuzzy matching
# ---------------------------------------------------------------------------


_NOISE_TERM = re.compile(
    r"(?ix)\b(?:"
    r"official\s+(?:music\s+)?(?:video|audio|visuali[sz]er)|"
    r"official\s+lyrics?|lyrics?\s+video|music\s+video|"
    r"visuali[sz]er|audio\s+only|mv|m/v|4k|8k|uhd|full\s+hd|hd|"
    r"slowed(?:\s*(?:\+|and|&)?\s*reverb)?|sped\s*up|nightcore|"
    r"clean\s+version|explicit\s+version"
    r")\b"
)
_BRACKETED = re.compile(r"[\[(]([^\])]{1,100})[\])]")
_TITLE_SEPARATOR = re.compile(r"\s+[\-–—]\s+", re.UNICODE)


def _remove_noisy_bracket(match: re.Match[str]) -> str:
    return " " if _NOISE_TERM.search(match.group(1)) else match.group(0)


def clean_title(value: str) -> str:
    """Remove common upload/version noise while preserving meaningful mix names."""

    text = html.unescape(value or "")
    text = _BRACKETED.sub(_remove_noisy_bracket, text)
    text = _NOISE_TERM.sub(" ", text)
    text = re.sub(r"\s*[|•]\s*$", "", text)
    text = re.sub(r"\s{2,}", " ", text)
    return text.strip(" \t\r\n-|–—:()[]")


def clean_artist(value: str) -> str:
    text = html.unescape(value or "")
    text = re.sub(r"(?i)\s*-\s*topic\s*$", "", text)
    text = re.sub(r"(?i)(?:vevo|official)\s*$", "", text)
    return re.sub(r"\s{2,}", " ", text).strip(" -|–—")


def derive_track_metadata(video_title: str, owner_channel: str) -> tuple[str, str]:
    """Derive a useful artist/title pair from a YouTube playlist item."""

    title = clean_title(video_title)
    artist = clean_artist(owner_channel)
    parts = _TITLE_SEPARATOR.split(title, maxsplit=1)
    if len(parts) == 2 and 0 < len(parts[0]) <= 100 and parts[1]:
        artist_from_title = clean_artist(parts[0])
        if artist_from_title:
            artist = artist_from_title
            title = clean_title(parts[1])
    return title or clean_title(video_title), artist


def normalize_text(value: str) -> str:
    value = unicodedata.normalize("NFKD", html.unescape(value or "")).casefold()
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    value = re.sub(r"(?i)\b(?:feat(?:uring)?|ft)\.?\b", " ", value)
    value = re.sub(r"[^\w]+", " ", value, flags=re.UNICODE)
    return re.sub(r"\s+", " ", value).strip()


def candidate_score(source: SourceTrack, candidate: Candidate) -> float:
    source_title = normalize_text(source.title)
    target_title = normalize_text(candidate.title)
    title_score = float(fuzz.WRatio(source_title, target_title))
    if not source.artist or not candidate.artist:
        return title_score
    artist_score = float(
        fuzz.WRatio(normalize_text(source.artist), normalize_text(candidate.artist))
    )
    return (title_score * 0.78) + (artist_score * 0.22)


def choose_candidate(
    source: SourceTrack,
    candidates: Sequence[Candidate],
    threshold: float,
) -> tuple[Candidate | None, float | None]:
    if not candidates:
        return None, None
    scored = [(candidate_score(source, candidate), candidate) for candidate in candidates]
    score, candidate = max(scored, key=lambda item: item[0])
    if score < threshold:
        return None, round(score, 2)
    return candidate, round(score, 2)


def search_query(track: SourceTrack) -> str:
    return " ".join(part for part in (track.artist, track.title) if part).strip()


# ---------------------------------------------------------------------------
# Durable history (legacy-list compatible, partial-platform aware)
# ---------------------------------------------------------------------------


class HistoryStore:
    """Atomic JSON state with a completed-ID list and per-platform checkpoints."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.data: dict[str, Any] = {
            "schema_version": 3,
            "synced_video_ids": [],
            "tracks": {},
            "youtube_source_state": {},
        }
        self._completed: set[str] = set()

    def load(self) -> None:
        if not self.path.exists():
            LOG.info("History file not found; initializing an empty history")
            self.save()
            return
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            # Resetting corrupted state would cause duplicate writes on every service.
            raise ConfigurationError(
                f"History file {self.path} is unreadable/corrupt; refusing to reset it"
            ) from exc

        if isinstance(raw, list):
            # Original schema: ["youtube_id", ...]
            ids = [str(item) for item in raw if item]
            self.data = {
                "schema_version": 3,
                "synced_video_ids": list(dict.fromkeys(ids)),
                "tracks": {
                    video_id: {"completed": True, "platforms": {}, "migrated": True}
                    for video_id in ids
                },
            }
            self._completed = set(ids)
            self.save()
            return

        if not isinstance(raw, dict):
            raise ConfigurationError("History JSON must be an object or a legacy list")

        if isinstance(raw.get("tracks"), dict):
            self.data = raw
            self.data["schema_version"] = 3
            self.data.setdefault("synced_video_ids", [])
            self.data.setdefault("tracks", {})
            self.data.setdefault("youtube_source_state", {})
        else:
            # Tolerate common hand-written/older dict layouts.
            ids: list[str] = []
            for key in ("synced_video_ids", "synced", "video_ids", "history"):
                if isinstance(raw.get(key), list):
                    ids.extend(str(item) for item in raw[key] if item)
            if not ids and raw and all(isinstance(key, str) for key in raw):
                ids = [key for key, value in raw.items() if bool(value)]
            self.data = {
                "schema_version": 3,
                "synced_video_ids": list(dict.fromkeys(ids)),
                "tracks": {
                    video_id: {"completed": True, "platforms": {}, "migrated": True}
                    for video_id in ids
                },
            }
            self.save()

        completed_from_tracks = [
            video_id
            for video_id, record in self.data["tracks"].items()
            if isinstance(record, dict) and record.get("completed") is True
        ]
        ordered_completed = list(
            dict.fromkeys(
                [
                    str(item)
                    for item in self.data.get("synced_video_ids", [])
                    if item
                ]
                + completed_from_tracks
            )
        )
        self._completed = set(ordered_completed)
        self.data["synced_video_ids"] = ordered_completed
        self.data.setdefault("youtube_source_state", {})

    def is_completed(self, video_id: str) -> bool:
        return video_id in self._completed

    def known_video_ids(self) -> set[str]:
        """Return every completed or partially checkpointed YouTube ID."""

        return self._completed | {
            str(video_id) for video_id in self.data.get("tracks", {})
        }

    def youtube_source_state(self) -> dict[str, Any]:
        state = self.data.get("youtube_source_state", {})
        return dict(state) if isinstance(state, dict) else {}

    def pending_tracks(self) -> list[SourceTrack]:
        """Rehydrate tracks that still need one or more target platforms."""

        pending: list[SourceTrack] = []
        for video_id, record in self.data.get("tracks", {}).items():
            if not isinstance(record, dict) or record.get("completed") is True:
                continue
            youtube = record.get("youtube")
            if not isinstance(youtube, dict):
                continue
            try:
                pending.append(
                    SourceTrack(
                        video_id=str(youtube.get("video_id") or video_id),
                        original_title=str(youtube["original_title"]),
                        title=str(youtube["title"]),
                        artist=str(youtube.get("artist") or ""),
                        position=int(youtube["position"]),
                    )
                )
            except (KeyError, TypeError, ValueError):
                LOG.warning("Ignoring malformed pending history for YouTube ID %s", video_id)
        return sorted(pending, key=lambda track: (track.position, track.video_id))

    def checkpoint_source_scan(self, scan: SourceScan) -> None:
        """Persist discovered tracks and the source cursor in one atomic write."""

        if not scan.state_changed and not scan.new_tracks:
            return
        for track in scan.new_tracks:
            self.ensure_track(track)
        previous = self.youtube_source_state()
        state = dict(scan.state)
        for key in (
            "last_successfully_synced_video_id",
            "last_successfully_synced_at",
        ):
            if key in previous and key not in state:
                state[key] = previous[key]
        self.data["youtube_source_state"] = state
        self.save()

    def ensure_track(self, track: SourceTrack) -> dict[str, Any]:
        records = self.data.setdefault("tracks", {})
        record = records.setdefault(
            track.video_id,
            {
                "completed": False,
                "first_seen_at": utc_now(),
                "platforms": {},
            },
        )
        record["youtube"] = asdict(track)
        record.setdefault("platforms", {})
        record["updated_at"] = utc_now()
        return record

    def platform_status(self, video_id: str, platform: str) -> str:
        record = self.data.get("tracks", {}).get(video_id, {})
        result = record.get("platforms", {}).get(platform, {})
        return str(result.get("status", "")) if isinstance(result, dict) else ""

    def set_platform_result(
        self, video_id: str, platform: str, result: SyncResult
    ) -> None:
        record = self.data["tracks"][video_id]
        payload = asdict(result)
        payload["updated_at"] = utc_now()
        record["platforms"][platform] = {
            key: value for key, value in payload.items() if value not in ("", None)
        }
        record["updated_at"] = utc_now()
        self.save()

    def mark_completed(self, video_id: str) -> None:
        record = self.data["tracks"][video_id]
        record["completed"] = True
        record["completed_at"] = utc_now()
        record["updated_at"] = utc_now()
        if video_id not in self._completed:
            self._completed.add(video_id)
            self.data.setdefault("synced_video_ids", []).append(video_id)
        source_state = self.data.setdefault("youtube_source_state", {})
        if isinstance(source_state, dict):
            source_state["last_successfully_synced_video_id"] = video_id
            source_state["last_successfully_synced_at"] = utc_now()
        self.save()

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.data["schema_version"] = 3
        self.data["updated_at"] = utc_now()
        temporary = self.path.with_name(f".{self.path.name}.tmp")
        try:
            with temporary.open("w", encoding="utf-8") as handle:
                json.dump(self.data, handle, ensure_ascii=False, indent=2, sort_keys=True)
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, self.path)
        except OSError as exc:
            raise PlatformAPIError("Unable to write synchronization history atomically") from exc
        finally:
            try:
                temporary.unlink(missing_ok=True)
            except OSError:
                pass


def utc_now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat()


# ---------------------------------------------------------------------------
# YouTube source
# ---------------------------------------------------------------------------


class YouTubeDataAPISource:
    """Incremental Data API reader backed by persisted head/tail cursors.

    YouTube's ``playlistItems.list`` API has no "items after video ID" filter and
    does not support reverse ordering. To avoid walking the complete playlist on
    every run, this reader stores both boundary IDs and the page token for the
    page that contained the previous tail:

    * unchanged playlist ETag -> no playlist-item page is requested;
    * appended tracks -> resume at the cached tail page;
    * prepended tracks -> scan from the head only until the prior head is found;
    * an ambiguous edit, invalidated page token, deletion, or middle insertion ->
      perform one full reconciliation and refresh the cursors.

    The full reconciliation is a safety fallback, not the normal scheduled path.
    """

    ITEMS_API_URL = "https://www.googleapis.com/youtube/v3/playlistItems"
    PLAYLIST_API_URL = "https://www.googleapis.com/youtube/v3/playlists"
    UNAVAILABLE_TITLES = frozenset(
        {
            "deleted video",
            "private video",
            "[deleted video]",
            "[private video]",
        }
    )

    def __init__(self, api_key: str, playlist_id: str, start_index: int) -> None:
        self.api_key = api_key
        self.playlist_id = playlist_id
        self.start_index = start_index

    def _fetch_metadata(
        self, previous_state: Mapping[str, Any]
    ) -> tuple[int, str, bool]:
        previous_etag = str(previous_state.get("playlist_etag") or "")
        headers = {"If-None-Match": previous_etag} if previous_etag else {}
        response = HTTP.request(
            "GET",
            self.PLAYLIST_API_URL,
            platform="YouTube",
            expected={200, 304},
            params={
                "part": "contentDetails",
                "id": self.playlist_id,
                "key": self.api_key,
            },
            headers=headers,
        )
        if response.status_code == 304:
            return (
                int(previous_state.get("item_count") or 0),
                previous_etag,
                True,
            )

        payload = HTTP.json(response, "YouTube")
        items = payload.get("items", []) if isinstance(payload, dict) else []
        if not items or not isinstance(items[0], dict):
            raise PlatformAPIError("YouTube: source playlist was not found")
        item_count = int((items[0].get("contentDetails") or {}).get("itemCount") or 0)
        etag = str(
            (payload.get("etag") if isinstance(payload, dict) else "")
            or response.headers.get("ETag")
            or ""
        )
        unchanged = bool(
            previous_etag
            and etag
            and etag == previous_etag
            and item_count == int(previous_state.get("item_count") or 0)
        )
        return item_count, etag, unchanged

    def _fetch_page(
        self,
        page_token: str,
        page_cache: dict[str, YouTubePage],
        inspected: list[int],
    ) -> YouTubePage:
        if page_token in page_cache:
            return page_cache[page_token]

        params: dict[str, Any] = {
            "part": "snippet,contentDetails",
            "playlistId": self.playlist_id,
            "maxResults": 50,
            "key": self.api_key,
        }
        if page_token:
            params["pageToken"] = page_token
        response = HTTP.request(
            "GET",
            self.ITEMS_API_URL,
            platform="YouTube",
            expected={200},
            params=params,
        )
        payload = HTTP.json(response, "YouTube")
        if not isinstance(payload, dict):
            raise PlatformAPIError("YouTube: malformed playlist-items response")

        parsed_items: list[YouTubePageItem] = []
        for fallback_position, item in enumerate(payload.get("items", [])):
            if not isinstance(item, dict):
                continue
            snippet = item.get("snippet") or {}
            content = item.get("contentDetails") or {}
            video_id = str(
                content.get("videoId")
                or (snippet.get("resourceId") or {}).get("videoId")
                or ""
            )
            if not video_id:
                continue
            try:
                position = int(snippet.get("position", fallback_position)) + 1
            except (TypeError, ValueError):
                position = fallback_position + 1
            original_title = str(snippet.get("title") or "")
            track: SourceTrack | None = None
            if original_title.casefold() not in self.UNAVAILABLE_TITLES:
                owner = str(
                    snippet.get("videoOwnerChannelTitle")
                    or snippet.get("channelTitle")
                    or ""
                )
                title, artist = derive_track_metadata(original_title, owner)
                track = SourceTrack(
                    video_id=video_id,
                    original_title=original_title,
                    title=title,
                    artist=artist,
                    position=position,
                )
            else:
                LOG.warning("Skipping unavailable YouTube item at position %d", position)
            parsed_items.append(YouTubePageItem(video_id, position, track))

        page = YouTubePage(
            items=tuple(parsed_items),
            next_page_token=str(payload.get("nextPageToken") or ""),
            request_page_token=page_token,
        )
        page_cache[page_token] = page
        inspected[0] += len(page.items)
        return page

    @staticmethod
    def _find(items: Sequence[YouTubePageItem], video_id: str) -> int | None:
        for index, item in enumerate(items):
            if item.video_id == video_id:
                return index
        return None

    def _state(
        self,
        *,
        item_count: int,
        etag: str,
        head_video_id: str,
        tail_video_id: str,
        tail_page_token: str,
        ignored_video_ids: Sequence[str],
    ) -> dict[str, Any]:
        return {
            "version": 1,
            "backend": "youtube-data-api",
            "playlist_id": self.playlist_id,
            "playlist_etag": etag,
            "item_count": item_count,
            "head_video_id": head_video_id,
            "tail_video_id": tail_video_id,
            "tail_page_token": tail_page_token,
            # These are the original pre-index-51 baseline. They must remain
            # ignored during later full reconciliations, while genuinely new
            # tracks prepended after bootstrap are still eligible.
            "ignored_video_ids": list(dict.fromkeys(ignored_video_ids)),
            "last_observed_video_id": tail_video_id,
            "updated_at": utc_now(),
        }

    def _full_scan(
        self,
        *,
        item_count: int,
        etag: str,
        known_video_ids: set[str],
        previous_state: Mapping[str, Any],
        page_cache: dict[str, YouTubePage],
        inspected: list[int],
        bootstrap: bool,
    ) -> SourceScan:
        all_items: list[YouTubePageItem] = []
        page_token = ""
        tail_page_token = ""
        seen_tokens: set[str] = set()

        while True:
            if page_token in seen_tokens:
                raise PlatformAPIError("YouTube: repeated pagination token")
            seen_tokens.add(page_token)
            page = self._fetch_page(page_token, page_cache, inspected)
            all_items.extend(page.items)
            tail_page_token = page.request_page_token
            if not page.next_page_token:
                break
            page_token = page.next_page_token

        previous_ignored = [
            str(item)
            for item in previous_state.get("ignored_video_ids", [])
            if item
        ]
        if bootstrap:
            baseline_ignored = [
                item.video_id for item in all_items if item.position < self.start_index
            ]
        else:
            baseline_ignored = previous_ignored
        effective_known = known_video_ids | set(baseline_ignored)

        new_tracks = tuple(
            item.track
            for item in all_items
            if item.track is not None and item.video_id not in effective_known
        )
        head_id = all_items[0].video_id if all_items else ""
        tail_id = all_items[-1].video_id if all_items else ""
        state = self._state(
            item_count=item_count,
            etag=etag,
            head_video_id=head_id,
            tail_video_id=tail_id,
            tail_page_token=tail_page_token,
            ignored_video_ids=baseline_ignored,
        )
        mode = "bootstrap-full" if bootstrap else "reconciliation-full"
        LOG.info(
            "YouTube %s scan inspected %d item(s) and discovered %d new track(s)",
            mode,
            inspected[0],
            len(new_tracks),
        )
        return SourceScan(new_tracks, state, inspected[0], mode, True)

    def fetch_new(
        self,
        previous_state: Mapping[str, Any],
        known_video_ids: set[str],
    ) -> SourceScan:
        """Fetch only items outside the saved head/tail boundaries when safe."""

        has_prior_boundaries = bool(
            previous_state
            and previous_state.get("playlist_id") == self.playlist_id
            and previous_state.get("head_video_id")
            and previous_state.get("tail_video_id")
        )
        valid_state = bool(
            has_prior_boundaries
            and previous_state.get("backend") == "youtube-data-api"
        )
        state_for_metadata = previous_state if valid_state else {}
        item_count, etag, unchanged = self._fetch_metadata(state_for_metadata)
        if valid_state and unchanged:
            LOG.info(
                "YouTube playlist ETag is unchanged; no playlist-item pages are needed"
            )
            return SourceScan((), dict(previous_state), 0, "etag-unchanged", False)

        page_cache: dict[str, YouTubePage] = {}
        inspected = [0]
        if not valid_state:
            return self._full_scan(
                item_count=item_count,
                etag=etag,
                known_video_ids=known_video_ids,
                previous_state=previous_state,
                page_cache=page_cache,
                inspected=inspected,
                bootstrap=not has_prior_boundaries,
            )

        previous_count = int(previous_state.get("item_count") or 0)
        # Deletions, replacements, reorders, and same-size edits are ambiguous.
        # Reconcile once so a middle insertion cannot be silently missed.
        if item_count <= previous_count:
            return self._full_scan(
                item_count=item_count,
                etag=etag,
                known_video_ids=known_video_ids,
                previous_state=previous_state,
                page_cache=page_cache,
                inspected=inspected,
                bootstrap=False,
            )

        old_head = str(previous_state["head_video_id"])
        old_tail = str(previous_state["tail_video_id"])
        prefix: list[YouTubePageItem] = []
        suffix: list[YouTubePageItem] = []
        current_head_id = ""
        current_tail_id = ""
        current_tail_page_token = ""

        try:
            # Detect prepends by reading only until the prior first item.
            token = ""
            seen_head_tokens: set[str] = set()
            head_found = False
            while True:
                if token in seen_head_tokens:
                    break
                seen_head_tokens.add(token)
                page = self._fetch_page(token, page_cache, inspected)
                if not current_head_id and page.items:
                    current_head_id = page.items[0].video_id
                anchor_index = self._find(page.items, old_head)
                if anchor_index is not None:
                    prefix.extend(page.items[:anchor_index])
                    head_found = True
                    break
                prefix.extend(page.items)
                if not page.next_page_token:
                    break
                token = page.next_page_token

            # Detect appends by resuming at the page that contained the old tail.
            token = str(previous_state.get("tail_page_token") or "")
            seen_tail_tokens: set[str] = set()
            tail_found = False
            while True:
                if token in seen_tail_tokens:
                    break
                seen_tail_tokens.add(token)
                page = self._fetch_page(token, page_cache, inspected)
                current_tail_page_token = page.request_page_token
                anchor_index = self._find(page.items, old_tail)
                if anchor_index is not None:
                    tail_found = True
                    suffix.extend(page.items[anchor_index + 1 :])
                elif tail_found:
                    suffix.extend(page.items)
                if not page.next_page_token:
                    if page.items:
                        current_tail_id = page.items[-1].video_id
                    break
                token = page.next_page_token
        except PlatformAPIError:
            # Cached Google page tokens can be invalidated by sufficiently large
            # playlist edits. A complete scan obtains a fresh safe cursor.
            LOG.warning("YouTube incremental cursor was invalidated; reconciling")
            page_cache.clear()
            inspected[0] = 0
            return self._full_scan(
                item_count=item_count,
                etag=etag,
                known_video_ids=known_video_ids,
                previous_state=previous_state,
                page_cache=page_cache,
                inspected=inspected,
                bootstrap=False,
            )

        outer_items = list(
            {
                item.video_id: item
                for item in [*prefix, *suffix]
            }.values()
        )
        ignored_ids = {
            str(item)
            for item in previous_state.get("ignored_video_ids", [])
            if item
        }
        effective_known = known_video_ids | ignored_ids
        unknown_outer_ids = {
            item.video_id for item in outer_items if item.video_id not in effective_known
        }
        expected_growth = item_count - previous_count

        if not head_found or not tail_found or len(unknown_outer_ids) < expected_growth:
            # Growth not fully explained by prepend/append boundaries means an
            # item was probably inserted in the middle. Reconcile to find it.
            LOG.info(
                "YouTube boundary scan could not explain playlist growth; reconciling"
            )
            return self._full_scan(
                item_count=item_count,
                etag=etag,
                known_video_ids=known_video_ids,
                previous_state=previous_state,
                page_cache=page_cache,
                inspected=inspected,
                bootstrap=False,
            )

        new_tracks = tuple(
            item.track
            for item in sorted(outer_items, key=lambda value: value.position)
            if item.track is not None and item.video_id in unknown_outer_ids
        )
        state = self._state(
            item_count=item_count,
            etag=etag,
            head_video_id=current_head_id or old_head,
            tail_video_id=current_tail_id or old_tail,
            tail_page_token=current_tail_page_token,
            ignored_video_ids=sorted(ignored_ids),
        )
        LOG.info(
            "YouTube incremental boundary scan inspected %d item(s) and discovered "
            "%d new track(s)",
            inspected[0],
            len(new_tracks),
        )
        return SourceScan(new_tracks, state, inspected[0], "incremental", True)


class _YTDLPLogger:
    """Keep yt-dlp diagnostics useful without echoing extraction URLs/cookies."""

    @staticmethod
    def debug(message: str) -> None:
        if message.startswith("[debug]"):
            LOG.debug("yt-dlp: %s", message[:300])

    @staticmethod
    def warning(message: str) -> None:
        LOG.debug("yt-dlp warning: %s", message[:300])

    @staticmethod
    def error(_message: str) -> None:
        # The coordinator logs a sanitized exception and activates the fallback.
        return


class YTDLPYouTubeSource:
    """No-key primary source using bounded yt-dlp playlist slices.

    yt-dlp does not expose YouTube Data API ETags or Google page tokens. It can,
    however, report the total playlist count and select positional ranges. This
    implementation reads the head plus the range containing the previous tail,
    which preserves prepend/append incrementality. A periodic full snapshot
    (24 hours by default) catches same-size middle replacements that cannot be
    inferred from boundary ranges alone.
    """

    BACKEND = "yt-dlp"

    def __init__(self, playlist_id: str, start_index: int) -> None:
        self.playlist_id = playlist_id
        self.start_index = start_index
        self.playlist_url = (
            playlist_id
            if playlist_id.startswith(("http://", "https://"))
            else f"https://www.youtube.com/playlist?list={playlist_id}"
        )
        try:
            self.full_rescan_hours = max(
                1.0, float(os.getenv("YTDLP_FULL_RESCAN_HOURS", "24"))
            )
        except ValueError:
            self.full_rescan_hours = 24.0
        self._range_cache: dict[tuple[int, int | None], tuple[list[YouTubePageItem], int]] = {}
        self._inspected = 0

    @staticmethod
    def _entry_video_id(entry: Mapping[str, Any]) -> str:
        video_id = str(entry.get("id") or "")
        if video_id:
            return video_id
        url = str(entry.get("url") or entry.get("webpage_url") or "")
        parsed = urlparse(url)
        if parsed.hostname and "youtu" in parsed.hostname:
            query = dict(
                part.split("=", 1) if "=" in part else (part, "")
                for part in parsed.query.split("&")
                if part
            )
            return str(query.get("v") or parsed.path.rsplit("/", 1)[-1])
        return ""

    def _extract_range(
        self, start: int = 1, end: int | None = None
    ) -> tuple[list[YouTubePageItem], int]:
        key = (start, end)
        if key in self._range_cache:
            return self._range_cache[key]
        try:
            import yt_dlp
        except ImportError as exc:
            raise PlatformAPIError("yt-dlp primary source is not installed") from exc

        options: dict[str, Any] = {
            "quiet": True,
            "no_warnings": True,
            "logger": _YTDLPLogger(),
            "extract_flat": "in_playlist",
            "skip_download": True,
            "lazy_playlist": True,
            "ignoreerrors": False,
            "socket_timeout": 30,
            "retries": 2,
            "extractor_retries": 2,
        }
        if end is not None:
            options["playlist_items"] = f"{start}:{end}"
        elif start > 1:
            options["playlist_items"] = f"{start}:"

        PACER.wait()
        try:
            with yt_dlp.YoutubeDL(options) as downloader:
                info = downloader.extract_info(self.playlist_url, download=False)
        except Exception as exc:
            raise PlatformAPIError(
                f"yt-dlp primary extraction failed ({type(exc).__name__})"
            ) from exc
        if not isinstance(info, dict):
            raise PlatformAPIError("yt-dlp primary extraction returned no playlist")

        try:
            raw_entries = list(info.get("entries") or [])
        except Exception as exc:
            raise PlatformAPIError(
                f"yt-dlp primary playlist iteration failed ({type(exc).__name__})"
            ) from exc
        if not raw_entries:
            raise PlatformAPIError("yt-dlp primary extraction returned an empty playlist")
        try:
            playlist_count = int(info.get("playlist_count") or 0)
        except (TypeError, ValueError):
            playlist_count = 0
        if playlist_count <= 0:
            if end is None and start == 1:
                playlist_count = len(raw_entries)
            else:
                raise PlatformAPIError("yt-dlp did not report the playlist item count")

        parsed_items: list[YouTubePageItem] = []
        for offset, raw_entry in enumerate(raw_entries):
            if not isinstance(raw_entry, dict):
                continue
            video_id = self._entry_video_id(raw_entry)
            if not video_id:
                continue
            position = start + offset
            original_title = str(raw_entry.get("title") or "")
            track: SourceTrack | None = None
            if original_title.casefold() not in YouTubeDataAPISource.UNAVAILABLE_TITLES:
                owner = str(
                    raw_entry.get("channel")
                    or raw_entry.get("uploader")
                    or raw_entry.get("channel_id")
                    or ""
                )
                title, artist = derive_track_metadata(original_title, owner)
                track = SourceTrack(
                    video_id=video_id,
                    original_title=original_title,
                    title=title,
                    artist=artist,
                    position=position,
                )
            else:
                LOG.warning("Skipping unavailable yt-dlp item at position %d", position)
            parsed_items.append(YouTubePageItem(video_id, position, track))

        if not parsed_items:
            raise PlatformAPIError("yt-dlp primary extraction contained no usable IDs")
        self._inspected += len(parsed_items)
        result = (parsed_items, playlist_count)
        self._range_cache[key] = result
        return result

    def _full_scan_due(self, previous_state: Mapping[str, Any]) -> bool:
        value = str(previous_state.get("last_full_scan_at") or "")
        if not value:
            return True
        try:
            last_scan = datetime.fromisoformat(value.replace("Z", "+00:00"))
            if last_scan.tzinfo is None:
                last_scan = last_scan.replace(tzinfo=UTC)
        except ValueError:
            return True
        age_seconds = (datetime.now(UTC) - last_scan).total_seconds()
        return age_seconds >= self.full_rescan_hours * 3600

    @staticmethod
    def _window_ids(items: Sequence[YouTubePageItem], *, tail: bool = False) -> list[str]:
        window = items[-50:] if tail else items[:50]
        return [item.video_id for item in window]

    def _state(
        self,
        *,
        item_count: int,
        head_items: Sequence[YouTubePageItem],
        tail_items: Sequence[YouTubePageItem],
        ignored_video_ids: Sequence[str],
        previous_state: Mapping[str, Any],
        full_scan: bool,
    ) -> dict[str, Any]:
        head_id = head_items[0].video_id if head_items else ""
        tail_id = tail_items[-1].video_id if tail_items else ""
        state: dict[str, Any] = {
            "version": 1,
            "backend": self.BACKEND,
            "playlist_id": self.playlist_id,
            "playlist_etag": "",
            "item_count": item_count,
            "head_video_id": head_id,
            "tail_video_id": tail_id,
            "tail_page_token": "",
            "head_window_ids": self._window_ids(head_items),
            "tail_window_ids": self._window_ids(tail_items, tail=True),
            "ignored_video_ids": list(dict.fromkeys(ignored_video_ids)),
            "last_observed_video_id": tail_id,
            "updated_at": utc_now(),
        }
        if full_scan:
            state["last_full_scan_at"] = utc_now()
        elif previous_state.get("last_full_scan_at"):
            state["last_full_scan_at"] = previous_state["last_full_scan_at"]
        return state

    def _full_snapshot(
        self,
        previous_state: Mapping[str, Any],
        known_video_ids: set[str],
        *,
        bootstrap: bool,
    ) -> SourceScan:
        # No playlist_items option means the lazy entries iterator spans the
        # complete playlist. Materializing it is reserved for bootstrap and
        # ambiguous/periodic reconciliation.
        items, item_count = self._extract_range(1, None)
        previous_ignored = [
            str(item)
            for item in previous_state.get("ignored_video_ids", [])
            if item
        ]
        ignored = (
            [item.video_id for item in items if item.position < self.start_index]
            if bootstrap
            else previous_ignored
        )
        effective_known = known_video_ids | set(ignored)
        new_tracks = tuple(
            item.track
            for item in items
            if item.track is not None and item.video_id not in effective_known
        )
        state = self._state(
            item_count=item_count,
            head_items=items,
            tail_items=items,
            ignored_video_ids=ignored,
            previous_state=previous_state,
            full_scan=True,
        )
        mode = "primary-ytdlp-bootstrap-full" if bootstrap else "primary-ytdlp-reconcile-full"
        LOG.info(
            "yt-dlp %s inspected %d item(s) and discovered %d new track(s)",
            mode,
            self._inspected,
            len(new_tracks),
        )
        return SourceScan(new_tracks, state, self._inspected, mode, True)

    def fetch_new(
        self,
        previous_state: Mapping[str, Any],
        known_video_ids: set[str],
    ) -> SourceScan:
        self._range_cache.clear()
        self._inspected = 0
        has_prior_boundaries = bool(
            previous_state
            and previous_state.get("playlist_id") == self.playlist_id
            and previous_state.get("head_video_id")
            and previous_state.get("tail_video_id")
        )
        valid_state = bool(
            has_prior_boundaries and previous_state.get("backend") == self.BACKEND
        )
        if not valid_state:
            return self._full_snapshot(
                previous_state,
                known_video_ids,
                bootstrap=not has_prior_boundaries,
            )

        if self._full_scan_due(previous_state):
            LOG.info("yt-dlp periodic source reconciliation is due")
            return self._full_snapshot(previous_state, known_video_ids, bootstrap=False)
        head_items, item_count = self._extract_range(1, 50)

        previous_count = int(previous_state.get("item_count") or 0)
        if item_count < previous_count:
            return self._full_snapshot(previous_state, known_video_ids, bootstrap=False)

        old_head = str(previous_state["head_video_id"])
        old_tail = str(previous_state["tail_video_id"])
        if item_count == previous_count:
            tail_start = max(1, item_count - 49)
            tail_items, _ = self._extract_range(tail_start, item_count)
            current_head_window = self._window_ids(head_items)
            current_tail_window = self._window_ids(tail_items, tail=True)
            if (
                current_head_window == previous_state.get("head_window_ids")
                and current_tail_window == previous_state.get("tail_window_ids")
            ):
                LOG.info(
                    "yt-dlp head/tail windows are unchanged; no new tracks were found"
                )
                return SourceScan(
                    (), dict(previous_state), self._inspected, "primary-ytdlp-unchanged", False
                )
            return self._full_snapshot(previous_state, known_video_ids, bootstrap=False)

        growth = item_count - previous_count
        # If many tracks were prepended, widen the head range enough to include
        # the prior head boundary. The tail range starts one page before the old
        # end and extends through the new end, covering appends and shifted tails.
        head_end = min(item_count, max(50, growth + 1))
        if head_end > 50:
            head_items, _ = self._extract_range(1, head_end)
        tail_start = max(1, previous_count - 49)
        tail_items, _ = self._extract_range(tail_start, item_count)

        head_index = YouTubeDataAPISource._find(head_items, old_head)
        tail_index = YouTubeDataAPISource._find(tail_items, old_tail)
        if head_index is None or tail_index is None:
            return self._full_snapshot(previous_state, known_video_ids, bootstrap=False)
        outer_items = [*head_items[:head_index], *tail_items[tail_index + 1 :]]
        # Preserve source order while removing overlap between the two ranges.
        outer_items = list({item.video_id: item for item in outer_items}.values())
        ignored_ids = {
            str(item)
            for item in previous_state.get("ignored_video_ids", [])
            if item
        }
        effective_known = known_video_ids | ignored_ids
        unknown_ids = {
            item.video_id for item in outer_items if item.video_id not in effective_known
        }
        if len(unknown_ids) < growth:
            # The count increase is not fully explained by the boundaries, so at
            # least one insertion occurred in the middle.
            return self._full_snapshot(previous_state, known_video_ids, bootstrap=False)

        new_tracks = tuple(
            item.track
            for item in sorted(outer_items, key=lambda value: value.position)
            if item.track is not None and item.video_id in unknown_ids
        )
        state = self._state(
            item_count=item_count,
            head_items=head_items,
            tail_items=tail_items,
            ignored_video_ids=sorted(ignored_ids),
            previous_state=previous_state,
            full_scan=False,
        )
        LOG.info(
            "yt-dlp incremental scan inspected %d item(s) and discovered %d new track(s)",
            self._inspected,
            len(new_tracks),
        )
        return SourceScan(
            new_tracks,
            state,
            self._inspected,
            "primary-ytdlp-incremental",
            True,
        )


class YouTubeSource:
    """Primary yt-dlp source with automatic YouTube Data API v3 fallback."""

    def __init__(self, api_key: str, playlist_id: str, start_index: int) -> None:
        self.api_key = api_key
        self.playlist_id = playlist_id
        self.start_index = start_index

    def fetch_new(
        self,
        previous_state: Mapping[str, Any],
        known_video_ids: set[str],
    ) -> SourceScan:
        try:
            scan = YTDLPYouTubeSource(
                self.playlist_id, self.start_index
            ).fetch_new(previous_state, known_video_ids)
            if not scan.new_tracks and not scan.state.get("head_video_id"):
                raise PlatformAPIError("yt-dlp primary source returned no playlist items")
            return scan
        except Exception as primary_error:
            LOG.warning(
                "Primary YouTube source failed (%s); using Data API v3 fallback",
                safe_error(primary_error),
            )

        if not self.api_key:
            raise ConfigurationError(
                "yt-dlp primary source failed and YOUTUBE_API_KEY is not configured for fallback"
            )
        fallback = YouTubeDataAPISource(
            self.api_key, self.playlist_id, self.start_index
        ).fetch_new(previous_state, known_video_ids)
        state = dict(fallback.state)
        state["last_fetch_strategy"] = "youtube-data-api-fallback"
        return SourceScan(
            fallback.new_tracks,
            state,
            fallback.inspected_items,
            f"fallback-api-{fallback.mode}",
            fallback.state_changed,
        )


# ---------------------------------------------------------------------------
# Spotify target
# ---------------------------------------------------------------------------


class SpotifyClient:
    API_BASE = "https://api.spotify.com/v1"
    WEB_HOME = "https://open.spotify.com/"
    TOKEN_URL = "https://open.spotify.com/api/token"
    SCRIPT_RE = re.compile(
        r"(?:vendor~|encore~)?web-player\.[0-9a-f]{4,}\.(?:js|mjs)$", re.I
    )
    JS_STRING = r"(?:'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\")"
    SECRET_PATTERNS = (
        re.compile(
            r"\{\s*(?:secret|['\"]secret['\"])\s*:\s*(?P<secret>"
            + JS_STRING
            + r")\s*,\s*(?:version|['\"]version['\"])\s*:\s*(?P<version>\d+)\s*\}"
        ),
        re.compile(
            r"\{\s*(?:version|['\"]version['\"])\s*:\s*(?P<version>\d+)\s*,"
            r"\s*(?:secret|['\"]secret['\"])\s*:\s*(?P<secret>"
            + JS_STRING
            + r")\s*\}"
        ),
    )

    def __init__(self, sp_dc: str, playlist_id: str, threshold: float) -> None:
        self.sp_dc = sp_dc
        self.playlist_id = self._extract_playlist_id(playlist_id)
        self.threshold = threshold
        self.access_token = ""
        self.client_id = ""
        self.expires_at_ms = 0
        self._playlist_uris: set[str] | None = None

    @staticmethod
    def _extract_playlist_id(value: str) -> str:
        if "spotify.com" in value:
            match = re.search(r"/playlist/([A-Za-z0-9]+)", value)
            if match:
                return match.group(1)
        return value.strip()

    @staticmethod
    def _totp(secret_cipher: str, server_timestamp: int) -> str:
        transformed = [
            ord(character) ^ ((index % 33) + 9)
            for index, character in enumerate(secret_cipher)
        ]
        # The Web Player converts these decimal values to a byte string before
        # applying standard six-digit SHA-1 TOTP.
        key = "".join(str(value) for value in transformed).encode("ascii")
        counter = server_timestamp // 30
        digest = hmac.new(key, struct.pack(">Q", counter), hashlib.sha1).digest()
        offset = digest[-1] & 0x0F
        code = (struct.unpack(">I", digest[offset : offset + 4])[0] & 0x7FFFFFFF) % 1_000_000
        return f"{code:06d}"

    def _discover_web_secret(self) -> tuple[int, str, int]:
        home = HTTP.request(
            "GET",
            self.WEB_HOME,
            platform="Spotify",
            expected={200},
            headers={"Accept": "text/html,*/*"},
            cookies={"sp_dc": self.sp_dc},
        )
        try:
            server_time = int(parsedate_to_datetime(home.headers["Date"]).timestamp())
        except (KeyError, TypeError, ValueError, OverflowError):
            server_time = int(time.time())

        script_urls: list[str] = []
        for source in re.findall(r"<script[^>]+src=[\"']([^\"']+)", home.text):
            url = urljoin(home.url, html.unescape(source))
            filename = urlparse(url).path.rsplit("/", 1)[-1]
            if self.SCRIPT_RE.search(filename) and url not in script_urls:
                script_urls.append(url)
        if not script_urls:
            raise AuthenticationError("Spotify: Web Player token bundle was not found")

        discovered: list[tuple[int, str]] = []
        # The non-vendor bundle normally contains all current secret versions.
        script_urls.sort(key=lambda url: ("vendor~" in url or "encore~" in url, url))
        for url in script_urls:
            response = HTTP.request(
                "GET", url, platform="Spotify", expected={200}, headers={"Accept": "*/*"}
            )
            for pattern in self.SECRET_PATTERNS:
                for match in pattern.finditer(response.text):
                    try:
                        secret = ast.literal_eval(match.group("secret"))
                        version = int(match.group("version"))
                    except (SyntaxError, ValueError):
                        continue
                    if isinstance(secret, str) and secret:
                        discovered.append((version, secret))
            if discovered:
                break
        if not discovered:
            raise AuthenticationError("Spotify: current Web Player TOTP material was not found")
        version, secret = max(discovered, key=lambda value: value[0])
        return version, secret, server_time

    def _refresh_token(self) -> None:
        version, secret, server_time = self._discover_web_secret()
        otp = self._totp(secret, server_time)
        response = HTTP.request(
            "GET",
            self.TOKEN_URL,
            platform="Spotify",
            expected={200},
            params={
                "reason": "transport",
                "productType": "web-player",
                "totp": otp,
                "totpServer": otp,
                "totpVer": version,
            },
            cookies={"sp_dc": self.sp_dc},
            headers={
                "Accept": "application/json",
                "Referer": self.WEB_HOME,
                "App-Platform": "WebPlayer",
            },
        )
        data = HTTP.json(response, "Spotify")
        if not isinstance(data, dict) or not data.get("accessToken"):
            raise AuthenticationError("Spotify: Web Player did not issue an access token")
        if data.get("isAnonymous") is True:
            raise AuthenticationError("Spotify: sp_dc cookie is expired or was rejected")
        self.access_token = str(data["accessToken"])
        self.client_id = str(data.get("clientId") or "")
        self.expires_at_ms = int(data.get("accessTokenExpirationTimestampMs") or 0)

    def _headers(self) -> dict[str, str]:
        if (
            not self.access_token
            or self.expires_at_ms <= int(time.time() * 1000) + 60_000
        ):
            self._refresh_token()
        headers = {
            "Authorization": f"Bearer {self.access_token}",
            "App-Platform": "WebPlayer",
        }
        if self.client_id:
            headers["Client-Id"] = self.client_id
        return headers

    def _request(self, method: str, path: str, **kwargs: Any) -> Response:
        for attempt in range(2):
            try:
                headers = self._headers()
                headers.update(kwargs.pop("headers", {}))
                return HTTP.request(
                    method,
                    f"{self.API_BASE}{path}",
                    platform="Spotify",
                    headers=headers,
                    **kwargs,
                )
            except AuthenticationError:
                if attempt == 0:
                    self.access_token = ""
                    self.expires_at_ms = 0
                    continue
                raise
        raise AuthenticationError("Spotify: token refresh failed")  # pragma: no cover

    def _load_playlist_uris(self) -> set[str]:
        if self._playlist_uris is not None:
            return self._playlist_uris
        uris: set[str] = set()
        path = f"/playlists/{self.playlist_id}/tracks"
        params: dict[str, Any] | None = {"limit": 100, "offset": 0}
        while path:
            response = self._request("GET", path, expected={200}, params=params)
            data = HTTP.json(response, "Spotify")
            for item in data.get("items", []) if isinstance(data, dict) else []:
                track = (item or {}).get("track") or (item or {}).get("item") or {}
                uri = str(track.get("uri") or "")
                if uri:
                    uris.add(uri)
            next_url = str(data.get("next") or "") if isinstance(data, dict) else ""
            if next_url:
                parsed = urlparse(next_url)
                path = parsed.path.removeprefix("/v1")
                params = dict(
                    part.split("=", 1) if "=" in part else (part, "")
                    for part in parsed.query.split("&")
                    if part
                )
            else:
                path = ""
        self._playlist_uris = uris
        return uris

    def sync(self, track: SourceTrack) -> SyncResult:
        response = self._request(
            "GET",
            "/search",
            expected={200},
            params={"q": search_query(track), "type": "track", "limit": 10},
        )
        data = HTTP.json(response, "Spotify")
        candidates: list[Candidate] = []
        items = ((data.get("tracks") or {}).get("items") or []) if isinstance(data, dict) else []
        for item in items:
            if not isinstance(item, dict) or not item.get("id"):
                continue
            artists = ", ".join(
                str(artist.get("name") or "")
                for artist in item.get("artists", [])
                if isinstance(artist, dict)
            )
            candidates.append(
                Candidate(
                    target_id=str(item["id"]),
                    title=str(item.get("name") or ""),
                    artist=artists,
                    uri=str(item.get("uri") or f"spotify:track:{item['id']}"),
                )
            )
        candidate, score = choose_candidate(track, candidates, self.threshold)
        if candidate is None:
            return SyncResult("not_found", score=score, detail="No confident catalog match")

        if candidate.uri in self._load_playlist_uris():
            return SyncResult("already_present", candidate.target_id, score)
        self._request(
            "POST",
            f"/playlists/{self.playlist_id}/tracks",
            expected={200, 201},
            retry_reads=False,
            json={"uris": [candidate.uri]},
        )
        assert self._playlist_uris is not None
        self._playlist_uris.add(candidate.uri)
        return SyncResult("synced", candidate.target_id, score)


# ---------------------------------------------------------------------------
# SoundCloud target
# ---------------------------------------------------------------------------


class SoundCloudClient:
    API_BASE = "https://api.soundcloud.com"

    def __init__(
        self,
        token: str,
        client_id: str,
        playlist: str,
        threshold: float,
    ) -> None:
        self.token = token
        self.client_id = client_id or DEFAULT_SOUNDCLOUD_CLIENT_ID
        self.playlist_value = playlist
        self.threshold = threshold
        self.auth_scheme = environment_value("SOUNDCLOUD_AUTH_SCHEME", default="OAuth")
        self.playlist_id = ""
        self._track_ids: list[str] | None = None

    def _headers(self) -> dict[str, str]:
        return {"Authorization": f"{self.auth_scheme} {self.token}"}

    def _request(self, method: str, path: str, **kwargs: Any) -> Response:
        # SoundCloud expects the application client ID in addition to the user
        # OAuth token. Preserve endpoint-specific parameters while injecting it
        # into every search, resolve, playlist-read, and playlist-write request.
        params = dict(kwargs.pop("params", {}) or {})
        params.setdefault("client_id", self.client_id)
        retried_scheme = False
        while True:
            try:
                return HTTP.request(
                    method,
                    f"{self.API_BASE}{path}",
                    platform="SoundCloud",
                    headers=self._headers(),
                    params=params,
                    **kwargs,
                )
            except AuthenticationError:
                if not retried_scheme and self.auth_scheme.casefold() != "bearer":
                    # Some JWT-style tokens are accepted with Bearer while the public
                    # SoundCloud API documents the OAuth scheme.
                    self.auth_scheme = "Bearer"
                    retried_scheme = True
                    continue
                raise

    def _resolve_playlist_id(self) -> str:
        if self.playlist_id:
            return self.playlist_id
        raw = self.playlist_value.strip()
        if raw.isdigit():
            self.playlist_id = raw
            return raw
        if raw.startswith(("http://", "https://")):
            response = self._request(
                "GET", "/resolve", expected={200}, params={"url": raw}
            )
            data = HTTP.json(response, "SoundCloud")
            identifier = str(data.get("id") or "") if isinstance(data, dict) else ""
            if identifier:
                self.playlist_id = identifier
                return identifier
        raise ConfigurationError("SoundCloud playlist URL/ID could not be resolved")

    def _load_playlist_track_ids(self) -> list[str]:
        if self._track_ids is not None:
            return self._track_ids
        playlist_id = self._resolve_playlist_id()
        response = self._request("GET", f"/playlists/{playlist_id}", expected={200})
        data = HTTP.json(response, "SoundCloud")
        tracks = data.get("tracks", []) if isinstance(data, dict) else []
        self._track_ids = [
            str(item.get("id"))
            for item in tracks
            if isinstance(item, dict) and item.get("id") is not None
        ]
        return self._track_ids

    def sync(self, track: SourceTrack) -> SyncResult:
        response = self._request(
            "GET",
            "/tracks",
            expected={200},
            params={
                "q": search_query(track),
                "access": "playable",
                "limit": 10,
                "linked_partitioning": "true",
            },
        )
        data = HTTP.json(response, "SoundCloud")
        raw_items = data.get("collection", []) if isinstance(data, dict) else data
        candidates: list[Candidate] = []
        for item in raw_items if isinstance(raw_items, list) else []:
            if not isinstance(item, dict) or item.get("id") is None:
                continue
            publisher = item.get("publisher_metadata") or {}
            user = item.get("user") or {}
            artist = str(publisher.get("artist") or user.get("username") or "")
            candidates.append(
                Candidate(
                    target_id=str(item["id"]),
                    title=str(item.get("title") or ""),
                    artist=artist,
                )
            )
        candidate, score = choose_candidate(track, candidates, self.threshold)
        if candidate is None:
            return SyncResult("not_found", score=score, detail="No confident catalog match")

        track_ids = self._load_playlist_track_ids()
        if candidate.target_id in track_ids:
            return SyncResult("already_present", candidate.target_id, score)
        updated = track_ids + [candidate.target_id]
        self._request(
            "PUT",
            f"/playlists/{self._resolve_playlist_id()}",
            expected={200},
            retry_reads=False,
            json={"playlist": {"tracks": [{"id": item} for item in updated]}},
        )
        self._track_ids = updated
        return SyncResult("synced", candidate.target_id, score)


# ---------------------------------------------------------------------------
# Audiomack target
# ---------------------------------------------------------------------------


class AudiomackClient:
    """Audiomack target supporting OAuth 1.0a and requested session fallback.

    The documented write API requires all four OAuth 1.0a values:
      AUDIOMACK_CONSUMER_KEY, AUDIOMACK_CONSUMER_SECRET,
      AUDIOMACK_TOKEN, AUDIOMACK_TOKEN_SECRET

    If the OAuth values are incomplete, AUDIOMACK_TOKEN is sent as both a
    Bearer token and ``player_session`` cookie. That compatibility mode is
    expected to fail fast with an authentication alert if the captured value is
    only Audiomack's statistics player token rather than an account token.
    """

    API_BASE = "https://api.audiomack.com/v1"

    def __init__(self, token: str, playlist: str, threshold: float) -> None:
        self.token = token
        self.playlist_value = playlist
        self.threshold = threshold
        self.token_secret = os.getenv("AUDIOMACK_TOKEN_SECRET", "").strip()
        self.consumer_key = os.getenv("AUDIOMACK_CONSUMER_KEY", "").strip()
        self.consumer_secret = os.getenv("AUDIOMACK_CONSUMER_SECRET", "").strip()
        self.oauth: OAuth1 | None = None
        if all(
            (self.consumer_key, self.consumer_secret, self.token, self.token_secret)
        ):
            self.oauth = OAuth1(
                self.consumer_key,
                client_secret=self.consumer_secret,
                resource_owner_key=self.token,
                resource_owner_secret=self.token_secret,
                signature_type="AUTH_HEADER",
            )
        self.playlist_id = ""
        self._track_ids: set[str] | None = None

    def _request(self, method: str, path: str, **kwargs: Any) -> Response:
        if self.oauth is not None:
            kwargs["auth"] = self.oauth
        else:
            headers = {"Authorization": f"Bearer {self.token}"}
            headers.update(kwargs.pop("headers", {}))
            kwargs["headers"] = headers
            kwargs["cookies"] = {"player_session": self.token}
        return HTTP.request(
            method,
            f"{self.API_BASE}{path}",
            platform="Audiomack",
            **kwargs,
        )

    @staticmethod
    def _single_result(data: Any) -> Mapping[str, Any]:
        if not isinstance(data, dict):
            return {}
        result = data.get("results", data.get("result", data))
        if isinstance(result, list):
            return result[0] if result and isinstance(result[0], dict) else {}
        return result if isinstance(result, dict) else {}

    def _resolve_playlist(self) -> str:
        if self.playlist_id:
            return self.playlist_id
        value = unquote(self.playlist_value.strip())
        if value.isdigit():
            self.playlist_id = value
            return value
        parsed = urlparse(value)
        parts = [part for part in parsed.path.split("/") if part]
        if "playlist" in parts:
            index = parts.index("playlist")
            if index > 0 and len(parts) > index + 1:
                artist_slug, playlist_slug = parts[index - 1], parts[index + 1]
                response = self._request(
                    "GET",
                    f"/playlist/{artist_slug}/{playlist_slug}",
                    expected={200},
                )
                item = self._single_result(HTTP.json(response, "Audiomack"))
                identifier = str(item.get("id") or "")
                if identifier:
                    self.playlist_id = identifier
                    tracks = item.get("tracks") or []
                    self._track_ids = {
                        str(track.get("id") or track.get("music_id"))
                        for track in tracks
                        if isinstance(track, dict)
                        and (track.get("id") or track.get("music_id"))
                    }
                    return identifier
        # The documented endpoint may also accept a non-numeric opaque ID.
        if value and not parsed.scheme:
            self.playlist_id = value
            return value
        raise ConfigurationError("Audiomack playlist URL/ID could not be resolved")

    def sync(self, track: SourceTrack) -> SyncResult:
        response = self._request(
            "GET",
            "/search",
            expected={200},
            params={
                "q": search_query(track),
                "show": "songs",
                "sort": "relevance",
                "limit": 10,
            },
        )
        data = HTTP.json(response, "Audiomack")
        raw_items = data.get("results", []) if isinstance(data, dict) else []
        candidates: list[Candidate] = []
        for item in raw_items if isinstance(raw_items, list) else []:
            if not isinstance(item, dict):
                continue
            identifier = item.get("id") or item.get("music_id")
            if identifier is None:
                continue
            artist_value = item.get("artist") or item.get("uploader") or ""
            if isinstance(artist_value, dict):
                artist_value = artist_value.get("name") or artist_value.get("artist_name") or ""
            candidates.append(
                Candidate(
                    target_id=str(identifier),
                    title=str(item.get("title") or item.get("name") or ""),
                    artist=str(artist_value),
                )
            )
        candidate, score = choose_candidate(track, candidates, self.threshold)
        if candidate is None:
            return SyncResult("not_found", score=score, detail="No confident catalog match")

        playlist_id = self._resolve_playlist()
        if self._track_ids is not None and candidate.target_id in self._track_ids:
            return SyncResult("already_present", candidate.target_id, score)
        self._request(
            "POST",
            f"/playlist/{playlist_id}/track",
            expected={200, 201, 204},
            retry_reads=False,
            data={"music_id": candidate.target_id},
        )
        if self._track_ids is None:
            self._track_ids = set()
        self._track_ids.add(candidate.target_id)
        return SyncResult("synced", candidate.target_id, score)


# ---------------------------------------------------------------------------
# Deezer target
# ---------------------------------------------------------------------------


class DeezerClient:
    def __init__(self, arl: str, playlist: str, threshold: float) -> None:
        try:
            from deezer_python_gql import (
                DeezerGQLClient,
                GraphQLClientAuthError,
                GraphQLClientError,
                GraphQLClientHttpError,
            )
        except ImportError as exc:
            raise ConfigurationError("deezer-python-gql is not installed") from exc

        self._auth_error_type = GraphQLClientAuthError
        self._http_error_type = GraphQLClientHttpError
        self._base_error_type = GraphQLClientError
        self.client = DeezerGQLClient(arl=arl)
        self.playlist_id = self._extract_playlist_id(playlist)
        self.threshold = threshold
        self.loop = asyncio.new_event_loop()
        self._track_ids: set[str] | None = None

    @staticmethod
    def _extract_playlist_id(value: str) -> str:
        match = re.search(r"/playlist/(\d+)", value)
        return match.group(1) if match else value.strip()

    def _run(self, coroutine: Any, operation: str) -> Any:
        PACER.wait()
        try:
            return self.loop.run_until_complete(coroutine)
        except self._auth_error_type as exc:
            raise AuthenticationError("Deezer: ARL cookie is expired or rejected") from exc
        except self._http_error_type as exc:
            status = int(getattr(exc, "status_code", 0) or 0)
            if status in {401, 403}:
                raise AuthenticationError(
                    f"Deezer: authentication rejected (HTTP {status})"
                ) from exc
            raise PlatformAPIError(
                f"Deezer: {operation} failed (HTTP {status or 'unknown'})"
            ) from exc
        except self._base_error_type as exc:
            raise PlatformAPIError(f"Deezer: {operation} failed") from exc
        except Exception as exc:
            raise PlatformAPIError(
                f"Deezer: {operation} failed ({type(exc).__name__})"
            ) from exc

    def _load_playlist_track_ids(self) -> set[str]:
        if self._track_ids is not None:
            return self._track_ids
        identifiers: set[str] = set()
        cursor: str | None = None
        while True:
            playlist = self._run(
                self.client.get_playlist(
                    playlist_id=self.playlist_id,
                    tracks_first=100,
                    tracks_after=cursor,
                ),
                "playlist lookup",
            )
            if playlist is None:
                raise PlatformAPIError("Deezer: target playlist was not found")
            for edge in playlist.tracks.edges:
                if edge.node is not None:
                    identifiers.add(str(edge.node.id))
            page_info = playlist.tracks.page_info
            if not page_info.has_next_page or not page_info.end_cursor:
                break
            cursor = str(page_info.end_cursor)
        self._track_ids = identifiers
        return identifiers

    def sync(self, track: SourceTrack) -> SyncResult:
        result = self._run(
            self.client.search(
                query=search_query(track),
                tracks_first=10,
                albums_first=0,
                artists_first=0,
                playlists_first=0,
                livestreams_first=0,
                podcasts_first=0,
            ),
            "search",
        )
        candidates: list[Candidate] = []
        if result is not None:
            for edge in result.results.tracks.edges:
                node = edge.node
                if node is None:
                    continue
                artists = ", ".join(
                    contributor.node.name
                    for contributor in node.contributors.edges
                    if contributor.node is not None
                )
                candidates.append(
                    Candidate(str(node.id), str(node.title), artists)
                )
        candidate, score = choose_candidate(track, candidates, self.threshold)
        if candidate is None:
            return SyncResult("not_found", score=score, detail="No confident catalog match")

        track_ids = self._load_playlist_track_ids()
        if candidate.target_id in track_ids:
            return SyncResult("already_present", candidate.target_id, score)
        result = self._run(
            self.client.add_tracks_to_playlist(
                playlist_id=self.playlist_id,
                track_ids=[candidate.target_id],
            ),
            "playlist update",
        )
        added = getattr(result, "added_track_ids", None)
        if not added or candidate.target_id not in {str(item) for item in added}:
            raise PlatformAPIError("Deezer: playlist update was not allowed")
        track_ids.add(candidate.target_id)
        return SyncResult("synced", candidate.target_id, score)

    def close(self) -> None:
        try:
            self.loop.run_until_complete(self.client.close())
        except Exception:
            LOG.warning("Deezer client did not close cleanly")
        finally:
            self.loop.close()


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------


TargetClient = SpotifyClient | SoundCloudClient | AudiomackClient | DeezerClient


def build_clients(config: Config) -> tuple[dict[str, TargetClient], dict[str, str]]:
    """Build every target independently; absent optional targets never abort setup."""

    clients: dict[str, TargetClient] = {}
    unavailable: dict[str, str] = {}
    # Deezer is deliberately first so an optional platform's throttling cannot
    # delay it until the end of a track's target loop.
    specifications: list[tuple[str, dict[str, str], Any]] = [
        (
            "deezer",
            {
                "DEEZER_ARL": config.deezer_arl,
                "DEEZER_PLAYLIST_ID": config.deezer_playlist_id,
            },
            lambda: DeezerClient(
                config.deezer_arl,
                config.deezer_playlist_id,
                config.match_threshold,
            ),
        ),
        (
            "spotify",
            {
                "SPOTIFY_SP_DC": config.spotify_sp_dc,
                "SPOTIFY_PLAYLIST_ID": config.spotify_playlist_id,
            },
            lambda: SpotifyClient(
                config.spotify_sp_dc,
                config.spotify_playlist_id,
                config.match_threshold,
            ),
        ),
        (
            "soundcloud",
            {
                "SOUNDCLOUD_OAUTH_TOKEN": config.soundcloud_token,
                "SOUNDCLOUD_CLIENT_ID": config.soundcloud_client_id,
                "SOUNDCLOUD_PLAYLIST_ID": config.soundcloud_playlist_id,
            },
            lambda: SoundCloudClient(
                config.soundcloud_token,
                config.soundcloud_client_id,
                config.soundcloud_playlist_id,
                config.match_threshold,
            ),
        ),
        (
            "audiomack",
            {
                "AUDIOMACK_TOKEN": config.audiomack_token,
                "AUDIOMACK_PLAYLIST_ID": config.audiomack_playlist_id,
            },
            lambda: AudiomackClient(
                config.audiomack_token,
                config.audiomack_playlist_id,
                config.match_threshold,
            ),
        ),
    ]

    for name, environment, constructor in specifications:
        missing = [key for key, value in environment.items() if not value]
        if missing:
            reason = "disabled for this run; missing " + ", ".join(missing)
            unavailable[name] = reason
            LOG.warning("%s target %s", name.title(), reason)
            continue
        try:
            clients[name] = constructor()
            LOG.info(
                "%s target enabled (credential and playlist ID detected)",
                name.title(),
            )
        except SyncError as exc:
            unavailable[name] = f"disabled after initialization error: {exc}"
            LOG.warning("%s target initialization failed: %s", name.title(), exc)
        except Exception as exc:
            reason = f"disabled after initialization error ({type(exc).__name__})"
            unavailable[name] = reason
            LOG.warning("%s target initialization failed: %s", name.title(), reason)
    return clients, unavailable


def safe_error(error: BaseException) -> str:
    if isinstance(error, SyncError):
        return str(error)[:300]
    return f"unexpected {type(error).__name__}"


def format_summary(
    inspected: int,
    discovered: int,
    scan_mode: str,
    pending: int,
    completed: int,
    stats: Mapping[str, Counter[str]],
    unavailable: Mapping[str, str],
) -> str:
    lines = [
        "🎵 Playlist sync job finished",
        (
            f"YouTube: {discovered} newly discovered, {inspected} inspected "
            f"({scan_mode}), {pending} new/partial, {completed} completed this run"
        ),
    ]
    labels = {
        "spotify": "Spotify",
        "soundcloud": "SoundCloud",
        "audiomack": "Audiomack",
        "deezer": "Deezer",
    }
    for platform in ("deezer", "spotify", "soundcloud", "audiomack"):
        if platform in unavailable:
            lines.append(f"{labels[platform]}: {unavailable[platform]}")
            continue
        values = stats.get(platform, Counter())
        if not values:
            continue
        lines.append(
            f"{labels[platform]}: "
            f"synced {values['synced']}, already present {values['already_present']}, "
            f"not found {values['not_found']}, errors {values['error']}, "
            f"rate limited {values['rate_limited']}, deferred {values['deferred']}, "
            f"retained {values['retained']}, blocked {values['blocked']}"
        )
    return "\n".join(lines)


def run() -> int:
    try:
        config = Config.from_environment()
    except ConfigurationError as exc:
        LOG.critical("Configuration error: %s", exc)
        send_telegram_alert(f"🚨 Playlist sync configuration error\n{exc}")
        return 2

    missing_core = [
        name
        for name, value in (
            # YOUTUBE_API_KEY is optional at startup because yt-dlp is the
            # primary source. It is required only if that source needs fallback.
            ("YT_PLAYLIST_ID", config.yt_playlist_id),
            ("TELEGRAM_BOT_TOKEN", config.telegram_bot_token),
            ("TELEGRAM_CHAT_ID", config.telegram_chat_id),
        )
        if not value
    ]
    if missing_core:
        LOG.critical("Missing required environment variables: %s", ", ".join(missing_core))
        # This works only when the Telegram values themselves are present.
        send_telegram_alert(
            "🚨 Playlist sync configuration error\nMissing: " + ", ".join(missing_core)
        )
        return 2

    history = HistoryStore(HISTORY_PATH)
    try:
        history.load()
    except SyncError as exc:
        LOG.critical("History error: %s", exc)
        send_telegram_alert(f"🚨 Playlist sync history error\n{exc}")
        return 2

    try:
        youtube = YouTubeSource(
            config.yt_api_key,
            config.yt_playlist_id,
            config.yt_start_index,
        )
        source_scan = youtube.fetch_new(
            history.youtube_source_state(),
            history.known_video_ids(),
        )
        # Persist the source cursor and newly discovered metadata before touching
        # targets. If a target cookie expires, the next run resumes those tracks
        # from history without walking the YouTube playlist again.
        history.checkpoint_source_scan(source_scan)
    except Exception as exc:
        message = safe_error(exc)
        # Avoid traceback chains here: requests exceptions can include a URL
        # whose query string contains the YouTube API key.
        LOG.error("Fatal YouTube source failure: %s", message)
        send_telegram_alert(f"🚨 Playlist sync failed at YouTube source\n{message}")
        return 1

    pending_tracks = history.pending_tracks()
    LOG.info(
        "Found %d pending track(s), including %d newly discovered in this scan",
        len(pending_tracks),
        len(source_scan.new_tracks),
    )

    clients, unavailable = build_clients(config)
    if unavailable:
        details = "\n".join(
            f"- {name.title()}: {reason}" for name, reason in unavailable.items()
        )
        # Missing optional targets are informational and must not turn the run
        # into a configuration failure or affect an enabled target such as Deezer.
        LOG.warning("Disabled optional target platform(s):\n%s", details)

    active_platforms = [
        name
        for name in ("deezer", "spotify", "soundcloud", "audiomack")
        if name in clients
    ]
    if active_platforms:
        LOG.info("Active target platforms: %s", ", ".join(active_platforms))
    else:
        LOG.warning("No target platform is fully configured; tracks will remain pending")

    stats: defaultdict[str, Counter[str]] = defaultdict(Counter)
    unhealthy: set[str] = set()
    rate_limited: set[str] = set()
    alerted_failures: set[tuple[str, str]] = set()
    completed_this_run = 0

    try:
        for track in pending_tracks:
            LOG.info(
                "Processing YouTube position %d: %s — %s (%s)",
                track.position,
                track.artist or "Unknown artist",
                track.title,
                track.video_id,
            )
            history.ensure_track(track)

            for platform in active_platforms:
                previous = history.platform_status(track.video_id, platform)
                if previous in SUCCESS_STATUSES:
                    stats[platform]["retained"] += 1
                    continue
                if platform in rate_limited:
                    stats[platform]["deferred"] += 1
                    continue
                if platform in unhealthy:
                    stats[platform]["blocked"] += 1
                    continue

                try:
                    result = clients[platform].sync(track)  # type: ignore[union-attr]
                    stats[platform][result.status] += 1
                    history.set_platform_result(track.video_id, platform, result)
                    LOG.info(
                        "%s result for %s: %s%s",
                        platform.title(),
                        track.video_id,
                        result.status,
                        f" (score {result.score})" if result.score is not None else "",
                    )
                except RateLimitError as exc:
                    message = safe_error(exc)
                    stats[platform]["rate_limited"] += 1
                    history.set_platform_result(
                        track.video_id,
                        platform,
                        SyncResult("rate_limited", detail=message),
                    )
                    # Defer only this platform for the rest of the run. The
                    # current and later tracks remain pending for the next run,
                    # while Deezer and every other active target keep running.
                    rate_limited.add(platform)
                    LOG.warning(
                        "%s deferred after rate-limit retries for %s: %s",
                        platform.title(),
                        track.video_id,
                        message,
                    )
                    fingerprint = (platform, "rate_limited")
                    if fingerprint not in alerted_failures:
                        alerted_failures.add(fingerprint)
                        send_telegram_alert(
                            f"⚠️ {platform.title()} rate limited; deferred until next run\n"
                            f"Track: {track.artist} — {track.title}\n{message}"
                        )
                except (AuthenticationError, ConfigurationError) as exc:
                    message = safe_error(exc)
                    stats[platform]["error"] += 1
                    history.set_platform_result(
                        track.video_id,
                        platform,
                        SyncResult("error", detail=message),
                    )
                    # Credential/target configuration failures affect future
                    # tracks on this platform, but never disable another target.
                    unhealthy.add(platform)
                    LOG.error(
                        "%s disabled for the rest of this run: %s",
                        platform.title(),
                        message,
                    )
                    fingerprint = (platform, message)
                    if fingerprint not in alerted_failures:
                        alerted_failures.add(fingerprint)
                        send_telegram_alert(
                            f"🚨 {platform.title()} authentication/configuration failure\n"
                            f"Track: {track.artist} — {track.title}\n{message}"
                        )
                except PlatformAPIError as exc:
                    message = safe_error(exc)
                    stats[platform]["error"] += 1
                    history.set_platform_result(
                        track.video_id,
                        platform,
                        SyncResult("error", detail=message),
                    )
                    # Treat ordinary API failures as track-scoped. This keeps
                    # attempting subsequent tracks and isolates all platforms.
                    LOG.error(
                        "%s failed for %s; continuing other tracks/targets: %s",
                        platform.title(),
                        track.video_id,
                        message,
                    )
                    fingerprint = (platform, message)
                    if fingerprint not in alerted_failures:
                        alerted_failures.add(fingerprint)
                        send_telegram_alert(
                            f"🚨 {platform.title()} synchronization failure\n"
                            f"Track: {track.artist} — {track.title}\n{message}"
                        )
                except Exception as exc:
                    message = safe_error(exc)
                    stats[platform]["error"] += 1
                    history.set_platform_result(
                        track.video_id,
                        platform,
                        SyncResult("error", detail=message),
                    )
                    unhealthy.add(platform)
                    LOG.error(
                        "%s encountered an unexpected error; isolated from other targets: %s",
                        platform.title(),
                        message,
                    )
                    fingerprint = (platform, message)
                    if fingerprint not in alerted_failures:
                        alerted_failures.add(fingerprint)
                        send_telegram_alert(
                            f"🚨 {platform.title()} unexpected synchronization failure\n"
                            f"Track: {track.artist} — {track.title}\n{message}"
                        )

            if active_platforms and all(
                history.platform_status(track.video_id, platform) in SUCCESS_STATUSES
                for platform in active_platforms
            ):
                history.mark_completed(track.video_id)
                completed_this_run += 1
                LOG.info("Track %s is complete on every enabled target", track.video_id)
            else:
                LOG.warning(
                    "Track %s remains pending; successful targets are checkpointed",
                    track.video_id,
                )
    finally:
        for client in clients.values():
            if isinstance(client, DeezerClient):
                client.close()

    summary = format_summary(
        inspected=source_scan.inspected_items,
        discovered=len(source_scan.new_tracks),
        scan_mode=source_scan.mode,
        pending=len(pending_tracks),
        completed=completed_this_run,
        stats=stats,
        unavailable=unavailable,
    )
    LOG.info("\n%s", summary)
    send_telegram_alert(summary)
    # Target failures are deliberately non-fatal: their partial checkpoints remain
    # retryable, and one expired cookie must not block the other services.
    return 0


def main() -> None:
    logging.basicConfig(
        level=os.getenv("LOG_LEVEL", "INFO").upper(),
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%Y-%m-%dT%H:%M:%SZ",
    )
    # Logging timestamps should be unambiguous in GitHub Actions.
    logging.Formatter.converter = time.gmtime
    raise SystemExit(run())


if __name__ == "__main__":
    main()
