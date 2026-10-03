#!/usr/bin/env python3
"""Synchronize new YouTube playlist entries to music-service playlists.

The program is intentionally headless. Configuration and credentials come from
environment variables (or a local .env file for development), and durable state
is written atomically to ``synced_history.json``.

Important compatibility notes:
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


@dataclass(frozen=True, slots=True)
class SourceTrack:
    video_id: str
    original_title: str
    title: str
    artist: str
    position: int  # One-based YouTube playlist position.


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
        def value(name: str, default: str = "") -> str:
            return os.getenv(name, default).strip()

        try:
            start_index = max(1, int(value("YT_START_INDEX", "51")))
            threshold = min(100.0, max(0.0, float(value("MATCH_THRESHOLD", "78"))))
        except ValueError as exc:
            raise ConfigurationError(
                "YT_START_INDEX must be an integer and MATCH_THRESHOLD must be numeric"
            ) from exc

        return cls(
            yt_api_key=value("YT_API_KEY"),
            yt_playlist_id=value(
                "YT_PLAYLIST_ID", "PLUZA3HbIj2ifyaRs6YrctsjQ08vPCUHE"
            ),
            spotify_sp_dc=value("SPOTIFY_SP_DC"),
            spotify_playlist_id=value(
                "SPOTIFY_PLAYLIST_ID", "1G84VxuubZb4cofjVmk40D"
            ),
            soundcloud_token=value("SOUNDCLOUD_OAUTH_TOKEN"),
            soundcloud_playlist_id=value("SOUNDCLOUD_PLAYLIST_ID"),
            audiomack_token=value("AUDIOMACK_TOKEN"),
            audiomack_playlist_id=value("AUDIOMACK_PLAYLIST_ID"),
            deezer_arl=value("DEEZER_ARL"),
            deezer_playlist_id=value("DEEZER_PLAYLIST_ID"),
            telegram_bot_token=value("TELEGRAM_BOT_TOKEN"),
            telegram_chat_id=value("TELEGRAM_CHAT_ID"),
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

    RETRYABLE_STATUSES = frozenset({429, 500, 502, 503, 504})

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
        can_retry = retry_reads and method in {"GET", "HEAD"}
        max_attempts = 3 if can_retry else 1

        for attempt in range(1, max_attempts + 1):
            self.pacer.wait()
            try:
                response = self.session.request(method, url, timeout=timeout, **kwargs)
            except (requests.Timeout, requests.ConnectionError) as exc:
                if attempt < max_attempts:
                    time.sleep(min(2**attempt, 8))
                    continue
                raise PlatformAPIError(
                    f"{platform}: network request failed after {attempt} attempt(s)"
                ) from exc
            except requests.RequestException as exc:
                raise PlatformAPIError(f"{platform}: HTTP request could not be sent") from exc

            if response.status_code in expected_codes:
                return response
            if response.status_code in {401, 403}:
                raise AuthenticationError(
                    f"{platform}: authentication rejected (HTTP {response.status_code})"
                )
            if (
                response.status_code in self.RETRYABLE_STATUSES
                and attempt < max_attempts
            ):
                retry_after = response.headers.get("Retry-After", "")
                try:
                    delay = min(float(retry_after), 60.0)
                except ValueError:
                    delay = min(2**attempt, 8)
                time.sleep(max(delay, 0.0))
                continue
            raise PlatformAPIError(
                f"{platform}: API request failed (HTTP {response.status_code})"
            )

        raise PlatformAPIError(f"{platform}: API request failed")  # pragma: no cover

    @staticmethod
    def json(response: Response, platform: str) -> Any:
        try:
            return response.json()
        except (ValueError, requests.JSONDecodeError) as exc:
            raise PlatformAPIError(f"{platform}: API returned invalid JSON") from exc


try:
    _delay = float(os.getenv("API_DELAY_SECONDS", "2"))
except ValueError:
    _delay = 2.0
PACER = APIPacer(_delay)
HTTP = HTTPClient(PACER)


def send_telegram_alert(message: str) -> bool:
    """Send a best-effort Telegram message without ever exposing credentials."""

    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()
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
            "schema_version": 2,
            "synced_video_ids": [],
            "tracks": {},
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
                "schema_version": 2,
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
            self.data.setdefault("schema_version", 2)
            self.data.setdefault("synced_video_ids", [])
            self.data.setdefault("tracks", {})
        else:
            # Tolerate common hand-written/older dict layouts.
            ids: list[str] = []
            for key in ("synced_video_ids", "synced", "video_ids", "history"):
                if isinstance(raw.get(key), list):
                    ids.extend(str(item) for item in raw[key] if item)
            if not ids and raw and all(isinstance(key, str) for key in raw):
                ids = [key for key, value in raw.items() if bool(value)]
            self.data = {
                "schema_version": 2,
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

    def is_completed(self, video_id: str) -> bool:
        return video_id in self._completed

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
        self.save()

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.data["schema_version"] = 2
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


class YouTubeSource:
    API_URL = "https://www.googleapis.com/youtube/v3/playlistItems"

    def __init__(self, api_key: str, playlist_id: str, start_index: int) -> None:
        self.api_key = api_key
        self.playlist_id = playlist_id
        self.start_index = start_index

    def fetch(self) -> list[SourceTrack]:
        tracks: list[SourceTrack] = []
        page_token = ""
        fallback_position = 0

        while True:
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
                self.API_URL,
                platform="YouTube",
                expected={200},
                params=params,
            )
            payload = HTTP.json(response, "YouTube")
            if not isinstance(payload, dict):
                raise PlatformAPIError("YouTube: malformed playlist response")

            for item in payload.get("items", []):
                if not isinstance(item, dict):
                    continue
                snippet = item.get("snippet") or {}
                content = item.get("contentDetails") or {}
                video_id = str(
                    content.get("videoId")
                    or (snippet.get("resourceId") or {}).get("videoId")
                    or ""
                )
                original_title = str(snippet.get("title") or "")
                position_zero_based = int(snippet.get("position", fallback_position))
                fallback_position += 1
                position = position_zero_based + 1
                if position < self.start_index:
                    continue
                if not video_id or original_title.casefold() in {
                    "deleted video",
                    "private video",
                    "[deleted video]",
                    "[private video]",
                }:
                    LOG.warning("Skipping unavailable YouTube item at position %d", position)
                    continue
                owner = str(
                    snippet.get("videoOwnerChannelTitle")
                    or snippet.get("channelTitle")
                    or ""
                )
                title, artist = derive_track_metadata(original_title, owner)
                tracks.append(
                    SourceTrack(
                        video_id=video_id,
                        original_title=original_title,
                        title=title,
                        artist=artist,
                        position=position,
                    )
                )

            page_token = str(payload.get("nextPageToken") or "")
            if not page_token:
                break

        LOG.info(
            "Fetched %d eligible YouTube item(s) from playlist position %d onward",
            len(tracks),
            self.start_index,
        )
        return tracks


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

    def __init__(self, token: str, playlist: str, threshold: float) -> None:
        self.token = token
        self.playlist_value = playlist
        self.threshold = threshold
        self.auth_scheme = os.getenv("SOUNDCLOUD_AUTH_SCHEME", "OAuth").strip() or "OAuth"
        self.playlist_id = ""
        self._track_ids: list[str] | None = None

    def _headers(self) -> dict[str, str]:
        return {"Authorization": f"{self.auth_scheme} {self.token}"}

    def _request(self, method: str, path: str, **kwargs: Any) -> Response:
        retried_scheme = False
        while True:
            try:
                return HTTP.request(
                    method,
                    f"{self.API_BASE}{path}",
                    platform="SoundCloud",
                    headers=self._headers(),
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
    clients: dict[str, TargetClient] = {}
    unavailable: dict[str, str] = {}

    constructors: list[tuple[str, bool, Any]] = [
        (
            "spotify",
            bool(config.spotify_sp_dc and config.spotify_playlist_id),
            lambda: SpotifyClient(
                config.spotify_sp_dc,
                config.spotify_playlist_id,
                config.match_threshold,
            ),
        ),
        (
            "soundcloud",
            bool(config.soundcloud_token and config.soundcloud_playlist_id),
            lambda: SoundCloudClient(
                config.soundcloud_token,
                config.soundcloud_playlist_id,
                config.match_threshold,
            ),
        ),
        (
            "audiomack",
            bool(config.audiomack_token and config.audiomack_playlist_id),
            lambda: AudiomackClient(
                config.audiomack_token,
                config.audiomack_playlist_id,
                config.match_threshold,
            ),
        ),
    ]
    if config.deezer_arl:
        constructors.append(
            (
                "deezer",
                bool(config.deezer_playlist_id),
                lambda: DeezerClient(
                    config.deezer_arl,
                    config.deezer_playlist_id,
                    config.match_threshold,
                ),
            )
        )
    else:
        LOG.info("Deezer ARL not provided, skipping Deezer...")

    for name, configured, constructor in constructors:
        if not configured:
            unavailable[name] = "required token/cookie or playlist ID is missing"
            continue
        try:
            clients[name] = constructor()
        except SyncError as exc:
            unavailable[name] = str(exc)
        except Exception as exc:
            unavailable[name] = f"client initialization failed ({type(exc).__name__})"
    return clients, unavailable


def safe_error(error: BaseException) -> str:
    if isinstance(error, SyncError):
        return str(error)[:300]
    return f"unexpected {type(error).__name__}"


def format_summary(
    fetched: int,
    pending: int,
    completed: int,
    stats: Mapping[str, Counter[str]],
    unavailable: Mapping[str, str],
) -> str:
    lines = [
        "🎵 Playlist sync job finished",
        f"YouTube: {fetched} eligible, {pending} new/partial, {completed} completed this run",
    ]
    for platform in ("spotify", "soundcloud", "audiomack", "deezer"):
        if platform in unavailable:
            lines.append(f"{platform.title()}: unavailable")
            continue
        values = stats.get(platform, Counter())
        if not values and platform == "deezer":
            continue
        lines.append(
            f"{platform.title()}: "
            f"synced {values['synced']}, already present {values['already_present']}, "
            f"not found {values['not_found']}, errors {values['error']}, "
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
            ("YT_API_KEY", config.yt_api_key),
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
        fetched_tracks = YouTubeSource(
            config.yt_api_key,
            config.yt_playlist_id,
            config.yt_start_index,
        ).fetch()
    except Exception as exc:
        message = safe_error(exc)
        # Avoid traceback chains here: requests exceptions can include a URL
        # whose query string contains the YouTube API key.
        LOG.error("Fatal YouTube source failure: %s", message)
        send_telegram_alert(f"🚨 Playlist sync failed at YouTube source\n{message}")
        return 1

    pending_tracks = [
        track for track in fetched_tracks if not history.is_completed(track.video_id)
    ]
    LOG.info("Found %d new or partially completed track(s)", len(pending_tracks))

    clients, unavailable = build_clients(config)
    if unavailable:
        details = "\n".join(
            f"- {name.title()}: {reason}" for name, reason in unavailable.items()
        )
        LOG.error("Unavailable target platform(s):\n%s", details)
        send_telegram_alert(f"🚨 Playlist sync target configuration error\n{details}")

    required_platforms = ["spotify", "soundcloud", "audiomack"]
    if config.deezer_arl:
        required_platforms.append("deezer")

    stats: defaultdict[str, Counter[str]] = defaultdict(Counter)
    unhealthy: set[str] = set()
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

            for platform in required_platforms:
                previous = history.platform_status(track.video_id, platform)
                if previous in SUCCESS_STATUSES:
                    stats[platform]["retained"] += 1
                    continue
                if platform in unavailable or platform not in clients:
                    stats[platform]["blocked"] += 1
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
                except Exception as exc:
                    message = safe_error(exc)
                    stats[platform]["error"] += 1
                    history.set_platform_result(
                        track.video_id,
                        platform,
                        SyncResult("error", detail=message),
                    )
                    # Log the sanitized error only. Traceback chains from HTTP
                    # libraries may contain credential-bearing request URLs.
                    LOG.error(
                        "%s failed for %s: %s", platform.title(), track.video_id, message
                    )
                    # An auth or API failure is generally credential/target-wide;
                    # stop hammering it but continue every other platform.
                    unhealthy.add(platform)
                    fingerprint = (platform, message)
                    if fingerprint not in alerted_failures:
                        alerted_failures.add(fingerprint)
                        send_telegram_alert(
                            f"🚨 {platform.title()} synchronization failure\n"
                            f"Track: {track.artist} — {track.title}\n{message}"
                        )

            if all(
                history.platform_status(track.video_id, platform) in SUCCESS_STATUSES
                for platform in required_platforms
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
        fetched=len(fetched_tracks),
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
