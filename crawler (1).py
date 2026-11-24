#!/usr/bin/env python3
"""
crawler.py - lightweight URL-discovery crawler for GLOBAL-remote job postings.

It discovers job-posting URLs ONLY. It never opens job detail pages and never
parses job descriptions. A URL is emitted only when BOTH are true:

  1. LOCATION: the listing card / row / API record itself shows a global
     remote label ("Remote - Global", "Worldwide", "Work from anywhere", ...)
     with no regional qualifier (country, region, state, time zone, hybrid...).
     If the label is not visible on the listing, the URL is skipped (never
     guessed).
  2. FRESHNESS: the posting date (visible on the listing, in the ATS API, or
     the sitemap <lastmod>) is within the last N days (default 3), relative to
     UTC "now" at run time. Missing dates follow --missing-date (drop | keep).

Discovery order (fast -> heavy):
  * ATS JSON listing APIs for Greenhouse, Lever and Ashby boards (one request
    per board; list endpoints only, never per-job pages)
  * sitemap.xml / robots.txt Sitemap: entries (dates + URL-slug labels)
  * httpx + BeautifulSoup on /careers, /jobs and similar listing pages
  * Playwright, only with --playwright, only when a career/jobs page exposes
    no links in its static HTML

Outputs (appended across runs, deduplicated across runs via SQLite):
  <out-dir>/jobs.csv, <out-dir>/jobs.jsonl, <out-dir>/seen_urls.sqlite3,
  <out-dir>/crawler.log

Automatic mode (no site list needed):
  --discover finds Greenhouse / Lever / Ashby job boards from the public Common
  Crawl index (random small queries each run, so coverage grows over time),
  remembers them in the state DB, and re-checks the least-recently-checked ones
  each run (--max-boards). --loop keeps the process running as a server.
  --search-discovery additionally finds boards through web-search queries (needs
  the optional `ddgs` package); it is a best-effort source and may be rate-limited.

Usage:
  pip install -r requirements.txt
  python crawler.py --discover --loop --interval 6        # fully automatic server
  python crawler.py --targets targets.txt                 # or your own sites
  python crawler.py --url https://job-boards.greenhouse.io/gitlab --days 3

Targets file (optional): one URL or bare domain per line (company site,
/careers or /jobs URL, or ATS board). Blank lines and '#' lines are ignored.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import logging
import random
import re
import sqlite3
import sys
import time
import xml.etree.ElementTree as ET
from collections import Counter, deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Optional
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit
from urllib.robotparser import RobotFileParser

import httpx
from bs4 import BeautifulSoup

log = logging.getLogger("jobcrawler")
UTC = timezone.utc
DEFAULT_UA = "job-url-discovery/1.0 (polite URL-only crawler)"


# --------------------------------------------------------------------------- #
# URL normalisation and classification
# --------------------------------------------------------------------------- #
TRACKING_PARAMS = {
    "fbclid", "gclid", "msclkid", "mc_cid", "mc_eid", "ref", "referrer", "source",
    "src", "gh_src", "lever-source", "lever-origin", "_hsenc", "_hsmi", "trk",
    "trackingid",
}


def normalize_url(url: str) -> str:
    """Canonical form used for deduplication: https, lowercase host, no fragment,
    no tracking params, sorted query, no trailing slash. Returns '' if unusable."""
    try:
        parts = urlsplit((url or "").strip())
        host = (parts.hostname or "").lower()
        port = parts.port
    except ValueError:
        return ""
    if parts.scheme.lower() not in ("http", "https") or not host:
        return ""
    netloc = host if port in (None, 80, 443) else f"{host}:{port}"
    path = re.sub(r"/{2,}", "/", parts.path or "/")
    if len(path) > 1:
        path = path.rstrip("/")
    query = sorted(
        (k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
        if k.lower() not in TRACKING_PARAMS and not k.lower().startswith("utm_")
    )
    return urlunsplit(("https", netloc, path, urlencode(query), ""))


def registrable(host: str) -> str:
    """Approximate registrable domain (good enough for same-site checks)."""
    parts = host.lower().split(".")
    if len(parts) >= 3 and len(parts[-1]) == 2 and parts[-2] in {"co", "com", "org", "net", "gov", "ac", "edu"}:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def same_site(a: str, b: str) -> bool:
    return registrable(urlsplit(a).hostname or "") == registrable(urlsplit(b).hostname or "")


ATS_JOB_PATTERNS = [re.compile(p, re.I) for p in (
    r"(?:job-)?boards(?:\.eu)?\.greenhouse\.io/[^/]+/jobs/\d+",
    r"jobs(?:\.eu)?\.lever\.co/[^/]+/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}",
    r"jobs\.ashbyhq\.com/[^/]+/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}",
    r"apply\.workable\.com/[^/]+/j/[A-Z0-9]+",
    r"jobs\.smartrecruiters\.com/[^/]+/\d+",
    r"[^/]+\.recruitee\.com/o/[^/]+",
    r"[^/]+\.breezy\.hr/p/[0-9a-f]+",
    r"[^/]+\.bamboohr\.com/(?:careers|jobs)/\d+",
    r"[^/]+\.jobs\.personio\.(?:de|com)/job/\d+",
    r"[^/]+\.teamtailor\.com/jobs/\d+",
    r"[^/]+\.myworkdayjobs\.com/.+/job/",
)]
JOB_ROOTS = {
    "careers", "career", "jobs", "job", "positions", "openings", "vacancies",
    "opportunities", "join-us", "work-with-us", "open-roles",
}
LISTING_WORDS = {
    "open-positions", "open-roles", "openings", "all-jobs", "all", "search", "departments",
    "department", "teams", "team", "locations", "location", "remote", "categories",
    "category", "students", "internships", "early-careers", "benefits", "culture", "life",
    "faq", "hiring-process", "how-we-hire", "results", "list",
}
EXCLUDE_SEGS = {
    "blog", "news", "press", "privacy", "terms", "legal", "cookie", "cookies", "about",
    "contact", "login", "signin", "signup", "investors", "events", "resources", "policy",
    "policies", "support", "help", "tag", "tags", "author", "feed", "rss", "wp-content",
    "wp-json", "static", "assets", "images", "cdn-cgi",
}
STATIC_EXT = (".pdf", ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".css", ".js",
              ".ico", ".zip", ".mp4", ".xml", ".json")


def classify_url(url: str) -> Optional[str]:
    """'job' (looks like a single posting), 'listing' (career/jobs index page) or None."""
    p = urlsplit(url)
    host = p.netloc.lower()
    if p.path.lower().endswith(STATIC_EXT):
        return None
    target = host + p.path
    if any(pat.search(target) for pat in ATS_JOB_PATTERNS) or "gh_jid=" in p.query.lower():
        return "job"
    segs = [s.lower() for s in p.path.split("/") if s]
    if any(s in EXCLUDE_SEGS for s in segs):
        return None
    root = next((i for i, s in enumerate(segs) if s in JOB_ROOTS), None)
    if root is None:
        if host.split(".")[0] not in {"jobs", "careers", "career"}:
            return None
        tail = segs
    else:
        tail = segs[root + 1:]
    if not tail:
        return "listing"
    if any(s in LISTING_WORDS for s in tail):
        return "listing"
    last = tail[-1]
    if re.search(r"\d", last) or last.count("-") >= 2 or len(last) >= 20:
        return "job"
    return "listing"


def ats_board_from_url(url: str) -> Optional[tuple[str, str]]:
    """Return (kind, board_token) for Greenhouse / Lever / Ashby URLs, else None."""
    p = urlsplit(url)
    host = (p.hostname or "").lower()
    segs = [s for s in p.path.split("/") if s]
    if re.fullmatch(r"(?:job-)?boards(?:\.eu)?\.greenhouse\.io", host):
        if segs and segs[0] == "embed":
            token = dict(parse_qsl(p.query)).get("for")
            return ("greenhouse", token) if token else None
        return ("greenhouse", segs[0]) if segs else None
    if host in ("jobs.lever.co", "jobs.eu.lever.co") and segs:
        return ("lever_eu" if ".eu." in host else "lever", segs[0])
    if host == "jobs.ashbyhq.com" and segs:
        return ("ashby", segs[0])
    return None


# --------------------------------------------------------------------------- #
# Global-remote location matching (strict: do not guess)
# --------------------------------------------------------------------------- #
_GLOBAL_RE = re.compile(
    r"\b(?:remote anywhere in the world"
    r"|remote (?:global|globally|worldwide|world wide|anywhere)"
    r"|(?:global|globally|worldwide|world wide) remote"
    r"|anywhere remote|anywhere in the world|work from anywhere"
    r"|worldwide|world wide)\b"
)
# Used for URL slugs only: stricter (must involve "remote"/"anywhere") to avoid
# false hits such as "worldwide-logistics-manager".
_SLUG_RE = re.compile(
    r"\b(?:remote (?:global|globally|worldwide|world wide|anywhere)"
    r"|(?:global|worldwide|world wide) remote|work from anywhere|anywhere in the world)\b"
)
_SLUG_RESTRICT = {
    "us", "usa", "uk", "eu", "emea", "apac", "latam", "americas", "europe", "canada",
    "asia", "africa", "india", "hybrid", "onsite", "only",
}
# Words allowed to remain beside the global phrase. Anything else (a country,
# region, time zone, "hybrid", "except", a job title...) rejects the segment.
_FILLER = {
    "remote", "remotely", "fully", "full", "time", "100", "open", "to", "candidates",
    "applicants", "location", "locations", "work", "from", "home", "the", "in", "of",
    "world", "a", "an", "wfh", "position", "role", "job", "or", "and", "any", "where",
    "flexible", "eligible", "everywhere",
}
_HYBRID_ONSITE = {"hybrid", "onsite", "on-site", "on site", "office"}


def _norm(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", text.lower().replace("&", " and ")).strip()


def match_global_segment(segment: str) -> Optional[str]:
    """Accept a short location string only if it is ENTIRELY a global-remote label."""
    s = _norm(segment)
    if not s or len(s) > 80 or not _GLOBAL_RE.search(s):
        return None
    leftover = [w for w in _GLOBAL_RE.sub(" ", s).split() if w not in _FILLER]
    if leftover:
        return None
    return re.sub(r"\s+", " ", segment).strip()


def candidate_segments(text: str):
    """Split noisy text into short segments, plus any (parenthetical)/[bracketed] parts."""
    for part in re.split(r"[\n\r\u2022\u00b7|;]+", text or ""):
        part = part.strip()
        if not part:
            continue
        yield part
        for groups in re.findall(r"\(([^)]{1,60})\)|\[([^\]]{1,60})\]", part):
            for g in groups:
                if g:
                    yield g


def first_global_label(strings) -> Optional[str]:
    for s in strings:
        if not isinstance(s, str):
            continue
        for seg in candidate_segments(s):
            label = match_global_segment(seg)
            if label:
                return label
    return None


def match_global_slug(url: str) -> Optional[str]:
    slug = _norm(urlsplit(url).path)
    m = _SLUG_RE.search(slug)
    if not m or set(slug.split()) & _SLUG_RESTRICT:
        return None
    return f"{m.group(0)} (url)"


# --------------------------------------------------------------------------- #
# Date parsing
# --------------------------------------------------------------------------- #
@dataclass
class ParsedDate:
    dt: datetime            # timezone-aware, UTC
    date_only: bool = False  # True when the source had no time-of-day

    def iso(self) -> str:
        return self.dt.strftime("%Y-%m-%d") if self.date_only else self.dt.strftime("%Y-%m-%dT%H:%M:%SZ")

    def is_fresh(self, cutoff: datetime) -> bool:
        # Date-only values are compared by calendar day so "3 days ago" stays inside a 3-day window.
        return self.dt.date() >= cutoff.date() if self.date_only else self.dt >= cutoff


_ISO_RE = re.compile(
    r"(?<!\d)(\d{4})-(\d{2})-(\d{2})"
    r"(?:[T ](\d{2}):(\d{2})(?::(\d{2}))?(?:\.\d+)?\s?(Z|[+-]\d{2}(?::?\d{2})?)?)?(?!\d)"
)
_MONTH = (r"(jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|june?|july?|aug(?:ust)?"
          r"|sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)")
_MDY_RE = re.compile(rf"\b{_MONTH}\.?\s+(\d{{1,2}})(?:st|nd|rd|th)?,?\s+(\d{{4}})\b")
_DMY_RE = re.compile(rf"\b(\d{{1,2}})(?:st|nd|rd|th)?\s+{_MONTH}\.?,?\s+(\d{{4}})\b")
_REL_RE = re.compile(r"\b(?:(\d{1,3})\+?|an?|one)\s+(minute|min|hour|hr|day|week|month|year)s?\s+ago\b")
_NEG_DATE_RE = re.compile(r"deadline|closing|closes|expire|apply by|until|starts?\b|start date", re.I)
_MONTHS = {m: i for i, m in enumerate(
    ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"], 1)}


def _tz(s: Optional[str]) -> timezone:
    if not s or s.upper() == "Z":
        return UTC
    sign = 1 if s[0] == "+" else -1
    digits = s[1:].replace(":", "")
    return timezone(sign * timedelta(hours=int(digits[:2]), minutes=int(digits[2:4] or "0")))


def _from_iso_match(m: re.Match) -> Optional[ParsedDate]:
    y, mo, d, hh, mi, ss, tz = m.groups()
    try:
        if hh is None:
            return ParsedDate(datetime(int(y), int(mo), int(d), tzinfo=UTC), True)
        dt = datetime(int(y), int(mo), int(d), int(hh), int(mi), int(ss or 0), tzinfo=_tz(tz))
        return ParsedDate(dt.astimezone(UTC), False)
    except (ValueError, OverflowError):
        return None


def _midnight(dt: datetime) -> datetime:
    return dt.replace(hour=0, minute=0, second=0, microsecond=0)


def parse_api_date(value: Any) -> Optional[ParsedDate]:
    """Dates from JSON/ISO attributes: ISO strings or epoch seconds/milliseconds."""
    if value is None or value == "":
        return None
    if isinstance(value, str) and value.strip().isdigit():
        value = int(value.strip())
    if isinstance(value, (int, float)):
        ts = float(value)
        if ts > 1e11:
            ts /= 1000.0
        try:
            return ParsedDate(datetime.fromtimestamp(ts, UTC), False)
        except (OverflowError, OSError, ValueError):
            return None
    if isinstance(value, str):
        m = _ISO_RE.search(value)
        return _from_iso_match(m) if m else None
    return None


def latest_date(*values: Any) -> Optional[ParsedDate]:
    dates = [d for d in (parse_api_date(v) for v in values) if d]
    return max(dates, key=lambda d: d.dt) if dates else None


def parse_date_text(text: str, now: datetime) -> Optional[ParsedDate]:
    """Dates shown on listing pages: ISO, 'Nov 22, 2026', '22 Nov 2026', '3 days ago', 'Posted today'."""
    m = _ISO_RE.search(text)
    if m:
        return _from_iso_match(m)
    low = text.lower()
    try:
        m = _MDY_RE.search(low)
        if m:
            return ParsedDate(datetime(int(m.group(3)), _MONTHS[m.group(1)[:3]], int(m.group(2)), tzinfo=UTC), True)
        m = _DMY_RE.search(low)
        if m:
            return ParsedDate(datetime(int(m.group(3)), _MONTHS[m.group(2)[:3]], int(m.group(1)), tzinfo=UTC), True)
    except ValueError:
        return None
    m = _REL_RE.search(low)
    if m:
        n = int(m.group(1)) if m.group(1) else 1
        unit = m.group(2)
        if unit in ("minute", "min"):
            return ParsedDate(now - timedelta(minutes=n), False)
        if unit in ("hour", "hr"):
            return ParsedDate(now - timedelta(hours=n), False)
        days = {"day": 1, "week": 7, "month": 30, "year": 365}[unit] * n
        return ParsedDate(_midnight(now - timedelta(days=days)), True)
    if re.search(r"\b(just now|just posted|moments? ago)\b", low):
        return ParsedDate(now, False)
    # Bare "today"/"yesterday" only count when clearly about the posting date.
    stripped = low.strip(" :-\u2022\u00b7")
    labelled = re.search(r"\b(posted|updated|published|added|listed|new)\b", low)
    if re.fullmatch(r"(?:posted|updated|published|added)?\s*(?:on\s+)?(today|yesterday)", stripped) or labelled:
        if re.search(r"\btoday\b", low):
            return ParsedDate(_midnight(now), True)
        if re.search(r"\byesterday\b", low):
            return ParsedDate(_midnight(now - timedelta(days=1)), True)
    return None


# --------------------------------------------------------------------------- #
# Data model
# --------------------------------------------------------------------------- #
@dataclass
class Candidate:
    url: str
    source_url: str
    location_matched: str
    posted: Optional[ParsedDate] = None


@dataclass
class PageResult:
    jobs: list[Candidate] = field(default_factory=list)
    listing_links: list[str] = field(default_factory=list)
    next_links: list[str] = field(default_factory=list)
    ats_boards: list[tuple[str, str]] = field(default_factory=list)
    job_links_seen: int = 0
    unverified: int = 0


# --------------------------------------------------------------------------- #
# HTTP layer: polite delay, retry/backoff, robots.txt
# --------------------------------------------------------------------------- #
class Fetcher:
    RETRY_STATUS = {429, 500, 502, 503, 504}

    def __init__(self, user_agent: str, delay: float, timeout: float, retries: int):
        self.user_agent = user_agent
        self.delay = max(0.0, delay)
        self.retries = max(0, retries)
        self.client = httpx.Client(
            headers={
                "User-Agent": user_agent,
                "Accept": "text/html,application/xhtml+xml,application/xml,application/json;q=0.9,*/*;q=0.8",
                "Accept-Language": "en",
            },
            timeout=timeout,
            follow_redirects=True,
        )
        self._last_hit: dict[str, float] = {}
        self._robots: dict[str, RobotFileParser] = {}

    def close(self) -> None:
        self.client.close()

    def _pause(self, host: str) -> None:
        gap = self.delay * random.uniform(1.0, 1.4)
        wait = self._last_hit.get(host, 0.0) + gap - time.monotonic()
        if wait > 0:
            time.sleep(wait)

    @staticmethod
    def _backoff(attempt: int) -> float:
        return min(60.0, 2.0 * (2 ** attempt)) + random.uniform(0, 1.0)

    @staticmethod
    def _retry_after(resp: httpx.Response) -> Optional[float]:
        value = resp.headers.get("Retry-After", "")
        return min(float(value), 90.0) if value.strip().isdigit() else None

    def _request(self, url: str, retries: Optional[int] = None) -> Optional[httpx.Response]:
        host = urlsplit(url).netloc.lower()
        max_retries = self.retries if retries is None else retries
        for attempt in range(max_retries + 1):
            self._pause(host)
            try:
                resp = self.client.get(url)
            except httpx.TransportError as exc:  # timeouts, DNS, connection resets
                self._last_hit[host] = time.monotonic()
                if attempt < max_retries:
                    wait = self._backoff(attempt)
                    log.warning("%s on %s; retrying in %.1fs", type(exc).__name__, url, wait)
                    time.sleep(wait)
                    continue
                log.warning("giving up on %s: %s", url, type(exc).__name__)
                return None
            except (httpx.HTTPError, httpx.InvalidURL) as exc:
                log.warning("request failed for %s: %s", url, exc)
                return None
            self._last_hit[host] = time.monotonic()
            if resp.status_code in self.RETRY_STATUS and attempt < max_retries:
                wait = self._retry_after(resp) or self._backoff(attempt)
                log.warning("HTTP %s on %s; retrying in %.1fs", resp.status_code, url, wait)
                time.sleep(wait)
                continue
            return resp
        return None

    def _robots_for(self, origin: str) -> RobotFileParser:
        if origin not in self._robots:
            rp = RobotFileParser()
            resp = self._request(origin + "/robots.txt")
            if resp is None or 400 <= resp.status_code < 500:
                rp.allow_all = True      # unreachable / no robots.txt -> allowed
            elif resp.status_code >= 500:
                rp.disallow_all = True   # persistent server error -> be conservative
                log.warning("robots.txt for %s returned %s; skipping that origin", origin, resp.status_code)
            else:
                rp.parse(resp.text.splitlines())
            self._robots[origin] = rp
        return self._robots[origin]

    def allowed(self, url: str) -> bool:
        p = urlsplit(url)
        return self._robots_for(f"{p.scheme}://{p.netloc}").can_fetch(self.user_agent, url)

    def robots_sitemaps(self, origin: str) -> list[str]:
        return list(self._robots_for(origin).site_maps() or [])

    def get(self, url: str, check_robots: bool = True, retries: Optional[int] = None) -> Optional[httpx.Response]:
        if check_robots and not self.allowed(url):
            log.info("robots.txt disallows %s", url)
            return None
        resp = self._request(url, retries)
        if resp is None:
            return None
        if resp.status_code >= 400:
            level = logging.DEBUG if resp.status_code in (404, 410) else logging.WARNING
            log.log(level, "HTTP %s for %s", resp.status_code, url)
            return None
        return resp

    def get_json(self, url: str, check_robots: bool = False) -> Any:
        resp = self.get(url, check_robots=check_robots)
        if resp is None:
            return None
        try:
            return resp.json()
        except ValueError:
            log.warning("invalid JSON from %s", url)
            return None


class Renderer:
    """Optional Playwright fallback; created lazily and only used when --playwright is set."""

    def __init__(self, enabled: bool, user_agent: str, timeout: float):
        self.enabled = enabled
        self.user_agent = user_agent
        self.timeout_ms = int(timeout * 1000)
        self._pw = self._browser = self._ctx = None

    def _start(self) -> bool:
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            log.warning("--playwright set but playwright is not installed "
                        "(pip install playwright && playwright install chromium)")
            self.enabled = False
            return False
        try:
            self._pw = sync_playwright().start()
            self._browser = self._pw.chromium.launch(headless=True)
            self._ctx = self._browser.new_context(user_agent=self.user_agent)
            return True
        except Exception as exc:  # browser binaries missing, sandbox problems...
            log.warning("could not start Playwright (%s); disabling JS rendering", exc)
            self.enabled = False
            self.close()
            return False

    def render(self, url: str) -> Optional[str]:
        if not self.enabled or (self._ctx is None and not self._start()):
            return None
        page = self._ctx.new_page()
        try:
            page.goto(url, wait_until="domcontentloaded", timeout=self.timeout_ms)
            try:
                page.wait_for_load_state("networkidle", timeout=10_000)
            except Exception:
                pass
            page.wait_for_timeout(1500)
            return page.content()
        except Exception as exc:
            log.warning("Playwright render failed for %s: %s", url, exc)
            return None
        finally:
            page.close()

    def close(self) -> None:
        for obj in (self._ctx, self._browser):
            try:
                if obj:
                    obj.close()
            except Exception:
                pass
        try:
            if self._pw:
                self._pw.stop()
        except Exception:
            pass
        self._pw = self._browser = self._ctx = None


# --------------------------------------------------------------------------- #
# HTML extraction
# --------------------------------------------------------------------------- #
def find_card(anchor, url_by_tag: dict[int, str]):
    """Climb from a job link to the smallest container that holds only that job."""
    best = node = anchor
    for _ in range(6):
        parent = node.parent
        if parent is None or parent.name in ("body", "html", "main", "[document]"):
            break
        urls = {url_by_tag[id(x)] for x in parent.find_all("a", href=True) if id(x) in url_by_tag}
        if len(urls) > 1 or len(parent.get_text(" ", strip=True)) > 1000:
            break
        best = node = parent
    return best


def find_card_date(card, lines: list[str], now: datetime) -> Optional[ParsedDate]:
    def plausible(pd: Optional[ParsedDate]) -> bool:
        return pd is not None and pd.dt <= now + timedelta(days=2)

    for t in card.find_all("time"):
        for val in (t.get("datetime"), t.get_text(" ", strip=True)):
            pd = parse_date_text(val, now) if val else None
            if plausible(pd):
                return pd
    for tag in card.find_all(attrs={"itemprop": "datePosted"}):
        val = tag.get("content") or tag.get_text(" ", strip=True)
        pd = parse_date_text(val, now) if val else None
        if plausible(pd):
            return pd
    for line in lines:
        if len(line) > 80 or _NEG_DATE_RE.search(line):
            continue
        pd = parse_date_text(line, now)
        if plausible(pd):
            return pd
    return None


def extract_page(html: str, page_url: str, now: datetime) -> PageResult:
    soup = BeautifulSoup(html, "lxml")
    res = PageResult()
    anchors: list[tuple[Any, str]] = []
    url_by_tag: dict[int, str] = {}
    page_path = urlsplit(page_url).path

    head_next = soup.find("link", rel="next")
    if head_next and head_next.get("href"):
        nxt = normalize_url(urljoin(page_url, head_next["href"]))
        if nxt and same_site(nxt, page_url):
            res.next_links.append(nxt)

    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href or href.startswith(("#", "mailto:", "tel:", "javascript:")):
            continue
        url = normalize_url(urljoin(page_url, href))
        if not url:
            continue
        board = ats_board_from_url(url)
        if board and board not in res.ats_boards:
            res.ats_boards.append(board)
        kind = classify_url(url)
        if kind == "job":
            anchors.append((a, url))
            url_by_tag[id(a)] = url
        elif kind == "listing" and same_site(url, page_url):
            res.listing_links.append(url)
        txt = a.get_text(" ", strip=True).lower()
        aria = (a.get("aria-label") or "").lower()
        is_next = "next" in (a.get("rel") or []) or re.fullmatch(r"next( page)?|[\u203a\u00bb\u2192>]+", txt) \
            or aria.startswith("next")
        if is_next and same_site(url, page_url) and (urlsplit(url).path == page_path or kind == "listing"):
            res.next_links.append(url)

    res.job_links_seen = len({u for _, u in anchors})
    for a, url in anchors:
        card = find_card(a, url_by_tag)
        text = card.get_text("\n", strip=True)
        label = first_global_label([text])
        if not label:
            res.unverified += 1
            continue
        lines = [p.strip() for p in re.split(r"[\n\r\u2022\u00b7|;]+", text) if p.strip()]
        res.jobs.append(Candidate(url, page_url, label, find_card_date(card, lines, now)))
    return res


# --------------------------------------------------------------------------- #
# Sitemaps
# --------------------------------------------------------------------------- #
MAX_SITEMAP_FILES = 25
MAX_SITEMAP_BYTES = 30 * 1024 * 1024


def _local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def parse_sitemap(data: bytes) -> tuple[str, list[tuple[str, Optional[str]]]]:
    """Return ('index'|'urlset'|'', [(loc, lastmod), ...])."""
    if data[:2] == b"\x1f\x8b":
        try:
            data = gzip.decompress(data)
        except (OSError, EOFError):
            return "", []
    if len(data) > MAX_SITEMAP_BYTES:
        return "", []
    try:
        root = ET.fromstring(data)
    except ET.ParseError:
        return "", []
    kind = {"sitemapindex": "index", "urlset": "urlset"}.get(_local(root.tag), "")
    entries = []
    for el in root:
        loc = lastmod = None
        for child in el:
            name = _local(child.tag)
            if name == "loc":
                loc = (child.text or "").strip()
            elif name == "lastmod":
                lastmod = (child.text or "").strip()
        if loc:
            entries.append((loc, lastmod))
    return kind, entries


# --------------------------------------------------------------------------- #
# Crawler
# --------------------------------------------------------------------------- #
class Crawler:
    MAX_ATS_PER_SEED = 3

    def __init__(self, args: argparse.Namespace, fetcher: Fetcher, renderer: Renderer, now: datetime):
        self.args = args
        self.fetcher = fetcher
        self.renderer = renderer
        self.now = now
        self.candidates: dict[str, Candidate] = {}
        self.sitemap_dates: dict[str, Optional[ParsedDate]] = {}
        self.sitemap_origins: set[str] = set()
        self.ats_done: set[tuple[str, str]] = set()
        self.stats: Counter = Counter()
        self.near_miss: Counter = Counter()  # remote-ish locations that were NOT accepted

    # -- bookkeeping -------------------------------------------------------- #
    def _add(self, c: Candidate) -> None:
        old = self.candidates.get(c.url)
        if old is None:
            self.candidates[c.url] = c
        elif c.posted and (old.posted is None or c.posted.dt > old.posted.dt):
            old.posted = c.posted

    def _note_miss(self, strings) -> None:
        for s in strings:
            if isinstance(s, str) and re.search(r"remote|anywhere|global|worldwide", s, re.I):
                self.near_miss[re.sub(r"\s+", " ", s).strip()[:60]] += 1
                return

    # -- entry point per target -------------------------------------------- #
    def process_target(self, seed: str) -> None:
        board = ats_board_from_url(seed)
        if board:
            self.run_ats(*board)
        else:
            self.crawl_site(seed)

    # -- ATS JSON listing APIs (no per-job requests) ------------------------ #
    def run_ats(self, kind: str, token: str) -> None:
        key = (kind, token.lower())
        if key in self.ats_done:
            return
        self.ats_done.add(key)
        log.info("ATS board: %s/%s", kind, token)
        handler = {"greenhouse": self._greenhouse, "lever": self._lever,
                   "lever_eu": self._lever, "ashby": self._ashby}[kind]
        total, matched = handler(kind, token)
        log.info("  %s/%s: %d postings listed, %d with a global-remote label", kind, token, total, matched)

    def _greenhouse(self, kind: str, token: str) -> tuple[int, int]:
        api = f"https://boards-api.greenhouse.io/v1/boards/{token}/jobs"
        data = self.fetcher.get_json(api)
        jobs = data.get("jobs", []) if isinstance(data, dict) else []
        matched = 0
        for job in jobs:
            link = normalize_url(job.get("absolute_url") or "")
            loc = (job.get("location") or {}).get("name") or ""
            label = first_global_label([loc])
            if not label:
                self._note_miss([loc])
            if link and label:
                matched += 1
                self._add(Candidate(link, api, label, latest_date(job.get("updated_at"), job.get("first_published"))))
        return len(jobs), matched

    def _lever(self, kind: str, token: str) -> tuple[int, int]:
        host = "api.eu.lever.co" if kind == "lever_eu" else "api.lever.co"
        api = f"https://{host}/v0/postings/{token}?mode=json"
        data = self.fetcher.get_json(api)
        jobs = data if isinstance(data, list) else []
        matched = 0
        for job in jobs:
            if str(job.get("workplaceType", "")).lower() in _HYBRID_ONSITE:
                continue
            cats = job.get("categories") or {}
            locs = [cats.get("location")] + list(cats.get("allLocations") or [])
            label = first_global_label(locs)
            if not label:
                self._note_miss(locs)
            link = normalize_url(job.get("hostedUrl") or "")
            if link and label:
                matched += 1
                self._add(Candidate(link, api, label, parse_api_date(job.get("createdAt"))))
        return len(jobs), matched

    def _ashby(self, kind: str, token: str) -> tuple[int, int]:
        api = f"https://api.ashbyhq.com/posting-api/job-board/{token}"
        data = self.fetcher.get_json(api)
        jobs = data.get("jobs", []) if isinstance(data, dict) else []
        matched = 0
        for job in jobs:
            if job.get("isListed") is False:
                continue
            if str(job.get("workplaceType", "")).lower() in _HYBRID_ONSITE:
                continue
            locs = [job.get("location")]
            for sec in job.get("secondaryLocations") or []:
                locs.append(sec.get("location") if isinstance(sec, dict) else sec)
            label = first_global_label(locs)
            if not label:
                self._note_miss(locs)
            link = normalize_url(job.get("jobUrl") or "")
            if link and label:
                matched += 1
                self._add(Candidate(link, api, label, parse_api_date(job.get("publishedAt"))))
        return len(jobs), matched

    # -- sitemaps ------------------------------------------------------------ #
    def discover_sitemaps(self, origin: str) -> None:
        if origin in self.sitemap_origins:
            return
        self.sitemap_origins.add(origin)
        seeds = list(dict.fromkeys(
            self.fetcher.robots_sitemaps(origin) + [origin + "/sitemap.xml", origin + "/sitemap_index.xml"]))
        queue, seen, files, job_urls = deque(seeds), set(), 0, 0
        while queue and files < MAX_SITEMAP_FILES:
            sm = queue.popleft()
            if sm in seen:
                continue
            seen.add(sm)
            resp = self.fetcher.get(sm)
            if resp is None:
                continue
            files += 1
            kind, entries = parse_sitemap(resp.content)
            if kind == "index":
                kids = [loc for loc, _ in entries]
                if len(kids) > 8:  # big index: only descend into job-looking children
                    kids = [k for k in kids if re.search(r"job|career|position|posting|opening|vacanc", k, re.I)]
                queue.extend(kids)
            elif kind == "urlset":
                for loc, lastmod in entries:
                    url = normalize_url(loc)
                    if not url or classify_url(url) != "job":
                        continue
                    job_urls += 1
                    posted = parse_api_date(lastmod)
                    self.sitemap_dates[url] = posted
                    label = match_global_slug(url)
                    if label:
                        self._add(Candidate(url, sm, label, posted))
        if job_urls:
            log.info("sitemaps for %s: %d job-like URLs (%d files)", origin, job_urls, files)

    # -- generic HTML crawl --------------------------------------------------- #
    def crawl_site(self, seed: str) -> None:
        p = urlsplit(seed)
        origin = f"{p.scheme}://{p.netloc}"
        log.info("Site: %s", seed)
        if not self.args.no_sitemaps:
            self.discover_sitemaps(origin)

        queue: deque[tuple[str, int]] = deque([(seed, 0)])
        visited: set[str] = set()
        pages = ats_used = 0
        while queue and pages < self.args.max_pages:
            url, depth = queue.popleft()
            key = normalize_url(url)
            if not key or key in visited:
                continue
            visited.add(key)
            resp = self.fetcher.get(url)
            if resp is None:
                continue
            ctype = resp.headers.get("content-type", "")
            if ctype and "html" not in ctype.lower():
                continue
            pages += 1
            page_url = str(resp.url)
            result = extract_page(resp.text, page_url, self.now)
            career_page = depth == 0 or classify_url(key) == "listing"

            if (career_page and not result.job_links_seen and not result.listing_links
                    and not result.ats_boards and self.renderer.enabled):
                log.info("no links in static HTML for %s; rendering with Playwright", url)
                html = self.renderer.render(url)
                if html:
                    result = extract_page(html, page_url, self.now)

            self.stats["unverified_location"] += result.unverified
            for c in result.jobs:
                self._add(c)
            log.info("  %s: %d job links, %d with global-remote label", page_url, result.job_links_seen, len(result.jobs))

            if career_page:
                for board in result.ats_boards:
                    if ats_used >= self.MAX_ATS_PER_SEED:
                        break
                    if board not in self.ats_done:
                        ats_used += 1
                        self.run_ats(*board)
            if depth < self.args.max_depth:
                for link in result.listing_links:
                    if same_site(link, seed):
                        queue.append((link, depth + 1))
            for link in result.next_links:
                queue.append((link, depth))

    # -- apply freshness + dedupe, then emit ---------------------------------- #
    def finalize(self, store: "Store") -> int:
        cutoff = self.now - timedelta(days=self.args.days)
        emitted = 0
        for url in sorted(self.candidates):
            c = self.candidates[url]
            if c.posted is None:
                c.posted = self.sitemap_dates.get(url)
            if c.posted is None:
                if self.args.missing_date == "drop":
                    self.stats["dropped_no_date"] += 1
                    continue
                status = "unknown"
            elif not c.posted.is_fresh(cutoff):
                self.stats["dropped_older"] += 1
                continue
            else:
                status = "known"
            record = {
                "url": c.url,
                "source_url": c.source_url,
                "location_matched": c.location_matched,
                "posted_date": c.posted.iso() if c.posted else None,
                "date_status": status,
                "discovered_at": self.now.strftime("%Y-%m-%dT%H:%M:%SZ"),
            }
            if store.add(record):
                emitted += 1
            else:
                self.stats["already_seen"] += 1
        return emitted


# --------------------------------------------------------------------------- #
# Output + cross-run state
# --------------------------------------------------------------------------- #
FIELDS = ["url", "source_url", "location_matched", "posted_date", "date_status", "discovered_at"]


class Store:
    def __init__(self, out_dir: Path, db_path: Path, reset: bool, dry_run: bool):
        out_dir.mkdir(parents=True, exist_ok=True)
        self.csv_path = out_dir / "jobs.csv"
        self.jsonl_path = out_dir / "jobs.jsonl"
        self.dry_run = dry_run
        self.db = sqlite3.connect(db_path)
        self.db.execute("CREATE TABLE IF NOT EXISTS seen (url TEXT PRIMARY KEY, first_seen TEXT NOT NULL)")
        self.db.execute("CREATE TABLE IF NOT EXISTS boards (kind TEXT NOT NULL, token TEXT NOT NULL, "
                        "first_seen TEXT NOT NULL, last_crawled TEXT, PRIMARY KEY (kind, token))")
        if reset and not dry_run:
            self.db.execute("DELETE FROM seen")
        self.db.commit()

    def add(self, record: dict) -> bool:
        """Persist a record if its URL was never emitted before. Returns True if new."""
        exists = self.db.execute("SELECT 1 FROM seen WHERE url = ?", (record["url"],)).fetchone()
        if exists:
            return False
        if self.dry_run:
            log.info("[dry-run] %s", json.dumps(record, ensure_ascii=False))
            return True
        self.db.execute("INSERT INTO seen (url, first_seen) VALUES (?, ?)", (record["url"], record["discovered_at"]))
        write_header = not self.csv_path.exists() or self.csv_path.stat().st_size == 0
        with self.csv_path.open("a", newline="", encoding="utf-8") as fh:
            writer = csv.DictWriter(fh, fieldnames=FIELDS)
            if write_header:
                writer.writeheader()
            writer.writerow(record)
        with self.jsonl_path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(record, ensure_ascii=False) + "\n")
        self.db.commit()
        return True

    def add_boards(self, boards, ts: str) -> int:
        """Remember ATS boards (kind, token) for future runs. Returns how many were new."""
        before = self.db.total_changes
        self.db.executemany("INSERT OR IGNORE INTO boards (kind, token, first_seen) VALUES (?, ?, ?)",
                            [(k, t, ts) for k, t in boards])
        self.db.commit()
        return self.db.total_changes - before

    def boards_due(self, limit: int) -> list[tuple[str, str]]:
        """Never-crawled boards first, then the least recently crawled."""
        rows = self.db.execute("SELECT kind, token FROM boards ORDER BY COALESCE(last_crawled, '') ASC, "
                               "first_seen ASC LIMIT ?", (limit,)).fetchall()
        return [(k, t) for k, t in rows]

    def mark_crawled(self, kind: str, token: str, ts: str) -> None:
        self.db.execute("UPDATE boards SET last_crawled = ? WHERE kind = ? AND token = ?", (ts, kind, token))
        self.db.commit()

    def count_boards(self) -> int:
        return self.db.execute("SELECT COUNT(*) FROM boards").fetchone()[0]

    def close(self) -> None:
        self.db.commit()
        self.db.close()


# --------------------------------------------------------------------------- #
# Automatic ATS-board discovery via the public Common Crawl index
# --------------------------------------------------------------------------- #
CC_COLLINFO = "https://index.commoncrawl.org/collinfo.json"
CC_HOSTS = ["boards.greenhouse.io", "job-boards.greenhouse.io", "jobs.lever.co", "jobs.ashbyhq.com"]
_TOKEN_RE = re.compile(r"^[A-Za-z0-9_-]{2,64}$")


def discover_boards(fetcher: Fetcher, queries_per_host: int) -> set[tuple[str, str]]:
    """Find ATS board tokens via small Common Crawl prefix queries (e.g. jobs.lever.co/ab*).
    Random 2-character prefixes are used each run, so coverage grows over time. The index
    server is often overloaded, so each query gets few retries and a host is abandoned after
    two failures; boards already known are still re-checked either way."""
    found: set[tuple[str, str]] = set()
    info = fetcher.get_json(CC_COLLINFO)
    if not isinstance(info, list) or not info or "cdx-api" not in info[0]:
        log.warning("Common Crawl collection list unavailable; skipping board discovery this run")
        return found
    api = info[0]["cdx-api"]  # newest collection first
    log.info("Common Crawl index: %s", info[0].get("id", api))
    chars = "abcdefghijklmnopqrstuvwxyz0123456789"
    all_prefixes = [a + b for a in chars for b in chars]
    for host in CC_HOSTS:
        failures = 0
        for prefix in random.sample(all_prefixes, min(queries_per_host, len(all_prefixes))):
            resp = fetcher.get(f"{api}?url={host}/{prefix}&matchType=prefix&output=json&fl=url&limit=500",
                               check_robots=False, retries=1)
            if resp is None:
                failures += 1
                if failures >= 2:
                    log.warning("  %s: Common Crawl not responding; skipping this host for now", host)
                    break
                continue
            for line in resp.text.splitlines():
                try:
                    url = json.loads(line).get("url", "")
                except ValueError:
                    continue
                board = ats_board_from_url(url)
                if board and _TOKEN_RE.match(board[1]):
                    found.add((board[0], board[1]))
        log.info("  %s: %d boards found so far this run", host, len(found))
    return found


# --------------------------------------------------------------------------- #
# Optional: ATS-board discovery via web-search queries (best effort)
# --------------------------------------------------------------------------- #
SEARCH_HOSTS = ["boards.greenhouse.io", "job-boards.greenhouse.io", "jobs.lever.co", "jobs.ashbyhq.com"]
SEARCH_TERMS = ['"remote - global"', "remote worldwide", '"work from anywhere"', '"anywhere in the world"']


def discover_boards_from_search(max_results: int) -> set[tuple[str, str]]:
    """Query a search engine for global-remote postings on ATS hosts and extract board tokens.
    Unofficial scraping can be blocked or rate-limited at any time: failures are logged, the
    source is abandoned after 3 failures, and the crawler works without it."""
    try:
        from ddgs import DDGS
    except ImportError:
        try:
            from duckduckgo_search import DDGS  # legacy package name
        except ImportError:
            log.warning("--search-discovery needs the 'ddgs' package (pip install ddgs); skipping")
            return set()
    found: set[tuple[str, str]] = set()
    failures = 0
    for host in SEARCH_HOSTS:
        for term in SEARCH_TERMS:
            query = f"site:{host} {term}"
            try:
                rows = DDGS().text(query, max_results=max_results) or []
            except Exception as exc:
                failures += 1
                log.warning("search failed for %r: %s", query, exc)
                if failures >= 3:
                    log.warning("search engine is blocking or rate-limiting; stopping search discovery")
                    return found
                time.sleep(10)
                continue
            for row in rows:
                board = ats_board_from_url(row.get("href") or row.get("url") or "")
                if board and _TOKEN_RE.match(board[1]):
                    found.add(board)
            log.info("  search %r: %d boards so far", query, len(found))
            time.sleep(random.uniform(4, 8))
    return found


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def load_targets(args: argparse.Namespace) -> list[str]:
    raw = list(args.url or [])
    if args.targets:
        for line in Path(args.targets).read_text(encoding="utf-8").splitlines():
            line = re.split(r"\s+#", line.strip(), maxsplit=1)[0].strip()
            if line and not line.startswith("#"):
                raw.append(line)
    targets = []
    for t in raw:
        t = t if "://" in t else "https://" + t
        if urlsplit(t).netloc and t not in targets:
            targets.append(t)
    return targets


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Discover URLs of global-remote, recently posted jobs (URLs only).")
    ap.add_argument("--discover", action="store_true",
                    help="automatically discover ATS boards (Common Crawl) and re-check known ones")
    ap.add_argument("--search-discovery", action="store_true",
                    help="also discover ATS boards via web-search queries (pip install ddgs; best effort)")
    ap.add_argument("--search-results", type=int, default=60,
                    help="max results per search query (default: 60)")
    ap.add_argument("--discover-queries", type=int, default=8,
                    help="Common Crawl prefix queries per ATS host per run (default: 8)")
    ap.add_argument("--max-boards", type=int, default=300,
                    help="max known ATS boards re-checked per run, oldest first (default: 300)")
    ap.add_argument("--loop", action="store_true", help="keep running forever (server mode)")
    ap.add_argument("--interval", type=float, default=6.0, help="hours between runs with --loop (default: 6)")
    ap.add_argument("--targets", help="optional text file with one target URL or domain per line")
    ap.add_argument("--url", action="append", help="target URL (repeatable)")
    ap.add_argument("--out-dir", default="output", help="output directory (default: output)")
    ap.add_argument("--state-db", help="SQLite file for cross-run dedupe (default: <out-dir>/seen_urls.sqlite3)")
    ap.add_argument("--days", type=float, default=3, help="freshness window in days (default: 3)")
    ap.add_argument("--missing-date", choices=["drop", "keep"], default="drop",
                    help="drop: skip URLs with no date; keep: emit with posted_date=null, date_status=unknown")
    ap.add_argument("--delay", type=float, default=1.5, help="min seconds between requests per host (default: 1.5)")
    ap.add_argument("--timeout", type=float, default=20, help="HTTP timeout in seconds (default: 20)")
    ap.add_argument("--retries", type=int, default=4, help="retries on transient errors (default: 4)")
    ap.add_argument("--max-pages", type=int, default=15, help="max HTML pages fetched per target (default: 15)")
    ap.add_argument("--max-depth", type=int, default=2, help="max listing-page depth from the seed (default: 2)")
    ap.add_argument("--no-sitemaps", action="store_true", help="skip sitemap discovery")
    ap.add_argument("--playwright", action="store_true", help="JS-render career pages that expose no links statically")
    ap.add_argument("--user-agent", default=DEFAULT_UA, help="User-Agent string (include a contact URL/email)")
    ap.add_argument("--reset-state", action="store_true", help="forget previously emitted URLs")
    ap.add_argument("--dry-run", action="store_true", help="log matches without writing output files or seen-URL state")
    ap.add_argument("-v", "--verbose", action="store_true", help="debug logging")
    return ap.parse_args(argv)


def setup_logging(out_dir: Path, verbose: bool) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    level = logging.DEBUG if verbose else logging.INFO
    fmt = logging.Formatter("%(asctime)s %(levelname)-7s %(message)s", "%Y-%m-%dT%H:%M:%SZ")
    fmt.converter = time.gmtime
    handlers = [logging.StreamHandler(sys.stderr), logging.FileHandler(out_dir / "crawler.log", encoding="utf-8")]
    for h in handlers:
        h.setFormatter(fmt)
        log.addHandler(h)
    log.setLevel(level)
    logging.getLogger("httpx").setLevel(logging.WARNING)


def run_once(args: argparse.Namespace, targets: list[str]) -> int:
    out_dir = Path(args.out_dir)
    now = datetime.now(UTC)
    ts = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    log.info("run start %s UTC | %d target(s) | discover=%s search=%s | window=%.1f days | missing-date=%s",
             ts, len(targets), args.discover, args.search_discovery, args.days, args.missing_date)

    fetcher = Fetcher(args.user_agent, args.delay, args.timeout, args.retries)
    renderer = Renderer(args.playwright, args.user_agent, args.timeout)
    store = Store(out_dir, Path(args.state_db) if args.state_db else out_dir / "seen_urls.sqlite3",
                  args.reset_state, args.dry_run)
    crawler = Crawler(args, fetcher, renderer, now)
    try:
        for target in targets:
            try:
                crawler.process_target(target)
            except Exception:  # one bad site must not abort the run
                log.exception("target failed: %s", target)

        if args.discover or args.search_discovery:
            boards: set[tuple[str, str]] = set()
            if args.discover:
                try:
                    boards |= discover_boards(fetcher, args.discover_queries)
                except Exception:
                    log.exception("Common Crawl discovery failed")
            if args.search_discovery:
                try:
                    boards |= discover_boards_from_search(args.search_results)
                except Exception:
                    log.exception("search discovery failed")
            new = store.add_boards(boards, ts)
            log.info("board discovery: %d new board(s); %d known in total", new, store.count_boards())
            # boards linked from crawled company pages are remembered too
            store.add_boards(list(crawler.ats_done), ts)
            for kind, token in store.boards_due(args.max_boards):
                try:
                    crawler.run_ats(kind, token)
                except Exception:
                    log.exception("board failed: %s/%s", kind, token)
                store.mark_crawled(kind, token, ts)
        emitted = crawler.finalize(store)
    finally:
        renderer.close()
        fetcher.close()
        store.close()

    if crawler.near_miss:
        log.info("remote-ish locations NOT accepted (not global; check if results look too thin): %s",
                 "; ".join(f"{k} x{v}" for k, v in crawler.near_miss.most_common(10)))
    s = crawler.stats
    log.info("done: %d new URL(s) written | %d global-remote candidates | dropped: %d older, %d no date | "
             "%d already seen | %d listing links without a visible global-remote label (skipped)",
             emitted, len(crawler.candidates), s["dropped_older"], s["dropped_no_date"],
             s["already_seen"], s["unverified_location"])
    return emitted


def main(argv: Optional[list[str]] = None) -> int:
    args = parse_args(argv)
    setup_logging(Path(args.out_dir), args.verbose)
    targets = load_targets(args)
    if not targets and not (args.discover or args.search_discovery):
        log.error("nothing to crawl: use --discover / --search-discovery and/or --targets FILE / --url URL")
        return 2
    try:
        while True:
            try:
                run_once(args, targets)
            except Exception:
                if not args.loop:
                    raise
                log.exception("run failed; will retry at the next interval")
            if not args.loop:
                return 0
            log.info("sleeping %.1f hour(s) until the next run (Ctrl+C to stop)", args.interval)
            time.sleep(max(60.0, args.interval * 3600))
    except KeyboardInterrupt:
        log.info("stopped by user")
        return 0


if __name__ == "__main__":
    sys.exit(main())
