#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════╗
║  Xeny.ai Real-Time Monitor — Technotask Business Solutions  ║
║  Version 1.0 | June 2026                                    ║
╠══════════════════════════════════════════════════════════════╣
║  Polls every 15 minutes; fires instant alerts on anomalies  ║
║  Sends Day-on-Day email at 7:00 AM IST daily                ║
║  Sends heartbeat confirmation at 9:00 AM IST daily          ║
║                                                              ║
║  REQUIRES — set as environment variables (never hardcode):  ║
║    XENY_EMAIL      → Xeny.ai super-admin email              ║
║    XENY_PASSWORD   → Xeny.ai super-admin password           ║
║    SMTP_EMAIL      → Gmail address for sending reports      ║
║    SMTP_PASSWORD   → Gmail App Password (not login password)║
╚══════════════════════════════════════════════════════════════╝
"""

import os
import sys
import json
import time
import logging
import smtplib
import argparse
import schedule
import pytz
from datetime import datetime, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from urllib.parse import urlencode
from playwright.sync_api import sync_playwright, TimeoutError as PWTimeout


# ══════════════════════════════════════════════════════════════
#  CONFIGURATION
# ══════════════════════════════════════════════════════════════

XENY_BASE_URL = "https://app.xeny.ai"

# Credentials — loaded from env vars only. Script exits if missing.
XENY_EMAIL    = os.environ.get("XENY_EMAIL", "")
XENY_PASSWORD = os.environ.get("XENY_PASSWORD", "")
SMTP_EMAIL    = os.environ.get("SMTP_EMAIL", "")
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD", "")

ALERT_RECIPIENTS = [
    "Kautuk.sood@technotaskbusinesssolutions.com",
    "Kautuk.sood@technotaskglobal.com",
]

ALERT_CC = [
    "Rajib.Ray@technotaskglobal.com",
]

IST             = pytz.timezone("Asia/Kolkata")
BUSINESS_START  = 8   # 8 AM IST — polling window start
BUSINESS_END    = 22  # 10 PM IST — polling window end

POLL_INTERVAL_MIN       = 15   # minutes between polls
ZERO_CALL_ALERT_CHECKS  = 2    # consecutive 0-call polls before alert (~30 min)
VOLUME_DROP_PCT         = 50   # % drop vs D-1 same day triggers WARNING
FAILURE_RATE_ALERT_PCT  = 25   # % failed calls triggers WARNING (>50% → CRITICAL)
ALERT_COOLDOWN_HOURS    = 2    # don't re-send same alert within 2 hours

# ── Active clients to monitor (exclude: Success Resources, Zenfone, EBMS, Connection Uniform) ──
ACTIVE_CLIENTS = [
    {"name": "OffDuty",                     "country": "India", "currency": "INR", "rate": 2.50},
    {"name": "Blue Tyga Fashions Pvt. Ltd.","country": "India", "currency": "INR", "rate": 2.00},
    {"name": "Sikka Estate",                "country": "India", "currency": "INR", "rate": 5.00},
    {"name": "Century Express",             "country": "UAE",   "currency": "AED", "rate": 0.25},
    {"name": "Edument Education",           "country": "UAE",   "currency": "AED", "rate": 0.50},
]

EXCLUDED_CLIENTS = ["Success Resources", "Zenfone", "EBMS", "Connection Uniform"]
ACTIVE_NAMES     = [c["name"] for c in ACTIVE_CLIENTS]


# ══════════════════════════════════════════════════════════════
#  LOGGING
# ══════════════════════════════════════════════════════════════

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("xeny_monitor.log", encoding="utf-8"),
        logging.StreamHandler(sys.stdout),
    ],
)
log = logging.getLogger("XenyMonitor")


# ══════════════════════════════════════════════════════════════
#  RUNTIME STATE
# ══════════════════════════════════════════════════════════════

_pw              = None   # Playwright instance (kept alive)
_browser         = None   # Chromium browser instance
_pw_context      = None   # Browser context with live session
_data_page       = None   # Persistent app page used for all fetch() API calls
_api_auth_headers = {}    # auth headers captured from real page requests
_cookies_valid   = False
_zero_counts     = {}
_alert_log       = {}


# ══════════════════════════════════════════════════════════════
#  HELPERS
# ══════════════════════════════════════════════════════════════

def now_ist() -> datetime:
    return datetime.now(IST)

def date_str(delta_days: int = 0) -> str:
    return (now_ist() - timedelta(days=delta_days)).strftime("%Y-%m-%d")

def today()     -> str: return date_str(0)
def yesterday() -> str: return date_str(1)
def day_before() -> str: return date_str(2)

def _can_alert(key: str) -> bool:
    """Returns True if this alert key is not in cooldown."""
    last = _alert_log.get(key)
    if last and (now_ist() - last).total_seconds() < ALERT_COOLDOWN_HOURS * 3600:
        return False
    _alert_log[key] = now_ist()
    return True

def _match(client_row: dict, name: str) -> bool:
    """Fuzzy match client_row name against our canonical name."""
    row_name = client_row.get("clientName", client_row.get("name", "")).lower()
    return name.lower() in row_name or row_name in name.lower()

def _get(d: dict, *keys, default=0):
    """Safe dict lookup; coerces strings to int/float so format specs work.
    Handles currency strings like 'INR 775.00' or 'AED 0.00' by stripping prefix."""
    for k in keys:
        if k in d and d[k] is not None:
            v = d[k]
            if isinstance(v, str):
                # Strip currency prefixes like "INR ", "AED " before parsing
                stripped = v.strip()
                for prefix in ("INR ", "AED ", "₹", "$", "€"):
                    if stripped.startswith(prefix):
                        stripped = stripped[len(prefix):].strip()
                        break
                try:
                    return float(stripped) if "." in stripped else int(stripped)
                except (ValueError, TypeError):
                    return default
            return v
    return default

def _sym(currency: str) -> str:
    return "₹" if currency == "INR" else "AED "


# ══════════════════════════════════════════════════════════════
#  AUTHENTICATION — Playwright headless login
# ══════════════════════════════════════════════════════════════

def login() -> bool:
    """Log in to Xeny.ai; keep Playwright browser context alive for all API calls."""
    global _pw, _browser, _pw_context, _cookies_valid
    log.info("🔐 Logging in to Xeny.ai ...")

    try:
        # Clean up any existing instance
        if _pw_context:
            try: _pw_context.close()
            except Exception: pass
        if _browser:
            try: _browser.close()
            except Exception: pass
        if _pw:
            try: _pw.stop()
            except Exception: pass

        _pw      = sync_playwright().start()
        _browser = _pw.chromium.launch(headless=True)
        _pw_context = _browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                       "AppleWebKit/537.36 (KHTML, like Gecko) "
                       "Chrome/124.0.0.0 Safari/537.36"
        )
        page = _pw_context.new_page()

        # Navigate — Next.js redirects to /login if not authenticated
        page.goto(XENY_BASE_URL, timeout=30_000)
        page.wait_for_load_state("networkidle", timeout=20_000)
        log.info(f"  Landed at: {page.url}")

        needs_login = (
            "login" in page.url.lower() or
            "signin" in page.url.lower() or
            page.locator('input[type="password"]').count() > 0
        )

        if needs_login:
            log.info("  Filling login form ...")
            page.wait_for_timeout(2000)

            # Fill email
            for sel in ['input[type="email"]', 'input[name="email"]',
                        'input[placeholder*="email" i]', 'input[autocomplete*="email" i]']:
                try:
                    if page.locator(sel).count() > 0:
                        page.locator(sel).first.click()
                        page.wait_for_timeout(300)
                        page.locator(sel).first.fill(XENY_EMAIL)
                        log.info(f"  Email filled via: {sel}")
                        break
                except Exception:
                    continue

            page.wait_for_timeout(500)

            # Fill password
            for sel in ['input[type="password"]', 'input[name="password"]',
                        'input[placeholder*="password" i]']:
                try:
                    if page.locator(sel).count() > 0:
                        page.locator(sel).first.click()
                        page.wait_for_timeout(300)
                        page.locator(sel).first.fill(XENY_PASSWORD)
                        log.info(f"  Password filled via: {sel}")
                        break
                except Exception:
                    continue

            page.wait_for_timeout(500)

            # Submit
            submitted = False
            for sel in ['button[type="submit"]', 'button:has-text("Login")',
                        'button:has-text("Sign in")', 'button:has-text("Log in")',
                        'button:has-text("Continue")']:
                try:
                    if page.locator(sel).count() > 0:
                        page.locator(sel).first.click()
                        submitted = True
                        log.info(f"  Submit clicked via: {sel}")
                        break
                except Exception:
                    continue

            if not submitted:
                log.info("  Pressing Enter to submit")
                page.keyboard.press("Enter")

            try:
                page.wait_for_url(lambda url: "login" not in url, timeout=15_000)
            except PWTimeout:
                pass

            page.wait_for_timeout(2000)
            log.info(f"  After login: {page.url}")

        if "login" in page.url.lower():
            log.error("❌ Login failed — still on login page. Check XENY_EMAIL / XENY_PASSWORD.")
            return False

        page.close()
        _cookies_valid = True
        log.info("✅ Login OK — Playwright context active")
        return True

    except PWTimeout as e:
        log.error(f"❌ Login timed out: {e}")
        return False
    except Exception as e:
        log.error(f"❌ Login error: {e}")
        return False


def _setup_data_page() -> bool:
    """
    Open revenue-stats page, capture auth credentials via 4 independent methods,
    keep page alive for all subsequent API calls.

    Method 1: Monkey-patch window.fetch via add_init_script (captures headers
              the app's own JS sends — most reliable, works with CSRF tokens)
    Method 2: Playwright request event (network-level headers)
    Method 3: Non-httpOnly cookie scan for CSRF/session tokens
    Method 4: localStorage/sessionStorage JWT scan
    """
    global _data_page, _api_auth_headers, _cookies_valid

    if not _cookies_valid:
        if not login():
            return False

    log.info("  Setting up data page & capturing auth ...")
    captured_req_headers = {}

    # ── Method 1: inject BEFORE page loads — captures app's own fetch headers ──
    FETCH_INTERCEPTOR = """
        window._capturedFetchHeaders = null;
        window._capturedApiResponses  = {};
        const __origFetch = window.fetch;
        window.fetch = async function(url, init) {
            const isApi = typeof url === 'string' && url.includes('/apis/api/');
            // Capture request headers
            if (isApi && !window._capturedFetchHeaders) {
                try {
                    const h = init && init.headers;
                    if (h) {
                        if (h instanceof Headers) {
                            const obj = {};
                            h.forEach((v, k) => { obj[k] = v; });
                            window._capturedFetchHeaders = obj;
                        } else if (typeof h === 'object') {
                            window._capturedFetchHeaders = Object.assign({}, h);
                        }
                    }
                } catch(e) {}
            }
            // Capture response body
            const resp = await __origFetch.apply(this, arguments);
            if (isApi && resp.ok) {
                try {
                    const clone = resp.clone();
                    clone.json().then(data => {
                        const key = url.split('/apis/api/')[1].split('?')[0];
                        window._capturedApiResponses[key] = data;
                    }).catch(() => {});
                } catch(e) {}
            }
            return resp;
        };
    """

    # ── Method 2: network-level request interception ──
    def on_request(req):
        if "/apis/api/" in req.url:
            for k, v in req.headers.items():
                captured_req_headers[k.lower()] = v
            log.info(f"  [Net] Intercepted: ...{req.url.split('/apis/api/')[-1][:60]}")

    page = _pw_context.new_page()
    page.add_init_script(FETCH_INTERCEPTOR)
    page.on("request", on_request)

    try:
        page.goto(f"{XENY_BASE_URL}/revenue-stats", timeout=30_000)
        page.wait_for_load_state("networkidle", timeout=25_000)
        page.wait_for_timeout(3000)   # let async fetch responses settle
    except Exception as e:
        log.error(f"  Page load error: {e}")
        try: page.close()
        except Exception: pass
        return False
    finally:
        try: page.remove_listener("request", on_request)
        except Exception: pass

    if "login" in page.url.lower():
        _cookies_valid = False
        page.close()
        return False

    auth_headers = {}

    # ── Apply Method 2 results ──
    AUTH_KEYS = {"authorization", "x-auth-token", "x-csrf-token", "x-nextauth-token",
                 "x-session-token", "x-api-key", "x-access-token"}
    from_net = {k: v for k, v in captured_req_headers.items() if k in AUTH_KEYS}
    if from_net:
        auth_headers.update(from_net)
        log.info(f"  [Method 2 - Net] {list(from_net.keys())}")

    # ── Apply Method 1 results ──
    try:
        fetched_hdrs = page.evaluate("() => window._capturedFetchHeaders")
        if fetched_hdrs and isinstance(fetched_hdrs, dict):
            for k, v in fetched_hdrs.items():
                kl = k.lower()
                if kl in AUTH_KEYS or kl.startswith("x-"):
                    auth_headers[kl] = v
            log.info(f"  [Method 1 - Fetch monkey-patch] {list(fetched_hdrs.keys())}")
        else:
            log.info("  [Method 1] No headers captured from fetch monkey-patch")
    except Exception as e:
        log.warning(f"  [Method 1] Error: {e}")

    # ── Method 3: readable cookies ──
    try:
        cookies = _pw_context.cookies()
        for c in cookies:
            nl = c["name"].lower()
            if any(t in nl for t in ["csrf", "xsrf"]) and not c.get("httpOnly"):
                hdr = "x-csrf-token"
                auth_headers[hdr] = c["value"]
                log.info(f"  [Method 3 - Cookie] {c['name']} → {hdr}")
    except Exception as e:
        log.warning(f"  [Method 3] Cookie scan error: {e}")

    # ── Method 4: localStorage/sessionStorage JWT ──
    if "authorization" not in auth_headers:
        try:
            tok = page.evaluate("""
                () => {
                    const stores = [];
                    try { stores.push(window.localStorage); }     catch(_) {}
                    try { stores.push(window.sessionStorage); }   catch(_) {}
                    for (const s of stores) {
                        try {
                            for (const key of Object.keys(s)) {
                                const v = s.getItem(key);
                                if (!v || typeof v !== 'string') continue;
                                if (v.startsWith('eyJ') && v.length > 80)
                                    return {type:'raw', key, val: v};
                                try {
                                    const o = JSON.parse(v);
                                    const t = o && (o.token || o.accessToken || o.authToken
                                                    || o.access_token || o.idToken);
                                    if (t && typeof t === 'string' && t.startsWith('eyJ'))
                                        return {type:'field', key, val: t};
                                } catch(_) {}
                            }
                        } catch(_) {}
                    }
                    return null;
                }
            """)
            if tok:
                log.info(f"  [Method 4 - Storage] JWT found [{tok['type']}] key={tok['key']}")
                auth_headers["authorization"] = f"Bearer {tok['val']}"
            else:
                log.info("  [Method 4] No JWT in storage")
        except Exception as e:
            log.warning(f"  [Method 4] Storage scan error: {e}")

    _api_auth_headers = auth_headers
    _data_page = page

    if auth_headers:
        log.info(f"✅ Data page ready. Captured auth: {list(auth_headers.keys())}")
    else:
        log.info("✅ Data page ready. Cookie-only (no extra auth headers found — may still work)")

    return True


def api_get(endpoint: str, params: dict = None) -> dict | None:
    """
    Fetch JSON from Xeny.ai API via the authenticated Playwright page.
    Uses captured auth headers from _setup_data_page().
    Falls back to cached page responses on 401.
    """
    global _data_page, _cookies_valid

    # Ensure data page is ready
    if not _data_page or _data_page.is_closed():
        if not _setup_data_page():
            return None

    url = f"{XENY_BASE_URL}/apis/api/{endpoint}"
    if params:
        url = f"{url}?{urlencode(params)}"  # FIX V-4: use urlencode, not manual join

    fetch_headers = {"Accept": "application/json", **_api_auth_headers}

    try:
        # FIX V-2: Pass url and headers as data arguments, not embedded in JS code.
        # Playwright serializes the second arg safely — no injection risk.
        result = _data_page.evaluate("""
            async ([url, headers]) => {
                try {
                    const r = await fetch(url, {
                        method: "GET",
                        credentials: "include",
                        headers: headers
                    });
                    if (!r.ok) return { _status: r.status, _url: url };
                    return await r.json();
                } catch(e) {
                    return { _error: e.message };
                }
            }
        """, [url, fetch_headers])

        if not result:
            return None

        if "_status" in result:
            s = result["_status"]
            log.warning(f"  API /{endpoint} → HTTP {s}")
            if s == 401:
                # Try cache first before re-login
                short_key = endpoint.split("?")[0]
                try:
                    cached = _data_page.evaluate(
                        f"() => window._capturedApiResponses['{short_key}'] || null"
                    )
                    if cached:
                        log.info(f"  ✔ Using cached page response for {short_key}")
                        return cached
                except Exception:
                    pass
                log.warning("  Auth failed — resetting page for next call")
                _cookies_valid = False
                _data_page     = None
            return None

        if "_error" in result:
            log.warning(f"  API /{endpoint} JS error: {result['_error']}")
            return None

        return result

    except Exception as exc:
        log.error(f"api_get exception: {exc}")
        _data_page = None
        return None


# ══════════════════════════════════════════════════════════════
#  DATA FETCH
# ══════════════════════════════════════════════════════════════

def _base_params(from_date: str, to_date: str, preset: str) -> dict:
    return {
        "startDate": from_date, "endDate": to_date,
        "datePreset": preset, "client": "", "campaign": "",
        "search": "", "page": 1, "limit": 20,
        "sortBy": "totalRevenue", "sortOrder": "desc",
        "country": "", "currency": "INR",
    }

def fetch_clients(from_date: str, to_date: str, preset: str) -> list:
    """Per-client breakdown for a date range."""
    raw = api_get("revenue-dashboard/client-wise", _base_params(from_date, to_date, preset))
    if not raw:
        return []
    # API returns {"data": [...]} or {"data": {"clients": [...]}} or [...]
    data = raw.get("data", raw)
    if isinstance(data, list):
        return data
    if isinstance(data, dict):
        return data.get("clients", data.get("result", data.get("items", [])))
    return []

def fetch_summary(from_date: str, to_date: str, preset: str) -> dict:
    """Platform-level totals for a date range."""
    raw = api_get("revenue-dashboard/summary", _base_params(from_date, to_date, preset))
    if not raw:
        return {}
    data = raw.get("data", raw)
    # If data is a list, try the first element or return empty
    if isinstance(data, list):
        return data[0] if data else {}
    return data if isinstance(data, dict) else {}

def client_row(rows: list, name: str) -> dict:
    """Find one client's row from an API result list."""
    return next((r for r in rows if _match(r, name)), {})


# ══════════════════════════════════════════════════════════════
#  EMAIL SENDER
# ══════════════════════════════════════════════════════════════

def send_email(subject: str, html: str, to: list = None, cc: list = None):
    recipients = to or ALERT_RECIPIENTS
    cc_list    = cc or ALERT_CC
    try:
        msg = MIMEMultipart("alternative")
        msg["From"]    = f"Xeny Monitor <{SMTP_EMAIL}>"
        msg["To"]      = ", ".join(recipients)
        msg["Cc"]      = ", ".join(cc_list)
        msg["Subject"] = subject
        msg.attach(MIMEText(html, "html", "utf-8"))

        # Auto-detect SMTP server from email domain
        domain = SMTP_EMAIL.split("@")[-1].lower()
        all_recipients = recipients + cc_list
        if "gmail" in domain:
            with smtplib.SMTP("smtp.gmail.com", 587) as srv:
                srv.ehlo()
                srv.starttls()
                srv.ehlo()
                srv.login(SMTP_EMAIL, SMTP_PASSWORD)
                srv.sendmail(SMTP_EMAIL, all_recipients, msg.as_string())
        else:
            with smtplib.SMTP("smtp.office365.com", 587) as srv:
                srv.ehlo()
                srv.starttls()
                srv.ehlo()
                srv.login(SMTP_EMAIL, SMTP_PASSWORD)
                srv.sendmail(SMTP_EMAIL, all_recipients, msg.as_string())

        log.info(f"📧 Email sent → {subject}")
    except smtplib.SMTPAuthenticationError:
        log.error("❌ SMTP Auth failed — check SMTP_EMAIL and SMTP_PASSWORD")
        log.error("   For Outlook: use your regular Microsoft 365 password")
        log.error("   If MFA is on: generate App Password at account.microsoft.com/security")
    except Exception as exc:
        log.error(f"❌ Email error: {exc}")


# ══════════════════════════════════════════════════════════════
#  ALERT EMAIL BUILDER
# ══════════════════════════════════════════════════════════════

def _alert_html(today_rows: list, d1_rows: list, severity: str, headline: str) -> str:
    colors = {"CRITICAL": "#dc2626", "WARNING": "#d97706", "INFO": "#2563eb"}
    icons  = {"CRITICAL": "🔴", "WARNING": "⚠️", "INFO": "ℹ️"}
    bg     = colors.get(severity, "#dc2626")
    icon   = icons.get(severity, "🔴")
    ts     = now_ist().strftime("%d %b %Y, %I:%M %p IST")

    rows_html = ""
    for ac in ACTIVE_CLIENTS:
        tc = client_row(today_rows, ac["name"])
        dc = client_row(d1_rows,   ac["name"])
        if not tc:
            continue

        t_sched  = _get(tc, "totalCalls")
        t_conn   = _get(tc, "connectedCalls")
        t_fail   = _get(tc, "notConnectedOrFailedCalls")
        t_min    = _get(tc, "minutesConsumed")
        t_rev    = _get(tc, "totalRevenue")
        d_conn   = _get(dc, "connectedCalls")

        fail_pct = round(t_fail / t_sched * 100, 1) if t_sched else 0
        delta    = t_conn - d_conn
        d_str    = f"+{delta}" if delta >= 0 else str(delta)
        d_col    = "#16a34a" if delta >= 0 else "#dc2626"
        f_col    = "#dc2626" if fail_pct > 25 else "#374151"
        curr     = _sym(ac["currency"])

        rows_html += f"""
        <tr style="border-bottom:1px solid #e5e7eb;">
          <td style="padding:10px 8px;font-weight:600;">{ac['name']}</td>
          <td style="padding:10px 8px;text-align:center;">{t_sched:,}</td>
          <td style="padding:10px 8px;text-align:center;color:#16a34a;font-weight:700;">{t_conn:,}</td>
          <td style="padding:10px 8px;text-align:center;color:{f_col};font-weight:700;">{t_fail:,} ({fail_pct}%)</td>
          <td style="padding:10px 8px;text-align:center;">{t_min:,} min</td>
          <td style="padding:10px 8px;text-align:center;">{curr}{t_rev:,.2f}</td>
          <td style="padding:10px 8px;text-align:center;color:{d_col};font-weight:700;">{d_str} vs D-1</td>
        </tr>"""

    return f"""
<!DOCTYPE html><html><head><meta charset="UTF-8"></head>
<body style="font-family:Arial,sans-serif;background:#f9fafb;margin:0;padding:20px;">
<div style="max-width:700px;margin:0 auto;">
  <div style="background:{bg};color:white;padding:18px 22px;border-radius:10px 10px 0 0;">
    <div style="font-size:20px;font-weight:700;">{icon} {severity} — Xeny.ai Monitor</div>
    <div style="font-size:12px;margin-top:4px;opacity:0.85;">{ts}</div>
  </div>
  <div style="background:white;padding:22px;border:1px solid #e5e7eb;border-radius:0 0 10px 10px;">
    <p style="font-size:15px;color:#111827;margin:0 0 18px;font-weight:600;">{headline}</p>
    <table width="100%" cellspacing="0" style="border-collapse:collapse;font-size:13px;">
      <thead>
        <tr style="background:#f3f4f6;text-transform:uppercase;font-size:11px;color:#374151;">
          <th style="padding:8px;text-align:left;">Client</th>
          <th style="padding:8px;">Scheduled</th>
          <th style="padding:8px;">Connected</th>
          <th style="padding:8px;">Failed</th>
          <th style="padding:8px;">Minutes</th>
          <th style="padding:8px;">Revenue</th>
          <th style="padding:8px;">vs D-1</th>
        </tr>
      </thead>
      <tbody>{rows_html}</tbody>
    </table>
    <p style="margin:18px 0 0;font-size:12px;color:#6b7280;">
      Monitor polls every 15 min during 8 AM–10 PM IST &nbsp;|&nbsp;
      <a href="https://app.xeny.ai/revenue-stats" style="color:#2563eb;">Live Dashboard →</a>
    </p>
  </div>
</div></body></html>"""


# ══════════════════════════════════════════════════════════════
#  DAY-ON-DAY EMAIL BUILDER  (7 AM IST daily)
# ══════════════════════════════════════════════════════════════

def _day_closing_html(yest_rows: list, d2_rows: list,
                      yest_sum: dict, d2_sum: dict) -> str:

    yest_label = yesterday()
    d2_label   = day_before()
    gen_date   = now_ist().strftime("%d %b %Y")

    # ── Platform-level numbers (summed from client rows — more reliable than summary endpoint) ──
    def _sum(rows, *keys):
        return sum(_get(r, *keys) for r in rows)

    y_sched = _sum(yest_rows, "totalCalls")
    y_conn  = _sum(yest_rows, "connectedCalls")
    y_fail  = _sum(yest_rows, "notConnectedOrFailedCalls")
    y_mins  = _sum(yest_rows, "minutesConsumed")
    y_rev   = _sum(yest_rows, "totalRevenue")

    d2_conn = _sum(d2_rows, "connectedCalls")
    d2_rev  = _sum(d2_rows, "totalRevenue")

    conn_delta = y_conn - d2_conn
    rev_delta  = y_rev  - d2_rev
    pfail_rate = round(y_fail / y_sched * 100, 1) if y_sched else 0

    conn_d_str = (f"+{conn_delta:,}" if conn_delta >= 0 else f"{conn_delta:,}")
    rev_d_str  = (f"+₹{rev_delta:,.2f}" if rev_delta >= 0 else f"-₹{abs(rev_delta):,.2f}")
    conn_col   = "#16a34a" if conn_delta >= 0 else "#dc2626"
    rev_col    = "#16a34a" if rev_delta  >= 0 else "#dc2626"

    # ── Per-client rows & anomaly flags ──
    client_rows_html = ""
    anomalies        = []

    for ac in ACTIVE_CLIENTS:
        yc = client_row(yest_rows, ac["name"])
        dc = client_row(d2_rows,   ac["name"])

        y_s  = _get(yc, "totalCalls")
        y_c  = _get(yc, "connectedCalls")
        y_f  = _get(yc, "notConnectedOrFailedCalls")
        y_m  = _get(yc, "minutesConsumed")
        y_r  = _get(yc, "totalRevenue")

        d_c  = _get(dc, "connectedCalls")
        fail = round(y_f / y_s * 100, 1) if y_s > 0 else 0

        dc_delta = y_c - d_c
        dc_str   = (f"+{dc_delta:,}" if dc_delta >= 0 else f"{dc_delta:,}")
        dc_col   = "#16a34a" if dc_delta >= 0 else "#dc2626"
        fc_col   = "#dc2626" if fail > 25 else "#374151"
        curr     = _sym(ac["currency"])

        # Status badge
        if y_s == 0 and y_c == 0:
            badge = ('<span style="background:#f3f4f6;color:#6b7280;'
                     'padding:2px 8px;border-radius:12px;font-size:11px;">NO ACTIVITY</span>')
        elif y_c == 0 and y_s > 0:
            badge = ('<span style="background:#fee2e2;color:#991b1b;'
                     'padding:2px 8px;border-radius:12px;font-size:11px;">🔴 OUTAGE</span>')
            anomalies.append(f"🔴 <strong>{ac['name']}</strong>: ZERO connected calls — possible dialer outage")
        elif fail > 50:
            badge = ('<span style="background:#fee2e2;color:#991b1b;'
                     'padding:2px 8px;border-radius:12px;font-size:11px;">HIGH FAILURE</span>')
            anomalies.append(f"⚠️ <strong>{ac['name']}</strong>: {fail}% failure rate — critical threshold exceeded")
        elif fail > 25:
            badge = ('<span style="background:#fef3c7;color:#92400e;'
                     'padding:2px 8px;border-radius:12px;font-size:11px;">ELEVATED FAIL</span>')
            anomalies.append(f"⚠️ <strong>{ac['name']}</strong>: {fail}% failure rate — above 25% threshold")
        else:
            badge = ('<span style="background:#d1fae5;color:#065f46;'
                     'padding:2px 8px;border-radius:12px;font-size:11px;">✅ NORMAL</span>')

        client_rows_html += f"""
        <tr style="border-bottom:1px solid #e5e7eb;">
          <td style="padding:12px 8px;">
            <div style="font-weight:600;color:#111827;">{ac['name']}</div>
            <div style="font-size:11px;color:#6b7280;margin-top:2px;">
              {ac['country']} &nbsp;·&nbsp; {curr}{ac['rate']}/min
            </div>
          </td>
          <td style="padding:12px 8px;text-align:center;">{y_s:,}</td>
          <td style="padding:12px 8px;text-align:center;color:#16a34a;font-weight:700;">{y_c:,}</td>
          <td style="padding:12px 8px;text-align:center;color:{fc_col};font-weight:700;">
            {y_f:,}<div style="font-size:11px;color:{fc_col};">({fail}%)</div>
          </td>
          <td style="padding:12px 8px;text-align:center;">{y_m:,}</td>
          <td style="padding:12px 8px;text-align:center;font-weight:600;">{curr}{y_r:,.2f}</td>
          <td style="padding:12px 8px;text-align:center;color:{dc_col};font-weight:700;">{dc_str}</td>
          <td style="padding:12px 8px;text-align:center;">{badge}</td>
        </tr>"""

    # Anomaly block
    anomaly_html = ""
    if anomalies:
        items = "".join(f"<li style='margin:5px 0;color:#374151;'>{a}</li>" for a in anomalies)
        anomaly_html = f"""
        <div style="background:#fef2f2;border-left:4px solid #dc2626;
                    padding:14px 18px;margin:20px 0;border-radius:4px;">
          <strong style="color:#991b1b;font-size:14px;">⚠️ Anomalies Detected on {yest_label}</strong>
          <ul style="margin:8px 0 0;padding-left:18px;font-size:13px;">{items}</ul>
        </div>"""

    return f"""
<!DOCTYPE html>
<html>
<head><meta charset="UTF-8">
<style>
  body{{font-family:Arial,Helvetica,sans-serif;background:#f3f4f6;margin:0;padding:20px;}}
  .wrap{{max-width:780px;margin:0 auto;}}
  .kpi{{flex:1;min-width:130px;border-radius:8px;padding:16px;text-align:center;}}
  .kpi-val{{font-size:26px;font-weight:700;}}
  .kpi-lbl{{font-size:11px;margin-top:3px;}}
  .kpi-delta{{font-size:12px;font-weight:600;margin-top:5px;}}
</style>
</head>
<body>
<div class="wrap">

  <!-- ── Header ── -->
  <div style="background:linear-gradient(135deg,#1e3a5f 0%,#2563eb 100%);
              color:white;padding:26px 28px;border-radius:12px 12px 0 0;">
    <div style="font-size:11px;text-transform:uppercase;letter-spacing:1px;opacity:0.75;
                margin-bottom:6px;">Technotask Business Solutions · Xeny.ai Monitor</div>
    <div style="font-size:24px;font-weight:700;">📊 Day Closing Report</div>
    <div style="font-size:13px;opacity:0.85;margin-top:6px;">
      Performance: <strong>{yest_label}</strong> vs <strong>{d2_label}</strong>
      &nbsp;|&nbsp; Auto-generated {gen_date} at 07:00 IST
    </div>
  </div>

  <!-- ── Platform KPIs ── -->
  <div style="background:white;padding:22px 24px;border-left:1px solid #e5e7eb;
              border-right:1px solid #e5e7eb;">
    <div style="font-size:11px;text-transform:uppercase;color:#6b7280;
                letter-spacing:0.5px;margin-bottom:14px;font-weight:600;">
      Platform Summary — {yest_label}
    </div>
    <div style="display:flex;gap:12px;flex-wrap:wrap;">

      <div class="kpi" style="background:#f0fdf4;border:1px solid #bbf7d0;">
        <div class="kpi-val" style="color:#15803d;">{y_conn:,}</div>
        <div class="kpi-lbl" style="color:#166534;">Connected Calls</div>
        <div class="kpi-delta" style="color:{conn_col};">{conn_d_str} vs prev day</div>
      </div>

      <div class="kpi" style="background:#fff7ed;border:1px solid #fed7aa;">
        <div class="kpi-val" style="color:#c2410c;">{y_fail:,}</div>
        <div class="kpi-lbl" style="color:#9a3412;">Failed Calls</div>
        <div class="kpi-delta" style="color:#6b7280;">{pfail_rate}% failure rate</div>
      </div>

      <div class="kpi" style="background:#eff6ff;border:1px solid #bfdbfe;">
        <div class="kpi-val" style="color:#1d4ed8;">{y_mins:,}</div>
        <div class="kpi-lbl" style="color:#1e40af;">Minutes Used</div>
        <div class="kpi-delta" style="color:#6b7280;">{y_sched:,} scheduled</div>
      </div>

      <div class="kpi" style="background:#faf5ff;border:1px solid #e9d5ff;">
        <div class="kpi-val" style="color:#7e22ce;font-size:20px;">₹{y_rev:,.2f}</div>
        <div class="kpi-lbl" style="color:#6b21a8;">Revenue (INR)</div>
        <div class="kpi-delta" style="color:{rev_col};">{rev_d_str} vs prev day</div>
      </div>

    </div>
  </div>

  {anomaly_html}

  <!-- ── Client Table ── -->
  <div style="background:white;padding:22px 24px;border:1px solid #e5e7eb;
              {'margin-top:2px;' if not anomalies else ''}">
    <div style="font-size:11px;text-transform:uppercase;color:#6b7280;
                letter-spacing:0.5px;margin-bottom:14px;font-weight:600;">
      Active Client Breakdown &nbsp;
      <span style="font-weight:400;text-transform:none;">
        Day-on-Day: {yest_label} vs {d2_label}
      </span>
    </div>
    <table width="100%" cellspacing="0"
           style="border-collapse:collapse;font-size:13px;color:#374151;">
      <thead>
        <tr style="background:#f8fafc;font-size:11px;text-transform:uppercase;
                   color:#475569;letter-spacing:0.3px;">
          <th style="padding:10px 8px;text-align:left;border-bottom:2px solid #e5e7eb;">Client</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Sched</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Connected</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Failed</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Minutes</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Revenue</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Δ Calls</th>
          <th style="padding:10px 8px;text-align:center;border-bottom:2px solid #e5e7eb;">Status</th>
        </tr>
      </thead>
      <tbody>
        {client_rows_html}
      </tbody>
    </table>
    <p style="font-size:11px;color:#9ca3af;margin:12px 0 0;">
      * Excluded (zero calls ≥1 month): Success Resources · Zenfone · EBMS · Connection Uniform
    </p>
  </div>

  <!-- ── Footer ── -->
  <div style="background:#1e293b;color:#94a3b8;padding:16px 22px;
              border-radius:0 0 12px 12px;font-size:12px;line-height:1.7;">
    <span style="color:white;font-weight:600;">Xeny.ai Auto-Monitor</span>
    &nbsp;·&nbsp; Technotask Business Solutions &nbsp;·&nbsp; Report date: {yest_label}<br>
    <a href="https://app.xeny.ai/revenue-stats" style="color:#60a5fa;text-decoration:none;">
      View Live Dashboard →
    </a>
    &nbsp;&nbsp;
    <a href="https://app.xeny.ai/super-admin/dashboard" style="color:#60a5fa;text-decoration:none;">
      Super Admin →
    </a><br>
    <span style="font-size:11px;opacity:0.6;">Auto-generated. Do not reply.</span>
  </div>

</div>
</body>
</html>"""


# ══════════════════════════════════════════════════════════════
#  HEARTBEAT EMAIL
# ══════════════════════════════════════════════════════════════

def _heartbeat_html() -> str:
    ts = now_ist().strftime("%d %b %Y, %I:%M %p IST")
    return f"""
<!DOCTYPE html><html><head><meta charset="UTF-8"></head>
<body style="font-family:Arial,sans-serif;background:#f0fdf4;margin:0;padding:30px;">
<div style="max-width:480px;margin:0 auto;background:white;border:1px solid #bbf7d0;
            border-radius:10px;overflow:hidden;">
  <div style="background:#15803d;padding:16px 20px;">
    <span style="color:white;font-size:16px;font-weight:700;">✅ Xeny Monitor — System Alive</span>
  </div>
  <div style="padding:20px;font-size:14px;color:#374151;line-height:1.7;">
    Your Xeny.ai monitoring script is running normally.<br><br>
    <strong>Timestamp:</strong> {ts}<br>
    <strong>Polling:</strong> Every 15 minutes · 8 AM – 10 PM IST<br>
    <strong>Day closing email:</strong> 07:00 AM IST daily<br>
    <strong>Monitored clients:</strong> OffDuty, Blue Tyga Fashions, Sikka Estate,
      Century Express, Edument Education<br><br>
    <a href="https://app.xeny.ai/revenue-stats" style="color:#2563eb;">
      View Live Dashboard →
    </a>
  </div>
  <div style="background:#f9fafb;padding:10px 20px;font-size:11px;color:#9ca3af;">
    Auto-generated heartbeat · Technotask Business Solutions
  </div>
</div>
</body></html>"""


# ══════════════════════════════════════════════════════════════
#  SCHEDULED JOBS
# ══════════════════════════════════════════════════════════════

def _monitor_down_html() -> str:
    """FIX V-3: Email body sent when the monitor itself cannot fetch data."""
    ts = now_ist().strftime("%d %b %Y, %I:%M %p IST")
    return f"""<!DOCTYPE html><html><head><meta charset="UTF-8"></head>
<body style="font-family:Arial,sans-serif;background:#fef2f2;margin:0;padding:30px;">
<div style="max-width:500px;margin:0 auto;background:white;border:1px solid #fca5a5;
  border-radius:10px;overflow:hidden;">
  <div style="background:#dc2626;padding:16px 20px;">
    <span style="color:white;font-size:16px;font-weight:700;">
      XENY MONITOR — Self-Check Failed
    </span>
  </div>
  <div style="padding:20px;font-size:14px;color:#374151;line-height:1.8;">
    The monitoring script ran at <strong>{ts}</strong> but could NOT
    fetch data from Xeny.ai. No alert checks were performed this cycle.<br><br>
    <strong>Possible causes:</strong><br>
    &bull; Xeny.ai login credentials have expired or changed<br>
    &bull; Xeny.ai platform is down or unreachable<br>
    &bull; GitHub Actions network issue<br>
    &bull; Xeny.ai changed their internal API structure<br><br>
    <strong>Action required:</strong><br>
    1. Log in to app.xeny.ai and verify the platform is up.<br>
    2. Check GitHub Actions logs for the specific error message.<br>
    3. Verify XENY_EMAIL and XENY_PASSWORD secrets are still valid.
  </div>
  <div style="background:#f9fafb;padding:10px 20px;font-size:11px;color:#9ca3af;">
    Auto-generated self-check alert · Technotask Business Solutions
  </div>
</div>
</body></html>"""


def job_poll():
    """15-minute polling job — alert on anomalies during business hours."""
    h = now_ist().hour
    if not (BUSINESS_START <= h < BUSINESS_END):
        log.info(f"⏸  Outside business hours ({h:02d}:xx IST) — poll skipped")
        return

    log.info("🔍 Poll starting ...")
    td   = today()
    yd   = yesterday()
    t_rows = fetch_clients(td, td, "today")
    d1_rows = fetch_clients(yd, yd, "yesterday")

    if not t_rows:
        log.warning("No client data returned — possible auth or network issue")
        # FIX V-3: Alert when the monitor itself cannot fetch data.
        # 2-hour cooldown prevents email flooding if issue persists across many polls.
        if _can_alert("MONITOR_SELF_DOWN"):
            send_email(
                "⚠️ ALERT: Xeny Monitor Failed to Fetch Data — Check Credentials",
                _monitor_down_html()
            )
        return

    # ── Platform-wide outage check ──
    active_today = [r for r in t_rows if any(_match(r, n) for n in ACTIVE_NAMES)]

    # FIX V-1: Correct logic — outage = ANY client has scheduled calls but
    # ALL connected calls across active clients are zero.
    # Previous code checked all_zero (both scheduled AND connected = 0),
    # which created a logical impossibility with the not all_scheduled_zero guard.
    any_have_scheduled = any(_get(r, "totalCalls") > 0 for r in active_today)
    all_connected_zero = all(_get(r, "connectedCalls") == 0 for r in active_today)
    if active_today and any_have_scheduled and all_connected_zero and _can_alert("PLATFORM_OUTAGE"):
        html = _alert_html(t_rows, d1_rows, "CRITICAL",
            "🚨 ALL active clients showing ZERO connected calls despite scheduled campaigns — "
            "Possible platform-wide dialer failure")
        send_email("🚨 PLATFORM OUTAGE: All Xeny.ai clients at ZERO calls", html)
        log.warning("CRITICAL: Platform-wide zero-call alert fired")
        return  # No need to check per-client if platform is fully down

    # ── Per-client checks ──
    for ac in ACTIVE_CLIENTS:
        name   = ac["name"]
        tc     = client_row(t_rows, name)
        dc     = client_row(d1_rows, name)

        t_conn  = _get(tc, "connectedCalls")
        t_sched = _get(tc, "totalCalls")
        t_fail  = _get(tc, "notConnectedOrFailedCalls")
        d1_conn = _get(dc, "connectedCalls")
        fail_pct = round(t_fail / t_sched * 100, 1) if t_sched else 0

        # ── Zero call tracker ──
        if t_conn == 0 and t_sched > 0:
            _zero_counts[name] = _zero_counts.get(name, 0) + 1
            log.info(f"  {name}: zero calls — count {_zero_counts[name]}")
        else:
            _zero_counts[name] = 0

        if _zero_counts.get(name, 0) >= ZERO_CALL_ALERT_CHECKS:
            if _can_alert(f"ZERO_{name}"):
                mins = _zero_counts[name] * POLL_INTERVAL_MIN
                html = _alert_html(t_rows, d1_rows, "CRITICAL",
                    f"🔴 {name} has had ZERO connected calls for {mins} minutes "
                    f"({t_sched} calls scheduled, all failing) — possible dialer issue")
                send_email(f"🔴 CRITICAL: {name} — ZERO calls for {mins} min", html)

        # ── Volume drop vs D-1 ──
        if d1_conn > 0:
            drop_pct = round((1 - t_conn / d1_conn) * 100)
            if drop_pct >= VOLUME_DROP_PCT and _can_alert(f"DROP_{name}"):
                html = _alert_html(t_rows, d1_rows, "WARNING",
                    f"⚠️ {name}: Call volume is {drop_pct}% below yesterday — "
                    f"{t_conn:,} today vs {d1_conn:,} yesterday (same day)")
                send_email(f"⚠️ WARNING: {name} — {drop_pct}% volume drop vs yesterday", html)

        # ── High failure rate ──
        if t_sched >= 10 and fail_pct > FAILURE_RATE_ALERT_PCT:
            severity = "CRITICAL" if fail_pct > 50 else "WARNING"
            if _can_alert(f"FAIL_{name}"):
                html = _alert_html(t_rows, d1_rows, severity,
                    f"{severity}: {name} — {fail_pct}% call failure rate "
                    f"({t_fail:,} of {t_sched:,} calls not connecting)")
                send_email(f"{'🔴' if severity=='CRITICAL' else '⚠️'} {severity}: "
                           f"{name} — {fail_pct}% failure rate", html)

    log.info(f"✅ Poll done — {len(t_rows)} clients checked")


def job_day_closing():
    """Runs at 7:00 AM IST — fetch yesterday vs day-before, build & send email."""
    log.info("📊 Day closing email job starting ...")

    yd  = yesterday()
    d2  = day_before()
    y_rows  = fetch_clients(yd, yd, "yesterday")
    d2_rows = fetch_clients(d2, d2, "custom")
    y_sum   = fetch_summary(yd, yd, "yesterday")
    d2_sum  = fetch_summary(d2, d2, "custom")

    if not y_rows:
        log.warning("Day closing: no data for yesterday — email skipped")
        return

    html = _day_closing_html(y_rows, d2_rows, y_sum, d2_sum)
    send_email(f"📊 Xeny Day Closing — {yd} | Day-on-Day Report", html)


def job_heartbeat():
    """Runs at 9:00 AM IST — confirms script is still alive."""
    log.info("💓 Heartbeat email ...")
    send_email("✅ Xeny Monitor Alive — Daily Heartbeat", _heartbeat_html())


# ══════════════════════════════════════════════════════════════
#  STATE PERSISTENCE  (for GitHub Actions between runs)
# ══════════════════════════════════════════════════════════════

STATE_FILE = "state.json"

def load_state():
    """Load persisted zero-counts and alert-log from previous run."""
    global _zero_counts, _alert_log
    try:
        if os.path.exists(STATE_FILE):
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                s = json.load(f)
            _zero_counts = s.get("zero_counts", {})
            _alert_log   = {
                k: IST.localize(datetime.fromisoformat(v)) if datetime.fromisoformat(v).tzinfo is None
                   else datetime.fromisoformat(v)
                for k, v in s.get("alert_log", {}).items()
            }
            log.info(f"  State loaded — {len(_zero_counts)} client counters, {len(_alert_log)} alert keys")
    except Exception as e:
        log.warning(f"  State load skipped: {e}")

def save_state():
    """Persist state so the next GitHub Actions run continues from here."""
    try:
        with open(STATE_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "zero_counts": _zero_counts,
                "alert_log":   {k: v.isoformat() for k, v in _alert_log.items()},
            }, f, indent=2)
        log.info("  State saved.")
    except Exception as e:
        log.warning(f"  State save failed: {e}")


# ══════════════════════════════════════════════════════════════
#  MAIN
# ══════════════════════════════════════════════════════════════

def main():
    ap = argparse.ArgumentParser(description="Xeny.ai Monitor")
    ap.add_argument(
        "--mode",
        choices=["daemon", "poll", "dayclosing"],
        default="daemon",
        help="daemon=run forever (laptop)  poll=single poll & exit (GitHub Actions)  dayclosing=send report & exit"
    )
    args = ap.parse_args()

    log.info("=" * 62)
    log.info("  Xeny.ai Monitor — Technotask Business Solutions")
    log.info(f"  Mode: {args.mode.upper()}")
    log.info("=" * 62)

    # Validate environment variables
    missing = [v for v in ("XENY_EMAIL", "XENY_PASSWORD", "SMTP_EMAIL", "SMTP_PASSWORD")
               if not os.environ.get(v)]
    if missing:
        log.error(f"❌ Missing environment variables: {', '.join(missing)}")
        sys.exit(1)

    # Login + auth setup (required for all modes)
    if not login():
        log.error("❌ Cannot start — initial login failed. Check credentials.")
        sys.exit(1)
    if not _setup_data_page():
        log.error("❌ Cannot start — data page setup failed.")
        sys.exit(1)

    load_state()

    # ── GitHub Actions single-run modes ──
    if args.mode == "poll":
        job_poll()
        save_state()
        return

    if args.mode == "dayclosing":
        job_day_closing()
        return

    # ── Daemon mode: runs forever on laptop ──
    # Register jobs
    schedule.every(POLL_INTERVAL_MIN).minutes.do(job_poll)
    schedule.every().day.at("07:00").do(job_day_closing)
    schedule.every().day.at("09:00").do(job_heartbeat)

    # Fire immediately on startup
    log.info("⚡ Running startup checks ...")
    job_poll()
    job_heartbeat()

    log.info(f"✅ Scheduler running — polling every {POLL_INTERVAL_MIN} min. Press Ctrl+C to stop.")
    log.info("   Day closing email: 07:00 AM IST daily")
    log.info("   Heartbeat email:   09:00 AM IST daily")
    log.info("-" * 62)

    while True:
        try:
            schedule.run_pending()
            time.sleep(30)
        except KeyboardInterrupt:
            log.info("⛔ Monitor stopped by user.")
            sys.exit(0)
        except Exception as exc:
            log.error(f"Scheduler error: {exc}")
            time.sleep(60)  # brief pause before retrying


if __name__ == "__main__":
    main()
