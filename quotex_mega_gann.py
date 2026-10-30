#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Quotex Mega Fetcher — Full-Featured Candle + Profit + Live Price Engine
=======================================================================
A complete port of the working `wedsoket_.py` engine, but focused on what
the user actually needs for the competition:

  1. EXACTLY 500 candles per asset for all 13 OTC pairs (M1 default).
  2. PROFIT/PAYOUT percentage fetched from instruments/list (binary frame).
  3. GAP-FILLING via _fill_missing_slots (verbatim port).
  4. LIVE PRICE via subscribe_realtime_candle + depth/follow + quotes/stream.
  5. NEVER-SLEEP engine: keepalive_loop + stale_message_watchdog + auto_reconnect
     + health_monitor running concurrently in background.

ARCHITECTURE
------------
  - Reuses the Quotex client from OTC_canda_.py for connection / auth / WS.
  - Installs interceptors on WebsocketClient.on_message to capture:
      (a) binary instruments/list frames (JSON, 0x04-prefixed)
      (b) live tick arrays (quotes/stream, depth/change)
      (c) historical candle responses (history/load, history/list/v2)
  - Runs four background asyncio tasks:
      (i)   keepalive_loop: ping every 5s
      (ii)  stale_message_watchdog: detect silent connection (45s)
      (iii) auto_reconnect: rebuild connection on loss (exponential backoff)
      (iv)  health_monitor: periodic state check (20s)
  - Fetch logic uses overlapping chunks (60 candles, 10 overlap) + dedup +
    gap-fill + truncate/pad to exactly 500.

USAGE
-----
    python3 mega_fetch.py

After login, the script:
  1. Fetches the instruments list (to get profit % per asset).
  2. Subscribes to live price for all 13 OTC pairs.
  3. Fetches exactly 500 candles per asset (gap-filled).
  4. Saves results to candles_otc_data/{asset}_1m_500c_{8-hex}.json

OUTPUT
------
    candles_otc_data/{asset}_{tf}m_500c_{8-hex}.json
"""

# ============================================================================
# SECTION 0: STANDARD LIBRARY IMPORTS
# ============================================================================
import os
import sys
import ssl
import json
import time
import random
import re
import shutil
import logging
import asyncio
import threading
import traceback
import itertools
import contextlib
import platform
from pathlib import Path
from datetime import datetime, timezone, timedelta
from collections import defaultdict, OrderedDict, deque
from enum import IntEnum
from typing import Any, Callable, Dict, List, Optional, Tuple, Union
from dataclasses import dataclass, field

# Third-party dependencies (required by the Quotex connection engine)
import certifi
import requests
import websocket
from requests import Session
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup
from fake_useragent import UserAgent

try:
    import orjson as _orjson
    HAS_ORJSON = True
except ImportError:
    _orjson = None
    HAS_ORJSON = False

# ============================================================================

# ============================================================================
# SECTION 1: QUOTEX CONNECTION ENGINE (embedded — no external file needed)
# ============================================================================
# This section contains the FULL Quotex connection engine, ported verbatim
# from OTC_canda_.py. It includes:
#   - SSL setup + logging
#   - Event-driven wait primitives
#   - HTTP Navigator (CipherSuiteAdapter, Browser)
#   - HTTP Login & Settings
#   - WebSocket Client & State
#   - Quotex API Core (QuotexAPI class)
#   - Candle parsing helpers
#   - Quotex stable API class (with get_historical_candles)
#   - Helper utilities (logmsg, Colors, credentials, save_candles_to_json)
#   - keepalive_loop + auto_reconnect_loop + connect_quotex
#
# By embedding this code directly, mega_fetch.py is now a SINGLE-FILE solution
# that does NOT require OTC_canda_.py to be present in the same folder.

# SECTION 1: LOGGING & SSL SETUP
# ==============================================================================
def _prepare_logging():
    logger = logging.getLogger(__name__)
    logger.addHandler(logging.NullHandler())
    websocket_logger = logging.getLogger("websocket")
    websocket_logger.setLevel(logging.INFO)
    websocket_logger.addHandler(logging.NullHandler())

_prepare_logging()
logger = logging.getLogger(__name__)

cert_path = certifi.where()
os.environ['SSL_CERT_FILE'] = cert_path
os.environ['WEBSOCKET_CLIENT_CA_BUNDLE'] = cert_path
cacert = os.environ.get('WEBSOCKET_CLIENT_CA_BUNDLE')

ssl_context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
ssl_context.minimum_version = ssl.TLSVersion.TLSv1_2
ssl_context.load_verify_locations(cert_path)


# ==============================================================================
# SECTION 1.5: EVENT-DRIVEN WAIT PRIMITIVES
# ==============================================================================
async def wait_until(predicate: Callable[[], bool], *, timeout: float = 10.0,
                      poll_interval: float = 0.05) -> None:
    """يستدعي predicate() كل poll_interval ثانية حتى يُعيد True أو ينتهي timeout."""
    async def _loop():
        while not predicate():
            await asyncio.sleep(poll_interval)
    await asyncio.wait_for(_loop(), timeout=timeout)


async def wait_for_first_event(*events: asyncio.Event, timeout: float = 10.0) -> int:
    """ينتظر أول event يُطلق من القائمة ويعيد indexه. يطلق TimeoutError عند المهلة."""
    if not events:
        raise ValueError("wait_for_first_event requires at least one event")
    tasks = [asyncio.ensure_future(e.wait()) for e in events]
    try:
        done, pending = await asyncio.wait(tasks, timeout=timeout,
                                           return_when=asyncio.FIRST_COMPLETED)
        for t in pending:
            t.cancel()
        for i, t in enumerate(tasks):
            if t in done and t.result() and not t.cancelled():
                return i
        raise asyncio.TimeoutError()
    except asyncio.CancelledError:
        for t in tasks:
            if not t.done():
                t.cancel()
        raise


def _schedule_event_set(event: Optional[asyncio.Event],
                        loop: Optional[asyncio.AbstractEventLoop]) -> None:
    if event is None or loop is None:
        return
    try:
        if not loop.is_closed() and loop.is_running():
            loop.call_soon_threadsafe(event.set)
    except RuntimeError:
        pass


# ==============================================================================
# SECTION 2: CONSTANTS & SESSION
# ==============================================================================
USER_AGENT = "Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:109.0) Gecko/20100101 Firefox/119.0"
base_dir = Path.cwd()
session_lock = threading.Lock()


def resource_path(relative_path: str) -> Path:
    global base_dir
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        base_dir = Path(sys._MEIPASS)
    return base_dir / relative_path


def load_session(email: str, user_agent: str = None) -> dict:
    if user_agent is None:
        try:
            user_agent = UserAgent().random
        except Exception:
            user_agent = USER_AGENT
    output_file = Path(resource_path("session.json"))
    with session_lock:
        all_sessions = {}
        if output_file.exists():
            try:
                all_sessions = json.loads(output_file.read_text())
            except json.JSONDecodeError:
                pass
        else:
            output_file.parent.mkdir(exist_ok=True, parents=True)
        if email not in all_sessions:
            all_sessions[email] = {"cookies": None, "token": None, "user_agent": user_agent}
        output_file.write_text(json.dumps(all_sessions, indent=4))
        return all_sessions.get(email)


def update_session(email: str, d: dict) -> dict:
    output_file = Path(resource_path("session.json"))
    with session_lock:
        current_sessions = {}
        if output_file.exists():
            try:
                current_sessions = json.loads(output_file.read_text())
            except json.JSONDecodeError:
                pass
        else:
            output_file.parent.mkdir(exist_ok=True, parents=True)
        current_sessions[email] = d
        output_file.write_text(json.dumps(current_sessions, indent=4))
        return current_sessions.get(email)


# ==============================================================================
# SECTION 3: HTTP NAVIGATOR (PROVEN WORKING METHOD)
# ==============================================================================
retry_strategy = Retry(
    total=3, backoff_factor=1,
    status_forcelist=[429, 500, 502, 503, 504, 104],
    allowed_methods=["HEAD", "POST", "PUT", "GET", "OPTIONS"],
)


class CipherSuiteAdapter(HTTPAdapter):
    __attrs__ = ['ssl_context', 'max_retries', 'config', '_pool_connections',
                 '_pool_maxsize', '_pool_block', 'source_address']

    def __init__(self, *args, **kwargs):
        self.ssl_context = kwargs.pop('ssl_context', None)
        self.cipherSuite = kwargs.pop('cipherSuite',
            'ECDHE-ECDSA-AES128-GCM-SHA256:ECDHE-RSA-AES128-GCM-SHA256:'
            'ECDHE-ECDSA-AES256-GCM-SHA384:ECDHE-RSA-AES256-GCM-SHA384:'
            'ECDHE-ECDSA-CHACHA20-POLY1305:ECDHE-RSA-CHACHA20-POLY1305:'
            'DHE-RSA-AES128-GCM-SHA256:DHE-RSA-AES256-GCM-SHA384')
        self.source_address = kwargs.pop('source_address', None)
        self.server_hostname = kwargs.pop('server_hostname', None)
        self.ecdhCurve = kwargs.pop('ecdhCurve', 'prime256v1')
        if not self.ssl_context:
            self.ssl_context = ssl.create_default_context(ssl.Purpose.SERVER_AUTH)
            self.ssl_context.orig_wrap_socket = self.ssl_context.wrap_socket
            self.ssl_context.wrap_socket = self.wrap_socket
        if self.server_hostname:
            self.ssl_context.server_hostname = self.server_hostname
        if self.cipherSuite:
            self.ssl_context.set_ciphers(self.cipherSuite)
            self.ssl_context.set_ecdh_curve(self.ecdhCurve)
            self.ssl_context.minimum_version = ssl.TLSVersion.TLSv1_2
            self.ssl_context.maximum_version = ssl.TLSVersion.TLSv1_3
        super().__init__(**kwargs)

    def wrap_socket(self, *args, **kwargs):
        if hasattr(self.ssl_context, 'server_hostname') and self.ssl_context.server_hostname:
            kwargs['server_hostname'] = self.ssl_context.server_hostname
            self.ssl_context.check_hostname = False
        else:
            self.ssl_context.check_hostname = True
        return self.ssl_context.orig_wrap_socket(*args, **kwargs)

    def init_poolmanager(self, *args, **kwargs):
        kwargs['ssl_context'] = self.ssl_context
        kwargs['source_address'] = self.source_address
        return super().init_poolmanager(*args, **kwargs)


class Browser(Session):
    def __init__(self, *args, **kwargs):
        self.response = None
        self.default_headers = None
        self.ecdhCurve = kwargs.pop('ecdhCurve', 'prime256v1')
        self.cipherSuite = kwargs.pop('cipherSuite',
            'ECDHE-ECDSA-AES128-GCM-SHA256:ECDHE-RSA-AES128-GCM-SHA256:'
            'ECDHE-ECDSA-AES256-GCM-SHA384:ECDHE-RSA-AES256-GCM-SHA384:'
            'ECDHE-ECDSA-CHACHA20-POLY1305:ECDHE-RSA-CHACHA20-POLY1305:'
            'DHE-RSA-AES128-GCM-SHA256:DHE-RSA-AES256-GCM-SHA384')
        self.source_address = kwargs.pop('source_address', None)
        self.server_hostname = kwargs.pop('server_hostname', None)
        # استخرج proxies قبل super().__init__ (الذي يعيد ضبط self.proxies إلى {})
        _proxies = kwargs.pop('proxies', None)
        super().__init__(*args, **kwargs)
        # اضبط proxies بعد super().__init__ حتى لا تُكتب فوقها بـ {}
        # هذا يحل المشكلة: send_request يفحص self.proxies لكن Session.__init__ يفرغها
        self.proxies = _proxies
        self.headers.update(self.get_headers())
        self.mount('https://', CipherSuiteAdapter(
            ecdhCurve=self.ecdhCurve, cipherSuite=self.cipherSuite,
            server_hostname=self.server_hostname, source_address=self.source_address,
            ssl_context=ssl_context, max_retries=retry_strategy))

    def __enter__(self): return self
    def __exit__(self, exc_type, exc_val, exc_tb): self.close()
    async def __aenter__(self): return self
    async def __aexit__(self, exc_type, exc_val, exc_tb): self.__exit__(exc_type, exc_val, exc_tb)

    def get_headers(self):
        self.default_headers = {"User-Agent": USER_AGENT}
        return self.default_headers

    def set_headers(self, headers=None):
        self.headers.update(self.default_headers)
        if headers: self.headers.update(headers)

    def get_cookies(self):
        return '; '.join(f'{i.name}={i.value}' for i in self.cookies)

    def get_soup(self):
        if self.response and not self.response.ok:
            raise RuntimeError(self.response.reason)
        return BeautifulSoup(self.response.content, "html.parser")

    def send_request(self, method, url, headers=None, **kwargs):
        merged_headers = self.headers.copy()
        if headers: merged_headers.update(headers)
        if self.proxies: kwargs['proxies'] = self.proxies
        self.response = self.request(method, url, headers=merged_headers, **kwargs)
        return self.response


# ==============================================================================
# SECTION 4: HTTP LOGIN & SETTINGS
# ==============================================================================
class Login(Browser):
    url = ""
    cookies = None
    ssid = None
    base_url = 'quotex.com'  # <--- تم التحديث هنا
    https_base_url = f'https://{base_url}'

    def __init__(self, api, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.api = api
        self.headers = self.get_headers()
        self.full_url = f"{self.https_base_url}/{api.lang}"

    def get_token(self):
        self.headers["Connection"] = "keep-alive"
        self.headers["Accept-Encoding"] = "gzip, deflate, br"
        self.headers["Accept-Language"] = "pt-BR,pt;q=0.8,en-US;q=0.5,en;q=0.3"
        self.headers["Accept"] = ("text/html,application/xhtml+xml,application/xml;q=0.9,"
                                  "image/avif,image/webp,*/*;q=0.8")
        self.headers["Referer"] = f"{self.full_url}/sign-in"
        self.headers["Upgrade-Insecure-Requests"] = "1"
        self.headers["Sec-Ch-Ua-Mobile"] = "?0"
        self.headers["Sec-Ch-Ua-Platform"] = '"Linux"'
        self.headers["Sec-Fetch-Site"] = "same-origin"
        self.headers["Sec-Fetch-User"] = "?1"
        self.headers["Sec-Fetch-Dest"] = "document"
        self.headers["Sec-Fetch-Mode"] = "navigate"
        self.headers["Dnt"] = "1"
        self.send_request("GET", f"{self.full_url}/sign-in/modal/")
        html = self.get_soup()
        match = html.find("input", {"name": "_token"})
        return None if not match else match.get("value")

    async def awaiting_pin(self, data, input_message):
        self.headers["Content-Type"] = "application/x-www-form-urlencoded"
        self.headers["Referer"] = f"{self.full_url}/sign-in/modal"
        data["keep_code"] = 1
        try:
            code = input(input_message)
            if not code.isdigit():
                print("Please enter a valid code.")
                await self.awaiting_pin(data, input_message)
            data["code"] = code
        except KeyboardInterrupt:
            print("\nClosing program.")
            sys.exit()
        await asyncio.sleep(1)
        self.send_request(method="POST", url=f"{self.full_url}/sign-in/modal", data=data)

    def get_profile(self):
        self.response = self.send_request(method="GET", url=f"{self.full_url}/trade")
        if self.response:
            script = self.get_soup().find_all("script", {"type": "text/javascript"})
            script = script[0].get_text() if script else "{}"
            match = script.strip().replace(";", "").replace("window.settings = ", "")
            self.cookies = self.get_cookies()
            try:
                settings_dict = json.loads(match)
                self.ssid = settings_dict.get("token")
            except json.JSONDecodeError:
                self.ssid = None
            self.api.session_data["cookies"] = self.cookies
            self.api.session_data["token"] = self.ssid
            self.api.session_data["user_agent"] = self.headers["User-Agent"]
            update_session(self.api.username, self.api.session_data)
            return self.response, settings_dict if self.ssid else None
        return None, None

    async def _post(self, data):
        self.response = self.send_request(method="POST", url=f"{self.full_url}/sign-in/", data=data)
        required_keep_code = self.get_soup().find("input", {"name": "keep_code"})
        if required_keep_code:
            auth_body = self.get_soup().find("main", {"class": "auth__body"})
            input_message = (f'{auth_body.find("p").text}: '
                             if auth_body.find("p")
                             else "Enter the PIN code sent to your email: ")
            await self.awaiting_pin(data, input_message)
            await asyncio.sleep(1)
            return self.success_login()
        return self.success_login()

    def success_login(self):
        if "trade" in str(self.response.url):
            return True, "Login successful."
        soup = self.get_soup()
        not_available = soup.select_one("#tab-1 > div > div.modal-sign__not-avalible__title")
        if not_available:
            return False, f"Service unavailable: {not_available.get_text(strip=True)}"
        error = soup.select_one("#tab-1 form > div:nth-child(2) > div")
        msg = error.get_text(strip=True) if error else "Unknown error"
        return False, f"Login failed. {msg}"

    async def __call__(self, username, password, user_data_dir=None):
        data = {"_token": self.get_token(), "email": username,
                "password": password, "remember": 1}
        status, msg = await self._post(data)
        if status:
            self.get_profile()
        return status, msg


class Settings(Browser):
    def __init__(self, api):
        # مرّر proxies من api إلى Settings
        proxies_dict = api._normalize_proxies(api.proxies) if hasattr(api, '_normalize_proxies') else None
        super().__init__(proxies=proxies_dict)
        self.set_headers()
        self.api = api
        self.headers = self.get_headers()

    def get_settings(self):
        self.headers["content-type"] = "application/json"
        self.headers["referer"] = f"{self.api.https_url}/{self.api.lang}/trade"
        self.headers["cookie"] = self.api.session_data.get("cookies", "")
        self.headers["user-agent"] = self.api.session_data.get("user_agent", "")
        response = self.send_request("GET", f"{self.api.https_url}/api/v1/cabinets/digest")
        return response.json()


# ==============================================================================
# SECTION 5: WEBSOCKET CLIENT & STATE
# ==============================================================================
class WebsocketStatus(IntEnum):
    DISCONNECTED = 0
    CONNECTED = 1
    CONNECTING = 2
    ERROR = -1


class AuthStatus(IntEnum):
    NOT_AUTHENTICATED = 0
    AUTHENTICATING = 1
    AUTHENTICATED = 2
    FAILED = -1


class ConnectionState:
    def __init__(self):
        self.SSID = None
        self.status = WebsocketStatus.DISCONNECTED
        self.auth_status = AuthStatus.NOT_AUTHENTICATED
        self.ssl_Mutual_exclusion = False
        self.ssl_Mutual_exclusion_write = False
        self.check_rejected_connection = False
        self.check_accepted_connection = False
        self.check_websocket_if_error = False
        self.check_websocket_if_connect = None
        self.websocket_error_reason = None
        # EVENT-DRIVEN: تُهيّأ lazily من async context
        self.ws_connected_event: Optional[asyncio.Event] = None
        self.ws_closed_event: Optional[asyncio.Event] = None
        self.auth_accepted_event: Optional[asyncio.Event] = None
        self.auth_rejected_event: Optional[asyncio.Event] = None
        self.ws_error_event: Optional[asyncio.Event] = None
        self._loop: Optional[asyncio.AbstractEventLoop] = None

    def init_events(self) -> None:
        if self.ws_connected_event is None: self.ws_connected_event = asyncio.Event()
        if self.ws_closed_event is None: self.ws_closed_event = asyncio.Event()
        if self.auth_accepted_event is None: self.auth_accepted_event = asyncio.Event()
        if self.auth_rejected_event is None: self.auth_rejected_event = asyncio.Event()
        if self.ws_error_event is None: self.ws_error_event = asyncio.Event()
        try:
            self._loop = asyncio.get_running_loop()
        except RuntimeError:
            self._loop = None

    def reset_events(self) -> None:
        for ev in (self.ws_connected_event, self.ws_closed_event,
                   self.auth_accepted_event, self.auth_rejected_event,
                   self.ws_error_event):
            if ev is not None:
                ev.clear()

    def signal_ws_connected(self): _schedule_event_set(self.ws_connected_event, self._loop)
    def signal_ws_closed(self): _schedule_event_set(self.ws_closed_event, self._loop)
    def signal_auth_accepted(self): _schedule_event_set(self.auth_accepted_event, self._loop)
    def signal_auth_rejected(self): _schedule_event_set(self.auth_rejected_event, self._loop)
    def signal_ws_error(self): _schedule_event_set(self.ws_error_event, self._loop)


class WebsocketClient:
    def __init__(self, api):
        self.api = api
        self.state = api.state
        self.headers = {
            "User-Agent": self.api.session_data.get("user_agent", USER_AGENT),
            "Origin": self.api.https_url,
            "Host": f"ws2.{self.api.host}",
        }
        self.wss = websocket.WebSocketApp(
            self.api.wss_url,
            on_message=self.on_message,
            on_error=self.on_error,
            on_close=self.on_close,
            on_open=self.on_open,
            on_ping=self.on_ping,
            on_pong=self.on_pong,
            header=self.headers,
            cookie=self.api.session_data.get("cookies"),
        )

    def on_message(self, wss, msg):
        self.state.ssl_Mutual_exclusion = True
        try:
            if self.api is not None:
                self.api.last_message_at = time.time()
            msg_str = msg.decode("utf-8", errors="ignore") if isinstance(msg, bytes) else str(msg)

            if msg_str == "2":
                try:
                    self.wss.send("3")
                except Exception:
                    pass
                self.state.ssl_Mutual_exclusion = False
                return
            if msg_str == "3":
                self.state.ssl_Mutual_exclusion = False
                return

            if "authorization/reject" in msg_str:
                logger.warning("Token rejected.")
                self.state.check_rejected_connection = True
                self.state.auth_status = AuthStatus.FAILED
                self.state.signal_auth_rejected()
            elif "s_authorization" in msg_str:
                self.state.check_accepted_connection = True
                self.state.check_rejected_connection = False
                self.state.auth_status = AuthStatus.AUTHENTICATED
                self.state.status = WebsocketStatus.CONNECTED
                self.state.signal_auth_accepted()

            message = None
            if len(msg_str) > 1 and msg_str[1] in ('[', '{'):
                try:
                    message = json.loads(msg_str[1:])
                except Exception:
                    pass

            if message is not None:
                self._process_message_and_raise_events(message)

            if str(msg_str) == "41":
                self.state.check_websocket_if_connect = 0
        except Exception as e:
            logger.error("Unhandled error in on_message: %s", e)
        self.state.ssl_Mutual_exclusion = False

    def _process_message_and_raise_events(self, message):
        try:
            loop = self.api._async_loop
            if loop is None or not loop.is_running():
                return
            if isinstance(message, dict):
                asset = message.get("asset")
                if asset and (message.get("candles") or message.get("data") or message.get("history")):
                    self.api.candle_v2_data[asset] = message
                    self.api.candles.candles_data = (message.get("candles")
                                                    or message.get("data")
                                                    or message.get("history"))
                    asyncio.run_coroutine_threadsafe(
                        self.api.event_registry.set_event(f'candles_ready_{asset}', message),
                        loop)
                    index = message.get("index")
                    if index is not None:
                        asyncio.run_coroutine_threadsafe(
                            self.api.event_registry.set_event(f'candles_ready_{asset}_{index}', message),
                            loop)
            if isinstance(message, dict) and (message.get("liveBalance") or message.get("demoBalance")):
                self.api.account_balance = message
        except Exception as e:
            logger.debug(f"Error processing message: {e}")

    def on_error(self, wss, error):
        logger.error(error)
        self.state.websocket_error_reason = str(error)
        self.state.check_websocket_if_error = True
        self.state.status = WebsocketStatus.ERROR
        self.state.check_accepted_connection = False
        self.state.signal_ws_error()

    def on_open(self, wss):
        logger.info("Websocket client connected.")
        self.state.check_websocket_if_connect = 1
        self.state.status = WebsocketStatus.CONNECTED
        self.state.signal_ws_connected()
        asset_name = self.api.current_asset or "EURUSD_otc"
        period = self.api.current_period or 60
        self.wss.send('42["tick"]')
        self.wss.send('42["indicator/list"]')
        self.wss.send('42["drawing/load"]')
        self.wss.send('42["pending/list"]')
        self.wss.send(f'42["instruments/update",{{"asset":"{asset_name}","period":{period}}}]')
        self.wss.send(f'42["depth/follow","{asset_name}"]')
        self.wss.send('42["chart_notification/get"]')
        self.wss.send('42["instruments/get"]')
        self.wss.send('42["tick"]')

    def on_close(self, wss, close_status_code, close_msg):
        logger.info("Websocket connection closed.")
        self.state.check_websocket_if_connect = 0
        self.state.status = WebsocketStatus.DISCONNECTED
        self.state.check_accepted_connection = False
        self.state.signal_ws_closed()

    def on_ping(self, wss, ping_msg): pass
    def on_pong(self, wss, pong_msg): pass


# ==============================================================================
# SECTION 6: QUOTEX API CORE
# ==============================================================================
class CandlesObj:
    def __init__(self): self.__candles_data = None
    @property
    def candles_data(self): return self.__candles_data
    @candles_data.setter
    def candles_data(self, candles_data): self.__candles_data = candles_data


class EventRegistry:
    def __init__(self):
        self._events: Dict[str, asyncio.Event] = {}
        self._data: Dict[str, Any] = {}
        self._lock = asyncio.Lock()

    async def get_event(self, key: str) -> asyncio.Event:
        async with self._lock:
            if key not in self._events:
                self._events[key] = asyncio.Event()
            return self._events[key]

    async def set_event(self, key: str, data: Any = None):
        async with self._lock:
            if key not in self._events:
                self._events[key] = asyncio.Event()
            self._data[key] = data
            self._events[key].set()

    async def wait_event(self, key: str, timeout: float = 30.0) -> Any:
        event = await self.get_event(key)
        try:
            await asyncio.wait_for(event.wait(), timeout=timeout)
            return self._data.get(key)
        except asyncio.TimeoutError:
            return None

    async def clear_event(self, key: str):
        async with self._lock:
            if key in self._events:
                self._events[key].clear()
            if key in self._data:
                del self._data[key]


class QuotexAPI:
    def __init__(self, host, username, password, lang, proxies=None, user_data_dir="."):
        self.state = ConnectionState()
        self.trace_ws = False
        self.current_asset = None
        self.current_period = None
        self.account_balance = None
        self.account_type = 1
        self.instruments = None
        self.host = host
        self.https_url = f"https://{host}"
        self.wss_url = f"wss://ws2.{host}/socket.io/?EIO=3&transport=websocket"
        self.websocket_thread = None
        self.websocket_client = None
        self.username = username
        self.password = password
        self.proxies = proxies
        self.lang = lang
        self.user_data_dir = user_data_dir
        self.session_data = {}
        # مرّر proxies إلى Browser حتى يستخدمها HTTP (Login + Settings)
        # إذا proxy هو "http://1.2.3.4:8080" نُحوّله إلى dict متوافق مع requests
        proxies_dict = self._normalize_proxies(proxies)
        self.browser = Browser(proxies=proxies_dict)
        self.browser.set_headers()
        self.settings = Settings(self)
        self.settings.proxies = proxies_dict  # تأكد أن Settings أيضاً يستخدم البروكسي
        self.candles = CandlesObj()
        self.candle_v2_data = {}
        self.realtime_price = defaultdict(list)
        self.event_registry = EventRegistry()
        self._async_loop: Optional[asyncio.AbstractEventLoop] = None
        self.last_message_at: float = time.time()

    @staticmethod
    def _normalize_proxies(proxies) -> Optional[dict]:
        """يحوّل proxy string (أو dict) إلى dict صيغة requests."""
        if not proxies:
            return None
        if isinstance(proxies, dict):
            return proxies
        if isinstance(proxies, str):
            # صيغة مثل "http://1.2.3.4:8080" أو "socks5://1.2.3.4:1080"
            return {"http": proxies, "https": proxies}
        return None

    @property
    def login(self):
        # مرّر proxies إلى Login حتى يستخدمها طلبات HTTP لتسجيل الدخول
        return Login(self, proxies=self._normalize_proxies(self.proxies))

    def send_websocket_request(self, data, no_force_send=True):
        if no_force_send:
            deadline = time.time() + 5.0
            while (self.state.ssl_Mutual_exclusion or self.state.ssl_Mutual_exclusion_write):
                if time.time() > deadline:
                    break
                time.sleep(0.001)
        self.state.ssl_Mutual_exclusion_write = True
        try:
            if self.websocket_client and self.websocket_client.wss:
                self.websocket_client.wss.send(data)
        finally:
            self.state.ssl_Mutual_exclusion_write = False

    def subscribe_realtime_candle(self, asset, period):
        self.realtime_price[asset] = []
        data = f'42["instruments/update", {json.dumps({"asset": asset, "period": period})}]'
        return self.send_websocket_request(data)

    def follow_candle(self, asset):
        return self.send_websocket_request(f'42["depth/follow", {json.dumps(asset)}]')

    def chart_notification(self, asset):
        return self.send_websocket_request(
            f'42["chart_notification/get", {json.dumps({"asset": asset, "version": "1.0.0"})}]')

    def get_candles_ws(self, asset, index, time_val, offset, period):
        payload = {"asset": asset, "index": index, "time": time_val, "offset": offset, "period": period}
        data = f'42["history/load",{json.dumps(payload)}]'
        return self.send_websocket_request(data)

    async def authenticate(self):
        async with self.login as login:
            status, msg = await login(self.username, self.password, self.user_data_dir)
        if status:
            self.state.SSID = self.session_data.get("token")
        return status, msg

    async def start_websocket(self):
        self.state.check_websocket_if_connect = None
        self.state.check_websocket_if_error = False
        self.state.websocket_error_reason = None
        self.state.init_events()
        self.state.reset_events()
        try:
            self.state._loop = asyncio.get_running_loop()
        except RuntimeError:
            self.state._loop = None

        if not self.state.SSID:
            await self.authenticate()
        self.websocket_client = WebsocketClient(self)
        payload = {
            "suppress_origin": True, "ping_interval": 24, "ping_timeout": 20,
            "ping_payload": "2",
            "origin": self.https_url, "host": f"ws2.{self.host}",
            "sslopt": {"check_hostname": True, "cert_reqs": ssl.CERT_REQUIRED,
                       "ca_certs": cacert, "context": ssl_context},
        }
        # مرّر البروكسي إلى WebSocket إذا وُجد
        proxy_dict = self._normalize_proxies(self.proxies)
        if proxy_dict:
            proxy_url = proxy_dict.get("http") or proxy_dict.get("https")
            if proxy_url:
                # تحليل "http://host:port" أو "socks5://host:port"
                try:
                    from urllib.parse import urlparse
                    parsed = urlparse(proxy_url)
                    if parsed.hostname and parsed.port:
                        payload["http_proxy_host"] = parsed.hostname
                        payload["http_proxy_port"] = parsed.port
                        if parsed.scheme.startswith("socks"):
                            payload["http_proxy_auth_timeout"] = 30
                except Exception:
                    pass
        if platform.system() == "Linux":
            payload["sslopt"]["ssl_version"] = ssl.PROTOCOL_TLS
        self.websocket_thread = threading.Thread(
            target=self.websocket_client.wss.run_forever, kwargs=payload)
        self.websocket_thread.daemon = True
        self.websocket_thread.start()

        try:
            idx = await wait_for_first_event(
                self.state.ws_connected_event,
                self.state.auth_rejected_event,
                self.state.ws_error_event,
                self.state.ws_closed_event,
                timeout=10.0,
            )
        except asyncio.TimeoutError:
            return False, "Timeout waiting for websocket open"

        if idx == 0:
            return True, "Websocket connected successfully!!!"
        elif idx == 1:
            self.state.SSID = None
            return False, "Websocket Token Rejected."
        elif idx == 2:
            return False, self.state.websocket_error_reason or "Websocket error"
        elif idx == 3:
            return False, "Websocket connection closed."
        return False, "Unknown websocket state"

    async def send_ssid(self, timeout=10):
        if not self.state.SSID:
            return False
        if self.state.auth_accepted_event is None:
            self.state.init_events()
        self.state.auth_accepted_event.clear()
        self.state.auth_rejected_event.clear()

        payload = {"session": self.state.SSID, "isDemo": self.account_type, "tournamentId": 0}
        data = f'42["authorization",{json.dumps(payload)}]'
        self.send_websocket_request(data)

        try:
            idx = await wait_for_first_event(
                self.state.auth_accepted_event,
                self.state.auth_rejected_event,
                timeout=timeout,
            )
        except asyncio.TimeoutError:
            return False
        return idx == 0

    async def connect(self, is_demo):
        self.account_type = 1 if is_demo else 0
        self.state.ssl_Mutual_exclusion = False
        self.state.ssl_Mutual_exclusion_write = False
        check_websocket, websocket_reason = await self.start_websocket()
        if not check_websocket:
            return check_websocket, websocket_reason
        check_ssid = await self.send_ssid()
        if not check_ssid:
            await self.authenticate()
            if self.state.SSID:
                await self.send_ssid()
        return check_websocket, websocket_reason

    async def close(self):
        if self.websocket_client and self.websocket_client.wss:
            self.websocket_client.wss.close()
            await asyncio.sleep(1)
        if self.websocket_thread and self.websocket_thread.is_alive():
            self.websocket_thread.join(timeout=5)
        return True


# ==============================================================================
# SECTION 7: QUOTEX STABLE API + CANDLE PARSING
# ==============================================================================
_request_counter = itertools.count(int(time.time() * 1000))


def _parse_raw_candles(raw_candles):
    """يُحوّل الشموع الخام من WebSocket إلى قائمة dicts بصيغة OHLC موحّدة.

    يدعم ثلاث صيغ يمكن أن يُرسلها الخادم عبر "history/load":
      1) [time, open, close, high, low]       — صيغة Quotex الشائعة (5 عناصر)
      2) [time, open, close, high, low, vol] — نفس الصيغة مع volume (6 عناصر)
      3) {"time", "open", "high", "low", "close", ...} — dict
      4) [time, price(, volume)] — tick فردي (يُحوّل إلى شمعة بسيطة)
    """
    if not raw_candles:
        return []
    parsed = []
    for c in raw_candles:
        try:
            if isinstance(c, dict) and 'time' in c:
                t = int(c.get('time', c.get('timestamp', 0)))
                o = float(c.get('open', 0) or 0)
                h = float(c.get('high', c.get('max', 0)) or 0)
                l = float(c.get('low', c.get('min', 0)) or 0)
                cl = float(c.get('close', c.get('c', 0)) or 0)
                v = int(c.get('volume', c.get('vol', 0)) or 0)
                if t > 0 and o > 0 and h > 0 and l > 0 and cl > 0:
                    parsed.append({'time': t, 'open': o, 'high': h, 'low': l,
                                   'close': cl, 'volume': v})
            elif isinstance(c, (list, tuple)) and len(c) >= 5:
                t = int(c[0]); o = float(c[1]); cl = float(c[2])
                h = float(c[3]); l = float(c[4])
                v = int(c[5]) if len(c) >= 6 else 0
                if t > 0 and o > 0 and h > 0 and l > 0 and cl > 0:
                    parsed.append({'time': t, 'open': o, 'high': h, 'low': l,
                                   'close': cl, 'volume': v})
            elif isinstance(c, (list, tuple)) and len(c) >= 2:
                t = int(c[0]); p = float(c[1])
                v = int(c[2]) if len(c) >= 3 else 0
                if t > 0 and p > 0:
                    parsed.append({'time': t, 'open': p, 'high': p, 'low': p,
                                   'close': p, 'volume': v})
        except (TypeError, ValueError):
            continue
    return parsed


def process_candles_v2(history, asset, data):
    if not history or not isinstance(history, dict):
        return data if data else []
    candles_data = history.get(asset, {})
    candles = candles_data.get("candles", [])[1:] if candles_data else []
    combined = candles + (data if data else [])
    if combined:
        candle_dict = {c.get('time'): c for c in combined if isinstance(c, dict) and 'time' in c}
        return list(candle_dict.values()) if candle_dict else []
    return combined


def merge_candles(candles_data):
    if not candles_data:
        return []
    candle_dict = {c['time']: c for c in candles_data if isinstance(c, dict) and 'time' in c}
    return sorted(candle_dict.values(), key=lambda x: x['time']) if candle_dict else []


class Quotex:
    def __init__(self, email=None, password=None, host="quotex.com", lang="en",  # <--- تم التحديث هنا
                 proxies=None, user_data_dir="browser",
                 asset_default="EURUSD_otc", period_default=60):
        self.email = email
        self.password = password
        self.host = host
        self.lang = lang
        self.proxies = proxies
        self.user_data_dir = user_data_dir
        self.asset_default = asset_default
        self.period_default = period_default
        self.account_is_demo = 1
        self.codes_asset = {}
        self.api = None
        self.subscribe_candle = []
        self.subscribe_candle_all_size = []
        self.subscribe_mood = []
        session = load_session(self.email, USER_AGENT)
        self.session_data = session

    async def check_connect(self):
        if self.api is None:
            return False
        try:
            await wait_until(
                lambda: self.api.state.check_accepted_connection == 1,
                timeout=2.0, poll_interval=0.05,
            )
            return True
        except asyncio.TimeoutError:
            return self.api.state.check_accepted_connection == 1

    async def connect(self):
        self.api = QuotexAPI(self.host, self.email, self.password, self.lang,
                             proxies=self.proxies, user_data_dir=self.user_data_dir)
        self.api.session_data = self.session_data
        self.api.state.SSID = self.session_data.get("token")
        self.api._async_loop = asyncio.get_running_loop()
        if not self.session_data.get("token"):
            check, reason = await self.api.authenticate()
            if not check:
                return check, reason
        check, reason = await self.api.connect(self.account_is_demo == 1)
        if not check:
            self.session_data = {}
            return False, "Websocket connection rejected."
        return check, reason

    async def change_account(self, balance_mode: str):
        self.account_is_demo = 0 if balance_mode.upper() == "REAL" else 1
        self.api.account_type = self.account_is_demo
        payload = {"demo": self.api.account_type, "tournamentId": 0}
        self.api.send_websocket_request(f'42["account/change",{json.dumps(payload)}]')

    async def start_candles_stream(self, asset="EURUSD_otc", period=60):
        if self.api:
            self.api.current_asset = asset
            self.api.current_period = period
            self.api.subscribe_realtime_candle(asset, period)
            self.api.chart_notification(asset)
            self.api.follow_candle(asset)

    async def _fetch_historical_batch(self, asset, fetch_time, offset, period, index, timeout):
        if self.api is None:
            return None
        payload = {"asset": asset, "index": index, "time": fetch_time,
                   "offset": offset, "period": period}
        ws_msg = f'42["history/load",{json.dumps(payload)}]'
        event_name = f'candles_ready_{asset}_{index}'
        await self.api.event_registry.clear_event(event_name)
        self.api.send_websocket_request(ws_msg)
        try:
            return await self.api.event_registry.wait_event(event_name, timeout=timeout)
        except Exception:
            return None

    def _parse_historical_candles(self, raw_data):
        if raw_data is None:
            return []
        raw_candles = raw_data.get("data", []) or raw_data.get("candles", [])
        if not raw_candles:
            return []
        parsed = []
        for c in raw_candles:
            if isinstance(c, list) and len(c) >= 5:
                parsed.append({
                    "time": int(c[0]), "open": float(c[1]),
                    "close": float(c[2]), "high": float(c[3]), "low": float(c[4]),
                })
            elif isinstance(c, dict) and "time" in c:
                parsed.append(c)
        return parsed

    async def get_historical_candles(self, asset, amount_of_seconds, period,
                                     timeout=30, max_workers=5, progress_callback=None):
        """يجلب شموع تاريخية للأصل المطلوب.

        المعاملات:
          asset            : اسم الأصل بصيغة Quotex (مثلاً EURUSD_otc)
          amount_of_seconds: عدد الثواني المطلوب جلبها للماضي
          period           : طول الشمعة بالثواني (60 = M1, 300 = M5, 3600 = H1)
          max_workers      : عدد العمال المتوازين (5 = السرعة الأصلية)
        """
        max_workers = max_workers or 1
        chunk_seconds = period * FETCH_CHUNK_SIZE  # period * 200 = عدد الثواني لكل batch
        all_candles = {}
        current_time = int(time.time())
        target_start_time = current_time - amount_of_seconds
        block_size = amount_of_seconds // max_workers
        semaphore = asyncio.Semaphore(max_workers)

        async def worker(start_t, end_t, worker_id):
            worker_candles = {}
            async with semaphore:
                oldest_t = start_t
                consecutive_failures = 0
                while oldest_t > end_t:
                    # تحقق من الاتصال قبل كل batch
                    if not self.api or not getattr(self.api.state, 'check_accepted_connection', False):
                        break
                    index = next(_request_counter)
                    batch_data = await self._fetch_historical_batch(
                        asset, oldest_t, chunk_seconds, period, index, timeout)
                    if not batch_data:
                        oldest_t -= chunk_seconds
                        consecutive_failures += 1
                        if consecutive_failures >= 3:
                            break
                        await asyncio.sleep(FETCH_BATCH_DELAY * 2)
                        continue
                    consecutive_failures = 0
                    new_batch = self._parse_historical_candles(batch_data)
                    if not new_batch:
                        oldest_t -= chunk_seconds
                        continue
                    batch_times = []
                    for c in new_batch:
                        ts = c['time']
                        if ts >= end_t and ts <= start_t:
                            worker_candles[ts] = c
                            batch_times.append(ts)
                    if not batch_times:
                        oldest_t -= chunk_seconds
                        continue
                    batch_times.sort()
                    new_oldest = batch_times[0]
                    if progress_callback:
                        progress_callback(start_t - new_oldest, start_t - end_t,
                                          len(worker_candles), f"Worker-{worker_id}")
                    oldest_t = new_oldest if new_oldest < oldest_t else oldest_t - chunk_seconds
                    await asyncio.sleep(FETCH_BATCH_DELAY)
            return list(worker_candles.values())

        await self.start_candles_stream(asset, period)
        tasks = []
        for i in range(max_workers):
            s = current_time - (i * block_size)
            e = max(target_start_time, s - block_size)
            tasks.append(worker(s, e, i))
        results = await asyncio.gather(*tasks)
        for batch in results:
            for c in batch:
                all_candles[c['time']] = c
        return sorted(all_candles.values(), key=lambda x: x['time'])

    async def close(self):
        if self.api:
            return await self.api.close()
        return True


# ==============================================================================
# SECTION 8: CONSTANTS & CONFIG (جديد)
# ==============================================================================
CREDENTIALS_FILE = Path("credentials.json")

# مجلد حفظ الشموع — ملفات JSON تُحفظ مباشرة هنا بدون مجلدات فرعية.
CANDLES_DIR = Path("candles_otc_data")
CANDLES_DIR.mkdir(exist_ok=True)

# قائمة العملات الـ13 (OTC) — تُجلب تلقائياً عند اختيار الخيار 2 بعد تسجيل الدخول.
OTC_ASSETS = [
    "BRLUSD_otc",   # Brazil
    "USDARS_otc",   # Argentina
    "USDBDT_otc",   # Bangladesh
    "USDCOP_otc",   # Colombia
    "USDDZD_otc",   # Algeria
    "USDEGP_otc",   # Egypt
    "USDIDR_otc",   # Indonesia
    "USDINR_otc",   # India
    "USDMXN_otc",   # Mexico
    "USDNGN_otc",   # Nigeria
    "USDPHP_otc",   # Philippines
    "USDPKR_otc",   # Pakistan
    "USDZAR_otc",   # South Africa
]

# إعدادات الجلب — متوازي 5 workers (السرعة الأصلية ~4s لكل 1000 شمعة)
FETCH_MAX_WORKERS = 5
FETCH_CHUNK_SIZE = 200         # 200 شمعة لكل batch
FETCH_BATCH_DELAY = 0.1        # 0.1s بين batches
MAX_FETCH_RETRIES = 5
RETRY_BACKOFF_BASE = 2
RETRY_BACKOFF_MAX = 15
KEEPALIVE_INTERVAL = 5         # ping كل 5 ثوانٍ للحفاظ على الاتصال بين عمليات الجلب
RECONNECT_CHECK_INTERVAL = 10  # فحص حالة الاتصال كل 10 ثوانٍ
MAX_RECONNECT_ATTEMPTS = 5     # عدد محاولات إعادة الاتصال قبل الاستسلام
RECONNECT_BACKOFF_BASE = 3     # ثانية بين المحاولات (يتضاعف)

# أدوات التسجيل
LOG_FILE = Path("candal.log")


def logmsg(msg: str):
    ts = datetime.now().strftime("%H:%M:%S")
    print(f"  \033[2m[{ts}]\033[0m {msg}")
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"[{ts}] {msg}\n")
    except Exception:
        pass


def log_exception(context: str, exc: BaseException):
    ts = datetime.now().strftime("%H:%M:%S")
    tb_text = "".join(traceback.format_exception(type(exc), exc, exc.__traceback__))
    print(f"  \033[91m[{ts}] FATAL in {context}: {exc}\033[0m")
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"[{ts}] FATAL in {context}: {exc}\n{tb_text}\n")
    except Exception:
        pass


class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    YELLOW = '\033[93m'
    CYAN = '\033[96m'
    BOLD = '\033[1m'
    DIM = '\033[2m'
    RESET = '\033[0m'


# التقاط استثناءات الـ threads
def _thread_excepthook(args):
    log_exception(f"thread '{args.thread.name}'", args.exc_value)
threading.excepthook = _thread_excepthook


def _main_excepthook(exc_type, exc_value, exc_tb):
    if issubclass(exc_type, KeyboardInterrupt):
        sys.__excepthook__(exc_type, exc_value, exc_tb)
        return
    log_exception("main thread (top level)", exc_value)
sys.excepthook = _main_excepthook


# ==============================================================================
# SECTION 9: CREDENTIALS MANAGEMENT (حفظ الإيميل وكلمة المرور)
# ==============================================================================
SESSION_FILE = Path("session.json")
BROWSER_DIR = Path("browser")


def purge_old_session() -> None:
    """Delete any saved Quotex session so we always log in fresh.

    Quotex may reject connections that reuse a stale token from a previous
    run. By deleting session.json and the browser/ cache directory on
    startup, we force a brand-new login every time.
    """
    try:
        if SESSION_FILE.exists():
            SESSION_FILE.unlink()
    except Exception:
        pass
    try:
        if BROWSER_DIR.exists():
            shutil.rmtree(BROWSER_DIR, ignore_errors=True)
    except Exception:
        pass


def load_credentials() -> Optional[Dict[str, str]]:
    """يقرأ بيانات الدخول من credentials.json. يُعيد None إذا لم توجد."""
    if not CREDENTIALS_FILE.exists():
        return None
    try:
        data = json.loads(CREDENTIALS_FILE.read_text())
        if data.get("email") and data.get("password"):
            return data
        return None
    except Exception:
        return None


def save_credentials(email: str, password: str, proxy: str = "") -> bool:
    """يحفظ بيانات الدخول والبروكسي في credentials.json لإعادة الاستخدام لاحقاً."""
    try:
        existing = {}
        if CREDENTIALS_FILE.exists():
            try: existing = json.loads(CREDENTIALS_FILE.read_text())
            except Exception: pass
        existing.update({
            "email": email,
            "password": password,
            "proxy": proxy,
            "saved_at": int(time.time())
        })
        CREDENTIALS_FILE.write_text(json.dumps(existing, indent=2))
        return True
    except Exception as e:
        logmsg(f"Failed to save credentials: {e}")
        return False


# ==============================================================================
# SECTION 10: ASSET NAME NORMALIZATION
# ==============================================================================
def normalize_asset(raw: str) -> str:
    """يُنظّف اسم الأصل ولا يضيف _otc إلا إذا كتبتها أنت.

    أمثلة:
      "XAUUSD"      -> "XAUUSD"        (حقيقي، بدون otc)
      "XAUUSD_otc"  -> "XAUUSD_otc"
      "xauusd otc"  -> "XAUUSD_otc"
      "EUR/USD"     -> "EURUSD"
    """
    s = re.sub(r'[^a-zA-Z0-9]', '', raw.strip())
    if not s:
        return ""
    is_otc = s.upper().endswith("OTC")
    if is_otc:
        s = s[:-3]
    s = s.upper()
    if not s:
        return ""
    return f"{s}_otc" if is_otc else s


def pretty_asset(symbol: str, timeframe_min: int) -> str:
    """يُعيد اسم عرض جميل: EUR/USD · OTC (M5)"""
    base = symbol
    suffix = ""
    if base.upper().endswith("_OTC"):
        base = base[:-4]
        suffix = " · OTC"
    if len(base) == 6 and base.isalpha():
        pretty = f"{base[:3]}/{base[3:]}{suffix}"
    else:
        pretty = f"{base}{suffix}"
    return f"{pretty} (M{timeframe_min})"


# ==============================================================================
# SECTION 11: JSON FILE SAVING (منسّق: شمعة واحدة في كل سطر)
# ==============================================================================
def _save_debug_json(candles: List[Dict], asset: str, timeframe_min: int, tag: str) -> None:
    """Save a debug snapshot of candles for gap-fill inspection.

    Creates a file like: candles_otc_data/<run>/<asset>_<tf>m_<tag>.json
    This lets you open the file and compare candles before/after gap-filling.
    """
    if not candles:
        return
    try:
        debug_path = CANDLES_DIR / f"{asset}_{timeframe_min}m_{tag}.json"
        def fmt_dt(ts: int) -> str:
            return datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
        rows = []
        for c in candles:
            row = {
                "datetime": fmt_dt(c['time']),
                "time": c['time'],
                "open": c['open'],
                "high": c['high'],
                "low": c['low'],
                "close": c['close'],
                "volume": c.get('volume', 0),
                "synthetic": c.get('volume', 1) == 0,
            }
            rows.append("    " + json.dumps(row, ensure_ascii=False))
        body = ",\n".join(rows)
        meta = {
            "asset": asset,
            "timeframe_minutes": timeframe_min,
            "candle_count": len(candles),
            "synthetic_count": sum(1 for c in candles if c.get('volume', 1) == 0),
            "tag": tag,
            "saved_at": datetime.now().isoformat(timespec="seconds"),
        }
        meta_txt = json.dumps(meta, indent=2, ensure_ascii=False).replace("\n", "\n  ")
        with open(debug_path, 'w', encoding='utf-8') as f:
            f.write('{\n')
            f.write(f'  "metadata": {meta_txt},\n')
            f.write('  "candles": [\n')
            f.write(body + '\n')
            f.write('  ]\n}\n')
    except Exception:
        pass


def save_candles_to_json(candles: List[Dict], asset: str, timeframe_min: int, days: int) -> Optional[Path]:
    """يحفظ الشموع في ملف JSON منسّق باسم: {asset}_{timeframe}m_{days}d_{random}.json

    كل شمعة في سطر واحد مع تاريخ مقروء (UTC) بجانب الـ timestamp.
    """
    if not candles:
        logmsg("No candles to save.")
        return None

    def fmt_dt(ts: int) -> str:
        return datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d %H:%M:%S")

    random_suffix = ''.join(random.choices('0123456789abcdef', k=8))
    filepath = CANDLES_DIR / f"{asset}_{timeframe_min}m_{days}d_{random_suffix}.json"

    meta = {
        "asset": asset,
        "display_name": pretty_asset(asset, timeframe_min),
        "is_otc": asset.lower().endswith("_otc"),
        "timeframe_minutes": timeframe_min,
        "days_requested": days,
        "candle_count": len(candles),
        "first_candle": fmt_dt(candles[0]['time']),
        "last_candle": fmt_dt(candles[-1]['time']),
        "first_candle_time": candles[0]['time'],
        "last_candle_time": candles[-1]['time'],
        "timezone": "UTC",
        "fetch_time": datetime.now().isoformat(timespec="seconds"),
        "fetch_timestamp": int(time.time()),
    }

    try:
        meta_txt = json.dumps(meta, indent=2, ensure_ascii=False).replace("\n", "\n  ")
        rows = []
        for c in candles:
            row = {
                "datetime": fmt_dt(c['time']),
                "time": c['time'],
                "open": c['open'],
                "high": c['high'],
                "low": c['low'],
                "close": c['close'],
                "volume": c.get('volume', 0),
            }
            rows.append("    " + json.dumps(row, ensure_ascii=False))
        body = ",\n".join(rows)

        with open(filepath, 'w', encoding='utf-8') as f:
            f.write('{\n')
            f.write(f'  "metadata": {meta_txt},\n')
            f.write('  "candles": [\n')
            f.write(body + '\n')
            f.write('  ]\n}\n')
        return filepath
    except Exception as e:
        log_exception("save_candles_to_json", e)
        return None


# ==============================================================================
# SECTION 12: FETCH LOGIC (جديد)
# ==============================================================================
async def keepalive_loop(client: Quotex, stop_event: asyncio.Event):
    """حلقة keepalive بسيطة ترسل ping كل KEEPALIVE_INTERVAL ثانية.
    تحافظ على اتصال WebSocket حياً بين عمليات الجلب، وتتوقف فوراً عند ضبط stop_event."""
    while not stop_event.is_set():
        try:
            if client and client.api:
                client.api.send_websocket_request("2", no_force_send=False)
                client.api.send_websocket_request('42["tick"]', no_force_send=False)
        except Exception:
            pass
        # انتظار قابل للإيقاف: يخرج فوراً عند ضبط stop_event
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=KEEPALIVE_INTERVAL)
        except asyncio.TimeoutError:
            pass  # انتهى المحدّد = أرسل ping التالي


# ------------------------------------------------------------------------------
# آلية "عدم النوم" (مستوحاة من الكود الضخم wedsoket_.py)
# ------------------------------------------------------------------------------
# مشترك بين keepalive_loop و auto_reconnect_loop لتجديد كائن Quotex عند الفقد.
# يتم تحديثه عبر attribute set بدلاً من closure لتفادي مشاكل الـ late binding.
class _ClientHolder:
    """حاوية بسيطة تتيح لـ auto_reconnect استبدال كائن Quotex برمجياً."""
    def __init__(self, client: Optional[Quotex]):
        self.client = client
        self.email: Optional[str] = None
        self.password: Optional[str] = None
        self.proxies: Optional[str] = None
        self.lock = asyncio.Lock()


def _is_connection_alive(client: Optional[Quotex]) -> bool:
    """فحص سريع: هل اتصال Quotex ما زال نشطاً؟
    يعيد False بأمان لأي كائن لا يحتوي على api أو state."""
    if client is None:
        return False
    try:
        api = getattr(client, "api", None)
        if api is None:
            return False
        state = getattr(api, "state", None)
        if state is None:
            return False
        return bool(getattr(state, "check_accepted_connection", False))
    except Exception:
        return False


async def auto_reconnect_loop(holder: _ClientHolder, stop_event: asyncio.Event,
                              on_reconnect=None) -> None:
    """راقب حالة الاتصال كل RECONNECT_CHECK_INTERVAL ثانية. عند الفقد،
    حاول إعادة الاتصال تلقائياً حتى MAX_RECONNECT_ATTEMPTS محاولة.

    - لا يوقف البرنامج أبداً ما لم يُضبط stop_event.
    - يستبدل holder.client بكائن Quotex جديد عند نجاح إعادة الاتصال.
    - يستدعي on_reconnect(new_client) إن وُجدت (لإعلام الـ fetcher باستخدام الكائن الجديد).
    """
    while not stop_event.is_set():
        try:
            alive = _is_connection_alive(holder.client)
            if not alive:
                logmsg(f"{Colors.YELLOW}[reconnect] connection lost, attempting reconnect...{Colors.RESET}")
                backoff = RECONNECT_BACKOFF_BASE
                for attempt in range(1, MAX_RECONNECT_ATTEMPTS + 1):
                    if stop_event.is_set():
                        return
                    try:
                        new_client = Quotex(
                            email=holder.email,
                            password=holder.password,
                            host="quotex.com",
                            lang="en",
                            proxies=holder.proxies,
                        )
                        check, reason = await new_client.connect()
                        if check:
                            try:
                                await new_client.change_account("PRACTICE")
                                await asyncio.sleep(0.5)
                            except Exception:
                                pass
                            async with holder.lock:
                                # أغلق القديم بهدوء قبل الاستبدال
                                try:
                                    if holder.client:
                                        await holder.client.close()
                                except Exception:
                                    pass
                                holder.client = new_client
                            logmsg(f"{Colors.GREEN}[reconnect] reconnect successful on attempt {attempt}{Colors.RESET}")
                            if on_reconnect:
                                try:
                                    on_reconnect(new_client)
                                except Exception as cb_err:
                                    logmsg(f"[reconnect] on_reconnect callback raised: {cb_err}")
                            break
                        else:
                            err = str(reason) if reason else "Unknown"
                            logmsg(f"[reconnect] attempt {attempt}/{MAX_RECONNECT_ATTEMPTS} failed: {err}")
                    except Exception as e:
                        logmsg(f"[reconnect] attempt {attempt}/{MAX_RECONNECT_ATTEMPTS} raised: {e}")
                    if attempt < MAX_RECONNECT_ATTEMPTS:
                        await asyncio.sleep(backoff)
                        backoff = min(backoff * 2, 30)
                else:
                    logmsg(f"{Colors.RED}[reconnect] all {MAX_RECONNECT_ATTEMPTS} attempts failed; "
                           f"will retry in {RECONNECT_CHECK_INTERVAL}s.{Colors.RESET}")
        except Exception as e:
            log_exception("auto_reconnect_loop", e)
        # انتظار قابل للإيقاف
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=RECONNECT_CHECK_INTERVAL)
        except asyncio.TimeoutError:
            pass


async def connect_quotex(email: str, password: str, max_attempts: int = 3,
                         proxies: Optional[str] = None) -> Optional[Quotex]:
    """يتصل بـ Quotex ويعيد كائن Quotex. يُعيد None عند الفشل.

    المعاملات:
      email      : بريد Quotex
      password   : كلمة المرور
      max_attempts: عدد محاولات الاتصال
      proxies    : URL البروكسي (مثل "http://1.2.3.4:8080" أو "socks5://1.2.3.4:1080")
    """
    for attempt in range(1, max_attempts + 1):
        try:
            client = Quotex(email=email, password=password,
                            host="quotex.com", lang="en",  # <--- تم التحديث هنا
                            proxies=proxies)
            check, reason = await client.connect()
            if check:
                try:
                    await client.change_account("PRACTICE")
                    await asyncio.sleep(0.5)
                except Exception:
                    pass
                logmsg(f"Connected to Quotex as {email}")
                return client
            else:
                err = str(reason) if reason else "Unknown error"
                logmsg(f"Login attempt {attempt}/{max_attempts} failed: {err}")
        except Exception as e:
            logmsg(f"Login attempt {attempt}/{max_attempts} raised: {e}")
        if attempt < max_attempts:
            await asyncio.sleep(3 * attempt)
    return None

# ============================================================================
# SECTION 2: EXTENDED COLOR SYSTEM + FORMATTING HELPERS
# ============================================================================

# SECTION 2: COLOR SYSTEM + FORMATTING HELPERS
# ============================================================================
class C2:
    """Extended color system."""
    RESET = '\033[0m'
    BOLD = '\033[1m'
    DIM = '\033[2m'
    ITALIC = '\033[3m'
    UNDERLINE = '\033[4m'
    BLINK = '\033[5m'
    REVERSE = '\033[7m'
    HIDDEN = '\033[8m'
    STRIKE = '\033[9m'

    BLACK = '\033[30m'
    RED = '\033[31m'
    GREEN = '\033[32m'
    YELLOW = '\033[33m'
    BLUE = '\033[34m'
    MAGENTA = '\033[35m'
    CYAN = '\033[36m'
    WHITE = '\033[37m'

    BRIGHT_BLACK = '\033[90m'
    BRIGHT_RED = '\033[91m'
    BRIGHT_GREEN = '\033[92m'
    BRIGHT_YELLOW = '\033[93m'
    BRIGHT_BLUE = '\033[94m'
    BRIGHT_MAGENTA = '\033[95m'
    BRIGHT_CYAN = '\033[96m'
    BRIGHT_WHITE = '\033[97m'

    BG_BLACK = '\033[40m'
    BG_RED = '\033[41m'
    BG_GREEN = '\033[42m'
    BG_YELLOW = '\033[43m'
    BG_BLUE = '\033[44m'
    BG_MAGENTA = '\033[45m'
    BG_CYAN = '\033[46m'
    BG_WHITE = '\033[47m'

    BG_BRIGHT_BLACK = '\033[100m'
    BG_BRIGHT_RED = '\033[101m'
    BG_BRIGHT_GREEN = '\033[102m'
    BG_BRIGHT_YELLOW = '\033[103m'
    BG_BRIGHT_BLUE = '\033[104m'
    BG_BRIGHT_MAGENTA = '\033[105m'
    BG_BRIGHT_CYAN = '\033[106m'
    BG_BRIGHT_WHITE = '\033[107m'


def paint(color: str, text: str) -> str:
    return f"{color}{text}{C2.RESET}"


def paint_bold(text: str, color: str = C2.WHITE) -> str:
    return f"{C2.BOLD}{color}{text}{C2.RESET}"


def paint_dim(text: str) -> str:
    return f"{C2.DIM}{text}{C2.RESET}"


def visible_length(s: str) -> int:
    import re
    return len(re.sub(r'\x1b\[[0-9;]*m', '', s))


def pad_visible(s: str, width: int) -> str:
    gap = max(0, width - visible_length(s))
    return s + ' ' * gap


def hr(width: int = 80, char: str = '─', color: str = C2.DIM) -> str:
    return paint(color, char * width)


def progress_bar(progress: float, width: int = 30, fill: str = '█',
                 empty: str = '░', color_fill: str = C2.BRIGHT_GREEN,
                 color_empty: str = C2.DIM) -> str:
    filled = int(width * progress)
    bar = paint(color_fill, fill * filled) + paint(color_empty, empty * (width - filled))
    pct = f"{progress * 100:5.1f}%"
    return f"[{bar}] {pct}"


# ============================================================================
# SECTION 3: ASCII ART BANNER
# ============================================================================
BANNER_ART = r"""
██╗  ██╗██████╗  ██████╗ ██╗  ██╗ ██████╗ ███████╗████████╗
██║ ██╔╝██╔══██╗██╔═══██╗██║ ██╔╝██╔═══██╗██╔════╝╚══██╔══╝
█████╔╝ ██████╔╝██║   ██║█████╔╝ ██║   ██║███████╗   ██║
██╔═██╗ ██╔══██╗██║   ██║██╔═██╗ ██║   ██║╚════██║   ██║
██║  ██╗██║  ██║╚██████╔╝██║  ██╗╚██████╔╝███████║   ██║
╚═╝  ╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═╝  ╚═╝ ╚═════╝ ╚══════╝   ╚═╝
"""


def print_banner():
    print(paint(C2.BRIGHT_CYAN, BANNER_ART))
    print(hr(70, '═', C2.BRIGHT_BLUE))
    print(paint_bold("  Quotex Mega Fetcher — Full Engine", C2.BRIGHT_WHITE))
    print(paint_dim("  500 candles · profit % · gap-fill · live price · never-sleep"))
    print(hr(70, '═', C2.BRIGHT_BLUE))
    print(f"  {paint('Output dir:', C2.DIM)}       {paint(str(CANDLES_DIR.absolute()), C2.BRIGHT_YELLOW)}")
    print(f"  {paint('Target count:', C2.DIM)}     {paint('500 candles per asset', C2.BRIGHT_GREEN)}")
    print(f"  {paint('Default assets:', C2.DIM)}   {paint(f'{len(OTC_ASSETS)} OTC pairs', C2.BRIGHT_GREEN)}")
    print(f"  {paint('Gap-filling:', C2.DIM)}      {paint('ENABLED', C2.BRIGHT_GREEN)} (max_gap=1440 slots)")
    print(f"  {paint('Live price:', C2.DIM)}       {paint('ENABLED', C2.BRIGHT_GREEN)} (depth/follow + quotes/stream)")
    print(f"  {paint('Profit %:', C2.DIM)}         {paint('ENABLED', C2.BRIGHT_GREEN)} (instruments/list binary)")
    print(f"  {paint('Never-sleep:', C2.DIM)}      {paint('ENABLED', C2.BRIGHT_GREEN)} (keepalive + watchdog + reconnect)")
    print(hr(70, '═', C2.BRIGHT_BLUE))
    print()


# ============================================================================
# SECTION 4: EXTENDED LOGGER
# ============================================================================
class ExtendedLogger:
    """Logger that writes both to console (colored) and to file (plain)."""

    def __init__(self, log_file: str = "mega_fetch.log"):
        self.log_file = Path(log_file)
        self._lock = threading.Lock()

    def _time(self) -> str:
        return datetime.now().strftime("%H:%M:%S")

    def _write_file(self, level: str, msg: str):
        try:
            with self._lock:
                with open(self.log_file, "a", encoding="utf-8") as f:
                    f.write(f"[{level}] {self._time()} - {msg}\n")
        except Exception:
            pass

    def info(self, msg: str):
        ts = self._time()
        print(f"{paint(C2.DIM, '[INFO]')} {paint(C2.BRIGHT_CYAN, ts)} "
              f"{paint(C2.DIM, '-')} {paint(C2.WHITE, msg)}")
        self._write_file("INFO", msg)

    def success(self, msg: str):
        ts = self._time()
        print(f"{paint(C2.BOLD + C2.BRIGHT_GREEN, '[OK]')} {paint(C2.BRIGHT_CYAN, ts)} "
              f"{paint(C2.DIM, '-')} {paint(C2.BRIGHT_GREEN, msg)}")
        self._write_file("OK", msg)

    def warn(self, msg: str):
        ts = self._time()
        print(f"{paint(C2.BOLD + C2.BRIGHT_YELLOW, '[WARN]')} {paint(C2.BRIGHT_CYAN, ts)} "
              f"{paint(C2.DIM, '-')} {paint(C2.BRIGHT_YELLOW, msg)}")
        self._write_file("WARN", msg)

    def error(self, msg: str):
        ts = self._time()
        print(f"{paint(C2.BOLD + C2.BRIGHT_RED, '[ERROR]')} {paint(C2.BRIGHT_CYAN, ts)} "
              f"{paint(C2.DIM, '-')} {paint(C2.BRIGHT_RED, msg)}")
        self._write_file("ERROR", msg)

    def debug(self, msg: str):
        ts = self._time()
        print(f"{paint(C2.DIM, '[DBG]')} {paint(C2.BRIGHT_CYAN, ts)} "
              f"{paint(C2.DIM, '-')} {paint(C2.DIM, msg)}")


elog = ExtendedLogger()


# ============================================================================
# SECTION 5: SPINNER
# ============================================================================
class Spinner:
    FRAMES = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏']
    FRAMES_DOTS = ['⣾', '⣽', '⣻', '⢿', '⡿', '⣟', '⣯', '⣷']
    FRAMES_CIRCLE = ['◐', '◓', '◑', '◒']

    def __init__(self, text: str = '', style: str = 'braille'):
        self.text = text
        self.frames = {
            'braille': self.FRAMES,
            'dots': self.FRAMES_DOTS,
            'circle': self.FRAMES_CIRCLE,
        }.get(style, self.FRAMES)
        self.i = 0
        self.timer = None
        self._stop_event = threading.Event()

    def start(self, text: Optional[str] = None):
        if text is not None:
            self.text = text
        if self.timer is not None:
            return self
        sys.stdout.write('\x1b[?25l')
        self._stop_event.clear()
        self.timer = threading.Thread(target=self._run, daemon=True)
        self.timer.start()
        return self

    def _run(self):
        while not self._stop_event.is_set():
            frame = paint(C2.BRIGHT_CYAN, self.frames[self.i])
            self.i = (self.i + 1) % len(self.frames)
            sys.stdout.write(f'\r{frame} {paint(C2.DIM, self.text)}\x1b[K')
            sys.stdout.flush()
            time.sleep(0.08)

    def update(self, text: str):
        self.text = text

    def stop(self, final_msg: Optional[str] = None, success: bool = True):
        if self.timer is None:
            return
        self._stop_event.set()
        self.timer.join(timeout=0.5)
        self.timer = None
        sys.stdout.write('\r\x1b[K')
        sys.stdout.write('\x1b[?25h')
        sys.stdout.flush()
        if final_msg:
            if success:
                elog.success(final_msg)
            else:
                elog.error(final_msg)


# ============================================================================
# SECTION 6: CONFIGURATION
# ============================================================================
TARGET_CANDLE_COUNT = 150          # was 500 — reduced per user request for faster fetch
TIMEFRAME_DEFAULT = 1
GAP_FILL_MAX_SLOTS = 1440

# Fetch strategy (ported from OTC_canda_.py)
FETCH_MAX_WORKERS = 5
FETCH_CHUNK_SIZE = 200         # 200 candles per batch (server paging)
FETCH_BATCH_DELAY = 0.1        # 0.1s between batches
MAX_FETCH_RETRIES = 5          # retry failed fetches 5 times
RETRY_BACKOFF_BASE = 2         # initial backoff (2s)
RETRY_BACKOFF_MAX = 15         # max backoff (15s)

# Never-sleep engine timings (ported from wedsoket_.py)
KEEPALIVE_PING_INTERVAL = 5         # seconds between pings
STALE_MESSAGE_TIMEOUT = 45         # if no message for 45s, recycle connection
STALE_WATCHDOG_INTERVAL = 10       # check every 10s
HEALTH_CHECK_INTERVAL = 20         # health monitor every 20s
RECONNECT_CHECK_INTERVAL = 10      # reconnect check every 10s
MAX_RECONNECT_ATTEMPTS = 8         # attempts before giving up (was 5, increased)
RECONNECT_BACKOFF_BASE = 3         # initial backoff in seconds
RECONNECT_BACKOFF_MAX = 60         # maximum backoff
LONG_DISCONNECT_THRESHOLD = 3600   # 1 hour — triggers full re-fetch

# Live price settings
LIVE_PRICE_LISTEN_SECONDS = 20.0   # increased to 20s — Quotex sends fluctuating
                                   # payout values; we need time to capture the
                                   # HIGH value for each asset (alternates
                                   # between CALL and PUT payouts every 1-2s)
LIVE_PRICE_BROADCAST_INTERVAL = 0.5

# DEBUG: when True, every WS message is logged for diagnosis.
# Disable by setting this to False in production.
# Set to True ONLY when debugging protocol issues — it produces A LOT of output.
DEBUG_WS_TRAFFIC = False          # was True — disabled (too noisy)
DEBUG_BINARY_PREVIEW_BYTES = 32
DEBUG_TEXT_PREVIEW_CHARS = 200

# More granular debug: only log specific message types when DEBUG_WS_TRAFFIC
# is False. Each entry is a substring to match in the text/binary content.
# Empty list = no granular logging.
# NOTE: depth/change ANNOUNCEMENTS ('451-["depth/change",{"_placeholder":...}]')
# arrive every ~1 second, so even with this filter the log is noisy.
# Keep this list EMPTY for clean output; the [depth/change] SUCCESS log
# in _handle_depth_change already shows progress.
DEBUG_WS_TYPES = []  # empty = no per-frame debug logs

# Fetch strategy
CHUNK_CANDLES = 60
OVERLAP_CANDLES = 10
FETCH_BATCH_SIZE = 4
FETCH_STAGGER_MS = 150

# The 13 OTC pairs
OTC_ASSETS = [
    "BRLUSD_otc",   # Brazil
    "USDARS_otc",   # Argentina
    "USDBDT_otc",   # Bangladesh
    "USDCOP_otc",   # Colombia
    "USDDZD_otc",   # Algeria
    "USDEGP_otc",   # Egypt
    "USDIDR_otc",   # Indonesia
    "USDINR_otc",   # India
    "USDMXN_otc",   # Mexico
    "USDNGN_otc",   # Nigeria
    "USDPHP_otc",   # Philippines
    "USDPKR_otc",   # Pakistan
    "USDZAR_otc",   # South Africa
]


# ============================================================================
# SECTION 7: GAP-FILLING ENGINE (ported verbatim from wedsoket_.py)
# ============================================================================
def _fill_missing_slots(candles: List[Dict], period_seconds: int,
                        max_gap: int = GAP_FILL_MAX_SLOTS) -> List[Dict]:
    """Fills time gaps between candles with flat candles (previous close).

    Ported verbatim from wedsoket_.py.
    - Added candles have volume=0 (marked synthetic).
    - max_gap: max number of periods to fill (1440 = 1 day for M1).
    """
    if len(candles) < 2:
        return list(candles)
    candles = sorted(candles, key=lambda x: x['time'])
    out = [dict(candles[0])]
    for i in range(1, len(candles)):
        prev = out[-1]
        curr = candles[i]
        gap = (curr['time'] - prev['time']) // period_seconds
        if 0 < gap <= max_gap:
            slot = prev['time'] + period_seconds
            while slot < curr['time']:
                out.append({
                    'time': slot,
                    'open': prev['close'],
                    'high': prev['close'],
                    'low': prev['close'],
                    'close': prev['close'],
                    'volume': 0,
                })
                slot += period_seconds
        out.append(dict(curr))
    return out


def _aggregate_1s_to_target(raw_ticks: List, target_period: int) -> List[Dict]:
    """Aggregate 1-second tick data into target-period OHLC candles.

    The Quotex server returns 1s data as either:
      - Dicts: {"time": ts, "open": o, "high": h, "low": l, "close": c, ...}
      - Arrays: [timestamp, price, direction]  (tick data — NOT OHLC!)
      - Arrays: [timestamp, open, close, high, low]  (OHLC without keys)

    This function handles ALL formats and aggregates them into target_period
    candles (e.g. 60s for M1).

    Ported from wedsoket_.py:_aggregate_sub_minute + calculate_candles.
    """
    if not raw_ticks or target_period <= 1:
        return []

    # Step 1: Normalize all ticks to (timestamp, price) pairs
    prices_at_time = []  # list of (aligned_ts, price)
    for item in raw_ticks:
        if isinstance(item, dict):
            ts = int(item.get("time", item.get("timestamp", 0)))
            # If it already has OHLC, use close as the price
            price = float(item.get("close", item.get("price", 0)) or 0)
            if ts > 0 and price > 0:
                prices_at_time.append((ts, price))
        elif isinstance(item, list) and len(item) >= 2:
            try:
                ts = int(item[0])
                price = float(item[1])
                if ts > 0 and price > 0:
                    prices_at_time.append((ts, price))
            except (ValueError, TypeError):
                continue

    if not prices_at_time:
        return []

    # Step 2: Group prices by target_period bucket
    buckets = OrderedDict()
    for ts, price in prices_at_time:
        bucket_time = (ts // target_period) * target_period
        if bucket_time not in buckets:
            buckets[bucket_time] = []
        buckets[bucket_time].append(price)

    # Step 3: Build OHLC candles from each bucket
    result = []
    for bucket_time, prices in buckets.items():
        if not prices:
            continue
        o = prices[0]
        h = max(prices)
        l = min(prices)
        cl = prices[-1]
        result.append({
            'time': bucket_time,
            'open': o,
            'high': h,
            'low': l,
            'close': cl,
            'volume': len(prices),
        })

    return sorted(result, key=lambda x: x['time'])


# ============================================================================
# SECTION 8: MESSAGE INTERCEPTOR (instruments + candles + live ticks)
# ============================================================================
class MessageInterceptor:
    """Intercepts WebsocketClient.on_message to capture:

    (a) binary instruments/list frames (JSON, 0x04-prefixed) → profit %, enabled
    (b) live tick arrays (quotes/stream, depth/change) → current price
    (c) historical candle responses (history/load, history/list/v2) → candles

    All captured data is stored in the `state` dict and surfaced via
    asyncio events.
    """

    def __init__(self, client: Quotex):
        self.client = client
        self.instruments: List[Dict] = []
        # profit_by_asset = LAST value from depth/change (for reference)
        # max_profit_by_asset = HIGHEST value from any source
        # profit_history = list of all values from depth/change (for MODE)
        # instruments_profit_by_asset = payout from instruments/list (AUTHORITATIVE)
        # instruments_locked = True once instruments/list provides data for an asset
        #   Once locked, depth/change CANNOT overwrite the payout for that asset.
        self.profit_by_asset: Dict[str, int] = {}
        self.max_profit_by_asset: Dict[str, int] = {}
        self.profit_history: Dict[str, List[int]] = defaultdict(list)
        self.instruments_profit_by_asset: Dict[str, int] = {}
        self.instruments_locked: Dict[str, bool] = {}
        self.enabled_by_asset: Dict[str, bool] = {}
        self.live_prices: Dict[str, float] = {}
        self.live_ticks_seen: Dict[str, int] = defaultdict(int)
        self.last_tick_at: Dict[str, float] = {}

        self.instruments_ready = asyncio.Event()
        self.candles_ready: Dict[str, asyncio.Event] = defaultdict(asyncio.Event)
        self.candles_data: Dict[str, List[Dict]] = {}

        self._original_on_message = None
        self._original_wss_on_message = None  # WebSocketApp callback
        self._ws_client = None
        self._expecting_instruments_binary = False
        self._expecting_depth_change_binary = False
        self._expecting_quotes_stream_binary = False
        self._expecting_orders_binary = False
        self._temp_status_instruments = ""
        self._temp_status_history = ""  # tracks which asset we're awaiting

    def install(self) -> bool:
        """Install the interceptor on the WebSocket connection.

        IMPORTANT: The Quotex library's WebsocketClient creates a
        `websocket.WebSocketApp` in __init__ and passes `on_message=self.on_message`
        to it. This means WebSocketApp captures a BOUND METHOD reference at
        construction time. If we later patch `ws_client.on_message = ...`, the
        WebSocketApp still holds the OLD reference and will NEVER call our
        interceptor.

        To fix this, we must patch `ws_client.wss.on_message` directly — that's
        the attribute WebSocketApp actually calls. We also patch the WebsocketClient
        method itself, for safety (in case it's called directly).
        """
        api = self.client.api
        if api is None:
            return False
        ws_client = getattr(api, "websocket_client", None)
        if ws_client is None:
            return False
        self._ws_client = ws_client

        # Save originals
        self._original_on_message = ws_client.on_message

        # 1) Patch the WebsocketClient method (in case anyone calls it directly)
        ws_client.on_message = self._on_message

        # 2) Patch the WebSocketApp callback (this is the one actually invoked
        #    by the websocket-client library when frames arrive).
        ws_app = getattr(ws_client, "wss", None)
        if ws_app is not None:
            self._original_wss_on_message = ws_app.on_message
            ws_app.on_message = self._on_message
            elog.info("[interceptor] installed on WebsocketClient.on_message "
                      "AND WebSocketApp.on_message")
        else:
            elog.warn("[interceptor] WebSocketApp (wss) not yet available — "
                      "only patched WebsocketClient.on_message. "
                      "Live frames may NOT be captured.")
        return True

    def restore(self) -> None:
        """Restore the original on_message handlers."""
        try:
            # Restore WebSocketApp callback first
            if self._ws_client is not None:
                ws_app = getattr(self._ws_client, "wss", None)
                if ws_app is not None and self._original_wss_on_message is not None:
                    ws_app.on_message = self._original_wss_on_message
                # Restore WebsocketClient method
                if self._original_on_message is not None:
                    self._ws_client.on_message = self._original_on_message
                elog.info("[interceptor] original handlers restored")
        except Exception:
            pass

    def _on_message(self, wss, msg) -> None:
        """Capture binary frames + tick arrays; chain text to original.

        With DEBUG_WS_TRAFFIC enabled, every frame is logged for diagnosis:
          - text frames: size + first DEBUG_TEXT_PREVIEW_CHARS chars
          - binary frames: size + first DEBUG_BINARY_PREVIEW_BYTES hex bytes
                            + UTF-8 preview (after 0x04 strip)
        """
        # === DEBUG LOGGING ===
        # Log a frame ONLY if:
        #   - DEBUG_WS_TRAFFIC is True (log everything), OR
        #   - DEBUG_WS_TYPES contains a substring that matches the frame content
        if DEBUG_WS_TRAFFIC or DEBUG_WS_TYPES:
            try:
                if isinstance(msg, (bytes, bytearray)):
                    raw = bytes(msg)
                    utf8_preview = ""
                    if len(raw) > 0:
                        offset = 1 if raw[0] == 0x04 else 0
                        utf8_preview = raw[offset:offset + 100].decode('utf-8', errors='replace')
                    # Check if any DEBUG_WS_TYPE matches the content
                    should_log = DEBUG_WS_TRAFFIC or any(
                        t in utf8_preview for t in DEBUG_WS_TYPES
                    )
                    if should_log:
                        preview_hex = raw[:DEBUG_BINARY_PREVIEW_BYTES].hex(' ')
                        elog.debug(f"[ws-debug] BINARY {len(raw):,}B | hex: {preview_hex} | utf8: {utf8_preview!r}")
                else:
                    text = msg if isinstance(msg, str) else msg.decode("utf-8", errors="ignore")
                    should_log = DEBUG_WS_TRAFFIC or any(t in text for t in DEBUG_WS_TYPES)
                    if should_log:
                        preview = text[:DEBUG_TEXT_PREVIEW_CHARS]
                        trunc = "…" if len(text) > DEBUG_TEXT_PREVIEW_CHARS else ""
                        elog.debug(f"[ws-debug] TEXT {len(text):,}c | {preview!r}{trunc}")
            except Exception as e:
                elog.debug(f"[ws-debug] preview error: {e}")

        # === CAPTURE ===
        if isinstance(msg, (bytes, bytearray)):
            # Binary frame: try to capture (instruments/ticks/payout)
            self._try_capture_binary(bytes(msg))

            # CRITICAL: also pass decoded history/list/v2 frames to the
            # original handler so that candles_ready events fire.
            # The original on_message in OTC_canda_.py only parses text
            # frames where msg_str[1] in ('[', '{'), so binary history
            # frames are NEVER processed by it — which means
            # get_historical_candles() returns 0 candles!
            #
            # We decode the binary frame, check if it looks like a history
            # response, and if so, wrap it as a fake text message that
            # the original handler can parse.
            try:
                raw = bytes(msg)
                if len(raw) > 0 and raw[0] == 0x04:
                    text_candidate = raw[1:].decode('utf-8', errors='ignore')
                    # Find first '[' or '{'
                    start_idx = -1
                    for i, ch in enumerate(text_candidate):
                        if ch in ('[', '{'):
                            start_idx = i
                            break
                    if start_idx >= 0:
                        # Try to parse as JSON to verify it's a real payload
                        try:
                            parsed = json.loads(text_candidate[start_idx:])
                            # Check if it's a history response (has 'asset' and 'history')
                            if isinstance(parsed, dict) and "asset" in parsed and "history" in parsed:
                                # Wrap as a fake text message that the original handler can parse
                                # The original handler expects msg_str[1] in ('[', '{')
                                # so we add a '4' prefix (Engine.IO MESSAGE marker)
                                fake_msg = f"4{json.dumps(parsed)}"
                                if self._original_on_message is not None:
                                    try:
                                        self._original_on_message(wss, fake_msg)
                                    except Exception as e:
                                        elog.debug(f"[interceptor] history forward raised: {e}")
                        except Exception:
                            pass
            except Exception:
                pass
        else:
            text = msg if isinstance(msg, str) else msg.decode("utf-8", errors="ignore")
            # Detect ANY _placeholder announcement — track which type of
            # binary frame is coming next. The Quotex server sends:
            #   451-["instruments/list",{...}]     → instruments list (profit %)
            #   451-["depth/change",{...}]          → payout % per asset
            #   451-["quotes/stream",{...}]         → live price ticks
            #   451-["history/list/v2",{...}]       → historical candles (ticks)
            if "_placeholder" in text:
                if "instruments/list" in text:
                    if not self._expecting_instruments_binary:
                        self._expecting_instruments_binary = True
                        elog.info("[interceptor] received 451-['instruments/list',{...}] announcement")
                    self._temp_status_instruments = text
                elif "depth/change" in text:
                    self._expecting_depth_change_binary = True
                elif "quotes/stream" in text:
                    self._expecting_quotes_stream_binary = True
                elif "orders/closed" in text or "orders/opened" in text:
                    self._expecting_orders_binary = True
                elif "history/list" in text or "history/load" in text:
                    self._temp_status_history = text
            # Try to extract live ticks from EVERY text frame (not just '42'-prefixed)
            self._try_extract_ticks_from_text(text)

        # === CHAIN TO ORIGINAL ===
        if self._original_on_message is not None:
            try:
                self._original_on_message(wss, msg)
            except Exception as e:
                elog.debug(f"[interceptor] original on_message raised: {e}")

    def _try_capture_binary(self, data: bytes) -> None:
        """Try to decode a binary frame as JSON (with 0x04 strip) or msgpack.

        Ported and enhanced from wedsoket_.py's _onMessage pattern:
          1. Strip leading 0x04 byte (Engine.IO binary marker)
          2. Find first '[' or '{' and JSON-parse the rest
          3. Fallback to msgpack if JSON fails

        Handles BOTH instrument formats Quotex may send:
          - Dict form:  [{"asset":"USDARS_otc","profit":92,"enabled":true}, ...]
          - Array form: [[1,"USDARS_otc","USD/ARS",...,92,...,true], ...]
        """
        # Lower threshold (was 128) — some binary frames are smaller
        if len(data) < 32:
            return

        decoded = None
        decode_strategy = "none"

        # Strategy 1: strip 0x04, then JSON (the working Node.js pattern)
        candidate = data[1:] if data[0] == 0x04 else data
        try:
            text = candidate.decode("utf-8", errors="ignore")
            start_idx = -1
            for i, ch in enumerate(text):
                if ch in ('[', '{'):
                    start_idx = i
                    break
            if start_idx >= 0:
                parsed = json.loads(text[start_idx:])
                if parsed is not None:
                    decoded = parsed
                    decode_strategy = "json+0x04-strip"
        except Exception:
            pass

        # Strategy 2: raw JSON (no byte strip)
        if decoded is None:
            try:
                text = data.decode("utf-8", errors="ignore")
                start_idx = -1
                for i, ch in enumerate(text):
                    if ch in ('[', '{'):
                        start_idx = i
                        break
                if start_idx >= 0:
                    parsed = json.loads(text[start_idx:])
                    if parsed is not None:
                        decoded = parsed
                        decode_strategy = "json-raw"
            except Exception:
                pass

        # Strategy 3: msgpack fallback (rare, but possible)
        if decoded is None:
            try:
                import msgpack
                decoded = msgpack.unpackb(data, raw=False, strict_map_key=False)
                decode_strategy = "msgpack"
            except Exception:
                pass

        if decoded is None:
            # Debug: log unrecognized binary frames
            if len(data) >= 100:
                preview_hex = data[:32].hex(' ')
                elog.debug(f"[binary] unrecognized frame: {len(data)} bytes, "
                           f"hex: {preview_hex}")
            return

        # Route the decoded payload based on what we're expecting.

        # Case A: orders/closed or orders/opened → REAL payout % from trades
        # Format: [{"id":"...","asset":"USDMXN_otc","percentProfit":92,...}, ...]
        if self._expecting_orders_binary:
            self._expecting_orders_binary = False
            self._handle_orders(decoded)
            return

        # Case B: depth/change → payout % per asset (fluctuating CALL/PUT)
        if self._expecting_depth_change_binary:
            self._expecting_depth_change_binary = False
            self._handle_depth_change(decoded)
            return

        # Case C: quotes/stream → live price ticks
        if self._expecting_quotes_stream_binary:
            self._expecting_quotes_stream_binary = False
            self._handle_quotes_stream(decoded)
            return

        # Case D: instruments/list → full instruments list
        if self._expecting_instruments_binary or self._looks_like_instruments(decoded):
            self._handle_instruments(decoded, decode_strategy, len(data))
            self._expecting_instruments_binary = False
            self._temp_status_instruments = ""
            return

        # Case E: historical candles (history/list/v2 response)
        if self._temp_status_history or self._looks_like_history(decoded):
            self._handle_history(decoded)
            self._temp_status_history = ""
            return

    def _handle_orders(self, data: Any) -> None:
        """Handle orders/closed/list binary frame — the REAL payout source.

        Each order contains:
          - asset: the OTC pair name
          - percentProfit: the REAL payout % (e.g. 92)
          - profit: actual profit amount
          - amount: investment amount

        This is the most reliable source of payout % because it reflects
        actual executed trades, not the fluctuating CALL/PUT values
        from depth/change.

        Strategy: extract percentProfit for each asset and store as
        the AUTHORITATIVE payout (overwrites any value from depth/change).
        """
        if not isinstance(data, list):
            return

        new_count = 0
        for order in data:
            if not isinstance(order, dict):
                continue
            asset = order.get("asset")
            percent_profit = order.get("percentProfit")
            if asset and percent_profit is not None:
                try:
                    p_int = int(percent_profit)
                    # Store as the authoritative payout
                    self.profit_by_asset[asset] = p_int
                    # Also update max
                    if p_int > self.max_profit_by_asset.get(asset, 0):
                        self.max_profit_by_asset[asset] = p_int
                    # Track history (orders are the MOST reliable source)
                    self.profit_history[asset].append(p_int)
                    if len(self.profit_history[asset]) > 30:
                        self.profit_history[asset] = self.profit_history[asset][-30:]
                    if asset not in self.enabled_by_asset:
                        self.enabled_by_asset[asset] = True
                    new_count += 1
                except (ValueError, TypeError):
                    pass

        if new_count > 0 and DEBUG_WS_TRAFFIC:
            elog.info(f"[orders/closed] REAL payout captured for {new_count} trades | "
                      f"assets: {len(self.max_profit_by_asset)}")

    def _handle_depth_change(self, data: Any) -> None:
        """Handle depth/change binary frame: payout % per asset.

        If an asset is LOCKED (instruments/list already provided the real payout),
        SKIP it — depth/change values are unreliable (alternating CALL/PUT).
        Only update assets that have NOT been locked by instruments/list yet.
        """
        if not isinstance(data, list):
            return

        new_count = 0
        for item in data:
            if isinstance(item, list) and len(item) >= 2:
                asset = item[0]
                payout = item[1]
                if isinstance(asset, str) and isinstance(payout, (int, float)):
                    # SKIP if this asset is locked by instruments/list
                    if self.instruments_locked.get(asset, False):
                        continue

                    payout_int = int(payout)
                    self.profit_history[asset].append(payout_int)
                    if len(self.profit_history[asset]) > 30:
                        self.profit_history[asset] = self.profit_history[asset][-30:]
                    self.profit_by_asset[asset] = payout_int
                    if payout_int > self.max_profit_by_asset.get(asset, 0):
                        self.max_profit_by_asset[asset] = payout_int
                    if asset not in self.enabled_by_asset:
                        self.enabled_by_asset[asset] = True
                    new_count += 1

        if new_count > 0 and DEBUG_WS_TRAFFIC:
            elog.info(f"[depth/change] +{new_count} updates | "
                      f"assets tracked: {len(self.max_profit_by_asset)}")

    def _handle_quotes_stream(self, data: Any) -> None:
        """Handle quotes/stream binary frame: live price ticks.

        Format: [["USDARS_otc",1792778133.816,1621.74,1], ...]
        Each entry: [asset_name, timestamp, price, direction(0/1)]
        """
        if not isinstance(data, list):
            return
        new_count = 0
        for tick in data:
            if isinstance(tick, list) and len(tick) >= 3:
                asset = tick[0]
                price = tick[2]
                if isinstance(asset, str) and isinstance(price, (int, float)):
                    self.live_prices[asset] = float(price)
                    self.live_ticks_seen[asset] += 1
                    self.last_tick_at[asset] = time.time()
                    new_count += 1
        if new_count > 0 and DEBUG_WS_TRAFFIC:
            # Show total ticks received across all assets (more meaningful than unique count)
            # Only log when DEBUG_WS_TRAFFIC is True (too noisy otherwise — ticks arrive
            # many times per second).
            total_ticks = sum(self.live_ticks_seen.values())
            elog.debug(f"[quotes/stream] +{new_count} tick | "
                       f"total ticks: {total_ticks} | assets tracked: {len(self.live_prices)}")

    @staticmethod
    def _looks_like_instruments(data: Any) -> bool:
        """Heuristic: is this a list of instrument dicts OR arrays?

        Supports both formats Quotex may send:
          - Dict form:  [{"asset":"USDARS_otc","profit":92,...}, ...]
          - Array form: [[1,"USDARS_otc","USD/ARS",...,92,...,true], ...]
        """
        if not isinstance(data, list) or len(data) < 5:
            return False
        sample = data[:5]

        # Dict form: each item must be a dict with asset/id/symbol/name
        if all(isinstance(item, dict) for item in sample):
            for item in sample:
                if not any(k in item for k in ("asset", "id", "symbol", "name")):
                    return False
            return True

        # Array form: each item must be a list with >= 6 elements
        # (id, symbol, name, type, ..., payout, ..., open)
        if all(isinstance(item, list) and len(item) >= 6 for item in sample):
            # Second element should be a string (asset name)
            if all(isinstance(item[1], str) for item in sample):
                return True

        return False

    @staticmethod
    def _looks_like_history(data: Any) -> bool:
        if not isinstance(data, list) or len(data) < 1:
            return False
        first = data[0]
        if isinstance(first, dict) and 'time' in first:
            return True
        if isinstance(first, list) and len(first) >= 5:
            return True
        return False

    def _handle_instruments(self, data: Any, strategy: str, size: int) -> None:
        """Process the instruments list and extract profit % per asset.

        Handles BOTH formats (mirrors wedsoket_.py's printAssetsTable logic):
          - Dict form:  item.get("profit") or item.get("payout")
          - Array form:  item[5] (payout at index 5)
        And enabled status:
          - Dict form:  item.get("enabled") or item.get("open") or item.get("isOpen")
          - Array form: item[14] (open flag at index 14)
        """
        # Unwrap Socket.IO envelope if present
        if isinstance(data, list) and len(data) == 2 and isinstance(data[0], str):
            data = data[1]
        if isinstance(data, dict):
            if isinstance(data.get("instruments"), list):
                data = data["instruments"]
            elif isinstance(data.get("list"), list):
                data = data["list"]

        if not isinstance(data, list):
            return

        self.instruments = data
        dict_count = 0
        array_count = 0
        for item in data:
            # === Dict form ===
            if isinstance(item, dict):
                dict_count += 1
                # Asset name: try multiple field names
                asset = (item.get("asset") or item.get("name") or
                         item.get("symbol") or item.get("id"))
                # Profit %: try "profit" then "payout"
                profit = item.get("profit")
                if profit is None:
                    profit = item.get("payout")
                # Enabled: try "enabled", "open", "isOpen"
                enabled = None
                for k in ("enabled", "open", "isOpen"):
                    if k in item:
                        enabled = bool(item[k])
                        break
                if asset:
                    if profit is not None:
                        try:
                            p_int = int(profit)
                        except (ValueError, TypeError):
                            try:
                                p_int = int(float(profit))
                            except Exception:
                                p_int = 0
                        # FILTER: only accept payout in valid range [70, 94]
                        if p_int and 70 <= p_int <= 94:
                            self.profit_by_asset[asset] = p_int
                            if p_int > self.max_profit_by_asset.get(asset, 0):
                                self.max_profit_by_asset[asset] = p_int
                    if enabled is not None:
                        self.enabled_by_asset[asset] = enabled

            # === Array form: [id, symbol, name, type, ?, payout(5), ..., open(14)] ===
            elif isinstance(item, list) and len(item) >= 6:
                array_count += 1
                asset = item[1] if isinstance(item[1], str) else None
                profit = item[5] if len(item) > 5 else None
                enabled = bool(item[14]) if len(item) > 14 else None
                if asset:
                    if profit is not None:
                        try:
                            p_int = int(profit)
                        except (ValueError, TypeError):
                            try:
                                p_int = int(float(profit))
                            except Exception:
                                p_int = 0
                        # Store in instruments_profit_by_asset (AUTHORITATIVE)
                        # and LOCK it — depth/change cannot overwrite this value.
                        if p_int:
                            self.instruments_profit_by_asset[asset] = p_int
                            self.instruments_locked[asset] = True
                    if enabled is not None:
                        self.enabled_by_asset[asset] = enabled

        elog.success(f"[instruments] captured via {strategy}: {len(data)} entries "
                     f"({dict_count} dict, {array_count} array), "
                     f"{len(self.instruments_profit_by_asset)} payout %, {size:,} bytes")
        if not self.instruments_ready.is_set():
            self.instruments_ready.set()

    def _handle_history(self, data: Any) -> None:
        """Process a historical candles response."""
        # Unwrap envelope
        if isinstance(data, list) and len(data) == 2 and isinstance(data[0], str):
            payload = data[1]
            if isinstance(payload, dict):
                asset = payload.get("asset") or payload.get("symbol")
                candles = payload.get("history") or payload.get("data") or payload.get("candles") or []
                if asset and candles:
                    self.candles_data[asset] = candles
                    self.candles_ready[asset].set()
                return
            if isinstance(payload, list):
                # No asset identifier; best-effort: store under "last"
                self.candles_data["_last"] = payload
                self.candles_ready["_last"].set()
                return
        elif isinstance(data, dict):
            asset = data.get("asset") or data.get("symbol")
            candles = data.get("history") or data.get("data") or data.get("candles") or []
            if asset and candles:
                self.candles_data[asset] = candles
                self.candles_ready[asset].set()
            return
        elif isinstance(data, list) and data and isinstance(data[0], list):
            # Bare list of candle arrays
            self.candles_data["_last"] = data
            self.candles_ready["_last"].set()
            return

    def _try_extract_ticks_from_text(self, text: str) -> None:
        """Extract live price ticks from any text frame.

        Tries multiple Quotex message formats:
          42["quotes/stream",[[asset, time, price], ...]]
          42["depth/change",[[asset, time, price], ...]]
          42[<event>,[[asset, time, price], ...]]
          42[<event>,{"data":[[asset, time, price], ...]}]

        Also handles raw JSON arrays (no Socket.IO prefix):
          [[asset, time, price], ...]
        """
        # Try to find ANY JSON array/object in the text and parse it.
        # The Socket.IO prefix (42, 451-, etc.) may or may not be present.
        # We search for the first '[' or '{' character.
        start_idx = -1
        for i, ch in enumerate(text):
            if ch in ('[', '{'):
                start_idx = i
                break
        if start_idx < 0:
            return

        try:
            json_str = text[start_idx:]
            parsed = json.loads(json_str)
        except Exception:
            return

        if parsed is None:
            return

        # Route to _extract_ticks which handles all payload shapes.
        # _extract_ticks handles both bare lists and Socket.IO envelopes.
        self._extract_ticks(parsed)

    def _extract_ticks(self, payload: Any) -> None:
        """Look for tick arrays in the payload and record prices.

        Handles ALL of these shapes (mirrors wedsoket_.py's tick handling):
          1. [[asset, time, price], ...]                    (bare list of ticks)
          2. ["quotes/stream", [[asset, time, price], ...]]  (Socket.IO envelope)
          3. {"asset": asset, "price": price, ...}           (single tick dict)
          4. {"data": [[asset, time, price], ...]}           (wrapped in 'data')
          5. [event_name, {"data": [...]}]                   (envelope + wrapper)
        """
        candidates = []

        # Shape 1: bare list of ticks
        if isinstance(payload, list):
            if payload and isinstance(payload[0], list):
                candidates = payload
            # Shape 2: Socket.IO envelope [event_name, payload]
            elif payload and isinstance(payload[0], str) and len(payload) >= 2:
                inner = payload[1]
                # Inner could be a list of ticks
                if isinstance(inner, list) and inner and isinstance(inner[0], list):
                    candidates = inner
                # Inner could be a dict with 'data' key (Shape 5)
                elif isinstance(inner, dict) and isinstance(inner.get("data"), list):
                    candidates = inner["data"]
                # Inner could be a single tick dict (Shape 3)
                elif isinstance(inner, dict) and "asset" in inner and "price" in inner:
                    candidates = [inner]

        # Shape 3: single tick dict at top level
        elif isinstance(payload, dict):
            if "asset" in payload and "price" in payload:
                candidates = [payload]
            # Shape 4: wrapped in 'data' key
            elif isinstance(payload.get("data"), list):
                candidates = payload["data"]

        # Extract prices from candidates
        new_ticks = 0
        for tick in candidates:
            if isinstance(tick, list) and len(tick) >= 3:
                asset = tick[0]
                price = tick[2]
                if isinstance(asset, str) and isinstance(price, (int, float)):
                    self.live_prices[asset] = float(price)
                    self.live_ticks_seen[asset] += 1
                    self.last_tick_at[asset] = time.time()
                    new_ticks += 1
            elif isinstance(tick, dict) and "asset" in tick and "price" in tick:
                asset = tick["asset"]
                price = tick["price"]
                if isinstance(asset, str) and isinstance(price, (int, float)):
                    self.live_prices[asset] = float(price)
                    self.live_ticks_seen[asset] += 1
                    self.last_tick_at[asset] = time.time()
                    new_ticks += 1

        if new_ticks > 0 and DEBUG_WS_TRAFFIC:
            elog.debug(f"[ticks] captured {new_ticks} new ticks "
                       f"(total assets tracked: {len(self.live_prices)})")

    # === Public API ===
    def get_profit(self, asset: str) -> Optional[int]:
        """Return the payout % for this asset.

        Priority:
          1. instruments_profit_by_asset — from instruments/list binary frame
             (AUTHORITATIVE — locked, cannot be overwritten by depth/change)
          2. profit_by_asset — last value from depth/change (for unlocked assets)
          3. None if no data available
        """
        # Priority 1: instruments/list (locked, authoritative)
        if asset in self.instruments_profit_by_asset:
            return self.instruments_profit_by_asset[asset]

        # Priority 2: last depth/change value (for unlocked assets only)
        return self.profit_by_asset.get(asset)

    def get_last_profit(self, asset: str) -> Optional[int]:
        """Return the LAST payout % seen (for debugging)."""
        return self.profit_by_asset.get(asset)

    def get_profit_history(self, asset: str) -> List[int]:
        """Return all payout values seen for this asset (for debugging)."""
        return list(self.profit_history.get(asset, []))

    def get_enabled(self, asset: str) -> Optional[bool]:
        return self.enabled_by_asset.get(asset)

    def get_live_price(self, asset: str) -> Optional[float]:
        return self.live_prices.get(asset)

    def get_stats(self, asset: str) -> Dict[str, Any]:
        return {
            'price': self.live_prices.get(asset),
            'ticks_seen': self.live_ticks_seen.get(asset, 0),
            'last_tick_ago': time.time() - self.last_tick_at[asset]
                             if asset in self.last_tick_at else None,
            'profit': self.get_profit(asset),  # max profit (real payout)
            'last_profit': self.profit_by_asset.get(asset),
            'profit_history': self.get_profit_history(asset),
            'enabled': self.enabled_by_asset.get(asset),
        }


# ============================================================================
# SECTION 9: NEVER-SLEEP ENGINE (ported from wedsoket_.py)
# ============================================================================
class NeverSleepEngine:
    """Runs four background asyncio tasks to keep the connection alive:

    1. keepalive_loop: ping every KEEPALIVE_PING_INTERVAL seconds
    2. stale_message_watchdog: detect silent connection (no msgs for 45s)
    3. auto_reconnect: rebuild connection on loss (exponential backoff)
    4. health_monitor: periodic state check (every 20s)

    All four loops are cancellable via stop_event.
    """

    def __init__(self, client_holder: 'ClientHolder', interceptor: MessageInterceptor):
        self.client_holder = client_holder
        self.interceptor = interceptor
        self.stop_event = asyncio.Event()
        self.tasks: List[asyncio.Task] = []
        self.connection_alive = True
        self.last_ping_at = 0.0
        self.last_message_at = time.time()
        self.connection_drops = 0
        self.last_drop_time = 0.0
        self.uptime_start = time.time()
        self.is_reconnecting = False

    def start(self):
        self.tasks = [
            asyncio.create_task(self.keepalive_loop()),
            asyncio.create_task(self.stale_message_watchdog()),
            asyncio.create_task(self.auto_reconnect()),
            asyncio.create_task(self.health_monitor()),
        ]
        elog.info("[never-sleep] background engine started (4 tasks)")

    async def stop(self):
        self.stop_event.set()
        for t in self.tasks:
            try:
                await asyncio.wait_for(t, timeout=2.0)
            except Exception:
                pass
        self.tasks.clear()

    def _mark_message_received(self):
        """Called by interceptor when any message arrives."""
        self.last_message_at = time.time()

    async def keepalive_loop(self):
        """Ping every KEEPALIVE_PING_INTERVAL seconds.

        Ported from wedsoket_.py:keepalive_loop.
        Sends engine.io ping ("2") + application tick ('42["tick"]')
        + periodically instruments/get to refresh the asset list.
        """
        tick_count = 0
        while not self.stop_event.is_set():
            await asyncio.sleep(0.5)
            now = time.time()
            if now - self.last_ping_at < KEEPALIVE_PING_INTERVAL:
                continue
            self.last_ping_at = now
            client = self.client_holder.client
            if client is None or client.api is None:
                continue
            try:
                # engine.io ping
                client.api.send_websocket_request("2", no_force_send=False)
                # application tick
                client.api.send_websocket_request('42["tick"]', no_force_send=False)
                # periodic instruments refresh (every 3rd ping)
                if tick_count % 3 == 0:
                    client.api.send_websocket_request('42["instruments/get"]', no_force_send=False)
                tick_count += 1
            except Exception as e:
                elog.debug(f"[keepalive] ping failed: {e}")

    async def stale_message_watchdog(self):
        """Recycle connection if no messages for STALE_MESSAGE_TIMEOUT seconds.

        Ported from wedsoket_.py:stale_message_watchdog.
        """
        while not self.stop_event.is_set():
            await asyncio.sleep(STALE_WATCHDOG_INTERVAL)
            client = self.client_holder.client
            if client is None or client.api is None:
                continue
            try:
                # Update last_message_at from the API's own tracking
                api_last = getattr(client.api, 'last_message_at', None)
                if api_last is not None:
                    self.last_message_at = api_last

                silent_for = time.time() - self.last_message_at
                if silent_for > STALE_MESSAGE_TIMEOUT:
                    elog.warn(f"[watchdog] no messages for {silent_for:.1f}s "
                              f"(>{STALE_MESSAGE_TIMEOUT}s); recycling connection")
                    if self.last_drop_time == 0:
                        self.last_drop_time = time.time()
                    self.connection_alive = False
                    # Force-close WS to trigger on_close → auto_reconnect
                    try:
                        ws_client = getattr(client.api, 'websocket_client', None)
                        if ws_client and ws_client.wss:
                            ws_client.wss.close()
                    except Exception:
                        pass
            except Exception as e:
                elog.debug(f"[watchdog] error: {e}")

    async def auto_reconnect(self):
        """Rebuild connection on loss — ported from wedsoket_.py:auto_reconnect.

        Key differences from the previous version:
          1. IMMEDIATE reconnect on first failure (delay=0)
          2. Exponential backoff ONLY after consecutive failures
          3. Re-installs the interceptor on the new WebSocketApp
          4. Re-subscribes to all assets after reconnect
          5. Uses the RECONNECTING flag to prevent overlapping attempts
        """
        consecutive_failures = 0
        while not self.stop_event.is_set():
            await asyncio.sleep(RECONNECT_CHECK_INTERVAL)

            # Record drop time if connection is dead and not yet recorded
            if not self.connection_alive and self.last_drop_time == 0:
                self.last_drop_time = time.time()
                elog.info(f"[reconnect] connection loss detected at {self.last_drop_time:.0f}; "
                          f"will re-fetch if outage > {LONG_DISCONNECT_THRESHOLD}s")

            # Skip if connection is alive or already reconnecting
            if self.connection_alive or self.is_reconnecting:
                consecutive_failures = 0
                continue

            self.is_reconnecting = True
            try:
                h = self.client_holder
                if not (h.email and h.password):
                    elog.warn("[reconnect] no credentials available — cannot reconnect")
                    self.is_reconnecting = False
                    continue

                # IMMEDIATE reconnect on first failure, backoff after that
                # (same as wedsoket_.py)
                delay = 0 if consecutive_failures == 0 else min(
                    RECONNECT_BACKOFF_BASE * (2 ** (consecutive_failures - 1)),
                    RECONNECT_BACKOFF_MAX
                )
                if delay > 0:
                    elog.info(f"[reconnect] connection lost, retrying in {delay:.0f}s...")
                    await asyncio.sleep(delay)
                else:
                    elog.info("[reconnect] connection lost, reconnecting immediately...")

                # Create new Quotex client and connect
                new_client = Quotex(
                    email=h.email, password=h.password,
                    host="quotex.com", lang="en", proxies=h.proxies,
                )
                check, reason = await new_client.connect()

                if check:
                    elog.success("[reconnect] reconnect successful, restarting streams...")
                    consecutive_failures = 0

                    # Switch to PRACTICE account
                    try:
                        await new_client.change_account("PRACTICE")
                        await asyncio.sleep(0.5)
                    except Exception:
                        pass

                    # Update last_message_at to prevent stale watchdog
                    if new_client.api is not None:
                        new_client.api.last_message_at = time.time()

                    # Close old client
                    try:
                        if self.client_holder.client:
                            await self.client_holder.client.close()
                    except Exception:
                        pass

                    # Swap in new client
                    self.client_holder.client = new_client
                    self.connection_alive = True
                    self.last_message_at = time.time()

                    # Calculate drop duration
                    drop_duration = 0.0
                    if self.last_drop_time > 0:
                        drop_duration = time.time() - self.last_drop_time
                        if drop_duration > LONG_DISCONNECT_THRESHOLD:
                            elog.warn(f"[reconnect] LONG disconnect: {drop_duration/60:.1f} min "
                                      f"> {LONG_DISCONNECT_THRESHOLD/60:.0f} min threshold")
                        else:
                            elog.info(f"[reconnect] short disconnect ({drop_duration:.1f}s)")

                    self.last_drop_time = 0
                    self.connection_drops += 1

                    # Re-install interceptor on new WS client
                    self.interceptor.client = new_client
                    self.interceptor.install()

                    # Re-subscribe to all assets (depth/follow + chart_notification)
                    try:
                        for asset in OTC_ASSETS:
                            new_client.api.send_websocket_request(
                                f'42["instruments/update",{{"asset":"{asset}","period":60}}]',
                                no_force_send=False,
                            )
                            new_client.api.send_websocket_request(
                                f'42["depth/follow","{asset}"]', no_force_send=False
                            )
                        new_client.api.send_websocket_request(
                            '42["chart_notification/get"]', no_force_send=False
                        )
                        elog.success(f"[reconnect] re-subscribed to {len(OTC_ASSETS)} assets")
                    except Exception as e:
                        elog.warn(f"[reconnect] failed to re-subscribe: {e}")

                else:
                    err = str(reason) if reason else "Unknown"
                    elog.warn(f"[reconnect] attempt failed: {err}")
                    consecutive_failures += 1

            except Exception as e:
                elog.warn(f"[reconnect] unexpected error: {e}")
                consecutive_failures += 1
            finally:
                self.is_reconnecting = False

    async def health_monitor(self):
        """Periodic health check (every HEALTH_CHECK_INTERVAL seconds).

        Ported from wedsoket_.py:health_monitor.
        """
        while not self.stop_event.is_set():
            await asyncio.sleep(HEALTH_CHECK_INTERVAL)
            client = self.client_holder.client
            if client is None or client.api is None:
                continue
            try:
                state = getattr(client.api, 'state', None)
                if state is None:
                    continue
                alive = bool(getattr(state, 'check_accepted_connection', False))
                if not alive and self.connection_alive:
                    elog.warn("[health] connection marked dead by health monitor")
                    self.connection_alive = False
                    if self.last_drop_time == 0:
                        self.last_drop_time = time.time()
                elif alive and not self.connection_alive:
                    # State says alive but we thought it was dead — refresh
                    self.connection_alive = True
                    self.last_drop_time = 0
                    elog.success("[health] connection restored (state confirms)")
            except Exception as e:
                elog.debug(f"[health] error: {e}")

    def stats(self) -> Dict[str, Any]:
        return {
            'uptime_seconds': time.time() - self.uptime_start,
            'connection_alive': self.connection_alive,
            'connection_drops': self.connection_drops,
            'last_drop_ago': time.time() - self.last_drop_time if self.last_drop_time else None,
            'last_ping_ago': time.time() - self.last_ping_at if self.last_ping_at else None,
            'last_message_ago': time.time() - self.last_message_at,
            'is_reconnecting': self.is_reconnecting,
        }


# ============================================================================
# SECTION 10: CLIENT HOLDER
# ============================================================================
class ClientHolder:
    """Holds the active Quotex client. Allows swapping on reconnect."""

    def __init__(self, client: Optional[Quotex], email: str = '', password: str = '',
                 proxies: Optional[str] = None):
        self.client = client
        self.email = email
        self.password = password
        self.proxies = proxies
        self.label = email or 'N/A'


# ============================================================================
# SECTION 11: LIVE PRICE SUBSCRIBER
# ============================================================================
class LivePriceSubscriber:
    """Subscribes to live price updates for one or more assets.

    Uses the same subscription messages as wedsoket_.py:
      42["instruments/update",{"asset":"ASSET_otc","period":60}]
      42["depth/follow","ASSET_otc"]
      42["chart_notification/get"]
    """

    def __init__(self, interceptor: MessageInterceptor):
        self.interceptor = interceptor
        self.subscribed_assets: set = set()

    def subscribe(self, asset: str, period: int = 60) -> None:
        api = self.interceptor.client.api
        try:
            api.send_websocket_request(
                f'42["instruments/update",{{"asset":"{asset}","period":{period}}}]',
                no_force_send=False,
            )
            api.send_websocket_request(f'42["depth/follow","{asset}"]', no_force_send=False)
            api.send_websocket_request('42["chart_notification/get"]', no_force_send=False)
            self.subscribed_assets.add(asset)
        except Exception as e:
            elog.warn(f"[live] failed to subscribe {asset}: {e}")

    def subscribe_all(self, assets: List[str], period: int = 60) -> None:
        for asset in assets:
            self.subscribe(asset, period)

    def refresh_payouts(self, assets: List[str]) -> None:
        """Force-refresh payout % for each asset by sending multiple requests.

        Sends:
          1. chart_notification/get for each asset (forces depth/change push)
          2. orders/closed (forces server to push closed orders with REAL payout)
          3. instruments/get (forces full instruments list push)

        The orders/closed response is the MOST reliable source because it
        contains percentProfit from actual executed trades.
        """
        api = self.interceptor.client.api
        for asset in assets:
            try:
                api.send_websocket_request(
                    f'42["instruments/update",{{"asset":"{asset}","period":60}}]',
                    no_force_send=False,
                )
                api.send_websocket_request(
                    f'42["chart_notification/get",{{"asset":"{asset}","version":"1.0.0"}}]',
                    no_force_send=False,
                )
                api.send_websocket_request(f'42["depth/follow","{asset}"]', no_force_send=False)
            except Exception as e:
                elog.debug(f"[refresh] failed for {asset}: {e}")
        # Request closed orders (contains REAL percentProfit)
        try:
            api.send_websocket_request('42["orders/closed"]', no_force_send=False)
        except Exception:
            pass
        # Request instruments list (full payout data)
        try:
            api.send_websocket_request('42["instruments/get"]', no_force_send=False)
        except Exception:
            pass

    def unsubscribe(self, asset: str) -> None:
        api = self.interceptor.client.api
        try:
            api.send_websocket_request(f'42["depth/unfollow","{asset}"]', no_force_send=False)
            self.subscribed_assets.discard(asset)
        except Exception:
            pass

    def unsubscribe_all(self) -> None:
        for asset in list(self.subscribed_assets):
            self.unsubscribe(asset)


# ============================================================================
# SECTION 12: CANDLE FETCHER (chunked, with gap-fill)
# ============================================================================
class CandleFetcher:
    """Fetches exactly N candles for an asset — same method as OTC_canda_.py.

    Instead of the broken "overlapping chunks" approach, this uses the SAME
    method as the original OTC_canda_.py:
      1. Calculate days needed: days = ceil(target_count * timeframe_min / 1440) + buffer
      2. Call client.get_historical_candles(asset, amount_of_seconds=days*86400,
         period=period_seconds, max_workers=5) — this is ONE call that fetches
         the entire span, with max_workers=5 doing parallel chunks internally.
      3. Dedup by timestamp + sort + gap-fill
      4. Truncate to last target_count candles (or pad if insufficient)
    """

    def __init__(self, client_holder: ClientHolder, interceptor: MessageInterceptor):
        self.client_holder = client_holder
        self.interceptor = interceptor

    async def fetch_exactly_n(self, asset: str, timeframe_min: int,
                              target_count: int = TARGET_CANDLE_COUNT,
                              progress: bool = True) -> List[Dict]:
        """Fetch exactly target_count candles for asset — same method as OTC_canda_.py.

        Uses the EXACT same approach as fetch_candles_for_asset in OTC_canda_.py:
          1. Calculate amount_of_seconds from target_count + buffer
          2. Call client.get_historical_candles with max_workers=5 and progress_callback
          3. On failure, RETRY up to MAX_FETCH_RETRIES times with exponential backoff
          4. Dedup by timestamp + sort + gap-fill + truncate to target_count
        """
        period_seconds = int(timeframe_min * 60)
        display_name = f"{asset} (M{timeframe_min})"
        client = self.client_holder.client
        if client is None:
            elog.error(f"No client for {asset}")
            return []

        # === Calculate MINIMUM seconds needed for target_count candles ===
        # +20% buffer to ensure enough after dedup
        # NO minimum 1 day — Quotex accepts shorter requests after the
        # interceptor fix (forwarding history binary frames to original handler).
        total_seconds_needed = target_count * period_seconds
        amount_of_seconds = int(total_seconds_needed * 1.2)
        # For display: convert to days/hours
        days_float = amount_of_seconds / 86400
        if days_float >= 1:
            duration_str = f"{days_float:.2f} day(s)"
        else:
            hours_float = amount_of_seconds / 3600
            duration_str = f"{hours_float:.1f} hour(s)"

        # Timeout: 60s minimum, +1s per 1000 seconds of history
        timeout = max(60, amount_of_seconds // 1000)

        print(f"\n  {paint_bold('Fetching ', C2.BRIGHT_CYAN)}"
              f"{paint_bold(f'{target_count} candles', C2.BRIGHT_GREEN)} — {display_name}")
        expected_candles = amount_of_seconds // period_seconds
        elog.info(f"Requesting {duration_str} of {asset} history "
                  f"({amount_of_seconds:,}s = ~{expected_candles:,} candles, need {target_count})")

        # === RETRY LOOP — same as OTC_canda_.py ===
        candles = []
        for attempt in range(1, MAX_FETCH_RETRIES + 1):
            # Check connection before each attempt
            if (client is None or client.api is None
                    or not getattr(client.api.state, 'check_accepted_connection', False)):
                elog.error(f"Connection dead before attempt {attempt}; aborting.")
                return []

            # Progress tracker (thread-safe) — shared by all 5 workers
            progress_state = {
                'candles': 0,
                'oldest_ts': int(time.time()),
                'start_ts': int(time.time()),
                'target_ts': int(time.time()) - amount_of_seconds,
                'lock': threading.Lock(),
                'last_print': 0.0,
                'fetch_start': time.time(),
                'worker_candles': [0] * FETCH_MAX_WORKERS,
            }

            def progress_callback(seconds_done, total_seconds, candles_count, worker_label):
                now = time.time()
                with progress_state['lock']:
                    try:
                        wid = int(worker_label.split('-')[1]) if '-' in worker_label else 0
                        if 0 <= wid < FETCH_MAX_WORKERS:
                            # REPLACE (not accumulate) — each callback gives the
                            # total candles THIS worker has fetched so far.
                            # Workers fetch overlapping windows, so accumulation
                            # would double-count. Use max to track the highest.
                            if candles_count > progress_state['worker_candles'][wid]:
                                progress_state['worker_candles'][wid] = candles_count
                    except Exception:
                        pass
                    # Total = sum of unique candles per worker (approximate)
                    progress_state['candles'] = sum(progress_state['worker_candles'])
                    current_oldest = progress_state['start_ts'] - seconds_done
                    if current_oldest < progress_state['oldest_ts']:
                        progress_state['oldest_ts'] = current_oldest
                    if now - progress_state['last_print'] < 0.3:
                        return
                    progress_state['last_print'] = now

                    elapsed = now - progress_state['fetch_start']
                    total_span = progress_state['start_ts'] - progress_state['target_ts']
                    done_span = progress_state['start_ts'] - progress_state['oldest_ts']
                    pct = min(done_span / total_span, 1.0) if total_span > 0 else 0
                    bar_len = 30
                    filled = int(bar_len * pct)
                    bar = paint(C2.BRIGHT_GREEN, '█' * filled) + paint(C2.DIM, '░' * (bar_len - filled))
                    speed = progress_state['candles'] / elapsed if elapsed > 0 else 0
                    if pct > 0.01:
                        eta = elapsed * (1.0 - pct) / pct
                        eta_str = f"{int(eta//60):02d}:{int(eta%60):02d}"
                    else:
                        eta_str = "  ?  "
                    elapsed_str = f"{int(elapsed//60):02d}:{int(elapsed%60):02d}"
                    candle_count = progress_state['candles']
                    sys.stdout.write(
                        f"\r  {paint('[', C2.DIM)}{bar}{paint(']', C2.DIM)} "
                        f"{pct*100:5.1f}% | "
                        f"{paint_bold(str(candle_count), C2.BRIGHT_GREEN)}"
                        f"/{target_count} | "
                        f"{elapsed_str} | "
                        f"{speed:>5.0f} c/s | "
                        f"ETA {eta_str}   "
                    )
                    sys.stdout.flush()

            elog.info(f"Attempt {attempt}/{MAX_FETCH_RETRIES} ...")
            fetch_start = time.time()
            try:
                candles_raw = await asyncio.wait_for(
                    client.get_historical_candles(
                        asset,
                        amount_of_seconds=amount_of_seconds,
                        period=period_seconds,
                        max_workers=FETCH_MAX_WORKERS,
                        progress_callback=progress_callback,
                    ),
                    timeout=timeout,
                )
                # Force a 100% progress print with ACTUAL count (not inflated)
                actual_count = len(candles_raw) if candles_raw else 0
                with progress_state['lock']:
                    progress_state['candles'] = actual_count
                    # Reset worker_candles to actual values (not accumulated sums)
                    progress_state['worker_candles'] = [actual_count, 0, 0, 0, 0]
                    progress_state['oldest_ts'] = progress_state['target_ts']
                    progress_state['last_print'] = 0
                if progress:
                    progress_callback(amount_of_seconds, amount_of_seconds, actual_count, "Worker-0")
                    print()
            except asyncio.TimeoutError:
                if progress: print()
                elog.warn(f"Attempt {attempt}/{MAX_FETCH_RETRIES}: fetch timed out.")
                candles_raw = []
            except Exception as e:
                if progress: print()
                elog.warn(f"Attempt {attempt}/{MAX_FETCH_RETRIES} raised: {e}")
                candles_raw = []

            if candles_raw:
                elapsed = time.time() - fetch_start
                elog.info(f"Received {len(candles_raw):,} raw candles in {int(elapsed)}s")
                candles = candles_raw
                break  # success, exit retry loop

            # Exponential backoff between retries (same as OTC_canda_.py)
            if attempt < MAX_FETCH_RETRIES:
                delay = min(RETRY_BACKOFF_BASE * (2 ** (attempt - 1)), RETRY_BACKOFF_MAX)
                elog.info(f"Retry in {delay:.1f}s...")
                await asyncio.sleep(delay)

        if not candles:
            elog.error(f"All {MAX_FETCH_RETRIES} attempts failed for {display_name}")
            return []

        # === DEDUP + FORMAT (same as OTC_canda_.py) ===
        candles_map: Dict[int, Dict] = {}
        for c in candles:
            if not isinstance(c, dict):
                continue
            try:
                ts = int(c.get("time", c.get("timestamp", 0)))
                aligned = (ts // period_seconds) * period_seconds
                o = float(c.get("open", 0))
                h = float(c.get("high", c.get("max", 0)))
                l = float(c.get("low", c.get("min", 0)))
                cl = float(c.get("close", 0))
                if aligned not in candles_map and o > 0 and h > 0 and l > 0 and cl > 0:
                    candles_map[aligned] = {
                        'time': aligned, 'open': o, 'high': h,
                        'low': l, 'close': cl,
                        'volume': int(c.get("volume", 0) or 0),
                    }
            except Exception:
                continue

        if not candles_map:
            elog.error(f"No valid candles after dedup for {asset}.")
            return []

        # Sort by time
        candles = sorted(candles_map.values(), key=lambda x: x['time'])
        elog.info(f"After dedup: {len(candles):,} unique candles "
                  f"({candles[0]['time']} → {candles[-1]['time']})")

        # ============================================================
        # GAP-FILL WITH REAL DATA (ported from wedsoket_.py:fill_gap_once)
        # ============================================================
        # Instead of just filling ALL gaps with flat candles (previous close),
        # we first fetch a SMALL batch of REAL recent candles (GAP_FILL_CANDLES=10)
        # and use them to REPLACE any synthetic (volume=0) candles in our data.
        # This gives more accurate OHLC data for the last few candles.
        #
        # Steps (same as wedsoket_.py:fill_gap_once + line 1701 comments):
        #   1. Fetch 1-SECOND candles (period=1) for the last N seconds
        #   2. Aggregate 1s candles into target timeframe using _aggregate_sub_minute
        #   3. Replace synthetic candles (volume=0) with real aggregated data
        #   4. Run _fill_missing_slots on the merged result
        #
        # wedsoket_.py line 1701:
        #   "1) fetch 1s candles -> aggregate to 1m (8-13 bridge candles, no gaps)"
        GAP_FILL_CANDLES = 10  # same as wedsoket_.py
        try:
            # Fetch 1-SECOND candles for maximum granularity
            # amount_of_seconds = 10 * period_seconds (e.g. 10 * 60 = 600s for M1)
            # period = 1 (1-second candles, NOT the target timeframe!)
            gap_fill_seconds = GAP_FILL_CANDLES * period_seconds
            elog.info(f"Fetching 1-second candles for gap-fill "
                      f"({gap_fill_seconds}s = ~{gap_fill_seconds} 1s candles)...")
            raw_1s_candles = await asyncio.wait_for(
                client.get_historical_candles(
                    asset,
                    amount_of_seconds=gap_fill_seconds,
                    period=1,  # ← 1-SECOND candles! (was period_seconds)
                    max_workers=1,
                    progress_callback=None,
                ),
                timeout=30,
            )

            # Aggregate 1s candles into target timeframe
            # (same as wedsoket_.py line 1701: "fetch 1s candles -> aggregate to 1m")
            if raw_1s_candles and len(raw_1s_candles) > 0:
                elog.info(f"Received {len(raw_1s_candles)} 1-second candles, "
                          f"aggregating to M{timeframe_min}...")
                real_candles = _aggregate_1s_to_target(raw_1s_candles, period_seconds)
                elog.info(f"Aggregated to {len(real_candles)} {timeframe_min}m candles")
            else:
                elog.warn(f"Gap-fill: no 1s candles returned — using flat fill only")
                real_candles = []

            if real_candles:
                # Build candle_map from existing candles
                candle_map: Dict[int, Dict] = {}
                for c in candles:
                    candle_map[c['time']] = c

                # Replace synthetic candles with real data
                current_period_start = (int(time.time()) // period_seconds) * period_seconds
                replaced_count = 0
                new_count = 0

                for c in real_candles:
                    if not isinstance(c, dict):
                        continue
                    try:
                        ts = int(c.get("time", c.get("timestamp", 0)))
                        aligned = (ts // period_seconds) * period_seconds
                        o = float(c.get("open", 0))
                        h = float(c.get("high", c.get("max", 0)))
                        l = float(c.get("low", c.get("min", 0)))
                        cl = float(c.get("close", 0))
                        v = int(c.get("volume", 0) or 0)

                        if o > 0 and h > 0 and l > 0 and cl > 0:
                            existing = candle_map.get(aligned)
                            if existing is None:
                                # Missing candle — add with real data
                                candle_map[aligned] = {
                                    'time': aligned, 'open': o, 'high': h,
                                    'low': l, 'close': cl, 'volume': v,
                                }
                                new_count += 1
                            elif aligned >= current_period_start:
                                # Current streaming candle — don't touch
                                continue
                            elif existing.get('volume', 1) == 0:
                                # Synthetic candle (volume=0) — REPLACE with real data
                                candle_map[aligned] = {
                                    'time': aligned, 'open': o, 'high': h,
                                    'low': l, 'close': cl, 'volume': v,
                                }
                                replaced_count += 1
                    except Exception:
                        continue

                # Rebuild candles from the updated map
                candles = sorted(candle_map.values(), key=lambda x: x['time'])
                elog.info(f"Gap-fill: replaced {replaced_count} synthetic + "
                          f"added {new_count} real candles")

                # Save BEFORE gap-fill snapshot for inspection
                _save_debug_json(candles, asset, timeframe_min, "before_flat_fill")
            else:
                elog.warn(f"Gap-fill: no real candles returned — using flat fill only")
        except Exception as e:
            elog.warn(f"Gap-fill fetch failed: {e} — using flat fill only")

        # Save BEFORE _fill_missing_slots snapshot for inspection
        _save_debug_json(candles, asset, timeframe_min, "before_fill_missing")

        # Apply flat gap-filling for any remaining gaps
        before_fill = len(candles)
        candles = _fill_missing_slots(candles, period_seconds, max_gap=GAP_FILL_MAX_SLOTS)
        after_fill = len(candles)
        filled_count = after_fill - before_fill
        if filled_count > 0:
            elog.warn(f"Filled {filled_count} remaining gaps with flat candles for {asset}.")

        # Truncate or pad to exactly target_count
        if len(candles) > target_count:
            candles = candles[-target_count:]
            elog.info(f"Truncated to last {target_count} candles.")
        elif len(candles) < target_count:
            first_ts = candles[0]['time']
            last_close = candles[0]['open']
            deficit = target_count - len(candles)
            for i in range(deficit, 0, -1):
                candles.insert(0, {
                    'time': first_ts - i * period_seconds,
                    'open': last_close, 'high': last_close,
                    'low': last_close, 'close': last_close, 'volume': 0,
                })
            elog.warn(f"Padded {deficit} candles at the start for {asset} "
                      f"(insufficient history).")

        elapsed_total = time.time() - fetch_start
        elog.success(f"Fetched {len(candles)} candles in "
                     f"{int(elapsed_total//60):02d}:{int(elapsed_total%60):02d} — {display_name}")
        return candles


# ============================================================================
# SECTION 13: INSTRUMENTS FETCHER (profit %, enabled status)
# ============================================================================
class InstrumentsFetcher:
    """Fetches the instruments list to get profit % and enabled status per asset.

    Sends 42["instruments/get"] and waits for the binary response.
    The MessageInterceptor captures the response and populates
    profit_by_asset and enabled_by_asset.
    """

    def __init__(self, client_holder: ClientHolder, interceptor: MessageInterceptor):
        self.client_holder = client_holder
        self.interceptor = interceptor

    async def fetch(self, timeout: float = 30.0) -> bool:
        """Send instruments/get request and wait for response."""
        client = self.client_holder.client
        if client is None or client.api is None:
            elog.error("No client for instruments fetch.")
            return False

        # Send the request multiple times (in case of silent drop)
        requests = ['42["instruments/get"]'] * 3
        for i, req in enumerate(requests, 1):
            try:
                client.api.send_websocket_request(req, no_force_send=False)
                elog.info(f"[instruments] sent request {i}/{len(requests)}")
            except Exception as e:
                elog.warn(f"[instruments] failed to send request {i}: {e}")
            if i < len(requests):
                await asyncio.sleep(1.5)

        # Wait for the binary response
        try:
            await asyncio.wait_for(
                self.interceptor.instruments_ready.wait(),
                timeout=timeout,
            )
            return True
        except asyncio.TimeoutError:
            elog.error(f"[instruments] timeout after {timeout}s — no response")
            return False

    def get_profit(self, asset: str) -> Optional[int]:
        return self.interceptor.get_profit(asset)

    def get_enabled(self, asset: str) -> Optional[bool]:
        return self.interceptor.get_enabled(asset)

    def print_summary(self, assets: List[str]):
        """Print a summary table of profit % and enabled status for the given assets.

        Shows MAX payout % (the real one) + history of recent values for debugging.
        """
        print()
        print(hr(95, '─', C2.DIM))
        print(f"  {paint_bold('📊 INSTRUMENTS SUMMARY', C2.BRIGHT_CYAN)}")
        print(hr(95, '─', C2.DIM))
        print(f"  {'Asset':<16} {'Max Profit':<14} {'Last':<6} {'History (recent)':<35} {'Status':<8} {'Live Price':<12}")
        print(hr(95, '─', C2.DIM))
        for asset in assets:
            max_profit = self.interceptor.get_profit(asset)
            last_profit = self.interceptor.get_last_profit(asset)
            history = self.interceptor.get_profit_history(asset)
            enabled = self.get_enabled(asset)
            live = self.interceptor.get_live_price(asset)

            # Color the profit based on value (high = green, low = red)
            if max_profit is not None:
                if max_profit >= 80:
                    profit_color = C2.BRIGHT_GREEN
                elif max_profit >= 60:
                    profit_color = C2.BRIGHT_YELLOW
                elif max_profit >= 30:
                    profit_color = C2.BRIGHT_RED
                else:
                    profit_color = C2.DIM
                profit_str = paint_bold(f"{max_profit}%", profit_color)
            else:
                profit_str = paint_dim("N/A")

            last_str = f"{last_profit}" if last_profit is not None else "—"
            # Show last 5 history values
            if history:
                history_str = ",".join(str(h) for h in history[-5:])
            else:
                history_str = "—"

            enabled_str = (paint_bold("OPEN", C2.BRIGHT_GREEN) if enabled
                           else paint_bold("CLOSED", C2.BRIGHT_RED) if enabled is False
                           else paint_dim("?"))
            live_str = paint_bold(f"{live:.5f}", C2.BRIGHT_CYAN) if live is not None else paint_dim("—")
            print(f"  {paint_bold(asset, C2.BRIGHT_YELLOW):<16} "
                  f"{profit_str:<14} "
                  f"{paint_dim(last_str):<6} "
                  f"{paint_dim(history_str):<35} "
                  f"{enabled_str:<8} "
                  f"{live_str:<12}")
        print(hr(95, '─', C2.DIM))
        print()


# ============================================================================
# SECTION 14: JSON SAVER
# ============================================================================
def save_candles_to_json(candles: List[Dict], asset: str, timeframe_min: int,
                          target_count: int, profit: Optional[int] = None) -> Optional[Path]:
    """Saves candles to candles_otc_data/{asset}_{tf}m_{count}c_{8-hex}.json"""
    if not candles:
        elog.warn("No candles to save.")
        return None

    def fmt_dt(ts: int) -> str:
        return datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d %H:%M:%S")

    random_suffix = ''.join(random.choices('0123456789abcdef', k=8))
    filename = f"{asset}_{timeframe_min}m_{target_count}c_{random_suffix}.json"
    filepath = CANDLES_DIR / filename

    meta = {
        "asset": asset,
        "timeframe_minutes": timeframe_min,
        "target_count": target_count,
        "actual_count": len(candles),
        "profit_percent": profit,
        "first_candle": fmt_dt(candles[0]['time']),
        "last_candle": fmt_dt(candles[-1]['time']),
        "first_candle_time": candles[0]['time'],
        "last_candle_time": candles[-1]['time'],
        "timezone": "UTC",
        "fetch_time": datetime.now().isoformat(timespec="seconds"),
        "fetch_timestamp": int(time.time()),
        "gap_filled_count": sum(1 for c in candles if c.get('volume', 1) == 0),
    }

    try:
        meta_txt = json.dumps(meta, indent=2, ensure_ascii=False).replace("\n", "\n  ")
        rows = []
        for c in candles:
            row = {
                "datetime": fmt_dt(c['time']),
                "time": c['time'],
                "open": c['open'],
                "high": c['high'],
                "low": c['low'],
                "close": c['close'],
                "volume": c.get('volume', 0),
            }
            rows.append("    " + json.dumps(row, ensure_ascii=False))
        body = ",\n".join(rows)

        with open(filepath, 'w', encoding='utf-8') as f:
            f.write('{\n')
            f.write(f'  "metadata": {meta_txt},\n')
            f.write('  "candles": [\n')
            f.write(body + '\n')
            f.write('  ]\n}\n')
        return filepath
    except Exception as e:
        log_exception("save_candles_to_json", e)
        return None


# ============================================================================
# SECTION 15: INTERACTIVE HELPERS
# ============================================================================
async def _ainput(prompt: str) -> str:
    return await asyncio.to_thread(input, prompt)


async def prompt_credentials() -> Optional[Tuple[str, str]]:
    creds = load_credentials()
    if creds:
        elog.info(f"Found saved credentials for: {creds['email']}")
        use_saved = (await _ainput(
            f"{paint(C2.BRIGHT_YELLOW, 'Use saved credentials? (Y/n): ')}"
        )).strip().lower()
        if use_saved in ('y', '', 'yes'):
            return creds['email'], creds['password']
    print(paint(C2.BRIGHT_CYAN, 'Enter your Quotex credentials:'))
    email = (await _ainput(f"{paint(C2.BRIGHT_YELLOW, 'Email: ')}")).strip()
    password = (await _ainput(f"{paint(C2.BRIGHT_YELLOW, 'Password: ')}")).strip()
    if not email or not password:
        return None
    return email, password


async def prompt_timeframe() -> Optional[int]:
    while True:
        try:
            raw = (await _ainput(
                f"{paint(C2.BRIGHT_YELLOW, 'Timeframe in minutes (1, 5, 15, 30, 60) [default: 1]: ')}"
            )).strip()
        except (EOFError, KeyboardInterrupt):
            return None
        if not raw:
            return TIMEFRAME_DEFAULT
        if raw.lower() in ('exit', 'quit', 'q'):
            return None
        try:
            tf = int(raw)
            if tf <= 0:
                elog.error("Timeframe must be positive.")
                continue
            return tf
        except ValueError:
            elog.error("Please enter a valid integer.")


# ============================================================================
# ============================================================================
# SECTION 15.5: GANN SIGNAL CALCULATOR
# ----------------------------------------------------------------------------
# يحتوي على:
#   - GANN_CONFIG: إعدادات الحاسبة (أرقام Gann + Fibonacci + المربعات)
#   - detect_swings: كاشف القمم والقيعان (fractal متعدد الطبقات)
#   - build_families: بناء عوائل إسقاطات Gann الزمنية
#   - confluence_at: حساب عدد التطابقات عند نقطة زمنية
#   - generate_signals_for_asset: مولّد الإشارات لكل أصل
#   - SignalsTable: مدير جدول الإشارات (CSV + عرض لوحي)
# ============================================================================
import csv
import math

GANN_CONFIG = {
    "lookback":          40,    # آخر 40 شمعة في التحليل
    "swing_strength":    2,     # قوة fractal
    "min_confluence":    3,     # أقل عدد تطابقات للإشارة
    "signal_gap":        4,     # أقل مسافة بين إشارتين
    "max_signals":       13,    # عدد الإشارات في الجدول
    "entry_lead_time":   60,    # عرض ⚡ قبل 60 ثانية من الدخول
    "output_csv":        "signals_table.csv",
}

# أرقام Gann الزمنية
GANN_NUMBERS = [7, 9, 12, 14, 21, 30, 45, 60, 90, 120, 144, 180, 270, 360]
FIBONACCI    = [13, 34, 55, 89, 233]
SQUARES      = [16, 25, 36, 49, 64, 81, 100, 121, 169, 196, 225]
RATIOS       = [0.382, 0.5, 0.618, 0.786, 1.0, 1.272, 1.618,
                2.0, 2.618, 3.0, 4.0]


def _swing_time_str(candle):
    """يُرجع HH:MM من شمعة بصيغة {time, datetime, ...}."""
    dt = candle.get("datetime")
    if isinstance(dt, str) and len(dt) >= 16:
        return dt[11:16]
    ts = candle.get("time", 0)
    if ts:
        try:
            return datetime.fromtimestamp(int(ts)).strftime("%H:%M")
        except Exception:
            pass
    return "?"


def detect_swings(candles, strength=GANN_CONFIG["swing_strength"]):
    """كشف القمم والقيعان بطريقة fractal متعدد الطبقات."""
    n = len(candles)
    if n < strength * 2 + 1:
        return []
    raw = []
    for i in range(strength, n - strength):
        c = candles[i]
        is_high = all(c["high"] > candles[i - k]["high"]
                      and c["high"] > candles[i + k]["high"]
                      for k in range(1, strength + 1))
        is_low = all(c["low"] < candles[i - k]["low"]
                     and c["low"] < candles[i + k]["low"]
                     for k in range(1, strength + 1))
        if is_high:
            raw.append({"i": i, "type": "H", "price": float(c["high"]),
                        "time_str": _swing_time_str(c),
                        "timestamp": int(c.get("time", 0))})
        if is_low:
            raw.append({"i": i, "type": "L", "price": float(c["low"]),
                        "time_str": _swing_time_str(c),
                        "timestamp": int(c.get("time", 0))})

    # دمج المتتالية من نفس النوع
    merged = []
    for s in raw:
        if not merged or merged[-1]["type"] != s["type"]:
            merged.append(s)
        elif (s["type"] == "H" and s["price"] > merged[-1]["price"]) or \
             (s["type"] == "L" and s["price"] < merged[-1]["price"]):
            merged[-1] = s
    return merged


def build_families(s1, s2):
    """يبني عوائل الإسقاطات الزمنية لزوج قمم/قيعان."""
    D = s2["i"] - s1["i"]
    families = []
    for p, label in [(s1, "first"), (s2, "last")]:
        base = p["i"]
        families.append(("Gann-" + label, set(base + g for g in GANN_NUMBERS)))
        families.append(("Fib-"  + label, set(base + f for f in FIBONACCI)))
        families.append(("Sq-"   + label, set(base + sq for sq in SQUARES)))
        families.append(("Rt-"   + label,
                         set(base + round(D * r) for r in RATIOS)))
        sd = math.sqrt(D)
        families.append(("Sq9-"  + label,
                         set(base + round((sd + k * 0.25) ** 2)
                             for k in range(1, 9))))
    return families


def confluence_at(families, target, tol=1):
    """يحسب عدد العوائل التي تحتوي target ضمن ±tol."""
    k = 0
    sources = []
    for name, indices in families:
        if any(abs(idx - target) <= tol for idx in indices):
            k += 1
            sources.append(name)
    return k, sources


def generate_signals_for_asset(candles, asset_name):
    """يولّد إشارات BUY/SELL متناوبة لكل زوج قمة/قاع."""
    n = len(candles)
    if n < 10:
        return []

    lookback = GANN_CONFIG["lookback"]
    work = candles[-lookback:] if n > lookback else candles
    offset = n - len(work) if n > lookback else 0

    swings = detect_swings(work, GANN_CONFIG["swing_strength"])
    for s in swings:
        s["i"] += offset

    if len(swings) < 2:
        return []

    candidates = []
    for j in range(len(swings) - 1):
        s1, s2 = swings[j], swings[j + 1]
        if s1["type"] == s2["type"]:
            continue
        D = s2["i"] - s1["i"]
        if D < 3:
            continue

        families = build_families(s1, s2)
        direction = 1 if s2["type"] == "L" else -1
        first_sig = "BUY" if direction == 1 else "SELL"
        pair_label = (f"{s1['time_str']}{'H' if s1['type']=='H' else 'L'}-"
                      f"{s2['time_str']}{'H' if s2['type']=='H' else 'L'}")

        for b in range(s2["i"] + 1, s2["i"] + 200):
            k, sources = confluence_at(families, b)
            if k >= GANN_CONFIG["min_confluence"]:
                zones_after = b - s2["i"]
                sig = first_sig if zones_after % 2 == 1 else (
                    "SELL" if first_sig == "BUY" else "BUY")
                candidates.append({
                    "asset": asset_name,
                    "entry_index": b,
                    "confluence": k,
                    "signal": sig,
                    "D": D,
                    "pair": pair_label,
                    "first_sig": first_sig,
                    "sources": sources,
                })

    # ترتيب وفلترة
    candidates.sort(key=lambda x: (-x["confluence"], x["entry_index"]))
    filtered = []
    gap = GANN_CONFIG["signal_gap"]
    for c in candidates:
        if all(abs(c["entry_index"] - f["entry_index"]) >= gap for f in filtered):
            filtered.append(c)

    # إعادة تعيين الاتجاهات بالتناوب لكل زوج
    by_pair = defaultdict(list)
    for z in filtered:
        by_pair[z["pair"]].append(z)
    for pair, items in by_pair.items():
        items.sort(key=lambda x: x["entry_index"])
        cur = items[0]["first_sig"]
        for z in items:
            z["signal"] = cur
            cur = "SELL" if cur == "BUY" else "BUY"
    return filtered


class SignalsTable:
    """مدير جدول الإشارات: يكتب CSV ويحفظ أحدث إشارة لكل أصل."""

    def __init__(self, max_signals=GANN_CONFIG["max_signals"],
                 csv_path=GANN_CONFIG["output_csv"]):
        self.max_signals = max_signals
        self.csv_path = csv_path
        self.current = []

    def update(self, all_signals):
        """يقبل قائمة كاملة من كل الأصول ويرتّبها حسب قرب الدخول."""
        all_signals.sort(key=lambda x: x.get("seconds_to_entry", 9999))
        self.current = all_signals[:self.max_signals]
        self._write_csv()
        return self.current

    def _write_csv(self):
        """يكتب الإشارات إلى ملف CSV بصيغة موحّدة."""
        try:
            with open(self.csv_path, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow([
                    "#", "Asset", "Entry Time", "Signal", "Direction",
                    "Confluence", "D", "Swing Pair", "Strength", "Status"
                ])
                for i, sig in enumerate(self.current, 1):
                    sig_type = sig["signal"]
                    strength = ("STRONG" if sig["confluence"] >= 5
                                else "GOOD" if sig["confluence"] >= 4
                                else "MEDIUM")
                    w.writerow([
                        i, sig["asset"],
                        sig.get("entry_time_str", "?"),
                        sig_type,
                        "CALL" if sig_type == "BUY" else "PUT",
                        sig["confluence"], sig["D"],
                        sig["pair"], strength,
                        sig.get("status", "WAITING"),
                    ])
        except Exception as e:
            elog.debug(f"[signals] CSV write failed: {e}")

    def print_inplace(self, num_rows=18):
        """يطبع جدول الإشارات في موقع ثابت (cursor up + clear line)."""
        CURSOR_UP = f"\033[{num_rows}A"
        CLEAR_LINE = "\033[2K"
        now_str = datetime.now().strftime("%H:%M:%S")
        sys.stdout.write(CURSOR_UP)
        sys.stdout.write(f"\r{CLEAR_LINE}  {paint_bold('GANN SIGNALS', C2.BRIGHT_MAGENTA)}"
                         f"  {paint_dim('— ' + now_str)}  "
                         f"{paint_dim('(' + str(len(self.current)) + '/' + str(self.max_signals) + ')')}\n")
        sys.stdout.write(f"{CLEAR_LINE}{'─' * 95}\n")
        sys.stdout.write(f"{CLEAR_LINE}  {'#':<3} {'Asset':<14} {'Entry':<7} {'Sig':<5} {'Dir':<5}"
                         f" {'conf':>4} {'D':>3} {'Strength':<8} {'Status':<14}\n")
        sys.stdout.write(f"{CLEAR_LINE}{'─' * 95}\n")
        if not self.current:
            sys.stdout.write(f"{CLEAR_LINE}  {paint_dim('No signals yet — waiting for candles...')}\n")
            for _ in range(self.max_signals - 1):
                sys.stdout.write(f"{CLEAR_LINE}\n")
        else:
            for i in range(1, self.max_signals + 1):
                if i <= len(self.current):
                    sig = self.current[i - 1]
                    sig_type = sig["signal"]
                    direction = "CALL" if sig_type == "BUY" else "PUT"
                    strength = ("STRONG" if sig["confluence"] >= 5
                                else "GOOD" if sig["confluence"] >= 4
                                else "MEDIUM")
                    s = sig.get("seconds_to_entry", 999)
                    if s <= GANN_CONFIG["entry_lead_time"]:
                        status = f"⚡ {s}s ENTER!"
                        marker = paint(C2.BRIGHT_YELLOW, "⚡")
                    elif s <= 300:
                        status = f"in {s // 60}m {s % 60}s"
                        marker = " "
                    else:
                        status = "waiting"
                        marker = " "
                    entry_str = sig.get("entry_time_str", "?")
                    sig_color = (C2.BRIGHT_GREEN if sig_type == "BUY"
                                 else C2.BRIGHT_RED)
                    sys.stdout.write(
                        f"{CLEAR_LINE}  {marker}{i:<3} "
                        f"{paint_bold(sig['asset'], C2.BRIGHT_YELLOW):<14} "
                        f"{entry_str:<7} "
                        f"{paint_bold(sig_type, sig_color):<5} "
                        f"{direction:<5} "
                        f"{sig['confluence']:>4} {sig['D']:>3} {strength:<8} "
                        f"{status:<14}\n"
                    )
                else:
                    sys.stdout.write(f"{CLEAR_LINE}\n")
        sys.stdout.write(f"{CLEAR_LINE}{'─' * 95}\n")
        sys.stdout.flush()


# ============================================================================
# LIVE CANDLE AGGREGATOR — يجمع ticks اللحظية في شموع M1
# ----------------------------------------------------------------------------
# عندما يصل سعر مباشر من WebSocket (quotes/stream) عبر interceptor،
# نحدّث الشمعة الحالية إن كانت في نفس الدقيقة، أو نبدأ شمعة جديدة.
# هذا يضمن أن latest_candles تبقى محدّثة بالبيانات اللحظية.
# ============================================================================
class LiveCandleAggregator:
    """يجمع ticks اللحظية في شموع M1 ويحدّث قائمة الشموع لكل أصل.

    الاستخدام:
        agg = LiveCandleAggregator(period_seconds=60)
        agg.update_from_price(asset, price, ts)  # تحدّث الشمعة الحالية
        candles = agg.merge_with_saved(asset, saved_candles)  # دمج مع المحفوظات
    """

    def __init__(self, period_seconds=60):
        self.period = period_seconds
        # asset -> current_minute_candle {time, open, high, low, close, volume}
        self.current: Dict[str, Dict] = {}
        # asset -> list of completed candles (in-memory buffer)
        self.buffer: Dict[str, List[Dict]] = defaultdict(list)
        # max buffer size per asset (keep last 200 candles)
        self.max_buffer = 200

    def _align(self, ts: int) -> int:
        """يحاذي timestamp مع بداية فترة الشمعة."""
        return (ts // self.period) * self.period

    def update_from_price(self, asset: str, price: float, ts: float):
        """يحدّث الشمعة الحالية للأصل بناءً على tick جديد.

        - إن كان ts داخل الشمعة الحالية: حدّث high/low/close
        - إن بدأت دقيقة جديدة: أغلق الشمعة الحالية وابدأ واحدة جديدة
        """
        if not asset or price <= 0:
            return
        ts_int = int(ts)
        bucket = self._align(ts_int)
        cur = self.current.get(asset)
        if cur is None:
            # أول tick لهذا الأصل
            self.current[asset] = {
                "time": bucket,
                "open": price, "high": price,
                "low": price, "close": price,
                "volume": 1,
            }
            return
        if bucket == cur["time"]:
            # نفس الدقيقة: حدّث OHLC
            if price > cur["high"]:
                cur["high"] = price
            if price < cur["low"]:
                cur["low"] = price
            cur["close"] = price
            cur["volume"] += 1
        elif bucket > cur["time"]:
            # دقيقة جديدة: أغلق القديمة، ابدأ الجديدة
            self.buffer[asset].append(cur)
            # احتفظ بآخر max_buffer شمعة فقط
            if len(self.buffer[asset]) > self.max_buffer:
                self.buffer[asset] = self.buffer[asset][-self.max_buffer:]
            self.current[asset] = {
                "time": bucket,
                "open": price, "high": price,
                "low": price, "close": price,
                "volume": 1,
            }
        # إذا bucket < cur["time"] (tick قديم) نتجاهله

    def merge_with_saved(self, asset: str, saved: List[Dict]) -> List[Dict]:
        """يدمج الشموع المحفوظة + الشموع المجمَّعة + الشمعة الحالية.

        الاستراتيجية:
          1. ابدأ بقائمة الشموع المحفوظة (إن وُجدت)
          2. أضف الشموع المجمَّعة في الـbuffer إن لم تكن موجودة
          3. أضف الشمعة الحالية (آخر دقيقة) إن لم تكن موجودة
          4. ترتيب + إزالة التكرارات حسب timestamp
          5. اقتصاص على آخر 200 شمعة
        """
        merged: Dict[int, Dict] = {}
        for c in (saved or []):
            if isinstance(c, dict):
                t = int(c.get("time", 0))
                if t > 0:
                    merged[t] = c
        # الشموع المجمَّعة
        for c in self.buffer.get(asset, []):
            t = int(c.get("time", 0))
            if t > 0:
                # الشمعة المجمَّعة لها أولوية على المحفوظة لأنها أحدث
                merged[t] = c
        # الشمعة الحالية
        cur = self.current.get(asset)
        if cur:
            t = int(cur.get("time", 0))
            if t > 0:
                merged[t] = cur
        # ترتيب + اقتصاص
        result = sorted(merged.values(), key=lambda x: x["time"])
        if len(result) > self.max_buffer:
            result = result[-self.max_buffer:]
        return result

    def get_latest(self, asset: str, saved: List[Dict]) -> List[Dict]:
        """alias لـ merge_with_saved — يُرجع أحدث قائمة شموع."""
        return self.merge_with_saved(asset, saved)

    def current_price(self, asset: str) -> Optional[float]:
        """يُرجع سعر الإغلاق الحالي للأصل."""
        c = self.current.get(asset)
        return c["close"] if c else None


def swing_signature(swings: List[Dict]) -> str:
    """يبني بصمة فريدة لآخر القمم/القيعان.

    تستخدم لاكتشاف تكوّن قمة/قاع جديد: نقارن البصمة قبل وبعد التحديث.
    إن اختلفت → قمة/قاع جديد → إعادة توليد الإشارات فوراً.

    البصمة: آخر 3 swings بصيغة "i:type:price|..."
    """
    if not swings:
        return ""
    # خذ آخر 3 swings فقط (يكتفي لاكتشاف أي تغيير في النمط الأخير)
    last = swings[-3:]
    return "|".join(f"{s['i']}:{s['type']}:{s['price']:.5f}" for s in last)


def detect_new_swings(prev_sigs: Dict[str, str],
                       latest_candles: Dict[str, List[Dict]]
                       ) -> List[str]:
    """يكشف الأصول التي تكوّنت لديها قمة/قاع جديد.

    المعاملات:
      prev_sigs      : {asset: signature} من الاستدعاء السابق
      latest_candles : {asset: candles} الحالي

    يُرجع:
      قائمة بأسماء الأصول التي تغيّرت بصمتها (قمة/قاع جديد)
    """
    changed = []
    for asset, candles in latest_candles.items():
        if not candles or len(candles) < 10:
            continue
        try:
            swings = detect_swings(candles, GANN_CONFIG["swing_strength"])
            sig = swing_signature(swings)
            prev = prev_sigs.get(asset, "")
            if sig != prev:
                changed.append(asset)
                prev_sigs[asset] = sig
        except Exception:
            pass
    return changed


# ============================================================================

# ============================================================================
# TERMINAL CAPABILITY DETECTION + CSV VIEWER
# ----------------------------------------------------------------------------
# - supports_ansi_cursor(): يكشف إذا كانت الطرفية تدعم ANSI escape codes
#   (cursor up, clear line) — يعمل في Linux/Mac و Windows Terminal
#   لكنه لا يعمل في Git Bash (MINGW64) أو CMD التقليدي
# - clear_screen(): يمسح الشاشة بطريقة متوافقة مع كل الطرفيات
# - open_csv_in_viewer(): يفتح ملف CSV بالبرنامج الافتراضي (Excel/LibreOffice)
# ============================================================================
import subprocess as _sp
import shlex as _shlex


def supports_ansi_cursor() -> bool:
    """يكشف إذا كانت الطرفية تدعم ANSI cursor control.

    يعتمد على:
      1. متغير البيئة TERM (Linux/Mac)
      2. WT_SESSION (Windows Terminal)
      3. ConEmuPID (ConEmu/Cmder)
      4. ANSICON (ANSI shim قديم)
      5. على Windows 10+ مع git bash، نعطل cursor control (مشاكل معروفة)
    """
    # 1) ANSICON مثبّت → يدعم ANSI بالتأكيد
    if os.environ.get("ANSICON"):
        return True
    # 2) Windows Terminal → يدعم ANSI
    if os.environ.get("WT_SESSION"):
        return True
    # 3) ConEmu/Cmder → يدعم ANSI
    if os.environ.get("ConEmuANSI") == "ON":
        return True
    # 4) على Linux/Mac، تحقق من TERM
    if sys.platform.startswith(("linux", "darwin")):
        term = os.environ.get("TERM", "")
        if term and term != "dumb":
            return True
    # 5) على Windows، تحقق من Terminal PID
    if sys.platform == "win32":
        # Git Bash (MINGW64/MSYS) → TERM=xterm لكن cursor control لا يعمل موثوقاً
        msystem = os.environ.get("MSYSTEM", "")
        if msystem:  # نحن في Git Bash
            return False
        # PowerShell/CMD على Windows 10+ → يدعم ANSI افتراضياً
        try:
            import ctypes
            kernel32 = ctypes.windll.kernel32
            # ENABLE_VIRTUAL_TERMINAL_PROCESSING = 0x0004
            kernel32.SetConsoleMode(kernel32.GetStdHandle(-11), 7)
            return True
        except Exception:
            return False
    return False


def clear_screen() -> None:
    """يمسح الشاشة بطريقة متوافقة مع كل الطرفيات."""
    if sys.platform == "win32":
        # cls يعمل في كل طرفيات Windows
        try:
            os.system("cls")
            return
        except Exception:
            pass
    # على Linux/Mac: ANSI clear screen
    sys.stdout.write("\033[2J\033[H")
    sys.stdout.flush()


def open_csv_in_viewer(csv_path: str) -> bool:
    """يفتح ملف CSV بالبرنامج الافتراضي (Excel/LibreOffice/Numbers).

    يحاول:
      - Windows: os.startfile (يستخدم اقتران الملفات)
      - Linux: xdg-open
      - Mac: open
    """
    try:
        path = os.path.abspath(csv_path)
        if not os.path.exists(path):
            return False
        if sys.platform == "win32":
            os.startfile(path)  # type: ignore
        elif sys.platform == "darwin":
            _sp.Popen(["open", path], stdout=_sp.DEVNULL, stderr=_sp.DEVNULL)
        else:
            _sp.Popen(["xdg-open", path], stdout=_sp.DEVNULL, stderr=_sp.DEVNULL)
        return True
    except Exception as e:
        elog.debug(f"[csv-viewer] failed to open: {e}")
        return False


# ============================================================================
# SECTION 16: MAIN ASYNC ENTRY POINT
# ============================================================================
async def main_async():
    print_banner()
    purge_old_session()

    # Credentials
    creds = await prompt_credentials()
    if creds is None:
        elog.error("Invalid credentials.")
        return
    email, password = creds

    # Connect
    elog.info("Connecting to Quotex...")
    spinner = Spinner("Connecting to Quotex...")
    spinner.start()
    client = await connect_quotex(email, password, max_attempts=3)
    if client is None:
        spinner.stop("Connection failed after multiple attempts.", success=False)
        return
    spinner.stop("Connected successfully.")
    save_credentials(email, password)
    elog.success("Credentials saved.")

    # Wrap in ClientHolder
    holder = ClientHolder(client, email, password)

    # Install message interceptor
    interceptor = MessageInterceptor(client)
    if not interceptor.install():
        elog.error("Failed to install message interceptor.")
        return

    # Start never-sleep engine
    engine = NeverSleepEngine(holder, interceptor)
    engine.start()

    # Wait briefly for the WebSocket to settle
    await asyncio.sleep(1.5)

    # The 13 OTC pairs are hardcoded in OTC_ASSETS — no need to fetch the
    # instruments list. The MessageInterceptor will still CAPTURE profit %
    # automatically if the server pushes it (via keepalive's periodic
    # 42["instruments/get"] request), but we don't block on it.

    # Subscribe to live prices for all OTC pairs (the 13 hardcoded assets)
    live_sub = LivePriceSubscriber(interceptor)
    live_sub.subscribe_all(OTC_ASSETS, period=60)
    elog.success(f"Subscribed to live prices for {len(OTC_ASSETS)} OTC pairs")

    # Wait briefly for live prices to arrive (no payout data needed before fetching)
    elog.info(f"Listening for live prices (5s)...")
    deadline = time.time() + 5.0
    while time.time() < deadline:
        n_live = len(interceptor.live_prices)
        if n_live >= 10:
            elog.success(f"Got {n_live} live prices — starting fetch.")
            break
        await asyncio.sleep(0.5)

    n_live = len(interceptor.live_prices)
    elog.info(f"Collected: {n_live} live prices")
    if n_live == 0:
        elog.warn("No live prices received. Market may be closed or subscription failed.")

    # NOTE: We do NOT print the instruments summary here anymore.
    # The user requested that payout % fetching be removed from the candle
    # fetch phase to speed it up. Payout data is still being collected in
    # the background (interceptor captures depth/change frames automatically)
    # and can be queried later if needed.

    # Ask for timeframe
    timeframe = await prompt_timeframe()
    if timeframe is None:
        # Cleanup — unsubscribe_all is SYNC, not async
        try:
            live_sub.unsubscribe_all()
        except Exception:
            pass
        try:
            await engine.stop()
        except Exception:
            pass
        try:
            await client.close()
        except Exception:
            pass
        return

    # Fetch candles for all 13 OTC pairs
    elog.info(f"Fetching {TARGET_CANDLE_COUNT} candles for each of {len(OTC_ASSETS)} OTC pairs (M{timeframe})...")
    fetcher = CandleFetcher(holder, interceptor)

    print(f"\n{paint_bold('  Starting batch fetch...', C2.BRIGHT_CYAN)}")
    print(hr(70, '═', C2.BRIGHT_BLUE))

    successes = 0
    failures = []
    try:
        for idx, asset in enumerate(OTC_ASSETS, 1):
            print(f"\n{paint_bold(f'  [{idx}/{len(OTC_ASSETS)}] {asset}', C2.BRIGHT_CYAN)}")
            print(hr(70, '─', C2.DIM))

            # Show only live price before fetch (no payout — user requested removing it)
            live_price = interceptor.get_live_price(asset)
            ticks_seen = interceptor.live_ticks_seen.get(asset, 0)
            if live_price is not None:
                price_str = paint_bold(f"{live_price}", C2.BRIGHT_GREEN)
                ticks_str = paint_dim(f"({ticks_seen} ticks)")
                print(f"  {paint('●', C2.BRIGHT_GREEN)} Live price: {price_str} {ticks_str}")
            else:
                print(f"  {paint('○', C2.BRIGHT_YELLOW)} No live ticks — market may be closed")

            try:
                candles = await fetcher.fetch_exactly_n(asset, timeframe, TARGET_CANDLE_COUNT)
            except Exception as e:
                log_exception(f"fetch_{asset}", e)
                candles = []

            if candles:
                profit = interceptor.get_profit(asset)
                fp = save_candles_to_json(candles, asset, timeframe, TARGET_CANDLE_COUNT, profit)
                if fp:
                    # Print FULL absolute path so the user can find the file
                    abs_path = fp.resolve()
                    elog.success(f"Saved {len(candles)} candles → {abs_path}")
                    successes += 1
                else:
                    failures.append(asset)
            else:
                failures.append(asset)

        # Final summary
        print(f"\n{hr(70, '═', C2.BRIGHT_BLUE)}")
        print(f"  {paint_bold('BATCH COMPLETE', C2.BRIGHT_WHITE)}")
        print(hr(70, '═', C2.BRIGHT_BLUE))
        print(f"  Successful: {paint_bold(f'{successes}/{len(OTC_ASSETS)}', C2.BRIGHT_GREEN)}")
        if failures:
            print(f"  Failed:     {paint_bold(f'{len(failures)}', C2.BRIGHT_RED)} — {', '.join(failures)}")
        print(f"  Output dir: {paint(str(CANDLES_DIR.absolute()), C2.BRIGHT_YELLOW)}")
        print(hr(70, '═', C2.BRIGHT_BLUE))

        # ============================================================
        # GANN SIGNALS — تحميل الشموع المحفوظة + إعداد جدول الإشارات
        # ============================================================
        # بعد اكتمال BATCH COMPLETE، نقرأ جميع ملفات JSON المحفوظة في
        # candles_otc_data/ ونحمّلها في الذاكرة، ثم ننشئ SignalsTable
        # الذي سيتولى عرض الإشارات وتحديث ملف signals_table.csv.
        latest_candles = {}  # asset -> List[Dict]  (آخر شموع محفوظة)
        try:
            candle_files = sorted(CANDLES_DIR.glob(f"*_1m_{TARGET_CANDLE_COUNT}c_*.json"))
            # خذ آخر ملف لكل أصل (الأحدث تعديلاً)
            by_asset = {}
            for fp in candle_files:
                # اسم الملف: {asset}_{tf}m_{count}c_{hex}.json
                name = fp.stem
                parts = name.split("_")
                if len(parts) >= 2:
                    asset_key = "_".join(parts[:-3]) if len(parts) > 3 else parts[0]
                    # اصنع مفتاح الأصل الصحيح: نمط مثل EURUSD_otc
                    # نبحث عن _otc في الأجزاء
                    asset_name = None
                    for i, p in enumerate(parts):
                        if p == "otc" and i > 0:
                            asset_name = "_".join(parts[:i+1])
                            break
                    if not asset_name:
                        asset_name = parts[0]
                    by_asset[asset_name] = fp  # آخر ملف (مرتب حسب mtime)
            elog.info(f"[signals] loading {len(by_asset)} candle files...")
            for asset, fp in by_asset.items():
                try:
                    data = json.loads(fp.read_text(encoding="utf-8"))
                    candles = data.get("candles", [])
                    if candles:
                        latest_candles[asset] = candles
                except Exception as e:
                    elog.debug(f"[signals] failed to load {fp.name}: {e}")
            elog.success(f"[signals] loaded candles for {len(latest_candles)} assets")
        except Exception as e:
            elog.warn(f"[signals] failed to scan candle files: {e}")

        # إنشاء جدول الإشارات
        signals_table = SignalsTable()
        elog.success(f"[signals] SignalsTable ready — output: {GANN_CONFIG['output_csv']}")

        # إنشاء مدير الشموع اللحظي — يجمع ticks من WebSocket
        # ليُحدّث latest_candles تلقائياً عند وصول أسعار جديدة
        live_agg = LiveCandleAggregator(period_seconds=timeframe * 60)
        elog.success(f"[signals] LiveCandleAggregator ready (period={timeframe * 60}s)")

        # تتبع بصمات القمم/القيعان لكل أصل — لاكتشاف تكوّن swing جديد
        prev_swing_sigs: Dict[str, str] = {}
        # تتبع آخر مرة حدّثنا فيها latest_candles من الـ aggregator
        last_candles_refresh_time = 0.0
        candles_refresh_interval = 1.0   # حدّث كل 1 ثانية (سريع)

        # إنشاء مولّد إشارات مرة واحدة لكل أصل وتحديثه دورياً
        last_signals_gen_time = 0.0
        signals_gen_interval = 30.0   # إعادة توليد دوري كل 30 ثانية
        # العدّاد: كم مرة تم اكتشاف swing جديد
        swing_changes_count = 0

        # Print engine stats
        s = engine.stats()
        uptime = int(s['uptime_seconds'])
        print(f"\n  {paint_bold('Engine stats:', C2.BRIGHT_CYAN)}")
        print(f"    Uptime:        {int(uptime//3600):02d}:{int((uptime%3600)//60):02d}:{int(uptime%60):02d}")
        print(f"    Connection:    {paint_bold('ALIVE', C2.BRIGHT_GREEN) if s['connection_alive'] else paint_bold('DEAD', C2.BRIGHT_RED)}")
        print(f"    Drops:         {s['connection_drops']}")
        if s.get('last_drop_ago'):
            print(f"    Last drop:     {int(s['last_drop_ago'])}s ago")
        if s.get('last_ping_ago'):
            print(f"    Last ping:     {int(s['last_ping_ago'])}s ago")
        print(f"    Last message:  {int(s['last_message_ago'])}s ago")

        # ============================================================
        # LIVE PRICE LOOP — never sleeps until user stops (Ctrl+C)
        # ============================================================
        # The user requested that the program continues running and shows
        # live prices for all 13 OTC pairs after BATCH COMPLETE.
        # This loop:
        #   1. Refreshes payouts every 5 seconds (force-refresh)
        #   2. Re-subscribes to live prices every 10 seconds (keep alive)
        #   3. Displays the instruments summary table every 2 seconds
        #   4. Stops ONLY when the user presses Ctrl+C
        #
        # The interceptor's _fill_missing_slots (ported from wedsoket_.py)
        # is applied to the LIVE prices: if a price for an asset is missing
        # (no tick received), the previous price is carried forward.
        # ============================================================
        # LIVE PRICE MONITOR — in-place updates (no scrolling)
        # ============================================================
        # Table layout:
        #   Row 1: 📊 LIVE PRICES — HH:MM:SS
        #   Row 2: ───
        #   Row 3: Asset | Profit | Live Price | Δ | Ticks
        #   Row 4: ───
        #   Rows 5..17: 13 asset rows
        #   Row 18: ───
        # Total = 4 (header) + 13 (assets) + 1 (footer) = 18 rows
        # ============================================================
        # COMBINED MONITOR: LIVE PRICES + GANN SIGNALS (in-place updates)
        # ============================================================
        # Table layout (top to bottom):
        #   Block 1: LIVE PRICES  (4 header + 13 assets + 1 footer = 18 rows)
        #   Block 2: blank spacer (1 row)
        #   Block 3: GANN SIGNALS (4 header + 13 rows + 1 footer = 18 rows)
        # Total = 37 rows
        LIVE_ROWS = len(OTC_ASSETS) + 5      # 4 header + 13 assets + 1 footer = 18
        SIGNAL_ROWS = GANN_CONFIG["max_signals"] + 5  # 4 header + 13 + 1 footer = 18
        TOTAL_ROWS = LIVE_ROWS + 1 + SIGNAL_ROWS  # 37

        print(f"\n{hr(95, '=', C2.BRIGHT_GREEN)}")
        print(f"  {paint_bold('LIVE PRICE MONITOR + GANN SIGNALS', C2.BRIGHT_GREEN)} — press Ctrl+C to stop")
        print(hr(95, '=', C2.BRIGHT_GREEN))
        print(f"  {paint_dim('Live prices every 0.5s · Signals refreshed every 30s · CSV: ' + GANN_CONFIG['output_csv'])}")
        print()
        # طباعة أسطر فارغة لمحاذاة مؤشر الكتابة (سيتم استبدالها بالجدول)
        for _ in range(TOTAL_ROWS):
            print()
        # تحريك المؤشر للأعلى مرة واحدة ليصبح قبل أول سطر فارغ
        sys.stdout.write(f"\033[{TOTAL_ROWS}A")
        sys.stdout.flush()

        prev_prices = {}
        last_refresh_time = 0.0
        last_resubscribe_time = 0.0
        last_instruments_time = 0.0
        last_render_time = 0.0          # آخر مرة طبعنا الجدول على الشاشة
        refresh_interval = 10.0
        resubscribe_interval = 30.0
        instruments_interval = 15.0
        render_interval = 2.0           # إعادة رسم الشاشة كل 2 ثانية

        # كشف دعم الطرفية لـ ANSI cursor control مرة واحدة عند البدء
        USE_CLEAR_SCREEN = not supports_ansi_cursor()
        elog.info(f"[terminal] ANSI cursor support: {not USE_CLEAR_SCREEN} → "
                  f"mode: {'clear-screen' if USE_CLEAR_SCREEN else 'in-place'}")

        # فتح ملف CSV تلقائياً مع برنامج العرض الافتراضي (Excel/LibreOffice)
        try:
            if open_csv_in_viewer(GANN_CONFIG["output_csv"]):
                elog.success(f"[csv] opened {GANN_CONFIG['output_csv']} in default viewer")
            else:
                elog.warn(f"[csv] could not auto-open viewer — open manually: {GANN_CONFIG['output_csv']}")
        except Exception as e:
            elog.debug(f"[csv] auto-open failed: {e}")

        def render_live_table():
            """يطبع جدول الأسعار المباشرة (clear-screen mode أو in-place)."""
            now_str = datetime.now().strftime("%H:%M:%S")
            if USE_CLEAR_SCREEN:
                # وضع مسح الشاشة: اطبع الجدول بدون cursor up
                CLEAR_LINE = ""  # لا حاجة لمسح السطر
                sys.stdout.write(f"\r  {paint_bold('LIVE PRICES', C2.BRIGHT_CYAN)}  {paint_dim('— ' + now_str)}\n")
                sys.stdout.write(f"{'─' * 95}\n")
                sys.stdout.write(f"  {'Asset':<16} {'Profit':<10} {'Live Price':<16} {'Δ':<16} {'Ticks':<8}\n")
                sys.stdout.write(f"{'─' * 95}\n")
            else:
                # وضع in-place: استخدم cursor up (Linux/Mac/Windows Terminal)
                CURSOR_UP_LIVE = f"\033[{LIVE_ROWS}A"
                CLEAR_LINE = "\033[2K"
                sys.stdout.write(CURSOR_UP_LIVE)
                sys.stdout.write(f"\r{CLEAR_LINE}  {paint_bold('LIVE PRICES', C2.BRIGHT_CYAN)}  {paint_dim('— ' + now_str)}\n")
                sys.stdout.write(f"{CLEAR_LINE}{'─' * 95}\n")
                sys.stdout.write(f"{CLEAR_LINE}  {'Asset':<16} {'Profit':<10} {'Live Price':<16} {'Δ':<16} {'Ticks':<8}\n")
                sys.stdout.write(f"{CLEAR_LINE}{'─' * 95}\n")
            for asset in OTC_ASSETS:
                profit = interceptor.get_profit(asset)
                live = interceptor.get_live_price(asset)
                ticks = interceptor.live_ticks_seen.get(asset, 0)
                if live is None and asset in prev_prices:
                    live = prev_prices[asset]
                if profit is not None:
                    if profit >= 80: profit_color = C2.BRIGHT_GREEN
                    elif profit >= 70: profit_color = C2.BRIGHT_YELLOW
                    elif profit >= 50: profit_color = C2.BRIGHT_RED
                    else: profit_color = C2.DIM
                    profit_str = paint_bold(f"{profit}%", profit_color)
                else:
                    profit_str = paint_dim("N/A")
                if live is not None:
                    live_str = paint_bold(f"{live:.5f}", C2.BRIGHT_CYAN)
                    prev = prev_prices.get(asset)
                    if prev is not None:
                        delta = live - prev
                        if delta > 0: delta_str = paint(C2.BRIGHT_GREEN, f"▲ {delta:+.5f}")
                        elif delta < 0: delta_str = paint(C2.BRIGHT_RED, f"▼ {delta:+.5f}")
                        else: delta_str = paint_dim("= 0.00000")
                    else:
                        delta_str = paint_dim("—")
                    prev_prices[asset] = live
                else:
                    live_str = paint_dim("—")
                    delta_str = paint_dim("—")
                ticks_str = paint_dim(f"{ticks}")
                sys.stdout.write(f"{CLEAR_LINE}  {paint_bold(asset, C2.BRIGHT_YELLOW):<16} {profit_str:<10} {live_str:<16} {delta_str:<16} {ticks_str:<8}\n")
            sys.stdout.write(f"{CLEAR_LINE}{'─' * 95}\n")
            sys.stdout.flush()

        def render_signals_block():
            """يطبع جدول الإشارات (clear-screen mode أو in-place)."""
            if USE_CLEAR_SCREEN:
                # وضع مسح الشاشة: اطبع الجدول مباشرة بدون cursor up
                now_str = datetime.now().strftime("%H:%M:%S")
                sys.stdout.write(f"  {paint_bold('GANN SIGNALS', C2.BRIGHT_MAGENTA)}"
                                 f"  {paint_dim('— ' + now_str)}  "
                                 f"{paint_dim('(' + str(len(signals_table.current)) + '/' + str(signals_table.max_signals) + ')')}\n")
                sys.stdout.write(f"{'─' * 95}\n")
                sys.stdout.write(f"  {'#':<3} {'Asset':<14} {'Entry':<7} {'Sig':<5} {'Dir':<5}"
                                 f" {'conf':>4} {'D':>3} {'Strength':<8} {'Status':<14}\n")
                sys.stdout.write(f"{'─' * 95}\n")
                if not signals_table.current:
                    sys.stdout.write(f"  {paint_dim('No signals yet — waiting for candles...')}\n")
                else:
                    for i in range(1, signals_table.max_signals + 1):
                        if i <= len(signals_table.current):
                            sig = signals_table.current[i - 1]
                            sig_type = sig["signal"]
                            direction = "CALL" if sig_type == "BUY" else "PUT"
                            strength = ("STRONG" if sig["confluence"] >= 5
                                        else "GOOD" if sig["confluence"] >= 4
                                        else "MEDIUM")
                            s = sig.get("seconds_to_entry", 999)
                            if s <= GANN_CONFIG["entry_lead_time"]:
                                status = f"⚡ {s}s ENTER!"
                                marker = paint(C2.BRIGHT_YELLOW, "⚡")
                            elif s <= 300:
                                status = f"in {s // 60}m {s % 60}s"
                                marker = " "
                            else:
                                status = "waiting"
                                marker = " "
                            entry_str = sig.get("entry_time_str", "?")
                            sig_color = (C2.BRIGHT_GREEN if sig_type == "BUY"
                                         else C2.BRIGHT_RED)
                            sys.stdout.write(
                                f"  {marker}{i:<3} "
                                f"{paint_bold(sig['asset'], C2.BRIGHT_YELLOW):<14} "
                                f"{entry_str:<7} "
                                f"{paint_bold(sig_type, sig_color):<5} "
                                f"{direction:<5} "
                                f"{sig['confluence']:>4} {sig['D']:>3} {strength:<8} "
                                f"{status:<14}\n"
                            )
                sys.stdout.write(f"{'─' * 95}\n")
                sys.stdout.flush()
            else:
                # وضع in-place: استخدم cursor up
                signals_table.print_inplace(num_rows=SIGNAL_ROWS)

        def update_live_candles():
            """يجمع آخر ticks من interceptor ويحدّث latest_candles لكل أصل."""
            changed_assets = []
            for asset in OTC_ASSETS:
                price = interceptor.get_live_price(asset)
                if price is None:
                    continue
                ts_now = time.time()
                # تحدّث aggregator بهذا الـ tick
                live_agg.update_from_price(asset, price, ts_now)
                # ادمج مع المحفوظات لإنتاج قائمة شموع محدّثة
                saved = latest_candles.get(asset, [])
                merged = live_agg.merge_with_saved(asset, saved)
                if merged and len(merged) > len(saved):
                    latest_candles[asset] = merged
                    changed_assets.append(asset)
                elif merged:
                    # حتى لو لم يزد العدد، السعر الحالي قد تغيّر
                    latest_candles[asset] = merged
                    changed_assets.append(asset)
            return changed_assets

        def regenerate_signals():
            """يولّد الإشارات من أحدث شموع متاحة ويحدّث signals_table."""
            all_signals = []
            now_ts = int(time.time())
            for asset, candles in latest_candles.items():
                if not candles or len(candles) < 10:
                    continue
                try:
                    sigs = generate_signals_for_asset(candles, asset)
                except Exception as e:
                    elog.debug(f"[signals] gen failed for {asset}: {e}")
                    continue
                n = len(candles)
                for sig in sigs:
                    entry_offset = sig["entry_index"] - (n - 1)
                    if entry_offset < 0:
                        continue  # إشارة قديمة، تخطّي
                    # تقدير وقت الدخول بناءً على آخر شمعة
                    last_ts = int(candles[-1].get("time", 0))
                    if last_ts > 0:
                        entry_ts = last_ts + entry_offset * (timeframe * 60)
                        sig["entry_timestamp"] = entry_ts
                        try:
                            sig["entry_time_str"] = datetime.fromtimestamp(entry_ts).strftime("%H:%M")
                        except Exception:
                            sig["entry_time_str"] = f"+{entry_offset}m"
                        sig["seconds_to_entry"] = entry_ts - now_ts
                    else:
                        sig["entry_time_str"] = f"+{entry_offset}m"
                        sig["seconds_to_entry"] = 999
                    s = sig["seconds_to_entry"]
                    if s <= GANN_CONFIG["entry_lead_time"]:
                        sig["status"] = "ENTER NOW"
                    elif s <= 300:
                        sig["status"] = f"in {s // 60}m {s % 60}s"
                    else:
                        sig["status"] = "WAITING"
                    all_signals.append(sig)
            signals_table.update(all_signals)

        # توليد الإشارات لأول مرة فوراً
        try:
            regenerate_signals()
            elog.success(f"[signals] initial generation: {len(signals_table.current)} signals")
        except Exception as e:
            elog.warn(f"[signals] initial generation failed: {e}")

        def render_combined():
            """يطبع كلا الجدولين (الأسعار + الإشارات).

            - في وضع clear-screen: نمسح الشاشة ثم نطبع الجدولين معاً
            - في وضع in-place: نستخدم cursor up (Linux/Mac/Windows Terminal)
            """
            if USE_CLEAR_SCREEN:
                # امسح الشاشة بالكامل ثم اطبع الجدولين
                clear_screen()
                # عنوان رئيسي
                sys.stdout.write(f"  {paint_bold('QUOTEX MEGA + GANN MONITOR', C2.BRIGHT_GREEN)}"
                                 f"  {paint_dim('— ' + datetime.now().strftime('%H:%M:%S'))}\n")
                sys.stdout.write(f"  {paint_dim('CSV: ' + GANN_CONFIG['output_csv'] + '  ·  Ctrl+C to stop')}\n")
                sys.stdout.write(f"{'=' * 95}\n")
                # 1) جدول الأسعار
                render_live_table()
                # 2) سطر فاصل
                sys.stdout.write("\n")
                # 3) جدول الإشارات
                render_signals_block()
                sys.stdout.flush()
            else:
                # وضع in-place: استخدم cursor up على الجدولين معاً
                render_live_table()
                sys.stdout.write("\033[2K\n")
                signals_table.print_inplace(num_rows=SIGNAL_ROWS)

        # في وضع clear-screen: لا نحتاج لطباعة أسطر فارغة مسبقاً
        if not USE_CLEAR_SCREEN:
            # طباعة أسطر فارغة لمحاذاة مؤشر الكتابة (في وضع in-place فقط)
            for _ in range(TOTAL_ROWS):
                print()
            sys.stdout.write(f"\033[{TOTAL_ROWS}A")
            sys.stdout.flush()

        render_combined()

        try:
            while True:
                now = time.time()

                # 1) تحديث الشموع بالـticks اللحظية (كل 0.5 ثانية)
                try:
                    update_live_candles()
                except Exception as e:
                    elog.debug(f"[signals] update_live_candles failed: {e}")

                # 2) كشف تكوّن قمة/قاع جديد كل ثانية
                #    إن اكتشفنا swing جديد → إعادة توليد فوري
                should_regenerate = False
                if now - last_candles_refresh_time >= candles_refresh_interval:
                    last_candles_refresh_time = now
                    try:
                        changed = detect_new_swings(prev_swing_sigs, latest_candles)
                        if changed:
                            swing_changes_count += 1
                            should_regenerate = True
                            elog.success(
                                f"[signals] ⚡ NEW swing detected for "
                                f"{len(changed)} asset(s): "
                                f"{', '.join(changed[:3])}"
                                f"{'...' if len(changed) > 3 else ''} — "
                                f"regenerating signals immediately "
                                f"(#{swing_changes_count})"
                            )
                    except Exception as e:
                        elog.debug(f"[signals] swing detection failed: {e}")

                # 3) إعادة توليد دوري كل 30 ثانية
                if now - last_signals_gen_time >= signals_gen_interval:
                    should_regenerate = True

                # 4) تنفيذ إعادة التوليد إن لزم (فوري عند swing جديد أو دوري)
                if should_regenerate:
                    try:
                        regenerate_signals()
                        last_signals_gen_time = now
                    except Exception as e:
                        elog.debug(f"[signals] regenerate failed: {e}")

                # 5) إعادة طلب الأسعار المباشرة + payouts
                if now - last_refresh_time >= refresh_interval:
                    try: live_sub.refresh_payouts(OTC_ASSETS)
                    except: pass
                    last_refresh_time = now
                if now - last_instruments_time >= instruments_interval:
                    try:
                        api = client.api
                        api.send_websocket_request('42["instruments/get"]', no_force_send=False)
                    except: pass
                    last_instruments_time = now
                if now - last_resubscribe_time >= resubscribe_interval:
                    try:
                        for asset in OTC_ASSETS:
                            live_sub.subscribe(asset, period=60)
                    except: pass
                    last_resubscribe_time = now

                # 6) عرض الجدولين كل 2 ثانية (تقليل الوميض)
                #    ملف CSV يُحدّث فورياً عند كل swing جديد، لكن عرض
                #    الشاشة يُحدّث كل 2 ثانية لتجنب الوميض والتنقل السريع
                if now - last_render_time >= render_interval:
                    render_combined()
                    last_render_time = now
                await asyncio.sleep(0.5)

        except (KeyboardInterrupt, asyncio.CancelledError):
            print(f"\n{paint(C2.BRIGHT_YELLOW, 'Stopping live monitor...')}")


    finally:
        # Cleanup
        # unsubscribe_all() is SYNC (not async), so no await
        try:
            live_sub.unsubscribe_all()
        except Exception:
            pass
        # engine.stop() is async
        try:
            await engine.stop()
        except Exception:
            pass
        interceptor.restore()
        try:
            await client.close()
        except Exception:
            pass
        print(f"\n{paint(C2.BRIGHT_CYAN, 'Done.')}")


# ============================================================================
# SECTION 17: MAIN ENTRY POINT
# ============================================================================
def main():
    try:
        asyncio.run(main_async())
    except KeyboardInterrupt:
        print(f"\n{paint(C2.BRIGHT_YELLOW, 'Stopped.')}")
    except Exception as e:
        log_exception("main", e)
        traceback.print_exc()


if __name__ == "__main__":
    main()