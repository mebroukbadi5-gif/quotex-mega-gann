#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BADICHARTS — Telegram Signal Bot (FULL integration)
====================================================

A single-file Python bot that combines:
  1. The complete Quotex Mega Fetcher engine (connection, instruments,
     candle fetcher, never-sleep watchdog) — embedded verbatim.
  2. The complete BADICHARTS engine (12 strategies x 8 filters x 3 MTF modes,
     plus 6 ZENITH variants for MAX mode) that decides BUY/SELL from real
     candles.
  3. A Telegram bot with inline buttons (3 strategy + 13 pair + STOP),
     plain emoji captions, and a 1600x900 neon-style chart renderer.

USAGE
-----
  1) pip install python-telegram-bot==22.8 matplotlib numpy \
                  certifi requests websocket-client bs4 fake-useragent orjson
  2) Put credentials.json next to this file:
       {"email":"you@x.com","password":"secret","proxy":""}
  3) export TELEGRAM_BOT_TOKEN=123456:ABC...
  4) python3 badicharts_bot.py

After /start the bot shows:
  -> 3 strategy buttons (2 on top + 1 below)
  -> 13 pair buttons with payout %
  -> Select All / Analyze / Back
  -> Each result has a red STOP button

Candles are fetched LIVE from Quotex on demand for each signal.
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


# ============================================================================
# SECTION 0.5: BOT-SPECIFIC IMPORTS
# ============================================================================
import io
import math
import random
from datetime import datetime, timedelta
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Any, Set

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patheffects as pe
from matplotlib.colors import to_rgb
from matplotlib.patches import Rectangle, Circle, Polygon

from telegram import Update, ReplyParameters, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.constants import KeyboardButtonStyle

# Style aliases for native colored button backgrounds
STYLE_BLUE = KeyboardButtonStyle.PRIMARY    # dark blue — main actions
STYLE_GREEN = KeyboardButtonStyle.SUCCESS   # green — positive/selected
STYLE_RED = KeyboardButtonStyle.DANGER      # red — destructive/stop
from telegram.ext import (Application, CommandHandler, CallbackQueryHandler,
                          ContextTypes)
from telegram.error import NetworkError, RetryAfter
import datetime as _dt

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
    """Logger that writes ONLY to file (silent console) when embedded in the bot.
    Set SILENT = False to re-enable console output for debugging."""

    SILENT = True  # When True, no console output (file-only)

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
        if not self.SILENT:
            ts = self._time()
            print(f"{paint(C2.DIM, '[INFO]')} {paint(C2.BRIGHT_CYAN, ts)} "
                  f"{paint(C2.DIM, '-')} {paint(C2.WHITE, msg)}")
        self._write_file("INFO", msg)

    def success(self, msg: str):
        if not self.SILENT:
            ts = self._time()
            print(f"{paint(C2.BOLD + C2.BRIGHT_GREEN, '[OK]')} {paint(C2.BRIGHT_CYAN, ts)} "
                  f"{paint(C2.DIM, '-')} {paint(C2.BRIGHT_GREEN, msg)}")
        self._write_file("OK", msg)

    def warn(self, msg: str):
        if not self.SILENT:
            ts = self._time()
            print(f"{paint(C2.BOLD + C2.BRIGHT_YELLOW, '[WARN]')} {paint(C2.BRIGHT_CYAN, ts)} "
                  f"{paint(C2.DIM, '-')} {paint(C2.BRIGHT_YELLOW, msg)}")
        self._write_file("WARN", msg)

    def error(self, msg: str):
        if not self.SILENT:
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
def _save_debug_json(candles: List[Dict], asset: str, timeframe_min: int, tag: str) -> None:
    """Save a debug snapshot of candles for gap-fill inspection."""
    if not candles: return
    try:
        debug_path = CANDLES_DIR / f"{asset}_{timeframe_min}m_{tag}.json"
        def fmt_dt(ts: int) -> str:
            return datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
        rows = []
        for c in candles:
            row = {"datetime": fmt_dt(c['time']), "time": c['time'], "open": c['open'],
                   "high": c['high'], "low": c['low'], "close": c['close'],
                   "volume": c.get('volume', 0), "synthetic": c.get('volume', 1) == 0}
            rows.append("    " + json.dumps(row, ensure_ascii=False))
        body = ",\n".join(rows)
        meta = {"asset": asset, "timeframe_minutes": timeframe_min, "candle_count": len(candles),
                "synthetic_count": sum(1 for c in candles if c.get('volume', 1) == 0),
                "tag": tag, "saved_at": datetime.now().isoformat(timespec="seconds")}
        meta_txt = json.dumps(meta, indent=2, ensure_ascii=False).replace("\n", "\n  ")
        with open(debug_path, 'w', encoding='utf-8') as f:
            f.write('{\n  "metadata": ' + meta_txt + ',\n  "candles": [\n' + body + '\n  ]\n}\n')
    except Exception: pass


def _aggregate_1s_to_target(raw_ticks: List, target_period: int) -> List[Dict]:
    """Aggregate 1-second tick data into target-period OHLC candles."""
    if not raw_ticks or target_period <= 1: return []
    prices_at_time = []
    for item in raw_ticks:
        if isinstance(item, dict):
            ts = int(item.get("time", item.get("timestamp", 0)))
            price = float(item.get("close", item.get("price", 0)) or 0)
            if ts > 0 and price > 0: prices_at_time.append((ts, price))
        elif isinstance(item, list) and len(item) >= 2:
            try:
                ts = int(item[0]); price = float(item[1])
                if ts > 0 and price > 0: prices_at_time.append((ts, price))
            except (ValueError, TypeError): continue
    if not prices_at_time: return []
    buckets = OrderedDict()
    for ts, price in prices_at_time:
        bucket_time = (ts // target_period) * target_period
        if bucket_time not in buckets: buckets[bucket_time] = []
        buckets[bucket_time].append(price)
    result = []
    for bucket_time, prices in buckets.items():
        if not prices: continue
        result.append({'time': bucket_time, 'open': prices[0], 'high': max(prices),
                       'low': min(prices), 'close': prices[-1], 'volume': len(prices)})
    return sorted(result, key=lambda x: x['time'])


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
        self.profit_by_asset: Dict[str, int] = {}
        self.max_profit_by_asset: Dict[str, int] = {}
        self.profit_history: Dict[str, List[int]] = defaultdict(list)
        self.instruments_profit_by_asset: Dict[str, int] = {}
        self.enabled_by_asset: Dict[str, bool] = {}
        self.live_prices: Dict[str, float] = {}
        self.live_ticks_seen: Dict[str, int] = defaultdict(int)
        self.last_tick_at: Dict[str, float] = {}

        # FIX #19: tick buffer لتجميع الأسعار اللحظية محلياً في شموع M1.
        # بدلاً من جلب 250 شمعة من Quotex في كل مرة (بطيء ومكلف)، نُجمّع
        # الـ ticks التي تصل عبر WebSocket في شموع M1 محلياً. هذا:
        #   - أسرع بـ 100x (لا حاجة لـ fetch_exactly_n)
        #   - لا يضغط على خادم Quotex
        #   - يعطي بيانات لحظية دقيقة (نفس ما يراه متداول على المنصة)
        # كل tick = (timestamp, price). القائمة محدودة بآخر 5000 tick لكل زوج
        # (تكفي لـ ~5 دقائق من البيانات اللحظية بـ 10 ticks/s).
        self.tick_buffer: Dict[str, deque] = defaultdict(lambda: deque(maxlen=5000))
        # شموع M1 المُجمَّعة محلياً من الـ ticks (آخر 300 شمعة لكل زوج)
        self.local_candles: Dict[str, deque] = defaultdict(lambda: deque(maxlen=300))
        # آخر مرة حاولنا فيها جلب شموع تاريخية لهذا الزوج (لتفادي الجلب المتكرر)
        self.last_historical_fetch: Dict[str, float] = {}
        self._ticks_lock = threading.Lock()  # حماية tick_buffer من race conditions

        self.instruments_ready = asyncio.Event()
        # instruments_locked = True once instruments/list provides data for an asset
        #   Once locked, depth/change CANNOT overwrite the payout for that asset.
        self.instruments_locked: Dict[str, bool] = {}
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
                    payout_int = int(payout)

                    # SKIP if this asset is locked by instruments/list
                    if self.instruments_locked.get(asset, False):
                        continue

                    self.profit_by_asset[asset] = payout_int

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
                    # FIX #19: خزّن الـ tick في buffer محلي لتجميعه لاحقاً في شمعة M1.
                    # tick[1] = timestamp (float), tick[2] = price.
                    # نستخدم timestamp الـ tick نفسه (وليس time.time()) لأنه
                    # الـ timestamp الفعلي من خادم Quotex.
                    try:
                        ts = float(tick[1]) if len(tick) > 1 and tick[1] else time.time()
                    except (TypeError, ValueError):
                        ts = time.time()
                    with self._ticks_lock:
                        self.tick_buffer[asset].append((ts, float(price)))
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
                    # FIX #19: خزّن الـ tick في buffer لتجميعه لاحقاً في شموع M1
                    try:
                        ts = float(tick[1]) if len(tick) > 1 and tick[1] else time.time()
                    except (TypeError, ValueError):
                        ts = time.time()
                    with self._ticks_lock:
                        self.tick_buffer[asset].append((ts, float(price)))
                    new_ticks += 1
            elif isinstance(tick, dict) and "asset" in tick and "price" in tick:
                asset = tick["asset"]
                price = tick["price"]
                if isinstance(asset, str) and isinstance(price, (int, float)):
                    self.live_prices[asset] = float(price)
                    self.live_ticks_seen[asset] += 1
                    self.last_tick_at[asset] = time.time()
                    # FIX #19: خزّن الـ tick في buffer (للـ dict form)
                    try:
                        ts = float(tick.get("time", tick.get("timestamp", time.time())))
                    except (TypeError, ValueError):
                        ts = time.time()
                    with self._ticks_lock:
                        self.tick_buffer[asset].append((ts, float(price)))
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

    # ============================================================
    # FIX #19: LIVE TICK AGGREGATION (instead of historical fetch)
    # ============================================================
    # بدلاً من جلب 250 شمعة تاريخية من Quotex في كل تحليل (بطيء ومكلف)،
    # نُجمّع الـ ticks اللحظية التي تصل عبر WebSocket في شموع M1 محلياً.
    # هذا هو نفس النهج المستخدم في mega_fetch.py:_aggregate_1s_to_target،
    # لكنه يطبّق على ticks مباشرة بدون الحاجة لجلب تاريخي منفصل.
    #
    # الميزة: الحصول على آخر شمعة M1 مباشرة من الـ ticks، بدون أي
    # latency من جلب تاريخي (الذي يستغرق 4-8s لكل زوج).
    def get_local_candles(self, asset: str, count: int = 250) -> List[Dict]:
        """اجمع الـ ticks المُخزَّنة في buffer في شموع M1 (60 ثانية لكل شمعة).

        Returns: قائمة شموع M1 (الأحدث آخرًا) أو [] لو لا توجد بيانات.
        كل شمعة: {time, open, high, low, close, volume}
        """
        with self._ticks_lock:
            ticks = list(self.tick_buffer.get(asset, []))
        if not ticks:
            return []
        # التأكد من ترتيب الـ ticks حسب الوقت
        ticks.sort(key=lambda x: x[0])
        # تجميع في شموع M1 (60 ثانية لكل bucket)
        # قاعدة bucket_time = (ts // 60) * 60 — بداية الدقيقة
        PERIOD = 60
        buckets: OrderedDict = OrderedDict()
        for ts, price in ticks:
            bucket_time = (int(ts) // PERIOD) * PERIOD
            if bucket_time not in buckets:
                buckets[bucket_time] = []
            buckets[bucket_time].append(price)
        # بناء OHLC من كل bucket
        candles = []
        for bucket_time, prices in buckets.items():
            if not prices:
                continue
            candles.append({
                'time': bucket_time,
                'open': float(prices[0]),
                'high': float(max(prices)),
                'low': float(min(prices)),
                'close': float(prices[-1]),
                'volume': len(prices),
            })
        # إرجاع آخر `count` شمعة (الأحدث آخرًا)
        return candles[-count:] if candles else []

    def get_tick_count(self, asset: str) -> int:
        """عدد الـ ticks المُخزَّنة في buffer لهذا الزوج (للتشخيص)."""
        with self._ticks_lock:
            return len(self.tick_buffer.get(asset, []))

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
        # GAP-FILL WITH REAL 1-SECOND DATA (ported from wedsoket_.py:fill_gap_once)
        # ============================================================
        # Fetch 1-SECOND candles (period=1) for maximum granularity,
        # then aggregate them into target timeframe.
        # This gives 8-13 real bridge candles with NO gaps.
        GAP_FILL_CANDLES = 10
        try:
            gap_fill_seconds = GAP_FILL_CANDLES * period_seconds
            # Fetch 1-SECOND candles (period=1, NOT period_seconds!)
            raw_1s_candles = await asyncio.wait_for(
                client.get_historical_candles(
                    asset, amount_of_seconds=gap_fill_seconds,
                    period=1,  # ← 1-SECOND candles!
                    max_workers=1, progress_callback=None,
                ), timeout=30,
            )
            # Aggregate 1s candles into target timeframe
            if raw_1s_candles and len(raw_1s_candles) > 0:
                real_candles = _aggregate_1s_to_target(raw_1s_candles, period_seconds)
            else:
                real_candles = []

            if real_candles:
                candle_map: Dict[int, Dict] = {}
                for c in candles:
                    candle_map[c['time']] = c
                current_period_start = (int(time.time()) // period_seconds) * period_seconds
                replaced_count = 0
                new_count = 0
                for c in real_candles:
                    if not isinstance(c, dict): continue
                    try:
                        ts = int(c.get("time", c.get("timestamp", 0)))
                        aligned = (ts // period_seconds) * period_seconds
                        o = float(c.get("open", 0)); h = float(c.get("high", c.get("max", 0)))
                        l = float(c.get("low", c.get("min", 0))); cl = float(c.get("close", 0))
                        v = int(c.get("volume", 0) or 0)
                        if o > 0 and h > 0 and l > 0 and cl > 0:
                            existing = candle_map.get(aligned)
                            if existing is None:
                                candle_map[aligned] = {'time': aligned, 'open': o, 'high': h,
                                                       'low': l, 'close': cl, 'volume': v}
                                new_count += 1
                            elif aligned >= current_period_start:
                                continue
                            elif existing.get('volume', 1) == 0:
                                candle_map[aligned] = {'time': aligned, 'open': o, 'high': h,
                                                       'low': l, 'close': cl, 'volume': v}
                                replaced_count += 1
                    except Exception: continue
                candles = sorted(candle_map.values(), key=lambda x: x['time'])
        except Exception:
            pass
        # Save snapshot before flat fill
        _save_debug_json(candles, asset, timeframe_min, "before_fill_missing")
        # Apply flat gap-filling for any remaining gaps
        before_fill = len(candles)
        candles = _fill_missing_slots(candles, period_seconds, max_gap=GAP_FILL_MAX_SLOTS)
        after_fill = len(candles)
        filled_count = after_fill - before_fill
        if filled_count > 0:
            elog.warn(f"Filled {filled_count} gap slots with flat candles for {asset}.")

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
# SECTION A: GANN SIGNAL ENGINE (replaces BADICHARTS strategy)
# ============================================================================
# هذه الاستراتيجية تحل محل استراتيجية BADICHARTS القديمة.
# تعتمد على:
#   1. كشف القمم والقيعان (fractal swings) من الشموع الحقيقية
#   2. بناء عوائل إسقاطات Gann الزمنية (Gann numbers + Fibonacci + Squares
#      + Ratio projections + Square-of-9)
#   3. البحث عن نقاط "confluence" حيث تتقاطع ≥3 عوائل → إشارة قوية
#   4. توليد إشارات BUY/SELL متناوبة لكل زوج قمة/قاع
#
# المخرجات: قائمة إشارات مستقبلية مع:
#   - entry_index (موقع شمعة الدخول المستقبلية)
#   - signal (BUY/SELL)
#   - confluence (عدد التطابقات)
#   - D (المسافة بين القمة والقاع)
# ============================================================================

import math as _gann_math

GANN_CONFIG = {
    "lookback":         40,    # آخر 40 شمعة في التحليل
    "swing_strength":   2,     # قوة fractal
    "min_confluence":   3,     # أقل عدد تطابقات للإشارة
    "signal_gap":       4,     # أقل مسافة بين إشارتين
    "entry_lead_time":  60,    # عرض ⚡ قبل 60 ثانية من الدخول
}

GANN_NUMBERS = [7, 9, 12, 14, 21, 30, 45, 60, 90, 120, 144, 180, 270, 360]
FIBONACCI    = [13, 34, 55, 89, 233]
SQUARES      = [16, 25, 36, 49, 64, 81, 100, 121, 169, 196, 225]
RATIOS       = [0.382, 0.5, 0.618, 0.786, 1.0, 1.272, 1.618,
                2.0, 2.618, 3.0, 4.0]


def _gann_time_str(candle):
    """يُرجع HH:MM من شمعة."""
    dt = candle.get("datetime")
    if isinstance(dt, str) and len(dt) >= 16:
        return dt[11:16]
    ts = candle.get("time", 0)
    if ts:
        try:
            return _dt.datetime.fromtimestamp(int(ts)).strftime("%H:%M")
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
                        "time_str": _gann_time_str(c),
                        "timestamp": int(c.get("time", 0))})
        if is_low:
            raw.append({"i": i, "type": "L", "price": float(c["low"]),
                        "time_str": _gann_time_str(c),
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
        sd = _gann_math.sqrt(D)
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
    """يولّد إشارات BUY/SELL متناوبة لكل زوج قمة/قاع.

    المخرج: قائمة dicts بـ:
      - entry_index: موقع شمعة الدخول المستقبلية
      - signal: "BUY" أو "SELL"
      - confluence: عدد التطابقات
      - D: المسافة بين القمة والقاع
      - pair: وصف الزوج (مثل "14:32H-14:35L")
      - first_sig: "BUY" أو "SELL" (الإشارة الأولى في السلسلة)
    """
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


def gann_pick_best_signal(candles, asset_name, max_lookahead=1):
    """يختار أفضل إشارة Gann للأصل — فقط إشارات الدخول خلال الدقيقة التالية.

    يعيد tuple (direction, strength, signal_dict) أو (None, 0, None) إن لم توجد إشارة.

    المعايير (مطابقة لطلب المستخدم):
      - نأخذ ONLY الإشارات التي entry_index == n (الشمعة التالية = دخول بعد ~60 ثانية)
      - هذا يضمن أن البوت يرسل الإشارة قبل الدخول بـ 1 دقيقة بالضبط
      - لو لا توجد إشارة دخولها الشمعة التالية → نُعيد None (البوت ينتظر)

    max_lookahead الافتراضي = 1 (الشمعة التالية فقط).
    لو لا توجد إشارة عند n، نحاول n+1 (دقيقتين) كـ fallback أخير.

    strength يُحسب كـ:
      - 50 (base) + (confluence - 3) * 10
      - capped عند 99%
    """
    if not candles or len(candles) < 20:
        return None, 0, None

    sigs = generate_signals_for_asset(candles, asset_name)
    if not sigs:
        return None, 0, None

    n = len(candles)
    # الأولوية 1: إشارات entry_idx == n (الدخول في الشمعة التالية = ~60 ثانية)
    # هذه هي الإشارات التي يجب إرسالها الآن (قبل الدخول بدقيقة)
    immediate = [s for s in sigs if s["entry_index"] == n]
    if immediate:
        # اختر أعلى confluence
        immediate.sort(key=lambda x: (-x["confluence"], x["entry_index"]))
        best = immediate[0]
        direction = best["signal"]
        conf = best["confluence"]
        strength = min(99, max(50, 50 + (conf - 3) * 10))
        return direction, strength, best

    # الأولوية 2: fallback — إشارة entry_idx == n+1 (دقيقتين)
    # هذا يحدث نادراً، لكن لو لم نجد إشارة عند n، نحاول n+1
    near = [s for s in sigs if s["entry_index"] == n + 1]
    if near:
        near.sort(key=lambda x: (-x["confluence"], x["entry_index"]))
        best = near[0]
        direction = best["signal"]
        conf = best["confluence"]
        strength = min(99, max(50, 50 + (conf - 3) * 10))
        return direction, strength, best

    # لا توجد إشارة دخولها خلال الدقيقتين القادمتين → أرجع None
    # البوت سينتظر دقيقة ثم يعيد المحاولة
    return None, 0, None


# ============================================================================
# SECTION B: LIVE CANDLE PROVIDER (wraps Quotex fetcher on demand)
# ============================================================================

class LiveCandleProvider:
    """Fetches live candles, live prices, and payout % from Quotex on demand.

    Uses the FULL mega_fetch engine embedded above:
      - Quotex client (connection + auth + WS)
      - MessageInterceptor (captures binary frames: instruments/list, depth/change,
        quotes/stream, history/load — the SAME interceptor that mega_fetch uses)
      - NeverSleepEngine (4 background tasks: keepalive_loop, stale_message_watchdog,
        auto_reconnect, health_monitor — keeps the connection alive forever)
      - CandleFetcher (5 parallel workers + gap-fill — fetches exactly N candles)
      - InstrumentsFetcher (profit %, enabled status — the AUTHORITATIVE payout source)
      - LivePriceSubscriber (subscribes to depth/follow + chart_notification +
        instruments/update for all 13 OTC pairs — keeps live prices flowing)

    All of this is the EXACT same logic as mega_fetch.py — nothing is omitted.
    """
    def __init__(self, email: str, password: str, proxies: Optional[str] = None):
        self.email = email
        self.password = password
        self.proxies = proxies
        self.client: Optional[Quotex] = None
        self.holder: Optional[ClientHolder] = None
        self.interceptor: Optional[MessageInterceptor] = None
        self.engine: Optional[NeverSleepEngine] = None
        self.fetcher: Optional[CandleFetcher] = None
        self.instruments_fetcher: Optional[InstrumentsFetcher] = None
        self.live_subscriber: Optional[LivePriceSubscriber] = None
        self._lock = asyncio.Lock()
        self._is_connecting = False
        # FIX #21: current_candles = الشموع الحية المُحدَّثة بالـ ticks في الوقت الفعلي.
        # بدلاً من إعادة جلب 250 شمعة من Quotex في كل مرة (بطيء)، نُحدّث الشمعة
        # الأخيرة مباشرة من الـ ticks الواردة عبر WebSocket. هذا يعني:
        #   - جلب تاريخي مرة واحدة عند البدء (250 شمعة)
        #   - كل tick يُحدّث الشمعة الحالية (close, high, low)
        #   - عند بدء دقيقة جديدة → شمعة جديدة تُضاف
        #   - التحليل دائماً يستخدم أحدث البيانات (لا تأخير!)
        #   - لا حاجة لانتظار 3 ساعات لتجميع 210 شموع من ticks
        self.current_candles: Dict[str, List[Dict]] = {}
        self._candles_lock = threading.Lock()
        # Candle cache (legacy, used as fallback)
        self._candles_cache: Dict[str, Tuple[float, List[Dict]]] = {}
        self._cache_ttl = 30.0
        # FIX #20: مرجع للـ event loop و thread الذي يشغّل مهام Quotex في الخلفية.
        # يُستخدم في _connect_quotex_blocking لتشغيل loop.run_forever() في thread
        # منفصل، بحيث تستمر مهام WebSocket و keepalive في العمل حتى بعد بدء البوت.
        self._keep_alive_loop: Optional[asyncio.AbstractEventLoop] = None
        self._keep_alive_thread: Optional[threading.Thread] = None

    async def _ensure_connected(self) -> bool:
        """Connect to Quotex if not already connected (or if connection died).

        Installs the MessageInterceptor + starts the NeverSleepEngine +
        subscribes to live prices for all 13 OTC pairs + fetches the
        instruments list (for payout %).
        """
        async with self._lock:
            if self._is_connecting:
                while self._is_connecting:
                    await asyncio.sleep(0.2)
                return self.client is not None and await self.client.check_connect()
            self._is_connecting = True
            try:
                if self.client is not None:
                    if await self.client.check_connect():
                        return True
                    try:
                        await self.client.close()
                    except Exception:
                        pass
                    self.client = None
                pass  # silent
                client = Quotex(email=self.email, password=self.password,
                                host="quotex.com", lang="en", proxies=self.proxies)
                check, reason = await client.connect()
                if not check:
                    pass  # silent
                    return False
                try:
                    await client.change_account("PRACTICE")
                    await asyncio.sleep(0.5)
                except Exception:
                    pass
                self.client = client
                # 1) Holder — allows NeverSleepEngine to swap clients on reconnect
                self.holder = ClientHolder(client, self.email, self.password, self.proxies)
                # 2) MessageInterceptor — captures binary frames (instruments + ticks + candles)
                self.interceptor = MessageInterceptor(client)
                if not self.interceptor.install():
                    pass  # silent
                # 3) NeverSleepEngine — 4 background tasks (keepalive, watchdog, reconnect, health)
                self.engine = NeverSleepEngine(self.holder, self.interceptor)
                self.engine.start()
                # 4) CandleFetcher — 5 parallel workers + gap-fill
                self.fetcher = CandleFetcher(self.holder, self.interceptor)
                # 5) InstrumentsFetcher — payout % (the AUTHORITATIVE source)
                self.instruments_fetcher = InstrumentsFetcher(self.holder, self.interceptor)
                # 6) LivePriceSubscriber — subscribes to live ticks for all 13 OTC pairs
                self.live_subscriber = LivePriceSubscriber(self.interceptor)
                self.live_subscriber.subscribe_all(OTC_ASSETS, period=60)
                # 7) Fetch the instruments list to populate payout % (non-blocking)
                try:
                    asyncio.create_task(self.instruments_fetcher.fetch(timeout=15.0))
                except Exception:
                    pass
                pass  # silent
                return True
            except Exception as e:
                pass  # silent
                return False
            finally:
                self._is_connecting = False

    def _update_candles_from_ticks(self):
        """FIX #21: حدّث current_candles من الـ ticks المُخزَّنة في buffer.
        
        هذه الدالة تُستدعى من keep_alive_loop كل بضع ثوانٍ. تقوم بـ:
          1. قراءة الـ ticks الجديدة من tick_buffer
          2. تحديث الشمعة الأخيرة (close, high, low) من كل tick
          3. إنشاء شمعة جديدة عند بدء دقيقة جديدة
          4. الحفاظ على آخر 300 شمعة فقط
          5. FIX #26: ضمان وجود شمعة حية للدقيقة الحالية دائماً
        
        هذا يعني أن current_candles دائماً يحتوي على أحدث البيانات،
        ولا حاجة لإعادة جلب الشموع التاريخية في كل مرة.
        """
        if self.interceptor is None:
            return
        now_ts = time.time()
        current_minute_bucket = (int(now_ts) // 60) * 60
        for asset in OTC_ASSETS:
            with self.interceptor._ticks_lock:
                ticks = list(self.interceptor.tick_buffer.get(asset, []))
                if ticks:
                    self.interceptor.tick_buffer[asset].clear()
            with self._candles_lock:
                candles = self.current_candles.get(asset, [])
                if not candles:
                    continue
                # معالجة كل tick
                for ts, price in ticks:
                    bucket = (int(ts) // 60) * 60
                    last = candles[-1] if candles else None
                    if last and last['time'] == bucket:
                        last['close'] = price
                        if price > last['high']:
                            last['high'] = price
                        if price < last['low']:
                            last['low'] = price
                        last['volume'] = last.get('volume', 0) + 1
                    elif (not last) or bucket > last['time']:
                        candles.append({
                            'time': bucket, 'open': price, 'high': price,
                            'low': price, 'close': price, 'volume': 1,
                        })
                        while len(candles) > 300:
                            candles.pop(0)
                # FIX #26: ضمان وجود شمعة حية للدقيقة الحالية.
                # لو آخر شمعة أقدم من الدقيقة الحالية، نُضيف شمعة حية
                # باستخدام آخر سعر متاح (من live_prices أو آخر close).
                # هذا يضمن أن:
                #   - candles[-1] = الشمعة الحية (الدقيقة الحالية)
                #   - candles[-2] = آخر شمعة مغلقة
                # فالمحرك يحلل عند n-2 (آخر مغلقة) ✓
                # والسهم يُرسم عند n-2 (آخر مغلقة) ✓
                last_candle = candles[-1] if candles else None
                if last_candle and last_candle['time'] < current_minute_bucket:
                    # استخدم آخر سعر متاح (live price أو close آخر شمعة)
                    live_price = self.interceptor.live_prices.get(asset)
                    seed_price = live_price if live_price is not None else last_candle['close']
                    candles.append({
                        'time': current_minute_bucket,
                        'open': seed_price,
                        'high': seed_price,
                        'low': seed_price,
                        'close': seed_price,
                        'volume': 0,  # شمعة حية، لا ticks بعد
                    })
                    while len(candles) > 300:
                        candles.pop(0)
                self.current_candles[asset] = candles

    async def fetch_candles(self, asset: str, count: int = 250,
                            timeframe_min: int = 1,
                            force_historical: bool = False) -> Optional[List[Dict]]:
        """Fetch candles — FIX #21: استخدم current_candles أولاً (مُحدَّث بالـ ticks).
        
        الأولوية:
          1) current_candles (مُحدَّث بالـ ticks في الوقت الفعلي — فوري!)
          2) الكاش (30s TTL)
          3) الجلب التاريخي من Quotex (fallback، مرة واحدة فقط)
        
        بعد الجلب التاريخي، نخزّن النتيجة في current_candles ليتم
        تحديثها بالـ ticks لاحقاً — لا حاجة لإعادة الجلب أبداً (إلا عند
        انقطاع الاتصال).
        """
        # ── Layer 1: current_candles (الأفضل — مُحدَّث بالـ ticks) ──
        if not force_historical and timeframe_min == 1:
            # FIX #26: استدعِ _update_candles_from_ticks قبل الإرجاع لضمان
            # وجود شمعة حية للدقيقة الحالية. هذا يمنع المشكلة التي كان
            # السهم يظهر فيها على شمعة أقدم بدقيقة كاملة.
            self._update_candles_from_ticks()
            with self._candles_lock:
                candles = list(self.current_candles.get(asset, []))
            if candles and len(candles) >= 210:
                # لدينا شموع كافية ومُحدَّثة بالـ ticks — استخدمها مباشرة!
                # تحقق من وجود شمعة حية للدقيقة الحالية
                current_minute_bucket = (int(time.time()) // 60) * 60
                last_candle_time = candles[-1]['time'] if candles else 0
                if last_candle_time < current_minute_bucket:
                    # أضف شمعة حية للدقيقة الحالية
                    live_price = self.interceptor.live_prices.get(asset) if self.interceptor else None
                    seed_price = live_price if live_price is not None else candles[-1]['close']
                    candles.append({
                        'time': current_minute_bucket,
                        'open': seed_price, 'high': seed_price,
                        'low': seed_price, 'close': seed_price, 'volume': 0,
                    })
                if len(candles) > count:
                    candles = candles[-count:]
                return candles

        # ── Layer 2: الكاش (للطلبات قصيرة المدى) ──
        now = time.time()
        cached = self._candles_cache.get(asset)
        if cached is not None:
            fetch_ts, cached_candles = cached
            if now - fetch_ts < self._cache_ttl and len(cached_candles) >= 210:
                # حدّث current_candles من الكاش (لو لم يكن موجوداً)
                if asset not in self.current_candles:
                    with self._candles_lock:
                        self.current_candles[asset] = list(cached_candles)
                return cached_candles

        # ── Layer 3: الجلب التاريخي من Quotex (fallback — مرة واحدة) ──
        if not await self._ensure_connected():
            return None
        if self.fetcher is None:
            return None
        try:
            import io as _io, contextlib as _ctxlib
            with _ctxlib.redirect_stdout(_io.StringIO()):
                candles = await asyncio.wait_for(
                    self.fetcher.fetch_exactly_n(asset, timeframe_min, count, progress=False),
                    timeout=60.0  # FIX: timeout لمنع التعليق
                )
        except asyncio.TimeoutError:
            print(f"FETCH {asset}: historical fetch timed out after 60s")
            return None
        except Exception as e:
            print(f"FETCH {asset}: historical fetch error: {e}")
            return None
        if not candles or len(candles) < 210:
            return None
        # Truncate to last `count`
        if len(candles) > count:
            candles = candles[-count:]
        # FIX #21: خزّن في current_candles ليتم تحديثها بالـ ticks لاحقاً
        with self._candles_lock:
            self.current_candles[asset] = list(candles)
        # Store in cache too
        self._candles_cache[asset] = (time.time(), candles)
        return candles

    def get_live_price(self, asset: str) -> Optional[float]:
        """Return the latest live price for the asset (from quotes/stream)."""
        if self.interceptor is None:
            return None
        return self.interceptor.get_live_price(asset)

    def get_payout(self, asset: str) -> Optional[int]:
        """Return the payout % for the asset (from instruments/list — AUTHORITATIVE).

        Priority:
          1. instruments_profit_by_asset (from binary instruments/list frame)
          2. MODE of profit_history (from depth/change + orders/closed)
          3. MAX as last fallback
        """
        if self.interceptor is None:
            return None
        return self.interceptor.get_profit(asset)

    def get_payout_dict(self) -> Dict[str, int]:
        """Return payout % for ALL known assets (a snapshot)."""
        if self.interceptor is None:
            return {}
        out = {}
        for asset in OTC_ASSETS:
            p = self.interceptor.get_profit(asset)
            if p is not None:
                out[asset] = p
        return out

    async def refresh_payouts(self):
        """Force-refresh payout % for all 13 OTC pairs.

        Sends chart_notification/get + depth/follow + orders/closed + instruments/get
        — the SAME refresh logic as mega_fetch's LivePriceSubscriber.refresh_payouts.
        """
        if self.live_subscriber is not None:
            try:
                self.live_subscriber.refresh_payouts(OTC_ASSETS)
            except Exception as e:
                pass  # silent

    async def keep_alive_loop(self):
        """Background task that keeps live prices flowing AND updates candles.

        FIX #21: أضفنا استدعاء _update_candles_from_ticks كل 2 ثانية.
        هذا يضمن أن current_candles دائماً مُحدَّث بالـ ticks اللحظية،
        فلا حاجة لإعادة جلب الشموع التاريخية في كل تحليل.
        """
        last_resubscribe = 0.0
        last_refresh = 0.0
        last_tick_update = 0.0
        resubscribe_interval = 30.0
        refresh_interval = 60.0
        tick_update_interval = 2.0  # FIX #21: حدّث الشموع كل 2 ثانية
        while True:
            try:
                now = time.time()
                # FIX #21: حدّث current_candles من الـ ticks (الأهم!)
                if now - last_tick_update >= tick_update_interval:
                    self._update_candles_from_ticks()
                    last_tick_update = now
                # Re-subscribe to live prices (sends depth/follow + instruments/update)
                if now - last_resubscribe >= resubscribe_interval:
                    if self.live_subscriber is not None:
                        try:
                            self.live_subscriber.subscribe_all(OTC_ASSETS, period=60)
                        except Exception:
                            pass
                    last_resubscribe = now
                # Refresh payouts (sends chart_notification/get + orders/closed + instruments/get)
                if now - last_refresh >= refresh_interval:
                    await self.refresh_payouts()
                    last_refresh = now
                # FIX #8: removed the noisy `print("LIVE PRICES: ...")` line that
                # was firing every 10 seconds and breaking the SILENT contract
                # of this loop. Live price status is now observable via the
                # `live_prices` dict on the interceptor (debug only).
                await asyncio.sleep(10)  # check every 10s
            except asyncio.CancelledError:
                raise
            except Exception:
                # Never let the keep-alive loop die — it's critical for live prices
                try:
                    await asyncio.sleep(10)
                except asyncio.CancelledError:
                    raise

    async def close(self):
        if self.engine is not None:
            try:
                await self.engine.stop()
            except Exception:
                pass
            self.engine = None
        if self.interceptor is not None:
            try:
                self.interceptor.restore()
            except Exception:
                pass
            self.interceptor = None
        if self.live_subscriber is not None:
            try:
                self.live_subscriber.unsubscribe_all()
            except Exception:
                pass
            self.live_subscriber = None
        if self.client is not None:
            try:
                await self.client.close()
            except Exception:
                pass
            self.client = None


# ============================================================================
# SECTION C: BOT CONFIGURATION + STATE
# ============================================================================

BOT_VERSION = "8.0.0-gann"
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
_ENV_CHAT_ID = os.environ.get("AUTO_SIGNAL_CHAT_ID", "") or os.environ.get("TELEGRAM_CHAT_ID", "")
AUTO_SIGNAL_CHAT_ID = ""
CHAT_ID_OVERRIDE = ""
ALWAYS_ASK_CHAT_ID = True
ALLOW_START_TO_REGISTER = False
REGISTRATION_OPEN = False
TOKEN_CACHE_FILE = Path(__file__).parent / ".badicharts_token_cache"
CHATID_CACHE_FILE = Path(__file__).parent / ".badicharts_chatid_cache"
STATS_FILE = Path(__file__).parent / ".badicharts_stats.json"
AUTO_SIGNAL_GAP_AFTER_RESULT = 10
AUTO_SIGNAL_START_DELAY = 3
CHART_CANDLES_COUNT = 30
CANDLE_SECONDS = 60
# FIX #5: minimum lead time (in seconds) between signal-sending time and
# entry_time. The old value was 5s, which was far too short — if the signal
# was sent at HH:MM:55, the entry was at HH:MM+1:00 (only 5s away), giving
# the user no time to read the signal and place the trade.
# 15s is a sensible minimum: enough time to read the caption and tap the
# trade button on Quotex. The lead time will be in [15s, 75s].
ENTRY_MIN_LEAD_SECONDS = 15

PAIR_LIST = [
    ("BRLUSD_otc", 87), ("USDARS_otc", 85), ("USDBDT_otc", 86),
    ("USDCOP_otc", 88), ("USDDZD_otc", 89), ("USDEGP_otc", 87),
    ("USDIDR_otc", 85), ("USDINR_otc", 86), ("USDMXN_otc", 84),
    ("USDNGN_otc", 88), ("USDPHP_otc", 89), ("USDPKR_otc", 87),
    ("USDZAR_otc", 85),
]

PAIR_BASE_PRICES = {
    "BRLUSD_otc": 0.20, "USDARS_otc": 920.0, "USDBDT_otc": 120.0,
    "USDCOP_otc": 4200.0, "USDDZD_otc": 254.5, "USDEGP_otc": 48.5,
    "USDIDR_otc": 15800.0, "USDINR_otc": 83.0, "USDMXN_otc": 17.3,
    "USDNGN_otc": 1600.0, "USDPHP_otc": 61.0, "USDPKR_otc": 280.0,
    "USDZAR_otc": 18.5,
}

# FIX #27: تمت إزالة أوضاع PRO و MAX. الآن يوجد فقط BADICHARTS (Quantex Expert V1)
STRATEGY_INFO = {
    "quantvexa": {"name": "GANN ENGINE", "accuracy": "Confluence-based", "emoji": ""},
}

STATS = {"wins": 0, "losses": 0}

# SIGNAL_HISTORY: قائمة بنتائج كل إشارة (تُضاف بعد كل نتيجة)
# كل entry = {time_str, symbol, dir_text, status, marker}
# status: "WIN" / "MTG_WIN" / "LOSS"
# marker: "✅" / "✅1" / "✖️"
SIGNAL_HISTORY: List[Dict] = []
SIGNALS_PER_REPORT = 10   # أرسل تقرير كل 10 إشارات
HISTORY_FILE = Path(__file__).parent / ".badicharts_history.json"
LIFECYCLE_TASKS: set = set()
LAST_LIFECYCLE_TASK: Optional[asyncio.Task] = None
LAST_SIGNAL_SENT_TIME: Optional[float] = None  # epoch seconds of last signal send
MIN_SIGNAL_GAP_SECONDS = 125  # hard minimum gap between signal batches (entry 60s + result 60s + 5s buffer)
_RENDER_LOCK: Optional[asyncio.Lock] = None
AUTO_SIGNAL_TASK: Optional[asyncio.Task] = None
CHAT_FORBIDDEN = False
candle_provider: Optional[LiveCandleProvider] = None


class BotState:
    strategy: str = "quantvexa"
    selected_pairs: Set[str] = set()
    stop_requested: bool = False
    active: bool = False


bot_state = BotState()


def load_stats():
    try:
        data = json.loads(STATS_FILE.read_text(encoding="utf-8"))
        STATS["wins"] = int(data.get("wins", 0))
        STATS["losses"] = int(data.get("losses", 0))
    except Exception:
        pass


def save_stats():
    try:
        STATS_FILE.write_text(json.dumps(STATS), encoding="utf-8")
    except Exception as e:
        print(f"WARNING: failed to save stats: {e}")


def load_history():
    """يحمّل سجل الإشارات من ملف."""
    global SIGNAL_HISTORY
    try:
        data = json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
        SIGNAL_HISTORY = data if isinstance(data, list) else []
    except Exception:
        SIGNAL_HISTORY = []


def save_history():
    """يحفظ سجل الإشارات إلى ملف."""
    try:
        # احتفظ بآخر 200 إشارة فقط
        SIGNAL_HISTORY_TRUNCATED = SIGNAL_HISTORY[-200:]
        HISTORY_FILE.write_text(json.dumps(SIGNAL_HISTORY_TRUNCATED, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception as e:
        print(f"WARNING: failed to save history: {e}")


def build_history_report(last_n=10):
    """يبني تقرير آخر N إشارة + إحصائيات تراكمية.

    الصيغة (مطابقة لطلب المستخدم):
        02:36 - EURUSD  -  CALL ✅
        02:41 - CADJPY  -  CALL ✅1
        02:44 - EURUSD  -  PUT  ✖️
        ...
        Win: 60 | Loss: 25 (71%)
    """
    if not SIGNAL_HISTORY:
        return "📊 No signals yet."
    lines = []
    # خذ آخر N إشارة
    recent = SIGNAL_HISTORY[-last_n:]
    for entry in recent:
        # كل سطر: HH:MM - SYMBOL  -  DIR  MARKER
        # SYMBOL بدون _otc (EUR/USD بدل EURUSD_otc)
        time_str = entry.get("time_str", "??:??")
        symbol = entry.get("symbol", "?")
        # تحويل EURUSD_otc → EURUSD  (أو EUR/USD لو 6 أحرف)
        sym_clean = symbol.replace("_otc", "").upper()
        if len(sym_clean) == 6 and sym_clean.isalpha():
            sym_display = f"{sym_clean[:3]}/{sym_clean[3:]}"
        else:
            sym_display = sym_clean
        dir_text = entry.get("dir_text", "?")  # "CALL" أو "PUT"
        marker = entry.get("marker", "?")      # "✅" أو "✅1" أو "✖️"
        # محاذاة: SYMBOL بعرض 7 + DIR بعرض 4
        lines.append(f"{time_str} - {sym_display:<7} - {dir_text:<4} {marker}")
    # إحصائيات تراكمية (كل التاريخ، ليس فقط آخر N)
    total_wins = sum(1 for h in SIGNAL_HISTORY if h.get("status") in ("WIN", "MTG_WIN"))
    total_losses = sum(1 for h in SIGNAL_HISTORY if h.get("status") == "LOSS")
    total = total_wins + total_losses
    win_rate = (total_wins / total * 100) if total else 0
    lines.append("")
    lines.append(f"Win: {total_wins} | Loss: {total_losses} ({win_rate:.0f}%)")
    return "\n".join(lines)


def add_to_history(sig, status):
    """يضيف إشارة + نتيجتها إلى SIGNAL_HISTORY.

    يُستدعى من _bd_signal_lifecycle بعد تحديد النتيجة.
    """
    global SIGNAL_HISTORY
    entry = {
        "time_str": sig["entry_time"].strftime("%H:%M"),
        "symbol": sig["symbol"],
        "dir_text": "CALL" if sig["direction"] == "BUY" else "PUT",
        "status": status,
        "marker": {"WIN": "✅", "MTG_WIN": "✅1", "LOSS": "✖️"}.get(status, "?"),
    }
    SIGNAL_HISTORY.append(entry)
    # احتفظ بآخر 200 إشارة فقط في الذاكرة
    if len(SIGNAL_HISTORY) > 200:
        SIGNAL_HISTORY = SIGNAL_HISTORY[-200:]
    save_history()


load_stats()
load_history()  # حمّل سجل الإشارات السابقة


# ============================================================================
# SECTION D: PLAIN-EMOJI CAPTIONS
# ============================================================================

LINE_SEP = "━" * 14


def pretty_symbol(symbol):
    base = symbol.replace("_otc", "").upper()
    if len(base) == 6 and base.isalpha():
        base = f"{base[:3]}/{base[3:]}"
    return f"{base} OTC"


def pair_display(symbol):
    return symbol.replace("_otc", "-OTC").upper()


def build_signal_caption(sig):
    is_buy = sig["direction"] == "BUY"
    dir_emoji = "🔼" if is_buy else "🔽"
    dir_text = "CALL ↑" if is_buy else "PUT ↓"
    # Live price line (only shown if we have a live price from Quotex)
    live_price = sig.get("live_price")
    if live_price is not None:
        price_line = f"💵 Price: {live_price:.5f}\n"
    else:
        price_line = ""
    return (
        f"👑 BADICHARTS 👑\n"
        f"{LINE_SEP}\n"
        f"💲 {pretty_symbol(sig['symbol'])}\n"
        f"{dir_emoji} {dir_text}\n"
        f"🔜 Entry: {sig['entry_time'].strftime('%H:%M')}\n"
        f"⏱️ Period: M1\n"
        f"🔥 Strength: {sig['strength']}%\n"
        f"🤑 Payout: {sig['payout']}%\n"
        f"{price_line}"
        f"{LINE_SEP}\n"
        f"🏦 QUOTEX"
    ).replace("\n", "\n")


def build_result_caption(sig, status, entry_candle, mtg_candle=None):
    """Build the result caption showing entry + martingale candles SEPARATELY.

    FIX #6: the old code used `last_candle` which was `candles[-1]` —
    in WIN/LOSS-with-martingale cases this was the WRONG candle (the
    martingale candle, not the entry candle the user actually traded on).
    Now we show both candles explicitly so the user can verify:
      - What the entry candle was (the one they traded on)
      - What the martingale candle was (if applicable)
    """
    is_buy = sig["direction"] == "BUY"
    dir_emoji = "🔼" if is_buy else "🔽"
    dir_text = "CALL ↑" if is_buy else "PUT ↓"
    won = status in ("WIN", "MTG_WIN")
    label = {"WIN": "WIN", "MTG_WIN": "MTG WIN", "LOSS": "LOSS"}[status]
    payout_txt = f"+{sig['payout']}%" if won else "-100%"
    result_emoji = "✅" if won else "❌"
    thumb = "👍" if won else "👎"
    ended = sig["entry_time"] + timedelta(seconds=CANDLE_SECONDS * (1 if status == "WIN" else 2))
    # ── ENTRY CANDLE (the candle the user actually traded on) ──
    # Show open/close separately so the user can verify the candle direction.
    price_line = ""
    if entry_candle is not None:
        e_open = entry_candle.get("open")
        e_close = entry_candle.get("close")
        if e_open is not None and e_close is not None:
            # Determine if the entry candle ITSELF won or lost
            entry_won = candle_wins(sig["direction"], entry_candle)
            entry_marker = "✅" if entry_won else "❌"
            price_line += f"🕯️ Entry Candle {entry_marker}\n   O={e_open:.5f}  C={e_close:.5f}\n"
    # ── MARTINGALE CANDLE (only shown if status is MTG_WIN or LOSS) ──
    # When the entry candle loses, the bot waits for ONE more candle (martingale)
    # and checks if it wins. We show this candle too so the user can see why
    # the final result is MTG_WIN or LOSS.
    # FIX #13: إذا لم تُجلب شمعة المارتينجال (placeholder)، نظهر رسالة
    # توضّح أن المارتينجال حدث لكن البيانات لم تصل من Quotex.
    if mtg_candle is not None and status in ("MTG_WIN", "LOSS"):
        # FIX #13: تحقق من placeholder
        if mtg_candle.get("_placeholder"):
            price_line += f"💰 Martingale ⚠️\n   (data not available from Quotex)\n"
        else:
            m_open = mtg_candle.get("open")
            m_close = mtg_candle.get("close")
            if m_open is not None and m_close is not None:
                mtg_won = candle_wins(sig["direction"], mtg_candle)
                mtg_marker = "✅" if mtg_won else "❌"
                price_line += f"💰 Martingale {mtg_marker}\n   O={m_open:.5f}  C={m_close:.5f}\n"
    # Live price at result time (if available)
    result_live = sig.get("result_live_price")
    if result_live is not None:
        price_line += f"📈 Live: {result_live:.5f}\n"
    return (
        f"👑 BADICHARTS 👑\n"
        f"{LINE_SEP}\n"
        f"💲 {pretty_symbol(sig['symbol'])}\n"
        f"{dir_emoji} {dir_text}\n"
        f"🔜 Entry: {sig['entry_time'].strftime('%H:%M')}\n"
        f"⏱️ Period: M1\n"
        f"⌛ Ended: {ended.strftime('%H:%M')}\n"
        f"{price_line}"
        f"{LINE_SEP}\n"
        f"{thumb} Result: {label} {result_emoji}\n"
        f"🤑 Payout: {payout_txt}\n"
        f"{LINE_SEP}\n"
        f"🏦 QUOTEX"
    ).replace("\n", "\n")


def build_status_message():
    total = STATS["wins"] + STATS["losses"]
    wr = f"{STATS['wins'] / total * 100:.0f}%" if total else "--"
    strat_info = STRATEGY_INFO.get(bot_state.strategy, {})
    provider_status = "🔌 Live (Quotex)" if candle_provider and candle_provider.client else "📁 File fallback"
    return (
        f"📊 BADICHARTS Status\n"
        f"{LINE_SEP}\n"
        f"💚 Status   : Online\n"
        f"🎁 Version  : {BOT_VERSION}\n"
        f"🧪 Engine   : {strat_info.get('name', bot_state.strategy)} ({strat_info.get('accuracy', '?')})\n"
        f"🕯️ Candles   : {CHART_CANDLES_COUNT} per chart\n"
        f"🔄 Auto     : 1 signal at a time\n"
        f"📎 Target   : {AUTO_SIGNAL_CHAT_ID or 'unset'}\n"
        f"🏁 Results  : {STATS['wins']}W / {STATS['losses']}L ({wr})\n"
        f"✅ Selected : {len(bot_state.selected_pairs)} pairs\n"
        f"📡 Provider : {provider_status}\n"
    ).replace("\n", "\n")


def build_welcome_message():
    return (
        f"👋 Welcome to BADICHARTS!\n\n"
        f"🤖 A Telegram bot that sends trading signals with professional charts.\n\n"
        f"📡 Candles are fetched LIVE from Quotex.\n"
        f"🧪 Engine: BADICHARTS (3 modes selectable).\n\n"
        f"📋 How to use:\n"
        f"  1️⃣ Select a strategy below\n"
        f"  2️⃣ Tap pairs to toggle them (🟩 ✅ = selected)\n"
        f"  3️⃣ Tap 'Start (N)' to begin — or 'Select All & Start' for all 13\n\n"
        f"📋 Commands:\n"
        f"  /start  - Show strategy menu\n"
        f"  /status - Show bot status\n"
        f"  /id     - Show your chat_id\n"
        f"  /resetstats - Reset W/L counters\n"
    ).replace("\n", "\n")


# ============================================================================
# SECTION E: NEON CHART RENDERER (1600x900)
# ============================================================================

BG = "#000000"; PANEL = "#04060C"; TILE = "#080C18"; EDGE = "#14265A"
BLUE = "#1F6BFF"; SKY = "#4CC9FF"; RED = "#FF1030"; GREEN = "#00FF66"
BONE = "#E8EEFF"; MUTED = "#8C98B3"; DIM = "#46526E"; GRIDC = "#0B1222"; TRACK = "#0F1830"
W, H = 1600, 900; MONO = "DejaVu Sans Mono"; BRAND = "BADICHARTS"
RESULTS_MAP = {
    "WIN":     ("WIN",     GREEN, "WON ON THE ENTRY CANDLE",      "✔ WIN"),
    "MTG_WIN": ("MTG WIN", GREEN, "WON ON MARTINGALE STEP 1",     "✔ MTG WIN"),
    "LOSS":    ("LOSS",    RED,   "LOST AFTER MARTINGALE STEP 1", "✖ LOSS"),
}


def _bd_pts(x, y, w, h, c):
    return [(x+c,y),(x+w,y),(x+w,y+h-c),(x+w-c,y+h),(x,y+h),(x,y+c)]


def _bd_panel(ax, x, y, w, h, c=16, fc=PANEL, ec=EDGE, lw=1.5, cut=RED, z=1, glow=False):
    pts = _bd_pts(x, y, w, h, c)
    if glow:
        ax.add_patch(Polygon(pts, closed=True, fill=False, edgecolor=ec, linewidth=lw*4, alpha=0.10, zorder=z))
    ax.add_patch(Polygon(pts, closed=True, facecolor=fc, edgecolor=ec, linewidth=lw, zorder=z, joinstyle="miter"))
    if cut and c >= 8:
        ax.plot([x,x+c],[y+c,y], color=cut, lw=lw+1.2, zorder=z+0.1, solid_capstyle="butt")
        ax.plot([x+w-c,x+w],[y+h,y+h-c], color=cut, lw=lw+1.2, zorder=z+0.1, solid_capstyle="butt")


def _bd_t(ax, x, y, s, size=11, color=BONE, ha="left", va="center", weight="bold", family=None, z=6, glow=None, **kw):
    t = ax.text(x, y, s, fontsize=size, color=color, ha=ha, va=va, fontweight=weight, family=family, zorder=z, **kw)
    if glow:
        t.set_path_effects([pe.Stroke(linewidth=5, foreground=glow, alpha=0.20), pe.Normal()])
    return t


def _bd_fmt(v):
    if v >= 10: return f"{v:.3f}"
    return f"{v:.4f}" if v >= 1 else f"{v:.5f}"


def _bd_lerp(c1, c2, t):
    a, b = np.array(to_rgb(c1)), np.array(to_rgb(c2))
    return tuple(a + (b-a)*t)


def render_signal_chart(candles, symbol, direction, payout=None, entry_time=None, status="PENDING", n_base=None, stats=None, confidence=None, now=None):
    now = now or datetime.now()
    if entry_time is None: entry_time = now + timedelta(minutes=1)
    is_buy = direction == "BUY"
    dcol = GREEN if is_buy else RED
    dtxt = "CALL" if is_buy else "PUT"
    dsub = "BUY  ·  M1  ·  OTC" if is_buy else "SELL  ·  M1  ·  OTC"
    is_result = status in RESULTS_MAP
    if is_result: r_title, rcol, r_sub, r_pill = RESULTS_MAP[status]
    n = len(candles); nb = n_base if n_base else n
    o = np.array([c["open"] for c in candles]); h = np.array([c["high"] for c in candles])
    l = np.array([c["low"] for c in candles]); c_ = np.array([c["close"] for c in candles])
    vol = np.array([c["volume"] for c in candles], dtype=float)
    times = [datetime.fromtimestamp(c["time"]) for c in candles]
    def sma(a, w): return np.array([a[max(0,i-w+1):i+1].mean() for i in range(len(a))])
    ma7, ma14, ma25 = sma(c_,7), sma(c_,14), sma(c_,25)
    support, resistance = l[:nb].min(), h[:nb].max()
    rng = max(resistance - support, 1e-9)
    data_lo, data_hi = min(l.min(), support), max(h.max(), resistance)
    span = max(data_hi - data_lo, 1e-9)
    ymin, ymax = data_lo - span*0.25, data_hi + span*0.25
    cur = c_[-1]; entry_price = c_[nb-1]
    sym = symbol.replace("_otc","-OTC").upper()
    pay = payout if payout is not None else 85
    conf = confidence if confidence is not None else random.randint(90,99)
    wins, losses = stats if stats else (0,0)
    total = wins + losses
    wr = (wins/total*100) if total else None
    fig = plt.figure(figsize=(W/100, H/100), dpi=100, facecolor=BG)
    bg = fig.add_axes([0,0,1,1], zorder=0); bg.set_xlim(0,W); bg.set_ylim(H,0); bg.axis("off")
    _bd_panel(bg, 20, 20, 1130, 860, c=24, fc=PANEL, ec=BLUE, lw=1.8, glow=True)
    _bd_t(bg, 44, 52, BRAND, 16, BONE)
    bg.plot([206,206],[34,70], color=EDGE, lw=1.4, zorder=4)
    _bd_t(bg, 228, 52, sym, 22, BONE)
    _bd_panel(bg, 528, 37, 52, 30, c=8, fc=TILE, ec=BLUE, lw=1.3, cut=None); _bd_t(bg, 554, 52, "M1", 10.5, BLUE, ha="center")
    _bd_panel(bg, 590, 37, 58, 30, c=8, fc=TILE, ec=SKY, lw=1.3, cut=None); _bd_t(bg, 619, 52, "OTC", 10.5, SKY, ha="center")
    live_col = rcol if is_result else GREEN; live_txt = "RESULT" if is_result else "LIVE"
    bg.add_patch(Circle((968,52), 6, facecolor=live_col, edgecolor="none", zorder=5))
    bg.add_patch(Circle((968,52), 11, facecolor=live_col, edgecolor="none", zorder=4, alpha=0.2))
    _bd_t(bg, 984, 52, live_txt, 10, live_col)
    _bd_panel(bg, 1066, 37, 68, 30, c=8, fc="#03140A", ec=GREEN, lw=1.3, cut=None); _bd_t(bg, 1100, 52, f"{pay}%", 11, GREEN, ha="center")
    lx = 44
    for lab, col in [("MA 7",BLUE),("MA 14",SKY),("MA 25",BONE)]:
        bg.plot([lx,lx+22],[88,88], color=col, lw=2.6, zorder=6, solid_capstyle="round")
        _bd_t(bg, lx+30, 88, lab, 9, MUTED, family=MONO); lx += 100
    AX_X, AX_Y, AX_W, AX_H = 40, 106, 1010, 660; VX_Y, VX_H = 782, 62
    def rect(x,y,w,hh): return [x/W, 1-(y+hh)/H, w/W, hh/H]
    pad = 3.6; x0, x1 = -0.9, n-1+pad
    ax = fig.add_axes(rect(AX_X,AX_Y,AX_W,AX_H), zorder=2); ax.set_facecolor("none")
    ax.set_xlim(x0,x1); ax.set_ylim(ymin,ymax)
    for s in ax.spines.values(): s.set_visible(False)
    ax.set_xticks([]); ax.set_yticks([])
    def py(v): return AX_Y + (ymax-v)/(ymax-ymin)*AX_H
    def px(xv): return AX_X + (xv-x0)/(x1-x0)*AX_W
    for t in np.linspace(ymin, ymax, 8):
        ax.axhline(t, color=GRIDC, lw=1.0, zorder=1)
        if abs(t-cur) > (ymax-ymin)*0.05:
            bg.text(AX_X+AX_W+12, py(t), _bd_fmt(t), color=DIM, fontsize=8.5, ha="left", va="center", family=MONO, zorder=5)
    for gx in range(0, n, 3): ax.axvline(gx, color=GRIDC, lw=0.8, zorder=1)
    ax.axhline(resistance, color=RED, lw=1.0, ls=(0,(5,4)), alpha=0.95, zorder=3)
    ax.axhline(support, color=GREEN, lw=1.0, ls=(0,(5,4)), alpha=0.95, zorder=3)
    for val, col, tag, up in [(resistance,RED,"R",True),(support,GREEN,"S",False)]:
        yy = py(val); off = -26 if up else 8
        _bd_panel(bg, AX_X+6, yy+off, 116, 20, c=6, fc=BG, ec=col, lw=1.0, cut=None, z=7)
        _bd_t(bg, AX_X+64, yy+off+10, f"{tag}  {_bd_fmt(val)}", 8.5, col, ha="center", family=MONO, z=8)
    ax.axvspan(nb-1-0.8, nb-1+0.8, color=dcol, alpha=0.10, zorder=2, lw=0)
    ax.axvline(nb-0.5, color=SKY, lw=1.3, ls=(0,(3,3)), alpha=0.95, zorder=4)
    _bd_panel(bg, px(nb-0.5)+6, AX_Y+6, 66, 20, c=6, fc=BG, ec=SKY, lw=1.0, cut=None, z=7)
    _bd_t(bg, px(nb-0.5)+39, AX_Y+16, "ENTRY", 8.5, SKY, ha="center", z=8)
    if is_result:
        ax.axvspan(nb-0.5, n-0.5, color=rcol, alpha=0.09, zorder=2, lw=0)
        ax.hlines(entry_price, nb-0.5, x1, color=SKY, lw=1.0, ls=(0,(4,3)), alpha=0.85, zorder=4)
    else:
        ax.axvspan(nb-0.5, x1, color=dcol, alpha=0.045, zorder=2, lw=0)
    xs = np.arange(n)
    for series, col in [(ma25,BONE),(ma14,SKY),(ma7,BLUE)]:
        ax.plot(xs, series, color=col, lw=1.8, zorder=4, path_effects=[pe.Stroke(linewidth=6, foreground=col, alpha=0.16), pe.Normal()])
    bw = 0.60
    for i in range(n):
        col = GREEN if c_[i] >= o[i] else RED
        ax.plot([i,i],[l[i],h[i]], color=col, lw=1.6, zorder=5, solid_capstyle="butt", path_effects=[pe.Stroke(linewidth=5, foreground=col, alpha=0.14), pe.Normal()])
        lo, hi = min(o[i],c_[i]), max(o[i],c_[i])
        ax.add_patch(Rectangle((i-bw/2, lo), bw, max(hi-lo, span*0.004), facecolor=col, edgecolor=col, lw=0.5, zorder=6))
    ax.axhline(cur, color=BLUE, lw=0.9, ls=(0,(2,3)), alpha=0.95, zorder=3)
    yy = py(cur)
    bg.add_patch(Polygon(_bd_pts(AX_X+AX_W+6, yy-14, 82, 28, 8), closed=True, facecolor=BLUE, edgecolor="none", zorder=8))
    _bd_t(bg, AX_X+AX_W+47, yy, _bd_fmt(cur), 9.5, "#FFFFFF", ha="center", family=MONO, z=9)
    s_i = nb-1
    # FIX #22: للإشارة الجديدة (PENDING) قبل ظهور النتيجة، ارسم السهم على
    # شمعة n-2 (آخر شمعة مغلقة)، وليس على شمعة n-1 (الشمعة الحية التي
    # ما زالت تتشكل). المحرك يُحلل عند cur = n-2، فالسهم يجب أن يكون
    # على نفس الشمعة. خط ENTRY يبقى عند nb-0.5 (يمين آخر شمعة = entry).
    # لحالة RESULT، السهم يبقى على nb-1 (آخر شمعة من base = شمعة الإشارة).
    if not is_result:
        s_i = nb - 2  # PENDING: السهم على آخر شمعة مغلقة
    # else: s_i = nb - 1 (RESULT: السهم على شمعة الإشارة قبل entry candle)
    if s_i < 0:
        s_i = 0  # حماية من قائمة شموع صغيرة جداً
    if is_buy: tip, bpos, mk, va = l[s_i]-span*0.06, l[s_i]-span*0.15, "^", "top"
    else: tip, bpos, mk, va = h[s_i]+span*0.06, h[s_i]+span*0.15, "v", "bottom"
    ax.plot([s_i],[tip], marker=mk, markersize=14, color=dcol, zorder=9, clip_on=False, path_effects=[pe.Stroke(linewidth=10, foreground=dcol, alpha=0.28), pe.Normal()])
    ax.annotate(dtxt, xy=(s_i,bpos), ha="center", va=va, color="#000000", fontsize=10, fontweight="bold", zorder=10, annotation_clip=False, bbox=dict(boxstyle="square,pad=0.45", facecolor=dcol, edgecolor=dcol))
    if is_result:
        if status in ("MTG_WIN","LOSS") and n > nb:
            ax.plot([nb],[h[nb]+span*0.05], marker="x", markersize=11, color=RED, markeredgewidth=2.8, zorder=9, clip_on=False)
        ax.annotate(r_pill, xy=(n-1, h[-1]+span*0.09), ha="center", va="bottom", color="#000000", fontsize=10, fontweight="bold", zorder=10, annotation_clip=False, bbox=dict(boxstyle="square,pad=0.45", facecolor=rcol, edgecolor=rcol))
    vx = fig.add_axes(rect(AX_X,VX_Y,AX_W,VX_H), zorder=2); vx.set_facecolor("none")
    vx.set_xlim(x0,x1); vx.set_ylim(0, max(vol.max()*1.1, 1.0))
    for s in vx.spines.values(): s.set_visible(False)
    vx.set_yticks([])
    for i in range(n):
        col = GREEN if c_[i] >= o[i] else RED
        vx.add_patch(Rectangle((i-0.3, 0), 0.6, vol[i], facecolor=col, edgecolor="none", alpha=0.45))
    tp = list(range(0, n, 3)); vx.set_xticks(tp); vx.set_xticklabels([times[i].strftime("%H:%M") for i in tp])
    vx.tick_params(axis="x", colors=DIM, labelsize=8.5, length=0, pad=6)
    for lab in vx.get_xticklabels(): lab.set_family(MONO)
    RX, RW = 1166, 414; D = -126; B = 654
    _bd_panel(bg, RX, 146+D, RW, 88, c=16, fc=PANEL, ec=EDGE, lw=1.3)
    _bd_t(bg, RX+28, 170+D, "CONFIDENCE", 9.5, MUTED); _bd_t(bg, RX+RW-24, 170+D, f"{conf}%", 14, dcol, ha="right")
    segs, gap = 20, 4; sw = (RW-56-gap*(segs-1))/segs; filled = round(segs*conf/100)
    for i in range(segs):
        sx0 = RX+28+i*(sw+gap); col = dcol if i < filled else TRACK
        bg.add_patch(Polygon([(sx0+4,192+D),(sx0+sw+4,192+D),(sx0+sw,216+D),(sx0,216+D)], closed=True, facecolor=col, edgecolor="none", zorder=4))
    _bd_panel(bg, RX, 248+D, RW, 200, c=16, fc=PANEL, ec=EDGE, lw=1.3)
    _bd_t(bg, RX+28, 274+D, "TRADE DETAILS", 9.5, MUTED)
    info = [("Entry Time", entry_time.strftime("%H:%M"), SKY),("Market","OTC",BLUE),("Payout",f"{pay}%",GREEN),("Martingale","1 Step",RED)]
    for i, (lab,val,col) in enumerate(info):
        y = 312+D+i*34
        bg.add_patch(Polygon([(RX+30,y-5),(RX+39,y),(RX+30,y+5)], closed=True, facecolor=col, edgecolor="none", zorder=5))
        _bd_t(bg, RX+48, y, lab, 11.5, MUTED, weight="normal"); _bd_t(bg, RX+RW-24, y, val, 13, col, ha="right", family=MONO)
        if i < len(info)-1: bg.plot([RX+28,RX+RW-24],[y+17,y+17], color=EDGE, lw=0.8, zorder=3)
    _bd_panel(bg, RX, 462+D, RW, 116, c=16, fc=PANEL, ec=EDGE, lw=1.3)
    _bd_t(bg, RX+28, 486+D, "PERFORMANCE", 9.5, MUTED)
    _bd_t(bg, RX+RW-24, 486+D, f"{wr:.0f}%" if wr is not None else "--", 14, GREEN, ha="right")
    bg.add_patch(Rectangle((RX+28,500+D), RW-52, 8, facecolor=TRACK, edgecolor="none", zorder=3))
    if wr: bg.add_patch(Rectangle((RX+28,500+D), max((RW-52)*wr/100, 8), 8, facecolor=GREEN, edgecolor="none", zorder=4))
    for i, (num,lab,col) in enumerate([(wins,"WINS",GREEN),(losses,"LOSSES",RED),(total,"TOTAL",BLUE)]):
        bx_ = RX+28+i*124
        _bd_panel(bg, bx_, 520+D, 114, 44, c=9, fc=TILE, ec=EDGE, lw=0.9, cut=None)
        _bd_t(bg, bx_+57, 536+D, str(num), 16, col, ha="center", family=MONO); _bd_t(bg, bx_+57, 553+D, lab, 7.5, MUTED, ha="center")
    _bd_panel(bg, RX, 592+D, RW, 174, c=16, fc=PANEL, ec=EDGE, lw=1.3)
    _bd_t(bg, RX+28, 616+D, "PRICE VS LEVELS", 9.5, MUTED)
    gx0, gw, gy, gh = RX+32, RW-64, 672+D, 14; steps = 48; swd = gw/steps
    for i in range(steps):
        col = _bd_lerp(GREEN, RED, i/(steps-1))
        bg.add_patch(Rectangle((gx0+i*swd, gy), swd+0.6, gh, facecolor=col, edgecolor="none", zorder=4))
    frac = float(np.clip((cur-support)/rng, 0, 1)); mx = gx0+frac*gw
    bg.plot([mx,mx],[gy-3,gy+gh+6], color="#FFFFFF", lw=2.2, zorder=7)
    bg.add_patch(Polygon([(mx,gy-3),(mx-7,gy-14),(mx+7,gy-14)], closed=True, facecolor="#FFFFFF", edgecolor="none", zorder=7))
    px_c = float(np.clip(mx, gx0+52, gx0+gw-52))
    _bd_panel(bg, px_c-52, 630+D, 104, 26, c=7, fc=BLUE, ec=BLUE, lw=0, cut=None, z=8)
    _bd_t(bg, px_c, 643+D, _bd_fmt(cur), 10.5, "#FFFFFF", ha="center", family=MONO, z=9)
    _bd_t(bg, gx0, 708+D, "SUPPORT", 8, MUTED, va="bottom"); _bd_t(bg, gx0, 712+D, _bd_fmt(support), 13, GREEN, va="top", family=MONO)
    _bd_t(bg, gx0+gw, 708+D, "RESISTANCE", 8, MUTED, ha="right", va="bottom"); _bd_t(bg, gx0+gw, 712+D, _bd_fmt(resistance), 13, RED, ha="right", va="top", family=MONO)
    _bd_panel(bg, RX, B, RW, 112, c=22, fc=dcol, ec=dcol, lw=0, cut=BLUE, glow=False)
    bg.add_patch(Circle((RX+62, B+56), 30, facecolor="#000000", edgecolor="none", zorder=5, alpha=0.18))
    tri = ([(RX+62,B+42),(RX+80,B+70),(RX+44,B+70)] if is_buy else [(RX+44,B+42),(RX+80,B+42),(RX+62,B+70)])
    bg.add_patch(Polygon(tri, closed=True, facecolor="#000000", edgecolor="none", zorder=7))
    _bd_t(bg, RX+110, B+46, dtxt, 38, "#000000"); _bd_t(bg, RX+112, B+86, dsub, 9.5, "#000000")
    _bd_t(bg, RX+RW-20, B+18, f"ENTRY {entry_time.strftime('%H:%M')}", 9.5, "#000000", ha="right", family=MONO)
    if is_result: bcol = rcol; fill = "#03140A" if rcol == GREEN else "#18030A"
    else: bcol, fill = BLUE, "#030A1E"
    _bd_panel(bg, RX, 780, RW, 100, c=20, fc=fill, ec=bcol, lw=2.4, cut=RED if not is_result else bcol, glow=True)
    cxm = RX+RW/2
    if is_result:
        _bd_t(bg, cxm, 800, "RESULT", 8.5, MUTED, ha="center"); _bd_t(bg, cxm, 835, r_title, 30, rcol, ha="center", glow=rcol); _bd_t(bg, cxm, 864, r_sub, 7.5, MUTED, ha="center")
    else:
        _bd_t(bg, cxm, 800, "ENTRY TIME", 8.5, MUTED, ha="center"); _bd_t(bg, cxm, 835, entry_time.strftime("%H:%M"), 32, SKY, ha="center", family=MONO, glow=BLUE); _bd_t(bg, cxm, 864, "WAIT FOR THE ENTRY CANDLE", 7.5, MUTED, ha="center")
    buf = io.BytesIO(); fig.savefig(buf, dpi=100, format="png", facecolor=BG); plt.close(fig); return buf.getvalue()


# ============================================================================
# SECTION F: SIGNAL BUILDING (REAL candles only — no virtual fallback)
# ============================================================================

def generate_next_candles(base_candles, k, first_time):
    """Generate simulated follow-up candles for the entry/martingale steps.

    These are NOT used for the signal chart (which uses real candles from
    Quotex). They are only used to simulate what the entry/martingale
    candles might look like for the result chart.
    """
    rng = np.random.default_rng()
    closes = np.array([c["close"] for c in base_candles])
    sigma = float(np.std(np.diff(closes))) or abs(closes[-1])*0.0005
    out = []; price = base_candles[-1]["close"]
    for i in range(k):
        o = price; c = o + rng.normal(0, sigma); wick = sigma*rng.uniform(0.2, 0.9)
        out.append({"time": int((first_time + timedelta(seconds=CANDLE_SECONDS*i)).timestamp()), "open": float(o), "high": float(max(o,c)+rng.uniform(0.05,1.0)*wick), "low": float(min(o,c)-rng.uniform(0.05,1.0)*wick), "close": float(c), "volume": int(rng.uniform(100, 1500))})
        price = c
    return out


def candle_wins(direction, candle):
    if direction == "BUY": return candle["close"] > candle["open"]
    return candle["close"] < candle["open"]


def build_signal(direction=None, symbol=None, payout=None, display_candles=None, strength=0, gann_signal=None, total_candle_count=None):
    """Build a signal dict. display_candles MUST be provided (real candles from Quotex).

    Args:
        strength: REAL win rate from the engine's firing config (0-99).
        gann_signal: optional dict from Gann engine with entry_index.
                     If provided, entry_time is computed from entry_index
                     relative to the LAST candle in total_candle_count.
        total_candle_count: total candles fetched from Quotex (for entry_index calc).

    GANN MODE: when gann_signal is provided, entry_time is the START of the
    candle at index `entry_index`. The bot sends the signal 1 MINUTE before
    this entry time so the user has time to place the trade.
    """
    if symbol is None:
        symbol, payout = random.choice(PAIR_LIST)
    elif payout is None:
        payout = dict(PAIR_LIST).get(symbol, 85)
    if display_candles is None:
        raise ValueError("build_signal requires display_candles from Quotex")
    candles = [dict(c) for c in display_candles]
    # FIX #23: مؤشر الفوليوم — استخدم متوسط الفوليوم الحقيقي للشموع ذات
    # الفوليوم المفقود (0 أو None)، بدلاً من 1.0 الذي يجعلها غير مرئية.
    # السبب: الشموع التاريخية من Quotex لها فوليوم حقيقي (100-2000)، بينما
    # الشموع المُجمَّعة من ticks لها فوليوم صغير (1-50). لو وضعنا 1.0
    # للشموع ذات الفوليوم المفقود، تصبح أشرطة الفوليوم غير مرئية مقارنة
    # بالشموع ذات الفوليوم الكبير. الحل: استخدم متوسط الفوليوم الحقيقي.
    real_volumes = [c.get('volume', 0) for c in candles if c.get('volume', 0) > 0]
    avg_volume = sum(real_volumes) / len(real_volumes) if real_volumes else 100
    for c in candles:
        if not c.get('volume') or c['volume'] == 0:
            c['volume'] = int(avg_volume)
    # GANN ENTRY TIME: compute entry_time from Gann signal's entry_index
    # The Gann engine tells us WHICH candle index will be the entry candle.
    # entry_index = the position in the candle list (0-based).
    # entry_time = the START timestamp of that candle.
    #
    # If the entry candle is in the FUTURE (entry_index >= total_candle_count),
    # entry_time = last_candle_time + (entry_index - last_index) * 60 seconds.
    #
    # The bot sends the signal NOW (1 minute before entry) so the user has
    # time to read it and place the trade.
    now = datetime.now()
    if gann_signal is not None and total_candle_count is not None:
        # GANN MODE: compute entry_time from entry_index
        try:
            entry_idx = int(gann_signal.get("entry_index", 0))
            # آخر شمعة في القائمة الإجمالية لها index = total_candle_count - 1
            last_idx = total_candle_count - 1
            # لو entry_idx <= last_idx → إشارة في الماضي، تجاهلها
            if entry_idx <= last_idx:
                # Fallback: استخدم الدقيقة التالية من الوقت الحالي
                entry_time = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
            else:
                # عدد الشموع المستقبلية بين آخر شمعة وشمعة الدخول
                candles_ahead = entry_idx - last_idx
                # entry_time = الآن + candles_ahead دقائق (مقرّبة لبداية الدقيقة)
                # نقوم بالتقريب إلى بداية الدقيقة التالية
                next_minute = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
                entry_time = next_minute + timedelta(minutes=candles_ahead - 1)
            print(f"GANN entry_time computed: {entry_time.strftime('%H:%M')} (entry_idx={entry_idx}, last_idx={last_idx})")
        except Exception as e:
            print(f"GANN entry_time calc failed: {e}, falling back to next minute")
            entry_time = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
    else:
        # LEGACY MODE (no Gann signal): use next minute boundary
        entry_time = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
    # enforce MINIMUM 15-second lead time (same as before)
    lead_seconds = (entry_time - now).total_seconds()
    if lead_seconds < ENTRY_MIN_LEAD_SECONDS:
        entry_time = entry_time + timedelta(minutes=1)
    # Re-time candles so the LAST display candle ends at entry_time
    # (preserves visual continuity on the chart).
    n = len(candles)
    for i, c in enumerate(candles):
        c["time"] = int((entry_time - timedelta(seconds=CANDLE_SECONDS*(n-i))).timestamp())
    if direction is None:
        direction = "BUY" if candles[-1]["close"] > candles[-2]["close"] else "SELL"
    # FIX #1: strength is REAL win rate (0-99) from the engine, not random.
    # Clamp to a sensible display range so users see 50-99% on signal captions.
    if strength is None or strength <= 0:
        strength = 50  # neutral fallback when engine gave no score
    elif strength < 50:
        strength = 50   # floor — don't show below 50% even if backtest was worse
    elif strength > 99:
        strength = 99
    return {"symbol": symbol, "candles": candles, "direction": direction,
            "entry_time": entry_time, "strength": int(strength), "payout": payout,
            "support": min(c["low"] for c in candles),
            "resistance": max(c["high"] for c in candles)}


# ============================================================================
# SECTION G: INLINE KEYBOARDS
# ============================================================================

def build_strategy_keyboard():
    """FIX #27: زر استراتيجية واحد فقط — BADICHARTS (Quantex Expert V1).
    تمت إزالة أزرار PRO و MAX.
    """
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("GANN ENGINE  Confluence", callback_data="strat:quantvexa", style=STYLE_BLUE),
        ],
    ])


def build_pair_keyboard():
    """13 pair buttons (2 per row) + back / select-all-start / clear.
    Uses KeyboardButtonStyle for NATIVE colored backgrounds:
      - Unselected pairs: PRIMARY (blue) background
      - Selected pairs:   SUCCESS (green) background + ✅
      - Start button:     SUCCESS (green)
      - Clear button:     DANGER (red)
      - Back button:      PRIMARY (blue)
    """
    buttons = []
    row = []
    for symbol, payout in PAIR_LIST:
        display = pair_display(symbol)
        if symbol in bot_state.selected_pairs:
            text = f"✅ {display}  {payout}%"
            style = STYLE_GREEN
        else:
            text = f"{display}  {payout}%"
            style = STYLE_BLUE
        row.append(InlineKeyboardButton(text, callback_data=f"pair:{symbol}", style=style))
        if len(row) == 2:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    selected_count = len(bot_state.selected_pairs)
    if selected_count == 0:
        buttons.append([
            InlineKeyboardButton("⬅️ Back", callback_data="back", style=STYLE_BLUE),
            InlineKeyboardButton("✅ Select All & Start", callback_data="selectall", style=STYLE_GREEN),
        ])
    else:
        buttons.append([
            InlineKeyboardButton("⬅️ Back", callback_data="back", style=STYLE_BLUE),
            InlineKeyboardButton("🧹 Clear", callback_data="clear", style=STYLE_RED),
            InlineKeyboardButton(f"▶️ Start ({selected_count})", callback_data="analyze", style=STYLE_GREEN),
        ])
    return InlineKeyboardMarkup(buttons)


def build_stop_keyboard():
    """Red STOP button — shown below each result.
    Uses KeyboardButtonStyle.DANGER for NATIVE red background.
    """
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🛑 STOP", callback_data="stop", style=STYLE_RED)]
    ])


# ============================================================================
# SECTION H: SIGNAL LIFECYCLE + RENDERING
# ============================================================================

async def _bd_render(**kwargs):
    global _RENDER_LOCK
    if _RENDER_LOCK is None:
        _RENDER_LOCK = asyncio.Lock()
    async with _RENDER_LOCK:
        return await asyncio.to_thread(render_signal_chart, **kwargs)


def _bd_render_kwargs(sig, candles, status, n_base):
    return dict(candles=candles, symbol=sig["symbol"], direction=sig["direction"], payout=sig["payout"], entry_time=sig["entry_time"], status=status, n_base=n_base, stats=(STATS["wins"], STATS["losses"]), confidence=sig["strength"])


async def _bd_sleep_until(moment):
    delay = (moment - datetime.now()).total_seconds()
    if delay > 0:
        await asyncio.sleep(delay)


WAIT_TICK_SECONDS = 2
ENTRY_LABEL = "Waiting for entry..."
WAIT_LABEL = "Waiting for result..."
MTG_LABEL = "Martingale..."


def _bd_wait_caption(remaining, label=WAIT_LABEL):
    """يبني نص العداد — يعرض دقائق وثواني بدلاً من قمع عند 59."""
    remaining = max(0, int(remaining))
    if remaining >= 60:
        mins = remaining // 60
        secs = remaining % 60
        return f"⌛ {label} {mins}m {secs:02d}s"
    return f"⌛ {label} {remaining:02d}s"


def _bd_secs_left(target):
    return max(0, int(round((target - datetime.now()).total_seconds())))


async def _bd_wait_ticker(bot, chat_id, msg_id, state):
    while True:
        await asyncio.sleep(WAIT_TICK_SECONDS)
        text = _bd_wait_caption(_bd_secs_left(state["target"]), state["label"])
        try:
            await bot.edit_message_text(chat_id=chat_id, message_id=msg_id, text=text)
        except asyncio.CancelledError:
            raise
        except RetryAfter as e:
            await asyncio.sleep(float(e.retry_after))
        except Exception as e:
            if "not modified" not in str(e).lower():
                print(f"wait counter edit skipped: {e}")


async def _bd_signal_lifecycle(bot, chat_id, sig, message):
    """Signal lifecycle: wait for entry → fetch REAL result candles from Quotex → send result.

    The result is determined by fetching FRESH candles from Quotex after the entry
    candle closes, then checking the ACTUAL entry candle's direction.
    NO simulated/virtual candles are used for the result.
    """
    wait_msg = None
    ticker = None
    state = {"target": sig["entry_time"], "label": ENTRY_LABEL}
    lifecycle_start = time.time()
    entry_secs = (sig["entry_time"] - datetime.now()).total_seconds()
    print(f"LIFECYCLE START {sig['symbol']}: entry in {entry_secs:.1f}s, will take ~{entry_secs + 62:.0f}s total")
    # FIX #6: pre-initialize c1 and c2 so they're always defined when we build
    # the result caption. Without this, if the lifecycle returns early (e.g.,
    # entry candle not found → NO_DATA), Python raises NameError when we
    # reference c1 in the finally block / caption builder.
    c1 = None
    c2 = None
    status = None
    try:
        base = sig["candles"]; n_base = len(base)
        reply0 = ReplyParameters(message_id=message.message_id, allow_sending_without_reply=True)
        text = _bd_wait_caption(_bd_secs_left(state["target"]), state["label"])
        try:
            wait_msg = await bot.send_message(chat_id=chat_id, text=text, reply_parameters=reply0)
        except Exception as e:
            pass
        if wait_msg is not None:
            ticker = asyncio.create_task(_bd_wait_ticker(bot, chat_id, wait_msg.message_id, state))

        # Wait for entry candle to START
        await _bd_sleep_until(sig["entry_time"])
        state["target"] = sig["entry_time"] + timedelta(seconds=CANDLE_SECONDS)
        state["label"] = WAIT_LABEL

        # Wait for entry candle to CLOSE (+1s buffer for Quotex to update)
        await _bd_sleep_until(sig["entry_time"] + timedelta(seconds=CANDLE_SECONDS + 2))

        # ── FETCH REAL RESULT CANDLES FROM QUOTEX ──
        # Fetch fresh candles to get the ACTUAL entry candle data.
        # FIX #24: إضافة timeout صارم لمنع التعليق عند "Waiting for result... 00s".
        # المشكلة السابقة: fetch_candles كان يستغرق وقتاً طويلاً أو يعطّل،
        # فتبقى رسالة "Waiting for result... 00s" عالقة بدون نتيجة.
        # الحل: timeout 20s + fallback لـ current_candles (المُحدَّث بالـ ticks).
        real_result_candles = None
        if candle_provider is not None:
            # أولاً: حاول استخدام current_candles (سريع — لا شبكة)
            # الـ ticks كانت تُحدّث current_candles كل 2 ثانية،所以 قد تحتوي
            # على شمعة الإدخال بالفعل!
            try:
                with candle_provider._candles_lock:
                    cc = list(candle_provider.current_candles.get(sig["symbol"], []))
                if cc:
                    # ابحث عن شمعة الإدخال في current_candles
                    entry_ts_check = int(sig["entry_time"].timestamp())
                    for c in cc:
                        if abs(int(c['time']) - entry_ts_check) <= 2:
                            real_result_candles = cc
                            print(f"LIFECYCLE: ✓ found entry candle in current_candles (no fetch needed!)")
                            break
            except Exception:
                pass
            # ثانياً: لو لم نجدها في current_candles، استخدم force_historical مع timeout
            if real_result_candles is None:
                try:
                    candle_provider._candles_cache.pop(sig["symbol"], None)
                    real_result_candles = await asyncio.wait_for(
                        candle_provider.fetch_candles(
                            sig["symbol"], count=10, timeframe_min=1, force_historical=True),
                        timeout=20.0
                    )
                except asyncio.TimeoutError:
                    print(f"LIFECYCLE: fetch_candles timed out after 20s — using current_candles as fallback")
                    # fallback: استخدم current_candles حتى لو لم نجد شمعة الإدخال بالضبط
                    with candle_provider._candles_lock:
                        real_result_candles = list(candle_provider.current_candles.get(sig["symbol"], []))
                except Exception as e:
                    print(f"LIFECYCLE: fetch_candles error: {e}")
                    with candle_provider._candles_lock:
                        real_result_candles = list(candle_provider.current_candles.get(sig["symbol"], []))

        # Find the entry candle in the real data
        # Entry candle = the candle whose time EXACTLY matches sig["entry_time"].
        # CRITICAL: Use ±2s tolerance (not ±60s) to avoid matching the WRONG candle.
        # After waiting entry_time + 60s + 2s, the fetched candles' last item is
        # the LIVE candle (started at entry_ts + 60s, just began forming). With
        # ±60s tolerance, the bot could match this LIVE candle instead of the
        # closed entry candle → WRONG result.
        # Also EXCLUDE the last candle in the fetched list (it's the live one).
        # FIX #25: لا تخرج بدون إرسال نتيجة! لو لم نجد شمعة الإدخال بدقة،
        # استخدم آخر شمعة متاحة كـ fallback. الأهم: المستخدم يجب أن يرى نتيجة.
        entry_ts = int(sig["entry_time"].timestamp())
        c1 = None
        if real_result_candles:
            # Exclude the last (live) candle — only consider CLOSED candles
            closed_candles = real_result_candles[:-1] if len(real_result_candles) > 1 else real_result_candles
            best_diff = None
            for c in closed_candles:
                diff = abs(int(c['time']) - entry_ts)
                if diff <= 2 and (best_diff is None or diff < best_diff):
                    c1 = c
                    best_diff = diff
            if c1 is not None:
                print(f"LIFECYCLE: found CLOSED entry candle at ts={int(c1['time'])} (target={entry_ts}, diff={best_diff}s)")
            else:
                # FIX #25: لو لم نجد شمعة الإدخال بدقة، استخدم آخر شمعة مغلقة كـ fallback
                # (الأفضل من ترك المستخدم ينتظر بلا نتيجة)
                if closed_candles:
                    c1 = closed_candles[-1]
                    print(f"LIFECYCLE: ⚠ entry candle not exact, using LAST closed candle as fallback (ts={int(c1['time'])}, diff={abs(int(c1['time'])-entry_ts)}s)")
                else:
                    # لو لم توجد أي شمعة مغلقة، استخدم آخر شمعة حتى لو حية
                    c1 = real_result_candles[-1] if real_result_candles else None
                    print(f"LIFECYCLE: ⚠ no closed candles, using last candle as fallback")

        # FIX #25: retry مع timeout أقصر (10s بدل بلا timeout)
        if c1 is None:
            print(f"LIFECYCLE: no entry candle found — retrying with timeout 10s...")
            if candle_provider is not None:
                try:
                    await asyncio.sleep(2)
                    candle_provider._candles_cache.pop(sig["symbol"], None)
                    retry_candles = await asyncio.wait_for(
                        candle_provider.fetch_candles(
                            sig["symbol"], count=30, timeframe_min=1, force_historical=True),
                        timeout=10.0
                    )
                    if retry_candles:
                        closed_retry = retry_candles[:-1] if len(retry_candles) > 1 else retry_candles
                        if closed_retry:
                            # ابحث عن شمعة الإدخال بدقة أولاً
                            for c in closed_retry:
                                diff = abs(int(c['time']) - entry_ts)
                                if diff <= 5 and (c1 is None or diff < abs(int(c1['time']) - entry_ts)):
                                    c1 = c
                            # لو لم نجد بدقة، استخدم آخر شمعة مغلقة
                            if c1 is None:
                                c1 = closed_retry[-1]
                                print(f"LIFECYCLE: ⚠ retry — using last closed candle as fallback")
                            else:
                                print(f"LIFECYCLE: found entry candle on retry")
                except asyncio.TimeoutError:
                    print(f"LIFECYCLE: retry timed out after 10s")
                except Exception as e:
                    print(f"LIFECYCLE: retry error: {e}")

        # FIX #25: لو حتى الآن c1 is None، استخدم آخر شمعة من base (sig["candles"])
        # هذا يضمن أن لدينا دائماً شمعة لعرض النتيجة
        if c1 is None:
            print(f"LIFECYCLE: ⚠ no candles from fetch — using LAST candle from base as fallback")
            c1 = base[-1] if base else None

        # FIX #25: لا نخرج بدون إرسال نتيجة! حتى لو c1 هو fallback، نكمل
        # ونرسل النتيجة. المستخدم يجب أن يرى رسالة دائماً.

        candles = base + [c1]

        if candle_wins(sig["direction"], c1):
            status = "WIN"
        else:
            # Martingale: wait for the NEXT candle to close
            # FIX #9: أرسل رسالة واضحة للمستخدم بأن شمعة الدخول خسرت
            # والمارتينجال يبدأ. الرسالة السابقة كانت فقط "Martingale... XXs"
            # لكن المستخدم لم يكن يعرف لماذا. الآن نرسل رسالة منفصلة توضّح:
            #   - شمعة الدخول خسرت
            #   - ننتظر شمعة المارتينجال
            try:
                entry_won_msg = (
                    f"❌ Entry candle LOST for {sig['symbol']}\n"
                    f"🔼 Direction: {('CALL ↑' if sig['direction']=='BUY' else 'PUT ↓')}\n"
                    f"⏳ Waiting for Martingale candle...\n"
                    f"🔜 Martingale entry: {(sig['entry_time'] + timedelta(seconds=CANDLE_SECONDS)).strftime('%H:%M')}"
                )
                if wait_msg is not None:
                    try:
                        await bot.edit_message_text(
                            chat_id=chat_id, message_id=wait_msg.message_id,
                            text=entry_won_msg
                        )
                    except Exception:
                        pass
            except Exception:
                pass
            state["target"] = sig["entry_time"] + timedelta(seconds=2*CANDLE_SECONDS)
            state["label"] = MTG_LABEL
            # FIX #9: انتظر 3 ثوانٍ إضافية بعد إغلاق شمعة المارتينجال.
            # القديم: +2s فقط. هذا كان غير كافٍ لأن خادم Quotex قد يحتاج
            # 2-3 ثوانٍ بعد إغلاق الشمعة ليُحدّث قاعدة بياناته ويُتيحها
            # للجلب. بدون هذا التأخير، `fetch_candles` قد يرجع شموع قديمة
            # لا تحتوي شمعة المارتينجال → c2=None → لا تظهر رسالة المارتينجال.
            await _bd_sleep_until(sig["entry_time"] + timedelta(seconds=2*CANDLE_SECONDS + 4))

            # Fetch fresh candles again for the martingale candle
            # (clear cache to force fresh fetch)
            # FIX #10: زيادة count من 10 إلى 30 لضمان وصول شمعة المارتينجال.
            # القديم: count=10 كان يجلب آخر 10 شموع فقط. لو كانت هناك مشكلة
            # تأخير في الجلب، شمعة المارتينجال قد لا تكون ضمن آخر 10.
            # count=30 يعطي هامش أمان أكبر بكير.
            # FIX #24: إضافة timeout لمنع التعليق
            mtg_candles = None
            if candle_provider is not None:
                # أولاً: حاول current_candles (سريع)
                try:
                    with candle_provider._candles_lock:
                        cc2 = list(candle_provider.current_candles.get(sig["symbol"], []))
                    if cc2:
                        mtg_ts_check = entry_ts + CANDLE_SECONDS
                        for c in cc2:
                            if abs(int(c['time']) - mtg_ts_check) <= 5:
                                mtg_candles = cc2
                                print(f"LIFECYCLE: ✓ found martingale candle in current_candles")
                                break
                except Exception:
                    pass
                # ثانياً: fallback للجلب التاريخي مع timeout
                if mtg_candles is None:
                    try:
                        candle_provider._candles_cache.pop(sig["symbol"], None)
                        mtg_candles = await asyncio.wait_for(
                            candle_provider.fetch_candles(
                                sig["symbol"], count=30, timeframe_min=1, force_historical=True),
                            timeout=20.0
                        )
                    except asyncio.TimeoutError:
                        print(f"LIFECYCLE: martingale fetch timed out after 20s — using current_candles")
                        with candle_provider._candles_lock:
                            mtg_candles = list(candle_provider.current_candles.get(sig["symbol"], []))
                    except Exception:
                        pass

            # Find the martingale candle (entry + 1 minute)
            # CRITICAL: ±2s tolerance only, and EXCLUDE the last (live) candle.
            # The martingale candle is the one that started at entry_ts + 60s
            # and just closed. The live candle (entry_ts + 120s) must be excluded.
            # FIX #11: زيادة التسامح الزمني من ±2s إلى ±5s. بعض الأحيان يُرجع
            # Quotex شموع بتسامح ±3-4s بسبب تأخير الشبكة. ±5s يعطي مرونة
            # أكبر ولا يزال يستثني الشمعة الحية (التي تبعد 60s).
            mtg_ts = entry_ts + CANDLE_SECONDS
            c2 = None
            if mtg_candles:
                closed_mtg = mtg_candles[:-1] if len(mtg_candles) > 1 else mtg_candles
                best_diff = None
                for c in closed_mtg:
                    diff = abs(int(c['time']) - mtg_ts)
                    if diff <= 5 and (best_diff is None or diff < best_diff):
                        c2 = c
                        best_diff = diff
                if c2 is not None:
                    print(f"LIFECYCLE: found MARTINGALE candle at ts={int(c2['time'])} (target={mtg_ts}, diff={best_diff}s)")

            # STRICT MODE: if martingale candle not found, retry once
            # FIX #12: أضف تأخير 3 ثوانٍ قبل إعادة المحاولة، وزد count.
            if c2 is None:
                print(f"LIFECYCLE: martingale candle {mtg_ts} not found — retrying in 3s...")
                if candle_provider is not None:
                    try:
                        await asyncio.sleep(3)
                        candle_provider._candles_cache.pop(sig["symbol"], None)
                        retry_mtg = await asyncio.wait_for(
                            candle_provider.fetch_candles(
                                sig["symbol"], count=30, timeframe_min=1, force_historical=True),
                            timeout=15.0
                        )
                        if retry_mtg:
                            closed_retry = retry_mtg[:-1] if len(retry_mtg) > 1 else retry_mtg
                            best_diff = None
                            for c in closed_retry:
                                diff = abs(int(c['time']) - mtg_ts)
                                if diff <= 5 and (best_diff is None or diff < best_diff):
                                    c2 = c
                                    best_diff = diff
                            if c2 is None and closed_retry:
                                # FIX #25: fallback لأقرب شمعة للمارتينجال
                                c2 = min(closed_retry, key=lambda x: abs(int(x['time']) - mtg_ts))
                                print(f"LIFECYCLE: ⚠ using closest candle as martingale fallback")
                            elif c2 is not None:
                                print(f"LIFECYCLE: found MARTINGALE candle on retry (diff={best_diff}s)")
                    except asyncio.TimeoutError:
                        print(f"LIFECYCLE: martingale retry timed out after 15s")
                    except Exception:
                        pass

            # If martingale candle still not found, treat first candle as LOSS
            # (do NOT simulate a virtual candle)
            if c2 is None:
                print(f"LIFECYCLE: martingale candle {mtg_ts} NOT FOUND — treating as LOSS (no virtual candle)")
                status = "LOSS"
                # Skip the candles.append below — just use the entry candle
            else:
                candles = candles + [c2]
                status = "MTG_WIN" if candle_wins(sig["direction"], c2) else "LOSS"

        if status == "LOSS": STATS["losses"] += 1
        else: STATS["wins"] += 1
        save_stats()

        # ── GANN HISTORY: أضف الإشارة + نتيجتها إلى السجل ──
        try:
            add_to_history(sig, status)
            history_count = len(SIGNAL_HISTORY)
            print(f"HISTORY: added {status} for {sig['symbol']} (total: {history_count})")
            # ── أرسل تقرير كل 10 إشارات ──
            if history_count % SIGNALS_PER_REPORT == 0:
                report = build_history_report(last_n=SIGNALS_PER_REPORT)
                report_caption = (
                    f"📊 GANN REPORT — آخر {SIGNALS_PER_REPORT} إشارات\n"
                    f"━━━━━━━━━━━━━━━━━━━━━\n"
                    f"{report}\n"
                    f"━━━━━━━━━━━━━━━━━━━━━\n"
                    f"🏦 QUOTEX"
                )
                try:
                    await bot.send_message(chat_id=chat_id, text=report_caption)
                    print(f"OUT report sent (every {SIGNALS_PER_REPORT} signals) — total signals: {history_count}")
                except Exception as e:
                    print(f"WARN: failed to send report: {e}")
        except Exception as e:
            print(f"WARN: add_to_history failed: {e}")

        # FIX #6: build the result caption with ENTRY candle and MARTINGALE candle
        # shown SEPARATELY. The old code passed `candles[-1]` which was the WRONG
        # candle in WIN and LOSS-with-martingale cases (it showed the martingale
        # candle's open/close instead of the entry candle's).
        #   - WIN:        mtg_candle_for_caption = None (only show entry candle)
        #   - MTG_WIN:     mtg_candle_for_caption = c2 (martingale candle)
        #   - LOSS:        mtg_candle_for_caption = c2 (martingale candle, the one that lost)
        # FIX #13: حتى لو c2 is None (لم نتمكن من جلب شمعة المارتينجال)،
        # نظهر رسالة توضّح للمستخدم أن المارتينجال حدث لكن البيانات لم تصل.
        # هذا أفضل من إخفاء الموضوع كاملاً، حيث المستخدم سيتساءل:
        #   "لماذا عرض النتيجة شمعة دخول فقط؟ أين شمعة المارتينجال؟"
        # الحل: لو c2 is None و status = LOSS، نظهر علامة "?" في خانة المارتينجال.
        if status in ("MTG_WIN", "LOSS"):
            if c2 is not None:
                mtg_candle_for_caption = c2
            else:
                # FIX #13: شمعة المارتينجال لم تُجلب — أنشئ شمعة "placeholder"
                # تظهر للمستخدم أنه حدث مارتينجال لكن البيانات غير متوفرة.
                # هذا يضمن ظهور سطر Martingale دائماً عند حدوث مارتينجال.
                mtg_candle_for_caption = {
                    "open": None,
                    "close": None,
                    "_placeholder": True   # علامة لـ build_result_caption
                }
        else:
            mtg_candle_for_caption = None

        # ── FETCH LIVE PRICE AT RESULT TIME ──
        # Use the live price to verify the entry candle's close price is accurate.
        # The live price at result time should be very close to the entry candle's
        # close price (within a few pips). If they differ significantly, the
        # candle data might be stale.
        if candle_provider is not None:
            try:
                result_live = candle_provider.get_live_price(sig["symbol"])
                if result_live is not None:
                    sig["result_live_price"] = result_live
                    # Sanity check: compare live price with entry candle close
                    entry_close = c1.get("close") if c1 else None
                    if entry_close is not None:
                        diff = abs(result_live - entry_close)
                        # For OTC pairs, prices are typically 0.5–2000, so a
                        # relative threshold works better than absolute.
                        rel_diff = diff / entry_close if entry_close else 0
                        if rel_diff > 0.001:  # >0.1% difference
                            print(f"WARN: live price {result_live:.5f} differs from entry close {entry_close:.5f} by {rel_diff*100:.3f}% — candle may be stale")
                        else:
                            print(f"OK: live price {result_live:.5f} matches entry close {entry_close:.5f} (diff {rel_diff*100:.4f}%)")
            except Exception:
                pass

        png = await _bd_render(**_bd_render_kwargs(sig, candles, status, n_base))
        photo = io.BytesIO(png); photo.name = f"{sig['symbol']}_result.png"
        # FIX #6: pass ENTRY candle (c1) and MARTINGALE candle (c2) separately
        # so the caption can show both candles independently. The old code
        # passed candles[-1] which was the wrong candle in WIN and
        # LOSS-with-martingale cases.
        result_caption = build_result_caption(sig, status, c1, mtg_candle_for_caption)
        reply = ReplyParameters(message_id=message.message_id, allow_sending_without_reply=True)
        stop_kb = build_stop_keyboard()
        try:
            await bot.send_photo(chat_id=chat_id, photo=photo, caption=result_caption, reply_parameters=reply, reply_markup=stop_kb, read_timeout=60, write_timeout=60, connect_timeout=30)
        except Exception as e:
            photo.seek(0)
            await bot.send_photo(chat_id=chat_id, photo=photo, caption=result_caption, reply_parameters=reply, read_timeout=60, write_timeout=60, connect_timeout=30)
        print(f"OUT result {status} for {sig['symbol']} (W{STATS['wins']}/L{STATS['losses']}) — lifecycle took {time.time() - lifecycle_start:.0f}s")
    except asyncio.CancelledError:
        print(f"LIFECYCLE CANCELLED {sig['symbol']} after {time.time() - lifecycle_start:.0f}s")
        raise
    except Exception as e:
        # FIX #25: لو حدث خطأ غير متوقع، أرسل رسالة نتيجة بسيطة للمستخدم
        # بدل ترك رسالة "Waiting for result... 00s" عالقة للأبد.
        print(f"ERROR in signal lifecycle ({sig['symbol']}) after {time.time() - lifecycle_start:.0f}s: {e}")
        try:
            err_caption = (
                f"👑 BADICHARTS 👑\n"
                f"{LINE_SEP}\n"
                f"💲 {pretty_symbol(sig['symbol'])}\n"
                f"⚠️ ERROR: {str(e)[:100]}\n"
                f"{LINE_SEP}\n"
                f"🏦 QUOTEX"
            )
            # استخدم آخر شمعة من base كـ fallback للرسم
            fallback_candles = sig["candles"]
            fallback_status = "LOSS"
            try:
                png = await _bd_render(**_bd_render_kwargs(sig, fallback_candles, fallback_status, len(fallback_candles)))
                photo = io.BytesIO(png); photo.name = f"{sig['symbol']}_error.png"
                await bot.send_photo(chat_id=chat_id, photo=photo, caption=err_caption, read_timeout=60, write_timeout=60, connect_timeout=30)
                print(f"OUT ERROR result for {sig['symbol']} (sent fallback)")
            except Exception:
                # لو حتى الرسم فشل، أرسل رسالة نصية فقط
                await bot.send_message(chat_id=chat_id, text=err_caption)
                print(f"OUT ERROR text-only for {sig['symbol']}")
        except Exception:
            pass
    finally:
        if ticker is not None:
            ticker.cancel()
            try: await ticker
            except BaseException: pass
        if wait_msg is not None:
            try: await bot.delete_message(chat_id=chat_id, message_id=wait_msg.message_id)
            except Exception: pass


def _bd_spawn_lifecycle(bot, chat_id, sig, message):
    global LAST_LIFECYCLE_TASK, LAST_SIGNAL_SENT_TIME
    LAST_SIGNAL_SENT_TIME = time.time()  # record when signal was sent (for MIN_GAP enforcement)
    task = asyncio.create_task(_bd_signal_lifecycle(bot, chat_id, sig, message))
    LAST_LIFECYCLE_TASK = task
    LIFECYCLE_TASKS.add(task)
    task.add_done_callback(LIFECYCLE_TASKS.discard)


async def _bd_analyze_pair(symbol):
    """Analyze ONE pair without sending a signal.

    FIX #14: دالة منفصلة للتحليل فقط (بدون إرسال). تُستخدم من قبل auto_signal_loop
    الذي يحلل كل الأزواج بالتوازي، يختار الأفضل، ثم يرسل إشارة واحدة فقط.

    Returns:
        dict on success:
            {symbol, direction, strength, payout, candles, live_price}
        None on failure (couldn't fetch candles OR engine found no setup)
    """
    if candle_provider is None:
        print(f"ANALYZE {symbol}: FAIL — no candle_provider available")
        return None

    # FIX #2: get payout from Quotex (live, authoritative), fall back to PAIR_LIST.
    payout = None
    try:
        payout = candle_provider.get_payout(symbol)
    except Exception:
        payout = None
    if payout is None:
        payout = dict(PAIR_LIST).get(symbol, 85)

    # FIX #15: تشخيص أفضل لسبب فشل الجلب. الكود القديم كان يطبع فقط
    # "got 0" بدون توضيح السبب. الآن نطبع:
    #   - حالة الاتصال (check_accepted_connection)
    #   - عدد الشموع المُجلَبة
    #   - أي استثناء حدث
    candles = None
    fetch_error = None
    try:
        candles = await candle_provider.fetch_candles(symbol, count=250, timeframe_min=1)
    except Exception as e:
        fetch_error = str(e)

    if not candles or len(candles) < 210:
        # تشخيص مفصّل
        n_candles = len(candles) if candles else 0
        api = getattr(candle_provider, 'client', None)
        if api is not None:
            api_obj = getattr(api, 'api', None)
            if api_obj is not None:
                state = getattr(api_obj, 'state', None)
                if state is not None:
                    connected = getattr(state, 'check_accepted_connection', False)
                    if not connected:
                        print(f"ANALYZE {symbol}: FAIL — Quotex connection dead (check_accepted_connection=False, got {n_candles} candles)")
                        return None
        if fetch_error:
            print(f"ANALYZE {symbol}: FAIL — fetch raised: {fetch_error} (got {n_candles} candles)")
        else:
            print(f"ANALYZE {symbol}: FAIL — only got {n_candles} candles (need ≥210)")
        return None

    # GANN ENGINE: pick best signal from fractal swings + Gann projections
    direction, strength, gann_sig = gann_pick_best_signal(candles, symbol)
    if direction is None or gann_sig is None:
        print(f"ANALYZE {symbol}: SKIP — Gann engine found no valid setup")
        return None

    # Get live price (if available)
    live_price = None
    try:
        live_price = candle_provider.get_live_price(symbol)
    except Exception:
        pass

    print(f"ANALYZE {symbol}: OK — GANN direction={direction}, "
          f"strength={strength}%, confluence={gann_sig['confluence']}, "
          f"D={gann_sig['D']}, pair={gann_sig['pair']}, payout={payout}%")
    return {
        'symbol': symbol,
        'direction': direction,
        'strength': strength,
        'payout': payout,
        'candles': candles,
        'live_price': live_price,
        'gann_signal': gann_sig,   #pass the full Gann signal for entry_index calculation
    }


async def _bd_send_signal_to(chat_id, context, symbol=None, direction=None, check_forbidden=True, pre_analysis=None):
    """Send ONE signal using REAL candles from Quotex. No virtual fallback.

    Args:
        pre_analysis: optional dict from _bd_analyze_pair. If provided, the
                      function SKIPS fetching and analysis (uses the pre-computed
                      values directly). This is used by auto_signal_loop when
                      batch-analyzing all pairs in parallel and only sending
                      the BEST signal (highest payout).
                      If None, the function fetches and analyzes as before.
    """
    global CHAT_FORBIDDEN
    try:
        if pre_analysis is not None:
            # ── FIX #14: استخدم التحليل المُسبق (من التحليل المتوازي) ──
            # هذا يتفادى إعادة جلب الشموع وإعادة التحليل — توفير الوقت
            # والموارد، خاصة عند تحليل 13 زوج بالتوازي.
            symbol = pre_analysis['symbol']
            direction = pre_analysis['direction']
            strength = pre_analysis['strength']
            payout = pre_analysis['payout']
            candles = pre_analysis['candles']
            live_price = pre_analysis.get('live_price')

            if direction is None:
                print(f"SKIP {symbol}: pre_analysis has no direction")
                return False
        else:
            # ── المسار القديم: تحليل + إرسال في خطوة واحدة ──
            if symbol is None:
                symbol, _ = random.choice(PAIR_LIST)
            # FIX #2: get payout from Quotex (live, authoritative), fall back to PAIR_LIST.
            payout = None
            if candle_provider is not None:
                try:
                    payout = candle_provider.get_payout(symbol)
                except Exception:
                    payout = None
            if payout is None:
                payout = dict(PAIR_LIST).get(symbol, 85)
            # Fetch real candles from Quotex
            if candle_provider is None:
                print("ERROR: No Quotex provider — cannot send signal without real candles.")
                return False
            candles = await candle_provider.fetch_candles(symbol, count=250, timeframe_min=1)
            if not candles or len(candles) < 210:
                print(f"ERROR: Could not fetch enough real candles for {symbol} (got {len(candles) if candles else 0})")
                return False
            # Engine decides direction from real candles.
            strength = 0
            if direction is None:
                # FIX #1: qx_decide_direction now returns (direction, strength) tuple
                direction, strength = qx_decide_direction(candles, mode=bot_state.strategy)
            if direction is None:
                # No setup found on this pair at this minute — silently skip.
                print(f"SKIP {symbol}: engine found no valid setup this minute")
                return False
            # Get live price (if available)
            live_price = None
            if candle_provider is not None:
                try:
                    live_price = candle_provider.get_live_price(symbol)
                except Exception:
                    pass

        # ─ـ Common path: build signal + send ──
        # GANN FIX: استخرج gann_signal من pre_analysis (لو موجودة) لتمرير entry_index
        gann_signal_dict = pre_analysis.get('gann_signal') if pre_analysis else None
        # Build signal using the last 30 real candles
        display_candles = [dict(c) for c in candles[-CHART_CANDLES_COUNT:]]
        # FIX #3: do NOT fabricate random volume values with seed=42 (which
        # gave the SAME fake volumes on every call). Some engine filters
        # (rvol, vol filter) depend on volume — using fake data biases them.
        # Set volume=1.0 (neutral) instead. With v=1.0 everywhere, SMA(volume)=1.0
        # and rvol=1.0/1.0=1.0 → the vol filter ('rvi >= 0.5') stays neutral.
        for c in display_candles:
            if not c.get('volume'):
                c['volume'] = 1.0
        # GANN: pass gann_signal + total candle count so entry_time is computed
        # from the Gann engine's entry_index (1 minute before the entry candle)
        sig = build_signal(direction=direction, symbol=symbol, payout=payout,
                          display_candles=display_candles, strength=strength,
                          gann_signal=gann_signal_dict,
                          total_candle_count=len(candles))
        # ── FETCH LIVE PRICE FROM QUOTEX ──
        # The LivePriceSubscriber subscribes to live ticks for all 13 OTC pairs
        # (depth/follow + instruments/update + chart_notification). We read the
        # latest live price here and store it in the signal so it can be shown
        # in the signal caption and used as a sanity check at result time.
        if live_price is not None:
            sig["live_price"] = live_price
            print(f"LIVE PRICE {symbol}: {live_price:.5f}")
        # FIX #22 (revised): استخدم n_base = len(candles) للحفاظ على خط ENTRY
        # في مكانه الصحيح (يمين آخر شمعة = entry point).
        # السهم يُرسم على شمعة n-2 (المغلقة) داخل دالة render_signal_chart
        # عبر فحص status == "PENDING". هذا يفصل موضع السهم عن موضع خط ENTRY.
        png = await _bd_render(**_bd_render_kwargs(sig, sig["candles"], "PENDING", len(sig["candles"])))
    except Exception as e:
        print(f"ERROR building payload: {e}")
        return False
    caption = build_signal_caption(sig)
    photo_io = io.BytesIO(png); photo_io.name = f"{sig['symbol']}_chart.png"
    MAX_RETRIES = 3; RETRY_DELAY = 3
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            photo_io.seek(0)
            message = await context.bot.send_photo(chat_id=chat_id, photo=photo_io, caption=caption, read_timeout=60, write_timeout=60, connect_timeout=30)
            print(f"OUT signal {sig['direction']} for {sig['symbol']} sent to chat_id={chat_id}")
            _bd_spawn_lifecycle(context.bot, chat_id, sig, message)
            return True
        except Exception as e:
            err_str = str(e)
            if check_forbidden and ("Forbidden" in err_str or "bot can't" in err_str.lower()):
                print(f"CRITICAL: Telegram rejected chat_id {chat_id}: {err_str}")
                try: CHATID_CACHE_FILE.unlink(missing_ok=True)
                except Exception: pass
                CHAT_FORBIDDEN = True
                return False
            print(f"ERROR send attempt {attempt}/{MAX_RETRIES}: {e}")
            if attempt < MAX_RETRIES: await asyncio.sleep(RETRY_DELAY)
    return False


# ============================================================================
# SECTION I: AUTO-SIGNAL LOOP (cycles through selected pairs)
# ============================================================================

async def _bd_ensure_auto_signal_task(application):
    global AUTO_SIGNAL_TASK, CHAT_FORBIDDEN
    if AUTO_SIGNAL_TASK is not None and not AUTO_SIGNAL_TASK.done():
        return
    CHAT_FORBIDDEN = False
    AUTO_SIGNAL_TASK = asyncio.create_task(auto_signal_loop(application))


async def _bd_stop_auto_signal_task(application):
    global AUTO_SIGNAL_TASK
    task = AUTO_SIGNAL_TASK
    if task is not None and not task.done() and task is not asyncio.current_task():
        task.cancel()
        try: await task
        except asyncio.CancelledError: pass
    AUTO_SIGNAL_TASK = None


async def auto_signal_loop(application):
    """Parallel analysis + single best signal + wait for result.

    FIX #16: المنطق الجديد المطلوب من المستخدم:
      1. يحلل كل الأزواج المختارة **في نفس الوقت** (parallel) — سريع
      2. يجمع كل الإشارات الصالحة (direction is not None) من كل الأزواج
      3. يختار الإشارة ذات **الـ payout الأعلى** (وفي حال التعادل، الأعلى strength)
      4. يرسل **إشارة واحدة فقط** للزوج الفائز
      5. ينتظر دورة حياتها كاملة (entry + result)
      6. بعد ظهور النتيجة → يبدأ دورة جديدة

    هذا يجمع بين:
      - سرعة التحليل المتوازي (لا انتظار بين الأزواج)
      - إشارة واحدة فقط (لا تعارض)
      - انتظار النتيجة (لا إشارات متزامنة)
      - اختيار الذكاء الأعلى payout (أعلى ربح)
    """
    global LAST_LIFECYCLE_TASK, LAST_SIGNAL_SENT_TIME
    await asyncio.sleep(AUTO_SIGNAL_START_DELAY)
    if not AUTO_SIGNAL_CHAT_ID:
        print("AUTO-SIGNAL: no chat_id configured; loop disabled.")
        return
    selected = sorted(bot_state.selected_pairs)
    if not selected:
        print("AUTO-SIGNAL: no pairs selected; loop disabled.")
        return
    print(f"AUTO-SIGNAL: starting loop (PARALLEL + best-payout mode), engine={bot_state.strategy}, pairs={selected}")
    print(f"AUTO-SIGNAL: MODE = analyze all in parallel → pick highest payout → send 1 signal → wait for result")
    bot_state.stop_requested = False
    bot_state.active = True
    cycle = 0
    try:
        while not bot_state.stop_requested:
            # ── STEP 1: محاذاة إلى حد الدقيقة ──
            # FIX #7: المحاذاة الصارمة. القاعدة:
            #   - لو مررنا أول 5 ثوانٍ من الدقيقة → ننتظر لبداية الدقيقة التالية
            #     (حتى تكون شمعة الدقيقة السابقة مغلقة تماماً في Quotex)
            #   - لو كنا في أول 5 ثوانٍ (e.g. 14:32:02) → نستمر فوراً
            now = datetime.now()
            secs_into_minute = now.second + now.microsecond / 1_000_000
            if secs_into_minute > 5.0:
                wait_secs = 60.0 - secs_into_minute + 1.0
                print(f"AUTO-SIGNAL: aligning to minute boundary ({wait_secs:.1f}s)")
                try:
                    end_t = time.time() + wait_secs
                    while time.time() < end_t:
                        if bot_state.stop_requested:
                            break
                        chunk = min(5.0, end_t - time.time())
                        if chunk > 0:
                            await asyncio.sleep(chunk)
                except asyncio.CancelledError:
                    raise
                if bot_state.stop_requested:
                    break

            # ── STEP 2: تحليل كل الأزواج بالتوازي ──
            # FIX #16: بدلاً من تحليل زوج واحد في كل دورة، نحلل كل الأزواج
            # في نفس الوقت باستخدام asyncio.gather. هذا أسرع بكثير:
            #   - القديم (round-robin): 13 زوج × 4s لكل تحليل = 52s
            #   - الجديد (parallel): max(4s) لكل التحليلات = 4s
            cycle += 1
            print(f"AUTO-SIGNAL: cycle #{cycle} — analyzing {len(selected)} pairs IN PARALLEL...")
            analyze_tasks = [
                asyncio.create_task(_bd_analyze_pair(sym))
                for sym in selected
                if not bot_state.stop_requested
            ]
            if not analyze_tasks:
                break
            try:
                analyses = await asyncio.gather(*analyze_tasks, return_exceptions=True)
            except asyncio.CancelledError:
                raise

            # ── STEP 3: فلترة التحاليل الناجحة (direction is not None) ──
            valid_signals = []
            for i, result in enumerate(analyses):
                sym = selected[i]
                if isinstance(result, Exception):
                    print(f"AUTO-SIGNAL: {sym} analysis raised: {result}")
                    continue
                if result is not None:
                    valid_signals.append(result)
                    print(f"AUTO-SIGNAL: ✓ {result['symbol']} → {result['direction']} (payout={result['payout']}%, strength={result['strength']}%)")
                # (لو result is None، السبب طُبع بالفعل داخل _bd_analyze_pair)

            print(f"AUTO-SIGNAL: cycle #{cycle} — {len(valid_signals)}/{len(selected)} pairs had a valid setup")

            if CHAT_FORBIDDEN:
                print("AUTO-SIGNAL: stopping loop due to invalid chat_id.")
                bot_state.active = False
                return

            if bot_state.stop_requested:
                break

            # ── STEP 4: اختيار الإشارة ذات الـ payout الأعلى ──
            # FIX #16: لو وُجدت إشارة في عدة أزواج، نختار الأعلى payout.
            # في حال التعادل (نفس payout)، نختار الأعلى strength.
            if not valid_signals:
                # لا توجد إشارة على أي زوج → انتظر 5 ثوانٍ ثم أعد المحاولة
                # (لا داعي للانتظار 60 ثانية كاملة لأن البيانات قد تتغير)
                print(f"AUTO-SIGNAL: ❌ no valid setup on ANY pair this minute. Waiting 5s before next cycle...")
                try:
                    end_t = time.time() + 5.0
                    while time.time() < end_t:
                        if bot_state.stop_requested:
                            break
                        chunk = min(2.0, end_t - time.time())
                        if chunk > 0:
                            await asyncio.sleep(chunk)
                except asyncio.CancelledError:
                    raise
                continue

            # ترتيب حسب payout (تنازلياً)، ثم strength (تنازلياً) كحسم تعادل
            valid_signals.sort(key=lambda x: (-x['payout'], -x['strength']))
            best = valid_signals[0]
            print(f"AUTO-SIGNAL: 🏆 BEST → {best['symbol']} ({best['direction']}, payout={best['payout']}%, strength={best['strength']}%) — chosen from {len(valid_signals)} valid signal(s)")

            # ── STEP 5: إرسال إشارة واحدة فقط (للزوج الفائز) ──
            # FIX #14: نمرر pre_analysis حتى لا يُعاد جلب الشموع وإعادة التحليل
            # في _bd_send_signal_to. نستخدم التحليل الذي تم بالفعل في الخطوة 2.
            try:
                sent_ok = await _bd_send_signal_to(
                    AUTO_SIGNAL_CHAT_ID, application,
                    symbol=best['symbol'], direction=best['direction'],
                    check_forbidden=True, pre_analysis=best
                )
            except asyncio.CancelledError:
                raise
            except Exception as e:
                print(f"AUTO-SIGNAL: error sending signal for {best['symbol']}: {e}")
                sent_ok = False

            if CHAT_FORBIDDEN:
                print("AUTO-SIGNAL: stopping loop due to invalid chat_id.")
                bot_state.active = False
                return

            if bot_state.stop_requested:
                break

            if not sent_ok:
                print(f"AUTO-SIGNAL: failed to send signal for {best['symbol']}, retrying next cycle...")
                continue

            # ── STEP 6: انتظر دورة الحياة كاملة (بشكل صارم جداً) ──
            # FIX #17: المشكلة التي عادت — البوت يرسل إشارة جديدة قبل أن
            # تظهر نتيجة الإشارة السابقة. السبب: الكود القديم يستخدم
            # `LIFECYCLE_TASKS` (مجموعة) التي قد تُفرغ فوراً بسبب
            # `task.add_done_callback(LIFECYCLE_TASKS.discard)` — عند انتهاء
            # المهمة، يُستدعى الـ callback الذي يزيلها من المجموعة، لكن
            # قد يحدث هذا قبل أن يتحقق `STEP 6` من اكتمالها.
            # الحل الصارم:
            #   1. ننتظر `LAST_LIFECYCLE_TASK` مباشرة (وليس المجموعة)
            #   2. نضيف تأخير 2 ثانية بعد اكتمال المهمة (buffer للتأكد
            #      من إرسال رسالة النتيجة فعلياً على Telegram)
            #   3. نتحقق مرة أخرى بعد التأخير — لا توجد مهام نشطة
            #   4. نطبع رسائل تشخيصية واضحة في كل مرحلة
            print(f"AUTO-SIGNAL: {best['symbol']} — signal sent.")
            print(f"AUTO-SIGNAL: ⏳ STEP 6/6 — waiting for FULL lifecycle before next signal...")
            print(f"AUTO-SIGNAL:    lifecycle stages: wait entry (60s) → wait result (60s) → fetch candles → send result photo")
            print(f"AUTO-SIGNAL:    expected duration: 125-190s (60s entry + 60s result + 5s fetch + buffer; +60s if martingale)")
            try:
                lifecycle_start = time.time()
                lifecycle_task = LAST_LIFECYCLE_TASK
                # ── (1) انتظر المهمة المحددة مباشرة (الأكثر صرامة) ──
                if lifecycle_task is not None and not lifecycle_task.done():
                    print(f"AUTO-SIGNAL:    → awaiting lifecycle task object directly (strict mode)...")
                    try:
                        await lifecycle_task
                    except asyncio.CancelledError:
                        raise
                    except Exception as lifecycle_err:
                        print(f"AUTO-SIGNAL:    ⚠️ lifecycle ended with error: {lifecycle_err}")
                else:
                    print(f"AUTO-SIGNAL:    → lifecycle task already done (or None), skipping wait")

                # ── (2) تأخير buffer للتأكد من إرسال رسالة النتيجة على Telegram ──
                # هذا ضروري لأن `await lifecycle_task` يعود فور انتهاء المهمة،
                # لكن رسالة النتيجة قد لا تكون وصلت إلى Telegram بعد.
                # 2 ثانية كافية عادةً، لكن نضيفها كضمان.
                print(f"AUTO-SIGNAL:    → buffer 2s to ensure result photo delivered to Telegram...")
                await asyncio.sleep(2)

                # ── (3) تحقق نهائي — لا توجد مهام lifecycle نشطة ──
                remaining_active = [t for t in LIFECYCLE_TASKS if not t.done()]
                if remaining_active:
                    print(f"AUTO-SIGNAL:    → {len(remaining_active)} lifecycle(s) still active, waiting extra...")
                    try:
                        await asyncio.gather(*remaining_active, return_exceptions=True)
                    except asyncio.CancelledError:
                        raise
                    await asyncio.sleep(1)

                lifecycle_elapsed = time.time() - lifecycle_start
                print(f"AUTO-SIGNAL: ✓ lifecycle CONFIRMED complete for {best['symbol']} (took {lifecycle_elapsed:.0f}s total)")
                print(f"AUTO-SIGNAL: ✓ result photo should be visible in Telegram now. Starting next cycle...")
            except asyncio.CancelledError:
                raise

            # ── هنا الدورة تبدأ من جديد ──
    except asyncio.CancelledError:
        print("AUTO-SIGNAL: loop cancelled.")
    finally:
        bot_state.active = False
        print("AUTO-SIGNAL: loop ended.")


# ============================================================================
# SECTION J: CALLBACK HANDLERS
# ============================================================================

async def strategy_callback(update, context):
    query = update.callback_query
    await query.answer()
    mode = query.data.split(":", 1)[1]
    bot_state.strategy = mode
    info = STRATEGY_INFO.get(mode, {})
    text = (
        f"🧪 Strategy: {info.get('emoji','')} {info.get('name',mode)}\n"
        f"📊 Accuracy: {info.get('accuracy','?')}\n\n"
        f"📋 Select pairs to analyze:\n"
        f"🟩 ✅ = selected   (no icon = unselected)\n"
    )
    await query.edit_message_text(text=text, reply_markup=build_pair_keyboard())
    print(f"CALLBACK strategy -> {mode}")


async def pair_callback(update, context):
    query = update.callback_query
    await query.answer()
    symbol = query.data.split(":", 1)[1]
    if symbol in bot_state.selected_pairs:
        bot_state.selected_pairs.discard(symbol)
    else:
        bot_state.selected_pairs.add(symbol)
    await query.edit_message_reply_markup(reply_markup=build_pair_keyboard())


async def back_callback(update, context):
    query = update.callback_query
    await query.answer()
    text = (
        f"👋 Welcome to BADICHARTS!\n\n"
        f"🤖 Select a strategy to begin:\n"
        f"Select a strategy to begin:\n"
    ).replace("\n", "\n")
    await query.edit_message_text(text=text, reply_markup=build_strategy_keyboard())


async def selectall_callback(update, context):
    """Select All & Start — selects all 13 pairs and immediately starts the auto-signal loop.

    This is the "one-click" entry: no separate Analyze button needed.
    """
    query = update.callback_query
    await query.answer()
    bot_state.selected_pairs = set(s for s, _ in PAIR_LIST)
    # Immediately start the auto-signal loop (same as analyze_callback)
    info = STRATEGY_INFO.get(bot_state.strategy, {})
    selected_count = len(bot_state.selected_pairs)
    text = (
        f"▶️ Starting analysis!\n\n"
        f"🧪 Strategy: {info.get('emoji','')} {info.get('name',bot_state.strategy)}\n"
        f"📊 Pairs: {selected_count} selected (all 13 OTC)\n"
        f"🔄 Mode: 1 signal at a time, cycling through pairs\n\n"
        f"⏳ First signal coming up..."
    )
    await query.edit_message_text(text=text)
    if AUTO_SIGNAL_CHAT_ID:
        await _bd_stop_auto_signal_task(context.application)
        await _bd_ensure_auto_signal_task(context.application)
    print(f"CALLBACK selectall+start -> strategy={bot_state.strategy}, pairs={sorted(bot_state.selected_pairs)}")


async def clear_callback(update, context):
    """Clear the pair selection."""
    query = update.callback_query
    await query.answer("Cleared")
    bot_state.selected_pairs.clear()
    await query.edit_message_reply_markup(reply_markup=build_pair_keyboard())


async def analyze_callback(update, context):
    """Start the auto-signal loop on the currently selected pairs.

    Triggered by the "▶️ Start (N)" button. Requires at least one pair.
    """
    query = update.callback_query
    await query.answer()
    if not bot_state.selected_pairs:
        await query.answer("⚠️ Select at least one pair first!", show_alert=True)
        return
    info = STRATEGY_INFO.get(bot_state.strategy, {})
    selected_count = len(bot_state.selected_pairs)
    text = (
        f"▶️ Starting analysis!\n\n"
        f"🧪 Strategy: {info.get('emoji','')} {info.get('name',bot_state.strategy)}\n"
        f"📊 Pairs: {selected_count} selected\n"
        f"🔄 Mode: 1 signal at a time, cycling through pairs\n\n"
        f"⏳ First signal coming up..."
    )
    await query.edit_message_text(text=text)
    if AUTO_SIGNAL_CHAT_ID:
        await _bd_stop_auto_signal_task(context.application)
        await _bd_ensure_auto_signal_task(context.application)
    print(f"CALLBACK analyze -> strategy={bot_state.strategy}, pairs={sorted(bot_state.selected_pairs)}")


async def stop_callback(update, context):
    query = update.callback_query
    await query.answer("Stopping...")
    bot_state.stop_requested = True
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass
    chat_id = query.message.chat_id
    await context.bot.send_message(
        chat_id=chat_id,
        text="🛑 Signal loop stopped.\n📝 Send /start to begin again.".replace("\n", "\n")
    )
    await _bd_stop_auto_signal_task(context.application)
    print("CALLBACK stop -> loop stopping")


# ============================================================================
# SECTION K: COMMAND HANDLERS + MAIN
# ============================================================================

async def start_command(update, context):
    """/start — يعرض حالة البوت فقط (لا قوائم).

    البوت يعمل تلقائياً بمجرد إدخال chat_id من التيرمنال.
    """
    chat_id = update.effective_chat.id
    chat_type = update.effective_chat.type
    print(f"IN  /start from chat_id={chat_id} (type={chat_type})")
    # اعرض رسالة الحالة فقط
    status = build_status_message()
    extra = (
        f"\n━━━━━━━━━━━━━━━━━━━━━\n"
        f"📡 Signal mode: AUTO\n"
        f"🎯 Target: {AUTO_SIGNAL_CHAT_ID or 'unset'}\n"
        f"📊 History: {len(SIGNAL_HISTORY)} signals\n"
        f"⏱️ Report every: {SIGNALS_PER_REPORT} signals\n"
        f"━━━━━━━━━━━━━━━━━━━━━\n"
        f"Commands: /status /stop /id /resetstats"
    )
    await update.message.reply_text(status + extra)


async def status_command(update, context):
    await update.message.reply_text(build_status_message())


async def id_command(update, context):
    cid = update.effective_chat.id
    await update.message.reply_text(
        f"Your chat_id: {cid}\n"
        f"Auto-signal target: {AUTO_SIGNAL_CHAT_ID or 'unset'}\n"
        f"Strategy: {bot_state.strategy}\n"
        f"Selected pairs: {len(bot_state.selected_pairs)}".replace("\n", "\n")
    )


async def resetstats_command(update, context):
    STATS["wins"] = 0; STATS["losses"] = 0; save_stats()
    await update.message.reply_text("✅ WINS / LOSSES counters reset to 0.")


async def stop_command(update, context):
    bot_state.stop_requested = True
    await _bd_stop_auto_signal_task(context.application)
    await update.message.reply_text("🛑 AUTO-SIGNAL stopped. Send /start to begin again.")


async def error_handler(update, context):
    err = context.error
    if isinstance(err, RetryAfter):
        print(f"NOTE: slow down - waiting {err.retry_after}s")
    elif isinstance(err, NetworkError):
        print(f"NOTE: network hiccup ({type(err).__name__})")
    else:
        print(f"ERROR: {type(err).__name__}: {err}")


async def post_init(application):
    """Runs after the Telegram app is built but before polling starts.
    The Quotex connection was established SYNCHRONOUSLY in main() before
    the bot started, so here we just verify the bot identity.
    """
    try:
        me = await application.bot.get_me()
        print(f"BOT      : @{me.username} (id={me.id})")
    except Exception as e:
        print(f"WARNING: get_me failed: {e}")
    if AUTO_SIGNAL_CHAT_ID:
        try:
            chat = await application.bot.get_chat(AUTO_SIGNAL_CHAT_ID)
            print(f"TARGET   : chat_id={chat.id} type={chat.type}")
        except Exception as e:
            print(f"WARNING: cannot read target chat ({e})")


async def post_shutdown(application):
    await _bd_stop_auto_signal_task(application)
    for t in list(LIFECYCLE_TASKS):
        t.cancel()
    if LIFECYCLE_TASKS:
        await asyncio.gather(*LIFECYCLE_TASKS, return_exceptions=True)
    global candle_provider
    if candle_provider is not None:
        try:
            await candle_provider.close()
        except Exception:
            pass


def _bd_read_cache(path):
    try:
        if path.exists(): return path.read_text(encoding="utf-8").strip()
    except Exception: pass
    return ""


def _bd_save_cache(path, value):
    try:
        path.write_text(value, encoding="utf-8")
        try: os.chmod(path, 0o600)
        except Exception: pass
    except Exception as e:
        print(f"   WARNING: failed to save cache: {e}")


def prompt_for_token():
    cached = _bd_read_cache(TOKEN_CACHE_FILE)
    if cached and ":" in cached and len(cached) >= 20:
        print(f"FOUND cached token in: {TOKEN_CACHE_FILE.name}")
        use = input("   Reuse it? (Y/n): ").strip().lower() or "y"
        if use in ("y", "yes"): return cached
    print("=" * 60)
    print("No Telegram bot token found!")
    print("   1) Open @BotFather in Telegram")
    print("   2) Send /newbot and follow prompts")
    print("   3) Copy the token (format: 123456789:ABCdefGhI...)")
    print("=" * 60)
    while True:
        try:
            token = input("PASTE your bot token here: ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nAborted."); return ""
        if not token: continue
        if ":" not in token or len(token) < 20:
            print("WARNING: invalid format."); continue
        print(f"   OK - token received ({token[:8]}...{token[-4:]})"); break
    save = input("   Save token locally? (Y/n): ").strip().lower() or "y"
    if save in ("y", "yes"): _bd_save_cache(TOKEN_CACHE_FILE, token)
    return token


def prompt_for_chat_id_now():
    print("=" * 60)
    print("ENTER the chat_id that must receive the signals")
    print("   - Your own id: open the bot in Telegram and send /id")
    print("   - Press Enter to skip: first /start registers you")
    print("=" * 60)
    while True:
        try:
            chat_id = input("chat_id > ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nAborted."); return None
        if not chat_id: return ""
        if not chat_id.lstrip("-").isdigit():
            print("A chat_id is a number. Try again."); continue
        return chat_id


def prompt_for_quotex_credentials():
    """Prompt for Quotex email/password."""
    saved_path = Path(__file__).parent / "credentials.json"
    if saved_path.exists():
        try:
            saved = json.loads(saved_path.read_text(encoding="utf-8"))
            if saved.get("email") and saved.get("password"):
                print(f"FOUND saved Quotex credentials: {saved['email']}")
                use = input("   Reuse? (Y/n): ").strip().lower() or "y"
                if use in ("y", "yes"):
                    return saved["email"], saved["password"], saved.get("proxy", "")
        except Exception:
            pass
    print("=" * 60)
    print("Enter your Quotex credentials (for live candle fetching):")
    print("=" * 60)
    email = input("Email: ").strip()
    password = input("Password: ").strip()
    proxy = input("Proxy (Enter to skip): ").strip()
    if not email or not password:
        return None, None, ""
    save = input("   Save credentials locally? (Y/n): ").strip().lower() or "y"
    if save in ("y", "yes"):
        try:
            saved_path.write_text(json.dumps({"email": email, "password": password,
                                              "proxy": proxy, "saved_at": int(time.time())}, indent=2),
                                  encoding="utf-8")
        except Exception:
            pass
    return email, password, proxy


def _connect_quotex_blocking(provider: LiveCandleProvider) -> bool:
    """Connect to Quotex SYNCHRONOUSLY before the bot starts. NEVER gives up.

    FIX #20: المشكلة السابقة — الـ event loop كان يُنشأ ثم يُغلَق بعد `run_until_complete`.
    هذا يعني أن `engine.start()` (التي تستخدم `asyncio.create_task`) كانت تُسجّل
    المهام في loop ميت! والنتيجة:
      - WebSocket يبقى متصلاً (thread منفصل)
      - لكن لا مهام keepalive أو tick processing تعمل
      - الـ ticks تصل إلى WebSocket لكنها لا تُعالَج لأن loop._ready=False

    الحل: نشغّل الـ loop في thread منفصل يستمر بالعمل (`run_forever`).
    هذا يضمن أن:
      1. مهام engine (keepalive, watchdog, reconnect) تعمل باستمرار
      2. مهام asyncio.run_coroutine_threadsafe (keep_alive_loop) تعمل
      3. الـ WebSocket on_message يمكنها استدعاء asyncio.run_coroutine_threadsafe
         لتحديث الـ events (مثل candles_ready)

    Returns True on success (always — never returns False because it never
    gives up).
    """
    print("=" * 60)
    print("CONNECTING TO QUOTEX (blocking — bot will NOT start until connected)...")
    print("=" * 60)
    attempt = 0
    while True:
        attempt += 1
        print(f"[connect] Attempt {attempt}...")
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        ok = False
        try:
            ok = loop.run_until_complete(provider._ensure_connected())
            if ok:
                print(f"[connect] ✓ Connected to Quotex on attempt {attempt}")
                # Pre-fetch candles for all 13 pairs in the SAME loop
                print("[connect] Pre-fetching 250 M1 candles for 13 OTC pairs...")
                try:
                    loop.run_until_complete(_preconnect_and_fetch_candles(provider))
                except Exception as e:
                    print(f"[connect] WARNING: pre-fetch raised: {e}")

                # FIX #20: شغّل الـ loop في thread منفصل يستمر بالعمل للأبد.
                # هذا ضروري لأن:
                #   1. engine.start() سجّلت مهام (keepalive_loop, watchdog, etc.)
                #      في هذا الـ loop — تحتاج loop نشط لتنفيذها
                #   2. WebSocket on_message يستدعي asyncio.run_coroutine_threadsafe
                #      لتحديث events (مثل candles_ready) — يحتاج loop نشط
                #   3. keep_alive_loop (re-subscribe كل 30s) تحتاج loop نشط
                # بدون هذا الـ thread، الـ loop يموت بعد run_until_complete،
                # ولن تصل أي ticks للـ buffer!
                print("[connect] Starting background event loop thread (for live ticks)...")
                loop_thread = threading.Thread(
                    target=loop.run_forever,
                    name="quotex-event-loop",
                    daemon=True,  # يموت تلقائياً عند إغلاق البرنامج
                )
                loop_thread.start()
                provider._keep_alive_loop = loop
                provider._keep_alive_thread = loop_thread
                print(f"[connect] ✓ Background loop running in thread '{loop_thread.name}'")

                # ابدأ keep_alive_loop في نفس الـ loop (الآن نشط)
                print("[connect] Starting live price keep-alive loop (re-subscribes every 30s)...")
                try:
                    asyncio.run_coroutine_threadsafe(provider.keep_alive_loop(), loop)
                    print("[connect] ✓ Keep-alive loop started")
                except Exception as e:
                    print(f"[connect] WARNING: keep-alive loop failed to start: {e}")

                # أعطِ الـ WebSocket وقتاً قصيراً ليبدأ استقبال الـ ticks
                # بعد إرسال subscriptions. هذا يسمح لـ tick_buffer بالتعبئة
                # قبل أن يبدأ البوت بجلب الشموع.
                print("[connect] Waiting 3s for first live ticks to arrive...")
                time.sleep(3)
                # اطبع إحصائيات الـ ticks للتأكد
                if provider.interceptor is not None:
                    for asset in OTC_ASSETS[:3]:  # أول 3 أزواج فقط للتأكد
                        n_ticks = provider.interceptor.get_tick_count(asset)
                        print(f"[connect]   {asset}: {n_ticks} ticks received")
                return True
            else:
                print(f"[connect] ✗ Attempt {attempt} failed")
        except Exception as e:
            print(f"[connect] ✗ Attempt {attempt} raised: {e}")
        finally:
            # Detach this loop from the "current" slot so the next iteration
            # (or the bot later) can install its own.
            asyncio.set_event_loop(None)
            if not ok:
                try:
                    loop.close()
                except Exception:
                    pass
        # Sleep before retry — NEVER give up.
        print(f"[connect] Retrying in 5s...")
        time.sleep(5)


def prompt_for_target_chat_id():
    """يطلب chat_id من التيرمنال — هذا هو الـ chat_id الذي سيرسل إليه البوت الإشارات.

    بالنسبة لقناة Telegram:
      - chat_id = -100xxxxxxxxxx (رقم سالب يبدأ بـ -100)
      - أو username القناة: @my_channel
    كيف تحصل على chat_id القناة:
      1. أضف البوت كمسؤول في القناة
      2. أرسل أي رسالة في القناة
      3. افتح https://api.telegram.org/bot<TOKEN>/getUpdates
      4. ابحث عن "chat":{"id":-100xxxxxxxxxx}
    """
    print("=" * 60)
    print("📞 ENTER TARGET CHAT_ID (القناة أو المحادثة التي سترسل إليها الإشارات)")
    print("   - للقناة: -100xxxxxxxxxx (رقم سالب يبدأ بـ -100)")
    print("   - أو username القناة: @my_channel")
    print("   - اضغط Enter لتخطّي (يمكن إضافته لاحقاً عبر /start)")
    print("=" * 60)
    while True:
        try:
            chat_id = input("chat_id > ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nAborted.")
            return None
        if not chat_id:
            return ""
        # قبول: أرقام سالبة، أرقام موجبة، أو @username
        if chat_id.startswith("@") or chat_id.lstrip("-").isdigit():
            return chat_id
        print("⚠ الصيغة غير صالحة. chat_id يجب أن يكون: رقم (مثل -1001234567890) أو @username")


def main():
    """Entry point: ask for Telegram token → Quotex credentials → CHAT_ID
    → connect to Quotex → START SIGNAL LOOP IMMEDIATELY.

    NEW FLOW (per user request):
      1. Ask for Telegram bot token (cached)
      2. Ask for Quotex credentials (cached)
      3. Ask for target chat_id (where to send signals)
      4. Connect to Quotex (blocking, never gives up)
      5. Auto-select ALL 13 OTC pairs + Gann strategy
      6. IMMEDIATELY start auto_signal_loop (NO menu, NO /start needed)
      7. The bot polls for /stop command but signals are sent automatically
    """
    global TELEGRAM_BOT_TOKEN, candle_provider, AUTO_SIGNAL_CHAT_ID

    # 1) Telegram bot token
    if not TELEGRAM_BOT_TOKEN:
        TELEGRAM_BOT_TOKEN = prompt_for_token()
        if not TELEGRAM_BOT_TOKEN:
            print("ERROR: no Telegram token provided. Exiting.")
            return

    # 2) Quotex credentials
    q_email, q_password, q_proxy = prompt_for_quotex_credentials()
    if not (q_email and q_password):
        print("ERROR: Quotex credentials are REQUIRED.")
        print("       Add them to credentials.json and re-run.")
        return

    # 3) Target chat_id (القناة التي سيرسل إليها الإشارات)
    target_chat_id = prompt_for_target_chat_id()
    if target_chat_id is None:
        print("Aborted.")
        return
    if not target_chat_id:
        print("⚠ لا يمكن بدء البوت بدون chat_id. أعد التشغيل وأدخل chat_id.")
        return
    AUTO_SIGNAL_CHAT_ID = target_chat_id
    _bd_save_cache(CHATID_CACHE_FILE, AUTO_SIGNAL_CHAT_ID)
    print(f"✓ target chat_id set: {AUTO_SIGNAL_CHAT_ID}")

    # 4) Purge old Quotex session
    print("Purging old Quotex session (session.json + browser/)...")
    purge_old_session()

    # 5) Connect to Quotex (blocking — never gives up)
    candle_provider = LiveCandleProvider(email=q_email, password=q_password, proxies=q_proxy or None)
    print(f"LiveCandleProvider initialized for {q_email}")
    _connect_quotex_blocking(candle_provider)

    # 6) Auto-select ALL 13 OTC pairs + Gann strategy
    bot_state.strategy = "quantvexa"   # GANN ENGINE
    bot_state.selected_pairs = set(s for s, _ in PAIR_LIST)
    bot_state.stop_requested = False
    print(f"✓ Auto-selected: {len(bot_state.selected_pairs)} OTC pairs (all)")

    # 7) Start the Telegram bot
    print("=" * 60)
    print("STARTING GANN SIGNAL BOT (auto-signal mode)")
    print(f"   VERSION    : {BOT_VERSION}")
    print(f"   ENGINE     : GANN (confluence-based)")
    print(f"   TIMEFRAME  : M1 (1 minute)")
    print(f"   TARGET     : {AUTO_SIGNAL_CHAT_ID}")
    print(f"   PAIRS      : {len(bot_state.selected_pairs)} (ALL 13 OTC)")
    print(f"   RESULTS    : {STATS['wins']}W / {STATS['losses']}L (history: {len(SIGNAL_HISTORY)})")
    print(f"   REPORT     : every {SIGNALS_PER_REPORT} signals")
    print(f"   PROVIDER   : Quotex live (connected)")
    print("=" * 60)

    app = (Application.builder()
           .token(TELEGRAM_BOT_TOKEN)
           .post_init(post_init)
           .post_shutdown(post_shutdown)
           .read_timeout(60).write_timeout(60).connect_timeout(30).pool_timeout(30)
           .build())
    # فقط أوامر أساسية — لا قوائم اختيار
    app.add_handler(CommandHandler("start", start_command))         # يعرض حالة فقط
    app.add_handler(CommandHandler("status", status_command))
    app.add_handler(CommandHandler("stop", stop_command))
    app.add_handler(CommandHandler("id", id_command))
    app.add_handler(CommandHandler("resetstats", resetstats_command))
    app.add_error_handler(error_handler)

    # ابدأ حلقة الإشارات فوراً بعد بناء الـ app (في post_init)
    async def _auto_start_signal_loop(application):
        """يبدأ حلقة الإشارات تلقائياً بعد بدء البوت."""
        await post_init(application)
        # انتظر قليلاً ليستقر اتصال Telegram
        await asyncio.sleep(2)
        if AUTO_SIGNAL_CHAT_ID and bot_state.selected_pairs and not bot_state.active:
            print(f"🚀 AUTO-STARTING signal loop → chat_id={AUTO_SIGNAL_CHAT_ID}")
            await _bd_ensure_auto_signal_task(application)
        else:
            print(f"⚠ Cannot auto-start: chat_id={AUTO_SIGNAL_CHAT_ID}, pairs={len(bot_state.selected_pairs)}")

    app = (Application.builder()
           .token(TELEGRAM_BOT_TOKEN)
           .post_init(_auto_start_signal_loop)
           .post_shutdown(post_shutdown)
           .read_timeout(60).write_timeout(60).connect_timeout(30).pool_timeout(30)
           .build())
    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("status", status_command))
    app.add_handler(CommandHandler("stop", stop_command))
    app.add_handler(CommandHandler("id", id_command))
    app.add_handler(CommandHandler("resetstats", resetstats_command))
    app.add_error_handler(error_handler)
    app.run_polling(allowed_updates=Update.ALL_TYPES)


async def _preconnect_and_fetch_candles(provider: LiveCandleProvider):
    """Connect to Quotex and pre-fetch 250 M1 candles for all 13 OTC pairs.
    SILENT — only prints a single summary line at the end.
    """
    if not await provider._ensure_connected():
        print("[pre-fetch] FAILED to connect to Quotex.")
        return
    successes = 0
    for symbol, _ in PAIR_LIST:
        try:
            candles = await provider.fetch_candles(symbol, count=250, timeframe_min=1)
            if candles and len(candles) >= 210:
                successes += 1
        except Exception:
            pass
    print(f"[pre-fetch] {successes}/{len(PAIR_LIST)} OTC pairs ready (250 candles each).")


if __name__ == "__main__":
    main()