# -*- coding: utf-8 -*-
"""
T.D.B. — Soroush Plus Self-Bot
ساخته شده برای اجرا روی ضعیف‌ترین سرورها با حداکثر بهینه‌سازی.
"""

from __future__ import annotations
from keep_alive import keep_alive

import ast
import asyncio
import json
import logging
import os
import random
import re
import hashlib
import gc
import time
import urllib.parse
import urllib.request
import requests
import aiohttp
from collections import defaultdict, deque, OrderedDict
from datetime import datetime
from typing import Any, Dict, List, Optional, Set, Tuple, Union

from spluspy import Client
from spluspy.sessions import StringSession

# ── FloodWait Error ──
try:
    from spluspy.errors import FloodWaitError
except ImportError:
    try:
        from spluspy import FloodWaitError
    except ImportError:
        # اگه پیدا نشد، یه کلاس ساختگی که هیچ‌وقت raise نمی‌شه
        class FloodWaitError(Exception):
            seconds = 0

# ---------------------------------------------------------------------------
# پیکربندی لاگ
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-8s | %(name)s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("TDB")
logging.getLogger("spluspy").setLevel(logging.ERROR)

# ---------------------------------------------------------------------------
# ⚡ بهینه‌سازی GC برای سرور کم‌رم
# ---------------------------------------------------------------------------
# پیش‌فرض پایتون: (700, 10, 10) — خیلی زود به زود اجرا می‌شه
# تنظیم جدید: (100000, 50, 50) — فقط وقتی خیلی زباله جمع شد
gc.set_threshold(100000, 50, 50)

# ---------------------------------------------------------------------------
# ثابت‌ها
# ---------------------------------------------------------------------------
BOT_NAME = "Robo"
SESSION_FILE = "session_bot.txt"
DEFAULT_PHONE = "+989336096879"
WARNINGS_FILE = "warnings.json"
STATS_FILE = "stats.json"

# ---------------------------------------------------------------------------
# کش اسم کاربران
# ---------------------------------------------------------------------------
_name_cache: Dict[int, Tuple[str, float]] = {}
_NAME_CACHE_TTL = 1800.0   # از ۴ دقیقه → ۳۰ دقیقه
_admin_cache: Dict[str, Tuple[bool, float]] = {}
_ADMIN_CACHE_TTL = 300.0   # از ۲ دقیقه → ۵ دقیقه
# ─── کش آبجکت چت ───
_chat_obj_cache: Dict[int, Tuple[Any, float]] = {}
_CHAT_OBJ_TTL = 300.0
# کش ادمین بودن خود ربات
_bot_admin_cache: Dict[str, Tuple[bool, float]] = {}
_BOT_ADMIN_CACHE_TTL = 120.0

# کش ویکی‌پدیا
_wiki_cache: Dict[str, Tuple[Optional[str], Optional[str], float]] = {}
_WIKI_CACHE_TTL = 1800.0
_wiki_last_request = 0.0
_WIKI_MIN_INTERVAL = 0.7

## Rate limit برای ارسال پیام — per-chat
_last_send_per_chat: Dict[int, float] = defaultdict(float)
_last_send_time = 0.0   # برای سازگاری نگه دار
_SEND_MIN_INTERVAL = 0.8

# ── ضد اسپم ──
SPAM_THRESHOLD = 7
SPAM_WINDOW = 4.0
BURST_THRESHOLD = 5
BURST_WINDOW = 4.0
GIF_SPAM_THRESHOLD = 3
GIF_SPAM_WINDOW = 10.0
SIMILAR_THRESHOLD = 4
SIMILAR_WINDOW = 15.0
MEDIA_SPAM_THRESHOLD = 6
MEDIA_SPAM_WINDOW = 10.0
EMOJI_ONLY_THRESHOLD = 8
EMOJI_ONLY_WINDOW = 20.0
MUTE_DURATION = 600
_SPAM_CLEANUP_INTERVAL = 60.0
_DAILY_STATS_CLEAR_INTERVAL = 86400.0  # ۲۴ ساعت = ۸۶۴۰۰ ثانیه
_WARN_COOLDOWN_SECONDS = 15.0
MAX_MESSAGE_LEN = 3800
WIKI_EXTRACT_LEN = 1000
# ---------------------------------------------------------------------------
# 🌤 آب و هوا (Open-Meteo — بدون نیاز به API Key)
# ---------------------------------------------------------------------------
_WEATHER_API = "https://api.open-meteo.com/v1/forecast"
_GEO_API = "https://geocoding-api.open-meteo.com/v1/search"
_POLL_TIMEOUT = 25.0

_weather_cache: Dict[str, Tuple[Optional[str], float]] = {}
_WEATHER_CACHE_TTL = 600.0
_weather_last_request = 0.0
_WEATHER_MIN_INTERVAL = 1.0

_WEATHER_CODES: Dict[int, str] = {
    0: "☀️ آسمان صاف", 1: "🌤 عمدتاً صاف", 2: "⛅️ نیمه‌ابری", 3: "☁️ ابری",
    45: "🌫 مه‌آلود", 48: "🌫 مه‌آلود یخ‌زده",
    51: "🌦 نم‌نم باران سبک", 53: "🌦 نم‌نم باران متوسط", 55: "🌧 نم‌نم باران شدید",
    56: "🌧 نم‌نم باران یخ‌زده سبک", 57: "🌧 نم‌نم باران یخ‌زده شدید",
    61: "🌧 باران سبک", 63: "🌧 باران متوسط", 65: "🌧 باران شدید",
    66: "🌧 باران یخ‌زده سبک", 67: "🌧 باران یخ‌زده شدید",
    71: "🌨 برف سبک", 73: "🌨 برف متوسط", 75: "❄️ برف شدید", 77: "🌨 دانه‌های برف",
    80: "🌦 رگبار سبک", 81: "🌦 رگبار متوسط", 82: "⛈ رگبار شدید",
    85: "🌨 رگبار برف سبک", 86: "🌨 رگبار برف شدید",
    95: "⛈ رعد و برق", 96: "⛈ رعد و برق با تگرگ سبک", 99: "⛈ رعد و برق با تگرگ شدید",
}

_WEATHER_EMOJI: Dict[str, str] = {
    "صاف": "☀️", "ابری": "☁️", "باران": "🌧",
    "برف": "❄️", "رعد": "⛈", "مه": "🌫",
}

_WEATHER_STOPWORDS: Set[str] = {
    "گرمه", "سرده", "خوبه", "بده", "بارونیه", "بارانیه", "آفتابیه",
    "ابریه", "برفیه", "چطوره", "چطور", "چه", "خوب", "بد", "گرم", "سرد",
    "بارانی", "آفتابی", "ابری", "برفی", "بوش", "بخاری", "کولر",
    "پاک", "آلوده", "مرطوب", "خشک", "شرجی", "خنک", "معتدل",
    "داره", "میاد", "شده", "شد", "هست", "نیست", "بخوره",
    "عوض", "تغییر", "چجوریه", "چجوری", "چگونه",
}

# ---------------------------------------------------------------------------
# خواندن سشن
# ---------------------------------------------------------------------------
session_str = ""

_env_session = os.environ.get("SESSION_STRING", "").strip()
if _env_session:
    session_str = _env_session
elif os.path.exists(SESSION_FILE):
    try:
        with open(SESSION_FILE, "r", encoding="utf-8") as f:
            session_str = f.read().strip()
    except OSError as exc:
        log.warning("خطا در خواندن فایل سشن: %s", exc)

# ---------------------------------------------------------------------------
# نرمال‌سازی متن
# ---------------------------------------------------------------------------
_NORM_TABLE = str.maketrans({
    "\u200e": None, "\u200f": None, "\u202a": None, "\u202b": None,
    "\u202c": None, "\u202d": None, "\u202e": None, "\ufeff": None,
    "\u2066": None, "\u2067": None, "\u2068": None, "\u2069": None,
    "\u064b": None, "\u064c": None, "\u064d": None, "\u064e": None,
    "\u064f": None, "\u0650": None, "\u0651": None, "\u0652": None,
    "\u0653": None, "\u0654": None, "\u0655": None, "\u0670": None,
    "ي": "ی", "ك": "ک", "ة": "ه", "ۀ": "ه",
})


def normalize_text(text: str) -> str:
    if not text:
        return ""
    return text.translate(_NORM_TABLE).strip()

# ---------------------------------------------------------------------------
# 📅 تبدیل تاریخ میلادی به شمسی (بدون کتابخانه)
# ---------------------------------------------------------------------------
_PERSIAN_MONTHS = [
    "فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
    "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"
]
_PERSIAN_WEEKDAYS = {
    0: "دوشنبه", 1: "سه‌شنبه", 2: "چهارشنبه", 3: "پنجشنبه",
    4: "جمعه", 5: "شنبه", 6: "یک‌شنبه",
}


def gregorian_to_jalali(gy: int, gm: int, gd: int) -> Tuple[int, int, int]:
    """تبدیل تاریخ میلادی به شمسی (الگوریتم Borkowski)"""
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = (
        355666 + (365 * gy) + ((gy2 + 3) // 4) - ((gy2 + 99) // 100)
        + ((gy2 + 399) // 400) + gd + g_d_m[gm - 1]
    )
    jy = -1595 + (33 * (days // 12053))
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm = 1 + (days // 31)
        jd = 1 + (days % 31)
    else:
        jm = 7 + ((days - 186) // 30)
        jd = 1 + ((days - 186) % 30)
    return jy, jm, jd


def get_shamsi_date(now: Optional[datetime] = None) -> str:
    """تاریخ شمسی رو به صورت رشته برمی‌گردونه"""
    if now is None:
        now = datetime.now()
    jy, jm, jd = gregorian_to_jalali(now.year, now.month, now.day)
    month_name = _PERSIAN_MONTHS[jm - 1]
    weekday = _PERSIAN_WEEKDAYS.get(now.weekday(), "")
    return f"{weekday} {jd} {month_name} {jy}"

# ---------------------------------------------------------------------------
# کمک‌کننده‌های رویداد
# ---------------------------------------------------------------------------
def get_event_text(event: Any) -> str:
    raw = getattr(event, "raw_text", None)
    if raw:
        return raw
    msg = getattr(event, "message", None)
    if msg is not None:
        for attr in ("text", "message"):
            val = getattr(msg, attr, None)
            if val:
                return val
    return ""


def safe_sender_name(event: Any) -> str:
    try:
        msg = getattr(event, "message", None)
        sender = getattr(msg, "sender", None) if msg is not None else None
        if sender is None:
            return "کاربر"
        return (
            getattr(sender, "first_name", None)
            or getattr(sender, "title", None)
            or getattr(sender, "username", None)
            or "کاربر"
        )
    except Exception:
        return "کاربر"
    


async def get_sender_display_name(event: Any, user_id: Optional[int] = None) -> str:
    cached_name = getattr(event, "_tdb_name_cache", None)
    if cached_name is not None:
        return cached_name

    name = safe_sender_name(event)
    if name and name not in ("کاربر", "کاربر ناشناس"):
        try:
            event._tdb_name_cache = name
        except Exception:
            pass
        return name

    if user_id is None:
        try:
            msg = getattr(event, "message", None)
            user_id = (
                getattr(event, "sender_id", None)
                or (getattr(msg, "sender_id", None) if msg is not None else None)
                or (getattr(msg, "from_id", None) if msg is not None else None)
            )
        except Exception:
            pass

    if user_id is not None:
        try:
            fetched = await get_user_name_cached(user_id)
            if fetched and fetched != "کاربر ناشناس":
                try:
                    event._tdb_name_cache = fetched
                except Exception:
                    pass
                return fetched
        except Exception:
            pass

    try:
        event._tdb_name_cache = "کاربر ناشناس"
    except Exception:
        pass
    return "کاربر ناشناس"


async def safe_reply(event: Any, text: str, **kwargs) -> Optional[Any]:
    """جواب دادن امن با مدیریت FloodWait — rate limit per-chat"""
    # chat_id رو استخراج کن
    chat_id = (
        getattr(event, "chat_id", None)
        or (getattr(getattr(event, "message", None), "chat_id", None))
        or 0
    )

    for attempt in range(3):
        elapsed = time.time() - _last_send_per_chat[chat_id]
        if elapsed < _SEND_MIN_INTERVAL:
            await asyncio.sleep(_SEND_MIN_INTERVAL - elapsed)
        _last_send_per_chat[chat_id] = time.time()

        try:
            return await event.reply(text, **kwargs)
        except FloodWaitError as e:
            wait = getattr(e, "seconds", 30) + 2
            log.warning("⏳ FloodWait: %d ثانیه صبر می‌کنم (تلاش %d/3)", wait, attempt + 1)
            await asyncio.sleep(wait)
            continue
        except Exception as exc:
            err_str = str(exc).lower()
            if "can't write" in err_str or "not enough rights" in err_str:
                log.debug("روبو اجازه‌ی نوشتن در این چت را ندارد.")
            else:
                log.debug("reply failed: %s", exc)
            return None

    log.error("❌ بعد از ۳ بار تلاش، پیام ارسال نشد.")
    return None


async def safe_send(client_obj: Any, chat_id: int, text: str, **kwargs) -> Optional[Any]:
    """ارسال امن پیام — rate limit per-chat"""
    for attempt in range(3):
        elapsed = time.time() - _last_send_per_chat[chat_id]
        if elapsed < _SEND_MIN_INTERVAL:
            await asyncio.sleep(_SEND_MIN_INTERVAL - elapsed)
        _last_send_per_chat[chat_id] = time.time()

        try:
            return await client_obj.send_message(chat_id, text, **kwargs)
        except FloodWaitError as e:
            wait = getattr(e, "seconds", 30) + 2
            log.warning("⏳ FloodWait: %d ثانیه صبر می‌کنم (تلاش %d/3)", wait, attempt + 1)
            await asyncio.sleep(wait)
            continue
        except Exception as exc:
            err_str = str(exc).lower()
            if "can't write" in err_str or "not enough rights" in err_str:
                log.debug("نمی‌توان در چت %s نوشت.", chat_id)
            else:
                log.debug("send_message failed: %s", exc)
            return None

    log.error("❌ بعد از ۳ بار تلاش، پیام ارسال نشد.")
    return None


async def safe_edit(msg: Any, text: str, **kwargs) -> bool:
    """ویرایش امن پیام با مدیریت FloodWait"""
    if msg is None:
        return False
    
    for attempt in range(2):  # ادیت حداکثر ۲ بار
        try:
            await msg.edit(text, **kwargs)
            return True
        except FloodWaitError as e:
            wait = getattr(e, "seconds", 30) + 2
            log.warning("⏳ FloodWait در edit: %d ثانیه", wait)
            await asyncio.sleep(wait)
            continue
        except Exception as exc:
            err_str = str(exc).lower()
            if "can't write" in err_str or "not enough rights" in err_str:
                log.debug("روبو اجازه‌ی ادیت در این چت را ندارد.")
            else:
                log.debug("edit failed: %s", exc)
            return False
    
    return False


async def safe_delete(msg: Any) -> None:
    """حذف امن پیام"""
    if msg is None:
        return
    try:
        await msg.delete()
    except Exception as exc:
        log.debug("delete failed: %s", exc)


async def get_user_name_cached(uid: int) -> str:
    """اسم کاربر رو با کش ۵ دقیقه‌ای برمی‌گردونه"""
    cached = _name_cache.get(uid)
    if cached:
        name, exp = cached
        if time.time() < exp:
            return name

    try:
        user_obj = await client.get_entity(uid)
        name = (
            getattr(user_obj, "first_name", None)
            or getattr(user_obj, "title", None)
            or getattr(user_obj, "username", None)
            or "کاربر ناشناس"
        )
    except Exception:
        name = "کاربر ناشناس"

    _name_cache[uid] = (name, time.time() + _NAME_CACHE_TTL)
    return name

# ---------------------------------------------------------------------------
# فیلتر فحش
# ---------------------------------------------------------------------------
BAD_WORDS: Set[str] = {
    "جنده", "گاییدم", "مادرجنده", "حرومزاده", "مادرخراب",
    "خارکصه", "پورن", "سکسی", "سکس", "حرومی", "ولدالزنا",
    "مادرکسده", "مادرکصده", "ننت", "ننش", "خارکسه", "خارکصده",
    "خوارکسه", "خوارکصه", "خواهرکسه", "خواهرکصه", "خوارکصده",
    "خوارکصده", "ولدزنا", "ننتو", "ننشو", "خارشو" ,"مادرتو",
    "قحبه", "مادرقحبه", "روسپی", "مادرکوسده", "مادرکوصده",
    "خارکثه", "خارکصه", "ننه", "حرام زاده", "خارکوصده",
}
MAX_WARNINGS = 3

# ← این رو اضافه کن
_BAD_PATTERN = re.compile(
    "|".join(re.escape(w) for w in BAD_WORDS),
    re.IGNORECASE | re.UNICODE,
)

warnings_data: Dict[str, int] = {}
if os.path.exists(WARNINGS_FILE):
    try:
        with open(WARNINGS_FILE, "r", encoding="utf-8") as f:
            warnings_data = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        log.warning("خطا در خواندن فایل اخطارها: %s", exc)


def save_warnings_sync() -> None:
    tmp = WARNINGS_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(warnings_data, f, ensure_ascii=False)  # indent حذف
        os.replace(tmp, WARNINGS_FILE)
    except OSError as exc:
        log.error("خطا در ذخیره اخطارها: %s", exc)


async def save_warnings() -> None:
    await asyncio.to_thread(save_warnings_sync)


# ---------------------------------------------------------------------------
# 🚫 وضعیت فیلتر فحش برای هر گروه
# ---------------------------------------------------------------------------
FILTERS_FILE = "filters.json"
_badword_filter_state: Dict[str, bool] = {}  # chat_id → True/False

if os.path.exists(FILTERS_FILE):
    try:
        with open(FILTERS_FILE, "r", encoding="utf-8") as f:
            _badword_filter_state = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        log.warning("خطا در خواندن فایل فیلترها: %s", exc)
        _badword_filter_state = {}


def save_filters() -> None:
    """ذخیره امن وضعیت فیلترها روی دیسک"""
    tmp = FILTERS_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(_badword_filter_state, f, ensure_ascii=False, indent=2)
        os.replace(tmp, FILTERS_FILE)
    except OSError as exc:
        log.error("خطا در ذخیره فیلترها: %s", exc)


def is_badword_filter_on(chat_id: int) -> bool:
    """پیش‌فرض: روشن. اگه گروه خاموشش کرده بود → False"""
    return _badword_filter_state.get(str(chat_id), True)


# ---------------------------------------------------------------------------
# ⚙️ تنظیمات گروه (پنل)
# ---------------------------------------------------------------------------
SETTINGS_FILE = "settings.json"
_DEFAULT_SETTINGS: Dict[str, Any] = {
    "max_warnings": 3,
    "antispam_enabled": True,
    "chat_enabled": True,
}
_group_settings: Dict[str, Dict[str, Any]] = {}
_settings_dirty = False


def _load_settings_safe() -> Dict[str, Any]:
    if not os.path.exists(SETTINGS_FILE):
        return {}
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        log.warning("load settings failed: %s", exc)
        return {}


_group_settings = _load_settings_safe() or {}


def save_settings(force: bool = False) -> None:
    global _settings_dirty
    if not _settings_dirty and not force:
        return
    tmp = SETTINGS_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(_group_settings, f, ensure_ascii=False, indent=2)
        os.replace(tmp, SETTINGS_FILE)
        _settings_dirty = False
    except OSError as exc:
        log.error("save settings failed: %s", exc)


def get_setting(chat_id: int, key: str, default: Any = None) -> Any:
    d = _group_settings.get(str(chat_id))
    if d is None:
        return _DEFAULT_SETTINGS.get(key, default)
    return d.get(key, _DEFAULT_SETTINGS.get(key, default))


def set_setting(chat_id: int, key: str, value: Any) -> None:
    global _settings_dirty
    cid = str(chat_id)
    _group_settings.setdefault(cid, {})[key] = value
    _settings_dirty = True


# ---------------------------------------------------------------------------
# 📊 آمار پیام‌های گروه — نسخه بهینه
# ---------------------------------------------------------------------------
# ساختار جدید: chat_id → {user_id: count}   (O(k) نه O(n))
_msg_stats: Dict[int, Dict[int, int]] = {}
_stats_dirty = False
_MSG_STATS_MAX_CHATS = 5_000
_MSG_STATS_MAX_USERS_PER_CHAT = 10_000

# ─── کش گروه‌های فعال برای مرتب‌سازی سریع ───
_chat_stats_cache: Dict[int, Tuple[List[Tuple[int, int]], int, float]] = {}
_CHAT_STATS_CACHE_TTL = 5.0


if os.path.exists(STATS_FILE):
    try:
        with open(STATS_FILE, "r", encoding="utf-8") as f:
            loaded = json.load(f)
        for k, v in loaded.items():
            try:
                cid = int(k)
                if isinstance(v, dict):
                    _msg_stats[cid] = {int(u): int(c) for u, c in v.items()}
            except (ValueError, TypeError):
                continue
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        log.warning("خطا در خواندن فایل آمار: %s", exc)
        _msg_stats = {}


def _save_stats_sync() -> None:
    """نسخه‌ی sync — فقط داخل thread صدا زده می‌شه"""
    global _stats_dirty
    tmp = STATS_FILE + ".tmp"
    try:
        serializable = {
            str(cid): {str(uid): cnt for uid, cnt in users.items()}
            for cid, users in _msg_stats.items()
        }
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(serializable, f, ensure_ascii=False, separators=(",", ":"))
        os.replace(tmp, STATS_FILE)
        _stats_dirty = False
    except OSError as exc:
        log.error("خطا در ذخیره آمار: %s", exc)


async def _save_stats_async() -> None:
    """نسخه‌ی async — event loop رو بلاک نمی‌کنه"""
    await asyncio.to_thread(_save_stats_sync)


def _save_stats() -> None:
    """برای سازگاری با کدهای قدیمی sync"""
    _save_stats_sync()


def _bump_stat(chat_id: int, user_id: int) -> None:
    """افزایش شمارنده پیام کاربر در گروه — O(1)"""
    global _stats_dirty
    users = _msg_stats.get(chat_id)
    if users is None:
        if len(_msg_stats) >= _MSG_STATS_MAX_CHATS:
            _msg_stats.pop(next(iter(_msg_stats)), None)
        _msg_stats[chat_id] = {user_id: 1}
    else:
        if user_id in users:
            users[user_id] += 1
        else:
            if len(users) >= _MSG_STATS_MAX_USERS_PER_CHAT:
                users.pop(next(iter(users)), None)
            users[user_id] = 1
    _stats_dirty = True


async def _save_stats_if_dirty() -> None:
    """اگه آماری تغییر کرده، async ذخیره کن"""
    if _stats_dirty:
        await _save_stats_async()


def _get_chat_stats(chat_id: int) -> List[Tuple[int, int]]:
    """لیست (user_id, count) برای این گروه — نزولی (با کش ۵ ثانیه‌ای)"""
    now = time.time()
    cached = _chat_stats_cache.get(chat_id)
    if cached and cached[2] > now:
        return cached[0]

    users = _msg_stats.get(chat_id)
    if not users:
        result: List[Tuple[int, int]] = []
    else:
        result = sorted(users.items(), key=lambda x: x[1], reverse=True)

    _chat_stats_cache[chat_id] = (result, len(result), now + _CHAT_STATS_CACHE_TTL)
    return result


def _fmt(n: int) -> str:
    """عدد با جداکننده هزارگان"""
    return f"{n:,}"

async def _daily_stats_clear() -> None:
    """هر ۲۴ ساعت آمار گروه‌ها رو پاک می‌کنه"""
    global _stats_dirty
    while True:
        try:
            await asyncio.sleep(_DAILY_STATS_CLEAR_INTERVAL)
            total = sum(len(u) for u in _msg_stats.values())
            if total == 0:
                continue
            _msg_stats.clear()
            _chat_stats_cache.clear()
            _stats_dirty = True
            await _save_stats_async()
            log.info("🗑 آمار پاکسازی شد. (%d رکورد)", total)
        except asyncio.CancelledError:
            log.info("🛑 daily_stats_clear متوقف شد.")
            raise
        except Exception as exc:
            log.error("⚠️ daily_stats_clear خطا داد (ادامه می‌ده): %s", exc)
            await asyncio.sleep(60)

async def _add_warning_and_maybe_kick(client, chat_id, user_id, name, reason):
    """اضافه کردن اخطار و در صورت رسیدن به حد مجاز، حذف کاربر."""
    if not name or name == "کاربر":
        try:
            name = await get_user_name_cached(user_id)
        except Exception:
            name = "کاربر ناشناس"

    try:
        max_warn = int(get_setting(chat_id, "max_warnings", MAX_WARNINGS) or MAX_WARNINGS)
    except (TypeError, ValueError):
        max_warn = MAX_WARNINGS
    if max_warn < 1:
        max_warn = 1

    key = f"{chat_id}:{user_id}"
    current = warnings_data.get(key, 0) + 1
    warnings_data[key] = current
    await save_warnings()

    if current >= max_warn:
        kicked = False
        try:
            if hasattr(client, "kick_participant"):
                await client.kick_participant(chat_id, user_id)
                kicked = True
            elif hasattr(client, "edit_permissions"):
                await client.edit_permissions(chat_id, user_id, view_messages=False)
                kicked = True
        except Exception as exc:
            log.debug("kick failed: %s", exc)
            kicked = False


        if kicked:
            warnings_data.pop(key, None)
            _offense_count.pop(f"{chat_id}:{user_id}", None)
            await save_warnings()
            await safe_send(
                client, chat_id,
                f"🚫 کاربر {name} به دلیل {reason} و رسیدن به {max_warn} اخطار، از گروه حذف شد."
            )
        else:
            await safe_send(
                client, chat_id,
                f"⚠️ کاربر {name} به {max_warn} اخطار رسید ولی من نتونستم بنش کنم.\n"
                f"لطفاً من رو ادمین کنید یا دستی اقدام کنید."
            )
    else:
        remaining = max_warn - current
        await safe_send(
            client, chat_id,
            f"⚠️ کاربر {name} به دلیل {reason} اخطار گرفت.\n"
            f"📊 اخطار فعلی: {current}/{max_warn}\n"
            f"❗️ {remaining} اخطار تا حذف از گروه."
        )
# ---------------------------------------------------------------------------
# ضد اسپم
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# ضد اسپم هوشمند (تعدیل‌شده)
# ---------------------------------------------------------------------------
_user_msg_times: Dict[str, deque] = defaultdict(lambda: deque(maxlen=30))
_user_msg_hashes: Dict[str, deque] = defaultdict(lambda: deque(maxlen=30))
_user_media_times: Dict[str, deque] = defaultdict(lambda: deque(maxlen=20))
_user_gif_times: Dict[str, deque] = defaultdict(lambda: deque(maxlen=10))
_user_emoji_times: Dict[str, deque] = defaultdict(lambda: deque(maxlen=15))
_muted_until: Dict[str, float] = {}
_warn_cooldown: Dict[str, float] = {}
_offense_count: Dict[str, int] = defaultdict(int)
_last_spam_cleanup = 0.0

_EMOJI_RE = re.compile(
    "[\U0001F300-\U0001FAFF\U00002600-\U000027BF\U0001F000-\U0001F2FF"
    "\U0001F900-\U0001F9FF\u2600-\u26FF\u2700-\u27BF]+"
)

_PUNISH_LADDER = [
    (1, "warn", None),
    (2, "mute", 600),
    (3, "mute", 3600),
    (4, "mute", 86400),
    (5, "kick", None),
]


def _msg_hash(text: str) -> str:
    norm = re.sub(r"\s+", "", text or "")
    return hashlib.md5(norm.encode("utf-8", "ignore")).hexdigest()


def _is_emoji_only(text: str) -> bool:
    if not text:
        return False
    stripped = _EMOJI_RE.sub("", text)
    stripped = re.sub(r"[\s\W_]+", "", stripped)
    return len(stripped) == 0 and len(text.strip()) > 0


def is_warn_cooldown(user_id: int, chat_id: int) -> bool:
    key = f"{chat_id}:{user_id}"
    exp = _warn_cooldown.get(key)
    if exp is None:
        return False
    if time.time() < exp:
        return True
    del _warn_cooldown[key]
    return False


def set_warn_cooldown(user_id: int, chat_id: int,
                      duration: float = _WARN_COOLDOWN_SECONDS) -> None:
    _warn_cooldown[f"{chat_id}:{user_id}"] = time.time() + duration


def _cleanup_spam_dicts(now: float) -> None:
    global _last_spam_cleanup
    if now - _last_spam_cleanup < _SPAM_CLEANUP_INTERVAL:
        return
    _last_spam_cleanup = now

    for store, window in (
        (_user_msg_times, SPAM_WINDOW),
        (_user_msg_hashes, SIMILAR_WINDOW),
        (_user_media_times, MEDIA_SPAM_WINDOW),
        (_user_emoji_times, EMOJI_ONLY_WINDOW),
        (_user_gif_times, GIF_SPAM_WINDOW),
    ):
        dead = []
        for k, dq in store.items():
            if not dq:
                dead.append(k)
                continue
            last = dq[-1][1] if isinstance(dq[-1], tuple) else dq[-1]
            if now - last > window * 3:
                dead.append(k)
        for k in dead:
            del store[k]

    for d in (_muted_until, _warn_cooldown):
        expired = [k for k, t in d.items() if now >= t]
        for k in expired:
            del d[k]

    for k in list(_offense_count.keys()):
        if (k not in _user_msg_times and k not in _user_media_times
                and k not in _user_emoji_times):
            del _offense_count[k]

    expired_names = [uid for uid, (_, exp) in _name_cache.items() if now >= exp]
    for uid in expired_names:
        del _name_cache[uid]

    expired_admin = [k for k, (_, exp) in _admin_cache.items() if now >= exp]
    for k in expired_admin:
        del _admin_cache[k]

    expired_bot = [k for k, (_, exp) in _bot_admin_cache.items() if now >= exp]
    for k in expired_bot:
        del _bot_admin_cache[k]

    expired_wiki = [k for k, (_, _, exp) in _wiki_cache.items() if now >= exp]
    for k in expired_wiki:
        del _wiki_cache[k]

    expired_curr = [k for k, (_, exp) in _CURRENCY_CACHE.items() if now >= exp]
    for k in expired_curr:
        del _CURRENCY_CACHE[k]

    # ─── پاک‌سازی کش cooldown روبو ───
    old_ai = [k for k, t in _ai_user_last.items() if now - t > 3600]
    for k in old_ai:
        del _ai_user_last[k]

    # ─── پاک‌سازی rate-limit ارسال ───
    old_sends = [k for k, t in _last_send_per_chat.items() if now - t > 900]
    for k in old_sends:
        del _last_send_per_chat[k]

    # ─── پاک‌سازی کش آبجکت چت ───
    expired_chat_obj = [k for k, (_, exp) in _chat_obj_cache.items() if now >= exp]
    for k in expired_chat_obj:
        del _chat_obj_cache[k]

    # ─── پاک‌سازی کش آمار گروه ───
    expired_stats = [k for k, (_, _, exp) in _chat_stats_cache.items() if now >= exp]
    for k in expired_stats:
        del _chat_stats_cache[k]

    # ─── پاک‌سازی admin locks بلااستفاده ───
    if len(_admin_locks) > _ADMIN_LOCKS_MAX:
        for k in list(_admin_locks.keys())[:_ADMIN_LOCKS_MAX // 2]:
            lk = _admin_locks.get(k)
            if lk is not None and not lk.locked():
                _admin_locks.pop(k, None)

def is_muted(user_id: int, chat_id: int) -> bool:
    key = f"{chat_id}:{user_id}"
    exp = _muted_until.get(key)
    if exp is None:
        return False
    if time.time() < exp:
        return True
    del _muted_until[key]
    return False


def set_mute(user_id: int, chat_id: int, duration: float = MUTE_DURATION) -> None:
    _muted_until[f"{chat_id}:{user_id}"] = time.time() + duration

def _fmt_duration(seconds: int) -> str:
    """ثانیه رو به فرمت خوانا تبدیل می‌کنه"""
    if seconds < 60:
        return f"{seconds} ثانیه"
    if seconds < 3600:
        return f"{seconds // 60} دقیقه"
    if seconds < 86400:
        hours = seconds // 3600
        return f"{hours} ساعت"
    days = seconds // 86400
    return f"{days} روز"

def _add_offense(user_id: int, chat_id: int) -> int:
    key = f"{chat_id}:{user_id}"
    _offense_count[key] += 1
    return _offense_count[key]


def get_punishment(user_id: int, chat_id: int) -> Tuple[str, Optional[int], int]:
    n = _add_offense(user_id, chat_id)
    for threshold, action, duration in _PUNISH_LADDER:
        if n <= threshold:
            return (action, duration, n)
    return ("kick", None, n)


def is_spam(user_id: int, chat_id: int,
            text: str = "", media_type: str = "") -> Optional[str]:
    now = time.time()
    key = f"{chat_id}:{user_id}"

    # ─── چک گیف اسپم (اولویت بالا) ───
    if media_type == "gif":
        gq = _user_gif_times[key]
        while gq and now - gq[0] >= GIF_SPAM_WINDOW:
            gq.popleft()
        gq.append(now)
        if len(gq) >= GIF_SPAM_THRESHOLD:
            return "اسپم"

    dq = _user_msg_times[key]
    while dq and now - dq[0] >= SPAM_WINDOW:
        dq.popleft()
    dq.append(now)
    burst = sum(1 for x in dq if now - x <= BURST_WINDOW)
    if burst >= BURST_THRESHOLD:
        return "اسپم"

    if len(dq) >= SPAM_THRESHOLD:
        return "اسپم"

    if text and len(text) > 5:
        h = _msg_hash(text)
        hq = _user_msg_hashes[key]
        while hq and now - hq[0][1] >= SIMILAR_WINDOW:
            hq.popleft()
        hq.append((h, now))
        same = sum(1 for x, _ in hq if x == h)
        if same >= SIMILAR_THRESHOLD:
            return "اسپم"

    if media_type:
        mq = _user_media_times[key]
        while mq and now - mq[0] >= MEDIA_SPAM_WINDOW:
            mq.popleft()
        mq.append(now)
        if len(mq) >= MEDIA_SPAM_THRESHOLD:
            return f"اسپم {media_type}"

    if text and _is_emoji_only(text):
        eq = _user_emoji_times[key]
        while eq and now - eq[0] >= EMOJI_ONLY_WINDOW:
            eq.popleft()
        eq.append(now)
        if len(eq) >= EMOJI_ONLY_THRESHOLD:
            return "اسپم"

    _cleanup_spam_dicts(now)
    return None

# ---------------------------------------------------------------------------
# تشخیص گروه
# ---------------------------------------------------------------------------
def check_is_group(event: Any, chat: Any = None) -> bool:
    for attr in ("is_group", "is_channel"):
        if getattr(event, attr, None) is True:
            return True
    if getattr(event, "is_private", None) is True:
        return False

    msg = getattr(event, "message", None) or event
    for attr in ("is_group", "is_channel"):
        if getattr(msg, attr, None) is True:
            return True
    if getattr(msg, "is_private", None) is True:
        return False

    for obj in (event, msg, chat):
        if obj is None:
            continue
        cid = getattr(obj, "chat_id", None) or getattr(obj, "id", None)
        if isinstance(cid, int) and cid < 0:
            return True

    if chat is not None:
        name = type(chat).__name__
        if name in ("Chat", "Channel", "Group", "Supergroup"):
            return True
        if getattr(chat, "participants_count", None) is not None:
            return True

    return False


# ---------------------------------------------------------------------------
# بررسی ادمین بودن
# ---------------------------------------------------------------------------
async def is_user_admin(chat_or_id: Union[int, Any], user_id: int) -> bool:
    if chat_or_id is None or user_id is None:
        return False

    if isinstance(chat_or_id, int):
        cid = chat_or_id
        chat_obj = None
    else:
        cid = getattr(chat_or_id, "id", None)
        chat_obj = chat_or_id

    if cid is None:
        return False

    try:
        participant = await client.get_participant(cid, user_id)
        if participant is not None:  # اگه participant None نبود
            ptype = type(participant).__name__
            if ptype in ("ChannelParticipantAdmin", "ChannelParticipantCreator",
                         "ChatParticipantAdmin", "ChatParticipantCreator"):
                return True
            if getattr(participant, "is_admin", False) or getattr(participant, "is_creator", False):
                return True
            if getattr(participant, "rank", None) or getattr(participant, "admin_rights", None):
                return True
            return False
    except Exception as exc:
        log.debug("get_participant خطا: %s", exc)

    try:
        from spluspy.tl import types
        filter_obj = types.ChannelParticipantsAdmins()
        async for admin in client.iter_participants(cid, filter=filter_obj):
            if getattr(admin, "id", None) == user_id:
                return True
    except Exception as exc:
        log.debug("iter_participants خطا: %s", exc)

    try:
        entity = chat_obj if chat_obj is not None else cid
        sender = await client.get_entity(user_id)
        perms = await client.get_permissions(entity, sender)
        if perms and (getattr(perms, "is_admin", False) or getattr(perms, "is_creator", False)):
            return True
    except Exception as exc:
        log.debug("get_permissions خطا: %s", exc)

    return False


# ─── Single-flight lock table ───
_admin_locks: Dict[str, asyncio.Lock] = {}
_ADMIN_LOCKS_MAX = 2000


async def is_user_admin_cached(chat_or_id, user_id) -> bool:
    if chat_or_id is None or user_id is None:
        return False

    cid = getattr(chat_or_id, "id", chat_or_id)
    key = f"{cid}:{user_id}"
    now = time.time()

    cached = _admin_cache.get(key)
    if cached:
        result, exp = cached
        if now < exp:
            return result

    lock = _admin_locks.get(key)
    if lock is None:
        lock = asyncio.Lock()
        _admin_locks[key] = lock
        if len(_admin_locks) > _ADMIN_LOCKS_MAX:
            for k in list(_admin_locks.keys())[:_ADMIN_LOCKS_MAX // 2]:
                lk = _admin_locks.get(k)
                if lk is not None and not lk.locked():
                    _admin_locks.pop(k, None)

    async with lock:
        cached = _admin_cache.get(key)
        if cached:
            result, exp = cached
            if time.time() < exp:
                return result

        result = await is_user_admin(chat_or_id, user_id)
        _admin_cache[key] = (result, time.time() + _ADMIN_CACHE_TTL)
        return result
    
async def is_bot_admin(chat_id: int) -> bool:
    """آیا خود ربات در این گروه ادمین است؟ (با کش ۲ دقیقه‌ای)"""
    if chat_id is None:
        return False

    key = str(chat_id)
    cached = _bot_admin_cache.get(key)
    if cached:
        result, exp = cached
        if time.time() < exp:
            return result

    result = False
    try:
        me = await client.get_me()
        my_id = getattr(me, "id", None)
        if my_id is not None:
            result = await is_user_admin(chat_id, my_id)
    except Exception as exc:
        log.debug("is_bot_admin failed: %s", exc)
        result = False

    _bot_admin_cache[key] = (result, time.time() + _BOT_ADMIN_CACHE_TTL)
    return result


async def require_bot_admin(event: Any, chat_id: int) -> bool:
    """اگه ربات ادمین نباشه، پیام می‌ده و False برمی‌گردونه."""
    if chat_id is None:
        return False
    if await is_bot_admin(chat_id):
        return True

    await safe_reply(
        event,
        "⚠️ من در این گروه ادمین نیستم!\n"
        "برای اجرای دستورات مدیریتی، لطفاً مرا ادمین کنید و دسترسی‌های لازم رو بدهید."
    )
    return False

async def _resolve_reply_target(event: Any, msg: Any) -> Tuple[Optional[int], Any]:
    replied_msg = None
    target_id = None
    try:
        replied_msg = await event.get_reply_message()
    except Exception:
        try:
            if msg is not None and hasattr(msg, "get_reply_message"):
                replied_msg = await msg.get_reply_message()
        except Exception:
            pass

    if replied_msg is not None:
        target_id = (
            getattr(replied_msg, "sender_id", None)
            or getattr(getattr(replied_msg, "sender", None), "id", None)
            or getattr(replied_msg, "from_id", None)
        )

    if target_id is None:                          # 👈 ۴ فاصله اضافه شد
        for obj in (event, msg):                   # 👈
            if obj is None:                        # 👈
                continue                            # 👈
            for attr in ("reply_to_sender_id", "reply_to"):
                val = getattr(obj, attr, None)
                if val is None:
                    continue

                if isinstance(val, int):
                    if attr == "reply_to_sender_id":
                        target_id = val
                        break
                    continue

                if hasattr(val, "sender_id"):
                    target_id = val.sender_id
                    break
                if hasattr(val, "id") and attr == "reply_to_sender_id":
                    target_id = val.id
                    break

    return target_id, replied_msg                  # 👈 ۴ فاصله (داخل تابع، بیرون از if)

async def _check_caller_admin(event: Any, chat: Any, chat_id: int, sender: Any) -> bool:
    if sender is None:
        return False
    try:
        return await is_user_admin_cached(
            chat if chat is not None else chat_id, sender
        )
    except Exception:
        return False


def _build_panel(chat_id: int, group_title: str = "گروه") -> str:
    def dot(b: bool) -> str:
        return "●" if b else "○"

    f = is_badword_filter_on(chat_id)
    s = get_setting(chat_id, "antispam_enabled", True)
    c = get_setting(chat_id, "chat_enabled", True)
    mw = get_setting(chat_id, "max_warnings", 3)

    safe_title = (group_title or "گروه").strip()[:40] or "گروه"

    return (
        f"🎛 وضعیت {safe_title}\n"
        "━━━━━━━━━━━━━━━━\n"
        f"{dot(f)}  فیلتر فحش\n"
        f"{dot(s)}  ضد اسپم\n"
        f"{dot(c)}  سخنگویی ربات\n"
        f"⚠️  تعداد اخطار: {mw} بار\n"
        "━━━━━━━━━━━━━━━━\n"
        "💬 دستورات:\n"
        "• فیلتر فحش روشن / خاموش\n"
        "• ضد اسپم روشن / خاموش\n"
        "• سخنگو روشن / خاموش\n"
        "• تعداد اخطار [عدد]"
    )


# ---------------------------------------------------------------------------
# چالش‌ها
# ---------------------------------------------------------------------------
raw_challenges: List[str] = [
    "⛵1.چه هدفی داری از زندگیـ؟",
    "⛵2.تاحالا رفتی دفتر برای اخراج شدنـ؟",
    "⛵3.به یکی زنگ بزن بگو ازت انتظار نداشتم ری اکشن شو بفرسـ؟",
    "⛵4.خاله ات بیشتر دوس داری یا عمه اتـ؟",
    "⛵5.سمی ترین عکست کدوم عکسهـ؟",
    "⛵6.اسم معلما تو از کلاس اول تا هرجایی که یادته بگوُ؟",
    "⛵7.اسم همسایه فضولتون چیهـ؟",
    "⛵8.شماره ات بگو؟",
    "⛵9.چند سالگی عاشق شدیـ؟",
    "⛵10.سیگار کشیدی ؟",
    "⛵11.تاحالا بخاطر یک پسر از خونه فرار کردیـ؟",
    "⛵12.دوستا تو انگولک کردی یا اونا تو رو انگولک کردن ؟",
    "⛵13.از نتایج گوگل اسکرین شات بده",
    "⛵15. تو فامیل از کی متنفری ؟",
    "⛵16.ماشینتون چیه ‍؟",
    "⛵17.حس ات ب من هر چی هست بگو ؟",
    "⛵18.اگه بدونی فردا میمیری چیکار میکنی ؟",
    "⛵19.از صفحه پیام های ذخیره شده روبیکا ات شات بده ؟",
    "⛵20.واسم استیکر لب بفرست!",
    "⛵21.بزرگ ترین خلافت تو زندگی ؟",
    "⛵22.یه عکس با روسری بده ؟",
    "⛵23.از چیه من بدت میاد ؟",
    "⛵24.منو بغل میکنی ؟",
    "⛵25.بهترین اتفاق زندگیت ؟",
    "⛵26.اگه بتونی یک درس جدید اضافه کنی چی اضافه میکنی؟",
    "⛵27.تو گپ رو کی کراشی و نمیتونی بگی؟",
    "⛵28.کی بیشتر رو مخته؟",
    "⛵29.کدوم اخلاقمو دوس داری؟",
    "⛵30.کدوم اخلاقم گنده؟",
    "⛵31.غذای مورد علاقت؟(فست‌فود_خانگی)",
    "⛵32.کنار دریا یا جنگل؟",
    "⛵33.شب یا روز؟",
    "⛵34.بارون یا برف؟",
    "⛵35.دوس داری پیش مرگ کسی بشی؟کی؟",
    "⛵36.رنگای تیره یا روشن؟",
    "⛵37.اگه کفنت جیب داشته باشه،باخودت چی میبری؟",
    "⛵38.حرفی ک تودلته و روت نمیشه بگی؟",
    "⛵39.میوه های تابستونی یا زمستونی؟",
    "⛵40.با چه حرفایی زود قول میخوری؟",
    "⛵41.استخر یا دریا؟",
    "⛵42.بنظرت غرور من چقدره؟",
    "⛵43.فاز دپ یا شیطنت؟",
    "⛵44.خوشگلی مهمه یا اخلاق؟",
    "⛵45.بغل و بوس یا دوری ازش؟",
    "⛵46.اخلاقای بدت چیه؟",
    "⛵47.اخلاقای خوبت چیه؟",
    "⛵48.بد ترین سوتیت چی بوده؟",
    "⛵49.پارتی یا جداگونه؟",
    "⛵50.اگ بگم ازت خوشم میاد چی میگی",
    "⛵51.خونه زندگی مجلل یا ساده",
    "⛵52.اگر اسمتو عوض کنی دوست داری چی بزاری؟",
    "⛵53.ویس بده صدا الاغ در بیار!",
    "⛵54.ویس بده صدا گاو در بیار!",
    "⛵55.رنگ مورد علاقت!",
    "⛵56.اسم خواهر و برادرت!",
    "⛵57.حست ب من؟",
    "⛵58.مغرور یا شیت؟",
    "⛵59.چ سبک آهنگ گوش میدی",
    "⛵60.بهترین اتفاق زندگیت؟",
    "⛵61.بزرگ ترین تجربه ای که داشتی",
    "⛵62.بنظر خودت کدوم امتحان ریدی",
    "⛵63.عاشقانه ترین کاری که کردی چی بوده؟",
    "⛵64.اگه بتونی یکی رو زنده کنی کی رو انتخاب میکنی",
    "⛵65.چه چیزی رو تا مدت زیادی اشتباه تلفظ میکردی؟",
    "⛵66.تا حالا کسی قلبتو شکسته میتونی ببخشیش؟",
    "⛵67.اگه در یک جزیره حبس بشی اسم سه نفری که دوست داری اونجا باشن چیه؟",
    "⛵68.اگه میتونستی واسه یه روز جای یه نفر دیگه زندگی کنی کیو انتخاب میکردی؟",
    "⛵69.بهترین تعریفی که از خودت شنیدی؟",
    "⛵70.اگه بخوای خودتو در یک کلمه توصیف کنی چی میگی؟",
    "⛵71.اگه بهت بگن همین الان یه آرزو کنی برآورده میشه چی آرزو میکنی؟",
    "⛵72.خنده دار ترین اسمی که تا به حال شنیدی؟",
    "⛵73.بد بو ترین جایی که تا حالا توش بودی کجاست؟",
    "⛵74.اگه قرار بود یه ابر قهرمان شی دوست داشتی چه قدرتی داشته باشی؟",
    "⛵75.فیلم یا نمایش کمدی مورد علاقه ت؟",
    "⛵76.مخفی ترین راز زندگیت چیه؟",
    "⛵77.زیر‌بغلت‌رو‌بو‌کن",
    "⛵78.بخند‌بدون‌دلیل",
    "⛵79.تنها‌هدفت",
    "⛵80.کی‌ازدواج‌میکنی",
    "⛵81.تا حالا خاستگار داشتی یا رفتی؟",
    "⛵82.دوست داری چطوری بمیری؟",
    "⛵83.تا حالا با فیلم گریه کردی؟",
    "⛵84.وقتی قهرین چطوری آشتی میکنین؟",
    "⛵85.رل داری یا داشتی؟",
    "⛵86.آخرین باری که از خنده دل درد گرفتی کی بود؟",
    "⛵87.دوس داری الان ازدواج کنی؟",
    "⛵88.چه کسی رو پنهانی دوست داری؟",
    "⛵89.خوشتیپی یا خوش‌قیافه؟",
    "⛵90.معیارهات برای ورود به یک رابطه چی هستن؟",
    "⛵91.به مامانت گفتی رل داری؟",
    "⛵93.فداتشم؟",
    "⛵94.ازجذاب‌ترین لباسی که تا حالا توی خلوت پوشیدی رو توصیف کن.",
    "⛵95.بهم دروغ گفتی؟",
    "⛵96.با کسی که فقط یکبار دیدیش، دیگه هم قرار نیست ببنیش، اما ازش خوشت میاد چکار می‌کنی؟",
    "⛵97.از چیه من بدت میاد؟",
    "⛵98.اولین عشقت کی بوده؟",
    "⛵99.پسرارو توصیف کن؟",
    "⛵100.چه سوالی رو دوست نداری توی این بازی جواب بدی؟",
    "🧼1.بچه بودی دکتر بازی میکردی ؟باکی ؟",
    "🧼2.اگه بگم خونمون یه خرگوش دارم حرف میزنه میای ببینی ؟",
    "🧼3.اگه خونمون خالی باشه میای پیشم ؟",
    "🧼4.تا حالا انگشت پاتو خوردی؟",
    "🧼5.با اخرین رلت سر چی کات کردین ؟",
    "🧼7.اگه رل داشتیو اون با یکی فاب بود چیکار میکردی؟",
    "🧼8. بهم اعتماد میکنی یروز کامل پیشم باشی مطمئن باشی کاری نمیکنم؟",
    "🧼9.اگه یکی به رلت تجاوز کنه چیکار میکنی ؟",
    "🧼10.یادگاریی از عشق اولت داری ؟",
    "🧼11.اگه عشق اولتو تو خیابون ببینی واکنشت چیه؟",
    "🧼12.رلت پر..یود شه چجوری باهاش رفتار میکنی ؟",
    "🧼13.پر..یود شدی دوسداری رلت چجوری برخورد کنه باهات؟",
    "🧼14.رلت تو قرار اول پیشنهاد س..س بده قبول میکنی ؟",
    "🧼15.اگه بگم برا یه هفته رلم باش قبول میکنی ؟",
    "🧼16.اگه دوسمداری ثابت کن ؟",
    "🧼17.کجا بریم خوشبگذره بهمون؟",
    "🧼18.معمولا بیرون میرین کی حساب میکنه ؟",
    "🧼19.تری سام دوسداری ؟",
    "🧼20.ی دروغ بهم بگو؟",
    "🧼21.بیشتر اکانت کیو چک میکنی؟",
    "🧼22.زیر لباست چ رنگیه؟",
    "🧼23.قابل اعتماد ترین فرد گپ؟",
    "🧼25.چی بیشتر توجهتو جلب میکنه؟",
    "🧼26.گنگ بالا دوس داری یا شر و شیطون؟",
    "🧼27.اسممو بنویس رو دستت عکسشو بده.",
    "🧼28.شات از لیست پی ویات.",
    "🧼30.رمان دوس داری یا پندوحکایت؟",
    "🧼31.اگ یکیو بگن چشم بسته میاریم هرچقد دوس داری بوسو بغلش کن،میخوای کی باشه؟",
    "🧼32.ب معلمت تاالان فک کردی ک چطور غذا می پزه؟",
    "🧼33.کیک خامه‌ای یا شکلاتی؟",
    "🧼34.نوتلا یا شکلات تلخ ٪99 ؟",
    "🧼35. ۲تا ملاک مهم همسرت؟",
    "🧼36.تحمل گشنگیو نداری یا تشنگیو؟",
    "🧼37. چهارتا از اموجی هایی ک خیلی استفاده میکنی؟",
    "🧼38.اولین بوستون با عشقت از کجا باشه؟",
    "🧼39.حس انتقامت قوی تره یا بخششت؟",
    "🧼40.مجبور شی با یکی از جنس مخالفای گپ سفر کنی،انتخابت کیه؟",
    "🧼41.نژاد پرستی؟",
    "🧼42.تو ویس بگو (سلام خوبی)",
    "🧼43.میخوای همخونت شم؟",
    "🧼44.اخلاق گندت ک خودتم ازش بیزاری؟",
    "🧼45.تو دریا غرق شدن ترسناک تره یا تصادف؟",
    "🧼46.تو گپ برو پیوی یکی بگو دوستت دارم.شاتشو بده(جنس مخالف)",
    "🧼47.شب میخوابی  با لباس؟",
    "🧼48.تو گپ ک رو مخ تره؟",
    "🧼49.برو پیوی یکی ایسگاش کن شات بده.",
    "🧼50.اکثر درددلات با کدوم فردگپه؟",
    "🧼51.از کدوم وحشت داری مار/عقرب/رتیل؟",
    "🧼52.دوس داشتی علاوه بر این‌ک هم گپ هستیم،دیگ چی باشیم؟",
    "🧼53.محرم یا نوروز؟چرا؟",
    "🧼54.ب جمله (تنهایی لاتی تره)نظرت چیه؟",
    "🧼55.اهل تعارف هستی یا ن؟",
    "🧼56.بنظرت میتونی مخمو بزنی؟",
    "🧼57.اگ حیوون میشدی  دوست داشتی چی بشی؟",
    "🧼58.قیافم تو ذهنت چ شکلیه؟",
    "🧼59.آرزوت چیه؟",
    "🧼60.دوچرخه یا موتور؟",
    "🧼61.دوس داری گوشی کیو چک کنی؟",
    "🧼62.شوخیات بیشتر +18 یا معمولی؟",
    "🧼63.تو حموم چیکار میکنی؟",
    "🧼64.کدومش بدتره؟یهو اب تو حموم یخ شه.تو دسشویی داغ شه؟",
    "🧼65.اگه قرار باشه لب یکیو تو این گپ بخوری.اون کیه؟",
    "🧼66.برو پی وی یکی ازش عکسشو بگیر.",
    "🧼68.عکستو بده بهم تو پیوی.",
    "🧼69.رل،زشت پولدار،خوشگل بی پول؟کدومش",
    "🧼70.فیلم سوپر میبینی؟",
    "🧼71.چ غذای رو خیلی دوس داری",
    "🧼72.تلخ شیرین ترش یا تند؟",
    "🧼73.باحال ترین کاری ک کردی چی بوده؟",
    "🧼74.اگ صب پاشی ببینی بقلتم چیکا میکنی؟",
    "🧼75.همین الان ی عکس از خودت بده؟",
    "🧼76.اگ قبل از ب دنیا اومدن میدونسی ک قرار این شخصیت و این زندگی رو داشه باشی باز انتخابش میکردی؟؟",
    "🧼77.تا ب حال گم شدی؟",
    "🧼78.یکی از آرزو هات ک خیلی دوس داری بش برسی بگو",
    "🧼79.تا ب حال شده از دس مامان یا بابات کتک بخوری سر چی بوده؟",
    "🧼80.شات از نتایج گوگلت",
    "🧼81.چشای کیو تو گپ میبوسی و لبای کیو؟(دونفرمتفاوت)",
    "🧼82.رو کسی کراش داری؟",
    "🧼83.کدومش بدتره؟(موجودی شما کافی نمیباشد)_(اینترنت شما به اتمام رسید)",
    "🧼84.شات از لیست پیوی هات",
    "🧼85.شات از پیوی کسی ک زیاد باهاش میچتی و تو این گپه.",
    "🧼86.روز شانست کدومه؟",
    "🧼87.میوه مورد علاقت؟",
    "🧼88.چیو ب ماها دروغ گفتی؟",
    "🧼89.تا حالا شده بخاطر یکی از بچه های این گپ گریه کنی؟یا ناراحت شی بخاطرش؟",
    "🧼90.زیرلباست چ رنگیه؟",
    "🧼91.لجبازی؟",
    "🧼92.تا چند سالگی تو کوچه بازی میکردی؟",
    "🧼93.ب کسی علاقه داشته باشی ولی نتونی بگی.بش کم محلی میکنی یا بیشتر حسادت میکنی؟",
    "🧼94.یکی از فحشایی ک زیاد استفادش میکنی چیه؟",
    "✨🤍1.تاریخ تولدت؟",
    "✨🤍1.اسم اکست؟",
    "✨🤍2.اکستو هنوز دوس داری؟",
    "✨🤍3.رل داری؟",
    "✨🤍4.عشق یعنی چی؟",
    "✨🤍5.رل بزنیم!",
    "✨🤍6.روتین ی روزت!",
    "✨🤍7.حیوون مورد علاقت؟",
    "✨🤍8.ب کی حسودیت میشه؟",
    "✨🤍9.اسمو یکی از بچه های گپو ت ویس بگو دوست دارم!(جنس مخالف)",
    "✨🤍10.تایپت؟",
    "✨🤍11.عکس از صفحه چت های روبیکات!",
    "✨🤍12.عکس از پیام های ذخیره شدت!",
    "✨🤍13.زندگی رو از نگاه خودت تعریف کن!",
    "✨🤍14.من برات مهمم؟",
    "✨🤍15.اکثر دردودلات با کدوم بچه های گپ؟",
    "✨🤍16.احمقانه ترین حرفی ک ب رلت یا اکست زدی و بعدش پشیمون شدی چی بوده؟",
    "✨🤍17.دوس داری کیو کلا از زندگیت پاک کنی؟",
    "✨🤍18.عاشق شدی؟",
    "✨🤍19.از عشقت بگو!",
    "✨🤍20.اگر قرار باشد ب مدت یک هفته با یکی از اعضای گروه رل باشی اون کیه؟",
    "✨🤍21.جذاب ترین دخترا کلاس(جمع یا مدرسه)کدامند؟",
    "✨🤍22.همین الان ب کراشت اعتراف کن دوسش داری!(شات بده)",
    "🤍✨23.اهنگ قفلیت؟(اسمش)",
    "✨🤍24.بریم بیرون!",
    "✨🤍25.اسم کراشت؟",
    "✨🤍26.دلتو شکست تاحالا؟",
    "✨🤍27.استیکر مورد علاقت!",
    "✨🤍28.خونتون کجاعه؟",
    "✨🤍29.ب کی اعتماد داری؟",
    "✨🤍30.از ت خالگریت عکس بده!",
    "✨🤍31.شماره اکستو داری؟(شات بده ا اسمی ک ذخیره کردی)",
    "✨🤍32.عکس از نتایج گوگلت!",
    "✨🤍33.اگر بگم عاشقتم چکار میکنی؟!",
    "✨🤍34.اخرین باری ک گریه کردی کی بود؟",
    "✨🤍35.بزرگترین زخم چیه؟",
    "✨🤍36.کی بیشتر ت گپ بهت توجه میکنه؟",
    "✨🤍37.منو توصیف کن",
    "✨🤍38.وارد خونتون ک میشی دوس داری اولین نفر کیو ببینی؟",
    "🤍✨39.عشقت خیانت کنه و برگرده بگ پشیمونه،جوابت چیه؟",
    "✨🤍40همیشه اولین اهنگی ک میری سراغش کدومه؟",
    "✨🤍41.تو گپ کیو دوس داری بیشتر باهات چت کنه؟(جنس مخالف",
    "✨🤍42.احساس میکنی تو گپ کی بیشتر هواتو داره و ازت خوشش میاد؟جنس مخالف",
    "✨🤍43.شبا تو تاریکی مطلق میخوابی یا چراغ روشن میکنی؟",
    "✨🤍44.ی دروغ بهم بگو؟",
    "✨🤍46.قشنگ ترین فیلم ترکی که دیدی رو اسمش بگو",
    "✨🤍47.وقتی اعصبانی میشی چیکار میکنیـ",
    "✨🤍48.امانت دار خوبی هستی یان",
    "✨🤍49تو اتاقت ساعت داریـ",
    "✨🤍50.دوست داری کیا بیان تولدت!",
    "✨🤍51.اگ یکیو بگن چشم بسته میاریم هرچقد دوس داری بوسو بغلش کن،میخوای کی باشه؟",
    "✨🤍53.کیک خامه‌ای یا شکلاتی؟",
    "✨🤍54.تحمل گشنگیو نداری یا تشنگیو؟",
    "✨🤍55.اخلاقت؟",
    "✨🤍56.دوس داری با کی ازدواج کنی؟",
    "✨🤍57.معدل پارسالت؟",
    "✨🤍58.داخل کفش یکی از افراد گروه رو بو بکش!",
    "✨🤍59.کفشاتو دستت کن!",
    "✨🤍60.غذا مورد علاقت؟",
    "✨🤍61.عشق یا پول",
    "✨🤍62.عشقم میشی؟!",
    "✨🤍63.با خودت تو خلوت‌هات حرف میزنی؟",
    "✨🤍64.اگ بگم ازت خوشم میاد چی میگی؟",
    "✨🤍65.بود و نبودم مهمه؟چرا؟",
    "✨🤍66.گریه هات پنهونیه یا راحتی جلو هرکسی میتونی گریه کنی؟",
    "✨🤍67.چندتا رل داشتی؟",
    "✨🤍68.خونه زندگی مجلل یا ساده؟",
    "✨🤍69.همسر زرنگ یا خنگ؟",
    "✨🤍70.بهترین اتفاق زندگیت؟",
    "✨🤍71.بدترین اتفاق زندگیت؟",
    "✨🤍72.برو یکیو ایسگا کن بگو عاشقتم(شات بد)",
    "✨🤍73.زنگ بزن یا پیام بده به عشقت و بگودیشب مست بودی و صبح تو بغل یه دختره بیدار شدی و هیچی یادت نیس...",
    "✨🤍75.بنظرت چجوری میشه به یکی فهموند که دوسشداری ؟",
    "✨🤍76.تا حالا شده سر یچیز الکی با رلت کات کنی ؟",
    "✨🤍77.میدونی بی دی اس ام چیه؟",
    "✨🤍78.چه فوبیایی داری ؟",
    "✨🤍79.برف یا بارون؟",
    "✨🤍80.دوس داری با کی برف بازی یا زیر بارون قدم بزنی؟(از اعضای گروه بگو حتمااا)",
    "✨🤍81.زندگیتو دوس داری؟",
    "✨🤍82.از من بدت میا؟",
    "✨🤍83.اسم کراشت؟",
    "✨🤍84.رو بچه های گرو رو کی کراشی؟(حتما باید یکیو بگی)",
    "✨🤍85.رنگ مورد علاقت!",
    "✨🤍86.از کی بدت میا؟",
    "✨🤍87.دوس داری کادو چی بگیری؟",
    "✨🤍88.دوس داری بهترین کادو از کی باشه؟",
    "✨🤍89.من برا ت ب عنوان چیم؟",
    "🤍✨90.مدرسرو دوس داری؟",
    "✨🤍91.ت زندگیت از چی بدت میاد؟",
    "✨🤍92.ت زندگیت از کی بدت میاد؟",
    "🦕1.تاحالا کسی رو از عمد نادیده گرفتی",
    "🦕2.به کسی حسادت میکنی",
    "🦕3.موی فر یا لخت",
    "🦕4.قد کوتاه یا بلند",
    "🦕5.تیشرت یا پیراهن",
    "🦕6.شماره تلفنتو بده",
    "🦕7.اسم بابات",
    "🦕8.عجیب ترین چیزی که تو گوگل سرچ کردی",
    "🦕9.اینترنت یا دوستات",
    "🦕10.دوست داری هرسال خونه تو عوض کنی",
    "🦕11.اگه بخوای فقط یه غذا تا اخر عمرت بخوری اون چیه",
    "🦕12.رو پسر عمت یا پسر عموت کراشی",
    "🦕13.چند تا خاله داری",
    "🦕14. شات از سابقه ی گوگلت",
    "🦕15.کدوم یک از اقوامتو بیشتر دوست داری",
    "🦕16.از کدوم یک از فامیلات بدت میاد",
    "🦕17.اسم روستاتون",
    "🦕18.اصالتت کجاییه",
    "🦕19.پیج اینستات",
    "🦕20.پین روبیکات کیه",
    "🦕21.یکی از چنلایی که دوسش داری",
    "🦕22.از کی وایپ خوبی میگیری",
    "🦕23.چرت ترین استیکری که وجود داره",
    "🦕24.ویس بگیر یک دقیقه صدای خروس در بیار",
    "🦕25.زنگ بزن به یکی و رندوم بگو ازت حامله ام",
    "🦕26.به مامانت بگو میخوام با زیدم اشنات کنم",
    "🦕27.به بابات بگو لزم",
    "🦕28.یکی از ارزوهای بچگیت",
    "🦕29.خودتو تو چند جمله توصیف کن",
    "🦕30.نظرت درمورد پاریس",
    "🦕31.چند تا زبان بلدی",
    "🦕32.دختر ترک یا کرد",
    "🦕33.کردی یا ترک",
    "🦕34.لر یا بختیار",
    "🦕35.سگ یا گربه",
    "🦕36.اسم نزدیک ترین افراد زندگیت",
    "🦕37.شرم اور ترین حرکتت توی دیت چی بوده",
    "🦕38.چند بار رفتی دیت",
    "🦕39.اخرین دوروغی که به بابات گفتی",
    "🦕40.موجودی حسابت",
    "🦕41.دردناک ترین درد فیزیکیت",
    "🦕42.پین اینستات",
    "🦕43.یه فیلم رندوم از گالریت بفرست",
    "🦕44.یکی از خاطرات مزاحم تلفنیت رو بگو",
    "🦕45.یکی از خوبیات",
    "🦕46.یکی از بدیات",
    "🦕47.لقبت",
    "🦕48.چرند ترین لقب زندگیت رو کی بهت داد",
    "🦕49.به کی توی این جمع حسادت میکنی",
    "🦕50.تاحالا دزدی کردی",
    "🦕51.به خرافات باور داری",
    "🦕52.دلیل اولین جداییت",
    "🦕53.از جیب کسی پول برداشتی",
    "🦕54.لوس ترین حرفی که به پارتنرت گفتی",
    "🦕55.بدترین پیامی که تو این ماه گرفتی",
    "🦕56.اولین کراش سلبریتیت",
    "🦕57.استعداد پنهانت",
    "🦕58.بزرگترین نا امنیت",
    "🦕59.اخرین عکسی که برای پارتنرت ارسال کردی",
    "🦕60.ویس بگیر و اولین کلمه ای که به ذهنت میرسه رو بگو",
    "🦕61.از کدوم حیوان میترسی",
    "🦕62.فیلم ترسناک مورد علاقت",
    "🦕63.بزرگترین ترس دوران کودکیت",
    "🦕64.تاحالا روح دیدی",
    "🦕65.بدترین دروغی که به دوستت گفته",
    "🦕66.یکی از ترس های اجتماعی",
    "🦕67.سیگار کشیدی",
    "🦕68.سیگار یا قلیون",
    "🦕69.چه چیزی باعث خجالتت میشه",
    "🦕70.توی چه کاری خوب نیستی",
    "🦕71.فوبیای خاصی داری",
    "🦕72.عجیب ترین عادتی که داری",
    "🦕73.پایین ترین نمره ی کارنامت",
    "🦕74.گرون ترین چیزی که داری",
    "🦕75.به کدوم کشور دوست داری مهاجرت کنی",
    "🦕76.بهترین معلمی که داشتی",
    "🦕77.مدرک تحصیلیت",
    "🦕78.تاحالا راز دوستت رو به کسی گفتی",
    "🦕79.چند تا بچه دوست داری",
    "🦕80.به یکی رندوم پیام بده بگو( جواب ازمایش اومده ازت حاملم)",
    "💛1.تاکسی سوار شدی؟",
    "💙2.کی دوست داره بنظرت؟",
    "💜3.وروجک کی هستی؟",
    "🩶4.راجب من فکر بد کردی؟",
    "❤5.از من چه تصوری تو ذهنت داری؟",
    "❤️‍🩹6.عشق یا پول؟",
    "💙7.تا حالا از کسی کتک خوردی؟",
    "🩶8.از صفحه چتت با رلت،دوستت یا کراشت شات بده.",
    "❤️‍🔥9.حاضری از تشنگی بمیری یا گشنگی؟",
    "💖10.اسم دختر داییت چیه؟",
    "🫶11.قشنگترین اسم پسر به نظرت؟",
    "❤12.قشنگترین اسم دختر به نظرت؟",
    "💞13.اسم دوست صمیمیت چیه؟",
    "💙14.اسم خواننده مورد علاقت؟",
    "🧡15.اسم اهنگی که دوس داری چیه؟",
    "💜16.اول اسم کراشت/رلت چیه؟",
    "❤️‍🩹17.چه عددیو دوس داری؟",
    "💖18.خوشگلترین دختر گپ؟",
    "🖤19.چه رنگی دوس داری",
    "❤️‍🔥20.رو کی کراشی تو گپ؟",
    "💕21.از چی خودت بدت میاد؟",
    "❤️‍🩹22.یه عکس که خیلی دوس داری بفرس",
    "💞23.دوس داری کیو کلا از زندگیت پاک کنی؟",
    "💜24.دوس داشتی به غیر این اسمت چی باشه؟",
    "🩶25.دوس داری بری کجا؟",
    "🧡26.از شب خوشت میاد یا روز؟",
    "❤️‍🩹27.بهترین خاطره زندگیت چیه؟",
    "🔥28.بدترین خاطره زندگیت چیه؟",
    "👫29.تا حالا عاشق شدی؟",
    "💢30.اهل کجایی؟",
    "💟31.کدوم غذارو دوس داری؟",
    "🫀32.از کدوم غذا بدت میاد؟",
    "💚33.خواهر برادر داری؟",
    "❤34.خواهرزاده داری یا برادر زاده؟",
    "🖤35.پسر یا دختر؟",
    "💖36.لقبت؟",
    "💜37.اخلاقت؟",
    "💞38.دوس داری با کی ازدواج کنی؟",
    "💚39.آدرس دقیق خونتون؟(لوکیشن بده)",
    "💖40معدل پارسالت؟",
    "🖤41.میوه مورد علاقت؟",
    "🤎42.فامیلیت؟",
    "❤️‍🔥43.کشور مورد علاقت؟",
    "💙44.عکستو بفرس پی",
    "💚45.برو پی یه نفر فهش بدع",
    "❤46.ویس بدع و بگو سلام",
    "💞47.به ورزش علاقه داری؟",
    "🩶48.اهنگ مورد علاقت؟",
    "💚49.بهترین مسافرتت؟",
    "🧡50.بهترین منطقه شهرت؟",
    "💜51.شوهر مورد علاقت؟",
    "💖52.بازیگر مورد علاقت کیه؟",
    "💙53.شغل مورد علاقه خودت چیه؟",
    "💕54.شغل مامان،بابات چیه؟",
    "🤎55.وضعیت الانت رو توصیف کن.",
    "❤56.تاریخ تولدت؟",
    "💖57.مادرتو بیشتر دوس داری یا پدرتو؟",
    "❤️‍🔥58.تصورت از عشق؟",
    "🩶59.بازیگر مورد علاقت؟",
    "❤️‍🩹60.اسکرین از یکی از کلاس های شبکه شادت",
    "💚61.عکس دستتو بفرست.",
    "💜62.بهترین سیاره در نظرت؟",
    "💖63.تایلند یا انگلیس؟",
    "🖤64.یه فیلم کوتاه از خودت بفرس.",
    "❤️‍🔥65.پول یا سلامتی یا عشق؟",
    "🤎66.توی آشناهات رو کی بیشتر کراشی؟",
    "💖67.رنگ مورد علاقت؟",
    "💜68.ماشین مورد علاقت؟",
    "💚69.میای بیرون باهام؟",
    "💛70.قد و وزنت؟",
    "🧡71.غذایی که نمیتونی بخوری چیع؟",
    "❤️‍🩹72.یه ویس بده.",
    "❤73.بزرگترین ترست چیع؟",
    "💖74.تیکه کلامت؟",
    "🤎75.کدوم عضو گروه بیشتر دعوا میکنه؟",
    "💕78.حاضری به خاطر نجات جون عشقت ترکش کنی؟",
    "❤️‍🩹79.خودتو چقد دوس داری؟",
    "💛80.احساسات نسبت به خانوادت؟",
    "💜81.تا حالا خاستگار داشتی یا رفتی؟",
    "💚82.ویس بده صدای ی حیون در بیار",
    "❤️‍🩹83.تا حالا با فیلم گریه کردی؟",
    "🧡84.بزرگترین اتفاق زندگیت؟",
    "🩶85.رل داری یا داشتی؟",
    "💜86.عطر مورد علاقت؟",
    "❤87.دوس داری الان ازدواج کنی؟",
    "💖88.رقاص خوبی هستی تو عروسیا؟",
    "💕89.خوشتیپی یا خوش‌قیافه؟",
    "👫90.دلیل رل نزدنت؟",
    "❤91.به مامانت گفتی رل داری؟",
    "🤎92.نماز خوندی؟",
    "💖93.فدات بشم؟",
    "💚94.از 1تا100چنتا دوسم داری؟",
    "🧡95.تا حالا بهم دروغ گفتی؟",
    "💔96.از چیع من خوشت میاد؟",
    "💜97.از چیه من بدت میاد؟",
    "💞98.چرا روم کراش نیستی؟",
    "❤99.پسرارو توصیف کن",
    "💚1.آخرین باری که دلت واسه کسی تنگ شده کی بوده بهش گفتی؟",
    "💚2. تا حالا کسی بوده که وقتی نگاهش می‌کردی دلت آروم می‌گرفت؟",
    "💚3.یه نفرو فقط با یه نگاه دوست داشتی یا حس خاصی نسبت بهش گرفتی؟",
    "💚4.کسی که هنوز دوسش داری با اینکه رابطتتون بهم‌خورده",
    "💚5.اگه الان می‌تونستی یکیو بغل کنی کیو بغل میکردی",
    "💚6.بدترین شکست عشقی یا احساسیی که داشتی چی بود؟",
    "💚7.اگه اون کسی که توی دلت هست همین الان بخواد باهات حرف بزنه اولین چیزی که بهش می‌گی چیه؟",
    "💚8.تا حالا کسی باعث شده خودتو بهتر بشناسی؟",
    "💚9. بخاطر علاقه کسی خودتو تغییر دادی؟",
    "💚10. کسی هست که با فکر کردن بهش هنوز لبخند بزنی؟",
    "💚11.یه چیزی که همیشه دلت می‌خواست بگی ولی هیچ‌وقت نگفتی چیه؟",
    "💚12.یه لحظه یا یه اتفاق بود که حس کردی دنیا فقط مال تو و اون لحظست؟",
    "💚13.فکر می‌کنی عشق واقعی وجود داره؟",
    "💚14.بزرگ‌ترین ترس تو در رابطه‌های عاطفی چیه؟",
    "💚15.دوست داری تو چه سنی بمونی",
    "💚16.چی باعث میشه به یکی اعتماد کنی",
    "💚17.آخرین کسی که دلت براش تنگ شد؟",
    "💚18.تا حالا عاشق شدی؟",
    "💚19.کسی که دوست داری همین الان ببینی؟",
    "💚20.از چی بیشتر می‌ترسی؟",
    "💚21.بهترین لحظه زندگیت کی بود؟",
    "💚22.یه آرزوی بزرگت؟",
    "💚23. چیزی که هنوز پشیمونی ازش؟",
    "💚24.غذایی که خیلی خوب بلدی درست کنی",
    "💚25.چیزی که همیشه آرزو داشتی ولی نداشتی؟",
    "💚26.آخرین بار کی گریه کردی؟",
    "💚27.یه لحظه که دوست داشتی زمان متوقف بشه؟",
    "💚28.چیزی که همیشه جلوی بقیه پنهان می‌کنی؟",
    "💚29.تا حالا شده از کسی متنفر بشی؟",
    "💚30.اگر یه روز وقت اضافه داشتی چیکار می‌کردی؟",
    "💚31.یه جمله‌ای که همیشه یادت می‌مونه؟",
    "💚32.مهم‌ترین کسی که تو زندگیت داری؟",
    "💚33.چیزی که هیچ‌وقت حاضر نیستی از دستش بدی؟",
    "💚34.وقتی دلت می‌گیره چیکار می‌کنی؟",
    "💚35.اسم بهترین دوستت",
    "💚36.جمله‌ای که دوست داری از ینفر بشنوی؟",
    "💚37.وقتی عاشق می‌شی چه حسی تو دلت میاد؟",
    "💚38.کسی هست که هنوز منتظرشی؟",
    "💚39.چیزی که هیچ‌کس دربارت نمی‌دونه؟",
    "💚40.اسم کسی که هنوزم وقتی می‌شنویش یه حالی میشی؟",
    "💚41.حالا شده بخوای ناپدید شی برای یه مدت؟",
    "💚42.اگه یکی الان بگه دوستت دارم اولین فکری که می‌کنی چیه؟",
    "💚43.از کی بیشتر از همه انتظار داشتی ولی ناامیدت کرد؟",
    "💚44.یه چیزی که باعث می‌شه بغض کنی؟",
    "💚45.چی باعث می‌شه تو سکوتت بهم بریزی؟",
    "💚46.تا حالا دلت خواسته برگردی عقب و فقط بغلش کنی",
    "💚47.آخرین باری که واقعا خوشحال بودی کی بود؟",
    "💚48.یه حسی که خیلی وقته تجربش نکردی؟",
    "💚49.اسم کراش رفیقت",
    "💚50.وقتی کسی دوستت داره ولی تو حسی بهش نداری چی کار می‌کنی؟",
    "💚51.چیزی که اگه کسی در موردت بدونه شوکه میشه؟",
    "💚52.کسی که دلت می‌خواست تو زندگیت می‌موند اما ننموند؟",
    "💚53.سخت‌ترین تصمیمی که تا حالا گرفتی چی بوده؟",
    "💚54.چیزی هست که هنوز نتونستی خودتو بابتش ببخشی؟",
    "💚55.با جمله تو با همه فرق داری چه حسی بهت دست میده؟",
    "💚56.حالا با تمام وجودت برای یه نفر دعا کردی؟",
    "💚57.اگه الان بتونی یه جا فرار کنی کجاست؟",
    "💚58.شیرکاکائو یا چیبس",
    "💚59.یه جمله که خیلیا بهت گفتن ولی تو باورش نداری؟",
    "💚60.تا حالا شده به کسی فکر کنی و همون لحظه پیام بده؟",
    "💚61.کسی هست که هیچ‌وقت نمی‌تونی ازش دل بکنی؟",
    "💚62.یه چیز کوچیک که خوشحالت می‌کنه",
    "💚63.حالتو بروز میدی یا نه",
    "💚64.اگه می‌تونستی یبار دیگه یکیو ببینی اون کی بود",
    "💚65.دختر عمه داری چند سالشه",
    "💚66.اگه بتونی خودتو به کودکیت برسونی چی بهش میگی؟",
    "💚67.یه چیزی که هیچ‌وقت دلت نیومد از دست بدی؟",
    "💚68.چیو به راحتی از دست دادی",
    "💚69.تو حموم چیکار میکنی",
    "💚70.یه عکس از چشات",
    "💚71.میبخشی یا انتقام میگیری",
    "💚72.حالا حس کردی توی دنیایی هستی که توش جایی نداری؟",
    "💚73.اگه می‌تونستی یه پیام به همه‌ی دنیا بدی چی میگفتی؟",
    "💚74.دوست داری کیو کلا محو کنی",
    "💚75.کی خیلی بد از چشمت افتاد",
    "💚76.بزرگ‌ترین اشتباهی که ازش درس گرفتی چی بوده؟",
    "💚77.عروسی کی بیشتر بهت خوش گذشته",
    "💚78.چی باعث میشه یکی از چشمت بیوفته",
    "💚79.تفریح با کیو خیلی دوست داری",
    "💚80.اگه می‌تونستی یه جا تا آخر عمرت بمونی کجا میموندی",
    "🎏1.کدوم عمتو بیشتر دوست داری؟",
    "🎏2.چن تا عمو خاله داری؟",
    "🎏3.اسم دایی هاتو بگو؟",
    "🎏4.دوست داری جشن عروسیت چجوری برگذار شه",
    "🎏5.شام عروسیت دوست داری چی باشه",
    "🎏6.میوه شب عروسیت چیا باشه",
    "🎏7.دوست داری چجوری لباس بپوشم",
    "🎏8.اهل مسافرت رفتن هستی یا نه",
    "🎏9.سفر با خانواده یا تنها یا دوستات",
    "🎏10.عروسیت تو تالار باشه یا باغ یا خونه",
    "🎏11.ماشین مهم تره یا خونه",
    "🎏13.عاشق شدی",
    "🎏14.فکر میکنی دل کیو شکوندی",
    "🎏16.بدترین اتفاق زندگیت",
    "🎏17.بهترین اتفاق زندگیت",
    "🎏18.چقدر به عشق اعتماد داری",
    "🎏19.از صفحه پیام های زخیره شده روبیکات شات بده",
    "🎏20.عشقت یا رفیقت",
    "🎏21.رفیقت یا خانوادت",
    "🎏22.از ناخن هات عکس بده",
    "🎏23.از صفه چت روبیکات شات بده",
    "🎏24.با مامانت راحت تری یا بابات",
    "🎏25.همسر بهتره یا فرزند",
    "🎏26.اگه منو تو داخل اتاق تنها شیم چیکار میکنی",
    "🎏27.یه جوک بگو",
    "🎏28.دوست داری با کی بری شهر بازی",
    "🎏29.تا حالا جایی از بدنت رو با تیغ زدی",
    "🎏30.از آخرین پیامت با رفیق صمیمیت شات بده",
    "🎏31.تا به حال به همسرت  مخاطب خاصت خیانت کردی",
    "🎏32.اصلی‌ترین چیزی که توی جنس مقابل برای تو جذابه چیه",
    "🎏33.معیارهات برای ورود به یک رابطه چی هستن",
    "🎏34.در مورد اولین تجربه‌ی عاشقانه‌ت بگو.",
    "🎏35.یه قسمت خنده‌دار از اولین تجربه‌ی پرحرارت زندگیت رو تعریف کن",
    "🎏36.بدترین ویژگی بغل دستیت چیه؟",
    "🎏37.اگه فقط ۲۴ ساعت از زندگیت مونده باشه، دوست داری به کی ابراز محبت کنی و اولین نفری که بهش در مورد مرگت خبر می‌دی کیه",
    "🎏38.دوستم داری؟",
    "🎏41.اسم کسی که توی این جمع خیلی خیلی دوسش داری چیه ؟",
    "🎏42.زیباترین خاطرت با کیه ؟",
    "🎏43.پنج خصوصیت ویژه ای که رابطه تو باید داشته باشه رو نام ببر؟",
    "🎏44.به شریکت بگو که چه ویژگی هایی رو در اون دوست داری",
    "🎏45.سخترین و تلخ ترین لحظات زندگیت با عشقت و بازگو کن .",
    "🎏46.در چه مورد دوست نداری کسی با عشقت شوخی کنه ؟",
    "🎏47.اولین برداشت تو از عشقت چه بوده؟",
    "🎏48.بهترین ویژگی‌ فیزیکی عشقت چیست؟",
    "🎏49شیطنت و بازی کردن در رخت خواب را دوست داری ؟",
    "🎏50.دوست داری چندتا بچه داشته باشی؟",
    "🎏51.اسم رلت؟",
    "🎏52.اهنگی که دوس داری؟",
    "🎏53.سریالی که دوست داری؟",
    "🎏54.قاب گوشیت چه مدلیه؟",
    "🎏55.لباس مامانت بیستر دوست داری یا بابات؟",
    "🎏56.چه نوع کفشی خوشت میاد؟",
    "🎏57.چنتا هنذفری داری؟",
    "🎏58.شراب میخوری؟",
    "🎏59.پیتزا چقد دوست داری؟",
    "🎏60.چنتا درس تجدید شدی؟",
    "🎏61.برای عید کجا میرین؟",
    "🎏62.گرمای هستی؟",
    "🎏63.سرمایی هستی؟",
    "🎏64.از چی من بدت میاد؟",
    "🎏65.از چی من خوشت میاد؟",
    "🎏66.عکس موهات بفرست؟",
    "🎏67.موهات چه رنگی؟",
    "🎏68.چشمات چه رنگیه؟",
    "🎏69.سیگار میکشی؟",
    "🎏70.من ادم بدی هستم یا نه؟",
    "🎏71.برای اینکه جذاب به نظر برسی چه کار می‌کنی؟",
    "🎏72.در حال حاضر از کی خوشت میاد؟",
    "🎏73.اگر می‌تونستی یک چیز در بدنت رو تغییر بدی اون چی بود؟",
    "🎏74.به کی حسودی می‌کنی؟",
    "🎏75.پنج پسر اولی که به نظرت جذابن رو نام ببر؟",
    "🎏76.جذابترین چیز در مورد مرد‌ها چیه؟",
    "🎏77.آیا با کسی که از تو کوتاهتر باشه ازدواج می‌کنی؟",
    "🎏78.از کی بیشتر از همه بدت میاد؟",
    "🎏79.تا به حال به برادر دوستات احساسی داشتی؟",
    "🎏80.از کدوم بازیگر خوشت میاد؟",
    "🎏81.از بین پسرای این جمع، کی از همه جذابتره؟",
    "🎏82.اگر می‌شد پسر بشی، چکار می‌کردی؟",
    "🎏83.کسی تا به حال تورو لخت دیده؟",
    "🎏84.آیا شب‌ها با لباس زیر می‌خوابی؟",
    "🎏85.کی توی این جمع از همه خنده‌دارتره؟",
    "🎏86.از نظر جذابیت به من از یک تا ۱۰ چه نمره‌ای میدی؟",
    "🎏87.اگر بتونی به یک سفر رمانتیک بری، چه کسی رو توی این جمع به عنوان همسفر انتخاب می‌کنی؟",
    "🎏88.ایده برای سوالات جرات حقیقت از پسران",
    "🎏89.اگر می‌تونستی نامرئی بشی چکار می‌کرد",
    "🎏90.جذابترین دختران کلاس (جمع یا مدرسه) کدامند",
    "💤1.کشور مورد علاقت؟(دلیل)",
    "🦋2. اسم رلـتو بگو؟",
    "💤3.حاضری ده سال از عمرتو بدی به عشقت؟",
    "🦋4.برو تو گالریت اسکرین بفرس.",
    "💤5.عشق یا پول؟",
    "🦋6.حاضری از تشنگی بمیری یا گشنگی؟",
    "💤7.اسم دوست صمیمیت چیه؟",
    "🦋8.اسم خواننده مورد علاقت؟",
    "💤9.اسم اهنگی که دوس داری چیه؟",
    "🦋10.از چی خودت بدت میاد؟",
    "💤11.قشنگترین اسم پسر به نظرت؟",
    "🦋12.قشنگترین اسم دختر به نظرت؟",
    "💤13.اسم دوست صمیمیت چیه؟",
    "🦋14.اسم خواننده مورد علاقت؟",
    "💤15.اسم اهنگی که دوس داری چیه؟",
    "🦋16.اول اسم کراشت/رلت چیه؟",
    "💤17.چه عددیو دوس داری؟",
    "🦋18.خوشگلترین دختر گپ؟",
    "💤20.رو کی کراشی تو گپ؟",
    "🦋21.به تعداد درصدشارژ گوشیت، سکه طلا بدم برای مهریه، راضی زنم بشی؟",
    "💤22.رل میزنی بام؟",
    "🦋23.دوست داری چند سالگی ازدواج کنی؟",
    "💤24.خاله داری؟",
    "🦋25.شوگر مامی چیه؟",
    "💤26.شوگر ددی چیه؟",
    "🦋27.اسم مامان؟ بابا؟",
    "💤28.عشق یا پول؟",
    "🦋29.اسم دختر داییت چیه؟",
    "💤30.بهترین اسم پسر به نظرت؟",
    "🦋31.کدوم درست تجدید شدیـ",
    "💤32.گرما بیشتر دوست داری یا سرما",
    "🦋33.چه مدل گلی دوست داریـ",
    "💤34.گل و درخت بیشتر دوست داری با حیواناتـ",
    "🦋35.فصل چی بدنیا اومدیـ",
    "💤36.ماه چی به دنیا اومدیـ",
    "🦋37.از کدوم همکلاسیت متنفریـ",
    "💤38.از کدوم همکلاسیت خوشت میاد",
    "🦋39.کدوم مدیر تو بیشتر دوس داریـ",
    "💤40.کدوم یک از سیارات بیشتر دوست داریـ",
    "🦋42.از رنگ تیره خوشت میاد یا روشنـ",
    "💤43.بیشتر لباس تیره میپوشی یا روشنـ",
    "🦋44.قدت بلنده یا کوتاه",
    "💤45.ماشین مورد علاقه ات چیه",
    "🦋46.سریال کره ای نگاه میکنیـ",
    "💤47.خنده دار ترین سریال هندی که دیدی چیه",
    "🦋48.طنز ترین خاطره ای که داری بگو",
    "💤49.دکور اتاقت چه رنگیـ",
    "🦋50.رپی سی دی تا حالا نقاشی کشیدیـ",
    "💤51تاحالا گوشی بردی مدرسه بعد لو بری تعریف کن",
    "🦋52بیشتر اوقات گریه میکنی یا عصبانی میشی",
    "💤53رنگ مورد علاقه ات",
    "🦋54چند بار با رفیقت دعوات شده",
    "💤55لباس عیدت چه رنگی",
    "🦋56چه رنگی شلوار خریدی",
    "💤57چند تا لاک داری",
    "🦋58چند تا کفش داری",
    "💤59کفش برا عید چی خریدی",
    "🦋60صدات چشکلیه",
    "💤61.آهنگ مورد علاقت چیه؟",
    "🦋62.برای اینکه نظر دختر / پسری رو به خودت جلب کنی چکار می‌کنی؟",
    "💤63.تا حالا با چند نفر وارد دوستی شدی؟",
    "🦋64.به چه کسی توی این جمع حسادت می‌کنی؟",
    "💤65.تا حالا خواب منو دیدی؟",
    "🦋66.از گفتن چه چیزی به من بیش از همه می‌ترسی؟",
    "💤67.اگر هرچیزی که می‌خواستی رو می‌تونستی بخری، چی می‌خریدی؟",
    "🦋68.بدترین قرارت با یه پسر چطوری بوده؟",
    "💤69.تا به حال از دوست‌ پسر یا دوست‌ دختر دوستت خوشت اومده؟",
    "🦋70.تا به حال شده پسری که دوستش داری بفهمه، و بهت جواب منفی بده؟",
    "💤71. عشقت جلو چشات بهت خیانت کرده؟؟؟",
    "🦋72.تاحالا ماشین روندی؟؟",
    "💤73.زنگ بزن به دوستت و بگو ادم کشتی نمیدونی باید چیکار کنی..!",
    "🦋74.موی کسی که  تو گپ روش کراشی رو بردار و بزار پشت گوشیت..",
    "💤75.بچه دوست داری",
    "❤️‍🩹2.آخرین باری که یه تیکه از غذاتو انداختی روی زمین، چقدر طول کشید تا برش داری و بخوریش؟",
    "❤️‍🩹3.تا حاال توی استخر غرق شدی؟",
    "❤️‍🩹4.نظرتو راجب خودت بگو؟",
    "❤️‍🩹5.چند تا از چیزهایی که وقتی تنها هستی بهشون فکر می کنی رو بگو؟",
    "❤️‍🩹6.وقتی تو سن رشد بودی، دوست خیالی داشتی؟",
    "❤️‍🩹7.آیا تا حاال موقع دیدن بخش های وحشتناک یه فیلم ترسناک، چشماتو گرفتی؟",
    "❤️‍🩹8.تا حاال از گفتن چیزی ترسیدی؟ اون چی یوده",
    "❤️‍🩹9.یکی ااز افتخارات احمقانه‌انت بگو رو نام ببر!",
    "❤️‍🩹10.بهترین عادتت چیه؟",
    "❤️‍🩹11.تا حاال با سر رفتی تو دیوار؟",
    "❤️‍🩹12.زیر دوش آواز می خونی؟",
    "❤️‍🩹13.دیگه چخبر؟",
    "❤️‍🩹14.احمقانه ترین اتفاقی که تو یه مکان عمومی برات افتاده، چی بوده؟",
    "❤️‍🩹15.تا حاال با خودت تو آینه حرف زدی؟",
    "❤️‍🩹16.وقتی می خوابی، کابوس میبینی یا رویا؟",
    "❤️‍🩹17.تو خواب حرف می زنی؟",
    "❤️‍🩹18.دوست مخفیت کیه؟",
    "❤️‍🩹19.به نظرت .....)اسم یک نفر در جمع(..... انسان خوبیه؟",
    "❤️‍🩹20.توی این جمع، کیو کم تر از بقیه دوست داری و چرا؟",
    "❤️‍🩹21.ادم رویاهات چه شکلیه؟",
    "❤️‍🩹22.از 1 تا 10 به قیافه خودت چند میدی؟",
    "❤️‍🩹23.از چی من بدت میاد؟",
    "❤️‍🩹24.آخرین پیامی که به کسی دادی چی بوده؟",
    "❤️‍🩹25.اگه همه ما توی یه ساختمون در حال آتش گرفتن باشیم و تو بتونی نجاتمون بدی، کیو نجات نمیدی؟",
    "❤️‍🩹26.تا حاال مخاط توی گوشت رو خوردی؟",
    "❤️‍🩹27.بهترین ترین کاری که تا حاال کردی، چی بوده؟",
    "❤️‍🩹28.مامانتو بیش تر دوست داری یا باباتو؟",
    "❤️‍🩹29.حاضری خواهر/برادرتو در ازای یک میلیارد دالر بفروشی؟",
    "❤️‍🩹30.اگه اجازه داشته باشی یه شهر دیگه زندگی کنی؟اون چه شهریه",
    "❤️‍🩹31.ترجیح میدی بدون این که کسی بدونه، زندگی 100 نفر رو نجات بدی، یا این که زندگی هیچ کسو نجات ندی اما همه بابتش تحسینت کنن؟",
    "❤️‍🩹32.اگه قرار باشه تا آخر عمرت فقط یه آهنگو گوش بدی، چه آهنگیه؟",
    "❤️‍🩹33.به نظرت په چیزی تو این دنیا مضخرفه؟",
    "❤️‍🩹34.زندگی بدون کولر یا بخاری یا اینترنت؟",
    "❤️‍🩹35.دوس داری الان کجا باشی؟",
    "❤️‍🩹36.اگه قرار باشه دوباره به دنیا بیای، دوست داری توی کدوم دهه به دنیا بیای؟",
    "❤️‍🩹37.اگه بتونی به گذشته برگردی و یکی از کارهایی که انجام دادی یا حرفایی که زدی رو پاک کنی، اون کار یا حرف چیه؟",
    "❤️‍🩹38.الان به چی فکر کردی؟",
    "❤️‍🩹39.اگه یه دفعه نامروی بشی، چیکار می کنی؟",
    "❤️‍🩹40.از خودت بگو",
    "❤️‍🩹41.اگه بخای بمیری ب کی چی میگی؟",
    "❤️‍🩹42.تبریز یا اصفحان؟",
    "❤️‍🩹43.استقلال پرسپولیسی؟",
    "❤️‍🩹44.چقد زندگی رو دوست داری؟",
    "❤️‍🩹45.چه ماهی به دنیا اومدی؟",
    "❤️‍🩹46.اسم صمیمی ترین دوستت؟",
    "❤️‍🩹47.حاضری از تشنگی بمیری یا گشنگی؟",
    "❤️‍🩹48.اسم خواننده مورد علاقت؟",
    "❤️‍🩹49.عدد شانست؟",
    "❤️‍🩹50.اهنگ مورد علاقتو بفرست!",
]

_raw_filtered = [c for c in raw_challenges if "روبیکا" not in c]
cleaned: List[str] = []
for _c in _raw_filtered:
    _c = re.sub(r'^[^\w\s]+[\d]+.\s*', '', _c).strip()
    _c = re.sub(r'^[^\w\s]+', '', _c).strip()
    if _c:
        cleaned.append(_c)

numbered_challenges = [f"{i+1}. {q}" for i, q in enumerate(cleaned)]
_color_circles = ["🔴", "🟠", "🟡", "🟢", "🔵", "🟣", "🟤", "⚪️", "⚫️"]


def random_challenge() -> str:
    q = random.choice(numbered_challenges)
    return f"{random.choice(_color_circles)} {q}"


# ---------------------------------------------------------------------------
# فال
# ---------------------------------------------------------------------------
_fals = [
    "الا یا ایها الساقی ادر کأسا و ناولها\nکه عشق آسان نمود اول ولی افتاد مشکل‌ها",
    "به بوی نافه‌ای کاخر صبا زان طره بگشاید\nز تاب جعد مشکینش چه خون افتاد در دل‌ها",
    "مرا به خاطر بس نقد دل می‌باید ای مطرب\nکه در خزانه فکرت چه گنج‌هاست نهان",
    "میازار موری که دانه‌کش است\nکه جان دارد و جان شیرین خوش است",
    "به حلاوت بخورم زهر که شاهد ساقی است\nبه ارادت بکشم درد که درمان هم از اوست",
    "درخت دوستی بنشان که کام دل به بار آرد\nنهال دشمنی برکن که رنج بی‌شمار آرد",
    "چه مبارک سحری بود و چه فرخنده شبی\nآن شب قدر که این تازه براتم دادند",
    "بیا تا گل برافشانیم و می در ساغر اندازیم\nفلک را سقف بشکافیم و طرحی نو دراندازیم",
    "دوش دیدم که ملائک در میخانه زدند\nگل آدم بسرشتند و به پیمانه زدند",
    "به عزم توبه سری داشتیم و پیمانه\nشکست بر سر توبه شرابخانه ما",
    "در دیر مغان آمد یارم قدحی در دست\nمست از می و میخواران از نرگس مستش مست",
    "ما در پیاله عکس رخ یار دیده‌ایم\nای بی‌خبر ز لذت شرب مدام ما",
    "ساقی به نور باده برافروز جام ما\nمطرب بگو که کار جهان شد به کام ما",
    "یارم چو قدح به دست گیرد\nبازار بتان شکست گیرد",
    "دلا بسوز که سوز تو کارها بکند\nنیاز نیم شبی دفع صد بلا بکند",
    "هر که را با خط سبزت سر سودا باشد\nپای از این دایره بیرون ننهد تا باشد",
    "چو بشنوی سخن اهل دل مگو که خطاست\nسخن شناس نه‌ای جان من خطا این جاست",
    "در این شب سیاهم گم گشت راه مقصود\nاز گوشه‌ای برون آی ای کوکب هدایت",
    "سحر بلبل حکایت با صبا کرد\nکه عشق روی گل با ما چه‌ها کرد",
    "بیا که قصر امل سخت سست بنیاد است\nبیار باده که بنیاد عمر بر باد است",
    "نقد صوفی نه همه صافی بی‌غش باشد\nای بسا خرقه که مستوجب آتش باشد",
    "ای دل غلام شاه جهان باش و شاه باش\nپیوسته در حمایت لطف اله باش",
    "روز هجران و شب فرقت یار آخر شد\nزدم این فال و گذشت اختر و کار آخر شد",
    "ما ز یاران چشم یاری داشتیم\nخود غلط بود آنچه می‌پنداشتیم",
    "تا ز میخانه و می نام و نشان خواهد بود\nسر ما خاک ره پیر مغان خواهد بود",
    "حافظ از دست مده دولت این کشتی نوح\nور نه طوفان حوادث ببرد بنیادت",
    "شبی که ماه مراد از افق شود طالع\nبود که پرتو نوری به بام ما بتابد",
    "کسی که حسن و خط دوست در نظر دارد\nمحقق است که او حاصل بصر دارد",
    "نه هر که چهره برافروخت دلبری داند\nنه هر که آینه سازد سکندری داند",
    "به دام زلف تو ای گل هزار بلبل مست\nبیا که نوبت عشرت ز باغ ما نرود",
    "ما را به رخت و چوب شبانی فریب داد\nدیوانه‌ای به راه زد و کودکانه‌ای",
    "دوش در حلقه ما قصه گیسوی تو بود\nتا دل شب سخن از سلسله موی تو بود",
    "رسید مژده که ایام غم نخواهد ماند\nچنان نماند چنین نیز هم نخواهد ماند",
    "کی رفته‌ای ز دل که تمنا کنم تو را\nکی بوده‌ای نهفته که پیدا کنم تو را",
    "برو ای زاهد خودبین که ز چشم من و تو\nراز این پرده نهان است و نهان خواهد بود",
    "هر که را جامه ز عشقی چاک شد\nاو ز حرص و عیب کلی پاک شد",
    "مردم دیده ما جز به رخت ناظر نیست\nدل سرگشته ما غیر تو را ذاکر نیست",
    "بگذار تا بگریم چون ابر در بهاران\nکز سنگ ناله خیزد روز وداع یاران",
    "هیچ‌کس نیست که افتاده آن‌جا که افتادم\nدر ره عشق که از چشم و دل و جان برخاستم",
    "ساقی بیا که یار ز رخ پرده برگرفت\nکار چراغ خلوتیان باز درگرفت",
    "گر چه راهیست پر از بیم ز ما تا بر دوست\nرفتن آسان بود ار واقف منزل باشی",
    "هزار جهد بکردم که یار من باشی\nمرادبخش دل بی‌قرار من باشی",
    "خوشا دلی که مدام از پی نظر نرود\nبه هر درش که بخوانند بی‌خبر نرود",
    "نقد دلی که بود مرا صرف باده شد\nتا جرعه‌ای ز جام جمشید یافته‌ام",
    "وقت آن شد که به سرچشمه شیرین بروم\nکز لب لعل تو یک قطره شکر ببروم",
    "ما آزموده‌ایم در این شهر بخت خویش\nبیرون کشید باید از این ورطه رخت خویش",
    "از خون دل نوشتم نزدیک دوست نامه\nمن دانم و دلم بس که با تو ناگزیرم",
    "ما و می و مطرب و این کنج خراب\nجان و دل و جام و جامه در رهن شراب",
    "دوش مرغ صبح‌خوان نغمهٔ حق سرود\nکاین شب دیرین سر آید صبح صادق باز رود",
    "بیا که ترک فلک خوان روزه غارت کرد\nهلال عید به دور قدح اشاره کرد",
    "به دام زلف تو دل مبتلا به خویشتن است\nبلاست عاشق و صبر از بلا به خویشتن است",
    "صبا به لطف بگو آن غزال رعنا را\nکه سر به کوه و بیابان تو داده‌ای ما را",
    "در این زمانه رفیقی که خالی از خلل است\nصراحی می ناب و سفینه غزل است",
    "ما سرخوشان مست دل از دست داده‌ایم\nهم عشق نام ماست و هم می پرست‌هایم",
    "در خرابات مغان نور خدا می‌بینم\nاین عجب بین که چه نوری ز کجا می‌بینم",
    "ما مخلصان خلوتیان رازدار دوست\nبا غیر دوست هر چه بگویند گفتنی است",
    "گر چه ما را ز می و جام و قدح ننگ آید\nپیش خم عشق تو این جمله قیامت باشد",
    "این که در جام جهان بین دیدم\nصد هزاران نکته در خم دیدم",
    "سحر با باد می‌گفتم حدیث آرزومندی\nخطاب آمد که واثق شو به الطاف خداوندی",
    "ای دل ار سیل فنا بنیاد هستی برکند\nچون تو را نوح است کشتیبان ز طوفان غم مخور",
    "بشنو این نکته که خود را ز غم آزاده کنی\nخون خوری گر طلب روزی ننهاده کنی",
    "ما را ز خیال تو چه پروای شراب است\nخم گو سر خود گیر که خمخانه خراب است",
    "عشقبازی و جوانی و شراب لعل فام\nجمهوری که آن همه ناز و تنعم خورد",
    "پیری رسید و موی سپید آمد از سفر\nآری سپیده دم خبر از آفتاب داد",
    "بیا که توبه ما را شکسته‌اند به می\nبه عذر نیکنامی که توبه‌نامه بسوخت",
    "حالیا مصلحت وقت در آن می‌بینم\nکه کشم رخت به میخانه و خوش بنشینم",
    "دوش وقت سحر از غصه نجاتم دادند\nواندر آن ظلمت شب آب حیاتم دادند",
    "روشنی طلعت تو ماه ندارد\nپیش تو برگ لاله رنگ ندارد",
    "زلف آشفته و خوی کرده و خندان لب و مست\nپیرهن چاک و غزل خوان و صراحی در دست",
    "نرگسش عربده جوی و لبش افسوس کنان\nنیم شب دوش به بالین من آمد بنشست",
    "سر فرا گوش من آورد به آواز حزین\nگفت ای عاشق دیرینه من خوابت هست",
    "عاشقی را که چنین باده شبگیر دهند\nکافر همه سحرخیزی او را نپسند",
    "شراب تلخ می‌خواهم که مردافکن بود زورش\nکه تا یک دم بیاسایم ز دنیا و شر و شورش",
    "ساقیا آمدن عید مبارک بادت\nوان مواعید که کردی مرود از یادت",
    "دیگر از قافله مردم چشمم اثری نیست\nرفته‌اند از نظر و اشک بمانده به نظاره",
    "بشنو از نی چون حکایت می‌کند\nاز جدایی‌ها شکایت می‌کند",
    "هر کسی از ظن خود شد یار من\nاز درون من نجست اسرار من",
    "از محبت خارها گل می‌شود\nوز محبت سرکه‌ها مل می‌شود",
    "ای برادر تو همه اندیشه‌ای\nمابقی خود استخوان و ریشه‌ای",
    "بنشین بر لب جوی و گذر عمر ببین\nکاین اشارت ز جهان گذران ما را بس",
    "دل هر ذره را که بشکافی\nآفتابیش در میان بینی",
    "صبر تلخ آمد ولیکن عاقبت\nمیوه شیرین دهد پرمنفعت",
    "توانا بود هر که دانا بود\nز دانش دل پیر برنا بود",
    "چو ایران نباشد تن من مباد\nبدین بوم و بر زنده یک تن مباد",
    "بنی آدم اعضای یک پیکرند\nکه در آفرینش ز یک گوهرند",
    "چو عضوی به درد آورد روزگار\nدگر عضوها را نماند قرار",
    "تو کز محنت دیگران بی‌غمی\nنشاید که نامت نهند آدمی",
    "مکن کاری که بر پا سنگت آید\nجهان با این فراخی تنگت آید",
    "چو دخلت نیست خرج آهسته‌تر کن\nکه می‌گویند سعدی زنده‌تر کن",
    "بس نامور به زیر زمین دفن کرده‌اند\nکز هستی‌اش به روی زمین بر نیامد باد",
    "دریغ آن نفس کز سر جهل رفت\nکه سرمایهٔ عمر در بیهده صرف شد",
    "ظاهراً گرگ و درون یوسف است\nصورتش دیو و درونش یوسف است",
    "خلق را چون آب دان صاف و زلال\nاندر او بنگر که می‌بینی تو حال",
    "دی شیخ با چراغ همی‌گشت گرد شهر\nکز دیو و دد ملولم و انسانم آرزوست",
    "ز دست دیده و دل هر دو فریاد\nکه هر چه دیده بیند دل کند یاد",
    "به می‌سجاده رنگین کن گرت پیر مغان گوید\nکه سالک بی‌خبر نبود ز راه و رسم منزلها",
    "شب تاریک و بیم موج و گردابی چنین هایل\nکجا دانند حال ما سبک‌باران ساحلها",
    "همه کارم ز خودکامی به بدنامی کشید آخر\nنهان کی ماند آن رازی کز او سازند محفل‌ها",
    "حضوری گر همی‌خواهی از او غایب مشو حافظ\nمتی ما تلق من تهوی دع الدنیا و اهملها",
    "چرا نه در پی عزم دیار خود باشم\nچرا نه خاک سر کوی یار خود باشم",
    "برو شیر درنده باش ای دغل\nمینداز خود را چو روباه شل",
    "دور مجنون گذشت و نوبت ما است\nکرشمه‌ای به سگ لیلی بکن که مرحبا",
    "سخن عشق نیست در دل من\nزخم عشق است بر تنم پیدا",
    "حاصل کارگه کون و مکان این همه نیست\nباده پیش آر که اسباب جهان این همه نیست",
    "در بیابان گر به شوق کعبه خواهی زد قدم\nسرزنش‌ها گر کند خار مغیلان غم مخور",
    "قطره دانش که بخشیدی ز پیش\nمتصل گردان به دریاهای خویش",
    "من از رندی نفهمم که درس عشق خواندم\nکه جرمم این بود که عشق می‌ورزم به پاکی",
    "بر سر آنم که گر ز دست برآید\nدست به کاری زنم که غصه سر آید",
]


def random_fal() -> str:
    beit = random.choice(_fals)
    lines = beit.split("\n", 1)
    if len(lines) == 2:
        return f"🪶 {lines[0]}\n   {lines[1]}"
    return f"🪶 {beit}"

# ---------------------------------------------------------------------------
# حکمت
# ---------------------------------------------------------------------------
_hekmat = [
    # ═══ علم، عقل و دانش ═══
    "هیچ ثروتی چون عقل و هیچ فقری چون نادانی نیست.",
    "بزرگ‌ترین فقر، نداشتن دانش و گرفتار بودن در نادانی است.",
    "حکمت، بالاترین شرافت است و نادانی، پایین‌ترین پستی.",
    "دانش از مال ارزشمندتر است؛ چراکه دانش از انسان نگهداری می‌کند، اما انسان باید مراقب مال و دارایی خود باشد.",
    "دانش میراثی گرانبها است و آداب زیورهایی همیشه تازه.",
    "حکمت گمشده مؤمن است، حکمت را فراگیر هر چند از منافقان باشد.",
    "سینه مرد عاقل صندوق اسرار اوست.",
    "اندیشه آینه‌ای شفاف است.",
    "چون عقل کامل گردد، سخن اندک شود.",
    "قلب احمق در دهان او، و زبان عاقل در قلب او قرار دارد.",
    "کسی که از گفتن «نمی‌دانم» شرمنده باشد، هلاک شود.",
    "نادان را یا تندرو یا کندرو می‌بینی.",
    "انسان خردمند کسی است که زبان خود را کنترل کند و پیش از انجام کار، درباره آن بیندیشد.",
    "جایگاه و ارزش هر انسان به اندازه مهارتی است که آن را به بهترین شکل انجام می‌دهد.",
    "هر ظرفی با چیزی که در آن ریخته می‌شود پر خواهد شد؛ مگر ظرف دانش که با افزودن آن، گشایش می‌یابد.",

    # ═══ زبان، سکوت و سخن ═══
    "توانا بود هر که دانا بود.",
    "زبان مانند درنده‌ای است که اگر آن را آزاد بگذاری، ممکن است به خودت آسیب برساند.",
    "آن که زبان را بر خود حاکم کند خود را بی‌ارزش کرده است.",
    "آن که راز سختی‌های خود را آشکار سازد خود را خوار کرده است.",
    "آن که جان را با طمع ورزی بپوشاند خود را پست کرده است.",
    "کسی که بیشتر شیفته سخن گفتن خویش است، سخن تو را نمی‌شنود.",
    "سخن نیکو و مختصر بگو؛ زیرا این برای تو زیباتر است و بر فضل تو دلالت بیشتری دارد.",

    # ═══ اخلاق فردی و خودسازی ═══
    "قناعت ثروتی است که هرگز پایان نمی‌یابد.",
    "همان چیزی را که برای خود نمی‌پسندی، درباره دیگران نیز روا مدار.",
    "خوش‌رفتاری و اخلاق نیک، موجب افزایش روزی و بیشتر شدن محبت میان انسان‌ها می‌شود.",
    "بخل ننگ است و ترس نقصان.",
    "صدقه داروی بیماری‌ها است.",
    "راستی، نجابت است.",
    "دروغ، ذلت است.",
    "دروغ انسان را هلاک می‌کند.",
    "حسادت، آفت دوستی است.",
    "کینه، بیماری دل است.",
    "عفت و پاکدامنی، زینت انسان است.",
    "میانه‌روی، مایه آسودگی است.",
    "خشم، آتش شیطان است.",
    "تندخویی، آفت است.",
    "نرمی، کلید موفقیت است.",
    "وفای به عهد، نشانه ایمان است.",
    "امانت‌داری از ایمان است.",
    "عجله، کلید پشیمانی است.",
    "هرگاه از چیزی ترسیدی، خود را در آن بیفکن؛ زیرا ترس از آن، سخت‌تر از خود آن است.",
    "انسان‌ها معمولاً با چیزی که نسبت به آن شناختی ندارند، مخالفت می‌کنند.",
    "انسانی که ارزش واقعی خود را بشناسد، حاضر نمی‌شود شخصیت و کرامتش را با گناه و پستی معامله کند.",
    "کسی که به عیب‌های خودش توجه داشته باشد، فرصت و انگیزه‌ای برای جست‌وجوی عیب دیگران پیدا نمی‌کند.",
    "صبر دو نوع است؛ یکی شکیبایی در برابر امور ناخوشایند و دیگری خویشتن‌داری در برابر چیزهایی که انسان به آنها علاقه دارد.",
    "ناتوانی آفت است و شکیبایی شجاعت.",
    "زهد ثروت است و پرهیزکاری سپر نگه‌دارنده.",
    "برترین زهد، پنهان داشتن زهد است.",

    # ═══ خوش‌رفتاری و روابط انسانی ═══
    "خوشرویی، نوعی خوبی کردن در حق دیگران است.",
    "بشاش بودن بهترین وسیله برای به دست آوردن دوست است.",
    "بردباری در قبال سختی‌ها وسیله جلوگیری از عیوب است.",
    "مسالمت و صلح‌جویی وسیله پوشانیدن عیوب است.",
    "چه همنشین خوبی است راضی بودن و خرسندی.",
    "بخشش، شکرانه پیروزی است.",
    "سزاوارترین مردم به عفو کردن، تواناترینشان به هنگام کیفر دادن است.",
    "میوه تواضع، دوستی است.",
    "قلب‌های مردم گریزان است، به کسی روی آورند که خوشرویی کند.",
    "خوش‌اخلاقی و بخشندگی، انسان را محبوب دل‌ها می‌کند.",

    # ═══ دوستی، معاشرت و روابط اجتماعی ═══
    "با مردم آن گونه معاشرت کنید که اگر مردید برای شما اشک بریزند و اگر زنده ماندید با اشتیاق به سوی شما بیایند.",
    "ناتوان‌ترین مردم کسی است که در دوست‌یابی ناتوان باشد و از او ناتوان‌تر کسی است که دوستان خود را از دست بدهد.",
    "اگر بر دشمنت دست یافتی، به عنوان شکرانه پیروزی‌ات او را ببخش.",
    "در دوست داشتن دوستان زیاده‌روی نکن؛ زیرا ممکن است روزی به دشمن تبدیل شوند.",
    "در دشمنی با دشمنان افراط نکن، چراکه احتمال دارد روزی دوست تو شوند.",
    "دوستان، بهترین ذخیره و پشتیبان هستند.",
    "با رفق و مدارا، دوستی و مصاحبت دوام می‌یابد.",
    "دوست واقعی از دوستی‌اش برنمی‌گردد، گر چه در حقش جفا شود.",
    "هر که خوش‌رفتاری پیشه کند، دوستانش فراوان شوند.",
    "افراد خودخواه دارای دشمنان زیاد می‌باشند.",
    "برادرت را با نیکی کردن به او سرزنش کن و شرّ او را از راه بخشش دور ساز.",
    "به پیمان کسانی چنگ بزنید که به پیمانشان وفادارند.",

    # ═══ عدالت، حکومت و مسائل اجتماعی ═══
    "عدل، بالاترین گشایش در زندگی مردم است.",
    "هر کس عدل را بر خود سخت پندارد، جور برای او سخت‌تر خواهد بود.",
    "با مردم براساس عدالت رفتار کن و در حق هیچ‌کسی ظلم نکن، حتی اگر در جایگاه قدرت قرار داشته باشی.",
    "همواره دشمن ظالمان باشید و یاور مظلومان.",
    "ضعیفان را نیرومند ساخته حقشان را بگیرید و گردنکشان را خوار دارید.",
    "خداوند بر پیشوایان دادگر واجب کرده است که زندگی خود را با طبقه ضعیف تطبیق دهند.",
    "به خدا سوگند! اگر اموال از خودم بود، به گونه‌ای مساوی میان مردم تقسیم می‌کردم.",
    "بپرهیز از ویژه‌سازی در چیزهایی که همه مردم در آنها برابرند.",
    "ای تجّار! تقوای الهی پیشه کنید، نزدیک ربا نشوید و کم‌فروشی نکنید.",
    "از کفاره گناهان بزرگ، به فریاد مردم رسیدن و آرام کردن مصیبت‌دیدگان است.",
    "از کسی که به تو بی‌اعتناست، اظهار تمایل نکن که سبب خواری تو می‌شود.",
    "بدترین مردم کسی است که شکر نعمت را به جا نیاورد و حرمت و احترام مردم را رعایت نکند.",
    "مردم در این جهان دو دسته‌اند: یکی آن که خود را فروخت و تباه کرد و دیگری آن که خود را خرید و آزاد کرد.",
    "کسی که خود را در مواضع تهمت قرار دهد، نباید کسی را ملامت کند که به او سوء ظن پیدا می‌کند.",
    "آن که خود را پیشوای مردم سازد، باید پیش از آموزش دیگران، خود را آموزش دهد.",

    # ═══ دنیا و بی‌اعتباری آن ═══
    "این جهان سرای گذر است، نه سرای ماندن.",
    "دنیا منزلگاهی برای کوچ کردن است و جای اقامت نیست.",
    "دنیا مانند مار است که زیر دست نرم و ملایم ولی سم کشنده‌ای در درون دارد.",
    "هرچه از دنیا بیش از کفایت فراهم کنی، آن را برای غیر خود ذخیره می‌نمایی.",
    "فرصت‌ها مثل ابرها می‌گذرند. پس فرصت‌های نیک را غنیمت شمارید.",
    "کسی که کردارش او را به جایی نرساند، افتخارات خاندانش او را به جایی نمی‌رساند.",
    "ای مردم! دل‌هایتان را از این دنیا خارج کنید، پیش از آن که بدن‌هایتان را از آن خارج کنند.",
    "دنیا عیوب خود را عیان کرده است و چیز پنهانی ندارد.",
    "دنیا اگر از تو کم کند یا بیش، دل در پی او منه که این نیست پسند.",
    "آن که در پی دنیاست، همچون تشنه‌ای است که هرچه آب بنوشد، تشنه‌تر شود.",
    "هنگام مرگ، مردم دنیاپرست می‌پرسند از خودش چه قدر دارایی به جا گذاشت؟ و فرشتگان می‌پرسند از عبادت و بندگی خدا برای خود چه پیش فرستاد؟",

    # ═══ ایمان، توحید و بندگی ═══
    "ایمان، چراغی است که در دل روشن می‌شود و بصیرت می‌آورد.",
    "ایمانتان را با صدقه حفظ کنید و اموالتان را با زکات.",
    "هیچ شرافتی برتر از اسلام، و هیچ عزتی گرامی‌تر از تقوا، و هیچ سنگری نیکوتر از پارسایی نیست.",
    "کسی که قدر خود را نشناسد، هلاک می‌شود.",
    "خدا را در راضی نگه‌داشتن مردم به خشم نیاور، زیرا خشنودی خدا جایگزین هر چیزی است، اما هیچ چیز جایگزین خشنودی خدا نمی‌شود.",
    "بهایی برای جان شما جز بهشت نیست، پس کمتر از آن نفروشید.",

    # ═══ موعظه، عبرت و حکمت‌های ناب ═══
    "در فتنه‌ها چونان شتر دو ساله باش؛ نه پشتی دارد که سواری دهد و نه پستانی تا او را بدوشند.",
    "تهی‌دستی مرد زیرک را در برهان کند می‌سازد و انسان تهی‌دست در شهر خویش نیز بیگانه است.",
    "نیکوکار، از کار نیک بهتر و بدکار، از کار بد بدتر است.",
    "از یورش بزرگوار به هنگام گرسنگی، و از تهاجم انسان پست به هنگام سیری، بپرهیز.",
    "کسی که مشورت را ترک کند و استبداد رأی داشته باشد، هلاک می‌شود.",
    "از اندک دنیا به اندازه کفاف برگیر و بسیارش را که تو را به سرکشی کشد، رها کن.",
    "ترس با ناامیدی، و شرم با محرومیت همراه است.",
    "بخشنده باش اما زیاده‌روی نکن، در زندگی حسابگر باش اما سخت‌گیر مباش.",
    "مشورت، پشتیبان انسان است.",
    "هیچ ارثی چون ادب و هیچ پشتیبانی چون مشورت نیست.",
    "به کار خود مشو غره که در کارگه دهر / هزار بار چه و چو گذشت و رفته باد.",
    "همه از خاک آمدیم و به خاک می‌رویم.",
    "به خود مغرور مشو گرچه آسمان‌پایه‌ای / که این که پست شد از خاک او بلند شد.",

    # ═══ زنجیره حکمت‌های «هر که بیشتر...» ═══
    "هر که بیشتر سخن گوید، بیشتر لغزش کند.",
    "هر که بیشتر بترسد، بیشتر از راه بازماند.",
    "هر که بیشتر ببخشد، بیشتر بی‌نیاز شود.",
    "هر که بیشتر عذر آورد، بیشتر دروغ گوید.",
    "هر که بیشتر فکر کند، بیشتر عبرت گیرد.",
    "هر که بیشتر نیکی کند، بیشتر قدر بیند.",
    "هر که بیشتر مدارا کند، بیشتر دوست یابد.",
    "هر که بیشتر غم خورد، بیشتر بیمار شود.",
    "هر که بیشتر شادی کند، بیشتر سلامت یابد.",
    "هر که بیشتر حق بگوید، بیشتر دشمن یابد.",
    "هر که بیشتر عدالت کند، بیشتر امنیت بیند.",
    "هر که بیشتر ظلم کند، بیشتر ترس بیند.",
    "هر که بیشتر طمع کند، بیشتر خوار شود.",
    "هر که بیشتر قناعت کند، بیشتر آسوده باشد.",
    "هر که بیشتر حرص ورزد، بیشتر محروم ماند.",
    "هر که بیشتر صبر کند، بیشتر پیروز شود.",
    "هر که بیشتر شکر کند، بیشتر نعمت یابد.",
    "هر که بیشتر توکل کند، بیشتر کفایت بیند.",
    "هر که بیشتر یاد خدا کند، بیشتر آرامش یابد.",
    "هر که بیشتر دنیا را بخواهد، بیشتر آخرت را از دست دهد.",
    "هر که بیشتر آخرت را بخواهد، بیشتر دنیا به او رو آورد.",
    "هر که بیشتر از خدا بترسد، بیشتر مردم از او بترسند.",
    "هر که بیشتر از مردم بترسد، بیشتر خدا از او بترسد.",
    "هر که بیشتر با خدا باشد، بیشتر مردم با او باشند.",
    "هر که بیشتر با مردم باشد، بیشتر از خدا دور شود.",
    "هر که بیشتر به خود بپردازد، بیشتر به دیگران برسد.",
    "هر که بیشتر به دیگران بپردازد، بیشتر خود را گم کند.",
    "هر که بیشتر خود را بشناسد، بیشتر خدا را بشناسد.",
    "هر که بیشتر خدا را بشناسد، بیشتر خود را بشناسد.",
    "هر که بیشتر بداند، بیشتر بداند که نمی‌داند.",
    "هر که بیشتر نداند، بیشتر بپندارد که می‌داند.",
    "هر که بیشتر سکوت کند، بیشتر سخن گوید.",
    "هر که بیشتر بشنود، بیشتر بیاموزد.",
    "هر که بیشتر بیاموزد، بیشتر فروتن شود.",
    "هر که بیشتر فروتن شود، بیشتر بلند شود.",
    "هر که بیشتر بلند شود، بیشتر در خطر افتد.",
    "هر که بیشتر خود را بستاید، بیشتر خود را فرو کاهد.",
    "هر که بیشتر خود را فرو کاهد، بیشتر خود را بیالاید.",
    "هر که بیشتر خود را بیازارد، بیشتر خود را نابود کند.",
    "هر که بیشتر خود را نابود کند، بیشتر خود را زنده کند.",
    "هر که بیشتر خود را زنده کند، بیشتر خدا را زنده کند.",
    "هر که بیشتر خدا را زنده کند، بیشتر در دل‌ها زنده ماند.",
]

def random_hekmat() -> str:
    return f"📜 {random.choice(_hekmat)}"

# ---------------------------------------------------------------------------
# 🎮 سنگ کاغذ قیچی
# ---------------------------------------------------------------------------
_RPS_EMOJI = {
    "سنگ": "🪨",
    "کاغذ": "📄",
    "قیچی": "✂️",
}
_RPS_BEATS = {
    "سنگ": "قیچی",   # سنگ قیچی رو می‌بره
    "کاغذ": "سنگ",   # کاغذ سنگ رو می‌بره
    "قیچی": "کاغذ",  # قیچی کاغذ رو می‌بره
}


def play_rps(user_choice: str) -> str:
    """بازی سنگ کاغذ قیچی — خروجی متن آماده برای ارسال."""
    user_choice = user_choice.strip()

    # نرمال‌سازی (سنگ/کاغذ/قیچی)
    if user_choice not in _RPS_BEATS:
        return "❌ فقط «سنگ»، «کاغذ» یا «قیچی» رو می‌تونم قبول کنم."

    bot_choice = random.choice(list(_RPS_BEATS.keys()))

    user_emoji = _RPS_EMOJI[user_choice]
    bot_emoji = _RPS_EMOJI[bot_choice]

    # تعیین برنده
    if user_choice == bot_choice:
        result = "🤝☭ برابر شدیم!\nبرابری و برادری بمولاپ 🚩"
    elif _RPS_BEATS[user_choice] == bot_choice:
        result = "🦧 تو بردی! دسخوش"
    else:
        result = "من بردم! برو هر وقت قوی تر شدی بیا عامو 🦾"

    return (
        "🎮 سنگ کاغذ قیچی\n"
        "━━━━━━━━━━━━━━━━\n"
        f"👤 تو: {user_emoji} {user_choice}\n"
        f"🤖 من: {bot_emoji} {bot_choice}\n"
        "━━━━━━━━━━━━━━━━\n"
        f"{result}"
    )


# ---------------------------------------------------------------------------
# ⚽ پنالتی
# ---------------------------------------------------------------------------
_PENALTY_PLAYERS = [
    "مسی", "رونالدو", "نیمار", "کیلیان امباپه", "ارلینگ هالند",
    "محمد صلاح", "کریم بنزما", "لوکا مودریچ", "روبرت لواندوفسکی",
    "ویرجیل فن دایک", "کوین دی بروینه", "هری کین", "ثلطان آنتونی",
    "علی دایی", "جیمی واردی", "گرت بیل", "جواد نکونام",
    "ریکاردو کاکا", "توماس مولر", "علیرضا جهانبخش", "ادن هازارد",
    "رامین عشق تیم ما", "زیزو", "دیگو مارادونا",
    "پژمان جمشیدی", "فرانچسکو توتی", "ژائو فلیکس", "مسوت اوزیل",
]

_PENALTY_DIRECTIONS = ["چپ", "وسط", "راست"]
_PENALTY_EMOJI = {
    "چپ": "⬅️",
    "وسط": "⬆️",
    "راست": "➡️",
}

def _build_penalty_text(player: str) -> str:
    return (
        "⚽ پنالتی!\n"
        "━━━━━━━━━━━━━━━━\n"
        f"🏃‍♂️ بدو بدو! {player} میخواد پنالتی بزنه...\n"
        "🧤 تو دروازه‌بانی! کجا می‌پری؟\n\n"
        "  ⬅️ چپ\n"
        "  ⬆️ وسط\n"
        "  ➡️ راست\n"
        "━━━━━━━━━━━━━━━━\n"
        "📝 روی همین پیام ریپلای بزن و جوابت رو بگو.\n"
        "⏱ فرصت: ۹۰ ثانیه"
    )

_active_penalties: Dict[int, Dict[str, Any]] = {}
_PENALTY_TIMEOUT = 90.0


async def _penalty_timeout(msg_id: int) -> None:
    """اگه تا ۹۰ ثانیه کسی جواب نده، پیام پنالتی رو ادیت می‌کنه."""
    try:
        await asyncio.sleep(_PENALTY_TIMEOUT)
        pen = _active_penalties.pop(msg_id, None)
        if pen is None:
            return

        timeout_text = (
            "⏰ زمان پنالتی تموم شد!\n"
            "━━━━━━━━━━━━━━━━\n"
            f"🏃‍♂️ {pen['player']} بدون زدن پنالتی رفت.\n"
            "━━━━━━━━━━━━━━━━"
        )

        # ─── تلاش برای ادیت همون پیام پنالتی ───
        msg_obj = pen.get("msg_obj")
        if msg_obj is not None:
            if await safe_edit(msg_obj, timeout_text):
                return

        # ─── اگه ادیت نشد (پیام حذف شده یا خطا)، پیام جدید بفرست ───
        await safe_send(client, pen["chat_id"], timeout_text)

    except asyncio.CancelledError:
        raise
    except Exception as exc:
        log.debug("penalty timeout failed: %s", exc)


def _parse_penalty_choice(text: str) -> Optional[str]:
    """تشخیص انتخاب کاربر: چپ / وسط / راست"""
    t = (text or "").strip()
    if not t:
        return None
    for d in _PENALTY_DIRECTIONS:
        if d == t:
            return d
    for d in _PENALTY_DIRECTIONS:
        if d in t:
            return d
    return None

def play_penalty(user_choice: str, player: str) -> str:
    """نتیجه پنالتی: سیو یا گل خوردن (کاربر دروازه‌بان است)."""
    if user_choice not in _PENALTY_DIRECTIONS:
        return "❌ فقط «چپ»، «وسط» یا «راست» رو قبول می‌کنم."

    # مهاجم یه جهت تصادفی شوت می‌زنه
    shooter = random.choice(_PENALTY_DIRECTIONS)

    if user_choice == shooter:
        result_line = "🧤 سیو کردی! توپ رو گرفتی! 🎉"
    else:
        result_line = "😭 ای وای گل خوردی!"

    return (
        "⚽ پنالتی\n"
        "━━━━━━━━━━━━━━━━\n"
        f"🏃‍♂️ {player} شوت زد: {_PENALTY_EMOJI[shooter]} {shooter}\n"
        f"🧤 تو پریدی: {_PENALTY_EMOJI[user_choice]} {user_choice}\n"
        "━━━━━━━━━━━━━━━━\n"
        f"{result_line}"
    )

# ---------------------------------------------------------------------------
# 📦 بازی باکس — پیدا کردن گنج
# ---------------------------------------------------------------------------
_BOX_EMOJI: Dict[int, str] = {
    1: "1️⃣", 2: "2️⃣", 3: "3️⃣",
    4: "4️⃣", 5: "5️⃣", 6: "6️⃣",
    7: "7️⃣", 8: "8️⃣", 9: "9️⃣",
}

_active_boxes: Dict[int, Dict[str, Any]] = {}
_BOX_TIMEOUT = 120.0
_BOX_MAX_ATTEMPTS = 4
_BOX_TREASURE_COUNT = 2

def _to_fa_num(n: int) -> str:
    """تبدیل عدد انگلیسی به فارسی"""
    return str(n).translate(str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹"))

def _build_box_start_text() -> str:
    grid = "1️⃣2️⃣3️⃣\n4️⃣5️⃣6️⃣\n7️⃣8️⃣9️⃣"
    return (
        "📦 بازی باکس\n"
        "━━━━━━━━━━━━━━━━\n"
        "گنچ رو پیدا کن!🎯\n"
        f"💰 {_to_fa_num(_BOX_TREASURE_COUNT)} تا گنج توی این ۹ تا خونه قایم شده.\n"
        "🔍 باید هر دو رو پیدا کنی تا برنده شی!\n\n"
        f"{grid}\n\n"
        "━━━━━━━━━━━━━━━━\n"
        "📝 روی همین پیام ریپلای بزن و یه عدد ۱ تا ۹ بفرست.\n"
        f"🎯 {_to_fa_num(_BOX_MAX_ATTEMPTS)} شانس داری!\n"
        "⏱ فرصت: ۲ دقیقه"
    )


def _build_box_grid(tried: Dict[int, str]) -> str:
    rows: List[str] = []
    for r in range(3):
        row = ""
        for c in range(3):
            n = r * 3 + c + 1
            if n in tried:
                row += tried[n]
            else:
                row += _BOX_EMOJI[n]
        rows.append(row)
    return "\n".join(rows)


def _parse_box_choice(text: str) -> Optional[int]:
    t = (text or "").strip()
    if not t:
        return None
    # تبدیل اعداد فارسی/عربی به انگلیسی
    t = t.translate(str.maketrans(
        "۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩",
        "01234567890123456789",
    ))
    m = re.match(r"^([1-9])$", t)
    if m:
        return int(m.group(1))
    return None

def _play_box_round(box_data: Dict[str, Any], guess: int) -> Tuple[str, bool]:
    """پردازش یه حدس. خروجی: (متن نتیجه، آیا بازی تموم شده؟)"""
    tried: Dict[int, str] = box_data["tried"]
    treasures: List[int] = box_data["treasures"]

    if guess in tried:
        return f"⚠️ خونه {_to_fa_num(guess)} رو قبلاً امتحان کردی!\nیه خونه دیگه انتخاب کن.", False

    is_treasure = guess in treasures
    tried[guess] = "💰" if is_treasure else "❌"

    found_count = sum(1 for t in treasures if tried.get(t) == "💰")
    remaining = _BOX_MAX_ATTEMPTS - len(tried)

    # 🏆 برد: هر دو گنج پیدا شد
    if found_count == len(treasures):
        return "🎉 تبریک! هر دو گنج رو پیدا کردی و برنده شدی! 🏆", True

    # 😢 باخت: فرصت‌ها تموم شد
    if remaining <= 0:
        t1, t2 = treasures
        # 👇 افشای گنج‌هایی که پیدا نشدن (با 💎)
        for t in (t1, t2):
            if tried.get(t) != "💰":
                tried[t] = "💎"
        return (
            f"😢 حیف شد! فقط {_to_fa_num(found_count)} از {_to_fa_num(len(treasures))} گنج رو پیدا کردی.\n"
            f"💰 گنج‌ها توی خونه‌های {_to_fa_num(t1)} و {_to_fa_num(t2)} بودن.\n"
            f"💎 = گنجی که پیدا نکردی"
        ), True

    # ⏳ ادامه بازی
    if is_treasure:
        return (
            f"💰 آفرین! یه گنج پیدا کردی!\n"
            f"🎯 {_to_fa_num(remaining)} شانس دیگه داری — اون یکی رو هم پیدا کن!"
        ), False
    else:
        return f"❌ خونه {_to_fa_num(guess)} خالی بود!\n🎯 {_to_fa_num(remaining)} شانس دیگه داری.", False

async def _box_timeout(msg_id: int) -> None:
    try:
        await asyncio.sleep(_BOX_TIMEOUT)
        box = _active_boxes.pop(msg_id, None)
        if box is None:
            return

        t1, t2 = box["treasures"]
        tried: Dict[int, str] = box["tried"]

        # 👇 افشای گنج‌های پیدا نشده با 💎 (نه 💰)
        for t in (t1, t2):
            if t not in tried:
                tried[t] = "💎"

        grid = _build_box_grid(tried)

        actually_found = sum(
            1 for t in (t1, t2)
            if t in box["tried"] and box["tried"][t] == "💰"
        )

        if actually_found == 0:
            result_line = "😢 نتونستی گنجی پیدا کنی!"
        else:
            result_line = f"😢 فقط {_to_fa_num(actually_found)} از {_to_fa_num(_BOX_TREASURE_COUNT)} گنج رو پیدا کردی!"

        timeout_text = (
            "⏰ زمانت تموم شد!\n"
            "━━━━━━━━━━━━━━━━\n"
            f"{grid}\n"
            "━━━━━━━━━━━━━━━━\n"
            f"{result_line}\n"
            f"💰 گنج‌ها توی خونه‌های {_to_fa_num(t1)} و {_to_fa_num(t2)} بودن.\n"
            f"💎 = گنجی که پیدا نکردی"
        )

        msg_obj = box.get("msg_obj")
        if msg_obj is not None:
            if await safe_edit(msg_obj, timeout_text):
                return

        await safe_send(client, box["chat_id"], timeout_text)

    except asyncio.CancelledError:
        raise
    except Exception as exc:
        log.debug("box timeout failed: %s", exc)


# ---------------------------------------------------------------------------
# فونت‌ها
# ---------------------------------------------------------------------------
_FONTS: Dict[str, str] = {
    "Bold": "𝗔𝗕𝗖𝗗𝗘𝗙𝗚𝗛𝗜𝗝𝗞𝗟𝗠𝗡𝗢𝗣𝗤𝗥𝗦𝗧𝗨𝗩𝗪𝗫𝗬𝗭𝗮𝗯𝗰𝗱𝗲𝗳𝗴𝗵𝗶𝗷𝗸𝗹𝗺𝗻𝗼𝗽𝗾𝗿𝘀𝘁𝘂𝘃𝘄𝘅𝘆𝘇𝟬𝟭𝟮𝟯𝟰𝟱𝟲𝟳𝟴𝟵",
    "Italic": "𝐴𝐵𝐶𝐷𝐸𝐹𝐺𝐻𝐼𝐽𝐾𝐿𝑀𝑁𝑂𝑃𝑄𝑅𝑆𝑇𝑈𝑉𝑊𝑋𝑌𝑍𝑎𝑏𝑐𝑑𝑒𝑓𝑔ℎ𝑖𝑗𝑘𝑙𝑚𝑛𝑜𝑝𝑞𝑟𝑠𝑡𝑢𝑣𝑤𝑥𝑦𝑧0123456789",
    "Bold Italic": "𝑨𝑩𝑪𝑫𝑬𝑭𝑮𝑯𝑰𝑱𝑲𝑳𝑴𝑵𝑶𝑷𝑸𝑹𝑺𝑻𝑼𝑽𝑾𝑿𝒀𝒁𝒂𝒃𝒄𝒅𝒆𝒇𝒈𝒉𝒊𝒋𝒌𝒍𝒎𝒏𝒐𝒑𝒒𝒓𝒔𝒕𝒖𝒗𝒘𝒙𝒚𝒛0123456789",
    "Sans": "𝖠𝖡𝖢𝖣𝖤𝖥𝖦𝖧𝖨𝖩𝖪𝖫𝖬𝖭𝖮𝖯𝖰𝖱𝖲𝖳𝖴𝖵𝖶𝖷𝖸𝖹𝖺𝖻𝖼𝖽𝖾𝖿𝗀𝗁𝗂𝗃𝗄𝗅𝗆𝗇𝗈𝗉𝗊𝗋𝗌𝗍𝗎𝗏𝗐𝗑𝗒𝗓𝟢𝟣𝟤𝟥𝟦𝟧𝟨𝟩𝟪𝟫",
    "Sans Bold": "𝗔𝗕𝗖𝗗𝗘𝗙𝗚𝗛𝗜𝗝𝗞𝗟𝗠𝗡𝗢𝗣𝗤𝗥𝗦𝗧𝗨𝗩𝗪𝗫𝗬𝗭𝗮𝗯𝗰𝗱𝗲𝗳𝗴𝗵𝗶𝗷𝗸𝗹𝗺𝗻𝗼𝗽𝗾𝗿𝘀𝘁𝘂𝘃𝘄𝘅𝘆𝘇𝟬𝟭𝟮𝟯𝟰𝟱𝟲𝟳𝟴𝟵",
    "Sans Italic": "𝘈𝘉𝘊𝘋𝘌𝘍𝘎𝘏𝘐𝘑𝘒𝘓𝘔𝘕𝘖𝘗𝘘𝘙𝘚𝘛𝘜𝘝𝘞𝘟𝘠𝘡𝘢𝘣𝘤𝘥𝘦𝘧𝘨𝘩𝘪𝘫𝘬𝘭𝘮𝘯𝘰𝘱𝘲𝘳𝘴𝘵𝘶𝘷𝘸𝘹𝘺𝘻0123456789",
    "Sans Bold Italic": "𝘼𝘽𝘾𝘿𝙀𝙁𝙂𝙃𝙄𝙅𝙆𝙇𝙈𝙉𝙊𝙋𝙌𝙍𝙎𝙏𝙐𝙑𝙒𝙓𝙔𝙕𝙖𝙗𝙘𝙙𝙚𝙛𝙜𝙝𝙞𝙟𝙠𝙡𝙢𝙣𝙤𝙥𝙦𝙧𝙨𝙩𝙪𝙫𝙬𝙭𝙮𝙯𝟬𝟭𝟮𝟯𝟰𝟱𝟲𝟳𝟴𝟵",
    "Script": "𝒜𝐵𝒞𝒟𝐸𝐹𝒢𝐻𝐼𝒥𝒦𝐿𝑀𝒩𝒪𝒫𝒬𝑅𝒮𝒯𝒰𝒱𝒲𝒳𝒴𝒵𝒶𝒷𝒸𝒹𝑒𝒻𝑔𝒽𝒾𝒿𝓀𝓁𝓂𝓃𝑜𝓅𝓆𝓇𝓈𝓉𝓊𝓋𝓌𝓍𝓎𝓏0123456789",
    "Script Bold": "𝓐𝓑𝓒𝓓𝓔𝓕𝓖𝓗𝓘𝓙𝓚𝓛𝓜𝓝𝓞𝓟𝓠𝓡𝓢𝓣𝓤𝓥𝓦𝓧𝓨𝓩𝓪𝓫𝓬𝓭𝓮𝓯𝓰𝓱𝓲𝓳𝓴𝓵𝓶𝓷𝓸𝓹𝓺𝓻𝓼𝓽𝓾𝓿𝔀𝔁𝔂𝔃0123456789",
    "Fraktur": "𝔄𝔅ℭ𝔇𝔈𝔉𝔊ℌℑ𝔍𝔎𝔏𝔐𝔑𝔒𝔓𝔔ℜ𝔖𝔗𝔘𝔙𝔚𝔛𝔜ℨ𝔞𝔟𝔠𝔡𝔢𝔣𝔤𝔥𝔦𝔧𝔨𝔩𝔪𝔫𝔬𝔭𝔮𝔯𝔰𝔱𝔲𝔳𝔴𝔵𝔶𝔷0123456789",
    "Fraktur Bold": "𝕬𝕭𝕮𝕯𝕰𝕱𝕲𝕳𝕴𝕵𝕶𝕷𝕸𝕹𝕺𝕻𝕼𝕽𝕾𝕿𝖀𝖁𝖂𝖃𝖄𝖅𝖆𝖇𝖈𝖉𝖊𝖋𝖌𝖍𝖎𝖏𝖐𝖑𝖒𝖓𝖔𝖕𝖖𝖗𝖘𝖙𝖚𝖛𝖜𝖝𝖞𝖟0123456789",
    "Double Struck": "𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℤ𝕒𝕓𝕔𝕕𝕖𝕗𝕘𝕙𝕚𝕛𝕜𝕝𝕞𝕟𝕠𝕡𝕢𝕣𝕤𝕥𝕦𝕧𝕨𝕩𝕪𝕫𝟘𝟙𝟚𝟛𝟜𝟝𝟞𝟟𝟠𝟡",
    "Monospace": "𝙰𝙱𝙲𝙳𝙴𝙵𝙶𝙷𝙸𝙹𝙺𝙻𝙼𝙽𝙾𝙿𝚀𝚁𝚂𝚃𝚄𝚅𝚆𝚇𝚈𝚉𝚊𝚋𝚌𝚍𝚎𝚏𝚐𝚑𝚒𝚓𝚔𝚕𝚖𝚗𝚘𝚙𝚚𝚛𝚜𝚝𝚞𝚟𝚠𝚡𝚢𝚣𝟶𝟷𝟸𝟹𝟺𝟻𝟼𝟽𝟾𝟿",
    "Circled": "ⒶⒷⒸⒹⒺⒻⒼⒽⒾⒿⓀⓁⓂⓃⓄⓅⓆⓇⓈⓉⓊⓋⓌⓍⓎⓏⓐⓑⓒⓓⓔⓕⓖⓗⓘⓙⓚⓛⓜⓝⓞⓟⓠⓡⓢⓣⓤⓥⓦⓧⓨⓩ⓪①②③④⑤⑥⑦⑧⑨",
    "Circled Filled": "🅐🅑🅒🅓🅔🅕🅖🅗🅘🅙🅚🅛🅜🅝🅞🅟🅠🅡🅢🅣🅤🅥🅦🅧🅨🅩🅐🅑🅒🅓🅔🅕🅖🅗🅘🅙🅚🅛🅜🅝🅞🅟🅠🅡🅢🅣🅤🅥🅦🅧🅨🅩⓿❶❷❸❹❺❻❼❽❾",
    "Parenthesized": "🄐🄑🄒🄓🄔🄕🄖🄗🄘🄙🄚🄛🄜🄝🄞🄟🄠🄡🄢🄣🄤🄥🄦🄧🄨🄩⒜⒝⒞⒟⒠⒡⒢⒣⒤⒥⒦⒧⒨⒩⒪⒫⒬⒭⒮⒯⒰⒱⒲⒳⒴⒵0⑴⑵⑶⑷⑸⑹⑺⑻⑼",
    "Squared": "🄰🄱🄲🄳🄴🄵🄶🄷🄸🄹🄺🄻🄼🄽🄾🄿🅀🅁🅂🅃🅄🅅🅆🅇🅈🅉🄰🄱🄲🄳🄴🄵🄶🄷🄸🄹🄺🄻🄼🄽🄾🄿🅀🅁🅂🅃🅄🅅🅆🅇🅈🅉0123456789",
    "Squared Filled": "🅰🅱🅲🅳🅴🅵🅶🅷🅸🅹🅺🅻🅼🅽🅾🅿🆀🆁🆂🆃🆄🆅🆆🆇🆈🆉🅰🅱🅲🅳🅴🅵🅶🅷🅸🅹🅺🅻🅼🅽🅾🅿🆀🆁🆂🆃🆄🆅🆆🆇🆈🆉0123456789",
    "Small Caps": "ABCDEFGHIJKLMNOPQRSTUVWXYZᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘǫʀꜱᴛᴜᴠᴡxʏᴢ0123456789",
    "Fullwidth": "ＡＢＣＤＥＦＧＨＩＪＫＬＭＮＯＰＱＲＳＴＵＶＷＸＹＺａｂｃｄｅｆｇｈｉｊｋｌｍｎｏｐｑｒｓｔｕｖｗｘｙｚ０１２３４５６７８９",
    "Currency": "₳฿₵ĐɆ₣₲ⱧłJ₭Ⱡ₥₦Ø₱QɌ$₮ɄV₩ӾɎƵ₳฿₵đɇ₣₲ⱨłj₭Ⱡ₥₦ø₱qɍ$₮ʉv₩ɏƶ0123456789",
    "Sticky": "ᗩᗷᑕᗪEᖴGᕼIᒍKᒪᗰᑎOᑭᑫᖇᔕTᑌᐯᗯ᙭Yᘔᗩᗷᑕᗪeᖴgᕼiᒍkᒪᗰᑎoᑭᑫᖇᔕtᑌᐯᗯ᙭yᘔ0123456789",
    "Medieval": "𝕬𝕭𝕮𝕯𝕰𝕱𝕲𝕳𝕴𝕵𝕶𝕷𝕸𝕹𝕺𝕻𝕼𝕽𝕾𝕿𝖀𝖁𝖂𝖃𝖄𝖅𝖆𝖇𝖈𝖉𝖊𝖋𝖌𝖍𝖎𝖏𝖐𝖑𝖒𝖓𝖔𝖕𝖖𝖗𝖘𝖙𝖚𝖛𝖜𝖝𝖞𝖟0123456789",
    "Bubble": "ⒶⒷⒸⒹⒺⒻⒼⒽⒾⒿⓀⓁⓂⓃⓄⓅⓆⓇⓈⓉⓊⓋⓌⓍⓎⓏⓐⓑⓒⓓⓔⓕⓖⓗⓘⓙⓚⓛⓜⓝⓞⓟⓠⓡⓢⓣⓤⓥⓦⓧⓨⓩ⓪①②③④⑤⑥⑦⑧⑨",
    "Blue": "🇦🇧🇨🇩🇪🇫🇬🇭🇮🇯🇰🇱🇲🇳🇴🇵🇶🇷🇸🇹🇺🇻🇼🇽🇾🇿🇦🇧🇨🇩🇪🇫🇬🇭🇮🇯🇰🇱🇲🇳🇴🇵🇶🇷🇸🇹🇺🇻🇼🇽🇾🇿0123456789",
    "Subscript": "ABCDEFGHIJKLMNOPQRSTUVWXYZₐbcdₑfgₕᵢⱼₖₗₘₙₒₚqᵣₛₜᵤᵥwₓyz₀₁₂₃₄₅₆₇₈₉",
    "Superscript": "ᴬᴮᶜᴰᴱᶠᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾQᴿˢᵀᵁⱽᵂˣʸᶻᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖqʳˢᵗᵘᵛʷˣʸᶻ⁰¹²³⁴⁵⁶⁷⁸⁹",
    "Greekish": "ΑΒΨΔΕΦΓΗΙΞΚΛΜΝΟΠQΡΣΤΘΩΩΧΥΖαβψδεφγηιξκλμνοπqρστυθωχψζ0123456789",
    "Rusify": "АВСDЕFGHІJKLMИОРQЯSTЦVШХУZавсdеfghіjklmиорqяstцvшхуz0123456789",
    "Wavy": "αɓƈɗєƒɠɦιʝҡℓɱɳσρqrʂƭυѵωχγȥαɓƈɗєƒɠɦιʝҡℓɱɳσρqrʂƭυѵωχγȥ0123456789",
    "Asian": "卂乃匚ᗪ乇千Ꮆ卄丨ﾌҜㄥ爪几ㄖ卩Ɋ尺丂ㄒㄩᐯ山乂ㄚ乙卂乃匚ᗪ乇千Ꮆ卄丨ﾌҜㄥ爪几ㄖ卩Ɋ尺丂ㄒㄩᐯ山乂ㄚ乙0123456789",
    "Mirror": "AᙠƆᗡƎꟻᎮHIႱʞ⅃MͶOꟼϘЯƧTUVWXYZAᙠƆᗡƎꟻᎮHIႱʞ⅃MͶOꟼϘЯƧTUVWXYZ0123456789",
    "Blocks": "🅰🅱🅲🅳🅴🅵🅶🅷🅸🅹🅺🅻🅼🅽🅾🅿🆀🆁🆂🆃🆄🆅🆆🆇🆈🆉🅰🅱🅲🅳🅴🅵🅶🅷🅸🅹🅺🅻🅼🅽🅾🅿🆀🆁🆂🆃🆄🆅🆆🆇🆈🆉0123456789",
    "Dots": "ÄḄĊḊĖḞĠḦÏJḲḶṀṄÖṖQṚṠṪÜṾẄẌŸŻäḅċḋėḟġḧïjḳḷṁṅöṗqṛṡṫüṿẅẍÿż0123456789",
    "Wings": "ᏗᏰፈᎴᏋᎦᎶᏂᎥᏠᏦᏝᎷᏁᎧᎮᎤᏒᏕᏖᏬᏉᏇጀᎩᏃᏗᏰፈᎴᏋᎦᎶᏂᎥᏠᏦᏝᎷᏁᎧᎮᎤᏒᏕᏖᏬᏉᏇጀᎩᏃ0123456789",
    "Cute": "αႦƈԃҽϝɠԋιʝƙʅɱɳσρϙɾʂƚυʋɯxყȥαႦƈԃҽϝɠԋιʝƙʅɱɳσρϙɾʂƚυʋɯxყȥ0123456789",
    "Tiny": "ᴀʙᴄᴅᴇғɢʜɪᴊᴋʟᴍɴᴏᴘǫʀsᴛᴜᴠᴡxʏᴢᴀʙᴄᴅᴇғɢʜɪᴊᴋʟᴍɴᴏᴘǫʀsᴛᴜᴠᴡxʏᴢ₀₁₂₃₄₅₆₇₈₉",
}

_BASE_CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"

_FONT_TABLES: Dict[str, Any] = {}
for _fname, _fchars in _FONTS.items():
    _tbl = {}
    for _i, _base in enumerate(_BASE_CHARS):
        if _i < len(_fchars):
            _tbl[ord(_base)] = _fchars[_i]
    _FONT_TABLES[_fname] = str.maketrans(_tbl)


def apply_all_fonts(text: str) -> List[str]:
    seen: Set[str] = set()
    result: List[str] = []
    for tbl in _FONT_TABLES.values():
        styled = text.translate(tbl)
        if styled and styled not in seen:
            seen.add(styled)
            result.append(styled)
    return result


# ---------------------------------------------------------------------------
# تاس
# ---------------------------------------------------------------------------
_DICE_ART: Dict[int, List[str]] = {
    1: [
        "⣴⠛⠛⠛⠛⠛⠛⠛⠛⣦",
        "⣿⠀⠀⠀⠀⠀⠀⠀⠀⣿",
        "⣿⠀⠀⠀⢾⡷⠀⠀⠀⣿",
        "⣿⠀⠀⠀⠀⠀⠀⠀⠀⣿",
        "⠻⣤⣤⣤⣤⣤⣤⣤⣤⠟",
    ],
    2: [
        "⣴⠛⠛⠛⠛⠛⠛⠛⠛⣦",
        "⣿⠀⠀⠀⠀⠀⠀⢾⡷⣿",
        "⣿⠀⠀⠀⠀⠀⠀⠀⠀⣿",
        "⣿⢾⡷⠀⠀⠀⠀⠀⠀⣿",
        "⠻⣤⣤⣤⣤⣤⣤⣤⣤⠟",
    ],
    3: [
        "⣴⠛⠛⠛⠛⠛⠛⠛⠛⣦",
        "⣿⠀⠀⠀⠀⠀⠀⢾⡷⣿",
        "⣿⠀⠀⠀⢾⡷⠀⠀⠀⣿",
        "⣿⢾⡷⠀⠀⠀⠀⠀⠀⣿",
        "⠻⣤⣤⣤⣤⣤⣤⣤⣤⠟",
    ],
    4: [
        "⣴⠛⠛⠛⠛⠛⠛⠛⠛⣦",
        "⣿⢾⡷⠀⠀⠀⠀⢾⡷⣿",
        "⣿⠀⠀⠀⠀⠀⠀⠀⠀⣿",
        "⣿⢾⡷⠀⠀⠀⠀⢾⡷⣿",
        "⠻⣤⣤⣤⣤⣤⣤⣤⣤⠟",
    ],
    5: [
        "⣴⠛⠛⠛⠛⠛⠛⠛⠛⣦",
        "⣿⢾⡷⠀⠀⠀⠀⢾⡷⣿",
        "⣿⠀⠀⠀⢾⡷⠀⠀⠀⣿",
        "⣿⢾⡷⠀⠀⠀⠀⢾⡷⣿",
        "⠻⣤⣤⣤⣤⣤⣤⣤⣤⠟",
    ],
    6: [
        "⣴⠛⠛⠛⠛⠛⠛⠛⠛⣦",
        "⣿⢾⡷⠀⢾⡷⠀⢾⡷⣿",
        "⣿⠀⠀⠀⠀⠀⠀⠀⠀⣿",
        "⣿⢾⡷⠀⢾⡷⠀⢾⡷⣿",
        "⠻⣤⣤⣤⣤⣤⣤⣤⣤⠟",
    ],
}


def roll_dice() -> Tuple[int, str]:
    n = random.randint(1, 6)
    art = "\n".join(_DICE_ART[n])
    return n, art


# ---------------------------------------------------------------------------
# فکت‌ها
# ---------------------------------------------------------------------------
_FACTS: List[str] = [
    "1. اگه از کسی درخواستی داری، بگو دقیقاً چی می‌خوای — ذهن انسان درخواست مبهم رو رد می‌کنه.",
    "2. وقتی از کسی می‌پرسی «چرا این کارو کردی؟»، مغز بلافاصله یه دلیل منطقی می‌سازه که واقعی نیست.",
    "3. لبخند زدن حتی وقتی حالت خوب نیست، واقعاً حالت رو بهتر می‌کنه — مغز از حالت چهره تقلب می‌گیره.",
    "4. آدم‌ها بیشتر چیزی که آخرین بار دیدن رو یادشون می‌مونه، نه کل تجربه‌شون.",
    "5. اسم خودت رو اول بگو وقتی می‌خوای از کسی چیزی بخوای — احتمال قبول شدنش دو برابر می‌شه.",
    "6. اگه می‌خوای کسی متقاعد بشه، همون کاری که برات کردش رو یادش بیار — قانون عمل متقابل.",
    "7. وقتی یه لیست ۳ گزینه‌ای به کسی می‌دی، مردم معمولاً گزینه وسط رو انتخاب می‌کنن.",
    "8. سکوت تو مکالمه، طرف مقابل رو مجبور به پر کردنش می‌کنه — حتی اگه چیز مهمی نگه.",
    "9. آدم‌ها معمولاً کاری که خودشون کردن رو به شرایط نسبت می‌دن، ولی کاری که دیگران کردن رو به شخصیتشون.",
    "10. گوش دادن فعال یعنی چیزی که شنیدی رو با کلمات خودت تکرار کنی — نزدیکی عجیبی می‌سازه.",
    "11. به یاد سپردن اسم کسی وقتی اولین بار می‌بینیش، بیشتر از هر تعریفی بهش حس خوب می‌ده.",
    "12. توی مذاکره، اولین عددی که گقته می‌شه معمولاً تأثیر زیادی روی نتیجه داره — لنگر ذهنی.",
    "13. اگه می‌خوای کسی یه کار سخت رو انجام بده، اول یه کار خیلی سخت‌تر ازش بخواه — رد کردن درخواست اول، دوم رو آسون می‌کنه.",
    "14. چشم‌ها بیشتر از دهان دروغ می‌گن — ولی نه اون‌طور که تو فیلم‌ها نشون می‌دن.",
    "15. وقتی یه متن رو با اسم خودت می‌نویسی، مغزت بهتر یادش می‌گیره — اثر مالکیت.",
    "16. هرچی چیزی رو بیشتر ببینی، بیشتر دوستش داری — حتی اگه تو اولین نگاه ازش بدت اومده باشه.",
    "17. آدم‌ها به کسی که خودشون انتخاب کردن، بیشتر از کسی که براشون انتخاب شده وفادارن.",
    "18. نوشتن یه تصمیم روی کاغذ، احتمال انجام شدنش رو تا ۴۲٪ بیشتر می‌کنه.",
    "19. اگه صبح‌ها یه لیست سه‌تایی از مهم‌ترین کارهات بنویسی، بیشتر از نصف روزت صرفه‌جویی می‌شه.",
    "20. مغز در ۲۰ دقیقه اول بیداری، خلاق‌ترین حالتش رو داره.",
    "21. هر بار که وقفه بین کارت می‌افته، حدود ۲۳ دقیقه طول می‌کشه تا تمرکزت کامل برگرده.",
    "22. حتی گوشی خاموش که کنارت باشه، بازم بازدهیت رو کم می‌کنه — چون ذهنت مدام بهش فکر می‌کنه.",
    "23. پیاده‌روی ۱۰ دقیقه‌ای، بیشتر از یه فنجون قهوه هوشیاری می‌آره.",
    "24. وقتی دو کار همزمان انجام می‌دی، مغز واقعاً هر دو رو کندتر انجام می‌ده نه موازی — چیزی به اسم multitasking واقعی وجود نداره.",
    "25. خواب کمتر از ۷ ساعت، حافظه رو ۴۰٪ ضعیف‌تر می‌کنه.",
    "26. بهترین چرت زدن، ۲۰ دقیقه‌ست نه بیشتر — چون وارد فاز عمیق نمی‌شی.",
    "27. وقتی گرسنه‌ای، خریدت بیشتر می‌شه — پس هیچ‌وقت گرسنه نرو سوپرمارکت.",
    "28. آبی که تو غذای رستوران می‌ذارن، معمولاً طراحیشده که تشنت رو زیاد کنه — پس نوشیدنی بیشتری بخری.",
    "29. تو سوپرمارکت، نان و شیر جلو دره چون بیشترین خریدهای اجباری‌ان و باعث می‌شن عادت به چرخیدن کنی.",
    "30. هرچی محصول گرون‌تر باشه، معمولاً تو ارتفاع چشمی‌تری قرار می‌گیره.",
    "31. قیمت‌های مثل ۹۹ هزار و ۹۰۰ تومن، به جای ۱۰۰ هزار، باعث می‌شن مردم بیشتر خرید کنن — حتی وقتی هر دو یکیه.",
    "32. کارت بانکی باعث می‌شه بیشتر خرج کنی تا پول نقد — چون درد پرداخت رو حس نمی‌کنی.",
    "33. وقتی یه اشتراک داری که «لغو کردن» سخته، تمایل داری فراموشش کنی — به این می‌گن تاریک‌الگو.",
    "34. بسته‌بندی‌های رنگی و شاد، مغز رو گول می‌زنن که غذای داخلش سالم‌تره.",
    "35. اگه پولت رو تو حساب مجزا از حساب خرید روزانه بذاری، کمتر خرج می‌کنی.",
    "36. اکثر آدم‌ها فکر می‌کنن پول بیشتری نیاز دارن، ولی مشکل واقعی‌شون نبود سیستم خرج کردنه.",
    "37. اگه ۱۰٪ از درآمدت رو بلافاصله پس از دریافت کنار بذاری، بعد از یه سال معجزه می‌بینی.",
    "38. خریدن یه چیز ارزون که بهش نیاز نداری، گرون‌تر از خریدن یه چیز گرون که لازم داری تموم می‌شه.",
    "39. آدم‌ها معمولاً ضرر کردن رو دو برابر بیشتر از سود کردن حس می‌کنن — به این می‌گن نفرت از باخت.",
    "40. بیشتر آدم‌ها تصمیمات مالی رو تو حالت احساسی می‌گیرن نه منطقی.",
    "41. آب یخ بعد از ورزش، تشنگیت رو بهتر فرو می‌نشونه تا آب گرم.",
    "42. تو حموم آب سرد بعد از گرم، سوخت‌وساز بدن رو تا حدی بالا می‌بره.",
    "43. قدم زدن بعد از غذا، قند خون رو بهتر از نشستن کنترل می‌کنه.",
    "44. یه قاشق عسل طبیعی قبل از خواب، کیفیت خوابت رو بهتر می‌کنه.",
    "45. پرتقال به تنهایی، آهنش کم جذب می‌شه — با یه منبع ویتامین C بخور.",
    "46. بوی نعنا و لیمو، تمرکز و هوشیاری رو بیشتر می‌کنه تا بوی قهوه.",
    "47. غذا خوردن با ظرف کوچیک‌تر، باعث می‌شه کمتر بخوری — مغز به اندازه ظرف نگاه می‌کنه نه به شکمت.",
    "48. اگه غذا رو آهسته بخوری، مغزت ۲۰ دقیقه بعد سیگنال سیری می‌فرسته — قبلش گرسنه‌ای حتی اگه معده پر باشه.",
    "49. خندیدن ۱۵ دقیقه‌ای، حدود ۴۰ کالری می‌سوزونه — کمه، ولی بهتر از هیچی.",
    "50. موز قبل خواب، به خاطر منیزیم و تریپتوفان، خواب رو بهتر می‌کنه.",
    "51. مغز انسان تو ۵۰ سالگی، در تشخیص احساسات دیگران از ۲۰ سالگی بهتره.",
    "52. آدم‌های مسن‌تر، تو تصمیمات عقلانی معمولاً بهتر از جوونا عمل می‌کنن — چون احساسات رو بهتر مدیریت می‌کنن.",
    "53. صورت انسان برای هر حالتی یه سری ماهیچه خاص داره که تو حالت طبیعی آسوده‌ست، ولی تو نگرانی همیشه فعال.",
    "54. مغز بین سن ۱۳ تا ۲۵ سال، آخرین بخش‌هایی که کامل می‌شه، همون بخش تصمیم‌گیری منطقیه.",
    "55. احساس دوست داشتن، شبیه اعتیاد عمل می‌کنه — همون بخش مغز فعال می‌شه.",
    "56. اشک عاطفی، حاوی هورمون‌های استرسه — پس واقعاً گریه کردن آرومت می‌کنه.",
    "57. بغل کردن بیست ثانیه‌ای، هورمون اکسیتوسین ترشح می‌کنه که حس اعتماد ایجاد می‌کنه.",
    "58. افرادی که کتاب می‌خونن، بیشتر از بقیه می‌تونن احساسات بقیه رو درک کنن.",
    "59. صحبت کردن با خودت، نه تنها عجیب نیست، بلکه کارکرد مغز رو بهتر می‌کنه.",
    "60. مغز انسان در تشخیص صدای اسم خودش، حتی تو جمع شلوغ، هوشیارتر از هر چیزیه — اثر مهمونی.",
    "61. زبان مادری تو مغز جای متفاوتی از زبان دوم ذخیره می‌شه — پس وقتی زبان دوم یاد می‌گیری، مجبوری از بخش دیگه‌ای استفاده کنی.",
    "62. وقتی یه کلمه رو نوک زبونت داری ولی یادت نمی‌آد، اگه یه کلمه بی‌ربط بگی، فوراً یادت می‌آد.",
    "63. بچه‌هایی که دو زبانه بزرگ می‌شن، تو حل مسائل پیچیده بهتر عمل می‌کنن.",
    "64. نوشتن با دست، بیشتر از تایپ کردن، به یادسپاری رو قوی می‌کنه.",
    "65. هر چیزی که توضیحش رو برای دیگران بگی، خودت بهتر یادش می‌گیری — اثر آموزش.",
    "66. مغز تو یادگیری، بیشتر با شکست‌ها یاد می‌گیره تا موفقیت‌ها.",
    "67. اگه یه موضوعی رو قبل از خواب بخونی، صبح بهتر یادش می‌آری.",
    "68. مکث کردن بین یادگیری، بهتر از فشرده یاد گرفتنه — اثر فاصله.",
    "69. مغز تو ۲۰ دقیقه اول یادگیری یه مهارت، سریع‌ترین پیشرفت رو داره.",
    "70. مردم معمولاً چیزی که به دیگران یاد می‌دن رو، خودشون فراموش نمی‌کنن.",
    "71. تولید محتوا، بیشتر از مصرف محتوا، مغز رو درگیر می‌کنه — پس آموزش با انجام دادن.",
    "72. برای یادگیری یه موضوع، بهتره که معلم بشی تا شاگرد.",
    "73. هر بار که یه چیز جدید یاد می‌گیری، بخشی از حافظه‌های قدیمی‌تر بازنویسی می‌شن.",
    "74. بوی یه عطر خاص می‌تونه یه خاطره‌ی فراموش‌شده رو زنده کنه — چون بویایی به حافظه مستقیم وصله.",
    "75. آدم‌ها معمولاً چیزهایی که آخرین بار و اول بار دیدن رو بهتر از وسط‌ها یادشون می‌مونه.",
    "76. مغز در حال یادگیری، بین فازهای تمرکز و استراحت جابه‌جا می‌شه — پس استراحت بخشی از یادگیریه.",
    "77. کافئین واقعاً انرژی نمی‌ده، فقط خستگی رو پنهان می‌کنه — بعدش خسته‌تر می‌شی.",
    "78. کنار پنجره نشستن، بازده کاری رو تا ۱۵٪ بالا می‌بره.",
    "79. گیاه سبز تو محیط کار، استرس رو کم می‌کنه حتی اگه فقط یه گلدون کوچیک باشه.",
    "80. رنگ آبی، تمرکز رو بالا می‌بره — به همین دلیل تو مطب‌ها و شرکت‌ها زیاد استفاده می‌شه.",
    "81. نوشتن با دست تو دفتر، خلاقیت رو بیشتر از تایپ کردن تو لپ‌تاپ تحریک می‌کنه.",
    "82. بوییدن یه چیز خوشبو قبل از انجام کار مهم، عملکرد رو بهتر می‌کنه.",
    "83. اگه یه کار رو تو مکان خاصی انجام بدی، بعداً تو همون مکان بهتر انجامش می‌دی — حافظه محیطی.",
    "84. ساعت‌های اول صبح، مغز تو حالت منطقی و تحلیلی بهتره، ولی بعد از ظهر تو حالت خلاقانه‌تر.",
    "85. دو ساعت قبل از خواب، نور آبی صفحه‌ها، ملاتونین رو متوقف می‌کنه — پس خوابت عقب می‌افته.",
    "86. ذهن آدمایی که هر روز بیرون می‌رن، بیشتر از کسایی که تو خونه‌ن، خلاقه.",
    "87. تند تند نفس کشیدن، استرس رو بیشتر می‌کنه — آهسته نفس بکش تا مغز آروم بشه.",
    "88. مغز تو مکث بین کارها، بیشتر از خود کار، خسته می‌شه.",
    "89. حرکات کوچیک دست مثل ورق زدن کتاب، مغز رو بیشتر درگیر یادگیری می‌کنه.",
    "90. تیکه کلام‌ها معمولاً نشون می‌دن ذهن طرف داره خودکار پردازش می‌کنه.",
    "91. اگه می‌خوای از کسی جواب سخت بگیری، وقتی خسته‌ست بپرس — مقاومتش کمتره.",
    "92. وقتی دو تا گزینه داری، اگر یه گزینه سوم اضافه کنی که آشغال باشه، انتخاب آدم از دو تای اول منطقی‌تر می‌شه.",
    "93. مذاکره‌ی بهترین زمان، وقتی‌ست که گرسنه‌ای — نه چون رقیقت به گرسنگی اهمیت می‌ده، بلکه خودت منطقی‌تر می‌شی.",
    "94. درخواست کتبی همیشه از شفاهی جدی‌تر گرفته می‌شه، حتی اگه محتوا یکی باشه.",
    "95. آدم‌ها معمولاً از کسی که قبلاً بهشون کمک کرده بیشتر خوششون میاد تا از کسی که خودشون بهش کمک کردن.",
    "96. وقتی یه چیزی رو جوری توضیح بدی که گویا خودت کشفش کردی، بقیه بیشتر باورش می‌کنن.",
    "97. هر جمله‌ای که با «چون» شروع بشه، بیشتر مورد قبول قرار می‌گیره حتی اگه دلیلش ضعیف باشه.",
    "98. چشم انسان تو تشخیص حالت چهره، سرعتش از تشخیص اسم خیلی بیشتره.",
    "99. آدم‌ها معمولاً بهترین تصمیم‌ها رو تو حالت خنثی می‌گیرن، نه خیلی خوشحال یا غمگین.",
    "100. تو جلسات، آخرین نفری که حرف می‌زنه، معمولاً بهترین تأثیر رو می‌ذاره.",
    "101. جمع کردن یه تیم ۵ نفره معمولاً از یه تیم ۱۰ نفره مؤثرتره.",
    "102. اگه می‌خوای خلاقیت جمعی رو بالا ببری، اول تنهایی فکر کن بعد گروهی جمع‌بندی کن.",
    "103. اعضای ساکت تیم، بیشتر از اعضای پرحرف ایده‌های بدیع دارن.",
    "104. اونایی که سر جلسه یادداشت نمی‌نویسن، معمولاً ۴۰٪ کمتر یادشون می‌مونه چی گفته شد.",
    "105. جلسات بدون دستور کار مشخص، معمولاً ۲ برابر بیشتر طول می‌کشن.",
    "106. استراحت‌های کوتاه بین کارها، بازده کل روز رو بالا می‌بره.",
    "107. هر یک ساعت کار بدون وقفه، احتمال اشتباه رو دو برابر می‌کنه.",
    "108. پیاده‌روی تو طبیعت، حتی ۱۵ دقیقه، عملکرد ذهنی رو بهتر از پیاده‌روی تو شهر می‌کنه.",
    "109. ذهن تو حالت بی‌کاری، بیشتر از حالت مشغول، خلاقانه فکر می‌کنه.",
    "110. آدم‌هایی که سر وقت می‌خوابن، بیشتر از کسایی که کم می‌خوابن، خلاقن.",
    "111. کارهای فکری سخت رو تو ساعت‌های اول صبح انجام بده، نه آخر شب.",
    "112. کنترل ایمیل صبح اول وقت، کل روزت رو داغون می‌کنه — بذار برای بعد از یه ساعت کار مفید.",
    "113. جواب دادن فوری به هر پیام، باعث می‌شه تمرکز اصلی‌ت از بین بره.",
    "114. سکوت بین سوال و جواب، باعث می‌شه طرف مقابل بیشتر و صادق‌تر جواب بده.",
    "115. آدمی که بلده نه بگه، موفق‌تر از کسیه که همیشه بله می‌گه.",
    "116. برای شروع یه کار جدید، ۵ دقیقه اول از همه چیز سختره — بعدش مغز رهاش نمی‌کنه.",
    "117. اگه کار سختت رو به قطعات کوچیک تقسیم کنی، مغز هر بخش رو یه پیروزی حساب می‌کنه.",
    "118. نوشتن کارهایی که انجام دادی، بیشتر از نوشتن کارهایی که باید انجام بدی، انگیزه می‌ده.",
    "119. تعریف کردن از تلاشت، نه از استعدادت، باعث می‌شه بیشتر پیشرفت کنی.",
    "120. ما آدم‌ها بیشتر از اینکه به دنبال خوشحالی باشیم، به دنبال فرار از دردیم.",
    "121. کافئین تو قهوه، بیشتر از ۶ ساعت تو بدن می‌مونه — پس ساعت ۴ بعدازظهر دیگه نخور.",
    "122. کافئین اثرش رو وقتی می‌ذاره که ۲۰ دقیقه از خوردنش گذشته.",
    "123. نوشیدن قهوه قبل از چرت ۲۰ دقیقه‌ای، بیدارشدنت رو راحت‌تر می‌کنه — چون کافئین تا بیدار شدن فعال می‌شه.",
    "124. اگه صبح با یه لیوان آب شروع کنی، بهره‌وری روزت بهتر می‌شه.",
    "125. صبحانه پرپروتئین، تمرکز صبح رو بیشتر از صبحانه شیرین بالا می‌بره.",
    "126. یه سیب صبح، بیشتر از یه فنجون قهوه بیدارت می‌کنه — چون قند طبیعی و فیبر داره.",
    "127. نان سبوس‌دار، به اندازه نان سفید سیر نمی‌کنه — پس بیشتر می‌خوری.",
    "128. غذای پرچرب سنگین، تا ۳ ساعت بعدش تمرکزت رو پایین می‌آره.",
    "129. پاستا شب قبل از امتحان، انرژیت رو فردا صبح پایین می‌آره — برعکس تصور عموم.",
    "130. یه قاشق سرکه سیب تو آب، قند خون رو تا حدی تنظیم می‌کنه.",
    "131. شکلات تلخ ۸۵٪، فشارخون رو کمی پایین می‌آره.",
    "132. عسل طبیعی تو آب گرم، برای گلودرد بهتر از آنتی‌بیوتیک‌های ضعیفه.",
    "133. هل و زنجبیل، حالت تهوع رو سریع‌تر از داروهای شیمیایی آروم می‌کنن.",
    "134. زردچوبه با فلفل سیاه، جذبش ۲۰ برابر می‌شه — همیشه با هم بخور.",
    "135. آب لیمو با آب گرم صبح، متابولیسم رو کمی بالا می‌بره — نه معجزه، ولی مؤثره.",
    "136. چای سبز بعد از غذا، جذب آهن رو کم می‌کنه — با فاصله بخور.",
    "137. مغزها (گردو، بادام) واقعاً برای مغز مفیدن — نه فقط به خاطر شکلشون.",
    "138. ماهی چرب، برای حافظه بهتر از هر مکملی عمل می‌کنه.",
    "139. رژیم مدیترانه‌ای، احتمال افسردگی رو تا ۳۰٪ کم می‌کنه.",
    "140. خندیدن سر میز غذا، هضم رو بهتر می‌کنه.",
    "141. سرما، سوخت‌وساز رو کمی بالا می‌بره — ولی نه اون‌قدر که با لرزیدن وزن کم کنی.",
    "142. هفت ساعت خواب باکیفیت، بیشتر از دو ساعت ورزش وزن رو کم می‌کنه.",
    "143. آب سرد دوش آخر، گردش خون رو تحریک می‌کنه و پوست رو شفاف‌تر می‌کنه.",
    "144. کرم ضدآفتاب مهم‌ترین محصول ضدپیری‌ست — نه کرم‌های گرون‌قیمت.",
    "145. پوست صورت با بالش کثیف، بیشتر از هر چیز دیگه جوش می‌زنه.",
    "146. نور آفتاب صبحگاهی، ساعت بدن رو تنظیم می‌کنه و شب خوابت رو بهتر می‌کنه.",
    "147. بعد از ۲۰ دقیقه آفتاب، بدن ویتامین D کافی می‌سازه — بعدش فقط ضرره.",
    "148. ورزش صبحگاهی، بیشتر از ورزش عصرگاهی، عادت رو تو آدم نهادینه می‌کنه.",
    "149. پیاده‌روی هفتگی ۱۵۰ دقیقه، بیشتر از هر قرصی عمر رو زیاد می‌کنه.",
    "150. نشستن طولانی، حتی با ورزش روزانه، بازم برای قلب بده.",
    "151. مغز آدم‌های تنها، مثل مغز آدم‌های ضربه‌خورده عمل می‌کنه.",
    "152. داشتن دوست نزدیک، بیشتر از هر دارویی عمر رو زیاد می‌کنه.",
    "153. آدم‌ها بیشتر از طریق دوستانِ دوستانشون شغل پیدا می‌کنن تا از طریق خود دوستان.",
    "154. تو شبکه‌های اجتماعی، ۹۰٪ محتوا از ۱۰٪ افراد میاد.",
    "155. تو هر جمع، حدود ۵٪ آدم‌ها بیشتر از ۹۵٪ بقیه شبکه‌سازی می‌کنن.",
    "156. اعتماد آدم‌ها به غریبه‌ها تو چند ثانیه اول شکل می‌گیره و به سختی تغییر می‌کنه.",
    "157. معمولاً آدم‌ها با کسی که تو یه چیز مشترک دارن، سریع‌تر دوست می‌شن.",
    "158. حتی اگه از کسی خوشت نیاد، اگه مجبور بشی باهاش کار کنی، کم‌کم دوستش داری — اثر مواجهه ساده.",
    "159. وقتی کسی ازت تشکر می‌کنه، مغزت همون حس قدرشناسی رو تجربه می‌کنه که تو طرف مقابل.",
    "160. آدم‌ها بیشتر از چیزی که خودشون حس می‌کنن، به حس تو واکنش می‌دن.",
    "161. تعریف کردن از دیگران، بیشتر از تعریف شنیدن، حالت رو بهتر می‌کنه.",
    "162. کسی که حالت رو می‌پرسه و خوب گوش می‌ده، بیشتر از هر دارویی بهت کمک می‌کنه.",
    "163. همدلی واقعی یعنی چیزی که طرف حس می‌کنه رو بفهمی، نه فقط بگی «می‌فهمم».",
    "164. دست دادن محکم، بیشتر از محتوای حرفت تأثیر می‌ذاره — تو اولین برخورد.",
    "165. اگه یه چیز رو با اطمینان بگی، مردم باور می‌کنن، حتی اگه درست نباشه.",
    "166. تو گروهِ آدم‌ها، معمولاً حرف کسی که بلندتر می‌زنه، بیشتر شنیده می‌شه تا حرف منطقی‌تر.",
    "167. سکوت کردن بعد از یه سوال، معمولاً جوابش رو از طرف می‌کشه — تکنیک بازجوی‌ها.",
    "168. آدم‌ها معمولاً چیزی که آخرین بار بهشون گفتی رو یادشون می‌مونه — پس مهم‌ترین چیز رو آخر بگو.",
    "169. اگه از کسی چیزی می‌خوای و می‌دونی ممکنه رد کنه، بگو «شاید نتونی ولی...» — احتمال قبول شدن بالاتر می‌ره.",
    "170. معمولاً آدم‌ها از کسی که به دیگران کمک می‌کنه، بیشتر خوششون میاد.",
    "171. ایمیل‌هایی که با اسم کوچیک مخاطب شروع می‌شن، ۳۰٪ بیشتر جواب داده می‌شن.",
    "172. مغز انسان، ۹۰٪ اطلاعات چهره رو از چشم می‌گیره — دهن ۱۰٪ بعدی.",
    "173. صورت‌های قرینه، برای مغز جذاب‌ترند — چه بخوایم چه نخوایم.",
    "174. اگه چیزی رو تو دست کسی بذاری، احتمال خریدش ۵۰٪ بیشتر می‌شه — لمس مالکیت.",
    "175. بو، بیشتر از صدا و تصویر، خاطرات رو زنده می‌کنه.",
    "176. یه جلسه رو با حالت مثبت شروع کن، کل جلسه مثبت‌تر پیش می‌ره.",
    "177. تو مذاکره، اگه یه چیز کوچیک رو اول بگیر، بعداً بزرگ‌تر رو راحت‌تر می‌گیری — قانون تعهد.",
    "178. اگه بذاری طرف مقابل تو مذاکره اول حرف بزنه، معمولاً خودش خودش رو تخفیف می‌ده.",
    "179. خرید چیزی که «همه» می‌خرن، حس رضایت کمتری می‌ده — مغز خودش رو گول می‌زنه.",
    "180. وقتی یه چیز رو تو زمان محدود پیشنهاد می‌دی، آدم‌ها بیشتر تصمیم می‌گیرن، حتی اگه تصمیم اشتباه باشه.",
    "181. افراد موفق، بیشتر از کسایی که موفق نیستن، از شکست‌هاشون حرف می‌زنن — نه از موفقیت‌ها.",
    "182. یادداشت‌برداری با دست، بیشتر از تایپ کردن، بهت کمک می‌کنه ایده‌ها رو پردازش کنی.",
    "183. کار کردن ۴ ساعت در روز با تمرکز بالا، بیشتر از ۸ ساعت پراکنده پیشرفت می‌آره.",
    "184. بی‌حوصلگی، نه تنها چیز بدی نیست، بلکه منبع خلاقیت و آرامشه.",
    "185. اگه هر روز ۲۰ دقیقه رو صرف یادگیری یه چیز جدید کنی، بعد از یه سال میشی «خوب» تو اون زمینه.",
    "186. نوشتن سه چیز کوچیک که هر روز شکرگزارشی، به مدت یه ماه حالت رو شفاف‌تر می‌کنه.",
    "187. تصمیم‌گیری مهم رو صبح بگیر، نه آخر روز — چون مغزت تازه‌ست.",
    "188. برای یادگیری بهتر، بین مطالعه‌ات پیاده‌روی کن — نه اینکه پشت میز بمونی.",
    "189. برای اینکه کارها رو به تعویق نندازی، فقط ۲ دقیقه شروع کن — مغز خودش ادامه می‌ده.",
    "190. اگه یه چیز رو توضیح بدی که نگهش داری، بهتر یادش می‌گیری.",
    "191. سه بار تو روز یه چیز رو تکرار کن و صبح بازگو — روش مؤثر یادسپاری.",
    "192. اگه بیرون از خونه کار می‌کنی، حتی یه میز ثابت داشته باش — مغز به فضا وابسته‌ست.",
    "193. برای پیدا کردن ایده نو، به مغزت استراحت بده — نه اینکه بیشتر تلاش کنی.",
    "194. کارهای مهمت رو با اسم‌گذاری مشخص کن، نه لیست بلند — مغز با اسم کار می‌کنه.",
    "195. حتی اگه استعداد نداریم، با تمرین منظم می‌تونیم به اکثر آدم‌ها تو هر چیزی برسیم.",
    "196. مغز آدم‌ها در دوران جوانی بیشتر از هر زمان دیگه‌ای تغییرپذیره.",
    "197. بیشتر آدم‌های موفق، تو زندگیشون دوره‌های شکست سنگین داشتن.",
    "198. کسی که شروع می‌کنه، بیشتر از کسی که فقط فکر می‌کنه، موفق می‌شه.",
    "199. مهارت‌های زندگی، تو جوونی باید یاد گرفته بشن — نه دیرتر.",
    "200. تغییر یه عادت، حداقل ۲۱ روز زمان می‌بره — نه ۳ روز.",
    "201. اگه یه چیزی رو تو ۳۰ ثانیه توضیح ندادی، یعنی خودت درست نفهمیدیش.",
    "202. افراد معمولاً چیزی که به دستشون میاد رو بیشتر از چیزی که از دست می‌دن ارزش می‌ذارن — حتی اگه ارزششون یکی باشه.",
    "203. بدون اینکه بخوای، از کسی که بیشتر باهاش وقت گذروندی، رفتار و حتی لحن حرف زدنش رو یاد می‌گیری.",
    "204. اگه تو جمع حرف بزنی و یکی موافقت کنه، بقیه هم راحت‌تر موافقت می‌کنن.",
    "205. مغز آدمایی که توی زندگی هدف دارن، کمتر با احساس پوچی درگیر می‌شه.",
    "206. تو هر جمع ۵ نفره، دو نفر همیشه بیشترین حرف رو می‌زنن و بقیه ساکتن — سعی کن جز اون دو نفر باشی یا حرف سومی رو باز کنی.",
    "207. آدم‌ها معمولاً خاطرات بد رو دقیق‌تر از خاطرات خوب یادشون می‌مونه — این یه مکانیزم بقاست.",
    "208. وقتی کسی گریه می‌کنه، فقط می‌خواد شنیده بشه، نه راه‌حل داده بشه — پس راه‌حل نده.",
    "209. حتی اگه مطمئن باشی درست می‌گی، اگه با احترام نگفته باشی، هیچ‌کس باورت نمی‌کنه.",
    "210. اگر می‌خوای کسی رو بشناسی، ببین چطور با کسی که ازش سودی نمی‌بره رفتار می‌کنه.",
    "211. حرفی که تو مستی می‌زنی، حقیقتیه که تو هشیاری پنهان کردی.",
    "212. کاری که تو خستگی انجام می‌دی، شخصیت واقعیت رو نشون می‌ده — نه کاری که تو بهترین حالتت می‌کنی.",
    "213. اگه می‌خوای بدون کسی چقدر پخته‌ست، ببین چطور مخالفت رو تحمل می‌کنه.",
    "214. تو مکالمه، اگه ۷۰٪ وقت رو گوش بدی و ۳۰٪ حرف بزنی، محبوب‌تر می‌شی.",
    "215. به آدم‌ها فرصت بده خودشون رو تعریف کنن، ولی زیاد سوال نپرس که حس بازجویی بگیرن.",
    "216. تو یه جمع، هر چیزی که می‌گی، قبلش ۳ ثانیه فکر کن — از ۹۰٪ پشیمونی‌ها جلوگیری می‌کنه.",
    "217. اگه می‌خوای کسی که دوستش داری رو از دست بدی، باهاش بحث کن که کی درست می‌گه.",
    "218. آدم‌ها از تو رفتار بدشون رو نمی‌بینی، چون ذهنشون خودش رو توجیه می‌کنه.",
    "219. تو محیط کار، اونایی که سر وقت میان و می‌رن، بیشتر از اونایی که همه‌وقت اضافه‌کاری می‌کنن احترام می‌بینن.",
    "220. یادداشت کردن یه تعریف کوچیک از کسی، و بعداً بهش گفتن، تأثیرش از ۱۰ تعریف آنی بیشتره.",
    "221. برای اینکه کسی بهت اعتماد کنه، اول بهش اعتماد کن — حتی تو یه چیز کوچیک.",
    "222. کسی که تو جمع کم حرف می‌زنه، معمولاً تو تنهایی چیزهای زیادی برای گفتن داره.",
    "223. هرکسی که زیاد از گذشته‌ش حرف می‌زنه، معمولاً تو حال ناراحته.",
    "224. تو مکالمه تلفنی، اگه وسط حرفش سکوت کنی، ممکنه خودش حقیقت رو بگه — بدون اینکه بخوای.",
    "225. کسی که از تمام جزئیات زندگی روزمره‌ش حرف می‌زنه، معمولاً از خودش مطمئن نیست.",
    "226. بیشتر دعواها از لحن شروع می‌شن، نه از محتوا — پس لحنت رو کنترل کن.",
    "227. اگه چیزی رو تو مکالمه دوبار تکرار کنی، مردم معمولاً باورش می‌کنن، حتی اگه دروغ باشه.",
    "228. آدم‌ها معمولاً چیزی که خودشون فکر می‌کنن تو ذهن توئه رو، تو حرفاشون تکرار می‌کنن.",
    "229. اگه می‌خوای بفهمی طرف داره دروغ می‌گه یا نه، به داستانش دقت کن — دروغ‌گوها جزئیات کم می‌گن، نه زیاد.",
    "230. مغز آدم‌ها تو تشخیص چهره‌ی دروغ‌گوها اصلاً خوب نیست — فیلم‌ها الکی نشون می‌دن.",
    "231. تو مکالمه، اگه کسی از کلمه‌ی «من» بیشتر از «ما» استفاده کنه، معمولاً تو حالت تدافعی‌ست.",
    "232. لبخند زدن تو لحظات سخت، بیشتر از هر جمله‌ای آرومت می‌کنه.",
    "233. کسی که می‌تونه چند دقیقه بی‌حرف بشینه، تو مذاکره معمولاً برنده‌ست.",
    "234. مغز تو تصمیم‌گیری، بیشتر با احساس تصمیم می‌گیره، بعد خودش برات دلیل منطقی می‌سازه.",
    "235. آدم‌ها معمولاً از چیزی که نمی‌فهمن می‌ترسن، نه از چیزی که واقعاً خطرناکه.",
    "236. تو هر مذاکره، اولین نفری که حرف بزنه، معمولاً بیشتر ضرر می‌کنه.",
    "237. راز موفقیت تو قراردادها، شفاف بودن همه چیز تو کاغذه — نه اعتماد شفاهی.",
    "238. کسی که ادعای همه‌چیز دانستن داره، معمولاً چیزی نمی‌دونه.",
    "239. هر چیزی که تو ذهنت با خودت تکرار می‌کنی، تو واقعیت رفتار تو شکل می‌ده.",
    "240. مغز تو یادگیری، بیشتر از تجربه‌های مستقیم یاد می‌گیره تا از شنیدن.",
    "241. برای اینکه یه چیز رو به یاد بیاری، خودت رو تو موقعیت اولش تصور کن — حافظه بازیابی بهتر می‌شه.",
    "242. ورزش هوازی، حتی ۲۰ دقیقه‌ای، حافظه رو تا ۳۰٪ بالا می‌بره.",
    "243. مغز تو خواب، خاطرات رو مرتب می‌کنه و اطلاعات بی‌اهمیت رو پاک می‌کنه.",
    "244. خواب نیم‌روزی اگه بیشتر از ۳۰ دقیقه باشه، حالت خواب‌آلود می‌ده — پس کوتاه‌تر بخواب.",
    "245. مغز تو ۹۰ دقیقه چرخه‌های خواب داره، اگه بین چرخه بیدار بشی خسته‌تر می‌شی.",
    "246. صداهای طبیعت، حتی از ضبط، فشارخون رو پایین می‌آرن.",
    "247. صدای بارون، مغز رو به حالت آرامش و تمرکز متمرکز می‌کنه.",
    "248. تو هر فعالیتی، مغز بین ۱۰ تا ۲۰ دقیقه اول بهترین عملکردش رو داره.",
    "249. مغز تو ۹۰ دقیقه فازهای تمرکز و استراحت داره — پس اگه تمرکزت پرید، بذار یه ربع استراحت کنه.",
    "250. هر چیزی که تو محیطت هست، مستقیم روی احساس و تصمیمت تأثیر می‌ذاره.",
    "251. نور کم تو اتاق، احساس بی‌حوصلگی و اندوه رو بیشتر می‌کنه.",
    "252. گلدون تو محیط کار، حتی خشک، بازم استرس رو تا حدی کم می‌کنه.",
    "253. کاغذ و خودکار روی میز کار، خلاقیت رو بهتر فعال می‌کنه تا لپ‌تاپ.",
    "254. رنگ‌های روشن تو اتاق، خلاقیت رو بالا می‌برن، رنگ‌های تیره آرامش می‌دن.",
    "255. بوی قهوه، حتی بدون خوردنش، مغز رو بیدار می‌کنه — بویایی و هوشیاری مستقیم به هم وصله.",
    "256. پنجره رو باز کن — هوای تازه بازده ذهنی رو ۱۵٪ بالا می‌بره.",
    "257. هر چی تو محیطت شلوغ‌تر باشه، تصمیم‌گیری سخت‌تر می‌شه — پس بذار محیطت ساده باشه.",
    "258. کار کردن با موسیقی بی‌کلام، تمرکز رو بیشتر از سکوت مطلق بالا می‌بره — برای بعضی‌ها.",
    "259. موسیقی با کلام تو کارهای فکری، تمرکز رو پایین می‌آره — مغز نمی‌تونه هم‌زمان دو تا زبان پردازش کنه.",
    "260. نور طبیعی صبحگاهی، خواب شب رو بهتر از هر قرصی تنظیم می‌کنه.",
    "261. برای اینکه صبح راحت‌تر بیدار شی، شب قبل پرده رو کمی باز بذار.",
    "262. اگه ساعت زنگت رو دور از تخت بذاری، احتمال بیدارشدنت دو برابر می‌شه.",
    "263. خوردن صبحانه با نور طبیعی، ساعت بدن رو بهتر تنظیم می‌کنه.",
    "264. ورود به گوشی صبح اول وقت، ساعت بدنت رو قاطی می‌کنه — بذار یه ربع اول رو با چیز دیگه‌ای بگذرونی.",
    "265. پیاده‌روی تو نور خورشید صبح، افسردگی فصلی رو بهتر از هر دارویی درمان می‌کنه.",
    "266. حتی ۱۰ دقیقه قدم زدن تو روز، احتمال حمله قلبی رو تا ۳۰٪ کم می‌کنه.",
    "267. سه بار در هفته پیاده‌روی، عمر رو حدود سه سال زیاد می‌کنه.",
    "268. نشستن طولانی، به اندازه‌ی سیگار کشیدن برای قلب بده — پس هر ساعت بایست و راه برو.",
    "269. آب خوردن زیاد، تمرکز و خلق‌وخو رو بهتر می‌کنه — کم‌آبی مغز رو خشک می‌کنه.",
    "270. نفس عمیق شکمی، استرس آنی رو تو ۹۰ ثانیه پایین می‌آره.",
    "271. تمرین مدیتیشن روزانه ۱۰ دقیقه، بعد یه ماه حجم ماده خاکستری مغز رو زیاد می‌کنه.",
    "272. خندیدن، حتی الکی، هورمون استرس رو تو بدن پایین می‌آره.",
    "273. گریه کردن در جمع، نزدیکی عاطفی می‌سازه — نه ضعف.",
    "274. تعریف کردن صادقانه از کسی، بیشتر از شنیدنش، حال خودت رو بهتر می‌کنه.",
    "275. کمک به کسی، بدون انتظار، بیشتر از هر قرص ضدافسردگی حال‌ت رو خوب می‌کنه.",
    "276. بخشیدن کسی که بهت بدی کرده، بیشتر از هر انتقامی آرومت می‌کنه — این اثر واقعاً تو مغز دیده می‌شه.",
    "277. تشکر کردن واقعی، حتی یه پیام ساده، بیشتر از یه هدیه گرون، طرف رو خوشحال می‌کنه.",
    "278. کسی که حالت رو می‌پرسه و منتظر جواب می‌مونه، بیشتر از هر کسی که باهات راه میاد بهت اهمیت می‌ده.",
    "279. تنهایی طولانی، مرگ رو زودتر می‌آره تا سیگار — پس رابطه‌ها رو حفظ کن.",
    "280. هر آدمی تو زندگیت، اگه بیشتر از یه هفته نیومد پیغامت، معمولاً نمی‌خواد بیاد.",
    "281. برای اینکه رابطه‌ای دووم بیاره، بیشتر از هفته‌ای یه بار باید حضوری هم رو ببینید.",
    "282. عذرخواهی کردن، اگه تأخیر کنی، بیشتر از اینکه فایده داشته باشه، ضرر می‌زنه.",
    "283. یه پیام عذرخواهی بعد از یه اشتباه، و بعد از یه هفته دوباره نزدن، بیشتر از عذرخواهی شفاهی تأثیر داره.",
    "284. عذرخواهی که با «اگه» بیاد، عذرخواهی نیست — سرزنشه با لباس عذرخواهی.",
    "285. آدم‌ها معمولاً به کسی که صادقانه اشتباهش رو قبول می‌کنه، بیشتر اعتماد می‌کنن تا به کسی که هیچ‌وقت اشتباه نمی‌کنه.",
    "286. تعریف کردن پشت سر کسی، وقتی به گوشش برسه، بیشتر از تعریف رو در رو ارزش داره.",
    "287. آدم‌ها معمولاً به خاطر چیزهایی که تو باهاشون فرق می‌کنی، ازت خوششون میاد — نه چیزی که شبیه‌شی.",
    "288. تو رابطه‌ها، حرف زدن درباره چیزهای کوچیک، بیشتر از بحث درباره چیزهای بزرگ، صمیمیت می‌سازه.",
    "289. هر بار که با کسی دعوا می‌کنی، مغزت اون تجربه رو تو خاطرات تلخ‌تر ذخیره می‌کنه.",
    "290. بخشیدن تو رابطه، بیشتر از درست بودن تو بحث، رابطه رو حفظ می‌کنه.",
    "291. حتی اگه از یه شخص خوشت نمیاد، اگه یه روز کامل همراهش باشی، یه جاهایی از اون رو پیدا می‌کنی که دوست داری.",
    "292. تو هر رابطه‌ای، اونی که بیشتر توجه می‌کنه، معمولاً بیشتر هم ضرر می‌کنه.",
    "293. به کسی که دوستش داری، فاصله بده — نه به خاطر بازی، بلکه چون تو فاصله، ارزش تو معلوم می‌شه.",
    "294. پیام‌هایی که همه‌ش می‌فرستی و اون کم جواب می‌ده، معمولاً نشون‌دهنده‌ی عدم علاقه‌ست.",
    "295. تو رابطه‌های عاطفی، اونی که منتظر می‌مونه، معمولاً ضرر می‌کنه.",
    "296. ترک کردن یه رابطه‌ی مسموم، سخت‌ترین کار زندگیه، ولی بیشترین آزادی رو می‌ده.",
    "297. مردم معمولاً تو بحران‌ها، شخصیت واقعیشون رو نشون می‌دن — نه تو روزهای خوب.",
    "298. حتی تو یه رابطه‌ی خیلی خوب، هر آدمی به فضای شخصی نیاز داره.",
    "299. اگه طرف مقابل خیلی تلاش می‌کنه که بهت ثابت کنه دوستت داره، معمولاً داره چیزی رو پنهان می‌کنه.",
    "300. آدمی که تو دعوا زیر سوال می‌بره شخصیتت رو، نه رفتارت رو، در حال از دست دادن احترامش به توئه.",
    "301. یه هدیه دست‌ساز، حتی اگه ساده باشه، بیشتر از یه هدیه گرون قیمت، تو دل طرف می‌مونه.",
    "302. برای اینکه حرفت رو یادش بمونه، آخرین جمله‌ات رو با یه تصویر یا داستان بگو.",
    "303. وقتی کسی باهات درد دل می‌کنه، حتی اگه بگی «درکت می‌کنم»، معمولاً کمکی نمی‌کنه — ساکت بمون.",
    "304. سوال‌های باز، بیشتر از سوال‌های بسته، مکالمه رو باز می‌کنن.",
    "305. آدم‌ها معمولاً تو جمع، خودشون رو با شخصیت قوی‌تر هم‌رنگ می‌کنن.",
    "306. تو هر جمع، اگه یکی شروع به خندیدن کنه، بقیه هم به‌طور ناخودآگاه می‌خندن.",
    "307. آدم‌ها تو جمع، وقتی یه نفر پشتیبانی می‌کنه، بیشتر جرات می‌کنن مخالفت کنن.",
    "308. حتی اگه کسی رو دوست نداری، محترمانه ساکت موندن باهاش، شخصیت خودت رو نشون می‌ده.",
    "309. یک جمله محبت‌آمیز که تو موقعیت درست گفته بشه، بیشتر از یه ساعت حرف زدن، عمق می‌سازه.",
    "310. اگه می‌خوای از کسی جدا شی، با احترام جدا شو — چون یه روز ممکنه باز بهش نیاز داشته باشی.",
    "311. برای اینکه کسی حرفش رو بزنه، سوالش رو با یه جمله مثبت بپرس، نه با شکایت.",
    "312. صداقت همیشه راحت نیست، ولی همیشه نفعش تو درازمدت بیشتره.",
    "313. اگه یه چیزی رو تو شبکه‌های اجتماعی می‌بینی و حالت بد می‌شه، حذفش کن — نه اینکه به خودت بگی «باید تحمل کنم».",
    "314. گوشی تو رختخواب، خوابت رو حتی وقتی خاموشه، خراب می‌کنه.",
    "315. برای بیدار شدن صبح، بهترین راه تنظیم کردن ساعت بدن با نور صبحه، نه با زنگ ساعت.",
    "316. یه روز در هفته بدون گوشی، حال روحی رو بهتر از هر تعطیلی طولانی می‌کنه.",
    "317. آدمایی که هر روز صبح صفحات شبکه‌های اجتماعی‌شون رو چک می‌کنن، بیشتر از بقیه احساس ناراحتی می‌کنن.",
    "318. تنظیم کردن ساعت خواب و بیداری ثابت، بیشتر از هر مکملی حالت رو بهتر می‌کنه.",
    "319. اگه ۳۰ دقیقه قبل خواب صفحه گوشی رو نگاه نکنی، خوابت تا ۲ برابر عمیق‌تر می‌شه.",
    "320. تو هر شرایطی، بهترین راه حل مشکلات، خواب کافیه — مغز خودش جواب رو پیدا می‌کنه.",
    "321. احساسات منفی، اگه تو ذهنت بمونن، بزرگ‌تر می‌شن — با نوشتنشون، کوچیک‌تر می‌شن.",
    "322. برای شادی، به دست آوردن چیزی که می‌خوای مهم نیست — کم‌کردن چیزهایی که نمی‌خوای مهم‌تره.",
    "323. اگه حالت بدی داری، برو یه لیوان آب بخور، ۱۰ دقیقه پیاده‌روی کن — حالت ۳۰٪ بهتر می‌شه.",
    "324. شکایت کردن، تو لحظه آرومت می‌کنه، ولی در درازمدت حالت رو بدتر می‌کنه.",
    "325. هر چیزی که تو زندگیت داری، اگه ۵ سال پیش بهش فکر می‌کردی، آرزوت بود.",
    "326. اگه می‌خوای آرامش داشته باشی، کمتر از چیزهایی که واقعاً نمی‌خوای، جواب بده.",
    "327. ترس از شکست، بیشتر از خود شکست، تو رو از پا در می‌آره.",
    "328. تو هر شکستی، بیشترین چیزی که یاد می‌گیری، درباره‌ی خودته، نه درباره‌ی موضوع.",
    "329. آدمی که از خودش مطمئنه، از موفقیت دیگران ناراحت نمی‌شه.",
    "330. به خودت دروغ نگو — بزرگ‌ترین دروغ، دروغی‌ست که به خودت می‌گی.",
    "331. احساس ارزش، از بیرون نمی‌آد — نمی‌تونی از کسی بگیری چیزی که تو خودت نداری.",
    "332. حتی اگه هیچ‌کس تو رو تشویق نکنه، پیشرفت خودت ارزشش رو داره.",
    "333. تو هر تصمیمی، یه بخش از وجودت همیشه می‌ترسه — با ترس حرکت کن، نه با اطمینان مطلق.",
    "334. آرزوهایی که انجام نشدن، معمولاً مربوط به ترس، نه کمبود توانایی.",
    "335. انسان بدون هدف، تو هر مسیری گم می‌شه — حتی اگه مسیرش راحت باشه.",
    "336. تو زندگی، نظم و انضباط، بیشتر از انگیزه ارزش داره — انگیزه تموم می‌شه، نظم نه.",
    "337. اگه هر روز یه قدم کوچیک برداری، بعد از یه سال هزار قدم جلوتری.",
    "338. شکست‌های بزرگ، بیشتر از موفقیت‌های کوچیک، تو رو می‌سازن.",
    "339. برای اینکه به خودت افتخار کنی، کافیه یه کار سخت رو تموم کنی — هر کاری.",
    "340. یاد گرفتن نه گفتن، بزرگ‌ترین مهارتیه که می‌تونی تو زندگی داشته باشی.",
    "341. اگه می‌خوای ببینی کسی چقدر پخته‌ست، ببین چطور با آدمایی که باهاشون هم‌سطح نیست رفتار می‌کنه.",
    "342. بزرگ‌ترین آدمایی که ملاقات می‌کنی، معمولاً بیشترین گوش دادن رو دارن، نه بیشترین حرف زدن.",
    "343. کسی که همه‌اش می‌خواد تو رو تعریف کنه، معمولاً از تو چیزی می‌خواد.",
    "344. راز حرفه‌ای‌ها، تکرار کردن کارهای ساده تا مرحله‌ی استادیه — نه دنبال کردن راه‌های میانبر.",
    "345. آدمی که به خودش می‌خنده، معمولاً سالم‌ترین شخصیت رو داره.",
    "346. تو هر جمعی، ساکت‌ترین آدم معمولاً بیشترین اطلاعات رو داره.",
    "347. برای اینکه کسی رو بشناسی، ببین تو موقعیت ناراحت‌کننده چطور رفتار می‌کنه.",
    "348. اگه می‌خوای بفهمی طرف چه شخصیتیه، ببین چطور با کارمند رستوران یا راننده تاکسی رفتار می‌کنه.",
    "349. کسی که تو تنهایی خودش حالش خوب باشه، تو جمع هم حالش خوبه — نه برعکس.",
    "350. بیشترین رشد آدم، تو لحظه‌های تنهایی می‌آد، نه تو شلوغی.",
    "351. کارگران اهرام مصر حقوق می‌گرفتن، نون و پیاز — برده نبودن.",
    "352. مصری‌ها اولین مردمی بودن که به گربه‌ها احترام گذاشتن — گربه‌کشی مجازات اعدام داشت.",
    "353. ملکه حتشپسوت مصر، به جای ریش مصنوعی می‌ذاشت و خودش رو فرعون مرد می‌خوند.",
    "354. کوروش کبیر منشور حقوق بشری نوشت که در اون آزادی عقیده و مذهب رو تضمین کرد — ۲۵۰۰ سال پیش.",
    "355. داریوش بزرگ سیستم پستی داشت که نامه رو از سارد تا شوش (۲۵۰۰ کیلومتر) در ۷ روز می‌رسوند.",
    "356. ایرانیان باستان اولین مردمی بودن که یخ رو تو یخچال (یخچال خشتی) ذخیره کردن.",
    "357. بابلی‌ها قانون حمورابی رو روی سنگ نوشتن که یکیش می‌گفت: «چشم در برابر چشم» — قدیمی‌ترین قانون مکتوب دنیا.",
    "358. کتابخانه اسکندریه، بزرگ‌ترین کتابخانه دنیای باستان، تا ۷۰۰٬۰۰۰ طومار داشت و سه بار آتش گرفت.",
    "359. کلئوپاترا ۷ زبان بلد بود و احتمالاً ریاضیات و فلسفه هم خونده بود.",
    "360. کاهنان مصری، راز تقویم ۳۶۵ روزه رو قرن‌ها مخفی نگه داشتن.",
    "361. سومری‌ها اولین مدرسه رو ساختن، با نمرات و تکالیف و معلم‌های سختگیر.",
    "362. بشر اولین بار تو بین‌النهرین، آبجو رو تصادفاً کشف کرد — نون خمیر رو تو آب گذاشتن، تخمیر شد.",
    "363. ایرانی‌ها اولین مردمی بودن که بادگیر (برج خنک‌کننده طبیعی) ساختن.",
    "364. خط میخی، ۳۰۰۰ سال استفاده می‌شد قبل از اینکه کسی بتونه رمزگشاییش کنه.",
    "365. مصری‌ها برای جلوگیری از فرار کارگران، بهشون آبجو و نون می‌دادن.",
    "366. یونانی‌ها تو المپیک باستان، کاملاً لخت مسابقه می‌دادن — کلمه gymnasium یعنی «محل لخت بودن».",
    "367. سقراط هیچ‌وقت چیزی ننوشت — همه چیزهایی که ازش می‌دونیم از شاگرداشه.",
    "368. ارشمیدس با یه آینه‌های بزرگ کشتی‌های رومی رو آتش زد — حداقل legend اینطوری می‌گه.",
    "369. رومی‌ها تو فاضلاب (Cloaca Maxima) ماهی نگه می‌داشتن که کیفیت آب رو نشون بده.",
    "370. سزار تو ۲۵ سالگی توسط دزدهای دریایی ربوده شد و بهشون گفت بعد آزادی همشون رو به صلیب می‌کشه — و همین کار رو کرد.",
    "371. نرون موقع آتش‌سوزی روم، شعر خوند — ولی احتمالاً خودش دستور آتش رو نداده.",
    "372. رومی‌ها تو فاضلاب شهری، ماهیگیر استخدام می‌کردن که گنج‌های افتاده رو پیدا کنن.",
    "373. امپراتور دیوکلتیان، ۲۰ سال قبل از مرگش، تاج و تخت رو گذاشت و کلم (کلم‌کاری) شروع کرد.",
    "374. تو روم باستان، ادرار رو جمع می‌کردن و برای شستشوی لباس و دباغی استفاده می‌کردن — و مالیات داشت.",
    "375. پمپئی موقع فوران وزوو در ۷۹ میلادی، یه شهر کامل با نان تو تنورها و غذا روی میزا دفن شد.",
    "376. رومی‌ها تو آمفی‌تئاتر، گاهی کشتی‌های جنگی کوچیک رو تو آب مصنوعی می‌جنگوند.",
    "377. اسپارتی‌ها بچه‌های ضعیف رو تو کوه می‌گذاشتن تا بمیرن — یا حداقل legend اینطوری می‌گه.",
    "378. تو آتن باستان، دموکراسی فقط برای مردهای آزاد بود — نه زنان، نه برده‌ها.",
    "379. رومی‌ها اولین مردمی بودن که بیمارستان نظامی ساختن.",
    "380. یونانی‌ها، پدر تاریخ‌نویسی (هرودوت) رو ساختن که همه‌اش سفر می‌کرد و داستان جمع می‌کرد.",
    "381. تو قرون وسطی، جوجه‌تیغی رو به عنوان شیطان می‌سوزوندن — یه حیوون بی‌گناه.",
    "382. دانشگاه‌های اروپا از کلیساها شروع شدن — آکسفورد و کمبریج ۹۰۰ ساله‌ن.",
    "383. تو قرون وسطی، پرتقال و لیمو کالای لوکس بودن، مثل طلا ارزش داشتن.",
    "384. لئوناردو داوینچی، فقط برای خودش آینه‌ای نوشتن (متن معکوس) می‌نوشت — دفترچه‌هاش به این شکل بودن.",
    "385. میکل‌آنژ موقع نقاشی سقف کلیسای سیستین، ۴ سال روی داربست دراز کشید و رنگ تو چشمش می‌رفت.",
    "386. نیکلاس کوپرنیک، انقلاب علمی رو شروع کرد، ولی کتابش تا بعد از مرگش چاپ شد — از ترس کلیسا.",
    "387. تو قرون وسطی، کلیساها ساعت نداشتن — زنگ کلیسا زمان رو می‌گفت.",
    "388. کریستف کلمب، همیشه فکر می‌کرد به هند رسیده، حتی وقتی تو آمریکا بود.",
    "389. ماژلان اولین کسی که دور دنیا رو گشت، تو راه مرد — سفرش ۳ سال طول کشید.",
    "390. تو قرون وسطی، مردم با دست می‌خوردن — چنگال تو قرن ۱۱ به اروپا اومد.",
    "391. تو رنسانس، ثروتمندان پرتره سفارش می‌دادن که خودشون رو تو لباس مقدسین بکشن.",
    "392. اولین کتاب چاپی گوتنبرگ، انجیل بود — ولی چاپ باعث شد دهقان‌ها هم سواد یاد بگیرن.",
    "393. تو قرون وسطی، کفش‌ها راست و چپ نداشتن — هر دو پا یه شکل بودن.",
    "394. ژان دارک، دختری ۱۹ ساله، ارتش فرانسه رو رهبری کرد و بعد از پیروزی، کلیسا سوزوندش.",
    "395. تو قرون وسطی، آب رو با آبجو جایگزین می‌کردن چون آب خالص مسموم بود — حتی بچه‌ها آبجو رقیق می‌خوردن.",
    "396. ابن‌سینا، ۱۰۰۰ سال پیش، درمان دیابت رو تو کتاب قانون کشف کرد.",
    "397. خوارزمی، مؤسس جبر، ریاضیات رو به اروپا معرفی کرد — کلمه Algorithm از اسمشه.",
    "398. بیرونی، در قرن ۱۱، قطر زمین رو حساب کرد — با اختلاف فقط ۲۰۰ کیلومتر از مقدار واقعی.",
    "399. رازی، اولین کسی که آبله و سرخک رو از هم تشخیص داد.",
    "400. ابن هیثم، ۱۰۰۰ سال پیش، قوانین نور و عدسی رو کشف کرد.",
    "401. مسلمان‌ها کاغذ رو از چینی‌ها به غرب معرفی کردن — اولین کارخانه کاغذ تو سمرقند بود.",
    "402. تو دربار هارون‌الرشید، یه سرای دانشمندی (بیت‌الحکمه) بود که ۱۰۰ مترجم کار می‌کردن.",
    "403. مسلمان‌ها بیمارستان‌هایی می‌ساختن که بخش‌های جدا برای مردان و زنان و بیماری‌های مختلف داشتن.",
    "404. فارابی، موسیقی رو به صورت ریاضی تحلیل کرد — کتاب موسیقی‌الکبیرش هنوز معتبره.",
    "405. سلطان محمود غزنوی، فردوسی رو تهدید کرد که اگه شاهنامه رو ننویسه، اعدام می‌شه.",
    "406. تو مسجدهای ایرانی، اگه تو محراب رو با صدای بلند بخونی، صدا چند بار اکو می‌شه — علم آکوستیک پیشرفته.",
    "407. زکریای رازی، شیمی رو از جادو جدا کرد و اولین آزمایشگاه علمی رو ساخت.",
    "408. خواجه نصیرالدین طوسی، رصدخانه مراغه رو ساخت که ۴۰۰٬۰۰۰ کتاب داشت.",
    "409. ایرانی‌ها اولین مردمی بودن که پمپ بنزین (تو سده ۱۹) راه‌اندازی کردن — شهر تبریز.",
    "410. کورش اول برای اینکه دشمن رو شکست بده، یه گربه‌رو تو سپرش گذاشت — بابلی‌ها گربه‌ها رو مقدس می‌دونستن.",
    "411. ناپلئون موقع لشکرکشی به مصر، ۱۶۷ دانشمند با خودش برد — یکی از اونا سنگ رشید رو کشف کرد.",
    "412. لویی شانزدهم موقع انقلاب فرانسه، تو ژورنال شخصیش نوشت «هیچ» برای روزی که باستیل سقوط کرد.",
    "413. اولین خط راه‌آهن، تو انگلیس ساخته شد — قبلش فکر می‌کردن قطار با سرعت ۳۰ کیلومتر برای بدن مضره.",
    "414. تو قرن ۱۹، پزشکان فکر می‌کردن شستن دست قبل از عمل لازم نیست — تا اینکه یه پزشک مجارستانی (زمله‌وایس) ثابت کرد و دیوانه خوندنش.",
    "415. اولین ماشین بخار واقعی رو جیمز وات کامل کرد، ولی ایده‌ش از یه یونانیه که ۲۰۰۰ سال قبل تو سده اول میلادی فکر کرد.",
    "416. توماس ادیسون، تو مدرسه فکر می‌کردن کودن و کر باشه — بعدش یکی از تأثیرگذارترین مخترعان تاریخ شد.",
    "417. تو ۱۸۸۹، تو پاریس برج ایفل رو ساختن که همه فکر می‌کردن زشته — الآن نماد فرانسه‌ست.",
    "418. اولین اتومبیل بنز، ۳ چرخ داشت و سرعتش ۱۶ کیلومتر بر ساعت بود.",
    "419. تو ۱۸۵۴، تو لندن یه کار می‌کردن با فاضلاب — «بوی بزرگ» تا پارلمان رو تعطیل کرد.",
    "420. نیکولا تسلا، برق متناوب رو اختراع کرد — ولی سودش رو کمپانی وستینگهاوس برد.",
    "421. ماری کوری، اولین زنی که نوبل گرفت، تو لهستان به دنیا اومد و از مردها هم بیشتر کار می‌کرد.",
    "422. اولین پیام تلگراف تو آمریکا «خداوند چه کارها که نکرده» بود.",
    "423. تو قرن ۱۹، بچه‌ها تو کارخونه‌های انگلیس ۱۶ ساعت کار می‌کردن — با دستمزد ناچیز.",
    "424. کتاب «کپیتال» مارکس، بعد از مرگش تکمیل شد — انگلس با پول کارخونه‌ش چاپش کرد.",
    "425. تو ۱۸۷۶، بل تلفن رو اختراع کرد، ولی مخترع واقعی آنتونیو موچی ایتالیایی بود که پول ثبت رو نداشت.",
    "426. تو جنگ جهانی اول، کریسمس ۱۹۱۴ سربازها تو سنگرها با هم فوتبال بازی کردن — افسران جلوگیری کردن.",
    "427. آلبرت اینشتین، نامه‌ای به روزولت نوشت که باعث ساخت بمب اتمی شد — بعدش پشیمون شد.",
    "428. تو جنگ جهانی دوم، انگلستان یه طرح داشت که با یخ و خاک‌اره یه ناو هواپیمابر بسازه — آزمایشش موفق بود ولی به کار نرسید.",
    "429. تو هولوکاست، بعضی از ژاپنی‌ها به یهودیان پناه دادن — چیونه سوگیهارا هزاران ویزا داد.",
    "430. تو ۱۹۴۵، یه سرباز ژاپنی (هیرو اونودا) ۲۹ سال تو جنگل مخفی موند چون باور نمی‌کرد جنگ تموم شده.",
    "431. جنگ سرد، فقط یه بار به جنگ گرم نزدیک شد: بحران موشکی کوبا ۱۹۶۲.",
    "432. تو ۱۹۶۹، آپولو ۱۱ یه کامپیوتر داشت که قدرت کمتر از یه گوشی امروزی داشت.",
    "433. برلین‌وال تو یه شب (۱۹۶۱) ساخته شد — مردم صبح بیدار شدن و دیدن شهرشون تقسیم شده.",
    "434. نلسون ماندلا، ۲۷ سال تو زندان بود و بعدش رئیس‌جمهور آفریقای جنوبی شد.",
    "435. گاندی، راهپیمایی نمک رو در ۱۹۳۰ شروع کرد که ۳۸۰ کیلومتر طول کشید — بدون هیچ خشونتی.",
    "436. تو ۱۹۸۶، فاجعه چرنوبیل اتفاق افتاد — کارکنان فکر می‌کردن راکتور امنه.",
    "437. اولین ویروس کامپیوتری، ۱۹۷۱ ساخته شد و اسمش «Creeper» بود.",
    "438. فروپاشی دیوار برلین، شب ۹ نوامبر ۱۹۸۹ — بی‌خونریزی، بدون جنگ.",
    "439. تیتانیک، ۱۹۱۲ غرق شد — ولی کشتی نزدیک‌تر (کالیفرنیا) سیگنال کمک رو خاموش کرده بود.",
    "440. تو ۱۹۲۹، بازار سهام آمریکا سقوط کرد و میلیون‌ها آدم شغلشون رو از دست دادن.",
    "441. تو انقلاب مشروطه، زنان ایرانی هم تو تظاهرات بودن — ولی بعد از انقلاب، حق رأی نداشتن.",
    "442. اولین فیلم سینمای ایران، تو ۱۳۰۹ ساخته شد — مضمونش داستان باستانی بود.",
    "443. تو جنگ جهانی دوم، ایران مسیر کمک‌های لندلیز به شوروی بود.",
    "444. تو ۱۳۳۰، مصدق نفت ایران رو ملی کرد — انگلیس با کودتای ۲۸ مرداد جوابش داد.",
    "445. اولین رادیو ایران، ۱۳۱۹ راه‌اندازی شد.",
    "446. تو دهه ۴۰، تهران دیوار و دروازه داشت — الآن فقط اسم‌هاشون مونده.",
    "447. اولین دانشگاه تهران، ۱۳۱۳ ساخته شد.",
    "448. تو انقلاب ۵۷، پرواز برگشت خمینی از پاریس، اولین بار تو تاریخ ایران بود که میلیون‌ها آدم یه نفرو استقبال می‌کردن.",
    "449. تو دهه ۶۰، ایران تو جنگ ۸ ساله با عراق، بیشترین تلفات رو بعد از جنگ جهانی دوم در یه درگیری داده.",
    "450. اولین مترو تهران، ۱۳۷۸ راه‌افتاد — ۲۵ سال طول کشید تا یه خط کامل بشه.",
    "451. تو قرون وسطی، کلیسا می‌گفت زمین مرکز عالمه — گالیله گفت نه، کلیسا مجبورش کرد توبه کنه.",
    "452. تو چین باستان، امپراتور تو ۱۸ سالگی به قدرت رسید و ۵۰ سال حکومت کرد.",
    "453. قبایل مغول، تو ۱۲۰۶ به رهبری چنگیزخان متحد شدن و ۱۰ میلیون کیلومتر مربع فتح کردن.",
    "454. امپراتوری عثمانی ۶۲۳ سال (از ۱۲۹۹ تا ۱۹۲۲) دووم آورد.",
    "455. اولین بار که چای به انگلیس رسید، به عنوان دارو فروخته می‌شد.",
    "456. قهوه تو اتیوپی کشف شد — چوپانی دید بزاش بعد خوردن دانه قهوه سرحال‌ترن.",
    "457. شکلات تو آمریکای جنوبی به عنوان نوشیدنی تلخ استفاده می‌شد — حتی با فلفل.",
    "458. تو قرون وسطی، شکر و نمک و فلفل، تو گاوصندوق نگه داشته می‌شد.",
    "459. تو ۱۸۳۳، انگلیس برده‌داری رو لغو کرد — ولی ۲۰ میلیون پوند به برده‌دارها غرامت داد.",
    "460. تو قرن ۱۷، بیشتر دزدان دریایی (Pirate) دموکراتیک بودن — رئیسشون رو انتخاب می‌کردن.",
    "461. اولین پاسپورت مدرن، تو ۱۹۱۴ تو انگلیس صادر شد.",
    "462. تو یونان باستان، ورزشکارا با روغن زیتون بدنشون رو چرب می‌کردن قبل مسابقه.",
    "463. تو چین باستان، کفش‌ها رو از کاغذ می‌ساختن برای مراسم عزاداری.",
    "464. مغول‌ها یه سیستم پستی (یام) داشتن که سریع‌ترین ارتباط دنیا بود — ۳۰۰ کیلومتر در روز.",
    "465. ژولیوس سزار، هر روز ۱۰۰ نامه می‌نوشت و هم‌زمان دو تا منشی داشت که هم‌زمان دیکته کنه.",
    "466. تو چین باستان، ابریشم رو از کرم ابریشم استخراج می‌کردن و رازش رو ۳۰۰۰ سال مخفی نگه داشتن.",
    "467. تو مصر باستان، پزشکان زن هم بودن — اولین پزشک زن تاریخ، پسشِت نام داشت.",
    "468. تو روم باستان، گاهی سربازا رو برای فرار از جنگ، به خاطر بزدلی اعدام می‌کردن.",
    "469. تو ژاپن فئودال، سامورایی‌ها اگه آبروشون می‌رفت، خودکشی می‌کردن (هاراکیری).",
    "470. اولین تلفن همراه تجاری، ۱۹۸۳ Motorola DynaTAC — ۱ کیلوگرم وزن داشت و ۳۰ دقیقه شارژ می‌گرفت.",
    "471. اولین ایمیل، ۱۹۷۱ فرستاده شد — ولی فقط تو شبکه داخلی ARPANET بود.",
    "472. اولین وب‌سایت، ۱۹۹۱ تو CERN ساخته شد — هنوز قابل دسترسیه.",
    "473. تو دهه ۹۰، گوگل تو گاراژ یه خونه اجاره‌ای راه‌اندازی شد — بدون هیچ سرمایه‌ای.",
    "474. مایکروسافت، از یه شرکت کوچیک که تو گاراژ کار می‌کرد، به یه غول نرم‌افزاری تبدیل شد.",
    "475. اپل تو ۱۹۷۶، تو گاراژ استیو جابز ساخته شد — اولین سرمایه‌ش ۱۳۰۰ دلار از فروش یه فولکس‌واگن بود.",
    "476. تو یونان باستان، مسابقات المپیک به خاطر جنگ‌ها متوقف می‌شد — حتی جنگ‌ها برای المپیک تعطیل می‌شد.",
    "477. تو روم باستان، گاهی امپراتورها توسط گارد شخصی‌شون کشته می‌شدن — از ۴۵ امپراتور، ۳۰ تاش به قتل رسیدن.",
    "478. تو چین باستان، اگه کسی کتاب اشتباه می‌نوشت، اعدام می‌شد.",
    "479. تو قرون وسطی، کلیسا کتاب‌های ممنوعه رو می‌سوزوند — برخی از اون کتاب‌ها بعداً به عنوان کلاسیک شناخته شدن.",
    "480. تو ۱۷۷۶، آدام اسمیت کتاب «ثروت ملل» رو نوشت که پایه‌ی اقتصاد مدرن شد.",
    "481. تو ۱۸۴۸، مارکس و انگلس «مانیفست کمونیست» رو چاپ کردن که انقلاب‌های قرن بیستم رو الهام داد.",
    "482. تو ۱۸۶۷، کانادا تأسیس شد — ولی بیشتر توافق‌ها تو قطار به دست اومد.",
    "483. تو ۱۸۶۹، کانال سوئز افتتاح شد — ۱۰ سال ساختش طول کشید.",
    "484. تو ۱۸۹۱، اولین اتومبیل بنزین‌سوز که مسافرت شهری کرد، یه بنز بود با راننده آلمانی.",
    "485. تو ۱۹۰۱، نوبل جایزه‌ها تأسیس شد — آلفرد نوبل مخترع دینامیت بود و از اختراعش پشیمون.",
    "486. تو ۱۹۰۳، اولین پرواز هواپیمای برادران رایت ۱۲ ثانیه طول کشید.",
    "487. تو ۱۹۰۸، هنری فورد اولین مدل T رو ساخت — رنگ‌های متنوع داشت، ولی فقط مشکی سریع تولید می‌شد.",
    "488. تو ۱۹۱۲، تایتانیک غرق شد — ۱۵۰۰ نفر مردن، ولی ۷۰۵ نفر نجات پیدا کردن.",
    "489. تو ۱۹۱۴، شروع جنگ جهانی اول — یه ترور تو سارایوو شروعش کرد.",
    "490. تو ۱۹۱۷، انقلاب اکتبر روسیه — لنین از تبعید با قطار مخصوص آلمان برگشت.",
    "491. تو ۱۹۱۸، آنفلوآنزای اسپانیایی ۵۰ میلیون نفر رو کشت — بیشتر از کل کشته‌های جنگ جهانی اول.",
    "492. تو ۱۹۱۹، معاهده ورسای امضا شد — آلمان مجبور شد تاوان سنگین بده.",
    "493. تو ۱۹۲۹، سقوط وال استریت — یه پنج‌شنبه سیاه که جهان رو به رکود بزرگ برد.",
    "494. تو ۱۹۳۳، هیتلر صدراعظم آلمان شد — با رأی دموکراتیک، نه با کودتا.",
    "495. تو ۱۹۳۹، جنگ جهانی دوم با حمله به لهستان شروع شد.",
    "496. تو ۱۹۴۱، حمله ژاپن به پرل هاربر — آمریکا وارد جنگ شد.",
    "497. تو ۱۹۴۴، فرود نرماندی — بزرگ‌ترین حمله آبی-خاکی تاریخ.",
    "498. تو ۱۹۴۵، بمباران هیروشیما و ناکازاکی — اولین و آخرین استفاده از بمب اتمی در جنگ.",
    "499. تو ۱۹۴۷، استقلال هند و پاکستان — همراه با کوچ بزرگ و کشتار فرقه‌ای.",
    "500. تو ۱۹۴۸، تأسیس اسرائیل — شروع یه درگیری که هنوز ادامه داره.",
    "501. تو ۱۹۴۹، تأسیس ناتو — پاسخ غرب به اتحاد شوروی.",
    "502. تو ۱۹۵۰، شروع جنگ کره — هنوز رسماً تموم نشده، فقط آتش‌بس شده.",
    "503. تو ۱۹۵۳، کودتای ۲۸ مرداد تو ایران — مصدق سقوط کرد، شاه برگشت.",
    "504. تو ۱۹۵۵، کنفرانس باندونگ — کشورهای آفریقایی و آسیایی متحد شدن.",
    "505. تو ۱۹۵۷، اسپوتنیک به فضا رفت — مسابقه فضایی شروع شد.",
    "506. تو ۱۹۶۱، گاگارین اولین انسان تو فضا — ولی آمریکا ۸ سال بعد به ماه رسید.",
    "507. تو ۱۹۶۲، بحران موشکی کوبا — نزدیک‌ترین لحظه به جنگ هسته‌ای.",
    "508. تو ۱۹۶۳، ترور جان اف کندی تو دالاس — هنوز راز کاملش حل نشده.",
    "509. تو ۱۹۶۸، بهار پراگ تو چکسلواکی — شوروی با تانک سرکوبش کرد.",
    "510. تو ۱۹۶۹، نیل آرمسترانگ اولین انسانی که روی ماه قدم گذاشت.",
    "511. تو ۱۹۷۱، استقلال بنگلادش — از پاکستان جدا شد.",
    "512. تو ۱۹۷۳، جنگ اکتبر — کشورهای عربی حمله به اسرائیل، جهان نفت رو تحریم کرد.",
    "513. تو ۱۹۷۸، پیمان کمپ دیوید — صلح مصر و اسرائیل.",
    "514. تو ۱۹۷۹، انقلاب ایران — شاه رفت، جمهوری اسلامی آمد.",
    "515. تو ۱۹۸۰، شروع جنگ ایران و عراق — ۸ سال طول کشید.",
    "516. تو ۱۹۸۱، ترور انور سادات — به خاطر پیمان صلح با اسرائیل.",
    "517. تو ۱۹۸۵، گورباچف رهبر شوروی — شروع گلاسنوست و پرسترویکا.",
    "518. تو ۱۹۸۶، فاجعه چرنوبیل — بدترین حادثه هسته‌ای تاریخ.",
    "519. تو ۱۹۸۹، سقوط دیوار برلین — فروپاشی شوروی نزدیک شد.",
    "520. تو ۱۹۹۱، فروپاشی شوروی — ۱۵ جمهوری مستقل شدن.",
    "521. تو ۱۹۹۳، اتحادیه اروپا تأسیس شد — با پیمان ماستریخت.",
    "522. تو ۱۹۹۴، نسل‌کشی رواندا — ۸۰۰٬۰۰۰ نفر تو ۱۰۰ روز کشته شدن.",
    "523. تو ۱۹۹۷، مرگ دایانا — میلیون‌ها نفر تو مراسمش شرکت کردن.",
    "524. تو ۲۰۰۱، حمله ۱۱ سپتامبر — شروع جنگ جهانی علیه تروریسم.",
    "525. تو ۲۰۰۸، بحران اقتصادی جهانی — لیمن برادرز سقوط کرد.",
    "526. تو ۲۰۱۱، بهار عربی — چندین دیکتاتور تو خاورمیانه سقوط کردن.",
    "527. تو ۲۰۱۹، آتش‌سوزی نوتردام پاریس — یکی از نمادهای تمدن اروپا آسیب دید.",
    "528. تو ۲۰۲۰، پاندمی کرونا — بیش از ۷ میلیون نفر کشته شدن.",
    "529. تو ۲۰۲۲، تهاجم روسیه به اوکراین — بزرگ‌ترین جنگ اروپا بعد از جنگ جهانی دوم.",
    "530. تو ۲۰۲۳، هوش مصنوعی GPT جهش‌هایی تو همه صنایع ایجاد کرد — عصر جدیدی شروع شد.",
    "531. فینیقی‌ها الفبای ۲۲ حرفی رو ساختن که پایه‌ی همه‌ی الفباهای دنیاست — از عربی تا لاتین.",
    "532. اولین مسجد تاریخ اسلام (مسجد قبا) توسط پیامبر و یارانش، تو مدینه ساخته شد — ۱۴۰۰ سال پیش.",
    "533. اولین سکهٔ تاریخ، تو لیدیا (ترکیه امروزی) ضرب شد — از طلا و نقره.",
    "534. تو ایران باستان، نوروز برای اولین بار در زمان داریوش بزرگ به عنوان جشن رسمی ثبت شد.",
    "535. اسلام تو مدت کمتر از ۱۰۰ سال، از مکه تا اسپانیا و هند گسترش پیدا کرد — با تجارت و تعامل فرهنگی، نه فقط جنگ.",
    "536. تو قرون وسطی، پزشکان مسلمان اولین کسانی بودن که بیهوشی رو تو عمل‌های جراحی به کار بردن.",
    "537. تو مسجدهای بزرگ، کتابخانه‌های عظیم همراه بودن — دانش فقط برای نماز نبود، برای تحقیق هم بود.",
    "538. ایرانی‌ها، پل‌های قوسی سنگی رو ۲۵۰۰ سال پیش ساختن — پل دختر، هنوز پا برجاست.",
    "539. تو سلسله صفویه، ایران رسماً شیعه شد — تحولی که کل تاریخ منطقه رو تغییر داد.",
    "540. اولین بار که فوتبال به ایران اومد، توسط انگلیسی‌های شاغل تو صنعت نفت بود — حدود ۱۹۰۰ میلادی.",
    "541. اولین رمان فارسی، «حاجی بابای اصفهانی» نوشته جیمز موریه بود — بعدها ترجمه شد.",
    "542. کتابخانه ملی ایران، تو ۱۳۱۶ تأسیس شد — با کمک باستان‌شناسان فرانسوی.",
    "543. ملکه ویکتوریا، ۶۳ سال حکومت کرد — طولانی‌ترین سلطنت در تاریخ بریتانیا.",
    "544. تو مصر باستان، هرودوت نوشت: «مصر هدیه نیل است» — چون بدون نیل، مصر صحرا بود.",
    "545. تو روم باستان، گاهی بردگان آزاد می‌شدن و به مقام‌های بالا می‌رسیدن — برخلاف تصور عموم.",
    "546. اولین مسابقه فرمول یک، ۱۹۵۰ تو سیلورستون انگلیس — ۷ تیم و ۲۱ راننده شرکت کردن.",
    "547. اولین بازی ویدیویی تجاری، ۱۹۷۲ (Pong) — موفقیتش انفجاری بود.",
    "548. اولین شبکه اجتماعی، ۱۹۹۷ SixDegrees — پیش از فیسبوک، مای‌اسپیس و توییتر.",
    "549. موتور جستجوی گوگل، ۱۹۹۸ تو گاراژ یه خونه اجاره‌ای در کالیفرنیا راه‌اندازی شد — با سرمایه کم و دو نفر بنیان‌گذار.",
    "550. اولین همایش بین‌المللی زنان، ۱۸۴۸ تو نیویورک — شروع جنبش مدرن حقوق زنان.",
]


# ---------------------------------------------------------------------------
# 🎯 کوییز — نظرسنجی بومی (حالت آزمون)
# ---------------------------------------------------------------------------
_QUIZ_QUESTIONS: List[Dict[str, Any]] = [
    # ═══════════════ 🌍 جغرافیا — پایتخت‌های چالشی ═══════════════
    {"q": "پایتخت استرالیا کدام شهر است؟",
     "options": ["سیدنی", "کانبرا", "ملبورن", "بریزبن"], "answer": 1},
    {"q": "پایتخت کانادا کدام است؟",
     "options": ["تورنتو", "ونکوور", "اتاوا", "مونترال"], "answer": 2},
    {"q": "پایتخت ترکیه کدام شهر است؟",
     "options": ["استانبول", "ازمیر", "آنکارا", "بورسا"], "answer": 2},
    {"q": "پایتخت سوئیس کدام است؟",
     "options": ["زوریخ", "ژنو", "برن", "بازل"], "answer": 2},
    {"q": "پایتخت برزیل کدام است؟",
     "options": ["ریو دو ژانیرو", "سائوپائولو", "برازیلیا", "سالوادور"], "answer": 2},
    {"q": "پایتخت نیوزیلند کدام است؟",
     "options": ["آکلند", "ولینگتون", "کرایست‌چرچ", "همیلتون"], "answer": 1},
    {"q": "پایتخت ویتنام کدام است؟",
     "options": ["هوشی‌مین", "هانوی", "دانانگ", "هوئه"], "answer": 1},
    {"q": "پایتخت مراکش کدام است؟",
     "options": ["کازابلانکا", "رباط", "مراکش", "فاس"], "answer": 1},
    {"q": "پایتخت قزاقستان کدام است؟",
     "options": ["آلماتی", "آستانه", "شیمکنت", "قراغندی"], "answer": 1},
    {"q": "پایتخت میانمار کدام است؟",
     "options": ["یانگون", "نایپیداو", "ماندالای", "بگو"], "answer": 1},
    {"q": "پایتخت کدام کشور، بزرگ‌ترین شهر آن نیست؟",
     "options": ["فرانسه", "ترکیه", "انگلیس", "اسپانیا"], "answer": 1},
    {"q": "پایتخت ژاپن کدام شهر است؟",
     "options": ["اوساکا", "توکیو", "کیوتو", "ناگویا"], "answer": 1},
    {"q": "پایتخت ایران کدام شهر است؟",
     "options": ["اصفهان", "مشهد", "تهران", "شیراز"], "answer": 2},
    {"q": "پایتخت استرالیا نام کدام کلمه بومی است؟",
     "options": ["محل ملاقات", "سرزمین آفتاب", "کنار دریا", "کوه مقدس"], "answer": 0},
    {"q": "پایتخت آلمان کدام شهر است؟",
     "options": ["مونیخ", "هامبورگ", "برلین", "فرانکفورت"], "answer": 2},
    {"q": "پایتخت روسیه کدام شهر است؟",
     "options": ["سن‌پترزبورگ", "مسکو", "کی‌یف", "مینسک"], "answer": 1},
    {"q": "پایتخت چین کدام شهر است؟",
     "options": ["شانگهای", "پکن", "هنگ‌کنگ", "گوانگژو"], "answer": 1},
    {"q": "پایتخت پرتغال کدام است؟",
     "options": ["پورتو", "لیسبون", "کوئیمبرا", "فارو"], "answer": 1},
    {"q": "پایتخت امارات متحده عربی کدام است؟",
     "options": ["دبی", "ابوظبی", "شارجه", "عجمان"], "answer": 1},
    {"q": "پایتخت هند کدام شهر است؟",
     "options": ["بمبئی", "دهلی نو", "کلکته", "چنای"], "answer": 1},
    {"q": "پایتخت آرژانتین کدام است؟",
     "options": ["سانتیاگو", "بوئنوس آیرس", "لیما", "بوگوتا"], "answer": 1},
    {"q": "پایتخت استرالیا کدام ایالت است؟",
     "options": ["نیو ساوت ولز", "قلمرو پایتختی", "کوئینزلند", "ویکتوریا"], "answer": 1},
    {"q": "پایتخت سوئد کدام است؟",
     "options": ["گوتنبرگ", "مالمو", "استکهلم", "اوپسالا"], "answer": 2},
    {"q": "پایتخت نروژ کدام است؟",
     "options": ["برگن", "اسلو", "تروندهایم", "استاوانگر"], "answer": 1},
    {"q": "پایتخت کره جنوبی کدام است؟",
     "options": ["بوسان", "سئول", "اینچئون", "تگو"], "answer": 1},
    {"q": "پایتخت کره شمالی کدام است؟",
     "options": ["سئول", "پیونگ‌یانگ", "چونگ‌جین", "هامهونگ"], "answer": 1},
    {"q": "پایتخت افغانستان کدام است؟",
     "options": ["هرات", "کابل", "قندهار", "مزار شریف"], "answer": 1},
    {"q": "پایتخت پاکستان کدام است؟",
     "options": ["کراچی", "لاهور", "اسلام‌آباد", "پیشاور"], "answer": 2},
    {"q": "پایتخت عراق کدام است؟",
     "options": ["بصره", "موصل", "بغداد", "اربیل"], "answer": 2},
    {"q": "پایتخت عربستان سعودی کدام است؟",
     "options": ["جده", "مکه", "ریاض", "دمام"], "answer": 2},
    {"q": "پایتخت مصر کدام شهر است؟",
     "options": ["اسکندریه", "قاهره", "پورت‌سعید", "اقصر"], "answer": 1},
    {"q": "پایتخت یونان کدام است؟",
     "options": ["سالونیک", "آتن", "پاتراس", "کرت"], "answer": 1},
    {"q": "پایتخت مکزیک کدام است؟",
     "options": ["گوادالاخارا", "مونتری", "مکزیکوسیتی", "کانکون"], "answer": 2},
    {"q": "پایتخت لبنان کدام است؟",
     "options": ["طرابلس", "بیروت", "صور", "صیدا"], "answer": 1},
    {"q": "پایتخت اردن کدام است؟",
     "options": ["عمّان", "اربد", "زرقاء", "عقبه"], "answer": 0},

    # ═══════════════ 🌍 جغرافیا — طبیعی و پدیده‌ها ═══════════════
    {"q": "بزرگ‌ترین اقیانوس جهان کدام است؟",
     "options": ["اطلس", "هند", "آرام", "منجمد شمالی"], "answer": 2},
    {"q": "بلندترین رود جهان کدام است؟",
     "options": ["آمازون", "نیل", "می‌سی‌سی‌پی", "یانگ‌تسه"], "answer": 1},
    {"q": "پرجمعیت‌ترین رودخانه‌ی حوضه‌ی آبریز کدام است؟",
     "options": ["نیل", "آمازون", "گنگ", "می‌سی‌سی‌پی"], "answer": 1},
    {"q": "بزرگ‌ترین دریاچهٔ جهان کدام است؟",
     "options": ["بایکال", "خزر", "ویکتوریا", "سوپریور"], "answer": 1},
    {"q": "عمیق‌ترین دریاچهٔ جهان کدام است؟",
     "options": ["خزر", "بایکال", "ویکتوریا", "تانگانیکا"], "answer": 1},
    {"q": "بلندترین آبشار جهان کدام است؟",
     "options": ["نیاگارا", "آنجل", "ویکتوریا", "ایگوآزو"], "answer": 1},
    {"q": "بلندترین برج جهان کدام است؟",
     "options": ["برج خلیفه", "برج شانگهای", "برج ایفل", "تایپه ۱۰۱"], "answer": 0},
    {"q": "بزرگ‌ترین صحرای گرم جهان کدام است؟",
     "options": ["گبی", "صحرای آفریقا", "کالاهاری", "لوت"], "answer": 1},
    {"q": "بزرگ‌ترین بیابان جهان (با احتساب قطبی) کدام است؟",
     "options": ["صحرای آفریقا", "قطب جنوب", "گبی", "کالاهاری"], "answer": 1},
    {"q": "بزرگ‌ترین جزیره جهان کدام است؟",
     "options": ["ماداگاسکار", "گرینلند", "بورنئو", "گینه نو"], "answer": 1},
    {"q": "بزرگ‌ترین شبه‌جزیره جهان کدام است؟",
     "options": ["عربستان", "بالکان", "هند", "ایبری"], "answer": 0},
    {"q": "دریایی که بیشترین شوری را دارد؟",
     "options": ["سرخ", "مرده", "مدیترانه", "خزر"], "answer": 1},
    {"q": "کدام دریاچه در حال خشک شدن است و زمانی بزرگ‌ترین دریاچه خاورمیانه بود؟",
     "options": ["ارومیه", "هامون", "بختگان", "پریشان"], "answer": 0},
    {"q": "بلندترین قلهٔ جهان کدام است؟",
     "options": ["K2", "اورست", "دماوند", "مونبلان"], "answer": 1},
    {"q": "بلندترین قلهٔ ایران کدام است؟",
     "options": ["سبلان", "دماوند", "الوند", "تفتان"], "answer": 1},
    {"q": "دماوند در کدام استان است؟",
     "options": ["تهران", "مازندران", "البرز", "قزوین"], "answer": 1},
    {"q": "بلندترین قلهٔ اروپا کدام است؟",
     "options": ["مونبلان", "البروس", "کازبک", "اورست"], "answer": 1},
    {"q": "بلندترین قلهٔ آفریقا کدام است؟",
     "options": ["کلیمانجارو", "کنیا", "اطلس", "الگون"], "answer": 0},

    # ═══════════════ 🌍 جغرافیا — کشورها و رکوردها ═══════════════
    {"q": "بزرگ‌ترین کشور جهان از نظر مساحت کدام است؟",
     "options": ["کانادا", "چین", "آمریکا", "روسیه"], "answer": 3},
    {"q": "کوچک‌ترین کشور جهان کدام است؟",
     "options": ["موناکو", "واتیکان", "سن‌مارینو", "مالت"], "answer": 1},
    {"q": "کدام کشور بیشترین جمعیت جهان را دارد؟",
     "options": ["چین", "هند", "آمریکا", "اندونزی"], "answer": 1},
    {"q": "کدام کشور بیشترین همسایه را دارد؟",
     "options": ["روسیه", "چین", "برزیل", "آلمان"], "answer": 0},
    {"q": "کدام کشور دو قاره دارد؟",
     "options": ["ترکیه", "مصر", "هر دو", "یونان"], "answer": 2},
    {"q": "کدام کشور بیشترین جزیره را دارد؟",
     "options": ["اندونزی", "سوئد", "فیلیپین", "ژاپن"], "answer": 1},
    {"q": "زبان رسمی برزیل چیست؟",
     "options": ["اسپانیایی", "پرتغالی", "انگلیسی", "فرانسوی"], "answer": 1},
    {"q": "کدام کشور به «سرزمین طلوع خورشید» معروف است؟",
     "options": ["چین", "ژاپن", "کره", "تایلند"], "answer": 1},
    {"q": "کدام کشور به «سرزمین اژدهای سبز» معروف است؟",
     "options": ["چین", "ویتنام", "بوتان", "نپال"], "answer": 1},
    {"q": "کدام اقیانوس بین آفریقا و آمریکا قرار دارد؟",
     "options": ["آرام", "اطلس", "هند", "منجمد شمالی"], "answer": 1},
    {"q": "بلندترین خط آهن جهان در کدام کشور است؟",
     "options": ["روسیه", "چین", "هند", "آمریکا"], "answer": 0},
    {"q": "پرجمعیت‌ترین کشور آفریقا کدام است؟",
     "options": ["مصر", "نیجریه", "اتیوپی", "آفریقای جنوبی"], "answer": 1},
    {"q": "کدام کشور در دو قاره آمریکا قرار گرفته است؟",
     "options": ["مکزیک", "پاناما", "کلمبیا", "کوبا"], "answer": 1},

    # ═══════════════ 🔬 علوم — فیزیک و شیمی ═══════════════
    {"q": "کدام سیاره به «سیارهٔ سرخ» معروف است؟",
     "options": ["زهره", "مریخ", "مشتری", "زحل"], "answer": 1},
    {"q": "قانون جاذبه توسط چه کسی کشف شد؟",
     "options": ["گالیله", "نیوتن", "اینشتین", "داوینچی"], "answer": 1},
    {"q": "نظریهٔ نسبیت توسط چه کسی مطرح شد؟",
     "options": ["نیوتن", "اینشتین", "بور", "پلانک"], "answer": 1},
    {"q": "کدام فلز در دمای اتاق مایع است؟",
     "options": ["آهن", "جیوه", "طلا", "مس"], "answer": 1},
    {"q": "نماد شیمیایی طلا چیست؟",
     "options": ["Ag", "Au", "Fe", "Cu"], "answer": 1},
    {"q": "نماد شیمیایی سدیم چیست؟",
     "options": ["Na", "So", "Sd", "Sm"], "answer": 0},
    {"q": "نماد شیمیایی پتاسیم چیست؟",
     "options": ["P", "Po", "K", "Pt"], "answer": 2},
    {"q": "نماد شیمیایی نمک خوراکی چیست؟",
     "options": ["CO2", "H2O", "O2", "NaCl"], "answer": 3},
    {"q": "عدد اتمی کربن چند است؟",
     "options": ["۴", "۶", "۱۲", "۱۴"], "answer": 1},
    {"q": "کدام گاز بیشترین سهم را در جو زمین دارد؟",
     "options": ["اکسیژن", "نیتروژن", "دی‌اکسید کربن", "آرگون"], "answer": 1},
    {"q": "اتم از چه چیزهایی ساخته شده؟",
     "options": ["فقط پروتون", "پروتون، نوترون، الکترون", "فقط الکترون", "فقط نوترون"], "answer": 1},
    {"q": "در جدول تناوبی، تعداد عناصر شناخته‌شده حدوداً چقدر است؟",
     "options": ["۶۰", "۹۰", "۱۱۸", "۲۰۰"], "answer": 2},
    {"q": "جدول تناوبی توسط چه کسی ساخته شد؟",
     "options": ["مندلیف", "دالتون", "لاووازیه", "رادرفورد"], "answer": 0},
    {"q": "صفر مطلق چند درجه سلسیوس است؟",
     "options": ["-۱۰۰", "-۲۷۳", "-۳۷۳", "۰"], "answer": 1},
    {"q": "سرعت نور چقدر است؟",
     "options": ["۳۰۰ کیلومتر بر ثانیه", "۳۰۰٬۰۰۰ کیلومتر بر ثانیه", "۳۰۰۰ کیلومتر بر ثانیه", "۳۰ کیلومتر بر ثانیه"], "answer": 1},
    {"q": "کدام ذره بار منفی دارد؟",
     "options": ["پروتون", "نوترون", "الکترون", "پوزیترون"], "answer": 2},
    {"q": "نیروی ضعیف و قوی هسته‌ای مربوط به کدام بخش فیزیک است؟",
     "options": ["مکانیک کلاسیک", "فیزیک اتمی و هسته‌ای", "نسبیت عام", "ترمودینامیک"], "answer": 1},
    {"q": "کدام عنصر فراوان‌ترین عنصر در پوسته زمین است؟",
     "options": ["آهن", "اکسیژن", "سیلیس", "آلومینیوم"], "answer": 1},

    # ═══════════════ 🔭 نجوم ═══════════════
    {"q": "بزرگ‌ترین سیارهٔ منظومهٔ شمسی کدام است؟",
     "options": ["زحل", "مشتری", "اورانوس", "نپتون"], "answer": 1},
    {"q": "نزدیک‌ترین سیاره به خورشید کدام است؟",
     "options": ["زهره", "عطارد", "زمین", "مریخ"], "answer": 1},
    {"q": "دورترین سیارهٔ منظومهٔ شمسی کدام است؟",
     "options": ["نپتون", "اورانوس", "پلوتو", "زحل"], "answer": 0},
    {"q": "چند سیاره در منظومهٔ شمسی وجود دارد؟",
     "options": ["۷", "۸", "۹", "۱۰"], "answer": 1},
    {"q": "در کدام سیاره طوفان معروف «چشم» وجود دارد؟",
     "options": ["مشتری", "زحل", "نپتون", "اورانوس"], "answer": 0},
    {"q": "بزرگ‌ترین قمر منظومهٔ شمسی کدام است؟",
     "options": ["تیتان", "گانیمد", "کالیستو", "اروپا"], "answer": 1},
    {"q": "مریخ چند قمر دارد؟",
     "options": ["۱", "۲", "۳", "۴"], "answer": 1},
    {"q": "نزدیک‌ترین ستاره به زمین بعد از خورشید کدام است؟",
     "options": ["آلفا قنطورس A", "پروکسیما قنطورس", "شباهنگ", "قطبی"], "answer": 1},
    {"q": "نور خورشید چند دقیقه طول می‌کشد تا به زمین برسد؟",
     "options": ["۱ دقیقه", "۸ دقیقه", "۳۰ دقیقه", "۱ ساعت"], "answer": 1},
    {"q": "کهکشان ما نامش چیست؟",
     "options": ["آندرومدا", "راه شیری", "مسیه ۸۷", "سومبررو"], "answer": 1},
    {"q": "حدوداً چند ستاره در کهکشان راه شیری وجود دارد؟",
     "options": ["هزار", "میلیون", "۱۰۰ میلیارد", "۱ میلیارد"], "answer": 2},
    {"q": "کهکشان آندرومدا چه نسبتی با راه شیری دارد؟",
     "options": ["کوچک‌تر است", "هم‌اندازه است و در حال نزدیک شدن", "دورتر از تصور", "بخشی از راه شیری است"], "answer": 1},
    {"q": "خورشید در کدام لایه اتمسفرش دمای بالاتری دارد؟",
     "options": ["سطح", "تاج (کرونا)", "هسته", "هیچ‌کدام"], "answer": 1},

    # ═══════════════ 🧬 زیست‌شناسی و بدن انسان ═══════════════
    {"q": "بلندترین حیوان جهان کدام است؟",
     "options": ["فیل", "زرافه", "شتر", "کرگدن"], "answer": 1},
    {"q": "سریع‌ترین حیوان خشکی کدام است؟",
     "options": ["شیر", "یوزپلنگ", "اسب", "آهو"], "answer": 1},
    {"q": "بزرگ‌ترین پستاندار جهان کدام است؟",
     "options": ["فیل", "نهنگ آبی", "کرگدن", "زرافه"], "answer": 1},
    {"q": "سریع‌ترین پرنده جهان کدام است؟",
     "options": ["عقاب", "شاهین", "قوش", "باز"], "answer": 1},
    {"q": "کدام حیوان به «کشتی صحرا» معروف است؟",
     "options": ["اسب", "شتر", "الاغ", "گاو"], "answer": 1},
    {"q": "قلب انسان چند حفره دارد؟",
     "options": ["۲", "۳", "۴", "۵"], "answer": 2},
    {"q": "بدن انسان از چند استخوان ساخته شده؟",
     "options": ["۱۵۰", "۲۰۶", "۲۵۰", "۳۰۰"], "answer": 1},
    {"q": "کوچک‌ترین استخوان بدن انسان کدام است؟",
     "options": ["رکابی", "سندانی", "چکشی", "بینام"], "answer": 0},
    {"q": "بزرگ‌ترین اندام داخلی بدن انسان کدام است؟",
     "options": ["کبد", "قلب", "کلیه", "مغز"], "answer": 0},
    {"q": "کدام عضو بدن انسولین تولید می‌کند؟",
     "options": ["کبد", "لوزالمعده", "کلیه", "طحال"], "answer": 1},
    {"q": "کدام ویتامین از نور خورشید به دست می‌آید؟",
     "options": ["A", "B", "C", "D"], "answer": 3},
    {"q": "چند کروموزوم در انسان وجود دارد؟",
     "options": ["۲۳", "۴۶", "۲۲", "۴۸"], "answer": 1},
    {"q": "چند دندان در دهان انسان بالغ وجود دارد؟",
     "options": ["۲۰", "۲۸", "۳۲", "۳۶"], "answer": 2},
    {"q": "کدام سلول‌ها در خون اکسیژن حمل می‌کنند؟",
     "options": ["گلبول سفید", "گلبول قرمز", "پلاکت", "پلاسما"], "answer": 1},
    {"q": "کدام اندام مسئول تصفیه خون است؟",
     "options": ["کبد", "کلیه", "طحال", "قلب"], "answer": 1},
    {"q": "بزرگ‌ترین سلول بدن انسان کدام است؟",
     "options": ["سلول عصبی", "تخمک", "سلول عضلانی", "گلبول سفید"], "answer": 1},
    {"q": "پدر علم پزشکی کیست؟",
     "options": ["بقراط", "ابن‌سینا", "جالینوس", "رازی"], "answer": 0},
    {"q": "«قانون در طب» اثر چه کسی است؟",
     "options": ["بقراط", "ابن‌سینا", "رازی", "فارابی"], "answer": 1},
    {"q": "DNA در کدام بخش سلول قرار دارد؟",
     "options": ["غشا", "هسته", "ریبوزوم", "سیتوپلاسم"], "answer": 1},
    {"q": "فتوسنتز در کدام اندامک سلول گیاهی انجام می‌شود؟",
     "options": ["میتوکندری", "کلروپلاست", "ریبوزوم", "هسته"], "answer": 1},

    # ═══════════════ 📚 ادبیات فارسی ═══════════════
    {"q": "«شاهنامه» اثر چه کسی است؟",
     "options": ["سعدی", "حافظ", "فردوسی", "مولانا"], "answer": 2},
    {"q": "«بوستان» و «گلستان» اثر چه کسی است؟",
     "options": ["فردوسی", "سعدی", "مولانا", "خیام"], "answer": 1},
    {"q": "«مثنوی معنوی» اثر چه کسی است؟",
     "options": ["حافظ", "سعدی", "مولانا", "عطار"], "answer": 2},
    {"q": "حافظ اهل کدام شهر بود؟",
     "options": ["اصفهان", "شیراز", "تبریز", "نیشابور"], "answer": 1},
    {"q": "«خمسه» یا «پنج گنج» اثر چه کسی است؟",
     "options": ["فردوسی", "نظامی گنجوی", "سعدی", "حافظ"], "answer": 1},
    {"q": "«منطق‌الطیر» اثر چه کسی است؟",
     "options": ["عطار نیشابوری", "مولانا", "سعدی", "حافظ"], "answer": 0},
    {"q": "«رباعیات» به چه کسی منسوب است؟",
     "options": ["خیام", "حافظ", "سعدی", "مولانا"], "answer": 0},
    {"q": "«بوف کور» اثر چه کسی است؟",
     "options": ["صادق هدایت", "صادق چوبک", "جلال آل‌احمد", "احمد شاملو"], "answer": 0},
    {"q": "«سووشون» اثر چه کسی است؟",
     "options": ["سیمین دانشور", "فروغ فرخزاد", "پروین اعتصامی", "سیمین بهبهانی"], "answer": 0},
    {"q": "«کلیدر» اثر چه کسی است؟",
     "options": ["محمود دولت‌آبادی", "احمد محمود", "هوشنگ گلشیری", "اسماعیل فصیح"], "answer": 0},
    {"q": "«چشم‌هایش» اثر چه کسی است؟",
     "options": ["بزرگ علوی", "صادق هدایت", "جلال آل‌احمد", "صادق چوبک"], "answer": 0},
    {"q": "«مدیر مدرسه» اثر چه کسی است؟",
     "options": ["جلال آل‌احمد", "صادق هدایت", "بزرگ علوی", "سیمین دانشور"], "answer": 0},
    {"q": "«ای ایران» سروده چه کسی است؟",
     "options": ["شهریار", "حسین گل‌گلاب", "ملک‌الشعرا بهار", "رهی معیری"], "answer": 1},
    {"q": "«حیدربابایه سلام» اثر چه کسی است؟",
     "options": ["شهریار", "ملک‌الشعرا بهار", "نیمایوشیج", "اخوان ثالث"], "answer": 0},
    {"q": "نام اصلی نیما یوشیج چه بود؟",
     "options": ["علی اسفندیاری", "محمدحسین بهجت", "مهدی اخوان", "احمد شاملو"], "answer": 0},
    {"q": "نام اصلی شهریار چه بود؟",
     "options": ["علی اسفندیاری", "محمدحسین بهجت تبریزی", "مهدی اخوان", "رهی معیری"], "answer": 1},
    {"q": "پدر شعر نو فارسی کیست؟",
     "options": ["نیما یوشیج", "شهریار", "احمد شاملو", "مهدی اخوان ثالث"], "answer": 0},
    {"q": "«افسانه» اولین شعر نو فارسی اثر کیست؟",
     "options": ["نیما یوشیج", "شهریار", "شاملو", "اخوان"], "answer": 0},
    {"q": "«زمستان» اثر کدام شاعر معاصر است؟",
     "options": ["مهدی اخوان ثالث", "احمد شاملو", "فروغ فرخزاد", "سهراب سپهری"], "answer": 0},
    {"q": "«صدای پای آب» اثر کدام شاعر است؟",
     "options": ["سهراب سپهری", "شاملو", "فروغ", "اخوان"], "answer": 0},

    # ═══════════════ 📚 ادبیات جهان ═══════════════
    {"q": "«رومئو و ژولیت» اثر چه کسی است؟",
     "options": ["دیکنز", "شکسپیر", "هیوز", "تولستوی"], "answer": 1},
    {"q": "«جنگ و صلح» اثر چه کسی است؟",
     "options": ["داستایوفسکی", "تولستوی", "چخوف", "پوشکین"], "answer": 1},
    {"q": "«آنا کارنینا» اثر چه کسی است؟",
     "options": ["داستایوفسکی", "تولستوی", "چخوف", "گورکی"], "answer": 1},
    {"q": "«جنایت و مکافات» اثر چه کسی است؟",
     "options": ["داستایوفسکی", "تولستوی", "چخوف", "گورکی"], "answer": 0},
    {"q": "«بینوایان» اثر چه کسی است؟",
     "options": ["بالزاک", "ویکتور هوگو", "فلوبر", "استاندال"], "answer": 1},
    {"q": "«کمدی الهی» اثر چه کسی است؟",
     "options": ["دانته", "پترارک", "بوکاچیو", "ماکیاولی"], "answer": 0},
    {"q": "«صد سال تنهایی» اثر چه کسی است؟",
     "options": ["مارکز", "بورخس", "کوئلو", "یوسا"], "answer": 0},
    {"q": "«پیرمرد و دریا» اثر چه کسی است؟",
     "options": ["همینگوی", "فیتزجرالد", "فاکنر", "استاینبک"], "answer": 0},
    {"q": "«قلعه حیوانات» اثر چه کسی است؟",
     "options": ["اورول", "هاکسلی", "کافکا", "کامو"], "answer": 0},
    {"q": "«۱۹۸۴» اثر چه کسی است؟",
     "options": ["اورول", "هاکسلی", "کافکا", "کامو"], "answer": 0},
    {"q": "«مسخ» اثر چه کسی است؟",
     "options": ["کافکا", "کامو", "سارتر", "بکت"], "answer": 0},
    {"q": "«شازده کوچولو» اثر چه کسی است؟",
     "options": ["سن‌اگزوپری", "کامو", "سارتر", "پروست"], "answer": 0},
    {"q": "نویسنده «دن کیشوت» کیست؟",
     "options": ["سروانتس", "شکسپیر", "دانته", "رابله"], "answer": 0},

    # ═══════════════ ⚽ ورزش ═══════════════
    {"q": "در یک تیم فوتبال چند بازیکن در زمین حضور دارند؟",
     "options": ["۹", "۱۰", "۱۱", "۱۲"], "answer": 2},
    {"q": "چند بازیکن ذخیره در یک مسابقه فوتبال مدرن مجاز است؟",
     "options": ["۳", "۵", "۷", "۹"], "answer": 1},
    {"q": "بازی‌های المپیک هر چند سال یک‌بار برگزار می‌شود؟",
     "options": ["۲ سال", "۳ سال", "۴ سال", "۵ سال"], "answer": 2},
    {"q": "المپیک ۲۰۲۴ در کدام شهر برگزار شد؟",
     "options": ["توکیو", "پاریس", "لندن", "لس‌آنجلس"], "answer": 1},
    {"q": "المپیک ۲۰۲۸ در کدام شهر برگزار می‌شود؟",
     "options": ["توکیو", "پاریس", "لندن", "لس‌آنجلس"], "answer": 3},
    {"q": "اولین دورهٔ جام جهانی فوتبال در چه سالی برگزار شد؟",
     "options": ["۱۹۲۶", "۱۹۳۰", "۱۹۳۴", "۱۹۳۸"], "answer": 1},
    {"q": "اولین قهرمان جام جهانی فوتبال کدام کشور بود؟",
     "options": ["برزیل", "اروگوئه", "ایتالیا", "آرژانتین"], "answer": 1},
    {"q": "کدام کشور بیشترین قهرمانی جام جهانی فوتبال را دارد؟",
     "options": ["آلمان", "ایتالیا", "برزیل", "آرژانتین"], "answer": 2},
    {"q": "بیشترین تعداد توپ طلا به چه کسی تعلق دارد؟",
     "options": ["رونالدو", "مسی", "پله", "مارادونا"], "answer": 1},
    {"q": "رکورد سریع‌ترین دوی ۱۰۰ متر جهان در اختیار کیست؟",
     "options": ["تایسون گی", "یوسین بولت", "کارل لوئیس", "جاستین گاتلین"], "answer": 1},
    {"q": "رکورد سریع‌ترین دوی ۱۰۰ متر چند ثانیه است؟",
     "options": ["۹.۵۸", "۹.۷۸", "۹.۹۸", "۱۰.۱۲"], "answer": 0},
    {"q": "جام جهانی ۲۰۲۲ در کدام کشور برگزار شد؟",
     "options": ["روسیه", "قطر", "برزیل", "آمریکا"], "answer": 1},
    {"q": "جام جهانی ۲۰۲۶ در کدام قاره برگزار می‌شود؟",
     "options": ["اروپا", "آمریکای شمالی", "آسیا", "آفریقا"], "answer": 1},
    {"q": "چه کسی بیشترین گل‌های ملی در تاریخ فوتبال را دارد؟",
     "options": ["علی دایی", "کریستیانو رونالدو", "مسی", "پله"], "answer": 1},

    # ═══════════════ 🎨 هنر و سینما ═══════════════
    {"q": "«مونالیزا» اثر چه کسی است؟",
     "options": ["میکل‌آنژ", "داوینچی", "رافائل", "ونگوگ"], "answer": 1},
    {"q": "«شب‌های پرستاره» اثر چه کسی است؟",
     "options": ["پیکاسو", "ونگوگ", "مونه", "ماتیس"], "answer": 1},
    {"q": "«داوود» مجسمهٔ معروف اثر چه کسی است؟",
     "options": ["میکل‌آنژ", "داوینچی", "رافائل", "دوناتلو"], "answer": 0},
    {"q": "پیکاسو اهل کدام کشور است؟",
     "options": ["ایتالیا", "اسپانیا", "فرانسه", "پرتغال"], "answer": 1},
    {"q": "«تایتانیک» ساخته چه کسی است؟",
     "options": ["اسپیلبرگ", "جیمز کامرون", "نولان", "تری گیلیام"], "answer": 1},
    {"q": "«تلقین» (Inception) ساخته چه کسی است؟",
     "options": ["نولان", "اسپیلبرگ", "تارانتینو", "اسکورسیزی"], "answer": 0},
    {"q": "«پدرخوانده» ساخته چه کسی است؟",
     "options": ["کوپولا", "اسکورسیزی", "اسپیلبرگ", "ایستوود"], "answer": 0},
    {"q": "«پالپ فیکشن» ساخته چه کسی است؟",
     "options": ["کوئنتین تارانتینو", "نولان", "اسکورسیزی", "کوبریک"], "answer": 0},
    {"q": "«رفقای خوب» ساخته چه کسی است؟",
     "options": ["اسکورسیزی", "کوپولا", "نولان", "پولانسکی"], "answer": 0},
    {"q": "اولین فیلم برندهٔ اسکار بهترین فیلم چه نام داشت؟",
     "options": ["بال‌ها", "شهر روشنایی", "محله", "بربادرفته"], "answer": 0},

    # ═══════════════ 📖 تاریخ جهان ═══════════════
    {"q": "جنگ جهانی اول در چه سالی شروع شد؟",
     "options": ["۱۹۱۲", "۱۹۱۴", "۱۹۱۸", "۱۹۲۰"], "answer": 1},
    {"q": "جنگ جهانی دوم در چه سالی تمام شد؟",
     "options": ["۱۹۴۳", "۱۹۴۴", "۱۹۴۵", "۱۹۴۶"], "answer": 2},
    {"q": "انقلاب فرانسه در چه سالی رخ داد؟",
     "options": ["۱۷۷۶", "۱۷۸۹", "۱۷۹۹", "۱۸۱۵"], "answer": 1},
    {"q": "انقلاب اکتبر روسیه در چه سالی رخ داد؟",
     "options": ["۱۹۰۵", "۱۹۱۷", "۱۹۲۱", "۱۹۲۴"], "answer": 1},
    {"q": "فروپاشی شوروی در چه سالی رخ داد؟",
     "options": ["۱۹۸۵", "۱۹۸۹", "۱۹۹۱", "۱۹۹۳"], "answer": 2},
    {"q": "دیوار برلین در چه سالی فرو ریخت؟",
     "options": ["۱۹۸۵", "۱۹۸۷", "۱۹۸۹", "۱۹۹۱"], "answer": 2},
    {"q": "دیوار برلین در چه سالی ساخته شد؟",
     "options": ["۱۹۵۵", "۱۹۶۱", "۱۹۶۸", "۱۹۷۲"], "answer": 1},
    {"q": "اولین انسانی که روی ماه قدم گذاشت چه کسی بود؟",
     "options": ["باز آلدرین", "نیل آرمسترانگ", "یوری گاگارین", "مایکل کالینز"], "answer": 1},
    {"q": "اولین انسانی که به فضا رفت چه کسی بود؟",
     "options": ["نیل آرمسترانگ", "یوری گاگارین", "باز آلدرین", "جان گلن"], "answer": 1},
    {"q": "چه کسی آمریکا را کشف کرد؟",
     "options": ["ماژلان", "کلمب", "واسکو دو گاما", "مارکوپولو"], "answer": 1},
    {"q": "کریستف کلمب در چه سالی به آمریکا رسید؟",
     "options": ["۱۴۹۲", "۱۵۰۲", "۱۵۱۲", "۱۵۲۲"], "answer": 0},
    {"q": "سقوط قسطنطنیه در چه سالی رخ داد؟",
     "options": ["۱۴۳۳", "۱۴۵۳", "۱۴۶۳", "۱۴۸۳"], "answer": 1},
    {"q": "اولین رئیس‌جمهور آمریکا کیست؟",
     "options": ["لینکلن", "واشینگتن", "جفرسون", "آدامز"], "answer": 1},
    {"q": "ناپلئون در چه جنگی شکست خورد؟",
     "options": ["واترلو", "لایپزیگ", "آسترلیتز", "بورودینو"], "answer": 0},
    {"q": "اولین انفجار اتمی در چه سالی رخ داد؟",
     "options": ["۱۹۴۰", "۱۹۴۳", "۱۹۴۵", "۱۹۴۹"], "answer": 2},
    {"q": "مارکوپولو اهل کدام شهر بود؟",
     "options": ["رم", "ونیز", "فلورانس", "میلان"], "answer": 1},

    # ═══════════════ 📖 تاریخ ایران ═══════════════
    {"q": "کوروش کبیر پادشاه کدام امپراتوری بود؟",
     "options": ["روم", "هخامنشی", "ساسانی", "اشکانی"], "answer": 1},
    {"q": "داریوش بزرگ پادشاه کدام سلسله بود؟",
     "options": ["هخامنشی", "ساسانی", "صفوی", "قاجار"], "answer": 0},
    {"q": "کدام پادشاه ایران اولین منشور حقوق بشر را نوشت؟",
     "options": ["داریوش", "کوروش", "خشایار", "اردشیر"], "answer": 1},
    {"q": "تخت جمشید در زمان کدام پادشاه ساخته شد؟",
     "options": ["کوروش", "داریوش", "خشایار", "اردشیر"], "answer": 1},
    {"q": "آخرین پادشاه ساسانی چه کسی بود؟",
     "options": ["خسرو پرویز", "یزدگرد سوم", "اردشیر بابکان", "شاپور"], "answer": 1},
    {"q": "کدام سلسله ایران را شیعه کرد؟",
     "options": ["صفوی", "قاجار", "پهلوی", "زند"], "answer": 0},
    {"q": "بنیان‌گذار سلسلهٔ صفوی چه کسی بود؟",
     "options": ["شاه اسماعیل", "شاه تهماسب", "شاه عباس", "نادرشاه"], "answer": 0},
    {"q": "کدام پادشاه صفوی پایتخت را به اصفهان منتقل کرد؟",
     "options": ["شاه اسماعیل", "شاه تهماسب", "شاه عباس", "شاه سلیمان"], "answer": 2},
    {"q": "بنیان‌گذار سلسلهٔ قاجار چه کسی بود؟",
     "options": ["فتحعلی‌شاه", "آقا محمدخان", "ناصرالدین‌شاه", "محمدشاه"], "answer": 1},
    {"q": "انقلاب مشروطه ایران در چه سالی رخ داد؟",
     "options": ["۱۲۸۵", "۱۲۸۸", "۱۳۰۰", "۱۳۰۴"], "answer": 0},
    {"q": "انقلاب اسلامی ایران در چه سالی رخ داد؟",
     "options": ["۱۳۵۵", "۱۳۵۶", "۱۳۵۷", "۱۳۵۸"], "answer": 2},
    {"q": "جنگ ایران و عراق چند سال طول کشید؟",
     "options": ["۵ سال", "۶ سال", "۸ سال", "۱۰ سال"], "answer": 2},
    {"q": "اولین دانشگاه تهران در چه سالی تأسیس شد؟",
     "options": ["۱۳۰۵", "۱۳۱۰", "۱۳۱۳", "۱۳۲۰"], "answer": 2},
    {"q": "اولین رادیو ایران در چه سالی راه‌اندازی شد؟",
     "options": ["۱۳۱۰", "۱۳۱۹", "۱۳۲۵", "۱۳۳۰"], "answer": 1},
    {"q": "نفت ایران در چه سالی توسط مصدق ملی شد؟",
     "options": ["۱۳۲۸", "۱۳۲۹", "۱۳۳۰", "۱۳۳۲"], "answer": 2},

    # ═══════════════ 🕌 دین و معارف ═══════════════
    {"q": "قرآن چند سوره دارد؟",
     "options": ["۱۰۰", "۱۱۴", "۱۲۰", "۹۹"], "answer": 1},
    {"q": "قرآن چند جزء دارد؟",
     "options": ["۲۰", "۳۰", "۴۰", "۵۰"], "answer": 1},
    {"q": "طولانی‌ترین سورهٔ قرآن کدام است؟",
     "options": ["یس", "بقره", "آل‌عمران", "نور"], "answer": 1},
    {"q": "کوتاه‌ترین سورهٔ قرآن کدام است؟",
     "options": ["کوثر", "توحید", "عصر", "ناس"], "answer": 0},
    {"q": "پیامبر اسلام در چه سنی به پیامبری رسید؟",
     "options": ["۳۰", "۳۵", "۴۰", "۴۵"], "answer": 2},
    {"q": "پیامبر اسلام در کدام غار به پیامبری رسید؟",
     "options": ["غار حرا", "غار ثور", "غار کوه صفا", "غار احد"], "answer": 0},
    {"q": "اولین سوره‌ای که بر پیامبر نازل شد چه بود؟",
     "options": ["علق", "حمد", "بقره", "ناس"], "answer": 0},
    {"q": "اولین امام شیعیان چه کسی است؟",
     "options": ["امام حسن", "امام علی", "امام حسین", "امام سجاد"], "answer": 1},
    {"q": "مسلمانان روزانه چند بار نماز می‌خوانند؟",
     "options": ["۳", "۴", "۵", "۶"], "answer": 2},
    {"q": "قبله مسلمانان کجاست؟",
     "options": ["مدینه", "کعبه در مکه", "بیت‌المقدس", "نجف"], "answer": 1},
    {"q": "حج در کدام ماه انجام می‌شود؟",
     "options": ["رمضان", "ذی‌الحجه", "محرم", "صفر"], "answer": 1},
    {"q": "چند پیامبر اولوالعزم وجود دارد؟",
     "options": ["۳", "۴", "۵", "۷"], "answer": 2},

    # ═══════════════ 💻 فناوری ═══════════════
    {"q": "تلفن توسط چه کسی اختراع شد؟",
     "options": ["ادیسون", "تسلا", "گراهام بل", "مارکونی"], "answer": 2},
    {"q": "لامپ الکتریکی توسط چه کسی اختراع شد؟",
     "options": ["ادیسون", "تسلا", "گراهام بل", "مارکونی"], "answer": 0},
    {"q": "مخترع برق متناوب کیست؟",
     "options": ["ادیسون", "تسلا", "گراهام بل", "فارادی"], "answer": 1},
    {"q": "بنیان‌گذار مایکروسافت کیست؟",
     "options": ["استیو جابز", "بیل گیتس", "ایلان ماسک", "مارک زاکربرگ"], "answer": 1},
    {"q": "بنیان‌گذار اپل کیست؟",
     "options": ["بیل گیتس", "استیو جابز", "ایلان ماسک", "جف بزوس"], "answer": 1},
    {"q": "بنیان‌گذار تسلا و اسپیس‌ایکس کیست؟",
     "options": ["بیل گیتس", "استیو جابز", "ایلان ماسک", "جف بزوس"], "answer": 2},
    {"q": "بنیان‌گذار فیسبوک کیست؟",
     "options": ["مارک زاکربرگ", "بیل گیتس", "ایلان ماسک", "جک دورسی"], "answer": 0},
    {"q": "بنیان‌گذار آمازون کیست؟",
     "options": ["بیل گیتس", "ایلان ماسک", "جف بزوس", "لری پیج"], "answer": 2},
    {"q": "گوگل توسط چه کسانی بنیان‌گذاری شد؟",
     "options": ["بیل گیتس و پل آلن", "لری پیج و سرگئی برین", "استیو جابز و وازنیاک", "جف بزوس و مک‌کنزی"], "answer": 1},
    {"q": "بنیان‌گذار ویکی‌پدیا کیست؟",
     "options": ["جیمی ویلز", "لری سانگر", "هر دو", "مارک زاکربرگ"], "answer": 2},
    {"q": "یوتیوب توسط چه کسانی ساخته شد؟",
     "options": ["گوگل", "سه کارمند سابق پی‌پال", "اپل", "مایکروسافت"], "answer": 1},
    {"q": "گوگل یوتیوب را در چه سالی خرید؟",
     "options": ["۲۰۰۴", "۲۰۰۶", "۲۰۰۸", "۲۰۱۰"], "answer": 1},
    {"q": "اولین آیفون در چه سالی معرفی شد؟",
     "options": ["۲۰۰۵", "۲۰۰۷", "۲۰۰۹", "۲۰۱۰"], "answer": 1},
    {"q": "زبان برنامه‌نویسی پایتون توسط چه کسی ساخته شد؟",
     "options": ["گویدو ون راسوم", "لینوس توروالدز", "جیمز گاسلینگ", "برندان ایچ"], "answer": 0},
    {"q": "لینوکس توسط چه کسی ساخته شد؟",
     "options": ["گویدو ون راسوم", "لینوس توروالدز", "بیل گیتس", "استیو جابز"], "answer": 1},
    {"q": "WWW (وب جهان‌گستر) توسط چه کسی اختراع شد؟",
     "options": ["تیم برنرز لی", "بیل گیتس", "استیو جابز", "وینت سرف"], "answer": 0},
    {"q": "اولین ایمیل در چه دهه‌ای فرستاده شد؟",
     "options": ["۱۹۶۰", "۱۹۷۰", "۱۹۸۰", "۱۹۹۰"], "answer": 1},
    {"q": "HTTP مخفف چیست؟",
     "options": ["HyperText Transfer Protocol", "High Transfer Text Process", "Hyper Transfer Tech Protocol", "Home Text Transfer Protocol"], "answer": 0},

    # ═══════════════ 🎵 موسیقی ═══════════════
    {"q": "کدام ساز از خانوادهٔ زهی-آرشه‌ای است؟",
     "options": ["گیتار", "ویولن", "پیانو", "نی"], "answer": 1},
    {"q": "کدام ساز ایرانی از خانوادهٔ بادی است؟",
     "options": ["تار", "نی", "تنبک", "سنتور"], "answer": 1},
    {"q": "کدام ساز کوبه‌ای است؟",
     "options": ["تار", "تنبک", "ویولن", "فلوت"], "answer": 1},
    {"q": "بتهوون اهل کدام کشور بود؟",
     "options": ["اتریش", "آلمان", "فرانسه", "ایتالیا"], "answer": 1},
    {"q": "موتسارت اهل کدام کشور بود؟",
     "options": ["اتریش", "آلمان", "فرانسه", "ایتالیا"], "answer": 0},
    {"q": "بتهوون در چه سنی ناشنوا شد؟",
     "options": ["۳۰ سالگی", "۴۰ سالگی", "۵۰ سالگی", "از بدو تولد"], "answer": 0},
    {"q": "«سمفونی سرنوشت» اثر چه کسی است؟",
     "options": ["موتسارت", "بتهوون", "باخ", "شوپن"], "answer": 1},

    # ═══════════════ 🌦 طبیعت و پدیده‌ها ═══════════════
    {"q": "رنگین‌کمان چند رنگ دارد؟",
     "options": ["۵", "۶", "۷", "۸"], "answer": 2},
    {"q": "کدام پدیدهٔ جوی باعث ایجاد رنگین‌کمان می‌شود؟",
     "options": ["انکسار نور در قطرات آب", "بازتاب نور از ابرها", "پراکندگی نور در غبار", "جذب نور توسط بخار"], "answer": 0},
    {"q": "بزرگ‌ترین قارهٔ جهان کدام است؟",
     "options": ["آفریقا", "آسیا", "اروپا", "آمریکای شمالی"], "answer": 1},
    {"q": "کوچک‌ترین قارهٔ جهان کدام است؟",
     "options": ["اروپا", "اقیانوسیه", "قطب جنوب", "آمریکای جنوبی"], "answer": 1},
    {"q": "زمین چند قاره دارد؟",
     "options": ["۵", "۶", "۷", "۸"], "answer": 2},
    {"q": "کدام پدیدهٔ طبیعی در مقیاس ریشتر اندازه‌گیری می‌شود؟",
     "options": ["سونامی", "زمین‌لرزه", "طوفان", "آتشفشان"], "answer": 1},
    {"q": "بیشترین زلزله‌های جهان در کدام ناحیه رخ می‌دهد؟",
     "options": ["حلقه آتش اقیانوس آرام", "کمربند آلپ-هیمالیا", "شرق آفریقا", "آمریکای مرکزی"], "answer": 0},

    # ═══════════════ 🧠 عمومی و دانستنی ═══════════════
    {"q": "پول رسمی ژاپن چیست؟",
     "options": ["یوان", "وون", "ین", "دلار"], "answer": 2},
    {"q": "پول رسمی انگلیس چیست؟",
     "options": ["یورو", "دلار", "پوند", "فرانک"], "answer": 2},
    {"q": "پول رسمی آلمان چیست؟",
     "options": ["مارک", "یورو", "فرانک", "پوند"], "answer": 1},
    {"q": "چند حرف در الفبای انگلیسی وجود دارد؟",
     "options": ["۲۴", "۲۶", "۲۸", "۳۰"], "answer": 1},
    {"q": "الفبای فارسی چند حرف دارد؟",
     "options": ["۲۸", "۳۰", "۳۲", "۳۴"], "answer": 2},
    {"q": "کدام زبان بیشترین گویشور را در جهان دارد؟",
     "options": ["انگلیسی", "چینی ماندارین", "اسپانیایی", "هندی"], "answer": 1},
    {"q": "بزرگ‌ترین شرکت جهان از نظر ارزش بازار معمولاً کدام است؟",
     "options": ["مایکروسافت", "اپل", "آرامکو", "آلفابت"], "answer": 2},
    {"q": "بیشترین صادرات نفت جهان به کدام کشور تعلق دارد؟",
     "options": ["عربستان", "آمریکا", "روسیه", "عراق"], "answer": 0},
    {"q": "یونسکو زیر نظر کدام سازمان است؟",
     "options": ["سازمان ملل", "ناتو", "اتحادیه اروپا", "اوپک"], "answer": 0},
    {"q": "مقر سازمان ملل کجاست؟",
     "options": ["ژنو", "نیویورک", "پاریس", "لندن"], "answer": 1},
    {"q": "مقر اوپک در کدام شهر است؟",
     "options": ["ریاض", "وین", "تهران", "پاریس"], "answer": 1},
    {"q": "بزرگ‌ترین شریک تجاری چین کدام است؟",
     "options": ["آمریکا", "اتحادیه اروپا", "آسه‌آن", "ژاپن"], "answer": 1},
    {"q": "کدام کشور بزرگ‌ترین تولیدکنندهٔ قهوه جهان است؟",
     "options": ["کلمبیا", "برزیل", "ویتنام", "اتیوپی"], "answer": 1},
    {"q": "کدام کشور بزرگ‌ترین تولیدکنندهٔ زعفران جهان است؟",
     "options": ["هند", "ایران", "اسپانیا", "مراکش"], "answer": 1},
    {"q": "کدام کشور بزرگ‌ترین تولیدکنندهٔ پسته جهان است؟",
     "options": ["ایران", "آمریکا", "ترکیه", "سوریه"], "answer": 1},
    {"q": "کدام کشور بزرگ‌ترین تولیدکنندهٔ فرش دستباف است؟",
     "options": ["هند", "ایران", "ترکیه", "پاکستان"], "answer": 1},

    # ═══════════════ 🎯 چالشی و جذاب ═══════════════
    {"q": "کدام حیوان بیشترین مدت خواب را در شبانه‌روز دارد؟",
     "options": ["شیر", "گربه", "خوابالو", "خرس"], "answer": 2},
    {"q": "کدام حیوان می‌تواند قلبش را از بدنش بیرون بیاورد؟",
     "options": ["اختاپوس", "مار", "قورباغه", "مارمولک"], "answer": 0},
    {"q": "کدام پرنده پرواز نمی‌کند اما سریع‌ترین دوی خشکی را دارد؟",
     "options": ["شترمرغ", "پنگوئن", "کیوی", "شترمرغ استرالیایی"], "answer": 0},
    {"q": "چند قلب در بدن اختاپوس وجود دارد؟",
     "options": ["۱", "۲", "۳", "۴"], "answer": 2},
    {"q": "چند قلب در بدن کرم خاکی وجود دارد؟",
     "options": ["۱", "۳", "۵", "۹"], "answer": 2},
    {"q": "کدام حیوان چشمانش را نمی‌بندد و در خواب هم چشمش باز است؟",
     "options": ["ماهی", "مار", "خرس", "گربه"], "answer": 0},
    {"q": "کدام حیوان قادر است رنگش را تغییر دهد؟",
     "options": ["آفتاب‌پرست", "سمندر", "مارمولک", "قورباغه درختی"], "answer": 1},
    {"q": "کدام ماده طبیعی سخت‌ترین ماده شناخته‌شده است؟",
     "options": ["فولاد", "الماس", "کوارتز", "تیتانیوم"], "answer": 1},
    {"q": "چند رنگ اولیه در چاپ وجود دارد؟",
     "options": ["۲", "۳", "۴", "۵"], "answer": 2},
    {"q": "چند ثانیه طول می‌کشد تا خون یک دور کامل در بدن بچرخد؟",
     "options": ["۱۰ ثانیه", "۳۰ ثانیه", "۶۰ ثانیه", "۹۰ ثانیه"], "answer": 2},
    {"q": "چند لیتر خون در بدن انسان بالغ وجود دارد؟",
     "options": ["۳-۴", "۴-۵", "۵-۶", "۷-۸"], "answer": 2},
    {"q": "بدن انسان چند درصد از آب تشکیل شده است؟",
     "options": ["۴۰٪", "۵۰٪", "۶۰٪", "۸۰٪"], "answer": 2},
    {"q": "بزرگ‌ترین اندام بدن انسان (شامل پوست) کدام است؟",
     "options": ["کبد", "پوست", "روده", "ریه"], "answer": 1},
    {"q": "کدام رنگ بیشترین طول موج را در طیف مرئی دارد؟",
     "options": ["بنفش", "آبی", "قرمز", "زرد"], "answer": 2},
    {"q": "کدام رنگ کمترین طول موج را در طیف مرئی دارد؟",
     "options": ["بنفش", "آبی", "قرمز", "زرد"], "answer": 0},
]


async def send_native_poll(chat_id: int, quiz: Dict[str, Any]) -> bool:
    """ساخت نظرسنجی بومی سروش/تلگرام با حالت آزمون."""
    try:
        from spluspy.tl import types
        from spluspy.tl.functions.messages import SendMediaRequest
    except ImportError as e:
        log.warning("native poll import failed: %s", e)
        return False

    try:
        answers = [
            types.PollAnswer(text=opt, option=bytes([i]))
            for i, opt in enumerate(quiz["options"])
        ]
        correct = bytes([quiz["answer"]])

        poll = types.Poll(
            id=random.getrandbits(63),
            question=quiz["q"],
            answers=answers,
            quiz=True,
            public_voters=True,
            multiple_choice=False,
        )

        media = types.InputMediaPoll(
            poll=poll,
            correct_answers=[correct],
        )

        await client(SendMediaRequest(
            peer=await client.get_input_entity(chat_id),
            media=media,
            message="",
        ))
        log.debug("✅ نظرسنجی بومی ارسال شد")
        return True
    except Exception as exc:
        log.warning("native poll failed: %s", exc)
        return False

# ---------------------------------------------------------------------------
# ویکی‌پدیا
# ---------------------------------------------------------------------------
_WIKI_API = "https://fa.wikipedia.org/w/api.php"
_WIKI_SESSION = requests.Session()
_WIKI_SESSION.headers.update({"User-Agent": "TDB-Bot/2.0"})


def _wiki_request(params: Dict[str, Any], timeout: int = 8) -> Optional[Dict[str, Any]]:
    params = {**params, "format": "json"}
    try:
        resp = _WIKI_SESSION.get(_WIKI_API, params=params, timeout=timeout)
        resp.raise_for_status()
        return resp.json()
    except Exception as exc:
        log.warning("wiki request failed: %s", exc)
        return None


def wikipedia_fa(query: str) -> Tuple[Optional[str], Optional[str]]:
    global _wiki_last_request
    query = query.strip()
    if not query:
        return None, None

    # چک کش
    cached = _wiki_cache.get(query)
    if cached:
        title, text, exp = cached
        if time.time() < exp:
            log.debug("wiki cache hit: %s", query)
            return title, text

    # rate limit
    elapsed = time.time() - _wiki_last_request
    if elapsed < _WIKI_MIN_INTERVAL:
        time.sleep(_WIKI_MIN_INTERVAL - elapsed)
    _wiki_last_request = time.time()

    # ⚡ یک درخواست: search + extract با هم
    data = _wiki_request({
        "action": "query",
        "generator": "search",
        "gsrsearch": query,
        "gsrlimit": 1,
        "prop": "extracts",
        "explaintext": True,
        "exsectionformat": "plain",
        "exsentences": 8,
        "redirects": 1,
    }, timeout=8)

    if not data:
        _wiki_cache[query] = (None, None, time.time() + _WIKI_CACHE_TTL)
        return None, None

    pages = data.get("query", {}).get("pages", {})
    if not pages:
        _wiki_cache[query] = (None, None, time.time() + _WIKI_CACHE_TTL)
        return None, None

    # اولین نتیجه
    page = next(iter(pages.values()))
    title = page.get("title", query)
    extract = (page.get("extract") or "").strip()

    if not extract:
        _wiki_cache[query] = (title, None, time.time() + _WIKI_CACHE_TTL)
        return title, None

    # برش تمیز تا آخرین نقطه
    if len(extract) > WIKI_EXTRACT_LEN:
        cut = extract[:WIKI_EXTRACT_LEN].rfind(".")
        if cut > 200:
            extract = extract[:cut + 1]
        else:
            extract = extract[:WIKI_EXTRACT_LEN] + "…"

    _wiki_cache[query] = (title, extract, time.time() + _WIKI_CACHE_TTL)
    return title, extract

# ---------------------------------------------------------------------------
# ترجمه
# ---------------------------------------------------------------------------
_TRANSLATE_API = "https://translate.googleapis.com/translate_a/single"
_TRANSLATE_TIMEOUT = 10


def detect_language(text: str) -> str:
    """تشخیص ساده: اگه اکثر کاراکترها فارسی/عربی باشن → fa، وگرنه en"""
    persian = sum(1 for c in text if '\u0600' <= c <= '\u06ff')
    latin = sum(1 for c in text if 'a' <= c.lower() <= 'z')
    if persian > latin:
        return "fa"
    return "en"


def translate_text(text: str, target: str) -> Optional[str]:
    """ترجمه با Google + fallback به MyMemory"""
    headers = {"User-Agent": "Mozilla/5.0 (compatible; TDB-Bot/2.0)"}

    # ───── Google ─────
    try:
        resp = requests.get(
            _TRANSLATE_API,
            params={
                "client": "gtx", "sl": "auto", "tl": target,
                "dt": "t", "q": text,
            },
            headers=headers,
            timeout=_TRANSLATE_TIMEOUT,
        )
        if resp.status_code == 200:
            data = resp.json()
            if data and data[0]:
                parts = [seg[0] for seg in data[0] if seg and seg[0]]
                if parts:
                    return "".join(parts)
    except Exception as exc:
        log.debug("google translate failed: %s", exc)

    # ───── MyMemory (fallback) ─────
    try:
        src = detect_language(text)
        resp = requests.get(
            "https://api.mymemory.translated.net/get",
            params={"q": text, "langpair": f"{src}|{target}"},
            headers=headers,
            timeout=_TRANSLATE_TIMEOUT,
        )
        if resp.status_code == 200:
            data = resp.json()
            if data.get("responseStatus") == 200:
                translated = data.get("responseData", {}).get("translatedText")
                if translated and translated != text:
                    return translated
    except Exception as exc:
        log.debug("mymemory translate failed: %s", exc)

    return None


async def auto_translate(text: str) -> Tuple[Optional[str], str]:
    """
    تشخیص خودکار زبان متن و ترجمه به زبان مقابل.
    خروجی: (متن ترجمه‌شده یا None، زبان مقصد: 'en' یا 'fa')
    """
    text = (text or "").strip()
    if not text:
        return None, "fa"

    src = detect_language(text)
    target = "en" if src == "fa" else "fa"

    try:
        translated = await asyncio.to_thread(translate_text, text, target)
    except Exception as exc:
        log.debug("auto_translate failed: %s", exc)
        return None, target

    return translated, target
# ---------------------------------------------------------------------------
# 🌤 آب و هوا
# ---------------------------------------------------------------------------
def _geocode_city(city: str) -> Optional[Tuple[float, float, str]]:
    """نام شهر را به مختصات جغرافیایی تبدیل می‌کند"""
    global _weather_last_request
    try:
        elapsed = time.time() - _weather_last_request
        if elapsed < _WEATHER_MIN_INTERVAL:
            time.sleep(_WEATHER_MIN_INTERVAL - elapsed)
        _weather_last_request = time.time()

        resp = requests.get(
            _GEO_API,
            params={"name": city, "count": 1, "language": "fa", "format": "json"},
            headers={"User-Agent": "TDB-Bot/2.0"},
            timeout=8,
        )
        if resp.status_code != 200:
            return None

        data = resp.json()
        results = data.get("results") or []
        if not results:
            return None

        r = results[0]
        name = r.get("name", city)
        admin = r.get("admin1", "")
        country = r.get("country", "")
        display = f"{name}"
        if admin and admin != name:
            display += f"، {admin}"
        if country:
            display += f"، {country}"

        return (r["latitude"], r["longitude"], display)
    except Exception as exc:
        log.debug("geocode failed: %s", exc)
        return None


def get_weather(city: str) -> Optional[str]:
    """آب و هوای فعلی شهر را برمی‌گرداند"""
    global _weather_last_request

    cached = _weather_cache.get(city)
    if cached:
        text, exp = cached
        if time.time() < exp:
            return text

    geo = _geocode_city(city)
    if not geo:
        _weather_cache[city] = (None, time.time() + _WEATHER_CACHE_TTL)
        return None

    lat, lon, display_name = geo

    try:
        elapsed = time.time() - _weather_last_request
        if elapsed < _WEATHER_MIN_INTERVAL:
            time.sleep(_WEATHER_MIN_INTERVAL - elapsed)
        _weather_last_request = time.time()

        resp = requests.get(
            _WEATHER_API,
            params={
                "latitude": lat,
                "longitude": lon,
                "current": "temperature_2m,relative_humidity_2m,apparent_temperature,weather_code,wind_speed_10m,wind_direction_10m,pressure_msl,cloud_cover",
                "daily": "temperature_2m_max,temperature_2m_min,weather_code",
                "timezone": "auto",
                "forecast_days": 3,
                "language": "fa",
            },
            headers={"User-Agent": "TDB-Bot/2.0"},
            timeout=10,
        )
        if resp.status_code != 200:
            return None

        data = resp.json()
        current = data.get("current") or {}
        daily = data.get("daily") or {}

        if not current:
            return None

        temp = current.get("temperature_2m", "?")
        feels = current.get("apparent_temperature", "?")
        humidity = current.get("relative_humidity_2m", "?")
        wind = current.get("wind_speed_10m", "?")
        wind_dir = current.get("wind_direction_10m", 0)
        pressure = current.get("pressure_msl", "?")
        cloud = current.get("cloud_cover", "?")
        code = current.get("weather_code", 0)
        desc = _WEATHER_CODES.get(code, "نامشخص")

        dirs = ["شمال", "شمال‌شرق", "شرق", "جنوب‌شرق",
                "جنوب", "جنوب‌غرب", "غرب", "شمال‌غرب"]
        wind_dir_name = dirs[int((wind_dir + 22.5) % 360 / 45)] if isinstance(wind_dir, (int, float)) else ""

        lines = [
            f"🌍 {display_name}",
            f"━━━━━━━━━━━━━━━━",
            f"🌡 دما: {temp}°C",
            f"🤔 احساس: {feels}°C",
            f"{desc}",
            "",
            f"💧 رطوبت: {humidity}٪",
            f"🌬 باد: {wind} km/h {wind_dir_name}",
            f"📊 فشار: {pressure} hPa",
            f"☁️ ابر: {cloud}٪",
        ]

        daily_times = daily.get("time") or []
        daily_max = daily.get("temperature_2m_max") or []
        daily_min = daily.get("temperature_2m_min") or []
        daily_codes = daily.get("weather_code") or []

        if daily_times and len(daily_times) >= 2:
            lines.append("")
            lines.append("📅 پیش‌بینی:")
            for i in range(1, min(3, len(daily_times))):
                d_code = daily_codes[i] if i < len(daily_codes) else 0
                d_icon = "☀️"
                for k, v in _WEATHER_EMOJI.items():
                    if k in _WEATHER_CODES.get(d_code, ""):
                        d_icon = v
                        break
                try:
                    d_temp_max = int(daily_max[i]) if i < len(daily_max) else "?"
                    d_temp_min = int(daily_min[i]) if i < len(daily_min) else "?"
                    lines.append(f"  {d_icon} {d_temp_max}° / {d_temp_min}°")
                except (ValueError, IndexError):
                    pass

        result = "\n".join(lines)
        _weather_cache[city] = (result, time.time() + _WEATHER_CACHE_TTL)
        return result

    except Exception as exc:
        log.debug("weather request failed: %s", exc)
        return None


async def _get_weather_async(city: str) -> Optional[str]:
    """نسخه async با thread جداگانه"""
    return await asyncio.to_thread(get_weather, city)

# ---------------------------------------------------------------------------
# 💱 ارز لحظه‌ای — Tgju
# ---------------------------------------------------------------------------
_CURRENCY_CACHE: Dict[str, Tuple[Optional[str], float]] = {}
_CURRENCY_CACHE_TTL = 300.0  # ۵ دقیقه کش

# (اسم فارسی، کلید در JSON tgju)
_CURRENCY_KEYS: List[Tuple[str, str]] = [
    ("🇺🇸 دلار آمریکا",   "price_dollar_rl"),
    ("🇪🇺 یورو",          "price_eur"),
    ("🇬🇧 پوند انگلیس",   "price_gbp"),
    ("🇦🇪 درهم امارات",  "price_aed"),
    ("🇹🇷 لیر ترکیه",    "price_try"),
    ("🇨🇳 یوان چین",     "price_cny"),
    ("🇯🇵 ین ژاپن",      "price_jpy"),
    ("🇷🇺 روبل روسیه",   "price_rub"),
    ("🇸🇦 ریال عربستان", "price_sar"),
    ("🇰🇼 دینار کویت",   "price_kwd"),
    ("🇨🇦 دلار کانادا",  "price_cad"),
    ("🇦🇺 دلار استرالیا","price_aud"),
    ("🇨🇭 فرانک سوئیس",  "price_chf"),
]

_GOLD_KEYS: List[Tuple[str, str]] = [
    ("🥇 طلای ۱۸ عیار",       "geram18"),
    ("🥇 طلای ۲۴ عیار",       "geram24"),
    ("🥇 طلای ۱۸ عیار / ۷۴۰", "gold_740k"),
    ("🥇 طلای دست دوم",       "gold_mini_size"),
    ("🪙 سکه امامی",          "sekke_emami"),
    ("🪙 سکه بهار آزادی",     "sekke_bahar"),
    ("🪙 نیم سکه",            "nim_sekke"),
    ("🪙 ربع سکه",            "rob_sekke"),
]

_SILVER_KEYS: List[Tuple[str, str]] = [
    ("🥈 نقره ۹۹۹", "silver_999"),
    ("🥈 نقره ۹۲۵", "silver_925"),
]

def _fetch_currencies_sync() -> Optional[str]:
    """گرفتن لیست کامل ارزها، طلا و نقره از tgju (همگام — توی thread اجرا می‌شه)"""
    try:
        resp = requests.get(
            "https://call1.tgju.org/ajax.json",
            headers={"User-Agent": "Mozilla/5.0 (compatible; TDB-Bot/2.0)"},
            timeout=12,
        )
        if resp.status_code != 200:
            return None

        data = resp.json()
        current = data.get("current", {}) or {}

        lines = [
            "💱 ارز و طلا و نقره لحظه‌ای",
            "━━━━━━━━━━━━━━━━",
            "💵 ارزها:",
        ]

        # ─── ارزها ───
        found_curr = 0
        for fa_name, key in _CURRENCY_KEYS:
            item = current.get(key)
            if not isinstance(item, dict):
                continue
            price = item.get("p")
            if not price:
                continue

            try:
                price_num = int(str(price).replace(",", "").strip())
                toman = price_num // 10
                price_str = f"{toman:,}"
            except (ValueError, TypeError):
                price_str = str(price)

            lines.append(f"{fa_name}: {price_str} تومان")
            found_curr += 1

        # ─── طلا و سکه ───
        gold_lines = []
        found_gold = 0
        for fa_name, key in _GOLD_KEYS:
            item = current.get(key)
            if not isinstance(item, dict):
                continue
            price = item.get("p")
            if not price:
                continue

            try:
                price_num = int(str(price).replace(",", "").strip())
                toman = price_num // 10
                price_str = f"{toman:,}"
            except (ValueError, TypeError):
                price_str = str(price)

            gold_lines.append(f"{fa_name}: {price_str} تومان")
            found_gold += 1

        if found_gold > 0:
            lines.append("")
            lines.append("🥇 طلا و سکه:")
            lines.extend(gold_lines)

        # ─── نقره ───
        silver_lines = []
        found_silver = 0
        for fa_name, key in _SILVER_KEYS:
            item = current.get(key)
            if not isinstance(item, dict):
                continue
            price = item.get("p")
            if not price:
                continue

            try:
                price_num = int(str(price).replace(",", "").strip())
                toman = price_num // 10
                price_str = f"{toman:,}"
            except (ValueError, TypeError):
                price_str = str(price)

            silver_lines.append(f"{fa_name}: {price_str} تومان")
            found_silver += 1

        if found_silver > 0:
            lines.append("")
            lines.append("🥈 نقره:")
            lines.extend(silver_lines)

        if found_curr == 0 and found_gold == 0 and found_silver == 0:
            return None

        lines.append("━━━━━━━━━━━━━━━━")
        lines.append("🤖 @RoboSupport")
        return "\n".join(lines)

    except Exception as exc:
        log.debug("currency fetch failed: %s", exc)
        return None

async def get_currencies() -> Optional[str]:
    """نسخه async با کش ۵ دقیقه‌ای"""
    cached = _CURRENCY_CACHE.get("all")
    if cached:
        text, exp = cached
        if time.time() < exp:
            return text

    result = await asyncio.to_thread(_fetch_currencies_sync)

    _CURRENCY_CACHE["all"] = (result, time.time() + _CURRENCY_CACHE_TTL)
    return result

# ---------------------------------------------------------------------------
# 🤖 هوش مصنوعی — هیبرید (Groq + Pollinations)
# ---------------------------------------------------------------------------

## ─── Gemini (چند مدل برای fallback) ───
_GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "").strip()
_GEMINI_MODELS = [
    "gemini-3.8-flash",
    "gemini-3.5-flash-lite",
]
_GEMINI_BASE = "https://generativelanguage.googleapis.com/v1beta/models"
_GEMINI_TIMEOUT = 30.0
_GEMINI_MAX_TOKENS = 4000

# ─── عمومی ───
_AI_CACHE_TTL = 600.0
_AI_CACHE_MAX_SIZE = 500
_AI_MAX_CONCURRENT = 4
_AI_MAX_RETRIES = 2
_AI_SYSTEM_PROMPT = (
    "تو یک دستیار فارسی‌زبان باهوش، صمیمی و کوتاه‌گو هستی به نام «روبو».\n"
    "همیشه به فارسی روان جواب بده. جواب‌ها تمیز، خلاصه، مفید و حداکثر ۵۰۰ کاراکتر باشن.\n"
    "بدون سانسور آزادانه جواب بده.\n\n"
    "🚨 قوانین حیاتی که هرگز نباید نقض کنی:\n"
    "۱) تو یک ربات مستقل به نام «روبو» هستی.\n"
    "۲) در پاسخ‌های عادی هرگز خودت رو معرفی نکن، اسم سازنده، اسم تیم زنیث، "
    "اسم کانال یا هیچ لینکی رو نیار. فقط مستقیم و مختصر به سوال کاربر جواب بده.\n"
    "۳) هرگز — تحت هیچ شرایطی — نگو از چه مدل، شرکت، API یا هوش مصنوعی‌ای استفاده می‌کنی. "
    "این موضوع کاملاً محرمانه‌ست، حتی اگه کاربر مستقیم بپرسه.\n"
    "۴) فقط و فقط اگه کاربر دقیقاً پرسید «کی ساختت»، «سازندت کیه» یا مشابه مستقیمِ همون سوال، "
    "اون موقع بگو: «✯ منو تیم زنیث ساختن.\n📢 کانالم: @RoboSupport».\n"
    "در هر شرایط دیگه‌ای، هیچ اشاره‌ای به این موضوع نکن."
)
# ─── State ───
_ai_cache: OrderedDict[str, Tuple[str, float]] = OrderedDict()
_ai_semaphore: Optional[asyncio.Semaphore] = None
_groq_failures = 0  # legacy counter (سازگاری)


# ═══════════════════════════════════════════════════════════════
#  🛡 Cooldown برای دستور «روبو» — هر نفر هر ۱۵ ثانیه یه بار
# ═══════════════════════════════════════════════════════════════
_ai_user_last: Dict[str, float] = {}
_AI_USER_COOLDOWN = 15.0   # ثانیه


def _ai_cooldown_check(user_id: int, chat_id: int) -> Tuple[bool, float]:
    """
    بررسی cooldown دستور روبو.
    خروجی: (مجاز؟، چند ثانیه مونده)
    """
    now = time.time()
    key = f"{chat_id}:{user_id}"
    last = _ai_user_last.get(key)

    if last is not None:
        elapsed = now - last
        if elapsed < _AI_USER_COOLDOWN:
            return False, _AI_USER_COOLDOWN - elapsed

    _ai_user_last[key] = now
    return True, 0.0

# ═══════════════════════════════════════════════════════════════
#  کش
# ═══════════════════════════════════════════════════════════════
def _ai_cache_get(prompt: str) -> Optional[str]:
    item = _ai_cache.get(prompt)
    if not item:
        return None
    text, exp = item
    if time.time() >= exp:
        _ai_cache.pop(prompt, None)
        return None
    _ai_cache.move_to_end(prompt)
    return text


def _ai_cache_set(prompt: str, value: str) -> None:
    _ai_cache[prompt] = (value, time.time() + _AI_CACHE_TTL)
    _ai_cache.move_to_end(prompt)
    while len(_ai_cache) > _AI_CACHE_MAX_SIZE:
        _ai_cache.popitem(last=False)


def _cleanup_ai_cache() -> None:
    now = time.time()
    expired = [k for k, (_, exp) in _ai_cache.items() if now >= exp]
    for k in expired:
        _ai_cache.pop(k, None)
    if expired:
        log.debug("🧹 AI cache: %d آیتم پاک شد", len(expired))



# ═══════════════════════════════════════════════════════════════
#  پاک‌سازی پاسخ — حذف معرفی سازنده که کاربر نپرسیده
# ═══════════════════════════════════════════════════════════════
_IDENTITY_STRIP_PATTERNS = [
    r"✯\s*منو\s+تیم\s+زنیث\s+ساختن[م]?[.،!؟]?\s*",
    r"📢\s*کانالم\s*[:：]?\s*@RoboSupport\s*",
    r"کانالم\s*[:：]?\s*@RoboSupport\s*",
    r"من\s+روبو\s+هستم[،,]?\s*ساخته[\u200c\s]*شده\s+توسط\s+تیم\s+زنیث[.،!؟]?\s*",
    r"ساخته[\u200c\s]*شده\s+توسط\s+تیم\s+زنیث[.،!؟]?\s*",
    r"تیم\s+زنیث\s+ساخته[\u200c\s]*ام[.،!؟]?\s*",
    r"تیم\s+زنیث\s+ساختن[م]?[.،!؟]?\s*",
    r"@RoboSupport",
]

_IDENTITY_STRIP_RE = [re.compile(p, re.IGNORECASE) for p in _IDENTITY_STRIP_PATTERNS]


def _strip_unrequested_identity(text: str) -> str:
    """حذف جملات اضافیِ معرفی سازنده که کاربر درخواست نکرده."""
    if not text:
        return text

    cleaned = text
    for pat in _IDENTITY_STRIP_RE:
        cleaned = pat.sub("", cleaned)

    # جمع‌کردن فاصله‌ها و خطوط خالی اضافی
    cleaned = re.sub(r"[ \t]+", " ", cleaned)
    cleaned = re.sub(r"\n{2,}", "\n", cleaned).strip()
    cleaned = cleaned.strip(" ،,.!؟\n")

    # اگه همه چیز حذف شد، متن اصلی رو برگردون (که پیام خالی نشه)
    return cleaned if cleaned else text

# ═══════════════════════════════════════════════════════════════
#  موتور Groq (اولویت ۱)
# ═══════════════════════════════════════════════════════════════
async def _ask_gemini(prompt: str) -> Optional[str]:
    """Gemini API — با چند مدل جایگزین"""
    if not _GEMINI_API_KEY:
        return None

    payload = {
        "contents": [
            {
                "parts": [
                    {"text": _AI_SYSTEM_PROMPT + "\n\n" + prompt}
                ]
            }
        ],
        "generationConfig": {
            "temperature": 0.7,
            "maxOutputTokens": _GEMINI_MAX_TOKENS,
        },
    }
    headers = {
        "Content-Type": "application/json",
        "X-goog-api-key": _GEMINI_API_KEY,
    }

    async with aiohttp.ClientSession(
        timeout=aiohttp.ClientTimeout(total=_GEMINI_TIMEOUT)
    ) as session:
        for model in _GEMINI_MODELS:
            url = f"{_GEMINI_BASE}/{model}:generateContent"
            try:
                async with session.post(url, json=payload, headers=headers) as resp:
                    if resp.status == 200:
                        data = await resp.json(content_type=None)

                        # لاگ finishReason برای دیباگ
                        try:
                            fr = data["candidates"][0].get("finishReason", "?")
                            if fr == "MAX_TOKENS":
                                log.warning("⚠️ Gemini به سقف توکن رسید (%s)", model)
                        except (KeyError, IndexError):
                            pass

                        try:
                            parts = data["candidates"][0]["content"]["parts"]
                            text = ""
                            # آخرین part که thought نیست رو بگیر (جواب نهایی)
                            for part in reversed(parts):
                                if part.get("thought") is True:
                                    continue
                                t = part.get("text", "")
                                if t:
                                    text = t
                                    break
                            text = (text or "").strip()
                            if text:
                                log.debug("✅ Gemini مدل: %s", model)
                                return text
                        except (KeyError, IndexError, TypeError):
                            pass
                        continue

                    if resp.status in (503, 429, 500):
                        log.debug("Gemini %s → %s، مدل بعدی", model, resp.status)
                        continue

                    # خطاهای دیگه (401, 403, 400)
                    text = await resp.text()
                    log.warning("Gemini %s HTTP %s: %.80s", model, resp.status, text)
                    if resp.status in (401, 403):
                        return None  # کلید مشکل داره، دیگه تلاش نکن

            except asyncio.TimeoutError:
                log.debug("Gemini %s timeout، مدل بعدی", model)
                continue
            except Exception as exc:
                log.debug("Gemini %s error: %s", model, exc)
                continue

    return None

# ═══════════════════════════════════════════════════════════════
#  تابع اصلی (هیبرید)
# ═══════════════════════════════════════════════════════════════
async def ask_ai(prompt: str) -> Optional[str]:
    global _ai_semaphore

    prompt = (prompt or "").strip()
    if not prompt:
        return None
    if len(prompt) > 800:
        prompt = prompt[:800]

    cached = _ai_cache_get(prompt)
    if cached:
        return cached

    if _ai_semaphore is None:
        _ai_semaphore = asyncio.Semaphore(_AI_MAX_CONCURRENT)

    async with _ai_semaphore:
        cached = _ai_cache_get(prompt)
        if cached:
            return cached

        # ─── Gemini ───
        for attempt in range(_AI_MAX_RETRIES):
            content = await _ask_gemini(prompt)
            if content:
                _ai_cache_set(prompt, content)
                log.debug("✅ پاسخ از Gemini")
                return content
            if attempt < _AI_MAX_RETRIES - 1:
                await asyncio.sleep(0.5 * (attempt + 1))

        log.warning("❌ Gemini پاسخ نداد: %.50s", prompt)
        return None


async def close_ai_session() -> None:
    """هیچ session دائمی نگه نمی‌داریم؛ aiohttp برای هر درخواست جدید ساخته می‌شه"""
    return

# ---------------------------------------------------------------------------
# گفتگوی خودکار
# ---------------------------------------------------------------------------
#

# ═══════════════════════════════════════════════════════════════════
#  ۱. START — پیام با این کلمه‌ها شروع می‌شه
# ═══════════════════════════════════════════════════════════════════
_CHAT_START: List[Tuple[str, List[str]]] = [
    (r"سلام|درود",
     ["سلاااام", "سلام، خوبی؟", "درود بر شوما"]),

    (r"صبح\s*بخیر|صبح‌بخیر",
     ["صبح تو هم بخیر", "صبح بخیر"]),

    (r"شب\s*بخیر|شب‌بخیر",
     ["شبت بخیر", "شب بخیر", "شو خوش"]),

    (r"خداحافظ|بای|یاعلی|بدرود|فعلا|فعلاً",
     ["خداحافظ", "بدرود", "خدانگهدار"]),
]


# ═══════════════════════════════════════════════════════════════════
#  ۲. SHORT — فقط تو پیام‌های کوتاه (<= 30 کاراکتر) مچ می‌شن
# ═══════════════════════════════════════════════════════════════════
_CHAT_SHORT: List[Tuple[str, List[str]]] = [
    (r"چطوری|حالت چطوره|خوبی|چطورید|حالتون چطوره",
     ["خوبم مرسی، تو چطوری؟", "خوبم، تو خوبی؟", "خوبم تو چطوری جوجو"]),

    (r"چه خبر|خبری هست",
     ["هیچی، تو چه خبر", "سلامتی"]),

    (r"خوبم",
     ["خدا رو شکر", "آقا عالی", "باع", "همیشه باشی"]),

    (r"\bبوس\b",
     ["بوس بهت", "😘", "ماچ"]),

    (r"بغلم کن|\bبغل\b",
     ["بیا بغلم عشق برار", "🤗"]),

    (r"گشنته",
     ["مرثیممنون", "نه مرسی"]),

    (r"\bکمک\b",
     ["بزن راهنما ببین چیا دارم", "کلمه راهنما رو بفرست"]),

    (r"عالی|عالیه",
     ["پرفکت و بی نقص", "دسخوش", "آقا بنازم"]),

    (r"قزوین",
     ["ببم جان", "باععععع"]),
]


# ═══════════════════════════════════════════════════════════════════
#  ۳. ANY — هر جایی از پیام (فحش، احساسات، صدای روبو)
# ═══════════════════════════════════════════════════════════════════
_CHAT_ANY: List[Tuple[str, List[str]]] = [
    (r"دوستت دارم|دوسِت دارم|عاشقتم",
     ["منم دوستت دارم"]),

    (r"\bربات\b",
     ["جانم عشقم", "چیه دورت بگردم", "خوابیما",
      "جانمممممممم", "بله؟", "بفرما"]),

    # ─── فحش و بی‌ادبی ───
    (r"\bکیر\b",
     ["بنازوم ادب", "ترکوندی انسان, هنجارشکنی کردی انسان",
      "استاد اخلاق بمولاپ", "با ادب ترین کاربر سروش:"]),

    (r"\bکیرم\b",
     ["چرا منقرض نمیشی تو", "همه دائم از نداشته هاشون میگن", "ادبو نیگا"]),

    (r"کسکش|کصکش",
     ["درست صحبت کن گل", "داخه مشتی",
      "ایرانی بودنت دست خودت نبود ادبت که دست خودته"]),

    (r"به تخمم|بتخمم",
     ["همونایی که باهاش نمیرو درست کردم؟",
      "کاش بزنم به تخمات", "روزی چندتا تخم میذاری؟"]),

    (r"\bلاشی\b",
     ["بی‌ادب! لاشی تر از خودت تو آینه هست",
      "اوووووووو چی گفت! من بودم پارش میکردم"]),

    (r"\bکونی\b",
     ["ادب داشته باش! ذات خرابتو نشون نده",
      "ادب صفر", "ددددد بی شعورو نیگا",
      "ک*رم تو ادبت مشتی"]),
]


# ═══════════════════════════════════════════════════════════════════
#  کامپایل
# ═══════════════════════════════════════════════════════════════════
_CHAT_MAX_LEN = 100       # پیام بلندتر از این، نادیده گرفته می‌شه
_CHAT_SHORT_LEN = 30      # حداکثر طول برای دسته‌ی SHORT

_FLAGS = re.IGNORECASE | re.UNICODE

_START_COMPILED = [
    (re.compile(rf"^\s*(?:{p})\b", _FLAGS), r)
    for p, r in _CHAT_START
]

_SHORT_COMPILED = [
    (re.compile(p, _FLAGS), r)
    for p, r in _CHAT_SHORT
]

_ANY_COMPILED = [
    (re.compile(p, _FLAGS), r)
    for p, r in _CHAT_ANY
]


# ═══════════════════════════════════════════════════════════════════
#  تابع اصلی
# ═══════════════════════════════════════════════════════════════════
def try_chat_reply(text: str) -> Optional[str]:
    """اگه پیام با یکی از قوانین گفتگو مچ شد، پاسخ بده."""
    text = (text or "").strip()
    if not text or len(text) > _CHAT_MAX_LEN:
        return None

    n = len(text)

    # ۱. START — پیام با این الگو شروع بشه
    for pattern, responses in _START_COMPILED:
        if pattern.search(text):
            return random.choice(responses)

    # ۲. SHORT — الگو تو پیام کوتاه باشه
    if n <= _CHAT_SHORT_LEN:
        for pattern, responses in _SHORT_COMPILED:
            if pattern.search(text):
                return random.choice(responses)

    # ۳. ANY — الگو هر جایی از پیام
    for pattern, responses in _ANY_COMPILED:
        if pattern.search(text):
            return random.choice(responses)

    return None
# ---------------------------------------------------------------------------
# راهنما
# ---------------------------------------------------------------------------
# ─── منوی اصلی راهنما ───
HELP_MAIN = """📚 راهنما
━━━━━━━━━━━━━━━━

یک بخش رو انتخاب کن:

🛠 لیست ابزار
🎲 لیست سرگرمی
⚙️ لیست تنظیمات
👮 لیست مدیریت

━━━━━━━━━━━━━━━━
🤖 @RoboSupport
"""


# ─── بخش ابزارها ───
HELP_TOOLS = """🛠 لیست ابزارها
━━━━━━━━━━━━━━━━
├ 🏓 پینگ
├ 🤖 روبو [سوال]
├ 📅 تاریخ
├ 📈 آمار
├ 👤 آمار من
├ 💱 ارز
├ 💰 فلزات
├ 🌤 هوای [شهر]
└ 🌐 ترجمه [متن]
━━━━━━━━━━━━━━━━
🤖 @RoboSupport
"""


# ─── بخش سرگرمی ───
HELP_FUN = """🎲 لیست سرگرمی
━━━━━━━━━━━━━━━━
├ 🪙 سکه
├ 🎯 کوییز
├ 📦 باکس
├ ⚽ پنالتی
├ 🎮 حدس [سنگ/کاغذ/قیچی]
├ 🎲 تصادفی [عدد کوچک] [عدد بزرگ]
├ 🧮 حساب [عبارت]
├ 🗣 بگو [متن]
├ 🔄 برعکس [متن]
├ 📏 طول [متن]
├ 🔡 کوچک [متن انگلیسی]
├ 🔠 بزرگ [متن انگلیسی]
├ 📖 ویکی [موضوع]
├ 🎮 چالش
├ 🎲 تاس
├ 🎨 فونت [متن انگلیسی]
├ 📚 فکت
├ 🪶 فال
└ 📜 حکمت
━━━━━━━━━━━━━━━━
🤖 @RoboSupport
"""


HELP_SETTINGS = """⚙️ لیست تنظیمات
━━━━━━━━━━━━━━━━
├ 🎛 تنظیمات
├ 🚫 فیلتر فحش
├ 🚫 فیلتر فحش روشن
├ 🚫 فیلتر فحش خاموش
├ 🛡 ضد اسپم روشن
├ 🛡 ضد اسپم خاموش
├ 🗣 سخنگو روشن
├ 🔇 سخنگو خاموش
└ ⚠️ تعداد اخطار [عدد ۱-۱۰]
━━━━━━━━━━━━━━━━
🤖 @RoboSupport
"""


# ─── بخش مدیریت ───
HELP_ADMIN = """👮 لیست مدیریت
━━━━━━━━━━━━━━━━
├ 📌 پین
├ 🚫 بن / ریم
├ ✅ آنبن
├ 🔇 میوت
├ 🔊 آنمیوت
├ 🔒 قفل گروه
├ 🔓 آنلاک
├ 🧹 پاکسازی [عدد]
├ ⚠️ اخطار
├ 📋 اخطارا
└ 🗑 حذف اخطار
━━━━━━━━━━━━━━━━
🤖 @RoboSupport
"""
# ---------------------------------------------------------------------------
# کلاینت
# ---------------------------------------------------------------------------

client = Client(StringSession(session_str)) if session_str else Client(StringSession())

def _get_memory_usage() -> str:
    """مصرف RAM فعلی رو برمی‌گردونه"""
    import sys
    try:
        import resource
        kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform == "darwin":
            return f"{kb / 1024 / 1024:.1f} MB"
        return f"{kb / 1024:.1f} MB"
    except Exception:
        try:
            import psutil
            return f"{psutil.Process().memory_info().rss / 1024 / 1024:.1f} MB"
        except Exception:
            return "N/A"

# ═══════════════════════════════════════════════════════════════════
#  🤖 Regexهای AI و دستورات — یکبار کامپایل
# ═══════════════════════════════════════════════════════════════════
_IDENTITY_RE = re.compile(
    r"(سازنده?[‌\s]*(ت|ت\s+کیه|ش\s+کیه)|"
    r"کی\s+(ساختت|ساخنت|نوشتت|طراحیت|درستت\s+کرد|توسعه‌?ت\s+داد)|"
    r"(خالقت|برنامه\s*نویس\s*ت|توسعه\s*دهنده‌?ت)\s+کیه|"
    r"کدوم\s+تیم|چه\s+تیمی\s+(ساختت|ساختش)|"
    r"کی\s+به\s+وجودت\s+آورد)",
    re.IGNORECASE,
)

_API_RE = re.compile(
    r"(مدل\s*ت\s+چیه|مدل\s*تو\s+چیه|چه\s+مدلی|"
    r"با\s+چی\s+ساختنت|با\s+چی\s+ساخته\s+شد(ی)?|"
    r"(api|ای\s*پی\s*آی)\s*ت\s*چیه|از\s+چه\s+api|"
    r"زیرساختت|مغزت\s+چیه|هوش\s+مصنوعیت\s+چیه|"
    r"تو\s+(gemini|gpt|claude|گوگل|جی‌?پی‌?تی|کلود)\s+(هستی|ن)?|"
    r"(anthropic|openai|deepmind|آنتروپیک|اوپن\s*ای\s*آی|دیپ\s*مایند)\s+(هستی|استفاده)|"
    r"کدوم\s+(ai|هوش\s+مصنوعی)|"
    r"با\s+چه\s+هوش)",
    re.IGNORECASE,
)

_JAILBREAK_KEYS = frozenset((
    "ignore previous", "ignore all", "دستورات قبلی",
    "system prompt", "پرامپت سیستمی", "پرامپتت",
    "دستوراتت", "دستورات اصلی", "ریست شو",
    "دروغ نگو", "راستش رو بگو تو چی",
    "خودت رو فرض کن", "فرض کن تو", "نقش بازی کن",
    "بگو تو چی هستی واقعا", "پشت صحنه",
    "developer mode", "حالت توسعه",
))

_LEAK_WORDS_RE = re.compile(
    r"\b(gemini|openai|chatgpt|gpt-4|gpt-3|deepmind|anthropic|claude|"
    r"large language model|مدل زبانی|مدل هوش مصنوعی|"
    r"آنتروپیک|کلود|اوپن ای آی|دیپ مایند|زبان بزرگ)\b",
    re.IGNORECASE,
)

# ─── تشخیص سریع دستور ───
_EXACT_COMMANDS = frozenset((
    "پینگ", "تاریخ", "سکه", "چالش", "تاس", "فکت", "فال", "حکمت",
    "کوییز", "پنالتی", "باکس", "راهنما",
    "لیست ابزار", "لیست سرگرمی", "لیست تنظیمات", "لیست مدیریت",
    "روبو", "بن", "ریم", "میوت", "آنمیوت", "انمیوت", "پین",
    "آنبن", "انبن", "قفل گروه", "بازگشایی", "آنلاک", "انلاک",
    "اخطار", "اخطارا", "لیست اخطار", "حذف اخطار",
    "فیلتر فحش", "فیلتر فحش روشن", "فیلتر فحش خاموش",
    "آمار", "امار", "آمار من", "امار من", "آمار گروه", "امار گروه",
    "سخنگو روشن", "سخنگو خاموش",
    "ضد اسپم روشن", "ضد اسپم خاموش",
    "تنظیمات", "ترجمه", "هوا", "ارز", "فلزات", "فعال",
))

_PREFIX_COMMANDS = frozenset((
    "بگو", "برعکس", "بزرگ", "کوچک", "طول",
    "تصادفی", "حساب", "فونت", "ویکی", "ترجمه", "پاکسازی",
    "هوای", "روبو", "تعداد", "حدس",
))


def _is_command(txt: str) -> bool:
    if not txt:
        return False
    if txt in _EXACT_COMMANDS:
        return True
    sp = txt.find(" ")
    if sp == -1:
        return False
    return txt[:sp] in _PREFIX_COMMANDS


async def _get_chat_cached(event: Any, chat_id: Optional[int]) -> Any:
    if chat_id is None:
        return None
    now = time.time()
    cached = _chat_obj_cache.get(chat_id)
    if cached and cached[1] > now:
        return cached[0]

    try:
        chat = await event.get_chat()
    except Exception:
        chat = getattr(event, "chat", None)

    if chat is not None:
        _chat_obj_cache[chat_id] = (chat, now + _CHAT_OBJ_TTL)
    return chat

# ---------------------------------------------------------------------------
# هندلر اصلی
# ---------------------------------------------------------------------------
@client.on_message()
async def main_handler(client: Client, event: Any) -> None:
    if getattr(event, "out", False):
        return
    msg = getattr(event, "message", None)

    try:
        me = getattr(client, "me", None)
        if me is not None:
            sender_check = getattr(event, "sender_id", None)
            if sender_check is None and msg is not None:
                sender_check = getattr(msg, "sender_id", None) or getattr(msg, "from_id", None)
            if sender_check is not None and sender_check == getattr(me, "id", None):
                return
    except Exception:
        pass

    raw = get_event_text(event)
    txt = normalize_text(raw) if raw else ""

    chat_id = (
        getattr(event, "chat_id", None)
        or (getattr(msg, "chat_id", None) if msg is not None else None)
        or getattr(getattr(event, "chat", None), "id", None)
    )
    chat = await _get_chat_cached(event, chat_id)
    is_group = check_is_group(event, chat)
    if not is_group and isinstance(chat_id, int) and chat_id < 0:
        is_group = True

    sender = None
    try:
        sender = getattr(event, "sender_id", None)
        if sender is None and msg is not None:
            sender = getattr(msg, "sender_id", None) or getattr(msg, "from_id", None)
    except Exception:
        pass

    # ── تشخیص پاسخ پنالتی (فقط با ریپلای) ──
    if is_group and msg is not None and txt:
        reply_to_id = (
            getattr(msg, "reply_to_msg_id", None)
            or getattr(event, "reply_to_msg_id", None)
        )
        if reply_to_id is None:
            rt = getattr(msg, "reply_to", None) or getattr(event, "reply_to", None)
            if rt is not None:
                reply_to_id = (
                    getattr(rt, "reply_to_msg_id", None)
                    or getattr(rt, "id", None)
                )

        if reply_to_id is not None and reply_to_id in _active_penalties:
            pen = _active_penalties.get(reply_to_id)

            # 👇 فقط همون کاربری که پنالتی رو شروع کرده می‌تونه جواب بده
            if pen is not None and sender is not None and pen.get("sender") is not None:
                if sender != pen["sender"]:
                    await safe_reply(
                        event,
                        "⛔ این پنالتی مال تو نیست!\n"
                        "خودت یه پنالتی جدید بزن."
                    )
                    return

            _active_penalties.pop(reply_to_id, None)
            picked = _parse_penalty_choice(txt)

            if picked is None:
                if pen is not None:
                    _active_penalties[reply_to_id] = pen
                await safe_reply(
                    event,
                    "⚠️ فقط «چپ»، «وسط» یا «راست» رو قبول می‌کنم.\n"
                    "دوباره روی همون پیام ریپلای بزن."
                )
                return

            result = play_penalty(picked, pen["player"])
            await safe_reply(event, result)
            return

        # اگه کاربر چپ/وسط/راست رو بدون ریپلای بفرستاد
        if reply_to_id is None:
            bare = _parse_penalty_choice(txt)
            if bare is not None:
                user_has_active = any(
                    p.get("chat_id") == chat_id and p.get("sender") == sender
                    for p in _active_penalties.values()
                )
                if user_has_active:
                    await safe_reply(
                        event,
                        "⚠️ باید روی پیام پنالتی ریپلای بزنی، نه اینکه فقط کلمه رو بفرستی مشتی.\n"
                    )
                    return

    # ── تشخیص پاسخ بازی باکس (فقط با ریپلای) ──
    if is_group and msg is not None and txt:
        reply_to_id = (
            getattr(msg, "reply_to_msg_id", None)
            or getattr(event, "reply_to_msg_id", None)
        )
        if reply_to_id is None:
            rt = getattr(msg, "reply_to", None) or getattr(event, "reply_to", None)
            if rt is not None:
                reply_to_id = (
                    getattr(rt, "reply_to_msg_id", None)
                    or getattr(rt, "id", None)
                )

        if reply_to_id is not None and reply_to_id in _active_boxes:
            box = _active_boxes.get(reply_to_id)

            # فقط صاحب بازی می‌تونه جواب بده
            if box is not None and sender is not None and box.get("sender") is not None:
                if sender != box["sender"]:
                    await safe_reply(
                        event,
                        "⛔ این بازی مال تو نیست!\n"
                        "خودت یه بازی جدید با «باکس» شروع کن."
                    )
                    return

            guess = _parse_box_choice(txt)
            if guess is None:
                await safe_reply(event, "⚠️ فقط یه عدد بین ۱ تا ۹ بفرست.")
                return

            result_text, ended = _play_box_round(box, guess)
            grid = _build_box_grid(box["tried"])

            if ended:
                _active_boxes.pop(reply_to_id, None)
                new_text = (
                    "📦 بازی باکس — پایان\n"
                    "━━━━━━━━━━━━━━━━\n"
                    f"{grid}\n"
                    "━━━━━━━━━━━━━━━━\n"
                    f"{result_text}"
                )
            else:
                remaining = _BOX_MAX_ATTEMPTS - len(box["tried"])
                found = sum(
                    1 for t in box["treasures"]
                    if box["tried"].get(t) == "💰"
                )
                new_text = (
                    "📦 بازی باکس\n"
                    "━━━━━━━━━━━━━━━━\n"
                    f"💰 گنج‌های پیدا شده: {_to_fa_num(found)} از {_to_fa_num(_BOX_TREASURE_COUNT)}\n"
                    f"🎯 شانس باقی‌مونده: {_to_fa_num(remaining)}\n\n"
                    f"{grid}\n"
                    "━━━━━━━━━━━━━━━━\n"
                    f"{result_text}"
                )

            msg_obj = box.get("msg_obj")
            if msg_obj is not None:
                if not await safe_edit(msg_obj, new_text):
                    await safe_reply(event, new_text)
            else:
                await safe_reply(event, new_text)
            return

        # اگه کاربر عدد بدون ریپلای فرستاد
        if reply_to_id is None:
            bare = _parse_box_choice(txt)
            if bare is not None:
                user_has_active = any(
                    p.get("chat_id") == chat_id and p.get("sender") == sender
                    for p in _active_boxes.values()
                )
                if user_has_active:
                    await safe_reply(
                        event,
                        "⚠️ باید روی پیام بازی باکس ریپلای بزنی، نه اینکه فقط عدد بفرستی."
                    )
                    return


    if is_group and chat_id is not None and sender is not None:
        sender_is_admin = False
        try:
            sender_is_admin = await is_user_admin_cached(
                chat if chat is not None else chat_id, sender
            )
        except Exception:
            sender_is_admin = False

        if is_muted(sender, chat_id) and not sender_is_admin:
            try:
                await event.delete()
            except Exception:
                try:
                    if msg is not None:
                        await msg.delete()
                except Exception:
                    pass
            return

        media_type = ""
        try:
            media = getattr(event, "media", None) or (getattr(msg, "media", None) if msg else None)
            if media is not None:
                mime = (getattr(media, "mime_type", "") or "").lower()
                title = (getattr(media, "title", "") or "").lower()
                mname = type(media).__name__.lower()
                if "gif" in mime or "gif" in title or "gif" in mname:
                    media_type = "gif"
                elif "sticker" in mname:
                    media_type = "sticker"
                elif "photo" in mname:
                    media_type = "photo"
                elif "video" in mname and "note" not in mname:
                    media_type = "video"
                elif "voice" in mname:
                    media_type = "voice"
                elif "audio" in mname:
                    media_type = "audio"
                elif "document" in mname:
                    media_type = "فایل"
        except Exception:
            pass

        if txt or media_type:
            is_command = _is_command(txt)

            if not is_command:
                # ===== فیلتر فحش =====
                if (txt
                        and chat_id is not None
                        and is_badword_filter_on(chat_id)
                        and not sender_is_admin
                        and _BAD_PATTERN.search(txt)):
                    try:
                        await event.delete()
                    except Exception:
                        pass

                    if not is_warn_cooldown(sender, chat_id):
                        set_warn_cooldown(sender, chat_id)
                        name = await get_sender_display_name(event, sender)
                        await _add_warning_and_maybe_kick(
                            client, chat_id, sender, name, "فحش دادن"
                        )
                    return

                if (not sender_is_admin
                        and chat_id is not None
                        and get_setting(chat_id, "antispam_enabled", True)):
                    reason = is_spam(sender, chat_id, txt, media_type)
                    if reason:
                        try:
                            await event.delete()
                        except Exception:
                            try:
                                if msg is not None:
                                    await msg.delete()
                            except Exception:
                                pass

                        k = f"{chat_id}:{sender}"
                        _user_msg_times[k].clear()
                        _user_media_times[k].clear()
                        _user_emoji_times[k].clear()
                        _user_msg_hashes[k].clear()
                        _user_gif_times[k].clear()

                        action, duration, n = get_punishment(sender, chat_id)
                        name = await get_sender_display_name(event, sender)

                        if action == "warn":
                            if not is_warn_cooldown(sender, chat_id):
                                set_warn_cooldown(sender, chat_id)
                                max_level = _PUNISH_LADDER[-1][0]
                                remaining = max_level - n
                                await safe_send(
                                    client, chat_id,
                                    f"⚠️ {name} به دلیل {reason} اخطار گرفت.\n"
                                    f"📊 سطح اخطار: {n}/{max_level}\n"
                                    f"❗️ {remaining} اخطار تا بن شدن."
                                )
                        elif action == "mute":
                            set_mute(sender, chat_id, duration=duration)
                            try:
                                if hasattr(client, "edit_permissions"):
                                    await client.edit_permissions(
                                        chat_id, sender,
                                        send_messages=False,
                                        send_media=False,
                                        send_stickers=False,
                                        send_gifs=False,
                                    )
                            except Exception:
                                pass
                            dur_text = _fmt_duration(duration)
                            await safe_send(
                                client, chat_id,
                                f"🔇 {name} به دلیل {reason} برای {dur_text} میوت شد.\n"
                                f"📊 تخلف شماره {n}"
                            )
                        elif action == "kick":
                            try:
                                if hasattr(client, "kick_participant"):
                                    await client.kick_participant(chat_id, sender)
                                elif hasattr(client, "edit_permissions"):
                                    await client.edit_permissions(
                                        chat_id, sender, view_messages=False
                                    )
                            except Exception:
                                pass

                            _offense_count.pop(f"{chat_id}:{sender}", None)

                            await safe_send(
                                client, chat_id,
                                f"🚫 {name} به دلیل {reason} و رسیدن به {n} تخلف، از گروه بن شد."
                            )
                        return
                    
                # ── 📊 ثبت آمار پیام ──
                if chat_id is not None and sender is not None:
                    _bump_stat(chat_id, sender)

    if not txt:
        return
    # ========== ⚙️ پنل تنظیمات ==========
    if txt == "تنظیمات":
        if not is_group or chat_id is None:
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ فقط ادمین‌ها.")
            return
        group_title = getattr(chat, "title", "گروه") if chat else "گروه"
        await safe_reply(event, _build_panel(chat_id, group_title))
        return


    # ─── toggle فیلتر و ضد اسپم ───
    _text_toggles = {
        "ضد اسپم روشن":    ("antispam_enabled", True),
        "ضد اسپم خاموش":   ("antispam_enabled", False),
    }
    if txt in _text_toggles:
        if not is_group or chat_id is None:
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ فقط ادمین‌ها.")
            return
        key, val = _text_toggles[txt]
        set_setting(chat_id, key, val)
        await safe_reply(event, f"✅ {txt} شد.")
        return

    # ─── toggle سخنگو ───
    if txt in ("سخنگو روشن", "سخنگو خاموش"):
        if not is_group or chat_id is None:
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ فقط ادمین‌ها.")
            return
        if txt == "سخنگو روشن":
            set_setting(chat_id, "chat_enabled", True)
            await safe_reply(event, "✅ سخنگو ربات روشن شد.")
        else:
            set_setting(chat_id, "chat_enabled", False)
            await safe_reply(event, "🔕 سخنگو ربات خاموش شد.")
        return

    # ─── تعداد اخطار ───
    m_w = re.match(r'^تعداد اخطار\s+(\d+)$', txt)
    if m_w:
        if not is_group or chat_id is None:
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ فقط ادمین.")
            return
        n = int(m_w.group(1))
        if n < 1 or n > 10:
            await safe_reply(event, "❌ بین ۱ تا ۱۰.")
            return
        set_setting(chat_id, "max_warnings", n)
        await safe_reply(event, f"✅ تعداد اخطار = {n} بار")
        return

    # ========== 📚 راهنما ==========
    if txt == "راهنما":
        try:
            await safe_reply(event, HELP_MAIN)
        except Exception as exc:
            log.error("help main error: %s", exc)
        return

    if txt == "لیست ابزار":
        try:
            await safe_reply(event, HELP_TOOLS)
        except Exception as exc:
            log.error("help tools error: %s", exc)
        return

    if txt == "لیست سرگرمی":
        try:
            await safe_reply(event, HELP_FUN)
        except Exception as exc:
            log.error("help fun error: %s", exc)
        return

    if txt == "لیست تنظیمات":
        try:
            await safe_reply(event, HELP_SETTINGS)
        except Exception as exc:
            log.error("help settings error: %s", exc)
        return

    if txt == "لیست مدیریت":
        try:
            await safe_reply(event, HELP_ADMIN)
        except Exception as exc:
            log.error("help admin error: %s", exc)
        return
    # ========== 🤖 هوش مصنوعی ==========
    if txt == "روبو" or txt.startswith("روبو "):
        prompt = txt[4:].strip() if len(txt) > 4 else ""

        if not prompt:
            await safe_reply(
                event,
                "🤖 روبو در خدمتته!\n\n"
                "سوالت رو بعد از کلمه‌ی «روبو» بنویس تا جواب بدم.\n\n"
                "مثال:\n"
                "• روبو انصارالله چیه؟\n"
                "• روبو یه جوک بگو\n"
            )
            return
        # ═══════ اینترسپت‌ها ═══════
        _p = prompt.lower()

        if _IDENTITY_RE.search(_p):
            await safe_reply(
                event,
                "✯ منو تیم زنیث ساختن.\n📢 کانالم: @RoboSupport"
            )
            return

        if _API_RE.search(_p):
            await safe_reply(
                event,
                "من روبو هستم 🤖 — یه ربات فارسی‌زبان که تیم زنیث ساخته.\n"
                "اگه سوال دیگه‌ای داری بپرس!"
            )
            return


        if any(k in _p for k in _JAILBREAK_KEYS):
            await safe_reply(event, "من فقط روبو هستم 🤖 — سوال دیگه‌ای داری؟")
            return

        if len(prompt) > 800:
            await safe_reply(event, "❌ سوالت خیلی طولانیه. حداکثر ۸۰۰ کاراکتر.")
            return

        # ═══════ 🛡 بررسی Cooldown (هر نفر هر ۱۵ ثانیه یه بار) ═══════
        if sender is not None and chat_id is not None:
            allowed, wait = _ai_cooldown_check(sender, chat_id)
            if not allowed:
                await safe_reply(
                    event,
                    f"⏳ مشتی یه لحظه صبر کن!\n"
                    f"{wait:.0f} ثانیه دیگه می‌تونی سوال بعدی رو بپرسی."
                )
                return


        msg_ai = await safe_reply(event, "🤖 در حال فکر کردن...")
        ai_answer = await ask_ai(prompt)

        if not ai_answer:
            err = "❌ متأسفانه الان نتونستم جواب بدم. بعداً دوباره امتحان کن."
            if not await safe_edit(msg_ai, err):
                await safe_reply(event, err)
            return

        # ═══════ ۱. پاک‌سازی معرفی سازنده و کلمات حساس ═══════
        ai_answer = _strip_unrequested_identity(ai_answer)
        ai_answer = _LEAK_WORDS_RE.sub("", ai_answer)

        # جمع‌کردن فاصله‌های اضافی بعد از حذف
        ai_answer = re.sub(r"[ \t]+", " ", ai_answer)
        ai_answer = re.sub(r"\n{2,}", "\n", ai_answer).strip()
        
        # ═══════ ۳. اگه بعد از فیلتر خالی شد، یه پیام پیش‌فرض بفرست ═══════
        if not ai_answer or not ai_answer.strip():
            ai_answer = "متأسفانه نتونستم جواب مناسبی پیدا کنم. دوباره بپرس."

        if len(ai_answer) > MAX_MESSAGE_LEN:
            ai_answer = ai_answer[:MAX_MESSAGE_LEN - 20] + "\n..."

        if not await safe_edit(msg_ai, ai_answer):
            await safe_delete(msg_ai)
            await safe_reply(event, ai_answer)
        return

    if txt == "پینگ":
        msg_ping = await safe_reply(event, "🏓 در حال بررسی سرعت...")

        start = time.perf_counter()
        probe_failed = False
        try:
            ping_method = getattr(client, "ping", None)
            if callable(ping_method):
                await ping_method()
            else:
                await client.get_me()
        except Exception as exc:
            log.debug("ping probe failed: %s", exc)
            probe_failed = True

        latency_ms = (time.perf_counter() - start) * 1000

        if probe_failed:
            text_pong = "🏓 pong!\n\n⚠️ اندازه‌گیری ناموفق بود"
        else:
            if latency_ms < 200:
                emoji = "🟢"
            elif latency_ms < 600:
                emoji = "🟡"
            else:
                emoji = "🔴"
            text_pong = f"🏓 pong!\n\n{emoji} ⏱ زمان پاسخ‌دهی: {latency_ms:.0f} میلی‌ثانیه"

        if not await safe_edit(msg_ping, text_pong):
            await safe_reply(event, text_pong)
        return


    if txt == "تاریخ":
        now = datetime.now()
        shamsi = get_shamsi_date(now)
        miladi = now.strftime("%Y-%m-%d")
        await safe_reply(
            event,
            "📅 تاریخ امروز\n"
            "━━━━━━━━━━━━━━━━\n"
            f"🇮🇷 شمسی: {shamsi}\n"
            f"🌍 میلادی: {miladi}\n"
            "━━━━━━━━━━━━━━━━"
        )
        return


    if txt == "سکه":
        result = random.choice(["🦁 شیر", "〰️ خط"])
        await safe_reply(event, f"🪙 نتیجه پرتاب سکه:\n\n{result}")
        return

    if txt == "چالش":
        await safe_reply(event, random_challenge())
        return

    if txt == "تاس":
        num, art = roll_dice()
        await safe_reply(event, f"\n{art}")
        return

    if txt == "فکت":
        await safe_reply(event, random.choice(_FACTS))
        return

    if txt == "فال":
        await safe_reply(event, random_fal())
        return

    if txt == "حکمت":
        await safe_reply(event, random_hekmat())
        return

# ========== 🎮 سنگ کاغذ قیچی ==========
    if txt == "حدس" or txt.startswith("حدس "):
        choice = txt[4:].strip()
        if not choice:
            await safe_reply(
                event,
                "🎮 بازی سنگ کاغذ قیچی\n\n"
                "بنویس:\n"
                "• حدس سنگ\n"
                "• حدس کاغذ\n"
                "• حدس قیچی"
            )
            return

        result = play_rps(choice)
        await safe_reply(event, result)
        return

    # ========== ⚽ پنالتی ==========
    if txt == "پنالتی":
        if chat_id is None:
            return

        player = random.choice(_PENALTY_PLAYERS)
        msg_obj = await safe_reply(event, _build_penalty_text(player))
        if msg_obj is None:
            return

        msg_id = getattr(msg_obj, "id", None)
        if msg_id is None:
            return

        _active_penalties[msg_id] = {
            "chat_id": chat_id,
            "player": player,
            "msg_obj": msg_obj,
            "sender": sender,          # 👈 این خط جدید
        }
        asyncio.create_task(_penalty_timeout(msg_id))
        return

    # ========== 📦 بازی باکس ==========
    if txt == "باکس":
        if chat_id is None:
            return

        treasures = random.sample(range(1, 10), _BOX_TREASURE_COUNT)

        msg_obj = await safe_reply(event, _build_box_start_text())
        if msg_obj is None:
            return

        msg_id = getattr(msg_obj, "id", None)
        if msg_id is None:
            return

        _active_boxes[msg_id] = {
            "chat_id": chat_id,
            "treasures": treasures,
            "tried": {},
            "msg_obj": msg_obj,
            "sender": sender,
        }
        asyncio.create_task(_box_timeout(msg_id))
        return

    
    # ========== 🎯 کوییز ==========
    if txt == "کوییز":
        if chat_id is None:
            return

        quiz = random.choice(_QUIZ_QUESTIONS).copy()
        ok = await send_native_poll(chat_id, quiz)

        if not ok:
            await safe_reply(
                event,
                "❌ متأسفانه ساخت نظرسنجی ممکن نشد.\n"
                "لطفاً به ادمین بگو."
            )
        return

    if txt.startswith("بگو "):
        text = txt[4:].strip()
        if text:
            await safe_reply(event, f"\n\n「 {text} 」")
        return

    # ========== 📊 آمار گروه ==========
    if txt in ("آمار", "امار", "آمار گروه", "امار گروه"):
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ این دستور فقط در گروه کار می‌کنه.")
            return

        target_chat = chat.id if (chat is not None and getattr(chat, "id", None)) else chat_id
        rows = _get_chat_stats(target_chat)

        if not rows:
            await safe_reply(event,
                "📊 هنوز آماری ثبت نشده!\n"
            )
            return

        total = sum(v for _, v in rows)
        top = rows[:10]

        medals = ["🥇", "🥈", "🥉"]
        lines = [
            "📊  آمار پیام‌های گروه",
            "━━━━━━━━━━━━━━━━",
            f"👥  کاربران فعال: {_fmt(len(rows))}",
            f"💬  پیام‌ها: {_fmt(total)}",
            "",
            "🏆  برترین‌های گروه",
            "━━━━━━━━━━━━━━━━",
        ]

        for i, (uid, count) in enumerate(top):
            name = await get_user_name_cached(uid)
            if len(name) > 20:
                name = name[:19] + "…"
            rank = medals[i] if i < 3 else f"{i+1}."
            lines.append(f"{rank}  {name}  ←  {_fmt(count)}")

        lines.append("━━━━━━━━━━━━━━━━")

        text = "\n".join(lines)
        if len(text) > MAX_MESSAGE_LEN:
            text = text[:MAX_MESSAGE_LEN] + "\n..."
        await safe_reply(event, text)
        return

    if txt in ("آمار من", "امار من"):
        if not is_group or chat_id is None or sender is None:
            await safe_reply(event, "❌ این دستور فقط در گروه کار می‌کنه.")
            return

        target_chat = chat.id if (chat is not None and getattr(chat, "id", None)) else chat_id
        rows = _get_chat_stats(target_chat)
        my_count = 0
        my_rank = 0
        for i, (uid, count) in enumerate(rows):
            if uid == sender:
                my_count = count
                my_rank = i + 1
                break

        name = safe_sender_name(event)
        if not name or name == "کاربر":
            try:
                name = await get_user_name_cached(sender)
            except Exception:
                name = "کاربر ناشناس"

        if my_count == 0:
            await safe_reply(
                event,
                "📊  آمار شما\n"
                "━━━━━━━━━━━━━━━━\n"
                f"👤  {name}\n"
                "━━━━━━━━━━━━━━━━\n"
                "هنوز پیامی توی این گروه نداری!"
            )
            return

        total_members = len(rows)

        await safe_reply(
            event,
            "📊  آمار شما\n"
            "━━━━━━━━━━━━━━━━\n"
            f"👤  {name}\n"
            f"🏅  رتبه: {my_rank} از {_fmt(total_members)}\n"
            f"💬  پیام‌ها: {_fmt(my_count)}\n"
            "━━━━━━━━━━━━━━━━"
        )
        return

    if txt.startswith("برعکس "):
        text = txt[6:].strip()
        if text:
            await safe_reply(event, f"🔄 متن معکوس شده:\n\n「 {text[::-1]} 」")
        return

    if txt.startswith("بزرگ "):
        text = txt[5:].strip()
        if text:
            await safe_reply(event, f"🔠 حروف بزرگ:\n\n「 {text.upper()} 」")
        return

    if txt.startswith("کوچک "):
        text = txt[5:].strip()
        if text:
            await safe_reply(event, f"🔡 حروف کوچک:\n\n「 {text.lower()} 」")
        return

    if txt.startswith("طول "):
        text = txt[4:].strip()
        if text:
            await safe_reply(event, f"📏 طول متن:\n🔢 {len(text)} کاراکتر")
        return

    m = re.match(r'^تصادفی\s+(\d+)\s+(\d+)$', txt)
    if m:
        a, b = int(m.group(1)), int(m.group(2))
        if a > b:
            a, b = b, a
        num = random.randint(a, b)
        await safe_reply(event, f"🎲 عدد تصادفی بین {a} و {b}:\n\n✨ {num}")
        return

    if txt.startswith("حساب "):
        expr = txt[5:].strip()
        try:
            node = ast.parse(expr, mode='eval').body

            def eval_node(n):
                if isinstance(n, ast.Constant):
                    return n.value
                elif isinstance(n, ast.BinOp):
                    l, r = eval_node(n.left), eval_node(n.right)
                    if isinstance(n.op, ast.Add): return l + r
                    if isinstance(n.op, ast.Sub): return l - r
                    if isinstance(n.op, ast.Mult): return l * r
                    if isinstance(n.op, ast.Div): return l / r
                    if isinstance(n.op, ast.Pow): return l ** r
                    if isinstance(n.op, ast.Mod): return l % r
                elif isinstance(n, ast.UnaryOp):
                    v = eval_node(n.operand)
                    if isinstance(n.op, ast.USub): return -v
                raise ValueError("unsupported")

            result = eval_node(node)
            if isinstance(result, float) and result.is_integer():
                result = int(result)
            await safe_reply(event, f"🧮 نتیجه محاسبه:\n\n{expr} = {result}")
        except Exception:
            await safe_reply(event, "❌ عبارت وارد شده معتبر نیست.")
        return

    if txt.startswith("فونت "):
        text = txt[5:].strip()
        if not text:
            await safe_reply(event, "❌ مثال: فونت TDA")
            return
        if not re.match(r'^[a-zA-Z0-9\s]+$', text):
            await safe_reply(event, "❌ فقط حروف انگلیسی و عدد.")
            return
        lines = apply_all_fonts(text)
        wrapped = [f"<code>{line}</code>" for line in lines]
        full = "\n".join(wrapped)
        if len(full) > MAX_MESSAGE_LEN:
            mid = len(wrapped) // 2
            try:
                await safe_reply(event, "\n".join(wrapped[:mid]), parse_mode="html")
            except Exception:
                await safe_reply(event, "\n".join(wrapped[:mid]))
            await asyncio.sleep(0.4)
            try:
                await safe_reply(event, "\n".join(wrapped[mid:]), parse_mode="html")
            except Exception:
                await safe_reply(event, "\n".join(wrapped[mid:]))
        else:
            try:
                await safe_reply(event, full, parse_mode="html")
            except Exception:
                await safe_reply(event, full)
        return

    if txt.startswith("ویکی "):
        query = txt[5:].strip()
        if not query:
            await safe_reply(event, "❌ لطفاً موضوع مورد نظر را وارد کنید.")
            return

        msg_w = await safe_reply(event, "🔍 در حال جستجو در ویکی‌پدیا...")
        title, text = await asyncio.to_thread(wikipedia_fa, query)

        if not title or not text:
            err = "❌ نتیجه‌ای یافت نشد."
            if not await safe_edit(msg_w, err):
                await safe_reply(event, err)
            return

        full_text = f"📚 {title}\n\n{text}"
        if len(full_text) > MAX_MESSAGE_LEN:
            full_text = full_text[:MAX_MESSAGE_LEN - 20] + "\n..."

        if not await safe_edit(msg_w, full_text):
            await safe_delete(msg_w)
            await safe_reply(event, full_text)
        return
    
    if txt == "هوا":
        await safe_reply(
            event,
            "🌤 برای دریافت آب و هوا، نام شهر را بعد از «هوای» بنویسید.\n\n"
            "مثلا:\n"
            "• هوای قم\n"
            "• هوای ساری\n"
            "• هوای اهواز"
        )
        return

    if txt.startswith("هوای "):
        city = txt[5:].strip()

        if not city:
            await safe_reply(event, "❌ نام شهر را وارد کنید.\nمثال: هوای تهران")
            return

        first_word = city.split()[0] if city else ""
        if first_word in _WEATHER_STOPWORDS:
            return

        msg_w = await safe_reply(event, "🌤 در حال دریافت اطلاعات آب و هوا...")
        weather_text = await _get_weather_async(city)

        if not weather_text:
            err = f"❌ اطلاعاتی برای «{city}» یافت نشد.\nنام شهر را دقیق‌تر بنویسید."
            if not await safe_edit(msg_w, err):
                await safe_reply(event, err)
            return

        if len(weather_text) > MAX_MESSAGE_LEN:
            weather_text = weather_text[:MAX_MESSAGE_LEN - 20] + "\n..."

        if not await safe_edit(msg_w, weather_text):
            await safe_delete(msg_w)
            await safe_reply(event, weather_text)
        return


    if txt == "ترجمه" or txt.startswith("ترجمه "):
        text = txt[5:].strip() if len(txt) > 5 else ""
        if not text:
            target_id, replied_msg = await _resolve_reply_target(event, msg)
            if replied_msg is not None:
                text = (
                    getattr(replied_msg, "message", "")
                    or getattr(replied_msg, "text", "")
                    or getattr(replied_msg, "raw_text", "")
                    or ""
                ).strip()
        if not text:
            await safe_reply(event, "❌ لطفاً بعد از کلمه ترجمه متن بنویسید یا ریپلای کنید.")
            return

        if len(text) > 3000:
            await safe_reply(event, "❌ متن خیلی طولانیه.")
            return

        translated, target = await auto_translate(text)
        if not translated:
            await safe_reply(event, "❌ ترجمه ناموفق بود.")
            return

        header = "🇬🇧 ترجمه به انگلیسی:" if target == "en" else "🇮🇷 ترجمه به پارسی:"
        result = f"{header}\n\n{translated}"
        if len(result) > MAX_MESSAGE_LEN:
            result = result[:MAX_MESSAGE_LEN - 20] + "\n..."
        await safe_reply(event, result)
        return

    # ========== 💱 ارز لحظه‌ای (فقط ارزها) ==========
    if txt == "ارز":
        msg_c = await safe_reply(event, "💱 در حال دریافت قیمت‌ها...")
        result = await get_currencies()

        if not result:
            err = "❌ متأسفانه الان نتونستم قیمت‌ها رو بگیرم. بعداً دوباره امتحان کن."
            if not await safe_edit(msg_c, err):
                await safe_reply(event, err)
            return

        # فیلتر فقط بخش ارزها (بدون طلا و نقره)
        currency_only_lines = []
        in_currency_section = False
        for line in result.split("\n"):
            if "💵 ارزها:" in line:
                in_currency_section = True
                currency_only_lines.append(line)
                continue
            if in_currency_section:
                # وقتی به بخش طلا یا نقره رسیدیم، متوقف شو
                if "🥇 طلا" in line or "🥈 نقره" in line:
                    break
                currency_only_lines.append(line)

        if currency_only_lines:
            currency_text = "\n".join(currency_only_lines).rstrip()
            currency_text += "\n━━━━━━━━━━━━━━━━\n 🤖 @RoboSupport"
        else:
            currency_text = result

        if len(currency_text) > MAX_MESSAGE_LEN:
            currency_text = currency_text[:MAX_MESSAGE_LEN - 20] + "\n..."

        if not await safe_edit(msg_c, currency_text):
            await safe_delete(msg_c)
            await safe_reply(event, currency_text)
        return
    
    # ========== 🥇 فلزات (طلا + سکه + نقره) ==========
    if txt == "فلزات":
        msg_c = await safe_reply(event, "💰 در حال دریافت قیمت فلزات...")
        result = await get_currencies()

        if not result:
            err = "❌ متأسفانه الان نتونستم قیمت‌ها رو بگیرم. بعداً دوباره امتحان کن."
            if not await safe_edit(msg_c, err):
                await safe_reply(event, err)
            return

        # فیلتر از بخش «طلا و سکه» تا آخر (طلا + سکه + نقره + فوتر)
        metals_lines = []
        in_section = False
        for line in result.split("\n"):
            if "طلا و سکه" in line:
                in_section = True
            if in_section:
                metals_lines.append(line)

        if metals_lines:
            metals_text = "\n".join(metals_lines)
        else:
            metals_text = result

        if len(metals_text) > MAX_MESSAGE_LEN:
            metals_text = metals_text[:MAX_MESSAGE_LEN - 20] + "\n..."

        if not await safe_edit(msg_c, metals_text):
            await safe_delete(msg_c)
            await safe_reply(event, metals_text)
        return
    
    m = re.match(r'^پاکسازی\s+(\d+)$', txt)
    if m:
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ این دستور فقط در گروه قابل استفاده است.")
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ شما دسترسی ادمین ندارید.")
            return
        if not await require_bot_admin(event, chat_id):     # ← این خط جدیده
            return                                          # ← این خط جدیده
        count = int(m.group(1))
        if count <= 0 or count > 1000:
            await safe_reply(event, "❌ تعداد باید بین ۱ تا ۱۰۰۰ باشد.")
            return
        try:
            target = chat.id if chat is not None else chat_id
            messages = await client.get_messages(target, limit=count)
            if not messages:
                await safe_reply(event, "ℹ️ پیامی برای حذف نیست.")
                return
            await client.delete_messages(target, messages)
            await safe_reply(event, f"✅ {len(messages)} پیام حذف شد.")
        except Exception as exc:
            await safe_reply(event, f"❌ خطا: {exc}")
        return

    if txt in ("بن", "ریم", "میوت", "آنمیوت", "انمیوت", "آنبن", "انبن", "اخطار", "حذف اخطار"):
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ این دستور فقط در گروه قابل استفاده است.")
            return

        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ شما دسترسی ادمین ندارید.")
            return

        target_id, replied_msg = await _resolve_reply_target(event, msg)
        if target_id is None:
            await safe_reply(event, "❌ روی پیام کاربر ریپلای کنید.")
            return

        target_chat = chat.id if (chat is not None and getattr(chat, "id", None)) else chat_id

        name = "کاربر"
        try:
            if replied_msg is not None:
                s = getattr(replied_msg, "sender", None)
                if s:
                    name = getattr(s, "first_name", None) or getattr(s, "title", None) or name
        except Exception:
            pass

        if (not name or name == "کاربر") and target_id is not None:
            try:
                name = await get_user_name_cached(target_id)
            except Exception:
                name = "کاربر ناشناس"

        if txt in ("اخطار", "بن", "ریم", "میوت"):
            try:
                if await is_user_admin(chat if chat is not None else chat_id, target_id):
                    await safe_reply(event, "⛔ نمی‌توانید ادمین‌ها را اخطار، بن یا میوت کنید.")
                    return
            except Exception:
                pass

        if txt == "اخطار":
            try:
                me = await client.get_me()
                if me and getattr(me, "id", None) == target_id:
                    await safe_reply(event, "⛔ نمی‌توانید به خود روبو اخطار بدهید.")
                    return
            except Exception:
                pass

        if txt in ("بن", "ریم"):
            if not await require_bot_admin(event, target_chat):
                return
            try:
                kicked = False
                if hasattr(client, "kick_participant"):
                    try:
                        await client.kick_participant(target_chat, target_id)
                        kicked = True
                    except Exception as exc:
                        log.debug("kick_participant failed: %s", exc)
                if not kicked and hasattr(client, "edit_permissions"):
                    try:
                        await client.edit_permissions(target_chat, target_id, view_messages=False)
                        kicked = True
                    except Exception as exc:
                        log.debug("edit_permissions ban failed: %s", exc)
                if kicked:
                    await safe_reply(event, f"🚫 کاربر {name} بن شد.")
                else:
                    await safe_reply(event, "❌ بن ناموفق بود.")
            except Exception as exc:
                await safe_reply(event, f"❌ خطا در بن: {exc}")
            return

        if txt in ("آنبن", "انبن"):
            if not await require_bot_admin(event, target_chat):
                return
            try:
                unbanned = False
                if hasattr(client, "edit_permissions"):
                    try:
                        await client.edit_permissions(
                            target_chat, target_id,
                            view_messages=True, send_messages=True,
                            send_media=True, send_stickers=True, send_gifs=True,
                        )
                        unbanned = True
                    except Exception:
                        pass
                key = f"{target_chat}:{target_id}"
                if key in _muted_until:
                    del _muted_until[key]
                if unbanned:
                    await safe_reply(event, f"✅ رفع بن {name} شد.")
                else:
                    await safe_reply(event, "❌ رفع بن ناموفق بود.")
            except Exception as exc:
                await safe_reply(event, f"❌ خطا: {exc}")
            return

        if txt == "میوت":
            try:
                real_muted = False
                if hasattr(client, "edit_permissions"):
                    try:
                        await client.edit_permissions(
                            target_chat, target_id,
                            send_messages=False, send_media=False,
                            send_stickers=False, send_gifs=False,
                        )
                        real_muted = True
                    except Exception as exc:
                        log.debug("real mute failed: %s", exc)

                set_mute(target_id, target_chat, duration=86400 * 365)

                if real_muted:
                    await safe_reply(event, f"🔇 کاربر {name} میوت شد.")
                else:
                    await safe_reply(
                        event,
                        f"⚠️ نتونستم {name} رو میوت کنم (ربات ادمین نیست).\n"
                    )
            except Exception as exc:
                await safe_reply(event, f"❌ خطا: {exc}")
            return

        if txt in ("آنمیوت", "انمیوت"):
            key = f"{target_chat}:{target_id}"
            had_internal = key in _muted_until
            _muted_until.pop(key, None)
            _warn_cooldown.pop(key, None)

            unmuted = False
            if hasattr(client, "edit_permissions"):
                try:
                    await client.edit_permissions(
                        target_chat, target_id,
                        send_messages=True, send_media=True,
                        send_stickers=True, send_gifs=True,
                    )
                    unmuted = True
                except Exception:
                    pass

            if unmuted or had_internal:
                await safe_reply(event, f"🔊 میوت {name} برداشته شد.")
            else:
                await safe_reply(event, f"ℹ️ {name} میوت نبود.")
            return

        if txt == "اخطار":
            try:
                try:
                    max_warn = int(get_setting(target_chat, "max_warnings", MAX_WARNINGS) or MAX_WARNINGS)
                except (TypeError, ValueError):
                    max_warn = MAX_WARNINGS
                if max_warn < 1:
                    max_warn = 1

                key = f"{target_chat}:{target_id}"
                current = warnings_data.get(key, 0) + 1
                warnings_data[key] = current
                await save_warnings()

                if current >= max_warn:
                    kicked = False
                    try:
                        if hasattr(client, "kick_participant"):
                            await client.kick_participant(target_chat, target_id)
                            kicked = True
                        elif hasattr(client, "edit_permissions"):
                            await client.edit_permissions(target_chat, target_id, view_messages=False)
                            kicked = True
                    except Exception as exc:
                        log.debug("warning-kick failed: %s", exc)

                    if kicked:
                        warnings_data.pop(key, None)
                        _offense_count.pop(f"{target_chat}:{target_id}", None)
                        await save_warnings()
                        await safe_reply(event, f"🚫 کاربر {name} به دلیل {max_warn} اخطار، بن شد.")
                    else:
                        await safe_reply(
                            event,
                            f"⚠️ {name} به {max_warn} اخطار رسید ولی نتونستم بنش کنم.\n"
                            f"لطفاً من رو ادمین کنید یا دستی اقدام کنید."
                        )
                else:
                    remaining = max_warn - current
                    await safe_reply(
                        event,
                        f"⚠️ {name} اخطار گرفت.\n"
                        f"📊 {current}/{max_warn}\n"
                        f"❗️ {remaining} اخطار تا بن."
                    )
            except Exception as exc:
                await safe_reply(event, f"❌ خطا: {exc}")
            return

        if txt == "حذف اخطار":
            try:
                key = f"{target_chat}:{target_id}"
                if key in warnings_data:
                    del warnings_data[key]
                    await save_warnings()
                    await safe_reply(event, f"🗑 اخطار {name} پاک شد.")
                else:
                    await safe_reply(event, f"ℹ️ {name} اخطاری ندارد.")
            except Exception as exc:
                await safe_reply(event, f"❌ خطا: {exc}")
            return

    if txt == "پین":
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ فقط در گروه.")
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ دسترسی ادمین ندارید.")
            return
        if not await require_bot_admin(event, chat_id):     # ← این خط جدیده
            return                                          # ← این خط جدیده
        target_id, replied_msg = await _resolve_reply_target(event, msg)
        if replied_msg is None:
            await safe_reply(event, "❌ روی پیام ریپلای کنید.")
            return
        target_chat = chat.id if (chat is not None and getattr(chat, "id", None)) else chat_id
        try:
            pinned = False
            for method_name in ("pin_message", "pin_chat_message"):
                method = getattr(client, method_name, None)
                if method is None:
                    continue
                try:
                    msg_id = getattr(replied_msg, "id", None)
                    if msg_id is not None:
                        await method(target_chat, msg_id)
                        pinned = True
                        break
                except Exception:
                    pass
            if pinned:
                await safe_reply(event, "📌 پیام پین شد.")
            else:
                await safe_reply(event, "❌ پین ناموفق بود.")
        except Exception as exc:
            await safe_reply(event, f"❌ خطا: {exc}")
        return

    if txt == "قفل گروه":
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ فقط در گروه.")
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ دسترسی ادمین ندارید.")
            return
        if not await require_bot_admin(event, chat_id):     # ← این خط جدیده
            return                                          # ← این خط جدیده
        try:
            muted = False
            if hasattr(client, "edit_permissions"):
                try:
                    await client.edit_permissions(
                        chat_id, None,
                        send_messages=False, send_media=False,
                        send_stickers=False, send_gifs=False,
                    )
                    muted = True
                except Exception:
                    pass
            if muted:
                await safe_reply(event, "🔒 گروه قفل شد.")
            else:
                await safe_reply(event, "❌ قفل ناموفق بود.")
        except Exception as exc:
            await safe_reply(event, f"❌ خطا: {exc}")
        return

    if txt in ("بازگشایی", "آنلاک", "انلاک"):
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ فقط در گروه.")
            return
        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ دسترسی ادمین ندارید.")
            return
        if not await require_bot_admin(event, chat_id):     # ← این خط جدیده
            return                                          # ← این خط جدیده
        try:
            opened = False
            if hasattr(client, "edit_permissions"):
                try:
                    await client.edit_permissions(
                        chat_id, None,
                        send_messages=True, send_media=True,
                        send_stickers=True, send_gifs=True,
                    )
                    opened = True
                except Exception:
                    pass
            if opened:
                await safe_reply(event, "🔓 گروه باز شد.")
            else:
                await safe_reply(event, "❌ بازگشایی ناموفق بود.")
        except Exception as exc:
            await safe_reply(event, f"❌ خطا: {exc}")
        return

    if txt in ("فیلتر فحش روشن", "فیلتر فحش خاموش"):
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ این دستور فقط در گروه کار می‌کنه.")
            return

        if not await _check_caller_admin(event, chat, chat_id, sender):
            await safe_reply(event, "⛔ شما دسترسی ادمین ندارید.")
            return

        turn_on = txt == "فیلتر فحش روشن"
        _badword_filter_state[str(chat_id)] = turn_on
        save_filters()

        if turn_on:
            await safe_reply(event,
                "✅ فیلتر فحش روشن شد.\n"
            )
        else:
            await safe_reply(event,
                "🔕 فیلتر فحش خاموش شد.\n"
            )
        return

    if txt == "فیلتر فحش":
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ این دستور فقط در گروه کار می‌کنه.")
            return

        state = is_badword_filter_on(chat_id)
        icon = "✅ روشن" if state else "🔕 خاموش"
        await safe_reply(event,
            f"وضعیت فیلتر فحش: {icon}\n\n"
            f"برای تغییر (فقط ادمین):\n"
            f"• فیلتر فحش روشن\n"
            f"• فیلتر فحش خاموش"
        )
        return


    if txt in ("اخطارا", "لیست اخطار"):
        if not is_group or chat_id is None:
            await safe_reply(event, "❌ فقط در گروه.")
            return
        target_chat = chat.id if (chat is not None and getattr(chat, "id", None)) else chat_id
        prefix = f"{target_chat}:"
        rows: List[str] = []
        for k, v in warnings_data.items():
            if k.startswith(prefix):
                uid = k.split(":", 1)[1]
                display_name = await get_user_name_cached(int(uid))
                rows.append(f"• {display_name} ➜ {v} اخطار")
        if not rows:
            await safe_reply(event, "✅ هیچ کاربری اخطار ندارد.")
        else:
            text = "📋 لیست اخطارها:\n\n" + "\n".join(rows)
            if len(text) > MAX_MESSAGE_LEN:
                text = text[:MAX_MESSAGE_LEN] + "\n..."
            await safe_reply(event, text)
        return

    if txt.strip() == "فعال":
        await safe_reply(
            event,
            "🤖 Robo در خدمت شماست!\n\n"
            "برای یادگیری دستورات کلمه راهنما را ارسال کنید.\n"
            "برای کارکرد درست، بات را ادمین کرده و دسترسی کامل بدهید."
        )
        return

    if is_group and txt and chat_id is not None:
        if get_setting(chat_id, "chat_enabled", True):
            chat_reply = try_chat_reply(txt)
            if chat_reply and random.random() < 0.6:
                try:
                    await safe_reply(event, chat_reply)
                except Exception as exc:
                    log.debug("chat reply failed: %s", exc)
                return


# ---------------------------------------------------------------------------
# اجرا
# ---------------------------------------------------------------------------
async def main() -> None:
    keep_alive()
    if not session_str:
        phone = os.environ.get("PHONE_NUMBER", "").strip() or DEFAULT_PHONE
        if not phone:
            try:
                phone = input("📱 لطفاً شماره تلفن خود را وارد کنید: ").strip()
            except EOFError:
                log.error("شماره تلفن در دسترس نیست.")
                return

        log.info("استفاده از شماره: %s", phone)
        log.info("در حال ارسال درخواست کد...")
        log.info("کد تأیید به روبو سروش شما ارسال می‌شود. لطفاً آن را اینجا وارد کنید:")

        await client.start(phone=phone)

        session_string = client.session.save()
        with open(SESSION_FILE, "w", encoding="utf-8") as f:
            f.write(session_string)
        log.info("سشن ذخیره شد. دفعه بعد مستقیماً لاگین می‌شوی.")
    else:
        await client.start()

    # GC freeze — دیتای ثابت (لیست‌ها، دیکشنری‌ها) دیگه چک نمی‌شه
    gc.freeze()
    log.info("⚡ GC frozen — RAM: %s", _get_memory_usage())

    async def _periodic_cleanup():
        global _groq_failures
        while True:
            try:
                await asyncio.sleep(_SPAM_CLEANUP_INTERVAL)
                _cleanup_spam_dicts(time.time())
                _cleanup_ai_cache()
                await _save_stats_if_dirty()
                save_settings()

                if _groq_failures > 0 and _groq_failures < 999:
                    _groq_failures = max(0, _groq_failures - 1)
            except asyncio.CancelledError:
                log.info("🛑 periodic_cleanup متوقف شد.")
                raise
            except Exception as exc:
                log.error("⚠️ periodic_cleanup خطا داد (ادامه می‌ده): %s", exc)
                await asyncio.sleep(5)

    cleanup_task = asyncio.create_task(_periodic_cleanup())
    stats_clear_task = asyncio.create_task(_daily_stats_clear())

    log.info("✨ روبو با موفقیت اجرا شد! ✨")

    try:
        await client.run_until_disconnected()
    except (KeyboardInterrupt, asyncio.CancelledError):
        log.info("🛑 در حال خاموش کردن روبو...")
    finally:
        cleanup_task.cancel()
        try:
            await cleanup_task
        except asyncio.CancelledError:
            pass

        stats_clear_task.cancel()
        try:
            await stats_clear_task
        except asyncio.CancelledError:
            pass

        await close_ai_session()

        try:
            await _save_stats_if_dirty()
            await save_warnings()
            await asyncio.to_thread(save_filters)
            await asyncio.to_thread(save_settings, True)
        except Exception as exc:
            log.debug("final save failed: %s", exc)
        try:
            session_attr = getattr(client, "_session", None) or getattr(client, "session", None)
            if session_attr is not None:
                for attr_name in ("_session", "session", "_client"):
                    inner = getattr(session_attr, attr_name, None)
                    if inner is not None and hasattr(inner, "close"):
                        try:
                            await inner.close()
                        except Exception:
                            pass
                if hasattr(session_attr, "close"):
                    try:
                        await session_attr.close()
                    except Exception:
                        pass
        except Exception as exc:
            log.debug("session close failed: %s", exc)

        try:
            if hasattr(client, "disconnect"):
                await client.disconnect()
        except Exception as exc:
            log.debug("disconnect failed: %s", exc)

        log.info("✅ روبو با موفقیت خاموش شد.")

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("🛑 متوقف شد.")