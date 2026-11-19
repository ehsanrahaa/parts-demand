#!/usr/bin/env python3
"""آمار تاریخی تقاضای قطعات یدکی خودرو از کانال‌های عمومی تلگرام.

سه کار می‌کند:
  1) collect  — صفحه‌های عمومی کانال‌ها را تا N روز به عقب می‌خواند، نام قطعه/خودرو/برند را
                در متن هر پست پیدا می‌کند و شمارش و بازدید هر پست را در SQLite ذخیره می‌کند.
  2) report   — جدول‌های فراوانی (قطعه×خودرو، قطعه، خودرو) را CSV و Markdown می‌نویسد.
  3) digest   — خلاصهٔ کوتاه را به تلگرام می‌فرستد.

خروجی «لحظه‌ای» نیست؛ یک تحقیق تاریخی است. عدد تقاضا = فراوانی نام قطعه در پست‌های عمومی
(و مجموع بازدید همان پست‌ها)، نه نرخ کلیک گوگل که منتشر نمی‌شود.
"""
import argparse
import calendar
import hashlib
import html
import json
import logging
import os
import re
import shutil
import sqlite3
import statistics
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import quote

import requests
from bs4 import BeautifulSoup

HERE = os.path.dirname(os.path.abspath(__file__))
log = logging.getLogger("parts")

def _load_env():
    """مقادیر .env را فقط برای کلیدهای تعریف‌نشده در محیط می‌گذارد؛ در Actions نیازی به فایل نیست."""
    p = os.path.join(HERE, ".env")
    if not os.path.exists(p):
        return
    with open(p, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, v = line.split("=", 1)
            os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))

_load_env()

TELEGRAM_TOKEN = os.environ.get("TELEGRAM_TOKEN", "")
CHAT_ID = os.environ.get("CHAT_ID", "")
DB_PATH = os.environ.get("DB_PATH", os.path.join(HERE, "data", "parts.db"))
OUT_DIR = os.environ.get("OUT_DIR", os.path.join(HERE, "out"))
CHANNELS_FILE = os.environ.get("CHANNELS_FILE", os.path.join(HERE, "channels.txt"))
NEWS_FILE = os.environ.get("NEWS_FILE", os.path.join(HERE, "news.txt"))
UA = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36",
      "Accept-Language": "fa-IR,fa;q=0.9"}
FA_DIGITS = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")

# ---------- متن ----------
TR = str.maketrans({"‌": " ", "ي": "ی", "ك": "ک", "ة": "ه", "ـ": "", "ﻻ": "لا", "٫": ".",
                    "۰": "0", "۱": "1", "۲": "2", "۳": "3", "۴": "4", "۵": "5", "۶": "6", "۷": "7", "۸": "8", "۹": "9"})


def norm(t):
    """نیم‌فاصله به فاصله، ي/ك عربی به فارسی، ارقام فارسی به لاتین، حروف کوچک برای تطبیق."""
    return re.sub(r"\s+", " ", (t or "").lower().translate(TR)).strip()


def flat(t):
    """برای نمایش: فاصله‌های اضافی و علامت‌های جهت حذف می‌شوند، نیم‌فاصله دست‌نخورده می‌ماند."""
    return re.sub(r"\s+", " ", (t or "").replace("\u200f", "").replace("\u200e", "")).strip()


# ---------- کاتالوگ و تطبیق ----------
AR = "\u0621-\u064A"
WORD_L = f"(?<![{AR}a-z0-9])"
WORD_R = f"(?![{AR}a-z0-9])"


def alias_re(alias):
    return r"\s+".join(re.escape(x) for x in norm(alias).split())


def load_catalog():
    path = os.path.join(HERE, "catalog.json")
    if not os.path.exists(path):
        import build_catalog  # noqa: F401  (فایل را می‌سازد)
    return json.load(open(path, encoding="utf-8"))


def build_matchers(cat):
    """یک regex بزرگ از همهٔ نام‌ها؛ بلندترین نام اول تا «وانت پراید» جای «پراید» را نگیرد."""
    terms = []
    for p in cat["parts"]:
        for a in p.get("aliases", []) + [p["name"]]:
            terms.append((norm(a), "part", p["key"], p["name"]))
    for v in cat["vehicles"]:
        for a in v.get("aliases", []) + [v["name"]]:
            terms.append((norm(a), "vehicle", v["key"], v["name"]))
    brand_aliases = cat.get("brand_aliases", {})
    for b in cat["brands"]:
        for a in [b] + brand_aliases.get(b, []):
            terms.append((norm(a), "brand", norm(b), b))
    uniq = {}
    for a, kind, key, name in terms:
        uniq.setdefault((a, kind), (key, name))
    items = sorted(((a, k, v[0], v[1]) for (a, k), v in uniq.items()), key=lambda x: -len(x[0]))
    groups, term_map = [], {}
    for i, (a, kind, key, name) in enumerate(items):
        name_g = f"t{i}"
        groups.append(f"(?P<{name_g}>{WORD_L}{alias_re(a)}{WORD_R})")
        term_map[name_g] = (kind, key, name)
    return re.compile("|".join(groups)), term_map


def match_terms(rx, term_map, text):
    hits = {"part": {}, "vehicle": {}, "brand": {}}
    for m in rx.finditer(text):
        kind, key, name = term_map[m.lastgroup]
        hits[kind][key] = name
    return hits


# ---------- قیمت ----------
# فقط قیمت‌های صریحِ متن. قیمتی که فروشنده در عکس می‌گذارد خوانده نمی‌شود (در README هم آمده).
PRICE_NUM = (r"(?<![\d/])(\d{1,3}(?:[,/]\d{3})+|\d{1,3}(?:\.\d{3})+"
             r"|\d+(?:[.,]\d+)?)")
PRICE_UNIT = re.compile(PRICE_NUM + r"\s*(میلیون|هزار|ه)?\s*(تومان|تومن|ریال|ت|t)"
                        r"(?=$|[\s,،.؛:)\-])")
PRICE_BARE = re.compile(r"قیمت[^\d]{0,15}" + PRICE_NUM)
# «۲۵۰ه» یعنی ۲۵۰ هزار؛ «۳/۰۰۰/۰۰۰» یا «۱,۰۰۰,۰۰۰» بدون واحد هم قطعاً قیمت است.
PRICE_K = re.compile(PRICE_NUM + r"\s*(ه|هزار)(?=$|[\s,،.؛:)\-])")
PRICE_GROUPED = re.compile(r"(?<![\d/])(\d{1,3}(?:[,/]\d{3}){2,}|\d{1,3}(?:\.\d{3}){2,})(?![\d/])")
PRICE_WORD = re.compile(r"(?<![\w])(یک|دو|سه|چهار|پنج|شش|هفت|هشت|نه|ده)\s*"
                        r"(میلیون|هزار)\s*(تومان|تومن)")
FA_WORDS = {"یک": 1, "دو": 2, "سه": 3, "چهار": 4, "پنج": 5,
            "شش": 6, "هفت": 7, "هشت": 8, "نه": 9, "ده": 10}
# «جمع کل ۱۵۱٫۵۲۰٫۰۰۰ تومان» جمع سبد است، نه قیمت یک قطعه؛ نزدیک‌ترین قطعه هم فقط تصادفی است.
TOTAL_LABEL = re.compile(r"(?<![\w])(جمع\s*کل|جمعا|جمعاً|مجموع|قیمت\s*کل|مبلغ\s*کل|توتال|"
                         r"روی\s*هم|در\s*مجموع|کل\s*مبلغ)(?![\w])")
# «تا سقف ۲۰۰٫۰۰۰٫۰۰۰ ریال» سقف پوشش بیمه است، نه قیمت قطعه.
CAP_LABEL = re.compile(r"(?<![\w])(تا\s*سقف|سقف|بیمه|پوشش|خسارت|غرامت)(?![\w])")


def _amount(raw, mult=1):
    try:
        if re.fullmatch(r"\d{1,3}(?:\.\d{3})+", raw):
            raw = raw.replace(".", "")
        s = re.sub(r"[,/\s]", "", raw)
        return float(s) * mult
    except ValueError:
        return None


def parse_prices(text):
    """[(تومان, start, end)] — ریال به تومان تبدیل می‌شود؛ محدودهٔ معقول قیمت قطعه نگه داشته می‌شود."""
    t = norm(text)
    out = []
    seen = []
    totals = [m.end() for m in TOTAL_LABEL.finditer(t)]
    caps = [m.end() for m in CAP_LABEL.finditer(t)]

    def add(n, a, b, lo=50000):
        if any(0 <= a - e <= 25 for e in totals):
            return
        if any(0 <= a - e <= 30 for e in caps):
            return
        if n is not None and lo <= n <= 500000000:
            out.append((int(n), a, b))
            seen.append((a, b))

    def overlaps(a, b):
        return any(a < se and ss < b for ss, se in seen)

    for m in PRICE_UNIT.finditer(t):
        mult = 1000 if m.group(2) in ("هزار", "ه") else 1000000 if m.group(2) == "میلیون" else 1
        n = _amount(m.group(1), mult)
        if m.group(3) == "ریال" and n is not None:
            n /= 10
        add(n, m.start(), m.end())
    for m in PRICE_K.finditer(t):
        if overlaps(m.start(1), m.end(1)):
            continue
        add(_amount(m.group(1), 1000), m.start(), m.end())
    for m in PRICE_BARE.finditer(t):
        if overlaps(m.start(1), m.end(1)):
            continue
        add(_amount(m.group(1)), m.start(1), m.end(1), lo=100000)
    for m in PRICE_GROUPED.finditer(t):
        if overlaps(m.start(1), m.end(1)):
            continue
        add(_amount(m.group(1)), m.start(1), m.end(1))
    for m in PRICE_WORD.finditer(t):
        add(FA_WORDS[m.group(1)] * (1000000 if m.group(2) == "میلیون" else 1000),
            m.start(), m.end())
    return out


def _dist(s, e, a, b):
    """فاصلهٔ دو بازهٔ متنی؛ صفر یعنی هم‌پوشان."""
    return 0 if (a <= s < b or s <= a < e) else min(abs(s - b), abs(a - e))


def _write_prices(db, ppos, vpos, bpos, brands, pid, channel, kind, ts, text, post_vehicle):
    """هر قیمت به نزدیک‌ترین قطعه (۲۰۰ نویسه) و نزدیک‌ترین برند (۱۲۰ نویسه) در همان پست نسبت می‌شود."""
    if not ppos:
        return

    def pick(pos, s, e, limit):
        """در فهرست‌های قیمت، نام قطعه پیش از عدد می‌آید؛ اگر بود همان اولویت دارد."""
        cands = [p for p in pos if _dist(s, e, p[0], p[1]) <= limit]
        if not cands:
            return None
        before = [p for p in cands if p[1] <= s]
        return min(before or cands, key=lambda p: _dist(s, e, p[0], p[1]))

    for amount, s, e in parse_prices(text):
        near = pick(ppos, s, e, 200)
        if not near:
            continue
        veh = post_vehicle
        if not veh:
            nv = pick(vpos, s, e, 80)
            if nv:
                veh = nv[2]
        brand = ""
        if bpos:
            nb = min(bpos, key=lambda b: _dist(s, e, b[0], b[1]))
            if _dist(s, e, nb[0], nb[1]) <= 120:
                brand = nb[2]
        if not brand and len(brands) == 1:
            brand = next(iter(brands.values()))
        db.execute("INSERT OR IGNORE INTO prices VALUES(?,?,?,?,?,?,?,?)",
                   (pid, near[2], veh, brand, ts, channel, amount, kind))


# ---------- دیتابیس ----------
def open_db(path=None):
    path = path or DB_PATH
    os.makedirs(os.path.dirname(path), exist_ok=True)
    conn = sqlite3.connect(path)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS posts(
        id TEXT PRIMARY KEY, channel TEXT, ts REAL, url TEXT, text TEXT,
        views INTEGER DEFAULT 0, kind TEXT);
    CREATE TABLE IF NOT EXISTS mentions(
        post_id TEXT, part TEXT, vehicle TEXT, ts REAL, channel TEXT, url TEXT,
        views INTEGER DEFAULT 0, cat TEXT, kind TEXT,
        PRIMARY KEY(post_id, part));
    CREATE TABLE IF NOT EXISTS brand_mentions(
        post_id TEXT, part TEXT, brand TEXT, PRIMARY KEY(post_id, part, brand));
    -- هر (قطعه، خودرو) که در یک پست با هم آمده‌اند؛ پست چندخودرویی به همهٔ جفت‌ها شمرده می‌شود.
    CREATE TABLE IF NOT EXISTS pairs(
        post_id TEXT, part TEXT, vehicle TEXT, ts REAL, channel TEXT, kind TEXT, views INTEGER,
        PRIMARY KEY(post_id, part, vehicle));
    CREATE TABLE IF NOT EXISTS runs(
        id INTEGER PRIMARY KEY AUTOINCREMENT, at REAL, days INTEGER, channels INTEGER,
        posts_scanned INTEGER, posts_with_parts INTEGER, new_posts INTEGER,
        oldest REAL, newest REAL);
    -- قیمت‌های صریحِ متن پست (تومان/ریال) که به نزدیک‌ترین قطعه نسبت داده شده‌اند.
    CREATE TABLE IF NOT EXISTS prices(
        post_id TEXT, part TEXT, vehicle TEXT, brand TEXT, ts REAL, channel TEXT,
        amount INTEGER, kind TEXT, PRIMARY KEY(post_id, part, amount));
    -- عکس روزانه از بازدید و تعداد پست هر قطعه؛ اختلاف دو روز = نرخ توجه در آن روز.
    CREATE TABLE IF NOT EXISTS signals(
        day TEXT, part TEXT, posts INTEGER DEFAULT 0, views INTEGER DEFAULT 0,
        PRIMARY KEY(day, part));
    CREATE TABLE IF NOT EXISTS alerts(
        key TEXT PRIMARY KEY, ts REAL, note TEXT);
    -- آخرین ارسال موفق گزارش‌ها؛ مبنای انتخاب حالت اجرا بدون تکیه بر ساعتِ زمان‌بند.
    CREATE TABLE IF NOT EXISTS meta(
        key TEXT PRIMARY KEY, value TEXT);
    CREATE INDEX IF NOT EXISTS idx_mentions_part ON mentions(part, ts);
    CREATE INDEX IF NOT EXISTS idx_mentions_veh ON mentions(vehicle, ts);
    CREATE INDEX IF NOT EXISTS idx_prices_part ON prices(part, ts);
    """)
    return conn


def get_meta(db, key):
    r = db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return r[0] if r else None


def set_meta(db, key, value):
    db.execute("INSERT OR REPLACE INTO meta(key, value) VALUES(?,?)", (key, str(value)))
    db.commit()


def decide_mode(db, now=None):
    """حالت این اجرا از تاریخچهٔ ارسال‌ها، نه از ساعت شروع؛ زمان‌بند GitHub دیر می‌زند و ساعت ۰۴ گم می‌شود."""
    now = now or time.time()
    last_full = float(get_meta(db, "last_full") or 0)
    last_daily = float(get_meta(db, "last_daily") or 0)
    if last_full <= 0:
        return "full"
    f = time.gmtime(last_full)
    n = time.gmtime(now)
    if (f.tm_year, f.tm_mon) != (n.tm_year, n.tm_mon):
        return "full"
    if last_daily <= 0 or now - last_daily >= 20 * 3600:
        return "daily"
    return "alerts"


# ---------- شبکه ----------
# t.me با درخواست‌های پشت‌سرهم از یک IP سریع سخت‌گیر می‌شود (خطای اتصال، نه ۴۲۹).
# یک فاصلهٔ حداقلیِ سراسری بین همهٔ درخواست‌ها + نشستِ هر Thread، خطاها را عملاً حذف می‌کند.
import threading

_tls = threading.local()
_rl_lock = threading.Lock()
_rl_last = [0.0]


def _session():
    s = getattr(_tls, "s", None)
    if s is None:
        s = requests.Session()
        s.headers.update(UA)
        _tls.s = s
    return s


def _throttle(gap=0.9):
    with _rl_lock:
        wait = _rl_last[0] + gap - time.time()
        if wait > 0:
            time.sleep(wait)
        _rl_last[0] = time.time()


def get(url, tries=4):
    last = None
    for i in range(tries):
        _throttle()
        try:
            r = _session().get(url, timeout=30)
            if r.status_code in (429, 503):
                last = Exception(f"http {r.status_code}")
                time.sleep(4 + 6 * i)
                continue
            if r.status_code == 404:
                return r
            r.raise_for_status()
            return r
        except Exception as e:
            last = e
            time.sleep(4 + 8 * i)  # ۴، ۱۲، ۲۰ ثانیه؛ محدودیت IP معمولاً در همین حد رفع می‌شود
    raise last


def iso_ts(s):
    try:
        return calendar.timegm(time.strptime(s[:19], "%Y-%m-%dT%H:%M:%S"))
    except Exception:
        return None


def parse_views(txt):
    s = (txt or "").strip().replace(",", "").replace("٫", ".").upper()
    m = re.match(r"([\d.]+)\s*([KM]?)", s)
    if not m:
        return 0
    n = float(m.group(1))
    return int(n * {"": 1, "K": 1000, "M": 1000000}[m.group(2)])


def parse_page(html):
    """پست‌های صفحهٔ عمومی تلگرام: متن، لینک، زمان، بازدید."""
    soup = BeautifulSoup(html, "html.parser")
    out = []
    for el in soup.select(".tgme_widget_message"):
        if "service_message" in (el.get("class") or []):
            continue
        t = el.select_one(".tgme_widget_message_text")
        if not t:
            continue
        txt = flat(t.get_text(" ", strip=True))
        if len(txt) < 8:
            continue
        a = el.select_one("a.tgme_widget_message_date")
        v = el.select_one(".tgme_widget_message_views")
        tm = el.select_one("time[datetime]")
        out.append((txt, a.get("href", "") if a else "",
                    iso_ts(tm.get("datetime", "")) if tm else None,
                    parse_views(v.get_text() if v else "")))
    return out, ids_of(html)


def ids_of(html):
    return [int(x) for x in re.findall(r'data-post="[^"/]+/(\d+)"', html)]


def fetch_channel(name, cutoff, max_pages, deadline):
    url = f"https://t.me/s/{name}"
    before, items, pages, scanned = None, [], 0, 0
    while pages < max_pages and time.time() < deadline:
        u = url if before is None else f"{url}?before={before}"
        try:
            r = get(u)
        except Exception as e:
            log.warning("%s: %s", name, str(e)[:80])
            break
        if r.status_code != 200:
            break
        page, ids = parse_page(r.text)
        if not page:
            break
        items += [(t, u_, ts, v) for t, u_, ts, v in page]
        scanned += len(page)
        pages += 1
        stamps = [ts for _, _, ts, _ in page if ts]
        if stamps and min(stamps) < cutoff:
            break
        if not ids:
            break
        before = min(ids)
    return name, items, scanned, pages


def load_channels(args):
    """channels.txt = فروشندگان (سیگنال اصلی)؛ news.txt = خبری (زمینه، نه تقاضای مستقیم)."""
    def read(path, kind):
        if not os.path.exists(path):
            return []
        return [(c.strip(), kind) for c in open(path, encoding="utf-8")
                if c.strip() and not c.strip().startswith("#")]
    if args.channels:
        return [(c, "seller") for c in args.channels]
    return read(CHANNELS_FILE, "seller") + ([] if args.no_news else read(NEWS_FILE, "news"))


# ---------- برداشت ----------
def _write_mentions(db, rx, term_map, cat, pid, channel, kind, ts, url, text, views):
    t = norm(text)
    hits = {"part": {}, "vehicle": {}, "brand": {}}
    ppos, vpos, bpos = [], [], []
    for m in rx.finditer(t):
        k, key, name = term_map[m.lastgroup]
        hits[k][key] = name
        if k == "part":
            ppos.append((m.start(), m.end(), name))
        elif k == "vehicle":
            vpos.append((m.start(), m.end(), name))
        else:
            bpos.append((m.start(), m.end(), name))
    parts, vehicles, brands = hits["part"], hits["vehicle"], hits["brand"]
    vehicle = next(iter(vehicles.values())) if len(vehicles) == 1 else ""
    cat_of = {p["key"]: p["cat"] for p in cat["parts"]}
    for pk, pname in parts.items():
        db.execute("INSERT OR IGNORE INTO mentions VALUES(?,?,?,?,?,?,?,?,?)",
                   (pid, pname, vehicle, ts, channel, url, views, cat_of.get(pk, ""), kind))
        for bname in brands.values():
            db.execute("INSERT OR IGNORE INTO brand_mentions VALUES(?,?,?)", (pid, pname, bname))
        for vname in vehicles.values():
            db.execute("INSERT OR IGNORE INTO pairs VALUES(?,?,?,?,?,?,?)",
                       (pid, pname, vname, ts, channel, kind, views))
    _write_prices(db, ppos, vpos, bpos, brands, pid, channel, kind, ts, text, vehicle)
    return parts


def ingest(db, rx, term_map, cat, channel, kind, url, ts, text, views):
    pid = hashlib.md5(f"{channel}|{url}|{text[:80]}".encode()).hexdigest()
    old = db.execute("SELECT length(text), views FROM posts WHERE id=?", (pid,)).fetchone()
    if old:
        # پست تکراری است، ولی بازدید و متنِ کامل‌تر را به‌روز کن
        if views > (old[1] or 0):
            db.execute("UPDATE posts SET views=? WHERE id=?", (views, pid))
            for t in ("mentions", "pairs"):
                db.execute(f"UPDATE {t} SET views=? WHERE post_id=?", (views, pid))
        if len(text) > old[0]:
            db.execute("UPDATE posts SET text=? WHERE id=?", (text[:20000], pid))
            for t in ("mentions", "brand_mentions", "pairs", "prices"):
                db.execute(f"DELETE FROM {t} WHERE post_id=?", (pid,))
            _write_mentions(db, rx, term_map, cat, pid, channel, kind, ts, url, text, views)
        return False
    if not _write_mentions(db, rx, term_map, cat, pid, channel, kind, ts, url, text, views):
        return False
    db.execute("INSERT OR IGNORE INTO posts VALUES(?,?,?,?,?,?,?)",
               (pid, channel, ts, url, text[:20000], views, kind))
    return True


def rebuild(args):
    """بعد از تغییر کاتالوگ، نام‌ها را از متن پست‌های ذخیره‌شده دوباره استخراج می‌کند (بدون شبکه)."""
    cat = load_catalog()
    rx, term_map = build_matchers(cat)
    db = open_db()
    for t in ("mentions", "brand_mentions", "pairs", "prices"):
        db.execute(f"DELETE FROM {t}")
    n = 0
    for pid, channel, kind, ts, url, text, views in db.execute(
            "SELECT id, channel, kind, ts, url, text, views FROM posts"):
        _write_mentions(db, rx, term_map, cat, pid, channel, kind, ts, url, text, views)
        n += 1
    db.commit()
    log.info("بازسازی شد: %d پست", n)


def collect(args):
    cat = load_catalog()
    rx, term_map = build_matchers(cat)
    db = open_db()
    channels = load_channels(args)
    cutoff = time.time() - args.days * 86400
    deadline = time.time() + args.max_runtime
    log.info("برداشت: %d کانال (%d فروشنده، %d خبری) | %d روز | حداکثر %d صفحه/کانال | %d کارگر",
             len(channels), sum(1 for _, k in channels if k == "seller"),
             sum(1 for _, k in channels if k == "news"),
             args.days, args.pages, args.workers)
    scanned = with_parts = new_posts = 0
    oldest = newest = None
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(fetch_channel, c, cutoff, args.pages, deadline): (c, k) for c, k in channels}
        for i, f in enumerate(as_completed(futs), 1):
            ch, kind = futs[f]
            try:
                name, items, sc, pages = f.result()
            except Exception as e:
                log.warning("%s شکست: %s", ch, str(e)[:100])
                continue
            scanned += sc
            added = 0
            for text, url, ts, views in items:
                if ts and ts < cutoff:
                    continue
                if ts:
                    oldest = ts if oldest is None else min(oldest, ts)
                    newest = ts if newest is None else max(newest, ts)
                if ingest(db, rx, term_map, cat, name, kind, url, ts or 0, text, views):
                    added += 1
                    new_posts += 1
            with_parts += added
            db.commit()
            log.info("[%d/%d] %s (%s): %d پست، %d صفحه، %d تازه",
                     i, len(channels), name, kind, sc, pages, added)
    db.execute("INSERT INTO runs(at,days,channels,posts_scanned,posts_with_parts,new_posts,oldest,newest)"
               " VALUES(?,?,?,?,?,?,?,?)",
               (time.time(), args.days, len(channels), scanned, with_parts, new_posts, oldest, newest))
    db.commit()
    log.info("پایان در %.0f ثانیه: %d پست خوانده شد، %d پست نام قطعه داشت، %d تازه",
             time.time() - t0, scanned, with_parts, new_posts)
    return db


# ---------- گزارش ----------
def fmt_ts(ts):
    return time.strftime("%Y-%m-%d", time.gmtime(ts)) if ts else "—"


def fa_num(n):
    try:
        return f"{int(round(n)):,}".replace(",", "٬").translate(FA_DIGITS)
    except (TypeError, ValueError):
        return "—"


def fa_pct(v):
    if v is None:
        return "—"
    return ("▲" if v > 0 else "▼" if v < 0 else "■") + fa_num(abs(v)) + "٪"


# ---------- سیگنال بازار ----------
def price_board(db, span_days=120):
    """آخرین قیمت ثبت‌شدهٔ هر قطعه، تغییر نسبت به قیمت قبلی و نسبت به ۲۴ ساعت قبل."""
    now = time.time()
    rows = db.execute("""SELECT part, vehicle, brand, ts, amount, channel FROM prices
                         WHERE kind='seller' AND ts>=? ORDER BY ts""",
                      (now - span_days * 86400,)).fetchall()
    by = {}
    for part, veh, brand, ts, amount, ch in rows:
        by.setdefault(part, []).append({"ts": ts, "amount": amount, "vehicle": veh or "",
                                        "brand": brand or "", "channel": ch})
    demand = dict(db.execute("""SELECT part, COUNT(DISTINCT post_id) FROM mentions
                                WHERE kind='seller' AND ts>=? GROUP BY part""",
                             (now - 7 * 86400,)).fetchall())
    board = []
    for part, obs in by.items():
        # یک قیمت در روز برای هر خودرو (میانه) تا چند قیمتِ یک لیست، «تغییر» جعلی نسازد.
        daily = {}
        for o in obs:
            daily.setdefault((o["vehicle"], int(o["ts"] // 86400)), []).append(o)
        vehs = {}
        for (veh, day), lst in daily.items():
            lst.sort(key=lambda x: x["ts"])
            med = int(statistics.median(x["amount"] for x in lst))
            vehs.setdefault(veh, []).append({"day": day, "amount": med, "ts": lst[-1]["ts"],
                                             "brand": lst[-1]["brand"]})
        veh = max(vehs, key=lambda k: vehs[k][-1]["ts"])
        seq = sorted(vehs[veh], key=lambda x: x["day"])
        last = seq[-1]
        prev = seq[-2] if len(seq) > 1 else None
        chg = None
        if prev and prev["amount"]:
            chg = (last["amount"] - prev["amount"]) / prev["amount"] * 100
            if abs(chg) > 60:  # جابه‌جایی مدل/برند یا نادرست‌خواندن؛ سیگنال نیست
                chg = None
        day_chg = None
        if prev and last["day"] - prev["day"] == 1 and prev["amount"]:
            day_chg = (last["amount"] - prev["amount"]) / prev["amount"] * 100
        win = [x["amount"] for x in seq if x["day"] >= int((now - 30 * 86400) // 86400)] or [x["amount"] for x in seq]
        board.append({"part": part, "vehicle": veh, "brand": last["brand"],
                      "last": last["amount"], "last_ts": last["ts"],
                      "prev": prev["amount"] if prev else None,
                      "prev_ts": prev["ts"] if prev else None, "chg": chg, "day": day_chg,
                      "lo": min(win), "hi": max(win), "med": statistics.median(win),
                      "n": len(obs), "demand": demand.get(part, 0)})
    board.sort(key=lambda r: (-r["demand"], -r["last_ts"]))
    return board, demand


def _window_counts(db, sql, days):
    now = time.time()
    a = now - days * 86400
    b = a - days * 86400
    rows = db.execute(sql, (a, a, b)).fetchall()
    out = []
    for name, cu, pr in rows:
        pct = (cu - pr) / pr * 100 if pr else (100 if cu else 0)
        state = "داده کم" if cu + pr < 3 else ("صعودی" if pct >= 15 else "نزولی" if pct <= -15 else "ثابت")
        out.append({"name": name, "cur": cu, "prev": pr, "pct": pct, "state": state})
    out.sort(key=lambda r: (-r["cur"], r["name"]))
    return out


def market_moves(db, days=7):
    """قطعه‌ها: هفت روز اخیر در برابر هفت روز قبل از آن."""
    return _window_counts(db, """
        SELECT part,
          COUNT(DISTINCT CASE WHEN ts>=? THEN post_id END),
          COUNT(DISTINCT CASE WHEN ts<? THEN post_id END)
        FROM mentions WHERE kind='seller' AND ts>=? GROUP BY part""", days)


def combo_moves(db, days=7):
    return _window_counts(db, """
        SELECT part || '×' || vehicle,
          COUNT(DISTINCT CASE WHEN ts>=? THEN post_id END),
          COUNT(DISTINCT CASE WHEN ts<? THEN post_id END)
        FROM pairs WHERE kind='seller' AND ts>=? GROUP BY part, vehicle""", days)


def brand_moves(db, days=7):
    return _window_counts(db, """
        SELECT b.brand,
          COUNT(DISTINCT CASE WHEN p.ts>=? THEN b.post_id END),
          COUNT(DISTINCT CASE WHEN p.ts<? THEN b.post_id END)
        FROM brand_mentions b JOIN posts p ON p.id=b.post_id
        WHERE p.kind='seller' AND p.ts>=? GROUP BY b.brand""", days)


def take_snapshot(db):
    """عکس روزانه از بازدید تجمعی و تعداد پست هر قطعه؛ اختلاف دو روز = نرخ توجه."""
    day = fmt_ts(time.time())
    rows = db.execute("""SELECT part, COUNT(DISTINCT post_id), SUM(views)
                         FROM mentions WHERE kind='seller' GROUP BY part""").fetchall()
    for part, posts, views in rows:
        db.execute("""INSERT INTO signals(day, part, posts, views) VALUES(?,?,?,?)
                      ON CONFLICT(day, part) DO UPDATE SET
                        posts=MAX(posts, excluded.posts), views=MAX(views, excluded.views)""",
                   (day, part, posts or 0, views or 0))
    db.commit()


def attention_rates(db):
    """آخرین رشد بازدید هر قطعه و پایهٔ روزهای قبل (فقط وقتی حداقل دو روز عکس داریم)."""
    days = [d for (d,) in db.execute("SELECT DISTINCT day FROM signals ORDER BY day DESC LIMIT 8")]
    if len(days) < 2:
        return {}
    by = {}
    for day, part, views in db.execute("SELECT day, part, views FROM signals WHERE day>=?",
                                       (min(days),)).fetchall():
        by.setdefault(part, []).append((day, views))
    rates = {}
    for part, seq in by.items():
        seq.sort()
        if len(seq) < 2:
            continue
        deltas = [seq[i][1] - seq[i - 1][1] for i in range(1, len(seq))]
        last = deltas[-1]
        base = sum(deltas[:-1]) / len(deltas[:-1]) if len(deltas) > 1 else 0
        rates[part] = {"views_delta": last, "views_base": base}
    return rates


def detect_alerts(db):
    """مواردی که در ۲۴ ساعت اخیر از پایهٔ خودشان معنادار بالاتر رفته‌اند (بدون علامت‌زدن)."""
    now = time.time()
    cur = dict(db.execute("""SELECT part, COUNT(DISTINCT post_id) FROM mentions
                             WHERE kind='seller' AND ts>=? GROUP BY part""",
                          (now - 86400,)).fetchall())
    base_rows = db.execute("""SELECT part, COUNT(DISTINCT post_id) FROM mentions
                              WHERE kind='seller' AND ts>=? AND ts<? GROUP BY part""",
                           (now - 15 * 86400, now - 86400)).fetchall()
    base = {p: c / 14.0 for p, c in base_rows}
    rates = attention_rates(db)
    board, _ = price_board(db)
    day = fmt_ts(now)
    items = []
    for part, c in cur.items():
        b = base.get(part, 0.0)
        if c >= 3 and c >= max(2 * b, 2.5):
            items.append({"part": part, "kind": "حجم پست", "key": f"{day}|{part}|posts",
                          "line": f"• {part}: {fa_num(c)} پست در ۲۴ ساعت "
                                  f"(پایهٔ روزانه: {fa_num(max(b, 1))})"})
        r = rates.get(part)
        if r and r["views_delta"] >= 300 and r["views_delta"] >= 2 * r["views_base"]:
            items.append({"part": part, "kind": "بازدید", "key": f"{day}|{part}|views",
                          "line": f"• {part}: بازدید +{fa_num(r['views_delta'])} در ۲۴ ساعت "
                                  f"(پایه: {fa_num(r['views_base'])})"})
    for row in board:
        if (row["demand"] >= 2 and row["chg"] is not None and abs(row["chg"]) >= 8
                and row["last_ts"] >= now - 3 * 86400):
            items.append({"part": row["part"], "kind": "قیمت", "key": f"{day}|{row['part']}|price",
                          "line": f"• {row['part']}: قیمت {fa_pct(row['chg'])} "
                                  f"({fa_num(row['prev'])} → {fa_num(row['last'])} تومان)"})
    return [i for i in items
            if not db.execute("SELECT 1 FROM alerts WHERE key=?", (i["key"],)).fetchone()]


def management_summary(db, moves, combos, board, brands):
    """چند جملهٔ تصمیم‌محور از همان اعداد گزارش؛ بدون ادعای فروش یا کلیک که اندازه‌گیری نشده."""
    lines = []
    rising = [m for m in moves if m["state"] == "صعودی" and m["cur"] >= 2][:3]
    falling = [m for m in moves if m["state"] == "نزولی" and m["prev"] >= 2][:2]
    if rising:
        lines.append("روند ۷ روزه: " + "، ".join(f"{m['name']} ({fa_num(m['cur'])} پست)" for m in rising)
                     + " بیشترین رشد را داشتند.")
    if falling:
        lines.append("افت نسبی: " + "، ".join(f"{m['name']} ({fa_pct(m['pct'])})" for m in falling) + ".")
    pm = [r for r in board if r["chg"] is not None and r["demand"] >= 2
          and r["last_ts"] >= time.time() - 30 * 86400]
    pm.sort(key=lambda r: -abs(r["chg"]))
    if pm:
        r = pm[0]
        lines.append(f"قیمت: {r['part']} {fa_pct(r['chg'])} "
                     f"({fa_num(r['prev'])} → {fa_num(r['last'])} تومان، "
                     f"{fmt_ts(r['prev_ts'])} تا {fmt_ts(r['last_ts'])}).")
    opp = [c for c in combos if c["state"] == "صعودی" and c["cur"] >= 2][:3]
    if opp:
        lines.append("موجودی: " + "، ".join(f"{c['name']} ({fa_num(c['cur'])} پست)" for c in opp)
                     + " را در اولویت تأمین بگذارید.")
    if brands:
        lines.append("برندها: " + "، ".join(f"{b['name']} ({fa_num(b['cur'])} پست)"
                                          for b in brands[:4]) + ".")
    since7 = time.time() - 7 * 86400
    nobs = db.execute("SELECT COUNT(*) FROM prices WHERE kind='seller' AND ts>=?", (since7,)).fetchone()[0]
    nposts = db.execute("SELECT COUNT(DISTINCT post_id) FROM mentions WHERE kind='seller' AND ts>=?",
                        (since7,)).fetchone()[0]
    nparts = db.execute("SELECT COUNT(DISTINCT part) FROM mentions WHERE kind='seller' AND ts>=?",
                        (since7,)).fetchone()[0]
    nbranded = db.execute("""SELECT COUNT(DISTINCT b.part) FROM brand_mentions b
                             JOIN posts p ON p.id=b.post_id
                             WHERE p.kind='seller' AND p.ts>=?""", (since7,)).fetchone()[0]
    if nparts:
        lines.append(f"پوشش برند: {fa_num(nbranded)} از {fa_num(nparts)} قطعهٔ ۷ روز برند مشخص دارند "
                     f"({fa_num(round(nbranded * 100 / nparts))}٪).")
    if nposts:
        lines.append(f"پوشش قیمت: {fa_num(nobs)} قیمت صریح در ۷ روز از {fa_num(nposts)} پست دارای قطعه "
                     f"({fa_num(round(nobs * 100 / nposts))}٪) — بقیهٔ قیمت‌ها در عکس یا سؤال‌محور است.")
    return lines[:6]


def build_report(db, top=500):
    now = time.time()
    yr = now - 365 * 86400
    d90 = now - 90 * 86400
    part_rows = db.execute("""
        SELECT part,
               COUNT(DISTINCT CASE WHEN kind='seller' THEN post_id END),
               COUNT(DISTINCT CASE WHEN kind='seller' AND ts>=? THEN post_id END),
               COUNT(DISTINCT CASE WHEN kind='news' THEN post_id END),
               COUNT(DISTINCT CASE WHEN kind='seller' THEN channel END),
               COUNT(DISTINCT CASE WHEN kind='news' THEN channel END),
               MIN(ts), MAX(ts),
               SUM(CASE WHEN kind='seller' THEN views ELSE 0 END),
               MAX(cat)
        FROM mentions WHERE ts>=? GROUP BY part""", (d90, yr)).fetchall()
    part_stats = {r[0]: r for r in part_rows}
    combo_rows = db.execute("""
        SELECT part, vehicle,
               COUNT(DISTINCT CASE WHEN kind='seller' THEN post_id END),
               COUNT(DISTINCT CASE WHEN kind='seller' AND ts>=? THEN post_id END),
               COUNT(DISTINCT CASE WHEN kind='news' THEN post_id END),
               COUNT(DISTINCT CASE WHEN kind='seller' THEN channel END),
               MIN(ts), MAX(ts),
               SUM(CASE WHEN kind='seller' THEN views ELSE 0 END)
        FROM pairs WHERE ts>=? GROUP BY part, vehicle""", (d90, yr)).fetchall()
    combo_stats = {(r[0], r[1]): r for r in combo_rows}
    brand_rows = db.execute("""
        SELECT b.part, b.brand, COUNT(DISTINCT b.post_id) c
        FROM brand_mentions b JOIN mentions m ON m.post_id=b.post_id AND m.part=b.part
        WHERE m.kind='seller'
        GROUP BY b.part, b.brand ORDER BY c DESC""").fetchall()
    brands_by_part = {}
    for p, b, c in brand_rows:
        brands_by_part.setdefault(p, []).append(f"{b} ({c})")
    combo_brand_rows = db.execute("""
        SELECT p.part, p.vehicle, b.brand, COUNT(DISTINCT b.post_id) c
        FROM brand_mentions b JOIN pairs p ON p.post_id=b.post_id AND p.part=b.part
        WHERE p.kind='seller' AND p.ts>=?
        GROUP BY p.part, p.vehicle, b.brand ORDER BY c DESC""", (yr,)).fetchall()
    combo_brands = {}
    for p, v, b, c in combo_brand_rows:
        combo_brands.setdefault((p, v), []).append(f"{b} ({c})")
    brand_totals = db.execute("""
        SELECT b.brand, COUNT(DISTINCT b.post_id), COUNT(DISTINCT b.part),
               GROUP_CONCAT(DISTINCT b.part)
        FROM brand_mentions b JOIN posts p ON p.id=b.post_id
        WHERE p.kind='seller' AND p.ts>=?
        GROUP BY b.brand""", (yr,)).fetchall()
    brand_views = dict(db.execute("""
        SELECT brand, SUM(views) FROM (
          SELECT DISTINCT b.brand brand, p.id, p.views
          FROM brand_mentions b JOIN posts p ON p.id=b.post_id
          WHERE p.kind='seller' AND p.ts>=?
        ) GROUP BY brand""", (yr,)).fetchall())
    sample = dict(db.execute("""
        SELECT part, url FROM mentions WHERE url!='' AND kind='seller'
        GROUP BY part ORDER BY MAX(views) DESC""").fetchall())
    coverage = db.execute("""
        SELECT COUNT(*), COUNT(DISTINCT channel), MIN(ts), MAX(ts),
               SUM(CASE WHEN kind='seller' THEN 1 ELSE 0 END),
               SUM(CASE WHEN kind='news' THEN 1 ELSE 0 END),
               (SELECT SUM(posts_scanned) FROM runs) FROM posts""").fetchone()
    return {"parts": part_stats, "combos": combo_stats, "brands": brands_by_part,
            "combo_brands": combo_brands, "brand_totals": brand_totals, "brand_views": brand_views,
            "sample": sample, "coverage": coverage, "yr": yr, "d90": d90, "top": top}


def write_csv(path, header, rows):
    import csv
    with open(path, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)


def find_chrome():
    import shutil as _sh
    for c in (os.environ.get("CHROME_BIN"),
              "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
              _sh.which("google-chrome"), _sh.which("google-chrome-stable"),
              _sh.which("chromium"), _sh.which("chromium-browser"),
              "/usr/bin/google-chrome", "/usr/bin/chromium"):
        if c and os.path.exists(c):
            return c
    return None


def make_pdf(html_path, pdf_path):
    """HTML را با Chrome بی‌سر به PDF تبدیل می‌کند؛ بدون وابستگی پایتونی و با فونت‌های سیستم."""
    chrome = find_chrome()
    if not chrome:
        log.warning("Chrome/Chromium پیدا نشد؛ PDF ساخته نشد (HTML موجود است)")
        return False
    if os.path.exists(pdf_path):
        os.remove(pdf_path)
    url = "file://" + quote(os.path.abspath(html_path))
    for mode in ("--headless=new", "--headless"):
        cmd = [chrome, mode, "--disable-gpu", "--no-sandbox", "--disable-dev-shm-usage",
               "--no-pdf-header-footer", "--print-to-pdf-no-header",
               "--virtual-time-budget=3000", f"--print-to-pdf={pdf_path}", url]
        try:
            r = subprocess.run(cmd, capture_output=True, timeout=240)
        except Exception as e:
            log.warning("اجرای Chrome برای PDF شکست: %s", e)
            continue
        if os.path.exists(pdf_path) and os.path.getsize(pdf_path) > 1000:
            return True
        log.warning("PDF با %s ساخته نشد: %s", mode, (r.stderr or b"")[-200:].decode(errors="ignore"))
    return False


def daily_report(db, hours=48):
    """تصویر کوتاه بازار در بازهٔ اخیر. ۴۸ ساعت (نه ۲۴) تا یک نوبتِ عقب‌افتادهٔ زمان‌بند داده را از دست ندهد."""
    since = time.time() - hours * 3600
    parts = db.execute("""
        SELECT m.part, COUNT(DISTINCT m.post_id), COUNT(DISTINCT m.channel), SUM(m.views)
        FROM mentions m WHERE m.kind='seller' AND m.ts>=?
        GROUP BY m.part ORDER BY 2 DESC""", (since,)).fetchall()
    combos = db.execute("""
        SELECT part, vehicle, COUNT(DISTINCT post_id), SUM(views)
        FROM pairs WHERE kind='seller' AND ts>=?
        GROUP BY part, vehicle ORDER BY 3 DESC""", (since,)).fetchall()
    bparts = {}
    for p, b, c in db.execute("""
        SELECT b.part, b.brand, COUNT(DISTINCT b.post_id)
        FROM brand_mentions b JOIN posts p ON p.id=b.post_id
        WHERE p.kind='seller' AND p.ts>=? GROUP BY 1,2 ORDER BY 3 DESC""", (since,)).fetchall():
        bparts.setdefault(p, []).append(f"{b} ({c})")
    brands = db.execute("""
        SELECT brand, COUNT(DISTINCT post_id) FROM brand_mentions b
        JOIN posts p ON p.id=b.post_id WHERE p.kind='seller' AND p.ts>=?
        GROUP BY brand ORDER BY 2 DESC""", (since,)).fetchall()
    hit_posts, hit_ch = db.execute("""
        SELECT COUNT(DISTINCT post_id), COUNT(DISTINCT channel) FROM mentions
        WHERE kind='seller' AND ts>=?""", (since,)).fetchone()
    posts, channels = db.execute("""
        SELECT COUNT(*), COUNT(DISTINCT channel) FROM posts
        WHERE kind='seller' AND ts>=?""", (since,)).fetchone()
    samples = db.execute("""
        SELECT part, url, MAX(views) v FROM mentions
        WHERE kind='seller' AND ts>=? AND url!=''
        GROUP BY url ORDER BY v DESC LIMIT 12""", (since,)).fetchall()
    board, _ = price_board(db)
    moves = market_moves(db)
    combos_mv = combo_moves(db)
    brands_mv = brand_moves(db)
    mgmt = management_summary(db, moves, combos_mv, board, brands_mv)
    fresh = time.time() - 30 * 86400
    pmoves = [r for r in board if r["chg"] is not None and r["demand"] >= 1 and r["last_ts"] >= fresh]
    pmoves.sort(key=lambda r: -abs(r["chg"]))
    demand7 = dict(db.execute("""SELECT part, COUNT(DISTINCT post_id) FROM mentions
                                 WHERE kind='seller' AND ts>=? GROUP BY part""",
                              (time.time() - 7 * 86400,)).fetchall())
    price_obs = db.execute("SELECT COUNT(*) FROM prices WHERE kind='seller' AND ts>=?",
                           (since,)).fetchone()[0]
    branded = db.execute("""SELECT COUNT(DISTINCT b.part) FROM brand_mentions b
                            JOIN posts p ON p.id=b.post_id
                            WHERE p.kind='seller' AND p.ts>=?""", (since,)).fetchone()[0]
    return {"hours": hours, "since": since, "parts": parts, "combos": combos, "branded": branded,
            "bparts": bparts, "brands": brands, "hit_posts": hit_posts or 0,
            "posts": posts or 0, "channels": channels or 0, "samples": samples,
            "board": board, "moves": moves, "combos_mv": combos_mv, "brands_mv": brands_mv,
            "mgmt": mgmt, "pmoves": pmoves[:5], "price_obs": price_obs, "demand7": demand7}


def build_daily_html(path, d):
    E = html.escape
    fa = lambda x: str(x).translate(FA_DIGITS)
    since = fmt_ts(d["since"])

    def table(headers, rows):
        h = "".join(f"<th>{E(str(x))}</th>" for x in headers)
        body = "".join("<tr>" + "".join(f"<td>{E(str(c))}</td>" for c in row) + "</tr>" for row in rows)
        return f"<table><thead><tr>{h}</tr></thead><tbody>{body}</tbody></table>"

    views = sum((p[3] or 0) for p in d["parts"])
    cards = [("پست با نام قطعه", d["hit_posts"]), ("پست فروشنده", d["posts"]),
             ("کانال", d["channels"]), ("بازدید", views),
             ("قطعه", len(d["parts"])), ("قطعه با برند", d.get("branded", 0)),
             ("ترکیب", len(d["combos"])), ("برند", len(d["brands"])),
             ("قیمت صریح", d["price_obs"])]
    cards_html = "".join(f'<div class="card"><div class="k">{E(k)}</div><div class="v">{E(fa_num(v))}</div></div>'
                         for k, v in cards)
    mgmt_html = "".join(f"<li>{E(x)}</li>" for x in d["mgmt"]) or "<li>سیگنال روشنی در این بازه نبود.</li>"
    move_rows = [[m["name"], fa_num(m["cur"]), fa_num(m["prev"]), fa_pct(m["pct"]), m["state"]]
                 for m in d["moves"][:14]]
    price_rows = []
    recent = {b["part"]: b for b in d["board"]
              if b["demand"] > 0 and b["last_ts"] >= time.time() - 60 * 86400}
    demand7 = d.get("demand7") or {}
    # ترتیب جدول را تقاضای ۷ روز می‌دهد؛ قلم پرتقاضای بدون قیمت متنی هم ردیف «—» می‌گیرد.
    for part, n in sorted(demand7.items(), key=lambda x: -x[1])[:24]:
        r = recent.get(part)
        if r:
            rng = (f'{fa_num(r["lo"])}–{fa_num(r["hi"])} (میانه {fa_num(r["med"])})'
                   if r["lo"] != r["hi"] else "—")
            price_rows.append([r["part"], r["vehicle"] or "—", r["brand"] or "—",
                               fa_num(r["last"]), fmt_ts(r["last_ts"]), fa_pct(r["day"]),
                               fa_pct(r["chg"]) if r["chg"] is not None else "—", rng,
                               fa_num(n)])
        else:
            price_rows.append([part, "—", "—", "—", "—", "—", "—", "—", fa_num(n)])
    for part, r in recent.items():
        if len(price_rows) >= 24:
            break
        if part in demand7:
            continue
        rng = (f'{fa_num(r["lo"])}–{fa_num(r["hi"])} (میانه {fa_num(r["med"])})'
               if r["lo"] != r["hi"] else "—")
        price_rows.append([part, r["vehicle"] or "—", r["brand"] or "—",
                           fa_num(r["last"]), fmt_ts(r["last_ts"]), fa_pct(r["day"]),
                           fa_pct(r["chg"]) if r["chg"] is not None else "—", rng,
                           fa_num(r["demand"])])
    part_rows = [[fa(i), p[0], fa_num(p[1]), fa_num(p[2]), fa_num(p[3] or 0),
                  "، ".join(d["bparts"].get(p[0], [])[:4]) or "—"]
                 for i, p in enumerate(d["parts"][:20], 1)]
    combo_rows = [[fa(i), c[0], c[1], fa_num(c[2]), fa_num(c[3] or 0)]
                  for i, c in enumerate(d["combos"][:15], 1)]
    brand_rows = [[b, fa_num(n)] for b, n in d["brands"]]
    sample_rows = [[s[0], s[1], fa_num(s[2] or 0)] for s in d["samples"]]

    price_block = (table(["قطعه", "خودرو", "برند", "آخرین قیمت (تومان)", "تاریخ", "تغییر ۲۴ساعته",
                          "تغییر نسبت به قیمت قبلی", "کمینه–بیشینه (میانه)", "پست ۷ روز"], price_rows)
                   if price_rows else "<p>در متن پست‌های این بخش قیمت صریحی ثبت نشده است.</p>")

    doc = f"""<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">
<title>گزارش روزانهٔ بازار قطعات</title>
<style>
@page {{ size: A4; margin: 12mm 9mm; }}
body {{ font-family: Tahoma, "DejaVu Sans", "Noto Naskh Arabic", sans-serif; color:#111827;
        font-size: 10px; line-height: 1.6; }}
h1 {{ font-size: 18px; margin: 0 0 2px; }}
h2 {{ font-size: 13px; margin: 14px 0 6px; padding-bottom: 3px; border-bottom: 2px solid #0f766e;
      color:#0f766e; page-break-after: avoid; }}
.sub {{ color:#4b5563; font-size: 10px; margin-bottom: 8px; }}
.cards {{ display: flex; flex-wrap: wrap; gap: 5px; margin: 8px 0 4px; }}
.card {{ border:1px solid #d1d5db; border-radius: 5px; padding: 4px 8px; min-width: 95px;
         background:#f8fafc; }}
.card .k {{ color:#6b7280; font-size: 8.5px; }}
.card .v {{ font-weight: bold; font-size: 13px; color:#0f766e; }}
.mgmt {{ background:#f0fdfa; border:1px solid #99f6e4; border-radius:6px; padding:6px 10px; margin:8px 0; }}
.mgmt ul {{ margin: 0; padding-right: 16px; }}
.mgmt li {{ margin: 2px 0; }}
table {{ width: 100%; border-collapse: collapse; margin: 4px 0 10px; font-size: 8.5px; }}
thead {{ display: table-header-group; }}
th, td {{ border: 1px solid #d1d5db; padding: 2px 4px; text-align: right; vertical-align: top; }}
th {{ background: #e5e7eb; }}
tbody tr:nth-child(even) {{ background: transparent; }}
tr {{ page-break-inside: avoid; }}
.url {{ direction: ltr; text-align: left; font-size: 7.5px; word-break: break-all; }}
.footer {{ margin-top: 12px; border-top:1px solid #d1d5db; padding-top:4px; color:#6b7280; font-size: 8px; }}
</style></head><body>
<h1>گزارش روزانه و خلاصهٔ مدیریتی بازار قطعات</h1>
<div class="sub">بازه: {E(fa(d['hours']))} ساعت اخیر (از <span dir="ltr">{E(since)}</span>) — تولید: <span dir="ltr">{E(fmt_ts(time.time()))}</span></div>
<div class="cards">{cards_html}</div>

<h2>خلاصهٔ مدیریتی</h2>
<div class="mgmt"><ul>{mgmt_html}</ul></div>

<h2>جهت بازار — ۷ روز اخیر در برابر ۷ روز قبل</h2>
{table(["قطعه", "این هفته", "هفتهٔ قبل", "تغییر", "وضعیت"], move_rows)}

<h2>قیمت اقلام پرتقاضا</h2>
{price_block}

<h2>قطعه‌های پرتکرار این بازه</h2>
{table(["#", "قطعه", "پست", "کانال", "بازدید", "برندهای دیده‌شده"], part_rows)}

<h2>ترکیب‌های پرتکرار قطعه×خودرو</h2>
{table(["#", "قطعه", "خودرو", "پست", "بازدید"], combo_rows)}

<h2>برندها</h2>
{table(["برند", "پست"], brand_rows)}

<h2>نمونه پست‌ها برای بازبینی</h2>
{table(["قطعه", "لینک", "بازدید"], sample_rows)}

<div class="footer">پروژهٔ parts-demand — «تغییر ۲۴ساعته» فقط وقتی پر است که قیمت دیروز و امروز هر دو در متن پست ثبت شده باشد؛
«تغییر قبلی» نسبت به آخرین قیمت پیش از آن است. ردیف‌هایی که ستون قیمتشان «—» است جزو اقلام پرتقاضا هستند
ولی قیمت صریح در متن پستشان نبوده. قیمت‌های داخل عکس خوانده نمی‌شوند. گزارش تاریخی یک‌ساله در report.pdf.</div>
</body></html>"""
    open(path, "w", encoding="utf-8").write(doc)
    return path


def build_prices_html(path, board, since_ts, demand_parts=()):
    E = html.escape
    cutoff = time.time() - 60 * 86400
    fresh = {b["part"]: b for b in board if b["last_ts"] >= cutoff}
    dm = dict(demand_parts)
    movers = [b for b in fresh.values() if b["demand"] > 0 and b["chg"] is not None]
    movers.sort(key=lambda b: -abs(b["chg"]))
    movers_html = "".join(
        f"<li>{E(b['part'])} ({E(b['vehicle'] or 'بدون خودرو')}): {fa_pct(b['chg'])} — "
        f"{fa_num(b['prev'])} → {fa_num(b['last'])} تومان "
        f"(<span dir=\"ltr\">{E(fmt_ts(b['prev_ts']))}</span> → <span dir=\"ltr\">{E(fmt_ts(b['last_ts']))}</span>)</li>"
        for b in movers[:8]) or "<li>قیمت تکراری برای مقایسه ثبت نشده است.</li>"
    # همهٔ قلم‌های پرتقاضا ردیف می‌گیرند؛ قیمت کهنه یا متنی‌نشده با «—» می‌آید.
    entries = []
    for part in set(dm) | set(fresh):
        b = fresh.get(part)
        n = max(dm.get(part, 0), b["demand"] if b else 0)
        if b or part in dm:
            entries.append((n, part, b))
    entries.sort(key=lambda x: (-x[0], x[1]))
    table_rows = []
    for n, part, b in entries[:40]:
        if b:
            table_rows.append([part, b["vehicle"] or "—", b["brand"] or "—",
                               fa_num(b["last"]), fmt_ts(b["last_ts"]),
                               fa_pct(b["day"]), fa_pct(b["chg"]) if b["chg"] is not None else "—",
                               f'{fa_num(b["lo"])}–{fa_num(b["hi"])}', fa_num(b["med"]),
                               fa_num(n), fa_num(b["n"])])
        else:
            table_rows.append([part, "—", "—", "—", "—", "—", "—", "—", "—", fa_num(n), "۰"])
    body = "".join("<tr>" + "".join(f"<td>{c}</td>" for c in r) + "</tr>" for r in table_rows)
    head = "".join(f"<th>{E(h)}</th>" for h in
                   ["قطعه", "خودرو", "برند", "آخرین قیمت (تومان)", "تاریخ", "تغییر ۲۴ساعته",
                    "تغییر قبلی", "بازهٔ ۳۰ روز", "میانه", "پست ۷ روز", "دفعات ثبت"])
    doc = f"""<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">
<title>قیمت روزانهٔ اقلام پرفروش</title>
<style>
@page {{ size: A4; margin: 12mm 9mm; }}
body {{ font-family: Tahoma, "DejaVu Sans", "Noto Naskh Arabic", sans-serif; color:#111827;
        font-size: 10px; line-height: 1.6; }}
h1 {{ font-size: 18px; margin: 0 0 2px; }}
h2 {{ font-size: 13px; margin: 14px 0 6px; padding-bottom: 3px; border-bottom: 2px solid #b45309;
      color:#b45309; }}
.sub {{ color:#4b5563; font-size: 10px; margin-bottom: 8px; }}
.box {{ background:#fffbeb; border:1px solid #fde68a; border-radius:6px; padding:6px 10px; margin:8px 0; }}
.box ul {{ margin: 0; padding-right: 16px; }}
table {{ width: 100%; border-collapse: collapse; margin: 4px 0 10px; font-size: 8px; }}
thead {{ display: table-header-group; }}
th, td {{ border: 1px solid #d1d5db; padding: 2px 4px; text-align: right; vertical-align: top; }}
th {{ background: #fef3c7; }}
tbody tr:nth-child(even) {{ background: transparent; }}
tr {{ page-break-inside: avoid; }}
.footer {{ margin-top: 12px; border-top:1px solid #d1d5db; padding-top:4px; color:#6b7280; font-size: 8px; }}
</style></head><body>
<h1>قیمت روزانهٔ اقلام پرفروش</h1>
<div class="sub">آخرین قیمت هر قطعه تا <span dir="ltr">{E(fmt_ts(time.time()))}</span> — مبنای داده: قیمت‌های صریحِ متن پست‌های فروشندگان</div>

<h2>بیشترین حرکت قیمت (نسبت به قیمت قبلی)</h2>
<div class="box"><ul>{movers_html}</ul></div>

<h2>جدول قیمت — مرتب بر تقاضای ۷ روز</h2>
<table><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>

<div class="footer">«تغییر ۲۴ساعته» فقط وقتی پر است که قیمت دیروز و امروز هر دو در متن پست ثبت شده باشد؛
«تغییر قبلی» نسبت به آخرین قیمت پیش از آن است. یک پست چندقطعه‌ای قیمتش به نزدیک‌ترین قطعه نسبت داده می‌شود.
ردیف‌هایی که قیمتشان «—» است جزو اقلام پرتقاضای ۷ روزند ولی قیمت صریح در متن پستشان نبوده.
قیمت‌های داخل عکس، فایل PDF یا سؤال‌محور خوانده نمی‌شوند؛ پوشش واقعی در گزارش روزانه ذکر می‌شود.</div>
</body></html>"""
    open(path, "w", encoding="utf-8").write(doc)
    return path


def build_html(path, summary, top_parts, top_combos, parts, combos, brands, prepared, hints, board=()):
    E = html.escape
    fa = lambda x: str(x).translate(FA_DIGITS)

    def table(headers, rows, cls=""):
        h = "".join(f"<th>{E(str(x))}</th>" for x in headers)
        body = "".join("<tr>" + "".join(f"<td>{E(str(c))}</td>" for c in row) + "</tr>" for row in rows)
        return f'<table class="{cls}"><thead><tr>{h}</tr></thead><tbody>{body}</tbody></table>'

    def hint(cat):
        return "، ".join(hints.get(cat, [])) or "—"

    cards = [
        ("پست فروشنده با نام قطعه", summary["posts_seller"]),
        ("پست خبری", summary["posts_news"]),
        ("پست خوانده‌شده", summary["posts_scanned"]),
        ("کانال فروشنده", summary["channels"]),
        ("قطعهٔ دیده‌شده", f'{summary["parts_with_hits"]} از {summary["parts_total"]}'),
        ("ترکیب دیده‌شده", f'{summary["combos_with_hits"]} از {summary["combos_total"]}'),
        ("بازدید پست‌های فروشنده", summary["views_seller"]),
        ("برند دیده‌شده", summary["brands_observed"]),
    ]
    cards_html = "".join(f'<div class="card"><div class="k">{E(k)}</div><div class="v">{E(fa(v))}</div></div>'
                         for k, v in cards)

    part_rows = [[fa(i), p[0], p[1], fa(p[2]), fa(p[3]), fa(p[5]), fa(p[6]), p[9], hint(p[1])]
                 for i, p in enumerate(top_parts, 1)]
    combo_rows = [[fa(i), c[0], c[2], fa(c[5]), fa(c[6]), fa(c[9]), c[14], c[4]]
                  for i, c in enumerate(top_combos, 1)]
    all_combo_rows = [[fa(i), c[0], c[1], c[2], fa(c[5]), fa(c[6]), fa(c[8]), fa(c[9]), c[14], c[4]]
                      for i, c in enumerate(combos[:500], 1)]
    all_part_rows = [[fa(i), p[0], p[1], fa(p[2]), fa(p[3]), fa(p[5]), fa(p[6]), p[9], hint(p[1])]
                     for i, p in enumerate([p for p in parts], 1)]
    brand_rows = [[b, fa(n), fa(np), fa(v), "بله" if b in prepared else "—", plist or "—"]
                  for b, n, np, v, plist in brands]
    hint_rows = [[cat, "، ".join(bs)] for cat, bs in hints.items()]
    prep = "، ".join(prepared)
    price_rows = [[b["part"], b["vehicle"] or "—", b["brand"] or "—", fa_num(b["last"]),
                   fmt_ts(b["last_ts"]), fa_pct(b["day"]),
                   fa_pct(b["chg"]) if b["chg"] is not None else "—", fa_num(b["demand"])]
                  for b in [x for x in board if x["demand"] > 0][:30]]

    doc = f"""<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">
<title>آمار تقاضای قطعات یدکی خودرو</title>
<style>
@page {{ size: A4; margin: 12mm 9mm; }}
* {{ box-sizing: border-box; }}
body {{ font-family: Tahoma, "DejaVu Sans", "Noto Naskh Arabic", sans-serif; color:#111827;
        font-size: 9.5px; line-height: 1.6; }}
h1 {{ font-size: 19px; margin: 0 0 2px; }}
h2 {{ font-size: 13px; margin: 16px 0 6px; padding-bottom: 3px; border-bottom: 2px solid #0f766e;
      color:#0f766e; page-break-after: avoid; }}
.sub {{ color:#4b5563; font-size: 10px; margin-bottom: 10px; }}
.cards {{ display: flex; flex-wrap: wrap; gap: 5px; margin: 8px 0 4px; }}
.card {{ border:1px solid #d1d5db; border-radius: 5px; padding: 4px 8px; min-width: 108px;
         background:#f8fafc; }}
.card .k {{ color:#6b7280; font-size: 8.5px; }}
.card .v {{ font-weight: bold; font-size: 13px; color:#0f766e; }}
table {{ width: 100%; border-collapse: collapse; margin: 4px 0 10px; font-size: 8px; }}
thead {{ display: table-header-group; }}
tr {{ page-break-inside: avoid; }}
th, td {{ border: 1px solid #d1d5db; padding: 2px 3px; text-align: right; vertical-align: top; }}
th {{ background: #e5e7eb; font-size: 8px; }}
tbody tr:nth-child(even) {{ background: #f9fafb; }}
.note {{ background:#fffbeb; border:1px solid #fcd34d; border-radius:5px; padding:6px 8px;
         font-size:9px; margin:6px 0; }}
ol, ul {{ margin: 4px 18px 8px 0; padding: 0; }}
li {{ margin-bottom: 2px; }}
.footer {{ margin-top: 14px; border-top:1px solid #d1d5db; padding-top:4px; color:#6b7280; font-size: 8px; }}
</style></head><body>
<h1>آمار تاریخی تقاضای قطعات یدکی خودرو</h1>
<div class="sub">بازه: <span dir="ltr">{E(summary['first'])}</span> تا <span dir="ltr">{E(summary['last'])}</span> — قطعات خودروهای سواری و وانت — تولید: <span dir="ltr">{E(fmt_ts(time.time()))}</span></div>
<div class="cards">{cards_html}</div>

<h2>۳۰ قطعهٔ پرتکرار در کانال فروشندگان</h2>
{table(["#", "قطعه", "دسته", "پست", "۹۰ روز", "کانال", "بازدید", "برندهای دیده‌شده", "برندهای پیشنهادی بازار"], part_rows)}

<h2>۳۰ ترکیب پرتکرار قطعه×خودرو</h2>
{table(["#", "قطعه", "خودرو", "پست", "۹۰ روز", "بازدید", "برندهای دیده‌شده", "برندهای پیشنهادی بازار"], combo_rows)}

<h2>برندها (دیده‌شده و فهرست آماده)</h2>
{table(["برند", "پست", "قطعه", "بازدید", "در فهرست آماده", "قطعه‌های دیده‌شده"], brand_rows)}
<p class="note">برندهای فهرست آماده: {E(prep)}<br>
برندهایی که در پست‌ها دیده نشده‌اند با صفر آمده‌اند تا فهرست کامل بماند.</p>
{table(["دسته", "برندهای پیشنهادی"], hint_rows)}

<h2>قیمت اقلام پرتقاضا (آخرین قیمت ثبت‌شده)</h2>
{table(["قطعه", "خودرو", "برند", "آخرین قیمت (تومان)", "تاریخ", "تغییر ۲۴ساعته", "تغییر قبلی", "پست ۷ روز"], price_rows)}
<p class="note">قیمت‌ها از متن صریح پست‌های فروشنده خوانده می‌شوند ({E(fa(summary.get('price_observations', 0)))} مشاهده)؛
قیمت داخل عکس یا استعلام تلفنی دیده نمی‌شود. «تغییر ۲۴ساعته» فقط با قیمت دیروز و امروز پر می‌شود.</p>

<h2>۵۰۰ ترکیب اول (کامل، با برند)</h2>
{table(["#", "قطعه", "دسته", "خودرو", "پست", "۹۰ روز", "کانال", "بازدید", "برندهای دیده‌شده", "برندهای پیشنهادی بازار"], all_combo_rows)}

<h2>همهٔ قطعه‌ها</h2>
{table(["#", "قطعه", "دسته", "پست", "۹۰ روز", "کانال", "بازدید", "برندهای دیده‌شده", "برندهای پیشنهادی بازار"], all_part_rows)}

<h2>روش</h2>
<ol>
<li>صفحهٔ عمومی هر کانال (<code>t.me/s/&lt;name&gt;</code>) با <code>?before=</code> تا تاریخ برش عقب می‌رود.</li>
<li>در متن هر پست، نام قطعه/خودرو/برند با تطبیق واژه‌ای (طولانی‌ترین نام اول) پیدا می‌شود؛ برندهای «پیشنهادی بازار» از فهرست آمادهٔ هر دسته می‌آیند.</li>
<li>جدول ترکیبی از هم‌رخدادی ساخته می‌شود: هر پست با نام قطعه و خودرو، برای هر جفت یک‌بار شمرده می‌شود.</li>
<li>بازدید از پیش‌نمایش تلگرام خوانده می‌شود؛ مجموعش شاخص دیده‌شدن است، نه تعداد خرید.</li>
<li>کانال‌های فروشنده منبع اصلی‌اند؛ کانال‌های خبری فقط ستون جداگانه دارند.</li>
</ol>

<h2>محدودیت‌ها</h2>
<ul>
<li>نرخ کلیک گوگل قابل‌اندازه‌گیری نیست؛ این گزارش «فراوانی نام قطعه در محتوای عمومی» است.</li>
<li>فقط پست‌های متنی شمرده می‌شوند؛ کانال خصوصی و پست عکس‌محور بیرون‌اند.</li>
<li>فروشنده بیشتر از خریدار حرف می‌زند؛ عدد = شدت عرضه/مکالمهٔ بازار که با تقاضا همبسته است.</li>
<li>برند فقط وقتی ثبت می‌شود که در همان پست کنار نام قطعه آمده باشد؛ ستون «برندهای پیشنهادی بازار» تعمیم دسته است، نه مشاهده.</li>
</ul>
<div class="footer">پروژهٔ parts-demand — {E(fa(summary['posts'] or 0))} پست یکتا، {E(fa(summary['channels']))} کانال فروشنده</div>
</body></html>"""
    open(path, "w", encoding="utf-8").write(doc)
    return path


def report(args):
    db = open_db()
    r = build_report(db, args.top)
    os.makedirs(OUT_DIR, exist_ok=True)
    cat = load_catalog()
    fa = lambda x: str(x).translate(FA_DIGITS)

    # قطعه×خودرو: هر ۱۹۷۵ ترکیب کاتالوگ، مرتب بر اساس اندازه‌گیری در کانال‌های فروشنده
    combos = []
    for c in cat["combos"]:
        s = r["combos"].get((c["part"], c["vehicle"]))
        (sa, s90, na, chs, first, last, vs) = (s[2], s[3], s[4], s[5], s[6], s[7], s[8]) if s \
            else (0, 0, 0, 0, None, None, 0)
        combos.append([c["part"], c["cat"], c["vehicle"], c["models"], c["brand_hint"],
                       sa, s90, na, chs, vs, fmt_ts(first), fmt_ts(last),
                       c["spec"], r["sample"].get(c["part"], ""),
                       "، ".join(r["combo_brands"].get((c["part"], c["vehicle"]), [])[:4]) or "—"])
    combos.sort(key=lambda x: (-x[5], -x[9], -x[6], x[0]))
    header = ["رتبه", "قطعه", "دسته", "خودرو", "مدل‌ها", "برندهای رایج بازار",
              "پست فروشندگان", "همان در ۹۰ روز", "پست خبری", "کانال فروشنده",
              "مجموع بازدید", "اولین‌بار", "آخرین‌بار", "مشخصات", "نمونه لینک",
              "برندهای دیده‌شده (تعداد)"]
    rows = [[i] + row for i, row in enumerate(combos, 1)]
    write_csv(os.path.join(OUT_DIR, "parts_frequency.csv"), header, rows)
    write_csv(os.path.join(OUT_DIR, "top%d.csv" % args.top), header, rows[:args.top])

    # قطعه (بدون تفکیک خودرو)
    parts = []
    for p in cat["parts"]:
        s = r["parts"].get(p["name"])
        (sa, s90, na, chs, first, last, vs) = (s[1], s[2], s[3], s[4], s[6], s[7], s[8]) if s \
            else (0, 0, 0, 0, None, None, 0)
        parts.append([p["name"], p["cat"], sa, s90, na, chs, vs, fmt_ts(first), fmt_ts(last),
                      "، ".join(r["brands"].get(p["name"], [])[:4]) or "—",
                      r["sample"].get(p["name"], "")])
    parts.sort(key=lambda x: (-x[2], -x[6], -x[3]))
    write_csv(os.path.join(OUT_DIR, "parts_by_mentions.csv"),
              ["رتبه", "قطعه", "دسته", "پست فروشندگان", "همان در ۹۰ روز", "پست خبری", "کانال",
               "مجموع بازدید", "اولین‌بار", "آخرین‌بار", "برندهای دیده‌شده (تعداد)", "نمونه لینک"],
              [[i] + row for i, row in enumerate(parts, 1)])

    # خودرو
    veh = {v["name"]: [0, 0, 0, 0, 0] for v in cat["vehicles"]}
    for (part, vehicle), s in r["combos"].items():
        if vehicle in veh:
            veh[vehicle][0] += s[2]
            veh[vehicle][1] += s[3]
            veh[vehicle][2] += s[4]
            veh[vehicle][3] += s[8]
            veh[vehicle][4] += 1
    vrows = sorted(([k] + v for k, v in veh.items()), key=lambda x: -x[1])
    write_csv(os.path.join(OUT_DIR, "vehicles.csv"),
              ["رتبه", "خودرو", "پست فروشندگان", "همان در ۹۰ روز", "پست خبری",
               "مجموع بازدید", "تعداد قطعه دیده‌شده"],
              [[i] + [str(x) for x in row] for i, row in enumerate(vrows, 1)])

    total_posts, n_ch, first_ts, last_ts, s_posts, n_posts, scanned = r["coverage"]
    hit_combos = sum(1 for c in combos if c[5] > 0)
    hit_parts = sum(1 for p in parts if p[2] > 0)
    prepared = cat.get("brands", [])
    r_hints = cat.get("brand_hints", {})
    brand_table, seen_brands = [], set()
    for b, n, nparts, plist in r["brand_totals"]:
        brand_table.append([b, n, nparts, r["brand_views"].get(b, 0), plist])
        seen_brands.add(b)
    for b in prepared:
        if b not in seen_brands:
            brand_table.append([b, 0, 0, 0, ""])
    brand_table.sort(key=lambda x: (-x[1], x[0]))
    board, _ = price_board(db)
    obs = db.execute("""SELECT p.ts, p.part, p.vehicle, p.brand, p.amount, p.channel, q.url
                        FROM prices p LEFT JOIN posts q ON q.id=p.post_id
                        WHERE p.kind='seller' ORDER BY p.ts DESC""").fetchall()
    write_csv(os.path.join(OUT_DIR, "prices.csv"),
              ["تاریخ", "قطعه", "خودرو", "برند", "قیمت (تومان)", "کانال", "لینک"],
              [[fmt_ts(ts), part, veh, brand, str(amount), ch, url or ""]
               for ts, part, veh, brand, amount, ch, url in obs])
    summary = {"posts": total_posts or 0, "posts_seller": s_posts or 0, "posts_news": n_posts or 0,
               "channels": n_ch, "first": fmt_ts(first_ts), "last": fmt_ts(last_ts),
               "posts_scanned": scanned or 0, "combos_total": len(combos), "combos_with_hits": hit_combos,
               "parts_total": len(parts), "parts_with_hits": hit_parts,
               "brands_observed": len(seen_brands), "brands_prepared": len(prepared),
               "price_observations": len(obs), "parts_with_price": len({o[1] for o in obs}),
               "parts_with_brand": db.execute(
                   """SELECT COUNT(DISTINCT b.part) FROM brand_mentions b
                      JOIN posts q ON q.id=b.post_id WHERE q.kind='seller' AND q.ts>=?""",
                   (first_ts or 0,)).fetchone()[0],
               "top_brands": [[b, n] for b, n, nparts, views, plist in brand_table if n > 0][:5],
               "mentions_seller": sum(p[2] for p in parts), "views_seller": sum(p[6] for p in parts)}
    json.dump(summary, open(os.path.join(OUT_DIR, "summary.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)

    top_parts = [p for p in parts if p[2] > 0][:30]
    top_combos = [c for c in combos if c[5] > 0][:30]
    md = [f"# آمار تقاضای قطعات یدکی خودرو — {fmt_ts(time.time())}", "",
          "## پوشش داده", "",
          f"- پست دارای نام قطعه در کانال فروشندگان: **{fa(summary['posts_seller'])}** "
          f"(از {fa(n_ch)} کانال)",
          f"- پست دارای نام قطعه در کانال‌های خبری: {fa(summary['posts_news'])}",
          f"- پست خوانده‌شده (کل): {fa(summary['posts_scanned'])}",
          f"- بازه: {summary['first']} تا {summary['last']}",
          f"- قطعه‌های دیده‌شده: {fa(hit_parts)} از {fa(len(parts))}",
          f"- ترکیب‌های قطعه×خودروی دیده‌شده: {fa(hit_combos)} از {fa(len(combos))}",
          f"- مجموع بازدید پست‌های فروشندگان: {fa(summary['views_seller'])}", "",
          "## ۳۰ قطعهٔ پرتکرار در کانال فروشندگان", "",
          "| # | قطعه | دسته | پست | ۹۰ روز | کانال | بازدید | برندهای دیده‌شده | برندهای پیشنهادی بازار |",
          "|---|------|------|-----|--------|-------|--------|------------------|------------------------|"]
    for i, p in enumerate(top_parts, 1):
        md.append(f"| {fa(i)} | {p[0]} | {p[1]} | {fa(p[2])} | {fa(p[3])} | {fa(p[5])} | {fa(p[6])} | {p[9]} | "
                  f"{'، '.join(r_hints.get(p[1], [])) or '—'} |")
    md += ["", "## ۳۰ ترکیب پرتکرار قطعه×خودرو (فروشندگان)", "",
           "| # | قطعه | خودرو | پست | ۹۰ روز | بازدید | برندهای دیده‌شده | برندهای پیشنهادی بازار |",
           "|---|------|-------|-----|--------|--------|------------------|------------------------|"]
    for i, c in enumerate(top_combos, 1):
        md.append(f"| {fa(i)} | {c[0]} | {c[2]} | {fa(c[5])} | {fa(c[6])} | {fa(c[9])} | {c[14]} | {c[4]} |")
    md += ["", "## برندها (دیده‌شده و فهرست آماده)", "",
           "| برند | پست | قطعه | بازدید | در فهرست آماده | قطعه‌های دیده‌شده |",
           "|------|-----|------|--------|----------------|------------------|"]
    for b, n, nparts, views, plist in brand_table:
        md.append(f"| {b} | {fa(n)} | {fa(nparts)} | {fa(views)} | "
                  f"{'بله' if b in prepared else '—'} | {plist or '—'} |")
    md += ["", "برندهای فهرست آماده: " + "، ".join(prepared)]
    md += ["", "| دسته | برندهای پیشنهادی |", "|------|------------------|"]
    for cat_name, bs in r_hints.items():
        md.append(f"| {cat_name} | {'، '.join(bs)} |")
    md += ["", "## قیمت اقلام پرتقاضا (آخرین قیمت ثبت‌شده)", "",
           "| قطعه | خودرو | برند | قیمت (تومان) | تاریخ | تغییر ۲۴ساعته | تغییر قبلی | پست ۷ روز |",
           "|------|-------|------|----------------|-------|----------------|--------------|-----------|"]
    for b in [x for x in board if x["demand"] > 0][:25]:
        md.append(f"| {b['part']} | {b['vehicle'] or '—'} | {b['brand'] or '—'} | {fa_num(b['last'])} | "
                  f"{fmt_ts(b['last_ts'])} | {fa_pct(b['day'])} | "
                  f"{fa_pct(b['chg']) if b['chg'] is not None else '—'} | {fa_num(b['demand'])} |")
    md += ["", f"قیمت صریح ثبت‌شده: {fa_num(len(obs))} مشاهده برای {fa_num(len(board))} قطعه "
               f"(قیمت‌های داخل عکس خوانده نمی‌شوند)."]
    md += ["", "## روش", "",
           "1. صفحهٔ عمومی هر کانال (`t.me/s/<name>`) با `?before=` تا تاریخ برش عقب می‌رود.",
           "2. در متن هر پست، نام قطعه/خودرو/برند با تطبیق واژه‌ای (طولانی‌ترین نام اول) پیدا می‌شود.",
           "3. جدول ترکیبی از «هم‌رخدادی» ساخته می‌شود: هر پستی که هم نام قطعه و هم نام خودرو را داشته باشد،"
           " برای هر جفت (قطعه، خودرو) یک‌بار شمرده می‌شود؛ پست چندخودرویی به همهٔ خودروهای نام‌برده نسبت می‌گیرد."
           " در جدول قطعه‌ای هر پست فقط یک‌بار شمرده می‌شود.",
           "4. بازدید همان پست از پیش‌نمایش تلگرام خوانده می‌شود؛ مجموعش شاخص دیده‌شدن است.",
           "5. کانال‌های فروشنده (channels.txt) منبع اصلی‌اند؛ کانال‌های خبری (news.txt) فقط ستون جداگانه دارند"
           " تا خبرهای خودروهای جهانی آمار تقاضای بازار ایران را رقیق نکند.",
           "", "## محدودیت‌ها", "",
           "- نرخ کلیک گوگل قابل‌اندازه‌گیری نیست: گوگل این داده را منتشر نمی‌کند و Google Trends هم API رسمی ندارد.",
           "  عدد این پروژه «فراوانی نام قطعه در محتوای عمومی» است، نه کلیک.",
           "- فقط پست‌هایی که متن دارند شمرده می‌شوند؛ عکس‌محور و کانال‌های خصوصی بیرون‌اند.",
           "- کانال‌های فروشنده بیشتر از خریدار حرف می‌زنند؛ عدد = شدت عرضه/مکالمهٔ بازار، که با تقاضا همبسته است.",
           "- نام‌های مبهم (مثل «آینه»، «شمع») در متن‌های غیرقطعه‌ای می‌توانند خطا بسازند؛ ستون «نمونه لینک» برای بازبینی است.",
           "- پوشش یک سال به حجم کانال بستگی دارد؛ اگر `--pages` کم باشد، کانال‌های پرحجم فقط بخشی از سال را می‌دهند.",
           ""]
    open(os.path.join(OUT_DIR, "report.md"), "w", encoding="utf-8").write("\n".join(md))

    html_path = os.path.join(OUT_DIR, "report.html")
    build_html(html_path, summary, top_parts, top_combos, parts, combos, brand_table,
               prepared, r_hints, board)
    pdf_path = os.path.join(OUT_DIR, "report.pdf")
    if make_pdf(html_path, pdf_path):
        log.info("PDF نوشته شد: %s", pdf_path)
    else:
        log.warning("PDF ساخته نشد؛ HTML در %s هست", html_path)
    log.info("گزارش نوشته شد: %s (پست فروشنده=%d، ترکیب دیده‌شده=%d از %d)",
             OUT_DIR, s_posts or 0, hit_combos, len(combos))
    return summary, top_parts, top_combos


# ---------- تلگرام ----------
def send(text):
    if not (TELEGRAM_TOKEN and CHAT_ID):
        log.info("[بی‌توکن] %s", text[:300])
        return False
    for i in range(4):
        try:
            r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                              json={"chat_id": CHAT_ID, "text": text[:3900],
                                    "disable_web_page_preview": True}, timeout=30)
        except Exception as e:
            log.warning("خطای ارسال: %s", e)
            time.sleep(2 + 3 * i)
            continue
        if r.ok:
            return True
        if r.status_code == 429:
            time.sleep(int(r.json().get("parameters", {}).get("retry_after", 5)) + 1)
            continue
        log.warning("ارسال رد شد %s: %s", r.status_code, r.text[:160])
        return False
    return False


def send_document(path, caption=""):
    if not (TELEGRAM_TOKEN and CHAT_ID):
        log.info("[بی‌توکن] سند %s ارسال نشد", os.path.basename(path))
        return False
    if not os.path.exists(path):
        log.warning("سند نیست: %s", path)
        return False
    mime = "text/csv; charset=utf-8" if path.lower().endswith(".csv") else "text/markdown; charset=utf-8"
    for i in range(4):
        try:
            with open(path, "rb") as f:
                r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendDocument",
                                  data={"chat_id": CHAT_ID, "caption": caption[:1024]},
                                  files={"document": (os.path.basename(path), f, mime)}, timeout=120)
        except Exception as e:
            log.warning("خطای ارسال سند: %s", e)
            time.sleep(2 + 3 * i)
            continue
        if r.ok:
            return True
        if r.status_code == 429:
            try:
                time.sleep(int(r.json().get("parameters", {}).get("retry_after", 5)) + 1)
            except Exception:
                time.sleep(6)
            continue
        if r.status_code >= 500:
            time.sleep(2 + 3 * i)
            continue
        log.warning("سند رد شد %s: %s", r.status_code, r.text[:160])
        return False
    return False


def daily_digest(args):
    db = open_db()
    take_snapshot(db)
    d = daily_report(db)
    os.makedirs(OUT_DIR, exist_ok=True)
    fa_num_local = fa_num
    views = sum((p[3] or 0) for p in d["parts"])
    lines = [f"📅 بازار قطعات — {fmt_ts(time.time())}",
             f"بازه: {fa_num_local(d['hours'])} ساعت اخیر | پست فروشنده: {fa_num_local(d['posts'])} "
             f"(با نام قطعه: {fa_num_local(d['hit_posts'])}) | کانال: {fa_num_local(d['channels'])}",
             f"قطعه: {fa_num_local(len(d['parts']))} | ترکیب: {fa_num_local(len(d['combos']))} | "
             f"برند: {fa_num_local(len(d['brands']))} | بازدید: {fa_num_local(views)}"]
    if d["mgmt"]:
        lines += ["", "خلاصهٔ مدیریتی:"] + [f"• {x}" for x in d["mgmt"][:3]]
    if d["pmoves"]:
        lines += ["", "حرکت قیمت (نسبت به قیمت قبلی):"]
        for r in d["pmoves"][:5]:
            lines.append(f"• {r['part']}: {fa_pct(r['chg'])} — {fa_num_local(r['prev'])} → "
                         f"{fa_num_local(r['last'])} تومان")
    if d["parts"]:
        lines += ["", "۱۰ قطعهٔ پرتکرار این بازه:"]
        for i, p in enumerate(d["parts"][:10], 1):
            lines.append(f"{fa_num_local(i)}. {p[0]} — {fa_num_local(p[1])} پست")
        if d["brands"]:
            lines += ["", "برندها: " + "، ".join(f"{b} ({fa_num_local(n)})" for b, n in d["brands"][:6])]
        lines += ["", "PDF روزانه و PDF قیمت در پیام‌های بعدی."]
    else:
        lines += ["", "در این بازه پستی با نام قطعه نبود."]
    ok = send("\n".join(lines))
    if not d["parts"]:
        log.info("گزارش روزانه: در بازه پستی نبود")
        return ok
    html_path = os.path.join(OUT_DIR, "daily.html")
    build_daily_html(html_path, d)
    pdf_path = os.path.join(OUT_DIR, "daily.pdf")
    sent = 0
    if make_pdf(html_path, pdf_path) and send_document(pdf_path, f"گزارش روزانهٔ بازار — {fmt_ts(time.time())}"):
        sent += 1
    else:
        log.warning("گزارش روزانه ساخته/ارسال نشد")
    if d["board"]:
        price_html = os.path.join(OUT_DIR, "prices.html")
        demand_parts = sorted(d["demand7"].items(), key=lambda x: -x[1])
        build_prices_html(price_html, d["board"], d["since"], demand_parts)
        price_pdf = os.path.join(OUT_DIR, "prices.pdf")
        if make_pdf(price_html, price_pdf) and send_document(
                price_pdf, f"قیمت روزانهٔ اقلام پرفروش — {fmt_ts(time.time())}"):
            sent += 1
        else:
            log.warning("گزارش قیمت ساخته/ارسال نشد")
    log.info("گزارش روزانه ارسال شد · %d قطعه، %d ترکیب، %d قیمت، %d فایل",
             len(d["parts"]), len(d["combos"]), d["price_obs"], sent)
    if ok:
        set_meta(db, "last_daily", time.time())
    return ok


def alerts_digest(args):
    db = open_db()
    take_snapshot(db)
    fresh = detect_alerts(db)
    if not fresh:
        log.info("هشدار تازه‌ای نبود")
        return True
    lines = [f"🚨 هشدار بازار — {fmt_ts(time.time())} (UTC)", ""]
    lines += [i["line"] for i in fresh[:20]]
    lines += ["", "معیار: جهش تعداد پست در ۲۴ ساعت نسبت به پایهٔ ۱۴ روز، رشد بازدید روزانه، "
                  "یا تغییر قیمت ≥۸٪ در قطعه‌های پرتقاضا."]
    ok = send("\n".join(lines))
    if ok:
        for i in fresh:
            db.execute("INSERT OR REPLACE INTO alerts(key, ts, note) VALUES(?,?,?)",
                       (i["key"], time.time(), i["kind"]))
        db.commit()
        log.info("هشدار ارسال شد: %d مورد", len(fresh))
    return ok


def digest(args):
    if getattr(args, "daily", False):
        return daily_digest(args)
    if getattr(args, "alerts", False):
        return alerts_digest(args)
    summary, top_parts, _ = report(args)
    fa = lambda x: str(x).translate(FA_DIGITS)
    lines = [f"📊 آمار تقاضای قطعات — {fmt_ts(time.time())}",
             f"پست فروشندگان با نام قطعه: {fa(summary['posts_seller'])} "
             f"(خبری: {fa(summary['posts_news'])})",
             f"بازه: {summary['first']} تا {summary['last']}",
             f"ترکیب دیده‌شده: {fa(summary['combos_with_hits'])} از {fa(summary['combos_total'])}",
             f"قیمت ثبت‌شده: {fa_num(summary.get('price_observations', 0))} "
             f"برای {fa_num(summary.get('parts_with_price', 0))} قطعه",
             f"برند مشخص: {fa_num(summary.get('parts_with_brand', 0))} "
             f"از {fa_num(summary.get('parts_with_hits', 0))} قطعهٔ دیده‌شده",
             "", "۱۵ قطعهٔ پرتکرار در بازار:"]
    for i, p in enumerate([p for p in top_parts if p[2] > 0][:15], 1):
        lines.append(f"{fa(i)}. {p[0]} — {fa(p[2])} پست ({fa(p[3])} در ۹۰ روز)")
    tb = summary.get("top_brands") or []
    if tb:
        lines += ["", "برندهای پرتکرار: " + "، ".join(f"{b} ({fa(n)})" for b, n in tb)]
    lines += ["", "گزارش کامل (PDF) و جدول‌ها در پیام‌های بعدی."]
    ok = send("\n".join(lines))
    sent = 0
    for name, cap in (("report.pdf", "گزارش کامل (PDF)"),
                      ("prices.csv", "قیمت‌های ثبت‌شده"),
                      ("top500.csv", "۵۰۰ ترکیب پرتقاضا"),
                      ("parts_frequency.csv", "ماتریس کامل ترکیب‌ها")):
        if send_document(os.path.join(OUT_DIR, name), f"{cap} — {fmt_ts(time.time())}"):
            sent += 1
        time.sleep(1.0)
    if ok:
        mdb = open_db()
        now = time.time()
        set_meta(mdb, "last_full", now)
        set_meta(mdb, "last_daily", now)  # گزارش کامل جای گزارش روزانهٔ همان روز را می‌گیرد
        mdb.close()
    log.info("خلاصه %s · فایل‌ها: %d از ۴", "ارسال شد" if ok else "ارسال نشد (توکن/چت تنظیم نشده)", sent)
    return ok


def mode_cmd(args):
    """حالت پیشنهادی این اجرا را چاپ می‌کند تا workflow به ساعتِ زمان‌بند وابسته نباشد."""
    db = open_db()
    mode = decide_mode(db)
    db.close()
    print(mode)
    return 0


# ---------- تست ----------
def selftest():
    cat = load_catalog()
    rx, term_map = build_matchers(cat)
    cases = [
        ("لنت ترمز جلو پراید ۱۳۱ موجود شد", "لنت ترمز جلو", "پراید", ""),
        ("کیت کلاچ پژو ۲۰۶ تیپ ۲ اصل", "کیت کلاچ", "پژو ۲۰۶", ""),
        ("وانت پراید کمک فنر عقب", "کمک فنر عقب", "وانت پراید", ""),
        ("رادیاتور کولر پژو ۴۰۵", "کندانسور کولر", "پژو ۴۰۵", ""),
        ("فیلتر روغن سمند EF7", "فیلتر روغن", "سمند", ""),
        ("بلبرینگ چرخ جلو پیکان", "بلبرینگ چرخ جلو", "وانت پیکان", ""),
        ("تیغه برف پاک کن پژو ۲۰۶", "تیغه برف پاک‌کن", "پژو ۲۰۶", ""),
        ("پمپ بنزین پراید و پژو ۲۰۶", "پمپ بنزین", "", ""),
        ("قیمت دلار امروز", "", "", ""),
        ("ایساکو لنت ترمز جلو پراید", "لنت ترمز جلو", "پراید", "ایساکو"),
        ("کمپرسور کولر ام وی ام ۳۱۵", "کمپرسور کولر", "ام‌وی‌ام", ""),
    ]
    bad = 0
    for text, want_part, want_veh, want_brand in cases:
        h = match_terms(rx, term_map, norm(text))
        parts = sorted(h["part"].values())
        # همان قاعدهٔ نسبت‌دادن خودرو در ingest: فقط وقتی دقیقاً یک خودرو در پست آمده باشد
        got_veh = next(iter(h["vehicle"].values())) if len(h["vehicle"]) == 1 else ""
        got_brand = next(iter(h["brand"].values()), "")
        ok = (want_part in parts if want_part else not parts) and got_veh == want_veh and got_brand == want_brand
        print(("✓" if ok else "✗"), text, "→", parts, got_veh or "—", got_brand or "—")
        bad += 0 if ok else 1
    print(f"\n{len(cases) - bad}/{len(cases)} درست")
    return 0 if bad == 0 else 1


def probe(args):
    channels = [c.strip() for c in open(CHANNELS_FILE, encoding="utf-8") if c.strip() and not c.strip().startswith("#")]
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = {ex.submit(fetch_channel, c, time.time() - args.days * 86400, 1, time.time() + 120): c
                for c in channels}
        for f in as_completed(futs):
            try:
                name, items, sc, pages = f.result()
            except Exception as e:
                print("ERR", e)
                continue
            ts = [t for _, _, t, _ in items if t]
            print(f"{name:32} {sc:4d} پست   آخرین={fmt_ts(max(ts)) if ts else '—'}")
    return 0


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
    ap = argparse.ArgumentParser(description="آمار تاریخی تقاضای قطعات یدکی خودرو")
    sub = ap.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("collect", help="برداشت پست‌های کانال‌ها")
    c.add_argument("--days", type=int, default=int(os.environ.get("DAYS", "365")))
    c.add_argument("--pages", type=int, default=int(os.environ.get("PAGES", "40")))
    c.add_argument("--workers", type=int, default=int(os.environ.get("WORKERS", "3")))
    c.add_argument("--max-runtime", type=int, default=int(os.environ.get("MAX_RUNTIME", "2400")))
    c.add_argument("--channels", nargs="*", default=None)
    c.add_argument("--no-news", action="store_true", help="کانال‌های خبری را نخوان (فقط فروشندگان)")

    r = sub.add_parser("report", help="ساخت جدول‌های فراوانی")
    r.add_argument("--top", type=int, default=int(os.environ.get("TOP", "500")))

    d = sub.add_parser("digest", help="ارسال خلاصه به تلگرام")
    d.add_argument("--top", type=int, default=int(os.environ.get("TOP", "500")))
    d.add_argument("--daily", action="store_true", help="گزارش کوتاه بازهٔ اخیر + PDF روزانه و قیمت")
    d.add_argument("--alerts", action="store_true", help="فقط هشدارهای جهش (بدون PDF)")
    sub.add_parser("rebuild", help="استخراج دوبارهٔ نام‌ها از پست‌های ذخیره‌شده (بدون شبکه)")
    sub.add_parser("selftest", help="تست تطبیق نام‌ها")
    sub.add_parser("mode", help="حالت پیشنهادی: full | daily | alerts")

    p = sub.add_parser("probe", help="سلامت و حجم کانال‌ها")
    p.add_argument("--days", type=int, default=365)

    args = ap.parse_args()
    if args.cmd == "collect":
        collect(args)
    elif args.cmd == "report":
        report(args)
    elif args.cmd == "digest":
        digest(args)
    elif args.cmd == "rebuild":
        rebuild(args)
    elif args.cmd == "selftest":
        sys.exit(selftest())
    elif args.cmd == "mode":
        sys.exit(mode_cmd(args))
    elif args.cmd == "probe":
        sys.exit(probe(args))


if __name__ == "__main__":
    main()
