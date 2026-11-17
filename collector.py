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
TR = str.maketrans({"‌": " ", "ي": "ی", "ك": "ک", "ة": "ه", "ـ": "", "ﻻ": "لا",
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
    for b in cat["brands"]:
        terms.append((norm(b), "brand", norm(b), b))
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
    CREATE INDEX IF NOT EXISTS idx_mentions_part ON mentions(part, ts);
    CREATE INDEX IF NOT EXISTS idx_mentions_veh ON mentions(vehicle, ts);
    """)
    return conn


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
    hits = match_terms(rx, term_map, norm(text))
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
    return parts


def ingest(db, rx, term_map, cat, channel, kind, url, ts, text, views):
    pid = hashlib.md5(f"{channel}|{url}|{text[:80]}".encode()).hexdigest()
    if db.execute("SELECT 1 FROM posts WHERE id=?", (pid,)).fetchone():
        return False
    if not _write_mentions(db, rx, term_map, cat, pid, channel, kind, ts, url, text, views):
        return False
    db.execute("INSERT OR IGNORE INTO posts VALUES(?,?,?,?,?,?,?)",
               (pid, channel, ts, url, text[:2000], views, kind))
    return True


def rebuild(args):
    """بعد از تغییر کاتالوگ، نام‌ها را از متن پست‌های ذخیره‌شده دوباره استخراج می‌کند (بدون شبکه)."""
    cat = load_catalog()
    rx, term_map = build_matchers(cat)
    db = open_db()
    for t in ("mentions", "brand_mentions", "pairs"):
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


def build_html(path, summary, top_parts, top_combos, parts, combos, brands, prepared, hints):
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
    summary = {"posts": total_posts or 0, "posts_seller": s_posts or 0, "posts_news": n_posts or 0,
               "channels": n_ch, "first": fmt_ts(first_ts), "last": fmt_ts(last_ts),
               "posts_scanned": scanned or 0, "combos_total": len(combos), "combos_with_hits": hit_combos,
               "parts_total": len(parts), "parts_with_hits": hit_parts,
               "brands_observed": len(seen_brands), "brands_prepared": len(prepared),
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
               prepared, r_hints)
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


def digest(args):
    summary, top_parts, _ = report(args)
    fa = lambda x: str(x).translate(FA_DIGITS)
    lines = [f"📊 آمار تقاضای قطعات — {fmt_ts(time.time())}",
             f"پست فروشندگان با نام قطعه: {fa(summary['posts_seller'])} "
             f"(خبری: {fa(summary['posts_news'])})",
             f"بازه: {summary['first']} تا {summary['last']}",
             f"ترکیب دیده‌شده: {fa(summary['combos_with_hits'])} از {fa(summary['combos_total'])}",
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
                      ("top500.csv", "۵۰۰ ترکیب پرتقاضا"),
                      ("parts_frequency.csv", "ماتریس کامل ترکیب‌ها")):
        if send_document(os.path.join(OUT_DIR, name), f"{cap} — {fmt_ts(time.time())}"):
            sent += 1
        time.sleep(1.0)
    log.info("خلاصه %s · فایل‌ها: %d از ۳", "ارسال شد" if ok else "ارسال نشد (توکن/چت تنظیم نشده)", sent)
    return ok


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
    sub.add_parser("rebuild", help="استخراج دوبارهٔ نام‌ها از پست‌های ذخیره‌شده (بدون شبکه)")
    sub.add_parser("selftest", help="تست تطبیق نام‌ها")

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
    elif args.cmd == "probe":
        sys.exit(probe(args))


if __name__ == "__main__":
    main()
