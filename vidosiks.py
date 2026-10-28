#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GAME AUTOMIX v7 — ускоренный автомонтаж с диагностикой ручных лазеров.
v7.1: ручные лазеры больше не пропадают молча — кроп сдвигается к меткам, слой считается
      в шкале исходного видео на 12 fps без декодирования кадров, итоговый клип проверяется.
"""

import glob
import hashlib
import importlib.util
import io
import json
import math
import os
import queue

# Отключаем предупреждение про симлинки Hugging Face на Windows
os.environ["HF_HUB_DISABLE_SYMLINKS_WARNING"] = "1"
# Сдерживаем внутренний параллелизм численных библиотек, чтобы не занимать все ядра.
for _env_name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_env_name] = "1"

import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import traceback
import time
import webbrowser
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from dataclasses import dataclass, field, replace
from datetime import datetime
from tkinter import filedialog, simpledialog, messagebox
import tkinter as tk

import customtkinter as ctk

try:
    import numpy as np
except ImportError:
    np = None
try:
    from PIL import Image, ImageDraw, ImageFont, ImageTk, ImageFilter
except Exception:
    Image = ImageDraw = ImageFont = ImageTk = ImageFilter = None
try:
    import cv2
except Exception:
    cv2 = None

# ──────────────────────────────────────────────────────────────────────────────
#  Константы
# ──────────────────────────────────────────────────────────────────────────────
VIDEO_EXT = (".mp4", ".mkv")
AUDIO_EXT = (".mp3", ".wav", ".m4a", ".aac", ".flac", ".ogg", ".opus", ".wma", ".mp4", ".mkv")
BELOW_NORMAL_PRIORITY_CLASS = 0x00004000 if sys.platform == "win32" else 0
CREATE_NO_WINDOW = (0x08000000 | BELOW_NORMAL_PRIORITY_CLASS) if sys.platform == "win32" else 0
FFMPEG_FILTER_THREADS = 1
# A few encoder threads are much faster than one thread at 1080x1920,
# while still avoiding an unrestricted FFmpeg thread explosion.
FFMPEG_CODEC_THREADS = max(2, min(6, os.cpu_count() or 4))
LASER_FPS = 4
DETECT_WIDTH = 640
LASER_OVERLAY_SCALE = 0.5  # draw transparent laser PNGs at half size, upscale in FFmpeg
LASER_MANUAL_FPS = 30        # верхняя граница частоты слоя ручных лазеров; совпадает с половиной 60 FPS
MANUAL_LASER_EDGE_TOL = 0.55 # сек: «хвост» лазеров вокруг первой/последней метки
LASER_PROBE_MIN_PIXELS = 120 # минимум красных пикселей на проверочном кадре готового клипа
LASER_MANUAL_MIN_FPS = 15   # минимум ручного слоя; далее частота адаптируется по скорости движения меток
LASER_TRACK_TOL_PX = 10      # допустимое отставание лучей от размеченной точки, px итогового кадра

def resource_path(relative_path: str) -> str:
    """Resolve a bundled file both in normal Python mode and in PyInstaller EXE."""
    base_path = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base_path, relative_path)


MATADOR_FILE_EXTS = (".mp3", ".wav", ".m4a", ".aac", ".flac", ".ogg", ".opus", ".wma", ".mp4", ".mkv")


def _find_matador_asset(directory: str) -> str:
    """Find the single auto-saved Matadores track in a project/user assets folder."""
    for ext in MATADOR_FILE_EXTS:
        candidate = os.path.join(directory, "matadores" + ext)
        if os.path.isfile(candidate):
            return candidate
    return ""


def bundled_matador_music_path() -> str:
    """Find the Matadores audio asset in project files or inside a PyInstaller EXE."""
    return _find_matador_asset(resource_path("assets"))


def user_matador_music_path() -> str:
    """Persistent copy used when the app is already running as a packaged EXE."""
    return _find_matador_asset(os.path.join(APP_DIR, "assets"))


def default_matador_music_path() -> str:
    return bundled_matador_music_path() or user_matador_music_path()


def is_bundled_matador_music(path: str) -> bool:
    if not path:
        return False
    bundled = bundled_matador_music_path()
    if not bundled:
        return False
    return os.path.normcase(os.path.abspath(path)) == os.path.normcase(os.path.abspath(bundled))


def project_assets_directory() -> str:
    """Writable assets folder beside the .py source; used for future EXE builds."""
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets")


APP_DIR = os.environ.get("AUTOMIX_HOME") or os.path.join(os.path.expanduser("~"), ".game_automix")
CACHE_DIR = os.path.join(APP_DIR, "cache")
HISTORY_FILE = os.path.join(APP_DIR, "history.json")
SETTINGS_FILE = os.path.join(APP_DIR, "settings.json")
MANUAL_LASER_DIR = os.path.join(APP_DIR, "manual_lasers")
_MANUAL_LASER_CACHE = {}
_MANUAL_LASER_LAST_ERROR = {}
CACHE_VERSION = 3


def manual_laser_annotation_path(video_path: str) -> str:
    """Stable per-video location for user-authored laser keyframes."""
    identity = os.path.normcase(os.path.abspath(video_path))
    digest = hashlib.sha1(identity.encode("utf-8", "ignore")).hexdigest()[:20]
    return os.path.join(MANUAL_LASER_DIR, digest + ".json")


def _copy_laser_rows(rows: list) -> list:
    """Копия меток, включая необязательные точки направления лучей."""
    copied = []
    for row in rows:
        item = {"time": row["time"], "points": [list(p) for p in row["points"]]}
        if row.get("directions") and len(row["directions"]) == 2:
            item["directions"] = [list(p) for p in row["directions"]]
        copied.append(item)
    return copied


def manual_laser_window(rows: list):
    """Интервал (с), в котором ручные лазеры включены: первая метка − хвост … последняя + хвост."""
    if not rows:
        return None
    return rows[0]["time"] - MANUAL_LASER_EDGE_TOL, rows[-1]["time"] + MANUAL_LASER_EDGE_TOL


def manual_laser_span_text(rows: list) -> str:
    """Человеческое объяснение, когда лазеры будут видны (показывается после сохранения метки)."""
    window = manual_laser_window(rows)
    if not window:
        return "Меток нет."
    a, b = max(0.0, window[0]), window[1]
    if len(rows) == 1:
        return (f"Одна метка: лазеры будут видны только около неё ({a:.2f}–{b:.2f} с). "
                f"Добавь вторую метку позже по времени, чтобы лазеры шли дольше.")
    return f"Лазеры будут видны с {a:.2f} по {b:.2f} с (между метками позиции интерполируются)."


def find_related_annotation_files(video_path: str) -> list:
    """Файлы меток с тем же именем видео, но по другому пути (видео переместили/переименовали папку)."""
    own = manual_laser_annotation_path(video_path)
    name = os.path.basename(video_path).lower()
    found = []
    try:
        for fn in os.listdir(MANUAL_LASER_DIR):
            full = os.path.join(MANUAL_LASER_DIR, fn)
            if not fn.endswith(".json") or full == own:
                continue
            with open(full, "r", encoding="utf-8") as f:
                payload = json.load(f)
            old_path = str(payload.get("video_path", ""))
            if os.path.basename(old_path).lower() == name:
                found.append((old_path, len(payload.get("annotations", []))))
    except (OSError, ValueError, AttributeError, TypeError):
        pass
    return found


def load_manual_laser_annotations(video_path: str) -> list:
    """Load validated normalized-coordinate keyframes for one source video."""
    filename = manual_laser_annotation_path(video_path)
    identity = os.path.normcase(os.path.abspath(video_path))
    try:
        mtime = os.path.getmtime(filename)
    except OSError:
        mtime = None
    cached = _MANUAL_LASER_CACHE.get(identity)
    if cached is not None and cached[0] == mtime:
        return _copy_laser_rows(cached[1])
    _MANUAL_LASER_LAST_ERROR.pop(identity, None)
    try:
        with open(filename, "r", encoding="utf-8") as f:
            payload = json.load(f)
        rows = payload.get("annotations", [])
        cleaned = []
        for row in rows:
            stamp = float(row.get("time", -1))
            points = row.get("points", [])
            if stamp < 0 or len(points) != 2:
                continue
            fixed = []
            valid = True
            for point in points:
                if not isinstance(point, (list, tuple)) or len(point) != 2:
                    valid = False
                    break
                x, y = float(point[0]), float(point[1])
                if not (math.isfinite(x) and math.isfinite(y)):
                    valid = False
                    break
                fixed.append([min(1.0, max(0.0, x)), min(1.0, max(0.0, y))])
            if valid:
                raw_directions = row.get("directions")
                fixed_directions = []
                directions_valid = isinstance(raw_directions, (list, tuple)) and len(raw_directions) == 2
                if directions_valid:
                    for point in raw_directions:
                        if not isinstance(point, (list, tuple)) or len(point) != 2:
                            directions_valid = False
                            break
                        try:
                            x, y = float(point[0]), float(point[1])
                        except (TypeError, ValueError):
                            directions_valid = False
                            break
                        if not (math.isfinite(x) and math.isfinite(y)):
                            directions_valid = False
                            break
                        fixed_directions.append([min(1.0, max(0.0, x)), min(1.0, max(0.0, y))])
                # Сортируем глаза слева направо и сохраняем соответствующую им стрелку направления.
                if directions_valid:
                    paired = sorted(zip(fixed, fixed_directions), key=lambda pair: pair[0][0])
                    fixed = [pair[0] for pair in paired]
                    fixed_directions = [pair[1] for pair in paired]
                else:
                    fixed.sort(key=lambda p: p[0])
                item = {"time": stamp, "points": fixed}
                if directions_valid:
                    item["directions"] = fixed_directions
                cleaned.append(item)
        result = sorted(cleaned, key=lambda row: row["time"])
    except FileNotFoundError:
        result = []
    except (OSError, ValueError, TypeError, AttributeError, json.JSONDecodeError) as exc:
        # Раньше повреждённый файл молча превращался в «меток нет». Теперь причина видна в диагностике.
        _MANUAL_LASER_LAST_ERROR[identity] = f"{type(exc).__name__}: {exc}"
        result = []
    _MANUAL_LASER_CACHE[identity] = (mtime, result)
    return _copy_laser_rows(result)


def _smooth_laser_field(rows: list, field: str, timestamp: float):
    """Cubic-Hermite interpolation of two normalized points per keyframe.

    Time-aware tangents smooth the velocity at keyframes without changing saved marks.
    Values are constrained close to the segment endpoints to prevent spline overshoot.
    """
    valid = [row for row in rows if isinstance(row.get(field), (list, tuple)) and len(row[field]) == 2]
    if not valid:
        return None
    valid = sorted(valid, key=lambda row: row["time"])
    if timestamp <= valid[0]["time"]:
        return [list(p) for p in valid[0][field]]
    if timestamp >= valid[-1]["time"]:
        return [list(p) for p in valid[-1][field]]

    right_idx = next(i for i in range(1, len(valid)) if valid[i]["time"] >= timestamp)
    left_idx = right_idx - 1
    left, right = valid[left_idx], valid[right_idx]
    t0, t1 = float(left["time"]), float(right["time"])
    if t1 <= t0:
        return [list(p) for p in right[field]]
    dt = t1 - t0
    u = min(1.0, max(0.0, (timestamp - t0) / dt))
    u2, u3 = u * u, u * u * u
    h00, h10 = 2*u3 - 3*u2 + 1, u3 - 2*u2 + u
    h01, h11 = -2*u3 + 3*u2, u3 - u2

    out = []
    for point_idx in range(2):
        xy = []
        for axis in range(2):
            p0 = float(left[field][point_idx][axis])
            p1 = float(right[field][point_idx][axis])
            secant = (p1 - p0) / dt
            if left_idx == 0:
                m0 = secant
            else:
                prev = valid[left_idx - 1]
                span = max(1e-9, float(right["time"]) - float(prev["time"]))
                m0 = (float(right[field][point_idx][axis]) - float(prev[field][point_idx][axis])) / span
            if right_idx == len(valid) - 1:
                m1 = secant
            else:
                nxt = valid[right_idx + 1]
                span = max(1e-9, float(nxt["time"]) - float(left["time"]))
                m1 = (float(nxt[field][point_idx][axis]) - float(left[field][point_idx][axis])) / span
            value = h00*p0 + h10*dt*m0 + h01*p1 + h11*dt*m1
            # Avoid large spline excursions if keyframes are irregularly spaced.
            margin = 0.01
            value = min(max(value, min(p0, p1) - margin), max(p0, p1) + margin)
            xy.append(min(1.0, max(0.0, value)))
        out.append(xy)
    return out


def manual_laser_points_from_rows(rows: list, timestamp: float):
    """Return smoothed, interpolated normalized laser origins from keyframes."""
    if not rows:
        return None
    edge_tolerance = MANUAL_LASER_EDGE_TOL
    if timestamp < rows[0]["time"] - edge_tolerance or timestamp > rows[-1]["time"] + edge_tolerance:
        return None
    return _smooth_laser_field(rows, "points", timestamp)

def manual_laser_points_at(video_path: str, timestamp: float):
    """Return interpolated normalized laser origins, or None outside marked ranges."""
    return manual_laser_points_from_rows(load_manual_laser_annotations(video_path), timestamp)


def manual_laser_sample_from_rows(rows: list, timestamp: float):
    """Interpolate laser origins and optional user-defined direction targets smoothly."""
    points = manual_laser_points_from_rows(rows, timestamp)
    if points is None or not rows:
        return None

    direction_rows = [row for row in rows
                      if isinstance(row.get("directions"), (list, tuple)) and len(row["directions"]) == 2]
    directions = None
    if direction_rows:
        # Keep the nearest known direction outside the direction-mark interval, as before.
        directions = _smooth_laser_field(direction_rows, "directions", timestamp)
    return {"points": points, "directions": directions}

def manual_laser_sample_at(video_path: str, timestamp: float):
    """Return the current origins + optional direction handles for a source-video timestamp."""
    return manual_laser_sample_from_rows(load_manual_laser_annotations(video_path), timestamp)

STEP = 0.5            # шаг анализа, сек
SR = 12000            # частота дискретизации для анализа звука
SW, SH = 64, 36       # миниатюра кадра для анализа
SILENCE_DB = -48.0    # тишина
BLACK_LUMA = 10       # «чёрный кадр»
FREEZE_DIFF = 0.35    # статичная картинка
FREEZE_RATE = 0.5     # статичная картинка
MIN_EVENT = 0.30      # минимальный «счёт» события
GOOD_SCORE = 0.40     # «хороший» момент
MIN_PAD = 2.0         # минимальный запас до/после события, сек
MAX_BAD_FRACTION = 0.30

WEIGHTS = {"loud": 1.0, "burst": 1.5, "motion": 1.0, "scene": 0.7}
EVENT_LABELS = {"loud": "громкий момент", "burst": "выстрел/взрыв",
                "motion": "экшен", "scene": "смена сцены"}


class Cancelled(Exception):
    """Пользователь нажал «Стоп»."""


# ──────────────────────────────────────────────────────────────────────────────
#  Настройки и структуры данных
# ──────────────────────────────────────────────────────────────────────────────
@dataclass
class Settings:
    root_dir: str = ""
    out_dir: str = ""
    files: list = field(default_factory=list)
    trim_on: bool = True
    trim_sec: float = 4.0
    clean_audio: bool = True
    suppress_speech: bool = True
    events: dict = field(default_factory=lambda: {
        "loud": True, "burst": True, "motion": True, "scene": True})
    skip_black: bool = True
    skip_frozen: bool = True
    pre: float = 5.0
    post: float = 5.0
    min_len: float = 8.0
    max_len: float = 40.0
    target: int = 60
    strict: bool = True
    order: str = "Блоки: игра → видео → по времени"
    per_file_max: int = 2
    balance: bool = True
    variety: float = 0.3
    no_repeat: bool = True
    width: int = 1080
    height: int = 1920
    fps: int = 30
    frame_mode: str = "Умный кроп (по активности)"
    quality: str = "Высокое"
    threads: int = 1
    depth: str = "Сбалансировано"
    hw: bool = True
    require_visual: bool = True
    visual_level: float = 0.30
    snap_pauses: bool = True
    transitions: str = "Авто (умный выбор)"
    effects: bool = True
    titles: bool = True
    captions: bool = False
    caption_lang: str = "auto"
    mode: str = "Игры"
    shorts_mode: bool = False
    music_path: str = ""
    music_volume: float = 0.45
    matador_music_enabled: bool = False
    matador_music_path: str = ""
    matador_music_volume: float = 0.45
    original_volume: float = 0.65
    keep_original_audio: bool = True
    laser_effect: bool = False
    laser_universal_search: bool = True
    limit_resources: bool = True
    youtube_attribution_filter: str = "Атрибуция не требуется"


@dataclass
class Episode:
    path: str
    game: str
    start: float
    end: float
    core_s: float
    core_e: float
    score: float
    tag: str
    has_audio: bool
    src_w: int = 0
    src_h: int = 0
    file_dur: float = 0.0
    cx: float = 0.5
    eff: float = 0.0
    trans: str = "auto"
    reaction: float = 0.0
    e_start: float = 0.5
    e_end: float = 0.5
    zoom: bool = False
    manual: bool = False
    title: str = ""
    words: list = field(default_factory=list)
    words_rng: tuple = (0.0, 0.0)

    @property
    def dur(self):
        return self.end - self.start


@dataclass
class FileFeatures:
    path: str
    game: str
    dur: float
    n: int
    loud: object = None
    burst: object = None
    speech: object = None
    motion: object = None
    bright: object = None
    scene: object = None


# ──────────────────────────────────────────────────────────────────────────────
#  Определитель имени игры
# ──────────────────────────────────────────────────────────────────────────────
def detect_game_name(path, root=""):
    if root:
        try:
            rel = os.path.relpath(path, root)
            if not rel.startswith(".."):
                parts = rel.split(os.sep)
                if len(parts) >= 2:
                    pname = parts[0].strip()
                    if pname and not pname.lower().startswith(("unknown", "video", "replay", "_")):
                        return pname
        except ValueError:
            pass

    parent = os.path.basename(os.path.dirname(os.path.abspath(path)))
    if parent and not parent.lower().startswith(("unknown", "video", "replay", "desktop", "captures", "_")):
        return parent

    fname = os.path.splitext(os.path.basename(path))[0]
    m = re.split(r"(_replay_|_clip_|_DVR_|_202\d|\(\d+\))", fname, flags=re.IGNORECASE)
    clean = m[0].strip(" _-")
    if clean.lower().startswith("unknown"):
        clean = ""
    return clean or "Игра"


# ──────────────────────────────────────────────────────────────────────────────
#  Работа с ffmpeg
# ──────────────────────────────────────────────────────────────────────────────
def find_ffmpeg():
    try:
        import imageio_ffmpeg
        return imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        return shutil.which("ffmpeg")


def run(cmd, cancelled=None):
    # Все команды этого приложения вызывают FFmpeg. Опции ставятся в начало,
    # чтобы ограничить потоки декодирования и фильтров на длинных записях.
    if cmd and os.path.basename(str(cmd[0])).lower().startswith("ffmpeg"):
        cmd = [cmd[0], "-filter_threads", str(FFMPEG_FILTER_THREADS),
               "-filter_complex_threads", str(FFMPEG_FILTER_THREADS),
               "-threads", str(FFMPEG_CODEC_THREADS), *cmd[1:]]
    try:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             stdin=subprocess.DEVNULL, creationflags=CREATE_NO_WINDOW)
    except Exception as e:
        return (-1, b"", str(e))
    while True:
        try:
            out, err = p.communicate(timeout=0.5)
            return (p.returncode, out, err.decode("utf-8", errors="ignore"))
        except subprocess.TimeoutExpired:
            if cancelled and cancelled():
                p.kill()
                p.communicate()
                raise Cancelled()


def probe(ffmpeg, path):
    _, _, err = run([ffmpeg, "-nostdin", "-hide_banner", "-i", path])
    info = {"dur": 0.0, "audio": "Audio:" in err, "video": False, "w": 0, "h": 0}
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", err)
    if m:
        info["dur"] = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    v = re.search(r"Video:.*?\b(\d{2,5})x(\d{2,5})\b", err)
    if v:
        info["video"] = True
        info["w"], info["h"] = int(v.group(1)), int(v.group(2))
    elif "Video:" in err:
        info["video"] = True
    return info


# ──────────────────────────────────────────────────────────────────────────────
#  История и Сохранение Настроек
# ──────────────────────────────────────────────────────────────────────────────
def _hkey(path):
    try:
        size = os.path.getsize(path)
    except OSError:
        size = 0
    return hashlib.sha1(f"{os.path.abspath(path)}|{size}".encode()).hexdigest()[:20]


def _ckey(path):
    try:
        st = os.stat(path)
        sig = f"{os.path.abspath(path)}|{st.st_size}|{int(st.st_mtime)}"
    except OSError:
        sig = os.path.abspath(path)
    return hashlib.sha1(sig.encode()).hexdigest()[:24]


class History:
    def __init__(self, path=None):
        self.path = path or HISTORY_FILE
        self.lock = threading.Lock()
        self.data = {}
        self.load()

    def load(self):
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                self.data = json.load(f).get("files", {})
        except Exception:
            self.data = {}

    def save(self):
        try:
            os.makedirs(os.path.dirname(self.path), exist_ok=True)
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({"version": 1, "files": self.data}, f, ensure_ascii=False)
            os.replace(tmp, self.path)
        except Exception:
            pass

    def ranges(self, media_path):
        rec = self.data.get(_hkey(media_path))
        return [(a, b) for a, b in rec["r"]] if rec else []

    def add(self, media_path, a, b):
        with self.lock:
            rec = self.data.setdefault(_hkey(media_path),
                                       {"p": os.path.basename(media_path), "r": []})
            rec["r"].append([round(a, 2), round(b, 2)])

    def count(self):
        return sum(len(v["r"]) for v in self.data.values())

    def clear(self):
        self.data = {}
        self.save()


def save_settings_to_disk(s: Settings):
    try:
        os.makedirs(APP_DIR, exist_ok=True)
        data = {k: v for k, v in s.__dict__.items() if k != "files"}
        # PyInstaller --onefile unpacks bundled data into a temporary folder on each launch.
        # Never persist that temporary path; an empty path means "use the built-in track".
        if is_bundled_matador_music(s.matador_music_path):
            data["matador_music_path"] = ""
        tmp = SETTINGS_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, SETTINGS_FILE)
    except Exception:
        pass


def load_settings_from_disk() -> Settings:
    s = Settings()
    if os.path.exists(SETTINGS_FILE):
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                for k, v in data.items():
                    if hasattr(s, k):
                        setattr(s, k, v)
        except Exception:
            pass
    # Empty path means use the auto-saved project asset or the track embedded in the EXE.
    if not s.matador_music_path:
        s.matador_music_path = default_matador_music_path()
    return s


# ──────────────────────────────────────────────────────────────────────────────
#  Признаки: звук и видео
# ──────────────────────────────────────────────────────────────────────────────
def long_runs(mask, min_len):
    out = np.zeros(len(mask), dtype=bool)
    i = 0
    while i < len(mask):
        if mask[i]:
            j = i
            while j < len(mask) and mask[j]:
                j += 1
            if j - i >= min_len:
                out[i:j] = True
            i = j
        else:
            i += 1
    return out


def fit_len(a, n, fill):
    if a is None:
        return None
    if len(a) >= n:
        return a[:n]
    return np.concatenate([a, np.full(n - len(a), fill, dtype=a.dtype)])


def audio_features(ffmpeg, path, cancelled):
    # PCM пишется во временный файл и читается через memmap: длинная запись
    # не хранится целиком как bytes в оперативной памяти.
    tmp_pcm = tempfile.NamedTemporaryFile(suffix=".pcm", delete=False)
    tmp_path = tmp_pcm.name
    tmp_pcm.close()
    pcm = None
    try:
        code, _, _ = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-i", path, "-map", "0:a:0",
                          "-vn", "-ac", "1", "-ar", str(SR), "-f", "s16le", tmp_path], cancelled)
        if code != 0 or os.path.getsize(tmp_path) < SR * 4:
            return None
        pcm = np.memmap(tmp_path, dtype=np.int16, mode="r")
        n = int(SR * STEP)
        k = len(pcm) // n
        if k < 4:
            return None
        loud = np.empty(k, dtype=np.float32)
        mid_ratio = np.empty(k, dtype=np.float32)
        freqs = np.fft.rfftfreq(n, 1.0 / SR)
        b_low = (freqs >= 40) & (freqs < 250)
        b_mid = (freqs >= 300) & (freqs < 3400)
        b_high = freqs >= 3400
        hann = np.hanning(n).astype(np.float32)
        B = 800
        for b0 in range(0, k, B):
            blk = pcm[b0 * n:(b0 + B) * n]
            kk = len(blk) // n
            blk = blk[: kk * n].reshape(kk, n).astype(np.float32) / 32768.0
            rms = np.sqrt((blk ** 2).mean(axis=1))
            loud[b0:b0 + kk] = 20 * np.log10(rms + 1e-6)
            sp = np.abs(np.fft.rfft(blk * hann, axis=1)) ** 2
            el, em, eh = sp[:, b_low].sum(1), sp[:, b_mid].sum(1), sp[:, b_high].sum(1)
            mid_ratio[b0:b0 + kk] = em / (el + em + eh + 1e-9)
        padded = np.concatenate([np.full(6, loud[0], dtype=np.float32), loud])
        win = np.lib.stride_tricks.sliding_window_view(padded[:-1], 6)
        burst = np.maximum(0.0, loud - np.median(win, axis=1)).astype(np.float32)
        speech = long_runs((mid_ratio > 0.62) & (burst < 5.0) & (loud > -45.0), 3)
        return {"loud": loud, "burst": burst, "speech": speech.astype(np.uint8)}
    finally:
        if pcm is not None:
            del pcm
        try:
            os.unlink(tmp_path)
        except OSError:
            pass


def video_coarse(ffmpeg, path, cancelled):
    base = [ffmpeg, "-nostdin", "-v", "info", "-skip_frame", "nokey", "-i", path, "-an",
            "-vf", f"showinfo,scale={SW}:{SH}:flags=area,format=gray", "-f", "rawvideo"]
    out = err = None
    for flag in (["-fps_mode", "passthrough"], ["-vsync", "0"]):
        code, out, err = run(base + flag + ["-"], cancelled)
        if code == 0:
            break
    else:
        return None
    times = [float(x) for line in err.splitlines() if "Parsed_showinfo" in line
             for x in re.findall(r"pts_time:\s*(-?[0-9.]+)", line)]
    fs = SW * SH
    m = min(len(times), len(out) // fs)
    if m < 3:
        return None
    t = np.array(times[:m], dtype=np.float64)
    fr = np.frombuffer(out[: m * fs], dtype=np.uint8).reshape(m, fs).astype(np.float32)
    bright = fr.mean(axis=1)
    diff = np.zeros(m, dtype=np.float32)
    diff[1:] = np.abs(np.diff(fr, axis=0)).mean(axis=1)
    dt = np.zeros(m)
    dt[1:] = np.diff(t)
    dt = np.clip(dt, 0.25, None)
    rate = (diff / np.sqrt(dt)).astype(np.float32)
    rate[0] = rate[1]
    mid = np.zeros(m)
    mid[1:] = (t[1:] + t[:-1]) / 2
    mid[0] = t[0]
    return {"vt": mid, "vr": rate, "vb": bright}


def coarse_to_grid(d, n):
    g = (np.arange(n) + 0.5) * STEP
    order = np.argsort(d["vt"])
    vt, vr, vb = d["vt"][order], d["vr"][order], d["vb"][order]
    motion = np.interp(g, vt, vr).astype(np.float32)
    bright = np.interp(g, vt, vb).astype(np.float32)
    thr = max(45.0, 3.0 * float(np.percentile(vr, 90)))
    scene = np.zeros(n, dtype=bool)
    for tt in vt[vr > thr]:
        i = int(tt / STEP)
        if 0 <= i < n:
            scene[i] = True
    return motion, bright, scene


def get_features(ffmpeg, path, game, info, s, cancelled):
    os.makedirs(CACHE_DIR, exist_ok=True)
    cpath = os.path.join(CACHE_DIR, _ckey(path) + ".npz")
    data = {}
    if os.path.exists(cpath):
        try:
            with np.load(cpath) as z:
                if int(z["ver"]) == CACHE_VERSION:
                    data = {k: z[k] for k in z.files}
        except Exception:
            data = {}
    changed = False
    if info["audio"] and int(data.get("has_a", 0)) == 0:
        af = audio_features(ffmpeg, path, cancelled)
        if af:
            data.update(af)
            data["has_a"] = np.array(1)
        else:
            data["has_a"] = np.array(2)
        changed = True
    audio_ok = int(data.get("has_a", 0)) == 1
    need_video = (s.events.get("motion") or s.events.get("scene") or not audio_ok)
    if need_video and info["video"] and int(data.get("has_v", 0)) == 0:
        vc = video_coarse(ffmpeg, path, cancelled)
        if vc:
            data.update(vc)
            data["has_v"] = np.array(1)
        else:
            data["has_v"] = np.array(2)
        changed = True
    if changed:
        data["ver"] = np.array(CACHE_VERSION)
        try:
            tmp = cpath[:-4] + ".tmp.npz"
            np.savez_compressed(tmp, **data)
            os.replace(tmp, cpath)
        except Exception:
            pass

    n = int(info["dur"] / STEP)
    f = FileFeatures(path, game, info["dur"], n)
    if audio_ok:
        f.loud = fit_len(data["loud"].astype(np.float32), n, -80.0)
        f.burst = fit_len(data["burst"].astype(np.float32), n, 0.0)
        f.speech = fit_len(data["speech"].astype(bool), n, False)
    if int(data.get("has_v", 0)) == 1 and n > 0:
        f.motion, f.bright, f.scene = coarse_to_grid(data, n)
    return f


# ──────────────────────────────────────────────────────────────────────────────
#  Оценка окон и поиск моментов
# ──────────────────────────────────────────────────────────────────────────────
def window_scores(f, s):
    n = f.n
    comps = {}
    if f.loud is not None:
        l = np.clip((f.loud + 48.0) / 30.0, 0, 1)
        b = np.clip(f.burst / 10.0, 0, 1)
        if s.suppress_speech:
            l = np.where(f.speech, l * 0.45, l)
            b = np.where(f.speech, b * 0.6, b)
        comps["loud"], comps["burst"] = l.astype(np.float32), b.astype(np.float32)
    if f.motion is not None:
        ref = max(float(np.percentile(f.motion, 90)), 10.0)
        comps["motion"] = np.clip(f.motion / ref, 0, 1).astype(np.float32)
        comps["scene"] = f.scene.astype(np.float32)
    active = [k for k in comps if s.events.get(k)]
    if not active:
        return None
    wsum = sum(WEIGHTS[k] for k in active)
    S = sum(WEIGHTS[k] * comps[k] for k in active) / wsum
    agree = sum((comps[k] > 0.5).astype(np.float32) for k in active) / len(active)
    S = (0.8 * S + 0.2 * agree).astype(np.float32)
    bad = np.zeros(n, dtype=bool)
    if s.clean_audio and f.loud is not None:
        bad |= f.loud < SILENCE_DB
    if s.skip_black and f.bright is not None:
        bad |= f.bright < BLACK_LUMA
    if s.skip_frozen and f.motion is not None:
        bad |= long_runs(f.motion < FREEZE_RATE, 3)
    S = np.where(bad, S * 0.2, S).astype(np.float32)
    return S, comps, active, bad


def snap(t, lo, hi, ls, scene, pen=1.5):
    n = len(ls) if ls is not None else (len(scene) if scene is not None else 0)
    if n == 0 or hi <= lo:
        return t
    ia, ib = max(0, int(lo / STEP)), min(n - 1, int(hi / STEP))
    best_t, best_c = t, None
    for i in range(ia, ib + 1):
        tt = i * STEP
        c = (float(ls[i]) if ls is not None else 0.0) + pen * abs(tt - t)
        if scene is not None and scene[i]:
            c -= 8.0
        if best_c is None or c < best_c:
            best_t, best_c = tt, c
    return best_t


def clip_against_used(start, end, core_s, core_e, used):
    for us, ue in used:
        if min(ue, core_e + 1.0) - max(us, core_s - 1.0) > 0:
            return None
        if ue > start and us < end:
            if us <= start:
                start = ue + 0.3
            elif ue >= end:
                end = us - 0.3
            else:
                return None
    return start, end


def episodes_from_features(f, s, used):
    res = window_scores(f, s)
    if res is None or f.n < 8:
        return []
    S, comps, active, bad = res
    n = f.n
    trim = s.trim_sec if s.trim_on else 0.0
    S[: int(math.ceil(trim / STEP))] = 0
    for us, ue in used:
        S[max(0, int((us - 1.0) / STEP)): min(n, int((ue + 1.0) / STEP) + 1)] = 0
    Ss = np.convolve(S, np.array([0.25, 0.5, 0.25], dtype=np.float32), mode="same")
    T = max(MIN_EVENT, float(np.median(Ss)) + 0.15)

    regions, claimed = [], np.zeros(n, dtype=bool)
    for i in np.argsort(-Ss):
        if Ss[i] < T or len(regions) >= 60:
            break
        if claimed[i]:
            continue
        thr = max(0.8 * T, 0.5 * float(Ss[i]))
        l = r = int(i)
        miss, j = 0, i - 1
        while j >= 0:
            if Ss[j] >= thr:
                l, miss = j, 0
            else:
                miss += 1
                if miss > 4:
                    break
            j -= 1
        miss, j = 0, i + 1
        while j < n:
            if Ss[j] >= thr:
                r, miss = j, 0
            else:
                miss += 1
                if miss > 4:
                    break
            j += 1
        claimed[l:r + 1] = True
        regions.append([l, r])

    regions.sort()
    gap_w = int((s.pre + s.post) / STEP) + 2
    merged = []
    for l, r in regions:
        if merged and l - merged[-1][1] <= gap_w:
            merged[-1][1] = max(merged[-1][1], r)
        else:
            merged.append([l, r])

    ls = np.convolve(f.loud, np.ones(2, dtype=np.float32) / 2, mode="same") \
        if f.loud is not None else None
    scene = f.scene if f.scene is not None else None
    out = []
    max_core = max(4.0, s.max_len - (s.pre + s.post))
    for l, r in merged:
        seg = Ss[l:r + 1]
        p = l + int(np.argmax(seg))
        tp = p * STEP
        core_s, core_e = l * STEP, (r + 1) * STEP
        if core_e - core_s > max_core:
            core_s = max(core_s, tp - 0.4 * max_core)
            core_e = min(core_e, core_s + max_core)
        start, end = core_s - s.pre, core_e + s.post
        start, end = max(start, trim), min(end, f.dur)
        if end - start < s.min_len:
            need = s.min_len - (end - start)
            start = max(trim, start - need / 2)
            end = min(f.dur, end + need / 2)
            if end - start < s.min_len:
                start = max(trim, end - s.min_len)
                end = min(f.dur, start + s.min_len)
        start = snap(start, start - 1.5, min(start + 1.0, core_s - MIN_PAD), ls, scene)
        end = snap(end, max(end - 1.0, core_e + MIN_PAD), end + 3.0, ls, scene)
        start, end = max(start, trim), min(end, f.dur)
        if used:
            c = clip_against_used(start, end, core_s, core_e, used)
            if c is None:
                continue
            start, end = c
        if end - start < max(4.0, s.min_len * 0.6):
            continue
        agree = float(np.mean([comps[k][l:r + 1].max() > 0.5 for k in active]))
        score = 0.55 * float(Ss[p]) + 0.25 * float(seg.mean()) + 0.20 * agree
        vals = sorted(((float(comps[k][l:r + 1].mean()) * WEIGHTS[k], k) for k in active),
                      reverse=True)
        tags = [EVENT_LABELS[k] for v, k in vals[:2] if v > 0.25 * vals[0][0] and v > 0.05]
        out.append(Episode(f.path, f.game, float(start), float(end), float(core_s), float(core_e),
                           float(score),
                           " + ".join(tags) or "событие",
                           f.loud is not None, 0, 0, f.dur))
    out.sort(key=lambda e: -e.score)
    return out[:8]


# ──────────────────────────────────────────────────────────────────────────────
#  Детальная проверка
# ──────────────────────────────────────────────────────────────────────────────
FINE_FPS = 4
ENV_HOP = 0.01
HAVE_WHISPER = importlib.util.find_spec("faster_whisper") is not None
_wh_model = None
_wh_model_size = None
_wh_lock = threading.Lock()
_wh_run_lock = threading.Lock()


def video_fine(ffmpeg, path, a, length, cancelled):
    code, out, _ = run([ffmpeg, "-nostdin", "-v", "error", "-ss", f"{a:.3f}", "-t",
                        f"{length:.3f}", "-i", path, "-an", "-vf",
                        f"fps={FINE_FPS},scale={SW}:{SH}:flags=area,format=rgb24",
                        "-f", "rawvideo", "-"], cancelled)
    fs = SW * SH * 3
    if code != 0 or len(out) < fs * 6:
        return None
    m = len(out) // fs
    rgb = np.frombuffer(out[: m * fs], dtype=np.uint8).reshape(m, SH, SW, 3).astype(np.float32)
    gray = (rgb[..., 0] * 0.299 + rgb[..., 1] * 0.587 + rgb[..., 2] * 0.114).reshape(m, -1)
    d = np.abs(np.diff(gray, axis=0))
    motion = np.zeros(m, dtype=np.float32)
    motion[1:] = d.mean(axis=1)
    motion[0] = motion[1]
    bm = np.zeros((SH, SW), dtype=bool)
    bm[:4, :] = bm[-4:, :] = True
    bm[:, :6] = bm[:, -6:] = True
    red = (rgb[..., 0] - (rgb[..., 1] + rgb[..., 2]) / 2)[:, bm].mean(axis=1)
    return {"bright": gray.mean(axis=1), "motion": motion, "red": red,
            "colw": d.reshape(m - 1, SH, SW).mean(axis=(0, 1))}


def visual_reaction(fv, ep):
    mot, br, rd = fv["motion"], fv["bright"], fv["red"]
    m = len(mot)
    i0 = max(0, int((ep.core_s - 0.5 - ep.start) * FINE_FPS))
    i1 = min(m, int((ep.core_e + 0.5 - ep.start) * FINE_FPS) + 1)
    if i1 <= i0:
        return 0.0
    guard = int(0.75 * FINE_FPS)
    base = np.concatenate([np.arange(0, max(0, i0 - guard)),
                           np.arange(min(m, i1 + guard), m)]).astype(int)
    if len(base) < 4:
        base = np.arange(m)
    core_mot = float(mot[i0:i1].max())
    lift = core_mot / (float(np.percentile(mot[base], 90)) + 0.5)
    r_motion = float(np.clip((lift - 1.2) / 1.0, 0, 1))
    if core_mot < 2.0:
        r_motion *= 0.3
    r_flash = float(np.clip((float(br[i0:i1].max()) - float(br[base].max())) / 20.0, 0, 1))
    r_hit = float(np.clip((float(rd[i0:i1].max()) - float(rd[base].max())) / 12.0, 0, 1))
    return max(r_motion, r_flash, r_hit)


def audio_env(ffmpeg, path, a, length, cancelled):
    a = max(0.0, a)
    code, out, _ = run([ffmpeg, "-nostdin", "-v", "error", "-ss", f"{a:.3f}", "-t",
                        f"{length:.3f}", "-i", path, "-map", "0:a:0", "-vn", "-ac", "1",
                        "-ar", "16000", "-f", "s16le", "-"], cancelled)
    if code != 0 or len(out) < 6400:
        return None
    pcm = np.frombuffer(out[: len(out) // 2 * 2], dtype=np.int16).astype(np.float32) / 32768.0
    k = len(pcm) // 160
    x = pcm[: k * 160].reshape(k, 160)
    return (20 * np.log10(np.sqrt((x ** 2).mean(axis=1)) + 1e-6)).astype(np.float32)


def pause_cut(env, a, t, lo, hi, kind):
    if hi <= lo or env is None:
        return t
    i_lo, i_hi = max(0, int((lo - a) / ENV_HOP)), min(len(env) - 1, int((hi - a) / ENV_HOP))
    if i_hi <= i_lo:
        return t
    seg = env[i_lo:i_hi + 1]
    j0, j1 = max(0, int((t - 3 - a) / ENV_HOP)), min(len(env), int((t + 3 - a) / ENV_HOP))
    ref = float(np.percentile(env[j0:j1], 90)) if j1 > j0 else float(seg.max())
    thr = max(ref - 20.0, -58.0)
    quiet = seg < thr
    best, i = None, 0
    while i < len(quiet):
        if quiet[i]:
            j = i
            while j < len(quiet) and quiet[j]:
                j += 1
            L = (j - i) * ENV_HOP
            if L >= 0.12:
                ps, pe = a + (i_lo + i) * ENV_HOP, a + (i_lo + j) * ENV_HOP
                cut = (pe - min(0.08, L / 2)) if kind == "start" else (ps + min(0.14, L / 2))
                cost = abs(cut - t) - 0.4 * min(L, 0.6)
                if best is None or cost < best[0]:
                    best = (cost, cut)
            i = j
        else:
            i += 1
    if best:
        return best[1]
    sm = np.convolve(seg, np.ones(5, dtype=np.float32) / 5, mode="same")
    pen = 6.0 * np.abs(lo + np.arange(len(sm)) * ENV_HOP - t)
    return lo + int(np.argmin(sm + pen)) * ENV_HOP


def refine_cuts(ffmpeg, path, start, end, core_s, core_e, trim, fdur, cancelled):
    a, b = max(0.0, start - 3.0), min(fdur, end + 4.0)
    env = audio_env(ffmpeg, path, a, b - a, cancelled)
    if env is None:
        return start, end, 0.5, 0.5
    ns = pause_cut(env, a, start, max(trim, start - 2.0, a), min(start + 1.0, core_s - 1.0), "start")
    ne = pause_cut(env, a, end, max(end - 1.0, core_e + 1.0), min(end + 2.5, b - 0.05), "end")
    ns, ne = max(trim, ns), min(fdur, ne)

    def energy(t0, t1):
        i0, i1 = max(0, int((t0 - a) / ENV_HOP)), min(len(env), int((t1 - a) / ENV_HOP))
        if i1 <= i0:
            return 0.5
        return float(np.clip((float(env[i0:i1].mean()) + 50.0) / 35.0, 0, 1))
    return ns, ne, energy(ns, ns + 1.0), energy(ne - 1.0, ne)


def get_whisper(model_size="small"):
    global _wh_model, _wh_model_size
    with _wh_lock:
        if _wh_model is None or _wh_model_size != model_size:
            from faster_whisper import WhisperModel
            _wh_model = WhisperModel(model_size, device="cpu", compute_type="int8",
                                     cpu_threads=1, num_workers=1)
            _wh_model_size = model_size
        return _wh_model


def transcribe(ffmpeg, path, a, dur, lang, cancelled):
    tmpf = tempfile.NamedTemporaryFile(suffix=".wav", delete=False)
    tmpf.close()
    try:
        code, _, _ = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-ss", f"{a:.3f}", "-t",
                          f"{dur:.3f}", "-i", path, "-map", "0:a:0", "-vn", "-ac", "1",
                          "-ar", "16000", tmpf.name], cancelled)
        if code != 0:
            return []
        words = []
        with _wh_run_lock:
            model = get_whisper()
            segs, _ = model.transcribe(tmpf.name, language=None if lang == "auto" else lang,
                                       word_timestamps=True, vad_filter=True)
            for sg in segs:
                for w in (sg.words or []):
                    words.append((a + w.start, a + w.end, w.word.strip()))
        return words
    finally:
        try:
            os.unlink(tmpf.name)
        except OSError:
            pass


def snap_to_words(start, end, words):
    ns, ne = start, end
    for w0, w1, _ in words:
        if w0 < ns < w1:
            ns = w0 - 0.12 if ns - w0 < (w1 - w0) / 2 else w1 + 0.10
        if w0 < ne < w1:
            ne = w1 + 0.15 if w1 - ne < (w1 - w0) / 2 else w0 - 0.05
    return ns, ne


def speech_pass(ffmpeg, ep, s, cancelled, adjust):
    a, b = max(0.0, ep.start - 1.5), min(ep.file_dur, ep.end + 1.5)
    words = transcribe(ffmpeg, ep.path, a, b - a, s.caption_lang, cancelled)
    ns, ne = ep.start, ep.end
    if adjust and not ep.manual and words:
        ns, ne = snap_to_words(ns, ne, words)
        ns = max(0.0, min(ns, ep.core_s - 1.0))
        ne = min(ep.file_dur, max(ne, ep.core_e + 1.0))
    return replace(ep, start=ns, end=ne, words=words, words_rng=(a, b))


def verify_episode(ffmpeg, ep, s, info, cancelled):
    res = video_fine(ffmpeg, ep.path, ep.start, ep.dur, cancelled)
    if res is None:
        return None, "не удалось декодировать видео"
    bright, motion = res["bright"], res["motion"]
    bad = np.zeros(len(bright), dtype=bool)
    if s.skip_black:
        bad |= bright < BLACK_LUMA
    if s.skip_frozen:
        bad |= long_runs(motion < 0.2, 6)
    if bad.mean() > MAX_BAD_FRACTION:
        return None, "чёрные/статичные кадры"
    start, end = ep.start, ep.end
    i = 0
    while i < len(bad) and bad[i] and i / FINE_FPS < 3.0:
        i += 1
    j = 0
    while j < len(bad) and bad[len(bad) - 1 - j] and j / FINE_FPS < 3.0:
        j += 1
    start = min(start + i / FINE_FPS, ep.core_s - 1.0)
    end = max(end - j / FINE_FPS, ep.core_e + 1.0)
    if end - start < max(4.0, s.min_len * 0.6):
        return None, "слишком короткий после обрезки краёв"

    react = visual_reaction(res, ep)
    if s.require_visual and react < s.visual_level:
        return None, f"нет реакции на экране ({react:.2f}) — звук без действий"

    e_s = e_e = 0.5
    if s.snap_pauses and ep.has_audio:
        trim = s.trim_sec if s.trim_on else 0.0
        start, end, e_s, e_e = refine_cuts(ffmpeg, ep.path, start, end, ep.core_s, ep.core_e,
                                           trim, ep.file_dur, cancelled)
    w = res["colw"] - res["colw"].min()
    cx = 0.5
    if w.sum() > 1e-3:
        cx = float((w * (np.arange(SW) + 0.5) / SW).sum() / w.sum())
    cx = min(0.85, max(0.15, 0.5 + (cx - 0.5) * 0.7))
    new = replace(ep, start=max(0.0, start), end=min(ep.file_dur, end), cx=cx,
                  src_w=info[0], src_h=info[1], reaction=react, e_start=e_s, e_end=e_e,
                  eff=ep.eff + 0.2 * react)
    if s.captions and HAVE_WHISPER and ep.has_audio:
        try:
            new = speech_pass(ffmpeg, new, s, cancelled, adjust=True)
        except Exception:
            pass
    return new, ""


# ──────────────────────────────────────────────────────────────────────────────
#  Выбор и планирование
# ──────────────────────────────────────────────────────────────────────────────
def scan_root(root, exclude_dir=""):
    games = defaultdict(list)
    ex = os.path.realpath(exclude_dir) if exclude_dir else None

    def skipped(path):
        rp = os.path.realpath(path)
        return bool(ex) and (rp == ex or rp.startswith(ex + os.sep))
    for name in sorted(os.listdir(root)):
        folder = os.path.join(root, name)
        if not os.path.isdir(folder) or name.startswith("_") or skipped(folder):
            continue
        gname = detect_game_name(folder, root)
        for dp, dns, fns in os.walk(folder):
            dns[:] = [d for d in dns if not d.startswith("_") and not skipped(os.path.join(dp, d))]
            for fn in fns:
                full = os.path.join(dp, fn)
                try:
                    if (fn.lower().endswith(VIDEO_EXT) and not fn.startswith("automix_")
                            and os.path.getsize(full) > 1024):
                        games[gname].append(full)
                except OSError:
                    pass
    return dict(games)


def collect_sources(s):
    if s.files:
        games = defaultdict(list)
        for p in s.files:
            if os.path.isfile(p):
                games[detect_game_name(p, s.root_dir)].append(p)
        return dict(games)
    return scan_root(s.root_dir, s.out_dir)


def scan_order(games):
    def mt(p):
        try:
            return os.path.getmtime(p)
        except OSError:
            return 0
    queues = {}
    for g, files in games.items():
        fs = sorted(files, key=lambda p: (mt(p), p))
        q, i, j = [], 0, len(fs) - 1
        while i <= j:
            q.append(fs[i]); i += 1
            if i <= j:
                q.append(fs[j]); j -= 1
        queues[g] = deque(q)
    order = []
    while any(queues.values()):
        for g in list(queues):
            if queues[g]:
                order.append((g, queues[g].popleft()))
    return order


def shrink(e, room):
    core = e.core_e - e.core_s
    avail = room - core
    if avail < 2 * MIN_PAD:
        return None
    pre, post = e.core_s - e.start, e.end - e.core_e
    tot = pre + post
    if tot <= 0:
        return None
    k = min(1.0, avail / tot)
    pre, post = max(MIN_PAD, pre * k), max(MIN_PAD, post * k)
    if pre + post > avail:
        pre = post = avail / 2
    return replace(e, start=e.core_s - pre, end=e.core_e + post)


def overlaps_chosen(e, chosen):
    return any(c.path == e.path and min(c.end, e.end) - max(c.start, e.start) > -1.0
               for c in chosen)


def greedy(cands, s, budget, ngames):
    chosen, total = [], 0.0
    fc, gt = Counter(), Counter()
    quota = budget / ngames * 1.3 if (s.balance and ngames > 1) else 1e9
    for pass_i in (0, 1):
        for e in cands:
            if any(e is c for c in chosen):
                continue
            if fc[e.path] >= s.per_file_max or overlaps_chosen(e, chosen):
                continue
            if pass_i == 0 and gt[e.game] + e.dur > quota:
                continue
            e2 = e
            if e.dur > budget - total:
                e2 = shrink(e, budget - total)
                if e2 is None:
                    continue
            chosen.append(e2)
            total += e2.dur
            fc[e.path] += 1
            gt[e.game] += e2.dur
            if total >= budget * 0.98:
                return chosen
        if total >= budget * 0.9:
            break
    return chosen


def expand_to_fill(chosen, s):
    trim = s.trim_sec if s.trim_on else 0.0
    total = sum(e.dur for e in chosen)
    for _ in range(8):
        if total >= s.target * 0.95:
            break
        grew = False
        for idx in sorted(range(len(chosen)), key=lambda i: -chosen[i].score):
            e = chosen[idx]
            if (e.core_s - e.start) >= s.pre + 4 and (e.end - e.core_e) >= s.post + 4:
                continue
            ns, ne = max(trim, e.start - 1.0), min(e.file_dur, e.end + 1.0)
            probe_e = replace(e, start=ns, end=ne)
            others = [c for k, c in enumerate(chosen) if k != idx]
            if overlaps_chosen(probe_e, others) or total + (probe_e.dur - e.dur) > (
                    s.target if s.strict else s.target * 1.1):
                continue
            total += probe_e.dur - e.dur
            chosen[idx] = probe_e
            grew = True
        if not grew:
            break
    return chosen


def order_plan(chosen, s):
    if s.order.startswith("По силе"):
        return sorted(chosen, key=lambda e: -e.score)
    groups = defaultdict(list)
    for e in chosen:
        groups[(e.game, e.path)].append(e)
    for g in groups.values():
        g.sort(key=lambda e: e.start)
    gscore = lambda g: max(e.score for e in g)
    bygame = defaultdict(list)
    for (game, _), g in groups.items():
        bygame[game].append(g)
    for lst in bygame.values():
        lst.sort(key=gscore, reverse=True)
    games = sorted(bygame, key=lambda gm: -max(gscore(g) for g in bygame[gm]))
    out = []
    if s.order.startswith("Блоки"):
        for gm in games:
            for g in bygame[gm]:
                out += g
    else:
        queues = {gm: deque(bygame[gm]) for gm in games}
        while any(queues.values()):
            for gm in games:
                if queues[gm]:
                    out += queues[gm].popleft()
    return out


def review_plan(plan, s, rep):
    fixed = 0
    budget = s.target if s.strict else s.target * 1.1
    for e in list(plan):
        if e.dur < 3.0:
            plan.remove(e)
            fixed += 1
    while sum(e.dur for e in plan) > budget * 1.02 and len(plan) > 1:
        weakest = min(plan, key=lambda e: e.score)
        plan.remove(weakest)
        fixed += 1
    rep.log("Самопроверка плана: " + ("исправлено проблем — %d" % fixed if fixed
                                      else "проблем не найдено"))
    return plan


# ──────────────────────────────────────────────────────────────────────────────
#  Рендер
# ──────────────────────────────────────────────────────────────────────────────
def detect_hw_encoder(ffmpeg):
    _, out, err = run([ffmpeg, "-hide_banner", "-encoders"])
    listing = out.decode("utf-8", errors="ignore") + err
    for enc in ("h264_nvenc", "h264_qsv", "h264_amf", "h264_videotoolbox"):
        if enc not in listing:
            continue
        code, _, _ = run([ffmpeg, "-nostdin", "-v", "error", "-f", "lavfi", "-i",
                          "color=c=black:s=256x256:d=0.2", "-frames:v", "1",
                          "-pix_fmt", "yuv420p", "-c:v", enc, "-f", "null", "-"])
        if code == 0:
            return enc
    return None


def vcodec_args(enc, quality):
    crf = {"Высокое": 17, "Обычное": 21, "Быстрое": 24, "Промежуточное": 12}.get(quality, 19)
    if enc == "h264_nvenc":
        return ["-c:v", enc, "-preset", "p5", "-rc", "vbr", "-cq", str(crf + 2), "-b:v", "0", "-threads", str(FFMPEG_CODEC_THREADS)]
    if enc == "h264_qsv":
        return ["-c:v", enc, "-global_quality", str(crf + 2), "-threads", str(FFMPEG_CODEC_THREADS)]
    if enc == "h264_amf":
        return ["-c:v", enc, "-quality", "quality", "-rc", "cqp",
                "-qp_i", str(crf + 2), "-qp_p", str(crf + 3), "-threads", str(FFMPEG_CODEC_THREADS)]
    if enc == "h264_videotoolbox":
        return ["-c:v", enc, "-b:v", "14M", "-threads", str(FFMPEG_CODEC_THREADS)]
    # CRF controls visual quality; veryfast substantially reduces CPU time at the same CRF.
    preset = {"Высокое": "veryfast", "Промежуточное": "ultrafast"}.get(quality, "veryfast")
    return ["-c:v", "libx264", "-preset", preset, "-crf", str(crf), "-threads", str(FFMPEG_CODEC_THREADS)]


def find_font():
    for p in (r"C:\Windows\Fonts\segoeuib.ttf", r"C:\Windows\Fonts\arialbd.ttf",
              r"C:\Windows\Fonts\arial.ttf", "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
              "/Library/Fonts/Arial Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
              "/usr/share/fonts/noto/NotoSans-Bold.ttf"):
        if os.path.exists(p):
            return p
    return None


def make_text_png(text, path, W, kind):
    if Image is None or not text.strip():
        return None
    size = int(W * (0.062 if kind == "caption" else 0.020))
    fp = find_font()
    try:
        font = ImageFont.truetype(fp, size) if fp else ImageFont.load_default(size)
    except Exception:
        font = ImageFont.load_default()
    probe_d = ImageDraw.Draw(Image.new("RGBA", (10, 10)))
    maxw, lines, cur = int(W * 0.88), [], ""
    for word in text.split():
        t = (cur + " " + word).strip()
        if probe_d.textlength(t, font=font) <= maxw or not cur:
            cur = t
        else:
            lines.append(cur)
            cur = word
    lines.append(cur)
    stroke = max(2, size // 11) if kind == "caption" else 0
    pad = int(size * 0.5) if kind == "title" else stroke + 6
    line_h = int(size * 1.22)
    widths = [int(probe_d.textlength(l, font=font)) for l in lines]
    tw, th = max(widths) + 2 * pad, line_h * len(lines) + 2 * pad
    img = Image.new("RGBA", (tw, th), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    if kind == "title":
        d.rounded_rectangle((0, 0, tw - 1, th - 1), radius=int(size * 0.4), fill=(0, 0, 0, 160))
    for k, l in enumerate(lines):
        d.text(((tw - widths[k]) // 2, pad + k * line_h), l, font=font, fill=(255, 255, 255, 255),
               stroke_width=stroke, stroke_fill=(0, 0, 0, 255))
    img.save(path)
    return tw, th


def caption_chunks(words, ep):
    inside = [w for w in words if w[0] >= ep.start - 0.05 and w[1] <= ep.end + 0.05]
    chunks, cur = [], []
    for w in inside:
        if cur and (len(cur) >= 4 or w[1] - cur[0][0] > 2.4 or w[0] - cur[-1][1] > 0.6
                    or cur[-1][2][-1:] in ".!?…"):
            chunks.append(cur)
            cur = []
        cur.append(w)
    if cur:
        chunks.append(cur)
    return [(max(0.0, c[0][0] - ep.start), min(ep.dur, c[-1][1] - ep.start + 0.12),
             " ".join(x[2] for x in c)) for c in chunks]


def prepare_overlays(ep, s, tmp, key):
    ov = []
    ycap = "H*0.70" if s.height > s.width else "H*0.80"
    if ep.title:
        p = os.path.join(tmp, f"{key}_title.png")
        if make_text_png(ep.title, p, s.width, "title"):
            ov.append((p, "W*0.05", "H*0.07", 0.25, min(ep.dur, 2.6)))
    if s.captions and ep.words:
        for k, (t0, t1, txt) in enumerate(caption_chunks(ep.words, ep)):
            p = os.path.join(tmp, f"{key}_cap{k:02d}.png")
            if make_text_png(txt, p, s.width, "caption"):
                ov.append((p, "(W-w)/2", ycap, t0, t1))
    return ov


def base_graph(ep, s):
    W, H = s.width, s.height
    sw, sh = ep.src_w, ep.src_h
    mode = s.frame_mode
    if sw and sh and abs(sw / sh - W / H) < 0.02:
        return f"[0:v]scale={W}:{H}:flags=lanczos[vb]"
    if mode.startswith("Размытый"):
        bw, bh = max(2, (W // 8) // 2 * 2), max(2, (H // 8) // 2 * 2)
        return (f"[0:v]split=2[a][b];"
                f"[a]scale={bw}:{bh}:force_original_aspect_ratio=increase,crop={bw}:{bh},"
                f"boxblur=3:1,scale={W}:{H}[bg];"
                f"[b]scale={W}:{H}:force_original_aspect_ratio=decrease:flags=lanczos[fg];"
                f"[bg][fg]overlay=(W-w)/2:(H-h)/2[vb]")
    if mode.startswith("Чёрные"):
        return (f"[0:v]scale={W}:{H}:force_original_aspect_ratio=decrease:flags=lanczos,"
                f"pad={W}:{H}:(ow-iw)/2:(oh-ih)/2:black[vb]")
    if mode.startswith("Умный") and sw and sh:
        sc_w = int(round(sw * H / sh))
        if sc_w >= W:
            x = int(min(max(ep.cx * sc_w - W / 2, 0), sc_w - W)) // 2 * 2
            return f"[0:v]scale=-2:{H}:flags=lanczos,crop={W}:{H}:{x}:0[vb]"
    return (f"[0:v]scale={W}:{H}:force_original_aspect_ratio=increase:flags=lanczos,"
            f"crop={W}:{H}[vb]")


def zoom_filter(ep, W, H):
    tc = max(0.0, ep.core_s - ep.start - 0.2)
    te = max(tc + 0.5, ep.core_e - ep.start)
    z = (f"(1+0.07*min(max((t-{tc:.2f})/0.35,0),1)"
         f"*(1-min(max((t-{te:.2f})/0.6,0),1)))")
    return (f"scale=w='trunc({W}*{z}/2)*2':h='trunc({H}*{z}/2)*2':eval=frame:flags=bilinear,"
            f"crop={W}:{H}")


def build_graph(ep, s, ovl, first_idx, fx, laser_idx=None, laser_offset=0.0, laser_box=None):
    g = [base_graph(ep, s)]
    cur = "[vb]"
    if fx and ep.zoom:
        g.append(f"{cur}{zoom_filter(ep, s.width, s.height)}[vz]")
        cur = "[vz]"
    for k, (_, x, y, t0, t1) in enumerate(ovl):
        g.append(f"[{first_idx + k}:v]format=rgba[ov{k}]")
        g.append(f"{cur}[ov{k}]overlay=x={x}:y={y}:enable='between(t,{t0:.2f},{t1:.2f})'[o{k}]")
        cur = f"[o{k}]"
    if laser_idx is not None:
        # Laser PNGs are stored at half output resolution to reduce disk I/O and PNG work.
        # Слой может начинаться не с 0-й секунды клипа (PNG пишутся только там, где есть метки):
        # setpts сдвигает его на laser_offset секунд, до этого момента overlay пропускает кадр без лазеров.
        shift = f"setpts=PTS+{laser_offset:.4f}/TB," if laser_offset > 1e-6 else ""
        if laser_box:
            # Ручной слой хранится только в рамке, где вообще бывают лучи: меньше PNG, масштабирования и наложения.
            bx, by, bw, bh = laser_box
            g.append(f"[{laser_idx}:v]{shift}scale={bw}:{bh}:flags=bilinear,format=rgba[laser]")
            g.append(f"{cur}[laser]overlay=x={bx}:y={by}:eof_action=pass:repeatlast=0[laserout]")
        else:
            g.append(f"[{laser_idx}:v]{shift}scale={s.width}:{s.height}:flags=bilinear,format=rgba[laser]")
            g.append(f"{cur}[laser]overlay=eof_action=pass:repeatlast=0[laserout]")
        cur = "[laserout]"
    g.append(f"{cur}setsar=1,fps={s.fps},format=yuv420p[v]")
    return ";".join(g)


def _map_source_to_output(x, y, ep, s):
    sw, sh, W, H = ep.src_w, ep.src_h, s.width, s.height
    if not sw or not sh:
        return x, y
    mode = s.frame_mode
    if abs(sw / sh - W / H) < 0.02:
        return x * W / sw, y * H / sh
    if mode.startswith("Размытый") or mode.startswith("Чёрные"):
        scale = min(W / sw, H / sh)
        return x * scale + (W - sw * scale) / 2, y * scale + (H - sh * scale) / 2
    if mode.startswith("Умный"):
        scaled_w = int(round(sw * H / sh))
        if scaled_w >= W:
            scale = H / sh
            crop_x = int(min(max(ep.cx * scaled_w - W / 2, 0), scaled_w - W)) // 2 * 2
            return x * scale - crop_x, y * scale
    scale = max(W / sw, H / sh)
    return x * scale - (sw * scale - W) / 2, y * scale - (sh * scale - H) / 2


@dataclass
class LaserLayer:
    """Слой лазеров одного клипа: что подать FFmpeg и что проверять после экспорта."""
    pattern: str
    fps: float
    offset: float = 0.0           # секунды от начала клипа до первого PNG
    frames: int = 0
    expected: bool = False        # ручные лазеры должны быть видны в итоговом клипе
    probe_times: list = field(default_factory=list)   # моменты клипа (с), где лучи точно есть
    ep: object = None             # эпизод с (возможно) скорректированным кадрированием
    stats: dict = field(default_factory=dict)
    box: object = None            # (x, y, w, h) в пикселях итогового кадра; None — слой на весь кадр


def manual_layer_fps(ep, s, rows):
    """Выбирает частоту PNG-слоя по движению глаз И ручных направляющих, максимум 12 fps."""
    step, t, prev, fastest = 1.0 / 24, ep.start, None, 0.0
    while t < ep.end:
        sample = manual_laser_sample_from_rows(rows, t)
        if sample and sample.get("points"):
            source_points = list(sample["points"])
            if sample.get("directions"):
                source_points += sample["directions"]
            cur = [_map_source_to_output(p[0] * ep.src_w, p[1] * ep.src_h, ep, s)
                   for p in source_points]
            if prev is not None and len(prev) == len(cur):
                fastest = max(fastest, max(math.hypot(a[0] - b[0], a[1] - b[1])
                                           for a, b in zip(cur, prev)) / step)
            prev = cur
        else:
            prev = None
        t += step
    need = int(math.ceil(fastest / (2.0 * LASER_TRACK_TOL_PX)))
    return float(min(LASER_MANUAL_FPS, max(LASER_MANUAL_MIN_FPS, need)))


def _smart_crop_window(ep, s):
    """(ширина после масштаба, левый край кропа), если применяется «Умный кроп»; иначе None.
    Формулы совпадают с base_graph() и _map_source_to_output()."""
    sw, sh, W, H = ep.src_w, ep.src_h, s.width, s.height
    if not sw or not sh or abs(sw / sh - W / H) < 0.02 or not s.frame_mode.startswith("Умный"):
        return None
    scaled_w = int(round(sw * H / sh))
    if scaled_w < W:
        return None
    crop_x = int(min(max(ep.cx * scaled_w - W / 2, 0), scaled_w - W)) // 2 * 2
    return scaled_w, crop_x


def fit_crop_to_manual_marks(ep, s, rows):
    """Сдвигает «Умный кроп» так, чтобы размеченные точки попали в кадр.
    Из 16:9 в 1080×1920 виден только ~32% ширины, а ep.cx считается по «активности», а не по меткам:
    раньше персонаж часто оказывался за краем, и лучи молча не рисовались.
    Возвращает (эпизод, описание сдвига или '')."""
    win = _smart_crop_window(ep, s)
    if not win or not rows:
        return ep, ""
    scaled_w, crop_x = win
    W = s.width
    xs, t = [], ep.start
    while t <= ep.end:
        pts = manual_laser_points_from_rows(rows, t)
        if pts:
            xs.extend(p[0] * scaled_w for p in pts)
        t += 0.25
    if not xs:
        return ep, ""
    margin = 0.04 * W

    def covered(cx_left):
        return sum(1 for x in xs if cx_left + margin <= x <= cx_left + W - margin)

    best_possible = len(xs)
    if covered(crop_x) == best_possible:
        return ep, ""                      # кадр уже содержит все точки — не трогаем
    mean_x = sum(xs) / len(xs)
    candidates = range(0, max(0, scaled_w - W) + 1, 8)
    scored = [(covered(c), -abs(c + W / 2 - mean_x), c) for c in candidates]
    best = max(scored)
    new_x = best[2] // 2 * 2
    if covered(new_x) <= covered(crop_x):
        return ep, ""
    new_cx = (new_x + W / 2) / scaled_w
    return replace(ep, cx=new_cx), (f"кроп сдвинут к меткам: cx {ep.cx:.2f} → {new_cx:.2f} "
                                    f"(в кадре {covered(new_x)} из {best_possible} точек вместо {covered(crop_x)})")


def laser_decide_reason(st):
    """Записывает в статистику клипа уровень (ok/info/warn/error) и понятную причину."""
    n = st.get("manual_keyframes", 0)
    clip = f'{st.get("clip_start", 0):.1f}–{st.get("clip_end", 0):.1f} с'
    mode = st.get("frame_mode", "")
    if st.get("annotation_error"):
        note = f" Файл меток не читается ({st['annotation_error']})."
    else:
        note = ""
    if st.get("manual_only"):
        matched, vis = st.get("manual_matched_frames", 0), st.get("manual_frames", 0)
        if matched == 0:
            st["level"], st["reason"] = "warn", (
                f"Метки заданы на {st['marked_from']:.1f}–{st['marked_to']:.1f} с, фрагмент {clip} лишь касается их края: "
                f"ни один кадр слоя не попал в интервал — лазеров нет.")
        elif vis == 0:
            st["level"], st["reason"] = "error", (
                f"Метки совпали по времени ({matched} кадров слоя), но все точки лежат за границей видимого кадра "
                f"(режим кадрирования «{mode}»). Лазеров НЕТ. Выбери «Умный кроп» (кадр сам сдвинется к меткам) "
                f"или «Размытый фон», либо отметь точки внутри видимой области.")
        elif vis < matched:
            st["level"], st["reason"] = "warn", (
                f"Лазеры видны в {vis} из {matched} размеченных кадров; в остальных точки вне кадра (режим «{mode}»)."
                + (f" {st['crop_shift']}." if st.get("crop_shift") else ""))
        else:
            extra = f" {st['crop_shift']}." if st.get("crop_shift") else ""
            single = (" Метка одна — лазеры показаны только ±%.2f с вокруг неё." % MANUAL_LASER_EDGE_TOL
                      if st.get("manual_keyframes_in_clip", 0) == 1 else "")
            st["level"], st["reason"] = "ok", (
                f"Лазеры включены по ручным меткам ({st.get('manual_keyframes_in_clip', 0)} в фрагменте): "
                f"видны с {st['visible_from']:.1f} по {st['visible_to']:.1f} с исходного видео "
                f"({st.get('layer_frames', 0)} кадров слоя, {st.get('layer_fps', 0):g} fps).{extra}{single}")
        return
    found = st.get("frames_with_lasers", 0)
    total = st.get("frames", 0)
    if n == 0:
        if found:
            st["level"], st["reason"] = "info", (
                f"Ручных меток нет — лазеры найдены автопоиском в {found} из {total} кадров.{note}")
        else:
            related = st.get("related_files") or []
            hint = ""
            if related:
                hint = (" Метки для файла с таким же именем лежат под другим путём: "
                        + "; ".join(f"{p} ({c} шт.)" for p, c in related[:3]) + ".")
            st["level"], st["reason"] = "warn", (
                f"Ручных меток для этого видео нет, а автопоиск (лица, глаза, силуэты) ничего не нашёл — "
                f"лазеров в этом фрагменте НЕТ. Разметь вручную: План → «🔴 Лазеры в этом кадре». "
                f"Ожидаемый файл меток: {st.get('annotation_file', '')} "
                f"({'найден' if st.get('annotation_file_exists') else 'не найден'}).{hint}{note}")
    else:
        gap = st.get("nearest_mark_gap")
        base = (f"Метки есть ({n}, интервал {st['marked_from']:.1f}–{st['marked_to']:.1f} с), но фрагмент {clip} "
                f"вне него (до ближайшей метки {gap:.1f} с) — ручные лазеры здесь не применяются; ")
        if found:
            st["level"], st["reason"] = "info", base + f"автопоиск нашёл лазеры в {found} из {total} кадров."
        else:
            st["level"], st["reason"] = "warn", base + "автопоиск тоже ничего не нашёл — лазеров НЕТ. Добавь метку внутри этого фрагмента."


def prepare_laser_sequence(ffmpeg, ep, s, tmp, key, cancelled, diagnostics_state=None):
    """Слой лазеров для клипа. Ручные метки главнее автопоиска: если они пересекают клип,
    кадры НЕ декодируются и детекторы НЕ запускаются — слой строится прямо из меток в шкале исходного видео."""
    started = time.perf_counter()
    annotation_file = manual_laser_annotation_path(ep.path)
    stats = {
        "clip": os.path.basename(ep.path), "clip_start": float(ep.start),
        "clip_end": float(ep.start + ep.dur), "manual_keyframes": 0,
        "manual_keyframes_in_clip": 0, "manual_only": False, "frames": 0,
        "manual_matched_frames": 0, "manual_frames": 0, "manual_outside_crop_frames": 0,
        "auto_frames": 0, "detector_frames": 0,
        "frames_with_lasers": 0, "frames_blank": 0, "extract_s": 0.0,
        "detect_s": 0.0, "png_s": 0.0, "encode_s": 0.0, "verify_s": 0.0,
        "overlay_s": 0.0, "total_s": 0.0,
        "annotation_file": annotation_file, "annotation_file_exists": os.path.isfile(annotation_file),
        "annotation_error": "", "related_files": [], "frame_mode": s.frame_mode,
        "layer_fps": 0.0, "layer_frames": 0, "layer_offset": 0.0,
        "visible_from": None, "visible_to": None, "crop_shift": "", "nearest_mark_gap": None,
        "marked_from": None, "marked_to": None, "level": "info", "reason": "",
        "verified": None, "probe_pixels": None,
    }
    recorded = False

    def record_stats():
        nonlocal recorded
        stats["total_s"] = round(time.perf_counter() - started, 2)
        for k in ("extract_s", "detect_s", "png_s"):
            stats[k] = round(stats[k], 2)
        if recorded or diagnostics_state is None:
            return
        recorded = True
        lock = diagnostics_state.get("laser_diag_lock")
        if lock:
            with lock:
                diagnostics_state.setdefault("laser_diagnostics", []).append(stats)
        else:
            diagnostics_state.setdefault("laser_diagnostics", []).append(stats)

    if cv2 is None or Image is None or ImageDraw is None:
        raise RuntimeError("Эффект лазеров требует бесплатный OpenCV и Pillow: pip install opencv-python pillow")
    if not ep.src_w or not ep.src_h:
        meta = probe(ffmpeg, ep.path)
        ep.src_w, ep.src_h = meta["w"], meta["h"]
    if not ep.src_w or not ep.src_h:
        stats["level"], stats["reason"] = "error", "Не удалось определить размер исходного видео — слой лазеров не создан."
        record_stats()
        return None

    # Метки читаются один раз на клип, а не на каждый кадр.
    annotations = load_manual_laser_annotations(ep.path)
    identity = os.path.normcase(os.path.abspath(ep.path))
    stats["annotation_error"] = _MANUAL_LASER_LAST_ERROR.get(identity, "")
    stats["manual_keyframes"] = len(annotations)
    window = manual_laser_window(annotations)
    tol = MANUAL_LASER_EDGE_TOL
    stats["manual_keyframes_in_clip"] = sum(
        1 for row in annotations if ep.start - tol <= row["time"] <= ep.start + ep.dur + tol)
    manual_only = bool(window) and window[0] <= ep.start + ep.dur and window[1] >= ep.start
    stats["manual_only"] = manual_only
    if annotations:
        stats["marked_from"], stats["marked_to"] = window
        stats["nearest_mark_gap"] = min(
            max(0.0, ep.start - row["time"], row["time"] - ep.end) for row in annotations)
    else:
        stats["related_files"] = find_related_annotation_files(ep.path)

    if manual_only:
        ep, shift = fit_crop_to_manual_marks(ep, s, annotations)
        stats["crop_shift"] = shift

    out_dir = os.path.join(tmp, key + "_laser")
    os.makedirs(out_dir, exist_ok=True)

    sw, sh, W, H = ep.src_w, ep.src_h, s.width, s.height
    overlay_w = max(2, int(round(W * LASER_OVERLAY_SCALE)))
    overlay_h = max(2, int(round(H * LASER_OVERLAY_SCALE)))
    overlay_scale_x, overlay_scale_y = overlay_w / W, overlay_h / H
    # Sparse HOG scans are tracked with optical flow between scans, instead of running HOG on every frame.
    previous_gray = None
    tracked_hog_groups = []
    overlay_started = time.perf_counter()

    def make_overlay():
        return Image.new("RGBA", (overlay_w, overlay_h), (0, 0, 0, 0))

    def compose_laser_layers(beam_canvas, glow_canvas):
        """Blur the red light layer, then put crisp hot beam cores above it."""
        if ImageFilter is not None:
            blur_radius = max(3, min(8, int(round(overlay_w / 160))))
            glow_canvas = glow_canvas.filter(ImageFilter.GaussianBlur(radius=blur_radius))
        glow_canvas.alpha_composite(beam_canvas)
        return glow_canvas

    def draw_beams(draw, eye_points, center_x, coords_are_source, dw, dh, shift=(0, 0), record=None,
                   direction_points=None, glow_draw=None, animation_time=0.0):
        mapped_center_x, _ = _map_source_to_output(center_x * sw / dw, 0, ep, s) if coords_are_source else (center_x, 0)
        drawn = 0
        for eye_idx, (ex, ey) in enumerate(eye_points):
            if coords_are_source:
                src_x, src_y = ex * sw / dw, ey * sh / dh
                x, y = _map_source_to_output(src_x, src_y, ep, s)
            else:
                x, y = ex, ey
            if x < -10 or x > W + 10 or y < -10 or y > H + 10:
                continue
            # Draw at half resolution; FFmpeg scales the alpha layer to the final video size.
            sx, sy = x * overlay_scale_x, y * overlay_scale_y
            target = direction_points[eye_idx] if direction_points and eye_idx < len(direction_points) else None
            if target is not None:
                if coords_are_source:
                    tx, ty = _map_source_to_output(target[0] * sw / dw, target[1] * sh / dh, ep, s)
                else:
                    tx, ty = target
                tx, ty = tx * overlay_scale_x, ty * overlay_scale_y
                vx, vy = tx - sx, ty - sy
                if math.hypot(vx, vy) < 1.0:
                    target = None
                else:
                    # Continue the user-indicated direction to the frame edge, not just to the clicked handle.
                    candidates = []
                    if vx > 1e-6:
                        candidates.append((overlay_w - 1 - sx) / vx)
                    elif vx < -1e-6:
                        candidates.append((0 - sx) / vx)
                    if vy > 1e-6:
                        candidates.append((overlay_h - 1 - sy) / vy)
                    elif vy < -1e-6:
                        candidates.append((0 - sy) / vy)
                    positive = [t for t in candidates if t >= 0]
                    stretch = min(positive) if positive else 1.0
                    end_x, end_y = sx + vx * stretch, sy + vy * stretch
            if target is None:
                direction = -1 if x < mapped_center_x else 1
                end_x = sx + direction * overlay_w * 0.62
                end_y = sy + overlay_h * (0.07 if eye_idx == 0 else 0.10)
            start, end = (int(sx), int(sy)), (int(end_x), int(end_y))
            if record is not None:
                record.append((start, end, max(8, overlay_w // 70)))
            start = (start[0] - shift[0], start[1] - shift[1])
            end = (end[0] - shift[0], end[1] - shift[1])

            # Animate the laser's energy without moving its manually tracked origin/aim.
            # The pulse is subtle, deterministic, and evaluated per generated layer frame.
            pulse = 0.88 + 0.12 * (0.5 + 0.5 * math.sin(animation_time * 2.0 * math.pi * 3.2 + eye_idx * 0.8))
            shimmer = 0.5 + 0.5 * math.sin(animation_time * 2.0 * math.pi * 7.0 + eye_idx * 1.7)
            glow_alpha = int(72 + 28 * pulse)
            inner_glow_alpha = int(112 + 38 * pulse)

            # A separate blurred red layer creates a broad halo around the beam and eye.
            if glow_draw is not None:
                glow_draw.line((start, end), fill=(255, 0, 0, glow_alpha), width=max(24, overlay_w // 24))
                glow_draw.line((start, end), fill=(255, 18, 0, inner_glow_alpha), width=max(14, overlay_w // 42))
                glow_r = max(8, int((overlay_w // 82) * (0.92 + 0.16 * pulse)))
                eye_alpha = int(190 + 45 * pulse)
                glow_draw.ellipse((start[0]-glow_r, start[1]-glow_r,
                                   start[0]+glow_r, start[1]+glow_r), fill=(255, 8, 0, eye_alpha))

            # Crisp beam: red outer body, orange-hot inner line and a white-hot core.
            draw.line((start, end), fill=(255, 0, 0, int(112 + 24 * pulse)), width=max(8, overlay_w // 90))
            draw.line((start, end), fill=(255, 42, 8, int(205 + 35 * pulse)), width=max(4, overlay_w // 190))
            draw.line((start, end), fill=(255, 238, 232, int(232 + 23 * pulse)), width=max(2, overlay_w // 520))
            draw.line((start, end), fill=(255, 255, 255, 255), width=1)

            # A short hot streak travels from the eye to the tip, making the beam feel energized.
            # Its location is time-based, so consecutive PNGs produce actual animation.
            dx, dy = end[0] - start[0], end[1] - start[1]
            streak_pos = (animation_time * 0.72 + eye_idx * 0.41) % 1.0
            streak_len = 0.075 + 0.025 * shimmer
            a = min(0.96, streak_pos)
            b = min(1.0, a + streak_len)
            streak_start = (int(start[0] + dx * a), int(start[1] + dy * a))
            streak_end = (int(start[0] + dx * b), int(start[1] + dy * b))
            if glow_draw is not None:
                glow_draw.line((streak_start, streak_end), fill=(255, 45, 12, int(160 + 70 * shimmer)),
                               width=max(18, overlay_w // 34))
            draw.line((streak_start, streak_end), fill=(255, 95, 35, int(210 + 45 * shimmer)),
                      width=max(5, overlay_w // 115))
            draw.line((streak_start, streak_end), fill=(255, 250, 238, 255),
                      width=max(2, overlay_w // 400))

            hot_r = max(2, int((overlay_w // 350) * (0.9 + 0.2 * pulse)))
            draw.ellipse((start[0]-hot_r, start[1]-hot_r,
                          start[0]+hot_r, start[1]+hot_r), fill=(255, 245, 235, 255))
            drawn += 1
        return drawn


    if manual_only:
        fps = manual_layer_fps(ep, s, annotations)
        total_frames = max(1, int(math.ceil(ep.dur * fps - 1e-6)))
        marked = {}
        for i in range(total_frames):
            # Середина интервала показа кадра слоя: лучи в среднем отстают от объекта на полшага, а не на шаг.
            sample_time = ep.start + (i + 0.5) / fps
            sample = manual_laser_sample_from_rows(annotations, sample_time)
            if sample and sample.get("points"):
                sample["_animation_time"] = sample_time
                marked[i] = sample
        stats["frames"] = total_frames
        stats["manual_matched_frames"] = len(marked)
        stats["layer_fps"] = fps
        if not marked:
            laser_decide_reason(stats)
            record_stats()
            return None
        first, last = min(marked), max(marked)
        reporter = diagnostics_state.get("laser_reporter") if diagnostics_state else None
        if reporter is not None:
            reporter.status(f"Лазеры: {os.path.basename(ep.path)} — ручная разметка, кадров слоя {last - first + 1}")
        png_started = time.perf_counter()

        def beams_points(sample):
            points = sample["points"]
            directions = sample.get("directions")
            paired = [(list(p), list(directions[idx]) if directions and idx < len(directions) else None)
                      for idx, p in enumerate(points)]
            paired.sort(key=lambda item: item[0][0])
            pts = [(float(p[0]) * sw, float(p[1]) * sh) for p, _ in paired]
            dirs = [(float(d[0]) * sw, float(d[1]) * sh) if d is not None else None for _, d in paired]
            return pts, sum(p[0] for p in pts) / len(pts), (dirs if any(d is not None for d in dirs) else None)

        # Проход 1: только геометрия (рисуем в 1×1 — почти бесплатно). Даёт, какие кадры видимы, и общую рамку слоя.
        scratch = ImageDraw.Draw(Image.new("RGBA", (1, 1)), "RGBA")
        drawn_by_frame, records = {}, []
        for i in range(first, last + 1):
            if cancelled():
                raise Cancelled()
            points = marked.get(i)
            drawn = 0
            if points:
                pts, cxm, dirs = beams_points(points)
                drawn = draw_beams(scratch, pts, cxm, True, sw, sh, record=records,
                                   direction_points=dirs)
            if drawn:
                drawn_by_frame[i] = drawn
                stats["manual_frames"] += 1
                stats["frames_with_lasers"] += 1
            else:
                stats["frames_blank"] += 1
                if points:
                    stats["manual_outside_crop_frames"] += 1
        stats["layer_frames"] = last - first + 1
        stats["layer_offset"] = first / fps
        probe_times = []
        box = None
        if drawn_by_frame:
            visible = sorted(drawn_by_frame)
            stats["visible_from"] = ep.start + visible[0] / fps
            stats["visible_to"] = ep.start + (visible[-1] + 1) / fps
            most = max(drawn_by_frame.values())
            both = [i for i in visible if drawn_by_frame[i] == most]
            middle = visible[len(visible) // 2]
            best = min(both, key=lambda i: abs(i - middle))
            probe_times = [(best + 0.5) / fps]
            if visible[0] != best:
                probe_times.append((visible[0] + 0.5) / fps)
            pad = max(30, overlay_w // 32)  # запас для размытого свечения на половинном разрешении
            bx0 = max(0, min(min(a[0], b[0]) for a, b, _ in records) - max(w for *_, w in records) - pad)
            by0 = max(0, min(min(a[1], b[1]) for a, b, _ in records) - max(w for *_, w in records) - pad)
            bx1 = min(overlay_w, max(max(a[0], b[0]) for a, b, _ in records) + max(w for *_, w in records) + pad)
            by1 = min(overlay_h, max(max(a[1], b[1]) for a, b, _ in records) + max(w for *_, w in records) + pad)
            bw, bh = max(2, bx1 - bx0), max(2, by1 - by0)
            # положение/размер в итоговом кадре; при LASER_OVERLAY_SCALE=0.5 масштаб ровно ×2, без дробей
            kx, ky = W / overlay_w, H / overlay_h
            box = (int(round(bx0 * kx)), int(round(by0 * ky)), int(round(bw * kx)), int(round(bh * ky)))
            stats["layer_box"] = box
            # Проход 2: PNG только нужной рамки и только для кадров в диапазоне показа.
            blank_path = os.path.join(out_dir, "blank.png")
            Image.new("RGBA", (bw, bh), (0, 0, 0, 0)).save(blank_path)
            for i in range(first, last + 1):
                if cancelled():
                    raise Cancelled()
                path = os.path.join(out_dir, f"laser_{i - first + 1:06d}.png")
                if i in drawn_by_frame:
                    beam_canvas = Image.new("RGBA", (bw, bh), (0, 0, 0, 0))
                    glow_canvas = Image.new("RGBA", (bw, bh), (0, 0, 0, 0))
                    pts, cxm, dirs = beams_points(marked[i])
                    draw_beams(ImageDraw.Draw(beam_canvas, "RGBA"), pts, cxm, True, sw, sh,
                               shift=(bx0, by0), direction_points=dirs,
                               glow_draw=ImageDraw.Draw(glow_canvas, "RGBA"),
                               animation_time=float(marked[i].get("_animation_time", 0.0)))
                    compose_laser_layers(beam_canvas, glow_canvas).save(path)
                else:
                    shutil.copyfile(blank_path, path)
            # Замыкающий пустой кадр: при repeatlast=0 FFmpeg не удерживает ПОСЛЕДНИЙ кадр слоя до конца его интервала.
            shutil.copyfile(blank_path, os.path.join(out_dir, f"laser_{last - first + 2:06d}.png"))
        stats["png_s"] += time.perf_counter() - png_started
        stats["overlay_s"] = round(time.perf_counter() - overlay_started, 2)
        laser_decide_reason(stats)
        record_stats()
        if not drawn_by_frame:
            return None  # все точки вне кадра: слой пустой; причина (error) записана
        return LaserLayer(pattern=os.path.join(out_dir, "laser_%06d.png"), fps=fps, offset=first / fps,
                          frames=last - first + 1, expected=True, probe_times=probe_times, ep=ep, stats=stats, box=box)

    src_dir = os.path.join(tmp, key + "_laser_src")
    out_dir = os.path.join(tmp, key + "_laser")
    os.makedirs(src_dir, exist_ok=True)
    os.makedirs(out_dir, exist_ok=True)
    src_pattern = os.path.join(src_dir, "frame_%06d.png")
    extract_started = time.perf_counter()
    code, _, err = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-ss", f"{ep.start:.3f}",
                        "-t", f"{ep.dur:.3f}", "-i", ep.path, "-an", "-vf",
                        f"fps={LASER_FPS},scale={DETECT_WIDTH}:-2:flags=fast_bilinear,format=gray",
                        "-start_number", "1", src_pattern], cancelled)
    stats["extract_s"] = round(time.perf_counter() - extract_started, 2)
    if code != 0:
        record_stats()
        raise RuntimeError("Не удалось подготовить кадры для лазеров: " + err.strip()[-220:])
    frame_paths = sorted(glob.glob(os.path.join(src_dir, "frame_*.png")))
    if not frame_paths:
        record_stats()
        return None

    cascade_dir = cv2.data.haarcascades
    universal = bool(getattr(s, "laser_universal_search", True))
    # If manual keys overlap this clip, use only the user's track for this clip.
    # This avoids both false positives outside the requested interval and costly fallback detectors.
    face_detectors, eye_detectors, profile_detector = [], [], None
    if not manual_only:
        face_names = ["haarcascade_frontalface_default.xml"]
        if universal:
            face_names.extend(["haarcascade_frontalface_alt2.xml", "haarcascade_frontalface_alt.xml"])
        for name in face_names:
            path = os.path.join(cascade_dir, name)
            if os.path.isfile(path):
                detector = cv2.CascadeClassifier(path)
                if not detector.empty():
                    face_detectors.append(detector)
        profile_path = os.path.join(cascade_dir, "haarcascade_profileface.xml")
        profile_detector = cv2.CascadeClassifier(profile_path) if universal and os.path.isfile(profile_path) else None
        if not face_detectors:
            record_stats()
            raise RuntimeError("OpenCV не содержит каскады распознавания лиц.")
        eye_names = ["haarcascade_eye.xml"]
        if universal:
            eye_names.append("haarcascade_eye_tree_eyeglasses.xml")
        for name in eye_names:
            path = os.path.join(cascade_dir, name)
            if os.path.isfile(path):
                detector = cv2.CascadeClassifier(path)
                if not detector.empty():
                    eye_detectors.append(detector)

    def add_face(face_list, rect, profile=False, facing=0):
        x, y, w, h = [int(v) for v in rect]
        if w < 16 or h < 16:
            return
        candidate = [x, y, w, h, bool(profile), int(facing)]
        for i, old in enumerate(face_list):
            ox, oy, ow, oh, old_profile, old_facing = old
            ix1, iy1 = max(x, ox), max(y, oy)
            ix2, iy2 = min(x + w, ox + ow), min(y + h, oy + oh)
            inter = max(0, ix2 - ix1) * max(0, iy2 - iy1)
            union = w * h + ow * oh - inter
            iou = inter / max(1, union)
            close = (abs((x + w / 2) - (ox + ow / 2)) < min(w, ow) * 0.28 and
                     abs((y + h / 2) - (oy + oh / 2)) < min(h, oh) * 0.28)
            if iou >= 0.36 or close:
                if old_profile and not profile:
                    face_list[i] = candidate
                return
        face_list.append(candidate)

    progress_reporter = diagnostics_state.get("laser_reporter") if diagnostics_state else None
    progress_step = max(1, len(frame_paths) // 10)
    for number, frame_path in enumerate(frame_paths, 1):
        if cancelled():
            raise Cancelled()
        if progress_reporter is not None and (number == 1 or number % progress_step == 0 or number == len(frame_paths)):
            mode_label = "автоматический поиск"
            progress_reporter.status(
                f"Лазеры: {os.path.basename(ep.path)} — кадр {number}/{len(frame_paths)} ({mode_label})"
            )
        stats["frames"] += 1
        gray = cv2.imread(frame_path, cv2.IMREAD_GRAYSCALE)
        if gray is None:
            make_overlay().save(os.path.join(out_dir, f"laser_{number:06d}.png"))
            stats["frames_blank"] += 1
            continue
        dh, dw = gray.shape[:2]
        overlay = make_overlay()
        glow_overlay = make_overlay()
        draw = ImageDraw.Draw(overlay, "RGBA")
        glow_draw = ImageDraw.Draw(glow_overlay, "RGBA")
        stats["auto_frames"] += 1
        stats["detector_frames"] += 1
        det_started = time.perf_counter()
        faces = []
        for detector in face_detectors:
            try:
                min_neighbors = 3 if universal else 4
                found = detector.detectMultiScale(gray, scaleFactor=1.10, minNeighbors=min_neighbors,
                                                  minSize=(18 if universal else 22, 18 if universal else 22))
                for rect in found:
                    add_face(faces, rect)
            except cv2.error:
                pass
        if profile_detector is not None and not profile_detector.empty():
            try:
                for rect in profile_detector.detectMultiScale(gray, scaleFactor=1.10,
                                                               minNeighbors=3, minSize=(18, 18)):
                    add_face(faces, rect, profile=True, facing=-1)
                flipped = cv2.flip(gray, 1)
                for rect in profile_detector.detectMultiScale(flipped, scaleFactor=1.10,
                                                               minNeighbors=3, minSize=(18, 18)):
                    x, y, w, h = [int(v) for v in rect]
                    add_face(faces, (dw - x - w, y, w, h), profile=True, facing=1)
            except cv2.error:
                pass
        faces.sort(key=lambda f: f[2] * f[3], reverse=True)
        faces = faces[:24]

        laser_sources = []
        for fx, fy, fw, fh, is_profile, facing in faces:
            roi = gray[max(0, fy):min(dh, fy + fh), max(0, fx):min(dw, fx + fw)]
            eye_points = []
            if eye_detectors and roi.size:
                for eye_detector in eye_detectors:
                    try:
                        detected_eyes = eye_detector.detectMultiScale(
                            roi, scaleFactor=1.10, minNeighbors=3,
                            minSize=(4 if universal else 5, 4 if universal else 5))
                    except cv2.error:
                        continue
                    for ex, ey, ew, eh in detected_eyes:
                        cx, cy = ex + ew / 2, ey + eh / 2
                        if cy >= fh * 0.76 or cx < fw * 0.06 or cx > fw * 0.94:
                            continue
                        point = (fx + cx, fy + cy)
                        if not any(math.hypot(point[0] - ox, point[1] - oy) < max(3, fw * 0.045)
                                   for ox, oy in eye_points):
                            eye_points.append(point)
            if is_profile:
                if eye_points:
                    eye_points = [min(eye_points, key=lambda p: abs(p[1] - (fy + fh * 0.38)))]
                else:
                    eye_x = fx + fw * (0.62 if facing >= 0 else 0.38)
                    eye_points = [(eye_x, fy + fh * 0.40)]
            elif len(eye_points) >= 2:
                eye_points.sort(key=lambda p: p[0])
                eye_points = [eye_points[0], eye_points[-1]]
            elif len(eye_points) == 1:
                ex, ey = eye_points[0]
                partner_x = fx + fw * (0.68 if ex < fx + fw * 0.5 else 0.32)
                eye_points = [eye_points[0], (partner_x, ey)]
                eye_points.sort(key=lambda p: p[0])
            else:
                eye_points = [(fx + fw * 0.32, fy + fh * 0.40), (fx + fw * 0.68, fy + fh * 0.40)]
            laser_sources.append((eye_points, fx + fw / 2))

        # Global eye-pair search is skipped when a face already yielded a source.
        if universal and eye_detectors and not laser_sources:
            global_eyes = []
            for eye_detector in eye_detectors:
                try:
                    found_eyes = eye_detector.detectMultiScale(
                        gray, scaleFactor=1.10, minNeighbors=4,
                        minSize=(4, 4), maxSize=(max(16, dw // 10), max(16, dh // 5)))
                except cv2.error:
                    continue
                for ex, ey, ew, eh in found_eyes:
                    cx, cy = ex + ew / 2, ey + eh / 2
                    if cy > dh * 0.80:
                        continue
                    if not any(math.hypot(cx - ox, cy - oy) < max(4, dw * 0.015)
                               for ox, oy in global_eyes):
                        global_eyes.append((cx, cy))
            pending = sorted(global_eyes, key=lambda p: (p[1], p[0]))
            pairs = []
            max_dx = max(16, int(dw * 0.15))
            min_dx = max(7, int(dw * 0.012))
            max_dy = max(5, int(dh * 0.035))
            while pending and len(pairs) < 12:
                first = pending.pop(0)
                options = []
                for idx, second in enumerate(pending):
                    dx, dy = second[0] - first[0], abs(second[1] - first[1])
                    if min_dx <= dx <= max_dx and dy <= max_dy:
                        score = dy * 3.0 + abs(dx - dw * 0.055)
                        options.append((score, idx, second))
                if options:
                    _, idx, second = min(options, key=lambda item: item[0])
                    pending.pop(idx)
                    pairs.append(([first, second], (first[0] + second[0]) / 2))
            laser_sources.extend(pairs)

        # Silhouette detection is expensive; use optical flow for alternate frames and
        # run HOG only when face/eye detection found nothing.
        if laser_sources:
            tracked_hog_groups = []
        elif universal:
            need_hog = (not tracked_hog_groups) or (number % 2 == 1) or previous_gray is None or np is None
            if not need_hog and tracked_hog_groups and previous_gray is not None and np is not None:
                old_points = [point for group in tracked_hog_groups for point in group]
                try:
                    p0 = np.asarray(old_points, dtype=np.float32).reshape(-1, 1, 2)
                    p1, status, _ = cv2.calcOpticalFlowPyrLK(
                        previous_gray, gray, p0, None, winSize=(15, 15), maxLevel=2,
                        criteria=(cv2.TERM_CRITERIA_EPS | cv2.TERM_CRITERIA_COUNT, 12, 0.03))
                    if p1 is None or status is None or int(status.sum()) < 2:
                        need_hog = True
                    else:
                        tracked = p1.reshape(-1, 2)
                        flags = status.reshape(-1).astype(bool)
                        new_groups = []
                        for group_index in range(len(tracked_hog_groups)):
                            offset = group_index * 2
                            if flags[offset] and flags[offset + 1]:
                                pair = [(float(tracked[offset][0]), float(tracked[offset][1])),
                                        (float(tracked[offset + 1][0]), float(tracked[offset + 1][1]))]
                                new_groups.append(pair)
                                laser_sources.append((pair, (pair[0][0] + pair[1][0]) / 2))
                        if new_groups:
                            tracked_hog_groups = new_groups
                        else:
                            need_hog = True
                except (cv2.error, ValueError, TypeError):
                    need_hog = True
            if need_hog:
                try:
                    if not hasattr(prepare_laser_sequence, "_people_hog"):
                        hog = cv2.HOGDescriptor()
                        hog.setSVMDetector(cv2.HOGDescriptor_getDefaultPeopleDetector())
                        prepare_laser_sequence._people_hog = hog
                    hog = prepare_laser_sequence._people_hog
                    person_image = cv2.cvtColor(gray, cv2.COLOR_GRAY2BGR)
                    people, weights = hog.detectMultiScale(
                        person_image, hitThreshold=0.0, winStride=(8, 8), padding=(8, 8), scale=1.05)
                    candidates = []
                    for idx, (px, py, pw, ph) in enumerate(people):
                        px, py, pw, ph = int(px), int(py), int(pw), int(ph)
                        confidence = float(weights[idx]) if idx < len(weights) else 0.0
                        if pw < 24 or ph < 58 or confidence < 0.15:
                            continue
                        head_cx = px + pw * 0.5
                        if any(abs(head_cx - (fx + fw * 0.5)) < pw * 0.42 and
                               fy < py + ph * 0.34 and fy + fh > py - ph * 0.03
                               for fx, fy, fw, fh, *_ in faces):
                            continue
                        if any(abs(head_cx - old[0]) < min(pw, old[2]) * 0.45 and
                               abs((py + ph * 0.5) - (old[1] + old[3] * 0.5)) < min(ph, old[3]) * 0.35
                               for old in candidates):
                            continue
                        candidates.append((px, py, pw, ph, confidence))
                    candidates.sort(key=lambda item: item[4], reverse=True)
                    tracked_hog_groups = []
                    for px, py, pw, ph, confidence in candidates[:8]:
                        head_y = py + ph * 0.105
                        half_eye_gap = max(3.0, min(pw * 0.12, ph * 0.055))
                        pair = [(px + pw * 0.5 - half_eye_gap, head_y),
                                (px + pw * 0.5 + half_eye_gap, head_y)]
                        tracked_hog_groups.append(pair)
                        laser_sources.append((pair, px + pw * 0.5))
                except (cv2.error, AttributeError, TypeError, ValueError):
                    tracked_hog_groups = []
        else:
            tracked_hog_groups = []

        stats["detect_s"] += time.perf_counter() - det_started
        drawn_count = 0
        animation_time = ep.start + (number - 1) / max(1, LASER_FPS)
        for eye_points, center_x in laser_sources:
            drawn_count += draw_beams(draw, eye_points, center_x, True, dw, dh,
                                      glow_draw=glow_draw, animation_time=animation_time)
        png_started = time.perf_counter()
        if drawn_count:
            compose_laser_layers(overlay, glow_overlay).save(os.path.join(out_dir, f"laser_{number:06d}.png"))
        else:
            overlay.save(os.path.join(out_dir, f"laser_{number:06d}.png"))
        stats["png_s"] += time.perf_counter() - png_started
        if drawn_count:
            stats["frames_with_lasers"] += 1
        else:
            stats["frames_blank"] += 1
        previous_gray = gray

    make_overlay().save(os.path.join(out_dir, f"laser_{len(frame_paths) + 1:06d}.png"))  # замыкающий пустой кадр
    stats["overlay_s"] = round(time.perf_counter() - overlay_started, 2)
    stats["layer_fps"], stats["layer_frames"] = float(LASER_FPS), len(frame_paths)
    laser_decide_reason(stats)
    record_stats()
    if stats["frames_with_lasers"] == 0:
        return None  # автопоиск ничего не нашёл: слой не нужен, причина уже записана в stats
    return LaserLayer(pattern=os.path.join(out_dir, "laser_%06d.png"), fps=float(LASER_FPS), offset=0.0,
                      frames=len(frame_paths), expected=False, ep=ep, stats=stats)

def add_laser_issue(state, level, ep, message, tech=""):
    """Фиксирует проблему лазеров: level = error | warn | tech (tech — только в журнал)."""
    item = {"level": level, "clip": os.path.basename(ep.path), "start": float(ep.start),
            "end": float(ep.start + ep.dur), "message": message, "tech": tech}
    lock = state.get("laser_diag_lock")
    if lock:
        with lock:
            state.setdefault("laser_issues", []).append(item)
            if level != "tech":
                state.setdefault("laser_warnings", []).append(
                    f"{item['clip']} ({item['start']:.1f}–{item['end']:.1f} с): {message}")
    else:
        state.setdefault("laser_issues", []).append(item)
        if level != "tech":
            state.setdefault("laser_warnings", []).append(
                f"{item['clip']} ({item['start']:.1f}–{item['end']:.1f} с): {message}")


def verify_lasers_in_clip(ffmpeg, path, times, cancelled):
    """Берёт кадры ГОТОВОГО клипа и считает красные пиксели (R заметно выше G и B).
    Возвращает (найдены ли лучи, максимум пикселей) или (None, 0), если проверить нечем."""
    if np is None or cv2 is None or not times:
        return None, 0
    best = 0
    for t in times:
        code, out, _ = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-ss", f"{t:.3f}", "-i", path,
                            "-frames:v", "1", "-f", "image2pipe", "-vcodec", "png", "-"], cancelled)
        if code != 0 or not out:
            continue
        img = cv2.imdecode(np.frombuffer(out, np.uint8), cv2.IMREAD_COLOR)
        if img is None:
            continue
        b, g, r = (img[..., i].astype(np.int16) for i in range(3))
        best = max(best, int(((r - np.maximum(g, b)) > 60).sum()))
        if best >= LASER_PROBE_MIN_PIXELS:
            break
    return best >= LASER_PROBE_MIN_PIXELS, best


def render_one(ffmpeg, ep, out, s, enc, state, tmp, cancelled):
    if s.captions and HAVE_WHISPER and ep.has_audio and not (
            ep.words_rng[0] <= ep.start + 0.2 and ep.words_rng[1] >= ep.end - 0.2):
        try:
            ep = speech_pass(ffmpeg, ep, s, cancelled, adjust=False)
        except Cancelled:
            raise
        except Exception:
            pass
    key = os.path.basename(out)[:-4]
    ovs = prepare_overlays(ep, s, tmp, key)
    layer = prepare_laser_sequence(ffmpeg, ep, s, tmp, key, cancelled, diagnostics_state=state) if s.laser_effect else None
    if layer is not None and layer.ep is not None:
        ep = layer.ep   # кроп мог сдвинуться к меткам; слой и видео обязаны использовать один и тот же ep
    af = (f"afade=t=in:d=0.05,afade=t=out:st={max(0.0, ep.dur - 0.12):.3f}:d=0.12,apad")
    last_cmd = {"text": ""}

    def cmd_for(codec, fx, use_lasers=True):
        ovl = ovs if fx else []
        cmd = [ffmpeg, "-y", "-nostdin", "-v", "error", "-ss", f"{ep.start:.3f}", "-i", ep.path]
        n_in, a_idx = 1, 0
        if not ep.has_audio:
            cmd += ["-f", "lavfi", "-i", "anullsrc=r=48000:cl=stereo"]
            n_in, a_idx = 2, 1
        for o in ovl:
            cmd += ["-i", o[0]]
        laser_idx = None
        if use_lasers and layer is not None:
            laser_idx = n_in + len(ovl)
            cmd += ["-framerate", f"{layer.fps:g}", "-start_number", "1", "-i", layer.pattern]
        graph = build_graph(ep, s, ovl, n_in, fx, laser_idx=laser_idx,
                            laser_offset=layer.offset if layer is not None else 0.0,
                            laser_box=layer.box if layer is not None else None)
        cmd += ["-t", f"{ep.dur:.3f}", "-filter_complex", graph,
                "-map", "[v]", "-map", f"{a_idx}:a:0", "-af", af]
        cmd += vcodec_args(codec, state.get("q", s.quality))
        cmd += ["-c:a", "aac", "-b:a", "192k", "-ar", "48000", "-ac", "2", out]
        last_cmd["text"] = " ".join(str(c) for c in cmd)
        return cmd

    attempts = [(enc, True, True)]
    if enc:
        attempts.append((None, True, True))
    if ovs or ep.zoom:
        attempts.append((None, False, True))
    if layer is not None:
        attempts.append((None, False, False))
    last_error = ""
    for codec, fx, use_lasers in attempts:
        started = time.perf_counter()
        code, _, err = run(cmd_for(codec, fx, use_lasers), cancelled)
        elapsed = time.perf_counter() - started
        if layer is not None and use_lasers:
            layer.stats["encode_s"] = round(layer.stats.get("encode_s", 0.0) + elapsed, 2)
        if err:
            last_error = str(err).strip()[-600:]
        ok_file = code == 0 and os.path.exists(out) and os.path.getsize(out) > 0
        if layer is not None and use_lasers and not ok_file:
            # Техническая причина сохраняется в журнал, даже если следующая попытка пройдёт.
            add_laser_issue(state, "tech", ep, f"FFmpeg отклонил попытку (кодек={codec or 'x264'}, эффекты={fx}, лазеры=да)",
                            tech=f"код {code}: {last_error}\nКоманда: {last_cmd['text'][:1500]}")
        if ok_file:
            if codec != enc:
                state["mixed"] = True
            if layer is not None and not use_lasers:
                layer.stats["level"] = "error"
                layer.stats["reason"] = "FFmpeg не смог наложить слой лазеров — клип экспортирован БЕЗ лазеров."
                add_laser_issue(state, "error", ep,
                                "FFmpeg не смог наложить слой лазеров; клип создан без них. "
                                "Техническая причина записана в отчёт диагностики.", tech=last_error)
            elif layer is not None and layer.expected:
                vstart = time.perf_counter()
                found, pixels = verify_lasers_in_clip(ffmpeg, out, layer.probe_times, cancelled)
                layer.stats["verify_s"] = round(time.perf_counter() - vstart, 2)
                layer.stats["verified"], layer.stats["probe_pixels"] = found, pixels
                if found is False:
                    layer.stats["level"] = "error"
                    layer.stats["reason"] += " ПРОВЕРКА ГОТОВОГО КЛИПА: лазеры в кадре не обнаружены."
                    add_laser_issue(state, "error", ep,
                                    f"в готовом клипе лазеры не обнаружены (проверочные кадры {', '.join(f'{t:.2f}' for t in layer.probe_times)} с, "
                                    f"красных пикселей: {pixels}, нужно ≥ {LASER_PROBE_MIN_PIXELS}), хотя слой из "
                                    f"{layer.frames} кадров создан.", tech=last_cmd["text"][:1500])
            return True
    if layer is not None:
        layer.stats["level"] = "error"
        layer.stats["reason"] = "Клип не удалось собрать вообще."
        add_laser_issue(state, "error", ep, f"не удалось собрать клип с лазерами. {last_error}", tech=last_cmd["text"][:1500])
    return False


TRANS_RU = {"auto": "авто", "cut": "склейка", "fade": "плавно", "fadeblack": "через чёрное",
            "wipeleft": "шторка", "slideleft": "сдвиг", "circleopen": "круг",
            "zoomin": "наезд", "pixelize": "пиксели", "radial": "radial"}
TRANS_CYCLE = ["auto", "cut", "fade", "fadeblack", "wipeleft", "slideleft", "circleopen",
               "zoomin", "pixelize", "radial"]
DYNAMIC = ["wipeleft", "slideleft", "circleopen", "zoomin", "radial", "pixelize"]
SAFE_TRANS = ("fade", "fadeblack", "wipeleft", "slideleft")


def decide_transitions(eps, s):
    out, prev = [None], None
    base = 0.30 if s.target <= 75 else 0.50
    rnd = random.Random(len(eps) * 7919 + int(sum(e.start for e in eps)))
    for i in range(1, len(eps)):
        a, b = eps[i - 1], eps[i]
        name, mode = b.trans, s.transitions
        if name == "auto":
            if mode.startswith("Только"):
                name = "cut"
            elif mode.startswith("Плавные"):
                name = "fade"
            else:
                if a.path == b.path and 0 <= b.start - a.end < 4:
                    name = "cut"
                elif b.e_start > 0.75:
                    name = "cut"
                elif a.e_end < 0.25 and b.e_start < 0.3:
                    name = "fade"
                elif a.path == b.path:
                    name = "fade"
                elif a.game == b.game:
                    name = rnd.choice(["slideleft", "wipeleft", "fade"])
                else:
                    name = rnd.choice(DYNAMIC + ["fadeblack"])
                if mode.startswith("Динамичные") and name in ("cut", "fade") and a.path != b.path:
                    name = rnd.choice(DYNAMIC)
                if name == prev and name not in ("cut", "fade"):
                    name = rnd.choice([x for x in DYNAMIC if x != prev])
        dur = 0.0 if name == "cut" else base * (1.3 if name == "fadeblack" else 1.0)
        dur = min(dur, 0.35 * min(a.dur, b.dur))
        if dur < 0.08:
            name, dur = "cut", 0.0
        out.append((name, dur))
        prev = name
    return out


def decide_effects(eps, s):
    for e in eps:
        e.zoom = False
    if not s.effects:
        return
    n = 0
    for i, e in enumerate(eps):
        if (not e.manual and e.reaction >= 0.6 and e.score >= 0.5 and (e.core_e - e.core_s) <= 8
                and n < max(1, int(len(eps) * 0.4)) and not (i > 0 and eps[i - 1].zoom)):
            e.zoom = True
            n += 1


def concat_copy(ffmpeg, clips, out, tmp, cancelled):
    lf = os.path.join(tmp, "list.txt")
    with open(lf, "w", encoding="utf-8") as f:
        for p in clips:
            f.write("file '" + p.replace("\\", "/").replace("'", r"'\''") + "'\n")
    code, _, err = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-f", "concat", "-safe", "0",
                        "-i", lf, "-c", "copy", out], cancelled)
    if code != 0:
        raise RuntimeError("Ошибка склейки: " + err.strip()[-300:])


def assemble(ffmpeg, clips, eps, s, enc, tmp, cancelled, rep, reencode=False):
    raw = os.path.join(tmp, "mix_raw.mp4")
    trans = decide_transitions(eps, s)
    all_cut = all(t is None or t[0] == "cut" for t in trans)
    if (len(clips) == 1 or all_cut) and not reencode:
        concat_copy(ffmpeg, clips, raw, tmp, cancelled)
        return raw
    if len(clips) == 1:
        for codec in ([enc, None] if enc else [None]):
            cmd = [ffmpeg, "-y", "-nostdin", "-v", "error", "-i", clips[0]]
            cmd += vcodec_args(codec, s.quality) + ["-pix_fmt", "yuv420p", "-c:a", "aac",
                                                   "-b:a", "192k", "-ar", "48000", raw]
            if run(cmd, cancelled)[0] == 0:
                return raw
        raise RuntimeError("Не удалось обработать клип.")
    durs = [max(0.5, probe(ffmpeg, c)["dur"]) for c in clips]

    def run_graph(tr, codec):
        cmd = [ffmpeg, "-y", "-nostdin", "-v", "error"]
        for c in clips:
            cmd += ["-i", c]
        # xfade requires matching time bases. Each MP4 can have a different time base,
        # and an earlier xfade may output AVTB (1/1000000) while the next input uses
        # something like 1/15360. Normalize all input video streams before transitions.
        parts = []
        for idx in range(len(clips)):
            parts.append(
                f"[{idx}:v]settb=AVTB,setpts=PTS-STARTPTS,fps={int(s.fps)},setsar=1[v{idx}in]"
            )
        vcur, acur, cur_len = "[v0in]", "[0:a]", durs[0]
        for i in range(1, len(clips)):
            name, t = tr[i]
            if name == "cut":
                parts.append(f"{vcur}{acur}[v{i}in][{i}:a]concat=n=2:v=1:a=1[v{i}raw][a{i}]")
                cur_len += durs[i]
            else:
                parts.append(f"{vcur}[v{i}in]xfade=transition={name}:duration={t:.3f}:"
                             f"offset={cur_len - t:.3f}[v{i}raw]")
                parts.append(f"{acur}[{i}:a]acrossfade=d={t:.3f}:c1=tri:c2=tri[a{i}]")
                cur_len += durs[i] - t
            # concat and xfade can themselves emit different time bases; normalize
            # each intermediate result before it enters the next transition.
            parts.append(
                f"[v{i}raw]settb=AVTB,setpts=PTS-STARTPTS,fps={int(s.fps)},setsar=1[v{i}]"
            )
            vcur, acur = f"[v{i}]", f"[a{i}]"
        cmd += ["-filter_complex", ";".join(parts), "-map", vcur, "-map", acur]
        cmd += vcodec_args(codec, s.quality) + ["-pix_fmt", "yuv420p",
                                               "-c:a", "aac", "-b:a", "192k", "-ar", "48000", raw]
        return run(cmd, cancelled)[0] == 0 and os.path.exists(raw)

    simple = [t if t is None or t[0] in SAFE_TRANS or t[0] == "cut" else ("fade", t[1])
              for t in trans]
    # ИСПРАВЛЕНИЕ: При переходах принудительно используем libx264 для стабильной работы xfade
    for tr in (trans, simple):
        for codec in (["libx264"] if enc else [None]):
            if run_graph(tr, codec):
                rep.log("Переходы: " + ", ".join(TRANS_RU.get(t[0], t[0]) for t in tr[1:]))
                return raw
    rep.log("Переходы не удались — используются резкие склейки.")
    concat_copy(ffmpeg, clips, raw, tmp, cancelled)
    return raw


def normalize_audio(ffmpeg, raw, out_path, s, cancelled):
    # Музыка Матадоров включается отдельно и имеет приоритет над общей фоновой музыкой.
    # Если она выключена, продолжает работать обычная фоновая музыка из основных настроек.
    selected_music_path = s.matador_music_path if s.matador_music_enabled else s.music_path
    selected_music_volume = s.matador_music_volume if s.matador_music_enabled else s.music_volume
    if selected_music_path:
        music_path = os.path.abspath(os.path.expanduser(selected_music_path))
        if not os.path.isfile(music_path):
            label = "музыки Матадоров" if s.matador_music_enabled else "фоновой музыки"
            raise RuntimeError(f"Файл {label} не найден: " + music_path)
        music_info = probe(ffmpeg, music_path)
        if not music_info["audio"]:
            raise RuntimeError("В выбранном файле нет аудиодорожки. Для MP4 используется только звук, картинка игнорируется.")
        filters = []
        if s.keep_original_audio:
            filters.append(f"[0:a:0]volume={max(0.0, min(1.0, s.original_volume)):.3f}[original]")
            filters.append(f"[1:a:0]volume={max(0.0, min(1.0, selected_music_volume)):.3f}[music]")
            filters.append("[original][music]amix=inputs=2:duration=first:dropout_transition=2[mixed]")
            audio_chain = "[mixed]"
        else:
            filters.append(f"[1:a:0]volume={max(0.0, min(1.0, selected_music_volume)):.3f}[mixed]")
            audio_chain = "[mixed]"
        tail = "alimiter=limit=0.95"
        if s.clean_audio:
            tail = "loudnorm=I=-14:TP=-1.5:LRA=11," + tail
        filters.append(f"{audio_chain}{tail}[aout]")
        raw_info = probe(ffmpeg, raw)
        max_duration = max(0.1, float(raw_info.get("dur", 0.0)))
        cmd = [ffmpeg, "-y", "-nostdin", "-v", "error", "-i", raw,
               "-stream_loop", "-1", "-i", music_path,
               "-filter_complex", ";".join(filters), "-map", "0:v:0", "-map", "[aout]",
               "-t", f"{max_duration:.3f}", "-shortest", "-c:v", "copy",
               "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
               "-movflags", "+faststart", out_path]
        code, _, err = run(cmd, cancelled)
        if code != 0:
            raise RuntimeError("Ошибка микширования фоновой музыки: " + err.strip()[-300:])
        return

    afilter = None
    if s.clean_audio:
        target = "I=-14:TP=-1.5:LRA=11"
        _, _, err = run([ffmpeg, "-nostdin", "-hide_banner", "-i", raw, "-vn", "-af",
                         f"loudnorm={target}:print_format=json", "-f", "null", "-"], cancelled)
        afilter = f"loudnorm={target}"
        m = re.search(r"\{[^{}]*\"input_i\"[^{}]*\}", err, re.S)
        if m:
            try:
                j = json.loads(m.group(0))
                v = {k: float(j[k]) for k in
                     ("input_i", "input_tp", "input_lra", "input_thresh", "target_offset")}
                if all(math.isfinite(x) for x in v.values()):
                    afilter = (f"loudnorm={target}:measured_I={v['input_i']}:"
                               f"measured_TP={v['input_tp']}:measured_LRA={v['input_lra']}:"
                               f"measured_thresh={v['input_thresh']}:offset={v['target_offset']}:"
                               f"linear=true")
            except Exception:
                pass
    cmd = [ffmpeg, "-y", "-nostdin", "-v", "error", "-i", raw, "-c:v", "copy"]
    if afilter:
        cmd += ["-af", afilter]
    cmd += ["-c:a", "aac", "-b:a", "192k", "-ar", "48000", "-movflags", "+faststart", out_path]
    code, _, err = run(cmd, cancelled)
    if code != 0:
        raise RuntimeError("Ошибка финальной обработки: " + err.strip()[-300:])


# ──────────────────────────────────────────────────────────────────────────────
#  Главный конвейер
# ──────────────────────────────────────────────────────────────────────────────
def fmt_time(sec):
    return f"{int(sec // 60):02d}:{int(sec % 60):02d}"


@dataclass
class PlanState:
    s: object
    ffmpeg: str
    plan: list
    ranked: list
    games: dict
    info: dict
    results: dict = field(default_factory=dict)
    taken: set = field(default_factory=set)


def movie_dialogue_intervals(ffmpeg, path, info, s, cancelled):
    """Return dialogue-only intervals using VAD/transcription in small audio chunks."""
    if not HAVE_WHISPER:
        raise RuntimeError("Для режима «Фильмы» нужен бесплатный пакет faster-whisper: pip install faster-whisper")
    model = get_whisper("tiny")
    ranges = []
    chunk_seconds = 180.0  # не извлекаем звуковую дорожку всего фильма в RAM
    offset = 0.0
    while offset < info["dur"]:
        if cancelled():
            raise Cancelled()
        chunk_len = min(chunk_seconds, info["dur"] - offset)
        tmpf = tempfile.NamedTemporaryFile(suffix=".wav", delete=False)
        tmpf.close()
        try:
            code, _, err = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-ss",
                                f"{offset:.3f}", "-t", f"{chunk_len:.3f}", "-i", path,
                                "-map", "0:a:0", "-vn", "-ac", "1", "-ar", "16000",
                                "-c:a", "pcm_s16le", tmpf.name], cancelled)
            if code != 0:
                raise RuntimeError("Не удалось извлечь звук фильма: " + err.strip()[-240:])
            segments, _ = model.transcribe(
                tmpf.name,
                language=None if s.caption_lang == "auto" else s.caption_lang,
                beam_size=1,
                word_timestamps=False,
                vad_filter=True,
                condition_on_previous_text=False,
            )
            for seg in segments:
                if cancelled():
                    raise Cancelled()
                if str(getattr(seg, "text", "")).strip():
                    start = max(0.0, offset + float(seg.start))
                    end = min(info["dur"], offset + float(seg.end))
                    if end > start:
                        ranges.append((start, end))
        finally:
            try:
                os.unlink(tmpf.name)
            except OSError:
                pass
        offset += chunk_len
    return ranges


def plan_movie_dialogue(s, rep, cancelled, history=None):
    """Build a montage from detected speech segments instead of game-action scores."""
    t_start = time.time()
    ffmpeg = find_ffmpeg()
    if not ffmpeg:
        raise RuntimeError("ffmpeg не найден. Выполните: pip install imageio-ffmpeg")
    if not HAVE_WHISPER:
        raise RuntimeError("Для режима «Фильмы» нужен faster-whisper. Установите: pip install faster-whisper")
    history = history if history is not None else History()
    games = collect_sources(s)
    if not games:
        raise RuntimeError("Не найдено ни одного видео (.mp4/.mkv). Проверьте источники.")
    all_files = [(game, path) for game, paths in games.items() for path in paths]
    candidates, infos = [], {}
    for idx, (game, path) in enumerate(all_files, 1):
        if cancelled():
            raise Cancelled()
        rep.status(f"Поиск диалогов: {idx}/{len(all_files)} — {os.path.basename(path)}")
        info = probe(ffmpeg, path)
        if not info["video"] or not info["audio"] or info["dur"] <= 0:
            rep.log(f"Пропуск {os.path.basename(path)}: нет видео или звуковой дорожки.")
            rep.bar(0, idx / max(1, len(all_files)))
            continue
        infos[path] = (info["w"], info["h"])
        raw_ranges = movie_dialogue_intervals(ffmpeg, path, info, s, cancelled)
        raw_ranges.sort()
        # Объединяем реплики рядом, но не соединяем длинные паузы и не превышаем max_len.
        groups = []
        for a, b in raw_ranges:
            if groups and a - groups[-1][1] <= 1.15 and b - groups[-1][0] <= s.max_len:
                groups[-1][1] = max(groups[-1][1], b)
            else:
                groups.append([a, b])
        used = history.ranges(path) if s.no_repeat else []
        for a, b in groups:
            start = max(0.0, a - 0.25)
            end = min(info["dur"], b + 0.35)
            if end - start < 0.25:
                continue
            if any(min(ue, end) - max(us, start) > 0 for us, ue in used):
                continue
            dur = end - start
            score = 0.45 + 0.5 * min(1.0, dur / max(1.0, s.max_len))
            candidates.append(Episode(path, game, start, end, a, b, score, "диалог", True,
                                     info["w"], info["h"], info["dur"]))
        rep.log(f"[{game}] {os.path.basename(path)} → диалоговых фрагментов: {len(groups)}")
        rep.bar(0, idx / max(1, len(all_files)))
    if not candidates:
        raise RuntimeError("Диалоги не найдены. Проверьте наличие речи, язык или установку faster-whisper.")
    # В режиме фильма разрешаем несколько диалогов из одного файла и не включаем баланс игр.
    candidates.sort(key=lambda e: (-e.score, -e.dur, e.start))
    select_settings = replace(s, per_file_max=max(s.per_file_max, len(candidates)), balance=False)
    budget = s.target if s.strict else s.target * 1.1
    chosen = greedy(candidates, select_settings, budget, max(1, len(games)))
    if not chosen:
        chosen = candidates[:1]
    chosen = order_plan(chosen, s)
    st = PlanState(s, ffmpeg, chosen, candidates, games, infos)
    rep.bar(0, 1.0)
    rep.bar(1, 1.0)
    rep.log(f"План диалогов готов за {time.time() - t_start:.0f} с: фрагментов — {len(chosen)}, "
            f"{sum(e.dur for e in chosen):.0f} с")
    return st


def plan_moments(s, rep, cancelled, history=None):
    if s.mode.startswith("Фильмы"):
        return plan_movie_dialogue(s, rep, cancelled, history)
    t_start = time.time()
    ffmpeg = find_ffmpeg()
    if not ffmpeg:
        raise RuntimeError("ffmpeg не найден. Выполните: pip install imageio-ffmpeg")
    if np is None:
        raise RuntimeError("Не установлен numpy. Выполните: pip install numpy")
    history = history if history is not None else History()

    rep.status("Собираю список видео…")
    games = collect_sources(s)
    if not games:
        raise RuntimeError("Не найдено ни одного видео (.mp4/.mkv). Проверьте папку.")
    total_files = sum(len(v) for v in games.values())
    rep.log(f"Источники: игр — {len(games)}, файлов — {total_files}")

    order = scan_order(games)
    workers = max(1, min(s.threads, 1 if s.limit_resources else 4))
    need_eps = max(1, math.ceil(s.target / (s.pre + s.post + 8)))
    factor = {"Быстро": 2, "Сбалансировано": 4, "Тщательно": None}.get(s.depth, 4)

    pool, done_n = [], 0
    per_game_good, per_game_done = Counter(), Counter()
    game_total = {g: len(v) for g, v in games.items()}
    info_cache = {}

    def task(item):
        game, path = item
        info = probe(ffmpeg, path)
        info_cache[path] = (info["w"], info["h"])
        if not info["video"] or info["dur"] < s.min_len + 2:
            return []
        f = get_features(ffmpeg, path, game, info, s, cancelled)
        used = history.ranges(path) if s.no_repeat else []
        eps = episodes_from_features(f, s, used)
        for e in eps:
            e.src_w, e.src_h = info["w"], info["h"]
        return eps

    def enough():
        if factor is None:
            return False
        if sum(per_game_good.values()) < need_eps * factor:
            return False
        if s.balance and len(games) > 1:
            share = need_eps * factor / len(games)
            for g in games:
                if per_game_good[g] < share and per_game_done[g] < game_total[g]:
                    return False
        return True

    ex = ThreadPoolExecutor(max_workers=workers)
    it = iter(order)
    pending, stop = {}, False
    try:
        while True:
            while not stop and len(pending) < workers:
                nxt = next(it, None)
                if nxt is None:
                    break
                pending[ex.submit(task, nxt)] = nxt
            if not pending:
                break
            done, _ = wait(list(pending), timeout=0.5, return_when=FIRST_COMPLETED)
            if cancelled():
                raise Cancelled()
            for fu in done:
                game, path = pending.pop(fu)
                done_n += 1
                per_game_done[game] += 1
                try:
                    eps = fu.result()
                except Cancelled:
                    raise
                except Exception as e:
                    rep.log(f"Пропуск {os.path.basename(path)}: {e}")
                    eps = []
                pool.extend(eps)
                per_game_good[game] += sum(1 for e in eps if e.score >= GOOD_SCORE)
                rep.bar(0, done_n / max(1, len(order)))
                rep.status(f"Анализ: {done_n}/{len(order)} файлов, найдено моментов: {len(pool)}")
                if eps:
                    rep.log(f"[{game}] {os.path.basename(path)} → моментов: {len(eps)}")
            if not stop and enough():
                stop = True
                rep.log("Найдено достаточно сильных моментов — поиск остановлен досрочно.")
                for fu in list(pending):
                    if fu.cancel():
                        pending.pop(fu)
    finally:
        ex.shutdown(wait=True, cancel_futures=True)
    rep.bar(0, 1.0)
    if not pool:
        raise RuntimeError("Не найдено подходящих моментов. Попробуйте отключить некоторые фильтры.")

    rep.status("Проверяю лучшие моменты по реальному видео и звуку…")
    budget = s.target if s.strict else s.target * 1.1
    for e in pool:
        e.eff = e.score * (1 + s.variety * random.uniform(-0.5, 0.5))
    ranked = sorted(pool, key=lambda e: -e.eff)
    st = PlanState(s, ffmpeg, [], ranked, games, info_cache)
    cursor, batch = 0, max(4, workers)
    vex = ThreadPoolExecutor(max_workers=max(1, min(workers, 1 if s.limit_resources else 3)))
    try:
        while True:
            cands = sorted([r for r in st.results.values() if r], key=lambda e: -e.eff)
            plan = greedy(cands, s, budget, len(games))
            total = sum(e.dur for e in plan)
            if total >= budget * 0.93 or cursor >= len(ranked):
                break
            ok_cnt = Counter(c.path for c in cands)
            todo = []
            while cursor < len(ranked) and len(todo) < batch:
                i = cursor
                cursor += 1
                if ok_cnt[ranked[i].path] >= s.per_file_max + 1:
                    continue
                todo.append(i)
            futs = [(i, vex.submit(verify_episode, ffmpeg, ranked[i], s,
                                   info_cache.get(ranked[i].path, (0, 0)), cancelled))
                    for i in todo]
            for i, fu in futs:
                try:
                    res, why = fu.result()
                except Cancelled:
                    raise
                except Exception as e:
                    res, why = None, str(e)
                st.results[i] = res
                if res is None:
                    rep.log(f"Отброшен момент [{ranked[i].game}] {os.path.basename(ranked[i].path)} "
                            f"{fmt_time(ranked[i].start)}: {why}")
            rep.status(f"Проверка моментов: {len(st.results)}/{len(ranked)}")
    finally:
        vex.shutdown(wait=True, cancel_futures=True)
    if not plan:
        raise RuntimeError("Моменты найдены, но не прошли проверку.")
    plan = expand_to_fill(plan, s)
    plan = review_plan(plan, s, rep)
    st.plan = order_plan(plan, s)
    total = sum(e.dur for e in st.plan)
    rep.log(f"План готов за {time.time() - t_start:.0f} с: моментов — {len(st.plan)}, "
            f"{total:.0f} с (цель {s.target} с)")
    return st


def replace_episode(st, idx, cancelled):
    s, cur = st.s, st.plan[idx]
    others = [e for k, e in enumerate(st.plan) if k != idx]
    if s.mode.startswith("Фильмы"):
        existing = {(e.path, round(e.start, 2), round(e.end, 2)) for e in others}
        for candidate in st.ranked:
            key = (candidate.path, round(candidate.start, 2), round(candidate.end, 2))
            if key == (cur.path, round(cur.start, 2), round(cur.end, 2)) or key in existing:
                continue
            if not overlaps_chosen(candidate, others):
                return candidate
        return None
    fc = Counter(e.path for e in others)
    order = sorted(range(len(st.ranked)), key=lambda i: -st.ranked[i].eff)
    for same_game in (True, False):
        tries = 0
        for i in order:
            c0 = st.ranked[i]
            if (same_game and c0.game != cur.game) or i in st.taken:
                continue
            if fc[c0.path] >= s.per_file_max or overlaps_chosen(c0, others + [cur]):
                continue
            st.taken.add(i)
            if i in st.results:
                res = st.results[i]
            else:
                res, _ = verify_episode(st.ffmpeg, c0, s, st.info.get(c0.path, (0, 0)), cancelled)
                st.results[i] = res
            tries += 1
            if res is not None and not overlaps_chosen(res, others + [cur]):
                return res
            if tries >= 12:
                break
    return None


def make_manual_episode(ffmpeg, path, a, b, game):
    info = probe(ffmpeg, path)
    return Episode(path, game, a, b, a, b, 1.0, "вручную", info["audio"], info["w"], info["h"],
                   info["dur"], manual=True)


LASER_LEVEL_ICON = {"ok": "✅", "info": "ℹ", "warn": "⚠", "error": "✖"}


def laser_timing_totals(diags):
    keys = ("extract_s", "detect_s", "png_s", "encode_s", "verify_s", "total_s")
    return {k: round(sum(float(d.get(k, 0.0) or 0.0) for d in diags), 2) for k in keys}


def laser_clip_has_lasers(d):
    return d.get("frames_with_lasers", 0) > 0 and d.get("level") != "error" and d.get("verified") is not False


def laser_run_problems(state):
    """[(уровень, текст)] — что пользователь должен увидеть после экспорта; ошибки идут первыми.
    Предупреждения (нет меток и автопоиск пуст) попадают в окно только вместе с ошибкой или если лазеров нет нигде."""
    diags = sorted(state.get("laser_diagnostics", []), key=lambda d: d.get("clip_start", 0))
    problems = [(d["level"], f"{d.get('clip')} {d.get('clip_start', 0):.1f}–{d.get('clip_end', 0):.1f} с: {d.get('reason', '')}")
                for d in diags if d.get("level") in ("warn", "error")]
    problems.sort(key=lambda p: 0 if p[0] == "error" else 1)
    has_error = any(p[0] == "error" for p in problems)
    nowhere = bool(diags) and not any(laser_clip_has_lasers(d) for d in diags)
    return problems if (has_error or nowhere) else []


def laser_report_lines(state, s):
    diags = sorted(state.get("laser_diagnostics", []), key=lambda d: d.get("clip_start", 0))
    lines = ["GAME AUTOMIX — диагностика лазеров", f"Создано: {datetime.now():%Y-%m-%d %H:%M:%S}",
             f"Режим кадрирования: {s.frame_mode}; размер {s.width}×{s.height}; ручной слой {LASER_MANUAL_MIN_FPS}–{LASER_MANUAL_FPS} fps (адаптивно), "
             f"автопоиск {LASER_FPS} fps", ""]
    for d in diags:
        icon = LASER_LEVEL_ICON.get(d.get("level"), "?")
        lines.extend([
            f"{icon} Файл: {d.get('clip')}",
            f"   Фрагмент источника: {d.get('clip_start', 0):.3f}–{d.get('clip_end', 0):.3f} с",
            f"   РЕЗУЛЬТАТ: {d.get('reason', '')}",
            f"   Режим: {'только ручная разметка (автопоиск отключён)' if d.get('manual_only') else 'автоматический поиск'}",
            f"   Файл меток: {d.get('annotation_file', '')} ({'найден' if d.get('annotation_file_exists') else 'не найден'}); "
            f"меток в файле {d.get('manual_keyframes', 0)}, в/около фрагмента {d.get('manual_keyframes_in_clip', 0)}",
            f"   Кадров слоя: {d.get('layer_frames', 0)} ({d.get('layer_fps', 0):g} fps, сдвиг {d.get('layer_offset', 0):.2f} с); "
            f"совпали с метками {d.get('manual_matched_frames', 0)}; с видимыми ручными лучами {d.get('manual_frames', 0)}; "
            f"точки вне кадра {d.get('manual_outside_crop_frames', 0)}; с любыми лучами {d.get('frames_with_lasers', 0)}",
            f"   Проверка готового клипа: " + ("лучи найдены" if d.get("verified") is True else
                                               "ЛУЧИ НЕ НАЙДЕНЫ" if d.get("verified") is False else "не выполнялась")
            + (f" ({d.get('probe_pixels')} красных пикселей)" if d.get("probe_pixels") is not None else ""),
            f"   Время, с: извлечение кадров {d.get('extract_s', 0):.2f}; автопоиск {d.get('detect_s', 0):.2f}; "
            f"создание PNG {d.get('png_s', 0):.2f}; кодирование+наложение {d.get('encode_s', 0):.2f}; "
            f"проверка {d.get('verify_s', 0):.2f}; подготовка слоя всего {d.get('total_s', 0):.2f}",
            ""])
    tot = laser_timing_totals(diags)
    lines.append(f"ИТОГО по лазерам, с: извлечение кадров {tot['extract_s']}; автопоиск {tot['detect_s']}; "
                 f"создание PNG {tot['png_s']}; кодирование+наложение {tot['encode_s']}; проверка {tot['verify_s']}")
    issues = state.get("laser_issues", [])
    if issues:
        lines += ["", "Журнал ошибок FFmpeg и проверок:"]
        for it in issues:
            lines.append(f"- [{it['level']}] {it['clip']} {it['start']:.1f}–{it['end']:.1f} с: {it['message']}")
            if it.get("tech"):
                lines.append("    техническая причина: " + str(it["tech"]).replace("\n", "\n    "))
    return lines


def report_laser_run(state, s, rep):
    """Пишет в журнал по строке на клип и итоги по времени. Возвращает короткий текст проблемы или ''."""
    diags = sorted(state.get("laser_diagnostics", []), key=lambda d: d.get("clip_start", 0))
    for d in diags:
        icon = LASER_LEVEL_ICON.get(d.get("level"), "?")
        rep.log(f"{icon} Лазеры [{d.get('clip')} {d.get('clip_start', 0):.1f}–{d.get('clip_end', 0):.1f} с]: {d.get('reason', '')}")
    tot = laser_timing_totals(diags)
    rep.log(f"Лазеры — время, с: извлечение кадров {tot['extract_s']}; автопоиск {tot['detect_s']}; "
            f"создание PNG {tot['png_s']}; кодирование+наложение {tot['encode_s']}; проверка {tot['verify_s']}")
    errors = [d for d in diags if d.get("level") == "error"]
    if errors:
        return f"лазеры отсутствуют или не подтверждены в {len(errors)} фрагм.:"
    if diags and not any(laser_clip_has_lasers(d) for d in diags):
        return "лазеров нет ни в одном фрагменте:"
    return ""


def render_plan(st, rep, cancelled, history=None):
    t_start = time.time()
    s, ffmpeg = st.s, st.ffmpeg
    history = history if history is not None else History()
    plan = [replace(e) for e in st.plan]
    if not plan:
        raise RuntimeError("План пуст — нечего монтировать.")
    decide_effects(plan, s)
    if s.laser_effect:
        # Зум меняет координаты кадра после детекции и мешает привязке лучей к глазам.
        for e in plan:
            e.zoom = False
    if s.laser_effect and cv2 is None:
        raise RuntimeError("Для лазеров установите бесплатный пакет: pip install opencv-python pillow")
    prev_game = None
    for e in plan:
        e.title = e.game if (s.titles and e.game != prev_game) else ""
        prev_game = e.game
    total = sum(e.dur for e in plan)
    rep.log(f"Монтаж: фрагментов — {len(plan)}, длительность — {total:.0f} с")

    tmp = tempfile.mkdtemp(prefix="automix_")
    try:
        enc = detect_hw_encoder(ffmpeg) if s.hw else None
        rep.log("Кодирование: " + (f"аппаратное ({enc})" if enc else "процессор (x264)"))
        inter = not s.transitions.startswith("Только")
        state = {
            "mixed": False, "q": "Промежуточное" if inter else s.quality,
            "laser_diagnostics": [], "laser_warnings": [], "laser_diag_lock": threading.Lock(),
            "laser_reporter": rep,
        }
        outs = [os.path.join(tmp, f"clip_{i:03d}.mp4") for i in range(len(plan))]
        workers = max(1, min(s.threads, 1 if s.limit_resources else 4))
        rex = ThreadPoolExecutor(max_workers=max(1, min(1 if s.limit_resources else 3, workers)))
        render_settings = replace(s, width=1080, height=1920) if s.shorts_mode else s
        ok, finished = {}, 0
        try:
            futs = {rex.submit(render_one, ffmpeg, e, outs[i], render_settings, enc, state, tmp, cancelled): i
                    for i, e in enumerate(plan)}
            pend = set(futs)
            while pend:
                done, pend = wait(pend, timeout=0.5, return_when=FIRST_COMPLETED)
                if cancelled():
                    raise Cancelled()
                for fu in done:
                    ok[futs[fu]] = fu.result()
                    finished += 1
                    rep.bar(1, finished / len(plan))
                    rep.status(f"Нарезка: {finished}/{len(plan)}")
        finally:
            rex.shutdown(wait=True, cancel_futures=True)
        good = [i for i in range(len(plan)) if ok.get(i)]
        laser_problem = ""
        if s.laser_effect:
            laser_problem = report_laser_run(state, s, rep)
        if not good:
            raise RuntimeError("Не удалось вырезать ни одного момента.")
        rep.bar(1, 1.0)

        rep.status("Склейка, переходы и нормализация звука…")
        rep.bar(2, 0.2)
        os.makedirs(s.out_dir, exist_ok=True)
        stamp = f"{datetime.now():%Y%m%d_%H%M%S}"
        final = [plan[i] for i in good]
        if s.shorts_mode:
            # Shorts: каждый уже обрезанный фрагмент становится отдельным вертикальным MP4.
            shorts_dir = os.path.join(s.out_dir, f"Shorts_{stamp}")
            os.makedirs(shorts_dir, exist_ok=True)
            out_paths = []
            for n, i in enumerate(good, 1):
                if cancelled():
                    raise Cancelled()
                out_path = os.path.join(shorts_dir, f"short_{n:03d}.mp4")
                normalize_audio(ffmpeg, outs[i], out_path, s, cancelled)
                out_paths.append(out_path)
                rep.bar(2, 0.2 + 0.8 * n / len(good))
                rep.status(f"Экспорт Shorts: {n}/{len(good)}")
            out_path = shorts_dir
            rep.log(f"Shorts сохранены отдельными файлами: {len(out_paths)}")
        else:
            out_path = os.path.join(s.out_dir, f"automix_{stamp}.mp4")
            raw = assemble(ffmpeg, [outs[i] for i in good], final, s, enc, tmp, cancelled, rep,
                           reencode=inter)
            rep.bar(2, 0.7)
            normalize_audio(ffmpeg, raw, out_path, s, cancelled)
            rep.bar(2, 1.0)

        try:
            with open(os.path.join(s.out_dir, f"automix_{stamp}_plan.txt"), "w",
                      encoding="utf-8") as r:
                t = 0.0
                for e in final:
                    r.write(f"{fmt_time(t)}–{fmt_time(t + e.dur)} | {e.game} | "
                            f"{os.path.basename(e.path)} {fmt_time(e.start)}–{fmt_time(e.end)}"
                            f" | {e.tag} | оценка {e.score:.2f} | реакция {e.reaction:.2f}"
                            f"{' | зум' if e.zoom else ''}{' | вручную' if e.manual else ''}\n")
                    t += e.dur
        except Exception:
            pass
        if s.laser_effect:
            diag_path = ""
            try:
                diag_path = os.path.join(s.out_dir, f"automix_{stamp}_laser_diagnostics.txt")
                with open(diag_path, "w", encoding="utf-8") as f:
                    f.write("\n".join(laser_report_lines(state, s)))
                rep.log(f"Отчёт диагностики лазеров сохранён: {diag_path}")
            except OSError as exc:
                rep.log(f"⚠ Не удалось сохранить отчёт диагностики лазеров: {exc}")
            problems = laser_run_problems(state)
            try:
                st.laser_problem = laser_problem
            except Exception:
                pass
            if problems:
                alert = getattr(rep, "alert", None)
                if alert is not None:
                    shown = "\n\n".join(f"{'✖' if lv == 'error' else '⚠'} {txt}" for lv, txt in problems[:6])
                    more = f"\n\n… и ещё {len(problems) - 6}." if len(problems) > 6 else ""
                    alert("Лазеры: есть проблемы",
                          "Видео собрано, но лазеры есть не везде, где ожидалось:\n\n" + shown + more +
                          (f"\n\nПодробный отчёт: {diag_path}" if diag_path else ""))
        if s.no_repeat:
            for e in final:
                history.add(e.path, e.start, e.end)
            history.save()
        rep.log(f"Готово за {time.time() - t_start:.0f} с: {out_path}")
        return out_path
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ──────────────────────────────────────────────────────────────────────────────
#  Интерфейс
# ──────────────────────────────────────────────────────────────────────────────
class QueueReporter:
    def __init__(self, q):
        self.q = q

    def log(self, m):
        self.q.put(("log", m))

    def bar(self, i, v):
        self.q.put(("bar", i, v))

    def status(self, t):
        self.q.put(("status", t))

    def alert(self, title, text):
        self.q.put(("alert", title, text))


class FilePicker(ctk.CTkToplevel):
    def __init__(self, parent, items, selected, on_done):
        super().__init__(parent)
        self.title("Выбор видео для монтажа")
        self.geometry("920x640")
        self.items, self.selected, self.on_done = items, set(selected), on_done
        self.visible = []
        top = ctk.CTkFrame(self)
        top.pack(fill="x", padx=10, pady=8)
        self.qv = ctk.StringVar()
        self.qv.trace_add("write", lambda *_: self.refilter())
        ctk.CTkEntry(top, textvariable=self.qv,
                     placeholder_text="Фильтр: название игры или файла…"
                     ).pack(side="left", fill="x", expand=True)
        frame = ctk.CTkFrame(self)
        frame.pack(fill="both", expand=True, padx=10)
        self.lb = tk.Listbox(frame, selectmode="extended", exportselection=False,
                             bg="#2b2b2b", fg="#e6e6e6", selectbackground="#1f6aa5",
                             highlightthickness=0, borderwidth=0, activestyle="none")
        sb = tk.Scrollbar(frame, command=self.lb.yview)
        self.lb.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.lb.pack(side="left", fill="both", expand=True)
        self.lb.bind("<<ListboxSelect>>", self._on_select)
        bt = ctk.CTkFrame(self, fg_color="transparent")
        bt.pack(fill="x", padx=10, pady=8)
        ctk.CTkButton(bt, text="Выделить все видимые", width=170,
                      command=self.select_visible).pack(side="left")
        ctk.CTkButton(bt, text="Снять все видимые", width=150, fg_color="#555",
                      command=self.clear_visible).pack(side="left", padx=8)
        self.cnt = ctk.CTkLabel(bt, text="")
        self.cnt.pack(side="left", padx=10)
        ctk.CTkButton(bt, text="Готово", width=110, command=self.finish).pack(side="right")
        self.refilter()
        self.after(150, lambda: (self.lift(), self.focus_force()))

    def refilter(self):
        q = self.qv.get().strip().lower()
        self.visible = [it for it in self.items if q in it[2].lower()]
        self.lb.delete(0, "end")
        for _, _, label in self.visible:
            self.lb.insert("end", label)
        for i, (_, p, _) in enumerate(self.visible):
            if p in self.selected:
                self.lb.selection_set(i)
        self.cnt.configure(text=f"Выбрано: {len(self.selected)}")

    def _on_select(self, _=None):
        sel = set(self.lb.curselection())
        for i, (_, p, _) in enumerate(self.visible):
            (self.selected.add if i in sel else self.selected.discard)(p)
        self.cnt.configure(text=f"Выбрано: {len(self.selected)}")

    def select_visible(self):
        self.selected.update(p for _, p, _ in self.visible)
        self.refilter()

    def clear_visible(self):
        self.selected.difference_update(p for _, p, _ in self.visible)
        self.refilter()

    def finish(self):
        self.on_done(sorted(self.selected))
        self.destroy()


def fmt_tc(t):
    t = max(0.0, float(t))
    m, s = int(t // 60), t - 60 * int(t // 60)
    if m >= 60:
        return f"{m // 60}:{m % 60:02d}:{s:04.1f}"
    return f"{m}:{s:04.1f}"


def parse_tc(text):
    text = text.strip().replace(",", ".")
    if not text:
        raise ValueError("пустой таймкод")
    parts = text.split(":")
    if len(parts) > 3:
        raise ValueError("неверный таймкод")
    t = 0.0
    for p in parts:
        t = t * 60 + float(p)
    return t


def fmt_clock(t):
    return f"{int(t // 60)}:{int(t % 60):02d}"


def grab_frame(ffmpeg, path, t, width):
    code, out, _ = run([ffmpeg, "-nostdin", "-v", "error", "-ss", f"{max(0.0, t):.3f}", "-i",
                        path, "-frames:v", "1", "-vf", f"scale={width}:-2",
                        "-f", "image2pipe", "-vcodec", "png", "-"])
    return out if code == 0 and out else None


def open_external(path):
    try:
        if sys.platform.startswith("win"):
            os.startfile(path)
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
    except Exception:
        pass


class Timeline(tk.Canvas):
    PAD = 12

    def __init__(self, parent, dur, on_seek, on_range, height=74):
        super().__init__(parent, height=height, bg="#1b1b1b", highlightthickness=0)
        self.dur = max(1.0, dur)
        self.va, self.vb = 0.0, self.dur
        self.a, self.b = 0.0, self.dur
        self.core = None
        self.cur = 0.0
        self.on_seek, self.on_range = on_seek, on_range
        self.mode = None
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Button-1>", self._down)
        self.bind("<B1-Motion>", self._move)
        self.bind("<ButtonRelease-1>", lambda e: setattr(self, "mode", None))

    def set_view(self, va, vb):
        self.va = max(0.0, va)
        self.vb = min(self.dur, max(vb, self.va + 1.0))
        self.redraw()

    def set_range(self, a, b):
        self.a, self.b = a, b
        self.redraw()

    def set_cur(self, t):
        self.cur = t
        self.redraw()

    def t2x(self, t):
        w = max(1, self.winfo_width() - 2 * self.PAD)
        return self.PAD + (t - self.va) / (self.vb - self.va) * w

    def x2t(self, x):
        w = max(1, self.winfo_width() - 2 * self.PAD)
        return min(self.vb, max(self.va, self.va + (x - self.PAD) / w * (self.vb - self.va)))

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 40:
            return
        self.create_rectangle(self.PAD, 22, w - self.PAD, h - 8, fill="#2a2a2a", outline="")
        span = self.vb - self.va
        step = 1800
        for st in (1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 1800):
            if st / span * (w - 2 * self.PAD) >= 70:
                step = st
                break
        t = math.ceil(self.va / step) * step
        while t <= self.vb:
            x = self.t2x(t)
            self.create_line(x, 14, x, h - 8, fill="#444")
            self.create_text(x + 3, 9, text=fmt_clock(t), anchor="w", fill="#999", font=("TkDefaultFont", 8))
            t += step
        xa, xb = self.t2x(min(max(self.a, self.va), self.vb)), self.t2x(min(max(self.b, self.va), self.vb))
        self.create_rectangle(xa, 22, xb, h - 8, fill="#245d8f", outline="")
        if self.core:
            c1, c2 = self.t2x(min(max(self.core[0], self.va), self.vb)), self.t2x(min(max(self.core[1], self.va), self.vb))
            self.create_rectangle(c1, h - 15, c2, h - 8, fill="#e0902a", outline="")
        for x in (xa, xb):
            self.create_rectangle(x - 4, 18, x + 4, h - 4, fill="#ffffff", outline="")
        xp = self.t2x(min(max(self.cur, self.va), self.vb))
        self.create_line(xp, 4, xp, h, fill="#ff4d4d", width=2)

    def _down(self, e):
        xa, xb = self.t2x(self.a), self.t2x(self.b)
        self.mode = "a" if abs(e.x - xa) <= 9 else "b" if abs(e.x - xb) <= 9 else "seek"
        self._move(e)

    def _move(self, e):
        t = self.x2t(e.x)
        if self.mode == "a":
            self.a = min(t, self.b - 0.5)
            self.on_range(self.a, self.b)
        elif self.mode == "b":
            self.b = max(t, self.a + 0.5)
            self.on_range(self.a, self.b)
        elif self.mode == "seek":
            self.cur = t
            self.on_seek(t)
        self.redraw()


class PlayerPanel(ctk.CTkFrame):
    def __init__(self, parent, ffmpeg, path, width=640, on_time=None):
        super().__init__(parent, fg_color="#000000")
        self.ffmpeg, self.path, self.W = ffmpeg, path, width
        self.H = int(width * 9 / 16)
        self.on_time = on_time
        self.cur, self.stop_at, self.playing = 0.0, None, False
        self.backend, self.vlc, self.player, self.inst = "scrub", None, None, None
        self._q = queue.Queue()
        self._busy, self._pending, self._closed, self._img = False, None, False, None
        self._last = time.time()
        self.screen = tk.Frame(self, width=self.W, height=self.H, bg="black")
        self.img_lbl = ctk.CTkLabel(self, text="Загрузка кадра…", width=self.W, height=self.H)
        self.img_lbl.pack()
        if self._init_vlc():
            self.img_lbl.pack_forget()
            self.screen.pack()
            self.update_idletasks()
            self._attach_vlc()
        self.after(100, self._tick)

    def _init_vlc(self):
        if sys.platform == "darwin":
            return False
        try:
            import vlc
            inst = vlc.Instance("--quiet")
            if inst is None:
                return False
            self.vlc, self.inst = vlc, inst
            self.player = inst.media_player_new()
            self.player.set_media(inst.media_new(self.path))
            self.backend = "vlc"
            return True
        except Exception:
            self.vlc = self.inst = self.player = None
            return False

    def _attach_vlc(self):
        try:
            wid = self.screen.winfo_id()
            if sys.platform.startswith("win"):
                self.player.set_hwnd(wid)
            else:
                self.player.set_xwindow(wid)
        except Exception:
            self._to_scrub()

    def _to_scrub(self):
        self.backend = "scrub"
        try:
            self.player.stop()
        except Exception:
            pass
        self.screen.pack_forget()
        self.img_lbl.pack()

    def seek(self, t):
        t = max(0.0, t)
        self.cur = t
        if self.backend == "vlc":
            try:
                if not self.playing:
                    self.player.audio_set_mute(True)
                if self.player.get_state() not in (self.vlc.State.Playing, self.vlc.State.Paused):
                    self.player.play()
                self.player.set_time(int(t * 1000))
                if not self.playing:
                    self.after(150, self._vlc_pause)
                return
            except Exception:
                self._to_scrub()
        self._request(t)

    def _vlc_pause(self):
        try:
            if not self.playing and self.backend == "vlc":
                self.player.set_pause(1)
        except Exception:
            pass

    def play(self, start=None, stop=None):
        if start is not None:
            self.seek(start)
        self.stop_at, self.playing, self._last = stop, True, time.time()
        if self.backend == "vlc":
            try:
                self.player.audio_set_mute(False)
                self.player.set_pause(0)
                if self.player.get_state() not in (self.vlc.State.Playing, self.vlc.State.Paused):
                    self.player.play()
            except Exception:
                self._to_scrub()

    def pause(self):
        self.playing = False
        if self.backend == "vlc":
            try:
                self.player.set_pause(1)
            except Exception:
                pass

    def close(self):
        self._closed = True
        try:
            if self.player is not None:
                self.player.stop()
                self.player.release()
            if self.inst is not None:
                self.inst.release()
        except Exception:
            pass

    def _request(self, t):
        if self._busy:
            self._pending = t
            return
        self._busy = True

        def work():
            self._q.put(grab_frame(self.ffmpeg, self.path, t, self.W))
        threading.Thread(target=work, daemon=True).start()

    def _show(self, data):
        if Image is None:
            return
        try:
            img = Image.open(io.BytesIO(data))
            self._img = ctk.CTkImage(light_image=img, dark_image=img, size=img.size)
            self.img_lbl.configure(image=self._img, text="")
        except Exception:
            pass

    def _tick(self):
        if self._closed:
            return
        try:
            while True:
                try:
                    data = self._q.get_nowait()
                except queue.Empty:
                    break
                if data:
                    self._show(data)
                self._busy = False
                if self._pending is not None:
                    t, self._pending = self._pending, None
                    self._request(t)
            if self.playing:
                if self.backend == "vlc":
                    t = self.player.get_time() / 1000.0
                    if t >= 0:
                        self.cur = t
                else:
                    now = time.time()
                    self.cur += now - self._last
                    self._last = now
                    self._request(self.cur)
                if self.stop_at is not None and self.cur >= self.stop_at:
                    self.pause()
                if self.on_time:
                    self.on_time(self.cur)
        except Exception:
            pass
        self.after(100, self._tick)


class FragmentEditor(ctk.CTkToplevel):
    def __init__(self, parent, ffmpeg, ep, on_apply, on_remove=None, on_replace=None,
                 autoplay=False, new=False):
        super().__init__(parent)
        self.title("Новый момент" if new else "Предпросмотр и подгонка момента")
        self.geometry("880x820")
        self.minsize(780, 760)
        self.ffmpeg, self.ep = ffmpeg, ep
        self.dur = max(1.0, ep.file_dur)
        self.on_apply, self.on_remove, self.on_replace = on_apply, on_remove, on_replace
        self.a, self.b = ep.start, ep.end
        self.q = queue.Queue()
        self.wide = False
        self.columnconfigure(0, weight=1)

        ctk.CTkLabel(self, text=f"[{ep.game}]  {os.path.basename(ep.path)}   "
                                f"(длина файла {fmt_tc(self.dur)})", anchor="w",
                     font=ctk.CTkFont(weight="bold")).grid(row=0, column=0, sticky="ew",
                                                           padx=14, pady=(12, 2))
        self.player = PlayerPanel(self, ffmpeg, ep.path, width=640, on_time=self._on_time)
        self.player.grid(row=1, column=0, pady=4)
        self.tl = Timeline(self, self.dur, self._tl_seek, self._tl_range)
        self.tl.grid(row=2, column=0, sticky="ew", padx=14, pady=(4, 0))
        if not ep.manual and ep.core_e > ep.core_s:
            self.tl.core = (ep.core_s, ep.core_e)
        self.tl.set_range(self.a, self.b)

        nav = ctk.CTkFrame(self, fg_color="transparent")
        nav.grid(row=3, column=0, sticky="ew", padx=14, pady=4)
        self.cur_lbl = ctk.CTkLabel(nav, text="Текущее: 0:00.0", width=130, anchor="w")
        self.cur_lbl.pack(side="left")
        for txt, dt in (("−5 с", -5), ("−1 с", -1), ("−0.2", -0.2), ("+0.2", 0.2),
                        ("+1 с", 1), ("+5 с", 5)):
            ctk.CTkButton(nav, text=txt, width=54, height=28, fg_color="#444",
                          command=lambda d=dt: self.nudge(d)).pack(side="left", padx=2)
        self.view_btn = ctk.CTkButton(nav, text="Весь файл", width=100, height=28,
                                      fg_color="#444", command=self.toggle_view)
        self.view_btn.pack(side="right")

        tc = ctk.CTkFrame(self)
        tc.grid(row=4, column=0, sticky="ew", padx=14, pady=4)
        ctk.CTkLabel(tc, text="С:").grid(row=0, column=0, padx=(10, 2), pady=8)
        self.a_var = ctk.StringVar(value=fmt_tc(self.a))
        ea = ctk.CTkEntry(tc, textvariable=self.a_var, width=90, justify="center")
        ea.grid(row=0, column=1)
        ctk.CTkButton(tc, text="[ = текущее", width=100, height=28,
                      command=self.set_a_here).grid(row=0, column=2, padx=6)
        ctk.CTkLabel(tc, text="ПО:").grid(row=0, column=3, padx=(14, 2))
        self.b_var = ctk.StringVar(value=fmt_tc(self.b))
        eb = ctk.CTkEntry(tc, textvariable=self.b_var, width=90, justify="center")
        eb.grid(row=0, column=4)
        ctk.CTkButton(tc, text="] = текущее", width=100, height=28,
                      command=self.set_b_here).grid(row=0, column=5, padx=6)
        self.len_lbl = ctk.CTkLabel(tc, text="", width=110)
        self.len_lbl.grid(row=0, column=6, padx=10)
        for e in (ea, eb):
            e.bind("<Return>", lambda _e: self.commit_entries())
            e.bind("<FocusOut>", lambda _e: self.commit_entries())

        pl = ctk.CTkFrame(self, fg_color="transparent")
        pl.grid(row=5, column=0, sticky="ew", padx=14, pady=4)
        ctk.CTkButton(pl, text="▶ Играть отрезок", width=140, command=self.play_range).pack(side="left")
        ctk.CTkButton(pl, text="⏸ Пауза", width=80, fg_color="#555",
                      command=self.player.pause).pack(side="left", padx=6)
        ctk.CTkButton(pl, text="Смотреть со звуком", width=150, fg_color="#555",
                      command=self.preview_with_audio).pack(side="left")
        ctk.CTkButton(pl, text="Подогнать к паузам", width=150, fg_color="#555",
                      command=self.snap_pauses).pack(side="left", padx=6)
        ctk.CTkButton(pl, text="🔴 Лазеры в этом кадре", width=170,
                      command=self.open_laser_annotation_here).pack(side="left", padx=6)

        ac = ctk.CTkFrame(self, fg_color="transparent")
        ac.grid(row=6, column=0, sticky="ew", padx=14, pady=(8, 4))
        ctk.CTkButton(ac, text="✔ Применить" if not new else "✔ Добавить", width=130,
                      command=self.apply).pack(side="left")
        if on_replace and not new:
            ctk.CTkButton(ac, text="↻ Заменить другим", width=150, fg_color="#555",
                          command=self.replace_other).pack(side="left", padx=6)
        if on_remove and not new:
            ctk.CTkButton(ac, text="✕ Убрать момент", width=140, fg_color="#8a2f2f",
                          hover_color="#a33", command=self.remove).pack(side="left", padx=6)
        ctk.CTkButton(ac, text="Закрыть", width=90, fg_color="#444",
                      command=self.close).pack(side="right")
        self.msg = ctk.CTkLabel(self, text="", anchor="w", wraplength=820, justify="left")
        self.msg.grid(row=7, column=0, sticky="ew", padx=14, pady=(2, 10))

        self.protocol("WM_DELETE_WINDOW", self.close)
        self._fit_view()
        self._upd_len()
        self.after(100, self._poll)
        self.after(350, lambda: self.player.seek(self.a))
        if autoplay:
            self.after(900, self.play_range)
        self.after(200, lambda: (self.lift(), self.focus_force()))

    def open_laser_annotation_here(self):
        """Open the laser annotator on the exact source-video time at the playhead."""
        self.player.pause()
        if cv2 is None or Image is None or ImageTk is None:
            messagebox.showerror(
                "Не хватает библиотек",
                "Ручная разметка требует OpenCV и Pillow. Установи: python -m pip install opencv-python pillow",
                parent=self)
            return
        LaserAnnotationWindow(self, self.ep.path, start_time=self.player.cur)

    def _fit_view(self):
        if self.wide:
            self.tl.set_view(0, self.dur)
        else:
            self.tl.set_view(self.a - 30, self.b + 30)

    def toggle_view(self):
        self.wide = not self.wide
        self.view_btn.configure(text="Вокруг момента" if self.wide else "Весь файл")
        self._fit_view()

    def _upd_len(self):
        self.len_lbl.configure(text=f"Длина: {max(0.0, self.b - self.a):.1f} с")

    def _on_time(self, t):
        self.tl.set_cur(t)
        self.cur_lbl.configure(text=f"Текущее: {fmt_tc(t)}")

    def _tl_seek(self, t):
        self.player.seek(t)
        self.cur_lbl.configure(text=f"Текущее: {fmt_tc(t)}")

    def _tl_range(self, a, b):
        self.a, self.b = a, b
        self.a_var.set(fmt_tc(a))
        self.b_var.set(fmt_tc(b))
        self._upd_len()

    def commit_entries(self):
        try:
            a, b = parse_tc(self.a_var.get()), parse_tc(self.b_var.get())
        except ValueError:
            self.msg.configure(text="⚠ Неверный таймкод.")
            return
        a, b = max(0.0, a), min(self.dur, b)
        if b - a < 0.5:
            self.msg.configure(text="⚠ Конец должен быть позже начала хотя бы на 0.5 с.")
            return
        self.msg.configure(text="")
        self.a, self.b = a, b
        self.tl.set_range(a, b)
        self._upd_len()
        if not (self.tl.va <= a and b <= self.tl.vb):
            self._fit_view()

    def nudge(self, dt):
        t = min(self.dur, max(0.0, self.player.cur + dt))
        self.player.seek(t)
        self._on_time(t)

    def set_a_here(self):
        self._tl_range(min(self.player.cur, self.b - 0.5), self.b)
        self.tl.set_range(self.a, self.b)

    def set_b_here(self):
        self._tl_range(self.a, max(self.player.cur, self.a + 0.5))
        self.tl.set_range(self.a, self.b)

    def play_range(self):
        self.commit_entries()
        self.player.play(self.a, self.b)

    def preview_with_audio(self):
        self.commit_entries()
        self.msg.configure(text="Готовлю предпросмотр со звуком…")
        a, b = self.a, self.b
        path, ffmpeg = self.ep.path, self.ffmpeg

        def work():
            out = os.path.join(tempfile.gettempdir(), f"automix_preview_{int(time.time())}.mp4")
            code, _, _ = run([ffmpeg, "-y", "-nostdin", "-v", "error", "-ss", f"{a:.3f}", "-i", path,
                                "-t", f"{b - a:.3f}", "-vf", "scale=-2:480", "-c:v", "libx264",
                                "-preset", "ultrafast", "-crf", "28", "-af", "apad", "-c:a", "aac", out])
            self.q.put(("preview", out if code == 0 else None))
        threading.Thread(target=work, daemon=True).start()

    def snap_pauses(self):
        self.commit_entries()
        self.msg.configure(text="Ищу паузы в речи…")
        ep, a, b = self.ep, self.a, self.b

        def work():
            try:
                ns, ne, _, _ = refine_cuts(self.ffmpeg, ep.path, a, b, a + 0.9, b - 0.9, 0.0,
                                           self.dur, None)
                self.q.put(("snap", (ns, ne)))
            except Exception as e:
                self.q.put(("snap", e))
        threading.Thread(target=work, daemon=True).start()

    def _poll(self):
        try:
            while True:
                kind, val = self.q.get_nowait()
                if kind == "preview":
                    if val:
                        self.msg.configure(text="Открыл предпросмотр во внешнем плеере.")
                        open_external(val)
                    else:
                        self.msg.configure(text="⚠ Не удалось подготовить предпросмотр.")
                elif kind == "snap":
                    if isinstance(val, Exception):
                        self.msg.configure(text=f"⚠ {val}")
                    else:
                        self._tl_range(val[0], val[1])
                        self.tl.set_range(self.a, self.b)
                        self.msg.configure(text="Границы подогнаны к паузам.")
        except queue.Empty:
            pass
        except Exception:
            pass
        if self.winfo_exists():
            self.after(100, self._poll)

    def apply(self):
        self.commit_entries()
        self.on_apply(self.a, self.b)
        self.close()

    def remove(self):
        if self.on_remove:
            self.on_remove()
        self.close()

    def replace_other(self):
        if self.on_replace:
            self.on_replace()
        self.close()

    def close(self):
        try:
            self.player.close()
        except Exception:
            pass
        self.destroy()



class LaserAnnotationWindow(ctk.CTkToplevel):
    """Manual keyframe annotator for laser origins in game footage."""
    PREVIEW_W = 880
    PREVIEW_H = 500

    def __init__(self, master, video_path, start_time=0.0):
        super().__init__(master)
        self.video_path = os.path.abspath(video_path)
        self.title("GAME AUTOMIX — ручная разметка лазеров")
        # Fit the annotator to the actual display, including laptops with small screens
        # and Windows display scaling. The canvas will follow the available space.
        screen_w = max(760, int(self.winfo_screenwidth()))
        screen_h = max(560, int(self.winfo_screenheight()))
        win_w = min(1160, screen_w - 40)
        win_h = min(830, screen_h - 70)
        win_w = max(min(760, screen_w), win_w)
        win_h = max(min(560, screen_h), win_h)
        pos_x = max(0, (screen_w - win_w) // 2)
        pos_y = max(0, (screen_h - win_h) // 2)
        self.geometry(f"{win_w}x{win_h}+{pos_x}+{pos_y}")
        self.minsize(min(760, screen_w), min(560, screen_h))
        self.transient(master)
        self.cap = cv2.VideoCapture(self.video_path) if cv2 is not None else None
        if self.cap is None or not self.cap.isOpened():
            messagebox.showerror("Не удалось открыть видео",
                                 "OpenCV не смог открыть этот файл. Проверьте формат видео и установку opencv-python.",
                                 parent=self)
            if self.cap is not None:
                self.cap.release()
            self.destroy()
            return

        self.video_fps = float(self.cap.get(cv2.CAP_PROP_FPS) or 0.0)
        if not math.isfinite(self.video_fps) or self.video_fps <= 0:
            self.video_fps = 30.0
        frame_count = float(self.cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0.0)
        self.duration = max(0.0, (frame_count - 1) / self.video_fps) if frame_count > 0 else 0.0
        try:
            start_time = float(start_time)
        except (TypeError, ValueError):
            start_time = 0.0
        self.current_time = max(0.0, min(self.duration, start_time))
        self.frame = None
        self.frame_w = 0
        self.frame_h = 0
        self.preview_w = 0
        self.preview_h = 0
        self.preview_x = 0
        self.preview_y = 0
        self.photo = None
        self._preview_base_image = None
        self._preview_cache_key = None
        self._drag_handle = None
        self.selected_points = []
        self.selected_directions = []
        self.annotations = load_manual_laser_annotations(self.video_path)
        self._updating_slider = False

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        ctk.CTkLabel(self, text=os.path.basename(self.video_path),
                     font=ctk.CTkFont(size=15, weight="bold"), anchor="w"
                     ).grid(row=0, column=0, sticky="ew", padx=14, pady=(12, 4))

        body = ctk.CTkFrame(self)
        body.grid(row=1, column=0, sticky="nsew", padx=10, pady=3)
        body.grid_columnconfigure(0, weight=1, minsize=320)
        body.grid_columnconfigure(1, weight=0)
        body.grid_rowconfigure(0, weight=1, minsize=180)
        self.canvas = tk.Canvas(body, width=self.PREVIEW_W, height=self.PREVIEW_H,
                                bg="#151515", highlightthickness=1,
                                highlightbackground="#444444", cursor="crosshair")
        self.canvas.grid(row=0, column=0, sticky="nsew", padx=(5, 3), pady=5)
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        side_width = 205 if screen_w < 1100 else 225
        side = ctk.CTkFrame(body, width=side_width)
        side.grid(row=0, column=1, sticky="nsew", padx=(3, 5), pady=5)
        side.grid_propagate(False)
        ctk.CTkLabel(side, text="Сохранённые ключевые кадры",
                     font=ctk.CTkFont(weight="bold"), wraplength=side_width - 24
                     ).pack(fill="x", padx=8, pady=(8, 4))
        self.key_list = tk.Listbox(side, bg="#252525", fg="#eeeeee",
                                   selectbackground="#1f6aa5", relief="flat",
                                   highlightthickness=0, exportselection=False,
                                   activestyle="dotbox", font=("Arial", 10))
        self.key_list.pack(fill="both", expand=True, padx=7, pady=4)
        self.key_list.bind("<<ListboxSelect>>", self.on_key_selected)
        ctk.CTkLabel(side,
                     text="Кликни по метке и перетащи её мышью, чтобы поправить. Изменения сохраняются кнопкой ниже.",
                     wraplength=side_width - 24, justify="left"
                     ).pack(fill="x", padx=8, pady=(4, 8))

        nav = ctk.CTkFrame(self, fg_color="transparent")
        nav.grid(row=2, column=0, sticky="ew", padx=14, pady=(4, 2))
        nav.grid_columnconfigure(0, weight=1)
        self.time_slider = ctk.CTkSlider(nav, from_=0, to=max(self.duration, 0.01),
                                         command=self.on_slider)
        self.time_slider.grid(row=0, column=0, sticky="ew", padx=(0, 10))
        self.time_var = ctk.StringVar(value="0.000")
        ctk.CTkEntry(nav, textvariable=self.time_var, width=100, justify="center"
                     ).grid(row=0, column=1, padx=(0, 6))
        ctk.CTkButton(nav, text="Перейти", width=90,
                      command=self.seek_from_entry).grid(row=0, column=2)

        # Split the actions into two rows so buttons do not disappear off-screen
        # at lower resolutions or with enlarged system fonts.
        controls = ctk.CTkFrame(self, fg_color="transparent")
        controls.grid(row=3, column=0, sticky="ew", padx=12, pady=(3, 1))
        for label, delta in (("−5 с", -5.0), ("−0,25 с", -0.25),
                             ("+0,25 с", 0.25), ("+5 с", 5.0)):
            ctk.CTkButton(controls, text=label, width=78,
                          command=lambda d=delta: self.show_time(self.current_time + d)
                          ).pack(side="left", padx=(0, 5))
        ctk.CTkButton(controls, text="Сохранить метку", width=142,
                      fg_color="#277a43", hover_color="#329957",
                      command=self.save_current_keyframe).pack(side="left", padx=(5, 5))
        ctk.CTkButton(controls, text="Сбросить точки", width=122,
                      command=self.reset_selected_points).pack(side="left", padx=5)

        manage = ctk.CTkFrame(self, fg_color="transparent")
        manage.grid(row=4, column=0, sticky="ew", padx=12, pady=(1, 2))
        ctk.CTkButton(manage, text="Удалить метку времени", width=145,
                      fg_color="#8a3d3d", hover_color="#a84b4b",
                      command=self.delete_current_keyframe).pack(side="left", padx=(0, 6))
        ctk.CTkButton(manage, text="Удалить всё", width=110,
                      fg_color="#555555", hover_color="#666666",
                      command=self.delete_all_keyframes).pack(side="left", padx=6)
        ctk.CTkButton(manage, text="Закрыть", width=90,
                      command=self.close_window).pack(side="right", padx=(6, 0))

        self.status_var = ctk.StringVar(value="Кликни 2 глаза, затем 2 направления. Сохранённые точки можно перетаскивать мышью; затем нажми «Сохранить метку».")
        self.status_label = ctk.CTkLabel(self, textvariable=self.status_var, anchor="w", justify="left",
                                          wraplength=max(500, win_w - 40))
        self.status_label.grid(row=5, column=0, sticky="ew", padx=14, pady=(3, 7))
        self.bind("<Configure>", self._on_window_resize)
        self.refresh_key_list()
        self.show_time(self.current_time)
        self.protocol("WM_DELETE_WINDOW", self.close_window)
        self.after(120, lambda: (self.lift(), self.focus_force()))

    def on_slider(self, value):
        if not self._updating_slider:
            self.show_time(float(value), from_slider=True)

    def seek_from_entry(self):
        try:
            value = float(self.time_var.get().replace(",", ".").strip())
        except ValueError:
            messagebox.showwarning("Время", "Введи время в секундах, например 12.500.", parent=self)
            return
        self.show_time(value)

    def show_time(self, timestamp, from_slider=False):
        if not self.winfo_exists():
            return
        timestamp = max(0.0, min(self.duration, float(timestamp)))
        self.current_time = timestamp
        self.time_var.set(f"{timestamp:.3f}")
        self._updating_slider = True
        self.time_slider.set(timestamp)
        self._updating_slider = False
        self.cap.set(cv2.CAP_PROP_POS_MSEC, timestamp * 1000.0)
        ok, frame = self.cap.read()
        if not ok or frame is None:
            self.status_var.set("Не удалось прочитать кадр на этом времени. Попробуй соседнее значение.")
            return
        self.frame = frame
        self.frame_h, self.frame_w = frame.shape[:2]
        self.selected_points = []
        self.selected_directions = []
        if self.annotations:
            nearest = min(self.annotations, key=lambda row: abs(row["time"] - timestamp))
            tolerance = max(0.045, 0.5 / self.video_fps)
            if abs(nearest["time"] - timestamp) <= tolerance:
                self.selected_points = [list(p) for p in nearest["points"]]
                self.selected_directions = [list(p) for p in nearest.get("directions", [])]
        self.draw_preview()
        if len(self.selected_points) == 2 and len(self.selected_directions) != 2:
            hint = "Загружена старая метка без направлений. Добавь 2 точки направления и сохрани заново."
        elif len(self.selected_points) == 2 and len(self.selected_directions) == 2:
            hint = "Метка загружена. Перетаскивай маркеры мышью, чтобы поправить; затем нажми «Сохранить метку»."
        else:
            hint = "Поставь 2 точки на глаза, затем по одной точке направления для каждого луча. Можно перетаскивать маркеры мышью."
        self.status_var.set(f"Время: {timestamp:.3f} с. {hint}")

    def _on_canvas_resize(self, _event=None):
        if self.frame is not None:
            self.draw_preview()

    def _on_window_resize(self, event=None):
        if event is not None and event.widget is not self:
            return
        try:
            self.status_label.configure(wraplength=max(360, self.winfo_width() - 36))
        except Exception:
            pass

    def _point_to_canvas(self, point):
        return (self.preview_x + float(point[0]) * self.preview_w,
                self.preview_y + float(point[1]) * self.preview_h)

    def _ray_to_preview_edge(self, ox, oy, tx, ty):
        """Extend a direction handle from the eye to the visible frame border."""
        dx, dy = tx - ox, ty - oy
        if abs(dx) < 1e-6 and abs(dy) < 1e-6:
            return tx, ty
        left = float(self.preview_x + 1)
        top = float(self.preview_y + 1)
        right = float(self.preview_x + self.preview_w - 2)
        bottom = float(self.preview_y + self.preview_h - 2)
        candidates = []
        if dx > 1e-6:
            candidates.append((right - ox) / dx)
        elif dx < -1e-6:
            candidates.append((left - ox) / dx)
        if dy > 1e-6:
            candidates.append((bottom - oy) / dy)
        elif dy < -1e-6:
            candidates.append((top - oy) / dy)
        candidates = [t for t in candidates if t >= 1.0 - 1e-6]
        if not candidates:
            return tx, ty
        scale = min(candidates)
        return (min(right, max(left, ox + dx * scale)),
                min(bottom, max(top, oy + dy * scale)))

    def _draw_point_label(self, x, y, label, color):
        # Keep label boxes inside the actual video viewport so edge points stay legible.
        box_w = max(48, 7 * len(label) + 14)
        box_h = 22
        left = x + 9
        if left + box_w > self.preview_x + self.preview_w - 2:
            left = x - box_w - 9
        left = min(max(left, self.preview_x + 2),
                   max(self.preview_x + 2, self.preview_x + self.preview_w - box_w - 2))
        top = y - box_h - 7
        if top < self.preview_y + 2:
            top = y + 7
        top = min(max(top, self.preview_y + 2),
                  max(self.preview_y + 2, self.preview_y + self.preview_h - box_h - 2))
        self.canvas.create_rectangle(left, top, left + box_w, top + box_h,
                                     fill="#101010", outline=color, width=1)
        self.canvas.create_text(left + 6, top + box_h / 2, text=label,
                                fill=color, anchor="w", font=("Arial", 10, "bold"))

    def draw_preview(self):
        if self.frame is None or Image is None or ImageTk is None:
            return
        # Use the real canvas size, not the initial requested size. This keeps the
        # entire frame and its overlays visible after resizing / display scaling.
        canvas_w = int(self.canvas.winfo_width())
        canvas_h = int(self.canvas.winfo_height())
        if canvas_w < 100:
            canvas_w = self.PREVIEW_W
        if canvas_h < 100:
            canvas_h = self.PREVIEW_H
        available_w = max(80, canvas_w - 16)
        available_h = max(80, canvas_h - 16)
        scale = min(available_w / max(1, self.frame_w),
                    available_h / max(1, self.frame_h))
        self.preview_w = max(1, int(self.frame_w * scale))
        self.preview_h = max(1, int(self.frame_h * scale))
        self.preview_x = (canvas_w - self.preview_w) // 2
        self.preview_y = (canvas_h - self.preview_h) // 2
        cache_key = (id(self.frame), self.preview_w, self.preview_h)
        if cache_key != self._preview_cache_key or self._preview_base_image is None:
            image = Image.fromarray(cv2.cvtColor(self.frame, cv2.COLOR_BGR2RGB))
            resampling = getattr(getattr(Image, "Resampling", Image), "LANCZOS", 1)
            self._preview_base_image = image.resize((self.preview_w, self.preview_h), resampling)
            self._preview_cache_key = cache_key
        self.photo = ImageTk.PhotoImage(self._preview_base_image)
        self.canvas.delete("all")
        self.canvas.create_image(self.preview_x, self.preview_y, anchor="nw", image=self.photo)

        eye_colors = ("#ff5555", "#32d6ff")
        eye_labels = ("ГЛАЗ 1", "ГЛАЗ 2")
        direction_colors = ("#ff9c38", "#ffe15a")
        origins_px = [self._point_to_canvas(p) for p in self.selected_points[:2]]
        directions_px = [self._point_to_canvas(p) for p in self.selected_directions[:2]]
        marker_r = max(5, min(9, int(min(self.preview_w, self.preview_h) * 0.014)))

        # Draw projected laser guides first; the eye and direction handles stay on top.
        for idx, (ox, oy) in enumerate(origins_px):
            if idx < len(directions_px):
                tx, ty = directions_px[idx]
                ex, ey = self._ray_to_preview_edge(ox, oy, tx, ty)
                self.canvas.create_line(ox, oy, ex, ey, fill=eye_colors[idx],
                                        width=max(2, marker_r // 3), dash=(6, 3),
                                        arrow="last", arrowshape=(10, 12, 5))
                self.canvas.create_line(ox, oy, tx, ty, fill=direction_colors[idx],
                                        width=2, dash=(3, 3))

        for idx, (px, py) in enumerate(origins_px):
            color = eye_colors[idx]
            r = marker_r
            self.canvas.create_oval(px-r, py-r, px+r, py+r,
                                    fill="#151515", outline=color, width=3)
            self.canvas.create_line(px-r-4, py, px+r+4, py, fill=color, width=2)
            self.canvas.create_line(px, py-r-4, px, py+r+4, fill=color, width=2)
            self._draw_point_label(px, py, eye_labels[idx], color)

        for idx, (tx, ty) in enumerate(directions_px):
            color = direction_colors[idx]
            r = marker_r
            self.canvas.create_oval(tx-r, ty-r, tx+r, ty+r,
                                    fill="#151515", outline=color, width=3)
            self.canvas.create_line(tx-r-3, ty, tx+r+3, ty, fill=color, width=2)
            self.canvas.create_line(tx, ty-r-3, tx, ty+r+3, fill=color, width=2)
            self._draw_point_label(tx, ty, f"НАПР. {idx+1}", color)

    def _event_to_normalized_point(self, event):
        x = event.x - self.preview_x
        y = event.y - self.preview_y
        if x < 0 or y < 0 or x >= self.preview_w or y >= self.preview_h:
            return None
        return [min(1.0, max(0.0, x / self.preview_w)),
                min(1.0, max(0.0, y / self.preview_h))]

    def on_canvas_click(self, event):
        if self.frame is None:
            return
        point = self._event_to_normalized_point(event)
        if point is None:
            self._drag_handle = None
            return
        # Clicking close to an existing marker selects it for drag/edit rather than
        # accidentally restarting the four-point annotation.
        px, py = self._point_to_canvas(point)
        handles = []
        for idx, p in enumerate(self.selected_points[:2]):
            hx, hy = self._point_to_canvas(p)
            handles.append((math.hypot(px - hx, py - hy), "eye", idx))
        for idx, p in enumerate(self.selected_directions[:2]):
            hx, hy = self._point_to_canvas(p)
            handles.append((math.hypot(px - hx, py - hy), "direction", idx))
        if handles:
            distance, kind, idx = min(handles)
            if distance <= max(18, int(min(self.preview_w, self.preview_h) * 0.035)):
                self._drag_handle = (kind, idx)
                name = f"глаз {idx + 1}" if kind == "eye" else f"направление {idx + 1}"
                self.status_var.set(f"Выбрано: {name}. Перетащи точку мышью, затем нажми «Сохранить метку».")
                return
        self._drag_handle = None
        if len(self.selected_points) < 2:
            self.selected_points.append(point)
            step = "Теперь отметь второй глаз." if len(self.selected_points) == 1 else "Теперь отметь направление луча из первого глаза."
        elif len(self.selected_directions) < 2:
            self.selected_directions.append(point)
            if len(self.selected_directions) == 1:
                step = "Теперь отметь направление луча из второго глаза."
            else:
                step = "Готово: 2 глаза и 2 направления. Проверь линии и нажми «Сохранить метку»."
        else:
            # A click away from existing handles starts a fresh annotation for this time.
            self.selected_points = [point]
            self.selected_directions = []
            step = "Начато заново: теперь отметь второй глаз."
        self.draw_preview()
        self.status_var.set(f"Время: {self.current_time:.3f} с. {step}")

    def on_canvas_drag(self, event):
        if self.frame is None or self._drag_handle is None:
            return
        point = self._event_to_normalized_point(event)
        if point is None:
            return
        kind, idx = self._drag_handle
        if kind == "eye" and idx < len(self.selected_points):
            self.selected_points[idx] = point
        elif kind == "direction" and idx < len(self.selected_directions):
            self.selected_directions[idx] = point
        else:
            return
        self.draw_preview()
        name = f"глаз {idx + 1}" if kind == "eye" else f"направление {idx + 1}"
        self.status_var.set(f"Перемещается: {name}. Нажми «Сохранить метку», чтобы записать изменения.")

    def on_canvas_release(self, _event=None):
        if self._drag_handle is not None:
            self._drag_handle = None
            self.status_var.set(f"Точка изменена на {self.current_time:.3f} с. Нажми «Сохранить метку», чтобы сохранить изменения.")

    def reset_selected_points(self):
        self.selected_points = []
        self.selected_directions = []
        self.draw_preview()
        self.status_var.set("Разметка очищена для текущего кадра. Отметь два глаза, затем два направления.")

    def save_current_keyframe(self):
        if len(self.selected_points) != 2:
            messagebox.showwarning("Нужны две точки", "Сначала отметь два глаза (начала лучей).", parent=self)
            return
        points = [[float(p[0]), float(p[1])] for p in self.selected_points]
        directions = [[float(p[0]), float(p[1])] for p in self.selected_directions]
        if len(directions) != 2:
            messagebox.showwarning(
                "Нужны направления",
                "Отметь ещё две точки: куда должен быть направлен каждый луч. Старые метки можно загрузить и дополнить.",
                parent=self)
            return
        paired = sorted(zip(points, directions), key=lambda pair: pair[0][0])
        row = {"time": round(self.current_time, 3),
               "points": [pair[0] for pair in paired],
               "directions": [pair[1] for pair in paired]}
        tolerance = max(0.045, 0.5 / self.video_fps)
        matched = next((i for i, old in enumerate(self.annotations)
                        if abs(old["time"] - self.current_time) <= tolerance), None)
        previous = _copy_laser_rows(self.annotations)
        if matched is None:
            self.annotations.append(row)
        else:
            self.annotations[matched] = row
        self.annotations.sort(key=lambda item: item["time"])
        if not self.write_annotations():
            self.annotations = previous
            return
        self.refresh_key_list()
        self.status_var.set(
            f"Сохранено на {self.current_time:.3f} с: 2 начала + 2 направления. Ключевых кадров: {len(self.annotations)}. "
            + manual_laser_span_text(self.annotations))

    def refresh_key_list(self):
        self.key_list.delete(0, "end")
        for row in sorted(self.annotations, key=lambda item: item["time"]):
            kind = "направления есть" if len(row.get("directions", [])) == 2 else "старый формат"
            self.key_list.insert("end", f'{row["time"]:.3f} с — {kind}')

    def on_key_selected(self, _event=None):
        selection = self.key_list.curselection()
        if not selection:
            return
        rows = sorted(self.annotations, key=lambda item: item["time"])
        idx = selection[0]
        if 0 <= idx < len(rows):
            self.show_time(rows[idx]["time"])

    def delete_current_keyframe(self):
        tolerance = max(0.045, 0.5 / self.video_fps)
        candidates = [(abs(row["time"] - self.current_time), idx)
                      for idx, row in enumerate(self.annotations)]
        candidates = [pair for pair in candidates if pair[0] <= tolerance]
        if not candidates:
            self.status_var.set("На текущем времени нет сохранённой метки. Выбери её в списке справа.")
            return
        _, idx = min(candidates)
        self.annotations.pop(idx)
        self.write_annotations()
        self.refresh_key_list()
        self.selected_points = []
        self.selected_directions = []
        self.draw_preview()
        self.status_var.set(f"Метка на {self.current_time:.3f} с удалена.")

    def delete_all_keyframes(self):
        if not self.annotations:
            return
        if not messagebox.askyesno("Удалить всё?", "Удалить все ручные метки для этого видео?", parent=self):
            return
        self.annotations = []
        self.write_annotations()
        self.refresh_key_list()
        self.selected_points = []
        self.selected_directions = []
        self.draw_preview()
        self.status_var.set("Все ручные метки удалены.")

    def write_annotations(self) -> bool:
        try:
            os.makedirs(MANUAL_LASER_DIR, exist_ok=True)
            destination = manual_laser_annotation_path(self.video_path)
            temporary = destination + ".tmp"
            try:
                file_size = os.path.getsize(self.video_path)
            except OSError:
                file_size = 0
            with open(temporary, "w", encoding="utf-8") as f:
                # Старые файлы (version 1) читаются как раньше; новые поля только добавлены.
                json.dump({"version": 1, "video_path": self.video_path,
                           "basename": os.path.basename(self.video_path), "file_size": file_size,
                           "frame_width": self.frame_w, "frame_height": self.frame_h,
                           "annotations": self.annotations}, f, ensure_ascii=False, indent=2)
            os.replace(temporary, destination)
            _MANUAL_LASER_CACHE.pop(os.path.normcase(os.path.abspath(self.video_path)), None)
            _MANUAL_LASER_LAST_ERROR.pop(os.path.normcase(os.path.abspath(self.video_path)), None)
            return True
        except OSError as exc:
            messagebox.showerror("Не удалось сохранить", str(exc), parent=self)
            return False

    def close_window(self):
        try:
            if self.cap is not None:
                self.cap.release()
        finally:
            self.destroy()


class App(ctk.CTk):
    RESOLUTIONS = {
        "1080×1920 (Shorts / вертикаль)": (1080, 1920),
        "1920×1080 (Full HD)": (1920, 1080),
        "1280×720 (HD)": (1280, 720),
        "2560×1440 (2K)": (2560, 1440),
    }
    ORDERS = ["Блоки: игра → видео → по времени",
              "Чередовать игры (видео целиком подряд)",
              "По силе момента (лучшее вперёд)"]
    FRAMES = ["Умный кроп (по активности)", "Центр-кроп", "Размытый фон", "Чёрные поля"]
    TRANSITIONS = ["Авто (умный выбор)", "Динамичные", "Плавные (fade)", "Только склейки"]
    VIS_LEVELS = {"Мягко": 0.20, "Средне": 0.30, "Жёстко": 0.50}

    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")
        self.title("Game AutoMix v7 — ускоренный монтаж и ручные лазеры")
        self.geometry("920x1020")
        self.minsize(860, 940)
        self.q = queue.Queue()
        self.stop_flag = False
        self.worker = None
        self.busy = False
        self.manual_files = []
        self.plan_state = None
        self.history = History()
        self.loaded_settings = load_settings_from_disk()
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        self._build()
        self._apply_settings_to_ui()
        self.protocol("WM_DELETE_WINDOW", self.on_close_app)
        self.after(100, self._poll)

    def _entry(self, parent, row, col, label, default, width=60):
        ctk.CTkLabel(parent, text=label).grid(row=row, column=col, padx=(12, 4), pady=6, sticky="w")
        var = ctk.StringVar(value=str(default))
        ctk.CTkEntry(parent, textvariable=var, width=width, justify="center"
                     ).grid(row=row, column=col + 1, padx=(0, 12), sticky="w")
        return var

    def _check(self, parent, row, col, text, on=True, span=1):
        c = ctk.CTkCheckBox(parent, text=text)
        if on:
            c.select()
        c.grid(row=row, column=col, columnspan=span, padx=12, pady=6, sticky="w")
        return c

    def _build(self):
        self.tabs = ctk.CTkTabview(self)
        self.tabs.grid(row=0, column=0, sticky="nsew", padx=14, pady=(14, 6))
        for name in ("Источники", "Режим и музыка", "События и моменты", "Монтаж", "Формат и скорость", "План"):
            self.tabs.add(name)

        # --- Источники ---
        t = self.tabs.tab("Источники")
        t.columnconfigure(1, weight=1)
        ctk.CTkButton(t, text="Папка с играми…", width=170, command=self.pick_root
                      ).grid(row=0, column=0, padx=10, pady=10)
        self.root_var = ctk.StringVar()
        ctk.CTkEntry(t, textvariable=self.root_var,
                     placeholder_text="Корень: подпапки STALCRAFT, Deadlock…"
                     ).grid(row=0, column=1, padx=(0, 10), sticky="ew")
        ctk.CTkButton(t, text="Папка сохранения…", width=170, command=self.pick_out
                      ).grid(row=1, column=0, padx=10, pady=4)
        self.out_var = ctk.StringVar()
        ctk.CTkEntry(t, textvariable=self.out_var,
                     placeholder_text="Куда сохранить готовый ролик"
                     ).grid(row=1, column=1, padx=(0, 10), sticky="ew")
        box = ctk.CTkFrame(t)
        box.grid(row=2, column=0, columnspan=2, sticky="ew", padx=10, pady=(14, 6))
        ctk.CTkLabel(box, text="Какие видео монтировать", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, columnspan=3, padx=12, pady=(8, 2), sticky="w")
        self.src_lbl = ctk.CTkLabel(box, text="Все видео из выбранной папки", anchor="w")
        self.src_lbl.grid(row=1, column=0, columnspan=3, padx=12, sticky="w")
        ctk.CTkButton(box, text="Выбрать из списка…", width=170, command=self.open_picker
                      ).grid(row=2, column=0, padx=12, pady=10)
        ctk.CTkButton(box, text="Добавить файлы…", width=150, command=self.add_files
                      ).grid(row=2, column=1, padx=4)
        ctk.CTkButton(box, text="Сбросить (все видео)", width=160, fg_color="#555",
                      command=self.reset_sources).grid(row=2, column=2, padx=12)
        tb = ctk.CTkFrame(t)
        tb.grid(row=3, column=0, columnspan=2, sticky="ew", padx=10, pady=6)
        self.trim_chk = self._check(tb, 0, 0, "Обрезать первые N секунд каждого видео")
        self.trim_var = ctk.StringVar(value="4")
        ctk.CTkEntry(tb, textvariable=self.trim_var, width=60, justify="center").grid(row=0, column=1)
        ctk.CTkLabel(tb, text="сек").grid(row=0, column=2, padx=6)
        self.audio_chk = self._check(t, 4, 0, "Нормализация звука и удаление тишины/пауз", span=2)

        # --- Режим и музыка ---
        # В этой вкладке много настроек. Размещаем их внутри прокручиваемой области,
        # иначе блоки внизу (YouTube, расширенный поиск, Shorts и др.) недоступны
        # на экранах небольшой высоты.
        mode_music_tab = self.tabs.tab("Режим и музыка")
        mode_music_tab.grid_columnconfigure(0, weight=1)
        mode_music_tab.grid_rowconfigure(1, weight=1)
        ctk.CTkLabel(
            mode_music_tab,
            text="Все настройки доступны ниже: прокручивайте колесом мыши или полосой справа.",
            anchor="w",
        ).grid(row=0, column=0, padx=12, pady=(6, 0), sticky="ew")
        t = ctk.CTkScrollableFrame(mode_music_tab, fg_color="transparent")
        t.grid(row=1, column=0, sticky="nsew", padx=2, pady=(0, 2))
        mode_box = ctk.CTkFrame(t)
        mode_box.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(mode_box, text="Режим обработки", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, padx=12, pady=(10, 4), sticky="w")
        self.mode_menu = ctk.CTkOptionMenu(
            mode_box, values=["Игры", "Фильмы — только диалоги"], width=300)
        self.mode_menu.set("Игры")
        self.mode_menu.grid(row=0, column=1, padx=8, pady=(10, 4), sticky="w")
        ctk.CTkLabel(mode_box, text="«Игры» сохраняет нынешнюю логику. «Фильмы» выделяет речь через бесплатный Whisper.",
                     wraplength=720, justify="left").grid(row=1, column=0, columnspan=2,
                                                          padx=12, pady=(2, 10), sticky="w")

        music_box = ctk.CTkFrame(t)
        music_box.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(music_box, text="Фоновая музыка", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, columnspan=3, padx=12, pady=(10, 4), sticky="w")
        self.music_path_var = ctk.StringVar(value="")
        ctk.CTkEntry(music_box, textvariable=self.music_path_var,
                     placeholder_text="MP3/WAV/M4A/MP4/MKV — если MP4, берётся только звук"
                     ).grid(row=1, column=0, columnspan=2, padx=(12, 6), pady=5, sticky="ew")
        ctk.CTkButton(music_box, text="Выбрать файл…", width=135, command=self.pick_music
                      ).grid(row=1, column=2, padx=(0, 12), pady=5)
        music_box.columnconfigure(0, weight=1)
        self.music_vol_var = self._entry(music_box, 2, 0, "Громкость музыки, %:", 45, 70)
        self.original_vol_var = self._entry(music_box, 2, 2, "Громкость оригинала, %:", 65, 70)
        self.keep_original_chk = self._check(music_box, 3, 0, "Сохранить звук игры/фильма", on=True, span=3)
        ctk.CTkLabel(music_box,
                     text="Эти настройки применяются ко всем итоговым видео и к каждому Shorts-файлу.",
                     wraplength=740, justify="left").grid(row=4, column=0, columnspan=3,
                                                          padx=12, pady=(0, 10), sticky="w")

        matador_music_box = ctk.CTkFrame(t)
        matador_music_box.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(matador_music_box, text="Музыка режима «Матадоры»",
                     font=ctk.CTkFont(weight="bold")).grid(
                         row=0, column=0, columnspan=3, padx=12, pady=(10, 4), sticky="w")
        self.matador_music_chk = self._check(
            matador_music_box, 1, 0,
            "Добавлять музыку Матадоров (включается отдельно от лазеров)", on=False, span=3)
        self.laser_chk = self._check(
            matador_music_box, 2, 0,
            "🔴 Показывать лазеры из глаз (эффект «Матадоры», нужен OpenCV)",
            on=False, span=3)
        self.matador_music_path_var = ctk.StringVar(value="")
        ctk.CTkEntry(matador_music_box, textvariable=self.matador_music_path_var,
                     placeholder_text="Выберите аудиофайл с музыкой Матадоров").grid(
                         row=3, column=0, columnspan=2, padx=(12, 6), pady=5, sticky="ew")
        ctk.CTkButton(matador_music_box, text="Выбрать файл…", width=135,
                      command=self.pick_matador_music).grid(
                          row=3, column=2, padx=(0, 12), pady=5)
        matador_music_box.columnconfigure(0, weight=1)
        self.matador_music_vol_var = self._entry(
            matador_music_box, 4, 0, "Громкость музыки Матадоров, %:", 45, 70)
        ctk.CTkLabel(matador_music_box,
                     text="При включённом отдельном треке он заменяет обычную фоновую музыку. "
                          "При выборе файла в версии .py программа сама копирует его в assets\\matadores.* "
                          "для следующих сборок EXE. При запуске из готового EXE выбранный трек хранится "
                          "в папке пользователя. Если поле пустое, используется встроенный/сохранённый трек. "
                          "Музыка по YouTube-ссылке автоматически не скачивается; используйте файл, "
                          "который вы вправе включать в свою программу и видео.",
                     wraplength=740, justify="left").grid(
                         row=5, column=0, columnspan=3, padx=12, pady=(0, 4), sticky="w")
        ctk.CTkButton(matador_music_box, text="Открыть видео-источник на YouTube",
                      width=245, command=self.open_matador_music_source).grid(
                          row=6, column=0, padx=12, pady=(2, 10), sticky="w")

        yt_box = ctk.CTkFrame(t)
        yt_box.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(yt_box, text="Бесплатная музыка YouTube", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, columnspan=2, padx=12, pady=(10, 4), sticky="w")
        self.yt_filter_menu = ctk.CTkOptionMenu(
            yt_box, values=["Атрибуция не требуется", "Атрибуция требуется"], width=250)
        self.yt_filter_menu.set("Атрибуция не требуется")
        self.yt_filter_menu.grid(row=1, column=0, padx=12, pady=5, sticky="w")
        ctk.CTkButton(yt_box, text="Открыть YouTube Audio Library",
                      command=self.open_youtube_audio_library, width=230
                      ).grid(row=1, column=1, padx=8, pady=5, sticky="w")
        ctk.CTkLabel(yt_box,
                     text="На сайте выберите соответствующий фильтр и скачайте трек вручную, затем укажите его выше. Это фильтр авторской атрибуции, а не универсальная проверка прав на любой ролик YouTube.",
                     wraplength=740, justify="left").grid(row=2, column=0, columnspan=2,
                                                          padx=12, pady=(2, 10), sticky="w")
        self.laser_universal_chk = self._check(
            yt_box, 4, 0,
            "🔎 Расширенный поиск глаз и лиц (для игровых и стилизованных персонажей)",
            on=True, span=2)
        ctk.CTkLabel(yt_box,
                     text="Расширенный поиск проверяет несколько типов лиц и ищет пары глаз по всему кадру. На игровых моделях без различимых глаз результат всё равно не гарантирован.",
                     wraplength=740, justify="left").grid(row=5, column=0, columnspan=2, padx=12, pady=(2, 6), sticky="w")
        self.shorts_chk = self._check(yt_box, 7, 0,
                                      "📱 Режим Shorts: сохранить каждый найденный фрагмент отдельным вертикальным MP4",
                                      on=False, span=2)
        ctk.CTkLabel(yt_box, text="Shorts не склеивает все моменты в один ролик: каждый выбранный фрагмент экспортируется отдельным файлом.",
                     wraplength=740, justify="left").grid(row=8, column=0, columnspan=2, padx=12, pady=(2, 10), sticky="w")

        # --- События и моменты ---
        t = self.tabs.tab("События и моменты")
        ev = ctk.CTkFrame(t)
        ev.pack(fill="x", padx=10, pady=6)
        ctk.CTkLabel(ev, text="Искать события", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, columnspan=2, padx=12, pady=(8, 2), sticky="w")
        self.ev_chk = {}
        for idx, (k, txt) in enumerate([("loud", "🔊 Громкие моменты"),
                                         ("burst", "💥 Резкие звуки (выстрелы, взрывы)"),
                                         ("motion", "🏃 Движение / экшен"),
                                         ("scene", "🎬 Резкая смена сцены")]):
            self.ev_chk[k] = self._check(ev, 1 + idx // 2, idx % 2, txt)
        self.speech_chk = self._check(ev, 3, 0, "🗣 Подавлять просто разговоры/голос", span=2)
        ctk.CTkLabel(ev, text="Отбрасывать", font=ctk.CTkFont(weight="bold")
                     ).grid(row=4, column=0, columnspan=2, padx=12, pady=(8, 2), sticky="w")
        self.black_chk = self._check(ev, 5, 0, "⬛ Чёрные кадры / загрузки")
        self.frozen_chk = self._check(ev, 5, 1, "🧊 Статику (меню, пауза, AFK)")
        vis = ctk.CTkFrame(t)
        vis.pack(fill="x", padx=10, pady=6)
        self.vis_chk = self._check(vis, 0, 0, "👁 Требовать реакцию на экране (отсев «выстрелов в никуда»)", span=3)
        ctk.CTkLabel(vis, text="Строгость:").grid(row=1, column=0, padx=12, pady=(0, 8), sticky="w")
        self.vis_menu = ctk.CTkOptionMenu(vis, values=list(self.VIS_LEVELS), width=120)
        self.vis_menu.set("Средне")
        self.vis_menu.grid(row=1, column=1, sticky="w", pady=(0, 8))
        self.snap_chk = self._check(vis, 2, 0, "✂ Резать по паузам речи (не обрывать слова на полуслове)", span=3)
        mm = ctk.CTkFrame(t)
        mm.pack(fill="x", padx=10, pady=6)
        ctk.CTkLabel(mm, text="Границы момента", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, columnspan=4, padx=12, pady=(8, 2), sticky="w")
        self.pre_var = self._entry(mm, 1, 0, "Секунд ДО события:", 5)
        self.post_var = self._entry(mm, 1, 2, "Секунд ПОСЛЕ события:", 5)
        self.minl_var = self._entry(mm, 2, 0, "Мин. длина момента, с:", 8)
        self.maxl_var = self._entry(mm, 2, 2, "Макс. длина момента, с:", 40)

        # --- Монтаж ---
        t = self.tabs.tab("Монтаж")
        d = ctk.CTkFrame(t)
        d.pack(fill="x", padx=10, pady=6)
        d.columnconfigure(1, weight=1)
        ctk.CTkLabel(d, text="Длительность итога:").grid(row=0, column=0, padx=12, pady=10)
        self.target_slider = ctk.CTkSlider(d, from_=10, to=900, number_of_steps=89, command=self._on_target)
        self.target_slider.set(60)
        self.target_slider.grid(row=0, column=1, sticky="ew")
        self.target_lbl = ctk.CTkLabel(d, text="60 с", width=90)
        self.target_lbl.grid(row=0, column=2, padx=10)
        self.strict_chk = self._check(d, 1, 0, "Строго не длиннее цели (для Shorts)", span=3)
        o = ctk.CTkFrame(t)
        o.pack(fill="x", padx=10, pady=6)
        ctk.CTkLabel(o, text="Порядок:").grid(row=0, column=0, padx=12, pady=8, sticky="w")
        self.order_menu = ctk.CTkOptionMenu(o, values=self.ORDERS, width=330)
        self.order_menu.grid(row=0, column=1, columnspan=2, sticky="w")
        self.pfm_var = self._entry(o, 1, 0, "Макс. моментов из одного видео:", 2, 50)
        self.bal_chk = self._check(o, 2, 0, "Баланс между играми (поровну по времени)", span=3)
        ctk.CTkLabel(o, text="Вариативность выбора:").grid(row=3, column=0, padx=12, pady=8, sticky="w")
        self.var_slider = ctk.CTkSlider(o, from_=0, to=100, number_of_steps=20, width=220)
        self.var_slider.set(30)
        self.var_slider.grid(row=3, column=1, sticky="w")
        fx = ctk.CTkFrame(t)
        fx.pack(fill="x", padx=10, pady=6)
        ctk.CTkLabel(fx, text="Переходы, эффекты, текст", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, columnspan=3, padx=12, pady=(8, 2), sticky="w")
        ctk.CTkLabel(fx, text="Переходы:").grid(row=1, column=0, padx=12, pady=6, sticky="w")
        self.trans_menu = ctk.CTkOptionMenu(fx, values=self.TRANSITIONS, width=200)
        self.trans_menu.grid(row=1, column=1, sticky="w")
        self.fx_chk = self._check(fx, 2, 0, "✨ Эффекты (пунш-ин на самые ударные моменты)", span=3)
        self.titles_chk = self._check(fx, 3, 0, "🏷 Плашка с названием игры в начале блока", span=3)
        self.cap_chk = self._check(fx, 4, 0, "💬 Субтитры речи (нужен faster-whisper)", on=HAVE_WHISPER, span=2)
        self.lang_menu = ctk.CTkOptionMenu(fx, values=["auto", "ru", "en", "uk"], width=80)
        self.lang_menu.grid(row=4, column=2, padx=6)
        if not HAVE_WHISPER:
            self.cap_chk.configure(state="disabled")
        h = ctk.CTkFrame(t)
        h.pack(fill="x", padx=10, pady=6)
        self.norep_chk = self._check(h, 0, 0, "Не повторять уже использованные моменты", span=2)
        self.hist_lbl = ctk.CTkLabel(h, text="")
        self.hist_lbl.grid(row=1, column=0, padx=12, pady=(0, 8), sticky="w")
        ctk.CTkButton(h, text="Сбросить историю", width=150, fg_color="#8a2f2f", hover_color="#a33",
                      command=self.reset_history).grid(row=1, column=1, padx=12, pady=(0, 8))
        self._update_hist()

        # --- Формат и скорость ---
        t = self.tabs.tab("Формат и скорость")
        f = ctk.CTkFrame(t)
        f.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(f, text="Разрешение:").grid(row=0, column=0, padx=12, pady=8, sticky="w")
        self.res_menu = ctk.CTkOptionMenu(f, values=list(self.RESOLUTIONS), width=250)
        self.res_menu.grid(row=0, column=1, sticky="w")
        ctk.CTkLabel(f, text="FPS:").grid(row=0, column=2, padx=(16, 4))
        self.fps_menu = ctk.CTkOptionMenu(f, values=["30", "60", "24"], width=70)
        self.fps_menu.grid(row=0, column=3)
        ctk.CTkLabel(f, text="Кадрирование:").grid(row=1, column=0, padx=12, pady=8, sticky="w")
        self.frame_menu = ctk.CTkOptionMenu(f, values=self.FRAMES, width=250)
        self.frame_menu.grid(row=1, column=1, sticky="w")
        ctk.CTkLabel(f, text="Качество:").grid(row=1, column=2, padx=(16, 4))
        self.qual_menu = ctk.CTkOptionMenu(f, values=["Высокое", "Обычное", "Быстрое"], width=110)
        self.qual_menu.grid(row=1, column=3)
        p = ctk.CTkFrame(t)
        p.pack(fill="x", padx=10, pady=8)
        self.thr_var = self._entry(p, 0, 0, "Потоков (параллельно):", 1, 50)
        ctk.CTkLabel(p, text="Глубина поиска:").grid(row=1, column=0, padx=12, pady=8, sticky="w")
        self.depth_menu = ctk.CTkOptionMenu(p, values=["Быстро", "Сбалансировано", "Тщательно"], width=170)
        self.depth_menu.set("Сбалансировано")
        self.depth_menu.grid(row=1, column=1, sticky="w")
        self.hw_chk = self._check(p, 2, 0, "Кодировать на видеокарте, если возможно (NVENC/QSV/AMF)", span=3)
        self.limit_resources_chk = self._check(
            p, 3, 0, "Экономный режим: один рабочий поток и пониженный приоритет FFmpeg", on=True, span=3)

        # --- План ---
        t = self.tabs.tab("План")
        top = ctk.CTkFrame(t, fg_color="transparent")
        top.pack(fill="x", padx=6, pady=(4, 2))
        self.plan_info = ctk.CTkLabel(top, text="План пуст.", anchor="w")
        self.plan_info.pack(side="left", padx=6)
        ctk.CTkButton(top, text="+ Добавить момент вручную…", width=210, command=self.add_manual
                      ).pack(side="right")
        self.plan_frame = ctk.CTkScrollableFrame(t)
        self.plan_frame.pack(fill="both", expand=True, padx=4, pady=4)

        # --- Нижняя панель ---
        b = ctk.CTkFrame(self, fg_color="transparent")
        b.grid(row=1, column=0, sticky="ew", padx=14)
        b.columnconfigure(0, weight=1)
        b.columnconfigure(1, weight=1)
        self.start_btn = ctk.CTkButton(b, text="🔎  Подобрать моменты", height=42,
                                       font=ctk.CTkFont(size=15, weight="bold"), command=self.start)
        self.start_btn.grid(row=0, column=0, sticky="ew", padx=(0, 6))
        self.build_btn = ctk.CTkButton(b, text="🎬  Собрать ролик", height=42, state="disabled",
                                       fg_color="#2b8a3e", hover_color="#37a34d",
                                       font=ctk.CTkFont(size=15, weight="bold"), command=self.build)
        self.build_btn.grid(row=0, column=1, sticky="ew", padx=(0, 6))
        self.stop_btn = ctk.CTkButton(b, text="■ Стоп", width=90, height=42, fg_color="#8a2f2f",
                                      hover_color="#a33", state="disabled", command=self.stop)
        self.stop_btn.grid(row=0, column=2)
        self.auto_chk = ctk.CTkCheckBox(b, text="Собрать сразу, без проверки плана")
        self.auto_chk.grid(row=1, column=0, columnspan=3, sticky="w", pady=(6, 0))
        self.bars = []
        for i, name in enumerate(("Поиск и анализ", "Нарезка", "Склейка и звук")):
            ctk.CTkLabel(b, text=name, width=120, anchor="w").grid(row=2 + i, column=0, sticky="w", pady=(6, 0))
            pb = ctk.CTkProgressBar(b)
            pb.set(0)
            pb.grid(row=2 + i, column=0, columnspan=3, sticky="ew", padx=(130, 0), pady=(6, 0))
            self.bars.append(pb)
        self.status = ctk.CTkLabel(self, text="Готов к работе.", anchor="w", wraplength=860, justify="left")
        self.status.grid(row=2, column=0, sticky="ew", padx=16, pady=(6, 0))
        self.log_box = ctk.CTkTextbox(self, height=120)
        self.log_box.grid(row=3, column=0, sticky="ew", padx=14, pady=(4, 14))
        self.log_box.configure(state="disabled")
        self._render_plan()

    def _apply_settings_to_ui(self):
        s = self.loaded_settings
        if s.root_dir:
            self.root_var.set(s.root_dir)
        if s.out_dir:
            self.out_var.set(s.out_dir)
        self.trim_chk.select() if s.trim_on else self.trim_chk.deselect()
        self.trim_var.set(str(s.trim_sec))
        self.audio_chk.select() if s.clean_audio else self.audio_chk.deselect()
        self.speech_chk.select() if s.suppress_speech else self.speech_chk.deselect()
        for k, c in self.ev_chk.items():
            if s.events.get(k, True):
                c.select()
            else:
                c.deselect()
        self.black_chk.select() if s.skip_black else self.black_chk.deselect()
        self.frozen_chk.select() if s.skip_frozen else self.frozen_chk.deselect()
        self.vis_chk.select() if s.require_visual else self.vis_chk.deselect()
        for k, val in self.VIS_LEVELS.items():
            if abs(val - s.visual_level) < 0.01:
                self.vis_menu.set(k)
                break
        self.snap_chk.select() if s.snap_pauses else self.snap_chk.deselect()
        self.pre_var.set(str(s.pre))
        self.post_var.set(str(s.post))
        self.minl_var.set(str(s.min_len))
        self.maxl_var.set(str(s.max_len))
        self.target_slider.set(s.target)
        self._on_target(s.target)
        self.strict_chk.select() if s.strict else self.strict_chk.deselect()
        if s.order in self.ORDERS:
            self.order_menu.set(s.order)
        self.pfm_var.set(str(s.per_file_max))
        self.bal_chk.select() if s.balance else self.bal_chk.deselect()
        self.var_slider.set(s.variety * 100)
        self.norep_chk.select() if s.no_repeat else self.norep_chk.deselect()
        if s.transitions in self.TRANSITIONS:
            self.trans_menu.set(s.transitions)
        self.fx_chk.select() if s.effects else self.fx_chk.deselect()
        self.titles_chk.select() if s.titles else self.titles_chk.deselect()
        if HAVE_WHISPER:
            self.cap_chk.select() if s.captions else self.cap_chk.deselect()
        self.lang_menu.set(s.caption_lang)
        if s.mode in ("Игры", "Фильмы — только диалоги"):
            self.mode_menu.set(s.mode)
        elif s.mode == "Матадоры":
            self.mode_menu.set("Игры")
            s.laser_effect = True
            self.laser_chk.select()
        self.shorts_chk.select() if s.shorts_mode else self.shorts_chk.deselect()
        self.music_path_var.set(s.music_path)
        self.matador_music_chk.select() if s.matador_music_enabled else self.matador_music_chk.deselect()
        self.matador_music_path_var.set(s.matador_music_path)
        self.matador_music_vol_var.set(str(round(s.matador_music_volume * 100)))
        if s.youtube_attribution_filter in ("Атрибуция не требуется", "Атрибуция требуется"):
            self.yt_filter_menu.set(s.youtube_attribution_filter)
        self.music_vol_var.set(str(round(s.music_volume * 100)))
        self.original_vol_var.set(str(round(s.original_volume * 100)))
        self.keep_original_chk.select() if s.keep_original_audio else self.keep_original_chk.deselect()
        self.laser_chk.select() if s.laser_effect else self.laser_chk.deselect()
        self.laser_universal_chk.select() if s.laser_universal_search else self.laser_universal_chk.deselect()
        self.limit_resources_chk.select() if s.limit_resources else self.limit_resources_chk.deselect()
        for res_name, (w, h) in self.RESOLUTIONS.items():
            if w == s.width and h == s.height:
                self.res_menu.set(res_name)
                break
        self.fps_menu.set(str(s.fps))
        self.frame_menu.set(s.frame_mode)
        self.qual_menu.set(s.quality)
        self.thr_var.set(str(min(4, max(1, int(s.threads)))))
        self.depth_menu.set(s.depth)
        self.hw_chk.select() if s.hw else self.hw_chk.deselect()

    def on_close_app(self):
        current_s = self._read_settings()
        if current_s:
            save_settings_to_disk(current_s)
        self.destroy()

    def _lock_ui(self, on):
        self.busy = on
        self.start_btn.configure(state="disabled" if on else "normal")
        self.stop_btn.configure(state="normal" if on else "disabled")
        self.build_btn.configure(state="disabled" if on or not (self.plan_state and self.plan_state.plan) else "normal")

    def start(self):
        if self.busy:
            return
        s = self._read_settings()
        if s is None:
            return
        save_settings_to_disk(s)
        auto = bool(self.auto_chk.get())
        self.stop_flag = False
        self._lock_ui(True)
        for b in self.bars:
            b.set(0)
        self.worker = threading.Thread(target=self._work_plan, args=(s, auto), daemon=True)
        self.worker.start()

    def build(self):
        if self.busy or not (self.plan_state and self.plan_state.plan):
            return
        s = self._read_settings()
        if s is None:
            return
        save_settings_to_disk(s)
        self.plan_state.s = s
        self.stop_flag = False
        self._lock_ui(True)
        for b in self.bars[1:]:
            b.set(0)
        self.worker = threading.Thread(target=self._work_render, daemon=True)
        self.worker.start()

    def stop(self):
        self.stop_flag = True
        self.set_status("Останавливаю…")

    def _work_plan(self, s, auto):
        rep = QueueReporter(self.q)
        try:
            st = plan_moments(s, rep, lambda: self.stop_flag, self.history)
            self.q.put(("plan", st))
            if auto:
                out = render_plan(st, rep, lambda: self.stop_flag, self.history)
                problem = getattr(st, "laser_problem", "")
                self.q.put(("status", f"⚠ Готово, но {problem} {out}" if problem else f"✅ Готово: {out}"))
            else:
                self.q.put(("status", "План готов. Проверьте фрагменты на вкладке «План» и нажмите «Собрать ролик»."))
        except Cancelled:
            self.q.put(("status", "⛔ Остановлено пользователем."))
        except Exception as e:
            details = f"{type(e).__name__}: {e}\n\nПодробности для исправления:\n{traceback.format_exc()}"
            self.q.put(("status", f"❌ Ошибка обработки: {type(e).__name__}: {e}"))
            self.q.put(("error", "Обработка остановлена", details))
        finally:
            self.q.put(("finished",))

    def _work_render(self):
        rep = QueueReporter(self.q)
        try:
            out = render_plan(self.plan_state, rep, lambda: self.stop_flag, self.history)
            problem = getattr(self.plan_state, "laser_problem", "")
            self.q.put(("status", f"⚠ Готово, но {problem} {out}" if problem else f"✅ Готово: {out}"))
        except Cancelled:
            self.q.put(("status", "⛔ Остановлено пользователем."))
        except Exception as e:
            details = f"{type(e).__name__}: {e}\n\nПодробности для исправления:\n{traceback.format_exc()}"
            self.q.put(("status", f"❌ Экспорт остановлен: {type(e).__name__}: {e}"))
            self.q.put(("error", "Экспорт остановлен", details))
        finally:
            self.q.put(("finished",))

    def _bg(self, fn, done):
        def work():
            try:
                r = fn()
            except Exception as e:
                r = e
            self.q.put(("call", done, r))
        threading.Thread(target=work, daemon=True).start()

    def _index_of(self, ep):
        if not self.plan_state:
            return -1
        for i, e in enumerate(self.plan_state.plan):
            if e is ep:
                return i
        return -1

    def _ensure_state(self):
        if self.plan_state is None:
            s = self._read_settings() or Settings()
            self.plan_state = PlanState(s, find_ffmpeg(), [], [], {}, {})
        return self.plan_state

    def _render_plan(self):
        for w in self.plan_frame.winfo_children():
            w.destroy()
        st = self.plan_state
        if not st or not st.plan:
            ctk.CTkLabel(self.plan_frame, text="Здесь появятся найденные моменты.\nНажмите «Подобрать моменты».", text_color="#999"
                         ).pack(pady=40)
            self.plan_info.configure(text="План пуст.")
            self.build_btn.configure(state="disabled")
            return
        total = sum(e.dur for e in st.plan)
        tgt = st.s.target
        self.plan_info.configure(
            text=f"Фрагментов: {len(st.plan)}  ·  итого {total:.0f} с  (цель {tgt} с)",
            text_color="#e0902a" if (total > tgt * 1.1 or total < tgt * 0.8) else "#7fd18b")
        for i, ep in enumerate(st.plan):
            self._plan_row(i, ep)
        if not self.busy:
            self.build_btn.configure(state="normal")

    def _plan_row(self, i, ep):
        n = len(self.plan_state.plan)
        row = ctk.CTkFrame(self.plan_frame)
        row.pack(fill="x", padx=4, pady=3)
        row.columnconfigure(1, weight=1)
        ctk.CTkLabel(row, text=str(i + 1), width=34, font=ctk.CTkFont(size=16, weight="bold")
                     ).grid(row=0, column=0, rowspan=2, padx=(8, 4))
        ctk.CTkLabel(row, text=f"[{ep.game}]  {os.path.basename(ep.path)}", anchor="w"
                     ).grid(row=0, column=1, sticky="ew", pady=(6, 0))
        sub = f"{fmt_tc(ep.start)} – {fmt_tc(ep.end)}  ·  {ep.dur:.1f} с  ·  {ep.tag}"
        if not ep.manual:
            sub += f"  ·  реакция {ep.reaction:.0%}"
        ctk.CTkLabel(row, text=sub, anchor="w", text_color="#9aa4ad"
                     ).grid(row=1, column=1, sticky="ew", pady=(0, 6))
        bt = ctk.CTkFrame(row, fg_color="transparent")
        bt.grid(row=0, column=2, rowspan=2, padx=6)
        col = 0

        def mk(text, cmd, width=34, color=None):
            nonlocal col
            kw = {"fg_color": color, "hover_color": "#a33"} if color else {}
            ctk.CTkButton(bt, text=text, width=width, height=30, command=cmd, **kw
                          ).grid(row=0, column=col, padx=2)
            col += 1
        mk("▶", lambda e=ep: self.open_editor(e, True))
        mk("✂", lambda e=ep: self.open_editor(e, False))
        mk("🖊", lambda e=ep: self.rename_game(e), width=34) # Переименовать игру вручную
        mk("↻", lambda e=ep: self.replace_item(e))
        if i > 0:
            mk(f"⇄ {TRANS_RU.get(ep.trans, ep.trans)}", lambda e=ep: self.cycle_trans(e), 120)
        if i > 0:
            mk("▲", lambda e=ep: self.move(e, -1))
        if i < n - 1:
            mk("▼", lambda e=ep: self.move(e, 1))
        mk("🔴 Лазеры", lambda e=ep: self.open_laser_annotation(e.path, start_time=e.start), width=88)
        mk("✕", lambda e=ep: self.remove_item(e), color="#8a2f2f")

    def rename_game(self, ep):
        """Ручное переименование игры для выбранного момента."""
        new_name = simpledialog.askstring("Название игры", f"Введите название игры для файла:\n{os.path.basename(ep.path)}", initialvalue=ep.game, parent=self)
        if new_name and new_name.strip():
            new_name = new_name.strip()
            # Меняем во всем плане для этого файла или конкретно этого момента
            for e in self.plan_state.plan:
                if e.path == ep.path:
                    e.game = new_name
            self._render_plan()
            self.set_status(f"Название игры изменено на «{new_name}».")

    def open_editor(self, ep, autoplay):
        if self.busy:
            self.set_status("Подождите, идёт обработка.")
            return
        st = self.plan_state

        def on_apply(a, b, ep=ep):
            i = self._index_of(ep)
            if i < 0:
                self.set_status("⚠ Этот фрагмент уже изменён или удалён.")
                return
            old = st.plan[i]
            cs, ce = max(a, old.core_s), min(b, old.core_e)
            if ce - cs < 0.5:
                cs, ce = a, b
            st.plan[i] = replace(old, start=a, end=b, core_s=cs, core_e=ce, manual=True,
                                 words=[], words_rng=(0.0, 0.0), zoom=False)
            self._render_plan()
        FragmentEditor(self, st.ffmpeg, ep, on_apply,
                       on_remove=lambda: self.remove_item(ep),
                       on_replace=lambda: self.replace_item(ep), autoplay=autoplay)

    def add_manual(self):
        if self.busy:
            return
        path = filedialog.askopenfilename(title="Видео для нового момента",
                                          filetypes=[("Видео", "*.mp4 *.mkv"), ("Все файлы", "*.*")])
        if not path:
            return
        st = self._ensure_state()
        if not st.ffmpeg:
            self.set_status("❌ ffmpeg не найден. Выполните: pip install imageio-ffmpeg")
            return
        root = self.root_var.get().strip()
        detected_game = detect_game_name(path, root)
        if detected_game == "Игра":
            g_in = simpledialog.askstring("Название игры", "Не удалось определить игру. Введите название вручную:", initialvalue="Моя игра", parent=self)
            if g_in:
                detected_game = g_in.strip()

        ep = make_manual_episode(st.ffmpeg, path, 0.0, 10.0, detected_game)
        if ep.file_dur <= 0:
            self.set_status("⚠ Не удалось прочитать видео.")
            return
        ep = replace(ep, end=min(10.0, ep.file_dur))

        def on_apply(a, b):
            new = replace(ep, start=a, end=b, core_s=a, core_e=b)
            st.plan.append(new)
            self._render_plan()
            self.tabs.set("План")
        FragmentEditor(self, st.ffmpeg, ep, on_apply, new=True)

    def move(self, ep, d):
        i = self._index_of(ep)
        j = i + d
        if i < 0 or not (0 <= j < len(self.plan_state.plan)):
            return
        p = self.plan_state.plan
        p[i], p[j] = p[j], p[i]
        self._render_plan()

    def remove_item(self, ep):
        i = self._index_of(ep)
        if i >= 0:
            if not ep.manual:
                self.history.add(ep.path, ep.start, ep.end)
                self.history.save()
                self._update_hist()
            del self.plan_state.plan[i]
            self._render_plan()
            self.set_status("Момент удален и добавлен в исключения (больше не повторится).")

    def cycle_trans(self, ep):
        cyc = TRANS_CYCLE
        ep.trans = cyc[(cyc.index(ep.trans) + 1) % len(cyc)] if ep.trans in cyc else "auto"
        self._render_plan()

    def replace_item(self, ep):
        if self.busy:
            self.set_status("Подождите, идёт обработка.")
            return
        i = self._index_of(ep)
        if i < 0:
            return
        st = self.plan_state
        self.busy = True
        self.set_status("Ищу замену…")

        def done(r, ep=ep):
            self.busy = False
            if isinstance(r, Exception):
                self.set_status(f"❌ {r}")
            elif r is None:
                self.set_status("Подходящей замены не нашлось.")
            else:
                j = self._index_of(ep)
                if j >= 0:
                    st.plan[j] = replace(r, trans=ep.trans)
                    self.set_status("Момент заменён.")
                self._render_plan()
        self._bg(lambda: replace_episode(st, i, lambda: False), done)

    def _on_target(self, v):
        v = int(round(float(v) / 10) * 10)
        self.target_lbl.configure(text=f"{v} с" if v < 120 else f"{v // 60} мин {v % 60} с")

    def _update_hist(self):
        self.hist_lbl.configure(text=f"В истории: {self.history.count()} использованных моментов")

    def reset_history(self):
        self.history.clear()
        self._update_hist()
        self.set_status("История очищена.")

    def pick_music(self):
        path = filedialog.askopenfilename(
            title="Выберите музыкальную дорожку",
            filetypes=[("Аудио и видео со звуком", "*.mp3 *.wav *.m4a *.aac *.flac *.ogg *.opus *.wma *.mp4 *.mkv"),
                       ("Все файлы", "*.*")])
        if path:
            self.music_path_var.set(path)

    def pick_matador_music(self):
        path = filedialog.askopenfilename(
            title="Выберите музыку для режима «Матадоры»",
            filetypes=[("Аудио и видео со звуком", "*.mp3 *.wav *.m4a *.aac *.flac *.ogg *.opus *.wma *.mp4 *.mkv"),
                       ("Все файлы", "*.*")])
        if not path:
            return

        ext = os.path.splitext(path)[1].lower()
        if ext not in MATADOR_FILE_EXTS:
            self.set_status("⚠ Выберите MP3/WAV/M4A/AAC/FLAC/OGG/OPUS/WMA или MP4/MKV с аудио.")
            return

        # In source mode, put the chosen track beside the .py so build_exe.bat can embed it.
        # In a packaged EXE, persist it under the user's app data because _MEIPASS is temporary.
        if getattr(sys, "frozen", False):
            asset_dir = os.path.join(APP_DIR, "assets")
        else:
            asset_dir = project_assets_directory()

        target = os.path.join(asset_dir, "matadores" + ext)
        try:
            os.makedirs(asset_dir, exist_ok=True)
            source_abs = os.path.normcase(os.path.abspath(path))
            target_abs = os.path.normcase(os.path.abspath(target))

            # Keep only one auto-managed Matadores file, so the next build has no ambiguity.
            for old_ext in MATADOR_FILE_EXTS:
                old_file = os.path.join(asset_dir, "matadores" + old_ext)
                old_abs = os.path.normcase(os.path.abspath(old_file))
                if old_abs != target_abs and os.path.isfile(old_file):
                    try:
                        os.remove(old_file)
                    except OSError:
                        pass

            if source_abs != target_abs:
                shutil.copy2(path, target)

            self.matador_music_path_var.set(target)
            self.matador_music_chk.select()
            if getattr(sys, "frozen", False):
                self.set_status(
                    "Музыка Матадоров сохранена в папке пользователя и будет доступна при следующих запусках этого EXE. "
                    "Чтобы встроить её в новый EXE, выберите файл в версии .py перед сборкой."
                )
            else:
                self.set_status(
                    "Музыка Матадоров сохранена в assets рядом с программой. При следующем запуске build_exe.bat "
                    "она будет встроена в новый EXE автоматически."
                )
        except Exception as exc:
            self.set_status(f"Не удалось сохранить музыку Матадоров: {exc}")

    def open_matador_music_source(self):
        webbrowser.open("https://www.youtube.com/watch?v=9jSq99uN7q0")

    def open_youtube_audio_library(self):
        chosen = self.yt_filter_menu.get()
        webbrowser.open("https://www.youtube.com/audiolibrary")
        if chosen == "Атрибуция не требуется":
            msg = "В YouTube Audio Library выберите фильтр Attribution not required."
        else:
            msg = "В YouTube Audio Library выберите фильтр Attribution required и добавьте кредит автора в описание ролика."
        self.set_status(msg + " После скачивания выберите аудиофайл на вкладке «Режим и музыка».")

    def pick_root(self):
        d = filedialog.askdirectory(title="Корневая папка с играми")
        if d:
            self.root_var.set(d)
            if not self.out_var.get():
                self.out_var.set(os.path.join(d, "_output"))

    def pick_out(self):
        d = filedialog.askdirectory(title="Папка для готового ролика")
        if d:
            self.out_var.set(d)

    def _src_label(self):
        n = len(self.manual_files)
        self.src_lbl.configure(text=f"Выбрано вручную: {n} файл(ов)" if n else "Все видео из выбранной папки")

    def open_picker(self):
        root = self.root_var.get().strip()
        if not root or not os.path.isdir(root):
            self.set_status("⚠ Сначала выберите папку с играми.")
            return
        games = scan_root(root, self.out_var.get().strip())
        items = []
        for g in sorted(games):
            for p in sorted(games[g]):
                try:
                    mb = os.path.getsize(p) / 1048576
                except OSError:
                    mb = 0
                items.append((g, p, f"{g}  │  {os.path.relpath(p, os.path.join(root, g))}  ({mb:.0f} МБ)"))
        if not items:
            self.set_status("⚠ В папке нет видео .mp4/.mkv.")
            return
        FilePicker(self, items, self.manual_files, lambda sel: (setattr(self, 'manual_files', sel), self._src_label()))

    def add_files(self):
        files = filedialog.askopenfilenames(title="Добавить видео", filetypes=[("Видео", "*.mp4 *.mkv"), ("Все файлы", "*.*")])
        if files:
            self.manual_files = sorted(set(self.manual_files) | set(files))
            self._src_label()

    def open_laser_annotation(self, video_path, start_time=0.0):
        """Open manual laser marking from a concrete planned video moment."""
        if cv2 is None or Image is None or ImageTk is None:
            messagebox.showerror(
                "Не хватает библиотек",
                "Ручная разметка требует OpenCV и Pillow. Установи: python -m pip install opencv-python pillow",
                parent=self)
            return
        if not video_path or not os.path.isfile(video_path):
            messagebox.showerror("Видео не найдено", "Исходный файл этого момента недоступен.", parent=self)
            return
        LaserAnnotationWindow(self, video_path, start_time=start_time)

    def reset_sources(self):
        self.manual_files = []
        self._src_label()

    def set_status(self, text):
        self.status.configure(text=text)

    def _num(self, var, name, lo, hi):
        try:
            v = float(var.get().replace(",", "."))
        except ValueError:
            raise ValueError(f"Поле «{name}» должно быть числом.")
        if not lo <= v <= hi:
            raise ValueError(f"«{name}» должно быть от {lo} до {hi}.")
        return v

    def _read_settings(self):
        s = Settings()
        try:
            s.root_dir = self.root_var.get().strip()
            s.out_dir = self.out_var.get().strip()
            s.files = list(self.manual_files)
            if not s.files and (not s.root_dir or not os.path.isdir(s.root_dir)):
                raise ValueError("Выберите папку с играми или добавьте файлы вручную.")
            if not s.out_dir:
                raise ValueError("Выберите папку для сохранения ролика.")
            s.mode = self.mode_menu.get()
            s.shorts_mode = bool(self.shorts_chk.get())
            s.youtube_attribution_filter = self.yt_filter_menu.get()
            s.music_path = self.music_path_var.get().strip()
            s.music_volume = self._num(self.music_vol_var, "Громкость музыки", 0, 100) / 100.0
            s.matador_music_enabled = bool(self.matador_music_chk.get())
            s.matador_music_path = self.matador_music_path_var.get().strip()
            s.matador_music_volume = self._num(
                self.matador_music_vol_var, "Громкость музыки Матадоров", 0, 100) / 100.0
            s.original_volume = self._num(self.original_vol_var, "Громкость оригинала", 0, 100) / 100.0
            s.keep_original_audio = bool(self.keep_original_chk.get())
            s.laser_effect = bool(self.laser_chk.get())
            s.laser_universal_search = bool(self.laser_universal_chk.get())
            s.limit_resources = bool(self.limit_resources_chk.get())
            if s.music_path and not os.path.isfile(s.music_path):
                raise ValueError("Выбранный файл фоновой музыки не существует.")
            if s.matador_music_path and not os.path.isfile(s.matador_music_path):
                # Recover settings saved by older versions that stored a temporary PyInstaller path.
                embedded_track = default_matador_music_path()
                old_name = os.path.basename(s.matador_music_path).casefold()
                if embedded_track and old_name.startswith("matadores."):
                    s.matador_music_path = embedded_track
                else:
                    raise ValueError("Выбранный файл музыки Матадоров не существует.")
            if s.matador_music_enabled and not s.matador_music_path:
                s.matador_music_path = default_matador_music_path()
                if not s.matador_music_path:
                    raise ValueError(
                        "Включена музыка Матадоров, но файл не выбран и встроенный трек не найден. "
                        "Запустите версию .py и нажмите «Выбрать файл…» — программа сама сохранит трек "
                        "в assets для следующей сборки EXE."
                    )
            if s.mode.startswith("Фильмы") and not HAVE_WHISPER:
                raise ValueError("Режим «Фильмы» требует бесплатный пакет faster-whisper: pip install faster-whisper")
            if s.laser_effect and cv2 is None:
                raise ValueError("Эффект лазеров требует бесплатный OpenCV: pip install opencv-python")
            s.trim_on = bool(self.trim_chk.get())
            s.trim_sec = self._num(self.trim_var, "Обрезать секунд", 0, 600) if s.trim_on else 0
            s.clean_audio = bool(self.audio_chk.get())
            s.suppress_speech = bool(self.speech_chk.get())
            s.events = {k: bool(c.get()) for k, c in self.ev_chk.items()}
            if not any(s.events.values()) and not s.mode.startswith("Фильмы"):
                raise ValueError("Отметьте хотя бы одно событие.")
            s.skip_black = bool(self.black_chk.get())
            s.skip_frozen = bool(self.frozen_chk.get())
            s.require_visual = bool(self.vis_chk.get())
            s.visual_level = self.VIS_LEVELS[self.vis_menu.get()]
            s.snap_pauses = bool(self.snap_chk.get())
            s.pre = self._num(self.pre_var, "Секунд до события", 0, 30)
            s.post = self._num(self.post_var, "Секунд после события", 0, 30)
            s.min_len = self._num(self.minl_var, "Мин. длина момента", 3, 120)
            s.max_len = max(self._num(self.maxl_var, "Макс. длина момента", 5, 300), s.pre + s.post + 4, s.min_len)
            s.target = int(round(self.target_slider.get() / 10) * 10)
            s.strict = bool(self.strict_chk.get())
            s.order = self.order_menu.get()
            s.per_file_max = int(self._num(self.pfm_var, "Моментов из одного видео", 1, 20))
            s.balance = bool(self.bal_chk.get())
            s.variety = float(self.var_slider.get()) / 100.0
            s.no_repeat = bool(self.norep_chk.get())
            s.transitions = self.trans_menu.get()
            s.effects = bool(self.fx_chk.get())
            s.titles = bool(self.titles_chk.get())
            s.captions = bool(self.cap_chk.get()) and HAVE_WHISPER
            s.caption_lang = self.lang_menu.get()
            s.width, s.height = self.RESOLUTIONS[self.res_menu.get()]
            s.fps = int(self.fps_menu.get())
            s.frame_mode = self.frame_menu.get()
            s.quality = self.qual_menu.get()
            s.threads = int(self._num(self.thr_var, "Потоков", 1, 4))
            if s.limit_resources:
                s.threads = 1
            s.depth = self.depth_menu.get()
            s.hw = bool(self.hw_chk.get())
        except ValueError as e:
            self.set_status(f"⚠ {e}")
            return None
        return s

    def _poll(self):
        try:
            while True:
                item = self.q.get_nowait()
                kind = item[0]
                if kind == "log":
                    self.log_box.configure(state="normal")
                    self.log_box.insert("end", f"{datetime.now():%H:%M:%S}  {item[1]}\n")
                    self.log_box.see("end")
                    self.log_box.configure(state="disabled")
                elif kind == "bar":
                    self.bars[item[1]].set(item[2])
                elif kind == "status":
                    self.set_status(item[1])
                elif kind == "alert":
                    messagebox.showwarning(item[1], item[2], parent=self)
                elif kind == "error":
                    messagebox.showerror(item[1], item[2], parent=self)
                elif kind == "plan":
                    self.plan_state = item[1]
                    self._render_plan()
                    self.tabs.set("План")
                elif kind == "call":
                    item[1][item[2]](item[3]) # исправление под вызов
                elif kind == "finished":
                    self._lock_ui(False)
                    self._update_hist()
                    self._render_plan()
        except queue.Empty:
            pass
        self.after(100, self._poll)


if __name__ == "__main__":
    App().mainloop()