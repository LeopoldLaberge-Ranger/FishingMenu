"""
Box Tracker - holds A / D so a chosen object stays centered in a box.

How it works
  1. Press F9, then click in the game like normal. The script records the
     next 1.5 s of that monitor; step through the frames (LEFT/RIGHT or A/D),
     press ENTER on one where the image is showing, then drag:
       1/3  the SEARCH AREA  (the strip where the object and box move)
       2/3  the OBJECT       (a tight box around the thing to follow)
       3/3  the in-game BOX  (or press C to skip and use a virtual square
                              centered in the search area)
     In each selection window: drag with the mouse, then press ENTER or SPACE.
  2. Press F8 to start / pause pressing keys (tracking + overlay keep running
     while paused so you can check it's locked on).
  3. Press F10 to quit.

Overlay colors: blue = search area, green = box, red = object.
"""
import ctypes
import ctypes.wintypes
import base64
import json
import pickle
import queue
import random
import sys
import threading
from collections import deque
import time
import traceback
import tkinter as tk
from tkinter import scrolledtext, ttk
from pathlib import Path

import cv2
import mss

MSS = getattr(mss, "MSS", None) or mss.mss  # newer mss renamed the class
import numpy as np
import pydirectinput
from pynput import keyboard, mouse

# ----------------------------- settings ---------------------------------
LEFT_KEY = "a"
RIGHT_KEY = "d"
INVERT = False          # True swaps A and D
DEADZONE_PX = 4         # no key pressed while object is this close to box center
FULL_PRESS_PX = 40      # off by this many px or more -> key held fully; less -> tapped
TAP_PERIOD = 0.06       # seconds per tap cycle for small corrections
LEAD = 0.15             # seconds of prediction / braking. F6 lower, F7 raise (live)
BOX_SEARCH_RADIUS = 120 # px the box may move between frames (image matching mode)
MIN_COLOR_DIFF = 6      # box vs track color difference needed to use color mode
BOX_MIN_CONTRAST = 6    # box must be this much brighter (0-255) than beside it to count as found
GONE_DELAY = 0.5        # fish missing this long (s) = minigame ended
# keys / mouse buttons + hold times, pressed in order when the minigame ends (ACTIVE only).
# Mouse names: "mouse1" (left), "mouse2" (right), "mouse3" (middle), "mouse4", "mouse5" (side buttons)
END_SEQUENCE = [("a", 0.25), ("d", 0.25), ("mouse4", 0.05)]
# then, until the yellow "!" shows (or CHECK_TIMEOUT s pass), look for yellow in the search area
CHECK_CLICK = "mouse4"  # clicked when the yellow checkmark appears
CHECK_MIN_PIXELS = 250  # smallest '!' stroke in px (yours measures ~380-480)
EXCL_MAX_PIXELS = 800   # bigger yellow shapes (scenery, catch popups) are not the '!'
EXCL_WIDTH = (8, 26)    # '!' stroke width range in px (yours ~12-20)
EXCL_HEIGHT = (28, 50)  # '!' stroke height range in px (yours ~34-41)
CHECK_TIMEOUT = 30.0    # no '!' this long (s) after casting -> cast again
IDLE_RECAST = 15.0      # ACTIVE but nothing happening this long (s) -> cast again
MODE = "fishing"        # "fishing", "mining" or "combat" (panel tabs / F2)
MODES = ("fishing", "mining", "combat")
GAME_MONITOR = 0        # which screen the game is on: 0 = auto (where you picked things / main), 1, 2, ...
MANUAL_MODE = False     # start in manual mode (F4 toggles): catch + recast only, no moving
WANDER_ENABLED = True   # walk around + jump now and then (panel switch)
WANDER_EVERY = 60.0     # s of fishing between walk-arounds (0 = never)
WANDER_JITTER = 10.0    # +/- this many s of randomness on that interval
WANDER_SECONDS = (2.0, 4.0)  # walk A for a random time in this range, then D for the same time
JUMP_KEY = "space"
WATCH_WHOLE_SCREEN = True  # look for a NEW '!' anywhere on screen (no F11 setup needed)
CHAR_TRACK_EVERY = 0.2  # s between looks for your character (moves the '!' area with it)
CHAR_MOVE_PX = 20       # character must move more than this (px) before the '!' area follows
CHAR_MAX_JUMP = 400     # bigger jumps need a confident (0.7+) match, so look-alikes can't steal it
CHAR_SURE_MATCH = 0.62   # 0-1: a match this good near the last spot is trusted without searching everywhere
CHAR_X_MATCH = 0.45      # 0-1: how sure the left-right character search must be
CHAR_JUMP_MATCH = 0.55   # 0-1: needed to accept a big change in the character's height
CHAR_HEIGHT_MATCH = 0.25  # 0-1: how sure the character-height search must be (else keep last height)
CHAR_MIN_MATCH = 0.45   # 0-1: below this the character isn't recognized -> area stays put
ANCHOR_ENABLED = True   # walk back to the F5 anchor before casting (panel switch)
ANCHOR_TOLERANCE = 12   # px: this close to the anchor (F5) counts as "there"
ANCHOR_MAX_TIME = 6.0   # s to spend walking back before giving up
ANCHOR_MIN_MATCH = 0.5  # 0-1: below this the scenery isn't recognized -> don't walk
ANCHOR_WALK_SPEED = 300 # px/s first guess at walking speed (it learns the real one)
ANCHOR_INVERT = False   # True if it walks the wrong way
YELLOW_HSV_LOW = (20, 120, 150)   # OpenCV HSV: hue 0-179
YELLOW_HSV_HIGH = (38, 255, 255)
EXCL_MIN_ASPECT = 1.8   # '!' stroke: height at least this many times its width
EXCL_JUMP_PX = 150      # F11 area: yellow must jump by this many px above the last second
CLEAR_BEFORE_WATCH = 0.3  # s the area must be free of '!'-like yellow before watching
EXCL_MIN_THICKNESS = 4  # px; yellow lines thinner than this (borders) are erased first
YELLOW_DIAGNOSTICS = True  # print what yellow it sees while waiting for the '!'
MATCH_THRESHOLD = 0.55  # 0..1 template-match confidence; below = "lost"
VIRTUAL_BOX_WIDTH = 80  # width of the virtual square when no in-game box chosen
MAX_FPS = 120
BURST_SECONDS = 1.5     # how long to record after your click when selecting (F9)
BURST_FPS = 15
# -------------------------------------------------------------------------

mouse_ctl = mouse.Controller()
MOUSE_BUTTONS = {
    "mouse1": mouse.Button.left, "mouse2": mouse.Button.right, "mouse3": mouse.Button.middle,
    "mouse4": mouse.Button.x1, "mouse5": mouse.Button.x2,
}

pydirectinput.PAUSE = 0
pydirectinput.FAILSAFE = False

# Use real pixels so screenshots, overlay and selections line up on scaled displays
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


def select_roi(img, title):
    """Let the user drag a rectangle on img. Returns (x, y, w, h) or None."""
    h, w = img.shape[:2]
    scale = min(1600 / w, 900 / h, 4.0)
    interp = cv2.INTER_NEAREST if scale > 1 else cv2.INTER_AREA
    disp = cv2.resize(img, None, fx=scale, fy=scale, interpolation=interp)
    cv2.namedWindow(title, cv2.WINDOW_AUTOSIZE)
    cv2.setWindowProperty(title, cv2.WND_PROP_TOPMOST, 1)
    x, y, rw, rh = cv2.selectROI(title, disp, showCrosshair=True, fromCenter=False)
    try:
        cv2.destroyWindow(title)
    except cv2.error:
        pass  # already closed with the window's X
    cv2.waitKey(1)
    if rw == 0 or rh == 0:
        return None
    x, y = int(x / scale), int(y / scale)
    rw, rh = max(1, int(rw / scale)), max(1, int(rh / scale))
    return x, y, min(rw, w - x), min(rh, h - y)


def wait_for_click(cancelled):
    """Block until the left mouse button is pressed. False if cancelled() turns true."""
    clicked = threading.Event()

    def on_click(x, y, button, pressed):
        if pressed and button == mouse.Button.left:
            clicked.set()
            return False

    listener = mouse.Listener(on_click=on_click)
    listener.start()
    while not clicked.wait(0.05):
        if cancelled():
            listener.stop()
            return False
    return True


def pick_frame(frames):
    """Step through captured frames; returns the chosen one or None."""
    title = "Pick the frame:  LEFT/RIGHT or A/D to step,  ENTER to use,  ESC to cancel"
    h, w = frames[0].shape[:2]
    scale = min(1600 / w, 900 / h, 1.0)
    cv2.namedWindow(title, cv2.WINDOW_AUTOSIZE)
    cv2.setWindowProperty(title, cv2.WND_PROP_TOPMOST, 1)
    i = 0
    chosen = None
    while True:
        disp = cv2.resize(frames[i], None, fx=scale, fy=scale, interpolation=cv2.INTER_AREA)
        cv2.putText(disp, f"frame {i + 1}/{len(frames)}", (10, 30),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.9, (0, 255, 0), 2)
        cv2.imshow(title, disp)
        k = cv2.waitKeyEx(0)
        if k in (2424832, ord("a"), ord("A")):        # left arrow
            i = max(0, i - 1)
        elif k in (2555904, ord("d"), ord("D")):      # right arrow
            i = min(len(frames) - 1, i + 1)
        elif k in (13, 32):                           # enter / space
            chosen = frames[i]
            break
        elif k == 27 or cv2.getWindowProperty(title, cv2.WND_PROP_VISIBLE) < 1:
            break
    try:
        cv2.destroyWindow(title)
    except cv2.error:
        pass  # already closed with the window's X
    cv2.waitKey(1)
    return chosen


_THICK_KERNEL = None


def yellow_blobs(frame):
    """Returns (raw yellow px, [(w, h, area), ...] of the thick yellow blobs).
    Lines thinner than EXCL_MIN_THICKNESS (like the x2 badge's border) are erased first."""
    global _THICK_KERNEL
    if _THICK_KERNEL is None:
        _THICK_KERNEL = np.ones((EXCL_MIN_THICKNESS, EXCL_MIN_THICKNESS), np.uint8)
    hsv = cv2.cvtColor(frame, cv2.COLOR_BGR2HSV)
    mask = cv2.inRange(hsv, YELLOW_HSV_LOW, YELLOW_HSV_HIGH)
    raw = int(cv2.countNonZero(mask))
    thick = cv2.morphologyEx(mask, cv2.MORPH_OPEN, _THICK_KERNEL)
    _, _, stats, _ = cv2.connectedComponentsWithStats(thick, connectivity=8)
    return raw, [(int(w), int(h), int(a)) for _, _, w, h, a in stats[1:]]


def is_exclamation(w, h, area):
    return (h >= EXCL_MIN_ASPECT * w
            and EXCL_WIDTH[0] <= w <= EXCL_WIDTH[1]
            and EXCL_HEIGHT[0] <= h <= EXCL_HEIGHT[1]
            and CHECK_MIN_PIXELS <= area <= EXCL_MAX_PIXELS)


def find_exclamations(frame):
    """Centers (x, y) and sizes of every '!'-shaped yellow mark in the frame."""
    hsv = cv2.cvtColor(frame, cv2.COLOR_BGR2HSV)
    mask = cv2.inRange(hsv, YELLOW_HSV_LOW, YELLOW_HSV_HIGH)
    if cv2.countNonZero(mask) < CHECK_MIN_PIXELS:
        return []
    global _THICK_KERNEL
    if _THICK_KERNEL is None:
        _THICK_KERNEL = np.ones((EXCL_MIN_THICKNESS, EXCL_MIN_THICKNESS), np.uint8)
    thick = cv2.morphologyEx(mask, cv2.MORPH_OPEN, _THICK_KERNEL)
    _, _, stats, cents = cv2.connectedComponentsWithStats(thick, connectivity=8)
    return [(int(cx), int(cy), int(a)) for (x, y, w, h, a), (cx, cy) in zip(stats[1:], cents[1:])
            if is_exclamation(int(w), int(h), int(a))]


def count_yellow(frame):
    """Size in px of the biggest yellow blob shaped and sized like the '!' stroke; 0 if none."""
    _, blobs = yellow_blobs(frame)
    return max((a for w, h, a in blobs if is_exclamation(w, h, a)), default=0)


def click(name, secs=0.05):
    btn = MOUSE_BUTTONS[name]
    mouse_ctl.press(btn)
    try:
        time.sleep(secs)
    finally:
        mouse_ctl.release(btn)


def find_hp_bar(shot):
    """The green HP bar at the bottom of the screen: (x0, y0, y1, width) or None."""
    H, W = shot.shape[:2]
    y_top, x_lo, x_hi = int(H * 0.9), int(W * 0.15), int(W * 0.55)
    hsv = cv2.cvtColor(shot[y_top:, x_lo:x_hi], cv2.COLOR_BGR2HSV)
    g = ((hsv[:, :, 0] >= 60) & (hsv[:, :, 0] <= 92) & (hsv[:, :, 1] > 110) & (hsv[:, :, 2] > 140)).astype(np.uint8)
    n, _, st, _ = cv2.connectedComponentsWithStats(g, connectivity=8)
    best = None
    for i in range(1, n):
        x, y, w, h, a = st[i]
        if w >= 6 * h and 4 <= h <= 60 and (best is None or a > best[4]):
            best = (x, y, w, h, a)
    if best is None:
        return None
    x, y, w, h, _ = best
    return x_lo + x, y_top + y, y_top + y + h, w


def hp_fill(band):
    """How many px of the HP bar are filled, from its left end: bright, colourful, not blue
    (any colour, in case the bar turns yellow / red when low)."""
    hsv = cv2.cvtColor(band, cv2.COLOR_BGR2HSV)
    # (the bar shades from cyan to green; the MP bar's real blue is left out)
    fill = (hsv[:, :, 1] > 100) & (hsv[:, :, 2] > 120) & ~((hsv[:, :, 0] >= 100) & (hsv[:, :, 0] <= 130))
    cols = fill.mean(axis=0) > 0.3
    start = np.where(cols[:6])[0]  # (rounded left end)
    if not len(start):
        return 0
    x, gap, end = int(start[0]), 0, int(start[0])
    while x < len(cols):  # filled part: from the left, allowing tiny gaps
        if cols[x]:
            end, gap = x + 1, 0
        else:
            gap += 1
            if gap > 2:
                break
        x += 1
    return end


def valid_key(name):
    """A key or mouse button name the script can press: mouse1-5, or a keyboard key (y, 6, f, space...)."""
    name = (name or "").strip().lower()
    return name in MOUSE_BUTTONS or name in pydirectinput.KEYBOARD_MAPPING


def press(name, secs=0.06):
    """Press a key or a mouse button (by name, as in the panel's KEYS settings)."""
    name = (name or "").strip().lower()
    if not name:
        return
    if name in MOUSE_BUTTONS:
        click(name, secs)
    else:
        pydirectinput.keyDown(name)
        time.sleep(secs)
        pydirectinput.keyUp(name)


def log(*args):
    print(time.strftime("[%H:%M:%S]"), *args)


def grab_area(sct, area):
    x, y, w, h = area
    return np.ascontiguousarray(np.array(sct.grab({"left": x, "top": y, "width": w, "height": h}))[:, :, :3])


def find_box_by_brightness(frame, by, bh, bw, fish=None):
    """Locate the see-through box as the bw-wide stretch that is brightest compared with
    the strips right beside it. Works in any lighting (day, night, dark areas) because it
    only compares the box with its own surroundings. fish = (x, y, w, h) to ignore.
    Returns (left_x, contrast) where contrast = how much brighter (0-255 scale) it is."""
    trim = bh // 6
    y0, y1 = by + trim, by + bh - trim
    L = cv2.cvtColor(frame[y0:y1], cv2.COLOR_BGR2LAB)[:, :, 0].astype(np.float32)
    if fish is not None:  # the fish's white outline would look like extra brightness
        fx, fy, fw, fh = fish
        r0, r1 = max(fy - y0, 0), min(fy + fh - y0, L.shape[0])
        if r1 - r0 < L.shape[0] and r1 > r0:
            L[r0:r1, max(fx, 0):fx + fw] = np.nan
    col = np.nanmean(L, axis=0)
    col = np.where(np.isnan(col), np.nanmean(col), col)
    n = len(col)
    if bw >= n:
        return 0, 0.0
    cs = np.concatenate([[0.0], np.cumsum(col)])
    x = np.arange(n - bw + 1)
    inside = (cs[x + bw] - cs[x]) / bw
    m = max(6, bw // 2)  # width of the strips beside the box
    lo, hi = np.maximum(x - m, 0), np.minimum(x + bw + m, n)
    side_sum = (cs[x] - cs[lo]) + (cs[hi] - cs[x + bw])
    side_n = (x - lo) + (hi - x - bw)
    outside = np.where(side_n > 0, side_sum / np.maximum(side_n, 1), inside)
    contrast = inside - outside
    best = int(np.argmax(contrast))
    return best, float(contrast[best])


SAVE_FILE = Path(__file__).with_name("selection.pkl")
CFG_KEYS = {"search", "obj", "obj_y", "box", "box_mask", "box_colors", "box_w", "box_y", "box_h"}


def save_selection(cfg, mon, excl_area, anchor=None, char=None):
    try:
        with open(SAVE_FILE, "wb") as f:
            pickle.dump({"cfg": cfg, "mon": mon, "excl": excl_area, "anchor": anchor, "char": char}, f)
        print(f"Selection saved to {SAVE_FILE}")
    except Exception as e:
        print("Couldn't save selection:", e)


def load_selection():
    """Returns (cfg, mon, excl_area, anchor, char) from the last run, or None."""
    if not SAVE_FILE.exists():
        return None
    try:
        with open(SAVE_FILE, "rb") as f:
            data = pickle.load(f)
        cfg = data.get("cfg")
        if cfg is not None and set(cfg) != CFG_KEYS:  # saved by a different version of the script
            print("Saved fishing selection is from an older version - press F9 to select again.")
            cfg = None
        if data.get("cfg2") is not None and set(data["cfg2"]) == CFG_KEYS:
            cfg = data["cfg2"]  # older save with an x2 selection: it works for every catch
        return cfg, data["mon"], data.get("excl"), data.get("anchor"), data.get("char")
    except Exception as e:
        print("Couldn't load saved selection:", e)
        return None


CHAR_SCALE = 2  # character search runs at 1/2 size: fast enough to do several times a second


def make_character(shot, rect, excl_area, mon):
    """Remember what the character looks like (both facing directions) and where the
    '!' area sits relative to it."""
    x, y, w, h = rect
    tpl = shot[y:y + h, x:x + w].copy()
    small = cv2.resize(tpl, None, fx=1 / CHAR_SCALE, fy=1 / CHAR_SCALE, interpolation=cv2.INTER_AREA)
    cx, cy = mon["left"] + x, mon["top"] + y
    ex, ey, ew, eh = excl_area
    shape, mask = _light_norm(small), _figure_mask(small)
    return {"tpls": [small, cv2.flip(small, 1)], "offset": (ex - cx, ey - cy), "size": (ew, eh), "mon": mon,
            "pick": (cx, cy, w, h),  # the camera keeps the character at this left-right spot
            "shapes": [(shape, mask), (cv2.flip(shape, 1), cv2.flip(mask, 1))]}


def _light_norm(bgr):
    """Gray picture divided by its local brightness: looks the same in day, night and rain."""
    g = cv2.cvtColor(bgr, cv2.COLOR_BGR2GRAY).astype(np.float32)
    return g / (cv2.GaussianBlur(g, (0, 0), 6) + 8)


def _figure_mask(tpl, tol=16):
    """1 = character, 0 = background: flood-fill from the picture's edges through colors like
    the edge (sky, grass, trees...). The bottom quarter is dropped too: grass hides the legs."""
    h, w = tpl.shape[:2]
    ff = np.zeros((h + 2, w + 2), np.uint8)
    flags = 4 | cv2.FLOODFILL_MASK_ONLY | cv2.FLOODFILL_FIXED_RANGE | (255 << 8)
    seeds = [(x, y) for x in range(0, w, 2) for y in (0, h - 1)] + [(x, y) for y in range(0, h, 2) for x in (0, w - 1)]
    for x, y in seeds:
        if ff[y + 1, x + 1] == 0:
            cv2.floodFill(tpl.copy(), ff, (x, y), 0, (tol,) * 3, (tol,) * 3, flags)
    m = (ff[1:-1, 1:-1] == 0).astype(np.float32)
    m[int(h * 0.75):] = 0
    if m.mean() < 0.12:  # the fill ate (almost) everything: keep the whole top part instead
        m[:] = 1
        m[int(h * 0.75):] = 0
    return m


def find_char_shape(shot, mon, char, x0, y0, x1, y1):
    """Search the character's shape (lighting-proof, background cut out) inside the screen
    area x0..x1, y0..y1 (px from the monitor's corner). Near the screen's left/right edge
    the character may be half off screen, so its visible half is tried there too.
    Returns (left x, top y) on screen + match 0-1."""
    x0, y0 = max(0, int(x0)), max(0, int(y0))
    x1, y1 = min(shot.shape[1], int(x1)), min(shot.shape[0], int(y1))
    if x1 - x0 < 8 or y1 - y0 < 8:
        return None, -1.0
    small = cv2.resize(shot[y0:y1, x0:x1], None, fx=1 / CHAR_SCALE, fy=1 / CHAR_SCALE, interpolation=cv2.INTER_AREA)
    norm = _light_norm(small)
    sw = norm.shape[1]
    best = (None, -1.0)
    for shape, mask in char["shapes"]:
        w = shape.shape[1]
        tries = [(shape, mask, 0, None)]
        if x1 >= shot.shape[1] - 2:  # right edge: only the character's left half may be visible
            tries.append((shape[:, :w // 2], mask[:, :w // 2], 0, "right"))
        if x0 <= 2:  # left edge: only the right half may be visible
            tries.append((shape[:, w // 2:], mask[:, w // 2:], -(w // 2), "left"))
        for shp, msk, dx, edge in tries:
            if shp.shape[0] > norm.shape[0] or shp.shape[1] > norm.shape[1] or msk.sum() < 10:
                continue
            res = cv2.matchTemplate(norm, shp, cv2.TM_CCOEFF_NORMED, mask=msk)
            res = np.nan_to_num(res, nan=-1.0, posinf=-1.0, neginf=-1.0)
            # a half-picture only counts where the character would stick out past the edge
            if edge == "right":
                res[:, :max(0, sw - w)] = -1
            elif edge == "left":
                res[:, w // 2 + 1:] = -1
            _, conf, _, (lx, ly) = cv2.minMaxLoc(res)
            if edge:
                conf -= 0.1  # half a picture matches junk more easily: it counts for less
            if conf > best[1]:
                best = ((mon["left"] + x0 + (lx + dx) * CHAR_SCALE, mon["top"] + y0 + ly * CHAR_SCALE), conf)
    return best


def character_height(shot, mon, char, left=None):
    """Search a narrow up-down strip at the character's left-right spot.
    Returns (top y on screen, match 0-1)."""
    px, py, pw, ph = char["pick"]
    left = px if left is None else left
    pos, conf = find_char_shape(shot, mon, char, left - mon["left"] - pw, 0, left - mon["left"] + 2 * pw, shot.shape[0])
    return (pos[1] if pos else None), conf


def locate_character(shot, mon, char, last=None):
    """Find the character in a screenshot of mon. Searches near the last known spot first
    (fast, and can't jump to look-alikes), then the whole screen.
    Returns (x, y, w, h) on screen and the match (0-1), or (None, best match)."""
    small = cv2.resize(shot, None, fx=1 / CHAR_SCALE, fy=1 / CHAR_SCALE, interpolation=cv2.INTER_AREA)
    th, tw = char["tpls"][0].shape[:2]
    regions = []
    if last is not None:
        lx, ly = (last[0] - mon["left"]) // CHAR_SCALE, (last[1] - mon["top"]) // CHAR_SCALE
        r = 3 * max(th, tw)
        regions.append((max(0, lx - r), max(0, ly - r), min(small.shape[1], lx + tw + r),
                        min(small.shape[0], ly + th + r), CHAR_MIN_MATCH - 0.1))
    regions.append((0, 0, small.shape[1], small.shape[0], CHAR_MIN_MATCH))
    best_conf = -1.0
    for x0, y0, x1, y1, need in regions:
        area = small[y0:y1, x0:x1]
        best = None
        for tpl in char["tpls"]:
            if tpl.shape[0] > area.shape[0] or tpl.shape[1] > area.shape[1]:
                continue
            res = cv2.matchTemplate(area, tpl, cv2.TM_CCOEFF_NORMED)
            _, conf, _, loc = cv2.minMaxLoc(res)
            if best is None or conf > best[0]:
                best = (conf, loc, tpl.shape[:2])
        if best is None:
            continue
        conf, (bx, by), (h, w) = best
        best_conf = max(best_conf, conf)
        if conf >= need:
            sx, sy = x0 + bx, y0 + by
            if conf >= 0.75 and len(char["tpls"]) < 12:  # remember new poses (walking frames...)
                pose = small[sy:sy + th, sx:sx + tw]
                if pose.shape[:2] == (th, tw) and all(_ncc(pose.astype(np.float32), t.astype(np.float32)) < 0.97
                                                      for t in char["tpls"]):
                    char["tpls"] += [pose.copy(), cv2.flip(pose, 1)]
            return (mon["left"] + sx * CHAR_SCALE, mon["top"] + sy * CHAR_SCALE,
                    w * CHAR_SCALE, h * CHAR_SCALE), conf
    return None, best_conf


def find_character(sct, char):
    """Returns (screen x, screen y, match 0-1) of the character's top-left corner."""
    mon = char["mon"]
    shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
    small = cv2.resize(shot, None, fx=1 / CHAR_SCALE, fy=1 / CHAR_SCALE, interpolation=cv2.INTER_AREA)
    best = (0, 0, -1.0)
    for tpl in char["tpls"]:
        res = cv2.matchTemplate(small, tpl, cv2.TM_CCOEFF_NORMED)
        _, conf, _, loc = cv2.minMaxLoc(res)
        if conf > best[2]:
            best = (mon["left"] + loc[0] * CHAR_SCALE, mon["top"] + loc[1] * CHAR_SCALE, conf)
    return best


ANCHOR_SCALE = 4  # anchor screenshots are compared at 1/4 size (fast, and ignores tiny details)


def _anchor_small(shot):
    return cv2.cvtColor(cv2.resize(shot, None, fx=1 / ANCHOR_SCALE, fy=1 / ANCHOR_SCALE,
                                   interpolation=cv2.INTER_AREA), cv2.COLOR_BGR2GRAY)


def make_anchor(shot, mon):
    """Remember the scenery as 7 overlapping vertical strips across the screen, so even
    after a big drift some strip is still on screen to recognize. The character (always
    at screen center) is masked out."""
    small = _anchor_small(shot)
    h, w = small.shape
    y0, y1 = int(h * 0.15), int(h * 0.85)       # skip UI bars at the very top/bottom
    sw = w // 4
    cx0, cx1 = int(w * 0.45), int(w * 0.55)     # character columns
    cy0, cy1 = int(h * 0.375) - y0, int(h * 0.625) - y0
    strips = []
    for k in range(7):
        x = round(k * (w - sw) / 6)
        mask = np.ones((y1 - y0, sw), np.uint8)
        a, b_ = max(cx0 - x, 0), min(cx1 - x, sw)
        if b_ > a:
            mask[cy0:cy1, a:b_] = 0
        strips.append({"patch": small[y0:y1, x:x + sw].copy(), "mask": mask, "pos": (x, y0)})
    return {"strips": strips, "mon": mon}


def anchor_offset(sct, anchor):
    """Where the anchor is now relative to the character, in screen px (negative = to the
    left), and how sure (0-1) the match is (best of the strips)."""
    shot = np.ascontiguousarray(np.array(sct.grab(anchor["mon"]))[:, :, :3])
    small = _anchor_small(shot)
    best_dx, best_conf = 0, -1.0
    for st in anchor["strips"]:
        res = cv2.matchTemplate(small, st["patch"], cv2.TM_CCOEFF_NORMED, mask=st["mask"])
        res = np.nan_to_num(res, nan=-1.0, posinf=-1.0, neginf=-1.0)
        _, conf, _, loc = cv2.minMaxLoc(res)
        if conf > best_conf:
            best_dx, best_conf = (loc[0] - st["pos"][0]) * ANCHOR_SCALE, conf
    return best_dx, best_conf


def monitor_at(sct, x, y):
    for m in sct.monitors[1:]:
        if m["left"] <= x < m["left"] + m["width"] and m["top"] <= y < m["top"] + m["height"]:
            return m
    return sct.monitors[1]


def monitor_under_cursor(sct):
    pt = ctypes.wintypes.POINT()
    ctypes.windll.user32.GetCursorPos(ctypes.byref(pt))
    return monitor_at(sct, pt.x, pt.y)


def match(frame, tpl, mask=None, near_x=None, radius=None):
    """Find tpl in frame. Returns (left_x, score).
    With near_x, only searches within radius px of that left-x position."""
    tw, fw = tpl.shape[1], frame.shape[1]
    lo, hi = 0, fw
    if near_x is not None:
        lo = max(0, int(near_x - radius))
        hi = min(fw, int(near_x + tw + radius))
        if hi - lo < tw:
            lo, hi = 0, fw
    res = cv2.matchTemplate(frame[:, lo:hi], tpl, cv2.TM_CCOEFF_NORMED, mask=mask)
    res = np.nan_to_num(res, nan=-1.0, posinf=-1.0, neginf=-1.0)
    _, score, _, loc = cv2.minMaxLoc(res)
    return lo + loc[0], score


class Tracker:
    def __init__(self):
        self.cfg = None
        self.mon = None          # monitor the target was selected on
        self.state = None       # latest result, read by the overlay
        self.active = False      # pressing keys?
        self.hidden = False      # hide overlay (during selection)
        self.quit = False
        self.reselect = False
        self.armed = False       # waiting for the click that starts the capture
        self.lead = LEAD
        self.excl_area = None     # (x, y, w, h) on screen where the '!' pops up (F11)
        self.select_excl = False
        self.anchor = None        # scenery around the character, for walking back (F5)
        self.char = None          # character look + '!' offset, so the '!' area follows you (F11)
        self.set_anchor = False
        self.walk_speed = ANCHOR_WALK_SPEED
        self.mine_wait = False    # answered a mining menu, waiting for it to close
        self.mine_seen = self.mine_answered = 0.0
        self.mine_pending = None
        self.mine_answered_sig = ()
        self.mine_done_ys = []
        self.add_ore = False      # panel asked to grab a new ore picture
        self.reveal_at = -1e9     # auto mining: last mouse-5 reveal
        self.after_mine, self.reveal_due = False, None  # reveal again a moment after mining
        self.e_at, self.e_tries = None, 0
        self.skip_until = 0.0     # ignore ores until then (after giving up on one)
        self.patrol_dir, self.dir_since, self.walk_dir = 1, 0.0, 0
        self.patrol_len = PATROL_SWITCH  # current sweep length (grows while nothing is found)
        self.stuck_hist, self.jump_at = deque(), -1e9
        self.char_cache = (-1e9, None)  # (time, last character rect)
        self.char_warned = -1e9
        self.level_warned = -1e9
        self.prev_scene, self.hann = None, None  # for measuring camera scrolling
        self.walk_speed_px = 400.0   # learned walking speed (px/s)
        self.mm = self.mm_prev = None  # minimap (dot x, dot y, terrain left, terrain right)
        self.mm_scale = None         # learned: screen px per minimap px
        self.mm_sum_world = self.mm_sum_dot = 0.0
        self.mm_speed = 15.0          # learned walking speed in minimap px/s
        self.crystal_checked = 0.0
        self.jump_capped = False   # jump height only measured under a ceiling (may be higher)
        self.mm_last_dot = None
        self.mm_last_crystal = None
        self.test_jump, self.jump_trace = False, []
        self.user_e_at, self.pc_last, self.pc_block, self.pc_prev = -1e9, 0.0, 0.0, None  # manual crystal help
        self.pc_bg, self.pc_bg_t = None, 0.0  # a recent picture from before you pressed E
        self.crys_mem = None  # the crystal being tried: guesses already used
        self.dash_at = -1e9  # when the last dash was used (it has a cooldown)
        self.buff_due = 0.0  # when the buff key (Y) is due next
        self.mouse_held = set()  # mouse buttons held down (combat)
        self.veil_at = -1e9  # last veil press
        self.hunt_vis = None  # crystal hunt, on screen: character box + crystal spot (overlay)
        self.hp_bar, self.hp_bar_t, self.hp_checked, self.hp_frac = None, -1e9, -1e9, None
        self.healing = None  # combat: when we stopped to heal (low HP)
        self.combat_turn_at, self.combat_dir = 0.0, 1
        self.cmb_track, self.cmb_checked, self.cmb_run_start = deque(), -1e9, 0.0  # combat: am I moving?
        self.cmb_stuck, self.cmb_lock, self.cmb_screen_x, self.cmb_bursting = 0, None, 0.0, False
        self.veil_due = None  # when the veil key (6) is due, after the buff
        self.seen_ref, self.scroll_since_seen = None, 0.0  # last clear sighting: (left x, dot x)
        self.mm_hist = deque()       # (time, dot x) for stuck detection
        self.pick_minimap = False
        self.look_time = 0.25        # learned time per look (s)
        self.last_look = self.last_cx = None
        self.walking_since_look = False
        self.approach_last, self.tap_gain = None, 0.8
        self.diag_at, self.char_conf = -1e9, (0.0, 0.0)
        self.target = None        # last ore we walked to: (screen x, time seen, name)
        self.pick_char = False
        self.mine_vis = None      # what the overlay shows while mining: character + target ore
        self.manual = MANUAL_MODE  # manual mode: no A/D taps, walk-arounds or anchor walking
        self.yellow_goal = CHECK_MIN_PIXELS
        self.yellow_px = None     # set while watching for the '!'
        self.held = None
        self.fps = 0.0

    # --- keys ---
    def game_mon(self, sct, cursor=False):
        """The screen the game is on: the one chosen in the panel, else the one things were
        picked on, else (cursor=True) the one under the mouse, else the main screen."""
        mons = sct.monitors
        if GAME_MONITOR and 1 <= int(GAME_MONITOR) < len(mons):
            return mons[int(GAME_MONITOR)]
        if self.mon is not None:
            return self.mon
        return monitor_under_cursor(sct) if cursor else monitor_at(sct, 0, 0)

    def hold(self, key):
        if key is None and self.mouse_held:
            for name in list(self.mouse_held):
                try:
                    mouse_ctl.release(MOUSE_BUTTONS[name])
                except Exception:
                    pass
            self.mouse_held.clear()
        if key == self.held:
            return
        if self.held:
            pydirectinput.keyUp(self.held)
        if key:
            pydirectinput.keyDown(key)
        self.held = key

    # --- selection ---
    def do_select(self, sct):
        # hand keyboard focus back to the game once the selection windows close
        game = ctypes.windll.user32.GetForegroundWindow()
        try:
            self._select(sct)
        finally:
            self.hidden = False
            if game:
                ctypes.windll.user32.SetForegroundWindow(game)

    def _select(self, sct):
        # F9 arms; the next left click in the game starts a short burst capture
        self.armed = True
        print("Armed - click in the game to make the image appear.")
        clicked = wait_for_click(lambda: self.quit or self.reselect)
        self.armed = False
        if not clicked:
            self.reselect = False
            print("Capture cancelled.")
            return

        mon = monitor_under_cursor(sct)
        self.mon = mon
        frames = []
        end = time.perf_counter() + BURST_SECONDS
        while time.perf_counter() < end:
            t = time.perf_counter()
            frames.append(np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3]))
            time.sleep(max(0.0, 1 / BURST_FPS - (time.perf_counter() - t)))

        self.hidden = True
        shot = pick_frame(frames)
        del frames
        if shot is None:
            print("Selection cancelled.")
            return

        r = select_roi(shot, "1/3  Drag the SEARCH AREA, then ENTER")
        if not r:
            print("Selection cancelled.")
            self.hidden = False
            return
        sx, sy, sw, sh = r
        crop = shot[sy:sy + sh, sx:sx + sw].copy()

        o = select_roi(crop, "2/3  Drag tightly around the OBJECT, then ENTER")
        if not o:
            print("Selection cancelled.")
            self.hidden = False
            return
        ox, oy, ow, oh = o

        b = select_roi(crop, "3/3  Drag around the in-game BOX + ENTER  (or C for a virtual square)")

        box_tpl = box_mask = None
        if b:
            bx, by, bw, bh = b
            box_tpl = crop[by:by + bh, bx:bx + bw].copy()
            # ignore the part of the box image the fish was covering, so the box
            # still matches when the fish is somewhere else inside it
            box_mask = np.ones(box_tpl.shape, np.uint8)
            x0, x1 = max(ox - 4 - bx, 0), min(ox + ow + 4 - bx, bw)
            y0, y1 = max(oy - 4 - by, 0), min(oy + oh + 4 - by, bh)
            if x1 > x0 and y1 > y0:
                box_mask[y0:y1, x0:x1] = 0
            if box_mask.mean() < 0.3:  # fish covered most of it; masking would leave too little
                box_mask = None

        # Color model: see-through boxes tint the track, so find the box as the stretch of
        # track whose color is closer to "box color" than to "empty track color".
        box_colors = None
        if b:
            trim = bh // 6  # skip the box's top/bottom edges
            y0, y1 = by + trim, by + bh - trim
            lab = cv2.cvtColor(crop, cv2.COLOR_BGR2LAB).astype(np.float32)
            inside = lab[y0:y1, bx:bx + bw]
            if box_mask is not None:
                inside = inside[box_mask[trim:bh - trim, :, 0] > 0]
            inside = inside.reshape(-1, 3)
            outside = np.concatenate([lab[y0:y1, :bx].reshape(-1, 3),
                                      lab[y0:y1, bx + bw:].reshape(-1, 3)])
            if len(outside) >= 50 and len(inside) >= 50:
                bc, tc = np.median(inside, axis=0), np.median(outside, axis=0)
                if np.linalg.norm(bc - tc) >= MIN_COLOR_DIFF:
                    box_colors = (bc, tc, trim)
            if box_colors is None:
                print("Box color is too close to the track color; falling back to image matching.")

        new_cfg = {
            "search": (mon["left"] + sx, mon["top"] + sy, sw, sh),
            "obj": crop[oy:oy + oh, ox:ox + ow].copy(),
            "obj_y": oy,
            "box": box_tpl,
            "box_mask": box_mask,
            "box_colors": box_colors,
            "box_w": b[2] if b else VIRTUAL_BOX_WIDTH,
            "box_y": b[1] if b else 0,
            "box_h": b[3] if b else sh,
        }
        self.cfg = new_cfg
        self.state = None
        mode = ("in-game box (color)" if box_colors else "in-game box (image)") if b else "virtual square"
        print("Locked on. Mode:", mode, "| F8 to start/pause")
        save_selection(self.cfg, self.mon, self.excl_area, self.anchor, self.char)
        self.hidden = False

    def do_select_excl(self, sct):
        """F11: drag a box over the spot above your head where the '!' appears."""
        game = ctypes.windll.user32.GetForegroundWindow()
        try:
            self.hidden = True
            time.sleep(0.1)
            mon = monitor_under_cursor(sct)
            shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
            r = select_roi(shot, "Drag a box (a bit bigger than the !) over the spot above your head, then ENTER")
            if r:
                self.excl_area = (mon["left"] + r[0], mon["top"] + r[1], r[2], r[3])
                c = select_roi(shot, "Now drag snugly around YOUR CHARACTER, then ENTER  (C to skip)")
                if c:
                    self.char = make_character(shot, c, self.excl_area, mon)
                    print("'!' area set - it will follow your character.")
                else:
                    self.char = None
                    print("'!' area set (fixed spot - it won't follow your character).")
                save_selection(self.cfg, self.mon, self.excl_area, self.anchor, self.char)
            else:
                print("'!' area selection cancelled.")
        finally:
            self.hidden = False
            if game:
                ctypes.windll.user32.SetForegroundWindow(game)

    def do_set_anchor(self, sct):
        mon = self.game_mon(sct, cursor=True)
        shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
        self.anchor = make_anchor(shot, mon)
        log("Anchor set - I'll walk back here before each cast.")
        save_selection(self.cfg, self.mon, self.excl_area, self.anchor, self.char)

    def _hold_for(self, key, secs):
        """Hold key for secs; stops early (returns False) if paused or quitting."""
        self.hold(key)
        end = time.perf_counter() + secs
        while time.perf_counter() < end:
            if not self.active or self.quit:
                self.hold(None)
                return False
            time.sleep(0.02)
        self.hold(None)
        return True

    def wander(self):
        """Walk left (A) a random 2-4 s, jump, walk right (D) the same time, jump."""
        secs = random.uniform(*WANDER_SECONDS)
        log(f"Walking around: A {secs:.1f} s, jump, D {secs:.1f} s, jump")
        for key in ("a", "d"):
            if not (self._hold_for(key, secs) and self._hold_for(JUMP_KEY, 0.1)):
                break
            time.sleep(0.5)  # land before the next move
        self.hold(None)

    def go_to_anchor(self, sct):
        """Walk (A/D) in short steps until the scenery lines up with the anchor again."""
        if self.anchor is None or not ANCHOR_ENABLED:
            return
        end = time.perf_counter() + ANCHOR_MAX_TIME
        moved = False
        while time.perf_counter() < end and self.active and not self.quit:
            dx, conf = anchor_offset(sct, self.anchor)
            if conf < ANCHOR_MIN_MATCH:
                log(f"Anchor scenery not recognized (match {conf:.2f}) - not walking")
                return
            if abs(dx) <= ANCHOR_TOLERANCE:
                if moved:
                    log("Back at the anchor")
                return
            go_left = dx < 0  # anchor is to the left of the character -> walk left
            if ANCHOR_INVERT:
                go_left = not go_left
            if not moved:
                log(f"{abs(dx)} px from the anchor - walking {'left' if go_left else 'right'}")
            secs = min(0.3, max(0.03, 0.8 * abs(dx) / self.walk_speed))
            self.hold(LEFT_KEY if go_left else RIGHT_KEY)
            time.sleep(secs)
            self.hold(None)
            time.sleep(0.25)  # let the camera catch up
            moved = True
            dx2, conf2 = anchor_offset(sct, self.anchor)
            step = abs(dx - dx2)
            if conf2 >= ANCHOR_MIN_MATCH and step >= 4:  # learn the real walking speed
                self.walk_speed = 0.5 * self.walk_speed + 0.5 * step / secs
        if moved:
            log("Couldn't reach the anchor in time - casting anyway")

    def type_keys(self, keys):
        for k in keys:
            if not self.active or self.quit:
                break
            self.hold(k)
            time.sleep(MINE_KEY_HOLD)
            self.hold(None)
            time.sleep(MINE_KEY_GAP)

    def mining_step(self, sct):
        """Look for the ore menu; when it shows, type the arrows of the best row."""
        t = time.perf_counter()
        if not self.active:
            self.mine_wait, self.mine_pending, self.e_at = False, None, None
            self.hold(None)
            time.sleep(0.05)
            return
        mon = self.game_mon(sct)
        if (MINE_AUTO and not self.mine_wait and MINIMAP_RECT and CRYSTAL_ENABLED
                and t - self.crystal_checked > CRYSTAL_CHECK_EVERY):
            self.crystal_checked = t
            if self.crystal_visible(sct):
                self.hunt_crystal(sct, return_home=False)
                self.target, self.e_at = None, None
                return
        shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
        rows = find_mining_menu(shot)
        self.fps = 0.8 * self.fps + 0.2 / max(time.perf_counter() - t, 1e-3)
        if self.mine_wait:  # already answered this menu: wait until it closes
            if rows:
                self.mine_seen = t
                sig_now = tuple(tuple(a[4] for a in r["arrows"]) for r in rows)
                if t - self.mine_answered > 0.25 and _is_new_menu(sig_now, self.mine_answered_sig):
                    self.mine_wait, self.mine_pending = False, None  # a different menu: start over
                    return
                # mining frenzy: the menu stays open because ALL rows must be entered
                if t - self.mine_answered > FRENZY_WAIT:
                    left = [r for r in rows if all(abs(r["yc"] - y) > 0.5 * r["scale"] * 38 for y in self.mine_done_ys)]
                    if left:
                        row = min(left, key=lambda r: r["yc"])  # top to bottom
                        keys = [MINE_KEYS[a[4]] for a in row["arrows"]]
                        log(f"  frenzy - entering every row: next {' '.join(k.upper() for k in keys)}")
                        self.type_keys(keys)
                        self.mine_done_ys.append(row["yc"])
                        self.mine_seen = self.mine_answered = time.perf_counter()
                        return
            if t - self.mine_seen > 0.4 or t - self.mine_answered > MINE_RETRY_AFTER:
                self.mine_wait = False
                if self.after_mine:
                    self.after_mine = False
                    self.reveal_due = t + REVEAL_AFTER_MINE
            time.sleep(MINE_SCAN_EVERY)
            return
        self.hp_tick(sct)  # low HP -> veil
        if not rows:
            self.mine_pending = None
            self.buff_tick()  # every ~2 min: Y for the buff (no ore menu up)
            if MINE_AUTO:
                self.auto_mine_step(sct, shot, mon, t)
                if self.held or self.target or self.e_at is not None:
                    return  # on the move: look again right away
            else:
                self.passive_crystal(sct)  # manual: you pressed E at a crystal? solve its symbols
            time.sleep(MINE_SCAN_EVERY)
            return
        self.hold(None)  # menu is up: stop walking
        self.e_at, self.e_tries, self.target = None, 0, None
        # act only once the same menu shows on two looks in a row (fully drawn, not a flicker)
        sig = tuple(tuple(a[4] for a in r["arrows"]) for r in rows)
        if sig != self.mine_pending:
            self.mine_pending = sig
            time.sleep(MINE_SCAN_EVERY / 2)
            return
        self.mine_pending = None
        amounts = [read_amount(shot, r) for r in rows]
        best = max(range(len(rows)), key=lambda i: (amounts[i][0], -i))  # biggest amount, first on a tie
        menu = " | ".join(f"{txt}x " + " ".join(ARROW_KEY_NAMES[a[4]] + ("*" if a[5] else "") for a in r["arrows"])
                          for r, (_, txt) in zip(rows, amounts))
        keys = [MINE_KEYS[a[4]] for a in rows[best]["arrows"]]
        log(f"Ore menu: {menu}  ->  row {best + 1}: {' '.join(k.upper() for k in keys)}"
            + ("   (* = purple arrow: pressing the opposite)" if any(a[5] for r in rows for a in r["arrows"]) else ""))
        self.type_keys(keys)
        self.mine_done_ys = [rows[best]["yc"]]  # rows entered in this menu (a frenzy wants them all)
        self.mine_wait = True
        self.mine_answered_sig = sig
        self.mine_seen = self.mine_answered = time.perf_counter()
        self.patrol_len = PATROL_SWITCH
        self.after_mine = True  # mined one: reveal again (mouse 5) shortly after the menu closes

    def combat_step(self, sct):
        """Combat: hold both attacks down and run left / right, turning every COMBAT_RUN s.
        The buff (and veil) go off on their timer."""
        if not self.active:
            self.hold(None)
            time.sleep(0.05)
            return
        t = time.perf_counter()
        frac = self.hp_tick(sct)
        if self.healing:
            # invisible: stand still, no attacks, until HP is back up (or it's taking too long)
            self.hold(None)
            if frac is None or frac * 100 >= HP_RESUME or t - self.healing > 40:
                log(f"HP back to {frac * 100:.0f}% - fighting again" if frac is not None else "Back to fighting")
                self.healing = None
            else:
                self.buff_tick()
                time.sleep(0.2)
                return
        if MINIMAP_RECT and CRYSTAL_ENABLED and t - self.crystal_checked > CRYSTAL_CHECK_EVERY:
            self.crystal_checked = t
            if self.crystal_visible(sct):
                self.hold(None)  # let go of the attacks and the run
                self.hunt_crystal(sct, return_home=True)  # solve it, then back to where we fought
                self.hold(None)
                log("Back to fighting")
                return
        t = time.perf_counter()
        # attacks: held - except, if holding them stops us from moving, only in bursts between short runs
        attacking = True
        if self.cmb_lock:
            phase = (t - self.cmb_lock) % 1.8
            attacking = phase >= 1.0  # 1 s running with the attacks let go, then 0.8 s attacking
            if attacking != self.cmb_bursting:
                self.cmb_bursting = attacking
                self.cmb_track.clear()  # (movement is only judged while running)
                self.cmb_run_start = t - (0.0 if attacking else 0.6)
        if attacking:
            for name in (COMBAT_ATTACK_1, COMBAT_ATTACK_2):
                name = (name or "").strip().lower()
                if not name or name in self.mouse_held:
                    continue
                if name in MOUSE_BUTTONS:
                    mouse_ctl.press(MOUSE_BUTTONS[name])
                    self.mouse_held.add(name)
            for name in (COMBAT_ATTACK_1, COMBAT_ATTACK_2):  # an attack on a keyboard key: tap it often
                name = (name or "").strip().lower()
                if name and name not in MOUSE_BUTTONS and valid_key(name):
                    press(name, 0.03)
        else:
            for name in list(self.mouse_held):
                mouse_ctl.release(MOUSE_BUTTONS[name])
                self.mouse_held.discard(name)
        if t >= self.combat_turn_at:
            self.combat_turn(t)
        self.hold(COMBAT_RIGHT if self.combat_dir > 0 else COMBAT_LEFT)
        if not (self.cmb_lock and attacking):  # (standing still while attacking in bursts is fine)
            self.combat_watch_moving(sct, t)
        self.buff_tick()
        self.fps = 1.0 / 0.05
        time.sleep(0.05)

    def press_veil(self, why):
        """Veil (6): go invisible. Not more often than every VEIL_GAP s (it may be a toggle)."""
        t = time.perf_counter()
        if not valid_key(VEIL_KEY) or t - self.veil_at < VEIL_GAP:
            return False
        press(VEIL_KEY)
        self.veil_at = t
        log(f"Veil: pressed {VEIL_KEY.upper()} ({why})")
        return True

    def hp_tick(self, sct):
        """Look at the HP bar (a few times a second). Low -> veil; in combat also stop and heal.
        Returns the HP fraction (0..1) or None if the bar can't be seen."""
        t = time.perf_counter()
        if not (self.active and HP_SAFETY) or t - self.hp_checked < 0.4:
            return self.hp_frac
        self.hp_checked = t
        mon = self.game_mon(sct)
        try:
            if self.hp_bar is None or t - self.hp_bar_t > 30:  # find it (again) now and then
                region = {"left": mon["left"], "top": mon["top"] + int(mon["height"] * 0.9),
                          "width": mon["width"], "height": mon["height"] - int(mon["height"] * 0.9)}
                shot = np.ascontiguousarray(np.array(sct.grab(region))[:, :, :3])
                full = np.zeros((mon["height"], mon["width"], 3), np.uint8)
                full[int(mon["height"] * 0.9):] = shot
                bar = find_hp_bar(full)
                self.hp_bar_t = t
                if bar is not None:
                    x0, y0, y1, w = bar
                    old = self.hp_bar
                    self.hp_bar = (x0, y0, y1, max(w, old[3]) if old and abs(old[0] - x0) <= 4 else w)
            if self.hp_bar is None:
                self.hp_frac = None
                return None
            x0, y0, y1, full_w = self.hp_bar
            band = np.ascontiguousarray(np.array(sct.grab(
                {"left": mon["left"] + x0, "top": mon["top"] + y0, "width": full_w + 4, "height": max(2, y1 - y0)}))[:, :, :3])
            w = hp_fill(band)
            if w > full_w:  # bar fuller than we've seen: that's the real full width
                self.hp_bar = (x0, y0, y1, w)
                full_w = w
            self.hp_frac = w / max(1, full_w)
        except Exception:
            self.hp_frac = None
            return None
        if self.hp_frac * 100 < HP_LOW:
            if self.press_veil(f"HP low: {self.hp_frac * 100:.0f}%") and MODE == "combat" and not self.healing:
                self.healing = t
                log("  stopping the fight to heal up")
            elif MODE == "combat" and not self.healing:
                self.healing = t
        return self.hp_frac

    def combat_turn(self, t, why=None):
        self.combat_dir = -self.combat_dir
        self.combat_turn_at = t + max(0.2, float(COMBAT_RUN)) * random.uniform(0.85, 1.15)
        self.cmb_track.clear()
        self.cmb_run_start = t
        if why:
            log(why)

    def combat_watch_moving(self, sct, t):
        """Make sure the character really runs from side to side. Position from the minimap dot
        (or, without a minimap, from the scenery scrolling + the character's box on screen).
        Not moving while running -> a wall: turn around; stuck both ways -> holding the attacks
        must be stopping us: run with them let go, attacking in bursts in between."""
        if t - self.cmb_checked < 0.25:
            return
        self.cmb_checked = t
        pos = None
        if MINIMAP_RECT:
            d = self.read_mm(sct)["dot"]
            if d:
                pos, unit = d[0], 1.0  # minimap px
        if pos is None:
            mon = self.game_mon(sct)
            shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
            self.cmb_screen_x -= self.scene_shift(shot)  # the camera following us = we moved
            crect = self.character_rect(shot, mon, t, 0.0) if self.char is not None else None
            pos, unit = self.cmb_screen_x + (crect[0] if crect else 0.0), 25.0  # screen px
        self.cmb_track.append((t, pos))
        while self.cmb_track and t - self.cmb_track[0][0] > 1.0:
            self.cmb_track.popleft()
        if t - self.cmb_run_start < 1.0 or len(self.cmb_track) < 3:
            return  # (just turned / started: give it a moment)
        if self.cmb_lock and self.cmb_track[-1][0] - self.cmb_track[0][0] < 0.3:
            return
        span = max(p_ for _, p_ in self.cmb_track) - min(p_ for _, p_ in self.cmb_track)
        if span >= unit:
            self.cmb_stuck = 0
            return
        self.cmb_stuck += 1
        if self.cmb_stuck == 1:
            self.combat_turn(t, "Combat: not moving - a wall? turning around")
        elif not self.cmb_lock:
            self.cmb_lock = t
            self.cmb_stuck = 0
            self.combat_turn(t, "Combat: stuck both ways - holding the attacks seems to stop me running: "
                                "running with them let go, attacking in bursts")
        else:
            self.cmb_stuck = 0
            self.tap(JUMP_KEY, 0.15)  # still stuck: hop over whatever it is, and turn
            self.combat_turn(t, "Combat: still stuck - jumping and turning around")

    def buff_tick(self, wait=False):
        """Every BUFF_EVERY seconds press the buff key - only called when no minigame is up.
        The first press comes right after starting."""
        t = time.perf_counter()
        if not (self.active and BUFF_ENABLED):
            return
        if t - self.user_e_at < 6.0:
            return  # (manual) you just pressed E: a crystal's symbols may be up
        if self.veil_due is not None:
            if wait and t < self.veil_due:  # (between crystal moves: nothing held, just wait)
                time.sleep(self.veil_due - t)
                t = time.perf_counter()
            if t >= self.veil_due:
                self.veil_due = None
                if valid_key(VEIL_KEY) and t - self.veil_at >= VEIL_GAP:  # (not right after another veil)
                    press(VEIL_KEY)
                    self.veil_at = t
                    log(f"Veil: pressed {VEIL_KEY.upper()}")
            return
        if t < self.buff_due:
            return
        press(BUFF_KEY)
        self.buff_due = t + max(10.0, float(BUFF_EVERY))
        self.veil_due = t + VEIL_DELAY if VEIL_KEY else None
        log(f"Buff: pressed {BUFF_KEY.upper()} (next in {BUFF_EVERY:.0f} s)"
            + (f" - veil ({VEIL_KEY.upper()}) in {VEIL_DELAY:.0f} s" if VEIL_KEY else ""))

    def tap(self, key, secs=0.06):
        pydirectinput.keyDown(key)
        time.sleep(secs)
        pydirectinput.keyUp(key)

    def character_rect(self, shot, mon, t, shift=0.0):
        """Where the character is on screen (x, y, w, h), or None without a picked character.
        Searched for by shape; when unsure, the camera tells us: if the scenery scrolls, the
        camera is following and the character is at its usual left-right spot."""
        if self.char is None:
            return None
        if "pick" not in self.char:  # picked with an older version of the script
            if t - self.char_warned > 30:
                self.char_warned = t
                log("Please press 'Pick my character' again (needed by this version)")
            return None
        px, py, pw, ph = self.char["pick"]
        last = self.char_cache[1]
        left, top = (last[0], last[1]) if last else (px, py)
        # left-right: search a band at the character's height - near the last spot first,
        # the whole screen width only if it's not there
        band = (top - mon["top"] - ph // 2, top - mon["top"] + ph + ph // 2)
        lx = left - mon["left"]
        pos, conf = find_char_shape(shot, mon, self.char, lx - 3 * pw, band[0], lx + 4 * pw, band[1])
        if not (pos and conf >= CHAR_SURE_MATCH):  # not a strong match nearby: check everywhere too
            pos2, conf2 = find_char_shape(shot, mon, self.char, 0, band[0], shot.shape[1], band[1])
            if pos2 and conf2 > conf + 0.03:
                pos, conf = pos2, conf2
        # where the minimap says we must be: how far the dot moved, minus the camera scroll
        # (counted from the last time the character was clearly seen, so small errors don't pile up)
        self.scroll_since_seen += shift
        predicted = None
        if self.mm and self.mm_scale and self.seen_ref is not None:
            ref_left, ref_dot = self.seen_ref
            predicted = ref_left + self.mm_scale * (self.mm[0] - ref_dot) + self.scroll_since_seen
            if not (mon["left"] - pw <= predicted <= mon["left"] + mon["width"]):
                predicted, self.seen_ref = None, None  # off the screen: the estimate went wrong
        trusted = False
        if pos and conf >= CHAR_X_MATCH:
            if predicted is not None and abs(pos[0] - predicted) > max(2 * pw, 80) and conf < 0.9:
                left = predicted  # the search found something far from where the minimap says: a look-alike
                conf = 0.0
            else:
                left, trusted = pos[0], True
                if self.mm:
                    self.seen_ref, self.scroll_since_seen = (left, self.mm[0]), 0.0
        elif predicted is not None:
            left = predicted  # unsure: go by the minimap
        elif abs(shift) > 2:
            left = px  # unsure, but the scenery is scrolling: the camera is following, so we're at the usual spot
        # (otherwise: keep the last left-right spot)
        y, hconf = character_height(shot, mon, self.char, left)
        if trusted and y is not None and hconf >= CHAR_HEIGHT_MATCH:
            near = last is None or abs(y - top) <= ph * 0.6
            if near or hconf >= CHAR_JUMP_MATCH:  # a big jump in height needs a confident match
                top = y
        self.char_conf = (conf, hconf)
        rect = (left, top, pw, ph)
        self.char_cache = (t, rect)
        return rect

    def do_pick_minimap(self, sct):
        """Panel 'Pick minimap': screenshot, drag around the minimap's map area."""
        game = ctypes.windll.user32.GetForegroundWindow()
        try:
            self.hidden = True
            time.sleep(0.1)
            mon = self.game_mon(sct, cursor=True)
            shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
            r = select_roi(shot, "Drag around the MINIMAP's map (where the cyan dot is), then ENTER")
            if r:
                globals()["MINIMAP_RECT"] = [mon["left"] + r[0], mon["top"] + r[1], r[2], r[3]]
                self.mm_scale, self.mm_prev = None, None
                self.mm_sum_world = self.mm_sum_dot = 0.0
                info = minimap_info(shot, mon)
                log("Minimap picked - " + ("I can see your dot." if info else
                                           "but I can't see your cyan dot in it - try again?"))
                self.settings_dirty = True
            else:
                log("Pick minimap cancelled")
        finally:
            self.hidden = False
            if game:
                ctypes.windll.user32.SetForegroundWindow(game)

    def do_pick_char(self, sct):
        """Panel 'Pick my character': screenshot, drag around the character."""
        game = ctypes.windll.user32.GetForegroundWindow()
        try:
            self.hidden = True
            time.sleep(0.1)
            mon = self.game_mon(sct, cursor=True)
            shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
            r = select_roi(shot, "Drag around YOUR CHARACTER (hat to feet, a little margin is fine), then ENTER")
            if r:
                abs_rect = (mon["left"] + r[0], mon["top"] + r[1], r[2], r[3])
                self.char = make_character(shot, r, self.excl_area or abs_rect, mon)
                self.char_cache = (time.perf_counter(), abs_rect)
                self.mon = self.mon or mon
                save_selection(self.cfg, self.mon, self.excl_area, self.anchor, self.char)
                log("Character picked - I'll track it while mining.")
            else:
                log("Pick character cancelled")
        finally:
            self.hidden = False
            if game:
                ctypes.windll.user32.SetForegroundWindow(game)

    def walk(self, direction, shot, t, crect=None):
        """Walk left (-1) or right (+1). If neither the scenery scrolls nor the character
        moves on screen, we're stuck: jump once, and if still stuck, turn around."""
        if direction != self.walk_dir:
            self.walk_dir, self.dir_since = direction, t
            self.stuck_hist.clear()
        self.hold("d" if direction > 0 else "a")
        small = cv2.resize(cv2.cvtColor(shot, cv2.COLOR_BGR2GRAY), None, fx=1 / 8, fy=1 / 8,
                           interpolation=cv2.INTER_AREA).astype(np.float32)
        self.stuck_hist.append((t, small, crect[0] if crect else None))
        while self.stuck_hist and t - self.stuck_hist[0][0] > 1.0:
            self.stuck_hist.popleft()
        if t - self.dir_since < 1.0 or t - self.stuck_hist[0][0] < 0.7:
            return
        old_x = self.stuck_hist[0][2]
        if self.mm and self.mm_hist and t - self.mm_hist[0][0] >= 0.8:
            stuck = abs(self.mm[0] - self.mm_hist[0][1]) < 0.5  # the minimap dot isn't moving
        else:
            char_moved = crect is not None and old_x is not None and abs(crect[0] - old_x) > 8
            stuck = not char_moved and float(np.abs(small - self.stuck_hist[0][1]).mean()) < STUCK_DIFF
        if stuck:
            if t - self.jump_at > 2.5:
                log("Stuck - jumping")
                self.tap(JUMP_KEY, 0.1)
                self.jump_at = t
            else:
                log("Still stuck - turning around")
                self.patrol_dir = -direction
                self.skip_until = t + 1.5  # don't head straight back to an ore we can't reach
                self.hold(None)
                self.walk_dir, self.dir_since = 0, t
            self.stuck_hist.clear()

    def auto_mine_step(self, sct, shot, mon, t):
        """No menu on screen: keep ores revealed, walk to the nearest selected ore, press E."""
        if self.reveal_due is not None:  # just mined one: stand still, then reveal again
            self.hold(None)
            if t < self.reveal_due:
                return
            self.reveal_due, self.reveal_at = None, -1e9
        if t - self.reveal_at >= REVEAL_EVERY:
            self.hold(None)
            log(f"Revealing ores ({REVEAL_BUTTON})")
            press(REVEAL_BUTTON, 0.05)
            self.reveal_at = t
            time.sleep(0.3)
            return
        if self.e_at is not None:
            if t - self.e_at < E_WAIT:  # pressed E: give the menu time to open
                return
            self.e_at = None
        shift = self.scene_shift(shot)
        self.mm = minimap_info(shot, mon)
        if self.mm and self.mm_prev and (abs(self.mm[0] - self.mm_prev[0]) > 25
                                         or abs(self.mm[2] - self.mm_prev[2]) > 6 or abs(self.mm[3] - self.mm_prev[3]) > 6):
            # a different area (or a teleport): its minimap has another scale - measure again
            self.mm_scale, self.seen_ref, self.scroll_since_seen = None, None, 0.0
            self.mm_sum_world = self.mm_sum_dot = 0.0
            self.mm_hist.clear()
        if self.mm:
            self.mm_hist.append((t, self.mm[0]))
            while self.mm_hist and t - self.mm_hist[0][0] > 1.2:
                self.mm_hist.popleft()
        if self.target:  # the camera scrolled: the remembered ore moved on screen with the scenery
            self.target = (self.target[0] + shift,) + self.target[1:]
        ores = find_ores(shot) if t >= self.skip_until else []
        crect = self.character_rect(shot, mon, t, shift)
        self.mine_vis = {"char": crect, "ore": None}
        self.learn_speed(t, shift, crect)
        if ores and crect:
            # only ores on the character's level: ones up on ledges / down below can't be walked to
            feet = crect[1] + crect[3]
            level = [o for o in ores if -ORE_LEVEL_ABOVE <= (mon["top"] + o[1]) - feet <= ORE_LEVEL_BELOW
                     or (self.target and t - self.target[1] < 1.5 and abs(mon["left"] + o[0] - self.target[0]) < 60)]
            if len(level) < len(ores) and t - self.level_warned > 10:
                self.level_warned = t
                o = min((o for o in ores if o not in level), key=lambda o: abs((mon["top"] + o[1]) - feet))
                dy = (mon["top"] + o[1]) - feet
                log(f"{o[3]} seen {abs(dy):.0f} px {'above' if dy < 0 else 'below'} my level - "
                    f"can't walk to it, looking for ones on my level")
            ores = level
        if ores:
            if crect is None and self.char is not None:
                self.hold(None)  # can't see the character: don't walk blind
                if t - self.char_warned > 3:
                    self.char_warned = t
                    log("Can't find my character on screen - re-pick it on the panel if this keeps happening")
                return
            cx = crect[0] + crect[2] / 2 if crect else mon["left"] + mon["width"] / 2
            ox, oy, v, name = min(ores, key=lambda o: abs(mon["left"] + o[0] - cx))
            dx = mon["left"] + ox - cx
            self.mine_vis["ore"] = (mon["left"] + ox, mon["top"] + oy)
            self.dir_since = t  # an ore is in view: don't turn around
            self.target = (mon["left"] + ox, t, name)  # remember it, in case the character covers it
            self.approach(dx, name, shot, t, crect)
            return
        # The ore dropped out of view (the character is probably covering it, or it flickered):
        # keep going for where it was last seen instead of wandering off.
        if self.target and crect and t - self.target[1] < 1.2:
            tx, _, name = self.target
            self.approach(tx - (crect[0] + crect[2] / 2), name, shot, t, crect)  # under the character: we're on it
            return
        if self.mm and self.walk_dir != 0:
            dot_x, _, end_l, end_r = self.mm
            if (self.patrol_dir > 0 and dot_x >= end_r - 2) or (self.patrol_dir < 0 and dot_x <= end_l + 2):
                log("End of the area (minimap) - turning around")
                self.patrol_dir = -self.patrol_dir
                self.walk_dir = 0
                self.hold(None)
                return
        if self.walk_dir == 0:  # just starting to patrol
            self.dir_since = t
        elif t - self.dir_since > self.patrol_len:
            # sweep back and forth, each sweep longer than the last, so new ground gets covered
            self.patrol_len = min(self.patrol_len * 1.6, 90.0)
            log(f"No ore this way - turning around (next sweep {self.patrol_len:.0f} s)")
            self.patrol_dir = -self.patrol_dir
            self.walk_dir = 0
            self.hold(None)
            return
        self.walk(self.patrol_dir, shot, t, crect)

    def learn_speed(self, t, shift, crect):
        """Learn how fast the character walks (px/s) and how long one look takes. Walking moves
        the scenery (camera following) and/or the character on screen; both count."""
        if self.last_look is not None:
            dt = t - self.last_look
            if 0 < dt < 1.0:
                self.look_time = 0.7 * self.look_time + 0.3 * dt
                cx = crect[0] + crect[2] / 2 if crect else None
                steady = (self.char_conf[0] >= CHAR_X_MATCH and cx is not None and self.last_cx is not None
                          and abs(cx - self.last_cx) < (self.char["pick"][2] if self.char else 150))
                if self.walking_since_look and steady:
                    moved = abs(shift) + abs(cx - self.last_cx)
                    if 3 < moved and moved / dt < 2500:
                        self.walk_speed_px = min(3000.0, max(50.0, 0.7 * self.walk_speed_px + 0.3 * moved / dt))
                if steady and self.mm and self.mm_prev:
                    dmm = self.mm[0] - self.mm_prev[0]
                    world = (cx - self.last_cx) - shift  # how far we really walked, in screen px
                    if (dmm > 0) == (world > 0) and abs(world) > 2:
                        # total distance walked / total dot distance: rounding averages out
                        self.mm_sum_world += abs(world)
                        self.mm_sum_dot += abs(dmm)
                        if self.mm_sum_dot >= 6:
                            self.mm_scale = self.mm_sum_world / self.mm_sum_dot
        self.last_look = t
        self.last_cx = crect[0] + crect[2] / 2 if crect else None
        self.walking_since_look = self.held in ("a", "d")
        self.mm_prev = self.mm

    def approach(self, dx, name, shot, t, crect):
        """Get onto the ore: walk while far, let go early enough to not overshoot (the
        character keeps walking during a look), then taps sized to the distance left."""
        if YELLOW_DIAGNOSTICS and t - self.diag_at > 1.0:
            self.diag_at = t
            cx = crect[0] + crect[2] / 2 if crect else None
            xc, hc = self.char_conf
            log(f"  approach: character x={cx:.0f} feet y={crect[1] + crect[3] if crect else '?'} "
                f"(match x {xc:.2f}, height {hc:.2f}) | ore x={cx + dx:.0f} | {dx:+.0f} px to go | "
                f"speed {self.walk_speed_px:.0f} px/s, look {self.look_time * 1000:.0f} ms"
                + (f" | minimap dot x={self.mm[0]:.0f}" + (f", {self.mm_scale:.0f} px per map px" if self.mm_scale else "")
                   if self.mm else ""))
        if abs(dx) <= ORE_ON_PX:
            self.approach_last = None
            self.press_e(name, t)
            return
        # how far we'd travel during one look if we kept holding the key
        coast = self.walk_speed_px * self.look_time * 1.3
        if abs(dx) > coast + 3 * ORE_ON_PX:
            self.approach_last = None
            self.walk(1 if dx > 0 else -1, shot, t, crect)
            return
        # close: taps. If the last tap overshot, make taps smaller; if it fell well short, bigger.
        if self.approach_last is not None:
            if (dx > 0) != (self.approach_last > 0):
                self.tap_gain = max(0.15, self.tap_gain * 0.6)
            elif abs(dx) > 0.6 * abs(self.approach_last):
                self.tap_gain = min(1.5, self.tap_gain * 1.25)
        self.approach_last = dx
        self.hold(None)
        secs = min(0.25, max(0.02, abs(dx) / self.walk_speed_px * self.tap_gain))
        self.tap("d" if dx > 0 else "a", secs)

    def scene_shift(self, shot):
        """How many px the scenery moved sideways since the last look (camera scrolling)."""
        g = cv2.resize(cv2.cvtColor(shot, cv2.COLOR_BGR2GRAY), None, fx=0.25, fy=0.25,
                       interpolation=cv2.INTER_AREA).astype(np.float32)
        prev, self.prev_scene = self.prev_scene, g
        if prev is None or prev.shape != g.shape:
            return 0.0
        if self.hann is None or self.hann.shape != g.shape:
            self.hann = cv2.createHanningWindow((g.shape[1], g.shape[0]), cv2.CV_32F)
        (dx, dy), response = cv2.phaseCorrelate(prev, g, self.hann)
        return dx * 4 if response > 0.05 else 0.0

    def press_e(self, name, t):
        """Standing on an ore: press E (up to 3 times, then give up on it)."""
        self.hold(None)
        if self.e_tries >= 3:
            log(f"Can't open this {name} - moving on")
            self.e_tries, self.skip_until, self.target = 0, t + 4.0, None
            return
        time.sleep(0.15)
        log(f"On the {name} - pressing E")
        self.tap("e")
        self.e_at, self.e_tries = time.perf_counter(), self.e_tries + 1

    def do_add_ore(self, sct):
        """Panel 'Add ore': screenshot, drag around an ore, save it to the ores folder."""
        game = ctypes.windll.user32.GetForegroundWindow()
        try:
            self.hidden = True
            time.sleep(0.1)
            mon = monitor_under_cursor(sct)
            shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
            r = select_roi(shot, "Drag snugly around ONE ore, then ENTER")
            if r:
                x, y, w, h = r
                ORES_DIR.mkdir(exist_ok=True)
                n = 1
                while (ORES_DIR / f"ore_{n}.png").exists():
                    n += 1
                ok, buf = cv2.imencode(".png", shot[y:y + h, x:x + w])
                (ORES_DIR / f"ore_{n}.png").write_bytes(buf.tobytes())
                load_ores()
                for o in ORE_LIST:
                    if o["name"] == f"ore_{n}":
                        o["scale"] = 1.0  # grabbed from the screen: exact size
                log(f"Added ore_{n} - rename the file in the ores folder to give it a nicer name")
            else:
                log("Add ore cancelled")
        finally:
            self.hidden = False
            if game:
                ctypes.windll.user32.SetForegroundWindow(game)

    # --- darkness crystal: get there over the platforms using the minimap ---
    def read_mm(self, sct):
        x, y, w, h = MINIMAP_RECT
        img = np.ascontiguousarray(np.array(sct.grab({"left": int(x), "top": int(y),
                                                      "width": int(w), "height": int(h)}))[:, :, :3])
        info = parse_minimap(img)
        if info["dot"]:
            self.mm_last_dot = info["dot"]
        if info["crystal"]:
            self.mm_last_crystal = info["crystal"]
        return info

    def crystal_visible(self, sct):
        if not (CRYSTAL_ENABLED and MINIMAP_RECT):
            return False
        try:
            return self.read_mm(sct)["crystal"] is not None
        except Exception:
            return False

    def crystal_on_screen(self, sct):
        mon = self.game_mon(sct)
        return find_crystal_sprite_xy(np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])) is not None

    def crystal_gone(self, sct, secs=1.5):
        """The purple dot has to stay gone for a while (it can blink, or hide under our own dot),
        and the crystal mustn't be on screen any more either."""
        end = time.perf_counter() + secs
        while time.perf_counter() < end:
            if self.read_mm(sct)["crystal"] is not None:
                return False
            time.sleep(0.1)
        mon = self.game_mon(sct)
        shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
        return find_crystal_sprite_xy(shot) is None

    def double_jump(self, sct=None):
        """Two full-height jumps: hold Space while rising, let go at the top, then the second
        jump the same way. The minimap dot tells when the top is reached."""
        if sct is None or not MINIMAP_RECT:
            for _ in range(2):  # no minimap: fixed timing, held long enough for a full jump
                pydirectinput.keyDown(JUMP_KEY)
                time.sleep(JUMP_HOLD)
                pydirectinput.keyUp(JUMP_KEY)
                time.sleep(0.03)
            return
        self.jump_trace = []
        for _ in range(2):
            pydirectinput.keyDown(JUMP_KEY)
            start = time.perf_counter()
            top, last_rise = None, None
            while time.perf_counter() - start < JUMP_HOLD_MAX and self.active and not self.quit:
                d = self.read_mm(sct)["dot"]
                now = time.perf_counter()
                if d:
                    self.jump_trace.append(d[2])
                    if top is None:
                        top = d[2]
                    elif d[2] < top - 0.2:  # still going up
                        top, last_rise = d[2], now
                    # the dot moves in whole minimap pixels, so it can sit still for a moment
                    # while rising: only call it the top after it hasn't risen for a little while
                    elif last_rise is not None and now - last_rise >= JUMP_TOP_WAIT:
                        break
                time.sleep(0.01)
            pydirectinput.keyUp(JUMP_KEY)
            time.sleep(0.03)

    def mm_landed(self, sct, timeout=2.5):
        """Wait until the dot stops moving up and down. Returns the last minimap reading."""
        info, last, still = None, None, 0
        end = time.perf_counter() + timeout
        while time.perf_counter() < end and self.active and not self.quit:
            info = self.read_mm(sct)
            d = info["dot"]
            still = still + 1 if (d and last is not None and abs(d[2] - last) < 0.3) else 0
            if still >= 6:
                break
            last = d[2] if d else last
            time.sleep(0.025)
        return info

    def mm_walk_to(self, sct, x_target, timeout=15.0, careful=False):
        """Walk until the minimap dot is at x_target (map px). careful: small taps only (walking up
        to the crystal), so we don't run off the end of a small platform. Near a platform's end
        it always switches to taps."""
        end = time.perf_counter() + timeout
        prev, hidden_since = None, None
        last_key, flips = None, 0
        best_dist, best_at = None, time.perf_counter()  # blocked (no progress) -> give up early
        while time.perf_counter() < end and self.active and not self.quit:
            info = self.read_mm(sct)
            d = info["dot"]
            now = time.perf_counter()
            if d is None:  # dot hidden (e.g. under the crystal's square)
                self.hold(None)
                hidden_since = hidden_since or now
                if now - hidden_since > 0.5:
                    return False
                time.sleep(0.05)
                continue
            hidden_since = None
            if prev and self.held in ("a", "d") and now - prev[0] > 0.02:  # learn map walking speed
                v = abs(d[0] - prev[1]) / (now - prev[0])
                if 1 < v < 200:
                    self.mm_speed = 0.8 * self.mm_speed + 0.2 * v
            prev = (now, d[0])
            dx = x_target - d[0]
            if abs(dx) <= (1.25 if careful else 0.75):
                self.hold(None)
                return True
            if best_dist is None or abs(dx) < best_dist - 0.5:
                best_dist, best_at = abs(dx), now
            elif now - best_at > (3.0 if careful else 1.5):
                self.hold(None)
                return False  # not getting any closer: something's in the way
            key = "d" if dx > 0 else "a"
            if careful and abs(dx) <= 6:
                if last_key and key != last_key:
                    flips += 1
                    if flips >= 3:  # overshooting back and forth: close enough
                        self.hold(None)
                        return True
                last_key = key
            near_edge = False
            segs_ = platform_tops(info["terrain"])
            on = segment_under(segs_, d[0], d[2])
            if on is not None:
                _, ex0, ex1 = segs_[on]
                near_edge = (dx > 0 and ex1 - d[0] <= EDGE_CAREFUL) or (dx < 0 and d[0] - ex0 <= EDGE_CAREFUL)
            if (careful and abs(dx) <= 6) or near_edge:
                self.hold(None)
                self.tap(key, min(0.06, max(0.025, 0.5 * abs(dx) / max(self.mm_speed, 1.0))))
                time.sleep(0.12)
                prev = None
                continue
            if abs(dx) > 3:
                self.hold(key)
            else:
                self.hold(None)
                self.tap(key, min(0.12, max(0.03, 0.8 * abs(dx) / max(self.mm_speed, 1.0))))
                time.sleep(0.05)
                prev = None
            time.sleep(0.01)
        self.hold(None)
        return False

    def mm_onto(self, sct, seg, d, timeout):
        """Hold toward seg until the dot is over it (a few px in), then let go and wait to land."""
        by, bx0, bx1 = seg
        inside = min(bx0 + 3, (bx0 + bx1) / 2) if d > 0 else max(bx1 - 3, (bx0 + bx1) / 2)
        self.hold("d" if d > 0 else "a")
        end = time.perf_counter() + timeout
        while time.perf_counter() < end and self.active and not self.quit:
            dot = self.read_mm(sct)["dot"]
            if dot and ((d > 0 and dot[0] >= inside) or (d < 0 and dot[0] <= inside)):
                break
            time.sleep(0.01)
        self.hold(None)
        return self.mm_landed(sct)

    def mm_climb(self, sct, segs, to, d):
        """Standing beside a higher platform: double jump, and once above its top, move onto it."""
        global JUMP_RISE
        by = segs[to][0]
        info = self.read_mm(sct)
        start = info["dot"][2] if info["dot"] else None
        self.double_jump(sct)
        lowest, above = start, False
        end = time.perf_counter() + 1.5
        while time.perf_counter() < end and self.active and not self.quit:
            dot = self.read_mm(sct)["dot"]
            if dot:
                lowest = min(lowest, dot[2]) if lowest is not None else dot[2]
                if dot[2] <= by - 0.5:
                    above = True
                    break
                if lowest is not None and dot[2] > lowest + 1.5:  # already falling, never got high enough
                    break
            time.sleep(0.008)
        if start is not None and lowest is not None and start - lowest > JUMP_RISE:
            JUMP_RISE = start - lowest  # jumped higher than we thought
            self.settings_dirty = True
        if start is not None and lowest is not None:
            log(f"  jump rose {start - lowest:.0f} minimap px (this climb needed {start - by:.0f})")
        if not above:
            if start is not None and lowest is not None and self.jump_capped:
                # a full jump with room overhead that still fell short: now we know the real height
                info2 = self.read_mm(sct)
                if info2["dot"] and headroom(info2["terrain"], info2["dot"][0], start) > start - lowest + 2:
                    JUMP_RISE, self.jump_capped = start - lowest, False
                    self.settings_dirty = True
                    log(f"  my double jump is {JUMP_RISE:.0f} minimap px high")
            self.mm_landed(sct)
            return False
        self.mm_onto(sct, segs[to], d, 1.5)
        return True

    def mm_dash(self, sct, segs, to, d):
        """Standing under a platform: hold W and press the dash key (R) - the character
        dashes up onto it. The dash needs DASH_COOLDOWN seconds between uses."""
        wait = self.dash_at + DASH_COOLDOWN + 0.1 - time.perf_counter()
        if wait > 0:
            time.sleep(wait)
        self.hold(None)
        info = self.mm_landed(sct, 1.0)
        start = info["dot"][2] if info and info["dot"] else None
        by = segs[to][0]
        pydirectinput.keyDown("w")
        try:
            time.sleep(0.06)
            press(DASH_KEY, 0.05)
            self.dash_at = time.perf_counter()
            end = time.perf_counter() + 1.2
            while time.perf_counter() < end and self.active and not self.quit:
                dot = self.read_mm(sct)["dot"]
                if dot and dot[2] <= by + 0.5 and time.perf_counter() - self.dash_at > 0.15:
                    break
                time.sleep(0.01)
            time.sleep(0.1)
        finally:
            pydirectinput.keyUp("w")
        after = self.mm_landed(sct)
        if after and after["dot"] and start is not None:
            log(f"  dashed up {start - after['dot'][2]:.0f} minimap px (platform was {start - by:.0f} up)")
        return True

    def mm_step_over(self, sct, segs, to, d):
        """Walk onto the surface right beside this one (a slope or a small step)."""
        by, bx0, bx1 = segs[to]
        return self.mm_walk_to(sct, min(bx0 + 2, bx1) if d > 0 else max(bx1 - 2, bx0), timeout=4.0)

    def mm_drop(self, sct, segs, to, d):
        """Walk off the edge toward the lower platform."""
        info = self.read_mm(sct)
        start = info["dot"][2] if info["dot"] else 0
        self.hold("d" if d > 0 else "a")
        end = time.perf_counter() + 4.0
        while time.perf_counter() < end and self.active and not self.quit:
            dot = self.read_mm(sct)["dot"]
            if dot and dot[2] > start + 1.5:  # falling
                break
            time.sleep(0.01)
        time.sleep(0.06)  # a little more push so we clear the edge
        self.hold(None)
        self.mm_landed(sct)
        return True

    def mm_leap(self, sct, segs, to, d):
        """Jump across a gap from this platform's edge."""
        self.hold("d" if d > 0 else "a")
        self.double_jump(sct)
        return self.mm_onto(sct, segs[to], d, 2.0) is not None

    def test_jump_now(self, sct):
        """Panel 'Test jump': double jump where we stand and log what the minimap dot did."""
        if not MINIMAP_RECT:
            log("Test jump: pick the minimap first")
            return
        was_active, self.active = self.active, True  # (works while paused too)
        info = self.mm_landed(sct, 1.5)
        if not info or not info["dot"]:
            self.active = was_active
            log("Test jump: can't see my dot on the minimap")
            return
        start = info["dot"][2]
        try:
            self.double_jump(sct)
            lowest, end = start, time.perf_counter() + 1.2
            while time.perf_counter() < end:
                d = self.read_mm(sct)["dot"]
                if d:
                    lowest = min(lowest, d[2])
                    self.jump_trace.append(d[2])
                time.sleep(0.02)
        finally:
            self.active = was_active
        heights = [round(start - v) for v in self.jump_trace[::3]]
        log(f"Test jump: rose {start - lowest:.0f} minimap px | room above me: "
            f"{headroom(info['terrain'], info['dot'][0], start):.0f} px | height over time: {heights}")

    def calibrate_jump(self, sct):
        """Measure how high a double jump goes (minimap px), jumping where there's open sky above."""
        global JUMP_RISE
        info = self.mm_landed(sct, 1.5)
        if not info or not info["dot"]:
            return
        dot, terrain = info["dot"], info["terrain"]
        segs = platform_tops(terrain)
        here = segment_under(segs, dot[0], dot[2])
        room = 0
        if here is not None:  # walk to the spot on this platform with the most room overhead
            _, x0, x1 = segs[here]
            best_x, room = dot[0], headroom(terrain, dot[0], dot[2])
            for x in range(int(x0) + 3, int(x1) - 2):
                r = headroom(terrain, x, dot[2])
                if r > room + 1 or (r >= room - 1 and r >= 30 and abs(x - dot[0]) < abs(best_x - dot[0])):
                    best_x, room = x, r
            if abs(best_x - dot[0]) > 1:
                self.mm_walk_to(sct, best_x)
                info = self.mm_landed(sct, 1.0)
                if not info or not info["dot"]:
                    return
        start = lowest = info["dot"][2]
        self.double_jump(sct)
        end = time.perf_counter() + 1.6
        while time.perf_counter() < end:
            dot = self.read_mm(sct)["dot"]
            if dot:
                lowest = min(lowest, dot[2])
            time.sleep(0.008)
        self.mm_landed(sct)
        rise = start - lowest
        if rise >= 2:
            JUMP_RISE = rise
            self.settings_dirty = True
            capped = bool(room and rise >= room - 1.5)
            self.jump_capped = capped
            log(f"  measured my double jump: {rise:.0f} minimap px high"
                + (" (hit a ceiling - it may go higher; I'll learn more while climbing)" if capped else ""))
        else:
            log("  couldn't measure the double jump (no room above?)")

    def mm_go(self, sct, target):
        """Get to target over the platforms: "crystal" (and press E there) or (map x, feet y)."""
        end = time.perf_counter() + CRYSTAL_TIMEOUT
        banned, fails, e_tries, last_plan = set(), {}, 0, None
        last_fail, cool_waits = -1e9, 0  # when the last wrong sequence was typed; extra cooldown waits
        forced_up = None  # set when the screen shows the crystal higher than the minimap suggested
        hidden_since = None  # when our dot went missing from the minimap
        ghosts, air_at = [], None  # ledges the minimap doesn't draw (roofs...); 'still in the air' check
        goal_override = None  # the crystal's platform, when the minimap shows we're above it
        while time.perf_counter() < end and self.active and not self.quit:
            self.buff_tick(wait=True)  # (between moves - never while a minigame is up)
            self.hp_tick(sct)
            if target == "crystal" and time.perf_counter() - (self.hunt_vis or {}).get("t", -1e9) > 0.3:
                self.screen_track(sct)  # character + crystal on screen (overlay, final approach)
            info = self.read_mm(sct)
            dot = info["dot"]
            if dot is None:
                last, c = self.mm_last_dot, info["crystal"]
                hidden_since = hidden_since or time.perf_counter()
                if target == "crystal" and c and (
                        (last and abs(last[0] - c[0]) < 6 and abs(last[2] - c[2]) < 4)
                        or time.perf_counter() - hidden_since > 1.0):
                    # the crystal's square covers our dot: we're on it (a dash can land us
                    # there in one go, so the last place we saw the dot may be far away)
                    dot = (c[0], c[1], c[2])
                else:
                    time.sleep(0.1)
                    continue
            else:
                hidden_since = None
            if target == "crystal":
                if info["crystal"] is None:
                    lc, ld = self.mm_last_crystal, dot
                    if lc and ld and abs(lc[0] - ld[0]) <= 7 and abs(lc[2] - ld[2]) <= 9 and self.crystal_on_screen(sct):
                        info["crystal"] = lc  # our dot is covering its square, but it's on screen: still there
                    elif self.crystal_gone(sct):
                        return True
                    else:
                        continue
                tx, tfeet = info["crystal"][0], info["crystal"][2]
            else:
                tx, tfeet = target
            segs = platform_tops(info["terrain"]) + ghosts
            here = segment_under(segs, dot[0], dot[2])
            if here is None:
                # in the air - or standing on something the minimap doesn't draw (a roof, scenery):
                # if the dot stays put, use that spot as a little ledge and plan from it
                now_ = time.perf_counter()
                if air_at is None or abs(dot[2] - air_at[1]) > 0.6 or abs(dot[0] - air_at[2]) > 1.5:
                    air_at = (now_, dot[2], dot[0])
                    self.mm_landed(sct, 0.8)
                    continue
                if now_ - air_at[0] < 1.2:
                    time.sleep(0.1)
                    continue
                log("  standing on something the minimap doesn't show - treating it as a ledge")
                ghosts.append((int(round(dot[2])), int(dot[0]) - 3, int(dot[0]) + 3))
                air_at = None
                continue
            air_at = None
            goal = segment_under(segs, tx, tfeet)
            if goal is None and target == "crystal":
                # the crystal's square can cover the end of its platform on the minimap:
                # take the platform right under it, even if it seems to stop a few px short
                near = [i for i, (y, x0, x1) in enumerate(segs) if tfeet - 1.5 <= y <= tfeet + 6 and x0 - 8 <= tx <= x1 + 8]
                if near:
                    goal = min(near, key=lambda i: segs[i][0] - tfeet)
            if goal is None:
                goal = landing_segment(segs, tx, tfeet - 2)
            if forced_up is not None:  # the screen showed the crystal above us earlier
                # ...but only a platform near the crystal's height on the minimap, never way above it
                above = [i for i, (y, x0, x1) in enumerate(segs)
                         if tfeet - 6 <= y <= forced_up and x0 - 8 <= tx <= x1 + 8]
                if above:
                    goal = max(above, key=lambda i: segs[i][0])
            if goal_override is not None:
                gy_, gx0_, gx1_ = goal_override
                same = [i for i, (y, x0, x1) in enumerate(segs) if abs(y - gy_) <= 1 and x0 <= gx1_ and x1 >= gx0_]
                if same:
                    goal = same[0]
            if goal is None:
                log("  can't tell which platform that's on")
                return False
            if here == goal:
                # stay on the platform: aim a little in from its ends, and creep there in taps
                gy, gx0, gx1 = segs[goal]
                aim = min(max(tx, gx0 + 2), gx1 - 2) if gx1 - gx0 > 4 else (gx0 + gx1) / 2
                if abs(dot[0] - aim) > 1.5 and not self.mm_walk_to(sct, aim, careful=target == "crystal"):
                    continue
                if target != "crystal":
                    return True
                now_dot = self.read_mm(sct)["dot"]
                if now_dot and now_dot[2] < tfeet - 4:
                    # the minimap shows us clearly ABOVE the crystal: don't press E up here
                    log(f"  I'm above the crystal on the minimap (my feet {now_dot[2]:.0f}, crystal {tfeet:.0f}) - going down")
                    forced_up = None
                    lower = [i for i, (y, x0, x1) in enumerate(segs)
                             if i != here and y > segs[here][0] + 1 and tfeet - 2 <= y <= tfeet + 6 and x0 - 8 <= tx <= x1 + 8]
                    if lower:
                        goal_override = segs[min(lower, key=lambda i: abs(segs[i][0] - tfeet))]
                    continue
                # 2. check on screen: is the crystal really on our level, or up on a platform?
                # (only matters if the minimap has a platform just above us near the crystal's height)
                if forced_up is None and self.crystal_above_me(sct):
                    cand = [i for i, (y, x0, x1) in enumerate(segs)
                            if tfeet - 6 <= y < segs[here][0] - 1 and x0 - 8 <= tx <= x1 + 8]
                    if cand:
                        forced_up = segs[here][0] - 3
                        log("  the crystal is up on a platform above me - dashing up to it")
                        continue
                self.line_up_with_crystal(sct)  # the minimap is too coarse for the last few steps
                crect_, cxy_, dx_, dy_ = self.screen_track(sct)
                if dx_ is not None and abs(dx_) > max(25.0, crect_[2] / 2 + 10) * 2.5 and e_tries < 4:
                    # on screen the crystal is still well to one side: not close enough for E yet
                    log(f"  on screen the crystal is still {abs(dx_):.0f} px to the {'right' if dx_ > 0 else 'left'} - getting closer")
                    e_tries += 1
                    continue
                if e_tries and self.mm_last_dot and abs(self.mm_last_dot[0] - tx) > 0.5:
                    # E didn't work yet: shuffle a little closer (our dot may be hidden under the crystal)
                    self.tap("d" if tx > self.mm_last_dot[0] else "a", 0.04)
                    time.sleep(0.15)
                played = self.crystal_minigame(sct)  # press E; solve the symbol panel if it opens
                e_tries += 1
                if not played and time.perf_counter() - last_fail < 120 and cool_waits < 12:
                    # no panel right after a wrong try: the crystal's cooldown isn't over yet
                    # (it gets longer after each failure) - wait, and don't count this one
                    e_tries -= 1
                    cool_waits += 1
                    log("  still on cooldown - waiting a bit longer")
                    t_cool = time.perf_counter() + 6.0
                    while time.perf_counter() < t_cool and self.active and not self.quit:
                        time.sleep(0.2)
                    end += 6.0
                    continue
                time.sleep(0.7)
                if self.crystal_gone(sct):
                    if played:
                        self.learn_crystal()
                    return True
                if played:  # wrong sequence: the crystal won't open again for a while
                    last_fail = time.perf_counter()
                    log(f"  the crystal is still there - waiting out its cooldown ({CRYSTAL_COOLDOWN:.0f} s)")
                    end_wait = time.perf_counter() + CRYSTAL_COOLDOWN
                    while time.perf_counter() < end_wait and self.active and not self.quit:
                        time.sleep(0.2)
                    end += CRYSTAL_COOLDOWN  # don't count the wait against the time limit
                if e_tries >= 6:
                    log("  pressed E at the crystal 6 times - giving up")
                    return False
                continue
            # where we are on the map -> which platforms to drop / dash to
            terrain_ = info["terrain"]
            if ghosts:  # ledges the minimap doesn't draw are solid too (walls when walking off an end)
                terrain_ = terrain_.copy()
                for gy, gx0, gx1 in ghosts:
                    terrain_[gy:gy + 3, max(0, gx0):gx1 + 1] = True
            route = plan_route(terrain_, segs, here, dot[0], goal, None, banned)
            if not route:
                log("  no way there that I can see (no platform to dash up from?)")
                return False
            kind, stand, d, to = route[0]
            if route != last_plan:
                log(f"  route: " + " -> ".join(
                    (f"dash up at x={sx} to height {segs[t][0]}" if k == "dash" else
                     f"walk {'right' if dd > 0 else 'left'} onto height {segs[t][0]}" if k == "walk" else
                     f"drop off the {'right' if dd > 0 else 'left'} end to height {segs[t][0]}")
                    for k, sx, dd, t in route))
                last_plan = route
            at_end = kind == "drop" and ((d > 0 and dot[0] >= stand - 1.5) or (d < 0 and dot[0] <= stand + 1.5))
            if not at_end and not self.mm_walk_to(sct, stand, careful=kind == "dash" and abs(dot[0] - stand) <= 4):
                key = (here, to, kind)
                fails[key] = fails.get(key, 0) + 1
                if fails[key] >= 2:
                    banned.add(key)
                    log(f"  can't get to the spot for that {kind} - trying another way")
                continue
            ok = {"dash": self.mm_dash, "drop": self.mm_drop, "walk": self.mm_step_over,
                  "climb": self.mm_climb, "leap": self.mm_leap}[kind](sct, segs, to, d)
            after = self.read_mm(sct)
            now_on = segment_under(platform_tops(after["terrain"]), *(after["dot"][0], after["dot"][2])) \
                if after["dot"] else None
            if not ok or now_on != to:
                key = (here, to, kind)
                fails[key] = fails.get(key, 0) + 1
                if fails[key] >= 2:
                    banned.add(key)  # this jump keeps failing: find another way
                    log(f"  that {kind} keeps failing - trying another way")
        self.hold(None)
        return False

    def screen_track(self, sct):
        """On screen: the character's box and the crystal's spot -> (crect, crystal_xy, dx, dy).
        dx / dy = crystal minus character centre, in screen px (None when either isn't seen).
        Also kept for the overlay (cyan box = me, purple circle = crystal)."""
        if self.char is None or "pick" not in self.char:
            return None, None, None, None
        mon = self.game_mon(sct)
        shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
        t = time.perf_counter()
        crect = self.character_rect(shot, mon, t, self.scene_shift(shot))
        spot = find_crystal_sprite_xy(shot)
        cxy = (mon["left"] + spot[0], mon["top"] + spot[1]) if spot else None
        self.hunt_vis = {"char": crect, "crystal": cxy, "t": t}
        if crect is None or cxy is None:
            return crect, cxy, None, None
        return crect, cxy, cxy[0] - (crect[0] + crect[2] / 2), cxy[1] - (crect[1] + crect[3] / 2)

    def crystal_above_me(self, sct):
        """On screen: is the crystal sprite clearly higher than the character (another floor)?"""
        if self.char is None or "pick" not in self.char:
            return False
        crect, cxy, dx, dy = self.screen_track(sct)
        if dx is None:
            return False
        return cxy[1] < crect[1] - 0.6 * crect[3]

    def line_up_with_crystal(self, sct, timeout=4.0):
        """Walk the last bit onto the crystal. On screen (character box vs crystal) when both can
        be seen - more precise than the minimap; the minimap when not. Standing on the crystal
        hides most of it, so its visible bit can jump around: stop when the taps start going back
        and forth, and never tap toward a platform's end when we're close to it.
        Returns True when we're on it (or as close as it gets)."""
        mon = self.game_mon(sct)
        end = time.perf_counter() + timeout
        last_dir, flips, taps = 0, 0, 0
        while time.perf_counter() < end and self.active and not self.quit and taps < 12:
            crect, cxy, dx, dy = self.screen_track(sct)
            mm = self.read_mm(sct)
            if dx is None:  # can't see both on screen: go by the minimap
                if mm["dot"] and mm["crystal"] and abs(mm["dot"][0] - mm["crystal"][0]) <= 1.5:
                    return True
                if mm["dot"] is None and mm["crystal"] is not None:
                    return True  # our dot is hidden under the crystal's square: we're on it
                return False
            reach = max(25.0, crect[2] / 2 + 10)  # the crystal overlaps the character: that's on it
            if abs(dx) <= reach:
                return True
            step = 1 if dx > 0 else -1
            if last_dir and step != last_dir:
                flips += 1
                if flips >= 2:
                    return True  # going back and forth: we're as close as it gets
            last_dir = step
            d = mm["dot"]
            if d:
                segs_ = platform_tops(mm["terrain"])
                on = segment_under(segs_, d[0], d[2])
                if on is not None:
                    _, ex0, ex1 = segs_[on]
                    if (step > 0 and ex1 - d[0] <= 2) or (step < 0 and d[0] - ex0 <= 2):
                        return True  # one more step would be off the edge
            taps += 1
            self.tap("d" if dx > 0 else "a", min(0.07, max(0.025, abs(dx) / max(self.walk_speed_px, 100) * 0.5)))
            time.sleep(0.15)
        return False

    def passive_crystal(self, sct):
        """Manual modes: for a few seconds after YOU press E, look for a crystal's symbols next to
        the crystal on screen; once two readings agree, type them."""
        t = time.perf_counter()
        mon = self.game_mon(sct)
        if t - self.user_e_at > 5.0:  # not pressed E lately: keep a picture of the normal screen
            if t - self.pc_bg_t >= 0.5 and t - self.user_e_at > 6.0:
                self.pc_bg = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
                self.pc_bg_t = t
            return
        if t < self.pc_block or t - self.pc_last < 0.3:
            return
        self.pc_last = t
        shot = np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
        near = find_crystal_sprite_xy(shot)
        before = self.pc_bg if self.pc_bg is not None and self.pc_bg.shape == shot.shape else None
        if near is None and before is None:
            return
        reading = [d for d, _ in find_crystal_symbols(shot, near, before)]
        if not reading or reading != self.pc_prev:
            self.pc_prev = reading or None
            return
        log(f"Crystal minigame: {len(reading)} symbols -> " + " ".join(f"{d}({MINE_KEYS[d].upper()})" for d in reading))
        for d in reading:
            if not self.active or self.quit:
                break
            self.hold(MINE_KEYS[d])
            time.sleep(MINE_KEY_HOLD)
            self.hold(None)
            time.sleep(MINE_KEY_GAP)
        self.pc_prev, self.pc_block, self.user_e_at = None, t + 3.0, -1e9

    def crystal_minigame(self, sct):
        """Press E at the crystal, read the symbols that appear (white, next to the crystal),
        type their directions (W A S D). Returns True if a minigame was played."""
        mon = self.game_mon(sct)
        grab = lambda: np.ascontiguousarray(np.array(sct.grab(mon))[:, :, :3])
        before = grab()
        near = find_crystal_sprite_xy(before)  # None if it's hidden behind us: then the new symbols are looked for
        self.tap("e")
        # the game says "take your time": wait until two readings in a row agree
        reading, symbols, shot, end = None, [], None, time.perf_counter() + 3.0
        while time.perf_counter() < end and self.active and not self.quit:
            time.sleep(0.3)
            shot = grab()
            symbols = find_crystal_symbols(shot, near, before, detail=True)
            now_reading = [s_[0] for s_ in symbols]
            if now_reading and now_reading == reading:
                break
            reading = now_reading
        self.save_crystal_debug(before, shot, [s_[1] for s_ in symbols])
        if not symbols:
            log("  pressed E at the crystal but saw no minigame symbols")
            return False
        seq = self.crystal_guess(symbols)
        keys = [MINE_KEYS[d] for d in seq]
        log(f"Crystal minigame: {len(symbols)} symbols -> " + " ".join(f"{d}({MINE_KEYS[d].upper()})" for d in seq)
            + ("" if seq == [s_[0] for s_ in symbols] else "  (trying my 2nd guesses this time)"))
        for k in keys:
            if not self.active or self.quit:
                break
            self.hold(k)
            time.sleep(MINE_KEY_HOLD)
            self.hold(None)
            time.sleep(MINE_KEY_GAP)
        time.sleep(1.0)
        return True

    def crystal_guess(self, symbols):
        """The directions to type. The same crystal keeps its symbols when you try again, and
        the game only says right/wrong at the end - so after a failed try, swap the guesses
        the reading was least sure about (cheapest swaps first)."""
        n = len(symbols)
        mem = self.crys_mem
        same = (mem is not None and mem["n"] == n and time.perf_counter() - mem["t"] <= 300
                and all(a is not None and b_ is not None and _ncc(a, b_) >= 0.6
                        for a, b_ in zip(mem.get("squares", []), [_symbol_square(s_[3]) for s_ in symbols])))
        if not same:
            mem = self.crys_mem = {"n": n, "tried": [], "t": 0.0,
                                   "squares": [_symbol_square(s_[3]) for s_ in symbols]}
        mem["t"] = time.perf_counter()
        cands = [([s_[2][i][0] for i in range(4)], [s_[2][0][1] - s_[2][i][1] for i in range(4)]) for s_ in symbols]
        options = [([0] * n, 0.0)]
        for i in range(n):  # one symbol on its 2nd / 3rd choice
            for k in (1, 2):
                c = [0] * n
                c[i] = k
                options.append((c, cands[i][1][k]))
        for i in range(n):  # two symbols on their 2nd choice
            for j in range(i + 1, n):
                c = [0] * n
                c[i] = c[j] = 1
                options.append((c, cands[i][1][1] + cands[j][1][1]))
        options.sort(key=lambda o: o[1])
        for c, _ in options:
            seq = [cands[i][0][c[i]] for i in range(n)]
            if seq not in mem["tried"]:
                break
        mem["tried"].append(seq)
        mem["masks"] = [s_[3] for s_ in symbols]
        mem["last"] = seq
        return seq

    def learn_crystal(self):
        """The last sequence opened the crystal: keep its symbols as reference drawings (with
        the right directions), so this drawing style is read right next time."""
        global _crystal_refs
        mem = self.crys_mem
        if not mem or "last" not in mem:
            return
        try:
            if _crystal_refs is None:
                _crystal_refs = load_crystal_refs()
            learned = list(CRYSTAL_SYMBOLS_DIR.glob("*_learned_*.png"))
            saved = 0
            for m, d in zip(mem["masks"], mem["last"]):
                sq = _symbol_square(m)
                if sq is None or len(learned) + saved >= 80:
                    continue
                if any(rd == d and _ncc(sq, r) >= 0.85 for rd, _, r in _crystal_refs):
                    continue  # already know this one well
                ys, xs = np.where(m)
                ok, buf = cv2.imencode(".png", m[ys.min():ys.max() + 1, xs.min():xs.max() + 1].astype(np.uint8) * 255)
                (CRYSTAL_SYMBOLS_DIR / f"{d}_learned_{time.strftime('%m%d%H%M%S')}_{saved}.png").write_bytes(buf.tobytes())
                saved += 1
            if saved:
                _crystal_refs = None  # reload with the new ones
                log(f"  learned {saved} new symbol drawing(s) from this crystal")
        except Exception:
            pass
        self.crys_mem = None

    def save_crystal_debug(self, before, shot, panel):
        """Keep the last 3 crystal minigames (before E / what was read) for checking. Small JPGs."""
        if not CRYSTAL_DEBUG or shot is None:
            return
        try:
            folder = Path(__file__).with_name("debug_crystal")
            folder.mkdir(exist_ok=True)
            self.crystal_dbg_n = (getattr(self, "crystal_dbg_n", -1) + 1) % 3
            marked = shot.copy()
            for x, y, w, h in (panel or []):
                cv2.rectangle(marked, (int(x), int(y)), (int(x + w), int(y + h)), (0, 255, 255), 3)
            for name, img in (("before_E", before), ("read", marked)):
                small = cv2.resize(img, None, fx=0.5, fy=0.5, interpolation=cv2.INTER_AREA)
                ok, buf = cv2.imencode(".jpg", small, [cv2.IMWRITE_JPEG_QUALITY, 80])
                (folder / f"crystal_{self.crystal_dbg_n}_{name}.jpg").write_bytes(buf.tobytes())
            if panel:
                xs0 = max(0, int(min(b_[0] for b_ in panel)) - 250)
                ys0 = max(0, int(min(b_[1] for b_ in panel)) - 60)
                xs1 = int(max(b_[0] + b_[2] for b_ in panel)) + 250
                ys1 = int(max(b_[1] + b_[3] for b_ in panel)) + 60
                for name, img in (("panel", shot), ("panel_before", before)):
                    ok, buf = cv2.imencode(".png", img[ys0:ys1, xs0:xs1])
                    (folder / f"crystal_{self.crystal_dbg_n}_{name}.png").write_bytes(buf.tobytes())
            log(f"  (saved what I saw to debug_crystal/crystal_{self.crystal_dbg_n}_*.jpg)")
        except Exception:
            pass

    def hunt_crystal(self, sct, return_home):
        """A darkness crystal showed up: go press E on it; optionally come back afterwards."""
        self.hold(None)
        info = self.read_mm(sct)
        home = info["dot"]
        log("Darkness crystal on the minimap! Going for it")
        if CRYSTAL_VEIL:
            self.press_veil("darkness crystal spotted")
        got = self.mm_go(sct, "crystal")
        log("Got the darkness crystal" if got else "Couldn't reach the darkness crystal")
        if return_home and home and self.active and not self.quit:
            log("Walking back to where I was")
            self.mm_go(sct, (home[0], home[2]))
        self.hold(None)


    # --- main loop (worker thread) ---
    def run(self):
        """Keeps the loop alive: on any error, release keys, log it, and restart."""
        errors = 0
        while not self.quit:
            try:
                self._loop()
            except Exception:
                errors += 1
                try:
                    self.hold(None)
                except Exception:
                    pass
                if errors <= 3 or errors % 20 == 0:
                    traceback.print_exc()
                log(f"Loop error #{errors} - recovering in 1 s")
                time.sleep(1.0)

    def _loop(self):
        sct = MSS()
        prev_t = prev_obj = prev_box = None
        box_x = box_weak_since = gone_since = check_until = None
        last_diag = 0.0
        excl_armed, clear_since = False, None
        excl_hist = deque()  # (time, yellow px) in the '!' area, last ~1 s
        seen = False
        v_obj = v_box = 0.0
        last_progress = time.perf_counter()  # last time anything happened (watchdog)
        frame_errors = consecutive = 0

        next_wander = time.perf_counter() + WANDER_EVERY
        last_char_look = last_char_warn = 0.0
        screen_hist = deque()  # (time, ['!' marks]) over the last 1.5 s, whole-screen mode
        new_streak = 0

        def cast(reason):
            """Run END_SEQUENCE (A, D, cast) and start watching for the '!'."""
            nonlocal prev_t, check_until, excl_armed, clear_since, last_progress, next_wander, new_streak
            steps = [(FISH_BUTTON if k == "mouse4" else k, secs) for k, secs in END_SEQUENCE]
            steps = [(k, secs) for k, secs in steps if not (self.manual and k != FISH_BUTTON)]
            log(f"{reason} -> " + ", ".join(k.upper() for k, _ in steps))
            anchored = False
            for k, secs in steps:
                if k == FISH_BUTTON:
                    self.hold(None)
                    if self.manual:
                        pass  # manual mode: just cast, no walking around or back to the anchor
                    elif WANDER_ENABLED and WANDER_EVERY > 0 and time.perf_counter() >= next_wander:
                        self.wander()  # every ~minute: walk around and jump, then cast
                        next_wander = time.perf_counter() + WANDER_EVERY + random.uniform(-WANDER_JITTER, WANDER_JITTER)
                    if not anchored and not self.manual:  # stand on the anchor before casting
                        self.go_to_anchor(sct)
                        anchored = True
                    press(k, secs)
                else:
                    self.hold(k)
                    time.sleep(secs)
            self.hold(None)
            prev_t = None  # skip the time spent in the sequence
            check_until = time.perf_counter() + CHECK_TIMEOUT
            excl_armed, clear_since = False, None
            excl_hist.clear()
            screen_hist.clear()
            new_streak = 0
            last_progress = time.perf_counter()

        try:
            while not self.quit:
                try:
                    if self.test_jump:
                        self.test_jump = False
                        self.hold(None)
                        self.test_jump_now(sct)
                        continue
                    if self.pick_minimap:
                        self.pick_minimap = False
                        self.hold(None)
                        self.do_pick_minimap(sct)
                        continue
                    if self.pick_char:
                        self.pick_char = False
                        self.hold(None)
                        self.do_pick_char(sct)
                        continue
                    if self.add_ore:
                        self.add_ore = False
                        self.hold(None)
                        self.do_add_ore(sct)
                        continue
                    if self.set_anchor:
                        self.set_anchor = False
                        self.do_set_anchor(sct)
                        continue
                    if self.select_excl:
                        self.select_excl = False
                        self.do_select_excl(sct)
                        continue
                    if self.reselect:
                        self.reselect = False
                        self.active = False
                        self.hold(None)
                        self.do_select(sct)
                        prev_t = box_x = box_weak_since = gone_since = check_until = None
                        seen = False
                        v_obj = v_box = 0.0
                        continue

                    if MODE == "mining":
                        self.mining_step(sct)
                        continue
                    if MODE == "combat":
                        self.combat_step(sct)
                        continue
                    if self.cfg is None:
                        time.sleep(0.05)
                        continue

                    t0 = time.perf_counter()
                    if self.active:
                        self.hp_tick(sct)  # low HP -> veil
                    if self.active and not seen:
                        self.buff_tick()  # every ~2 min: Y for the buff (not during the fish minigame)
                    if self.active and self.manual and not seen:
                        self.passive_crystal(sct)  # manual: you pressed E at a crystal? solve its symbols
                    if (self.active and not self.manual and not seen and MINIMAP_RECT and CRYSTAL_ENABLED
                            and t0 - self.crystal_checked > CRYSTAL_CHECK_EVERY):
                        self.crystal_checked = t0
                        if self.crystal_visible(sct):
                            self.hunt_crystal(sct, return_home=True)
                            cast("Back from the crystal")
                            continue
                    cfg = self.cfg
                    frame = grab_area(sct, cfg["search"])
                    ox, o_score = match(frame, cfg["obj"])
                    sx, sy, sw, sh = cfg["search"]
                    ow = cfg["obj"].shape[1]
                    obj_cx = ox + ow / 2

                    dt = max(t0 - prev_t, 1e-3) if prev_t is not None else 0.0
                    if cfg["box_colors"] is not None:
                        fish_rect = (int(ox), cfg["obj_y"], ow, cfg["obj"].shape[0])
                        bx, b_score = find_box_by_brightness(frame, cfg["box_y"], cfg["box_h"],
                                                             cfg["box_w"], fish_rect)
                        if b_score >= BOX_MIN_CONTRAST:
                            box_x, box_weak_since = bx, None
                        else:
                            box_weak_since = box_weak_since or t0
                            box_x = bx if box_x is None else box_x
                        bx = box_x
                        box_lost = box_weak_since is not None and t0 - box_weak_since > 0.3
                    elif cfg["box"] is not None:
                        # search near where the box was; it can't teleport between frames
                        near = None if box_weak_since and t0 - box_weak_since > 0.3 else box_x
                        bx, b_score = match(frame, cfg["box"], cfg["box_mask"],
                                            near, BOX_SEARCH_RADIUS)
                        if b_score >= MATCH_THRESHOLD or box_x is None:
                            box_x = bx
                            box_weak_since = None
                        else:
                            # poor match (fish covering it, etc.): coast on the last position
                            box_weak_since = box_weak_since or t0
                            box_x = box_x + v_box * dt
                        bx = box_x
                        box_lost = box_weak_since is not None and t0 - box_weak_since > 0.5
                    else:
                        bx, b_score, box_lost = (sw - cfg["box_w"]) / 2, 1.0, False
                    box_cx = bx + cfg["box_w"] / 2

                    # smoothed velocities for prediction
                    if prev_t is not None:
                        v_obj = 0.6 * v_obj + 0.4 * (obj_cx - prev_obj) / dt
                        v_box = 0.6 * v_box + 0.4 * (box_cx - prev_box) / dt
                    prev_t, prev_obj, prev_box = t0, obj_cx, box_cx

                    lost = o_score < MATCH_THRESHOLD or box_lost
                    key = None
                    if not lost:
                        # aim where the fish will be, and account for the box's momentum
                        err = (obj_cx + v_obj * self.lead) - (box_cx + v_box * self.lead)
                        # small errors -> short taps, big errors -> key held down
                        duty = min(1.0, max(0.0, (abs(err) - DEADZONE_PX) / FULL_PRESS_PX))
                        phase = (t0 % TAP_PERIOD) / TAP_PERIOD
                        if duty >= 1.0 or phase < duty:
                            go_right = err > 0
                            if INVERT:
                                go_right = not go_right
                            key = RIGHT_KEY if go_right else LEFT_KEY
                    self.hold(key if self.active else None)

                    # minigame ended: fish gone for GONE_DELAY after having been seen
                    if o_score >= MATCH_THRESHOLD:
                        seen, gone_since = True, None
                        last_progress = t0
                    else:
                        gone_since = gone_since or t0
                        if seen and t0 - gone_since >= GONE_DELAY:
                            seen = False
                            if self.active:
                                cast("Minigame ended")

                    # after the end sequence, watch for the yellow '!'
                    if check_until is not None:
                        if o_score >= 0.8 or not self.active:
                            check_until = None  # minigame came back, or paused
                            self.yellow_px = None
                        elif time.perf_counter() > check_until:
                            self.yellow_px = None
                            cast(f"No '!' within {CHECK_TIMEOUT:.0f} s")
                        elif WATCH_WHOLE_SCREEN and (self.mon is not None or GAME_MONITOR):
                            # whole-screen mode: click when a NEW '!' mark shows up anywhere.
                            # Marks that were already there half a second ago (signs, icons) don't count.
                            wmon = self.game_mon(sct)
                            shot = np.ascontiguousarray(np.array(sct.grab(wmon))[:, :, :3])
                            marks = find_exclamations(shot)
                            screen_hist.append((t0, marks))
                            while screen_hist and t0 - screen_hist[0][0] > 1.5:
                                screen_hist.popleft()
                            warmed = t0 - screen_hist[0][0] >= 0.5
                            older = [m for t_, ms in screen_hist if t0 - t_ >= 0.5 for m in ms]
                            new = [m for m in marks
                                   if all(abs(m[0] - o[0]) > 20 or abs(m[1] - o[1]) > 20 for o in older)]
                            new_streak = new_streak + 1 if (warmed and new) else 0
                            self.yellow_px, self.yellow_goal = (max(m[2] for m in new) if new else 0), CHECK_MIN_PIXELS
                            if new_streak >= 2:  # seen in 2 frames in a row: not a flicker
                                mx, my, ma = max(new, key=lambda m: m[2])
                                log(f"Yellow ! at ({wmon['left'] + mx}, {wmon['top'] + my}), "
                                    f"{ma} px -> {FISH_BUTTON.upper()}")
                                press(FISH_BUTTON, 0.05)
                                last_progress = time.perf_counter()
                                check_until = None
                                self.yellow_px = None
                                new_streak = 0
                        elif self.excl_area is not None:
                            # '!' area mode: click when yellow suddenly appears above your head
                            if self.char is not None and t0 - last_char_look >= CHAR_TRACK_EVERY:
                                last_char_look = t0
                                chx, chy, chconf = find_character(sct, self.char)
                                if chconf >= CHAR_MIN_MATCH:
                                    ox_, oy_ = self.char["offset"]
                                    new_area = (chx + ox_, chy + oy_) + tuple(self.char["size"])
                                    dist = max(abs(new_area[0] - self.excl_area[0]), abs(new_area[1] - self.excl_area[1]))
                                    # only follow real moves (not idle-animation jitter), and don't let a so-so
                                    # match (another player, look-alike) drag the area across the screen
                                    if dist > CHAR_MOVE_PX and (dist <= CHAR_MAX_JUMP or chconf >= 0.7):
                                        self.excl_area = new_area
                                        excl_hist.clear()  # new spot: relearn what's normally there
                                        if YELLOW_DIAGNOSTICS:
                                            log(f"  '!' area follows your character -> ({new_area[0]}, {new_area[1]}), match {chconf:.2f}")
                                elif YELLOW_DIAGNOSTICS and t0 - last_char_warn > 5:
                                    last_char_warn = t0
                                    log(f"  character not recognized (match {chconf:.2f}) - '!' area stays where it is")
                            ex, ey, ew, eh = self.excl_area
                            eframe = np.ascontiguousarray(
                                np.array(sct.grab({"left": ex, "top": ey, "width": ew, "height": eh}))[:, :, :3])
                            raw, blobs = yellow_blobs(eframe)
                            shape = max((a for w, h, a in blobs if is_exclamation(w, h, a)), default=0)
                            # trigger 2 ("!" shape) needs the area to be free of a "!" shape for a moment first
                            if shape < CHECK_MIN_PIXELS:
                                clear_since = clear_since or t0
                                if t0 - clear_since >= CLEAR_BEFORE_WATCH:
                                    excl_armed = True
                            else:
                                clear_since = None
                            while excl_hist and t0 - excl_hist[0][0] > 1.0:
                                excl_hist.popleft()
                            warmed = bool(excl_hist) and t0 - excl_hist[0][0] >= 0.3
                            base = min(v for _, v in excl_hist) if excl_hist else raw
                            self.yellow_px, self.yellow_goal = max(0, raw - base), EXCL_JUMP_PX
                            if YELLOW_DIAGNOSTICS and (raw - base >= 20 or shape) and t0 - last_diag > 0.3:
                                last_diag = t0
                                big = sorted(blobs, key=lambda b: -b[2])[:3]
                                print(f"  '!' area: {raw} yellow px (was {base}) | '!' shape {shape} px | blobs: "
                                      + (", ".join(f"{w}x{h} {a}" for w, h, a in big) or "none"))
                            jump_hit = warmed and raw - base >= EXCL_JUMP_PX     # trigger 1: yellow suddenly appeared
                            shape_hit = excl_armed and shape >= CHECK_MIN_PIXELS  # trigger 2: a "!"-shaped mark appeared
                            if jump_hit or shape_hit:
                                why = f"+{raw - base} px yellow" if jump_hit else f"'!' shape {shape} px"
                                log(f"Yellow ! above head ({why}) -> {FISH_BUTTON.upper()}")
                                press(FISH_BUTTON, 0.05)
                                last_progress = time.perf_counter()
                                check_until = None
                                self.yellow_px = None
                            else:
                                excl_hist.append((t0, raw))
                        else:
                            self.yellow_px, self.yellow_goal = count_yellow(frame), CHECK_MIN_PIXELS
                            if YELLOW_DIAGNOSTICS and t0 - last_diag > 0.5:
                                raw, blobs = yellow_blobs(frame)
                                if raw >= CHECK_MIN_PIXELS:
                                    last_diag = t0
                                    big = sorted(blobs, key=lambda b: -b[2])[:4]
                                    print(f"  yellow seen: {raw} px raw | thick blobs (w x h, px): "
                                          + (", ".join(f"{w}x{h} {a}" for w, h, a in big) or "none")
                                          + f" | '!' score {self.yellow_px}/{CHECK_MIN_PIXELS}"
                                          + ("" if excl_armed else " (ignored: waiting for screen to clear)"))
                            # yellow already on screen when the minigame ends (catch popup, x2...)
                            # doesn't count: the area must be clear first, then a NEW '!' triggers
                            if not excl_armed:
                                if self.yellow_px < CHECK_MIN_PIXELS:
                                    clear_since = clear_since or t0
                                    if t0 - clear_since >= CLEAR_BEFORE_WATCH:
                                        excl_armed = True
                                        print("  screen clear - watching for the '!'")
                                else:
                                    clear_since = None
                            elif self.yellow_px >= CHECK_MIN_PIXELS:
                                log(f"Yellow ! ({self.yellow_px} px) -> {FISH_BUTTON.upper()}")
                                press(FISH_BUTTON, 0.05)
                                last_progress = time.perf_counter()
                                check_until = None
                                self.yellow_px = None

                    # watchdog: ACTIVE but no minigame, no '!' wait, nothing for a while -> cast again
                    if not self.active:
                        last_progress = t0
                        next_wander = max(next_wander, t0 + WANDER_EVERY)  # paused: restart the minute
                    elif check_until is None and not seen and t0 - last_progress > IDLE_RECAST:
                        cast(f"Nothing happened for {IDLE_RECAST:.0f} s")

                    self.state = {
                        "obj": (sx + ox, sy + cfg["obj_y"], ow, cfg["obj"].shape[0]),
                        "box": (sx + bx, sy + cfg["box_y"], cfg["box_w"], cfg["box_h"]),
                        "lost": lost,
                        "scores": (o_score, b_score),
                    }

                    elapsed = time.perf_counter() - t0
                    time.sleep(max(0.0, 1 / MAX_FPS - elapsed))
                    self.fps = 0.9 * self.fps + 0.1 / max(time.perf_counter() - t0, 1e-4)
                except Exception:
                    # one bad frame (screenshot failed, window changed...) shouldn't stop anything
                    frame_errors += 1
                    consecutive += 1
                    if consecutive >= 3:
                        self.hold(None)  # don't leave A/D held while blind
                    if frame_errors <= 2 or frame_errors % 100 == 0:
                        traceback.print_exc()
                        log(f"Frame error #{frame_errors} - skipping the frame and carrying on")
                    if consecutive % 10 == 0:
                        sct = MSS()  # fresh screen-capture handle
                    time.sleep(0.02)
                else:
                    consecutive = 0
        finally:
            self.hold(None)


def make_overlay(tracker):
    # overlay spans every monitor; the game can be on any of them
    with MSS() as s:
        mon = s.monitors[0]
        primary = monitor_at(s, 0, 0)
    ml, mt = mon["left"], mon["top"]

    user32 = ctypes.windll.user32
    prev_focus = user32.GetForegroundWindow()

    root = tk.Tk()
    root.overrideredirect(True)
    root.attributes("-topmost", True)
    root.attributes("-transparentcolor", "#ff00ff")
    root.geometry(f'{mon["width"]}x{mon["height"]}+{ml}+{mt}')
    canvas = tk.Canvas(root, bg="#ff00ff", highlightthickness=0)
    canvas.pack(fill="both", expand=True)
    root.update()

    # click-through, no taskbar entry, and hidden from screen capture
    hwnd = user32.GetParent(root.winfo_id()) or root.winfo_id()
    ex = user32.GetWindowLongW(hwnd, -20)
    user32.SetWindowLongW(hwnd, -20, ex | 0x80000 | 0x20 | 0x80 | 0x08000000)
    # a disabled window can never take keyboard focus, so keys keep going to the game
    user32.EnableWindow(hwnd, False)
    if prev_focus:
        user32.SetForegroundWindow(prev_focus)
    excluded = bool(user32.SetWindowDisplayAffinity(hwnd, 0x11))  # WDA_EXCLUDEFROMCAPTURE
    if not excluded:
        print("Note: overlay can't be hidden from capture; drawing markers outside the search area.")

    def rect(x, y, w, h, color, width=2):
        canvas.create_rectangle(x - ml, y - mt, x + w - ml, y + h - mt, outline=color, width=width)

    def draw():
        if tracker.quit:
            root.destroy()
            return
        canvas.delete("all")
        if not tracker.hidden:
            if tracker.armed:
                status = "ARMED - click in the game to show the image   (F9 again to cancel)"
            elif tracker.cfg is None:
                status = "No target - press F9 to select   |   F10 quit"
            else:
                mode = ("ACTIVE" if tracker.active else "PAUSED") + (" MANUAL" if tracker.manual else "")
                status = (f"{mode}  holding: {(tracker.held or '-').upper()}  "
                          f"lead {tracker.lead:.2f}  {tracker.fps:.0f} fps"
                          + (f"  [waiting for !  {tracker.yellow_px}/{tracker.yellow_goal}]"
                             if tracker.yellow_px is not None else "")
                          + "   |   "
                          f"F8 start/pause  F6/F7 lead -/+  F4 manual  F5 anchor  F9 reselect  F11 ! area  F10 quit")
            smon = tracker.mon or primary
            canvas.create_text(smon["left"] - ml + 12, smon["top"] - mt + 12, anchor="nw",text=status, fill="#00ff00",
                               font=("Consolas", 12, "bold"))

            if tracker.excl_area is not None and not WATCH_WHOLE_SCREEN:  # area unused in whole-screen mode
                ex, ey, ew, eh = tracker.excl_area
                rect(ex - 3, ey - 3, ew + 6, eh + 6, "#ffd000")
            cfg, st = (tracker.cfg if MODE == "fishing" else None), tracker.state
            if cfg is not None:
                sx, sy, sw, sh = cfg["search"]
                rect(sx - 3, sy - 3, sw + 6, sh + 6, "#3399ff")
                if st is not None:
                    bx, by, bw, bh = st["box"]
                    ox, oy, ow, oh = st["obj"]
                    box_col = "#888888" if st["lost"] else "#00ff00"
                    if excluded:
                        rect(bx, by, bw, bh, box_col)
                        rect(ox, oy, ow, oh, "#ff3333")
                    else:  # markers above/below the search area so they don't confuse matching
                        rect(bx, sy - 14, bw, 8, box_col)
                        rect(ox, sy + sh + 6, ow, 8, "#ff3333")
                    if st["lost"]:
                        canvas.create_text(sx - ml, sy - mt - 20, anchor="sw", fill="#ff3333",
                                           font=("Consolas", 11, "bold"),
                                           text="LOST obj=%.2f box=%.2f" % st["scores"])
            hv = tracker.hunt_vis
            if hv and time.perf_counter() - hv["t"] < 1.0:  # crystal hunt: me + the crystal on screen
                if hv.get("char"):
                    cx_, cy_, cw_, ch_ = hv["char"]
                    rect(cx_, cy_, cw_, ch_, "#22d3ee")
                if hv.get("crystal"):
                    kx, ky = hv["crystal"]
                    canvas.create_oval(kx - 22 - ml, ky - 22 - mt, kx + 22 - ml, ky + 22 - mt, outline="#c084fc", width=3)
                    if hv.get("char"):
                        canvas.create_line(cx_ + cw_ / 2 - ml, cy_ + ch_ / 2 - mt, kx - ml, ky - mt,
                                           fill="#c084fc", dash=(4, 3))
            vis = tracker.mine_vis if MODE == "mining" else None
            if vis:
                if vis.get("char"):
                    cx_, cy_, cw_, ch_ = vis["char"]
                    rect(cx_, cy_, cw_, ch_, "#22d3ee")
                    canvas.create_line(cx_ + cw_ / 2 - ml, cy_ - 8 - mt, cx_ + cw_ / 2 - ml, cy_ + ch_ + 8 - mt,
                                       fill="#22d3ee", dash=(3, 3))
                if vis.get("ore"):
                    ox_, oy_ = vis["ore"]
                    canvas.create_oval(ox_ - 10 - ml, oy_ - 10 - mt, ox_ + 10 - ml, oy_ + 10 - mt,
                                       outline="#ff9f1c", width=3)
        root.after(16, draw)

    draw()
    return root


# ----------------------------- mining -----------------------------
# Clicking an ore opens a menu: rows of [ore icon (+ amount)] [arrows]. We pick the row
# with the biggest amount (first one on a tie) and type its arrows with W A S D.
MINE_KEYS = {"up": "w", "left": "a", "down": "s", "right": "d"}
MINE_KEY_HOLD = 0.05    # s each arrow key is held
MINE_KEY_GAP = 0.08     # s between arrow keys
MINE_SCAN_EVERY = 0.08  # s between looks for the menu
FRENZY_WAIT = 0.6       # s: menu still open this long after a row = frenzy, enter the other rows too
MINE_RETRY_AFTER = 2.5  # s: if the menu is still open this long after answering, answer again
DIGITS_DIR = Path(__file__).with_name("digits")  # learned numbers: rename unknown_*.png to e.g. 3.png

# reference shapes, taken from a real screenshot (arrow 32x38 px, digit 11x14 px at scale 1)
_ARROW_UP = """
.............######.............
.............######.............
.............######.............
...........###########..........
...........###########..........
........################........
........################........
........################........
.....######################.....
.....######################.....
.....######################.....
...###########################..
...###########################..
...###########################..
################################
################################
################################
################################
################################
""" + "........################........\n" * 19
_DIGIT_2 = """
########...
########...
........###
........###
........###
...#####...
...#####...
...#####...
###........
###........
###........
###########
###########
###########
"""


def _rows_to_mask(text):
    rows = [r for r in text.strip().splitlines()]
    return np.array([[c == "#" for c in r] for r in rows], np.float32)


_UP = _rows_to_mask(_ARROW_UP)
ARROW_SHAPES = {"up": _UP, "down": np.flipud(_UP), "left": np.rot90(_UP), "right": np.fliplr(np.rot90(_UP))}
ARROW_KEY_NAMES = {"up": "W", "left": "A", "down": "S", "right": "D"}
_digit_shapes = None


def _ncc(a, b):
    a, b = a - a.mean(), b - b.mean()
    d = float(np.sqrt((a * a).sum() * (b * b).sum()))
    return float((a * b).sum() / d) if d else 0.0


def _white(bgr):
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV)
    return ((hsv[:, :, 2] > 200) & (hsv[:, :, 1] < 60)).astype(np.uint8)


def _shape_score(blob, shape):
    r = cv2.resize(blob.astype(np.float32), (shape.shape[1], shape.shape[0]), interpolation=cv2.INTER_AREA)
    return _ncc(r, shape)


def classify_arrow(blob):
    """blob: 0/1 mask of one white shape. Returns 'up'/'down'/'left'/'right', or None."""
    h, w = blob.shape
    names = ("up", "down") if h >= w else ("left", "right")
    scores = {d: _shape_score(blob, ARROW_SHAPES[d]) for d in names}
    best = max(scores, key=scores.get)
    return best if scores[best] >= 0.75 else None


# --- auto mining: reveal ores (mouse 5), walk to the nearest selected ore, press E
MINE_AUTO = True        # auto mining (panel switch): reveal, walk to ores, press E
REVEAL_AFTER_MINE = 1.0 # s to wait after mining (menu closed) before pressing mouse 5 again
REVEAL_EVERY = 15.0     # s the mouse-5 ore reveal lasts; pressed again after this
ORE_ON_PX = 18       # px: character this close (sideways) to the ore's middle = standing on it
MINIMAP_RECT = None     # [x, y, w, h] on screen of the minimap's map area (panel: Pick minimap)
ORE_LEVEL_ABOVE = 140   # px: ores whose middle is more than this above the character's feet are on a ledge
ORE_LEVEL_BELOW = 60    # px: ...or this far below them (a lower floor): skipped
ORE_SLOW_ZONE = 140     # px: closer than this, walk in short taps so we don't overshoot
ORE_MATCH = 0.62        # 0-1: how closely something must look like the ore picture
ORE_SCALES = (0.5, 0.65, 0.8, 1.0, 1.2, 1.45)  # sizes tried for ore pictures (sizes vary by screen)
PATROL_SWITCH = 12.0    # s walking one way without seeing an ore -> turn around
E_WAIT = 2.5            # s to wait for the menu after pressing E
STUCK_DIFF = 2.0        # screen change below this while walking = stuck (jump, then turn)
ORES_DIR = Path(__file__).with_name("ores")  # ore pictures: add with the panel's "Add ore" button
ORES_DISABLED = []      # names of ores NOT to mine (panel gallery)
ORE_LIST = []           # loaded ore pictures
ORES_VERSION = 0        # bumps when ores are added (panel redraws the gallery)


def load_ores():
    """Load every picture in the ores folder. The picture's corner color is treated as
    background and ignored when matching, so the ore is found on any ground."""
    global ORE_LIST, ORES_VERSION
    ores = []
    ORES_DIR.mkdir(exist_ok=True)
    for f in sorted(ORES_DIR.glob("*.png")):
        img = cv2.imdecode(np.frombuffer(f.read_bytes(), np.uint8), cv2.IMREAD_COLOR)
        if img is None or min(img.shape[:2]) < 6:
            continue
        corners = np.array([img[0, 0], img[0, -1], img[-1, 0], img[-1, -1]], np.float32)
        bg = np.median(corners, axis=0)
        mask = (np.linalg.norm(img.astype(np.float32) - bg, axis=2) > 30).astype(np.uint8)
        ores.append({"name": f.stem, "img": img, "mask": mask})
    ORE_LIST = ores
    ORES_VERSION += 1
    return ores


ORE_DOWN = 4  # ores are searched at 1/4 size: fast, and plenty for walking up to them


def find_ores(shot, all_sizes=False):
    """Selected ores on screen: [(center x, center y, match, name)], best first.
    Each ore remembers the size it was found at, so later looks only search that size;
    until then one size is tried per look (all_sizes=True tries them all at once)."""
    small = cv2.resize(shot, None, fx=1 / ORE_DOWN, fy=1 / ORE_DOWN, interpolation=cv2.INTER_AREA)
    hits = []
    for ore in ORE_LIST:
        if ore["name"] in ORES_DISABLED:
            continue
        if ore.get("scale") and not all_sizes:
            sizes = [ore["scale"]]
        elif all_sizes:
            sizes = list(ORE_SCALES)
        else:
            ore["next"] = (ore.get("next", -1) + 1) % len(ORE_SCALES)
            sizes = [ORE_SCALES[ore["next"]]]
        for sc in sizes:
            f = sc / ORE_DOWN
            tpl = cv2.resize(ore["img"], None, fx=f, fy=f, interpolation=cv2.INTER_AREA)
            m = cv2.resize(ore["mask"], (tpl.shape[1], tpl.shape[0]), interpolation=cv2.INTER_NEAREST)
            th, tw = tpl.shape[:2]
            if th < 5 or tw < 5 or th >= small.shape[0] or tw >= small.shape[1] or m.sum() < 10:
                continue
            res = cv2.matchTemplate(small, tpl, cv2.TM_CCOEFF_NORMED, mask=m)
            res = np.nan_to_num(res, nan=-1.0, posinf=-1.0, neginf=-1.0)
            for _ in range(6):
                _, v, _, (lx, ly) = cv2.minMaxLoc(res)
                if v < ORE_MATCH:
                    break
                if v >= ORE_MATCH + 0.1 and not ore.get("scale"):
                    ore["scale"] = sc  # found clearly: search only this size from now on
                hits.append(((lx + tw / 2) * ORE_DOWN, (ly + th / 2) * ORE_DOWN, float(v), ore["name"], tw * ORE_DOWN))
                res[max(0, ly - th):ly + th, max(0, lx - tw):lx + tw] = -1
    hits.sort(key=lambda h: -h[2])
    kept = []
    for h in hits:  # the same ore found at several sizes -> keep the best
        if all(abs(h[0] - k[0]) > 0.5 * k[4] or abs(h[1] - k[1]) > 0.5 * k[4] for k in kept):
            kept.append(h)
    return [(x, y, v, name) for x, y, v, name, _ in kept]


def minimap_info(shot, mon):
    """The player's dot (cyan) on the minimap, and the left/right ends of the terrain
    (grey) there, all in minimap px. Returns (dot x, dot y, terrain left, terrain right) or None."""
    if not MINIMAP_RECT:
        return None
    x, y, w, h = MINIMAP_RECT
    x, y = int(x - mon["left"]), int(y - mon["top"])
    area = shot[max(0, y):y + int(h), max(0, x):x + int(w)]
    if area.size == 0:
        return None
    hsv = cv2.cvtColor(area, cv2.COLOR_BGR2HSV)
    H, S, V = hsv[:, :, 0], hsv[:, :, 1], hsv[:, :, 2]
    dot = ((H >= 80) & (H <= 100) & (S > 120) & (V > 150)).astype(np.uint8)
    n, _, st, cen = cv2.connectedComponentsWithStats(dot, connectivity=8)
    if n < 2:
        return None
    i = 1 + int(np.argmax(st[1:, 4]))
    if st[i, 4] < 4:
        return None
    grey = (S < 60) & (V > 100) & (V < 215)
    cols = np.where(grey.sum(axis=0) >= 2)[0]
    tl, tr = (int(cols.min()), int(cols.max())) if len(cols) else (0, area.shape[1] - 1)
    return float(cen[i][0]), float(cen[i][1]), tl, tr


# ----------------------------- darkness crystal -----------------------------
# A purple dot on the minimap = a darkness crystal. Walk/climb there using the minimap's
# platform layout, press E, then go back to what we were doing.
CRYSTAL_ENABLED = True     # go for darkness crystals (panel switch)
CRYSTAL_DEBUG = True       # keep pictures of the last 3 crystal minigames (debug_crystal folder)
CRYSTAL_COOLDOWN = 18.0    # s the crystal refuses after a wrong sequence ('Try again in 17 seconds')
CRYSTAL_TIMEOUT = 90.0     # s to try reaching a crystal before giving up
CRYSTAL_CHECK_EVERY = 1.0  # s between looks for a crystal on the minimap
BUFF_KEY = "y"             # key that activates the needed (EXP) buff
VEIL_KEY = "6"             # pressed VEIL_DELAY s after the buff so monsters leave us alone ("" = off)
VEIL_DELAY = 1.0
VEIL_GAP = 8.0             # s at least between two veil presses (it may toggle)
HP_SAFETY = True           # low HP -> veil (6) to go invisible; in combat also stop and heal up
HP_LOW = 35                # % of the HP bar that counts as low
HP_RESUME = 80             # % (combat) to heal back up to before fighting again
CRYSTAL_VEIL = True        # veil (6) as soon as a darkness crystal shows up
FISH_BUTTON = "mouse4"     # fishing: cast, and catch when the '!' shows
# combat: run left and right while holding both attacks down; the buff (and veil) on their timer
COMBAT_ATTACK_1 = "mouse1"  # held down the whole time ("" = not used)
COMBAT_ATTACK_2 = "mouse2"
COMBAT_LEFT = "a"
COMBAT_RIGHT = "d"
COMBAT_RUN = 2.0           # s running one way before turning around
REVEAL_BUTTON = "mouse5"   # mining: reveal the ores
BUFF_EVERY = 120           # s between buff key presses (fishing and mining, never during a minigame)
BUFF_ENABLED = True
JUMP_HOLD = 0.3            # s Space is held per jump when there's no minimap to watch
JUMP_TOP_WAIT = 0.1        # s without rising (on the minimap) that counts as the top of a jump
JUMP_HOLD_MAX = 0.7        # s at most to hold Space while waiting for the top of a jump
DOUBLE_JUMP_GAP = 0.22     # s between the two jump presses of a double jump
JUMP_RISE = 0.0            # minimap px a double jump climbs (learned; 0 = not measured yet)
CLEAR_PAD = 3             # safety room (minimap px) checked around the character when planning jumps
CLIMB_MARGIN = 5           # minimap px from a platform's edge to stand before jumping up beside it
LEAP_GAP = 6               # minimap px: widest gap to jump across
DASH_COOLDOWN = 2.0        # s between dashes (stand under a platform, hold W, press DASH_KEY -> up onto it)
DASH_KEY = "r"             # the dash: pressed while holding W (a key, or mouse1-mouse5)
DASH_EDGE = 3              # minimap px to stay in from a platform's ends when dashing up onto it
EDGE_CAREFUL = 6           # minimap px from a platform's end where walking turns into small taps


def parse_minimap(img):
    """Read a minimap picture: terrain mask, player dot and crystal (centers + bottoms, map px)."""
    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
    H, S, V = hsv[:, :, 0], hsv[:, :, 1], hsv[:, :, 2]

    def blob(mask, min_px):
        n, _, st, cen = cv2.connectedComponentsWithStats(mask.astype(np.uint8), connectivity=8)
        best = None
        for i in range(1, n):
            x, y, w, h, a = st[i]
            if a >= min_px and w >= 3 and h >= 3 and (best is None or a > best[3]):
                best = (float(cen[i][0]), float(cen[i][1]), float(y + h), a)
        return best[:3] if best else None

    terrain = (S < 60) & (V > 100) & (V < 215)
    return {"terrain": terrain,
            "dot": blob((H >= 80) & (H <= 100) & (S > 120) & (V > 150), 6),
            "crystal": blob((H >= 125) & (H <= 150) & (S > 100) & (V > 160), 6)}


def platform_tops(terrain):
    """Walkable surfaces: rows of terrain with empty space right above. [(y, x0, x1)]"""
    above = np.zeros_like(terrain)
    above[1:] = terrain[:-1]
    top = terrain & ~above
    segs = []
    for y in range(1, top.shape[0]):
        xs = np.where(top[y])[0]
        if len(xs) == 0:
            continue
        start = prev = xs[0]
        for x in list(xs[1:]) + [None]:
            if x is None or x != prev + 1:
                if prev - start >= 1:
                    segs.append((y, int(start), int(prev)))
                if x is not None:
                    start = x
            if x is not None:
                prev = x
    return segs


def segment_under(segs, x, feet, tol=3):
    """The surface the feet stand on (or are just above)."""
    # the body is ~5 px wide: standing on a platform as long as part of it is over the platform
    c = [i for i, (y, x0, x1) in enumerate(segs) if feet - 1.5 <= y <= feet + tol and x0 - 3 <= x <= x1 + 3]
    return min(c, key=lambda i: segs[i][0] - feet) if c else None


def landing_segment(segs, x, below_y):
    """First surface below height below_y that a falling character at x (~5 px wide) hits."""
    c = [i for i, (y, x0, x1) in enumerate(segs) if y > below_y + 1 and x0 - 3 <= x <= x1 + 3]
    return min(c, key=lambda i: segs[i][0]) if c else None


def headroom(terrain, x, feet):
    """Open space (minimap px) above the character's head at column x."""
    x0, x1 = max(0, int(x) - 3), min(terrain.shape[1], int(x) + 4)
    head = int(feet) - 5
    rows = np.where(terrain[:max(0, head), x0:x1].any(axis=1))[0]
    return head - (rows.max() + 1) if len(rows) else head


def column_clear(terrain, x, y_top, y_bottom):
    """No terrain in a 5-px-wide column between two heights (room for the character to rise)."""
    pad = CLEAR_PAD  # body is ~5 px wide (+-2), plus a safety px each side when CLEAR_PAD is 3
    x0, x1 = max(0, int(x) - pad), min(terrain.shape[1], int(x) + pad + 1)
    y0, y1 = max(0, int(y_top)), max(0, int(y_bottom))
    return y1 <= y0 or not terrain[y0:y1, x0:x1].any()


def platform_above(segs, a, x):
    """The platform right above surface a at column x (the one a dash from there lands on)."""
    ay = segs[a][0]
    c = [i for i, (y, x0, x1) in enumerate(segs) if y < ay - 1 and x0 <= x <= x1]
    return max(c, key=lambda i: segs[i][0]) if c else None


def plan_route(terrain, segs, start, start_x, goal, rise=None, banned=()):
    """Cheapest list of moves from surface start to surface goal.
    Moves: ("drop", stand_x, dir, to)  walk off an end and fall
           ("dash", stand_x, 0, to)    stand under the platform right above, dash up onto it"""
    import heapq
    best = {start: 0.0}
    heap = [(0.0, start, start_x, [])]
    while heap:
        cost, a, ax, path = heapq.heappop(heap)
        if a == goal:
            return path
        if cost > best.get(a, 1e9):
            continue
        ay, ax0, ax1 = segs[a]
        moves = []
        for d, edge in ((-1, ax0 - 3), (1, ax1 + 3)):  # drop off either end
            b = landing_segment(segs, edge, ay)
            if b is None:
                continue
            # the fall needs room for the body (~5 px wide) all the way down: no wall, no narrow gap
            c0, c1 = (ax1 + 1, ax1 + 7) if d > 0 else (ax0 - 6, ax0)  # just past this end (body + 1 px)
            if c0 < 0 or c1 > terrain.shape[1] or terrain[max(0, int(ay) - 5):max(0, int(segs[b][0]) - 1), c0:c1].any():
                continue
            moves.append(("drop", ax0 if d < 0 else ax1, d, b, 4))
        for b, (by, bx0, bx1) in enumerate(segs):  # a slope / small step right beside: just walk on
            if b != a and abs(by - ay) <= 3:
                if 0 <= bx0 - ax1 <= 2:
                    moves.append(("walk", ax1, 1, b, 1))
                elif 0 <= ax0 - bx1 <= 2:
                    moves.append(("walk", ax0, -1, b, 1))
        for b, (by, bx0, bx1) in enumerate(segs):
            if b == a or by >= ay - 1:
                continue
            lo, hi = max(ax0 + 1, bx0 + DASH_EDGE), min(ax1 - 1, bx1 - DASH_EDGE)
            if lo > hi:
                continue  # not over this surface
            # stand where it's the platform right above (nothing in between), closest to where we are
            spots = sorted({int(round(min(max(ax, lo), hi))), int(lo), int(hi), int((lo + hi) / 2)},
                           key=lambda x: abs(x - ax))
            for x in spots:
                if platform_above(segs, a, x) == b:
                    moves.append(("dash", x, 0, b, 6))
                    break
        for kind, stand, d, b, penalty in moves:
            if (a, b, kind) in banned:
                continue
            by, bx0, bx1 = segs[b]
            land_x = min(max(stand + d * 3, bx0), bx1)
            c = cost + abs(stand - ax) + penalty
            if c < best.get(b, 1e9):
                best[b] = c
                heapq.heappush(heap, (c, b, land_x, path + [(kind, stand, d, b)]))
    return None


# --- darkness crystal minigame: a panel of hand-drawn direction symbols (W A S D), typed in order


def symbol_direction(mask):
    """Which way a hand-drawn arrow-ish symbol points: the side that narrows to a tip
    (arrowhead, roof peak) while the opposite side stays wide/flat.
    Returns (direction, score)."""
    ys, xs = np.where(mask)
    if len(xs) < 30:
        return None, 0.0
    x0, x1, y0, y1 = xs.min(), xs.max(), ys.min(), ys.max()
    m = mask[y0:y1 + 1, x0:x1 + 1]
    h, w = m.shape

    def extents(a):  # for each row of a: width covered (rightmost - leftmost)
        out = np.zeros(a.shape[0])
        for i, row in enumerate(a):
            nz = np.where(row)[0]
            out[i] = (nz[-1] - nz[0] + 1) if len(nz) else 0
        return out

    rows, cols = extents(m), extents(m.T)
    def taper(prof, side):
        band = max(2, int(len(prof) * 0.12))
        part = prof[:band] if side == "start" else prof[-band:]
        return 1.0 - part.mean() / max(prof.max(), 1)

    t = {"up": taper(rows, "start"), "down": taper(rows, "end"),
         "left": taper(cols, "start"), "right": taper(cols, "end")}
    opposite = {"up": "down", "down": "up", "left": "right", "right": "left"}
    # where the ink is: an arrowhead / roof puts more of it toward the tip; a thin trail adds little
    total = max(m.sum(), 1)
    mass = {"up": m[: h // 2].sum() / total, "down": m[(h + 1) // 2:].sum() / total,
            "left": m[:, : w // 2].sum() / total, "right": m[:, (w + 1) // 2:].sum() / total}
    score = {d: t[d] - 0.5 * t[opposite[d]] + 0.5 * (mass[d] - mass[opposite[d]]) for d in t}
    best = max(score, key=score.get)
    return best, score[best]


def find_crystal_sprite_xy(shot):
    """(x, y) of the darkness crystal sprite on screen (a big light-purple diamond), or None.
    The hotbar at the bottom and the minimap have purple bits too, so they're left out."""
    small = cv2.resize(shot, None, fx=0.5, fy=0.5, interpolation=cv2.INTER_AREA)
    hsv = cv2.cvtColor(small, cv2.COLOR_BGR2HSV)
    H, S, V = hsv[:, :, 0], hsv[:, :, 1], hsv[:, :, 2]
    m = ((H >= 128) & (H <= 155) & (S >= 45) & (S <= 170) & (V >= 165)).astype(np.uint8)
    m[int(m.shape[0] * 0.75):] = 0  # hotbar / chat / HP bars
    if MINIMAP_RECT:
        mx, my, mw, mh = MINIMAP_RECT
        m[max(0, int(my) // 2 - 20):(int(my) + int(mh)) // 2 + 20, max(0, int(mx) // 2 - 20):(int(mx) + int(mw)) // 2 + 20] = 0
    m = cv2.morphologyEx(m, cv2.MORPH_CLOSE, np.ones((3, 3), np.uint8))
    n, _, st, cen = cv2.connectedComponentsWithStats(m, connectivity=8)
    # the crystal (a purple diamond, often half hidden behind the character) sits at the bottom of
    # its own light beam, which shows up as more purple pieces straight above it. Group the pieces
    # into columns, take the column with the most purple, and its LOWEST piece is the crystal.
    parts = [(float(cen[i][0]), float(cen[i][1]), int(st[i][2]), int(st[i][3]), int(st[i][4]))
             for i in range(1, n) if st[i][4] >= 40 and st[i][3] >= 8 and st[i][2] >= 8]
    if not parts:
        return None
    best_col, best_area = None, 0
    for cx, _, _, _, _ in parts:
        col = [p_ for p_ in parts if abs(p_[0] - cx) <= 35]
        total = sum(p_[4] for p_ in col)
        if total > best_area:
            best_col, best_area = col, total
    if best_area < 70:
        return None
    low = max(best_col, key=lambda p_: p_[1] + p_[3] / 2)  # lowest bottom edge
    return low[0] * 2, low[1] * 2


def find_crystal_sprite(shot):
    """Center x of the crystal sprite on screen, or None."""
    xy = find_crystal_sprite_xy(shot)
    return xy[0] if xy else None


def find_crystal_panel(before, after, near_x=None):
    """The crystal minigame's panel: the big rectangle that got about half as bright between
    the screenshot before pressing E and after. Returns (x, y, w, h) or None."""
    def small(img):
        return cv2.resize(cv2.cvtColor(img, cv2.COLOR_BGR2GRAY), None, fx=0.25, fy=0.25,
                          interpolation=cv2.INTER_AREA).astype(np.float32)
    b, a = small(before), small(after)
    # line the "before" picture up with the "after" one, in case the camera scrolled a bit
    (dx, dy), response = cv2.phaseCorrelate(b, a)
    if response > 0.05 and (abs(dx) > 0.5 or abs(dy) > 0.5):
        b = cv2.warpAffine(b, np.float32([[1, 0, dx], [0, 1, dy]]), (b.shape[1], b.shape[0]),
                           borderMode=cv2.BORDER_REPLICATE)
    dark = ((a < b * 0.72) & (b > 25)).astype(np.uint8)
    dark = cv2.morphologyEx(dark, cv2.MORPH_CLOSE, np.ones((5, 5), np.uint8))  # fill in the symbols
    n, _, st, _ = cv2.connectedComponentsWithStats(dark, connectivity=8)
    best = None
    screen_area = dark.shape[0] * dark.shape[1]
    for i in range(1, n):
        x, y, w, h, area = st[i]
        solid = area >= 0.85 * w * h          # a clean rectangle, not a ragged patch
        not_huge = w * h <= 0.35 * screen_area  # a flash / lighting change covers most of the screen
        panel_shape = 1.8 <= w / h <= 4.5 and h * 4 >= 80  # message boxes are long thin strips
        near = near_x is None or abs((x + w / 2) * 4 - near_x) <= 450  # the panel opens by the crystal
        if area >= 400 and solid and not_huge and panel_shape and near and (best is None or area > best[4]):
            best = (x, y, w, h, area)
    return tuple(int(v * 4) for v in best[:4]) if best else None


def _symbol_mask(slot):
    """The symbol in one slot, without sparkles and without the thin swoosh trail."""
    n_, lab, st, _ = cv2.connectedComponentsWithStats(slot, connectivity=8)
    keep = np.zeros_like(slot)
    for j in range(1, n_):
        if st[j, 4] >= 25:
            keep[lab == j] = 1
    if keep.sum() == 0:
        return keep
    # thick symbols (like the big arrow): keep the thick body, drop thin lines stuck to it
    dist = cv2.distanceTransform(keep, cv2.DIST_L2, 3)
    core = (dist >= 3).astype(np.uint8)
    if core.sum() >= 0.15 * keep.sum():
        body = cv2.dilate(core, np.ones((7, 7), np.uint8)) & keep
        return body
    return keep  # all thin strokes (like the house): keep everything


CRYSTAL_SYMBOLS_DIR = Path(__file__).with_name("crystal_symbols")  # reference symbols: up_*.png, right_*.png...
_DIR_CYCLE = ("up", "right", "down", "left")  # clockwise
_crystal_refs = None


def _symbol_square(mask, size=64):
    """Crop a symbol to its outline, pad to a square (keeps its shape), shrink, soften."""
    ys, xs = np.where(mask)
    if len(xs) < 20:
        return None
    m = mask[ys.min():ys.max() + 1, xs.min():xs.max() + 1].astype(np.float32)
    h, w = m.shape
    side = max(h, w)
    sq = np.zeros((side, side), np.float32)
    sq[(side - h) // 2:(side - h) // 2 + h, (side - w) // 2:(side - w) // 2 + w] = m
    sq = cv2.resize(sq, (size, size), interpolation=cv2.INTER_AREA)
    return cv2.GaussianBlur(sq, (0, 0), 2.0)


def load_crystal_refs():
    """Reference symbols (pictures named by the direction they point), each also turned to
    point the other three ways."""
    refs = []
    if CRYSTAL_SYMBOLS_DIR.exists():
        for f in sorted(CRYSTAL_SYMBOLS_DIR.glob("*.png")):
            label = f.stem.split("_")[0]
            if label not in _DIR_CYCLE:
                continue
            img = cv2.imdecode(np.frombuffer(f.read_bytes(), np.uint8), cv2.IMREAD_GRAYSCALE)
            if img is None:
                continue
            m = img > 127
            for k in range(4):
                sq = _symbol_square(np.rot90(m, -k))
                if sq is not None:
                    refs.append((_DIR_CYCLE[(_DIR_CYCLE.index(label) + k) % 4], f.stem, sq))
    return refs


def _hull_taper(mask):
    """Per direction: how much the symbol's outline (convex hull) narrows to a point on that
    side compared with the opposite side. Gaps in the strokes don't change the hull."""
    out = {d: 0.0 for d in _DIR_CYCLE}
    ys, xs = np.where(mask)
    if len(xs) < 20:
        return out
    hull = cv2.convexHull(np.column_stack([xs, ys]).astype(np.int32))
    x0, y0 = xs.min(), ys.min()
    sil = np.zeros((ys.max() - y0 + 1, xs.max() - x0 + 1), np.uint8)
    cv2.fillPoly(sil, [hull - [x0, y0]], 1)
    h, w = sil.shape
    for axis, lo, hi, length, across in ((1, "up", "down", h, w), (0, "left", "right", w, h)):
        prof = sil.sum(axis=axis).astype(float)
        k = max(2, int(len(prof) * 0.1))
        a, z = prof[:k].mean() / prof.max(), prof[-k:].mean() / prof.max()
        along = (length / max(1, across)) ** 0.5  # an arrow is longer the way it points
        out[lo], out[hi] = (z - a) * along, (a - z) * along
    return out


def _card_lines(mask):
    """A symbol drawn as dark lines on a solid white card: return the dark lines (as a mask),
    or None if it's a normal white drawing."""
    ys, xs = np.where(mask)
    if len(xs) < 100:
        return None
    hull = cv2.convexHull(np.column_stack([xs, ys]).astype(np.int32))
    card = np.zeros(mask.shape, np.uint8)
    cv2.fillPoly(card, [hull], 1)
    if mask.sum() < 0.6 * card.sum():
        return None
    (_, _), (rw, rh), _ = cv2.minAreaRect(np.column_stack([xs, ys]).astype(np.float32))
    if card.sum() < 0.88 * rw * rh:  # a card is a (maybe tilted) rectangle; a solid arrow isn't
        return None
    k = max(3, int(min(mask.shape) * 0.08))
    inner = cv2.erode(card, np.ones((k, k), np.uint8))  # leave out the card's edge
    lines = (inner > 0) & ~mask
    n, lab, st, _ = cv2.connectedComponentsWithStats(lines.astype(np.uint8), connectivity=8)
    keep = np.zeros_like(lines)
    for i in range(1, n):
        if st[i, 4] >= 25:
            keep |= lab == i
    return keep if keep.sum() >= 40 else None


CRYSTAL_TAPER_WEIGHT = 0.5  # how much the outline's 'narrows to a point' counts vs the reference drawings


def rank_symbol(mask):
    """All 4 directions for one symbol, most likely first: [(direction, score), ...].
    Score = best match among the reference drawings for that direction, plus how the
    symbol's outline narrows toward that side, plus a little for the 'pointy side' rule."""
    global _crystal_refs
    lines = _card_lines(mask)
    if lines is not None:
        mask = lines
    if _crystal_refs is None:
        _crystal_refs = load_crystal_refs()
    ref = {d: 0.0 for d in _DIR_CYCLE}
    sq = _symbol_square(mask)
    if sq is not None:
        for d, _, r in _crystal_refs:
            ref[d] = max(ref[d], _ncc(sq, r))
    if max(ref.values()) < 0.5:
        _save_new_symbol(mask)  # a drawing style we don't know yet: keep it so it can be taught
    taper = _hull_taper(mask)
    pointy, _ = symbol_direction(mask)
    total = {d: ref[d] + CRYSTAL_TAPER_WEIGHT * taper[d] + (0.1 if d == pointy else 0.0) for d in _DIR_CYCLE}
    return sorted(total.items(), key=lambda kv: kv[1], reverse=True)


def classify_symbol(mask):
    """Direction of one symbol and its score."""
    return rank_symbol(mask)[0]


def _save_new_symbol(mask):
    try:
        folder = CRYSTAL_SYMBOLS_DIR / "new"
        folder.mkdir(parents=True, exist_ok=True)
        if len(list(folder.glob("*.png"))) >= 40:
            return
        ys, xs = np.where(mask)
        if len(xs) < 20:
            return
        m = mask[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
        ok, buf = cv2.imencode(".png", m.astype(np.uint8) * 255)
        name = f"unknown_{time.strftime('%H%M%S')}_{len(list(folder.glob('*.png')))}.png"
        (folder / name).write_bytes(buf.tobytes())
        log(f"  new symbol style saved as crystal_symbols/new/{name} - rename it to up_/down_/left_/right_"
            f"... and move it into crystal_symbols to teach me")
    except Exception:
        pass


def read_crystal_panel(bgr, panel):
    """Split the panel into its symbol slots and read each one's direction (None = dimmed,
    already entered). The slot count is picked so slots line up with the symbols; each slot
    is read with slightly shifted boundaries and the majority wins."""
    px, py, pw, ph = panel
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV)
    white = ((hsv[:, :, 2] > 200) & (hsv[:, :, 1] < 60)).astype(np.uint8)
    white = cv2.morphologyEx(white, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))  # drop sparkle dots
    band = white[max(0, int(py + 0.06 * ph)):int(py + 0.94 * ph), max(0, int(px)):int(px + pw)]
    cols = band.sum(axis=0).astype(np.float32)
    guess = max(1, int(round(pw / (0.87 * ph))))
    best_n, best_fit = guess, -1e9
    for n in {max(1, guess - 1), guess, guess + 1}:
        sw = pw / n
        fit = 0.0
        for i in range(n):  # ink near slot centers is good, ink on slot boundaries is bad
            c = int((i + 0.5) * sw)
            fit += cols[max(0, c - int(sw * 0.25)):c + int(sw * 0.25)].sum()
        for i in range(1, n):
            e = int(i * sw)
            fit -= 3 * cols[max(0, e - 4):e + 4].sum()
        fit -= abs(n - pw / (0.87 * ph)) * 0.05 * max(cols.sum(), 1)  # mild preference for the usual shape
        if fit > best_fit:
            best_n, best_fit = n, fit
    n, sw = best_n, pw / best_n
    out = []
    for i in range(n):
        votes = {}
        for shift in (-0.06, -0.03, 0.0, 0.03, 0.06):
            for margin in (0.05, 0.09):
                sx0 = int(px + (i + shift + margin) * sw)
                sx1 = int(px + (i + 1 + shift - margin) * sw)
                slot = white[int(py + 0.06 * ph):int(py + 0.94 * ph), max(0, sx0):max(0, sx1)]
                if slot.size == 0 or slot.sum() < 0.01 * slot.size:
                    votes[None] = votes.get(None, 0) + 1
                    continue
                d, sc = classify_symbol(_symbol_mask(slot) > 0)
                votes[d] = votes.get(d, 0) + 1
        best = max(votes, key=votes.get)
        out.append((i, best, votes[best] / sum(votes.values())))
    return n, out


def _erase_trail(white, sym_h, need_span):
    """Follow the smoothest left-to-right path that stays on white the most, and erase the
    thin parts of its long unbroken stretches (a swoosh / slash). A symbol's own straight edge
    is short, so it stays."""
    H, W = white.shape
    cols = np.where(white.any(axis=0))[0]
    if len(cols) == 0 or cols[-1] - cols[0] < need_span:
        return white
    x_lo, x_hi = cols[0], cols[-1]
    miss = 1.0 - white[:, x_lo:x_hi + 1].astype(np.float32)  # 0 on white, 1 off it
    n = x_hi - x_lo + 1
    cost = miss[:, 0].copy()
    back = np.zeros((H, n), np.int8)
    for i in range(1, n):  # each step: stay on the same row, or move one row up / down
        up = np.r_[np.inf, cost[:-1]] + 0.05
        dn = np.r_[cost[1:], np.inf] + 0.05
        stack = np.vstack([up, cost, dn])
        k = stack.argmin(axis=0)
        back[:, i] = k - 1
        cost = stack[k, np.arange(H)] + miss[:, i]
    y = int(cost.argmin())
    path = np.zeros(n, int)
    for i in range(n - 1, -1, -1):
        path[i] = y
        y = y + int(back[y, i]) if i else y
    on = white[path, np.arange(n) + x_lo] > 0
    step = np.sqrt(1.0 + np.r_[0, np.diff(path)] ** 2)  # length along the line
    long_run = np.zeros(n, bool)
    i = 0
    while i < n:
        if not on[i]:
            i += 1
            continue
        j = i
        while j < n and on[j]:
            j += 1
        if step[i:j].sum() >= 1.2 * sym_h:
            long_run[i:j] = True
        i = j
    if not long_run.any():
        return white
    out = white.copy()
    thin = max(3, int(sym_h * 0.11))
    for i in np.where(long_run)[0]:
        x, y = i + x_lo, path[i]
        y0 = y
        while y0 > 0 and white[y0 - 1, x]:
            y0 -= 1
        y1 = y
        while y1 < H - 1 and white[y1 + 1, x]:
            y1 += 1
        if y1 - y0 + 1 <= thin:  # just the trail here: erase it
            out[y0:y1 + 1, x] = 0
        elif y1 - y0 + 1 <= 2 * thin:  # crossing a stroke: only take out the trail's own width
            out[max(0, y - 2):y + 3, x] = 0
    return out


def remove_swoosh(white, sym_h):
    """The minigame draws thin trails over the symbols: a swoosh across the row, or a steep
    slash. Erase both (the steep one is traced on the picture turned sideways)."""
    out = _erase_trail(white, sym_h, 2 * sym_h)
    return np.ascontiguousarray(_erase_trail(np.ascontiguousarray(out.T), sym_h, 0.8 * sym_h).T)


def _aligned_before(before, shot):
    """The 'before' picture shifted to line up with 'shot' (in case the camera moved a bit)."""
    def small(img):
        return cv2.resize(cv2.cvtColor(img, cv2.COLOR_BGR2GRAY), None, fx=0.25, fy=0.25,
                          interpolation=cv2.INTER_AREA).astype(np.float32)
    (dx, dy), response = cv2.phaseCorrelate(small(before), small(shot))
    if response > 0.05 and (abs(dx) > 0.5 or abs(dy) > 0.5):
        return cv2.warpAffine(before, np.float32([[1, 0, dx * 4], [0, 1, dy * 4]]),
                              (before.shape[1], before.shape[0]), borderMode=cv2.BORDER_REPLICATE)
    return before


def find_crystal_symbols(shot, near=None, before=None, detail=False):
    """The minigame's symbols in one screenshot: big white hand-drawn strokes in a row, near the
    crystal. Dimmed (already entered) ones aren't white, so they're left out on their own.
    Returns [(direction, (x, y, w, h)), ...] left to right, or [] if there's no minigame."""
    H, W = shot.shape[:2]
    if before is not None:
        # with a picture from before E, the panel is found by how it darkens the screen: look
        # anywhere above the hotbar (the panel doesn't center on the crystal - it can reach far
        # to one side of it)
        x0, x1, y0, y1 = 0, W, int(H * 0.09), int(H * 0.75)  # (not the buff icons along the top)
    elif near is not None:  # the panel opens around the crystal
        nx, ny = near
        x0, x1 = max(0, int(nx - 800)), min(W, int(nx + 800))
        y0, y1 = max(int(H * 0.09), int(ny - 350)), min(int(H * 0.75), int(ny + 350))
    else:  # (only used for cropped test pictures)
        x0, x1, y0, y1 = 0, W, 0, H
    if x1 - x0 < 20 or y1 - y0 < 20:
        return []
    area = shot[y0:y1, x0:x1]

    def white_of(img):
        hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
        m = ((hsv[:, :, 2] > 200) & (hsv[:, :, 1] < 60)).astype(np.uint8)
        return cv2.morphologyEx(m, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))  # sparkles out
    white = white_of(area)
    if near is None and before is not None and MINIMAP_RECT:
        mx, my, mw, mh = (int(v) for v in MINIMAP_RECT)
        white[max(0, my - 40 - y0):my + mh + 40 - y0, max(0, mx - 40 - x0):mx + mw + 40 - x0] = 0
    gray = cv2.cvtColor(area, cv2.COLOR_BGR2GRAY)
    if before is not None:  # what was there before E: the symbols are new, and the panel dims things
        # line 'before' up with this picture around the panel only (the fixed HUD would say 'no shift'
        # even when the camera moved)
        ga = cv2.cvtColor(area, cv2.COLOR_BGR2GRAY).astype(np.float32)
        gb_ = cv2.cvtColor(before[y0:y1, x0:x1], cv2.COLOR_BGR2GRAY).astype(np.float32)
        win = cv2.createHanningWindow((ga.shape[1], ga.shape[0]), cv2.CV_32F)
        (sdx, sdy), resp = cv2.phaseCorrelate(gb_, ga, win)
        if resp > 0.05 and (abs(sdx) > 0.5 or abs(sdy) > 0.5) and abs(sdx) < 200 and abs(sdy) < 200:
            moved = cv2.warpAffine(before, np.float32([[1, 0, sdx], [0, 1, sdy]]), (before.shape[1], before.shape[0]),
                                   borderMode=cv2.BORDER_REPLICATE)
            b_area = moved[y0:y1, x0:x1]
        else:
            b_area = before[y0:y1, x0:x1]
        b_gray = cv2.cvtColor(b_area, cv2.COLOR_BGR2GRAY).astype(np.float32)
        # how much the whole area got darker (night / 'darkness clouds your senses'): the panel
        # has to be clearly darker than that
        overall = float(np.median(gray.astype(np.float32) / np.maximum(b_gray, 1)))
        new = white & (1 - cv2.dilate(white_of(b_area), np.ones((7, 7), np.uint8)))
    grown = cv2.dilate(white, np.ones((9, 9), np.uint8))  # strokes of one symbol -> one blob
    n, lab, st, _ = cv2.connectedComponentsWithStats(grown, connectivity=8)
    boxes = []
    for i in range(1, n):
        x, y, w, h, _ = st[i]
        ink = int(white[y:y + h, x:x + w][lab[y:y + h, x:x + w] == i].sum())
        if not (40 <= h <= 260 and w >= 20 and h <= 3 * w and ink >= 600):
            continue
        bx0, by0 = max(0, x - 10), max(0, y - 10)
        ring = white[by0:y + h + 10, bx0:x + w + 10] == 0
        around = gray[by0:y + h + 10, bx0:x + w + 10][ring]
        if not around.size:
            continue
        if before is not None:
            # new white strokes (not scenery) on a patch that got darker (the panel)
            mine = lab[y:y + h, x:x + w] == i
            new_part = new[y:y + h, x:x + w][mine].sum() / max(1, white[y:y + h, x:x + w][mine].sum())
            was = b_gray[by0:y + h + 10, bx0:x + w + 10][ring]
            ratio = float(np.median(around.astype(np.float32) / np.maximum(was, 1)))
            dimmed = ratio < 0.8 and ratio < 0.8 * overall  # the panel is see-through dark
            if dimmed:  # (not 'new white' too: the crystal's light beam can stand right where a symbol shows up)
                boxes.append([x, y, w, h])
        # symbols are drawn on the panel's dark background (the crystal's light beam isn't)
        elif np.median(around) < 125:
            boxes.append([x, y, w, h])
    if not boxes:
        return []
    # they sit in one row: keep the ones lined up with the biggest symbol
    ref = max(boxes, key=lambda b: b[2] * b[3])
    ref_cy, sym_h = ref[1] + ref[3] / 2, ref[3]
    boxes = [b for b in boxes if abs(b[1] + b[3] / 2 - ref_cy) <= 0.45 * sym_h and b[3] >= 0.3 * sym_h]
    row = np.zeros_like(white)
    for x, y, w, h in boxes:
        row[y:y + h, x:x + w] = white[y:y + h, x:x + w]
    # judge trails by a typical symbol's height (the biggest blob can be a symbol + swoosh)
    white = remove_swoosh(row, float(np.median([b_[3] for b_ in boxes])) if len(boxes) >= 3 else sym_h)
    n, lab, st, _ = cv2.connectedComponentsWithStats(cv2.dilate(white, np.ones((9, 9), np.uint8)), connectivity=8)
    boxes = []
    for i in range(1, n):
        x, y, w, h, _ = st[i]
        ink = int(white[y:y + h, x:x + w][lab[y:y + h, x:x + w] == i].sum())
        if h >= 0.3 * sym_h and w >= 0.15 * sym_h and ink >= 300:
            boxes.append((x, y, w, h))
    # two symbols still joined: split wide blobs at the thinnest column
    split = []
    for x, y, w, h in sorted(boxes):
        parts = max(1, int(round(w / (1.15 * sym_h))))
        if parts == 1:
            split.append((x, y, w, h))
            continue
        cols = white[y:y + h, x:x + w].sum(axis=0).astype(np.float32)
        cuts = []
        for k in range(1, parts):
            c = int(k * w / parts)
            lo, hi = max(1, c - int(0.25 * w / parts)), min(w - 1, c + int(0.25 * w / parts))
            cuts.append(lo + int(np.argmin(cols[lo:hi])))
        edges = [0] + cuts + [w]
        for a, b_ in zip(edges, edges[1:]):
            split.append((x + a, y, b_ - a, h))
    pieces = []
    for x, y, w, h in split:
        m = _symbol_mask(white[y:y + h, x:x + w]) > 0
        if m.sum() >= 20:
            pieces.append([x, y, w, h, m])
    # symbols sit evenly spaced, about a symbol apart: a small piece squeezed in between two of
    # them is a stray bit of the swoosh, not a symbol
    changed = True
    while changed and len(pieces) > 1:
        changed = False
        ctr = [pc[0] + pc[2] / 2 for pc in pieces]
        typical_h = float(np.median([pc[3] for pc in pieces]))  # (the biggest can be swollen by a swoosh)
        for a in range(len(pieces) - 1):
            ink_a, ink_b = pieces[a][4].sum(), pieces[a + 1][4].sum()
            # squeezed in AND much smaller than its neighbour: a bit of swoosh, not a symbol
            if ctr[a + 1] - ctr[a] < 1.0 * typical_h and min(ink_a, ink_b) < 0.45 * max(ink_a, ink_b):
                del pieces[a if ink_a < ink_b else a + 1]
                changed = True
                break
    if pieces:
        typical = float(np.median([pc[4].sum() for pc in pieces]))
        pieces = [pc for pc in pieces if pc[4].sum() >= 0.35 * typical]
    out = []
    for x, y, w, h, m in pieces:
        ranking = rank_symbol(m)
        box = (x0 + x, y0 + y, w, h)
        out.append((ranking[0][0], box, ranking, m) if detail else (ranking[0][0], box))
    return out


def _is_new_menu(now, answered):
    """Is this a different arrow menu, or still the one we just answered (maybe with its arrows
    fading out as they're entered)? Rows that are a piece of an answered row count as old."""
    def piece_of(row, full):
        return any(full[i:i + len(row)] == row for i in range(len(full) - len(row) + 1))
    if not now or now == answered:
        return False
    return any(not any(piece_of(r, a) for a in answered) for r in now)


_OPPOSITE = {"up": "down", "down": "up", "left": "right", "right": "left"}


def find_mining_menu(bgr):
    """Rows of arrows on screen, top to bottom: [{'arrows': [(x, y, w, h, dir, purple), ...]}].
    dir is the direction to PRESS: a purple arrow means the opposite of where it points."""
    white = _white(bgr)
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV)
    purple = ((hsv[:, :, 0] >= 125) & (hsv[:, :, 0] <= 155) & (hsv[:, :, 1] > 120) & (hsv[:, :, 2] > 150)).astype(np.uint8)
    n, lab, stats, _ = cv2.connectedComponentsWithStats(white | purple, connectivity=8)
    arrows = []
    for i in range(1, n):
        x, y, w, h, a = stats[i]
        if not (16 <= h <= 120 and 16 <= w <= 120 and 0.65 <= h / w <= 1.55):
            continue
        blob = lab[y:y + h, x:x + w] == i
        d = classify_arrow(blob)
        if d:
            is_purple = purple[y:y + h, x:x + w][blob].mean() > 0.5
            arrows.append((int(x), int(y), int(w), int(h), _OPPOSITE[d] if is_purple else d, bool(is_purple)))
    rows = []
    for a in sorted(arrows, key=lambda a: a[1] + a[3] / 2):
        yc, size = a[1] + a[3] / 2, max(a[2], a[3])
        for r in rows:
            if abs(r["yc"] - yc) <= 0.45 * size:
                r["arrows"].append(a)
                break
        else:
            rows.append({"yc": yc, "arrows": [a]})
    good = []
    for r in rows:
        r["arrows"].sort(key=lambda a: a[0])
        size = max(max(a[2], a[3]) for a in r["arrows"])
        gaps_ok = all(b[0] - (a[0] + a[2]) <= 1.5 * size for a, b in zip(r["arrows"], r["arrows"][1:]))
        if gaps_ok:
            r["scale"] = size / 38.0
            good.append(r)
    # a real menu: at least 2 arrows, and the rows line up on the left
    if sum(len(r["arrows"]) for r in good) < 2:
        return []
    left = min(r["arrows"][0][0] for r in good)
    return [r for r in good if r["arrows"][0][0] - left <= 0.6 * max(a[2] for a in r["arrows"])]


def _digit_grid(blob):
    """Numbers are drawn on a 4x5 grid of game pixels, each 2-3 screen pixels wide depending
    on where they land. Shrinking to that grid makes the same digit always look the same."""
    g = cv2.resize(blob.astype(np.float32), (4, 5), interpolation=cv2.INTER_AREA)
    return g >= 0.5


def _load_digit_shapes():
    shapes = {"2": [_digit_grid(_rows_to_mask(_DIGIT_2) > 0)]}
    if DIGITS_DIR.exists():
        for f in DIGITS_DIR.glob("*.png"):
            label = f.stem.split("_")[0]
            if not label.isdigit():
                continue
            img = cv2.imdecode(np.frombuffer(f.read_bytes(), np.uint8), cv2.IMREAD_COLOR)
            if img is None:
                continue
            m = _white(img)
            n, lab, st, _ = cv2.connectedComponentsWithStats(m, connectivity=8)
            if n < 2:
                continue
            i = 1 + int(np.argmax(st[1:, 4]))  # biggest white shape in the picture
            x, y, w, h, _ = st[i]
            shapes.setdefault(label, []).append(_digit_grid(lab[y:y + h, x:x + w] == i))
    return shapes


def read_amount(bgr, row):
    """Number shown on the row's ore icon (1 if none). Returns (value, text)."""
    global _digit_shapes
    if _digit_shapes is None:
        _digit_shapes = _load_digit_shapes()
    x0, s = row["arrows"][0][0], row["scale"]
    top = int(row["yc"] - 19 * s)
    zx0, zx1 = max(0, int(x0 - 75 * s)), max(0, int(x0 - 22 * s))
    zy0, zy1 = max(0, int(top + 8 * s)), min(bgr.shape[0], int(top + 52 * s))
    zone = bgr[zy0:zy1, zx0:zx1]
    if zone.size == 0:
        return 1, "1"
    white = _white(zone)
    dark = cv2.cvtColor(zone, cv2.COLOR_BGR2GRAY) < 60
    n, lab, st, _ = cv2.connectedComponentsWithStats(white, connectivity=8)
    glyphs = []
    for i in range(1, n):
        x, y, w, h, a = st[i]
        if not (10 * s <= h <= 18 * s and 3 * s <= w <= 14 * s):
            continue
        blob = lab[y:y + h, x:x + w] == i
        ring = cv2.dilate(blob.astype(np.uint8), np.ones((5, 5), np.uint8)) > 0
        y0, x0b = max(0, y - 2), max(0, x - 2)
        big = np.zeros(white.shape, bool)
        big[y:y + h, x:x + w] = blob
        grown = cv2.dilate(big.astype(np.uint8), np.ones((5, 5), np.uint8)) > 0
        edge = grown & ~big
        if edge.sum() == 0 or dark[edge].mean() < 0.5:  # numbers have a black outline
            continue
        glyphs.append((int(x), blob, (int(x), int(y), int(w), int(h))))
    if not glyphs:
        return 1, "1"
    text = ""
    for gx, blob, box in sorted(glyphs, key=lambda g: g[0]):
        grid = _digit_grid(blob)
        best, diff = "?", 99
        for digit, grids in _digit_shapes.items():
            for g in grids:
                d = int((g != grid).sum())  # how many of the 20 game pixels differ
                if d < diff:
                    best, diff = digit, d
        if diff > 1:
            best = "?"
            _save_unknown_digit(zone, box)
        text += best
    if "?" in text:
        return 2, text  # unknown number: at least 2
    return int(text), text


def _save_unknown_digit(zone, box):
    """Save just the number (plus its outline), enlarged so it's easy to see."""
    try:
        DIGITS_DIR.mkdir(exist_ok=True)
        if len(list(DIGITS_DIR.glob("unknown_*.png"))) >= 30:
            return
        x, y, w, h = box
        crop = zone[max(0, y - 3):y + h + 3, max(0, x - 3):x + w + 3]
        f = DIGITS_DIR / f"unknown_{time.strftime('%H%M%S')}_{x}.png"
        big = cv2.resize(crop, None, fx=4, fy=4, interpolation=cv2.INTER_NEAREST)
        ok, buf = cv2.imencode(".png", big)
        if ok:
            f.write_bytes(buf.tobytes())
            log(f"New number on an ore - saved {f.name} in the digits folder. "
                f"Rename it to the number it shows (e.g. 3.png) to teach me.")
    except Exception:
        pass


# ----------------------------- control panel -----------------------------
SETTINGS_FILE = Path(__file__).with_name("settings.json")
# setting name: (label, min, max, step)
TUNABLES = {
    "LEAD": ("Braking / prediction (s)", 0.0, 0.6, 0.01),
    "DEADZONE_PX": ("Dead zone (px)", 0, 30, 1),
    "FULL_PRESS_PX": ("Full press distance (px)", 5, 150, 1),
    "WANDER_EVERY": ("Walk around every (s)", 20, 300, 5),
    "CHECK_TIMEOUT": ("Recast if no '!' after (s)", 5, 120, 1),
    "IDLE_RECAST": ("Recast if idle for (s)", 5, 120, 1),
    "ORE_ON_PX": ("'On the ore' within (px)", 4, 60, 1),
    "ORE_MATCH": ("Ore match strictness", 0.4, 0.9, 0.01),
    "BUFF_EVERY": ("Press Y (buff) every (s)", 30, 600, 5),
    "COMBAT_RUN": ("Run one way for (s)", 0.3, 10, 0.1),
    "HP_LOW": ("Low HP: veil below (%)", 5, 90, 1),
    "HP_RESUME": ("Combat: heal up to (%)", 30, 100, 1),
}
TOGGLES = {
    "MANUAL_MODE": "Manual mode: catch + recast only, no moving  (F4)",
    "WATCH_WHOLE_SCREEN": "Look for the '!' on the whole screen",
    "WANDER_ENABLED": "Walk around + jump now and then",
    "ANCHOR_ENABLED": "Walk back to the anchor before casting",
    "YELLOW_DIAGNOSTICS": "Detailed '!' info in the log",
    "MINE_AUTO": "Auto mining (Auto / Manual buttons)",
    "CRYSTAL_ENABLED": "Go for darkness crystals (purple dot on the minimap)",
    "BUFF_ENABLED": "Press Y every couple of minutes (buff)",
    "HP_SAFETY": "Low HP: press the veil (6) to go invisible and heal",
    "CRYSTAL_VEIL": "Press the veil (6) when a darkness crystal shows up",
}
KEY_SETTINGS = {  # name: (label, which pages)
    "FISH_BUTTON": ("Fishing: cast / catch", ("fishing",)),
    "REVEAL_BUTTON": ("Mining: reveal ores", ("mining",)),
    "BUFF_KEY": ("EXP buff", ("fishing", "mining", "combat")),
    "VEIL_KEY": ("Veil (1 s after the buff)", ("fishing", "mining", "combat")),
    "DASH_KEY": ("Dash up (held W + this)", ("fishing", "mining", "combat")),
    "COMBAT_ATTACK_1": ("Attack held down", ("combat",)),
    "COMBAT_ATTACK_2": ("Second attack held down", ("combat",)),
    "COMBAT_LEFT": ("Run left", ("combat",)),
    "COMBAT_RIGHT": ("Run right", ("combat",)),
}
OPTIONAL_KEYS = ("VEIL_KEY", "COMBAT_ATTACK_1", "COMBAT_ATTACK_2")  # may be left empty = not used
LOG_QUEUE = queue.Queue()


class _Tee:
    """Send everything printed to both the terminal and the panel's log."""

    def __init__(self, stream):
        self.stream = stream

    def write(self, text):
        if self.stream is not None:
            try:
                self.stream.write(text)
            except Exception:
                pass
        LOG_QUEUE.put(text)

    def flush(self):
        if self.stream is not None:
            try:
                self.stream.flush()
            except Exception:
                pass


def load_settings():
    """Apply settings.json (from the panel) on top of the defaults above."""
    try:
        data = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}
    if isinstance(data.get("GAME_MONITOR"), int):
        globals()["GAME_MONITOR"] = data["GAME_MONITOR"]
    if isinstance(data.get("JUMP_RISE"), (int, float)):
        globals()["JUMP_RISE"] = float(data["JUMP_RISE"])
    if isinstance(data.get("MINIMAP_RECT"), list) and len(data["MINIMAP_RECT"]) == 4:
        globals()["MINIMAP_RECT"] = data["MINIMAP_RECT"]
    if isinstance(data.get("ORES_DISABLED"), list):
        globals()["ORES_DISABLED"] = data["ORES_DISABLED"]
    if data.get("MODE") in ("fishing", "mining", "combat"):
        globals()["MODE"] = data["MODE"]
    for name in list(TUNABLES) + list(TOGGLES):
        if name in data:
            globals()[name] = data[name]
    for name in KEY_SETTINGS:
        v = data.get(name)
        if isinstance(v, str) and (v == "" and name in OPTIONAL_KEYS or valid_key(v)):
            globals()[name] = v.strip().lower()
    return data


def save_settings(tracker, panel_visible):
    data = {name: globals()[name] for name in list(TUNABLES) + list(TOGGLES) + list(KEY_SETTINGS)}
    data["LEAD"], data["MANUAL_MODE"] = tracker.lead, tracker.manual
    data["panel_visible"] = panel_visible
    data["MODE"] = MODE
    data["ORES_DISABLED"] = ORES_DISABLED
    data["MINIMAP_RECT"] = MINIMAP_RECT
    data["JUMP_RISE"] = JUMP_RISE
    data["GAME_MONITOR"] = GAME_MONITOR
    try:
        SETTINGS_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")
    except Exception as e:
        print("Couldn't save settings:", e)


def make_panel(root, tracker, visible=True):
    BG, CARD, FG, MUTED, GOOD, WARN = "#1d1f24", "#272a31", "#e9e9ec", "#9ca0a8", "#3ecf6e", "#f0b429"
    user32 = ctypes.windll.user32

    win = tk.Toplevel(root)
    win.title("Fishing helper")
    win.configure(bg=BG)
    win.attributes("-topmost", True)
    win.minsize(480, 0)
    win.protocol("WM_DELETE_WINDOW", lambda: set_visible(False))  # X hides it; F3 shows it again

    st = ttk.Style(win)
    st.theme_use("clam")
    st.configure(".", background=BG, foreground=FG, fieldbackground=CARD, font=("Segoe UI", 10))
    st.configure("Card.TFrame", background=CARD)
    st.configure("Card.TLabel", background=CARD, foreground=FG)
    st.configure("Muted.TLabel", background=CARD, foreground=MUTED, font=("Segoe UI", 9))
    st.configure("Head.TLabel", background=BG, foreground=MUTED, font=("Segoe UI", 9, "bold"))
    st.configure("Status.TLabel", background=CARD, font=("Segoe UI", 18, "bold"))
    st.configure("TButton", background=CARD, foreground=FG, borderwidth=0, padding=(10, 6))
    st.map("TButton", background=[("active", "#353943")])
    st.configure("Go.TButton", background="#2f6f47")
    st.map("Go.TButton", background=[("active", "#3a8a58")])
    st.configure("TCheckbutton", background=BG, foreground=FG)
    st.map("TCheckbutton", background=[("active", BG)])
    st.configure("Horizontal.TScale", background=BG, troughcolor=CARD)
    st.configure("TNotebook", background=BG, borderwidth=0, tabmargins=(12, 6, 12, 0))
    st.configure("TNotebook.Tab", background=CARD, foreground=MUTED, padding=(18, 7), borderwidth=0,
                 font=("Segoe UI", 10, "bold"))
    st.map("TNotebook.Tab", background=[("selected", "#2f6f47")], foreground=[("selected", FG)])

    state = {"visible": visible}

    def set_visible(v):
        state["visible"] = v
        (win.deiconify if v else win.withdraw)()
        save_settings(tracker, v)

    def refocus():
        if tracker.game_hwnd:
            user32.SetForegroundWindow(tracker.game_hwnd)

    def save_soon():
        if state.get("save_job"):
            win.after_cancel(state["save_job"])
        state["save_job"] = win.after(400, lambda: save_settings(tracker, state["visible"]))

    def ask(flag):
        setattr(tracker, flag, True)
        refocus()

    # ================= shared top: status + start/pause + quit =================
    card = ttk.Frame(win, style="Card.TFrame", padding=12)
    card.pack(fill="x", padx=12, pady=(12, 6))
    status = ttk.Label(card, text="PAUSED", style="Status.TLabel")
    status.pack(anchor="w")
    detail = ttk.Label(card, text="", style="Muted.TLabel")
    detail.pack(anchor="w")
    setup = ttk.Label(card, text="", style="Muted.TLabel")
    setup.pack(anchor="w", pady=(4, 0))

    def start_pause():
        if tracker.cfg is None and MODE == "fishing" and not tracker.active:
            log("Select the fishing minigame first (Fishing tab: Select minigame / F9)")
            return
        tracker.active = not tracker.active
        log("ACTIVE" if tracker.active else "PAUSED")
        refocus()

    top = ttk.Frame(win)
    top.pack(fill="x", padx=12, pady=(0, 4))
    start_btn = ttk.Button(top, text="Start  (F8)", style="Go.TButton", command=start_pause)
    start_btn.pack(side="left")
    ttk.Button(top, text="Quit (F10)", command=lambda: setattr(tracker, "quit", True)).pack(side="right")
    with MSS() as s_:
        mons_ = s_.monitors[1:]
    screen_names = ["Game screen: auto"] + [f"Game screen: {i} ({m['width']}x{m['height']})"
                                             for i, m in enumerate(mons_, 1)]
    screen_var = tk.StringVar(value=screen_names[GAME_MONITOR] if GAME_MONITOR < len(screen_names) else screen_names[0])
    screen_box = ttk.Combobox(top, textvariable=screen_var, values=screen_names, state="readonly", width=30)
    screen_box.pack(side="right", padx=8)

    def screen_changed(_=None):
        i = screen_names.index(screen_var.get())
        globals()["GAME_MONITOR"] = i
        tracker.hold(None)
        log(("Game screen: auto" if i == 0 else f"Game screen: {i}")
            + " - if the game moved screens, pick the minimap / fishing minigame / character again on it")
        save_soon()

    screen_box.bind("<<ComboboxSelected>>", screen_changed)

    # ================= one page per minigame =================
    nb = ttk.Notebook(win)
    nb.pack(fill="x", padx=8, pady=(4, 0))
    pages = {m: ttk.Frame(nb, padding=(6, 8)) for m in MODES}
    nb.add(pages["fishing"], text="  Fishing  ")
    nb.add(pages["mining"], text="  Mining  ")
    nb.add(pages["combat"], text="  Combat  ")
    nb.select(MODES.index(MODE))

    def tab_changed(_=None):
        m = MODES[nb.index(nb.select())]
        if m != MODE:
            globals()["MODE"] = m
            tracker.hold(None)
            log(f"Mode: {MODE}")
            save_soon()

    nb.bind("<<NotebookTabChanged>>", tab_changed)

    # shared on/off switches (the same switch can show up on both pages)
    toggle_vars = {name: tk.BooleanVar(value=tracker.manual if name == "MANUAL_MODE" else bool(globals()[name]))
                   for name in TOGGLES}

    def toggle_changed(name):
        var = toggle_vars[name]
        if name == "MANUAL_MODE":
            tracker.manual = var.get()
            log("Fishing manual mode ON - catch + recast only, no moving" if tracker.manual
                else "Fishing manual mode OFF")
        else:
            globals()[name] = var.get()
        save_soon()

    def add_toggles(parent, names):
        ttk.Label(parent, text="OPTIONS", style="Head.TLabel").pack(anchor="w", padx=6, pady=(10, 2))
        for name in names:
            ttk.Checkbutton(parent, text=TOGGLES[name], variable=toggle_vars[name],
                            command=lambda n=name: toggle_changed(n)).pack(anchor="w", padx=6)

    def add_keys(parent, page):
        """KEYS: type a key (y, 6, f...) or a mouse button (mouse1..mouse5), then Enter."""
        ttk.Label(parent, text="KEYS  (a key like y / 6, or mouse1-mouse5; Enter to apply)",
                  style="Head.TLabel").pack(anchor="w", padx=6, pady=(10, 2))
        grid = ttk.Frame(parent)
        grid.pack(fill="x", padx=6)
        for i, (name, (label, pages_)) in enumerate([kv for kv in KEY_SETTINGS.items() if page in kv[1][1]]):
            var = tk.StringVar(value=globals()[name])
            ent = ttk.Entry(grid, textvariable=var, width=10)
            status = ttk.Label(grid, text="", width=12)

            def apply(_=None, name=name, var=var, status=status):
                v = var.get().strip().lower()
                if (v == "" and name in OPTIONAL_KEYS) or valid_key(v):
                    globals()[name] = v
                    var.set(v)
                    status.configure(text="ok")
                    log(f"Key for '{KEY_SETTINGS[name][0]}': {v.upper() if v else 'off'}")
                    save_soon()
                else:
                    status.configure(text="unknown key")
                    var.set(globals()[name])

            ent.bind("<Return>", apply)
            ent.bind("<FocusOut>", apply)
            ttk.Label(grid, text=label).grid(row=i, column=0, sticky="w", pady=2)
            ent.grid(row=i, column=1, sticky="w", padx=8)
            status.grid(row=i, column=2, sticky="w")

    sliders = {}

    def add_sliders(parent, names):
        ttk.Label(parent, text="TUNING", style="Head.TLabel").pack(anchor="w", padx=6, pady=(10, 2))
        grid = ttk.Frame(parent)
        grid.pack(fill="x", padx=6)
        grid.columnconfigure(1, weight=1)
        for i, name in enumerate(names):
            label, lo, hi, step = TUNABLES[name]
            cur = tracker.lead if name == "LEAD" else globals()[name]
            var = tk.DoubleVar(value=cur)
            shown = ttk.Label(grid, width=6, anchor="e")
            fmt = (lambda v: f"{v:.2f}") if step < 1 else (lambda v: f"{v:.0f}")
            shown.configure(text=fmt(cur))

            def moved(_=None, name=name, var=var, shown=shown, fmt=fmt, step=step):
                v = round(var.get() / step) * step
                v = round(v, 2) if step < 1 else int(v)
                shown.configure(text=fmt(v))
                if name == "LEAD":
                    tracker.lead = v
                else:
                    globals()[name] = v
                save_soon()

            ttk.Label(grid, text=label).grid(row=i, column=0, sticky="w", pady=2)
            ttk.Scale(grid, from_=lo, to=hi, variable=var, command=moved).grid(row=i, column=1, sticky="ew", padx=8)
            shown.grid(row=i, column=2, sticky="e")
            sliders[name] = (var, shown)

    # ---------------- Fishing page ----------------
    fp = pages["fishing"]
    r = ttk.Frame(fp)
    r.pack(fill="x", padx=6)
    ttk.Button(r, text="Select minigame (F9)", command=lambda: ask("reselect")).pack(side="left")
    ttk.Button(r, text="Set anchor (F5)", command=lambda: ask("set_anchor")).pack(side="left", padx=6)
    ttk.Button(r, text="Pick '!' area (F11)", command=lambda: ask("select_excl")).pack(side="left")
    add_toggles(fp, ["MANUAL_MODE", "WATCH_WHOLE_SCREEN", "WANDER_ENABLED", "ANCHOR_ENABLED",
                     "CRYSTAL_ENABLED", "BUFF_ENABLED", "HP_SAFETY", "CRYSTAL_VEIL", "YELLOW_DIAGNOSTICS"])
    add_sliders(fp, ["LEAD", "DEADZONE_PX", "FULL_PRESS_PX", "WANDER_EVERY", "CHECK_TIMEOUT", "IDLE_RECAST",
                     "BUFF_EVERY", "HP_LOW"])
    add_keys(fp, "fishing")

    # ---------------- Mining page ----------------
    mp = pages["mining"]
    mr = ttk.Frame(mp)
    mr.pack(fill="x", padx=6)
    ttk.Label(mr, text="How:").pack(side="left")

    def set_mine_auto(v):
        globals()["MINE_AUTO"] = v
        toggle_vars["MINE_AUTO"].set(v)
        tracker.hold(None)
        log("Mining: AUTO - reveal ores, walk to them, press E, solve the menus" if v
            else "Mining: MANUAL - you press E, I solve the ore menu and the crystal symbols")
        save_soon()

    mine_btns = {True: ttk.Button(mr, text="Auto", command=lambda: set_mine_auto(True)),
                 False: ttk.Button(mr, text="Manual (you press E)", command=lambda: set_mine_auto(False))}
    mine_btns[True].pack(side="left", padx=(8, 0))
    mine_btns[False].pack(side="left", padx=(6, 0))
    add_toggles(mp, ["CRYSTAL_ENABLED", "BUFF_ENABLED", "HP_SAFETY", "CRYSTAL_VEIL", "YELLOW_DIAGNOSTICS"])
    add_sliders(mp, ["ORE_ON_PX", "ORE_MATCH", "BUFF_EVERY", "HP_LOW"])
    add_keys(mp, "mining")

    # ---------------- Combat page ----------------
    cp = pages["combat"]
    ttk.Label(cp, text="Runs left and right holding both attacks down; presses the buff (then the veil) on its timer. "
                       "Darkness crystals: stops, solves it, comes back and keeps fighting.",
              wraplength=520).pack(anchor="w", padx=6)
    add_toggles(cp, ["CRYSTAL_ENABLED", "BUFF_ENABLED", "HP_SAFETY", "CRYSTAL_VEIL"])
    add_sliders(cp, ["COMBAT_RUN", "BUFF_EVERY", "HP_LOW", "HP_RESUME"])
    add_keys(cp, "combat")
    ttk.Label(mp, text="ORES TO MINE  (click to switch on/off)", style="Head.TLabel").pack(anchor="w", padx=6, pady=(10, 2))
    gallery = tk.Frame(mp, bg=BG)
    gallery.pack(fill="x", padx=6)
    ttk.Label(mp, text="SETUP", style="Head.TLabel").pack(anchor="w", padx=6, pady=(10, 2))
    sr = ttk.Frame(mp)
    sr.pack(fill="x", padx=6)
    ttk.Button(sr, text="Pick my character", command=lambda: ask("pick_char")).pack(side="left")
    ttk.Button(sr, text="Pick minimap", command=lambda: ask("pick_minimap")).pack(side="left", padx=6)
    ttk.Button(sr, text="Test jump", command=lambda: ask("test_jump")).pack(side="left")

    def thumb(img):
        scale = 56 / img.shape[0]
        big = cv2.resize(img, None, fx=scale, fy=scale, interpolation=cv2.INTER_NEAREST)
        ok, buf = cv2.imencode(".png", big)
        return tk.PhotoImage(data=base64.b64encode(buf.tobytes()))

    def toggle_ore(name):
        if name in ORES_DISABLED:
            ORES_DISABLED.remove(name)
        else:
            ORES_DISABLED.append(name)
        build_gallery()
        save_soon()

    def build_gallery():
        for c in gallery.winfo_children():
            c.destroy()
        state["thumbs"] = []
        for ore in ORE_LIST:
            on = ore["name"] not in ORES_DISABLED
            tile = tk.Frame(gallery, bg=GOOD if on else CARD, padx=3, pady=3, cursor="hand2")
            img = thumb(ore["img"])
            state["thumbs"].append(img)
            pic = tk.Label(tile, image=img, bg=CARD)
            pic.pack()
            cap = tk.Label(tile, text=ore["name"] + ("" if on else "  (off)"), bg=CARD,
                           fg=FG if on else MUTED, font=("Segoe UI", 8))
            cap.pack(fill="x")
            for w in (tile, pic, cap):
                w.bind("<Button-1>", lambda e, n=ore["name"]: toggle_ore(n))
            tile.pack(side="left", padx=(0, 8))
        ttk.Button(gallery, text="+ Add ore", command=lambda: ask("add_ore")).pack(side="left", pady=8)
        state["ores_ver"] = ORES_VERSION

    build_gallery()

    # ================= shared bottom: log =================
    ttk.Label(win, text="LOG", style="Head.TLabel").pack(anchor="w", padx=14, pady=(10, 2))
    logbox = scrolledtext.ScrolledText(win, height=10, bg=CARD, fg=FG, insertbackground=FG,
                                       relief="flat", font=("Consolas", 9), wrap="word")
    logbox.pack(fill="both", expand=True, padx=12)
    logbox.configure(state="disabled")
    ttk.Label(win, text="F2 next mode   ·   F3 show/hide   ·   F4 fishing manual   ·   F8 start/pause   ·   F10 quit",
              style="Head.TLabel").pack(pady=(4, 10))

    win.update()
    hwnd = user32.GetParent(win.winfo_id()) or win.winfo_id()
    user32.SetWindowDisplayAffinity(hwnd, 0x11)  # keep the panel out of the script's screenshots
    if not visible:
        win.withdraw()

    def refresh():
        if tracker.quit:
            return
        fg = user32.GetForegroundWindow()  # remember the game window, so buttons can hand focus back
        if fg and fg != hwnd:
            tracker.game_hwnd = fg
        if tracker.toggle_panel:
            tracker.toggle_panel = False
            set_visible(not state["visible"])
        chunks = []
        while not LOG_QUEUE.empty():
            chunks.append(LOG_QUEUE.get_nowait())
        if chunks:
            logbox.configure(state="normal")
            logbox.insert("end", "".join(chunks))
            lines = int(logbox.index("end-1c").split(".")[0])
            if lines > 400:
                logbox.delete("1.0", f"{lines - 400}.0")
            logbox.see("end")
            logbox.configure(state="disabled")
        # status
        if MODE == "mining":
            sub = "MINING · " + ("AUTO" if MINE_AUTO else "MANUAL")
        elif MODE == "combat":
            sub = "COMBAT"
        else:
            sub = "FISHING" + (" · MANUAL" if tracker.manual else "")
        status.configure(text=("ACTIVE" if tracker.active else "PAUSED") + "  ·  " + sub,
                         foreground=GOOD if tracker.active else MUTED)
        start_btn.configure(text="Pause  (F8)" if tracker.active else "Start  (F8)")
        bits = [f"{tracker.fps:.0f} fps", f"holding {(tracker.held or '-').upper()}"]
        if HP_SAFETY and tracker.hp_frac is not None:
            bits.append(f"HP {tracker.hp_frac * 100:.0f}%" + (" (healing)" if tracker.healing else ""))
        if tracker.armed:
            bits.append("click in the game to capture the minigame")
        elif tracker.yellow_px is not None:
            bits.append("waiting for the '!'")
        detail.configure(text="   ·   ".join(bits))
        tick = lambda ok: "✓" if ok else "—"
        if MODE == "combat":
            setup.configure(text=f"Combat: hold {COMBAT_ATTACK_1 or '-'} + {COMBAT_ATTACK_2 or '-'}, run "
                                 f"{COMBAT_LEFT.upper()}/{COMBAT_RIGHT.upper()} every {COMBAT_RUN:.1f} s, "
                                 f"buff {BUFF_KEY.upper()} every {BUFF_EVERY:.0f} s" + ("" if BUFF_ENABLED else " (off)"),
                            foreground=FG)
        elif MODE == "mining":
            n_on = sum(o["name"] not in ORES_DISABLED for o in ORE_LIST)
            if not MINE_AUTO:
                setup.configure(text="Manual: press E on an ore or crystal - I'll solve its minigame", foreground=FG)
            elif tracker.char is None:
                setup.configure(text="Auto mining needs your character: Mining tab → Pick my character", foreground=WARN)
            else:
                setup.configure(text=f"Auto: {n_on} ore type(s), character ✓, minimap {tick(MINIMAP_RECT)}",
                                foreground=FG if n_on else WARN)
        else:
            setup.configure(text=f"Minigame {tick(tracker.cfg is not None)}    Anchor {tick(tracker.anchor is not None)}"
                                 f"    '!' area {tick(tracker.excl_area is not None)}"
                                 + ("" if tracker.cfg is not None else "    ← Select minigame first"),
                            foreground=FG if tracker.cfg is not None else WARN)
        want = MODES.index(MODE)
        if nb.index(nb.select()) != want:  # F2 pressed
            nb.select(want)
        for v, btn in mine_btns.items():  # the active mining style is the green one
            btn.configure(style="Go.TButton" if v == bool(MINE_AUTO) else "TButton")
        if getattr(tracker, "settings_dirty", False):  # minimap picked / jump measured: remember it
            tracker.settings_dirty = False
            save_soon()
        if state.get("ores_ver") != ORES_VERSION:  # an ore was added
            build_gallery()
        if toggle_vars["MANUAL_MODE"].get() != tracker.manual:  # F4
            toggle_vars["MANUAL_MODE"].set(tracker.manual)
        if abs(sliders["LEAD"][0].get() - tracker.lead) > 0.004:  # F6/F7
            sliders["LEAD"][0].set(tracker.lead)
            sliders["LEAD"][1].configure(text=f"{tracker.lead:.2f}")
        win.after(150, refresh)

    refresh()
    return win


def main():
    sys.stdout, sys.stderr = _Tee(sys.stdout), _Tee(sys.stderr)  # mirror output into the panel
    settings = load_settings()
    load_ores()
    tracker = Tracker()
    tracker.toggle_panel = False
    tracker.game_hwnd = None
    saved = load_selection()
    if saved:
        tracker.cfg, tracker.mon, tracker.excl_area, tracker.anchor, tracker.char = saved
        if tracker.excl_area is not None and tracker.char is None:
            print("Tip: press F11 again to also pick your character, so the '!' area follows you.")
        if tracker.anchor is not None and "strips" not in tracker.anchor:
            tracker.anchor = None  # older anchor format
        if tracker.anchor is not None:
            print("Loaded anchor point too.")
        print(f"Loaded saved selection from {SAVE_FILE}  (F9 to redo it)")

    def on_press(key):
        if getattr(key, "char", None) in ("e", "E"):
            tracker.user_e_at = time.perf_counter()  # manual modes: a crystal minigame may open now
        if key == keyboard.Key.f8 and (tracker.cfg is not None or MODE in ("mining", "combat")):
            tracker.active = not tracker.active
            print("ACTIVE" if tracker.active else "PAUSED")
        elif key in (keyboard.Key.f6, keyboard.Key.f7):
            step = 0.02 if key == keyboard.Key.f7 else -0.02
            tracker.lead = round(min(1.0, max(0.0, tracker.lead + step)), 2)
            print(f"lead = {tracker.lead:.2f}")
        elif key == keyboard.Key.f9:
            tracker.reselect = True
        elif key == keyboard.Key.f2:
            globals()["MODE"] = MODES[(MODES.index(MODE) + 1) % len(MODES)]
            tracker.hold(None)
            log(f"Mode: {MODE}")
        elif key == keyboard.Key.f3:
            tracker.toggle_panel = True
        elif key == keyboard.Key.f4:
            tracker.manual = not tracker.manual
            log("Manual mode ON - catch + recast only, no moving" if tracker.manual
                else "Manual mode OFF - A/D taps, walk-arounds and anchor are back")
        elif key == keyboard.Key.f5:
            tracker.set_anchor = True
        elif key == keyboard.Key.f11:
            tracker.select_excl = True
        elif key == keyboard.Key.f10:
            tracker.quit = True
            return False

    listener = keyboard.Listener(on_press=on_press)
    listener.start()
    worker = threading.Thread(target=tracker.run, daemon=True)
    worker.start()

    print("F9 = select target   F11 = select the '!' area above your head   F4 = manual mode (no moving)   F5 = set anchor (stand where you fish)   F8 = start/pause   F10 = quit")
    if tracker.excl_area is None:
        print("No '!' area yet - press F11 and drag a box over the spot above your head.")
    root = make_overlay(tracker)
    make_panel(root, tracker, visible=True)  # always show at start (F3 / X hide it until next start)
    threads = {"worker": worker, "listener": listener}

    def supervise():
        # last line of defense: restart the loop or the hotkey listener if either died
        if tracker.quit:
            return
        if not threads["worker"].is_alive():
            log("Tracking loop stopped - restarting it")
            threads["worker"] = threading.Thread(target=tracker.run, daemon=True)
            threads["worker"].start()
        if not threads["listener"].is_alive():
            log("Hotkey listener stopped - restarting it")
            threads["listener"] = keyboard.Listener(on_press=on_press)
            threads["listener"].start()
        root.after(2000, supervise)

    root.after(2000, supervise)
    try:
        root.mainloop()
    finally:
        tracker.quit = True
        threads["worker"].join(timeout=1)
        tracker.hold(None)


if __name__ == "__main__":
    main()
