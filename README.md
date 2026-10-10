# Soul's Remnant helper

Fishing, mining and combat helper with a settings panel (F3).

## Setup on a new computer
1. Install Python 3.12 from python.org (tick "Add python.exe to PATH").
2. In this folder, run:
   ```
   pip install -r requirements.txt
   ```
3. Start it:
   ```
   python box_tracker.py
   ```
4. In the panel, pick the **Game screen**, then set things up again for this screen
   (they're saved per computer, not in this repo):
   - Fishing tab: **Select minigame (F9)**, and the anchor (F5) / '!' area (F11) if you use them
   - Mining tab: **Pick minimap**, **Pick my character**
   - Check the **KEYS** on each tab (buff, veil, dash, attacks...)

## Keys
F2 next mode · F3 show/hide panel · F4 fishing manual · F8 start/pause · F10 quit

## Learned data (shared through this repo)
- `crystal_symbols/` – crystal minigame symbols it learned (keeps getting better)
- `digits/`, `ores/` – mining numbers and ore pictures
