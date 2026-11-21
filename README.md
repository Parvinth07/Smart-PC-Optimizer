# ⚡ Smart PC Optimizer & Autopilot

A lightweight, animated Windows system monitor and performance optimizer built with Python. Designed to keep RAM and CPU overhead minimal while automating background cleanup, game-mode resource protection, and process hibernation.

## ✨ Key Features
- **Live Animated Dashboard:** Real-time CPU & RAM tracking with dynamic stress alerts.
- **Smart Game Mode:** Automatically detects full-screen games, pauses background pop-ups/cleaners during gameplay, and cleans temp files after you exit.
- **Process Freeze & Thaw:** Suspend heavy background apps (`0% CPU`) without losing open tabs or unsaved work, and resume them anytime.
- **60-Second Lag Forensics:** Tracks recent spikes to answer *"Why did my PC just lag?"* with one-click fixes.
- **Ambient Edge Status Glow & Panic Hotkey:** Unobtrusive screen-edge health indicator and `Ctrl + Shift + Space` emergency RAM rescue.
- **Startup & App Manager:** Toggle Windows startup items and manage running sub-processes effortlessly.

## 🚀 How to Run (No Coding Required)
1. Go to the **[Releases](../../releases)** section on the right side of this page.
2. Download **`SmartPCOptimizer.exe`**.
3. Double-click to run (Windows SmartScreen may ask for confirmation since it's an independent open-source app—click *More info* → *Run anyway*).

## 🛠️ Built With
- Python, CustomTkinter, psutil, Winotify, PyInstaller
