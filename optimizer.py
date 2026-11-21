from collections import deque
import ctypes
from ctypes import wintypes
import gc
import math
import os
import tempfile
import threading
import time
import tkinter as tk
import traceback
import winreg
import customtkinter as ctk
import psutil
import pystray
from PIL import Image, ImageDraw
from winotify import Notification, audio

try:
    import keyboard
except ImportError:
    keyboard = None

# Critical Windows processes strictly protected from being listed, frozen, or closed
PROTECTED_PROCESSES = {
    "system",
    "system idle process",
    "idle",
    "registry",
    "memory compression",
    "memcompression",
    "ntoskrnl.exe",
    "smss.exe",
    "csrss.exe",
    "wininit.exe",
    "services.exe",
    "lsass.exe",
    "lsaiso.exe",
    "svchost.exe",
    "winlogon.exe",
    "dwm.exe",
    "explorer.exe",
    "fontdrvhost.exe",
    "sihost.exe",
    "taskhostw.exe",
    "ctfmon.exe",
    "runtimebroker.exe",
    "searchindexer.exe",
    "searchhost.exe",
    "startmenuexperiencehost.exe",
    "shellexperiencehost.exe",
    "securityhealthservice.exe",
    "securityhealthsystray.exe",
    "msmpeng.exe",
    "nissrv.exe",
    "audiodg.exe",
    "spoolsv.exe",
    "conhost.exe",
    "wudfhost.exe",
    "sgrmbroker.exe",
    "dllhost.exe",
    "textinputhost.exe",
    "widgetservice.exe",
    "dashost.exe",
    "wmiprvse.exe",
    "taskmgr.exe",
}

# Kernel pseudo-processes ignored during Lag Forensics culprit attribution
IGNORED_CULPRIT_NAMES = {
    "system idle process",
    "idle",
    "system",
}

# Windows desktop/shell window classes that must NOT trigger Game Mode
IGNORED_FULLSCREEN_CLASSES = {
    "progman",
    "workerw",
    "shell_traywnd",
    "shell_secondarytraywnd",
    "notifyiconoverflowwindow",
    "windows.ui.core.corewindow",
}

# Windows Registry paths for current-user startup apps (non-destructive toggling)
HKCU_RUN_PATH = r"Software\Microsoft\Windows\CurrentVersion\Run"
HKCU_STARTUP_APPROVED_PATH = (
    r"Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run"
)

# Theme Palette (Modern Dark Gaming / System Utility)
BG_WINDOW = "#0D1017"
BG_CARD = "#151A25"
BG_INNER = "#0F131C"
BG_ROW = "#1B2232"
BG_ROW_FROZEN = "#12324A"        # Icy blue tint for suspended apps
BORDER_FROZEN = "#38BDF8"        # Crisp frost-cyan border for frozen rows
BG_SUBPANEL = "#111622"
BG_SUBROW = "#171F30"
BORDER_SUBTLE = "#242D42"
TEXT_PRIMARY = "#F8FAFC"
TEXT_MUTED = "#94A3B8"

CURRENT_PID = os.getpid()
TOP_APPS_COUNT = 10
STATS_REFRESH_MS = 2000          # Poll CPU/RAM every 2 seconds while window is open
APPS_REFRESH_MS = 2000           # Refresh Top RAM list & lag sample every 2 seconds
LAG_BUFFER_MAXLEN = 30           # 30 samples x 2 seconds = 60-second rolling buffer
TRAY_LAG_SAMPLE_MS = 2000        # Lightweight tray lag sampling when Lag Recorder is ON
TRAY_RAM_CHECK_MS = 15000        # Check RAM every 15 seconds while minimized to tray
GAME_MODE_POLL_MS = 3000         # Lightweight Win32 fullscreen check every 3 seconds
POST_GAME_CLEAN_DELAY_MS = 10000 # Wait 10 seconds on desktop before post-game cleanup
EDGE_GLOW_POLL_MS = 2000         # Edge glow telemetry check every 2 seconds when ON
EDGE_GLOW_ANIM_MS = 75           # Lightweight ~13 FPS fade/pulse for 3px edge glow
IDLE_CHECK_MS = 15000            # Check mouse/keyboard idle time every 15 seconds when ON
IDLE_TRIGGER_SECONDS = 600.0     # 10 continuous minutes of inactivity triggers Away-Clean
IDLE_RETURN_SECONDS = 30.0       # Activity within 30s marks user as returned
AUTO_CLEAN_THRESHOLD = 85.0      # Auto-clean temp files when tray RAM exceeds 85%
AUTO_CLEAN_COOLDOWN_SEC = 300    # 5-minute cooldown if RAM remains above 85%
PANIC_HOTKEY_COMBO = "ctrl+shift+space"
PANIC_DEBOUNCE_SEC = 4.0         # Prevent accidental rapid double-triggers
ANIM_INTERVAL_MS = 33            # ~30 FPS glide animation (pauses automatically when settled)
ANIM_SMOOTHING = 0.20            # Smooth ease-out speed for circular gauges
BOOST_ANIM_INTERVAL_MS = 35      # Smooth sweeping/pulsing animation while boosting
EXPAND_ANIM_STEPS = 7            # Smooth slide open/close animation frames
EXPAND_ANIM_STEP_MS = 20         # ~140ms total expand/collapse duration
FADE_ANIM_STEPS = 6              # Subtle fade/collapse frames on process close
FADE_ANIM_STEP_MS = 28           # ~168ms total fade duration
MODAL_ANIM_STEPS = 8             # Smooth modal entrance/exit animation frames
MODAL_ANIM_STEP_MS = 18          # ~144ms modal fade + glide
SPINNER_FRAMES = ("⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏")


# ----------------------------------------------------------------------
# Isolated Windows Win32 Helpers (Fullscreen, Click-Through, Idle Time)
# ----------------------------------------------------------------------
MONITOR_DEFAULTTONEAREST = 2
GWL_EXSTYLE = -20
WS_EX_TRANSPARENT = 0x00000020
WS_EX_TOOLWINDOW = 0x00000080
WS_EX_LAYERED = 0x00080000
WS_EX_NOACTIVATE = 0x08000000
HWND_TOPMOST = -1
SWP_NOSIZE = 0x0001
SWP_NOMOVE = 0x0002
SWP_NOACTIVATE = 0x0010
SWP_FRAMECHANGED = 0x0020


class MONITORINFO(ctypes.Structure):
    _fields_ = [
        ("cbSize", wintypes.DWORD),
        ("rcMonitor", wintypes.RECT),
        ("rcWork", wintypes.RECT),
        ("dwFlags", wintypes.DWORD),
    ]


class LASTINPUTINFO(ctypes.Structure):
    _fields_ = [
        ("cbSize", wintypes.UINT),
        ("dwTime", wintypes.DWORD),
    ]


_user32 = None
_kernel32 = None
_get_window_long_ptr = None
_set_window_long_ptr = None
_CLASS_NAME_BUF = ctypes.create_unicode_buffer(256)

try:
    # Isolated WinDLL instances prevent argtype collisions with pystray/customtkinter/keyboard
    _user32 = ctypes.WinDLL("user32")
    _kernel32 = ctypes.WinDLL("kernel32")

    _user32.GetForegroundWindow.restype = wintypes.HWND
    _user32.GetDesktopWindow.restype = wintypes.HWND
    _user32.GetShellWindow.restype = wintypes.HWND
    _user32.GetParent.argtypes = [wintypes.HWND]
    _user32.GetParent.restype = wintypes.HWND
    _user32.IsWindowVisible.argtypes = [wintypes.HWND]
    _user32.IsWindowVisible.restype = wintypes.BOOL
    _user32.IsIconic.argtypes = [wintypes.HWND]
    _user32.IsIconic.restype = wintypes.BOOL
    _user32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    _user32.GetClassNameW.restype = ctypes.c_int
    _user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    _user32.GetWindowThreadProcessId.restype = wintypes.DWORD
    _user32.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
    _user32.GetWindowRect.restype = wintypes.BOOL
    _user32.MonitorFromWindow.argtypes = [wintypes.HWND, wintypes.DWORD]
    _user32.MonitorFromWindow.restype = wintypes.HMONITOR
    _user32.GetMonitorInfoW.argtypes = [wintypes.HMONITOR, ctypes.POINTER(MONITORINFO)]
    _user32.GetMonitorInfoW.restype = wintypes.BOOL
    _user32.GetLastInputInfo.argtypes = [ctypes.POINTER(LASTINPUTINFO)]
    _user32.GetLastInputInfo.restype = wintypes.BOOL
    _user32.SetWindowPos.argtypes = [
        wintypes.HWND,
        wintypes.HWND,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        wintypes.UINT,
    ]
    _user32.SetWindowPos.restype = wintypes.BOOL

    if hasattr(_user32, "GetWindowLongPtrW") and hasattr(_user32, "SetWindowLongPtrW"):
        _get_window_long_ptr = _user32.GetWindowLongPtrW
        _get_window_long_ptr.argtypes = [wintypes.HWND, ctypes.c_int]
        _get_window_long_ptr.restype = ctypes.c_ssize_t
        _set_window_long_ptr = _user32.SetWindowLongPtrW
        _set_window_long_ptr.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t]
        _set_window_long_ptr.restype = ctypes.c_ssize_t
    else:
        _get_window_long_ptr = _user32.GetWindowLongW
        _get_window_long_ptr.argtypes = [wintypes.HWND, ctypes.c_int]
        _get_window_long_ptr.restype = ctypes.c_long
        _set_window_long_ptr = _user32.SetWindowLongW
        _set_window_long_ptr.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
        _set_window_long_ptr.restype = ctypes.c_long

    _kernel32.GetTickCount.restype = wintypes.DWORD
except Exception:
    _user32 = None
    _kernel32 = None


def get_foreground_pid():
    """Return the PID of the currently focused Windows application, or 0."""
    if _user32 is None:
        return 0
    try:
        hwnd = _user32.GetForegroundWindow()
        if not hwnd:
            return 0
        fg_pid = wintypes.DWORD(0)
        _user32.GetWindowThreadProcessId(hwnd, ctypes.byref(fg_pid))
        return int(fg_pid.value)
    except Exception:
        return 0


def is_fullscreen_app_running():
    """Return True if a non-desktop foreground window covers its full monitor."""
    if _user32 is None:
        return False
    try:
        hwnd = _user32.GetForegroundWindow()
        if not hwnd:
            return False

        if hwnd == _user32.GetDesktopWindow() or hwnd == _user32.GetShellWindow():
            return False
        if not _user32.IsWindowVisible(hwnd) or _user32.IsIconic(hwnd):
            return False

        fg_pid = wintypes.DWORD(0)
        _user32.GetWindowThreadProcessId(hwnd, ctypes.byref(fg_pid))
        if fg_pid.value == CURRENT_PID:
            return False

        class_len = _user32.GetClassNameW(hwnd, _CLASS_NAME_BUF, 256)
        if class_len > 0 and _CLASS_NAME_BUF.value.lower() in IGNORED_FULLSCREEN_CLASSES:
            return False

        win_rect = wintypes.RECT()
        if not _user32.GetWindowRect(hwnd, ctypes.byref(win_rect)):
            return False

        hmonitor = _user32.MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST)
        mon_info = MONITORINFO()
        mon_info.cbSize = ctypes.sizeof(MONITORINFO)

        if hmonitor and _user32.GetMonitorInfoW(hmonitor, ctypes.byref(mon_info)):
            m = mon_info.rcMonitor
            mon_left, mon_top, mon_right, mon_bottom = m.left, m.top, m.right, m.bottom
        else:
            mon_left, mon_top = 0, 0
            mon_right = _user32.GetSystemMetrics(0)
            mon_bottom = _user32.GetSystemMetrics(1)

        if (mon_right - mon_left) <= 0 or (mon_bottom - mon_top) <= 0:
            return False

        tolerance = 2
        return (
            win_rect.left <= mon_left + tolerance
            and win_rect.top <= mon_top + tolerance
            and win_rect.right >= mon_right - tolerance
            and win_rect.bottom >= mon_bottom - tolerance
        )
    except Exception:
        return False


def get_system_idle_seconds():
    """Return seconds elapsed since the last mouse or keyboard input on Windows."""
    if _user32 is None or _kernel32 is None:
        return 0.0
    try:
        lii = LASTINPUTINFO()
        lii.cbSize = ctypes.sizeof(LASTINPUTINFO)
        if not _user32.GetLastInputInfo(ctypes.byref(lii)):
            return 0.0
        tick_now = _kernel32.GetTickCount()
        elapsed_ms = (tick_now - lii.dwTime) & 0xFFFFFFFF
        return elapsed_ms / 1000.0
    except Exception:
        return 0.0


def apply_click_through_style(tk_window):
    """Make a Tkinter Toplevel completely click-through, non-activating, and hidden from Alt+Tab."""
    if _user32 is None or _get_window_long_ptr is None or _set_window_long_ptr is None:
        return
    try:
        tk_window.update_idletasks()
        wid = tk_window.winfo_id()
        parent_hwnd = _user32.GetParent(wid)
        hwnd = parent_hwnd if parent_hwnd else wid
        if not hwnd:
            return

        ex_style = _get_window_long_ptr(hwnd, GWL_EXSTYLE)
        new_style = (
            ex_style
            | WS_EX_LAYERED
            | WS_EX_TRANSPARENT
            | WS_EX_TOOLWINDOW
            | WS_EX_NOACTIVATE
        )
        _set_window_long_ptr(hwnd, GWL_EXSTYLE, new_style)
        _user32.SetWindowPos(
            hwnd,
            HWND_TOPMOST,
            0,
            0,
            0,
            0,
            SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_FRAMECHANGED,
        )
    except Exception:
        pass


def format_bytes(size_bytes):
    """Convert raw bytes into a clean, human-readable string."""
    size = float(max(size_bytes, 0))
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024.0 or unit == "TB":
            return f"{size:.1f} {unit}" if unit != "B" else f"{int(size)} B"
        size /= 1024.0
    return "0 B"


def hex_to_rgb(hex_color):
    value = hex_color.lstrip("#")
    return int(value[0:2], 16), int(value[2:4], 16), int(value[4:6], 16)


def rgb_to_hex(rgb):
    r, g, b = (max(0, min(255, int(c))) for c in rgb)
    return f"#{r:02x}{g:02x}{b:02x}"


def blend_hex(fg_hex, bg_hex, alpha):
    """Blend two hex colors to create smooth transitions and neon glow halos."""
    alpha = max(0.0, min(1.0, alpha))
    fr, fg, fb = hex_to_rgb(fg_hex)
    br, bg, bb = hex_to_rgb(bg_hex)
    return rgb_to_hex((
        br + (fr - br) * alpha,
        bg + (fg - bg) * alpha,
        bb + (fb - bb) * alpha,
    ))


def get_smooth_usage_color(percent):
    """Smoothly interpolate Green (<45%) -> Orange (~65%) -> Red (>85%)."""
    green = "#22C55E"
    orange = "#F97316"
    red = "#EF4444"

    p = max(0.0, min(100.0, percent))
    if p <= 45.0:
        return green
    if p <= 65.0:
        t = (p - 45.0) / 20.0
        return blend_hex(orange, green, t)
    if p <= 85.0:
        t = (p - 65.0) / 20.0
        return blend_hex(red, orange, t)
    return red


def trim_own_memory():
    """Safely release unused memory from this optimizer's own process only."""
    gc.collect()
    if _kernel32 is None:
        return
    try:
        _kernel32.SetProcessWorkingSetSize(
            ctypes.c_void_p(-1), ctypes.c_size_t(-1), ctypes.c_size_t(-1)
        )
    except Exception:
        pass


def create_tray_image():
    """Draw a crisp 64x64 tray icon in memory (no external icon file needed)."""
    img = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    draw.ellipse((4, 4, 60, 60), fill="#0D1017", outline="#38BDF8", width=5)
    bolt = [(35, 14), (20, 35), (31, 35), (28, 50), (44, 29), (33, 29)]
    draw.polygon(bolt, fill="#22C55E")
    return img


class EdgeGlowOverlay:
    """Borderless, always-on-top, click-through 3-pixel ambient status bar at the top edge."""

    def __init__(self, master):
        self.master = master
        self._destroyed = False
        self._anim_after_id = None
        self._mode = "healthy"  # "healthy" | "game" | "stress"
        self._phase = 0.0
        self._current_alpha = 0.0
        self._target_alpha = 0.0
        self._current_color = "#A855F7"
        self._target_color = "#A855F7"

        screen_w = master.winfo_screenwidth()
        self.win = tk.Toplevel(master)
        self.win.overrideredirect(True)
        self.win.geometry(f"{screen_w}x3+0+0")
        self.win.configure(bg=self._current_color)

        try:
            self.win.attributes("-topmost", True)
            self.win.attributes("-alpha", 0.0)
        except Exception:
            pass

        apply_click_through_style(self.win)

    def update_state(self, cpu_percent, ram_percent, game_mode_active):
        """Set target glow state: invisible when healthy, purple in Game Mode, amber/red >85%."""
        if self._destroyed or not self.win.winfo_exists():
            return

        peak = max(cpu_percent, ram_percent)
        if peak > 85.0:
            self._mode = "stress"
            # Smoothly shift from warm amber at 85% to bright red at 95%+
            severity = min(1.0, max(0.0, (peak - 85.0) / 10.0))
            self._target_color = blend_hex("#EF4444", "#F59E0B", severity)
            self._target_alpha = 0.75
        elif game_mode_active:
            self._mode = "game"
            self._target_color = "#A855F7"
            self._target_alpha = 0.50
        else:
            self._mode = "healthy"
            self._target_alpha = 0.0

        # Ensure bar remains topmost above full-screen windows when visible
        if self._target_alpha > 0.0:
            try:
                self.win.attributes("-topmost", True)
            except Exception:
                pass

        if self._anim_after_id is None:
            self._step_animation()

    def _step_animation(self):
        self._anim_after_id = None
        if self._destroyed or not self.win.winfo_exists():
            return

        keep_running = False

        if self._mode == "game":
            # Gentle soft purple breathing centered around alpha=0.5
            self._phase += 0.16
            pulse_target = 0.50 + 0.10 * math.sin(self._phase)
            self._current_alpha += (pulse_target - self._current_alpha) * 0.25
            self._current_color = blend_hex(self._target_color, self._current_color, 0.25)
            keep_running = True
        elif self._mode == "stress":
            # Smooth glide to amber/red at alpha=0.75 with subtle breathing
            self._phase += 0.22
            pulse_target = 0.75 + 0.05 * math.sin(self._phase)
            self._current_alpha += (pulse_target - self._current_alpha) * 0.25
            self._current_color = blend_hex(self._target_color, self._current_color, 0.25)
            keep_running = True
        else:
            # Smoothly fade back to invisible (alpha=0.0), then stop timer completely
            if self._current_alpha > 0.02:
                self._current_alpha *= 0.72
                keep_running = True
            else:
                self._current_alpha = 0.0
                keep_running = False

        try:
            self.win.configure(bg=self._current_color)
            self.win.attributes("-alpha", max(0.0, min(0.85, self._current_alpha)))
        except Exception:
            return

        if keep_running:
            self._anim_after_id = self.master.after(EDGE_GLOW_ANIM_MS, self._step_animation)

    def destroy(self):
        self._destroyed = True
        if self._anim_after_id is not None:
            try:
                self.master.after_cancel(self._anim_after_id)
            except Exception:
                pass
            self._anim_after_id = None
        try:
            if self.win.winfo_exists():
                self.win.destroy()
        except Exception:
            pass


class CircularGauge(ctk.CTkFrame):
    """Lightweight animated circular ring gauge drawn with tkinter.Canvas."""

    def __init__(self, master, title, initial_detail="", size=192, bg_color=BG_CARD):
        super().__init__(master, fg_color="transparent")
        self.size = size
        self.bg_color = bg_color

        self.canvas = tk.Canvas(
            self,
            width=size,
            height=size,
            bg=bg_color,
            highlightthickness=0,
            bd=0,
        )
        self.canvas.pack()

        pad = 22
        cx = size / 2
        cy = size / 2
        bbox = (pad, pad, size - pad, size - pad)

        inner_pad = pad + 12
        self.canvas.create_oval(
            inner_pad,
            inner_pad,
            size - inner_pad,
            size - inner_pad,
            fill="#101521",
            outline="#1F283D",
            width=1,
        )

        self.canvas.create_arc(
            *bbox,
            start=0,
            extent=359.9,
            style=tk.ARC,
            width=13,
            outline="#222B3F",
        )

        self.glow_outer_id = self.canvas.create_arc(
            *bbox,
            start=90,
            extent=0,
            style=tk.ARC,
            width=25,
            outline=bg_color,
            state="hidden",
        )
        self.glow_inner_id = self.canvas.create_arc(
            *bbox,
            start=90,
            extent=0,
            style=tk.ARC,
            width=18,
            outline=bg_color,
            state="hidden",
        )
        self.arc_id = self.canvas.create_arc(
            *bbox,
            start=90,
            extent=0,
            style=tk.ARC,
            width=11,
            outline="#22C55E",
            state="hidden",
        )

        self.percent_text_id = self.canvas.create_text(
            cx,
            cy - 8,
            text="0.0%",
            fill=TEXT_PRIMARY,
            font=("Segoe UI", 22, "bold"),
        )
        self.title_text_id = self.canvas.create_text(
            cx,
            cy + 22,
            text=title.upper(),
            fill=TEXT_MUTED,
            font=("Segoe UI", 9, "bold"),
        )

        self.detail_label = ctk.CTkLabel(
            self,
            text=initial_detail,
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#22C55E",
        )
        self.detail_label.pack(pady=(2, 0))

    def set_value(self, percent, detail_text=None):
        p = max(0.0, min(100.0, percent))
        accent = get_smooth_usage_color(p)
        glow_outer = blend_hex(accent, self.bg_color, 0.16)
        glow_inner = blend_hex(accent, self.bg_color, 0.34)

        if p < 0.2:
            self.canvas.itemconfigure(self.glow_outer_id, state="hidden")
            self.canvas.itemconfigure(self.glow_inner_id, state="hidden")
            self.canvas.itemconfigure(self.arc_id, state="hidden")
        else:
            extent = -359.9 if p >= 99.9 else -(p / 100.0) * 360.0
            self.canvas.itemconfigure(self.glow_outer_id, extent=extent, outline=glow_outer, state="normal")
            self.canvas.itemconfigure(self.glow_inner_id, extent=extent, outline=glow_inner, state="normal")
            self.canvas.itemconfigure(self.arc_id, extent=extent, outline=accent, state="normal")

        self.canvas.itemconfigure(self.percent_text_id, text=f"{p:.1f}%")
        self.detail_label.configure(text_color=accent)
        if detail_text is not None:
            self.detail_label.configure(text=detail_text)


class LagForensicsModal(ctk.CTkToplevel):
    """Animated modal card displaying the biggest CPU/RAM spike from the last 60 seconds."""

    def __init__(self, app_controller, samples):
        super().__init__(app_controller)
        self.app = app_controller
        self.samples = list(samples)
        self._closing = False
        self._anim_after_id = None
        self.culprit_key = None
        self.culprit_name = None
        self.culprit_protected = False
        self.freeze_btn = None
        self.close_btn = None
        self.action_feedback_label = None
        self.status_badge = None

        self.withdraw()
        self.title("60-Second Lag Forensics")
        self.resizable(False, False)
        self.configure(fg_color=BG_WINDOW)
        self.transient(app_controller)

        self._width = 540
        self._height = 465 if self.samples else 285

        self._build_content()

        app_controller.update_idletasks()
        px = app_controller.winfo_rootx()
        py = app_controller.winfo_rooty()
        pw = app_controller.winfo_width()
        ph = app_controller.winfo_height()

        self._target_x = max(20, px + (pw - self._width) // 2)
        self._target_y = max(20, py + (ph - self._height) // 2)
        self._start_y = self._target_y + 20

        self.geometry(f"{self._width}x{self._height}+{self._target_x}+{self._start_y}")
        try:
            self.attributes("-alpha", 0.0)
        except Exception:
            pass

        self.protocol("WM_DELETE_WINDOW", self.close_animated)
        self.bind("<Escape>", lambda _e: self.close_animated())

        self.deiconify()
        self.lift()
        self.focus_force()
        try:
            self.grab_set()
        except Exception:
            pass

        self._animate_open(1)

    @staticmethod
    def _find_peak_spike(samples):
        avg_ram = sum(s["total_ram"] for s in samples) / max(1, len(samples))
        best_idx = 0
        best_score = -1.0

        for idx, s in enumerate(samples):
            ram_surge = max(0.0, s["total_ram"] - avg_ram)
            ram_critical = 18.0 if s["total_ram"] >= 90.0 else (8.0 if s["total_ram"] >= 85.0 else 0.0)
            score = s["total_cpu"] + (s["culprit_cpu"] * 0.65) + (ram_surge * 2.2) + ram_critical
            if score >= best_score:
                best_score = score
                best_idx = idx

        return best_idx, samples[best_idx]

    def _build_content(self):
        card = ctk.CTkFrame(
            self,
            fg_color=BG_CARD,
            corner_radius=14,
            border_width=2,
            border_color="#7C3AED",
        )
        card.pack(fill="both", expand=True, padx=14, pady=14)

        header = ctk.CTkFrame(card, fg_color="transparent")
        header.pack(fill="x", padx=18, pady=(14, 6))

        title_col = ctk.CTkFrame(header, fg_color="transparent")
        title_col.pack(side="left")

        ctk.CTkLabel(
            title_col,
            text="🕵️  60-SECOND LAG FORENSICS",
            font=ctk.CTkFont(size=16, weight="bold"),
            text_color=TEXT_PRIMARY,
        ).pack(anchor="w")

        if self.samples:
            span_sec = min(60, len(self.samples) * 2)
            subtitle = f"Scanned {len(self.samples)} snapshots covering the last {span_sec} seconds"
        elif self.app.lag_recorder_enabled:
            subtitle = "Lag Recorder is ON — collecting your first 2-second snapshot..."
        else:
            subtitle = "Lag Recorder is currently turned OFF"

        ctk.CTkLabel(
            title_col,
            text=subtitle,
            font=ctk.CTkFont(size=11),
            text_color=TEXT_MUTED,
        ).pack(anchor="w")

        ctk.CTkButton(
            header,
            text="✕",
            width=32,
            height=30,
            corner_radius=8,
            font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#1F293D",
            hover_color="#334155",
            text_color=TEXT_MUTED,
            command=self.close_animated,
        ).pack(side="right")

        if not self.samples:
            empty_box = ctk.CTkFrame(
                card,
                fg_color=BG_INNER,
                corner_radius=10,
                border_width=1,
                border_color=BORDER_SUBTLE,
            )
            empty_box.pack(fill="both", expand=True, padx=18, pady=(8, 12))

            if not self.app.lag_recorder_enabled:
                msg = (
                    "Turn on 'Lag Recorder' in Smart Features to keep a silent\n"
                    "60-second rolling log of CPU/RAM spikes (< 1 MB RAM)."
                )
            else:
                msg = (
                    "Buffer is warming up.\n"
                    "Wait 2 seconds and click 'Why Did My PC Just Lag?' again."
                )

            ctk.CTkLabel(
                empty_box,
                text=msg,
                font=ctk.CTkFont(size=13),
                text_color="#CBD5E1",
                justify="center",
            ).pack(expand=True, padx=16, pady=(18, 10))

            if not self.app.lag_recorder_enabled:
                ctk.CTkButton(
                    empty_box,
                    text="Turn ON Lag Recorder",
                    height=38,
                    width=200,
                    corner_radius=8,
                    font=ctk.CTkFont(size=13, weight="bold"),
                    fg_color="#7C3AED",
                    hover_color="#6D28D9",
                    command=self._enable_recorder_and_close,
                ).pack(pady=(0, 16))
            return

        peak_idx, peak = self._find_peak_spike(self.samples)
        seconds_ago = max(0, int(round(time.time() - peak["timestamp"])))
        ago_text = "Just now" if seconds_ago <= 1 else f"{seconds_ago}s ago"

        self.culprit_key = peak["culprit_key"]
        self.culprit_name = peak["culprit_name"]
        self.culprit_protected = peak["culprit_protected"]

        chart_frame = ctk.CTkFrame(
            card,
            fg_color=BG_INNER,
            corner_radius=10,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        chart_frame.pack(fill="x", padx=18, pady=(4, 10))

        chart_hdr = ctk.CTkFrame(chart_frame, fg_color="transparent")
        chart_hdr.pack(fill="x", padx=12, pady=(8, 2))
        ctk.CTkLabel(
            chart_hdr,
            text="60s CPU TIMELINE (PEAK HIGHLIGHTED)",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#A78BFA",
        ).pack(side="left")
        ctk.CTkLabel(
            chart_hdr,
            text=f"Spike @ {peak['time_str']} ({ago_text})",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#F87171",
        ).pack(side="right")

        spark_w = 452
        spark_h = 54
        canvas = tk.Canvas(
            chart_frame,
            width=spark_w,
            height=spark_h,
            bg=BG_INNER,
            highlightthickness=0,
            bd=0,
        )
        canvas.pack(padx=12, pady=(2, 10))
        self._draw_sparkline(canvas, spark_w, spark_h, peak_idx)

        stats_row = ctk.CTkFrame(card, fg_color="transparent")
        stats_row.pack(fill="x", padx=18, pady=(0, 10))
        stats_row.grid_columnconfigure(0, weight=1, uniform="stat")
        stats_row.grid_columnconfigure(1, weight=1, uniform="stat")
        stats_row.grid_columnconfigure(2, weight=1, uniform="stat")

        self._make_stat_tile(stats_row, 0, "SPIKE TIME", peak["time_str"], ago_text, "#C4B5FD")
        self._make_stat_tile(
            stats_row,
            1,
            "TOTAL CPU",
            f"{peak['total_cpu']:.1f}%",
            "System Load",
            get_smooth_usage_color(peak["total_cpu"]),
        )
        self._make_stat_tile(
            stats_row,
            2,
            "TOTAL RAM",
            f"{peak['total_ram']:.1f}%",
            "Memory Used",
            get_smooth_usage_color(peak["total_ram"]),
        )

        culprit_card = ctk.CTkFrame(
            card,
            fg_color=BG_INNER,
            corner_radius=12,
            border_width=1,
            border_color="#312E81",
        )
        culprit_card.pack(fill="x", padx=18, pady=(0, 10))

        culprit_hdr = ctk.CTkFrame(culprit_card, fg_color="transparent")
        culprit_hdr.pack(fill="x", padx=14, pady=(10, 4))

        ctk.CTkLabel(
            culprit_hdr,
            text="BIGGEST CPU-SPIKING CULPRIT",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#93C5FD",
        ).pack(side="left")

        is_running = self._is_culprit_running()
        is_frozen = self.culprit_key in self.app.frozen_apps

        if self.culprit_protected:
            badge_text, badge_fg, badge_bg = "  🛡️ PROTECTED SYSTEM  ", "#FBBF24", "#2D2312"
        elif not is_running:
            badge_text, badge_fg, badge_bg = "  ALREADY CLOSED  ", "#94A3B8", "#1E293B"
        elif is_frozen:
            badge_text, badge_fg, badge_bg = "  ❄️ FROZEN  ", "#38BDF8", "#12324A"
        else:
            badge_text, badge_fg, badge_bg = "  ● RUNNING  ", "#22C55E", "#122620"

        self.status_badge = ctk.CTkLabel(
            culprit_hdr,
            text=badge_text,
            height=20,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=badge_fg,
            fg_color=badge_bg,
            corner_radius=6,
        )
        self.status_badge.pack(side="right")

        ctk.CTkLabel(
            culprit_card,
            text=self.culprit_name or "No active user app detected",
            font=ctk.CTkFont(size=19, weight="bold"),
            text_color=TEXT_PRIMARY,
            anchor="w",
        ).pack(fill="x", padx=14)

        ctk.CTkLabel(
            culprit_card,
            text=(
                f"App CPU at spike: {peak['culprit_cpu']:.1f}%   •   "
                f"App RAM: {peak['culprit_ram_mb']:.1f} MB"
            ),
            font=ctk.CTkFont(size=12),
            text_color="#CBD5E1",
            anchor="w",
        ).pack(fill="x", padx=14, pady=(2, 12))

        actions_row = ctk.CTkFrame(culprit_card, fg_color="transparent")
        actions_row.pack(fill="x", padx=14, pady=(0, 12))
        actions_row.grid_columnconfigure(0, weight=1, uniform="act")
        actions_row.grid_columnconfigure(1, weight=1, uniform="act")

        can_act = bool(self.culprit_key) and (not self.culprit_protected) and is_running

        self.freeze_btn = ctk.CTkButton(
            actions_row,
            text="Thaw 🔥" if is_frozen else "Freeze ❄️",
            height=40,
            corner_radius=8,
            font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#EA580C" if is_frozen else "#0284C7",
            hover_color="#C2410C" if is_frozen else "#0369A1",
            state="normal" if can_act else "disabled",
            command=self._on_modal_freeze,
        )
        self.freeze_btn.grid(row=0, column=0, sticky="ew", padx=(0, 6))

        self.close_btn = ctk.CTkButton(
            actions_row,
            text="Close App ✕",
            height=40,
            corner_radius=8,
            font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#DC2626",
            hover_color="#B91C1C",
            state="normal" if can_act else "disabled",
            command=self._on_modal_close_app,
        )
        self.close_btn.grid(row=0, column=1, sticky="ew", padx=(6, 0))

        if self.culprit_protected:
            default_note = "Windows system processes are protected and cannot be frozen or closed."
            default_col = "#FBBF24"
        elif not is_running:
            default_note = "This process exited after the spike."
            default_col = TEXT_MUTED
        else:
            default_note = "Freeze drops CPU to 0.0% without losing work • Close stops the app."
            default_col = TEXT_MUTED

        self.action_feedback_label = ctk.CTkLabel(
            card,
            text=default_note,
            font=ctk.CTkFont(size=11),
            text_color=default_col,
            anchor="w",
        )
        self.action_feedback_label.pack(fill="x", padx=20, pady=(0, 12))

    def _make_stat_tile(self, parent, col_idx, label, value, subtext, value_color):
        tile = ctk.CTkFrame(
            parent,
            fg_color=BG_INNER,
            corner_radius=10,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        pad_left = 0 if col_idx == 0 else 4
        pad_right = 0 if col_idx == 2 else 4
        tile.grid(row=0, column=col_idx, sticky="nsew", padx=(pad_left, pad_right))

        ctk.CTkLabel(
            tile,
            text=label,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=TEXT_MUTED,
        ).pack(pady=(8, 0))

        ctk.CTkLabel(
            tile,
            text=value,
            font=ctk.CTkFont(size=18, weight="bold"),
            text_color=value_color,
        ).pack(pady=(2, 0))

        ctk.CTkLabel(
            tile,
            text=subtext,
            font=ctk.CTkFont(size=10),
            text_color=TEXT_MUTED,
        ).pack(pady=(0, 8))

    def _draw_sparkline(self, canvas, width, height, peak_idx):
        for pct in (50, 80):
            y = height - (pct / 100.0) * (height - 8) - 4
            canvas.create_line(0, y, width, y, fill="#1E293B", dash=(3, 3))

        slot_w = width / float(LAG_BUFFER_MAXLEN)
        offset = LAG_BUFFER_MAXLEN - len(self.samples)

        for idx, sample in enumerate(self.samples):
            x0 = (offset + idx) * slot_w + 2
            x1 = (offset + idx + 1) * slot_w - 2
            bar_h = max(4.0, (sample["total_cpu"] / 100.0) * (height - 8))
            y0 = height - bar_h - 2
            y1 = height - 2

            if idx == peak_idx:
                color = "#EF4444"
                canvas.create_rectangle(x0 - 1, 2, x1 + 1, y1, fill="#2A1520", outline="")
            else:
                color = blend_hex(get_smooth_usage_color(sample["total_cpu"]), BG_INNER, 0.72)

            canvas.create_rectangle(x0, y0, x1, y1, fill=color, outline="")

    def _is_culprit_running(self):
        if not self.culprit_key:
            return False
        for proc in psutil.process_iter(["name"]):
            try:
                name = proc.info["name"]
                if name and name.lower() == self.culprit_key:
                    return True
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue
        return False

    def _enable_recorder_and_close(self):
        self.app.lag_recorder_var.set(True)
        self.app.on_lag_recorder_toggled()
        self.close_animated()

    def _on_modal_freeze(self):
        if not self.culprit_key or self.culprit_protected:
            return

        if not self.app.freeze_mode_enabled:
            self.app.freeze_mode_var.set(True)
            self.app.on_freeze_mode_toggled()

        was_frozen = self.culprit_key in self.app.frozen_apps
        self.app.toggle_freeze_app(self.culprit_key, display_name_override=self.culprit_name)

        if was_frozen:
            self.freeze_btn.configure(text="Freeze ❄️", fg_color="#0284C7", hover_color="#0369A1")
            self.status_badge.configure(text="  ● RUNNING  ", text_color="#22C55E", fg_color="#122620")
            self.action_feedback_label.configure(
                text=f"🔥 Thawing {self.culprit_name}...", text_color="#22C55E"
            )
        else:
            self.freeze_btn.configure(text="Thaw 🔥", fg_color="#EA580C", hover_color="#C2410C")
            self.status_badge.configure(text="  ❄️ FROZEN  ", text_color="#38BDF8", fg_color="#12324A")
            self.action_feedback_label.configure(
                text=f"❄️ Freezing {self.culprit_name} to 0.0% CPU...", text_color="#38BDF8"
            )

    def _on_modal_close_app(self):
        if not self.culprit_key or self.culprit_protected:
            return

        self.freeze_btn.configure(state="disabled")
        self.close_btn.configure(state="disabled", text="Closing...")
        self.status_badge.configure(text="  CLOSING  ", text_color="#F87171", fg_color="#3B1519")
        self.action_feedback_label.configure(
            text=f"Stopping {self.culprit_name} safely...", text_color="#F87171"
        )
        self.app.close_app_by_key(self.culprit_key, self.culprit_name)
        self.after(450, self.close_animated)

    def _animate_open(self, step):
        if self._closing or not self.winfo_exists():
            return
        t = step / float(MODAL_ANIM_STEPS)
        eased = 1.0 - ((1.0 - t) ** 3)
        cur_y = int(self._start_y + (self._target_y - self._start_y) * eased)
        self.geometry(f"{self._width}x{self._height}+{self._target_x}+{cur_y}")
        try:
            self.attributes("-alpha", min(1.0, eased))
        except Exception:
            pass

        if step < MODAL_ANIM_STEPS:
            self._anim_after_id = self.after(MODAL_ANIM_STEP_MS, self._animate_open, step + 1)
        else:
            self._anim_after_id = None

    def close_animated(self):
        if self._closing:
            return
        self._closing = True
        if self._anim_after_id is not None:
            try:
                self.after_cancel(self._anim_after_id)
            except Exception:
                pass
            self._anim_after_id = None

        try:
            self.grab_release()
        except Exception:
            pass

        self._animate_close(1)

    def _animate_close(self, step):
        if not self.winfo_exists():
            self.app._on_forensics_modal_closed()
            return
        t = step / float(max(1, MODAL_ANIM_STEPS - 2))
        try:
            self.attributes("-alpha", max(0.0, 1.0 - t))
        except Exception:
            pass

        if step < max(1, MODAL_ANIM_STEPS - 2):
            self._anim_after_id = self.after(MODAL_ANIM_STEP_MS, self._animate_close, step + 1)
        else:
            self._anim_after_id = None
            self.app._on_forensics_modal_closed()
            self.destroy()


class AppGroupCard:
    """Expandable app row with live sub-process checkboxes and App Freeze/Thaw controls."""

    def __init__(self, master, app_controller, app_data):
        self.master = master
        self.app = app_controller
        self.key = app_data["key"]
        self.display_name = app_data["display_name"]
        self.processes = app_data["processes"]
        self.is_expanded = False
        self.is_selected = False
        self.is_frozen = self.key in app_controller.frozen_apps
        self._slide_after_id = None
        self._sub_rows = {}  # pid -> dict of reusable widgets

        self.container = ctk.CTkFrame(
            master,
            fg_color=BG_ROW,
            corner_radius=8,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )

        self.header_frame = ctk.CTkFrame(
            self.container,
            fg_color="transparent",
            height=40,
            cursor="hand2",
        )
        self.header_frame.pack(fill="x", padx=8, pady=4)

        self.right_controls = ctk.CTkFrame(self.header_frame, fg_color="transparent")
        self.right_controls.pack(side="right", padx=(6, 0))

        self.freeze_button = ctk.CTkButton(
            self.right_controls,
            text="Freeze ❄️",
            width=84,
            height=26,
            corner_radius=6,
            font=ctk.CTkFont(size=11, weight="bold"),
            fg_color="#0284C7",
            hover_color="#0369A1",
            text_color="#FFFFFF",
            command=self._on_freeze_button_click,
        )

        self.mem_label = ctk.CTkLabel(
            self.right_controls,
            text="",
            height=24,
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#93C5FD",
            fg_color="#131B2E",
            corner_radius=6,
            cursor="hand2",
        )
        self.mem_label.pack(side="right", padx=(0, 2))

        self.arrow_label = ctk.CTkLabel(
            self.header_frame,
            text="▸",
            width=18,
            font=ctk.CTkFont(size=14, weight="bold"),
            text_color=TEXT_MUTED,
            cursor="hand2",
        )
        self.arrow_label.pack(side="left", padx=(2, 4))

        self.name_label = ctk.CTkLabel(
            self.header_frame,
            text=self.display_name,
            font=ctk.CTkFont(size=13, weight="bold"),
            text_color=TEXT_PRIMARY,
            cursor="hand2",
        )
        self.name_label.pack(side="left", padx=(0, 6))

        self.count_label = ctk.CTkLabel(
            self.header_frame,
            text="",
            font=ctk.CTkFont(size=11),
            text_color=TEXT_MUTED,
            cursor="hand2",
        )
        self.count_label.pack(side="left")

        for widget in (
            self.header_frame,
            self.arrow_label,
            self.name_label,
            self.count_label,
            self.mem_label,
        ):
            widget.bind("<Button-1>", self._on_header_click)

        self.sub_wrapper = tk.Frame(
            self.container,
            bg=BG_ROW,
            bd=0,
            highlightthickness=0,
            height=1,
        )

        self.sub_panel = ctk.CTkFrame(
            self.sub_wrapper,
            fg_color=BG_SUBPANEL,
            corner_radius=8,
            border_width=1,
            border_color="#1F293D",
        )
        self.sub_panel.pack(fill="x", padx=8, pady=(0, 8))

        self.sub_top_bar = ctk.CTkFrame(self.sub_panel, fg_color="transparent")
        self.sub_top_bar.pack(fill="x", padx=10, pady=(8, 4))

        self.select_all_var = tk.BooleanVar(value=False)
        self.select_all_cb = ctk.CTkCheckBox(
            self.sub_top_bar,
            text="Select All",
            variable=self.select_all_var,
            command=self._on_select_all_toggle,
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#E2E8F0",
            checkbox_width=16,
            checkbox_height=16,
            corner_radius=4,
            border_width=2,
            fg_color="#2563EB",
            hover_color="#1D4ED8",
            border_color="#475569",
        )
        self.select_all_cb.pack(side="left")

        ctk.CTkLabel(
            self.sub_top_bar,
            text="RAM (MB)   •   CPU %",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=TEXT_MUTED,
        ).pack(side="right", padx=(0, 4))

        self.rows_frame = ctk.CTkFrame(self.sub_panel, fg_color="transparent")
        self.rows_frame.pack(fill="x", padx=8, pady=(0, 8))

        self.set_freeze_mode(app_controller.freeze_mode_enabled)
        self.set_frozen(self.is_frozen)
        self.update_data(app_data)

    def _on_header_click(self, _event=None):
        self.app.on_app_card_clicked(self.key)

    def _on_freeze_button_click(self):
        self.app.toggle_freeze_app(self.key)

    def set_freeze_mode(self, enabled):
        if not self.container.winfo_exists():
            return
        if enabled:
            if not self.freeze_button.winfo_ismapped():
                self.freeze_button.pack(side="right", padx=(6, 2))
        else:
            if self.freeze_button.winfo_ismapped():
                self.freeze_button.pack_forget()
        self._refresh_display_name()

    def set_freeze_busy(self, busy):
        if not self.container.winfo_exists():
            return
        if busy:
            self.freeze_button.configure(state="disabled", text="...")
        else:
            self.freeze_button.configure(state="normal")
            self.set_frozen(self.is_frozen)

    def set_frozen(self, frozen):
        self.is_frozen = frozen
        if not self.container.winfo_exists():
            return

        if frozen:
            self.container.configure(fg_color=BG_ROW_FROZEN, border_color=BORDER_FROZEN)
            self.sub_wrapper.configure(bg=BG_ROW_FROZEN)
            self.name_label.configure(text_color="#E0F2FE")
            self.count_label.configure(text_color="#7DD3FC")
            self.mem_label.configure(fg_color="#0C2538", text_color="#7DD3FC")
            self.freeze_button.configure(
                text="Thaw 🔥",
                fg_color="#EA580C",
                hover_color="#C2410C",
            )
        else:
            border_col = "#38BDF8" if self.is_selected else BORDER_SUBTLE
            self.container.configure(fg_color=BG_ROW, border_color=border_col)
            self.sub_wrapper.configure(bg=BG_ROW)
            self.name_label.configure(text_color=TEXT_PRIMARY)
            self.count_label.configure(text_color=TEXT_MUTED)
            self.mem_label.configure(fg_color="#131B2E", text_color="#93C5FD")
            self.freeze_button.configure(
                text="Freeze ❄️",
                fg_color="#0284C7",
                hover_color="#0369A1",
            )

        self._refresh_count_label()

    def set_selected(self, selected):
        self.is_selected = selected
        if not self.container.winfo_exists():
            return
        if self.is_frozen:
            self.container.configure(border_color="#7DD3FC" if selected else BORDER_FROZEN)
        else:
            self.container.configure(border_color="#38BDF8" if selected else BORDER_SUBTLE)

    def _refresh_display_name(self):
        if not self.container.winfo_exists():
            return
        max_len = 18 if self.app.freeze_mode_enabled else 26
        short_name = (
            self.display_name
            if len(self.display_name) <= max_len
            else self.display_name[: max_len - 3] + "..."
        )
        self.name_label.configure(text=short_name)

    def _refresh_count_label(self):
        if not self.container.winfo_exists():
            return
        count = len(self.processes)
        proc_word = "proc" if count == 1 else "procs"
        frozen_tag = " • Frozen" if self.is_frozen else ""
        self.count_label.configure(text=f"({count} {proc_word}){frozen_tag}")

    def update_data(self, app_data):
        if not self.container.winfo_exists():
            return

        self.display_name = app_data["display_name"]
        self.processes = app_data["processes"]

        self._refresh_display_name()
        self._refresh_count_label()
        self.mem_label.configure(text=f"  {format_bytes(app_data['bytes'])}  ")

        is_now_frozen = self.key in self.app.frozen_apps
        if is_now_frozen != self.is_frozen and self.key not in self.app._freezing_apps:
            self.set_frozen(is_now_frozen)

        if self.is_expanded:
            self._sync_sub_rows()

    def _sync_sub_rows(self):
        live_map = {p["pid"]: p for p in self.processes}

        for pid in list(self._sub_rows.keys()):
            if pid not in live_map and pid not in self.app._fading_pids:
                row_info = self._sub_rows.pop(pid)
                if row_info["wrapper"].winfo_exists():
                    row_info["wrapper"].destroy()

        for proc in self.processes:
            pid = proc["pid"]
            if pid in self.app._fading_pids:
                continue

            ram_mb = proc["rss"] / (1024.0 * 1024.0)
            cpu_pct = 0.0 if self.is_frozen else proc["cpu"]
            is_checked = pid in self.app.selected_pids

            if pid in self._sub_rows:
                row_info = self._sub_rows[pid]
                if row_info["var"].get() != is_checked:
                    row_info["var"].set(is_checked)
                row_info["ram_label"].configure(text=f"{ram_mb:.1f} MB")
                row_info["cpu_label"].configure(
                    text=f"{cpu_pct:.1f}%",
                    text_color="#38BDF8" if self.is_frozen else self._cpu_tint(cpu_pct),
                )
            else:
                self._create_sub_row(pid, ram_mb, cpu_pct, is_checked)

        self._sync_select_all_checkbox()

    @staticmethod
    def _cpu_tint(cpu_pct):
        if cpu_pct >= 30.0:
            return "#EF4444"
        if cpu_pct >= 10.0:
            return "#F97316"
        return "#94A3B8"

    def _create_sub_row(self, pid, ram_mb, cpu_pct, is_checked):
        wrapper = tk.Frame(self.rows_frame, bg=BG_SUBPANEL, bd=0, highlightthickness=0)
        wrapper.pack(fill="x", pady=2)

        row_frame = ctk.CTkFrame(
            wrapper,
            fg_color=BG_SUBROW,
            corner_radius=6,
            height=30,
        )
        row_frame.pack(fill="x")

        var = tk.BooleanVar(value=is_checked)
        cb = ctk.CTkCheckBox(
            row_frame,
            text=f"PID {pid}",
            variable=var,
            command=lambda p=pid, v=var: self._on_pid_checkbox_toggle(p, v),
            font=ctk.CTkFont(size=12),
            text_color="#E2E8F0",
            checkbox_width=15,
            checkbox_height=15,
            corner_radius=4,
            border_width=2,
            fg_color="#38BDF8",
            hover_color="#2563EB",
            border_color="#475569",
        )
        cb.pack(side="left", padx=(8, 6), pady=4)

        cpu_label = ctk.CTkLabel(
            row_frame,
            text=f"{cpu_pct:.1f}%",
            width=48,
            anchor="e",
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color="#38BDF8" if self.is_frozen else self._cpu_tint(cpu_pct),
        )
        cpu_label.pack(side="right", padx=(6, 10), pady=4)

        ram_label = ctk.CTkLabel(
            row_frame,
            text=f"{ram_mb:.1f} MB",
            width=74,
            anchor="e",
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color="#93C5FD",
        )
        ram_label.pack(side="right", padx=(4, 4), pady=4)

        self._sub_rows[pid] = {
            "wrapper": wrapper,
            "frame": row_frame,
            "var": var,
            "cb": cb,
            "ram_label": ram_label,
            "cpu_label": cpu_label,
        }

    def _on_pid_checkbox_toggle(self, pid, var):
        if var.get():
            self.app.selected_pids.add(pid)
        else:
            self.app.selected_pids.discard(pid)

        self._sync_select_all_checkbox()
        self.app.update_close_button()

    def _on_select_all_toggle(self):
        select_all = bool(self.select_all_var.get())
        for proc in self.processes:
            pid = proc["pid"]
            if select_all:
                self.app.selected_pids.add(pid)
            else:
                self.app.selected_pids.discard(pid)

            if pid in self._sub_rows:
                self._sub_rows[pid]["var"].set(select_all)

        self._sync_select_all_checkbox()
        self.app.update_close_button()

    def _sync_select_all_checkbox(self):
        active_pids = [p["pid"] for p in self.processes if p["pid"] not in self.app._fading_pids]
        total = len(active_pids)
        selected_here = sum(1 for pid in active_pids if pid in self.app.selected_pids)

        self.select_all_cb.configure(text=f"Select All ({selected_here}/{total})")
        all_checked = (total > 0 and selected_here == total)
        if self.select_all_var.get() != all_checked:
            self.select_all_var.set(all_checked)

    def _cancel_slide(self):
        if self._slide_after_id is not None:
            try:
                self.app.after_cancel(self._slide_after_id)
            except Exception:
                pass
            self._slide_after_id = None

    def expand(self, animate=True):
        if self.is_expanded or not self.container.winfo_exists():
            return

        self._cancel_slide()
        self.is_expanded = True
        self.arrow_label.configure(text="▾", text_color="#38BDF8")
        self._sync_sub_rows()

        if not animate:
            self.sub_wrapper.pack_propagate(True)
            self.sub_wrapper.pack(fill="x")
            return

        target_h = min(44 + len(self.processes) * 34, 340)
        self.sub_wrapper.pack_propagate(False)
        self.sub_wrapper.configure(height=1)
        self.sub_wrapper.pack(fill="x")
        self._animate_slide(step=1, start_h=1, end_h=target_h, expanding=True)

    def collapse(self, animate=True, on_done=None):
        if not self.is_expanded or not self.container.winfo_exists():
            if on_done:
                on_done()
            return

        self._cancel_slide()
        self.is_expanded = False
        self.arrow_label.configure(text="▸", text_color=TEXT_MUTED)

        if not animate:
            self._finish_collapse(on_done)
            return

        current_h = self.sub_wrapper.winfo_height()
        start_h = min(max(current_h, 30), 340)
        self.sub_wrapper.pack_propagate(False)
        self.sub_wrapper.configure(height=start_h)
        self._animate_slide(step=1, start_h=start_h, end_h=1, expanding=False, on_done=on_done)

    def _animate_slide(self, step, start_h, end_h, expanding, on_done=None):
        if not self.container.winfo_exists():
            self._slide_after_id = None
            return

        t = step / float(EXPAND_ANIM_STEPS)
        eased = 1.0 - ((1.0 - t) ** 3)
        new_h = max(1, int(start_h + (end_h - start_h) * eased))
        self.sub_wrapper.configure(height=new_h)

        if step < EXPAND_ANIM_STEPS:
            self._slide_after_id = self.app.after(
                EXPAND_ANIM_STEP_MS,
                self._animate_slide,
                step + 1,
                start_h,
                end_h,
                expanding,
                on_done,
            )
        else:
            self._slide_after_id = None
            if expanding:
                self.sub_wrapper.pack_propagate(True)
                self.sub_wrapper.configure(height=0)
            else:
                self._finish_collapse(on_done)

    def _finish_collapse(self, on_done=None):
        if self.sub_wrapper.winfo_exists():
            self.sub_wrapper.pack_forget()

        for pid in list(self._sub_rows.keys()):
            row_info = self._sub_rows.pop(pid)
            if row_info["wrapper"].winfo_exists():
                row_info["wrapper"].destroy()

        if on_done:
            on_done()

    def get_sub_row(self, pid):
        return self._sub_rows.get(pid)

    def remove_sub_row(self, pid):
        row_info = self._sub_rows.pop(pid, None)
        if row_info and row_info["wrapper"].winfo_exists():
            row_info["wrapper"].destroy()
        if self.is_expanded:
            self._sync_select_all_checkbox()

    def destroy(self):
        self._cancel_slide()
        self._sub_rows.clear()
        if self.container.winfo_exists():
            self.container.destroy()


class PCOptimizerApp(ctk.CTk):
    def __init__(self):
        super().__init__()

        # Appearance and window setup
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")

        self.title("PC Optimizer v4.0")
        self.geometry("1120x710")
        self.minsize(960, 640)
        self.configure(fg_color=BG_WINDOW)

        # Internal state flags
        self._is_cleaning = False
        self._is_refreshing_apps = False
        self._is_sampling_tray_lag = False
        self._is_closing_app = False
        self._is_panicking = False
        self._is_quitting = False
        self._in_tray = False
        self._game_mode_active = False
        self._tray_hint_shown = False
        self._last_auto_clean_time = 0.0
        self._last_panic_time = 0.0

        # Smart Feature Master Toggle States
        self.freeze_mode_enabled = False
        self.freeze_mode_var = tk.BooleanVar(value=False)
        self.frozen_apps = {}       # app_key -> set of suspended PIDs
        self._freezing_apps = set()

        self.lag_recorder_enabled = True
        self.lag_recorder_var = tk.BooleanVar(value=True)
        self.lag_buffer = deque(maxlen=LAG_BUFFER_MAXLEN)
        self._forensics_modal = None

        self.edge_glow_enabled = False
        self.edge_glow_var = tk.BooleanVar(value=False)
        self._edge_glow_overlay = None

        self.panic_hotkey_enabled = False
        self.panic_hotkey_var = tk.BooleanVar(value=False)
        self._panic_hotkey_handle = None
        self._panic_banner_after_id = None

        self.idle_clean_enabled = False
        self.idle_clean_var = tk.BooleanVar(value=False)
        self._cleaned_this_idle_session = False

        # Persistent multi-select & expansion state (preserved across live refreshes)
        self.selected_pids = set()
        self.expanded_apps = set()
        self.selected_main_app = ""
        self.app_cards = {}         # app_key -> AppGroupCard
        self.app_cards_order = []   # Current visual order of app_keys
        self._fading_pids = set()
        self._fading_apps = set()

        # Tray resources
        self._tray_image = create_tray_image()
        self._tray_icon = None

        # Scheduled callback IDs (tracked for clean pausing and shutdown)
        self._stats_after_id = None
        self._apps_after_id = None
        self._anim_after_id = None
        self._boost_anim_after_id = None
        self._tray_ram_after_id = None
        self._tray_lag_after_id = None
        self._game_mode_after_id = None
        self._post_game_clean_after_id = None
        self._edge_glow_poll_after_id = None
        self._idle_check_after_id = None

        # Smooth gauge animation state
        self._displayed_cpu = 0.0
        self._target_cpu = 0.0
        self._displayed_ram = 0.0
        self._target_ram = 0.0
        self._ram_detail_text = "0.0 / 0.0 GB"
        self._cpu_cores = psutil.cpu_count(logical=True) or 1

        # Hero boost animation state
        self._boost_phase = 0.0
        self._boost_spinner_idx = 0

        self.startup_widgets = []

        # Prime non-blocking CPU measurement
        psutil.cpu_percent(interval=None)

        self._build_ui()

        # Start periodic lightweight updates, startup reader, and Game Mode monitor
        self.update_system_stats()
        self.refresh_top_apps()
        self.refresh_startup_apps()
        self._schedule_game_mode_check()

        # Clicking the X button hides to the Windows system tray
        self.protocol("WM_DELETE_WINDOW", self.hide_to_tray)

    # ------------------------------------------------------------------
    # UI Construction (Header + 3 Clean Tabs + Status Bar)
    # ------------------------------------------------------------------
    def _build_ui(self):
        main_frame = ctk.CTkFrame(self, fg_color="transparent")
        main_frame.pack(fill="both", expand=True, padx=18, pady=12)

        # --- Top Header ---
        header_frame = ctk.CTkFrame(main_frame, fg_color="transparent")
        header_frame.pack(fill="x", pady=(0, 6))

        title_group = ctk.CTkFrame(header_frame, fg_color="transparent")
        title_group.pack(side="left")

        ctk.CTkLabel(
            title_group,
            text="⚡ PC OPTIMIZER",
            font=ctk.CTkFont(size=22, weight="bold"),
            text_color=TEXT_PRIMARY,
        ).pack(side="left")

        ctk.CTkLabel(
            title_group,
            text="  v4.0  ",
            height=22,
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color="#38BDF8",
            fg_color="#162238",
            corner_radius=6,
        ).pack(side="left", padx=(10, 0), pady=(2, 0))

        self.game_mode_pill = ctk.CTkLabel(
            title_group,
            text="  SMART GAME MODE: STANDBY  ",
            height=22,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#A78BFA",
            fg_color="#1E1B3A",
            corner_radius=6,
        )
        self.game_mode_pill.pack(side="left", padx=(8, 0), pady=(2, 0))

        self.active_features_pill = ctk.CTkLabel(
            title_group,
            text="  1 AUTOPILOT ON  ",
            height=22,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#34D399",
            fg_color="#112A24",
            corner_radius=6,
        )
        self.active_features_pill.pack(side="left", padx=(8, 0), pady=(2, 0))

        ctk.CTkLabel(
            header_frame,
            text="Close (X) minimizes to tray • Configure toggles in Smart Features",
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
        ).pack(side="right", pady=(4, 0))

        # --- Navigation Tabs (Dashboard | Smart Features | Startup & Apps) ---
        self.tabview = ctk.CTkTabview(
            main_frame,
            fg_color=BG_WINDOW,
            segmented_button_fg_color=BG_CARD,
            segmented_button_selected_color="#2563EB",
            segmented_button_selected_hover_color="#1D4ED8",
            segmented_button_unselected_color=BG_CARD,
            segmented_button_unselected_hover_color="#1F283D",
            text_color=TEXT_PRIMARY,
            corner_radius=12,
        )
        self.tabview.pack(fill="both", expand=True, pady=(0, 8))

        dashboard_tab = self.tabview.add("Dashboard")
        smart_tab = self.tabview.add("Smart Features")
        startup_tab = self.tabview.add("Startup & Apps")

        self._build_dashboard_tab(dashboard_tab)
        self._build_smart_features_tab(smart_tab)
        self._build_startup_tab(startup_tab)
        self._update_active_features_pill()

        # --- Bottom Status Bar ---
        status_bar = ctk.CTkFrame(
            main_frame,
            fg_color=BG_CARD,
            corner_radius=8,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        status_bar.pack(fill="x")

        self.status_label = ctk.CTkLabel(
            status_bar,
            text="System Ready • Manage all autopilot toggles inside the Smart Features tab",
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
            anchor="w",
        )
        self.status_label.pack(fill="x", padx=12, pady=6)

    def _build_dashboard_tab(self, parent):
        # Row 0: Flash Banner (hidden until Panic Rescue triggers)
        # Row 1: Compact Insights Strip (Away-Clean Summary + Why Did My PC Just Lag?)
        # Row 2: Two-column spacious Dashboard
        parent.grid_columnconfigure(0, weight=10, uniform="dash_col")
        parent.grid_columnconfigure(1, weight=13, uniform="dash_col")
        parent.grid_rowconfigure(0, weight=0)
        parent.grid_rowconfigure(1, weight=0)
        parent.grid_rowconfigure(2, weight=1)

        # ================= PANIC RESCUE FLASH BANNER (HIDDEN BY DEFAULT) =================
        self.panic_banner = ctk.CTkFrame(
            parent,
            fg_color="#143227",
            corner_radius=10,
            border_width=2,
            border_color="#22C55E",
        )
        self.panic_banner_label = ctk.CTkLabel(
            self.panic_banner,
            text="",
            font=ctk.CTkFont(size=13, weight="bold"),
            text_color="#DCFCE7",
            anchor="w",
        )
        self.panic_banner_label.pack(side="left", fill="x", expand=True, padx=14, pady=8)

        ctk.CTkButton(
            self.panic_banner,
            text="✕",
            width=26,
            height=24,
            corner_radius=6,
            font=ctk.CTkFont(size=11, weight="bold"),
            fg_color="#1F4D3A",
            hover_color="#28634B",
            text_color="#DCFCE7",
            command=self._hide_panic_banner,
        ).pack(side="right", padx=10, pady=6)

        # ================= COMPACT DASHBOARD INSIGHTS BAR =================
        insights_bar = ctk.CTkFrame(
            parent,
            fg_color=BG_CARD,
            corner_radius=12,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        insights_bar.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(4, 10))

        # Sleek 'Last Away-Clean Summary' badge on the dashboard
        self.away_clean_badge = ctk.CTkLabel(
            insights_bar,
            text="  🌙 Last Away-Clean: None yet (Idle Auto-Clean OFF)  ",
            height=28,
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color=TEXT_MUTED,
            fg_color=BG_INNER,
            corner_radius=8,
        )
        self.away_clean_badge.pack(side="left", padx=(12, 8), pady=8)

        self.dashboard_frozen_badge = ctk.CTkLabel(
            insights_bar,
            text="  ❄️ 0 Frozen  ",
            height=28,
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color="#38BDF8",
            fg_color="#12324A",
            corner_radius=8,
        )

        # Prominent 'Why Did My PC Just Lag?' button on the right
        self.lag_analysis_button = ctk.CTkButton(
            insights_bar,
            text="🕵️  Why Did My PC Just Lag?",
            height=34,
            corner_radius=9,
            font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#7C3AED",
            hover_color="#6D28D9",
            border_width=2,
            border_color="#A78BFA",
            text_color="#FFFFFF",
            command=self.open_lag_forensics,
        )
        self.lag_analysis_button.pack(side="right", padx=12, pady=6)

        self.dashboard_lag_pill = ctk.CTkLabel(
            insights_bar,
            text="  ● REC 0s/60s  ",
            height=26,
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color="#C4B5FD",
            fg_color="#231942",
            corner_radius=6,
        )
        self.dashboard_lag_pill.pack(side="right", padx=(0, 8), pady=8)

        # ================= LEFT COLUMN =================
        left_col = ctk.CTkFrame(parent, fg_color="transparent")
        left_col.grid(row=2, column=0, sticky="nsew", padx=(0, 8))
        left_col.grid_columnconfigure(0, weight=1)
        left_col.grid_rowconfigure(0, weight=3)
        left_col.grid_rowconfigure(1, weight=2)

        # --- Circular Gauges Card ---
        gauges_card = ctk.CTkFrame(
            left_col,
            fg_color=BG_CARD,
            corner_radius=14,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        gauges_card.grid(row=0, column=0, sticky="nsew", pady=(0, 12))

        gauges_header = ctk.CTkFrame(gauges_card, fg_color="transparent")
        gauges_header.pack(fill="x", padx=18, pady=(12, 4))

        ctk.CTkLabel(
            gauges_header,
            text="LIVE TELEMETRY",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#93C5FD",
        ).pack(side="left")

        self.telemetry_status_label = ctk.CTkLabel(
            gauges_header,
            text="● ACTIVE",
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color="#22C55E",
        )
        self.telemetry_status_label.pack(side="right")

        gauges_row = ctk.CTkFrame(gauges_card, fg_color="transparent")
        gauges_row.pack(fill="both", expand=True, padx=10, pady=(2, 12))
        gauges_row.grid_columnconfigure(0, weight=1)
        gauges_row.grid_columnconfigure(1, weight=1)
        gauges_row.grid_rowconfigure(0, weight=1)

        self.cpu_gauge = CircularGauge(
            gauges_row,
            title="CPU Load",
            initial_detail=f"{self._cpu_cores} Logical Cores",
            size=182,
            bg_color=BG_CARD,
        )
        self.cpu_gauge.grid(row=0, column=0, padx=4, pady=2)

        self.ram_gauge = CircularGauge(
            gauges_row,
            title="RAM Used",
            initial_detail="0.0 / 0.0 GB",
            size=182,
            bg_color=BG_CARD,
        )
        self.ram_gauge.grid(row=0, column=1, padx=4, pady=2)

        # --- Hero Smart Boost & Clean Card ---
        self.hero_card = ctk.CTkFrame(
            left_col,
            fg_color=BG_CARD,
            corner_radius=14,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        self.hero_card.grid(row=1, column=0, sticky="nsew")

        hero_header = ctk.CTkFrame(self.hero_card, fg_color="transparent")
        hero_header.pack(fill="x", padx=18, pady=(12, 4))

        ctk.CTkLabel(
            hero_header,
            text="ONE-CLICK OPTIMIZATION",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#93C5FD",
        ).pack(side="left")

        self.boost_badge = ctk.CTkLabel(
            hero_header,
            text="  READY  ",
            height=22,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#22C55E",
            fg_color="#122620",
            corner_radius=6,
        )
        self.boost_badge.pack(side="right")

        ctk.CTkLabel(
            self.hero_card,
            text="Safely wipes unused Windows Temp junk & auto-runs 10s after gaming.",
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
            anchor="w",
        ).pack(fill="x", padx=18, pady=(0, 10))

        self.clean_button = ctk.CTkButton(
            self.hero_card,
            text="⚡  SMART BOOST & CLEAN",
            height=60,
            corner_radius=12,
            font=ctk.CTkFont(size=17, weight="bold"),
            fg_color="#2563EB",
            hover_color="#1D4ED8",
            border_width=2,
            border_color="#3B82F6",
            text_color="#FFFFFF",
            command=self.start_temp_cleanup,
        )
        self.clean_button.pack(fill="x", padx=18, pady=(0, 10))

        self.clean_button.bind("<Enter>", self._on_hero_hover_enter)
        self.clean_button.bind("<Leave>", self._on_hero_hover_leave)

        # Custom Canvas sweeping neon progress beam (active while cleaning runs)
        self.sweep_canvas = tk.Canvas(
            self.hero_card,
            height=8,
            bg=BG_CARD,
            highlightthickness=0,
            bd=0,
        )
        self.sweep_canvas.pack(fill="x", padx=18, pady=(0, 6))
        self._sweep_track = self.sweep_canvas.create_rectangle(0, 1, 10, 7, fill="#222B3F", outline="")
        self._sweep_glow = self.sweep_canvas.create_rectangle(0, 0, 0, 8, fill="#1D4ED8", outline="", state="hidden")
        self._sweep_beam = self.sweep_canvas.create_rectangle(0, 1, 0, 7, fill="#38BDF8", outline="", state="hidden")
        self.sweep_canvas.bind("<Configure>", self._on_sweep_resize)

        self.boost_summary_label = ctk.CTkLabel(
            self.hero_card,
            text="Idle • Ready to boost your PC",
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
            anchor="w",
        )
        self.boost_summary_label.pack(fill="x", padx=18, pady=(0, 12))

        # ================= RIGHT COLUMN =================
        right_col = ctk.CTkFrame(
            parent,
            fg_color=BG_CARD,
            corner_radius=14,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        right_col.grid(row=2, column=1, sticky="nsew", padx=(8, 0))

        apps_header = ctk.CTkFrame(right_col, fg_color="transparent")
        apps_header.pack(fill="x", padx=16, pady=(12, 8))

        apps_title_box = ctk.CTkFrame(apps_header, fg_color="transparent")
        apps_title_box.pack(side="left")

        ctk.CTkLabel(
            apps_title_box,
            text="TOP RAM-USING APPS",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#93C5FD",
        ).pack(anchor="w")

        ctk.CTkLabel(
            apps_title_box,
            text="Click any app to inspect sub-processes • System apps protected",
            font=ctk.CTkFont(size=11),
            text_color=TEXT_MUTED,
        ).pack(anchor="w")

        header_actions = ctk.CTkFrame(apps_header, fg_color="transparent")
        header_actions.pack(side="right", pady=(2, 0))

        self.clear_sel_button = ctk.CTkButton(
            header_actions,
            text="Clear",
            width=58,
            height=30,
            corner_radius=8,
            font=ctk.CTkFont(size=11, weight="bold"),
            fg_color="#1F293D",
            hover_color="#303C56",
            text_color=TEXT_MUTED,
            command=self.clear_all_selections,
        )
        self.clear_sel_button.pack(side="left", padx=(0, 6))

        ctk.CTkButton(
            header_actions,
            text="↻ Refresh",
            width=82,
            height=30,
            corner_radius=8,
            font=ctk.CTkFont(size=12, weight="bold"),
            fg_color="#222B3F",
            hover_color="#303C56",
            command=self.refresh_top_apps,
        ).pack(side="left")

        self.apps_list_frame = ctk.CTkScrollableFrame(
            right_col,
            fg_color=BG_INNER,
            corner_radius=10,
        )
        self.apps_list_frame.pack(fill="both", expand=True, padx=16, pady=(2, 12))

        apps_footer = ctk.CTkFrame(right_col, fg_color="transparent")
        apps_footer.pack(fill="x", padx=16, pady=(0, 14))

        self.close_app_button = ctk.CTkButton(
            apps_footer,
            text="✕  CLOSE SELECTED (0)",
            height=48,
            corner_radius=10,
            font=ctk.CTkFont(size=14, weight="bold"),
            fg_color="#DC2626",
            hover_color="#B91C1C",
            border_width=2,
            border_color="#EF4444",
            text_color="#FFFFFF",
            command=self.close_selected_targets,
        )
        self.close_app_button.pack(fill="x")

    def _build_smart_features_tab(self, parent):
        """Dedicated Smart Features tab grouping all autopilot ON/OFF toggle switches."""
        scroll = ctk.CTkScrollableFrame(parent, fg_color="transparent")
        scroll.pack(fill="both", expand=True, padx=4, pady=(4, 2))

        header_box = ctk.CTkFrame(scroll, fg_color="transparent")
        header_box.pack(fill="x", padx=4, pady=(2, 10))

        ctk.CTkLabel(
            header_box,
            text="AUTOPILOT & SMART FEATURES",
            font=ctk.CTkFont(size=13, weight="bold"),
            text_color="#93C5FD",
        ).pack(anchor="w")

        ctk.CTkLabel(
            header_box,
            text="Every feature below runs with near-zero overhead and completely unloads when toggled OFF.",
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
        ).pack(anchor="w", pady=(2, 0))

        # 1. Edge Status Glow
        self.edge_glow_card, self.edge_glow_switch, self.edge_glow_badge = self._create_feature_card(
            scroll,
            title="Edge Status Glow",
            description=(
                "Draws a borderless, click-through 3-pixel ambient bar along the top monitor edge: "
                "invisible when healthy, soft purple pulse in Game Mode, amber/red above 85% CPU or RAM."
            ),
            variable=self.edge_glow_var,
            command=self.on_edge_glow_toggled,
            accent="#A855F7",
            badge_text="  OFF • ZERO OVERLAY  ",
        )

        # 2. Panic Hotkey (Ctrl+Shift+Space)
        panic_desc = (
            "Listens globally for Ctrl + Shift + Space even inside full-screen games. "
            "Instantly rescues RAM by stopping the top non-essential RAM hog (never system or active game), "
            "cleaning temp files, flashing a dashboard banner, and sending a Windows notification."
        )
        if keyboard is None:
            panic_desc += " (Run 'pip install keyboard' to enable.)"

        self.panic_card, self.panic_switch, self.panic_badge = self._create_feature_card(
            scroll,
            title="Panic Hotkey (Ctrl+Shift+Space)",
            description=panic_desc,
            variable=self.panic_hotkey_var,
            command=self.on_panic_hotkey_toggled,
            accent="#EF4444",
            badge_text="  OFF • UNHOOKED  ",
        )

        # 3. Idle Auto-Clean
        self.idle_card, self.idle_switch, self.idle_badge = self._create_feature_card(
            scroll,
            title="Idle Auto-Clean",
            description=(
                "Uses Windows GetLastInputInfo to detect 10 continuous minutes of mouse/keyboard inactivity "
                "(outside Game Mode), silently cleans Windows Temp once per away session, and logs freed space on the Dashboard."
            ),
            variable=self.idle_clean_var,
            command=self.on_idle_clean_toggled,
            accent="#10B981",
            badge_text="  OFF • DISABLED  ",
        )

        # 4. App Freeze Mode
        self.freeze_card, self.freeze_mode_switch, self.frozen_count_badge = self._create_feature_card(
            scroll,
            title="App Freeze Mode",
            description=(
                "Adds a 'Freeze ❄️' button to every app on the Dashboard so you can suspend heavy background apps "
                "to 0.0% CPU without closing tabs. Turning OFF automatically thaws all frozen apps."
            ),
            variable=self.freeze_mode_var,
            command=self.on_freeze_mode_toggled,
            accent="#0EA5E9",
            badge_text="  ❄️ 0 FROZEN  ",
        )

        # 5. Lag Recorder
        self.lag_card, self.lag_recorder_switch, self.lag_buffer_badge = self._create_feature_card(
            scroll,
            title="Lag Recorder",
            description=(
                "Silently keeps a 60-second rolling buffer (30 samples, < 1 MB RAM) of CPU/RAM spikes and culprit apps "
                "for the 'Why Did My PC Just Lag?' forensics tool. Turning OFF clears the buffer immediately."
            ),
            variable=self.lag_recorder_var,
            command=self.on_lag_recorder_toggled,
            accent="#8B5CF6",
            badge_text="  ● REC 0s / 60s  ",
            active_on_start=True,
        )

    def _create_feature_card(
        self,
        parent,
        title,
        description,
        variable,
        command,
        accent,
        badge_text,
        active_on_start=False,
    ):
        card = ctk.CTkFrame(
            parent,
            fg_color=BG_CARD,
            corner_radius=12,
            border_width=1,
            border_color=accent if active_on_start else BORDER_SUBTLE,
        )
        card.pack(fill="x", padx=4, pady=5)

        inner = ctk.CTkFrame(card, fg_color="transparent")
        inner.pack(fill="x", padx=16, pady=13)

        left = ctk.CTkFrame(inner, fg_color="transparent")
        left.pack(side="left", fill="x", expand=True, padx=(0, 14))

        top_row = ctk.CTkFrame(left, fg_color="transparent")
        top_row.pack(fill="x")

        switch = ctk.CTkSwitch(
            top_row,
            text=title,
            variable=variable,
            onvalue=True,
            offvalue=False,
            command=command,
            font=ctk.CTkFont(size=14, weight="bold"),
            text_color=TEXT_PRIMARY,
            progress_color=accent,
            button_color="#F8FAFC",
            fg_color="#334155",
        )
        switch.pack(side="left")

        badge = ctk.CTkLabel(
            top_row,
            text=badge_text,
            height=22,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color="#C4B5FD" if active_on_start else TEXT_MUTED,
            fg_color="#231942" if active_on_start else "#1A2233",
            corner_radius=6,
        )
        badge.pack(side="right")

        ctk.CTkLabel(
            left,
            text=description,
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
            anchor="w",
            justify="left",
            wraplength=920,
        ).pack(fill="x", pady=(6, 0))

        return card, switch, badge

    def _build_startup_tab(self, parent):
        uninstall_card = ctk.CTkFrame(
            parent,
            fg_color=BG_CARD,
            corner_radius=14,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        uninstall_card.pack(fill="x", pady=(6, 12))

        uninstall_inner = ctk.CTkFrame(uninstall_card, fg_color="transparent")
        uninstall_inner.pack(fill="x", padx=18, pady=14)

        uninstall_text = ctk.CTkFrame(uninstall_inner, fg_color="transparent")
        uninstall_text.pack(side="left", fill="x", expand=True)

        ctk.CTkLabel(
            uninstall_text,
            text="Uninstall Unwanted Software",
            font=ctk.CTkFont(size=15, weight="bold"),
            text_color=TEXT_PRIMARY,
        ).pack(anchor="w")

        ctk.CTkLabel(
            uninstall_text,
            text="Opens Windows Installed Apps so you can safely uninstall programs.",
            font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
        ).pack(anchor="w", pady=(2, 0))

        ctk.CTkButton(
            uninstall_inner,
            text="Open Installed Apps",
            width=180,
            height=42,
            corner_radius=10,
            font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#2563EB",
            hover_color="#1D4ED8",
            border_width=1,
            border_color="#3B82F6",
            command=self.open_installed_apps,
        ).pack(side="right", padx=(12, 0))

        startup_card = ctk.CTkFrame(
            parent,
            fg_color=BG_CARD,
            corner_radius=14,
            border_width=1,
            border_color=BORDER_SUBTLE,
        )
        startup_card.pack(fill="both", expand=True)

        startup_header = ctk.CTkFrame(startup_card, fg_color="transparent")
        startup_header.pack(fill="x", padx=18, pady=(14, 6))

        ctk.CTkLabel(
            startup_header,
            text="USER STARTUP PROGRAMS (HKCU\\...\\Run)",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="#93C5FD",
        ).pack(side="left")

        ctk.CTkButton(
            startup_header,
            text="↻ Refresh",
            width=88,
            height=30,
            corner_radius=8,
            font=ctk.CTkFont(size=12, weight="bold"),
            fg_color="#222B3F",
            hover_color="#303C56",
            command=self.refresh_startup_apps,
        ).pack(side="right")

        self.startup_list_frame = ctk.CTkScrollableFrame(
            startup_card,
            fg_color=BG_INNER,
            corner_radius=10,
        )
        self.startup_list_frame.pack(fill="both", expand=True, padx=18, pady=(4, 10))

        ctk.CTkLabel(
            startup_card,
            text="Toggles safely sync with Windows Task Manager without deleting registry entries.",
            font=ctk.CTkFont(size=11),
            text_color=TEXT_MUTED,
            anchor="w",
        ).pack(fill="x", padx=18, pady=(0, 12))

    def _update_active_features_pill(self):
        if self._is_quitting:
            return
        active = sum((
            1 if self.edge_glow_enabled else 0,
            1 if self.panic_hotkey_enabled else 0,
            1 if self.idle_clean_enabled else 0,
            1 if self.freeze_mode_enabled else 0,
            1 if self.lag_recorder_enabled else 0,
        ))
        if active > 0:
            self.active_features_pill.configure(
                text=f"  {active} AUTOPILOT ON  ",
                text_color="#34D399",
                fg_color="#112A24",
            )
        else:
            self.active_features_pill.configure(
                text="  AUTOPILOT OFF  ",
                text_color=TEXT_MUTED,
                fg_color="#1A2233",
            )

    # ------------------------------------------------------------------
    # Feature 1: Ambient Screen Edge Glow (3px Click-Through Overlay)
    # ------------------------------------------------------------------
    def on_edge_glow_toggled(self):
        enabled = bool(self.edge_glow_var.get())
        self.edge_glow_enabled = enabled

        if enabled:
            if self._edge_glow_overlay is None:
                self._edge_glow_overlay = EdgeGlowOverlay(self)
            self.edge_glow_card.configure(border_color="#A855F7")
            self.edge_glow_badge.configure(
                text="  ● ACTIVE • TOP EDGE  ",
                text_color="#D8B4FE",
                fg_color="#2A1B47",
            )
            self._poll_edge_glow()
            self._set_status(
                "Edge Status Glow ON — 3px click-through ambient bar active at top monitor edge.",
                "#C084FC",
            )
        else:
            if self._edge_glow_poll_after_id is not None:
                self.after_cancel(self._edge_glow_poll_after_id)
                self._edge_glow_poll_after_id = None
            if self._edge_glow_overlay is not None:
                self._edge_glow_overlay.destroy()
                self._edge_glow_overlay = None
            self.edge_glow_card.configure(border_color=BORDER_SUBTLE)
            self.edge_glow_badge.configure(
                text="  OFF • ZERO OVERLAY  ",
                text_color=TEXT_MUTED,
                fg_color="#1A2233",
            )
            self._set_status("Edge Status Glow OFF — overlay destroyed (zero resources used).", TEXT_MUTED)

        self._update_active_features_pill()

    def _poll_edge_glow(self):
        self._edge_glow_poll_after_id = None
        if not self.edge_glow_enabled or self._is_quitting or self._edge_glow_overlay is None:
            return

        # Reuse dashboard metrics when visible; sample directly only in tray or Game Mode
        if self._in_tray or self._game_mode_active:
            cpu_val = psutil.cpu_percent(interval=None)
            ram_val = psutil.virtual_memory().percent
        else:
            cpu_val = self._target_cpu
            ram_val = self._target_ram

        self._edge_glow_overlay.update_state(cpu_val, ram_val, self._game_mode_active)
        self._edge_glow_poll_after_id = self.after(EDGE_GLOW_POLL_MS, self._poll_edge_glow)

    # ------------------------------------------------------------------
    # Feature 2: Global Panic Hotkey (Ctrl+Shift+Space)
    # ------------------------------------------------------------------
    def on_panic_hotkey_toggled(self):
        enabled = bool(self.panic_hotkey_var.get())

        if enabled:
            if keyboard is None:
                self.panic_hotkey_var.set(False)
                self.panic_hotkey_enabled = False
                self._set_status(
                    "Install the 'keyboard' library first: run 'pip install keyboard' in PowerShell.",
                    "#F97316",
                )
                return

            try:
                self._unhook_panic_hotkey()
                self._panic_hotkey_handle = keyboard.add_hotkey(
                    PANIC_HOTKEY_COMBO,
                    self._on_panic_hotkey_pressed,
                    suppress=False,
                )
                self.panic_hotkey_enabled = True
                self.panic_card.configure(border_color="#EF4444")
                self.panic_badge.configure(
                    text="  ● ARMED (CTRL+SHIFT+SPACE)  ",
                    text_color="#FCA5A5",
                    fg_color="#3B1519",
                )
                self._set_status(
                    "Panic Hotkey ARMED — press Ctrl+Shift+Space anytime for emergency RAM rescue.",
                    "#F87171",
                )
            except Exception as exc:
                self.panic_hotkey_var.set(False)
                self.panic_hotkey_enabled = False
                self._set_status(
                    f"Could not bind global hotkey ({exc}). Try running as Administrator.",
                    "#EF4444",
                )
        else:
            self._unhook_panic_hotkey()
            self.panic_hotkey_enabled = False
            self.panic_card.configure(border_color=BORDER_SUBTLE)
            self.panic_badge.configure(
                text="  OFF • UNHOOKED  ",
                text_color=TEXT_MUTED,
                fg_color="#1A2233",
            )
            self._set_status("Panic Hotkey OFF — global shortcut completely unhooked.", TEXT_MUTED)

        self._update_active_features_pill()

    def _unhook_panic_hotkey(self):
        if keyboard is not None and self._panic_hotkey_handle is not None:
            try:
                keyboard.remove_hotkey(self._panic_hotkey_handle)
            except Exception:
                pass
            self._panic_hotkey_handle = None

    def _on_panic_hotkey_pressed(self):
        """Called on keyboard's background listener thread — safely dispatch to main UI thread."""
        if not self.panic_hotkey_enabled or self._is_quitting:
            return
        try:
            self.after(0, self.trigger_panic_rescue)
        except Exception:
            pass

    def trigger_panic_rescue(self):
        if self._is_quitting or self._is_panicking:
            return
        now = time.monotonic()
        if (now - self._last_panic_time) < PANIC_DEBOUNCE_SEC:
            return

        self._is_panicking = True
        self._last_panic_time = now
        fg_pid = get_foreground_pid()

        self._set_status("🚨 Panic Rescue triggered! Freeing RAM & cleaning temp files...", "#F97316")
        threading.Thread(
            target=self._run_panic_rescue_worker,
            args=(fg_pid,),
            daemon=True,
        ).start()

    def _run_panic_rescue_worker(self, fg_pid):
        ram_before = psutil.virtual_memory().used

        # Determine the active foreground app name so we NEVER touch the active game/window
        fg_app_lower = ""
        if fg_pid > 4 and fg_pid != CURRENT_PID:
            try:
                fg_app_lower = (psutil.Process(fg_pid).name() or "").lower()
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                fg_app_lower = ""

        # Find the top non-essential RAM hog (excluding Windows system apps, self, and active game)
        ram_by_app = {}
        for proc in psutil.process_iter(["pid", "name", "memory_info"]):
            try:
                pid = proc.info["pid"]
                name = proc.info["name"]
                mem_info = proc.info["memory_info"]
                if not name or not mem_info or pid <= 4 or pid == CURRENT_PID or pid == fg_pid:
                    continue
                lower = name.lower()
                if lower in PROTECTED_PROCESSES or (fg_app_lower and lower == fg_app_lower):
                    continue
                if lower in ram_by_app:
                    ram_by_app[lower]["bytes"] += mem_info.rss
                    ram_by_app[lower]["pids"].append(pid)
                else:
                    ram_by_app[lower] = {
                        "key": lower,
                        "display_name": name,
                        "bytes": mem_info.rss,
                        "pids": [pid],
                    }
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        action_desc = "No non-essential RAM hog found"
        hog_name = None
        hog_key = None
        hog_action = None

        if ram_by_app:
            top_hog = max(ram_by_app.values(), key=lambda x: x["bytes"])
            hog_name = top_hog["display_name"]
            hog_key = top_hog["key"]

            # Close the top non-essential RAM hog to immediately reclaim RAM; fallback to freeze if needed
            matched = []
            for pid in top_hog["pids"]:
                try:
                    p = psutil.Process(pid)
                    if (p.name() or "").lower() == hog_key and hog_key not in PROTECTED_PROCESSES:
                        p.terminate()
                        matched.append(p)
                except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                    continue

            gone, alive = psutil.wait_procs(matched, timeout=1.5)
            for p in alive:
                try:
                    p.kill()
                    gone.append(p)
                except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                    pass

            if gone:
                hog_action = "closed"
                action_desc = f"Closed {hog_name} ({format_bytes(top_hog['bytes'])})"
            else:
                # Fallback: try suspending it if termination was blocked
                suspended = 0
                for pid in top_hog["pids"]:
                    try:
                        p = psutil.Process(pid)
                        if (p.name() or "").lower() == hog_key and hog_key not in PROTECTED_PROCESSES:
                            p.suspend()
                            suspended += 1
                    except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                        continue
                if suspended > 0:
                    hog_action = "frozen"
                    action_desc = f"Froze {hog_name} ({suspended} procs)"

        # Clean Windows temp files and trim optimizer memory
        deleted_items, _skipped, freed_temp_bytes, _err = self._perform_safe_temp_cleanup()
        trim_own_memory()
        time.sleep(0.35)

        ram_after = psutil.virtual_memory()
        ram_rescued = max(0, ram_before - ram_after.used)

        if not self._is_quitting:
            self.after(
                0,
                self._finish_panic_rescue,
                action_desc,
                hog_key,
                hog_action,
                ram_rescued,
                ram_after.percent,
                freed_temp_bytes,
                deleted_items,
            )

    def _finish_panic_rescue(
        self,
        action_desc,
        hog_key,
        hog_action,
        ram_rescued,
        ram_after_percent,
        freed_temp_bytes,
        deleted_items,
    ):
        self._is_panicking = False
        if self._is_quitting:
            return

        if hog_action == "closed" and hog_key:
            self.frozen_apps.pop(hog_key, None)
            self._update_freeze_ui_summary()

        ram_str = format_bytes(ram_rescued)
        temp_str = format_bytes(freed_temp_bytes)
        banner_msg = (
            f"🚨 PANIC RESCUE COMPLETE: {action_desc} • Rescued {ram_str} RAM "
            f"(now {ram_after_percent:.1f}%) • Cleaned {temp_str} temp ({deleted_items} items)."
        )

        self._show_panic_banner(banner_msg)
        self._set_status(banner_msg, "#22C55E")
        self.boost_summary_label.configure(
            text=f"Panic Rescue: {ram_str} RAM rescued • {temp_str} temp cleaned",
            text_color="#22C55E",
        )

        # Force toast notification even if triggered while inside a full-screen game
        self._send_notification(
            title="PC Optimizer — Emergency Panic Rescue",
            message=f"Rescued {ram_str} of RAM ({action_desc}) & cleaned {temp_str} temp. RAM now {ram_after_percent:.1f}%.",
            force=True,
        )

        if not self._in_tray and not self._game_mode_active:
            self.refresh_top_apps()

    def _show_panic_banner(self, message):
        if self._is_quitting:
            return
        if self._panic_banner_after_id is not None:
            self.after_cancel(self._panic_banner_after_id)
            self._panic_banner_after_id = None

        self.panic_banner_label.configure(text=message)
        self.panic_banner.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(4, 4))
        self._panic_banner_after_id = self.after(6000, self._hide_panic_banner)

    def _hide_panic_banner(self):
        if self._panic_banner_after_id is not None:
            self.after_cancel(self._panic_banner_after_id)
            self._panic_banner_after_id = None
        if not self._is_quitting:
            self.panic_banner.grid_forget()

    # ------------------------------------------------------------------
    # Feature 3: Smart Idle Auto-Cleaner (GetLastInputInfo)
    # ------------------------------------------------------------------
    def on_idle_clean_toggled(self):
        enabled = bool(self.idle_clean_var.get())
        self.idle_clean_enabled = enabled

        if enabled:
            self._cleaned_this_idle_session = False
            self.idle_card.configure(border_color="#10B981")
            self.idle_badge.configure(
                text="  ● ARMED (10 MIN IDLE)  ",
                text_color="#6EE7B7",
                fg_color="#0E2F26",
            )
            if "None yet" in self.away_clean_badge.cget("text"):
                self.away_clean_badge.configure(
                    text="  🌙 Last Away-Clean: Armed (triggers after 10m idle)  ",
                    text_color="#6EE7B7",
                    fg_color="#0E2F26",
                )
            self._schedule_idle_check()
            self._set_status(
                "Idle Auto-Clean ON — silently cleans temp files once after 10 minutes away.",
                "#34D399",
            )
        else:
            if self._idle_check_after_id is not None:
                self.after_cancel(self._idle_check_after_id)
                self._idle_check_after_id = None
            self._cleaned_this_idle_session = False
            self.idle_card.configure(border_color=BORDER_SUBTLE)
            self.idle_badge.configure(
                text="  OFF • DISABLED  ",
                text_color=TEXT_MUTED,
                fg_color="#1A2233",
            )
            if "Armed" in self.away_clean_badge.cget("text"):
                self.away_clean_badge.configure(
                    text="  🌙 Last Away-Clean: None yet (Idle Auto-Clean OFF)  ",
                    text_color=TEXT_MUTED,
                    fg_color=BG_INNER,
                )
            self._set_status("Idle Auto-Clean OFF — idle monitoring disabled.", TEXT_MUTED)

        self._update_active_features_pill()

    def _schedule_idle_check(self):
        if not self.idle_clean_enabled or self._is_quitting:
            return
        if self._idle_check_after_id is not None:
            self.after_cancel(self._idle_check_after_id)
        self._idle_check_after_id = self.after(IDLE_CHECK_MS, self._check_system_idle)

    def _check_system_idle(self):
        self._idle_check_after_id = None
        if not self.idle_clean_enabled or self._is_quitting:
            return

        idle_secs = get_system_idle_seconds()

        # User has returned to mouse/keyboard — arm again for the next away session
        if idle_secs < IDLE_RETURN_SECONDS:
            self._cleaned_this_idle_session = False
        elif (
            idle_secs >= IDLE_TRIGGER_SECONDS
            and not self._game_mode_active
            and not self._cleaned_this_idle_session
            and not self._is_cleaning
            and not self._is_panicking
        ):
            self._cleaned_this_idle_session = True
            self._is_cleaning = True
            threading.Thread(target=self._run_idle_cleanup_worker, daemon=True).start()

        self._schedule_idle_check()

    def _run_idle_cleanup_worker(self):
        deleted_items, skipped_items, freed_bytes, error_msg = self._perform_safe_temp_cleanup()
        trim_own_memory()
        if not self._is_quitting:
            self.after(0, self._finish_idle_cleanup, deleted_items, skipped_items, freed_bytes, error_msg)

    def _finish_idle_cleanup(self, deleted_items, skipped_items, freed_bytes, error_msg):
        self._is_cleaning = False
        if self._is_quitting or error_msg:
            return

        freed_str = format_bytes(freed_bytes)
        stamp = time.strftime("%H:%M")

        # Update sleek 'Last Away-Clean Summary' badge on the Dashboard (silent — no intrusive popup)
        self.away_clean_badge.configure(
            text=f"  🌙 Last Away-Clean: Freed {freed_str} ({deleted_items} items) @ {stamp}  ",
            text_color="#6EE7B7",
            fg_color="#0E2F26",
        )
        self.idle_badge.configure(
            text=f"  ● LAST CLEAN: {freed_str} @ {stamp}  ",
            text_color="#6EE7B7",
            fg_color="#0E2F26",
        )
        self._set_status(
            f"Silent Idle Auto-Clean finished while away: freed {freed_str} ({deleted_items} items).",
            "#34D399",
        )

    # ------------------------------------------------------------------
    # 60-Second Lag Forensics (Rolling Deque + Animated Modal Card)
    # ------------------------------------------------------------------
    def _update_lag_recorder_badge(self):
        if self._is_quitting:
            return
        if self.lag_recorder_enabled:
            secs = min(60, len(self.lag_buffer) * 2)
            self.lag_buffer_badge.configure(
                text=f"  ● REC {secs}s / 60s  ",
                text_color="#C4B5FD",
                fg_color="#231942",
            )
            self.dashboard_lag_pill.configure(
                text=f"  ● REC {secs}s/60s  ",
                text_color="#C4B5FD",
                fg_color="#231942",
            )
        else:
            self.lag_buffer_badge.configure(
                text="  OFF • BUFFER CLEARED  ",
                text_color=TEXT_MUTED,
                fg_color="#1A2233",
            )
            self.dashboard_lag_pill.configure(
                text="  REC OFF  ",
                text_color=TEXT_MUTED,
                fg_color="#1A2233",
            )

    def on_lag_recorder_toggled(self):
        enabled = bool(self.lag_recorder_var.get())
        self.lag_recorder_enabled = enabled

        if enabled:
            self.lag_card.configure(border_color="#8B5CF6")
            self._update_lag_recorder_badge()
            self._set_status(
                "Lag Recorder ON — silently recording 60s rolling snapshots (< 1 MB RAM).",
                "#A78BFA",
            )
            if self._in_tray and not self._game_mode_active:
                self._schedule_tray_lag_sample()
        else:
            if self._tray_lag_after_id is not None:
                self.after_cancel(self._tray_lag_after_id)
                self._tray_lag_after_id = None
            self.lag_buffer.clear()
            self.lag_card.configure(border_color=BORDER_SUBTLE)
            self._update_lag_recorder_badge()
            self._set_status("Lag Recorder OFF — recording paused and 60s buffer cleared.", TEXT_MUTED)

        self._update_active_features_pill()

    def _record_lag_sample(self, culprit_info, total_cpu=None, total_ram=None):
        if not self.lag_recorder_enabled or self._game_mode_active or self._is_quitting:
            return

        cpu_val = self._target_cpu if total_cpu is None else total_cpu
        ram_val = self._target_ram if total_ram is None else total_ram

        sample = {
            "timestamp": time.time(),
            "time_str": time.strftime("%H:%M:%S"),
            "total_cpu": float(cpu_val),
            "total_ram": float(ram_val),
            "culprit_name": culprit_info["display_name"] if culprit_info else "Idle / None",
            "culprit_key": culprit_info["key"] if culprit_info else None,
            "culprit_cpu": float(culprit_info["cpu"]) if culprit_info else 0.0,
            "culprit_ram_mb": float(culprit_info["rss"]) / (1024.0 * 1024.0) if culprit_info else 0.0,
            "culprit_protected": bool(culprit_info["protected"]) if culprit_info else False,
        }
        self.lag_buffer.append(sample)

        if not self._in_tray:
            self._update_lag_recorder_badge()

    def _schedule_tray_lag_sample(self):
        if (
            not self._in_tray
            or not self.lag_recorder_enabled
            or self._game_mode_active
            or self._is_quitting
        ):
            return
        if self._tray_lag_after_id is not None:
            self.after_cancel(self._tray_lag_after_id)
        self._tray_lag_after_id = self.after(TRAY_LAG_SAMPLE_MS, self._run_tray_lag_tick)

    def _run_tray_lag_tick(self):
        self._tray_lag_after_id = None
        if (
            not self._in_tray
            or not self.lag_recorder_enabled
            or self._game_mode_active
            or self._is_quitting
        ):
            return

        if not self._is_sampling_tray_lag:
            self._is_sampling_tray_lag = True
            threading.Thread(target=self._tray_lag_worker, daemon=True).start()

        self._schedule_tray_lag_sample()

    def _tray_lag_worker(self):
        total_cpu = psutil.cpu_percent(interval=None)
        total_ram = psutil.virtual_memory().percent
        cores = max(1, self._cpu_cores)
        cpu_by_app = {}

        for proc in psutil.process_iter(["pid", "name", "memory_info", "cpu_percent"]):
            try:
                pid = proc.info["pid"]
                name = proc.info["name"]
                if not name or pid <= 4 or pid == CURRENT_PID:
                    continue
                lower = name.lower()
                if lower in IGNORED_CULPRIT_NAMES:
                    continue

                raw_cpu = proc.info["cpu_percent"]
                cpu_pct = min(100.0, max(0.0, (raw_cpu or 0.0) / cores))
                mem_info = proc.info["memory_info"]
                rss = mem_info.rss if mem_info else 0

                if lower in cpu_by_app:
                    cpu_by_app[lower]["cpu"] = min(100.0, cpu_by_app[lower]["cpu"] + cpu_pct)
                    cpu_by_app[lower]["rss"] += rss
                else:
                    cpu_by_app[lower] = {
                        "key": lower,
                        "display_name": name,
                        "cpu": cpu_pct,
                        "rss": rss,
                        "protected": lower in PROTECTED_PROCESSES,
                    }
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        culprit = None
        if cpu_by_app:
            culprit = max(cpu_by_app.values(), key=lambda x: (x["cpu"], x["rss"]))

        if not self._is_quitting:
            self.after(0, self._finish_tray_lag_sample, culprit, total_cpu, total_ram)

    def _finish_tray_lag_sample(self, culprit, total_cpu, total_ram):
        self._is_sampling_tray_lag = False
        if not self._is_quitting and self._in_tray and self.lag_recorder_enabled:
            self._record_lag_sample(culprit, total_cpu=total_cpu, total_ram=total_ram)

    def open_lag_forensics(self):
        if self._is_quitting:
            return
        if self._forensics_modal is not None and self._forensics_modal.winfo_exists():
            self._forensics_modal.lift()
            self._forensics_modal.focus_force()
            return
        self._forensics_modal = LagForensicsModal(self, self.lag_buffer)

    def _on_forensics_modal_closed(self):
        self._forensics_modal = None

    # ------------------------------------------------------------------
    # App Freeze & Thaw Master Switch + Safe Process Suspend / Resume
    # ------------------------------------------------------------------
    def _update_freeze_ui_summary(self):
        if self._is_quitting:
            return
        count = len(self.frozen_apps)
        if count > 0:
            self.frozen_count_badge.configure(
                text=f"  ❄️ {count} FROZEN  ",
                text_color="#38BDF8",
                fg_color="#12324A",
            )
            self.dashboard_frozen_badge.configure(text=f"  ❄️ {count} Frozen  ")
            if not self.dashboard_frozen_badge.winfo_ismapped():
                self.dashboard_frozen_badge.pack(side="left", padx=(0, 8), pady=8)
        else:
            self.frozen_count_badge.configure(
                text="  ❄️ 0 FROZEN  ",
                text_color="#38BDF8" if self.freeze_mode_enabled else TEXT_MUTED,
                fg_color="#12324A" if self.freeze_mode_enabled else "#1A2233",
            )
            if self.dashboard_frozen_badge.winfo_ismapped():
                self.dashboard_frozen_badge.pack_forget()

        self.freeze_card.configure(
            border_color="#0EA5E9" if self.freeze_mode_enabled else BORDER_SUBTLE
        )

    def on_freeze_mode_toggled(self):
        enabled = bool(self.freeze_mode_var.get())
        self.freeze_mode_enabled = enabled

        for card in self.app_cards.values():
            card.set_freeze_mode(enabled)

        if enabled:
            self._update_freeze_ui_summary()
            self._set_status(
                "App Freeze Mode ON — Freeze ❄️ buttons enabled on Dashboard (system apps protected).",
                "#38BDF8",
            )
        else:
            if self.frozen_apps:
                snapshot = {k: set(v) for k, v in self.frozen_apps.items()}
                self.frozen_apps.clear()
                for card in self.app_cards.values():
                    if card.is_frozen:
                        card.set_frozen(False)
                self._update_freeze_ui_summary()
                self._set_status("App Freeze Mode OFF — thawing all frozen apps...", "#F97316")
                threading.Thread(
                    target=self._thaw_all_worker,
                    args=(snapshot,),
                    daemon=True,
                ).start()
            else:
                self._update_freeze_ui_summary()
                self._set_status("App Freeze Mode OFF.", TEXT_MUTED)

        self._update_active_features_pill()

    def toggle_freeze_app(self, app_key, display_name_override=None):
        if not self.freeze_mode_enabled or app_key in self._freezing_apps:
            return

        if app_key in PROTECTED_PROCESSES:
            self._set_status(f"Blocked: '{app_key}' is a protected Windows process.", "#EF4444")
            return

        action = "thaw" if app_key in self.frozen_apps else "freeze"
        self._freezing_apps.add(app_key)

        card = self.app_cards.get(app_key)
        display_name = display_name_override or (card.display_name if card else app_key)
        if card:
            card.set_freeze_busy(True)

        known_pids = set(self.frozen_apps.get(app_key, set()))
        verb = "Freezing" if action == "freeze" else "Thawing"
        self._set_status(f"{verb} {display_name}...", "#38BDF8" if action == "freeze" else "#F97316")

        threading.Thread(
            target=self._freeze_or_thaw_worker,
            args=(app_key, display_name, action, known_pids),
            daemon=True,
        ).start()

    def _freeze_or_thaw_worker(self, app_key, display_name, action, known_pids):
        affected_pids = set()
        denied_count = 0

        if action == "freeze":
            for proc in psutil.process_iter(["pid", "name"]):
                try:
                    pid = proc.info["pid"]
                    name = proc.info["name"]
                    if not name or pid <= 4 or pid == CURRENT_PID:
                        continue
                    lower = name.lower()
                    if lower == app_key and lower not in PROTECTED_PROCESSES:
                        proc.suspend()
                        affected_pids.add(pid)
                except psutil.AccessDenied:
                    denied_count += 1
                except (psutil.NoSuchProcess, psutil.ZombieProcess):
                    continue
        else:
            target_pids = set(known_pids)
            for proc in psutil.process_iter(["pid", "name"]):
                try:
                    pid = proc.info["pid"]
                    name = proc.info["name"]
                    if not name or pid <= 4 or pid == CURRENT_PID:
                        continue
                    lower = name.lower()
                    if lower == app_key and lower not in PROTECTED_PROCESSES:
                        target_pids.add(pid)
                except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                    continue

            for pid in target_pids:
                if pid <= 4 or pid == CURRENT_PID:
                    continue
                try:
                    proc = psutil.Process(pid)
                    if (proc.name() or "").lower() in PROTECTED_PROCESSES:
                        continue
                    proc.resume()
                    affected_pids.add(pid)
                except psutil.AccessDenied:
                    denied_count += 1
                except (psutil.NoSuchProcess, psutil.ZombieProcess):
                    continue

        if not self._is_quitting:
            self.after(
                0,
                self._finish_freeze_toggle,
                app_key,
                display_name,
                action,
                affected_pids,
                denied_count,
            )

    def _finish_freeze_toggle(self, app_key, display_name, action, affected_pids, denied_count):
        self._freezing_apps.discard(app_key)
        if self._is_quitting:
            return

        card = self.app_cards.get(app_key)

        if action == "freeze":
            if not self.freeze_mode_enabled:
                if affected_pids:
                    threading.Thread(
                        target=self._thaw_all_worker,
                        args=({app_key: set(affected_pids)},),
                        daemon=True,
                    ).start()
                if card:
                    card.set_frozen(False)
                    card.set_freeze_busy(False)
                self._update_freeze_ui_summary()
                return

            if affected_pids:
                self.frozen_apps[app_key] = set(affected_pids)
                if card:
                    card.set_frozen(True)
                    card.set_freeze_busy(False)
                    if card.is_expanded:
                        card._sync_sub_rows()
                extra = f" ({denied_count} needed Admin)" if denied_count > 0 else ""
                self._set_status(
                    f"❄️ Froze {display_name} ({len(affected_pids)} process(es) suspended to 0.0% CPU){extra}.",
                    "#38BDF8",
                )
            elif denied_count > 0:
                if card:
                    card.set_freeze_busy(False)
                self._set_status(
                    f"Access denied freezing {display_name}. Run as Administrator to freeze it.",
                    "#EF4444",
                )
            else:
                if card:
                    card.set_freeze_busy(False)
                self._set_status(f"{display_name} is no longer running.", TEXT_MUTED)
        else:
            self.frozen_apps.pop(app_key, None)
            if card:
                card.set_frozen(False)
                card.set_freeze_busy(False)
                if card.is_expanded:
                    card._sync_sub_rows()

            if affected_pids:
                self._set_status(
                    f"🔥 Thawed {display_name} ({len(affected_pids)} process(es) resumed).",
                    "#22C55E",
                )
            elif denied_count > 0:
                self._set_status(
                    f"Access denied thawing {display_name}. Run as Administrator.",
                    "#EF4444",
                )
            else:
                self._set_status(f"{display_name} already resumed or closed.", TEXT_MUTED)

        self._update_freeze_ui_summary()
        self.refresh_top_apps()

    def _thaw_all_sync(self, snapshot):
        resumed_count = 0
        target_pids = set()
        app_keys = set(snapshot.keys())

        for pids in snapshot.values():
            target_pids.update(pids)

        for proc in psutil.process_iter(["pid", "name"]):
            try:
                pid = proc.info["pid"]
                name = proc.info["name"]
                if not name or pid <= 4 or pid == CURRENT_PID:
                    continue
                lower = name.lower()
                if lower in app_keys and lower not in PROTECTED_PROCESSES:
                    target_pids.add(pid)
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        for pid in target_pids:
            if pid <= 4 or pid == CURRENT_PID:
                continue
            try:
                proc = psutil.Process(pid)
                if (proc.name() or "").lower() in PROTECTED_PROCESSES:
                    continue
                proc.resume()
                resumed_count += 1
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        return resumed_count

    def _thaw_all_worker(self, snapshot):
        resumed_count = self._thaw_all_sync(snapshot)
        if not self._is_quitting:
            self.after(0, self._finish_thaw_all, len(snapshot), resumed_count)

    def _finish_thaw_all(self, app_count, resumed_count):
        if self._is_quitting:
            return
        self._update_freeze_ui_summary()
        self._set_status(
            f"🔥 App Freeze Mode OFF — auto-thawed {app_count} app(s) ({resumed_count} process(es) resumed).",
            "#22C55E",
        )
        self.refresh_top_apps()

    # ------------------------------------------------------------------
    # Expandable Top RAM Apps, Multi-Select PIDs & Fade/Collapse Closing
    # ------------------------------------------------------------------
    def on_app_card_clicked(self, app_key):
        if app_key not in self.app_cards or app_key in self._fading_apps:
            return

        if self.selected_main_app and self.selected_main_app in self.app_cards:
            self.app_cards[self.selected_main_app].set_selected(False)

        self.selected_main_app = app_key
        card = self.app_cards[app_key]
        card.set_selected(True)

        if card.is_expanded:
            self.expanded_apps.discard(app_key)
            card.collapse(animate=True)
        else:
            self.expanded_apps.add(app_key)
            card.expand(animate=True)

        self.update_close_button()

    def clear_all_selections(self):
        self.selected_pids.clear()
        if self.selected_main_app and self.selected_main_app in self.app_cards:
            self.app_cards[self.selected_main_app].set_selected(False)
        self.selected_main_app = ""

        for card in self.app_cards.values():
            if card.is_expanded:
                card._sync_sub_rows()

        self.update_close_button()
        self._set_status("Cleared process selection.", TEXT_MUTED)

    def update_close_button(self):
        if self._is_closing_app or self._is_quitting:
            return

        pid_count = len(self.selected_pids)
        if pid_count > 0:
            self.close_app_button.configure(text=f"✕  CLOSE SELECTED ({pid_count})")
        elif self.selected_main_app and self.selected_main_app in self.app_cards:
            card = self.app_cards[self.selected_main_app]
            short_name = (
                card.display_name
                if len(card.display_name) <= 22
                else card.display_name[:19] + "..."
            )
            self.close_app_button.configure(
                text=f"✕  CLOSE {short_name} ({len(card.processes)})"
            )
        else:
            self.close_app_button.configure(text="✕  CLOSE SELECTED (0)")

    def refresh_top_apps(self):
        if self._apps_after_id is not None:
            self.after_cancel(self._apps_after_id)
            self._apps_after_id = None

        if self._in_tray or self._is_quitting or self._game_mode_active:
            return

        if not self._is_refreshing_apps:
            self._is_refreshing_apps = True
            threading.Thread(target=self._scan_top_apps_worker, daemon=True).start()

        self._apps_after_id = self.after(APPS_REFRESH_MS, self.refresh_top_apps)

    def _scan_top_apps_worker(self):
        app_memory = {}
        cpu_by_app = {}
        all_live_pids = set()
        cores = max(1, self._cpu_cores)

        for proc in psutil.process_iter(["pid", "name", "memory_info", "cpu_percent"]):
            try:
                pid = proc.info["pid"]
                name = proc.info["name"]
                mem_info = proc.info["memory_info"]

                if not name or pid <= 4 or pid == CURRENT_PID:
                    continue

                lower_name = name.lower()
                raw_cpu = proc.info["cpu_percent"]
                cpu_pct = min(100.0, max(0.0, (raw_cpu or 0.0) / cores))
                rss = mem_info.rss if mem_info else 0

                if lower_name not in IGNORED_CULPRIT_NAMES:
                    if lower_name in cpu_by_app:
                        cpu_by_app[lower_name]["cpu"] = min(100.0, cpu_by_app[lower_name]["cpu"] + cpu_pct)
                        cpu_by_app[lower_name]["rss"] += rss
                    else:
                        cpu_by_app[lower_name] = {
                            "key": lower_name,
                            "display_name": name,
                            "cpu": cpu_pct,
                            "rss": rss,
                            "protected": lower_name in PROTECTED_PROCESSES,
                        }

                if not mem_info or lower_name in PROTECTED_PROCESSES:
                    continue

                all_live_pids.add(pid)
                proc_entry = {"pid": pid, "rss": rss, "cpu": cpu_pct}

                if lower_name in app_memory:
                    app_memory[lower_name]["bytes"] += rss
                    app_memory[lower_name]["count"] += 1
                    app_memory[lower_name]["processes"].append(proc_entry)
                else:
                    app_memory[lower_name] = {
                        "key": lower_name,
                        "display_name": name,
                        "bytes": rss,
                        "count": 1,
                        "processes": [proc_entry],
                    }
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                continue

        top_apps = sorted(
            app_memory.values(),
            key=lambda item: item["bytes"],
            reverse=True,
        )[:TOP_APPS_COUNT]

        for app_item in top_apps:
            app_item["processes"].sort(key=lambda p: p["rss"], reverse=True)

        top_culprit = None
        if cpu_by_app:
            top_culprit = max(cpu_by_app.values(), key=lambda x: (x["cpu"], x["rss"]))

        if not self._is_quitting:
            self.after(0, self._render_top_apps, top_apps, all_live_pids, top_culprit)

    def _render_top_apps(self, top_apps, all_live_pids, top_culprit):
        self._is_refreshing_apps = False
        if self._in_tray or self._is_quitting or self._game_mode_active:
            return

        if self.lag_recorder_enabled:
            self._record_lag_sample(top_culprit)

        self.selected_pids.intersection_update(all_live_pids)

        frozen_changed = False
        for frozen_key in list(self.frozen_apps.keys()):
            self.frozen_apps[frozen_key].intersection_update(all_live_pids)
            if not self.frozen_apps[frozen_key]:
                self.frozen_apps.pop(frozen_key, None)
                frozen_changed = True
        if frozen_changed:
            self._update_freeze_ui_summary()

        new_order = [app["key"] for app in top_apps]
        visible_keys = set(new_order)

        if self.selected_main_app and self.selected_main_app not in visible_keys:
            self.selected_main_app = ""

        for old_key in list(self.app_cards.keys()):
            if old_key not in visible_keys and old_key not in self._fading_apps:
                self.app_cards.pop(old_key).destroy()
                self.expanded_apps.discard(old_key)

        for app_data in top_apps:
            key = app_data["key"]
            if key in self._fading_apps:
                continue

            if key in self.app_cards:
                self.app_cards[key].update_data(app_data)
            else:
                card = AppGroupCard(self.apps_list_frame, self, app_data)
                self.app_cards[key] = card
                if key == self.selected_main_app:
                    card.set_selected(True)
                if key in self.expanded_apps:
                    card.expand(animate=False)

        if new_order != self.app_cards_order:
            for key in new_order:
                if key in self.app_cards:
                    self.app_cards[key].container.pack_forget()
            for key in new_order:
                if key in self.app_cards:
                    self.app_cards[key].container.pack(fill="x", padx=4, pady=3)
            self.app_cards_order = new_order

        self.update_close_button()

    def close_app_by_key(self, app_key, display_name=None):
        if self._is_closing_app or not app_key:
            return
        if app_key in PROTECTED_PROCESSES:
            self._set_status(f"Blocked: '{display_name or app_key}' is protected.", "#EF4444")
            return

        label = display_name or app_key
        self._is_closing_app = True
        self.close_app_button.configure(state="disabled", text="CLOSING...")
        self._set_status(f"Closing {label}...", "#38BDF8")

        threading.Thread(
            target=self._terminate_targets_worker,
            args=("app", [], app_key, label),
            daemon=True,
        ).start()

    def close_selected_targets(self):
        if self._is_closing_app:
            return

        if self.selected_pids:
            target_pids = list(self.selected_pids)
            mode = "pids"
            label = f"{len(target_pids)} selected process(es)"
        elif self.selected_main_app and self.selected_main_app in self.app_cards:
            card = self.app_cards[self.selected_main_app]
            if card.key in PROTECTED_PROCESSES:
                self._set_status(f"Blocked: '{card.display_name}' is protected.", "#EF4444")
                return
            target_pids = [p["pid"] for p in card.processes]
            mode = "app"
            label = card.display_name
        else:
            self._set_status(
                "Click an app or check sub-process boxes before clicking Close.",
                "#F97316",
            )
            return

        self._is_closing_app = True
        self.close_app_button.configure(state="disabled", text="CLOSING...")
        self._set_status(f"Closing {label}...", "#38BDF8")

        threading.Thread(
            target=self._terminate_targets_worker,
            args=(mode, target_pids, self.selected_main_app, label),
            daemon=True,
        ).start()

    def _terminate_targets_worker(self, mode, target_pids, main_app_key, label):
        matched_procs = []
        access_denied_count = 0

        if mode == "app" and main_app_key:
            for proc in psutil.process_iter(["pid", "name"]):
                try:
                    pid = proc.info["pid"]
                    name = proc.info["name"]
                    if not name or pid <= 4 or pid == CURRENT_PID:
                        continue
                    lower = name.lower()
                    if lower == main_app_key and lower not in PROTECTED_PROCESSES:
                        proc.terminate()
                        matched_procs.append(proc)
                except psutil.AccessDenied:
                    access_denied_count += 1
                except (psutil.NoSuchProcess, psutil.ZombieProcess):
                    continue
        else:
            for pid in target_pids:
                if pid <= 4 or pid == CURRENT_PID:
                    continue
                try:
                    proc = psutil.Process(pid)
                    name = (proc.name() or "").lower()
                    if name in PROTECTED_PROCESSES:
                        continue
                    proc.terminate()
                    matched_procs.append(proc)
                except psutil.AccessDenied:
                    access_denied_count += 1
                except (psutil.NoSuchProcess, psutil.ZombieProcess):
                    continue

        gone, alive = psutil.wait_procs(matched_procs, timeout=2.0)

        for proc in alive:
            try:
                proc.kill()
                gone.append(proc)
            except psutil.AccessDenied:
                access_denied_count += 1
            except (psutil.NoSuchProcess, psutil.ZombieProcess):
                pass

        closed_pids = [p.pid for p in gone]
        if not self._is_quitting:
            self.after(
                0,
                self._finish_close_targets,
                mode,
                main_app_key,
                label,
                closed_pids,
                access_denied_count,
            )

    def _finish_close_targets(self, mode, main_app_key, label, closed_pids, denied_count):
        self._is_closing_app = False
        if self._is_quitting:
            return

        closed_set = set(closed_pids)
        self.selected_pids.difference_update(closed_set)

        for fkey in list(self.frozen_apps.keys()):
            self.frozen_apps[fkey].difference_update(closed_set)
            if not self.frozen_apps[fkey]:
                self.frozen_apps.pop(fkey, None)
        self._update_freeze_ui_summary()

        self.close_app_button.configure(state="normal")

        closed_count = len(closed_set)
        if closed_count > 0 and denied_count == 0:
            self._set_status(f"Closed {label} ({closed_count} process(es) stopped).", "#22C55E")
        elif closed_count > 0 and denied_count > 0:
            self._set_status(
                f"Partially closed {label} ({closed_count} stopped, {denied_count} need Admin rights).",
                "#F97316",
            )
        elif denied_count > 0:
            self._set_status(
                f"Access denied for {label}. Run as Administrator to close it.",
                "#EF4444",
            )
        else:
            self._set_status(f"{label} is already closed.", TEXT_MUTED)

        if mode == "app" and closed_count > 0 and main_app_key in self.app_cards and denied_count == 0:
            if self.selected_main_app == main_app_key:
                self.selected_main_app = ""
            self.expanded_apps.discard(main_app_key)
            self.frozen_apps.pop(main_app_key, None)
            self._update_freeze_ui_summary()
            self.update_close_button()
            self._animate_fade_app_card(main_app_key)
        elif closed_set:
            self.update_close_button()
            self._animate_fade_sub_rows(closed_set)
        else:
            self.update_close_button()
            self.refresh_top_apps()

    def _animate_fade_sub_rows(self, closed_pids):
        targets = []
        for card in self.app_cards.values():
            if not card.is_expanded:
                continue
            for pid in closed_pids:
                row_info = card.get_sub_row(pid)
                if row_info and row_info["wrapper"].winfo_exists():
                    start_h = max(row_info["wrapper"].winfo_height(), 28)
                    row_info["wrapper"].pack_propagate(False)
                    row_info["wrapper"].configure(height=start_h)
                    targets.append((card, pid, row_info, start_h))
                    self._fading_pids.add(pid)

        if not targets:
            self.refresh_top_apps()
            return

        def step_anim(step):
            if self._is_quitting:
                return
            t = step / float(FADE_ANIM_STEPS)
            bg_col = blend_hex(BG_SUBPANEL, "#7F1D1D", t)
            txt_col = blend_hex(BG_SUBPANEL, "#FCA5A5", t)

            for _card, _pid, row_info, start_h in targets:
                if row_info["wrapper"].winfo_exists():
                    new_h = max(1, int(start_h * (1.0 - t)))
                    row_info["wrapper"].configure(height=new_h)
                    row_info["frame"].configure(fg_color=bg_col)
                    row_info["cb"].configure(text_color=txt_col)
                    row_info["ram_label"].configure(text_color=txt_col)
                    row_info["cpu_label"].configure(text_color=txt_col)

            if step < FADE_ANIM_STEPS:
                self.after(FADE_ANIM_STEP_MS, step_anim, step + 1)
            else:
                for card, pid, _row_info, _start_h in targets:
                    self._fading_pids.discard(pid)
                    card.remove_sub_row(pid)
                self.refresh_top_apps()

        step_anim(1)

    def _animate_fade_app_card(self, app_key):
        card = self.app_cards.get(app_key)
        if not card or not card.container.winfo_exists():
            self.refresh_top_apps()
            return

        self._fading_apps.add(app_key)

        def run_card_fade():
            if self._is_quitting or not card.container.winfo_exists():
                self._fading_apps.discard(app_key)
                return

            def step_anim(step):
                if self._is_quitting:
                    return
                t = step / float(FADE_ANIM_STEPS)
                if card.container.winfo_exists():
                    bg_col = blend_hex(BG_INNER, "#7F1D1D", t)
                    txt_col = blend_hex(BG_INNER, "#FCA5A5", t)
                    card.container.configure(fg_color=bg_col, border_color=bg_col)
                    card.name_label.configure(text_color=txt_col)
                    card.count_label.configure(text_color=txt_col)
                    card.mem_label.configure(text_color=txt_col, fg_color=bg_col)

                if step < FADE_ANIM_STEPS:
                    self.after(FADE_ANIM_STEP_MS, step_anim, step + 1)
                else:
                    self._fading_apps.discard(app_key)
                    popped = self.app_cards.pop(app_key, None)
                    if popped:
                        popped.destroy()
                    if app_key in self.app_cards_order:
                        self.app_cards_order.remove(app_key)
                    self.refresh_top_apps()

            step_anim(1)

        if card.is_expanded:
            card.collapse(animate=True, on_done=run_card_fade)
        else:
            run_card_fade()

    # ------------------------------------------------------------------
    # Automatic Smart Game Mode (Zero-Interruption Full-Screen Detection)
    # ------------------------------------------------------------------
    def _schedule_game_mode_check(self):
        if self._is_quitting:
            return
        if self._game_mode_after_id is not None:
            self.after_cancel(self._game_mode_after_id)
        self._game_mode_after_id = self.after(GAME_MODE_POLL_MS, self._poll_game_mode)

    def _poll_game_mode(self):
        self._game_mode_after_id = None
        if self._is_quitting:
            return

        fullscreen_now = is_fullscreen_app_running()

        if fullscreen_now:
            if self._post_game_clean_after_id is not None:
                self.after_cancel(self._post_game_clean_after_id)
                self._post_game_clean_after_id = None

            if not self._game_mode_active:
                self._enter_game_mode()
        elif self._game_mode_active:
            self._exit_game_mode()

        self._schedule_game_mode_check()

    def _enter_game_mode(self):
        self._game_mode_active = True

        for attr in (
            "_stats_after_id",
            "_apps_after_id",
            "_anim_after_id",
            "_boost_anim_after_id",
            "_tray_ram_after_id",
            "_tray_lag_after_id",
            "_post_game_clean_after_id",
        ):
            after_id = getattr(self, attr)
            if after_id is not None:
                self.after_cancel(after_id)
                setattr(self, attr, None)

        self.game_mode_pill.configure(
            text="  GAME MODE: ACTIVE  ",
            text_color="#C4B5FD",
            fg_color="#3B1D6A",
        )
        self.telemetry_status_label.configure(text="● PAUSED (GAME MODE)", text_color="#A78BFA")
        self._set_status(
            "Smart Game Mode active — polling, auto-clean & notifications paused.",
            "#A78BFA",
        )

        if self._tray_icon is not None:
            try:
                self._tray_icon.title = "PC Optimizer (Game Mode Active)"
            except Exception:
                pass

        # Immediately update Edge Status Glow to soft purple pulse if enabled
        if self.edge_glow_enabled and self._edge_glow_overlay is not None:
            self._edge_glow_overlay.update_state(
                self._target_cpu, self._target_ram, True
            )

        trim_own_memory()

    def _exit_game_mode(self):
        self._game_mode_active = False

        self.game_mode_pill.configure(
            text="  SMART GAME MODE: STANDBY  ",
            text_color="#A78BFA",
            fg_color="#1E1B3A",
        )

        if self._tray_icon is not None:
            try:
                self._tray_icon.title = "PC Optimizer (Monitoring RAM)"
            except Exception:
                pass

        if self.edge_glow_enabled and self._edge_glow_overlay is not None:
            self._edge_glow_overlay.update_state(
                self._target_cpu, self._target_ram, False
            )

        if self._in_tray:
            self._schedule_tray_ram_check()
            if self.lag_recorder_enabled:
                self._schedule_tray_lag_sample()
        else:
            self.telemetry_status_label.configure(text="● ACTIVE", text_color="#22C55E")
            psutil.cpu_percent(interval=None)
            self.update_system_stats()
            self.refresh_top_apps()

        self._set_status(
            "Exited Game Mode — automatic post-game temp cleanup in 10 seconds...",
            "#38BDF8",
        )

        if self._post_game_clean_after_id is not None:
            self.after_cancel(self._post_game_clean_after_id)
        self._post_game_clean_after_id = self.after(
            POST_GAME_CLEAN_DELAY_MS, self._trigger_post_game_cleanup
        )

    def _trigger_post_game_cleanup(self):
        self._post_game_clean_after_id = None
        if self._is_quitting or self._game_mode_active or self._is_cleaning:
            return

        self._is_cleaning = True
        self._last_auto_clean_time = time.monotonic()
        self._set_status("Running post-game temporary file cleanup...", "#38BDF8")

        threading.Thread(
            target=self._run_post_game_cleanup_worker,
            daemon=True,
        ).start()

    def _run_post_game_cleanup_worker(self):
        deleted_items, skipped_items, freed_bytes, error_msg = self._perform_safe_temp_cleanup()
        trim_own_memory()

        if not self._is_quitting:
            self.after(
                0,
                self._finish_post_game_cleanup,
                deleted_items,
                skipped_items,
                freed_bytes,
                error_msg,
            )

    def _finish_post_game_cleanup(self, deleted_items, skipped_items, freed_bytes, error_msg):
        self._is_cleaning = False
        if self._is_quitting or error_msg:
            return

        freed_str = format_bytes(freed_bytes)
        msg = f"Post-game cleanup freed {freed_str} ({deleted_items} temporary items removed)."

        self.boost_summary_label.configure(
            text=f"Post-game boost: Freed {freed_str} ({deleted_items} items removed)",
            text_color="#22C55E",
        )
        self._set_status(msg, "#22C55E")

        self._send_notification(
            title="PC Optimizer — Post-Game Cleanup",
            message=msg,
        )

    # ------------------------------------------------------------------
    # Hero Button Hover Glow & Sweeping Progress Canvas Helpers
    # ------------------------------------------------------------------
    def _on_hero_hover_enter(self, _event=None):
        if not self._is_cleaning:
            self.hero_card.configure(border_color="#38BDF8")
            self.clean_button.configure(border_color="#93C5FD", fg_color="#1D4ED8")

    def _on_hero_hover_leave(self, _event=None):
        if not self._is_cleaning:
            self.hero_card.configure(border_color=BORDER_SUBTLE)
            self.clean_button.configure(border_color="#3B82F6", fg_color="#2563EB")

    def _on_sweep_resize(self, event):
        self.sweep_canvas.coords(self._sweep_track, 0, 1, max(1, event.width), 7)

    # ------------------------------------------------------------------
    # Startup Programs (Registry) & Installed Apps
    # ------------------------------------------------------------------
    def open_installed_apps(self):
        try:
            os.startfile("ms-settings:appsfeatures")
            self._set_status("Opened Windows Installed Apps settings.", "#22C55E")
        except OSError as exc:
            self._set_status(f"Could not open Windows Settings: {exc}", "#EF4444")

    def _read_startup_approved_states(self):
        states = {}
        try:
            with winreg.OpenKey(
                winreg.HKEY_CURRENT_USER, HKCU_STARTUP_APPROVED_PATH, 0, winreg.KEY_READ
            ) as key:
                index = 0
                while True:
                    try:
                        name, raw_data, reg_type = winreg.EnumValue(key, index)
                        index += 1
                        if reg_type == winreg.REG_BINARY and isinstance(raw_data, (bytes, bytearray)) and len(raw_data) > 0:
                            states[name.lower()] = (raw_data[0] % 2 == 0)
                    except OSError:
                        break
        except OSError:
            pass
        return states

    def _read_user_startup_entries(self):
        approved_states = self._read_startup_approved_states()
        entries = []

        try:
            with winreg.OpenKey(
                winreg.HKEY_CURRENT_USER, HKCU_RUN_PATH, 0, winreg.KEY_READ
            ) as key:
                index = 0
                while True:
                    try:
                        name, command, _ = winreg.EnumValue(key, index)
                        index += 1
                        if not name:
                            continue
                        enabled = approved_states.get(name.lower(), True)
                        entries.append((name, str(command), enabled))
                    except OSError:
                        break
        except OSError:
            pass

        entries.sort(key=lambda item: item[0].lower())
        return entries

    def refresh_startup_apps(self):
        for widget in self.startup_widgets:
            widget.destroy()
        self.startup_widgets.clear()

        entries = self._read_user_startup_entries()
        if not entries:
            empty_label = ctk.CTkLabel(
                self.startup_list_frame,
                text="No user startup programs found in HKCU\\...\\Run.",
                font=ctk.CTkFont(size=13),
                text_color=TEXT_MUTED,
            )
            empty_label.pack(pady=24)
            self.startup_widgets.append(empty_label)
            return

        for name, command, is_enabled in entries:
            row = ctk.CTkFrame(self.startup_list_frame, fg_color=BG_ROW, corner_radius=8)
            row.pack(fill="x", padx=4, pady=4)

            info_frame = ctk.CTkFrame(row, fg_color="transparent")
            info_frame.pack(side="left", fill="x", expand=True, padx=(12, 8), pady=8)

            ctk.CTkLabel(
                info_frame,
                text=name,
                font=ctk.CTkFont(size=13, weight="bold"),
                text_color=TEXT_PRIMARY,
                anchor="w",
            ).pack(fill="x")

            short_cmd = command if len(command) <= 84 else command[:81] + "..."
            ctk.CTkLabel(
                info_frame,
                text=short_cmd,
                font=ctk.CTkFont(size=11),
                text_color=TEXT_MUTED,
                anchor="w",
            ).pack(fill="x")

            switch_var = ctk.BooleanVar(value=is_enabled)
            switch = ctk.CTkSwitch(
                row,
                text="On" if is_enabled else "Off",
                variable=switch_var,
                onvalue=True,
                offvalue=False,
                width=70,
                font=ctk.CTkFont(size=12, weight="bold"),
                text_color="#22C55E" if is_enabled else TEXT_MUTED,
                progress_color="#22C55E",
                fg_color="#334155",
            )
            switch.configure(
                command=lambda n=name, v=switch_var, s=switch: self._toggle_startup_app(n, v, s)
            )
            switch.pack(side="right", padx=14)

            self.startup_widgets.append(row)

    def _toggle_startup_app(self, app_name, switch_var, switch_widget):
        enable = bool(switch_var.get())
        try:
            with winreg.CreateKeyEx(
                winreg.HKEY_CURRENT_USER,
                HKCU_STARTUP_APPROVED_PATH,
                0,
                winreg.KEY_SET_VALUE,
            ) as key:
                if enable:
                    binary_flag = bytes([0x02] + [0x00] * 11)
                else:
                    filetime = int((time.time() + 11644473600) * 10_000_000)
                    binary_flag = bytes([0x03, 0x00, 0x00, 0x00]) + filetime.to_bytes(8, "little")

                winreg.SetValueEx(key, app_name, 0, winreg.REG_BINARY, binary_flag)

            switch_widget.configure(
                text="On" if enable else "Off",
                text_color="#22C55E" if enable else TEXT_MUTED,
            )
            state_text = "Enabled" if enable else "Disabled"
            self._set_status(f"{state_text} startup item: {app_name}", "#22C55E")
        except OSError as exc:
            switch_var.set(not enable)
            self._set_status(f"Could not update '{app_name}': {exc}", "#EF4444")

    # ------------------------------------------------------------------
    # System Tray Mode & 15-Second RAM Auto-Cleaner
    # ------------------------------------------------------------------
    def _start_tray_icon(self):
        if self._tray_icon is not None:
            return

        menu = pystray.Menu(
            pystray.MenuItem(
                "Open PC Optimizer",
                lambda icon, item: self.after(0, self.restore_from_tray),
                default=True,
            ),
            pystray.MenuItem(
                "Why Did My PC Just Lag?",
                lambda icon, item: self.after(0, self._restore_and_open_forensics),
            ),
            pystray.MenuItem(
                "Smart Boost & Clean Now",
                lambda icon, item: self.after(0, self.start_temp_cleanup),
            ),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem(
                "Quit PC Optimizer",
                lambda icon, item: self.after(0, self.quit_app),
            ),
        )

        tooltip = (
            "PC Optimizer (Game Mode Active)"
            if self._game_mode_active
            else "PC Optimizer (Monitoring RAM)"
        )
        self._tray_icon = pystray.Icon(
            "PCOptimizer",
            self._tray_image,
            tooltip,
            menu,
        )
        self._tray_icon.run_detached()

    def _restore_and_open_forensics(self):
        self.restore_from_tray()
        self.after(60, self.open_lag_forensics)

    def _stop_tray_icon(self):
        if self._tray_icon is not None:
            try:
                self._tray_icon.stop()
            except Exception:
                pass
            self._tray_icon = None

    def hide_to_tray(self):
        if self._in_tray or self._is_quitting:
            return

        if self._forensics_modal is not None and self._forensics_modal.winfo_exists():
            try:
                self._forensics_modal.destroy()
            except Exception:
                pass
            self._forensics_modal = None

        self._in_tray = True

        for attr in ("_stats_after_id", "_apps_after_id", "_anim_after_id", "_boost_anim_after_id"):
            after_id = getattr(self, attr)
            if after_id is not None:
                self.after_cancel(after_id)
                setattr(self, attr, None)

        self.withdraw()
        self._start_tray_icon()
        trim_own_memory()

        if not self._game_mode_active:
            self._schedule_tray_ram_check()
            if self.lag_recorder_enabled:
                self._schedule_tray_lag_sample()

        if not self._tray_hint_shown:
            self._tray_hint_shown = True
            self._send_notification(
                title="PC Optimizer Running in Tray",
                message="Minimized to save resources. Smart Game Mode & 85% RAM auto-clean active.",
            )

    def restore_from_tray(self):
        if self._is_quitting:
            return
        if not self._in_tray:
            self.lift()
            self.focus_force()
            return

        self._in_tray = False

        for attr in ("_tray_ram_after_id", "_tray_lag_after_id"):
            after_id = getattr(self, attr)
            if after_id is not None:
                self.after_cancel(after_id)
                setattr(self, attr, None)

        self._stop_tray_icon()
        self.deiconify()
        self.lift()
        self.focus_force()
        self._update_lag_recorder_badge()

        if not self._game_mode_active:
            self.telemetry_status_label.configure(text="● ACTIVE", text_color="#22C55E")
            psutil.cpu_percent(interval=None)
            self.update_system_stats()
            self.refresh_top_apps()

        if self._is_cleaning and self._boost_anim_after_id is None and not self._game_mode_active:
            self._animate_boost_progress()

    def _schedule_tray_ram_check(self):
        if not self._in_tray or self._is_quitting or self._game_mode_active:
            return
        if self._tray_ram_after_id is not None:
            self.after_cancel(self._tray_ram_after_id)
        self._tray_ram_after_id = self.after(TRAY_RAM_CHECK_MS, self._check_tray_ram)

    def _check_tray_ram(self):
        self._tray_ram_after_id = None
        if not self._in_tray or self._is_quitting or self._game_mode_active:
            return

        ram = psutil.virtual_memory()
        ram_percent = ram.percent

        if ram_percent < 80.0:
            self._last_auto_clean_time = 0.0

        now = time.monotonic()
        cooldown_passed = (now - self._last_auto_clean_time) >= AUTO_CLEAN_COOLDOWN_SEC

        if ram_percent > AUTO_CLEAN_THRESHOLD and not self._is_cleaning and cooldown_passed:
            self._is_cleaning = True
            self._last_auto_clean_time = now
            threading.Thread(
                target=self._run_auto_tray_cleanup_worker,
                args=(ram_percent, ram.used),
                daemon=True,
            ).start()

        self._schedule_tray_ram_check()

    def _run_auto_tray_cleanup_worker(self, trigger_ram_percent, ram_used_before):
        deleted_items, skipped_items, freed_temp_bytes, error_msg = self._perform_safe_temp_cleanup()
        trim_own_memory()

        ram_after = psutil.virtual_memory()
        ram_freed_bytes = max(0, ram_used_before - ram_after.used)

        if not self._is_quitting:
            self.after(
                0,
                self._finish_auto_tray_cleanup,
                trigger_ram_percent,
                ram_after.percent,
                ram_freed_bytes,
                freed_temp_bytes,
                deleted_items,
                error_msg,
            )

    def _finish_auto_tray_cleanup(
        self,
        trigger_ram_percent,
        ram_after_percent,
        ram_freed_bytes,
        freed_temp_bytes,
        deleted_items,
        error_msg,
    ):
        self._is_cleaning = False
        if error_msg or self._is_quitting:
            return

        temp_str = format_bytes(freed_temp_bytes)
        if ram_freed_bytes > 0:
            ram_freed_str = format_bytes(ram_freed_bytes)
            msg = (
                f"RAM reached {trigger_ram_percent:.1f}%. Auto-cleaned {temp_str} "
                f"({deleted_items} temp items) and freed {ram_freed_str} of RAM "
                f"(now {ram_after_percent:.1f}%)."
            )
        else:
            msg = (
                f"RAM reached {trigger_ram_percent:.1f}%. Auto-cleaned {temp_str} "
                f"({deleted_items} temp items). Current RAM: {ram_after_percent:.1f}%."
            )

        self._set_status(msg, "#22C55E")
        self.boost_summary_label.configure(
            text=f"Auto-boosted: {temp_str} temp cleaned • RAM now {ram_after_percent:.1f}%",
            text_color="#22C55E",
        )
        self._send_notification(
            title="PC Optimizer — Auto-Cleanup Complete",
            message=msg,
        )

    # ------------------------------------------------------------------
    # Live CPU & RAM Monitoring with Smooth Circular Ring Gauges
    # ------------------------------------------------------------------
    def _set_status(self, message, color=TEXT_MUTED):
        self.status_label.configure(text=message, text_color=color)

    def update_system_stats(self):
        if self._in_tray or self._is_quitting or self._game_mode_active:
            return

        self._target_cpu = psutil.cpu_percent(interval=None)
        ram = psutil.virtual_memory()
        self._target_ram = ram.percent

        used_gb = ram.used / (1024 ** 3)
        total_gb = ram.total / (1024 ** 3)
        self._ram_detail_text = f"{used_gb:.1f} / {total_gb:.1f} GB"

        if self._anim_after_id is None:
            self._animate_gauges()

        self._stats_after_id = self.after(STATS_REFRESH_MS, self.update_system_stats)

    def _animate_gauges(self):
        if self._in_tray or self._is_quitting or self._game_mode_active:
            self._anim_after_id = None
            return

        cpu_diff = self._target_cpu - self._displayed_cpu
        ram_diff = self._target_ram - self._displayed_ram

        if abs(cpu_diff) < 0.2:
            self._displayed_cpu = self._target_cpu
        else:
            self._displayed_cpu += cpu_diff * ANIM_SMOOTHING

        if abs(ram_diff) < 0.2:
            self._displayed_ram = self._target_ram
        else:
            self._displayed_ram += ram_diff * ANIM_SMOOTHING

        self.cpu_gauge.set_value(self._displayed_cpu)
        self.ram_gauge.set_value(self._displayed_ram, self._ram_detail_text)

        if self._displayed_cpu != self._target_cpu or self._displayed_ram != self._target_ram:
            self._anim_after_id = self.after(ANIM_INTERVAL_MS, self._animate_gauges)
        else:
            self._anim_after_id = None

    # ------------------------------------------------------------------
    # Smart Boost & Safe Temp Cleaner + Sweeping/Pulsing Hero Animation
    # ------------------------------------------------------------------
    @staticmethod
    def _perform_safe_temp_cleanup():
        temp_dir = os.path.abspath(tempfile.gettempdir())
        deleted_items = 0
        skipped_items = 0
        freed_bytes = 0

        if not os.path.isdir(temp_dir) or "temp" not in temp_dir.lower():
            return 0, 0, 0, "Safety check failed: invalid Temp path."

        for root, dirs, files in os.walk(temp_dir, topdown=False, followlinks=False):
            for filename in files:
                file_path = os.path.join(root, filename)
                try:
                    file_size = os.path.getsize(file_path) if not os.path.islink(file_path) else 0
                    os.unlink(file_path)
                    deleted_items += 1
                    freed_bytes += file_size
                except (PermissionError, OSError):
                    skipped_items += 1

            for dirname in dirs:
                dir_path = os.path.join(root, dirname)
                try:
                    if os.path.islink(dir_path):
                        os.unlink(dir_path)
                    else:
                        os.rmdir(dir_path)
                    deleted_items += 1
                except (PermissionError, OSError):
                    skipped_items += 1

        return deleted_items, skipped_items, freed_bytes, None

    def start_temp_cleanup(self):
        if self._is_cleaning:
            return

        if self._post_game_clean_after_id is not None:
            self.after_cancel(self._post_game_clean_after_id)
            self._post_game_clean_after_id = None

        self._is_cleaning = True
        self._boost_phase = 0.0
        self._boost_spinner_idx = 0

        self.clean_button.configure(
            state="disabled",
            text="⚡  BOOSTING & CLEANING...",
            fg_color="#1E3A8A",
            border_color="#38BDF8",
        )
        self.boost_badge.configure(text="  RUNNING  ", text_color="#38BDF8", fg_color="#12263A")

        if not self._in_tray and not self._game_mode_active:
            self.sweep_canvas.itemconfigure(self._sweep_glow, state="normal")
            self.sweep_canvas.itemconfigure(self._sweep_beam, state="normal")
            self._animate_boost_progress()

        threading.Thread(target=self._run_temp_cleanup_worker, daemon=True).start()

    def _animate_boost_progress(self):
        if not self._is_cleaning or self._in_tray or self._is_quitting or self._game_mode_active:
            self._boost_anim_after_id = None
            return

        width = max(120, self.sweep_canvas.winfo_width())
        self._boost_phase += 0.14
        pos = (1.0 - math.cos(self._boost_phase)) * 0.5

        beam_w = max(54.0, width * 0.24)
        glow_w = beam_w * 1.45
        center = (beam_w * 0.5) + pos * max(1.0, width - beam_w)

        self.sweep_canvas.coords(self._sweep_glow, center - glow_w / 2, 0, center + glow_w / 2, 8)
        self.sweep_canvas.coords(self._sweep_beam, center - beam_w / 2, 1, center + beam_w / 2, 7)

        pulse = (1.0 + math.sin(self._boost_phase * 1.6)) * 0.5
        border_pulse = blend_hex("#38BDF8", "#1D4ED8", pulse)
        self.hero_card.configure(border_color=border_pulse)
        self.clean_button.configure(border_color=border_pulse)

        self._boost_spinner_idx += 1
        if self._boost_spinner_idx % 4 == 0:
            frame = SPINNER_FRAMES[(self._boost_spinner_idx // 4) % len(SPINNER_FRAMES)]
            dots = "." * (((self._boost_spinner_idx // 8) % 3) + 1)
            msg = f"{frame} Sweeping Windows Temp files & optimizing{dots}"
            self.boost_summary_label.configure(text=msg, text_color="#38BDF8")
            self._set_status(msg, "#38BDF8")

        self._boost_anim_after_id = self.after(BOOST_ANIM_INTERVAL_MS, self._animate_boost_progress)

    def _run_temp_cleanup_worker(self):
        ram_before = psutil.virtual_memory().used
        deleted_items, skipped_items, freed_bytes, error_msg = self._perform_safe_temp_cleanup()
        trim_own_memory()
        ram_freed = max(0, ram_before - psutil.virtual_memory().used)

        if not self._is_quitting:
            self.after(0, self._finish_temp_cleanup, deleted_items, skipped_items, freed_bytes, ram_freed, error_msg)

    def _finish_temp_cleanup(self, deleted_items, skipped_items, freed_bytes, ram_freed, error_msg):
        self._is_cleaning = False
        if self._is_quitting:
            return

        if self._boost_anim_after_id is not None:
            self.after_cancel(self._boost_anim_after_id)
            self._boost_anim_after_id = None

        self.sweep_canvas.itemconfigure(self._sweep_glow, state="hidden")
        self.sweep_canvas.itemconfigure(self._sweep_beam, state="hidden")
        self.hero_card.configure(border_color=BORDER_SUBTLE)

        self.clean_button.configure(
            state="normal",
            text="⚡  SMART BOOST & CLEAN",
            fg_color="#2563EB",
            border_color="#3B82F6",
        )
        self.boost_badge.configure(text="  READY  ", text_color="#22C55E", fg_color="#122620")

        if error_msg:
            self.boost_summary_label.configure(text=error_msg, text_color="#EF4444")
            self._set_status(error_msg, "#EF4444")
            return

        freed_str = format_bytes(freed_bytes)
        ram_note = f" • {format_bytes(ram_freed)} RAM freed" if ram_freed > 0 else ""
        summary = f"Boost complete: freed {freed_str} ({deleted_items} items removed, {skipped_items} in-use skipped){ram_note}."

        self.boost_summary_label.configure(
            text=f"Last boost: Freed {freed_str} ({deleted_items} items removed)",
            text_color="#22C55E",
        )
        self._set_status(summary, "#22C55E")

        self._send_notification(
            title="PC Optimizer — Smart Boost Complete",
            message=f"Freed {freed_str} ({deleted_items} temporary items removed){ram_note}.",
        )

    def _send_notification(self, title, message, force=False):
        if self._game_mode_active and not force:
            return
        try:
            toast = Notification(
                app_id="PC Optimizer",
                title=title,
                msg=message,
                duration="short",
            )
            toast.set_audio(audio.Default, loop=False)
            toast.show()
        except Exception:
            pass

    def quit_app(self):
        self._is_quitting = True
        self._in_tray = False
        self._game_mode_active = False

        # Cleanly unhook global panic hotkey & destroy edge glow overlay
        self._unhook_panic_hotkey()
        if self._edge_glow_overlay is not None:
            self._edge_glow_overlay.destroy()
            self._edge_glow_overlay = None

        if self._forensics_modal is not None and self._forensics_modal.winfo_exists():
            try:
                self._forensics_modal.destroy()
            except Exception:
                pass
            self._forensics_modal = None

        # Auto-thaw any frozen apps before quitting so nothing stays suspended
        if self.frozen_apps:
            self._thaw_all_sync({k: set(v) for k, v in self.frozen_apps.items()})
            self.frozen_apps.clear()

        for attr in (
            "_stats_after_id",
            "_apps_after_id",
            "_anim_after_id",
            "_boost_anim_after_id",
            "_tray_ram_after_id",
            "_tray_lag_after_id",
            "_game_mode_after_id",
            "_post_game_clean_after_id",
            "_edge_glow_poll_after_id",
            "_idle_check_after_id",
            "_panic_banner_after_id",
        ):
            after_id = getattr(self, attr)
            if after_id is not None:
                self.after_cancel(after_id)
                setattr(self, attr, None)

        for card in list(self.app_cards.values()):
            card.destroy()
        self.app_cards.clear()

        self._stop_tray_icon()
        self.destroy()


if __name__ == "__main__":
    try:
        app = PCOptimizerApp()
        app.mainloop()
    except Exception:
        traceback.print_exc()
        input("\nAn error occurred. Copy the error above and press Enter to close...")