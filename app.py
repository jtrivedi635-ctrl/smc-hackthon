"""
╔══════════════════════════════════════════════════════════════════╗
║   HYDRONAUTS - Smart Water Pressure Management System           ║
║   Solapur Municipal Corporation                                  ║
║   Desktop Dashboard Application                                  ║
╚══════════════════════════════════════════════════════════════════╝

Requirements:
    pip install matplotlib numpy

Run:
    python hydronauts_dashboard.py
"""

import tkinter as tk
from tkinter import ttk, messagebox, font as tkfont
import threading
import time
import random
import math
from datetime import datetime, timedelta
from collections import deque
import warnings

try:
    import matplotlib
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        matplotlib.use("TkAgg")
    from matplotlib.figure import Figure
    import matplotlib.gridspec as gridspec
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    HAS_MPL = True
except Exception:
    HAS_MPL = False

# ─────────────────────────────────────────────────────────────────
#  COLOUR PALETTE  (deep navy + electric teal + amber alerts)
# ─────────────────────────────────────────────────────────────────
C = {
    "bg":        "#0A1628",   # deep navy
    "panel":     "#0E1F3D",   # card bg
    "surface":   "#132644",   # elevated surface
    "border":    "#1E3A5F",   # subtle border
    "teal":      "#00D4FF",   # primary accent
    "teal2":     "#00A8CC",   # secondary teal
    "green":     "#00E676",   # safe / OK
    "amber":     "#FFB300",   # warning
    "red":       "#FF3D3D",   # alert / danger
    "text":      "#E8F4F8",   # primary text
    "muted":     "#6B8FAD",   # secondary text
    "white":     "#FFFFFF",
    "chart_bg":  "#0B1A2E",
    "zone_a":    "#00D4FF",
    "zone_b":    "#00E676",
    "zone_c":    "#FFB300",
    "zone_d":    "#FF6B6B",
}

# ─────────────────────────────────────────────────────────────────
#  SIMULATION ENGINE
# ─────────────────────────────────────────────────────────────────

ZONES = ["Zone A (Central)", "Zone B (North)", "Zone C (Elevated)", "Zone D (Tail-End)"]
ZONE_COLORS = [C["zone_a"], C["zone_b"], C["zone_c"], C["zone_d"]]
ZONE_BASE_PRESSURE = [3.8, 3.2, 2.4, 1.8]  # bar
ZONE_MIN_OK = [2.5, 2.5, 2.0, 1.5]

class WaterSimulator:
    def __init__(self):
        self.running = True
        self.tick = 0
        self.history_len = 120  # 2 min of data points
        self.anomaly_active = {z: False for z in ZONES}
        self.anomaly_type   = {z: None for z in ZONES}

        # Per-zone rolling history
        self.pressure_hist = {z: deque([ZONE_BASE_PRESSURE[i]] * self.history_len,
                                       maxlen=self.history_len)
                              for i, z in enumerate(ZONES)}
        self.flow_hist     = {z: deque([round(random.uniform(8, 14), 2)] * self.history_len,
                                       maxlen=self.history_len)
                              for i, z in enumerate(ZONES)}

        # Alerts log
        self.alerts = []
        self.total_alerts = 0

        # Metrics
        self.nrw_percent = 18.4
        self.energy_kwh  = 0.0
        self.uptime_pct  = 99.2

        # Pump status
        self.pump_status = ["Running", "Running", "Standby", "Running"]
        self.valve_status = [True, True, False, True]

    def step(self):
        self.tick += 1
        t = self.tick

        for i, zone in enumerate(ZONES):
            base = ZONE_BASE_PRESSURE[i]
            # Natural sinusoidal demand variation
            demand_wave = 0.3 * math.sin(t / 20.0) + 0.1 * math.sin(t / 7.0)
            noise = random.gauss(0, 0.05)

            # Random anomaly injection (rare)
            if not self.anomaly_active[zone] and random.random() < 0.003:
                self.anomaly_active[zone] = True
                self.anomaly_type[zone] = random.choice(["leak", "burst", "low_pressure"])
                self._add_alert(zone, self.anomaly_type[zone])

            anom_effect = 0.0
            if self.anomaly_active[zone]:
                atype = self.anomaly_type[zone]
                if atype == "leak":
                    anom_effect = -0.4
                elif atype == "burst":
                    anom_effect = -0.9
                elif atype == "low_pressure":
                    anom_effect = -0.6
                # Auto-resolve after ~30 ticks
                if random.random() < 0.035:
                    self.anomaly_active[zone] = False
                    self.anomaly_type[zone] = None

            pressure = max(0.3, base + demand_wave + noise + anom_effect)
            flow = max(0.5, (pressure / base) * random.uniform(10, 15))

            self.pressure_hist[zone].append(round(pressure, 3))
            self.flow_hist[zone].append(round(flow, 2))

        # Update global metrics slowly
        if t % 10 == 0:
            self.nrw_percent = max(10, min(35, self.nrw_percent + random.gauss(0, 0.3)))
            self.energy_kwh  += random.uniform(0.05, 0.12)
            active_anomalies  = sum(1 for z in ZONES if self.anomaly_active[z])
            self.uptime_pct   = 100.0 if active_anomalies == 0 else max(90.0, 100 - active_anomalies * 2.5)

    def current_pressure(self, zone):
        return list(self.pressure_hist[zone])[-1]

    def current_flow(self, zone):
        return list(self.flow_hist[zone])[-1]

    def zone_status(self, zone):
        p = self.current_pressure(zone)
        i = ZONES.index(zone)
        if self.anomaly_active[zone]:
            atype = self.anomaly_type[zone]
            if atype == "burst": return "BURST"
            if atype == "leak":  return "LEAK"
            return "LOW"
        if p < ZONE_MIN_OK[i]:
            return "LOW"
        if p > ZONE_BASE_PRESSURE[i] + 0.8:
            return "HIGH"
        return "OK"

    def _add_alert(self, zone, atype):
        self.total_alerts += 1
        msg = {
            "leak":         f"⚠ Possible leak detected in {zone}",
            "burst":        f"🔴 Pipe burst alert in {zone}!",
            "low_pressure": f"⬇ Low pressure threshold crossed in {zone}",
        }.get(atype, f"Alert in {zone}")
        ts = datetime.now().strftime("%H:%M:%S")
        self.alerts.insert(0, (ts, msg, atype))
        if len(self.alerts) > 50:
            self.alerts.pop()

    def resolve_anomaly(self, zone):
        self.anomaly_active[zone] = False
        self.anomaly_type[zone] = None

    def toggle_valve(self, zone_idx):
        self.valve_status[zone_idx] = not self.valve_status[zone_idx]


SIM = WaterSimulator()


# ─────────────────────────────────────────────────────────────────
#  HELPERS
# ─────────────────────────────────────────────────────────────────

def status_color(status):
    return {"OK": C["green"], "LOW": C["amber"], "HIGH": C["red"],
            "LEAK": C["amber"], "BURST": C["red"]}.get(status, C["muted"])

def pressure_bar_color(pressure, min_ok, base):
    if pressure < min_ok:   return C["red"]
    if pressure > base + 0.7: return C["amber"]
    return C["green"]

class Tooltip:
    def __init__(self, widget, text):
        self.widget = widget
        self.text = text
        self.tip = None
        widget.bind("<Enter>", self._show)
        widget.bind("<Leave>", self._hide)

    def _show(self, _=None):
        if self.tip or not self.text:
            return
        x = self.widget.winfo_rootx() + 20
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 2
        self.tip = tk.Toplevel(self.widget)
        self.tip.wm_overrideredirect(True)
        self.tip.configure(bg=C["surface"])
        lbl = tk.Label(self.tip, text=self.text, bg=C["surface"],
                       fg=C["muted"], font=("Courier New", 8), padx=6, pady=3)
        lbl.pack()
        self.tip.wm_geometry(f"+{x}+{y}")

    def _hide(self, _=None):
        if self.tip:
            self.tip.destroy()
            self.tip = None


# ─────────────────────────────────────────────────────────────────
#  CUSTOM WIDGETS
# ─────────────────────────────────────────────────────────────────

class GaugeCanvas(tk.Canvas):
    """Semi-circular pressure gauge."""
    def __init__(self, parent, size=120, **kw):
        kw.setdefault("bg", C["panel"])
        kw.setdefault("highlightthickness", 0)
        super().__init__(parent, width=size, height=size//2 + 20, **kw)
        self.size = size
        self.value = 0.0
        self.max_val = 6.0
        self._draw()

    def set_value(self, val, color=C["teal"]):
        self.value = val
        self.color = color
        self._draw()

    def _draw(self):
        self.delete("all")
        s = self.size
        cx, cy = s // 2, s // 2 + 5
        r = s // 2 - 10

        # Background arc
        self.create_arc(cx-r, cy-r, cx+r, cy+r,
                        start=0, extent=180, style="arc",
                        outline=C["border"], width=10)

        # Value arc
        angle = (self.value / self.max_val) * 180
        color = getattr(self, "color", C["teal"])
        if angle > 0:
            self.create_arc(cx-r, cy-r, cx+r, cy+r,
                            start=0, extent=min(angle, 180), style="arc",
                            outline=color, width=10)

        # Needle
        rad = math.radians(180 - angle)
        nx = cx + (r - 15) * math.cos(rad)
        ny = cy - (r - 15) * math.sin(rad)
        self.create_line(cx, cy, nx, ny, fill=C["white"], width=2)
        self.create_oval(cx-4, cy-4, cx+4, cy+4, fill=C["white"], outline="")

        # Value text
        self.create_text(cx, cy - 8, text=f"{self.value:.2f}",
                         fill=C["white"], font=("Courier New", 10, "bold"))
        self.create_text(cx, cy + 8, text="bar",
                         fill=C["muted"], font=("Courier New", 8))


class PulsingDot(tk.Canvas):
    """Animated status dot."""
    def __init__(self, parent, size=14, **kw):
        kw.setdefault("bg", C["panel"])
        kw.setdefault("highlightthickness", 0)
        super().__init__(parent, width=size, height=size, **kw)
        self.size = size
        self.color = C["green"]
        self._pulse = 0
        self._animate()

    def set_color(self, color):
        self.color = color

    def _animate(self):
        self._pulse = (self._pulse + 1) % 20
        alpha = abs(10 - self._pulse) / 10.0
        r = int(self.size * (0.4 + 0.15 * alpha))
        c = self.size // 2
        self.delete("all")
        # glow ring
        self.create_oval(c-r-2, c-r-2, c+r+2, c+r+2,
                        outline=self.color, width=1)
        # solid dot
        self.create_oval(c-5, c-5, c+5, c+5,
                         fill=self.color, outline="")
        self.after(80, self._animate)


# ─────────────────────────────────────────────────────────────────
#  ZONE CARD
# ─────────────────────────────────────────────────────────────────

class ZoneCard(tk.Frame):
    def __init__(self, parent, zone_idx, **kw):
        super().__init__(parent, bg=C["panel"], bd=0,
                         highlightthickness=1,
                         highlightbackground=C["border"], **kw)
        self.zone_idx = zone_idx
        self.zone = ZONES[zone_idx]
        self.zcolor = ZONE_COLORS[zone_idx]
        self._build()

    def _build(self):
        # Header
        hdr = tk.Frame(self, bg=C["surface"])
        hdr.pack(fill="x")

        self.dot = PulsingDot(hdr, bg=C["surface"])
        self.dot.pack(side="left", padx=8, pady=6)

        tk.Label(hdr, text=self.zone, bg=C["surface"],
                 fg=self.zcolor, font=("Courier New", 10, "bold")).pack(side="left")

        self.status_lbl = tk.Label(hdr, text="● OK", bg=C["surface"],
                                   fg=C["green"], font=("Courier New", 9, "bold"))
        self.status_lbl.pack(side="right", padx=10)

        # Gauge
        self.gauge = GaugeCanvas(self, size=110)
        self.gauge.pack(pady=(6, 0))

        # Stats row
        stats = tk.Frame(self, bg=C["panel"])
        stats.pack(fill="x", padx=8, pady=4)

        self.press_lbl = tk.Label(stats, text="Pressure: --", bg=C["panel"],
                                  fg=C["text"], font=("Courier New", 9))
        self.press_lbl.pack(side="left")

        self.flow_lbl = tk.Label(stats, text="Flow: --", bg=C["panel"],
                                 fg=C["muted"], font=("Courier New", 9))
        self.flow_lbl.pack(side="right")

        # Resolve button
        self.resolve_btn = tk.Button(self, text="⚡ Resolve Anomaly",
                                     bg=C["red"], fg=C["white"],
                                     font=("Courier New", 8, "bold"),
                                     relief="flat", cursor="hand2",
                                     command=self._resolve)
        # Valve toggle
        valve_row = tk.Frame(self, bg=C["panel"])
        valve_row.pack(fill="x", padx=8, pady=(0, 6))
        tk.Label(valve_row, text="Valve:", bg=C["panel"],
                 fg=C["muted"], font=("Courier New", 8)).pack(side="left")
        self.valve_btn = tk.Button(valve_row, text="OPEN",
                                   bg=C["green"], fg=C["bg"],
                                   font=("Courier New", 8, "bold"),
                                   relief="flat", cursor="hand2", width=6,
                                   command=self._toggle_valve)
        self.valve_btn.pack(side="left", padx=6)

    def update(self):
        p = SIM.current_pressure(self.zone)
        f = SIM.current_flow(self.zone)
        status = SIM.zone_status(self.zone)
        sc = status_color(status)
        i = self.zone_idx
        color = pressure_bar_color(p, ZONE_MIN_OK[i], ZONE_BASE_PRESSURE[i])

        self.gauge.set_value(p, color)
        self.dot.set_color(sc)
        self.status_lbl.config(text=f"● {status}", fg=sc)
        self.press_lbl.config(text=f"P: {p:.2f} bar", fg=color)
        self.flow_lbl.config(text=f"F: {f:.1f} L/s")

        # Show/hide resolve button
        if SIM.anomaly_active[self.zone]:
            self.resolve_btn.pack(fill="x", padx=8, pady=2)
        else:
            self.resolve_btn.pack_forget()

        # Valve button
        v = SIM.valve_status[self.zone_idx]
        self.valve_btn.config(text="OPEN" if v else "CLOSED",
                              bg=C["green"] if v else C["red"])

    def _resolve(self):
        SIM.resolve_anomaly(self.zone)

    def _toggle_valve(self):
        SIM.toggle_valve(self.zone_idx)


# ─────────────────────────────────────────────────────────────────
#  CHART PANEL
# ─────────────────────────────────────────────────────────────────

class ChartPanel(tk.Frame):
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C["bg"], **kw)
        if not HAS_MPL:
            tk.Label(self, text="matplotlib not installed\npip install matplotlib",
                     bg=C["bg"], fg=C["red"]).pack(expand=True)
            return
        self._build_charts()

    def _build_charts(self):
        self.fig = Figure(figsize=(8, 5), facecolor=C["chart_bg"])
        gs = gridspec.GridSpec(2, 2, figure=self.fig, hspace=0.4, wspace=0.35)

        axs = [self.fig.add_subplot(gs[r, c]) for r in range(2) for c in range(2)]
        self.axes = axs

        titles = ["Zone A — Central", "Zone B — North",
                  "Zone C — Elevated", "Zone D — Tail-End"]
        self.lines = []

        for ax, title, color in zip(axs, titles, ZONE_COLORS):
            ax.set_facecolor(C["chart_bg"])
            ax.set_title(title, color=color, fontsize=8, fontweight="bold", pad=4)
            ax.tick_params(colors=C["muted"], labelsize=6)
            for spine in ax.spines.values():
                spine.set_edgecolor(C["border"])
            ax.set_ylim(0, 6)
            ax.set_xlim(0, SIM.history_len)
            ax.axhline(y=2.0, color=C["red"], linewidth=0.8, linestyle="--", alpha=0.6)
            ax.set_ylabel("bar", color=C["muted"], fontsize=6)
            line, = ax.plot([], [], color=color, linewidth=1.5, alpha=0.9)
            fill = ax.fill_between([], [], alpha=0.0)  # placeholder
            self.lines.append((line, ax, color))

        canvas = FigureCanvasTkAgg(self.fig, master=self)
        canvas.draw()
        canvas.get_tk_widget().pack(fill="both", expand=True)
        self.canvas = canvas

    def refresh(self):
        if not HAS_MPL:
            return
        x = list(range(SIM.history_len))
        for i, (line, ax, color) in enumerate(self.lines):
            zone = ZONES[i]
            y = list(SIM.pressure_hist[zone])
            line.set_data(x, y)
            # Recolor fill
            for coll in ax.collections:
                coll.remove()
            ax.fill_between(x, y, alpha=0.12, color=color)
        self.canvas.draw_idle()


# ─────────────────────────────────────────────────────────────────
#  ALERT LOG PANEL
# ─────────────────────────────────────────────────────────────────

class AlertPanel(tk.Frame):
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C["panel"],
                         highlightthickness=1,
                         highlightbackground=C["border"], **kw)
        self._build()

    def _build(self):
        hdr = tk.Frame(self, bg=C["surface"])
        hdr.pack(fill="x")
        tk.Label(hdr, text="🔔  ALERT LOG", bg=C["surface"],
                 fg=C["amber"], font=("Courier New", 10, "bold")).pack(side="left", padx=10, pady=6)
        self.count_lbl = tk.Label(hdr, text="0 alerts", bg=C["surface"],
                                  fg=C["muted"], font=("Courier New", 9))
        self.count_lbl.pack(side="right", padx=10)

        container = tk.Frame(self, bg=C["panel"])
        container.pack(fill="both", expand=True)

        scrollbar = tk.Scrollbar(container, bg=C["border"], troughcolor=C["panel"])
        scrollbar.pack(side="right", fill="y")

        self.listbox = tk.Listbox(container, bg=C["panel"], fg=C["text"],
                                  font=("Courier New", 9),
                                  relief="flat", selectbackground=C["surface"],
                                  yscrollcommand=scrollbar.set,
                                  highlightthickness=0, bd=0)
        self.listbox.pack(fill="both", expand=True)
        scrollbar.config(command=self.listbox.yview)

    def refresh(self):
        self.listbox.delete(0, "end")
        for ts, msg, atype in SIM.alerts:
            color = C["red"] if atype == "burst" else C["amber"]
            self.listbox.insert("end", f"  {ts}  {msg}")
            self.listbox.itemconfig("end", fg=color)
        self.count_lbl.config(text=f"{SIM.total_alerts} alerts")


# ─────────────────────────────────────────────────────────────────
#  KPI STRIP
# ─────────────────────────────────────────────────────────────────

class KPIStrip(tk.Frame):
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C["bg"], **kw)
        kpis = [
            ("💧 Total Zones", "4",        C["teal"]),
            ("📊 NRW %",       "18.4%",    C["amber"]),
            ("⚡ Energy Used", "0.0 kWh",  C["green"]),
            ("🟢 Uptime",      "99.2%",    C["green"]),
            ("🔔 Total Alerts","0",        C["red"]),
            ("🕒 Last Update", "--:--:--", C["muted"]),
        ]
        self.labels = {}
        for i, (title, val, color) in enumerate(kpis):
            card = tk.Frame(self, bg=C["panel"],
                            highlightthickness=1,
                            highlightbackground=C["border"])
            card.pack(side="left", expand=True, fill="both", padx=4, pady=4)
            tk.Label(card, text=title, bg=C["panel"],
                     fg=C["muted"], font=("Courier New", 8)).pack(pady=(6, 0))
            lbl = tk.Label(card, text=val, bg=C["panel"],
                           fg=color, font=("Courier New", 12, "bold"))
            lbl.pack(pady=(0, 6))
            self.labels[title] = (lbl, color)

    def refresh(self):
        now = datetime.now().strftime("%H:%M:%S")
        updates = {
            "📊 NRW %":       (f"{SIM.nrw_percent:.1f}%",
                                C["red"] if SIM.nrw_percent > 25 else C["amber"]),
            "⚡ Energy Used": (f"{SIM.energy_kwh:.1f} kWh", C["green"]),
            "🟢 Uptime":      (f"{SIM.uptime_pct:.1f}%",
                                C["green"] if SIM.uptime_pct > 97 else C["amber"]),
            "🔔 Total Alerts":(str(SIM.total_alerts),
                                C["red"] if SIM.total_alerts > 0 else C["green"]),
            "🕒 Last Update": (now, C["muted"]),
        }
        for key, (val, color) in updates.items():
            if key in self.labels:
                lbl, _ = self.labels[key]
                lbl.config(text=val, fg=color)


# ─────────────────────────────────────────────────────────────────
#  AI ANOMALY PANEL
# ─────────────────────────────────────────────────────────────────

class AIPanel(tk.Frame):
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C["panel"],
                         highlightthickness=1,
                         highlightbackground=C["border"], **kw)
        self._build()

    def _build(self):
        hdr = tk.Frame(self, bg=C["surface"])
        hdr.pack(fill="x")
        tk.Label(hdr, text="🤖  AI ANOMALY DETECTION",
                 bg=C["surface"], fg=C["teal"],
                 font=("Courier New", 10, "bold")).pack(side="left", padx=10, pady=6)

        self.grid_frame = tk.Frame(self, bg=C["panel"])
        self.grid_frame.pack(fill="both", expand=True, padx=8, pady=6)

        self.rows = {}
        for z in ZONES:
            row = tk.Frame(self.grid_frame, bg=C["panel"])
            row.pack(fill="x", pady=2)
            zcolor = ZONE_COLORS[ZONES.index(z)]
            tk.Label(row, text=z[:15], bg=C["panel"],
                     fg=zcolor, font=("Courier New", 9, "bold"), width=20,
                     anchor="w").pack(side="left")
            bar_frame = tk.Frame(row, bg=C["border"], height=10, width=180)
            bar_frame.pack(side="left", padx=6)
            bar_frame.pack_propagate(False)
            bar = tk.Frame(bar_frame, bg=C["green"], height=10, width=0)
            bar.place(x=0, y=0, relheight=1)
            type_lbl = tk.Label(row, text="Normal", bg=C["panel"],
                                fg=C["green"], font=("Courier New", 9))
            type_lbl.pack(side="left")
            self.rows[z] = (bar, type_lbl, bar_frame)

    def refresh(self):
        for z in ZONES:
            bar, lbl, frame = self.rows[z]
            p = SIM.current_pressure(z)
            i = ZONES.index(z)
            base = ZONE_BASE_PRESSURE[i]
            deviation = abs(p - base) / base  # 0-1 anomaly score
            score = min(1.0, deviation * 3)
            width = int(frame.winfo_width() * score) if frame.winfo_width() > 1 else int(180 * score)

            if SIM.anomaly_active[z]:
                atype = SIM.anomaly_type[z]
                color = C["red"] if atype == "burst" else C["amber"]
                label = {"leak": "⚠ Leak", "burst": "🔴 BURST!", "low_pressure": "⬇ Low P"}.get(atype, "Alert")
            elif score > 0.5:
                color = C["amber"]
                label = "Elevated"
            else:
                color = C["green"]
                label = "Normal"

            bar.config(bg=color, width=max(2, width))
            lbl.config(text=label, fg=color)


# ─────────────────────────────────────────────────────────────────
#  MAIN APPLICATION
# ─────────────────────────────────────────────────────────────────

class HydronautsApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("HYDRONAUTS — Smart Water Pressure Management | SMC Solapur")
        self.configure(bg=C["bg"])
        self.geometry("1280x800")
        self.minsize(1100, 700)
        self._build_ui()
        self._start_sim()
        self._bind_shortcuts()

    # ── UI Construction ──────────────────────────────────────────

    def _build_ui(self):
        self._build_topbar()
        main = tk.Frame(self, bg=C["bg"])
        main.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        self.status = tk.Frame(self, bg=C["surface"])
        self.status.pack(fill="x", side="bottom")
        self.status_lbl = tk.Label(self.status, text="",
                                   bg=C["surface"], fg=C["muted"],
                                   font=("Courier New", 8))
        self.status_lbl.pack(side="right", padx=8)

        # KPI strip
        self.kpi = KPIStrip(main)
        self.kpi.pack(fill="x")

        # Body: left (zones) | right (charts + alerts + AI)
        body = tk.Frame(main, bg=C["bg"])
        body.pack(fill="both", expand=True, pady=6)

        # ── Left: Zone Cards ────────────────────────────────────
        left = tk.Frame(body, bg=C["bg"])
        left.pack(side="left", fill="y")

        zone_title = tk.Label(left, text="▸ DISTRIBUTION ZONES",
                              bg=C["bg"], fg=C["teal"],
                              font=("Courier New", 9, "bold"))
        zone_title.pack(anchor="w", padx=4, pady=(0, 4))

        self.zone_cards = []
        grid = tk.Frame(left, bg=C["bg"])
        grid.pack()
        for i, z in enumerate(ZONES):
            r, c = divmod(i, 2)
            card = ZoneCard(grid, i)
            card.grid(row=r, column=c, padx=4, pady=4, sticky="nsew")
            self.zone_cards.append(card)

        # ── Right: Charts + panels ──────────────────────────────
        right = tk.Frame(body, bg=C["bg"])
        right.pack(side="left", fill="both", expand=True, padx=(8, 0))

        # Chart panel
        chart_lbl = tk.Label(right, text="▸ REAL-TIME PRESSURE HISTORY  (— 2 min window)",
                             bg=C["bg"], fg=C["teal"], font=("Courier New", 9, "bold"))
        chart_lbl.pack(anchor="w", pady=(0, 4))
        self.chart = ChartPanel(right)
        self.chart.pack(fill="both", expand=True)

        # Bottom: AI + Alerts side-by-side
        bottom = tk.Frame(right, bg=C["bg"])
        bottom.pack(fill="x", pady=(8, 0))

        self.ai_panel = AIPanel(bottom)
        self.ai_panel.pack(side="left", fill="both", expand=True, padx=(0, 4))

        self.alert_panel = AlertPanel(bottom)
        self.alert_panel.pack(side="left", fill="both", expand=True)

    def _build_topbar(self):
        bar = tk.Frame(self, bg=C["surface"], height=52)
        bar.pack(fill="x")
        bar.pack_propagate(False)

        # Logo / brand
        tk.Label(bar, text="💧 HYDRONAUTS",
                 bg=C["surface"], fg=C["teal"],
                 font=("Courier New", 16, "bold")).pack(side="left", padx=16)

        tk.Label(bar, text="Smart Water Pressure Management System — Solapur Municipal Corporation",
                 bg=C["surface"], fg=C["muted"],
                 font=("Courier New", 9)).pack(side="left")

        # Right controls
        right = tk.Frame(bar, bg=C["surface"])
        right.pack(side="right", padx=12)

        self.sim_btn = tk.Button(right, text="⏸ PAUSE SIM",
                                 bg=C["teal"], fg=C["bg"],
                                 font=("Courier New", 9, "bold"),
                                 relief="flat", cursor="hand2", padx=10,
                                 command=self._toggle_sim)
        self.sim_btn.pack(side="left", padx=4)

        self.clear_btn = tk.Button(right, text="🗑 CLEAR ALERTS",
                                   bg=C["border"], fg=C["text"],
                                   font=("Courier New", 9), relief="flat",
                                   cursor="hand2", padx=8,
                                   command=self._clear_alerts)
        self.clear_btn.pack(side="left", padx=4)

        self.info_btn = tk.Button(right, text="ℹ INFO",
                                  bg=C["border"], fg=C["text"],
                                  font=("Courier New", 9), relief="flat",
                                  cursor="hand2", padx=8,
                                  command=self._show_info)
        self.info_btn.pack(side="left", padx=4)

        # Live indicator
        self.live_dot = PulsingDot(right, bg=C["surface"])
        self.live_dot.pack(side="left", padx=4)
        tk.Label(right, text="LIVE", bg=C["surface"],
                 fg=C["green"], font=("Courier New", 8, "bold")).pack(side="left")
        Tooltip(self.sim_btn, "Pause/Resume simulation (P)")
        Tooltip(self.clear_btn, "Clear all alerts (C)")
        Tooltip(self.info_btn, "About this app (I)")

    # ── Simulation Thread ─────────────────────────────────────────

    def _start_sim(self):
        self._sim_running = True
        self._sim_thread = threading.Thread(target=self._sim_loop, daemon=True)
        self._sim_thread.start()
        self._refresh_ui()

    def _sim_loop(self):
        while True:
            if self._sim_running:
                SIM.step()
            time.sleep(0.5)

    def _refresh_ui(self):
        for card in self.zone_cards:
            card.update()
        self.kpi.refresh()
        self.chart.refresh()
        self.alert_panel.refresh()
        self.ai_panel.refresh()
        state = "LIVE" if self._sim_running else "PAUSED"
        self.status_lbl.config(text=f"{datetime.now().strftime('%H:%M:%S')} · {state} · Alerts {SIM.total_alerts}")
        self.after(600, self._refresh_ui)

    # ── Controls ──────────────────────────────────────────────────

    def _bind_shortcuts(self):
        self.bind("<Key-p>", lambda _: self._toggle_sim())
        self.bind("<Key-P>", lambda _: self._toggle_sim())
        self.bind("<Key-c>", lambda _: self._clear_alerts())
        self.bind("<Key-C>", lambda _: self._clear_alerts())
        self.bind("<Key-i>", lambda _: self._show_info())
        self.bind("<Key-I>", lambda _: self._show_info())

    def _toggle_sim(self):
        self._sim_running = not self._sim_running
        if self._sim_running:
            self.sim_btn.config(text="⏸ PAUSE SIM", bg=C["teal"])
            self.live_dot.set_color(C["green"])
        else:
            self.sim_btn.config(text="▶ RESUME SIM", bg=C["amber"])
            self.live_dot.set_color(C["amber"])

    def _clear_alerts(self):
        SIM.alerts.clear()
        SIM.total_alerts = 0

    def _show_info(self):
        info = (
            "HYDRONAUTS — Smart Water Pressure Management\n"
            "════════════════════════════════════════════\n\n"
            "Project: IoT-based Water Pressure Monitoring\n"
            "Client : Solapur Municipal Corporation (SMC)\n"
            "Team   : Hydronauts\n\n"
            "Features:\n"
            "  • Real-time pressure & flow monitoring\n"
            "  • AI anomaly detection (leak / burst)\n"
            "  • Zone-level valve control\n"
            "  • Alert logging with timestamps\n"
            "  • NRW, energy & uptime KPIs\n\n"
            "Zones:\n"
            "  A – Central   | B – North\n"
            "  C – Elevated  | D – Tail-End\n\n"
            "Thresholds:\n"
            "  Min pressure: 1.5 – 2.5 bar (zone-wise)\n"
            "  NRW alert   : > 25%\n"
        )
        messagebox.showinfo("About Hydronauts", info)


# ─────────────────────────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    app = HydronautsApp()
    app.mainloop()
