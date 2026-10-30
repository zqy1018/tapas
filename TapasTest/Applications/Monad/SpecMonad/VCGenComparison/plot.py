#!/usr/bin/env python3
"""Draw a run's results.json as SVG figures, with figures/index.html showing them all; see PROTOCOL.md.

The figures: two scoreboards (total time at each case's largest common size, and how time grows with n),
the phase breakdown of each measurement, and total time and peak memory against n. Medians are formed
from the samples as run.py's report() forms them, so an interrupted run can be drawn too; runs recorded
before Share or peak memory were measured are drawn without them. Standard library only.

The page and figures are self-contained and name no local file, user, or machine, so they can be published
as they are: text from the records, such as Lean's error messages, has local paths and names replaced, and
a file that would still contain one is not written.

  python3 plot.py                                    # the run `all`, into results/all/figures/
  python3 plot.py --name tonight                      # the run `tonight`, in results/tonight/
  python3 plot.py --name elab-async-20261101          # an archived run
  python3 plot.py --results PATH --out DIR            # any results.json, the figures in DIR
"""

import argparse
import html
import json
import math
import os
from pathlib import Path
import pwd
import re
import socket
import statistics

import run


FOLDER = Path(__file__).resolve().parent
# Known routes in display order, by family; other routes follow in their order in the results.
FAMILIES = [["vcgen", "vcgen-finish", "vcgen-finish-simp"], ["sym"], ["normalize", "normalize-sym"],
            ["dsimp", "sym-dsimp"], ["wp-simp", "wp-sym"]]
ROUTES = [route for family in FAMILIES for route in family]
TIERS = ["custom-monad", "hand-written-specs", "library", "-"]
MODES = {"complete": "Complete proofs", "generation": "Generation only"}
SKIPPED = "skipped after smaller failure"
# Outcomes of a configuration at a size that are neither a result nor a failure.
UNFINISHED = ("partial", "missing")

# Light-surface tokens of the data-viz reference palette.
SURFACE, PAGE, INK, INK2, MUTED = "#fcfcfb", "#f9f9f7", "#0b0b0b", "#52514e", "#898781"
GRID, AXIS, CONTEXT, BAND = "#e1e0d9", "#c3c2b7", "#d6d5ce", "#f3f2ee"
FONT = 'system-ui, -apple-system, "Segoe UI", sans-serif'
# Phases in the order they run. The five hues pass the palette validator as neighbors in a stack.
PHASES = [("prepare", "Prepare", "#eda100"), ("generate", "Generate", "#008300"),
          ("grind", "Grind", "#e87ba4"), ("share", "Share", "#6250d6"), ("kernel", "Kernel", "#e34948")]
OTHER = "#a3a29c"
# Tiers, on the three hues left by the phases that pass the validator as all pairs. Sym has no tier.
TIER_COLORS = {"custom-monad": "#1baf7a", "hand-written-specs": "#2a78d6", "library": "#eb6834", "-": INK2}
SPARE_COLORS = ["#6250d6", "#008300", "#e87ba4"]
# Scoreboard bins on one blue ramp, light to dark: (upper bound, label, fill, text ink).
SLOWDOWN = [(1.25, "≤ 1.25×", "#cde2fb", INK), (2, "≤ 2×", "#9ec5f4", INK), (4, "≤ 4×", "#6da7ec", INK),
            (10, "≤ 10×", "#2a78d6", "#ffffff"), (30, "≤ 30×", "#1c5cab", "#ffffff"),
            (math.inf, "> 30×", "#0d366b", "#ffffff")]
GROWTH = [(1.25, "< 1.25", "#cde2fb", INK), (1.75, "1.25–1.75", "#86b6ef", INK),
          (2.25, "1.75–2.25 (≈ n²)", "#3987e5", "#ffffff"), (2.75, "2.25–2.75", "#1c5cab", "#ffffff"),
          (math.inf, "≥ 2.75", "#0d366b", "#ffffff")]
# Advance widths of Helvetica in thousandths of an em, to lay out text without a font.
WIDTHS = dict(zip(
    " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~",
    [278, 278, 355, 556, 556, 889, 667, 191, 333, 333, 389, 584, 278, 333, 278, 278] + [556] * 10 +
    [278, 278, 584, 584, 584, 556, 1015, 667, 667, 722, 722, 667, 611, 778, 722, 278, 500, 667, 556, 833, 722,
     778, 667, 778, 722, 667, 611, 722, 667, 944, 667, 667, 611, 278, 278, 278, 469, 556, 333, 556, 556, 500,
     556, 556, 278, 556, 556, 222, 222, 500, 222, 833, 556, 556, 556, 556, 333, 500, 278, 556, 500, 722, 500,
     500, 500, 334, 260, 334, 584]))
# An absolute path, or one from `.` or `..`, of at least two parts; not `a/b` or `(x)/2`, nor a URL.
LOCAL_PATH = re.compile(r"(?<![\w~./\\])(?:~|\.{1,2}|[A-Za-z]:)?[/\\](?:[^\s/\\'\"`<>()]+[/\\])+[^\s/\\'\"`<>()]*")


# Publishing

def local_names():
    """What identifies this machine or its user: the home and repository folders, the login and full names,
    and the host name, longest first."""
    user, host = pwd.getpwuid(os.getuid()), socket.gethostname()
    names = {str(Path.home()), str(run.REPO), user.pw_name, user.pw_gecos.split(",")[0], host, host.split(".")[0]}
    return sorted((name for name in names if len(name) >= 3), key=len, reverse=True)


LOCAL_NAMES = local_names()


def public(content):
    """Text from the records, such as a Lean error message, with local paths and names replaced."""
    content = LOCAL_PATH.sub("<path>", content)
    for name in LOCAL_NAMES:
        content = content.replace(name, "<local>")
    return content


def check(name, content):
    """Refuse to write a file that would name a local file, user, or machine."""
    path = LOCAL_PATH.search(content)
    found = path.group() if path else next((n for n in LOCAL_NAMES if n in content), None)
    if found:
        raise SystemExit(f"Not writing {name}: it would contain {found!r}")


# Data

def order(items, known):
    """The distinct `items` in the order of `known`, then the others in their order of appearance."""
    seen = list(dict.fromkeys(items))
    return [item for item in known if item in seen] + [item for item in seen if item not in known]


def family(route):
    return next((i for i, routes in enumerate(FAMILIES) if route in routes), len(FAMILIES))


def ident(record):
    return record["case"], record["mode"], record["route"], record["tier"]


def one_time(state, case, route, tier):
    """A route's one-time cost for a case, as report() in run.py adds it to the medians, or None."""
    setup = state.get("setup_ms")
    try:
        if setup and route in {label for _, label in run.NORMALIZATION}:
            return run.one_time(setup, case, tier)
        if setup and route in {label for _, label in run.WP_ROUTES}:
            return run.wp_one_time(setup, case)
    except KeyError:
        pass
    return None


def medians(state):
    """Median rows by (case, mode, route, tier, n), as report() in run.py forms them, from the samples."""
    groups = {}
    for row in state["runs"]:
        groups.setdefault(ident(row) + (row["n"],), []).append(row)
    rows = {}
    for key, samples in groups.items():
        if len(samples) != state["repetitions"]:
            continue
        row = dict(vc_count=samples[0]["vc_count"])
        for field in samples[0]:
            if field.endswith("_hms") and all(field in s for s in samples):
                row[field[:-4] + "_ms"] = statistics.median(s[field] for s in samples) / 100
        if all("peak_mb" in s for s in samples):
            row["peak_mb"] = statistics.median(s["peak_mb"] for s in samples)
        cost = one_time(state, key[0], key[2], key[3])
        if cost is not None:
            row["one_time_ms"] = cost
        rows[key] = row
    return rows


def load(path):
    """The run with its medians, statuses by key, and its configurations, cases, and routes in order."""
    state = json.loads(path.read_text())
    records = state["statuses"] + state["runs"]
    statuses = {}
    for record in state["statuses"]:
        statuses.setdefault(ident(record) + (record["n"],), []).append(record)
    cases = order([r["case"] for r in records], run.CASES)
    modes = order([r["mode"] for r in records], list(MODES))
    routes = order([r["route"] for r in records], ROUTES)
    tiers = order([r["tier"] for r in records], TIERS)
    present = {ident(r) for r in records}
    configs = [(case, mode, route, tier) for case in cases for mode in modes for route in routes for tier in tiers
               if (case, mode, route, tier) in present]
    rows = medians(state)
    phases = [phase for phase in PHASES if any(phase[0] + "_ms" in row for row in rows.values())]
    colors = dict(TIER_COLORS)
    for tier, color in zip([t for t in tiers if t not in colors], SPARE_COLORS * 3):
        colors[tier] = color
    return dict(state=state, medians=rows, statuses=statuses, configs=configs, cases=cases, modes=modes,
                routes=routes, phases=phases, tier_colors=colors)


def sizes(data, case, mode):
    """The planned and recorded sizes of a case in a mode."""
    planned = data["state"].get("sizes", {}).get(case, {}).get(mode, [])
    recorded = [key[4] for key in data["statuses"] if key[:2] == (case, mode)]
    return sorted(set(planned) | set(recorded) | {key[4] for key in data["medians"] if key[:2] == (case, mode)})


def outcome(data, config, n):
    """What a configuration recorded at size n: ("ok", median row), (status, record) for a failure at n,
    ("skipped", the failure at a smaller size), ("partial", samples so far), or ("missing", None)."""
    if config + (n,) in data["medians"]:
        return "ok", data["medians"][config + (n,)]
    statuses = data["statuses"].get(config + (n,), [])
    failed = [s for s in statuses if s["status"] not in ("ok", SKIPPED)]
    if failed:
        return failed[0]["status"], failed[0]
    if any(s["status"] == SKIPPED for s in statuses):
        earlier = [s for key, records in data["statuses"].items() if key[:4] == config and key[4] < n
                   for s in records if s["status"] not in ("ok", SKIPPED)]
        return "skipped", max(earlier, key=lambda s: s["n"]) if earlier else None
    return ("partial", len(statuses)) if statuses else ("missing", None)


def failure_text(data, status, record, short=False):
    """A failure in words, e.g. `timeout > 60 s`, or `timeout` if short."""
    state = data["state"]
    if status == "skipped":
        if record is None:
            return "skipped"
        earlier = failure_text(data, record["status"], record, short)
        return f"{earlier} @{record['n']}" if short else f"{earlier}, at n = {record['n']}; larger sizes skipped"
    if status == "partial":
        return "in progress" if short else f"{record} of {state['repetitions']} runs recorded so far"
    if status == "missing":
        return "not run" if short else "not measured"
    if short:
        return status
    reason = public((record or {}).get("reason") or "")
    if status == "timeout":
        limit = state.get("timeout_seconds", state.get("process_timeout_seconds", 60))
        return f"timeout: {reason} (limit {limit} s)" if reason.startswith("measured") else \
            f"timeout > {limit} s" + (f" ({reason})" if reason else "")
    if status == "memory":
        return f"memory > {state.get('memory_limit_mb', 8192) / 1024:g} GB"
    return f"{status}: {reason}" if reason else status


def chosen_size(data, case, mode):
    """The largest size at which most configurations finished (else the size where the most did), with the
    numbers that finished and that were recorded."""
    configs = [c for c in data["configs"] if c[:2] == (case, mode)]
    finished = {n: sum(c + (n,) in data["medians"] for c in configs) for n in sizes(data, case, mode)}
    most = [n for n, count in finished.items() if 2 * count > len(configs)]
    n = max(most) if most else max(finished, key=lambda n: (finished[n], n))
    return n, finished[n], len(configs)


def growth(data, config):
    """The exponent k of t ∝ n^k between the two largest sizes that finished, with those sizes."""
    done = [(n, data["medians"][config + (n,)]["total_ms"]) for n in sizes(data, *config[:2])
            if config + (n,) in data["medians"]]
    if len(done) < 2:
        return None
    (n1, t1), (n2, t2) = done[-2:]
    return math.log(t2 / t1) / math.log(n2 / n1), n1, n2


# Formatting

def fmt_ms(ms):
    """A time with three significant digits, e.g. 0.06 ms, 50.6 ms, 560 ms, 1.52 s, 22.5 s."""
    if ms >= 999.5:
        value, unit = ms / 1000, "s"
    else:
        value, unit = ms, "ms"
    digits = 0 if value >= 99.95 else 1 if value >= 9.995 else 2
    return f"{value:.{digits}f} {unit}"


def fmt_mb(mb):
    return f"{mb / 1024:.2f} GB" if mb >= 1000 else f"{mb:.0f} MB"


def text_width(s, size, bold=False):
    return sum(WIDTHS.get(c, 600) for c in s) * size / 1000 * (1.1 if bold else 1.04)


def clip(s, size, width):
    """`s`, cut with an ellipsis to fit `width`."""
    if text_width(s, size) <= width:
        return s
    while s and text_width(s + "…", size) > width:
        s = s[:-1]
    return s + "…"


def nice_ticks(low, high, count=5):
    """Round ticks from at most `low` to at least `high`, about `count` steps apart."""
    if high <= low:
        high = low + 1
    raw = (high - low) / count
    magnitude = 10 ** math.floor(math.log10(raw))
    step = next(m * magnitude for m in (1, 2, 2.5, 5, 10) if m * magnitude >= raw * 0.999)
    start = math.floor(low / step + 1e-9) * step
    return [start + i * step for i in range(int(math.ceil((high - start) / step - 1e-9)) + 1)]


def time_tick(ms, seconds):
    if ms == 0:
        return "0"
    return f"{ms / 1000:g} s" if seconds else f"{ms:g} ms"


def log_ticks(low, high):
    """Ticks between `low` and `high` (in ms) on a log scale: decades, and 2× and 5× where they are few."""
    decades = [10 ** e for e in range(math.floor(math.log10(low)), math.ceil(math.log10(high)) + 1)]
    ticks = [t for t in decades if low <= t <= high]
    if len(ticks) < 3:
        ticks = sorted(t * m for t in decades for m in (1, 2, 5) if low <= t * m <= high)
    return ticks


def log_label(ms):
    return f"{ms / 1000:g} s" if ms >= 1000 else f"{ms:g} ms"


# SVG

def esc(value):
    return html.escape(str(value), quote=True)


def text(x, y, content, size=11, fill=INK2, anchor="start", weight=None):
    weight = f' font-weight="{weight}"' if weight else ""
    anchor = f' text-anchor="{anchor}"' if anchor != "start" else ""
    return f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" fill="{fill}"{anchor}{weight}>{esc(content)}</text>'


def line(x1, y1, x2, y2, stroke=GRID, width=1, extra=""):
    return (f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{stroke}" '
            f'stroke-width="{width}"{extra}/>')


def bar(x, y, w, h, fill, left=0, right=0):
    """A rectangle whose left and right ends are rounded with the given radii."""
    left, right = min(left, w / 2, h / 2), min(right, w / 2, h / 2)
    if not left and not right:
        return f'<rect x="{x:.2f}" y="{y:.1f}" width="{w:.2f}" height="{h}" fill="{fill}"/>'
    d = f"M{x + left:.2f},{y:.1f} H{x + w - right:.2f} "
    d += (f"A{right:.2f},{right:.2f} 0 0 1 {x + w:.2f},{y + right:.2f} V{y + h - right:.2f} "
          f"A{right:.2f},{right:.2f} 0 0 1 {x + w - right:.2f},{y + h:.1f} " if right else f"V{y + h:.1f} ")
    d += f"H{x + left:.2f} "
    d += (f"A{left:.2f},{left:.2f} 0 0 1 {x:.2f},{y + h - left:.2f} V{y + left:.2f} "
          f"A{left:.2f},{left:.2f} 0 0 1 {x + left:.2f},{y:.1f} " if left else f"V{y:.1f} ")
    return f'<path d="{d}Z" fill="{fill}"/>'


def pieces(parts, y, h, gap=2, round_left=0, round_right=4):
    """Touching segments [(x0, x1, fill)] separated by surface gaps; the outer ends rounded."""
    parts = [p for p in parts if p[1] - p[0] >= 0.3]
    out = []
    for i, (x0, x1, fill) in enumerate(parts):
        last = i == len(parts) - 1
        x1 -= 0 if last else min(gap, (x1 - x0) / 2)
        out.append(bar(x0, y, x1 - x0, h, fill, round_left if i == 0 else 0, round_right if last else 0))
    return out


def hatch(uid):
    return (f'<pattern id="{uid}" width="4" height="4" patternUnits="userSpaceOnUse" '
            f'patternTransform="rotate(45)"><rect width="4" height="4" fill="#ecebe6"/>'
            f'<line x1="0" y1="0" x2="0" y2="4" stroke="{OTHER}" stroke-width="1.6"/></pattern>')


def glyph(kind, x, y, fill=INK2, size=4):
    """A failure mark centered at (x, y): a cross for a timeout, a triangle for memory, else a diamond."""
    s = size
    if kind == "timeout":
        return (f'<path d="M{x - s:.1f},{y - s:.1f} L{x + s:.1f},{y + s:.1f} M{x - s:.1f},{y + s:.1f} '
                f'L{x + s:.1f},{y - s:.1f}" stroke="{fill}" stroke-width="2" stroke-linecap="round"/>')
    if kind == "memory":
        return (f'<path d="M{x:.1f},{y - s - 0.5:.1f} L{x + s + 0.5:.1f},{y + s:.1f} L{x - s - 0.5:.1f},{y + s:.1f} Z" '
                f'fill="{fill}" stroke="{SURFACE}" stroke-width="1"/>')
    return (f'<path d="M{x:.1f},{y - s - 0.5:.1f} L{x + s + 0.5:.1f},{y:.1f} L{x:.1f},{y + s + 0.5:.1f} '
            f'L{x - s - 0.5:.1f},{y:.1f} Z" fill="{fill}" stroke="{SURFACE}" stroke-width="1"/>')


def swatch(x, y, fill):
    return f'<rect x="{x:.1f}" y="{y - 9:.1f}" width="11" height="11" rx="2" fill="{fill}"/>'


def legend(x, y, items, max_x, lead=None):
    """Legend entries [(draw(x, y) -> svg, label)] in rows from (x, y), after a `lead` text if given;
    returns the svg and the last y."""
    out, start = [], x
    if lead:
        out.append(text(x, y, lead, 11, INK2, weight=600))
        x += text_width(lead, 11, True) + 12
    for draw, label in items:
        width = 16 + text_width(label, 11) + 18
        if x + width > max_x and x > start:
            x, y = start, y + 18
        out.append(draw(x, y))
        out.append(text(x + 16, y, label, 11, INK2))
        x += width
    return out, y


def document(width, height, body, label):
    style = (".hit{fill:#0b0b0b;fill-opacity:0}.row:hover .hit{fill-opacity:.045}"
             ".series:hover .trace{stroke-width:3}text{font-variant-numeric:tabular-nums}")
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{width:.0f}" height="{height:.0f}" '
            f'viewBox="0 0 {width:.0f} {height:.0f}" role="img" aria-label="{esc(label)}" '
            f'font-family="{esc(FONT)}"><style>{style}</style>'
            f'<rect width="{width:.0f}" height="{height:.0f}" fill="{SURFACE}"/>\n' + "\n".join(body) + "\n</svg>\n")


def wrap_words(content, size, width):
    """`content` broken into lines at spaces to fit `width`."""
    lines = []
    for word in content.split(" "):
        if lines and text_width(lines[-1] + " " + word, size) <= width:
            lines[-1] += " " + word
        else:
            lines.append(word)
    return lines


def title_block(title, paragraphs, width):
    """A title and its paragraphs, wrapped; returns the svg and the baseline of the last line."""
    out = [text(16, 26, title, 15, INK, weight=600)]
    lines = [part for paragraph in paragraphs for part in wrap_words(paragraph, 12, width - 32)]
    for i, content in enumerate(lines):
        out.append(text(16, 46 + 17 * i, content, 12, INK2))
    return out, 46 + 17 * len(lines)


def row_labels(configs, top, row_height, route_gap=4, family_gap=12):
    """The y of each configuration's row, with gaps between routes and wider ones between families."""
    rows, y, previous = [], top, None
    for config in configs:
        route = config[2]
        if previous is not None and route != previous:
            y += family_gap if family(route) != family(previous) else route_gap
        rows.append((y, config, route != previous))
        y += row_height
        previous = route
    return rows, y


def label_columns(configs):
    """The widths of the route and tier label columns."""
    route_w = max([text_width(c[2], 12, True) for c in configs] + [40]) + 14
    tier_w = max([text_width(c[3], 11.5) for c in configs] + [40]) + 16
    return route_w, tier_w


def config_labels(x, y, config, first, route_w):
    """A row's route (on the first row of its route) and tier."""
    out = [text(x, y, config[2], 12, INK, weight=600)] if first else []
    out.append(text(x + route_w, y, "–" if config[3] == "-" else config[3], 11.5, INK2))
    return out


def details(data, config, n, status, payload):
    """A configuration's tooltip at size n."""
    case, mode, route, tier = config
    head = f"{route} · {tier}" if tier != "-" else route
    head += f" — {case}, {MODES.get(mode, mode).lower()}, n = {n}"
    if status != "ok":
        return f"{head}\n{failure_text(data, status, payload)}"
    row = payload
    lines = [head, f"Total {fmt_ms(row['total_ms'])}" +
             (f"; + one-time {fmt_ms(row['one_time_ms'])} = {fmt_ms(row['total_ms'] + row['one_time_ms'])}"
              if "one_time_ms" in row else "")]
    phases = [f"{label} {fmt_ms(row[key + '_ms'])}" for key, label, _ in PHASES if key + "_ms" in row]
    if "instantiate_ms" in row:
        phases.append(f"Instantiate {fmt_ms(row['instantiate_ms'])}")
    lines.append(" · ".join(phases))
    lines.append(f"{row['vc_count']} VC{'s' if row['vc_count'] != 1 else ''}" +
                 (f" · peak {fmt_mb(row['peak_mb'])}" if "peak_mb" in row else ""))
    return "\n".join(lines)


# Figures

def breakdown_svg(data, case, mode, n, uid):
    """One bar per configuration at size n: its median phases on a linear axis, with a strip of their
    shares; failed configurations get a labeled row."""
    configs = [c for c in data["configs"] if c[:2] == (case, mode)]
    phases = data["phases"]
    width = 1000
    route_w, tier_w = label_columns(configs)
    x0 = 16
    x_bar = x0 + route_w + tier_w
    strip_w = 140
    x_strip = width - 16 - strip_w
    bar_w = x_strip - 72 - x_bar
    outcomes = {c: outcome(data, c, n) for c in configs}
    ok = {c: row for c, (status, row) in outcomes.items() if status == "ok"}
    count = len(ok)
    where = ""
    if n == data["chosen"][(case, mode)][0]:
        where = ", the largest size" if n == max(sizes(data, case, mode)) else \
            ", the largest size at which most finished" if 2 * count > len(configs) else \
            ", the size at which the most finished"
    title = f"{case} · {MODES.get(mode, mode).lower()} · n = {n}"
    lines = [f"{count} of {len(configs)} route·tier configurations finished at n = {n}{where}.",
             "Bars: median time of each phase over the runs, on this panel's linear axis. "
             "Strip: each phase's share of the total."]
    body, y = title_block(title, lines, width)
    one_time = any("one_time_ms" in row for row in ok.values())
    other = "Other (Total − these; incl. Share)" if not any(p[0] == "share" for p in phases) else \
        "Other (Total − these)"
    items = [(lambda x, y, c=color: swatch(x, y, c), label) for _, label, color in phases]
    items.append((lambda x, y: swatch(x, y, OTHER), other))
    if one_time:
        items.append((lambda x, y: swatch(x, y, f"url(#{uid}-hatch)"), "one-time cost, not per run"))
    parts, y = legend(16, y + 10, items, width - 16)
    body += parts
    top = y + 26
    body.append(text(x_bar, top - 8, "median time per run", 10.5, MUTED))
    body.append(text(x_strip, top - 8, "share of total", 10.5, MUTED))
    rows, bottom = row_labels(configs, top, 22)
    high = max([row["total_ms"] + row.get("one_time_ms", 0) for row in ok.values()] + [1])
    ticks = nice_ticks(0, high)
    scale = bar_w / ticks[-1]
    seconds = ticks[-1] >= 2000
    defs = [f"<defs>{hatch(uid + '-hatch')}</defs>"]
    grid = []
    for tick in ticks:
        x = x_bar + tick * scale
        grid.append(line(x, top - 2, x, bottom + 2, GRID if tick else AXIS))
        grid.append(text(x, bottom + 16, time_tick(tick, seconds), 10.5, MUTED, "middle"))
    for frac in (0, 0.5, 1):
        grid.append(text(x_strip + frac * strip_w, bottom + 16, f"{frac:.0%}", 10.5, MUTED,
                         ["start", "middle", "end"][int(frac * 2)]))
    marks = []
    for y, config, first in rows:
        status, payload = outcomes[config]
        g = ['<g class="row">', f'<rect class="hit" x="8" y="{y - 1}" width="{width - 16}" height="22"/>']
        g += config_labels(x0, y + 15, config, first, route_w)
        if status == "ok":
            row = payload
            spans, x = [], x_bar
            for *_, color, ms in segments(row, phases):
                spans.append((x, x + ms * scale, color))
                x += ms * scale
            end = x
            if row.get("one_time_ms"):
                end = x + row["one_time_ms"] * scale
                spans.append((x, end, f"url(#{uid}-hatch)"))
            g += pieces(spans, y + 4, 14)
            g.append(text(max(end, x_bar + 2) + 6, y + 15, fmt_ms(row["total_ms"]), 11, INK))
            total = row["total_ms"]
            shares, x = [], x_strip
            for *_, color, ms in segments(row, phases):
                shares.append((x, x + ms / total * strip_w, color))
                x += ms / total * strip_w
            g += pieces(shares, y + 7, 8, round_left=4)
        else:
            kind = payload["status"] if status == "skipped" and payload else status
            if kind not in UNFINISHED:
                g.append(glyph(kind, x_bar + 6, y + 11, INK2, 3.5))
            g.append(text(x_bar + 16, y + 15, clip(failure_text(data, status, payload), 11.5, width - x_bar - 40),
                          11.5, INK2))
        g.append(f"<title>{esc(details(data, config, n, status, payload))}</title></g>")
        marks += g
    body = defs + body + grid + marks
    return document(width, bottom + 30, body, title)


def segments(row, phases):
    """(key, label, color, ms) of a median row's phases, then the rest of its total. Medians of the parts
    need not add up to the median total; where they exceed it, they are scaled down to fit."""
    parts = [(key, label, color, row.get(key + "_ms", 0.0)) for key, label, color in phases]
    shown = sum(part[3] for part in parts)
    total = row["total_ms"]
    if shown > total:
        return [(key, label, color, ms * total / shown) for key, label, color, ms in parts] + \
            [("other", "Other", OTHER, 0.0)]
    return parts + [("other", "Other", OTHER, total - shown)]


def grid_svg(data, mode, kind):
    """Total time (kind "time", log–log) or peak memory ("memory") against n: a row per case with shared
    axes, a column per route, a line per tier, and the case's other routes in gray."""
    state = data["state"]
    key = "total_ms" if kind == "time" else "peak_mb"
    configs = [c for c in data["configs"] if c[1] == mode]
    if kind == "memory":
        configs = [c for c in configs if any(key in data["medians"].get(c + (n,), {})
                                              for n in sizes(data, c[0], mode))]
    if not configs:
        return None
    routes = [route for route in data["routes"] if any(c[2] == route for c in configs)]
    tiers = list(dict.fromkeys(t for t in TIERS + list(data["tier_colors"]) if any(c[3] == t for c in configs)))
    column_gap, left, plot_h, band_h = 16, 72, 92, 13
    # Narrower columns where there are many routes, to keep the figure about 1240 wide.
    column_w = max(100, min(124, (1240 - left - 16 - (len(routes) - 1) * column_gap) // len(routes)))
    right = left + len(routes) * (column_w + column_gap) - column_gap
    width = max(right + 16, 760)
    baseline = state.get("baseline_mb")
    limit = (1000 * state.get("timeout_seconds", state.get("process_timeout_seconds", 60)) if kind == "time"
             else state.get("memory_limit_mb"))
    rows = [row for row in (grid_axes(data, case, mode, [c for c in configs if c[0] == case], key, kind, baseline)
                            for case in data["cases"]) if row]
    if not rows:
        return None
    if kind == "time":
        title = f"Total time against n · {MODES.get(mode, mode).lower()}"
        lines = ["Median total time per run on log–log axes, shared within each row (case). Colored: the "
                 "column's route by tier; gray: the case's other routes.",
                 "Slope 1 is linear growth and 2 quadratic, as in the guide at the right of each row. "
                 "Failures are marked above the plot at the size where they happened."]
    else:
        title = f"Peak memory against n · {MODES.get(mode, mode).lower()}"
        lines = ["Median peak resident memory of the Lean process, imports and the audits after the timers "
                 "included, on a linear axis shared within each row (case). Colored: the column's route by "
                 "tier; gray: the case's other routes."]
    body, y = title_block(title, lines, width)
    untiered = ", ".join(r for r in routes if any(c[2:] == (r, "-") for c in configs))
    items = [(lambda x, y, c=data["tier_colors"][t]: series_key(x, y, c),
              f"no tier ({untiered})" if t == "-" else t) for t in tiers]
    items.append((lambda x, y: line(x, y - 4, x + 12, y - 4, CONTEXT, 1.5), "other routes"))
    if limit and any(row["low"] <= scale(limit, kind) <= row["high"] for row in rows):
        items.append((lambda x, y: line(x, y - 4, x + 12, y - 4, MUTED, 1.2),
                      f"{limit / 1000:g} s time limit" if kind == "time" else f"{fmt_mb(limit)} memory limit"))
    if kind == "memory" and baseline and any(row["low"] <= baseline <= row["high"] for row in rows):
        items.append((lambda x, y: line(x, y - 4, x + 12, y - 4, INK2, 1.5),
                      f"a process that only imports the benchmark ({fmt_mb(baseline)})"))
    statuses = {outcome(data, c, n)[0] for c in configs for n in sizes(data, c[0], mode)}
    for status in order([s for s in statuses if s not in UNFINISHED + ("ok", "skipped")],
                        ["timeout", "memory", "error"]):
        items.append((lambda x, y, s=status: glyph(s, x + 6, y - 4, INK2, 3.5),
                      {"memory": "over memory"}.get(status, status)))
    parts, y = legend(16, y + 10, items, width - 16)
    body += parts
    y += 26
    for row in rows:
        ns, case_configs, low, high = row["sizes"], row["configs"], row["low"], row["high"]
        xlo, xhi = row["x"]

        def px(n, x0):
            return x0 + (math.log10(n) - xlo) / (xhi - xlo) * column_w

        def py(v, top):
            return top + plot_h - (scale(v, kind) - low) / (high - low) * plot_h

        body.append(text(16, y + 14, row["case"], 13, INK, weight=600))
        if kind == "time":
            body += slope_key(right, y + 18, column_w / (xhi - xlo), plot_h / (high - low))
        band = y + 40
        top = band + band_h + 4
        if row["failures"]:
            body.append(text(left - 8, band + 10, "failed", 10, MUTED, "end"))
        for label, value in row["ticks"]:
            body.append(text(left - 8, py(value, top) + 3.5, label, 10, MUTED, "end"))
        for j, route in enumerate(routes):
            x0 = left + j * (column_w + column_gap)
            mine = [c for c in case_configs if c[2] == route]
            if not mine:
                continue
            body.append(text(x0, y + 33, route, 11, INK2, weight=500))
            if row["failures"]:
                body.append(f'<rect x="{x0}" y="{band}" width="{column_w}" height="{band_h}" rx="2" fill="{BAND}"/>')
            for _, value in row["ticks"]:
                body.append(line(x0, py(value, top), x0 + column_w, py(value, top), GRID))
            for n in ns:
                body.append(line(px(n, x0), top, px(n, x0), top + plot_h, GRID, 1, ' stroke-opacity="0.6"'))
            if limit and low <= scale(limit, kind) <= high:
                body.append(line(x0, py(limit, top), x0 + column_w, py(limit, top), MUTED, 1.2))
            if kind == "memory" and baseline and low <= baseline <= high:
                body.append(line(x0, py(baseline, top), x0 + column_w, py(baseline, top), INK2, 1.5))
            body.append(line(x0, top + plot_h, x0 + column_w, top + plot_h, AXIS))
            for other in case_configs:
                points = [(px(n, x0), py(data["medians"][other + (n,)][key], top)) for n in ns
                          if key in data["medians"].get(other + (n,), {})]
                if other[2] != route and len(points) > 1:
                    body.append(polyline(points, CONTEXT, 1.2))
            for i, config in enumerate(mine):
                color = data["tier_colors"].get(config[3], INK2)
                body += series(data, config, ns, key, kind, color, px, py, x0, top, band + band_h / 2,
                               (i - (len(mine) - 1) / 2) * 9)
            for x, label in tick_positions([px(n, x0) for n in ns], [str(n) for n in ns], 9.5):
                body.append(text(x, top + plot_h + 13, label, 9.5, MUTED, "middle"))
        y = top + plot_h + 34
    return document(width, y - 8, body, title)


def scale(value, kind):
    """A value on a grid's vertical scale: log10 of a time, a memory as it is."""
    return math.log10(value) if kind == "time" else value


def grid_axes(data, case, mode, configs, key, kind, baseline):
    """A grid row's sizes, configurations, horizontal (log n) and vertical domains, and labeled ticks."""
    ns = sizes(data, case, mode)
    values = [data["medians"][c + (n,)][key] for c in configs for n in ns if key in data["medians"].get(c + (n,), {})]
    if not values:
        return None
    xlo, xhi = math.log10(min(ns)), math.log10(max(ns))
    pad = max(0.07 * (xhi - xlo), 0.05)
    if kind == "time":
        low, high = math.log10(min(values)), math.log10(max(values))
        spread = max(high - low, 0.6)
        middle = (low + high) / 2
        low, high = middle - 0.58 * spread, middle + 0.58 * spread
        ticks = [(log_label(t), t) for t in log_ticks(10 ** low, 10 ** high)]
    else:
        gb = [v / 1024 for v in values + ([baseline] if baseline else [])]
        pad_gb = max(0.06 * (max(gb) - min(gb)), 0.02)
        steps = nice_ticks(min(gb) - pad_gb, max(gb) + pad_gb, 4)
        digits = next(d for d in range(4) if all(abs(t * 10 ** d - round(t * 10 ** d)) < 1e-6 for t in steps))
        ticks = [(f"{t:.{digits}f} GB", t * 1024) for t in steps]
        low, high = steps[0] * 1024, steps[-1] * 1024
    failures = any(outcome(data, c, n)[0] not in UNFINISHED + ("ok",) for c in configs for n in ns)
    return dict(case=case, sizes=ns, configs=configs, x=(xlo - pad, xhi + pad), low=low, high=high, ticks=ticks,
                failures=failures)


def series_key(x, y, color):
    return line(x, y - 4, x + 14, y - 4, color, 2) + \
        f'<circle cx="{x + 7}" cy="{y - 4}" r="3.2" fill="{color}" stroke="{SURFACE}" stroke-width="1.5"/>'


def polyline(points, stroke, width, extra=""):
    coords = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    return (f'<polyline points="{coords}" fill="none" stroke="{stroke}" stroke-width="{width}" '
            f'stroke-linejoin="round" stroke-linecap="round"{extra}/>')


def series(data, config, ns, key, kind, color, px, py, x0, top, band_y, offset):
    """A configuration's line, its points, and its failure marked in the band, with a tooltip."""
    points, tips, failure = [], [], None
    for n in ns:
        status, payload = outcome(data, config, n)
        if status == "ok" and key in payload:
            points.append((n, payload[key]))
            tips.append(f"n = {n}: " + (fmt_ms(payload[key]) if kind == "time" else fmt_mb(payload[key])))
        elif status not in UNFINISHED + ("ok", "skipped") and failure is None:
            failure = (n, status, payload)
            tips.append(f"n = {n}: {failure_text(data, status, payload)}")
    head = f"{config[2]} · {config[3]}" if config[3] != "-" else config[2]
    head += f" — {config[0]}"
    if kind == "time":
        rate = growth(data, config)
        if rate:
            tips.append(f"grows like n^{rate[0]:.2f} between n = {rate[1]} and {rate[2]}")
    out = ['<g class="series">']
    xy = [(px(n, x0), py(v, top)) for n, v in points]
    if len(xy) > 1:
        out.append(polyline(xy, color, 2, ' class="trace"'))
    if failure:
        fx = px(failure[0], x0) + offset
        if xy:
            out.append(polyline([xy[-1], (fx, band_y + 5)], color, 1.3, ' stroke-dasharray="1.5 2.5"'))
        out.append(glyph(failure[1], fx, band_y, color, 3.5))
    for x, y in xy:
        out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.2" fill="{color}" stroke="{SURFACE}" stroke-width="1.5"/>')
    out.append(f"<title>{esc(head)}\n" + esc("\n".join(tips)) + "</title></g>")
    return out


def tick_positions(xs, labels, size):
    """The labels that fit side by side, keeping the first and the last."""
    if not xs:
        return []
    keep = [0, len(xs) - 1] if len(xs) > 1 else [0]
    chosen = []
    for i in keep + list(range(1, len(xs) - 1)):
        half = text_width(labels[i], size) / 2 + 2
        if all(abs(xs[i] - xs[j]) >= half + text_width(labels[j], size) / 2 + 2 for j in chosen):
            chosen.append(i)
    return [(xs[i], labels[i]) for i in sorted(chosen)]


def slope_key(right, base, per_decade_x, per_decade_y):
    """Two short lines at slopes 1 and 2 on a row's log–log scales, rising from `base` to the left of
    `right`."""
    ratio = per_decade_y / per_decade_x
    run_x = min(56, 13 / ratio)
    rise = ratio * run_x
    # Keep the two labels apart where the lines end close together.
    spread = max(0, 11 - rise) / 2
    x0 = right - run_x - 30
    out = [text(x0 - 8, base, "slopes", 10, MUTED, "end")]
    for k, label, shift in [(1, "n", spread), (2, "n²", -spread)]:
        out.append(line(x0, base, x0 + run_x, base - k * rise, MUTED, 1.4, ' stroke-linecap="round"'))
        out.append(text(x0 + run_x + 4, base - k * rise + 4 + shift, label, 10, MUTED))
    return out


def scoreboard_svg(data, columns, cell, bins, lead, title, lines):
    """A heatmap with a row per configuration and a column per (mode, case, subheading): cell(config) gives
    (bin value or None, text, bold, tooltip); `lead` introduces the bins' legend."""
    present = {c for c in data["configs"] for mode, case, _ in columns if c[:2] == (case, mode)}
    rows_order = []
    for route in data["routes"]:
        for tier in list(dict.fromkeys(TIERS + list(data["tier_colors"]))):
            if any(c[2:] == (route, tier) for c in present):
                rows_order.append(("", "", route, tier))
    route_w, tier_w = label_columns(rows_order)
    cell_w, cell_h, group_gap = 90, 22, 14
    x_cells = 16 + route_w + tier_w
    groups = list(dict.fromkeys(mode for mode, _, _ in columns))
    xs, x = [], x_cells
    for i, (mode, case, _) in enumerate(columns):
        if i and columns[i - 1][0] != mode:
            x += group_gap
        xs.append(x)
        x += cell_w + 2
    width = max(x + 14, 760)
    body, y = title_block(title, lines, width)
    items = [(lambda x, y, c=fill: swatch(x, y, c), label) for _, label, fill, _ in bins]
    parts, y = legend(16, y + 10, items, width - 16, lead)
    body += parts
    y += 28
    for mode in groups:
        first = next(i for i, c in enumerate(columns) if c[0] == mode)
        body.append(text(xs[first], y, MODES.get(mode, mode), 12, INK, weight=600))
    head = y + 18
    names = [split_name(case, 11, cell_w) for _, case, _ in columns]
    lines_needed = max(len(name) for name in names)
    for i, (mode, case, sub) in enumerate(columns):
        for k, part in enumerate(names[i]):
            body.append(text(xs[i] + cell_w / 2, head + 14 * k, part, 11, INK, "middle", 500))
        body.append(text(xs[i] + cell_w / 2, head + 14 * lines_needed, sub, 10, MUTED, "middle"))
    top = head + 14 * lines_needed + 10
    rows, bottom = row_labels(rows_order, top, cell_h + 2)
    for y, config, first in rows:
        body += config_labels(16, y + 15, config, first, route_w)
        for i, (mode, case, _) in enumerate(columns):
            full = (case, mode) + config[2:]
            if full not in present:
                continue
            value, label, bold, tip = cell(full)
            g = ['<g class="row">']
            if value is None:
                g.append(f'<rect x="{xs[i]:.1f}" y="{y}" width="{cell_w}" height="{cell_h}" rx="3" fill="{BAND}"/>')
                g.append(text(xs[i] + cell_w / 2, y + 15, clip(label, 10, cell_w - 6), 10, INK2, "middle"))
            else:
                _, _, fill, ink = next(b for b in bins if value <= b[0])
                g.append(f'<rect x="{xs[i]:.1f}" y="{y}" width="{cell_w}" height="{cell_h}" rx="3" fill="{fill}"/>')
                g.append(text(xs[i] + cell_w / 2, y + 15, label, 11, ink, "middle", 700 if bold else None))
            g.append(f'<rect class="hit" x="{xs[i]:.1f}" y="{y}" width="{cell_w}" height="{cell_h}" rx="3"/>')
            g.append(f"<title>{esc(tip)}</title></g>")
            body += g
    return document(width, bottom + 16, body, title)


def split_name(name, size, width):
    """A name in at most two lines, split before a capital letter if it is too wide for one."""
    if text_width(name, size, True) <= width - 6:
        return [name]
    cuts = [i for i in range(1, len(name)) if name[i].isupper() and text_width(name[:i], size, True) <= width - 6]
    if not cuts:
        return [clip(name, size, width - 6)]
    i = cuts[-1]
    return [name[:i], clip(name[i:], size, width - 6)]


def time_board(data, columns):
    """Total time at each case's chosen size, colored by its slowdown against the fastest in the column."""
    fastest = {}
    for mode, case, _ in columns:
        n = data["chosen"][(case, mode)][0]
        totals = [data["medians"][c + (n,)]["total_ms"] for c in data["configs"]
                  if c[:2] == (case, mode) and c + (n,) in data["medians"]]
        fastest[(case, mode)] = min(totals) if totals else None

    def cell(config):
        case, mode = config[:2]
        n = data["chosen"][(case, mode)][0]
        status, payload = outcome(data, config, n)
        tip = details(data, config, n, status, payload)
        if status != "ok":
            short = failure_text(data, status, payload, short=True)
            return None, short if status in UNFINISHED else "× " + short, False, tip
        ratio = payload["total_ms"] / fastest[(case, mode)]
        tip += f"\n{ratio:.2f}× the fastest at this size"
        return ratio, fmt_ms(payload["total_ms"]), ratio == 1, tip
    return cell


def growth_board(data):
    """The growth exponent of each configuration's total time."""
    def cell(config):
        rate = growth(data, config)
        ns = sizes(data, *config[:2])
        outcomes = [f"n = {n}: " + (fmt_ms(data["medians"][config + (n,)]["total_ms"])
                                    if config + (n,) in data["medians"] else
                                    failure_text(data, *outcome(data, config, n)))
                    for n in ns]
        head = f"{config[2]} · {config[3]}" if config[3] != "-" else config[2]
        head += f" — {config[0]}, {MODES.get(config[1], config[1]).lower()}"
        if rate is None:
            return None, "–", False, head + "\nfewer than two sizes finished\n" + "\n".join(outcomes)
        tip = f"{head}\ngrows like n^{rate[0]:.2f} between n = {rate[1]} and {rate[2]}\n" + "\n".join(outcomes)
        return rate[0], f"{rate[0]:.2f}", False, tip
    return cell


# Index

def index_html(data, sections):
    """A self-contained page with every figure: sections of (anchor, heading, paragraph, figures), where each
    figure is (file, svg, subheading, None or (summary, [(file, svg)]) for figures folded under it)."""
    state = data["state"]
    failures = sum(1 for records in data["statuses"].values() for s in records
                   if s["status"] not in ("ok", SKIPPED))
    limit = state.get("timeout_seconds", state.get("process_timeout_seconds", 60))
    facts = [esc(public(state.get("lean", ""))),
             f"{len(state['runs'])} successful samples, {len(data['medians'])} medians of "
             f"{state['repetitions']} fresh single-threaded processes each, {failures} failed samples",
             f"limits: {limit} s per measurement, {state.get('memory_limit_mb', 8192) / 1024:g} GB of memory"]
    nav = " ".join(f'<a href="#{anchor}">{esc(heading)}</a>' for anchor, heading, _, _ in sections)
    parts = []
    for anchor, heading, paragraph, figures in sections:
        parts.append(f'<h2 id="{anchor}">{esc(heading)}</h2>\n<p>{paragraph}</p>')
        for _, svg, sub, extra in figures:
            if sub:
                parts.append(f"<h3>{esc(sub)}</h3>")
            parts.append(f"<figure>{svg}</figure>")
            if extra:
                summary, more = extra
                inner = "".join(f"<figure>{s}</figure>" for _, s in more)
                parts.append(f"<details><summary>{esc(summary)}</summary>{inner}</details>")
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>VCGen comparison figures</title>
<style>
:root {{ color-scheme: light; }}
body {{ margin: 0; background: {PAGE}; color: {INK}; font: 15px/1.5 {FONT}; }}
main {{ max-width: 1280px; margin: 0 auto; padding: 24px 16px 64px; }}
h1 {{ font-size: 24px; margin: 0 0 6px; }}
h2 {{ font-size: 19px; margin: 44px 0 4px; }}
h3 {{ font-size: 15px; margin: 22px 0 4px; }}
p, li {{ color: {INK2}; max-width: 90ch; }}
p {{ margin: 4px 0 12px; }}
ul {{ margin: 6px 0 12px; padding-left: 20px; font-size: 14px; }}
nav {{ display: flex; flex-wrap: wrap; gap: 6px 18px; font-size: 14px; }}
a {{ color: #256abf; }}
figure {{ margin: 10px 0 18px; padding: 12px; background: {SURFACE}; border: 1px solid rgba(11,11,11,0.10);
  border-radius: 10px; overflow-x: auto; }}
figure svg {{ display: block; max-width: 100%; height: auto; min-width: 640px; }}
details {{ margin: 0 0 18px; }}
summary {{ cursor: pointer; color: {INK2}; font-size: 14px; }}
</style>
</head>
<body>
<main>
<h1>vcgen versus specification normalization</h1>
<ul>{"".join(f"<li>{fact}</li>" for fact in facts)}</ul>
<p>Hover a bar, cell, or line for its numbers.</p>
<nav>{nav}</nav>
{chr(10).join(parts)}
</main>
</body>
</html>
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--name", default=run.NAME,
                        help=f"the run to draw, in results/NAME/ as run.py names it (default {run.NAME})")
    parser.add_argument("--results", type=Path, help="draw this results.json instead")
    parser.add_argument("--out", type=Path, help="where to write the figures (default: figures/ next to the results)")
    args = parser.parse_args()
    results = (args.results or FOLDER / "results" / args.name / "results.json").resolve()
    if not results.is_file():
        raise SystemExit(f"{results} does not exist; name a run with --name, or give a results.json with --results")
    out = (args.out or results.parent / "figures").resolve()
    data = load(results)
    if not data["configs"]:
        raise SystemExit(f"{results} records no measurements yet")
    out.mkdir(parents=True, exist_ok=True)
    pairs = [(case, mode) for mode in data["modes"] for case in data["cases"]
             if any(c[:2] == (case, mode) for c in data["configs"])]
    data["chosen"] = {pair: chosen_size(data, *pair) for pair in pairs}
    written = []

    def save(name, svg):
        check(name, svg)
        (out / name).write_text(svg, encoding="utf-8")
        written.append(name)
        return name, svg

    columns = [(mode, case, f"n = {data['chosen'][(case, mode)][0]}") for case, mode in pairs]
    boards = [save("scoreboard-time.svg", scoreboard_svg(
        data, columns, time_board(data, columns), SLOWDOWN, "slowdown against the fastest",
        "Total time at each case's largest common size",
        ["Median total time per run at the largest n at which most route·tiers finished. The fastest in "
         "each column is bold, and the color is each cell's slowdown against it.",
         "× marks a failure at this size, or with @n at the smaller size n, after which larger sizes were "
         "skipped; hover for the reason."])) + ("", None)]
    growth_columns = [(mode, case, f"n ≤ {max(sizes(data, case, mode))}") for case, mode in pairs]
    boards.append(save("scoreboard-growth.svg", scoreboard_svg(
        data, growth_columns, growth_board(data), GROWTH, "exponent k",
        "How total time grows with n",
        ["The exponent k of total time ∝ n^k between the two largest sizes that finished: 1 is linear, "
         "2 quadratic. Fixed costs make small sizes look slower than linear.",
         "– : fewer than two sizes finished. Hover for every size's time or failure."])) + ("", None))
    sections = [("overview", "At a glance", "Two scoreboards over every case: how fast each route·tier is at a "
                 "size most of them reach, and how its time grows with n.", boards)]
    for mode in data["modes"]:
        figures = []
        for case, m in pairs:
            if m != mode:
                continue
            n = data["chosen"][(case, mode)][0]
            stem = f"breakdown-{mode}-{case}"
            main_figure = save(f"{stem}-n{n}.svg", breakdown_svg(data, case, mode, n, f"{stem}-n{n}"))
            others = [save(f"{stem}-n{k}.svg", breakdown_svg(data, case, mode, k, f"{stem}-n{k}"))
                      for k in sizes(data, case, mode) if k != n]
            extra = (f"{case} at the other sizes: " + ", ".join(f"n = {k}" for k in sizes(data, case, mode)
                                                                 if k != n), others) if others else None
            figures.append(main_figure + ("", extra))
        phases = ", ".join(label for _, label, _ in data["phases"])
        rest = "mostly Instantiate" if any(p[0] == "share" for p in data["phases"]) else \
            "Instantiate and Share, which this run did not time separately"
        sections.append((f"breakdown-{mode}", f"Where the time goes · {MODES.get(mode, mode).lower()}",
                         f"One bar per route·tier at each case's largest common size: the median of each phase "
                         f"({phases}; Other is the rest of Total, {rest}) on the panel's own linear axis. "
                         "Routes with a one-time cost add it, hatched. The strip on the right shows "
                         "each phase's share of the total, which stays readable for fast routes. Other sizes "
                         "are under each panel.", figures))
    for kind, heading, paragraph in [
            ("time", "Scaling with n", "Total time against n, one row per case and one column per route. "
             "Straight lines on log–log axes are power laws; their slope is the exponent of the scoreboard above."),
            ("memory", "Peak memory", "Peak resident memory against n; the dark line is the import-only "
             "baseline. Only runs that record peak memory are drawn.")]:
        figures = []
        for mode in data["modes"]:
            svg = grid_svg(data, mode, kind)
            if svg:
                figures.append(save(f"{kind}-{mode}.svg", svg) + (MODES.get(mode, mode), None))
        if figures:
            sections.append((kind, heading, paragraph, figures))
    page = index_html(data, sections)
    check("index.html", page)
    (out / "index.html").write_text(page, encoding="utf-8")
    print(f"Wrote {len(written)} figures and index.html to {out}")


if __name__ == "__main__":
    main()
