"""Draws the charts of `docs/speed.json` and prints the tables of the README's Speed section.

Every number is a rate (higher is better): commands per second are the inverse of the median
time of the runs, replies per second the mean of the runs.
"""

import json
import math
import statistics
import sys
from pathlib import Path

DOCS = Path(__file__).resolve().parent.parent / "docs"
COLORS = ["#4477aa", "#ee6677", "#228833", "#ccbb44", "#66ccee", "#aa3377"]
STYLE = (
    "text{font-family:system-ui,sans-serif;font-size:12px;fill:#24292f}"
    ".title{font-size:14px;font-weight:600}.grid{stroke:#d0d7de}.axis{fill:#57606a}"
    "@media(prefers-color-scheme:dark){text{fill:#e6edf3}.grid{stroke:#30363d}.axis{fill:#8b949e}}"
)


def rate(value: float) -> str:
    if value >= 1e6:
        return f"{value / 1e6:.3g} M"
    if value >= 1e4:
        return f"{round(value, -2):,.0f}"
    return f"{float(f'{value:.3g}'):,.0f}"


def chart(
    title: str,
    unit: str,
    groups: list[str],
    series: dict[str, list[float | None]],
    log: bool,
) -> str:
    left, top, bar, gap = 150, 64 + 18 * len(series), 14, 16
    width, plot = 860, 600
    values = [v for row in series.values() for v in row if v is not None]
    if log:
        low, high = (
            math.floor(math.log10(min(values))),
            math.ceil(math.log10(max(values))),
        )
        ticks = [10.0**e for e in range(low, high + 1)]

        def x(v: float) -> float:
            return (math.log10(v) - low) / (high - low) * plot
    else:
        step = 10 ** math.floor(math.log10(max(values)))
        step = step / 2 if max(values) / step < 3 else step
        ticks = [step * i for i in range(int(max(values) / step) + 2)]

        def x(v: float) -> float:
            return v / ticks[-1] * plot

    out = [f'<text class="title" x="{left}" y="20">{title}</text>']
    for i, name in enumerate(series):
        y = 34 + 18 * i
        out.append(
            f'<rect x="{left}" y="{y}" width="12" height="12" fill="{COLORS[i]}"/>'
        )
        out.append(f'<text x="{left + 18}" y="{y + 10}">{name}</text>')
    y = top
    body = []
    for g, group in enumerate(groups):
        start = y
        for i, row in enumerate(series.values()):
            if row[g] is None:
                continue
            w = max(x(row[g]), 1)
            body.append(
                f'<rect x="{left}" y="{y}" width="{w:.1f}" height="{bar}" fill="{COLORS[i]}"/>'
            )
            body.append(
                f'<text x="{left + w + 6:.1f}" y="{y + 11}">{rate(row[g])}</text>'
            )
            y += bar + 3
        body.append(
            f'<text x="{left - 10}" y="{(start + y) / 2 + 2:.0f}" text-anchor="end">{group}</text>'
        )
        y += gap
    bottom = y - gap + 6
    for tick in ticks:
        tx = left + x(tick)
        out.append(
            f'<line class="grid" x1="{tx:.1f}" y1="{top - 6}" x2="{tx:.1f}" y2="{bottom}"/>'
        )
        out.append(
            f'<text class="axis" x="{tx:.1f}" y="{bottom + 16}" text-anchor="middle">{rate(tick)}</text>'
        )
    scale = ", logarithmic scale" if log else ""
    out.append(
        f'<text class="axis" x="{left}" y="{bottom + 36}">{unit}{scale}; higher is better</text>'
    )
    height = bottom + 48
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" width="{width}" height="{height}" role="img">'
        f"<title>{title}</title><style>{STYLE}</style>{''.join(out)}{''.join(body)}</svg>\n"
    )


def table(corner: str, groups: list[str], series: dict[str, list[float | None]]) -> str:
    lines = [
        f"| {corner} | " + " | ".join(groups) + " |",
        "|---|" + "---:|" * len(groups),
    ]
    for name, row in series.items():
        lines.append(
            f"| {name} | "
            + " | ".join("" if v is None else rate(v) for v in row)
            + " |"
        )
    return "\n".join(lines)


def main() -> None:
    data = json.loads((DOCS / "speed.json").read_text())
    sizes = ["1", "100", "1000", "10000"]
    engine = {
        name: [1e9 / statistics.median(runs[s]) if s in runs else None for s in sizes]
        for name, runs in data["engine_ns_per_command"].items()
    }
    users = [f"{int(s):,} user{'s' if s != '1' else ''}" for s in sizes]
    cases = list(next(iter(data["http_replies_per_second"].values())))
    http = {
        name: [statistics.mean(runs[c]) for c in cases]
        for name, runs in data["http_replies_per_second"].items()
    }
    (DOCS / "speed-engine.svg").write_text(
        chart(
            "One command, by the number of users in the tenant",
            "Commands per second",
            users,
            engine,
            True,
        )
    )
    (DOCS / "speed-http.svg").write_text(
        chart("POST /rpc over HTTP", "Replies per second", cases, http, False)
    )
    sys.stdout.write(
        table("Commands per second", users, engine)
        + "\n\n"
        + table("Replies per second", cases, http)
        + "\n"
    )


if __name__ == "__main__":
    main()
