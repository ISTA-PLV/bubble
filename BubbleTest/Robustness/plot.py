#!/usr/bin/env python3
"""Plot the deferred-versus-eager context-splitting benchmark.

Usage:
    plot.py [--out FIG.png] <dir> [<dir> ...]

Every ``results.jsonl`` below the input directories is loaded. Later inputs
override earlier measurements with the same
``(tactic, propositions, seed, shuffle)``.
Runtime summaries include only completed successful tactics. Failed groups
are marked by red dots at the budget, never treated as completed runtimes.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402


LABELS = {
    "ibubble": "ibubble",
    "inaive": "inaive (Aesop + enum)",
}
COLORS = {"ibubble": "#2980b9", "inaive": "#c0392b"}


def load(directories: list[Path]) -> tuple[
        dict[str, dict[int, list[tuple[int, int, bool, float]]]], float, float]:
    records: dict[tuple[str, int, int, int], tuple[bool, float]] = {}
    densities = set()
    protocols = set()
    for directory in directories:
        for results in sorted(directory.rglob("results.jsonl")):
            for line in results.read_text().splitlines():
                if not line.strip():
                    continue
                record = json.loads(line)
                reported = record.get("reportedTimeMs")
                seconds = record.get("tacticSeconds")
                if seconds is None:
                    seconds = reported / 1000 if reported is not None else record.get("wallSeconds")
                if seconds is None:
                    continue
                tactic = record.get("tactic", "ibubble")
                densities.add(record["density"])
                protocols.add((record.get("schemaVersion", 0),
                               record.get("timeoutScope", "process"),
                               record.get("timeoutSeconds")))
                records[(tactic, record["propositions"], record["seed"],
                         record.get("shuffle", 0))] = (
                             record["status"] == "success", seconds)
    if len(densities) != 1:
        raise SystemExit(
            "expected exactly one density; pass directories from one experiment "
            f"(found {sorted(densities)})")
    if len(protocols) != 1:
        raise SystemExit("Refusing to combine different protocols/configurations in one plot")

    grouped: dict[
        str, dict[int, list[tuple[int, int, bool, float]]]
    ] = defaultdict(
        lambda: defaultdict(list))
    for (tactic, size, seed, shuffle), (ok, seconds) in records.items():
        grouped[tactic][size].append((seed, shuffle, ok, seconds))
    _, _, budget = next(iter(protocols))
    if budget is None or budget <= 0:
        raise SystemExit("A positive timeoutSeconds is required to locate failure markers")
    return grouped, densities.pop(), budget


def statistics(rows: list[tuple[int, int, bool, float]]) -> dict[str, object]:
    times = np.array([seconds for _, _, _, seconds in rows])
    ok = np.array([success for _, _, success, _ in rows])
    return {
        "n": len(rows),
        "times": times,
        "ok": ok,
        "median": np.median(times[ok]) if ok.any() else np.nan,
        "p25": np.percentile(times[ok], 25) if ok.any() else np.nan,
        "p75": np.percentile(times[ok], 75) if ok.any() else np.nan,
        "failures": int((~ok).sum()),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="+", type=Path)
    parser.add_argument("--override", action="append", type=Path, default=[],
                        help="results whose duplicate records replace earlier ones")
    parser.add_argument("--out", type=Path, default=Path("architecture_comparison.png"))
    parser.add_argument("--title", default=None,
                        help="optional title; omitted by default")
    parser.add_argument("--min-seeds", type=int, default=2,
                        help="skip tactic/size groups with fewer samples")
    args = parser.parse_args()

    grouped, _, budget = load(args.directories + args.override)
    prepared: dict[str, dict[int, dict[str, object]]] = {}
    for tactic, by_size in grouped.items():
        prepared[tactic] = {
            size: statistics(rows) for size, rows in by_size.items()
            if len(rows) >= args.min_seeds
        }
    prepared = {tactic: rows for tactic, rows in prepared.items() if rows}
    if not prepared:
        raise SystemExit("no tactic/size group has enough samples")

    fig, runtime_ax = plt.subplots(figsize=(7.6, 4.8))
    fallback_colors = plt.rcParams["axes.prop_cycle"].by_key()["color"]
    tactics = sorted(prepared, key=lambda tactic: (tactic != "ibubble", tactic))
    rng = np.random.default_rng(1)
    failure_points = []

    for tactic_index, tactic in enumerate(tactics):
        by_size = prepared[tactic]
        sizes = sorted(by_size)
        x = np.array(sizes)
        color = COLORS.get(tactic, fallback_colors[tactic_index % len(fallback_colors)])
        label = LABELS.get(tactic, tactic)
        offset = (tactic_index - (len(tactics) - 1) / 2) * 0.24

        for size in sizes:
            stat = by_size[size]
            times = stat["times"]
            ok = stat["ok"]
            jitter = rng.uniform(-0.32, 0.32, size=stat["n"]) + offset
            runtime_ax.scatter(size + jitter[ok], times[ok], s=7, color=color,
                               alpha=0.20, linewidths=0, zorder=1)
            if stat["failures"]:
                failure_points.append((size + offset, stat["failures"], stat["n"], tactic))

        median = np.array([by_size[size]["median"] for size in sizes])
        p25 = np.array([by_size[size]["p25"] for size in sizes])
        p75 = np.array([by_size[size]["p75"] for size in sizes])
        runtime_ax.fill_between(x, p25, p75, color=color, alpha=0.13, linewidth=0)
        runtime_ax.plot(x, median, color=color, linewidth=2, marker="o",
                        markersize=3.5, label=label)

    runtime_ax.axhline(budget, color="#9a9a9a", linestyle="--", linewidth=1, zorder=0)
    runtime_ax.text(0.995, budget, f"{budget:g}s limit", color="#666666", fontsize=8,
                    transform=runtime_ax.get_yaxis_transform(), ha="right", va="bottom")
    if failure_points:
        runtime_ax.scatter([point[0] for point in failure_points],
                           [budget] * len(failure_points), s=32, color="#c0392b",
                           zorder=5, label="failed (at limit)")
        for xpos, count, total, _ in failure_points:
            runtime_ax.annotate(f"{count}/{total}", (xpos, budget), xytext=(0, 9),
                                textcoords="offset points", ha="center",
                                color="#c0392b", fontsize=8)

    all_sizes = sorted({size for by_size in prepared.values() for size in by_size})
    runtime_ax.set_yscale("log")
    runtime_ax.set_ylabel("successful runtime (s, log scale)")
    if args.title:
        runtime_ax.set_title(args.title, fontsize=10.5)
    successful = [seconds for by_size in grouped.values() for rows in by_size.values()
                  for _, _, ok, seconds in rows if ok]
    runtime_ax.set_ylim(min(successful, default=budget / 100) / 1.35,
                        max([budget, *successful]) * 1.7)
    runtime_ax.grid(True, which="major", alpha=0.3)
    runtime_ax.grid(True, which="minor", alpha=0.12)
    runtime_ax.legend(loc="upper left", fontsize=8.5, frameon=True,
                      framealpha=1, facecolor="white", edgecolor="none")
    runtime_ax.set_xlabel("propositions (P and Q atoms)")
    runtime_ax.set_xticks(all_sizes if len(all_sizes) <= 25 else all_sizes[::2])

    target = args.out.with_suffix(".png")
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, dpi=200, bbox_inches="tight")
    plt.close(fig)
    print(f"wrote {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
