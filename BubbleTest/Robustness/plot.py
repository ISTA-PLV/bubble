#!/usr/bin/env python3
"""Plot ibubble runtime versus proposition count from sweep/overnight results.

Usage:
    uv run --with matplotlib --with numpy plot.py [--out FIG.pdf] <dir> [<dir> ...]

Reads every results.jsonl under the given directories (all seeds, one density).
Produces a runtime figure, plus a timeout panel when timeouts are present:
  top    - runtime vs. propositions (log scale): median with interquartile band,
           p90, mean with a bootstrap 95% CI, and the per-case scatter;
  bottom - fraction of instances that hit the heartbeat / process limit.
Timed-out cases enter every statistic at their abort time (a lower bound), and
are drawn as open markers.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402


def load(directories: list[Path]) -> dict[int, list[tuple[int, bool, float]]]:
    """Later directories override earlier ones for the same (propositions, seed)."""
    records: dict[tuple[int, int], tuple[bool, float]] = {}
    densities = set()
    for directory in directories:
        for results in sorted(directory.rglob("results.jsonl")):
            for line in results.read_text().splitlines():
                if not line.strip():
                    continue
                record = json.loads(line)
                reported = record.get("reportedTimeMs")
                seconds = reported / 1000 if reported else record.get("wallSeconds")
                if seconds is None:
                    continue
                densities.add(record["density"])
                records[(record["propositions"], record["seed"])] = (
                    record["status"] == "success", seconds)
    by_size: dict[int, list[tuple[int, bool, float]]] = defaultdict(list)
    for (size, seed), (ok, seconds) in records.items():
        by_size[size].append((seed, ok, seconds))
    if len(densities) > 1:
        raise SystemExit(f"mixed densities {sorted(densities)}; pass one density's directories")
    return by_size


def bootstrap_mean_ci(values: np.ndarray, iterations: int = 4000, seed: int = 0) -> tuple[float, float]:
    rng = np.random.default_rng(seed)
    means = rng.choice(values, size=(iterations, values.size), replace=True).mean(axis=1)
    return float(np.percentile(means, 2.5)), float(np.percentile(means, 97.5))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="+", type=Path)
    parser.add_argument("--override", action="append", type=Path, default=[],
                        help="results dir whose records replace same (size, seed), e.g. re-runs")
    parser.add_argument("--out", type=Path, default=Path("runtime_vs_propositions.pdf"))
    parser.add_argument("--title", default="ibubble on the triangular resource-contention benchmark")
    parser.add_argument("--min-seeds", type=int, default=2,
                        help="skip sizes with fewer samples than this")
    args = parser.parse_args()

    by_size = load(args.directories + args.override)
    sizes = sorted(size for size, rows in by_size.items() if len(rows) >= args.min_seeds)
    if not sizes:
        raise SystemExit("no size has enough samples")

    stats = {}
    for size in sizes:
        rows = by_size[size]
        times = np.array([t for _, _, t in rows])
        ok = np.array([s for _, s, _ in rows])
        lo, hi = bootstrap_mean_ci(times)
        stats[size] = {
            "n": len(rows), "times": times, "ok": ok,
            "mean": times.mean(), "ci": (lo, hi),
            "median": np.median(times), "p25": np.percentile(times, 25),
            "p75": np.percentile(times, 75), "p90": np.percentile(times, 90),
            "timeout_rate": 1 - ok.mean(),
        }

    x = np.array(sizes)
    has_timeouts = any(not stats[size]["ok"].all() for size in sizes)
    if has_timeouts:
        fig, (ax, ax_to) = plt.subplots(
            2, 1, figsize=(7.5, 6.5), sharex=True,
            gridspec_kw={"height_ratios": [3.2, 1], "hspace": 0.08})
    else:
        fig, ax = plt.subplots(figsize=(7.5, 5.1))
        ax_to = None

    # Scatter of every case; successes filled, timeouts open.
    rng = np.random.default_rng(1)
    for size in sizes:
        s = stats[size]
        jitter = rng.uniform(-0.45, 0.45, size=s["n"])
        ax.scatter(size + jitter[s["ok"]], s["times"][s["ok"]], s=7, color="0.6", alpha=0.35,
                   linewidths=0, zorder=1)
        ax.scatter(size + jitter[~s["ok"]], s["times"][~s["ok"]], s=14, facecolors="none",
                   edgecolors="#c0392b", alpha=0.8, linewidths=0.7, zorder=2)

    median = np.array([stats[s]["median"] for s in sizes])
    p25 = np.array([stats[s]["p25"] for s in sizes])
    p75 = np.array([stats[s]["p75"] for s in sizes])
    p90 = np.array([stats[s]["p90"] for s in sizes])
    mean = np.array([stats[s]["mean"] for s in sizes])
    ci_lo = np.array([stats[s]["ci"][0] for s in sizes])
    ci_hi = np.array([stats[s]["ci"][1] for s in sizes])

    ax.fill_between(x, p25, p75, color="#2980b9", alpha=0.18, linewidth=0, label="interquartile range")
    ax.plot(x, median, color="#2980b9", linewidth=2, marker="o", markersize=3.5, label="median")
    ax.plot(x, p90, color="#8e44ad", linewidth=1.2, linestyle="--", marker="^", markersize=3.5,
            label="90th percentile")
    ax.errorbar(x, mean, yerr=[mean - ci_lo, ci_hi - mean], color="#e67e22", linewidth=1.5,
                marker="s", markersize=3.5, capsize=2, label="mean (bootstrap 95% CI)")

    ax.set_yscale("log")
    ax.set_ylabel("ibubble time (s, log scale)")
    ax.grid(True, which="major", alpha=0.3)
    ax.grid(True, which="minor", alpha=0.12)
    n_seeds = sorted({stats[s]["n"] for s in sizes})
    n_label = f"{n_seeds[0]}" if len(n_seeds) == 1 else f"{n_seeds[0]}–{n_seeds[-1]}"
    ax.set_title(f"{args.title}\n{n_label} random instances per size (density 0.2)", fontsize=10.5)
    ax.legend(loc="upper left", fontsize=8.5, frameon=False)
    if has_timeouts:
        ax.text(0.99, 0.02, "open red markers: timed out (heartbeat / process limit);\n"
                "their abort time is a lower bound and is included in all statistics",
                transform=ax.transAxes, ha="right", va="bottom", fontsize=7.5,
                color="#c0392b")

        timeout_rate = np.array([stats[s]["timeout_rate"] for s in sizes]) * 100
        ax_to.bar(x, timeout_rate, width=1.4, color="#c0392b", alpha=0.75)
        ax_to.set_ylabel("timed out (%)")
        ax_to.set_ylim(0, max(5, timeout_rate.max() * 1.15))
        ax_to.set_xlabel("propositions (P and Q atoms)")
        ax_to.grid(True, axis="y", alpha=0.3)
        ax_to.set_xticks(x if len(x) <= 25 else x[::2])
    else:
        ax.set_xlabel("propositions (P and Q atoms)")
        ax.set_xticks(x if len(x) <= 25 else x[::2])

    for suffix in {args.out.suffix or ".pdf", ".png"}:
        target = args.out.with_suffix(suffix)
        fig.savefig(target, dpi=200, bbox_inches="tight")
        print(f"wrote {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
