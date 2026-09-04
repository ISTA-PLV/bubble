#!/usr/bin/env python3
"""Run the ibubble robustness sweep: one Lean process per (size, seed) case.

Each case is a triangular resource-contention instance from ``generate.py``,
elaborated in its own process so that per-case time and failures are isolated.
Records are appended to ``<out>/results.jsonl``; cases already recorded there
are skipped, so an interrupted run can simply be restarted.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import signal
import statistics
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from generate import build_case, parse_density, recommended_max_depth, render_lean

REPO = Path(__file__).resolve().parent.parent.parent
MAX_REC_DEPTH = 10_000
REPORTED_TIME = re.compile(r"^time: ([0-9.]+)(ms|s)$", re.MULTILINE)


def parse_int_list(value: str) -> list[int]:
    return [int(x) for x in value.split(",") if x.strip()]


def parse_seed_range(value: str) -> list[int]:
    """'100-399' or a comma-separated list."""
    if "-" in value:
        low, high = value.split("-", 1)
        return list(range(int(low), int(high) + 1))
    return parse_int_list(value)


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sizes", type=parse_int_list, required=True,
                        help="proposition counts, comma separated")
    parser.add_argument("--seeds", type=parse_seed_range, required=True,
                        help="'100-399' or a comma-separated list")
    parser.add_argument("--density", type=parse_density, default=0.2)
    parser.add_argument("--workers", type=int, default=4,
                        help="parallel Lean processes (each is single-threaded)")
    parser.add_argument("--timeout", type=float, default=1800.0, help="per case, seconds")
    parser.add_argument("--max-heartbeats", type=int, default=2_000_000)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--csv", type=Path, help="also write the per-case table here")
    return parser


def _status(output: str, timed_out: bool, return_code: int | None) -> str:
    if timed_out:
        return "process_timeout"
    if "maximum number of heartbeats" in output:
        return "heartbeat_timeout"
    if "error:" in output or return_code != 0:
        return "lean_error"
    return "success"


def _reported_time_ms(output: str) -> float | None:
    match = REPORTED_TIME.search(output)
    if match is None:
        return None
    value = float(match.group(1))
    return value * 1000 if match.group(2) == "s" else value


def run_case(size: int, seed: int, args: argparse.Namespace) -> dict[str, object]:
    case = build_case(propositions=size, density=args.density, seed=seed,
                      shuffle_resources=True, shuffle_targets=True)
    max_depth = recommended_max_depth(case)
    source = render_lean(case, max_heartbeats=args.max_heartbeats,
                         max_depth=max_depth, max_rec_depth=MAX_REC_DEPTH)
    lean_path = args.out / f"case_p{size}_s{seed}.lean"
    lean_path.write_text(source, encoding="utf-8")

    # -DElab.async=false is essential: without it `#time` measures the theorem
    # header rather than the tactic.
    command = ["lake", "env", "lean", "-DElab.async=false",
               f"-DmaxRecDepth={MAX_REC_DEPTH}", str(lean_path.resolve())]
    # Own process group, so a timeout kills the whole `lake` -> `lean` tree rather
    # than just `lake`, which would leave `lean` running and skew concurrent cases.
    # Output goes to a file because a full pipe buffer would deadlock the wait.
    output_path = args.out / f"case_p{size}_s{seed}.out"
    started = time.perf_counter()
    with output_path.open("w", encoding="utf-8") as handle:
        process = subprocess.Popen(command, cwd=REPO, stdout=handle,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            return_code, timed_out = process.wait(timeout=args.timeout), False
        except subprocess.TimeoutExpired:
            return_code, timed_out = None, True
            try:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
    wall = time.perf_counter() - started
    output = output_path.read_text(encoding="utf-8", errors="replace")
    output_path.unlink()

    return {
        "propositions": size,
        "seed": seed,
        "density": args.density,
        "pairs": case.pairs,
        "conflicts": len(case.conflicts),
        "maxHeartbeats": args.max_heartbeats,
        "maxDepth": max_depth,
        "timeoutSeconds": args.timeout,
        "status": _status(output, timed_out, return_code),
        "reportedTimeMs": _reported_time_ms(output),
        "wallSeconds": wall,
    }


def load(directory: Path) -> dict[tuple[int, int], tuple[float, str, float]]:
    """(size, seed) -> (density, status, seconds) for every record under `directory`.

    Searched recursively, so a directory of sub-runs merges as readily as a
    single `results.jsonl`; later files win for the same (size, seed).
    """
    records: dict[tuple[int, int], tuple[float, str, float]] = {}
    for results in sorted(directory.rglob("results.jsonl")):
        for line in results.read_text().splitlines():
            if not line.strip():
                continue
            record = json.loads(line)
            reported = record.get("reportedTimeMs")
            seconds = reported / 1000 if reported else record.get("wallSeconds")
            if seconds is None:
                continue
            records[(record["propositions"], record["seed"])] = (
                record["density"], record["status"], seconds)
    return records


def summarize(records: dict[tuple[int, int], tuple[float, str, float]],
              csv_path: Path | None = None) -> None:
    """Print a per-size markdown table; timed-out cases enter at their abort time."""
    by_size: dict[int, list[tuple[int, float, str, float]]] = {}
    for (size, seed), (density, status, seconds) in records.items():
        by_size.setdefault(size, []).append((seed, density, status, seconds))

    print("\n| props | n | timeouts | mean | median | p25 | p75 | p90 | min | max |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for size, rows in sorted(by_size.items()):
        times = sorted(seconds for *_, seconds in rows)
        timeouts = sum(1 for *_, status, _ in rows if status != "success")
        # "inclusive" is the linear interpolation numpy's percentile uses.
        cuts = (statistics.quantiles(times, n=100, method="inclusive")
                if len(times) > 1 else times * 99)
        print(f"| {size} | {len(rows)} | {timeouts} ({100 * timeouts / len(rows):.0f}%) "
              f"| {statistics.mean(times):.1f} | {statistics.median(times):.1f} "
              f"| {cuts[24]:.1f} | {cuts[74]:.1f} | {cuts[89]:.1f} "
              f"| {times[0]:.1f} | {times[-1]:.1f} |")
    print("\nTimes in seconds (`#time` of the `ibubble` command, or wall time for process "
          "timeouts). Timed-out cases enter the statistics with their abort time, a lower "
          "bound.")

    if csv_path is not None:
        with csv_path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.writer(handle)
            writer.writerow(["propositions", "density", "seed", "status", "time_s"])
            for size, rows in sorted(by_size.items()):
                for seed, density, status, seconds in sorted(rows):
                    writer.writerow([size, density, seed, status, f"{seconds:.3f}"])
        print(f"wrote {csv_path}")


def main(argv: list[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    args.out.mkdir(parents=True, exist_ok=True)
    results_path = args.out / "results.jsonl"

    # Seed-major order keeps the per-size sample counts balanced if interrupted.
    done = set(load(args.out))
    cases = [(size, seed) for seed in args.seeds for size in args.sizes
             if (size, seed) not in done]
    print(f"{len(cases)} cases to run ({len(done)} already done), {args.workers} workers, "
          f"timeout {args.timeout:.0f}s, maxHeartbeats {args.max_heartbeats}", flush=True)

    started = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run_case, size, seed, args) for size, seed in cases]
        for finished, future in enumerate(as_completed(futures), start=1):
            record = future.result()
            # Written from this thread only, so no lock is needed.
            with results_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(record) + "\n")
            eta = (time.perf_counter() - started) / finished * (len(cases) - finished)
            print(f"[{finished}/{len(cases)} eta {eta / 3600:.1f}h] "
                  f"p{record['propositions']} seed {record['seed']} {record['status']:18s} "
                  f"time={record['reportedTimeMs']} ms wall={record['wallSeconds']:.1f}s",
                  flush=True)

    summarize(load(args.out), args.csv)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
