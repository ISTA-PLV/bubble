#!/usr/bin/env python3
"""Compare context-splitting architectures on the robustness sweep.

Each case is a triangular resource-contention instance from ``generate.py``.
Every base seed is rendered under several complete presentation shuffles and
elaborated once per tactic in its own process, isolating time and failures.
Records are appended to ``<out>/results.jsonl``; cases already recorded there
are skipped, so an interrupted run can simply be restarted.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import signal
import statistics
import subprocess
import tempfile
import threading
import time
from concurrent.futures import CancelledError, ThreadPoolExecutor, as_completed
from pathlib import Path

from generate import TACTICS, build_case, case_metadata, parse_density, recommended_max_depth, render_lean

REPO = Path(__file__).resolve().parent.parent.parent
MAX_REC_DEPTH = 10_000
REPORTED_TIME = re.compile(r"^time: ([0-9.]+)(ms|s)$", re.MULTILINE)
TACTIC_END = re.compile(r"^ROBUSTNESS_END (\d+) (\d+)$", re.MULTILINE)
SEQ_STATS = re.compile(r"^IOSEQ_STATS (\d+) (\d+) (\d+) (\d+)$", re.MULTILINE)
SEQ_PHASES = re.compile(r"^IOSEQ_PHASES (\d+) (\d+) (\d+)$", re.MULTILINE)
STOP = threading.Event()
PROCESS_LOCK = threading.Lock()
PROCESSES: set[subprocess.Popen] = set()
ARCHITECTURES = {
    "ibubble": "deferred_context_splitting",
    "inaive": "aesop_proofmode_eager_partition_enumeration",
}
DEFAULT_IBUBBLE_SIZES = list(range(4, 31, 2))
DEFAULT_INAIVE_SIZES = list(range(4, 17, 2))
DEFAULT_SEEDS = list(range(3000, 3005))
DEFAULT_SHUFFLES = 5
DEFAULT_WALL_TIMEOUT_SECONDS = 10.0


def parse_int_list(value: str) -> list[int]:
    return [int(x) for x in value.split(",") if x.strip()]


def parse_seed_range(value: str) -> list[int]:
    """'100-399' or a comma-separated list."""
    if "-" in value:
        low, high = value.split("-", 1)
        return list(range(int(low), int(high) + 1))
    return parse_int_list(value)


def parse_tactics(value: str) -> list[str]:
    tactics = [tactic.strip() for tactic in value.split(",") if tactic.strip()]
    unknown = sorted(set(tactics) - set(TACTICS))
    if unknown:
        raise argparse.ArgumentTypeError(
            f"unknown tactic(s) {', '.join(unknown)}; choose from {', '.join(TACTICS)}"
        )
    if not tactics:
        raise argparse.ArgumentTypeError("at least one tactic is required")
    return list(dict.fromkeys(tactics))


def build_argument_parser() -> argparse.ArgumentParser:
    script_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sizes", type=parse_int_list,
                        help="override both tactic-specific size ranges")
    parser.add_argument("--ibubble-sizes", type=parse_int_list,
                        default=DEFAULT_IBUBBLE_SIZES,
                        help="ibubble proposition counts (default: 4,6,...,30)")
    parser.add_argument("--inaive-sizes", type=parse_int_list,
                        default=DEFAULT_INAIVE_SIZES,
                        help="inaive proposition counts (default: 4,6,...,16)")
    parser.add_argument("--seeds", type=parse_seed_range, default=DEFAULT_SEEDS,
                        help="inclusive range or comma-separated list "
                             "(default: 3000-3004)")
    parser.add_argument("--shuffles", type=int, default=DEFAULT_SHUFFLES,
                        help="complete shuffles per base instance (default: 5)")
    parser.add_argument("--tactics", type=parse_tactics, default=list(TACTICS),
                        help="comma-separated architectures "
                             "(default: ibubble,inaive)")
    parser.add_argument("--density", type=parse_density, default=0.2)
    parser.add_argument("--workers", type=int, default=1,
                        help="parallel Lean processes (each is single-threaded)")
    parser.add_argument("--timeout", type=float, default=DEFAULT_WALL_TIMEOUT_SECONDS,
                        help="deadline in seconds (default: 10)")
    parser.add_argument("--timeout-scope", choices=["tactic", "process"],
                        default="tactic", help="time limit boundary (default: tactic)")
    parser.add_argument("--startup-timeout", type=float, default=30.0)
    parser.add_argument("--check-timeout", type=float, default=10.0)
    parser.add_argument("--order-seed", type=int, default=20260909,
                        help="reproducible balanced tactic-order rotation")
    parser.add_argument("--max-heartbeats", type=int, default=2_000_000)
    parser.add_argument("--out", type=Path,
                        default=script_dir / "result",
                        help="result directory (default: result)")
    parser.add_argument("--csv", type=Path, help="also write the per-case table here")
    return parser


def _status(output: str, timed_out: bool, return_code: int | None) -> str:
    if timed_out:
        return "process_timeout"
    if "maximum number of heartbeats" in output:
        return "heartbeat_timeout"
    if "iseq: no resource allocation" in output:
        return "search_exhausted"
    if "error:" in output or return_code != 0:
        return "lean_error"
    return "success"


def _reported_time_ms(output: str) -> float | None:
    match = REPORTED_TIME.search(output)
    if match is None:
        return None
    value = float(match.group(1))
    return value * 1000 if match.group(2) == "s" else value


def kill_process(process: subprocess.Popen) -> None:
    """Only signal the private process group created for this exact case."""
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


def cancel_running() -> None:
    STOP.set()
    with PROCESS_LOCK:
        for process in tuple(PROCESSES):
            kill_process(process)


def wait_case(process: subprocess.Popen, output_path: Path,
              args: argparse.Namespace, started: float,
              timing_path: Path | None = None) -> tuple[int | None, str | None]:
    """Poll flushed markers. Deadline resolution is 20 ms; accept completed
    tactics only if their internal elapsed time is also within the exact limit.
    Imports and final declaration checking have separate safety watchdogs.
    """
    tactic_started = None
    checking_started = None
    while True:
        if STOP.is_set():
            kill_process(process)
            raise CancelledError()
        output = (timing_path or output_path).read_text(encoding="utf-8", errors="replace")
        now = time.perf_counter()
        if tactic_started is None and "ROBUSTNESS_START\n" in output:
            tactic_started = now
        if checking_started is None and TACTIC_END.search(output):
            checking_started = now
        code = process.poll()
        if code is not None:
            return code, None
        if args.timeout_scope == "process":
            expired = now - started >= args.timeout
            reason = "process_timeout"
        elif checking_started is not None:
            expired = now - checking_started >= args.check_timeout
            reason = "check_timeout"
        elif tactic_started is not None:
            expired = now - tactic_started >= args.timeout
            reason = "tactic_timeout"
        else:
            expired = now - started >= args.startup_timeout
            reason = "startup_timeout"
        if expired:
            kill_process(process)
            return None, reason
        STOP.wait(0.02)


def run_case(tactic: str, size: int, seed: int, shuffle: int,
             args: argparse.Namespace) -> dict[str, object]:
    # Inputs and timer/log sidecars are disposable; the JSONL keeps measurements,
    # reproducible input metadata, source hashes, and diagnostics for failures.
    with tempfile.TemporaryDirectory(prefix="bubble-case-") as directory:
        return _run_case(tactic, size, seed, shuffle, args, Path(directory))


def _run_case(tactic: str, size: int, seed: int, shuffle: int,
              args: argparse.Namespace, work_dir: Path) -> dict[str, object]:
    case = build_case(propositions=size, density=args.density, seed=seed,
                      shuffle=shuffle)
    max_depth = recommended_max_depth(case)
    source = render_lean(case, tactic=tactic, max_heartbeats=args.max_heartbeats,
                         max_depth=max_depth, max_rec_depth=MAX_REC_DEPTH)
    lean_path = work_dir / f"case_{tactic}_p{size}_s{seed}_r{shuffle}.lean"
    lean_path.write_text(source, encoding="utf-8")

    # -DElab.async=false is essential: without it `#time` measures the theorem
    # header rather than the tactic.
    command = ["lake", "env", "lean", "-DElab.async=false",
               f"-DmaxRecDepth={MAX_REC_DEPTH}", str(lean_path.resolve())]
    # Own process group, so a timeout kills the whole `lake` -> `lean` tree rather
    # than just `lake`, which would leave `lean` running and skew concurrent cases.
    # Output goes to a file because a full pipe buffer would deadlock the wait.
    output_path = work_dir / f"case_{tactic}_p{size}_s{seed}_r{shuffle}.out"
    timing_path = output_path.with_suffix(".timing")
    timing_path.write_text("")
    environment = dict(os.environ, BUBBLE_ROBUSTNESS_MARKERS=str(timing_path.resolve()))
    started = time.perf_counter()
    with output_path.open("w", encoding="utf-8") as handle:
        with PROCESS_LOCK:
            if STOP.is_set():
                raise CancelledError()
            process = subprocess.Popen(command, cwd=REPO, stdout=handle,
                                       stderr=subprocess.STDOUT, start_new_session=True,
                                       env=environment)
            PROCESSES.add(process)
        try:
            return_code, timeout_reason = wait_case(process, output_path, args, started, timing_path)
        finally:
            with PROCESS_LOCK:
                kill_process(process)
                PROCESSES.discard(process)
    wall = time.perf_counter() - started
    output = output_path.read_text(encoding="utf-8", errors="replace")
    markers = timing_path.read_text()
    timing = TACTIC_END.search(markers)
    stats = SEQ_STATS.findall(markers)
    phases = SEQ_PHASES.search(markers)
    tactic_seconds = int(timing.group(1)) / 1e9 if timing else None
    status = timeout_reason or _status(output, False, return_code)
    if status == "success" and not timing:
        status = "instrumentation_error"
    if status == "success" and "declaration uses 'sorry'" in output:
        status = "invalid_proof"
    if status == "success" and args.timeout_scope == "tactic" and tactic_seconds > args.timeout:
        status = "tactic_timeout"
    if status == "success" and args.timeout_scope == "process" and wall > args.timeout:
        status = "process_timeout"

    return {
        "tactic": tactic,
        "architecture": ARCHITECTURES[tactic],
        "propositions": size,
        "seed": seed,
        "shuffle": shuffle,
        "density": args.density,
        "pairs": case.pairs,
        "conflicts": len(case.conflicts),
        "maxHeartbeats": args.max_heartbeats,
        "maxDepth": max_depth,
        "timeoutSeconds": args.timeout,
        "timeoutScope": args.timeout_scope,
        "schemaVersion": 6,
        "caseMetadata": case_metadata(case),
        "sourceSha256": hashlib.sha256(source.encode()).hexdigest(),
        "status": status,
        "tacticSeconds": tactic_seconds,
        "tacticHeartbeatsRaw": int(timing.group(2)) if timing else None,
        "reportedTimeMs": _reported_time_ms(output),
        "wallSeconds": wall,
        "returnCode": return_code,
        "outputFile": None,
        "timingFile": None,
        "diagnosticOutput": output if status != "success" else None,
        "sequentialStats": dict(zip(["nodes", "choices", "backtracks", "candidateChecks"],
                                     map(int, stats[-1]))) if stats else None,
        "sequentialStatsComplete": phases is not None or status == "search_exhausted",
        "sequentialPhasesSeconds": dict(zip(["prepare", "search", "replay"],
                                            [int(x) / 1e9 for x in phases.groups()])) if phases else None,
    }


def load(directory: Path) -> dict[tuple[str, int, int, int], tuple[float, str, float]]:
    """(tactic, size, seed, shuffle) -> measurements under `directory`.

    Searched recursively, so a directory of sub-runs merges as readily as a
    single `results.jsonl`; later files win for the same key. Legacy records
    without tactic or shuffle fields are treated as `ibubble`/shuffle 0.
    """
    records: dict[tuple[str, int, int, int], tuple[float, str, float]] = {}
    for results in sorted(directory.rglob("results.jsonl")):
        for line in results.read_text().splitlines():
            if not line.strip():
                continue
            record = json.loads(line)
            reported = record.get("reportedTimeMs")
            seconds = record.get("tacticSeconds")
            if seconds is None:
                seconds = reported / 1000 if reported is not None else record.get("wallSeconds")
            if record["status"] != "success":
                seconds = record.get("wallSeconds")
            if seconds is None:
                continue
            records[(record.get("tactic", "ibubble"),
                     record["propositions"], record["seed"],
                     record.get("shuffle", 0))] = (
                record["density"], record["status"], seconds)
    return records


def summarize(records: dict[tuple[str, int, int, int], tuple[float, str, float]],
              csv_path: Path | None = None) -> None:
    """Print success rates and conditional successful runtimes separately."""
    by_tactic_size: dict[
        str, dict[int, list[tuple[int, int, float, str, float]]]
    ] = {}
    for (tactic, size, seed, shuffle), (density, status, seconds) in records.items():
        by_tactic_size.setdefault(tactic, {}).setdefault(size, []).append(
            (seed, shuffle, density, status, seconds))

    for tactic, by_size in sorted(by_tactic_size.items()):
        print(f"\n### {tactic}")
        print("\n| props | n | failures | mean | median | p25 | p75 | p90 | min | max |")
        print("|---|---|---|---|---|---|---|---|---|---|")
        for size, rows in sorted(by_size.items()):
            times = sorted(seconds for *_, status, seconds in rows if status == "success")
            failures = sum(1 for *_, status, _ in rows if status != "success")
            if not times:
                print(f"| {size} | {len(rows)} | {failures} (100%) | — | — | — | — | — | — | — |")
                continue
            # "inclusive" is the linear interpolation numpy's percentile uses.
            cuts = (statistics.quantiles(times, n=100, method="inclusive")
                    if len(times) > 1 else times * 99)
            print(f"| {size} | {len(rows)} | {failures} ({100 * failures / len(rows):.0f}%) "
                  f"| {statistics.mean(times):.1f} | {statistics.median(times):.1f} "
                  f"| {cuts[24]:.1f} | {cuts[74]:.1f} | {cuts[89]:.1f} "
                  f"| {times[0]:.1f} | {times[-1]:.1f} |")
    print("\nRuntime statistics include successful runs only; failures and timeouts "
          "are excluded, not treated as completed runtimes. V3 and later use tactic timings; "
          "legacy data uses declaration #time. See raw records for process wall time.")

    if csv_path is not None:
        with csv_path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.writer(handle)
            writer.writerow(["tactic", "propositions", "density", "seed", "shuffle",
                             "status", "successful_tactic_or_legacy_declaration_seconds"])
            for tactic, by_size in sorted(by_tactic_size.items()):
                for size, rows in sorted(by_size.items()):
                    for seed, shuffle, density, status, seconds in sorted(rows):
                        writer.writerow([tactic, size, density, seed, shuffle, status,
                                         f"{seconds:.3f}" if status == "success" else ""])
        print(f"wrote {csv_path}")


def main(argv: list[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if args.shuffles < 1:
        raise SystemExit("shuffles must be at least 1")
    if args.workers < 1 or min(args.timeout, args.startup_timeout, args.check_timeout) <= 0:
        raise SystemExit("workers and time limits must be positive")
    STOP.clear()
    args.out.mkdir(parents=True, exist_ok=True)
    results_path = args.out / "results.jsonl"

    sizes_by_tactic = {
        "ibubble": args.sizes or args.ibubble_sizes,
        "inaive": args.sizes or args.inaive_sizes,
    }
    for tactic in args.tactics:
        for size in sizes_by_tactic[tactic]:
            build_case(propositions=size, density=args.density)
    # Paired runs alternate which tactic goes first. Resume retains this order.
    done = set(load(args.out))
    cases = []
    for seed_index, seed in enumerate(args.seeds):
        for shuffle in range(args.shuffles):
            for size_index, size in enumerate(sorted({s for t in args.tactics for s in sizes_by_tactic[t]})):
                order = list(args.tactics)
                rotation = (seed_index * args.shuffles + shuffle + size_index + args.order_seed) % len(order)
                order = order[rotation:] + order[:rotation]
                for tactic in order:
                    key = (tactic, size, seed, shuffle)
                    if size in sizes_by_tactic[tactic] and key not in done:
                        cases.append(key)
    print(f"{len(cases)} tactic/cases to run ({len(done)} cached), "
          f"{args.workers} workers, "
          f"{args.timeout_scope} timeout {args.timeout:.0f}s, "
          f"maxHeartbeats {args.max_heartbeats}", flush=True)

    started = time.perf_counter()
    pool = ThreadPoolExecutor(max_workers=args.workers)
    def interrupt(signum, frame):
        raise KeyboardInterrupt
    old_term = signal.signal(signal.SIGTERM, interrupt)
    old_int = signal.getsignal(signal.SIGINT)
    try:
        futures = [pool.submit(run_case, tactic, size, seed, shuffle, args)
                   for tactic, size, seed, shuffle in cases]
        for finished, future in enumerate(as_completed(futures), start=1):
            record = future.result()
            # Written from this thread only, so no lock is needed.
            with results_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(record) + "\n")
            eta = (time.perf_counter() - started) / finished * (len(cases) - finished)
            print(f"[{finished}/{len(cases)} eta {eta / 3600:.1f}h] "
                  f"{record['tactic']:7s} p{record['propositions']} seed {record['seed']} "
                  f"shuffle {record['shuffle']} "
                  f"{record['status']:18s} "
                  f"tactic={record['tacticSeconds']}s wall={record['wallSeconds']:.1f}s"
                  f" backtracks={record['sequentialStats']['backtracks'] if record['sequentialStats'] else '-'}",
                  flush=True)
    except KeyboardInterrupt:
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        cancel_running()
        print("Stopped: queued cases cancelled and active case process groups killed.", flush=True)
        return 130
    finally:
        cancel_running()
        pool.shutdown(wait=True, cancel_futures=True)
        signal.signal(signal.SIGTERM, old_term)
        signal.signal(signal.SIGINT, old_int)

    records = load(args.out)
    if args.csv is not None:
        summarize(records, args.csv)
    print(f"Data saved: {results_path} ({len(records)} observations)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
