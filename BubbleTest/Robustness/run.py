#!/usr/bin/env python3
"""Generate, run, and record Bubble size and density robustness sweeps."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Sequence

from generate import (
    build_case,
    case_metadata,
    parse_density,
    recommended_max_depth,
    render_suite,
)


def build_argument_parser() -> argparse.ArgumentParser:
    script_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--propositions",
        type=_parse_integer_list,
        default=[10, 20, 30, 40, 50],
        help="size sweep, as a comma-separated list (default: 10,20,30,40,50)",
    )
    parser.add_argument(
        "--density",
        type=parse_density,
        default=0.2,
        help="density used by the size sweep (default: 20%%)",
    )
    parser.add_argument(
        "--density-sweep-propositions",
        type=int,
        default=30,
        help="proposition count used by the density sweep (default: 30)",
    )
    parser.add_argument(
        "--density-levels",
        type=_parse_density_list,
        default=[0.0, 0.2, 0.4, 0.6, 0.8],
        help="density sweep at one size (default: 0%%,20%%,40%%,60%%,80%%)",
    )
    parser.add_argument(
        "--no-density-sweep",
        action="store_true",
        help="generate only the proposition-size sweep",
    )
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--max-heartbeats", type=int, default=2_000_000)
    parser.add_argument(
        "--max-depth",
        type=int,
        help="Bubble search/normalization depth; default is computed per case",
    )
    parser.add_argument("--max-rec-depth", type=int, default=10_000)
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument(
        "--lean-output",
        type=Path,
        default=script_dir / "bench.lean",
    )
    parser.add_argument(
        "--results",
        type=Path,
        default=script_dir / "bench_results.json",
    )
    parser.add_argument(
        "--lake-dir",
        type=Path,
        default=script_dir.parent.parent,
    )
    parser.add_argument(
        "--canonical-resources",
        action="store_true",
        help="do not shuffle spatial resources",
    )
    parser.add_argument(
        "--canonical-targets",
        action="store_true",
        help="do not shuffle target conjuncts",
    )
    return parser


def _parse_integer_list(value: str) -> list[int]:
    try:
        result = [int(item.strip()) for item in value.split(",") if item.strip()]
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            f"expected comma-separated integers, got {value!r}"
        ) from error
    if not result:
        raise argparse.ArgumentTypeError("proposition list cannot be empty")
    return result


def _parse_density_list(value: str) -> list[float]:
    result = [
        parse_density(item.strip())
        for item in value.split(",")
        if item.strip()
    ]
    if not result:
        raise argparse.ArgumentTypeError("density list cannot be empty")
    return result


def _benchmark_specs(
    propositions: Sequence[int],
    size_density: float,
    density_sweep_propositions: int,
    density_levels: Sequence[float],
    include_density_sweep: bool,
) -> list[tuple[int, float]]:
    requested = [(value, size_density) for value in propositions]
    if include_density_sweep:
        requested.extend(
            (density_sweep_propositions, density) for density in density_levels
        )
    result: list[tuple[int, float]] = []
    seen: set[tuple[int, float]] = set()
    for spec in requested:
        if spec not in seen:
            seen.add(spec)
            result.append(spec)
    return result


def _partial_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def _case_results(output: str, cases: Sequence[object]) -> list[dict[str, object]]:
    marker_re = re.compile(
        r"^BENCH propositions=(\d+) pairs=(\d+) "
        r"requested_density=([0-9.]+) realized_density=([0-9.]+) "
        r"conflicts=(\d+)$",
        re.MULTILINE,
    )
    matches = list(marker_re.finditer(output))
    sections: dict[tuple[int, str], str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(output)
        key = (int(match.group(1)), f"{float(match.group(3)):.6f}")
        sections[key] = output[match.end():end]

    results: list[dict[str, object]] = []
    for case in cases:
        key = (case.propositions, f"{case.requested_density:.6f}")
        section = sections.get(key)
        if section is None:
            results.append({
                "propositions": case.propositions,
                "requestedDensity": case.requested_density,
                "realizedDensity": case.realized_density,
                "status": "not_started",
                "reportedElaborationTimeMs": None,
                "diagnostic": "",
            })
            continue

        time_match = re.search(r"^time: ([0-9.]+)(ms|s)$", section, re.MULTILINE)
        reported_ms = None
        if time_match is not None:
            reported_ms = float(time_match.group(1))
            if time_match.group(2) == "s":
                reported_ms *= 1000

        if "error:" not in section:
            status = "success"
            diagnostic = ""
        elif "maximum number of heartbeats" in section:
            status = "heartbeat_timeout"
            diagnostic = section[section.find("error:"):].strip()
        elif "exceeded" in section and "normalization iterations" in section:
            status = "normalization_limit"
            diagnostic = section[section.find("error:"):].strip()
        elif "maximum recursion depth" in section:
            status = "recursion_limit"
            diagnostic = section[section.find("error:"):].strip()
        else:
            status = "lean_error"
            diagnostic = section[section.find("error:"):].strip()
        results.append({
            "propositions": case.propositions,
            "requestedDensity": case.requested_density,
            "realizedDensity": case.realized_density,
            "status": status,
            "reportedElaborationTimeMs": reported_ms,
            "diagnostic": diagnostic,
        })
    return results


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if args.max_heartbeats < 1:
        raise SystemExit("max-heartbeats must be positive")
    if args.max_depth is not None and args.max_depth < 1:
        raise SystemExit("max-depth must be positive")
    if args.max_rec_depth < 1:
        raise SystemExit("max-rec-depth must be positive")
    if args.timeout <= 0:
        raise SystemExit("timeout must be positive")

    specs = _benchmark_specs(
        args.propositions,
        args.density,
        args.density_sweep_propositions,
        args.density_levels,
        not args.no_density_sweep,
    )
    try:
        cases = [
            build_case(
                propositions=propositions,
                density=density,
                seed=args.seed,
                shuffle_resources=not args.canonical_resources,
                shuffle_targets=not args.canonical_targets,
            )
            for propositions, density in specs
        ]
    except ValueError as error:
        raise SystemExit(str(error)) from error

    args.lean_output.parent.mkdir(parents=True, exist_ok=True)
    args.lean_output.write_text(
        render_suite(
            cases,
            max_heartbeats=args.max_heartbeats,
            max_depth=args.max_depth,
            max_rec_depth=args.max_rec_depth,
        ),
        encoding="utf-8",
    )

    command = [
        "lake",
        "env",
        "lean",
        "-DElab.async=false",
        f"-DmaxRecDepth={args.max_rec_depth}",
        str(args.lean_output.resolve()),
    ]
    started_at = datetime.now(timezone.utc).isoformat()
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            cwd=args.lake_dir,
            capture_output=True,
            text=True,
            timeout=args.timeout,
        )
        elapsed = time.perf_counter() - started
        output = (completed.stdout or "") + (completed.stderr or "")
        return_code: int | None = completed.returncode
        status = "success" if completed.returncode == 0 else "lean_error"
    except subprocess.TimeoutExpired as error:
        elapsed = time.perf_counter() - started
        output = _partial_text(error.stdout) + _partial_text(error.stderr)
        return_code = None
        status = "process_timeout"

    record = {
        "schemaVersion": 1,
        "startedAt": started_at,
        "status": status,
        "returnCode": return_code,
        "processWallTimeSeconds": elapsed,
        "command": command,
        "parameters": {
            "sizeSweepPropositions": args.propositions,
            "sizeSweepDensity": args.density,
            "densitySweepPropositions": args.density_sweep_propositions,
            "densityLevels": args.density_levels,
            "densitySweepEnabled": not args.no_density_sweep,
            "seed": args.seed,
            "maxHeartbeats": args.max_heartbeats,
            "maxDepth": args.max_depth,
            "maxRecDepth": args.max_rec_depth,
            "timeoutSeconds": args.timeout,
            "shuffleResources": not args.canonical_resources,
            "shuffleTargets": not args.canonical_targets,
        },
        "cases": [
            {
                **case_metadata(case),
                "effectiveMaxDepth": args.max_depth or recommended_max_depth(case),
            }
            for case in cases
        ],
        "caseResults": _case_results(output, cases),
        "leanFile": str(args.lean_output.resolve()),
        "leanOutput": output,
    }
    args.results.parent.mkdir(parents=True, exist_ok=True)
    args.results.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")

    if output:
        sys.stdout.write(output)
        if not output.endswith("\n"):
            sys.stdout.write("\n")
    print(f"generated: {args.lean_output}")
    print(f"results:   {args.results}")
    print(f"status:    {status} ({elapsed:.3f}s)")
    return 0 if status == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
