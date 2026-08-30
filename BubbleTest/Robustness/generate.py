#!/usr/bin/env python3
"""Generate one synthetic triangular resource-contention benchmark for Bubble."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


@dataclass(frozen=True, order=True)
class Conflict:
    """A decoy using resource P_j to prove an earlier target Q_i."""

    resource: int
    target: int


@dataclass(frozen=True)
class BenchmarkCase:
    propositions: int
    requested_density: float
    seed: int
    conflicts: tuple[Conflict, ...]
    resource_order: tuple[int, ...]
    target_order: tuple[int, ...]

    @property
    def pairs(self) -> int:
        return self.propositions // 2

    @property
    def maximum_conflicts(self) -> int:
        return self.pairs * (self.pairs - 1) // 2

    @property
    def realized_density(self) -> float:
        if self.maximum_conflicts == 0:
            return 0.0
        return len(self.conflicts) / self.maximum_conflicts


def parse_density(value: str) -> float:
    original = value
    value = value.strip()
    try:
        density = float(value[:-1]) / 100 if value.endswith("%") else float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            f"density must be between 0 and 1 or a percentage, got {original!r}"
        ) from error
    if not 0 <= density <= 1:
        raise argparse.ArgumentTypeError("density must be between 0 and 1")
    return density


def _derived_seed(seed: int, propositions: int, purpose: str) -> int:
    payload = f"bubble-resource-contention-v1\0{seed}\0{propositions}\0{purpose}"
    return int.from_bytes(hashlib.sha256(payload.encode()).digest()[:8], "big")


def build_case(
    *,
    propositions: int,
    density: float,
    seed: int = 0,
    shuffle_resources: bool = False,
    shuffle_targets: bool = False,
) -> BenchmarkCase:
    """Build a case with ``propositions / 2`` resource-target pairs."""

    if propositions < 4 or propositions % 2 != 0:
        raise ValueError("propositions must be an even integer of at least 4")
    if not 0 <= density <= 1:
        raise ValueError("density must be between 0 and 1")

    pairs = propositions // 2
    all_conflicts = [
        Conflict(resource=resource, target=target)
        for target in range(pairs)
        for resource in range(target + 1, pairs)
    ]
    random.Random(
        _derived_seed(seed, propositions, "conflicts")
    ).shuffle(all_conflicts)

    # Taking prefixes makes the conflict sets monotone as density increases.
    conflict_count = int(len(all_conflicts) * density + 0.5)
    conflicts = tuple(all_conflicts[:conflict_count])

    resource_order = list(range(pairs))
    target_order = list(range(pairs))
    if shuffle_resources:
        random.Random(
            _derived_seed(seed, propositions, "resources")
        ).shuffle(resource_order)
    if shuffle_targets:
        random.Random(
            _derived_seed(seed, propositions, "targets")
        ).shuffle(target_order)

    return BenchmarkCase(
        propositions=propositions,
        requested_density=density,
        seed=seed,
        conflicts=conflicts,
        resource_order=tuple(resource_order),
        target_order=tuple(target_order),
    )


def _flat_sep(terms: Sequence[str]) -> str:
    if not terms:
        raise ValueError("a separating conjunction needs at least one term")
    return " ∗ ".join(terms)


def _binders(names: Sequence[str], width: int = 8) -> list[str]:
    return [
        f"    ({' '.join(names[start:start + width])} : PROP)"
        for start in range(0, len(names), width)
    ]


def case_metadata(case: BenchmarkCase) -> dict[str, object]:
    return {
        "family": "triangular-resource-contention",
        "ruleRepresentation": "lean-entailment-hypothesis",
        "propositions": case.propositions,
        "resourceTargetPairs": case.pairs,
        "requestedDensity": case.requested_density,
        "realizedDensity": case.realized_density,
        "conflicts": len(case.conflicts),
        "maximumConflicts": case.maximum_conflicts,
        "seed": case.seed,
        "resourceOrder": list(case.resource_order),
        "targetOrder": list(case.target_order),
        "conflictEdges": [
            [edge.resource, edge.target] for edge in case.conflicts
        ],
    }


def recommended_max_depth(case: BenchmarkCase) -> int:
    """Allow enough normalization steps for every connective in the instance."""

    # Rules are Lean hypotheses, so only the spatial resource and target trees
    # need Iris normalization.  The extra factor also leaves room for search.
    return max(100, 4 * case.pairs)


def _render_example(
    case: BenchmarkCase,
    *,
    declaration: str,
    max_heartbeats: int,
    max_depth: int,
    timed: bool,
) -> list[str]:
    canonical_hypotheses = [
        f"    (hCanon{index} : P{index} ⊢ Q{index})"
        for index in range(case.pairs)
    ]
    decoy_hypotheses = [
        f"    (hDecoy{index} : P{edge.resource} ⊢ Q{edge.target})"
        for index, edge in enumerate(case.conflicts)
    ]
    resources = [f"P{index}" for index in case.resource_order]
    targets = [f"Q{index}" for index in case.target_order]
    proposition_names = [
        *(f"P{index}" for index in range(case.pairs)),
        *(f"Q{index}" for index in range(case.pairs)),
    ]

    lines = ["set_option linter.unusedVariables false in"]
    if timed:
        lines.append("#time")
    lines.extend([
        f"set_option maxHeartbeats {max_heartbeats} in",
        f"{declaration} [BI PROP]",
        *_binders(proposition_names),
        "    -- Canonical rules",
        *canonical_hypotheses,
        "    -- Decoy rules",
        *decoy_hypotheses,
        "    : " + _flat_sep(resources) + " ⊢",
        "      " + _flat_sep(targets) + " := by",
        f"  ibubble maxDepth {max_depth}",
    ])
    return lines


def render_lean(
    case: BenchmarkCase,
    *,
    max_heartbeats: int = 2_000_000,
    max_depth: int | None = None,
    max_rec_depth: int = 10_000,
) -> str:
    """Render a standalone Lean example whose complete allocation is unique."""

    lines = [
        "module",
        "",
        "public import Iris.BI",
        "public import Iris.ProofMode",
        "public import Bubble",
        "",
        "@[expose] public section",
        "",
        "namespace BubbleTest.Benchmark.Generated",
        "open Iris Iris.BI",
        "",
        "set_option Elab.async false",
        f"set_option maxRecDepth {max_rec_depth}",
        "",
        *_render_example(
            case,
            declaration="example",
            max_heartbeats=max_heartbeats,
            max_depth=max_depth or recommended_max_depth(case),
            timed=True,
        ),
        "",
        "end BubbleTest.Benchmark.Generated",
        "",
        "/- benchmark-metadata: "
        + json.dumps(case_metadata(case), sort_keys=True, separators=(",", ":"))
        + " -/",
        "",
    ]
    return "\n".join(lines)


def render_suite(
    cases: Sequence[BenchmarkCase],
    *,
    max_heartbeats: int = 2_000_000,
    max_depth: int | None = None,
    max_rec_depth: int = 10_000,
) -> str:
    """Render several timed benchmarks into one Lean module."""

    lines = [
        "module",
        "",
        "public import Iris.BI",
        "public import Iris.ProofMode",
        "public import Bubble",
        "",
        "@[expose] public section",
        "",
        "namespace BubbleTest.Benchmark.Generated",
        "open Iris Iris.BI",
        "",
        "set_option Elab.async false",
        f"set_option maxRecDepth {max_rec_depth}",
        "",
    ]
    for case in cases:
        density_percent = round(case.requested_density * 100)
        name = f"bench_robustness_p{case.propositions}_d{density_percent}"
        marker = (
            f"BENCH propositions={case.propositions} pairs={case.pairs} "
            f"requested_density={case.requested_density:.6f} "
            f"realized_density={case.realized_density:.6f} "
            f"conflicts={len(case.conflicts)}"
        )
        lines.extend([
            f'#eval IO.println "{marker}"',
            *_render_example(
                case,
                declaration=f"theorem {name}",
                max_heartbeats=max_heartbeats,
                max_depth=max_depth or recommended_max_depth(case),
                timed=True,
            ),
            "/- benchmark-metadata: "
            + json.dumps(case_metadata(case), sort_keys=True, separators=(",", ":"))
            + " -/",
            "",
        ])
    lines.extend(["end BubbleTest.Benchmark.Generated", ""])
    return "\n".join(lines)


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--propositions",
        type=int,
        required=True,
        help="total number of atomic propositions; must be even (half P, half Q)",
    )
    parser.add_argument(
        "--density",
        type=parse_density,
        required=True,
        help="fraction of triangular decoys, e.g. 0.5 or 50%%",
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--shuffle-resources", action="store_true")
    parser.add_argument("--shuffle-targets", action="store_true")
    parser.add_argument("--max-heartbeats", type=int, default=2_000_000)
    parser.add_argument(
        "--max-depth",
        type=int,
        help="Bubble search/normalization depth; default is computed from case size",
    )
    parser.add_argument("--max-rec-depth", type=int, default=10_000)
    parser.add_argument(
        "--output",
        type=Path,
        help="output Lean file; omit to print to standard output",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    try:
        case = build_case(
            propositions=args.propositions,
            density=args.density,
            seed=args.seed,
            shuffle_resources=args.shuffle_resources,
            shuffle_targets=args.shuffle_targets,
        )
    except ValueError as error:
        raise SystemExit(str(error)) from error

    rendered = render_lean(
        case,
        max_heartbeats=args.max_heartbeats,
        max_depth=args.max_depth,
        max_rec_depth=args.max_rec_depth,
    )
    if args.output is None:
        sys.stdout.write(rendered)
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
        print(
            f"generated {case.pairs} pairs, {len(case.conflicts)}/"
            f"{case.maximum_conflicts} decoys "
            f"({case.realized_density:.1%}) at {args.output}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
