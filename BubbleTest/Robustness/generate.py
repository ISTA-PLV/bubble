#!/usr/bin/env python3
"""Generate one synthetic triangular resource-contention benchmark case."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


TACTICS = ("ibubble", "inaive")


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
    shuffle: int
    conflicts: tuple[Conflict, ...]
    proposition_order: tuple[str, ...]
    rule_order: tuple[tuple[str, int], ...]
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


def _derived_seed(
    seed: int, propositions: int, purpose: str, shuffle: int | None = None
) -> int:
    payload = (
        f"bubble-resource-contention-v4\0{seed}\0{propositions}\0"
        f"{shuffle if shuffle is not None else 'instance'}\0{purpose}"
    )
    return int.from_bytes(hashlib.sha256(payload.encode()).digest()[:8], "big")


def build_case(
    *,
    propositions: int,
    density: float,
    seed: int = 0,
    shuffle: int = 0,
) -> BenchmarkCase:
    """Build one logical instance and one complete presentation shuffle."""

    if propositions < 4 or propositions % 2 != 0:
        raise ValueError("propositions must be an even integer of at least 4")
    if not 0 <= density <= 1:
        raise ValueError("density must be between 0 and 1")
    if shuffle < 0:
        raise ValueError("shuffle must be non-negative")

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
    # The base seed determines the logical graph.  Sorting after sampling keeps
    # that graph fixed while the separate shuffle index controls presentation.
    conflicts = tuple(sorted(all_conflicts[:conflict_count]))

    proposition_order = [
        *(f"P{index}" for index in range(pairs)),
        *(f"Q{index}" for index in range(pairs)),
    ]
    # Shuffle the complete potential rule universe, then remove absent decoys.
    # Consequently a density change neither changes the other three orders nor
    # the relative order of rules shared by the two instances.
    rule_universe = [
        *(('canonical', index) for index in range(pairs)),
        *(('decoy', edge) for edge in sorted(all_conflicts)),
    ]
    resource_order = list(range(pairs))
    target_order = list(range(pairs))
    # One recorded master seed drives the complete presentation shuffle.  The
    # calls are deliberately sequential so the entire rendered case is one
    # reproducible randomization, rather than four independently seeded ones.
    shuffle_seed = _derived_seed(
        seed, propositions, "complete-presentation", shuffle
    )
    shuffle_rng = random.Random(shuffle_seed)
    for values in (
        proposition_order, rule_universe, resource_order, target_order
    ):
        shuffle_rng.shuffle(values)
    conflict_indices = {edge: index for index, edge in enumerate(conflicts)}
    rule_order = [
        (kind, value if kind == 'canonical' else conflict_indices[value])
        for kind, value in rule_universe
        if kind == 'canonical' or value in conflict_indices
    ]

    return BenchmarkCase(
        propositions=propositions,
        requested_density=density,
        seed=seed,
        shuffle=shuffle,
        conflicts=conflicts,
        proposition_order=tuple(proposition_order),
        rule_order=tuple(rule_order),
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
    graph = {"propositions": case.propositions,
             "conflictEdges": [[edge.resource, edge.target] for edge in case.conflicts]}
    instance_hash = hashlib.sha256(json.dumps(graph, sort_keys=True).encode()).hexdigest()
    presentation = {"instanceHash": instance_hash, "propositionOrder": case.proposition_order,
                    "ruleOrder": case.rule_order, "resourceOrder": case.resource_order,
                    "targetOrder": case.target_order}
    return {
        "family": "triangular-resource-contention",
        "generatorVersion": 4,
        "instanceHash": instance_hash,
        "presentationHash": hashlib.sha256(json.dumps(presentation, sort_keys=True).encode()).hexdigest(),
        "ruleRepresentation": "lean-entailment-hypothesis",
        "propositions": case.propositions,
        "resourceTargetPairs": case.pairs,
        "requestedDensity": case.requested_density,
        "realizedDensity": case.realized_density,
        "conflicts": len(case.conflicts),
        "maximumConflicts": case.maximum_conflicts,
        "seed": case.seed,
        "shuffle": case.shuffle,
        "shuffleSeed": _derived_seed(
            case.seed, case.propositions, "complete-presentation", case.shuffle
        ),
        "propositionOrder": list(case.proposition_order),
        "ruleOrder": [list(rule) for rule in case.rule_order],
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
    tactic: str,
    max_heartbeats: int,
    max_depth: int,
    timed: bool,
) -> list[str]:
    rule_hypotheses = [
        f"    (hRule{position} : P{index} ⊢ Q{index})" if kind == "canonical" else
        f"    (hRule{position} : P{case.conflicts[index].resource} ⊢ Q{case.conflicts[index].target})"
        for position, (kind, index) in enumerate(case.rule_order)
    ]
    resources = [f"P{index}" for index in case.resource_order]
    targets = [f"Q{index}" for index in case.target_order]

    lines = ["set_option linter.unusedVariables false in"]
    if timed:
        lines.append("#time")
    invocation = f"ibubble noSimp maxDepth {max_depth}" if tactic == "ibubble" else tactic
    tactic_line = f"  robustness_timed {invocation}"
    lines.extend([
        f"set_option maxHeartbeats {max_heartbeats} in",
        f"{declaration} [BI PROP]",
        *_binders(case.proposition_order),
        "    -- Canonical and decoy rules, shuffled together",
        *rule_hypotheses,
        "    : " + _flat_sep(resources) + " ⊢",
        "      " + _flat_sep(targets) + " := by",
        tactic_line,
    ])
    return lines


def render_lean(
    case: BenchmarkCase,
    *,
    tactic: str = "ibubble",
    max_heartbeats: int = 2_000_000,
    max_depth: int | None = None,
    max_rec_depth: int = 10_000,
) -> str:
    """Render a standalone Lean example whose complete allocation is unique."""

    if tactic not in TACTICS:
        raise ValueError(f"unknown tactic {tactic!r}; expected one of {TACTICS}")

    lines = [
        "module",
        "",
        "public import Iris.BI",
        "public import Iris.ProofMode",
        "public import Bubble",
        "public import BubbleTest.Robustness.Tactics",
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
            tactic=tactic,
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
    tactic: str = "ibubble",
    max_heartbeats: int = 2_000_000,
    max_depth: int | None = None,
    max_rec_depth: int = 10_000,
) -> str:
    """Render several timed benchmarks into one Lean module."""

    if tactic not in TACTICS:
        raise ValueError(f"unknown tactic {tactic!r}; expected one of {TACTICS}")

    lines = [
        "module",
        "",
        "public import Iris.BI",
        "public import Iris.ProofMode",
        "public import Bubble",
        "public import BubbleTest.Robustness.Tactics",
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
        name = (
            f"bench_robustness_p{case.propositions}_d{density_percent}_"
            f"s{case.seed}_r{case.shuffle}"
        )
        marker = (
            f"BENCH propositions={case.propositions} pairs={case.pairs} "
            f"requested_density={case.requested_density:.6f} "
            f"realized_density={case.realized_density:.6f} "
            f"conflicts={len(case.conflicts)} seed={case.seed} "
            f"shuffle={case.shuffle}"
        )
        lines.extend([
            f'#eval IO.println "{marker}"',
            *_render_example(
                case,
                declaration=f"theorem {name}",
                tactic=tactic,
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
    parser.add_argument(
        "--shuffle",
        type=int,
        default=0,
        help="complete presentation-shuffle index (default: 0)",
    )
    parser.add_argument(
        "--tactic",
        choices=TACTICS,
        default="ibubble",
        help="proof-search architecture to invoke (default: ibubble)",
    )
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
            shuffle=args.shuffle,
        )
    except ValueError as error:
        raise SystemExit(str(error)) from error

    rendered = render_lean(
        case,
        tactic=args.tactic,
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
            f" using seed {case.seed}, shuffle {case.shuffle}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
