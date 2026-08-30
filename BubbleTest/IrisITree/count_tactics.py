#!/usr/bin/env python3
"""Count manual and automated Lean/Iris tactics in the Bubble IrisITree tests.

The test files keep many pre-Bubble proof scripts as line comments next to
their automated replacements.  This script reconstructs the original count as

    current tactics - active ibubble commands + commented manual tactics.

Counts are lexical tactic-command counts, not physical lines.  In particular,
``iapply foo; simp`` contributes one Iris tactic and one Lean tactic.  Bubble
configuration such as the ``simp`` in ``ibubble simp`` is not a separate Lean
tactic, while solvers passed through ``pureBy`` are counted.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


SOURCE_FOLDERS = ("Core", "Effects", "HeapLang")

IRIS_TACTICS = (
    "ibubble",
    "iapply",
    "iassumption",
    "icases",
    "iclear",
    "icombine",
    "iexact",
    "iexists",
    "iframe",
    "ihave",
    "iinduction",
    "iintro",
    "ileft",
    "imod",
    "imodintro",
    "inext",
    "ipureintro",
    "irename",
    "irevert",
    "iright",
    "ispecialize",
    "isplit",
    "isplitl",
    "isplitr",
    "istart",
    "istop",
    "itrivial",
)

LEAN_TACTICS = (
    "aesop",
    "all_goals",
    "any_goals",
    "apply",
    "assumption",
    "by_cases",
    "by_contra",
    "case",
    "cases",
    "change",
    "congr",
    "constructor",
    "contradiction",
    "decide",
    "exact",
    "exact_mod_cast",
    "ext",
    "first",
    "focus",
    "funext",
    "generalize",
    "grind",
    "have",
    "induction",
    "infer_instance",
    "intro",
    "left",
    "linarith",
    "next",
    "norm_num",
    "obtain",
    "omega",
    "rcases",
    "refine",
    "rename_i",
    "repeat",
    "rfl",
    "right",
    "ring",
    "rintro",
    "rotate_left",
    "rotate_right",
    "rw",
    "show",
    "simpa",
    "simp",
    "simp_all",
    "skip",
    "solve",
    "specialize",
    "split",
    "subst",
    "suffices",
    "trivial",
    "try",
    "unfold",
    "use",
)

IRIS_RE = re.compile(r"\b(?:" + "|".join(map(re.escape, IRIS_TACTICS)) + r")\b")
LEAN_RE = re.compile(r"\b(?:" + "|".join(map(re.escape, LEAN_TACTICS)) + r")\b")
IBUBBLE_RE = re.compile(r"\bibubble\b")
PURE_BY_RE = re.compile(r"\bpureBy\b")


@dataclass(frozen=True)
class TacticCounts:
    iris: int = 0
    lean: int = 0

    @property
    def total(self) -> int:
        return self.iris + self.lean

    def __add__(self, other: "TacticCounts") -> "TacticCounts":
        return TacticCounts(self.iris + other.iris, self.lean + other.lean)

    def __sub__(self, other: "TacticCounts") -> "TacticCounts":
        return TacticCounts(self.iris - other.iris, self.lean - other.lean)


@dataclass(frozen=True)
class FolderMetrics:
    folder: str
    files: int
    commented: TacticCounts
    original: TacticCounts
    current: TacticCounts

    @property
    def saved(self) -> TacticCounts:
        return self.original - self.current


@dataclass(frozen=True)
class ProofSource:
    active: tuple[str, ...]
    commented: tuple[str, ...]


def _leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip())


def extract_proof_source(text: str) -> ProofSource:
    """Extract active and commented tactic text from ``:= by`` proof bodies."""

    active: list[str] = []
    commented: list[str] = []
    in_proof = False
    waiting_for_body = False
    start_indent = 0
    body_indent: int | None = None

    def start_proof(line: str) -> bool:
        nonlocal in_proof, waiting_for_body, start_indent, body_indent
        code = line.split("--", 1)[0]
        if ":= by" not in code:
            return False
        start_indent = _leading_spaces(line)
        tail = code.split(":= by", 1)[1].strip()
        in_proof = True
        waiting_for_body = not bool(tail)
        body_indent = None
        if tail:
            active.append(tail)
        return True

    for line in text.splitlines():
        stripped = line.lstrip()
        indent = _leading_spaces(line)
        is_comment = stripped.startswith("--")

        if not in_proof:
            start_proof(line)
            continue

        if not stripped:
            continue
        if is_comment:
            if body_indent is not None and indent < body_indent:
                in_proof = False
                waiting_for_body = False
                body_indent = None
                continue
            candidate = stripped[2:].lstrip()
            if count_tactics(candidate).total:
                commented.append(candidate)
            continue

        if waiting_for_body:
            body_indent = indent
            waiting_for_body = False
            active.append(stripped.split("--", 1)[0])
            continue

        proof_ended = (
            body_indent is not None and indent < body_indent
        ) or (
            body_indent is None and indent <= start_indent
        )
        if proof_ended:
            in_proof = False
            waiting_for_body = False
            body_indent = None
            start_proof(line)
            continue

        active.append(stripped.split("--", 1)[0])

    return ProofSource(tuple(active), tuple(commented))


def _plain_tactic_counts(text: str) -> TacticCounts:
    return TacticCounts(
        iris=len(IRIS_RE.findall(text)),
        lean=len(LEAN_RE.findall(text)),
    )


def _top_level_separator(text: str) -> tuple[int, int] | None:
    """Return the first top-level Lean tactic separator in ``text``."""

    opening = {"(": ")", "[": "]", "{": "}"}
    closing = set(opening.values())
    stack: list[str] = []
    in_string = False
    escaped = False
    index = 0

    while index < len(text):
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
        elif char in opening:
            stack.append(opening[char])
        elif char in closing:
            if stack and char == stack[-1]:
                stack.pop()
        elif not stack and text.startswith("<;>", index):
            return index, index + 3
        elif not stack and char == ";":
            return index, index + 1
        index += 1

    return None


def _top_level_config_keyword(text: str, start: int) -> int:
    """Find where a ``pureBy`` solver ends and Bubble configuration resumes."""

    opening = {"(": ")", "[": "]", "{": "}"}
    closing = set(opening.values())
    stack: list[str] = []
    index = start

    while index < len(text):
        char = text[index]
        if char in opening:
            stack.append(opening[char])
        elif char in closing:
            if stack and char == stack[-1]:
                stack.pop()
        elif not stack:
            for keyword in ("with", "without", "pureStop"):
                end = index + len(keyword)
                if (
                    text.startswith(keyword, index)
                    and (index == 0 or not (text[index - 1].isalnum() or text[index - 1] == "_"))
                    and (end == len(text) or not (text[end].isalnum() or text[end] == "_"))
                ):
                    return index
        index += 1

    return len(text)


def _pure_solver_counts(configuration: str) -> TacticCounts:
    result = TacticCounts()
    cursor = 0
    while match := PURE_BY_RE.search(configuration, cursor):
        start = match.end()
        end = _top_level_config_keyword(configuration, start)
        result += _plain_tactic_counts(configuration[start:end])
        cursor = end
        if cursor >= len(configuration):
            break
    return result


def count_tactics(text: str) -> TacticCounts:
    """Classify tactics in one source fragment, including Bubble automation."""

    match = IBUBBLE_RE.search(text)
    if match is None:
        return _plain_tactic_counts(text)

    before = text[:match.start()]
    after = text[match.end():]
    separator = _top_level_separator(after)
    if separator is None:
        configuration = after
        suffix = ""
    else:
        separator_start, separator_end = separator
        configuration = after[:separator_start]
        suffix = after[separator_end:]

    return (
        _plain_tactic_counts(before)
        + TacticCounts(iris=1)
        + _pure_solver_counts(configuration)
        + count_tactics(suffix)
    )


def automation_counts(active: Sequence[str]) -> TacticCounts:
    """Count active Bubble tactics that replace adjacent commented scripts."""

    result = TacticCounts()
    for index, line in enumerate(active):
        match = IBUBBLE_RE.search(line)
        if match is not None:
            result += count_tactics(line[match.start():])
            if line.strip().startswith("all_goals"):
                result += TacticCounts(lean=1)
        elif line.strip() == "all_goals" and index + 1 < len(active):
            if IBUBBLE_RE.search(active[index + 1]):
                result += TacticCounts(lean=1)
    return result


def sum_counts(fragments: Iterable[str]) -> TacticCounts:
    result = TacticCounts()
    for fragment in fragments:
        result += count_tactics(fragment)
    return result


def analyze_folder(folder: Path) -> FolderMetrics:
    current = TacticCounts()
    commented = TacticCounts()
    automated = TacticCounts()
    files = sorted(folder.rglob("*.lean"))

    for source_file in files:
        proof = extract_proof_source(source_file.read_text(encoding="utf-8"))
        current += sum_counts(proof.active)
        commented += sum_counts(proof.commented)
        automated += automation_counts(proof.active)

    original = current - automated + commented
    return FolderMetrics(folder.name, len(files), commented, original, current)


def combine_metrics(metrics: Sequence[FolderMetrics]) -> FolderMetrics:
    return FolderMetrics(
        folder="TOTAL",
        files=sum(metric.files for metric in metrics),
        commented=sum((metric.commented for metric in metrics), TacticCounts()),
        original=sum((metric.original for metric in metrics), TacticCounts()),
        current=sum((metric.current for metric in metrics), TacticCounts()),
    )


def factor(original: int, current: int) -> str:
    if current == 0:
        return "--" if original == 0 else "inf"
    return f"{original / current:.2f}x"


def render_table(metrics: Sequence[FolderMetrics]) -> str:
    headers = (
        "Folder", "Files",
        "Comment I", "Comment L", "Comment T",
        "Original I", "Original L", "Original T",
        "Current I", "Current L", "Current T",
        "I factor", "L factor", "All factor",
    )
    rows: list[tuple[str, ...]] = []
    for metric in metrics:
        rows.append((
            metric.folder,
            str(metric.files),
            str(metric.commented.iris),
            str(metric.commented.lean),
            str(metric.commented.total),
            str(metric.original.iris),
            str(metric.original.lean),
            str(metric.original.total),
            str(metric.current.iris),
            str(metric.current.lean),
            str(metric.current.total),
            factor(metric.original.iris, metric.current.iris),
            factor(metric.original.lean, metric.current.lean),
            factor(metric.original.total, metric.current.total),
        ))

    widths = [
        max(len(headers[index]), *(len(row[index]) for row in rows))
        for index in range(len(headers))
    ]

    def render_row(row: Sequence[str]) -> str:
        return "  ".join(
            value.ljust(widths[index]) if index == 0
            else value.rjust(widths[index])
            for index, value in enumerate(row)
        )

    separator = "  ".join("-" * width for width in widths)
    return "\n".join((render_row(headers), separator, *(render_row(row) for row in rows)))


def metrics_as_json(metrics: Sequence[FolderMetrics]) -> str:
    payload = []
    for metric in metrics:
        item = asdict(metric)
        item["saved"] = asdict(metric.saved)
        item["factors"] = {
            "iris": None if metric.current.iris == 0 else metric.original.iris / metric.current.iris,
            "lean": None if metric.current.lean == 0 else metric.original.lean / metric.current.lean,
            "all": None if metric.current.total == 0 else metric.original.total / metric.current.total,
        }
        payload.append(item)
    return json.dumps(payload, indent=2)


def build_argument_parser() -> argparse.ArgumentParser:
    default_root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=default_root,
        help=f"IrisITree source root (default: {default_root})",
    )
    parser.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    missing = [name for name in SOURCE_FOLDERS if not (args.root / name).is_dir()]
    if missing:
        raise SystemExit(f"missing IrisITree folders under {args.root}: {', '.join(missing)}")

    per_folder = [analyze_folder(args.root / name) for name in SOURCE_FOLDERS]
    metrics = [*per_folder, combine_metrics(per_folder)]
    print(metrics_as_json(metrics) if args.json else render_table(metrics))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
