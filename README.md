# Anonymous Bubble artifact snapshot

This directory contains the anonymized implementation and evaluation material for the paper submission.

Bubble provides the `ibubble` proof-search tactic for Iris Lean.

## Requirements

- [Elan](https://github.com/leanprover/elan), which installs the pinned Lean
  toolchain automatically
- Python 3, for generating and running the robustness benchmarks
- NumPy and Matplotlib, only for plotting benchmark results

The Lean version is fixed in `lean-toolchain`. Lake downloads the project
dependencies when needed. Downstream projects can depend on this package and
`import Bubble`; they do not build Bubble's test suite by default.

## Build, test, and lint

From this directory, run:

```sh
lake build
lake test
lake lint
```

`Bubble` and `BubbleTest` are two libraries in one Lake package. `lake build`
builds only `Bubble`; `lake test` builds the complete test suite. Their sources
remain in `Bubble/` and `BubbleTest/`, and the editor uses the root `lakefile.toml`
for both. Lake fetches the declared benchmark dependencies, including Coinductive,
Aesop, and Wander.

To lint both libraries, as CI does, run:

```sh
lake lint Bubble BubbleTest
```

Linting uses Lean's built-in checks, including unused variables and section
parameters, deprecated declarations, unreachable tactics, and unnecessary `<;>`
combinators. The command fails when it finds lint warnings.

## Daily upstream compatibility

Every day at 06:23 UTC, CI builds, tests, and lints two upstream configurations:

- The latest commit on Iris Lean's default branch, using the Lean toolchain that
  commit declares.
- The latest Iris commit with Lean's latest official stable release.

The workflow logs the exact Iris commit and Lean toolchain. These checks change
versions only in the CI checkout; committed dependency pins are unchanged. The
workflow can also be run manually in GitHub Actions.

## Evaluation environment

The reported timings were collected on an Apple M3 with 8 CPU cores
(4 performance and 4 efficiency cores) and 24 GB of memory, running macOS
26.6.2. With the shared dependencies already built, rebuilding the manual,
search, and generated IrisITree variants took 8.5 s, 77.7 s, and 9.7 s on
average, respectively.

## Contents

- `Bubble/` contains the implementation of `ibubble`.
- `BubbleTest/` contains unit tests and small examples.
- `BubbleTest/IrisITree/`, `BubbleTest/IrisITreeBubble/`, and
  `BubbleTest/IrisITreeScript/` contain three versions of IrisITree, a framework
  for building composable program logics based on Interaction Trees (ITrees):
  manual proofs, proofs using `ibubble`, and generated scripts, respectively.
- `BubbleTest/IrisITreeBenchmark/` contains the IrisITree benchmark runner,
  tactic-counting script, cached samples, and aggregated metrics.
- `BubbleTest/Robustness/` contains the synthetic resource-contention
  benchmark generator, runner, plotting script, and benchmark-only Aesop
  baselines.

## Paper examples

The examples used in Sections 2.1–2.4 and 6 of the paper are collected in
[`BubbleTest/Example.lean`](BubbleTest/Example.lean). Comments in the file mark
the corresponding paper sections.

The `wp_store` example from the introduction is available as both a
[manual proof](BubbleTest/IrisITree/HeapLang/ProgramLogic.lean#L368) and an
[`ibubble` proof](BubbleTest/IrisITreeBubble/HeapLang/ProgramLogic.lean#L296).

## Robustness benchmark

Compares `ibubble` with `inaive` (Aesop + context-partition enumeration),
with simp disabled for both.

From this directory, run:

```sh
python3 -m pip install matplotlib numpy
lake build BubbleTest.Robustness
bash BubbleTest/Robustness/run_benchmark.sh
```

Data and the PNG figure are saved in
[`BubbleTest/Robustness/result/`](BubbleTest/Robustness/result/).
The command reuses the included measurements and redraws the figure.
Runs resume by skipping recorded tactic/size/seed/shuffle combinations.
Use a new output directory when changing the source or experiment settings.
To run the experiment from scratch, choose a new output directory:

```sh
bash BubbleTest/Robustness/run_benchmark.sh --out BubbleTest/Robustness/result-new
```

Use `bash BubbleTest/Robustness/run_benchmark.sh --help` for experiment options.

## IrisITree benchmark

This benchmark compares three proof variants:

- `IrisITree`: handwritten proofs.
- `IrisITreeBubble`: proofs using `ibubble`.
- `IrisITreeScript`: generated proof scripts, replayed without search.

It measures proof size (tactic counts), complete build time, and `ibubble` search time.

From this directory, count tactics with:

```sh
python3 BubbleTest/IrisITreeBenchmark/count_tactics.py
```

To reproduce the timing measurements from scratch, first move the included
results aside, then run five repetitions (from the `bubble/` directory):

```sh
mv BubbleTest/IrisITreeBenchmark/results BubbleTest/IrisITreeBenchmark/results-original
bash BubbleTest/IrisITreeBenchmark/run_benchmark.sh 5
```

Move the included results only once, and choose another backup name if
`results-original` already exists. The runner builds the required dependencies
and measures all three proof variants; Lean/Elan and Python 3 must be installed.

Results are saved in `BubbleTest/IrisITreeBenchmark/results/`: `README.md`
summarizes the results, and the CSV files contain measurements and summary statistics.

To resume an interrupted run, repeat the benchmark command without moving
`results/`; completed measurements are reused.

Copyright (c) 2026 Institute of Science and Technology Austria (ISTA).

Licensed under the Apache License, Version 2.0.
