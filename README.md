# Bubble

Bubble provides the `ibubble` proof-search tactic for Iris Lean.

## Requirements

- [Elan](https://github.com/leanprover/elan), which installs the pinned Lean
  toolchain automatically

The Lean version is fixed in `lean-toolchain`. Lake downloads the project
dependencies when needed. Downstream projects can depend on this package and
`import Bubble`; they do not build Bubble's test suite by default.

## Build, test, and lint

From this directory, run:

```sh
lake build
lake test
lake lint Bubble BubbleTest
```

`Bubble` and `BubbleTest` are two libraries in one Lake package. `lake build`
builds only `Bubble`; `lake test` builds the complete test suite. The editor uses
the root `lakefile.toml` for both. Lake fetches the declared dependencies,
including Coinductive.

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

Copyright (c) 2026 Institute of Science and Technology Austria (ISTA).

Licensed under the Apache License, Version 2.0.
