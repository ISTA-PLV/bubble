# Bubble

Bubble provides the `ibubble` proof-search tactic for Iris Lean.

## Requirements

- [Elan](https://github.com/leanprover/elan), which installs the pinned Lean
  toolchain automatically

The Lean version is fixed in `lean-toolchain`. Lake downloads the project
dependencies when needed. Downstream projects can depend on this package and
`import Bubble`; they do not download Coinductive or build Bubble's test suite.

## Build, test, and lint

From this directory, run:

```sh
lake build
lake lint
```

These commands build and lint the Bubble library. The tests have a separate Lake
package in `tests/`, with their own test-only Coinductive dependency. Their Lean
source files remain in `BubbleTest.lean` and `BubbleTest/`.

To build and lint the complete test suite from the repository root, run:

```sh
lake -d tests test
lake -d tests lint BubbleTest
```

CI builds, tests, and lints both packages.

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
