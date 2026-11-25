# Bubble

Bubble provides the `ibubble` proof-search tactic for Iris Lean.

## Requirements

- [Elan](https://github.com/leanprover/elan), which installs the pinned Lean
  toolchain automatically

The repository contains two Lake packages, laid out like Iris Lean:

- `Bubble/`: the `bubble` library, which depends only on Iris.
- `BubbleTest/`: the test suite, which depends on `bubble` (by path) and on
  Coinductive.

Each package has its own `lakefile.toml`, `lake-manifest.json`, and
`lean-toolchain`. Lake downloads the dependencies when needed. Downstream
projects depend on the `Bubble` subdirectory and `import Bubble`; they do not
download Coinductive or build the tests:

```toml
[[require]]
name = "bubble"
git = "<this repository>"
rev = "main"
subDir = "Bubble"
```

## Build, test, and lint

From the repository root, run:

```sh
(cd Bubble && lake build && lake lint)
(cd BubbleTest && lake test && lake lint)
```

The test package builds `bubble` from `../Bubble`, so `lake test` always uses
the current library sources. In the editor, each file uses the package of its
nearest `lakefile.toml`.

Linting uses Lean's built-in checks, including unused variables and section
parameters, deprecated declarations, unreachable tactics, and unnecessary `<;>`
combinators. The command fails when it finds lint warnings.

## Daily upstream compatibility

Every day at 06:23 UTC, CI builds, tests, and lints both packages against two
upstream configurations:

- The latest commit on Iris Lean's default branch, using the Lean toolchain that
  commit declares.
- The latest Iris commit with Lean's latest official stable release.

The workflow logs the exact Iris commit and Lean toolchain. These checks change
versions only in the CI checkout; committed dependency pins are unchanged. The
workflow can also be run manually in GitHub Actions.

Copyright (c) 2026 Institute of Science and Technology Austria (ISTA).

Licensed under the Apache License, Version 2.0.
