# Bubble

Bubble provides the `ibubble` proof-search tactic for Iris Lean.

## Requirements

- [Elan](https://github.com/leanprover/elan), which installs the pinned Lean
  toolchain automatically

The Lean version is fixed in `lean-toolchain`. Lake downloads the project
dependencies when needed.

## Build and test

From this directory, run:

```sh
lake build
lake test
```

`lake build` builds the Bubble library. `lake test` builds the complete test
suite.

Copyright (c) 2026 Institute of Science and Technology Austria (ISTA).

Licensed under the Apache License, Version 2.0.
