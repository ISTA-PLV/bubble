# Bubble

Bubble provides `ibubble`, a general-purpose finishing tactic (inspired by Aesop) for [Iris Lean](https://github.com/leanprover-community/iris-lean). For its design and search algorithm, see our [paper](https://yunsongyang.com/files/bubble.pdf).

## Installation

Add Bubble to your project's `lakefile.toml`:

```toml
[[require]]
name = "bubble"
git = "https://github.com/ISTA-PLV/bubble.git"
rev = "main"
subDir = "Bubble"
```

Then run `lake update bubble`. Bubble already depends on Iris Lean, so you do not need to require Iris separately. Your project should use the same Lean toolchain as `Bubble/lean-toolchain`.

## Build

The core package `Bubble` is separate from its test package `BubbleTest`, so downstream users do not need the test dependencies.

```sh
cd Bubble
lake build
```

To run the tests:

```sh
cd BubbleTest
lake test
```

`Bubble/` depends only on Iris; `BubbleTest/` also depends on Coinductive.

## Usage

```lean
import Bubble
open Iris BI

variable {PROP : Type} [BI PROP] (P Q : PROP)

example : P -∗ □ (P -∗ Q) -∗ Q := by
  ibubble
```

Use `ibubble?` to print the proof script that `ibubble` finds, and then you can replace the invocation with the script to reuse the proof (once for all).

## Pure goals

When the search reaches a pure Lean goal `⌜φ⌝`, it runs a solver on `φ`.

- `ibubble`: uses `assumption` (the default).
- `ibubble pureBy <tac>`: uses `<tac>`, e.g. `ibubble pureBy simp [*]`. One internal search fails if `<tac>` does not close the goal.
- `ibubble pureStop`: does not solve pure goals. They are returned as remaining goals after `ibubble`:
  ```lean
  ibubble pureStop
  · simp
  · assumption
  ```

**Warning:** `pureStop` stops at the first pure goal it encounters, and that goal may not be provable.

## Rules

Register a theorem with a success probability. Rules with a higher probability are tried first. Rules are *backward* by default.

```lean
@[ibubble 75%] theorem foo ...           -- backward rule
@[ibubble forward 50%] theorem bar ...   -- forward rule
```

To register a theorem that is already defined, use `attribute`. Add `local` to limit the rule to the current section or file:

```lean
section
attribute [local ibubble 50%] baz   -- only inside this section

theorem qux ... := by
  ibubble                          -- may use baz
end
```

Add (`with`) or remove (`without`) rules for one call:

```lean
ibubble with [baz, qux 10%, forward bar]
ibubble without [foo]
```

Copyright (c) 2026 Institute of Science and Technology Austria (ISTA).
Licensed under the Apache License, Version 2.0.
