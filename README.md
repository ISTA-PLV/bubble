# Bubble

Bubble provides `ibubble`, a proof-search tactic for Iris Lean. For its design and search algorithm, see our [paper](https://yunsongyang.com/files/bubble.pdf).

```lean
import Bubble
open Iris BI

variable {PROP : Type} [BI PROP] (P Q : PROP)

example : P -∗ □ (P -∗ Q) -∗ Q := by
  ibubble
```

Use `ibubble?` to print the proof script that `ibubble` finds. You can then paste the script in place of the call to reuse the proof.

## Pure goals

When the search reaches a pure Lean goal `⌜φ⌝`, it runs a solver on `φ`.

- `ibubble`: uses `assumption` (the default).
- `ibubble pureBy <tac>`: uses `<tac>`, e.g. `ibubble pureBy simp [*]`. A branch fails if `<tac>` does not close the goal.
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
@[ibubble 75%] theorem wpi_get ...          -- backward rule
@[ibubble forward 50%] theorem foo ...      -- forward rule
```

To register a theorem that is already defined, use `attribute`. Add `local` to limit the rule to the current section or file:

```lean
section
attribute [local ibubble 50%] lemmaX   -- only inside this section

theorem thm ... := by
  ibubble                                       -- may use lemmaX
end
```

Add (`with`) or remove (`without`) rules for one call:

```lean
ibubble with [StepMod.mono, wpi_wand 10%, forward foo]
ibubble without [wpi_wand]
```

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

Copyright (c) 2026 Institute of Science and Technology Austria (ISTA).
Licensed under the Apache License, Version 2.0.
