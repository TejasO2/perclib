# perclib

Mathematical formalisations in Lean 4 using mathlib.

## Plan

The current plan is in [docs/ROADMAP.md](docs/ROADMAP.md), the decisions behind it in [docs/DECISIONS.md](docs/DECISIONS.md), and the working rules in [docs/COORDINATION.md](docs/COORDINATION.md). The other files in `docs/` are background reference.

## Build

Install [Lean using elan](https://lean-lang.org/install/), then run:

```sh
lake exe cache get
lake build --wfail
```

The project pins Lean **4.35.0**, mathlib **4.35.0**, and all dependency revisions.
Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` in sync when deliberately updating dependencies.

## Layout

- `PercLib/`: definitions and proofs.
- `PercLib.lean`: imports every project module that the default build should check.
- `PercLib/Basic.lean`: a small initial theorem, `PercLib.two_mul_le_add_sq`, proving `2 * a * b ≤ a ^ 2 + b ^ 2` for real numbers.

Add each new proof module to `PercLib.lean` so `lake build` checks it.

## Automated verification

This public repository has no GitHub Actions workflows yet; continuous integration will be added in a separate pull request. This snapshot was checked before publication: it builds with warnings treated as errors, and an audit of the axioms of declarations in namespace `PercLib` allows only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. This rejects `sorry`/`admit` placeholders and additional axioms in completed proofs.

The initial inequality is a build check for the environment; no research theorem has been formalised yet.
