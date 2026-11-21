# Working on PercLib

PercLib is a Lean 4 / mathlib library of percolation theory, proved from the axioms. This
file is the entry point for any assistant or person working here. The workflow (tasks,
claims, pull requests, CI, merging, issues) is in [CONTRIBUTING.md](CONTRIBUTING.md); the
detailed rules are in [docs/COORDINATION.md](docs/COORDINATION.md); the reasons are in
[docs/DECISIONS.md](docs/DECISIONS.md) (later decisions override earlier ones; D-35 and
D-37 are the current rules).

## Start

- Branch from `main` (in your fork if you cannot push here). Never push to `main` or to a
  branch that is not yours.
- Use the pinned toolchain (`lean-toolchain`) and pinned mathlib (`lake-manifest.json`).
  Never upgrade them, and never rebuild mathlib from source:

```sh
lake exe cache get                         # once: download mathlib's build
lake build --wfail PercLib.Area.YourFile   # while working: only the modules you changed
python3 scripts/check_forbidden.py PercLib # forbidden-construct scan (seconds)
```

- Before opening a pull request, if your machine has the memory, run the gate. It needs
  the saved extract of the base, so run it on `main` first:

```sh
git switch main && scripts/gate.sh                  # saves .lake/gate/<main sha>.json
git switch your-branch && scripts/gate.sh main      # build, axiom audit, import closure,
                                                    # forbidden scan, classifier tests,
                                                    # extract, D-35 checks, classification
```

  A full build from a warm mathlib cache takes about 4.5 minutes on 4 cores. Kernel
  replay is `scripts/kernel_replay.sh 6` (6 modules per process, about 4 GB each). Never
  run `lake env leanchecker PercLib`: one process needs more than 15 GB and is killed.
  CI runs all of this on your pull request anyway.

## Rules for the Lean

1. **Forbidden:** `sorry`, `admit`, `axiom`, `native_decide`, code that runs at
   elaboration time (`#eval`, `elab`, `macro`, `syntax`, `initialize`, `run_cmd`, ...),
   `set_option maxHeartbeats`, `set_option linter.*`. Only the axioms `propext`,
   `Classical.choice` and `Quot.sound` are allowed.
2. **Bond interface (D-2).** A configuration on `V` is a `Set (Sym2 V)`, its law is
   `PercLib.Probability.prodBernoulli q`, the open graph is `SimpleGraph.fromEdgeSet ω`,
   row sums use `rowSum` from `PercLib/Percolation/Bond/Basic.lean`. Everything lands on it.
3. **Search before writing.** For any lemma that does not mention percolation, search
   mathlib by name and by type (`exact?`, `rg` in `.lake/packages/mathlib`) and search
   `PercLib`; say in the pull request what you searched. A private copy of an existing
   lemma is rejected: import it.
4. **Definitions** go only in files named `Basic.lean` or `Defs.lean`, never duplicate a
   notion of this library or mathlib, and land with their API: evaluation and membership
   lemmas, `@[simp]` where in normal form, `ext` for structures, monotonicity, the trivial
   case. If you would spell out the same predicate or quantity a third time, propose a
   definition (a small interface pull request); this is encouraged.
5. **Generality when it is free:** state a lemma at the generality its proof supports
   (arbitrary index type or measure, general profile, a `SimpleGraph`); the
   percolation-facing form is a corollary. Use mathlib's notions through mathlib's API.
   A theorem with more than ten hypotheses needs a stated reason; a recurring group of
   hypotheses becomes a structure.
6. **Names follow mathlib:** the name describes the conclusion, hypotheses via `_of_`,
   the most specific namespace that gives dot notation. No tag, task or issue id in a
   declaration name.
7. **Tagged statements.** `@[tag "XXXX"]` (see `PercLib/Meta/Tag.lean`) links a
   declaration to a wiki assertion. Files in `Tags/` directories are a correspondence
   layer: they restate library lemmas and add no mathematics; each conjunct of a tagged
   conjunction is also a named lemma in the area file, and other code uses that lemma.
   A tagged `Prop` statement is never a hypothesis; its proof carries the same tag.
8. **Never narrow a tagged statement**, or a definition it uses, to make a proof close.
   If it is false, vacuous or needs a hypothesis its source lacks, stop and report it
   (issue template "Mathematical gap"). Narrowing is for helper lemmas only.
9. **Literature results** are used only as explicit hypotheses bundled in a structure
   named `…Input`, listed in `docs/CITED_INPUTS.md`; such a result is "proved modulo",
   never "proved". Hypotheses that are not obviously satisfiable ship with a compiled
   `example` showing they can hold (D-5).
10. **Files.** Every new module is imported from `PercLib.lean` (one line, alphabetical),
    starts with `module` and uses `public import`. After the imports comes a module
    docstring `/-! # Title ... ## Main results -/`. The header carries the copyright,
    provenance of adapted code (source, revision, licence) and the mathematical
    reference only: no task, issue, agent or decision ids (those go in the commit
    message).
11. **Interface and proofs are separate pull requests.** Never mix definitions, tagged
    statements, `.github/`, `scripts/` or pin changes with proofs.
12. **Honesty.** A compilation claim refers to a build that ran on the stated commit.
    Call anything else an uncompiled draft.

## Reviewing a pull request

Do not review proof bodies or helper lemmas: the kernel, `lake build --wfail` and the
axiom audit check them. Check, and treat any defect as blocking: every new or changed
definition, instance and notation (right notion? duplicate? API present?); every tagged
statement, by a binder table: each binder, including fields of project structures it
unfolds to, is SOURCE (a premise of the assertion or cited source), TYPING, RULED (a
recorded erratum) or EXCESS, and any EXCESS fails; the order of existential quantifiers
against every parameter a constant must not depend on; vacuity and missing witnesses;
headers of adapted code; mixing of interface, tooling and proofs. State the verdict with
the full commit sha reviewed, and list required changes as numbered concrete edits. Do
not ask for cosmetic changes no check enforces.
