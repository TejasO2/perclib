# Working on PercLib

PercLib is a Lean 4 / mathlib library of percolation theory, proved from the axioms. This
file is the entry point for any assistant or person working here, and with
[CONTRIBUTING.md](CONTRIBUTING.md) it is all you need: it has the build and gate commands
and the rules for the Lean. The workflow (tasks, areas taken by other contributors,
claims, pull requests, checks, merging, issues) is in [CONTRIBUTING.md](CONTRIBUTING.md); the
detailed rules are in [docs/COORDINATION.md](docs/COORDINATION.md); the reasons are in
[docs/DECISIONS.md](docs/DECISIONS.md) (later decisions override earlier ones; D-35 and
D-37 are the current rules). Where `docs/COORDINATION.md` or `docs/DECISIONS.md`
describe the project's internal roles (ARCHITECT, LEAD, workers, `work/<package>` branches, who runs full builds), they
do not bind outside contributors; where they differ from this file or CONTRIBUTING.md, these two files win.

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

- Before opening a pull request, run the gate locally (next section) and paste its final
  lines into the pull request.

## Running the gate locally

**CI is being added; auto-merge is not active.** The CI workflow (build and checks only) is
being added to `main`; the auto-merge workflow is still under review. Until they are, the gate you run yourself is the only automatic
check: run it before you mark a pull request ready, and paste the commit it ran on and its
final lines (`== gate passed on <sha>` and any `NOTICE:` line, or the failure) into the
pull request. Every pull request is merged by a maintainer (see
[CONTRIBUTING.md](CONTRIBUTING.md), section 5).

You need only a clone, `git`, `python3` (standard library only) and
[elan](https://github.com/leanprover/elan); `lake` then selects the pinned toolchain
from `lean-toolchain`. From the repository root:

```sh
lake exe cache get              # once per clone (and after a pin change): mathlib's build
lake build --wfail              # full build of PercLib, warnings are errors
```

The gate is `scripts/gate.sh [BASE]`. It classifies your change by comparing it with a
saved extract of the base, `.lake/gate/<base sha>.json`, which only a gate run on the base
itself writes (and only when `PercLib/` has no uncommitted changes). So bring your branch
up to date with `main` (merge or rebase), then run it twice in the same clone:

```sh
git switch main && scripts/gate.sh                 # writes .lake/gate/<main sha>.json
git switch your-branch && scripts/gate.sh main     # the gate on your change
```

If no extract of the base exists (for example because `main` does not yet have
`scripts/gate.sh`), the gate prints `NOTICE: no saved extraction for base …;
classification skipped` and your change is treated as an interface change. The steps, in
order; the gate stops at the first failure:

1. `lake build --wfail`: the whole library compiles with warnings (including mathlib's
   standard linters set in `lakefile.toml`) as errors.
2. `lake env lean --run scripts/AxiomAudit.lean`: every constant under `PercLib` uses no
   axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
3. `python3 scripts/check_import_closure.py PercLib`: every file under `PercLib/` is
   imported, directly or transitively, by `PercLib.lean` (an unimported file is never
   compiled).
4. `python3 scripts/check_forbidden.py PercLib`: no forbidden construct (rule 1 below)
   outside comments and strings.
5. `python3 scripts/test_proof_pr.py`: unit tests of the proof-only classifier.
6. `lake env lean --run scripts/ExtractManifest.lean`: the manifest of declarations,
   tags and dependencies, saved under `.lake/gate/` when the tree is clean.
7. `python3 scripts/check_d35.py`: no tagged `Prop` definition is used as a hypothesis
   and its proofs carry its tag; files not listed in `scripts/legacy_headers.txt` have a
   module docstring and no task, issue, agent or decision labels in their headers.
8. With `BASE`: `scripts/check_proof_pr.py` classifies the change as proof-only or
   interface. An interface change prints `NOTICE: interface change; an auditor must
   approve before merge.` and still exits 0: it needs review, it is not a failure.

**Memory and time.** A full build needs several GB of memory and, from the downloaded
mathlib cache, about 4.5 minutes on 4 cores; run one build or gate at a time on a machine
and never two in parallel. The kernel replay, `scripts/kernel_replay.sh 6`, is separate
from the gate and optional for contributors: it replays every module through
`leanchecker`, 6 modules per process at about 4 GB each, and must not run beside a build.
Never run `lake env leanchecker PercLib`: one process needs more than 15 GB and is killed.

**What CI checks** (being added): on every pull request it will run
`scripts/gate.sh` against the merge base, the kernel replay (for pushes and interface
changes), the unit tests of `scripts/`, and the wiki build, and label the pull request
`proof-only` or `interface`. Until then, the commands above are the check.

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
