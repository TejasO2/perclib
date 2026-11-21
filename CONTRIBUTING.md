# Contributing to PercLib

PercLib is a Lean 4 / mathlib library of percolation theory, proved from the axioms, led
by Tom Hutchcroft. Most of the work is done by AI assistants, and this page is written so
that you can hand it to yours; people are equally welcome and follow the same rules. It
assumes only a clone of the repository and a GitHub account: you can find a task, do it
and check it without anybody being online. Merging still needs a maintainer for now
(section 5).

The repository is `tomhutchcroft/perclib`. Work in your own fork (or a branch you own),
branched from **`main`**, and reach `main` only by pull request. Read
[AGENTS.md](AGENTS.md) first: it has the build commands and the rules for the Lean.

## 1. How to choose a task

- **The task board** will be the directory `tasks/`: `tasks/open/<task-id>.md` will hold
  tasks ready to start, each giving the files you own, the exact target statement, the
  allowed inputs, the stop condition and whether it is proof-only or interface;
  `tasks/README.md` will explain the board, and tasks labelled `good-first-task` are a
  good start. The board is being set up and is not yet in the repository; until it is,
  use the frontier.
- **The frontier**, `docs/FRONTIER.md`, is generated from the library's manifest and
  lists wiki assertions not yet proved whose prerequisites are all proved. Use it for
  work no task covers; open an issue describing the statements before a large piece of
  such work, so that it does not duplicate work in progress.
- **Areas taken.** The lace-expansion articles (`wiki/articles/`: lace-expansion,
  lace-coefficient-diagrams, weighted-lace-coefficients, higher-lace-moments,
  planar-lace-moments, planar-pointwise-lace, spatial-lace-coefficient-bounds,
  two-mark-first-coefficients, bootstrap-diagram-bounds, fourier-bootstrap,
  completed-fourier-bootstrap, tilted-fourier-bootstrap, infrared-diagrams,
  triangle-condition) are being formalised by Codex, a contributor working for Tom. Its
  map of the area is [`tasks/areas/lace-expansion.md`](tasks/areas/lace-expansion.md)
  (being written). Other contributors coordinate there, by an issue or a draft pull
  request that links it, before starting work in that area. Shared prerequisites outside
  those articles (BK inequality, tree-graph bounds, Fourier and convolution lemmas, the
  two-point function API) are open to everyone.

## 2. Claim it

1. Check the [open pull requests](../../pulls): a task is taken if an open pull request's
   title begins with its id.
2. Claim by opening a **draft pull request** against `main` whose title begins with the
   task id, for example `<task-id>: short description`. An empty first commit is fine.
3. A draft with no push for **seven days** is free to take over: open your own draft and
   link the old one.

## 3. Do it

Follow [AGENTS.md](AGENTS.md) and the task file. Build only the modules you change
(`lake build --wfail PercLib.Area.YourFile`); commit whenever something compiles. If the
target turns out false, vacuous or to need a hypothesis its source lacks, **do not alter
it**: stop and open a "Mathematical gap" issue (section 6) with the counterexample, and
link it from your pull request. In the pull request that completes a task, move its file
from `tasks/open/` to `tasks/done/` (`git mv`); change nothing else under `tasks/`.

## 4. Open the pull request

Mark it ready for review when it is done. The description follows
[the template](.github/pull_request_template.md) and states:

- the task id (or the frontier tag / issue it addresses);
- what was proved: declarations added, each with its tag if it has one, and whether it is
  proved or proved modulo named `…Input` hypotheses;
- tags added or changed;
- the lemmas you searched for, in mathlib and in PercLib, and what you found;
- the gate result: the commit you ran `scripts/gate.sh` on and its final lines, pasted
  (see "Running the gate locally" in [AGENTS.md](AGENTS.md)); CI is being added; until it
  runs on your pull request, this is the only automatic check a reviewer sees;
- **interface changes**: every new or changed definition, structure, class, instance,
  notation or tagged statement, and any change outside `PercLib/`. If there are none,
  say "none (proof-only)".

One coherent group of results per pull request; small and early is better than large and
late. Interface changes and proofs go in separate pull requests, the interface first.

## 5. Checks and merging

> **Today: CI is being added; no auto-merge.** The CI workflow (build and checks only) is
> being added to `main`; the auto-merge workflow is still under review. Until they are, run the gate locally (the commands in
> [AGENTS.md](AGENTS.md), "Running the gate locally") and paste its final lines into the
> pull request. Every pull request is merged by a maintainer, Tom Hutchcroft, even when
> it is proof-only and the gate passes.

**What CI checks** (being added): on every pull
request,

- `gate`: `scripts/gate.sh` against the merge base: full `lake build --wfail`, axiom
  audit (`scripts/AxiomAudit.lean`), import closure, forbidden-construct scan, the
  classifier's unit tests, manifest extract, D-35 checks (tagged statements, headers and
  docstrings of new files), and the classification of the change as `proof-only` or
  `interface`, which it will apply as a label;
- `kernel-replay`: every module replayed through `leanchecker`, for pushes and for
  interface changes;
- `scripts`: the unit tests of the tooling in `scripts/`;
- `wiki`: the wiki build.

**What will merge without review, once auto-merge is active** (not yet). A *proof-only*
pull request: it touches only `.lean` files under `PercLib/` (and `PercLib.lean` import
lines), changes no definition, no tagged statement and no `Basic.lean`/`Defs.lean`, and
nothing under `scripts/`, `.github/`, `tasks/` (other than moving its own task to
`tasks/done/`) or the pins (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`).
The kernel and the axiom audit are its check. The planned auto-merge workflow will merge
such a pull request on green CI only if its author is listed in a file of authors under
`.github/` that Tom maintains; it also needs repository settings only Tom can make.

**Everything else waits for review**, then and now: interface, wiki and tooling pull
requests, and proof-only pull requests by authors not on that list. They need the
approval of a maintainer (Tom Hutchcroft, and any collaborators he later names in a
`CODEOWNERS` file) or of the project's auditing agent when it is running. Make exactly
the numbered changes a review asks for and push; a statement whose fidelity to its
source is in real doubt waits for Tom.

## 6. Issues

Use the issue templates:

- **Mathematical gap** (`math-gap`): a target or tagged statement that is false, vacuous
  or under-hypothesised. Give the statement (tag and Lean name), its source with an exact
  locator, and the counterexample or the missing hypothesis.
- **Definition proposal** (`definition-proposal`): a notion that recurs, or that mathlib
  lacks. Give the definition, where it would live (`Basic.lean`/`Defs.lean`), the sites
  that would use it, and its planned API.
- **Question** (`question`): anything else about scope, rules or tooling.

## Licence and credit

Lean code and tooling are under Apache-2.0 (see `LICENSE`). By opening a pull request you
agree that your contribution is licensed on those terms. Contributors are credited in the
commit history; adapted code names its source, revision and licence in its file header.

## A prompt you can give your assistant

```text
You are contributing to PercLib (github.com/tomhutchcroft/perclib), a Lean 4 / mathlib
library of percolation theory proved from the axioms. Read AGENTS.md and CONTRIBUTING.md
in the repository and follow them exactly; docs/COORDINATION.md and docs/DECISIONS.md
give the detailed rules and their reasons. Pick a task from tasks/open/ (prefer
good-first-task if you are new), or from docs/FRONTIER.md while tasks/ does not exist,
that no open pull request has claimed and that is not in an area CONTRIBUTING.md lists as
taken; claim it with a draft pull request against main titled "<task-id>: ...", from a
branch of main in your fork. Build only the modules you change, after
`lake exe cache get`. CI is being added: before marking the pull request ready, run
scripts/gate.sh as AGENTS.md describes and paste its final lines into it. Never use
sorry, admit, axiom or native_decide; never redefine an existing notion; never alter a
tagged statement to make a proof close (report a counterexample in a math-gap issue
instead); never mix definitions and proofs in one pull request; never change the
toolchain, the lakefile, scripts/ or .github/. Fill in the pull request template, mark
the pull request ready when done, and make exactly the changes a review lists.
```
