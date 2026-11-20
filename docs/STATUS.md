# Status

Kept by LEAD under D-34. Last updated 20 November 2026, end of the first LEAD session.
A new LEAD resumes from this file, [COORDINATION.md](COORDINATION.md) and D-34 in
[DECISIONS.md](DECISIONS.md).

## Gate

**Baseline green** on `4c72765` (integration branch `claude/zen-lovelace-rvlcw2`;
its Lean tree is identical to the snapshot `f849aa9`). Local verification, not CI:

| Check | Command | Result | Time |
|---|---|---|---|
| Build | `lake build --wfail` | passed, 3,828 jobs, no warnings | 4 min 23 s cold, 2 min 19 s whole gate warm |
| Axiom audit | `lake env lean --run scripts/AxiomAudit.lean` | passed, 4,816 constants, only `propext`, `Classical.choice`, `Quot.sound` | 52 s |
| Import closure | `python3 scripts/check_import_closure.py PercLib` | passed, 250 modules | <1 s |
| Forbidden scan | `python3 scripts/check_forbidden.py PercLib` | passed, 250 files | <1 s |
| Classifier tests | `python3 scripts/test_proof_pr.py` | passed, 5 tests | <1 s |
| Extract | `lake env lean --run scripts/ExtractManifest.lean` | 4,816 declarations, 71 tagged | 74 s |
| Kernel replay | `scripts/kernel_replay.sh 12` | passed, 249 modules | 14 min 9 s, peak about 9.7 GB |

All of it is `scripts/gate.sh <tip>` except the kernel replay. The extract of `4c72765`
is saved at `.lake/gate/4c72765…json` in this container only; a new container regenerates
it by running `scripts/gate.sh` on the tip before classifying the next change.

Build output carries four `info: Try this` messages (LogScaling 272, UniformConvergence
605, HierarchicalGeometry 81, LongRange/Convolution 42): not warnings, but a hygiene
package below removes them.

## Machine

4 cores, 15 GB, no swap. A full build uses all 4 cores; `lake build` of one module plus
its dependents is the prover's unit. `leanchecker` on all modules in one process was
killed for lack of memory; batches of 12 peak at about 9.7 GB, so the kernel replay runs
only when no prover builds. Mathlib is fetched once into `.lake/packages` of the main
checkout (`lake exe cache get`, about 8 min); worktrees symlink `.lake/packages` to it.
Planned concurrency: 3 provers building single modules, no full build while they run.
Throughput: none measured yet (no worker has run in this session).

## Wiki

The wiki draft of 20 November (revision `3873524`, 142 articles, 1,401 active tags, 40
tombstones, 194 provisional errata in 29 sources, 157 reading maps) is committed in the
private repository at `1fe07bc` on its `claude/zen-lovelace-rvlcw2`; `npm ci && npm run
build` in `wiki/` passed there (76 tests, all links and mathematics validated).

The manifest built in the private repository from the extract of `4c72765` and the wiki
catalogue (`scripts/build_manifest.py`, 20 s) gives, over 1,401 assertions: 65 `proved`,
6 `statement-only`, 1,330 `unformalised`. A preliminary work frontier computed from the
wiki's authored `proof_uses` records (954 assertions carry one) has 132 assertions, 111
of them with no recorded prerequisite. This is before step 2 links existing
declarations, which will move many assertions to `proved` and enlarge the frontier.

Tom's ruling of 20 November (amendment to D-34 and D-32): the wiki becomes public in
`perclib/wiki/` after the publication check; the book draft never does. No wiki file is
in this repository yet. The check has not run.

## Packages

Nothing is in progress: this session had no means to start worker agents. Every package
below is startable; briefs are kept by ARCHITECT for this session. Package ids are the
`work/<id>` branch names.

| Id | Kind | Repository | What | Depends on |
|---|---|---|---|---|
| `pub-scan` | worker | lrp | Overlap scan script (12+ shared words after normalising TeX) of every wiki file against the book draft and its notes; run it; commit the script and hit list in lrp | none |
| `pub-audit` | auditor | lrp | Classify every hit and every notes-facing page as fine, rewrite or withhold; check private links, hashes, emails, old issue links | `pub-scan` |
| `pub-move` | wiki | both | Apply rewrites in lrp, copy what passed to `perclib/wiki/` with an all-rights-reserved notice, move `build_manifest.py`, `test_manifest.py`, `MANIFEST.md`; local manifest receipt for the wiki build | `pub-audit`, LEAD sign-off |
| `link-<area>` (6) | scout | perclib (read), lrp wiki (read) | Propose tag-to-declaration matches area by area from the reading maps | none |
| `audit-link-<area>` (6) | auditor | — | Check each proposed match statement against statement | matching scout |
| `attach-<area>` | LEAD | perclib | Add `@[tag]` to audited matches; gate; rebuild manifest and frontier | matching audit |
| `hygiene-info` | prover | perclib | Replace the four `Try this` calls by the suggested tactic | none |
| `salvage-scan` | scout | lrp (read) | List unmerged `work/*` branches on the private remote (105 refs not ancestors of `main`) with compiled Lean worth porting | none |
| `d33-map` | scout | lrp (read) | Map the D-33 source (private remote `refs/pull/488/head`, `d382e4c`, 281 files, about 92K lines) against what is in `PercLib/Models/LongRange`; list portable files in dependency order | none |
| `hier-map` | scout | perclib, lrp wiki | State of the hierarchical two-point theorem: tagged targets, `Input`s, what remains | none |

Areas for `link-*`: `bond-core` (`Percolation/Bond/*.lean`, top level), `bond-sub`
(`Percolation/Bond/*/`), `probability` (`Probability/`), `models` (`Models/*.lean`,
`Models/Site`), `longrange` (`Models/LongRange`), `analysis` (`Analysis/`,
`Combinatorics/`).

## For ARCHITECT

Nothing that blocks work. One note: the session that ran as LEAD had no tool to start
agents, so step 1 was done directly and the wave plan returned to ARCHITECT.

## For Tom

Nothing new from this session. The 194 provisional errata entries in the wiki await his
confirmation as before (D-30).
