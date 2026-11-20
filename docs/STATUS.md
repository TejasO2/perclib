# Status

Kept by LEAD under D-34. Last updated 20 November 2026, second LEAD resumption (prover wave 1 briefed).
A new LEAD resumes from this file, [COORDINATION.md](COORDINATION.md) and D-34 in
[DECISIONS.md](DECISIONS.md).

## Gate

**Latest: green on `eb09ac5`** (`scripts/gate.sh`; build, axiom audit, closure, scan,
tests, extract; change classified proof-only against `4c72765`). Kernel replay last run on
the baseline below.

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

Workers are started by ARCHITECT from briefs that LEAD writes to
`/home/user/reports/briefs/<id>.md` (container-local); each worker reads
`/home/user/reports/PREAMBLE.md` and reports to `/home/user/reports/<id>.md`. Worktrees
are `/home/user/wt/<id>` on branch `work/<id>` of the repository named in the brief.
Package ids from the first session (`pub-*`, `link-*`, scouts) are as listed in the
previous version of this file.

**Merged**
- `hygiene-info` (`99f189f`, merged `eb09ac5`): four `Try this` messages removed.
  Proof-only against `4c72765`; gate passed on `eb09ac5`.
- `pub-scan` (lrp `dc23231`, merged lrp `5a2943b`): `scripts/draft_overlap.py` and
  `wiki-overlap-hits.json` in the private repository.

**Finished, reports read**: `salvage-scan`, `hier-map` (the hierarchical programme as
packages H0–H9), `link-longrange`, `link-analysis` (awaiting their audits).

**Running (wave 1)**: `d33-map`, `link-bond-core`, `link-bond-sub`, `link-probability`,
`link-models`, `pub-audit`, `audit-link-longrange`, `audit-link-analysis`.

**Prover wave 1, briefs ready** (disjoint new files, proof-only):

| Id | Files | Target |
|---|---|---|
| `hier-kernel` (H1) | `Models/HierarchicalPowerKernel.lean` | power-law kernel row bounds, `β_c ≥ (L^α-1)/(C(1-L^{-d}))`, transitivity hypotheses |
| `hier-translate` (H3) | `Models/HierarchicalTranslation.lean` | non-radial R11/R12 and the Prop 2.10 reduction |
| `hier-sibling` (H6) | `Models/HierarchicalSibling.lean`, `Percolation/Bond/CrossEdge.lean` | Lemma 2.8 (655W recursion); critical path |
| `salvage-analysis` | `Analysis/LaplaceUniqueness.lean`, `Probability/ChiSquareDeterminacy.lean`, `Analysis/RiccatiBootstrap.lean` | rebase three private branches (Q-188, Q-154, Q-149) |

**Startable next, brief ready**: `hier-quantile-finite` (H2,
`Percolation/Bond/Tightness/RestrictQuantile.lean`).

**Queued** (hierarchical dependency order from `hier-map`): H0 `hier-stmt` (interface:
`Prop` statements of Theorem 1.1 and W498 in `Models/Hierarchical/Defs.lean`, needs an
audit and a new wiki tag for Theorem 1.1); H4 `hier-runaway` after H1; H5
`hier-endpoint` after H1, H2, H4; H7 after H5, H6; H8 Theorem 1.1 after H0, H3, H5–H7;
H9 W498 after H8. Then salvage tier 2 (Q-211, Q-195, Q-194, restated for the
`Seminorm` kernel API), `attach-<area>` after each link audit, and `pub-move` after
`pub-audit`.

Concurrency: at most 4 provers building single modules; no full build or kernel
replay while they build. Merges are batched and gated by LEAD.

## For ARCHITECT

Nothing that meets the D-34 escalation test in prover wave 1 (all four packages add
theorems only). Coming up, LEAD's decision unless ARCHITECT objects: the salvage branches
Q-81 (Galton–Watson definitions) and Q-10 (uniqueness definitions) add new definitions;
LEAD will take them only with a fresh audit and only if no existing notion covers them.

## For Tom

- The 194 provisional errata entries in the wiki await his confirmation (D-30).
- Issue-52 reading of universal tightness (`k ≥ 1` where the source prints `k ≥ 0`, false at
  `k = 0`): still his ruling; the hierarchical programme uses only `k ≥ 1`.
- arXiv 2103.17013v1 Prop. 2.12(ii) states `E_{β_c}|K_n| ≥ L^{αn}` with constant 1; the
  flux argument gives the factor `(L^α-1)/(β_c C (1-L^{-d}))`. Already a provisional
  erratum; the Lean target keeps the factor.
- The wiki remark under W498 that radiality matters for the pointwise bound looks
  misleading (the wiki's own 7YNX argument does not use it); to be reworded when the
  article is next touched.
