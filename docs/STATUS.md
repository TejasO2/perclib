# Status

Kept by LEAD under D-34. Last updated 20 November 2026, third LEAD resumption (first link batch merged).
A new LEAD resumes from this file, [COORDINATION.md](COORDINATION.md) and D-34 in
[DECISIONS.md](DECISIONS.md).

## Gate

**Latest: green on `fc917ec`** (`scripts/gate.sh`: build, axiom audit of 4,865 constants,
closure of 262 modules, forbidden scan, tests, extract). It merges `hier-translate`,
`attach-analysis`, `attach-longrange` and the root imports. Interface change (27 tags),
approved by the fresh audits `audit-link-analysis` and `audit-link-longrange`; LEAD
spot-checked wrappers 6PGV and JK7V against the audit text. Kernel replay last run on the
baseline below. Earlier: green on `eb09ac5`.

**Manifest after this batch** (private repository, from the `fc917ec` extract): 92
`proved`, 6 `statement-only`, 1,303 `unformalised` (was 65 / 6 / 1,330); 99 `@[tag]`
attributes in `PercLib/`. Preliminary frontier (authored `proof_uses`): 135.

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
- `hygiene-info` (`99f189f`, merged `eb09ac5`).
- `pub-scan` (lrp `dc23231`, merged lrp `5a2943b`).
- `hier-translate` (H3, `273ee65`, merged `d31df2d`): non-radial R11/R12 and the Prop 2.10
  reduction, `PercLib/Models/HierarchicalTranslation.lean`, proof-only.
- `attach-analysis` (`835e077`, merged `3688361`): 9 tags attached, 8 wrappers in
  `PercLib/Analysis/Tags/`.
- `attach-longrange` (`acf3acb`, merged `422070e`): 2 tags attached, 8 wrappers in
  `PercLib/Models/LongRange/Tags/`.

**Finished scouting**: `salvage-scan`, `hier-map`, `d33-map` (32 port packages, 14
startable), all six `link-*`, audits `audit-link-analysis`, `audit-link-longrange`,
`audit-link-bond-sub`, `pub-audit`.

**Running**: provers `hier-sibling` (H6), `hier-kernel` (H1), `hier-quantile-finite` (H2),
`salvage-analysis`; `attach-bond-sub`; auditors `audit-link-models`,
`audit-link-probability`, `audit-link-bond-core`; `pub-move` (perclib `work/pub-move`;
LEAD reruns the overlap scan and greps on its tree before any merge).

**Briefs ready** in `/home/user/reports/briefs/` (disjoint files, none overlapping running
work):

| Id | Kind | Files | Target |
|---|---|---|---|
| `hier-stmt` (H0) | interface | `Models/Hierarchical/Defs.lean`, `…/Witness.lean` | `Prop` statements of Theorem 1.1 and W498 (tagged), D-5 witness; needs audit |
| `lrp-rv-geninv` | D-33 port 1 | `Analysis/RegularVariation/GeneralInverse.lean` | inverse regular variation, Karamata tail |
| `lrp-tauber-laplace` | D-33 port 9 | `Analysis/Tauberian/Laplace.lean` | Laplace half of the Tauberian chain to I.2.11 |
| `lrp-I413` | D-33 port 4 | `Analysis/RegularVariation/LogErrorTransforms.lean` | Lemma I.4.13 |
| `nm-analysis` | near-miss | `Analysis/Tags/MarginalODETail.lean`, `Combinatorics/Tags/ForestConnections.lean` | K58A, 4K33 in full; needs audit |
| `nm-longrange` | near-miss | `Models/LongRange/Tags/CutsAndRows.lean` | ZH13, R01V in full; needs audit |

**Queued** (hierarchical dependency order from `hier-map`): H4 `hier-runaway` after H1; H5
`hier-endpoint` after H1, H2, H4; H7 after H5, H6; H8 Theorem 1.1 after H0, H3, H5–H7;
H9 W498 after H8. D-33 next: packages 2, 23 and 29 wait for `salvage-analysis` (Q-154 and
Q-149 overlap them), 25, 26, 19. Then salvage tier 2 (Q-211, Q-195, Q-194, restated for the
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
