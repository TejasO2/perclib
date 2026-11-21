# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 18:00 UTC, at the end of
coordinator round 5 of a new series (twenty-third coordinator overall; the previous handoff, round 4, is at `180d45f`;
older rounds are in `git log -p docs/STATUS.md`, the long per-round gate records up to round 3 in `git show
47b6ffa:docs/STATUS.md`). A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md),
[COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md) (D-34 to D-37) and `/home/user/reports/RULINGS.md`
(rulings 1-16; obey them). **Rulings 15 and 16 are now met:** task board, contributor docs, CI, auto-merge (merge job
enabled after its final scoped audit APPROVE) and the Pages workflow are all gated (`0e30c75`) and pushed;
`/home/user/reports/READY-FOR-MAIN` is written (Tom has pull request #4 open from the integration branch). Ruling 14
(Codex owns the lace-expansion Lean area; each round `git ls-remote`, fetch outside heads, queue reviews, `git fetch
origin main` and merge it if it moved) stands. Container-local reports and briefs are copied for durability to
`lrp/docs/reports/` at each round's lrp commit (ruling 9i).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `0e30c75`** (pushed; extract
  `.lake/gate/0e30c75….json` saved). On top of it, pushed: `77cf614` (task-board mirror and `docs/FRONTIER.md`, no
  Lean/scripts) and this STATUS commit. **Next gate: `scripts/gate.sh 0e30c75`.**
- **Round 5 (17:30-18:00): one gated batch, passed, pushed.** Started 17:30 (predecessor's STATUS commit 17:29:42;
  tree clean; the only Lean processes were the kernel replay and `mig-model-norm`'s build, each in its own worktree).
  `origin/main` unchanged (`0eb4dc4`, already merged). Merged, in order: `fix-scanner-r5` (`18049a6`),
  `fix-workflows-r6` (`b77968c`, auto-merge with AM6; merge job enabled), `hier-j98j-tag` (`4fd9f49`, J98J),
  `hier-cor12` (`eace6cc`, proof-only, with the audit's one-token merge repair: ` hcC` dropped at
  `HierarchicalTwoPointRadial.lean:65`), `fix-nm-uniform-volume` (`1242118`, XLWI/YVJT), `fix-frontier-four-functions`
  (`c7ca677`, EZJ7), `fix-wiki-revise-proof-sections-a` (`60a4a8a`), `review-pr-2` (`8252109`), `docs-contrib-followup`
  (`0c10038`), `wiki-nc7f-precision` (`2ba2b5f`), `pages-deploy` (`eea6ceb`, after `audit-pages-deploy` APPROVE at
  17:35). Each head equalled its audited commit; merged non-Lean files byte-identical to their branches.
  First gate (`scripts/gate.sh df5d0fd`, log `/home/user/reports/gate-round5.log`) **failed at D-35 check (i)**:
  `hierarchicalTwoPointRadial` proves the tagged Prop W498 but carried no tag (its brief had said "no tag"). Merge
  repair `0e30c75`: one line `@[tag "W498"]` on the theorem (the J98J pattern; the W498 Prop itself is unchanged and
  was audited earlier); a mechanical confirmation audit `004-audit-w498-proof-tag` is queued. Second gate on
  **`0e30c75`** (log `/home/user/reports/gate-round5b.log`): build `--wfail` OK (3,961 jobs), axiom audit 6,663
  constants only `propext`/`Classical.choice`/`Quot.sound`, import closure 368 modules, forbidden scan 368 files,
  script tests, "D-35 checks passed", "INTERFACE change against df5d0fd…: … FiniteRangeDecay.lean: ['def']" (expected:
  audited tags), "== gate passed on 0e30c75…". Wiki: `npm test` 107/107 on the merged tree.
- **Kernel replay (ruling 13b).** Running at `df5d0fd` in `/home/user/wt/replay-df5d0fd` (started 17:24 by the
  predecessor; log `/home/user/reports/replay-df5d0fd.log`; 228/363 at 17:53, survived this round's two gates).
  Next coordinator: `tail` the log; "Kernel replay passed" = pass at `df5d0fd` (record it, `rm` the `.lake/packages`
  symlink, `git worktree remove`, update `READY-FOR-MAIN` and the "For Tom" line, then start a new replay at the newest
  gated commit right after a gate); a checker error names the module ("For ARCHITECT", no further merges until
  understood); if `pgrep -f kernel_replay.sh` is empty with neither line, it was killed: `dmesg | grep -i oom`, restart
  the same way. Last replay that passed: baseline `4c72765`.
- **GitHub and ruling 14c/d.** No GitHub write tool (ToolSearch: none; ruling 13a). `git ls-remote`: `main` `0eb4dc4`;
  `refs/pull/2/head` = `work/lace-foundations` `630d985` (unchanged; reviewed, verdict now on the tip as
  `docs/reviews/pr-2.md`); `refs/pull/3/head` merged; **`refs/pull/4/head` = our integration branch** (Tom opened
  pull request #4 "Claude/zen lovelace rvlcw2"; it follows our pushes); `work/hierarchical-two-point-paper` `be2b9df`
  (unchanged). Open issue #1 (README, fixed on `main`).
- Note: `origin/claude/zen-lovelace-rvlcw2` reached `77cf614` before this coordinator pushed it (something else
  pushed the fast-forward; harmless, but check `git status -sb` before assuming a local commit is unpushed).

Commands (from `/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
scripts/gate.sh <previous-gated-commit>  # build --wfail, AxiomAudit, closure, forbidden, tests, extract
                                         # (.lake/manifest-raw.json; saved .lake/gate/<sha>.json),
                                         # check_d35, proof-only/interface classification
scripts/kernel_replay.sh 6               # leanchecker in batches; never alongside a build
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm test; rm node_modules; rm -rf dist
```

Use the perclib `scripts/build_manifest.py` (as above), not the lrp copy named in COORDINATOR.md. Run the gate in the
background (`nohup scripts/gate.sh … > log &`) and poll `pgrep -f scripts/gate.sh`; this round's warm gate after an
11-branch merge took about 10 minutes beside the replay and two worker builds. The base passed to `gate.sh` must have a
saved extract in `.lake/gate/` (STATUS- or FRONTIER-only commits have none: pass their gated parent). After
`frontier.py` delete `scripts/__pycache__/frontier.*.pyc`. Older worktrees (branches cut before `df5d0fd`) still track
`scripts/__pycache__/*.pyc`: before `git worktree remove` there, `git checkout -- scripts/__pycache__`.

## Progress (D-35 measure)

Round 5 (new series): **5 new assertions proved and merged (J98J, W498 = Corollary 1.2, XLWI, YVJT, EZJ7), 4 tagged
statements audited and merged (J98J, XLWI, YVJT, EZJ7; W498's Prop was audited earlier, its proof-tag confirmation is
queued).** Manifest at `0e30c75` (perclib script): **298 proved, 1 statement-only, 1,104 unformalised, of 1,403**.
Frontier (`docs/FRONTIER.md` regenerated at `0e30c75`): 283 ready, 811 blocked, 11 without recorded prerequisites, 298
proved. Approved and waiting for the next batch: migration (e) (PVA8, MQNP, LF50, 6YYS re-audited), 9YE6.

Round 4 (new series): 10 new assertions proved and merged (RU6O, JZN0, 1C8G, 5LNL, WD2J, H48I, U8CI, K38T, 5U4L,
RZSW), 11 tagged statements audited and merged (those ten plus Q0D1). Manifest at `df5d0fd`: 293 proved, 2
statement-only, 1,108 unformalised, of 1,403.

Round 3 (new series): 7 proved and merged (8IGH, 04ZI, PAFY, QW2L, 57FJ, F75G, 0YH8), 7 audited and merged. Round 2: 1
(KJWA). Round 1: 0 proved, 2 re-audited (BQ44, ZH13). Earlier series: see `git show 180d45f:docs/STATUS.md`.

## Merged in round 5 (new series)

- **Rulings 15c, 16:** `fix-scanner-r5`, `fix-workflows-r6` (auto-merge, merge job **enabled**: `audit-fix-workflows-r6`
  APPROVE, neither (A) nor (B)), `pages-deploy` (`audit-pages-deploy` APPROVE under (B); builds with the compiled
  manifest, `WIKI_REQUIRE_MANIFEST=1`; banner, About, noindex, draft markers, base path `/perclib/`).
- **Lean:** `hier-j98j-tag` (J98J), `hier-cor12` (Corollary 1.2, W498 now proved; V4QQ/YWTU consequences untagged),
  `fix-nm-uniform-volume` (XLWI, YVJT), `fix-frontier-four-functions` (EZJ7), merge repair `0e30c75` (W498 tag).
- **Docs/wiki:** `fix-wiki-revise-proof-sections-a`, `review-pr-2` (`docs/reviews/pr-2.md`), `docs-contrib-followup`,
  `wiki-nc7f-precision`.
- Board mirror `77cf614`; `/home/user/reports/READY-FOR-MAIN` written (the old `.pending` draft renamed `.superseded`).
- Worktrees removed (26): automerge-workflow, docs-contrib-followup, fix-frontier-four-functions, fix-gate-scanner,
  fix-nm-uniform-volume, fix-port-wiki-hier-thm11, fix-scanner-r2…r5, fix-wiki-revise-proof-sections-a,
  fix-workflows(-r2…-r6), frontier-four-functions, hier-cor12, hier-j98j-tag, nm-uniform-volume, pages-deploy,
  port-wiki-hier-thm11, review-pr-2, wiki-nc7f-precision, wiki-revise-proof-sections-a.

## Task board (`tasks/`, ruling 9b, 15a)

**11 open, 12 claimed, 11 done** (below the 20+ that ruling 9b asks for: the next coordinator should write about ten new
public tasks from public material, e.g. from `docs/FRONTIER.md` nearest-first and the held D-33/salvage briefs once
(e) merges). This round: `hier-cor12`, `hier-j98j-tag` to `done/`; to `claimed/` with the note "Being done by the
project's own agents": finite-edge-change-infinite-component, restricted-cluster-strict, two-edge-routes (156),
cluster-boundary-product, isolation-positivity (157), nm-small-intensity (158), connection-kernel-tags (160),
monotone-coupling-tag (161), kernel-comparison-off-diagonal (200), frontier-riccati-linear-error (389),
hier-pointwise-ingredients (170). When a held brief with a public twin is released, move the twin in the same push
(twins listed in `/home/user/reports/scout-held-briefs-e.md` release notes: 210 lrp-I41-mt, 220 lrp-spatial-russo-a,
230 lrp-levy-measures, 240 holley-observable-form + profile-perturbation-bound (+ countable-closed-product with its
item 3)). `scout-held-briefs-e` findings still to act on: (2) open tasks `cluster-second-moment-any-law` and
`cluster-mixed-moments-any-law` both own `ClusterMoments.lean`, `cluster-count-any-law` and
`component-count-edge-insert` both own `ClusterCount.lean` (say so in the task files); (3) `tasks/areas/lace-expansion.md`
§3 rows 70KD/UZ7J cite the old `tau` names (now `connProb`); (4) `isolation-positivity` cites a non-existent mathlib
lemma as a search hint. A board checker (`scripts/check_tasks.py`) is under fix (`005`).

## Finished, not merged (each waits for the item named)

**Ready for the next batch (one gated batch; merge in this order, then `scripts/gate.sh 0e30c75`, push):**
1. **`work/mig-model-norm`** (`d1295a4`, migration (e), `ModelNorm`; PVA8, MQNP, LF50, 6YYS respelled):
   `audit-mig-model-norm` **APPROVE** (fresh, binder tables, compiled old↔new equivalence; four non-blocking
   recommendations at its end). Expect conflicts only in `PercLib.lean` imports (it is based on `e8e790e`). Then move
   (e) in `docs/INTERFACE_CHANGES.md` from "Announced" to "Merged" with the rename table from the audit
   (`seminorm_intCast_pos` → `ModelNorm.intCast_comp_pos`, `norm_sub_pos` → `ModelNorm.intCast_comp_sub_pos`,
   `LongRange.exists_pos_mul_norm_le` deleted for `ModelNorm.exists_pos_mul_norm_le`, `normSeminorm_eq_zero` /
   `euclidean_seminorm_eq_zero` replaced; no deprecated aliases: no outside caller). **This closes window (e)**: then
   release 210, 220, 230, 370, 371 with their notes from `scout-held-briefs-e.md` (append verbatim) and move their twins.
2. `work/nm-multipoint-geometry` (`1a4d0ba`, 9YE6): `audit-nm-multipoint-geometry` APPROVE.
3. `work/wiki-revise-proof-sections-b` (`352ad97`; triangle-condition, triangle-susceptibility, finite-random-graphs,
   `wiki/migration-baseline.json`): `audit-wiki-revise-proof-sections-b` APPROVE (npm 100/100). Check merged wiki files
   byte-identical to `352ad97`; run `npm test`. Then a critic re-read of these three (one critic at a time).
4. `work/wiki-revise-regular-variation-r2` (`6ca5601`): mechanical `audit-wiki-revise-regular-variation-r3` PASS (one
   recommended wording fix in the new notation sentence); third critic read `007-critic-reread-regular-variation-r3`
   queued: merge after it passes (or on its residual list going "For Tom", ruling 7's three-round limit).

**Waiting for audits / fixes:**
- `work/fix-nm-tree-depth` (merge `704fd9e`, fix `8fb0e70`; contains `nm-tree-depth`, GGH2 + UHVH): re-audit
  `006-audit-nm-tree-depth-r2` released.
- `work/tooling-task-board-check` (`5704b1b`): audit APPROVE WITH CHANGES (4 required); fix `005` startable, re-audit
  `HOLD-audit-tooling-task-board-check-r2` written.
- `critic/proof-sections-a-r2.md`: `size-biased-laws` PASS; `branching-random-walk` (3 items) and `marginal-ode` (1)
  NOT PASS: reviser `wiki-revise-proof-sections-a-r3` claimed (round 3 of 3), audit
  `HOLD-audit-wiki-revise-proof-sections-a-r3` written (release with a third critic read of the two articles).
- `critic/proof-sections-c.md` (`adaptive-three-point`, `critical-exponents`): finished; **reviser brief not yet
  written** (one reviser at a time: write it when `wiki-revise-proof-sections-a-r3` is done).
- `scout-defs-2` (`/home/user/reports/scout-defs-2.md`): six notions assessed; recommends interface packages for
  kernel transitivity (then a fold migration), `chiCriticalIntensity` (small, with fold), the set-level pivotal event
  (then a fold), `kTree`/`reachDepth` (after `fix-nm-tree-depth` merges); off-diagonal agreement: use mathlib
  `Set.EqOn … Sym2.diagSetᶜ`, no new definition; edge-set connectivity: not now. Not yet briefed: the next coordinator
  writes the `chiCriticalIntensity` package first (smallest; tag 5LNL respelled, audit needed), each a D-34 interface
  change announced in `docs/INTERFACE_CHANGES.md` first (ruling 14e); folds are migrations, one window at a time.
- `scout-d33-volume-law`: claimed 17:43, in flight (prepares D-33 package 17 for release after (e)).
- Lemma I.5.5 (PROVED AS STATED) and 2KB9 / B5SL: one tag package, now unblocked (`fix-wiki-revise-proof-sections-a`
  merged); `marginal-ode` is under revision by `wiki-revise-proof-sections-a-r3`: brief the tag package (Lean `Tags/`
  only, no wiki edits) when that revision merges.

## In flight (claims without a done marker at 17:54)

`nm-graph-certificates` (156), `wiki-revise-proof-sections-a-r3`, `docs-automerge-state` (003),
`scout-d33-volume-law`, and whatever was claimed after (check `claims/` against `done/`). Also running: the kernel
replay at `df5d0fd`. Worktrees kept: fix-nm-tree-depth, mig-model-norm, nm-graph-certificates, nm-multipoint-geometry,
nm-tree-depth, replay-df5d0fd, tooling-task-board-check, wiki-revise-proof-sections-a-r3, wiki-revise-proof-sections-b,
wiki-revise-regular-variation-r2, and the claimed packages' worktrees.

## Migration window (e)

Opened in round 4. `mig-model-norm` finished at 17:36 and its audit approved at 17:46, both during this round's gate;
under the one-batch rule it merges first in round 6. Ruling 11g ("if (e) has not merged by the end of round 5, reopen
proving anyway"): **proving reopened at the end of this round** for every held brief disjoint from (e)'s six files
(scripted check: tags untagged, new files absent, no overlap with (e) or pull request #2, no lace-area target):
released 156, 157, 158, 160, 161, 200 (owned files narrowed to `IntensityScaling.lean` + its Tags file, per
scout-held-briefs-e), 389, `fix-nm-tree-depth`, and the new 170 (`hier-pointwise-ingredients`, H10 step 1) and 171
(`dedup-exponential-moments`). Still held because they touch (e)'s files or names: 210, 220, 230, 370, 371; 240 waits
for its amendment (items 1-2 now, item 3 after `nm-closed-products` merges; text in scout-held-briefs-e). After (e)
merges, the three migrations of D-35 are done; next interface changes come from `scout-defs-2`.

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the directory.
**Startable at 17:58 (12; 8 Lean proving briefs):** `004-audit-w498-proof-tag`, `005-fix-tooling-task-board-check`,
`006-audit-nm-tree-depth-r2`, `007-critic-reread-regular-variation-r3`, `157-nm-closed-products`,
`158-nm-small-intensity`, `160-connection-kernel-tags`, `161-monotone-coupling-tag`, `170-hier-pointwise-ingredients`,
`171-dedup-exponential-moments`, `200-nm-bond-core`, `389-frontier-riccati-linear-error`. Owned files are mutually
disjoint (Lean: `Combinatorics/FiniteEdgeChange` + `Bond/{LocalConnectivity,ClosedCertificates,PathLowerBounds}` (156,
claimed); `Probability/ClosedProduct` + `LongRange/CutPoints` + `Bond/{DegreeGenerating,ClusterLaw}` (157);
`Models/NormalizedSmallIntensity` (158); `Bond/ConnectionKernel` (160); `Probability/Coupling/Monotone` (161);
`Models/HierarchicalPointwise` (170); `Probability/ExponentialMoments` + `Bond/UniformVolumeTail` +
`Models/FiniteRangeDecay` (171); `Bond/IntensityScaling` (200); `Analysis/RiccatiLinearError` (389); `Models/Tree`
(fix-nm-tree-depth), each with its own new Tags file; only `PercLib.lean` import lines are shared).
Written this round and already claimed or done: 000-audit-mig-model-norm (done, APPROVE),
001-audit-wiki-revise-proof-sections-b (done, APPROVE), 002-audit-tooling-task-board-check (done, changes),
003-docs-automerge-state (claimed), 010-wiki-revise-proof-sections-a-r3 (claimed), 150-fix-nm-tree-depth (done),
156-nm-graph-certificates (claimed).
**Held:** `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-370`, `HOLD-371` (after (e)), `HOLD-240` (amend first),
`HOLD-audit-nm-bond-core` (after 200), `HOLD-audit-nm-probability` (after 240),
`HOLD-audit-tooling-task-board-check-r2` (after 005), `HOLD-audit-wiki-revise-proof-sections-a-r3` (after the reviser).

Next packages to brief: audits of each prover package as it reports (interface: fresh D-35 audit; 170/171 proof-only
merge on the gate); the reviser for `critic-proof-sections-c` after a-r3; a critic re-read of the proof-sections-b
articles after they merge; the I.5.5/B5SL/2KB9 tag package; the `scout-defs-2` interface packages; D-33 packages 17
(`lrp-volume-law`, after `scout-d33-volume-law` and (e)) and 18 (`lrp-I31-I32`) of `/home/user/reports/d33-map.md`; the
7YNX tag package after 170 (hier-map H10 step 2: outer-shell recursion and the tagged conditional bounds); near-misses
B2ZL (after (e)), 32GP, NM-7 `nm-window-correlation`; the F75G hypothesis bundle (optional); moving
`ae_cluster_eq_singleton_of_offDiagonal`/`ae_openGraph_le_of_offDiagonal`/`ae_edgeSet_subset_of_forall_eq_one`
(audit-nm-tree-depth N3) into `Percolation/Bond`; the `mig-model-norm` audit's four non-blocking recommendations;
restructuring the index and hubs (ruling 8; `pages-deploy` has merged, so `wiki/src` is free); about ten new public
tasks for the board.

## For ARCHITECT

- **Round 5 additions.** (1) **One batch per round, again.** During this round's gate (17:36-17:52) the (e) migration
  finished and was approved, and four more approvals arrived (9YE6, two wiki revisions, a tooling audit with changes).
  All wait for round 6, and window (e) stays open one round longer than ruling 11g intends. I kept to one batch as the
  launcher says; please allow a second gated batch per round when an approved migration arrives during the first.
  (2) **W498 merge repair (coordinator's call):** the gate's D-35 check (i) failed because `hier-cor12`'s brief told
  the author not to tag the theorem proving the tagged Prop W498. I added the one line `@[tag "W498"]` (the J98J
  pattern; no statement changed) and queued a mechanical confirmation audit; W498 now counts as proved. Overrule if you
  want such repairs audited before the merge. (3) **Proving reopened under 11g** at the end of round 5 for every held
  brief disjoint from (e)'s six files, with (e) approved but unmerged; the five briefs that touch (e)'s files or names
  stay held until it merges.

- **Round 4 additions.** (1) **One batch per round versus ruling 15 ("stop waiting for one thing behind another").**
  This round's batch (11 branches, 13 min) closed at 17:19; within the next eight minutes eleven done markers arrived,
  among them the auto-merge audit (approve with one change) and its fix, four approvals of tagged packages and a wiki
  re-audit approval. Under the launcher's one-batch rule they wait for round 5, which is the queueing ruling 15 asks us
  to stop. I kept to one batch; please let the coordinator run a second gated batch when ruling-15 items or approvals
  arrive during the first gate. (2) **The kernel replay keeps dying.** Two runs were OOM-killed (`cfef666` at 66/338,
  `622c846` at 234/342; one `leanchecker` reached 10.7 GB RSS beside a gate and worker builds). No replay has passed since
  the baseline `4c72765`, so ruling 10(1)'s "after each batch that passed the gate and the kernel replay" cannot be met;
  Tom merged `b1db272` regardless. Options: (a) reduce the batch size of `kernel_replay.sh` from 6 to 2 and accept longer
  runs; (b) hold worker Lean builds for the replay's duration once per series; (c) rely on CI's `kernel-replay` job once
  `ci.yml` is on `main` (16 GB runner, nothing else running) and record its result. I recommend (c), with (a) locally as
  a fallback. (3) **Migration (d) kept no deprecated aliases** for its 11 renames (ruling 9h asks for them "where
  possible"); pull request #2 uses none of the old names. Overrule if you want aliases added in a follow-up.
- Still open from round 3: (3) **shared lace prerequisites** (nearest-neighbour bond model on `ℤ^d` with `p_c`, Fourier
  transform, signed convolution: I recommend (a) we propose the bond model and `p_c` as interface packages, (b) leave
  Fourier/convolution to Codex) and (4) **reserved scope** (all 111 transitive dependants of the lace articles, or only
  the 21 direct ones). Nothing is queued in either until you answer. The board tasks `connection-kernel-tags` (70KD,
  UZ7J) and `monotone-coupling-tag` (2ML7) are shared prerequisites outside the lace articles (ruling 14a gives them
  priority). Also from round 3: the critic's M-T2 (2ZI0 in `triangle-condition` and I23O in `triangle-susceptibility`
  are one lattice theorem with two full proofs; any Lean work should target one chain; `triangle-condition` is a lace
  article, so that is Codex's call).

- **Window (d) on the strict reading (round 1 of this series).** The launcher asked that, once its preconditions hold,
  only the migration brief be startable until claimed Lean work merges. Done so: (d) released, six unclaimed Lean
  briefs held (hier-cor12 among them), audits/wiki/tooling left open (ruling 11f). Lanes therefore take audits until
  (d) merges; reopening is a rename (steps in the window section). Overrule if you prefer the round-5 reading
  (disjoint proving open beside the migration), which the previous series used.
- **One batch per round** (launcher) **is now the bottleneck.** In round 2, ten mergeable or approved packages arrived
  within 20 minutes of the round's single batch (six approved tagged statements, a proof-only port, two wiki branches,
  the (d) report); all wait for round 3. The lessons of the previous series (several small gated batches per round,
  2.5-4 min each) suggest allowing up to three batches per round when no gate is already running. Overrule or confirm.
- **Workers run the full `scripts/gate.sh` in their own worktrees** (the (d) brief asked for it): with the coordinator's
  gate, the kernel replay and audit builds beside it, the coordinator's gate was OOM-killed (15 GB) and the replay died.
  Proposal: briefs ask workers for `lake build --wfail` of changed modules and importers only; the gate is the
  coordinator's (one machine-wide). Coordinator's call from round 3 unless you object.
- **Window (c) closed early for proving (round 5, coordinator's call under 11g).** The fold still runs (phase 1
  of 3 after 22 minutes); fourteen prover briefs on new or disjoint files were released beside it rather than
  let the window run past one round. Overrule if you want the queue kept empty until the fold merges.
- **Unrecorded predecessor.** A coordinator merged eight branches (05:33-05:56) without gating its last
  two merges or writing STATUS (it seems to have been cut off). Recovered and gated in round 1. The
  launcher should not start a coordinator while a predecessor may still be running, and a coordinator
  should commit STATUS after each gated batch, not only at the end.
- **mig-linters left three linters off** (`lakefile.toml`): `style.header` (six files carry third-party
  notices; rewriting them into mathlib's `Copyright (c) … All rights reserved.` form means asserting a
  holder: a licence-notice question, see "For Tom"), `unusedFintypeInType` and `unusedDecidableInType`
  (removing 44 unused instance binders changes statements, ≥5 tagged: an interface package after the
  window, coordinator's call unless you object).
- **Window reading changed in round 2 (coordinator's call under 11g; overrule if you disagree).**
  Migration (c) is waiting on its interface audit, and (d), (e) follow one at a time; no Lean proof has
  merged since round 4 of the earlier series. Ten prover briefs whose owned files are disjoint from every
  file of (c), the D4b fold, (d) and (e) were released. The migrations still run one at a time, but no
  longer behind an empty queue: each is checked for file-disjointness against the claimed prover work
  before release. (Still: no GitHub write tool in rounds 2 and 3; the first item above stands.)
  Round 4 opened window (c) properly once `mig-def-bond` merged: unclaimed prover briefs held, the fold the
  only new Lean brief; three prover packages claimed seconds earlier on disjoint new files ran beside it and
  merged. Overrule if you want strict emptiness even in that case.

## For ARCHITECT (round 7 additions)

- **Proving kept open beside the migrations (coordinator's call under 11g; overrule if you want strict quiet
  windows).** In round 7 the fold merged and the iscut part of (c) ran beside eight prover packages, all on files
  disjoint from it; seven tagged statements were proved and merged and eight more await audit. The same reading is
  proposed for (d) and (e), each still run alone among migrations.

## For Tom

- **Pull request to `main` (rulings 13a, 15e, 16): ready.** Your pull request #4 (from `claude/zen-lovelace-rvlcw2`)
  follows our pushes; merge it with a merge commit when you wish (or use
  https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2). Summary in
  `/home/user/reports/READY-FOR-MAIN`. It brings the task board, the self-sufficient `AGENTS.md`/`CONTRIBUTING.md`,
  the lace-expansion map, CI (build and checks, read-only token), **auto-merge (merge job enabled; only proof-only pull
  requests on green CI whose author is in `.github/automerge-authors`, initially you)**, the Pages workflow (site
  https://tomhutchcroft.github.io/perclib/ once on `main`) and fifteen new proved tagged assertions. Last gated commit
  `0e30c75` (gate passed 17:52); commits after it touch only `tasks/` and docs. No kernel replay has passed since the
  baseline `4c72765` (one is running at `df5d0fd`, 228/363 at 17:53); once `ci.yml` is on `main`, CI runs the replay on
  every push. After merging: Settings → Branches, protect `main` requiring the CI check, no force pushes; Settings →
  General, allow auto-merge. `AGENTS.md`/`CONTRIBUTING.md` still say auto-merge "is not active"; a docs fix is in
  progress.
- **Pages wording for your approval (ruling 12):** the banner ("This wiki is unfinished and under active construction.
  Articles may be incomplete, and statements and proofs may contain errors. Only assertions marked 'proved' have been
  checked in Lean; see About.") and the About page text, exactly as in `wiki/src/render.mjs` and `wiki/src/build.mjs`
  at `eea6ceb` (list in `/home/user/reports/audit-pages-deploy.md` §"For Tom", item 2). The site ships with them
  meanwhile; the `noindex` meta stays until you lift it.
- **Wiki-original results, all nine now audited:** Q7QG, V7MP and 9FO5 (`hierarchical-runaway`) are judged CORRECT by a
  fresh correctness audit (`audit-wiki-original-runaway-c`), like J0DE, MFGT, OQV3, Q4PO, F7Q2, NC7F before them. They
  stay marked "original to this wiki; proof not independently checked" until you say how the marking should change; the
  NC7F precision fix (refining grids) is written and under audit.
- **Your branch `work/hierarchical-two-point-paper`** (`be2b9df`): reviewed (ruling 14c); the review is on the
  integration branch at `docs/reviews/branch-hierarchical-two-point-paper.md`. Verdict MERGEABLE AFTER CHANGES: the six
  translation-invariant first-exit theorems duplicate `PercLib/Models/HierarchicalTranslation.lean` (already merged, with
  Theorem 1.1 built on it) and should be dropped; `HierarchicalTriangle.lean` (the triangle recursion, new to the
  library) needs 15 whitespace fixes to build under `--wfail`. We do not merge or change your branch.
- **Licence notices (from `mig-linters`).** Six files keep their third-party headers and the header
  linter stays off: `Probability/ProdBernoulli.lean`, `Probability/Harris.lean`,
  `Probability/Cylinder.lean` (adapted from PercolationContinuity, Anthropic PBC), `Models/Site/Basic.lean`,
  `Percolation/Bond/Basic.lean` (Percolation, Apache 2.0 via `third_party/percolation/`),
  `Probability/Russo.lean` ("adapted from NearCritical/Russo.lean by Tom Hutchcroft and collaborators").
  Either prepend a mathlib-form block naming the upstream holder and keep the old notice below it, or
  keep the linter off for these headers. Your choice.
- **Issue #1** (README) is fixed on `main` since your merge of pull request #3: it can be closed.

- **Wiki-original results (critic of `hierarchical-runaway`, M8).** J0DE, MFGT, OQV3, Q4PO, F7Q2,
  NC7F (and Q7QG, V7MP, 9FO5) go beyond Hutchcroft 2022 Remark 6.14 (Gaussian limits with explicit
  covariance, a functional limit, a nested-block limit) and are marked in the body as "not attributed
  to the source". How should results original to the wiki be marked in History, and must each have a
  fresh correctness audit before it stays public? (The critic read their proofs and found no error; two
  steps are compressed, P10 and P11.)
- **T9KC scope** (long-range uniqueness of the infinite cluster): settled by `audit-wiki-proofs-misc`:
  the statement as worded (allowing p(z) = 1 and Σ p(z) = ∞) is true, by an elementary coset argument
  when some p(u) = 1 and by Grimmett–Keane–Marstrand (1984) connectivity when Σ p = ∞; the article's
  scope paragraph was rewritten accordingly and is merged (`4b5b504`, re-audit APPROVE). Nothing for
  you unless the GKM hypothesis check fails.
- **The model article is ready for you to look at (ruling 8):** `/articles/hierarchical-two-point/` (merged on
  the integration branch at `c8e3d2c` after a correctness audit, a second critic read and two re-audits; it
  includes the new J98J statement). The reviser's open questions are in §5 of its report (copy in
  `lrp/docs/reports/`, `wiki-model-hier-two-point.md`); the restructuring of the other articles follows this
  pattern unless you object.
- **Milestone:** Theorem 1.1 of *Critical percolation on the hierarchical lattice* (arXiv:2103.17013v1), the averaged
  critical two-point bounds with constants uniform in the kernel, is now proved in Lean on the integration branch
  (`PercLib/Models/HierarchicalTwoPointAveraged.lean`, merged `78ee775`), using the corrected Prop. 2.12(ii) constant
  listed below. Corollary 1.2 (pointwise bounds for radial kernels) is the next package. The kernel replay of `cfef666`
  (which contains it) was started this round; see "Integration tip and gate".
- **Questions from the wiki revisions (D-19: you judge style).** (1) `regular-variation`: the slowly varying function
  is written `L` (as in Feller, Vol. II, cited first) or `ℓ` (STYLE notation table; Bingham–Goldie–Teugels)? It stays
  `L` with one defining sentence until you decide; `ℓ` would touch the tagged statements 3491 and SLGY (letter
  only, with an audit). The assertion titles of SLGY and LTJ1 are being renamed to the literature's terms (metadata
  only); overrule if you prefer the old titles. (2) `branching-random-walk`: the reviser keeps the parameter
  conversion of BSI3 after the idea, with the references (critic: before the statement as setting). (3)
  `size-biased-laws`: the near-critical input of the IIC construction is stated as uniform-in-p
  quasi-multiplicativity plus uniform convergence (Basu–Sapozhnikov), not as `L(p)`-based arm bounds and
  θ(p) ≍ π(L(p)) (critic); the polynomial rate in r/s of the old FM8D idea was dropped (the published scheme gives
  geometric damping in the number of annuli only); the decoupling uses the innermost circuit with the outside
  independent. Both versions are in `/home/user/reports/authors/wiki-revise-proof-sections-a.md` (copy in
  `lrp/docs/reports/authors/`), "Disagreements with the critic".
- **Wiki-original results (ruling 11h), audited:** fresh correctness audits judge J0DE, MFGT, OQV3, Q4PO, F7Q2 and
  NC7F (`hierarchical-runaway` material beyond Hutchcroft 2022 Remark 6.14) correct, with no step failing
  (`/home/user/reports/audit-wiki-original-runaway-a.md`, `-b.md`; copies in `lrp/docs/reports/`). They are being
  marked "original to this wiki; proof not independently checked" as ruling 11h says; tell us whether, now that
  they have been checked, the marking should change. One precision point: NC7F's interpolated-paths clause holds
  for deterministic grids N_n → ∞ at every node, not for a fixed grid; a wording fix of the tagged block (with a
  fresh audit) is planned.

- Publishing the wiki: done as ruling 6 directs. The attribution pass (`pub-attrib`, 56
  articles credited "T. Hutchcroft, book in preparation", one catalogue entry, no locators)
  was approved by a fresh auditor on all four points of 6b with nothing withheld, and is
  merged and pushed on `claude/zen-lovelace-rvlcw2` of `perclib` (merge `6146737`). It
  reaches `main` only with the first pull request (see "For ARCHITECT").
- The wiki critic's mathematical reports (critic/general.md §5) were settled from the published
  sources by `scout-wiki-math`: the erratum "susceptibility-lower-coefficient" now attaches to
  FF30 and 7YNX only, and `tree-graph`'s proof of L82Q now follows the Lean route (both merged,
  `202e752`); FCU7 (`sharpness`) gets the precise statement of Duminil-Copin–Tassion
  arXiv:1502.03051 Thm 1.1 (`014-wiki-fcu7`, then a fresh audit). Nothing needed your ruling.
- Repository settings for ruling 10(2), once the CI workflow is on `main`: (1) Settings →
  Branches → add a protection rule for `main`: require a pull request, require the status
  check `CI / gate`, no force pushes; (2) Settings → General → allow auto-merge;
  (3) add collaborators to `.github/automerge-authors` and `CODEOWNERS` as you wish.
- Lemma I.4.13, second half, of *Critical long-range percolation I* implicitly assumes
  local integrability of `h` on `(1, ∞)` (compiled counterexample
  `not_integrableOn_rpow_mul_indicator_sub_inv`).
- The provisional errata in the wiki await confirmation (D-30). There are **180**, not 194 as said
  before. `scout-errata-triage` checked 104 against the published arXiv versions: **92 are forced
  corrections (class A), safe to confirm in bulk** (list in `/home/user/reports/scout-errata-triage.md`
  §2, copy in `lrp/docs/reports/`); 4 are A* (printed step wrong, repair a choice:
  `hnhyper:upper-extrapolation-error-scale`, `hhier21:scaled-truncation`,
  `triangle:boundary-positive-part`, `richards:conditioning-induction`); 6 are B (source readable as
  right: `hhiervol:coalescent-holding-rate`, `hhiervol:periodic-quotient-subgroup`,
  `lrp1:levy-first-moment-weight`, `rohde:reverse-derivative-comparison`, `sw:radial-clock-derivative`,
  `sw:finite-starting-image`); none found mistaken. Worth your glance first:
  `hhiervol:first-moment-terminal-amplitude` (p=1 coefficient in Thms 1.4/1.6 off by L^α),
  `hhiervol:critical-integral-and-amplitude`, `chensakai:compound-zeta-normalization` (forced; the
  choice of fix is yours), `gladkov:capacity-law` (Thm 8.2 false as stated). **Round 6:**
  `scout-errata-triage-b` classed the remaining 43 (`/home/user/reports/scout-errata-triage-b.md` §2,
  copy in `lrp/docs/reports/`): **42 more class A** (safe to confirm in bulk; list in §2), 1 A*
  (`lrp3:restricted-cluster-heredity`: Lemma III.4.2 false for arbitrary classes; the repair restricts
  to downward-closed classes; please confirm the classes used later in LRP III satisfy it), none
  mistaken. Totals over 180: A 134, A* 5, B 6, C 0, D 33 (Heydenreich–van der Hofstad: no public
  copy reachable), 2 handled elsewhere. Within A worth a glance: `triangle:triangle-numerator` (the
  main differential inequality (1.23) is false near β = 0; the corrected form is weaker),
  `hl2:reverse-bk-cancellation` (the step is false; no repair known), `kls:red-first-round-parameter`,
  `lrp3:deficit-ode-merger-forcing`.
- Universal tightness, issue-52 reading (`k ≥ 1` where the source prints `k ≥ 0`, false
  at `k = 0`); the hierarchical programme uses only `k ≥ 1`.
- arXiv:2103.17013v1 Prop. 2.12(ii) prints constant 1 where the flux argument gives
  `(L^α-1)/(β_c C (1-L^{-d}))` (provisional erratum; the Lean target keeps the factor).
- J98J (Theorem 1.1, averaged estimate for symmetric kernels) is audited and fixed; V4QQ/YWTU now
  cite it, so they hold for symmetric `J` (audit-j98j C1/C2). It reaches the tip with the
  restructured model article.
- Critic reports on `hierarchical-two-point` that change tagged statements (R2, R4, R6 in
  `/home/user/reports/critic/hierarchical-two-point.md` §4): V4QQ and YWTU are prose, not precise
  statements; the coordinator will queue a wiki package to state them precisely (hypotheses as
  in J98J; constants depending only on d, L, α, c, C) with a fresh audit. Say if you prefer to
  word them yourself.
- **Please approve `wiki/STYLE.md`** (merged on the integration branch as a draft, ruling 7 (i);
  wiki work follows it meanwhile). Open choices for you: the notation table (`P_q` for
  edge-dependent laws, `η` for the extinction probability) and whether "we" stays allowed
  inside proofs. Coming next: the restructured model article `hierarchical-two-point`.
- CI settings (from `audit-workflows`, note N6): with "require Code Owner review, no required
  approvals", anyone with write access could merge interface pull requests touching paths
  outside CODEOWNERS (definitions in area files, `PercLib/**/Tags/`, `docs/`, `tasks/`). Either
  add `/PercLib/**/Tags/` (and area `Defs`) to CODEOWNERS or accept this knowingly. Also check
  once that each action SHA pinned in the workflows is the tag it names (N4).

## Lessons

- **Round 5 (new series, 17:30-18:00):** started 50 s after the predecessor's STATUS commit (tree clean; only the
  replay and a worker build, each in its own worktree). A top-priority audit claimed seconds before the round finished
  within 5 minutes: waiting for it before gating put Pages in the batch. **Run `check_d35` expectations through the
  brief:** a brief that says "no tag on the proof of a tagged Prop" makes the gate fail (D-35 check (i)); proof
  packages for a tagged Prop must carry the tag (write that in future briefs). A worker branched from the
  coordinator's unpushed batch commit and something pushed the integration branch: check `git status -sb` before
  pushing. Twelve done markers arrived within 25 minutes; the one-batch rule left five approvals for round 6.

- **Round 4 (new series, 17:05-17:28):** lanes were extremely fast: eleven briefs written during the gate were claimed
  within minutes and most finished before the gate ended (an interface audit in 3 minutes, a critique in 4). The
  bottleneck was the single gate (13 min beside the replay and worker builds) and the one-batch rule, not briefs.
  Prepare non-Lean commits (board mirror, `INTERFACE_CHANGES`) in a separate worktree branched from the gated commit
  while the gate runs, then fast-forward after it passes; never edit the main checkout during a gate. A ruling arrived
  mid-round again (15, during orientation): re-read RULINGS.md after the first commands. `find … -delete` on
  `__pycache__` in older worktrees deletes tracked files: use `git checkout -- scripts/__pycache__` instead. The kernel
  replay died from OOM near the end of a gate: start it right after the gate, not before.

- **Round 3 (new series, 16:56-17:15):** started one minute after the predecessor's push (tree clean; the only build
  running was an audit's, in its own worktree). Eleven approved/mergeable branches gated in one 9-minute batch beside the
  kernel replay without OOM (no worker gate running). Five more approvals arrived during the gate: with one batch per
  round they wait. Write release notes and new prover briefs while the gate runs; a scripted pre-release check (tags
  untagged, new files absent, no branch/claim of the id, owned files vs. migration files) took one command. `git worktree
  remove` refuses a worktree whose `scripts/__pycache__` the gate touched: `git checkout scripts/__pycache__/` and delete
  untracked `.pyc` there first. An outside pull request appeared minutes before the round (`git ls-remote` showed
  `refs/pull/2/head`): check at the start and queue its review early; it was claimed within a minute.

- **Round 2 (new series, 16:35-16:58):** started the minute the predecessor pushed (tree clean, nothing running in the
  main checkout; the kernel replay in its own worktree does not count). Two packages waiting: one gated batch. **Check
  memory before gating:** `pgrep -af 'scripts/gate.sh'` and read each process's cwd (`readlink /proc/<pid>/cwd`): a
  worker running its own gate plus the replay plus audit builds made the coordinator's gate OOM in the extract step; the
  log simply stops after the script tests (`dmesg | grep -i oom` confirms). Wait for the other gate, re-run alone. Start
  the replay with `setsid nohup … < /dev/null &` so it survives the coordinator's shell. **RULINGS.md can change
  mid-round** (ruling 14 arrived at 16:40): re-read it before writing STATUS. A fixer may merge the coordinator's
  local, not yet pushed batch commit into its branch (here `622c846`): harmless when the gate passes, but push promptly.
  Claims were instant: four new briefs were claimed within five minutes.

- **Round 1 (new series, 16:22-16:40):** started 2h20 after the predecessor's last STATUS with the tree clean and all
  four lanes claiming Lean briefs at the same second (16:22): an idle gap, not a running predecessor. Three done markers
  were waiting (one approved migration, two interface packages): one 4-minute gated batch. The kernel replay niced
  beside four worker builds runs at about 2 modules a minute (338 modules: hours); start it at the very beginning of a
  round, right after a gated commit, and leave the log where the next coordinator can read it. Interface reports
  arrive faster than audits are claimed when lanes are all on Lean: keep the audit template (148/149/152) handy.

- **Round 7, second half (13:36-14:00):** throughput was very high: 20 done markers in 25 minutes, including an
  interface audit of a 30-file migration in 15 minutes and four prover packages within ten minutes of release. The
  bottleneck was writing briefs, not gates: keep audit-brief and fix-brief templates (the frontier audit 134 served
  for seven more by substitution) and release held re-audits the moment a fixer's marker appears. A batch with the
  fold needed a 9-minute gate; small batches took 2.5 minutes. Prover briefs released from HOLD need a release note
  (current tip, which migrations run beside them, renamed names) and a scripted check that their tags are untagged
  and their new files absent.

- **Round 7:** started 13:15 with the tree clean; nothing waiting, and the wait produced two markers within 90 s,
  then nine more during the first gate. Four small gated batches (2.5 min each) kept every approved branch moving.
  Each wiki branch that adds a lead rewrites the frozen-digest test in `wiki/tests/lead.test.mjs`: expect that
  conflict on every such merge and keep the most general form (now on the tip). Running `pytest` in `scripts/`
  leaves untracked `__pycache__/*.pyc`: delete them before committing. An interface package's audit brief takes
  ten minutes to write from the brief and the diff: write it as soon as the done marker appears.

- **Round 6:** started at 13:03 with the tree clean and the predecessor's STATUS pushed; three done markers waiting
  (an audit with changes, a fix, a revision), none mergeable: two held audits released and a fix brief written within
  five minutes. A proof-only new-file merge gated in 2.5 min beside three worker Lean builds without OOM. When all
  four lanes are on Lean, released audits sit unclaimed: expect merges of wiki/tooling work only once a lane frees.

- **Round 5:** short (10 min); four done markers in the first six minutes, none mergeable (audit with changes,
  fix awaiting re-audit, premises audit, follow-up needing its own audit). Reopening proving was a rename once the
  held briefs had been brought up to date (G3/G5 edits, note) and checked by script: grep each brief for the
  fold's owned basenames and for target files that already exist, and `git grep 'tag "XXXX"'` for its tags.

- **Round 4:** started at 12:24 with the tree clean; done markers kept arriving (twelve in 30 minutes), so the
  round ran six small gated batches (2.5-4 min each, the `Bond/Basic.lean` gate included) instead of one; each
  was pushed at once. When holding briefs to open a window, expect races: three prover briefs were claimed in
  the seconds before the rename; check `claims/` after renaming and record them as in flight. Release a held
  re-audit only with the fixer's exact `<merge>`/`<fix>` commits from its report. An interface audit with a
  change "for the next package" (mig-def-bond change (1)) lets the branch merge as is; carry the change into
  the next brief explicitly.

- **Round 3:** started 25 s after the predecessor's push; nothing waiting; the 8-minute wait produced one critique
  within 90 s. A critique covering several articles gets one reviser brief owning all of them (ruling 7: one
  reviser at a time), with the held audit written at the same time. Briefs released in round 2 sat unclaimed for
  several minutes: there is no need to add more beyond about 20 startable.

- **Round 2:** a predecessor's STATUS commit (12:09) and this round's start (12:09) coincided; the tree
  was clean and pushed, so no wait was needed. Five done markers arrived in ten minutes, all needing an
  audit or a fix: no merge was possible, so the round's work was briefs. Release a fixer's re-audit with
  the exact commits (`git diff <merge> <fix>`) instead of branch-diff "minus the tip" wording. Workers
  take the alphabetically first brief: renumbering the whole startable set is how to set the lane mix.

- **Round 1 (this series):** the predecessor stopped mid-round after merging eight branches; nothing
  in STATUS said so. Compare `git log` with STATUS first, gate any ungated merges before adding more,
  and commit a short STATUS update after each gated batch so a cut-off coordinator loses little.
- **Read a fixer's report before releasing its re-audit.** A done marker also means "blocked": the
  model-article fixer stopped on a conflict, the audit was released on the marker alone and spent a
  worker on an unchanged branch. Check `git log` of the branch for the expected commit.
- Fix briefs that merge the tip into an older branch must say how to resolve the expected trivial
  conflicts (`wiki/tags.json` allocation entries, `migration-baseline.json` entries: keep both).
- Throughput: 20 done markers in 45 minutes; 8 startable briefs were all claimed within minutes. Write
  the next briefs (and HOLD follow-ups) while gates run.
- A full gate after a 323-file Lean merge took about 20 min; a gate running beside a worker's Lean
  build triggered an OOM kill (gate survived). Prefer gating when no worker builds Lean.
- No GitHub write tool may be available: check with ToolSearch and `gh auth status` early, and read
  pull requests and issues anonymously (`curl https://api.github.com/repos/<owner>/<repo>/pulls`).
- `mig-linters` added a copyright block before each provenance header: header checks must read all
  leading comment blocks (`071`/`081`).


- **Round 9:** two audit markers arrived within two minutes of the start (one at 05:22, one at 05:24);
  both approved with changes. When a correctness audit and a critic re-read target the same article,
  hold one combined revision brief until both are done instead of two fixes on one file. Workers now
  write build logs into the coordinator's scratchpad path; read them there to judge a long Lean claim.

- **Round 8:** predecessor's handoff and this round's start overlapped by a minute (STATUS time 05:14,
  clock 05:13 at start); tree was clean, so no wait needed. One done marker arrived within 90 s of
  waiting; an errata-only merge plus gate took about 4 min. Errata entries are not tagged statements:
  merged on the gate (as `wiki-math-fixes` was).

- **Round 7:** nothing new was done at the start; within one minute of waiting two markers arrived
  (`fix-workflows-r2`, `audit-wiki-fcu7`), both leading to audit briefs, no merge. Claims are fast
  again (two audits claimed within a minute of the round's start).

- **Round 6:** six done markers were waiting at the start (four wiki branches with mathematical or
  tagged content needing audits, one records-only branch, one critique), and a seventh arrived during
  the gate. Only records-only work merged on the gate; everything else became audit briefs. A
  wiki-only gate on a 0-Lean merge took about 5 min. Claims slowed: nine startable briefs from round 5
  and this round sat unclaimed for 15+ minutes, so do not over-produce briefs beyond about 10.
- Merged worktrees with a `wiki/node_modules` symlink refuse `git worktree remove`: delete the
  symlink first (never `--force`).

- **Round 5:** a comments-only migration over 266 files still rebuilds them: the gate took about
  12 min (beyond the Bash tool's 10-min foreground limit; run it in the background and poll for
  `pgrep -f scripts/gate.sh`). Check comment-only migrations by comparing the saved extracts in
  `.lake/gate/`: only the `line` field may differ. The classifier's token scan flags the word
  "tag(s)" in comments: a known false positive. Workers claimed six briefs within ten minutes.

- **Workers run as in-process agents:** there are no separate worker processes to look for; judge a
  claim live by recent file changes in its worktree (`find <wt> -newer docs/STATUS.md`).
- **Round 4 (short):** one finished package at the start (`wiki-lead-parser`), one more during the
  round (`wiki-I421`, interface: audit queued). The wiki gate on a 0-Lean merge took about 4 min.

- **Worktrees:** `git worktree add /home/user/wt/<id> -b work/<id> claude/zen-lovelace-rvlcw2`,
  `ln -s /home/user/perclib/.lake/packages <wt>/.lake/packages`, and
  `cp -a /home/user/perclib/.lake/build <wt>/.lake/build` so the worker does not rebuild
  PercLib; never download or rebuild mathlib per worktree.
- **Memory:** 15 GB, no swap. `lake env leanchecker PercLib` in one process is killed; use
  `kernel_replay.sh` batches, never during builds. A warm gate takes 4-6 min.
- **Merges:** conflicts are only `PercLib.lean` import lines; keep both sides in sorted
  position, `git add`, commit with `-m`, then `check_import_closure.py`. During an
  unresolved conflict the closure check reports spurious missing modules; rerun after
  the commit.
- **Workers are fast:** done markers arrive while the gate runs (four during this round's
  first gate). Integrate them in follow-up gated batches in the same round when they
  unblock something (here: the drain before the migration window); otherwise record them
  as finished-unmerged.
- **Check `git log` against STATUS** at the start: a predecessor may have merged after
  writing its handoff.
- **Briefs are claimed within a minute** of being written; write a brief only when it is
  ready to start, and put HOLD briefs in place before releasing anything they depend on.
- **Workers** sometimes use their harness's commit trailer instead of the preamble's;
  accepted, not rewritten.
- **Headers:** ported files tend to say "pull request 488" and package ids in headers; the
  D-35 check rejects them in new files; briefs say "repository, branch, commit".
- **Tags inside `to_additive`:** write `@[tag "XXXX", to_additive …]`.
- **One coordinator per checkout**, never two `gate.sh` runs at once.
- **Wiki merges** need no Lean rebuild beyond the gate; verify the merged `wiki/` tree is
  byte-identical to the audited commit (`git diff --quiet <audited> HEAD -- wiki`) instead of
  re-running `npm` (no network for `npm ci` is guaranteed).
- **Docs that describe CI** (contrib-docs, task-board) wait for the workflows; check each
  non-Lean branch for references to files or processes not yet on the tip.
- **`frontier.py` leaves an untracked `scripts/__pycache__/frontier.*.pyc`**: delete it before
  committing.
- **Kernel replay** was not run this pass: `mig-rowsum` may be building in its worktree
  (memory). Run `scripts/kernel_replay.sh 6` when no worker builds, before the first pull
  request to `main`.
- **Removing worktrees:** only if `done/<id>` exists and the branch is an ancestor of the
  tip (a fresh branch is trivially an ancestor before its first commit).
- **Pre-gate an interface branch while its audit runs:** `git worktree add --detach
  /home/user/wt/gate-<id> <tip>`, merge the branch there, symlink `.lake/packages`, copy the
  branch's built `.lake/build` and `.lake/gate/<base>.json`, run `scripts/gate.sh <base>` there
  (2.5 min warm), then remove the worktree. The main checkout stays clean.
- **During a window the queue empties fast:** workers claimed 10 non-Lean briefs within 15
  minutes. Keep HOLD Lean briefs ready (written this round from the scouts) so closing the
  window is a rename, and keep enough read-only/tooling briefs to stay at 8 startable.
- **An audit that approves with required changes** gets a fix brief to a new worker with the
  audit attached and a HOLD re-audit brief written at the same time.
- **Low numeric prefixes (000-014)** put critical-path briefs first; workers take the
  alphabetically first startable brief.
- **Wiki merges:** run `npm test` (or `npm run build`) on the merged tree with
  `node_modules` symlinked from `/home/user/lrp/wiki/node_modules`, then remove the symlink and
  `dist/`; no network needed. Several wiki branches touching `migration-baseline.json` or
  `tags.json` will conflict trivially: merge one at a time.
- **This round's throughput:** about 25 done markers in 50 minutes. Integrate in several gated
  batches within the round (each wiki-only gate is ~2.5 min warm) rather than leaving finished
  work for the next coordinator.
