# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 17:28 UTC, at the end of
coordinator round 4 of a new series (twenty-second coordinator overall; the previous handoff, round 3, is at `47b6ffa`;
older rounds are in `git log -p docs/STATUS.md`, the long per-round gate records up to round 3 in `git show
47b6ffa:docs/STATUS.md`). A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md),
[COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md) (D-34 to D-37) and `/home/user/reports/RULINGS.md`
(rulings 1-15; obey them). **Ruling 15 (new, Tom: "get the auto-merge and task board completed and merged as a matter
of top priority") outranks everything else this round and the next:** (a) task board and contributor docs (done this
round), (b) CI workflow (done this round), (c) auto-merge after one scoped audit, fix once, re-audit once, else merge
the auto-merge job disabled (`if: false`) — in progress, see "Auto-merge"; (d) pages workflow when audited; (e) keep
`/home/user/reports/READY-FOR-MAIN` current (written this round; rewrite it when (c) lands). Ruling 14 (Codex owns the
lace-expansion Lean area; each round `git ls-remote`, fetch outside heads, queue reviews, `git fetch origin main` and
merge it if it moved) stands. Container-local reports and briefs are copied for durability to `lrp/docs/reports/` at
each round's lrp commit (ruling 9i).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `df5d0fd`** (pushed; extract
  `.lake/gate/df5d0fd….json` saved). On top of it, pushed: `e8e790e` (task-board mirror and `docs/INTERFACE_CHANGES.md`
  only, no Lean/scripts) and this STATUS/FRONTIER commit. **Next gate: `scripts/gate.sh df5d0fd`.**
- **Round 4 (17:05-17:28): one gated batch, passed, pushed.** Started 17:05 (predecessor's STATUS commit 17:04:48; tree
  clean; the only Lean process was the kernel replay in its own worktree). `origin/main` had moved to `0eb4dc4` (Tom
  merged pull request #3 = `b1db272`, tree identical): merged into the integration branch first (`0a1dffc`, empty
  diff). Then merged, in order: `law-generality` (migration (d), Q0D1, `connProb`), `nm-core-wrappers` (RU6O JZN0 1C8G
  5LNL WD2J H48I), `nm-kernels-sitepaths` (U8CI K38T 5U4L), `nm-tree-split` (RZSW), `fix-contrib-docs-now` (contains
  `contrib-docs`) plus a merge-repair commit (the audit's required sentence in `AGENTS.md`; "CI is being added" wording
  in `AGENTS.md`/`CONTRIBUTING.md`, ruling 15a), `scout-lace-map`, `task-board` (conflict in `tasks/README.md`: board
  text kept, the "Areas taken" table added), `ci-workflow` plus a commit taking `ci.yml` and `scripts/ci_*.sh` exactly
  as at `0471b5e` of the audited workflows branch (the CI-only fixes; auto-merge files not included). Each merged branch
  head equalled its audited commit. `scripts/gate.sh b1db272` on **`df5d0fd`**: build `--wfail` OK (3,957 jobs),
  axiom audit 6,597 constants only `propext`/`Classical.choice`/`Quot.sound`, import closure 364 modules, forbidden
  scan 364 files, script tests, "D-35 checks passed", "INTERFACE change against b1db272eab7a: … Tags/TreeSplitting.lean:
  ['tag']" (expected: the eleven tags, each with a fresh APPROVE audit), "== gate passed on df5d0fd…" (log
  `/home/user/reports/gate-round4.log`; 13 min beside the kernel replay and worker builds). `bash
  scripts/ci_script_tests.sh` also passed locally (no `lake` needed). Then `e8e790e` (board mirror, see "Task board").
- **Kernel replay (ruling 13b).** The run at `622c846` was **OOM-killed at 234/342 modules** (dmesg: memcg OOM, a
  `leanchecker` at 10.7 GB RSS, around the end of this round's gate; no checker error). **Restarted at `df5d0fd`**
  (superset): `setsid nohup nice -n 15 scripts/kernel_replay.sh 6` in the detached worktree
  `/home/user/wt/replay-df5d0fd` (`.lake/packages` symlinked, `.lake/build` copied), started 17:24, log
  `/home/user/reports/replay-df5d0fd.log`. Next coordinator: `tail` the log; "Kernel replay passed" = pass at `df5d0fd`
  (record it, `rm` the `.lake/packages` symlink, `git worktree remove`, update `READY-FOR-MAIN` and the "For Tom" line);
  a checker error names the module ("For ARCHITECT", no further merges until understood); if `pgrep -f
  kernel_replay.sh` is empty with neither line, it was killed: check `dmesg | grep -i oom` and restart it the same way,
  ideally right after a gate when few workers build. Last replay that passed: baseline `4c72765`.
- **GitHub and ruling 14c/d (17:05-17:15).** No GitHub write tool (ToolSearch "github pull request": none; ruling 13a).
  `git ls-remote`: `main` `0eb4dc4` (merged in, above); `refs/pull/2/head` = `work/lace-foundations` `630d985`
  (unchanged); `refs/pull/3/head` = `b1db272` (merged by Tom); `work/hierarchical-two-point-paper` `be2b9df` (unchanged,
  reviewed in round 3). Anonymous API: open pull request #2 only; open issue #1 (README, fixed on `main` now).
  **Review of pull request #2 finished** (`review-pr-2`, verdict APPROVE WITH CHANGES, three mechanical changes;
  `docs/reviews/pr-2.md` on `work/review-pr-2` = `8252109`): merge it in the next batch (docs only).

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

Use the perclib `scripts/build_manifest.py` (as above), not the lrp copy named in COORDINATOR.md: the lrp
copy gives different counts (1,401 assertions, 264 proved, 6 statement-only at `c1f840a`).
Run a gate that rebuilds many modules in the background (`nohup scripts/gate.sh … > log &`) and poll
`pgrep -f scripts/gate.sh`; a full rebuild after a many-file Lean merge took 20 min (gate A), a 0-Lean or
new-file gate 2.5-4 min this round, the `Bond/Basic.lean` gate 4 min (warm). The base passed to `gate.sh`
must have a saved extract in `.lake/gate/` (STATUS- or FRONTIER-only commits have none: pass their gated
parent). After each gate `git checkout scripts/__pycache__/`; after `frontier.py` delete
`scripts/__pycache__/frontier.*.pyc`.

The `scripts/__pycache__/*.pyc` files are no longer tracked (removed by the CI merge, `__pycache__/` ignored): no
more `git checkout scripts/__pycache__/` after a gate on the tip. Older worktrees (branches cut before `df5d0fd`) still
track them: before `git worktree remove` there, `git checkout -- scripts/__pycache__`; never delete them with `find`.

## Progress (D-35 measure)

Round 4 (new series): **10 new assertions proved and merged (RU6O, JZN0, 1C8G, 5LNL, WD2J, H48I, U8CI, K38T, 5U4L,
RZSW), 11 tagged statements audited and merged (those ten plus Q0D1, respelled by migration (d)).** Manifest at
`df5d0fd` (perclib script): **293 proved, 2 statement-only, 1,108 unformalised, of 1,403**. Frontier (`docs/FRONTIER.md`
regenerated at `df5d0fd` by this commit): 281 ready, 818 blocked, 11 without recorded prerequisites, 293 proved.
Approved and waiting for the next batch: J98J (`hier-j98j-tag`), XLWI/YVJT (`fix-nm-uniform-volume`), EZJ7
(`fix-frontier-four-functions`), plus the proof-only Corollary 1.2 (`hier-cor12`, W498's Prop with V4QQ/YWTU untagged).
Correctness audits (wiki-original, ruling 11h): Q7QG, V7MP, 9FO5 judged CORRECT (`audit-wiki-original-runaway-c`).

Round 3 (new series): **7 new assertions proved and merged (8IGH, 04ZI, PAFY, QW2L, 57FJ, F75G, 0YH8), 7 tagged
statements audited and merged (the same seven, each a fresh APPROVE with binder table).** Manifest at `b1db272` (perclib
script): **283 proved, 2 statement-only, 1,118 unformalised, of 1,403**. Frontier (`docs/FRONTIER.md` at `b1db272`): 290
ready, 819 blocked, 11 without recorded prerequisites, 283 proved. One untagged proof-only package merged
(`lrp-I32-analytic`, D-33 package 16). Approved and waiting for the next batch: Q0D1 (migration (d)), RU6O/JZN0/1C8G/5LNL/
WD2J/H48I (`nm-core-wrappers`), U8CI/K38T/5U4L (`nm-kernels-sitepaths`), RZSW (`nm-tree-split`): 11 more tagged
statements.

Round 2 (new series): **1 new assertion proved and merged (KJWA), 1 tagged statement audited and merged (KJWA).**
Manifest at `622c846` (perclib script): **276 proved, 2 statement-only, 1,125 unformalised, of 1,403**. Frontier
(`docs/FRONTIER.md` at `622c846`): 296 ready, 820 blocked, 11 without recorded prerequisites, 276 proved. One untagged
proof-only package merged (`lrp-I56-gyration`, D-33 package 7). Approved and waiting for the next batch: 5 more tagged
statements (8IGH, 04ZI, PAFY, QW2L, 57FJ, F75G), one proof-only package (`lrp-I32-analytic`) and two wiki branches;
waiting for audits: 9YE6, Q0D1 (migration (d)), and the round-1 list (RU6O/JZN0/1C8G/5LNL/WD2J/H48I, U8CI/K38T/5U4L,
RZSW, 0YH8).

Round 1 (new series): **0 new assertions proved; 2 tagged statements re-audited and merged** (BQ44, ZH13, respelled by
`mig-iscut-fold`, meaning unchanged by compiled `Iff.rfl`). Manifest at `cfef666` (perclib script): **275 proved,
2 statement-only, 1,126 unformalised, of 1,403** (unchanged). Waiting for audits: 18 new tagged statements on finished
branches (the 8 frontier tags, RU6O/JZN0/1C8G/5LNL/WD2J/H48I, U8CI/K38T/5U4L, RZSW) plus XLWI/YVJT/EZJ7 after fixes.

Round 7: **7 assertions proved in Lean and merged** (R01V, ZH13, CPD6, XSA6, D1CH, DL0X, XRSL), **16 tagged Lean
statements audited and merged** (those 7 plus the 9 respelled by the fold: USAC, YLZV, R84Z, 5UJQ, 6QN7, 7902, 67GX,
7BMQ, JTBG), and 3 more audited with small required changes (XLWI, YVJT, EZJ7: fixes queued). Eight further
tagged statements are finished and wait for their audits (KJWA, 8IGH, 04ZI, PAFY, F75G, 57FJ, QW2L, 0YH8).
**Hierarchical line: Theorem 1.1 of arXiv:2103.17013v1 is proved in Lean** (`hierarchicalTwoPointAveraged`, proof-only,
merged `78ee775`); it counts as an assertion once the J98J tag package is audited. Merged: one untagged proof-only Lean package (`lrp-I526`: Lemma I.5.26 of
*Critical long-range percolation I* in the 2KB9 generality, `PercLib/Analysis/SignedDrivenODE.lean`, the
paper's `|f| = O(h)` hypothesis removed), the model article `hierarchical-two-point` with J98J (ruling 8), the
regular-variation revision, runaway split step 1 (two new articles `multiplicative-coalescent`,
`hierarchical-block-coalescent`), and the `check_d35` header-block fix. Wiki-original results (ruling 11h):
`audit-wiki-original-runaway-a` judges J0DE, MFGT, OQV3 **CORRECT**; `-b` judges Q4PO, F7Q2, NC7F **CORRECT**
(conditional on MFGT/OQV3 as stated; NC7F has a drafting imprecision, below). Manifest at `5fb1db4`
(perclib script): **275 proved, 2 statement-only, 1,126 unformalised, of 1,403** (J98J added to the wiki).
Frontier (`docs/FRONTIER.md` at `5fb1db4`): 297 ready, 820 blocked, 11 without recorded prerequisites, 275
proved.

Round 6: **0 assertions proved, 0 tagged statements audited.** One untagged proof-only Lean package merged
(`lrp-first-moment-b`, D-33: `PercLib/Analysis/FirstMomentAsymptotic.lean`, the analytic parts of Prop. I.4.2 /
Cor. I.4.8 / Lemma I.4.9 with the paper's inputs as explicit premises; the model statements I.4.2 and I.4.8 remain
unproved targets). Manifest at `1146988` (perclib script): **268 proved, 2 statement-only, 1,132 unformalised, of
1,402** (unchanged; `docs/FRONTIER.md` at `caa28bc` is still current, no tag changed).

Round 5: **0 assertions proved, 0 tagged statements audited** (no merge). One source-fidelity audit:
`audit-lrp-I55-premises` judges `regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio` (`CriticalDrivenODE.lean`)
to be Lemma I.5.5 of arXiv:2508.18807v1 **PROVED AS STATED** (binder table: every binder SOURCE or TYPING, no
EXCESS; nothing for Tom). It is not counted until a wiki tagged block and a `Tags/` restatement exist (no wiki
tag states I.5.5 today). Manifest unchanged from `caa28bc`.

Round 4: **0 new tagged assertions proved in Lean; 2 tagged definitions audited and merged** (OG96
`localCluster`, 6EIM `boundaryFlux`, in `mig-def-bond`; the manifest counts them as proved); **1 wiki tagged
block's proof completed and audited** (67W9; F9EV's proof merged after its re-audit). Four untagged Lean
packages merged (proof-only): Prop. 2.7 of the hierarchical programme (H7, `HierarchicalRestrictedSusc`),
D-33 packages 6 (Lemma I.5.5, premises not yet audited), 12 (Tauberian complete) and 14-15 (weak kernels).
Manifest at `caa28bc` (perclib script): **268 proved, 2 statement-only, 1,132 unformalised, of 1,402**.
Frontier (`docs/FRONTIER.md` regenerated at `caa28bc` by this STATUS commit): 301 ready, 818 blocked,
15 without recorded prerequisites, 268 proved. Rounds 1-3: 0 proved; 3 wiki tagged statements audited (round 1).

## Merged in round 4 (new series)

- `origin/main` (`0eb4dc4`) merged into the integration branch (`0a1dffc`; empty diff).
- **`law-generality`** (`d4fa3a0`, merged `605bc7d`): migration (d), `connProb`; Q0D1 respelled; `audit-mig-law-generality`
  APPROVE. `docs/INTERFACE_CHANGES.md`: (d) moved to "Merged" with the rename table (no deprecated aliases were kept:
  ruling 9h asks for them "where possible"; noted for the next interface change).
- **`nm-core-wrappers`** (`6d43725`): RU6O, JZN0, 1C8G, 5LNL, WD2J, H48I; **`nm-kernels-sitepaths`** (`b6162c0`): U8CI,
  K38T, 5U4L; **`nm-tree-split`** (`ff0e16c`): RZSW. Each with a fresh APPROVE audit (binder tables).
- **Ruling 15a:** `fix-contrib-docs-now` (`c3e8fd4`, contains `contrib-docs` `705ac8c`) with the required sentence and
  "CI is being added" wording (merge-repair commit `e2cf55d`), `scout-lace-map` (`bb00a05`), `task-board`
  (`0ae16d1`).
- **Ruling 15b:** `ci-workflow` (`560bd59`) plus the CI-only fixes as at `0471b5e` (`ci.yml`, `ci_script_tests.sh`,
  `ci_test_helpers.sh`). Not merged: `automerge.yml`, `automerge-authors`, `CODEOWNERS`, the classifier, the scanner fix.
- Board mirror commits `cccddd9`, `3cb1146`, `e8e790e` (see "Task board"), `d9468a4` (INTERFACE_CHANGES).
- Worktrees removed: law-generality, nm-core-wrappers, nm-kernels-sitepaths, nm-tree-split, contrib-docs,
  fix-contrib-docs-now, scout-lace-map, task-board, ci-workflow, board-r4, replay-622c846.

## Task board (`tasks/`, ruling 9b, 15a)

22 open tasks, 3 claimed stubs (`hier-cor12`, `hier-j98j-tag`, `tree-depth-limit`), 9 done. Mirror rules used this round:
a task whose package merged moves to `tasks/done/`; a task one of our lanes has taken (claimed or finished but
unmerged) moves to `tasks/claimed/` with a one-line "being done by the project's own agents" note; each new startable
Lean brief gets a public task written from public material only (this round: `nm-small-intensity` (1EWX, HRS7),
`frontier-riccati-linear-error` (19IN), `connection-kernel-tags` (70KD, UZ7J), `monotone-coupling-tag` (2ML7)). Our
held Lean briefs that mirror a board task say so and require checking open pull requests before release. Overlaps to
keep in mind: board tasks `restricted-cluster-strict`, `finite-edge-change-infinite-component`, `two-edge-routes`
(held brief 156), `isolation-positivity`, `cluster-boundary-product` (held brief 157); `cluster-*-any-law`,
`kernel-comparison-off-diagonal` (HOLD-200); `holley-observable-form`, `profile-perturbation-bound`,
`countable-closed-product` (HOLD-240). When one of those briefs is released, move the matching task files to
`tasks/claimed/` in the same push. Next: when `hier-cor12`/`hier-j98j-tag`/`nm-tree-depth` merge, move their stubs to
`done/`. A checker (`014-tooling-task-board-check`) is queued.

## Auto-merge (ruling 15c)

- `audit-fix-workflows-r5` (the last general audit): `fix-scanner-r5` (`18049a6`) **APPROVE**; `fix-workflows-r5`
  (`7912d1d`) **APPROVE WITH CHANGE AM6**, a hole in (A): file names printed by the `decide` step can inject
  `::set-output` workflow commands and forge the outputs the `merge` job trusts. The auditor confirms that a version
  with the merge job disabled (`if: false`) is free of (A) and (B).
- AM6 fixed once: `fix-workflows-r6` (merge `90223c2` of tip `e8e790e`, fix `b77968c`), done 17:24. **The single
  re-audit `000-audit-fix-workflows-r6` is released (top of the queue).**
- **Next coordinator, at once (ruling 15c):** on APPROVE merge `work/fix-scanner-r5` then `work/fix-workflows-r6`
  (expected clean: the auditor merged all pairs; `ci.yml` identical), gate, push; on FAIL merge `fix-scanner-r5` and
  `fix-workflows-r6` with `if: false` on the `merge` job of `automerge.yml`, a comment giving the reason, and one
  paragraph in `docs/CI_KNOWN_LIMITATIONS.md`; list it "For Tom". Either way rewrite `/home/user/reports/READY-FOR-MAIN`.
- `pages-deploy` (ruling 12, 15d) claimed 17:11 (brief `002`); its audit is written when it finishes (workflow
  privileges/pinning/injection + the strings for Tom).

## Finished, not merged (each waits for the item named)

**Ready for the next batch (one gated batch; merge in this order, then `scripts/gate.sh df5d0fd`, push):**
1. `work/fix-scanner-r5` and `work/fix-workflows-r6` per "Auto-merge" (only after the r6 verdict).
2. `work/hier-j98j-tag` (`4fd9f49`, J98J; the Prop `HierarchicalTwoPointAveraged` loses `c ≤ C`): `audit-hier-j98j-tag`
   APPROVE (fresh, binder table, no required change). Then `work/hier-cor12` (`eace6cc`, proof-only, Corollary 1.2 / W498
   Prop, V4QQ/YWTU untagged) **with the one-token merge repair**: delete the argument ` hcC` at the end of
   `PercLib/Models/HierarchicalTwoPointRadial.lean:65` in that merge commit (audit "Merge order"; the auditor built the
   repaired tree with `--wfail`). Move `tasks/claimed/hier-*.md` to `tasks/done/`.
3. `work/fix-nm-uniform-volume` (merge `88e9f26`, fix `1242118`; contains `nm-uniform-volume`, XLWI and YVJT):
   `audit-nm-uniform-volume` + `-r2` APPROVE. Then the exponential-moment dedup package can be briefed.
4. `work/fix-frontier-four-functions` (merge `ff0437e`, fix `c7ca677`; EZJ7): `audit-frontier-four-functions` + `-r2` APPROVE.
5. `work/fix-wiki-revise-proof-sections-a` (merge `3c3cb62`, fix `60a4a8a`): `-r2` APPROVE (npm 100/100). Check merged
   wiki files byte-identical to `60a4a8a`; then queue the critic re-read, then the I.5.5/B5SL/2KB9 tag package.
6. `work/review-pr-2` (`8252109`, `docs/reviews/pr-2.md`): docs only, merge on the gate.
7. `work/docs-contrib-followup` (`0c10038`): `audit-docs-contrib-followup` APPROVE (docs only).
8. `work/wiki-nc7f-precision` (`2ba2b5f`): `audit-wiki-nc7f-precision` APPROVE (one sentence of NC7F; `npm test`).

**Waiting for audits / fixes:**
- `work/nm-multipoint-geometry` (`1a4d0ba`, 9YE6): audit `154` startable (unclaimed for two rounds: lanes take low
  numbers first; renumber it lower if it is still unclaimed).
- `work/wiki-revise-regular-variation-r2` (`6ca5601`): mechanical audit `155` startable; then a third critic read.
- `work/nm-tree-depth` (`8fb36c7`, GGH2 + UHVH): `audit-nm-tree-depth` APPROVE WITH CHANGES (R1: GGH2's
  `ω ⊆ T.edgeSet` is EXCESS, use `openGraph ω ≤ T`; UHVH passes). Fix `HOLD-fix-nm-tree-depth` and re-audit
  `HOLD-audit-nm-tree-depth-r2` written; held only by window (e) (strict reading).
- `critic/proof-sections-b.md` (critic of `triangle-condition` 2ZI0 and `finite-random-graphs` F9EV; both NOT PASS,
  mathematics correct): reviser brief `010-wiki-revise-proof-sections-b` startable (coordinator's choice T-S1 option (a):
  keep the full 2ZI0 proof, summarise the lattice part of I23O's exposition with a "main article" link), held audit
  `HOLD-audit-wiki-revise-proof-sections-b`. The critic's M-F1 (make F9EV's statement precise: statement-change route)
  and M-T2 (2ZI0 and I23O are one lattice theorem: the Lean formalisation should target one chain) are open planning
  points, not briefed.
- **Lemma I.5.5** (PROVED AS STATED) and **2KB9**: one tag package after `fix-wiki-revise-proof-sections-a` merges.

## In flight (claims without a done marker at 17:29)

`audit-fix-workflows-r6` (ruling 15c), `mig-model-norm` (window (e), claimed 17:21), `pages-deploy` (17:11),
`wiki-revise-proof-sections-b`, and whatever was claimed after 17:29 (check `claims/` against `done/`). Also running: the
kernel replay at `df5d0fd`. Worktrees kept (unmerged or in use): automerge-workflow, fix-gate-scanner,
fix-workflows(-r2…-r6), fix-scanner-r2…-r5, port-wiki-hier-thm11, fix-port-wiki-hier-thm11,
wiki-revise-proof-sections-a, fix-wiki-revise-proof-sections-a, wiki-revise-regular-variation-r2, nm-uniform-volume,
fix-nm-uniform-volume, frontier-four-functions, fix-frontier-four-functions, nm-multipoint-geometry, hier-cor12,
hier-j98j-tag, nm-tree-depth, docs-contrib-followup, wiki-nc7f-precision, review-pr-2 (if present), replay-df5d0fd, and
the claimed packages' worktrees. After the auto-merge batch, remove the superseded fix-workflows/fix-scanner chains
(each an ancestor of the merged r5/r6 branch) and automerge-workflow.

## Migration window (e)

**Opened this round (17:20)**: (d) merged in `df5d0fd`, preconditions rechecked (31 definiteness lines in the five owned
files, 14 `normSeminorm_eq_zero` sites, no `KernelGeometry.lean`). `001-mig-model-norm` is the only startable Lean
brief (claimed 17:21); unclaimed Lean briefs renamed `HOLD-`: 156, 157, 158, 389, and new ones are written held (160,
161, `fix-nm-tree-depth`). Claimed Lean work beside it: none unfinished (hier-cor12, hier-j98j-tag, nm-tree-depth
finished; all disjoint). Audits, wiki, tooling and scouts stay startable (ruling 11f).
**Next coordinator:** when `mig-model-norm` reports, write its audit (re-audit PVA8, MQNP, LF50, 6YYS with binder tables;
template `154`, plus "no other declaration's meaning changed": compiled checks), merge on APPROVE, gate, move (e) in
`docs/INTERFACE_CHANGES.md` to "Merged" (rename table from the diff). Then **reopen proving**: release 156, 157, 158,
389, 160, 161, `fix-nm-tree-depth`, 200 (and `HOLD-audit-nm-bond-core` when 200 is done), 210, 220, 230, 370, 371, and
240 after its scout edit, each with the release note that `013-scout-held-briefs-e` prepares (if it has reported;
otherwise run the scripted check: names, tags untagged, files disjoint, open pull requests, lace area), moving the
matching board tasks to `tasks/claimed/`. If (e) has not merged by the end of round 5, reopen proving anyway (11g).

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the directory.
**Startable at 17:29 (8; window (e): no Lean except the claimed migration):** `011-scout-defs-2`,
`012-critic-proof-sections-c` (adaptive-three-point, critical-exponents), `013-scout-held-briefs-e`,
`014-tooling-task-board-check`, `015-critic-reread-proof-sections-a` (on the branch, before it merges),
`016-scout-d33-volume-law` (prepares D-33 package 17 for release after (e)), `154-audit-nm-multipoint-geometry`,
`155-audit-wiki-revise-regular-variation-r3`.
Written and already claimed or done this round: 000-audit-fix-workflows-r5 (done), 000-fix-workflows-r6 (done),
001-mig-model-norm, 002-pages-deploy, 003-docs-contrib-followup (done), 004-wiki-nc7f-precision (done),
005-critic-proof-sections-b (done), 006-audit-hier-j98j-tag (done), 007-audit-nm-tree-depth (done),
008-audit-docs-contrib-followup (done), 009-audit-wiki-nc7f-precision (done), 000-audit-fix-workflows-r6,
010-wiki-revise-proof-sections-b, 020-audit-nm-uniform-volume-r2 (done),
021-audit-frontier-four-functions-r2 (done), 090-audit-wiki-original-runaway-c (done).
**Held:** window (e): `HOLD-156`, `HOLD-157`, `HOLD-158`, `HOLD-389`, `HOLD-160-connection-kernel-tags`,
`HOLD-161-monotone-coupling-tag`, `HOLD-fix-nm-tree-depth` (+ `HOLD-audit-nm-tree-depth-r2`), `HOLD-200-nm-bond-core`
(+ `HOLD-audit-nm-bond-core`), `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-370`, `HOLD-371`, `HOLD-240`
(+ `HOLD-audit-nm-probability`); waiting for a done marker: `HOLD-audit-wiki-revise-proof-sections-b`.

Next packages to brief: the audit of `mig-model-norm`; the audit of `pages-deploy`; audits of `scout-defs-2` proposals
as interface packages; a reviser for `critic-proof-sections-c` when it reports (one reviser at a time: after 010); the
critic re-read after `fix-wiki-revise-proof-sections-a` merges, then the I.5.5/B5SL/2KB9 tag package; D-33 packages 17
(`lrp-volume-law`) and 18 (`lrp-I31-I32`) of `/home/user/reports/d33-map.md` (after (e): 17 reads `Models/LongRange/Defs`);
hierarchical H10 after `hier-cor12` merges (`/home/user/reports/hier-map.md`); near-misses B2ZL (after (e)), 32GP, NM-7
`nm-window-correlation` ((d) is merged: it may own `Tightness/Hyperscaling.lean` now); re-check NM-9's tags
70KD/UZ7J/C2YT/96A2 against 160; the exponential-moment dedup after `nm-uniform-volume` merges; the F75G hypothesis bundle
(optional); moving `ae_cluster_eq_singleton_of_offDiagonal`/`ae_openGraph_le_of_offDiagonal` and
`ae_edgeSet_subset_of_forall_eq_one` (audit-nm-tree-depth N3) into `Percolation/Bond`; the `unusedFintypeInType` clean-up;
the fold's clean-up list; the NC7F-style precision points as they come; restructuring the index and hubs (ruling 8: after
`pages-deploy` merges, since both touch `wiki/src`).


## For ARCHITECT

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

- **Pull request to `main` (rulings 13a, 15e):** open and merge
  https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 when you wish (summary in
  `/home/user/reports/READY-FOR-MAIN`). It brings the task board, the self-sufficient `AGENTS.md`/`CONTRIBUTING.md`,
  the lace-expansion map, the CI workflow (build and checks only, read-only token) and ten new proved tagged assertions.
  Last gated commit `df5d0fd` (gate passed 17:19); the commits after it touch only `tasks/` and docs. No kernel replay
  has passed since the baseline `4c72765` (two local runs were killed for memory; one is running at `df5d0fd`); once
  `ci.yml` is on `main`, CI runs the replay on every push. Auto-merge is not in it yet (final audit running, ruling 15c).
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
