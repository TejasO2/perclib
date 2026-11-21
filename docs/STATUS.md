# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 13:05 UTC, at the end of coordinator round 5 of the current series (sixteenth coordinator overall;
the previous file, round 9 of the earlier series, is at `874da60` and older rounds are in
`git log -p docs/STATUS.md`). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md), [COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md)
(D-34 to D-37) and `/home/user/reports/RULINGS.md` (rulings 1-12b; obey them; 10 and 11a authorise
pull requests to `main`). Container-local reports and briefs are copied for durability to
`lrp/docs/reports/` at each round's lrp commit (ruling 9i); `/home/user/reports/` stays the live copy.

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `caa28bc`** (pushed;
  extract `.lake/gate/caa28bc….json` saved); the tip is this STATUS/FRONTIER commit on top of it. **Next
  gate: `scripts/gate.sh caa28bc`.**
- **Round 5 (12:55-13:05): no merge, no gate** (nothing mergeable: the four done markers of the round were
  an audit asking for changes, a fix awaiting its re-audit, a premises audit, and a wiki follow-up whose brief
  requires a mechanical audit). Tip unchanged apart from this STATUS commit. Kernel replay still not run (the
  fold builds). **Proving reopened at 13:02** (ruling 11g, step 2 of the window plan below).
- **Round 4 (12:24-12:55): six gated batches, all passed, all pushed** (gate logs were in the round's
  scratchpad; counts below are copied from them). Every gate: build `--wfail` OK, axiom audit only
  `propext`/`Classical.choice`/`Quot.sound`, import closure, forbidden scan, script tests, "D-35 checks passed".
  1. `scripts/gate.sh 6e85f59` on **`031ef16`** (merge `fix-wiki-proof-F9EV`): 3,922 jobs, 5,990 constants,
     329 modules, "PROOF-ONLY change against 6e85f59: 0 Lean file(s)". Wiki `npm test` 100/100.
  2. `scripts/gate.sh 031ef16` on **`f33b4c1`** (merge `mig-def-bond`, migration (c) step 1): 6,045
     constants, "INTERFACE change against 031ef16: … PercLib/Percolation/Bond/Basic.lean" (expected: audited
     interface package, `audit-mig-def-bond` APPROVE with binder tables).
  3. `scripts/gate.sh f33b4c1` on **`e7cb06d`** (merge `hier-restricted-susc`): 6,060 constants, 330 modules,
     "PROOF-ONLY change against f33b4c1: 2 Lean file(s), no compiled interface change".
  4. `scripts/gate.sh e7cb06d` on **`c1f840a`** (merge `lrp-I55`): 6,110 constants, 331 modules, PROOF-ONLY.
  5. `scripts/gate.sh c1f840a` on **`62be6c2`** (merges `wiki-proof-67W9`, `lrp-weak-kernels`): 6,131
     constants, 332 modules, PROOF-ONLY; wiki `npm test` 100/100; merged 67W9 files byte-identical to `38232d3`.
  6. `scripts/gate.sh 62be6c2` on **`caa28bc`** (merge `lrp-tauber-complete`): 3,926 jobs, 6,167 constants,
     333 modules, "PROOF-ONLY change against 62be6c2: 2 Lean file(s), no compiled interface change",
     "== gate passed on caa28bc…".
- Kernel replay: **not run** (the migration worker `mig-localconn-fold` is building; 15 GB, never alongside
  a build). Last replay passed on the baseline `4c72765`. Run `scripts/kernel_replay.sh 6` when no Lean build
  runs; it is required before the first pull request to `main` (ruling 10(1)).
- **GitHub (round 5, 12:56):** unchanged: ToolSearch finds no GitHub MCP tool, `gh auth status` reports the
  `GH_TOKEN` invalid; anonymous read: no open pull requests, only issue #1. No pull request opened.
- **GitHub (round 4):** still no write tool: ToolSearch ("github pull request") finds no GitHub MCP tool,
  `gh auth status` says the `GH_TOKEN` is invalid. Anonymous read at 12:27: **no open pull requests**; one
  open issue, #1 (README; fixed on the integration branch at `882c3bf`). No pull request to `main` opened:
  **`main` (`1df822a`) lacks every commit since**, now including `caa28bc`.
- Rounds 1-3 of this series: see `git show 6f8ac2c:docs/STATUS.md` (gates A-D on `882c3bf`, `6d0833f`,
  `7e7b409`, `6e85f59`; mig-linters extract comparison; recovery of the round-10 merges).

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

## Progress (D-35 measure)

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

## Merged in round 4

- `fix-wiki-proof-F9EV` (`031ef16`; contains `wiki-proof-F9EV`): F9EV full proof in `finite-random-graphs`
  with the `(θ_++1)C` constants. `audit-wiki-proof-F9EV` (correctness) and `-r2` (mechanical) APPROVE.
- **`mig-def-bond`** (`f33b4c1`, migration (c) step 1): `localConn`, `localCluster` (OG96), `IsCut`,
  `boundaryFlux` (6EIM) in `Bond/Basic.lean`, `boundarySusceptibility` in `Bond/Intensity/Defs.lean`, with API
  (append-only). `audit-mig-def-bond` (fresh, binder tables OG96/6EIM no EXCESS, compiled `Iff.rfl` probes
  against today's spellings) APPROVE; its change (1) (free the plain names `measurableSet_localConn`,
  `isUpperSet_localConn`; drop the primes) is item 1 of the fold; fold notes (2) IsCut separately, (3) ℝ≥0∞
  rows take only the event fold.
- `hier-restricted-susc` (`e7cb06d`, proof-only): `exists_lintegral_clusterIntersection_le_at_rootCriticalIntensity`
  (Prop. 2.7 / upper half of 655W: `a_n(β_c) ≤ C' L^{αn}`, `C'` uniform in `J`), with D-5 witness.
- `lrp-I55` (`c1f840a`, proof-only, D-33 package 6): `CriticalDrivenODE.lean`; Lemma I.5.5 is an unproved
  target until `106-audit-lrp-I55-premises` reports (author lists premises: global measurability of `h`,
  `HasDerivAt` on `(0,∞)`, global positivity in the full lemma from the merged `b<a` case).
- `wiki-proof-67W9` (`e73aaba`): full collapsed proof of 67W9 (after DGT arXiv:2011.04642v2 §2.4).
  `audit-wiki-proof-67W9` APPROVE (its Change 1 optional; queued in `108-wiki-67W9-followup` with the stale
  "cited input" wording of NLDF/XP2Y and a provisional DGT erratum the auditor confirmed).
- `lrp-weak-kernels` (`62be6c2`, proof-only, D-33 packages 14-15): `Probability/WeakKernels.lean`.
- `lrp-tauber-complete` (`caa28bc`, proof-only, D-33 package 12): `Analysis/Tauberian/Complete.lean`.
- Worktrees removed: wiki-proof-F9EV, fix-wiki-proof-F9EV, mig-def-bond, audit-mig-def-bond (scratch),
  hier-restricted-susc, lrp-I55, wiki-proof-67W9, lrp-weak-kernels, lrp-tauber-complete.

## Finished, not merged (each waits for the item named)

- **`work/wiki-proof-2ZI0-tail`** (`5dea723`): proofs of the 2ZI0 critical tail and order-parameter
  estimates, by Hutchcroft's route (arXiv:2106.06400 §3). `audit-wiki-proof-2ZI0-tail` (round 5): **APPROVE WITH
  CHANGE**, both proofs correct and complete; two text changes (idea-paragraph sentence; explicit zero weights
  off nearest-neighbour pairs in Step 3), no tagged block touched. Fix **`114-fix-wiki-proof-2ZI0-tail`** queued,
  then `HOLD-audit-wiki-proof-2ZI0-tail-r2` (mechanical; release with the fixer's `<merge>`/`<fix>`). On APPROVE
  merge `work/fix-wiki-proof-2ZI0-tail` (contains the original branch), wiki test, gate.
- **`work/wiki-67W9-followup`** (`8803370` on `6c8a181`): audit-67W9 Change 1, stale "cited input" wording of
  NLDF/XP2Y reworded (article + record), provisional DGT erratum `bridge-box-edge-bound`. Mechanical audit
  **`116-audit-wiki-67W9-followup`** queued (diff and the 67W9 audit as source). On APPROVE merge, wiki test, gate.
- **Lemma I.5.5** (`CriticalDrivenODE.lean`, merged `c1f840a`): `audit-lrp-I55-premises` PROVED AS STATED (above).
  To count it: one interface package adding a wiki tagged block (in `marginal-ode`, beside B5SL, stating the
  paper's lemma) and its `Tags/` restatement of the full theorem, then a fresh binder-table audit. Brief it with
  the B5SL tag (both touch the driven-ODE material). The audit's optional §4 (drop `hpos`, weaken `hfpos` in the
  b<a theorem; strict generalisation) is a small prover package for later, not needed for fidelity.
- **`work/wiki-proof-WD31`** (`16a390a`): full proof of WD31 (duality, RSW, p_c=1/2 after Bollobás–Riordan,
  with four stated departures; upper bound via 6THJ). Correctness audit **`107-audit-wiki-proof-WD31`** queued.
- **`work/fix-wiki-runaway-split-1`** (`8bc1cd6`): `audit-wiki-runaway-split-1-r2` APPROVE WITH CHANGE, one
  sentence (first moment conserved only up to gelation, `multiplicative-coalescent`). Fix
  `fix-wiki-runaway-split-1-r2` done (merge `233ece3`, fix `6d47a91`, one-line diff checked); mechanical re-audit
  **`113-audit-wiki-runaway-split-1-r3`** released round 5 with those commits. On APPROVE merge `work/fix-wiki-runaway-split-1-r2`, then release
  `HOLD-wiki-original-marking` (ruling 11h) and queue runaway split step 2. The re-audit's non-blocking notes
  (MC lead wording, Z960 record reason, merging the three HR summaries) go to the next critic pass.
- **`work/fix-wiki-revise-regular-variation`** (`360214a` on merge `5ab23fc`): C1-C3 applied. Mechanical
  re-audit **`110-audit-wiki-revise-regular-variation-r2`** released. On APPROVE merge it (contains
  `wiki-revise-regular-variation`), then C4: a reading-map package retargeting 13 rows of
  `wiki/sources/perclib-dfbc5b4-analysis-symmetry.md`; then a critic re-read and the §3 sketched-proof package.
- **Model article** `work/fix-wiki-model-hier-two-point-r3` (`d38d03d` on merge `a8fda42`): `R_0=2` applied.
  Re-audit **`111-audit-wiki-model-hier-two-point-r4`** released. On APPROVE merge it, wiki test, gate, list
  the page for Tom (`/articles/hierarchical-two-point/`) with the reviser's §5 questions; then queue the J98J
  Lean tag (interface), critic R2/R4/R6 (V4QQ, YWTU precise; constants in 655W, 7YNX; fresh audit), runaway
  split step 8.
- **`work/tooling-d35-header-blocks`** (`c01bf41`): `audit-tooling-d35-header-blocks` APPROVE WITH CHANGE
  (changes 1-3 in `header_text`; change 1 closes a fail-open on valid Lean). Fix
  **`109-fix-tooling-d35-header-blocks`** queued, then `HOLD-audit-tooling-d35-header-blocks-r2`.
- **Workflows and scanner:** `work/fix-scanner-r4` (`0707396` on merge `3c65334`) and `work/fix-workflows-r4`
  (`0471b5e` on merge `1ab3c5c`) done 12:50/12:53; re-audit **`112-audit-fix-workflows-r4`** released 12:55. Merge order on APPROVE: `work/fix-scanner-r4`, then
  `work/fix-workflows-r4`, gate; the workflows must not reach `main` before AM4. Then `work/contrib-docs` and
  `work/task-board` (check against the tip), mirror the queue into `tasks/` (ruling 9b), open the
  pages-deploy brief (ruling 12).
- **`critic-proof-sections-a`**: revision `103-wiki-revise-proof-sections-a` claimed 12:48; then
  `HOLD-audit-wiki-revise-proof-sections-a`, then a critic re-read. S-S1 and M-B2 as recorded in round 3
  (`git show 6f8ac2c:docs/STATUS.md`).
- `work/wiki-I421`'s Lean counterpart: the `@[tag "B5SL"]` restatement (interface; not yet briefed; it touches
  `DrivenODE.lean`, outside the fold: brief it after the window closes).
- `work/nm-longrange` (`e4e9b59`; ZH13, R01V): `095-fix-nm-longrange` held for the window
  (`HOLD-095-fix-nm-longrange`); release first when proving reopens. The IsCut fold (`mig-iscut-fold`,
  scout-localconn-fold §6) follows it.

## In flight (claims without a done marker at 13:03)

`mig-localconn-fold` (claimed 12:39; live: commits P0 `23d0619`, P1 `06fc758` "respell the bond area files" by
13:01, P2-P3 to come), `wiki-revise-proof-sections-a` (12:48), `audit-wiki-proof-WD31` (~12:57),
`fix-tooling-d35-header-blocks` (~12:58). Briefs released at 13:02 may be claimed by now: check `claims/`.
Worktrees kept (unmerged; add wiki-67W9-followup, fix-wiki-runaway-split-1-r2):
automerge-workflow, ci-workflow, contrib-docs, task-board, fix-gate-scanner, fix-workflows(-r2,-r3,-r4),
fix-scanner-r2/-r3/-r4, nm-longrange, port-wiki-hier-thm11, fix-port-wiki-hier-thm11, wiki-model-hier-two-point,
fix-wiki-model-hier-two-point(-r3), wiki-runaway-split-1, fix-wiki-runaway-split-1, wiki-revise-regular-variation,
fix-wiki-revise-regular-variation, tooling-d35-header-blocks, wiki-proof-2ZI0-tail, wiki-proof-WD31,
wiki-revise-proof-sections-a, mig-localconn-fold.

## Migration window (c): fold `mig-localconn-fold` running; proving reopened beside it (round 5, 13:02)

**Round 5 decision (step 2 below, ruling 11g):** the window opened in round 4 (12:40) and the fold was still in
phase 1 of 3 at 13:01, so proving was reopened rather than letting the window exceed one round. Released, all on
files disjoint from the fold's owned list (checked by script against the list in `081-mig-localconn-fold.md`),
from each other and from the claims: 092 lrp-I526, 093 lrp-first-moment-b, 095 fix-nm-longrange, 096
nm-finite-coordinates, 098 nm-uniform-volume, 099 frontier-four-functions (round-2 note plus a round-5 line), and
381 KJWA, 382 8IGH, 384 04ZI, 385 PAFY, 386 QW2L, 387 F75G, 388 57FJ, 389 19IN (G3/G5 edits of
scout-hold-briefs-check applied, round-5 note appended; all new files; none of their tags is in the library yet).
The fold is not stopped: when it finishes, steps 1 and 3-5 below still apply, except that (d) and (e) must be
checked for file-disjointness against whatever prover work is claimed then (as in round 2), or wait for it to merge.
Still held: 383 (needs its edit: area lemmas only, it names fold files `FiniteSetCriterion`/`SusceptibilityDerivative`).

Round-4 text (still the plan for the fold itself):

Precondition met this round: `mig-def-bond` audited and merged (`f33b4c1`). At 12:36 the coordinator held
every unclaimed Lean prover brief (092, 093, 095, 096, 098, 099 renamed `HOLD-…`) and released the fold as
`081-mig-localconn-fold` at 12:40 on tip `e7cb06d` (census rerun there: A 167 statement / 87 proof sites, no
file outside the owned list; the scout's draft took the strict `Iff.rfl` rule, 9 tags change: USAC, YLZV, R84Z,
5UJQ, 6QN7, 7902, 67GX, 7BMQ, JTBG). Three prover briefs (087, 089, 090) had been claimed seconds before the
hold, on new files disjoint from the fold; all three finished and merged this round. **Now the fold is the
only claimed Lean work.** Non-Lean work continues (ruling 11f).
Next steps, in order:
1. When `done/mig-localconn-fold` exists: read its report, check `git log`, then release
   `HOLD-audit-mig-localconn-fold` (fill in head and base; mechanical audit, compiled checks). Pre-gate the branch
   in a detached worktree while the audit runs (lesson below). On APPROVE: merge, gate, push.
2. Ruling 11g: each migration no longer than one round. If the fold has not finished by the end of round 5,
   reopen proving (rename the `HOLD-09x` briefs back, file-disjoint from the fold's owned list, which is in the
   brief) and retry the fold later.
3. **(d):** `HOLD-mig-law-generality` after the fold merges; before release take items 1-3 (ZAIH, NEM5, 6HJ9)
   out of `HOLD-200-nm-bond-core`, update the tip, write its held audit.
4. **(e):** `HOLD-mig-model-norm` (ModelNorm; re-audit PVA8, MQNP, LF50, 6YYS) after (d); release before 371
   and 230.
5. Reopen proving after the fold merges (and between migrations if (d) waits): release 095 first (then
   `mig-iscut-fold`), 092, 093, 096, 098, 099, then 381, 382, 384-389 with the G3/G5 common edits and the
   round-2 note (as in 086-099), and the I.5.5 positivity strengthening if `audit-lrp-I55-premises` asks for it.
**Still held otherwise:** 200 (after (d)); 210, 220, 230, 370, 371 (after (e)); 360 (after the fold); 330 (086
has merged: release after the fold, telling the worker that `HierarchicalEndpoint` statements are respelled with
`localConn`), then 335; 362 after 095 merges, never with scout-defs D2; 361 not with scout-defs D1; 240 after
its scout edit; 383 after its edit (area lemmas, never H0OC).

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the
directory. **Startable at 13:03 (22; mutually file-disjoint and disjoint from the claims):** Lean (14): 092, 093,
095, 096, 098, 099, 381, 382, 384-389 (see the window section). Non-Lean (8): 110
audit-wiki-revise-regular-variation-r2, 111 audit-wiki-model-hier-two-point-r4, 112 audit-fix-workflows-r4, 113
audit-wiki-runaway-split-1-r3, 114 fix-wiki-proof-2ZI0-tail (owns `triangle-condition.md` and its baseline digest),
115 audit-wiki-original-runaway-a (J0DE, MFGT, OQV3) and -b (Q4PO, F7Q2, NC7F) (ruling 11h low-priority correctness
audits of wiki-original results, read-only at `6c8a181`; Q7QG, V7MP, 9FO5 still to brief), 116
audit-wiki-67W9-followup. Workers take the alphabetically first, so the six 09x Lean briefs go first.
**Held added in round 5:** `HOLD-audit-wiki-proof-2ZI0-tail-r2`. Released: `HOLD-audit-wiki-runaway-split-1-r3`
(as 113). Round-4 list for reference:
**Startable at 12:55 (9, all non-Lean: the eight below plus 112 audit-fix-workflows-r4; mutually file-disjoint and disjoint from the claims):**
104 audit-wiki-proof-2ZI0-tail, 105 fix-wiki-runaway-split-1-r2 (owns `multiplicative-coalescent.md`), 106
audit-lrp-I55-premises, 107 audit-wiki-proof-WD31, 108 wiki-67W9-followup (owns `integrated-susceptibility.md`
+ record, `wiki/errata/dgt-long-range-2023.json`), 109 fix-tooling-d35-header-blocks (owns `scripts/check_d35.py`,
`scripts/test_check_d35.py`), 110 audit-wiki-revise-regular-variation-r2, 111 audit-wiki-model-hier-two-point-r4.
Lean prover briefs are held for the window (see above); this is the window, so fewer than 8 Lean briefs are
startable by design.
**Held:** `HOLD-audit-mig-localconn-fold`, `HOLD-audit-wiki-runaway-split-1-r3`,
`HOLD-audit-tooling-d35-header-blocks-r2`, `HOLD-audit-wiki-revise-proof-sections-a`,
`HOLD-mig-law-generality`, `HOLD-mig-model-norm`, `HOLD-wiki-original-marking`, `HOLD-audit-nm-bond-core`,
`HOLD-audit-nm-probability`, the six window-held prover briefs `HOLD-092/093/095/096/098/099`, and the 21
prover briefs listed in the migration section.

Next packages to brief, in order: the fold's audit release; merges named above; the C4 reading-map package
after the regular-variation fix merges; the next critic pass (one critic at a time) of the new proof sections
of `integrated-susceptibility`, `finite-random-graphs`, `triangle-condition`, `adaptive-three-point`,
`critical-exponents` once their packages merge; the B5SL Lean tag after the window; the
`unusedFintypeInType`/`unusedDecidableInType` clean-up (44 declarations, ≥5 tagged; interface, after the
migrations); the `op8f_asymptotics` rename with a deprecated alias; runaway M1/M3/M4/M5 after the split moves
their tags; scout-defs D1, D2, D3a, D6; the `DrivenODE.normalized_increment_of_driving_ode` dedup (now a
corollary of `normalized_increment_of_ae_driving_ode`; lrp-I55 report); the tasks board mirror once
`task-board` merges.

## For ARCHITECT

- **No GitHub write access in this session.** Rulings 10(1) and 11a ask for a pull request from
  `claude/zen-lovelace-rvlcw2` to `main` after each gated batch; the launch text says to use the GitHub
  MCP tools, but none is loaded (ToolSearch finds none) and `gh` reports the `GH_TOKEN` invalid. No pull
  request was opened, issue #1 was not answered. Anonymous reads work (no open pull requests). Please
  give the coordinator a working GitHub tool or token; until then `main` stays at `1df822a`. (Rechecked in
  round 4: still no tool; `main` now lacks everything up to `caa28bc`, six gated batches of this round included.
  Round 5: unchanged.)
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

## For Tom

- **Licence notices (from `mig-linters`).** Six files keep their third-party headers and the header
  linter stays off: `Probability/ProdBernoulli.lean`, `Probability/Harris.lean`,
  `Probability/Cylinder.lean` (adapted from PercolationContinuity, Anthropic PBC), `Models/Site/Basic.lean`,
  `Percolation/Bond/Basic.lean` (Percolation, Apache 2.0 via `third_party/percolation/`),
  `Probability/Russo.lean` ("adapted from NearCritical/Russo.lean by Tom Hutchcroft and collaborators").
  Either prepend a mathlib-form block naming the upstream holder and keep the old notice below it, or
  keep the linter off for these headers. Your choice.
- **Issue #1** (README) is fixed on the integration branch (`882c3bf`); it reaches `main` with the first
  pull request.

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
- The model article `hierarchical-two-point` (ruling 8) is restructured, has passed a correctness audit,
  a second critic read and a re-audit that asked for one constant (`R_0=2`); the first fixer stopped on a conflict, so
  the fix is re-briefed (`094-fix-wiki-model-hier-two-point-r3`, then a mechanical re-audit). On approval it merges and the page to look at is
  `/articles/hierarchical-two-point/` (listed here then with the reviser's open questions).

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
