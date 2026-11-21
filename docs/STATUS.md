# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 16:35 UTC, at the end of coordinator round 1 of a new series (nineteenth coordinator overall;
the previous handoff, round 7 of the last series, is at `e29bacf`; older rounds are in
`git log -p docs/STATUS.md`). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md), [COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md)
(D-34 to D-37) and `/home/user/reports/RULINGS.md` (rulings 1-13; obey them; 13 is new since the last handoff:
(a) no GitHub write tool, keep one compare-link line "For Tom", stop reporting it; (b) kernel replay this round and
after every tenth merged batch, in a separate niced worktree; (c) the workflows merge once an audit finds no hole for
unlisted authors or write tokens; scanner gaps become documented known limitations). Container-local reports and
briefs are copied for durability to `lrp/docs/reports/` at each round's lrp commit (ruling 9i).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `cfef666`** (pushed; extract
  `.lake/gate/cfef666….json` saved); the tip is this STATUS commit on top of it. **Next gate: `scripts/gate.sh cfef666`.**
  `docs/FRONTIER.md` from `5fb1db4` is still current (no tag added or removed since).
- **Round 1 of this series (16:22-16:40): one gated batch, passed, pushed.** `scripts/gate.sh 78ee775` on **`cfef666`**
  (merge `mig-iscut-fold`, migration (c) last part): build `--wfail` OK (3,932 jobs), axiom audit 6,302 constants only
  `propext`/`Classical.choice`/`Quot.sound`, import closure 339 modules, forbidden scan 339 files, script tests,
  "D-35 checks passed", "INTERFACE change against 78ee775147a4: … Tags/CutsAndRows.lean: ['tag']" (expected:
  `audit-mig-iscut-fold` APPROVE, 50 compiled `@decl`/`Iff.rfl` checks, BQ44/ZH13 binder tables, no EXCESS),
  "== gate passed on cfef666…". **Migration (c) is complete.**
- **Kernel replay (ruling 13b): STARTED, NOT FINISHED.** `nice -n 15 scripts/kernel_replay.sh 6` in the detached
  worktree `/home/user/wt/replay-cfef666` (at `cfef666`, `.lake/packages` symlinked, `.lake/build` copied), started
  16:27, log `/home/user/reports/replay-cfef666.log` (symlink to the round's scratchpad). It runs slowly beside four
  worker builds (12/338 modules after 6 minutes). Next coordinator: `tail` the log; "Kernel replay passed: 338
  modules." means pass at `cfef666` (record it, then `git worktree remove /home/user/wt/replay-cfef666`); a checker
  error names the module (record it "For ARCHITECT", do not merge further until understood); if the process
  (`pgrep -f kernel_replay.sh`) is gone with neither line, the run was killed (OOM or container): restart it the same
  way. Last replay that passed: baseline `4c72765`.
- **GitHub:** no GitHub MCP tool (ToolSearch), `main` still `1df822a` (`git ls-remote`). Anonymous read 16:30: 0 open
  pull requests, issue #1 only (fixed on the integration branch). Per ruling 13(a) this is no longer a question for
  ARCHITECT; the one line for Tom is under "For Tom".
- **Round 7 (13:15-14:05): seven gated batches, all passed, all pushed.** Batch 7: `scripts/gate.sh 5fb1db4` on
  **`78ee775`** (merge `hier-thm11`): 3,932 jobs, 6,303 constants, 339 modules, "D-35 checks passed", "PROOF-ONLY
  change against 5fb1db4: 2 Lean file(s), no compiled interface change", "== gate passed on 78ee775…". Batches 5 and 6:
  5. `scripts/gate.sh e57e4b0` on **`a117338`** (merges `mig-localconn-fold` = migration (c) step 2, and
     `nm-longrange`): build `--wfail` OK (3,930 jobs, full rebuild of the fold's dependants, about 9 min),
     axiom audit 6,232 constants, closure 337 modules, "D-35 checks passed", "INTERFACE change against e57e4b0"
     (expected: fold audit APPROVE 9/9 tags by compiled `Iff.rfl`; R01V/ZH13 audit r2 APPROVE), "== gate passed".
  6. `scripts/gate.sh a117338` on **`5fb1db4`** (merges `nm-finite-coordinates`, `fix-wiki-proof-2ZI0-tail`,
     `fix-wiki-proof-WD31`, `wiki-rv-reading-map`): 3,931 jobs, 6,283 constants, 338 modules, "D-35 checks passed",
     "INTERFACE change against a117338" (expected: CPD6/XSA6/D1CH/DL0X/XRSL audit APPROVE), "== gate passed"; wiki
     `npm test` 100/100; merged wiki files byte-identical to the audited `47faa52` / `6afd5f9`.
  Batches 1-4: Every gate: build `--wfail` OK
  (3,928 jobs), axiom audit 6,226 constants only `propext`/`Classical.choice`/`Quot.sound`, import closure
  335 modules, forbidden scan, script tests, "D-35 checks passed", "== gate passed on …" (logs were in the
  round's scratchpad; counts copied from them).
  1. `scripts/gate.sh 1146988` on **`c1c4083`** (merge `lrp-I526`): "PROOF-ONLY change against 1146988: 2 Lean
     file(s), no compiled interface change" (2.5 min, beside worker builds).
  2. `scripts/gate.sh c1c4083` on **`d5e7d58`** (merges `fix-wiki-model-hier-two-point-r3`,
     `fix-wiki-revise-regular-variation`): PROOF-ONLY, 0 Lean files; wiki `npm test` 100/100 on the merged
     tree; merged articles/records byte-identical to the audited `d38d03d` / `360214a`.
  3. `scripts/gate.sh d5e7d58` on **`3da8955`** (merge `fix-wiki-runaway-split-1-r2`): PROOF-ONLY, 0 Lean
     files; wiki `npm test` 100/100; the three coalescent articles byte-identical to the audited `6d47a91`.
  4. `scripts/gate.sh 3da8955` on **`e57e4b0`** (merge `fix-tooling-d35-header-blocks`): PROOF-ONLY, 0 Lean
     files; `pytest scripts/test_check_d35.py` 12 passed.
  Merge repairs: `wiki/tests/lead.test.mjs` conflicted twice (each wiki branch had rewritten the
  frozen-digest test); resolved to the hierarchical-two-point form, which subsumes the other two (frozen
  articles are checked against their lead digest; articles outside the baseline may carry a lead).
  Kernel replay still **not run** (workers built Lean throughout). GitHub: unchanged (no GitHub MCP tool
  found by ToolSearch, `gh auth status`: `GH_TOKEN` invalid; anonymous read 13:18: 0 open pull requests,
  issue #1 only). `main` (`1df822a`) lacks everything up to `e57e4b0`.
- **Round 6 (13:03-13:16): one gated batch, passed, pushed.** `scripts/gate.sh caa28bc` on **`1146988`** (merge
  `lrp-first-moment-b`): build `--wfail` OK (3,927 jobs), axiom audit 6,194 constants only
  `propext`/`Classical.choice`/`Quot.sound`, import closure 334 modules, forbidden scan, script tests, "D-35 checks
  passed", "PROOF-ONLY change against caa28bc: 2 Lean file(s), no compiled interface change", "== gate passed on
  1146988…" (2.5 min, run beside three worker Lean builds without OOM). Kernel replay still **not run** (workers
  were building throughout). GitHub: unchanged (no MCP tool, `GH_TOKEN` invalid; anonymous read 13:05: 0 open pull
  requests, issue #1 only). `main` (`1df822a`) lacks everything up to `1146988`.
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

## Merged in round 1 (new series)

- **`mig-iscut-fold`** (`063e197`, merged `cfef666`): `IsCut` respelling in `Models/LongRange/{CutPoints,OneDimensional}.lean`
  and `Models/LongRange/Tags/{DisplacementKernels,CutsAndRows}.lean`; `measurableSet_cut` deleted (replacement
  `measurableSet_setOf_isCut`). `audit-mig-iscut-fold` APPROVE (fresh, mechanical: 22 named + 3 anonymous
  declarations by compiled `@decl` and `Iff.rfl`, two negative controls, census 59 → 58 `IsCut` + 1 deleted). Cosmetic
  note for a later touch: redundant parentheses in `cut_image_sym2Map_add_iff`. Worktree removed.

## Merged in round 7

- `lrp-I526` (`c1c4083`, proof-only, new file `PercLib/Analysis/SignedDrivenODE.lean`, D-33 Lemma I.5.26): eleven
  public theorems in `PercLib.Analysis`; `tendsto_div_of_ae_mul_deriv_eq` is the 2KB9 generality (8 hypotheses,
  none EXCESS by the author's table; it omits four of 2KB9's hypotheses: positivity and local integrability of
  `h`, local boundedness of `ε, δ`), and (b)-(d) of the port follow from it without the paper's `hO`. 2KB9 is not
  tagged: a later interface package either restates (e) with the four binders unused or relaxes the wiki
  statement (fresh audit). Core lemma `tendsto_div_of_ae_mul_deriv_eq_of_abs_le` has 13 hypotheses (internal);
  the author seconds a "measurable, → 0, |·| ≤ 1 on a tail" structure (interface, later).
- `fix-wiki-model-hier-two-point-r3` (`c8e3d2c`; contains the model article and J98J): `audit-...-r4` APPROVE
  (`R_0=2` only change, byte-checked; npm 100/100). The page for Tom: `/articles/hierarchical-two-point/`.
- `fix-wiki-revise-regular-variation` (`d5e7d58`; contains the revision): `audit-...-r2` APPROVE (C1-C3 verbatim).
  C4 queued as `126-wiki-rv-reading-map`; critic re-read queued as `127`.
- `fix-wiki-runaway-split-1-r2` (`3da8955`; contains split step 1): `audit-...-r3` APPROVE. Released
  `125-wiki-original-marking` (ruling 11h).
- `fix-tooling-d35-header-blocks` (`e57e4b0`; contains `tooling-d35-header-blocks`): `audit-...-r2` APPROVE.
- **`mig-localconn-fold`** (`9fe7989`, migration (c) step 2): `audit-mig-localconn-fold` APPROVE (fresh, 111 compiled
  `Iff.rfl` checks, 9 changed tags with binder tables, 10 unchanged confirmed, renames/deletions checked; scratch
  copies in `/home/user/reports/audit-mig-localconn-fold-scratch/`, the author's in
  `/home/user/reports/drafts/mig-localconn-fold-scratch/`). Notes for later: `sites.py` regex `\w+` → `[\w']+`;
  close duplicates and old-vocabulary names listed by the author (clean-up package).
- **`nm-longrange`** (`a117338`): R01V (ordered pairs), ZH13; `audit-nm-longrange-r2` APPROVE. Its notes: an `IsCut`
  respelling (now running as `mig-iscut-fold`).
- **`nm-finite-coordinates`** (merged in `5fb1db4`): CPD6, XSA6, D1CH, DL0X, XRSL; `audit-nm-finite-coordinates`
  APPROVE (all five, binder tables, no required change; non-blocking observations in the audit). Follow-ups from the
  author: move `prodBernoulli_restrict_apply` out of `Probability/Tags/ProductModel.lean`; set-level pivotal event
  definition proposal (scout-defs list).
- `fix-wiki-proof-2ZI0-tail` (2ZI0 tail proofs; audit + r2 APPROVE), `fix-wiki-proof-WD31` (WD31 proof; audit + r2
  APPROVE), `wiki-rv-reading-map` (C4 of the regular-variation audit; 13 rows, coordinator's mechanical check that only
  the last cell of those rows changed, links resolve: npm 100/100).
- **`hier-thm11`** (`78ee775`, proof-only, new file `PercLib/Models/HierarchicalTwoPointAveraged.lean`): **Theorem
  1.1 of arXiv:2103.17013v1** (averaged critical two-point bounds, H8 of the hierarchical programme) proved exactly
  as the Prop `HierarchicalTwoPointAveraged` of `Models/Hierarchical/Defs.lean` states, constants chosen before `J`
  and depending only on `d, L, α, c, C`. Not yet counted as a wiki assertion: the J98J tag is a separate interface
  package (next item to brief: tag the theorem or a restatement with J98J, fresh binder-table audit against
  `hierarchical-two-point.md#tag-J98J`, whose statement includes `β_c < ∞` and the symmetric-kernel hypotheses).
  Released `108-hier-cor12` (H9, Corollary 1.2, W498 Prop, and V4QQ/YWTU unconditionally).
- Worktrees removed: hier-thm11, mig-localconn-fold (its `scratch/` moved as above), nm-longrange, nm-finite-coordinates,
  wiki-proof-2ZI0-tail, fix-wiki-proof-2ZI0-tail, wiki-proof-WD31, fix-wiki-proof-WD31, wiki-rv-reading-map,
  lrp-I526, wiki-model-hier-two-point, fix-wiki-model-hier-two-point(-r3),
  wiki-revise-regular-variation, fix-wiki-revise-regular-variation, wiki-runaway-split-1,
  fix-wiki-runaway-split-1(-r2), tooling-d35-header-blocks, fix-tooling-d35-header-blocks.

## Merged in round 6

- `lrp-first-moment-b` (`1146988`, proof-only, new file, D-33 package "first moment b"): nine public theorems in
  `PercLib.Analysis` (error decomposition, perturbed bootstrap `bootstrap_perturbed` /
  `exists_forall_le_of_bootstrap_perturbed`, Riccati lower bound, closed form of `1+𝓗_r`, log-integrability of the
  error, `tendsto_div_rpow_of_one_sub_mul_one_sub_error`). D-33 premises (sharpness threshold, a-priori bound, error
  bound, left limit, ODE) are explicit hypotheses; four theorems have 11-14 hypotheses (the source's; the author
  suggests an ODE-hypotheses structure: interface package, later). Worktree removed.

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

- **`work/lrp-I56-gyration`** (`9df1a8b` on `e29bacf`; done 16:31): **proof-only** (two new files
  `PercLib/Analysis/{CriticalLogODE,GyrationReduction}.lean`, 16 public theorems, no def/tag; D-33 package 7: Lemma
  I.5.6 and the analytic reduction of Prop. I.5.2). Arrived after this round's single batch: **merge in the next batch
  on the gate** (conflict only in `PercLib.lean` imports).
- **`work/frontier-coupling-ratio`** (`4fbe172` on `a117338`, KJWA): `audit-frontier-coupling-ratio` **APPROVE** (16:34,
  fresh, binder table, no required change; optional docstring note). **Merge in the next batch** with `lrp-I56-gyration`
  (expected: INTERFACE notice for KJWA), push.
- **Interface packages awaiting fresh audits (all queued, all on new files or append-only area files):**
  `work/frontier-revealment-derivative`
  (`fd52af5`, 8IGH, 135), `work/frontier-reciprocal-cutoff` (`3000e12`, 04ZI, 136), `work/frontier-inverse-square-block`
  (`b2c8409`, PAFY, 137), `work/frontier-integrated-lower-tail` (`1c5a9ba`, F75G, 144), `work/frontier-rv-composition`
  (`af2d1f6`, 57FJ, 145), `work/frontier-sqrt-lower-bound` (`a0ca55a`, QW2L, 146), `work/frontier-root-global-percolation`
  (`4d9f278`, 0YH8, 147); **new this round:** `work/nm-core-wrappers` (`6d43725` on `5fb1db4`; RU6O, JZN0, 1C8G, 5LNL,
  WD2J, H48I; audit **148**), `work/nm-kernels-sitepaths` (`b6162c0` on `5fb1db4`; U8CI, K38T, 5U4L; audit **149**; it
  adds an import of `Models/HierarchicalCutoff` to `Models/NonSummable.lean`), `work/nm-tree-split` (`ff0e16c` on
  `78ee775`; RZSW; audit **152**). On APPROVE: merge (imports only conflict), gate. None of these branches uses a name
  that migration (d) renames (coordinator's grep of every `+` line, 16:28), so they merge before or after (d).
- **`work/nm-uniform-volume`** (`69ec361`): audit APPROVE WITH CHANGES (YVJT witness). Fix **held** as
  `HOLD-138-fix-nm-uniform-volume` during window (d), then `HOLD-audit-nm-uniform-volume-r2`.
- **`work/frontier-four-functions`** (`5ceed9b`): audit APPROVE WITH CHANGES (drop the untagged powerset corollary
  from the Tags file). Fix **held** as `HOLD-139-fix-frontier-four-functions` during (d), then
  `HOLD-audit-frontier-four-functions-r2`.
- **`work/wiki-revise-proof-sections-a`** (`024def9`): APPROVE WITH CHANGES; fix **140** queued, then
  `HOLD-audit-wiki-revise-proof-sections-a-r2`; then a critic re-read; it owns `marginal-ode.md`, so the I.5.5/B5SL and
  2KB9 tag package waits for it.
- **`work/fix-wiki-67W9-followup`** (merge `0f8d9a2`, fix `f73ebde`): mechanical re-audit **142** queued. On APPROVE merge,
  wiki test, gate.
- **`work/wiki-original-marking`** (`168800a`): mechanical audit **141** queued. On APPROVE merge, wiki test, gate. Then the
  NC7F precision fix and correctness audits for Q7QG, V7MP, 9FO5.
- **Regular-variation, critic r2:** reviser **143** queued, then `HOLD-audit-wiki-revise-regular-variation-r3`, then a third
  critic read.
- **Workflows and scanner (ruling 13c applied this round):** fixes **150-fix-scanner-r5** and **151-fix-workflows-r5**
  queued; 151 now also writes `docs/CI_KNOWN_LIMITATIONS.md` (scanner/classifier are lexical approximations, not a
  security boundary; S1-S6 listed). `HOLD-audit-fix-workflows-r5` now decides only on (A) can an unlisted author's
  pull request merge without a maintainer, (B) can pull-request code reach a write token or secret; new desync classes
  that open neither are recorded as known limitations, not required changes. **This is the last scanner round**: on its
  approval merge `fix-scanner-r5`, then `fix-workflows-r5` (both contain their r4 branches), gate, and then
  `contrib-docs`, `task-board`, the `tasks/` mirror (ruling 9b) and `pages-deploy` (ruling 12).
- **Lemma I.5.5** (PROVED AS STATED) and **2KB9**: one tag package after 140's branch merges (unchanged plan).
- **Wiki-original results** (ruling 11h): unchanged (NC7F wording fix after 141's merge).

## In flight (claims without a done marker at 16:35)

`lrp-I32-analytic` (16:22), `nm-multipoint-geometry` (16:22), `mig-law-generality` (16:31; migration (d)),
`audit-frontier-revealment-derivative` (16:34). Also running: the kernel replay (above).
Worktrees kept (unmerged): automerge-workflow, ci-workflow, contrib-docs, task-board, fix-gate-scanner,
fix-workflows(-r2,-r3,-r4), fix-scanner-r2/-r3/-r4, port-wiki-hier-thm11, fix-port-wiki-hier-thm11,
wiki-revise-proof-sections-a, wiki-67W9-followup, fix-wiki-67W9-followup, nm-uniform-volume, frontier-four-functions,
wiki-original-marking, the eight frontier branches, nm-core-wrappers, nm-kernels-sitepaths, nm-tree-split,
lrp-I56-gyration, replay-cfef666, and the claimed packages' worktrees.

## Migration window (d): open since 16:30

Migration (c) completed with `cfef666`. Window (d) opened this round on the strict reading the launcher asked for:
**the only startable Lean brief is `100-mig-law-generality`** (claimed 16:31); every other unclaimed Lean brief was renamed
`HOLD-` (108 hier-cor12, 133 nm-tree-depth, 138, 139, 389; plus the new `HOLD-109-hier-j98j-tag`). Non-Lean work (audits,
wiki, tooling) stays startable (ruling 11f). Claimed Lean work beside it (lrp-I32-analytic, nm-multipoint-geometry) is on
files disjoint from (d)'s owned list and calls none of its renamed names; no caller of a renamed name exists outside
(d)'s owned files at `cfef666` (coordinator's `git grep -lw` of every name). The brief was edited before release:
ids made consistent (claim/report/done marker `mig-law-generality`; branch and worktree `work/law-generality`), tip and
fold status updated.
Next steps, in order:
1. When `done/mig-law-generality` appears: read `authors/mig-law-generality.md` for the head commit only, fill
   `<head>`/`<base>` in `HOLD-audit-mig-law-generality.md` (`git log work/law-generality`), number it low (e.g. `100-`) and
   release it. On APPROVE: merge, gate (INTERFACE expected: Q0D1), push.
2. **Reopen proving** as soon as (d) has merged (or if (d) has not finished within one round: reopen anyway and retry
   later, ruling 11g): rename back `HOLD-108-hier-cor12`, `HOLD-109-hier-j98j-tag`, `HOLD-133-nm-tree-depth`,
   `HOLD-138-…`, `HOLD-139-…`, `HOLD-389-…` (drop `HOLD-`), and release `HOLD-200` (items 4+) and `HOLD-audit-nm-bond-core`
   (they wait for (d)). Then (e) `HOLD-mig-model-norm`, run as its own window the same way; after (e): 210, 220, 230,
   370, 371; 240 after its scout edit.

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the directory.
**Startable at 16:35 (15, mutually file-disjoint and disjoint from the claims):** audits 136-137, 144-147 (six frontier
interface audits, read-only scratch builds), 148 audit-nm-core-wrappers, 149 audit-nm-kernels-sitepaths, 152
audit-nm-tree-split (new), 141 audit-wiki-original-marking, 142 audit-wiki-67W9-followup-r2; wiki 140
fix-wiki-revise-proof-sections-a, 143 wiki-revise-regular-variation-r2; tooling 150 fix-scanner-r5, 151 fix-workflows-r5.
(Claimed: 100 mig-law-generality, 135 audit-frontier-revealment-derivative; 134 done, APPROVE.)
**Held:** for window (d): `HOLD-108-hier-cor12`, `HOLD-109-hier-j98j-tag` (new: `@[tag "J98J"]` on the Prop
`HierarchicalTwoPointAveraged`, dropping `c ≤ C`), `HOLD-133-nm-tree-depth`, `HOLD-138-fix-nm-uniform-volume`,
`HOLD-139-fix-frontier-four-functions`, `HOLD-389-frontier-riccati-linear-error`; after (d): `HOLD-200-nm-bond-core`,
`HOLD-audit-nm-bond-core`; (e): `HOLD-mig-model-norm`, then 210, 220, 230, 370, 371, 240 (+`HOLD-audit-nm-probability`);
re-audits waiting for fixers: `HOLD-audit-mig-law-generality`, `HOLD-audit-nm-uniform-volume-r2`,
`HOLD-audit-frontier-four-functions-r2`, `HOLD-audit-wiki-revise-proof-sections-a-r2`,
`HOLD-audit-wiki-revise-regular-variation-r3`, `HOLD-audit-fix-workflows-r5`.
Lean briefs queued (startable or held): 12, satisfying ruling 11g's 8+ once the window closes.

Next packages to brief, in order: audit of `hier-j98j-tag` when done (binder table against `tag-J98J`); audits of
`lrp-I32-analytic` (if it adds tags) and `nm-multipoint-geometry` (9YE6, interface) when done; I.5.5 + B5SL + 2KB9 tag
package after 140's branch merges; the exponential-moment dedup after `nm-uniform-volume` merges; the NC7F precision fix
after 141's merge; correctness audits of Q7QG, V7MP, 9FO5 (low priority); critic passes (one at a time) on the proof
sections of `integrated-susceptibility`, `finite-random-graphs`, `triangle-condition`, `adaptive-three-point`,
`critical-exponents`; near-miss B2ZL (after (e)) and 32GP, NM-4 `nm-graph-certificates`, NM-6..NM-9 of
`scout-nearmiss.md`; D-33 packages 17-18 after 16; hierarchical H10 after hier-cor12 (`hier-map.md`); the definition
proposals collected (`chiCriticalIntensity`, a transitivity predicate for kernels, off-diagonal agreement with an
intensity profile, "edge set connected on its endpoints"): one scout-defs pass; moving
`ae_cluster_eq_singleton_of_offDiagonal`/`ae_openGraph_le_of_offDiagonal` out of `Models/HierarchicalCutoff.lean`
into `Percolation/Bond`; the `unusedFintypeInType` clean-up; the fold's clean-up list; the tasks board mirror once
`task-board` merges.

## For ARCHITECT

- **Window (d) on the strict reading (round 1 of this series).** The launcher asked that, once its preconditions hold,
  only the migration brief be startable until claimed Lean work merges. Done so: (d) released, six unclaimed Lean
  briefs held (hier-cor12 among them), audits/wiki/tooling left open (ruling 11f). Lanes therefore take audits until
  (d) merges; reopening is a rename (steps in the window section). Overrule if you prefer the round-5 reading
  (disjoint proving open beside the migration), which the previous series used.
- **One batch per round** (launcher): `lrp-I56-gyration` (proof-only) finished during the round after the gate and is
  left for the next batch rather than gated a second time beside the kernel replay.
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

- **Pull request to `main` (ruling 13a):** open and merge https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  when you wish. Last commit that passed both the gate and the kernel replay: the baseline `4c72765`; the tip's last
  gated commit is `cfef666` (gate passed 16:27, kernel replay of `cfef666` running, result in the next STATUS).
  `main` is at `1df822a`.
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
