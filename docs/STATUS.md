# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 13:36 UTC, at the end of coordinator round 7 of the current series (eighteenth coordinator overall;
the previous file, round 9 of the earlier series, is at `874da60` and older rounds are in
`git log -p docs/STATUS.md`). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md), [COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md)
(D-34 to D-37) and `/home/user/reports/RULINGS.md` (rulings 1-12b; obey them; 10 and 11a authorise
pull requests to `main`). Container-local reports and briefs are copied for durability to
`lrp/docs/reports/` at each round's lrp commit (ruling 9i); `/home/user/reports/` stays the live copy.

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `e57e4b0`** (pushed;
  extract `.lake/gate/e57e4b0….json` saved); the tip is this STATUS commit (with `docs/FRONTIER.md`
  regenerated at `3da8955`) on top of it. **Next gate: `scripts/gate.sh e57e4b0`.**
- **Round 7 (13:15-13:36): four gated batches, all passed, all pushed.** Every gate: build `--wfail` OK
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

Round 7: **0 assertions proved in Lean, 0 tagged Lean statements audited** (three interface packages with 8
new tagged statements finished this round and wait for their audits: XLWI, YVJT, EZJ7, CPD6, XSA6, D1CH, DL0X,
XRSL; the fold's audit and R01V/ZH13's audit are running). Merged: one untagged proof-only Lean package (`lrp-I526`: Lemma I.5.26 of
*Critical long-range percolation I* in the 2KB9 generality, `PercLib/Analysis/SignedDrivenODE.lean`, the
paper's `|f| = O(h)` hypothesis removed), the model article `hierarchical-two-point` with J98J (ruling 8), the
regular-variation revision, runaway split step 1 (two new articles `multiplicative-coalescent`,
`hierarchical-block-coalescent`), and the `check_d35` header-block fix. Wiki-original results (ruling 11h):
`audit-wiki-original-runaway-a` judges J0DE, MFGT, OQV3 **CORRECT**; `-b` judges Q4PO, F7Q2, NC7F **CORRECT**
(conditional on MFGT/OQV3 as stated; NC7F has a drafting imprecision, below). Manifest at `e57e4b0`
(perclib script): **268 proved, 2 statement-only, 1,133 unformalised, of 1,403** (J98J added to the wiki).
Frontier (`docs/FRONTIER.md` at `3da8955`): 302 ready, 821 blocked, 12 without recorded prerequisites, 268
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
- Worktrees removed: lrp-I526, wiki-model-hier-two-point, fix-wiki-model-hier-two-point(-r3),
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

- **`work/mig-localconn-fold`** (head `6826749` on base `c1f840a`; done 13:17): items 1-6 complete, 111 `Iff.rfl`
  checks plus 9 tagged-statement and 8 rename checks pass by the author's account; census leaves form A only in
  `Basic.lean` (definition/API) and 2 proof sites in the unowned `Models/Hierarchical/Defs.lean`. Deviations: two
  proof-internal folds in P0, two sites fixed late in `6826749`. Audit **`100-audit-mig-localconn-fold`** released
  13:22 (head and base filled in), **claimed 13:20**. On APPROVE: `git merge-tree` against the tip and against
  `work/nm-longrange` (both touch `Models/`), pre-gate in a detached worktree if workers build, merge, gate, push;
  then step 3 of the window plan below. The author lists close-but-not-literal duplicates (`law_deleted_le_tau`,
  `tsum_law_deleted_le_chi`/`tsum_localConn_le_chi`, `setOf_deleted_of_mem`, `setOf_localConn_eq_exists`) and
  old-vocabulary names (`*_induce_conn*`, `*_induce_cluster`, `lintegral_encard_induce`) for a later clean-up.
- **`work/nm-uniform-volume`** (`69ec361` on `51fe8e5`; done 13:16): **interface**, tags XLWI (4 conjuncts, each
  an area lemma) and YVJT (no `htail`; `r ≥ 0` dropped as a strengthening) in new
  `Models/Tags/FiniteRangeExit.lean`; area code in new `Percolation/Bond/UniformVolumeTail.lean` and appended to
  `Models/FiniteRangeDecay.lean`. Fresh audit **`121-audit-nm-uniform-volume`** queued. On APPROVE merge, gate.
  Follow-up (proof-only, after merge): move the general two-parameter `PercLib.Probability` lemmas into
  `Probability/ExponentialMoments.lean` and make the one-parameter ones corollaries.
- **`work/frontier-four-functions`** (`5ceed9b` on `29a93e6`; done 13:18): **interface**, EZJ7 (Ahlswede–Daykin)
  as a direct instance of mathlib's `four_functions_theorem_univ`, new `Probability/Tags/FourFunctions.lean` (also
  holds an untagged corollary; the audit is asked whether it belongs in an area file). Audit
  **`122-audit-frontier-four-functions`** queued.
- **`work/nm-finite-coordinates`** (`a908569` on `51fe8e5`; done 13:18): **interface**, CPD6, XSA6, D1CH, DL0X,
  XRSL in new `Probability/Tags/FiniteCoordinates.lean`, append-only area lemmas in `Concentration`, `ZeroOne`,
  `FiniteEnergy/Insertion`, `RussoIntegral` (new imports, no cycle). Audit **`123-audit-nm-finite-coordinates`**
  queued (verdict per tag). Author's findings for later: `prodBernoulli_restrict_apply` is an area lemma inside
  `Probability/Tags/ProductModel.lean` (move to `Superposition.lean`); definition proposal for the set-level
  pivotal event (two spellings now in >3 statements; scout-defs list).
- **`work/nm-longrange`** (`0d4b908`): R01V, ZH13. Audit **`120-audit-nm-longrange-r2`** claimed 13:31. On APPROVE:
  merge, gate, then write and release `mig-iscut-fold` (scout-localconn-fold §6) and release `HOLD-362`, each
  checked for file overlap with the fold.
- **`work/fix-wiki-proof-WD31`** (merge `f12f07d`, fix `6afd5f9`; done 13:33): audit changes 1-5 and the COVERAGE
  line applied. Mechanical re-audit **`129-audit-wiki-proof-WD31-r2`** released. On APPROVE merge (contains
  `work/wiki-proof-WD31`), wiki test, gate.
- **`work/fix-wiki-proof-2ZI0-tail`** (merge `5c0a8f9`, fix `47faa52`; done 13:23): mechanical re-audit
  **`124-audit-wiki-proof-2ZI0-tail-r2`** released. On APPROVE merge, wiki test, gate.
- **`work/wiki-67W9-followup`** (`8803370`): `audit-wiki-67W9-followup` **APPROVE WITH CHANGE** (two edits to the
  new erratum entry: HTML equation numbers in the locator; corrected `resolution.summary`) plus follow-ups F1
  (`wiki/sources/one-dimensional-inverse-square.md`), F2 (`catalog.json` AN86 coverage note), optional record
  `relationship` values. Fix **`128-fix-wiki-67W9-followup`** queued (all of these), then
  `HOLD-audit-wiki-67W9-followup-r2` (mechanical; release with the fixer's `<merge>`/`<fix>`). On APPROVE merge
  `work/fix-wiki-67W9-followup`. The audit also flags a possible second DGT erratum in §3.4 (proof of Thm 2(ii),
  FK case, `|B_R|^2 e^{-β(K-2R)/q}`): a scout or erratum package later.
- **`work/wiki-revise-proof-sections-a`** (`024def9`): audit **`118`** claimed 13:28. On report record the reviser's
  four disagreements and mathematical reports (B-C2, M-S4, M-M1, M-B2) "For Tom", the G12U reason word; then a
  critic re-read. It owns `marginal-ode.md`: the I.5.5 and 2KB9 tag packages wait for it.
- **Workflows and scanner:** `work/fix-scanner-r4` (`0707396`), `work/fix-workflows-r4` (`0471b5e`); re-audit
  **`112-audit-fix-workflows-r4`** claimed 13:18. Merge order on APPROVE: `fix-scanner-r4`, then
  `fix-workflows-r4`, gate; the workflows must not reach `main` before AM4. Then `work/contrib-docs` and
  `work/task-board` (check against the tip), mirror the queue into `tasks/` (ruling 9b), open the pages-deploy
  brief (ruling 12).
- **Lemma I.5.5** (`CriticalDrivenODE.lean`, merged): PROVED AS STATED by `audit-lrp-I55-premises`. To count it: one
  interface package (wiki tagged block in `marginal-ode` beside B5SL, `Tags/` restatement, fresh audit), briefed
  with B5SL after 118's branch merges. Optional §4 strengthening later.
- **Wiki-original results** (ruling 11h): audits a/b CORRECT for J0DE, MFGT, OQV3, Q4PO, F7Q2, NC7F (not yet audited:
  Q7QG, V7MP, 9FO5). Notes for a wiki package after `125-wiki-original-marking` merges (same article): NC7F's
  interpolated-paths clause should say "deterministic grids N_n → ∞ at every node" (with a fixed grid the stated
  limit is false; this edits a tagged block's wording, so it is a precision fix with a fresh audit, listed "For
  Tom"); OQV3's A, Γ and estimates (18)-(22) are defined only inside MFGT's proof (presentational).
- `work/wiki-I421`'s Lean counterpart: the `@[tag "B5SL"]` restatement (interface; not yet briefed; touches
  `DrivenODE.lean`; brief it with I.5.5 as above).

## In flight (claims without a done marker at 13:35)

`audit-fix-workflows-r4` (13:18), `audit-mig-localconn-fold` (13:20), `audit-wiki-revise-proof-sections-a` (13:28),
`audit-nm-longrange-r2` (13:31). All four lanes are on audits; no Lean prover brief is claimed.
Worktrees kept (unmerged):
automerge-workflow, ci-workflow, contrib-docs, task-board, fix-gate-scanner, fix-workflows(-r2,-r3,-r4),
fix-scanner-r2/-r3/-r4, nm-longrange, port-wiki-hier-thm11, fix-port-wiki-hier-thm11, wiki-proof-2ZI0-tail,
fix-wiki-proof-2ZI0-tail, wiki-proof-WD31, fix-wiki-proof-WD31, wiki-revise-proof-sections-a, wiki-67W9-followup,
mig-localconn-fold, nm-finite-coordinates, nm-uniform-volume, frontier-four-functions (plus the auditors' scratch
worktrees, which they remove).

## Migration window (c): fold done, its audit running; proving open beside it

**Round 7:** `mig-localconn-fold` finished at 13:17; its audit was released at 13:22 and claimed. Proving stays open
(round-5 decision): no claimed prover brief overlaps the fold's owned files, and the eight startable prover briefs
381-389 are on new files. Steps still to come, in order:
1. On the fold audit's APPROVE: merge-tree check against the tip and `work/nm-longrange`, merge, gate, push.
2. **(d):** then open the window for `HOLD-mig-law-generality`: rename the unclaimed prover briefs `HOLD-…`, check
   `claims/` for races, release (d) alone (Lean-wise) once claimed Lean work has merged or is shown
   file-disjoint from (d); before release take items 1-3 (ZAIH, NEM5, 6HJ9) out of `HOLD-200-nm-bond-core`,
   update the tip in the brief, write its held audit. If (d) is not done within one round, reopen proving
   (ruling 11g).
3. **(e):** `HOLD-mig-model-norm` (ModelNorm; re-audit PVA8, MQNP, LF50, 6YYS) after (d); release before 371 and 230.
4. Reopen proving after each migration merges: `mig-iscut-fold` (after 095 merges), 360, 330 (tell the worker
   `HierarchicalEndpoint` statements are respelled with `localConn`), then 335; 362 after 095 merges, never with
   scout-defs D2; 361 not with scout-defs D1; 240 after its scout edit; 383 after its edit (area lemmas only,
   never H0OC); 200 after (d); 210, 220, 230, 370, 371 after (e).
The J98J Lean tag (hierarchical line, D-34 priority) touches fold-owned `Hierarchical*` files: brief it after
the fold merges.

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the directory.
**Startable at 13:35 (17; mutually file-disjoint and disjoint from the claims):** non-Lean (9): 121
audit-nm-uniform-volume, 122 audit-frontier-four-functions, 123 audit-nm-finite-coordinates (the three build
read-only in scratch worktrees), 124 audit-wiki-proof-2ZI0-tail-r2, 125 wiki-original-marking (owns the History
sections of the articles holding J0DE…9FO5), 126 wiki-rv-reading-map (owns
`wiki/sources/perclib-dfbc5b4-analysis-symmetry.md`), 127 critic-reread-regular-variation (read-only; the only
critic), 128 fix-wiki-67W9-followup (owns `wiki/errata/dgt-long-range-2023.json`,
`wiki/sources/one-dimensional-inverse-square.md`, one string of `wiki/src/content/catalog.json`, two values of
`wiki/records/integrated-susceptibility.json`), 129 audit-wiki-proof-WD31-r2. Lean (8): 381, 382, 384-389
(frontier assertions; new files). The audits sort first by design (they unblock merges).
**Held:** `HOLD-audit-wiki-67W9-followup-r2` (new), `HOLD-mig-law-generality`, `HOLD-mig-model-norm`,
`HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability`, and prover briefs 200, 210, 220, 230, 240, 330, 335, 360,
361, 362, 370, 371, 383 (conditions in the window section).
Released this round: `HOLD-audit-mig-localconn-fold` (as 100), `HOLD-audit-wiki-proof-2ZI0-tail-r2` (124),
`HOLD-wiki-original-marking` (125), `HOLD-audit-wiki-proof-WD31-r2` (129).

Next packages to brief, in order: merges named above as audits report; the J98J Lean tag after the fold; the I.5.5
+ B5SL tag package and the 2KB9 tag after 118's branch merges; the dedup of the two-parameter exponential-moment
lemmas after `nm-uniform-volume` merges; the NC7F precision fix after 125 merges; correctness audits of Q7QG, V7MP,
9FO5 (low priority); the next critic pass (one critic at a time) of the new proof sections of
`integrated-susceptibility`, `finite-random-graphs`, `triangle-condition`, `adaptive-three-point`,
`critical-exponents` once their packages merge; the `unusedFintypeInType`/`unusedDecidableInType` clean-up (after
the migrations); the `op8f_asymptotics` rename with a deprecated alias; runaway split step 2 and M1/M3/M4/M5;
scout-defs D1, D2, D3a, D6 (add the set-level pivotal event); the `DrivenODE.normalized_increment_of_driving_ode`
dedup; `exists_intervalIntegrable_tail_of_regularlyVarying` generalised through
`RegularlyVarying.exists_forall_abs_le` (lrp-I526 report); the tasks board mirror once `task-board` merges.

## For ARCHITECT

- **No GitHub write access in this session.** Rulings 10(1) and 11a ask for a pull request from
  `claude/zen-lovelace-rvlcw2` to `main` after each gated batch; the launch text says to use the GitHub
  MCP tools, but none is loaded (ToolSearch finds none) and `gh` reports the `GH_TOKEN` invalid. No pull
  request was opened, issue #1 was not answered. Anonymous reads work (no open pull requests). Please
  give the coordinator a working GitHub tool or token; until then `main` stays at `1df822a`. (Rechecked in
  round 4: still no tool; `main` now lacks everything up to `caa28bc`, six gated batches of this round included.
  Round 5: unchanged. Round 6: unchanged. Round 7: unchanged; `main` lacks everything up to `e57e4b0`, four
  more gated batches.)
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
- **The model article is ready for you to look at (ruling 8):** `/articles/hierarchical-two-point/` (merged on
  the integration branch at `c8e3d2c` after a correctness audit, a second critic read and two re-audits; it
  includes the new J98J statement). The reviser's open questions are in §5 of its report (copy in
  `lrp/docs/reports/`, `wiki-model-hier-two-point.md`); the restructuring of the other articles follows this
  pattern unless you object.
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
