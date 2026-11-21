# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 20 November 2026,
23:30 UTC, at the end of coordinator round 1 (the round after the first LEAD agent's session). A coordinator with no memory
resumes from this file, [COORDINATOR.md](COORDINATOR.md) (the procedure for one round),
[COORDINATION.md](COORDINATION.md) (worker rules), [DECISIONS.md](DECISIONS.md) (D-34,
D-35) and `/home/user/reports/RULINGS.md` (container-local rulings; obey them).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories; nothing else is ever pushed
  (ruling 5).
- **Last gate passed: `fa0dc2b`** (`scripts/gate.sh cf0733c`, round 1): build (3,905
  jobs), axiom audit of 5,525 constants (only `propext`, `Classical.choice`,
  `Quot.sound`), import closure of 312 modules, forbidden scan, classifier tests, extract,
  D-35 checks (no exemption left in `scripts/d35_exceptions.txt`; the 12 bond-core Tags
  files now carry module docstrings, so their temporary `legacy_headers.txt` entries were
  dropped). No saved extract for base `cf0733c`, so the classifier treated the batch as
  interface; the only interface change in it is `nm-analysis` (K58A, 4K33), approved by
  `audit-nm-analysis-r2`. Pushed: `origin/claude/zen-lovelace-rvlcw2` = `fa0dc2b`.
  Earlier green: `57593c8`, `13a999b`, `ce8ccd5`, `a11470b`. Local verification, not CI.
- Kernel replay (`scripts/kernel_replay.sh`) last passed on the baseline `4c72765` (249
  modules, 14 min, peak 9.7 GB at batch 12). Due before the next milestone report; run
  `scripts/kernel_replay.sh 6` when no build is running.

Commands (from `/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
scripts/gate.sh <previous-tip>   # build --wfail, AxiomAudit, closure, forbidden, tests,
                                 # extract (.lake/manifest-raw.json, saved .lake/gate/<sha>.json),
                                 # check_d35, proof-only/interface classification
scripts/kernel_replay.sh 6       # leanchecker in batches; never alongside a build
cd /home/user/lrp && python3 scripts/build_manifest.py /home/user/perclib/.lake/manifest-raw.json --output /tmp/manifest.json
```

The classifier's "INTERFACE" is a notice, not a failure: it must match audited interface
changes. It splits identifiers at non-ASCII letters (`hΦdef` reads as `def`), so it can
report a false interface, never a false proof-only.

## Progress (D-35 measure)

Manifest from the `fa0dc2b` extract (`build_manifest.py` in lrp): **231 assertions
proved**, 4 statement-only, 1,166 unformalised, of 1,401 (start of 20 November: 65 / 6 /
1,330; after the first LEAD session: 229 / 4 / 1,168). 235 distinct tags in `PercLib/`.
Tagged statements audited this round: 2 approved (K58A, 4K33 by `audit-nm-analysis-r2`),
2 reviewed on `work/nm-longrange` (ZH13 approved, R01V approve-with-change), 1 definition
package reviewed (`audit-rowsum-def`: approve with changes). Every merged tag has a fresh
audit (link audits; `audit-hier-stmt`; `audit-nm-analysis-r2`) except the five D-16 proof
tags PVA8, MQNP, LF50, 6YYS, L82Q.

## Merged on 20 November (gated)

Tooling: local gate scripts (`AxiomAudit.lean`, `check_forbidden.py`, `kernel_replay.sh`,
`gate.sh`, local `check_proof_pr.py`), D-35 checks (`check_d35.py` with the shrinking
exemption lists `scripts/legacy_headers.txt` and `scripts/d35_exceptions.txt`),
`docs/CITED_INPUTS.md` (empty: no `…Input` exists).
Lean: `hygiene-info`; hierarchical H0 `hier-stmt` (statements of Theorem 1.1, untagged,
and W498), H1 `hier-kernel`, H2 `hier-quantile-finite`, H3 `hier-translate`, H6
`hier-sibling` (Lemma 2.8 of arXiv:2103.17013, `sum_shell_tau_ge`, with the generic
`CrossEdge.lean`); salvage `LaplaceUniqueness`, `ChiSquareDeterminacy`,
`RiccatiBootstrap`; D-33 ports `lrp-tauber-laplace`, `lrp-rv-geninv`, `lrp-I413`,
`lrp-I413-premises`; tags `attach-analysis`, `attach-longrange`, `attach-bond-sub`,
`attach-probability`, `attach-bond-core`.
Round 1 (gated on `fa0dc2b`): `nm-analysis` (K58A, 4K33, audited), `hier-runaway` (H4:
Prop 2.2 for β < β_c, Cor 2.3 `β_c ≤ A/4`), `hier-avg-to-pointwise` (averaged bounds imply
pointwise bounds, the W498 step), D-33 ports `lrp-first-moment-a`, `lrp-rv-levelinv`,
`lrp-chisquare`, `lrp-tauber-converse`, and `d35-binders` (no declaration assumes the
tagged Props C5Q9/JGZB any more; `universalTightness_of_tightnessBK` replaced by three
`_of_bk` lemmas; tagged statements unchanged).
Private repository: the wiki draft of 20 November (`1fe07bc`), `pub-scan` (`5a2943b`).

Lemma I.4.13 (*Critical long-range percolation I*): the faithful form of the second half
is `IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_one`, with local integrability of `h`
on `(1, r]` as its one explicit premise; a compiled counterexample shows the premise does
not follow from the paper's hypotheses (listed for Tom). Nothing is tagged as the paper's
lemma.

## Finished, not merged

- `work/pub-move` (c442b2f): the public wiki. **Held by ruling 2** until Tom answers.
  LEAD's independent re-scan (`/home/user/reports/pub-move-lead-rescan.md`) reproduces
  the author's counts and finds nothing locating or quoting the draft. When Tom answers:
  regenerate with `/home/user/reports/pub-move-transform.py` from the current lrp wiki if
  the wiki moved, re-run the overlap scan (`/home/user/lrp/scripts/draft_overlap.py`)
  and the greps of the re-scan file, then merge and push. Irreversible.
- `work/rowsum-def` (now 3147f8b): `rowSum`, `unitInterval.toENNReal` and API.
  `audit-rowsum-def` approved with two changes; `fix-rowsum-def` applied them (report
  `/home/user/reports/fix-rowsum-def.md`). **Next round: check `git diff 9561ac5..3147f8b`
  against the audit's "Required changes" (docstring labels; `rowSum_fun_zero`), then merge
  on the gate.** Merging it is the precondition of the migration window.
- `work/nm-longrange` (e4e9b59; ZH13, R01V): audit approves ZH13 and asks for R01V in an
  ordered-pair form plus moving nine lemmas out of the Tags file. The coordinator adopted
  the audit's form (no erratum). Fix brief `HOLD-fix-nm-longrange` waits for
  `attach-models` to merge (both edit `Models/TranslationInvariant.lean`); then a fresh
  re-audit of R01V. Audit finding 3 proposes an `IsCut` definition (45 spelled-out sites):
  a future small interface package, after the migrations.
- `work/lrp-cov-gap` (4f4d4ce): D-33 port 28, proof-only per its report (one new file
  `Bond/ClusterCorrelation/CovarianceGap.lean`, no def/tag by grep). Finished after this
  round's batch: merge on the gate next round.
- `work/wiki-hier-thm11` in lrp (a795d41): new wiki tag **J98J** for Theorem 1.1. Items 1-3
  done; `npm run build` blocked by the W-1 frozen-article check (`migration-baseline.json`
  digests and the hard-coded count 65 in `wiki/tests/tags.test.mjs`). The worker left a
  patch `/home/user/reports/wiki-hier-thm11-baseline.patch`. Next round: review the patch
  (it is the "explicit review" the wiki README asks for), apply, build, merge into lrp's
  integration branch; then brief the J98J tag on `HierarchicalTwoPointAveraged`
  (interface, with audit).

## In flight (outside or inside the queue)

Claims without a done marker at 23:30: `hier-endpoint` (H5), `lrp-karamata-prim`,
`lrp-moment-conv`, `lrp-sb-mgf`; outside the queue: `attach-models` (worktree
`/home/user/wt/attach-models`, commit 3928d90 plus uncommitted work, no report yet).
Workers finish packages in minutes, so expect several done markers at the start of the next
round. Worktrees are `/home/user/wt/<id>`; claims in `/home/user/reports/claims/`.

## Queue (`/home/user/reports/queue/`)

Claimed briefs stay in the queue directory (never delete a claimed brief); a brief is
startable when it has no `HOLD-` prefix and no `claims/<id>`.
Startable at 23:30: `170-lrp-driven-ode` (D-33 package 5), `180-lrp-tauber-endpoints` (10),
`190-lrp-first-moment-b` (30), `200-nm-bond-core` (ZAIH, NEM5, 6HJ9, CKJQ),
`210-lrp-I41-mt` (25), `220-lrp-spatial-russo-a` (26), `230-lrp-levy-measures` (19),
`240-nm-probability` (KB49, W90W, QH7Q). Owned files are pairwise disjoint and disjoint
from claimed work.
Held: `HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability` (start when the target is
done), `HOLD-fix-nm-longrange` (after `attach-models` merges), `HOLD-mig-rowsum` (dot
notation corrected per the audit: `unitInterval.toENNReal (q e)`), `HOLD-mig-headers`,
`HOLD-mig-linters`.

**Migration window (D-35).** Open it when `rowsum-def` has merged and the work claimed
at that moment has finished and merged: stop queueing other briefs (prefix every
unclaimed startable brief with `HOLD-` so that no worker takes it), rename
`HOLD-mig-rowsum` to `001-mig-rowsum`, gate and merge it; then `mig-headers`, gate; then
`mig-linters` if time; then refill the queue. Briefs queued before the window that
spell row sums are migrated afterwards by a small follow-up, not held.

Next packages to brief when slots free: hierarchical H7 `hier-restricted-susc` (after H5
`hier-endpoint` merges; H6 is merged), then H8 Theorem 1.1, H9 (`hier-map.md` §(c); note
`hier-avg-to-pointwise` already did the averaged-to-pointwise step of H9); the J98J tag on
`HierarchicalTwoPointAveraged` after `wiki-hier-thm11` lands; D-33 packages (next: 8 after
5, 12 after 10, 13/14 after `lrp-sb-mgf`, 20 after 19, 27 after 26, 31/32 optional, 15
lowest); near-misses in the `link-*.md` reports;
salvage tier 2 (Q-211, Q-195, Q-194, restated for the `Seminorm` kernel API).

## For ARCHITECT

- Open under D-35: the long-range norm (structure versus type synonym), after migration 1.
- Two coordinators again overlapped at the start of round 1: the round-1 coordinator was
  started while the first LEAD was still writing its handoff (COORDINATOR.md existed,
  tree clean, no gate running, so the start test passed). No harm resulted (merges were
  disjoint), but the start test should also require that STATUS.md's tip equals
  `origin/claude/zen-lovelace-rvlcw2` and has been pushed, or the launcher should start a
  coordinator only after its predecessor has returned.
- Round 1 adopted, under its own authority, the audit's ordered-pair form for R01V (the
  `Sym2` form forces inversion-even kernels); object if a D-2 `Sym2` form with an erratum
  is preferred.
- Coming up, the coordinator's decision unless ARCHITECT objects: salvage branches Q-81
  (Galton–Watson definitions) and Q-10 (uniqueness definitions) add definitions; take
  them only with a fresh audit and if no existing notion covers them.

## For Tom

- Publishing the wiki (`work/pub-move`): results original to the draft, published without
  attribution (ruling 2).
- Lemma I.4.13, second half, of *Critical long-range percolation I* implicitly assumes
  local integrability of `h` on `(1, ∞)`; the lemma's integral from 1 is undefined
  otherwise (compiled counterexample `not_integrableOn_rpow_mul_indicator_sub_inv`).
- The 194 provisional errata entries in the wiki await confirmation (D-30).
- Universal tightness, issue-52 reading (`k ≥ 1` where the source prints `k ≥ 0`, false
  at `k = 0`); the hierarchical programme uses only `k ≥ 1`.
- arXiv:2103.17013v1 Prop. 2.12(ii) prints constant 1 where the flux argument gives
  `(L^α-1)/(β_c C (1-L^{-d}))` (provisional erratum; the Lean target keeps the factor).
- The wiki remark under W498 that radiality matters for the pointwise bound is misleading
  (queued for rewording in `wiki-hier-thm11`).

## Lessons

- **Worktrees:** `git worktree add /home/user/wt/<id> -b work/<id> claude/zen-lovelace-rvlcw2`,
  `ln -s /home/user/perclib/.lake/packages <wt>/.lake/packages`, and
  `cp -a /home/user/perclib/.lake/build <wt>/.lake/build` (469 MB) so the worker does
  not rebuild PercLib; never download or rebuild mathlib per worktree.
- **Memory:** 15 GB, no swap. Up to 5 single-module builders ran together with about
  14 GB free. `lake env leanchecker PercLib` in one process is killed for lack of memory;
  use `kernel_replay.sh` batches and never during builds. A full warm gate is 3-6 min;
  cold build 4.5 min.
- **Merges:** conflicts are only `PercLib.lean` import lines; keep both sides, pass `-m`
  to the conflict commit, then add the modules `check_import_closure.py` lists.
- **Workers** sometimes use their harness's commit trailer instead of the preamble's;
  accepted, not rewritten.
- **Headers:** ported files tend to say "pull request 488" and package ids in headers;
  the D-35 check rejects them in new files, so briefs must say "repository, branch,
  commit" instead.
- **Tags inside `to_additive`:** write `@[tag "XXXX", to_additive …]`; a separate
  `@[tag]` after `@[to_additive]` breaks the translation.
- **One coordinator per checkout**, and never two `gate.sh` runs at once.
- **Removing worktrees:** "branch is an ancestor of the tip" is true of a worker's branch
  before its first commit. Round 1 removed with `--force` the fresh worktrees of
  `hier-endpoint`, `lrp-moment-conv`, `lrp-sb-mgf` (claimed, not done) this way; the
  workers re-created them, but uncommitted work may have been lost — read those reports for
  a mention. Remove a worktree only if `done/<id>` exists and its branch is merged.
- **Speed:** workers finish a package in 3-15 minutes. Keep a dozen startable briefs and
  expect most of them claimed within a round.
