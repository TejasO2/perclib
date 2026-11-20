# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 20 November 2026,
23:10 UTC, at the end of the first LEAD agent's session. A coordinator with no memory
resumes from this file, [COORDINATOR.md](COORDINATOR.md) (the procedure for one round),
[COORDINATION.md](COORDINATION.md) (worker rules), [DECISIONS.md](DECISIONS.md) (D-34,
D-35) and `/home/user/reports/RULINGS.md` (container-local rulings; obey them).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories; nothing else is ever pushed
  (ruling 5).
- **Last gate passed: `57593c8`** (`scripts/gate.sh 13a999b`, run by this LEAD after the
  other agent's concurrent gate finished): build, axiom audit of 5,289 constants (only
  `propext`, `Classical.choice`, `Quot.sound`), import closure of 302 modules, forbidden
  scan, classifier tests, extract, D-35 checks. It covers `lrp-I413-premises`,
  `attach-bond-core` and its imports, `COORDINATOR.md`, and the exemption of the 12
  bond-core Tags files written before D-35 (they lack module docstrings; `mig-headers`
  fixes them). Earlier green: `13a999b`, `ce8ccd5`, `a11470b`, `711c330`, `fc917ec`,
  `eb09ac5`. Local verification, not CI.
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

Manifest from the `57593c8` extract: **229 assertions proved**, 4 statement-only, 1,168
unformalised, of 1,401 (start of 20 November: 65 / 6 / 1,330). 233 distinct tags in
`PercLib/`. Every tag added on 20 November
was approved by a fresh auditor (link audits for analysis, longrange, bond-sub,
probability, bond-core; `audit-hier-stmt`), except the five D-16 proof tags PVA8, MQNP,
LF50, 6YYS, L82Q, which repeat the tag of an already audited statement. Preliminary
frontier from the wiki's authored `proof_uses`: 150 assertions at `13a999b` (recompute).

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
- `work/rowsum-def` (9561ac5): `rowSum` and `unitInterval.toENNReal` with API in
  `Bond/Basic.lean`. Interface: waits for `audit-rowsum-def` (claimed).
- `work/hier-runaway` (H4; done marker present): not yet read or merged.
- `work/nm-analysis` (tags K58A, 4K33): revised after the first audit; re-audit queued
  as `006-audit-nm-analysis-r2`.

## In flight (outside or inside the queue)

Started by ARCHITECT before the queue existed (reports appear as
`/home/user/reports/<id>.md`): `attach-models`, `hier-avg-to-pointwise`,
`lrp-chisquare`, `lrp-rv-levelinv`. Claimed from the queue: `audit-rowsum-def`.
Worktrees are `/home/user/wt/<id>`; claims in `/home/user/reports/claims/`.

## Queue (`/home/user/reports/queue/`)

Startable: `005-audit-rowsum-def` (claimed), `006-audit-nm-analysis-r2`,
`070-lrp-first-moment-a`, `080-nm-longrange`, `090-d35-binders`, `100-wiki-hier-thm11`
(private repository: tag for Theorem 1.1), `110-lrp-tauber-converse`, `120-lrp-cov-gap`,
`130-lrp-moment-conv`, `140-lrp-sb-mgf`.
Held: `HOLD-audit-nm-longrange` (start when `nm-longrange` is done),
`HOLD-mig-rowsum`, `HOLD-mig-headers`, `HOLD-mig-linters`.

**Migration window (D-35).** Open it when `rowsum-def` has merged and the work claimed
at that moment has finished and merged: stop queueing other briefs, rename
`HOLD-mig-rowsum` to `001-mig-rowsum`, gate and merge it; then `mig-headers`, gate; then
`mig-linters` if time; then refill the queue. Briefs queued before the window that
spell row sums are migrated afterwards by a small follow-up, not held.

Next packages to brief when slots free: hierarchical H5 `hier-endpoint` (after H4 merges;
needs H1, H2, H4), H7 (after H5, H6), H8 Theorem 1.1, H9 (`hier-map.md` §(c));
the tag for `HierarchicalTwoPointAveraged` after `wiki-hier-thm11`; D-33 packages from
`d33-map.md` dependency order (next: 3 after 2, 5 and 8 after 1, 10, 12 after 10-11,
19, 25, 26, 29-30 after first-moment-a); near-misses in the `link-*.md` reports;
salvage tier 2 (Q-211, Q-195, Q-194, restated for the `Seminorm` kernel API).

## For ARCHITECT

- Open under D-35: the long-range norm (structure versus type synonym), after migration 1.
- Two agents merged into the same checkout during this session's last round (both ran
  `gate.sh` concurrently; one was stopped). One coordinator at a time per checkout.
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
