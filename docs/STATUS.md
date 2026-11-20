# Status

Kept by LEAD under D-34. Last updated 20 November 2026, fourth LEAD resumption (D-35 folded in, batch 3 merged).
A new LEAD resumes from this file, [COORDINATION.md](COORDINATION.md) and D-34 in
[DECISIONS.md](DECISIONS.md).

## Gate

**Latest: green on `ce8ccd5`** (`scripts/gate.sh a11470b`): build, axiom audit of 5,186
constants, closure of 278 modules, forbidden scan (D-35 list), tests, extract, D-35 checks.
Earlier green: `a11470b` (D-35 tooling, `hier-stmt`), `711c330` (batch 3), `fc917ec`,
`eb09ac5`. Kernel replay last run on the baseline below; due before the next milestone.
Note: the proof-only classifier splits identifiers at non-ASCII letters (`hΦdef` reads as
`def`), so it can report a false "interface"; it never reports a false "proof-only".

**Progress (D-35 measure: assertions proved, tagged statements audited)** — manifest
built in the private repository from the `ce8ccd5` extract: **121 proved**, 2
statement-only, 1,278 unformalised (start of day: 65 / 6 / 1,330). 123 distinct tags in
`PercLib/`; every tag added today was approved by a fresh audit (link audits for
analysis, longrange, bond-sub; `audit-hier-stmt`) except the five proof tags of D-16
(PVA8, MQNP, LF50, 6YYS, L82Q), which repeat the tag of an already audited statement.

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

**Merged today** (all gated): `hygiene-info`; `hier-translate` (H3); `attach-analysis`,
`attach-longrange`, `attach-bond-sub` (tags); `hier-kernel` (H1), `hier-quantile-finite`
(H2), `hier-sibling` (H6, Lemma 2.8 of arXiv:2103.17013 — `sum_shell_tau_ge`);
`salvage-analysis` (LaplaceUniqueness, ChiSquareDeterminacy, RiccatiBootstrap);
`hier-stmt` (H0: `Prop` statements of Theorem 1.1, untagged, and W498, audited);
D-33 ports `lrp-tauber-laplace`, `lrp-rv-geninv`, `lrp-I413`. In lrp: the wiki draft,
`pub-scan`.

D-33 caveat: the second half of Lemma I.4.13 (`lemma_I_4_13_second`, `_from_one`) carries
premises the paper does not state (global measurability of `h`; local integrability on
`(1, r₀]`); nothing tags or reports it as the paper's lemma. Brief `lrp-I413-premises`
discharges or justifies them.

**Held**: `work/pub-move` (c442b2f), the public wiki. Mechanical gate met: LEAD's own
re-scan reproduces the author's counts (9 distinct word runs and 4 formulas, all classed
fine by `pub-audit`; only synthetic fixture emails and URLs; no private links, draft hash
or draft locators; second read of the 55 notes-sourced articles found no leftover
reference). Not merged or pushed: Tom is ruling on publishing results original to the
draft without attribution (pub-move report §4 item 1).

**Running**: `attach-models`, `attach-probability`, `attach-bond-core`; `nm-analysis`
(done, with its auditor).

**Briefs ready** (`/home/user/reports/briefs/`): provers `rowsum-def` (interface; start
now) with `audit-rowsum-def`; `hier-runaway` (H4), `hier-avg-to-pointwise` (H9 without
H0), `lrp-rv-levelinv`, `lrp-chisquare`, `lrp-first-moment-a`, `lrp-I413-premises`,
`nm-longrange` with `audit-nm-longrange`, `d35-binders`; migrations `mig-rowsum`,
`mig-headers`, `mig-linters` (window only).

**Migration window (D-35)**: opens when `attach-models`, `attach-probability`,
`attach-bond-core`, `nm-analysis` and `rowsum-def` have merged; no other Lean branch is
open during it. Order: `mig-rowsum`, gate; `mig-headers`, gate; `mig-linters`, gate (if
time). Then the prover briefs above restart. `d35-binders` and the provers should not be
started before the window, because the migrations touch most files.

**Queued** (hierarchical dependency order from `hier-map`): H5
`hier-endpoint` after H1, H2, H4; H7 after H5, H6; H8 Theorem 1.1 after H0, H3, H5–H7;
H9 W498 after H8. D-33 next: packages 2, 23 and 29 wait for `salvage-analysis` (Q-154 and
Q-149 overlap them), 25, 26, 19. Then salvage tier 2 (Q-211, Q-195, Q-194, restated for the
`Seminorm` kernel API), `attach-<area>` after each link audit, and `pub-move` after
`pub-audit`.

Concurrency: at most 4 provers building single modules; no full build or kernel
replay while they build. Merges are batched and gated by LEAD.

## For ARCHITECT

- Open under D-35: the long-range norm (structure versus type synonym), after migration 1.
- Wiki: Theorem 1.1 of arXiv:2103.17013 needs a wiki tag (next wiki brief); then
  `HierarchicalTwoPointAveraged` gets it, with its own audit.
- Coming up, LEAD's decision unless ARCHITECT objects: the salvage branches
Q-81 (Galton–Watson definitions) and Q-10 (uniqueness definitions) add new definitions;
LEAD will take them only with a fresh audit and only if no existing notion covers them.

## For Tom

- Publishing the wiki (`work/pub-move`): results original to the draft, published without
  attribution (asked by ARCHITECT).
- The 194 provisional errata entries in the wiki await his confirmation (D-30).
- Issue-52 reading of universal tightness (`k ≥ 1` where the source prints `k ≥ 0`, false at
  `k = 0`): still his ruling; the hierarchical programme uses only `k ≥ 1`.
- arXiv 2103.17013v1 Prop. 2.12(ii) states `E_{β_c}|K_n| ≥ L^{αn}` with constant 1; the
  flux argument gives the factor `(L^α-1)/(β_c C (1-L^{-d}))`. Already a provisional
  erratum; the Lean target keeps the factor.
- The wiki remark under W498 that radiality matters for the pointwise bound looks
  misleading (the wiki's own 7YNX argument does not use it); to be reworded when the
  article is next touched.
