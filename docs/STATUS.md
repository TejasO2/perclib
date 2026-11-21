# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 12:10 UTC, at the end of coordinator round 1 of the current series (twelfth coordinator overall;
the previous file, round 9 of the earlier series, is at `874da60` and older rounds are in
`git log -p docs/STATUS.md`). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md), [COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md)
(D-34 to D-37) and `/home/user/reports/RULINGS.md` (rulings 1-12b; obey them; 10 and 11a authorise
pull requests to `main`). Container-local reports and briefs are copied for durability to
`lrp/docs/reports/` at each round's lrp commit (ruling 9i); `/home/user/reports/` stays the live copy.

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `6e85f59`** (pushed;
  extract `.lake/gate/6e85f59….json` saved); the tip is this STATUS commit on top of it. **Next gate:
  `scripts/gate.sh 6e85f59`.** Last gated commit with Lean changes: `882c3bf` (mig-linters).
- **Recovered this round:** a coordinator between 05:27 and 05:56 (call it round 10) merged seven
  branches and pushed only up to `9c023a7`, then stopped without a gate on its last two merges and
  without updating this file. Its merges, all checked here against the audits on file:
  `wiki-errata-bookkeeping-b` (`9cbdb37`), `wiki-fcu7` (`51af24f`, `audit-wiki-fcu7-r2` APPROVE),
  `tooling-manifest-setdefs` (`43ed13b`), FRONTIER at `43ed13b` (`ab1279b`), `fix-wiki-I421`
  (`8468326`, B5SL, `audit-wiki-I421-r2` APPROVE), `wiki-errata-hypercube-version` (`9c023a7`),
  **`mig-linters`** (`05d012c`, D-35 migration 2) and `fix-wiki-proofs-susc` (`4a20cf5`,
  `audit-wiki-proofs-susc-r2` APPROVE with binder table). Gates of round 10 (extracts saved):
  `9cbdb37`, `43ed13b`, `9c023a7`.
- **Gate A (this round):** merged `work/fix-wiki-proofs-misc` (`4b5b504`) and
  `work/docs-readme-status` (`882c3bf`) on `4a20cf5`; `scripts/gate.sh 9c023a7` on **`882c3bf`**:
  build 3,922 jobs, axiom audit **5,990** constants (only `propext`, `Classical.choice`,
  `Quot.sound`), closure 329 modules, forbidden scan 329 files, tests, extract, "D-35 checks passed",
  "INTERFACE change against 9c023a7: tokens in `PercLib/Analysis/GoodScales.lean`: ['tag']" (the known
  false positive, word "tags" in a comment), "== gate passed on 882c3bf". **mig-linters check:** the
  extracts `.lake/gate/9c023a7….json` and `.lake/gate/882c3bf….json` were compared: no public
  declaration added or removed, no `type`/`statement_expr` change of any public declaration, no tagged
  statement change; the +36 constants are private `_simp_*`/`_proof_*` auxiliaries of `simp only`
  rewrites (38 new, 2 gone); 3,335 `line` changes; the three theorems whose `hπ` became an explicit
  binder have identical types. Pushed `9c023a7..882c3bf`.
- **Gate B:** merged `work/wiki-catalogue-entries` (`5a24f17`) and `work/wiki-sharpness-records`
  (`6d0833f`) after the FRONTIER commit `d1bd1e1`; wiki `npm test` 100/100; `scripts/gate.sh 882c3bf`
  on **`6d0833f`**: same counts, "PROOF-ONLY change against 882c3bf: 0 Lean file(s), no compiled
  interface change", "== gate passed on 6d0833f". Pushed `882c3bf..6d0833f`.
- **Gate C:** merged `work/fix-wiki-proofs-brw-r2` (`7e7b409`); wiki `npm test` 100/100;
  `scripts/gate.sh 6d0833f` on `7e7b409`: same counts, "PROOF-ONLY change against 6d0833f: 0 Lean
  file(s)", "== gate passed on 7e7b409". Pushed `6d0833f..7e7b409`.
- **Gate D:** merged `work/wiki-proof-2ZI0-chi` (`a33c223`) and `work/wiki-marginal-ode-context`
  (`6e85f59`); wiki `npm test` 100/100; merged article and record files byte-identical to the audited
  commits; `scripts/gate.sh 7e7b409` on **`6e85f59`**: same counts, "PROOF-ONLY change against 7e7b409: 0
  Lean file(s), no compiled interface change", "== gate passed on 6e85f59". Pushed `7e7b409..6e85f59`.
  (The kernel killed a process for lack of memory during this gate, probably in the `mig-def-bond`
  worker's build running at the same time; the gate itself completed and passed.)
- Kernel replay: **not run** this round (the migration worker `mig-def-bond` is building in its
  worktree; 15 GB, never alongside a build). Last replay passed on the baseline `4c72765`. Run
  `scripts/kernel_replay.sh 6` when no Lean build runs; it is required before the first pull request to
  `main` (ruling 10(1)).
- **`main` (`1df822a`) lacks every commit since**; no pull request opened: this session has no GitHub
  write access (no GitHub MCP tools are loaded and the `gh` token is invalid; see "For ARCHITECT").
  Anonymous API read at 11:30: **no open pull requests**; one open issue, **#1** ("Update README to
  describe the published percolation library", by the owner): addressed by the `docs-readme-status`
  merge (`882c3bf`), not answered on GitHub (no write access). It can be closed once `main` has the merge.

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

Run a gate that rebuilds many modules in the background (`nohup scripts/gate.sh … > log &`) and poll
`pgrep -f scripts/gate.sh`; a full rebuild after a many-file Lean merge took 20 min (gate A), a 0-Lean
gate 4-6 min. The base passed to `gate.sh` must have a saved extract in `.lake/gate/` (STATUS- or
FRONTIER-only commits have none: pass their gated parent). After each gate
`git checkout scripts/__pycache__/`; after `frontier.py` delete `scripts/__pycache__/frontier.*.pyc`.

## Progress (D-35 measure)

This round (with the unrecorded round-10 merges): **0 new assertions proved in Lean**; **3 tagged
statements audited and merged** (FCU7 changed statement, B5SL new tag, JZG4 statement with binder
table; all wiki), plus statement-preservation audits of G12U and the misc tags (unchanged). Manifest at
`882c3bf`: **266 proved, 2 statement-only, 1,134 unformalised, of 1,402** (the +3 proved are T90E, 8FLS,
OQN6 reclassified as definitions by `tooling-manifest-setdefs`, not new proofs; +1 assertion is B5SL).
Frontier (`docs/FRONTIER.md` at `882c3bf`): **300 ready, 816 blocked, 20 without recorded
prerequisites**. No Lean proof has merged since round 4 of the earlier series: the migration window
(below) is the reason, and ruling 11g asks it to close fast.

## Merged this round

- `fix-wiki-proofs-misc` (`4b5b504`): idea paragraphs for JM5A, R9NU (`adaptive-three-point`), WD31
  (`critical-exponents`), T9KC (`infinite-cluster-uniqueness`) with the audit's replacements, and the new
  T9KC scope paragraph (T9KC as worded is true: coset argument when some p(u)=1, Grimmett–Keane–Marstrand
  1984 when Σp=∞, Gandolfi–Keane–Newman 1992 otherwise). `audit-wiki-proofs-misc-r2` APPROVE (fresh; did
  not read `authors/`). Statements byte-identical.
- `docs-readme-status` (`882c3bf`): README's stale last sentence replaced by a factual description
  (countable BK, the six areas, pointers to `PercLib.lean` and `docs/FRONTIER.md`); answers issue #1.
- FRONTIER regenerated at `882c3bf` (`d1bd1e1`).
- `wiki-catalogue-entries` (`5a24f17`): catalogue entries for Hara–Slade 1990 and Gandolfi–Keane–Newman
  1992, journal data for Bass–Levin; Hara 2008 already existed as `hara-nearest-neighbour-2008` (the
  author did not duplicate it). Catalogue only, merged on the gate.
- `wiki-sharpness-records` (`6d0833f`): `dt-sharpness-zd` in `sharpness` `sourceIds`, a `proofUses` row
  for 6EIM, the `sharpness` metadata digest. Records only, merged on the gate.
- `fix-wiki-proofs-brw-r2` (`7e7b409`; contains `wiki-proofs-brw` and `fix-wiki-proofs-brw`): full
  proof of G12U from V7FQ, idea paragraphs for BSI3, 48GR, FM8D, reading-map wording. Audits
  `audit-wiki-proofs-brw` (every step), `-r2`, `-r3` (mechanical) APPROVE; G12U statement unchanged.
  Ruling 7 (iii): its critic pass is queued (`077-critic-proof-sections-a`).
- `wiki-proof-2ZI0-chi` (`a33c223`): 2ZI0's first estimate, χ(p) ≍ (p_c−p)^{-1} under ∇_{p_c}<∞, with
  explicit constants; the other two estimates "proof wanted" (queued: `076-wiki-proof-2ZI0-tail`).
  `audit-wiki-proof-2ZI0-chi` (fresh) APPROVE; tagged block unchanged.
- `wiki-marginal-ode-context` (`6e85f59`): `marginal-ode` context sentence (which results the
  continuity and limit assumptions belong to) and the B5SL `occursIn` note.
  `audit-wiki-marginal-ode-context` (fresh) APPROVE.

## Finished, not merged (each waits for the item named)

- **Model article** `work/fix-wiki-model-hier-two-point` (`352ac8a`; contains the model article
  `792ca22` and J98J `4b8ee89`): the r2 audit asks one change (`R_0=1` → `R_0=2`). The fixer
  `fix-wiki-model-hier-two-point-r2` **stopped at setup** on a `wiki/tags.json` conflict (J98J and B5SL
  allocation entries) and changed nothing; its done marker was taken for completion, and the mechanical
  audit `audit-wiki-model-hier-two-point-r3` correctly REJECTED the unchanged branch. Re-briefed as
  **`079-fix-wiki-model-hier-two-point-r3`** (keep both tags.json entries), then
  `HOLD-audit-wiki-model-hier-two-point-r4` (release when its report says the change is committed).
  On APPROVE: merge `work/fix-wiki-model-hier-two-point-r3`, wiki test, gate, push, list the page for Tom (`/articles/
  hierarchical-two-point/`) with the reviser's §5 questions. Then queue: the J98J Lean tag on
  `HierarchicalTwoPointAveraged` (interface, after the window), critic reports R2/R4/R6 (precise V4QQ,
  YWTU; constants in 655W, 7YNX; fresh audit), runaway split step 8.
- `work/wiki-runaway-split-1` (`93ca706`): `audit-wiki-runaway-split-1` APPROVE WITH CHANGE (four
  wording/context changes, notes A, B); the critic of the two new articles (`critic-coalescent-articles`)
  is done (NOT PASS; mathematics correct). **`073-fix-wiki-runaway-split-1`** (one reviser applies audit
  and critique) is claimed; then `HOLD-audit-wiki-runaway-split-1-r2`; on APPROVE merge
  `work/fix-wiki-runaway-split-1`, then release `HOLD-wiki-original-marking` (ruling 11h) and split step 2.


- `work/wiki-proof-F9EV` (`4cd5987`): full proof of F9EV (two-sided tightness of the ordered largest
  components on the n^{2/3} scale) from `critical-random-graph-clusters`; `audit-wiki-proof-F9EV`
  (fresh) APPROVE WITH CHANGE (notation `C(θ_++1)` → `(θ_++1)C`, six places): `075-fix-wiki-proof-F9EV`
  queued, then `HOLD-audit-wiki-proof-F9EV-r2` (mechanical). Merge `work/fix-wiki-proof-F9EV` on APPROVE.
- `work/wiki-revise-regular-variation` (`0f995ce`, done 11:59): restructured from the critique with the
  two authorised tagged edits (M1: SLGY/LTJ1 name X and M_X; M2: 3491 on a half-line); audit
  `074-audit-wiki-revise-regular-variation` queued (binder table). On APPROVE: merge, then a critic
  re-read and the §3 sketched-proof package.
- **`work/mig-def-bond`** (`b0b0c41`, done 12:02; migration (c) step 1): `localConn`, `localCluster`
  (OG96), `IsCut`, `boundaryFlux` (6EIM), `boundarySusceptibility` with API, appended to
  `Bond/Basic.lean` and `Intensity/Defs.lean`; the author's gate in the worktree passed (6,045
  constants; not re-run by the coordinator). Interface: **`080-audit-mig-def-bond`** queued. On APPROVE:
  merge, gate against `6e85f59`, push; then release the fold (draft from `078-scout-localconn-fold`).
- `work/tooling-d35-header-blocks` (`c01bf41`, done 12:04): `header_text` reads every comment block
  before `module` (nesting-aware), 8 tests, tree still passes. Gate script:
  `081-audit-tooling-d35-header-blocks` queued; merge on APPROVE.
- Workflows and scanner: `work/fix-scanner-r3` (GS3, done 05:56) and `work/fix-workflows-r3` (AM2, AM3,
  done 11:32): third/fourth audit **`068-audit-fix-workflows-r3`** queued. On APPROVE merge
  `work/fix-scanner-r3` then `work/fix-workflows-r3` (they contain r2 and the originals), gate, then
  `work/contrib-docs` and `work/task-board` (check them against the tip for references to files not yet
  present), then mirror the queue into `tasks/` (ruling 9b) and open the pages-deploy brief (ruling 12).
  A fresh auditor must review the workflows before they reach `main` (ruling 10(2)).
- `work/nm-longrange` (e4e9b59; ZH13, R01V): `HOLD-fix-nm-longrange` after the window.
- `work/wiki-I421`'s Lean counterpart: the `@[tag "B5SL"]` restatement on
  `tendsto_div_of_tendsto_deriv_ratio` / `regularlyVarying_of_tendsto_deriv_ratio` (interface, after the
  window; not yet briefed).
- Read-only results consumed this round: `critic-regular-variation` (NOT PASS → `062` revision, held
  audit; §3 sketched proofs and M3/M4 later), `scout-hold-briefs-check` (edits and release order for the
  31 held prover briefs, `/home/user/reports/scout-hold-briefs-check.md`; edit G1 applied this round:
  author reports go to `authors/`; edits G3-G6 and the per-brief rows still to apply at release),
  `scout-law-generality` (drafts → `HOLD-mig-law-generality`, `HOLD-mig-model-norm`).

## In flight (claims without a done marker at 12:07)

`audit-fix-workflows-r3` (read-only), `fix-wiki-runaway-split-1` (owns the three runaway/coalescent
articles, their records, two rows of a reading map, their baseline entries), `wiki-proof-67W9` (owns
`integrated-susceptibility.md`), `wiki-proof-WD31` (owns `critical-exponents.md`). No Lean work is
claimed (mig-def-bond is done and awaits its audit). Worktrees kept (unmerged): automerge-workflow, ci-workflow, contrib-docs, task-board,
fix-gate-scanner, fix-workflows, fix-workflows-r2, fix-workflows-r3, fix-scanner-r2, fix-scanner-r3,
nm-longrange, port-wiki-hier-thm11, fix-port-wiki-hier-thm11, wiki-model-hier-two-point,
fix-wiki-model-hier-two-point, wiki-runaway-split-1, wiki-proof-F9EV, wiki-revise-regular-variation,
mig-def-bond, tooling-d35-header-blocks, and those of the in-flight claims. Removed this round:
docs-readme-status, fix-wiki-proofs-misc, wiki-proofs-misc, fix-wiki-proofs-susc, wiki-proofs-susc,
mig-linters, wiki-catalogue-entries, wiki-sharpness-records, fix-wiki-proofs-brw-r2, fix-wiki-proofs-brw,
wiki-proofs-brw, wiki-proof-2ZI0-chi, wiki-marginal-ode-context, fix-wiki-model-hier-two-point-r2
(abandoned, no commits).

## Migration window: OPEN (second window, rulings 11c/11g: migrations (c), (d), (e) one after another)

Migration 2 (`mig-linters`) is merged and gated (`882c3bf`); D-35's three migrations are complete
(`mig-rowsum`, `mig-headers`, `mig-linters`). Ruling 11 adds three more, run in one window, each at most
one round; if one stalls, reopen proving and retry later (11g). All prover briefs keep `HOLD-`;
non-Lean briefs stay startable (reading accepted in 11f). Sequence:
1. **(c) bond interface:** `000-mig-def-bond` released at `882c3bf`, **done 12:02**, audit `080` queued (definitions
   `localConn`, `localCluster` (OG96), `IsCut`, `boundaryFlux` (6EIM) in `Bond/Basic.lean`,
   `boundarySusceptibility` in `Intensity/Defs.lean`; append only). Merge on
   APPROVE of `080` (fresh, binder table for OG96 and 6EIM), gate. Then release the fold
   **`mig-localconn-fold`** (scout-defs D4b, ~30 files, re-audit of 19 tags; `078-scout-localconn-fold`
   writes the brief and its audit into `/home/user/reports/drafts/`) as the only Lean brief, with its
   held audit.
2. **(d) law generality:** `HOLD-mig-law-generality` (draft from `scout-law-generality`, written at
   `882c3bf`; `connProb μ x y := μ (conn x y)` in `Bond/Basic.lean`, `@[simp] connProb_law`). Before
   release: take items 1-3 (ZAIH, NEM5, 6HJ9) out of `HOLD-200-nm-bond-core` (conflict), update the tip,
   write its held audit.
3. **(e) long-range norm:** `HOLD-mig-model-norm` (`ModelNorm E` extending `Seminorm ℝ E`, 5 files +
   `Analysis/ModelNorm/Defs.lean`; re-audit PVA8, MQNP, LF50, 6YYS). Release before 371 and 230.
4. **Close the window:** apply `scout-hold-briefs-check` edits G3-G6 and the per-brief rows, drop
   `HOLD-` in its order: 320 (H7), 340, 350, 355, 345, 190, 220 (only after (e); else 380),
   fix-nm-longrange, 363, 364, 381, 385; then 380, 384, 386, 389, 382, 383, 387, 388; 330 after 320
   merges, then 335; 240 after its edit; 362 after fix-nm-longrange; 361 not with scout-defs D1; 360
   after D4b; 210, 230, 370, 371 after (e); 200 after (d). Keep 8+ Lean briefs startable from then on and
   three of four lanes on proving (11g).
If (c) has not merged by the end of the next round, ruling 11g says reopen proving: release the
prover briefs whose files are disjoint from `Bond/Basic.lean` and from the fold's file list.

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the
directory. **Startable at 12:07 (8, all non-Lean, mutually file-disjoint and disjoint from the claims;
several own one entry each of `wiki/migration-baseline.json`, accepted: merge one at a time):**
`074-audit-wiki-revise-regular-variation`, `075-fix-wiki-proof-F9EV` (owns the `finite-random-graphs.md`
proof block), `076-wiki-proof-2ZI0-tail` (owns the `triangle-condition.md` 2ZI0 proofs),
`077-critic-proof-sections-a` (read-only: G12U section of `branching-random-walk`, B5SL section of
`marginal-ode`), `078-scout-localconn-fold` (read-only; drafts the fold), `079-fix-wiki-model-hier-two-
point-r3` (owns `hierarchical-two-point.md` and the tags.json resolution), `080-audit-mig-def-bond`,
`081-audit-tooling-d35-header-blocks`. Claimed this round: `000`, `054`-`073`. Held:
`HOLD-audit-wiki-model-hier-two-point-r4`, `HOLD-audit-wiki-proof-F9EV-r2`,
`HOLD-audit-wiki-runaway-split-1-r2`, `HOLD-mig-law-generality`, `HOLD-mig-model-norm`,
`HOLD-wiki-original-marking`, `HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability`,
`HOLD-fix-nm-longrange`, and the 30 Lean prover briefs 190-389 (window; their author-report paths were
corrected to `authors/` this round, scout edit G1).

Next packages to brief, in order: correctness audits of the WD31, 67W9 and 2ZI0-tail proofs when done
(diff and sources, not the reports); merges named above; the next critic pass (one critic at a time) of
the new proof sections of `integrated-susceptibility`, `finite-random-graphs`, `triangle-condition`,
`adaptive-three-point`, `critical-exponents` after their packages merge; the
`unusedFintypeInType`/`unusedDecidableInType` clean-up (44 declarations, ≥5 tagged; interface, after
the window, mig-linters report §3b); the `op8f_asymptotics` rename with a deprecated alias (after the
window); runaway mathematical reports M1/M3/M4/M5 after the split moves their tags; scout-defs D1, D2,
D3a, D6; tasks board mirror once `task-board` merges.

## For ARCHITECT

- **No GitHub write access in this session.** Rulings 10(1) and 11a ask for a pull request from
  `claude/zen-lovelace-rvlcw2` to `main` after each gated batch; the launch text says to use the GitHub
  MCP tools, but none is loaded (ToolSearch finds none) and `gh` reports the `GH_TOKEN` invalid. No pull
  request was opened, issue #1 was not answered. Anonymous reads work (no open pull requests). Please
  give the coordinator a working GitHub tool or token; until then `main` stays at `1df822a`.
- **Unrecorded predecessor.** A coordinator merged eight branches (05:33-05:56) without gating its last
  two merges or writing STATUS (it seems to have been cut off). Recovered and gated this round. The
  launcher should not start a coordinator while a predecessor may still be running, and a coordinator
  should commit STATUS after each gated batch, not only at the end.
- **mig-linters left three linters off** (`lakefile.toml`): `style.header` (six files carry third-party
  notices; rewriting them into mathlib's `Copyright (c) … All rights reserved.` form means asserting a
  holder: a licence-notice question, see "For Tom"), `unusedFintypeInType` and `unusedDecidableInType`
  (removing 44 unused instance binders changes statements, ≥5 tagged: an interface package after the
  window, coordinator's call unless you object).
- Window reading unchanged (non-Lean briefs startable during a migration; only the migration is
  startable Lean work). The task text for this round said "leave only the migration brief startable";
  the coordinator kept the 11f reading.

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
  a second critic read and a re-audit that asked for one constant (`R_0=2`); that fix is done and its
  mechanical re-audit (`072`) is queued. On approval it merges and the page to look at is
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
