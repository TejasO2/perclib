# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 12:25 UTC, at the end of coordinator round 3 of the current series (fourteenth coordinator overall;
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
- **Round 3 (12:21-12:25): no merge, no gate.** The predecessor's STATUS commit `f67780f` landed at 12:20:55;
  the tree was clean and idle. Nothing was waiting, so the coordinator waited for a marker: one arrived at
  12:22 (`critic-proof-sections-a`, read-only critique, all three articles NOT PASS). It became revision brief
  `103-wiki-revise-proof-sections-a` plus `HOLD-audit-wiki-revise-proof-sections-a`. The tip is this STATUS
  commit on `f67780f` on the gated `6e85f59`; **next gate still `scripts/gate.sh 6e85f59`**. Kernel replay not
  run (prover briefs released and about to be claimed; never alongside a build; and no pull request can be
  opened anyway, see "For ARCHITECT"). GitHub: ToolSearch still finds no GitHub tool, `gh` token invalid;
  anonymous read at 12:23: no open pull requests, issue #1 only.
- **Round 2 (12:09-12:25): no merge, no gate.** Nothing finished was mergeable: every finished branch
  waits for an audit or a fix (see "Finished, not merged"). The tip is still the round-1 STATUS commit
  `0bd4b10` on the gated `6e85f59` (this round adds only a STATUS commit). **Next gate:
  `scripts/gate.sh 6e85f59`** on the first batch that merges anything. Kernel replay not run (provers
  were released this round and will be building; never alongside a build).
- **GitHub (round 2):** still no write tool: ToolSearch finds no GitHub MCP tool, `gh auth status` says
  the `GH_TOKEN` is invalid. Anonymous read at 12:12: **no open pull requests**; one open issue, #1
  (README; fixed on the integration branch at `882c3bf`). No pull request to `main` opened.
- **Round 1 (recovered round-10 merges):** a coordinator between 05:27 and 05:56 (call it round 10) merged seven
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

Round 3: 0 proved, 0 audited and merged (no merges). Round 2: **0 new assertions proved in Lean, 0 tagged statements audited and merged** (no merges). Lean
proving reopened this round (10 prover briefs released, see the migration section). Manifest unchanged
since `882c3bf`: **266 proved, 2 statement-only, 1,134 unformalised, of 1,402**. Frontier
(`docs/FRONTIER.md` at `882c3bf`): 300 ready, 816 blocked, 20 without recorded prerequisites. Round 1:
0 proved; 3 tagged statements audited and merged (FCU7, B5SL, JZG4; all wiki).

## Merged in round 1 (round 2 merged nothing)

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

- **`critic-proof-sections-a`** (done 12:22; `/home/user/reports/critic/proof-sections-a.md`): ruling 7 (iii) critic
  of the round-1 proof sections. NOT PASS for `branching-random-walk` (G12U placed before V7FQ, which it uses;
  48GR idea implies a single truncation gives the sharp bound, M-B1 PLAUSIBLE), `size-biased-laws` (FM8D idea's
  decoupling step wrong, M-S1 CONFIRMED as an error in the sketch, not the statement) and `marginal-ode` (pointer
  at l. 31 now wrong; structure). No tagged statement affected. Revision **`103-wiki-revise-proof-sections-a`**
  queued (one reviser, all three articles, no new lead because of the frozen-digest test), then
  `HOLD-audit-wiki-revise-proof-sections-a` (release with the branch commit when 103 is done), then a critic
  re-read (brief it after the audit). Coordinator's later decision: S-S1 (move FM8D, E22E, Q7E9 to
  `incipient-cluster-limits`); M-B2 (check Fitzner–van der Hofstad Thm 1.4 gives the x-space asymptotic) goes to
  the next source-fidelity audit of BSI3.

- **`work/wiki-proof-67W9`** (`38232d3`, done 12:09): full collapsed proof of 67W9 (θ>0 ⇒ L_qθ²≥1 for
  symmetric q on ℤ, after Duminil-Copin–Garban–Tassion arXiv:2011.04642v2 §2.4, adapted to general q),
  one `proofUses` row (F4CV, H0OC). The author reports a slip in DGT's bridge error term (not an upper
  bound; harmless) and stale "cited input" wording for 67W9 in NLDF, XP2Y and three record strings of the
  same article. Correctness audit **`091-audit-wiki-proof-67W9`** queued (diff and source only; it is
  asked to judge the DGT slip and give an erratum text if it agrees). On APPROVE: merge, wiki test, gate;
  then queue (one package, owns `integrated-susceptibility.md` + record) the NLDF/XP2Y/record rewording
  and, if the auditor confirms the slip, a provisional erratum for `dgt-long-range-2023`.
- **`work/fix-wiki-runaway-split-1`** (`8bc1cd6` on merge `e19b3a8`, done 12:15): audit changes 1-4,
  notes A/B and the critique applied; 65 tagged blocks byte-identical (author's check). Re-audit
  **`088-audit-wiki-runaway-split-1-r2`** released. On APPROVE merge it, then release
  `HOLD-wiki-original-marking` (ruling 11h) and queue runaway split step 2.
- **`work/fix-wiki-proof-F9EV`** (`c6f708b` on merge `cfb9f3d`, done 12:17): the six `(θ_++1)C`
  replacements. Mechanical re-audit **`083-audit-wiki-proof-F9EV-r2`** released. Merge on APPROVE.
- **`work/wiki-revise-regular-variation`** (`0f995ce`): `audit-wiki-revise-regular-variation` (fresh,
  binder tables for 3491, LTJ1, SLGY, PVM9: statements unchanged apart from the authorised M1/M2) APPROVE
  WITH CHANGE: C1 (`wiki/tests/lead.test.mjs`: the frozen-digest test must skip non-frozen articles;
  `npm test` fails without it), C2 (restore the integer-valued justification paragraph), C3 (one step of
  the oscillating non-example). **`100-fix-wiki-revise-regular-variation`** (one fixer, C1-C3 verbatim)
  queued, then `HOLD-audit-wiki-revise-regular-variation-r2` (mechanical). C4 (coordinator, after the
  merge): 13 of 30 rows of `wiki/sources/perclib-dfbc5b4-analysis-symmetry.md` linking
  `regular-variation.md#section-tail-interface` point to arguments the revision removed; queue a reading-map
  package to retarget them once the fix merges. Then a critic re-read and the §3 sketched-proof package.
- **Workflows and scanner:** `audit-fix-workflows-r3` (fresh, done 12:17): `work/fix-scanner-r3` APPROVE
  WITH CHANGE **GS4** and `work/fix-workflows-r3` APPROVE WITH CHANGE **AM4** (finding S2: a comment opener
  or character literal directly after a symbol desynchronises the scanner and the automerge classifier
  from Lean; an error-free pull request running `run_tac` IO would pass scanner, build and classifier and
  be auto-merged). **`101-fix-scanner-r4`** and **`102-fix-workflows-r4`** queued (disjoint files), then
  `HOLD-audit-fix-workflows-r4` (both branches). Merge order on APPROVE: `work/fix-scanner-r4`, then
  `work/fix-workflows-r4` (each contains r3, r2 and the originals), gate; the workflows must not reach
  `main` before AM4. Then `work/contrib-docs` and `work/task-board` (check them against the tip), mirror
  the queue into `tasks/` (ruling 9b), open the pages-deploy brief (ruling 12).
- **Model article** `work/fix-wiki-model-hier-two-point` (`352ac8a`): one change (`R_0=1` → `R_0=2`);
  **`094-fix-wiki-model-hier-two-point-r3`** queued (keep both tags.json entries), then
  `HOLD-audit-wiki-model-hier-two-point-r4` (release when its report says the change is committed). On
  APPROVE: merge `work/fix-wiki-model-hier-two-point-r3`, wiki test, gate, list the page for Tom
  (`/articles/hierarchical-two-point/`) with the reviser's §5 questions. Then queue: the J98J Lean tag on
  `HierarchicalTwoPointAveraged` (interface), critic reports R2/R4/R6 (precise V4QQ, YWTU; constants in
  655W, 7YNX; fresh audit), runaway split step 8.
- **`work/mig-def-bond`** (`b0b0c41`; migration (c) step 1): definitions `localConn`, `localCluster`
  (OG96), `IsCut`, `boundaryFlux` (6EIM), `boundarySusceptibility` with API. Interface audit
  **`085-audit-mig-def-bond`** queued (not yet claimed at 12:19). On APPROVE: merge, gate against
  `6e85f59`, push; then release the fold from the draft `084-scout-localconn-fold` writes into
  `/home/user/reports/drafts/` (claimed 12:18).
- `work/tooling-d35-header-blocks` (`c01bf41`): audit **`097-audit-tooling-d35-header-blocks`** queued;
  merge on APPROVE.
- `work/wiki-I421`'s Lean counterpart: the `@[tag "B5SL"]` restatement on
  `tendsto_div_of_tendsto_deriv_ratio` / `regularlyVarying_of_tendsto_deriv_ratio` (interface; not yet
  briefed; disjoint from the migrations, can be briefed next round).
- `work/nm-longrange` (`e4e9b59`; ZH13, R01V): **`095-fix-nm-longrange`** released this round.

## In flight (claims without a done marker at 12:23)

`audit-wiki-proof-F9EV-r2` (claimed 12:23), `scout-localconn-fold` (read-only; drafts the fold brief and its
audit into `/home/user/reports/drafts/`), `wiki-proof-2ZI0-tail` (owns the 2ZI0 proofs of
`triangle-condition.md`), `wiki-proof-WD31` (owns `critical-exponents.md`). Released prover briefs may be
claimed by the time you read this: check `claims/`. Worktrees kept (unmerged): automerge-workflow,
ci-workflow, contrib-docs, task-board, fix-gate-scanner, fix-workflows, fix-workflows-r2,
fix-workflows-r3, fix-scanner-r2, fix-scanner-r3, nm-longrange (used by 095), port-wiki-hier-thm11,
fix-port-wiki-hier-thm11, wiki-model-hier-two-point, fix-wiki-model-hier-two-point,
wiki-runaway-split-1, fix-wiki-runaway-split-1, wiki-proof-F9EV, fix-wiki-proof-F9EV,
wiki-revise-regular-variation, wiki-proof-67W9, mig-def-bond, tooling-d35-header-blocks, and those of
the in-flight claims. None removed this round (nothing merged).

## Migration window: (c), (d), (e) pending; **Lean proving reopened in round 2** on disjoint files

The round-1 plan said: if (c) has not merged by the end of round 2, reopen proving with the prover
briefs disjoint from `Bond/Basic.lean` and the fold's file list (ruling 11g: the window must close fast;
three of four lanes on proving). At 12:15 (c)'s interface audit was not even claimed, so (c) could not
merge this round; the coordinator reopened proving at once rather than at the end of the round.
**Released** (scout-hold-briefs-check order, its edits G3-G6 and per-brief rows applied, plus a note
listing the migration files the worker must not touch): 086 hier-restricted-susc (H7), 087 lrp-I55,
089 lrp-tauber-complete, 090 lrp-weak-kernels, 092 lrp-I526, 093 lrp-first-moment-b, 095 fix-nm-longrange,
096 nm-finite-coordinates, 098 nm-uniform-volume, 099 frontier-four-functions (in place of 220, which needs
(e)). Their owned files were checked (script) against the files of (c) (`Bond/Basic.lean`,
`Intensity/Defs.lean`, the D4b fold list of scout-defs), (d) (`HOLD-mig-law-generality` owned list) and
(e) (`HOLD-mig-model-norm` owned list): disjoint. The migrations therefore no longer need an empty queue:
each still runs alone **as a migration** (one at a time), beside prover work on disjoint files.
Sequence (unchanged):
1. **(c):** `085-audit-mig-def-bond` → merge `work/mig-def-bond`, gate → release the fold
   `mig-localconn-fold` from `084`'s draft (with its held audit). The fold must stay disjoint from
   claimed prover files: check the draft's list against `claims/` before release.
2. **(d):** `HOLD-mig-law-generality` after the fold merges; before release take items 1-3 (ZAIH, NEM5,
   6HJ9) out of `HOLD-200-nm-bond-core`, update the tip, write its held audit.
3. **(e):** `HOLD-mig-model-norm` (ModelNorm; re-audit PVA8, MQNP, LF50, 6YYS) after (d); release
   before 371 and 230.
**Still held:** 200 (after (d)); 210, 220, 230, 370, 371 (after (e)); 360 (after the fold); 330 after
086 merges, then 335; 362 after 095 merges, never with scout-defs D2; 361 not with scout-defs D1; 240
after its scout edit (QH7Q reuse of `prodBernoulli_forall_notMem`, `holley` first, path fix); 383 after
its edit (area lemmas, never H0OC); 381, 382, 384-389 ready (G1 done; apply the G3/G5 common edits and the
round-2 note as in 086-099; next releases to keep 8+ Lean briefs startable).

## Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the
directory. **Startable at 12:23 (19; mutually file-disjoint and disjoint from the claims):** 085 audit-mig-def-bond, 086 hier-restricted-susc, 087 lrp-I55, 088
audit-wiki-runaway-split-1-r2, 089 lrp-tauber-complete, 090 lrp-weak-kernels, 091 audit-wiki-proof-67W9,
092 lrp-I526, 093 lrp-first-moment-b, 094 fix-wiki-model-hier-two-point-r3, 095 fix-nm-longrange, 096
nm-finite-coordinates, 097 audit-tooling-d35-header-blocks, 098 nm-uniform-volume, 099
frontier-four-functions, 100 fix-wiki-revise-regular-variation, 101 fix-scanner-r4, 102 fix-workflows-r4, 103
wiki-revise-proof-sections-a (round 3; owns the three articles and their records, disjoint from all). Ten of them are Lean
prover briefs (086, 087, 089, 090, 092, 093, 095, 096, 098, 099).
All startable briefs were renumbered 083-102 this round so that Lean briefs are interleaved with the
critical-path audits (about three prover briefs per non-Lean brief; ruling 11g). Claimed this round:
`075`-`078`. **Held:** `HOLD-audit-wiki-revise-proof-sections-a`, `HOLD-audit-wiki-model-hier-two-point-r4`, `HOLD-audit-wiki-revise-regular-variation-r2`,
`HOLD-audit-fix-workflows-r4`, `HOLD-mig-law-generality`, `HOLD-mig-model-norm`, `HOLD-wiki-original-marking`,
`HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability`, and the 21 prover briefs listed in the migration
section. Interface prover packages (095, 096, 098; 086 is proof-only) get a fresh audit brief (diff and
source, binder table) when done.

Next packages to brief, in order: correctness audits of WD31 and 2ZI0-tail when done (diff and sources,
not the reports); the merges named above; the 67W9 follow-up wording package after its audit; the C4
reading-map package after the regular-variation fix merges; the B5SL Lean tag (interface, disjoint from
the migrations); the next critic pass (one critic at a time) of the new proof sections of
`integrated-susceptibility`, `finite-random-graphs`, `triangle-condition`, `adaptive-three-point`,
`critical-exponents` after their packages merge; the `unusedFintypeInType`/`unusedDecidableInType`
clean-up (44 declarations, ≥5 tagged; interface, after the migrations); the `op8f_asymptotics` rename
with a deprecated alias; runaway mathematical reports M1/M3/M4/M5 after the split moves their tags;
scout-defs D1, D2, D3a, D6; the tasks board mirror once `task-board` merges.

## For ARCHITECT

- **No GitHub write access in this session.** Rulings 10(1) and 11a ask for a pull request from
  `claude/zen-lovelace-rvlcw2` to `main` after each gated batch; the launch text says to use the GitHub
  MCP tools, but none is loaded (ToolSearch finds none) and `gh` reports the `GH_TOKEN` invalid. No pull
  request was opened, issue #1 was not answered. Anonymous reads work (no open pull requests). Please
  give the coordinator a working GitHub tool or token; until then `main` stays at `1df822a`.
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
