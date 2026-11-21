# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026,
05:00 UTC, at the end of coordinator round 5 (seventh coordinator; one gated batch). A coordinator with no
memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) (the procedure for one
round), [COORDINATION.md](COORDINATION.md) (worker rules), [DECISIONS.md](DECISIONS.md)
(D-34, D-35, D-36, D-37) and `/home/user/reports/RULINGS.md` (container-local rulings 1-10;
obey them). Container-local reports, briefs and rulings are also committed (copies, for
durability, ruling 9i) in the private repository under `lrp/docs/reports/` at the round's
lrp commit; `/home/user/reports/` stays the live copy.
## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. Pushed:
  `origin/claude/zen-lovelace-rvlcw2` = the commit of this STATUS file. Last gated commit
  **`2957b5a`** (merge of `work/mig-headers`, D-35 migration 3); after it only this STATUS commit.
  lrp: the round-5 commit refreshing `docs/reports/` (copies of the container reports; `lrp/wiki`
  stays frozen, ruling 6d).
- **Round 5 gate:** `scripts/gate.sh d71f8ce` on `2957b5a`: build 3,922 jobs (266 modules rebuilt,
  about 12 min), axiom audit 5,954 constants (only `propext`, `Classical.choice`, `Quot.sound`),
  closure 329 modules, forbidden scan, tests, extract, "D-35 checks passed" with
  `scripts/legacy_headers.txt` empty; "== gate passed on 2957b5a". The classifier printed
  "INTERFACE change against d71f8ce: tokens in `PercLib/Analysis/GoodScales.lean`: ['tag']": a
  false positive (the word "tags" in a rewrapped header comment). The coordinator compared the
  saved extracts `.lake/gate/d71f8ce….json` and `.lake/gate/2957b5a….json`: same 5,954
  declarations, the only differing field is `line` (2,035 declarations moved); no statement
  changed. Manifest rebuilt: counts unchanged. Pushed `7a45d94..2957b5a`.
- **Round 4 gate:** `scripts/gate.sh 18c879d` on `d71f8ce`: build 3,922 jobs, axiom audit 5,954
  constants (only `propext`, `Classical.choice`, `Quot.sound`), closure 329 modules, forbidden scan,
  tests, extract, D-35 checks; "PROOF-ONLY change against 18c879d1842b: 0 Lean file(s)"; "== gate
  passed on d71f8ce". Wiki on the merged tree: `npm test` 100/100 (92 + 8 new lead tests). Manifest
  rebuilt from this extract (counts unchanged). Pushed `efd7dce..d71f8ce`.
- **Gates passed in round 3** (each `scripts/gate.sh <previous>`: build 3,922 jobs, axiom audit
  of 5,954 constants with only `propext`, `Classical.choice`, `Quot.sound`, import closure of
  329 modules, forbidden scan, classifier tests, extract, D-35 checks):
  `fdc0542` (wiki-style; PROOF-ONLY, 0 Lean files), `029e7ac` (wiki-proof-uses-a; 0 Lean),
  **`9d06661`** (mig-rowsum + wiki-generator; "INTERFACE change against 029e7ac: tokens in
  `Models/LongRange/Tags/SizeBiasedLaws.lean`", which is the audited migration: 18 respelled
  tags approved by `audit-mig-rowsum`, C4E9 proof only), `202e752` (wiki-math-fixes; 0 Lean),
  `18c879d` (wiki-proof-uses-b; 0 Lean). Wiki on the merged trees: `npm run build` (92/92
  tests, 142 articles, all links and mathematics validated) at `9d06661`; `npm test` 92/92 at
  `202e752` and `18c879d` (node_modules symlinked from `/home/user/lrp/wiki/node_modules`,
  removed after). Local verification, not CI.
- Kernel replay (`scripts/kernel_replay.sh`) last passed on the baseline `4c72765`; not run
  this round (workers were building throughout). Run `scripts/kernel_replay.sh 6` when no
  build runs, before any milestone report or pull request to `main`: the row-sum migration
  touched 41 Lean files since the last replay.
- `main` (`1df822a`) is an ancestor of the tip and lacks every commit since; no pull request
  opened (see "For ARCHITECT", first item).

Commands (from `/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
scripts/gate.sh <previous-gated-tip>   # build --wfail, AxiomAudit, closure, forbidden, tests,
                                       # extract (.lake/manifest-raw.json, saved .lake/gate/<sha>.json),
                                       # check_d35, proof-only/interface classification
scripts/kernel_replay.sh 6             # leanchecker in batches; never alongside a build
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm run build && npm test; rm node_modules
```

The base passed to `gate.sh` must have a saved extract in `.lake/gate/` (a STATUS-only or
FRONTIER-only commit has none: pass its gated parent, here `18c879d`). The classifier's
"INTERFACE" is a notice: it must match audited interface changes. After each gate
`git checkout scripts/__pycache__/` (two `.pyc` files are tracked until the CI branch merges
and untracks them); delete `scripts/__pycache__/frontier.*.pyc` after `frontier.py`.

## Progress (D-35 measure)

Round 5: the Lean merged was migration 3 (comments and docstrings only), so **0 new assertions
proved and 0 tagged statements audited**; manifest at `2957b5a`: 263 proved, 5 statement-only,
1,133 unformalised, of 1,401 (unchanged).

Round 4: no Lean merged, so **0 new assertions proved and 0 tagged statements audited** (one new
wiki tag, B5SL, awaits its audit). Manifest from the `d71f8ce` extract (identical counts to
`18c879d`): **263 assertions proved**, 5 statement-only, 1,133
unformalised, of 1,401 (no new proofs merged this round; the Lean merged was the row-sum
migration). 268 distinct tags in `PercLib/`. Frontier (`docs/FRONTIER.md` at `18c879d`):
**287 ready**, 810 blocked, 41 without recorded prerequisites (start of round: 149 / 733 /
256), because `wiki-proof-uses-a`/`-b` recorded prerequisites of 215 assertions (10 have no
proof in their article: wanted proofs JM5A, R9NU, BSI3, 48GR, G12U, WD31, T9KC, 67W9, JZG4,
FM8D; 31 are in the frozen articles, not yet covered).
Tagged statements audited in round 3: **23 in Lean** (`audit-d16-tags`: PVA8, MQNP, LF50,
6YYS, L82Q, all APPROVE; `audit-mig-rowsum`: 18 respelled tags, all APPROVE by mechanical
`Iff.rfl` checks) and **1 wiki statement** (`audit-j98j`: J98J APPROVE; W498 and the context
change APPROVE WITH CHANGE, fixed by `fix-port-wiki-hier-thm11`). Every tag on the tip has a
fresh statement audit. Also on file: `audit-driven-ode-I421` (Lemma I.4.21 proved as stated in
`Analysis/DrivenODE.lean`; counts once a wiki assertion exists and is tagged: `013-wiki-I421`).

## Merged

Round 5 (seventh coordinator), one gated batch, pushed:
- **`mig-headers`** (`b7b401b`, merge `2957b5a`; D-35 migration 3 complete): process labels
  (issues, packages, agent names, decision labels) removed from the headers and declaration
  docstrings of 266 legacy files; module docstrings added to 58 files; foreign wiki tags removed from
  declaration docstrings; `scripts/legacy_headers.txt` emptied. Comments only (grep of the diff and
  the extract comparison above). Judgement calls the coordinator accepted: the upstream credit
  "produced with ChatGPT and Claude" in `Models/Site/Basic.lean` and `Percolation/Bond/Basic.lean`
  now points to `third_party/percolation/NOTICE`, which keeps the full wording (Apache 2.0 requires
  the NOTICE to travel with the code, which it does); "DECISIONS R-3" now reads "reuse permission
  recorded in `docs/DECISIONS.md`"; the tightness headers keep the mathematics of the `k ≥ 1`
  reading (the pending ruling stays listed "For Tom" below). Noticed, not in scope:
  `op8f_asymptotics` in `Analysis/LogarithmicCorrections.lean` carries a tag in its name (naming rule
  5; a rename is an interface change: queue after the window, with a deprecated alias, ruling 9h).

Round 4 (sixth coordinator), one gated batch, pushed:
- `wiki-lead-parser` (`4b63ca9`, tooling, ruling 8): headingless leads (up to three paragraphs before
  the first section heading; anchors, headings and collapsible blocks in a lead fail the build with
  file and line), lead rendered before the contents box, searchable, covered by backlinks and the
  link checks; frozen-article check gains an optional `lead` digest (existing baselines unchanged);
  8 tests. Coordinator then dropped the "parser requires a heading" parenthesis from
  `wiki/STYLE.md` rule 1 (`d71f8ce`), as the report asked.

Round 3 (fifth coordinator), five gated batches, all pushed:
- `wiki-style` (`fdc0542`): `wiki/STYLE.md`, "Draft for Tom's approval (D-19)".
- `wiki-proof-uses-a` (`029e7ac`): 147 `proofUses` rows in records a–l (coordinator spot-checked
  65PY against its proof); frontier regenerated (`3d61712`).
- **`mig-rowsum`** (`776e404`, D-35 migration 1 complete) after `audit-mig-rowsum` APPROVE on
  all 18 respelled tags (ROY9 BPR6 R84Z 7R5Q 67GX MXGM VNRG SZLN XJ74 VYCM AYPN 53Z9 F12C E771
  JZ47 BEJT MLLO F4RR; C4E9 proof only). The auditor disclosed that its first shell command
  printed the author's report; its verdicts rest on compiled `Iff.rfl` checks of old against
  new statements (36 checks, plus 91 untagged statements: 82 `Iff.rfl`, 9 by unfolding
  `rowSum_def`), so the coordinator accepted it (see "For ARCHITECT"). With
  **`wiki-generator`** (`9d06661`, ruling 8: collapsible `:::details` blocks, anchors open
  collapsed blocks, expand/collapse all, print/export expanded, TOC, backlinks, dead-link check,
  advisory link report, hover previews; 92 wiki tests).
- `wiki-math-fixes` (`202e752`): erratum `susceptibility-lower-coefficient` retagged to FF30,
  7YNX only (scout-wiki-math M3; also critic R5); `tree-graph` proof of L82Q rewritten to the
  Lean route (countable BK, JRCI, twice), statement byte-identical; `proofUses` L82Q → JRCI.
- `wiki-proof-uses-b` (`18c879d`): 68 rows in records m–z; frontier regenerated (`4e17f78`).

Round 2 (this round, three gated batches):
- After the predecessor's handoff and before this round (found in `git log`, gated on
  `4cb4679`, recorded here): `rowsum-def` (rowSum, `unitInterval.toENNReal`; audit fixes
  verified), `lrp-cov-gap` (port 28), `lrp-moment-conv`, `lrp-karamata-prim`, `lrp-sb-mgf`
  (port 13), `hier-endpoint` (H5: Prop. 2.2 endpoint, Prop. 2.12(ii) at β_c, proof-only),
  and `c53284d` recording D-36 (critic, article shape) and D-37 (repository runs without
  us) from rulings 7-10.
- `lrp-tauber-endpoints` (port 10; proof-only; the strict-tail converse of Thm I.2.11 is an
  explicit hypothesis `hconv`, to be discharged by package 12) — gate `40549b0`.
- `lrp-driven-ode` (port 5; proof-only; drops the `f > 0` premise of Lemma I.4.21 because
  the proof does not use it, a strengthening of untagged lemmas; I.4.21 is **not** recorded
  as proved: the author flags global measurability of `h`, differentiability at every
  `x > 0` and the ratio form of the hypothesis as possibly beyond the paper) — gate
  `7316ae9`.
- `attach-models` + `fix-attach-models` (33 Models tags: Site 8FLS 8EIH 6RWC 9R9K 3YMY AR5B
  M28D 3HEP MIUX; 9K6O 1J3B; Lattice 8QCR 7DGG F3YB; BinaryTree AAZS NDIC V5OZ GGVG;
  ZeroOne SA9P AHY3 KB1L; JTBG; Line BP7B FH1B; Hierarchical BW7V 9408 6KJQ YW7B KL29 B6KD
  0K45 7AER; IXEZ). V5OZ carries the audit's exact-ratio conjunct (new area lemma
  `binaryTree_law_card_ratio_eq`); the R01V wrapper and `Models/Tags/TranslationInvariant.lean`
  were removed (R01V goes to `fix-nm-longrange`). The coordinator checked the fix diff
  against both audits — gate `9314239`.

Round 2, second pass (fourth coordinator, gate `b40f5f2`):
- `pub-attrib` (on top of `pub-move`): the wiki moves to `perclib/wiki` and the manifest
  builder to `scripts/build_manifest.py`; 56 draft-original articles credited "T. Hutchcroft,
  book in preparation", one catalogue entry `hutchcroft-book`. `audit-pub-attrib`
  (fresh, did not read the author's report) **APPROVE** on ruling 6b (i)-(iv), nothing
  withheld. Merge `6146737`; pushed. Irreversible: the wiki is public on the integration
  branch. `lrp/wiki` is frozen from now on (6d) except the withheld notes-facing files.
- `frontier-doc`: `scripts/frontier.py`, `scripts/test_frontier.py`, `docs/FRONTIER.md`
  (non-Lean, merged on the gate; FRONTIER regenerated at `b40f5f2` from `wiki/records`).

Round 1 and earlier: see `git log --merges` (tooling and gate scripts, D-35 checks,
hierarchical H0-H4 and H6, salvage, D-33 ports, link tags, `nm-analysis`, `d35-binders`).

## Finished, not merged

- `work/port-wiki-hier-thm11` (025c8f3) + `work/fix-port-wiki-hier-thm11` (4b8ee89, on top):
  J98J with full proof; `audit-j98j` APPROVE for J98J, required changes W1/C1/C2 applied by the
  fix (coordinator compared the diff with the audit's texts: they match). **Deliberately not
  merged:** ruling 7 (iii) requires a critic to pass a substantially changed article;
  `critic-hierarchical-two-point` (done) gave a restructuring plan instead. J98J, its fix and
  the ruling-8 model-article restructuring (`HOLD-wiki-model-hier-two-point`, branches from the
  fix branch, waits for `wiki-lead-parser`) merge together after a fresh critic's re-read and an
  audit that tags, anchors and tagged mathematics are unchanged.
- `work/ci-workflow`, `work/automerge-workflow`: fixed on `work/fix-workflows` (merges both, applies
  A1–A4, C1, C2, X1) and `work/fix-gate-scanner` (G1, G2, scan before build in gate.sh, plus two
  extra holes it found: character literals and interpolated strings). The fresh re-audit
  `audit-fix-workflows` (done round 5) gives **APPROVE WITH CHANGE** on both: GS1/GS2 (scanner still
  passes `run_meta`, `@[tactic]`, `@[app_delab]`, `@[init]`, `cbv_simproc`, `meta`: elaboration-time
  IO, verified on Lean 4.35), CW1 (PR-scoped `.lake/build` cache lets an earlier commit forge a later
  commit's green gate/replay: no cache reads on pull-request runs), CW2 (the `scripts` job always
  fails without `lake`), AM1 (`where`/`let rec` add definitions the classifier accepts). Fix briefs
  `023-fix-scanner-r2` (branches from `work/fix-gate-scanner`) and `024-fix-workflows-r2` (from
  `work/fix-workflows`) queued for new workers with the audit attached; `HOLD-audit-fix-workflows-r2`
  (third fresh auditor) waits for both. On APPROVE: merge `work/fix-scanner-r2` then
  `work/fix-workflows-r2` (they contain their predecessors), gate, then `work/contrib-docs` and
  `work/task-board` (D-10), then mirror the queue into `tasks/` (ruling 9b).
- `work/wiki-I421` (27e9aa6, done 04:41): new wiki tag **B5SL** (Lemma I.4.21 of LRP I) with a
  full collapsed proof in `marginal-ode`; interface (new tagged statement): fresh audit
  `022-audit-wiki-I421` queued (diff and source, not the report). On APPROVE: merge (gate), then a
  critic pass of the new section when the critic slot is free (ruling 7 (iii); one critic at a
  time), then the Lean `Tags/` restatement `@[tag "B5SL"]` on `tendsto_div_of_tendsto_deriv_ratio`
  and `regularlyVarying_of_tendsto_deriv_ratio` (interface, audit after; after the window). The
  author added an `occursIn` row besides the requested `sourceOccurrences` row (README convention);
  the audit decides.
- `work/nm-longrange` (e4e9b59; ZH13, R01V): `HOLD-fix-nm-longrange` after the window (it must
  now also respell row sums with `rowSum`).
- Read-only results consumed in round 4: `scout-errata-triage` (180 entries, not 194: 92 A forced,
  4 A*, 6 B, 0 C, 76 D; follow-up `021-scout-errata-triage-b` for the 43 unreached; list for Tom
  below).
- Read-only results consumed in round 3: `scout-nearmiss`, `scout-d33-next`, `scout-defs`,
  `scout-wiki-math` (M1 → `014-wiki-fcu7`; M3, M4 merged), `scout-lrnorm` (recommends a bundled
  `ModelNorm E` extending `Seminorm ℝ E`; for ARCHITECT), `scout-salvage-t2` (drafts → HOLD-370,
  HOLD-371; draft C dropped, its input given to HOLD-210), `critic-hierarchical-two-point`
  (`/home/user/reports/critic/hierarchical-two-point.md`), `audit-d16-tags`,
  `audit-driven-ode-I421`, `audit-workflows`, `audit-j98j`, `audit-mig-rowsum`.

## In flight

Claims without a done marker at 05:00 (all live, all non-Lean): `critic-hierarchical-runaway`
(read-only), `wiki-fcu7`, `wiki-model-hier-two-point` (`015`, worktree merged the tip at 04:43),
`wiki-proofs-brw`, `wiki-proofs-susc`, `wiki-proofs-misc`, `wiki-proof-uses-frozen`,
`scout-frontier-next` (read-only), `scout-errata-triage-b` (read-only); `mig-linters` once claimed.
Worktrees: automerge-workflow, ci-workflow, contrib-docs, task-board, nm-longrange,
port-wiki-hier-thm11, fix-port-wiki-hier-thm11, fix-workflows, fix-gate-scanner, wiki-I421 (all
unmerged, keep), wiki-fcu7, wiki-model-hier-two-point and the new packages' (in flight); pub-scan and
wiki-hier-thm11 (older; check before removing). Removed in round 5: mig-headers (merged).

## Migration window: OPEN (since 03:42; migrations 1 and 3 merged at `776e404` and `2957b5a`; migration 2 released 04:57)

All prover briefs carry `HOLD-`. Non-Lean and read-only briefs stay startable. Sequence:
1. Done in round 5: `mig-headers` merged (gate `2957b5a`).
2. `000-mig-linters` (migration 2) released at tip `2957b5a` as the only Lean brief. When
   `done/mig-linters`: read the report (options enabled in `lakefile.toml`; no
   `set_option linter.* false`; no statement change: compare the saved extracts of the base and
   the merged tree as round 5 did, only `line` may differ), merge, gate against `2957b5a`, push.
   If it stopped with a linter left off, merge what is clean and record the rest. Do not merge any
   other Lean branch before it.
3. Close the window: drop `HOLD-` from the prover briefs after checking each one's setup names
   the current tip and spells row sums with `rowSum`. Release order (D-34 / STATUS priority):
   `HOLD-320-hier-restricted-susc` (H7) first; the D-33 ports `HOLD-340-lrp-I55`,
   `HOLD-350-lrp-tauber-complete`, `HOLD-355-lrp-weak-kernels`, `HOLD-345-lrp-I526`, then
   190/210 (210 now also has the Q-194 salvage as input)/220/230; near-misses 360, 363, 364
   (361: not with scout-defs D1; 362: after fix-nm-longrange); 200 and 240 (scout-nearmiss F1:
   240 must reuse `prodBernoulli_forall_notMem` from `CutPoints.lean`, not re-prove QH7Q);
   salvage 370, 371; `HOLD-fix-nm-longrange`. Keep 8+ startable, file-disjoint. H8 (`HOLD-330`)
   after H7 merges; H9 (`HOLD-335-hier-cor12`) after H8.

## Queue (`/home/user/reports/queue/`)

Claimed briefs stay in the queue directory (never delete a claimed brief); a brief is
startable when it has no `HOLD-` prefix and no `claims/<id>`.
Startable at 05:00 (5; during the window only the migration is required, COORDINATOR.md §2, and
non-Lean briefs stay startable): `000-mig-linters` (migration 2, the only Lean brief),
`022-audit-wiki-I421` (read-only), `023-fix-scanner-r2` (owns `scripts/check_forbidden.py`,
`scripts/test_check_forbidden.py`), `024-fix-workflows-r2` (owns `.github/workflows/ci.yml`,
`scripts/automerge_classify.py`, its test, `scripts/ci_script_tests.sh`, `scripts/ci_test_helpers.sh`),
`025-wiki-errata-bookkeeping` (the five inconsistent errata of `scout-errata-triage.md` §3, in five
`wiki/errata/*.json` files; no status change, D-30). Held: `HOLD-audit-fix-workflows-r2` (after
023 and 024). When the window closes, restock to 8+ from the HOLD prover briefs as listed above.

Round 4's list, for reference (now all claimed except 022):
`015-wiki-model-hier-two-point` (released this round: `hierarchical-two-point.md`, its record, its
baseline digests; branches from `work/fix-port-wiki-hier-thm11`), `016-wiki-proofs-brw` (full
proofs for BSI3, 48GR, G12U, FM8D: `branching-random-walk.md`, `size-biased-laws.md` and records),
`017-wiki-proofs-susc` (67W9, JZG4: `integrated-susceptibility.md` and record),
`018-wiki-proofs-misc` (JM5A, R9NU, WD31, T9KC: `adaptive-three-point.md`,
`critical-exponents.md`, `infinite-cluster-uniqueness.md` and records), `019-wiki-proof-uses-frozen`
(`proofUses` in 8 frozen-article records, not the baseline; stops if the baseline covers records),
`020-scout-frontier-next` (read-only: top-25 ready assertions by distance to Lean, 10 draft
prover briefs into `/home/user/reports/drafts/frontier/` for after the window),
`021-scout-errata-triage-b` (read-only), `022-audit-wiki-I421` (read-only).
File overlap accepted: `015` and `014-wiki-fcu7` (claimed) both edit `wiki/migration-baseline.json`,
different articles' entries; merge one at a time. The three `wiki-proofs-*` packages are
mathematical (ruling 8): each needs a fresh correctness audit before merge (write it when the
done marker appears; diff and sources, not the author's report).
Claimed (round 5): `011-critic-hierarchical-runaway`, `014-wiki-fcu7`, `015`-`021` (the
packages listed under "In flight"), plus older claimed briefs with done markers (`000-mig-headers`,
`012-audit-fix-workflows`, `010`, `013`, `329`, …).
Held (Lean, window): `HOLD-190-lrp-first-moment-b`, `HOLD-200-nm-bond-core`,
`HOLD-210-lrp-I41-mt`, `HOLD-220-lrp-spatial-russo-a`, `HOLD-230-lrp-levy-measures`,
`HOLD-240-nm-probability`, `HOLD-320-hier-restricted-susc` (H7), `HOLD-330-hier-thm11` (H8),
`HOLD-335-hier-cor12` (H9), `HOLD-340-lrp-I55` (D-33 pkg 6), `HOLD-345-lrp-I526` (pkg 8),
`HOLD-350-lrp-tauber-complete` (pkg 12, option C1: written out, Defs package later; discharges
`hconv`), `HOLD-355-lrp-weak-kernels` (pkgs 14+15), `HOLD-360-nm-core-wrappers`,
`HOLD-361-nm-tree-depth`, `HOLD-362-nm-kernels-sitepaths`, `HOLD-363-nm-finite-coordinates`,
`HOLD-364-nm-uniform-volume` (near-misses, interface, audit after), `HOLD-370-salvage-directional-decay`
(I8WP, 23RT; interface), `HOLD-371-salvage-kernel-geometry`, `HOLD-fix-nm-longrange` (`HOLD-mig-linters` released as
`000-mig-linters` in round 5).
Held (sequencing, non-Lean): `HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability` (after their targets).

Next packages to brief: after the window, rename `op8f_asymptotics`
(`Analysis/LogarithmicCorrections.lean`; tag in a declaration name, naming rule 5) with a deprecated
alias (interface, audit after; ruling 9h); after `wiki-model-hier-two-point`, a fresh critic re-read and an audit
of unchanged tags/anchors/mathematics, then merge with J98J; the J98J Lean tag on
`HierarchicalTwoPointAveraged` (interface) once J98J is on the tip; a wiki mathematical package
for critic reports R2 (align `0<β_c` in J98J), R4 (precise statements for V4QQ and YWTU:
hypotheses as J98J, all `n ≥ 0`, constants depending only on `d,L,α,c,C`) and R6 (constant
dependence in 655W and 7YNX), each with a fresh audit (statement changes; R1, a tagged
non-radial pointwise variant, optional); after `critic-hierarchical-runaway`, the runaway
split (a reviser, then critic re-read); tagged Lean restatement of B5SL (Lemma I.4.21) after `audit-wiki-I421` approves and B5SL merges;
correctness audits of `wiki-proofs-brw`/`-susc`/`-misc` when done; errata §3 inconsistencies
(`scout-errata-triage.md` §3: surplus tag attachments of `compound-zeta-normalization` (G12U, 6ZYT)
and `boundary-scaling-scope` (8XA9), the truncated `reverse-bk-cancellation` entry, the
`walk-time-boundary` locator) as one wiki errata-bookkeeping package (owns `wiki/errata/*.json`
entries named there; no status change, D-30); a critic for the long-range flagship article
`regular-variation` (ruling 7 (ii)) when the critic slot is free; scout-defs D6 `rv-const-mul` (proof-only), D1 `def-ktree`, D2
`def-pathcount`, D3a `def-hier-level` (after H7/H8; D3b touches W498 and
`HierarchicalTwoPointAveraged`), D4a/D4b (wait for ARCHITECT); D-33 drafts E/F (packages 31,
32, optional); near-miss NM-4, NM-6 (absorbs QH7Q, before 240), NM-7, NM-8, NM-9 (needs F2
ruling); tier-1 salvage (Q-188, Q-154, Q-149: check against merged ports first); `proofUses` for
the frozen `sharpness` and `hierarchical-two-point` records after `014`/`015` merge; ruling 9b: mirror the queue in `tasks/open/` once
`task-board` merges. Wiki revisions of frozen articles must update `migration-baseline.json`.

## For ARCHITECT

- Round 5 (seventh coordinator): the launch instructions again said "never main, no PRs/issues";
  no pull request opened, open pull requests/issues not read (first item below unchanged).
- `mig-headers` replaced the upstream credit "produced with ChatGPT and Claude" in two headers by a
  pointer to `third_party/percolation/NOTICE` (which keeps the full wording) because the D-35 header
  check rejects `\bClaude\b`. Accepted by the coordinator; object if the upstream wording must stay
  verbatim (then the D-35 check needs an exemption for third-party credit lines).

- **Pull requests to `main`.** Ruling 10(1) authorises a pull request from the integration
  branch to `main` after each fully gated batch, but this coordinator's launch instructions
  say "never main, no PRs/issues", and COORDINATOR.md still quotes ruling 5. Not opened;
  `main` (`1df822a`) lacks everything since. Please align the launcher and COORDINATOR.md
  with ruling 10, or confirm ruling 5 stands. (The kernel replay is also due before the
  first such pull request.) The fourth, fifth and sixth coordinators' launch instructions again said
  "never main, no PRs/issues"; again not opened, and open pull requests/issues on `perclib` were
  not read (ruling 10 (3) / 9g also wait on this).
- **Auto-merge evidence:** `audit-workflows` independently required the same change (X1:
  kernel replay on every PR and required by auto-merge); queued in `005-fix-workflows`.
- **Definitions in the D-2 bond interface (D-34 escalation).** `scout-defs` proposes adding
  `localConn`/`localCluster` (wiki OG96), `IsCut` and optionally `boundaryFlux` (6EIM) to
  `Bond/Basic.lean`, and `boundarySusceptibility` to `Intensity/Defs.lean`, then folding about
  30 files and re-auditing 19 tags. Options: (a) as proposed, `IsCut` in `Bond/Basic.lean`
  (scout's recommendation), OG96 on `localCluster`; (b) `IsCut` in `LongRange/Defs.lean`
  (only long-range uses it today); (c) defer until outside contributors' branches are fewer.
  Recommendation: (a), run right after the migrations (it is a migration-sized fold, ruling 9h).
  Nothing is queued until you answer; D1, D2, D3a and D6 (one area each) the coordinator runs.
- **Generality beyond `law q` (D-34, scout-nearmiss F2).** connection-kernels (70KD, UZ7J,
  C2YT, 96A2), critical-exponents (OB0A) and HOLD-200's ZAIH/NEM5/6HJ9 state results for any
  probability law on configurations; the Lean is `law q`. Tagging the `law q` form narrows them.
  Options: (a) state them for `μ : Measure (Config V)` with `[IsProbabilityMeasure μ]` and add a
  definition for `fun x y => μ (conn x y)`; (b) split the wiki assertions into a general
  sentence (description) and a `law q` statement; (c) leave them untagged. Recommendation (a):
  it is free generality (D-35 rule 4) and the bond interface is unaffected.
- **Migration window reading.** Rounds 2 and 3 kept read-only scouts, audits, the critic and
  non-Lean tooling startable during the window (they cannot conflict with a migration); only
  Lean briefs are held. Round 3 also requires the interface audit of the migration
  (`audit-mig-rowsum`) before merging it (ruling 4), which lengthens the window by one audit.
  Object if the window must hold everything, or if a spelling-only migration may merge on the
  gate with the audit afterwards.
- `audit-wiki-hier-thm11` disclosed that it read the author's report before its verdict; its
  J98J approval was treated as not fresh, and the fresh `audit-j98j` replaced it.
- `lrp-driven-ode`: `audit-driven-ode-I421` (fresh) finds Lemma I.4.21 proved as stated, no
  hypothesis beyond the paper. It counts once a wiki assertion for it exists and is tagged.
- **The long-range norm (D-35 open question), now prepared.** `scout-lrnorm`
  (`/home/user/reports/scout-lrnorm.md`) prototyped the options on real statements and
  recommends (a) a bundled `ModelNorm E` extending `Seminorm ℝ E` (in e.g.
  `PercLib/Analysis/ModelNorm/Defs.lean`) as the statement interface, with a synonym
  `WithModelNorm N` used inside proofs for mathlib's finite-dimensional API: 5 files, 29
  separation hypotheses removed, 4 tagged statements re-audited (PVA8, MQNP, LF50, 6YYS), proofs
  adapt mechanically. Fallback: a `Seminorm.IsNorm` predicate. (b) a normed-group instance on a
  type synonym is ruled out as the interface by the Lévy definitions in `Probability/Dispersion`.
  Your decision; the coordinator would run it as a small migration right after the window.
- **Audit freshness, mechanical checks.** `audit-mig-rowsum` saw the author's report by accident
  (disclosed) but based every verdict on compiled `Iff.rfl` checks; the coordinator accepted it,
  unlike `audit-wiki-hier-thm11` (prose judgement). Object if mechanical audits must also be
  re-run by a fresh agent.
- **Ruling 7 (iii) and audited statements.** J98J is audited and fixed but not merged, because
  its article has not passed a critic; it will merge with the model-article restructuring.
  Object if an audited statement should merge first and the critic pass follow.
- The round-1 note stands: start a coordinator only after its predecessor has returned.
  This round found four merges and a DECISIONS commit made after the predecessor's STATUS
  handoff and not recorded in it (now recorded above).
- Coming up, the coordinator's decision unless ARCHITECT objects: salvage branches Q-81
  (Galton–Watson definitions) and Q-10 (uniqueness definitions), only with a fresh audit
  and if no existing notion covers them.

## For Tom

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
  choice of fix is yours), `gladkov:capacity-law` (Thm 8.2 false as stated). The remaining 43 are
  being checked (`scout-errata-triage-b`); 33 Heydenreich–van der Hofstad entries need a copy of the
  book (the host was unreachable).
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
- Errata: `scout-errata-triage` is classing every provisional erratum against the published
  source (forced / plausible / mistaken / unchecked) so you can confirm the forced ones in bulk.
## Lessons

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
