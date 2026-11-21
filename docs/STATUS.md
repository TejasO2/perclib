# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026,
04:10 UTC, at the end of coordinator round 3 (fifth coordinator). A coordinator with no
memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) (the procedure for one
round), [COORDINATION.md](COORDINATION.md) (worker rules), [DECISIONS.md](DECISIONS.md)
(D-34, D-35, D-36, D-37) and `/home/user/reports/RULINGS.md` (container-local rulings 1-10;
obey them). Container-local reports, briefs and rulings are also committed (copies, for
durability, ruling 9i) in the private repository under `lrp/docs/reports/` at the round's
lrp commit; `/home/user/reports/` stays the live copy.
## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. Pushed:
  `origin/claude/zen-lovelace-rvlcw2` = the commit of this STATUS file, whose parent
  **`fdc0542`** (merge of `work/wiki-style`) is the last gated commit. lrp: the round-3 commit
  adding `docs/reports/` (on `5a2943b`; `lrp/wiki` stays frozen, ruling 6d).
- **Last gate passed: `fdc0542`** (`scripts/gate.sh b40f5f2`, 21 Nov ~04:07): build (3,922
  jobs), axiom audit of 5,954 constants (only `propext`, `Classical.choice`, `Quot.sound`),
  import closure of 329 modules, forbidden scan (329 files), classifier tests, extract, D-35
  checks; "PROOF-ONLY change against b40f5f247e0e: 0 Lean file(s)" (the batch was
  `wiki/STYLE.md` only). Earlier green: `b40f5f2`, `9314239`, `7316ae9`, `40549b0`, `4cb4679`.
  Local verification, not CI.
- **Pre-verification of `work/mig-rowsum` (not merged):** a test merge `d2b3110` of
  `work/mig-rowsum` onto `a9d25c3`, in a throwaway worktree (removed), passed the full gate
  (`scripts/gate.sh b40f5f2`, 2 min 35 s warm): build, axiom audit (5,954 constants), closure,
  forbidden, D-35 checks; "INTERFACE change … SizeBiasedLaws.lean: ['tag']" as expected. The
  merge waits for `audit-mig-rowsum` (ruling 4; claimed); after APPROVE, merge it onto the
  then tip and re-run the gate (the merge base will differ from `d2b3110`).
- Kernel replay (`scripts/kernel_replay.sh`) last passed on the baseline `4c72765`; not run
  this round (workers were building). Run `scripts/kernel_replay.sh 6` when no build runs,
  before any milestone report or pull request to `main`.
- `main` (`1df822a`) is an ancestor of the tip and lacks every commit since; no pull request
  opened (see "For ARCHITECT", first item). The public wiki is on the pushed integration branch.

Commands (from `/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
scripts/gate.sh <previous-gated-tip>   # build --wfail, AxiomAudit, closure, forbidden, tests,
                                       # extract (.lake/manifest-raw.json, saved .lake/gate/<sha>.json),
                                       # check_d35, proof-only/interface classification
scripts/kernel_replay.sh 6             # leanchecker in batches; never alongside a build
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
```

The base passed to `gate.sh` must have a saved extract in `.lake/gate/` (a STATUS-only
commit has none: pass its gated parent; `fdc0542` and `b40f5f2` have one). The classifier's
"INTERFACE" is a notice: it must match audited interface changes. After each gate
`git checkout scripts/__pycache__/` (two `.pyc` files are tracked until the CI branch merges
and untracks them); delete `scripts/__pycache__/frontier.*.pyc` after `frontier.py`.
## Progress (D-35 measure)

Manifest from the `fdc0542` extract: **263 assertions proved**, 5 statement-only, 1,133
unformalised, of 1,401 (unchanged this round: no Lean merged). 268 distinct tags in
`PercLib/`. Frontier (`docs/FRONTIER.md`, unchanged; regenerated at `fdc0542` and identical
apart from the commit line): 149 ready, 733 blocked, 256 unproved without recorded
prerequisites (being recorded by `wiki-proof-uses-a`/`-b`).
Tagged statements audited this round: **5** (`audit-d16-tags`: PVA8, MQNP, LF50, 6YYS, L82Q
all APPROVE, binder tables on file). With that, **every tag on the integration tip has a fresh
statement audit.** Also on file: `audit-driven-ode-I421` (Lemma I.4.21 is **proved as stated**
by `tendsto_div_of_tendsto_deriv_ratio` + `regularlyVarying_of_tendsto_deriv_ratio` in
`Analysis/DrivenODE.lean`; no hypothesis beyond the paper; not yet counted because no wiki
assertion carries Lemma I.4.21: a wanted assertion, then a Tags/ restatement package);
`audit-workflows` (both CI branches APPROVE WITH CHANGE; fixes queued).
## Merged

Round 3 (fifth coordinator, gate `fdc0542`):
- `wiki-style`: `wiki/STYLE.md` (145 lines), marked "Draft for Tom's approval (D-19)"; ruling
  7 (i) says work proceeds on the draft meanwhile. Non-Lean, merged on the gate. Listed
  "For Tom".

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

- `work/mig-rowsum` (5394b2a, 3 commits on `9314239`; 176 row-sum sites in 40 files, plus a
  proof-only repair in `Models/FiniteGraph.lean`; no API added). Respells 19 tagged statements
  (ROY9 BPR6 R84Z 7R5Q 67GX MXGM VNRG SZLN XJ74 VYCM AYPN 53Z9 F12C E771 JZ47 BEJT MLLO F4RR;
  C4E9 proof only). Gate on a test merge green (above). Waits for `audit-mig-rowsum`
  (`002`, claimed 04:00): mechanical old-vs-new `Iff.rfl` checks plus binder tables. Sites left
  (not D-2 row sums) are listed in `/home/user/reports/mig-rowsum.md`.
- `work/port-wiki-hier-thm11` (025c8f3 on `a9d25c3`): J98J (averaged critical two-point
  estimate) with a full proof in `wiki/articles/hierarchical-two-point.md`, context widened to
  symmetric kernels, W498 marked radial, `proofUses` for J98J and W498, baseline digests, test
  count 65→66. New tagged wiki statement → waits for `003-audit-j98j` (fresh; also checks the
  proof chain 7AER→FF30→12NL→655W→7YNX closes, and V4QQ/YWTU under the widened context) and,
  under ruling 7 (iii), `004-critic-hierarchical-two-point` (the same critique is the input for
  the ruling-8 model article). Then the J98J Lean tag on `HierarchicalTwoPointAveraged`
  (interface, with audit) after H8.
- `work/ci-workflow` (560bd59), `work/automerge-workflow` (279739b): `audit-workflows` APPROVE
  WITH CHANGE for both (F1 high: the automerge classifier accepts `def`/`instance`/`#eval!`
  hidden after `«x--»`, indented `open`, etc.; F2 high: the tip's `check_forbidden.py` misses
  `#eval!` and text after `«…--…»`; F3/F4 medium; F5 low). Fixes queued: `005-fix-workflows`
  (A1–A4, C1, C2, X1 = the kernel-replay requirement, i.e. the coordinator's "fix A") on a
  branch that merges both, and `006-fix-gate-scanner` (G1, G2, scan before build in gate.sh).
  Then `HOLD-audit-fix-workflows` (fresh re-audit) before anything merges.
- `work/contrib-docs` (705ac8c), `work/task-board` (0ae16d1): merge together with the fixed
  workflows (D-10). The task-board mapping of HOLD briefs to task ids is in the round-2 text
  of git history (`git show a9d25c3:docs/STATUS.md`); new HOLD briefs this round (340-364)
  correspond to task-board ids `lrp-I55`, `lrp-I526`, `lrp-tauber-complete`,
  `lrp-weak-kernels`, `global-threshold-infimum` etc. where the board has them.
- `work/nm-longrange` (e4e9b59; ZH13, R01V): `HOLD-fix-nm-longrange` after the migrations.
- Read-only results consumed this round: `scout-nearmiss` (58 open near-misses, packages
  NM-1…NM-10, findings F1–F7, no false assertion found), `scout-d33-next` (draft briefs for D-33
  packages 6, 8, 12, 14+15, 31, 32), `scout-defs` (definition packages D1–D6, five questions for
  LEAD), `audit-d16-tags`, `audit-driven-ode-I421`, `audit-workflows`, `critic-general`.
## In flight

Claims without a done marker at 04:10: `audit-mig-rowsum` (scratch worktree
`/home/user/wt/audit-mig-rowsum`, detached; it removes it), `scout-wiki-math`,
`wiki-generator` (worktree `/home/user/wt/wiki-generator`; note from `wiki-style`: the parser
`wiki/scripts/articles.mjs` rejects an article whose body does not start with a heading, so a
ruling-8 lead is impossible until the generator changes; and `check-articles.mjs` locks the
prose of the 12 baseline articles, so every revision also updates `migration-baseline.json`),
`wiki-proof-uses-a`. Worktrees: automerge-workflow, ci-workflow, contrib-docs, task-board,
nm-longrange, mig-rowsum, port-wiki-hier-thm11 (unmerged), wiki-generator,
wiki-proof-uses-a (in flight), audit-mig-rowsum (scratch). Removed this round: wiki-style
(merged).
## Migration window: OPEN (since 03:42; at 04:10 `mig-rowsum` done, waiting for its audit)

Preconditions held: `rowsum-def` merged, no claimed Lean work open. All prover briefs carry
`HOLD-`. Non-Lean and read-only briefs stay startable (they touch no file a migration owns);
this round also released `scout-lrnorm` (it owns only a never-merged scratch file and the
migrations do not touch the seminorm). Sequence from here:
1. When `done/audit-mig-rowsum`: if APPROVE for all 19 respelled tags, merge `work/mig-rowsum`
   onto the tip, gate, push (INTERFACE notice expected; it is the audited one). If any REJECT,
   queue a fix brief for a new worker with the audit attached; the window stays open.
2. Rename `HOLD-mig-headers` to `0NN-mig-headers` (it now lists `audit-d16-tags`' header
   findings as a checklist), gate, merge (comments only: proof-only on the classifier).
   Then `mig-linters` if time.
3. Close the window: drop `HOLD-` from the prover briefs after checking each one's setup names
   the current tip and spells row sums with `rowSum`; release order by D-34/STATUS priority:
   `HOLD-320-hier-restricted-susc` (H7) first, then the D-33 ports `HOLD-340-lrp-I55`,
   `HOLD-350-lrp-tauber-complete`, `HOLD-355-lrp-weak-kernels`, `HOLD-345-lrp-I526`, the older
   190/210/220/230, near-miss 360/363/364 (361 and 362 have ownership notes), 200 and 240
   (check scout-nearmiss F1: QH7Q duplication with `CutPoints.lean`; tell 240 to reuse
   `prodBernoulli_forall_notMem`), and `HOLD-fix-nm-longrange`. H8 (`HOLD-330`) after H7
   merges; H9 (`HOLD-335-hier-cor12`) after H8.
## Queue (`/home/user/reports/queue/`)

Claimed briefs stay in the queue directory (never delete a claimed brief); a brief is
startable when it has no `HOLD-` prefix and no `claims/<id>`.
Startable at 04:10 (8, pairwise disjoint in files and disjoint from claimed work; none is Lean
work, as the window requires): `003-audit-j98j` (read-only), `004-critic-hierarchical-two-point`
(read-only; one critic at a time), `005-fix-workflows` (`.github/workflows/*.yml`,
`scripts/automerge_classify.py` and its test, on a branch merging both CI branches),
`006-fix-gate-scanner` (`scripts/check_forbidden.py`, `check_proof_pr.py`'s literal stripper,
`test_proof_pr.py`, new `test_check_forbidden.py`, `gate.sh` order), `007-scout-lrnorm` (scratch
file only), `325-wiki-proof-uses-b` (`proofUses` of `wiki/records/[m-z]*.json` except the 12
frozen), `329-scout-errata-triage` (read-only: classify the provisional errata against the
published sources for Tom), `330-scout-salvage-t2` (read-only: restated signatures and draft
briefs for Q-211, Q-195, Q-194).
Claimed: `002-audit-mig-rowsum`, `318-wiki-generator`, `322-wiki-proof-uses-a`,
`324-scout-wiki-math` (plus older claimed briefs with done markers).
Held (Lean, window): `HOLD-190-lrp-first-moment-b`, `HOLD-200-nm-bond-core`,
`HOLD-210-lrp-I41-mt`, `HOLD-220-lrp-spatial-russo-a`, `HOLD-230-lrp-levy-measures`,
`HOLD-240-nm-probability`, `HOLD-320-hier-restricted-susc` (H7), `HOLD-330-hier-thm11` (H8),
`HOLD-335-hier-cor12` (H9, new), `HOLD-340-lrp-I55` (D-33 pkg 6, new), `HOLD-345-lrp-I526`
(pkg 8, new), `HOLD-350-lrp-tauber-complete` (pkg 12, option C1 chosen: written out, Defs
package later; discharges `hconv`), `HOLD-355-lrp-weak-kernels` (pkgs 14+15, new),
`HOLD-360-nm-core-wrappers`, `HOLD-361-nm-tree-depth` (not with scout-defs D1),
`HOLD-362-nm-kernels-sitepaths` (after fix-nm-longrange: shared `TranslationInvariant.lean`),
`HOLD-363-nm-finite-coordinates`, `HOLD-364-nm-uniform-volume` (all near-miss, interface,
audit after); `HOLD-fix-nm-longrange`; `HOLD-mig-headers`, `HOLD-mig-linters`.
Held (sequencing, non-Lean): `HOLD-338-critic-hierarchical-runaway` (after 004; with a split
plan for the 2,291-line article), `HOLD-audit-fix-workflows` (after 005 and 006),
`HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability` (after their targets).

Next packages to brief: scout-defs D6 `rv-const-mul` (proof-only, after the window and after
nothing else owns `DrivenODE.lean`), D1 `def-ktree`, D2 `def-pathcount`, D3a `def-hier-level`
(coordinator's order: after H7/H8 so the flagship line is not delayed; D3b touches W498 and
`HierarchicalTwoPointAveraged`), D4a/D4b (`localConn`, `IsCut` in `Bond/Basic.lean`: waits for
ARCHITECT, below); D-33 drafts E/F (packages 31, 32, optional); near-miss NM-4, NM-6 (absorbs
QH7Q, before 240), NM-7, NM-8, NM-9 (needs F2 ruling); salvage tier 2 from `scout-salvage-t2`;
tier-1 salvage (Q-188, Q-154, Q-149: check against merged ports first); a wiki assertion for
Lemma I.4.21, then its Tags/ restatement; the ruling-8 model article `hierarchical-two-point`
after `wiki-generator`, `audit-j98j` and the critic; ruling 9b: mirror the queue in
`tasks/open/` once `task-board` merges. Wiki revisions must update `migration-baseline.json`.
## For ARCHITECT

- **Pull requests to `main`.** Ruling 10(1) authorises a pull request from the integration
  branch to `main` after each fully gated batch, but this coordinator's launch instructions
  say "never main, no PRs/issues", and COORDINATOR.md still quotes ruling 5. Not opened;
  `main` (`1df822a`) lacks everything since. Please align the launcher and COORDINATOR.md
  with ruling 10, or confirm ruling 5 stands. (The kernel replay is also due before the
  first such pull request.) The fourth and fifth coordinators' launch instructions again said
  "never main, no PRs/issues"; again not opened.
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
- `audit-wiki-hier-thm11` disclosed that it read the author's report before its verdict.
  Its J98J approval is treated as not fresh; the carried-over J98J gets a fresh audit
  before merge.
- `lrp-driven-ode`: `audit-driven-ode-I421` (fresh) finds Lemma I.4.21 proved as stated, no
  hypothesis beyond the paper. It counts once a wiki assertion for it exists and is tagged.
- Open under D-35: the long-range norm (structure versus type synonym); `scout-lrnorm` is
  released (007) and now also covers `audit-d16-tags`' finding that the separation hypothesis
  is spelled 28 times.
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
- The wiki critic's mathematical reports (critic/general.md §5), being settled by
  `scout-wiki-math`: FCU7 (`sharpness`) has no precise statement; the provisional erratum
  "susceptibility-lower-coefficient" is attached to W498/V4QQ/YWTU although its text says
  they are unchanged; `tree-graph` is inconsistent about which BK proves L82Q. Any change to
  FCU7's content will come to you if the published source does not decide it.
- Repository settings for ruling 10(2), once the CI workflow is on `main`: (1) Settings →
  Branches → add a protection rule for `main`: require a pull request, require the status
  check `CI / gate`, no force pushes; (2) Settings → General → allow auto-merge;
  (3) add collaborators to `.github/automerge-authors` and `CODEOWNERS` as you wish.
- Lemma I.4.13, second half, of *Critical long-range percolation I* implicitly assumes
  local integrability of `h` on `(1, ∞)` (compiled counterexample
  `not_integrableOn_rpow_mul_indicator_sub_inv`).
- The 194 provisional errata entries in the wiki await confirmation (D-30).
- Universal tightness, issue-52 reading (`k ≥ 1` where the source prints `k ≥ 0`, false
  at `k = 0`); the hierarchical programme uses only `k ≥ 1`.
- arXiv:2103.17013v1 Prop. 2.12(ii) prints constant 1 where the flux argument gives
  `(L^α-1)/(β_c C (1-L^{-d}))` (provisional erratum; the Lean target keeps the factor).
- The W498 remark on radiality is reworded in the carried-over J98J change; the audit also
  suggests stating V4QQ/YWTU's scope (derive from J98J for symmetric `J`, or "for radial
  `J`"): a statement change, for your decision.
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
- **Low numeric prefixes (002-007)** put critical-path briefs first; workers take the
  alphabetically first startable brief.
