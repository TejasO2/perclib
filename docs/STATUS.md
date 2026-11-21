# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026,
03:50 UTC, at the end of coordinator round 2, second pass (fourth coordinator). A coordinator with no
memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) (the procedure for one
round), [COORDINATION.md](COORDINATION.md) (worker rules), [DECISIONS.md](DECISIONS.md)
(D-34, D-35, D-36, D-37) and `/home/user/reports/RULINGS.md` (container-local rulings 1-10;
obey them).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. Pushed:
  `origin/claude/zen-lovelace-rvlcw2` = the commit of this STATUS file, whose parent
  **`b40f5f2`** is the last gated commit (plus the regenerated `docs/FRONTIER.md` in the
  STATUS commit). lrp: `5a2943b` (unchanged; `lrp/wiki` is now frozen, ruling 6d).
- **Last gate passed: `b40f5f2`** (`scripts/gate.sh 9314239`): build (3,922 jobs), axiom
  audit of 5,954 constants (only `propext`, `Classical.choice`, `Quot.sound`), import
  closure of 329 modules, forbidden scan, classifier tests, extract, D-35 checks;
  "PROOF-ONLY change against 931423955c86: 0 Lean file(s)" (the batch was `wiki/`,
  `scripts/` and `docs/` only). `python3 scripts/test_frontier.py`: 7 tests OK. The wiki
  tree at the tip is byte-identical to `93aaac3`, where `audit-pub-attrib` ran `npm ci`,
  `npm run build` (77/77 tests, 142 articles) and `npm run test:export`. Earlier green:
  `9314239` (base `7316ae9`, INTERFACE = the 33 audited Models tags), `7316ae9`, `40549b0`,
  `4cb4679`. Local verification, not CI.
- Kernel replay (`scripts/kernel_replay.sh`) last passed on the baseline `4c72765`. Due
  before the next milestone report; run `scripts/kernel_replay.sh 6` when no build runs.
- `main` (`1df822a`) is an ancestor of the tip and lacks every commit since; no pull
  request to `main` has been opened (see "For ARCHITECT", first item). **The public wiki is
  now on the pushed integration branch** (`perclib/wiki`, ruling 6c satisfied by
  `audit-pub-attrib`'s APPROVE).

Commands (from `/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
scripts/gate.sh <previous-gated-tip>   # build --wfail, AxiomAudit, closure, forbidden, tests,
                                       # extract (.lake/manifest-raw.json, saved .lake/gate/<sha>.json),
                                       # check_d35, proof-only/interface classification
scripts/kernel_replay.sh 6             # leanchecker in batches; never alongside a build
cd /home/user/lrp && python3 scripts/build_manifest.py /home/user/perclib/.lake/manifest-raw.json --output /home/user/reports/manifest.json
```

The base passed to `gate.sh` must have a saved extract in `.lake/gate/` (a STATUS-only
commit has none: pass its gated parent). The classifier's "INTERFACE" is a notice: it must
match audited interface changes. After each gate `git checkout scripts/__pycache__/` (two
`.pyc` files are tracked until `ci-workflow` merges and untracks them).

## Progress (D-35 measure)

Manifest from the `b40f5f2` extract (rebuilt with `python3 scripts/build_manifest.py
.lake/manifest-raw.json --output /home/user/reports/manifest.json`, the builder now lives in
`perclib/scripts/`): **263 assertions proved**, 5 statement-only, 1,133 unformalised, of
1,401 (unchanged by this pass: no Lean merged; start of round: 231 / 4 / 1,166). 268
distinct tags in `PercLib/`. Frontier (`docs/FRONTIER.md`, regenerated at `b40f5f2` with
`python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records
--commit <sha> --output docs/FRONTIER.md`): 149 ready, 733 blocked, 256 unproved without
recorded prerequisites. Tagged statements audited and merged this round: **33** (attach-models: 23 of
24 approved by audit a, V5OZ after the required change; 9 of 10 by audit b; R01V withheld
for the ordered-pair form). Wiki: J98J reviewed (`audit-wiki-hier-thm11`, approve with one
change; independence breached, see "For ARCHITECT"). Every merged tag has a fresh audit
except the five D-16 proof tags PVA8, MQNP, LF50, 6YYS, L82Q (audit queued:
`313-audit-d16-tags`).

## Merged

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

- `work/ci-workflow` (560bd59), `work/automerge-workflow` (279739b; CODEOWNERS,
  `.github/automerge-authors`, `automerge.yml`, `scripts/automerge_classify.py`, 29 tests;
  inert until Tom sets `AUTOMERGE_ENABLED` and protects `main`): wait for
  `316-audit-workflows` (released this pass; ruling 10(2)). The automerge author raises a
  decision: kernel replay is not part of the auto-merge evidence (fix A: run kernel-replay
  on every PR and require it; fix B: auto-merge requires that job). Coordinator's choice
  unless the audit says otherwise: **A**, as a fix after the audit (D-29, ruling 9e).
- `work/contrib-docs` (705ac8c) and `work/task-board` (0ae16d1; `tasks/README.md`, 28 open
  tasks, 10 `good-first-task`; nothing outside `tasks/`; grep for private paths clean, only
  the public port source `PercLib/CriticalLRP/` of `yujinhkim/lrp` named): both describe CI
  and auto-merge, so they merge **together with the workflows** after `audit-workflows`
  approves (D-10: the branch never describes CI that is not present). The task-board's
  mapping: HOLD-200 = tasks cluster-count-any-law, cluster-second-moment-any-law,
  cluster-mixed-moments-any-law, kernel-comparison-off-diagonal; HOLD-240 =
  holley-observable-form, profile-perturbation-bound, countable-closed-product; other
  HOLD-derived tasks keep their ids. When a lane takes one, move its file to
  `tasks/claimed/` in the same push (ruling 9b).
- `work/nm-longrange` (e4e9b59; ZH13, R01V): fix brief `HOLD-fix-nm-longrange` (audit b's
  step 2: one pair of `Sym2` names `…_of_ne`; R01V wrapper in
  `Models/Tags/TranslationInvariant.lean`; exactly one R01V tag; row sums as migrated).
  Release it after the migrations; then a fresh re-audit of R01V.
- lrp `work/wiki-hier-thm11` (a795d41) + `/home/user/reports/wiki-hier-thm11-baseline.patch`:
  carried over to `perclib` by `317-port-wiki-hier-thm11` (released this pass; adds 7AER to
  J98J `proof_uses`); then a fresh audit of J98J, then the J98J Lean tag on
  `HierarchicalTwoPointAveraged` (interface, with audit).
- `critic-general` (critique `/home/user/reports/critic/general.md`, report
  `/home/user/reports/critic-general.md`): audit only, nothing to merge. Consumed by
  `323-wiki-style` (STYLE.md draft) and `324-scout-wiki-math` (its mathematical reports
  M1, M3, M4). Its flagship recommendation agrees with the coordinator's choice
  `hierarchical-two-point` (proof to be assembled from `hierarchical-runaway` l. 37-162,
  auditor to confirm the chain closes); fallback `subcritical-bound`. M2 (hypotheses only in
  the front-matter `context`) is handled by an instruction: every audit brief that compares
  a Lean statement with a wiki assertion must say that the assertion includes its article's
  front-matter context.

## In flight

Claims without a done marker at 03:50: `mig-rowsum` (worktree `/home/user/wt/mig-rowsum`,
no commit yet), `scout-defs` (claimed 03:41), `audit-d16-tags`, `scout-d33-next`.
Worktrees are `/home/user/wt/<id>`; claims in `/home/user/reports/claims/`. Remaining
worktrees: automerge-workflow, ci-workflow, contrib-docs, task-board, nm-longrange,
mig-rowsum (pub-attrib, pub-move, frontier-doc removed after merge).

## Migration window: OPEN (since 03:42, tip `9314239`; still open at 03:50, `mig-rowsum` claimed, not done)

Preconditions held: `rowsum-def` merged, and no claimed Lean work is open
(`lrp-driven-ode` and `fix-attach-models` merged). `001-mig-rowsum` is the only startable
Lean brief; all prover briefs carry `HOLD-`, and so does `HOLD-310-scout-lrnorm` (it builds
against shapes the migrations change). Read-only and non-Lean briefs (scouts, audits,
critic) stay startable: they touch no file a migration owns. Sequence:
1. When `done/mig-rowsum`: read the report, merge, gate; the tagged declarations it
   touched need re-review (list them; queue one audit brief confirming "spelling only").
2. Rename `HOLD-mig-headers` to `002-mig-headers`, gate, merge. Then `mig-linters` if time.
3. Close the window: drop `HOLD-` from the prover briefs (190, 200, 210, 220, 230, 240,
   320, 310-scout-lrnorm) after checking each one's setup names the current tip and spells
   row sums with `rowSum`; release `HOLD-fix-nm-longrange`; restock from the scout reports
   below.

## Queue (`/home/user/reports/queue/`)

Claimed briefs stay in the queue directory (never delete a claimed brief); a brief is
startable when it has no `HOLD-` prefix and no `claims/<id>`.
Startable at 03:50 (8, pairwise disjoint in files; none is Lean work, as the window
requires): `315-scout-nearmiss` (read-only), `316-audit-workflows` (read-only),
`317-port-wiki-hier-thm11` (owns `wiki/articles/hierarchical-two-point.md`, its record,
`wiki/tags.json`, `wiki/tests/tags.test.mjs`, `wiki/migration-baseline.json`),
`318-wiki-generator` (generator sources and new tests under `wiki/`, `wiki/README.md`;
explicitly not the files of 317), `319-audit-driven-ode-I421` (read-only: is Lemma I.4.21
proved as stated by `Analysis/DrivenODE.lean`? binder table against arXiv:2508.18807v1),
`322-wiki-proof-uses-a` (`proofUses` in `wiki/records/<a-l>*.json` except the 12 frozen
articles: records prerequisites of the 256 unproved assertions that have none, so they can
reach the frontier; a `-b` package for m-z follows), `323-wiki-style` (`wiki/STYLE.md`),
`324-scout-wiki-math` (read-only: exact texts for critic reports M1 FCU7, M3 erratum tags,
M4 L82Q's BK).
Claimed: `001-mig-rowsum`, `311-scout-defs`, `313-audit-d16-tags`, `314-scout-d33-next`.
Held: `HOLD-190-lrp-first-moment-b`, `HOLD-200-nm-bond-core`, `HOLD-210-lrp-I41-mt`,
`HOLD-220-lrp-spatial-russo-a`, `HOLD-230-lrp-levy-measures`, `HOLD-240-nm-probability`,
`HOLD-320-hier-restricted-susc` (H7), `HOLD-330-hier-thm11` (H8, new: after H7 merges and
the window closes), `HOLD-310-scout-lrnorm` (window); `HOLD-audit-nm-bond-core`,
`HOLD-audit-nm-probability` (after their targets); `HOLD-fix-nm-longrange` (after the
migrations); `HOLD-mig-headers`, `HOLD-mig-linters` (window steps 2-3).
Ownership conflict to watch when the window closes: the task board's `tasks/open/` lists
the HOLD prover packages too; whichever lane takes one moves its task file to
`tasks/claimed/` (only once `task-board` has merged).

Next packages to brief after the window: H7 and H8 are briefed; then H9
(`/home/user/reports/hier-map.md` §(c)); the J98J Lean tag; D-33 packages from
`scout-d33-next` (next by dependency: 8 after 5, 12 after 10, 14 after 13); near-misses
from `scout-nearmiss`; definition packages from `scout-defs`; salvage tier 2 (Q-211,
Q-195, Q-194). Ruling 8: the model article (a flagship one, coordinator's choice:
`hierarchical-two-point`) after `wiki-generator`; ruling 9b: mirror the queue in
`tasks/open/` each round once `task-board` merges.

## For ARCHITECT

- **Pull requests to `main`.** Ruling 10(1) authorises a pull request from the integration
  branch to `main` after each fully gated batch, but this coordinator's launch instructions
  say "never main, no PRs/issues", and COORDINATOR.md still quotes ruling 5. Not opened;
  `main` (`1df822a`) lacks everything since. Please align the launcher and COORDINATOR.md
  with ruling 10, or confirm ruling 5 stands. (The kernel replay is also due before the
  first such pull request.) The fourth coordinator's launch instructions again said "never
  main, no PRs/issues"; again not opened.
- **Auto-merge evidence** (from `automerge-workflow`): kernel replay is not required for a
  proof-only auto-merge. Coordinator intends fix A (kernel-replay on every PR, required by
  auto-merge) after `audit-workflows`; object if the gate alone should suffice.
- **Migration window reading.** This round kept read-only scouts, audits and the critic
  startable during the window (they cannot conflict with a migration); only Lean briefs
  are held. Object if the window must hold everything.
- `audit-wiki-hier-thm11` disclosed that it read the author's report before its verdict.
  Its J98J approval is treated as not fresh; the carried-over J98J gets a fresh audit
  before merge.
- `lrp-driven-ode` strengthened Lemma I.4.21's machinery by dropping the `f > 0` premise
  (unused by the proof). Recorded as proof-only; I.4.21 is not claimed proved until an
  auditor compares the remaining hypotheses with the paper.
- Open under D-35: the long-range norm (structure versus type synonym); `scout-lrnorm`
  prepares it after the window.
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
- Coming for your approval (rulings 7, 8): the draft `wiki/STYLE.md` and one restructured
  model article (`hierarchical-two-point`), after the critic's general critique.

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
