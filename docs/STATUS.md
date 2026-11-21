# Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026,
03:45 UTC, at the end of coordinator round 2 (third coordinator). A coordinator with no
memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) (the procedure for one
round), [COORDINATION.md](COORDINATION.md) (worker rules), [DECISIONS.md](DECISIONS.md)
(D-34, D-35, D-36, D-37) and `/home/user/reports/RULINGS.md` (container-local rulings 1-10;
obey them).

## Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. Pushed:
  `origin/claude/zen-lovelace-rvlcw2` = the commit of this STATUS file, whose parent
  **`9314239`** is the last gated commit. lrp: `5a2943b` (unchanged this round).
- **Last gate passed: `9314239`** (`scripts/gate.sh 7316ae9`): build (3,922 jobs), axiom
  audit of 5,954 constants (only `propext`, `Classical.choice`, `Quot.sound`), import
  closure of 329 modules, forbidden scan, classifier tests, extract, D-35 checks. The
  classifier reported INTERFACE (`tag` tokens in `Models/BinaryTreeCatalan.lean` and the
  other attach-models files): these are exactly the 33 tags approved by
  `audit-attach-models-a/b`. Earlier green this round: `7316ae9` (base `40549b0`,
  proof-only), `40549b0` (base `4cb4679`, proof-only); predecessor's `4cb4679`, `e12b2f6`,
  `fa0dc2b`. Local verification, not CI.
- Kernel replay (`scripts/kernel_replay.sh`) last passed on the baseline `4c72765`. Due
  before the next milestone report; run `scripts/kernel_replay.sh 6` when no build runs.
- `main` (`1df822a`) is an ancestor of the tip and lacks every commit since; no pull
  request to `main` has been opened (see "For ARCHITECT", first item).

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

Manifest from the `9314239` extract: **263 assertions proved**, 5 statement-only, 1,133
unformalised, of 1,401 (start of round: 231 / 4 / 1,166). 268 distinct tags in `PercLib/`
(was 235). Tagged statements audited and merged this round: **33** (attach-models: 23 of
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

Round 1 and earlier: see `git log --merges` (tooling and gate scripts, D-35 checks,
hierarchical H0-H4 and H6, salvage, D-33 ports, link tags, `nm-analysis`, `d35-binders`).

## Finished, not merged

- `work/pub-attrib` (93aaac3, on top of `work/pub-move` merged with `4cb4679`): ruling 6a
  done (56 draft-original articles credited "T. Hutchcroft, book in preparation"; no
  re-transform needed, lrp `wiki/` unchanged since 1fe07bc). **Waits for
  `audit-pub-attrib` (claimed)**; on approval (ruling 6c) merge into the tip (expect only
  the `wiki/` tree, check `git diff --stat`), gate, push. Irreversible; any doubtful
  passage is withheld and listed "For Tom". After it: `lrp/wiki` frozen (6d), release
  `HOLD-port-wiki-hier-thm11`, `HOLD-wiki-generator`, `HOLD-wiki-style`.
- `work/ci-workflow` (560bd59): CI workflow and `scripts/ci_*.sh`; never run on Actions.
  Waits for `automerge-workflow` (claimed) and then `HOLD-audit-workflows` (ruling 10(2):
  fresh audit for injection and privilege before reaching `main`).
- `work/contrib-docs` (705ac8c): `AGENTS.md`, `CONTRIBUTING.md`, issue and PR templates; no
  private paths (checked by grep). Merge **together with the workflows** after their audit,
  so the integration branch never describes CI or auto-merge that is not present (D-10).
- `work/frontier-doc` (460df3e): `scripts/frontier.py`, tests, `docs/FRONTIER.md`; finished
  at the end of the round, report `/home/user/reports/frontier-doc.md` not yet read. Next
  round: read, run `python3 scripts/test_frontier.py`, merge on the gate (non-Lean).
- `work/nm-longrange` (e4e9b59; ZH13, R01V): fix brief `HOLD-fix-nm-longrange`, amended
  this round with audit b's step 2 (one pair of `Sym2` names `…_of_ne`; R01V wrapper in
  `Models/Tags/TranslationInvariant.lean`; exactly one R01V tag; row sums as migrated).
  Release it after the migrations; then a fresh re-audit of R01V.
- lrp `work/wiki-hier-thm11` (a795d41) + `/home/user/reports/wiki-hier-thm11-baseline.patch`:
  not merged in lrp because the wiki moves to `perclib` (ruling 6d); carried over by
  `HOLD-port-wiki-hier-thm11` (adds 7AER to J98J `proof_uses`), then a fresh audit of J98J,
  then the J98J Lean tag on `HierarchicalTwoPointAveraged` (interface, with audit).
- `work/pub-move` (c442b2f): superseded by `work/pub-attrib`; remove its worktree after
  pub-attrib merges.

## In flight

Claims without a done marker at 03:45: `automerge-workflow`, `task-board`,
`audit-pub-attrib`, `critic-general`. Worktrees are `/home/user/wt/<id>`; claims in
`/home/user/reports/claims/`. The container restarted at 03:18; claims interrupted then
were re-taken by new workers (several reports mention resuming uncommitted work).

## Migration window: OPEN (since 03:42, tip `9314239`)

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
Startable at 03:45: `001-mig-rowsum`, `309-critic-general` (just claimed), `311-scout-defs`
(definition proposals from audits: self-avoiding count, k-ary tree graph, restricted
connection, boundary susceptibility, hierarchical level, `IsCut`, `RegularlyVarying.const_mul`),
`313-audit-d16-tags` (PVA8, MQNP, LF50, 6YYS, L82Q), `314-scout-d33-next` (status of the 32
D-33 packages, draft briefs for those with merged prerequisites), `315-scout-nearmiss`
(draft briefs for near-miss assertions). Fewer than 8 startable by design during the window.
Held: `HOLD-190-lrp-first-moment-b`, `HOLD-200-nm-bond-core`, `HOLD-210-lrp-I41-mt`,
`HOLD-220-lrp-spatial-russo-a`, `HOLD-230-lrp-levy-measures`, `HOLD-240-nm-probability`,
`HOLD-320-hier-restricted-susc` (H7), `HOLD-310-scout-lrnorm` (window);
`HOLD-audit-nm-bond-core`, `HOLD-audit-nm-probability` (after their targets);
`HOLD-audit-workflows` (after `automerge-workflow`); `HOLD-fix-nm-longrange` (after the
migrations); `HOLD-mig-headers`, `HOLD-mig-linters` (window steps 2-3);
`HOLD-port-wiki-hier-thm11`, `HOLD-wiki-generator`, `HOLD-wiki-style` (after pub-attrib
merges; wiki-style also after `critic-general`).

Next packages to brief after the window: H7 is briefed; then H8 Theorem 1.1, H9
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
  first such pull request.)
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

- Publishing the wiki: answered by ruling 6 ("published attributed to the book draft").
  The attribution pass is done on `work/pub-attrib`; the independent check of ruling 6b is
  running. Nothing is pushed until it approves.
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
- **Removing worktrees:** only if `done/<id>` exists and the branch is an ancestor of the
  tip (a fresh branch is trivially an ancestor before its first commit).
