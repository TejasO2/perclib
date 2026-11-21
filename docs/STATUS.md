# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~23:15 UTC, end of coordinator round 14
(new series). Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); round 13's STATUS is in git
history at `c5e5abb`. A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) and
`/home/user/reports/ACTIVE.md` (read it instead of RULINGS.md, ruling 20e). Round cap: 60 tool calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `29c7c4b`** (pushed). On top: the docs-only
  merge of `work/review-pr-5` (`docs/reviews/pr-5.md`) and this STATUS/FRONTIER commit. **Next batch:
  `scripts/integrate.sh <tip after this commit> <branches>`** (the tip is gate-equivalent to `29c7c4b`: docs only).
- **Round 14 batch** (log `/home/user/reports/integrate-round14b.log`, gate log `.lake/integrate/gate-20261121-225154-1.log`):
  `scripts/integrate.sh 2aac9c2` + 9 branches, all merged on audited APPROVE: `frontier-fourth-moment` (I2YU),
  `frontier-discrete-entropy` (JR0J), `frontier-consistent-geodesics` (BN7Z), `frontier-predictable-swap` (Q3MP),
  `p-a-655W-fix` (655W, 7GDE; auditor's exact edit dropping the duplicate 7YNX tag, applied verbatim), `frontier-chemical-moments`
  (SBMG), `p-b-UDUU` (UDUU, NIAD), `wiki-cite-hier-two-point` (citations only; `npm test` 116/116 pass), `p-a-GPDF-fix` (GPDF
  tags + 5 new definitions announced in `docs/INTERFACE_CHANGES.md`; merge repair: duplicate lemma `mem_toFinset_level_ball`
  renamed `..._finset`, it clashed with `Models/HierarchicalTriangle.lean`). 6 closure imports. Result: "D-35 checks passed",
  "== gate passed on 29c7c4b".
- **First attempt failed** (`integrate-round14.log`, base `cefd507`, 10 branches): (1) the GPDF name clash; (2) `p-b-CUE4`
  fails D-35 check (i): `HasMassTransport.tsum_eq` has a binder whose type is the tagged def `HasMassTransport` (N0HM). I
  killed the run (it drops the *last* branch each attempt, not the culprit), reset locally, re-ran without CUE4.
- **Kernel replay:** last passed at `a747905`; next after the tenth batch since then (about round 16).
- **GitHub (22:55):** `main` = `ae4eb08` (unchanged). Outside heads unchanged: PR #2 `630d985`, `work/hierarchical-two-point-paper`
  `be2b9df`, PR #5 `1b29f93` (reviewed: `docs/reviews/pr-5.md`, APPROVE WITH CHANGES, 3 small changes; merge waits for Tom,
  ruling 18b). **Actions:** CI on `e0ae3ec`/`5c02c84`/`4312804` cancelled (concurrency), `c5e5abb` in progress; CI on PR #5
  `action_required`; Automerge skipped. No failing workflow. No GitHub write tool in this session.

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <last-gated> work/<a> work/<b> ... > /home/user/reports/integrate-roundN.log 2>&1 < /dev/null &
timeout 110 bash -c 'until ! pgrep -f "scripts/integ[r]ate.sh" >/dev/null; do sleep 20; done'; tail -4 /home/user/reports/integrate-roundN.log
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>   # auditor's JSON, on a new branch work/<id>-fix from the audited sha
lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
rm -f scripts/__pycache__/frontier.*.pyc
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm test; rm node_modules; rm -rf dist
```

## Progress (D-35 measure)

Manifest at `29c7c4b`: **343 proved, 1 statement-only, 1,059 unformalised, of 1,403** (+11: I2YU, JR0J, BN7Z, Q3MP, 655W,
7GDE, SBMG, UDUU, NIAD and the two GPDF-package tags; 11 tagged statements audited and merged). `docs/FRONTIER.md`
regenerated at `29c7c4b`. Agents started in round 14 (claims seen): audit 4 (026-029, all finished), fix 1 (030, finished),
prover 7 (400-406), review 1 (025, finished); outside launcher new `tag-AFJX`, `tag-VI3Y`, `tag-XA7C`. Coordinator round 14:
1 batch (2 integrate runs), ~52 tool calls.

## Finished, not merged — NEXT BATCH (all ready; merge these first)

Ready on audited APPROVE (branch @ sha):
- `work/frontier-brw-first-moment` @ `9d86f6a` (CYYG, 94E7 + new BRW definitions; `audit-frontier-brw-first-moment`):
  **announce its definitions in `docs/INTERFACE_CHANGES.md` before merging.**
- `work/fix-nm-cutoff-localization` @ `2dcd845` (32GP; re-audit `audit-nm-cutoff-localization-r2` APPROVE).
- `work/frontier-finite-triangle` @ `f7facb9` (R2Y7) and `work/frontier-ghost-derivative` @ `d95ab93` (J2TE): `audit-r14-frontier`.
- `work/p-b-L9YJ` @ `881adb3` (L9YJ, XA7C) and `work/p-a-EKDO-fix` @ `8beb4cd` (EKDO; auditor's 3 exact edits applied verbatim
  on `faf5aee`, unbuilt: gate checks it; EKDO-package definitions: announce first): `audit-r14-outside-batch`.
- `work/p-b-CUE4-fix` @ `6ff621a` (CUE4, N0HM, TIKW; tag N0HM moved to `hasMassTransport_iff ... := Iff.rfl` with the def body
  verbatim, checked by the coordinator: no re-audit). Its definitions are listed under "Announced" in `INTERFACE_CHANGES.md`:
  move them to "Merged" when it merges. The fixer flagged one pre-existing issue outside its files (see its report).
- `work/frontier-ultrametric-sweep-rebased` @ (tip of that branch; cherry-pick of `7e2a017`, `cb4b97b` onto `29c7c4b`):
  proof-only area lemmas (sweep lower bound) for ESZG; merge on the gate. **Never merge `work/frontier-ultrametric-sweep`**: it
  was branched from a transient integrate.sh merge (`e443a47`) and contains unaudited/unmerged CUE4. ESZG itself is not proved;
  missing lemma: spanning-tree exchange (report `authors/frontier-ultrametric-sweep.md`, "Missing lemmas").
Audit queued (round 14): `frontier-lazy-walk-thresholds` (`69bc20d`, E9BP) -> `032`; `p-b-AFJX` (`d9af67c`, AFJX, ICQP, new
defs) and `p-a-VI3Y` (`1f18a8d`, VI3Y, 12 new defs) -> `031`; `frontier-section-comparison` (`806f5bd`, 9GXY, defs
`SamplingTree`, `law`) and `frontier-priority-exploration` (`bd1dd76`, 28UY, PWBU; its diff edits `docs/INTERFACE_CHANGES.md`:
expect a conflict, resolve by keeping both entries) -> `033`.
Superseded, never merge: `work/frontier-maximal-martingale`, `work/p-a-655W`, `work/p-a-GPDF`, `work/p-b-CUE4`, `work/p-a-EKDO`,
`work/frontier-ultrametric-sweep` (use the `-fix`/`-rebased` branches).

## In flight (claims without done at 23:10)

Prover: `frontier-dfs-pivot` (401), `frontier-invariant-weight-test` (406), `frontier-optimized-cluster-tail` (407),
`frontier-trivalent-count` (405). Outside-launcher `tag-*` dirs (28; many stale). Treat outside output as interface. They work
in `hierarchical-runaway`, `spatial-convolution-asymptotics`, `size-biased-laws`, `adaptive-three-point`, `connection-kernels`,
`regular-variation`, `hierarchical-block-coalescent`, `higher-correlation`: keep our briefs out.

## Queue (`/home/user/reports/queue/`)

Startable at 23:10: lane B (3): audits `031-audit-r14-outside-b`, `032-audit-frontier-lazy-walk-thresholds`,
`033-audit-r14-frontier-b`. Prover (11): `408-frontier-lrp-green-bubble` (1POM), `409-frontier-saw-generating` (C69U),
`410-frontier-compounded-law-normalization` (DTYB), `411-frontier-three-part-multigraph` (L3HA), `412-frontier-joint-cut-witnesses`
(RIH3), new `413-frontier-susceptibility-level` (6JZB), `414-frontier-window-mass-moments` (YN7V), `415-frontier-ghost-binary-tree`
(4QV6), `416-frontier-root-visit-tails` (Y2C3), `417-frontier-marked-volume-moments` (6AEH), `418-frontier-lazy-return-kernel`
(KGNK). Held (ruling 18b): `HOLD-205`, `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371`.
Next to brief: `7IVI` (needs a Poisson-mark process definition: interface), killed-Green notion for 331W, `7C2W`, ESZG
(spanning-tree exchange lemma), then the next frontier tags in `docs/FRONTIER.md` at `29c7c4b`. `rg` the queue and the
finished list for a tag before briefing it. To start: the old queue files are kept after claim; startable = no `claims/<id>`.

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL, PR #5: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (28): another launcher feeds workers with no brief in `queue/`. We audit before merge. D-34
  question still open: the launcher's brief source, so that its targets do not duplicate ours.
- **One batch per round** is the throughput limit: round 14 merged 9; at round end 8 more packages are audited and ready
  (list above) and workers finish within minutes. Proposal (repeated): allow a second batch when the first passed and fewer
  than 40 calls were used.
- **`scripts/integrate.sh` drops the last branch on failure**, not the culprit: a failure caused by the first branch costs
  one 12 s attempt per branch and ends with almost nothing merged. Proposal: a tooling brief to bisect (or to parse the
  failing module/D-35 line and drop its branch). Also: workers branch from its transient merges (`ultrametric-sweep` did).
- CI on the integration branch rarely completes (newer pushes cancel it): leave it (gate + replay are the boundary) [recommended].
- Older open items: STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip's last gate passed at `29c7c4b` (replay pending
  its schedule). `main` lacks everything after `ae4eb08`. PRs #3 and #4 were closed without merge: if that was a decision
  against merging, please say so in RULINGS.md.
- **PR #5** (outside contributor, `lrp-I41-mt`): reviewed, `docs/reviews/pr-5.md`, APPROVE WITH CHANGES (3 small changes).
  It is the held port package of ruling 18b (our `HOLD-210`); its CI awaits your first-contributor approval. Should it be
  accepted despite the long-range hold?
- Long-range collaboration (ruling 18): basis for the joint review in `tasks/areas/long-range.md` and
  `docs/reports/long-range-concordance.md`; please confirm the licence notices in `third_party/critical-lrp/`.
- Issue #1 can be closed (fixed on `main`). Older questions: STATUS_LOG.md "For Tom".

## Lessons

- Apply an auditor's exact edits on a new branch `work/<id>-fix` from the audited sha and merge that branch.
- `integrate.sh` runs under `setsid`; wait on `pgrep -f "scripts/integ[r]ate.sh"` (the bracket keeps the wait loop from
  matching itself; a plain `pgrep -f scripts/gate.sh` loop matches its own command line and integrate.sh then refuses).
- If integrate.sh's first attempt fails, read the gate log tail at once; if the culprit is not the last branch, kill it
  (`pkill -f 'scripts/integrate.sh <base>'`, then the gate and its AxiomAudit), `git reset --hard <base>` locally, fix or drop
  the culprit, re-run.
- New packages can clash on lemma names with merged files (`environment already contains ...`): rename in a `-fix` branch.
- A Prop-valued tagged `def` trips D-35 check (i) wherever it is assumed: tag a characterisation theorem (`:= Iff.rfl`) instead.
  Tell provers this in definition briefs.
- Workers branch from the newest tip, possibly a transient integrate merge: diff against `git merge-base`, and cherry-pick
  their own commits onto the gated tip when the base was never pushed.
- Grep the finished list's tags against the integration branch before every batch (duplicate tags, e.g. 7YNX).
- Older lessons: STATUS_LOG.md "Lessons".
