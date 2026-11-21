# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~23:15 UTC, end of coordinator round 15
(new series). Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); round 14's STATUS is in git
history at `13418dc`. A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) and
`/home/user/reports/ACTIVE.md` (read it instead of RULINGS.md, ruling 20e). Round cap: 60 tool calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `c26219e`** (pushed). On top: this
  STATUS/FRONTIER/INTERFACE_CHANGES commit (docs only, gate-equivalent). **Next batch: `scripts/integrate.sh <tip> <branches>`.**
- **Round 15 batch** (log `/home/user/reports/integrate-round15.log`, gate log `.lake/integrate/gate-20261121-230410-2.log`):
  `scripts/integrate.sh 5a9277c` (5a9277c = announcement of the BRW/EKDO definitions in `docs/INTERFACE_CHANGES.md`) + 8
  branches; 7 merged: `frontier-ultrametric-sweep-rebased` (proof-only, ESZG lemmas), `fix-nm-cutoff-localization` (32GP),
  `frontier-finite-triangle` (R2Y7), `frontier-ghost-derivative` (J2TE), `p-b-L9YJ` (L9YJ, XA7C), `frontier-brw-first-moment`
  (CYYG, 94E7 + BRW defs), `p-b-CUE4-fix` (CUE4, N0HM, TIKW). Result: "== gate passed on c26219e". Attempt 1 failed only on
  `p-a-EKDO-fix` (last branch, dropped): `Tags/HierarchicalComparison.lean:54: unexpected token 'open'` (the auditor's edit put
  a docstring before `open Classical in`). Repaired (syntax only) on `work/p-a-EKDO-fix2` @ `6fc5467`, unbuilt.
- **Kernel replay:** last passed at `a747905`; next after the tenth batch since then (about round 16).
- **GitHub (23:03):** `main` = `ae4eb08` (unchanged). Outside heads unchanged: PR #2 `630d985`, `work/hierarchical-two-point-paper`
  `be2b9df`, PR #3 `b1db272`, PR #4 `6867e43` (closed), PR #5 `1b29f93` (reviewed `docs/reviews/pr-5.md`; waits for Tom, 18b).
  **Actions:** CI `29c7c4b`/`c5e5abb` cancelled (concurrency), `13418dc` in progress; Automerge skipped. No failing workflow.

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
```

## Progress (D-35 measure)

Manifest at `c26219e`: **353 proved, 1 statement-only, 1,049 unformalised, of 1,403** (+10: 32GP, R2Y7, J2TE, L9YJ, XA7C,
CYYG, 94E7, CUE4, N0HM, TIKW; 10 tagged statements audited and merged). `docs/FRONTIER.md` regenerated at `c26219e` (277 ready).
Agents started in round 15 (claims seen): audit 4 (031-034, all finished),
tooling 1 (`tooling-integrate-culprit`), prover 2 (408, 409); outside launcher new `tag-26TT`, `tag-R1HO`. Provers 401, 405, 406,
407 finished. Coordinator round 15: 1 batch (1 integrate run, 2 attempts), ~45 tool calls.

## Finished, not merged — NEXT BATCH (merge these first)

Ready on audited APPROVE (branch @ sha):
- `work/p-a-EKDO-fix2` @ `6fc5467` (EKDO; definitions already under "Announced" in `INTERFACE_CHANGES.md`: move to "Merged").
  Put it LAST in the batch (unbuilt).
- `work/p-b-AFJX-fix` @ `908b023` (AFJX, ICQP; auditor's one exact edit of `audit-r14-outside-b` applied verbatim on `d9af67c`,
  unbuilt) and `work/p-a-VI3Y` @ `1f18a8d` (VI3Y, 12 new defs; APPROVE): **announce both packages' definitions first.**
- `work/frontier-lazy-walk-thresholds` @ `69bc20d` (E9BP; `audit-frontier-lazy-walk-thresholds` APPROVE).
- `work/frontier-section-comparison` @ `806f5bd` (9GXY, defs `SamplingTree`, `law`: announce) and
  `work/frontier-priority-exploration` @ `bd1dd76` (28UY, PWBU; its diff edits `docs/INTERFACE_CHANGES.md`: integrate.sh will
  skip it on conflict, so merge it by hand keeping both entries, or put its entry into your announcement commit and resolve):
  `audit-r14-frontier-b` APPROVE.
- 5PBL: merge **commit `4d5fea6`** (not the branch tip: the outside launcher keeps stacking commits on `work/p-b-5PBL`):
  `git branch work/p-b-5PBL-a 4d5fea6` and merge that; `audit-p-b-5PBL` APPROVE (5PBL, no new defs).
Audit queued (round 15): `frontier-dfs-pivot` (`263cc67`, KRU2, 5 new defs) + `frontier-trivalent-count` (`86fb115`, SO5J,
6 new defs) -> `036`; `frontier-invariant-weight-test` (`f6b9825`, G3HT) + `frontier-optimized-cluster-tail` (`c1bcee7`, 4A0G),
proof-complete, no defs -> `037`; DTYB (`c844bff`) + R1HO (`bbc0d54`) on `work/p-b-5PBL` -> `038`.
Superseded, never merge: `work/frontier-maximal-martingale`, `work/p-a-655W`, `work/p-a-GPDF`, `work/p-b-CUE4`, `work/p-a-EKDO`,
`work/p-a-EKDO-fix`, `work/p-b-AFJX`, `work/frontier-ultrametric-sweep` (branched from a transient merge).

## In flight (claims without done at 23:10)

Prover: `frontier-lrp-green-bubble` (408), `frontier-saw-generating` (409). Lane B: `tooling-integrate-culprit` (035).
Outside-launcher `tag-*` dirs (29, many stale; recent: 26TT, R1HO, DTYB, 5PBL). Treat outside output as interface. They work in
`hierarchical-runaway`, `spatial-convolution-asymptotics`, `size-biased-laws`, `adaptive-three-point`, `connection-kernels`,
`regular-variation`, `hierarchical-block-coalescent`, `higher-correlation`: keep our briefs out.

## Queue (`/home/user/reports/queue/`)

Startable at 23:12: lane B (3): audits `036-audit-r15-frontier-a`, `037-audit-r15-frontier-b`, `038-audit-p-b-5PBL-b`.
Prover (13): `411-frontier-three-part-multigraph` (L3HA), `412-frontier-joint-cut-witnesses` (RIH3), `413-frontier-susceptibility-level`
(6JZB), `414-frontier-window-mass-moments` (YN7V), `415-frontier-ghost-binary-tree` (4QV6), `416-frontier-root-visit-tails` (Y2C3),
`417-frontier-marked-volume-moments` (6AEH), `418-frontier-lazy-return-kernel` (KGNK), new `419-frontier-extinction-fixed-point`
(8TFY), `420-frontier-nonbacktracking-recurrence` (0MK8), `421-frontier-even-kernel-reciprocal` (84XD), `422-frontier-ultrametric-exchange`
(ESZG: spanning-tree exchange on top of merged sweep lemmas), `423-frontier-peierls-nontriviality` (NUJY).
Held: `HOLD-205`, `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371` (ruling 18b); `HOLD-410` (DTYB: done by the outside launcher,
under audit `038`; delete if `038` approves).
Next to brief: `7IVI` (needs a Poisson-mark process definition: interface), killed-Green notion for 331W, `7C2W`, `HATE`
(177 dependents), `GSLG`, `J1LW`, `RIRJ`/`EJHT`, `HJAT`, `X57A`, then the next frontier tags in `docs/FRONTIER.md` at `c26219e`.
`rg` the queue, the finished list and the `tag-*` claims for a tag before briefing it. Startable = no `claims/<id>`.

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL, PR #5: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (29): another launcher feeds workers with no brief in `queue/`, and it now stacks unrelated tags
  on one branch (`work/p-b-5PBL`: 5PBL, DTYB, R1HO) and duplicates our briefs (DTYB = our 410). We audit by exact commit.
  D-34 question still open: the launcher's brief source; recommended: it takes briefs from `queue/` or one branch per tag.
- **One batch per round** is the throughput limit: round 15 merged 7; at round end 7 more packages are audited and ready and
  4 more are under audit. Proposal (repeated): allow a second batch when the first passed and fewer than 40 calls were used.
- `integrate.sh` drops the last branch on failure: tooling brief `035-tooling-integrate-culprit` (claimed) adds culprit
  detection and refuses branches cut from transient merges (tests, no agent audit per ruling 10).
- CI on the integration branch rarely completes (newer pushes cancel it): leave it (gate + replay are the boundary) [recommended].
- Older open items: STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip's last gate passed at `c26219e` (replay pending
  its schedule). `main` lacks everything after `ae4eb08`. PRs #3 and #4 were closed without merge: if that was a decision
  against merging, please say so in RULINGS.md.
- **PR #5** (outside contributor, `lrp-I41-mt`): reviewed, `docs/reviews/pr-5.md`, APPROVE WITH CHANGES (3 small changes).
  It is the held port package of ruling 18b (our `HOLD-210`); its CI awaits your first-contributor approval. Should it be
  accepted despite the long-range hold?
- Long-range collaboration (ruling 18): basis for the joint review in `tasks/areas/long-range.md` and
  `docs/reports/long-range-concordance.md`; please confirm the licence notices in `third_party/critical-lrp/`.
- Issue #1 can be closed (fixed on `main`). Older questions: STATUS_LOG.md "For Tom".

## Lessons

- Apply an auditor's exact edits on a new branch `work/<id>-fix` from the audited sha and merge that branch; an edit that adds
  a docstring can land before `open ... in` and break parsing (EKDO): eyeball the edited region before batching.
- Outside-launcher branches move: record the audited sha and merge that commit (via a fresh branch name), never the tip.
- Audits can finish within minutes of queueing: re-list `done/` just before writing STATUS.
- `integrate.sh` runs under `setsid`; wait on `pgrep -f "scripts/integ[r]ate.sh"` (the bracket keeps the loop from matching itself).
- If integrate.sh's first attempt fails, read the gate log tail at once; if the culprit is not the last branch, kill it
  (`pkill -f 'scripts/integrate.sh <base>'`, then the gate and its AxiomAudit), `git reset --hard <base>` locally, fix or drop
  the culprit, re-run.
- New packages can clash on lemma names with merged files (`environment already contains ...`): rename in a `-fix` branch.
- A Prop-valued tagged `def` trips D-35 check (i) wherever it is assumed: tag a characterisation theorem (`:= Iff.rfl`).
- Workers branch from the newest tip, possibly a transient integrate merge: diff against `git merge-base`, and cherry-pick
  their own commits onto the gated tip when the base was never pushed.
- Grep the finished list's tags against the integration branch before every batch (duplicate tags, e.g. 7YNX).
- Older lessons: STATUS_LOG.md "Lessons".
