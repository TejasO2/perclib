# Status

Handoff for the coordinator (LEAD role of D-34). Updated 22 November 2026, ~02:50 UTC, end of coordinator round 1 of 22 Nov
(after round 16, whose STATUS was never written: its batch is recorded here). Older history: [STATUS_LOG.md](STATUS_LOG.md)
(do not read by default); round 15's STATUS is in git history at `f6536a5`. A coordinator with no memory resumes from this
file, [COORDINATOR.md](COORDINATOR.md) and `/home/user/reports/ACTIVE.md` (read it instead of RULINGS.md). Round cap: 60 calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `d5dcd74`** (pushed). On top: this
  STATUS/FRONTIER/INTERFACE_CHANGES commit (docs only). **Next batch: `scripts/integrate.sh <tip> <branches>`.**
- `scripts/integrate.sh` now drops the culprit branch (parses `error:` and D-35 `FAIL` lines) and refuses branches cut from
  unpushed transient merges (merged this round, `work/tooling-integrate-culprit`, 13 tests pass). So **push before a batch**
  whose branches were cut from local-only commits. It still does its trial merges on the checked-out branch.
- **Round 16 batch** (predecessor; log `/home/user/reports/integrate-round16.log`): gate passed on `28c5f0a`; merged
  `frontier-lazy-walk-thresholds` (E9BP), `p-b-5PBL-a` (5PBL), `frontier-section-comparison` (9GXY), `frontier-priority-exploration`
  (28UY, PWBU), `p-a-VI3Y` (VI3Y), `p-b-AFJX-fix` (AFJX, ICQP), `frontier-lrp-green-bubble` (proof-only); then `c639ada` merged
  `origin/main` (PR #6). `p-a-EKDO-fix2` dropped (D-35 (iv) read `L-1` in a docstring as a label).
- **This round, batch A** (log `integrate-round17.log`, gate log `.lake/integrate/gate-20261122-022658-1.log`):
  `scripts/integrate.sh 865796a` + 5 branches, all merged, "== gate passed on 1f14e57": `frontier-dfs-pivot` (KRU2, 5 defs),
  `frontier-invariant-weight-test` (G3HT), `frontier-optimized-cluster-tail` (4A0G), `p-b-5PBL-b` = `bbc0d54` (DTYB, R1HO),
  `p-a-EKDO-fix3` @ `0cde16d` (EKDO; `L - 1` header repair). Before it: `3bcaf8e` merged `origin/main` (`45309ab`, PR #7),
  `e31bc92` merged the tooling branch, `865796a` announced the KRU2 definitions.
- **Batch B** (log `integrate-round17b.log`, gate log `.lake/integrate/gate-20261122-023635-1.log`): `scripts/integrate.sh 3b28de3`
  + 4 branches, all merged, "== gate passed on d5dcd74": `frontier-joint-cut-witnesses-rebased` @ `402ceee` (RIH3; cherry-pick of
  `699d3f0`, which was cut from transient `823b631`), `frontier-saw-generating` (C69U), `p-a-3NBK` (3NBK, OCZT; the audit's one
  change was the import lines, added by the closure step), `frontier-trivalent-count-fix` @ `d65cae9` (SO5J; audit edits verbatim,
  proof term adjusted only, statement as the audit wrote it).
- `fd30085` (wiki tooling, not Lean): `wiki/scripts/check-articles.mjs` retries the shallow base-commit fetch. Cause: CI `wiki`
  job on `main` `45309ab` (run 44960839484) failed in `pages-site.test.mjs` with "shallow file has changed since we read it"
  (parallel test files fetching at once). Syntax-checked only: local wiki tests need `npm ci` (no `node_modules`); CI will tell.
- **Kernel replay:** last passed at `a747905`; batches since then: about 12. **Due now**: run it next round on `d5dcd74` (or
  later gated tip) per COORDINATOR.md, niced, batch size 2, own worktree.
- **GitHub (02:30):** `main` = `45309ab` (PR #7 merged by Tom at 23:14). PRs #6, #7 merged; PR #5 (`yujinhkim`) closed unmerged.
  No open PRs; outside heads unchanged (`work/lace-foundations` = PR #2 `630d985`, `work/hierarchical-two-point-paper` `be2b9df`).
  **Actions:** CI on `c639ada` success; CI on `main` `45309ab` failure (wiki job, flake above); Automerge skipped.

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <tip> work/<a> work/<b> ... > /home/user/reports/integrate-roundN.log 2>&1 < /dev/null &
timeout 590 bash -c 'until ! pgrep -f "scripts/integ[r]ate.sh" >/dev/null; do sleep 30; done'; tail -7 /home/user/reports/integrate-roundN.log
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>   # auditor's JSON, on a new branch work/<id>-fix from the audited sha
lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
rm -f scripts/__pycache__/frontier.*.pyc; python3 scripts/check_tasks.py
```

## Progress (D-35 measure)

Manifest at `d5dcd74`: **372 proved, 1 statement-only, 1,030 unformalised, of 1,403** (+19 since `c26219e`: round 16 E9BP, 5PBL,
9GXY, 28UY, PWBU, VI3Y, AFJX, ICQP; this round KRU2, G3HT, 4A0G, DTYB, R1HO, EKDO, RIH3, C69U, 3NBK, OCZT, SO5J; 19 tagged
statements audited and merged). `docs/FRONTIER.md` regenerated at `d5dcd74`. Tasks board: CUE4 and 4A0G tasks moved to
`tasks/done/` (18 open; `check_tasks.py` flags one more as possibly done): **board below 20 open, restock needed** (ruling 19).
Agents started this round (claims seen): audit 1 (`audit-r16-batch`, finished), fix 1 (`fix-frontier-trivalent-count`, finished),
prover 3 self-directed (`frontier-three-part-multigraph` finished, `frontier-ghost-binary-tree`, `frontier-window-mass-moments`);
lane-B `fix-ci-cancelled-push-run` finished. Coordinator: 2 batches, 2 integrate runs, 0 failures, ~45 tool calls.

## Finished, not merged

- `work/frontier-three-part-multigraph` @ `2d86afa` (L3HA, no new defs) and `work/fix-ci-cancelled-push-run` @ `dfdcdca`
  (`.github/workflows/ci.yml`: cancelled push run no longer reads as a failed gate): **audit queued, `041-audit-r17-batch`**.
  Merge both on APPROVE (both based on `c639ada`, pushed).
Superseded, never merge: `work/frontier-maximal-martingale`, `work/p-a-655W`, `work/p-a-GPDF`, `work/p-b-CUE4`, `work/p-a-EKDO`,
`work/p-a-EKDO-fix`, `work/p-a-EKDO-fix2`, `work/p-b-AFJX`, `work/frontier-ultrametric-sweep`, `work/frontier-joint-cut-witnesses`
(use `-rebased`), `work/frontier-trivalent-count` (use `-fix`), `work/p-b-5PBL` tip (outside launcher stacks commits on it).

## In flight (claims without done at 02:45)

Prover (self-directed, PROVER-CHARTER): `frontier-ghost-binary-tree` (415), `frontier-window-mass-moments` (414). Lane B: none
claimed; `041-audit-r17-batch` queued. Outside-launcher `tag-*` dirs: ~33, all stale since 21 Nov 23:17 (no new branches).

## Queue (`/home/user/reports/queue/`)

Startable: lane B `041-audit-r17-batch`. Prover (9, drain only, ruling 21: write no more): `413` (6JZB), `416` (Y2C3), `417` (6AEH),
`418` (KGNK), `419` (8TFY), `420` (0MK8), `421` (84XD), `422` (ESZG), `423` (NUJY). Held: `HOLD-205/210/220/230/371` (ruling 18b);
`HOLD-410` (DTYB) is obsolete (DTYB merged): delete it (the sandbox refused `rm` this round). `audit-requests/` empty (all moved
to `audit-requests/done/`). Wiki/tooling slot: free (integrate-culprit merged; wiki-fetch fix applied directly).

## Held items

- Port packages (ruling 18b) until Tom reports the long-range agreement. `scout-defs-2` interface packages: not briefed.

## For ARCHITECT

- `/home/user/reports/hard/`: empty.
- Kernel replay is overdue (~12 batches since `a747905`); next coordinator should start it first thing (it does not block batches).
- Tasks board has 18 open tasks (< 20, ruling 19): a restock brief is the natural next use of the wiki/tooling slot. Recommended.
- `integrate.sh` still trial-merges on the checked-out branch (the tooling brief only added the transient-base refusal and culprit
  detection). Workers branching mid-batch can still pick up a transient merge (joint-cut did, from `823b631`). Second small
  tooling brief, or accept with the refusal as the safety net [recommended: accept].
- Unknown `tag-*` launcher: open D-34 question from round 15 (STATUS at `f6536a5`); outside branches stacking tags remain audited
  by exact commit.

## For Tom

- **Next pull request to `main` (ruling 22.1):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 —
  gate passed on `d5dcd74` (372 proved); last gate + kernel replay: `a747905`. **PR #8 opened** (head `c4e9a7e`); the merge call
  (PUT `/pulls/8/merge`) was refused by this session's permission layer, so it waits: Tom merges it, or a later coordinator
  whose permissions allow it (do not work around a refusal). After it merges, merge `origin/main` back.
- CI on `main` `45309ab` failed in the wiki job (shallow-fetch race in tests, not the library); fix `fd30085` rides on the next PR.
- PR #5 (`yujinhkim`, `lrp-I41-mt`) was closed without merge; review stays in `docs/reviews/pr-5.md`.
- Issue #1 can be closed (fixed on `main`). Older questions: STATUS_LOG.md "For Tom".

## Lessons

- A predecessor may merge and push without writing STATUS: compare `git log` against STATUS before trusting "Finished, not merged".
- `check_d35.py` (iv) treats `L-1` in a header docstring as a label: write `L - 1`.
- Audits and fixes finish within minutes: re-list `done/` after batch A and run batch B in the same round (rule allows it).
- Branches cut from an unpushed transient merge: cherry-pick their own commits onto the pushed tip (`-rebased`), audit that sha.
- Apply an auditor's exact edits on `work/<id>-fix` from the audited sha; eyeball edited regions (`open ... in` vs docstrings).
- Outside-launcher branches move: merge the audited commit via a fresh branch name, never the tip.
- Older lessons: STATUS_LOG.md "Lessons" and STATUS at `f6536a5`.
