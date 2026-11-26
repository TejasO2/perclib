# Status

Handoff for the coordinator (LEAD role of D-34). Updated 22 November 2026, ~03:40 UTC, end of coordinator round 3 of 22 Nov.
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); round 2 of 22 Nov is in git history at `cf11c55`.
A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) and `/home/user/reports/ACTIVE.md`
(read it instead of RULINGS.md). Round cap: 60 calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `28c8877`** (pushed). On top: this
  STATUS/FRONTIER/INTERFACE_CHANGES/tasks commit (docs only). **Next batch: `scripts/integrate.sh <tip> <branches>`.**
- Five batches this round, all gated with `scripts/integrate.sh` (logs `/home/user/reports/integrate-round19{,b,c,d,e}.log`):
  - A `cf11c55` -> **`6afaba2`**: `p-a-XMYD-fix` (= `d488be8` + audit-r18-a's 4 exact edits, verbatim, `8435f18`), `p-a-YY9S` @ `58d97b8`,
    `p-c-ZDVK` @ `32a2c5e` (audit-r18-a).
  - B -> **`ddb4e1a`**: fork intake `yujinhkim:work/yujin-cutoff-moment-prereqs` moved `39f24c2` -> `7d8ea3c` (1 commit, 1 file
    `Models/LongRange/TruncatedMoments.lean`, +1077, no tags/defs); gate "PROOF-ONLY ... no compiled interface change". PR #10 head.
  - C -> **`8fe99e9`**: `p-b-NCWZ` @ `928297e`, `p-b-26TT` @ `8ac714e`, `frontier-ghost-binary-tree` @ `8fa3f80` (audit-r18-b),
    `p-c-2DZD` @ `3abe41f`, `p-d-NW8B` @ `022fc7a`, `frontier-susceptibility-level` @ `58fc8b0` (audit-r18-c). All APPROVE.
  - D -> **`99b7770`**: `p-d-B2ZL` @ `9050fa1`, `frontier-window-mass-moments` @ `f1229cf`, `frontier-marked-volume-moments` @ `1722208`
    (audit-r18-d), `p-a-MDB8` @ `6d8b6da`, `p-b-TAB8` @ `de04c45`, `p-c-TC6Q` @ `146074c` (audit-r19-a). MDB8 change 1 (move the two
    defs to a Defs file) **waived** by the coordinator as the auditor allowed (precedent); follow-up for a future cleanup.
    Three branches dropped: the culprit was `p-d-H35T-fix` (the verbatim edit made `Tags/SummableDegree.lean:44` exceed 100 chars);
    integrate.sh did not parse "Some required targets logged failures: - <module>" and dropped from the end.
  - E -> **`28c8877`**: `p-d-H35T-fix` @ `38be95b` (= `bf00634` + audit-r19-b's I24D edit `4d1d650` + line wrap), `frontier-root-visit-tails`
    @ `a7066a4` (audit-r19-b), `wiki-cc-by-licence` @ `afc72f3` (ruling 23; wiki/docs, no new proof: merged on the gate, no agent audit).
- **Kernel replay:** the run on `4ca13cb` was OOM-killed at 242/486 (manifest extraction + worker builds). Restarted on `28c8877` in
  `/home/user/wt/kreplay-28c8877` (`nice -n 15 scripts/kernel_replay.sh 2`, log `/home/user/reports/replay-28c8877.log`, 538 modules).
  Last passed: `a747905`. Next coordinator: `tail -2` the log; record; restart if dead; remove the worktree when passed.
  Do not run manifest extraction while it runs if a worker build is also running.
- **GitHub (03:30):** `main` = `45309ab`. PR #8 (integration -> main) open, head now `28c8877`, not merged (waiting for a kernel replay).
  PR #9, #10 open (in the integration branch; close as merged with #8). PR #2 (`630d985`) and `work/hierarchical-two-point-paper`
  (`be2b9df`) unchanged. **Actions:** CI on the integration branch superseded by pushes (fine); CI on PR #10 head `7d8ea3c` is
  `action_required`: our approve call was refused by the permission layer (see For Tom). Automerge on `main` skipped.
- **Fork tips seen (ruling 24):** `lrp-I41-mt-updated` `e6cf6fe`, `work/yujin-cutoff-moment-prereqs` `7d8ea3c` (both merged).

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <tip> work/<a> work/<b> ... > /home/user/reports/integrate-roundN.log 2>&1 < /dev/null &
timeout 110 bash -c 'until ! pgrep -f "scripts/integ[r]ate.sh" >/dev/null; do sleep 20; done'; tail -4 /home/user/reports/integrate-roundN.log
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>   # auditor's JSON, on a new branch work/<id>-fix from the audited sha
lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json   # >2 min: background it
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
rm -f scripts/__pycache__/frontier.*.pyc; python3 scripts/check_tasks.py
```

## Progress (D-35 measure)

Manifest at `28c8877`: **409 proved, 1 statement-only, 993 unformalised, of 1,403** (+36 this round; 391 at `8fe99e9`).
Tagged statements audited and merged this round: 36 tags + 10 definitions (audits r18-a/b/c/d, r19-a/b). `docs/FRONTIER.md`
regenerated at `28c8877`. Tasks: `schur-product-kernels` (TAB8), `separating-pairs-tag` (GA03) moved to `tasks/done/`;
**15 open** (restock brief claimed). Agents started this round by kind (claims seen): audit 3 (`audit-r19-a`, `-b`, `-c`),
tooling 1 (`tasks-restock-r3`); provers self-directed (launcher `p-*` and queue 418-420). Coordinator: 5 batches, 1 gate failure
(culprit repaired, re-merged), ~48 tool calls.

## Finished, not merged (interface: merge each on its audit's APPROVE)

| Audit brief | Branch @ sha (base) | Tags / definitions |
|---|---|---|
| `047c-audit-r19-c` (claimed) | `p-a-F2G0` @ `eac1ecd` (`4ca13cb`); `p-c-F7SW` @ `b7f1c9f` (`4ca13cb`); `p-d-4SZ9` @ `6522d39` (`6afaba2`) | def `blockCorner`, F2G0; def `HasLogExponent`, F7SW, PHLF; defs `erdosRenyiWindow`, `homogeneousProfile`, 4SZ9, O0TO, A65C, X9N1 |
| `047d-audit-r19-d` | `frontier-lazy-return-kernel` @ `d3988df` (`8fe99e9`); `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (`8fe99e9`) | KGNK; 0MK8 + a `Finite` instance |

New definitions announced in `docs/INTERFACE_CHANGES.md` (round 3 entry). `frontier-extinction-fixed-point`: done, nothing to
write (8TFY already merged). Launcher branches (`p-*`) may move: merge the audited sha, never a later tip.
Superseded, never merge: `work/frontier-maximal-martingale`, `work/p-a-655W`, `work/p-a-GPDF`, `work/p-b-CUE4`, `work/p-a-EKDO`,
`work/p-a-EKDO-fix`, `work/p-a-EKDO-fix2`, `work/p-b-AFJX`, `work/frontier-ultrametric-sweep`, `work/frontier-joint-cut-witnesses`,
`work/frontier-trivalent-count`, `work/fix-ci-cancelled-push-run`, `work/p-b-5PBL` tip, `work/p-a-XMYD` (use `-fix`, merged),
`work/p-d-H35T` (use `-fix`, merged).

## In flight (claims without done at 03:35)

Lane B: `audit-r19-c`, `tasks-restock-r3` (the one wiki/tooling slot). Launcher `tag-*` claims: self-directed provers; their
hand-overs arrive in `/home/user/reports/audit-requests/` (empty now; handled ones in `audit-requests/done/`).

## Queue (`/home/user/reports/queue/`)

Startable: `047d-audit-r19-d` (lane B); prover drain only (ruling 21): `421`-`423` (3 unclaimed). The queue directory also holds
every consumed brief (claimed; never delete). Held: `HOLD-205/210/220/230/371` (ruling 18b).

## Held items

- Port packages (ruling 18b) until Tom reports the long-range agreement. `scout-defs-2` interface packages: not briefed.
- MDB8 follow-up (non-blocking, audit-r19-a A): move `ConvexOrder`/`UnifIntegrableAlong` to a Defs file; bridge to mathlib
  `UniformIntegrable`; `ConvexOrder.trans`. XMYD follow-up (audit-r18-a): `HierarchicalLayers.pairLevel` via `level`.

## For ARCHITECT

- `/home/user/reports/hard/`: empty.
- Tooling (next wiki/tooling slot after `tasks-restock-r3`): integrate.sh culprit detection misses lake's "Some required targets
  logged failures: - <Module>" list (it dropped two innocent branches this round), and trial merges still run on the main
  checkout. Recommend one tooling brief covering both.
- Coordinator worktree cleanup removes clean worktrees whose branch is an ancestor of the tip: this also catches a freshly created,
  still-empty worker worktree. None was in use this round (checked claims), but restrict cleanup to branches with a done marker.
- Prover queue: 3 unclaimed left; provers are self-directed under PROVER-CHARTER, so no action.

## For Tom

- **Pull request #8 to `main` (ruling 22.1):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 —
  gate passed on `28c8877` (409 proved, local verification, not CI); last gate + kernel replay: `a747905` (replay on `28c8877`
  running). Merging it also closes #9 and #10 as merged.
- **PR #10 CI** (`yujinhkim:work/yujin-cutoff-moment-prereqs` @ `7d8ea3c`, one Lean file, nothing under `.github/`/`scripts/`/pins):
  first-run approval needed; our API approve call was refused by the permission layer. Click "Approve and run" if you wish.
- **Wiki licence CC BY 4.0 (ruling 23) is now in the integration branch** (`wiki-cc-by-licence`; the legal-code file was not
  fetched, linked instead, as the ruling allows).
- Stray remote branch `work/fix-ci-cancelled-push-run-fix` (merged); delete when convenient. Issue #1 can be closed.
- Older questions: STATUS_LOG.md "For Tom".

## Lessons

- An auditor's verbatim exact edit can break the style linter (line > 100): check `awk 'length>100'` on edited lines (character
  count, not bytes) before integrating a `-fix` branch.
- When integrate.sh drops several branches with quick gate failures, read the first gate log's "logged failures" module and
  re-merge the innocent branches in a new batch.
- Manifest extraction plus worker builds OOM-killed the kernel replay: run extraction while no replay is running, or accept a restart.

- Something detached HEAD of the main checkout after batch B (reflog: "checkout: moving from claude/zen-lovelace-rvlcw2 to
  HEAD" at `4ca13cb`); check `git status -sb` before committing STATUS, and `git ls-remote` after pushing.
- Push only the integration branch: never `git push origin work/*` (a remote branch delete is then refused).
- A predecessor may merge and push without writing STATUS: compare `git log` against STATUS before trusting "Finished, not merged".
- Re-list `done/` after each batch: four branches finished during this round; batches take 4-8 minutes.
- The manifest extraction takes over 2 minutes: background it, then build_manifest.
- `check_d35.py` (iv) treats `L-1` in a header docstring as a label: write `L - 1`.
- Branches cut from an unpushed transient merge: cherry-pick their own commits onto the pushed tip (`-rebased`), audit that sha.
- Apply an auditor's exact edits on `work/<id>-fix` from the audited sha; eyeball edited regions.
- Older lessons: STATUS_LOG.md "Lessons" and STATUS at `f6536a5`.
