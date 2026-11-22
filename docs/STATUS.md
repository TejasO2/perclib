# Status

Handoff for the coordinator (LEAD role of D-34). Updated 22 November 2026, ~03:15 UTC, end of coordinator round 2 of 22 Nov.
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); round 1 of 22 Nov is in git history at `cbffb2f`.
A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) and `/home/user/reports/ACTIVE.md`
(read it instead of RULINGS.md). Round cap: 60 calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `4ca13cb`** (pushed). On top: this
  STATUS/FRONTIER/INTERFACE_CHANGES/tasks commit (docs only). **Next batch: `scripts/integrate.sh <tip> <branches>`.**
- **Batch A** (log `/home/user/reports/integrate-round18.log`, gate log `.lake/integrate/gate-20261122-024615-1.log`):
  `scripts/integrate.sh cbffb2f` + 2 branches, both merged, "== gate passed on 831957d": `frontier-three-part-multigraph` @
  `2d86afa` (L3HA; `audit-r17-batch` A APPROVE), `fix-ci-cancelled-push-run-fix` @ `025be61` (= `dfdcdca` + the audit's one
  exact edit to `.github/workflows/ci.yml`, applied verbatim with `apply_exact_edits.py`; `audit-r17-batch` B APPROVE WITH CHANGES).
- **Batch B** (log `integrate-round18b.log`, gate log `.lake/integrate/gate-20261122-025046-1.log`): `scripts/integrate.sh 831957d
  work/yujin-cutoff-moment-prereqs`, "== gate passed on 4ca13cb", gate: "PROOF-ONLY change ... 4 Lean file(s), no compiled
  interface change". Fork intake (ruling 24): `yujinhkim:work/yujin-cutoff-moment-prereqs` @ `39f24c2` (7 commits, contains
  `lrp-I41-mt-updated` @ `e6cf6fe`), merged as a merge commit (authorship kept). Files: `Models/LongRange/{CutoffCorner,
  MassTransportI41,TruncatedMoments}.lean`, `docs/PORTED_FILES.md`. No tags, no definitions, no `sorry`/axiom; pr-5 changes:
  rebased onto main (1), PORTED_FILES registered (2), description = our PR (3). Listed in `tasks/areas/long-range.md`.
- **Kernel replay:** started this round on `4ca13cb` in `/home/user/wt/kreplay-4ca13cb` (`nice -n 15 scripts/kernel_replay.sh 2`,
  log `/home/user/reports/replay-4ca13cb.log`, 486 modules, ~8 done at 03:10). Last passed: `a747905`. Next coordinator: `tail -2`
  the log; record pass/fail; if it died (OOM), restart it there. Then remove the worktree.
- **GitHub (03:00):** `main` = `45309ab`. **PR #8** (integration -> main) open, head now `4ca13cb`, not merged (see For Tom).
  **PR #9** (`yujinhkim:lrp-I41-mt-updated`) and **PR #10** (`yujinhkim:work/yujin-cutoff-moment-prereqs`) opened by us (ruling 24);
  both are in the integration branch, so they close as merged when PR #8 merges. Open PR #2 (`tomhutchcroft`, lace) unchanged
  (`630d985`); `work/hierarchical-two-point-paper` `be2b9df` unchanged. **Actions:** CI on `cbffb2f` in progress at 02:47, then
  superseded by our pushes (cancellation is fine); Automerge on `main` skipped.
- **Fork tips seen (ruling 24):** `lrp-I41-mt-updated` `e6cf6fe`, `work/yujin-cutoff-moment-prereqs` `39f24c2` (both merged).
  A new or moved `work/yujin-*` tip is an intake.

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

Manifest at `4ca13cb`: **373 proved, 1 statement-only, 1,029 unformalised, of 1,403** (+1: L3HA; the fork intake is proof-only
support with no tags). `docs/FRONTIER.md` regenerated at `4ca13cb`. Tasks: `tree-shape-count` (SO5J) moved to `tasks/done/`;
**17 open (< 20, restock needed, ruling 19)**. Agents started this round by kind (claims seen): audit 1 (`audit-r18-a` claimed);
prover self-directed: `frontier-root-visit-tails` (in flight); finished since last round: provers `frontier-ghost-binary-tree`,
`frontier-susceptibility-level`, `frontier-window-mass-moments`, `frontier-marked-volume-moments`, and launcher hand-overs
`p-a-XMYD`, `p-a-YY9S`, `p-b-26TT`, `p-b-NCWZ`, `p-c-2DZD`, `p-c-ZDVK`, `p-d-NW8B`, `p-d-B2ZL`; audit `audit-r17-batch`.
Coordinator: 2 batches, 0 gate failures, ~38 tool calls.

## Finished, not merged (all interface: tagged statements; merge each on its audit's APPROVE)

| Audit brief | Branch @ sha (base) | Tags / definitions |
|---|---|---|
| `042-audit-r18-a` (claimed) | `p-a-XMYD` @ `d488be8` (`e31bc92`); `p-a-YY9S` @ `58d97b8` (`fd30085`); `p-c-ZDVK` @ `32a2c5e` (`e31bc92`) | XMYD, T6SL, JCRB; YY9S; ZDVK |
| `043-audit-r18-b` | `p-b-NCWZ` @ `928297e` (`fd30085`); `p-b-26TT` @ `8ac714e` (`c26219e`); `frontier-ghost-binary-tree` @ `8fa3f80` (`d5dcd74`) | def `generationSize`, 8TFY, UKY4, BFM4; 26TT, 7LLO; 4QV6 |
| `044-audit-r18-c` | `p-c-2DZD` @ `3abe41f` (`fd30085`); `p-d-NW8B` @ `022fc7a` (`c639ada`); `frontier-susceptibility-level` @ `58fc8b0` (`28c5f0a`) | 2DZD, def `truncatedChi` (MTJT); NW8B, 96A2, C2YT; 6JZB |
| `045-audit-r18-d` | `p-d-B2ZL` @ `9050fa1` (`d5dcd74`); `frontier-window-mass-moments` @ `f1229cf` (`1f14e57`); `frontier-marked-volume-moments` @ `1722208` (`cbffb2f`) | defs `pairBoundary`, `SeparatesPairs`, `openDegree`, `incidentCount`; B2ZL, PMHN, H4OA, GA03; YN7V; 6AEH |

All bases are on the pushed integration branch. New definitions are announced in `docs/INTERFACE_CHANGES.md` (round 2 entry).
Launcher branches (`p-*`) may move: merge the audited sha (fresh branch name if the tip moved), never a later tip.
Superseded, never merge: `work/frontier-maximal-martingale`, `work/p-a-655W`, `work/p-a-GPDF`, `work/p-b-CUE4`, `work/p-a-EKDO`,
`work/p-a-EKDO-fix`, `work/p-a-EKDO-fix2`, `work/p-b-AFJX`, `work/frontier-ultrametric-sweep`, `work/frontier-joint-cut-witnesses`,
`work/frontier-trivalent-count`, `work/fix-ci-cancelled-push-run` (use `-fix`, merged), `work/p-b-5PBL` tip.

## In flight (claims without done at 03:10)

Prover (self-directed): `frontier-root-visit-tails` (416). Lane B: `audit-r18-a`. Outside-launcher `tag-*` dirs: stale.

## Queue (`/home/user/reports/queue/`)

Startable lane B: `043-audit-r18-b`, `044-audit-r18-c`, `045-audit-r18-d`, `046-wiki-cc-by-licence` (the one wiki/tooling slot:
ruling 23 licence brief, which ruling 23 puts ahead of other wiki work). Prover (drain only, ruling 21): `418`-`423` (6 unclaimed).
Held: `HOLD-205/210/220/230/371` (ruling 18b). `HOLD-410` moved to `/home/user/reports/briefs/` (obsolete). `audit-requests/` empty.

## Held items

- Port packages (ruling 18b) until Tom reports the long-range agreement. `scout-defs-2` interface packages: not briefed.

## For ARCHITECT

- `/home/user/reports/hard/`: empty.
- Tasks board 17 open (< 20, ruling 19): a restock brief should take the wiki/tooling slot after `wiki-cc-by-licence` merges.
- The ARCHITECT tooling item "integrate.sh trial merges in a separate worktree" is still open (only culprit detection and the
  transient-base refusal are in). Queue it after the restock, or accept [recommended: accept for now; the refusal catches it].
- Prover queue drains (6 left, ruling 21 forbids new prover briefs): provers are self-directed under PROVER-CHARTER, so no action.

## For Tom

- **Pull request #8 to `main` (ruling 22.1):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 —
  gate passed on `4ca13cb` (373 proved); last gate + kernel replay: `a747905` (replay on `4ca13cb` running). Not merged this
  round: we wait for the kernel replay (ruling 10(1)); last round the merge call was refused by the permission layer. Merging it
  also closes #9 and #10 as merged.
- **PR #9 and #10** opened on Yujin Kim's behalf from his fork (ruling 24); proof-only, merged into the integration branch on our gate.
- **Stray branch:** this round pushed `work/fix-ci-cancelled-push-run-fix` (`025be61`, audited CI fix, now merged) to origin by
  mistake; deleting it was refused by the remote. Harmless; delete it when convenient.
- Wiki licence (ruling 23) is briefed (`wiki-cc-by-licence`); not yet in the repository.
- Issue #1 can be closed (fixed on `main`). Older questions: STATUS_LOG.md "For Tom".

## Lessons

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
