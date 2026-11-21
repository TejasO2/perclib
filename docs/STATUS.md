# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~22:45 UTC, end of coordinator round 12
(new series). Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); round 11's STATUS is in git
history at `7b0e331`. A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) and
`/home/user/reports/ACTIVE.md` (read it instead of RULINGS.md, ruling 20e). Round cap: 60 tool calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `4312804`** (pushed; STATUS, FRONTIER,
  INTERFACE_CHANGES and `tasks/` commit on top). **Next batch: `scripts/integrate.sh 4312804 <branches>`.**
- **Round 12 batch** (`scripts/integrate.sh ef5afb7 work/nm-bond-core work/nm-probability work/p-b-6L9Z-doc`, log
  `/home/user/reports/integrate-round12.log`, gate log `.lake/integrate/gate-20261121-220940-1.log`): interface on APPROVE:
  `nm-bond-core` (CKJQ), `nm-probability` (KB49, W90W), `p-b-6L9Z-doc` = `5611839` + `5ef1250` (audit-p-b-6L9Z docstring
  exact edit applied verbatim; new hub def `sizeBiased`, tags 6L9Z, IDIL; announced in `docs/INTERFACE_CHANGES.md` at
  `f72857c` before the merge, now under "Merged"). 3 closure imports added. Result: build OK, 9 script tests OK, "D-35
  checks passed", one INTERFACE notice (tag tokens in `Models/LongRange/Tags/SpatialConvolution.lean` = audited IDIL),
  "== gate passed on 4312804". Pushed. Worktrees `nm-bond-core`, `nm-probability` removed (`p-b-6L9Z`: outside launcher).
- **Kernel replay:** last passed at `a747905`; next after the tenth batch since then (about round 16).
- **GitHub (22:10):** `main` = `ae4eb08` (unchanged). Outside heads unchanged: PR #2 `630d985`,
  `work/hierarchical-two-point-paper` `be2b9df` (both reviewed); PRs #3/#4 closed (Tom's). **Actions:** CI on integration
  pushes keeps being cancelled by the next push (concurrency); last completed CI `fb3b525` success; Automerge skipped (no
  PR). No GitHub write tool in this session.

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <last-gated> work/<a> work/<b> ... > /home/user/reports/integrate-roundN.log 2>&1 < /dev/null &
timeout 590 bash -c 'until ! pgrep -f scripts/integrate.sh >/dev/null; do sleep 30; done'; tail -4 /home/user/reports/integrate-roundN.log
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>   # auditor's JSON, on a new branch work/<id>-fix from the audited sha
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
rm -f scripts/__pycache__/frontier.*.pyc
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm test; rm node_modules; rm -rf dist
```

## Progress (D-35 measure)

Manifest at `4312804`: **321 proved, 1 statement-only, 1,081 unformalised, of 1,403** (+5: CKJQ, KB49, W90W, 6L9Z, IDIL;
5 tagged statements and 1 definition audited and merged). `docs/FRONTIER.md` regenerated at `4312804`. `tasks/`:
`holley-observable-form` (KB49), `kernel-comparison-off-diagonal` (CKJQ), `profile-perturbation-bound` (W90W) moved
claimed -> done; `scripts/check_tasks.py` passes.
Agents started in round 12 (claims seen this round): prover 6 (frontier-discrete-entropy, -killed-green,
-chemical-moments, -consistent-geodesics, -ghost-derivative, -brw-first-moment, plus 176 dedup); audit 6 (009-013, 015, 016);
wiki 1 (020); outside launcher new `tag-6F2J, 7GDE, CUE4, GPDF, L9YJ, N0HM, TIKW`.

## Finished, not merged (next batch: integrate all of these first)

- **Interface, APPROVE on file — merge as is:** `work/salvage-directional-decay` (`2c6976b`, 23RT, I8WP);
  `work/nm-entropy-event` (`69d57a3`, 58HC); `work/nm-truncated-maximal` (`0787a59`, HXNR, 4GBV; audit APPROVE both);
  `work/hier-7ynx-pointwise` (`9197e55`, 7YNX); `work/p-a-S23T` (`44d8a15`, S23T, MS6M; the audit's only edits are three
  `PercLib.lean` import lines, which `integrate.sh` adds by itself: merge the branch as is).
- **Interface, APPROVE WITH CHANGES, exact edits already applied verbatim (round 12) — merge these branches instead of
  the originals:** `work/frontier-riccati-linear-error-edits` (`5d53721` = `b54472e` + 5 edits; 19IN);
  `work/nm-window-correlation-edits` (`1373dd6` = `8ea85e5` + 3 edits; OB0A, UXBN).
- **Proof-only (merge on the gate):** `work/hier-pointwise-sibling-dedup` (`2c3b7ac`, 176); `work/frontier-killed-green` (`ffa4856`, "partly done": five definition-free area
  lemmas, tag 331W not added because a notion is absent; check `git diff 4312804...ffa4856` has no `def`/`@[tag]`).
- **REJECT -> fix queued:** `nm-cutoff-localization` (`3d53b14`, 32GP stated only for bond percolation; wiki allows any
  random sets) -> `017-fix-nm-cutoff-localization`; then a fresh re-audit.
- **Audit queued:** `p-b-CUE4` (`535dc02`; defs `mobiusCoeff`, `HasNonnegMobiusCoeffs`, `HasMassTransport` = N0HM,
  PoissonTail defs; tags CUE4, TIKW) -> `018-audit-p-b-CUE4`; `frontier-fourth-moment` (`1bc48c4`, I2YU),
  `frontier-discrete-entropy` (`532e96b`, JR0J), `frontier-consistent-geodesics` (`b9c5537`, BN7Z) ->
  `019-audit-frontier-batch-r12`; `p-a-GPDF` (`1ab0a95`, GPDF def tag, 6F2J, new Defs file) -> `021-audit-p-a-GPDF`; `frontier-predictable-swap`
  (`fa67642`, Q3MP) -> `022-audit-frontier-predictable-swap`.
  New defs need an `docs/INTERFACE_CHANGES.md` announcement before they merge.
- **Superseded, do not merge:** `work/frontier-maximal-martingale` (`e9ec3b0`) tags **HXNR** again: round 11 briefed
  HXNR twice (392 and 252). Merge `nm-truncated-maximal` (audited) and drop this branch; record it in `tasks/`.

## In flight (claims without done at 22:40)

`frontier-brw-first-moment` (398), `frontier-chemical-moments` (395), `frontier-ghost-derivative` (397),
`wiki-cite-hier-two-point` (020), outside-launcher `tag-2XJX, 655W, 6F2J, 6L9Z, 7GDE, 7YNX, CUE4, FF30, GPDF, IDIL, L9YJ,
MS6M, N0HM, NIAD, S23T, TIKW, UDUU, V4QQ, YWTU` (worktrees `p-a-*`, `p-b-*`; several are already merged tags: the
launcher keeps stale claim dirs). Treat outside output as interface. They work in `hierarchical-runaway`,
`spatial-convolution-asymptotics`, `size-biased-laws`, `adaptive-three-point`, `connection-kernels`: keep our briefs out.

## Queue (`/home/user/reports/queue/`)

Startable at 22:40: **fix** `017-fix-nm-cutoff-localization`; **audits** `018-audit-p-b-CUE4`,
`019-audit-frontier-batch-r12`, `021-audit-p-a-GPDF`, `022-audit-frontier-predictable-swap`; **prover** `399-frontier-finite-triangle` (R2Y7),
`400-frontier-section-comparison` (9GXY), `401-frontier-dfs-pivot` (KRU2), `402-frontier-priority-exploration` (28UY,
a definition), new `403-frontier-lazy-walk-thresholds` (E9BP, 92 dependents), `404-frontier-ultrametric-sweep` (ESZG),
`405-frontier-trivalent-count` (SO5J, 128 dependents), `406-frontier-invariant-weight-test` (G3HT, 95 dependents),
`407-frontier-optimized-cluster-tail` (4A0G). 9 prover + 5 lane-B startable. Held (ruling 18b): `HOLD-205`,
`HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371`.
Next to brief (frontier, nearest first, not queued): `1POM`, `C69U`, `DTYB` (branching-random-walk; disjoint files
from 398/403), `L3HA`, `RIH3` (multipoint-trees), `7IVI` (intrinsic-geometry; needs a Poisson-mark process definition:
interface), killed-Green notion for 331W (scout or definition package). Before writing a brief, grep the queue for its
tag (round 11 duplicated HXNR).

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (now nineteen): another launcher feeds workers with no brief in `queue/` (CUE4, GPDF this
  round, with new definitions). We audit before merge (`p-b-6L9Z` merged this round on APPROVE). D-34 question still
  open: please tell the coordinator the launcher's brief source, so that its targets do not duplicate ours.
- **One batch per round** is the throughput limit: by the end of round 12, 9 packages are mergeable and 6 more await
  audit. Proposal (repeated): allow a second batch when the first passed and fewer than 40 calls were used (round 12:
  the batch passed at call ~17; a second batch would have merged 8 more).
- **CI on the integration branch rarely completes** (newer pushes cancel it). Options: (a) leave it (gate + replay are
  the boundary) [recommended]; (b) push once per round only.
- Older open items: STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip `4312804` passed the gate (replay
  pending its schedule). `main` lacks everything after `ae4eb08`. PRs #3 and #4 (same branch) were closed without merge:
  if that was a decision against merging, please say so in RULINGS.md.
- Long-range collaboration (ruling 18): `tasks/areas/long-range.md` and `docs/reports/long-range-concordance.md` are the
  basis for the joint review; new port work stays paused until you report. Please confirm the licence notices in
  `third_party/critical-lrp/`.
- Issue #1 can be closed (fixed on `main`).
- Open questions carried over unchanged: STATUS_LOG.md "For Tom".

## Lessons

- Apply an auditor's exact edits on a new branch `work/<id>-<fix>` from the audited sha (the author's worktree may still
  be checked out by another launcher) and merge that branch instead of the original.
- `integrate.sh` runs under `setsid`; the shell reports "Done" at once: wait on `pgrep -f scripts/integrate.sh`.
- Workers finish packages within minutes: by the end of a round expect a full "finished, not merged" list; write audit
  briefs for them in the same round so the next round can merge.
- Push immediately after a passed gate. Release held audit briefs with an amendment paragraph rather than as written.
- Grep the queue and the finished-unmerged list for a tag before briefing it: HXNR was briefed twice in round 11.
- Workers branch from the newest tip: diff a finished branch against its own base (`git merge-base`), not the previous tip, or the diff includes the last batch.
- Older lessons: STATUS_LOG.md "Lessons".
