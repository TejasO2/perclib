# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~22:40 UTC, end of coordinator round 13
(new series). Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); round 12's STATUS is in git
history at `5c02c84`. A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md) and
`/home/user/reports/ACTIVE.md` (read it instead of RULINGS.md, ruling 20e). Round cap: 60 tool calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `e0ae3ec`** (pushed; STATUS, FRONTIER and
  `tasks/` commit on top). **Next batch: `scripts/integrate.sh e0ae3ec <branches>`.**
- **Round 13 batch** (`scripts/integrate.sh 4312804` + 9 branches, log `/home/user/reports/integrate-round13.log`, gate log
  `.lake/integrate/gate-20261121-222734-1.log`): interface on APPROVE: `salvage-directional-decay` (23RT, I8WP),
  `nm-entropy-event` (58HC), `nm-truncated-maximal` (HXNR, 4GBV), `hier-7ynx-pointwise` (7YNX), `p-a-S23T` (S23T, MS6M),
  `frontier-riccati-linear-error-edits` (19IN), `nm-window-correlation-edits` (OB0A, UXBN); proof-only:
  `hier-pointwise-sibling-dedup` (176), `frontier-killed-green` (area lemmas; diff checked: no `def`/`@[tag]`). 3 closure
  imports. Result: build OK, "D-35 checks passed", one INTERFACE notice (tag token in
  `Analysis/MultiplicativeDecrement.lean` = audited S23T), "== gate passed on e0ae3ec". No new definitions, so no
  `INTERFACE_CHANGES.md` entry. Worktrees of the merged branches and of `frontier-maximal-martingale` removed.
- **Kernel replay:** last passed at `a747905`; next after the tenth batch since then (about round 16).
- **GitHub (22:30):** `main` = `ae4eb08` (unchanged). Outside heads: PR #2 `630d985` and `work/hierarchical-two-point-paper`
  `be2b9df` unchanged (reviewed); **new PR #5** `1b29f93` (outside contributor, branch `lrp-I41-mt` into the integration
  branch; proof-only as fetched: 58 lemmas, new `Models/LongRange/{CutoffCorner,MassTransportI41}.lean`, no def/tag; it is
  the held port package lrp-I41-mt) fetched as `refs/remotes/pr/5` -> `025-review-pr-5`. **Actions:** CI `4312804`
  cancelled (concurrency), `5c02c84`/`d1295a4` in progress, CI on PR #5 `action_required` (first-time contributor
  approval); Automerge skipped. No GitHub write tool in this session.

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

Manifest at `e0ae3ec`: **332 proved, 1 statement-only, 1,070 unformalised, of 1,403** (+11: 23RT, I8WP, 58HC, HXNR, 4GBV,
7YNX, S23T, MS6M, 19IN, OB0A, UXBN; 11 tagged statements audited and merged). `docs/FRONTIER.md` regenerated at `e0ae3ec`.
`tasks/`: `event-entropy-comparison`, `frontier-riccati-linear-error`, `truncated-maximal-bound`,
`window-correlation-chains` moved claimed -> done (the HXNR duplicate noted in the last).
Agents started in round 13 (new claims seen): prover 1 (399 frontier-finite-triangle); outside launcher new `tag-EKDO`.
Coordinator round 13: 1 batch, ~35 tool calls.

## Finished, not merged (next batch: integrate these first, as audits land)

- **Audit queued (round 12):** `p-b-CUE4` (`535dc02`) -> `018`; `frontier-fourth-moment` (`1bc48c4`, I2YU),
  `frontier-discrete-entropy` (`532e96b`, JR0J), `frontier-consistent-geodesics` (`b9c5537`, BN7Z) -> `019`; `p-a-GPDF`
  (`1ab0a95`, new defs: announce in `docs/INTERFACE_CHANGES.md` before merging) -> `021`; `frontier-predictable-swap`
  (`fa67642`, Q3MP) -> `022`.
- **Audit queued (round 13):** `p-a-655W` (`4bc05fb`, 655W, 7GDE, and a **duplicate 7YNX** tag: 7YNX merged this round
  from `hier-7ynx-pointwise`; the brief asks for an exact edit dropping the duplicate attribute) -> `023-audit-p-a-655W`;
  `frontier-chemical-moments` (`a141d02`, SBMG) and `p-b-UDUU` (`85b8622`, UDUU, NIAD; contains the already-merged
  `p-b-6L9Z`) -> `024-audit-r13-batch`.
- **REJECT -> fix queued:** `nm-cutoff-localization` (`3d53b14`, 32GP) -> `017-fix-nm-cutoff-localization`, then re-audit.
- **Superseded, never merge:** `work/frontier-maximal-martingale` (`e9ec3b0`, HXNR duplicate; recorded in `tasks/done/truncated-maximal-bound.md`).

## In flight (claims without done at 22:35)

`frontier-brw-first-moment` (398), `frontier-ghost-derivative` (397), `frontier-finite-triangle` (399),
`wiki-cite-hier-two-point` (020), outside-launcher `tag-*` dirs (2XJX, 655W, 6F2J, 6L9Z, 7GDE, 7YNX, CUE4, EKDO, FF30, GPDF,
IDIL, L9YJ, MS6M, N0HM, NIAD, S23T, TIKW, UDUU, V4QQ, YWTU; many stale: the launcher keeps claim dirs; `p-b-L9YJ` was
building `Analysis/RegularVariation/TruncatedMean` at 22:26). Treat outside output as interface. They work in
`hierarchical-runaway`, `spatial-convolution-asymptotics`, `size-biased-laws`, `adaptive-three-point`,
`connection-kernels`, `regular-variation`: keep our briefs out.

## Queue (`/home/user/reports/queue/`)

Startable at 22:35: lane B (8): **fix** `017`; **audits** `018`, `019`, `021`, `022`, new `023-audit-p-a-655W`,
`024-audit-r13-batch`; **review** new `025-review-pr-5`. Prover (13): `400-frontier-section-comparison` (9GXY), `401-frontier-dfs-pivot`
(KRU2), `402-frontier-priority-exploration` (28UY, a definition), `403-frontier-lazy-walk-thresholds` (E9BP),
`404-frontier-ultrametric-sweep` (ESZG), `405-frontier-trivalent-count` (SO5J), `406-frontier-invariant-weight-test`
(G3HT), `407-frontier-optimized-cluster-tail` (4A0G), new `408-frontier-lrp-green-bubble` (1POM; new files under
`Probability/` only, no long-range Defs), `409-frontier-saw-generating` (C69U), `410-frontier-compounded-law-normalization`
(DTYB), `411-frontier-three-part-multigraph` (L3HA), `412-frontier-joint-cut-witnesses` (RIH3). Held (ruling 18b):
`HOLD-205`, `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371`.
Next to brief (not queued): `7IVI` (intrinsic-geometry; needs a Poisson-mark process definition: interface), killed-Green
notion for 331W (scout or definition package), then the next frontier tags in `docs/FRONTIER.md` at `e0ae3ec`. Before
writing a brief, `rg` the queue and the finished list for its tag.

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (now twenty, EKDO new): another launcher feeds workers with no brief in `queue/`; in round 13
  its `p-a-655W` tagged **7YNX** a second time (ours was audited and merged first). We audit before merge (`p-b-6L9Z` merged this round on APPROVE). D-34 question still
  open: please tell the coordinator the launcher's brief source, so that its targets do not duplicate ours.
- **One batch per round** is the throughput limit: round 13 merged 9 at call ~12 and ends with 8 packages awaiting
  audit. Proposal (repeated): allow a second batch when the first passed and fewer than 40 calls were used (round 12:
  the batch passed at call ~17; a second batch would have merged 8 more).
- **CI on the integration branch rarely completes** (newer pushes cancel it). Options: (a) leave it (gate + replay are
  the boundary) [recommended]; (b) push once per round only.
- Older open items: STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip `e0ae3ec` passed the gate (replay
  pending its schedule). `main` lacks everything after `ae4eb08`. PRs #3 and #4 (same branch) were closed without merge:
  if that was a decision against merging, please say so in RULINGS.md.
- Long-range collaboration (ruling 18): `tasks/areas/long-range.md` and `docs/reports/long-range-concordance.md` are the
  basis for the joint review; new port work stays paused until you report. Please confirm the licence notices in
  `third_party/critical-lrp/`.
- **PR #5** (outside contributor, `lrp-I41-mt` into the integration branch) is the held port package of ruling 18b
  (our `HOLD-210`); its CI awaits your first-contributor approval. A review is queued (`025`). We will not merge it: should
  it be accepted despite the long-range hold, and was `tasks/open/lrp-I41-mt.md` meant to be open?
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
- Outside-launcher packages can tag a statement we already briefed (7YNX in `p-a-655W`): grep the finished list's tags
  against the integration branch before every batch; the duplicate goes to its audit as an exact edit removing the attribute.
- Older lessons: STATUS_LOG.md "Lessons".
