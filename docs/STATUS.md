# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~22:20 UTC, end of coordinator round 11
(new series). Cut to the current state under ruling 20e; older history is in [STATUS_LOG.md](STATUS_LOG.md) (do not read
by default; round 10's full STATUS is in git history at `e758be6`). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md) and `/home/user/reports/ACTIVE.md` (read it instead of RULINGS.md, ruling 20e). Round
cap: 60 tool calls.

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `ef5afb7`** (pushed; this STATUS commit,
  `docs/FRONTIER.md` and the `tasks/` moves on top). **Next batch: `scripts/integrate.sh ef5afb7 <branches>`.**
- **Round 11 batch** (one batch, `scripts/integrate.sh ba7dc00 ...`, log `/home/user/reports/integrate-round11.log`, gate log
  `.lake/integrate/gate-20261121-215345-1.log`): proof-only `hier-dedup-r11-sibling`, `move-small-intensity-helpers`,
  `cleanup-cluster-law`; interface on APPROVE: `connection-kernel-tags` (70KD, UZ7J), `monotone-coupling-tag` (2ML7)
  (`audit-tags-kernel-coupling`, optional cosmetic edits not applied), `p-a-V4QQ` as `work/p-a-V4QQ-ff30` = `68c66a6` +
  `c66ddce` (the audit's FF30 exact edits applied verbatim with `scripts/apply_exact_edits.py`; V4QQ, YWTU, 2XJX APPROVE,
  FF30 APPROVE WITH CHANGES). 3 missing imports added by the script. Result: build OK (3,976 jobs), script tests OK,
  "D-35 checks passed", one INTERFACE notice (tag tokens in `Models/HierarchicalBallSusceptibility.lean`, = audited
  V4QQ/YWTU), "== gate passed on ef5afb7". Pushed at once. Merged worktrees removed (`p-a-V4QQ` kept: outside launcher).
- **Kernel replay:** last passed at `a747905`; next after the tenth batch since then (about round 16).
- **GitHub (22:05):** `main` = `ae4eb08` (unchanged, nothing to merge in). Outside heads: PR #2 `630d985` and
  `work/hierarchical-two-point-paper` `be2b9df` unchanged (reviewed). New refs `pull/3`, `pull/4`: Tom's own PRs from
  `claude/zen-lovelace-rvlcw2` to `main`, both **closed unmerged** (17:03, 17:22); no outside code, no review needed.
  **Actions:** CI runs on the integration branch keep being cancelled by the next push (concurrency group, by design);
  last completed CI: `fb3b525` success (18:21); CI on `ef5afb7` in progress at 22:05 (this STATUS push will cancel it).
  Automerge: skipped (no PR). No GitHub write tool in this session.

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

Manifest at `ef5afb7`: **316 proved, 1 statement-only, 1,086 unformalised, of 1,403** (+7: 70KD, UZ7J, 2ML7, V4QQ,
YWTU, 2XJX, FF30; 7 tagged statements audited and merged). `docs/FRONTIER.md` regenerated at `ef5afb7` (276 ready).
`tasks/`: `connection-kernel-tags`, `monotone-coupling-tag`, `hier-pointwise-ingredients`, `nm-small-intensity` moved
claimed -> done; `scripts/check_tasks.py` passes.
Agents started in round 11 (claims seen this round): prover 3 (frontier-fourth-moment, frontier-maximal-martingale,
frontier-predictable-swap) plus finishes of 7 earlier claims; audit 3 (audit-nm-bond-core, audit-nm-probability,
audit-p-b-6L9Z); outside launcher `tag-655W`, `tag-7YNX` new.

## Finished, not merged (next batch: integrate all of these first)

All arrived during this round, after the batch was gated (one batch per round):
- **Interface, audit APPROVE on file — merge:** `work/nm-bond-core` (`13c31c3`, CKJQ; `/home/user/reports/audit-nm-bond-core.md`
  "Verdict: APPROVE", JSON `[]`); `work/nm-probability` (`bee1a2c`, KB49, W90W; `audit-nm-probability.md` APPROVE — read
  for any JSON); `work/p-b-6L9Z` (`5611839`, new hub def `sizeBiased` = 6L9Z + IDIL; `audit-p-b-6L9Z.md` APPROVE on the
  definition and both tags; announce `sizeBiased` in `docs/INTERFACE_CHANGES.md` before merging if not already there).
- **Interface, audit queued:** `frontier-riccati-linear-error` (`b54472e`, 19IN) -> `009-audit-frontier-riccati-linear-error`;
  `salvage-directional-decay` (`2c6976b`, 23RT, I8WP) -> `010-audit-salvage-directional-decay`; `nm-window-correlation`
  (`8ea85e5`, OB0A, UXBN; edits existing `Tightness/Hyperscaling.lean`) -> `011-audit-nm-window-correlation` (released
  HOLD with amendment); `nm-entropy-event` (`69d57a3`, 58HC; edits `BernoulliDivergence.lean`) -> `012-audit-nm-entropy-event`;
  `hier-7ynx-pointwise` (`9197e55`, 7YNX) + outside `p-a-S23T` (`44d8a15`, S23T, MS6M; edits existing
  `HierarchicalTriangle.lean`, `MultiplicativeDecrement.lean`) -> `013-audit-hier-runaway-7ynx-s23t`;
  `nm-cutoff-localization` (`3d53b14`, 32GP) -> `015-audit-nm-cutoff-localization`.
- Several of these branches are 17-33 commits behind `ef5afb7`; `integrate.sh` skips a branch with a non-import conflict
  (then queue a rebase fix brief).

## In flight (claims without done at 22:15)

`frontier-fourth-moment` (390), `frontier-maximal-martingale` (392), `frontier-predictable-swap` (391),
`nm-truncated-maximal` (252), outside-launcher `tag-2XJX, 655W, 6L9Z, 7YNX, FF30, IDIL, MS6M, NIAD, S23T, UDUU, V4QQ,
YWTU` (worktrees `p-a-*`, `p-b-*`). Treat outside output as interface: audit before merge. They work in
`hierarchical-runaway`, `spatial-convolution-asymptotics`, `size-biased-laws`: keep our briefs out of those articles.

## Queue (`/home/user/reports/queue/`)

Startable at 22:15 (no `HOLD-`, no claim): **audits** 009, 010, 011, 012, 013, 015 (above); **wiki** (the one lane-B
wiki/tooling slot) `020-wiki-cite-hier-two-point` (citation markup only; merge on `npm test` + anchor script check, no
agent audit); **prover** `176-hier-pointwise-sibling-dedup` (proof-only: drop the Pointwise copy of the lemma now in
`HierarchicalSibling.lean`), `393-frontier-discrete-entropy` (JR0J), `394-frontier-killed-green` (331W),
`395-frontier-chemical-moments` (SBMG), `396-frontier-consistent-geodesics` (BN7Z), new `397-frontier-ghost-derivative`
(J2TE), `398-frontier-brw-first-moment` (94E7, may formalise CYYG), `399-frontier-finite-triangle` (R2Y7),
`400-frontier-section-comparison` (9GXY), `401-frontier-dfs-pivot` (KRU2), `402-frontier-priority-exploration` (28UY,
a definition: interface). 11 prover briefs startable. Held: `HOLD-audit-nm-truncated-maximal` (release when 252 is
done, with an amendment paragraph: sha, scope, `/home/user/perclib/wiki` source, as round 11 did for 011/012); ruling
18b: `HOLD-205`, `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371`.
Next to brief (frontier, nearest first, not in `tasks/open/`): `7IVI` (intrinsic-geometry), `ESZG` (multipoint-trees),
`E9BP`, `1POM` (branching-random-walk), `7ZU5`, `AFJX` (adaptive-three-point); catalogue-gap scout; long-range area row in
`tasks/README.md`.

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (now twelve, incl. 655W, 7YNX): another launcher feeds workers with no brief in `queue/`.
  Their `p-a-V4QQ` merged this round after a fresh audit (option (a) of round 10, applied); `p-b-6L9Z` (new hub
  definition `sizeBiased`) has APPROVE and merges next round unless you object. D-34 question still open: please tell
  the coordinator the launcher's brief source.
- **One batch per round** remains the throughput limit: eleven packages finished during this round. Proposal: allow a
  second batch when the first passed and fewer than 40 calls were used (round 11 used ~45, so it would not have applied).
- **CI on the integration branch rarely completes** (newer pushes cancel it; last completed run 18:21). Options:
  (a) leave it (gate + replay are the boundary) [recommended]; (b) have the coordinator push once per round only.
- Older open items: STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip `ef5afb7` passed the gate (replay
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
- Older lessons: STATUS_LOG.md "Lessons".
