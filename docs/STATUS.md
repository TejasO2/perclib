# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~21:55 UTC, end of coordinator round 10
(new series). Cut to the current state under ruling 20e; the full round-7 file and older history are in
[STATUS_LOG.md](STATUS_LOG.md) (do not read by default). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md) and `/home/user/reports/ACTIVE.md` (**new: read it instead of RULINGS.md**, ruling 20e;
it distils rulings 1-20; new rulings are appended there). Round cap: 60 tool calls (ruling 20e).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `ba7dc00`** (pushed; this STATUS commit
  and `docs/FRONTIER.md` on top). **Next gate: `scripts/gate.sh ba7dc00`.**
- **Round 10 batch** (one batch, merged on `26a512e`): `tooling-integrate-scripts` (scripts + tests, no `.github/`),
  `docs-port-headers` (comment-only headers of 7 ported files + `third_party/critical-lrp/` licences),
  `dedup-exponential-moments` (proof-only move into `Probability/ExponentialMoments.lean`), `hier-pointwise-ingredients`
  (proof-only, new `Models/HierarchicalPointwise.lean`), `fix-tasks-restock` (contains `tasks-restock`; audit
  required changes 1-3 checked against the report), `wiki-citation-links`, `wiki-revise-proof-sections-a-r3` (audit r3
  APPROVE, critic r3 PASS on both articles: batch a of the critic is closed). `scripts/gate.sh 8076788` (log
  `/home/user/reports/gate-round10.log`): build OK (3,970 jobs), script tests OK, "D-35 checks passed", one INTERFACE
  notice = comment-only header change in `Analysis/RegularVariation/Defs.lean` (docs-port-headers; expected), "== gate
  passed on ba7dc00". Import closure: all 377 modules imported. Wiki `npm test` 116/116 on the merged tree.
- **Kernel replay:** last passed at `a747905`; next after the tenth batch since then (about round 16).
- **GitHub (21:45):** `main` = `ae4eb08` (unchanged); outside heads unchanged (PR #2 `630d985` reviewed,
  `work/hierarchical-two-point-paper` `be2b9df` reviewed). Open: PR #2, issue #1. **Actions:** CI on `8991deb`
  cancelled (superseded by the `26a512e` push, concurrency group); CI on `26a512e` in progress at 21:45; CI on `ba7dc00`
  started by this push — next coordinator records both. Automerge on `main`: skipped (no PR). No GitHub write tool
  (no MCP GitHub server in this session).

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
setsid nohup scripts/gate.sh <last-gated> > /home/user/reports/gate-roundN.log 2>&1 < /dev/null &
until ! pgrep -f scripts/gate.sh >/dev/null; do sleep 20; done; tail -6 /home/user/reports/gate-roundN.log
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
rm -f scripts/__pycache__/frontier.*.pyc
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm test; rm node_modules; rm -rf dist
```
`scripts/integrate.sh BASE BRANCH...` and `scripts/apply_exact_edits.py EDITS.json` are merged (round 10): use them for merges + gate and for auditors' exact replacements (usage in the script headers).

## Progress (D-35 measure)

Manifest at `ba7dc00`: **309 proved, 1 statement-only, 1,093 unformalised, of 1,403** (unchanged: the round-10 batch
was proof-only/tooling/docs, no new tags). Round 10: 0 assertions proved and merged, 0 tagged statements merged;
two hierarchical proof-only packages and a dedup merged. `docs/FRONTIER.md` regenerated at `ba7dc00`.
Agents started in round 10 (by claim, ruling 20g): prover 5 (hier-7ynx-pointwise, hier-dedup-r11-sibling,
nm-window-correlation, nm-entropy-event, nm-truncated-maximal; plus nm-probability/nm-bond-core claimed earlier);
audit 2 (audit-p-a-V4QQ, audit-tags-kernel-coupling); outside-launcher `tag-*` claims: NIAD, UDUU new.

## Finished, not merged (next batch: integrate all of these first)

Done markers that arrived during/after this round's gate (one batch per round):
- Proof-only, merge on the gate: `work/hier-dedup-r11-sibling` (`f132021`; item 2 done in the fallback form, item 1 not
  possible: import cycle), `work/move-small-intensity-helpers` (`f34212a`), `work/cleanup-cluster-law` (`3df9f0c`).
  Check each diff adds no def/tag (`git diff ba7dc00...work/<id> | grep -E '^\+.*@\[tag|^\+(def|instance|structure) '`).
- Interface, audit on file — read the verdicts, apply exact replacements with `scripts/apply_exact_edits.py`, merge on
  APPROVE: `work/connection-kernel-tags` (`196518a`) + `work/monotone-coupling-tag` (`a469e44`) with
  `/home/user/reports/audit-tags-kernel-coupling.md`; `work/p-a-V4QQ` (`68c66a6`, tags V4QQ, YWTU, 2XJX, FF30; add imports
  `Models.HierarchicalBallSusceptibility`, `Models.HierarchicalRunawayInterval`, `Models.Tags.HierarchicalRunaway`) with
  `/home/user/reports/audit-p-a-V4QQ.md`. On those merges move the matching `tasks/` twins to done.
- Interface, audit queued: `work/nm-bond-core` (`13c31c3`, CKJQ) -> `006-audit-nm-bond-core`; `work/nm-probability`
  (`bee1a2c`, KB49, W90W) -> `007-audit-nm-probability`; `work/p-b-6L9Z` (`5611839`: new hub definition `sizeBiased` =
  6L9Z, tag IDIL, two new files under `Models/LongRange/` (not Defs.lean)) -> `008-audit-p-b-6L9Z`.
- `tasks/`: STATUS r9 asked to "mirror the board" for the 15 new open tasks; `scripts/check_tasks.py` passes on the
  merged tree; check `tasks/README.md` lists them.

## In flight (claims without done at 21:51)

`hier-7ynx-pointwise` (174), `nm-entropy-event` (251), `nm-truncated-maximal` (252), `nm-window-correlation` (250), and
outside-launcher claims `tag-2XJX, tag-6L9Z, tag-FF30, tag-IDIL, tag-MS6M, tag-NIAD, tag-S23T, tag-UDUU, tag-V4QQ,
tag-YWTU` (worktrees `p-a-*`, `p-b-*`; their finished packages so far: `p-a-V4QQ`, `p-b-6L9Z`; `p-a-S23T` in progress).
Treat their output as interface (tags): audit before merge. They work in `hierarchical-runaway`,
`spatial-convolution-asymptotics`, `size-biased-laws`: keep our briefs out of those articles.

## Queue (`/home/user/reports/queue/`)

Startable at 21:55 (no `HOLD-`, no claim): **audits** `006-audit-nm-bond-core`, `007-audit-nm-probability`,
`008-audit-p-b-6L9Z`; **prover** `260-nm-cutoff-localization`, `370-salvage-directional-decay`,
`389-frontier-riccati-linear-error`, `390-frontier-fourth-moment` (I2YU), `391-frontier-predictable-swap` (Q3MP),
`392-frontier-maximal-martingale` (HXNR), `393-frontier-discrete-entropy` (JR0J), `394-frontier-killed-green` (331W),
`395-frontier-chemical-moments` (SBMG), `396-frontier-consistent-geodesics` (BN7Z). Claims are fast (workers took 5
briefs within minutes): if fewer than 8 remain, brief more frontier items nearest first (`docs/FRONTIER.md`; avoid
the three outside-launcher articles above and the `tasks/open/` items). Every brief has owned new files (disjoint) and
a tool-call budget. Held: `HOLD-audit-nm-{window-correlation,entropy-event,truncated-maximal}` (release on done, as
round 10 did for bond-core/probability: amendment paragraph with sha, scope and `/home/user/perclib/wiki` source);
ruling 18b: `HOLD-205`, `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371`.
Next to brief: after `hier-dedup-r11-sibling` merges, let `sum_shell_tau_ge`'s twin in `HierarchicalPointwise.lean`
call the extracted public lemma (small proof-only); 7YNX audit when 174 reports; catalogue-gap scout and conversion of
`hierarchical-two-point` to citation markup (`wiki-citation-links` merged; one wiki/tooling slot); long-range area row in
`tasks/README.md`.

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (now ten, incl. NIAD/UDUU): another launcher feeds workers with no brief in `queue/`; they
  produced `p-a-V4QQ` (4 tags) and `p-b-6L9Z` (a new hub definition `sizeBiased`, 90 dependents, plus IDIL under
  `Models/LongRange/`). D-34 escalation (widely used definition, ruling 23), not blocking: options (a) audit as usual
  and merge on APPROVE [recommended; audit 008 queued and asked to check duplication and ruling 18]; (b) hold all
  outside-launcher definitions until you confirm the launcher. Please tell the coordinator its brief source.
- **One batch per round** remains the throughput limit: eight packages finished during this round's gate and wait a
  round. Proposal unchanged: allow a second batch when the first passed and fewer than 40 calls were used.
- Older open items: STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip `ba7dc00` passed the gate (replay
  pending its schedule). `main` lacks everything after `ae4eb08`.
- Long-range collaboration (ruling 18): `tasks/areas/long-range.md` and `docs/reports/long-range-concordance.md` are the
  basis for the joint review; new port work stays paused until you report. `third_party/critical-lrp/` licence files
  and provenance headers are now on the integration branch (please confirm the licence notices).
- Issue #1 can be closed (fixed on `main`).
- Open questions carried over unchanged: STATUS_LOG.md "For Tom".

## Lessons

- Push immediately after a passed gate (done this round within one call of the pass).
- Workers claim new briefs within minutes and finish small packages during the gate: write briefs before the gate
  finishes, and expect a full "finished, not merged" list at the start of the next round.
- Held audit briefs go stale (scope withdrawn, wiki moved to `/home/user/perclib/wiki`): release them with an amendment
  paragraph rather than as written.
- Older lessons: STATUS_LOG.md "Lessons".
