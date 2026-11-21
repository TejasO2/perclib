# Status

Handoff for the coordinator (LEAD role of D-34). Updated 21 November 2026, ~21:45 UTC, end of coordinator round 9
(new series). Cut to the current state under ruling 20e; the full round-7 file and older history are in
[STATUS_LOG.md](STATUS_LOG.md) (do not read by default). A coordinator with no memory resumes from this file,
[COORDINATOR.md](COORDINATOR.md) and `/home/user/reports/ACTIVE.md` (**new: read it instead of RULINGS.md**, ruling 20e;
it distils rulings 1-20; new rulings are appended there). Round cap: 60 tool calls (ruling 20e).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2` (both repositories). **Last gated commit `8076788`** (pushed with this STATUS
  commit on top). **Next gate: `scripts/gate.sh 8076788`** (extract saved in `.lake/gate/`).
- **Round 8** (18:22-18:31, its coordinator committed but neither pushed nor wrote STATUS): merged `nm-graph-certificates`
  (D106, HQ6X, NBY2, YPNG), `nm-small-intensity` (1EWX, HRS7), `nm-closed-products` (UNJ6, R3I9), `fix-ci-c1`,
  `docs-port-credits`, each with its audit APPROVE on file; `scripts/gate.sh 2023c28` passed on `8991deb`
  (log `/home/user/reports/gate-round8.log`). Pushed by round 9 at 21:29.
- **Round 9 batch** (one batch): `scout-long-range-map` (docs/tasks only), `fix-docs-automerge-state` (contains
  `docs-automerge-state`; AGENTS.md/CONTRIBUTING.md R1-R4; docs, no re-audit under ruling 20b), `wiki-revise-proof-
  sections-c` (audit APPROVE WITH CHANGES; its one required change, `arXiv:0706.4105`, applied verbatim in `8076788`;
  critic r2 PASS). `scripts/gate.sh 8991deb` (log `/home/user/reports/gate-round9.log`): build OK (3,969 jobs), forbidden
  scan 376 files, script tests OK, "D-35 checks passed", "PROOF-ONLY change … 0 Lean file(s)", "== gate passed on
  8076788…". Wiki `npm test` 107/107 on the merged tree.
- **Kernel replay:** passed at `a747905` ("Kernel replay passed: 369 modules", `/home/user/reports/replay-a747905.log`);
  worktree removed. Next scheduled after the tenth batch since then (about round 16) unless an interface fold lands.
- **GitHub (21:30):** `main` = `ae4eb08` (unchanged). Outside heads unchanged: PR #2 `630d985` (reviewed,
  `docs/reviews/pr-2.md`), `work/hierarchical-two-point-paper` `be2b9df` (reviewed); `refs/pull/3,4` merged earlier.
  Open: PR #2, issue #1 (fixed on main; Tom can close). **Actions:** CI on `main` `ae4eb08` success; Pages `ae4eb08`
  success; CI push on integration `fb3b525` success (earlier `1af691c`, `f268213` failed: the push-wait race fixed by
  `fix-ci-c1`, merged); CI on `8991deb` in progress at 21:30 — next coordinator records it. Automerge runs: skipped
  (no PR).

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
setsid nohup scripts/gate.sh <last-gated> > /home/user/reports/gate-roundN.log 2>&1 < /dev/null &
until ! pgrep -f scripts/gate.sh >/dev/null; do sleep 20; done; tail -6 /home/user/reports/gate-roundN.log
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
rm -f scripts/__pycache__/frontier.*.pyc
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm test; rm node_modules; rm -rf dist
```
Once `scripts/integrate.sh` exists (brief `tooling-integrate-scripts`, claimed), use it for merges + gate.

## Progress (D-35 measure)

Manifest at `8076788`: **309 proved, 1 statement-only, 1,093 unformalised, of 1,403** (was 301 at `2023c28`).
Rounds 8-9: **8 assertions proved and merged, 8 tagged statements audited and merged** (D106, HQ6X, NBY2, YPNG, 1EWX,
HRS7, UNJ6, R3I9). `docs/FRONTIER.md` regenerated at `8076788`.
Agents started in round 9 (ruling 20g), by claim: prover 2 (hier-pointwise-ingredients, dedup-exponential-moments) plus
5 `tag-*` claims of unknown origin (below); tooling 2 (wiki-citation-links, tooling-integrate-scripts); fix 1
(fix-tasks-restock); docs 1 (docs-port-headers); critic 1 (critic-reread-proof-sections-a-r3); also finished just after
the batch: connection-kernel-tags, monotone-coupling-tag (prover, claimed in an earlier window).

## Finished, not merged (for the next batch)

- `work/connection-kernel-tags` (`196518a`) and `work/monotone-coupling-tag` (`a469e44`): tag packages (interface).
  Batched audit `003-audit-tags-kernel-coupling` queued. Merge on APPROVE (apply exact replacements verbatim).
- `work/fix-tasks-restock` (done 21:38): applies required changes 1-3 of `audit-tasks-restock` on top of
  `work/tasks-restock`. Check items 1-2 in its report against the audit; if faithful, merge (tasks only, no gate
  impact beyond script tests), then mirror the board (15 new open tasks; `connection-kernel-tags`,
  `monotone-coupling-tag` twins to done when they merge).
- `docs-port-headers` (done ~21:3x): header comments of seven ported files + `third_party/critical-lrp/`. Comment-only
  plus licence files: merge on the gate (check that only header blocks changed: `git diff` limited to leading comments).
- `work/wiki-revise-proof-sections-a-r3` (`3acea3f`): audit r3 APPROVE; critic re-read
  `critic-reread-proof-sections-a-r3` done at ~21:3x (read `/home/user/reports/critic-reread-proof-sections-a-r3.md`);
  merge if PASS, otherwise merge with the residual list "For Tom" (critic cap reached, ruling 20b).
- Then: Lemma I.5.5 / 2KB9 / B5SL tag package (Lean `Tags/` only) — check first that it is not "new port work" under
  ruling 18b; if it is, hold it.

## In flight (claims without done at 21:42)

`dedup-exponential-moments` (171), `hier-pointwise-ingredients` (170), `tooling-integrate-scripts` (002),
`wiki-citation-links` (008), and **`tag-2XJX`, `tag-6L9Z`, `tag-FF30`, `tag-V4QQ`, `tag-YWTU`** (worktrees `p-a-V4QQ`,
`p-b-6L9Z`): no brief of that name exists in `queue/`; probably workers of another launcher taking hierarchical tags
(V4QQ/YWTU are J98J-adjacent). Leave them alone; when they finish, treat as interface (tags): batched audit before merge.

## Queue (`/home/user/reports/queue/`)

Startable (no `HOLD-`, no claim) at 21:45: **10 prover** — `172-cleanup-cluster-law`, `173-move-small-intensity-
helpers`, `200-nm-bond-core`, `240-nm-probability`, `250-nm-window-correlation`, `251-nm-entropy-event`,
`252-nm-truncated-maximal`, `260-nm-cutoff-localization` (new: 32GP, group-free localization), `370-salvage-directional-
decay`, `389-frontier-riccati-linear-error`; **1 audit** — `003-audit-tags-kernel-coupling` (new, batched). Every
startable brief now carries a tool-call budget (ruling 20d). Owned files are mutually disjoint (260 owns new files in
`Bond/SpatialMoments/` and `Bond/Tags/CutoffLocalization.lean`; nobody else touches `Localization.lean`).
Held: `HOLD-audit-nm-{bond-core,probability,window-correlation,entropy-event,truncated-maximal}` (release when the
matching prover package reports: fill in its head sha, give a number; consider batching two into one auditor);
ruling 18b: `HOLD-205`, `HOLD-210`, `HOLD-220`, `HOLD-230`, `HOLD-371`. `HOLD-audit-fix-docs-automerge-state` retired
to `/home/user/reports/briefs/` (docs need no agent audit under 20b).
Next to brief (priorities D-34): audits of 170/171 are not needed (proof-only: merge on the gate); 7YNX tag package
after 170 merges (hier-map H10 step 2); near-miss B2ZL waits for ruling 18 (long-range area); move package from the
nm-small-intensity report = `173` (queued); catalogue-gap scout and conversion of `hierarchical-two-point` to citation
markup after `wiki-citation-links` merges; the long-range area row in `tasks/README.md` (scout-long-range-map merged).

## Migration windows

None open; all three D-35 migrations are done. Next interface changes: `scout-defs-2` packages (first
`chiCriticalIntensity`), each announced in `docs/INTERFACE_CHANGES.md` first; none may touch files frozen by ruling 18d.

## Held items

- Port packages and B2ZL: ruling 18b until Tom reports the agreement with the outside LRP author.
- `scout-defs-2` interface packages: not yet briefed (needs a free lane-B slot; token priority is proving).

## For ARCHITECT

- **Unknown `tag-*` claims** (see In flight): five claims not issued by this queue. If another launcher is feeding
  workers, please tell the coordinator which brief source they use so their owned files can be kept disjoint.
- **One batch per round** remains the main throughput limit: four packages finished during this round's gate and wait
  a full round. Proposal: allow a second batch when the first passed and fewer than 40 calls were used.
- Round-8 coordinator committed a gated batch without pushing or writing STATUS (likely ran out of budget). Order of
  work now: push right after the gate passes, STATUS before anything optional.
- Older open items (shared lace prerequisites, window readings, linters left off): see STATUS_LOG.md "For ARCHITECT".

## For Tom

- **Next pull request to `main` (ruling 13a):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2
  — last commit that passed both gate and kernel replay: **`a747905`**; the tip `8076788` passed the gate (replay
  pending its schedule). `main` lacks everything after `ae4eb08`. `/home/user/reports/READY-FOR-MAIN` not rewritten
  this round.
- Long-range collaboration (ruling 18): `tasks/areas/long-range.md` and `docs/reports/long-range-concordance.md` are now
  on the integration branch as a basis for the joint interface review; new port work stays paused until you report.
- Issue #1 can be closed (fixed on `main`).
- Open questions carried over unchanged (wiki style items, Pages wording approval, wiki-original results, errata
  confirmations, `wiki/STYLE.md` approval, CI settings, licence notices, I.4.13 premise): full text in STATUS_LOG.md
  "For Tom".

## Lessons

- Push immediately after a passed gate; a predecessor's unpushed gated batch cost three hours of visibility.
- Done markers arrive in bursts when lanes restart; integrate what is done at batch start, queue audits for the rest.
- Older lessons: STATUS_LOG.md "Lessons".
