# Status

Handoff for the maintainer (LEAD role of D-34). Updated 26 November 2026, ~05:55 UTC, end of **paced cycle 2** (ruling 25).
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default; cycle 1 details are at its end).
A maintainer with no memory resumes from this file and `/home/user/reports/ACTIVE.md` (ruling 25: 40 calls per round;
order: collaborators' pull requests and fork branches, then `main`, then the task board, then our own work).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2`. **Last gated commit `80a735b`** (`== gate passed`, log `/home/user/reports/gate-cycle2b.log`).
  On top: this STATUS commit only (docs). Push it; it reaches `main` with the next batch.
- **`main` = `be36e68`** (PR #25, merged by us). PR #24 (`c1f1a95`) also merged by us this cycle. The integration PR open+merge
  through the API **worked this cycle** (the cycle-1 refusal did not recur). `origin/main` is merged back (fast-forward).
- Batches this cycle:
  - `scripts/integrate.sh ded7bc4 pr/11 pr/12` -> **`d311edc`**, gate passed (log `/home/user/reports/integrate-cycle2.log`). PR #24.
  - `65f027f`: the five exact docstring edits of `audit-c1-planar` applied verbatim (`scripts/apply_exact_edits.py`); changed
    modules built `--wfail`. `80a735b`: 7 proved tasks moved to `tasks/done/`, FRONTIER regenerated. Gate on `80a735b` passed
    (base extract missing, so "treat as interface" NOTICE; content is verbatim audit edits + docs, no re-audit, ruling 10). PR #25.
- **Kernel replay:** the run on `28c8877` is dead at 180/538 (`/home/user/wt/kreplay-28c8877`). Last passed: `a747905`.
  Restart niced when a cycle has room (`nice -n 15 scripts/kernel_replay.sh 2` in a fresh worktree of the tip); remove the old one.
- **Actions (05:00):** CI on the integration branch at `39bd0af` success; earlier pushes cancelled (fine). Automerge on `main` skipped.

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <tip> <sha-or-branch> ... > /home/user/reports/integrate-<id>.log 2>&1 < /dev/null &
timeout 590 bash -c 'until ! pgrep -f "scripts/integ[r]ate.sh" >/dev/null; do sleep 60; done'; tail -4 /home/user/reports/integrate-<id>.log
git fetch https://github.com/yujinhkim/perclib work/<b>:refs/remotes/yujin/work/<b>; git fetch origin pull/<n>/head:refs/remotes/pr/<n>
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>
python3 scripts/build_manifest.py .lake/gate/<sha>.json --output .lake/manifest.json
python3 scripts/frontier.py .lake/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
python3 scripts/check_tasks.py      # "possibly done" warnings: check proof_status in the manifest, then git mv to tasks/done/
```

PR to `main`: POST `/pulls` (head `claude/zen-lovelace-rvlcw2`), then PUT `/pulls/<n>/merge` `{"merge_method":"merge","sha":<gated>}`.

## Collaborators (ruling 25.1)

| PR | Author / branch @ tip | State | Next |
|---|---|---|---|
| #10 | yujinhkim `work/yujin-cutoff-moment-prereqs` @ `80ee07a` | **merged** (Tom, `97b39e5`) | none |
| #11 | TejasO2 `work/TejasO2-planar-defs` @ `e3f955b` | **merged** via #24; audit A APPROVE WITH CHANGES; fix `65f027f` in #25; commented | none |
| #12 | TejasO2 `work/TejasO2-planar-arm-defs` @ `26bc850` | **merged** via #24; audit B APPROVE WITH CHANGES; fix in #25; commented (offered definitional `ArmsDisjoint` fix as his PR) | none |
| #13-#23 | yujinhkim stack (ruling 24), opened by us in cycle 1, commented | not reviewed; tips unchanged this cycle | audit `060-audit-c2-yujin-defs` queued (#13, #15, #17) |
| #2 | tomhutchcroft `work/lace-foundations` @ `630d985` | unchanged since 21 Nov | Codex's area; Tom's |

No new comments on any thread since cycle 1. Yujin stack (base `45309ab`, bottom to top; D = definitions, needs audit; P = proof-only,
merges on the gate after its base): #13 `exploration-envelope` `aa1cf85` D -> #14 `exploration-proofs` `9e7382d` P -> #15
`bfs-definitions` `45926a3` D -> #16 `bfs-core-proofs` `20fb6e9` P -> #17 `bfs-revelation-definitions` `2bde2d8` D -> #18
`bfs-revelation-proofs` `e9d938c` P -> #19 `bfs-limit-proofs` `302759e` P -> #20 `generation-definitions` `8acc3a8` D (9) -> #21
`generation-proofs` `cd5ff5c` P -> #22 `bfs-moment-definitions` `cc6eb18` D (1; one line mentions sorry/axiom/admit) -> #23
`bfs-high-temperature-proofs` `bf03542` D (~37k lines, 35 defs, long-range `Defs.lean` files; 7 lines mention sorry/axiom/admit;
asked him to confirm). **When `060` approves: integrate #13..#19 in stack order in one batch** (#14, #16, #18, #19 are proof-only),
apply exact edits in a `-fix` commit, comment on each PR. Then audit #20 + #22.

**Fork tips seen (ruling 24):** `lrp-I41-mt-updated` `e6cf6fe` (merged, #9); `work/yujin-cutoff-moment-prereqs` `80ee07a` (merged,
#10); the eleven stack tips above (unchanged at 05:00). No fork of `TejasO2` is watched (he opens pull requests directly).

## Progress (D-35 measure)

Manifest regenerated at `d311edc`: **417 proved of 1,403** (FRONTIER: 258 ready, 721 blocked, 7 without prerequisites).
Cycle 2 report: pull requests handled 4 (#11, #12 merged and commented; #24, #25 opened and merged); merged to `main`: `c1f1a95`,
`be36e68`; assertions proved this cycle: none new (no prover sessions ran); agents started by me: 0 (1 audit brief queued, `060`).
Lane B finished since cycle 1: `audit-c1-planar` (report `/home/user/reports/audit-c1-planar.md`).

## Finished, not merged

- `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8): approved, fails the gate on `local macro`
  (`PercLib/Combinatorics/NonbacktrackingRecurrence.lean` lines 98, 379). Needs fix branch (inline the notations, statements unchanged).
- `work/p-b-W8PB` @ `f030931` (W8PB, `Probability/Tags/PartitionSizeMoments.lean`) and `work/p-c-J1LW` @ `772a62c` (J1LW,
  `Bond/Tags/RevealedCluster.lean`): tagged statements; audit requests in `/home/user/reports/audit-requests/` (not yet briefed;
  move to `done/` when briefed).

## In flight / claims

- Lane B: `060-audit-c2-yujin-defs` (queued, unclaimed). `tasks-restock-r3` claim **released** this cycle (idle 4 days; moved to
  `/home/user/reports/claims-released/`; branch `work/tasks-restock-r3` @ `0d92c19` left in place, not merged).
- Launcher `tag-*` claims: self-directed provers (PROVER-CHARTER).

## Queue (`/home/user/reports/queue/`)

Next lane-B briefs, one per cycle, in this order: (1) batched audit W8PB + J1LW (2 tags); (2) 0MK8 macro fix; (3) task-board
restock: only **8 open tasks** (ruling 19 asks 20+; public material only; nothing in the planar, lace or long-range areas);
(4) `tasks/areas/planar.md` map for Tejas; (5) integrate.sh culprit parsing (tooling). Raise (3) earlier if contributors run dry.
Prover drain only (ruling 21): `420`-`423` in queue. Held: `HOLD-060/205/210/220/230/371` (ruling 18b).

## Held items

- Port packages (ruling 18b). MDB8 follow-up (move `ConvexOrder`/`UnifIntegrableAlong` to Defs). XMYD follow-up
  (`HierarchicalLayers.pairLevel` via `level`).

## For ARCHITECT

- Ruling 22.1 PR open+merge worked this cycle (#24, #25); the cycle-1 refusal item is closed.
- `/home/user/reports/hard/` is empty.
- The Yujin stack is ~45k lines with ~78 definitions; at one lane-B worker per cycle its audits take many cycles. Consider raising
  `others` for a few cycles, or asking him for smaller branches (asked on #23).
- The task board is down to 8 open tasks after moving 7 proved ones to done; a restock needs the single wiki/tooling slot.
- integrate.sh culprit detection misses gate `FAIL <file>: forbidden tokens` and lake's "logged failures" list; trial merges
  still run on the main checkout.

## For Tom

- Merged by us under ruling 22: #24 (`c1f1a95`: Tejas's #11, #12 after a D-35 audit + gate; KGNK) and #25 (`be36e68`: audit
  docstring edits, task board, FRONTIER). Compare link: https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 —
  last gate `80a735b` (local, not CI); last gate + kernel replay: `a747905`.
- Pull requests #13-#23 were opened by us from Yujin's fork (ruling 24) so that each has a thread; their audit has started.
- Stray remote branch `work/fix-ci-cancelled-push-run-fix` (merged); delete when convenient. Issue #1 can be closed.

## Lessons

- After a stop of several days, read `git log origin/main` first: Tom may have merged work while STATUS was stale.
- integrate.sh may drop innocent branches: when the gate log names a forbidden-token or module failure in one branch,
  re-merge the others in a new batch.
- An approved audit does not mean the gate passes (forbidden tokens such as `macro`): audit briefs now ask auditors to flag them.
- The gate extract `.lake/gate/<sha>.json` feeds `build_manifest.py` directly: FRONTIER regeneration costs no extra build.
- Check `git status -sb` before committing STATUS, and `git ls-remote` after pushing. Push only the integration branch.
- Older lessons: STATUS at `2e65744` and STATUS_LOG.md "Lessons".
