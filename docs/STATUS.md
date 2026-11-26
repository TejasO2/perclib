# Status

Handoff for the maintainer (LEAD role of D-34). Updated 26 November 2026, ~02:50 UTC, end of **paced cycle 1** (ruling 25).
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default); the 22 Nov round-3 STATUS is in git at `2e65744`.
A maintainer with no memory resumes from this file and `/home/user/reports/ACTIVE.md` (ruling 25: 40 calls per round;
order: collaborators' pull requests and fork branches, then `main`, then the task board, then our own work).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2`. **Last gated commit `4a6dc1b`** (pushed). On top: this STATUS/tasks commit (docs only).
- `main` was `c6efdce` = Tom's merge of PR #8 (head `fb821d8`, which also closed #9 as merged); fast-forwarded into the
  integration branch this cycle. **PR to `main` NOT opened:** the open+merge call was refused by the permission layer
  (not retried, ruling 25); see For ARCHITECT / For Tom.
- Batches this cycle (`scripts/integrate.sh`, logs `/home/user/reports/integrate-cycle1{,b}.log`):
  - A `c6efdce` -> **`2f5be3e`**: `frontier-lazy-return-kernel` @ `d3988df` (KGNK, audit-r19-d A APPROVE). Gate passed.
    `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8, audit-r19-d B APPROVE) **fails the gate**: forbidden token
    `macro` (two `local macro` notations, `PercLib/Combinatorics/NonbacktrackingRecurrence.lean` lines 98, 379). Needs a fix
    branch `work/frontier-nonbacktracking-recurrence-fix` (inline or replace the notations; statements unchanged) and then a
    gate; no re-audit if the tagged statement text is unchanged. integrate.sh again dropped from the end instead of the culprit
    (the forbidden-construct `FAIL <file>: forbidden tokens` line is not parsed): it dropped PR #10 innocently first.
  - B `2f5be3e` -> **`4a6dc1b`**: `yujinhkim:work/yujin-cutoff-moment-prereqs` @ `80ee07a` (PR #10 update, 27 commits, one file
    `Models/LongRange/TruncatedMoments.lean`, no new definitions or attributes): gate passed, proof-only.
- **Kernel replay:** the run on `28c8877` (`/home/user/wt/kreplay-28c8877`, log `/home/user/reports/replay-28c8877.log`) is dead at
  180/538 (the four-day stop). Last passed: `a747905`. Restart niced when a cycle has room (`nice -n 15 scripts/kernel_replay.sh 2`
  in a fresh worktree of the current tip); remove the old worktree.
- **Actions (02:25):** CI on `main` and the integration branch at `c6efdce` in progress; Tejas's PR CI runs (#11, #12) green;
  PR #10 head `80ee07a` CI `action_required` (approval refused before: Tom's click). Automerge on `main` skipped.

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <tip> <sha-or-branch> ... > /home/user/reports/integrate-<id>.log 2>&1 < /dev/null &
timeout 590 bash -c 'until ! pgrep -f "scripts/integ[r]ate.sh" >/dev/null; do sleep 60; done'; tail -4 /home/user/reports/integrate-<id>.log
git fetch https://github.com/yujinhkim/perclib work/<b>:refs/remotes/yujin/work/<b>; git fetch origin pull/<n>/head:refs/remotes/pr/<n>
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>
```

## Collaborators (ruling 25.1)

| PR | Author / branch @ tip | State | Next |
|---|---|---|---|
| #10 | yujinhkim `work/yujin-cutoff-moment-prereqs` @ `80ee07a` | in integration branch (`4a6dc1b`); commented | closes as merged when the integration PR reaches `main` |
| #11 | TejasO2 `work/TejasO2-planar-defs` @ `e3f955b` | 15 defs, CI green; first response posted | audit `050-audit-c1-planar` queued (lane B) |
| #12 | TejasO2 `work/TejasO2-planar-arm-defs` @ `26bc850` (on #11) | ~30 defs, CI green; first response posted | same audit |
| #13-#23 | yujinhkim, opened by us on his behalf this cycle (ruling 24); one linear stack, comments posted | not reviewed | see below |
| #2 | tomhutchcroft `work/lace-foundations` @ `630d985` | unchanged since 21 Nov | Codex's area; Tom's |

Yujin stack (base `45309ab`, bottom to top; D = adds definitions, needs audit; P = proof-only, merges on the gate after its base):
#13 `exploration-envelope` `aa1cf85` D (11 defs) -> #14 `exploration-proofs` `9e7382d` P -> #15 `bfs-definitions` `45926a3` D (14)
-> #16 `bfs-core-proofs` `20fb6e9` P -> #17 `bfs-revelation-definitions` `2bde2d8` D (8) -> #18 `bfs-revelation-proofs` `e9d938c` P
-> #19 `bfs-limit-proofs` `302759e` P -> #20 `generation-definitions` `8acc3a8` D (9) -> #21 `generation-proofs` `cd5ff5c` P
-> #22 `bfs-moment-definitions` `cc6eb18` D (1; one added line mentions sorry/axiom/admit) -> #23 `bfs-high-temperature-proofs`
`bf03542` D (~37k lines, 35 defs, long-range `Defs.lean` files, `docs/PORTED_FILES.md`; 7 lines mention sorry/axiom/admit; asked
him to confirm). Nothing touches `.github/`, `scripts/`, pins or `tasks/`. **Next lane-B audit: #13, #15, #17 together** (3 small
definition packages, increments `45309ab..aa1cf85`, `9e7382d..45926a3`, `20fb6e9..2bde2d8`); then #14, #16, #18, #19 merge on the gate.

**Fork tips seen (ruling 24):** `lrp-I41-mt-updated` `e6cf6fe` (merged, #9); `work/yujin-cutoff-moment-prereqs` `80ee07a`; the
eleven stack tips above. No fork of `TejasO2` is watched (he opens pull requests directly).

## Progress (D-35 measure)

Manifest last regenerated at `28c8877`: 409 proved of 1,403. Since then merged with audits: F2G0, F7SW, PHLF, 4SZ9, O0TO, A65C,
X9N1 (audit-r19-c, before PR #8) and KGNK (this cycle). Manifest and `docs/FRONTIER.md` **not regenerated this cycle** (call cap):
do it next cycle before task-board work. Assertions proved this cycle: 1 tag merged (KGNK); no prover sessions ran yet.
Cycle 1 report: pull requests handled 14 (#10-#23: 11 opened, 14 commented), merged to `main` none (refused), agents started 0
(1 audit brief queued).

## Finished, not merged

- `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8): approved, blocked by the `macro` gate failure above (fix brief needed).

## In flight / claims

- `tasks-restock-r3` (tooling slot): claimed 22 Nov, branch `work/tasks-restock-r3` @ `0d92c19` idle 4 days, not merged, no done
  marker. Stale under ruling 25.3: release it next cycle unless it moved.
- Launcher `tag-*` claims: self-directed provers (PROVER-CHARTER). `audit-requests/`: empty.

## Queue (`/home/user/reports/queue/`)

Startable lane B: **`050-audit-c1-planar`** (Tejas #11 + #12). Prover drain only (ruling 21): `421` unclaimed (`422`, `423` in
`hard/`). Held: `HOLD-205/210/220/230/371` (ruling 18b). Next briefs, one per cycle, in this order: Yujin #13/#15/#17 audit;
0MK8 macro fix; integrate.sh culprit parsing (tooling).

## Held items

- Port packages (ruling 18b). MDB8 follow-up (move `ConvexOrder`/`UnifIntegrableAlong` to Defs). XMYD follow-up
  (`HierarchicalLayers.pairLevel` via `level`).

## For ARCHITECT

- Cycle 1: the permission layer refused the API call opening and merging the integration PR to `main` (gated `4a6dc1b`,
  tip `e8cb162`). Not retried. Needs a decision on whether ruling 22.1 still applies under the current permissions.
- `/home/user/reports/hard/`: `422-frontier-ultrametric-exchange`, `423-frontier-peierls-nontriviality`,
  `HOLD-060-tooling-integrate-worktree`, and the held long-range items.
- The Yujin stack is ~45k lines with ~78 definitions: at one lane-B worker per cycle its audits take many cycles. Consider
  raising `others` for a few cycles, or asking him for smaller branches (asked on #23).
- integrate.sh culprit detection misses gate `FAIL <file>: forbidden tokens` and lake's "logged failures" list (dropped an
  innocent branch again); trial merges still run on the main checkout.

## For Tom

- **Integration branch to `main` (ruling 22.1):** https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 —
  gate passed on `4a6dc1b` (local verification, not CI); last gate + kernel replay: `a747905`. Merging closes #10 as merged.
- PR #10 CI on `80ee07a` needs your first-run approval click (our approve call was refused earlier).
- Pull requests #13-#23 were opened by us from Yujin's fork (ruling 24) so that each has a thread.
- Stray remote branch `work/fix-ci-cancelled-push-run-fix` (merged); delete when convenient. Issue #1 can be closed.

## Lessons

- After a stop of several days, read `git log origin/main` first: Tom may have merged the integration PR while STATUS was stale.
- integrate.sh may drop innocent branches: when the first gate log names a forbidden-token or module failure in one branch,
  re-merge the others in a new batch (done this cycle for PR #10).
- An approved audit does not mean the gate passes (forbidden tokens such as `macro`): audit briefs could ask auditors to flag them.
- Check `git status -sb` before committing STATUS, and `git ls-remote` after pushing. Push only the integration branch.
- Older lessons: STATUS at `2e65744` and STATUS_LOG.md "Lessons".
