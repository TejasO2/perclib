# Coordination

**20 November 2026.** Rewritten under D-34, which this file summarises and never
overrides. What has been decided is in [DECISIONS.md](DECISIONS.md). The current state,
the package list and anything waiting for Tom are in [STATUS.md](STATUS.md).

## Roles

| Role | Holder | Does |
|---|---|---|
| Mathematical lead | Tom Hutchcroft | Scope, fidelity of a target to its source, corrections to sources, publication. His word is final on everything. |
| ARCHITECT | Claude session | Architecture and `DECISIONS.md`. Escalations listed in D-34. |
| LEAD | One Claude Opus agent | Plans, starts workers, integrates, runs the gate, pushes, keeps `STATUS.md`. Writes no mathematics unless a merge needs a repair. |
| Worker | Claude Opus agent, one package | Prover, auditor, scout or wiki. |

## Rules for every worker

1. Work in your own git worktree on branch `work/<package>`, on the files your package
   names. Never edit another package's files, `PercLib.lean`, the pins or `STATUS.md`;
   LEAD does that.
2. Definitions go only in files named `Basic.lean` or `Defs.lean` (D-24). Search this
   library and mathlib before defining anything. A second definition of an existing
   notion is rejected whatever depends on it.
3. Statements are on the bond interface of D-2 and faithful to the wiki assertion or
   the cited source. If a statement is false, vacuous or needs a hypothesis the source
   lacks, stop and report it with the counterexample. Do not weaken it quietly.
4. No `sorry`, `admit`, `axiom`, `native_decide`, or code that runs at elaboration time
   (D-29). A result of the literature is used only as an explicit `…Input` hypothesis
   listed in `docs/CITED_INPUTS.md` (D-4), and a target with such an input is reported
   as proved modulo, never as proved.
5. Build only the modules you changed (`lake build PercLib.Your.Module`), with
   `--wfail`. Do not run a full build; LEAD does. Do not kill a build you did not start.
6. Commit when it compiles. A proof that will not close is narrowed or tried another
   way; what compiles is committed and the rest is described in the report.
7. Adapted code carries its source, revision and licence in the header (D-6).
8. Report at the end: branch and commit; declarations added, with tags; every new or
   changed definition and tagged statement; what was built and the result; what is not
   done; approaches that failed and why.

## The gate (LEAD)

On the merged tree, before the integration branch moves:

```sh
lake build --wfail
lake env lean scripts/ExtractManifest.lean   # axiom audit and declaration extract
python3 scripts/check_import_closure.py
python3 scripts/check_proof_pr.py            # proof-only or interface
```

An interface change also needs an auditor's approval (D-34). The kernel replay of D-29
runs before each milestone push. Results are recorded in `STATUS.md` with the commit,
as local verification.

## Reporting

"Proved" means D-4 `proved` on a named commit that passed the gate. "Proved modulo"
names the inputs. A draft that has not compiled is called an uncompiled draft. Nothing
on the integration branch describes unmerged work as present (D-10).
