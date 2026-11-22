---
id: exploration-terminates-at-cluster
title: On a finite graph, cluster exploration halts at the root cluster
difficulty: easy
kind: interface
labels: [good-first-task]
---

# On a finite graph, cluster exploration halts at the root cluster

## Goal
Prove and tag wiki assertion **7WHX** (article `exploration`): on a finite graph, the
edge-by-edge exploration started from the root halts, and at termination the discovered set is
exactly the root cluster. The library's priority exploration
(`PercLib/Probability/Exploration/PriorityStopped/Defs.lean`) already has the hard half:
`iUnion_priorityExploration_discovered_eq_cluster` identifies the union of the discovered sets
with the cluster whenever the size threshold is never reached. What is missing is termination
in finite time.

## Target
Let `G : SimpleGraph V` with finitely many edges (`G.edgeSet.Finite`, or `[Finite V]`), an edge
order `ι : G.edgeSet ↪ ℕ`, a root `o` and a configuration `ω`. Take threshold `n = 0` (never
reached, since the discovered set always contains `o`). Then there is a time `T` at which the
exploration has halted and its discovered set is the cluster of `o` in the open subgraph of `G`.

Sketch (spelling free):
```lean
theorem exists_priorityQuery_eq_none_and_discovered_eq_cluster [Finite V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (ω : Config V) :
    ∃ T, priorityQuery G ι o 0 ω T = none ∧
      (priorityExploration G ι o 0 ω T).discovered = cluster (ω ∩ G.edgeSet) o
```
Route: queried edges are distinct (`priorityQuery_injective`), so at most `|G.edgeSet|` steps
query an edge; after that `priorityQuery_eq_none_of_le` and
`priorityExploration_eq_of_priorityQuery_eq_none` freeze the state, and the frozen state equals
the union of all states. The area lemmas go in the new area file; the tagged statement restates
them in the `Tags/` file.

## Owned files
- New `PercLib/Probability/Exploration/Termination.lean` (area lemmas).
- New `PercLib/Probability/Exploration/Tags/Termination.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/Exploration/PriorityStopped/Defs.lean`,
`PercLib/Probability/Exploration/PriorityStopped.lean`, `PercLib/Percolation/Bond/Basic.lean`,
mathlib; wiki assertion 7WHX.

## Stop condition
7WHX tagged, built with `--wfail`; or the statement is found false as written (report it).

## Hand-off
Pull request description: the tagged statement in full, the lemmas it restates, build result.
