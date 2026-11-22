# Quad duality on ℤ², not both; interlacing and pivotal edges: advice for the wiki

Advice for the wiki agent on package PT2 of the arms plan: the "not both" half and the "exactly
one" statement of quad duality (`PercLib/Models/Planar/Arms/QuadDuality.lean`, continued from
PT1), and its first consequences in the new module
`PercLib/Models/Planar/Arms/Interlacing.lean`: the interlacing lemma in three forms
(primal–primal, mixed, dual–dual) and the four alternating arms at a pivotal edge. Order
invariance of arms across radii and relative duality are **not** done (see "Not done"). Everything
is proved with only `propext`, `Classical.choice` and `Quot.sound`; no `…Input` is used, and no
tags and no definitions were added. No wiki assertion is attached to these statements yet; they
are tools for the arm estimates.

## Conventions

As in `quad-duality-a.md`: points of `ℤ²` are `![x, y]`, boxes are `Set.Icc lo hi`, a face `f`
is the unit square with lower-left corner `f` (a dual vertex), `x` is a corner of `f` when
`x ∈ Icc f (f + 1)`, the faces inside `R = Icc lo hi` form `Icc lo (hi - 1)` and the faces touching
`R` form `Icc (lo - 1) hi`. Boundary points carry I2a's `perimeterPos` (counterclockwise from
`lo`, values `0` to `P - 1`, `P = 2 (hi₀ - lo₀) + 2 (hi₁ - lo₁)`). The arcs `A = [a, c)`,
`C = [c, b)`, `B = [b, d)`, `D = [d, P + a)` (positions read modulo `P`), the **dual arc** of an arc
(faces not inside `R` with a corner in it) and the **dual-open paths in the dual box** (paths of
faces of `Icc (lo - 1) hi` crossing only edges of `R` that are closed) are exactly PT1's.

Two pairs of boundary points **interlace** when one point of the second pair has its position
strictly between the positions of the first pair and the other strictly outside them; the four
points then alternate around the boundary.

## Statements as proved

**Quad duality, not both** (`not_exists_dualConfig_inter_mem_localConn_of_exists`, QuadDuality
l. 1447). For a box of positive width and height, `a < c < b < d < P + a` and every `ω`: if a
point of `A` is joined inside `R` to a point of `B`, then no face of the dual arc of `C` is joined
to a face of the dual arc of `D` by a dual-open path in the dual box. Same sets as PT1's
`exists_dualConfig_inter_mem_localConn_of_not_exists`, with hypothesis and conclusion exchanged.

**Quad duality** (`mem_arcCrossing_iff_dualConfig_notMem_arcCrossing`, QuadDuality l. 1612). Under
PT1's hypotheses (`h₀ : lo 0 < hi 0`, `h₁ : lo 1 < hi 1`, `a < c < b < d < P + a`), for every `ω`:

```lean
(∃ u v, u ∈ boxBoundary lo hi ∧ (∃ k : ℤ, perimeterPos lo hi u + k * P ∈ Ico a c) ∧
    v ∈ boxBoundary lo hi ∧ (∃ k : ℤ, perimeterPos lo hi v + k * P ∈ Ico b d) ∧
    ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v) ↔
  ¬ ∃ f g, (f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc f (f + 1) ∧
      ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico c b) ∧
    (g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc g (g + 1) ∧
      ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico d (P + a)) ∧
    dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g
```

(with `P` written out as `2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)` in the Lean). Exactly one of an
open crossing of `R` from `A` to `B` and a dual crossing from the dual arc of `C` to that of `D`
occurs.

**Interlacing lemma** (`Interlacing.lean`):

- *Primal–primal* (`exists_mem_support_of_interlaced`, l. 383). Two walks of `ℤ²` in a box, with
  ends `a, b` and `u, w` on its boundary, `u` strictly between `a` and `b` and `w` strictly outside
  (in either orientation of `a, b`), share a vertex. Any box: on a segment the positions are a
  coordinate and the discrete intermediate value theorem along walks applies; otherwise
  `exists_mem_support_of_interlaced_of_lt` (l. 325).
- *Mixed* (`dualConfig_inter_notMem_localConn_of_interlaced`, l. 262). In a box of positive width
  and height: if boundary points `a, b` are joined by an open path inside the box and `f, g` are
  faces outside the box with boundary corners `x, y` interlacing with `a, b`, then no dual-open
  path in the dual box (crossing only edges of the box) joins `f` to `g`.
- *Dual–dual* (`exists_mem_support_of_interlaced_dual`, l. 543). In a box of positive width and
  height: two walks of faces whose steps cross edges of the box, the second inside `Icc (lo - 1)
  hi` between faces outside the box, with boundary corners of their ends interlaced, share a
  face. The first walk's ends need only have boundary corners.

**Pivotal edges carry four alternating arms** (`exists_arms_of_pivotal`, l. 655). If the edge
`{x, y}` is pivotal for the left-right crossing of `R` (`insert s(x, y) ω ∈ crossing 0 lo hi` and
`ω \ {s(x, y)} ∉ crossing 0 lo hi`), then with the edge closed one end is joined inside `R` to the
left side and the other to the right side; and the two faces `f, g` of its dual edge
(`dualEdge s(x, y) = s(f, g)`) are joined, one to the bottom row and the other to the top row of
the dual box `R* = [lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]`, by dual-open paths of `dualConfig (insert
s(x, y) ω)` (with the edge open). The general form for any direction of any `ℤ^d`,
`exists_inter_mem_localConn_of_pivotal` (l. 599), gives the two primal arms and also that both
ends lie in the box.

**Supporting results**, each usable on its own:

- The parity function of a dual walk (QuadDuality): `add_add_add_eq_of_walk` (the crossings of the
  four edges of a face add up to the number of ends of the walk at the face),
  `eq_add_of_mem_edgeSet` and `eq_of_mem_localConn` (the parity changes across an edge of the box
  by its crossings, hence is constant on open clusters), `sum_map_ite_eq_add_of_notMem_Icc` (a
  boundary edge is crossed an odd number of times exactly when its outer face is an end of the
  walk), `eq_add_sum_of_perimeterPos` (telescoping along the boundary by positions).
- Outer faces (QuadDuality): `eq_of_mem_dualEdge_of_mem_dualEdge` (a face outside the box is a
  face of at most one edge of the box), `eq_of_mem_dualEdge_of_notMem_Icc` (an edge of the box has
  at most one outer face), `exists_perimeterPos_eq_add_one_of_mem_dualEdge` (that edge joins two
  consecutive boundary positions), `eq_or_eq_of_notMem_Icc` (an outer face has at most two boundary
  corners), `mem_edgeSet_and_mem_dualEdge_of_notMem_Icc`, `ite_mem_eq_sum_ite_dualEdge` (an edge
  of the dual lattice contains a face exactly when it is the dual of one of the face's four
  edges).
- Rings (Interlacing): `mem_localConn_of_walk_of_mem_dualEdge` (faces of edges of the box at the
  vertices of a walk untouched by `η` are joined by dual edges of closed edges of the box; the
  ring lemma of `Gluing.lean` uses dual edges crossing edges that leave the box, which quad duality
  does not allow) and `inter_mem_localConn_of_walk_of_mem_Icc` (corners of the faces of a dual
  walk are joined by edges of those faces).
- General: `Sym2.ite_add_ite_eq_ite_mem`, `Int.exists_add_mul_mem_Ico_iff_of_le` (positions modulo
  `P` after shifting by `a / P * P`), `dualConfig_sdiff_singleton_dualEdge`.

## Proofs the Lean follows

*Not both.* A parity argument generalising `notMem_crossing_one_dualConfig_of_mem_crossing_zero`.
Let `σ` be the dual walk from `f` (dual arc of `C`) to `g` (dual arc of `D`) and `X e` the number of
its steps across the edge `e`, modulo two. For a vertex `(x, y)` of `R` let `N (x, y)` be the sum
of `X` over the path from `lo` up the left side to `(lo₀, y)` and then along the row to `(x, y)`.
(1) Across a horizontal edge of `R`, `N` changes by `X` of that edge (one more term). Across a
vertical edge it changes by `X` of that edge as well: the difference is the sum of the crossing
counts of the boundary of a half-row of faces inside `R`, which is the number of ends of `σ` in that
half-row, and `f, g` are outside `R`. (2) `σ` crosses only closed edges, so `N` is constant on open
clusters: `N u = N v` for the open path from `u ∈ A` to `v ∈ B`. (3) A boundary edge is crossed
by `σ` an odd number of times exactly when its outer face is `f` or `g` (the steps touching an
outer face all cross its unique edge of `R`). Each of `f, g` is the outer face of exactly one
boundary edge (the first step of `σ` leaves it across one; `f ≠ g` because no outer face has corners
in both `C` and `D`); that edge has an end in `C` (resp. `D`). So, walking along the boundary from
`u` to `v`, `N` changes exactly once, at the edge next to `C`, or exactly once at the edge next to
`D` when going the other way. Contradiction with `N u = N v`. The iff combines this with PT1.

*Interlacing.* Mixed form: choose the arcs so that the open path's ends lie in `A` and `B` and the
dual path's corners in `C` and `D` (four cases of the cyclic order), then not both. Primal–primal:
if the walks were disjoint, the edges of the second walk would be open and touch no vertex of the
first; the faces around the first walk, between outer faces at its two ends, would form a
dual-open path crossing only edges of the box (restricted ring lemma: at each vertex the faces of
the edges of the box form a connected piece of the four-cycle of faces, because two perpendicular
edges share a face and every vertex has an edge of the box in each direction), contradicting the
mixed form. Dual–dual: if the dual walks were disjoint, open every edge not crossed by the second;
then the second is a dual-open path, and the corners of the faces of the first are joined by open
edges (each edge of a face of the first walk is uncrossed), contradicting the mixed form.

*Pivotal arms.* The primal arms come from `pivotal_localConn_iff` (`Bond/Pivotal.lean`): a
connection inside the box that appears when the edge is added splits at that edge. With the edge
closed there is no left-right crossing, so by box duality there is a bottom-top dual crossing of
`R*`; with it open there is a left-right crossing, so `dualConfig (insert e ω)` has none. These two
dual configurations differ by the dual edge `e*`, which is therefore pivotal for the dual
crossing, and the same splitting gives the dual arms.

## Statement choices compared with the plan

1. **The iff's name** is the plan's `mem_arcCrossing_iff_dualConfig_notMem_arcCrossing`, although
   no `arcCrossing` is defined: both events are spelled inline with PT1's sets (rule 4: they now
   appear in three statements; see "Notes for I2b").
2. **Interlacing hypotheses** are explicit inequalities between positions (one point strictly
   between, the other strictly outside, both orientations), not the draft's `sbtw`: mathlib has no
   `CircularOrder ℤ` instance (`LinearOrder.toCircularOrder` is an `abbrev`), and the
   inequalities feed `omega` directly.
3. **Box positivity.** The primal–primal form holds for every box, as in the plan's draft. The
   mixed and dual–dual forms (not drafted in the plan) assume positive width and height, like quad
   duality: their dual arcs are PT1's.
4. **Pivotal arms are inline.** The plan's `mem_multiArmEventIn_of_pivotal` concludes membership in
   I2b's `multiArmEventTo`, which does not exist yet; `exists_arms_of_pivotal` states the four
   arms with existentials, for I2b to re-export. The primal arms live in `ω \ {e}` and the dual
   arms in `dualConfig (insert e ω)`, in `Duality.lean`'s dual box `R*` (all dual edges between its
   faces, not PT1's restricted ones), because they come from box duality.
5. Nothing was narrowed. No counterexample to a plan statement was found in PT2.

## Not done (left for the rest of PT2)

- **Order invariance on walks** (plan §1.1). The interlacing lemma is the tool; still missing are
  (a) a walk along the boundary of a box between two positions, through exactly the boundary
  points in between; (b) arms that meet the inner boundary only at their first vertex, so that the
  cross-cut "arm `i` reversed, arc of `∂B_{r₁}`, arm `k`" avoids the arms `l, m` (this is I2b's
  "disjointness after the first step"); (c) for the converse direction, the count "exactly one of
  the three pairings of four boundary points interlaces", applied at both radii. Mixed colours need
  the doubled lattice or the mixed interlacing form above.
- **Relative duality** (plan §1.1: quad duality for a configuration modified on the explored edges
  of a wired cluster). Its precise statement depends on A2's exploration. The tools are PT1's
  abstract form `exists_dualConfig_inter_mem_localConn_of_arcs` (any sets `A, B, C, D` with the arc
  properties) and the parity lemmas above, which do not use positions until
  `eq_add_sum_of_perimeterPos`.

## Notes for I2b (shapes of arm events)

- **Dual arms** for which quad duality and interlacing hold are PT1's: paths of faces of
  `Icc (lo - 1) hi` crossing only edges of the box, ending at faces outside the box. With all dual
  edges allowed quad duality fails (PT1's counterexample). Box duality's dual arms (pivotal edges)
  use `Duality.lean`'s dual box instead; an arm-event definition has to say which, or the
  pivotal-arms statement needs a bridge.
- **Landing data.** A primal arm lands at a boundary point (its position); a dual arm lands at an
  outer face, whose boundary corners are one point (a diagonal face at a corner) or two consecutive
  positions; `exists_perimeterPos_eq_add_one_of_mem_dualEdge` gives the boundary edge of a face
  with an edge of the box, oriented by positions. Recording the position of its first corner is
  the natural landing position.
- **Disjointness.** The two primal arms of a pivotal edge lie in different open clusters of
  `ω \ {e}` inside the box, hence are vertex-disjoint; likewise the dual arms. The statement does
  not say so; derive it if `multiArmEventTo` asks for disjoint arms.
- **Rule 4 candidates.** The dual arc `{f | f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi,
  x ∈ Icc f (f + 1) ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico c b}`, the arc crossing event,
  the restricted dual configuration `dualConfig ω ∩ dualEdge '' {e | e ∈ L ∧ ∀ x ∈ e, x ∈ Icc lo
  hi}`, and "two pairs of positions interlace" are each spelled out three or more times now.

## Search

Mathlib: no parity-of-crossings lemma for walks; `Finset.sum_Ico_add_eq_sum_Ico_add_one` (for `ℤ`
intervals), `Finset.sum_ite_eq'`, `Sym2.mem_and_mem_iff`, `Sym2.congr_right` and
`SimpleGraph.Walk.transfer` are used; no `Int.le_induction` exists in this mathlib (induction runs on
a natural offset). Cyclic betweenness: `Mathlib/Order/Circular.lean` (no instance for `ℤ`).
PercLib: `Duality.lean` (telescoping `SimpleGraph.Walk.sum_map_darts_add_zmod_two`, box duality),
`Gluing.lean` (`mem_localConn_edges_of_walk`, `mem_support_of_mem_edge`; its ring lemma was not
reusable, see above), `CrossingSymmetry.lean` (`exists_walk_eq_of_le`,
`mem_localConn_iff_exists_walk`), `Bond/Pivotal.lean` (`pivotal_localConn_iff`,
`not_pivotal_localConn_of_not_internal`); `rg` on `dualEdge`, `perimeterPos` and `Icc lo (hi - 1)`
found no existing lemma with the statements of the new face and outer-face lemmas.

## Sources

As for PT1: the duality of crossings of quadrilaterals as used throughout P. Nolin, *Near-critical
percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper no. 55 (site percolation on
the triangular lattice), and G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.2 for the
four-sides case. The interlacing of crossings and the four arms at a pivotal edge are standard
in both settings; no exact lemma number was checked, and the wiki agent should confirm locators
before citing them. The Lean proofs are parity arguments and do not use planar topology.
