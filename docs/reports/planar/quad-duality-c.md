# Order of arms across radii on ℤ²: advice for the wiki

Advice for the wiki agent on the rest of package PT2 of the arms plan ("PT2b"): **order
invariance of arms**, proved in `PercLib/Models/Planar/Arms/Interlacing.lean` (continued from
PT2, part 1). The second item planned for PT2, **relative duality**, is not stated: its form
depends on the exploration used in the arm-separation package A2 (see "Relative duality").
Everything is proved with only `propext`, `Classical.choice` and `Quot.sound`. No `…Input` is
used, and no tags or definitions were added. No wiki assertion is attached yet; these are tools
for the arm estimates (quasi-multiplicativity, arm separation, the arm-event interface).

## Conventions

As in `quad-duality-a.md` and `quad-duality-b.md`: points of `ℤ²` are `![x, y]`, boxes are
`Set.Icc lo hi`, and a face `f` is the unit square with lower-left corner `f`. Boundary points
carry I2a's `perimeterPos` (counterclockwise from `lo`, values `0` to `P - 1`). Three positions
`a, b, c` are **in counterclockwise order** when

```lean
(a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)
```

(mathlib's `sbtw a b c` for the circular order `LinearOrder.toCircularOrder ℤ`, which is not an
instance; it is written out so that `omega` reads it). Going counterclockwise from `a`, one meets
`b` strictly before `c`.

An **arm** in the statements is a walk `γ` of `ℤ²` (any walk, not necessarily a path) from a
point `s` of `∂I`, the boundary of an inner box `I = Icc lo hi`, to a point `e` of `∂O`, the
boundary of an outer box `O = Icc lo' hi'`, with all vertices in `O` and meeting `I` only at its
first vertex:

```lean
∀ v ∈ γ.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s)
```

The arms of a family are pairwise vertex-disjoint (`∀ v ∈ γ₁.support, v ∉ γ₂.support`).

## Statements as proved

Standing hypotheses: `I` has positive width and height (`lo 0 < hi 0`, `lo 1 < hi 1`) and lies
in the interior of `O` (`lo' + 1 ≤ lo`, `hi + 1 ≤ hi'`).

**Order invariance, three arms** (`cyclicallyOrdered_end_iff`, Interlacing l. 1896). For
pairwise disjoint arms `γ₁, γ₂, γ₃` from `s₁, s₂, s₃ ∈ ∂I` to `e₁, e₂, e₃ ∈ ∂O`: the starts are in
counterclockwise order on `∂I` exactly when the ends are in counterclockwise order on `∂O`. The
arms may touch `∂O` before their end; the ends are their last vertices.

**Order invariance, families** (`cyclicallyOrdered_end_iff_of_pairwise_disjoint`, l. 1943). For
pairwise disjoint arms `γ i : Walk (s i) (e i)`, `i : Fin j`, and all `i, k, l`:

```lean
CCW (perimeterPos lo hi (s i)) (perimeterPos lo hi (s k)) (perimeterPos lo hi (s l)) ↔
  CCW (perimeterPos lo' hi' (e i)) (perimeterPos lo' hi' (e k)) (perimeterPos lo' hi' (e l))
```

(`CCW` the disjunction above, written out in the Lean). So the arms have the same cyclic order,
**with orientation**, at both ends.

**First-hit form** (`cyclicallyOrdered_firstHit_iff`, l. 1701). The same for arms that meet `∂O`
only at their last vertex. This is the form for "first hits of any `∂B_{r₂}`": the part of an arm
up to its first hit of the boundary of an intermediate box is such an arm for that box
(`SimpleGraph.Walk.exists_append_eq_of_mem` splits a walk at its first vertex in a set). With
`cyclicallyOrdered_end_iff` this gives the plan's statement: the same cyclic order on `∂B_{r₁}`, on
`∂B_{r₃}` and at the first hits of every `∂B_{r₂}`, `r₁ < r₂ ≤ r₃`.

**Core step** (`not_cyclicallyOrdered_of_cyclicallyOrdered`, l. 1314). If the starts `s₁, s₂, s₃`
are counterclockwise, `γ₂` meets `∂O` only at `e₂`, and `e₃` is not the boundary point just
before `e₂`, then `e₁` is not strictly between `e₂` and `e₃` counterclockwise.

**Same side** (`cyclicallyOrdered_of_cyclicallyOrdered_of_disjoint`, l. 1586). Two disjoint walks
in a box with all four ends on the boundary: if `a, b` follow `u` counterclockwise (the ends of the
first walk, the start of the second), they follow `w` (its end). Any box.

**Supporting results**, each usable on its own:

- *Left side of a path.* `mem_localConn_of_mem_dualEdge_left` (l. 804): at a vertex `v` of the
  interior of a box, for steps `u → v → w` with `w ≠ u` and no other edge of `η` at `v`, the faces
  on the left of the two steps are joined around `v` by dual edges of closed edges of the box
  (a left turn: the same face; straight on: one dual step; a right turn: two).
  `mem_localConn_of_isPath_left` (l. 912): along a path whose inner vertices are in the interior
  and touch no other edge of `η`, the face on the left of the first step is joined to the face on
  the left of every step. `exists_mem_boxBoundary_localConn_left` (l. 1254): for a path entering
  the interior from a boundary point `e`, the outer face of the boundary edge just before `e` is
  joined to the left of every step. The face on the left of `u → v` is the face of `{u, v}` with
  the corner `u + L(v - u)` (`L` the counterclockwise quarter turn): `eq_of_mem_dualEdge_of_mem_Icc_left`,
  `exists_mem_dualEdge_left`.
- *Walking along the boundary.* `exists_walk_boundary` (l. 1044): `n` steps counterclockwise
  from a point, through the positions `t, …, t + n` modulo `P`, each step joining consecutive
  positions; `exists_walk_boundary_of_ne` (l. 1102): between two distinct boundary points, every
  vertex is one of them or strictly between them counterclockwise. `adj_of_perimeterPos_eq_add_one`
  (consecutive positions are neighbours), `exists_mem_boxBoundary_perimeterPos_eq_add_one` (every
  boundary point has a successor), `exists_notMem_Icc_mem_dualEdge_of_perimeterPos_eq_add_one` (a
  boundary edge has a face outside), `mem_Icc_sub_one_of_perimeterPos_eq_add_one` (walking
  counterclockwise, the face on the left is inside), `mem_boxBoundary_of_adj_of_mem_Icc` (the
  point on the left of a step inward from `e` is the boundary point just before `e`).
- *Faces of a box are joined* (`mem_localConn_of_mem_Icc_sub_one`, l. 1151) when every edge of
  `η` has a face outside the box; `notMem_Icc_of_mem_dualEdge_of_mem_edges`: the faces of the edges
  of a walk meeting a box only at its first vertex lie outside the box.
- *First hit of a set* (`SimpleGraph.Walk.exists_append_eq_of_mem`, general graphs): a walk ending
  in `S` is a walk to its first vertex in `S` followed by the rest.

## Proofs the Lean follows

*Core step.* Let the starts be counterclockwise and suppose `e₁` lies strictly between `e₂` and
`e₃`. Replace `γ₂` by a path (`Walk.bypass`). The cross-cut `Q` = (`γ₂` reversed, the
counterclockwise arc of `∂I` from `s₂` to `s₃`, `γ₃`) is a walk in `O` from `e₂` to `e₃`; it avoids
`γ₁`, because the arc does not contain `s₁` (the starts are counterclockwise). Open exactly the
edges of `Q`. (1) The face on the left of the first arc step `s₂ → t₂` lies inside `I`: walking
counterclockwise along `∂I`, the inside is on the left. (2) Going back along `γ₂` from `e₂`, the
faces on the left of the path "`γ₂` reversed, then `s₂ → t₂`" are joined to each other without
crossing `Q`, and the first of them is joined to the outer face of `O` just before `e₂` (its corner
`x` has position `pos e₂ - 1`). (3) The faces inside `I` are joined (no edge of `Q` has both faces
inside `I`). (4) The ring of faces around `γ₁` joins a face inside `I` at `s₁` to an outer face at
`e₁`. So a dual path crossing no edge of `Q` joins the outer face at `x` to the outer face at `e₁`.
When `e₃` is not the point just before `e₂`, the corners `x` and `e₁` separate `e₂` from `e₃`, and
the mixed interlacing lemma forbids this. Topologically: `Q` runs counterclockwise along `∂I`, so
`I` is on its left, and `γ₁` leaves `I` on that side.

*Three arms meeting `∂O` only at their end.* If the starts are counterclockwise and the ends are
not, the ends are in the other order, and of the three gaps between consecutive ends one is not
empty (the perimeter is at least `4`); the core step for the matching rotation of the labels gives
a contradiction. The converse follows by swapping two arms.

*General arms.* Cut each arm at its first hit `hᵢ` of `∂O`. The prefixes give the counterclockwise
order of `h₁, h₂, h₃`. Then exchange `hᵢ` for `eᵢ` one arm at a time with the same-side lemma: the
rest of arm `1` (from `h₁` to `e₁`) does not cross the cross-cut built from the prefixes of arms
`2`, `3` and the arc of `∂I` between `s₂` and `s₃`; then the rest of arm `2` against the prefix of
arm `3`, an arc and the whole arm `1`; then the rest of arm `3` against arms `1`, `2` and an arc.

*Same side.* If the end `w` were on the other side of `{a, b}` than `u`, the pairs would interlace
and the primal–primal interlacing lemma would give a common vertex.

## Statement choices and a correction to the plan's route

1. **The plan's route gives the order only up to reflection.** Plan §1.1 proves order invariance
   from the interlacing lemma: for arms `i, k, l, m`, the arcs between the starts of `i, k` each
   contain one start of `l, m` exactly when the ends interlace. That is invariance of the
   *interlacing pattern* of every four arms. The pattern is unchanged by a reflection (four points
   in the order `1, 2, 3, 4` and in the order `4, 3, 2, 1` have the same interlaced pairs), and for
   three arms there is nothing to compare. So the route determines the cyclic order only up to
   reflection. The full statement (with orientation) is true and is what is proved here. The extra
   ingredient is the left side of a path, a local fact; no definition was needed. The interlacing
   pattern for four arms follows from the family statement by position arithmetic.
2. **One colour.** The arms are walks of `ℤ²`. Dual arms and mixed families reduce to this
   statement in the doubled lattice once I2b fixes the encoding of dual arms (see "Notes for I2b").
3. **Inner box.** `I` must have positive width and height and lie inside the interior of `O`. The
   case `r = 0` (all arms from one vertex) is not covered directly; see "Notes for I2b".
4. **Arms touch `I` only at their start, and may touch `∂O` anywhere.** The ends are the last
   vertices. The first-hit form adds "meets `∂O` only at its last vertex".
5. **Many hypotheses.** The three-arm theorems have about twenty hypotheses (ends, boxes,
   containment and disjointness of three arms). A structure or predicate for arms is an interface
   matter (rule 11); I2b's arm predicate should bundle them and re-export these theorems.
6. **Names.** The plan's `cyclicallyOrdered_firstHit_iff` is kept for the first-hit form; the form
   for last vertices is `cyclicallyOrdered_end_iff`.
7. Nothing was narrowed. No plan statement was found false.

## Relative duality (not stated; left to A2)

Plan §1.1: "quad duality applied to a configuration modified on the explored edges of a finite
wired cluster: the explored cluster acts as a wired boundary arc"; §1.2 and §2.3 (b), (c) use it to
find the next extremal crossing from the explored set alone, and to see that later events
(protecting circuits) live in unexplored edges. Its statement depends on choices A2 has not made
yet: which clusters are explored (the dual cluster of a side, then the open cluster of the
boundary crossing, alternately), in which region (the strip `[0, 4N] × [0, N]` or a box), and
whether the explored cluster is wired into an arc (configuration `ω ∪ E(K)`) or removed (`ω \ E(K)`)
or handled in the dual. Fixing it now would mean choosing those for A2. The pieces it will be
built from:

- `mem_arcCrossing_iff_dualConfig_notMem_arcCrossing` (QuadDuality l. 1612) applied to the
  modified configuration: the "relative" statement is a direct application once the modification
  is fixed. The work is in freshness (`prodBernoulli_inter_of_determined`) and in describing the
  dual crossing by unexplored edges.
- **Template: `RSWKeyStep.lean`.** `mem_crossing_one_boundary` (the edges separating an explored
  dual set `D₀` from its complement contain a crossing; proved from box duality on the
  deterministic configuration `∂D₀`, with `Walk.exists_boundary_dart`) and `exists_walk_unexplored`
  (every crossing reaches the chosen crossing through unexplored edges) are relative duality for
  the four-sides case. The arc version of `mem_crossing_one_boundary` (an explored dual set
  containing the dual arc of `C` and avoiding that of `D` has an open `A`–`B` crossing in its
  boundary edges) follows from the iff by the same argument. It is the first statement A2 will want.
- PT1's abstract form `exists_dualConfig_inter_mem_localConn_of_arcs` (any sets `A, B, C, D` with
  the arc properties), when the wired explored cluster replaces an arc.

## Notes for I2b (shapes of arm events)

What order invariance needs, and what makes re-exporting it cheap:

- **Leave the inner box at the first step, never return.** The theorems assume
  `∀ v ∈ γ.support, v ∈ Icc (z - r) (z + r) → v = start` and `start ∈ boxBoundary (z - r) (z + r)`.
  The plan's `IsOpenArm` condition `∀ v ∈ γ.support.tail, v ∉ Icc (z - r) (z + r)` (with the start
  in `B_r(z)`) gives this when the start is on `∂B_r(z)`. Require the start on the boundary, or
  derive it (the second vertex is outside `B_r`, so the start is on `∂B_r`).
- **Landing at the last vertex is fine.** `cyclicallyOrdered_end_iff` compares last vertices, so
  arms need not stop at their first hit of the outer boundary. Stopping there (first-hit arms) is
  harmless too: the first-hit form then applies with fewer steps.
- **Counterclockwise order of a family.** The theorems state the order by triples. If
  `multiArmEventTo` uses the plan's `∃ k, StrictMono (pos ∘ (finRotate j) ^ k)`, I2b should add the
  bridge "for injective positions, some rotation is strictly increasing iff every increasing
  triple `i < k < l` is counterclockwise" (pure combinatorics on `Fin j → ℤ`), so that A1
  re-exports `cyclicallyOrdered_end_iff_of_pairwise_disjoint` directly. Defining the order by
  triples avoids the bridge.
- **`r = 0`.** Arms from one vertex `z` share their start and may re-enter `B_1(z)`. The theorem
  applies to the parts after the *last* visit of `B_{r₂}(z)` for any `r₂ ≥ 1`: those are disjoint,
  start on `∂B_{r₂}` and meet `B_{r₂}` only at their start. So for `r = 0` the order is invariant
  between last exits of `B_{r₂}` and the landing points, for every `r₂ ≥ 1`. The order at
  radius `0` itself is not defined by positions.
- **Disjointness is vertex-disjointness of whole walks** (starts included) for `r ≥ 1`.
- **Dual arms and mixed colours (doubled lattice).** Order invariance for families with dual
  arms reduces to the theorem on the doubled lattice: a primal walk `v₀ v₁ …` becomes
  `2v₀, v₀ + v₁, 2v₁, …`, and a dual walk of faces `f₀ f₁ …` becomes `2f₀ + 1, f₀ + f₁ + 1,
  2f₁ + 1, …` (`+ 1` is `(1, 1)`; `f₀ + f₁ + 1` is the midpoint of the primal edge crossed). An open
  arm and a dual-open arm of the same configuration share no doubled vertex. For the doubled arms
  to start on `∂(2 B_r(z))` and meet `2 B_r(z)` only there, a dual arm should consist of faces not
  inside `B_r(z)`, with its first dual edge crossing an edge of `∂B_r(z)`, and the doubled walk
  should start at that edge's midpoint. It should land at the midpoint of the boundary edge of the
  outer box crossed by its last dual edge (as plan §8.2). Positions on the doubled outer box are
  then `2 · pos b` for a primal landing `b` and `2 · pos x + 1` for a dual landing across the
  boundary edge `{x, next x}`. A1 needs a walk-doubling lemma (support, disjointness, positions);
  no new topology.
- **Which dual arms.** As noted in `quad-duality-b.md`, quad duality and the mixed interlacing
  lemma hold for dual paths crossing only edges of the box (faces in `Icc (lo - 1) hi`). The
  encoding above (faces outside `B_r`, inside the outer face box, crossing edges of the annulus)
  is of that kind.
- **Rule-4 candidates** (each now spelled out many times): "three positions in counterclockwise
  order" (the disjunction above, about fifteen times in `Interlacing.lean`), the arm condition
  (support in `O`, meeting `I` only at the start), and "the face on the left of a step"
  (`f ∈ dualEdge s(u, v) ∧ ![u 0 + u 1 - v 1, u 1 + v 0 - u 0] ∈ Icc f (f + 1)`). The earlier
  candidates of `quad-duality-b.md` (dual arc, arc crossing, restricted dual configuration,
  interlacing of position pairs) stand.

## Search

Mathlib: `SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges` (the edges of a path at its start, used),
`Walk.bypass` with `bypass_isPath`, `support_bypass_subset_support`, `edges_bypass_subset_edges`,
`IsPath.concat`, `Walk.exists_eq_cons_of_ne`, `IsPath.reverse`, `mem_support_append_iff`.
`Walk.takeUntil`/`dropUntil` split at a given vertex, not at the first vertex of a set, and
`Walk.exists_boundary_dart` finds a dart leaving a set; hence `exists_append_eq_of_mem`.
`Mathlib/Order/Circular.lean` (`sbtw`, no instance on `ℤ`). Mathlib has no discrete Jordan-curve or
left-side-of-a-path lemma for `ℤ²`. PercLib: `RSWKeyStep.exists_walk_first_mem` gives only the
prefix up to a first visit and is not imported by `Interlacing.lean`; `exists_append_eq_of_mem`
also gives the rest of the walk and could replace it. `RSWKeyStep.exists_dualEdge_eq` (the primal
edge of a dual edge) is also not imported, and its two-line argument appears inline in
`mem_localConn_of_mem_Icc_sub_one`. `CrossingSymmetry`'s `Walk.exists_walk_eq_of_le`, Interlacing's
ring lemmas and QuadDuality's outer-face lemmas (`exists_notMem_Icc_of_perimeterPos`,
`mem_edgeSet_and_mem_dualEdge_of_notMem_Icc`) are reused. `rg` on `perimeterPos`, `dualEdge` and
"left" found no existing lemma with the statements of the new ones.

## Sources

The cyclic order of disjoint arms across annuli is used throughout P. Nolin, *Near-critical
percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper no. 55 (separation of arms,
quasi-multiplicativity), and H. Kesten, *Scaling relations for 2D-percolation*, Comm. Math. Phys.
109 (1987), usually as a consequence of the Jordan curve theorem. No exact lemma number was
checked; the wiki agent should confirm locators before citing them. The Lean proof uses quad
duality (a parity argument) and the local left-side lemma, not the Jordan curve theorem.
