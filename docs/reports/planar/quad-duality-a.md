# Quad duality on ℤ², at least one: advice for the wiki

Advice for the wiki agent on package PT1 of the arms plan
(`PercLib/Models/Planar/Arms/QuadDuality.lean`): the "at least one" half of quad duality, the
planar tool of plan §1.1 from which the interlacing lemma, order invariance of arms and relative
duality are to be derived (package PT2 and later). For a box and four boundary points cutting its
boundary into arcs `A, C, B, D`, if no open path in the box joins `A` to `B`, then a dual-open
path joins the dual arcs of `C` and `D`. The "not both" half and the "exactly one" statement are
PT2. Everything is proved with only `propext`, `Classical.choice` and `Quot.sound`; no `…Input`
is used, and no tags and no definitions were added. No wiki assertion is attached to this
statement yet; it is a tool for the arm estimates.

## Conventions

As in `duality.md` and `arms-interface-a.md`: a point of `ℤ²` is `![x, y]`, boxes are
`Set.Icc lo hi` on `Fin 2 → ℤ`, and `(1 : LatticeSite 2)` is the constant vector `1`, so
`Icc lo (hi - 1)` and `Icc (lo - 1) hi` are boxes shrunk and grown by one. Only the open
nearest-neighbour edges `ω ∩ (zdGraph 2).edgeSet` are read, and "joined inside `S`" is
`ω ∩ (zdGraph 2).edgeSet ∈ localConn S u v`. A **face** is a dual vertex: `f` stands for the unit
square with lower-left corner `f`, so `x` is a corner of `f` when `x ∈ Icc f (f + 1)`. The faces
inside the box `R = Icc lo hi` form `Icc lo (hi - 1)`, and the faces touching `R` (the faces of
`R` and the ring around it) form `Icc (lo - 1) hi`.

- **Boundary positions.** `boxBoundary lo hi` and `perimeterPos lo hi` are I2a's: positions run
  counterclockwise from `lo`, from `0` to `P - 1`, where `P = 2 (hi₀ - lo₀) + 2 (hi₁ - lo₁)` is the
  perimeter.
- **Arcs.** For `a < c < b < d < P + a` and positions read modulo `P`, the arc `[x, y)` is the set
  of boundary points `u` with `perimeterPos lo hi u + k * P ∈ Ico x y` for some integer `k`. The
  four arcs are `A = [a, c)`, `C = [c, b)`, `B = [b, d)`, `D = [d, P + a)`; every boundary point
  lies in exactly one of them, and each contains at least one point.
- **Dual arc** of an arc: the faces not inside `R` (not in `Icc lo (hi - 1)`) with a corner in
  the arc. For `C` these are the faces just outside `R` along `C`, including the outer faces of
  the two boundary edges joining `C` to `A` and to `B` (and, if a corner of `R` lies in `C`, the
  diagonal face outside that corner).
- **Dual box and dual paths.** A dual-open path in the dual box is a path of faces of
  `Icc (lo - 1) hi` each step of which crosses an edge of `R` (both ends in `R`) that is closed in
  `ω`. In Lean it is open in the configuration
  `dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi}`.

## Statements as proved

**Quad duality, at least one** (`exists_dualConfig_inter_mem_localConn_of_not_exists`). For a box
of positive width and height, `a < c < b < d < P + a` and every configuration `ω`: if no point of
`A` is joined inside `R` to a point of `B`, then some face of the dual arc of `C` is joined to some
face of the dual arc of `D` by a dual-open path in the dual box. In Lean:

```lean
theorem exists_dualConfig_inter_mem_localConn_of_not_exists {lo hi : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {a c b d : ℤ}
    (hacbd : a < c ∧ c < b ∧ b < d ∧ d < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)
    {ω : Config (LatticeSite 2)}
    (hω : ¬ ∃ u v, u ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi u + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico a c) ∧
      v ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi v + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico b d) ∧
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v) :
    ∃ f g, (f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc f (f + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico c b) ∧
      (g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc g (g + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈
          Ico d (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)) ∧
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g
```

For `hi₀ - lo₀ ≥ 2` the four sides of `R` are the special case `A` = left side, `B` = right side
(corners included), `C` and `D` the bottom and top sides without their corners
(`a = -(hi₁ - lo₁)`, `c = 1`, `b = hi₀ - lo₀`, `d = (hi₀ - lo₀) + (hi₁ - lo₁) + 1`); the dual arcs
are then the rows of faces below and above `R`, as in
`mem_crossing_one_dualConfig_of_notMem_crossing_zero`. (For width one, `C` and `D` would be
empty, which `a < c < b < d < P + a` excludes; `Duality.lean` covers that case.)

**Supporting results**, each usable on its own:

- `exists_dualConfig_inter_mem_localConn_of_arcs`: the parity argument for any four sets of
  points `A, B, C, D` covering the boundary, with `A, C, D` in the box, no face outside the box
  having corners in both `A` and `B`, and a single corner `(v₀, f₀)` with `v₀ ∈ A` and `f₀` a
  face outside the box with corners in `A` and `C`, one of whose two edges at `v₀` leaves the box.
  This form does not mention perimeter positions; it may serve relative duality (an explored
  cluster as a wired arc), where the arcs are not intervals of positions.
- `perimeterPos_eq_add_one_or_of_notMem_Icc`: two distinct boundary points that are corners of
  one face outside the box are neighbours on the boundary (positions differ by one modulo `P`).
- `eq_of_notMem_Icc_sub_one`: a face outside the box is determined by two distinct corners of it
  in the box.
- `exists_notMem_Icc_of_perimeterPos`: the boundary points at positions `p` and `p + 1` (modulo
  `P`) and the outer face of the boundary edge joining them.
- `Finset.apply_mem_of_involutive_of_mapsTo` (general): if two fixed-point-free involutions
  `φ, ψ` are such that `φ` maps a finite set `S` into itself and `ψ` maps `S` minus one element
  `J` into `S`, then `ψ J ∈ S`.
- Small facts on faces and boxes (`mem_Icc_of_mem_Icc_sub_one`, `mem_Icc_sub_one_of_mem_Icc`,
  `mem_boxBoundary_of_notMem_Icc`, `cornerVertex_add`, `cornerFace_add`,
  `mem_Icc_cornerFace_of_mem_cornerHEdge`, …) and positions modulo `P`
  (`Int.exists_add_mul_mem_Ico_iff`, `Int.exists_add_mul_mem_Ico_sub_mul_iff`).

## Proof the Lean follows

The parity argument of `duality.md` ("at least one"), with arc-dependent wiring and extreme
corners. A *corner* is a pair (vertex `v`, face `f`) with `v` a corner of `f`, encoded by
`s = v + f`; the involutions `hPartner ω'` and `vPartner ω'` move a corner along the horizontal or
vertical edge of its face through its vertex: the vertex moves if that edge is open in `ω'`, the
face moves across it if it is closed.

1. *Wiring.* `ω'` keeps the open edges of `ω` inside `R`, opens every edge all of whose points in
   `R` lie in `A` (edges inside `A`, edges leaving `R` from `A`), likewise for `B`, and closes the
   other edges leaving `R` (those leaving from `C` or `D`).
2. *Corners.* `K` is the finite set of corners whose vertex lies in `R` and whose face lies inside
   `R` or in the dual arc of `C` or of `D`. A partner of a corner of `K` lies outside `K` only
   when the vertex moves out of `R` along an open edge, an edge leaving `R` from `A` or `B` (a face
   moving across a closed edge always lands inside `R` or in a dual arc: a closed boundary edge
   has an end in `C` or `D`, because `A` and `B` are not neighbours and edges inside them are
   open; a closed edge leaving `R` leaves from `C` or `D`, and both faces at it then have a corner
   there).
3. *The counted set.* Suppose neither crossing exists. Let `S` be the corners of `K` whose vertex
   is joined to `A` inside `R` and whose face is joined to the dual arc of `C` by a dual-open path.
   A partner of a corner of `S` that lies in `K` lies in `S`: an open step stays joined to `A` (a
   wired step inside `B` would join `A` to `B`); a closed step inside `R` is a dual step; a closed
   step leaving `R` from `C` lands in the dual arc of `C` (from `D` the face would join the two
   dual arcs).
4. *The one exceptional corner.* A corner of `S` with a partner outside `K` has its vertex in `A`
   (not `B`: that would join `A` to `B`) and its face in the dual arc of `C` (not `D`). That face
   has corners in `A` and in `C`, two neighbours on the boundary, so it is the outer face of the
   boundary edge from the last point of `A` to the first point of `C`, and the corner is the one
   at that junction. It lies in `S`, and exactly one of its partners leaves `K`: the one across
   the edge leaving `R` (the other crosses the boundary edge).
5. *Counting.* One partner map pairs off `S`, so `|S|` is even; the other pairs off `S` without
   the junction corner, so `|S| - 1` is even. Contradiction.

The other three junction corners (between `C` and `B`, `B` and `D`, `D` and `A`) are not in `S`,
since each would give one of the two crossings; the Lean never needs to name them.

## Statement choices compared with the plan

The plan's §2.1 draft leaves `dualBox` and `dualArc` to PT1 ("inline set-builders"). The choices,
with the reasons:

1. **Positive width and height** (`h₀ : lo 0 < hi 0`, `h₁ : lo 1 < hi 1`) instead of the draft's
   `lo ≤ hi`. On a segment `perimeterPos` runs along the boundary only once (I2a's
   `perimeterPos_rotate` makes the same restriction), so the positions in `(hi₀ - lo₀, P)` (for a
   horizontal segment) belong to no boundary point and an arc can be empty. Counterexample to "at
   least one": the segment `[0, 3] × {0}`, `P = 6`, `a, c, b, d = 4, 5, 6, 7`; `A` and `C`
   contain no point, `B = {(0, 0)}`, `D = {(1, 0), (2, 0), (3, 0)}`; with every edge open there is
   no open crossing (`A` is empty) and no dual crossing (no dual edge is open and the dual arc of
   `C` is empty). The sources' quadrilaterals are genuine rectangles, so this is not a hypothesis
   the sources lack; every box used by the arm estimates has positive width and height.
2. **Positions modulo `P`** are written `∃ k : ℤ, perimeterPos lo hi u + k * P ∈ Ico a c`. The
   draft's `perimeterPos lo hi u ∈ Ico a c` is only right for `0 ≤ a` and `d ≤ P`; the plan says
   "positions read mod `P`". Mathlib's `toIcoMod` would also do, but it needs a proof of `0 < P`
   inside the statement.
3. **The dual box and dual arcs.** The dual box is `Icc (lo - 1) hi` (the faces of `R` and the
   ring around it, as the plan says) and the dual arc of an arc is the set of faces not inside `R`
   with a corner in the arc.
4. **Dual edges crossing edges of `R` only.** The dual path is open in
   `dualConfig ω ∩ dualEdge '' {edges with both ends in R}`, not in `dualConfig ω ∩ L`. With all
   dual edges allowed, "not both" (hence the plan's iff) is false whenever `A` or `B` is a single
   point that is not a corner of `R`: in the box `[0, 2] × [0, 1]` (positions `(0,0) ↦ 0`,
   `(1,0) ↦ 1`, `(2,0) ↦ 2`, `(2,1) ↦ 3`, `(1,1) ↦ 4`, `(0,1) ↦ 5`) take `A = {(1, 0)}` (`[1, 2)`),
   `C = [2, 4)`, `B = {(1, 1)}` (`[4, 5)`), `D = [5, 7)`, and `ω` = the single edge
   `{(1, 0), (1, 1)}`. Then `A` is joined to `B`, while the face `(0, -1)` (corner `(0, 0) ∈ D`) and
   the face `(1, -1)` (corner `(2, 0) ∈ C`) are joined by the dual edge crossing the closed edge
   `{(1, -1), (1, 0)}` outside `R`. With the restriction both events depend only on the edges of
   `R`, and the outer faces of the ring become dead ends of the dual graph (one step into `R`), so
   including the whole ring in the dual box is harmless. For the "at least one" half proved here
   the restriction makes the statement stronger.
5. **Only the implication** is proved, as PT1's scope; the name follows the conclusion
   (`exists_…_mem_localConn`) and the hypothesis (`of_not_exists`). The plan's iff
   `mem_arcCrossing_iff_dualConfig_notMem_arcCrossing` is for PT2, with the same inline sets.

No definition was needed. `dualArc` and the restricted dual configuration are now spelled out in
one statement; PT2's iff and the interlacing lemma will spell them out again, which is the rule-4
signal for a small interface package (I2b is the natural place: `dualArc`, `arcCrossing`, and a
name for the configuration of dual edges crossing edges of a box).

## Notes for PT2 (not both, and the iff)

- "Not both" must be proved for exactly these sets. In the restricted dual graph a face of the
  ring has at most one neighbour (the face inside `R` across its boundary edge), and a diagonal
  face outside a corner of `R` has none, so a dual path from the dual arc of `C` to that of `D`
  can be taken to be a step across a closed boundary edge from `C`'s dual arc, a path of faces
  inside `R`, and a step across a closed boundary edge into `D`'s dual arc (it is never a single
  face: the two dual arcs are disjoint).
- The plan's reference-path parity applies to that inner path; the parity is to be constant on
  each primal arc, and the two closed boundary edges where the dual path enters and leaves `R`
  are the only boundary crossings.
- `exists_notMem_Icc_of_perimeterPos` and `perimeterPos_eq_add_one_or_of_notMem_Icc` are the
  coordinate lemmas for walking along the boundary by positions; they took one `omega` per side.

## Where it is used

PT2 (not both, the iff, the interlacing lemma, order invariance of arms across radii, pivotal
edges carrying four alternating arms, relative duality), then A2's surgery (protecting circuits in
unexplored edges) through relative duality.

## Search

Mathlib: no parity lemma for two involutions on a finite set (searched `Finset`, `BigOperators`,
`GroupTheory/Perm` and `Combinatorics` for involution together with card or `Even`); the proof
uses `Finset.sum_involution` in `ZMod 2`, as `Duality.lean` does. The reduction of positions
modulo `P` is elementary; mathlib's `toIcoMod` was considered for the statement (choice 2). The
facts on boxes of faces are one-line order facts on `Fin d → ℤ`; no PercLib lemma with these
statements was found by `rg` on `Icc`, `sub_one` and `boxBoundary`. PercLib lemmas reused: the corner
lattice (`cornerVertex`, `cornerFace`, `hPartner`, `vPartner` and their API in `Defs.lean`;
`cornerFace_hPartner_of_mem`, `sym2_cornerVertex_hPartner_of_mem`,
`sym2_cornerFace_hPartner_of_notMem` and their vertical versions, and
`mem_localConn_of_mem_localConn_of_mem` in `Duality.lean`), `dualEdge_mem_dualConfig_iff`, and
I2a's `boxBoundary` and `perimeterPos` API (`mem_boxBoundary_two_iff`, `perimeterPos_nonneg`,
`perimeterPos_lt`, `perimeterPos_injOn`).

## Sources

The statement is the square-lattice form of the duality of crossings of quadrilaterals used
throughout P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008),
paper no. 55 (stated there for site percolation on the triangular lattice, where it is
self-matching); the four-sides case is G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.2
"Planar duality" (pp. 283–286, section title checked as recorded in `duality.md`). No exact lemma
number was checked in either text; the wiki agent should confirm locators before citing them.
The textbook proofs follow the boundary of a cluster (a discrete Jordan-curve argument); the Lean
proof is the parity argument above and does not use planar topology.
