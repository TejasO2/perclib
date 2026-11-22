# Colour inversion of multi-arm events at one half: advice for the wiki

Advice for the wiki agent on the last item of package A1 of the arms plan (A1c). It is proved in
the new file `PercLib/Models/Planar/Arms/ColourInversion.lean` (575 lines, 17 theorems), which
imports `Arms/MultiArmBounds.lean`. The file is proof-only: it adds no definition and no tag, and
`Arms/Defs.lean` and `Planar/Defs.lean` are unchanged. Everything uses only `propext`,
`Classical.choice` and `Quot.sound`, and no `…Input` is used.

With this file the required items of A1 are done (A1: items 1, 2, 3, 5; A1b: items 6, 8, 9; A1c:
item 7). Only the optional item 4 is not done (see "Not done here"). No wiki assertion is attached
yet. Colour inversion is a tool for the universal exponents (U1, U2): at `1/2` it turns a bound
proved for one colour sequence into a bound for the inverted sequence.

## Conventions

As in `multi-arm-basics.md` and `multi-arm-bounds.md`:

* points of `ℤ²` are `![x, y]`, boxes are `Set.Icc lo hi`, `B_r(z) = Icc (z - r) (z + r)`;
* the face `f` is the unit square with lower-left corner `f`;
* `π_σ(r, R)` is the probability of `multiArmEvent σ z r R`;
* three integers are in counterclockwise order when `sbtw a b c` (mathlib's `CircularOrder ℤ`);
* in the doubled lattice a point `v` becomes `2v`, a face `f` its centre `2f + (1, 1)`, and an
  edge its midpoint, the sum of its ends.

## Statements as proved

**Colour inversion at one half** (`law_multiArmEvent_comp_not_le`), the plan's statement:

```lean
theorem law_multiArmEvent_comp_not_le {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {j : ℕ} (σ : Fin j → Bool)
    (z : LatticeSite 2) {r R : ℕ} (h : r + 2 < R) :
    law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent (not ∘ σ) z (r + 1) (R - 1))
```

So `π_σ(r, R) ≤ π_{not ∘ σ}(r + 1, R - 1)`. The hypothesis on `q` is on the edges of `ℤ²` only;
the value of `q` on other pairs is free.

**The deterministic inclusion** (`dualConfig_mem_multiArmEvent`), for every configuration `ω`:

```lean
theorem dualConfig_mem_multiArmEvent (h : r + 2 < R) (hω : ω ∈ multiArmEvent σ z r R) :
    dualConfig ω ∈ multiArmEvent (not ∘ σ) z (r + 1) (R - 1)
```

**Order invariance for walks inside the doubled arms** (`sbtw_innerPos_iff_sbtw_perimeterPos`).
Suppose:

* `B_r(z)` lies in the interior of `Icc lo hi`, and `γ` is a disjoint family of arms of colours
  `σ` from `B_r(z)` to the boundary of `Icc lo hi`;
* `Icc lo' hi'` is a box of the doubled lattice whose interior contains the doubled inner box
  `2z + [-(2r + 1), 2r + 1]²`;
* for each `i`, `P i` is a walk of the doubled lattice from the start of the doubled arm `i` (the
  point of its inner position) to a point `e i` on the boundary of `Icc lo' hi'`, through points
  of the doubled arm `i` only, inside `Icc lo' hi'`.

Then three arms have their inner positions in counterclockwise order exactly when the points
`e i` are in counterclockwise order on the boundary of `Icc lo' hi'`. This is the plan's
"first-hit form" for arms of both colours stopped at an intermediate box, in a form that does
not require the walks to stop at their first exit.

**Inverting one arm** (`IsArm.exists_dualConfig`, from `IsOpenArm.exists_isDualArm_dualConfig`
and `IsDualArm.exists_isOpenArm_dualConfig`). An arm of `ω` of colour `c` from `B_r(z)` to the
boundary of `B_{R+1}(z)`, with `r + 1 < R`, contains an arm of `dualConfig ω` of colour `!c` from
`B_{r+1}(z)` to the boundary of `B_R(z)`:

* an open arm, started at its last vertex in `Icc (z - r - 1) (z + r + 2)` and stopped at its
  first vertex outside `Icc (z - R + 1) (z + R)`, then translated by `(-1, -1)`, is a dual arm of
  `dualConfig ω`; its vertices, translated back, lie in the tail of the open arm;
* a dual arm, started at its last face in `Icc (z - r - 1) (z + r + 1)` and stopped at its first
  face outside `Icc (z - R + 1) (z + R - 1)`, is an open arm of `dualConfig ω`; its faces are faces
  of the dual arm.

The theorem also gives the walk `P` of the previous paragraph: from the start of the doubled arm
to the point whose position on the boundary of `Icc (2 (z - R) + 1) (2 (z + R) + 1)` is the
landing position of the new arm.

**Tools**, also usable elsewhere:

* `isDualArm_dualConfig_map_of_isCrossing`: a walk of `ℤ²` along open edges crossing from
  `Icc (z - r) (z + r + 1)` out of `Icc (lo + 1) hi`, translated by `(-1, -1)`, is a dual arm of
  `dualConfig ω` (the converse direction of I2b's `isDualArm_dualConfig_iff`, stated for the
  translated walk);
* `exists_walk_double_tail_dropLast`: the doubled walk without its first and last vertices, from
  the midpoint of the first step to the midpoint of the last step;
* `mem_Icc_of_isCrossing`: a walk crossing out of `Icc (lo + 1) (hi - 1)` lies in `Icc lo hi`;
* coordinate facts on the doubled box `Icc (2 lo + 1) (2 hi + 1)`: `add_mem_Icc_of_adj`,
  `add_mem_boxBoundary_of_adj`, `two_nsmul_add_one_mem_Icc`,
  `two_nsmul_add_one_mem_boxBoundary`;
* for walks of any graph (`SimpleGraph.Walk`): `IsCrossing.exists_append_append_eq` (a crossing
  cut at both ends: first exit of a smaller set, then last visit of a larger set),
  `IsCrossing.not_nil_of_mem_tail_support_append`, `mem_tail_support_append_of_mem_support`,
  `mem_dropLast_support_of_mem_of_ne`.

## Proofs the Lean follows

**Why the radii move by one.** The dual of the dual lattice is `ℤ²` shifted by `(1, 1)`
(`dualConfig_dualConfig`). An open arm of `ω` becomes a dual arm of `dualConfig ω` only after the
translation by `(-1, -1)`. I2b's dual arms start at a face touching `B_r(z)` and stop at the first
face outside the faces of the outer box. After the translation these conditions are the
conditions on an open walk to cross from `Icc (z - r) (z + r + 1)` out of `Icc (lo + 1) hi`, which
is not symmetric about `z`. Cutting the open arm at the symmetric boxes
`Icc (z - r - 1) (z + r + 2)` and `Icc (z - R + 1) (z + R)` (new radii `r + 1` and `R`, old outer
radius `R + 1`) satisfies them. For dual arms of `ω` no translation is needed, but their first face
may lie outside `B_r(z)` and their last face outside the outer box, so they are cut too.

**Cutting.** `IsCrossing.exists_append_append_eq` writes the arm as `(q ++ s) ++ t`, where
`q ++ s` stops at the first exit of the smaller outer set and `s` starts at the last visit of the
larger inner set before that. For an open arm the second vertex lies in
`Icc (z - r - 1) (z + r + 2)`, because the first vertex lies in `B_r(z)`. So the last visit comes
after the first vertex, `q` has a step, and `s` lies in the tail of the arm. Then:

* two new dual arms (from two old open arms) share no face, because the tails of the old open arms
  avoid each other;
* two new open arms (from two old dual arms) share no vertex, because the old dual arms share no
  face.

**Order.** Work in the doubled lattice of `ω`, with the intermediate box
`O' = Icc (2 (z - R) + 1) (2 (z + R) + 1)` (new outer radius `R`).

* For an old open arm, the new landing position is
  `perimeterPos (2 (z - R)) (2 (z + R)) (s' + y - 1)`, where `y` is the first exit and `s'` the
  vertex before it. By `perimeterPos_add` it is the position on `∂O'` of the midpoint `s' + y` of
  the exit edge. The walk `P` is the doubled walk of `q ++ s` without its first and last vertices
  (`exists_walk_double_tail_dropLast`). It runs through doubled vertices and midpoints of the open
  arm, inside `O'`, and ends at `s' + y`, which lies on `∂O'` (`add_mem_boxBoundary_of_adj`).
* For an old dual arm, the new landing position is `2 · perimeterPos (z - R) (z + R) y` for the
  first face `y` outside `Icc (z - R + 1) (z + R - 1)`. That is the position on `∂O'` of the
  doubled centre `2y + (1, 1)` (`perimeterPos_add`, `perimeterPos_two_smul`). The walk `P` is the
  full doubled walk of `q ++ s` translated by `(1, 1)` (`exists_walk_double`). Its faces lie in
  `B_R(z)`, so none is the last face of the old arm, which lies outside `Icc (z - R - 1) (z + R)`.
  So `P` runs through the doubled dual arm.

The walks `P i` lie in the doubled arms. So they meet the doubled inner box only at their starts
(`IsArm.exists_double`) and are pairwise disjoint (`IsArm.double_disjoint`). PT2b's
`cyclicallyOrdered_end_iff_of_pairwise_disjoint` therefore applies to them with outer box `O'`,
which is `sbtw_innerPos_iff_sbtw_perimeterPos`. For `i < k < l` the chain is:

* old landing positions in counterclockwise order;
* hence old inner positions in counterclockwise order (`sbtw_innerPos_iff_sbtw_landingPos`);
* hence the points `e i` in counterclockwise order on `∂O'`;
* hence the new landing positions in counterclockwise order.

**Probability.** `multiArmEvent` reads only edges of `ℤ²` (`mem_multiArmEventTo_iff_of_agree`),
so self-duality at one half (`law_preimage_dualConfig_eq`) gives
`law q (dualConfig ⁻¹' A_{not ∘ σ}(r + 1, R - 1)) = π_{not ∘ σ}(r + 1, R - 1)`. The inclusion
gives the inequality.

## Statement choices compared with the plan

1. The plan wrote `π_σ ≤ C π_{not ∘ σ}` ("exact up to the half-lattice shift, absorbed by
   extendability once A3 is done"); the handoff fixed the form proved here, with constant `1` and
   radii `r + 1`, `R - 1`. The shift costs one unit at each radius; once A3 gives
   quasi-multiplicativity, `π_{not ∘ σ}(r + 1, R - 1)` and `π_{not ∘ σ}(r, R)` are comparable, which
   gives the plan's form. This statement is not narrowed: it is the one in the handoff, for every
   `σ`, `z`, `r` and `R` with `r + 2 < R`.
2. `r + 2 < R` is what the proof needs: the new annulus must be nondegenerate,
   `r + 1 < R - 1` (see the monotonicity counterexample in `multi-arm-basics.md`).
3. The deterministic inclusion is stated separately for every configuration. Only the last step
   uses `1/2`.
4. The order lemma takes arbitrary walks inside the doubled arms, not only first-exit cuts. The
   cut points of the open arms are midpoints of edges, which are not points of the doubled walk
   stopped at a vertex, so a lemma about cut arms alone would not apply.

## Not done here

* **Item 4** (optional): nonemptiness of the I2b example sequences for every `R ≥ 1`. Only `R = 1`
  is compiled, in `Arms/Defs.lean`. A route by straight arms:
  * A general straight-walk lemma: for a unit vector `d`, a walk from `v` to `v + (n + 1) • d` with
    penultimate vertex `v + n • d`, whose darts are the steps `v + k • d → v + (k + 1) • d` for
    `k ≤ n`. Build it with `Walk.concat`; describe the darts, because `map_fst_darts`,
    `map_snd_darts` and `edges` then give `dropLast`, the tail and the edges.
  * A crossing criterion stated through the darts.
  * For five arms `OCOOC` at `z = 0`, `r = 0`, the arms are the configuration of the `R = 1`
    example, stretched. The open arms go down, right and up from `0`, and the dual arms go down
    from the faces `(0, -1)` and `(-1, -1)`. The landing positions are `2R, 2R + 1, 6R, 10R,
    2R - 1` on a cycle of length `16R`, which are in counterclockwise order. The order follows
    from `Int.sbtw_iff` and `omega` over the ten triples.
  * `OCOC` in the plane and `OC`, `OCO` in the half-plane are similar.

  This gives D-5 witnesses only; no later package needs it.

## What A2 has from A1, A1b and A1c

* From A1 and A1b: the list in `multi-arm-bounds.md`, §"What A2 has from A1 and A1b".
* From A1c:
  * `sbtw_innerPos_iff_sbtw_perimeterPos`, order invariance at an intermediate box for walks inside
    the doubled arms. This is the form to use when arms are explored or cut inside an annulus
    (A2's exploration stops arms at intermediate boxes);
  * `IsCrossing.exists_append_append_eq`, cutting at both ends;
  * `exists_walk_double_tail_dropLast`;
  * `isDualArm_dualConfig_map_of_isCrossing` for passing between `ω` and `dualConfig ω`.
* Colour inversion itself is not needed by A2. It is needed by U1 and U2.

## Search

* **mathlib**:
  * used: `List.mem_dropLast_of_mem_of_ne_getLast` (for `mem_dropLast_support_of_mem_of_ne`),
    `SimpleGraph.Walk.getLast_support`, `end_mem_tail_support`, `tail_support_append`,
    `penultimate_cons_of_not_nil`, `getVert_map`, `List.tail_dropLast`, `Set.image_add_const_Icc`;
  * checked: `Walk.takeUntil` and `Walk.dropUntil` split at a vertex, not at the first vertex
    outside a set, so they do not give the cuts. `Walk.dropLast` is walk-valued; the existential
    doubling lemma keeps the style of A1.
* **PercLib**:
  * reused from A1: `exists_walk_double`, `exists_walk_double_dropLast`, `IsArm.exists_double`,
    `IsArm.double_disjoint`, `sbtw_innerPos_iff_sbtw_landingPos`, `snd_append_of_not_nil`,
    `penultimate_append_of_not_nil`, `IsCrossing.exists_append_eq_isCrossing(_of_subset)`,
    `add_one_le_of_Icc_subset`;
  * reused from PT2b: `cyclicallyOrdered_end_iff_of_pairwise_disjoint`;
  * reused from I2b: `dualConfig_dualConfig`, `isCrossing_map_iff`, `perimeterPos_add`,
    `perimeterPos_two_smul`, `landingPos_true`, `landingPos_false`,
    `mem_Icc_of_adj_of_mem_Icc_sub_one`, `boxBoundary_eq_Icc_diff_Icc`,
    `mem_multiArmEventTo_iff_of_agree`, `measurableSet_multiArmEvent`;
  * reused from the self-duality file: `law_preimage_dualConfig_eq`;
  * no colour inversion of arm events existed. `isDualArm_dualConfig_iff` (I2b) is the
    characterisation for the translated walk; the new
    `isDualArm_dualConfig_map_of_isCrossing` states its converse in the form the cuts give.
    `mem_Icc_of_isCrossing` generalises the proof of `IsOpenArm.mem_Icc` to any inner set.

## Sources

* P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
  no. 55: §4.1, arm events, p. 1572; Remark 26, p. 1592, on colour exchange. Colour exchange is
  not available on `ℤ²` in general. At `1/2`, the open/dual inversion comes from self-duality
  of bond percolation.
* H. Kesten, *Percolation theory for mathematicians*, Birkhäuser, 1982: the self-duality of bond
  percolation on `ℤ²` at `1/2`.
