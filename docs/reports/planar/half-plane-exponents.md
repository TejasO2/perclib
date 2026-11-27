# Arms in the half-plane: packages U1 and U1b (two arms; three arms dual–open–dual; open–dual–open lower bound)

Advice note for package U1 of the arms plan (`docs/reports/planar/arms-plan.md` on branch
`claude/planar-arms-plan-0a97fc`, §3 and §9 row U1). Sources: W. Werner, *Lectures on
two-dimensional critical percolation*, arXiv:0710.0856v3, first exercise sheet (arXiv pp. 13–15:
"Two-arm exponent in the half-plane", "Three-arm exponent in the half-plane"); P. Nolin,
*Near-critical percolation in two dimensions*, EJP 13 (2008), journal Theorem 24 = arXiv v1
Theorem 23 (arXiv pp. 35–36; the half-plane items are only sketched there, "using the separation
lemmas"). Both texts are on the triangular lattice (site percolation).

**Status.** The two-arm statement is proved as written in the plan (U1, §1–§3). U1b (§9, after the
user's decision of 2026-11-27): the three-arm statement is proved with both bounds for Werner's
colours on `ℤ²` bond, dual–open–dual (`![false, true, false]`); for the plan's colours
open–dual–open (`![true, false, true]`) only the lower bound is proved, and the upper bound stays
open (§9.4: the reason and the route, through half-plane arm separation, packages A3b-4c…f, parked).
Nothing in `Arms/Defs.lean`, `Planar/Defs.lean` or `Arms/Separation/Defs.lean` was changed. Local
commits only, nothing pushed.

## 1. What is proved

New file `PercLib/Models/Planar/Arms/HalfPlaneExponents.lean` (proof-only, about 1750 lines; builds
with `--wfail` in 14 s once its imports are built; axioms `propext`, `Classical.choice`,
`Quot.sound`). Main theorem, exactly the plan's statement:

```lean
theorem exists_halfArmEvent_two_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c / R ≤ (law q).real (halfArmEvent ![true, false] 0 0 R) ∧
          (law q).real (halfArmEvent ![true, false] 0 0 R) ≤ C / R
```

(`NN q` of the plan is spelled out: `q = 1/2` on the edges of `ℤ²`, anything elsewhere.)

Constants. Let `c` be the crossing bounds at `1/2` of `exists_crossingBounds_half` and
`β = c 7 ^ 4` (the dual-circuit bound of `pow_le_law_compl_crossing_inter`). Then

* upper bound (`exists_mul_law_halfArmEvent_two_le`): `R · P(A₂⁺(R)) ≤ 96 β⁻¹ + 4`, so
  `C = (96 β⁻¹ + 4).toReal + 1`;
* lower bound (`exists_pos_le_mul_law_halfArmEvent_two`): `min (c 4 · c 5) 1 ≤ 4R · P(A₂⁺(R))`,
  so `c = (min (c 4 · c 5) 1).toReal / 4`.

Supporting results (all in the same file):

| Declaration | Content |
|---|---|
| `PercLib.Probability.prodBernoulli_setOf_diff_singleton_mem_le` | `P(i closed) · P(ω \ {i} ∈ F) ≤ P(F)`, any profile, any `F` (no measurability) |
| `law_setOf_diff_singleton_mem_le` | closing an edge of probability `1/2` at most doubles a probability |
| `sum_law_le_sum_pow_of_forall_mem_foldl` | counting with BK: if any `k` of the events `F i` give `k` disjoint occurrences of an increasing `C`, then `∑ P(F i) ≤ ∑_{k ≤ |S|} P(C)^k` |
| `mem_foldl_of_pairwise_notMem_localConn` | points of `B_s(0)` in distinct clusters of a set `H`, each joined to sup-norm `3s`, give disjoint occurrences |
| `law_halfArmEventTo_add`, `law_halfArmEvent_eq_law_halfArmEvent_zero` | translation invariance of half-plane arm events (profile constant on edges) |
| `dualConfig_inter_image_mem_localConn_of_walk` | a dual walk, each step with a face inside the box, in quad-duality form |
| `notMem_localConn_of_dualConfig_left/right`, `le_perimeterPos_of_dualConfig_left` | mixed interlacing at a bottom point of a box |
| `mem_or_mem_of_mem_halfArmEvent_two` | upper bound, deterministic part (§2) |
| `exists_dualWalk_of_forall_notMem_localConn` | quad duality with the other bottom edges opened gives a dual path from the edge on the left of `x` |
| `exists_perimeterPos_two_nsmul_eq`, `landingPos_lt_of_dualWalk` | the landing position of a dual step; the landing order, by interlacing in the upper half-box |
| `exists_mem_halfArmEvent_two_of_mem_crossing` | lower bound, deterministic part (§3) |
| `SimpleGraph.Walk.exists_isCrossing_of_start_mem` | a walk from `S` to outside `T` contains a crossing from `S` out of `T` |

## 2. Small scales and conventions

* Both plan statements are fine at small scales: at `R = 1` both events are nonempty with positive
  probability (the I2b examples in `Arms/Defs.lean`: one open edge from `0`; two open edges and a
  closed boundary edge between them), and the constants are existential, so no `R₀` is needed.
* Conventions (I2b): `halfArmEvent σ 0 0 R` has open arms starting at the vertex `0` and dual arms
  starting at one of the four faces at `0`; the half-plane condition puts open vertices and the
  lower-left corners of dual faces at height `≥ 0`, so a dual arm starts at the upper-left or the
  upper-right face and never touches the line. Landing positions increase counterclockwise from
  the right end of the line, so `![true, false]` is "open arm on the right, dual arm on its left".
  This is Werner's two-arm event mirrored (his closed arm starts at `x + 1`, on the right); the
  reflection `x ↦ -x` exchanges the two, but it was not needed.

## 3. The two-arm route, and one correction to the plan

**The plan's claim fails on `ℤ²` bond as stated.** The plan (and Werner's 2(b)) says that a
two-arm point of `[-n/2, n/2] × {0}` is the extreme point of its cluster on the line. On the
triangular lattice the closed arm starts at the site `x + 1` on the line, so it separates `x` from
the rest of the line. On `ℤ²` bond the dual arm starts at a face above the line and the open arm may
run along the line. Counterexample: open the edges of the line `y = 0` from `-n` to `n`, close every
other edge. Then every `x` on the line has the event (open arm along the line to the right, dual
arm straight up from the face on its upper left), all in one cluster: the count of extreme points
is `1` while the count of two-arm points is `~n`. So no injection into clusters exists for the
event as defined.

**Fix used (a local modification, no statement change).** For a two-arm point `x`, close the edge on
the left of `x`, and also the edge above `x` when the dual arm starts at the upper-right face (or
the mirror edges on the right, depending on the first step of the open arm; four cases, at most two
edges, never an edge of the open arm). In the new configuration the dual arm, prolonged through the
closed edges to the face below the line, separates `x` from the bottom points two or more steps to
one side (mixed interlacing in the half-box), so `x` is, up to its neighbour, an extreme point of
its cluster on that side. Closing an edge of probability `1/2` at most doubles a probability, so
`P(A₂⁺) ≤ 6 P(F^L_x) + 6 P(F^R_x)`. Points of one parity with property `F^L` lie in distinct
clusters of the half-box `[-3s, 3s] × [0, 3s]`, each joining `B_s(0)` to sup-norm `3s`; BK with the
dual circuit around the annulus (`notMem_localConn_of_notMem_crossing`) bounds the expected number
by `β⁻¹`. With `s = (R - 1)/4` and translation invariance this gives `R P(A₂⁺(R)) ≤ 96 β⁻¹`.

**Lower bound.** With probability `≥ c 4 · c 5` (independent events on disjoint edge sets) the strip
`[R, 2R] × [0, 4R]` has an open bottom-top crossing and the strip of faces `[-2R, -R] × [-1, 4R]` a
dual one. In the half-box `[-4R, 4R] × [0, 4R]` let `x` be the leftmost bottom point joined to the
open crossing. The dual crossing keeps `x` in `(-2R, 2R]` (mixed interlacing). The edge on the left
of `x` is closed (minimality); no open path in the half-box joins the bottom part left of `x` to the
bottom part at or right of `x` (minimality and primal interlacing). Quad duality, applied to the
configuration in which every other bottom edge is opened, then gives a dual path from the face below
the edge on the left of `x`; its last step up from the row below the box crosses that edge, so the
rest is a dual path from the upper-left face of `x` to the boundary, above the line. Cutting the
open path and the dual path at `∂B_R(x)` gives the two arms; their landing order follows from
interlacing in the upper half of `B_R(x)` (`landingPos_lt_of_dualWalk`), and `x = (k, 0)` with
`k ∈ (-2R, 2R]`. Summing over these `4R` points with translation invariance gives the bound.
Monotonicity in `R` was not needed: the box sizes are chosen as functions of `R`.

## 4. Three arms: a gap in the route (analysis before U1b; outcome in §9)

### 4.1 Werner's "Good" points give dual–open–dual, not open–dual–open

Werner's three-arm count uses points `x` that are the unique lowest point of an open cluster that
leaves `x + H_n`. Such a point has **one** open arm (in the cluster) and **two** closed arms (the
boundary of the cluster on each side): colours closed–open–closed. The plan says "each lowest point
has two open arms and a dual arm between them" (§3, "Routes"); that is an erratum in the plan. On the
triangular lattice the colour sequence does not matter in the half-plane (colour switching), but on
`ℤ²` bond there is no exact colour switching (Nolin Remark 26), and A1c's colour inversion is for
the full plane only.

### 4.2 For `![true, false, true]` the lowest-point injection fails

For open–dual–open at a vertex `x` the open arms may run along the line `y = x₁` (vertices on the
line are allowed for open arms, not for dual faces). Example: an open "U": a horizontal open segment
`[a, b] × {h}` with open paths going up from both ends, and the faces above the segment in one dual
cluster reaching far. Every vertex of the segment has the three arms (right along the segment and
up, left along the segment and up, dual arm straight up), all with the same open cluster and the
same dual cluster. So the number of three-arm points is not bounded by any count of clusters, and,
unlike the two-arm case, no local modification at `x` helps (the arms touch the line far from `x`).
Nolin's sketch (arXiv p. 36) first makes the arms "stay strictly positive", i.e. leave the line,
and then counts; that step is arm separation (Theorem 11 type, package A3), which is paused.

For **dual–open–dual** (`![false, true, false]`) Werner's count does work: the dual arms never touch
the line, so closing the edges on the left, on the right and below `x` (at most three edges, none on
the open arm, after excluding the wrong landing orders by interlacing as in §3) makes `x` the unique
lowest point of its cluster in a half-box, and the clusters are counted by BK as in §3 (upper
bound); the lower bound needs a cluster with a unique lowest point built by RSW (Werner's 3)). This
has not been written in Lean; it is an estimate of the route, not a check.

For open–dual–open the **lower bound** is reachable now, by the dual of the same construction (a
dual cluster with a unique lowest face has an open arm on each side of it, both starting at the
bottom corners of that face, joined by the open bottom edge). Only the upper bound is blocked.

### 4.3 Options for the user (decided 2026-11-27: option 3, without the separation packages; §9)

1. **Change the three-arm statement to `![false, true, false]`** (Werner's colours on `ℤ²` bond).
   This is a statement change, so it is the user's call. Route: §4.2 above, both bounds without
   separation; size similar to the two-arm file.
2. **Keep `![true, false, true]`.** Prove the lower bound now; the upper bound waits for the
   separation step (making the arms leave the line), i.e. for A3, which is paused.
3. Prove both colour sequences (option 1 now, the open–dual–open upper bound after A3).

U2 (five arms) is unaffected by this choice; it is blocked on the pack gap of A3.

## 5. Errata and remarks on the sources

* Plan §3 "Routes", two arms: "a point `x ∈ S` with an open arm and a dual arm … is the rightmost
  point of `S` in one of these clusters" is false for the bond event as defined (§3 above); a local
  modification fixes it. The plan also has the orientation mirrored relative to Werner (his closed
  arm is on the right of the open arm; here the open arm lands first).
* Plan §3 "Routes", three arms: "Each lowest point has two open arms and a dual arm between them" is
  wrong; a unique lowest point of an open cluster has one open arm between two closed arms (§4.1).
* Werner's exercise 2(b) (two arms) relies on the closed arm starting on the line at `x + 1`; this is
  where the triangular site model and `ℤ²` bond differ.
* Nolin's Theorem 24 (journal) is Theorem 23 in arXiv v1; its half-plane items are a sketch based on
  separation, with no details.

## 6. Search (what was looked for before writing general lemmas)

* PercLib: `Probability/Coordinate.lean` (`prodBernoulli_map_diff_singleton`,
  `prodBernoulli_eq_smul_add_smul`: used for the closing lemma; no inequality of that form exists),
  `Probability/FiniteEnergy/Insertion.lean` (deletion and insertion maps, images of overwrites; no
  preimage inequality), `Probability/LocallyMonotone.lean` (`prodBernoulli_foldl_replicate_le_pow`:
  used), `Percolation/Bond/Tightness/BKStep.lean` (`mem_foldl_replicate_disjointOccurrence`: used),
  `Models/Planar/Arms/TwoPoint.lean` (`law_armEvent_add`: the pattern for translation; no half-plane
  version existed), `Gluing.lean` (`dualConfig_inter_mem_localConn_of_walk` is the ring lemma, a
  different statement, hence the name `dualConfig_inter_image_mem_localConn_of_walk`), `QuadDuality`
  (`exists_dualConfig_inter_mem_localConn_of_not_exists`, `Int.exists_add_mul_mem_Ico_iff`: used),
  `Interlacing` (`dualConfig_inter_notMem_localConn_of_interlaced`,
  `exists_mem_support_of_interlaced`: used), `MultiArmBasics` (`exists_append_eq_of_notMem`,
  `exists_append_eq_of_exists_mem`, `IsCrossing.exists_append_eq_isCrossing_of_subset`,
  `penultimate_append_of_not_nil`: used), `RSWKeyStep` (`exists_walk_first_mem`,
  `exists_walk_of_mem_localConn`, `mem_localConn_of_walk`: used), `CriticalProbability`
  (`notMem_localConn_of_notMem_crossing`, `mem_crossing_iff_of_inter_eq`: used), `MultiArmBounds`
  (`pow_le_law_compl_crossing_inter`, crossing bounds in sub-boxes: used), A3a
  (`dualConfig_inter_eq_of_inter_eq`: used).
* mathlib: `SimpleGraph.Walk.dropLast`, `support_dropLast`, `adj_penultimate`,
  `mk_penultimate_end_mem_edges`, `bypass`, `takeUntil`, `support_tail_of_not_nil`, `copy`
  (all used); `Finset.sum_boole`, `Finset.exists_subset_card_eq`, `lintegral_finsetSum`,
  `ENNReal.tsum_geometric`, `measure_biUnion_finset_le`, `toMeasurable` (used). Nothing like
  "a walk from `S` to outside `T` contains a crossing" was found in mathlib or PercLib in this
  general form (A3a's `exists_isCrossing_of_mem_crossing_one` is the box case), hence
  `SimpleGraph.Walk.exists_isCrossing_of_start_mem`.

## 7. What remains

U1b is done (§9) except the open–dual–open upper bound (§9.4). The decision of §4.3 was option 3,
trimmed: dual–open–dual with both bounds, open–dual–open lower bound only.

## 8. Lessons

* `rw` of a vertex variable fails when a walk's type depends on it (`a 0 = x` with `γ 0 : Walk (a 0) _`);
  use `congrArg (fun p => …) h` or `subst` on a local from `obtain`.
* `set x := ![k, 0]` keeps `x 0` and `x 1` reducible by `rfl`; after `subst` on a walk endpoint the
  remaining variable name changes, so later references must follow.
* In `exists_append_eq_of_*` and `exists_walk_first_mem` the results are prefix/suffix walks with
  membership facts only; for an arm's last step use `IsCrossing.exists_append_eq_isCrossing_of_subset`
  on a path (`bypass`), so that the suffix keeps the penultimate vertex.
* A whole new file of about 1750 lines was developed in scratch files of growing size
  (`lake env lean`, about one minute per run); every batch compiled within one to three runs.

## 9. U1b: three arms (2026-11-27)

**User decision (2026-11-27, "Yes, trim").** The three-arm statement is proved for Werner's colours
on `ℤ²` bond, **dual–open–dual** (`![false, true, false]`), with both bounds; for the plan's
colours **open–dual–open** (`![true, false, true]`) only the **lower** bound is proved. This is
option 3 of §4.3, with the open–dual–open upper bound left open (§9.4). After U1b the chain goes on
to U2a and stops; the half-plane inner half A3b-4c…f is parked.

### 9.1 What is proved

New file `PercLib/Models/Planar/Arms/HalfPlaneThreeArms.lean` (proof-only, imported from
`PercLib.lean`; imports `HalfPlaneExponents` and `HalfOuterSeparation`). No `@[tag]`, no new
definition, no change to `Planar/Defs.lean`, `Arms/Defs.lean` or `Arms/Separation/Defs.lean`.

```lean
theorem exists_halfArmEvent_three_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c / R ^ 2 ≤ (law q).real (halfArmEvent ![false, true, false] 0 0 R) ∧
          (law q).real (halfArmEvent ![false, true, false] 0 0 R) ≤ C / R ^ 2

theorem exists_halfArmEvent_open_dual_open_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c / R ^ 2 ≤ (law q).real (halfArmEvent ![true, false, true] 0 0 R)
```

`q` is spelled out as in U1a. Constants (with `c` the crossing bounds at `1/2` of
`exists_crossingBounds_half`, `β = c 7 ^ 4`):

* upper bound (`exists_mul_sq_law_halfArmEvent_three_le`): `R² P ≤ 1024 β⁻¹ + 16`;
* lower bounds (`exists_pos_le_mul_sq_law_halfArmEvent_three`, `…_three_open`):
  `c₀ ≤ 336 R² P` for `R ≥ 2`, `c₀ = c 3 · (c 9 · c 6 · c 6)`
  (`exists_pos_le_law_crossing_inter_compl`); the final constant is `c₀ / 1344`, which also covers
  `R = 1` by monotonicity in `R` (`halfArmEventIn_subset_halfArmEventIn_of_le`, A3b-4).

Supporting results (same file):

| Declaration | Content |
|---|---|
| `landingPos_lt_of_dualWalk_left`, `lt_landingPos_of_dualWalk_right` | landing order of an open walk from a point `s` of the line and a dual walk from the face above the edge on the left (right) of `s`, that edge closed; `s` need not be the centre |
| `exists_perimeterPos_two_nsmul_add_one_eq`, `two_mul_le_perimeterPos_of_notMem_Icc`, `le_perimeterPos_of_dualConfig_right` | the second end of the boundary edge crossed by a dual step; mirror interlacing at a bottom point |
| `exists_arms_of_mem_halfArmEvent_three` | at a dual–open–dual point the open arm steps up and the dual arms start at the two faces above `x` |
| `mem_of_mem_halfArmEvent_three` | with the edges left and right of `x` closed, `x` is joined to the far sides of a half-box and to no bottom point two or more steps away |
| `mem_localConn_of_forall_notMem` | a cluster whose bottom-row points have closed down edges does not leave the half-box |
| `law_setOf_sdiff_five_mem_le`, `law_setOf_insert_sdiff_three_mem_le`, `law_setOf_insert_insert_insert_sdiff_mem_le`, `law_setOf_insert_mem_le`, `PercLib.Probability.prodBernoulli_setOf_insert_mem_le` | closing and opening coordinates |
| `mem_crossing_of_walk_of_le` | a walk from `{v i ≤ lo i}` to `{hi i ≤ v i}` inside a box crosses `Icc lo hi` in direction `i` (any dimension) |
| `SimpleGraph.Walk.mem_of_mem_support_of_forall_darts` | a set closed under the steps of a walk contains its support |
| `exists_lowest_of_mem_crossing` | the lowest row of the cluster of the top of a crossing, under the four crossing events |
| `exists_walk_of_notMem_Icc`, `exists_isDualArm_of_walk` | a walk of faces up to its first exit; a dual arm inside a dual walk with the same last step |
| `exists_dualWalks_of_forall_lt`, `exists_dualWalks_of_mem_crossing` | the walks at the extended lowest point, for any configuration `η` and any `η'` agreeing with it away from `x'` |
| `mem_halfArmEvent_three_of_dualWalks`, `mem_halfArmEvent_three_open_of_dualWalks` | assembly of the three arms (dual–open–dual; open–dual–open from the walks of the dual configuration) |
| `exists_pos_le_law_crossing_inter_compl` | the four crossing events have probability `≥ c₀` (crossing bounds, Harris for decreasing events, independence) |

### 9.2 Routes as proved

**Dual–open–dual, the arms at `x`.** The open arm steps up from `x`: if it stepped right, both
faces above `x` would be on its left and the dual arm landing first could not land on its right.
In Lean: in the configuration with the edge left of `x` closed (and the edge above `x`, if that dual
arm starts at the upper-right face, prepending the upper-left face), U1a's landing lemma in the
upper half-box (now `landingPos_lt_of_dualWalk_left`) puts the open arm before the dual arm,
contradicting the order. The left step is the mirror (`lt_landingPos_of_dualWalk_right`). The
landing order is a property of the walks only, so closing edges for the proof is free.

**Upper bound.** For `x ∈ B_s(0)`, `4s + 1 ≤ R`, the half-box `U_x = [-3s, 3s] × [x₁, 3s]`
stands on the line through `x`. Close the edges left and right of `x` (not on the open arm, which
steps up) and the three edges downwards from `xl`, `x`, `xr`. Then (`mem_of_mem_halfArmEvent_three`)
`x` is joined inside `U_x` to its left, right or top side and to no bottom point two or more steps
away; and the cluster of `x` in the square `[-3s, 3s]²` stays in `U_x`
(`mem_localConn_of_forall_notMem`: it could leave only by a down edge of a bottom point within one
step of `x`, all closed). Two such points of the same column parity are therefore not joined in the
square (each would lie above the other's row, so they share a row, and then they are two or more
steps apart). BK with the dual circuit around `[s, 3s]` (as in U1a) bounds the expected number of
such points of one parity by `β⁻¹`. Five closed edges cost `2⁵`; `(2s + 1)² P ≤ 64 β⁻¹`.

**Lower bound, dual–open–dual.** Events: an open bottom-top crossing of `[-R, R] × [R + 2, 4R]`; no
open bottom-top crossing of `[-4R, 4R] × [0, R + 1]`; no open left-right crossing of
`[-3R - 1, -2R] × [0, 4R]` nor of `[2R, 3R + 1] × [0, 4R]` (each the complement of a dual crossing
of a box of faces at least `R` wide or tall). In the box `[-4R, 4R] × [0, 4R]`, the cluster `K` of
the top end `w` of the crossing has its lowest row `m ∈ [1, R + 2]` at a point `x₁ ∈ [-3R, 3R]`
(walks out of `K` would cross one of the three forbidden boxes, `mem_crossing_of_walk_of_le`).
**Local modification:** let `x'` be the point below `x₁`; open the edge `x' x₁` and close the
other three edges at `x'`. Then the cluster of `x'` above row `m - 1` is `K ∪ {x'}`, so `x'` is the
only point of that row in it and it reaches `w`; quad duality with the other bottom edges opened
(U1a's `exists_dualWalk_of_forall_notMem_localConn`, applied at `x'` and at `x' + e₁`) gives dual
walks from the faces above `x'`; they share no face (else the closed edges at `x'` and the shared
face give a dual path from below the edge left of `x'` to below the edge right of `x'`, which the
open path from `x'` to `w` interlaces). Cut at `∂B_R(x')` these are three arms, ordered by the two
landing lemmas. One opened and three closed edges cost `2⁴`; the points `x'` range over
`[-3R, 3R] × [0, R + 1]`, at most `21 R²` points, so `c₀ ≤ 16 · 21 R² P`.

**Lower bound, open–dual–open.** The same construction for the dual configuration `η = dualConfig ω`
(whose law at `1/2` is that of `ω`, `law_preimage_dualConfig_eq`): `exists_dualWalks_of_mem_crossing`
is stated for any configuration `η` and any `η'` agreeing with it away from `x'`. For `η' =
dualConfig ω'` the local modification is: close the top edge of the face `x'` and open its left,
bottom and right edges. The `η'`-open walk from `x'` is a dual walk of `ω'` from the face `x'` (the
dual arm); the `η'`-dual walks are walks of the dual of the dual configuration, i.e. open walks of
`ω'` translated by `(-1, -1)` (`dualConfig_dualConfig`): from the upper corners of the face `x'`.
With the left edge, and the bottom and right edges, they give two open arms from the lower-left
corner `x` of the face, disjoint except at `x` (the two walks share no face of the dual lattice).
Order: closing the bottom edge in an auxiliary configuration, `lt_landingPos_of_dualWalk_right` at
`x` and `landingPos_lt_of_dualWalk_left` at `x + e₁` (a start point off the centre: the reason the
landing lemmas take a general start `s`) give right arm < dual arm < left arm.

### 9.3 Decisions

* **Colours and names.** `exists_halfArmEvent_three_bounds` keeps the plan's name for the proved
  two-sided statement, with Werner's colours `![false, true, false]`; the open–dual–open lower
  bound is `exists_halfArmEvent_open_dual_open_lower_bound` (descriptive suffix; the colour
  sequence is the event's argument). Intermediate open–dual–open lemmas carry `_open`.
* **New module** `Arms/HalfPlaneThreeArms.lean` rather than growing `HalfPlaneExponents.lean`
  (1760 lines) to about 4000; U1a's file is unchanged.
* **2D count with a parity class and closed down edges** (upper bound) instead of Werner's "unique
  lowest point in `x + H_n`": the interlacing lemma at a bottom point (U1a) separates only points
  two or more steps away, so neighbours on the line are handled by closing their down edges and by
  counting one column parity at a time. Equivalent for the estimate (constant `64 β⁻¹`).
* **Lower bound by local modification** at the lowest point of a cluster (open one edge down, close
  three), instead of proving that a lowest point is unique with positive probability. New general
  lemma: opening a coordinate (`prodBernoulli_setOf_insert_mem_le`, in `PercLib.Probability`, in
  this file next to U1a's closing lemma).
* **Box sizes.** Strips of width `R + 1` (`[-3R - 1, -2R]`, `[2R, 3R + 1]`) and the bottom box of
  height `R + 1` so that the dual crossings have boxes at least `R` wide (crossing bounds need
  `n ≥ 1`); the open crossing starts at row `R + 2` so that its edges are disjoint from the bottom
  box. `R ≥ 2` in the deterministic lemmas (`x' + e₁` strictly inside); `R = 1` by monotonicity.
* **Constants:** `C = 1024 β⁻¹ + 16`, `c = c₀ / 1344` (both colourings), `c₀ = c 3 · c 9 · c 6²`.
* **Self-duality** for the open–dual–open lower bound instead of a separate dual development: the
  core lemma is generic in the configuration.

### 9.4 Target 3: the open–dual–open upper bound is not proved

`(law q).real (halfArmEvent ![true, false, true] 0 0 R) ≤ C / R²` remains open. Reason (§4.2): open
arms may run along the line (vertices on the line are allowed for open arms, not for the faces of
dual arms), so an open–dual–open point need not be a lowest point of anything: in the open "U"
example of §4.2 every vertex of the bottom segment has the three arms, all with one open and one
dual cluster, and no local modification at `x` helps because the arms touch the line far from `x`.
The lowest-point injection used for dual–open–dual therefore fails, and no count of clusters bounds
the number of three-arm points.

**Route that would prove it** (`quasi-multiplicativity.md` §24.7): make the arms leave the line
first, by half-plane arm separation at a fixed inner radius, then count. Concretely: the half-plane
inner half of Theorem 11 (strictness of the arms off the line via inner windows at a fixed radius,
`π⁺(r, R) ≤ C P(A⁺_J(r, R))`), which is packages **A3b-4c…f** (half-plane Theorem 11 outer half,
QM upper half, extendability outwards, a priori lower bound; then the inner step on the upper half of
`∂B_ρ`, two-sided gluing, QM lower half, extendability inwards). These packages are **parked by the
user** (decision of 2026-11-27, "Yes, trim").

### 9.5 Errata and remarks

* §4.2 above said the dual–open–dual route closes "at most three edges, none on the open arm" for
  the upper bound. As proved it closes five (left and right of `x`, and the down edges of `xl`,
  `x`, `xr`); the down edges are needed because U1a's interlacing at a bottom point does not
  separate the two neighbours of `x` on the line.
* The plan's lower-bound sketch ("a cluster with a unique lowest point built by RSW") is replaced by
  a local modification at the lowest row of a cluster; uniqueness is created, not found.
* Werner's lowest points on `ℤ²` bond: the open arm of a dual–open–dual point always leaves `x`
  upwards (§9.2), so the point is the lowest point of its cluster above its row up to its two
  neighbours on the line.

### 9.6 Search

* PercLib: `Probability/Coordinate.lean` (`prodBernoulli_map_insert`, used for the opening lemma; no
  opening inequality existed); `Probability/HarrisDecreasing.lean`
  (`prodBernoulli_harris_of_isLowerSet`, used); `DeterminedIndependence`
  (`prodBernoulli_inter_of_determined`, used); `CrossingSymmetry`/`Duality`
  (`compl_crossing_one_eq_preimage_dualConfig`, `crossing_zero_eq_compl_preimage_dualConfig`,
  used); `MultiArmBounds.mem_crossing_of_walk` (a walk inside the box from side to side; different
  hypotheses, hence `mem_crossing_of_walk_of_le`); `SelfDuality.law_preimage_dualConfig_eq` and
  `Arms/Defs.dualConfig_dualConfig`, `isDualArm_dualConfig_iff` (used, the last as the pattern);
  `HalfOuterSeparation.halfArmEventIn_subset_halfArmEventIn_of_le` (monotonicity, used); U1a's file
  (every tool in §1, used); `Interlacing` (`dualConfig_inter_notMem_localConn_of_interlaced`,
  `exists_mem_support_of_interlaced`, used); `RSWKeyStep.exists_walk_first_mem`,
  `MultiArmBasics.exists_append_eq_of_notMem`/`_of_exists_mem`, A1 `apply_le_apply_add_one_of_adj`
  (used).
* mathlib: `SimpleGraph.Walk.penultimate_cons_of_not_nil`, `support_map`, `edges_map`,
  `takeUntil`, `bypass`, `Sym2.mem_and_mem_iff`, `Int.card_Icc`, `Finset.card_product`,
  `measure_biUnion_finset_le` (used). No lemma "a set closed under the steps of a walk contains its
  support" was found (`SimpleGraph.Walk` has `induction` only), hence
  `SimpleGraph.Walk.mem_of_mem_support_of_forall_darts`.

### 9.7 Lessons

* State the landing-order lemmas for a start point off the centre: the open–dual–open assembly
  needed the left lemma at `x + e₁`.
* State a construction for an arbitrary configuration `η` and every `η'` agreeing with it away from
  one point (with the four edge conditions as hypotheses): the same proof then serves the dual
  configuration, and the probability cost is a separate lemma.
* `simp only [Matrix.cons_val_one]` leaves `![a] 0`; add `Matrix.cons_val_zero`.
* `(by simp <;> omega)` triggers linter warnings both when simp closes the goal and when it does
  not; check each and write `(by simp)` or `(by simp; omega)`.
* `fin_cases i <;> fin_cases k <;> simp` followed by bullets is a flexible-tactic warning under
  `--wfail`; use `all_goals first | exact absurd rfl hik | exact absurd hi (by decide) | …`.
* With `set e := … with he`, the instance of `Finset.filter` with a classical predicate and a later
  `rw [Finset.mem_filter]` disagree on decidability; obtain the finset with its membership `iff`
  instead (`⟨_, fun l => Finset.mem_filter⟩`).
