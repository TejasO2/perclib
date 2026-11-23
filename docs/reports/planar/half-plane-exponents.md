# Arms in the half-plane: package U1 (two arms done, three arms not)

Advice note for package U1 of the arms plan (`docs/reports/planar/arms-plan.md` on branch
`claude/planar-arms-plan-0a97fc`, §3 and §9 row U1). Sources: W. Werner, *Lectures on
two-dimensional critical percolation*, arXiv:0710.0856v3, first exercise sheet (arXiv pp. 13–15:
"Two-arm exponent in the half-plane", "Three-arm exponent in the half-plane"); P. Nolin,
*Near-critical percolation in two dimensions*, EJP 13 (2008), journal Theorem 24 = arXiv v1
Theorem 23 (arXiv pp. 35–36; the half-plane items are only sketched there, "using the separation
lemmas"). Both texts are on the triangular lattice (site percolation).

**Status.** The two-arm statement is proved as written in the plan. The three-arm statement is not
proved: the plan's route for its upper bound does not work for the colours `![true, false, true]`
on `ℤ²` bond percolation (§4). This needs a decision by the user (pending, §4.3). Nothing in
`Arms/Defs.lean` or `Planar/Defs.lean` was changed; no A3 result beyond A3a was used (in fact no A3a
result was needed). Local commits only, nothing pushed.

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

## 4. Three arms: a gap in the route (not proved; pending the user's decision)

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

### 4.3 Options for the user (decision pending)

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

## 7. What remains (U1b)

`exists_halfArmEvent_three_bounds`, after the user's decision in §4.3. Inputs ready in this file:
the closing lemma, the BK count, translation, the interlacing tools at a bottom point, the quad
duality trick of `exists_dualWalk_of_forall_notMem_localConn`, and the landing-order lemma.

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
