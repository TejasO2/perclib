/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: W. Werner, Lectures on two-dimensional critical percolation, IAS/Park City
Mathematics Series 16 (2009), arXiv:0710.0856, first exercise sheet (three-arm exponent in the
half-plane); P. Nolin, Near-critical percolation in two dimensions, Electron. J. Probab. 13 (2008),
paper no. 55, Theorem 24(2).
-/
module

public import PercLib.Models.Planar.Arms.HalfPlaneExponents
public import PercLib.Models.Planar.Arms.HalfOuterSeparation

/-!
# Three arms in the half-plane

At `1/2`, the probability that the boundary vertex `0` of the upper half-plane has three arms to
distance `R` inside the half-plane, a dual arm, then counterclockwise an open arm, then a dual arm
(`halfArmEvent ![false, true, false] 0 0 R`), is of order `1/R²`. The proof is Werner's elementary
count of lowest points of clusters; it uses no separation of arms.

* **The arms at a dual–open–dual point.** The open arm leaves `x` upwards: if it stepped to the
  right, both faces above `x` would lie on its left, and the dual arm landing before it would
  cross it (interlacing in the upper half-box, `landingPos_lt_of_dualWalk_left`, after closing the
  edges at `x` that the arms do not use); the left step is the mirror image
  (`lt_landingPos_of_dualWalk_right`). So the dual arms start at the two faces above `x`.
* **Upper bound.** In the square `B_s(0)`, `4s + 1 ≤ R`, let `x` have the three arms. Close the
  edges on the left and on the right of `x` and the three edges downwards from `x` and its two
  neighbours on the line. Then, in the half-box of `[-3s, 3s]²` above the line through `x`, `x` is
  joined to the left, right or top side and to no point of the bottom side two or more steps away
  (the dual arms, prolonged through the closed edges, separate them), and its cluster cannot leave
  the half-box through the bottom. Points of one parity with this property lie in distinct
  clusters of `[-3s, 3s]²`, so by BK and a dual circuit their expected number is bounded; closing
  five edges of probability `1/2` costs a factor `32`. With translation invariance,
  `(2s + 1)² P(A₃⁺(R)) ≤ C`.
* **Lower bound.** With probability bounded below (crossing bounds, Harris, independence), the
  strip `[-R, R] × [R + 2, 4R]` has an open bottom-top crossing, while `[-4R, 4R] × [0, R + 1]` has
  no open bottom-top crossing and `[-3R - 1, -2R] × [0, 4R]`, `[2R, 3R + 1] × [0, 4R]` no open
  left-right crossing. In the box `[-4R, 4R] × [0, 4R]` the cluster of the top of the crossing
  then has its lowest row in `[1, R + 2]`, at a point `x₁` of `[-3R, 3R]`. Open the edge from `x₁`
  down to `x'` and close the other three edges at `x'`: then `x'` is the only point of its row in
  its cluster above the row, which reaches the top; quad duality (with the other edges of the row
  opened) gives dual walks from the two faces above `x'`; they share no face (interlacing with the
  open path); cut at `∂B_R(x')`, these are three arms, in the right order by the landing lemmas.
  Opening one edge and closing three costs a factor `16`, so `c ≤ 336 R² P(A₃⁺(R))` for `R ≥ 2`;
  `R = 1` follows by monotonicity in `R`.

## Main results

* `exists_halfArmEvent_three_bounds`: `c / R² ≤ P(A₃⁺(R)) ≤ C / R²` for `R ≥ 1`, at `1/2`, for
  the colours dual, open, dual.
* `exists_mul_sq_law_halfArmEvent_three_le`, `exists_pos_le_mul_sq_law_halfArmEvent_three`: the
  two bounds, `R² P(A₃⁺(R)) ≤ C` and `c ≤ 336 R² P(A₃⁺(R))` for `R ≥ 2`.
* `exists_arms_of_mem_halfArmEvent_three`: the open arm of a dual–open–dual point leaves it
  upwards, and the dual arms start at the two faces above it.
* `mem_of_mem_halfArmEvent_three`: a dual–open–dual point is a separated point of its cluster in
  a half-box once the edges on its left and on its right are closed.
* `exists_dualWalks_of_mem_crossing`: the arms at the extended lowest point of a cluster, for any
  configuration (used for the dual configuration as well).
* `landingPos_lt_of_dualWalk_left`, `lt_landingPos_of_dualWalk_right`: landing orders of an open
  walk from a point of the line and a dual walk from a face above an edge at that point.
* `mem_crossing_of_walk_of_le`: a walk between two half-spaces crosses the box between them.
* `PercLib.Probability.prodBernoulli_setOf_insert_mem_le`, `law_setOf_insert_mem_le`: opening a
  coordinate.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

namespace PercLib.Probability

/-- **Opening one coordinate.** The configurations that land in `F` once the coordinate `i` is
opened have probability at most `P(F) / P(i open)`. -/
theorem prodBernoulli_setOf_insert_mem_le {ι : Type*} [Countable ι]
    (p : ι → unitInterval) (i : ι) (F : Set (Set ι)) :
    (unitInterval.toNNReal (p i) : ℝ≥0∞) * prodBernoulli p {ω | insert i ω ∈ F} ≤
      prodBernoulli p F := by
  classical
  set M := toMeasurable (prodBernoulli p) F
  have hFM : F ⊆ M := subset_toMeasurable _ _
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hsub : {ω : Set ι | insert i ω ∈ F} ⊆ (fun ω => insert i ω) ⁻¹' M := fun ω hω => hFM hω
  have hmap := prodBernoulli_map_insert p i
  have h1 : prodBernoulli p ((fun ω => insert i ω) ⁻¹' M) =
      PercLib.Probability.prodBernoulli (Function.update p i 1) M := by
    rw [← hmap, Measure.map_apply (measurable_insert i) hM]
  have h2 := prodBernoulli_eq_smul_add_smul p i
  calc (unitInterval.toNNReal (p i) : ℝ≥0∞) * prodBernoulli p {ω | insert i ω ∈ F}
      ≤ (unitInterval.toNNReal (p i) : ℝ≥0∞) *
          PercLib.Probability.prodBernoulli (Function.update p i 1) M := by
        rw [← h1]; gcongr
    _ ≤ prodBernoulli p M := by
        conv_rhs => rw [h2]
        simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ENNReal.smul_def]
        exact le_self_add
    _ = prodBernoulli p F := measure_toMeasurable F

end PercLib.Probability

namespace PercLib.Models.Planar

section HalfPlaneThreeArms

variable {lo hi : LatticeSite 2} {ω : Config (LatticeSite 2)}

/-! ### Landing orders at a point of the line -/

/-- A corner on the boundary of the upper half-box `[x₀ - R, x₀ + R] × [x₁, x₁ + R]` of a face
outside the faces of `B_R(x)`, at or above the line and after `x`, is not on the bottom side
before its right end. -/
theorem two_mul_le_perimeterPos_of_notMem_Icc {x u g qlo qhi : LatticeSite 2} {R : ℕ}
    (hR : 1 ≤ R) (hql : qlo 0 = x 0 - R ∧ qlo 1 = x 1) (hqh : qhi 0 = x 0 + R ∧ qhi 1 = x 1 + R)
    (hu : u ∈ boxBoundary qlo qhi) (hug : u ∈ Icc g (g + 1))
    (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1)) (hg1 : x 1 ≤ g 1)
    (hxu : x 0 - qlo 0 < perimeterPos qlo qhi u) :
    2 * (R : ℤ) ≤ perimeterPos qlo qhi u := by
  rw [mem_boxBoundary_two_iff] at hu
  rw [mem_Icc_two_iff] at hug hg
  simp only [Pi.add_apply, Pi.one_apply, Pi.sub_apply, Pi.natCast_apply] at hug hg
  unfold perimeterPos at hxu ⊢
  split_ifs at hxu ⊢ <;> omega

/-- **The landing position of a dual step out of `B_R(x)`, by its second end.** Above the line
through `x`, the step crosses a boundary edge of the upper half-box; its counterclockwise-second
end `u` has twice its position, plus `2R`, equal to the doubled position plus one, unless the
edge is the lowest edge of the left side, whose second end is the lower-left corner. -/
theorem exists_perimeterPos_two_nsmul_add_one_eq {x h g qlo qhi : LatticeSite 2} {R : ℕ}
    (hR : 1 ≤ R) (hql : qlo 0 = x 0 - R ∧ qlo 1 = x 1) (hqh : qhi 0 = x 0 + R ∧ qhi 1 = x 1 + R)
    (hh : h ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hadj : (zdGraph 2).Adj h g) (hh1 : x 1 ≤ h 1) (hg1 : x 1 ≤ g 1) :
    ∃ u ∈ boxBoundary qlo qhi, u ∈ Icc g (g + 1) ∧
      ((2 * (R : ℤ) < perimeterPos qlo qhi u ∧
        perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2)))
          (h + g + 1) + 1 = 2 * perimeterPos qlo qhi u + 2 * R) ∨
        perimeterPos qlo qhi u = 0) := by
  rw [mem_Icc_two_iff] at hh hg
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hh hg
  rw [zdGraph_two_adj_iff] at hadj
  rcases hadj with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
  · -- `g` above `h`: the top side
    obtain ⟨u, hu0, hu1⟩ : ∃ u : LatticeSite 2, u 0 = h 0 ∧ u 1 = g 1 := ⟨![_, _], rfl, rfl⟩
    refine ⟨u, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [mem_boxBoundary_two_iff]; omega
    · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    · unfold perimeterPos; split_ifs <;> omega
    · simp only [perimeterPos, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        Pi.one_apply, nsmul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega
  · omega
  · -- `g` right of `h`: the right side
    obtain ⟨u, hu0, hu1⟩ : ∃ u : LatticeSite 2, u 0 = g 0 ∧ u 1 = g 1 + 1 := ⟨![_, _], rfl, rfl⟩
    refine ⟨u, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [mem_boxBoundary_two_iff]; omega
    · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    · unfold perimeterPos; split_ifs <;> omega
    · simp only [perimeterPos, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        Pi.one_apply, nsmul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega
  · -- `g` left of `h`: the left side
    obtain ⟨u, hu0, hu1⟩ : ∃ u : LatticeSite 2, u 0 = h 0 ∧ u 1 = g 1 := ⟨![_, _], rfl, rfl⟩
    refine ⟨u, ?_, ?_, ?_⟩
    · rw [mem_boxBoundary_two_iff]; omega
    · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    · by_cases hgx : g 1 = x 1
      · right
        rw [perimeterPos_of_bottom (by omega)]; omega
      · left
        constructor
        · unfold perimeterPos; split_ifs <;> omega
        · simp only [perimeterPos, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
            Pi.one_apply, nsmul_eq_mul, Nat.cast_ofNat]
          split_ifs <;> omega

/-- **Interlacing at a bottom point, on the right.** In a box, let `x` be a point of the bottom
side joined inside the box to a boundary point `w` more than one step after it, and let a dual
path, crossing only edges of the box, join the face below the edge on the right of `x` to a face
outside the box with a boundary corner `y`. Then `y` does not come after `w`. -/
theorem le_perimeterPos_of_dualConfig_right (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {x w f g y : LatticeSite 2} (hx1 : x 1 = lo 1) (hx0 : lo 0 ≤ x 0) (hxh : x 0 < hi 0)
    (hw : w ∈ boxBoundary lo hi) (hf0 : f 0 = x 0) (hf1 : f 1 + 1 = x 1)
    (hg : g ∉ Icc lo (hi - 1)) (hy : y ∈ boxBoundary lo hi) (hyg : y ∈ Icc g (g + 1))
    (hxw' : perimeterPos lo hi x + 1 < perimeterPos lo hi w)
    (hxw : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x w)
    (hδ : dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g) :
    perimeterPos lo hi y ≤ perimeterPos lo hi w := by
  obtain ⟨x', hx'0, hx'1⟩ : ∃ p : LatticeSite 2, p 0 = x 0 + 1 ∧ p 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  have hxB : x ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hx'B : x' ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hfo : f ∉ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  have hx'f : x' ∈ Icc f (f + 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
  have hpx : perimeterPos lo hi x = x 0 - lo 0 := perimeterPos_of_bottom hx1
  have hpx' : perimeterPos lo hi x' = x 0 + 1 - lo 0 := by
    rw [perimeterPos_of_bottom (hx'1.trans hx1), hx'0]
  by_contra hc
  exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxw hxB hw hfo hx'B hx'f hg hy hyg
    (Or.inl ⟨by omega, by omega, Or.inr (by omega)⟩) hδ

/-- **The landing order on the left of a point of the line.** Let `s` be a point of the line
through `x`, the edge on its left closed, `α` an open walk from `s` inside `B_R(x)`, above the
line, to the boundary, and `δ` a dual walk from the face above that edge, above the line, leaving
the faces of `B_R(x)` at its last step only. Then `α` lands before the dual step,
counterclockwise from the right end of the line. -/
theorem landingPos_lt_of_dualWalk_left {x s sl fL p g : LatticeSite 2} {R : ℕ}
    (hs1 : s 1 = x 1) (hs0 : x 0 - R + 2 ≤ s 0) (hs0' : s 0 ≤ x 0 + R - 1)
    (hsl : sl 0 + 1 = s 0 ∧ sl 1 = s 1) (hfL : fL 0 + 1 = s 0 ∧ fL 1 = s 1)
    (α : (zdGraph 2).Walk s p) (hαe : ∀ e ∈ α.edges, e ∈ ω)
    (hαB : ∀ v ∈ α.support, v ∈ Icc (x - (R : LatticeSite 2)) (x + R))
    (hαH : ∀ v ∈ α.support, x 1 ≤ v 1)
    (hp : p ∈ boxBoundary (x - (R : LatticeSite 2)) (x + R)) (he₁ : s(sl, s) ∉ ω)
    (δ : (zdGraph 2).Walk fL g) (hδn : ¬δ.Nil)
    (hδ : ∀ f ∈ δ.support.dropLast, f ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδ1 : ∀ f ∈ δ.support, x 1 ≤ f 1) (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδE : ∀ E ∈ δ.edges, E ∈ dualConfig ω) :
    landingPos (x - R) (x + R) true α <
      perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2)))
        (δ.penultimate + g + 1) := by
  have hR : 1 ≤ R := by omega
  obtain ⟨qlo, hql0, hql1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 - R ∧ v 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  obtain ⟨qhi, hqh0, hqh1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 + R ∧ v 1 = x 1 + R :=
    ⟨![_, _], rfl, rfl⟩
  obtain ⟨f₀, hf₀0, hf₀1⟩ : ∃ v : LatticeSite 2, v 0 + 1 = s 0 ∧ v 1 + 1 = s 1 :=
    ⟨![s 0 - 1, s 1 - 1], by simp, by simp⟩
  -- the open walk in the upper half-box
  have hαQ : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc qlo qhi) s p :=
    mem_localConn_of_walk α (fun v hv => by
      have h₁ := hαB v hv
      have h₂ := hαH v hv
      rw [mem_Icc_two_iff] at h₁ ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at h₁
      omega) hαe
  have hp1 := hαH p α.end_mem_support
  have hpQ : p ∈ boxBoundary qlo qhi := by
    rw [mem_boxBoundary_two_iff] at hp ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hp
    omega
  -- the last dual step
  have hpen : δ.penultimate ∈ δ.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hδn]; exact SimpleGraph.Walk.end_mem_support _
  have hadj := δ.adj_penultimate hδn
  have hpenB := hδ _ hpen
  have hpen1 := hδ1 _ (List.mem_of_mem_dropLast hpen)
  have hg1 := hδ1 g δ.end_mem_support
  obtain ⟨u, huQ, hug, hxu, hland⟩ := exists_perimeterPos_two_nsmul_eq hR ⟨hql0, hql1⟩
    ⟨hqh0, hqh1⟩ hpenB hg hadj hpen1 hg1
  have hu2 := two_mul_le_perimeterPos_of_notMem_Icc hR ⟨hql0, hql1⟩ ⟨hqh0, hqh1⟩ huQ hug hg hg1
    hxu
  -- the dual path in the upper half-box, from the face below the closed edge
  have hsQ : s ∈ Icc qlo qhi := by rw [mem_Icc_two_iff]; omega
  have hslQ : sl ∈ Icc qlo qhi := by rw [mem_Icc_two_iff]; omega
  have hd₁ : f₀ ∈ dualEdge s(sl, s) ∧ fL ∈ dualEdge s(sl, s) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hgQ : g ∉ Icc qlo (qhi - 1) := fun h => hg (by
    rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega)
  have hδQ := dualConfig_inter_image_mem_localConn_of_walk (lo := qlo) (hi := qhi) δ
    (fun f hf => by
      rw [← SimpleGraph.Walk.dropLast_support_concat δ, List.mem_append,
        List.mem_singleton] at hf
      rcases hf with hf | rfl
      · have h₁ := hδ f hf
        have h₂ := hδ1 f (List.mem_of_mem_dropLast hf)
        rw [mem_Icc_two_iff] at h₁ ⊢
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ ⊢
        omega
      · rw [mem_Icc_two_iff] at hpenB ⊢
        rw [zdGraph_two_adj_iff] at hadj
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hpenB ⊢
        omega)
    (fun E hE => ⟨hδE E hE, by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hE
      refine ⟨d.fst, Sym2.mem_mk_left _ _, ?_⟩
      have hd' : d.fst ∈ δ.support.dropLast := by
        rw [← SimpleGraph.Walk.map_fst_darts]; exact List.mem_map_of_mem hd
      have h₁ := hδ _ hd'
      have h₂ := hδ1 _ (List.mem_of_mem_dropLast hd')
      rw [mem_Icc_two_iff] at h₁ ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ ⊢
      omega⟩)
  have hfδ := localConn_trans (mem_localConn_of_adj_of_notMem (lo := qlo) (hi := qhi)
    (by rw [zdGraph_two_adj_iff]; omega) hslQ hsQ he₁ hd₁.1 hd₁.2) hδQ
  have hposs : perimeterPos qlo qhi s = s 0 - qlo 0 := perimeterPos_of_bottom (by omega)
  obtain ⟨hlow, hup⟩ := le_perimeterPos_of_dualConfig_left (by omega) (by omega)
    (show s 1 = qlo 1 by omega) (by omega) (by omega) hpQ hf₀0 hf₀1 hgQ huQ hug
    (by omega) hαQ hfδ
  -- the open walk does not land at the lower-left corner of the half-box
  have hpne : ¬(p 0 = x 0 - R ∧ p 1 = x 1) := by
    rintro ⟨hp0, hp1'⟩
    have : perimeterPos qlo qhi p = 0 := by rw [perimeterPos_of_bottom (by omega)]; omega
    omega
  rw [landingPos_true, perimeterPos_eq_add_of_mem_boxBoundary hR
    ⟨hql0, hql1⟩ ⟨hqh0, hqh1⟩ hp hp1 hpne, hland]
  omega

/-- **The landing order on the right of a point of the line.** Let `s` be a point of the line
through `x`, the edge on its right closed, `α` an open walk from `s` inside `B_R(x)`, above the
line, to the boundary, and `δ` a dual walk from the face above that edge (the face with lower-left
corner `s`), above the line, leaving the faces of `B_R(x)` at its last step only. Then the dual
step lands before `α`, counterclockwise from the right end of the line. -/
theorem lt_landingPos_of_dualWalk_right {x s sr fR p g : LatticeSite 2} {R : ℕ}
    (hs1 : s 1 = x 1) (hs0 : x 0 - R + 1 ≤ s 0) (hs0' : s 0 ≤ x 0 + R - 2)
    (hsr : sr 0 = s 0 + 1 ∧ sr 1 = s 1) (hfR : fR 0 = s 0 ∧ fR 1 = s 1)
    (α : (zdGraph 2).Walk s p) (hαe : ∀ e ∈ α.edges, e ∈ ω)
    (hαB : ∀ v ∈ α.support, v ∈ Icc (x - (R : LatticeSite 2)) (x + R))
    (hαH : ∀ v ∈ α.support, x 1 ≤ v 1)
    (hp : p ∈ boxBoundary (x - (R : LatticeSite 2)) (x + R)) (he₁ : s(s, sr) ∉ ω)
    (δ : (zdGraph 2).Walk fR g) (hδn : ¬δ.Nil)
    (hδ : ∀ f ∈ δ.support.dropLast, f ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδ1 : ∀ f ∈ δ.support, x 1 ≤ f 1) (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδE : ∀ E ∈ δ.edges, E ∈ dualConfig ω) :
    perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2)))
        (δ.penultimate + g + 1) < landingPos (x - R) (x + R) true α := by
  have hR : 1 ≤ R := by omega
  obtain ⟨qlo, hql0, hql1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 - R ∧ v 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  obtain ⟨qhi, hqh0, hqh1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 + R ∧ v 1 = x 1 + R :=
    ⟨![_, _], rfl, rfl⟩
  obtain ⟨f₀, hf₀0, hf₀1⟩ : ∃ v : LatticeSite 2, v 0 = s 0 ∧ v 1 + 1 = s 1 :=
    ⟨![s 0, s 1 - 1], by simp, by simp⟩
  have hne : qlo ≠ qhi := fun h => by have := congrFun h 1; omega
  -- the open walk in the upper half-box
  have hαQ : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc qlo qhi) s p :=
    mem_localConn_of_walk α (fun v hv => by
      have h₁ := hαB v hv
      have h₂ := hαH v hv
      rw [mem_Icc_two_iff] at h₁ ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at h₁
      omega) hαe
  have hp1 := hαH p α.end_mem_support
  have hpQ : p ∈ boxBoundary qlo qhi := by
    rw [mem_boxBoundary_two_iff] at hp ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hp
    omega
  -- the last dual step
  have hpen : δ.penultimate ∈ δ.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hδn]; exact SimpleGraph.Walk.end_mem_support _
  have hadj := δ.adj_penultimate hδn
  have hpenB := hδ _ hpen
  have hpen1 := hδ1 _ (List.mem_of_mem_dropLast hpen)
  have hg1 := hδ1 g δ.end_mem_support
  obtain ⟨u, huQ, hug, hxu, hland⟩ := exists_perimeterPos_two_nsmul_eq hR ⟨hql0, hql1⟩
    ⟨hqh0, hqh1⟩ hpenB hg hadj hpen1 hg1
  have huP := perimeterPos_lt hne huQ.1
  -- the case of an open walk landing at the left end of the line
  by_cases hpne : p 0 = x 0 - R ∧ p 1 = x 1
  · have hpos : perimeterPos (x - (R : LatticeSite 2)) (x + R) p = 7 * R := by
      unfold perimeterPos
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
      split_ifs <;> omega
    rw [landingPos_true, hpos, hland]
    omega
  obtain ⟨u', hu'Q, hu'g, hu'⟩ := exists_perimeterPos_two_nsmul_add_one_eq hR ⟨hql0, hql1⟩
    ⟨hqh0, hqh1⟩ hpenB hg hadj hpen1 hg1
  -- the dual path in the upper half-box, from the face below the closed edge
  have hsQ : s ∈ Icc qlo qhi := by rw [mem_Icc_two_iff]; omega
  have hsrQ : sr ∈ Icc qlo qhi := by rw [mem_Icc_two_iff]; omega
  have hd₁ : f₀ ∈ dualEdge s(s, sr) ∧ fR ∈ dualEdge s(s, sr) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hgQ : g ∉ Icc qlo (qhi - 1) := fun h => hg (by
    rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega)
  have hδQ := dualConfig_inter_image_mem_localConn_of_walk (lo := qlo) (hi := qhi) δ
    (fun f hf => by
      rw [← SimpleGraph.Walk.dropLast_support_concat δ, List.mem_append,
        List.mem_singleton] at hf
      rcases hf with hf | rfl
      · have h₁ := hδ f hf
        have h₂ := hδ1 f (List.mem_of_mem_dropLast hf)
        rw [mem_Icc_two_iff] at h₁ ⊢
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ ⊢
        omega
      · rw [mem_Icc_two_iff] at hpenB ⊢
        rw [zdGraph_two_adj_iff] at hadj
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hpenB ⊢
        omega)
    (fun E hE => ⟨hδE E hE, by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hE
      refine ⟨d.fst, Sym2.mem_mk_left _ _, ?_⟩
      have hd' : d.fst ∈ δ.support.dropLast := by
        rw [← SimpleGraph.Walk.map_fst_darts]; exact List.mem_map_of_mem hd
      have h₁ := hδ _ hd'
      have h₂ := hδ1 _ (List.mem_of_mem_dropLast hd')
      rw [mem_Icc_two_iff] at h₁ ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ ⊢
      omega⟩)
  have hfδ := localConn_trans (mem_localConn_of_adj_of_notMem (lo := qlo) (hi := qhi)
    (by rw [zdGraph_two_adj_iff]; omega) hsQ hsrQ he₁ hd₁.1 hd₁.2) hδQ
  have hposs : perimeterPos qlo qhi s = s 0 - qlo 0 := perimeterPos_of_bottom (by omega)
  -- the open walk lands at least `2R` after the lower-left corner of the half-box
  have hp2 : 2 * (R : ℤ) ≤ perimeterPos qlo qhi p := by
    rw [mem_boxBoundary_two_iff] at hp
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hp
    unfold perimeterPos
    split_ifs <;> omega
  rcases hu' with ⟨hu'2, hland'⟩ | hu'0
  · have hle := le_perimeterPos_of_dualConfig_right (by omega) (by omega)
      (show s 1 = qlo 1 by omega) (by omega) (by omega) hpQ hf₀0 hf₀1 hgQ hu'Q hu'g
      (by omega) hαQ hfδ
    rw [landingPos_true, perimeterPos_eq_add_of_mem_boxBoundary hR
      ⟨hql0, hql1⟩ ⟨hqh0, hqh1⟩ hp hp1 hpne]
    omega
  · -- the lowest edge of the left side: impossible by interlacing
    exfalso
    obtain ⟨x', hx'0, hx'1⟩ : ∃ v : LatticeSite 2, v 0 = s 0 + 1 ∧ v 1 = s 1 :=
      ⟨![_, _], rfl, rfl⟩
    have hsB : s ∈ boxBoundary qlo qhi := by rw [mem_boxBoundary_two_iff]; omega
    have hx'B : x' ∈ boxBoundary qlo qhi := by rw [mem_boxBoundary_two_iff]; omega
    have hfo : f₀ ∉ Icc qlo (qhi - 1) := by
      rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
    have hx'f : x' ∈ Icc f₀ (f₀ + 1) := by
      rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    have hpx' : perimeterPos qlo qhi x' = s 0 + 1 - qlo 0 := by
      rw [perimeterPos_of_bottom (by omega), hx'0]
    exact dualConfig_inter_notMem_localConn_of_interlaced (by omega) (by omega) hαQ hsB hpQ hfo
      hx'B hx'f hgQ hu'Q hu'g (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩) hfδ

/-! ### The arms of a dual–open–dual point -/

/-- **The arms of three half-plane arms with colours dual, open, dual.** The open arm leaves `x`
upwards, and the two dual arms start at the two faces above `x`, one on each side of that edge:
an open arm stepping to the right (left) of `x` would leave both faces above `x` on its left
(right), so the dual arm landing before (after) it could not exist, by interlacing in the upper
half-box with the edges at `x` closed. -/
theorem exists_arms_of_mem_halfArmEvent_three {R : ℕ} (hR : 2 ≤ R) {x : LatticeSite 2}
    (hω : ω ∈ halfArmEvent ![false, true, false] x 0 R) :
    ∃ (p : LatticeSite 2) (α : (zdGraph 2).Walk x p), IsOpenArm ω x 0 (x - R) (x + R) α ∧
      (∀ v ∈ α.support, x 1 ≤ v 1) ∧ α.snd 0 = x 0 ∧ α.snd 1 = x 1 + 1 ∧
      (∃ (f g : LatticeSite 2) (β : (zdGraph 2).Walk f g), f 0 + 1 = x 0 ∧ f 1 = x 1 ∧
        IsDualArm ω x 0 (x - R) (x + R) β ∧ ∀ h ∈ β.support, x 1 ≤ h 1) ∧
      (∃ (f g : LatticeSite 2) (β : (zdGraph 2).Walk f g), f 0 = x 0 ∧ f 1 = x 1 ∧
        IsDualArm ω x 0 (x - R) (x + R) β ∧ ∀ h ∈ β.support, x 1 ≤ h 1) := by
  obtain ⟨a, b, γ, hγ, hd, hH, ho⟩ := mem_halfArmEvent_iff.1 hω
  have hα : IsOpenArm ω x 0 (x - R) (x + R) (γ 1) := hγ 1
  have hβ₀ : IsDualArm ω x 0 (x - R) (x + R) (γ 0) := hγ 0
  have hβ₂ : IsDualArm ω x 0 (x - R) (x + R) (γ 2) := hγ 2
  have ho₀ : landingPos (x - R) (x + R) false (γ 0) < landingPos (x - R) (x + R) true (γ 1) :=
    ho (show (0 : Fin 3) < 1 by decide)
  have ho₂ : landingPos (x - R) (x + R) true (γ 1) < landingPos (x - R) (x + R) false (γ 2) :=
    ho (show (1 : Fin 3) < 2 by decide)
  have ha1 : a 1 = x := by
    have := hα.isCrossing.start_mem
    simpa using this
  subst ha1
  set x := a 1 with hxdef
  have hHα : ∀ v ∈ (γ 1).support, x 1 ≤ v 1 := hH 1
  have hH₀ : ∀ v ∈ (γ 0).support, x 1 ≤ v 1 := hH 0
  have hH₂ : ∀ v ∈ (γ 2).support, x 1 ≤ v 1 := hH 2
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  -- the points and faces at `x`
  obtain ⟨xl, hxl0, hxl1⟩ : ∃ v : LatticeSite 2, v 0 + 1 = x 0 ∧ v 1 = x 1 :=
    ⟨![x 0 - 1, x 1], by simp, by simp⟩
  obtain ⟨xr, hxr0, hxr1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 + 1 ∧ v 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  obtain ⟨xu, hxu0, hxu1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 ∧ v 1 = x 1 + 1 := ⟨![_, _], rfl, rfl⟩
  obtain ⟨fL, hfL0, hfL1⟩ : ∃ v : LatticeSite 2, v 0 + 1 = x 0 ∧ v 1 = x 1 :=
    ⟨![x 0 - 1, x 1], by simp, by simp⟩
  -- the arms are not trivial
  have hS : Icc (x - ((0 : ℕ) : LatticeSite 2) - 1) (x + ((0 : ℕ) : LatticeSite 2)) ⊆
      Icc (x - R) (x + R - 1) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Nat.cast_zero, sub_zero, add_zero, Pi.sub_apply, Pi.add_apply, Pi.one_apply,
      Pi.natCast_apply, Pi.zero_apply] at hv ⊢
    omega
  have hB : Icc (x - ((0 : ℕ) : LatticeSite 2)) (x + ((0 : ℕ) : LatticeSite 2)) ⊆
      Icc (x - R + 1) (x + R - 1) := by
    intro v hv
    simp only [Nat.cast_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff] at hv
    subst hv
    rw [mem_Icc_two_iff]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hαn : ¬(γ 1).Nil := hα.not_nil hB
  have hβ₀n : ¬(γ 0).Nil := hβ₀.isCrossing.not_nil hS
  have hβ₂n : ¬(γ 2).Nil := hβ₂.isCrossing.not_nil hS
  have hαB : ∀ v ∈ (γ 1).support, v ∈ Icc (x - (R : LatticeSite 2)) (x + R) :=
    fun v hv => hα.mem_Icc hαn hv
  have hpB := hα.end_mem_boxBoundary hαn
  -- the first faces of the dual arms
  have hstart : ∀ i, IsDualArm ω x 0 (x - R) (x + R) (γ i) → (∀ v ∈ (γ i).support, x 1 ≤ v 1) →
      (a i 0 + 1 = x 0 ∨ a i 0 = x 0) ∧ a i 1 = x 1 := by
    intro i hi hiH
    have h₁ := hi.isCrossing.start_mem
    have h₂ := hiH _ (SimpleGraph.Walk.start_mem_support _)
    rw [mem_Icc_two_iff] at h₁
    simp only [Nat.cast_zero, sub_zero, add_zero, Pi.sub_apply, Pi.one_apply] at h₁
    omega
  have h₀s := hstart 0 hβ₀ hH₀
  have h₂s := hstart 2 hβ₂ hH₂
  have hne₀₂ : a 0 ≠ a 2 := fun h => hd.2 0 2 (by decide) rfl rfl (a 0)
    (SimpleGraph.Walk.start_mem_support _) (by rw [h]; exact SimpleGraph.Walk.start_mem_support _)
  -- the first step of the open arm
  have hsnd : (zdGraph 2).Adj x (γ 1).snd := (γ 1).adj_snd hαn
  have hsnd1 := hHα _ (List.mem_of_mem_tail ((γ 1).snd_mem_tail_support hαn))
  have hedge : ∀ e ∈ (γ 1).edges, x ∈ e → e = s(x, (γ 1).snd) := fun e he hx =>
    IsOpenArm.eq_of_mem_edges_of_mem hα he hx
  have hne : ∀ p p' : LatticeSite 2, p ≠ p' → s(x, p) ≠ s(x, p') := fun p p' hpp' h => by
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, h'⟩
    · exact hpp' h
    · exact hpp' (h'.trans h)
  have hdu : dualEdge s(x, xu) = s(fL, x) := by
    refine (Sym2.mem_and_mem_iff (fun h => by have := congrFun h 0; omega)).1 ⟨?_, ?_⟩ <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hadjxu : (zdGraph 2).Adj x xu := by rw [zdGraph_two_adj_iff]; omega
  have hdual_u : ∀ η : Config (LatticeSite 2), s(x, xu) ∉ η → s(fL, x) ∈ dualConfig η :=
    fun η h => (mem_dualConfig_iff' _ _).2 ⟨s(x, xu), hadjxu, h, hdu⟩
  have hsndr : ¬((γ 1).snd 0 = x 0 + 1 ∧ (γ 1).snd 1 = x 1) := by
    rintro ⟨hs0, hs1⟩
    have hsx : (γ 1).snd = xr := hpt _ _ (by omega) (by omega)
    have hl : ∀ e ∈ (γ 1).edges, e ≠ s(xl, x) := fun e he h => by
      have := hedge e he (h ▸ Sym2.mem_mk_right _ _)
      rw [h, hsx, Sym2.eq_swap] at this
      exact hne _ _ (fun h' => by have := congrFun h' 0; omega) this
    have hu : ∀ e ∈ (γ 1).edges, e ≠ s(x, xu) := fun e he h => by
      have := hedge e he (h ▸ Sym2.mem_mk_left _ _)
      rw [h, hsx] at this
      exact hne _ _ (fun h' => by have := congrFun h' 1; omega) this
    rcases h₀s.1 with h₀ | h₀
    · -- the dual arm landing first starts at the upper-left face
      have h := landingPos_lt_of_dualWalk_left (ω := ω \ {s(xl, x)}) (x := x) (s := x)
        (sl := xl) (fL := a 0) rfl (by omega) (by omega) ⟨hxl0, hxl1⟩ ⟨h₀, h₀s.2⟩ (γ 1)
        (fun e he => ⟨hα.mem_of_mem_edges e he, hl e he⟩) hαB hHα hpB (fun h => h.2 rfl) (γ 0)
        hβ₀n hβ₀.isCrossing.mem_of_mem_dropLast hH₀ hβ₀.isCrossing.end_notMem
        (fun E hE => dualConfig_anti sdiff_subset (hβ₀.mem_of_mem_edges E hE))
      rw [landingPos_false] at ho₀
      exact absurd ho₀ (not_lt.2 h.le)
    · -- the dual arm landing first starts at the upper-right face: prepend the upper-left face
      have hadj : (zdGraph 2).Adj fL (a 0) := by rw [zdGraph_two_adj_iff]; omega
      have h := landingPos_lt_of_dualWalk_left (ω := (ω \ {s(xl, x)}) \ {s(x, xu)}) (x := x)
        (s := x) (sl := xl) (fL := fL) rfl (by omega) (by omega) ⟨hxl0, hxl1⟩ ⟨hfL0, hfL1⟩ (γ 1)
        (fun e he => ⟨⟨hα.mem_of_mem_edges e he, hl e he⟩, hu e he⟩) hαB hHα hpB
        (fun h => h.1.2 rfl) (SimpleGraph.Walk.cons hadj (γ 0)) SimpleGraph.Walk.not_nil_cons
        (fun f hf => by
          rw [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil
            (SimpleGraph.Walk.support_ne_nil _), List.mem_cons] at hf
          rcases hf with rfl | hf
          · rw [mem_Icc_two_iff]
            simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
            omega
          · exact hβ₀.isCrossing.mem_of_mem_dropLast f hf)
        (fun f hf => by
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hf
          rcases hf with rfl | hf
          · omega
          · exact hH₀ f hf)
        hβ₀.isCrossing.end_notMem
        (fun E hE => by
          rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hE
          rcases hE with rfl | hE
          · rw [show s(fL, a 0) = s(fL, x) from congrArg (fun v => s(fL, v))
              (hpt _ _ (by omega) (by omega))]
            exact hdual_u _ (fun h => h.2 rfl)
          · exact dualConfig_anti (sdiff_subset.trans sdiff_subset) (hβ₀.mem_of_mem_edges E hE))
      rw [SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hβ₀n] at h
      rw [landingPos_false] at ho₀
      exact absurd ho₀ (not_lt.2 h.le)
  have hsndl : ¬((γ 1).snd 0 + 1 = x 0 ∧ (γ 1).snd 1 = x 1) := by
    rintro ⟨hs0, hs1⟩
    have hsx : (γ 1).snd = xl := hpt _ _ (by omega) (by omega)
    have hr : ∀ e ∈ (γ 1).edges, e ≠ s(x, xr) := fun e he h => by
      have := hedge e he (h ▸ Sym2.mem_mk_left _ _)
      rw [h, hsx] at this
      exact hne _ _ (fun h' => by have := congrFun h' 0; omega) this
    have hu : ∀ e ∈ (γ 1).edges, e ≠ s(x, xu) := fun e he h => by
      have := hedge e he (h ▸ Sym2.mem_mk_left _ _)
      rw [h, hsx] at this
      exact hne _ _ (fun h' => by have := congrFun h' 1; omega) this
    rcases h₂s.1 with h₂ | h₂
    · -- the dual arm landing last starts at the upper-left face: prepend the upper-right face
      have hadj : (zdGraph 2).Adj x (a 2) := by rw [zdGraph_two_adj_iff]; omega
      have h := lt_landingPos_of_dualWalk_right (ω := (ω \ {s(x, xr)}) \ {s(x, xu)}) (x := x)
        (s := x) (sr := xr) (fR := x) rfl (by omega) (by omega) ⟨hxr0, hxr1⟩ ⟨rfl, rfl⟩ (γ 1)
        (fun e he => ⟨⟨hα.mem_of_mem_edges e he, hr e he⟩, hu e he⟩) hαB hHα hpB
        (fun h => h.1.2 rfl) (SimpleGraph.Walk.cons hadj (γ 2)) SimpleGraph.Walk.not_nil_cons
        (fun f hf => by
          rw [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil
            (SimpleGraph.Walk.support_ne_nil _), List.mem_cons] at hf
          rcases hf with rfl | hf
          · rw [mem_Icc_two_iff]
            simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
            omega
          · exact hβ₂.isCrossing.mem_of_mem_dropLast f hf)
        (fun f hf => by
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact le_rfl
          · exact hH₂ f hf)
        hβ₂.isCrossing.end_notMem
        (fun E hE => by
          rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hE
          rcases hE with rfl | hE
          · rw [show s(x, a 2) = s(fL, x) from
              (congrArg (fun v => s(x, v)) (hpt _ _ (by omega) (by omega))).trans Sym2.eq_swap]
            exact hdual_u _ (fun h => h.2 rfl)
          · exact dualConfig_anti (sdiff_subset.trans sdiff_subset) (hβ₂.mem_of_mem_edges E hE))
      rw [SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hβ₂n] at h
      rw [landingPos_false] at ho₂
      exact absurd ho₂ (not_lt.2 h.le)
    · -- the dual arm landing last starts at the upper-right face
      have h := lt_landingPos_of_dualWalk_right (ω := ω \ {s(x, xr)}) (x := x) (s := x)
        (sr := xr) (fR := a 2) rfl (by omega) (by omega) ⟨hxr0, hxr1⟩ ⟨h₂, h₂s.2⟩ (γ 1)
        (fun e he => ⟨hα.mem_of_mem_edges e he, hr e he⟩) hαB hHα hpB (fun h => h.2 rfl) (γ 2)
        hβ₂n hβ₂.isCrossing.mem_of_mem_dropLast hH₂ hβ₂.isCrossing.end_notMem
        (fun E hE => dualConfig_anti sdiff_subset (hβ₂.mem_of_mem_edges E hE))
      rw [landingPos_false] at ho₂
      exact absurd ho₂ (not_lt.2 h.le)
  have hsu : (γ 1).snd 0 = x 0 ∧ (γ 1).snd 1 = x 1 + 1 := by
    rw [zdGraph_two_adj_iff] at hsnd
    omega
  refine ⟨b 1, γ 1, hα, hHα, hsu.1, hsu.2, ?_, ?_⟩
  · rcases h₀s.1 with h₀ | h₀
    · exact ⟨a 0, b 0, γ 0, h₀, h₀s.2, hβ₀, hH₀⟩
    · have h₂ : a 2 0 + 1 = x 0 := by
        rcases h₂s.1 with h₂ | h₂
        · exact h₂
        · exact absurd (hpt _ _ (by omega) (by omega)) hne₀₂
      exact ⟨a 2, b 2, γ 2, h₂, h₂s.2, hβ₂, hH₂⟩
  · rcases h₀s.1 with h₀ | h₀
    · have h₂ : a 2 0 = x 0 := by
        rcases h₂s.1 with h₂ | h₂
        · exact absurd (hpt _ _ (by omega) (by omega)) hne₀₂
        · exact h₂
      exact ⟨a 2, b 2, γ 2, h₂, h₂s.2, hβ₂, hH₂⟩
    · exact ⟨a 0, b 0, γ 0, h₀, h₀s.2, hβ₀, hH₀⟩

/-- **A dual–open–dual point is a separated point of its cluster** (the upper bound,
deterministic part). Let `x` have three arms to distance `R` in the upper half-plane through `x`,
dual, open, dual, and let the box `Icc lo hi` stand on the line through `x` inside the interior of
`B_R(x)`. In a configuration `ω' ⊆ ω` in which the edges on the left and on the right of `x` are
closed and the other edges of `ω` at or above the line are kept, `x` is joined inside the box to
its left, right or top side, and to no point of the bottom side two or more steps away: the dual
arms, prolonged through the closed edges, separate them. -/
theorem mem_of_mem_halfArmEvent_three {R : ℕ} (hR : 2 ≤ R) {x xl xr : LatticeSite 2}
    (hxl : xl 0 + 1 = x 0 ∧ xl 1 = x 1) (hxr : xr 0 = x 0 + 1 ∧ xr 1 = x 1)
    (hlo1 : lo 1 = x 1) (hlx : lo 0 < x 0) (hxh : x 0 < hi 0) (h₁ : lo 1 < hi 1)
    (hsub : Icc lo hi ⊆ Icc (x - R + 1) (x + R - 1))
    (hω : ω ∈ halfArmEvent ![false, true, false] x 0 R) {ω' : Config (LatticeSite 2)}
    (hω' : ω' ⊆ ω) (hl : s(xl, x) ∉ ω') (hr : s(x, xr) ∉ ω')
    (hkeep : ∀ e ∈ ω, (∀ v ∈ e, x 1 ≤ v 1) → e ≠ s(xl, x) → e ≠ s(x, xr) → e ∈ ω') :
    (∃ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
        ω' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
      (∀ a : LatticeSite 2, a 1 = lo 1 → a 0 + 2 ≤ x 0 →
        ω' ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a) ∧
      ∀ a : LatticeSite 2, a 1 = lo 1 → x 0 + 2 ≤ a 0 →
        ω' ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a := by
  obtain ⟨p, α, hα, hαH, hs0, hs1, ⟨fl, gl, βl, hfl0, hfl1, hβl, hβlH⟩,
    ⟨fr, gr, βr, hfr0, hfr1, hβr, hβrH⟩⟩ := exists_arms_of_mem_halfArmEvent_three hR hω
  have h₀ : lo 0 < hi 0 := by omega
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  obtain ⟨f₀, hf₀0, hf₀1⟩ : ∃ f : LatticeSite 2, f 0 + 1 = x 0 ∧ f 1 + 1 = x 1 :=
    ⟨![x 0 - 1, x 1 - 1], by simp, by simp⟩
  obtain ⟨f₀', hf₀'0, hf₀'1⟩ : ∃ f : LatticeSite 2, f 0 = x 0 ∧ f 1 + 1 = x 1 :=
    ⟨![x 0, x 1 - 1], by simp, by simp⟩
  have hxH : x ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxlH : xl ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxrH : xr ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hsub' : Icc lo (hi - 1) ⊆ Icc (x - R) (x + R - 1) := by
    intro f hf
    have h₁' := hsub (mem_Icc_of_mem_Icc_sub_one hf (left_mem_Icc.2 (by
      intro i; simp)))
    have h₂' := hsub (mem_Icc_of_mem_Icc_sub_one hf (right_mem_Icc.2 (by
      intro i; simp)))
    rw [mem_Icc_two_iff] at hf h₁' h₂' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, Pi.natCast_apply] at hf h₁' h₂' ⊢
    omega
  -- the open arm survives in `ω'`
  have hαn : ¬α.Nil := hα.not_nil (by
    intro v hv
    simp only [Nat.cast_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff] at hv
    subst hv
    exact hsub hxH)
  have hne : ∀ p p' : LatticeSite 2, p ≠ p' → s(x, p) ≠ s(x, p') := fun p p' hpp' h => by
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, h'⟩
    · exact hpp' h
    · exact hpp' (h'.trans h)
  have hαω' : ∀ e ∈ α.edges, e ∈ ω' := fun e he => by
    refine hkeep e (hα.mem_of_mem_edges e he)
      (fun v hv => hαH v (mem_support_of_mem_edge α he hv)) (fun h => ?_) (fun h => ?_)
    · have := IsOpenArm.eq_of_mem_edges_of_mem hα he (h ▸ Sym2.mem_mk_right _ _)
      rw [h, Sym2.eq_swap] at this
      exact hne _ _ (fun h' => by have := congrFun h' 1; omega) this
    · have := IsOpenArm.eq_of_mem_edges_of_mem hα he (h ▸ Sym2.mem_mk_left _ _)
      rw [h] at this
      exact hne _ _ (fun h' => by have := congrFun h' 1; omega) this
  have Lo := exists_inter_mem_localConn_of_isOpenArm hα (fun v hv => hlo1 ▸ hαH v hv) hxH hsub
    hαω'
  -- the dual paths from the faces below the closed edges
  have hflH : fl ∈ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  have hfrH : fr ∈ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  obtain ⟨g, y, hg, hy, hyg, hy1, q, hqs, hqE⟩ :=
    exists_walk_of_isDualArm hβl (fun f hf => hlo1 ▸ hβlH f hf) hflH hsub'
  obtain ⟨g', y', hg', hy', hy'g, hy'1, q', hq's, hq'E⟩ :=
    exists_walk_of_isDualArm hβr (fun f hf => hlo1 ▸ hβrH f hf) hfrH hsub'
  have hadjl : (zdGraph 2).Adj xl x := by rw [zdGraph_two_adj_iff]; omega
  have hadjr : (zdGraph 2).Adj x xr := by rw [zdGraph_two_adj_iff]; omega
  have hd₁ : f₀ ∈ dualEdge s(xl, x) ∧ fl ∈ dualEdge s(xl, x) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hd₃ : f₀' ∈ dualEdge s(x, xr) ∧ fr ∈ dualEdge s(x, xr) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hL := localConn_trans (mem_localConn_of_adj_of_notMem hadjl hxlH hxH hl hd₁.1 hd₁.2)
    (dualConfig_inter_image_mem_localConn_of_walk q hqs fun E hE =>
      ⟨dualConfig_anti hω' (hqE E hE).1, (hqE E hE).2⟩)
  have hR' := localConn_trans (mem_localConn_of_adj_of_notMem hadjr hxH hxrH hr hd₃.1 hd₃.2)
    (dualConfig_inter_image_mem_localConn_of_walk q' hq's fun E hE =>
      ⟨dualConfig_anti hω' (hq'E E hE).1, (hq'E E hE).2⟩)
  refine ⟨Lo, fun a' ha'1 hax => ?_, fun a' ha'1 hax => ?_⟩
  · by_cases ha'0 : lo 0 ≤ a' 0
    · exact notMem_localConn_of_dualConfig_left h₀ h₁ hlo1.symm hlx hxh.le ha'1 ha'0 hax hf₀0
        hf₀1 hg hy hyg hy1 hL
    · rw [localConn_of_notMem_right (by rw [mem_Icc_two_iff]; omega)]
      exact notMem_empty _
  · by_cases ha'0 : a' 0 ≤ hi 0
    · exact notMem_localConn_of_dualConfig_right h₀ h₁ hlo1.symm hlx.le hxh ha'1 ha'0 hax
        hf₀'0 hf₀'1 hg' hy' hy'g hy'1 hR'
    · rw [localConn_of_notMem_right (by rw [mem_Icc_two_iff]; omega)]
      exact notMem_empty _

/-! ### The upper bound: counting separated points in a square -/

/-- **A cluster that cannot leave through the bottom.** Let `Icc lo hi` be the part of the box
`Icc lo' hi` at or above the row of its bottom side. If every point of that row joined to `x`
inside `Icc lo hi` has its edge downwards closed, then every point joined to `x` inside the
larger box is joined to it inside `Icc lo hi`. -/
theorem mem_localConn_of_forall_notMem {lo' x z : LatticeSite 2} (hlo0 : lo' 0 = lo 0)
    (hx : x ∈ Icc lo hi)
    (hdown : ∀ u d : LatticeSite 2, u 1 = lo 1 → d 0 = u 0 → d 1 + 1 = u 1 →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x u → s(u, d) ∉ ω)
    (h : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo' hi) x z) :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x z := by
  classical
  obtain ⟨P, hPs, hPe⟩ := exists_walk_of_mem_localConn h
  by_cases hall : ∀ v ∈ P.support, v ∈ Icc lo hi
  · exact mem_localConn_of_walk P hall hPe
  push Not at hall
  obtain ⟨w, hw, hwU⟩ := hall
  obtain ⟨c, q, t, hqt, hc, hq⟩ :=
    SimpleGraph.Walk.exists_append_eq_of_notMem (P.takeUntil w hw) hwU
  have hqP : ∀ v ∈ q.support, v ∈ P.support := fun v hv => P.support_takeUntil_subset_support hw
    (by rw [← hqt, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hv)
  have hqe : ∀ e ∈ q.edges, e ∈ P.edges := fun e he => P.edges_takeUntil_subset_edges hw
    (by rw [← hqt, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he)
  have hqn : ¬q.Nil := fun hn => hc (by rw [← hn.eq]; exact hx)
  have hpen : q.penultimate ∈ q.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hqn]; exact SimpleGraph.Walk.end_mem_support _
  have hu := hq _ hpen
  have hcH := hPs c (hqP c q.end_mem_support)
  have hadj := q.adj_penultimate hqn
  have hxu : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x q.penultimate :=
    mem_localConn_of_walk q.dropLast (fun v hv => by
      rw [SimpleGraph.Walk.support_dropLast hqn] at hv; exact hq v hv)
      (fun e he => by
        rw [SimpleGraph.Walk.edges_dropLast] at he
        exact hPe e (hqe e (List.dropLast_subset _ he)))
  have hedge := hPe _ (hqe _ (q.mk_penultimate_end_mem_edges hqn))
  rw [mem_Icc_two_iff] at hu hcH hc
  rw [zdGraph_two_adj_iff] at hadj
  exact absurd hedge (hdown _ c (by omega) (by omega) (by omega) hxu)

/-- **Closing five edges of probability one half** multiplies a probability by at most `32`. -/
theorem law_setOf_sdiff_five_mem_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {e₁ e₂ e₃ e₄ e₅ : Sym2 (LatticeSite 2)} (h₁ : (q e₁ : ℝ) = 1 / 2) (h₂ : (q e₂ : ℝ) = 1 / 2)
    (h₃ : (q e₃ : ℝ) = 1 / 2) (h₄ : (q e₄ : ℝ) = 1 / 2) (h₅ : (q e₅ : ℝ) = 1 / 2)
    (F : Set (Config (LatticeSite 2))) :
    law q {ω | ((((ω \ {e₁}) \ {e₂}) \ {e₃}) \ {e₄}) \ {e₅} ∈ F} ≤ 32 * law q F := by
  calc law q {ω | ((((ω \ {e₁}) \ {e₂}) \ {e₃}) \ {e₄}) \ {e₅} ∈ F}
      ≤ 2 * law q {η | (((η \ {e₂}) \ {e₃}) \ {e₄}) \ {e₅} ∈ F} :=
        law_setOf_diff_singleton_mem_le h₁ {η | (((η \ {e₂}) \ {e₃}) \ {e₄}) \ {e₅} ∈ F}
    _ ≤ 2 * (2 * law q {η | ((η \ {e₃}) \ {e₄}) \ {e₅} ∈ F}) :=
        mul_le_mul_right (law_setOf_diff_singleton_mem_le h₂
          {η | ((η \ {e₃}) \ {e₄}) \ {e₅} ∈ F}) _
    _ ≤ 2 * (2 * (2 * law q {η | (η \ {e₄}) \ {e₅} ∈ F})) :=
        mul_le_mul_right (mul_le_mul_right (law_setOf_diff_singleton_mem_le h₃
          {η | (η \ {e₄}) \ {e₅} ∈ F}) _) _
    _ ≤ 2 * (2 * (2 * (2 * law q {η | η \ {e₅} ∈ F}))) :=
        mul_le_mul_right (mul_le_mul_right (mul_le_mul_right
          (law_setOf_diff_singleton_mem_le h₄ {η | η \ {e₅} ∈ F}) _) _) _
    _ ≤ 2 * (2 * (2 * (2 * (2 * law q F)))) :=
        mul_le_mul_right (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right
          (law_setOf_diff_singleton_mem_le h₅ F) _) _) _) _
    _ = 32 * law q F := by ring

/-- The events used in the count of separated points are measurable. -/
theorem measurableSet_setOf_exists_localConn_and_forall_and_forall (H : Set (LatticeSite 2))
    (x : LatticeSite 2) (P Q₁ Q₂ Q₃ : LatticeSite 2 → Prop) (E : Set (Sym2 (LatticeSite 2))) :
    MeasurableSet {η : Config (LatticeSite 2) | ((∃ v ∈ H, P v ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn H x v) ∧
      (∀ a : LatticeSite 2, Q₁ a → Q₂ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a) ∧
      ∀ a : LatticeSite 2, Q₁ a → Q₃ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a) ∧
      ∀ e ∈ E, e ∉ η} := by
  have h : {η : Config (LatticeSite 2) | ((∃ v ∈ H, P v ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn H x v) ∧
      (∀ a : LatticeSite 2, Q₁ a → Q₂ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a) ∧
      ∀ a : LatticeSite 2, Q₁ a → Q₃ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a) ∧
      ∀ e ∈ E, e ∉ η} =
      ({η : Config (LatticeSite 2) | (∃ v ∈ H, P v ∧ η ∩ (zdGraph 2).edgeSet ∈ localConn H x v) ∧
        ∀ a : LatticeSite 2, Q₁ a → Q₂ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a} ∩
      {η : Config (LatticeSite 2) | (∃ v ∈ H, P v ∧ η ∩ (zdGraph 2).edgeSet ∈ localConn H x v) ∧
        ∀ a : LatticeSite 2, Q₁ a → Q₃ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a}) ∩
      ⋂ e ∈ E, {η : Config (LatticeSite 2) | e ∈ η}ᶜ := by
    ext η
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff]
    tauto
  rw [h]
  exact ((measurableSet_setOf_exists_localConn_and_forall _ _ _ _ _).inter
    (measurableSet_setOf_exists_localConn_and_forall _ _ _ _ _)).inter
    (MeasurableSet.biInter (to_countable _) fun e _ => (measurableSet_mem e).compl)

/-- **Three arms in the half-plane, dual–open–dual, upper bound** (Werner's count of lowest
points). There is `C < ∞` such that `R² · P(A₃⁺(R)) ≤ C` for the colours dual, open, dual and
every profile equal to `1/2` on the edges of `ℤ²`. -/
theorem exists_mul_sq_law_halfArmEvent_three_le :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ,
        (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R) ≤ C := by
  classical
  obtain ⟨c, hc⟩ := exists_crossingBounds_half
  set q₀ : Sym2 (LatticeSite 2) → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
  have hq₀ : ∀ e ∈ (zdGraph 2).edgeSet, (q₀ e : ℝ) = 1 / 2 := fun _ _ => rfl
  set β := c 7 ^ 4 with hβ
  have hβ0 : β ≠ 0 := (ENNReal.pow_pos ((hc q₀ hq₀).pos 7) 4).ne'
  have hβ1 : β ≤ 1 :=
    (pow_le_law_compl_crossing_inter (hc q₀ hq₀) (t := 1) (m := 1) rfl le_top).trans prob_le_one
  refine ⟨1024 * β⁻¹ + 16, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.inv_ne_top.2 hβ0), ENNReal.ofNat_ne_top⟩, fun q hq R => ?_⟩
  have hCB := hc q hq
  set s := (R - 1) / 4 with hs
  by_cases hs1 : s = 0
  · have hR : (R : ℝ≥0∞) ^ 2 ≤ 16 := by
      have : R ≤ 4 := by omega
      calc (R : ℝ≥0∞) ^ 2 ≤ (4 : ℝ≥0∞) ^ 2 := by gcongr; exact_mod_cast this
        _ = 16 := by norm_num
    calc (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R) ≤ 16 * 1 :=
          mul_le_mul' hR prob_le_one
      _ ≤ 1024 * β⁻¹ + 16 := by rw [mul_one]; exact le_add_self
  -- the event joining `B_s(0)` to sup-norm `3s`, and its probability
  set Cs := {η : Config (LatticeSite 2) | ∃ u v : LatticeSite 2,
      (|u 0| ≤ s ∧ |u 1| ≤ s) ∧ (3 * (s : ℤ) ≤ |v 0| ∨ 3 * (s : ℤ) ≤ |v 1|) ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn univ u v} with hCs
  have hCup : IsUpperSet Cs := fun a b hab ha => by
    obtain ⟨u, w, hu, hw, h⟩ := ha
    exact ⟨u, w, hu, hw, localConn_mono (inter_subset_inter_left _ hab) h⟩
  have hlam : law q Cs ≤ 1 - β := by
    have hK := pow_le_law_compl_crossing_inter hCB (t := s) (m := 2 * s - 1) (by omega) le_top
    set K := (crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])ᶜ ∩
      (crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])ᶜ ∩
      (crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])ᶜ ∩
      (crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])ᶜ with hKdef
    have hKm : MeasurableSet K := (((measurableSet_crossing _ _ _).compl.inter
      (measurableSet_crossing _ _ _).compl).inter (measurableSet_crossing _ _ _).compl).inter
      (measurableSet_crossing _ _ _).compl
    have hsub : Cs ⊆ Kᶜ := fun η hη hK' => by
      obtain ⟨u, v, hu, hv, h⟩ := hη
      exact notMem_localConn_of_notMem_crossing hK'.1.1.1 hK'.1.1.2 hK'.1.2 hK'.2 hu hv univ h
    calc law q Cs ≤ law q Kᶜ := measure_mono hsub
      _ = 1 - law q K := prob_compl_eq_one_sub hKm
      _ ≤ 1 - β := tsub_le_tsub_left hK 1
  -- the square `B_s(0)`, its points, and the half-boxes standing on them
  set H : Set (LatticeSite 2) := Icc ![-(3 * (s : ℤ)), -(3 * s)] ![3 * (s : ℤ), 3 * s] with hH
  set hi : LatticeSite 2 := ![3 * (s : ℤ), 3 * s] with hhi
  have hhi0 : hi 0 = 3 * (s : ℤ) := rfl
  have hhi1 : hi 1 = 3 * (s : ℤ) := rfl
  set S : Finset (ℤ × ℤ) := Finset.Icc (-(s : ℤ)) s ×ˢ Finset.Icc (-(s : ℤ)) s with hSdef
  set F : ℤ × ℤ → Set (Config (LatticeSite 2)) := fun i => {η : Config (LatticeSite 2) |
      ((∃ v ∈ Icc (![-(3 * (s : ℤ)), i.2] : LatticeSite 2) hi,
        (v 0 = -(3 * (s : ℤ)) ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc ![-(3 * (s : ℤ)), i.2] hi) ![i.1, i.2] v) ∧
        (∀ a : LatticeSite 2, a 1 = i.2 → a 0 + 2 ≤ i.1 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc ![-(3 * (s : ℤ)), i.2] hi) ![i.1, i.2] a) ∧
        ∀ a : LatticeSite 2, a 1 = i.2 → i.1 + 2 ≤ a 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc ![-(3 * (s : ℤ)), i.2] hi) ![i.1, i.2] a) ∧
      ∀ e ∈ ({s(![i.1, i.2], ![i.1, i.2 - 1]), s(![i.1 - 1, i.2], ![i.1 - 1, i.2 - 1]),
        s(![i.1 + 1, i.2], ![i.1 + 1, i.2 - 1])} : Set (Sym2 (LatticeSite 2))), e ∉ η} with hFdef
  have hFm : ∀ i, MeasurableSet (F i) := fun i =>
    measurableSet_setOf_exists_localConn_and_forall_and_forall _ _ _ _ _ _ _
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  -- a separated point does not leave its half-box through the bottom
  have hesc : ∀ (i : ℤ × ℤ) (η : Config (LatticeSite 2)) (z : LatticeSite 2), i ∈ S → η ∈ F i →
      η ∩ (zdGraph 2).edgeSet ∈ localConn H ![i.1, i.2] z →
      η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc ![-(3 * (s : ℤ)), i.2] hi) ![i.1, i.2] z := by
    intro i η z hi' hη h
    rw [hSdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hi'
    refine mem_localConn_of_forall_notMem (lo' := ![-(3 * (s : ℤ)), -(3 * s)]) rfl
      (by rw [mem_Icc_two_iff]; simp [hhi0, hhi1]; omega)
      (fun u d hu1 hd0 hd1 hxu => ?_) h
    obtain ⟨⟨-, hL, hR⟩, hE⟩ := hη
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hu1
    have hu0 : i.1 - 1 ≤ u 0 ∧ u 0 ≤ i.1 + 1 := by
      constructor
      · by_contra hc'
        exact hL u (by simpa using hu1) (by omega) hxu
      · by_contra hc'
        exact hR u (by simpa using hu1) (by omega) hxu
    rcases (show u 0 = i.1 ∨ u 0 = i.1 - 1 ∨ u 0 = i.1 + 1 by omega) with h0 | h0 | h0
    · have e₁ : u = ![i.1, i.2] := hpt _ _ (by simp [h0]) (by simp [hu1])
      have e₂ : d = ![i.1, i.2 - 1] := hpt _ _ (by simp [hd0, h0]) (by simp; omega)
      rw [e₁, e₂]
      exact hE _ (by simp)
    · have e₁ : u = ![i.1 - 1, i.2] := hpt _ _ (by simp [h0]) (by simp [hu1])
      have e₂ : d = ![i.1 - 1, i.2 - 1] := hpt _ _ (by simp [hd0, h0]) (by simp; omega)
      rw [e₁, e₂]
      exact hE _ (by simp)
    · have e₁ : u = ![i.1 + 1, i.2] := hpt _ _ (by simp [h0]) (by simp [hu1])
      have e₂ : d = ![i.1 + 1, i.2 - 1] := hpt _ _ (by simp [hd0, h0]) (by simp; omega)
      rw [e₁, e₂]
      exact hE _ (by simp)
  -- separated points of one parity lie in distinct clusters of the square
  have hcount : ∀ r : ℤ, ∑ i ∈ S.filter (fun i => i.1 % 2 = r), law q (F i) ≤ β⁻¹ := by
    intro r
    refine (sum_law_le_sum_pow_of_forall_mem_foldl q hCup _ F hFm fun η T hT hTF => ?_).trans
      (sum_range_pow_succ_le_inv hβ1 hlam _)
    refine mem_foldl_of_pairwise_notMem_localConn (H := H) T (fun i => ![i.1, i.2])
      (fun i hi' => ?_) (fun i hi' => ?_) fun i hi' j hj hij => ?_
    · have := Finset.mem_product.1 (Finset.mem_filter.1 (hT hi')).1
      rw [Finset.mem_Icc, Finset.mem_Icc] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [abs_le, abs_le]
      omega
    · obtain ⟨⟨⟨v, hv, hv', h⟩, -⟩, -⟩ := hTF i hi'
      have hiS := Finset.mem_product.1 (Finset.mem_filter.1 (hT hi')).1
      rw [Finset.mem_Icc, Finset.mem_Icc] at hiS
      refine ⟨v, ?_, localConn_mono_set (fun w hw => ?_) _ _ h⟩
      · rw [mem_Icc_two_iff] at hv
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hhi0, hhi1] at hv hv'
        rw [le_abs, le_abs]
        omega
      · rw [mem_Icc_two_iff] at hw ⊢
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hhi0, hhi1] at hw ⊢
        omega
    · have hiS := (Finset.mem_filter.1 (hT hi')).1
      have hjS := (Finset.mem_filter.1 (hT hj)).1
      have hir := (Finset.mem_filter.1 (hT hi')).2
      have hjr := (Finset.mem_filter.1 (hT hj)).2
      intro hconn
      have h₁ := hesc i η _ hiS (hTF i hi') hconn
      have h₂ := hesc j η _ hjS (hTF j hj) (by rw [localConn_comm]; exact hconn)
      have hj1 := (mem_Icc_two_iff.1 h₁.2.1).2.2.1
      have hi1 := (mem_Icc_two_iff.1 h₂.2.1).2.2.1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hj1 hi1
      have hij1 : i.2 = j.2 := le_antisymm (by simpa using hj1) (by simpa using hi1)
      have hij0 : i.1 ≠ j.1 := fun h => hij (Prod.ext h hij1)
      obtain ⟨⟨-, hL, hR⟩, -⟩ := hTF i hi'
      rcases (show j.1 + 2 ≤ i.1 ∨ i.1 + 2 ≤ j.1 by omega) with h | h
      · exact hL _ (by simp [hij1]) (by simpa using h) h₁
      · exact hR _ (by simp [hij1]) (by simpa using h) h₁
  have hsum : ∑ i ∈ S, law q (F i) ≤ 2 * β⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun i : ℤ × ℤ => i.1 % 2 = 0), two_mul]
    have hno : ∀ k : ℤ, ¬k % 2 = 0 ↔ k % 2 = 1 := fun k => by omega
    simp only [hno]
    exact add_le_add (hcount 0) (hcount 1)
  -- each three-arm point is, after closing five edges, a separated point
  have hs4 : 4 * s + 1 ≤ R := by omega
  have hedge : ∀ u v : LatticeSite 2, (zdGraph 2).Adj u v → (q s(u, v) : ℝ) = 1 / 2 :=
    fun u v h => hq _ h
  have hptS : ∀ i ∈ S, law q (halfArmEvent ![false, true, false] ![i.1, i.2] 0 R) ≤
      32 * law q (F i) := by
    intro i hi'
    rw [hSdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hi'
    obtain ⟨k, l⟩ := i
    simp only at hi' ⊢
    refine (measure_mono fun ω hω => ?_).trans (law_setOf_sdiff_five_mem_le
      (hedge ![k - 1, l] ![k, l] (by rw [zdGraph_two_adj_iff]; simp))
      (hedge ![k, l] ![k + 1, l] (by rw [zdGraph_two_adj_iff]; simp))
      (hedge ![k, l] ![k, l - 1] (by rw [zdGraph_two_adj_iff]; simp))
      (hedge ![k - 1, l] ![k - 1, l - 1] (by rw [zdGraph_two_adj_iff]; simp))
      (hedge ![k + 1, l] ![k + 1, l - 1] (by rw [zdGraph_two_adj_iff]; simp)) (F (k, l)))
    have hsubk : Icc (![-(3 * (s : ℤ)), l] : LatticeSite 2) hi ⊆
        Icc ((![k, l] : LatticeSite 2) - R + 1) (![k, l] + R - 1) := by
      intro v hv
      rw [mem_Icc_two_iff, hhi0, hhi1] at hv
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, Pi.natCast_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
      omega
    have hrow : ∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, l ≤ v 1) → ∀ a b : ℤ,
        e ≠ s(![a, l], ![a, l - 1]) := by
      rintro e he a b rfl
      have := he _ (Sym2.mem_mk_right _ _)
      simp at this
    have hkey := mem_of_mem_halfArmEvent_three (lo := ![-(3 * (s : ℤ)), l]) (hi := hi)
      (x := ![k, l]) (xl := ![k - 1, l]) (xr := ![k + 1, l]) (by omega) (by simp) (by simp)
      (by simp) (by simp; omega) (by simp [hhi0]; omega) (by simp [hhi1]; omega) hsubk hω
      (ω' := ((((ω \ {s(![k - 1, l], ![k, l])}) \ {s(![k, l], ![k + 1, l])}) \
        {s(![k, l], ![k, l - 1])}) \ {s(![k - 1, l], ![k - 1, l - 1])}) \
        {s(![k + 1, l], ![k + 1, l - 1])})
      (fun e he => he.1.1.1.1.1) (fun h => h.1.1.1.1.2 rfl) (fun h => h.1.1.1.2 rfl)
      (fun e he hH hl hr => ⟨⟨⟨⟨⟨he, hl⟩, hr⟩, hrow e (by simpa using hH) k 0⟩,
        hrow e (by simpa using hH) (k - 1) 0⟩, hrow e (by simpa using hH) (k + 1) 0⟩)
    refine ⟨hkey, fun e he => ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact fun h => h.1.1.2 rfl
    · exact fun h => h.1.2 rfl
    · exact fun h => h.2 rfl
  -- translation invariance
  have htr : ∀ i : ℤ × ℤ, law q (halfArmEvent ![false, true, false] ![i.1, i.2] 0 R) =
      law q (halfArmEvent ![false, true, false] 0 0 R) := fun i =>
    law_halfArmEvent_eq_law_halfArmEvent_zero hq _ _ _ _
  have hcard : (S.card : ℝ≥0∞) = (2 * s + 1) ^ 2 := by
    rw [hSdef, Finset.card_product, Int.card_Icc,
      show ((s : ℤ) + 1 - -(s : ℤ)).toNat = 2 * s + 1 by omega]
    push_cast
    ring
  have hsum' : (2 * s + 1 : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R) ≤
      64 * β⁻¹ := by
    calc (2 * s + 1 : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R)
        = ∑ i ∈ S, law q (halfArmEvent ![false, true, false] ![i.1, i.2] 0 R) := by
          simp only [htr, Finset.sum_const, nsmul_eq_mul]
          rw [hcard]
      _ ≤ ∑ i ∈ S, 32 * law q (F i) := Finset.sum_le_sum hptS
      _ = 32 * ∑ i ∈ S, law q (F i) := by rw [Finset.mul_sum]
      _ ≤ 32 * (2 * β⁻¹) := mul_le_mul_right hsum _
      _ = 64 * β⁻¹ := by ring
  have hR : (R : ℝ≥0∞) ^ 2 ≤ 16 * (2 * (s : ℝ≥0∞) + 1) ^ 2 := by
    have : (R : ℝ≥0∞) ≤ 4 * (2 * s + 1) := by
      exact_mod_cast (show R ≤ 4 * (2 * s + 1) by omega)
    calc (R : ℝ≥0∞) ^ 2 ≤ (4 * (2 * (s : ℝ≥0∞) + 1)) ^ 2 := by gcongr
      _ = 16 * (2 * (s : ℝ≥0∞) + 1) ^ 2 := by ring
  calc (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R)
      ≤ 16 * (2 * s + 1) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R) :=
        mul_le_mul' hR le_rfl
    _ = 16 * ((2 * s + 1) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R)) := by ring
    _ ≤ 16 * (64 * β⁻¹) := mul_le_mul_right hsum' _
    _ = 1024 * β⁻¹ := by ring
    _ ≤ 1024 * β⁻¹ + 16 := le_self_add

/-! ### The lower bound: the lowest point of a cluster, extended by one edge -/

/-- **Opening an edge of probability one half** at most doubles the probability. -/
theorem law_setOf_insert_mem_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {e : Sym2 (LatticeSite 2)} (he : (q e : ℝ) = 1 / 2) (F : Set (Config (LatticeSite 2))) :
    law q {ω | insert e ω ∈ F} ≤ 2 * law q F := by
  have h := PercLib.Probability.prodBernoulli_setOf_insert_mem_le q e F
  have hσ : (unitInterval.toNNReal (q e) : ℝ≥0∞) = 2⁻¹ := by
    have hof : ∀ t : unitInterval, (unitInterval.toNNReal t : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) :=
      fun t => by rw [ENNReal.ofReal, Real.toNNReal_of_nonneg t.2.1]; rfl
    rw [hof, he, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [hσ] at h
  calc law q {ω | insert e ω ∈ F} = 2 * (2⁻¹ * law q {ω | insert e ω ∈ F}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * law q F := by gcongr; exact h

/-- **Opening one edge and closing three**, all of probability one half, multiplies a probability
by at most `16`. -/
theorem law_setOf_insert_sdiff_three_mem_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {e e₁ e₂ e₃ : Sym2 (LatticeSite 2)} (he : (q e : ℝ) = 1 / 2) (h₁ : (q e₁ : ℝ) = 1 / 2)
    (h₂ : (q e₂ : ℝ) = 1 / 2) (h₃ : (q e₃ : ℝ) = 1 / 2) (F : Set (Config (LatticeSite 2))) :
    law q {ω | insert e (((ω \ {e₁}) \ {e₂}) \ {e₃}) ∈ F} ≤ 16 * law q F := by
  calc law q {ω | insert e (((ω \ {e₁}) \ {e₂}) \ {e₃}) ∈ F}
      ≤ 2 * law q {η | insert e ((η \ {e₂}) \ {e₃}) ∈ F} :=
        law_setOf_diff_singleton_mem_le h₁ {η | insert e ((η \ {e₂}) \ {e₃}) ∈ F}
    _ ≤ 2 * (2 * law q {η | insert e (η \ {e₃}) ∈ F}) :=
        mul_le_mul_right (law_setOf_diff_singleton_mem_le h₂ {η | insert e (η \ {e₃}) ∈ F}) _
    _ ≤ 2 * (2 * (2 * law q {η | insert e η ∈ F})) :=
        mul_le_mul_right (mul_le_mul_right (law_setOf_diff_singleton_mem_le h₃
          {η | insert e η ∈ F}) _) _
    _ ≤ 2 * (2 * (2 * (2 * law q F))) :=
        mul_le_mul_right (mul_le_mul_right (mul_le_mul_right (law_setOf_insert_mem_le he F) _) _) _
    _ = 16 * law q F := by ring

/-- **A crossing inside a walk.** A walk inside `Icc lo' hi'` along open edges, from a point whose
`i`-th coordinate is at most `lo i` to a point whose `i`-th coordinate is at least `hi i`, crosses
the box `Icc lo hi` in direction `i`, when `Icc lo hi` has the other coordinates of `Icc lo' hi'`
and lies inside it. -/
theorem mem_crossing_of_walk_of_le {d : ℕ} {ω : Config (LatticeSite d)} {i : Fin d}
    {lo hi lo' hi' a b : LatticeSite d} (hother : ∀ j, j ≠ i → lo' j = lo j ∧ hi' j = hi j)
    (hle : lo i ≤ hi i) (p : (zdGraph d).Walk a b) (hp : ∀ v ∈ p.support, v ∈ Icc lo' hi')
    (hpe : ∀ e ∈ p.edges, e ∈ ω) (ha : a i ≤ lo i) (hb : hi i ≤ b i) : ω ∈ crossing i lo hi := by
  classical
  -- the last visit to the half-space below `lo i`
  obtain ⟨c, hc, q₁, s, hqs, hs⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
    (S := {v : LatticeSite d | v i ≤ lo i}) p ⟨a, p.start_mem_support, ha⟩
  have hsp : ∀ v ∈ s.support, v ∈ p.support := fun v hv => by
    rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inr hv
  have hse : ∀ e ∈ s.edges, e ∈ p.edges := fun e he => by
    rw [← hqs, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ he
  rw [mem_ofPred_eq] at hc
  have hc' : lo i ≤ c i := by
    by_cases hsn : s.Nil
    · have := hsn.eq
      rw [this]
      omega
    · have h₁ := hs _ (s.snd_mem_tail_support hsn)
      rw [mem_ofPred_eq] at h₁
      have h₂ := apply_le_apply_add_one_of_adj (s.adj_snd hsn) i
      omega
  have hlow : ∀ v ∈ s.support, lo i ≤ v i := fun v hv => by
    rcases (SimpleGraph.Walk.mem_support_iff s).1 hv with rfl | hv
    · exact hc'
    · have := hs v hv
      rw [mem_ofPred_eq] at this
      omega
  -- the first visit of the rest to the half-space above `hi i`
  obtain ⟨d', hd', t, hts, hte, htd⟩ := SimpleGraph.Walk.exists_walk_first_mem
    (fun v : LatticeSite d => hi i ≤ v i) s ⟨b, s.end_mem_support, hb⟩
  have hup : ∀ v ∈ t.support, v i ≤ hi i := fun v hv => by
    by_cases hvd : v = d'
    · subst hvd
      by_cases htn : t.Nil
      · have := htn.eq
        rw [← this]
        omega
      · have hpen : t.penultimate ∈ t.support.dropLast := by
          rw [← SimpleGraph.Walk.support_dropLast htn]; exact SimpleGraph.Walk.end_mem_support _
        have hne : t.penultimate ≠ v := (t.adj_penultimate htn).ne
        have h₁ : ¬ hi i ≤ t.penultimate i := fun h => hne (htd _ (List.mem_of_mem_dropLast hpen) h)
        have h₂ := apply_le_apply_add_one_of_adj (t.adj_penultimate htn) i
        omega
    · by_contra h
      exact hvd (htd v hv (by omega))
  have hin : ∀ v ∈ t.support, v ∈ Icc lo hi := fun v hv => by
    have h₁ := hp v (hsp v (hts v hv))
    have h₂ := hlow v (hts v hv)
    have h₃ := hup v hv
    rw [mem_Icc, Pi.le_def, Pi.le_def] at h₁ ⊢
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = i
      · subst hj; exact h₂
      · rw [← (hother j hj).1]; exact h₁.1 j
    · by_cases hj : j = i
      · subst hj; exact h₃
      · rw [← (hother j hj).2]; exact h₁.2 j
  refine ⟨c, hin c t.start_mem_support, le_antisymm hc hc', d', hin d' t.end_mem_support,
    le_antisymm (hup d' t.end_mem_support) hd', mem_localConn_of_walk t hin fun e he => ?_⟩
  exact hpe e (hse e (hte e he))

/-- **A set closed under the steps of a walk** contains its support when it contains its start. -/
theorem _root_.SimpleGraph.Walk.mem_of_mem_support_of_forall_darts {V : Type*}
    {G : SimpleGraph V} {A : Set V} :
    ∀ {u v : V} (p : G.Walk u v), u ∈ A → (∀ d ∈ p.darts, d.fst ∈ A → d.snd ∈ A) →
      ∀ w ∈ p.support, w ∈ A
  | _, _, .nil, hu, _, w, hw => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    exact hw ▸ hu
  | _, _, .cons h p, hu, hstep, w, hw => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · have hv := hstep ⟨(_, _), h⟩ (by simp) hu
      exact SimpleGraph.Walk.mem_of_mem_support_of_forall_darts p hv
        (fun d hd => hstep d (by simp [hd])) w hw

/-- **The lowest row of a cluster** (the lower bound, first step). Let the strip
`[-R, R] × [R + 2, 4R]` be crossed from bottom to top by open edges, and let no open path cross
`[-4R, 4R] × [0, R + 1]` from bottom to top, nor `[-3R - 1, -2R] × [0, 4R]` or
`[2R, 3R + 1] × [0, 4R]` from left to right. In the box `[-4R, 4R] × [0, 4R]`, the cluster of the
top end `w` of the crossing has its lowest row `m` in `[1, R + 2]`, and a point of that row lies
in `[-3R, 3R]`. -/
theorem exists_lowest_of_mem_crossing {η : Config (LatticeSite 2)} {R : ℕ} (hR : 1 ≤ R)
    (hO : η ∈ crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R])
    (hB : η ∉ crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])
    (hL : η ∉ crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])
    (hR' : η ∉ crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R]) :
    ∃ (w : LatticeSite 2) (k m : ℤ), w 1 = 4 * R ∧ -(3 * (R : ℤ)) ≤ k ∧ k ≤ 3 * R ∧ 1 ≤ m ∧
      m ≤ R + 2 ∧ η ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), 4 * R]) ![k, m] w ∧
      ∀ v : LatticeSite 2, η ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), 4 * R]) v w → m ≤ v 1 := by
  classical
  set B : Set (LatticeSite 2) := Icc ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), 4 * R] with hBdef
  have hmemB : ∀ v : LatticeSite 2, v ∈ B ↔
      -(4 * (R : ℤ)) ≤ v 0 ∧ v 0 ≤ 4 * R ∧ 0 ≤ v 1 ∧ v 1 ≤ 4 * R := fun v => by
    rw [hBdef, mem_Icc_two_iff]; simp
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  -- the crossing, inside the box
  obtain ⟨u, huI, hu1, w, hwI, hw1, huw⟩ := (mem_crossing_iff 1 _ _ η).1 hO
  rw [mem_Icc_two_iff] at huI hwI
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huI hwI hu1 hw1
  have huwB : η ∩ (zdGraph 2).edgeSet ∈ localConn B u w :=
    localConn_mono_set (fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      rw [hmemB]; omega) _ _ huw
  -- the rows of the cluster of `w`
  obtain ⟨Rows, hRows⟩ : ∃ Rows : Finset ℤ, ∀ l, l ∈ Rows ↔ l ∈ Finset.Icc (0 : ℤ) (4 * R) ∧
      ∃ k ∈ Finset.Icc (-(4 * (R : ℤ))) (4 * R),
        η ∩ (zdGraph 2).edgeSet ∈ localConn B ![k, l] w := ⟨_, fun l => Finset.mem_filter⟩
  have huR : u 1 ∈ Rows := by
    rw [hRows, Finset.mem_Icc]
    refine ⟨by omega, u 0, Finset.mem_Icc.2 (by omega), ?_⟩
    rwa [show (![u 0, u 1] : LatticeSite 2) = u from hpt _ _ (by simp) (by simp)]
  set m := Rows.min' ⟨_, huR⟩ with hm
  have hmR := Rows.min'_mem ⟨_, huR⟩
  rw [← hm, hRows, Finset.mem_Icc] at hmR
  obtain ⟨⟨hm0, hm4⟩, k, hk, hkw⟩ := hmR
  rw [Finset.mem_Icc] at hk
  have hmin : ∀ v : LatticeSite 2, η ∩ (zdGraph 2).edgeSet ∈ localConn B v w → m ≤ v 1 := by
    intro v hv
    have hvB := (hmemB v).1 hv.1
    refine Rows.min'_le _ ?_
    rw [hRows, Finset.mem_Icc]
    refine ⟨⟨hvB.2.2.1, hvB.2.2.2⟩, v 0, Finset.mem_Icc.2 ⟨hvB.1, hvB.2.1⟩, ?_⟩
    rwa [show (![v 0, v 1] : LatticeSite 2) = v from hpt _ _ (by simp) (by simp)]
  have hmu : m ≤ u 1 := Rows.min'_le _ huR
  obtain ⟨P, hPs, hPe⟩ := exists_walk_of_mem_localConn hkw
  refine ⟨w, k, m, hw1, ?_, ?_, ?_, by omega, hkw, hmin⟩
  · by_contra hc
    exact hL (mem_crossing_of_walk_of_le (lo' := ![-(4 * (R : ℤ)), 0])
      (hi' := ![4 * (R : ℤ), 4 * R])
      (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | exact ⟨rfl, rfl⟩)
      (by simp only [Matrix.cons_val_zero]; omega) P hPs hPe
      (by simp only [Matrix.cons_val_zero]; omega) (by simp only [Matrix.cons_val_zero]; omega))
  · by_contra hc
    exact hR' (mem_crossing_of_walk_of_le (lo' := ![-(4 * (R : ℤ)), 0])
      (hi' := ![4 * (R : ℤ), 4 * R])
      (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | exact ⟨rfl, rfl⟩)
      (by simp only [Matrix.cons_val_zero]; omega) P.reverse
      (fun v hv => hPs v (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv))
      (fun e he => hPe e (by rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he))
      (by simp only [Matrix.cons_val_zero]; omega) (by simp only [Matrix.cons_val_zero]; omega))
  · by_contra hc
    exact hB (mem_crossing_of_walk_of_le (lo' := ![-(4 * (R : ℤ)), 0])
      (hi' := ![4 * (R : ℤ), 4 * R])
      (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | exact ⟨rfl, rfl⟩)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega) P hPs hPe
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega))

/-- **A walk of faces up to its first exit from a box of faces.** A walk from a face of
`Icc lo (hi - 1)` to a face outside it contains a walk from the same face to its first face
outside, through faces of `Icc (lo - 1) hi`, each step with a face in `Icc lo (hi - 1)`. -/
theorem exists_walk_of_notMem_Icc {lo hi f g : LatticeSite 2} (δ : (zdGraph 2).Walk f g)
    (hf : f ∈ Icc lo (hi - 1)) (hg : g ∉ Icc lo (hi - 1)) :
    ∃ (g' : LatticeSite 2) (δ' : (zdGraph 2).Walk f g'), g' ∉ Icc lo (hi - 1) ∧
      (∀ h ∈ δ'.support.dropLast, h ∈ Icc lo (hi - 1)) ∧
      (∀ h ∈ δ'.support, h ∈ Icc (lo - 1) hi ∧ h ∈ δ.support) ∧
      ∀ E ∈ δ'.edges, E ∈ δ.edges ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1) := by
  obtain ⟨c, q, s, hqs, hc, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem δ hg
  have hqn : ¬q.Nil := fun hn => hc (by rw [← hn.eq]; exact hf)
  have hpen : q.penultimate ∈ q.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hqn]; exact SimpleGraph.Walk.end_mem_support _
  refine ⟨c, q, hc, hq, fun h hh => ⟨?_, ?_⟩, fun E hE => ⟨?_, ?_⟩⟩
  · rw [← SimpleGraph.Walk.dropLast_support_concat q, List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · have := hq h hh
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
      omega
    · have h₁ := hq _ hpen
      have hadj := q.adj_penultimate hqn
      rw [mem_Icc_two_iff] at h₁ ⊢
      rw [zdGraph_two_adj_iff] at hadj
      simp only [Pi.sub_apply, Pi.one_apply] at h₁ ⊢
      omega
  · rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hh
  · rw [← hqs, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ hE
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hE
    refine ⟨d.fst, Sym2.mem_mk_left _ _, hq _ ?_⟩
    rw [← SimpleGraph.Walk.map_fst_darts]
    exact List.mem_map_of_mem hd

/-- **The arms of the lowest point of a cluster, extended by one edge** (the lower bound,
deterministic part). Let `x₁` be a point of the lowest row of the cluster of `w` in the box
`Icc lo' hi`, and `x'` the point below it, on the bottom row of the box `Icc lo hi` (the part of
the larger box at or above that row, with `w` on its top side). In a configuration `η'` that agrees
with `η` away from `x'`, with the edge from `x'` up to `x₁` open and the other edges at `x'`
closed, `x'` is the only point of the bottom row in its cluster, which reaches `w`; by quad
duality, dual walks start from the faces above the edges on the left and on the right of `x'`
and leave the faces of the box above the bottom row; and these walks share no face (interlacing
with the open path from `x'` to `w`). -/
theorem exists_dualWalks_of_forall_lt {η η' : Config (LatticeSite 2)}
    {lo' w x₁ x' xl xr xd : LatticeSite 2} (hlo0 : lo' 0 = lo 0) (hlo1 : lo' 1 ≤ lo 1)
    (h₁ : lo 1 < hi 1) (hw : w ∈ Icc lo hi) (hw1 : w 1 = hi 1)
    (hx' : x' 1 = lo 1 ∧ lo 0 < x' 0 ∧ x' 0 + 1 < hi 0) (hx₁ : x₁ 0 = x' 0 ∧ x₁ 1 = x' 1 + 1)
    (hxl : xl 0 + 1 = x' 0 ∧ xl 1 = x' 1) (hxr : xr 0 = x' 0 + 1 ∧ xr 1 = x' 1)
    (hxd : xd 0 = x' 0 ∧ xd 1 + 1 = x' 1)
    (hx₁w : η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo' hi) x₁ w)
    (hmin : ∀ v, η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo' hi) v w → x' 1 < v 1)
    (he₁ : s(x', x₁) ∈ η') (hel : s(xl, x') ∉ η') (her : s(x', xr) ∉ η') (hed : s(xd, x') ∉ η')
    (hagree : ∀ e ∈ (zdGraph 2).edgeSet, x' ∉ e → (e ∈ η' ↔ e ∈ η)) :
    η' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x' w ∧
      ∃ (gl : LatticeSite 2) (δl : (zdGraph 2).Walk xl gl) (gr : LatticeSite 2)
        (δr : (zdGraph 2).Walk x' gr),
        (gl ∉ Icc lo (hi - 1) ∧ (∀ h ∈ δl.support.dropLast, h ∈ Icc lo (hi - 1)) ∧
          (∀ h ∈ δl.support, h ∈ Icc (lo - 1) hi ∧ lo 1 ≤ h 1) ∧
          ∀ E ∈ δl.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1)) ∧
        (gr ∉ Icc lo (hi - 1) ∧ (∀ h ∈ δr.support.dropLast, h ∈ Icc lo (hi - 1)) ∧
          (∀ h ∈ δr.support, h ∈ Icc (lo - 1) hi ∧ lo 1 ≤ h 1) ∧
          ∀ E ∈ δr.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1)) ∧
        ∀ h ∈ δl.support, h ∉ δr.support := by
  classical
  have h₀ : lo 0 < hi 0 := by omega
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  have hwI := hw
  rw [mem_Icc_two_iff] at hwI
  have hsubB : Icc lo hi ⊆ Icc lo' hi := fun v hv => by
    rw [mem_Icc_two_iff] at hv ⊢; omega
  have hx'U : x' ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxlU : xl ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxrU : xr ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  -- the cluster of `x'` inside `Icc lo hi` is `x'` and part of the cluster of `w`
  have hcl : ∀ z, η' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x' z →
      z = x' ∨ η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo' hi) z w := by
    intro z hz
    obtain ⟨P, hPs, hPe⟩ := exists_walk_of_mem_localConn hz
    refine P.mem_of_mem_support_of_forall_darts
      (A := {v | v = x' ∨ η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo' hi) v w}) (Or.inl rfl)
      (fun d hd hfst => ?_) z P.end_mem_support
    have hdU := hPs _ (P.dart_snd_mem_support_of_mem_darts hd)
    have hde : s(d.fst, d.snd) ∈ η' := hPe _ (List.mem_map_of_mem hd)
    rcases hfst with hf | hf
    · have hadj := d.adj
      rw [hf, zdGraph_two_adj_iff] at hadj
      rw [mem_Icc_two_iff] at hdU
      rcases hadj with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
      · right
        rw [hpt d.snd x₁ (by omega) (by omega)]
        exact hx₁w
      · omega
      · exfalso
        rw [hf, hpt d.snd xr (by omega) (by omega)] at hde
        exact her hde
      · exfalso
        rw [hf, hpt d.snd xl (by omega) (by omega), Sym2.eq_swap] at hde
        exact hel hde
    · by_cases hsx : d.snd = x'
      · exact Or.inl hsx
      · right
        have hfx : d.fst ≠ x' := fun h => by
          have := hmin _ hf
          rw [h] at this
          omega
        have hx'e : x' ∉ s(d.fst, d.snd) := by
          rw [Sym2.mem_iff]
          rintro (h | h)
          · exact hfx h.symm
          · exact hsx h.symm
        have heη : s(d.fst, d.snd) ∈ η := (hagree _ d.adj hx'e).1 hde
        rw [localConn_comm] at hf ⊢
        exact mem_localConn_of_mem_localConn_of_mem hf (hsubB hdU) ⟨heη, d.adj⟩
  have hrow : ∀ a : LatticeSite 2, a 1 = lo 1 →
      η' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x' a → a = x' := fun a ha h => by
    rcases hcl a h with h' | h'
    · exact h'
    · have := hmin a h'
      omega
  -- the open path from `x'` to `w`
  have hx'w : η' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x' w := by
    obtain ⟨P, hPs, hPe⟩ := exists_walk_of_mem_localConn hx₁w
    have hK : ∀ v ∈ P.support, x' 1 < v 1 := fun v hv => hmin v (localConn_trans (by
      rw [localConn_comm]; exact mem_localConn_of_mem_support P hPs hPe hv) hx₁w)
    have hadj : (zdGraph 2).Adj x' x₁ := by rw [zdGraph_two_adj_iff]; omega
    refine mem_localConn_of_walk (SimpleGraph.Walk.cons hadj P) (fun v hv => ?_) (fun e he => ?_)
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hx'U
      · have h₁' := hPs v hv
        have h₂' := hK v hv
        rw [mem_Icc_two_iff] at h₁' ⊢
        omega
    · rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact he₁
      · refine (hagree e (P.edges_subset_edgeSet he) fun hx => ?_).2 (hPe e he)
        have := hK _ (mem_support_of_mem_edge P he hx)
        omega
  -- no open path joins two points of the bottom row on either side of `x'`
  have hwB : w ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hx'B : x' ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hsep : ∀ a b : LatticeSite 2, a 1 = lo 1 → b 1 = lo 1 → a 0 ≤ x' 0 → x' 0 ≤ b 0 →
      η' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a b → a = x' ∧ b = x' := by
    intro a b ha1 hb1 ha0 hb0 hab
    have haU := hab.1
    have hbU := hab.2.1
    rw [mem_Icc_two_iff] at haU hbU
    rcases eq_or_lt_of_le ha0 with ha0 | ha0
    · have hax : a = x' := hpt _ _ ha0 (by omega)
      rw [hax] at hab
      exact ⟨hax, hrow b hb1 hab⟩
    rcases eq_or_lt_of_le hb0 with hb0 | hb0
    · have hbx : b = x' := hpt _ _ hb0.symm (by omega)
      rw [hbx, localConn_comm] at hab
      have := hrow a ha1 hab
      rw [this] at ha0
      omega
    · exfalso
      obtain ⟨pab, hpabs, hpabe⟩ := exists_walk_of_mem_localConn hab
      obtain ⟨pw, hpws, hpwe⟩ := exists_walk_of_mem_localConn hx'w
      have haB : a ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
      have hbB : b ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
      have hpw := perimeterPos_lt_perimeterPos_of_bottom hb1 (by omega) hwB (by omega)
      obtain ⟨z, hz₁, hz₂⟩ := exists_mem_support_of_interlaced pab pw hpabs hpws haB hbB hx'B hwB
        (Or.inl ⟨by rw [perimeterPos_of_bottom ha1, perimeterPos_of_bottom hx'.1]; omega,
          by rw [perimeterPos_of_bottom hx'.1, perimeterPos_of_bottom hb1]; omega, Or.inr hpw⟩)
      have h₁' := mem_localConn_of_mem_support pab hpabs hpabe hz₁
      have h₂' := mem_localConn_of_mem_support pw hpws hpwe hz₂
      rw [localConn_comm] at h₁'
      have := hrow a ha1 (localConn_trans h₂' h₁')
      rw [this] at ha0
      omega
  -- the dual walks, by quad duality
  obtain ⟨gl₀, δl₀, hgl₀, hδl₀1, hδl₀E⟩ := exists_dualWalk_of_forall_notMem_localConn (x := x')
    (fL := xl) h₁ hx'.1 hx'.2.1 (by omega) hxl (fun a b ha hb ha0 hb0 hab => by
      have := (hsep a b ha hb ha0.le hb0 hab).1
      rw [this] at ha0
      omega)
  obtain ⟨gr₀, δr₀, hgr₀, hδr₀1, hδr₀E⟩ := exists_dualWalk_of_forall_notMem_localConn (x := xr)
    (fL := x') h₁ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
    (fun a b ha hb ha0 hb0 hab => by
      have := (hsep a b ha hb (by omega) (by omega) hab).2
      rw [this] at hb0
      omega)
  have hxlF : xl ∈ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  have hx'F : x' ∈ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  obtain ⟨gl, δl, hgl, hδld, hδls, hδle⟩ := exists_walk_of_notMem_Icc δl₀ hxlF hgl₀
  obtain ⟨gr, δr, hgr, hδrd, hδrs, hδre⟩ := exists_walk_of_notMem_Icc δr₀ hx'F hgr₀
  have hδlE : ∀ E ∈ δl.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1) :=
    fun E hE => ⟨hδl₀E E (hδle E hE).1, (hδle E hE).2⟩
  have hδrE : ∀ E ∈ δr.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1) :=
    fun E hE => ⟨hδr₀E E (hδre E hE).1, (hδre E hE).2⟩
  refine ⟨hx'w, gl, δl, gr, δr, ⟨hgl, hδld, fun h hh => ⟨(hδls h hh).1, hδl₀1 h (hδls h hh).2⟩,
    hδlE⟩, ⟨hgr, hδrd, fun h hh => ⟨(hδrs h hh).1, hδr₀1 h (hδrs h hh).2⟩, hδrE⟩, ?_⟩
  -- the two dual walks share no face
  intro h hl hr
  have hcut : ∀ {f g' : LatticeSite 2} (δ : (zdGraph 2).Walk f g'),
      (∀ h ∈ δ.support, h ∈ Icc (lo - 1) hi ∧ h ∈ δ.support) →
      (∀ E ∈ δ.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1)) → ∀ h ∈ δ.support,
      dualConfig η' ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f h :=
    fun δ hs hE h hh => dualConfig_inter_image_mem_localConn_of_walk (δ.takeUntil h hh)
      (fun v hv => (hs v (δ.support_takeUntil_subset_support hh hv)).1)
      (fun E hE' => hE E (δ.edges_takeUntil_subset_edges hh hE'))
  have hL := hcut δl (fun h hh => ⟨(hδls h hh).1, hh⟩) hδlE h hl
  have hR := hcut δr (fun h hh => ⟨(hδrs h hh).1, hh⟩) hδrE h hr
  obtain ⟨f₀, hf₀0, hf₀1⟩ : ∃ f : LatticeSite 2, f 0 + 1 = x' 0 ∧ f 1 + 1 = x' 1 :=
    ⟨![x' 0 - 1, x' 1 - 1], by simp, by simp⟩
  obtain ⟨f₀', hf₀'0, hf₀'1⟩ : ∃ f : LatticeSite 2, f 0 = x' 0 ∧ f 1 + 1 = x' 1 :=
    ⟨![x' 0, x' 1 - 1], by simp, by simp⟩
  have hadjl : (zdGraph 2).Adj xl x' := by rw [zdGraph_two_adj_iff]; omega
  have hadjr : (zdGraph 2).Adj x' xr := by rw [zdGraph_two_adj_iff]; omega
  have hd₁ : f₀ ∈ dualEdge s(xl, x') ∧ xl ∈ dualEdge s(xl, x') := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hd₃ : f₀' ∈ dualEdge s(x', xr) ∧ x' ∈ dualEdge s(x', xr) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hl' := mem_localConn_of_adj_of_notMem hadjl hxlU hx'U hel hd₁.1 hd₁.2
  have hr' := mem_localConn_of_adj_of_notMem hadjr hx'U hxrU her hd₃.1 hd₃.2
  have hchain := localConn_trans hr' (localConn_trans hR
    (by rw [localConn_comm]; exact localConn_trans hl' hL))
  have hxlB : xl ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hxrB : xr ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hpw := perimeterPos_lt_perimeterPos_of_bottom (hxr.2.trans hx'.1) (by omega) hwB (by omega)
  exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hx'w hx'B hwB (f := f₀')
    (by rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega) hxrB
    (by rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega) (g := f₀)
    (by rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega) hxlB
    (by rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega)
    (Or.inl ⟨by
        rw [perimeterPos_of_bottom hx'.1, perimeterPos_of_bottom (hxr.2.trans hx'.1)]; omega,
      hpw, Or.inl (by rw [perimeterPos_of_bottom (hxl.2.trans hx'.1),
        perimeterPos_of_bottom hx'.1]; omega)⟩) hchain

/-- **A dual arm inside a dual walk.** A dual-open walk from a face at `x` to a face outside the
faces of `B_R(x)` contains a dual arm of `B_R(x)` from `x`, which ends with the last step of the
walk's first part up to its first exit; that part starts at the same face. -/
theorem exists_isDualArm_of_walk {x f g : LatticeSite 2} {R : ℕ} (hR : 1 ≤ R)
    (δ : (zdGraph 2).Walk f g) (hf : f ∈ Icc (x - 1) x)
    (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδE : ∀ E ∈ δ.edges, E ∈ dualConfig ω) :
    ∃ (g₁ : LatticeSite 2) (δ₁ : (zdGraph 2).Walk f g₁) (c : LatticeSite 2)
      (β : (zdGraph 2).Walk c g₁), IsDualArm ω x 0 (x - R) (x + R) β ∧
      (∀ h ∈ β.support, h ∈ δ.support) ∧ β.penultimate = δ₁.penultimate ∧ ¬δ₁.Nil ∧
      (∀ h ∈ δ₁.support.dropLast, h ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1)) ∧
      g₁ ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1) ∧ (∀ h ∈ δ₁.support, h ∈ δ.support) ∧
      ∀ E ∈ δ₁.edges, E ∈ δ.edges := by
  classical
  have hfT : f ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1) := by
    rw [mem_Icc_two_iff] at hf ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hf ⊢
    omega
  obtain ⟨g₁, δ₁, s₁, hδs₁, hg₁, hδ₁⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem δ.bypass hg
  have hδ₁p : δ₁.IsPath := by
    have := δ.bypass_isPath
    rw [← hδs₁] at this
    exact this.of_append_left
  have hδ₁n : ¬δ₁.Nil := fun hn => hg₁ (by rw [← hn.eq]; exact hfT)
  have hδ₁s : ∀ h ∈ δ₁.support, h ∈ δ.support := fun h hh => by
    refine δ.support_bypass_subset_support ?_
    rw [← hδs₁, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hh
  have hδ₁e : ∀ E ∈ δ₁.edges, E ∈ δ.edges := fun E hE => by
    refine δ.edges_bypass_subset_edges ?_
    rw [← hδs₁, SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ hE
  have hδ₁c : δ₁.IsCrossing {f} (Icc (x - (R : LatticeSite 2)) (x + R - 1)) := by
    refine ⟨rfl, fun v hv hvf => ?_, hg₁, hδ₁⟩
    have hnd := hδ₁p.support_nodup
    rw [← SimpleGraph.Walk.cons_support_tail hδ₁n, List.nodup_cons] at hnd
    rw [← SimpleGraph.Walk.support_tail_of_not_nil δ₁ hδ₁n] at hv
    rw [mem_singleton_iff] at hvf
    exact hnd.1 (hvf ▸ hv)
  obtain ⟨c', q', β, hqβ, hβc⟩ := hδ₁c.exists_append_eq_isCrossing_of_subset
    (S' := Icc (x - ((0 : ℕ) : LatticeSite 2) - 1) (x + ((0 : ℕ) : LatticeSite 2))) (by
      intro v hv
      rw [mem_singleton_iff] at hv
      subst hv
      simpa using hf)
  have hβs : ∀ h ∈ β.support, h ∈ δ₁.support := fun h hh => by
    rw [← hqβ, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inr hh
  have hβ : IsDualArm ω x 0 (x - R) (x + R) β := ⟨hβc, fun E hE => hδE E (hδ₁e E (by
    rw [← hqβ, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ hE))⟩
  have hβn : ¬β.Nil := hβc.not_nil (by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Nat.cast_zero, sub_zero, add_zero, Pi.sub_apply, Pi.add_apply, Pi.one_apply,
      Pi.natCast_apply, Pi.zero_apply] at hv ⊢
    omega)
  refine ⟨g₁, δ₁, c', β, hβ, fun h hh => hδ₁s h (hβs h hh), ?_, hδ₁n, hδ₁, hg₁, hδ₁s, hδ₁e⟩
  rw [← hqβ, SimpleGraph.Walk.penultimate_append_of_not_nil _ hβn]

/-- **Three half-plane arms from the walks at an extended lowest point** (the lower bound,
assembly). Let `x'` be a point of the bottom row of the box `Icc lo hi`, joined inside the box to
a point `w` of its top side, with the edges on its left and on its right closed, and let dual
walks, sharing no face, go from the faces above these edges, at or above the bottom row, to
faces outside the faces of the box. If `B_R(x')`, `R ≥ 2`, fits in the box above the row, then
`x'` has three arms to distance `R` in the half-plane, dual, open, dual. -/
theorem mem_halfArmEvent_three_of_dualWalks {R : ℕ} (hR : 2 ≤ R)
    {x' xl xr w gl gr : LatticeSite 2} (hx'1 : x' 1 = lo 1)
    (hfit : lo 0 + R ≤ x' 0 ∧ x' 0 + R ≤ hi 0 ∧ x' 1 + R ≤ hi 1)
    (hxl : xl 0 + 1 = x' 0 ∧ xl 1 = x' 1) (hxr : xr 0 = x' 0 + 1 ∧ xr 1 = x' 1)
    (hw1 : w 1 = hi 1) (hx'w : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x' w)
    (hel : s(xl, x') ∉ ω) (her : s(x', xr) ∉ ω)
    (δl : (zdGraph 2).Walk xl gl) (hgl : gl ∉ Icc lo (hi - 1))
    (hδl1 : ∀ h ∈ δl.support, lo 1 ≤ h 1) (hδlE : ∀ E ∈ δl.edges, E ∈ dualConfig ω)
    (δr : (zdGraph 2).Walk x' gr) (hgr : gr ∉ Icc lo (hi - 1))
    (hδr1 : ∀ h ∈ δr.support, lo 1 ≤ h 1) (hδrE : ∀ E ∈ δr.edges, E ∈ dualConfig ω)
    (hdisj : ∀ h ∈ δl.support, h ∉ δr.support) :
    ω ∈ halfArmEvent ![false, true, false] x' 0 R := by
  classical
  have hR1 : 1 ≤ R := by omega
  -- the open arm
  obtain ⟨pw, hpws, hpwe⟩ := exists_walk_of_mem_localConn hx'w
  have hwT : w ∉ Icc (x' - (R : LatticeSite 2) + 1) (x' + R - 1) := by
    intro h
    rw [mem_Icc_two_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h
    omega
  obtain ⟨c, d, α, hαc, hαs, hαe⟩ := pw.exists_isCrossing_of_start_mem
    (S := Icc (x' - ((0 : ℕ) : LatticeSite 2)) (x' + ((0 : ℕ) : LatticeSite 2))) (by simp) hwT
  have hcx : c = x' := by
    have := hαc.start_mem
    simpa using this
  subst hcx
  have hα : IsOpenArm ω c 0 (c - R) (c + R) α := ⟨hαc, fun e he => hpwe e (hαe e he)⟩
  have hαH : ∀ v ∈ α.support, c 1 ≤ v 1 := fun v hv => by
    have := hpws v (hαs v hv)
    rw [mem_Icc_two_iff] at this
    omega
  have hB : Icc (c - ((0 : ℕ) : LatticeSite 2)) (c + ((0 : ℕ) : LatticeSite 2)) ⊆
      Icc (c - R + 1) (c + R - 1) := by
    intro v hv
    simp only [Nat.cast_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff] at hv
    subst hv
    rw [mem_Icc_two_iff]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hαn : ¬α.Nil := hα.not_nil hB
  have hαB : ∀ v ∈ α.support, v ∈ Icc (c - (R : LatticeSite 2)) (c + R) :=
    fun v hv => hα.mem_Icc hαn hv
  have hpB := hα.end_mem_boxBoundary hαn
  -- the dual arms
  have hout : ∀ g : LatticeSite 2, g ∉ Icc lo (hi - 1) → lo 1 ≤ g 1 →
      g ∉ Icc (c - (R : LatticeSite 2)) (c + R - 1) := fun g hg hg1 h => hg (by
    rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega)
  obtain ⟨gl₁, δl₁, cl, βl, hβl, hβls, hβlp, hδl₁n, hδl₁d, hgl₁, hδl₁s, hδl₁e⟩ :=
    exists_isDualArm_of_walk hR1 δl (by
      rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega)
      (hout gl hgl (hδl1 gl δl.end_mem_support)) hδlE
  obtain ⟨gr₁, δr₁, cr, βr, hβr, hβrs, hβrp, hδr₁n, hδr₁d, hgr₁, hδr₁s, hδr₁e⟩ :=
    exists_isDualArm_of_walk hR1 δr (by
      rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega)
      (hout gr hgr (hδr1 gr δr.end_mem_support)) hδrE
  -- the landing order
  have hlt₁ := lt_landingPos_of_dualWalk_right (x := c) (s := c) (sr := xr) (fR := c) rfl
    (by omega) (by omega) hxr ⟨rfl, rfl⟩ α (fun e he => hpwe e (hαe e he)) hαB hαH hpB her δr₁
    hδr₁n hδr₁d (fun h hh => by rw [← hx'1] at hδr1; exact hδr1 h (hδr₁s h hh)) hgr₁
    (fun E hE => hδrE E (hδr₁e E hE))
  have hlt₂ := landingPos_lt_of_dualWalk_left (x := c) (s := c) (sl := xl) (fL := xl) rfl
    (by omega) (by omega) hxl hxl α (fun e he => hpwe e (hαe e he)) hαB hαH hpB hel δl₁
    hδl₁n hδl₁d (fun h hh => by rw [← hx'1] at hδl1; exact hδl1 h (hδl₁s h hh)) hgl₁
    (fun E hE => hδlE E (hδl₁e E hE))
  -- the three arms form the half-plane event
  have hfam : ∀ i : Fin 3, ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (![false, true, false] i) c 0 (c - R) (c + R) γ ∧ (∀ v ∈ γ.support, c 1 ≤ v 1) ∧
      (∀ v ∈ γ.support, ![false, true, false] i = false →
        v ∈ ![δr.support, [], δl.support] i) ∧
      landingPos (c - R) (c + R) (![false, true, false] i) γ =
        ![landingPos (c - R) (c + R) false βr, landingPos (c - R) (c + R) true α,
          landingPos (c - R) (c + R) false βl] i := by
    intro i
    fin_cases i
    · refine ⟨_, _, βr, hβr, fun v hv => ?_, fun v hv _ => hβrs v hv, rfl⟩
      rw [← hx'1] at hδr1
      exact hδr1 v (hβrs v hv)
    · exact ⟨_, _, α, hα, hαH, fun v _ h => absurd h (by decide), rfl⟩
    · refine ⟨_, _, βl, hβl, fun v hv => ?_, fun v hv _ => hβls v hv, rfl⟩
      rw [← hx'1] at hδl1
      exact hδl1 v (hβls v hv)
  choose a b γ hγ hγH hγs hγL using hfam
  refine mem_halfArmEvent_iff.2 ⟨a, b, γ, hγ, ⟨fun i k hik hi hk => ?_, fun i k hik hi hk => ?_⟩,
    hγH, ?_⟩
  · revert hik hi hk
    fin_cases i <;> fin_cases k <;> simp
  · intro v hvi hvk
    have h₁ := hγs i v hvi hi
    have h₂ := hγs k v hvk hk
    fin_cases i <;> fin_cases k
    all_goals first
      | exact absurd rfl hik
      | exact absurd hi (by decide)
      | exact absurd hk (by decide)
      | exact hdisj v h₂ h₁
      | exact hdisj v h₁ h₂
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    · rw [hγL, hγL]
      change landingPos (c - R) (c + R) false βr < landingPos (c - R) (c + R) true α
      rw [landingPos_false, hβrp]
      exact hlt₁
    · rw [hγL, hγL]
      change landingPos (c - R) (c + R) true α < landingPos (c - R) (c + R) false βl
      rw [landingPos_false, hβlp]
      exact hlt₂

/-- **The arms at the extended lowest point of a cluster** (the lower bound, deterministic part,
for any configuration `η`). Under the crossing events of `exists_lowest_of_mem_crossing`, there is
a point `x'` in `[-3R, 3R] × [0, R + 1]`, the point below a point of the lowest row of the
cluster of the top end `w` of the crossing, such that in every configuration `η'` agreeing with `η`
away from `x'`, with the edge from `x'` upwards open and the other three edges at `x'` closed,
`x'` is joined to `w` above its row and dual walks from the two faces above `x'`, sharing no face,
leave the faces of the box `[-4R, 4R] × [x'₁, 4R]` above the row of `x'`. -/
theorem exists_dualWalks_of_mem_crossing {η : Config (LatticeSite 2)} {R : ℕ} (hR : 2 ≤ R)
    (hO : η ∈ crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R])
    (hB : η ∉ crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])
    (hL : η ∉ crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])
    (hR' : η ∉ crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R]) :
    ∃ (x' w lo hi : LatticeSite 2), -(3 * (R : ℤ)) ≤ x' 0 ∧ x' 0 ≤ 3 * R ∧ 0 ≤ x' 1 ∧
      x' 1 ≤ R + 1 ∧ lo 0 = -(4 * (R : ℤ)) ∧ lo 1 = x' 1 ∧ hi 0 = 4 * (R : ℤ) ∧
      hi 1 = 4 * (R : ℤ) ∧ w 1 = hi 1 ∧
      ∀ (η' : Config (LatticeSite 2)) (x₁ xl xr xd : LatticeSite 2), x₁ 0 = x' 0 →
        x₁ 1 = x' 1 + 1 → xl 0 + 1 = x' 0 → xl 1 = x' 1 → xr 0 = x' 0 + 1 → xr 1 = x' 1 →
        xd 0 = x' 0 → xd 1 + 1 = x' 1 → s(x', x₁) ∈ η' → s(xl, x') ∉ η' → s(x', xr) ∉ η' →
        s(xd, x') ∉ η' → (∀ e ∈ (zdGraph 2).edgeSet, x' ∉ e → (e ∈ η' ↔ e ∈ η)) →
        η' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x' w ∧
          ∃ (gl : LatticeSite 2) (δl : (zdGraph 2).Walk xl gl) (gr : LatticeSite 2)
            (δr : (zdGraph 2).Walk x' gr),
            (gl ∉ Icc lo (hi - 1) ∧ (∀ h ∈ δl.support.dropLast, h ∈ Icc lo (hi - 1)) ∧
              (∀ h ∈ δl.support, h ∈ Icc (lo - 1) hi ∧ lo 1 ≤ h 1) ∧
              ∀ E ∈ δl.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1)) ∧
            (gr ∉ Icc lo (hi - 1) ∧ (∀ h ∈ δr.support.dropLast, h ∈ Icc lo (hi - 1)) ∧
              (∀ h ∈ δr.support, h ∈ Icc (lo - 1) hi ∧ lo 1 ≤ h 1) ∧
              ∀ E ∈ δr.edges, E ∈ dualConfig η' ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1)) ∧
            ∀ h ∈ δl.support, h ∉ δr.support := by
  obtain ⟨w, k, m, hw1, hk₁, hk₂, hm₁, hm₂, hkw, hmin⟩ :=
    exists_lowest_of_mem_crossing (by omega) hO hB hL hR'
  have hwB := hkw.2.1
  rw [mem_Icc_two_iff] at hwB
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hwB
  refine ⟨![k, m - 1], w, ![-(4 * (R : ℤ)), m - 1], ![4 * (R : ℤ), 4 * R], by simpa using hk₁,
    by simpa using hk₂, by simp; omega, by simp; omega, rfl, rfl, rfl, rfl, by simpa using hw1,
    fun η' x₁ xl xr xd hx₁0 hx₁1 hxl0 hxl1 hxr0 hxr1 hxd0 hxd1 he₁ hel her hed hagree => ?_⟩
  have hx₁ : x₁ = ![k, m] := funext (Fin.forall_fin_two.2 ⟨by simpa using hx₁0, by
    simp at hx₁1 ⊢; omega⟩)
  subst hx₁
  exact exists_dualWalks_of_forall_lt (lo' := ![-(4 * (R : ℤ)), 0]) (x' := ![k, m - 1])
    (x₁ := ![k, m]) (xl := xl) (xr := xr) (xd := xd) rfl (by simp; omega)
    (by simp; omega) (by rw [mem_Icc_two_iff]; simp; omega) (by simpa using hw1)
    ⟨rfl, by simp; omega, by simp; omega⟩ ⟨rfl, by simp⟩ ⟨hxl0, hxl1⟩ ⟨hxr0, hxr1⟩ ⟨hxd0, hxd1⟩
    hkw (fun v hv => by have := hmin v hv; simp; omega) he₁ hel her hed hagree

/-- **The crossing events of the lower bound are likely.** There is `c₀ > 0` such that, at `1/2`,
with probability at least `c₀` the strip `[-R, R] × [R + 2, 4R]` is crossed from bottom to top
and none of `[-4R, 4R] × [0, R + 1]` (bottom to top), `[-3R - 1, -2R] × [0, 4R]` and
`[2R, 3R + 1] × [0, 4R]` (left to right) is crossed: the first event is independent of the
others (disjoint edges), which are decreasing (Harris), and each has probability bounded below by
the crossing bounds at `1/2`. -/
theorem exists_pos_le_law_crossing_inter_compl :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ c₀ ≠ ∞ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c₀ ≤ law q (crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R] ∩
          ((crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])ᶜ ∩
            (crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])ᶜ ∩
            (crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R])ᶜ)) := by
  obtain ⟨c, hc⟩ := exists_crossingBounds_half
  set q₀ : Sym2 (LatticeSite 2) → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
  have hq₀ : ∀ e ∈ (zdGraph 2).edgeSet, (q₀ e : ℝ) = 1 / 2 := fun _ _ => rfl
  have hpos : ∀ k, c k ≠ 0 := fun k => ((hc q₀ hq₀).pos k).ne'
  have hfin : ∀ k, c k ≠ ∞ := fun k =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (((hc q₀ hq₀).le_law_crossing k 0 0 1 le_rfl
      le_top).trans prob_le_one)
  refine ⟨c 3 * (c 9 * c 6 * c 6), ENNReal.mul_pos (hpos 3)
    (ENNReal.mul_pos (ENNReal.mul_pos (hpos 9) (hpos 6)).ne' (hpos 6)).ne', ?_,
    fun q hq R hR => ?_⟩
  · exact ENNReal.mul_ne_top (hfin 3) (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hfin 9) (hfin 6))
      (hfin 6))
  have hCB := hc q hq
  have hle : ∀ a b a' b' : ℤ, a ≤ a' → b ≤ b' → (![a, b] : LatticeSite 2) ≤ ![a', b'] :=
    fun a b a' b' h h' => by rw [Pi.le_def, Fin.forall_fin_two]; exact ⟨h, h'⟩
  set O := crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R] with hOdef
  set DB := (crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])ᶜ with hDBdef
  set DL := (crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])ᶜ with hDLdef
  set DR := (crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R])ᶜ with hDRdef
  have hO : c 3 ≤ law q O := hCB.le_law_crossing_one_of_le 3 (m := R) hR le_top
    (by simp; omega) (by simp; omega)
    (by simp)
  have hDB : c 9 ≤ law q DB := by
    rw [hDBdef, compl_crossing_one_eq_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega))]
    exact hCB.le_law_dualConfig_crossing_zero_of_le 9 (m := R) hR le_top
      (by simp; omega)
      (by simp; omega)
      (by simp)
  have hDL : c 6 ≤ law q DL := by
    rw [hDLdef, crossing_zero_eq_compl_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega)),
      compl_compl]
    exact hCB.le_law_dualConfig_crossing_one_of_le 6 (m := R) hR le_top
      (by simp; omega)
      (by simp; omega)
      (by simp; omega)
  have hDR : c 6 ≤ law q DR := by
    rw [hDRdef, crossing_zero_eq_compl_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega)),
      compl_compl]
    exact hCB.le_law_dualConfig_crossing_one_of_le 6 (m := R) hR le_top
      (by simp; omega)
      (by simp; omega)
      (by simp; omega)
  have hl : ∀ (i : Fin 2) (lo hi : LatticeSite 2), IsLowerSet (crossing i lo hi)ᶜ :=
    fun i lo hi => (isUpperSet_crossing i lo hi).compl
  have hmc : ∀ (i : Fin 2) (lo hi : LatticeSite 2), MeasurableSet (crossing i lo hi)ᶜ :=
    fun i lo hi => (measurableSet_crossing i lo hi).compl
  have hharris : c 9 * c 6 * c 6 ≤ law q (DB ∩ DL ∩ DR) :=
    calc c 9 * c 6 * c 6 ≤ law q DB * law q DL * law q DR := mul_le_mul' (mul_le_mul' hDB hDL) hDR
      _ ≤ law q (DB ∩ DL) * law q DR := mul_le_mul' (prodBernoulli_harris_of_isLowerSet q
          (hl _ _ _) (hl _ _ _) (hmc _ _ _) (hmc _ _ _)) le_rfl
      _ ≤ law q (DB ∩ DL ∩ DR) := prodBernoulli_harris_of_isLowerSet q
          ((hl _ _ _).inter (hl _ _ _)) (hl _ _ _) ((hmc _ _ _).inter (hmc _ _ _)) (hmc _ _ _)
  -- the crossing of the strip reads edges disjoint from those read by the other three events
  set SB : Set (LatticeSite 2) := Icc ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1]
  set SL : Set (LatticeSite 2) := Icc ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R]
  set SR : Set (LatticeSite 2) := Icc ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R]
  set Q : Set (Sym2 (LatticeSite 2)) := {e | ∀ v ∈ e, v ∈ SB} ∪ {e | ∀ v ∈ e, v ∈ SL} ∪
    {e | ∀ v ∈ e, v ∈ SR} with hQ
  have hdet : ∀ (S : Set (LatticeSite 2)), {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ S} ⊆ Q →
      ∀ ω ω' : Config (LatticeSite 2), ω ∩ Q = ω' ∩ Q →
        ω ∩ {e | ∀ v ∈ e, v ∈ S} = ω' ∩ {e | ∀ v ∈ e, v ∈ S} := fun S hS ω ω' h => by
    rw [← inter_eq_right.2 hS, ← inter_assoc, ← inter_assoc, h]
  have hind : law q (O ∩ (DB ∩ DL ∩ DR)) = law q O * law q (DB ∩ DL ∩ DR) := by
    refine prodBernoulli_inter_of_determined q
      (P := {e | ∀ v ∈ e, v ∈ Icc (![-(R : ℤ), R + 2] : LatticeSite 2) ![(R : ℤ), 4 * R]})
      (Q := Q) ?_ (measurableSet_crossing _ _ _)
      (((hmc _ _ _).inter (hmc _ _ _)).inter (hmc _ _ _))
      (fun ω ω' h => mem_crossing_iff_of_inter_eq subset_rfl h) (fun ω ω' h => ?_)
    · rw [Set.disjoint_left]
      intro e he he'
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨(Quot.out e).1, Sym2.out_fst_mem e⟩
      have h₁ := he v hv
      rw [mem_Icc_two_iff] at h₁
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
      rcases he' with (h₂ | h₂) | h₂ <;>
      · have h₃ := h₂ v hv
        rw [mem_Icc_two_iff] at h₃
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₃
        omega
    · have hB' := hdet SB (fun e he => Or.inl (Or.inl he)) ω ω' h
      have hL' := hdet SL (fun e he => Or.inl (Or.inr he)) ω ω' h
      have hR' := hdet SR (fun e he => Or.inr he) ω ω' h
      simp only [hDBdef, hDLdef, hDRdef, mem_inter_iff, mem_compl_iff,
        mem_crossing_iff_of_inter_eq subset_rfl hB', mem_crossing_iff_of_inter_eq subset_rfl hL',
        mem_crossing_iff_of_inter_eq subset_rfl hR']
  calc c 3 * (c 9 * c 6 * c 6) ≤ law q O * law q (DB ∩ DL ∩ DR) := mul_le_mul' hO hharris
    _ = law q (O ∩ (DB ∩ DL ∩ DR)) := hind.symm

/-- **A dual–open–dual point from the crossing events** (the lower bound, deterministic part).
Under the crossing events of `exists_lowest_of_mem_crossing`, some point `x'` of
`[-3R, 3R] × [0, R + 1]` has three half-plane arms to distance `R ≥ 2`, dual, open, dual, once the
edge from `x'` upwards is opened and the other three edges at `x'` are closed. -/
theorem exists_mem_halfArmEvent_three_of_mem_crossing {R : ℕ} (hR : 2 ≤ R)
    (hO : ω ∈ crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R])
    (hB : ω ∉ crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])
    (hL : ω ∉ crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])
    (hR' : ω ∉ crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R]) :
    ∃ i ∈ Finset.Icc (-(3 * (R : ℤ))) (3 * R) ×ˢ Finset.Icc (0 : ℤ) (R + 1),
      insert s(![i.1, i.2], ![i.1, i.2 + 1]) (((ω \ {s(![i.1 - 1, i.2], ![i.1, i.2])}) \
        {s(![i.1, i.2], ![i.1 + 1, i.2])}) \ {s(![i.1, i.2 - 1], ![i.1, i.2])}) ∈
        halfArmEvent ![false, true, false] ![i.1, i.2] 0 R := by
  obtain ⟨x', w, lo, hi, hk₁, hk₂, hl₁, hl₂, hlo0, hlo1, hhi0, hhi1, hw1, key⟩ :=
    exists_dualWalks_of_mem_crossing hR hO hB hL hR'
  obtain ⟨k, l, rfl⟩ : ∃ k l : ℤ, x' = ![k, l] :=
    ⟨x' 0, x' 1, funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hk₁ hk₂ hl₁ hl₂ hlo1
  refine ⟨(k, l), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hk₁, hk₂⟩,
    Finset.mem_Icc.2 ⟨hl₁, hl₂⟩⟩, ?_⟩
  have hv : ∀ a b c d : ℤ, (![a, b] : LatticeSite 2) = ![c, d] ↔ a = c ∧ b = d :=
    fun a b c d => by rw [eq_vec_two_iff]; simp
  have hx : ∀ c d : LatticeSite 2, (![k, l] : LatticeSite 2) ∈ s(c, d) →
      ∀ e : Sym2 (LatticeSite 2), (![k, l] : LatticeSite 2) ∉ e → e ≠ s(c, d) :=
    fun c d h e he h' => he (h' ▸ h)
  obtain ⟨hx'w, gl, δl, gr, δr, ⟨hgl, -, hδls, hδlE⟩, ⟨hgr, -, hδrs, hδrE⟩, hdisj⟩ :=
    key (insert s(![k, l], ![k, l + 1]) (((ω \ {s(![k - 1, l], ![k, l])}) \
      {s(![k, l], ![k + 1, l])}) \ {s(![k, l - 1], ![k, l])})) ![k, l + 1] ![k - 1, l]
      ![k + 1, l] ![k, l - 1] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (mem_insert _ _)
      (fun h => by
        rcases mem_insert_iff.1 h with h | h
        · rw [Sym2.eq_iff, hv, hv, hv, hv] at h; omega
        · exact h.1.1.2 rfl)
      (fun h => by
        rcases mem_insert_iff.1 h with h | h
        · rw [Sym2.eq_iff, hv, hv, hv, hv] at h; omega
        · exact h.1.2 rfl)
      (fun h => by
        rcases mem_insert_iff.1 h with h | h
        · rw [Sym2.eq_iff, hv, hv, hv, hv] at h; omega
        · exact h.2 rfl)
      (fun e _ he => by
        have h₀ := hx ![k, l] ![k, l + 1] (Sym2.mem_mk_left _ _) e he
        have h₁ := hx ![k - 1, l] ![k, l] (Sym2.mem_mk_right _ _) e he
        have h₂ := hx ![k, l] ![k + 1, l] (Sym2.mem_mk_left _ _) e he
        have h₃ := hx ![k, l - 1] ![k, l] (Sym2.mem_mk_right _ _) e he
        simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff, h₀, h₁, h₂, h₃, false_or,
          not_false_eq_true, and_true])
  exact mem_halfArmEvent_three_of_dualWalks hR (lo := lo) (hi := hi) (x' := ![k, l])
    (xl := ![k - 1, l]) (xr := ![k + 1, l]) (by simp [hlo1])
    ⟨by simp [hlo0]; omega, by simp [hhi0]; omega, by simp [hhi1]; omega⟩ (by simp) (by simp)
    hw1 hx'w
    (fun h => by
      rcases mem_insert_iff.1 h with h | h
      · rw [Sym2.eq_iff, hv, hv, hv, hv] at h; omega
      · exact h.1.1.2 rfl)
    (fun h => by
      rcases mem_insert_iff.1 h with h | h
      · rw [Sym2.eq_iff, hv, hv, hv, hv] at h; omega
      · exact h.1.2 rfl)
    δl hgl (fun h hh => (hδls h hh).2) (fun E hE => (hδlE E hE).1) δr hgr
    (fun h hh => (hδrs h hh).2) (fun E hE => (hδrE E hE).1) hdisj

/-- **Three arms in the half-plane, dual–open–dual, lower bound** (lowest points of clusters).
There is `c₁ > 0` with `c₁ ≤ 336 R² · P(A₃⁺(R))` for every `R ≥ 2` and every profile equal to
`1/2` on the edges of `ℤ²`. -/
theorem exists_pos_le_mul_sq_law_halfArmEvent_three :
    ∃ c₁ : ℝ≥0∞, 0 < c₁ ∧ c₁ ≠ ∞ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 2 ≤ R →
        c₁ ≤ 336 * (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R) := by
  obtain ⟨c₀, hc₀, hc₀', hlow⟩ := exists_pos_le_law_crossing_inter_compl
  refine ⟨c₀, hc₀, hc₀', fun q hq R hR => ?_⟩
  set S := Finset.Icc (-(3 * (R : ℤ))) (3 * R) ×ˢ Finset.Icc (0 : ℤ) (R + 1) with hS
  have hedge : ∀ u v : LatticeSite 2, (zdGraph 2).Adj u v → (q s(u, v) : ℝ) = 1 / 2 :=
    fun u v h => hq _ h
  have hcard : S.card = (6 * R + 1) * (R + 2) := by
    rw [hS, Finset.card_product, Int.card_Icc, Int.card_Icc]
    congr 1; omega
  have hcard' : (S.card : ℝ≥0∞) ≤ 21 * (R : ℝ≥0∞) ^ 2 := by
    rw [hcard]
    exact_mod_cast (show (6 * R + 1) * (R + 2) ≤ 21 * R ^ 2 by nlinarith)
  have htr : ∀ i : ℤ × ℤ, law q (halfArmEvent ![false, true, false] ![i.1, i.2] 0 R) =
      law q (halfArmEvent ![false, true, false] 0 0 R) := fun i =>
    law_halfArmEvent_eq_law_halfArmEvent_zero hq _ _ _ _
  calc c₀ ≤ law q (crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R] ∩
          ((crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])ᶜ ∩
            (crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])ᶜ ∩
            (crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R])ᶜ)) := hlow q hq R (by omega)
    _ ≤ law q (⋃ i ∈ S, {ω : Config (LatticeSite 2) | insert s(![i.1, i.2], ![i.1, i.2 + 1])
          (((ω \ {s(![i.1 - 1, i.2], ![i.1, i.2])}) \ {s(![i.1, i.2], ![i.1 + 1, i.2])}) \
            {s(![i.1, i.2 - 1], ![i.1, i.2])}) ∈
          halfArmEvent ![false, true, false] ![i.1, i.2] 0 R}) := measure_mono fun ω hω => by
        obtain ⟨i, hi, h⟩ := exists_mem_halfArmEvent_three_of_mem_crossing hR hω.1 hω.2.1.1
          hω.2.1.2 hω.2.2
        exact mem_iUnion₂.2 ⟨i, hi, h⟩
    _ ≤ ∑ i ∈ S, law q {ω : Config (LatticeSite 2) | insert s(![i.1, i.2], ![i.1, i.2 + 1])
          (((ω \ {s(![i.1 - 1, i.2], ![i.1, i.2])}) \ {s(![i.1, i.2], ![i.1 + 1, i.2])}) \
            {s(![i.1, i.2 - 1], ![i.1, i.2])}) ∈
          halfArmEvent ![false, true, false] ![i.1, i.2] 0 R} := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ S, 16 * law q (halfArmEvent ![false, true, false] ![i.1, i.2] 0 R) :=
        Finset.sum_le_sum fun i _ => law_setOf_insert_sdiff_three_mem_le
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp))
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp))
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp))
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp)) _
    _ = 16 * S.card * law q (halfArmEvent ![false, true, false] 0 0 R) := by
        simp only [htr, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 16 * (21 * (R : ℝ≥0∞) ^ 2) * law q (halfArmEvent ![false, true, false] 0 0 R) := by
        gcongr
    _ = 336 * (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![false, true, false] 0 0 R) := by ring

/-- **Three arms in the half-plane, exponent 2** (Nolin, Theorem 24(2); Werner, *Lectures on
two-dimensional critical percolation*, first exercise sheet), for the colours dual, open, dual
of Werner's lowest points on `ℤ²` bond. At `1/2`, the probability that the boundary vertex `0` of
the upper half-plane has a dual arm, counterclockwise after it an open arm, and after that a dual
arm, to distance `R` in the half-plane, is of order `1/R²`. -/
theorem exists_halfArmEvent_three_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c / R ^ 2 ≤ (law q).real (halfArmEvent ![false, true, false] 0 0 R) ∧
          (law q).real (halfArmEvent ![false, true, false] 0 0 R) ≤ C / R ^ 2 := by
  obtain ⟨C₀, hC₀, hup⟩ := exists_mul_sq_law_halfArmEvent_three_le
  obtain ⟨c₁, hc₁, hc₁', hlow⟩ := exists_pos_le_mul_sq_law_halfArmEvent_three
  have hc₁r : 0 < c₁.toReal := ENNReal.toReal_pos hc₁.ne' hc₁'
  refine ⟨c₁.toReal / 1344, C₀.toReal + 1, by positivity, by positivity,
    fun q hq R hR => ⟨?_, ?_⟩⟩
  · have key : ∀ R' : ℕ, 2 ≤ R' → c₁.toReal ≤
        336 * (R' : ℝ) ^ 2 * (law q).real (halfArmEvent ![false, true, false] 0 0 R') := by
      intro R' hR'
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top R'))) (measure_ne_top _ _)) (hlow q hq R' hR')
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
        ENNReal.toReal_ofNat] at h
      rw [measureReal_def]
      exact h
    have hP : ∀ R' : ℕ, 0 ≤ (law q).real (halfArmEvent ![false, true, false] 0 0 R') :=
      fun R' => measureReal_nonneg
    rcases (show R = 1 ∨ 2 ≤ R by omega) with rfl | hR2
    · have hmono : (law q).real (halfArmEvent ![false, true, false] 0 0 2) ≤
          (law q).real (halfArmEvent ![false, true, false] 0 0 1) :=
        measureReal_mono (halfArmEventIn_subset_halfArmEventIn_of_le (z := 0) (r := 0)
          (σ := ![false, true, false]) (J := fun _ => univ) (N := 1) (R := 2) (by norm_num)
          (by norm_num))
      have h2 := key 2 le_rfl
      norm_num at h2 ⊢
      linarith
    · have h := key R hR2
      have hR' : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
      rw [div_div, div_le_iff₀ (by positivity)]
      nlinarith [hP R, sq_nonneg (R : ℝ)]
  · have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have h := ENNReal.toReal_mono hC₀ (hup q hq R)
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h
    rw [measureReal_def, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (R : ℝ)]

/-! ### Open–dual–open: the dual construction -/

/-- **Opening three edges and closing one**, all of probability one half, multiplies a
probability by at most `16`. -/
theorem law_setOf_insert_insert_insert_sdiff_mem_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {e₁ e₂ e₃ e₄ : Sym2 (LatticeSite 2)} (h₁ : (q e₁ : ℝ) = 1 / 2) (h₂ : (q e₂ : ℝ) = 1 / 2)
    (h₃ : (q e₃ : ℝ) = 1 / 2) (h₄ : (q e₄ : ℝ) = 1 / 2) (F : Set (Config (LatticeSite 2))) :
    law q {ω | insert e₁ (insert e₂ (insert e₃ (ω \ {e₄}))) ∈ F} ≤ 16 * law q F := by
  calc law q {ω | insert e₁ (insert e₂ (insert e₃ (ω \ {e₄}))) ∈ F}
      ≤ 2 * law q {η | insert e₁ (insert e₂ (insert e₃ η)) ∈ F} :=
        law_setOf_diff_singleton_mem_le h₄ {η | insert e₁ (insert e₂ (insert e₃ η)) ∈ F}
    _ ≤ 2 * (2 * law q {η | insert e₁ (insert e₂ η) ∈ F}) :=
        mul_le_mul_right (law_setOf_insert_mem_le h₃ {η | insert e₁ (insert e₂ η) ∈ F}) _
    _ ≤ 2 * (2 * (2 * law q {η | insert e₁ η ∈ F})) :=
        mul_le_mul_right (mul_le_mul_right (law_setOf_insert_mem_le h₂
          {η | insert e₁ η ∈ F}) _) _
    _ ≤ 2 * (2 * (2 * (2 * law q F))) :=
        mul_le_mul_right (mul_le_mul_right (mul_le_mul_right (law_setOf_insert_mem_le h₁ F) _) _) _
    _ = 16 * law q F := by ring

/-- **Three half-plane arms, open–dual–open, from walks at an extended lowest face** (the lower
bound, assembly). Let the face `x` (lower-left corner `x`) lie on the bottom row of the box
`Icc lo hi`, joined to a face `w` of its top row by a dual-open walk of faces of the box, and let
the left, bottom and right edges of `x` be open. Let walks of the dual of the dual configuration,
sharing no vertex, go from the faces on the left of `x` and at `x`, at or above the bottom row,
to faces outside the box (in `ω` they are open walks from the upper corners of `x`, translated
by `(-1, -1)`). If `B_R(x)`, `R ≥ 2`, fits in the box above the row, then `x` has three arms to
distance `R` in the half-plane, open, dual, open: the open arms go round the face `x` through its
left edge, and through its bottom and right edges, and continue along the translated walks. -/
theorem mem_halfArmEvent_three_open_of_dualWalks {R : ℕ} (hR : 2 ≤ R)
    {x xl xu xr xur w gl gr : LatticeSite 2} (hx1 : x 1 = lo 1)
    (hfit : lo 0 + R ≤ x 0 ∧ x 0 + R ≤ hi 0 ∧ x 1 + R ≤ hi 1)
    (hxl : xl 0 + 1 = x 0 ∧ xl 1 = x 1) (hxu : xu 0 = x 0 ∧ xu 1 = x 1 + 1)
    (hxr : xr 0 = x 0 + 1 ∧ xr 1 = x 1) (hxur : xur 0 = x 0 + 1 ∧ xur 1 = x 1 + 1)
    (hw1 : w 1 = hi 1)
    (hxw : dualConfig ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x w)
    (heL : s(x, xu) ∈ ω) (heB : s(x, xr) ∈ ω) (heR : s(xr, xur) ∈ ω)
    (δl : (zdGraph 2).Walk xl gl) (hgl : gl ∉ Icc lo (hi - 1))
    (hδl1 : ∀ h ∈ δl.support, lo 1 ≤ h 1)
    (hδlE : ∀ E ∈ δl.edges, E ∈ dualConfig (dualConfig ω))
    (δr : (zdGraph 2).Walk x gr) (hgr : gr ∉ Icc lo (hi - 1))
    (hδr1 : ∀ h ∈ δr.support, lo 1 ≤ h 1)
    (hδrE : ∀ E ∈ δr.edges, E ∈ dualConfig (dualConfig ω))
    (hdisj : ∀ h ∈ δl.support, h ∉ δr.support) :
    ω ∈ halfArmEvent ![true, false, true] x 0 R := by
  classical
  have hR1 : 1 ≤ R := by omega
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := 2) 1
  set f : zdGraph 2 →g zdGraph 2 := φ.toHom with hfdef
  have hf : ∀ v, f v = v + 1 := fun v => hφ v
  have hf' : (⇑f : LatticeSite 2 → LatticeSite 2) = (· + 1) := funext hf
  have hfi : Function.Injective f := by rw [hf']; exact add_left_injective 1
  -- the open edges of the dual of the dual configuration
  have hdd : ∀ E ∈ dualConfig (dualConfig ω), Sym2.map f E ∈ ω := by
    intro E hE
    rw [dualConfig_dualConfig] at hE
    obtain ⟨g, ⟨hgω, -⟩, rfl⟩ := hE
    have h : ((fun v : LatticeSite 2 => v + 1) ∘ fun v => v - 1) = id := by
      funext v
      simp
    rw [hf', Sym2.map_map, h, Sym2.map_id, id]
    exact hgω
  -- the interior of `B_R(x)`
  have hxT : x ∈ Icc (x - (R : LatticeSite 2) + 1) (x + R - 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hxrT : xr ∈ Icc (x - (R : LatticeSite 2) + 1) (x + R - 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hout : ∀ g : LatticeSite 2, g ∉ Icc lo (hi - 1) → lo 1 ≤ g 1 →
      f g ∉ Icc (x - (R : LatticeSite 2) + 1) (x + R - 1) := fun g hg hg1 h => hg (by
    rw [hf, mem_Icc_two_iff] at h
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega)
  -- the left open arm: up the left edge of `x`, then along the translated left walk
  have hfxl : f xl = xu := by
    rw [hf]
    exact hpt _ _ (by simp only [Pi.add_apply, Pi.one_apply]; omega)
      (by simp only [Pi.add_apply, Pi.one_apply]; omega)
  have hfx : f x = xur := by
    rw [hf]
    exact hpt _ _ (by simp only [Pi.add_apply, Pi.one_apply]; omega)
      (by simp only [Pi.add_apply, Pi.one_apply]; omega)
  have hadjL : (zdGraph 2).Adj x (f xl) := by rw [hfxl, zdGraph_two_adj_iff]; omega
  obtain ⟨pL, DL, sL, hDLs, hpL, hDL⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := Icc (x - (R : LatticeSite 2) + 1) (x + R - 1)) (δl.map f)
    (hout gl hgl (hδl1 gl δl.end_mem_support))
  have hDLsupp : ∀ v ∈ DL.support, ∃ h ∈ δl.support, v = f h := fun v hv => by
    have : v ∈ (δl.map f).support := by
      rw [← hDLs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at this
    obtain ⟨h, hh, rfl⟩ := this
    exact ⟨h, hh, rfl⟩
  have hDLe : ∀ e ∈ DL.edges, e ∈ ω := fun e he => by
    have : e ∈ (δl.map f).edges := by
      rw [← hDLs, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at this
    obtain ⟨E, hE, rfl⟩ := this
    exact hdd E (hδlE E hE)
  have hrowL : ∀ v ∈ DL.support, x 1 + 1 ≤ v 1 := fun v hv => by
    obtain ⟨h, hh, rfl⟩ := hDLsupp v hv
    have := hδl1 h hh
    rw [hf]
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  -- the right open arm: along the bottom and up the right edge of `x`, then the right walk
  have hadjR₁ : (zdGraph 2).Adj x xr := by rw [zdGraph_two_adj_iff]; omega
  have hadjR₂ : (zdGraph 2).Adj xr (f x) := by rw [hfx, zdGraph_two_adj_iff]; omega
  obtain ⟨pR, DR, sR, hDRs, hpR, hDR⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := Icc (x - (R : LatticeSite 2) + 1) (x + R - 1))
    (SimpleGraph.Walk.cons hadjR₂ (δr.map f)) (hout gr hgr (hδr1 gr δr.end_mem_support))
  have hDRsupp : ∀ v ∈ DR.support, v = xr ∨ ∃ h ∈ δr.support, v = f h := fun v hv => by
    have : v ∈ (SimpleGraph.Walk.cons hadjR₂ (δr.map f)).support := by
      rw [← hDRs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, SimpleGraph.Walk.support_map,
      List.mem_map] at this
    rcases this with rfl | ⟨h, hh, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h, hh, rfl⟩
  have hDRe : ∀ e ∈ DR.edges, e ∈ ω := fun e he => by
    have : e ∈ (SimpleGraph.Walk.cons hadjR₂ (δr.map f)).edges := by
      rw [← hDRs, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, SimpleGraph.Walk.edges_map,
      List.mem_map] at this
    rcases this with rfl | ⟨E, hE, rfl⟩
    · rw [hfx]; exact heR
    · exact hdd E (hδrE E hE)
  have hrowR : ∀ v ∈ DR.support, x 1 ≤ v 1 ∧ v ≠ x := fun v hv => by
    rcases hDRsupp v hv with rfl | ⟨h, hh, rfl⟩
    · exact ⟨by omega, fun h => by have := congrFun h 0; omega⟩
    · have := hδr1 h hh
      rw [hf]
      refine ⟨by simp only [Pi.add_apply, Pi.one_apply]; omega, fun h' => ?_⟩
      have := congrFun h' 1
      simp only [Pi.add_apply, Pi.one_apply] at this
      omega
  -- the two open arms
  have hS : ∀ v : LatticeSite 2,
      v ∈ Icc (x - ((0 : ℕ) : LatticeSite 2)) (x + ((0 : ℕ) : LatticeSite 2)) → v = x := by
    intro v hv
    simpa using hv
  have hαL : IsOpenArm ω x 0 (x - R) (x + R) (SimpleGraph.Walk.cons hadjL DL) := by
    refine ⟨⟨by simp, fun v hv hvS => ?_, hpL, fun v hv => ?_⟩, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.support_cons, List.tail_cons] at hv
      have := hrowL v hv
      rw [hS v hvS] at this
      omega
    · rw [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil
        (SimpleGraph.Walk.support_ne_nil _), List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hxT
      · exact hDL v hv
    · rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rw [hfxl]; exact heL
      · exact hDLe e he
  have hαR : IsOpenArm ω x 0 (x - R) (x + R) (SimpleGraph.Walk.cons hadjR₁ DR) := by
    refine ⟨⟨by simp, fun v hv hvS => ?_, hpR, fun v hv => ?_⟩, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.support_cons, List.tail_cons] at hv
      exact (hrowR v hv).2 (hS v hvS)
    · rw [SimpleGraph.Walk.support_cons, List.dropLast_cons_of_ne_nil
        (SimpleGraph.Walk.support_ne_nil _), List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hxT
      · exact hDR v hv
    · rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact heB
      · exact hDRe e he
  have hB : Icc (x - ((0 : ℕ) : LatticeSite 2)) (x + ((0 : ℕ) : LatticeSite 2)) ⊆
      Icc (x - R + 1) (x + R - 1) := fun v hv => by rw [hS v hv]; exact hxT
  have hαLn := hαL.not_nil hB
  have hαRn := hαR.not_nil hB
  have hpLB := hαL.end_mem_boxBoundary hαLn
  have hpRB := hαR.end_mem_boxBoundary hαRn
  have hαLH : ∀ v ∈ (SimpleGraph.Walk.cons hadjL DL).support, x 1 ≤ v 1 := fun v hv => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact le_rfl
    · have := hrowL v hv; omega
  have hαRH : ∀ v ∈ (SimpleGraph.Walk.cons hadjR₁ DR).support, x 1 ≤ v 1 := fun v hv => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact le_rfl
    · exact (hrowR v hv).1
  -- the dual arm, from the face `x` along the dual-open walk to the top
  obtain ⟨P, hPs, hPe⟩ := exists_walk_of_mem_localConn hxw
  have hwF : w ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1) := fun h => by
    rw [mem_Icc_two_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h
    omega
  obtain ⟨g₁, δ₁, c, β, hβ, hβs, hβp, hδ₁n, hδ₁d, hg₁, hδ₁s, hδ₁e⟩ :=
    exists_isDualArm_of_walk hR1 P (by
      rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega) hwF hPe
  have hPH : ∀ v ∈ P.support, x 1 ≤ v 1 := fun v hv => by
    have := hPs v hv
    rw [mem_Icc_two_iff] at this
    omega
  -- the landing order
  have hlt₁ : landingPos (x - R) (x + R) true (SimpleGraph.Walk.cons hadjR₁ DR) <
      landingPos (x - R) (x + R) false β := by
    have h := landingPos_lt_of_dualWalk_left (ω := ω \ {s(x, xr)}) (x := x) (s := xr) (sl := x)
      (fL := x) hxr.2 (by omega) (by omega) ⟨by omega, hxr.2.symm⟩ ⟨by omega, hxr.2.symm⟩ DR
      (fun e he => ⟨hDRe e he, fun h => by
        rw [mem_singleton_iff] at h
        exact (hrowR x (mem_support_of_mem_edge DR he (h ▸ Sym2.mem_mk_left x xr))).2 rfl⟩)
      (fun v hv => hαR.mem_Icc hαRn (by
        rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv))
      (fun v hv => (hrowR v hv).1) hpRB (fun h => h.2 rfl) δ₁ hδ₁n hδ₁d
      (fun h hh => hPH h (hδ₁s h hh)) hg₁
      (fun E hE => dualConfig_anti sdiff_subset (hPe E (hδ₁e E hE)))
    rw [landingPos_false, hβp]
    rw [landingPos_true] at h ⊢
    exact h
  have hlt₂ : landingPos (x - R) (x + R) false β <
      landingPos (x - R) (x + R) true (SimpleGraph.Walk.cons hadjL DL) := by
    have h := lt_landingPos_of_dualWalk_right (ω := ω \ {s(x, xr)}) (x := x) (s := x)
      (sr := xr) (fR := x) rfl (by omega) (by omega) hxr ⟨rfl, rfl⟩
      (SimpleGraph.Walk.cons hadjL DL)
      (fun e he => ⟨hαL.mem_of_mem_edges e he, fun h => by
        rw [mem_singleton_iff] at h
        rw [h, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with he | he
        · rw [hfxl, Sym2.eq_iff] at he
          rcases he with ⟨-, he⟩ | ⟨he, -⟩
          · have := congrFun he 1; omega
          · have := congrFun he 1; omega
        · have := hrowL xr (mem_support_of_mem_edge DL he (Sym2.mem_mk_right x xr))
          omega⟩)
      (fun v hv => hαL.mem_Icc hαLn hv) hαLH hpLB (fun h => h.2 rfl) δ₁ hδ₁n hδ₁d
      (fun h hh => hPH h (hδ₁s h hh)) hg₁
      (fun E hE => dualConfig_anti sdiff_subset (hPe E (hδ₁e E hE)))
    rw [landingPos_false, hβp]
    exact h
  -- the open arms meet only at `x`
  have hd₀₂ : ∀ v ∈ (SimpleGraph.Walk.cons hadjR₁ DR).support.tail,
      v ∉ (SimpleGraph.Walk.cons hadjL DL).support := fun v hv hv' => by
    rw [SimpleGraph.Walk.support_cons, List.tail_cons] at hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv'
    rcases hv' with rfl | hv'
    · exact (hrowR v hv).2 rfl
    obtain ⟨h, hh, rfl⟩ := hDLsupp v hv'
    rcases hDRsupp _ hv with h' | ⟨h', hh', h''⟩
    · have := hrowL _ hv'
      rw [h'] at this
      omega
    · exact hdisj h hh (hfi h'' ▸ hh')
  have hd₂₀ : ∀ v ∈ (SimpleGraph.Walk.cons hadjL DL).support.tail,
      v ∉ (SimpleGraph.Walk.cons hadjR₁ DR).support := fun v hv hv' => by
    rw [SimpleGraph.Walk.support_cons, List.tail_cons] at hv
    exact hd₀₂ v (by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv'
      rcases hv' with rfl | hv'
      · exfalso
        have := hrowL _ hv
        omega
      · rw [SimpleGraph.Walk.support_cons, List.tail_cons]; exact hv') (by
        rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
  -- the three arms form the half-plane event
  have hfam : ∀ i : Fin 3, ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (![true, false, true] i) x 0 (x - R) (x + R) γ ∧ (∀ v ∈ γ.support, x 1 ≤ v 1) ∧
      (∀ v ∈ γ.support, ![true, false, true] i = true →
        v ∈ ![(SimpleGraph.Walk.cons hadjR₁ DR).support, [],
          (SimpleGraph.Walk.cons hadjL DL).support] i) ∧
      (∀ v ∈ γ.support.tail, ![true, false, true] i = true →
        v ∈ ![(SimpleGraph.Walk.cons hadjR₁ DR).support.tail, [],
          (SimpleGraph.Walk.cons hadjL DL).support.tail] i) ∧
      landingPos (x - R) (x + R) (![true, false, true] i) γ =
        ![landingPos (x - R) (x + R) true (SimpleGraph.Walk.cons hadjR₁ DR),
          landingPos (x - R) (x + R) false β,
          landingPos (x - R) (x + R) true (SimpleGraph.Walk.cons hadjL DL)] i := by
    intro i
    fin_cases i
    · exact ⟨_, _, _, hαR, hαRH, fun v hv _ => hv, fun v hv _ => hv, rfl⟩
    · exact ⟨_, _, β, hβ, fun v hv => hPH v (hβs v hv), fun v _ h => absurd h (by decide),
        fun v _ h => absurd h (by decide), rfl⟩
    · exact ⟨_, _, _, hαL, hαLH, fun v hv _ => hv, fun v hv _ => hv, rfl⟩
  choose a b γ hγ hγH hγs hγt hγL using hfam
  refine mem_halfArmEvent_iff.2 ⟨a, b, γ, hγ, ⟨fun i k hik hi hk v hv hv' => ?_,
    fun i k hik hi hk => ?_⟩, hγH, ?_⟩
  · have h₁ := hγt i v hv hi
    have h₂ := hγs k v hv' hk
    fin_cases i <;> fin_cases k
    all_goals first
      | exact absurd rfl hik
      | exact absurd hi (by decide)
      | exact absurd hk (by decide)
      | exact hd₀₂ v h₁ h₂
      | exact hd₂₀ v h₁ h₂
  · fin_cases i <;> fin_cases k
    all_goals first
      | exact absurd rfl hik
      | exact absurd hi (by decide)
      | exact absurd hk (by decide)
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    · rw [hγL, hγL]
      exact hlt₁
    · rw [hγL, hγL]
      exact hlt₂

/-- **An open–dual–open point from dual crossing events** (the lower bound, deterministic
part). Under the crossing events of `exists_lowest_of_mem_crossing` for the dual configuration,
some face `x` of `[-3R, 3R] × [0, R + 1]` is, once its left, bottom and right edges are opened
and its top edge is closed, the unique lowest face of a dual cluster reaching far, and its lower
left corner `x` has three half-plane arms to distance `R ≥ 2`, open, dual, open. -/
theorem exists_mem_halfArmEvent_three_open_of_mem_crossing {R : ℕ} (hR : 2 ≤ R)
    (hO : dualConfig ω ∈ crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R])
    (hB : dualConfig ω ∉ crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])
    (hL : dualConfig ω ∉ crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])
    (hR' : dualConfig ω ∉ crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R]) :
    ∃ i ∈ Finset.Icc (-(3 * (R : ℤ))) (3 * R) ×ˢ Finset.Icc (0 : ℤ) (R + 1),
      insert s(![i.1, i.2], ![i.1, i.2 + 1]) (insert s(![i.1, i.2], ![i.1 + 1, i.2])
        (insert s(![i.1 + 1, i.2], ![i.1 + 1, i.2 + 1])
          (ω \ {s(![i.1, i.2 + 1], ![i.1 + 1, i.2 + 1])}))) ∈
        halfArmEvent ![true, false, true] ![i.1, i.2] 0 R := by
  obtain ⟨x', w, lo, hi, hk₁, hk₂, hl₁, hl₂, hlo0, hlo1, hhi0, hhi1, hw1, key⟩ :=
    exists_dualWalks_of_mem_crossing hR hO hB hL hR'
  obtain ⟨k, l, rfl⟩ : ∃ k l : ℤ, x' = ![k, l] :=
    ⟨x' 0, x' 1, funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hk₁ hk₂ hl₁ hl₂ hlo1
  refine ⟨(k, l), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hk₁, hk₂⟩,
    Finset.mem_Icc.2 ⟨hl₁, hl₂⟩⟩, ?_⟩
  have hv : ∀ a b c d : ℤ, (![a, b] : LatticeSite 2) = ![c, d] ↔ a = c ∧ b = d :=
    fun a b c d => by rw [eq_vec_two_iff]; simp
  -- the four sides of the face `x` and their dual edges
  set eL : Sym2 (LatticeSite 2) := s(![k, l], ![k, l + 1]) with heLdef
  set eB : Sym2 (LatticeSite 2) := s(![k, l], ![k + 1, l]) with heBdef
  set eR : Sym2 (LatticeSite 2) := s(![k + 1, l], ![k + 1, l + 1]) with heRdef
  set eT : Sym2 (LatticeSite 2) := s(![k, l + 1], ![k + 1, l + 1]) with heTdef
  set ω' := insert eL (insert eB (insert eR (ω \ {eT}))) with hω'
  have hadj : ∀ a b c d : ℤ, (a = c ∧ (b + 1 = d ∨ d + 1 = b)) ∨ (b = d ∧ (a + 1 = c ∨ c + 1 = a)) →
      s((![a, b] : LatticeSite 2), ![c, d]) ∈ (zdGraph 2).edgeSet := fun a b c d h => by
    rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]; simpa using h
  have hdual : ∀ a b c d a' b' c' d' : ℤ, (a' ≠ c' ∨ b' ≠ d') →
      (a' = (a + c - b + d - 1) / 2 ∧ b' = (a - c + b + d - 1) / 2 ∨
        a' = (c + a - d + b - 1) / 2 ∧ b' = (c - a + d + b - 1) / 2) →
      (c' = (a + c - b + d - 1) / 2 ∧ d' = (a - c + b + d - 1) / 2 ∨
        c' = (c + a - d + b - 1) / 2 ∧ d' = (c - a + d + b - 1) / 2) →
      dualEdge s((![a, b] : LatticeSite 2), ![c, d]) = s(![a', b'], ![c', d']) :=
    fun a b c d a' b' c' d' hne h₁ h₂ => by
      refine (Sym2.mem_and_mem_iff (by rw [Ne, hv]; omega)).1 ⟨?_, ?_⟩ <;>
      · simp only [dualEdge_mk, Sym2.mem_iff, hv, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
  have hdT : dualEdge eT = s(![k, l], ![k, l + 1]) :=
    hdual _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have hdL : dualEdge eL = s(![k - 1, l], ![k, l]) :=
    hdual _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have hdR : dualEdge eR = s(![k, l], ![k + 1, l]) :=
    hdual _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have hdB : dualEdge eB = s(![k, l - 1], ![k, l]) :=
    hdual _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have hTL : eT ≠ eL := by rw [heTdef, heLdef, Ne, Sym2.eq_iff, hv, hv, hv, hv]; omega
  have hTB : eT ≠ eB := by rw [heTdef, heBdef, Ne, Sym2.eq_iff, hv, hv, hv, hv]; omega
  have hTR : eT ≠ eR := by rw [heTdef, heRdef, Ne, Sym2.eq_iff, hv, hv, hv, hv]; omega
  have hLω : eL ∈ ω' := mem_insert _ _
  have hBω : eB ∈ ω' := mem_insert_of_mem _ (mem_insert _ _)
  have hRω : eR ∈ ω' := mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert _ _))
  have hTω : eT ∉ ω' := by
    simp only [hω', mem_insert_iff, mem_sdiff, mem_singleton_iff, hTL, hTB, hTR, not_true_eq_false,
      and_false, or_self, not_false_eq_true]
  have hedge : ∀ e : Sym2 (LatticeSite 2), e ∈ (zdGraph 2).edgeSet →
      dualEdge (Sym2.map (· + 1) (dualEdge e)) = e := fun e he =>
    congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨e, he⟩)
  obtain ⟨hx'w, gl, δl, gr, δr, ⟨hgl, -, hδls, hδlE⟩, ⟨hgr, -, hδrs, hδrE⟩, hdisj⟩ :=
    key (dualConfig ω') ![k, l + 1] ![k - 1, l] ![k + 1, l] ![k, l - 1] (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      ((mem_dualConfig_iff' _ _).2 ⟨eT, hadj _ _ _ _ (by omega), hTω, hdT⟩)
      (by rw [← hdL, dualEdge_mem_dualConfig_iff (hadj _ _ _ _ (by omega))]; exact not_not.2 hLω)
      (by rw [← hdR, dualEdge_mem_dualConfig_iff (hadj _ _ _ _ (by omega))]; exact not_not.2 hRω)
      (by rw [← hdB, dualEdge_mem_dualConfig_iff (hadj _ _ _ _ (by omega))]; exact not_not.2 hBω)
      (fun e he hx => by
        rw [mem_dualConfig_iff, mem_dualConfig_iff]
        have hne : ∀ e' : Sym2 (LatticeSite 2), (![k, l] : LatticeSite 2) ∈ dualEdge e' →
            Sym2.map (· + 1) (dualEdge e) ≠ e' := fun e' h₁ h₂ => hx (by
          rw [← hedge e he, h₂]; exact h₁)
        have h₁ := hne eT (by rw [hdT]; exact Sym2.mem_mk_left _ _)
        have h₂ := hne eL (by rw [hdL]; exact Sym2.mem_mk_right _ _)
        have h₃ := hne eR (by rw [hdR]; exact Sym2.mem_mk_left _ _)
        have h₄ := hne eB (by rw [hdB]; exact Sym2.mem_mk_right _ _)
        simp only [hω', mem_insert_iff, mem_sdiff, mem_singleton_iff, h₁, h₂, h₃, h₄, false_or,
          not_false_eq_true, and_true])
  exact mem_halfArmEvent_three_open_of_dualWalks hR (ω := ω') (lo := lo) (hi := hi)
    (x := ![k, l]) (xl := ![k - 1, l]) (xu := ![k, l + 1]) (xr := ![k + 1, l])
    (xur := ![k + 1, l + 1]) (by simp [hlo1])
    ⟨by simp [hlo0]; omega, by simp [hhi0]; omega, by simp [hhi1]; omega⟩ (by simp) (by simp)
    (by simp) (by simp) hw1 hx'w hLω hBω hRω δl hgl (fun h hh => (hδls h hh).2)
    (fun E hE => (hδlE E hE).1) δr hgr (fun h hh => (hδrs h hh).2) (fun E hE => (hδrE E hE).1)
    hdisj

/-- **Three arms in the half-plane, open–dual–open, lower bound** (lowest faces of dual
clusters). There is `c₁ > 0` with `c₁ ≤ 336 R² · P(A⁺(R))` for the colours open, dual, open,
every `R ≥ 2` and every profile equal to `1/2` on the edges of `ℤ²`: the construction of the
dual–open–dual lower bound, for the dual configuration, whose law at `1/2` is that of the
configuration (self-duality). -/
theorem exists_pos_le_mul_sq_law_halfArmEvent_three_open :
    ∃ c₁ : ℝ≥0∞, 0 < c₁ ∧ c₁ ≠ ∞ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 2 ≤ R →
        c₁ ≤ 336 * (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![true, false, true] 0 0 R) := by
  obtain ⟨c₀, hc₀, hc₀', hlow⟩ := exists_pos_le_law_crossing_inter_compl
  refine ⟨c₀, hc₀, hc₀', fun q hq R hR => ?_⟩
  set S := Finset.Icc (-(3 * (R : ℤ))) (3 * R) ×ˢ Finset.Icc (0 : ℤ) (R + 1) with hS
  set E := crossing 1 ![-(R : ℤ), R + 2] ![(R : ℤ), 4 * R] ∩
    ((crossing 1 ![-(4 * (R : ℤ)), 0] ![4 * (R : ℤ), R + 1])ᶜ ∩
      (crossing 0 ![-(3 * (R : ℤ) + 1), 0] ![-(2 * (R : ℤ)), 4 * R])ᶜ ∩
      (crossing 0 ![2 * (R : ℤ), 0] ![3 * (R : ℤ) + 1, 4 * R])ᶜ) with hEdef
  have hedge : ∀ u v : LatticeSite 2, (zdGraph 2).Adj u v → (q s(u, v) : ℝ) = 1 / 2 :=
    fun u v h => hq _ h
  have hcard : S.card = (6 * R + 1) * (R + 2) := by
    rw [hS, Finset.card_product, Int.card_Icc, Int.card_Icc]
    congr 1; omega
  have hcard' : (S.card : ℝ≥0∞) ≤ 21 * (R : ℝ≥0∞) ^ 2 := by
    rw [hcard]
    exact_mod_cast (show (6 * R + 1) * (R + 2) ≤ 21 * R ^ 2 by nlinarith)
  have htr : ∀ i : ℤ × ℤ, law q (halfArmEvent ![true, false, true] ![i.1, i.2] 0 R) =
      law q (halfArmEvent ![true, false, true] 0 0 R) := fun i =>
    law_halfArmEvent_eq_law_halfArmEvent_zero hq _ _ _ _
  have hEm : MeasurableSet E := (measurableSet_crossing _ _ _).inter
    ((((measurableSet_crossing _ _ _).compl).inter (measurableSet_crossing _ _ _).compl).inter
      (measurableSet_crossing _ _ _).compl)
  have hself : law q (dualConfig ⁻¹' E) = law q E :=
    law_preimage_dualConfig_eq hq hEm fun ω => by
      simp only [hEdef, mem_inter_iff, mem_compl_iff, inter_edgeSet_mem_crossing_iff]
  calc c₀ ≤ law q E := hlow q hq R (by omega)
    _ = law q (dualConfig ⁻¹' E) := hself.symm
    _ ≤ law q (⋃ i ∈ S, {ω : Config (LatticeSite 2) | insert s(![i.1, i.2], ![i.1, i.2 + 1])
          (insert s(![i.1, i.2], ![i.1 + 1, i.2]) (insert s(![i.1 + 1, i.2], ![i.1 + 1, i.2 + 1])
            (ω \ {s(![i.1, i.2 + 1], ![i.1 + 1, i.2 + 1])}))) ∈
          halfArmEvent ![true, false, true] ![i.1, i.2] 0 R}) := measure_mono fun ω hω => by
        obtain ⟨i, hi, h⟩ := exists_mem_halfArmEvent_three_open_of_mem_crossing hR hω.1
          hω.2.1.1 hω.2.1.2 hω.2.2
        exact mem_iUnion₂.2 ⟨i, hi, h⟩
    _ ≤ ∑ i ∈ S, law q {ω : Config (LatticeSite 2) | insert s(![i.1, i.2], ![i.1, i.2 + 1])
          (insert s(![i.1, i.2], ![i.1 + 1, i.2]) (insert s(![i.1 + 1, i.2], ![i.1 + 1, i.2 + 1])
            (ω \ {s(![i.1, i.2 + 1], ![i.1 + 1, i.2 + 1])}))) ∈
          halfArmEvent ![true, false, true] ![i.1, i.2] 0 R} := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ S, 16 * law q (halfArmEvent ![true, false, true] ![i.1, i.2] 0 R) :=
        Finset.sum_le_sum fun i _ => law_setOf_insert_insert_insert_sdiff_mem_le
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp))
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp))
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp))
          (hedge _ _ (by rw [zdGraph_two_adj_iff]; simp)) _
    _ = 16 * S.card * law q (halfArmEvent ![true, false, true] 0 0 R) := by
        simp only [htr, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 16 * (21 * (R : ℝ≥0∞) ^ 2) * law q (halfArmEvent ![true, false, true] 0 0 R) := by
        gcongr
    _ = 336 * (R : ℝ≥0∞) ^ 2 * law q (halfArmEvent ![true, false, true] 0 0 R) := by ring

/-- **Three arms in the half-plane, open–dual–open, lower bound** (Nolin, Theorem 24(2), for the
colours of the arms plan). At `1/2`, the probability that the boundary vertex `0` of the upper
half-plane has an open arm, counterclockwise after it a dual arm, and after that an open arm, to
distance `R` in the half-plane, is at least `c / R²`. The matching upper bound is not proved here:
open arms may run along the line, so the lowest points of open–dual–open configurations are not
separated points of clusters; it needs arm separation in the half-plane. -/
theorem exists_halfArmEvent_open_dual_open_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c / R ^ 2 ≤ (law q).real (halfArmEvent ![true, false, true] 0 0 R) := by
  obtain ⟨c₁, hc₁, hc₁', hlow⟩ := exists_pos_le_mul_sq_law_halfArmEvent_three_open
  have hc₁r : 0 < c₁.toReal := ENNReal.toReal_pos hc₁.ne' hc₁'
  refine ⟨c₁.toReal / 1344, by positivity, fun q hq R hR => ?_⟩
  have key : ∀ R' : ℕ, 2 ≤ R' → c₁.toReal ≤
      336 * (R' : ℝ) ^ 2 * (law q).real (halfArmEvent ![true, false, true] 0 0 R') := by
    intro R' hR'
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top R'))) (measure_ne_top _ _)) (hlow q hq R' hR')
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
    rw [measureReal_def]
    exact h
  have hP : ∀ R' : ℕ, 0 ≤ (law q).real (halfArmEvent ![true, false, true] 0 0 R') :=
    fun R' => measureReal_nonneg
  rcases (show R = 1 ∨ 2 ≤ R by omega) with rfl | hR2
  · have hmono : (law q).real (halfArmEvent ![true, false, true] 0 0 2) ≤
        (law q).real (halfArmEvent ![true, false, true] 0 0 1) :=
      measureReal_mono (halfArmEventIn_subset_halfArmEventIn_of_le (z := 0) (r := 0)
        (σ := ![true, false, true]) (J := fun _ => univ) (N := 1) (R := 2) (by norm_num)
        (by norm_num))
    have h2 := key 2 le_rfl
    norm_num at h2 ⊢
    linarith
  · have h := key R hR2
    have hR' : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith [hP R, sq_nonneg (R : ℝ)]

end HalfPlaneThreeArms

end PercLib.Models.Planar
