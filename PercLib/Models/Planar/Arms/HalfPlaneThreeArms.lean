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
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

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

end HalfPlaneThreeArms

end PercLib.Models.Planar
