/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12, and
quasi-multiplicativity, Proposition 17).
-/
module

public import PercLib.Models.Planar.Arms.CorridorGluing

/-!
# Gluing at the inner boundary: conditioning, independence and the barrier

Arms separated at the *inner* boundary of an annulus (`innerSeparatedArmEvent`) carry fences inside
`B_r(z)` next to their starts. The two-sided gluing (`TwoSidedGluing.lean`) joins such arms, from
`B_{R'}(z)` outwards, to arms separated at the *outer* boundary of a smaller box `B_R(z)`, through
corridors in the annulus between `B_R(z)` and `B_{R'}(z)`. This file proves the facts about the
inner family that the gluing needs; they mirror those of `OuterGluing.lean` for the outer family.

* **Conditioning.** Once the starts of the arms are confined to fixed sets, the event of arms
  separated at the inner boundary is upper for the mixed order (increasing in the open corridors,
  decreasing in the dual corridors) among the configurations that agree off the corridors, provided
  each pair read by a corridor has an end in `B_r(z)` and, for fences of length `2K ≤ 2M`, the
  corridors of one colour avoid the boxes of radius `M + 1` about the possible starts of the arms
  of the other colour. The arms beyond the first step do not see the corridors: an open arm meets
  `B_r(z)` only at its first vertex, and a dual arm crosses only edges with both ends outside
  `B_r(z)`.
* **Independence.** The event is determined by the pairs with both ends outside `B_ρ(z)` for
  `ρ + M + K + 1 < r`, and the event of arms separated at the outer boundary of `B_R(z)` by the
  pairs with both ends in `B_{R + M + K + 1}(z)`; for nested radii they are independent.
* **Positions at the inner boundary.** The inner position of an arm is given by one of four
  formulas, according to the direction of its first step; arms starting near each other, away from
  the corners, have nearby inner positions.
* **The barrier at the inner boundary.** Without packs, a walk of the colour of arm `i` that starts
  on arm `i` near its start and stays near that start meets no other arm of that colour: otherwise
  the last visit of `B_r(z)` on the walk "arm `i` up to the walk, the walk, arm `k` from the
  meeting point" starts an arm landing where arm `k` lands with the inner position of arm `i`, which
  the sector lemma (in its mirror form, `sbtw_innerPos_iff_of_landingPos_eq`) forbids.

## Main results

* `HasInnerFence.of_cond_subset`, `hasInnerFence_iff_of_inter_eq_of_le`, `HasInnerFence.side`.
* `IsOpenArm.mem_Icc_of_mem_edges_of_mem`: an edge of an open arm with an end in `B_r(z)` is its
  first edge.
* `innerSeparated_of_mixed_of_forall_mem`, `measurableSet_setOf_innerSeparated_forall_mem`: the
  conditioning.
* `innerSeparated_of_inter_eq_compl` (the inner family is determined from outside `B_ρ(z)`),
  `outerSeparated_of_inter_eq` (the outer family is determined by `B_{R + M + K + 1}(z)`),
  `law_inter_eq_mul_of_separated` (independence).
* `IsArm.innerPos_cases`, `abs_innerPos_sub_le`.
* `sbtw_innerPos_iff_sbtw_landingPos_of_isArm`, `sbtw_innerPos_iff_of_landingPos_eq`,
  `false_of_landingPos_eq_of_abs_lt`: sectors read at the inner boundary.
* `notMem_support_of_subset_Icc_start`: the barrier at the inner boundary.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ}

/-! ### Inner fences under changes of the configuration -/

/-- **An inner fence survives when the configuration of its colour grows.** -/
theorem HasInnerFence.of_cond_subset {ω' : Config (LatticeSite 2)} {c : Bool} {M K : ℕ}
    {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    (hωω' : cond c ω (dualConfig ω) ⊆ cond c ω' (dualConfig ω'))
    (h : HasInnerFence ω c z r M K γ) : HasInnerFence ω' c z r M K γ := by
  have hc : ∀ S x y, cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn S x y →
      cond c ω' (dualConfig ω') ∩ (zdGraph 2).edgeSet ∈ localConn S x y :=
    fun S x y h => localConn_mono (inter_subset_inter_left _ hωω') h
  obtain ⟨x, hx, u, v, hxu, hf⟩ := h
  refine ⟨x, hx, u, v, hc _ _ _ hxu, ?_⟩
  rcases hf with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · exact Or.inl ⟨h₁, h₂, h₃, hc _ _ _ h₄⟩
  · exact Or.inr (Or.inl ⟨h₁, h₂, h₃, hc _ _ _ h₄⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, hc _ _ _ h₄⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, hc _ _ _ h₄⟩))

/-- **The side of an inner fence.** An arm with an inner fence starts on one of the four sides of
`B_r(z)` (a dual arm at a face touching it from outside). -/
theorem HasInnerFence.side {c : Bool} {M K : ℕ} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    (h : HasInnerFence ω c z r M K γ) :
    a 1 = z 1 + r ∨ a 0 = z 0 + r ∨ a 1 = z 1 - r - cond c 0 1 ∨ a 0 = z 0 - r - cond c 0 1 := by
  obtain ⟨_, _, _, _, _, hf⟩ := h
  rcases hf with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **Determination, sharp form.** When `K ≤ M`, whether an arm starting at `a` has an inner fence
of length `2K` and depth `M` depends only on the pairs with both ends in any set containing
`Icc (a - M) (a + (M + 1))`: the fence box lies in the box of radius `M` about `a`. -/
theorem hasInnerFence_iff_of_inter_eq_of_le {ω' : Config (LatticeSite 2)} {c : Bool} {M K : ℕ}
    (hKM : K ≤ M) {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b} {T : Set (LatticeSite 2)}
    (hT : Icc (a - (M : LatticeSite 2)) (a + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    HasInnerFence ω c z r M K γ ↔ HasInnerFence ω' c z r M K γ := by
  suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      ω₁ ∩ {e | ∀ v ∈ e, v ∈ T} = ω₂ ∩ {e | ∀ v ∈ e, v ∈ T} →
      HasInnerFence ω₁ c z r M K γ → HasInnerFence ω₂ c z r M K γ from
    ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω₁ ω₂ h₁₂ hf
  have hconn : ∀ p q : LatticeSite 2, (∀ w ∈ Icc p (q + 1), w ∈
      Icc (a - (M : LatticeSite 2)) (a + ((M + 1 : ℕ) : LatticeSite 2))) →
      ∀ x y, cond c ω₁ (dualConfig ω₁) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y →
        cond c ω₂ (dualConfig ω₂) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc p q) x y :=
    fun p q hpq x y hxy => (cond_inter_edgeSet_mem_localConn_iff_of_inter_eq c
      (fun w hw => hT (hpq w hw)) h₁₂ x y).1 hxy
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  refine ⟨x, hx, u, v, hconn _ _ (fun w hw => ?_) _ _ hxu, ?_⟩
  · rw [mem_Icc_two_iff] at hw ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  rcases hfen with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩)
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩))
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega
  · refine Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, hconn _ _ (fun w hw => ?_) _ _ h₄⟩))
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hw ⊢
    push_cast
    omega

/-! ### Pairs used by an arm near its inner box -/

/-- **Edges of an open arm near the inner box.** An edge of an open arm from `B_r(z)` with an end
in `B_r(z)` is its first edge: both its ends lie in `Icc (a - 1) (a + 1)`, `a` the first vertex. -/
theorem IsOpenArm.mem_Icc_of_mem_edges_of_mem {lo hi a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsOpenArm ω z r lo hi γ) {e : Sym2 (LatticeSite 2)}
    (he : e ∈ γ.edges) {v : LatticeSite 2} (hv : v ∈ e)
    (hvr : v ∈ Icc (z - (r : LatticeSite 2)) (z + r)) :
    ∀ w ∈ e, w ∈ Icc (a - 1) (a + 1) := by
  unfold SimpleGraph.Walk.edges at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
  have hsnd : d.snd ∉ Icc (z - (r : LatticeSite 2)) (z + r) :=
    h.isCrossing.notMem_of_mem_tail _ (by
      rw [← SimpleGraph.Walk.map_snd_darts]
      exact List.mem_map_of_mem hd)
  have hfst : d.fst ∈ γ.support := γ.dart_fst_mem_support_of_mem_darts hd
  change v ∈ s(d.fst, d.snd) at hv
  have hva : v = d.fst := by
    rcases Sym2.mem_iff.1 hv with h' | h'
    · exact h'
    · exact absurd (h' ▸ hvr) hsnd
  have hfa : d.fst = a := by
    rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at hfst
    rcases hfst with h' | h'
    · exact h'
    · exact absurd (hva ▸ hvr) (h.isCrossing.notMem_of_mem_tail _ h')
  have hadj := (zdGraph_two_adj_iff _ _).1 d.adj
  intro w hw
  change w ∈ s(d.fst, d.snd) at hw
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  rcases Sym2.mem_iff.1 hw with rfl | rfl
  · rw [hfa]
    omega
  · rw [hfa] at hadj
    omega

/-! ### Conditioning on arms separated at the inner boundary -/

section Conditioning

variable {j : ℕ} {σ : Fin j → Bool} {s : ℝ} {M K : ℕ}

/-- **Arms separated at the inner boundary, with confined starts, stay separated under the mixed
order off the corridors** (one family of arms). Let `K ≤ M`, `1 ≤ M`, let `T` be a set of pairs
(the corridors) each with an end in `B_r(z)`, and `D` a set of pairs (morally the dual corridors).
Suppose that a pair of `T` with both ends in the box `Icc (a - M) (a + (M + 1))` about a possible
start `a ∈ B i` of arm `i` lies in `D` exactly when arm `i` is dual. If `γ` is a family of arms of
`ω` from `B_r(z)`, separated at the inner boundary, with starts in the sets `B i`, then it is such a
family of arms of every `ω'` that agrees with `ω` off `T`, has more open pairs than `ω` off `D` and
fewer on `D`. -/
theorem innerSeparated_of_mixed_of_forall_mem (hKM : K ≤ M) (hM : 1 ≤ M)
    {B : Fin j → Set (LatticeSite 2)} {T D : Set (Sym2 (LatticeSite 2))}
    (hT : ∀ e ∈ T, ∃ v ∈ e, v ∈ Icc (z - (r : LatticeSite 2)) (z + r))
    (hTB : ∀ i, ∀ a ∈ B i, ∀ e ∈ T, (∀ v ∈ e, v ∈ Icc (a - (M : LatticeSite 2))
      (a + ((M + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false))
    {ω' : Config (LatticeSite 2)} (h₀ : ω \ T = ω' \ T) (h₁ : ω \ D ⊆ ω' \ D)
    (h₂ : ω' ∩ D ⊆ ω ∩ D) {lo hi : LatticeSite 2} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i))
    (hsep : ArmsInnerSeparated ω σ z r s M K γ) (hB : ∀ i, a i ∈ B i) :
    (∀ i, IsArm ω' (σ i) z r lo hi (γ i)) ∧ ArmsInnerSeparated ω' σ z r s M K γ := by
  obtain ⟨hs₁, hs₂, hf⟩ := hsep
  have key : ∀ e, e ∉ T → (e ∈ ω ↔ e ∈ ω') := by
    intro e heT
    have := congrArg (e ∈ ·) h₀
    simp only [mem_sdiff, eq_iff_iff] at this
    constructor
    · intro he
      exact (this.1 ⟨he, heT⟩).1
    · intro he
      exact (this.2 ⟨he, heT⟩).1
  have hbox : ∀ i, ∀ v ∈ Icc (a i - 1) (a i + 1), v ∈ Icc (a i - (M : LatticeSite 2))
      (a i + ((M + 1 : ℕ) : LatticeSite 2)) := by
    intro i v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    push_cast
    omega
  refine ⟨fun i => ?_, ⟨hs₁, hs₂, fun i => ?_⟩⟩
  · -- the arms
    have hγi := hγ i
    cases hc : σ i
    · rw [hc] at hγi
      have h' : IsDualArm ω z r lo hi (γ i) := hγi
      refine ⟨h'.isCrossing, fun E hE => ?_⟩
      obtain ⟨e, he, heω, rfl, -, hout⟩ := h'.exists_mem_edgeSet_of_mem_edges hE
      rw [dualEdge_mem_dualConfig_iff he]
      intro heω'
      have heT : e ∉ T := fun heT => by
        obtain ⟨v, hv, hvr⟩ := hT e heT
        exact hout v hv hvr
      exact heω ((key e heT).2 heω')
    · rw [hc] at hγi
      have h' : IsOpenArm ω z r lo hi (γ i) := hγi
      refine ⟨h'.isCrossing, fun e he => ?_⟩
      have heω := h'.mem_of_mem_edges e he
      by_cases heT : e ∈ T
      · obtain ⟨v, hv, hvr⟩ := hT e heT
        have heD : e ∉ D := fun h => by
          have := (hTB i (a i) (hB i) e heT
            (fun w hw => hbox i w (h'.mem_Icc_of_mem_edges_of_mem he hv hvr w hw))).1 h
          simp [hc] at this
        exact (h₁ ⟨heω, heD⟩).1
      · exact (key e heT).1 heω
  · -- the fences
    set Bx := Icc (a i - (M : LatticeSite 2)) (a i + ((M + 1 : ℕ) : LatticeSite 2)) with hBx
    have hfi := hf i
    cases hc : σ i
    · rw [hc] at hfi
      set ω₁ := ω' ∩ {e | ∀ v ∈ e, v ∈ Bx} with hω₁
      have hsub : ω₁ ⊆ ω := by
        rintro e ⟨he, heB⟩
        by_cases heT : e ∈ T
        · have heD : e ∈ D := (hTB i (a i) (hB i) e heT heB).2 hc
          exact (h₂ ⟨he, heD⟩).1
        · exact (key e heT).2 he
      have hf₁ : HasInnerFence ω₁ false z r M K (γ i) :=
        hfi.of_cond_subset (dualConfig_anti hsub)
      refine (hasInnerFence_iff_of_inter_eq_of_le hKM subset_rfl ?_).1 hf₁
      rw [hω₁, inter_assoc, inter_self]
    · rw [hc] at hfi
      set ω₀ := ω ∩ {e | ∀ v ∈ e, v ∈ Bx} with hω₀
      have hsub : ω₀ ⊆ ω' := by
        rintro e ⟨he, heB⟩
        by_cases heT : e ∈ T
        · have heD : e ∉ D := fun h => by
            have := (hTB i (a i) (hB i) e heT heB).1 h
            simp [hc] at this
          exact (h₁ ⟨he, heD⟩).1
        · exact (key e heT).1 he
      have hf₀ : HasInnerFence ω₀ true z r M K (γ i) := by
        refine (hasInnerFence_iff_of_inter_eq_of_le hKM subset_rfl ?_).1 hfi
        rw [hω₀, inter_assoc, inter_self]
      exact hf₀.of_cond_subset hsub

/-- **Measurability** of the event of arms separated at the inner boundary with confined starts. -/
theorem measurableSet_setOf_innerSeparated_forall_mem (σ : Fin j → Bool) (z : LatticeSite 2)
    (r : ℕ) (lo hi : LatticeSite 2) (s : ℝ) (M K : ℕ) (B : Fin j → Set (LatticeSite 2)) :
    MeasurableSet {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
        (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))) ∧
      ArmsInnerSeparated ω σ z r s M K γ ∧ ∀ i, a i ∈ B i} := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  have hsep : Measurable fun ω => ArmsInnerSeparated ω σ z r s M K γ :=
    measurable_const.and (measurable_const.and (Measurable.forall fun i =>
      measurableSet_setOfPred.1 (measurableSet_setOf_hasInnerFence _ z r M K (γ i))))
  exact (Measurable.forall fun i => measurableSet_setOfPred.1
    (measurableSet_setOf_isArm _ z r _ _ (γ i))).and (measurable_const.and (measurable_const.and
      (hsep.and measurable_const)))

end Conditioning

/-! ### Determination and independence -/

section Determination

variable {j : ℕ} {σ : Fin j → Bool} {s : ℝ} {M K : ℕ} {ω' : Config (LatticeSite 2)}

/-- **Arms separated at the outer boundary are determined by a box** (one family of arms). For
`r < R`, a family of arms of `ω` from `B_r(z)` to the boundary of `B_R(z)`, separated at the outer
boundary, is such a family of arms of every `ω'` that agrees with `ω` on the pairs with both ends in
a set containing `B_{R + M + K + 1}(z)`. -/
theorem outerSeparated_of_inter_eq {R : ℕ} (hrR : r < R) {T : Set (LatticeSite 2)}
    (hT : Icc (z - ((R + M + K + 1 : ℕ) : LatticeSite 2))
      (z + ((R + M + K + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i))
    (hsep : ArmsOuterSeparated ω σ z R s M K γ) :
    (∀ i, IsArm ω' (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsOuterSeparated ω' σ z R s M K γ := by
  obtain ⟨hs₁, hs₂, hfen⟩ := hsep
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) := by
    refine Icc_subset_Icc ?_ ?_ <;> intro i <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] <;> omega
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc (z - R) (z + R)) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω') := by
    intro e _ he _
    have heT : e ∈ {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ T} := fun v hv => hT (by
      have hv' := he v hv
      rw [mem_Icc_two_iff] at hv' ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv' ⊢
      push_cast
      omega)
    have hmem := Set.ext_iff.1 h e
    exact ⟨fun h' => (hmem.1 ⟨h', heT⟩).1, fun h' => (hmem.2 ⟨h', heT⟩).1⟩
  refine ⟨fun i => (hγ i).of_agree hagree, hs₁, hs₂, fun i =>
    (hasOuterFence_iff_of_inter_eq (fun w hw => hT ?_) h).1 (hfen i)⟩
  have hb := (hγ i).end_mem_Icc hB
  rw [mem_Icc_two_iff] at hb hw ⊢
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hb hw ⊢
  push_cast at hw ⊢
  omega

/-- **Arms separated at the inner boundary are determined from outside** (one family of arms). For
`ρ + M + K + 1 < r`, a family of arms of `ω` from `B_r(z)` (to the boundary of any box), separated
at the inner boundary, is such a family of arms of every `ω'` that agrees with `ω` on the pairs with
both ends in a set `T` containing every point outside `B_ρ(z)`: the arms use only pairs with an
end outside `B_r(z)`, and the inner fences lie in boxes of radius `M + K + 1` about the starts. -/
theorem innerSeparated_of_inter_eq_compl {ρ : ℕ} (hρ : ρ + M + K + 1 < r)
    {T : Set (LatticeSite 2)} (hT : ∀ v, v ∉ Icc (z - (ρ : LatticeSite 2)) (z + ρ) → v ∈ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) {lo hi : LatticeSite 2}
    {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hsep : ArmsInnerSeparated ω σ z r s M K γ) :
    (∀ i, IsArm ω' (σ i) z r lo hi (γ i)) ∧ ArmsInnerSeparated ω' σ z r s M K γ := by
  obtain ⟨hs₁, hs₂, hfen⟩ := hsep
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, v ∈ Icc lo hi) →
      (∃ v ∈ e, v ∉ Icc (z - r) (z + r)) → (e ∈ ω ↔ e ∈ ω') := by
    intro e he _ ⟨w, hw, hwr⟩
    have heT : e ∈ {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ T} := by
      intro v hv
      refine hT v fun hvρ => hwr ?_
      induction e using Sym2.ind with
      | h u u' =>
        have hadj : (zdGraph 2).Adj u u' := he
        rw [zdGraph_two_adj_iff] at hadj
        rw [mem_Icc_two_iff] at hvρ ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hvρ ⊢
        rcases Sym2.mem_iff.1 hv with rfl | rfl <;> rcases Sym2.mem_iff.1 hw with rfl | rfl <;>
          omega
    have hmem := Set.ext_iff.1 h e
    exact ⟨fun h' => (hmem.1 ⟨h', heT⟩).1, fun h' => (hmem.2 ⟨h', heT⟩).1⟩
  refine ⟨fun i => (hγ i).of_agree hagree, hs₁, hs₂, fun i =>
    (hasInnerFence_iff_of_inter_eq (fun w hw => hT w ?_) h).1 (hfen i)⟩
  have hside := (hfen i).side
  have hc : cond (σ i) (0 : ℤ) 1 = 0 ∨ cond (σ i) (0 : ℤ) 1 = 1 := by cases σ i <;> simp
  intro hwρ
  rw [mem_Icc_two_iff] at hw hwρ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hw hwρ
  push_cast at hw
  omega

/-- **Independence of the two families.** For `r < R` and `R + M + K + 1 + M' + K' + 1 < R'`, the
event of arms from `B_r(z)` to the boundary of `B_R(z)` separated at the outer boundary, with ends
in sets `B i` and inner positions in sets `J i`, and the event of arms from `B_{R'}(z)` to the
boundary of any box separated at the inner boundary, with starts in sets `B' i`, are independent:
the first is determined by the pairs inside `B_{R + M + K + 1}(z)`, the second by the pairs outside
it. -/
theorem law_inter_eq_mul_of_separated (q : Sym2 (LatticeSite 2) → unitInterval) {R R' : ℕ}
    {s' : ℝ} {M' K' : ℕ} (hrR : r < R) (hRR' : R + M + K + 1 + M' + K' + 1 < R')
    {lo hi : LatticeSite 2} (B B' : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ) :
    law q ({ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ∩
    {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z R' lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
        (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))) ∧
      ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ B' i}) =
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} *
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z R' lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
        (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))) ∧
      ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ B' i} := by
  set ρ : ℕ := R + M + K + 1 with hρ
  set P : Set (Sym2 (LatticeSite 2)) :=
    {e | ∀ v ∈ e, v ∈ Icc (z - (ρ : LatticeSite 2)) (z + ρ)} with hP
  set Q : Set (Sym2 (LatticeSite 2)) :=
    {e | ∀ v ∈ e, v ∈ (Icc (z - (ρ : LatticeSite 2)) (z + ρ))ᶜ} with hQ
  have hPQ : Disjoint P Q := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact he' v hv (he v hv)
  refine PercLib.Probability.prodBernoulli_inter_of_determined q hPQ
    (measurableSet_setOf_separated_forall_mem_innerPos σ z r R s M K B J)
    (measurableSet_setOf_innerSeparated_forall_mem σ z R' lo hi s' M' K' B') ?_ ?_
  · suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2), ω₁ ∩ P = ω₂ ∩ P →
        ω₁ ∈ {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
            (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i} →
        ω₂ ∈ {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
            (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i} from
      fun ω₁ ω₂ h => ⟨key ω₁ ω₂ h, key ω₂ ω₁ h.symm⟩
    rintro ω₁ ω₂ h ⟨a, b, γ, hγ, hd, ho, hsep, hB, hJ⟩
    obtain ⟨hγ', hsep'⟩ := outerSeparated_of_inter_eq hrR subset_rfl h hγ hsep
    exact ⟨a, b, γ, hγ', hd, ho, hsep', hB, hJ⟩
  · suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2), ω₁ ∩ Q = ω₂ ∩ Q →
        ω₁ ∈ {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z R' lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
            (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))) ∧
          ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ B' i} →
        ω₂ ∈ {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z R' lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
            (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))) ∧
          ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ B' i} from
      fun ω₁ ω₂ h => ⟨key ω₁ ω₂ h, key ω₂ ω₁ h.symm⟩
    rintro ω₁ ω₂ h ⟨a, b, γ, hγ, hd, ho, hsep, hB⟩
    obtain ⟨hγ', hsep'⟩ := innerSeparated_of_inter_eq_compl (ρ := ρ) (by omega)
      (fun v hv => hv) h hγ hsep
    exact ⟨a, b, γ, hγ', hd, ho, hsep', hB⟩

end Determination

/-! ### Positions at the inner boundary -/

section Positions

variable {lo hi a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **The first step of an arm.** The second vertex (face) of an arm from `B_r(z)` is a neighbour
of the first, which lies in the start box `[z - r - [c = dual], z + r]²`, and lies outside that
box. -/
theorem IsArm.snd_mem {c : Bool} (h : IsArm ω c z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) :
    (γ.snd 0 = a 0 ∧ (a 1 + 1 = γ.snd 1 ∨ γ.snd 1 + 1 = a 1) ∨
      γ.snd 1 = a 1 ∧ (a 0 + 1 = γ.snd 0 ∨ γ.snd 0 + 1 = a 0)) ∧
    z 0 - r - cond c 0 1 ≤ a 0 ∧ a 0 ≤ z 0 + r ∧ z 1 - r - cond c 0 1 ≤ a 1 ∧ a 1 ≤ z 1 + r ∧
    ¬(z 0 - r - cond c 0 1 ≤ γ.snd 0 ∧ γ.snd 0 ≤ z 0 + r ∧ z 1 - r - cond c 0 1 ≤ γ.snd 1 ∧
      γ.snd 1 ≤ z 1 + r) := by
  have hne := h.not_nil hB
  have hadj := (zdGraph_two_adj_iff _ _).1 (γ.adj_snd hne)
  obtain ⟨hcr, -⟩ := isArm_iff_cond.1 h
  have ha := hcr.start_mem
  have hs := hcr.notMem_of_mem_tail _ (γ.snd_mem_tail_support hne)
  refine ⟨by omega, ?_⟩
  cases c <;> simp only [Bool.cond_true, Bool.cond_false] at ha hs ⊢ <;>
    rw [mem_Icc_two_iff] at ha hs <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at ha hs <;> omega

/-- **Inner positions on the four sides.** The inner position of an arm of colour `c` from
`B_r(z)` (on the doubled lattice, where the boundary of `2z + [-(2r + 1), 2r + 1]²` has perimeter
`16r + 8` and corners at the multiples of `4r + 2`) is `10r + 5 + 2z₀ - (2a₀ + [c = dual])` when
the arm starts on the top side, `6r + 3 + (2a₁ + [c = dual]) - 2z₁` on the right side,
`(2a₀ + [c = dual]) - 2z₀ + 2r + 1` on the bottom side and `14r + 7 + 2z₁ - (2a₁ + [c = dual])` on
the left side, where `a` is its first vertex (face). -/
theorem IsArm.innerPos_cases {c : Bool} (h : IsArm ω c z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) :
    (z 0 - r - cond c 0 1 ≤ a 0 ∧ a 0 ≤ z 0 + r ∧ z 1 - r - cond c 0 1 ≤ a 1 ∧ a 1 ≤ z 1 + r) ∧
    ((a 1 = z 1 + r ∧ innerPos z r c γ = 10 * r + 5 + 2 * z 0 - (2 * a 0 + cond c 0 1)) ∨
      (a 0 = z 0 + r ∧ innerPos z r c γ = 6 * r + 3 + (2 * a 1 + cond c 0 1) - 2 * z 1) ∨
      (a 1 = z 1 - r - cond c 0 1 ∧
        innerPos z r c γ = 2 * a 0 + cond c 0 1 - 2 * z 0 + 2 * r + 1) ∨
      (a 0 = z 0 - r - cond c 0 1 ∧
        innerPos z r c γ = 14 * r + 7 + 2 * z 1 - (2 * a 1 + cond c 0 1))) := by
  obtain ⟨hadj, h₁, h₂, h₃, h₄, hout⟩ := h.snd_mem hB
  refine ⟨⟨h₁, h₂, h₃, h₄⟩, ?_⟩
  cases c
  · simp only [Bool.cond_false] at h₁ h₂ h₃ h₄ hout ⊢
    rw [innerPos_false]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
    push_cast
    -- the corner face at the lower left corner has position `0`, on the bottom side
    by_cases hcor : a 1 = z 1 - r - 1 <;>
    rcases hadj with ⟨h0, h1 | h1⟩ | ⟨h0, h1 | h1⟩ <;>
    first
    | (exfalso; omega)
    | exact Or.inr (Or.inr (Or.inl ⟨by omega, by split_ifs <;> omega⟩))
    | exact Or.inl ⟨by omega, by split_ifs <;> omega⟩
    | exact Or.inr (Or.inl ⟨by omega, by split_ifs <;> omega⟩)
    | exact Or.inr (Or.inr (Or.inr ⟨by omega, by split_ifs <;> omega⟩))
  · simp only [Bool.cond_true, sub_zero, add_zero] at h₁ h₂ h₃ h₄ hout ⊢
    rw [innerPos_true]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply]
    push_cast
    rcases hadj with ⟨h0, h1 | h1⟩ | ⟨h0, h1 | h1⟩ <;>
    first
    | exact Or.inl ⟨by omega, by split_ifs <;> omega⟩
    | exact Or.inr (Or.inl ⟨by omega, by split_ifs <;> omega⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by omega, by split_ifs <;> omega⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by omega, by split_ifs <;> omega⟩))

/-- **Arms starting near each other have nearby inner positions**, away from the corners. Two arms
of one colour from `B_r(z)` whose starts are within sup-distance `M` of each other have inner
positions within `2M` of each other (on the doubled lattice), when the second lies more than
`2M + 1` from every doubled corner `m (4r + 2)` of the inner box. -/
theorem abs_innerPos_sub_le {c : Bool} {M : ℕ} {ω₁ ω₂ : Config (LatticeSite 2)}
    {lo₁ hi₁ lo₂ hi₂ a₁ e₁ a₂ e₂ : LatticeSite 2} {W₁ : (zdGraph 2).Walk a₁ e₁}
    {W₂ : (zdGraph 2).Walk a₂ e₂} (h₁ : IsArm ω₁ c z r lo₁ hi₁ W₁) (h₂ : IsArm ω₂ c z r lo₂ hi₂ W₂)
    (hB₁ : Icc (z - r) (z + r) ⊆ Icc (lo₁ + 1) (hi₁ - 1))
    (hB₂ : Icc (z - r) (z + r) ⊆ Icc (lo₂ + 1) (hi₂ - 1))
    (ha : a₁ ∈ Icc (a₂ - (M : LatticeSite 2)) (a₂ + M))
    (hc : ∀ m : ℕ, 2 * (M : ℤ) + 1 < |innerPos z r c W₂ - m * (4 * r + 2)|) :
    |innerPos z r c W₁ - innerPos z r c W₂| ≤ 2 * M := by
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  have c4 := hc 4
  push_cast at c0 c1 c2 c3 c4
  rw [lt_abs] at c0 c1 c2 c3 c4
  rw [mem_Icc_two_iff] at ha
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at ha
  rw [abs_le]
  obtain ⟨f₁, g₁⟩ := h₁.innerPos_cases hB₁
  obtain ⟨f₂, g₂⟩ := h₂.innerPos_cases hB₂
  have hδ : cond c (0 : ℤ) 1 = 0 ∨ cond c (0 : ℤ) 1 = 1 := by cases c <;> simp
  rcases g₁ with ⟨s₁, p₁⟩ | ⟨s₁, p₁⟩ | ⟨s₁, p₁⟩ | ⟨s₁, p₁⟩ <;>
    rcases g₂ with ⟨s₂, p₂⟩ | ⟨s₂, p₂⟩ | ⟨s₂, p₂⟩ | ⟨s₂, p₂⟩ <;> omega

end Positions

/-! ### Sectors read at the inner boundary -/

section Sectors

variable {j : ℕ} {σ : Fin j → Bool} {lo hi : LatticeSite 2} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **Order invariance for one more arm.** Let `γ` be a disjoint family of arms, `k ≠ l` two of its
arms of one colour, and `W` an arm of the other colour. The inner positions of `W`, `γ k`, `γ l`
are in the same cyclic order as their landing positions. -/
theorem sbtw_innerPos_iff_sbtw_landingPos_of_isArm
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ) {k l : Fin j} (hkl : k ≠ l)
    (hσkl : σ k = σ l) {c : Bool} (hc : c ≠ σ k) {a₀ b₀ : LatticeSite 2}
    {W : (zdGraph 2).Walk a₀ b₀} (hW : IsArm ω c z r lo hi W) :
    sbtw (innerPos z r c W) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) ↔
      sbtw (landingPos lo hi c W) (landingPos lo hi (σ k) (γ k))
        (landingPos lo hi (σ l) (γ l)) := by
  let A : Fin 3 → LatticeSite 2 := ![a₀, a k, a l]
  let B : Fin 3 → LatticeSite 2 := ![b₀, b k, b l]
  let F : ∀ t, (zdGraph 2).Walk (A t) (B t) :=
    @Fin.cases 2 (fun t => (zdGraph 2).Walk (A t) (B t)) W
      (@Fin.cases 1 (fun t => (zdGraph 2).Walk (A t.succ) (B t.succ)) (γ k)
        (@Fin.cases 0 (fun t => (zdGraph 2).Walk (A t.succ.succ) (B t.succ.succ)) (γ l)
          fun t => t.elim0))
  have hF : ∀ t, IsArm ω (![c, σ k, σ l] t) z r lo hi (F t) := by
    intro t
    fin_cases t
    · exact hW
    · exact hγ k
    · exact hγ l
  have hlk : σ l ≠ c := fun h => hc (h ▸ hσkl).symm
  have hdF : ArmsDisjoint ![c, σ k, σ l] F := by
    refine ⟨fun t u htu ht hu v hv hv' => ?_, fun t u htu ht hu v hv hv' => ?_⟩
    · fin_cases t <;> fin_cases u
      · exact htu rfl
      · exact hc (ht.trans hu.symm)
      · exact hlk (hu.trans ht.symm)
      · exact hc (hu.trans ht.symm)
      · exact htu rfl
      · exact hd.1 k l hkl ht hu v hv hv'
      · exact hlk (ht.trans hu.symm)
      · exact hd.1 l k hkl.symm ht hu v hv hv'
      · exact htu rfl
    · fin_cases t <;> fin_cases u
      · exact htu rfl
      · exact hc (ht.trans hu.symm)
      · exact hlk (hu.trans ht.symm)
      · exact hc (hu.trans ht.symm)
      · exact htu rfl
      · exact hd.2 k l hkl ht hu v hv hv'
      · exact hlk (ht.trans hu.symm)
      · exact hd.2 l k hkl.symm ht hu v hv hv'
      · exact htu rfl
  exact sbtw_innerPos_iff_sbtw_landingPos hB hF hdF 0 1 2

/-- **Sectors at the inner boundary** (the mirror of `sbtw_landingPos_iff_of_innerPos_eq`). Let `γ`
be a disjoint family of arms and `k ≠ l` two of its arms of one colour. Two arms of the other colour
with the same landing position start on the same side of the arms `k` and `l`: their inner
positions and those of `γ k`, `γ l` are in the same cyclic order. -/
theorem sbtw_innerPos_iff_of_landingPos_eq (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ) {k l : Fin j} (hkl : k ≠ l)
    (hσkl : σ k = σ l) {c : Bool} (hc : c ≠ σ k) {a₁ b₁ a₂ b₂ : LatticeSite 2}
    {W₁ : (zdGraph 2).Walk a₁ b₁} {W₂ : (zdGraph 2).Walk a₂ b₂} (h₁ : IsArm ω c z r lo hi W₁)
    (h₂ : IsArm ω c z r lo hi W₂) (hland : landingPos lo hi c W₁ = landingPos lo hi c W₂) :
    sbtw (innerPos z r c W₁) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) ↔
      sbtw (innerPos z r c W₂) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) := by
  rw [sbtw_innerPos_iff_sbtw_landingPos_of_isArm hB hγ hd hkl hσkl hc h₁,
    sbtw_innerPos_iff_sbtw_landingPos_of_isArm hB hγ hd hkl hσkl hc h₂, hland]

/-- **An arm stays in its sector, read at the inner boundary** (the mirror of
`false_of_innerPos_eq_of_abs_lt`). Let `γ` be a disjoint family of arms landing in counterclockwise
order, without packs, and `i ≠ k` two arms of one colour. An arm landing where `γ k` lands cannot
start closer to `γ i` (in inner position) than every arm of the other colour does. -/
theorem false_of_landingPos_eq_of_abs_lt (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
      (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l)))
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) {a' b' : LatticeSite 2}
    {W : (zdGraph 2).Walk a' b'} (hW : IsArm ω (σ i) z r lo hi W)
    (hland : landingPos lo hi (σ i) W = landingPos lo hi (σ k) (γ k))
    (hnear : ∀ l, σ l ≠ σ i → |innerPos z r (σ i) W - innerPos z r (σ i) (γ i)| <
      |innerPos z r (σ l) (γ l) - innerPos z r (σ i) (γ i)|) : False := by
  rcases hσ with hj | hσ
  · exact hik (Fin.ext (by omega))
  set f : Fin j → ℤ := fun i => innerPos z r (σ i) (γ i) with hf
  have hof : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l) := fun i k l h₁ h₂ =>
    (sbtw_innerPos_iff_sbtw_landingPos hB hγ hd i k l).2 (ho i k l h₁ h₂)
  set l₁ := finRotate j i with hl₁
  set l₂ := finRotate j k with hl₂
  have h₁ : σ l₁ ≠ σ i := (hσ i).symm
  have h₂ : σ l₂ ≠ σ i := fun h => hσ k (h.trans hσik).symm
  have h₁₂ : l₁ ≠ l₂ := fun h => hik ((finRotate j).injective h)
  have hσ₁₂ : σ l₁ = σ l₂ := by
    revert h₁ h₂
    generalize σ l₁ = x
    generalize σ l₂ = y
    generalize σ i = w
    cases x <;> cases y <;> cases w <;> simp
  have hl₂i : l₂ ≠ i := fun h => h₂ (congrArg σ h)
  have hl₁k : l₁ ≠ k := fun h => h₁ ((congrArg σ h).trans hσik.symm)
  have s₁ : sbtw (f i) (f l₁) (f l₂) := sbtw_apply_finRotate_apply hof hl₂i h₁₂.symm
  have s₂ : sbtw (f k) (f l₂) (f l₁) := sbtw_apply_finRotate_apply hof hl₁k h₁₂
  have s₃ : ¬sbtw (f k) (f l₁) (f l₂) := fun h => sbtw_asymm h (sbtw_cyclic_left s₂)
  have hn₁ := hnear l₁ h₁
  have hn₂ := hnear l₂ h₂
  have s₄ : sbtw (innerPos z r (σ i) W) (f l₁) (f l₂) := (sbtw_iff_of_abs_sub_lt hn₁ hn₂).2 s₁
  have hγk : IsArm ω (σ i) z r lo hi (γ k) := hσik ▸ hγ k
  have hsec := sbtw_innerPos_iff_of_landingPos_eq hB hγ hd h₁₂ hσ₁₂ h₁.symm hW hγk
    (by rw [hland, hσik])
  have : sbtw (innerPos z r (σ i) (γ k)) (f l₁) (f l₂) := hsec.1 s₄
  rw [hσik] at this
  exact s₃ this

end Sectors

/-! ### Walk helpers -/

section WalkHelpers

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex of a joined walk other than its last is a vertex of the first walk or a vertex of
the second walk other than its last. -/
theorem _root_.SimpleGraph.Walk.mem_support_dropLast_append {u x v : V} {p : G.Walk u x}
    {q : G.Walk x v} {w : V} (hw : w ∈ (p.append q).support.dropLast) :
    w ∈ p.support ∨ w ∈ q.support.dropLast := by
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
    List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil q), List.mem_append] at hw
  exact hw.imp List.mem_of_mem_dropLast id

/-- A vertex of the second walk other than its last is a vertex of the joined walk other than
its last. -/
theorem _root_.SimpleGraph.Walk.mem_support_dropLast_append_of_right {u x v : V}
    (p : G.Walk u x) {q : G.Walk x v} {w : V} (hw : w ∈ q.support.dropLast) :
    w ∈ (p.append q).support.dropLast := by
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
    List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil q)]
  exact List.mem_append_right _ hw

end WalkHelpers

/-! ### The barrier at the inner boundary -/

/-- The box of radius `M` about a point of `Icc (z - r - 1) (z + r)` lies in the interior of
`B_{R₃}(z)` (in its faces, for the dual colour) when `r + M + 1 < R₃`. -/
theorem Icc_sub_add_subset_cond_Icc {c : Bool} {M R₃ : ℕ} {a : LatticeSite 2}
    (ha : a ∈ Icc (z - (r : LatticeSite 2) - 1) (z + r)) (h : r + M + 1 < R₃) :
    Icc (a - (M : LatticeSite 2)) (a + M) ⊆ cond c (Icc (z - (R₃ : LatticeSite 2) + 1)
      (z + R₃ - 1)) (Icc (z - (R₃ : LatticeSite 2)) (z + R₃ - 1)) := by
  intro w hw
  rw [mem_Icc_two_iff] at ha hw
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at ha hw
  cases c <;> simp only [Bool.cond_true, Bool.cond_false] <;> rw [mem_Icc_two_iff] <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] <;> omega

section Barrier

variable {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **The barrier at the inner boundary** (the mirror of `notMem_support_of_mem_Icc`). Let `γ` be a
disjoint family of arms from `B_r(z)` to the boundary of `B_{R₃}(z)`, landing in counterclockwise
order, without packs, with inner positions more than `2M` apart and more than `2M + 1` from the
doubled corners of the inner box, and `r + M + 1 < R₃`. Let `P` be a walk of the colour of arm `i`,
starting at a vertex (face) of arm `i`, all of whose points lie within sup-distance `M` of the start
of arm `i`. Then `P` meets no other arm of the colour of `i`. -/
theorem notMem_support_of_subset_Icc_start (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    {M R₃ : ℕ} (hrM : r + M + 1 < R₃) (hγ : ∀ i, IsArm ω (σ i) z r (z - R₃) (z + R₃) (γ i))
    (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
      (landingPos (z - R₃) (z + R₃) (σ k) (γ k)) (landingPos (z - R₃) (z + R₃) (σ l) (γ l)))
    (hsep : ∀ i k, i ≠ k → 2 * (M : ℤ) < |innerPos z r (σ i) (γ i) - innerPos z r (σ k) (γ k)|)
    (hcor : ∀ i (m : ℕ), 2 * (M : ℤ) + 1 < |innerPos z r (σ i) (γ i) - m * (4 * r + 2)|)
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) {x y : LatticeSite 2}
    (P : (zdGraph 2).Walk x y) (hx : x ∈ (γ i).support)
    (hP : ∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω))
    (hloc : ∀ v ∈ P.support, v ∈ Icc (a i - (M : LatticeSite 2)) (a i + M)) :
    ∀ v ∈ P.support, v ∉ (γ k).support := by
  intro v hvP hvk
  have hrR : r < R₃ := by omega
  have hB := Icc_subset_Icc_add_one_sub_one (z := z) hrR
  obtain ⟨hcri, hEi⟩ := isArm_iff_cond.1 (hγ i)
  have hγk : IsArm ω (σ i) z r (z - R₃) (z + R₃) (γ k) := hσik ▸ hγ k
  obtain ⟨hcrk, hEk⟩ := isArm_iff_cond.1 hγk
  have hboxT := Icc_sub_add_subset_cond_Icc (c := σ i) (hγ i).start_mem_Icc hrM
  have hST := cond_Icc_subset_cond_Icc (c := σ i) (z := z) hrR
  -- split the arms and the walk
  obtain ⟨q', s', hq's'⟩ : ∃ (q' : (zdGraph 2).Walk (a i) x) (s' : (zdGraph 2).Walk x (b i)),
      q'.append s' = γ i := ⟨_, _, SimpleGraph.Walk.take_spec _ hx⟩
  obtain ⟨P₁, P₂, hP₁₂⟩ : ∃ (P₁ : (zdGraph 2).Walk x v) (P₂ : (zdGraph 2).Walk v y),
      P₁.append P₂ = P := ⟨_, _, SimpleGraph.Walk.take_spec _ hvP⟩
  obtain ⟨Qk, Sk, hQS⟩ : ∃ (Qk : (zdGraph 2).Walk (a k) v) (Sk : (zdGraph 2).Walk v (b k)),
      Qk.append Sk = γ k := ⟨_, _, SimpleGraph.Walk.take_spec _ hvk⟩
  have hP₁ : ∀ w ∈ P₁.support, w ∈ P.support := fun w hw => by
    rw [← hP₁₂, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  -- the walk from the start of arm `i` to the end of arm `k`
  set W := q'.append (P₁.append Sk) with hW
  have hWE : ∀ e ∈ W.edges, e ∈ cond (σ i) ω (dualConfig ω) := by
    intro e he
    rw [hW, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append, List.mem_append,
      List.mem_append] at he
    rcases he with he | he | he
    · refine hEi e ?_
      rw [← hq's', SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    · refine hP e ?_
      rw [← hP₁₂, SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    · refine hEk e ?_
      rw [← hQS, SimpleGraph.Walk.edges_append]
      exact List.mem_append_right _ he
  -- its last visit to the start box
  obtain ⟨e, heS, W₁, A, hW₁A, hAt⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem W
    ⟨a i, W.start_mem_support, hcri.start_mem⟩
  -- that visit is next to the start of arm `i`
  have heM : e ∈ Icc (a i - (M : LatticeSite 2)) (a i + M) := by
    have heW : e ∈ W.support := by
      rw [← hW₁A, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr A.start_mem_support
    rw [hW, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff] at heW
    rcases heW with h | h | h
    · have h' : e ∈ (γ i).support := by
        rw [← hq's', SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl h
      rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at h'
      rcases h' with rfl | h'
      · rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
        omega
      · exact absurd heS (hcri.notMem_of_mem_tail _ h')
    · exact hloc e (hP₁ e h)
    · rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at h
      rcases h with rfl | h
      · exact hloc _ hvP
      · refine absurd heS (hcrk.notMem_of_mem_tail _ ?_)
        rw [← hQS, SimpleGraph.Walk.tail_support_append]
        exact List.mem_append_right _ h
  -- the last part is an arm
  have hAcr : A.IsCrossing (cond (σ i) (Icc (z - (r : LatticeSite 2)) (z + r))
      (Icc (z - (r : LatticeSite 2) - 1) (z + r)))
      (cond (σ i) (Icc (z - (R₃ : LatticeSite 2) + 1) (z + R₃ - 1))
        (Icc (z - (R₃ : LatticeSite 2)) (z + R₃ - 1))) := by
    refine ⟨heS, hAt, hcrk.end_notMem, fun w hw => ?_⟩
    have hw' : w ∈ W.support.dropLast := by
      rw [← hW₁A]
      exact SimpleGraph.Walk.mem_support_dropLast_append_of_right W₁ hw
    rw [hW] at hw'
    rcases SimpleGraph.Walk.mem_support_dropLast_append hw' with h | h
    · by_contra hwT
      have hwx : w = x := by
        rw [← hq's'] at hcri
        exact hcri.eq_of_mem_support_left h hwT
      exact hwT (hboxT (hwx ▸ hloc x P.start_mem_support))
    · rcases SimpleGraph.Walk.mem_support_dropLast_append h with h | h
      · exact hboxT (hloc w (hP₁ w h))
      · refine hcrk.mem_of_mem_dropLast w ?_
        rw [← hQS]
        exact SimpleGraph.Walk.mem_support_dropLast_append_of_right Qk h
  have hAarm : IsArm ω (σ i) z r (z - R₃) (z + R₃) A := isArm_iff_cond.2 ⟨hAcr, fun e' he' =>
    hWE e' (by rw [← hW₁A, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ he')⟩
  -- it lands where arm `k` lands
  have hAnil : ¬A.Nil := fun h => hcrk.end_notMem (h.eq ▸ hST heS)
  have hSknil : ¬Sk.Nil := fun h => hcrk.end_notMem (h.eq ▸ hboxT (hloc v hvP))
  have hland : landingPos (z - R₃) (z + R₃) (σ i) A =
      landingPos (z - R₃) (z + R₃) (σ k) (γ k) := by
    have hW' : W = (q'.append P₁).append Sk := by
      rw [hW, SimpleGraph.Walk.append_assoc]
    calc landingPos (z - R₃) (z + R₃) (σ i) A
        = landingPos (z - R₃) (z + R₃) (σ i) (W₁.append A) := (landingPos_append W₁ hAnil).symm
      _ = landingPos (z - R₃) (z + R₃) (σ i) Sk := by
          rw [hW₁A, hW', landingPos_append _ hSknil]
      _ = landingPos (z - R₃) (z + R₃) (σ i) (γ k) := by
          rw [← hQS, landingPos_append _ hSknil]
      _ = landingPos (z - R₃) (z + R₃) (σ k) (γ k) := by rw [hσik]
  -- and starts next to arm `i`: a contradiction with the sectors
  have hnear := abs_innerPos_sub_le hAarm (hγ i) hB hB heM (hcor i)
  refine false_of_landingPos_eq_of_abs_lt hσ hB hγ hd ho hik hσik hAarm hland fun l hl => ?_
  exact lt_of_le_of_lt hnear (hsep l i fun h => hl (h ▸ rfl))

end Barrier

end PercLib.Models.Planar
