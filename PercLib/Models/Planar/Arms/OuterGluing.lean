/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-23. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12, and
Lemma 13).
-/
module

public import PercLib.Models.Planar.Arms.OuterSeparation
public import PercLib.Probability.MixedHarris

/-!
# Gluing separated arms: conditioning and the sectors beyond the boundary

Arms separated at the outer boundary of `B_R(z)` (`outerSeparatedArmEvent`) carry fences next to
their ends. Nolin's gluing extends them outwards: for each arm a corridor of its colour starts at
the fence and runs out to a larger box, and on the event that all corridors are crossed the
extended arms form a multi-arm event of the larger box. This file proves the two parts of the
gluing that do not depend on the shape of the corridors.

* **Conditioning.** The separated event is not monotone, but once the ends of the arms are confined
  to fixed sets `B i`, it is upper for the mixed order (increasing in the open corridors, decreasing
  in the dual corridors) among the configurations that agree off the corridors, provided the
  corridors avoid the interior of `B_R(z)` and, for fences of length `2K ≤ 2M`, the corridors of
  one colour avoid the boxes of radius `M + 1` about the possible ends of the arms of the other
  colour. By Harris for a mixed
  order (conditional form, `prodBernoulli_mul_le_inter_of_mixed_of_determined`) it is then
  positively correlated with every event determined by the corridors and upper for the mixed
  order, such as the crossings of the corridors.
* **Sectors beyond the boundary** (the fence-connection argument). Without packs, a walk of the
  colour of arm `i` that starts on arm `i` near its end, and meets `B_R(z)` only near the end of
  arm `i`, cannot meet another arm `k` of that colour: otherwise arm `k` up to the meeting point,
  followed by the walk backwards, is an arm with the inner position of arm `k` landing next to arm
  `i`, in the sector of `i`, which the sector lemma forbids. The walk may leave `B_R(z)` and come
  back; only its points in the box `B_{R+1}(z)` (in the faces version, `Icc (z - R - 1) (z + R)`)
  must lie near the end of arm `i`.
* **Gluing.** Consequently, if each arm `i` is continued by a walk of its colour starting at one of
  its vertices near its end, meeting `B_{R+1}(z)` only near that end and ending outside a larger
  box `B_{R'}(z)`, and continuations of arms of one colour are disjoint, then cutting each glued
  walk where it first leaves the larger box gives a disjoint family of arms of the larger box with
  the old inner positions, landing in the old cyclic order.

## Main results

* `HasOuterFence.of_cond_subset`: a fence survives when its colour's configuration grows;
  `hasOuterFence_iff_of_inter_eq_of_le`: for `K ≤ M` a fence is determined by the box of radius
  `M + 1` about the end.
* `IsDualArm.exists_mem_or_forall_mem_Icc`, `IsOpenArm.exists_mem_Icc_of_mem_edges`: arms use
  (cross) only edges with an end inside the box, except at the last dual edge.
* `separated_of_mixed_of_forall_mem` (one family of arms) and `mem_of_mixed_of_forall_mem` (the
  event): the separated event with confined ends is upper for the mixed order off the corridors;
  `law_mul_le_law_inter_of_mixed`: its positive correlation with the corridor events (conditioning
  on the separated event).
* `abs_landingPos_sub_le`: arms ending near each other, away from the corners, land near each
  other.
* `false_of_innerPos_eq_of_abs_lt`: an arm with the inner position of arm `k` cannot land closer to
  arm `i` of the same colour than every arm of the other colour;
  `two_mul_le_abs_landingPos_sub`: arms of one colour land at least twice the separation apart.
* `notMem_support_of_mem_Icc`: the fence-connection argument.
* `exists_isArm_of_glue`: the gluing, for continuations of any shape.

## Implementation notes

* The corridors themselves (their shape, the bins for the ends, their crossing probabilities) are
  not in this file: `exists_isArm_of_glue` takes the continuations as walks with three geometric
  properties, and `law_mul_le_law_inter_of_mixed` takes the corridor event as any measurable event
  determined by the corridors and upper for the mixed order.
* Separation is stated with integer bounds on landing positions (`2M < |L i - L k|`, and from the
  doubled corners), which the real separation `s` of `outerSeparatedArmEvent` gives when `2M < s`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ}

/-! ### Fences and arms under changes of the configuration -/

/-- **A fence survives when the configuration of its colour grows.** -/
theorem HasOuterFence.of_cond_subset {ω' : Config (LatticeSite 2)} {c : Bool} {R M K : ℕ}
    {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    (hωω' : cond c ω (dualConfig ω) ⊆ cond c ω' (dualConfig ω'))
    (h : HasOuterFence ω c z R M K γ) : HasOuterFence ω' c z R M K γ := by
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

/-- **Determination, sharp form.** When `K ≤ M`, whether an arm ending at `b` has an outer fence
of length `2K` and depth `M` depends only on the pairs with both ends in any set containing
`Icc (b - M) (b + (M + 1))`: the fence box lies in the box of radius `M` about `b`. -/
theorem hasOuterFence_iff_of_inter_eq_of_le {ω' : Config (LatticeSite 2)} {c : Bool} {R M K : ℕ}
    (hKM : K ≤ M) {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b} {T : Set (LatticeSite 2)}
    (hT : Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ T)
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    HasOuterFence ω c z R M K γ ↔ HasOuterFence ω' c z R M K γ := by
  suffices key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      ω₁ ∩ {e | ∀ v ∈ e, v ∈ T} = ω₂ ∩ {e | ∀ v ∈ e, v ∈ T} →
      HasOuterFence ω₁ c z R M K γ → HasOuterFence ω₂ c z R M K γ from
    ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω₁ ω₂ h₁₂ hf
  have hconn : ∀ p q : LatticeSite 2, (∀ w ∈ Icc p (q + 1), w ∈
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2))) →
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

/-- **Edges crossed by a dual arm.** Each edge crossed by a dual arm to the boundary of `B_R(z)`
has an end in the interior of `B_R(z)`, except the edge crossed by its last dual edge, whose ends
are corners of the last face `b`. -/
theorem IsDualArm.exists_mem_or_forall_mem_Icc {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsDualArm ω z r (z - R) (z + R) γ)
    {E : Sym2 (LatticeSite 2)} (hE : E ∈ γ.edges) {e : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) (hde : dualEdge e = E) :
    (∃ v ∈ e, v ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∨
      ∀ v ∈ e, v ∈ Icc b (b + 1) := by
  have hE' := hE
  unfold SimpleGraph.Walk.edges at hE'
  obtain ⟨δ, hδ, hδe⟩ := List.mem_map.1 hE'
  have hfst : δ.fst ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1) :=
    h.isCrossing.mem_of_mem_dropLast _ (by
      rw [← SimpleGraph.Walk.map_fst_darts]
      exact List.mem_map_of_mem hδ)
  have hsnd : δ.snd ∈ γ.support := γ.dart_snd_mem_support_of_mem_darts hδ
  have hfst' : δ.fst ∈ dualEdge e := by
    rw [hde, ← hδe, SimpleGraph.Dart.edge]
    exact Sym2.mem_mk_left _ _
  have hsnd' : δ.snd ∈ dualEdge e := by
    rw [hde, ← hδe, SimpleGraph.Dart.edge]
    exact Sym2.mem_mk_right _ _
  by_cases hs : δ.snd ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
  · left
    induction e using Sym2.ind with
    | h u w =>
      have huw : (zdGraph 2).Adj u w := he
      have hu₁ := mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_left u w) hfst'
      have hu₂ := mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_left u w) hsnd'
      have hw₁ := mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_right u w) hfst'
      have hw₂ := mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_right u w) hsnd'
      have hadj := (zdGraph_two_adj_iff _ _).1 δ.adj
      rw [zdGraph_two_adj_iff] at huw
      rw [mem_Icc_two_iff] at hu₁ hu₂ hw₁ hw₂ hfst hs
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hfst hs
      simp only [Pi.add_apply, Pi.one_apply] at hu₁ hu₂ hw₁ hw₂
      by_cases hu : u ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
      · exact ⟨u, Sym2.mem_mk_left u w, hu⟩
      · refine ⟨w, Sym2.mem_mk_right u w, ?_⟩
        rw [mem_Icc_two_iff] at hu ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hu ⊢
        omega
  · right
    have hb : δ.snd = b := h.isCrossing.eq_end_of_notMem hsnd hs
    intro v hv
    rw [← hb]
    exact mem_Icc_of_mem_dualEdge he hv hsnd'

/-- **Edges of an open arm.** Each edge of an open arm to the boundary of `B_R(z)` has an end in
the interior of `B_R(z)`. -/
theorem IsOpenArm.exists_mem_Icc_of_mem_edges {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsOpenArm ω z r (z - R) (z + R) γ)
    {e : Sym2 (LatticeSite 2)} (he : e ∈ γ.edges) :
    ∃ v ∈ e, v ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
  unfold SimpleGraph.Walk.edges at he
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 he
  exact ⟨δ.fst, by simp [SimpleGraph.Dart.edge], h.isCrossing.mem_of_mem_dropLast _ (by
    rw [← SimpleGraph.Walk.map_fst_darts]
    exact List.mem_map_of_mem hδ)⟩

/-! ### Conditioning on the separated event -/

section Conditioning

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Separated arms with confined ends stay separated under the mixed order off the corridors**
(one family of arms). Let `K ≤ M`, let `T` be a set of pairs (the corridors) with no end in the
interior of `B_R(z)`, and `D` a set of pairs (morally the dual corridors). Suppose that a pair of
`T` with both ends in the box `Icc (b - M) (b + (M + 1))` about a possible end `b ∈ B i` of arm `i`
lies in `D` exactly when arm `i` is dual. If `γ` is a family of arms of `ω`, separated, with ends in
the sets `B i`, then it is a separated family of arms of every `ω'` that agrees with `ω` off `T`,
has more open pairs than `ω` off `D` and fewer on `D`. -/
theorem separated_of_mixed_of_forall_mem (hKM : K ≤ M) {B : Fin j → Set (LatticeSite 2)}
    {T D : Set (Sym2 (LatticeSite 2))}
    (hT : ∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTB : ∀ i, ∀ b ∈ B i, ∀ e ∈ T, (∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false))
    {ω' : Config (LatticeSite 2)} (h₀ : ω \ T = ω' \ T) (h₁ : ω \ D ⊆ ω' \ D)
    (h₂ : ω' ∩ D ⊆ ω ∩ D) {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hsep : ArmsOuterSeparated ω σ z R s M K γ)
    (hB : ∀ i, b i ∈ B i) :
    (∀ i, IsArm ω' (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsOuterSeparated ω' σ z R s M K γ := by
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
  have hbox : ∀ i, ∀ v ∈ Icc (b i) (b i + 1), v ∈ Icc (b i - (M : LatticeSite 2))
      (b i + ((M + 1 : ℕ) : LatticeSite 2)) := by
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
      have h' : IsDualArm ω z r (z - R) (z + R) (γ i) := hγi
      refine ⟨h'.isCrossing, fun E hE => ?_⟩
      obtain ⟨e, he, heω, rfl, -, -⟩ := h'.exists_mem_edgeSet_of_mem_edges hE
      rw [dualEdge_mem_dualConfig_iff he]
      intro heω'
      rcases h'.exists_mem_or_forall_mem_Icc hE he rfl with ⟨v, hv, hvi⟩ | hsub
      · exact heω ((key e fun heT => hT e heT v hv hvi).2 heω')
      · by_cases heT : e ∈ T
        · have heD : e ∈ D := (hTB i (b i) (hB i) e heT fun v hv => hbox i v (hsub v hv)).2 hc
          exact heω (h₂ ⟨heω', heD⟩).1
        · exact heω ((key e heT).2 heω')
    · rw [hc] at hγi
      have h' : IsOpenArm ω z r (z - R) (z + R) (γ i) := hγi
      refine ⟨h'.isCrossing, fun e he => ?_⟩
      obtain ⟨v, hv, hvi⟩ := h'.exists_mem_Icc_of_mem_edges he
      exact (key e fun heT => hT e heT v hv hvi).1 (h'.mem_of_mem_edges e he)
  · -- the fences
    set Bx := Icc (b i - (M : LatticeSite 2)) (b i + ((M + 1 : ℕ) : LatticeSite 2)) with hBx
    have hfi := hf i
    cases hc : σ i
    · rw [hc] at hfi
      set ω₁ := ω' ∩ {e | ∀ v ∈ e, v ∈ Bx} with hω₁
      have hsub : ω₁ ⊆ ω := by
        rintro e ⟨he, heB⟩
        by_cases heT : e ∈ T
        · have heD : e ∈ D := (hTB i (b i) (hB i) e heT heB).2 hc
          exact (h₂ ⟨he, heD⟩).1
        · exact (key e heT).2 he
      have hf₁ : HasOuterFence ω₁ false z R M K (γ i) :=
        hfi.of_cond_subset (dualConfig_anti hsub)
      refine (hasOuterFence_iff_of_inter_eq_of_le hKM subset_rfl ?_).1 hf₁
      rw [hω₁, inter_assoc, inter_self]
    · rw [hc] at hfi
      set ω₀ := ω ∩ {e | ∀ v ∈ e, v ∈ Bx} with hω₀
      have hsub : ω₀ ⊆ ω' := by
        rintro e ⟨he, heB⟩
        by_cases heT : e ∈ T
        · have heD : e ∉ D := fun h => by
            have := (hTB i (b i) (hB i) e heT heB).1 h
            simp [hc] at this
          exact (h₁ ⟨he, heD⟩).1
        · exact (key e heT).1 he
      have hf₀ : HasOuterFence ω₀ true z R M K (γ i) := by
        refine (hasOuterFence_iff_of_inter_eq_of_le hKM subset_rfl ?_).1 hfi
        rw [hω₀, inter_assoc, inter_self]
      exact hf₀.of_cond_subset hsub

/-- **The separated event with confined ends is upper for the mixed order off the corridors.**
Under the hypotheses of `separated_of_mixed_of_forall_mem`, if `ω` has separated arms with ends in
the sets `B i`, so has every `ω'` that agrees with `ω` off `T`, has more open pairs than `ω` off
`D` and fewer on `D`: the same arms witness it. -/
theorem mem_of_mixed_of_forall_mem (hKM : K ≤ M) {B : Fin j → Set (LatticeSite 2)}
    {T D : Set (Sym2 (LatticeSite 2))}
    (hT : ∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTB : ∀ i, ∀ b ∈ B i, ∀ e ∈ T, (∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false))
    {ω' : Config (LatticeSite 2)} (h₀ : ω \ T = ω' \ T) (h₁ : ω \ D ⊆ ω' \ D)
    (h₂ : ω' ∩ D ⊆ ω ∩ D)
    (hω : ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, b i ∈ B i) :
    ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω' (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω' σ z R s M K γ ∧ ∀ i, b i ∈ B i := by
  obtain ⟨a, b, γ, hγ, hd, ho, hsep, hB⟩ := hω
  obtain ⟨hγ', hsep'⟩ := separated_of_mixed_of_forall_mem hKM hT hTB h₀ h₁ h₂ hγ hsep hB
  exact ⟨a, b, γ, hγ', hd, ho, hsep', hB⟩

/-- **Measurability** of the separated event with confined ends. -/
theorem measurableSet_setOf_separated_forall_mem (σ : Fin j → Bool) (z : LatticeSite 2)
    (r R : ℕ) (s : ℝ) (M K : ℕ) (B : Fin j → Set (LatticeSite 2)) :
    MeasurableSet {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, b i ∈ B i} := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  have hsep : Measurable fun ω => ArmsOuterSeparated ω σ z R s M K γ :=
    measurable_const.and (measurable_const.and (Measurable.forall fun i =>
      measurableSet_setOfPred.1 (measurableSet_setOf_hasOuterFence _ z R M K (γ i))))
  exact (Measurable.forall fun i => measurableSet_setOfPred.1
    (measurableSet_setOf_isArm _ z r _ _ (γ i))).and (measurable_const.and (measurable_const.and
      (hsep.and measurable_const)))

/-- **Conditioning on the separated event** (Nolin's Lemma 13 in the form the gluing needs). Under
the hypotheses of `mem_of_mixed_of_forall_mem` on the corridors `T` and the dual corridors `D`,
the separated event with ends in the sets `B i` is positively correlated with every measurable
event `C` determined by `T` and upper for the mixed order (increasing off `D`, decreasing on `D`):
`P(separated, ends in B) P(C) ≤ P(separated, ends in B, C)`. -/
theorem law_mul_le_law_inter_of_mixed (q : Sym2 (LatticeSite 2) → unitInterval) (hKM : K ≤ M)
    {B : Fin j → Set (LatticeSite 2)} {T D : Set (Sym2 (LatticeSite 2))}
    (hT : ∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTB : ∀ i, ∀ b ∈ B i, ∀ e ∈ T, (∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false))
    {C : Set (Config (LatticeSite 2))} (hCm : MeasurableSet C)
    (hC : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ C → ω' ∈ C)
    (hCT : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, b i ∈ B i} * law q C ≤
    law q ({ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, b i ∈ B i} ∩ C) :=
  PercLib.Probability.prodBernoulli_mul_le_inter_of_mixed_of_determined q
    (fun _ _ h₀ h₁ h₂ hω => mem_of_mixed_of_forall_mem hKM hT hTB h₀ h₁ h₂ hω) hC hCT
    (measurableSet_setOf_separated_forall_mem σ z r R s M K B) hCm

end Conditioning

/-! ### Sectors beyond the boundary -/

/-- **Nearby points of the integers are in the same cyclic position** with respect to two points
farther away. -/
theorem sbtw_iff_of_abs_sub_lt {w x a b : ℤ} (ha : |w - x| < |a - x|) (hb : |w - x| < |b - x|) :
    sbtw w a b ↔ sbtw x a b := by
  rw [Int.sbtw_iff, Int.sbtw_iff]
  rcases abs_cases (w - x) with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;>
    rcases abs_cases (a - x) with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩ <;>
    rcases abs_cases (b - x) with ⟨h₃, h₃'⟩ | ⟨h₃, h₃'⟩ <;> omega

/-- **Landing positions on the four sides**, as a disjunction. -/
theorem IsArm.landingPos_cases {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R) :
    (b 1 = z 1 + R ∧
        landingPos (z - R) (z + R) c γ = 8 * R + 2 * (z 0 + R) - (2 * b 0 + cond c 0 1)) ∨
      (b 0 = z 0 + R ∧
        landingPos (z - R) (z + R) c γ = 4 * R + (2 * b 1 + cond c 0 1) - 2 * (z 1 - R)) ∨
      (b 1 = z 1 - R - cond c 0 1 ∧
        landingPos (z - R) (z + R) c γ = 2 * b 0 + cond c 0 1 - 2 * (z 0 - R)) ∨
      (b 0 = z 0 - R - cond c 0 1 ∧
        landingPos (z - R) (z + R) c γ = 12 * R + 2 * (z 1 + R) - (2 * b 1 + cond c 0 1)) := by
  rcases h.end_mem_sides hrR with hb | hb | hb | hb
  · exact Or.inl ⟨hb, h.landingPos_eq_of_top hrR hb⟩
  · exact Or.inr (Or.inl ⟨hb, h.landingPos_eq_of_right hrR hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb, h.landingPos_eq_of_bottom hrR hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb, h.landingPos_eq_of_left hrR hb⟩))

/-- **Arms ending near each other land near each other**, away from the corners. Two arms of one
colour to the boundary of `B_R(z)` whose ends are within sup-distance `M < R` of each other land
within `2M` of each other (on the doubled lattice), when the second lands more than `2M` from
every doubled corner `4 m R`. -/
theorem abs_landingPos_sub_le {c : Bool} {R M r₁ r₂ : ℕ} {ω₁ ω₂ : Config (LatticeSite 2)}
    {a₁ e₁ a₂ e₂ : LatticeSite 2} {W₁ : (zdGraph 2).Walk a₁ e₁} {W₂ : (zdGraph 2).Walk a₂ e₂}
    (h₁ : IsArm ω₁ c z r₁ (z - R) (z + R) W₁) (h₂ : IsArm ω₂ c z r₂ (z - R) (z + R) W₂)
    (hr₁ : r₁ < R) (hr₂ : r₂ < R) (he : e₁ ∈ Icc (e₂ - (M : LatticeSite 2)) (e₂ + M))
    (hMR : M < R)
    (hc : ∀ m : ℕ, 2 * (M : ℤ) < |landingPos (z - R) (z + R) c W₂ - 4 * m * R|) :
    |landingPos (z - R) (z + R) c W₁ - landingPos (z - R) (z + R) c W₂| ≤ 2 * M := by
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  have c4 := hc 4
  push_cast at c0 c1 c2 c3 c4
  rw [lt_abs] at c0 c1 c2 c3 c4
  have hI₁ := h₁.end_mem_Icc (Icc_subset_Icc_add_one_sub_one hr₁)
  have hI₂ := h₂.end_mem_Icc (Icc_subset_Icc_add_one_sub_one hr₂)
  rw [mem_Icc_two_iff] at hI₁ hI₂ he
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hI₁ hI₂ he
  rw [abs_le]
  have f₁ := h₁.landingPos_cases hr₁
  have f₂ := h₂.landingPos_cases hr₂
  obtain ⟨hadj₁, hp₁⟩ := h₁.penultimate_mem hr₁
  obtain ⟨hadj₂, hp₂⟩ := h₂.penultimate_mem hr₂
  cases c <;> simp only [Bool.cond_true, Bool.cond_false] at f₁ f₂ hp₁ hp₂ <;>
    rcases f₁ with ⟨s₁, f₁⟩ | ⟨s₁, f₁⟩ | ⟨s₁, f₁⟩ | ⟨s₁, f₁⟩ <;>
    rcases f₂ with ⟨s₂, f₂⟩ | ⟨s₂, f₂⟩ | ⟨s₂, f₂⟩ | ⟨s₂, f₂⟩ <;> omega

section Sectors

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **An arm stays in its sector.** Let `γ` be a disjoint family of arms to the boundary of
`B_R(z)` landing in counterclockwise order, without packs, and `i ≠ k` two arms of one colour. An
arm with the inner position of `γ k` cannot land closer to `γ i` than every arm of the other colour
does: it lands between the two neighbours of `γ k` (`sbtw_landingPos_iff_of_innerPos_eq`). -/
theorem false_of_innerPos_eq_of_abs_lt (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    (hrR : r < R) (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l)))
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) {a' b' : LatticeSite 2}
    {W : (zdGraph 2).Walk a' b'} (hW : IsArm ω (σ i) z r (z - R) (z + R) W)
    (hin : innerPos z r (σ i) W = innerPos z r (σ k) (γ k))
    (hnear : ∀ l, σ l ≠ σ i → |landingPos (z - R) (z + R) (σ i) W -
      landingPos (z - R) (z + R) (σ i) (γ i)| < |landingPos (z - R) (z + R) (σ l) (γ l) -
        landingPos (z - R) (z + R) (σ i) (γ i)|) : False := by
  have hB := Icc_subset_Icc_add_one_sub_one (z := z) hrR
  rcases hσ with hj | hσ
  · exact hik (Fin.ext (by omega))
  set f : Fin j → ℤ := fun i => landingPos (z - R) (z + R) (σ i) (γ i) with hf
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
  -- the sector of `i` and the sector of `k`
  have s₁ : sbtw (f i) (f l₁) (f l₂) := sbtw_apply_finRotate_apply ho hl₂i h₁₂.symm
  have s₂ : sbtw (f k) (f l₂) (f l₁) := sbtw_apply_finRotate_apply ho hl₁k h₁₂
  have s₃ : ¬sbtw (f k) (f l₁) (f l₂) := fun h => sbtw_asymm h (sbtw_cyclic_left s₂)
  -- `W` lands where `γ i` does, relative to `l₁` and `l₂`
  have hn₁ := hnear l₁ h₁
  have hn₂ := hnear l₂ h₂
  have s₄ : sbtw (landingPos (z - R) (z + R) (σ i) W) (f l₁) (f l₂) :=
    (sbtw_iff_of_abs_sub_lt hn₁ hn₂).2 s₁
  -- the sector lemma
  have hγk : IsArm ω (σ i) z r (z - R) (z + R) (γ k) := hσik ▸ hγ k
  have hsec := sbtw_landingPos_iff_of_innerPos_eq hB hγ hd h₁₂ hσ₁₂ h₁.symm hW hγk
    (by rw [hin, hσik])
  have : sbtw (landingPos (z - R) (z + R) (σ i) (γ k)) (f l₁) (f l₂) := hsec.1 s₄
  rw [hσik] at this
  exact s₃ this

/-- **Arms of one colour land far apart.** Without packs, between two arms of one colour there is
an arm of the other colour on each side; so if any two arms land at least `S` apart, two arms of
one colour land at least `2S` apart. -/
theorem two_mul_le_abs_landingPos_sub (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l)))
    {S : ℤ} (hsep : ∀ i k, i ≠ k → S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) :
    2 * S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) - landingPos (z - R) (z + R) (σ k) (γ k)| := by
  rcases hσ with hj | hσ
  · exact absurd (Fin.ext (by omega)) hik
  set f : Fin j → ℤ := fun i => landingPos (z - R) (z + R) (σ i) (γ i) with hf
  set l₁ := finRotate j i with hl₁
  set l₂ := finRotate j k with hl₂
  have h₁ : σ l₁ ≠ σ i := (hσ i).symm
  have h₂ : σ l₂ ≠ σ i := fun h => hσ k (h.trans hσik).symm
  have h₁₂ : l₁ ≠ l₂ := fun h => hik ((finRotate j).injective h)
  have hl₂i : l₂ ≠ i := fun h => h₂ (congrArg σ h)
  have hl₁k : l₁ ≠ k := fun h => h₁ ((congrArg σ h).trans hσik.symm)
  have hl₁i : l₁ ≠ i := fun h => h₁ (congrArg σ h)
  have hl₂k : l₂ ≠ k := fun h => h₂ ((congrArg σ h).trans hσik.symm)
  have s₁ : sbtw (f i) (f l₁) (f l₂) := sbtw_apply_finRotate_apply ho hl₂i h₁₂.symm
  have s₂ : sbtw (f k) (f l₂) (f l₁) := sbtw_apply_finRotate_apply ho hl₁k h₁₂
  have s₃ : sbtw (f i) (f l₁) (f k) := sbtw_apply_finRotate_apply ho hik.symm hl₁k.symm
  have s₄ : sbtw (f k) (f l₂) (f i) := sbtw_apply_finRotate_apply ho hik hl₂i.symm
  have d₁ : S ≤ |f i - f l₁| := hsep i l₁ hl₁i.symm
  have d₂ : S ≤ |f l₁ - f k| := hsep l₁ k hl₁k
  have d₃ : S ≤ |f k - f l₂| := hsep k l₂ hl₂k.symm
  have d₄ : S ≤ |f l₂ - f i| := hsep l₂ i hl₂i
  change 2 * S ≤ |f i - f k|
  rw [Int.sbtw_iff] at s₁ s₂ s₃ s₄
  rcases abs_cases (f i - f l₁) with ⟨e₁, e₁'⟩ | ⟨e₁, e₁'⟩ <;>
    rcases abs_cases (f l₁ - f k) with ⟨e₂, e₂'⟩ | ⟨e₂, e₂'⟩ <;>
    rcases abs_cases (f k - f l₂) with ⟨e₃, e₃'⟩ | ⟨e₃, e₃'⟩ <;>
    rcases abs_cases (f l₂ - f i) with ⟨e₄, e₄'⟩ | ⟨e₄, e₄'⟩ <;>
    rcases abs_cases (f i - f k) with ⟨e₅, e₅'⟩ | ⟨e₅, e₅'⟩ <;> omega

end Sectors

/-! ### Walk helpers -/

section WalkHelpers

variable {V : Type*} {G : SimpleGraph V}

open SimpleGraph.Walk

/-- In a crossing split into two walks, the only vertex of the first walk outside `T` can be its
last vertex. -/
theorem _root_.SimpleGraph.Walk.IsCrossing.eq_of_mem_support_left {S T : Set V} {u x v : V}
    {q : G.Walk u x} {s : G.Walk x v} (h : (q.append s).IsCrossing S T) {w : V} (hw : w ∈ q.support)
    (hwT : w ∉ T) : w = x := by
  by_contra hne
  apply hwT
  apply h.mem_of_mem_dropLast
  rw [support_append_eq_support_dropLast_append, List.dropLast_append_of_ne_nil (support_ne_nil s)]
  refine List.mem_append_left _ ?_
  have hq := List.dropLast_append_getLast (support_ne_nil q)
  rw [getLast_support] at hq
  rw [← hq, List.mem_append, List.mem_singleton] at hw
  exact hw.resolve_right hne

/-- After a walk with at least one step, every vertex of a second walk lies in the tail of the
support of the joined walk. -/
theorem _root_.SimpleGraph.Walk.mem_support_tail_append_of_mem_right {u x v : V}
    {q : G.Walk u x} (s : G.Walk x v) (hq : ¬q.Nil) {w : V} (hw : w ∈ s.support) :
    w ∈ (q.append s).support.tail := by
  rw [tail_support_append]
  rcases (mem_support_iff s).1 hw with rfl | h
  · exact List.mem_append_left _ (end_mem_tail_support hq)
  · exact List.mem_append_right _ h

end WalkHelpers

/-! ### Boxes around `B_r(z)` for both colours -/

/-- **Arms of either colour as crossings.** -/
theorem isArm_iff_cond {c : Bool} {lo hi a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b} :
    IsArm ω c z r lo hi γ ↔ γ.IsCrossing (cond c (Icc (z - r) (z + r))
      (Icc (z - r - 1) (z + r))) (cond c (Icc (lo + 1) (hi - 1)) (Icc lo (hi - 1))) ∧
      ∀ e ∈ γ.edges, e ∈ cond c ω (dualConfig ω) := by
  cases c
  · exact isDualArm_iff
  · exact isOpenArm_iff

/-- The start box of an arm of either colour lies in `Icc (z - r - 1) (z + r)`. -/
theorem mem_Icc_of_mem_cond_Icc {c : Bool} {w : LatticeSite 2}
    (hw : w ∈ cond c (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r))) :
    w ∈ Icc (z - r - 1) (z + r) := by
  cases c
  · exact hw
  · refine Icc_subset_Icc_left (fun i => ?_) hw
    simp only [Pi.sub_apply, Pi.one_apply]
    omega

/-- An arm from a box inside the interior of the outer box runs through `Icc (lo - 1) hi`. -/
theorem IsArm.mem_Icc_of_mem_support {c : Bool} {lo hi a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) {v : LatticeSite 2} (hv : v ∈ γ.support) :
    v ∈ Icc (lo - 1) hi := by
  cases c
  · exact IsDualArm.mem_Icc h (IsDualArm.not_nil h hB) hv
  · refine Icc_subset_Icc_left (fun i => ?_) (IsOpenArm.mem_Icc h (IsOpenArm.not_nil h hB) hv)
    simp only [Pi.sub_apply, Pi.one_apply]
    omega

/-- For `r < R` the start box of an arm lies in the interior of `B_R(z)`, for either colour. -/
theorem cond_Icc_subset_cond_Icc {c : Bool} {R : ℕ} (hrR : r < R) :
    cond c (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) ⊆
      cond c (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
  cases c <;> refine Icc_subset_Icc (fun i => ?_) (fun i => ?_) <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] <;> omega

/-- For `R + 2 ≤ R'` the box `Icc (z - R - 1) (z + R)` lies in the interior of `B_{R'}(z)`, for
either colour. -/
theorem Icc_subset_cond_Icc {c : Bool} {R R' : ℕ} (hRR' : R + 2 ≤ R') :
    Icc (z - R - 1) (z + R) ⊆
      cond c (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) := by
  cases c <;> refine Icc_subset_Icc (fun i => ?_) (fun i => ?_) <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] <;> omega

/-! ### The fence-connection argument and the gluing -/

section Glue

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- The box of radius `M` about the end of an arm to the boundary of `B_R(z)` misses
`Icc (z - r - 1) (z + r)` when `r + M + 1 < R`. -/
theorem notMem_Icc_of_mem_Icc_end {c : Bool} {M : ℕ} {a₀ b₀ : LatticeSite 2}
    {W : (zdGraph 2).Walk a₀ b₀} (hW : IsArm ω c z r (z - R) (z + R) W) (hrM : r + M + 1 < R)
    {w : LatticeSite 2} (hw : w ∈ Icc (b₀ - M) (b₀ + M)) :
    w ∉ Icc (z - r - 1) (z + r) := by
  intro hwS
  have hs := hW.end_mem_sides (by omega)
  have hc : cond c (0 : ℤ) 1 = 0 ∨ cond c (0 : ℤ) 1 = 1 := by cases c <;> simp
  rw [mem_Icc_two_iff] at hw hwS
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw hwS
  omega

/-- **The fence-connection argument** (the barrier beyond the boundary). Let `γ` be a disjoint
family of arms to the boundary of `B_R(z)`, landing in counterclockwise order, without packs, with
landing positions more than `2M` apart and more than `2M` from the doubled corners, and
`r + M + 1 < R`. Let `P` be a walk of the colour of arm `i`, starting at a vertex (face) `x` of arm
`i` within sup-distance `M` of its end, whose points in `Icc (z - R - 1) (z + R)` all lie within
sup-distance `M` of the end of arm `i`. Then `P` meets no other arm of the colour of `i`. -/
theorem notMem_support_of_mem_Icc (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {M : ℕ}
    (hrM : r + M + 1 < R) (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i))
    (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l)))
    (hsep : ∀ i k, i ≠ k → 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    (hcor : ∀ i (m : ℕ), 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R|)
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) {x y : LatticeSite 2}
    (P : (zdGraph 2).Walk x y) (hx : x ∈ (γ i).support)
    (hxM : x ∈ Icc (b i - M) (b i + M))
    (hP : ∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω))
    (hloc : ∀ v ∈ P.support, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b i - M) (b i + M)) :
    ∀ v ∈ P.support, v ∉ (γ k).support := by
  intro v hvP hvk
  have hrR : r < R := by omega
  have hB := Icc_subset_Icc_add_one_sub_one (z := z) hrR
  obtain ⟨hcri, hEi⟩ := isArm_iff_cond.1 (hγ i)
  have hγk : IsArm ω (σ i) z r (z - R) (z + R) (γ k) := hσik ▸ hγ k
  obtain ⟨hcrk, hEk⟩ := isArm_iff_cond.1 hγk
  have hBS : ∀ w ∈ Icc (b i - M) (b i + M),
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) :=
    fun w hw hwS => notMem_Icc_of_mem_Icc_end (hγ i) hrM hw (mem_Icc_of_mem_cond_Icc hwS)
  have hPS : ∀ w ∈ P.support,
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) := by
    intro w hw hwS
    refine hBS w (hloc w hw ?_) hwS
    have := mem_Icc_of_mem_cond_Icc hwS
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  have hvM : v ∈ Icc (b i - M) (b i + M) := hloc v hvP (hγk.mem_Icc_of_mem_support hB hvk)
  -- split the arms and the walk
  obtain ⟨Q, Sk, hQS⟩ : ∃ (Q : (zdGraph 2).Walk (a k) v) (Sk : (zdGraph 2).Walk v (b k)),
      Q.append Sk = γ k := ⟨_, _, SimpleGraph.Walk.take_spec _ hvk⟩
  obtain ⟨P₁, P₂, hP₁₂⟩ : ∃ (P₁ : (zdGraph 2).Walk x v) (P₂ : (zdGraph 2).Walk v y),
      P₁.append P₂ = P := ⟨_, _, SimpleGraph.Walk.take_spec _ hvP⟩
  obtain ⟨q', s', hq's'⟩ : ∃ (q' : (zdGraph 2).Walk (a i) x) (s' : (zdGraph 2).Walk x (b i)),
      q'.append s' = γ i := ⟨_, _, SimpleGraph.Walk.take_spec _ hx⟩
  have hQnil : ¬Q.Nil := fun h => hBS v hvM (h.eq ▸ hcrk.start_mem)
  have hq'nil : ¬q'.Nil := fun h => hBS x hxM (h.eq ▸ hcri.start_mem)
  have hP₁ : ∀ w ∈ P₁.support, w ∈ P.support := fun w hw => by
    rw [← hP₁₂, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  -- the walk from the start of arm `k` to the end of arm `i`
  set W := Q.append (P₁.reverse.append s') with hW
  have hWE : ∀ e ∈ W.edges, e ∈ cond (σ i) ω (dualConfig ω) := by
    intro e he
    rw [hW, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_append, List.mem_reverse] at he
    rcases he with he | he | he
    · refine hEk e ?_
      rw [← hQS, SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    · refine hP e ?_
      rw [← hP₁₂, SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    · refine hEi e ?_
      rw [← hq's', SimpleGraph.Walk.edges_append]
      exact List.mem_append_right _ he
  have hWS : ∀ w ∈ W.support.tail,
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) := by
    intro w hw
    rw [hW, SimpleGraph.Walk.tail_support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · refine hcrk.notMem_of_mem_tail w ?_
      rw [← hQS, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw
    · have hw' := List.mem_of_mem_tail hw
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] at hw'
      rcases hw' with hw' | hw'
      · exact hPS w (hP₁ w hw')
      · refine hcri.notMem_of_mem_tail w ?_
        rw [← hq's']
        exact SimpleGraph.Walk.mem_support_tail_append_of_mem_right s' hq'nil hw'
  -- its first exit from the interior of `B_R(z)`
  obtain ⟨e, q, t, hqt, heT, hqT⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)))
    W hcri.end_notMem
  have hqcr : q.IsCrossing _ _ := ⟨hcrk.start_mem, fun w hw => hWS w (by
      rw [← hqt, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw), heT, hqT⟩
  have hqarm : IsArm ω (σ i) z r (z - R) (z + R) q := isArm_iff_cond.2 ⟨hqcr, fun e' he' =>
    hWE e' (by rw [← hqt, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he')⟩
  have hqnil : ¬q.Nil := fun h =>
    heT (h.eq ▸ cond_Icc_subset_cond_Icc hrR hcrk.start_mem)
  -- its end is next to the end of arm `i`
  have heM : e ∈ Icc (b i - M) (b i + M) := by
    have he : e ∈ W.support := by
      rw [← hqt, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl q.end_mem_support
    rw [hW, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at he
    rcases he with he | he | he
    · rw [← hQS] at hcrk
      rw [hcrk.eq_of_mem_support_left he heT]
      exact hvM
    · exact hloc e (hP₁ e he) (hqarm.end_mem_Icc hB)
    · have hb : e = b i := hcri.eq_end_of_notMem (by
        rw [← hq's', SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inr he) heT
      rw [hb, mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      omega
  -- it has the inner position of arm `k`
  have hin : innerPos z r (σ i) q = innerPos z r (σ k) (γ k) := by
    calc innerPos z r (σ i) q = innerPos z r (σ i) (q.append t) :=
          (innerPos_append t hqnil).symm
      _ = innerPos z r (σ i) Q := by rw [hqt, hW, innerPos_append _ hQnil]
      _ = innerPos z r (σ i) (γ k) := by rw [← hQS, innerPos_append _ hQnil]
      _ = innerPos z r (σ k) (γ k) := by rw [hσik]
  -- and lands next to arm `i`: a contradiction with the sectors
  have hnear := abs_landingPos_sub_le hqarm (hγ i) hrR hrR heM (by omega) (hcor i)
  refine false_of_innerPos_eq_of_abs_lt hσ hrR hγ hd ho hik hσik hqarm hin fun l hl => ?_
  exact lt_of_le_of_lt hnear (hsep l i fun h => hl (h ▸ rfl))

/-- **Gluing.** Let `γ` be a disjoint family of arms to the boundary of `B_R(z)`, landing in
counterclockwise order, without packs, with landing positions more than `2M` apart and more than
`2M` from the doubled corners, and `r + M + 1 < R`, `R + 2 ≤ R'`. Continue each arm `i` by a walk
`P i` of its colour from one of its vertices (faces) within sup-distance `M` of its end, whose
points in `Icc (z - R - 1) (z + R)` lie within sup-distance `M` of that end and whose last point
lies outside the interior of `B_{R'}(z)` (outside its faces for a dual arm); suppose the
continuations of two arms of one colour are disjoint. Then the arms up to `x i` followed by `P i`,
cut where they first leave the interior of `B_{R'}(z)`, form a disjoint family of arms to the
boundary of `B_{R'}(z)` with the inner positions of `γ`, landing in counterclockwise order, each
ending on its continuation. -/
theorem exists_isArm_of_glue (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {M R' : ℕ}
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i))
    (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l)))
    (hsep : ∀ i k, i ≠ k → 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    (hcor : ∀ i (m : ℕ), 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R|)
    {x y : Fin j → LatticeSite 2} (P : ∀ i, (zdGraph 2).Walk (x i) (y i))
    (hx : ∀ i, x i ∈ (γ i).support) (hxM : ∀ i, x i ∈ Icc (b i - M) (b i + M))
    (hP : ∀ i, ∀ e ∈ (P i).edges, e ∈ cond (σ i) ω (dualConfig ω))
    (hloc : ∀ i, ∀ v ∈ (P i).support, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b i - M) (b i + M))
    (hy : ∀ i, y i ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
      (Icc (z - R') (z + R' - 1)))
    (hdisj : ∀ i k, i ≠ k → σ i = σ k → ∀ v ∈ (P i).support, v ∉ (P k).support) :
    ∃ (b' : Fin j → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ' i))
        (landingPos (z - R') (z + R') (σ k) (γ' k)) (landingPos (z - R') (z + R') (σ l) (γ' l))) ∧
      (∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) ∧ ∀ i, b' i ∈ (P i).support := by
  have hrR : r < R := by omega
  have hB := Icc_subset_Icc_add_one_sub_one (z := z) hrR
  have hB' := Icc_subset_Icc_add_one_sub_one (z := z) (show r < R' by omega)
  -- the first part of each arm, up to `x i`
  choose q' s' hq's' using fun i => (⟨_, _, SimpleGraph.Walk.take_spec _ (hx i)⟩ :
    ∃ (q' : (zdGraph 2).Walk (a i) (x i)) (s' : (zdGraph 2).Walk (x i) (b i)),
      q'.append s' = γ i)
  have hcr := fun i => isArm_iff_cond.1 (hγ i)
  have hq'nil : ∀ i, ¬(q' i).Nil := fun i h => notMem_Icc_of_mem_Icc_end (hγ i) hrM (hxM i)
    (mem_Icc_of_mem_cond_Icc (h.eq ▸ (hcr i).1.start_mem))
  have hPS : ∀ i, ∀ w ∈ (P i).support,
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) := by
    intro i w hw hwS
    have hw' := mem_Icc_of_mem_cond_Icc hwS
    refine notMem_Icc_of_mem_Icc_end (hγ i) hrM (hloc i w hw ?_) hw'
    rw [mem_Icc_two_iff] at hw' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw' ⊢
    omega
  -- the glued walks, cut at their first exit from the interior of `B_{R'}(z)`
  choose e q t hqt heT hqT using fun i => SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
      (Icc (z - R') (z + R' - 1))) ((q' i).append (P i)) (hy i)
  have hmemt : ∀ i, ∀ w ∈ (q i).support.tail, w ∈ (γ i).support.tail ∨ w ∈ (P i).support := by
    intro i w hw
    have hw' : w ∈ ((q' i).append (P i)).support.tail := by
      rw [← hqt i, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw
    rw [SimpleGraph.Walk.tail_support_append, List.mem_append] at hw'
    rcases hw' with hw' | hw'
    · left
      rw [← hq's' i, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw'
    · exact Or.inr (List.mem_of_mem_tail hw')
  have hmem : ∀ i, ∀ w ∈ (q i).support, w ∈ (γ i).support ∨ w ∈ (P i).support := by
    intro i w hw
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hw with rfl | hw
    · exact Or.inl (γ i).start_mem_support
    · rcases hmemt i w hw with h | h
      · exact Or.inl (List.mem_of_mem_tail h)
      · exact Or.inr h
  have hγ' : ∀ i, IsArm ω (σ i) z r (z - R') (z + R') (q i) := by
    intro i
    refine isArm_iff_cond.2 ⟨⟨(hcr i).1.start_mem, fun w hw => ?_, heT i, hqT i⟩, fun e' he' => ?_⟩
    · rcases hmemt i w hw with h | h
      · exact (hcr i).1.notMem_of_mem_tail w h
      · exact hPS i w h
    · have he'' : e' ∈ ((q' i).append (P i)).edges := by
        rw [← hqt i, SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ he'
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at he''
      rcases he'' with he'' | he''
      · refine (hcr i).2 e' ?_
        rw [← hq's' i, SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ he''
      · exact hP i e' he''
  have hin : ∀ i, innerPos z r (σ i) (q i) = innerPos z r (σ i) (γ i) := by
    intro i
    have hqnil : ¬(q i).Nil := fun h => heT i (h.eq ▸ Icc_subset_cond_Icc hRR'
      ((hγ i).mem_Icc_of_mem_support hB (γ i).start_mem_support))
    rw [← innerPos_append (t i) hqnil, hqt i, innerPos_append _ (hq'nil i), ← hq's' i,
      innerPos_append _ (hq'nil i)]
  have hd' : ArmsDisjoint σ q := by
    rcases hσ with hj | hσ'
    · exact armsDisjoint_of_subsingleton hj σ q
    have noMeet := fun {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) =>
      notMem_support_of_mem_Icc (Or.inr hσ') hrM hγ hd ho hsep hcor hik hσik (P i) (hx i) (hxM i)
        (hP i) (hloc i)
    refine ⟨fun i k hik hσi hσk v hv hv' => ?_, fun i k hik hσi hσk v hv hv' => ?_⟩
    · rcases hmemt i v hv with h | h <;> rcases hmem k v hv' with h' | h'
      · exact hd.1 i k hik hσi hσk v h h'
      · exact noMeet hik.symm (hσk.trans hσi.symm) v h' (List.mem_of_mem_tail h)
      · exact noMeet hik (hσi.trans hσk.symm) v h h'
      · exact hdisj i k hik (hσi.trans hσk.symm) v h h'
    · rcases hmem i v hv with h | h <;> rcases hmem k v hv' with h' | h'
      · exact hd.2 i k hik hσi hσk v h h'
      · exact noMeet hik.symm (hσk.trans hσi.symm) v h' h
      · exact noMeet hik (hσi.trans hσk.symm) v h h'
      · exact hdisj i k hik (hσi.trans hσk.symm) v h h'
  refine ⟨e, q, hγ', hd', fun i k l hik hkl => ?_, hin, fun i => ?_⟩
  · rw [← sbtw_innerPos_iff_sbtw_landingPos hB' hγ' hd' i k l, hin i, hin k, hin l,
      sbtw_innerPos_iff_sbtw_landingPos hB hγ hd i k l]
    exact ho i k l hik hkl
  · rcases hmem i (e i) (q i).end_mem_support with h | h
    · exact absurd (Icc_subset_cond_Icc hRR' ((hγ i).mem_Icc_of_mem_support hB h)) (heT i)
    · exact h

end Glue

end PercLib.Models.Planar
