/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12) and
Section 4.6 (the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.HalfGluing

/-!
# The first gluing in the half-plane: straight corridors with caps

The first gluing of `CapGluing.lean` for the arms of the half-plane `{v | z₁ ≤ v₁}`, landing in
increasing order, without two consecutive arms of one colour: separated arms of the half-plane
(separation `s ≥ 4M`, the output of the half-plane outer step) are continued straight out through
narrow corridors with caps, which gives them small new fences at the new boundary while keeping
their separation; this makes room for the moves between windows (`HalfRotationGluing.lean`).

The plane's version uses the absence of packs in the cyclic order twice near the corners: two arms
of one colour on both sides of a corner, and two arms of one colour near both ends of the cycle of
positions. In the half-plane the first comes from the linear order (an arm of the other colour lands
between two arms of one colour, `exists_lt_lt_of_eq_half`); the second cannot happen, since the arms
land between the two points of the line on the boundary.

## Main results

* `exists_lt_lt_of_eq_half`, `le_or_le_of_lt_of_lt_half`, `two_mul_le_abs_sub_half`: arms of one
  colour in the linear order.
* `law_mul_prod_le_law_of_sides_half`: gluing through corridors inside straight boxes.
* `pow_mul_law_le_law_of_jogs_half`: gluing through jogs with caps, for fixed bins.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Arms of one colour in the half-plane -/

section Between

variable {j : ℕ} {σ : Fin j → Bool} {f : Fin j → ℤ}

/-- **Between two arms of one colour there is an arm of the other colour** (linear order). For a
family without two consecutive arms of one colour, landing in increasing order at the integer
positions `f`, and two arms `i`, `k` of one colour with `f k < f i`, some arm of the other colour
lands strictly between them. -/
theorem exists_lt_lt_of_eq_half (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k)
    (ho : StrictMono f) {i k : Fin j} (hσik : σ i = σ k) (hlt : f k < f i) :
    ∃ l, σ l ≠ σ i ∧ f k < f l ∧ f l < f i := by
  have hki : k < i := ho.lt_iff_lt.1 hlt
  have hki' : k.val < i.val := hki
  obtain ⟨l, hl⟩ : ∃ l : Fin j, l.val = k.val + 1 := ⟨⟨k.val + 1, by omega⟩, rfl⟩
  have hσl : σ l ≠ σ i := fun h => hσ k l hl.symm (hσik.symm.trans h.symm)
  have hli : l ≠ i := fun h => hσl (congrArg σ h)
  have hkl : k < l := by rw [Fin.lt_def]; omega
  have hli' : l < i := by
    rw [Fin.lt_def]
    have : l.val ≠ i.val := fun h => hli (Fin.ext h)
    omega
  exact ⟨l, hσl, ho hkl, ho hli'⟩

/-- **Arms of one colour on both sides of a corner** (linear order): `le_or_le_of_lt_of_lt` for a
family landing in increasing order without two consecutive arms of one colour. -/
theorem le_or_le_of_lt_of_lt_half (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k)
    (ho : StrictMono f) {S : ℤ}
    (hsep : ∀ i k, i ≠ k → S ≤ |f i - f k|) {C : ℤ} (hC : ∀ l, S ≤ |f l - C|) {i k : Fin j}
    (hσik : σ i = σ k) (hkC : f k < C) (hCi : C < f i) :
    C + 2 * S ≤ f i ∨ f k ≤ C - 2 * S := by
  obtain ⟨l, hl, hkl, hli⟩ := exists_lt_lt_of_eq_half hσ ho hσik (hkC.trans hCi)
  have hli' : l ≠ i := fun h => hl (congrArg σ h)
  have hlk' : l ≠ k := fun h => hl ((congrArg σ h).trans hσik.symm)
  have e₁ := hsep l i hli'
  have e₂ := hsep l k hlk'
  have e₃ := hC l
  rw [le_abs] at e₁ e₂ e₃
  omega

/-- **Arms of one colour land far apart** (linear order): `two_mul_le_abs_landingPos_sub` for a
family landing in increasing order without two consecutive arms of one colour. -/
theorem two_mul_le_abs_sub_half (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k)
    (ho : StrictMono f) {S : ℤ} (hsep : ∀ i k, i ≠ k → S ≤ |f i - f k|) {i k : Fin j}
    (hik : i ≠ k) (hσik : σ i = σ k) : 2 * S ≤ |f i - f k| := by
  rcases lt_or_gt_of_ne (fun h : f i = f k => hik (ho.injective h)) with hlt | hlt
  · obtain ⟨l, hl, hil, hlk⟩ := exists_lt_lt_of_eq_half hσ ho hσik.symm hlt
    have hli' : l ≠ i := fun h => hl ((congrArg σ h).trans hσik)
    have hlk' : l ≠ k := fun h => hl (congrArg σ h)
    have e₁ := hsep l i hli'
    have e₂ := hsep l k hlk'
    rw [le_abs] at e₁ e₂ ⊢
    omega
  · obtain ⟨l, hl, hkl, hli⟩ := exists_lt_lt_of_eq_half hσ ho hσik hlt
    have hli' : l ≠ i := fun h => hl (congrArg σ h)
    have hlk' : l ≠ k := fun h => hl ((congrArg σ h).trans hσik.symm)
    have e₁ := hsep l i hli'
    have e₂ := hsep l k hlk'
    rw [le_abs] at e₁ e₂ ⊢
    omega

end Between

/-! ### Gluing through corridors inside straight boxes -/

section Sides

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing through arbitrary corridors inside straight boxes, in the half-plane**
(`law_mul_prod_le_law_of_sides` for the arms of the half-plane `{v | z₁ ≤ v₁}`, landing in
increasing order, without two consecutive arms of one colour). The hypotheses are those of the
plane, with the continuation regions and the boxes of radius `M` about the possible ends in the
half-plane, and `4S ≤ R` (the arms land between the two points of the line,
`IsArm.landingPos_mem_Icc_of_half`, so two arms of one colour cannot be near the two ends of the
cycle of positions). -/
theorem law_mul_prod_le_law_of_sides_half (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {R' R'' W S : ℕ}
    (hKM : K ≤ M) (hM : 1 ≤ M) (hMS : M ≤ S) (hWS : 2 * W + 2 ≤ S) (hs : 4 * (S : ℝ) ≤ s)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hRR'' : R ≤ R'') (hSR : 4 * S ≤ R)
    (J : Fin j → Set ℤ) (x : Fin j → ℤ) (dir : Fin j → Fin 2) (lo hi : Fin j → LatticeSite 2)
    (Bf B : Fin j → Set (LatticeSite 2))
    (hside : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧ hi i = ![x i + W, z 1 + R''] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + W ∧ z 0 - R + 2 * S ≤ b 0 ∧
          b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + R'', x i + W] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + W ∧ z 1 - R + 2 * S ≤ b 1 ∧
          b 1 + 2 * S ≤ z 1 + R) ∨
      (dir i = 1 ∧ lo i = ![x i, z 1 - R'' - cond (σ i) 0 1] ∧
        hi i = ![x i + W, z 1 - R - cond (σ i) 0 1] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧ b 0 ≤ x i + W ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 - R'' - cond (σ i) 0 1, x i] ∧
        hi i = ![z 0 - R - cond (σ i) 0 1, x i + W] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧ b 1 ≤ x i + W ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R))
    (hB : ∀ i, B i ⊆ Bf i)
    (C : Fin j → Set (Config (LatticeSite 2))) (T : Fin j → Set (Sym2 (LatticeSite 2)))
    (Q : Fin j → Set (LatticeSite 2)) (Φ : Fin j → Config (LatticeSite 2) → LatticeSite 2 → Prop)
    (hCm : ∀ i, MeasurableSet (C i))
    (hCT : ∀ i (ω ω' : Config (LatticeSite 2)), ω ∩ T i = ω' ∩ T i → (ω ∈ C i ↔ ω' ∈ C i))
    (hCmono : ∀ i (ω ω' : Config (LatticeSite 2)), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω →
      ω ∈ C i → ω' ∈ C i)
    (hTsub : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∈ Icc (lo i) (hi i + cond (σ i) 0 1))
    (hQsub : ∀ i, Q i ⊆ Icc (lo i) (hi i))
    (hQloc : ∀ i, ∀ b ∈ B i, ∀ v ∈ Q i, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b - M) (b + M))
    (hQH : ∀ i, ∀ v ∈ Q i, z 1 ≤ v 1)
    (hBH : ∀ i, ∀ b ∈ B i, ∀ v ∈ Icc (b - (M : LatticeSite 2)) (b + M), z 1 ≤ v 1)
    (hhook : ∀ i, ∀ ω ∈ C i, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
      ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
        x ∈ Icc (b - M) (b + M) ∧ (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ v ∈ P.support, v ∈ Icc (b - M) (b + M) ∨ v ∈ Q i) ∧
        y ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) ∧
        ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
          (Icc (z - R') (z + R' - 1)) → Φ i ω v) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ∏ i, law q (C i) ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i)) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧ ∀ i, Φ i ω (b' i)} := by
  classical
  have hrR : r < R := by omega
  have hS : 1 ≤ S := by omega
  have hc : ∀ i, 0 ≤ cond (σ i) (0 : ℤ) 1 ∧ cond (σ i) (0 : ℤ) 1 ≤ 1 := fun i => by
    cases σ i <;> simp
  have hMS' : (M : ℝ) ≤ S := by exact_mod_cast hMS
  have hsM : 4 * (M : ℝ) ≤ s := by linarith
  -- the empty case
  by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
      (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
      (∀ i, IsArm ω₀ (σ i) z r (z - R) (z + R) (γ₀ i)) ∧ ArmsOuterSeparated ω₀ σ z R s M K γ₀ ∧
        ∀ i, b₀ i ∈ B i
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine mul_eq_zero_of_left ?_ _
    convert measure_empty (μ := law q)
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨a, b, γ, h₁, -, -, -, h₄, h₅, -⟩
    exact hne ⟨ω, a, b, γ, h₁, h₄, h₅⟩
  obtain ⟨ω₀, a₀, b₀, γ₀, hγ₀, hsep₀, hB₀⟩ := hne
  have hsep₀' := hsep₀.le_abs_landingPos_sub (S := 4 * S) (by push_cast; linarith)
  have SL₀ := fun i => (hγ₀ i).sideL_of_side hrR hS (hside i) (hB i (hB₀ i))
  -- open and dual corridors read disjoint pairs
  have hTT : ∀ i k, σ i = true → σ k = false → Disjoint (T i) (T k) := by
    intro i k hi hk
    rw [disjoint_left]
    intro e he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have h₁ := hTsub i e he v hv
    have h₂ := hTsub k e he' v hv
    have hik : i ≠ k := fun h => by
      rw [h, hk] at hi
      exact Bool.false_ne_true hi
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Pi.add_apply, cond_zero_one_apply] at h₁ h₂
    exact false_of_corridor_of_corridor (by omega) (by omega) (by simp [hi]) (by simp [hk])
      (SL₀ i) (SL₀ k) (hsep₀'.1 i k hik) h₁ h₂
  -- corridors of one colour avoid the end boxes of the other colour
  have hTB : ∀ i k, σ i ≠ σ k → ∀ b ∈ B i, ∀ e ∈ T k, ¬∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2)) := by
    intro i k hik b hb e he hbox
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have h₁ := hTsub k e he v hv
    have h₂ := hbox v hv
    have hik' : i ≠ k := fun h => hik (h ▸ rfl)
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, cond_zero_one_apply] at h₁ h₂
    refine false_of_box_of_corridor (by omega) (by omega) (by omega) ?_ (SL₀ i)
      (sideP_of_side (hside i) (hB i hb)) (SL₀ k) (hsep₀'.1 i k hik')
      ⟨by omega, by omega, by omega, by omega⟩ h₁
    rcases Bool.eq_false_or_eq_true (σ i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (σ k) with h' | h'
    · exact absurd (h.trans h'.symm) hik
    · rw [h, h']
      exact Or.inl ⟨rfl, rfl⟩
    · rw [h, h']
      exact Or.inr ⟨rfl, rfl⟩
    · exact absurd (h.trans h'.symm) hik
  -- the regions of arms of one colour are disjoint
  have hQdisj : ∀ (ω : Config (LatticeSite 2)) (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) → ArmsDisjoint σ γ →
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) →
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) →
      ArmsOuterSeparated ω σ z R s M K γ → (∀ i, b i ∈ B i) →
      ∀ i k, i ≠ k → σ i = σ k → ∀ v, (v ∈ Icc (b i - M) (b i + M) ∨ v ∈ Q i) →
        (v ∈ Icc (b k - M) (b k + M) ∨ v ∈ Q k) → False := by
    intro ω a b γ hγ _ hH ho hsep hBw i k hik hσik v hvi hvk
    have hsep' := hsep.le_abs_landingPos_sub (S := 4 * S) (by push_cast; linarith)
    have hbd : ∀ l, 0 ≤ landingPos (z - R) (z + R) (σ l) (γ l) ∧
        landingPos (z - R) (z + R) (σ l) (γ l) ≤ 16 * R := fun l => by
      have := (hγ l).sideL_of_side hrR hS (hside l) (hB l (hBw l))
      have := hc l
      omega
    have hlo' : ∀ l, 4 * (S : ℤ) ≤ landingPos (z - R) (z + R) (σ l) (γ l) := fun l => by
      have h₁ := hsep'.2 l 0
      have h₂ := hbd l
      rw [le_abs] at h₁
      push_cast at h₁
      omega
    have hhi' : ∀ l, landingPos (z - R) (z + R) (σ l) (γ l) + 4 * S ≤ 16 * R := fun l => by
      have h₁ := hsep'.2 l 4
      have h₂ := hbd l
      rw [le_abs] at h₁
      push_cast at h₁
      omega
    have h8 := two_mul_le_abs_sub_half (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ
      ho hsep'.1 hik hσik
    have hcorC : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R → ∀ l,
        4 * (S : ℤ) ≤ |landingPos (z - R) (z + R) (σ l) (γ l) - C| := by
      intro C hC l
      have h₁ := hsep'.2 l 1
      have h₂ := hsep'.2 l 2
      have h₃ := hsep'.2 l 3
      rw [le_abs] at h₁ h₂ h₃ ⊢
      push_cast at h₁ h₂ h₃
      omega
    have hvi' : v ∈ Icc (b i - S) (b i + S) ∨ v ∈ Icc (lo i) (hi i) := by
      rcases hvi with h | h
      · left
        rw [mem_Icc_two_iff] at h ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h ⊢
        omega
      · exact Or.inr (hQsub i h)
    have hvk' : v ∈ Icc (b k - S) (b k + S) ∨ v ∈ Icc (lo k) (hi k) := by
      rcases hvk with h | h
      · left
        rw [mem_Icc_two_iff] at h ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h ⊢
        omega
      · exact Or.inr (hQsub k h)
    rw [mem_Icc_two_iff, mem_Icc_two_iff] at hvi' hvk'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hvi' hvk'
    refine false_of_region_of_region (by omega) (by omega) (hc i) (by rw [hσik])
      ((hγ i).sideL_of_side hrR hS (hside i) (hB i (hBw i)))
      ((hγ k).sideL_of_side hrR hS (hside k) (hB k (hBw k))) (by linarith)
      (fun C hC => ⟨?_, ?_⟩) (fun P hP => ⟨?_, ?_⟩) hvi' hvk'
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt_half (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l))
        hσ ho hsep'.1 (hcorC C hC) hσik h₁ h₂
      omega
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt_half (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l))
        hσ ho hsep'.1 (hcorC C hC) hσik.symm h₁ h₂
      omega
    · intro _
      have := ((hγ i).landingPos_mem_Icc_of_half hrR (hH i)).2
      omega
    · intro _
      have := ((hγ k).landingPos_mem_Icc_of_half hrR (hH k)).2
      omega
  refine law_mul_prod_le_law_of_corridors_half q hσ hKM hM hrM hRR' hsM B J C T Q Φ hCm hCT
    hCmono hTT (fun i e he v hv => ?_) hTB hQloc hQH hBH hQdisj hhook
  have h₁ := hTsub i e he v hv
  have h₂ := sideP_of_side (hside i) (hB i (hB₀ i))
  have hc' := hc i
  intro hvI
  rw [mem_Icc_two_iff] at h₁ hvI
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
    cond_zero_one_apply] at h₁ hvI
  omega


end Sides

/-! ### Gluing through jogs with caps, for fixed bins -/

section JogGluing

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing separated arms of the half-plane through jogs with caps, for fixed bins**
(`pow_mul_law_le_law_of_jogs` for the arms of the half-plane, landing in increasing order, without
two consecutive arms of one colour), when the straight boxes and the boxes of radius `M` about the
possible ends lie in the half-plane (`hloH`, `hBH`) and `4S ≤ R`. The new arms lie in the
half-plane and land in increasing order. -/
theorem pow_mul_law_le_law_of_jogs_half (q : Sym2 (LatticeSite 2) → unitInterval) {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k)
    {R' M' K' W₀ D κ S : ℕ} {h : ℤ} (hM : 1 ≤ M) (hWK : W₀ ≤ K) (hKM : K ≤ M)
    (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K') (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hrM : r + M + 1 < R) (hMS : M ≤ S)
    (hWS : 2 * (W₀ + 2 * D) + 2 ≤ S) (hs : 4 * (S : ℝ) ≤ s)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) (J : Fin j → Set ℤ)
    (x d : Fin j → ℤ) (hd : ∀ i, -(D : ℤ) ≤ d i ∧ d i ≤ D) (dir : Fin j → Fin 2)
    (lo hi : Fin j → LatticeSite 2) (Bf B B' : Fin j → Set (LatticeSite 2))
    (hjog : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧ hi i = ![x i + ↑(W₀ + 2 * D), z 1 + ↑(R' +
        M')] ∧
          (∀ b, b ∈ Bf i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          (∀ b, b ∈ B i ↔ b 1 = z 1 + R ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W₀ ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          ∀ v, v ∈ B' i ↔ v 1 = z 1 + R' ∧ x i + D + d i + K' ≤ v 0 ∧ v 0 ≤ x i + D + d i + W₀ - K')
              ∨
        (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + ↑(R' + M'), x i + ↑(W₀ + 2 * D)] ∧
          (∀ b, b ∈ Bf i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          (∀ b, b ∈ B i ↔ b 0 = z 0 + R ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W₀ ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          ∀ v, v ∈ B' i ↔ v 0 = z 0 + R' ∧ x i + D + d i + K' ≤ v 1 ∧ v 1 ≤ x i + D + d i + W₀ - K')
              ∨
        (dir i = 1 ∧ lo i = ![x i, z 1 - ↑(R' + M') - cond (σ i) 0 1] ∧
          hi i = ![x i + ↑(W₀ + 2 * D), z 1 - R - cond (σ i) 0 1] ∧
          (∀ b, b ∈ Bf i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧ b 0 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          (∀ b, b ∈ B i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W₀ ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          ∀ v, v ∈ B' i ↔ v 1 = z 1 - R' - cond (σ i) 0 1 ∧ x i + D + d i + K' ≤ v 0 ∧
            v 0 ≤ x i + D + d i + W₀ - K') ∨
        (dir i = 0 ∧ lo i = ![z 0 - ↑(R' + M') - cond (σ i) 0 1, x i] ∧
          hi i = ![z 0 - R - cond (σ i) 0 1, x i + ↑(W₀ + 2 * D)] ∧
          (∀ b, b ∈ Bf i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧ b 1 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          (∀ b, b ∈ B i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W₀ ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          ∀ v, v ∈ B' i ↔ v 0 = z 0 - R' - cond (σ i) 0 1 ∧ x i + D + d i + K' ≤ v 1 ∧
            v 1 ≤ x i + D + d i + W₀ - K'))
    (hSR : 4 * S ≤ R) (hloH : ∀ i, z 1 ≤ lo i 1)
    (hBH : ∀ i, ∀ b ∈ B i, ∀ v ∈ Icc (b - (M : LatticeSite 2)) (b + M), z 1 ≤ v 1) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i)) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧
      ∀ i, b' i ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K' (γ' i)} := by
  classical
  have hMR : M ≤ R := by omega
  choose C T Q hCm hCT hCmono hTsub hQsub hQloc hhook hprob using fun i =>
    exists_corridor_jog (col := σ i) (z := z) (h := h) (d := d i) hCB hM hWK hKM hK' hM' hWM'
      (hd i).1 (hd i).2 hh hhR hMR hMS (by omega) hκV hκH hκC hL (hjog i)
  have hside : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧
        hi i = ![x i + ↑(W₀ + 2 * D), z 1 + ↑(R' + M')] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + ↑(W₀ + 2 * D) ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + ↑(R' + M'), x i + ↑(W₀ + 2 * D)] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + ↑(W₀ + 2 * D) ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨
      (dir i = 1 ∧ lo i = ![x i, z 1 - ↑(R' + M') - cond (σ i) 0 1] ∧
        hi i = ![x i + ↑(W₀ + 2 * D), z 1 - R - cond (σ i) 0 1] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧
          b 0 ≤ x i + ↑(W₀ + 2 * D) ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 - ↑(R' + M') - cond (σ i) 0 1, x i] ∧
        hi i = ![z 0 - R - cond (σ i) 0 1, x i + ↑(W₀ + 2 * D)] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧
          b 1 ≤ x i + ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) := by
    intro i
    rcases hjog i with ⟨h₁, h₂, h₃, h₄, -⟩ | ⟨h₁, h₂, h₃, h₄, -⟩ | ⟨h₁, h₂, h₃, h₄, -⟩ |
      ⟨h₁, h₂, h₃, h₄, -⟩
    · exact Or.inl ⟨h₁, h₂, h₃, h₄⟩
    · exact Or.inr (Or.inl ⟨h₁, h₂, h₃, h₄⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, h₄⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, h₄⟩))
  have hBsub : ∀ i, B i ⊆ Bf i := by
    intro i b hb
    rcases hjog i with ⟨-, -, -, h₄, h₅, -⟩ | ⟨-, -, -, h₄, h₅, -⟩ | ⟨-, -, -, h₄, h₅, -⟩ |
      ⟨-, -, -, h₄, h₅, -⟩ <;> rw [h₄] <;> rw [h₅] at hb <;> push_cast <;> omega
  have hmain := law_mul_prod_le_law_of_sides_half (σ := σ) (z := z) (r := r) (R := R) (s := s)
    (M := M) (K := K) (R' := R') (R'' := R' + M') (W := W₀ + 2 * D) (S := S) q hσ hKM hM hMS hWS
    hs hrM (by omega) (by omega) hSR J x dir lo hi Bf B hside hBsub C T Q
    (fun i ω v => v ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K'
      (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v))
    hCm hCT hCmono hTsub hQsub hQloc
    (fun i v hv => by
      have h₁ := hQsub i hv
      have h₂ := hloH i
      rw [mem_Icc_two_iff] at h₁
      omega)
    hBH (fun i ω hω a b γ _ hb hf => hhook i ω hω a b γ hb hf)
  have hprod : c κ ^ (6 * j) ≤ ∏ i, law q (C i) := by
    calc c κ ^ (6 * j) = ∏ _i : Fin j, c κ ^ 6 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ ∏ i, law q (C i) := Finset.prod_le_prod fun i _ => hprob i
  calc c κ ^ (6 * j) * law q _ ≤ law q _ * ∏ i, law q (C i) := by
        rw [mul_comm]
        exact mul_le_mul' le_rfl hprod
    _ ≤ _ := hmain.trans (measure_mono fun ω hω => by
        obtain ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hω
        exact ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅, fun i => ⟨(h₆ i).1, (h₆ i).2.of_nil (γ' i)⟩⟩)


end JogGluing

end PercLib.Models.Planar
