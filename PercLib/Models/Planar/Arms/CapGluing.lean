/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12).
-/
module

public import PercLib.Models.Planar.Arms.JogCorridors

/-!
# Gluing separated arms with fences at the new boundary

Arms separated at the outer boundary of `B_R(z)` (`outerSeparatedArmEvent`) are continued to the
boundary of `B_{R'}(z)`, moved along their sides by given shifts, and given new outer fences there,
at the cost of a constant factor (Nolin's Proposition 12, with fences at the new boundary).

* **Gluing inside straight boxes** (`law_mul_prod_le_law_of_sides`): the gluing through given
  corridors (`law_mul_prod_le_law_of_corridors`) when every corridor reads only pairs inside a
  straight box from its bin out to distance `R''`; the geometric conditions are those of the
  straight gluing, with a margin `S ≥ M` for the separation of the arms.
* **Jogs with caps for fixed bins** (`pow_mul_law_le_law_of_jogs`): the corridors of
  `exists_corridor_jog`.

## Main results

* `law_mul_prod_le_law_of_sides`
* `pow_mul_law_le_law_of_jogs`
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Gluing through corridors inside straight boxes -/

section Sides

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing through arbitrary corridors inside straight boxes.** Let each arm `i` have a straight
box `Icc (lo i) (hi i)` of width `W`, running from its side of `B_R(z)` straight out to distance
`R''` (`hside`, as in `pow_mul_law_le_law_multiArmEventIn_of_sides`, with the corner distance `2S`
for a margin `S ≥ M`), and let the possible ends `B i` of arm `i` lie at the foot of its box. Let
the corridor event `C i` read only pairs inside its box (enlarged by one at the upper corner for a
dual arm), and let the continuations run, apart from the box of radius `M` about the end, through a
region `Q i` inside the box that meets `Icc (z - R - 1) (z + R)` only near the end. With
separation `s ≥ 4S` and `2W + 2 ≤ S`, every fenced separated family ending in the sets `B i` is
glued: `P(separated, ends in B, inner positions in J) · ∏ P(C i) ≤ P(arms to ∂B_{R'}(z) with inner
positions in J and ends satisfying Φ)`. The margin `S` may exceed the fence size `M`: wide boxes
need well separated arms, not deep fences. -/
theorem law_mul_prod_le_law_of_sides (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' R'' W S : ℕ}
    (hKM : K ≤ M) (hM : 1 ≤ M) (hMS : M ≤ S) (hWS : 2 * W + 2 ≤ S) (hs : 4 * (S : ℝ) ≤ s)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hRR'' : R ≤ R'')
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
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ∏ i, law q (C i) ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ' i))
        (landingPos (z - R') (z + R') (σ k) (γ' k)) (landingPos (z - R') (z + R') (σ l) (γ' l))) ∧
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
    rintro ⟨a, b, γ, h₁, -, -, h₄, h₅, -⟩
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
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) →
      ArmsOuterSeparated ω σ z R s M K γ → (∀ i, b i ∈ B i) →
      ∀ i k, i ≠ k → σ i = σ k → ∀ v, (v ∈ Icc (b i - M) (b i + M) ∨ v ∈ Q i) →
        (v ∈ Icc (b k - M) (b k + M) ∨ v ∈ Q k) → False := by
    intro ω a b γ hγ _ ho hsep hBw i k hik hσik v hvi hvk
    rcases hσ with hj | hσ'
    · exact hik (Fin.ext (by omega))
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
    have h8 := two_mul_le_abs_landingPos_sub (Or.inr hσ') ho hsep'.1 hik hσik
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
      have := le_or_le_of_lt_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 (hcorC C hC) hik hσik h₁ h₂
      omega
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 (hcorC C hC) hik.symm hσik.symm h₁ h₂
      omega
    · intro h₁
      have := le_or_le_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 hlo' hhi' hik hσik h₁
      omega
    · intro h₁
      have := le_or_le_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 hlo' hhi' hik.symm hσik.symm h₁
      omega
  refine law_mul_prod_le_law_of_corridors q hσ hKM hM hrM hRR' hsM B J C T Q Φ hCm hCT hCmono hTT
    (fun i e he v hv => ?_) hTB hQloc hQdisj hhook
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

/-- **Gluing separated arms through jogs with caps, for fixed bins.** Let each arm `i` end in a bin
`B i` of width `W₀` on a side of `B_R(z)` (inside the fat bin `Bf i` of width `W₀ + 2D`, at least
`2S`
from the corners), and let it be moved along its side by `d i`, `|d i| ≤ D`, and capped at
`∂B_{R'}(z)` above the target `B' i` (`hjog`). With separation `s ≥ 4S`, `2(W₀ + 2D) + 2 ≤ S`,
`M ≤ S`, the level `h` and the aspect bounds `hκV`, `hκH`, `hκC` of `exists_corridor_jog`:
`c κ ^ (6j) · P(separated with ends in B, inner positions in J) ≤ P(arms to ∂B_{R'}(z), disjoint,
ordered, inner positions in J, ending in B' with outer fences of length 2K' and depth M')`. -/
theorem pow_mul_law_le_law_of_jogs (q : Sym2 (LatticeSite 2) → unitInterval) {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c) (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
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
            v 1 ≤ x i + D + d i + W₀ - K')) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ' i))
        (landingPos (z - R') (z + R') (σ k) (γ' k)) (landingPos (z - R') (z + R') (σ l) (γ' l))) ∧
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
  have hmain := law_mul_prod_le_law_of_sides (σ := σ) (z := z) (r := r) (R := R) (s := s) (M := M)
    (K := K) (R' := R') (R'' := R' + M') (W := W₀ + 2 * D) (S := S) q hσ hKM hM hMS hWS hs hrM
    (by omega) (by omega) J x dir lo hi Bf B hside hBsub C T Q
    (fun i ω v => v ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K'
      (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v))
    hCm hCT hCmono hTsub hQsub hQloc
    (fun i ω hω a b γ _ hb hf => hhook i ω hω a b γ hb hf)
  have hprod : c κ ^ (6 * j) ≤ ∏ i, law q (C i) := by
    calc c κ ^ (6 * j) = ∏ _i : Fin j, c κ ^ 6 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ ∏ i, law q (C i) := Finset.prod_le_prod fun i _ => hprob i
  calc c κ ^ (6 * j) * law q _ ≤ law q _ * ∏ i, law q (C i) := by
        rw [mul_comm]
        exact mul_le_mul' le_rfl hprod
    _ ≤ _ := hmain.trans (measure_mono fun ω hω => by
        obtain ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅⟩ := hω
        exact ⟨a, b', γ', h₁, h₂, h₃, h₄, fun i => ⟨(h₅ i).1, (h₅ i).2.of_nil (γ' i)⟩⟩)

end JogGluing

end PercLib.Models.Planar
