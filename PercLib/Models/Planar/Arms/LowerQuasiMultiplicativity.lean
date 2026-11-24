/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.5 (quasi-multiplicativity, Proposition 17, and
extendability, Proposition 16).
-/
module

public import PercLib.Models.Planar.Arms.InnerFamilyGluing
public import PercLib.Models.Planar.Arms.InnerSeparation
public import PercLib.Models.Planar.Arms.OuterArmSeparation

/-!
# The lower half of quasi-multiplicativity

Nolin's quasi-multiplicativity, lower half: `π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)` for colour
sequences without packs, uniformly under crossing bounds.

## Main results

* `exists_strictMono_comp_finRotate_pow`: rotating the indices of a cyclically ordered family so
  that its positions increase.
* `exists_pos_mul_le_law_of_plan_two_sided`: the motion plan carries a family separated at the
  outer boundary of `B_{R₀}(z)` into windows aligned with the starts of a family separated at the
  inner boundary of `B_ρ(z)`, and the two-sided gluing with regions disjoint by colour joins them.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Choosing the first arm -/

/-- Rotating the indices `k` times sends `0` to `k`. -/
theorem finRotate_pow_val_apply_zero {m : ℕ} (k : Fin (m + 1)) :
    (finRotate (m + 1) ^ (k : ℕ)) 0 = k := by
  rw [Equiv.Perm.coe_pow, ← finCycle_eq_finRotate_iterate, finCycle_apply, zero_add]

/-- **Choosing the first arm.** For pairwise distinct integer positions `P` in strict cyclic order
along the indices, rotating the indices so that the arm of smallest position comes first makes the
positions increasing. -/
theorem exists_strictMono_comp_finRotate_pow {j : ℕ} {P : Fin j → ℤ}
    (hP : ∀ i k l, i < k → k < l → sbtw (P i) (P k) (P l)) (hinj : Function.Injective P) :
    ∃ m : ℕ, StrictMono fun i => P ((finRotate j ^ m) i) := by
  rcases j with _ | m
  · exact ⟨0, fun i => i.elim0⟩
  obtain ⟨k₀, -, hk₀⟩ := Finset.univ.exists_min_image P Finset.univ_nonempty
  refine ⟨k₀, fun i l hil => ?_⟩
  change P ((finRotate (m + 1) ^ (k₀ : ℕ)) i) < P ((finRotate (m + 1) ^ (k₀ : ℕ)) l)
  have hgP := sbtw_comp_finRotate_pow (k₀ : ℕ) hP
  have hg0 : P ((finRotate (m + 1) ^ (k₀ : ℕ)) 0) = P k₀ := by
    rw [finRotate_pow_val_apply_zero]
  have hmin : ∀ i, P k₀ ≤ P ((finRotate (m + 1) ^ (k₀ : ℕ)) i) :=
    fun i => hk₀ _ (Finset.mem_univ _)
  have hne : ∀ i, i ≠ 0 → P k₀ ≠ P ((finRotate (m + 1) ^ (k₀ : ℕ)) i) := by
    intro i hi h
    rw [← hg0] at h
    exact hi ((finRotate (m + 1) ^ (k₀ : ℕ)).injective (hinj h)).symm
  have hl0 : l ≠ 0 := fun h => by
    rw [h] at hil
    exact absurd hil (Fin.not_lt_zero i)
  have h₁ := hmin l
  have h₂ := hne l hl0
  rcases (Fin.zero_le i).lt_or_eq with h0 | h0
  · have h₃ := Int.sbtw_iff.1 (hgP 0 i l h0 hil)
    rw [hg0] at h₃
    have h₄ := hmin i
    omega
  · subst h0
    rw [hg0]
    omega

section Core

variable {j : ℕ}

/-- **The motion plan into aligned windows followed by the two-sided gluing.** For a colour
sequence `σ` without packs and integers `Ap`, `At`, `n` there is `c₀ > 0` such that for every law
with crossing bounds `c` up to scale `L` the following holds. A family separated at the outer
boundary of `B_{R₀}(z)` (separation `s₀`, fences `(2u, u)`, inner positions in `J`) is carried by
the motion plan (`exists_pos_le_law_target_windows`, unit `u`, jog bound `D`, rooms `Sp`, `Gp`,
`Q`) to `∂B_R(z)`, ending in the windows `[x i, x i + B]` on the sides `t i` (in the linear
counterclockwise order from the lower-left corner encoded by `lamT`) with fences `(M₁, K₁)`; there
it is glued (`exists_pos_le_law_two_sided_of_colour`, corridors `[x i, x i + W]`, `ρ ≤ R + At W`)
to a family separated at the inner boundary of `B_ρ(z)` (separation `s'`, fences `(m', k')`) with
starts in the windows `[x i, x i + bw]`: `c₀ P(first) P(second) ≤ P(arms from B_r(z) to ∂B_{R₃}(z)
with inner positions in J)`. The hypotheses are those of the two lemmas, passed through (the
reason for their number); the arithmetic is done by the callers. -/
theorem exists_pos_mul_le_law_of_plan_two_sided (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (Ap At n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2)
      (r R₀ R ρ R₃ u D Sp Gp Q B M₁ K₁ W S m' k' bw : ℕ) (s₀ s' : ℝ) (J : Fin j → Set ℤ)
      (t : Fin j → Fin 4) (lamT x : Fin j → ℤ),
      1 ≤ u → 2 ≤ M₁ → u + K₁ ≤ M₁ → u + 2 * u ≤ Ap * (2 * u - 1) →
      u + 2 * K₁ ≤ Ap * (M₁ - 1) → u + 2 * D + 2 * (2 * u) + 2 * u + 3 ≤ Sp →
      Sp + 2 * (12 * j) * u ≤ Gp → u + 2 * (2 * u) + 2 * K₁ + 3 ≤ Q →
      ((2 * Gp + 4 * u + 2 : ℕ) : ℝ) ≤ s₀ → r + 2 * u + 1 < R₀ →
      R₀ + 12 * j * (Gp + 2 * u + u + 1) + n * (2 * (2 * u) + u + 1) + (2 * u + M₁ + u + 1) ≤ R →
      2 * R + 2 ≤ Ap * u → (R₃ : ℕ∞) ≤ L → 2 * R + 2 * n + n * u ≤ n * D →
      n + (2 * (12 * j) + 2 * n + 3) * u ≤ B →
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((t i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + (Sp + Q + 2 * u + M₁ + u + 1) ≤ x i ∧
        x i + B + (Sp + Q + 2 * u + M₁ + u + 1) ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      (∀ i l, i < l → t i = t l → (t i = 1 ∨ t i = 2 → x i + B + Sp + Q ≤ x l) ∧
        (t i = 0 ∨ t i = 3 → x l + B + Sp + Q ≤ x i)) →
      1 ≤ W → W ≤ K₁ → W ≤ k' → k' ≤ m' → M₁ + K₁ + m' + k' + 2 ≤ S → M₁ + 1 ≤ Q →
      2 * (m' : ℝ) + 2 ≤ s' → r + M₁ + 1 < R → R + M₁ + K₁ + 1 + m' + k' + 1 < ρ →
      ρ + m' + 1 < R₃ → ρ ≤ R + At * W → B ≤ K₁ → bw ≤ k' →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + 2 * S ≤ x i ∧
        x i + W + 2 * S ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      (∀ i k, i ≠ k → σ i = σ k → t i = t k → x i + W + 2 * S < x k ∨ x k + W + 2 * S < x i) →
      (∀ i k, i ≠ k → t i = t k → x i + W + (M₁ + K₁ + m' + k' + 2) < x k ∨
        x k + W + (M₁ + K₁ + m' + k' + 2) < x i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R₀) (z + R₀) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₀) (z + R₀) (σ i) (γ i))
          (landingPos (z - R₀) (z + R₀) (σ k) (γ k)) (landingPos (z - R₀) (z + R₀) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R₀ s₀ (2 * u) u γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} *
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z ρ (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
          (landingPos (z - R₃) (z + R₃) (σ k) (γ k)) (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z ρ s' m' k' γ ∧ ∀ i, a i ∈ {a : LatticeSite 2 |
          (t i = 0 ∧ a 1 = z 1 + ρ ∧ x i ≤ a 0 ∧ a 0 ≤ x i + bw) ∨
          (t i = 1 ∧ a 0 = z 0 + ρ ∧ x i ≤ a 1 ∧ a 1 ≤ x i + bw) ∨
          (t i = 2 ∧ a 1 = z 1 - ρ - cond (σ i) 0 1 ∧ x i ≤ a 0 ∧ a 0 ≤ x i + bw) ∨
          (t i = 3 ∧ a 0 = z 0 - ρ - cond (σ i) 0 1 ∧ x i ≤ a 1 ∧ a 1 ≤ x i + bw)}} ≤
      law q (multiArmEventIn σ z r R₃ J fun _ => univ) := by
  obtain ⟨c₁, hc₁, hplan⟩ := exists_pos_le_law_target_windows σ hσ c Ap n
  obtain ⟨c₂, hc₂, hglue⟩ := exists_pos_le_law_two_sided_of_colour σ hσ c At
  refine ⟨c₂ * c₁, ENNReal.mul_pos hc₂.ne' hc₁.ne', ?_⟩
  intro q L hCB z r R₀ R ρ R₃ u D Sp Gp Q B M₁ K₁ W S m' k' bw s₀ s' J t lamT x hu hM₁ huK
    hAp1 hAp2 hSp hGp hQ hs₀ hrR₀ hR₀R hApR hL hD hB hlamT hlamT2 hcor hgap hW hWK hWk hkm hS
    hMQ hs' hrR hRρ hρR₃ hAt hBK hbk hcor2 hgap2 hgap3
  have hRR₃ : R ≤ R₃ := by omega
  have hRL : (R : ℕ∞) ≤ L := le_trans (by exact_mod_cast hRR₃) hL
  have hWL : (W : ℕ∞) ≤ L := le_trans (by exact_mod_cast (show W ≤ R₃ by omega)) hL
  have h₁ := hplan q L hCB z r R₀ R u (2 * u) u M₁ K₁ D Sp Gp Q B s₀ J t lamT x
    (fun i => x i + B) hu le_rfl (by omega) hM₁ huK hAp1 hAp2 hSp hGp hQ hs₀ hrR₀ hR₀R hApR hRL
    hD hB hlamT hlamT2 (fun i => by have := hcor i; push_cast; constructor <;> omega)
    (fun i => le_rfl)
    (fun i l hil ht => by
      obtain ⟨h₁, h₂⟩ := hgap i l hil ht
      exact ⟨fun h => by have := h₁ h; omega, fun h => by have := h₂ h; omega⟩)
  have hs : 2 * (M₁ : ℝ) + 1 ≤ ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) := by
    have : (2 * (M₁ : ℤ) + 1) ≤ 2 * (Q : ℤ) - 1 := by omega
    exact_mod_cast this
  have h₂ := hglue q L hCB z r R ρ R₃ W M₁ K₁ m' k' S ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) s' J t x x
    (fun i => x i + B) x (fun i => x i + bw) hW hWK (by omega) hWk hkm hS hs hs' hrR hRρ hρR₃
    hAt hWL (fun i => ⟨by omega, by omega, by omega, by omega⟩) hcor2 hgap2 hgap3
  refine le_trans ?_ h₂
  rw [mul_assoc c₂ c₁]
  exact mul_le_mul' (mul_le_mul' le_rfl h₁) le_rfl

end Core

end PercLib.Models.Planar
