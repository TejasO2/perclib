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
public import PercLib.Models.Planar.Arms.InnerFarFamily

/-!
# The lower half of quasi-multiplicativity: step S

Nolin's quasi-multiplicativity, lower half: `π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)` for colour
sequences without packs, uniformly under crossing bounds. This file proves its main step: a family
separated at the outer boundary of `B_{⌊ρ/5⌋}(z)` (Theorem 11's outer half) and the far family
separated at the inner boundary of `B_ρ(z)` (the inner separation step) glue into arms from
`B_{r₁}(z)` to `∂B_{r₃}(z)` at a constant cost. The induction on scales that turns it into
quasi-multiplicativity is in `Extendability.lean`.

## Main results

* `exists_strictMono_comp_finRotate_pow`: rotating the indices of a cyclically ordered family so
  that its positions increase.
* `exists_pos_mul_le_law_of_plan_two_sided`: the motion plan carries a family separated at the
  outer boundary of `B_{R₀}(z)` into windows aligned with the starts of a family separated at the
  inner boundary of `B_ρ(z)`, and the two-sided gluing with regions disjoint by colour joins them.
* `exists_pos_mul_le_law_of_far_bins`: the same for a far inner family with starts in given bins,
  in any cyclic order (the rotation of the indices is chosen from a witness).
* `step_scales`, `step_scales_outer`, `step_products`, `step_bound_S`, `step_bounds_core`,
  `step_bounds_budget`, `step_bounds_bins`: the arithmetic of the scales.
* `exists_law_mul_law_far_le`: **step S**, `π(r, ⌊ρ / 5⌋) P(far inner family at ρ) ≤ C π(r, R₃)`.
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
along the indices, rotating the indices (by at most `j` steps) so that the arm of smallest position
comes first makes the positions increasing. -/
theorem exists_strictMono_comp_finRotate_pow {j : ℕ} {P : Fin j → ℤ}
    (hP : ∀ i k l, i < k → k < l → sbtw (P i) (P k) (P l)) (hinj : Function.Injective P) :
    ∃ m : ℕ, m ≤ j ∧ StrictMono fun i => P ((finRotate j ^ m) i) := by
  rcases j with _ | m
  · exact ⟨0, le_rfl, fun i => i.elim0⟩
  obtain ⟨k₀, -, hk₀⟩ := Finset.univ.exists_min_image P Finset.univ_nonempty
  refine ⟨k₀, k₀.isLt.le, fun i l hil => ?_⟩
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

/-! ### One bin assignment -/

/-- **Reindexing the separated event at the outer boundary** by a rotation of the indices. -/
theorem outerSeparatedArmEvent_subset_comp_finRotate_pow {σ : Fin j → Bool} (m : ℕ)
    {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ} :
    outerSeparatedArmEvent σ z r R s M K ⊆ {ω : Config (LatticeSite 2) |
      ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ ((finRotate j ^ m) i)) z r (z - R) (z + R) (γ i)) ∧
      ArmsDisjoint (fun i => σ ((finRotate j ^ m) i)) γ ∧
      (∀ i k l, i < k → k < l →
        sbtw (landingPos (z - R) (z + R) (σ ((finRotate j ^ m) i)) (γ i))
          (landingPos (z - R) (z + R) (σ ((finRotate j ^ m) k)) (γ k))
          (landingPos (z - R) (z + R) (σ ((finRotate j ^ m) l)) (γ l))) ∧
      ArmsOuterSeparated ω (fun i => σ ((finRotate j ^ m) i)) z R s M K γ ∧
      ∀ i, innerPos z r (σ ((finRotate j ^ m) i)) (γ i) ∈ (fun _ => univ : Fin j → Set ℤ) i} := by
  rintro ω ⟨a, b, γ, hγ, hd, ho, hs⟩
  exact ⟨fun i => a ((finRotate j ^ m) i), fun i => b ((finRotate j ^ m) i),
    fun i => γ ((finRotate j ^ m) i), fun i => hγ _, hd.comp_perm _,
    sbtw_comp_finRotate_pow m (f := fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ho,
    ⟨fun i k hik => hs.1 _ _ ((finRotate j ^ m).injective.ne hik), fun i mm => hs.2.1 _ mm,
      fun i => hs.2.2 _⟩, fun _ => mem_univ _⟩

/-- **Step S for one bin assignment.** For a colour sequence `σ` without packs and integers `Ap`,
`At`, `n` there is `c₀ > 0` such that for every law with crossing bounds `c` up to scale `L`: the
separated event at the outer boundary of `B_{R₀}(z)` (fences `(2u, u)`) and the family separated at
the inner boundary of `B_ρ(z)` (separation `s'`, fences `(m', k')`) whose starts are at least
`N + 1` from the ends of their sides and lie in the windows `[x i, x i + k']` of the sides `t i`
satisfy `c₀ P(first) P(second) ≤ π(r, R₃)`. A witness of the second event fixes the cyclic order of
the windows; a rotation of the indices makes it the linear order of the motion plan, and the
windows have the margins and gaps that `exists_pos_mul_le_law_of_plan_two_sided` asks for (corridor
width `W = u`, `S = M₁ + K₁ + m' + k' + 2`, `R + S + 1 = ρ`) once `m'` and `N` are large against the
other parameters (the last seven inequalities). The hypotheses are those of the core step, passed
through (the reason for their number); the arithmetic is done by the caller. -/
theorem exists_pos_mul_le_law_of_far_bins (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (Ap At n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2)
      (r R₀ R ρ R₃ N u D Sp Gp Q B M₁ K₁ S m' k' : ℕ) (s₀ s' : ℝ) (t : Fin j → Fin 4)
      (x : Fin j → ℤ),
      1 ≤ u → 2 ≤ M₁ → u + K₁ ≤ M₁ → u + 2 * u ≤ Ap * (2 * u - 1) →
      u + 2 * K₁ ≤ Ap * (M₁ - 1) → u + 2 * D + 2 * (2 * u) + 2 * u + 3 ≤ Sp →
      Sp + 2 * (12 * j) * u ≤ Gp → u + 2 * (2 * u) + 2 * K₁ + 3 ≤ Q →
      ((2 * Gp + 4 * u + 2 : ℕ) : ℝ) ≤ s₀ → r + 2 * u + 1 < R₀ →
      R₀ + 12 * j * (Gp + 2 * u + u + 1) + n * (2 * (2 * u) + u + 1) + (2 * u + M₁ + u + 1) ≤ R →
      2 * R + 2 ≤ Ap * u → (R₃ : ℕ∞) ≤ L → 2 * R + 2 * n + n * u ≤ n * D →
      n + (2 * (12 * j) + 2 * n + 3) * u ≤ B →
      u ≤ K₁ → u ≤ k' → k' ≤ m' → S = M₁ + K₁ + m' + k' + 2 → R + S + 1 = ρ → M₁ + 1 ≤ Q →
      4 * (m' : ℝ) ≤ s' → 2 * (m' : ℝ) + 2 ≤ s' → 1 ≤ m' → r + M₁ + 1 < R →
      2 * ρ + 2 ≤ R₃ → ρ ≤ R + At * u → B ≤ K₁ →
      2 * (B + Sp + Q + k') + 1 ≤ 4 * m' → 2 * (u + S + 1 + k') + 1 ≤ 4 * m' →
      2 * (u + 2 * S + 1 + k') + 1 ≤ 8 * m' →
      S + 1 + (Sp + Q + 2 * u + M₁ + u + 1) + k' ≤ N →
      S + 1 + (Sp + Q + 2 * u + M₁ + u + 1) + B ≤ N → 3 * S + k' ≤ N → u + 3 * S ≤ N →
      c₀ * law q (outerSeparatedArmEvent σ z r R₀ s₀ (2 * u) u) *
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z ρ (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
            (landingPos (z - R₃) (z + R₃) (σ k) (γ k))
            (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
          ArmsInnerSeparated ω σ z ρ s' m' k' γ ∧
          (∀ i, (z 0 - ρ + N + 1 ≤ a i 0 ∧ a i 0 + N + 1 ≤ z 0 + ρ) ∨
            (z 1 - ρ + N + 1 ≤ a i 1 ∧ a i 1 + N + 1 ≤ z 1 + ρ)) ∧
          ∀ i, (t i = 0 ∧ a i 1 = z 1 + ρ ∧ x i ≤ a i 0 ∧ a i 0 ≤ x i + k') ∨
            (t i = 1 ∧ a i 0 = z 0 + ρ ∧ x i ≤ a i 1 ∧ a i 1 ≤ x i + k') ∨
            (t i = 2 ∧ a i 1 = z 1 - ρ - cond (σ i) 0 1 ∧ x i ≤ a i 0 ∧ a i 0 ≤ x i + k') ∨
            (t i = 3 ∧ a i 0 = z 0 - ρ - cond (σ i) 0 1 ∧ x i ≤ a i 1 ∧ a i 1 ≤ x i + k')} ≤
      law q (multiArmEvent σ z r R₃) := by
  classical
  have hrot := fun m : Fin (j + 1) => exists_pos_mul_le_law_of_plan_two_sided
    (fun i => σ ((finRotate j ^ (m : ℕ)) i)) (comp_finRotate_pow_of_noPack hσ m) c Ap At n
  choose cm hcm hstep using hrot
  obtain ⟨m₀, -, hm₀⟩ := Finset.univ.exists_min_image cm Finset.univ_nonempty
  refine ⟨cm m₀, hcm m₀, ?_⟩
  intro q L hCB z r R₀ R ρ R₃ N u D Sp Gp Q B M₁ K₁ S m' k' s₀ s' t x hu hM₁ huK hAp1 hAp2 hSp
    hGp hQ hs₀ hrR₀ hR₀R hApR hL hD hB huK₁ huk hkm hS hRS hMQ hs'4 hs' hm1 hrR h2ρ hAt hBK hP1
    hP2 hP3 hP4 hP5 hP6 hP7
  refine mul_measure_le_of_nonempty fun hne => ?_
  obtain ⟨ω₀, a, b, γ, hγ, hd, ho, hsep, hfar, hbin⟩ := hne
  have hB3 : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆ Icc (z - R₃ + 1) (z + R₃ - 1) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  choose y hy1 hy2 hdat using fun i => exists_side_data (N := N) (hγ i) hB3 (hbin i) (hfar i)
  have hd01 : ∀ i, (0 : ℤ) ≤ cond (σ i) 0 1 ∧ (cond (σ i) 0 1 : ℤ) ≤ 1 := fun i => by
    cases σ i <;> simp
  -- the separation of the inner positions, in integers
  have hsepZ : ∀ i k, i ≠ k →
      (4 * m' : ℤ) ≤ |innerPos z ρ (σ i) (γ i) - innerPos z ρ (σ k) (γ k)| := by
    intro i k hik
    have h := hs'4.trans (hsep.1 i k hik)
    have h' : ((4 * m' : ℤ) : ℝ) ≤
        ((|innerPos z ρ (σ i) (γ i) - innerPos z ρ (σ k) (γ k)| : ℤ) : ℝ) := by
      push_cast at h ⊢
      exact h
    exact_mod_cast h'
  have hoP : ∀ i k l, i < k → k < l → sbtw (innerPos z ρ (σ i) (γ i))
      (innerPos z ρ (σ k) (γ k)) (innerPos z ρ (σ l) (γ l)) :=
    fun i k l hik hkl => (sbtw_innerPos_iff_sbtw_landingPos hB3 hγ hd i k l).2 (ho i k l hik hkl)
  have hinj : Function.Injective fun i => innerPos z ρ (σ i) (γ i) := by
    intro i k hik
    by_contra hne
    have h := hsepZ i k hne
    dsimp only at hik
    rw [hik, sub_self, abs_zero] at h
    omega
  have hsep2 : ∀ i k, i ≠ k → σ i = σ k →
      2 * (4 * m' : ℤ) ≤ |innerPos z ρ (σ i) (γ i) - innerPos z ρ (σ k) (γ k)| :=
    fun i k hik hσik => le_abs_sub_of_eq_colour hσ hoP hsepZ hik hσik
  -- the rotation that makes the inner positions increase
  obtain ⟨m, hmj, hmono⟩ := exists_strictMono_comp_finRotate_pow hoP hinj
  have hpair : ∀ i k, innerPos z ρ (σ i) (γ i) < innerPos z ρ (σ k) (γ k) → ∀ D' G : ℤ,
      D' ≤ |innerPos z ρ (σ i) (γ i) - innerPos z ρ (σ k) (γ k)| → 1 ≤ D' →
      2 * (G + k') + 1 ≤ D' →
      (((6 - (t i : ℕ)) % 4 : ℕ) : ℤ) ≤ (((6 - (t k : ℕ)) % 4 : ℕ) : ℤ) ∧
      (t i = t k → (t i = 1 ∨ t i = 2 → x i + G ≤ x k) ∧ (t i = 0 ∨ t i = 3 → x k + G ≤ x i)) := by
    intro i k hlt D' G hDle hD1 hG
    rw [abs_of_neg (by omega)] at hDle
    exact side_facts_pair ⟨hy1 i, hy2 i⟩ ⟨hy1 k, hy2 k⟩ (hd01 i) (hd01 k) (hdat i) (hdat k)
      (by omega) hD1 hG
  have hlamT : ∀ i, 0 ≤ (((6 - (t ((finRotate j ^ m) i) : ℕ)) % 4 : ℕ) : ℤ) ∧
      (((6 - (t ((finRotate j ^ m) i) : ℕ)) % 4 : ℕ) : ℤ) ≤ 3 ∧
      ((((6 - (t ((finRotate j ^ m) i) : ℕ)) % 4 : ℕ) : ℤ) +
        ((t ((finRotate j ^ m) i) : ℕ) : ℤ)) % 4 = 2 := fun i =>
    (side_facts_single ⟨hy1 _, hy2 _⟩ (hdat _) hRS hP4 hP5 hP6 hP7).1
  have hlamT2 : ∀ i l : Fin j, i ≤ l →
      (((6 - (t ((finRotate j ^ m) i) : ℕ)) % 4 : ℕ) : ℤ) ≤
        (((6 - (t ((finRotate j ^ m) l) : ℕ)) % 4 : ℕ) : ℤ) := by
    intro i l hil
    rcases hil.lt_or_eq with hil | rfl
    · exact (hpair _ _ (hmono hil) (4 * m') 0
        (hsepZ _ _ ((finRotate j ^ m).injective.ne hil.ne)) (by omega) (by omega)).1
    · exact le_rfl
  have hcor : ∀ i, (if t ((finRotate j ^ m) i) = 0 ∨ t ((finRotate j ^ m) i) = 2 then z 0
      else z 1) - R + (Sp + Q + 2 * u + M₁ + u + 1) ≤ x ((finRotate j ^ m) i) ∧
      x ((finRotate j ^ m) i) + B + (Sp + Q + 2 * u + M₁ + u + 1) ≤
        (if t ((finRotate j ^ m) i) = 0 ∨ t ((finRotate j ^ m) i) = 2 then z 0 else z 1) + R :=
    fun i => by
      obtain ⟨-, h, -⟩ := side_facts_single ⟨hy1 _, hy2 _⟩ (hdat ((finRotate j ^ m) i)) hRS hP4
        hP5 hP6 hP7
      push_cast at h
      exact h
  have hcor2 : ∀ i, (if t ((finRotate j ^ m) i) = 0 ∨ t ((finRotate j ^ m) i) = 2 then z 0
      else z 1) - R + 2 * S ≤ x ((finRotate j ^ m) i) ∧
      x ((finRotate j ^ m) i) + u + 2 * S ≤
        (if t ((finRotate j ^ m) i) = 0 ∨ t ((finRotate j ^ m) i) = 2 then z 0 else z 1) + R :=
    fun i => (side_facts_single ⟨hy1 _, hy2 _⟩ (hdat ((finRotate j ^ m) i)) hRS hP4 hP5 hP6
      hP7).2.2
  have hgap : ∀ i l, i < l → t ((finRotate j ^ m) i) = t ((finRotate j ^ m) l) →
      (t ((finRotate j ^ m) i) = 1 ∨ t ((finRotate j ^ m) i) = 2 →
        x ((finRotate j ^ m) i) + B + Sp + Q ≤ x ((finRotate j ^ m) l)) ∧
      (t ((finRotate j ^ m) i) = 0 ∨ t ((finRotate j ^ m) i) = 3 →
        x ((finRotate j ^ m) l) + B + Sp + Q ≤ x ((finRotate j ^ m) i)) := by
    intro i l hil htl
    obtain ⟨-, h⟩ := hpair _ _ (hmono hil) (4 * m') ((B : ℤ) + Sp + Q)
      (hsepZ _ _ ((finRotate j ^ m).injective.ne hil.ne)) (by omega) (by omega)
    obtain ⟨h1, h2⟩ := h htl
    exact ⟨fun h' => by have := h1 h'; omega, fun h' => by have := h2 h'; omega⟩
  -- the gaps between any two windows on one side, in either order
  have hgapG : ∀ i k, i ≠ k → t ((finRotate j ^ m) i) = t ((finRotate j ^ m) k) → ∀ D' G : ℤ,
      D' ≤ |innerPos z ρ (σ ((finRotate j ^ m) i)) (γ ((finRotate j ^ m) i)) -
        innerPos z ρ (σ ((finRotate j ^ m) k)) (γ ((finRotate j ^ m) k))| → 1 ≤ D' →
      2 * (G + k') + 1 ≤ D' →
      x ((finRotate j ^ m) i) + G ≤ x ((finRotate j ^ m) k) ∨
        x ((finRotate j ^ m) k) + G ≤ x ((finRotate j ^ m) i) := by
    intro i k hik htk D' G hDle hD1 hG
    have hne : (finRotate j ^ m) i ≠ (finRotate j ^ m) k := (finRotate j ^ m).injective.ne hik
    rcases lt_or_gt_of_ne (hinj.ne hne) with hlt | hlt
    · obtain ⟨-, h⟩ := hpair _ _ hlt D' G hDle hD1 hG
      obtain ⟨h1, h2⟩ := h htk
      by_cases h12 : t ((finRotate j ^ m) i) = 1 ∨ t ((finRotate j ^ m) i) = 2
      · exact Or.inl (h1 h12)
      · exact Or.inr (h2 (by omega))
    · obtain ⟨-, h⟩ := hpair _ _ hlt D' G (by rw [abs_sub_comm]; exact hDle) hD1 hG
      obtain ⟨h1, h2⟩ := h htk.symm
      by_cases h12 : t ((finRotate j ^ m) k) = 1 ∨ t ((finRotate j ^ m) k) = 2
      · exact Or.inr (h1 h12)
      · exact Or.inl (h2 (by omega))
  have hgap3 : ∀ i k, i ≠ k → t ((finRotate j ^ m) i) = t ((finRotate j ^ m) k) →
      x ((finRotate j ^ m) i) + u + (M₁ + K₁ + m' + k' + 2) < x ((finRotate j ^ m) k) ∨
        x ((finRotate j ^ m) k) + u + (M₁ + K₁ + m' + k' + 2) < x ((finRotate j ^ m) i) := by
    intro i k hik htk
    have h := hgapG i k hik htk (4 * m') ((u : ℤ) + S + 1)
      (hsepZ _ _ ((finRotate j ^ m).injective.ne hik)) (by omega) (by omega)
    omega
  have hgap2 : ∀ i k, i ≠ k → σ ((finRotate j ^ m) i) = σ ((finRotate j ^ m) k) →
      t ((finRotate j ^ m) i) = t ((finRotate j ^ m) k) →
      x ((finRotate j ^ m) i) + u + 2 * S < x ((finRotate j ^ m) k) ∨
        x ((finRotate j ^ m) k) + u + 2 * S < x ((finRotate j ^ m) i) := by
    intro i k hik hσik htk
    have h := hgapG i k hik htk (8 * m') ((u : ℤ) + 2 * S + 1)
      (by
        have := hsep2 _ _ ((finRotate j ^ m).injective.ne hik) hσik
        omega) (by omega) (by omega)
    omega
  -- the core step for the rotated family
  have hm : m < j + 1 := by omega
  have key := hstep ⟨m, hm⟩ q L hCB z r R₀ R ρ R₃ u D Sp Gp Q B M₁ K₁ u S m' k' k' s₀ s'
    (fun _ => univ) (fun i => t ((finRotate j ^ m) i))
    (fun i => (((6 - (t ((finRotate j ^ m) i) : ℕ)) % 4 : ℕ) : ℤ))
    (fun i => x ((finRotate j ^ m) i)) hu hM₁ huK hAp1 hAp2 hSp hGp hQ hs₀ hrR₀ hR₀R hApR hL hD
    hB hlamT hlamT2 hcor hgap hu huK₁ huk hkm (by omega) hMQ hs' hrR (by omega) (by omega) hAt
    hBK le_rfl hcor2 hgap2 hgap3
  refine le_trans ?_ (key.trans (measure_mono (multiArmEventTo_comp_finRotate_pow_subset
    (σ := σ) (z := z) (r := r) (lo := z - R₃) (hi := z + R₃) (J := fun _ => univ)
    (I := fun _ => univ) m)))
  refine mul_le_mul' (mul_le_mul' (hm₀ _ (Finset.mem_univ _)) (measure_mono ?_)) (measure_mono ?_)
  · exact outerSeparatedArmEvent_subset_comp_finRotate_pow m
  · rintro ω ⟨a, b, γ, hγ, hd, ho, hsep, -, hbin⟩
    exact ⟨fun i => a ((finRotate j ^ m) i), fun i => b ((finRotate j ^ m) i),
      fun i => γ ((finRotate j ^ m) i), fun i => hγ _, hd.comp_perm _,
      sbtw_comp_finRotate_pow m (f := fun i => landingPos (z - R₃) (z + R₃) (σ i) (γ i)) ho,
      ⟨fun i k hik => hsep.1 _ _ ((finRotate j ^ m).injective.ne hik), fun i mm => hsep.2.1 _ mm,
        fun i => hsep.2.2 _⟩, fun i => hbin _⟩

end Core

/-! ### The arithmetic of step S -/

section StepBounds

variable {j w E n N ρ m k R₀ u R Rn r : ℕ}

/-- **The scales of step S, first part.** With `n = 1000 (j + 1)² (w + 1) E`, the inner radius
`2ρ + 1 = wN`, the first family's radius `R₀ = ⌊ρ / 5⌋` and unit `u = ⌊R₀ / n²⌋`, and the inner
fences `m ≥ ⌊N / E⌋`, `k ≥ ⌊N / E²⌋`: the unit is at least `n`, and `n u`, `u` are tiny against
`m`, `k`. -/
theorem step_scales (hn : n = 1000 * (j + 1) * (j + 1) * (w + 1) * E) (hE : 1 ≤ E)
    (hρ : 2 * ρ + 1 = w * N) (hR₀ : R₀ = ρ / 5) (hu : u = R₀ / (n * n)) (hm1 : N / E ≤ m)
    (hk1 : N / (E * E) ≤ k) (hbig : 5 * (n * (n * n)) ≤ ρ) (hNE : E * E ≤ N) :
    1000 * (j + 1) * (j + 1) ≤ n ∧ 1000 * ((w + 1) * E) ≤ n ∧ n ≤ u ∧
      10000 * (n * u) ≤ m ∧ 10000 * u ≤ k ∧ 1 ≤ k ∧ N + 1 ≤ E * (m + 1) ∧
      N + 1 ≤ E * E * (k + 1) ∧ n * n * u ≤ R₀ ∧ 5 * R₀ ≤ ρ ∧
      ρ < 5 * (n * n * u) + 5 * (n * n) + 5 := by
  have hj1 : 1 ≤ (j + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hwE : 1 ≤ (w + 1) * E := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hn1 : 1000 * (j + 1) * (j + 1) ≤ n := by
    rw [hn]
    calc 1000 * (j + 1) * (j + 1) = 1000 * (j + 1) * (j + 1) * 1 := by ring
      _ ≤ 1000 * (j + 1) * (j + 1) * ((w + 1) * E) := Nat.mul_le_mul_left _ hwE
      _ = _ := by ring
  have hnwE : 1000 * ((w + 1) * E) ≤ n := by
    rw [hn]
    calc 1000 * ((w + 1) * E) = 1000 * 1 * ((w + 1) * E) := by ring
      _ ≤ 1000 * ((j + 1) * (j + 1)) * ((w + 1) * E) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hj1)
      _ = _ := by ring
  have hn1000 : 1000 ≤ n := le_trans (by nlinarith) hn1
  have hnn : 0 < n * n := by positivity
  have hEn : E ≤ n := le_trans (by nlinarith) hnwE
  have h5R₀ : 5 * R₀ ≤ ρ := by rw [hR₀]; omega
  have hR₀' : ρ < 5 * R₀ + 5 := by rw [hR₀]; omega
  have huR : n * n * u ≤ R₀ := by rw [hu, mul_comm]; exact Nat.div_mul_le_self R₀ (n * n)
  have huR' : R₀ < n * n * (u + 1) := by
    have := Nat.lt_div_mul_add (a := R₀) hnn
    rw [← hu] at this
    linarith
  have hnu : n ≤ u := by
    rw [hu, Nat.le_div_iff_mul_le hnn]
    have : n * (n * n) ≤ R₀ := by
      rw [hR₀, Nat.le_div_iff_mul_le (by norm_num)]
      linarith
    linarith
  have hNm : N + 1 ≤ E * (m + 1) := by
    have h := Nat.lt_div_mul_add (a := N) (show 0 < E by omega)
    have := Nat.mul_le_mul_right E hm1
    linarith
  have hNk : N + 1 ≤ E * E * (k + 1) := by
    have h := Nat.lt_div_mul_add (a := N) (show 0 < E * E by positivity)
    have := Nat.mul_le_mul_right (E * E) hk1
    linarith
  have hwN := Nat.mul_le_mul_left w hNm
  have hwNk := Nat.mul_le_mul_left w hNk
  -- `n u` against `m`
  have hb2 : 10000 * (n * u) ≤ m := by
    have h1 : 1000 * ((w + 1) * E) * (n * u) ≤ n * (n * u) := Nat.mul_le_mul_right _ hnwE
    have h2 : (w + 1) * E * (10000 * (n * u)) < (w + 1) * E * (m + 1) := by
      have z1 := Nat.zero_le (E * m)
      have z2 := Nat.zero_le E
      nlinarith
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  -- `u` against `k`
  have hb4 : 10000 * u ≤ k := by
    have hnn2 : 1000 * ((w + 1) * (E * E)) ≤ n * n := by
      have := Nat.mul_le_mul hnwE hEn
      calc 1000 * ((w + 1) * (E * E)) = 1000 * ((w + 1) * E) * E := by ring
        _ ≤ n * n := this
    have h1 : 1000 * ((w + 1) * (E * E)) * u ≤ n * n * u := Nat.mul_le_mul_right _ hnn2
    have h2 : (w + 1) * (E * E) * (10000 * u) < (w + 1) * (E * E) * (k + 1) := by
      have z1 := Nat.zero_le (E * E * k)
      have z2 := Nat.zero_le (E * E)
      nlinarith
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  have hk1' : 1 ≤ k := le_trans (by rw [Nat.le_div_iff_mul_le (by positivity)]; linarith) hk1
  refine ⟨hn1, hnwE, hnu, hb2, hb4, hk1', hNm, hNk, huR, h5R₀, ?_⟩
  nlinarith

/-- **The scales of step S, second part**: the jog bound's quotient `Rn = ⌊R / n⌋` of the gluing
radius `R ≤ ρ` is tiny against `m` and bounded by `5 n u + 5 n`. -/
theorem step_scales_outer (hρ : 2 * ρ + 1 = w * N) (hnwE : 1000 * ((w + 1) * E) ≤ n)
    (hNm : N + 1 ≤ E * (m + 1)) (hρu : ρ < 5 * (n * n * u) + 5 * (n * n) + 5)
    (hn1000 : 1000 ≤ n) (hRρ : R ≤ ρ) (hRn : Rn = R / n) :
    n * Rn ≤ R ∧ R < n * (Rn + 1) ∧ 1000 * Rn ≤ m ∧ Rn ≤ 5 * (n * u) + 5 * n := by
  have hn0 : 0 < n := by omega
  have hRn1 : n * Rn ≤ R := by rw [hRn, mul_comm]; exact Nat.div_mul_le_self R n
  have hRn2 : R < n * (Rn + 1) := by
    have := Nat.lt_div_mul_add (a := R) hn0
    rw [← hRn] at this
    linarith
  have hwN := Nat.mul_le_mul_left w hNm
  have hb3 : 1000 * Rn ≤ m := by
    have h1 : 1000 * ((w + 1) * E) * Rn ≤ n * Rn := Nat.mul_le_mul_right _ hnwE
    have h2 : (w + 1) * E * (2000 * Rn) < (w + 1) * E * (m + 1) := by
      have z1 := Nat.zero_le (E * m)
      have z2 := Nat.zero_le E
      nlinarith
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  have hb5 : Rn ≤ 5 * (n * u) + 5 * n := by
    have h : n * Rn < n * (5 * (n * u) + 5 * n + 1) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_left h
    omega
  exact ⟨hRn1, hRn2, hb3, hb5⟩

/-- **Products of the scales of step S** that the linear arithmetic below uses: `j`, `j²`, `u` and
`n` are tiny against `n`, `n u` and `n² u` once `n ≥ 1000 (j + 1)²` and `n ≤ u`. -/
theorem step_products (hn1 : 1000 * (j + 1) * (j + 1) ≤ n) (hnu : n ≤ u) :
    1000 ≤ n ∧ 1000 * j ≤ n ∧ 1 ≤ u ∧ 1000 * (j * u) ≤ n * u ∧ 1000 * (j * (j * u)) ≤ n * u ∧
      1000 * u ≤ n * u ∧ 1000 * n ≤ n * u ∧ 1000 * (n * u) ≤ n * n * u ∧ n * n ≤ n * n * u ∧
      1000 * (j * Rn) ≤ n * Rn := by
  have hn1000 : 1000 ≤ n := le_trans (by nlinarith) hn1
  have hj1000 : 1000 * j ≤ n := le_trans (by nlinarith) hn1
  have hjj : 1000 * (j * j) ≤ n := le_trans (by nlinarith) hn1
  have hu1 : 1 ≤ u := by omega
  refine ⟨hn1000, hj1000, hu1, ?_, ?_, ?_, ?_, ?_, Nat.le_mul_of_pos_right _ hu1, ?_⟩
  · have := Nat.mul_le_mul_right u hj1000
    linarith
  · have := Nat.mul_le_mul_right u hjj
    linarith
  · have := Nat.mul_le_mul_right u hn1000
    linarith
  · have := Nat.mul_le_mul_left n (le_trans hn1000 hnu)
    linarith
  · have := Nat.mul_le_mul_right (n * u) hn1000
    linarith
  · have := Nat.mul_le_mul_right Rn hj1000
    linarith

/-- **The arithmetic of step S: the room `S`.** With `K₁ = (2n + 24j + 5) u` and
`S = M₁ + K₁ + m + k + 2`, `M₁ = 2K₁`: `S + 1 ≤ N ≤ ρ`. -/
theorem step_bound_S {K₁ M₁ S : ℕ} (hn1 : 1000 * (j + 1) * (j + 1) ≤ n) (hnu : n ≤ u)
    (hb2 : 10000 * (n * u) ≤ m) (hk2 : 16 * k ≤ m) (hm2 : 16 * m ≤ N) (hk1 : 1 ≤ k)
    (h7N : 7 * N ≤ 2 * ρ + 1) (hK₁ : K₁ = (2 * n + 24 * j + 5) * u) (hM₁ : M₁ = 2 * K₁)
    (hS : S = M₁ + K₁ + m + k + 2) :
    S + 1 ≤ N ∧ N ≤ ρ ∧ K₁ ≤ 3 * (n * u) := by
  obtain ⟨-, -, -, hju, -, hu1000, -, -, -, -⟩ := step_products (Rn := 0) hn1 hnu
  have hK : K₁ = 2 * (n * u) + 24 * (j * u) + 5 * u := by rw [hK₁]; ring
  refine ⟨?_, by omega, by omega⟩
  omega

/-- **The arithmetic of step S: the hypotheses of the core step.** With the choices of §21.4
item 6 (`K₁ = (2n + 24j + 5) u`, `M₁ = 2K₁`, `B = (2n + 24j + 4) u`, `S = M₁ + K₁ + m + k + 2`,
`R + S + 1 = ρ`, jog bound `D = 2 Rn + u + 4`, rooms `Sp`, `Gp`, `Q`, `Ap = 32 n² + 2`,
`At = 4n² + 6n + 72j + 15`), the numerical hypotheses of `exists_pos_mul_le_law_of_far_bins` other
than the gluing budget and the bins. -/
theorem step_bounds_core {K₁ M₁ B S D Sp Gp Q : ℕ} (hn1 : 1000 * (j + 1) * (j + 1) ≤ n)
    (hnu : n ≤ u) (hb2 : 10000 * (n * u) ≤ m) (hk2 : 16 * k ≤ m) (hm2 : 16 * m ≤ N)
    (h7N : 7 * N ≤ 2 * ρ + 1) (hR₀' : ρ < 5 * R₀ + 5)
    (hρu : ρ < 5 * (n * n * u) + 5 * (n * n) + 5) (hRn2 : R < n * (Rn + 1))
    (hb5 : Rn ≤ 5 * (n * u) + 5 * n) (hr : 40 * r ≤ ρ)
    (hK₁ : K₁ = (2 * n + 24 * j + 5) * u) (hM₁ : M₁ = 2 * K₁) (hB : B = (2 * n + 24 * j + 4) * u)
    (hS : S = M₁ + K₁ + m + k + 2) (hRS : R + S + 1 = ρ) (hD : D = 2 * Rn + u + 4)
    (hSp : Sp = u + 2 * D + 2 * (2 * u) + 2 * u + 3) (hGp : Gp = Sp + 2 * (12 * j) * u)
    (hQ : Q = u + 2 * (2 * u) + 2 * K₁ + 3) :
    u + 2 * u ≤ (32 * (n * n) + 2) * (2 * u - 1) ∧
      u + 2 * K₁ ≤ (32 * (n * n) + 2) * (M₁ - 1) ∧ r + 2 * u + 1 < R₀ ∧
      2 * R + 2 ≤ (32 * (n * n) + 2) * u ∧ 2 * R + 2 * n + n * u ≤ n * D ∧
      n + (2 * (12 * j) + 2 * n + 3) * u ≤ B ∧ r + M₁ + 1 < R ∧
      ρ ≤ R + (4 * (n * n) + 6 * n + 72 * j + 15) * u ∧
      2 * Gp + 4 * u + 2 + 1 ≤ 2 * ((64 * n + 24 * j + 24) * u) ∧ u ≤ K₁ ∧ B ≤ K₁ ∧
      M₁ + 1 ≤ Q ∧ 2 ≤ M₁ := by
  obtain ⟨hn1000, hj1000, hu1, hju, -, hu1000, hnun, hnnu, hnn1, -⟩ :=
    step_products (Rn := Rn) hn1 hnu
  have hK : K₁ = 2 * (n * u) + 24 * (j * u) + 5 * u := by rw [hK₁]; ring
  have hB' : B = 2 * (n * u) + 24 * (j * u) + 4 * u := by rw [hB]; ring
  have hK3 : K₁ ≤ 3 * (n * u) := by omega
  have huK : u ≤ K₁ := by omega
  have hRρ : R ≤ ρ := by omega
  have hAp : 3 ≤ 32 * (n * n) + 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, huK, by omega, by omega, by omega⟩
  · have h1 : u ≤ 2 * u - 1 := by omega
    have := Nat.mul_le_mul_left (32 * (n * n) + 2) h1
    have := Nat.mul_le_mul_right u hAp
    linarith
  · have h1 : K₁ ≤ M₁ - 1 := by omega
    have := Nat.mul_le_mul_left (32 * (n * n) + 2) h1
    have := Nat.mul_le_mul_right K₁ hAp
    linarith
  · have : 8 * r ≤ R₀ := by omega
    linarith
  · linarith
  · rw [hD]
    linarith
  · rw [hB']
    linarith
  · omega
  · have : (4 * (n * n) + 6 * n + 72 * j + 15) * u =
        4 * (n * n * u) + 3 * (2 * (n * u) + 24 * (j * u) + 5 * u) := by ring
    rw [this]
    omega
  · have : 2 * ((64 * n + 24 * j + 24) * u) = 128 * (n * u) + 48 * (j * u) + 48 * u := by ring
    rw [this, hGp, hSp, hD]
    have : 2 * (12 * j) * u = 24 * (j * u) := by ring
    rw [this]
    linarith

/-- **The arithmetic of step S: the budget of the motion plan.** The plan carries the first family
from `∂B_{R₀}(z)` to `∂B_R(z)`, `R₀ = ⌊ρ / 5⌋`, `R + S + 1 = ρ`, within its radius budget. -/
theorem step_bounds_budget {K₁ M₁ S D Sp Gp : ℕ} (hn1 : 1000 * (j + 1) * (j + 1) ≤ n)
    (hnu : n ≤ u) (hk2 : 16 * k ≤ m) (hm2 : 16 * m ≤ N)
    (h7N : 7 * N ≤ 2 * ρ + 1) (h5R₀ : 5 * R₀ ≤ ρ) (huR : n * n * u ≤ R₀) (hRn1 : n * Rn ≤ R)
    (hK₁ : K₁ = (2 * n + 24 * j + 5) * u) (hM₁ : M₁ = 2 * K₁)
    (hS : S = M₁ + K₁ + m + k + 2) (hRS : R + S + 1 = ρ) (hD : D = 2 * Rn + u + 4)
    (hSp : Sp = u + 2 * D + 2 * (2 * u) + 2 * u + 3) (hGp : Gp = Sp + 2 * (12 * j) * u) :
    R₀ + 12 * j * (Gp + 2 * u + u + 1) + n * (2 * (2 * u) + u + 1) + (2 * u + M₁ + u + 1) ≤
      R := by
  obtain ⟨hn1000, hj1000, hu1, hju, hjju, hu1000, hnun, hnnu, -, hjRn⟩ :=
    step_products (Rn := Rn) hn1 hnu
  have hK : K₁ = 2 * (n * u) + 24 * (j * u) + 5 * u := by rw [hK₁]; ring
  have hjG : 12 * j * (Gp + 2 * u + u + 1) =
      48 * (j * Rn) + 144 * (j * u) + 288 * (j * (j * u)) + 144 * j := by
    rw [hGp, hSp, hD]
    ring
  have hnG : n * (2 * (2 * u) + u + 1) = 5 * (n * u) + n := by ring
  rw [hjG, hnG]
  omega

/-- **The arithmetic of step S: the bins.** The windows of width `k` around the starts of the far
family (separation `4m`, at least `N + 1` from the ends of the sides) have the gaps and margins
that `exists_pos_mul_le_law_of_far_bins` asks for. -/
theorem step_bounds_bins {K₁ M₁ B S D Sp Q : ℕ} (hn1 : 1000 * (j + 1) * (j + 1) ≤ n)
    (hnu : n ≤ u) (hb2 : 10000 * (n * u) ≤ m) (hk1 : 1 ≤ k) (hk2 : 16 * k ≤ m)
    (hm2 : 16 * m ≤ N) (hb3 : 1000 * Rn ≤ m) (hK₁ : K₁ = (2 * n + 24 * j + 5) * u)
    (hM₁ : M₁ = 2 * K₁) (hB : B = (2 * n + 24 * j + 4) * u) (hS : S = M₁ + K₁ + m + k + 2)
    (hD : D = 2 * Rn + u + 4) (hSp : Sp = u + 2 * D + 2 * (2 * u) + 2 * u + 3)
    (hQ : Q = u + 2 * (2 * u) + 2 * K₁ + 3) :
    2 * (B + Sp + Q + k) + 1 ≤ 4 * m ∧ 2 * (u + S + 1 + k) + 1 ≤ 4 * m ∧
      2 * (u + 2 * S + 1 + k) + 1 ≤ 8 * m ∧
      S + 1 + (Sp + Q + 2 * u + M₁ + u + 1) + k ≤ N ∧
      S + 1 + (Sp + Q + 2 * u + M₁ + u + 1) + B ≤ N ∧ 3 * S + k ≤ N ∧ u + 3 * S ≤ N ∧
      1 ≤ m := by
  obtain ⟨hn1000, hj1000, hu1, hju, -, hu1000, hnun, -, -, -⟩ :=
    step_products (Rn := Rn) hn1 hnu
  have hK : K₁ = 2 * (n * u) + 24 * (j * u) + 5 * u := by rw [hK₁]; ring
  have hB' : B = 2 * (n * u) + 24 * (j * u) + 4 * u := by rw [hB]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end StepBounds

/-! ### Step S -/

section StepS

variable {j : ℕ}

/-- **Step S** (the first family at `⌊ρ / 5⌋` against the far inner family at `ρ`). For a colour
sequence `σ` without packs, `0 < η ≤ 1 / 256` and `w ≥ 7` there are `C < ⊤` and `r₀` such that for
every law with crossing bounds `c` up to scale `L`, `2ρ + 1 = wN`, `r₀ ≤ r`, `40 r ≤ ρ`,
`2ρ + 2 ≤ R₃ ≤ L`: `π(r, ⌊ρ / 5⌋) P(far inner family at ρ) ≤ C π(r, R₃)`, where the far inner
family is separated at the inner boundary of `B_ρ(z)` with the parameters of the inner step
(`4 √η N`, `⌊√η N⌋`, `⌊η N⌋`) and every start at least `N + 1` from the ends of its side.

Proof: Theorem 11's outer half, separated form, at `R₀ = ⌊ρ / 5⌋` (unit `u = ⌊R₀ / n²⌋`,
`n = 1000 (j + 1)² (w + 1) ⌈1 / √η⌉`); the starts of the far family in one of `(4NB)^j`
assignments of bins of width `⌊η N⌋ + 1` (`NB = w ⌈1 / √η⌉²`); for each, the motion plan into
windows aligned with the bins and the two-sided gluing (`exists_pos_mul_le_law_of_far_bins`, with
the scales of §21.4 item 6). -/
theorem exists_law_mul_law_far_le (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 256) {w : ℕ} (hw : 7 ≤ w) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N ρ R₃ : ℕ), 2 * ρ + 1 = w * N →
      r₀ ≤ r → 40 * r ≤ ρ → 2 * ρ + 2 ≤ R₃ → (R₃ : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r (ρ / 5)) * law q {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z ρ (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
          (landingPos (z - R₃) (z + R₃) (σ k) (γ k))
          (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z ρ (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ γ ∧
        ∀ i, (z 0 - ρ + N + 1 ≤ a i 0 ∧ a i 0 + N + 1 ≤ z 0 + ρ) ∨
          (z 1 - ρ + N + 1 ≤ a i 1 ∧ a i 1 + N + 1 ≤ z 1 + ρ)} ≤
        C * law q (multiArmEvent σ z r R₃) := by
  classical
  -- the integer scale `E ≥ 1 / √η` and the unit `n`
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = ⌈1 / Real.sqrt η⌉₊ := ⟨_, rfl⟩
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hEs : 1 ≤ (E : ℝ) * Real.sqrt η := by
    have : 1 / Real.sqrt η ≤ E := hE ▸ Nat.le_ceil _
    rw [div_le_iff₀ hs] at this
    exact this
  have hE1 : 1 ≤ E := by
    rw [hE, Nat.one_le_ceil_iff]
    positivity
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 1000 * (j + 1) * (j + 1) * (w + 1) * E := ⟨_, rfl⟩
  have hn' : 1000 * (j + 1) * (j + 1) ≤ n := by
    rw [hn]
    calc 1000 * (j + 1) * (j + 1) = 1000 * (j + 1) * (j + 1) * 1 * 1 := by ring
      _ ≤ 1000 * (j + 1) * (j + 1) * (w + 1) * E := by gcongr; omega
  obtain ⟨C₁, hC₁, r₁, hsep⟩ := exists_law_multiArmEvent_le_law_outerSeparated σ hσ c hn'
  obtain ⟨c₀, hc₀, hbin⟩ := exists_pos_mul_le_law_of_far_bins σ hσ c (32 * (n * n) + 2)
    (4 * (n * n) + 6 * n + 72 * j + 15) n
  obtain ⟨NB, hNB⟩ : ∃ NB : ℕ, NB = w * (E * E) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, d = min c₀ 1 := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := (hd ▸ lt_min hc₀ one_pos).ne'
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hd ▸ min_le_right _ _)
  have hdc : d ≤ c₀ := hd ▸ min_le_left _ _
  refine ⟨C₁ * ((4 * NB : ℝ≥0∞) ^ j * d⁻¹), ENNReal.mul_ne_top hC₁
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top NB))) (ENNReal.inv_ne_top.2 hd0)),
    max r₁ (n * (n * n) + w * (E * E) + 1), ?_⟩
  intro q L hCB z r N ρ R₃ hρ hr hrρ h2ρ hL
  have hr₁ : r₁ ≤ r := le_trans (le_max_left _ _) hr
  have hr₂ : n * (n * n) + w * (E * E) + 1 ≤ r := le_trans (le_max_right _ _) hr
  -- the scales
  have hbig : 5 * (n * (n * n)) ≤ ρ := by omega
  have hNE : E * E ≤ N := by
    have h2 : w * (E * E) ≤ w * N := by omega
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  obtain ⟨hm1, hm2, hk1, hk2, -, hs4, hs2⟩ := floor_sqrt_mul_bounds hη hη1 hEs hNE
  set m := ⌊Real.sqrt η * N⌋₊ with hm
  set k := ⌊η * N⌋₊ with hk
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = ρ / 5 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = R₀ / (n * n) := ⟨_, rfl⟩
  obtain ⟨hn1, hnwE, hnu, hb2, hb4, hk1', hNm, hNk, huR, h5R₀, hρu⟩ :=
    step_scales hn hE1 hρ hR₀ hu hm1 hk1 hbig hNE
  obtain ⟨hn1000, -, hu1, -, -, -, -, -, -, -⟩ := step_products (Rn := 0) hn1 hnu
  have h7N : 7 * N ≤ 2 * ρ + 1 := by rw [hρ]; exact Nat.mul_le_mul_right N hw
  have hR₀' : ρ < 5 * R₀ + 5 := by omega
  -- the bins
  obtain ⟨X, hX⟩ : ∃ X : Fin 4 × Fin NB → ℤ, ∀ p, X p =
      (if p.1 = 0 ∨ p.1 = 2 then z 0 else z 1) - ρ - 1 + ((p.2 : ℕ) : ℤ) * (k + 1) :=
    ⟨fun p => (if p.1 = 0 ∨ p.1 = 2 then z 0 else z 1) - ρ - 1 + ((p.2 : ℕ) : ℤ) * (k + 1),
      fun _ => rfl⟩
  have hB3 : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆ Icc (z - R₃ + 1) (z + R₃ - 1) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  have hNB' : 2 * ρ + 1 < NB * (k + 1) := by
    have h₁ := Nat.mul_le_mul_left w hNk
    have h₂ : w * (E * E * (k + 1)) = NB * (k + 1) := by rw [hNB]; ring
    have h₃ : w * (N + 1) = w * N + w := by ring
    omega
  have hcover : {ω : Config (LatticeSite 2) |
      ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z ρ (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
        (landingPos (z - R₃) (z + R₃) (σ k) (γ k))
        (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
      ArmsInnerSeparated ω σ z ρ (4 * Real.sqrt η * N) m k γ ∧
      ∀ i, (z 0 - ρ + N + 1 ≤ a i 0 ∧ a i 0 + N + 1 ≤ z 0 + ρ) ∨
        (z 1 - ρ + N + 1 ≤ a i 1 ∧ a i 1 + N + 1 ≤ z 1 + ρ)} ⊆
      ⋃ p : Fin j → Fin 4 × Fin NB, {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z ρ (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
          (landingPos (z - R₃) (z + R₃) (σ k) (γ k))
          (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z ρ (4 * Real.sqrt η * N) m k γ ∧
        (∀ i, (z 0 - ρ + N + 1 ≤ a i 0 ∧ a i 0 + N + 1 ≤ z 0 + ρ) ∨
          (z 1 - ρ + N + 1 ≤ a i 1 ∧ a i 1 + N + 1 ≤ z 1 + ρ)) ∧
        ∀ i, ((p i).1 = 0 ∧ a i 1 = z 1 + ρ ∧ X (p i) ≤ a i 0 ∧ a i 0 ≤ X (p i) + k) ∨
          ((p i).1 = 1 ∧ a i 0 = z 0 + ρ ∧ X (p i) ≤ a i 1 ∧ a i 1 ≤ X (p i) + k) ∨
          ((p i).1 = 2 ∧ a i 1 = z 1 - ρ - cond (σ i) 0 1 ∧ X (p i) ≤ a i 0 ∧
            a i 0 ≤ X (p i) + k) ∨
          ((p i).1 = 3 ∧ a i 0 = z 0 - ρ - cond (σ i) 0 1 ∧ X (p i) ≤ a i 1 ∧
            a i 1 ≤ X (p i) + k)} := by
    rintro ω ⟨a, b, γ, hγ, hd, ho, hsep, hfar⟩
    obtain ⟨p, hp⟩ := exists_bin_assignment (σ := σ) hγ hB3 hNB' hX
    exact mem_iUnion.2 ⟨p, a, b, γ, hγ, hd, ho, hsep, hfar, hp⟩
  -- the parameters of the plan and of the gluing
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = (2 * n + 24 * j + 5) * u := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, M₁ = 2 * K₁ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (2 * n + 24 * j + 4) * u := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = M₁ + K₁ + m + k + 2 := ⟨_, rfl⟩
  obtain ⟨hS1, hNρ, -⟩ := step_bound_S hn1 hnu hb2 hk2 hm2 hk1' h7N hK₁ hM₁ hS
  obtain ⟨R, hR⟩ : ∃ R, R = ρ - (S + 1) := ⟨_, rfl⟩
  have hRS : R + S + 1 = ρ := by omega
  obtain ⟨Rn, hRn⟩ : ∃ Rn, Rn = R / n := ⟨_, rfl⟩
  obtain ⟨hRn1, hRn2, hb3, hb5⟩ :=
    step_scales_outer hρ hnwE hNm hρu hn1000 (by omega : R ≤ ρ) hRn
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * Rn + u + 4 := ⟨_, rfl⟩
  obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = u + 2 * D + 2 * (2 * u) + 2 * u + 3 := ⟨_, rfl⟩
  obtain ⟨Gp, hGp⟩ : ∃ Gp, Gp = Sp + 2 * (12 * j) * u := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = u + 2 * (2 * u) + 2 * K₁ + 3 := ⟨_, rfl⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := step_bounds_core hn1 hnu
    hb2 hk2 hm2 h7N hR₀' hρu hRn2 hb5 hrρ hK₁ hM₁ hB hS hRS hD hSp hGp hQ
  have c14 := step_bounds_budget hn1 hnu hk2 hm2 h7N h5R₀ huR hRn1 hK₁ hM₁ hS hRS hD hSp hGp
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
    step_bounds_bins hn1 hnu hb2 hk1' hk2 hm2 hb3 hK₁ hM₁ hB hS hD hSp hQ
  have hs₀ : ((2 * Gp + 4 * u + 2 : ℕ) : ℝ) ≤
      ((2 * (((64 * n + 24 * j + 24) * u : ℕ) : ℤ) - 1 : ℤ) : ℝ) := by
    have h' : ((2 * Gp + 4 * u + 2 : ℕ) : ℤ) ≤
        2 * (((64 * n + 24 * j + 24) * u : ℕ) : ℤ) - 1 := by
      have := c9
      omega
    calc _ = (((2 * Gp + 4 * u + 2 : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
      _ ≤ _ := Int.cast_le.2 h'
  -- Theorem 11, outer half, separated form, at `R₀`
  have hR₀L : (R₀ : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R₀ ≤ R₃)) hL
  have h1 := hsep q L hCB z r R₀ hr₁ (by omega) hR₀L
  rw [← hu] at h1
  rw [← hR₀]
  have hstep : ∀ p : Fin j → Fin 4 × Fin NB,
      law q (outerSeparatedArmEvent σ z r R₀
        ((2 * (((64 * n + 24 * j + 24) * u : ℕ) : ℤ) - 1 : ℤ) : ℝ) (2 * u) u) *
        law q {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z ρ (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
          (landingPos (z - R₃) (z + R₃) (σ k) (γ k))
          (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z ρ (4 * Real.sqrt η * N) m k γ ∧
        (∀ i, (z 0 - ρ + N + 1 ≤ a i 0 ∧ a i 0 + N + 1 ≤ z 0 + ρ) ∨
          (z 1 - ρ + N + 1 ≤ a i 1 ∧ a i 1 + N + 1 ≤ z 1 + ρ)) ∧
        ∀ i, ((p i).1 = 0 ∧ a i 1 = z 1 + ρ ∧ X (p i) ≤ a i 0 ∧ a i 0 ≤ X (p i) + k) ∨
          ((p i).1 = 1 ∧ a i 0 = z 0 + ρ ∧ X (p i) ≤ a i 1 ∧ a i 1 ≤ X (p i) + k) ∨
          ((p i).1 = 2 ∧ a i 1 = z 1 - ρ - cond (σ i) 0 1 ∧ X (p i) ≤ a i 0 ∧
            a i 0 ≤ X (p i) + k) ∨
          ((p i).1 = 3 ∧ a i 0 = z 0 - ρ - cond (σ i) 0 1 ∧ X (p i) ≤ a i 1 ∧
            a i 1 ≤ X (p i) + k)} ≤ d⁻¹ * law q (multiArmEvent σ z r R₃) := by
    intro p
    have h := hbin q L hCB z r R₀ R ρ R₃ N u D Sp Gp Q B M₁ K₁ S m k _
      (4 * Real.sqrt η * N) (fun i => (p i).1) (fun i => X (p i)) hu1 c13 (by omega) c1 c2
      hSp.ge hGp.ge hQ.ge hs₀ c3 c14 c4 hL c5 c6 c10 (by omega) (by omega) hS hRS c12 hs4 hs2 b8
      c7 h2ρ c8 c11 b1 b2 b3 b4 b5 b6 b7
    calc _ = d⁻¹ * (d * (law q (outerSeparatedArmEvent σ z r R₀
          ((2 * (((64 * n + 24 * j + 24) * u : ℕ) : ℤ) - 1 : ℤ) : ℝ) (2 * u) u) * law q _)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdt, one_mul]
      _ ≤ d⁻¹ * law q (multiArmEvent σ z r R₃) := by
          refine mul_le_mul' le_rfl (le_trans ?_ h)
          rw [← mul_assoc]
          exact mul_le_mul' (mul_le_mul' hdc le_rfl) le_rfl
  calc law q (multiArmEvent σ z r R₀) * law q _
      ≤ (C₁ * law q (outerSeparatedArmEvent σ z r R₀
          ((2 * (((64 * n + 24 * j + 24) * u : ℕ) : ℤ) - 1 : ℤ) : ℝ) (2 * u) u)) *
        ∑ p : Fin j → Fin 4 × Fin NB, law q _ :=
        mul_le_mul' h1 ((measure_mono hcover).trans (measure_iUnion_fintype_le _ _))
    _ = C₁ * ∑ p : Fin j → Fin 4 × Fin NB, law q (outerSeparatedArmEvent σ z r R₀
          ((2 * (((64 * n + 24 * j + 24) * u : ℕ) : ℤ) - 1 : ℤ) : ℝ) (2 * u) u) * law q _ := by
        rw [mul_assoc, Finset.mul_sum]
    _ ≤ C₁ * ∑ _p : Fin j → Fin 4 × Fin NB, d⁻¹ * law q (multiArmEvent σ z r R₃) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => hstep p)
    _ = C₁ * ((4 * NB : ℝ≥0∞) ^ j * d⁻¹) * law q (multiArmEvent σ z r R₃) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end StepS

end PercLib.Models.Planar
