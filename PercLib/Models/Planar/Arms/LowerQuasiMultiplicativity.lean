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

end PercLib.Models.Planar
