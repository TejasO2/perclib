/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (Theorem 11) and Section 4.5 (Proposition 16).
-/
module

public import PercLib.Models.Planar.Arms.Extendability
public import PercLib.Models.Planar.Arms.InnerWindows

/-!
# Theorem 11, inner half

Nolin's Theorem 11 at the internal extremities, for colour sequences without packs, uniformly over
the laws with crossing bounds: `π(r, R) ≤ C P(arms from B_r(z) to ∂B_R(z) with inner positions in
window (16 r + 8) θ η)` for landing data `(η, θ)`, `r₀ ≤ r`, `2r ≤ R ≤ L`.

The proof does not iterate over scales. Take the inner radius `ρ` of the inner separation step
(`2ρ + 1 = wN`) just above `40 r`. If `R < 2ρ + 2`, the ratio `R / r` is bounded and the one-scale
bound with inner windows (`exists_pos_le_law_multiArmEventIn_window_inner`) applies. Otherwise
`π(r, R) ≤ π(ρ, R) ≤ P(far inner family at ρ) + δ π(2ρ + 1, R)`
(`exists_law_multiArmEvent_diff_far_le`) and `π(2ρ + 1, R) ≤ C_b π(r, R)` (quasi-multiplicativity
and the one-scale bound), so `π(r, R) ≤ 2 P(far family)` once `δ C_b = 1/2`; step S with inner
windows (`exists_law_mul_law_far_le_inner`) and the one-scale bound for separated arms from inner
windows at `⌊ρ / 5⌋` (`exists_pos_le_law_outerSeparated_inner`) bound `P(far family)` by a constant
times the probability of arms with inner positions in the windows.

## Main results

* `le_two_mul_of_le_add_inv_two_mul`: `x ≤ F + x / 2` with `x < ⊤` gives `x ≤ 2F`.
* `exists_law_multiArmEvent_le_law_multiArmEvent_of_le_mul`: extendability of the inner radius
  at any bounded ratio, `π(r', R) ≤ C π(r, R)` for `r ≤ r' ≤ K r`.
* `exists_law_multiArmEvent_le_law_innerSeparated`: the separated form at the inner end,
  `π(ρ, R) ≤ 2 P(arms separated at the inner boundary of B_ρ(z))` for the radii `2ρ + 1 = wN` of
  the inner separation step.
* `exists_law_multiArmEvent_le_law_multiArmEventIn_window_inner`: **Theorem 11, inner half**.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-- **Absorbing half of a finite quantity**: `x ≤ F + x / 2` with `x ≠ ⊤` gives `x ≤ 2F`. -/
theorem le_two_mul_of_le_add_inv_two_mul {x F : ℝ≥0∞} (hx : x ≠ ⊤) (h : x ≤ F + 2⁻¹ * x) :
    x ≤ 2 * F := by
  have hx2 : 2⁻¹ * x ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 two_ne_zero) hx
  have h1 : 2⁻¹ * x + 2⁻¹ * x ≤ F + 2⁻¹ * x := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    exact h
  have h2 : 2⁻¹ * x ≤ F := (ENNReal.add_le_add_iff_right hx2).1 h1
  calc x = 2 * (2⁻¹ * x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * F := mul_le_mul' le_rfl h2

section InnerHalf

variable {j : ℕ}

/-- **Extendability of the inner radius at bounded ratio**: for a colour sequence `σ` without
packs and a ratio `K` there are `1 ≤ C < ⊤` and `r₀` such that for every law with crossing bounds
`c` up to scale `L` and `r₀ ≤ r ≤ r' ≤ K r`, `r' ≤ R ≤ L`: `π(r', R) ≤ C π(r, R)`. From the lower
half of quasi-multiplicativity, `π(r, r') π(r', R) ≤ C π(r, R)`, and the one-scale lower bound
`π(r, r') ≥ c`. -/
theorem exists_law_multiArmEvent_le_law_multiArmEvent_of_le_mul (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (K : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ 1 ≤ C ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval)
      (L : ℕ∞), CrossingBounds q L c → ∀ (z : LatticeSite 2) (r r' R : ℕ), r₀ ≤ r → r ≤ r' →
      r' ≤ K * r → r' ≤ R → (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r' R) ≤ C * law q (multiArmEvent σ z r R) := by
  obtain ⟨CQ, hCQ, rQ, hQM⟩ := exists_law_multiArmEvent_mul_law_multiArmEvent_le σ hσ c
  obtain ⟨c₂, hc₂, hone⟩ := exists_pos_le_law_multiArmEvent σ c K
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, d = min c₂ 1 := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := (hd ▸ lt_min hc₂ one_pos).ne'
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hd ▸ min_le_right _ _)
  have hdc : d ≤ c₂ := hd ▸ min_le_left _ _
  refine ⟨d⁻¹ * CQ + 1, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hd0) hCQ,
    ENNReal.one_ne_top⟩, le_add_self, max rQ (4 * j), ?_⟩
  intro q L hCB z r r' R hr hrr' hr'K hr'R hL
  have hrQ : rQ ≤ r := le_trans (le_max_left _ _) hr
  have hj : 4 * j ≤ r := le_trans (le_max_right _ _) hr
  rcases hrr'.lt_or_eq with hlt | rfl
  · have hr'L : (r' : ℕ∞) ≤ L := le_trans (by exact_mod_cast hr'R) hL
    have h1 : d ≤ law q (multiArmEvent σ z r r') := hdc.trans (hone q L hCB z r r' hj hlt hr'K hr'L)
    have h2 := hQM q L hCB z r r' R hrQ hrr' hr'R hL
    calc law q (multiArmEvent σ z r' R) = d⁻¹ * (d * law q (multiArmEvent σ z r' R)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdt, one_mul]
      _ ≤ d⁻¹ * (CQ * law q (multiArmEvent σ z r R)) :=
          mul_le_mul' le_rfl ((mul_le_mul' h1 le_rfl).trans h2)
      _ ≤ (d⁻¹ * CQ + 1) * law q (multiArmEvent σ z r R) := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · exact le_trans (le_of_eq (one_mul _).symm) (mul_le_mul' le_add_self le_rfl)

/-- **Theorem 11, the separated form at the inner end** (for the radii of the inner separation
step). For a colour sequence `σ` without packs there are `0 < η ≤ 1`, an odd `w ≥ 7` and `N₀` such
that for every law with crossing bounds `c` up to scale `L`, `2ρ + 1 = wN`, `N₀ ≤ N` and
`2ρ + 2 ≤ R ≤ L`: `π(ρ, R) ≤ 2 P(the arms can be chosen separated at the inner boundary of
B_ρ(z), separation 4 √η N, fences (⌊√η N⌋, ⌊η N⌋))`. From the inner step's probability form with
`δ = (2 C)⁻¹`, `C` the constant of extendability inwards at ratio `3`. -/
theorem exists_law_multiArmEvent_le_law_innerSeparated (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ w N₀ : ℕ, 7 ≤ w ∧ w % 2 = 1 ∧
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞), CrossingBounds q L c →
      ∀ (z : LatticeSite 2) (N ρ R : ℕ), 2 * ρ + 1 = w * N → N₀ ≤ N → 2 * ρ + 2 ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z ρ R) ≤ 2 * law q (innerSeparatedArmEvent σ z ρ R
        (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊) := by
  obtain ⟨Cb, hCb, hCb1, rb, hext⟩ :=
    exists_law_multiArmEvent_le_law_multiArmEvent_of_le_mul σ hσ c 3
  have hCb0 : Cb ≠ 0 := (lt_of_lt_of_le one_pos hCb1).ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0∞, δ = (2 * Cb)⁻¹ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact ENNReal.inv_pos.2 (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hCb)
  have hδCb : δ * Cb = 2⁻¹ := by
    rw [hδ, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_assoc,
      ENNReal.inv_mul_cancel hCb0 hCb, mul_one]
  obtain ⟨η, hη, hη1, w, N₀, hw, hwo, hG⟩ := exists_law_multiArmEvent_diff_innerSeparated_le σ hσ c
    hδ0
  refine ⟨η, hη, hη1, w, max (max N₀ rb) 1, hw, hwo, fun q L hCB z N ρ R hρ hN hR hL => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have h7 : 7 * N ≤ w * N := Nat.mul_le_mul_right N hw
  have hrb : rb ≤ ρ := by
    have := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    omega
  have hρL : (ρ : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : ρ ≤ R)) hL
  have h1 := measure_le_add_of_diff_le (hG q L hCB z N ρ R hρ hN₀ hR hρL)
  have h2 := hext q L hCB z ρ (2 * ρ + 1) R hrb (by omega) (by omega) (by omega) hL
  refine le_two_mul_of_le_add_inv_two_mul (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one)
    (h1.trans (add_le_add le_rfl ?_))
  calc δ * law q (multiArmEvent σ z (2 * ρ + 1) R) ≤ δ * (Cb * law q (multiArmEvent σ z ρ R)) :=
        mul_le_mul' le_rfl h2
    _ = 2⁻¹ * law q (multiArmEvent σ z ρ R) := by rw [← mul_assoc, hδCb]

/-- **Theorem 11, inner half** (Nolin, Theorem 11, the internal extremities; plan §2.4
`exists_law_multiArmEvent_le_law_multiArmEventIn` with the outer windows `univ`, the approved
`∃ r₀`). For a colour sequence `σ` without packs and landing data `(η, θ)` there are `C < ⊤` and
`r₀` such that for every law with crossing bounds `c` up to scale `L`, `r₀ ≤ r` and
`2r ≤ R ≤ L`: `π(r, R) ≤ C P(arms from B_r(z) to ∂B_R(z) with inner positions in
window (16 r + 8) θ η)`.

Constants, in order: the lower half of quasi-multiplicativity and the one-scale bound give `C_b`
with `π(2ρ + 1, R) ≤ C_b π(r, R)` for `2ρ + 1 ≤ 90 r`; `δ = (2 C_b)⁻¹`; the inner step's
`(η', w, N₀)` for `δ`; step S with inner windows (`C_S`, `n`); the one-scale bounds for separated
arms from inner windows (`c₁`) and for arms from inner windows at ratio at most `81` (`c₂`);
`C = 2 min(c₁, 1)⁻¹ C_S + c₂⁻¹`; the threshold last. -/
theorem exists_law_multiArmEvent_le_law_multiArmEventIn_window_inner (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ)
    (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 2 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤
        C * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η) fun _ => univ) := by
  obtain ⟨Cb, hCb, hCb1, rb, hext⟩ :=
    exists_law_multiArmEvent_le_law_multiArmEvent_of_le_mul σ hσ c 90
  have hCb0 : Cb ≠ 0 := (lt_of_lt_of_le one_pos hCb1).ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0∞, δ = (2 * Cb)⁻¹ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact ENNReal.inv_pos.2 (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hCb)
  have hδCb : δ * Cb = 2⁻¹ := by
    rw [hδ, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_assoc,
      ENNReal.inv_mul_cancel hCb0 hCb, mul_one]
  obtain ⟨ηs, hηs, hηs1, w, N₀, hw, hwo, hfar⟩ := exists_law_multiArmEvent_diff_far_le σ hσ c hδ0
  obtain ⟨CS, hCS, n, hn, rS, hS⟩ := exists_law_mul_law_far_le_inner σ hσ c hηs hηs1 hw
  obtain ⟨c₁, hc₁, r₁, hsep⟩ := exists_pos_le_law_outerSeparated_inner σ hσ hθ c hn
  obtain ⟨c₂, hc₂, r₂, hsmall⟩ := exists_pos_le_law_multiArmEventIn_window_inner σ hθ c 81
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : ℝ≥0∞, d₁ = min c₁ 1 := ⟨_, rfl⟩
  have hd₁0 : d₁ ≠ 0 := (hd₁ ▸ lt_min hc₁ one_pos).ne'
  have hd₁t : d₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hd₁ ▸ min_le_right _ _)
  have hd₁c : d₁ ≤ c₁ := hd₁ ▸ min_le_left _ _
  obtain ⟨a, ha⟩ : ∃ a, w = 2 * a + 1 := ⟨w / 2, by omega⟩
  refine ⟨2 * (d₁⁻¹ * CS) + c₂⁻¹, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hd₁0) hCS), ENNReal.inv_ne_top.2 hc₂.ne'⟩,
    max (max rb (max rS r₁)) (max r₂ (w * N₀ + 4 * w + 1)), ?_⟩
  intro q L hCB z r R hr h2r hRL
  have hrb : rb ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hrS : rS ≤ r :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr))
  have hr₁ : r₁ ≤ r :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr))
  have hr₂ : r₂ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr)
  have hrw : w * N₀ + 4 * w + 1 ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr)
  -- the inner radius `ρ` of the inner step, `2ρ + 1 = wN`, just above `40 r`
  obtain ⟨mX, hmX⟩ : ∃ mX, mX = 40 * r / w := ⟨_, rfl⟩
  have hw0 : 0 < w := by omega
  have hX1 : w * mX ≤ 40 * r := by rw [hmX, mul_comm]; exact Nat.div_mul_le_self _ w
  have hX2 : 40 * r < w * mX + w := by
    have := Nat.lt_div_mul_add (a := 40 * r) hw0
    rw [← hmX] at this
    linarith
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * mX + 3 := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = w * mX + w + a := ⟨_, rfl⟩
  have hρN : 2 * ρ + 1 = w * N := by rw [hρ, hN, ha]; ring
  have hNN₀ : N₀ ≤ N := by
    by_contra h
    have h₁ : w * (mX + 1) ≤ w * N₀ := Nat.mul_le_mul_left w (by omega)
    have h₂ : w * (mX + 1) = w * mX + w := by ring
    omega
  by_cases hbase : R < 2 * ρ + 2
  · -- bounded ratio: the one-scale bound with inner windows
    have h := hsmall q L hCB z r R hr₂ (by omega) (by omega) hRL
    have hc₂t : c₂ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (h.trans prob_le_one)
    calc law q (multiArmEvent σ z r R) ≤ 1 := prob_le_one
      _ = c₂⁻¹ * c₂ := (ENNReal.inv_mul_cancel hc₂.ne' hc₂t).symm
      _ ≤ (2 * (d₁⁻¹ * CS) + c₂⁻¹) * _ := mul_le_mul' le_add_self h
  · have hρ3 : 2 * ρ + 2 ≤ R := by omega
    have hρL : (ρ : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : ρ ≤ R)) hRL
    have hR₀L : ((ρ / 5 : ℕ) : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : ρ / 5 ≤ R)) hRL
    -- the inner step at `ρ`, and `π(2ρ + 1, R) ≤ C_b π(r, R)`
    have h1 := measure_le_add_of_diff_le (hfar q L hCB z N ρ R hρN hNN₀ hρ3 hρL)
    have h2 := hext q L hCB z r (2 * ρ + 1) R hrb (by omega) (by omega) (by omega) hRL
    have hmono : law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent σ z ρ R) :=
      measure_mono (multiArmEvent_subset_of_le (by omega) le_rfl (by omega))
    -- step S with inner windows and the one-scale bound for the first family
    have hSS := hS q L hCB z r N ρ (ρ / 5) R (window (16 * r + 8) θ η) hρN rfl hrS (by omega)
      hρ3 hRL
    have hc := hsep q L hCB z r (ρ / 5) hr₁ (by omega) (by omega) hR₀L
    have key : ∀ F : ℝ≥0∞, law q (multiArmEvent σ z ρ R) ≤
        F + δ * law q (multiArmEvent σ z (2 * ρ + 1) R) →
        F ≤ d₁⁻¹ * (CS * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η)
          fun _ => univ)) →
        law q (multiArmEvent σ z r R) ≤ (2 * (d₁⁻¹ * CS) + c₂⁻¹) *
          law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η) fun _ => univ) := by
      intro F hF1 hF2
      have hπ : law q (multiArmEvent σ z r R) ≤ F + 2⁻¹ * law q (multiArmEvent σ z r R) := by
        refine hmono.trans (hF1.trans (add_le_add le_rfl ?_))
        calc δ * law q (multiArmEvent σ z (2 * ρ + 1) R)
            ≤ δ * (Cb * law q (multiArmEvent σ z r R)) := mul_le_mul' le_rfl h2
          _ = 2⁻¹ * law q (multiArmEvent σ z r R) := by rw [← mul_assoc, hδCb]
      calc law q (multiArmEvent σ z r R)
          ≤ 2 * F := le_two_mul_of_le_add_inv_two_mul
            (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one) hπ
        _ ≤ 2 * (d₁⁻¹ * (CS * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η)
            fun _ => univ))) := mul_le_mul' le_rfl hF2
        _ = 2 * (d₁⁻¹ * CS) * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η)
            fun _ => univ) := by ring
        _ ≤ _ := mul_le_mul' le_self_add le_rfl
    refine key _ h1 ?_
    calc _ = d₁⁻¹ * (d₁ * law q _) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hd₁0 hd₁t, one_mul]
      _ ≤ d₁⁻¹ * (CS * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η)
          fun _ => univ)) := mul_le_mul' le_rfl ((mul_le_mul' (hd₁c.trans hc) le_rfl).trans hSS)

end InnerHalf

end PercLib.Models.Planar
