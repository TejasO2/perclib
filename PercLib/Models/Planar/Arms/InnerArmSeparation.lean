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
* `exists_law_multiArmEvent_le_law_outerSeparated_inner`: the separated form of the outer half with
  the inner positions in windows (needs the inner half: the outer step's error term has no windows).
* `exists_law_multiArmEvent_le_law_multiArmEventIn_windows`: **Theorem 11 with windows at both
  ends**, for `32 r ≤ R`.
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

/-! ### Theorem 11 at both ends -/

/-- **Theorem 11, outer half, separated form, with inner windows**
(`exists_law_multiArmEvent_le_law_outerSeparated` with the inner positions in the windows of landing
data). For a colour sequence `σ` without packs,
landing data `(η, θ)` and `n ≥ 1000 (j + 1)²` there are `C < ⊤` and `r₀` such that for every law
with crossing bounds `c` up to scale `L`, `r₀ ≤ r` and `7r ≤ R ≤ L`: `π(r, R)` is at most `C` times
the probability that there are arms from `B_r(z)` to `∂B_R(z)` with inner positions in
`window (16 r + 8) θ η`, separated at the outer boundary at scale `2Q - 1` with fences `(2u, u)`
(`u = ⌊R / n²⌋`, `Q = (64 n + 24 j + 24) u`).

Proof: Nolin's induction on scales as in the outer half, with the inner positions kept by the outer
step, the gluing step and the window step; the term `δ π(r, N)` of the outer step is bounded through
Theorem 11's inner half at `ρ = 2 ⌊R / 6⌋ + 1`, `π(r, ρ) ≤ C_in P(arms with inner positions in the
windows)`, so `δ` is chosen after `C_in`. -/
theorem exists_law_multiArmEvent_le_law_outerSeparated_inner (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ)
    (c : ℕ → ℝ≥0∞) {n : ℕ} (hn : 1000 * (j + 1) * (j + 1) ≤ n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 7 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤ C * law q {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R
          ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
          (2 * (R / (n * n))) (R / (n * n)) γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ window (16 * r + 8) θ η i} := by
  obtain ⟨C₀, hC₀, rI, hinner⟩ :=
    exists_law_multiArmEvent_le_law_multiArmEventIn_window_inner σ hσ hθ c
  obtain ⟨c₁, hc₁, rB, hbase⟩ := exists_pos_le_law_outerSeparated_inner σ hσ hθ c hn
  obtain ⟨cW, hcW, hwin⟩ := exists_pos_le_law_window_step_inner σ hσ c hn
  obtain ⟨Ci, hCi⟩ : ∃ Ci : ℝ≥0∞, Ci = max C₀ 1 := ⟨_, rfl⟩
  have hCit : Ci ≠ ⊤ := hCi ▸ max_ne_top hC₀ ENNReal.one_ne_top
  have hCi1 : 1 ≤ Ci := hCi ▸ le_max_right _ _
  have hC₀i : C₀ ≤ Ci := hCi ▸ le_max_left _ _
  obtain ⟨w, hw⟩ : ∃ w : ℝ≥0∞, w = min cW 1 := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := (hw ▸ lt_min hcW one_pos).ne'
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ min_le_right _ _)
  have hwc : w ≤ cW := hw ▸ min_le_left _ _
  -- `δ` with `Ci w⁻¹ δ = 1/2`
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0∞, D = Ci * w⁻¹ := ⟨_, rfl⟩
  have hDt : D ≠ ⊤ := hD ▸ ENNReal.mul_ne_top hCit (ENNReal.inv_ne_top.2 hw0)
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (lt_of_lt_of_le one_pos hCi1).ne' (ENNReal.inv_ne_zero.2 hwt)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0∞, δ = (2 * D)⁻¹ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact ENNReal.inv_pos.2 (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hDt)
  have hδD : δ * D = 2⁻¹ := by
    rw [hδ, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_assoc,
      ENNReal.inv_mul_cancel hD0 hDt, mul_one]
  obtain ⟨ε, hε, hε1, N₀, hstep⟩ := exists_law_multiArmEventIn_diff_separated_le σ hσ c hδ0
  obtain ⟨cG, hcG, N₁, hglue⟩ := exists_pos_le_law_glue_step_inner σ hσ c hn hε hε1
  obtain ⟨g, hg⟩ : ∃ g : ℝ≥0∞, g = min cG 1 := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := (hg ▸ lt_min hcG one_pos).ne'
  have hgt : g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hg ▸ min_le_right _ _)
  have hgc : g ≤ cG := hg ▸ min_le_left _ _
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞, E = Ci * g⁻¹ + c₁⁻¹ := ⟨_, rfl⟩
  have hEt : E ≠ ⊤ := hE ▸ ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hCit
    (ENNReal.inv_ne_top.2 hg0), ENNReal.inv_ne_top.2 hc₁.ne'⟩
  refine ⟨2 * E, ENNReal.mul_ne_top ENNReal.ofNat_ne_top hEt,
    max (max (rB + 7) (n * (n * n))) (max (max N₀ N₁) rI), ?_⟩
  intro q L hCB z r R₀ hr
  have hrB : rB ≤ r := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr); omega
  have h7 : 7 ≤ r := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr); omega
  have hn3 : n * (n * n) ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hN₀ : N₀ ≤ r :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr))
  have hN₁ : N₁ ≤ r :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr))
  have hrI : rI ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr)
  have hinv : ∀ {x y : ℝ≥0∞} {e : ℝ≥0∞}, e ≠ 0 → e ≠ ⊤ → e * x ≤ y → x ≤ e⁻¹ * y :=
    fun {x y e} he0 het h => by
      calc x = e⁻¹ * (e * x) := by rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
        _ ≤ e⁻¹ * y := mul_le_mul' le_rfl h
  induction R₀ using Nat.strong_induction_on with
  | _ R ih =>
  intro hR hRL
  obtain ⟨B, hB⟩ : ∃ B : Set (Config (LatticeSite 2)), B = {ω : Config (LatticeSite 2) |
      ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R
        ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
        (2 * (R / (n * n))) (R / (n * n)) γ ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ window (16 * r + 8) θ η i} := ⟨_, rfl⟩
  rw [← hB]
  by_cases hsmall : R < 42 * r + 42
  · -- small ratios: the one-scale bound for separated arms from inner windows
    have hb := hbase q L hCB z r R hrB hR (by omega) hRL
    rw [← hB] at hb
    have hc₁t : c₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hb.trans prob_le_one)
    calc law q (multiArmEvent σ z r R) ≤ 1 := prob_le_one
      _ = c₁⁻¹ * c₁ := (ENNReal.inv_mul_cancel hc₁.ne' hc₁t).symm
      _ ≤ (2 * E) * law q B := by
          refine mul_le_mul' ?_ hb
          rw [hE, two_mul]
          exact le_trans le_add_self (add_le_add le_rfl le_add_self)
  · -- the induction step at `N = ⌊R / 6⌋`, `ρ = 2N + 1`
    have hNL : ((R / 6 : ℕ) : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R / 6 ≤ R)) hRL
    have hρL : ((2 * (R / 6) + 1 : ℕ) : ℕ∞) ≤ L :=
      le_trans (by exact_mod_cast (by omega : 2 * (R / 6) + 1 ≤ R)) hRL
    -- Theorem 11's inner half at `ρ`
    have h0 := hinner q L hCB z r (2 * (R / 6) + 1) hrI (by omega) hρL
    -- the outer step at `ρ`, keeping the inner positions
    have h2 := hstep q L hCB z r (R / 6) (2 * (R / 6) + 1) (window (16 * r + 8) θ η) rfl
      (by omega) (by omega) hNL
    obtain ⟨S, hS⟩ : ∃ S : Set (Config (LatticeSite 2)), S = {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2))
          (z + ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l →
          sbtw (landingPos (z - ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2))
              (z + ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2)) (σ i) (γ i))
            (landingPos (z - ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2))
              (z + ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2)) (σ k) (γ k))
            (landingPos (z - ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2))
              (z + ((2 * (R / 6) + 1 : ℕ) : LatticeSite 2)) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (2 * (R / 6) + 1) (4 * Real.sqrt ε * (R / 6 : ℕ))
          ⌊Real.sqrt ε * (R / 6 : ℕ)⌋₊ ⌊ε * (R / 6 : ℕ)⌋₊ γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ window (16 * r + 8) θ η i} := ⟨_, rfl⟩
    rw [← hS] at h2
    -- the gluing step from `ρ` to `R` and the window step from `N` to `R`
    obtain ⟨tT, lamT, αT, βT, hw1', hw2, hw3, hw4, hw5⟩ := exists_bottom_windows hn z R
    have hG := hglue q L hCB z r (R / 6) (2 * (R / 6) + 1) R tT lamT αT βT
      (window (16 * r + 8) θ η) rfl (by omega) (by omega) (by omega) (by omega) hRL hw1' hw2 hw3
      hw4 hw5
    rw [← hS] at hG
    have hGB : g * law q S ≤ law q B := by
      refine (mul_le_mul' hgc le_rfl).trans (hG.trans (measure_mono ?_))
      rw [hB]
      rintro ω ⟨a, b, γ, hγ, hd, ho, hs, -, hJ⟩
      exact ⟨a, b, γ, hγ, hd, ho, hs, hJ⟩
    have hW := hwin q L hCB z r (R / 6) R tT lamT αT βT (window (16 * r + 8) θ η) (by omega)
      (by omega) (by omega) (by omega) hRL hw1' hw2 hw3 hw4 hw5
    have hih := ih (R / 6) (by omega) (by omega) hNL
    have hWB : law q (multiArmEvent σ z r (R / 6)) ≤ 2 * E * (w⁻¹ * law q B) := by
      refine hih.trans (mul_le_mul' le_rfl (hinv hw0 hwt ?_))
      refine (mul_le_mul' hwc le_rfl).trans (hW.trans (measure_mono ?_))
      rw [hB]
      rintro ω ⟨a, b, γ, hγ, hd, ho, hs, -, hJ⟩
      exact ⟨a, b, γ, hγ, hd, ho, hs, hJ⟩
    have hA : law q (multiArmEventIn σ z r (2 * (R / 6) + 1) (window (16 * r + 8) θ η)
        fun _ => univ) ≤ law q S + δ * law q (multiArmEvent σ z r (R / 6)) :=
      measure_le_add_of_diff_le h2
    calc law q (multiArmEvent σ z r R)
        ≤ law q (multiArmEvent σ z r (2 * (R / 6) + 1)) :=
          measure_mono (multiArmEvent_subset_of_le le_rfl (by omega) (by omega))
      _ ≤ Ci * law q (multiArmEventIn σ z r (2 * (R / 6) + 1) (window (16 * r + 8) θ η)
            fun _ => univ) := h0.trans (mul_le_mul' hC₀i le_rfl)
      _ ≤ Ci * (g⁻¹ * law q B + δ * (2 * E * (w⁻¹ * law q B))) :=
          mul_le_mul' le_rfl (hA.trans (add_le_add (hinv hg0 hgt hGB) (mul_le_mul' le_rfl hWB)))
      _ = Ci * g⁻¹ * law q B + ((δ * (Ci * w⁻¹)) * 2) * (E * law q B) := by ring
      _ = Ci * g⁻¹ * law q B + E * law q B := by
          rw [← hD, hδD, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ E * law q B + E * law q B := by
          gcongr
          rw [hE]
          exact le_self_add
      _ = 2 * E * law q B := by ring

/-- **Theorem 11 with windows at both ends, at large ratio** (Nolin, Theorem 11; plan §2.4
`exists_law_multiArmEvent_le_law_multiArmEventIn` for `32 r ≤ R`, with the approved `∃ r₀`). For a
colour sequence `σ` without packs and landing data `(η, θ)` (outer) and `(η, θ')` (inner) there are
`C < ⊤` and `r₀` such that for every law with crossing bounds `c` up to scale `L`, `r₀ ≤ r` and
`32 r ≤ R ≤ L`: `π(r, R) ≤ C P(arms from B_r(z) to ∂B_R(z) with inner positions in
window (16 r + 8) θ' η, landing in window (16 R) θ η)`. Proof: `π(r, R) ≤ π(r, ⌊R / 4⌋)`, the
separated form with inner windows at `⌊R / 4⌋`, and the window step with inner windows into the
windows of the landing data. -/
theorem exists_law_multiArmEvent_le_law_multiArmEventIn_windows (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℚ} {θ θ' : Fin j → ℚ} (hθ : IsLanding η θ)
    (hθ' : IsLanding η θ') (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 32 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤
        C * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ' η) (window (16 * R) θ η)) := by
  obtain ⟨n, hn, w, hw0, hwt, hwin⟩ := exists_pos_le_law_window_step_landing_inner σ hσ hθ c
  obtain ⟨C₁, hC₁, r₁, hsep⟩ := exists_law_multiArmEvent_le_law_outerSeparated_inner σ hσ hθ' c hn
  refine ⟨C₁ * w⁻¹, ENNReal.mul_ne_top hC₁ (ENNReal.inv_ne_top.2 hw0.ne'),
    max r₁ (n * (n * n) + 8), fun q L hCB z r R hr hR hRL => ?_⟩
  have hr₁ : r₁ ≤ r := le_trans (le_max_left _ _) hr
  have hn3 : n * (n * n) + 8 ≤ r := le_trans (le_max_right _ _) hr
  have hNL : ((R / 4 : ℕ) : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R / 4 ≤ R)) hRL
  have h1 := hsep q L hCB z r (R / 4) hr₁ (by omega) hNL
  have h2 := hwin q L hCB z r (R / 4) R (window (16 * r + 8) θ' η) (by omega) (by omega)
    (by omega) (by omega) hRL
  calc law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent σ z r (R / 4)) :=
        measure_mono (multiArmEvent_subset_of_le le_rfl (by omega) (by omega))
    _ ≤ C₁ * (w⁻¹ * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ' η)
          (window (16 * R) θ η))) := by
        refine h1.trans (mul_le_mul' le_rfl ?_)
        calc _ = w⁻¹ * (w * law q _) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hw0.ne' hwt, one_mul]
          _ ≤ _ := mul_le_mul' le_rfl h2
    _ = C₁ * w⁻¹ * _ := (mul_assoc _ _ _).symm

end InnerHalf

end PercLib.Models.Planar
