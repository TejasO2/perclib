/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.5 (extendability, Proposition 16, and
quasi-multiplicativity, Proposition 17).
-/
module

public import PercLib.Models.Planar.Arms.LowerQuasiMultiplicativity

/-!
# Quasi-multiplicativity and extendability

The lower half of Nolin's quasi-multiplicativity, `π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)`, and
extendability of the inner radius, `π(r', R) ≤ C π(r, R)` for `r ≤ r' ≤ 2r`, for colour sequences
without packs, uniformly over the laws with crossing bounds, for `r₁` (resp. `r`) above a
threshold.

The proof of the lower half is an induction on `r₃ - r₂`, with `Φ(r₂) = π(r₁, r₂) π(r₂, r₃)`. Take
an inner radius `ρ` of the inner separation step (`2ρ + 1 = wN`) just above
`X = max(2 r₂, 40 r₁)`. If `2ρ + 2 > r₃`, the ratio `r₃ / r₂` is bounded and `Φ(r₂) ≤ π(r₁, r₂)` is
handled by extendability of the outer radius at bounded ratio. Otherwise
`π(r₂, r₃) ≤ π(ρ, r₃) ≤ P(far inner family at ρ) + δ π(2ρ + 1, r₃)`
(`exists_law_multiArmEvent_diff_far_le`); step S (`exists_law_mul_law_far_le`) bounds
`π(r₁, ⌊ρ / 5⌋) P(far family)` by `C_S π(r₁, r₃)`, and extendability at bounded ratio gives
`π(r₁, r₂) ≤ C_b π(r₁, ⌊ρ / 5⌋)` and `π(r₁, r₂) ≤ C_b π(r₁, 2ρ + 1)`, so that
`Φ(r₂) ≤ C_b C_S π(r₁, r₃) + δ C_b Φ(2ρ + 1)`. With `δ = (2 C_b)⁻¹`, chosen before the inner step's
`η` and `w`, the induction closes with `C = 2 C_b C_S + C_b`.

## Main results

* `exists_law_multiArmEvent_le_law_multiArmEvent_of_le_eight_mul`,
  `exists_law_multiArmEvent_le_law_multiArmEvent_of_le_pow_mul`: extendability of the outer
  radius at bounded ratio, `π(r, R) ≤ C π(r, R')` for `R ≤ R' ≤ 8^k R`, `R' ≤ L` (only `R' ≤ L`
  is asked, unlike `exists_law_multiArmEvent_le_law_multiArmEvent_two_mul`).
* `exists_law_multiArmEvent_mul_law_multiArmEvent_le`: **quasi-multiplicativity, lower half**.
* `exists_law_multiArmEvent_le_law_multiArmEvent_of_le_two_mul`: **extendability of the inner
  radius**, `π(r', R) ≤ C π(r, R)` for `r ≤ r' ≤ 2r`, `r' ≤ R ≤ L`;
  `exists_law_multiArmEvent_two_mul_le_law_multiArmEvent`: Nolin's form, `π(2r, R) ≤ C π(r, R)`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-- The measure of a set is at most the measure of a second set plus a bound for the part of the
first outside the second (from `measure_le_inter_add_sdiff`). -/
theorem measure_le_add_of_diff_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A E : Set Ω}
    {x : ℝ≥0∞} (h : μ (A \ E) ≤ x) : μ A ≤ μ E + x :=
  (measure_le_inter_add_sdiff μ A E).trans (add_le_add (measure_mono inter_subset_right) h)

/-- **The arithmetic of one induction step** of quasi-multiplicativity: from
`p ≤ F + δ G`, `a ≤ C_b b`, `b F ≤ C_S π`, `a ≤ C_b a'`, `a' G ≤ C π`, `δ C_b = 1/2` and
`C_b C_S ≤ C / 2` follows `a p ≤ C π`. -/
theorem mul_le_of_induction_step {a p F G b a' π C Cb CS δ : ℝ≥0∞} (h23 : p ≤ F + δ * G)
    (ha : a ≤ Cb * b) (hS : b * F ≤ CS * π) (ha' : a ≤ Cb * a') (hih : a' * G ≤ C * π)
    (hδ : δ * Cb = 2⁻¹) (hC : Cb * CS ≤ 2⁻¹ * C) : a * p ≤ C * π :=
  calc a * p ≤ a * (F + δ * G) := mul_le_mul' le_rfl h23
    _ = a * F + δ * (a * G) := by ring
    _ ≤ Cb * b * F + δ * (Cb * a' * G) :=
        add_le_add (mul_le_mul' ha le_rfl) (mul_le_mul' le_rfl (mul_le_mul' ha' le_rfl))
    _ = Cb * (b * F) + δ * Cb * (a' * G) := by ring
    _ ≤ Cb * (CS * π) + δ * Cb * (C * π) :=
        add_le_add (mul_le_mul' le_rfl hS) (mul_le_mul' le_rfl hih)
    _ = Cb * CS * π + 2⁻¹ * C * π := by rw [hδ]; ring
    _ ≤ 2⁻¹ * C * π + 2⁻¹ * C * π := add_le_add (mul_le_mul' hC le_rfl) le_rfl
    _ = C * π := by rw [← add_mul, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

section Extendability

variable {j : ℕ}

/-- **Extendability of the outer radius at ratio at most 8**, with only the larger radius below
the scale `L`: for a colour sequence `σ` without packs there are `1 ≤ C < ⊤` and `r₀` such that for
every law with crossing bounds `c` up to scale `L` and `r₀ ≤ r ≤ R ≤ R' ≤ 8R`, `R' ≤ L`:
`π(r, R) ≤ C π(r, R')`. For `R' ≥ 56 r + 56` by the separated form of Theorem 11's outer half at
`N = ⌈R' / 8⌉ ≤ R` and the window step from `N` to `R'` (which accepts any `R' ∈ [2N, 8N]`); for
smaller `R'` by the one-scale lower bound for `π(r, R')`. -/
theorem exists_law_multiArmEvent_le_law_multiArmEvent_of_le_eight_mul (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ 1 ≤ C ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval)
      (L : ℕ∞), CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' : ℕ), r₀ ≤ r → r ≤ R →
      R ≤ R' → R' ≤ 8 * R → (R' : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤ C * law q (multiArmEvent σ z r R') := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 1000 * (j + 1) * (j + 1) := ⟨_, rfl⟩
  have hn : 1000 * (j + 1) * (j + 1) ≤ m := hm.ge
  obtain ⟨C₁, hC₁, r₁, hsep⟩ := exists_law_multiArmEvent_le_law_outerSeparated σ hσ c hn
  obtain ⟨cW, hcW, hwin⟩ := exists_pos_le_law_window_step σ hσ c hn
  obtain ⟨c₂, hc₂, hone⟩ := exists_pos_le_law_multiArmEvent σ c 57
  obtain ⟨w, hw⟩ : ∃ w : ℝ≥0∞, w = min cW 1 := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := (hw ▸ lt_min hcW one_pos).ne'
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ min_le_right _ _)
  have hwc : w ≤ cW := hw ▸ min_le_left _ _
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, d = min c₂ 1 := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := (hd ▸ lt_min hc₂ one_pos).ne'
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hd ▸ min_le_right _ _)
  have hdc : d ≤ c₂ := hd ▸ min_le_left _ _
  refine ⟨C₁ * w⁻¹ + d⁻¹ + 1, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hC₁ (ENNReal.inv_ne_top.2 hw0), ENNReal.inv_ne_top.2 hd0⟩,
      ENNReal.one_ne_top⟩, le_add_self, max (max r₁ (4 * j + 56)) (m * (m * m) + 2), ?_⟩
  intro q L hCB z r R R' hr hrR hRR' hR'8 hL
  have hr₁ : r₁ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hj : 4 * j + 56 ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hm3 : m * (m * m) + 2 ≤ r := le_trans (le_max_right _ _) hr
  have hinv : ∀ {x y : ℝ≥0∞} {e : ℝ≥0∞}, e ≠ 0 → e ≠ ⊤ → e * x ≤ y → x ≤ e⁻¹ * y :=
    fun {x y e} he0 het h => by
      calc x = e⁻¹ * (e * x) := by rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
        _ ≤ e⁻¹ * y := mul_le_mul' le_rfl h
  by_cases hbig : 56 * r + 56 ≤ R'
  · -- the separated form at `N = ⌈R' / 8⌉` and the window step from `N` to `R'`
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (R' + 7) / 8 := ⟨_, rfl⟩
    have hNL : (N : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : N ≤ R')) hL
    have h1 := hsep q L hCB z r N hr₁ (by omega) hNL
    obtain ⟨tT, lamT, αT, βT, hw1, hw2, hw3, hw4, hw5⟩ := exists_bottom_windows hn z R'
    have h2 := hwin q L hCB z r N R' tT lamT αT βT (by omega) (by omega) (by omega) (by omega)
      hL hw1 hw2 hw3 hw4 hw5
    have h3 : w * law q (outerSeparatedArmEvent σ z r N
        ((2 * (((64 * m + 24 * j + 24) * (N / (m * m)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
        (2 * (N / (m * m))) (N / (m * m))) ≤ law q (multiArmEvent σ z r R') := by
      refine (mul_le_mul' hwc le_rfl).trans (h2.trans (measure_mono ?_))
      rintro ω ⟨a, b, γ, hγ, hd, ho, -, -⟩
      exact mem_multiArmEvent_iff.2 ⟨a, b, γ, hγ, hd, ho⟩
    calc law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent σ z r N) :=
          measure_mono (multiArmEvent_subset_of_le le_rfl (by omega) (by omega))
      _ ≤ C₁ * (w⁻¹ * law q (multiArmEvent σ z r R')) :=
          h1.trans (mul_le_mul' le_rfl (hinv hw0 hwt h3))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' (le_trans le_self_add le_self_add) le_rfl
  · by_cases hRe : R' = r
    · have hRR : R = R' := by omega
      rw [hRR]
      exact le_trans (le_of_eq (one_mul _).symm) (mul_le_mul' le_add_self le_rfl)
    · -- small ratios: the one-scale lower bound
      have h1 : d ≤ law q (multiArmEvent σ z r R') :=
        hdc.trans (hone q L hCB z r R' (by omega) (by omega) (by omega) hL)
      calc law q (multiArmEvent σ z r R) ≤ 1 := prob_le_one
        _ = d⁻¹ * d := (ENNReal.inv_mul_cancel hd0 hdt).symm
        _ ≤ (C₁ * w⁻¹ + d⁻¹ + 1) * law q (multiArmEvent σ z r R') :=
          mul_le_mul' (le_trans le_add_self le_self_add) h1

/-- **Extendability of the outer radius at bounded ratio**: for a colour sequence `σ` without
packs and every `k` there are `1 ≤ C < ⊤` and `r₀` such that for every law with crossing bounds
`c` up to scale `L` and `r₀ ≤ r ≤ R ≤ R' ≤ 8^k R`, `R' ≤ L`: `π(r, R) ≤ C π(r, R')`. -/
theorem exists_law_multiArmEvent_le_law_multiArmEvent_of_le_pow_mul (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (k : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ 1 ≤ C ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval)
      (L : ℕ∞), CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' : ℕ), r₀ ≤ r → r ≤ R →
      R ≤ R' → R' ≤ 8 ^ k * R → (R' : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤ C * law q (multiArmEvent σ z r R') := by
  obtain ⟨C, hC, hC1, r₀, h8⟩ :=
    exists_law_multiArmEvent_le_law_multiArmEvent_of_le_eight_mul σ hσ c
  refine ⟨C ^ k, ENNReal.pow_ne_top hC, one_le_pow₀ hC1, r₀,
    fun q L hCB z r R R' hr hrR hRR' hR'k hL => ?_⟩
  induction k generalizing R' with
  | zero =>
    rw [pow_zero, one_mul] at hR'k
    have hRR : R' = R := by omega
    rw [hRR, pow_zero, one_mul]
  | succ k ih =>
    obtain ⟨P, hP⟩ : ∃ P, P = 8 ^ k * R := ⟨_, rfl⟩
    have hP8 : 8 ^ (k + 1) * R = 8 * P := by rw [hP, pow_succ]; ring
    have hRP : R ≤ P := by rw [hP]; exact Nat.le_mul_of_pos_left R (by positivity)
    rw [hP8] at hR'k
    obtain ⟨M, hM⟩ : ∃ M, M = max R ((R' + 7) / 8) := ⟨_, rfl⟩
    have h1 := ih M (by omega) (by rw [← hP]; omega)
      (le_trans (by exact_mod_cast (by omega : M ≤ R')) hL)
    have h2 := h8 q L hCB z r M R' hr (by omega) (by omega) (by omega) hL
    calc _ ≤ C ^ k * law q (multiArmEvent σ z r M) := h1
      _ ≤ C ^ k * (C * law q (multiArmEvent σ z r R')) := mul_le_mul' le_rfl h2
      _ = C ^ (k + 1) * law q (multiArmEvent σ z r R') := by rw [pow_succ, mul_assoc]

/-- **Quasi-multiplicativity, lower half** (Nolin, Proposition 17). For a colour sequence `σ`
without packs (`j ≤ 1` or no two cyclically consecutive arms of the same colour) there are `C < ⊤`
and `r₀` such that for every law with crossing bounds `c` up to scale `L` and
`r₀ ≤ r₁ ≤ r₂ ≤ r₃ ≤ L`: `π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)`. The constants are chosen in the
order: extendability at bounded ratio `C_b`, `δ = (2 C_b)⁻¹`, the inner step's `(η, w, N₀)`,
step S's `C_S`, then `C = 2 C_b C_S + C_b` and `r₀`; all before `q`, `L`, `z` and the radii. -/
theorem exists_law_multiArmEvent_mul_law_multiArmEvent_le (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r₁ r₂ r₃ : ℕ), r₀ ≤ r₁ → r₁ ≤ r₂ →
      r₂ ≤ r₃ → (r₃ : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃) ≤
        C * law q (multiArmEvent σ z r₁ r₃) := by
  obtain ⟨Cb, hCb, hCb1, rb, hext⟩ :=
    exists_law_multiArmEvent_le_law_multiArmEvent_of_le_pow_mul σ hσ c 3
  have hCb0 : Cb ≠ 0 := (lt_of_lt_of_le one_pos hCb1).ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0∞, δ = (2 * Cb)⁻¹ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact ENNReal.inv_pos.2 (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hCb)
  have hδCb : δ * Cb = 2⁻¹ := by
    rw [hδ, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_assoc,
      ENNReal.inv_mul_cancel hCb0 hCb, mul_one]
  obtain ⟨η, hη, hη1, w, N₀, hw, hwo, hfar⟩ := exists_law_multiArmEvent_diff_far_le σ hσ c hδ0
  obtain ⟨CS, hCS, rS, hS⟩ := exists_law_mul_law_far_le σ hσ c hη hη1 hw
  obtain ⟨a, ha⟩ : ∃ a, w = 2 * a + 1 := ⟨w / 2, by omega⟩
  refine ⟨2 * Cb * CS + Cb, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ENNReal.ofNat_ne_top hCb) hCS, hCb⟩, max (max rb rS) (w * N₀ + 4 * w + 1), ?_⟩
  intro q L hCB z r₁ r₂ r₃ hr₁ h12 h23 hL
  have hrb : rb ≤ r₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr₁)
  have hrS : rS ≤ r₁ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr₁)
  have hrw : w * N₀ + 4 * w + 1 ≤ r₁ := le_trans (le_max_right _ _) hr₁
  have hCS2 : Cb * CS ≤ 2⁻¹ * (2 * Cb * CS + Cb) :=
    calc Cb * CS = 2⁻¹ * (2 * (Cb * CS)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2⁻¹ * (2 * Cb * CS + Cb) := by
          refine mul_le_mul' le_rfl ?_
          rw [mul_assoc]
          exact le_self_add
  have h8 : (8 : ℕ) ^ 3 = 512 := by norm_num
  -- the induction on `r₃ - r₂`
  obtain ⟨d, hd⟩ : ∃ d, d = r₃ - r₂ := ⟨_, rfl⟩
  induction d using Nat.strong_induction_on generalizing r₂ with
  | _ d ih =>
  -- the inner radius `ρ` of the inner step, `2ρ + 1 = wN`, just above `max (2 r₂) (40 r₁)`
  obtain ⟨X, hX⟩ : ∃ X, X = max (2 * r₂) (40 * r₁) := ⟨_, rfl⟩
  obtain ⟨mX, hmX⟩ : ∃ mX, mX = X / w := ⟨_, rfl⟩
  have hw0 : 0 < w := by omega
  have hX1 : w * mX ≤ X := by rw [hmX, mul_comm]; exact Nat.div_mul_le_self X w
  have hX2 : X < w * mX + w := by
    have := Nat.lt_div_mul_add (a := X) hw0
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
  by_cases hbase : r₃ < 2 * ρ + 2
  · -- the base: the ratio `r₃ / r₂` is bounded
    have h := hext q L hCB z r₁ r₂ r₃ hrb h12 h23 (by rw [h8]; omega) hL
    calc law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃)
        ≤ law q (multiArmEvent σ z r₁ r₂) * 1 := mul_le_mul' le_rfl prob_le_one
      _ = law q (multiArmEvent σ z r₁ r₂) := mul_one _
      _ ≤ Cb * law q (multiArmEvent σ z r₁ r₃) := h
      _ ≤ (2 * Cb * CS + Cb) * law q (multiArmEvent σ z r₁ r₃) := mul_le_mul' le_add_self le_rfl
  · -- the induction step
    have hρ3 : 2 * ρ + 2 ≤ r₃ := by omega
    have hρL : (ρ : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : ρ ≤ r₃)) hL
    have h23' := measure_le_add_of_diff_le (hfar q L hCB z N ρ r₃ hρN hNN₀ hρ3 hρL)
    have hmono : law q (multiArmEvent σ z r₂ r₃) ≤ law q (multiArmEvent σ z ρ r₃) :=
      measure_mono (multiArmEvent_subset_of_le (by omega) le_rfl (by omega))
    have hSS := hS q L hCB z r₁ N ρ r₃ hρN hrS (by omega) hρ3 hL
    have hA1 : law q (multiArmEvent σ z r₁ r₂) ≤ Cb * law q (multiArmEvent σ z r₁ (ρ / 5)) := by
      by_cases hle : ρ / 5 ≤ r₂
      · calc _ ≤ law q (multiArmEvent σ z r₁ (ρ / 5)) :=
            measure_mono (multiArmEvent_subset_of_le le_rfl hle (by omega))
          _ ≤ _ := le_trans (le_of_eq (one_mul _).symm) (mul_le_mul' hCb1 le_rfl)
      · exact hext q L hCB z r₁ r₂ (ρ / 5) hrb h12 (by omega) (by rw [h8]; omega)
          (le_trans (by exact_mod_cast (by omega : ρ / 5 ≤ r₃)) hL)
    have hA2 : law q (multiArmEvent σ z r₁ r₂) ≤
        Cb * law q (multiArmEvent σ z r₁ (2 * ρ + 1)) :=
      hext q L hCB z r₁ r₂ (2 * ρ + 1) hrb h12 (by omega) (by rw [h8]; omega)
        (le_trans (by exact_mod_cast (by omega : 2 * ρ + 1 ≤ r₃)) hL)
    have hih := ih (r₃ - (2 * ρ + 1)) (by omega) (2 * ρ + 1) (by omega) (by omega) rfl
    exact mul_le_of_induction_step (hmono.trans h23') hA1 hSS hA2 hih hδCb hCS2

/-- **Extendability of the inner radius** (Nolin, Proposition 16, the inner radius). For a colour
sequence `σ` without packs there are `C < ⊤` and `r₀` such that for every law with crossing
bounds `c` up to scale `L` and `r₀ ≤ r ≤ r' ≤ 2r`, `r' ≤ R ≤ L`: `π(r', R) ≤ C π(r, R)`. From the
lower half of quasi-multiplicativity, `π(r, r') π(r', R) ≤ C π(r, R)`, and the one-scale lower
bound `π(r, r') ≥ c`. -/
theorem exists_law_multiArmEvent_le_law_multiArmEvent_of_le_two_mul (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r r' R : ℕ), r₀ ≤ r → r ≤ r' →
      r' ≤ 2 * r → r' ≤ R → (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r' R) ≤ C * law q (multiArmEvent σ z r R) := by
  obtain ⟨CQ, hCQ, rQ, hQM⟩ := exists_law_multiArmEvent_mul_law_multiArmEvent_le σ hσ c
  obtain ⟨c₂, hc₂, hone⟩ := exists_pos_le_law_multiArmEvent σ c 2
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, d = min c₂ 1 := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := (hd ▸ lt_min hc₂ one_pos).ne'
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hd ▸ min_le_right _ _)
  have hdc : d ≤ c₂ := hd ▸ min_le_left _ _
  refine ⟨d⁻¹ * CQ + 1, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hd0) hCQ,
    ENNReal.one_ne_top⟩, max rQ (4 * j), ?_⟩
  intro q L hCB z r r' R hr hrr' hr'2 hr'R hL
  have hrQ : rQ ≤ r := le_trans (le_max_left _ _) hr
  have hj : 4 * j ≤ r := le_trans (le_max_right _ _) hr
  rcases hrr'.lt_or_eq with hlt | rfl
  · have hr'L : (r' : ℕ∞) ≤ L := le_trans (by exact_mod_cast hr'R) hL
    have h1 : d ≤ law q (multiArmEvent σ z r r') := hdc.trans (hone q L hCB z r r' hj hlt hr'2 hr'L)
    have h2 := hQM q L hCB z r r' R hrQ hrr' hr'R hL
    calc law q (multiArmEvent σ z r' R) = d⁻¹ * (d * law q (multiArmEvent σ z r' R)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdt, one_mul]
      _ ≤ d⁻¹ * (CQ * law q (multiArmEvent σ z r R)) :=
          mul_le_mul' le_rfl ((mul_le_mul' h1 le_rfl).trans h2)
      _ ≤ (d⁻¹ * CQ + 1) * law q (multiArmEvent σ z r R) := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · exact le_trans (le_of_eq (one_mul _).symm) (mul_le_mul' le_add_self le_rfl)

/-- **Extendability of the inner radius, Nolin's form**: `π(2r, R) ≤ C π(r, R)` for `r₀ ≤ r`,
`2r ≤ R ≤ L`. -/
theorem exists_law_multiArmEvent_two_mul_le_law_multiArmEvent (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 2 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z (2 * r) R) ≤ C * law q (multiArmEvent σ z r R) := by
  obtain ⟨C, hC, r₀, h⟩ := exists_law_multiArmEvent_le_law_multiArmEvent_of_le_two_mul σ hσ c
  exact ⟨C, hC, r₀, fun q L hCB z r R hr hR hL =>
    h q L hCB z r (2 * r) R hr (by omega) le_rfl hR hL⟩

end Extendability

end PercLib.Models.Planar
