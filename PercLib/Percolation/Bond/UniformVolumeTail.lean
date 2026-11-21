/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against the pinned mathlib. Mathematical content: summing
the tree-graph moment bounds `E|K_o|^{j+1} ≤ (2j-1)!! χ_o M^{2j}` with the binomial series of
`(1 - z)^{-1/2}` and `1 - (1 - z)^{1/2}`, then Markov's inequality. No upstream proof is copied,
no definition is added and no Input is introduced.
-/
module

public import PercLib.Probability.ExponentialMoments
public import PercLib.Percolation.Bond.TreeGraph.Moments
public import PercLib.Percolation.Bond.RowSum

/-!
# Exponential cluster-volume bounds under uniform susceptibility

Let `X ≥ 0` satisfy the two-parameter moment bound `E X^m ≤ (2m-3)!! a M^{2m-2}` for every
`m ≥ 1`. Then the weighted and ordinary exponential moments and the tails of `X` are bounded
with the prefactor `a` and the scale `M` kept apart. For an independent bond model on a
countable vertex set with `M = ⨆ x, χ(x) < ∞`, the tree-graph bound supplies this hypothesis
for `X = |K_o|` with `a = χ(o)`, and no transitivity is used.

## Main results

* `PercLib.Probability.lintegral_mul_exp_le_of_moment_le`: `E[X e^{rX}] ≤ a/√(1 - 2rM²)` for
  `0 ≤ r < (2M²)⁻¹`, obtained from the one-parameter `lintegral_mul_exp_le` by rescaling the
  measure.
* `PercLib.Probability.lintegral_exp_le_of_moment_le`: `E e^{rX} ≤ 1 + (a/M²)(1 - √(1 - 2rM²))`
  for `0 ≤ r ≤ (2M²)⁻¹`, endpoint included.
* `PercLib.Probability.measure_le_le_min_of_moment_le`,
  `PercLib.Probability.measure_le_le_exp_of_moment_le`: the explicit tails.
* `PercLib.Percolation.Bond.lintegral_mul_exp_encard_cluster_le`,
  `PercLib.Percolation.Bond.lintegral_exp_encard_cluster_le`,
  `PercLib.Percolation.Bond.law_encard_cluster_ge_le_min`,
  `PercLib.Percolation.Bond.law_encard_cluster_ge_le_exp`: the same for the cluster volume.
-/

@[expose] public section

open Real Filter MeasureTheory Set
open scoped Nat ENNReal

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {a M : ℝ}

/-- The two-parameter moment hypothesis, re-indexed: `E X^{k+1} ≤ (2k−1)!! a M^{2k}`. -/
theorem lintegral_pow_succ_le_of_moment_le
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2))) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * k - 1) * a * M ^ (2 * k)) := by
  have h := hmom (k + 1) (by omega)
  rwa [show 2 * (k + 1) - 3 = 2 * k - 1 by omega, show 2 * (k + 1) - 2 = 2 * k by omega] at h

/-- **Weighted exponential moment, two parameters.** If `X ≥ 0`, `a, M > 0` and
`E X^m ≤ (2m−3)!! a M^{2m−2}` for all `m ≥ 1`, then for `0 ≤ r < (2M²)⁻¹`:
`E[X e^{rX}] ≤ a / √(1 − 2rM²)`. The measure is arbitrary. -/
theorem lintegral_mul_exp_le_of_moment_le (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < (2 * M ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (X ω * exp (r * X ω)) ∂P ≤
      ENNReal.ofReal (a / sqrt (1 - 2 * r * M ^ 2)) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (M / a) with hc
  have hmom' : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂(c • P) ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * M ^ (2 * m - 1)) := by
    intro m hm
    rw [lintegral_smul_measure]
    calc c * ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P
        ≤ c * ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)) := by
          gcongr
          exact hmom m hm
      _ = _ := by
          rw [hc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show 2 * m - 1 = (2 * m - 2) + 1 by omega, pow_succ]
          field_simp
  have h := lintegral_mul_exp_le (P := c • P) hX hX0 hM hmom' hr hr1
  rw [lintegral_smul_measure, smul_eq_mul] at h
  have hc1 : ENNReal.ofReal (a / M) * c = 1 := by
    rw [hc, ← ENNReal.ofReal_mul (by positivity),
      show a / M * (M / a) = 1 by field_simp, ENNReal.ofReal_one]
  calc ∫⁻ ω, ENNReal.ofReal (X ω * exp (r * X ω)) ∂P
      = ENNReal.ofReal (a / M) * (c * ∫⁻ ω, ENNReal.ofReal (X ω * exp (r * X ω)) ∂P) := by
        rw [← mul_assoc, hc1, one_mul]
    _ ≤ ENNReal.ofReal (a / M) * ENNReal.ofReal (M / sqrt (1 - 2 * r * M ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (a / sqrt (1 - 2 * r * M ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **Ordinary exponential moment, two parameters.** Under the hypotheses of
`lintegral_mul_exp_le_of_moment_le`, for a probability measure and `0 ≤ r ≤ (2M²)⁻¹`
(endpoint included): `E e^{rX} ≤ 1 + (a/M²)(1 − √(1 − 2rM²))`. -/
theorem lintegral_exp_le_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ (2 * M ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (exp (r * X ω)) ∂P ≤
      ENNReal.ofReal (1 + a / M ^ 2 * (1 - sqrt (1 - 2 * r * M ^ 2))) := by
  have h2 : 0 < 2 * M ^ 2 := by positivity
  have hz1 : 2 * r * M ^ 2 ≤ 1 := by
    calc 2 * r * M ^ 2 = r * (2 * M ^ 2) := by ring
      _ ≤ (2 * M ^ 2)⁻¹ * (2 * M ^ 2) := mul_le_mul_of_nonneg_right hr1 h2.le
      _ = 1 := inv_mul_cancel₀ h2.ne'
  have hz0 : 0 ≤ 2 * r * M ^ 2 := by positivity
  have hsq : 0 ≤ 1 - sqrt (1 - 2 * r * M ^ 2) := by
    rw [sub_nonneg, sqrt_le_one]; linarith
  have h1 := lintegral_pow_mul_exp (P := P) hX hX0 hr 0
  simp only [pow_zero, one_mul, zero_add] at h1
  rw [h1, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  rcases N with _ | N
  · simp
  rw [Finset.sum_range_succ', add_comm]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]
  gcongr
  calc ∑ k ∈ Finset.range N, ENNReal.ofReal (r ^ (k + 1) / (k + 1) !) *
        ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P
      ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (a / M ^ 2 *
          ((Nat.doubleFactorial (2 * k - 1) : ℝ) / ((k + 1) ! * 2 ^ (k + 1)) *
            (2 * r * M ^ 2) ^ (k + 1))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ENNReal.ofReal (r ^ (k + 1) / (k + 1) !) * ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P
            ≤ ENNReal.ofReal (r ^ (k + 1) / (k + 1) !) *
                ENNReal.ofReal (Nat.doubleFactorial (2 * k - 1) * a * M ^ (2 * k)) := by
              gcongr; exact lintegral_pow_succ_le_of_moment_le hmom k
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              field_simp
              ring
    _ ≤ ENNReal.ofReal (a / M ^ 2 * (1 - sqrt (1 - 2 * r * M ^ 2))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_range_le_one_sub_sqrt hz0 hz1 N) (by positivity)

/-- `P(X ≥ n) ≤ (√2 a / n) e^{−n/(4M²)}` for `n > 0`, under the two-parameter moment
hypothesis. -/
theorem measure_le_le_sqrt_two_mul_of_moment_le (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {n : ℝ} (hn : 0 < n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2)))) := by
  set r := (4 * M ^ 2)⁻¹ with hrdef
  have hr : 0 ≤ r := by positivity
  have hr1 : r < (2 * M ^ 2)⁻¹ := by
    rw [hrdef]; exact inv_strictAnti₀ (by positivity) (by nlinarith [sq_pos_of_pos hM])
  have hB := lintegral_mul_exp_le_of_moment_le hX hX0 ha hM hmom hr hr1
  have hz : 1 - 2 * r * M ^ 2 = 1 / 2 := by rw [hrdef]; field_simp; ring
  rw [hz] at hB
  refine (measure_le_ofReal_div (hX.mul (measurable_const.mul hX).exp)
    (mul_pos hn (exp_pos (r * n))) (fun ω hω => ?_) hB).trans_eq ?_
  · exact mul_le_mul hω (exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hr)) (exp_pos _).le
      (hX0 ω)
  · congr 1
    have hs2 : sqrt (1 / 2 : ℝ) = (sqrt 2)⁻¹ := by rw [one_div, sqrt_inv]
    have hs : 0 < sqrt (2 : ℝ) := by positivity
    rw [hs2, exp_neg, hrdef]
    field_simp

/-- `P(X ≥ n) ≤ (1 + a/M²) e^{−n/(2M²)}` for every real `n`, for a probability measure, under
the two-parameter moment hypothesis. -/
theorem measure_le_le_one_add_mul_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    (n : ℝ) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))) := by
  set r := (2 * M ^ 2)⁻¹ with hrdef
  have hr : 0 ≤ r := by positivity
  have hB := lintegral_exp_le_of_moment_le hX hX0 ha hM hmom hr le_rfl
  have hz : 1 - 2 * r * M ^ 2 = 0 := by rw [hrdef]; field_simp; ring
  rw [hz, sqrt_zero, sub_zero, mul_one] at hB
  refine (measure_le_ofReal_div (measurable_const.mul hX).exp (exp_pos (r * n))
    (fun ω hω => exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hr)) hB).trans_eq ?_
  congr 1
  rw [div_eq_mul_inv, ← exp_neg, hrdef]
  congr 2
  field_simp

/-- **Tail bounds, two parameters.** For every real `n > 0`,
`P(X ≥ n) ≤ min{1, (√2 a/n) e^{−n/(4M²)}, (1 + a/M²) e^{−n/(2M²)}}`. -/
theorem measure_le_le_min_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {n : ℝ} (hn : 0 < n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (min 1 (min (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2))))
      ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))))) := by
  rcases min_choice 1 (min (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2))))
      ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2))))) with h | h <;> rw [h]
  · rw [ENNReal.ofReal_one]; exact prob_le_one
  · rcases min_choice (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2))))
      ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))) with h' | h' <;> rw [h']
    · exact measure_le_le_sqrt_two_mul_of_moment_le hX hX0 ha hM hmom hn
    · exact measure_le_le_one_add_mul_of_moment_le hX hX0 ha.le hM hmom n

/-- **Pure exponential tail, two parameters.** `P(X ≥ n) ≤ e^{−n/(4M²)}` once
`n ≥ 4M² log(1 + a/M²)`. -/
theorem measure_le_le_exp_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {n : ℝ} (hn : 4 * M ^ 2 * log (1 + a / M ^ 2) ≤ n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (exp (-(n / (4 * M ^ 2)))) := by
  refine (measure_le_le_one_add_mul_of_moment_le hX hX0 ha hM hmom n).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h4 : 0 < 4 * M ^ 2 := by positivity
  have hl : log (1 + a / M ^ 2) ≤ n / (4 * M ^ 2) := by rw [le_div_iff₀ h4]; linarith
  have h1 : 1 + a / M ^ 2 ≤ exp (n / (4 * M ^ 2)) := by
    rw [← exp_log (by positivity : 0 < 1 + a / M ^ 2)]; exact exp_le_exp.2 hl
  calc (1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))
      ≤ exp (n / (4 * M ^ 2)) * exp (-(n / (2 * M ^ 2))) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp (-(n / (4 * M ^ 2))) := by
        rw [← exp_add]; congr 1; field_simp; ring

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*} [Countable V]

omit [Countable V] in
/-- Under `⨆ x, χ(x) < ∞`, the susceptibility at every vertex is finite. -/
theorem chi_ne_top_of_iSup_ne_top (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) : chi q o ≠ ⊤ :=
  ne_top_of_le_ne_top hM (le_iSup (fun x => chi q x) o)

/-- With finite susceptibility at `o`, the real cluster volume `|K_o|` (read through
`ℕ∞.toNat`) agrees almost surely with the extended cluster volume. -/
theorem ae_ofReal_encard_toNat_cluster_eq (q : Sym2 V → unitInterval) (o : V)
    (ho : chi q o ≠ ⊤) :
    ∀ᵐ ω ∂law q, ENNReal.ofReal ((cluster ω o).encard.toNat : ℝ) =
      ((cluster ω o).encard : ℝ≥0∞) := by
  have hmeas : Measurable fun ω : Config V => ((cluster ω o).encard : ℝ≥0∞) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster o)
  filter_upwards [ae_lt_top hmeas ho] with ω hω
  have h : (cluster ω o).encard ≠ ⊤ := (ENat.toENNReal_lt_top.1 hω).ne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
  simp [← hm]

/-- The real cluster volume `|K_o|` (read through `ℕ∞.toNat`) is measurable. -/
theorem measurable_encard_toNat_cluster (o : V) :
    Measurable fun ω : Config V => ((cluster ω o).encard.toNat : ℝ) :=
  (measurable_of_countable (fun n : ℕ∞ => (n.toNat : ℝ))).comp (measurable_encard_cluster o)

/-- **Cluster moments, real form.** With `M = ⨆ x, χ(x) < ∞`, the real cluster volume
satisfies `E|K_o|^m ≤ (2m−3)!! χ(o) M^{2m−2}` for every `m ≥ 1`. -/
theorem lintegral_ofReal_encard_toNat_cluster_pow_le (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) (m : ℕ) (hm : 1 ≤ m) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ m) ∂law q ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * (chi q o).toReal *
        (⨆ x, chi q x).toReal ^ (2 * m - 2)) := by
  have ho := chi_ne_top_of_iSup_ne_top q o hM
  calc ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ m) ∂law q
      ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q := lintegral_mono fun ω => by
        rw [ENNReal.ofReal_pow (Nat.cast_nonneg _)]
        refine pow_le_pow_left₀ zero_le ?_ m
        rcases eq_or_ne (cluster ω o).encard ⊤ with h | h
        · simp [h]
        · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
          simp [← hk]
    _ ≤ _ := lintegral_encard_pow_le_iSup q m hm o
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_toReal ho,
          ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM]

/-- `1 ≤ χ(o) ≤ M` in real form, for `M = ⨆ x, χ(x) < ∞`. -/
theorem one_le_toReal_chi_le_toReal_iSup (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) :
    1 ≤ (chi q o).toReal ∧ (chi q o).toReal ≤ (⨆ x, chi q x).toReal := by
  have ho := chi_ne_top_of_iSup_ne_top q o hM
  refine ⟨?_, ENNReal.toReal_mono hM (le_iSup (fun x => chi q x) o)⟩
  simpa using ENNReal.toReal_mono ho (one_le_chi q o)

/-- On the almost sure event of a finite cluster, `|K_o| ≥ n` in `ℝ≥0∞` and in `ℝ` agree. -/
theorem law_ofReal_le_encard_cluster_le (q : Sym2 V → unitInterval) (o : V)
    (ho : chi q o ≠ ⊤) (n : ℝ) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      law q {ω | n ≤ ((cluster ω o).encard.toNat : ℝ)} := by
  refine measure_mono_ae ((ae_ofReal_encard_toNat_cluster_eq q o ho).mono fun ω h hω => ?_)
  have hω' : ENNReal.ofReal n ≤ ENNReal.ofReal ((cluster ω o).encard.toNat : ℝ) := by
    rw [h]; exact hω
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).1 hω'

/-- **Weighted exponential moment of the cluster volume.** With `M = ⨆ x, χ(x) < ∞` and
`0 ≤ s < (2M²)⁻¹`: `E[|K_o| e^{s|K_o|}] ≤ χ(o) / √(1 − 2sM²)`. -/
theorem lintegral_mul_exp_encard_cluster_le (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s < (2 * (⨆ x, chi q x).toReal ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) *
        exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law q ≤
      ENNReal.ofReal ((chi q o).toReal / sqrt (1 - 2 * s * (⨆ x, chi q x).toReal ^ 2)) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact lintegral_mul_exp_le_of_moment_le (measurable_encard_toNat_cluster o)
    (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
    (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hs hs1

/-- **Ordinary exponential moment of the cluster volume.** With `M = ⨆ x, χ(x) < ∞` and
`0 ≤ s ≤ (2M²)⁻¹` (endpoint included): `E e^{s|K_o|} ≤ 1 + (χ(o)/M²)(1 − √(1 − 2sM²))`. -/
theorem lintegral_exp_encard_cluster_le (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ (2 * (⨆ x, chi q x).toReal ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law q ≤
      ENNReal.ofReal (1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2 *
        (1 - sqrt (1 - 2 * s * (⨆ x, chi q x).toReal ^ 2))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact lintegral_exp_le_of_moment_le (measurable_encard_toNat_cluster o)
    (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
    (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hs hs1

/-- `P(|K_o| ≥ n) ≤ (√2 χ(o)/n) e^{−n/(4M²)}` for real `n > 0`, with `M = ⨆ x, χ(x) < ∞`. -/
theorem law_encard_cluster_ge_le_sqrt_two_mul (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {n : ℝ} (hn : 0 < n) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (sqrt 2 * (chi q o).toReal / n *
        exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2)))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) n).trans
    (measure_le_le_sqrt_two_mul_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hn)

/-- **Cluster-volume tails.** With `M = ⨆ x, χ(x) < ∞`, for every real `n > 0`,
`P(|K_o| ≥ n) ≤ min{1, (√2 χ(o)/n) e^{−n/(4M²)}, (1 + χ(o)/M²) e^{−n/(2M²)}}`. -/
theorem law_encard_cluster_ge_le_min (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {n : ℝ} (hn : 0 < n) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (min 1 (min (sqrt 2 * (chi q o).toReal / n *
          exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2))))
        ((1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2) *
          exp (-(n / (2 * (⨆ x, chi q x).toReal ^ 2)))))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) n).trans
    (measure_le_le_min_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hn)

/-- **Pure exponential cluster-volume tail.** With `M = ⨆ x, χ(x) < ∞`,
`P(|K_o| ≥ n) ≤ e^{−n/(4M²)}` whenever `n ≥ 4M² log(1 + χ(o)/M²)`. -/
theorem law_encard_cluster_ge_le_exp (q : Sym2 V → unitInterval) (o : V)
    (hM : (⨆ x, chi q x) ≠ ⊤) {n : ℝ}
    (hn : 4 * (⨆ x, chi q x).toReal ^ 2 *
      log (1 + (chi q o).toReal / (⨆ x, chi q x).toReal ^ 2) ≤ n) :
    law q {ω | ENNReal.ofReal n ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (exp (-(n / (4 * (⨆ x, chi q x).toReal ^ 2)))) := by
  obtain ⟨h1, h2⟩ := one_le_toReal_chi_le_toReal_iSup q o hM
  exact (law_ofReal_le_encard_cluster_le q o (chi_ne_top_of_iSup_ne_top q o hM) n).trans
    (measure_le_le_exp_of_moment_le (measurable_encard_toNat_cluster o)
      (fun _ => Nat.cast_nonneg _) (by linarith) (by linarith)
      (lintegral_ofReal_encard_toNat_cluster_pow_le q o hM) hn)

/-! ### Non-vacuity -/

/-- The zero profile has `χ ≡ 1`, so `⨆ x, χ(x) < ∞` and the tail bound applies, here with
`χ(o) = M = 1` on `ℤ`. -/
example (n : ℝ) (hn : 0 < n) :
    law (fun _ : Sym2 ℤ => (0 : unitInterval))
        {ω | ENNReal.ofReal n ≤ ((cluster ω (0 : ℤ)).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (min 1 (min (sqrt 2 * 1 / n * exp (-(n / (4 * 1 ^ 2))))
        ((1 + 1 / 1 ^ 2) * exp (-(n / (2 * 1 ^ 2)))))) := by
  have h1 : ∀ x : ℤ, chi (fun _ : Sym2 ℤ => (0 : unitInterval)) x = 1 :=
    chi_eq_one_of_offDiagonal_zero _ fun _ _ _ => rfl
  have hM : (⨆ x, chi (fun _ : Sym2 ℤ => (0 : unitInterval)) x) = 1 := by simp [h1]
  have h := law_encard_cluster_ge_le_min (fun _ : Sym2 ℤ => (0 : unitInterval)) 0
    (by rw [hM]; exact ENNReal.one_ne_top) hn
  rwa [hM, h1, ENNReal.toReal_one] at h

end PercLib.Percolation.Bond
