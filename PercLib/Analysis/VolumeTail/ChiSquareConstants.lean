/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
The constants `A₃`, `A₄` of Proposition I.3.2 for the chi-square limit law, for T. Hutchcroft,
*Critical long-range percolation I*, arXiv:2508.18807v1, Proposition I.3.2 and the proof of
(I.1.7), p. 32.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/ChiSquareA3.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source's `Qinf` (the law of `Z²`, `Z` standard normal) is the chi-square law
`gammaMeasure (1/2) (1/2)` used in `PercLib/Probability/ChiSquareDeterminacy.lean`, and its
Laplace transform is computed from the Laplace transform of a gamma law (new) instead of the
Gaussian half-moment; the kernel `(1 - e^{-λx}) / x` is the kernel `f_λ` of
`PercLib/Probability/SizeBiasLimits.lean` (value `λ` at `0`), so the layer-cake identity needs
no hypothesis on the atom at `0`; the definitions `A3const`, `A4const`, `A3chi`, `A4chi` are
written out; `hypotheses_three_four_nonvacuous` becomes `gammaMeasure_singleton` and an
example; `import Mathlib`, `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Probability.ChiSquareDeterminacy
public import PercLib.Probability.SizeBiasLimits
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The constants of Proposition I.3.2 for the chi-square limit law

Proposition I.3.2 defines
`A₃ = (A₁ / A₂^{1/a}) lim_{λ→∞} λ^{-(a-1)/a} ∫ f_λ dQ_∞` and `A₄ = A₃ / Γ(1/a)`, where
`f_λ(x) = (1 - e^{-λx}) / x`, `f_λ(0) = λ`. In the proof of (I.1.7), `Q_∞` is the chi-square
law with one degree of freedom, `gammaMeasure (1/2) (1/2)`, and `a = 2`.

## Main results

* `integral_exp_neg_mul_gammaMeasure`: the Laplace transform of a gamma law,
  `∫ e^{-tx} dΓ(a, r) = (r / (r + t))^a` for `t > -r`.
* `integral_laplaceKernel_eq_intervalIntegral`: `∫ f_λ dQ = ∫_0^λ ∫ e^{-tx} dQ dt` for a finite
  measure on `[0, ∞)`.
* `integral_laplaceKernel_chiSquare`: `∫ f_λ dQ_∞ = √(1 + 2λ) - 1`, as printed in the paper.
* `tendsto_rpow_mul_integral_laplaceKernel_chiSquare`: `λ^{-1/2} ∫ f_λ dQ_∞ → √2`; the limit is
  `0` for `a > 2` and `+∞` for `0 < a < 2`.
* `div_rpow_mul_sqrt_two_eq`, `div_rpow_mul_sqrt_two_div_Gamma_eq`: `A₃ = √2 A₁ / √A₂` and
  `A₄ = √2 A₁ / (√A₂ √π)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal Topology

namespace PercLib.Analysis

open PercLib.Probability

/-! ### The Laplace transform of a gamma law -/

/-- **The Laplace transform of a gamma law**: `∫ e^{-tx} dΓ(a, r)(x) = (r / (r + t))^a` for
`a, r > 0` and `t > -r`. -/
theorem integral_exp_neg_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : -r < t) :
    ∫ x, exp (-(t * x)) ∂gammaMeasure a r = (r / (r + t)) ^ a := by
  have hrt : 0 < r + t := by linarith
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' a r)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hpt : ∀ x : ℝ, (gammaPDF a r x).toReal • exp (-(t * x)) =
      gammaPDFReal a r x * exp (-(t * x)) := fun x => by
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul]
  simp_rw [hpt]
  have hzero : ∀ x : ℝ, x ∉ Ici (0 : ℝ) → gammaPDFReal a r x * exp (-(t * x)) = 0 := by
    intro x hx
    rw [mem_Ici, not_le] at hx
    simp [gammaPDFReal, not_le.2 hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi]
  have hfun : ∀ x ∈ Ioi (0 : ℝ), gammaPDFReal a r x * exp (-(t * x)) =
      r ^ a / Gamma a * (x ^ (a - 1) * exp (-((r + t) * x))) := by
    intro x hx
    simp only [gammaPDFReal, show (0 : ℝ) ≤ x from le_of_lt hx, ↓reduceIte]
    rw [mul_assoc, mul_assoc, ← exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi ha hrt, div_rpow hr.le hrt.le, one_div,
    inv_rpow hrt.le]
  have hG : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
  field_simp

/-- **The Laplace transform of the chi-square law**: `∫ e^{-tx} dQ_∞(x) = (1 + 2t)^{-1/2}` for
`t > -1/2`. -/
theorem integral_exp_neg_mul_chiSquare {t : ℝ} (ht : -(1 / 2) < t) :
    ∫ x, exp (-(t * x)) ∂gammaMeasure (1 / 2) (1 / 2) = (√(1 + 2 * t))⁻¹ := by
  rw [integral_exp_neg_mul_gammaMeasure (by norm_num) (by norm_num) ht, ← sqrt_eq_rpow,
    ← sqrt_inv]
  congr 1
  have : (1 : ℝ) / 2 + t ≠ 0 := by linarith
  field_simp

/-! ### The layer-cake identity for the kernel -/

/-- `∫_0^λ e^{-tx} dt = f_λ(x)` for every `x`, with `f_λ(0) = λ`. -/
theorem intervalIntegral_exp_neg_mul (lam x : ℝ) :
    ∫ t in (0)..lam, exp (-(t * x)) =
      if x = 0 then lam else (1 - exp (-(lam * x))) / x := by
  split_ifs with hx
  · simp [hx]
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (1 - exp (-(t * x))) / x) (exp (-(t * x))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(t * x)) (-x) t := (hasDerivAt_mul_const x).neg
    have h4 := ((h1.exp).const_sub 1).div_const x
    convert h4 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- **Layer-cake identity for the kernel**: for a finite measure `Q` carried by `[0, ∞)` and
`λ ≥ 0`, `∫ f_λ dQ = ∫_0^λ (∫ e^{-tx} dQ(x)) dt`. -/
theorem integral_laplaceKernel_eq_intervalIntegral (Q : Measure ℝ) [IsFiniteMeasure Q]
    (hQ : ∀ᵐ x ∂Q, 0 ≤ x) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x) ∂Q =
      ∫ t in (0)..lam, ∫ x, exp (-(t * x)) ∂Q := by
  simp_rw [← intervalIntegral_exp_neg_mul]
  have hfin : IsFiniteMeasure ((volume.restrict (uIoc 0 lam)).prod Q) := by
    rw [uIoc_of_le hlam]
    infer_instance
  refine (intervalIntegral_integral_swap ?_).symm
  refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1 ?_
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  filter_upwards [hQ] with x hx
  have ht0 : 0 ≤ t := by
    rw [uIoc_of_le hlam] at ht
    exact ht.1.le
  rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_one_iff.2 (by nlinarith)

/-! ### The kernel integral for the chi-square law -/

/-- The chi-square law has no atoms; more generally a gamma law has none. -/
theorem gammaMeasure_singleton (a r x : ℝ) : gammaMeasure a r {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- `∫ f_λ dQ_∞ = ∫_0^λ (1 + 2t)^{-1/2} dt`: the layer-cake identity and the Laplace transform
of `Q_∞`. -/
theorem integral_laplaceKernel_chiSquare_eq_intervalIntegral {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x) ∂gammaMeasure (1 / 2) (1 / 2) =
      ∫ t in (0)..lam, (√(1 + 2 * t))⁻¹ := by
  have := isProbabilityMeasure_gammaMeasure (a := 1 / 2) (r := 1 / 2) (by norm_num)
    (by norm_num)
  rw [integral_laplaceKernel_eq_intervalIntegral _ gammaMeasure_one_half_ae_nonneg hlam]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hlam] at ht
  exact integral_exp_neg_mul_chiSquare (by linarith [ht.1])

/-- **The `A₃` kernel integral for the chi-square law**: `∫ f_λ dQ_∞ = √(1 + 2λ) - 1` for
`λ ≥ 0`, as printed in the paper (p. 32). -/
theorem integral_laplaceKernel_chiSquare {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x) ∂gammaMeasure (1 / 2) (1 / 2) =
      √(1 + 2 * lam) - 1 := by
  rw [integral_laplaceKernel_chiSquare_eq_intervalIntegral hlam]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) lam,
      HasDerivAt (fun t : ℝ => √(1 + 2 * t)) (√(1 + 2 * t))⁻¹ t := by
    intro t ht
    rw [uIcc_of_le hlam] at ht
    have hx : 1 + 2 * t ≠ 0 := by linarith [ht.1]
    have h0 : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).const_add 1
    convert h0.sqrt hx using 1
    have hpos : 0 < √(1 + 2 * t) := Real.sqrt_pos.mpr (by linarith [ht.1])
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => (√(1 + 2 * t))⁻¹) volume 0 lam := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hlam] at ht
    have hpos : 0 < √(1 + 2 * t) := Real.sqrt_pos.mpr (by linarith [ht.1])
    exact ((by fun_prop : Continuous fun t : ℝ => √(1 + 2 * t)).continuousAt.inv₀
      hpos.ne').continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-! ### The `A₃` limit -/

/-- `√(2 + 1/λ) - (√λ)⁻¹ → √2`. -/
theorem tendsto_sqrt_two_add_inv_sub_sqrt_inv :
    Tendsto (fun lam : ℝ => √(2 + 1 / lam) - (√lam)⁻¹) atTop (𝓝 (√2)) := by
  have h1 : Tendsto (fun lam : ℝ => √(2 + 1 / lam)) atTop (𝓝 (√2)) := by
    refine continuous_sqrt.continuousAt.tendsto.comp ?_
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h2 : Tendsto (fun lam : ℝ => (√lam)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  simpa using h1.sub h2

/-- `√(1 + 2λ) - 1 = √λ (√(2 + 1/λ) - (√λ)⁻¹)` for `λ > 0`. -/
theorem sqrt_one_add_two_mul_sub_one_eq {lam : ℝ} (hlam : 0 < lam) :
    √(1 + 2 * lam) - 1 = √lam * (√(2 + 1 / lam) - (√lam)⁻¹) := by
  have hl : √lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  have hm : √lam * √(2 + 1 / lam) = √(1 + 2 * lam) := by
    rw [← Real.sqrt_mul hlam.le]
    congr 1
    field_simp
    ring
  rw [mul_sub, hm, mul_inv_cancel₀ hl]

/-- `(√λ)⁻¹ (√(1 + 2λ) - 1) → √2`. -/
theorem tendsto_sqrt_inv_mul_sqrt_one_add_two_mul_sub_one :
    Tendsto (fun lam : ℝ => (√lam)⁻¹ * (√(1 + 2 * lam) - 1)) atTop (𝓝 (√2)) := by
  refine tendsto_sqrt_two_add_inv_sub_sqrt_inv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hl : √lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  rw [sqrt_one_add_two_mul_sub_one_eq hlam, ← mul_assoc, inv_mul_cancel₀ hl, one_mul]

/-- The normalised `A₃` kernel equals `λ^{1/a - 1/2} (√(2 + 1/λ) - (√λ)⁻¹)` for `λ > 0`. -/
theorem rpow_mul_integral_laplaceKernel_chiSquare_eventuallyEq {a : ℝ} (ha : a ≠ 0) :
    (fun lam : ℝ => lam ^ (-((a - 1) / a)) *
        ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x)
          ∂gammaMeasure (1 / 2) (1 / 2)) =ᶠ[atTop]
      fun lam => lam ^ (1 / a - 1 / 2) * (√(2 + 1 / lam) - (√lam)⁻¹) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
  rw [integral_laplaceKernel_chiSquare hlam.le, sqrt_one_add_two_mul_sub_one_eq hlam,
    ← mul_assoc, sqrt_eq_rpow, ← rpow_add hlam]
  congr 2
  field_simp
  ring

/-- **The `A₃` limit for the chi-square law** (`a = 2`): `λ^{-(2-1)/2} ∫ f_λ dQ_∞ → √2`. -/
theorem tendsto_rpow_mul_integral_laplaceKernel_chiSquare :
    Tendsto (fun lam : ℝ => lam ^ (-((2 - 1) / 2) : ℝ) *
        ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x)
          ∂gammaMeasure (1 / 2) (1 / 2)) atTop (𝓝 (√2)) := by
  rw [tendsto_congr' (rpow_mul_integral_laplaceKernel_chiSquare_eventuallyEq two_ne_zero)]
  simpa using tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-- **For `a > 2` the `A₃` limit is `0`** for the chi-square law. -/
theorem tendsto_rpow_mul_integral_laplaceKernel_chiSquare_of_two_lt {a : ℝ} (ha : 2 < a) :
    Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a)) *
        ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x)
          ∂gammaMeasure (1 / 2) (1 / 2)) atTop (𝓝 0) := by
  have ha0 : 0 < a := by linarith
  rw [tendsto_congr' (rpow_mul_integral_laplaceKernel_chiSquare_eventuallyEq ha0.ne')]
  have hexp : 0 < 1 / 2 - 1 / a := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt two_pos ha
  have hsmall : Tendsto (fun lam : ℝ => lam ^ (1 / a - 1 / 2)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop hexp using 2
    ring_nf
  simpa using hsmall.mul tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-- **For `0 < a < 2` the `A₃` kernel diverges** for the chi-square law. -/
theorem tendsto_rpow_mul_integral_laplaceKernel_chiSquare_of_lt_two {a : ℝ} (ha : 0 < a)
    (ha2 : a < 2) :
    Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a)) *
        ∫ x, (if x = 0 then lam else (1 - exp (-(lam * x))) / x)
          ∂gammaMeasure (1 / 2) (1 / 2)) atTop atTop := by
  rw [tendsto_congr' (rpow_mul_integral_laplaceKernel_chiSquare_eventuallyEq ha.ne')]
  have hexp : 0 < 1 / a - 1 / 2 := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha ha2
  exact (tendsto_rpow_atTop hexp).atTop_mul_pos (Real.sqrt_pos.mpr two_pos)
    tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-! ### The constants `A₃` and `A₄` at `a = 2` -/

/-- **`A₃ = √2 A₁ / √A₂`** for the chi-square law at `a = 2`, where
`A₃ = (A₁ / A₂^{1/2}) √2`. -/
theorem div_rpow_mul_sqrt_two_eq (A₁ A₂ : ℝ) :
    A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 = √2 * A₁ / √A₂ := by
  rw [← sqrt_eq_rpow]
  ring

/-- **`A₄ = A₃ / Γ(1/2) = √2 A₁ / (√A₂ √π)`** for the chi-square law at `a = 2`. -/
theorem div_rpow_mul_sqrt_two_div_Gamma_eq (A₁ A₂ : ℝ) :
    A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 / Gamma (1 / 2) = √2 * A₁ / (√A₂ * √π) := by
  rw [Gamma_one_half_eq, div_rpow_mul_sqrt_two_eq, div_div]

/-- `A₃ = √π A₄` at `a = 2`. -/
theorem div_rpow_mul_sqrt_two_eq_sqrt_pi_mul (A₁ A₂ : ℝ) :
    A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 = √π * (A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 / Gamma (1 / 2)) := by
  rw [Gamma_one_half_eq]
  have : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  field_simp

/-- For `A₁, A₂ > 0` the constants `A₃` and `A₄` are positive. -/
theorem div_rpow_mul_sqrt_two_pos {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    0 < A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 ∧
      0 < A₁ / A₂ ^ ((1 : ℝ) / 2) * √2 / Gamma (1 / 2) := by
  rw [div_rpow_mul_sqrt_two_div_Gamma_eq, div_rpow_mul_sqrt_two_eq]
  have := Real.sqrt_pos.mpr hA₂
  exact ⟨by positivity, by positivity⟩

/-- **The prefactor of (I.3.7) tends to `A₃`**: `A₁ / (A₂^{1/2} λ^{1 - 1/2}) (√(1 + 2λ) - 1)`
tends to `(A₁ / A₂^{1/2}) √2` as `λ → ∞`. -/
theorem tendsto_div_mul_sqrt_one_add_two_mul_sub_one (A₁ A₂ : ℝ) :
    Tendsto (fun lam : ℝ => A₁ / (A₂ ^ ((1 : ℝ) / 2) * lam ^ (1 - (1 : ℝ) / 2)) *
        (√(1 + 2 * lam) - 1)) atTop (𝓝 (A₁ / A₂ ^ ((1 : ℝ) / 2) * √2)) := by
  refine (tendsto_sqrt_inv_mul_sqrt_one_add_two_mul_sub_one.const_mul
    (A₁ / A₂ ^ ((1 : ℝ) / 2))).congr' ?_
  filter_upwards with lam
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← sqrt_eq_rpow lam, div_mul_eq_div_div,
    div_eq_mul_inv _ (√lam)]
  ring

/-- **Scale selection for `f(r) = r^{2α}` at `a = 2`**: the inverse of `f` is `y ↦ y^{1/(2α)}`,
and `f^{-1}(λ / (A₂ h))^α h = √(λ / A₂) √h`. -/
theorem rpow_div_mul_rpow_mul_eq {α A₂ h lam : ℝ} (hα : 0 < α) (hA₂ : 0 < A₂) (hh : 0 < h)
    (hlam : 0 < lam) :
    ((lam / (A₂ * h)) ^ (1 / (2 * α))) ^ α * h = √(lam / A₂) * √h := by
  have hy : 0 < lam / (A₂ * h) := by positivity
  have hs : √h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hsplit : √(lam / (A₂ * h)) = √(lam / A₂) / √h := by
    rw [show lam / (A₂ * h) = lam / A₂ / h by field_simp, Real.sqrt_div' _ hh.le]
  rw [← rpow_mul hy.le, show 1 / (2 * α) * α = 1 / 2 by field_simp, ← sqrt_eq_rpow, hsplit,
    div_mul_eq_mul_div, div_eq_iff hs, mul_assoc, Real.mul_self_sqrt hh.le]

/-- **The tail exponent at `a = 2`**: for `f(r) = r^{2α}`, `f^{-1}(n)^α / n = n^{-1/2}`, so (I.3.3)
reads `P(|K| ≥ n) ~ A₄ / √n`. -/
theorem rpow_rpow_div_eq_sqrt_inv {α n : ℝ} (hα : 0 < α) (hn : 0 < n) :
    (n ^ (1 / (2 * α))) ^ α / n = (√n)⁻¹ := by
  rw [← rpow_mul hn.le, show 1 / (2 * α) * α = 1 / 2 by field_simp, ← sqrt_eq_rpow]
  rw [← inv_div, Real.div_sqrt]

/-- Non-vacuity of hypotheses (3) and (4) of Proposition I.3.2 at the chi-square law: the
constant family `Q_r = Q_∞` converges weakly, and `Q_∞` has no atom at `0`. -/
example :
    haveI := isProbabilityMeasure_gammaMeasure (a := 1 / 2) (r := 1 / 2) (by norm_num)
      (by norm_num)
    Tendsto (fun _ : ℝ => (gammaMeasure (1 / 2) (1 / 2)).toProbabilityMeasure) atTop
        (𝓝 (gammaMeasure (1 / 2) (1 / 2)).toProbabilityMeasure) ∧
      gammaMeasure (1 / 2) (1 / 2) {0} = 0 :=
  ⟨tendsto_const_nhds, gammaMeasure_singleton _ _ _⟩

end PercLib.Analysis
