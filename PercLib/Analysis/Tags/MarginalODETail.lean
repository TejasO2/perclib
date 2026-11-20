/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for the perturbed-Riccati remainder assertion K58A, proved from
`RiccatiComparison.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.RiccatiComparison

@[expose] public section
noncomputable section

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- **K58A.** Let `A, α, r₀ > 0`, let `f > 0` be differentiable on `[r₀, ∞)` (one-sided at `r₀`)
with derivative `f'`, and let `h` be measurable and bounded on `[r₀, ∞)` with
`f' = A (1 - h) r^{-α-1} f²` there. Then for `r₀ ≤ r ≤ R`,
`1/f r = 1/f R + (A/α)(r^{-α} - R^{-α}) - A ∫_r^R h s s^{-α-1} ds`. If moreover `f → ∞`, then
for every `r ≥ r₀` the quantity `1 - α r^α ∫_r^∞ h s s^{-α-1} ds` is strictly positive and
`f r = (α/A) r^α / (1 - α r^α ∫_r^∞ h s s^{-α-1} ds)`; and if in addition `h → 0`, then
`f ~ (α/A) r^α`. -/
@[tag "K58A"]
theorem riccati_tail_remainder {f f' h : ℝ → ℝ} {A α r₀ : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hr₀ : 0 < r₀) (hderiv : ∀ x, r₀ ≤ x → HasDerivWithinAt f (f' x) (Ici r₀) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hode : ∀ x, r₀ ≤ x → f' x = A * (1 - h x) * x ^ (-α - 1) * f x ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hbdd : ∃ C, ∀ x, r₀ ≤ x → |h x| ≤ C) :
    (∀ r R, r₀ ≤ r → r ≤ R →
      (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1)) ∧
    (Tendsto f atTop atTop →
      (∀ r, r₀ ≤ r → 0 < 1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1) ∧
        f r = α / A * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))) ∧
      (Tendsto h atTop (𝓝 0) → f ~[atTop] fun r => α / A * r ^ α)) := by
  obtain ⟨C, hC⟩ := hbdd
  classical
  -- a globally measurable modification of `h`, equal to `h` on `[r₀, ∞)`
  set g : ℝ → ℝ := (Ici r₀).piecewise h 0 with hg
  have hgh : ∀ x, r₀ ≤ x → g x = h x := fun x hx => piecewise_eq_of_mem _ _ _ (mem_Ici.2 hx)
  have hgmeas : Measurable g := by
    refine measurable_of_restrict_of_restrict_compl (s := Ici r₀) measurableSet_Ici ?_ ?_
    · rw [hg, domRestrict_piecewise]; exact hmeas
    · rw [hg, domRestrict_piecewise_compl]; exact measurable_const
  have hgC : ∀ x, r₀ ≤ x → |g x| ≤ C := fun x hx => (hgh x hx).symm ▸ hC x hx
  have hgode : ∀ x, r₀ ≤ x → f' x = A * (1 - g x) * x ^ (-α - 1) * f x ^ 2 := fun x hx =>
    (hgh x hx).symm ▸ hode x hx
  -- two-sided derivatives away from the endpoint
  have hd : ∀ x, r₀ < x → HasDerivAt f (f' x) x := fun x hx =>
    (hderiv x hx.le).hasDerivAt (Ici_mem_nhds hx)
  -- the integrals of `g` and `h` agree to the right of `r₀`
  have hIcc : ∀ r R, r₀ ≤ r → r ≤ R →
      ∫ s in r..R, g s * s ^ (-α - 1) = ∫ s in r..R, h s * s ^ (-α - 1) := by
    intro r R hr hrR
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hrR] at hs
    simp only [hgh s (hr.trans hs.1)]
  have hIoi : ∀ r, r₀ ≤ r →
      ∫ s in Ioi r, g s * s ^ (-α - 1) = ∫ s in Ioi r, h s * s ^ (-α - 1) := by
    intro r hr
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [hgh s (hr.trans (le_of_lt hs))]
  -- the finite identity for `g`
  have hfin : ∀ r R, r₀ ≤ r → r ≤ R →
      (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, g s * s ^ (-α - 1) := by
    have hint : ∀ r R, r₀ < r → r ≤ R →
        (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
          - A * ∫ s in r..R, g s * s ^ (-α - 1) := fun r R hr hrR =>
      inv_eq_of_ode hA hα (hr₀.trans hr) (fun x hx => hd x (hr.trans_le hx))
        (fun x hx => hpos x (hr.le.trans hx)) (fun x hx => hgode x (hr.le.trans hx)) hgmeas
        (fun x hx => hgC x (hr.le.trans hx)) le_rfl hrR
    intro r R hr hrR
    rcases hr.eq_or_lt with rfl | hlt
    swap
    · exact hint r R hlt hrR
    rcases hrR.eq_or_lt with rfl | hlt'
    · simp
    -- pass to the limit `x ↓ r₀` in the identity on `(r₀, R]`
    have hfc : Tendsto (fun x => (f x)⁻¹) (𝓝[>] r₀) (𝓝 (f r₀)⁻¹) :=
      (((hderiv r₀ le_rfl).continuousWithinAt.mono Ioi_subset_Ici_self).tendsto).inv₀
        (hpos r₀ le_rfl).ne'
    have hgi : IntegrableOn (fun s => g s * s ^ (-α - 1)) (uIcc r₀ R) := by
      have h1 : IntegrableOn (fun s => g s * s ^ (-α - 1)) (Ioi r₀) :=
        integrableOn_mul_rpow_neg hr₀ hα hgmeas hgC
      rw [uIcc_of_le hrR, integrableOn_Icc_iff_integrableOn_Ioc]
      exact h1.mono_set Ioc_subset_Ioi_self
    have hcont : ContinuousWithinAt (fun x => ∫ s in x..R, g s * s ^ (-α - 1)) (Ioi r₀) r₀ := by
      have h1 := (intervalIntegral.continuousOn_primitive_interval_left hgi) r₀ left_mem_uIcc
      rw [uIcc_of_le hrR] at h1
      exact h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hlt')
    have hrpow : ContinuousWithinAt (fun x : ℝ => x ^ (-α)) (Ioi r₀) r₀ :=
      (Real.continuousAt_rpow_const r₀ (-α) (Or.inl hr₀.ne')).continuousWithinAt
    have hrhs : Tendsto (fun x => (f R)⁻¹ + A / α * (x ^ (-α) - R ^ (-α))
        - A * ∫ s in x..R, g s * s ^ (-α - 1)) (𝓝[>] r₀)
        (𝓝 ((f R)⁻¹ + A / α * (r₀ ^ (-α) - R ^ (-α))
          - A * ∫ s in r₀..R, g s * s ^ (-α - 1))) :=
      ((tendsto_const_nhds.add ((hrpow.tendsto.sub tendsto_const_nhds).const_mul _)).sub
        (hcont.tendsto.const_mul _))
    refine tendsto_nhds_unique hfc (hrhs.congr' ?_)
    filter_upwards [Ioc_mem_nhdsGT hlt'] with x hx
    exact (hint x R hx.1 hx.2).symm
  refine ⟨fun r R hr hrR => (hIcc r R hr hrR) ▸ hfin r R hr hrR, fun hinf => ?_⟩
  -- the tail identity `1/f r = (A/α) r^{-α} - A ∫_r^∞ g s s^{-α-1} ds`
  have hkey : ∀ r, r₀ ≤ r →
      (f r)⁻¹ = A / α * r ^ (-α) - A * ∫ s in Ioi r, g s * s ^ (-α - 1) := by
    intro r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    have hIint : IntegrableOn (fun s => g s * s ^ (-α - 1)) (Ioi r) :=
      integrableOn_mul_rpow_neg hr0 hα hgmeas (fun t ht => hgC t (hr.trans ht))
    have hlim : Tendsto (fun R : ℝ =>
        (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, g s * s ^ (-α - 1))
        atTop (𝓝 (A / α * r ^ (-α) - A * ∫ s in Ioi r, g s * s ^ (-α - 1))) := by
      have h1 : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
      have h3 : Tendsto (fun R : ℝ => A / α * (r ^ (-α) - R ^ (-α))) atTop
          (𝓝 (A / α * r ^ (-α))) := by
        simpa using (tendsto_const_nhds.sub (tendsto_rpow_neg_atTop hα)).const_mul (A / α)
      have h4 := (intervalIntegral_tendsto_integral_Ioi r hIint tendsto_id).const_mul A
      simpa using (h1.add h3).sub h4
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_ge_atTop r] with R hR
    exact hfin r R hr hR
  -- positivity of the denominator and the closed formula
  have hden : ∀ r, r₀ ≤ r → 0 < 1 - α * r ^ α * ∫ s in Ioi r, g s * s ^ (-α - 1) ∧
      f r = α / A * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, g s * s ^ (-α - 1)) := by
    intro r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
    have hfr : 0 < f r := hpos r hr
    have heq : 1 - α * r ^ α * (∫ s in Ioi r, g s * s ^ (-α - 1)) = α / A * r ^ α * (f r)⁻¹ := by
      rw [hkey r hr, Real.rpow_neg hr0.le]
      field_simp
    rw [heq]
    refine ⟨by positivity, ?_⟩
    field_simp
  refine ⟨fun r hr => (hIoi r hr) ▸ hden r hr, fun hh => ?_⟩
  -- the relative error `α r^α ∫_r^∞ g s s^{-α-1} ds` tends to zero
  have hT : Tendsto (fun r => α * r ^ α * ∫ s in Ioi r, g s * s ^ (-α - 1)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hh (ε / 2) (by positivity)
    refine ⟨max N r₀, fun r hr => ?_⟩
    have hrN : N ≤ r := (le_max_left _ _).trans hr
    have hrr₀ : r₀ ≤ r := (le_max_right _ _).trans hr
    have hr0 : 0 < r := hr₀.trans_le hrr₀
    have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
    have hbint : IntegrableOn (fun s : ℝ => ε / 2 * s ^ (-α - 1)) (Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hr0).const_mul _
    have hbound : ‖∫ s in Ioi r, g s * s ^ (-α - 1)‖ ≤ ∫ s in Ioi r, ε / 2 * s ^ (-α - 1) := by
      refine norm_integral_le_of_norm_le hbint ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hr0.trans hs
      have hpow : 0 ≤ s ^ (-α - 1) := Real.rpow_nonneg hs0.le _
      have hgs : |g s| ≤ ε / 2 := by
        have := hN s (hrN.trans hs.le)
        rw [Real.dist_eq, sub_zero] at this
        rw [hgh s (hrr₀.trans hs.le)]
        exact this.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
      exact mul_le_mul_of_nonneg_right hgs hpow
    have hval : ∫ s in Ioi r, ε / 2 * s ^ (-α - 1) = ε / 2 * (r ^ (-α) / α) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hr0]
      congr 1
      rw [show -α - 1 + 1 = -α by ring, neg_div_neg_eq]
    rw [hval, Real.norm_eq_abs] at hbound
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (by positivity : 0 < α * r ^ α)]
    calc α * r ^ α * |∫ s in Ioi r, g s * s ^ (-α - 1)|
        ≤ α * r ^ α * (ε / 2 * (r ^ (-α) / α)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ε / 2 := by
          rw [Real.rpow_neg hr0.le]
          field_simp
      _ < ε := by linarith
  -- conclude `f / ((α/A) r^α) = 1 / (1 - T) → 1`
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun r => (1 - α * r ^ α * ∫ s in Ioi r, g s * s ^ (-α - 1))⁻¹) atTop
      (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hT).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hr0 : 0 < r := hr₀.trans_le hr
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  obtain ⟨hpos', hform⟩ := hden r hr
  rw [Pi.div_apply, hform]
  field_simp

end PercLib.Analysis
