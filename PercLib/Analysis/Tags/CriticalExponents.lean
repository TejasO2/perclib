/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for the critical-exponents assertion UBFE, proved from
`LogExponent.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.LogExponent

@[expose] public section
noncomputable section

open Filter Asymptotics Real
open scoped Topology

namespace PercLib.Analysis

/-- **UBFE.** Asymptotic equivalence `f ~ c x^α` (`c > 0`) implies `f ≍ x^α`; `f ≍ x^α` with
`f` eventually positive implies logarithmic exponent `α`; `x^α (log x)^b (log log x)^c` has
logarithmic exponent `α` and is `≍ x^α` only when `b = c = 0`; and for every `α` some eventually
positive `f ≍ x^α` is not asymptotically equivalent to any `c x^α`. -/
@[tag "UBFE"]
theorem log_exponent_hierarchy :
    (∀ (f : ℝ → ℝ) (α c : ℝ), 0 < c → (f ~[atTop] fun x => c * x ^ α) →
      f =Θ[atTop] fun x => x ^ α) ∧
    (∀ (f : ℝ → ℝ) (α : ℝ), (∀ᶠ x in atTop, 0 < f x) → (f =Θ[atTop] fun x => x ^ α) →
      Tendsto (fun x => log (f x) / log x) atTop (𝓝 α)) ∧
    (∀ α b c : ℝ,
      Tendsto (fun x => log (x ^ α * log x ^ b * log (log x) ^ c) / log x) atTop (𝓝 α) ∧
      (((fun x => x ^ α * log x ^ b * log (log x) ^ c) =Θ[atTop] fun x => x ^ α) ↔
        b = 0 ∧ c = 0)) ∧
    (∀ α : ℝ, ∃ f : ℝ → ℝ, (∀ᶠ x in atTop, 0 < f x) ∧ (f =Θ[atTop] fun x => x ^ α) ∧
      ∀ c, ¬ f ~[atTop] fun x => c * x ^ α) := by
  refine ⟨fun f α c hc h => isTheta_rpow_of_isEquivalent hc h,
    fun f α hf h => tendsto_log_div_log_of_isTheta_rpow hf h,
    fun α b c => ⟨tendsto_log_div_log_rpow_mul_log_rpow_mul_log_log_rpow α b c,
      isTheta_rpow_mul_log_rpow_mul_log_log_rpow_iff α b c⟩, fun α => ?_⟩
  have hs : ∀ x : ℝ, 1 ≤ 2 + sin x := fun x => by linarith [neg_one_le_sin x]
  refine ⟨fun x => (2 + sin x) * x ^ α, ?_, isTheta_two_add_sin_mul_rpow α, fun c => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos (by linarith [hs x]) (rpow_pos_of_pos hx α)
  rcases lt_or_ge 0 c with hc | hc
  · exact not_isEquivalent_two_add_sin_mul_rpow α hc
  · -- for `c ≤ 0`, `f ~ c x^α` would force `f ≤ c x^α / 2 ≤ 0` eventually
    intro h
    obtain ⟨x, hx⟩ := ((h.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)).and
      (eventually_gt_atTop (0 : ℝ))).exists
    obtain ⟨hb, hx0⟩ := hx
    have hxa : 0 < x ^ α := rpow_pos_of_pos hx0 α
    have hv : c * x ^ α ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hxa.le
    have hf : 0 < (2 + sin x) * x ^ α := mul_pos (by linarith [hs x]) hxa
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonpos hv] at hb
    have := le_abs_self ((2 + sin x) * x ^ α - c * x ^ α)
    linarith

end PercLib.Analysis
