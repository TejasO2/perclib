/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.SpatialMoments.LocalizationMetric

/-!
# Correspondence wrapper: a spatial moment localizes the first volume moment

All mathematical inputs are proved in
`PercLib.Percolation.Bond.SpatialMoments.LocalizationMetric`.

## Main results

* `chi_localization_of_correlationLength_le`: the three clauses of the localization of the
  first volume moment by a correlation-length bound, over a family of profiles `q r`, `r ≥ 1`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-- On a countable pseudometric vertex type with root `o`, let `q r` (`r ≥ 1`) be profiles
whose root clusters `K_r` have finite positive mean size `χ_r`. If for one `p > 0` the
correlation length `ξ_p(r) = (E[∑_{x ∈ K_r} d(o, x)^p] / χ_r)^{1/p}` satisfies
`ξ_p(r) ≤ C_p r` for every `r ≥ 1`, then, with `Z_{r,C} = |K_r \ B_{C r}|`:
for every `C > 0` and `r ≥ 1`, `E Z_{r,C} / χ_r ≤ (C_p / C)^p`; for every `ε > 0` one
`C > 0` gives `χ_r ≤ (1 + ε) E|K_r ∩ B_{C r}|` for all `r ≥ 1`; and for every `C > 0` and
`r ≥ 1`, `P(Z_{r,C} > 0) ≤ χ_r (C_p / C)^p`. -/
@[tag "32GP"]
theorem chi_localization_of_correlationLength_le {V : Type*} [Countable V]
    [PseudoMetricSpace V] (o : V) (q : ℝ → Sym2 V → unitInterval)
    (hχ : ∀ r : ℝ, 1 ≤ r → 0 < chi (q r) o ∧ chi (q r) o < ⊤)
    {p : ℝ} (hp : 0 < p) (Cp : ℝ≥0)
    (hξ : ∀ r : ℝ, 1 ≤ r →
      ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
          ∂law (q r)) / chi (q r) o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    (∀ C : ℝ, 0 < C → ∀ r : ℝ, 1 ≤ r →
      (∫⁻ ω, ((cluster ω o \ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂law (q r)) /
          chi (q r) o ≤ ENNReal.ofReal ((Cp / C) ^ p)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      chi (q r) o ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((cluster ω o ∩ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂law (q r)) ∧
    (∀ C : ℝ, 0 < C → ∀ r : ℝ, 1 ≤ r →
      law (q r) {ω | 0 < (cluster ω o \ Metric.closedBall o (C * r)).encard} ≤
        chi (q r) o * ENNReal.ofReal ((Cp / C) ^ p)) := by
  refine ⟨fun C hC r hr => ?_, fun ε hε => ?_, fun C hC r hr => ?_⟩
  · exact lintegral_encard_diff_closedBall_div_chi_le (q r) o hp (by linarith) hC
      (hχ r hr).1 (hχ r hr).2 (hξ r hr)
  · obtain ⟨C, hC, h⟩ :=
      exists_chi_le_mul_lintegral_encard_inter_closedBall (V := V) (Cp := Cp) hp hε
    exact ⟨C, hC, fun r hr => h (q r) o r (by linarith) (hχ r hr).2 (hξ r hr)⟩
  · exact law_encard_diff_closedBall_pos_le (q r) o hp (by linarith) hC (hχ r hr).2 (hξ r hr)

end PercLib.Percolation.Bond
