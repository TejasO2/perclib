/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for the integrated-susceptibility assertion 6PGV, proved from
`LogarithmicCorrections.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.LogarithmicCorrections

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- **6PGV.** Let `0 ≤ β₀ < β_c`, `χ > 0` nondecreasing and locally absolutely continuous on
`(β₀, β_c)`, `D ≥ 1` measurable and `χ' ≥ (χ - D)₊²/(3β²D²)` a.e. on `(β₀, β_c)`. Then
`χ(β) ≤ (1 + 2(β_c - β)/(3ββ_c)) (∫_β^{β_c} ds/(3s²D(s)²))⁻¹` for every `β ∈ (β₀, β_c)`, and if
`D(β_c - u) ≤ C (log(1/u))^a` for small `u > 0` (`C > 0`, `a ≥ 0`), then
`χ(β_c - ε) = O(ε⁻¹ (log(1/ε))^{2a})` as `ε ↓ 0`. -/
@[tag "6PGV"]
theorem integrated_susceptibility_bounds {β₀ βc : ℝ} {χ D : ℝ → ℝ} (hβ₀ : 0 ≤ β₀)
    (hlt : β₀ < βc) (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      max (χ β - D β) 0 ^ 2 / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β) :
    (∀ β ∈ Ioo β₀ βc,
      χ β ≤ (1 + 2 * (βc - β) / (3 * β * βc)) * (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹) ∧
    (∀ {C a : ℝ}, 0 < C → 0 ≤ a → (∀ᶠ u in 𝓝[>] 0, D (βc - u) ≤ C * Real.log (1 / u) ^ a) →
      (fun ε => χ (βc - ε)) =O[𝓝[>] 0] fun ε => ε⁻¹ * Real.log (1 / ε) ^ (2 * a)) :=
  ⟨fun _ hβ => le_of_deriv_ge_sq_div hβ₀ hpos hmono hac hD hD1 hder hβ,
    fun hC ha h => isBigO_of_deriv_ge_sq_div hβ₀ hlt hpos hmono hac hD hD1 hder hC ha h⟩

end PercLib.Analysis
