/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for convex comparison under negative quadrant dependence with
preceding sums. All mathematical inputs come from the imported modules; no source proof is
copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.ConvexComparison

/-!
# Convex comparison for integrable increments: correspondence

Wiki correspondence for the convex comparison of a sum whose increments are negatively
quadrant dependent with their preceding sums against the sum of independent copies.

## Main results

* `convex_comparison_and_hinge_and_central_moment_of_tail_le`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped NNReal

namespace PercLib.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Let `Z₀, …, Z_{n-1}` be integrable real random variables with
`P(S_i ≥ u, Z_i ≥ v) ≤ P(S_i ≥ u) P(Z_i ≥ v)` for `1 ≤ i < n` and all real `u, v`, where
`S_i = Z₀ + ⋯ + Z_{i-1}`, and let `Z'_i` be independent with the same respective laws. Then
for every convex `φ : ℝ → ℝ`, `E φ(S_n) ≤ E φ(S'_n)` with both expectations well defined in
`(-∞, ∞]` (negative parts integrable; if the right side is finite so is the left, and the
inequality holds). In particular `E (S_n - a)₊ ≤ E (S'_n - a)₊` for real `a`, and
`E |S_n - E S_n|^r ≤ E |S'_n - E S'_n|^r` for `r ≥ 1`. -/
@[tag "3NBK"]
theorem convex_comparison_and_hinge_and_central_moment_of_tail_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ}
    {Z' : ℕ → Ω' → ℝ} {n : ℕ} (hZm : ∀ i < n, Measurable (Z i))
    (hZ : ∀ i < n, Integrable (Z i) μ) (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i)) :
    (∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ →
      Integrable (fun ω => (φ (∑ i ∈ range n, Z i ω))⁻) μ ∧
        Integrable (fun ω => (φ (∑ i ∈ range n, Z' i ω))⁻) μ' ∧
        (Integrable (fun ω => φ (∑ i ∈ range n, Z' i ω)) μ' →
          Integrable (fun ω => φ (∑ i ∈ range n, Z i ω)) μ ∧
            ∫ ω, φ (∑ i ∈ range n, Z i ω) ∂μ ≤ ∫ ω, φ (∑ i ∈ range n, Z' i ω) ∂μ')) ∧
      (∀ a : ℝ, ∫ ω, max (∑ i ∈ range n, Z i ω - a) 0 ∂μ ≤
        ∫ ω, max (∑ i ∈ range n, Z' i ω - a) 0 ∂μ') ∧
      ∀ r : ℝ, 1 ≤ r →
        ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range n, Z i ω - ∫ ω', ∑ i ∈ range n, Z i ω' ∂μ| ^ r)
            ∂μ ≤
          ∫⁻ ω, ENNReal.ofReal
            (|∑ i ∈ range n, Z' i ω - ∫ ω', ∑ i ∈ range n, Z' i ω' ∂μ'| ^ r) ∂μ' :=
  ⟨fun _ hφ => convex_comparison_sum_of_tail_le hZm hZ hZ'm htail hind hlaw hφ,
    integral_max_sub_le_of_tail_le hZm hZ hZ'm htail hind hlaw,
    fun _ hr => lintegral_abs_sub_integral_rpow_le_of_tail_le hZm hZ hZ'm htail hind hlaw hr⟩

end PercLib.Probability
