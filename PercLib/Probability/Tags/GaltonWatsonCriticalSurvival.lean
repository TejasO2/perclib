/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the survival probability of a critical Galton–Watson process. All
mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GaltonWatsonCriticalSurvival

/-!
# Critical survival to generation `n`: statement form

## Main results

* `galtonWatson_survival_isEquivalent`: for mean one and finite positive variance `σ²`,
  `P(Zₙ > 0) ~ 2/(σ² n)`.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics
open scoped ENNReal

namespace PercLib.Probability

/-- For an offspring law `p` with mean `m = ∑ k p(k) = 1` and variance
`σ² = ∑ (k - 1)² p(k)` finite and positive, the Galton–Watson process satisfies
`P(Zₙ > 0) ~ 2/(σ² n)` as `n → ∞`. -/
@[tag "8WO7"]
theorem galtonWatson_survival_isEquivalent (p : PMF ℕ) (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1)
    {σ2 : ℝ} (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    (fun n : ℕ => (galtonWatsonMeasure p {ω | 0 < generationSize n ω}).toReal) ~[atTop]
      fun n : ℕ => 2 / (σ2 * n) :=
  isEquivalent_measureReal_generationSize_pos p hm hσ hσ0

end PercLib.Probability
