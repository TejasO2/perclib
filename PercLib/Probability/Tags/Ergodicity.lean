/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for the zero-one law under law-preserving separating relabellings.
Every statement is assembled from lemmas proved in the imported modules; no new definition
is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.Mixing

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set

namespace PercLib.Probability
variable {ι : Type*}

/-- Ergodicity: under relabellings that preserve the Bernoulli law and separate finite
sets, invariant measurable events have probability `0` or `1`, and invariant measurable
`ℕ∞`-valued observables take some value with probability one. -/
@[tag "DRQ2"]
theorem prodBernoulli_ergodic (p : ι → unitInterval) (e : ℕ → ι ≃ ι)
    (hpres : ∀ n, MeasurePreserving (fun ω : Set ι => e n '' ω)
      (prodBernoulli p) (prodBernoulli p))
    (hsep : ∀ F G : Finset ι, ∀ᶠ n in atTop, ∀ i ∈ F, e n i ∉ G) :
    (∀ A : Set (Set ι), MeasurableSet A → (∀ n, (fun ω : Set ι => e n '' ω) ⁻¹' A = A) →
      prodBernoulli p A = 0 ∨ prodBernoulli p A = 1) ∧
    (∀ f : Set ι → ℕ∞, Measurable f → (∀ n ω, f (e n '' ω) = f ω) →
      ∃ c : ℕ∞, prodBernoulli p {ω | f ω = c} = 1) := by
  refine ⟨fun A hA hinv => prodBernoulli_eq_zero_or_one_of_invariant p e hpres hsep hA hinv,
    fun f hf hinv => ?_⟩
  obtain ⟨c, hc⟩ := prodBernoulli_ae_eq_const_of_invariant p e hpres hsep hf hinv
  refine ⟨c, (prob_compl_eq_zero_iff (hf (measurableSet_singleton c))).1 ?_⟩
  rw [ae_iff] at hc
  exact hc

end PercLib.Probability
