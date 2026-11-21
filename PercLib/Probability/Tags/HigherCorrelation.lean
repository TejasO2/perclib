/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the insertion recursion of higher correlations and the correlation
of nested events, proved in `PercLib.Probability.HigherCorrelation`. Mathematical reference:
E. H. Lieb and S. Sahi, *On the extension of the FKG inequality to n functions*, J. Math. Phys.
63 (2022), Section 2. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.HigherCorrelation

/-!
# Higher correlations: insertion recursion and nested events

## Main results

* `PercLib.higherCorrelation_insert_and_indicator_nested`: the recursion obtained by inserting
  one argument, and the product formula with its nonnegativity for nested events.
-/

@[expose] public section

open MeasureTheory Finset

namespace PercLib

universe u

/-- **Insertion of one argument gives a correlation recursion and a nested-event product
formula.** The higher correlation `E_s(f) = higherCorrelation μ s f` of a finite family is
indexed by a finset, so `E_n(f_1, …, f_{n-1}, f)` is `E_{insert a s}` of a family `f` with
`f a = f` and `s` indexing `f_1, …, f_{n-1}` (`n ≥ 2` is `s` nonempty). Then
`E_n(f_1, …, f_{n-1}, f) = ∑_{i=1}^{n-1} E_{n-1}(f_1, …, f_i f, …, f_{n-1}) - (∫ f) E_{n-1}(f_1, …,
f_{n-1})`; the identity needs no boundedness. Under a probability measure, if
`A 0 ⊆ ⋯ ⊆ A (n-1)` are measurable events with probabilities `a_j`, then
`E_n(1_{A 0}, …, 1_{A (n-1)}) = a_0 ∏_{j=1}^{n-1} (j - a_j) ≥ 0`, which is
`a_1 ∏_{j=2}^n (j - 1 - a_j) ≥ 0` in one-based indexing. -/
@[tag "AFJX"]
theorem higherCorrelation_insert_and_indicator_nested {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) :
    (∀ (ι : Type u) [DecidableEq ι] (a : ι) (s : Finset ι), a ∉ s → s.Nonempty →
      ∀ f : ι → Ω → ℝ, higherCorrelation μ (insert a s) f =
        ∑ i ∈ s, higherCorrelation μ s (Function.update f i (f i * f a)) -
          (∫ ω, f a ω ∂μ) * higherCorrelation μ s f) ∧
    (IsProbabilityMeasure μ → ∀ (n : ℕ) (hn : 0 < n) (A : Fin n → Set Ω),
      (∀ i, MeasurableSet (A i)) → Monotone A →
      higherCorrelation μ univ (fun i ↦ (A i).indicator 1) =
          μ.real (A ⟨0, hn⟩) *
            ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j)) ∧
        0 ≤ μ.real (A ⟨0, hn⟩) *
            ∏ j ∈ (univ : Finset (Fin n)).erase ⟨0, hn⟩, (((j : ℕ) : ℝ) - μ.real (A j))) :=
  ⟨fun _ _ _ _ ha hs f ↦ higherCorrelation_insert μ ha hs f,
    fun _ _ hn A hA hmono ↦ higherCorrelation_indicator_fin_of_monotone μ hn A hA hmono⟩

end PercLib
