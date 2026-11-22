/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied. The limit law comes from
mathlib's compactness of the space of probability measures on a compact space
(`Mathlib/MeasureTheory/Measure/Prokhorov.lean`) and the portmanteau theorem for clopen sets.
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import PercLib.Probability.Characterization

/-!
# Cylinder events: inclusion–exclusion and limit laws

An event `A ⊆ Set ι` is a *cylinder event* on a finite set `F` of coordinates when it is
determined by them: `ω ∈ A ↔ ω ∩ F ∈ A` for every `ω`. This file proves two general facts about
such events.

**Inclusion–exclusion.** The indicator of a cylinder event on `F` is a fixed signed combination
of the indicators of the all-open events `{F' ⊆ ω}`, `F' ⊆ F`:
`1_A(ω) = ∑_{S ⊆ F} c_A(S) 1{S ⊆ ω}` with `c_A(S) = ∑_{T ⊆ S} (-1)^{|S| - |T|} 1_A(T)`.
Hence `μ(A) = ∑_{S ⊆ F} c_A(S) μ(S ⊆ ω)` for every finite measure `μ`, and probabilities of
cylinder events converge as soon as those of the all-open events do. The combinatorial core is
Möbius inversion on the Boolean lattice of subsets of `F`.

**Limit laws.** For a countable index type `ι`, if probability laws `μ_a` on `Set ι` have
convergent probabilities of every cylinder event along a filter, then some probability law `ν`
on `Set ι` has these limits as its probabilities of cylinder events. Mathlib has no general
Kolmogorov extension theorem. The proof transports the laws to the compact space `ι → Bool`,
where the space of probability measures is compact (mathlib's Prokhorov theorem, via
Riesz–Markov–Kakutani). It takes a cluster point there. Cylinder events are clopen, so their
probabilities are continuous in the law (portmanteau), and the cluster point has the limits as
its values. Convergence of the all-open probabilities alone suffices, by inclusion–exclusion.

Nothing here is about percolation: the index type, the measures and the filter are arbitrary
(the index type countable for the limit law). This file adds no definition.

## Main results

* `Finset.sum_powerset_filter_subset_neg_one_pow`, `Finset.moebius_inversion_powerset`: Möbius
  inversion on the subsets of a finite set.
* `measurableSet_of_determined_finset`: cylinder events are measurable.
* `indicator_eq_sum_subset_of_determined`: inclusion–exclusion for indicators of cylinder events.
* `measureReal_eq_sum_subset_of_determined`: the same for finite measures;
  `tendsto_measureReal_of_determined`: limits of cylinder probabilities from limits of
  all-open probabilities.
* `exists_measure_of_tendsto_cylinder`: a probability law with prescribed limits of cylinder
  probabilities; `exists_measure_of_tendsto_subset`: the same from the all-open events only.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ### Möbius inversion on the subsets of a finite set -/

namespace Finset

variable {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]

/-- For `T ⊆ U`, `∑_{T ⊆ S ⊆ U} (-1)^{|S| - |T|}` is `1` if `T = U` and `0` otherwise. -/
theorem sum_powerset_filter_subset_neg_one_pow {T U : Finset α} (h : T ⊆ U) :
    ∑ S ∈ U.powerset with T ⊆ S, (-1 : R) ^ (#S - #T) = if T = U then 1 else 0 := by
  have e : ∑ S ∈ U.powerset with T ⊆ S, (-1 : R) ^ (#S - #T) =
      ∑ V ∈ (U \ T).powerset, (-1 : R) ^ #V := by
    refine sum_nbij' (fun S => S \ T) (fun V => T ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS ⊢
      exact sdiff_subset_sdiff hS.1 subset_rfl
    · intro V hV
      simp only [mem_filter, mem_powerset] at hV ⊢
      exact ⟨union_subset h (hV.trans sdiff_subset), subset_union_left⟩
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS
      exact union_sdiff_of_subset hS.2
    · intro V hV
      simp only [mem_powerset] at hV
      rw [union_sdiff_left]
      exact sdiff_eq_self_of_disjoint (disjoint_of_subset_left hV disjoint_sdiff_self_left)
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS
      rw [card_sdiff_of_subset hS.2]
  have hz := congrArg (Int.cast : ℤ → R) (Finset.sum_powerset_neg_one_pow_card (x := U \ T))
  push_cast at hz
  rw [e, hz]
  by_cases hTU : T = U
  · subst hTU
    simp
  · have hne : U \ T ≠ ∅ := by
      rw [Ne, sdiff_eq_empty_iff_subset]
      exact fun hUT => hTU (h.antisymm hUT)
    simp [hTU, hne]

/-- **Möbius inversion on the subsets of `F`.** For `U ⊆ F` and any `a : Finset α → R`,
`∑_{S ⊆ F} (∑_{T ⊆ S} (-1)^{|S| - |T|} a(T)) 1{S ⊆ U} = a(U)`. -/
theorem moebius_inversion_powerset {F U : Finset α} (hU : U ⊆ F) (a : Finset α → R) :
    ∑ S ∈ F.powerset, (∑ T ∈ S.powerset, (-1 : R) ^ (#S - #T) * a T) *
      (if S ⊆ U then 1 else 0) = a U := by
  have h₁ : ∑ S ∈ F.powerset, (∑ T ∈ S.powerset, (-1 : R) ^ (#S - #T) * a T) *
      (if S ⊆ U then 1 else 0) =
      ∑ S ∈ U.powerset, ∑ T ∈ S.powerset, (-1 : R) ^ (#S - #T) * a T := by
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext S
    simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hU, h⟩⟩
  rw [h₁, sum_comm' (s' := fun T => U.powerset.filter (T ⊆ ·)) (t' := U.powerset)]
  · simp_rw [← sum_mul]
    rw [sum_congr rfl fun T hT => by
      rw [sum_powerset_filter_subset_neg_one_pow (mem_powerset.1 hT)]]
    simp [ite_mul]
  · intro S T
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨h, h.2.trans h.1⟩, fun h => h.1⟩

end Finset

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Inclusion–exclusion for cylinder events -/

/-- **Cylinder events are measurable.** An event determined by a finite set `F` of
coordinates is measurable. -/
theorem measurableSet_of_determined_finset {F : Finset ι} {A : Set (Set ι)}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) : MeasurableSet A := by
  have hpre : A = (fun ω : Set ι => fun i : F => (i : ι) ∈ ω) ⁻¹'
      {p | {x | ∃ hx : x ∈ F, p ⟨x, hx⟩} ∈ A} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hA ω]
    have hset : {x | ∃ hx : x ∈ F, x ∈ ω} = ω ∩ ↑F := by
      ext x
      simp [and_comm]
    rw [hset]
  rw [hpre]
  exact (measurable_pi_iff.2 fun (i : F) => measurable_set_mem (i : ι) :
    Measurable fun (ω : Set ι) (i : F) => (i : ι) ∈ ω) (Set.to_countable _).measurableSet

/-- **Inclusion–exclusion for cylinder events.** If `A` is determined by the finite set `F`,
its indicator is the signed combination
`1_A(ω) = ∑_{S ⊆ F} (∑_{T ⊆ S} (-1)^{|S| - |T|} 1_A(T)) 1{S ⊆ ω}`
of the indicators of the all-open events `{S ⊆ ω}`, with coefficients that do not depend on
`ω`. -/
theorem indicator_eq_sum_subset_of_determined {R : Type*} [CommRing R] {F : Finset ι}
    {A : Set (Set ι)} (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) (ω : Set ι) :
    A.indicator (1 : Set ι → R) ω =
      ∑ S ∈ F.powerset, (∑ T ∈ S.powerset, (-1 : R) ^ (S.card - T.card) *
        A.indicator 1 (T : Set ι)) * {ω' : Set ι | (S : Set ι) ⊆ ω'}.indicator 1 ω := by
  classical
  set U := F.filter (· ∈ ω) with hU
  have hUF : U ⊆ F := Finset.filter_subset _ _
  have hωU : ω ∩ ↑F = ↑U := by
    ext i
    simp [hU, and_comm]
  have hAU : A.indicator (1 : Set ι → R) ω = A.indicator 1 (U : Set ι) := by
    have hiff : ω ∈ A ↔ (U : Set ι) ∈ A := by rw [hA ω, hωU]
    by_cases h : ω ∈ A
    · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h (hiff.2 h')]
  have hind : ∀ S ∈ F.powerset, {ω' : Set ι | (S : Set ι) ⊆ ω'}.indicator (1 : Set ι → R) ω =
      if S ⊆ U then 1 else 0 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hiff : (S : Set ι) ⊆ ω ↔ S ⊆ U := by
      constructor
      · intro h i hi
        simp only [hU, Finset.mem_filter]
        exact ⟨hS hi, h hi⟩
      · intro h i hi
        exact (Finset.mem_filter.1 (h hi)).2
    by_cases h : S ⊆ U
    · simp [h, indicator_of_mem (show ω ∈ {ω' : Set ι | (S : Set ι) ⊆ ω'} from hiff.2 h)]
    · simp [h, indicator_of_notMem (show ω ∉ {ω' : Set ι | (S : Set ι) ⊆ ω'} from
        fun h' => h (hiff.1 h'))]
  rw [hAU, Finset.sum_congr rfl fun S hS => by rw [hind S hS]]
  exact (Finset.moebius_inversion_powerset hUF fun T => A.indicator 1 (T : Set ι)).symm

/-- **Inclusion–exclusion for cylinder probabilities.** If `A` is determined by the finite set
`F`, then for every finite measure `μ`,
`μ(A) = ∑_{S ⊆ F} (∑_{T ⊆ S} (-1)^{|S| - |T|} 1_A(T)) μ(S ⊆ ω)`. -/
theorem measureReal_eq_sum_subset_of_determined (μ : Measure (Set ι)) [IsFiniteMeasure μ]
    {F : Finset ι} {A : Set (Set ι)} (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) :
    μ.real A = ∑ S ∈ F.powerset, (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
      A.indicator 1 (T : Set ι)) * μ.real {ω | (S : Set ι) ⊆ ω} := by
  rw [← integral_indicator_one (measurableSet_of_determined_finset hA)]
  have h : (fun ω => A.indicator (1 : Set ι → ℝ) ω) = fun ω =>
      ∑ S ∈ F.powerset, (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
        A.indicator 1 (T : Set ι)) * {ω' : Set ι | (S : Set ι) ⊆ ω'}.indicator 1 ω :=
    funext (indicator_eq_sum_subset_of_determined hA)
  rw [h, integral_finsetSum]
  · refine Finset.sum_congr rfl fun S _ => ?_
    rw [integral_const_mul, integral_indicator_one (measurableSet_setOf_finset_coe_subset S)]
  · intro S _
    exact ((integrable_const (1 : ℝ)).indicator
      (measurableSet_setOf_finset_coe_subset S)).const_mul _

/-- **Limits of cylinder probabilities.** If `A` is determined by the finite set `F` and the
probabilities of the all-open events `{S ⊆ ω}`, `S ⊆ F`, converge along a filter, then so does
the probability of `A`, to the corresponding signed combination of the limits. -/
theorem tendsto_measureReal_of_determined {α : Type*} {L : Filter α} (μ : α → Measure (Set ι))
    [∀ a, IsFiniteMeasure (μ a)] {F : Finset ι} {A : Set (Set ι)}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) {x : Finset ι → ℝ}
    (h : ∀ S ∈ F.powerset, Tendsto (fun a => (μ a).real {ω | (S : Set ι) ⊆ ω}) L (𝓝 (x S))) :
    Tendsto (fun a => (μ a).real A) L (𝓝 (∑ S ∈ F.powerset, (∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * A.indicator 1 (T : Set ι)) * x S)) := by
  have e : (fun a => (μ a).real A) = fun a => ∑ S ∈ F.powerset, (∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * A.indicator 1 (T : Set ι)) *
        (μ a).real {ω | (S : Set ι) ⊆ ω} :=
    funext fun a => measureReal_eq_sum_subset_of_determined (μ a) hA
  rw [e]
  exact tendsto_finsetSum _ fun S hS => (h S hS).const_mul _

/-! ### A law from limits of cylinder probabilities -/

/-- **A law from convergent cylinder probabilities.** Let `ι` be countable and `μ_a` probability
laws on `Set ι` indexed along a nontrivial filter `L`. If the probability of every cylinder event
(an event determined by finitely many coordinates) converges along `L`, then some probability
law `ν` on `Set ι` has these limits as its probabilities of cylinder events. -/
theorem exists_measure_of_tendsto_cylinder [Countable ι] {α : Type*} {L : Filter α} [L.NeBot]
    (μ : α → Measure (Set ι)) [∀ a, IsProbabilityMeasure (μ a)]
    (h : ∀ (F : Finset ι) (A : Set (Set ι)), (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
      ∃ l, Tendsto (fun a => μ a A) L (𝓝 l)) :
    ∃ ν : Measure (Set ι), IsProbabilityMeasure ν ∧
      ∀ (F : Finset ι) (A : Set (Set ι)), (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
        Tendsto (fun a => μ a A) L (𝓝 (ν A)) := by
  classical
  -- transport to the compact space `ι → Bool`
  let φ : Set ι → (ι → Bool) := fun ω i => decide (i ∈ ω)
  let ψ : (ι → Bool) → Set ι := fun x => {i | x i = true}
  have hφ : Measurable φ := by
    refine measurable_pi_iff.2 fun i => measurable_to_countable' fun b => ?_
    cases b
    · have : (fun ω : Set ι => decide (i ∈ ω)) ⁻¹' {false} = {ω | i ∈ ω}ᶜ := by
        ext ω
        simp
      rw [this]
      exact (measurableSet_mem i).compl
    · have : (fun ω : Set ι => decide (i ∈ ω)) ⁻¹' {true} = {ω | i ∈ ω} := by
        ext ω
        simp
      rw [this]
      exact measurableSet_mem i
  have hψ : Measurable ψ := by
    refine measurable_set_iff.2 fun i => ?_
    have hi : Measurable fun x : ι → Bool => x i := measurable_pi_apply i
    exact measurableSet_setOfPred.1 (hi (measurableSet_singleton true))
  have hψφ : ∀ ω, ψ (φ ω) = ω := by
    intro ω
    ext i
    simp [ψ, φ]
  -- the transported laws and a cluster point of them
  let ν' : α → ProbabilityMeasure (ι → Bool) := fun a =>
    ⟨(μ a).map φ, inferInstance⟩
  obtain ⟨νl, hνl⟩ := exists_clusterPt_of_compactSpace (map ν' L)
  refine ⟨(νl : Measure (ι → Bool)).map ψ, inferInstance,
    fun F A hA => ?_⟩
  obtain ⟨l, hl⟩ := h F A hA
  have hAm : MeasurableSet A := measurableSet_of_determined_finset hA
  set C := ψ ⁻¹' A with hC
  have hCm : MeasurableSet C := hAm.preimage hψ
  have hφC : φ ⁻¹' C = A := by
    ext ω
    simp only [hC, mem_preimage, hψφ]
  -- `C` is clopen: it depends only on the coordinates in `F`
  have hCclopen : IsClopen C := by
    let r : (ι → Bool) → (F → Bool) := fun x i => x i
    have hr : Continuous r := continuous_pi fun i => continuous_apply (i : ι)
    have hsat : C = r ⁻¹' (r '' C) := by
      refine (subset_preimage_image r C).antisymm ?_
      rintro x ⟨x', hx', hxx'⟩
      have hint : ψ x ∩ ↑F = ψ x' ∩ ↑F := by
        ext j
        simp only [mem_inter_iff, Finset.mem_coe]
        constructor
        · rintro ⟨hj, hjF⟩
          refine ⟨?_, hjF⟩
          have := congrFun hxx' ⟨j, hjF⟩
          simp only [r] at this
          simpa [ψ, this] using hj
        · rintro ⟨hj, hjF⟩
          refine ⟨?_, hjF⟩
          have := congrFun hxx' ⟨j, hjF⟩
          simp only [r] at this
          simpa [ψ, ← this] using hj
      change ψ x ∈ A
      rw [hA, hint, ← hA]
      exact hx'
    rw [hsat]
    exact (isClopen_discrete _).preimage hr
  -- the probability of `C` is continuous in the law, so the cluster point has the limit
  have hν'C : ∀ a, ((ν' a C : NNReal) : ℝ≥0∞) = μ a A := by
    intro a
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    change (μ a).map φ C = μ a A
    rw [Measure.map_apply hφ hCm, hφC]
  have hcont : ContinuousAt (fun ν : ProbabilityMeasure (ι → Bool) => ((ν C : NNReal) : ℝ≥0∞))
      νl :=
    (ENNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto (μs := id) tendsto_id hCclopen)
  have hcl := hνl.map hcont (tendsto_map'_iff.2 tendsto_map)
  have hl' : Tendsto ((fun ν : ProbabilityMeasure (ι → Bool) => ((ν C : NNReal) : ℝ≥0∞)) ∘ ν')
      L (𝓝 l) := by
    refine hl.congr fun a => ?_
    simp only [Function.comp_apply, hν'C]
  have heq : ((νl C : NNReal) : ℝ≥0∞) = l := eq_of_nhds_neBot (hcl.mono hl').neBot
  rw [Measure.map_apply hψ hAm, ← hC, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    heq]
  exact hl

/-- **A law from convergent all-open probabilities.** Let `ι` be countable and `μ_a`
probability laws on `Set ι` along a nontrivial filter `L`. If for every finite `F ⊆ ι` the
probability that all of `F` is open converges along `L`, then some probability law `ν` on
`Set ι` is the limit on every cylinder event. -/
theorem exists_measure_of_tendsto_subset [Countable ι] {α : Type*} {L : Filter α} [L.NeBot]
    (μ : α → Measure (Set ι)) [∀ a, IsProbabilityMeasure (μ a)]
    (h : ∀ F : Finset ι, ∃ l, Tendsto (fun a => μ a {ω | (F : Set ι) ⊆ ω}) L (𝓝 l)) :
    ∃ ν : Measure (Set ι), IsProbabilityMeasure ν ∧
      ∀ (F : Finset ι) (A : Set (Set ι)), (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
        Tendsto (fun a => μ a A) L (𝓝 (ν A)) := by
  refine exists_measure_of_tendsto_cylinder μ fun F A hA => ?_
  choose l hl using h
  have hlt : ∀ S, l S ≠ ∞ := fun S =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_tendsto' (hl S) fun a => prob_le_one)
  have hreal : ∀ S ∈ F.powerset,
      Tendsto (fun a => (μ a).real {ω | (S : Set ι) ⊆ ω}) L (𝓝 (l S).toReal) :=
    fun S _ => (ENNReal.tendsto_toReal (hlt S)).comp (hl S)
  have h₁ := ENNReal.tendsto_ofReal (tendsto_measureReal_of_determined μ hA hreal)
  exact ⟨_, h₁.congr fun a => ofReal_measureReal⟩

end PercLib.Probability

end
