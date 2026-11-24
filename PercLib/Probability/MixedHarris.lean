/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-23. No upstream proof is copied: everything is derived from
Harris's inequality (`PercLib.Probability.prodBernoulli_harris`) by flipping coordinates, and from
the splicing of `PercLib.Probability.LocallyMonotone`.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Lemma 13 and the gluing of separated arms (Proposition 12).
-/
module

public import PercLib.Probability.LocallyMonotone

/-!
# Harris's inequality for a mixed order

Fix a set `D` of coordinates and order configurations by `ω ≤ ω'` when `ω'` has more open
coordinates than `ω` off `D` and fewer on `D`: `ω \ D ⊆ ω' \ D` and `ω' ∩ D ⊆ ω ∩ D`. An event is
**upper for the mixed order** when it is closed upwards for this order, that is, increasing in the
coordinates off `D` and decreasing in those in `D`. Flipping the coordinates in `D`
(`ω ↦ ω ∆ D`) turns the mixed order into inclusion, and turns the product Bernoulli law with
profile `p` into the product law with profile `1 - p` on `D` and `p` off `D`. So Harris's
inequality holds for the mixed order, for every profile on every index type:
`P(A) P(B) ≤ P(A ∩ B)` for measurable events `A`, `B` upper for the mixed order.

The conditional form is what the gluing of separated arms uses. The event `A` there (separated
arms with their fences) is not monotone at all; but once the coordinates outside a set `T` are
fixed, it is increasing in the open corridors and decreasing in the dual corridors, which make up
`T`. If `B` (the corridor crossings) is determined by `T` and upper for the mixed order, then
conditioning on the coordinates outside `T` and applying the mixed Harris inequality to the
sections gives `P(A) P(B) ≤ P(A ∩ B)` again. Nolin's Lemma 13
(`prodBernoulli_mul_mul_le_inter_of_determined`) is the case of an event `A` that is the
intersection of an increasing and a decreasing event.

Nothing here is planar. This file adds no definition.

## Main results

* `prodBernoulli_map_symmDiff`: flipping the coordinates in `D` flips the profile on `D`.
* `prodBernoulli_harris_of_mixed`: **Harris for a mixed order**.
* `prodBernoulli_prod_le_biInter_of_mixed`: the same for finitely many events.
* `prodBernoulli_mul_le_inter_of_mixed_of_determined`: **the conditional form**, for an event
  whose sections at fixed coordinates outside `T` are upper for the mixed order and an event
  determined by `T` and upper for the mixed order.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal symmDiff

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Flipping coordinates -/

/-- **Flipping the coordinates in `D`.** If `ω` has law `prodBernoulli p`, then `ω ∆ D` has the
product law with open probability `1 - p i` on `D` and `p i` off `D`. -/
theorem prodBernoulli_map_symmDiff (p : ι → unitInterval) (D : Set ι) [DecidablePred (· ∈ D)] :
    (prodBernoulli p).map (· ∆ D) =
      prodBernoulli (fun i => if i ∈ D then unitInterval.symm (p i) else p i) := by
  have hset : Measurable (fun P : ι → Prop => {i | P i}) :=
    MeasurableEquiv.setOfPred.measurable
  have hflip : ∀ i, Measurable (fun P : Prop => if i ∈ D then ¬ P else P) := fun i =>
    measurable_from_top
  have hsd : Measurable (fun ω : Set ι => ω ∆ D) := measurable_id.symmDiff measurable_const
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map hsd hset]
  have hcomp : ((· ∆ D) ∘ fun P : ι → Prop => {i | P i}) =
      (fun P : ι → Prop => {i | P i}) ∘ (fun P : ι → Prop => fun i =>
        (fun Q : Prop => if i ∈ D then ¬ Q else Q) (P i)) := by
    funext P
    ext i
    by_cases hi : i ∈ D <;> simp [hi, mem_symmDiff]
  have hF : Measurable (fun P : ι → Prop => fun i =>
      (fun Q : Prop => if i ∈ D then ¬ Q else Q) (P i)) :=
    Measurable.of_eval fun i => (hflip i).comp (measurable_pi_apply i)
  rw [hcomp, ← Measure.map_map hset hF, Measure.infinitePi_map_pi _ hflip]
  congr 2
  funext i
  by_cases hi : i ∈ D
  · simp only [hi, ↓reduceIte]
    rw [map_bernoulliMeasure, not_true_eq_false, not_false_eq_true, bernoulliMeasure_swap]
  · simp only [hi, ↓reduceIte, Measure.map_id']

/-- The product law with profile `p` is the image, under flipping the coordinates in `D`, of the
product law with the profile flipped on `D`. -/
theorem prodBernoulli_eq_map_symmDiff (p : ι → unitInterval) (D : Set ι)
    [DecidablePred (· ∈ D)] :
    prodBernoulli p =
      (prodBernoulli (fun i => if i ∈ D then unitInterval.symm (p i) else p i)).map (· ∆ D) := by
  rw [prodBernoulli_map_symmDiff]
  congr 1
  funext i
  by_cases hi : i ∈ D <;> simp [hi]

/-- Flipping the coordinates in `D` turns the mixed order into inclusion: the configurations whose
flip lies in an event upper for the mixed order form an increasing event. -/
theorem isUpperSet_preimage_symmDiff {D : Set ι} {A : Set (Set ι)}
    (hA : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A) :
    IsUpperSet ((· ∆ D) ⁻¹' A) := by
  intro ω ω' h hω
  refine hA _ _ (fun i hi => ?_) (fun i hi => ?_) hω
  · simp only [mem_sdiff, mem_symmDiff] at hi ⊢
    tauto
  · simp only [mem_inter_iff, mem_symmDiff] at hi ⊢
    have : i ∈ ω → i ∈ ω' := fun h' => h h'
    tauto

/-! ### Harris for a mixed order -/

/-- **Harris for a mixed order.** Order configurations by `ω ≤ ω'` when `ω \ D ⊆ ω' \ D` and
`ω' ∩ D ⊆ ω ∩ D`. Two measurable events closed upwards for this order (increasing off `D`,
decreasing on `D`) are positively correlated under every product Bernoulli law. -/
theorem prodBernoulli_harris_of_mixed (p : ι → unitInterval) (D : Set ι) {A B : Set (Set ι)}
    (hA : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A)
    (hB : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ B → ω' ∈ B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    prodBernoulli p A * prodBernoulli p B ≤ prodBernoulli p (A ∩ B) := by
  classical
  have hsd : Measurable (fun ω : Set ι => ω ∆ D) := measurable_id.symmDiff measurable_const
  rw [prodBernoulli_eq_map_symmDiff p D, Measure.map_apply hsd hAm, Measure.map_apply hsd hBm,
    Measure.map_apply hsd (hAm.inter hBm), preimage_inter]
  exact prodBernoulli_harris _ (isUpperSet_preimage_symmDiff hA) (isUpperSet_preimage_symmDiff hB)
    (hsd hAm) (hsd hBm)

/-- The events upper for a mixed order are closed under intersection. -/
theorem mixed_inter {D : Set ι} {A B : Set (Set ι)}
    (hA : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A)
    (hB : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ B → ω' ∈ B) :
    ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A ∩ B → ω' ∈ A ∩ B :=
  fun ω ω' h₁ h₂ hω => ⟨hA ω ω' h₁ h₂ hω.1, hB ω ω' h₁ h₂ hω.2⟩

/-- **Harris for a mixed order, finitely many events.** The product of the probabilities of
finitely many measurable events upper for one mixed order is at most the probability of their
intersection. -/
theorem prodBernoulli_prod_le_biInter_of_mixed (p : ι → unitInterval) (D : Set ι) {κ : Type*}
    (s : Finset κ) {A : κ → Set (Set ι)}
    (hA : ∀ k ∈ s, ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A k → ω' ∈ A k)
    (hAm : ∀ k ∈ s, MeasurableSet (A k)) :
    ∏ k ∈ s, prodBernoulli p (A k) ≤ prodBernoulli p (⋂ k ∈ s, A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have hA' : ∀ k ∈ s, ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A k → ω' ∈ A k :=
      fun k hk => hA k (Finset.mem_insert_of_mem hk)
    have hAm' : ∀ k ∈ s, MeasurableSet (A k) := fun k hk => hAm k (Finset.mem_insert_of_mem hk)
    have hI : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ ⋂ k ∈ s, A k →
        ω' ∈ ⋂ k ∈ s, A k := by
      intro ω ω' h₁ h₂ hω
      simp only [mem_iInter] at hω ⊢
      exact fun k hk => hA' k hk ω ω' h₁ h₂ (hω k hk)
    rw [Finset.prod_insert has, Finset.set_biInter_insert]
    calc prodBernoulli p (A a) * ∏ k ∈ s, prodBernoulli p (A k)
        ≤ prodBernoulli p (A a) * prodBernoulli p (⋂ k ∈ s, A k) := by gcongr; exact ih hA' hAm'
      _ ≤ prodBernoulli p (A a ∩ ⋂ k ∈ s, A k) :=
        prodBernoulli_harris_of_mixed p D (hA a (Finset.mem_insert_self a s)) hI
          (hAm a (Finset.mem_insert_self a s)) (Finset.measurableSet_biInter s hAm')

/-! ### The conditional form -/

/-- **Harris for a mixed order, conditional form.** Let `T` and `D` be sets of coordinates. Let
`A` be a measurable event that is upper for the mixed order of `D` among configurations agreeing
off `T` (once the coordinates outside `T` are fixed, it is increasing in the coordinates of
`T \ D` and decreasing in those of `T ∩ D`), and `B` a measurable event upper for the mixed order
of `D` and determined by the coordinates in `T`. Then `P(A) P(B) ≤ P(A ∩ B)`. The proof conditions
on the coordinates outside `T` (splicing) and applies `prodBernoulli_harris_of_mixed` to the
sections. -/
theorem prodBernoulli_mul_le_inter_of_mixed_of_determined (p : ι → unitInterval)
    {T D : Set ι} {A B : Set (Set ι)}
    (hA : ∀ ω ω', ω \ T = ω' \ T → ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A)
    (hB : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ B → ω' ∈ B)
    (hBT : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ B ↔ ω' ∈ B))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    prodBernoulli p A * prodBernoulli p B ≤ prodBernoulli p (A ∩ B) := by
  set μ := prodBernoulli p
  set S : Set ι := Tᶜ with hS
  set sec : Set ι → Set (Set ι) → Set (Set ι) :=
    fun x E => (fun y => (x ∩ S) ∪ (y \ S)) ⁻¹' E with hsec
  -- the sections of `B` are `B`
  have hBs : ∀ x, sec x B = B := splice_preimage_eq_of_disjoint disjoint_compl_left hBT
  -- the sections of `A` are upper for the mixed order
  have hAs : ∀ x, ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ sec x A → ω' ∈ sec x A := by
    intro x ω ω' h₁ h₂ hω
    refine hA _ _ ?_ (fun i hi => ?_) (fun i hi => ?_) hω
    · ext i
      simp only [hS, mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    · simp only [hS, mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff] at hi ⊢
      have := @h₁ i
      simp only [mem_sdiff] at this
      tauto
    · simp only [hS, mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff] at hi ⊢
      have := @h₂ i
      simp only [mem_inter_iff] at this
      tauto
  have hpt : ∀ x, μ (sec x A) * μ B ≤ μ (sec x (A ∩ B)) := by
    intro x
    refine (prodBernoulli_harris_of_mixed p D (hAs x) hB
      (measurable_splice_right S x hAm) hBm).trans_eq ?_
    rw [show sec x (A ∩ B) = sec x A ∩ sec x B from rfl, hBs x]
  have hfin : μ B ≠ ∞ := measure_ne_top _ _
  rw [prodBernoulli_eq_lintegral_splice p S hAm,
    prodBernoulli_eq_lintegral_splice p S (hAm.inter hBm), ← lintegral_mul_const' _ _ hfin]
  exact lintegral_mono hpt

end PercLib.Probability
