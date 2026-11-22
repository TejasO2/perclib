/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied: everything is derived from
Harris's inequality for decreasing events, `PercLib.Probability.prodBernoulli_harris_of_isLowerSet`.
Mathematical reference: V. Tassion, Crossing probabilities for Voronoi percolation, Ann. Probab.
44 (2016), arXiv:1410.6773v2, Proposition 4.1 (the square-root trick), p. 11.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PercLib.Probability.HarrisDecreasing

/-!
# The square-root trick

If the union of finitely many increasing events `A_1, …, A_k` is likely, one of them is
likely:
`max_i P(A_i) ≥ 1 - (1 - P(A_1 ∪ ⋯ ∪ A_k))^(1/k)`.
For two events this reads `max (P(A), P(B)) ≥ 1 - √(1 - P(A ∪ B))`, hence the name. When the
events have equal probabilities, for instance because a symmetry of the law exchanges them,
each of them has probability at least `1 - (1 - P(⋃ A_i))^(1/k)`.

The proof: the complements `A_iᶜ` are decreasing, so Harris's inequality for decreasing events
gives `1 - P(⋃ A_i) = P(⋂ A_iᶜ) ≥ ∏ P(A_iᶜ) = ∏ (1 - P(A_i)) ≥ (1 - max_i P(A_i))^k`, and taking
`k`-th roots gives the bound.

Everything holds for the configuration law `prodBernoulli q` on an arbitrary index type `ι`,
with an arbitrary profile `q`, for events indexed by a finite set `s` of an arbitrary type; the
number of events is `k = s.card` and the `k`-th root is `x ^ (s.card : ℝ)⁻¹`. Nothing here is
planar. This file adds no definition.

## Main results

* `prodBernoulli_prod_le_biInter_of_isLowerSet`: Harris for finitely many decreasing events, the
  decreasing companion of `prodBernoulli_prod_le_biInter`; real form
  `prodBernoulli_real_prod_le_biInter_of_isLowerSet`.
* `prodBernoulli_prod_one_sub_le_one_sub_biUnion`: `∏ (1 - P(A_i)) ≤ 1 - P(⋃ A_i)` for increasing
  events; real form `prodBernoulli_real_prod_one_sub_le_one_sub_biUnion`.
* `Finset.one_sub_rpow_le_sup'_of_prod_one_sub_le`: the real-number step, for any reals
  `x_i ≤ 1` and `u` with `∏ (1 - x_i) ≤ 1 - u`.
* `prodBernoulli_one_sub_rpow_le_sup'`: **the square-root trick**, the maximum written
  `s.sup'`; `exists_one_sub_rpow_le_prodBernoulli_real` is the existential form.
* Equal probabilities `p`: `prodBernoulli_one_sub_pow_le_of_forall_eq`
  (`(1 - p)^k ≤ 1 - P(⋃ A_i)`, no root and no nonemptiness) and
  `prodBernoulli_one_sub_rpow_le_of_forall_eq` (`1 - (1 - P(⋃ A_i))^(1/k) ≤ p`).
* Two events: `prodBernoulli_one_sub_mul_one_sub_le_one_sub_union`
  (`(1 - P(A)) (1 - P(B)) ≤ 1 - P(A ∪ B)`), `prodBernoulli_one_sub_sqrt_le_max` and, for equal
  probabilities, `prodBernoulli_one_sub_sqrt_le_of_eq`.
-/

@[expose] public section

open MeasureTheory Set

/-! ### The real-number step -/

namespace Finset

/-- If `∏ (1 - x a) ≤ 1 - u` over a nonempty finite set `s`, with every `x a ≤ 1`, then the
largest `x a` is at least `1 - (1 - u)^(1/k)`, where `k = s.card`. -/
theorem one_sub_rpow_le_sup'_of_prod_one_sub_le {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {x : α → ℝ} {u : ℝ} (hx : ∀ a ∈ s, x a ≤ 1) (h : ∏ a ∈ s, (1 - x a) ≤ 1 - u) :
    1 - (1 - u) ^ (s.card : ℝ)⁻¹ ≤ s.sup' hs x := by
  have hm : 0 ≤ 1 - s.sup' hs x := sub_nonneg.2 (sup'_le hs x hx)
  have hpow : (1 - s.sup' hs x) ^ s.card ≤ 1 - u :=
    calc (1 - s.sup' hs x) ^ s.card = ∏ _a ∈ s, (1 - s.sup' hs x) := (prod_const _).symm
      _ ≤ ∏ a ∈ s, (1 - x a) :=
          prod_le_prod₀ (fun _ _ => hm) fun a ha => sub_le_sub_left (le_sup' x ha) 1
      _ ≤ 1 - u := h
  have hroot : ((1 - s.sup' hs x) ^ s.card) ^ (s.card : ℝ)⁻¹ ≤ (1 - u) ^ (s.card : ℝ)⁻¹ :=
    Real.rpow_le_rpow (pow_nonneg hm _) hpow (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [Real.pow_rpow_inv_natCast hm hs.card_pos.ne'] at hroot
  linarith

end Finset

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Harris for finitely many decreasing events -/

/-- **Harris for finitely many decreasing events.** -/
theorem prodBernoulli_prod_le_biInter_of_isLowerSet (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsLowerSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    ∏ a ∈ s, prodBernoulli q (A a) ≤ prodBernoulli q (⋂ a ∈ s, A a) := by
  classical
  revert hA hAm
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a s ha ih hA hAm
    have hs : ∀ b ∈ s, IsLowerSet (A b) := fun b hb => hA b (Finset.mem_insert_of_mem hb)
    have hsm : ∀ b ∈ s, MeasurableSet (A b) := fun b hb =>
      hAm b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert ha, Finset.set_biInter_insert]
    calc prodBernoulli q (A a) * ∏ b ∈ s, prodBernoulli q (A b)
        ≤ prodBernoulli q (A a) * prodBernoulli q (⋂ b ∈ s, A b) := by
          gcongr
          exact ih hs hsm
      _ ≤ prodBernoulli q (A a ∩ ⋂ b ∈ s, A b) :=
          prodBernoulli_harris_of_isLowerSet q (hA a (Finset.mem_insert_self a s))
            (isLowerSet_iInter₂ hs) (hAm a (Finset.mem_insert_self a s))
            (Finset.measurableSet_biInter s hsm)

/-- Real form of Harris for finitely many decreasing events. -/
theorem prodBernoulli_real_prod_le_biInter_of_isLowerSet (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsLowerSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    ∏ a ∈ s, (prodBernoulli q).real (A a) ≤ (prodBernoulli q).real (⋂ a ∈ s, A a) := by
  simp only [Measure.real, ← ENNReal.toReal_prod]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (prodBernoulli_prod_le_biInter_of_isLowerSet q s A hA hAm)

/-! ### The product bound for a union of increasing events -/

/-- For increasing events, `∏ (1 - P(A a)) ≤ 1 - P(⋃ A a)`: the complements are decreasing,
so Harris applies to them. -/
theorem prodBernoulli_prod_one_sub_le_one_sub_biUnion (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    ∏ a ∈ s, (1 - prodBernoulli q (A a)) ≤ 1 - prodBernoulli q (⋃ a ∈ s, A a) := by
  rw [← prob_compl_eq_one_sub (Finset.measurableSet_biUnion s hAm), compl_iUnion₂]
  calc ∏ a ∈ s, (1 - prodBernoulli q (A a)) = ∏ a ∈ s, prodBernoulli q (A a)ᶜ :=
        Finset.prod_congr rfl fun a ha => (prob_compl_eq_one_sub (hAm a ha)).symm
    _ ≤ prodBernoulli q (⋂ a ∈ s, (A a)ᶜ) :=
        prodBernoulli_prod_le_biInter_of_isLowerSet q s (fun a => (A a)ᶜ)
          (fun a ha => (hA a ha).compl) (fun a ha => (hAm a ha).compl)

/-- Real form of `prodBernoulli_prod_one_sub_le_one_sub_biUnion`. -/
theorem prodBernoulli_real_prod_one_sub_le_one_sub_biUnion (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    ∏ a ∈ s, (1 - (prodBernoulli q).real (A a)) ≤
      1 - (prodBernoulli q).real (⋃ a ∈ s, A a) := by
  rw [← probReal_compl_eq_one_sub (Finset.measurableSet_biUnion s hAm), compl_iUnion₂]
  calc ∏ a ∈ s, (1 - (prodBernoulli q).real (A a)) = ∏ a ∈ s, (prodBernoulli q).real (A a)ᶜ :=
        Finset.prod_congr rfl fun a ha => (probReal_compl_eq_one_sub (hAm a ha)).symm
    _ ≤ (prodBernoulli q).real (⋂ a ∈ s, (A a)ᶜ) :=
        prodBernoulli_real_prod_le_biInter_of_isLowerSet q s (fun a => (A a)ᶜ)
          (fun a ha => (hA a ha).compl) (fun a ha => (hAm a ha).compl)

/-! ### The square-root trick -/

/-- **The square-root trick.** For finitely many increasing events `A a`, `a ∈ s`, the largest
of their probabilities is at least `1 - (1 - P(⋃ A a))^(1/k)`, where `k = s.card`. -/
theorem prodBernoulli_one_sub_rpow_le_sup' (q : ι → unitInterval) {α : Type*} (s : Finset α)
    (hs : s.Nonempty) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    1 - (1 - (prodBernoulli q).real (⋃ a ∈ s, A a)) ^ (s.card : ℝ)⁻¹ ≤
      s.sup' hs fun a => (prodBernoulli q).real (A a) :=
  Finset.one_sub_rpow_le_sup'_of_prod_one_sub_le hs (fun _ _ => measureReal_le_one)
    (prodBernoulli_real_prod_one_sub_le_one_sub_biUnion q s A hA hAm)

/-- **The square-root trick**, existential form: one of finitely many increasing events `A a`,
`a ∈ s`, has probability at least `1 - (1 - P(⋃ A a))^(1/k)`, where `k = s.card`. -/
theorem exists_one_sub_rpow_le_prodBernoulli_real (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (hs : s.Nonempty) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    ∃ b ∈ s, 1 - (1 - (prodBernoulli q).real (⋃ a ∈ s, A a)) ^ (s.card : ℝ)⁻¹ ≤
      (prodBernoulli q).real (A b) :=
  (Finset.le_sup'_iff hs).1 (prodBernoulli_one_sub_rpow_le_sup' q s hs A hA hAm)

/-- **Equal probabilities**, without roots: if finitely many increasing events all have
probability `p`, then `(1 - p)^k ≤ 1 - P(⋃ A a)`, where `k = s.card`. -/
theorem prodBernoulli_one_sub_pow_le_of_forall_eq (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) {p : ℝ}
    (hp : ∀ a ∈ s, (prodBernoulli q).real (A a) = p) :
    (1 - p) ^ s.card ≤ 1 - (prodBernoulli q).real (⋃ a ∈ s, A a) :=
  calc (1 - p) ^ s.card = ∏ a ∈ s, (1 - (prodBernoulli q).real (A a)) :=
        (Finset.prod_eq_pow_card fun a ha => by rw [hp a ha]).symm
    _ ≤ _ := prodBernoulli_real_prod_one_sub_le_one_sub_biUnion q s A hA hAm

/-- **Equal probabilities**: if finitely many increasing events all have probability `p`, then
`p ≥ 1 - (1 - P(⋃ A a))^(1/k)`, where `k = s.card`. -/
theorem prodBernoulli_one_sub_rpow_le_of_forall_eq (q : ι → unitInterval) {α : Type*}
    (s : Finset α) (hs : s.Nonempty) (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) {p : ℝ}
    (hp : ∀ a ∈ s, (prodBernoulli q).real (A a) = p) :
    1 - (1 - (prodBernoulli q).real (⋃ a ∈ s, A a)) ^ (s.card : ℝ)⁻¹ ≤ p := by
  obtain ⟨b, hb, h⟩ := exists_one_sub_rpow_le_prodBernoulli_real q s hs A hA hAm
  exact h.trans_eq (hp b hb)

/-! ### Two events -/

/-- For two increasing events, `(1 - P(A)) (1 - P(B)) ≤ 1 - P(A ∪ B)`. -/
theorem prodBernoulli_one_sub_mul_one_sub_le_one_sub_union (q : ι → unitInterval)
    {A B : Set (Set ι)} (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) :
    (1 - (prodBernoulli q).real A) * (1 - (prodBernoulli q).real B) ≤
      1 - (prodBernoulli q).real (A ∪ B) := by
  rw [← probReal_compl_eq_one_sub hAm, ← probReal_compl_eq_one_sub hBm,
    ← probReal_compl_eq_one_sub (hAm.union hBm), compl_union]
  exact prodBernoulli_harris_real_of_isLowerSet q hA.compl hB.compl hAm.compl hBm.compl

/-- **The square-root trick for two events**:
`max (P(A), P(B)) ≥ 1 - √(1 - P(A ∪ B))` for increasing events `A` and `B`. -/
theorem prodBernoulli_one_sub_sqrt_le_max (q : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    1 - Real.sqrt (1 - (prodBernoulli q).real (A ∪ B)) ≤
      max ((prodBernoulli q).real A) ((prodBernoulli q).real B) := by
  have hm : 0 ≤ 1 - max ((prodBernoulli q).real A) ((prodBernoulli q).real B) :=
    sub_nonneg.2 (max_le measureReal_le_one measureReal_le_one)
  have h2 : (1 - max ((prodBernoulli q).real A) ((prodBernoulli q).real B)) ^ 2 ≤
      1 - (prodBernoulli q).real (A ∪ B) :=
    calc (1 - max ((prodBernoulli q).real A) ((prodBernoulli q).real B)) ^ 2
        = (1 - max ((prodBernoulli q).real A) ((prodBernoulli q).real B)) *
            (1 - max ((prodBernoulli q).real A) ((prodBernoulli q).real B)) := sq _
      _ ≤ (1 - (prodBernoulli q).real A) * (1 - (prodBernoulli q).real B) :=
          mul_le_mul (sub_le_sub_left (le_max_left _ _) 1)
            (sub_le_sub_left (le_max_right _ _) 1) hm (sub_nonneg.2 measureReal_le_one)
      _ ≤ 1 - (prodBernoulli q).real (A ∪ B) :=
          prodBernoulli_one_sub_mul_one_sub_le_one_sub_union q hA hB hAm hBm
  have hroot := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq hm] at hroot
  linarith

/-- **The square-root trick for two events of equal probability**: if increasing events `A`
and `B` have the same probability, then `P(A) ≥ 1 - √(1 - P(A ∪ B))`. -/
theorem prodBernoulli_one_sub_sqrt_le_of_eq (q : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAB : (prodBernoulli q).real A = (prodBernoulli q).real B) :
    1 - Real.sqrt (1 - (prodBernoulli q).real (A ∪ B)) ≤ (prodBernoulli q).real A := by
  have h := prodBernoulli_one_sub_sqrt_le_max q hA hB hAm hBm
  rwa [← hAB, max_self] at h

end PercLib.Probability
