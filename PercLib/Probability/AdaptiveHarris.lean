/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the canonical finite Bernoulli law. Mathematical reference: the adaptive Harris
inequality for predictable sharing in decision trees, N. Gladkov, "Percolation Inequalities and
Decision Trees", arXiv:2408.08457 (2024). The decision tree is encoded as in
`PercLib.Probability.PredictableSwap`; no new definition is introduced.
-/
module

public import PercLib.Probability.Coordinate
public import PercLib.Probability.PredictableSwap
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Adaptive Harris inequality

Let `X, Y` be independent with law `μ = prodBernoulli p` on a finite set `E`, read by a
decision tree of depth `n` which, before revealing the pair `(X e, Y e)` of a freshly queried
coordinate, decides whether `e` is shared. With `S` the shared set, the hybrid configuration is
`H = X ∩ S ∪ Y \ S`. If `A, B` are both increasing or both decreasing, then
`μ(A) μ(B) ≤ P(X ∈ A, H ∈ B)`.

The proof removes the sharing decisions from the deepest step upwards. On a fixed history of
the steps before step `k`, the coordinate queried at step `k` is fresh whenever it is shared,
so the fibre does not depend on it, and unsharing it can only lower the probability: this is
a two-point covariance inequality in that coordinate.

## Main results

* `measure_inter_add_measure_inter_le`: for `P₀ ⊆ P₁` and `Q₀ ⊆ Q₁`,
  `μ(P₀ ∩ Q₁) + μ(P₁ ∩ Q₀) ≤ μ(P₀ ∩ Q₀) + μ(P₁ ∩ Q₁)`.
* `prodBernoulli_prod_hybrid_le_insert`: sharing one more coordinate `e`, on an event that
  does not depend on `e`, does not decrease `P(X ∈ A, H ∈ B)`.
* `answers_eq_of_agree`: the event that the first `k` revealed pairs equal a given history
  depends only on the coordinates that history queries.
* `prodBernoulli_prod_hybrid_le_of_step`: the same monotonicity for the sharing decision of
  one step of a predictable sharing tree.
* `prodBernoulli_mul_le_prod_hybrid`: the adaptive Harris inequality.
-/

@[expose] public section

open MeasureTheory Set unitInterval
open scoped ENNReal NNReal

/-- **Two-by-two lattice inequality.** For `P₀ ⊆ P₁` and `Q₀ ⊆ Q₁`,
`μ(P₀ ∩ Q₁) + μ(P₁ ∩ Q₀) ≤ μ(P₀ ∩ Q₀) + μ(P₁ ∩ Q₁)`. -/
theorem MeasureTheory.measure_inter_add_measure_inter_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {P₀ P₁ Q₀ Q₁ : Set α} (hP : P₀ ⊆ P₁) (hQ : Q₀ ⊆ Q₁)
    (hQ₀ : MeasurableSet Q₀) :
    μ (P₀ ∩ Q₁) + μ (P₁ ∩ Q₀) ≤ μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₁) := by
  have key : ∀ P, μ (P ∩ Q₁) = μ (P ∩ Q₀) + μ ((P ∩ Q₁) \ Q₀) := fun P => by
    rw [← measure_inter_add_sdiff (P ∩ Q₁) hQ₀, inter_assoc, inter_eq_right.2 hQ]
  have hle : μ ((P₀ ∩ Q₁) \ Q₀) ≤ μ ((P₁ ∩ Q₁) \ Q₀) :=
    measure_mono fun x hx => ⟨⟨hP hx.1.1, hx.1.2⟩, hx.2⟩
  calc μ (P₀ ∩ Q₁) + μ (P₁ ∩ Q₀) = μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₀) + μ ((P₀ ∩ Q₁) \ Q₀) := by
        rw [key P₀]; ring
    _ ≤ μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₀) + μ ((P₁ ∩ Q₁) \ Q₀) := by gcongr
    _ = μ (P₀ ∩ Q₀) + μ (P₁ ∩ Q₁) := by rw [key P₁]; ring

namespace PercLib.Probability

variable {E : Type*}

/-- **Sharing one more coordinate.** Let `C` be an event of the pair `(X, Y)` that does not
depend on the two bits at `e`, and let `e ∉ S₀`. If `A, B` are both increasing or both
decreasing, adding `e` to the shared set does not decrease `P(C, X ∈ A, X ∩ S ∪ Y \ S ∈ B)`. -/
theorem prodBernoulli_prod_hybrid_le_insert [Fintype E] (p : E → unitInterval) (e : E)
    {C : Set (Set E × Set E)}
    (hC : ∀ x y x' y' : Set E, (∀ a, a ≠ e → (a ∈ x ↔ a ∈ x') ∧ (a ∈ y ↔ a ∈ y')) →
      (x, y) ∈ C → (x', y') ∈ C)
    {S₀ : Set E} (he : e ∉ S₀) {A B : Set (Set E)}
    (hAB : (IsUpperSet A ∧ IsUpperSet B) ∨ (IsLowerSet A ∧ IsLowerSet B)) :
    (prodBernoulli p).prod (prodBernoulli p)
        (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∈ B}) ≤
      (prodBernoulli p).prod (prodBernoulli p)
        (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ insert e S₀ ∪ ω.2 \ insert e S₀ ∈ B}) := by
  classical
  set μ := prodBernoulli p with hμdef
  set ν := μ.prod μ with hνdef
  set f : Bool → Set E → Set E := fun b x => if b then insert e x else x \ {e} with hfdef
  set w : Bool → ℝ≥0 := fun b =>
    if b then unitInterval.toNNReal (p e) else unitInterval.toNNReal (σ (p e)) with hwdef
  have hfm : ∀ b, Measurable (f b) := fun b => measurable_of_countable _
  have hμ : μ = w true • μ.map (f true) + w false • μ.map (f false) := by
    have h := prodBernoulli_eq_smul_add_smul p e
    rw [← prodBernoulli_map_insert, ← prodBernoulli_map_diff_singleton] at h
    exact h
  have hdec : ∀ T : Set (Set E × Set E), ν T = ∑ i : Bool, ∑ j : Bool,
      (w i : ℝ≥0∞) * w j * ν (Prod.map (f i) (f j) ⁻¹' T) := by
    intro T
    have hmeas : MeasurableSet T := (Set.to_countable T).measurableSet
    rw [hνdef]
    conv_lhs => rw [hμ]
    simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
      Measure.prod_smul_right, Measure.map_prod_map _ _ (hfm _) (hfm _), Measure.add_apply,
      Measure.smul_apply, Measure.map_apply (measurable_of_countable _) hmeas, Fintype.sum_bool,
      ENNReal.smul_def, smul_eq_mul]
    ring
  have hagree : ∀ i j (ω : Set E × Set E) a, a ≠ e →
      (a ∈ ω.1 ↔ a ∈ f i ω.1) ∧ (a ∈ ω.2 ↔ a ∈ f j ω.2) := by
    intro i j ω a ha
    cases i <;> cases j <;> simp [f, ha]
  have hc : ∀ i j (ω : Set E × Set E), Prod.map (f i) (f j) ω ∈ C ↔ ω ∈ C := by
    intro i j ω
    constructor
    · exact hC _ _ ω.1 ω.2 fun a ha =>
        ⟨(hagree i j ω a ha).1.symm, (hagree i j ω a ha).2.symm⟩
    · exact hC ω.1 ω.2 _ _ (hagree i j ω)
  have hH0 : ∀ i j (x y : Set E), f i x ∩ S₀ ∪ f j y \ S₀ = f j (x ∩ S₀ ∪ y \ S₀) := by
    intro i j x y
    ext a
    by_cases ha : a = e
    · subst ha
      cases i <;> cases j <;> simp [f, he]
    · cases i <;> cases j <;> simp [f, ha]
  have hH1 : ∀ i j (x y : Set E),
      f i x ∩ insert e S₀ ∪ f j y \ insert e S₀ = f i (x ∩ S₀ ∪ y \ S₀) := by
    intro i j x y
    ext a
    by_cases ha : a = e
    · subst ha
      cases i <;> cases j <;> simp [f, he]
    · cases i <;> cases j <;> simp [f, ha]
  set P : Bool → Set (Set E × Set E) := fun i => C ∩ {ω | f i ω.1 ∈ A} with hPdef
  set Q : Bool → Set (Set E × Set E) := fun j => {ω | f j (ω.1 ∩ S₀ ∪ ω.2 \ S₀) ∈ B}
    with hQdef
  have hpre0 : ∀ i j, Prod.map (f i) (f j) ⁻¹' (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ S₀ ∪ ω.2 \ S₀ ∈ B}) =
      P i ∩ Q j := by
    intro i j
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hc, Prod.map_fst, Prod.map_snd, hH0,
      P, Q]
    tauto
  have hpre1 : ∀ i j, Prod.map (f i) (f j) ⁻¹'
      (C ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ insert e S₀ ∪ ω.2 \ insert e S₀ ∈ B}) = P i ∩ Q i := by
    intro i j
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hc, Prod.map_fst, Prod.map_snd, hH1,
      P, Q]
    tauto
  have hfsub : ∀ x, f false x ⊆ f true x := fun x => by
    simp only [f]
    exact sdiff_subset.trans (subset_insert _ _)
  have hmeasQ : ∀ j, MeasurableSet (Q j) := fun j => (Set.to_countable _).measurableSet
  have key : ν (P true ∩ Q false) + ν (P false ∩ Q true) ≤
      ν (P true ∩ Q true) + ν (P false ∩ Q false) := by
    rcases hAB with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have h := measure_inter_add_measure_inter_le ν (P₀ := P false) (P₁ := P true)
        (Q₀ := Q false) (Q₁ := Q true) (fun ω hω => ⟨hω.1, hA (hfsub _) hω.2⟩)
        (fun ω hω => hB (hfsub _) hω) (hmeasQ _)
      rw [add_comm, add_comm (ν (P true ∩ Q true))]
      exact h
    · exact measure_inter_add_measure_inter_le ν (fun ω hω => ⟨hω.1, hA (hfsub _) hω.2⟩)
        (fun ω hω => hB (hfsub _) hω) (hmeasQ _)
  rw [hdec, hdec]
  simp only [hpre0, hpre1, Fintype.sum_bool]
  calc (w true : ℝ≥0∞) * w true * ν (P true ∩ Q true) + w true * w false * ν (P true ∩ Q false) +
        (w false * w true * ν (P false ∩ Q true) + w false * w false * ν (P false ∩ Q false))
      = w true * w true * ν (P true ∩ Q true) + w false * w false * ν (P false ∩ Q false) +
          w true * w false * (ν (P true ∩ Q false) + ν (P false ∩ Q true)) := by ring
    _ ≤ w true * w true * ν (P true ∩ Q true) + w false * w false * ν (P false ∩ Q false) +
          w true * w false * (ν (P true ∩ Q true) + ν (P false ∩ Q false)) := by gcongr
    _ = _ := by ring

section Tree

variable {n : ℕ} (next : (k : Fin n) → (Fin k.val → Bool × Bool) → E)
  (share : (k : Fin n) → (Fin k.val → Bool × Bool) → Bool)
  (answers : Set E × Set E → Fin n → Bool × Bool)

/-- **Histories depend only on their queried coordinates.** If the first `k` revealed pairs on
`ω` form the history `h`, and `ω'` agrees with `ω` on every coordinate that `h` queries, then the
first `k` revealed pairs on `ω'` also form `h`. -/
theorem answers_eq_of_agree
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (k : Fin n) (h : Fin k.val → Bool × Bool) {ω ω' : Set E × Set E}
    (hω : (fun i : Fin k.val => answers ω ⟨i.val, i.isLt.trans k.isLt⟩) = h)
    (hagree : ∀ (j : Fin n) (hj : j < k),
      (next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω.1 ↔
        next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω'.1) ∧
      (next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω.2 ↔
        next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ∈ ω'.2)) :
    (fun i : Fin k.val => answers ω' ⟨i.val, i.isLt.trans k.isLt⟩) = h := by
  suffices H : ∀ m (hm : m < k.val), answers ω' ⟨m, hm.trans k.isLt⟩ = h ⟨m, hm⟩ by
    funext i
    exact H i.val i.isLt
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  set j : Fin n := ⟨m, hm.trans k.isLt⟩ with hjdef
  have hj : j < k := hm
  have hω' : (fun i : Fin j.val => answers ω' ⟨i.val, i.isLt.trans j.isLt⟩) =
      fun i => h ⟨i.val, i.isLt.trans hj⟩ := funext fun i => ih i.val i.isLt _
  have hωj : (fun i : Fin j.val => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) =
      fun i => h ⟨i.val, i.isLt.trans hj⟩ :=
    funext fun i => congrFun hω ⟨i.val, i.isLt.trans hj⟩
  have hhm : answers ω j = h ⟨m, hm⟩ := congrFun hω ⟨m, hm⟩
  rw [← hhm]
  obtain ⟨ha1, ha2⟩ := hagree j hj
  refine Prod.ext (Bool.eq_iff_iff.2 ?_) (Bool.eq_iff_iff.2 ?_)
  · rw [(hrun ω' j).1, (hrun ω j).1, hω', hωj]
    exact ha1.symm
  · rw [(hrun ω' j).2, (hrun ω j).2, hω', hωj]
    exact ha2.symm

/-- **Unsharing one step.** Let `S₀` and `S₁` be the sets shared by a predictable sharing tree
strictly before step `k` and up to step `k`. If `A, B` are both increasing or both decreasing,
then `P(X ∈ A, X ∩ S₀ ∪ Y \ S₀ ∈ B) ≤ P(X ∈ A, X ∩ S₁ ∪ Y \ S₁ ∈ B)`. -/
theorem prodBernoulli_prod_hybrid_le_of_step [Fintype E] (p : E → unitInterval)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (k : Fin n) (S₀ S₁ : Set E × Set E → Set E)
    (hS₀ : ∀ ω e, e ∈ S₀ ω ↔ ∃ j : Fin n, j < k ∧
      share j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = true ∧
        next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e)
    (hS₁ : ∀ ω e, e ∈ S₁ ω ↔ ∃ j : Fin n, j ≤ k ∧
      share j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = true ∧
        next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e)
    {A B : Set (Set E)}
    (hAB : (IsUpperSet A ∧ IsUpperSet B) ∨ (IsLowerSet A ∧ IsLowerSet B)) :
    (prodBernoulli p).prod (prodBernoulli p) {ω | ω.1 ∈ A ∧ ω.1 ∩ S₀ ω ∪ ω.2 \ S₀ ω ∈ B} ≤
      (prodBernoulli p).prod (prodBernoulli p)
        {ω | ω.1 ∈ A ∧ ω.1 ∩ S₁ ω ∪ ω.2 \ S₁ ω ∈ B} := by
  classical
  set ν := (prodBernoulli p).prod (prodBernoulli p) with hν
  set g : Set E × Set E → (Fin k.val → Bool × Bool) :=
    fun ω i => answers ω ⟨i.val, i.isLt.trans k.isLt⟩ with hgdef
  have hsplit : ∀ T : Set (Set E × Set E), ν T = ∑ h, ν (T ∩ g ⁻¹' {h}) := by
    intro T
    have := sum_measure_preimage_singleton (μ := ν.restrict T) Finset.univ (f := g)
      (fun _ _ => (Set.to_countable _).measurableSet)
    simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at this
    rw [← this]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Measure.restrict_apply (Set.to_countable _).measurableSet, inter_comm]
  rw [hsplit, hsplit]
  refine Finset.sum_le_sum fun h _ => ?_
  have hhist : ∀ ω ∈ g ⁻¹' {h}, ∀ (j : Fin n) (hj : j < k),
      (fun i : Fin j.val => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) =
        fun i => h ⟨i.val, i.isLt.trans hj⟩ := by
    intro ω hω j hj
    funext i
    exact congrFun hω ⟨i.val, i.isLt.trans hj⟩
  set S₀' : Set E := {e | ∃ (j : Fin n) (hj : j < k),
    share j (fun i => h ⟨i.val, i.isLt.trans hj⟩) = true ∧
      next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) = e} with hS₀'
  have h₀ : ∀ ω ∈ g ⁻¹' {h}, S₀ ω = S₀' := by
    intro ω hω
    ext e
    rw [hS₀]
    constructor
    · rintro ⟨j, hj, hs⟩
      rw [hhist ω hω j hj] at hs
      exact ⟨j, hj, hs⟩
    · rintro ⟨j, hj, hs⟩
      refine ⟨j, hj, ?_⟩
      rw [hhist ω hω j hj]
      exact hs
  have h₁ : ∀ ω ∈ g ⁻¹' {h}, S₁ ω = S₀' ∪ {e | share k h = true ∧ next k h = e} := by
    intro ω hω
    have hk : (fun i : Fin k.val => answers ω ⟨i.val, i.isLt.trans k.isLt⟩) = h := hω
    ext e
    rw [hS₁, mem_union, ← h₀ ω hω, hS₀, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hs⟩
      rcases hj.lt_or_eq with hj | rfl
      · exact Or.inl ⟨j, hj, hs⟩
      · rw [hk] at hs
        exact Or.inr hs
    · rintro (⟨j, hj, hs⟩ | hs)
      · exact ⟨j, hj.le, hs⟩
      · exact ⟨k, le_rfl, by rw [hk]; exact hs⟩
  have hT : ∀ (S : Set E × Set E → Set E) (S' : Set E), (∀ ω ∈ g ⁻¹' {h}, S ω = S') →
      {ω | ω.1 ∈ A ∧ ω.1 ∩ S ω ∪ ω.2 \ S ω ∈ B} ∩ g ⁻¹' {h} =
        g ⁻¹' {h} ∩ {ω | ω.1 ∈ A ∧ ω.1 ∩ S' ∪ ω.2 \ S' ∈ B} := by
    intro S S' hS
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      rw [mem_ofPred_eq, hS ω h2] at h1
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      rw [mem_ofPred_eq, ← hS ω h2] at h1
      exact ⟨h1, h2⟩
  rw [hT S₀ S₀' h₀, hT S₁ _ h₁]
  cases hsk : share k h
  · simp
  · simp only [true_and, ofPred_eq_eq_singleton', union_singleton]
    rcases (g ⁻¹' {h}).eq_empty_or_nonempty with hempty | ⟨ω₀, hω₀⟩
    · simp [hempty]
    have hk0 : (fun i : Fin k.val => answers ω₀ ⟨i.val, i.isLt.trans k.isLt⟩) = h := hω₀
    refine prodBernoulli_prod_hybrid_le_insert p (next k h) ?_ ?_ hAB
    · intro x y x' y' hxy hmem
      refine answers_eq_of_agree next answers hrun k h hmem fun j hj => ?_
      have hne : next j (fun i => h ⟨i.val, i.isLt.trans hj⟩) ≠ next k h := by
        have := hfresh (answers ω₀) k (by rw [hk0]; exact hsk) j hj
        rwa [hk0, hhist ω₀ hω₀ j hj] at this
      exact hxy _ hne
    · rintro ⟨j, hj, -, hn⟩
      have := hfresh (answers ω₀) k (by rw [hk0]; exact hsk) j hj
      rw [hk0, hhist ω₀ hω₀ j hj] at this
      exact this hn

/-- **Adaptive Harris inequality.** Let `E` be finite, `μ = prodBernoulli p`, and let
`ω = (X, Y)` have law `μ ⊗ μ`, read by a predictable sharing tree (`next`, `share`, `answers`)
with shared set `S` as in `prodBernoulli_prod_map_predictableSwap`. If `A, B` are both
increasing or both decreasing, then `μ(A) μ(B) ≤ P(X ∈ A, X ∩ S ∪ Y \ S ∈ B)`. -/
theorem prodBernoulli_mul_le_prod_hybrid [Fintype E] (p : E → unitInterval)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e)
    {A B : Set (Set E)}
    (hAB : (IsUpperSet A ∧ IsUpperSet B) ∨ (IsLowerSet A ∧ IsLowerSet B)) :
    prodBernoulli p A * prodBernoulli p B ≤
      (prodBernoulli p).prod (prodBernoulli p) {ω | ω.1 ∈ A ∧ ω.1 ∩ S ω ∪ ω.2 \ S ω ∈ B} := by
  classical
  set T : ℕ → Set E × Set E → Set E := fun m ω => {e | ∃ j : Fin n, j.val < m ∧
      share j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = true ∧
        next j (fun i => answers ω ⟨i.val, i.isLt.trans j.isLt⟩) = e} with hTdef
  have hT0 : ∀ ω, T 0 ω = ∅ := fun ω => by
    ext e
    simp [T]
  have hTn : ∀ ω, T n ω = S ω := fun ω => by
    ext e
    rw [hS]
    simp only [T, mem_ofPred_eq]
    exact exists_congr fun j => by simp [j.isLt]
  have hmono : ∀ m ≤ n, (prodBernoulli p).prod (prodBernoulli p)
      {ω | ω.1 ∈ A ∧ ω.1 ∩ T 0 ω ∪ ω.2 \ T 0 ω ∈ B} ≤
        (prodBernoulli p).prod (prodBernoulli p)
          {ω | ω.1 ∈ A ∧ ω.1 ∩ T m ω ∪ ω.2 \ T m ω ∈ B} := by
    intro m
    induction m with
    | zero => exact fun _ => le_rfl
    | succ m ih =>
      intro hm
      refine (ih (by omega)).trans ?_
      exact prodBernoulli_prod_hybrid_le_of_step next share answers p hrun hfresh ⟨m, hm⟩
        (T m) (T (m + 1)) (fun ω e => Iff.rfl)
        (fun ω e => exists_congr fun j => and_congr_left'
          (by rw [Fin.le_iff_val_le_val]; exact Nat.lt_succ_iff))
        hAB
  have h := hmono n le_rfl
  simp only [hT0, hTn, inter_empty, empty_union, sdiff_empty] at h
  refine le_of_eq_of_le ?_ h
  rw [← Measure.prod_prod]
  rfl

end Tree

end PercLib.Probability
