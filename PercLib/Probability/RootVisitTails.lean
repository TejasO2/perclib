/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22: tails of the number of visits of a time-homogeneous Markov
chain on a countable state space to its starting point, relative to the mean visit count.
Standard mathematics; no upstream proof is copied and no Input is introduced.
-/
module

public import PercLib.Probability.ExponentialMoments
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Root visit counts of a Markov chain

Let `Z` be a time-homogeneous Markov chain on a countable state space `S` with transition
kernel `P`, started at `o`, given through its finite-dimensional distributions
`μ (Z 0 = x 0, …, Z n = x n) = 1_{x 0 = o} ∏ P (x i) {x (i + 1)}`. Write
`ℓ_n = ∑_{k ≤ n} 1_{Z k = o}` for the number of visits to `o` by time `n` (time zero included)
and `U_n = E ℓ_n`. No recurrence or reversibility is assumed.

## Main results

* `measure_window`: the law of a time window `Z r, …, Z (r + N)`.
* `lintegral_ite_shift`: the Markov property at a deterministic time at which the chain is at
  `o`.
* `lintegral_visitCount_pow_le`: `E ℓ_n^j ≤ j! U_n^j`.
* `lintegral_exp_visitCount_le`: `E exp (θ ℓ_n / U_n) ≤ (1 - θ)⁻¹` for `0 ≤ θ < 1`.
* `measure_visitCount_le_mul_le`: `P(ℓ_n ≤ m) U_n ≤ m`.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Nat

namespace PercLib.Probability

section Combinatorics

/-- `(y + d)^(j+1) ≤ (j+1) d (y+d)^j + y^(j+1)` in `ℕ`. -/
theorem add_pow_succ_le (y d : ℕ) : ∀ j : ℕ,
    (y + d) ^ (j + 1) ≤ (j + 1) * d * (y + d) ^ j + y ^ (j + 1)
  | 0 => by simp [Nat.add_comm]
  | j + 1 => by
    have ih := add_pow_succ_le y d j
    calc (y + d) ^ (j + 1 + 1) = (y + d) ^ (j + 1) * (y + d) := pow_succ _ _
      _ ≤ ((j + 1) * d * (y + d) ^ j + y ^ (j + 1)) * (y + d) := Nat.mul_le_mul_right _ ih
      _ = (j + 1) * d * (y + d) ^ (j + 1) + y ^ (j + 1) * d + y ^ (j + 1 + 1) := by ring
      _ ≤ (j + 1) * d * (y + d) ^ (j + 1) + (y + d) ^ (j + 1) * d + y ^ (j + 1 + 1) := by
          gcongr; exact Nat.le_add_right _ _
      _ = (j + 1 + 1) * d * (y + d) ^ (j + 1) + y ^ (j + 1 + 1) := by ring

/-- Suffix expansion of a power of a sum:
`(∑_{k<N} v k)^(j+1) ≤ (j+1) ∑_{t<N} v t (∑_{k<N-t} v (t+k))^j`. -/
theorem sum_range_pow_succ_le (j : ℕ) : ∀ (N : ℕ) (v : ℕ → ℕ),
    (∑ k ∈ range N, v k) ^ (j + 1) ≤
      (j + 1) * ∑ t ∈ range N, v t * (∑ k ∈ range (N - t), v (t + k)) ^ j
  | 0, v => by simp
  | N + 1, v => by
    have ih := sum_range_pow_succ_le j N (fun k => v (k + 1))
    have ha := add_pow_succ_le (∑ k ∈ range N, v (k + 1)) (v 0) j
    rw [← sum_range_succ' v N] at ha
    conv_rhs => rw [sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, zero_add]
    have e : ∀ t k : ℕ, t + k + 1 = t + 1 + k := fun t k => by omega
    simp only [e] at ih
    refine ha.trans ((Nat.add_le_add_left ih _).trans_eq ?_)
    ring

/-- At most `m` times `t ≤ n` have `p t` and at most `m` times `i ≤ n` with `p (t + i)`. -/
theorem card_filter_window_le (p : ℕ → Prop) [DecidablePred p] (n m : ℕ) :
    ((range (n + 1)).filter (fun t => p t ∧
      ((range (n + 1)).filter (fun i => p (t + i))).card ≤ m)).card ≤ m := by
  set T := (range (n + 1)).filter (fun t => p t ∧
      ((range (n + 1)).filter (fun i => p (t + i))).card ≤ m)
  rcases T.eq_empty_or_nonempty with h | h
  · simp [h]
  have ht0 := T.min'_mem h
  set t0 := T.min' h
  have hsub : T ⊆ ((range (n + 1)).filter (fun i => p (t0 + i))).image (t0 + ·) := by
    intro t ht
    have hle : t0 ≤ t := T.min'_le t ht
    simp only [T, mem_filter, mem_range] at ht
    simp only [mem_image, mem_filter, mem_range]
    exact ⟨t - t0, ⟨by omega, by rw [Nat.add_sub_cancel' hle]; exact ht.2.1⟩, by omega⟩
  calc T.card ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ ≤ m := by simp only [T, mem_filter] at ht0; exact ht0.2.2

end Combinatorics

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Countable S] [DecidableEq S] {μ : Measure Ω} {P : Kernel S S} {Z : ℕ → Ω → S} {o : S}

theorem lintegral_comp_eq_tsum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] {ν : Measure α} {Φ : α → β} (hΦ : Measurable Φ)
    (g : β → ℝ≥0∞) : ∫⁻ a, g (Φ a) ∂ν = ∑' y, g y * ν (Φ ⁻¹' {y}) := by
  rw [← lintegral_map (measurable_of_countable g) hΦ, lintegral_countable']
  simp_rw [Measure.map_apply hΦ (measurableSet_singleton _)]

omit [DecidableEq S] in
theorem measurableSet_forall_eq (hm : ∀ k, Measurable (Z k)) {ι : Type*} [Countable ι]
    (f : ι → ℕ) (y : ι → S) : MeasurableSet {ω | ∀ i, Z (f i) ω = y i} := by
  simp_rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => hm _ (measurableSet_singleton _)

omit [DecidableEq S] in
theorem measure_window_eq_tsum (hm : ∀ k, Measurable (Z k)) (r N : ℕ) (y : Fin (N + 1) → S) :
    μ {ω | ∀ i : Fin (N + 1), Z (r + 1 + i) ω = y i} =
      ∑' a, μ {ω | ∀ i : Fin (N + 2), Z (r + i) ω = (Fin.cons a y : Fin (N + 2) → S) i} := by
  rw [← measure_iUnion]
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨Z r ω, fun i => ?_⟩
      induction i using Fin.cases with
      | zero => simp
      | succ i =>
        simp only [Fin.cons_succ, Fin.val_succ]
        rw [← h i]; congr 1; omega
    · rintro ⟨a, h⟩ i
      have := h i.succ
      simp only [Fin.cons_succ, Fin.val_succ] at this
      rw [← this]; congr 1; omega
  · intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    apply hab
    have e1 := h1 0
    have e2 := h2 0
    simp only [Fin.cons_zero, Fin.val_zero, add_zero] at e1 e2
    rw [← e1, ← e2]
  · intro a
    exact measurableSet_forall_eq hm (fun i : Fin (N + 2) => r + i) _

/-- The law of a window `Z r, …, Z (r + N)`. -/
theorem measure_window (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) :
    ∀ (r N : ℕ) (y : Fin (N + 1) → S),
    μ {ω | ∀ i : Fin (N + 1), Z (r + i) ω = y i} =
      μ {ω | Z r ω = y 0} * ∏ i : Fin N, P (y i.castSucc) {y i.succ}
  | 0, N, y => by
    have h0 : μ {ω | Z 0 ω = y 0} = if y 0 = o then 1 else 0 := by
      simpa using hZ 0 (fun _ => y 0)
    simp only [zero_add]
    rw [hZ N y, h0]
  | r + 1, N, y => by
    have step : ∀ (N : ℕ) (y : Fin (N + 1) → S),
        μ {ω | ∀ i : Fin (N + 1), Z (r + 1 + i) ω = y i} =
          (∑' a, μ {ω | Z r ω = a} * P a {y 0}) * ∏ i : Fin N, P (y i.castSucc) {y i.succ} := by
      intro N y
      rw [measure_window_eq_tsum hm, ← ENNReal.tsum_mul_right]
      congr 1
      ext a
      rw [measure_window hm hZ r (N + 1), Fin.prod_univ_succ]
      simp [mul_assoc]
    have h1 : μ {ω | Z (r + 1) ω = y 0} = ∑' a, μ {ω | Z r ω = a} * P a {y 0} := by
      simpa using step 0 (fun _ => y 0)
    rw [step N y, ← h1]

/-- **Markov property at a deterministic time**, on the event that the chain is at `o`. -/
theorem lintegral_ite_shift (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (t s : ℕ)
    (g : (Fin (s + 1) → S) → ℝ≥0∞) :
    ∫⁻ ω, (if Z t ω = o then g (fun i => Z (t + i) ω) else 0) ∂μ =
      μ {ω | Z t ω = o} * ∫⁻ ω, g (fun i => Z i ω) ∂μ := by
  have hA : MeasurableSet {ω | Z t ω = o} := hm t (measurableSet_singleton o)
  have hΦ : Measurable fun ω (i : Fin (s + 1)) => Z (t + i) ω :=
    measurable_pi_iff.2 fun i => hm _
  have hΨ : Measurable fun ω (i : Fin (s + 1)) => Z i ω := measurable_pi_iff.2 fun i => hm _
  have hite : (fun ω => if Z t ω = o then g (fun i : Fin (s + 1) => Z (t + i) ω) else 0) =
      Set.indicator {ω | Z t ω = o} (fun ω => g (fun i => Z (t + i) ω)) := by
    ext ω; simp [Set.indicator_apply]
  rw [hite]
  rw [lintegral_indicator hA, lintegral_comp_eq_tsum hΦ, lintegral_comp_eq_tsum hΨ,
    ← ENNReal.tsum_mul_left]
  congr 1
  ext y
  rw [Measure.restrict_apply (hΦ (measurableSet_singleton y)), mul_left_comm]
  congr 1
  have hpre : ∀ (f : ℕ → ℕ), (fun ω (i : Fin (s + 1)) => Z (f i) ω) ⁻¹' {y} =
      {ω | ∀ i : Fin (s + 1), Z (f i) ω = y i} := by
    intro f; ext ω; simp [funext_iff]
  rw [hpre (fun i => t + i), hpre (fun i => i), hZ s y]
  by_cases hy : y 0 = o
  · have : {ω | ∀ i : Fin (s + 1), Z (t + i) ω = y i} ∩ {ω | Z t ω = o} =
        {ω | ∀ i : Fin (s + 1), Z (t + i) ω = y i} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro h; simpa [hy] using h 0
    rw [this, measure_window hm hZ t s y, hy]
    simp
  · have : {ω | ∀ i : Fin (s + 1), Z (t + i) ω = y i} ∩ {ω | Z t ω = o} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h h'; exact hy (by simpa [h'] using (h 0).symm)
    rw [this]
    simp [hy]

omit [DiscreteMeasurableSpace S] [Countable S] in
theorem measure_zero_eq_one
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) :
    μ {ω | Z 0 ω = o} = 1 := by
  simpa using hZ 0 (fun _ => o)

theorem measurable_count (hm : ∀ k, Measurable (Z k)) (f : ℕ → ℕ) (m : ℕ) :
    Measurable fun ω => ∑ i ∈ range m, if Z (f i) ω = o then 1 else 0 :=
  Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable (fun x : S => if x = o then (1 : ℕ) else 0)).comp (hm (f i))

/-- The Markov property at time `t` for a function of the visit count of the window
`Z t, …, Z (t + s)`. -/
theorem lintegral_count_shift (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (t s : ℕ)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ ω, (if Z t ω = o then F (∑ i ∈ range (s + 1), if Z (t + i) ω = o then 1 else 0)
      else 0) ∂μ =
      μ {ω | Z t ω = o} * ∫⁻ ω, F (∑ i ∈ range (s + 1), if Z i ω = o then 1 else 0) ∂μ := by
  have h := lintegral_ite_shift hm hZ t s (fun y => F (∑ i : Fin (s + 1), if y i = o then 1 else 0))
  have e1 : ∀ ω, (∑ i : Fin (s + 1), if Z (t + ↑i) ω = o then 1 else 0) =
      ∑ i ∈ range (s + 1), if Z (t + i) ω = o then 1 else 0 := fun ω =>
    Fin.sum_univ_eq_sum_range (fun i => if Z (t + i) ω = o then 1 else 0) (s + 1)
  have e2 : ∀ ω, (∑ i : Fin (s + 1), if Z ↑i ω = o then 1 else 0) =
      ∑ i ∈ range (s + 1), if Z i ω = o then 1 else 0 := fun ω =>
    Fin.sum_univ_eq_sum_range (fun i => if Z i ω = o then 1 else 0) (s + 1)
  simp only [e1, e2] at h
  exact h

/-- **Moments of the root visit count**: `E ℓ_n^j ≤ j! U_n^j`. -/
theorem lintegral_visitCount_pow_le [IsProbabilityMeasure μ] (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) :
    ∀ j n : ℕ, ∫⁻ ω, ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ≥0∞) ^ j ∂μ ≤
      j ! * (∑ k ∈ range (n + 1), μ {ω | Z k ω = o}) ^ j
  | 0, n => by simp
  | j + 1, n => by
    have hU : ∀ s ≤ n, (∑ k ∈ range (s + 1), μ {ω | Z k ω = o}) ≤
        ∑ k ∈ range (n + 1), μ {ω | Z k ω = o} :=
      fun s hs => sum_le_sum_of_subset (range_mono (by omega))
    have hpt : ∀ ω, ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ≥0∞) ^ (j + 1) ≤
        ((j + 1 : ℕ) : ℝ≥0∞) * ∑ t ∈ range (n + 1), if Z t ω = o then
          ((∑ i ∈ range (n - t + 1), if Z (t + i) ω = o then 1 else 0 : ℕ) : ℝ≥0∞) ^ j
          else 0 := by
      intro ω
      have h := sum_range_pow_succ_le j (n + 1) (fun k => if Z k ω = o then 1 else 0)
      calc _ = (((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) ^ (j + 1) : ℕ) :
            ℝ≥0∞) := (Nat.cast_pow _ _).symm
        _ ≤ _ := Nat.cast_le.2 h
        _ = _ := by
          rw [Nat.cast_mul, Nat.cast_sum]
          congr 1
          refine sum_congr rfl fun t ht => ?_
          have : n + 1 - t = n - t + 1 := by simp only [mem_range] at ht; omega
          rw [this]
          split_ifs <;> simp
    calc _ ≤ ∫⁻ ω, ((j + 1 : ℕ) : ℝ≥0∞) * ∑ t ∈ range (n + 1), (if Z t ω = o then
          ((∑ i ∈ range (n - t + 1), if Z (t + i) ω = o then 1 else 0 : ℕ) : ℝ≥0∞) ^ j
          else 0) ∂μ := lintegral_mono hpt
      _ = ((j + 1 : ℕ) : ℝ≥0∞) * ∑ t ∈ range (n + 1), ∫⁻ ω, (if Z t ω = o then
          ((∑ i ∈ range (n - t + 1), if Z (t + i) ω = o then 1 else 0 : ℕ) : ℝ≥0∞) ^ j
          else 0) ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finsetSum]
        intro t _
        exact Measurable.ite (hm t (measurableSet_singleton o))
          ((measurable_of_countable (fun c : ℕ => (c : ℝ≥0∞) ^ j)).comp
            (measurable_count hm (fun i => t + i) (n - t + 1))) measurable_const
      _ ≤ ((j + 1 : ℕ) : ℝ≥0∞) * ∑ t ∈ range (n + 1), μ {ω | Z t ω = o} *
          (j ! * (∑ k ∈ range (n + 1), μ {ω | Z k ω = o}) ^ j) := by
        gcongr with t ht
        rw [lintegral_count_shift hm hZ t (n - t) (fun c => (c : ℝ≥0∞) ^ j)]
        gcongr
        exact (lintegral_visitCount_pow_le hm hZ j (n - t)).trans
          (by gcongr; exact Nat.sub_le n t)
      _ = (j + 1)! * (∑ k ∈ range (n + 1), μ {ω | Z k ω = o}) ^ (j + 1) := by
        rw [← sum_mul, Nat.factorial_succ]
        push_cast
        ring

/-- **Linear lower tail of the root visit count**: `P(ℓ_n ≤ m) U_n ≤ m`. -/
theorem measure_visitCount_le_mul_le [IsProbabilityMeasure μ] (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (n m : ℕ) :
    μ {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} *
      ∑ k ∈ range (n + 1), μ {ω | Z k ω = o} ≤ m := by
  have hL : MeasurableSet {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} :=
    measurable_count hm (fun i => i) (n + 1) measurableSet_Iic
  have key : ∀ t, ∫⁻ ω, (if Z t ω = o then (if (∑ i ∈ range (n + 1),
      if Z (t + i) ω = o then 1 else 0) ≤ m then 1 else 0) else 0) ∂μ =
      μ {ω | Z t ω = o} * μ {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} := by
    intro t
    rw [lintegral_count_shift hm hZ t n (fun c => if c ≤ m then 1 else 0),
      ← lintegral_indicator_one hL]
    congr 1
    refine lintegral_congr fun ω => ?_
    simp [Set.indicator_apply]
  calc _ = ∑ t ∈ range (n + 1), μ {ω | Z t ω = o} *
        μ {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} := by
        rw [mul_comm, sum_mul]
    _ = ∑ t ∈ range (n + 1), ∫⁻ ω, (if Z t ω = o then (if (∑ i ∈ range (n + 1),
        if Z (t + i) ω = o then 1 else 0) ≤ m then 1 else 0) else 0) ∂μ :=
        sum_congr rfl fun t _ => (key t).symm
    _ = ∫⁻ ω, ∑ t ∈ range (n + 1), (if Z t ω = o then (if (∑ i ∈ range (n + 1),
        if Z (t + i) ω = o then 1 else 0) ≤ m then (1 : ℝ≥0∞) else 0) else 0) ∂μ := by
        rw [lintegral_finsetSum]
        intro t _
        exact Measurable.ite (hm t (measurableSet_singleton o))
          ((measurable_of_countable (fun c : ℕ => if c ≤ m then (1 : ℝ≥0∞) else 0)).comp
            (measurable_count hm (fun i => t + i) (n + 1))) measurable_const
    _ ≤ ∫⁻ _, (m : ℝ≥0∞) ∂μ := by
        refine lintegral_mono fun ω => ?_
        simp_rw [← ite_and]
        rw [sum_boole]
        have e : ∀ t, (∑ i ∈ range (n + 1), if Z (t + i) ω = o then 1 else 0) =
            #({i ∈ range (n + 1) | Z (t + i) ω = o}) := fun t => (card_filter _ _).symm
        simp only [e]
        exact_mod_cast card_filter_window_le (fun k => Z k ω = o) n m
    _ = m := by simp

omit [DiscreteMeasurableSpace S] [Countable S] in
/-- `U_n ≥ 1`, from the visit at time zero. -/
theorem one_le_sum_measureReal [IsProbabilityMeasure μ]
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (n : ℕ) :
    1 ≤ ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o} := by
  have h := single_le_sum (f := fun k => μ.real {ω | Z k ω = o})
    (fun k _ => measureReal_nonneg) (mem_range.2 (Nat.succ_pos n))
  simpa [measureReal_def, measure_zero_eq_one hZ] using h

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S] [DecidableEq S] in
theorem ofReal_sum_measureReal [IsProbabilityMeasure μ] (n : ℕ) :
    ENNReal.ofReal (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) =
      ∑ k ∈ range (n + 1), μ {ω | Z k ω = o} := by
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => measureReal_nonneg]
  exact sum_congr rfl fun k _ => ofReal_measureReal

/-- `E (ℓ_n / U_n)^j ≤ j!`. -/
theorem lintegral_ofReal_visitCount_div_pow_le [IsProbabilityMeasure μ]
    (hm : ∀ k, Measurable (Z k)) (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1)
        , Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (n j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ)
        / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ j) ∂μ ≤ j ! := by
  have hU : 0 < ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}
      := one_pos.trans_le (one_le_sum_measureReal hZ n)
  have hV0 : ENNReal.ofReal (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ≠ 0 := by simpa using hU
  have hpt : ∀ ω, ENNReal.ofReal ((((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ)
      / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ j) =
      ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ≥0∞) ^ j *
        (ENNReal.ofReal (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ j)⁻¹ := by
    intro ω
    rw [ENNReal.ofReal_pow (div_nonneg (Nat.cast_nonneg _) hU.le),
      ENNReal.ofReal_div_of_pos hU, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_pow,
      ENNReal.inv_pow]
  simp_rw [hpt]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (pow_ne_zero _ hV0))]
  calc _ ≤ (j ! : ℝ≥0∞) * ENNReal.ofReal (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ j
      * (ENNReal.ofReal (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ j)⁻¹ := by
        rw [ofReal_sum_measureReal]
        gcongr
        exact lintegral_visitCount_pow_le hm hZ j n
    _ = j ! := by
        rw [mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ hV0)
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), mul_one]

/-- **Exponential upper tail**: `E exp (θ ℓ_n / U_n) ≤ (1 - θ)⁻¹` for `0 ≤ θ < 1`. -/
theorem lintegral_exp_visitCount_le [IsProbabilityMeasure μ] (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n
            , P (x i.castSucc) {x i.succ}) (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (((∑ k ∈ range (n + 1), if Z k ω
        = o then 1 else 0 : ℕ) : ℝ) / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}))) ∂μ
            ≤ ENNReal.ofReal (1 - θ)⁻¹ := by
  have hU : 0 < ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}
      := one_pos.trans_le (one_le_sum_measureReal hZ n)
  have hX : Measurable fun ω => ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ)
      / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o} :=
    (measurable_of_countable (fun c : ℕ => (c : ℝ) / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω
        = o})).comp
      (measurable_count hm (fun i => i) (n + 1))
  have h := lintegral_pow_mul_exp (P := μ) hX (fun ω => div_nonneg (Nat.cast_nonneg _) hU.le)
    hθ0 0
  simp only [pow_zero, one_mul, zero_add] at h
  rw [h]
  calc _ ≤ ∑' k : ℕ, ENNReal.ofReal (θ ^ k / k !) * (k ! : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun k => by
          gcongr; exact lintegral_ofReal_visitCount_div_pow_le hm hZ n k
    _ = ∑' k : ℕ, ENNReal.ofReal (θ ^ k) := by
        congr 1
        ext k
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = ENNReal.ofReal (1 - θ)⁻¹ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hθ0 k)
          (summable_geometric_of_lt_one hθ0 hθ1), tsum_geometric_of_lt_one hθ0 hθ1]

/-- **Exponential upper tail**, as a Bochner integral. -/
theorem integral_exp_visitCount_le [IsProbabilityMeasure μ] (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n
            , P (x i.castSucc) {x i.succ}) (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∫ ω, Real.exp (θ * (((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ)
        / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o})) ∂μ ≤ 1 / (1 - θ) := by
  have hX : Measurable fun ω => ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ)
      / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o} :=
    (measurable_of_countable (fun c : ℕ => (c : ℝ) / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω
        = o})).comp
      (measurable_count hm (fun i => i) (n + 1))
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (Real.measurable_exp.comp (hX.const_mul θ)).aestronglyMeasurable, one_div]
  exact ENNReal.toReal_le_of_le_ofReal (inv_nonneg.2 (by linarith))
    (lintegral_exp_visitCount_le hm hZ n hθ0 hθ1)

/-- **Linear lower tail**: `P(ℓ_n ≤ m) ≤ m / U_n`. -/
theorem measureReal_visitCount_le_le_div [IsProbabilityMeasure μ] (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (n m : ℕ) :
    μ.real {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} ≤ m / ∑ k ∈ range (n + 1)
        , μ.real {ω | Z k ω = o} := by
  have hU : 0 < ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}
      := one_pos.trans_le (one_le_sum_measureReal hZ n)
  rw [le_div_iff₀ hU, measureReal_def]
  have h := measure_visitCount_le_mul_le hm hZ n m
  rw [← ofReal_sum_measureReal] at h
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top m) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hU.le, ENNReal.toReal_natCast] at this

/-- The lower tail with the constant `e / (1 - e⁻¹)`. -/
theorem measureReal_visitCount_le_le_min [IsProbabilityMeasure μ] (hm : ∀ k, Measurable (Z k))
    (hZ : ∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) (n m : ℕ) :
    μ.real {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} ≤
      min 1 (Real.exp 1 / (1 - Real.exp (-1)) * (m / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω
          = o})) := by
  have hU : 0 < ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}
      := one_pos.trans_le (one_le_sum_measureReal hZ n)
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hC : 1 ≤ Real.exp 1 / (1 - Real.exp (-1)) := by
    rw [le_div_iff₀ (by linarith)]
    linarith [Real.exp_pos (-1), Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)]
  refine le_min ?_ ((measureReal_visitCount_le_le_div hm hZ n m).trans
    (le_mul_of_one_le_left (div_nonneg (Nat.cast_nonneg _) hU.le) hC))
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

end PercLib.Probability
