/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrappers for two displacement-kernel assertions: cuts on both sides of
every vertex for a one-dimensional distance profile with finite first moment, and the
diagonal-insensitive row identity of a displacement kernel. New proofs from the imported
modules; no upstream code is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.OneDimensional
public import PercLib.Models.TranslationInvariant
public import PercLib.Percolation.Bond.Diagonal.Probability

/-! # Cuts on the line and off-diagonal rows of displacement kernels

## Main results

* `ae_cuts_unbounded_and_cluster_finite`: for a profile `q` on `ℤ` with
  `q s(a,b) = p |b - a|` off the diagonal (diagonal arbitrary), `p n < 1` for `n ≥ 1` and
  `∑ n p n < ∞`, almost surely closed gaps occur arbitrarily far to the right and to the
  left, and every open cluster is finite.
* `rowSum_eq_and_le_of_offDiagonal_translationInvariant`: if `J s(x,y) = k (y - x)` for
  `x ≠ y` on an additive group, the off-diagonal row of `J` at every vertex is
  `∑'_{z ≠ 0} k z ≤ ∑' z, k z` in `ℝ≥0∞`, whatever the diagonal values of `J`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- Gap cuts only involve non-diagonal pairs, so configurations agreeing off the diagonal
have the same cuts. -/
theorem cut_iff_of_sdiff_diagSet_eq {ω ω' : Config ℤ}
    (h : ω \ Sym2.diagSet = ω' \ Sym2.diagSet) (k : ℤ) :
    (∀ a b, a ≤ k → k < b → s(a, b) ∉ ω) ↔ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω' := by
  have key : ∀ a b : ℤ, a ≤ k → k < b → (s(a, b) ∈ ω ↔ s(a, b) ∈ ω') := by
    intro a b ha hb
    have hnd : ¬ (s(a, b) : Sym2 ℤ).IsDiag := by
      rw [Sym2.mk_isDiag_iff]; omega
    have h1 : s(a, b) ∈ ω \ Sym2.diagSet ↔ s(a, b) ∈ ω' \ Sym2.diagSet := by rw [h]
    simpa [Set.mem_sdiff, Sym2.mem_diagSet, hnd] using h1
  exact ⟨fun H a b ha hb hm => H a b ha hb ((key a b ha hb).2 hm),
    fun H a b ha hb hm => H a b ha hb ((key a b ha hb).1 hm)⟩

/-- A profile given by a distance profile off the diagonal agrees off the diagonal with
one given by that distance profile everywhere. -/
theorem exists_eq_distance_of_offDiagonal (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a))) :
    ∃ q' : Sym2 ℤ → unitInterval, (∀ a b, q' s(a, b) = p (Int.natAbs (b - a))) ∧
      ∀ e, ¬ e.IsDiag → q e = q' e := by
  classical
  refine ⟨fun e => if e.IsDiag then p 0 else q e, fun a b => ?_, fun e he => by simp [he]⟩
  by_cases hab : a = b
  · subst hab; simp
  · simp only [Sym2.mk_isDiag_iff, hab, ite_false]
    exact hq a b hab

/-- **Cuts recur to the right** for a distance profile off the diagonal (diagonal
arbitrary) with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞`. -/
theorem law_cuts_atTop_eq_one_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, N ≤ k ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} = 1 := by
  obtain ⟨q', hq', hqq'⟩ := exists_eq_distance_of_offDiagonal p q hq
  have hinv : ∀ x y g : ℤ, q' s(x + g, y + g) = q' s(x, y) := fun x y g => by
    rw [hq', hq', add_sub_add_right_eq_sub]
  rw [law_event_eq_of_offDiagonal q q' hqq' measurableSet_cuts_atTop (fun ω ω' h => by
    simp only [Set.mem_ofPred_eq, cut_iff_of_sdiff_diagSet_eq h])]
  exact law_cuts_atTop_eq_one q' hinv (law_cut_pos p q' hq' hsum hlt 0)
    fun k => by rw [law_cut_eq_tprod p q' hq' 0, law_cut_eq_tprod p q' hq' k]

/-- **Cuts recur to the left** for a distance profile off the diagonal (diagonal
arbitrary) with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞`. -/
theorem law_cuts_atBot_eq_one_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    law q {ω : Config ℤ | ∀ N : ℤ, ∃ k, k ≤ N ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω} = 1 := by
  obtain ⟨q', hq', hqq'⟩ := exists_eq_distance_of_offDiagonal p q hq
  have hinv : ∀ x y g : ℤ, q' s(x + g, y + g) = q' s(x, y) := fun x y g => by
    rw [hq', hq', add_sub_add_right_eq_sub]
  rw [law_event_eq_of_offDiagonal q q' hqq' measurableSet_cuts_atBot (fun ω ω' h => by
    simp only [Set.mem_ofPred_eq, cut_iff_of_sdiff_diagSet_eq h])]
  exact law_cuts_atBot_eq_one q' hinv (law_cut_pos p q' hq' hsum hlt 0)
    fun k => by rw [law_cut_eq_tprod p q' hq' 0, law_cut_eq_tprod p q' hq' k]

/-- Almost surely closed gaps occur arbitrarily far to the right. -/
theorem ae_cuts_atTop_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, ∀ N : ℤ, ∃ k, N ≤ k ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω :=
  (ae_iff_measure_eq measurableSet_cuts_atTop.nullMeasurableSet).mpr
    (by rw [law_cuts_atTop_eq_one_of_offDiagonal p q hq hlt hsum, measure_univ])

/-- Almost surely closed gaps occur arbitrarily far to the left. -/
theorem ae_cuts_atBot_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, ∀ N : ℤ, ∃ k, k ≤ N ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω :=
  (ae_iff_measure_eq measurableSet_cuts_atBot.nullMeasurableSet).mpr
    (by rw [law_cuts_atBot_eq_one_of_offDiagonal p q hq hlt hsum, measure_univ])

/-- Closed gaps arbitrarily far in both directions make every cluster finite. -/
theorem cluster_finite_of_cuts_unbounded (ω : Config ℤ)
    (hu : ∀ N : ℤ, ∃ k, N ≤ k ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω)
    (hd : ∀ N : ℤ, ∃ k, k ≤ N ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω) (x : ℤ) :
    (cluster ω x).Finite := by
  obtain ⟨k₂, hk₂, hc₂⟩ := hu x
  obtain ⟨k₁, hk₁, hc₁⟩ := hd (x - 1)
  exact (Set.finite_Ioc k₁ k₂).subset (cluster_subset_Ioc_of_cuts ω (by omega) hk₂ hc₁ hc₂)

/-- Almost surely every open cluster is finite, for a distance profile off the diagonal
(diagonal arbitrary) with `p n < 1` for `n ≥ 1` and `∑ n p n < ∞`. -/
theorem ae_cluster_finite_of_offDiagonal (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite := by
  filter_upwards [ae_cuts_atTop_of_offDiagonal p q hq hlt hsum,
    ae_cuts_atBot_of_offDiagonal p q hq hlt hsum] with ω hu hd
  exact cluster_finite_of_cuts_unbounded ω hu hd

/-- On `ℤ`, let the pair probabilities be a distance profile `p` off the diagonal (any
values on the diagonal), with `p n < 1` for every `n ≥ 1` and `∑ n p n` finite. Then
almost surely the closed gaps are unbounded above and below, and every open cluster is
finite. -/
@[tag "ZH13"]
theorem ae_cuts_unbounded_and_cluster_finite (p : ℕ → unitInterval)
    (q : Sym2 ℤ → unitInterval) (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a)))
    (hlt : ∀ n, 1 ≤ n → p n < 1) (hsum : Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂law q, (∀ N : ℤ, ∃ k, N ≤ k ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω) ∧
      (∀ N : ℤ, ∃ k, k ≤ N ∧ ∀ a b, a ≤ k → k < b → s(a, b) ∉ ω) ∧
      ∀ x, (cluster ω x).Finite := by
  filter_upwards [ae_cuts_atTop_of_offDiagonal p q hq hlt hsum,
    ae_cuts_atBot_of_offDiagonal p q hq hlt hsum,
    ae_cluster_finite_of_offDiagonal p q hq hlt hsum] with ω hu hd hf
  exact ⟨hu, hd, hf⟩

end PercLib.Models.LongRange

namespace PercLib.Models

open Classical

variable {G : Type*} [AddGroup G]

/-- The off-diagonal row of a pair intensity that equals a displacement kernel off the
diagonal is the kernel mass away from zero, whatever its diagonal values. -/
theorem rowSum_eq_of_offDiagonal_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) =
      ∑' z, if z = 0 then 0 else (k z : ℝ≥0∞) := by
  rw [← (Equiv.addRight v).tsum_eq]
  refine tsum_congr fun z => ?_
  by_cases hz : z = 0
  · simp [hz]
  · have hne : v ≠ z + v := fun h => hz (by simpa using h.symm)
    simp [hz, hJ v (z + v) hne]

/-- The off-diagonal row of a pair intensity that equals a displacement kernel off the
diagonal is at most the total kernel mass. -/
theorem rowSum_le_tsum_of_offDiagonal_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x, y) = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) ≤ ∑' z, (k z : ℝ≥0∞) := by
  rw [rowSum_eq_of_offDiagonal_translationInvariant J k hJ v]
  exact ENNReal.tsum_le_tsum fun z => by split_ifs <;> simp

/-- On a countable group (written additively), let `k` be a finite nonnegative kernel and
let the pair intensity `J` equal `k (y - x)` at every pair `x ≠ y`, its diagonal values
being arbitrary. Then at every vertex the off-diagonal row of `J` equals the kernel mass
away from the identity, as extended nonnegative sums, and so is at most the total mass
of `k`. -/
@[tag "R01V"]
theorem rowSum_eq_and_le_of_offDiagonal_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, x ≠ y → J s(x, y) = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) =
        ∑' z, (if z = 0 then 0 else (k z : ℝ≥0∞)) ∧
      (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) ≤ ∑' z, (k z : ℝ≥0∞) :=
  ⟨rowSum_eq_of_offDiagonal_translationInvariant J k hJ v,
    rowSum_le_tsum_of_offDiagonal_translationInvariant J k hJ v⟩

end PercLib.Models
