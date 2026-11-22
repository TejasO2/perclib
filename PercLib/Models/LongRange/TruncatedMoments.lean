/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written 2026-11-22 for the truncation/moment prerequisites of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1.
No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.UniformVolumeTail
public import PercLib.Models.HierarchicalCutoff

/-!
# Tail sums of cluster volumes

The paper's volume moment `E|K|^p` is unbounded; the formalised Russo formula
(`PercLib.Models.LongRange.hasDerivAt_integral_cutoff`) takes a bounded, eventually constant
observable `F : ℕ∞ → ℝ`. The passage between the unbounded moment and the bounded truncations
is a tail-sum (layer cake) identity, which this file proves on the existing bond model.

* `lintegral_iSup_sum_mul_indicator_enat_lt`: weighted layer cake for a measurable
  `f : α → ℕ∞`: if `g x = ⨆ N, ∑_{n < N} c n * 1(n < x)` then
  `∫⁻ g (f a) ∂μ = ∑' n, c n * μ {a | n < f a}`. No finiteness of `μ` beyond the statement.
* `enat_coe_eq_iSup_sum_ite_lt`: the `p = 1` instance, `x = ⨆ N, ∑_{n<N} 1(n < x)`;
* `enat_coe_pow_eq_iSup_sum_ite_lt`: the `p ≥ 1` instance,
  `x^p = ⨆ N, ∑_{n<N} ((n+1)^p - n^p) 1(n < x)` (telescoping);
* `lintegral_encard_cluster_eq_tsum_tail`: `E|K_o| = ∑_n P(n < |K_o|)` for the cluster volume
  `(cluster ω o).encard` under `law q`;
* `lintegral_encard_cluster_pow_eq_tsum_tail`: `E|K_o|^p = ∑_n ((n+1)^p - n^p) P(n < |K_o|)`.
Both are exact in `ℝ≥0∞`, so infinite cluster volume contributes `∞` on both sides: no
finiteness of the cluster is assumed, and the truncation step for the Russo formula needs no
dominator (only the derivative limit does).

Non-vacuity: the zero profile on `ℤ` has `|K_o| = 1` a.e., and the left side of the `p = 1`
identity evaluates to `1`.

Scope: these are tail-sum identities for any bond profile on a countable vertex set. They do
not assert differentiability or the limit of truncated derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Analysis

/-- **Weighted layer cake for `ℕ∞`-valued functions.** If `g` is the supremum of the partial
sums `∑_{n < N} c n * 1(n < x)`, then integrating `g ∘ f` against `μ` gives
`∑' n, c n * μ {a | n < f a}`. -/
theorem lintegral_iSup_sum_mul_indicator_enat_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℕ∞} (hf : Measurable f) (c : ℕ → ℝ≥0∞) {g : ℕ∞ → ℝ≥0∞}
    (hg : ∀ x : ℕ∞, g x = ⨆ N : ℕ, ∑ n ∈ Finset.range N,
      c n * (if (n : ℕ∞) < x then 1 else 0)) :
    ∫⁻ a, g (f a) ∂μ = ∑' n : ℕ, c n * μ {a | (n : ℕ∞) < f a} := by
  have hset : ∀ n : ℕ, MeasurableSet {a : α | (n : ℕ∞) < f a} :=
    fun n => hf (show MeasurableSet (Set.Ioi (n : ℕ∞)) from trivial)
  have hterm : ∀ n : ℕ, ∫⁻ a, c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) ∂μ =
      c n * μ {a : α | (n : ℕ∞) < f a} := by
    intro n
    have hfun : (fun a => c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0)) =
        {a : α | (n : ℕ∞) < f a}.indicator (fun _ => c n) := by
      funext a
      by_cases h : (n : ℕ∞) < f a <;> simp [Set.indicator, h]
    rw [hfun, lintegral_indicator (hset n), setLIntegral_const]
  have hmeas : ∀ n : ℕ, Measurable fun a : α =>
      c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) := by
    intro n
    have hfun : (fun a : α => c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0)) =
        {a : α | (n : ℕ∞) < f a}.indicator (fun _ => c n) := by
      funext a
      by_cases h : (n : ℕ∞) < f a <;> simp [Set.indicator, h]
    rw [hfun]
    exact measurable_const.indicator (hset n)
  have hsup : (fun a => g (f a)) = fun a => ⨆ N : ℕ, ∑ n ∈ Finset.range N,
      c n * (if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) := funext fun a => hg (f a)
  rw [hsup, lintegral_iSup]
  · rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_congr fun N => ?_
    rw [lintegral_finsetSum (s := Finset.range N) (fun n _ => hmeas n)]
    exact Finset.sum_congr rfl fun n _ => hterm n
  · exact fun N => Finset.measurable_sum _ fun n _ => hmeas n
  · exact fun N M hNM a => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      fun i _ _ => by positivity

end PercLib.Analysis

namespace PercLib.Analysis

/-- The partial sums of the `p = 1` layer cake, for a finite value `k`. -/
theorem sum_range_ite_enat_lt_cast (N k : ℕ) :
    ∑ n ∈ Finset.range N, (if (n : ℕ∞) < (k : ℕ∞) then (1 : ℝ≥0∞) else 0) =
      ((min N k : ℕ) : ℝ≥0∞) := by
  rw [← Finset.sum_filter (p := fun n : ℕ => (n : ℕ∞) < (k : ℕ∞))]
  have hfilt : (Finset.range N).filter (fun n : ℕ => (n : ℕ∞) < (k : ℕ∞)) =
      Finset.range (min N k) := by
    ext n
    simp [Finset.mem_filter, Finset.mem_range]
  rw [hfilt]
  simp

/-- **`p = 1` layer cake for `ℕ∞`.** `x` is the supremum of its partial counting sums. -/
theorem enat_coe_eq_iSup_sum_ite_lt (x : ℕ∞) :
    (x : ℝ≥0∞) = ⨆ N : ℕ,
      ∑ n ∈ Finset.range N, (if (n : ℕ∞) < x then (1 : ℝ≥0∞) else 0) := by
  rcases eq_or_ne x ⊤ with hx | hx
  · subst hx
    have hpt : ∀ N : ℕ,
        ∑ n ∈ Finset.range N, (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) =
          (N : ℝ≥0∞) := by
      intro N
      simp
    simp only [hpt]
    exact ENNReal.iSup_natCast.symm
  · obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hx
    simp only [sum_range_ite_enat_lt_cast]
    refine le_antisymm ?_ (iSup_le fun N => ?_)
    · calc (((k : ℕ∞)) : ℝ≥0∞) = (((min k k : ℕ)) : ℝ≥0∞) := by simp
      _ ≤ ⨆ N, (((min N k : ℕ)) : ℝ≥0∞) := le_iSup (fun N => (((min N k : ℕ)) : ℝ≥0∞)) k
    · exact_mod_cast Nat.min_le_right N k

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- **Tail sum of the cluster volume.** Under `law q`, the expected cluster volume equals the
sum of the tails of `(cluster ω o).encard`. Both sides are in `ℝ≥0∞`: infinite cluster volume
contributes `∞` to both, so no finiteness hypothesis is needed. -/
theorem lintegral_encard_cluster_eq_tsum_tail (q : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂law q =
      ∑' n : ℕ, law q {ω | (n : ℕ∞) < (cluster ω o).encard} := by
  have h := PercLib.Analysis.lintegral_iSup_sum_mul_indicator_enat_lt (μ := law q)
    (f := fun ω => (cluster ω o).encard) (measurable_encard_cluster o) (fun _ => 1)
    (g := fun x => (x : ℝ≥0∞)) fun x => by
      rw [PercLib.Analysis.enat_coe_eq_iSup_sum_ite_lt x]
      exact iSup_congr fun N => Finset.sum_congr rfl fun n _ => by rw [one_mul]
  simpa using h

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-- **Non-vacuity.** Under the zero profile on `ℤ` every cluster is a singleton
(`ae_cluster_eq_singleton_of_offDiagonal`), so `|K_o| = 1` almost surely and the left side of
`lintegral_encard_cluster_eq_tsum_tail` is the probability `1`. -/
example (o : ℤ) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂law (fun _ : Sym2 ℤ => (0 : unitInterval)) = 1 := by
  have hae : ∀ᵐ ω ∂law (fun _ : Sym2 ℤ => (0 : unitInterval)),
      ((cluster ω o).encard : ℝ≥0∞) = 1 :=
    (ae_cluster_eq_singleton_of_offDiagonal _ fun x y _ => rfl).mono fun ω h => by
      rw [h o, Set.encard_singleton]
      simp
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

end PercLib.Percolation.Bond

namespace PercLib.Analysis

theorem sum_range_ofReal_pow_sub (p k : ℕ) (hp : 1 ≤ p) :
    ∑ n ∈ Finset.range k, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) =
      (k : ℝ≥0∞) ^ p := by
  have hnn : ∀ n ∈ Finset.range k, 0 ≤ ((n : ℝ) + 1) ^ p - (n : ℝ) ^ p := by
    intro n _
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h3 := pow_le_pow_left₀ h1 h2 p
    linarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  rw [show (k : ℝ≥0∞) ^ p = ENNReal.ofReal ((k : ℝ) ^ p) by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]]
  congr 1
  have htel := Finset.sum_range_sub (fun i : ℕ => ((i : ℝ)) ^ p) k
  simpa [Nat.cast_zero, zero_pow (by omega : p ≠ 0)] using htel

theorem one_le_ofReal_pow_sub (p n : ℕ) (hp : 1 ≤ p) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) := by
  rw [ENNReal.one_le_ofReal]
  have hlt : n ^ p < (n + 1) ^ p := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by omega)
  have h1 : ((n ^ p : ℕ) : ℝ) + 1 ≤ (((n + 1) ^ p : ℕ) : ℝ) := by exact_mod_cast hlt
  push_cast at h1 ⊢
  linarith

theorem enat_coe_pow_eq_iSup_sum_ite_lt (p : ℕ) (hp : 1 ≤ p) (x : ℕ∞) :
    (x : ℝ≥0∞) ^ p = ⨆ N : ℕ, ∑ n ∈ Finset.range N,
      ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) * (if (n : ℕ∞) < x then 1 else 0) := by
  have hc : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ p - (n : ℝ) ^ p := by
    intro n
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h3 := pow_le_pow_left₀ h1 h2 p
    linarith
  rcases eq_or_ne x ⊤ with hx | hx
  · subst hx
    rw [show ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ from rfl, ENNReal.top_pow (by omega : p ≠ 0)]
    refine le_antisymm ?_ le_top
    rw [← ENNReal.iSup_natCast]
    refine iSup_le fun N => ?_
    have hpt : ∑ n ∈ Finset.range N, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
        (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) =
        ∑ n ∈ Finset.range N, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp
    calc (N : ℝ≥0∞) = ∑ n ∈ Finset.range N, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) :=
          Finset.sum_le_sum fun n _ => one_le_ofReal_pow_sub p n hp
      _ = _ := hpt.symm
      _ ≤ ⨆ N, ∑ n ∈ Finset.range N,
            ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
              (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) :=
          le_iSup (fun N => ∑ n ∈ Finset.range N,
            ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
              (if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0)) N
  · obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hx
    have hfilt : ∀ N : ℕ, (Finset.range N).filter (fun n : ℕ => (n : ℕ∞) < (k : ℕ∞)) =
        Finset.range (min N k) := by
      intro N
      ext n
      simp [Finset.mem_filter, Finset.mem_range]
    have hterm : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
          (if (n : ℕ∞) < ((k : ℕ∞)) then 1 else 0) =
        ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p) := by
      intro N
      have hstep : ∀ n ∈ Finset.range N,
          ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
            (if (n : ℕ∞) < ((k : ℕ∞)) then 1 else 0) =
          (if (n : ℕ∞) < ((k : ℕ∞)) then ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p)
            else 0) := by
        intro n _
        by_cases h : (n : ℕ∞) < ((k : ℕ∞)) <;> simp [h]
      rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter (p := fun n : ℕ => (n : ℕ∞) < (k : ℕ∞)),
        hfilt N]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => hc m)]
      rw [show (∑ n ∈ Finset.range (min N k), (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p)) =
          ((min N k : ℕ) : ℝ) ^ p by
        have htel := Finset.sum_range_sub (fun i : ℕ => ((i : ℝ)) ^ p) (min N k)
        simpa [Nat.cast_zero, zero_pow (by omega : p ≠ 0)] using htel]
    rw [show ((↑k : ℕ∞) : ℝ≥0∞) ^ p = ENNReal.ofReal (((k : ℕ) : ℝ) ^ p) by
      rw [show ((↑k : ℕ∞) : ℝ≥0∞) = (k : ℝ≥0∞) from rfl, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (Nat.cast_nonneg k)]]
    simp only [hterm]
    have hupper : ∀ N : ℕ, ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p) ≤
        ENNReal.ofReal (((k : ℕ) : ℝ) ^ p) := by
      intro N
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : (min N k : ℕ) ≤ k := Nat.min_le_right N k
      have hcast : ((min N k : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hle
      have := pow_le_pow_left₀ (Nat.cast_nonneg (min N k)) hcast p
      simpa using this
    refine le_antisymm ?_ (iSup_le hupper)
    calc ENNReal.ofReal (((k : ℕ) : ℝ) ^ p) = ENNReal.ofReal (((min k k : ℕ) : ℝ) ^ p) := by
          simp
      _ ≤ ⨆ N, ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p) :=
          le_iSup (fun N => ENNReal.ofReal (((min N k : ℕ) : ℝ) ^ p)) k


end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- **Tail sum of a cluster-volume power.** The `p`-th moment of the cluster volume is the
sum of the jumps `(n+1)^p - n^p` weighted by the tails of `(cluster ω o).encard`, exactly in
`ℝ≥0∞`; no finiteness hypothesis is used, and the exponent `p ≥ 1` is needed for the
telescoping weights `1^p - 0^p = 1`. -/
theorem lintegral_encard_cluster_pow_eq_tsum_tail (q : Sym2 V → unitInterval) (o : V)
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law q =
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p) *
        law q {ω | (n : ℕ∞) < (cluster ω o).encard} :=
  PercLib.Analysis.lintegral_iSup_sum_mul_indicator_enat_lt (μ := law q)
    (f := fun ω => (cluster ω o).encard) (measurable_encard_cluster o)
    (c := fun n => ENNReal.ofReal (((n : ℝ) + 1) ^ p - (n : ℝ) ^ p))
    (g := fun x => (x : ℝ≥0∞) ^ p)
    (fun x => PercLib.Analysis.enat_coe_pow_eq_iSup_sum_ite_lt p hp x)

end PercLib.Percolation.Bond
