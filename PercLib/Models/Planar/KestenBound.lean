/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: H. Kesten, The critical probability of bond percolation on the square
lattice equals 1/2, Comm. Math. Phys. 74 (1980), 41-59; G. Grimmett, Percolation, 2nd ed.,
Springer, 1999, Section 11.3.
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import PercLib.Models.Planar.SelfDuality
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.Transport

/-!
# Kesten's bound: bond percolation on `ℤ²` percolates above one half

Nearest-neighbour bond percolation on `ℤ²` is the intensity model with kernel
`J = (zdGraph 2).edgeSet.indicator 1`: an edge is open with probability `1 - e^{-β}`, so the
edge probability `1/2` is the intensity `β = log 2`. This file proves `β_c ≤ log 2`, that is
`p_c(ℤ²) ≤ 1/2`.

* At `β = log 2` the susceptibility is infinite
  (`chi_intensityProfile_indicator_edgeSet_log_two_eq_top`). The box
  `[0, n + 1] × [0, n]` is crossed from left to right with probability `1/2`
  (`law_crossing_zero_eq_half`); a crossing joins one of the `n + 1` vertices of the left side
  to the column at distance `n + 1`, so by translation invariance the sum `a(n + 1)` of the
  two-point function over that column satisfies `(n + 1) a(n + 1) ≥ 1/2`. Summing over `n`
  gives the harmonic series.
* Sharpness (`chi_lt_top_of_lt_rootCriticalIntensity`) turns this into `β_c ≤ log 2`
  (`rootCriticalIntensity_indicator_edgeSet_le_log_two`), for the root threshold and the
  global one.
* The mean-field lower bound of sharpness then gives `P_β(|K_o| = ∞) ≥ 1 - log 2 / β > 0` for
  every `β > log 2`, that is percolation for every edge probability `p > 1/2`
  (`law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt`).

## Main results

* `PercLib.Models.Planar.chi_intensityProfile_indicator_edgeSet_log_two_eq_top`
* `PercLib.Models.Planar.rootCriticalIntensity_indicator_edgeSet_le_log_two`
* `PercLib.Models.Planar.globalCriticalIntensity_indicator_edgeSet_le_log_two`
* `PercLib.Models.Planar.one_sub_div_le_law_cluster_infinite_indicator_edgeSet`
* `PercLib.Models.Planar.law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Models.Planar

/-! ### The nearest-neighbour kernel of `ℤ²` -/

/-- Translations preserve the edges of `ℤ²`, in both directions. -/
theorem map_add_mem_edgeSet_iff (c : LatticeSite 2) (e : Sym2 (LatticeSite 2)) :
    Sym2.map (· + c) e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet := by
  refine ⟨fun h => ?_, map_add_mem_edgeSet c⟩
  have h' := map_add_mem_edgeSet (-c) h
  have hid : ((fun v : LatticeSite 2 => v + -c) ∘ fun v => v + c) = id := by
    funext v
    simp
  rwa [Sym2.map_map, hid, Sym2.map_id, id] at h'

/-- The nearest-neighbour kernel is invariant under translations. -/
theorem indicator_edgeSet_map_add (c : LatticeSite 2) (e : Sym2 (LatticeSite 2)) :
    (zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0) (Sym2.map (· + c) e) =
      (zdGraph 2).edgeSet.indicator 1 e := by
  by_cases he : e ∈ (zdGraph 2).edgeSet
  · rw [indicator_of_mem he, indicator_of_mem ((map_add_mem_edgeSet_iff c e).2 he),
      Pi.one_apply, Pi.one_apply]
  · rw [indicator_of_notMem he, indicator_of_notMem (mt (map_add_mem_edgeSet_iff c e).1 he)]

/-- The nearest-neighbour kernel of `ℤ²` is transitive: a translation maps any vertex to any
other and preserves the kernel. -/
theorem indicator_edgeSet_transitive (x y : LatticeSite 2) :
    ∃ σ : LatticeSite 2 ≃ LatticeSite 2, σ x = y ∧
      ∀ e, (zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0) (Sym2.map σ e) =
        (zdGraph 2).edgeSet.indicator 1 e :=
  ⟨Equiv.addRight (y - x), by simp, fun e => indicator_edgeSet_map_add (y - x) e⟩

/-- The rows of the nearest-neighbour kernel of `ℤ²` are summable: each vertex has finitely
many neighbours. -/
theorem summable_indicator_edgeSet (u : LatticeSite 2) :
    Summable fun v =>
      (((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0) s(u, v) : ℝ≥0) : ℝ) := by
  refine summable_of_ne_finset_zero (s := (zdGraph_finite_neighborSet u).toFinset)
    fun v hv => ?_
  rw [Set.Finite.mem_toFinset, SimpleGraph.mem_neighborSet] at hv
  rw [indicator_of_notMem fun h => hv ((SimpleGraph.mem_edgeSet _).1 h)]
  simp

/-- At intensity `log 2` every edge of `ℤ²` is open with probability `1/2`. -/
theorem intensityProfile_indicator_edgeSet_log_two {e : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) :
    (intensityProfile ((zdGraph 2).edgeSet.indicator 1) (Real.log 2).toNNReal e : ℝ) =
      1 / 2 := by
  have h2 : ((Real.log 2).toNNReal : ℝ) = Real.log 2 :=
    Real.coe_toNNReal _ (Real.log_nonneg one_le_two)
  change 1 - Real.exp (-((Real.log 2).toNNReal : ℝ) *
    (((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0) e : ℝ≥0) : ℝ)) = 1 / 2
  rw [indicator_of_mem he, h2, Pi.one_apply, NNReal.coe_one, mul_one, Real.exp_neg,
    Real.exp_log two_pos]
  norm_num

/-- Translation invariance of the two-point function of the nearest-neighbour model. -/
theorem tau_intensityProfile_indicator_edgeSet_add_add (β : ℝ≥0) (x y c : LatticeSite 2) :
    tau (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β) (x + c) (y + c) =
      tau (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β) x y :=
  tau_eq_of_map_law (Equiv.addRight c)
    (law_intensityProfile_map_eq _ _ (fun e => indicator_edgeSet_map_add c e) β) x y

/-! ### A crossing joins the two sides -/

/-- **Union bound for a crossing.** The probability of a left-right crossing of the box
`[0, n + 1] × [0, n]` is at most the sum of the two-point function over pairs of vertices of
its left and right sides. -/
theorem law_crossing_zero_le_sum_tau (q : Sym2 (LatticeSite 2) → unitInterval) (n : ℕ) :
    law q (crossing 0 (0 : LatticeSite 2) (0 + ![(n : ℤ) + 1, n])) ≤
      ∑ i ∈ Finset.Icc (0 : ℤ) n, ∑ j ∈ Finset.Icc (0 : ℤ) n,
        tau q ![0, i] ![(n : ℤ) + 1, j] := by
  have hsub : crossing 0 (0 : LatticeSite 2) (0 + ![(n : ℤ) + 1, n]) ⊆
      ⋃ i ∈ Finset.Icc (0 : ℤ) n, ⋃ j ∈ Finset.Icc (0 : ℤ) n,
        conn (![0, i] : LatticeSite 2) ![(n : ℤ) + 1, j] := by
    rintro ω ⟨a, ha, ha0, b, hb, hb0, hab⟩
    rw [mem_Icc_two_iff] at ha hb
    simp only [Pi.zero_apply, Pi.add_apply, zero_add, Matrix.cons_val_zero,
      Matrix.cons_val_one] at ha hb ha0 hb0
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
    refine ⟨a 1, ⟨by omega, by omega⟩, b 1, ⟨by omega, by omega⟩, ?_⟩
    have h := conn_mono inter_subset_left (localConn_subset_conn _ a b hab)
    rwa [eq_vec_two a, eq_vec_two b, ha0, hb0] at h
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _))

/-! ### The susceptibility at `log 2` -/

/-- **The column sums at the self-dual point.** At intensity `log 2`, the two-point function
summed over the vertices `(n + 1, k)`, `|k| ≤ n`, is at least `1/(2(n + 1))`. -/
theorem half_le_mul_sum_tau_log_two (n : ℕ) :
    (1 / 2 : ℝ≥0∞) ≤ ((n : ℝ≥0∞) + 1) * ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      tau (intensityProfile ((zdGraph 2).edgeSet.indicator 1) (Real.log 2).toNNReal) 0
        ![(n : ℤ) + 1, k] := by
  set q := intensityProfile ((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0))
    (Real.log 2).toNNReal with hq
  have hhalf : law q (crossing 0 (0 : LatticeSite 2) (0 + ![(n : ℤ) + 1, n])) = 1 / 2 :=
    law_crossing_zero_eq_half 0 n fun e he => intensityProfile_indicator_edgeSet_log_two he
  -- translate each pair so that its left end is the origin
  have htrans : ∀ i j : ℤ, tau q ![0, i] ![(n : ℤ) + 1, j] = tau q 0 ![(n : ℤ) + 1, j - i] := by
    intro i j
    have h := tau_intensityProfile_indicator_edgeSet_add_add (Real.log 2).toNNReal 0
      ![(n : ℤ) + 1, j - i] ![0, i]
    rw [zero_add, vec_two_add] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, sub_add_cancel] at h
    exact h
  -- each left vertex sees the column through `|k| ≤ n`
  have hinner : ∀ i ∈ Finset.Icc (0 : ℤ) n,
      ∑ j ∈ Finset.Icc (0 : ℤ) n, tau q 0 ![(n : ℤ) + 1, j - i] ≤
        ∑ k ∈ Finset.Icc (-(n : ℤ)) n, tau q 0 ![(n : ℤ) + 1, k] := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [← Finset.sum_image (g := fun j => j - i) (f := fun k => tau q 0 ![(n : ℤ) + 1, k])
      fun x _ y _ h => by simpa using h]
    refine Finset.sum_le_sum_of_subset fun k hk => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    rw [Finset.mem_Icc] at hj ⊢
    omega
  calc (1 / 2 : ℝ≥0∞) = law q (crossing 0 (0 : LatticeSite 2) (0 + ![(n : ℤ) + 1, n])) :=
        hhalf.symm
    _ ≤ ∑ i ∈ Finset.Icc (0 : ℤ) n, ∑ j ∈ Finset.Icc (0 : ℤ) n,
          tau q ![0, i] ![(n : ℤ) + 1, j] := law_crossing_zero_le_sum_tau q n
    _ = ∑ i ∈ Finset.Icc (0 : ℤ) n, ∑ j ∈ Finset.Icc (0 : ℤ) n,
          tau q 0 ![(n : ℤ) + 1, j - i] := by
        simp only [htrans]
    _ ≤ ∑ _i ∈ Finset.Icc (0 : ℤ) n, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          tau q 0 ![(n : ℤ) + 1, k] := Finset.sum_le_sum hinner
    _ = ((n : ℝ≥0∞) + 1) * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, tau q 0 ![(n : ℤ) + 1, k] := by
        rw [Finset.sum_const, Int.card_Icc, sub_zero,
          show ((n : ℤ) + 1).toNat = n + 1 by omega, nsmul_eq_mul]
        push_cast
        rfl

/-- The column sums are bounded by the susceptibility. -/
theorem sum_range_sum_tau_le_chi (q : Sym2 (LatticeSite 2) → unitInterval) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.Icc (-(n : ℤ)) n, tau q 0 ![(n : ℤ) + 1, k] ≤
      chi q 0 := by
  set g : ℕ × ℤ → LatticeSite 2 := fun p => ![(p.1 : ℤ) + 1, p.2] with hg
  have hginj : Function.Injective g := by
    intro p p' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [hg, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext (by exact_mod_cast (add_left_inj 1).1 h0) h1
  calc ∑ n ∈ Finset.range N, ∑ k ∈ Finset.Icc (-(n : ℤ)) n, tau q 0 ![(n : ℤ) + 1, k]
      ≤ ∑ n ∈ Finset.range N, ∑ k ∈ Finset.Icc (-(N : ℤ)) N, tau q 0 (g (n, k)) := by
        refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum_of_subset fun k hk => ?_
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hk ⊢
        omega
    _ = ∑ p ∈ Finset.range N ×ˢ Finset.Icc (-(N : ℤ)) N, tau q 0 (g p) :=
        (Finset.sum_product _ _ (fun p => tau q 0 (g p))).symm
    _ ≤ ∑' p, tau q 0 (g p) := ENNReal.sum_le_tsum _
    _ ≤ ∑' y, tau q 0 y := ENNReal.tsum_comp_le_tsum_of_injective hginj _
    _ = chi q 0 := (chi_eq_tsum_tau q 0).symm

/-- **The susceptibility is infinite at the self-dual point.** For nearest-neighbour bond
percolation on `ℤ²` at intensity `log 2` (edge probability `1/2`), the expected size of the
cluster of every vertex is infinite. -/
theorem chi_intensityProfile_indicator_edgeSet_log_two_eq_top (x : LatticeSite 2) :
    chi (intensityProfile ((zdGraph 2).edgeSet.indicator 1) (Real.log 2).toNNReal) x = ⊤ := by
  set q := intensityProfile ((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0))
    (Real.log 2).toNNReal with hq
  rw [chi_eq_of_transitive _ indicator_edgeSet_transitive _ x 0]
  by_contra hne
  set S : ℕ → ℝ≥0∞ := fun n => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, tau q 0 ![(n : ℤ) + 1, k]
    with hS
  have hSne : ∀ n, S n ≠ ⊤ := fun n =>
    ENNReal.sum_ne_top.2 fun k _ => ((tau_le_one q _ _).trans_lt ENNReal.one_lt_top).ne
  -- `(n + 1) S(n) ≥ 1/2`, in real numbers
  have hlow : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 2 * (S n).toReal := by
    intro n
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (hSne n))
      (half_le_mul_sum_tau_log_two n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)] at h
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at h
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- the partial sums of `S` are bounded by the susceptibility
  have hsum : ∀ N, ∑ n ∈ Finset.range N, (S n).toReal ≤ (chi q 0).toReal := by
    intro N
    rw [← ENNReal.toReal_sum fun n _ => hSne n]
    exact ENNReal.toReal_mono hne (sum_range_sum_tau_le_chi q N)
  -- the harmonic series diverges
  obtain ⟨N, hN⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
    (2 * (chi q 0).toReal)).exists
  have h2 : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ≤
      2 * ∑ n ∈ Finset.range N, (S n).toReal := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => hlow n
  linarith [hsum N]

/-! ### The threshold -/

/-- **Kesten's bound, root form.** For nearest-neighbour bond percolation on `ℤ²` the critical
intensity is at most `log 2`: `p_c(ℤ²) ≤ 1/2`. -/
theorem rootCriticalIntensity_indicator_edgeSet_le_log_two (x : LatticeSite 2) :
    rootCriticalIntensity ((zdGraph 2).edgeSet.indicator 1) x ≤ ENNReal.ofReal (Real.log 2) := by
  by_contra h
  rw [not_le] at h
  have hlt := chi_lt_top_of_lt_rootCriticalIntensity ((zdGraph 2).edgeSet.indicator 1)
    indicator_edgeSet_transitive summable_indicator_edgeSet (β := (Real.log 2).toNNReal) h
  rw [chi_intensityProfile_indicator_edgeSet_log_two_eq_top] at hlt
  exact lt_irrefl _ hlt

/-- **Kesten's bound, global form.** -/
theorem globalCriticalIntensity_indicator_edgeSet_le_log_two :
    globalCriticalIntensity ((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0)) ≤
      ENNReal.ofReal (Real.log 2) := by
  rw [← rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive _
    indicator_edgeSet_transitive 0]
  exact rootCriticalIntensity_indicator_edgeSet_le_log_two 0

/-! ### Percolation above one half -/

/-- **Percolation above one half, quantitatively.** For every intensity `β > log 2` (edge
probability `1 - e^{-β} > 1/2`), the cluster of every vertex is infinite with probability at
least `1 - log 2 / β`. -/
theorem one_sub_div_le_law_cluster_infinite_indicator_edgeSet {β : ℝ≥0}
    (hβ : Real.log 2 < β) (x : LatticeSite 2) :
    1 - ENNReal.ofReal (Real.log 2) / β ≤
      law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)
        {ω | (cluster ω x).Infinite} := by
  have hc := rootCriticalIntensity_indicator_edgeSet_le_log_two x
  have hlt : ENNReal.ofReal (Real.log 2) < β := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff ((Real.log_pos one_lt_two).trans hβ)).2 hβ
  refine le_trans ?_ (one_sub_div_le_law_cluster_infinite _ indicator_edgeSet_transitive
    summable_indicator_edgeSet (hc.trans_lt hlt))
  exact tsub_le_tsub_left (ENNReal.div_le_div_right hc _) 1

/-- **Percolation above one half.** For every intensity `β > log 2` (edge probability
`1 - e^{-β} > 1/2`), the cluster of every vertex is infinite with positive probability. -/
theorem law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt {β : ℝ≥0}
    (hβ : Real.log 2 < β) (x : LatticeSite 2) :
    0 < law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)
      {ω | (cluster ω x).Infinite} := by
  refine lt_of_lt_of_le ?_ (one_sub_div_le_law_cluster_infinite_indicator_edgeSet hβ x)
  rw [tsub_pos_iff_lt]
  refine ENNReal.div_lt_of_lt_mul ?_
  rw [one_mul, ← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff ((Real.log_pos one_lt_two).trans hβ)).2 hβ

/-! ### Non-vacuity -/

/-- The hypothesis of the percolation statements holds: `1 > log 2`, so nearest-neighbour bond
percolation on `ℤ²` at intensity `1` (edge probability `1 - e^{-1} ≈ 0.63`) percolates. -/
example : 0 < law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) 1)
    {ω | (cluster ω (0 : LatticeSite 2)).Infinite} :=
  law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt
    (by
      rw [NNReal.coe_one]
      have := Real.log_lt_sub_one_of_pos two_pos (by norm_num)
      linarith) 0

end PercLib.Models.Planar
