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
public import PercLib.Models.LongRange.InfiniteVolumeRusso
public import PercLib.Probability.Coordinate
public import PercLib.Percolation.Bond.MomentDerivativeTruncated
public import PercLib.Percolation.Bond.Susceptibility
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

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

/-! ### The arithmetic of the cap -/

open PercLib.Probability

variable {V : Type*} [Countable V]

/-! ### Monotonicity of the cluster in the pair -/

omit [Countable V] in
/-- Closing (or rather restricting to) the pair `e` can only shrink the cluster of `o`: the
configuration `ω \ {e}` is a subconfiguration of `insert e ω`. -/
theorem encard_cluster_sdiff_le_insert (ω : Config V) (e : Sym2 V) (o : V) :
    (cluster (ω \ {e}) o).encard ≤ (cluster (insert e ω) o).encard :=
  Set.encard_mono (cluster_mono (Set.sdiff_subset.trans (Set.subset_insert e ω)) o)

omit [Countable V] in
/-- The cast form used below: the `ℝ≥0∞` cluster volumes are ordered the same way. -/
theorem encard_cluster_sdiff_le_insert_coe (ω : Config V) (e : Sym2 V) (o : V) :
    ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤ ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
  by exact_mod_cast encard_cluster_sdiff_le_insert ω e o

/-- **The cap in additive form.** For `y ≤ x` and any cap `c`,
`min c x - min c y = min c x - y` in `ℝ≥0∞` (truncated subtraction). Consequently the capped
increment is monotone in `c`, which is what a monotone convergence argument needs. -/
theorem min_tsub_min_eq {x y c : ℝ≥0∞} (hyx : y ≤ x) :
    min c x - min c y = min c x - y := by
  rcases le_total y c with hyc | hcy
  · rw [min_eq_right hyc]
  · rw [min_eq_left hcy, min_eq_left (hcy.trans hyx), tsub_self, tsub_eq_zero_iff_le.mpr hcy]

/-- The capped pivotal increment is monotone in the cap. -/
theorem monotone_tsub_min {x y : ℝ≥0∞} (hyx : y ≤ x) :
    Monotone fun c : ℝ≥0∞ => min c x - min c y := by
  intro c d hcd
  change min c x - min c y ≤ min d x - min d y
  rw [min_tsub_min_eq hyx, min_tsub_min_eq hyx]
  exact tsub_le_tsub_right (min_le_min_right x hcd) y

/-- Supremum over natural caps: `⨆ n, min n x = x`. -/
theorem iSup_min_natCast (x : ℝ≥0∞) : (⨆ n : ℕ, min (n : ℝ≥0∞) x) = x := by
  refine le_antisymm (iSup_le fun n => min_le_right _ _) ?_
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [show (⨆ n : ℕ, min (n : ℝ≥0∞) ⊤) = ⨆ n : ℕ, (n : ℝ≥0∞) from
      iSup_congr fun n => min_eq_left le_top]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact le_iSup_of_le n (le_min hn.le le_rfl)

/-- **The capped pivotal increments increase to the uncapped one.** -/
theorem iSup_pivotal_truncation (x y : ℝ≥0∞) (hyx : y ≤ x) :
    (⨆ n : ℕ, (min (n : ℝ≥0∞) x - min (n : ℝ≥0∞) y)) = x - y := by
  rw [iSup_congr fun n => min_tsub_min_eq hyx, ← ENNReal.iSup_sub, iSup_min_natCast]

/-- The capped pivotal increment is monotone in the cap, for natural caps. -/
theorem monotone_pivotal_truncation (x y : ℝ≥0∞) (hyx : y ≤ x) :
    Monotone fun n : ℕ => min (n : ℝ≥0∞) x - min (n : ℝ≥0∞) y :=
  fun m n hmn => monotone_tsub_min hyx (by exact_mod_cast hmn)

/-! ### Measurability -/

/-- The cluster volume of `o` after inserting the pair `e` is measurable in `ω`. -/
theorem measurable_encard_cluster_insert_coe (e : Sym2 V) (o : V) :
    Measurable fun ω : Config V => ((cluster (insert e ω) o).encard : ℝ≥0∞) :=
  Measurable.of_discrete.comp
    ((measurable_encard_cluster (x := o)).comp (measurable_insert e))

/-- The cluster volume of `o` after deleting the pair `e` is measurable in `ω`. -/
theorem measurable_encard_cluster_sdiff_coe (e : Sym2 V) (o : V) :
    Measurable fun ω : Config V => ((cluster (ω \ {e}) o).encard : ℝ≥0∞) :=
  Measurable.of_discrete.comp
    ((measurable_encard_cluster (x := o)).comp (measurable_diff_singleton e))

/-- The capped pivotal increment is measurable. -/
theorem measurable_pivotal_truncation (e : Sym2 V) (o : V) (p n : ℕ) :
    Measurable fun ω : Config V =>
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) :=
  ((measurable_const.min ((measurable_encard_cluster_insert_coe e o).pow_const p)).sub
    (measurable_const.min ((measurable_encard_cluster_sdiff_coe e o).pow_const p)))

/-! ### Flux convergence in `ℝ≥0∞` -/

/-- **Main theorem: the capped pivotal flux converges to the uncapped one.**

For any measure `μ` on bond configurations, any pair `e`, root `o` and exponent `p`, the
pivotal integrals of the capped moments `min (n) (|K_o| ^ p)` increase to the pivotal integral of
`|K_o| ^ p`. No boundedness, no dominator, no cluster finiteness: the statement is in `ℝ≥0∞` and
the truncated subtraction makes the degenerate infinite-cluster case consistent (both sides are
then `0`). -/
theorem tendsto_lintegral_pivotal_truncation (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (p : ℕ) :
    Tendsto (fun n : ℕ => ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      atTop (𝓝 (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)) := by
  have hyx : ∀ ω : Config V, ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  have hmono : Monotone fun n : ℕ => ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
    fun m n hmn => lintegral_mono fun ω => monotone_pivotal_truncation _ _ (hyx ω) hmn
  have hsup : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)
      = ⨆ n : ℕ, ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ := by
    rw [← MeasureTheory.lintegral_iSup
      (f := fun n ω => (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)))
      (fun n => measurable_pivotal_truncation e o p n)
      (fun m n hmn ω => monotone_pivotal_truncation _ _ (hyx ω) hmn)]
    exact lintegral_congr fun ω => (iSup_pivotal_truncation _ _ (hyx ω)).symm
  simpa only [← hsup] using tendsto_atTop_iSup hmono

omit [Countable V] in
/-- **The cap-independent bound.** The capped pivotal flux is dominated by the uncapped pivotal
flux: the natural dominator for the truncation limit is the full flux itself. -/
theorem lintegral_pivotal_truncation_le (μ : Measure (Config V)) (e : Sym2 V) (o : V)
    (p n : ℕ) :
    (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      ≤ ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
  refine lintegral_mono fun ω => ?_
  have hyx : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  exact (le_iSup (fun m : ℕ => (min (m : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
    min (m : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))) n).trans_eq
    (iSup_pivotal_truncation _ _ hyx)

/-- **Window flux convergence.** For a finite set `S` of pairs with nonnegative weights `c`, the
window flux of the capped moments converges to the window flux of the uncapped moments. -/
theorem tendsto_lintegral_sum_pivotal_truncation (μ : Measure (Config V))
    (S : Finset (Sym2 V)) (c : Sym2 V → ℝ≥0) (o : V) (p : ℕ) :
    Tendsto (fun n : ℕ => ∑ e ∈ S, (c e : ℝ≥0∞) * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      atTop (𝓝 (∑ e ∈ S, (c e : ℝ≥0∞) * ∫⁻ ω,
        (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)) := by
  refine tendsto_finsetSum _ fun e _ => ?_
  have hg : Tendsto (fun x : ℝ≥0∞ => (c e : ℝ≥0∞) * x)
      (𝓝 (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ))
      (𝓝 ((c e : ℝ≥0∞) * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)) :=
    (ENNReal.continuous_const_mul (a := (c e : ℝ≥0∞)) (by simp)).tendsto _
  exact hg.comp (tendsto_lintegral_pivotal_truncation μ e o p)


/-! ### The real form -/

omit [Countable V] in
/-- The `ℝ≥0∞` pivotal increment is bounded by the cap. -/
theorem pivotal_truncation_le_cap (x y : ℝ≥0∞) (n : ℕ) :
    min (n : ℝ≥0∞) x - min (n : ℝ≥0∞) y ≤ (n : ℝ≥0∞) :=
  (tsub_le_self).trans (min_le_left _ _)

omit [Countable V] in
/-- The uncapped pivotal increment is finite almost surely when the inserted cluster is. -/
theorem pivotal_truncation_lt_top_of_ne_top {ω : Config V} {e : Sym2 V} {o : V} {p : ℕ}
    (h : ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤) :
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) < ⊤ :=
  lt_of_le_of_lt tsub_le_self (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 h))

/-- Measurability of the uncapped pivotal increment. -/
theorem measurable_pivotal (e : Sym2 V) (o : V) (p : ℕ) :
    Measurable fun ω : Config V => (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) :=
  ((measurable_encard_cluster_insert_coe e o).pow_const p).sub
    ((measurable_encard_cluster_sdiff_coe e o).pow_const p)

/-- **Real form of the flux convergence.** The capped pivotal fluxes of `|K_o| ^ p`, viewed as
real numbers, converge to the pivotal flux of `|K_o| ^ p`.

The hypotheses are explicit and are exactly the ones under which the `ℝ≥0∞` identity of
`tendsto_lintegral_pivotal_truncation` is the difference of two finite real moments:

* `[IsFiniteMeasure μ]`;
* `hfin : μ`-almost surely the cluster of `o` after inserting `e` is finite (the cluster of `o`
  after deleting `e` is then finite too, since it is contained in it);
* `hflux`: the uncapped pivotal flux is finite. This is the `p`-th moment hypothesis of
  Lemma I.4.1 in the form in which the flux consumes it; it is not automatic and is not hidden.

Nothing is assumed about vertices other than `o` and the endpoints of `e`. -/
theorem tendsto_integral_pivotal_truncation (μ : Measure (Config V)) [IsFiniteMeasure μ]
    (e : Sym2 V) (o : V) (p : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ => ∫ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ)
      atTop (𝓝 (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ)) := by
  have hyx : ∀ ω : Config V, ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  -- each capped flux is finite
  have hne : ∀ n : ℕ, (∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω =>
      pivotal_truncation_le_cap _ _ n)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ univ)
  have hreal := (ENNReal.tendsto_toReal_iff hne hflux).2
    (tendsto_lintegral_pivotal_truncation μ e o p)
  -- identify the limit
  have hlim : (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂μ)
      = ((∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ)).toReal :=
    (integral_toReal (measurable_pivotal e o p).aemeasurable
      (hfin.mono fun ω h => pivotal_truncation_lt_top_of_ne_top h))
  rw [hlim]
  refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hreal
  exact (integral_toReal ((measurable_pivotal_truncation e o p n).aemeasurable)
    (Eventually.of_forall fun ω => lt_of_le_of_lt
      (pivotal_truncation_le_cap _ _ n) (by simp))).symm


/-! ### Non-vacuity -/

/-- **Non-vacuity witness.** On `Bool` with the Dirac law at the empty configuration, `p = 1`,
`e = {false, true}` and `o = false`, both hypotheses of
`tendsto_integral_pivotal_truncation` hold: `Bool` is finite, so the cluster of `o` is a finite set
and its `encard` is not `⊤`; the uncapped pivotal flux is then finite by
`pivotal_truncation_lt_top_of_ne_top`. The conclusion, a genuine real convergence statement with a
nonzero limit, is therefore not vacuous. -/
example :
    Tendsto (fun n : ℕ => ∫ ω : Config Bool,
        (min (n : ℝ≥0∞) (((cluster (insert (s(false, true)) ω) false).encard : ℝ≥0∞) ^ 1) -
          min (n : ℝ≥0∞) (((cluster (ω \ {s(false, true)}) false).encard : ℝ≥0∞) ^ 1)).toReal
        ∂(Measure.dirac (∅ : Config Bool))) atTop
      (𝓝 (∫ ω : Config Bool,
        (((cluster (insert (s(false, true)) ω) false).encard : ℝ≥0∞) ^ 1 -
          ((cluster (ω \ {s(false, true)}) false).encard : ℝ≥0∞) ^ 1).toReal
        ∂(Measure.dirac (∅ : Config Bool)))) := by
  refine tendsto_integral_pivotal_truncation _ (s(false, true)) false 1 ?_ ?_
  · filter_upwards with ω
    simpa using (Set.toFinite (cluster (insert (s(false, true)) ω) false))
  · rw [lintegral_dirac]
    exact ne_of_lt (pivotal_truncation_lt_top_of_ne_top
      (by simpa using (Set.toFinite (cluster (insert (s(false, true)) ∅) false))))

end PercLib.Percolation.Bond

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Analysis

variable {a b M : ℝ}

/-- **Exact capped increment.** For `b ≥ 0` the increment of `x ↦ min x M` across
`a ↦ a + b` is the part of `b` that fits under the cap:
`min (a + b) M - min a M = min b (max 0 (M - a))`. -/
theorem min_add_sub_min_eq_min_sup_zero (hb : 0 ≤ b) :
    min (a + b) M - min a M = min b (max 0 (M - a)) := by
  rcases le_total M a with hMa | haM
  · have h1 : min (a + b) M = M := min_eq_right (by linarith)
    have h2 : min a M = M := min_eq_right hMa
    have h3 : max 0 (M - a) = 0 := max_eq_left (by linarith)
    have h4 : min b 0 = 0 := min_eq_right hb
    rw [h1, h2, h3, h4]
    ring
  · have h1 : min a M = a := min_eq_left haM
    have h3 : max 0 (M - a) = M - a := max_eq_right (by linarith)
    rw [h1, h3]
    rcases le_total (M - a) b with hle | hle
    · have h5 : min (a + b) M = M := min_eq_right (by linarith)
      have h6 : min b (M - a) = M - a := min_eq_right hle
      rw [h5, h6]
    · have h5 : min (a + b) M = a + b := min_eq_left (by linarith)
      have h6 : min b (M - a) = b := min_eq_left hle
      rw [h5, h6]
      ring

/-- **Off the cap the truncation is exact.** If `a + b ≤ M` then
`min (a + b) M - min a M = b`; the capped pivotal increment already equals the untruncated
one. -/
theorem min_add_sub_min_eq_of_add_le (hb : 0 ≤ b) (h : a + b ≤ M) :
    min (a + b) M - min a M = b := by
  rw [min_add_sub_min_eq_min_sup_zero hb]
  exact min_eq_left (le_max_of_le_right (by linarith))

/-- **Monotonicity in the cap.** The capped increment increases with the cap when `b ≥ 0`. -/
theorem monotone_min_add_sub_min (hb : 0 ≤ b) :
    Monotone fun M => min (a + b) M - min a M := by
  intro M M' hMM'
  change min (a + b) M - min a M ≤ min (a + b) M' - min a M'
  rw [min_add_sub_min_eq_min_sup_zero hb, min_add_sub_min_eq_min_sup_zero hb]
  exact min_le_min_left b (max_le_max le_rfl (by linarith))

/-- **Exact merge identity.** `a` times the capped increment of `x ↦ min x M` is
`min a M` times `min b (max 0 (M - a))`. This is the exact form of
`PercLib.Analysis.mul_min_add_sub_min_le`, whose right-hand side `min a M * min b M` is
genuinely larger when `0 < a` and `M < a + b`. -/
theorem mul_min_add_sub_min_eq (hb : 0 ≤ b) :
    a * (min (a + b) M - min a M) = min a M * min b (max 0 (M - a)) := by
  have hid := min_add_sub_min_eq_min_sup_zero (a := a) (b := b) (M := M) hb
  rcases le_total M a with hMa | haM
  · have h2 : min a M = M := min_eq_right hMa
    have h3 : max 0 (M - a) = 0 := max_eq_left (by linarith)
    have h4 : min b 0 = 0 := min_eq_right hb
    rw [hid, h2, h3, h4, mul_zero, mul_zero]
  · have h2 : min a M = a := min_eq_left haM
    rw [hid, h2]

/-- The exact merge identity implies the merge inequality
`PercLib.Analysis.mul_min_add_sub_min_le` for `M ≥ 0`. -/
theorem mul_min_add_sub_min_le_of_eq (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) :
    a * (min (a + b) M - min a M) ≤ min a M * min b M := by
  rw [mul_min_add_sub_min_eq hb]
  exact mul_le_mul_of_nonneg_left (min_le_min_left b (max_le hM (by linarith))) (le_min ha hM)

/-- **Exact capped increment of `p`-th powers.** For nonnegative `a`, `b` the increment of
`x ↦ min (x ^ p) M` across `a ↦ a + b` is the part of the untruncated increment
`(a + b) ^ p - a ^ p` that fits under the cap. This is the `p`-th power form of
`min_add_sub_min_eq_min_sup_zero`, i.e. the pointwise statement behind the truncation step of
Lemma I.4.1's right-hand side. -/
theorem min_pow_sub_min_pow_eq (p : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min ((a + b) ^ p) M - min (a ^ p) M =
      min ((a + b) ^ p - a ^ p) (max 0 (M - a ^ p)) := by
  have hb' : (0 : ℝ) ≤ (a + b) ^ p - a ^ p := by
    have : a ^ p ≤ (a + b) ^ p := pow_le_pow_left₀ ha (by linarith) p
    linarith
  have hid := min_add_sub_min_eq_min_sup_zero (a := a ^ p) (b := (a + b) ^ p - a ^ p)
    (M := M) hb'
  rwa [show a ^ p + ((a + b) ^ p - a ^ p) = (a + b) ^ p by ring] at hid

/-- **The power-capped increment is dominated by the untruncated one.** Uniformly in the cap
`M`: this is the `p`-th power dominator for the flux of the untruncated moment, whose
untruncated value is `(a + b) ^ p - a ^ p`. -/
theorem min_pow_sub_min_pow_le (p : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (M : ℝ) :
    min ((a + b) ^ p) M - min (a ^ p) M ≤ (a + b) ^ p - a ^ p := by
  rw [min_pow_sub_min_pow_eq p ha hb]
  exact min_le_left _ _

/-- **Caps below the minimal cluster volume are degenerate.** Two cluster volumes are at
least `1`, so every cap `M ≤ 1` (negative ones included) truncates both `min (a + b) M` and
`min a M` to `M`, and the increment is `0`. -/
theorem min_add_sub_min_eq_zero_of_one_le (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : M ≤ 1) :
    min (a + b) M - min a M = 0 := by
  rw [min_eq_right (by linarith), min_eq_right (by linarith)]
  ring

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **The capped pivotal increment is monotone in the cap.** The real expression is the one
occurring in the integrand of `hasDerivAt_integral_fun_of_transitive` at
`h = fun x => min x M`. -/
theorem capped_pivotal_mono (ω : Config V) (o y : V) :
    Monotone fun M : ℝ =>
      min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
        min ((cluster ω o).ncard : ℝ) M :=
  PercLib.Analysis.monotone_min_add_sub_min (Nat.cast_nonneg _)

/-- **The untruncated far cluster volume dominates every capped pivotal increment.** For
every cap `M ≥ 0` the capped increment of the cluster volume of `o` across the union with the
cluster of `y` is nonnegative and at most the cluster volume of `y`, uniformly in `M`. This is
the dominator needed to pass capped flux integrals to the untruncated one. On a finite vertex
type `ncard` is the cardinality, so this is the finite-`V` Russo integrand; on an infinite
cluster both sides collapse to `0` because `ncard` is then `0` (see
`ncard_cluster_univ_nat`), which is why infinite-volume statements use `encard`. -/
theorem capped_pivotal_nonneg_le (ω : Config V) (o y : V) (M : ℝ) :
    0 ≤ min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
        min ((cluster ω o).ncard : ℝ) M ∧
      min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
        min ((cluster ω o).ncard : ℝ) M ≤ ((cluster ω y).ncard : ℝ) := by
  rw [PercLib.Analysis.min_add_sub_min_eq_min_sup_zero (Nat.cast_nonneg _)]
  exact ⟨le_min (Nat.cast_nonneg _) (le_max_left 0 _), min_le_left _ _⟩

/-- **Above the sum of the two cluster volumes the cap does not bind.** -/
theorem capped_pivotal_eq_of_add_le (ω : Config V) (o y : V) {M : ℝ}
    (h : ((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ) ≤ M) :
    min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
      min ((cluster ω o).ncard : ℝ) M = ((cluster ω y).ncard : ℝ) :=
  PercLib.Analysis.min_add_sub_min_eq_of_add_le (Nat.cast_nonneg _) h

/-- **A cap at most `1` gives a vanishing pivotal increment.** Every cluster contains its
base vertex, so a finite cluster volume is at least `1`. Consequently the
capped derivative of the first moment is `0` for every cap `M ≤ 1`, and the capped
derivatives can only converge to the untruncated one along `M → ∞`. -/
theorem capped_pivotal_eq_zero_of_cap_le_one (ω : Config V) (o y : V)
    (ho : (cluster ω o).Finite) (hy : (cluster ω y).Finite) {M : ℝ} (hM : M ≤ 1) :
    min (((cluster ω o).ncard : ℝ) + ((cluster ω y).ncard : ℝ)) M -
      min ((cluster ω o).ncard : ℝ) M = 0 := by
  have ho' : (1 : ℝ) ≤ (cluster ω o).ncard :=
    Nat.one_le_cast.2 ((Set.ncard_pos ho).2 ⟨o, mem_cluster_self ω o⟩)
  have hy' : (1 : ℝ) ≤ (cluster ω y).ncard :=
    Nat.one_le_cast.2 ((Set.ncard_pos hy).2 ⟨y, mem_cluster_self ω y⟩)
  exact PercLib.Analysis.min_add_sub_min_eq_zero_of_one_le ho' hy' hM

/-! ### Truncated susceptibility in `ℝ≥0∞` -/

/-- **Capped expected cluster volume increases to the susceptibility.** For every bond law on
a countable vertex type and every vertex `x`, the integer caps recover `chi` in `ℝ≥0∞`
without any finiteness hypothesis; `chi = ∞` is allowed, and then no finite real first moment
exists. -/
theorem iSup_lintegral_min_encard [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    (⨆ n : ℕ, ∫⁻ ω, min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞) ∂(law q)) = chi q x := by
  have hsup : ∀ y : ℝ≥0∞, (⨆ n : ℕ, min y (n : ℝ≥0∞)) = y := by
    intro y
    refine le_antisymm (ciSup_le fun n => min_le_left _ _) ?_
    by_cases hy : y = ⊤
    · subst hy
      rw [show (fun n : ℕ => min (⊤ : ℝ≥0∞) (n : ℝ≥0∞)) = fun n : ℕ => (n : ℝ≥0∞) from by
        funext n; simp]
      exact le_of_eq ENNReal.iSup_natCast.symm
    · have hy' : y ≤ ((⌈y.toNNReal⌉₊ : ℕ) : ℝ≥0∞) := by
        have h1 : y.toNNReal ≤ ⌈y.toNNReal⌉₊ := Nat.le_ceil _
        have h2 : ((y.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((⌈y.toNNReal⌉₊ : ℕ) : ℝ≥0∞) := by
          exact_mod_cast h1
        rwa [ENNReal.coe_toNNReal hy] at h2
      calc y = min y ((⌈y.toNNReal⌉₊ : ℕ) : ℝ≥0∞) := (min_eq_left hy').symm
        _ ≤ ⨆ n : ℕ, min y (n : ℝ≥0∞) := le_iSup (fun n : ℕ => min y (n : ℝ≥0∞)) _
  have hmeas_enc : Measurable fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞) := by
    have h := encard_cluster_eq_tsum (V := V) (x := x)
    simp only [h]
    exact Measurable.tsum fun y => measurable_const.indicator (measurableSet_conn x y)
  have hmono : Monotone fun n : ℕ => (fun ω : Config V =>
      min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞)) :=
    fun n n' h ω => min_le_min_left _ (by exact_mod_cast h)
  calc (⨆ n : ℕ, ∫⁻ ω, min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞) ∂(law q))
      = ∫⁻ ω, ⨆ n : ℕ, min ((cluster ω x).encard : ℝ≥0∞) (n : ℝ≥0∞) ∂(law q) :=
        (lintegral_iSup (fun n => hmeas_enc.min measurable_const) hmono).symm
    _ = ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂(law q) := by simp only [hsup]
    _ = chi q x := rfl

/-! ### The cap limit fails at intensity one on `ℕ` -/

/-- With every pair open, the cluster of every vertex is all of `ℕ`. -/
theorem cluster_univ_nat (x : ℕ) : cluster (Set.univ : Config ℕ) x = Set.univ := by
  ext y
  simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]

/-- **The infinite cluster has `ncard = 0`.** The `Set.ncard` of the infinite cluster at
intensity `1` on `ℕ` is zero, so a formalisation reading cluster volumes through `ncard`
sees a cluster of volume `0` — and a capped moment `0` for every cap — instead of an
infinite one. -/
theorem ncard_cluster_univ_nat (x : ℕ) : (cluster (Set.univ : Config ℕ) x).ncard = 0 := by
  rw [cluster_univ_nat]
  exact Set.infinite_univ.ncard

/-- The same cluster has full `encard`. -/
theorem encard_cluster_univ_nat (x : ℕ) :
    ((cluster (Set.univ : Config ℕ) x).encard : ℝ≥0∞) = ⊤ := by
  rw [cluster_univ_nat]
  simp

/-- At intensity `1` on `ℕ` the capped expected cluster volume equals the cap, so it
diverges in `ℝ≥0∞`: there is no finite first moment and hence no dominator of the capped
derivatives. -/
theorem lintegral_min_encard_nat (M : ℝ≥0∞) :
    ∫⁻ ω, min ((cluster ω (0 : ℕ)).encard : ℝ≥0∞) M ∂(law (fun _ : Sym2 ℕ => 1)) = M := by
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := cluster_univ_nat 0
  simp [law, PercLib.Probability.prodBernoulli_const, hc]

/-- Consequently `chi` is infinite there: the finite-dominator hypothesis is not merely
convenient at intensity `1` on `ℕ`, it fails. -/
theorem chi_nat_eq_top : chi (fun _ : Sym2 ℕ => 1) 0 = ∞ := by
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := cluster_univ_nat 0
  simp [chi, law, PercLib.Probability.prodBernoulli_const, hc]

/-! ### Non-vacuity -/

/-- The exact identity at concrete numbers where the cap binds. -/
example : min ((1 : ℝ) + 5) 2 - min 1 2 = min 5 (max 0 (2 - 1)) := by
  norm_num

/-- The untruncated increment is genuinely lost by a small cap: for two clusters of size `1`
and cap `1` the pivotal increment is `0`, while the untruncated increment is `1`. -/
example : min ((1 : ℝ) + 1) 1 - min 1 1 = 0 := by
  norm_num

/-- The bond-model domination statement is non-vacuous on the two-vertex set with no open
pair: both clusters are singletons, so the increment is bounded by `1`. -/
example : min (((cluster (∅ : Config Bool) false).ncard : ℝ) +
      ((cluster (∅ : Config Bool) true).ncard : ℝ)) 1 -
      min ((cluster (∅ : Config Bool) false).ncard : ℝ) 1 ≤
    ((cluster (∅ : Config Bool) true).ncard : ℝ) :=
  (capped_pivotal_nonneg_le (∅ : Config Bool) false true 1).2

end PercLib.Percolation.Bond


/-! ## Finite transitive Russo derivatives

The finite symmetric Russo formula also has the oriented form used in the binomial
expansion of Lemma I.4.1. These results use `ncard` on a finite vertex type; they are
not infinite-volume theorems. The cap monotonicity and cap-limit statements are
pointwise prerequisites for the missing infinite-volume argument.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- **Invariance of the oriented pivotal integral.** An intensity automorphism `σ` carries the
oriented flux integrand of the pair `(σ a, σ b)` to that of `(a, b)`. -/
theorem integral_oriented_invariant (J : Sym2 V → ℝ≥0) (σ : V ≃ V)
    (hσ : ∀ e, J (Sym2.map σ e) = J e) (h : ℝ → ℝ) (a b : V) :
    (∫ ω, (if ω ∈ conn (σ a) (σ b) then 0 else
        ((cluster ω (σ a)).ncard : ℝ) *
          (h (((cluster ω (σ a)).ncard : ℝ) + (cluster ω (σ b)).ncard) -
            h ((cluster ω (σ a)).ncard : ℝ))) ∂law (intensityProfile J 1)) =
      ∫ ω, (if ω ∈ conn a b then 0 else
        ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω a).ncard : ℝ))) ∂law (intensityProfile J 1) := by
  rw [← integral_image_sym2Map_of_invariant J σ hσ (fun ω =>
    (if ω ∈ conn (σ a) (σ b) then 0 else
      ((cluster ω (σ a)).ncard : ℝ) *
        (h (((cluster ω (σ a)).ncard : ℝ) + (cluster ω (σ b)).ncard) -
          h ((cluster ω (σ a)).ncard : ℝ))))]
  congr 1
  funext ω
  simp only [image_mem_conn_iff, cluster_image, Set.ncard_image_of_injective _ σ.injective]

open Classical in
/-- **The oriented Russo formula.** For a finite transitive intensity family `λ_u` with derivatives
`w` at `t`, and *any* `h : ℝ → ℝ`, the derivative of `u ↦ E_u h(|K_o|)` is

`∑_{y ≠ o} w(o,y) E_t[1{o ↮ y} |K_o| (h(|K_o| + |K_y|) - h(|K_o|))]`,

with coefficient `1` and only the root term: the shape used in Lemma I.4.1. -/
theorem hasDerivAt_integral_oriented_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ)
    (t : ℝ) (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (h : ℝ → ℝ) :
    HasDerivAt (fun u => ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1))
      (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard))) ∂law (intensityProfile (lam t) 1)) t := by
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨o⟩
  have hncard : ∀ (σ : V ≃ V) (ω : Config V) (x : V),
      (cluster (Sym2.map σ '' ω) (σ x)).ncard = (cluster ω x).ncard := by
    intro σ ω x
    rw [cluster_image, Set.ncard_image_of_injective _ σ.injective]
  have hroot : ∀ u (a : V), ∫ ω, h ((cluster ω a).ncard) ∂law (intensityProfile (lam u) 1) =
      ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1) := by
    intro u a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← integral_image_sym2Map_of_invariant (lam u) σ (hσ u)
      (fun ω => h ((cluster ω o).ncard))]
    congr 1
    funext ω
    rw [← hσa, hncard]
  have hfun : (fun u => ∫ ω, h ((cluster ω o).ncard) ∂law (intensityProfile (lam u) 1)) =
      fun u => (Fintype.card V : ℝ)⁻¹ *
        ∫ ω, ∑ v, h ((cluster ω v).ncard) ∂law (intensityProfile (lam u) 1) := by
    funext u
    rw [integral_finsetSum _ fun v _ => Integrable.of_finite]
    simp_rw [hroot u]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hV.ne', one_mul]
  rw [hfun]
  refine ((hasDerivAt_integral_sum_cluster_fun lam w t hlam h).const_mul _).congr_deriv ?_
  set μ := law (intensityProfile (lam t) 1)
  set G : V → V → ℝ := fun a b => ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
        h ((cluster ω a).ncard : ℝ))) ∂μ with hG
  set G2 : V → V → ℝ := fun a b => ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω b).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
        h ((cluster ω b).ncard : ℝ))) ∂μ with hG2
  -- splitting the symmetric integrand into the two oriented halves
  have hsplit : ∀ a b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω a).ncard : ℝ)) +
        ((cluster ω b).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω b).ncard : ℝ))) ∂μ = w s(a, b) * (G a b + G2 a b) := by
    intro a b
    simp only [hG, hG2]
    congr 1
    rw [← integral_add Integrable.of_finite Integrable.of_finite]
    congr 1
    funext ω
    by_cases hc : ω ∈ conn a b <;> simp [hc]
  -- swapping the two halves over the ordered pairs only uses symmetry of `w`
  have hswap : ∀ a b, G2 b a = G a b := by
    intro a b
    simp only [hG, hG2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hc : ω ∈ conn b a
    · have hc' : ω ∈ conn a b := by simpa only [conn_symm] using hc
      simp only [hc, hc', ↓reduceIte]
    · have hc' : ω ∉ conn a b := by simpa only [conn_symm] using hc
      simp only [hc, hc']
      rw [add_comm ((cluster ω b).ncard : ℝ) ((cluster ω a).ncard : ℝ)]
  have hG2sum : (∑ a, ∑ b, w s(a, b) * G2 a b) = ∑ a, ∑ b, w s(a, b) * G a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [hswap a b, Sym2.eq_swap]
  -- `w` and `G` are invariant under the intensity automorphisms
  have hw : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ e, w (Sym2.map σ e) = w e := by
    intro σ hσ e
    have h1 := hlam (Sym2.map σ e)
    simp_rw [hσ] at h1
    exact h1.unique (hlam e)
  have hGinv : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ a b, G (σ a) (σ b) = G a b := by
    intro σ hσ a b
    simp only [hG]
    exact integral_oriented_invariant (lam t) σ (hσ t) h a b
  have hwmk : ∀ (σ : V ≃ V), (∀ u e, lam u (Sym2.map σ e) = lam u e) →
      ∀ a b, w s(σ a, σ b) = w s(a, b) := by
    intro σ hσ a b
    have h1 := hw σ hσ s(a, b)
    rwa [Sym2.map_mk] at h1
  -- one row of the oriented pair sum does not depend on the root
  have hrow : ∀ a, ∑ b, w s(a, b) * G a b = ∑ b, w s(o, b) * G o b := by
    intro a
    obtain ⟨σ, hσa, hσ⟩ := hT a o
    rw [← hσa, ← Equiv.sum_comp σ (fun b => w s(σ a, b) * G (σ a) b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hwmk σ hσ a b, hGinv σ hσ a b]
  -- hence the whole pair sum is `|V|` times the root row
  have hGdiag : G o o = 0 := by simp [hG, conn_self]
  have hR : (∑ a, ∑ b, w s(a, b) * G a b) =
      (Fintype.card V : ℝ) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * G o y := by
    simp_rw [hrow]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ o), hGdiag, mul_zero, zero_add]
  have hS : (∑ a, ∑ b, w s(a, b) * ∫ ω, (if ω ∈ conn a b then 0 else
      ((cluster ω a).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω a).ncard : ℝ)) +
        ((cluster ω b).ncard : ℝ) * (h (((cluster ω a).ncard : ℝ) + (cluster ω b).ncard) -
          h ((cluster ω b).ncard : ℝ))) ∂μ) =
      (∑ a, ∑ b, w s(a, b) * G a b) + (∑ a, ∑ b, w s(a, b) * G2 a b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsplit a b, mul_add]
  rw [hS, hG2sum, hR]
  have hc : (Fintype.card V : ℝ) ≠ 0 := hV.ne'
  field_simp
  ring

/-! ### The coefficient check of I.4.1 -/

/-- **Coefficient check for (I.4.1).** With the root factor kept (the mass-transport form used in
I.4.1), the oriented power integrand expands with the binomial coefficients `binom(p,ℓ)`,
`ℓ = 0, …, p − 1`. This is the root-multiplied form of `add_pow_succ_sub_pow_sub_pow`
(`k = p − 1`), i.e. `A ((A+B)^p − A^p) = ∑_{ℓ<p} binom(p,ℓ) A^{ℓ+1} B^{p−ℓ}`. -/
theorem mul_add_pow_sub_pow (A B : ℝ) (p : ℕ) :
    A * ((A + B) ^ p - A ^ p) =
      ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ^ (ℓ + 1) * B ^ (p - ℓ) := by
  rw [mul_sub, add_pow, Finset.mul_sum, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
  rw [add_sub_cancel_right]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

open Classical in
/-- **I.4.1-shaped power formula.** For a finite transitive intensity family, the derivative of
`u ↦ E_u |K_o|^p` is the oriented (mass-transport) sum with the binomial coefficients of I.4.1,
`∑_{y ≠ o} w(o,y) E_t[1{o ↮ y} ∑_{ℓ<p} binom(p,ℓ) |K_o|^{ℓ+1} |K_y|^{p−ℓ}]`. -/
theorem hasDerivAt_moment_oriented_pow (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (p : ℕ) :
    HasDerivAt (fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ p
        ∂law (intensityProfile (lam u) 1))
      (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) *
          ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) * ((cluster ω y).ncard : ℝ) ^ (p - ℓ))
        ∂law (intensityProfile (lam t) 1)) t := by
  refine (hasDerivAt_integral_oriented_of_transitive lam w t hlam hT o
    (fun x => x ^ p)).congr_deriv ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hc : ω ∈ conn o y
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    exact mul_add_pow_sub_pow _ _ p

open Classical in
/-- **The I.4.1 binomial shape.** The oriented flux of `hasDerivAt_moment_oriented_pow`, rewritten
as in Lemma I.4.1: a sum over `ℓ < p` of `binom(p,ℓ)` times the expectation of `|K_o|^{ℓ+1}`
against the weighted, pivotal-restricted sum over `y` of `|K_y|^{p−ℓ}`. -/
theorem flux_oriented_eq_binomial (J : Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (o : V) (p : ℕ) :
    (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1)) =
      ∑ ℓ ∈ Finset.range p, ∫ ω, (((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ∑ y ∈ Finset.univ.erase o, (if ω ∈ conn o y then 0 else
          w s(o, y) * ((cluster ω y).ncard : ℝ) ^ (p - ℓ)))
        ∂law (intensityProfile J 1) := by
  -- pull the `ℓ`-sum out of the `y`-integral, then swap the two finite sums
  have h1 : ∀ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
      ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1)
      = ∑ ℓ ∈ Finset.range p, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1) := by
    intro y _
    have hsplit : (fun ω : Config V => if ω ∈ conn o y then (0 : ℝ) else
        ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) =
        fun ω : Config V => ∑ ℓ ∈ Finset.range p, (if ω ∈ conn o y then 0 else
          ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
            ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) := by
      funext ω
      by_cases hc : ω ∈ conn o y <;> simp [hc]
    rw [hsplit, integral_finsetSum _ fun ℓ _ => Integrable.of_finite, Finset.mul_sum]
  -- move the weight inside each integral
  have h2 : ∀ ℓ ∈ Finset.range p, (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω,
      (if ω ∈ conn o y then 0 else ((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ((cluster ω y).ncard : ℝ) ^ (p - ℓ)) ∂law (intensityProfile J 1))
      = ∑ y ∈ Finset.univ.erase o, ∫ ω, (if ω ∈ conn o y then 0 else
        w s(o, y) * (((p.choose ℓ : ℕ) : ℝ) * ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
          ((cluster ω y).ncard : ℝ) ^ (p - ℓ))) ∂law (intensityProfile J 1) := by
    intro ℓ _
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext ω
    by_cases hc : ω ∈ conn o y <;> simp [hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [h2 ℓ (by assumption)]
  rw [← integral_finsetSum _ fun y _ => Integrable.of_finite]
  congr 1
  funext ω
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hc : ω ∈ conn o y
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    ring

open Classical in
/-- **The I.4.1 RHS shape as a derivative.** Combining the oriented power formula with the binomial
rearrangement: in the finite transitive model the derivative of `E_u |K_o|^p` is the paper's
right-hand side, `∑_{ℓ<p} binom(p,ℓ) E_t[ |K_o|^{ℓ+1} ∑_{y ≠ o} w(o,y) 1(o ↮ y) |K_y|^{p−ℓ} ]`
(up to reading `w(o,y)` as the total weight `β|J'(r)| 1(‖o − y‖ ≤ r)` of the cut-off). -/
theorem hasDerivAt_moment_of_transitive_i41 (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (p : ℕ) :
    HasDerivAt (fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ p
        ∂law (intensityProfile (lam u) 1))
      (∑ ℓ ∈ Finset.range p, ∫ ω, (((p.choose ℓ : ℕ) : ℝ) *
          ((cluster ω o).ncard : ℝ) ^ (ℓ + 1) *
        ∑ y ∈ Finset.univ.erase o, (if ω ∈ conn o y then 0 else
          w s(o, y) * ((cluster ω y).ncard : ℝ) ^ (p - ℓ)))
        ∂law (intensityProfile (lam t) 1)) t :=
  (hasDerivAt_moment_oriented_pow lam w t hlam hT o p).congr_deriv
    (flux_oriented_eq_binomial (lam t) w o p)

open Classical in
/-- **The bounded truncated power.** For every cap `M`, the derivative of `u ↦ E_u min(|K_o|^p, M)`
is the oriented flux of the truncated integrand. This is the bounded object one differentiates
before letting `M → ∞`; no boundedness of `M` or of the moment is needed, only the cap. -/
theorem hasDerivAt_truncated_pow_oriented (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (p : ℕ) (M : ℝ) :
    HasDerivAt (fun u => ∫ ω, min (((cluster ω o).ncard : ℝ) ^ p) M
        ∂law (intensityProfile (lam u) 1))
      (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) *
          (min ((((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) ^ p) M -
            min (((cluster ω o).ncard : ℝ) ^ p) M))
        ∂law (intensityProfile (lam t) 1)) t :=
  hasDerivAt_integral_oriented_of_transitive lam w t hlam hT o (fun x => min (x ^ p) M)

omit [DecidableEq V] in
/-- **Scope marker: at finite `V` the cap is eventually irrelevant.** For `M ≥ |V|^p` the truncated
moment coincides with the untruncated one. This is recorded to delimit what the finite statements
above can and cannot do: at finite `V` the passage `M → ∞` is vacuous, so no theorem of this file
implies the infinite-volume `M → ∞` step, which needs a dominator there. -/
theorem truncated_pow_eq_pow_of_card_pow_le (lam : ℝ → Sym2 V → ℝ≥0) (o : V) (p : ℕ) {M : ℝ}
    (hM : (Fintype.card V : ℝ) ^ p ≤ M) :
    (fun u => ∫ ω, min (((cluster ω o).ncard : ℝ) ^ p) M ∂law (intensityProfile (lam u) 1)) =
      fun u => ∫ ω, ((cluster ω o).ncard : ℝ) ^ p ∂law (intensityProfile (lam u) 1) := by
  funext u
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hn : (cluster ω o).ncard ≤ Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_le_card (cluster ω o)
  refine min_eq_left (le_trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn) p) hM)

open Classical in
/-- **Coefficient consistency / mass transport.** The oriented formula (coefficient `1`, root term
only, as in I.4.1) and the library's symmetric formula (coefficient `1/2`, both terms) are two
values of the same derivative, hence equal. This is the mass-transport identity underlying the
step from Russo's formula to (I.4.1); in particular the paper's coefficient `1` is not a
normalisation slip for the library's `1/2`. -/
theorem oriented_eq_half_symm_of_transitive (lam : ℝ → Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (t : ℝ)
    (hlam : ∀ e, HasDerivAt (fun u => (lam u e : ℝ)) (w e) t)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ u e, lam u (Sym2.map σ e) = lam u e)
    (o : V) (h : ℝ → ℝ) :
    (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard))) ∂law (intensityProfile (lam t) 1)) =
      (1 / 2) * ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω o).ncard)) +
          ((cluster ω y).ncard : ℝ) * (h ((cluster ω o).ncard + (cluster ω y).ncard) -
            h ((cluster ω y).ncard))) ∂law (intensityProfile (lam t) 1) :=
  (hasDerivAt_integral_oriented_of_transitive lam w t hlam hT o h).unique
    (hasDerivAt_integral_fun_of_transitive lam w t hlam hT o h)

/-- The cap increment of an increasing pair is at most the untruncated increment. -/
theorem min_sub_min_le_sub {a b M : ℝ} (hab : a ≤ b) : min b M - min a M ≤ b - a := by
  rw [min_def, min_def]
  split_ifs <;> linarith

open Classical in
/-- **Flux domination.** With nonnegative derivative weights, the capped flux of
`hasDerivAt_truncated_pow_oriented` is dominated term by term by the untruncated flux of
`hasDerivAt_moment_oriented_pow` (whose integrand is the binomial sum of `mul_add_pow_sub_pow`).
This is the domination inequality needed to pass the derivative formula to the cap limit. -/
theorem truncated_flux_le_flux (J : Sym2 V → ℝ≥0) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (o : V) (p : ℕ) (M : ℝ) :
    (∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) *
          (min ((((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) ^ p) M -
            min (((cluster ω o).ncard : ℝ) ^ p) M))
        ∂law (intensityProfile J 1)) ≤
      ∑ y ∈ Finset.univ.erase o, w s(o, y) * ∫ ω, (if ω ∈ conn o y then 0 else
        ((cluster ω o).ncard : ℝ) *
          ((((cluster ω o).ncard : ℝ) + (cluster ω y).ncard) ^ p -
            ((cluster ω o).ncard : ℝ) ^ p))
        ∂law (intensityProfile J 1) := by
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hw _)
  refine integral_mono Integrable.of_finite Integrable.of_finite fun ω => ?_
  by_cases hc : ω ∈ conn o y
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact min_sub_min_le_sub (pow_le_pow_left₀ (by positivity)
      (le_add_of_nonneg_right (by positivity)) p)

/-! ### The cap passage `M → ∞` of the truncated flux term -/

/-- The cap increment of an increasing pair survives a larger cap. -/
theorem sub_min_sub_le {a b M M' : ℝ} (hab : a ≤ b) (hM : M ≤ M') :
    min a M' - min a M ≤ min b M' - min b M := by
  rw [min_def, min_def, min_def, min_def]
  split_ifs <;> linarith

/-- The truncated oriented flux term is nonnegative and increases with the cap. -/
theorem min_pow_sub_min_pow_mono {A B M M' : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) (hM : M ≤ M') :
    min ((A + B) ^ p) M - min (A ^ p) M ≤ min ((A + B) ^ p) M' - min (A ^ p) M' := by
  have hab : A ^ p ≤ (A + B) ^ p := pow_le_pow_left₀ hA (by linarith) p
  have h := sub_min_sub_le hab hM
  linarith

/-- The truncated oriented flux term is nonnegative. -/
theorem min_pow_sub_min_pow_nonneg {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    0 ≤ min ((A + B) ^ p) M - min (A ^ p) M := by
  have hab : A ^ p ≤ (A + B) ^ p := pow_le_pow_left₀ hA (by linarith) p
  have h := min_le_min_right M hab
  linarith

/-- **Monotone convergence input.** The truncated oriented flux term is monotone in the cap. -/
theorem monotone_min_pow_sub_min_pow {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    Monotone fun M : ℝ => min ((A + B) ^ p) M - min (A ^ p) M :=
  fun _ _ hM => min_pow_sub_min_pow_mono hA hB p hM

/-- **Cap limit.** As the cap grows, the truncated oriented flux term tends to the untruncated one,
i.e. the pointwise limit underlying the `M → ∞` passage from `min (|K_o|^p, M)` to `|K_o|^p`. -/
theorem tendsto_min_pow_sub_min_pow_atTop (A B : ℝ) (p : ℕ) :
    Tendsto (fun M : ℝ => min ((A + B) ^ p) M - min (A ^ p) M) atTop
      (𝓝 ((A + B) ^ p - A ^ p)) := by
  have h1 : Tendsto (fun M : ℝ => min ((A + B) ^ p) M) atTop (𝓝 ((A + B) ^ p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ((A + B) ^ p)] with M hM
    exact (min_eq_left hM).symm
  have h2 : Tendsto (fun M : ℝ => min (A ^ p) M) atTop (𝓝 (A ^ p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (A ^ p)] with M hM
    exact (min_eq_left hM).symm
  exact h1.sub h2

/-! ### Non-vacuity witness -/

open Classical in
/-- **Non-vacuity.** On `ZMod 2` with `λ_u = u⁺` (so `λ_u = u` near `t = 1`, `w = 1`) and the
translations as the transitive group, the hypotheses of the oriented power formula and of its
truncation hold, at `p = 2` and cap `1/2`. -/
example : ∃ D : ℝ, HasDerivAt (fun u : ℝ => ∫ ω,
      min (((cluster ω (0 : ZMod 2)).ncard : ℝ) ^ 2) (1 / 2)
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => u.toNNReal) 1)) D 1 ∧
    D = ∑ y ∈ Finset.univ.erase (0 : ZMod 2), (fun _ : Sym2 (ZMod 2) => (1 : ℝ)) s(0, y) *
      ∫ ω, (if ω ∈ conn 0 y then 0 else
        ((cluster ω (0 : ZMod 2)).ncard : ℝ) *
          (min ((((cluster ω (0 : ZMod 2)).ncard : ℝ) +
              (cluster ω y).ncard) ^ 2) (1 / 2) -
            min (((cluster ω (0 : ZMod 2)).ncard : ℝ) ^ 2) (1 / 2)))
        ∂law (intensityProfile (fun _ : Sym2 (ZMod 2) => (1 : ℝ).toNNReal) 1) := by
  refine ⟨_, hasDerivAt_truncated_pow_oriented (fun (u : ℝ) _ => u.toNNReal) (fun _ => 1) 1 ?_
    (fun x y => ⟨Equiv.addRight (y - x), by simp, fun _ _ => rfl⟩) 0 2 (1 / 2), rfl⟩
  intro e
  refine (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
  simp [Real.coe_toNNReal _ hu.le]

end PercLib.Percolation.Bond
