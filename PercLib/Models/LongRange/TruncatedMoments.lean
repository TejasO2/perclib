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
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Probability.MassTransportTuple
public import PercLib.Percolation.Bond.MomentDerivativeTruncated
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Models.HierarchicalCutoff
public import PercLib.Analysis.DominatedDerivative

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



/-! ## Exact one-edge cluster algebra


-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Loops -/

/-- Opening a diagonal pair does not change the open graph: adjacency in `openGraph` also
requires the two endpoints to be distinct. -/
theorem openGraph_insert_diag (ω : Config V) (a : V) :
    openGraph (insert s(a, a) ω) = openGraph ω := by
  refine SimpleGraph.ext ?_
  ext x y
  rw [openGraph_adj_iff, openGraph_adj_iff]
  by_cases hne : x = y
  · subst hne
    simp
  · have hne' : s(x, y) ≠ s(a, a) := by
      intro h
      have hd : (s(x, y)).IsDiag := h ▸ (Sym2.mk_isDiag_iff (x := a) (y := a)).2 rfl
      exact hne ((Sym2.mk_isDiag_iff (x := x) (y := y)).1 hd)
    have hiff : (s(x, y) ∈ insert s(a, a) ω) ↔ (s(x, y) ∈ ω) := by
      rw [mem_insert_iff]
      exact ⟨fun h => h.elim (fun heq => absurd heq hne') id, fun h => Or.inr h⟩
    rw [hiff]

/-- Opening a diagonal pair does not change the cluster of any vertex. -/
theorem cluster_insert_diag (ω : Config V) (a x : V) :
    cluster (insert s(a, a) ω) x = cluster ω x := by
  simp only [cluster, openGraph_insert_diag]

/-! ### The root-edge identity -/

open Classical in
/-- **The exact root-edge pivotal increment of a cluster moment.** Opening the pair
`s(o, y)` and counting the cluster of `o` by `encard` changes the `p`-th power of its
volume by `((|K_o| + |K_y|)^p - |K_o|^p)` when `o` and `y` were not connected, and by
nothing when they were. The subtraction is truncated, so if the cluster of `o` is
infinite both sides are `0`; no finiteness hypothesis is used. -/
theorem encard_cluster_insert_pow_sub_eq (ω : Config V) (o y : V) (p : ℕ) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p =
      if ω ∈ conn o y then 0
      else (((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p := by
  classical
  by_cases h : ω ∈ conn o y
  · have hKy : cluster ω y = cluster ω o := (cluster_eq_of_mem_conn h).symm
    have hno : cluster (insert s(o, y) ω) o = cluster ω o := by
      refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) o)
      intro z hz
      have hz' := cluster_insert_subset ω o y o hz
      simpa [hKy] using hz'
    rw [hno, ite_eq_left h, tsub_self]
  · have hdisj : Disjoint (cluster ω o) (cluster ω y) := by
      refine Set.disjoint_left.2 fun z hzo hzy => h ?_
      have hzy' : ω ∈ conn z y := by rwa [mem_cluster_iff, conn_symm] at hzy
      have hoz : ω ∈ conn o z := (mem_cluster_iff ω o z).1 hzo
      exact conn_trans hoz hzy'
    have hunion : cluster (insert s(o, y) ω) o = cluster ω o ∪ cluster ω y :=
      cluster_insert_of_mem ω o y o (Or.inl (mem_cluster_self ω o))
    rw [hunion, Set.encard_union_eq hdisj, ite_eq_right h, ENat.toENNReal_add]

/-! ### Pairs with one endpoint in the cluster -/

/-- If both endpoints of the pair `s(a, b)` are already in the cluster of `x`, opening it
does not change that cluster. Includes the loop case `a = b`. -/
theorem cluster_insert_eq_of_mem_of_mem {ω : Config V} {a b x : V}
    (ha : x ∈ cluster ω a) (hb : x ∈ cluster ω b) :
    cluster (insert s(a, b) ω) x = cluster ω x := by
  have hax : a ∈ cluster ω x := (mem_cluster_comm ω x a).2 ha
  have hbx : b ∈ cluster ω x := (mem_cluster_comm ω x b).2 hb
  refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) x)
  intro z hz
  rcases cluster_insert_subset ω a b x hz with (h | h) | h
  · exact h
  · rwa [← cluster_eq_of_mem_conn ((mem_cluster_iff ω x a).1 hax)] at h
  · rwa [← cluster_eq_of_mem_conn ((mem_cluster_iff ω x b).1 hbx)] at h

open Classical in
/-- **Exact increment, one endpoint in the cluster.** If `x` lies in the cluster of `a`
but not in the cluster of `b`, opening `s(a, b)` merges the two clusters and the `p`-th
power of the `encard` of the cluster of `x` (which is that of `a`) grows by
`((|K_a| + |K_b|)^p - |K_a|^p)`. -/
theorem encard_cluster_insert_pow_sub_eq_of_mem_of_not_mem {ω : Config V} {a b x : V}
    (p : ℕ) (ha : x ∈ cluster ω a) (hb : x ∉ cluster ω b) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p -
        ((cluster ω x).encard : ℝ≥0∞) ^ p =
      (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
        ((cluster ω a).encard : ℝ≥0∞) ^ p := by
  have hxK : cluster ω x = cluster ω a :=
    (cluster_eq_of_mem_conn ((mem_cluster_iff ω a x).1 ha)).symm
  have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
    refine Set.disjoint_left.2 fun z hza hzb => hb ?_
    have hax : ω ∈ conn x a := by
      rw [conn_symm]
      exact (mem_cluster_iff ω a x).1 ha
    have haz : ω ∈ conn a z := (mem_cluster_iff ω a z).1 hza
    have h1 : ω ∈ conn x z := conn_trans hax haz
    have h2 : ω ∈ conn z b := by rwa [mem_cluster_iff, conn_symm] at hzb
    have hxb : ω ∈ conn x b := conn_trans h1 h2
    rw [mem_cluster_iff, conn_symm]
    exact hxb
  have hunion : cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b :=
    cluster_insert_of_mem ω a b x (Or.inl ha)
  rw [hunion, Set.encard_union_eq hdisj, hxK, ENat.toENNReal_add]

open Classical in
/-- **Exact increment, the other endpoint in the cluster.** If `x` lies in the cluster of
`b` but not in the cluster of `a`, opening `s(a, b)` grows the `p`-th power of the
`encard` of the cluster of `x` (which is that of `b`) by
`((|K_a| + |K_b|)^p - |K_b|^p)`. -/
theorem encard_cluster_insert_pow_sub_eq_of_not_mem_of_mem {ω : Config V} {a b x : V}
    (p : ℕ) (ha : x ∉ cluster ω a) (hb : x ∈ cluster ω b) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p -
        ((cluster ω x).encard : ℝ≥0∞) ^ p =
      (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
        ((cluster ω b).encard : ℝ≥0∞) ^ p := by
  have hxK : cluster ω x = cluster ω b :=
    (cluster_eq_of_mem_conn ((mem_cluster_iff ω b x).1 hb)).symm
  have hdisj : Disjoint (cluster ω a) (cluster ω b) := by
    refine Set.disjoint_left.2 fun z hza hzb => ha ?_
    have hbx : ω ∈ conn x b := by
      rw [conn_symm]
      exact (mem_cluster_iff ω b x).1 hb
    have hbz : ω ∈ conn b z := (mem_cluster_iff ω b z).1 hzb
    have h1 : ω ∈ conn x z := conn_trans hbx hbz
    have h2 : ω ∈ conn z a := by rwa [mem_cluster_iff, conn_symm] at hza
    have hxa : ω ∈ conn x a := conn_trans h1 h2
    rw [mem_cluster_iff, conn_symm]
    exact hxa
  have hunion : cluster (insert s(a, b) ω) x = cluster ω a ∪ cluster ω b :=
    cluster_insert_of_mem ω a b x (Or.inr hb)
  rw [hunion, Set.encard_union_eq hdisj, hxK, ENat.toENNReal_add]

open Classical in
/-- **The four-case exact increment.** Opening the pair `s(a, b)` changes the `p`-th power
of the `encard` of the cluster of `x` by `0` when `x` is in both clusters or in neither,
and by the merge increment of the two clusters when `x` is in exactly one of them. -/
theorem encard_cluster_insert_pow_sub_eq_cases {ω : Config V} {a b x : V} (p : ℕ) :
    ((cluster (insert s(a, b) ω) x).encard : ℝ≥0∞) ^ p -
        ((cluster ω x).encard : ℝ≥0∞) ^ p =
      if x ∈ cluster ω a then
        (if x ∈ cluster ω b then 0
         else (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
           ((cluster ω a).encard : ℝ≥0∞) ^ p)
      else
        (if x ∈ cluster ω b then
          (((cluster ω a).encard : ℝ≥0∞) + ((cluster ω b).encard : ℝ≥0∞)) ^ p -
            ((cluster ω b).encard : ℝ≥0∞) ^ p
         else 0) := by
  by_cases ha : x ∈ cluster ω a
  · by_cases hb : x ∈ cluster ω b
    · rw [cluster_insert_eq_of_mem_of_mem ha hb, tsub_self]
      simp only [ha, hb, ↓reduceIte]
    · rw [encard_cluster_insert_pow_sub_eq_of_mem_of_not_mem p ha hb]
      simp only [ha, hb, ↓reduceIte]
  · by_cases hb : x ∈ cluster ω b
    · rw [encard_cluster_insert_pow_sub_eq_of_not_mem_of_mem p ha hb]
      simp only [ha, hb, ↓reduceIte]
    · rw [PercLib.Models.LongRange.cluster_insert_eq_of_forall_not_mem (ω := ω) (o := x)
        (e := s(a, b)) ?_, tsub_self]
      · simp only [ha, hb, ↓reduceIte]
      · intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with hza | hzb
        · subst hza
          exact fun h => ha ((mem_cluster_comm ω x z).1 h)
        · subst hzb
          exact fun h => hb ((mem_cluster_comm ω x z).1 h)

/-! ### The insertion/deletion form used by the derivative -/

open Classical in
/-- **The exact pivotal increment of the derivative integrand.** The function differentiated
by Russo's formula is `F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard`.
For `e = s(o, y)` and `F = (· ^ p)` this is the same root-edge identity, with `ω` replaced
by `ω \ {e}`: inserting into the configuration with `e` deleted is inserting into `ω`. -/
theorem encard_cluster_insert_pow_sub_sdiff_eq (ω : Config V) (o y : V) (p : ℕ) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p =
      if (ω \ {s(o, y)}) ∈ conn o y then 0
      else (((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) +
          ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞)) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p := by
  rw [← Set.insert_sdiff_singleton (s := ω) (a := s(o, y))]
  exact encard_cluster_insert_pow_sub_eq (ω \ {s(o, y)}) o y p

open Classical in
/-- **The first-moment increment is at most the far cluster volume.** For `p = 1` the
root-edge identity gives that opening `s(o, y)` increases the `encard` of the cluster of
`o` by at most `|K_y|`, and by nothing when `o` and `y` are already connected. No
finiteness hypothesis is used: the truncated subtraction `⊤ - ⊤ = 0` only makes the
bound easier. -/
theorem encard_cluster_insert_sub_le (ω : Config V) (o y : V) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) - ((cluster ω o).encard : ℝ≥0∞) ≤
      if ω ∈ conn o y then 0 else ((cluster ω y).encard : ℝ≥0∞) := by
  have h := encard_cluster_insert_pow_sub_eq ω o y 1
  simp only [pow_one] at h
  rw [h]
  by_cases hc : ω ∈ conn o y
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact tsub_le_iff_right.2 (le_of_eq (add_comm _ _))

open Classical in
/-- **The first-moment increment is exactly the far cluster volume when the root cluster is
finite.** With `|K_o| ≠ ⊤` the truncation does not bite and the increment of the `encard`
of the cluster of `o` is exactly `|K_y|` off the connection event, and `0` on it. The
finiteness hypothesis is necessary: for an infinite cluster of `o` the increment is `⊤ - ⊤
= 0` while `|K_y|` may be nonzero. -/
theorem encard_cluster_insert_sub_eq_of_ne_top (ω : Config V) (o y : V)
    (ho : ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) - ((cluster ω o).encard : ℝ≥0∞) =
      if ω ∈ conn o y then 0 else ((cluster ω y).encard : ℝ≥0∞) := by
  have h := encard_cluster_insert_pow_sub_eq ω o y 1
  simp only [pow_one] at h
  rw [h]
  by_cases hc : ω ∈ conn o y
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact (ENNReal.cancel_of_ne ho).add_tsub_cancel_left

/-! ### The capped increment -/

open Classical in
/-- **The capped increment is dominated by the uncapped exact flux.** For every cap `M`,
truncating the `p`-th powers at `M` cannot increase the pivotal increment of the root-edge
identity. This is the pointwise form of the domination used to pass the capped flux
integrals to the uncapped one; it is cap-independent on the right-hand side. -/
theorem min_encard_cluster_insert_pow_sub_le (ω : Config V) (o y : V) (p : ℕ) (M : ℝ≥0∞) :
    min M (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p) -
        min M (((cluster ω o).encard : ℝ≥0∞) ^ p) ≤
      if ω ∈ conn o y then 0
      else (((cluster ω o).encard : ℝ≥0∞) + ((cluster ω y).encard : ℝ≥0∞)) ^ p -
        ((cluster ω o).encard : ℝ≥0∞) ^ p := by
  by_cases h : ω ∈ conn o y
  · have hKy : cluster ω y = cluster ω o := (cluster_eq_of_mem_conn h).symm
    have hno : cluster (insert s(o, y) ω) o = cluster ω o := by
      refine Subset.antisymm ?_ (cluster_mono (subset_insert _ _) o)
      intro z hz
      have hz' := cluster_insert_subset ω o y o hz
      simpa [hKy] using hz'
    rw [hno, ite_eq_left h, tsub_self]
  · rw [ite_eq_right h]
    have hmain := encard_cluster_insert_pow_sub_eq ω o y p
    rw [ite_eq_right h] at hmain
    rw [← hmain]
    have hvol : ((cluster ω o).encard : ℝ≥0∞) ≤
        ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) := by
      exact_mod_cast Set.encard_mono (cluster_mono (subset_insert _ _) o)
    have hyx : ((cluster ω o).encard : ℝ≥0∞) ^ p ≤
        ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p :=
      pow_le_pow_left' hvol p
    rw [min_tsub_min_eq hyx]
    have hmin : min M (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p) ≤
        ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p :=
      min_le_right M (((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p)
    exact tsub_le_tsub_right hmin _

/-! ### The real form -/

open Classical in
/-- **The real form of the exact pivotal increment.** If the cluster of `o` after opening
`s(o, y)` and the cluster of `y` after deleting it are both finite, then the real
difference of the `p`-th powers of the corresponding `encard`s is the real merge increment
`((|K_o| + |K_y|)^p - |K_o|^p)`, and `0` when `o` and `y` are already connected. The
finiteness hypotheses are explicit and necessary: on an infinite cluster the truncated
`ℝ≥0∞` subtraction is `0`, which no real difference reproduces. -/
theorem encard_cluster_insert_pow_sub_sdiff_eq_real (ω : Config V) (o y : V) (p : ℕ)
    (hX : ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hB : ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞) ≠ ⊤) :
    ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞).toReal ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal ^ p =
      if (ω \ {s(o, y)}) ∈ conn o y then 0
      else ((((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal +
          ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞).toReal) ^ p -
        ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞).toReal ^ p) := by
  have hA : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top hX (encard_cluster_sdiff_le_insert_coe ω (s(o, y)) o)
  have hAB : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) +
      ((cluster (ω \ {s(o, y)}) y).encard : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hA, hB⟩
  have hXA : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ≤
      ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) :=
    encard_cluster_sdiff_le_insert_coe ω (s(o, y)) o
  have hYX : ((cluster (ω \ {s(o, y)}) o).encard : ℝ≥0∞) ^ p ≤
      ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p :=
    pow_le_pow_left' hXA p
  have hXp : ((cluster (insert s(o, y) ω) o).encard : ℝ≥0∞) ^ p ≠ ⊤ :=
    ENNReal.pow_ne_top hX
  rw [← ENNReal.toReal_pow, ← ENNReal.toReal_pow,
    ← ENNReal.toReal_sub_of_le hYX hXp, encard_cluster_insert_pow_sub_sdiff_eq]
  by_cases h : (ω \ {s(o, y)}) ∈ conn o y
  · simp only [h, ite_eq_left, ENNReal.toReal_zero]
  · simp only [h, ↓reduceIte]
    rw [ENNReal.toReal_sub_of_le (pow_le_pow_left' (le_add_right le_rfl) p)
      (ENNReal.pow_ne_top hAB), ENNReal.toReal_pow, ENNReal.toReal_add hA hB]

/-! ### The exact binomial (far-cluster) expansion -/

/-- **The pivotal increment as a far-cluster binomial sum.** For finite cluster volumes
`A = |K_o|` and `B = |K_y|`, the merge increment of the `p`-th power is the binomial sum
`∑_{ℓ<p} C(p, ℓ) A^ℓ B^{p-ℓ}`: the `ℓ = 0` term is the pure far-cluster term `B^p`, and
every other term carries a power of the far cluster volume. This is the un-multiplied
companion of `mul_pow_sub_pow_eq_sum_choose_ennreal` (which keeps the mass-transport factor
`|K_o|`), and the exact form of the binomial step of Lemma I.4.1 at one edge. -/
theorem pow_add_sub_pow_eq_sum_choose_ennreal {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (p : ℕ) :
    (A + B) ^ p - A ^ p =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * A ^ ℓ * B ^ (p - ℓ) := by
  have ha : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hdiff : 0 ≤ (A.toReal + B.toReal) ^ p - A.toReal ^ p := by
    have hle : A.toReal ^ p ≤ (A.toReal + B.toReal) ^ p :=
      pow_le_pow_left₀ ha (by linarith) p
    linarith
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
    ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ A.toReal + B.toReal),
    ← ENNReal.ofReal_pow ha,
    ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ A.toReal ^ p)]
  rw [← PercLib.Probability.sum_choose_mul_pow_eq_pow_sub]
  rw [ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by positivity)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

end PercLib.Percolation.Bond



/-! ## The infinite pair sum in the truncated Russo flux


-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.Analysis

/-! ### Commuting a monotone `ℕ`-supremum with `∑'` -/

/-- **A supremum over a monotone `ℕ`-family commutes with a finite sum.** -/
theorem iSup_finset_sum_of_monotone {ι : Type*} (s : Finset ι) (f : ℕ → ι → ℝ≥0∞)
    (hmono : ∀ e ∈ s, Monotone fun n => f n e) :
    (⨆ n, ∑ e ∈ s, f n e) = ∑ e ∈ s, ⨆ n, f n e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hmono' : ∀ e ∈ s, Monotone fun n => f n e :=
      fun e he => hmono e (Finset.mem_insert_of_mem he)
    have hsum : Monotone fun n => ∑ e ∈ s, f n e :=
      fun m n hmn => Finset.sum_le_sum fun e he => hmono' e he hmn
    have step : (⨆ n, ∑ e ∈ insert a s, f n e) = ⨆ n, (f n a + ∑ e ∈ s, f n e) :=
      iSup_congr fun n => Finset.sum_insert ha
    rw [step, Finset.sum_insert ha,
      ← ENNReal.iSup_add_iSup_of_monotone (hmono a (Finset.mem_insert_self a s)) hsum,
      ih hmono']

/-- **A supremum over a monotone `ℕ`-family commutes with `∑'`.**

For `f n e` monotone in `n` for every `e`,
`⨆ n, ∑' e, f n e = ∑' e, ⨆ n, f n e`. No summability is involved: both sides are `ℝ≥0∞`. -/
theorem iSup_tsum_of_monotone {ι : Type*} [Countable ι] (f : ℕ → ι → ℝ≥0∞)
    (hmono : ∀ e, Monotone fun n => f n e) :
    (⨆ n, ∑' e, f n e) = ∑' e, ⨆ n, f n e := by
  calc (⨆ n, ∑' e, f n e) = ⨆ n, ⨆ s : Finset ι, ∑ e ∈ s, f n e :=
        iSup_congr fun n => ENNReal.tsum_eq_iSup_sum
    _ = ⨆ s : Finset ι, ⨆ n, ∑ e ∈ s, f n e := iSup_comm
    _ = ⨆ s : Finset ι, ∑ e ∈ s, ⨆ n, f n e :=
        iSup_congr fun s => iSup_finset_sum_of_monotone s f fun e _ => hmono e
    _ = ∑' e, ⨆ n, f n e := (ENNReal.tsum_eq_iSup_sum).symm

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The pair sum and the measure integral -/

/-- **Tonelli for the pivotal flux of `|K_o|^p`.** For any measure on bond configurations, any
pair weight `c : Sym2 V → ℝ≥0∞`, root `o` and exponent `p`, the integral of the weighted pair sum
of pivotal increments is the weighted pair sum of the integrals.

Nothing is assumed about `c`, about the number of pairs with `c e ≠ 0`, about cluster finiteness,
or about finiteness of the sums: the pivotal increments are `ℝ≥0∞`-valued, and the truncated
subtraction makes the degenerate infinite-cluster case consistent. -/
theorem lintegral_tsum_pivotal_flux (μ : Measure (Config V)) (c : Sym2 V → ℝ≥0∞) (o : V)
    (p : ℕ) :
    ∫⁻ ω, ∑' e, c e * (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ
      = ∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
  rw [lintegral_tsum]
  · exact tsum_congr fun e => lintegral_const_mul (c e) (measurable_pivotal e o p)
  · exact fun e => (measurable_const.mul (measurable_pivotal e o p)).aemeasurable

/-- **The truncation cap can be removed through the infinite weighted pair sum.**

For any measure on bond configurations, any pair weight `c`, root `o` and exponent `p`, the
supremum over the cap `n` of the infinite weighted sums of capped pivotal integrals of `|K_o|^p` is
the infinite weighted sum of the uncapped pivotal integrals.

This monotone argument does not require a summable majorant over the pairs. The unit-weight
witness `tsum_pivotal_flux_eq_top_of_dirac` shows why such a majorant cannot be taken for
granted independently of the model's weights and finite-support restriction. -/
theorem iSup_tsum_lintegral_pivotal_truncation (μ : Measure (Config V)) (c : Sym2 V → ℝ≥0∞)
    (o : V) (p : ℕ) :
    (⨆ n : ℕ, ∑' e, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
  -- the monotonicity in the configuration
  have hyx : ∀ (ω : Config V) (e : Sym2 V),
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω e => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  -- the monotonicity in the cap, for each pair
  have hmono : ∀ e : Sym2 V, Monotone fun n : ℕ => c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ := by
    intro e m n hmn
    refine mul_le_mul_of_nonneg_left (lintegral_mono fun ω => ?_) zero_le
    exact monotone_pivotal_truncation _ _ (hyx ω e) hmn
  -- the cap limit for each pair
  have hper : ∀ e : Sym2 V, (⨆ n : ℕ, ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
    intro e
    rw [← lintegral_iSup (fun n => measurable_pivotal_truncation e o p n)
      (fun m n hmn ω => monotone_pivotal_truncation _ _ (hyx ω e) hmn)]
    exact lintegral_congr fun ω => iSup_pivotal_truncation _ _ (hyx ω e)
  calc (⨆ n : ℕ, ∑' e, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ)
      = ∑' e, ⨆ n : ℕ, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
        PercLib.Analysis.iSup_tsum_of_monotone _ hmono
    _ = ∑' e, c e * ⨆ n : ℕ, ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
        tsum_congr fun e => (ENNReal.mul_iSup _ _).symm
    _ = ∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ := by
        exact tsum_congr fun e => by rw [hper e]

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The real form: the finiteness that is *not* free -/

/-- **Real form of the cap limit through the infinite weighted pair sum.**

If the total uncapped weighted pivotal flux is finite, then the `ℝ≥0∞` cap limit of
`iSup_tsum_lintegral_pivotal_truncation` is a limit of finite `ℝ≥0∞` numbers and can be read in
`ℝ`. The hypothesis `htot` is not a leftover: `tsum_lintegral_pivotal_flux_dirac_eq_top` shows it
fails for this Dirac measure with all pair weights equal to `1`, even though every cluster is
finite and every moment is finite there. It is therefore *not* implied by a.e. finiteness of
clusters, nor by finiteness of any cluster moment. -/
theorem tendsto_toReal_tsum_lintegral_pivotal_truncation (μ : Measure (Config V))
    (c : Sym2 V → ℝ≥0∞) (o : V) (p : ℕ)
    (htot : (∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ => (∑' e, c e * ∫⁻ ω,
        (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal)
      atTop (𝓝 ((∑' e, c e * ∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ).toReal)) := by
  have hyx : ∀ (ω : Config V) (e : Sym2 V),
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p ≤
        ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p :=
    fun ω e => ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)
  have hmono : Monotone fun n : ℕ => ∑' e, c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ :=
    fun m n hmn => ENNReal.tsum_le_tsum fun e =>
      mul_le_mul_of_nonneg_left (lintegral_mono fun ω =>
        monotone_pivotal_truncation _ _ (hyx ω e) hmn) zero_le
  have hsup := iSup_tsum_lintegral_pivotal_truncation μ c o p
  have hne : ∀ n : ℕ, (∑' e, c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ) ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (hsup ▸ htot) (hsup ▸ le_iSup (fun n : ℕ => ∑' e, c e * ∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ) n)
  refine (ENNReal.tendsto_toReal_iff hne htot).2 ?_
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-! ### The total uncapped pair flux is infinite at the Dirac law

The next two results answer the question "is the finiteness hypothesis of
`tendsto_toReal_tsum_lintegral_pivotal_truncation` automatic?". It is not, and the failure is not
a formality: at the Dirac law on the empty configuration of `ℤ^d` the cluster of every vertex is
the singleton of that vertex, so every cluster is finite, every moment is finite and the model is
as degenerate as it can be, yet the total pivotal flux over *all* pairs is `⊤` because the
infinitely many pairs at the origin are each pivotal. -/

/-- At the empty configuration, inserting a pair `s(0, y)` with `y ≠ 0` adds `y` to the cluster of
`0`, so the `p`-th power of the cluster volume rises from `1` to at least `2`: the pivotal
increment is at least `1`. -/
theorem one_le_pivotal_flux_dirac (d : ℕ) (p : ℕ) (hp : 1 ≤ p) {y : Fin d → ℤ}
    (hy : y ≠ 0) :
    1 ≤ (((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p -
        ((cluster ((∅ : Config (Fin d → ℤ)) \ {s(0, y)}) 0).encard : ℝ≥0∞) ^ p) := by
  have hmem : y ∈ cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0 := by
    refine SimpleGraph.Adj.reachable ?_
    rw [openGraph_adj_iff]
    exact ⟨by simp, fun h => hy h.symm⟩
  have hsub : ({0, y} : Set (Fin d → ℤ)) ⊆
      cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0 := by
    intro z hz
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · rw [hz]; exact mem_cluster_self _ _
    · rw [Set.mem_singleton_iff.1 hz]; exact hmem
  have hpair : (2 : ℝ≥0∞) ≤
      ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) := by
    have h := Set.encard_le_encard hsub
    rw [Set.encard_pair (Ne.symm hy)] at h
    exact ENat.toENNReal_mono h
  have hbase : ((cluster ((∅ : Config (Fin d → ℤ)) \ {s(0, y)}) 0).encard : ℝ≥0∞) ^ p = 1 := by
    have hset : cluster ((∅ : Config (Fin d → ℤ)) \ {s(0, y)}) 0 = {0} := by
      rw [Set.empty_sdiff, cluster_empty]
    rw [hset]
    simp
  have hpow : (2 : ℝ≥0∞) ≤
      ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p := by
    calc (2 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ≥0∞) ^ p := pow_le_pow_right₀ (by norm_num) hp
      _ ≤ ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p :=
          ENNReal.pow_le_pow_left hpair
  rw [hbase]
  have hmono : (2 : ℝ≥0∞) - 1 ≤
      ((cluster (insert (s(0, y)) (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p - 1 :=
    tsub_le_tsub_right hpow 1
  rw [show (2 : ℝ≥0∞) - 1 = 1 by
    rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num, ENNReal.add_sub_cancel_left (by simp)]
    ] at hmono
  exact hmono

/-- **The total uncapped pivotal flux is infinite at the empty configuration of `ℤ^d`.**

For `d ≥ 1`, `p ≥ 1`, the sum over all pairs of the pivotal increment of `|K_0|^p` at `ω = ∅` is
`⊤`: the pairs `s(0, y)`, `y ≠ 0`, are infinitely many and each contributes at least `1`. In
particular this Dirac unit-weight example rules out a nonnegative summable majorant for the
unit-weight all-pairs sum. It is not a statement about a cut-off long-range law or its weights. -/
theorem tsum_pivotal_flux_eq_top_of_dirac (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    (∑' e : Sym2 (Fin d → ℤ),
      (((cluster (insert e (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p -
        ((cluster ((∅ : Config (Fin d → ℤ)) \ {e}) 0).encard : ℝ≥0∞) ^ p)) = ⊤ := by
  classical
  let i : Fin d := ⟨0, hd⟩
  have hne : ∀ n : ℕ, Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1) ≠ 0 := by
    intro n h
    have hval := congrFun h i
    rw [Function.update_self, Pi.zero_apply] at hval
    omega
  have hinj : Function.Injective fun n : ℕ =>
      s(0, Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1)) := by
    intro m n hmn
    have h1 : Function.update (0 : Fin d → ℤ) i ((m : ℤ) + 1) =
        Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1) := by
      rcases (Sym2.mk_eq_mk_iff (p := (0, Function.update (0 : Fin d → ℤ) i ((m : ℤ) + 1)))
        (q := (0, Function.update (0 : Fin d → ℤ) i ((n : ℤ) + 1)))).1 hmn with h | h
      · exact congrArg Prod.snd h
      · exact absurd (congrArg Prod.fst h).symm (hne n)
    have hval := congrFun h1 i
    rw [Function.update_self, Function.update_self] at hval
    omega
  have hstep : (∑' n : ℕ, (1 : ℝ≥0∞)) ≤ ∑' e : Sym2 (Fin d → ℤ),
      (((cluster (insert e (∅ : Config (Fin d → ℤ))) 0).encard : ℝ≥0∞) ^ p -
        ((cluster ((∅ : Config (Fin d → ℤ)) \ {e}) 0).encard : ℝ≥0∞) ^ p) := by
    refine le_trans (ENNReal.tsum_le_tsum fun n => ?_)
      (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
    exact one_le_pivotal_flux_dirac d p hp (hne n)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (c := (1 : ℝ≥0∞)) one_ne_zero] at hstep
  exact top_le_iff.1 hstep

/-- **The finiteness hypothesis of the real cap limit fails at a law with finite clusters.**

At the Dirac law on the empty configuration of `ℤ^d`, `d ≥ 1`, the total weighted pivotal flux with
all pair weights `1` is `⊤` (`tsum_pivotal_flux_eq_top_of_dirac` read through the Dirac integral),
while the `p`-th moment of the cluster volume is `1`
(`lintegral_encard_cluster_pow_dirac`). So a.e. finiteness of clusters and finiteness of the
cluster moment do not make the total pair flux finite. -/
theorem tsum_lintegral_pivotal_flux_dirac_eq_top (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    (∑' e : Sym2 (Fin d → ℤ), (1 : ℝ≥0∞) * ∫⁻ ω : Config (Fin d → ℤ),
      (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p)
        ∂Measure.dirac (∅ : Config (Fin d → ℤ))) = ⊤ := by
  simpa using tsum_pivotal_flux_eq_top_of_dirac d hd p hp

/-- The `p`-th moment of the cluster volume at the Dirac law on the empty configuration is `1`, in
particular finite. -/
theorem lintegral_encard_cluster_pow_dirac (d : ℕ) (p : ℕ) :
    ∫⁻ ω : Config (Fin d → ℤ), ((cluster ω 0).encard : ℝ≥0∞) ^ p
      ∂Measure.dirac (∅ : Config (Fin d → ℤ)) = 1 := by
  rw [lintegral_dirac, cluster_empty]
  simp

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

/-! ### Non-vacuity of the real cap limit

The finiteness hypothesis of `tendsto_toReal_tsum_lintegral_pivotal_truncation` is satisfiable, and
the convergence it asserts is not a statement about a zero sequence: on `Bool` at the Dirac law on
the empty configuration, with `p = 1` and the pair weight supported on the single pair
`s(false, true)`, the total weighted pivotal flux is `1`. -/

/-- **A witness for the finiteness hypothesis of the real cap limit, with value `1`.** -/
example :
    (∑' e : Sym2 Bool, (if e = s(false, true) then (1 : ℝ≥0∞) else 0) *
      ∫⁻ ω : Config Bool, (((cluster (insert e ω) false).encard : ℝ≥0∞) ^ 1 -
        ((cluster (ω \ {e}) false).encard : ℝ≥0∞) ^ 1) ∂Measure.dirac (∅ : Config Bool)) = 1 := by
  classical
  have hcl : cluster (insert (s(false, true)) (∅ : Config Bool)) false = {false, true} := by
    apply Set.eq_of_subset_of_subset
    · intro x _
      cases x <;> simp
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with h | h
      · rw [h]; exact mem_cluster_self _ _
      · rw [Set.mem_singleton_iff.1 h]
        exact SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨by simp, by simp⟩)
  have hbase : cluster ((∅ : Config Bool) \ {s(false, true)}) false = {false} := by
    rw [Set.empty_sdiff, cluster_empty]
  have hp2 : (({false, true} : Set Bool).encard : ℝ≥0∞) = 2 := by
    rw [Set.encard_pair (by simp)]
    simp
  have hs1 : (({false} : Set Bool).encard : ℝ≥0∞) = 1 := by
    simp
  have hflux : ∫⁻ ω : Config Bool,
      (((cluster (insert (s(false, true)) ω) false).encard : ℝ≥0∞) ^ 1 -
        ((cluster (ω \ {s(false, true)}) false).encard : ℝ≥0∞) ^ 1)
        ∂Measure.dirac (∅ : Config Bool) = 1 := by
    rw [lintegral_dirac, hcl, hbase, pow_one, pow_one, hp2, hs1,
      show (2 : ℝ≥0∞) = 1 + 1 by norm_num, ENNReal.add_sub_cancel_left (by simp)]
  rw [tsum_eq_single (s(false, true)) (fun b hb => by simp [hb]), hflux]
  simp

end PercLib.Percolation.Bond



/-! ## Real-valued cap limits and the uncapped Russo flux

The real observable `F_M` is bounded and eventually constant, fitting the infinite-volume
Russo theorem. The uncapped result keeps the finite-cluster, inserted-moment, dominator,
interval-integrability and measurability hypotheses explicit: the cap supplies none of them.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Analysis

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `min c M → c` as `M → ∞`, for the real order. -/
theorem tendsto_min_atTop (c : ℝ) : Tendsto (fun M : ℝ => min c M) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop c] with M hM
  exact (min_eq_left hM).symm

/-- **The capped integral converges to the uncapped one.** For a nonnegative integrable `f` the
capped integrals `∫ min (f a) M` increase to `∫ f`. The dominator is `f` itself, so nothing
beyond integrability of the uncapped function is needed. -/
theorem tendsto_integral_min_atTop {f : α → ℝ} (hfm : AEMeasurable f μ) (hnn : 0 ≤ f)
    (hf : Integrable f μ) :
    Tendsto (fun M : ℝ => ∫ a, min (f a) M ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence f ?_ ?_ hf ?_
  · filter_upwards with M
    exact ((hfm.min aemeasurable_const).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    filter_upwards [ae_of_all μ hnn] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min ha hM)]
    exact min_le_left _ _
  · exact ae_of_all μ fun a => tendsto_min_atTop (f a)

/-- **The capped pivotal increment converges to the uncapped one.** With `0 ≤ g ≤ f` and `f`
integrable, `∫ (min (f a) M - min (g a) M) → ∫ (f - g)`. This is the per-edge real cap limit for
a difference of cluster volumes, stated for abstract `f, g` so that no cluster finiteness is built
in; the dominator is `f` and no `2 m` bound appears. -/
theorem tendsto_integral_min_sub_min_atTop {f g : α → ℝ} (hfm : AEMeasurable f μ)
    (hgm : AEMeasurable g μ) (hg0 : 0 ≤ᵐ[μ] g) (hgf : g ≤ᵐ[μ] f) (hf : Integrable f μ) :
    Tendsto (fun M : ℝ => ∫ a, (min (f a) M - min (g a) M) ∂μ) atTop
      (𝓝 (∫ a, f a ∂μ - ∫ a, g a ∂μ)) := by
  have hgi : Integrable g μ :=
    hf.mono' hgm.aestronglyMeasurable (by
      filter_upwards [hg0, hgf] with a h0 h1
      simp only [Pi.zero_apply] at h0
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  rw [← integral_sub hf hgi]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence f ?_ ?_ hf ?_
  · filter_upwards with M
    exact (((hfm.min aemeasurable_const).sub (hgm.min aemeasurable_const))
      |>.aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    filter_upwards [hg0, hgf] with a h0 h1
    simp only [Pi.zero_apply] at h0
    have h1' : 0 ≤ min (f a) M - min (g a) M := by
      have := min_le_min h1 (le_refl M)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg h1']
    have h2 : min (f a) M - min (g a) M ≤ f a - g a :=
      PercLib.Percolation.Bond.min_sub_min_le_sub h1
    linarith
  · filter_upwards with a
    exact (tendsto_min_atTop (f a)).sub (tendsto_min_atTop (g a))

end PercLib.Analysis

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-! ### The capped moment observable -/

/-- **The cap is `⊤`-compatible.** On an infinite cluster the capped moment observable takes the
value `M` of the cap, and on a finite cluster it is `min M (|K|^p)`. -/
theorem capped_pow_top (pow : ℕ) (hp : 1 ≤ pow) {M : ℝ} (hM : 0 ≤ M) :
    (min (ENNReal.ofReal M) (((⊤ : ℕ∞) : ℝ≥0∞) ^ pow)).toReal = M := by
  have htop : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ := rfl
  have hp0 : pow ≠ 0 := by omega
  rw [htop, ENNReal.top_pow hp0, min_eq_left le_top, ENNReal.toReal_ofReal hM]

/-- **The capped moment is bounded by the cap.** -/
theorem abs_capped_pow_toReal_le (pow : ℕ) {M : ℝ} (hM : 0 ≤ M) (n : ℕ∞) :
    |(min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal| ≤ M := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  calc (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal
      ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left _ _)
    _ = M := ENNReal.toReal_ofReal hM

/-- **The capped moment is eventually constant.** For `1 ≤ p` and `M ≥ 0` there is `n₀` with
`F_M n = F_M ⊤` for every `n ≥ n₀`, which is the eventual-constancy hypothesis of the library's
Russo formula. -/
theorem capped_pow_eventually_const (pow : ℕ) (hp : 1 ≤ pow) {M : ℝ} (hM : 0 ≤ M) :
    ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n →
      (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal =
        (min (ENNReal.ofReal M) (((⊤ : ℕ∞) : ℝ≥0∞) ^ pow)).toReal := by
  refine ⟨⌊max M 1⌋₊ + 1, fun n hn => ?_⟩
  rw [capped_pow_top pow hp hM]
  rcases eq_or_ne n ⊤ with h | h
  · rw [h, capped_pow_top pow hp hM]
  · have hcoe : ((n.toNat : ℕ) : ℕ∞) = n := ENat.natCast_toNat h
    have hge : (⌊max M 1⌋₊ + 1 : ℕ) ≤ n.toNat := by
      have h2 : ((⌊max M 1⌋₊ + 1 : ℕ) : ℕ∞) ≤ ((n.toNat : ℕ) : ℕ∞) := by rw [hcoe]; exact hn
      exact_mod_cast h2
    have hm : max M 1 ≤ (n.toNat : ℝ) := by
      have h1 : (max M 1 : ℝ) < (⌊max M 1⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊max M 1⌋₊ : ℝ) + 1) ≤ (n.toNat : ℝ) := by
        have h3 : ((⌊max M 1⌋₊ + 1 : ℕ) : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast hge
        push_cast at h3
        linarith
      linarith
    have hm1 : (1 : ℝ) ≤ (n.toNat : ℝ) := le_trans (le_max_right M 1) hm
    have hpow : M ≤ (n.toNat : ℝ) ^ pow := by
      have h4 : (n.toNat : ℝ) ^ 1 ≤ (n.toNat : ℝ) ^ pow := pow_le_pow_right₀ hm1 hp
      have h5 : ((n.toNat : ℝ) ^ 1) ≤ (n.toNat : ℝ) ^ pow := h4
      have h6 : M ≤ (n.toNat : ℝ) ^ 1 := by simpa using le_trans (le_max_left M 1) hm
      exact le_trans h6 h5
    have hmain : ENNReal.ofReal M ≤ ((n : ℝ≥0∞) ^ pow) := by
      have hn' : ((n.toNat : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) := by
        rw [← ENat.toENNReal_coe, hcoe]
      rw [← hn', ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
      exact ENNReal.ofReal_le_ofReal hpow
    rw [min_eq_left hmain, ENNReal.toReal_ofReal hM]


/-! ### The cap in the `ℝ≥0∞`-form used by the cluster volumes -/

/-- On a finite `ℝ≥0∞` value the capped moment is the minimum of the moment and the cap. This is
where a.e. finiteness of the cluster enters: on `⊤` the left side is `M`, not `min M 0`. -/
theorem capped_toReal_eq_min (pow : ℕ) {M : ℝ} (hM : 0 ≤ M) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    (min (ENNReal.ofReal M) (x ^ pow)).toReal = min (x.toReal ^ pow) M := by
  rw [ENNReal.toReal_min ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hx), ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hM, min_comm]

/-- The `p`-th power of the cluster volume of `o` after closing `e` is integrable as soon as it is
integrable after opening `e`: the closed cluster is contained in the open one. -/
theorem integrable_encard_sdiff_pow (μ : Measure (Config V)) (e : Sym2 V) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Integrable (fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) μ := by
  refine hint.mono' ((ENNReal.measurable_toReal.comp
    (measurable_encard_cluster_sdiff_coe e o)).pow_const pow).aestronglyMeasurable ?_
  filter_upwards [hfin] with ω hω
  have hle := encard_cluster_sdiff_le_insert_coe ω e o
  have h2 : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top hω hle
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg pow)]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hω hle) pow

/-- **The capped moment integral converges to the moment.** For an a.e. finite cluster at `o` with
finite `p`-th moment, `∫ min M (|K_o|^p) → ∫ |K_o|^p`. Note that the moment `|K_o|^p` here is the
honest real moment, which is only honest because the cluster is a.e. finite. -/
theorem tendsto_integral_capped_encard (μ : Measure (Config V)) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Tendsto (fun M : ℝ =>
        ∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂μ)
      atTop (𝓝 (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂μ)) := by
  have hm : AEMeasurable (fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) μ :=
    ((ENNReal.measurable_toReal.comp
      (Measurable.of_discrete.comp
        (measurable_encard_cluster (x := o)))).pow_const pow).aemeasurable
  refine (PercLib.Analysis.tendsto_integral_min_atTop (μ := μ) (f := fun ω =>
    (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) hm
    (fun ω => pow_nonneg ENNReal.toReal_nonneg pow) hint).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
  exact (integral_congr_ae (by
    filter_upwards [hfin] with ω hω
    exact capped_toReal_eq_min pow hM hω)).symm

/-- **The per-edge real cap limit, in `min` form.** The capped pivotal increment of the `p`-th
cluster-volume moment converges to the uncapped one. Hypotheses: a.e. finiteness of the cluster of
`o` after opening `e`, and integrability of the `p`-th moment of that cluster. No dominator beyond
the uncapped moment itself is used. -/
theorem tendsto_integral_capped_pivotal (μ : Measure (Config V)) (e : Sym2 V) (o : V) (pow : ℕ)
    (hfin : ∀ᵐ ω ∂μ, ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ) :
    Tendsto (fun M : ℝ => ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal) ∂μ)
      atTop (𝓝 (∫ ω, ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
        (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂μ)) := by
  have hfin' : ∀ᵐ ω ∂μ, ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
    hfin.mono fun ω h => ne_top_of_le_ne_top h (encard_cluster_sdiff_le_insert_coe ω e o)
  have hgf : (fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
      ≤ᵐ[μ] (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) := by
    filter_upwards [hfin] with ω hω
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg
      (ENNReal.toReal_mono hω (encard_cluster_sdiff_le_insert_coe ω e o)) pow
  have hg0 : (0 : Config V → ℝ) ≤ᵐ[μ]
      (fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) :=
    ae_of_all μ fun ω => pow_nonneg ENNReal.toReal_nonneg pow
  have hfm : AEMeasurable (fun ω : Config V =>
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) μ :=
    ((ENNReal.measurable_toReal.comp
      (measurable_encard_cluster_insert_coe e o)).pow_const pow).aemeasurable
  have hgm : AEMeasurable (fun ω : Config V =>
      (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) μ :=
    ((ENNReal.measurable_toReal.comp
      (measurable_encard_cluster_sdiff_coe e o)).pow_const pow).aemeasurable
  have hmain := PercLib.Analysis.tendsto_integral_min_sub_min_atTop (μ := μ)
    (f := fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
    (g := fun ω => (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow)
    hfm hgm hg0 hgf hint
  rw [← integral_sub hint (integrable_encard_sdiff_pow μ e o pow hfin hint)] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
  exact (integral_congr_ae (by
    filter_upwards [hfin, hfin'] with ω h1 h2
    rw [capped_toReal_eq_min pow hM h1, capped_toReal_eq_min pow hM h2, min_comm])).symm

/-! ### The capped Russo identity for the moment itself -/

/-- **The capped infinite-volume Russo identity for the `p`-th cluster-volume moment.**

Instantiating `integral_sub_eq_integral_flux` at the observable `F_M n = min M (n ^ p)`,
`F_M ⊤ = M` gives, for every cap `M ≥ 0`, the identity between the capped moment difference and
the time integral of the capped flux. The constant in the flux dominator is `(max B 0) (2 M + 3)`:
it grows with the cap, which is precisely why this identity alone does not pass to `M → ∞`. -/
theorem integral_sub_eq_integral_flux_capped_moment
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {u v : ℝ} (Cc : Sym2 V → Set ℝ)
    (hC : ∀ e, (Cc e).Countable)
    (hcont : ∀ e, ContinuousOn (fun r => (p r e : ℝ)) (Ioo u v))
    (hderiv : ∀ e, ∀ r ∈ Ioo u v, r ∉ Cc e → HasDerivAt (fun r => (p r e : ℝ)) (c r e) r)
    (o : V) (pow : ℕ) (hp : 1 ≤ pow) {M : ℝ} (hM : 0 ≤ M) {B : ℝ}
    (hB : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ B)
    {s t : ℝ} (hus : u < s) (hst : s ≤ t) (htv : t < v) :
    (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂law (p r) := by
  have h := PercLib.Models.LongRange.integral_sub_eq_integral_flux
    (F := fun n : ℕ∞ => (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal) (m := M)
    (abs_capped_pow_toReal_le pow hM) (capped_pow_eventually_const pow hp hM) o p c Cc hC hcont
    hderiv (M := max B 0 * (2 * M + 3)) ?_ hus hst htv
  · simpa only using h
  · intro r hr S
    refine (hB r hr S).trans ?_
    have h1 : B ≤ max B 0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ max B 0 := le_max_right _ _
    have h3 : (1 : ℝ) ≤ 2 * M + 3 := by linarith
    nlinarith

/-! ### The all-pairs cap limit -/

/-- **The all-pairs flux cap limit.** Under a.e. finiteness of every inserted cluster, integrability
of every single-edge `p`-th moment, and summability of the all-pairs dominator
`e ↦ |c e| E|K_o(ω ∪ {e})|^p`, the capped flux series converges to the uncapped one. The dominator
is cap-independent; this is the point at which the `2 m` touch bound is replaced by the moment
itself. -/
theorem tendsto_tsum_capped_flux (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V)
    (pow : ℕ) (r : ℝ)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (p r)), ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (p r)))
    (hsum : Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) :
    Tendsto (fun M : ℝ => ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r)))
      atTop (𝓝 (∑' e, c r e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂(law (p r)))) := by
  refine tendsto_tsum_of_dominated_convergence hsum (fun e => ?_) ?_
  · exact (tendsto_integral_capped_pivotal (law (p r)) e o pow (hfin e) (hint e)).const_mul (c r e)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM e
    have hfin' : ∀ᵐ ω ∂(law (p r)), ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ :=
      (hfin e).mono fun ω h => ne_top_of_le_ne_top h (encard_cluster_sdiff_le_insert_coe ω e o)
    have hb : ∀ᵐ ω ∂(law (p r)), ‖(min (ENNReal.ofReal M)
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal‖ ≤
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
      filter_upwards [hfin e, hfin'] with ω h1 h2
      have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
          ((cluster (insert e ω) o).encard : ℝ≥0∞) := encard_cluster_sdiff_le_insert_coe ω e o
      have h2' : (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow ≤
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono h1 hle) pow
      rw [capped_toReal_eq_min pow hM h1, capped_toReal_eq_min pow hM h2, Real.norm_eq_abs,
        abs_of_nonneg]
      · have h3 : min ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) M -
            min ((((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) M ≤
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          PercLib.Percolation.Bond.min_sub_min_le_sub h2'
        have h4 : (0 : ℝ) ≤ (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          pow_nonneg ENNReal.toReal_nonneg pow
        linarith
      · have := min_le_min h2' (le_refl M)
        linarith
    have hle := norm_integral_le_of_norm_le (hint e) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

omit [Countable V] in
/-- **A sufficient condition for the all-pairs dominator.** The summability hypothesis `hsum` of
`abs_tsum_capped_flux_le` and `integral_sub_eq_integral_flux_of_cap` is implied by a
uniform-in-`e` bound `K` on the single-edge `p`-th moments together with summability of the
derivative weights `e ↦ |c r e|`. On the cut-off family the weights are finitely supported, so the
second input is free there; the first is what sharpness of the phase transition has to supply. The
two inputs are separate: the weights do not control the cluster moments. -/
theorem summable_flux_dominator_of_uniform_moment (p : ℝ → Sym2 V → unitInterval)
    (c : ℝ → Sym2 V → ℝ) (o : V) (pow : ℕ) (r : ℝ) {K : ℝ}
    (hbound : ∀ e, ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow
      ∂(law (p r)) ≤ K)
    (hw : Summable fun e => |c r e|) :
    Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
  refine Summable.of_nonneg_of_le (fun e => mul_nonneg (abs_nonneg _) (integral_nonneg fun ω =>
    pow_nonneg ENNReal.toReal_nonneg pow)) (fun e => ?_) (hw.mul_right K)
  exact mul_le_mul_of_nonneg_left (hbound e) (abs_nonneg _)

omit [Countable V] in
/-- **The cap-independent dominator of the whole capped flux series.**

For every cap `M ≥ 0` the capped all-pairs flux is dominated, uniformly in `M`, by the all-pairs
series of the *uncapped* single-edge `p`-th moments with the edge forced open:
`‖∑_e c_e ∫ (min M f_e - min M g_e)‖ ≤ ∑_e |c_e| ∫ f_e`. This is the honest replacement for the
`2 m` touch bound: the `2 m` bound of `abs_flux_le` is cap-dependent (its `m` is the cap), while
this one is not. The price is exactly the summability hypothesis `hsum`: the uncapped all-pairs
series must converge, which is not implied by finiteness of the single-edge moments. -/
theorem abs_tsum_capped_flux_le (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V)
    (pow : ℕ) (r : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfin : ∀ e, ∀ᵐ ω ∂(law (p r)), ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ e, Integrable (fun ω => (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow)
      (law (p r)))
    (hsum : Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) :
    ‖∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))‖ ≤ ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
  have hfin' : ∀ e, ∀ᵐ ω ∂(law (p r)), ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≠ ⊤ := fun e =>
    (hfin e).mono fun ω h => ne_top_of_le_ne_top h (encard_cluster_sdiff_le_insert_coe ω e o)
  have hterm : ∀ e, ‖c r e * ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
      ∂(law (p r))‖ ≤ |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
    intro e
    have hb : ∀ᵐ ω ∂(law (p r)), ‖(min (ENNReal.ofReal M)
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal‖ ≤
        (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow := by
      filter_upwards [hfin e, hfin' e] with ω h1 h2
      have hle : ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ≤
          ((cluster (insert e ω) o).encard : ℝ≥0∞) := encard_cluster_sdiff_le_insert_coe ω e o
      have h2' : (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow ≤
          (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono h1 hle) pow
      rw [capped_toReal_eq_min pow hM h1, capped_toReal_eq_min pow hM h2, Real.norm_eq_abs,
        abs_of_nonneg]
      · have h3 : min ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) M -
            min ((((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) M ≤
            (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
            (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          PercLib.Percolation.Bond.min_sub_min_le_sub h2'
        have h4 : (0 : ℝ) ≤ (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow :=
          pow_nonneg ENNReal.toReal_nonneg pow
        linarith
      · have := min_le_min h2' (le_refl M)
        linarith
    have hle := norm_integral_le_of_norm_le (hint e) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have hsumm' : Summable fun e => c r e * ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
      ∂(law (p r)) := hsum.of_norm_bounded fun i => by
        simpa only [norm_norm] using hterm i
  calc ‖∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))‖
      ≤ ∑' e, ‖c r e * ∫ ω,
          ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
            (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
          ∂(law (p r))‖ := norm_tsum_le_tsum_norm (hsum.of_norm_bounded fun i => by
            simpa only [norm_norm] using hterm i)
    _ ≤ ∑' e, |c r e| *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) :=
      Summable.tsum_le_tsum (fun i => hterm i) (hsum.of_norm_bounded fun i => by
        simpa only [norm_norm] using hterm i) hsum

/-! ### The assembled transfer -/

/-- **The uncapped integrated Russo identity for the `p`-th moment.** From the capped identities for
every cap (proved separately in `integral_sub_eq_integral_flux_capped_moment`) and dominated
convergence of the capped flux series (dominator: the all-pairs series of single-edge `p`-th
moments), the identity passes to the uncapped moment.

What is *not* proved here, and is exposed as hypotheses: a.e. finiteness of every inserted cluster
at `o` and of the cluster at `o` under the two endpoint profiles; integrability of every single-edge
`p`-th moment with the edge forced open, and of the endpoint moments; summability of the all-pairs
dominator; interval-integrability of the dominator; and measurability in the scale `r` of the capped
flux. None of these follows from finite clusters or a finite root moment alone — in particular
`hsum`, `hD` and `hmeas` are extra inputs. -/
theorem integral_sub_eq_integral_flux_of_cap
    (p : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {u v : ℝ} (Cc : Sym2 V → Set ℝ)
    (hC : ∀ e, (Cc e).Countable)
    (hcont : ∀ e, ContinuousOn (fun r => (p r e : ℝ)) (Ioo u v))
    (hderiv : ∀ e, ∀ r ∈ Ioo u v, r ∉ Cc e → HasDerivAt (fun r => (p r e : ℝ)) (c r e) r)
    (o : V) (pow : ℕ) (hp : 1 ≤ pow) {B : ℝ}
    (hB : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V),
      ∑ e ∈ S, |c r e| * (law (p r)).real {ω | ∃ x ∈ e, x ∈ cluster ω o} ≤ B)
    {s t : ℝ} (hus : u < s) (hst : s ≤ t) (htv : t < v)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (p r)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hint : ∀ r ∈ Ioo u v, ∀ e, Integrable (fun ω =>
      (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow) (law (p r)))
    (hsum : ∀ r ∈ Ioo u v, Summable fun e => |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)))
    (hD : IntervalIntegrable (fun r => ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)))
      volume s t)
    (hmeas : ∀ M : ℝ, AEStronglyMeasurable (fun r => ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))) (volume.restrict (uIoc s t)))
    (hfinT : ∀ᵐ ω ∂(law (p t)), ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤)
    (hfinS : ∀ᵐ ω ∂(law (p s)), ((cluster ω o).encard : ℝ≥0∞) ≠ ⊤)
    (hintT : Integrable (fun ω => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) (law (p t)))
    (hintS : Integrable (fun ω => (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow) (law (p s))) :
    (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p t)) -
      (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂(law (p r)) := by
  classical
  -- the LHS at both endpoints
  have hL : Tendsto (fun M : ℝ =>
      ∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p t)) atTop
      (𝓝 (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p t))) :=
    tendsto_integral_capped_encard (law (p t)) o pow hfinT hintT
  have hLs : Tendsto (fun M : ℝ =>
      ∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s)) atTop
      (𝓝 (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p s))) :=
    tendsto_integral_capped_encard (law (p s)) o pow hfinS hintS
  -- the interval-integral side
  have hDnn : ∀ r ∈ Ioo u v, 0 ≤ ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) := by
    intro r hr
    exact tsum_nonneg fun e => mul_nonneg (abs_nonneg _) (integral_nonneg fun ω =>
      pow_nonneg ENNReal.toReal_nonneg pow)
  have hbound : ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Ioo u v, ‖∑' e, c r e * ∫ ω,
      ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
      ∂(law (p r))‖ ≤ ∑' e, |c r e| *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r)) :=
    fun M hM r hr => abs_tsum_capped_flux_le p c o pow r hM (hfin r hr) (hint r hr) (hsum r hr)
  -- the per-cap identities
  have hcap : ∀ M : ℝ, 0 ≤ M → (∫ ω, (min (ENNReal.ofReal M)
        (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s)) =
      ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂law (p r) := fun M hM =>
    integral_sub_eq_integral_flux_capped_moment p c Cc hC hcont hderiv o pow hp hM hB hus hst htv
  have hleft : Tendsto (fun M : ℝ => (∫ ω, (min (ENNReal.ofReal M)
        (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s))) atTop
      (𝓝 ((∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p t)) -
        (∫ ω, (((cluster ω o).encard : ℝ≥0∞).toReal) ^ pow ∂law (p s)))) := hL.sub hLs
  have hright : Tendsto (fun M : ℝ => ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (p r))) atTop
      (𝓝 (∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow -
          (((cluster (ω \ {e}) o).encard : ℝ≥0∞).toReal) ^ pow) ∂(law (p r)))) := by
    have hsub : uIoc s t ⊆ Ioo u v := by
      rw [uIoc_of_le hst]
      exact fun r hr => ⟨lt_trans hus hr.1, lt_of_le_of_lt hr.2 htv⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun r => ∑' e, |c r e| *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞).toReal) ^ pow ∂(law (p r))) ?_ ?_ hD ?_
    · filter_upwards with M
      exact hmeas M
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
      filter_upwards with r hr
      exact hbound M hM r (hsub hr)
    · filter_upwards with r hr
      exact tendsto_tsum_capped_flux p c o pow r (hfin r (hsub hr))
        (hint r (hsub hr)) (hsum r (hsub hr))
  have hcongr : (fun M : ℝ => (∫ ω, (min (ENNReal.ofReal M)
        (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal ∂law (p t)) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂law (p s))) =ᶠ[atTop] fun M : ℝ => ∫ r in s..t, ∑' e, c r e * ∫ ω,
        ((min (ENNReal.ofReal M) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂law (p r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    exact hcap M hM
  exact tendsto_nhds_unique (hleft.congr' hcongr) hright


/-! ### Non-vacuity -/

/-- The cap binds below the cap value and does not bind above it: both branches of
`min M (n ^ p)` occur, and `capped_toReal_eq_min` computes them. -/
example : (min (ENNReal.ofReal (9 : ℝ)) (((6 : ℕ∞) : ℝ≥0∞) ^ 2)).toReal = 9 ∧
    (min (ENNReal.ofReal (9 : ℝ)) (((2 : ℕ∞) : ℝ≥0∞) ^ 2)).toReal = 4 := by
  refine ⟨?_, ?_⟩
  · rw [capped_toReal_eq_min 2 (by norm_num) (by norm_num)]; norm_num
  · rw [capped_toReal_eq_min 2 (by norm_num) (by norm_num)]; norm_num

/-- **Non-vacuity of the moment cap limit.** On the one-point vertex type `Unit` every cluster is
the whole vertex set, so the cluster of `()` is a.e. finite and has first moment `1`; the hypotheses
of `tendsto_integral_capped_encard` therefore hold, and the limit is the nonzero value `1`. -/
example : Tendsto (fun M : ℝ => ∫ ω : Config Unit,
      (min (ENNReal.ofReal M) (((cluster ω ()).encard : ℝ≥0∞) ^ 1)).toReal
      ∂(Measure.dirac (∅ : Config Unit))) atTop (𝓝 1) := by
  have hcl : ∀ ω : Config Unit, cluster ω () = Set.univ := fun ω =>
    Set.eq_univ_of_forall fun x => by
      rw [Subsingleton.elim x ()]
      exact mem_cluster_self ω ()
  have h := tendsto_integral_capped_encard (Measure.dirac (∅ : Config Unit)) () 1
    (by
      filter_upwards with ω
      rw [hcl ω]
      simp)
    (MeasureTheory.integrable_dirac (by simp))
  have hlim : (∫ ω : Config Unit, (((cluster ω ()).encard : ℝ≥0∞).toReal) ^ 1
      ∂(Measure.dirac (∅ : Config Unit))) = 1 := by
    rw [integral_dirac, hcl]
    simp
  rw [hlim] at h
  exact h

end PercLib.Percolation.Bond

/-! ### The capped moment identity on the cut-off family

The per-cap identity of `integral_sub_eq_integral_flux_capped_moment` is stated for an abstract
profile family with an abstract touch dominator. On the cut-off family of Definition I.1.5 all the
abstract inputs except the finiteness of the first moment are discharged (`cutoff_dominator`,
`continuousOn_cutoff_prob`, `hasDerivAt_cutoff_prob`, `countable_cutoff_corners`), so the capped
identity below is unconditional apart from `0 < s ≤ t < R` and `χ_{μ_R}(o) < ∞`. -/

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}

/-- **The capped Russo identity on the cut-off family.** With
`c_r(e) = 1{N(e) < r} β (-K'(r)) e^{-β J_r(e)}` and `μ_r` the cut-off law at scale `r`, for every
cap `M ≥ 0` and `0 < s ≤ t < R`,

`(capped moment at t) - (capped moment at s)
  = ∫_s^t ∑'_e c_r(e) ∫ (min M |K_o(ω ∪ {e})|^p - min M |K_o(ω \ {e})|^p) dμ_r dr`.

This is the per-cap identity of the paper's derivative formula (I.4.1) in integrated form, with the
`p`-th moment capped; it is not the `M → ∞` limit, which needs the cap-independent dominator of
`abs_tsum_capped_flux_le`. -/
theorem integral_sub_eq_integral_flux_cutoff_capped_moment
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (o : Fin d → ℤ) (pow : ℕ) (hp : 1 ≤ pow)
    {M : ℝ} (hM : 0 ≤ M) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (htR : t < R) :
    (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂(law (intensityProfile (cutoffKernel N K t) β))) -
      (∫ ω, (min (ENNReal.ofReal M) (((cluster ω o).encard : ℝ≥0∞) ^ pow)).toReal
        ∂(law (intensityProfile (cutoffKernel N K s) β))) =
      ∫ r in s..t, ∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        ∫ ω, ((min (ENNReal.ofReal M)
            (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
          (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
          ∂(law (intensityProfile (cutoffKernel N K r) β)) :=
  PercLib.Models.LongRange.integral_sub_eq_integral_flux_cutoff hKa hK' hK'c β
    (F := fun n : ℕ∞ => (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal) (m := M)
    (abs_capped_pow_toReal_le pow hM) (capped_pow_eventually_const pow hp hM) o hχ hs hst htR

end PercLib.Models.LongRange



/-! ## Measurability of capped cutoff fluxes

The capped flux is almost everywhere the derivative of the capped moment.
Identifying it with `deriv` supplies measurability on a finite time window outside
countable cutoff corners, with no separate regularity premise.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- The finite-window cutoff flux is a.e. strongly measurable because it is almost everywhere
the derivative of the capped moment. -/
theorem measurable_flux_cutoff_of_bounded
    {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {F : ℕ∞ → ℝ} {m : ℝ}
    (hFm : ∀ n, |F n| ≤ m)
    (hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n → F n = F ⊤)
    (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htR : t < R) :
    AEStronglyMeasurable (fun r => ∑' e, ((radialKernel N
      (fun u => if u < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (volume.restrict (uIoc s t)) := by
  let ψ : ℝ → ℝ := fun r => ∫ ω, F (cluster ω o).encard
    ∂(law (intensityProfile (cutoffKernel N K r) β))
  let Φ : ℝ → ℝ := fun r => ∑' e, ((radialKernel N
    (fun u => if u < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
    ∫ ω, (F (cluster (insert e ω) o).encard - F (cluster (ω \ {e}) o).encard)
      ∂(law (intensityProfile (cutoffKernel N K r) β))
  have hnear : ∀ r ∈ Ioc s t, r ∉ ⋃ e : Sym2 (Fin d → ℤ),
      {u : ℝ | ∃ x y, e = s(x, y) ∧ u = N (Int.cast ∘ (x - y))} → Φ r = deriv ψ r := by
    intro r hr hbad
    have hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r := by
      intro z hz
      apply hbad
      refine Set.mem_iUnion.2 ⟨s(0, z), 0, z, rfl, ?_⟩
      simpa only [zero_sub, intCast_comp_neg, map_neg_eq_map] using hz.symm
    exact (hasDerivAt_integral_cutoff hKa hK' hK'c β hFm hF o hχ
      (hs.trans hr.1) (hr.2.trans_lt htR) hcorner).deriv.symm
  have hcorners : (⋃ e : Sym2 (Fin d → ℤ),
      {r : ℝ | ∃ x y, e = s(x, y) ∧ r = N (Int.cast ∘ (x - y))}).Countable :=
    Set.countable_iUnion fun _ => countable_cutoff_corners _
  have hnull : ∀ᵐ r : ℝ ∂volume, r ∉ ⋃ e : Sym2 (Fin d → ℤ),
      {u : ℝ | ∃ x y, e = s(x, y) ∧ u = N (Int.cast ∘ (x - y))} :=
    measure_eq_zero_iff_ae_notMem.1 (hcorners.measure_zero volume)
  rw [uIoc_of_le hst]
  refine (measurable_deriv ψ).aestronglyMeasurable.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hnull] with r hr hbad
  exact (hnear r hr hbad).symm

end PercLib.Models.LongRange

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

/-- A nonpositive real cap is zero in the `ENNReal.ofReal` cap construction. -/
theorem capped_pow_toReal_eq_zero_of_nonpos {M : ℝ} (hM : M ≤ 0) (n : ℕ∞) (pow : ℕ) :
    (min (ENNReal.ofReal M) ((n : ℝ≥0∞) ^ pow)).toReal = 0 := by
  simp [ENNReal.ofReal_of_nonpos hM]

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond PercLib.Probability

/-- Every real cap produces an a.e.-strongly measurable cutoff flux of the `pow`-th
moment. The cap need not be nonnegative: for a negative cap the flux is identically zero. -/
theorem measurable_capped_flux_cutoff
    {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0)
    (o : Fin d → ℤ) (pow : ℕ) (hp : 1 ≤ pow) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htR : t < R) (M : ℝ) :
    AEStronglyMeasurable (fun r => ∑' e, ((radialKernel N
      (fun u => if u < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
      ∫ ω, ((min (ENNReal.ofReal M)
          (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ pow)).toReal -
        (min (ENNReal.ofReal M) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ pow)).toReal)
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (volume.restrict (uIoc s t)) := by
  by_cases hM : 0 ≤ M
  · exact measurable_flux_cutoff_of_bounded hKa hK' hK'c β
      (abs_capped_pow_toReal_le pow hM) (capped_pow_eventually_const pow hp hM)
      o hχ hs hst htR
  · have hMn : M ≤ 0 := le_of_not_ge hM
    simp_rw [capped_pow_toReal_eq_zero_of_nonpos hMn]
    exact measurable_flux_cutoff_of_bounded hKa hK' hK'c β
      (F := fun _ : ℕ∞ => (0 : ℝ)) (m := 0) (fun _ => by simp) ⟨0, fun _ _ => rfl⟩
      o hχ hs hst htR

end PercLib.Models.LongRange

/-! ## Differentiation of capped moments and the uncapped cap passage

The bounded Russo formula applies at every natural cap. The differentiability transfer to
uncapped moments is conditional on a finite cluster/moment bundle and a genuinely
interval-integrable all-pairs dominator, with continuity of the uncapped flux supplied
explicitly too. Neither of those model inputs is discharged here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open PercLib.Percolation.Bond
open PercLib.Analysis

namespace PercLib.Models.LongRange

/-- Measurability of the `p`-th power of a cluster volume. -/
theorem measurable_encard_cluster_pow {V : Type*} [Countable V] (o : V) (p : ℕ) :
    Measurable fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p := by
  have h : (fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p)
      = fun ω : Config V => (((cluster ω o).encard ^ p : ℕ∞) : ℝ≥0∞) := by
    funext ω
    simp
  rw [h]
  exact Measurable.of_discrete.comp ((measurable_encard_cluster o).pow_const p)

/-- Capped `p`-th cluster moments increase to the uncapped one, in `ℝ≥0∞`. -/
theorem tendsto_lintegral_min_pow_encard {V : Type*} [Countable V]
    (μ : Measure (Config V)) (o : V) (p : ℕ) :
    Tendsto (fun n : ℕ => ∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)
      atTop (𝓝 (∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)) := by
  have hmeas : Measurable fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p :=
    measurable_encard_cluster_pow o p
  have hmono : Monotone fun n : ℕ => fun ω : Config V =>
      min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) :=
    fun m n hmn ω => min_le_min_right _ (by exact_mod_cast hmn)
  have hiSup : (⨆ n : ℕ, ∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)
      = ∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ := by
    rw [← lintegral_iSup (f := fun n : ℕ => fun ω : Config V =>
      min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p))
      (fun n => measurable_const.min hmeas) hmono]
    exact lintegral_congr fun ω => iSup_min_natCast _
  have hmono' : Monotone fun n : ℕ =>
      ∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ :=
    fun m n hmn => lintegral_mono fun ω => hmono hmn ω
  have h := tendsto_atTop_iSup hmono'
  rwa [hiSup] at h

/-- Real form: the capped `p`-th moments converge to the uncapped one whenever the latter is
finite. -/
theorem tendsto_integral_min_pow_encard {V : Type*} [Countable V]
    (μ : Measure (Config V)) [IsFiniteMeasure μ] (o : V) (p : ℕ)
    (hmom : (∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p)).toReal ∂μ)
      atTop (𝓝 (∫ ω, (((((cluster ω o).encard : ℝ≥0∞)) ^ p)).toReal ∂μ)) := by
  have hmeas : Measurable fun ω : Config V => (((cluster ω o).encard : ℝ≥0∞)) ^ p :=
    measurable_encard_cluster_pow o p
  have hne : ∀ n : ℕ, (∫⁻ ω, min (n : ℝ≥0∞) ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω => min_le_left _ _)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ univ)
  have hreal := (ENNReal.tendsto_toReal_iff hne hmom).2 (tendsto_lintegral_min_pow_encard μ o p)
  have h1 : (∫ ω, (((((cluster ω o).encard : ℝ≥0∞)) ^ p)).toReal ∂μ)
      = ((∫⁻ ω, ((((cluster ω o).encard : ℝ≥0∞)) ^ p) ∂μ)).toReal :=
    integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hmom)
  rw [h1]
  refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hreal
  exact (integral_toReal ((measurable_const.min hmeas)).aemeasurable
    (Eventually.of_forall fun ω => lt_of_le_of_lt (min_le_left (n:ℝ≥0∞) _) (by simp))).symm

/-- **Per-edge domination of the capped pivotal flux.** The capped pivotal `p`-flux is bounded
in absolute value by the uncapped pivotal `ℝ≥0∞` flux, uniformly in the cap. -/
theorem abs_integral_pivotal_truncation_le {V : Type*} [Countable V]
    (μ : Measure (Config V)) [IsFiniteMeasure μ] (e : Sym2 V) (o : V) (p n : ℕ)
    (hflux : (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ) ≠ ⊤) :
    |∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ|
      ≤ (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ).toReal := by
  have hIntCap : ∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ
      = (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal :=
    integral_toReal (measurable_pivotal_truncation e o p n).aemeasurable
      (Eventually.of_forall fun ω => lt_of_le_of_lt (pivotal_truncation_le_cap _ _ n) (by simp))
  have hle : (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal
      ≤ (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂μ).toReal :=
    ENNReal.toReal_mono hflux (lintegral_pivotal_truncation_le μ e o p n)
  calc |∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ|
      ≤ ∫ ω, |(min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal| ∂μ :=
        abs_integral_le_integral_abs
    _ = ∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact abs_of_nonneg ENNReal.toReal_nonneg
    _ ≤ _ := by rw [hIntCap]; exact hle

/-- **Abstract series cap passage.** If the weighted family `g` has all finite weighted partial
sums bounded by `K`, and `f n → g` pointwise with `|f n| ≤ |g|` termwise, then the weighted
series of `f n` converges to the weighted series of `g`. -/
theorem tendsto_tsum_of_dominated_convergence_real {ι : Type*} [Countable ι]
    {f : ℕ → ι → ℝ} {g : ι → ℝ} {w : ι → ℝ} {K : ℝ}
    (hK : ∀ S : Finset ι, ∑ e ∈ S, |w e| * |g e| ≤ K)
    (hconv : ∀ e, Tendsto (fun n => f n e) atTop (𝓝 (g e)))
    (hle : ∀ n e, |f n e| ≤ |g e|) :
    Tendsto (fun n => ∑' e, w e * f n e) atTop (𝓝 (∑' e, w e * g e)) := by
  have hbound_nn : ∀ e, 0 ≤ |w e| * |g e| := fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsumm : Summable fun e => |w e| * |g e| := summable_of_sum_le hbound_nn hK
  have hdom : ∀ᶠ (n : ℕ) in atTop, ∀ e, ‖w e * f n e‖ ≤ |w e| * |g e| := by
    refine Eventually.of_forall fun n e => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hle n e) (abs_nonneg _)
  have hlim : ∀ e, Tendsto (fun n => w e * f n e) atTop (𝓝 (w e * g e)) :=
    fun e => (hconv e).const_mul (w e)
  exact tendsto_tsum_of_dominated_convergence hsumm hlim hdom

/-- **The cap passage of the infinite-volume Russo derivative for the `p`-th moment.**

Let `q r` be a family of bond laws on a countable vertex set, `c r e` the derivative in the
parameter `r` of the pair probability of `e`, `o` a root and `p : ℕ`. Assume:

* `hKd`: the weighted uncapped pivotal `p`-flux has all finite partial sums bounded by the
  fixed function `Kd` (the all-pairs dominator), and `Kd` is interval integrable;
* `hfin`: for every `r` in the parameter interval and every pair `e`, the cluster of `o` after
  forcing `e` open is almost surely finite;
* `hflux`: the uncapped pivotal `p`-flux of every pair is finite;
* `hmom`: the uncapped `p`-th cluster moment is finite;
* `hd`: every capped moment `r ↦ E[min (|K_o|^p) n]` is differentiable with derivative the
  capped pivotal series (this is the finite-window Russo formula for the bounded observable);
* `hmeas`, `hcont`: the capped flux functions are a.e. strongly measurable and the uncapped
  flux is continuous in the parameter.

Then the uncapped `p`-th cluster moment is differentiable with derivative the infinite
pivotal flux series. -/
theorem hasDerivAt_integral_pow_of_cap_flux {V : Type*} [Countable V]
    (q : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (o : V) (p : ℕ)
    {u v r₀ : ℝ} (hur : u < r₀) (hrv : r₀ < v)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 V), ∑ e ∈ S, |c r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))| ≤ Kd r)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (q r)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂(law (q r))) ≠ ⊤)
    (hmom : ∀ r ∈ Ioo u v, (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p) ∂(law (q r))) ≠ ⊤)
    (hd : ∀ n : ℕ, ∀ r ∈ Ioo u v, HasDerivAt (fun s =>
        ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q s)))
      (∑' e, c r e * (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂(law (q r))).toReal) r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, c r e * (∫⁻ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂(law (q r))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, c r e * ∫ ω,
      (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r)))
      (∑' e, c r₀ e * ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r₀))) r₀ := by
  classical
  let Q : ℝ → Sym2 V → ℝ := fun r e => ∫ ω,
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))
  let P : ℝ → Sym2 V → ℝ≥0∞ := fun r e => ∫⁻ ω,
    (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p) ∂(law (q r))
  let Pn : ℕ → ℝ → Sym2 V → ℝ := fun n r e => (∫⁻ ω,
    (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
      min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂(law (q r))).toReal
  let Φn : ℕ → ℝ → ℝ := fun n r => ∑' e, c r e * Pn n r e
  let Φ : ℝ → ℝ := fun r => ∑' e, c r e * Q r e
  let ψn : ℕ → ℝ → ℝ := fun n r =>
    ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q r))
  let ψ : ℝ → ℝ := fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal ∂(law (q r))
  have hPn_eq : ∀ n r e, Pn n r e = ∫ ω,
      (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
      min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q r)) := by
    intro n r e
    refine (integral_toReal ((measurable_pivotal_truncation e o p n).aemeasurable) ?_).symm
    filter_upwards with ω
    exact lt_of_le_of_lt (pivotal_truncation_le_cap _ _ n) (by simp)
  have hQ_eq : ∀ r ∈ Ioo u v, ∀ e, Q r e = (P r e).toReal := by
    intro r hr e
    refine (integral_toReal (measurable_pivotal e o p).aemeasurable ?_).trans rfl
    filter_upwards [hfin r hr e] with ω hω
    exact pivotal_truncation_lt_top_of_ne_top hω
  have hmomconv : ∀ r ∈ Ioo u v, Tendsto (fun n => ψn n r) atTop (𝓝 (ψ r)) := by
    intro r hr
    exact tendsto_integral_min_pow_encard (law (q r)) o p (hmom r hr)
  have hedge : ∀ r ∈ Ioo u v, ∀ e, Tendsto (fun n => Pn n r e) atTop (𝓝 (Q r e)) := by
    intro r hr e
    have h0 := tendsto_integral_pivotal_truncation (law (q r)) e o p (hfin r hr e) (hflux r hr e)
    exact h0.congr' (Eventually.of_forall fun n => (hPn_eq n r e).symm)
  have hle : ∀ r ∈ Ioo u v, ∀ n e, |Pn n r e| ≤ |Q r e| := by
    intro r hr n e
    have h := abs_integral_pivotal_truncation_le (law (q r)) e o p n (hflux r hr e)
    have h1 : Pn n r e = ∫ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal ∂(law (q r)) :=
      hPn_eq n r e
    have h2 : Q r e = (P r e).toReal := hQ_eq r hr e
    rw [h1, h2, abs_of_nonneg ENNReal.toReal_nonneg]
    exact h
  have hΦconv : ∀ r ∈ Ioo u v, Tendsto (fun n => Φn n r) atTop (𝓝 (Φ r)) := by
    intro r hr
    exact tendsto_tsum_of_dominated_convergence_real (hKd r hr) (hedge r hr) (hle r hr)
  have hbound : ∀ n : ℕ, ∀ r ∈ Ioo u v, |Φn n r| ≤ Kd r := by
    intro n r hr
    have hnn : ∀ e, 0 ≤ |c r e| * |Q r e| := fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsumm : Summable fun e => |c r e| * |Q r e| := summable_of_sum_le hnn (hKd r hr)
    have hsumm' : Summable fun e => |c r e| * |Pn n r e| :=
      hsumm.of_norm_bounded (fun e => by
        simpa only [Real.norm_eq_abs, abs_mul, abs_abs] using
          mul_le_mul_of_nonneg_left (hle r hr n e) (abs_nonneg (c r e)))
    have htri : |Φn n r| ≤ ∑' e, |c r e| * |Pn n r e| := by
      calc |Φn n r| = ‖∑' e, c r e * Pn n r e‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∑' e, ‖c r e * Pn n r e‖ :=
            norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs, abs_mul] using hsumm')
        _ = ∑' e, |c r e| * |Pn n r e| :=
            tsum_congr fun e => by rw [Real.norm_eq_abs, abs_mul]
    refine htri.trans (Real.tsum_le_of_sum_le
      (fun e => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (fun S => ?_))
    refine le_trans (Finset.sum_le_sum fun e _ => ?_) (hKd r hr S)
    exact mul_le_mul_of_nonneg_left (hle r hr n e) (abs_nonneg _)
  have hsubst : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, uIoc s t ⊆ Ioo u v := by
    intro s hs t ht x hx
    exact ⟨lt_trans (lt_min hs.1 ht.1) hx.1, lt_of_le_of_lt hx.2 (max_lt hs.2 ht.2)⟩
  have hsubst' : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, uIcc s t ⊆ Ioo u v := by
    intro s hs t ht x hx
    refine ⟨lt_of_lt_of_le (lt_min hs.1 ht.1) ?_, lt_of_le_of_lt ?_ (max_lt hs.2 ht.2)⟩
    · rw [Set.uIcc] at hx; exact hx.1
    · rw [Set.uIcc] at hx; exact hx.2
  have hcap : ∀ n : ℕ, ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, ∫ r in s..t, Φn n r = ψn n t - ψn n s := by
    intro n s hs t ht
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd n x (hsubst' s hs t ht hx)) ?_
    · exact IntervalIntegrable.mono_fun' (hKdint s hs t ht)
        ((hmeas n).mono_measure (Measure.restrict_mono_set volume (hsubst s hs t ht)))
        ((ae_restrict_mem measurableSet_uIoc).mono fun x hx =>
          (by simpa only [Real.norm_eq_abs] using hbound n x (hsubst s hs t ht hx)))
  have hlimint : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v,
      Tendsto (fun n => ∫ r in s..t, Φn n r) atTop (𝓝 (∫ r in s..t, Φ r)) := by
    intro s hs t ht
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := atTop) (a := s) (b := t) (f := Φ) (F := fun n => Φn n) Kd ?_ ?_ (hKdint s hs t ht) ?_
    · exact Eventually.of_forall fun n =>
        (hmeas n).mono_measure (Measure.restrict_mono_set volume (hsubst s hs t ht))
    · exact Eventually.of_forall fun n => by
        filter_upwards with x hx
        simpa only [Real.norm_eq_abs] using hbound n x (hsubst s hs t ht hx)
    · filter_upwards with x hx
      exact hΦconv x (hsubst s hs t ht hx)
  have hident : ∀ s ∈ Ioo u v, ∀ t ∈ Ioo u v, ∫ r in s..t, Φ r = ψ t - ψ s := by
    intro s hs t ht
    have h2 : Tendsto (fun n => ∫ r in s..t, Φn n r) atTop (𝓝 (ψ t - ψ s)) := by
      refine ((hmomconv t ht).sub (hmomconv s hs)).congr' (Eventually.of_forall fun n => ?_)
      exact (hcap n s hs t ht).symm
    exact tendsto_nhds_unique (hlimint s hs t ht) h2
  have hmem : Ioo u v ∈ 𝓝 r₀ := Ioo_mem_nhds hur hrv
  have hident' : ψ =ᶠ[𝓝 r₀] fun r => ψ r₀ + ∫ x in r₀..r, Φ x := by
    filter_upwards [hmem] with r hr
    rcases le_total r₀ r with h | h
    · have h1 := hident r₀ ⟨hur, hrv⟩ r hr
      rw [h1]; ring
    · have h1 := hident r hr r₀ ⟨hur, hrv⟩
      rw [intervalIntegral.integral_symm, h1]; ring
  have hInt : HasDerivAt (fun r => ψ r₀ + ∫ x in r₀..r, Φ x) (Φ r₀) r₀ :=
    (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hcont.stronglyMeasurableAtFilter isOpen_Ioo r₀ ⟨hur, hrv⟩)
      (hcont.continuousAt hmem)).const_add (ψ r₀)
  exact hInt.congr_of_eventuallyEq hident'

/-- **Bridge between the real-difference and the truncated-`ℝ≥0∞` form of the capped pivotal
flux.** The library's bounded-observable Russo formula `hasDerivAt_integral_cutoff` writes the
flux through a pair as the integral of the difference of the (real) observable, while the cap
passage here uses the `ℝ≥0∞` truncated subtraction. On a finite measure the two agree. -/
theorem integral_pivotal_min_sub_eq_lintegral {V : Type*} [Countable V]
    (μ : Measure (Config V)) [IsFiniteMeasure μ] (e : Sym2 V) (o : V) (p n : ℕ) :
    ∫ ω, ((min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal) ∂μ
      = (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)) ∂μ).toReal := by
  have hpt : ∀ ω : Config V,
      ((min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p)).toReal -
        (min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal)
      = (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)).toReal := by
    intro ω
    rw [ENNReal.toReal_sub_of_le
      (min_le_min_left (n : ℝ≥0∞)
        (ENNReal.pow_le_pow_left (encard_cluster_sdiff_le_insert_coe ω e o)))
      (ne_top_of_le_ne_top (by simp) (min_le_left (n : ℝ≥0∞) _))]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_toReal
    (measurable_pivotal_truncation e o p n).aemeasurable]
  exact Eventually.of_forall fun ω => lt_of_le_of_lt (pivotal_truncation_le_cap _ _ n) (by simp)


/-- The capped `p`-th power observable `k ↦ min (n) |k|^p` is bounded by its cap. -/
theorem abs_capped_pow_encard_le (n p : ℕ) (k : ℕ∞) :
    |(min (n : ℝ≥0∞) (((k : ℝ≥0∞)) ^ p)).toReal| ≤ (n : ℝ) := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (by simp) (min_le_left (n : ℝ≥0∞) _)

/-- The capped `p`-th power observable `k ↦ min (n) |k|^p` is eventually constant at `⊤`. -/
theorem capped_pow_encard_eventually_const (p : ℕ) (hp : 1 ≤ p) (n : ℕ) :
    ∃ n₀ : ℕ, ∀ k : ℕ∞, (n₀ : ℕ∞) ≤ k →
      (min (n : ℝ≥0∞) (((k : ℝ≥0∞)) ^ p)).toReal
        = (min (n : ℝ≥0∞) ((((⊤ : ℕ∞) : ℝ≥0∞)) ^ p)).toReal := by
  refine ⟨n, fun k hk => ?_⟩
  have hnk : (n : ℝ≥0∞) ≤ ((k : ℝ≥0∞)) := by
    have h1 : ((n : ℕ∞) : ℝ≥0∞) ≤ ((k : ℕ∞) : ℝ≥0∞) := by exact_mod_cast hk
    simpa using h1
  have hkp : (n : ℝ≥0∞) ≤ ((k : ℝ≥0∞) ^ p) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h1 : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) :=
        (by exact_mod_cast hn : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞)).trans hnk
      exact hnk.trans (le_self_pow₀ h1 (by omega))
  have htop : (n : ℝ≥0∞) ≤ (((⊤ : ℕ∞) : ℝ≥0∞) ^ p) := by
    rw [show ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ from by simp, ENNReal.top_pow (by omega)]
    exact le_top
  rw [min_eq_left hkp, min_eq_left htop]

/-- **Russo derivative of the capped `p`-th cluster moment of the cut-off family.** For every
cap `n`, the capped moment `s ↦ E[min (|K_o|^p) n]` under the cut-off law at scale `s` is
differentiable at `r ∈ (0, R)`, away from the corner values `N (z)`, with derivative the
(capped) infinite pivotal flux series in the truncated-`ℝ≥0∞` form consumed by the cap
passage `hasDerivAt_integral_pow_of_cap_flux`. Discharged from the library's bounded
Russo formula `hasDerivAt_integral_cutoff` with `F = k ↦ min (n) |k|^p`. -/
theorem hasDerivAt_capped_moment_cutoff {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p n : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤) {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r) :
    HasDerivAt (fun s => ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal
        ∂(law (intensityProfile (cutoffKernel N K s) β)))
      (∑' e, ((radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ)))) *
        (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal) r := by
  have h := hasDerivAt_integral_cutoff hKa hK' hK'c β
    (F := fun k : ℕ∞ => (min (n : ℝ≥0∞) (((k : ℝ≥0∞)) ^ p)).toReal)
    (abs_capped_pow_encard_le n p) (capped_pow_encard_eventually_const p hp n)
    o hχ hr hrR hcorner
  refine h.congr_deriv ?_
  refine tsum_congr fun e => ?_
  rw [integral_pivotal_min_sub_eq_lintegral]


/-- **Russo derivative of the capped `p`-th moment, with the cut-off weight as a parameter.**
This is `hasDerivAt_capped_moment_cutoff` with the (large) explicit edge weight replaced by a
parameter `cw` together with its defining equation `hcw`; nothing about the model changes. -/
theorem hasDerivAt_capped_moment_cutoff_of_weight {d : ℕ} {N : ModelNorm (Fin d → ℝ)}
    {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p n : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r) :
    HasDerivAt (fun s => ∫ ω, (min (n : ℝ≥0∞) (((cluster ω o).encard : ℝ≥0∞) ^ p)).toReal
        ∂(law (intensityProfile (cutoffKernel N K s) β)))
      (∑' e, cw r e *
        (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
          min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
          ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal) r :=
  (hasDerivAt_capped_moment_cutoff hKa hK' hK'c β p n hp o hχ hr hrR hcorner).congr_deriv
    (tsum_congr fun e => by rw [hcw])

/-- **The cap passage for the cut-off family, with the edge weight as a parameter.**

This is the conclusion of `hasDerivAt_integral_pow_of_cap_flux` for the cut-off law
`r ↦ law (intensityProfile (cutoffKernel N K r) β)`: the uncapped `p`-th cluster moment
`r ↦ E |K_o|^p` is differentiable at `r₀` with derivative the infinite pivotal flux series.

The cut-off edge weight `cw` and its defining equation `hcw` are explicit parameters so that no
large series expression has to be beta-reduced during elaboration. Assumptions kept as inputs:
the all-pairs dominator `hKd` with its interval integrability, the per-edge finiteness of the
inserted cluster and of the pivotal flux, the finite `p`-th moment, and the a.e. strong
measurability of the capped flux and the continuity of the uncapped flux in the parameter.
In particular `hcont` is an input: it is *not* discharged by `continuousOn_flux_cutoff`, which
only applies to bounded observables and hence not to the untruncated `p`-th moment. -/
theorem hasDerivAt_integral_cutoff_pow {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {R : ℝ}
    (hχ : chi (intensityProfile (cutoffKernel N K R) β) o ≠ ⊤)
    (cw : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hcw : ∀ r e, cw r e = (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel N K r e : ℝ))))
    {u v r₀ : ℝ} (hu : 0 < u) (hur : u < r₀) (hrv : r₀ < v) (hvR : v ≤ R)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v)
    (hmom : ∀ r ∈ Ioo u v, (∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p)
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (hfin : ∀ r ∈ Ioo u v, ∀ e, ∀ᵐ ω ∂(law (intensityProfile (cutoffKernel N K r) β)),
      ((cluster (insert e ω) o).encard : ℝ≥0∞) ≠ ⊤)
    (hflux : ∀ r ∈ Ioo u v, ∀ e, (∫⁻ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p)
      ∂(law (intensityProfile (cutoffKernel N K r) β))) ≠ ⊤)
    (Kd : ℝ → ℝ) (hKdint : ∀ a ∈ Ioo u v, ∀ b ∈ Ioo u v, IntervalIntegrable Kd volume a b)
    (hKd : ∀ r ∈ Ioo u v, ∀ S : Finset (Sym2 (Fin d → ℤ)), ∑ e ∈ S, |cw r e| *
      |∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))| ≤ Kd r)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun r => ∑' e, cw r e *
      (∫⁻ ω, (min (n : ℝ≥0∞) (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p) -
        min (n : ℝ≥0∞) (((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p))
        ∂(law (intensityProfile (cutoffKernel N K r) β))).toReal)
      (volume.restrict (Ioo u v)))
    (hcont : ContinuousOn (fun r => ∑' e, cw r e *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β))) (Ioo u v)) :
    HasDerivAt (fun r => ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel N K r) β)))
      (∑' e, cw r₀ e *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel N K r₀) β))) r₀ :=
  hasDerivAt_integral_pow_of_cap_flux (V := Fin d → ℤ)
    (q := fun r => intensityProfile (cutoffKernel N K r) β) (c := cw) (o := o) (p := p)
    (u := u) (v := v) (r₀ := r₀) (Kd := Kd) hur hrv hKdint hKd hfin hflux hmom
    (fun n r hr => hasDerivAt_capped_moment_cutoff_of_weight (N := N) (K := K) (K' := K')
      hKa hK' hK'c β p n hp o hχ cw hcw (hu.trans hr.1) (hr.2.trans_le hvR)
      (fun z hz => hcorner z (by
        simpa only [hz] using (show r ∈ Ioo u v from ⟨hr.1, hr.2⟩))))
    hmeas hcont

/-- **Non-vacuity of the cap passage.** On the one-vertex type `Unit` every cluster is the
whole vertex set, so with zero weights `c = 0`, zero dominator `Kd = 0` and an arbitrary bond
law family `q`, every hypothesis of `hasDerivAt_integral_pow_of_cap_flux` holds:

* the uncapped `p = 1` moment is the constant `1` (so finite);
* every pivotal increment vanishes identically, so the pivotal fluxes are `0`;
* hence the uncapped flux series and all capped flux series are the constant `0`, which is
  bounded by `Kd = 0`, a.e. strongly measurable and continuous;
* the capped moment `s ↦ E[min (|K_()|^1) n]` is the constant `min n 1`, whose derivative is
  `0`, i.e. the capped pivotal series.

The conclusion is therefore the genuine differentiability statement for the (constant) `p`-th
moment of the single-vertex model, with derivative `0` equal to the pivotal flux series. -/
theorem nonvacuous_cap_flux (q : ℝ → Sym2 Unit → unitInterval) :
    HasDerivAt (fun r => ∫ ω : Config Unit, (((cluster ω ()).encard : ℝ≥0∞) ^ 1).toReal
        ∂(law (q r)))
      (∑' e : Sym2 Unit, (0 : ℝ) * ∫ ω : Config Unit,
        ((((cluster (insert e ω) ())).encard : ℝ≥0∞) ^ 1 -
          ((((cluster (ω \ {e}) ())).encard : ℝ≥0∞)) ^ 1).toReal ∂(law (q 1))) 1 := by
  have hcl : ∀ (ω : Config Unit) (x : Unit), ((cluster ω x).encard : ℝ≥0∞) = 1 := by
    intro ω x
    have h : cluster ω x = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      simpa only [Subsingleton.elim y x] using mem_cluster_self ω x
    rw [h]
    simp
  have hzero : ∀ (r : ℝ) (e : Sym2 Unit),
      (∫⁻ ω : Config Unit, ((((cluster (insert e ω) ())).encard : ℝ≥0∞) ^ 1 -
        ((((cluster (ω \ {e}) ())).encard : ℝ≥0∞)) ^ 1) ∂(law (q r))) = 0 := by
    intro r e
    refine lintegral_eq_zero_iff ?_ |>.2 (Eventually.of_forall fun ω => ?_)
    · exact (measurable_pivotal e () 1)
    · simp only [hcl]
      simp
  refine hasDerivAt_integral_pow_of_cap_flux (V := Unit) (q := q) (c := fun _ _ => (0 : ℝ))
    (o := ()) (p := 1) (u := 0) (v := 2) (r₀ := 1) (Kd := fun _ => 0)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ => intervalIntegrable_const
  · intro r _ S
    simp
  · intro r _ e
    filter_upwards with ω
    simp only [hcl]
    exact (by simp : ((1 : ℝ≥0∞)) ≠ ⊤)
  · intro r _ e
    rw [hzero r e]
    simp
  · intro r _
    have hone : ∀ ω : Config Unit, ((cluster ω ()).encard : ℝ≥0∞) ^ 1 = 1 := by
      intro ω
      rw [hcl ω ()]
      simp
    simp only [hone]
    simp
  · intro n r _
    have hconst : (fun s => ∫ ω : Config Unit,
        (min (n : ℝ≥0∞) ((((cluster ω ()).encard : ℝ≥0∞)) ^ 1)).toReal ∂(law (q s)))
        = fun _ => (min (n : ℝ≥0∞) 1).toReal := by
      funext s
      have hone : ∀ ω : Config Unit, ((cluster ω ()).encard : ℝ≥0∞) ^ 1 = 1 := by
        intro ω
        rw [hcl ω ()]
        simp
      simp only [hone]
      rw [integral_const]
      simp
    rw [hconst]
    simpa using hasDerivAt_const (x := r) (c := (min (n : ℝ≥0∞) 1).toReal)
  · intro n
    simpa only [zero_mul, tsum_zero] using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (volume.restrict (Ioo (0 : ℝ) 2)))
  · simpa only [zero_mul, tsum_zero] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo (0 : ℝ) 2))

end PercLib.Models.LongRange

/-! ## L1 convergence of weighted series

Pointwise dominated convergence of weighted series is supplemented by an absolute
L1 estimate for their differences, using the same summability input.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PercLib.Analysis

/-- Weighted L1 convergence gives convergence of a real weighted series. -/
theorem tendsto_tsum_of_l1_dominated {ι : Type*} [Countable ι]
    {f : ℕ → ι → ℝ} {g w : ι → ℝ}
    (hsum : Summable fun e => |w e| * |g e|)
    (hconv : ∀ e, Tendsto (fun n => f n e) atTop (𝓝 (g e)))
    (hle : ∀ n e, |f n e| ≤ |g e|) :
    Tendsto (fun n => ∑' e, w e * f n e) atTop (𝓝 (∑' e, w e * g e)) := by
  have hbound : ∀ n e, |w e * f n e - w e * g e| ≤ 2 * (|w e| * |g e|) := by
    intro n e
    calc |w e * f n e - w e * g e| ≤ |w e * f n e| + |w e * g e| := abs_sub _ _
      _ = |w e| * |f n e| + |w e| * |g e| := by rw [abs_mul, abs_mul]
      _ ≤ |w e| * |g e| + |w e| * |g e| := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left (hle n e) (abs_nonneg _)) _
      _ = 2 * (|w e| * |g e|) := by ring
  have hs2 : Summable fun e => 2 * (|w e| * |g e|) := hsum.mul_left 2
  have hconv0 : ∀ e, Tendsto (fun n => |w e * f n e - w e * g e|) atTop (𝓝 0) := by
    intro e
    have h := ((hconv e).const_mul (w e)).sub_const (w e * g e)
    simpa using h.abs
  have hnorm : ∀ n, Summable fun e => |w e * f n e - w e * g e| := by
    intro n
    exact Summable.of_nonneg_of_le (fun e => abs_nonneg _) (hbound n) hs2
  have hl1 : Tendsto (fun n => ∑' e, |w e * f n e - w e * g e|) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hs2 hconv0
      (Eventually.of_forall fun n e => by
        simpa only [Real.norm_eq_abs, abs_abs] using hbound n e)
  have hf : ∀ n, Summable fun e => w e * f n e := by
    intro n
    exact hsum.of_norm_bounded fun e => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hle n e) (abs_nonneg _)
  have hg : Summable fun e => w e * g e := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs, abs_mul, abs_abs] using hsum
  have hnorm_sub : ∀ n, ‖(∑' e, w e * f n e) - ∑' e, w e * g e‖ ≤
      ∑' e, |w e * f n e - w e * g e| := by
    intro n
    rw [← (hf n).tsum_sub hg]
    calc ‖∑' e, (w e * f n e - w e * g e)‖
        ≤ ∑' e, ‖w e * f n e - w e * g e‖ := norm_tsum_le_tsum_norm
          (by simpa only [Real.norm_eq_abs] using hnorm n)
      _ = ∑' e, |w e * f n e - w e * g e| := by
        exact tsum_congr fun e => Real.norm_eq_abs _
  have hz : Tendsto (fun n => ‖(∑' e, w e * f n e) - ∑' e, w e * g e‖) atTop (𝓝 0) := by
    exact squeeze_zero (fun n => norm_nonneg _) hnorm_sub (by simpa using hl1)
  have hz' : Tendsto (fun n => (∑' e, w e * f n e) - ∑' e, w e * g e)
      atTop (𝓝 0) := by
    simpa only [Metric.tendsto_atTop, dist_eq_norm, sub_zero, norm_norm] using hz
  exact tendsto_sub_nhds_zero_iff.1 hz'

end PercLib.Analysis
