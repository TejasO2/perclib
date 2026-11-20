/-
Cutoff clusters and the exact omitted row on the hierarchical lattice, and the sharp
small-intensity bound. New proofs from the existing hierarchical geometry, the P-5/P-6
intensity theorems and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679's ENNReal
geometric series and graph reachability. No upstream code is copied.
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.IntensityScaling
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Cutoff clusters on the hierarchical lattice

The lattice is `ℕ →₀ (Fin d → ZMod L)`, the level of a displacement `z` is
`z.support.sup Nat.succ`, `N = L^d`, and the kernel is `J s(x,y) = C r^level(y − x)`.

* KL29 (a) `ae_cluster_subset_ball`: if the profile vanishes on pairs of level above `n`,
  almost surely every cluster lies in the level-`n` ball of its base vertex and has at most
  `N^n` points.
* KL29 (b) `tsum_level_gt_eq`: the kernel mass above level `n` is
  `C (N − 1) r / (1 − N r) · (N r)^n` (an identity in `ℝ≥0∞`, with no hypothesis).
* KL29 (c) `tsum_level_gt_intensity_le`: the omitted probability row of the exponential
  family is at most `β` times (b).
* B6KD (sharp form): with `M = C (N − 1) r / (1 − N r)` and `N r < 1`, the off-diagonal row
  of `J` is exactly `M`, so `β M < 1` gives `chi ≤ (1 − β M)⁻¹` and finite clusters, both
  thresholds are at least `M⁻¹`, and `M = 0` gives singleton clusters, `chi = 1` and
  infinite thresholds.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical
open PercLib.Percolation.Bond

/-! ### Clusters inside a host graph, allowing arbitrary loop probabilities -/

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- If the profile vanishes on every non-loop pair outside a graph `G`, then almost surely
the open graph is a subgraph of `G`. Loop probabilities are arbitrary. A corollary of
`ae_openGraph_le_support`. -/
theorem ae_openGraph_le_of_offDiagonal (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hq : ∀ x y, x ≠ y → ¬G.Adj x y → q s(x, y) = 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ G := by
  filter_upwards [ae_openGraph_le_support q] with ω hω
  intro x y hadj
  have h := hω hadj
  rw [SimpleGraph.fromEdgeSet_adj] at h
  by_contra hG
  have h0 : (0 : unitInterval) < q s(x, y) := h.1
  rw [hq x y h.2 hG] at h0
  exact lt_irrefl _ h0

/-- If the profile vanishes off the diagonal, almost surely every cluster is a singleton. -/
theorem ae_cluster_eq_singleton_of_offDiagonal (q : Sym2 V → unitInterval)
    (hq : ∀ x y, x ≠ y → q s(x, y) = 0) :
    ∀ᵐ ω ∂law q, ∀ x, cluster ω x = {x} := by
  filter_upwards [ae_openGraph_le_of_offDiagonal ⊥ q fun x y h _ => hq x y h] with ω hω
  intro x
  ext y
  constructor
  · intro hy
    exact (SimpleGraph.reachable_bot.1 (SimpleGraph.Reachable.mono hω hy)).symm
  · rintro rfl
    exact mem_cluster_self ω y

end PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-! ### KL29 (a): cutoff clusters lie in balls -/

omit [NeZero L] in
/-- Reachability in the graph of pairs of level at most `n` stays in the level-`n` ball. -/
theorem level_le_of_reachable (n : ℕ) {x y : ℕ →₀ (Fin d → ZMod L)}
    (h : (SimpleGraph.fromRel fun a b : ℕ →₀ (Fin d → ZMod L) =>
      (b - a).support.sup Nat.succ ≤ n).Reachable x y) :
    (y - x).support.sup Nat.succ ≤ n := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons a b c hab _ ih =>
    rw [SimpleGraph.fromRel_adj] at hab
    have hab' : (b - a).support.sup Nat.succ ≤ n := by
      rcases hab.2 with h | h
      · exact h
      · rwa [level_sub_comm]
    exact (level_sub_le_max a b c).trans (max_le hab' ih)

/-- The level-`n` ball around `x` has at most `N^n` points. -/
theorem encard_level_ball (x : ℕ →₀ (Fin d → ZMod L)) (n : ℕ) :
    {y : ℕ →₀ (Fin d → ZMod L) | (y - x).support.sup Nat.succ ≤ n}.encard =
      (((L ^ d) ^ n : ℕ) : ℕ∞) := by
  rw [level_ball_eq_translate, (add_right_injective x).encard_image,
    ← (finite_level_ball n).cast_ncard_eq, ← Nat.card_coe_set_eq]
  congr 1
  exact card_ball n

/-- **KL29 (a).** If the profile vanishes on every pair of level above `n` (only bonds of
level at most `n` are retained), then almost surely every cluster lies in the level-`n`
ball of its base vertex, so its volume is at most `N^n`. Loop probabilities are
arbitrary. -/
theorem ae_cluster_subset_ball (q : Sym2 (ℕ →₀ (Fin d → ZMod L)) → unitInterval) (n : ℕ)
    (hq : ∀ x y, n < (y - x).support.sup Nat.succ → q s(x, y) = 0) :
    ∀ᵐ ω ∂law q, ∀ x, cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} ∧
      (cluster ω x).encard ≤ (((L ^ d) ^ n : ℕ) : ℕ∞) := by
  let G := SimpleGraph.fromRel fun a b : ℕ →₀ (Fin d → ZMod L) =>
    (b - a).support.sup Nat.succ ≤ n
  have hG : ∀ x y, x ≠ y → ¬G.Adj x y → q s(x, y) = 0 := fun x y hxy hadj => by
    refine hq x y (not_le.1 fun h => hadj ?_)
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hxy, Or.inl h⟩
  filter_upwards [ae_openGraph_le_of_offDiagonal G q hG] with ω hω
  intro x
  have hsub : cluster ω x ⊆ {y | (y - x).support.sup Nat.succ ≤ n} := fun y hy =>
    level_le_of_reachable n (SimpleGraph.Reachable.mono hω hy)
  exact ⟨hsub, (Set.encard_le_encard hsub).trans_eq (encard_level_ball x n)⟩

/-! ### KL29 (b), (c): the omitted row -/

/-- **KL29 (b).** The kernel mass above level `n` is `C (N − 1) r / (1 − N r) · (N r)^n`.
In `ℝ≥0∞` this holds with no hypothesis on `N r`. -/
theorem tsum_level_gt_eq (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ)) (n : ℕ)
    (x : ℕ →₀ (Fin d → ZMod L)) :
    (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
      (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
        ((L : ℝ≥0∞) ^ d * r) ^ n := by
  set ρ : ℝ≥0∞ := (L : ℝ≥0∞) ^ d * r
  set a : ℝ≥0∞ := (C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r
  have h1 : (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
      ∑' z : ℕ →₀ (Fin d → ZMod L), (fun m : ℕ => if n < m then
        (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ m else 0) (z.support.sup Nat.succ) := by
    rw [← (Equiv.addLeft x).tsum_eq]
    refine tsum_congr fun z => ?_
    simp [hJ]
  rw [h1, tsum_radial_eq (d := d) (L := L) (fun m : ℕ => if n < m then
    (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ m else 0)]
  have hcard (k : ℕ) : (L ^ d) ^ (k + 1) - (L ^ d) ^ k = (L ^ d - 1) * (L ^ d) ^ k := by
    rw [pow_succ, Nat.mul_sub_right_distrib, one_mul, mul_comm]
  simp only [Nat.not_lt_zero, ite_false, zero_add, hcard]
  have h2 : ∀ k : ℕ, (((L ^ d - 1) * (L ^ d) ^ k : ℕ) : ℝ≥0∞) *
      (if n < k + 1 then (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (k + 1) else 0) =
      if n ≤ k then a * ρ ^ k else 0 := by
    intro k
    by_cases hk : n ≤ k
    · rw [ite_eq_left (by omega), ite_eq_left hk]
      simp only [a, ρ]
      push_cast
      ring
    · rw [ite_eq_right (by omega), ite_eq_right hk, mul_zero]
  simp_rw [h2]
  have h3 : (∑' k : ℕ, if n ≤ k then a * ρ ^ k else 0) =
      ∑' j : ℕ, (fun k : ℕ => if n ≤ k then a * ρ ^ k else 0) (j + n) := by
    refine ((add_left_injective n).tsum_eq fun k hk => ?_).symm
    have hk' : n ≤ k := by
      by_contra h
      exact hk (by simp [h])
    exact ⟨k - n, by simp only; omega⟩
  rw [h3]
  simp only [Nat.le_add_left, ite_true, pow_add]
  rw [ENNReal.tsum_mul_left]
  simp_rw [mul_comm (ρ ^ _) (ρ ^ n)]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]
  ring

/-- **KL29 (c).** In the exponential family the omitted probability row above level `n` is
at most `β` times the omitted kernel mass. -/
theorem tsum_level_gt_intensity_le (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ)) (β : ℝ≥0) (n : ℕ)
    (x : ℕ →₀ (Fin d → ZMod L)) :
    (∑' y, if n < (y - x).support.sup Nat.succ then
        (unitInterval.toNNReal (intensityProfile J β s(x, y)) : ℝ≥0∞) else 0) ≤
      (β : ℝ≥0∞) * ((C : ℝ≥0∞) * ((L ^ d - 1 : ℕ) : ℝ≥0∞) * r / (1 - (L : ℝ≥0∞) ^ d * r) *
        ((L : ℝ≥0∞) ^ d * r) ^ n) := by
  rw [← tsum_level_gt_eq J C r hJ n x, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs
  · rw [← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β _)
  · simp

/-! ### B6KD, sharp form -/

/-- With `N r < 1`, the off-diagonal row of the hierarchical kernel is exactly
`M = C (N − 1) r / (1 − N r)`. -/
theorem rowSum_hierarchical_eq (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (v : ℕ →₀ (Fin d → ZMod L)) :
    (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) =
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) := by
  have h := tsum_level_gt_eq J C r hJ 0 v
  rw [pow_zero, mul_one] at h
  have e : (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) =
      ∑' w, if 0 < (w - v).support.sup Nat.succ then (J s(v, w) : ℝ≥0∞) else 0 := by
    refine tsum_congr fun w => ?_
    by_cases hw : w = v
    · simp [hw]
    · have : 0 < (w - v).support.sup Nat.succ :=
        Nat.pos_of_ne_zero fun h0 => hw ((level_sub_eq_zero_iff v w).1 h0).symm
      simp [hw, this]
  rw [e, h]
  have hne : (1 - (L : ℝ≥0) ^ d * r) ≠ 0 := (tsub_pos_of_lt hr).ne'
  rw [ENNReal.coe_div hne]
  push_cast
  rfl

/-- **B6KD, susceptibility.** With `N r < 1` and `β M < 1`, `chi ≤ (1 − β M)⁻¹`. -/
theorem chi_intensity_le_hierarchical_sharp (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : ℕ →₀ (Fin d → ZMod L)) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  chi_intensity_le J _ (fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le) β hβ x

/-- **B6KD, finiteness.** With `N r < 1` and `β M < 1`, almost surely every cluster is
finite. -/
theorem law_exists_infinite_hierarchical_eq_zero (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) *
      ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞) < 1) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0 :=
  law_exists_infinite_intensity_eq_zero J _
    (fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le) β hβ

/-- **B6KD, global threshold.** With `N r < 1`, the global threshold is at least `M⁻¹`
(and is `⊤` when `M = 0`). -/
theorem inv_le_globalCriticalIntensity_hierarchical_sharp
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) :
    ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      globalCriticalIntensity J :=
  inv_le_globalCriticalIntensity J _ fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le

/-- **B6KD, root threshold.** With `N r < 1`, every root threshold is at least `M⁻¹`. -/
theorem inv_le_rootCriticalIntensity_hierarchical_sharp
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1) (x : ℕ →₀ (Fin d → ZMod L)) :
    ((C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      rootCriticalIntensity J x :=
  inv_le_rootCriticalIntensity J _ (fun v => by convert (rowSum_hierarchical_eq J C r hJ hr v).le) x

/-- **B6KD, `M = 0`.** With `N r < 1` and `M = 0`: at every parameter every cluster is
almost surely a singleton, `chi = 1`, and both thresholds are `⊤`. -/
theorem hierarchical_of_M_eq_zero (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r < 1)
    (hM : C * ((L ^ d - 1 : ℕ) : ℝ≥0) * r / (1 - (L : ℝ≥0) ^ d * r) = 0) (β : ℝ≥0) :
    (∀ᵐ ω ∂law (intensityProfile J β), ∀ x, cluster ω x = {x}) ∧
      (∀ x, chi (intensityProfile J β) x = 1) ∧
      globalCriticalIntensity J = ⊤ ∧ ∀ x, rootCriticalIntensity J x = ⊤ := by
  have hrow0 : ∀ v, (∑' w, if w = v then 0 else (J s(v, w) : ℝ≥0∞)) ≤ 0 := fun v => by
    rw [rowSum_hierarchical_eq J C r hJ hr v, hM, ENNReal.coe_zero]
  have hrow : ∀ v, (∑' w, @ite _ (w = v) (Classical.propDecidable _) 0 (J s(v, w) : ℝ≥0∞)) ≤
      0 := fun v => by convert hrow0 v
  refine ⟨ae_cluster_eq_singleton_of_offDiagonal _ fun x y hxy => ?_,
    chi_intensity_eq_one_of_rowSum_zero J hrow β,
    globalCriticalIntensity_eq_top_of_rowSum_zero J hrow,
    rootCriticalIntensity_eq_top_of_rowSum_zero J hrow⟩
  refine intensityProfile_eq_zero_of_eq_zero J ?_ β
  have h0 := ENNReal.tsum_eq_zero.1 (nonpos_iff_eq_zero.1 (hrow x)) y
  rw [ite_eq_right (Ne.symm hxy), ENNReal.coe_eq_zero] at h0
  exact h0

end PercLib.Models

/-! ### Non-vacuity witnesses (D-5) -/
section Witnesses

open PercLib.Models

/-- `L = 2, d = 1, C = 1, r = 1/4`: `N r = 1/2` and `M = 1/2`. At `β = 1` the
susceptibility is at most `2`, clusters are almost surely finite, both thresholds are at
least `2`, and the omitted kernel mass above level `n` is `2⁻¹ · 2⁻ⁿ`. -/
example (x : ℕ →₀ (Fin 1 → ZMod 2)) (n : ℕ) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
      (1 * ((2 ^ 1 - 1 : ℕ) : ℝ≥0) * (1 / 4) / (1 - (2 : ℝ≥0) ^ 1 * (1 / 4)) : ℝ≥0) = 1 / 2 ∧
      chi (intensityProfile J 1) x ≤ (1 - ((1 : ℝ≥0) : ℝ≥0∞) * ((1 / 2 : ℝ≥0) : ℝ≥0∞))⁻¹ ∧
      law (intensityProfile J 1) {ω | ∃ x, (cluster ω x).Infinite} = 0 ∧
      ((1 / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
      (∑' y, if n < (y - x).support.sup Nat.succ then (J s(x, y) : ℝ≥0∞) else 0) =
        ((1 : ℝ≥0) : ℝ≥0∞) * ((2 ^ 1 - 1 : ℕ) : ℝ≥0∞) * ((1 / 4 : ℝ≥0) : ℝ≥0∞) /
          (1 - ((2 : ℕ) : ℝ≥0∞) ^ 1 * ((1 / 4 : ℝ≥0) : ℝ≥0∞)) *
          (((2 : ℕ) : ℝ≥0∞) ^ 1 * ((1 / 4 : ℝ≥0) : ℝ≥0∞)) ^ n := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  have hr : ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4) < 1 := by norm_num
  have hM : (1 * ((2 ^ 1 - 1 : ℕ) : ℝ≥0) * (1 / 4) / (1 - (2 : ℝ≥0) ^ 1 * (1 / 4)) : ℝ≥0) =
      1 / 2 := by
    rw [show (2 : ℝ≥0) ^ 1 * (1 / 4) = 1 / 2 by norm_num,
      show (1 : ℝ≥0) - 1 / 2 = 1 / 2 by
        rw [← NNReal.coe_inj]; rw [NNReal.coe_sub (by norm_num)]; norm_num]
    norm_num
  have hM' : (1 * ((2 ^ 1 - 1 : ℕ) : ℝ≥0) * (1 / 4) / (1 - ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4)) :
      ℝ≥0) = 1 / 2 := by exact_mod_cast hM
  have hβ : ((1 : ℝ≥0) : ℝ≥0∞) * ((1 / 2 : ℝ≥0) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]; norm_num
  refine ⟨J, hM, ?_, ?_, ?_, tsum_level_gt_eq J 1 (1 / 4) hJ n x⟩
  · have := chi_intensity_le_hierarchical_sharp J 1 (1 / 4) hJ hr 1 (by rw [hM']; exact hβ) x
    rwa [hM'] at this
  · exact law_exists_infinite_hierarchical_eq_zero J 1 (1 / 4) hJ hr 1 (by rw [hM']; exact hβ)
  · have := inv_le_globalCriticalIntensity_hierarchical_sharp J 1 (1 / 4) hJ hr
    rwa [hM'] at this

/-- `C = 0`: `M = 0`, so every cluster is almost surely a singleton, `chi = 1` and the
thresholds are `⊤`. -/
example (β : ℝ≥0) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0,
      (∀ᵐ ω ∂PercLib.Percolation.Bond.law (intensityProfile J β), ∀ x, cluster ω x = {x}) ∧
      globalCriticalIntensity J = ⊤ := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 0 (1 / 4)
  have hr : ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4) < 1 := by norm_num
  obtain ⟨h1, -, h3, -⟩ := hierarchical_of_M_eq_zero J 0 (1 / 4) hJ hr (by simp) β
  exact ⟨J, h1, h3⟩

end Witnesses
