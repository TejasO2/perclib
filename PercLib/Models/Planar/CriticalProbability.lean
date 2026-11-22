/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: B. Bollobás and O. Riordan, A short proof of the Harris-Kesten theorem,
Bull. London Math. Soc. 38 (2006), 470-484 (arXiv math/0410359v3), Theorem 8; H. Kesten, The
critical probability of bond percolation on the square lattice equals 1/2, Comm. Math. Phys. 74
(1980), 41-59.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import PercLib.Models.Planar.KestenBound
public import PercLib.Models.Planar.RSW
public import PercLib.Percolation.Bond.DomainIndependence
public import PercLib.Percolation.Bond.Host
public import PercLib.Percolation.Bond.IntensityMonotone
public import PercLib.Probability.HarrisDecreasing

/-!
# Harris's theorem and the critical probability of `ℤ²`

Nearest-neighbour bond percolation on `ℤ²` has no infinite cluster at the self-dual point, where
every edge is open with probability `1/2` (Harris's theorem), and with Kesten's bound of
`KestenBound.lean` its critical probability is `1/2`: in the intensity parametrisation of the
library, with kernel `J = (zdGraph 2).edgeSet.indicator 1` and edge probability `1 - e^{-β}`,
the critical intensity is `log 2`.

* **Blocking** (`notMem_localConn_of_notMem_crossing`). Around the annulus
  `s ≤ ‖·‖∞ ≤ 3s` lie four strips, `[-3s, 3s] × [s, 3s]` and its images under quarter-turns.
  If none of them has an open crossing in its short direction, no open path joins a vertex with
  `‖·‖∞ ≤ s` to a vertex with `‖·‖∞ ≥ 3s`: follow such a path to its first vertex at sup norm
  `3s`; a segment of it then crosses one strip in its short direction. Walk combinatorics only.
* **The blocking probability** (`exists_pos_le_law_blocking`). At `1/2`, the four complements
  are decreasing events, each with the probability of a left-right crossing of
  `[0, 6s + 1] × [0, 2s - 1]` (vertical duality, `law_compl_crossing_one_eq`), which is at least a
  constant by RSW (`exists_pos_le_law_crossing`). Harris's inequality for decreasing events gives
  a lower bound uniform in `s ≥ 1`.
* **Harris's theorem** (`law_cluster_infinite_eq_zero_of_half`,
  `law_exists_cluster_infinite_eq_zero_of_half`). The blocking events at the scales `4^j` are
  determined by the edges inside the disjoint annuli `4^j ≤ ‖·‖∞ ≤ 3 · 4^j`, hence independent;
  an infinite cluster of the origin defeats all of them, so `θ(1/2) ≤ (1 - c)^J` for every `J`.
* **Intensity form** (`law_cluster_infinite_intensityProfile_eq_zero`,
  `law_exists_cluster_infinite_intensityProfile_eq_zero`): `θ(β) = 0` for every `β ≤ log 2`, by
  monotonicity in the intensity.
* **The critical probability** (`rootCriticalIntensity_indicator_edgeSet_eq_log_two`,
  `globalCriticalIntensity_indicator_edgeSet_eq_log_two`): `β_c = log 2`, that is
  `p_c(ℤ²) = 1/2`. The lower bound is the intensity form of Harris's theorem, the upper bound is
  Kesten's bound.

This is Theorem 8 of Bollobás and Riordan, with strips in place of their annuli of circuits, as
in the planar crossing section of the wiki; the upper bound uses sharpness, as there, instead of
the Friedgut–Kalai theorem used by Bollobás and Riordan.

## Main results

* `PercLib.Models.Planar.notMem_localConn_of_notMem_crossing`
* `PercLib.Models.Planar.exists_pos_le_law_blocking`
* `PercLib.Models.Planar.law_cluster_infinite_eq_zero_of_half`
* `PercLib.Models.Planar.law_exists_cluster_infinite_eq_zero_of_half`
* `PercLib.Models.Planar.law_cluster_infinite_intensityProfile_eq_zero`
* `PercLib.Models.Planar.law_exists_cluster_infinite_intensityProfile_eq_zero`
* `PercLib.Models.Planar.rootCriticalIntensity_indicator_edgeSet_eq_log_two`
* `PercLib.Models.Planar.globalCriticalIntensity_indicator_edgeSet_eq_log_two`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Percolation.Bond PercLib.Models.Site
  PercLib.Probability
open scoped ENNReal NNReal

/-! ### Walks between two levels -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **A connection between two levels.** If a function changes by at most one along each open
edge, an open walk inside `T` from level at most `s` to level at least `t ≥ s` yields an open
connection, inside `T` and between the two levels, from a vertex at level `s` to a vertex at
level `t`. -/
theorem exists_mem_localConn_of_walk {ω : Config V} (f : V → ℤ)
    (hf : ∀ u v, (openGraph ω).Adj u v → f v ≤ f u + 1) {T : Set V} {a b : V}
    (p : (openGraph ω).Walk a b) (hp : ∀ v ∈ p.support, v ∈ T) {s t : ℤ} (ha : f a ≤ s)
    (hst : s ≤ t) (hb : t ≤ f b) :
    ∃ u w, f u = s ∧ f w = t ∧ ω ∈ localConn (T ∩ {v | s ≤ f v ∧ f v ≤ t}) u w := by
  obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc f hf p ha hst hb
  exact ⟨u, w, hu, hw, mem_localConn_iff_exists_walk.2
    ⟨q, fun v hv => ⟨hp v (hq v hv).1, (hq v hv).2⟩⟩⟩

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

/-! ### Crossings determined by the edges of a region -/

/-- A crossing of a box is determined by the pairs inside any region containing the box. -/
theorem mem_crossing_iff_of_inter_eq {d : ℕ} {i : Fin d} {lo hi : LatticeSite d}
    {T : Set (LatticeSite d)} (hT : Icc lo hi ⊆ T) {ω ω' : Config (LatticeSite d)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ crossing i lo hi ↔ ω' ∈ crossing i lo hi := by
  have hagree : ∀ a b : LatticeSite d, a ∈ Icc lo hi → b ∈ Icc lo hi →
      (ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b ↔
        ω' ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b) := by
    intro a b ha hb
    rw [mem_localConn_iff_reachable ha hb, mem_localConn_iff_reachable ha hb]
    refine localConn_iff_of_agree (Icc lo hi) ⟨a, ha⟩ ⟨b, hb⟩ fun x hx y hy => ?_
    have hxy : s(x, y) ∈ {e : Sym2 (LatticeSite d) | ∀ v ∈ e, v ∈ T} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hT hx
      · exact hT hy
    have hmem := congrArg (s(x, y) ∈ ·) h
    simp only [eq_iff_iff, mem_inter_iff] at hmem
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨(hmem.1 ⟨h₁, hxy⟩).1, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨(hmem.2 ⟨h₁, hxy⟩).1, h₂⟩
  constructor
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    exact ⟨a, ha, hai, b, hb, hbi, (hagree a b ha hb).1 hab⟩
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    exact ⟨a, ha, hai, b, hb, hbi, (hagree a b ha hb).2 hab⟩

/-! ### Blocking -/

/-- One step of the open graph of `ω ∩ L` changes the sup norm `max |v 0| |v 1|` by at most
one. -/
theorem max_abs_le_add_one_of_adj {ω : Config (LatticeSite 2)} {u v : LatticeSite 2}
    (h : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj u v) :
    max |v 0| |v 1| ≤ max |u 0| |u 1| + 1 := by
  have h0 := coord_le_add_one_of_adj h 0
  have h0' := coord_le_add_one_of_adj h.symm 0
  have h1 := coord_le_add_one_of_adj h 1
  have h1' := coord_le_add_one_of_adj h.symm 1
  have hu0 : |u 0| ≤ max |u 0| |u 1| := le_max_left _ _
  have hu1 : |u 1| ≤ max |u 0| |u 1| := le_max_right _ _
  rw [abs_le] at hu0 hu1
  exact max_le (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 ⟨by omega, by omega⟩)

/-- **Blocking** (wiki WD31, Step 6, deterministic part). If none of the four strips around the
annulus `s ≤ ‖·‖∞ ≤ 3s`, the strip `[-3s, 3s] × [s, 3s]` and its images under quarter-turns,
has an open crossing in its short direction, then no open path joins a vertex with
`‖·‖∞ ≤ s` to a vertex with `‖·‖∞ ≥ 3s`, inside any set `S`. -/
theorem notMem_localConn_of_notMem_crossing {ω : Config (LatticeSite 2)} {s : ℕ}
    (hT : ω ∉ crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])
    (hB : ω ∉ crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])
    (hR : ω ∉ crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])
    (hL : ω ∉ crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])
    {a v : LatticeSite 2} (ha : |a 0| ≤ s ∧ |a 1| ≤ s) (hv : 3 * s ≤ |v 0| ∨ 3 * s ≤ |v 1|)
    (S : Set (LatticeSite 2)) : ω ∩ (zdGraph 2).edgeSet ∉ localConn S a v := by
  intro hav
  obtain ⟨p, -⟩ := mem_localConn_iff_exists_walk.1 hav
  obtain ⟨ha0, ha1⟩ := ha
  rw [abs_le] at ha0 ha1
  -- the first vertex of the path at sup norm `3s`
  have hfa : max |a 0| |a 1| ≤ 3 * (s : ℤ) :=
    max_le (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 ⟨by omega, by omega⟩)
  have hfv : 3 * (s : ℤ) ≤ max |v 0| |v 1| := by
    rcases hv with hv | hv
    · exact hv.trans (le_max_left _ _)
    · exact hv.trans (le_max_right _ _)
  obtain ⟨c, hc, q, hq⟩ := SimpleGraph.Walk.exists_walk_eq_of_le
    (fun w : LatticeSite 2 => max |w 0| |w 1|) (fun u w h => max_abs_le_add_one_of_adj h) p
    hfa hfv
  -- the path up to `c` stays in the box `[-3s, 3s]²`
  set T : Set (LatticeSite 2) := Icc ![-3 * (s : ℤ), -3 * s] ![3 * s, 3 * s] with hTdef
  have hqT : ∀ w ∈ q.support, w ∈ T := by
    intro w hw
    obtain ⟨hw0, hw1⟩ := max_le_iff.1 (hq w hw).2
    rw [abs_le] at hw0 hw1
    rw [hTdef, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hc' : c 0 = 3 * s ∨ c 0 = -(3 * s) ∨ c 1 = 3 * s ∨ c 1 = -(3 * s) := by
    have hc'' : max |c 0| |c 1| = 3 * s := hc
    rcases le_total |c 0| |c 1| with h | h
    · rw [max_eq_right h] at hc''
      rcases abs_eq (by positivity : (0 : ℤ) ≤ 3 * s) |>.1 hc'' with h' | h' <;> omega
    · rw [max_eq_left h] at hc''
      rcases abs_eq (by positivity : (0 : ℤ) ≤ 3 * s) |>.1 hc'' with h' | h' <;> omega
  rcases hc' with hc' | hc' | hc' | hc'
  · -- `c` on the right side: the right strip is crossed from left to right
    obtain ⟨u, w, hu, hw, huw⟩ := exists_mem_localConn_of_walk (fun v => v 0)
      (fun u v h => coord_le_add_one_of_adj h 0) q hqT (s := s) (t := 3 * s) (by omega)
      (by omega) (by omega)
    have hsub : T ∩ {v | (s : ℤ) ≤ v 0 ∧ v 0 ≤ 3 * s} ⊆
        Icc ![(s : ℤ), -3 * s] ![3 * s, 3 * s] := by
      rintro x ⟨hx, hx'⟩
      rw [hTdef, mem_Icc_two_iff] at hx
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq] at hx hx' ⊢
      omega
    exact hR ⟨u, hsub huw.1, by simpa using hu, w, hsub huw.2.1, by simpa using hw,
      localConn_mono_set hsub _ _ huw⟩
  · -- `c` on the left side: the left strip is crossed from right to left
    obtain ⟨u, w, hu, hw, huw⟩ := exists_mem_localConn_of_walk (fun v => -v 0)
      (fun u v h => by have := coord_le_add_one_of_adj h.symm 0; omega) q hqT (s := s)
      (t := 3 * s) (by omega) (by omega) (by omega)
    have hsub : T ∩ {v | (s : ℤ) ≤ -v 0 ∧ -v 0 ≤ 3 * s} ⊆
        Icc ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s] := by
      rintro x ⟨hx, hx'⟩
      rw [hTdef, mem_Icc_two_iff] at hx
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq] at hx hx' ⊢
      omega
    rw [localConn_comm] at huw
    exact hL ⟨w, hsub huw.1, by simp only [Matrix.cons_val_zero]; omega, u, hsub huw.2.1,
      by simp only [Matrix.cons_val_zero]; omega, localConn_mono_set hsub _ _ huw⟩
  · -- `c` on the top side: the top strip is crossed from bottom to top
    obtain ⟨u, w, hu, hw, huw⟩ := exists_mem_localConn_of_walk (fun v => v 1)
      (fun u v h => coord_le_add_one_of_adj h 1) q hqT (s := s) (t := 3 * s) (by omega)
      (by omega) (by omega)
    have hsub : T ∩ {v | (s : ℤ) ≤ v 1 ∧ v 1 ≤ 3 * s} ⊆
        Icc ![-3 * (s : ℤ), s] ![3 * s, 3 * s] := by
      rintro x ⟨hx, hx'⟩
      rw [hTdef, mem_Icc_two_iff] at hx
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq] at hx hx' ⊢
      omega
    exact hT ⟨u, hsub huw.1, by simpa using hu, w, hsub huw.2.1, by simpa using hw,
      localConn_mono_set hsub _ _ huw⟩
  · -- `c` on the bottom side: the bottom strip is crossed from top to bottom
    obtain ⟨u, w, hu, hw, huw⟩ := exists_mem_localConn_of_walk (fun v => -v 1)
      (fun u v h => by have := coord_le_add_one_of_adj h.symm 1; omega) q hqT (s := s)
      (t := 3 * s) (by omega) (by omega) (by omega)
    have hsub : T ∩ {v | (s : ℤ) ≤ -v 1 ∧ -v 1 ≤ 3 * s} ⊆
        Icc ![-3 * (s : ℤ), -3 * s] ![3 * s, -s] := by
      rintro x ⟨hx, hx'⟩
      rw [hTdef, mem_Icc_two_iff] at hx
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq] at hx hx' ⊢
      omega
    rw [localConn_comm] at huw
    exact hB ⟨w, hsub huw.1, by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega, u,
      hsub huw.2.1, by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega,
      localConn_mono_set hsub _ _ huw⟩

/-- **Blocking, cluster form.** If none of the four strips around the annulus
`s ≤ ‖·‖∞ ≤ 3s` has an open crossing in its short direction, the open cluster of every vertex
with `‖·‖∞ ≤ s` lies in the box `[1 - 3s, 3s - 1]²`. -/
theorem cluster_subset_Icc_of_notMem_crossing {ω : Config (LatticeSite 2)} {s : ℕ}
    (hT : ω ∉ crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])
    (hB : ω ∉ crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])
    (hR : ω ∉ crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])
    (hL : ω ∉ crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])
    {a : LatticeSite 2} (ha : |a 0| ≤ s ∧ |a 1| ≤ s) :
    cluster (ω ∩ (zdGraph 2).edgeSet) a ⊆
      Icc ![1 - 3 * (s : ℤ), 1 - 3 * s] ![3 * s - 1, 3 * s - 1] := by
  intro v hv
  by_contra hvI
  rw [mem_Icc_two_iff] at hvI
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvI
  refine notMem_localConn_of_notMem_crossing hT hB hR hL ha (v := v) ?_ univ ?_
  · rw [le_abs, le_abs]
    omega
  · rw [localConn_univ]
    exact hv

/-! ### The blocking probability -/

/-- **The complement of a horizontal crossing at `1/2`.** If every edge of `ℤ²` is open with
probability `1/2`, a box has no open left-right crossing with the probability that the box
`[0, hi₁ - lo₁ + 1] × [0, hi₀ - lo₀ - 1]`, of the size of the dual box turned a quarter, has an
open left-right crossing. -/
theorem law_compl_crossing_zero_eq {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {lo hi : LatticeSite 2} (hle : lo ≤ hi) :
    law q (crossing 0 lo hi)ᶜ = law q (crossing 0 0 ![hi 1 - lo 1 + 1, hi 0 - lo 0 - 1]) := by
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q e = ⟨1 / 2, by norm_num, by norm_num⟩ :=
    fun e he => Subtype.ext (hq e he)
  have h0 : lo 0 ≤ hi 0 := hle 0
  have h1 : lo 1 ≤ hi 1 := hle 1
  have hle' : (![lo 1, lo 0] : LatticeSite 2) ≤ ![hi 1, hi 0] := by
    intro i
    fin_cases i
    · simpa using h1
    · simpa using h0
  have h := law_crossing_one_eq_law_crossing_zero hq' ![lo 1, lo 0] ![hi 1, hi 0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← eq_vec_two lo, ← eq_vec_two hi] at h
  rw [prob_compl_eq_one_sub (measurableSet_crossing _ _ _), ← h,
    ← prob_compl_eq_one_sub (measurableSet_crossing _ _ _), law_compl_crossing_one_eq hq hle']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The blocking probability** (wiki WD31, Step 6). At the self-dual point, the event that
none of the four strips around the annulus `s ≤ ‖·‖∞ ≤ 3s` has an open crossing in its short
direction has probability bounded below uniformly in `s ≥ 1`. -/
theorem exists_pos_le_law_blocking :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ s : ℕ, 1 ≤ s →
        c ≤ law q ((crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])ᶜ ∩
          (crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])ᶜ ∩
          (crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])ᶜ ∩
          (crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])ᶜ) := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_le_law_crossing 7
  refine ⟨c ^ 4, ENNReal.pow_pos hc 4, fun q hq s hs => ?_⟩
  -- each strip complement has the probability of a crossing of `[0, 6s + 1] × [0, 2s - 1]`
  have hstrip : c ≤ law q (crossing 0 0 ![6 * (s : ℤ) + 1, 2 * s - 1]) := by
    have h := hcq q hq 0 0 (2 * s - 1) (by omega)
    simp only [↓reduceIte, zero_add] at h
    refine h.trans (measure_mono (crossing_zero_subset_crossing_zero ?_ ?_ ?_ ?_ ?_))
    · exact le_rfl
    · simp only [Pi.zero_apply, Matrix.cons_val_zero]
      omega
    · simp only [Matrix.cons_val_zero]
      omega
    · exact le_rfl
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  have hT : c ≤ law q (crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])ᶜ := by
    rw [law_compl_crossing_one_eq hq (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega)]
    convert hstrip using 4
    all_goals
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring_nf
  have hB : c ≤ law q (crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])ᶜ := by
    rw [law_compl_crossing_one_eq hq (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega)]
    convert hstrip using 4
    all_goals
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring_nf
  have hR : c ≤ law q (crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])ᶜ := by
    rw [law_compl_crossing_zero_eq hq (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega)]
    convert hstrip using 4
    all_goals
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring_nf
  have hL : c ≤ law q (crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])ᶜ := by
    rw [law_compl_crossing_zero_eq hq (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega)]
    convert hstrip using 4
    all_goals
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring_nf
  -- Harris's inequality for the four decreasing events
  set A₁ := (crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])ᶜ with hA₁
  set A₂ := (crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])ᶜ with hA₂
  set A₃ := (crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])ᶜ with hA₃
  set A₄ := (crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])ᶜ with hA₄
  have hl₁ : IsLowerSet A₁ := (isUpperSet_crossing _ _ _).compl
  have hl₂ : IsLowerSet A₂ := (isUpperSet_crossing _ _ _).compl
  have hl₃ : IsLowerSet A₃ := (isUpperSet_crossing _ _ _).compl
  have hl₄ : IsLowerSet A₄ := (isUpperSet_crossing _ _ _).compl
  have hm₁ : MeasurableSet A₁ := (measurableSet_crossing _ _ _).compl
  have hm₂ : MeasurableSet A₂ := (measurableSet_crossing _ _ _).compl
  have hm₃ : MeasurableSet A₃ := (measurableSet_crossing _ _ _).compl
  have hm₄ : MeasurableSet A₄ := (measurableSet_crossing _ _ _).compl
  calc c ^ 4 = c * c * c * c := by ring
    _ ≤ law q A₁ * law q A₂ * law q A₃ * law q A₄ := by gcongr
    _ ≤ law q (A₁ ∩ A₂) * law q A₃ * law q A₄ := by
        gcongr
        exact prodBernoulli_harris_of_isLowerSet q hl₁ hl₂ hm₁ hm₂
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃) * law q A₄ := by
        gcongr
        exact prodBernoulli_harris_of_isLowerSet q (hl₁.inter hl₂) hl₃ (hm₁.inter hm₂) hm₃
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃ ∩ A₄) :=
        prodBernoulli_harris_of_isLowerSet q ((hl₁.inter hl₂).inter hl₃) hl₄
          ((hm₁.inter hm₂).inter hm₃) hm₄

/-! ### Harris's theorem -/

/-- **Harris's theorem at the origin.** -/
theorem law_cluster_infinite_zero_eq_zero_of_half {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) :
    law q {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite} = 0 := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_le_law_blocking
  -- the blocking event at scale `s`
  let B : ℕ → Set (Config (LatticeSite 2)) := fun s =>
    (crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])ᶜ ∩
      (crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])ᶜ ∩
      (crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])ᶜ ∩
      (crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])ᶜ
  -- the annulus `s ≤ ‖·‖∞ ≤ 3s`
  let D : ℕ → Set (LatticeSite 2) := fun s =>
    {v | ((s : ℤ) ≤ v 0 ∨ v 0 ≤ -s ∨ (s : ℤ) ≤ v 1 ∨ v 1 ≤ -s) ∧
      -(3 * (s : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * s ∧ -(3 * (s : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * s}
  have hBm : ∀ s, MeasurableSet (B s) := fun s =>
    (((measurableSet_crossing _ _ _).compl.inter (measurableSet_crossing _ _ _).compl).inter
      (measurableSet_crossing _ _ _).compl).inter (measurableSet_crossing _ _ _).compl
  -- the blocking event is determined by the pairs inside the annulus
  have hBD : ∀ s, ∀ ω ω' : Config (LatticeSite 2),
      ω ∩ {e | ∀ v ∈ e, v ∈ D s} = ω' ∩ {e | ∀ v ∈ e, v ∈ D s} →
        (ω ∈ (B s)ᶜ ↔ ω' ∈ (B s)ᶜ) := by
    intro s ω ω' h
    have hsub : ∀ {lo hi : LatticeSite 2}, (∀ v ∈ Icc lo hi, v ∈ D s) → Icc lo hi ⊆ D s :=
      fun hD v hv => hD v hv
    have h₁ := mem_crossing_iff_of_inter_eq (i := 1)
      (lo := ![-3 * (s : ℤ), s]) (hi := ![3 * s, 3 * s]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    have h₂ := mem_crossing_iff_of_inter_eq (i := 1)
      (lo := ![-3 * (s : ℤ), -3 * s]) (hi := ![3 * s, -s]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    have h₃ := mem_crossing_iff_of_inter_eq (i := 0)
      (lo := ![(s : ℤ), -3 * s]) (hi := ![3 * s, 3 * s]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    have h₄ := mem_crossing_iff_of_inter_eq (i := 0)
      (lo := ![-3 * (s : ℤ), -3 * s]) (hi := ![-s, 3 * s]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    simp only [B, mem_compl_iff, mem_inter_iff, h₁, h₂, h₃, h₄]
  -- the annuli at the scales `4^j` are disjoint
  have hdisj : ∀ J : ℕ, Set.PairwiseDisjoint (↑(Finset.range J)) fun j => D (4 ^ j) := by
    intro J j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    rintro v ⟨hj, hj0, hj1, hj2, hj3⟩ ⟨hk, hk0, hk1, hk2, hk3⟩
    have key : ∀ {j k : ℕ}, j < k → 3 * ((4 ^ j : ℕ) : ℤ) < ((4 ^ k : ℕ) : ℤ) := by
      intro j k hjk
      have h4 : 4 ^ (j + 1) ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
      rw [pow_succ] at h4
      have hpos : 0 < 4 ^ j := by positivity
      exact_mod_cast (show 3 * 4 ^ j < 4 ^ k by omega)
    rcases lt_or_gt_of_ne hjk with h | h
    · have := key h
      omega
    · have := key h
      omega
  -- an infinite cluster of the origin defeats every blocking event
  have hsub : ∀ J : ℕ, {ω : Config (LatticeSite 2) |
      (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite} ⊆ ⋂ j ∈ Finset.range J, (B (4 ^ j))ᶜ := by
    intro J ω hω
    simp only [mem_iInter]
    intro j _
    rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    refine hω ((Set.finite_Icc _ _).subset
      (cluster_subset_Icc_of_notMem_crossing h₁ h₂ h₃ h₄ (a := 0) ?_))
    simp
  -- the bound `θ(1/2) ≤ (1 - c)^J`
  have hbound : ∀ J : ℕ, law q {ω : Config (LatticeSite 2) |
      (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite} ≤ (1 - c) ^ J := by
    intro J
    calc law q {ω : Config (LatticeSite 2) | (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite}
        ≤ law q (⋂ j ∈ Finset.range J, (B (4 ^ j))ᶜ) := measure_mono (hsub J)
      _ = ∏ j ∈ Finset.range J, law q (B (4 ^ j))ᶜ :=
          law_biInter_of_determined_internalPairs q (Finset.range J) (hdisj J)
            (fun j _ => (hBm _).compl) (fun j => hBD (4 ^ j))
      _ ≤ (1 - c) ^ (Finset.range J).card := by
          refine Finset.prod_le_pow_card _ _ _ fun j _ => ?_
          rw [prob_compl_eq_one_sub (hBm _)]
          exact tsub_le_tsub_left (hcq q hq (4 ^ j) (Nat.one_le_pow _ _ (by norm_num))) 1
      _ = (1 - c) ^ J := by rw [Finset.card_range]
  have hlt : 1 - c < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc.ne'
  exact nonpos_iff_eq_zero.1
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hbound)

/-- **Harris's theorem** (`θ(1/2) = 0`, wiki WD31, Step 6; Bollobás–Riordan, Theorem 8). If
every edge of `ℤ²` is open with probability `1/2`, the open cluster of every vertex is almost
surely finite. -/
theorem law_cluster_infinite_eq_zero_of_half {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) (x : LatticeSite 2) :
    law q {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} = 0 := by
  obtain ⟨σ, hσ⟩ := exists_zdGraph_iso_add (d := 2) x
  have hσ0 : σ 0 = x := by rw [hσ, zero_add]
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q (Sym2.map σ e) = q e := fun e he =>
    Subtype.ext (by rw [hq e he, hq _ (image_sym2Map_edgeSet σ ▸ mem_image_of_mem _ he)])
  have hmeas : MeasurableSet
      {ω : Config (LatticeSite 2) | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} :=
    (measurableSet_cluster_infinite x).preimage (by fun_prop)
  have hpre : (fun ω : Config (LatticeSite 2) => Sym2.map σ '' ω) ⁻¹'
      {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} =
      {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite} := by
    ext ω
    have hL : Sym2.map σ '' ω ∩ (zdGraph 2).edgeSet =
        Sym2.map σ '' (ω ∩ (zdGraph 2).edgeSet) := by
      rw [image_inter (Sym2.map.injective σ.injective)]
      congr 1
      exact (image_sym2Map_edgeSet σ).symm
    change (cluster (Sym2.map σ '' ω ∩ (zdGraph 2).edgeSet) x).Infinite ↔
      (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite
    rw [hL, ← hσ0]
    exact cluster_image_infinite_iff σ.toEquiv _ 0
  have hAG : ∀ ω : Config (LatticeSite 2),
      ω ∩ (zdGraph 2).edgeSet ∈ {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} ↔
        ω ∈ {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} := fun ω => by
    change (cluster (ω ∩ (zdGraph 2).edgeSet ∩ (zdGraph 2).edgeSet) x).Infinite ↔
      (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite
    rw [inter_assoc, inter_self]
  rw [← law_preimage_image_sym2Map_eq σ hq' hmeas hAG, hpre,
    law_cluster_infinite_zero_eq_zero_of_half hq]

/-- **Harris's theorem, global form.** If every edge of `ℤ²` is open with probability `1/2`,
there is almost surely no infinite open cluster. -/
theorem law_exists_cluster_infinite_eq_zero_of_half {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) :
    law q {ω | ∃ x, (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} = 0 := by
  have hU : {ω : Config (LatticeSite 2) | ∃ x, (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} =
      ⋃ x, {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} := by
    ext ω
    simp
  rw [hU]
  exact measure_iUnion_null fun x => law_cluster_infinite_eq_zero_of_half hq x

/-! ### The intensity form and the critical intensity -/

/-- **Harris's theorem, intensity form.** For nearest-neighbour bond percolation on `ℤ²` at
intensity `β ≤ log 2` (edge probability `1 - e^{-β} ≤ 1/2`), the cluster of every vertex is
almost surely finite. -/
theorem law_cluster_infinite_intensityProfile_eq_zero {β : ℝ≥0} (hβ : (β : ℝ) ≤ Real.log 2)
    (x : LatticeSite 2) :
    law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)
      {ω | (cluster ω x).Infinite} = 0 := by
  set q₀ := intensityProfile ((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0))
    (Real.log 2).toNNReal with hq₀
  have hβ' : β ≤ (Real.log 2).toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.log_nonneg one_le_two)]
    exact hβ
  refine nonpos_iff_eq_zero.1 ((law_intensityProfile_mono (isUpperSet_cluster_infinite x)
    (measurableSet_cluster_infinite x) _ hβ').trans ?_)
  -- at intensity `log 2` only edges of `ℤ²` can be open
  have h0 : ∀ e, e ∉ (zdGraph 2).edgeSet → q₀ e = 0 := fun e he =>
    Subtype.ext (by simp [q₀, intensityProfile, indicator_of_notMem he])
  have hae : {ω : Config (LatticeSite 2) | (cluster ω x).Infinite} =ᵐ[law q₀]
      {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} := by
    filter_upwards [ae_config_subset_host (zdGraph 2) q₀ h0] with ω hω
    rw [inter_eq_left.2 hω]
  rw [measure_congr hae, law_cluster_infinite_eq_zero_of_half
    (fun e he => intensityProfile_indicator_edgeSet_log_two he) x]

/-- **Harris's theorem, intensity form, global.** For nearest-neighbour bond percolation on
`ℤ²` at intensity `β ≤ log 2` there is almost surely no infinite cluster. -/
theorem law_exists_cluster_infinite_intensityProfile_eq_zero {β : ℝ≥0}
    (hβ : (β : ℝ) ≤ Real.log 2) :
    law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)
      {ω | ∃ x : LatticeSite 2, (cluster ω x).Infinite} = 0 := by
  have hU : {ω : Config (LatticeSite 2) | ∃ x, (cluster ω x).Infinite} =
      ⋃ x, {ω | (cluster ω x).Infinite} := by
    ext ω
    simp
  rw [hU]
  exact measure_iUnion_null fun x => law_cluster_infinite_intensityProfile_eq_zero hβ x

/-- **The critical probability of `ℤ²` is `1/2`** (the threshold conjunct of tag WD31; root
form). For nearest-neighbour bond percolation on `ℤ²` the critical intensity at every vertex is
`log 2`, that is `p_c(ℤ²) = 1/2` with edge probability `1 - e^{-β}`. -/
theorem rootCriticalIntensity_indicator_edgeSet_eq_log_two (x : LatticeSite 2) :
    rootCriticalIntensity ((zdGraph 2).edgeSet.indicator 1) x = ENNReal.ofReal (Real.log 2) := by
  refine le_antisymm (rootCriticalIntensity_indicator_edgeSet_le_log_two x) (le_sInf ?_)
  rintro b ⟨β, rfl, hpos⟩
  by_contra hlt
  rw [not_le] at hlt
  have hβ : (β : ℝ) ≤ Real.log 2 := by
    by_contra h
    rw [not_le] at h
    have h' := (ENNReal.ofReal_lt_ofReal_iff ((Real.log_pos one_lt_two).trans h)).2 h
    rw [ENNReal.ofReal_coe_nnreal] at h'
    exact lt_asymm h' hlt
  rw [law_cluster_infinite_intensityProfile_eq_zero hβ x] at hpos
  exact lt_irrefl _ hpos

/-- **The critical probability of `ℤ²` is `1/2`**, global form. -/
theorem globalCriticalIntensity_indicator_edgeSet_eq_log_two :
    globalCriticalIntensity ((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0)) =
      ENNReal.ofReal (Real.log 2) := by
  rw [← rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive _
    indicator_edgeSet_transitive 0]
  exact rootCriticalIntensity_indicator_edgeSet_eq_log_two 0

end PercLib.Models.Planar
