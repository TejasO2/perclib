/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (one-arm bounds, pp. 23-24); B. Bollobás and
O. Riordan, A short proof of the Harris-Kesten theorem, Bull. London Math. Soc. 38 (2006),
470-484 (arXiv math/0410359v3).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import PercLib.Models.Planar.Arms.Separator
public import PercLib.Models.Planar.CriticalProbability

/-!
# One-arm bounds at the self-dual point of `ℤ²`

At the self-dual point, where every nearest-neighbour edge of `ℤ²` is open with probability
`1/2`, the one-arm probability `π(r)`, the probability that the origin is joined to the boundary
of the box `B_r = [-r, r]²` (the event `armEvent 0 r` of `Arms/Defs.lean`), has uniform
polynomial scale bounds (wiki tag XB1U, "Extending an arm and blocking it"): there are constants
`c, C, a, b > 0` such that for all integers `1 ≤ r ≤ R`,
`π(2r) ≥ c π(r)` and `c (R/r)^(-b) π(r) ≤ π(R) ≤ C (R/r)^(-a) π(r)`. In particular `π(r)`
lies between two positive powers of `r` and tends to zero.

* **Extending an arm** (`mem_armEvent_of_mem_fourStrip_of_mem_crossing`). On the four-strip
  event `fourStrip 0 n` of the annulus `2n ≤ ‖·‖∞ ≤ 4n`, which plays the part of an open
  circuit, an arm of the origin of radius `r ≥ 4n` and a left-right crossing of
  `[0, m] × [-n, n]` with `m ≥ 4n` both cross the annulus, so circuit gluing
  (`Arms/Separator.lean`) joins the origin to the end of the crossing on the line `x = m`.
* **Doubling** (`exists_pos_mul_law_armEvent_le`). For `r ≥ 8` and `n = ⌊r/8⌋`, the arm of
  radius `r`, the four-strip event and a crossing of `[0, 30n] × [-n, n]` give an arm of radius
  `2r ≤ 30n`. Harris's inequality (`prodBernoulli_harris`, tag X5SS), the circuit bound
  (`exists_pos_le_law_fourStrip`) and RSW (`exists_pos_le_law_crossing`) give
  `π(2r) ≥ c₀ c₁₅ π(r)`. For `r < 8`, `π(2r) ≥ 2⁻¹⁶` because a straight segment of `2r` open
  edges is an arm (`inv_two_pow_le_law_armEvent`).
* **Blocking an arm** (`notMem_armEvent_of_notMem_crossing`). On the blocking event of
  `CriticalProbability.lean` at scale `s`, where none of the four strips around the annulus
  `s ≤ ‖·‖∞ ≤ 3s` has an open crossing in its short direction, the origin has no arm of radius
  `R ≥ 3s`.
* **Blocking at many scales** (`exists_law_armEvent_le_pow_mul`). At the scales
  `s_j = (r + 1) 4^j`, `j < N`, with `3 s_j ≤ R`, the annuli are disjoint from each other and
  from `B_r`. The arm of radius `r` and the blocking events are determined by the edges of these
  disjoint regions, hence independent, and each blocking event has probability at least a
  constant (`exists_pos_le_law_blocking`). An arm of radius `R` is an arm of radius `r` that
  defeats every blocking event, so `π(R) ≤ ρ^N π(r)` with `ρ < 1`.
* **The bounds** (`exists_armEvent_bounds`): iterating the doubling `k = ⌈log₂(R/r)⌉` times gives
  the lower bound with `b = -log₂ c`; the largest number of scales gives the upper bound with
  `a = -log₄ ρ` and `C = 6^a`. The limit `π(r) → 0` (`tendsto_law_armEvent_zero`) and the
  bounds `c R^(-b) ≤ π(R) ≤ C R^(-a)` (`exists_armEvent_polynomial_bounds`, the case `r = 1`)
  are the "in particular" clauses of XB1U.

The wiki blocks arms with a closed dual circuit built from four dual strip crossings in the
annulus `2n - 1 ≤ ‖·‖∞ ≤ 4n + 1` around `(1/2, 1/2)`, at the scales `2r 8^j`. Here the blocking
event is the primal one of `CriticalProbability.lean`: four strips without an open crossing in
their short direction, which by vertical duality is the event that their dual strips are crossed
in their long direction by closed dual paths. The annuli are `s ≤ ‖·‖∞ ≤ 3s` at the scales
`(r + 1) 4^j`.

## Main results

* `PercLib.Models.Planar.exists_armEvent_bounds`
* `PercLib.Models.Planar.tendsto_law_armEvent_zero`
* `PercLib.Models.Planar.exists_armEvent_polynomial_bounds`
* `PercLib.Models.Planar.exists_pos_mul_law_armEvent_le`
* `PercLib.Models.Planar.exists_law_armEvent_le_pow_mul`
* `PercLib.Models.Planar.mem_armEvent_of_mem_fourStrip_of_mem_crossing`
* `PercLib.Models.Planar.notMem_armEvent_of_notMem_crossing`
* `PercLib.Models.Planar.inv_two_pow_le_law_armEvent`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Percolation.Bond PercLib.Models.Site
  PercLib.Probability
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Extending and blocking an arm -/

/-- **Extending an arm.** On the four-strip event of the annulus `2n ≤ ‖·‖∞ ≤ 4n`, an arm of the
origin of radius `r ≥ 4n` and a left-right crossing of `[0, m] × [-n, n]` with `m ≥ 4n` join the
origin to the line `x = m`, so the origin has an arm of every radius `R ≤ m`. -/
theorem mem_armEvent_of_mem_fourStrip_of_mem_crossing {ω : Config (LatticeSite 2)}
    {n r m R : ℕ} (hnr : 4 * n ≤ r) (hnm : 4 * n ≤ m) (hRm : R ≤ m) (hr : ω ∈ armEvent 0 r)
    (hω : ω ∈ fourStrip 0 n) (hH : ω ∈ crossing 0 ![0, -(n : ℤ)] ![(m : ℤ), n]) :
    ω ∈ armEvent 0 R := by
  obtain ⟨y, hy, h0y⟩ := mem_armEvent_iff_exists_notMem_conn.1 hr
  obtain ⟨a, ha, ha0, b, hb, hb0, hab⟩ := hH
  rw [mem_Icc_two_iff] at ha hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha hb ha0 hb0
  -- the origin and the start of the crossing lie in the inner box `B_{2n}`
  have h0 : (0 : LatticeSite 2) ∈
      Icc (0 - ((2 * n : ℕ) : LatticeSite 2)) (0 + ((2 * n : ℕ) : LatticeSite 2)) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply]
    omega
  have ha' : a ∈ Icc (0 - ((2 * n : ℕ) : LatticeSite 2)) (0 + ((2 * n : ℕ) : LatticeSite 2)) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply]
    omega
  -- the arm and the crossing both leave the box `B_{4n - 1}`
  have hy' : y ∉ Icc (0 - ((4 * n : ℕ) : LatticeSite 2) + 1)
      (0 + ((4 * n : ℕ) : LatticeSite 2) - 1) := by
    intro hy4
    apply hy
    rw [mem_Icc_two_iff] at hy4 ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply,
      Pi.one_apply] at hy4 ⊢
    omega
  have hb' : b ∉ Icc (0 - ((4 * n : ℕ) : LatticeSite 2) + 1)
      (0 + ((4 * n : ℕ) : LatticeSite 2) - 1) := by
    intro hb4
    rw [mem_Icc_two_iff] at hb4
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply,
      Pi.one_apply] at hb4
    omega
  have hab' := localConn_subset_conn _ a b hab
  -- circuit gluing joins the origin to the start of the crossing
  have h0a := inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn hω h0 ha' hy' hb' h0y hab'
  refine mem_armEvent_of_mem_conn (y := b) (fun hbR => ?_)
    (conn_trans (localConn_subset_conn _ _ _ h0a) hab')
  rw [mem_Icc_two_iff] at hbR
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply, Pi.one_apply] at hbR
  omega

/-- **Blocking an arm.** If none of the four strips around the annulus `s ≤ ‖·‖∞ ≤ 3s`, the
strip `[-3s, 3s] × [s, 3s]` and its images under quarter-turns, has an open crossing in its short
direction, the origin has no arm of any radius `R ≥ 3s`. -/
theorem notMem_armEvent_of_notMem_crossing {ω : Config (LatticeSite 2)} {s R : ℕ}
    (hT : ω ∉ crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])
    (hB : ω ∉ crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])
    (hR : ω ∉ crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])
    (hL : ω ∉ crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s]) (hsR : 3 * s ≤ R) :
    ω ∉ armEvent 0 R := by
  rintro ⟨v, -, hv, hc⟩
  refine notMem_localConn_of_notMem_crossing hT hB hR hL (a := 0) (v := v) (by simp) ?_ _ hc
  rw [Fin.exists_fin_two] at hv
  simp only [Pi.zero_apply, zero_sub, zero_add] at hv
  rw [le_abs, le_abs]
  omega

/-- **A straight arm.** At the self-dual point the origin has an arm of radius `r` with
probability at least `2⁻ʳ`: it suffices that the `r` edges of the segment from the origin to
`(r, 0)` are open. -/
theorem inv_two_pow_le_law_armEvent {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) (r : ℕ) :
    2⁻¹ ^ r ≤ law q (armEvent 0 r) := by
  refine (inv_two_pow_le_law_crossing_zero hq r).trans (measure_mono ?_)
  rintro ω ⟨a, ha, ha0, b, hb, hb0, hab⟩
  have ha' := mem_Icc_two_iff.1 ha
  have hb' := mem_Icc_two_iff.1 hb
  simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at ha' hb' ha0 hb0
  obtain rfl : a = 0 := funext (Fin.forall_fin_two.2
    ⟨by simp only [Pi.zero_apply]; omega, by simp only [Pi.zero_apply]; omega⟩)
  have hsub : Icc (0 : LatticeSite 2) ![(r : ℤ), 0] ⊆
      Icc (0 - (r : LatticeSite 2)) (0 + (r : LatticeSite 2)) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hv ⊢
    omega
  refine ⟨b, hsub hb, ⟨0, Or.inr ?_⟩, localConn_mono_set hsub _ _ hab⟩
  simp only [Pi.zero_apply, zero_add]
  exact hb0

/-! ### Doubling -/

/-- **Doubling** (the first bound of XB1U). At the self-dual point there is `c ∈ (0, 1)` such
that `c π(r) ≤ π(2r)` for every radius `r`, uniformly in the profile. -/
theorem exists_pos_mul_law_armEvent_le :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < 1 ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ r : ℕ, c * law q (armEvent 0 r) ≤ law q (armEvent 0 (2 * r)) := by
  obtain ⟨c₀, hc₀, hc₀q⟩ := exists_pos_le_law_fourStrip
  obtain ⟨c₁, hc₁, hc₁q⟩ := exists_pos_le_law_crossing 15
  have h2 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  refine ⟨min (c₀ * c₁) (2⁻¹ ^ 16),
    lt_min (ENNReal.mul_pos hc₀.ne' hc₁.ne')
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) 16),
    (min_le_right _ _).trans_lt (pow_lt_one₀ zero_le h2 (by norm_num)), fun q hq r => ?_⟩
  rcases lt_or_ge r 8 with hr | hr
  · -- small radii: an arm of radius `2r ≤ 16` has probability at least `2⁻¹⁶`
    calc min (c₀ * c₁) (2⁻¹ ^ 16) * law q (armEvent 0 r) ≤ 2⁻¹ ^ 16 * 1 :=
          mul_le_mul' (min_le_right _ _) prob_le_one
      _ = 2⁻¹ ^ 16 := mul_one _
      _ ≤ 2⁻¹ ^ (2 * r) := pow_le_pow_right_of_le_one' h2.le (by omega)
      _ ≤ law q (armEvent 0 (2 * r)) := inv_two_pow_le_law_armEvent hq (2 * r)
  · -- large radii: extend the arm by a circuit and a long crossing, then Harris
    set n := r / 8 with hn
    have hn1 : 1 ≤ n := by omega
    have hsub : armEvent 0 r ∩ fourStrip 0 n ∩
        crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n] ⊆
          armEvent (0 : LatticeSite 2) (2 * r) := fun ω hω =>
      mem_armEvent_of_mem_fourStrip_of_mem_crossing (by omega) (by omega) (by omega)
        hω.1.1 hω.1.2 hω.2
    have hF := hc₀q q hq 0 n hn1
    -- the crossing of `[0, 30n] × [-n, n]`, a `15 · 2n × 2n` box
    have hH : c₁ ≤ law q (crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n]) := by
      have h := hc₁q q hq 0 ![0, -(n : ℤ)] (2 * n) (by omega)
      rw [ite_eq_left rfl] at h
      convert h using 3
      refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · simp only [Pi.add_apply, Matrix.cons_val_zero, Nat.cast_mul, Nat.cast_ofNat]
        omega
      · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_mul,
          Nat.cast_ofNat]
        omega
    have hu₁ : IsUpperSet (armEvent (0 : LatticeSite 2) r) := isUpperSet_armEvent 0 r
    have hu₂ : IsUpperSet (fourStrip 0 n) := isUpperSet_fourStrip 0 n
    have hu₃ : IsUpperSet (crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n]) :=
      isUpperSet_crossing _ _ _
    have hm₁ : MeasurableSet (armEvent (0 : LatticeSite 2) r) := measurableSet_armEvent 0 r
    have hm₂ : MeasurableSet (fourStrip 0 n) := measurableSet_fourStrip 0 n
    have hm₃ : MeasurableSet (crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n]) :=
      measurableSet_crossing _ _ _
    calc min (c₀ * c₁) (2⁻¹ ^ 16) * law q (armEvent 0 r)
        ≤ c₀ * c₁ * law q (armEvent 0 r) := mul_le_mul' (min_le_left _ _) le_rfl
      _ = law q (armEvent 0 r) * c₀ * c₁ := by ring
      _ ≤ law q (armEvent 0 r) * law q (fourStrip 0 n) *
          law q (crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n]) := by gcongr
      _ ≤ law q (armEvent 0 r ∩ fourStrip 0 n) *
          law q (crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n]) := by
          gcongr
          exact prodBernoulli_harris q hu₁ hu₂ hm₁ hm₂
      _ ≤ law q (armEvent 0 r ∩ fourStrip 0 n ∩
          crossing 0 ![0, -(n : ℤ)] ![((30 * n : ℕ) : ℤ), n]) :=
          prodBernoulli_harris q (hu₁.inter hu₂) hu₃ (hm₁.inter hm₂) hm₃
      _ ≤ law q (armEvent 0 (2 * r)) := measure_mono hsub

/-! ### Blocking at many scales -/

/-- **Blocking at many scales** (the upper bound of XB1U, before choosing the scales). At the
self-dual point there is `ρ ∈ (0, 1)` such that `π(R) ≤ ρ^N π(r)` whenever `r ≤ R` and the `N`
scales `s_j = (r + 1) 4^j`, `j < N`, satisfy `3 s_j ≤ R`, uniformly in the profile. -/
theorem exists_law_armEvent_le_pow_mul :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < 1 ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ r R N : ℕ, r ≤ R → (∀ j < N, 3 * ((r + 1) * 4 ^ j) ≤ R) →
        law q (armEvent 0 R) ≤ ρ ^ N * law q (armEvent 0 r) := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_le_law_blocking
  have h2 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have hc' : 0 < min c 2⁻¹ := lt_min hc (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
  refine ⟨1 - min c 2⁻¹, tsub_pos_of_lt ((min_le_right _ _).trans_lt h2),
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc'.ne', fun q hq r R N hrR hN => ?_⟩
  -- the blocking event at scale `t`
  let B : ℕ → Set (Config (LatticeSite 2)) := fun t =>
    (crossing 1 ![-3 * (t : ℤ), t] ![3 * t, 3 * t])ᶜ ∩
      (crossing 1 ![-3 * (t : ℤ), -3 * t] ![3 * t, -t])ᶜ ∩
      (crossing 0 ![(t : ℤ), -3 * t] ![3 * t, 3 * t])ᶜ ∩
      (crossing 0 ![-3 * (t : ℤ), -3 * t] ![-t, 3 * t])ᶜ
  -- the annulus `t ≤ ‖·‖∞ ≤ 3t`
  let D : ℕ → Set (LatticeSite 2) := fun t =>
    {v | ((t : ℤ) ≤ v 0 ∨ v 0 ≤ -t ∨ (t : ℤ) ≤ v 1 ∨ v 1 ≤ -t) ∧
      -(3 * (t : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * t ∧ -(3 * (t : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * t}
  have hBm : ∀ t, MeasurableSet (B t) := fun t =>
    (((measurableSet_crossing _ _ _).compl.inter (measurableSet_crossing _ _ _).compl).inter
      (measurableSet_crossing _ _ _).compl).inter (measurableSet_crossing _ _ _).compl
  -- the blocking event is determined by the pairs inside the annulus
  have hBD : ∀ t, ∀ ω ω' : Config (LatticeSite 2),
      ω ∩ {e | ∀ v ∈ e, v ∈ D t} = ω' ∩ {e | ∀ v ∈ e, v ∈ D t} →
        (ω ∈ (B t)ᶜ ↔ ω' ∈ (B t)ᶜ) := by
    intro t ω ω' h
    have hsub : ∀ {lo hi : LatticeSite 2}, (∀ v ∈ Icc lo hi, v ∈ D t) → Icc lo hi ⊆ D t :=
      fun hD v hv => hD v hv
    have h₁ := mem_crossing_iff_of_inter_eq (i := 1)
      (lo := ![-3 * (t : ℤ), t]) (hi := ![3 * t, 3 * t]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    have h₂ := mem_crossing_iff_of_inter_eq (i := 1)
      (lo := ![-3 * (t : ℤ), -3 * t]) (hi := ![3 * t, -t]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    have h₃ := mem_crossing_iff_of_inter_eq (i := 0)
      (lo := ![(t : ℤ), -3 * t]) (hi := ![3 * t, 3 * t]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    have h₄ := mem_crossing_iff_of_inter_eq (i := 0)
      (lo := ![-3 * (t : ℤ), -3 * t]) (hi := ![-t, 3 * t]) (hsub fun v hv => by
      rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩) h
    simp only [B, mem_compl_iff, mem_inter_iff, h₁, h₂, h₃, h₄]
  -- the scales `s_j = (r + 1) 4^j`
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℕ, s = fun j => (r + 1) * 4 ^ j := ⟨_, rfl⟩
  have hs1 : ∀ j, r + 1 ≤ s j := fun j => by
    simp only [hs]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hs3 : ∀ {j k : ℕ}, j < k → 3 * s j < s k := by
    intro j k hjk
    simp only [hs]
    have h4 : 4 ^ (j + 1) ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
    have hX : 0 < (r + 1) * 4 ^ j := by positivity
    calc 3 * ((r + 1) * 4 ^ j) < 4 * ((r + 1) * 4 ^ j) := by omega
      _ = (r + 1) * 4 ^ (j + 1) := by ring
      _ ≤ (r + 1) * 4 ^ k := Nat.mul_le_mul_left _ h4
  have hsR : ∀ j < N, 3 * s j ≤ R := fun j hj => by
    simp only [hs]
    exact hN j hj
  -- the annuli at these scales are disjoint from each other and from the box `B_r`
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range N)) fun j => D (s j) := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    rintro v ⟨hj, hj0, hj1, hj2, hj3⟩ ⟨hk, hk0, hk1, hk2, hk3⟩
    rcases lt_or_gt_of_ne hjk with h | h
    · have := hs3 h
      omega
    · have := hs3 h
      omega
  have hST : Disjoint (Icc (0 - (r : LatticeSite 2)) (0 + (r : LatticeSite 2)))
      (⋃ j ∈ Finset.range N, D (s j)) := by
    rw [Set.disjoint_left]
    intro v hv hvT
    rw [mem_Icc_two_iff] at hv
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply] at hv
    obtain ⟨j, -, hj, -, -, -, -⟩ := Set.mem_iUnion₂.1 hvT
    have := hs1 j
    omega
  -- the blocking events together are determined by the pairs inside the union of the annuli
  have hBT : ∀ ω ω' : Config (LatticeSite 2),
      ω ∩ {e | ∀ v ∈ e, v ∈ ⋃ j ∈ Finset.range N, D (s j)} =
        ω' ∩ {e | ∀ v ∈ e, v ∈ ⋃ j ∈ Finset.range N, D (s j)} →
      (ω ∈ ⋂ j ∈ Finset.range N, (B (s j))ᶜ ↔ ω' ∈ ⋂ j ∈ Finset.range N, (B (s j))ᶜ) := by
    intro ω ω' h
    simp only [mem_iInter]
    refine forall₂_congr fun j hj => hBD (s j) ω ω' ?_
    have hsub : {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ D (s j)} ⊆
        {e | ∀ v ∈ e, v ∈ ⋃ j ∈ Finset.range N, D (s j)} :=
      fun e he v hv => Set.mem_iUnion₂.2 ⟨j, hj, he v hv⟩
    rw [← inter_eq_right.2 hsub, ← inter_assoc, h, inter_assoc]
  -- an arm of radius `R` is an arm of radius `r` that defeats every blocking event
  have hsub : armEvent (0 : LatticeSite 2) R ⊆
      armEvent 0 r ∩ ⋂ j ∈ Finset.range N, (B (s j))ᶜ := by
    intro ω hω
    refine ⟨armEvent_anti 0 hrR hω, mem_iInter₂.2 fun j hj => ?_⟩
    rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    exact notMem_armEvent_of_notMem_crossing h₁ h₂ h₃ h₄ (hsR j (Finset.mem_range.1 hj)) hω
  calc law q (armEvent 0 R) ≤ law q (armEvent 0 r ∩ ⋂ j ∈ Finset.range N, (B (s j))ᶜ) :=
        measure_mono hsub
    _ = law q (armEvent 0 r) * law q (⋂ j ∈ Finset.range N, (B (s j))ᶜ) :=
        law_inter_of_determined_internalPairs q hST (measurableSet_armEvent 0 r)
          (Finset.measurableSet_biInter _ fun j _ => (hBm _).compl)
          (fun ω ω' h => mem_armEvent_iff_of_inter_eq subset_rfl h) hBT
    _ = law q (armEvent 0 r) * ∏ j ∈ Finset.range N, law q (B (s j))ᶜ := by
        rw [law_biInter_of_determined_internalPairs q (Finset.range N) hdisj
          (fun j _ => (hBm _).compl) (fun j => hBD (s j))]
    _ ≤ law q (armEvent 0 r) * (1 - min c 2⁻¹) ^ N := by
        gcongr
        calc ∏ j ∈ Finset.range N, law q (B (s j))ᶜ ≤
              (1 - min c 2⁻¹) ^ (Finset.range N).card := by
              refine Finset.prod_le_pow_card _ _ _ fun j _ => ?_
              rw [prob_compl_eq_one_sub (hBm _)]
              exact tsub_le_tsub_left
                ((min_le_left _ _).trans (hcq q hq (s j) (by have := hs1 j; omega))) 1
          _ = (1 - min c 2⁻¹) ^ N := by rw [Finset.card_range]
    _ = (1 - min c 2⁻¹) ^ N * law q (armEvent 0 r) := mul_comm _ _

/-! ### The one-arm bounds -/

/-- **One-arm bounds** (tag XB1U). At the self-dual point of `ℤ²`, with
`π(r) = P(0 ↔ ∂B_r)` the probability of `armEvent 0 r`, there are constants `c, C, a, b > 0`
such that for all integers `1 ≤ r ≤ R`: `π(2r) ≥ c π(r)` and
`c (R/r)^(-b) π(r) ≤ π(R) ≤ C (R/r)^(-a) π(r)`. The constants do not depend on the profile `q`,
which is `1/2` on the edges of `ℤ²` and arbitrary elsewhere, nor on `r` and `R`. -/
theorem exists_armEvent_bounds :
    ∃ c C a b : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < b ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ r R : ℕ, 1 ≤ r → r ≤ R →
        c * (law q).real (armEvent 0 r) ≤ (law q).real (armEvent 0 (2 * r)) ∧
        c * ((R : ℝ) / r) ^ (-b) * (law q).real (armEvent 0 r) ≤ (law q).real (armEvent 0 R) ∧
        (law q).real (armEvent 0 R) ≤ C * ((R : ℝ) / r) ^ (-a) * (law q).real (armEvent 0 r) := by
  obtain ⟨cE, hcE, hcE1, hcEq⟩ := exists_pos_mul_law_armEvent_le
  obtain ⟨ρE, hρE, hρE1, hρEq⟩ := exists_law_armEvent_le_pow_mul
  have hcE' : cE ≠ ∞ := (hcE1.trans ENNReal.one_lt_top).ne
  have hρE' : ρE ≠ ∞ := (hρE1.trans ENNReal.one_lt_top).ne
  set c := cE.toReal with hc_def
  set ρ := ρE.toReal with hρ_def
  have hc : 0 < c := ENNReal.toReal_pos hcE.ne' hcE'
  have hc1 : c < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hcE' ENNReal.one_ne_top).2 hcE1
  have hρ : 0 < ρ := ENNReal.toReal_pos hρE.ne' hρE'
  have hρ1 : ρ < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hρE' ENNReal.one_ne_top).2 hρE1
  -- the exponents: `c = 2^(-b)` and `ρ = 4^(-a)`
  set b := -Real.logb 2 c with hb_def
  set a := -Real.logb 4 ρ with ha_def
  have hb : 0 < b := neg_pos.2 (Real.logb_neg one_lt_two hc hc1)
  have ha : 0 < a := neg_pos.2 (Real.logb_neg (by norm_num) hρ hρ1)
  have h2b : (2 : ℝ) ^ (-b) = c := by
    rw [hb_def, neg_neg]
    exact Real.rpow_logb two_pos (by norm_num) hc
  have h4a : (4 : ℝ) ^ (-a) = ρ := by
    rw [ha_def, neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hρ
  refine ⟨c, 6 ^ a, a, b, hc, by positivity, ha, hb, fun q hq r R hr hrR => ?_⟩
  -- the real forms of the doubling and blocking bounds
  have hD : ∀ t : ℕ, c * (law q).real (armEvent 0 t) ≤ (law q).real (armEvent 0 (2 * t)) := by
    intro t
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hcEq q hq t)
    rw [ENNReal.toReal_mul] at h
    exact h
  have hU : ∀ N : ℕ, (∀ j < N, 3 * ((r + 1) * 4 ^ j) ≤ R) →
      (law q).real (armEvent 0 R) ≤ ρ ^ N * (law q).real (armEvent 0 r) := by
    intro N hN
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top hρE')
      (measure_ne_top _ _)) (hρEq q hq r R N hrR hN)
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h
    exact h
  have hA0 : ∀ t : ℕ, 0 ≤ (law q).real (armEvent (0 : LatticeSite 2) t) :=
    fun t => measureReal_nonneg
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hRr : (0 : ℝ) < (R : ℝ) / r := div_pos (by exact_mod_cast hr.trans hrR) hr0
  refine ⟨hD r, ?_, ?_⟩
  · -- lower bound: iterate the doubling `k` times, with `R ≤ 2^k r < 2R`
    have hDk : ∀ k : ℕ, c ^ k * (law q).real (armEvent 0 r) ≤
        (law q).real (armEvent 0 (2 ^ k * r)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc c ^ (k + 1) * (law q).real (armEvent 0 r) =
              c * (c ^ k * (law q).real (armEvent 0 r)) := by ring
          _ ≤ c * (law q).real (armEvent 0 (2 ^ k * r)) := mul_le_mul_of_nonneg_left ih hc.le
          _ ≤ (law q).real (armEvent 0 (2 * (2 ^ k * r))) := hD _
          _ = (law q).real (armEvent 0 (2 ^ (k + 1) * r)) := by
              rw [show 2 * (2 ^ k * r) = 2 ^ (k + 1) * r by ring]
    classical
    obtain ⟨k, hk, hk2⟩ : ∃ k : ℕ, R ≤ 2 ^ k * r ∧ 2 ^ k * r < 2 * R := by
      have hex : ∃ k : ℕ, R ≤ 2 ^ k * r :=
        ⟨R, Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ hr)⟩
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero, one_mul]
        omega
      · have hmin := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
        have h2 : 2 ^ Nat.find hex * r = 2 * (2 ^ (Nat.find hex - 1) * r) := by
          conv_lhs => rw [← Nat.sub_add_cancel hpos]
          ring
        omega
    have hk2' : (2 : ℝ) ^ k ≤ 2 * ((R : ℝ) / r) := by
      rw [← mul_div_assoc, le_div_iff₀ hr0]
      exact_mod_cast hk2.le
    have hck : c * ((R : ℝ) / r) ^ (-b) ≤ c ^ k := by
      calc c * ((R : ℝ) / r) ^ (-b) = (2 * ((R : ℝ) / r)) ^ (-b) := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hRr.le, h2b]
        _ ≤ ((2 : ℝ) ^ k) ^ (-b) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hk2' (by linarith)
        _ = c ^ k := by
            rw [← h2b, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
              ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
    calc c * ((R : ℝ) / r) ^ (-b) * (law q).real (armEvent 0 r)
        ≤ c ^ k * (law q).real (armEvent 0 r) := mul_le_mul_of_nonneg_right hck (hA0 r)
      _ ≤ (law q).real (armEvent 0 (2 ^ k * r)) := hDk k
      _ ≤ (law q).real (armEvent 0 R) := measureReal_mono (armEvent_anti 0 hk)
  · -- upper bound: block at the `N` scales `(r + 1) 4^j ≤ R / 3`, with `R < 3 (r + 1) 4^N`
    classical
    have hex : ∃ N : ℕ, R < 3 * ((r + 1) * 4 ^ N) := by
      refine ⟨R, ?_⟩
      have h1 : R < 4 ^ R := Nat.lt_pow_self (by norm_num)
      have h2 : 4 ^ R ≤ (r + 1) * 4 ^ R := Nat.le_mul_of_pos_left _ (by omega)
      omega
    set N := Nat.find hex with hN_def
    have hN : R < 3 * ((r + 1) * 4 ^ N) := Nat.find_spec hex
    have hNmin : ∀ j < N, 3 * ((r + 1) * 4 ^ j) ≤ R := fun j hj =>
      not_lt.1 (Nat.find_min hex hj)
    have h4N : (R : ℝ) / r / 6 ≤ (4 : ℝ) ^ N := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have h1 : (r + 1) * 4 ^ N ≤ 2 * r * 4 ^ N := Nat.mul_le_mul_right _ (by omega)
      have h2 : 4 ^ N * (r * 6) = 3 * (2 * r * 4 ^ N) := by ring
      have h3 : R ≤ 4 ^ N * (r * 6) := by omega
      exact_mod_cast h3
    have hρN : ρ ^ N ≤ 6 ^ a * ((R : ℝ) / r) ^ (-a) := by
      calc ρ ^ N = ((4 : ℝ) ^ N) ^ (-a) := by
            rw [← h4a, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 4),
              ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4), mul_comm]
        _ ≤ ((R : ℝ) / r / 6) ^ (-a) :=
            Real.rpow_le_rpow_of_nonpos (div_pos hRr (by norm_num)) h4N (by linarith)
        _ = 6 ^ a * ((R : ℝ) / r) ^ (-a) := by
            rw [Real.div_rpow hRr.le (by norm_num : (0 : ℝ) ≤ 6),
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6) a, div_inv_eq_mul, mul_comm]
    calc (law q).real (armEvent 0 R) ≤ ρ ^ N * (law q).real (armEvent 0 r) := hU N hNmin
      _ ≤ 6 ^ a * ((R : ℝ) / r) ^ (-a) * (law q).real (armEvent 0 r) :=
          mul_le_mul_of_nonneg_right hρN (hA0 r)

/-- **The one-arm probability tends to zero** (XB1U). At the self-dual point of `ℤ²`, the
probability that the origin is joined to the boundary of `B_r` tends to zero as `r → ∞`. -/
theorem tendsto_law_armEvent_zero {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) :
    Tendsto (fun r : ℕ => law q (armEvent 0 r)) atTop (𝓝 0) := by
  obtain ⟨ρ, -, hρ1, hρq⟩ := exists_law_armEvent_le_pow_mul
  have hanti : Antitone fun r : ℕ => law q (armEvent (0 : LatticeSite 2) r) :=
    fun r R h => measure_mono (armEvent_anti 0 h)
  have hinf : ⨅ r : ℕ, law q (armEvent (0 : LatticeSite 2) r) = 0 := by
    refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ1)
      fun N => ?_) zero_le
    calc ⨅ r : ℕ, law q (armEvent (0 : LatticeSite 2) r) ≤ law q (armEvent 0 (3 * 4 ^ N)) :=
          iInf_le _ _
      _ ≤ ρ ^ N * law q (armEvent 0 0) :=
          hρq q hq 0 (3 * 4 ^ N) N (Nat.zero_le _) fun j hj => by
            have : 4 ^ j ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) hj.le
            omega
      _ = ρ ^ N := by rw [armEvent_zero, measure_univ, mul_one]
  rw [← hinf]
  exact tendsto_atTop_iInf hanti

/-- **Polynomial bounds on the one-arm probability** (XB1U, the case `r = 1`). At the self-dual
point of `ℤ²` there are constants `c, C, a, b > 0` such that `c R^(-b) ≤ π(R) ≤ C R^(-a)` for
every integer `R ≥ 1`, uniformly in the profile. -/
theorem exists_armEvent_polynomial_bounds :
    ∃ c C a b : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < b ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c * (R : ℝ) ^ (-b) ≤ (law q).real (armEvent 0 R) ∧
        (law q).real (armEvent 0 R) ≤ C * (R : ℝ) ^ (-a) := by
  obtain ⟨c, C, a, b, hc, hC, ha, hb, h⟩ := exists_armEvent_bounds
  refine ⟨c * 2⁻¹, C, a, b, by positivity, hC, ha, hb, fun q hq R hR => ?_⟩
  obtain ⟨-, hlow, hup⟩ := h q hq 1 R le_rfl hR
  simp only [Nat.cast_one, div_one] at hlow hup
  have h1 : (2⁻¹ : ℝ) ≤ (law q).real (armEvent 0 1) := by
    rw [measureReal_def]
    simpa using ENNReal.toReal_mono (measure_ne_top _ _) (inv_two_pow_le_law_armEvent hq 1)
  constructor
  · calc c * 2⁻¹ * (R : ℝ) ^ (-b) = c * (R : ℝ) ^ (-b) * 2⁻¹ := by ring
      _ ≤ c * (R : ℝ) ^ (-b) * (law q).real (armEvent 0 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (law q).real (armEvent 0 R) := hlow
  · calc (law q).real (armEvent 0 R) ≤ C * (R : ℝ) ^ (-a) * (law q).real (armEvent 0 1) := hup
      _ ≤ C * (R : ℝ) ^ (-a) * 1 := mul_le_mul_of_nonneg_left measureReal_le_one (by positivity)
      _ = C * (R : ℝ) ^ (-a) := mul_one _

end PercLib.Models.Planar
