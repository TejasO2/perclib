/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (circuits in annuli and the one-arm bounds, pp. 23-24).
The two-point comparison follows the proof in the PercLib wiki article critical-exponents,
section "One arm at each endpoint".
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import PercLib.Models.Planar.Arms.OneArm

/-!
# The two-point function and the one-arm probability at the self-dual point of `ℤ²`

At the self-dual point, where every nearest-neighbour edge of `ℤ²` is open with probability
`1/2` and no other pair is ever open, the two-point function `τ(0, x)` is comparable to the
square of the one-arm probability `π(r)` at the scale `r = ‖x‖∞` (wiki tag Y8K3, "One arm at
each endpoint"): there are constants `0 < c ≤ C` such that `c π(r)² ≤ τ(0, x) ≤ C π(r)²` for
every `x ≠ 0`. Here `π(r)` is the probability of `armEvent 0 r` of `Arms/Defs.lean` and `r` is
written `max (x 0).natAbs (x 1).natAbs`.

* **Upper bound** (`tau_le_law_armEvent_sq`). If `2m < ‖x‖∞`, an open path from `0` to `x`
  leaves the boxes `B_m(0)` and `B_m(x)`, so it gives an arm of radius `m` at both ends
  (`mem_armEvent_inter_armEvent_of_mem_conn`). The two boxes are disjoint, so the two arm events
  are independent (`law_inter_of_determined_internalPairs`), and the arm at `x` has the
  probability of the arm at `0` (`law_armEvent_add`). Hence `τ(0, x) ≤ π(m)²`. With
  `m = ⌊r/3⌋` and three doublings (`exists_pos_mul_law_armEvent_le_eight_mul`),
  `π(r) ≥ π(8m) ≥ c³ π(m)`; the radii `r ≤ 2` use `π(2) ≥ 1/4`.
* **Lower bound** (`law_armEvent_sq_mul_law_fourStrip_le_tau`). On the four-strip event
  `fourStrip 0 r` of the annulus `2r ≤ ‖·‖∞ ≤ 4r`, arms of radius `8r` from `0` and from `x`
  both cross the annulus, so circuit gluing (`Arms/Separator.lean`) joins them
  (`inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent`). Harris's inequality
  (`prodBernoulli_harris`, tag X5SS), the circuit bound (`exists_pos_le_law_fourStrip`) and three
  doublings give `τ(0, x) ≥ c₀ π(8r)² ≥ c₀ c⁶ π(r)²`. This half needs no hypothesis off the
  edges of `ℤ²`.
* **The comparison** (`exists_tau_comparable_armEvent_sq`), the plan's T6.
* **Exponents** (the consequences listed in Y8K3, with the conventions of tag BLNL). Since
  `log τ(0, x) = 2 log π(‖x‖∞) + O(1)` uniformly, `-log π(r) / log r → L` as `r → ∞` exactly
  when `-log τ(0, x) / log ‖x‖ → 2L` as `x → ∞` over all vertices, that is along the cofinite
  filter (`tendsto_neg_log_law_armEvent_div_log_iff`); in particular one limit exists exactly
  when the other does (`exists_tendsto_neg_log_law_armEvent_div_log_iff`), and then `η = 2/ρ`.
  Such a limit lies between the two exponents of the polynomial bounds of XB1U, so it is
  positive (`exists_pos_le_of_tendsto_neg_log_law_armEvent_div_log`). For every real `s`,
  `π(r) ≍ r^(-s)` exactly when `τ(0, x) ≍ ‖x‖^(-2s)` uniformly in `x ≠ 0`
  (`exists_armEvent_rpow_bounds_iff_exists_tau_rpow_bounds`). The norm of `ℤ² = Fin 2 → ℤ` is
  the sup norm, `‖x‖ = max |x 0| |x 1|` (mathlib's `EisensteinSeries.norm_eq_max_natAbs`).

## Main results

* `PercLib.Models.Planar.exists_tau_comparable_armEvent_sq`
* `PercLib.Models.Planar.exists_pos_mul_law_armEvent_sq_le_tau`
* `PercLib.Models.Planar.exists_tau_le_mul_law_armEvent_sq`
* `PercLib.Models.Planar.tendsto_neg_log_law_armEvent_div_log_iff`
* `PercLib.Models.Planar.exists_tendsto_neg_log_law_armEvent_div_log_iff`
* `PercLib.Models.Planar.exists_pos_le_of_tendsto_neg_log_law_armEvent_div_log`
* `PercLib.Models.Planar.exists_armEvent_rpow_bounds_iff_exists_tau_rpow_bounds`
* `PercLib.Models.Planar.tau_le_law_armEvent_sq`
* `PercLib.Models.Planar.law_armEvent_sq_mul_law_fourStrip_le_tau`
* `PercLib.Models.Planar.inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent`
* `PercLib.Models.Planar.mem_armEvent_inter_armEvent_of_mem_conn`
* `PercLib.Models.Planar.exists_pos_mul_law_armEvent_le_eight_mul`
* `PercLib.Models.Planar.law_armEvent_add`
* `PercLib.Models.Planar.law_armEvent_eq_law_armEvent_zero`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Percolation.Bond PercLib.Models.Site
  PercLib.Probability
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Translation and three doublings -/

/-- **Translation invariance of the one-arm probability.** If the profile is constant on the
edges of `ℤ^d`, the one-arm event at `x + c` has the probability of the one-arm event at `x`. -/
theorem law_armEvent_add {d : ℕ} {q : Sym2 (LatticeSite d) → unitInterval} {p : ℝ}
    (hq : ∀ e ∈ (zdGraph d).edgeSet, (q e : ℝ) = p) (x c : LatticeSite d) (r : ℕ) :
    law q (armEvent (x + c) r) = law q (armEvent x r) := by
  obtain ⟨σ, hσ⟩ := exists_zdGraph_iso_add (d := d) c
  have hσf : (⇑σ : LatticeSite d → LatticeSite d) = fun v => v + c := funext hσ
  have hq' : ∀ e ∈ (zdGraph d).edgeSet, q (Sym2.map σ e) = q e := by
    intro e he
    have he' : Sym2.map σ e ∈ (zdGraph d).edgeSet := by
      rw [← image_sym2Map_edgeSet σ]
      exact mem_image_of_mem _ he
    exact Subtype.ext (by rw [hq _ he', hq _ he])
  rw [← law_preimage_image_sym2Map_eq σ hq' (measurableSet_armEvent (x + c) r)
    (fun ω => inter_edgeSet_mem_armEvent_iff), hσf, preimage_image_add_armEvent]

/-- The one-arm event at any point has the probability of the one-arm event at the origin, if the
profile is constant on the edges of `ℤ^d`. -/
theorem law_armEvent_eq_law_armEvent_zero {d : ℕ} {q : Sym2 (LatticeSite d) → unitInterval}
    {p : ℝ} (hq : ∀ e ∈ (zdGraph d).edgeSet, (q e : ℝ) = p) (x : LatticeSite d) (r : ℕ) :
    law q (armEvent x r) = law q (armEvent 0 r) := by
  simpa only [zero_add] using law_armEvent_add hq 0 x r

/-- **Three doublings.** At the self-dual point there is `c > 0` such that `c π(r) ≤ π(8r)` for
every radius `r`, uniformly in the profile. -/
theorem exists_pos_mul_law_armEvent_le_eight_mul :
    ∃ c : ℝ, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ r : ℕ, c * (law q).real (armEvent 0 r) ≤ (law q).real (armEvent 0 (8 * r)) := by
  obtain ⟨cE, hcE, hcE1, hcEq⟩ := exists_pos_mul_law_armEvent_le
  have hcE' : cE ≠ ∞ := (hcE1.trans ENNReal.one_lt_top).ne
  set c := cE.toReal with hc_def
  have hc : 0 < c := ENNReal.toReal_pos hcE.ne' hcE'
  refine ⟨c ^ 3, by positivity, fun q hq r => ?_⟩
  have hD : ∀ t : ℕ, c * (law q).real (armEvent 0 t) ≤ (law q).real (armEvent 0 (2 * t)) := by
    intro t
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hcEq q hq t)
    rw [ENNReal.toReal_mul] at h
    exact h
  calc c ^ 3 * (law q).real (armEvent 0 r) = c * (c * (c * (law q).real (armEvent 0 r))) := by
        ring
    _ ≤ c * (c * (law q).real (armEvent 0 (2 * r))) := by gcongr; exact hD r
    _ ≤ c * (law q).real (armEvent 0 (2 * (2 * r))) := by gcongr; exact hD _
    _ ≤ (law q).real (armEvent 0 (2 * (2 * (2 * r)))) := hD _
    _ = (law q).real (armEvent 0 (8 * r)) := by rw [show 2 * (2 * (2 * r)) = 8 * r by ring]

/-! ### The upper bound -/

/-- **A connection forces two arms.** If `x` and `y` are joined by an open path of
nearest-neighbour edges and `y` lies outside the box `x + [-(m - 1), m - 1]^d`, then both `x`
and `y` have an arm of radius `m`. -/
theorem mem_armEvent_inter_armEvent_of_mem_conn {d : ℕ} {x y : LatticeSite d} {m : ℕ}
    {ω : Config (LatticeSite d)} (hy : y ∉ Icc (x - m + 1) (x + m - 1))
    (h : ω ∩ (zdGraph d).edgeSet ∈ conn x y) : ω ∈ armEvent x m ∩ armEvent y m := by
  refine ⟨mem_armEvent_of_mem_conn hy h, mem_armEvent_of_mem_conn (fun hx => hy ?_)
    (by rwa [conn_symm] at h)⟩
  simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Pi.one_apply] at hx ⊢
  exact ⟨fun j => by have := hx.1 j; have := hx.2 j; omega,
    fun j => by have := hx.1 j; have := hx.2 j; omega⟩

/-- **Upper bound for the two-point function.** If the profile is constant on the edges of
`ℤ^d` and vanishes off them, and `2m < |x i|` for some coordinate `i`, then `τ(0, x) ≤ π(m)²`: a
connection from `0` to `x` forces an arm of radius `m` at each end, in the disjoint boxes
`B_m(0)` and `B_m(x)`. -/
theorem tau_le_law_armEvent_sq {d : ℕ} {q : Sym2 (LatticeSite d) → unitInterval} {p : ℝ}
    (hq : ∀ e ∈ (zdGraph d).edgeSet, (q e : ℝ) = p) (hq0 : ∀ e ∉ (zdGraph d).edgeSet, q e = 0)
    {x : LatticeSite d} {m : ℕ} (hm : ∃ i, 2 * m < (x i).natAbs) :
    tau q 0 x ≤ law q (armEvent 0 m) ^ 2 := by
  obtain ⟨i, hi⟩ := hm
  have hdisj : Disjoint (Icc ((0 : LatticeSite d) - m) (0 + m)) (Icc (x - m) (x + m)) := by
    rw [Set.disjoint_left]
    intro v hv hvx
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      Pi.zero_apply] at hv hvx
    have h₁ := hv.1 i
    have h₂ := hv.2 i
    have h₃ := hvx.1 i
    have h₄ := hvx.2 i
    omega
  have hsub : (conn (0 : LatticeSite d) x : Set (Config (LatticeSite d))) ≤ᵐ[law q]
      armEvent 0 m ∩ armEvent x m := by
    filter_upwards [ae_config_subset_host (zdGraph d) q hq0] with ω hωL hω
    refine mem_armEvent_inter_armEvent_of_mem_conn (fun hx => ?_) ?_
    · simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
        Pi.zero_apply, Pi.one_apply] at hx
      have h₁ := hx.1 i
      have h₂ := hx.2 i
      omega
    · rw [inter_eq_left.2 hωL]
      exact hω
  calc tau q 0 x = law q (conn 0 x) := rfl
    _ ≤ law q (armEvent 0 m ∩ armEvent x m) := measure_mono_ae hsub
    _ = law q (armEvent 0 m) * law q (armEvent x m) :=
        law_inter_of_determined_internalPairs q hdisj (measurableSet_armEvent _ _)
          (measurableSet_armEvent _ _) (fun ω ω' h => mem_armEvent_iff_of_inter_eq subset_rfl h)
          (fun ω ω' h => mem_armEvent_iff_of_inter_eq subset_rfl h)
    _ = law q (armEvent 0 m) ^ 2 := by
        rw [law_armEvent_eq_law_armEvent_zero hq x m, sq]

/-- **The upper half of the two-point comparison** (Y8K3). At the self-dual point of `ℤ²`, with
no pair other than the edges of `ℤ²` ever open, there is `C > 0` such that
`τ(0, x) ≤ C π(‖x‖∞)²` for every `x ≠ 0`. -/
theorem exists_tau_le_mul_law_armEvent_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → (∀ e ∉ (zdGraph 2).edgeSet, q e = 0) →
      ∀ x : LatticeSite 2, x ≠ 0 →
        (tau q 0 x).toReal ≤
          C * (law q).real (armEvent 0 (max (x 0).natAbs (x 1).natAbs)) ^ 2 := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_mul_law_armEvent_le_eight_mul
  refine ⟨max (c ^ 2)⁻¹ 16, lt_max_of_lt_right (by norm_num), fun q hq hq0 x hx => ?_⟩
  set r := max (x 0).natAbs (x 1).natAbs with hr
  have hA0 : ∀ t : ℕ, 0 ≤ (law q).real (armEvent (0 : LatticeSite 2) t) :=
    fun t => measureReal_nonneg
  rcases lt_or_ge r 3 with hr3 | hr3
  · -- small radii: `τ ≤ 1` and `π(r) ≥ π(2) ≥ 1/4`
    have hA : (2⁻¹ : ℝ) ^ 2 ≤ (law q).real (armEvent 0 r) := by
      rw [measureReal_def]
      simpa using ENNReal.toReal_mono (measure_ne_top _ _)
        ((inv_two_pow_le_law_armEvent hq 2).trans (measure_mono (armEvent_anti 0 (by omega))))
    have hτ : (tau q 0 x).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (tau_le_one q 0 x)
    calc (tau q 0 x).toReal ≤ 1 := hτ
      _ = 16 * ((2⁻¹ : ℝ) ^ 2) ^ 2 := by norm_num
      _ ≤ 16 * (law q).real (armEvent 0 r) ^ 2 := by gcongr
      _ ≤ max (c ^ 2)⁻¹ 16 * (law q).real (armEvent 0 r) ^ 2 := by
          gcongr
          exact le_max_right _ _
  · -- `m = ⌊r/3⌋`: the boxes `B_m(0)` and `B_m(x)` are disjoint and `r ≤ 8m`
    set m := r / 3 with hm
    have hτ : (tau q 0 x).toReal ≤ (law q).real (armEvent 0 m) ^ 2 := by
      have h := tau_le_law_armEvent_sq hq hq0 (x := x) (m := m)
        (Fin.exists_fin_two.2 (by omega))
      have h' := ENNReal.toReal_mono (ENNReal.pow_ne_top (measure_ne_top _ _)) h
      rw [ENNReal.toReal_pow] at h'
      exact h'
    have hcm : c * (law q).real (armEvent 0 m) ≤ (law q).real (armEvent 0 r) :=
      (hcq q hq m).trans (measureReal_mono (armEvent_anti 0 (by omega)))
    have h1 : (law q).real (armEvent 0 m) ^ 2 ≤ (c ^ 2)⁻¹ * (law q).real (armEvent 0 r) ^ 2 := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      calc (law q).real (armEvent 0 m) ^ 2 * c ^ 2 = (c * (law q).real (armEvent 0 m)) ^ 2 := by
            ring
        _ ≤ (law q).real (armEvent 0 r) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hc.le (hA0 m)) hcm 2
    calc (tau q 0 x).toReal ≤ (law q).real (armEvent 0 m) ^ 2 := hτ
      _ ≤ (c ^ 2)⁻¹ * (law q).real (armEvent 0 r) ^ 2 := h1
      _ ≤ max (c ^ 2)⁻¹ 16 * (law q).real (armEvent 0 r) ^ 2 := by
          gcongr
          exact le_max_left _ _

/-! ### The lower bound -/

/-- **Two arms meet on a circuit.** On the four-strip event of the annulus
`2n ≤ ‖v - z‖∞ ≤ 4n`, two points `a, b` of the inner box `B_{2n}(z)` with arms of radii at least
`6n` are joined by an open path inside `B_{4n}(z)`: both arms leave `B_{4n - 1}(z)`. -/
theorem inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent
    {ω : Config (LatticeSite 2)} {z a b : LatticeSite 2} {n R R' : ℕ} (hω : ω ∈ fourStrip z n)
    (ha : a ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (hb : b ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (hR : 6 * n ≤ R) (hR' : 6 * n ≤ R') (haR : ω ∈ armEvent a R) (hbR : ω ∈ armEvent b R') :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2))) a b := by
  obtain ⟨y, hy, hay⟩ := mem_armEvent_iff_exists_notMem_conn.1 haR
  obtain ⟨y', hy', hby'⟩ := mem_armEvent_iff_exists_notMem_conn.1 hbR
  have ha' := mem_Icc_two_iff.1 ha
  have hb' := mem_Icc_two_iff.1 hb
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at ha' hb'
  refine inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn hω ha hb
    (fun h => hy ?_) (fun h => hy' ?_) hay hby'
  · rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega
  · rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega

/-- **Lower bound for the two-point function.** If the profile is constant on the edges of
`ℤ²`, `‖x‖∞ ≤ 2n` and `6n ≤ R`, then `π(R)² P(fourStrip 0 n) ≤ τ(0, x)`: arms of radius `R` at
`0` and at `x` and the four-strip event of the annulus `2n ≤ ‖·‖∞ ≤ 4n` join `0` to `x`, and
Harris's inequality applies to the three increasing events. -/
theorem law_armEvent_sq_mul_law_fourStrip_le_tau {q : Sym2 (LatticeSite 2) → unitInterval}
    {p : ℝ} (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = p) {x : LatticeSite 2} {n R : ℕ}
    (hx : max (x 0).natAbs (x 1).natAbs ≤ 2 * n) (hR : 6 * n ≤ R) :
    law q (armEvent 0 R) ^ 2 * law q (fourStrip 0 n) ≤ tau q 0 x := by
  have hsub : armEvent (0 : LatticeSite 2) R ∩ armEvent x R ∩ fourStrip 0 n ⊆ conn 0 x := by
    rintro ω ⟨⟨h0, hxR⟩, hω⟩
    have h0B : (0 : LatticeSite 2) ∈
        Icc (0 - ((2 * n : ℕ) : LatticeSite 2)) (0 + ((2 * n : ℕ) : LatticeSite 2)) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply]
      omega
    have hxB : x ∈ Icc (0 - ((2 * n : ℕ) : LatticeSite 2)) (0 + ((2 * n : ℕ) : LatticeSite 2)) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.zero_apply]
      omega
    exact conn_mono inter_subset_left (localConn_subset_conn _ _ _
      (inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent hω h0B hxB hR hR h0 hxR))
  have hu₁ : IsUpperSet (armEvent (0 : LatticeSite 2) R) := isUpperSet_armEvent 0 R
  have hu₂ : IsUpperSet (armEvent x R) := isUpperSet_armEvent x R
  have hu₃ : IsUpperSet (fourStrip 0 n) := isUpperSet_fourStrip 0 n
  have hm₁ : MeasurableSet (armEvent (0 : LatticeSite 2) R) := measurableSet_armEvent 0 R
  have hm₂ : MeasurableSet (armEvent x R) := measurableSet_armEvent x R
  have hm₃ : MeasurableSet (fourStrip 0 n) := measurableSet_fourStrip 0 n
  calc law q (armEvent 0 R) ^ 2 * law q (fourStrip 0 n)
      = law q (armEvent 0 R) * law q (armEvent x R) * law q (fourStrip 0 n) := by
        rw [law_armEvent_eq_law_armEvent_zero hq x R, sq]
    _ ≤ law q (armEvent 0 R ∩ armEvent x R) * law q (fourStrip 0 n) := by
        gcongr
        exact prodBernoulli_harris q hu₁ hu₂ hm₁ hm₂
    _ ≤ law q (armEvent 0 R ∩ armEvent x R ∩ fourStrip 0 n) :=
        prodBernoulli_harris q (hu₁.inter hu₂) hu₃ (hm₁.inter hm₂) hm₃
    _ ≤ tau q 0 x := measure_mono hsub

/-- **The lower half of the two-point comparison** (Y8K3). At the self-dual point of `ℤ²` there is
`c > 0` such that `c π(‖x‖∞)² ≤ τ(0, x)` for every `x ≠ 0`, whatever the profile off the edges of
`ℤ²`. -/
theorem exists_pos_mul_law_armEvent_sq_le_tau :
    ∃ c : ℝ, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ x : LatticeSite 2, x ≠ 0 →
        c * (law q).real (armEvent 0 (max (x 0).natAbs (x 1).natAbs)) ^ 2 ≤
          (tau q 0 x).toReal := by
  obtain ⟨c₀, hc₀, hc₀q⟩ := exists_pos_le_law_fourStrip
  obtain ⟨c, hc, hcq⟩ := exists_pos_mul_law_armEvent_le_eight_mul
  have hc₀' : min c₀ 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set c₁ := (min c₀ 1).toReal with hc₁_def
  have hc₁ : 0 < c₁ := ENNReal.toReal_pos (lt_min hc₀ one_pos).ne' hc₀'
  refine ⟨c₁ * c ^ 2, by positivity, fun q hq x hx => ?_⟩
  set r := max (x 0).natAbs (x 1).natAbs with hr
  have hr1 : 1 ≤ r := by
    by_contra h
    exact hx (funext (Fin.forall_fin_two.2
      ⟨by simp only [Pi.zero_apply]; omega, by simp only [Pi.zero_apply]; omega⟩))
  have hlow : (law q).real (armEvent 0 (8 * r)) ^ 2 * c₁ ≤ (tau q 0 x).toReal := by
    have h₁ : law q (armEvent 0 (8 * r)) ^ 2 * min c₀ 1 ≤ tau q 0 x :=
      (mul_le_mul' le_rfl ((min_le_left _ _).trans (hc₀q q hq 0 r hr1))).trans
        (law_armEvent_sq_mul_law_fourStrip_le_tau hq (x := x) (n := r) (R := 8 * r)
          (by omega) (by omega))
    have h₂ := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q 0 x)) h₁
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h₂
    exact h₂
  have hA0 : 0 ≤ (law q).real (armEvent (0 : LatticeSite 2) r) := measureReal_nonneg
  calc c₁ * c ^ 2 * (law q).real (armEvent 0 r) ^ 2 =
        c₁ * (c * (law q).real (armEvent 0 r)) ^ 2 := by ring
    _ ≤ c₁ * (law q).real (armEvent 0 (8 * r)) ^ 2 := by
        gcongr
        exact hcq q hq r
    _ = (law q).real (armEvent 0 (8 * r)) ^ 2 * c₁ := mul_comm _ _
    _ ≤ (tau q 0 x).toReal := hlow

/-! ### The two-point comparison -/

/-- **T6: the two-point function is comparable to the square of the one-arm probability**
(tag Y8K3). At the self-dual point of `ℤ²`, where every edge of `ℤ²` is open with probability
`1/2` and no other pair is ever open, there are constants `0 < c ≤ C` such that every `x ≠ 0`
satisfies `c π(r)² ≤ τ(0, x) ≤ C π(r)²` with `r = ‖x‖∞ = max |x 0| |x 1|` and `π(r)` the
probability of `armEvent 0 r`. -/
theorem exists_tau_comparable_armEvent_sq :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → (∀ e ∉ (zdGraph 2).edgeSet, q e = 0) →
      ∀ x : LatticeSite 2, x ≠ 0 →
        c * (law q).real (armEvent 0 (max (x 0).natAbs (x 1).natAbs)) ^ 2 ≤
          (tau q 0 x).toReal ∧
        (tau q 0 x).toReal ≤
          C * (law q).real (armEvent 0 (max (x 0).natAbs (x 1).natAbs)) ^ 2 := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_mul_law_armEvent_sq_le_tau
  obtain ⟨C, hC, hCq⟩ := exists_tau_le_mul_law_armEvent_sq
  refine ⟨min c C, C, lt_min hc hC, min_le_right _ _, fun q hq hq0 x hx =>
    ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hcq q hq x hx),
      hCq q hq hq0 x hx⟩⟩

/-! ### Exponents -/

/-- **The logarithmic one-arm and two-point exponents** (Y8K3, conventions of tag BLNL). At the
self-dual point of `ℤ²`, with no pair other than the edges of `ℤ²` ever open, for every real `L`:
`-log π(r) / log r → L` as `r → ∞` if and only if `-log τ(0, x) / log ‖x‖ → 2L` as `x → ∞`
over all vertices (along the cofinite filter). With `1/ρ = L` and `η = 2L` this is `η = 2/ρ`. -/
theorem tendsto_neg_log_law_armEvent_div_log_iff {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) (hq0 : ∀ e ∉ (zdGraph 2).edgeSet, q e = 0)
    (L : ℝ) :
    Tendsto (fun r : ℕ => -Real.log ((law q).real (armEvent 0 r)) / Real.log r) atTop (𝓝 L) ↔
      Tendsto (fun x : LatticeSite 2 => -Real.log (tau q 0 x).toReal / Real.log ‖x‖) cofinite
        (𝓝 (2 * L)) := by
  obtain ⟨c, C, hc, hcC, h⟩ := exists_tau_comparable_armEvent_sq
  have hC : 0 < C := hc.trans_le hcC
  obtain ⟨ρ, hρ⟩ : ∃ ρ : LatticeSite 2 → ℕ, ρ = fun x => max (x 0).natAbs (x 1).natAbs :=
    ⟨_, rfl⟩
  have h' : ∀ x : LatticeSite 2, x ≠ 0 →
      c * (law q).real (armEvent 0 (ρ x)) ^ 2 ≤ (tau q 0 x).toReal ∧
        (tau q 0 x).toReal ≤ C * (law q).real (armEvent 0 (ρ x)) ^ 2 := by
    intro x hx
    rw [hρ]
    exact h q hq hq0 x hx
  have hρn : ∀ x : LatticeSite 2, ‖x‖ = (ρ x : ℝ) := fun x => by
    rw [hρ]
    exact EisensteinSeries.norm_eq_max_natAbs x
  set F := fun r : ℕ => -Real.log ((law q).real (armEvent 0 r)) / Real.log r with hF
  set G := fun x : LatticeSite 2 => -Real.log (tau q 0 x).toReal / Real.log ‖x‖ with hG
  -- the one-arm probability is positive
  have hA : ∀ r : ℕ, 0 < (law q).real (armEvent (0 : LatticeSite 2) r) := fun r =>
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) r)
      (inv_two_pow_le_law_armEvent hq r))) (measure_ne_top _ _)
  -- `log τ(0, x) = 2 log π(‖x‖∞) + O(1)`
  set K := |Real.log c| + |Real.log C| with hK_def
  have hK : ∀ x : LatticeSite 2, x ≠ 0 →
      |Real.log (tau q 0 x).toReal - 2 * Real.log ((law q).real (armEvent 0 (ρ x)))| ≤ K := by
    intro x hx
    obtain ⟨h₁, h₂⟩ := h' x hx
    have hAx := hA (ρ x)
    have hpos : 0 < c * (law q).real (armEvent 0 (ρ x)) ^ 2 := by positivity
    have l₁ := Real.log_le_log hpos h₁
    have l₂ := Real.log_le_log (hpos.trans_le h₁) h₂
    rw [Real.log_mul hc.ne' (by positivity), Real.log_pow] at l₁
    rw [Real.log_mul hC.ne' (by positivity), Real.log_pow] at l₂
    push_cast at l₁ l₂
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log C)]
    · linarith [le_abs_self (Real.log C), abs_nonneg (Real.log c)]
  have hbound : ∀ x : LatticeSite 2, x ≠ 0 →
      ‖G x - 2 * F (ρ x)‖ ≤ K / Real.log (ρ x) := by
    intro x hx
    have hlog : 0 ≤ Real.log (ρ x) := Real.log_natCast_nonneg _
    have heq : G x - 2 * F (ρ x) = -(Real.log (tau q 0 x).toReal -
        2 * Real.log ((law q).real (armEvent 0 (ρ x)))) / Real.log (ρ x) := by
      simp only [hF, hG, hρn x]
      ring
    rw [heq, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hlog]
    exact div_le_div_of_nonneg_right (hK x hx) hlog
  have hD : Tendsto (fun r : ℕ => K / Real.log r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  constructor
  · -- along all vertices, `‖x‖∞ → ∞`
    intro hFL
    have hρt : Tendsto ρ cofinite atTop := by
      have h₁ : Tendsto (fun x : LatticeSite 2 => ‖x‖) cofinite atTop := by
        rw [← cocompact_eq_cofinite]
        exact tendsto_norm_cocompact_atTop
      exact tendsto_natCast_atTop_iff.1 (h₁.congr hρn)
    have h₁ : Tendsto (fun x => G x - 2 * F (ρ x)) cofinite (𝓝 0) :=
      squeeze_zero_norm' ((eventually_cofinite_ne 0).mono hbound) (hD.comp hρt)
    have h₂ : Tendsto (fun x => 2 * F (ρ x)) cofinite (𝓝 (2 * L)) :=
      (hFL.comp hρt).const_mul 2
    simpa using h₁.add h₂
  · -- along the vertices `(r, 0)`
    intro hGL
    obtain ⟨e, he⟩ : ∃ e : ℕ → LatticeSite 2, e = fun r : ℕ => ![(r : ℤ), 0] := ⟨_, rfl⟩
    have he0 : ∀ r, e r 0 = r := fun r => by simp [he]
    have hρe : ∀ r, ρ (e r) = r := fun r => by simp [hρ, he]
    have het : Tendsto e atTop cofinite := by
      rw [← Nat.cofinite_eq_atTop]
      exact Function.Injective.tendsto_cofinite fun r s hrs => by
        have := congrFun hrs 0
        rw [he0, he0] at this
        exact_mod_cast this
    have h₁ : Tendsto (fun r => G (e r) - 2 * F r) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hD
      filter_upwards [eventually_ne_atTop 0] with r hr
      have hne : e r ≠ 0 := fun h0 => hr (by
        have := congrFun h0 0
        rw [he0, Pi.zero_apply] at this
        exact_mod_cast this)
      have := hbound (e r) hne
      rwa [hρe] at this
    have h₂ := ((hGL.comp het).sub h₁).const_mul (1 / 2)
    have h₃ : Tendsto F atTop (𝓝 (1 / 2 * (2 * L - 0))) :=
      h₂.congr fun r => by simp only [Function.comp]; ring
    rwa [show 1 / 2 * (2 * L - 0) = L by ring] at h₃

/-- **Existence of the exponents** (Y8K3). At the self-dual point of `ℤ²`, with no pair other than
the edges of `ℤ²` ever open, the logarithmic one-arm limit `lim -log π(r) / log r` exists if and
only if the logarithmic two-point limit `lim -log τ(0, x) / log ‖x‖` exists over all vertices
tending to infinity. -/
theorem exists_tendsto_neg_log_law_armEvent_div_log_iff {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2)
    (hq0 : ∀ e ∉ (zdGraph 2).edgeSet, q e = 0) :
    (∃ L : ℝ, Tendsto (fun r : ℕ => -Real.log ((law q).real (armEvent 0 r)) / Real.log r) atTop
      (𝓝 L)) ↔
      ∃ M : ℝ, Tendsto (fun x : LatticeSite 2 => -Real.log (tau q 0 x).toReal / Real.log ‖x‖)
        cofinite (𝓝 M) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨2 * L, (tendsto_neg_log_law_armEvent_div_log_iff hq hq0 L).1 hL⟩
  · rintro ⟨M, hM⟩
    refine ⟨M / 2, (tendsto_neg_log_law_armEvent_div_log_iff hq hq0 (M / 2)).2 ?_⟩
    rwa [show 2 * (M / 2) = M by ring]

/-- **The logarithmic one-arm limit is positive** (XB1U, as used in Y8K3). At the self-dual point
of `ℤ²` there are `0 < a` and `b` such that every limit `L` of `-log π(r) / log r` satisfies
`a ≤ L ≤ b`: the polynomial bounds `c r^(-b) ≤ π(r) ≤ C r^(-a)`. -/
theorem exists_pos_le_of_tendsto_neg_log_law_armEvent_div_log :
    ∃ a b : ℝ, 0 < a ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ L : ℝ,
      Tendsto (fun r : ℕ => -Real.log ((law q).real (armEvent 0 r)) / Real.log r) atTop (𝓝 L) →
        a ≤ L ∧ L ≤ b := by
  obtain ⟨c, C, a, b, hc, hC, ha, hb, h⟩ := exists_armEvent_polynomial_bounds
  refine ⟨a, b, ha, fun q hq L hL => ⟨?_, ?_⟩⟩
  · have hlow : Tendsto (fun r : ℕ => a - Real.log C / Real.log r) atTop (𝓝 (a - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    rw [sub_zero] at hlow
    refine le_of_tendsto_of_tendsto hlow hL ?_
    filter_upwards [eventually_ge_atTop 2] with r hr
    have hr1 : 1 < (r : ℝ) := by exact_mod_cast hr
    have hr0 : 0 < (r : ℝ) := by linarith
    have hlog : 0 < Real.log r := Real.log_pos hr1
    obtain ⟨hlo, hup⟩ := h q hq r (by omega)
    have hpos : 0 < c * (r : ℝ) ^ (-b) := by positivity
    have l := Real.log_le_log (hpos.trans_le hlo) hup
    rw [Real.log_mul hC.ne' (by positivity), Real.log_rpow hr0] at l
    have e : a - Real.log C / Real.log r = (a * Real.log r - Real.log C) / Real.log r := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hlog.le
  · have hup : Tendsto (fun r : ℕ => b - Real.log c / Real.log r) atTop (𝓝 (b - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    rw [sub_zero] at hup
    refine le_of_tendsto_of_tendsto hL hup ?_
    filter_upwards [eventually_ge_atTop 2] with r hr
    have hr1 : 1 < (r : ℝ) := by exact_mod_cast hr
    have hr0 : 0 < (r : ℝ) := by linarith
    have hlog : 0 < Real.log r := Real.log_pos hr1
    obtain ⟨hlo, -⟩ := h q hq r (by omega)
    have hpos : 0 < c * (r : ℝ) ^ (-b) := by positivity
    have l := Real.log_le_log hpos hlo
    rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow hr0] at l
    have e : b - Real.log c / Real.log r = (b * Real.log r - Real.log c) / Real.log r := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hlog.le

/-- **Power laws** (Y8K3). At the self-dual point of `ℤ²`, with no pair other than the edges of
`ℤ²` ever open, for every real `s`: `π(r) ≍ r^(-s)` over the integers `r ≥ 1` if and only if
`τ(0, x) ≍ ‖x‖^(-2s)` uniformly in `x ≠ 0`. -/
theorem exists_armEvent_rpow_bounds_iff_exists_tau_rpow_bounds
    {q : Sym2 (LatticeSite 2) → unitInterval} (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2)
    (hq0 : ∀ e ∉ (zdGraph 2).edgeSet, q e = 0) (s : ℝ) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
      c * (r : ℝ) ^ (-s) ≤ (law q).real (armEvent 0 r) ∧
        (law q).real (armEvent 0 r) ≤ C * (r : ℝ) ^ (-s)) ↔
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : LatticeSite 2, x ≠ 0 →
      c * ‖x‖ ^ (-(2 * s)) ≤ (tau q 0 x).toReal ∧ (tau q 0 x).toReal ≤ C * ‖x‖ ^ (-(2 * s))) := by
  obtain ⟨c, C, hc, hcC, h⟩ := exists_tau_comparable_armEvent_sq
  have hC : 0 < C := hc.trans_le hcC
  have hpow : ∀ t : ℝ, 0 ≤ t → (t ^ (-s)) ^ 2 = t ^ (-(2 * s)) := fun t ht => by
    rw [← Real.rpow_mul_natCast ht]
    congr 1
    push_cast
    ring
  constructor
  · rintro ⟨c₁, C₁, hc₁, hC₁, h₁⟩
    refine ⟨c * c₁ ^ 2, C * C₁ ^ 2, by positivity, by positivity, fun x hx => ?_⟩
    obtain ⟨hlo, hup⟩ := h q hq hq0 x hx
    rw [EisensteinSeries.norm_eq_max_natAbs x]
    set r := max (x 0).natAbs (x 1).natAbs with hr
    have hr1 : 1 ≤ r := by
      by_contra h0
      exact hx (funext (Fin.forall_fin_two.2
        ⟨by simp only [Pi.zero_apply]; omega, by simp only [Pi.zero_apply]; omega⟩))
    obtain ⟨hA₁, hA₂⟩ := h₁ r hr1
    have hrs : 0 ≤ (r : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hA0 : 0 ≤ (law q).real (armEvent (0 : LatticeSite 2) r) := measureReal_nonneg
    constructor
    · calc c * c₁ ^ 2 * (r : ℝ) ^ (-(2 * s)) = c * (c₁ * (r : ℝ) ^ (-s)) ^ 2 := by
            rw [mul_pow, hpow _ (Nat.cast_nonneg _)]
            ring
        _ ≤ c * (law q).real (armEvent 0 r) ^ 2 := by gcongr
        _ ≤ (tau q 0 x).toReal := hlo
    · calc (tau q 0 x).toReal ≤ C * (law q).real (armEvent 0 r) ^ 2 := hup
        _ ≤ C * (C₁ * (r : ℝ) ^ (-s)) ^ 2 := by gcongr
        _ = C * C₁ ^ 2 * (r : ℝ) ^ (-(2 * s)) := by
            rw [mul_pow, hpow _ (Nat.cast_nonneg _)]
            ring
  · rintro ⟨c₂, C₂, hc₂, hC₂, h₂⟩
    refine ⟨Real.sqrt (c₂ / C), Real.sqrt (C₂ / c), by positivity, by positivity, fun r hr => ?_⟩
    obtain ⟨x, hx_def⟩ : ∃ x : LatticeSite 2, x = ![(r : ℤ), 0] := ⟨_, rfl⟩
    have hx : x ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp only [hx_def, Matrix.cons_val_zero, Pi.zero_apply] at this
      omega
    have hrx : max (x 0).natAbs (x 1).natAbs = r := by simp [hx_def]
    have hnx : ‖x‖ = r := by rw [EisensteinSeries.norm_eq_max_natAbs, hrx]
    obtain ⟨hlo, hup⟩ := h q hq hq0 x hx
    obtain ⟨hlo₂, hup₂⟩ := h₂ x hx
    rw [hrx] at hlo hup
    rw [hnx] at hlo₂ hup₂
    have hA0 : 0 ≤ (law q).real (armEvent (0 : LatticeSite 2) r) := measureReal_nonneg
    have hrs : 0 ≤ (r : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    constructor
    · refine (pow_le_pow_iff_left₀ (by positivity) hA0 two_ne_zero).1 ?_
      rw [mul_pow, Real.sq_sqrt (by positivity), hpow _ (Nat.cast_nonneg _), div_mul_eq_mul_div,
        div_le_iff₀ hC]
      linarith
    · refine (pow_le_pow_iff_left₀ hA0 (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, Real.sq_sqrt (by positivity), hpow _ (Nat.cast_nonneg _), div_mul_eq_mul_div,
        le_div_iff₀ hc]
      linarith

end PercLib.Models.Planar
