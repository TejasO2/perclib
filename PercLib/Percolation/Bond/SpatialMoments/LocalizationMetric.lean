/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, adapting the group-based proofs of
`PercLib.Percolation.Bond.SpatialMoments.Localization`. Mathematical reference:
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.4.1.
No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Spatial moments localise the volume, without a group structure

For a countable vertex type `V`, a profile `q`, a root `o` and an arbitrary function
`f : V → ℝ` (for instance `f = (dist · o)` on a pseudometric space), write `B_R = {x | f x ≤ R}`
and `S = E[∑_{x ∈ K_o} f(x)^p]`. Nothing about `f` is assumed: no group structure, no sign.

## Main results

* `encard_diff_le_mul_tsum_indicator`: pointwise in the configuration,
  `|K_o \ B_R| ≤ R^{-p} ∑_{x ∈ K_o} f(x)^p`.
* `lintegral_encard_diff_le_of_lintegral_le`: if `S ≤ (C_p r)^p χ`, then
  `E|K_o \ B_{C r}| ≤ (C_p / C)^p χ`.
* `chi_eq_lintegral_encard_inter_add_diff`: `χ = E|K_o ∩ A| + E|K_o \ A|` for every set `A`.
* `exists_chi_le_mul_lintegral_encard_inter`: for every `ε > 0` one `C > 0`, depending only on
  `p`, `C_p`, `ε`, gives `χ ≤ (1 + ε) E|K_o ∩ B_{C r}|` whenever `S ≤ (C_p r)^p χ < ∞`.
* `law_encard_diff_pos_le`: `P(|K_o \ A| > 0) ≤ E|K_o \ A|` (Markov).
* Metric forms, with `B_R = closedBall o R` and the correlation length
  `ξ_p = (E[∑_{x ∈ K_o} d(o, x)^p] / χ)^{1/p}`:
  `lintegral_encard_diff_closedBall_div_chi_le`,
  `exists_chi_le_mul_lintegral_encard_inter_closedBall`,
  `law_encard_diff_closedBall_pos_le`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Group-free localization along an arbitrary function -/

/-- The cluster volume inside a set is measurable. -/
theorem measurable_encard_cluster_inter [Countable V] (o : V) (A : Set V) :
    Measurable fun ω : Config V => ((cluster ω o ∩ A).encard : ℝ≥0∞) :=
  (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
    (measurable_encard.comp (Measurable.of_mem fun x => by
      by_cases hx : x ∈ A
      · simp only [mem_inter_iff, hx, and_true]
        exact (measurableSet_conn o x).mem
      · simp only [mem_inter_iff, hx, and_false]
        exact measurable_const))

/-- **Pointwise Markov bound.** Every vertex of `K_o` with `f x > R > 0` contributes more
than `R^p` to `∑_{x ∈ K_o} f(x)^p`. -/
theorem encard_diff_le_mul_tsum_indicator (ω : Config V) (o : V) (f : V → ℝ) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R) :
    ((cluster ω o \ {x | f x ≤ R}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((R ^ p)⁻¹) *
        ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (f x ^ p)) x := by
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  rw [← ENNReal.tsum_set_one, tsum_subtype (cluster ω o \ {x | f x ≤ R}) (fun _ => (1 : ℝ≥0∞)),
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ cluster ω o \ {x | f x ≤ R}
  · rw [indicator_of_mem hx, indicator_of_mem hx.1,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hRp.le), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, one_le_div hRp]
    exact Real.rpow_le_rpow hR.le (le_of_lt (not_le.1 hx.2)) hp.le
  · rw [indicator_of_notMem hx]
    exact zero_le

/-- **Localization from the spatial moment.** Let `p, r, C > 0` and `C_p ≥ 0`. If
`E[∑_{x ∈ K_o} f(x)^p] ≤ (C_p r)^p χ`, then `E|K_o \ {f ≤ C r}| ≤ (C_p / C)^p χ`. -/
theorem lintegral_encard_diff_le_of_lintegral_le [Countable V] (q : Sym2 V → unitInterval)
    (o : V) {f : V → ℝ} {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C)
    (hS : ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂law q ≤
      ENNReal.ofReal ((Cp * r) ^ p) * chi q o) :
    ∫⁻ ω, ((cluster ω o \ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂law q ≤
      ENNReal.ofReal ((Cp / C) ^ p) * chi q o := by
  have hCr : 0 < C * r := mul_pos hC hr
  have hCrp : 0 < (C * r) ^ p := Real.rpow_pos_of_pos hCr p
  calc ∫⁻ ω, ((cluster ω o \ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂law q
      ≤ ∫⁻ ω, ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂law q :=
        lintegral_mono fun ω => encard_diff_le_mul_tsum_indicator ω o f hp hCr
    _ = ENNReal.ofReal (((C * r) ^ p)⁻¹) *
          ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂law q :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (((C * r) ^ p)⁻¹) * (ENNReal.ofReal ((Cp * r) ^ p) * chi q o) := by
        gcongr
    _ = ENNReal.ofReal ((Cp / C) ^ p) * chi q o := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hCrp.le)]
        congr 2
        rw [Real.mul_rpow (NNReal.coe_nonneg Cp) hr.le, Real.mul_rpow hC.le hr.le,
          Real.div_rpow (NNReal.coe_nonneg Cp) hC.le]
        have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
        have hCp' : 0 < C ^ p := Real.rpow_pos_of_pos hC p
        field_simp

/-- The expected volume of `K_o` is the expected volume inside `A` plus that outside. -/
theorem chi_eq_lintegral_encard_inter_add_diff [Countable V] (q : Sym2 V → unitInterval)
    (o : V) (A : Set V) :
    chi q o = ∫⁻ ω, ((cluster ω o ∩ A).encard : ℝ≥0∞) ∂law q +
      ∫⁻ ω, ((cluster ω o \ A).encard : ℝ≥0∞) ∂law q := by
  rw [chi, ← lintegral_add_left (measurable_encard_cluster_inter o A)]
  refine lintegral_congr fun ω => ?_
  have h := Set.encard_union_eq (s := cluster ω o ∩ A) (t := cluster ω o \ A)
    (Set.disjoint_left.2 fun x h1 h2 => h2.2 h1.2)
  rw [Set.inter_union_sdiff] at h
  rw [h, ENat.toENNReal_add]

/-- **Uniform localization.** For every `ε > 0` there is `C > 0`, depending only on `p`,
`C_p` and `ε`, such that every profile, root, function `f` and scale `r > 0` with
`E[∑_{x ∈ K_o} f(x)^p] ≤ (C_p r)^p χ < ∞` satisfy `χ ≤ (1 + ε) E|K_o ∩ {f ≤ C r}|`. -/
theorem exists_chi_le_mul_lintegral_encard_inter [Countable V] {p : ℝ} {Cp : ℝ≥0}
    (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Sym2 V → unitInterval) (o : V) (f : V → ℝ) (r : ℝ), 0 < r →
      ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (f x ^ p)) x ∂law q ≤
        ENNReal.ofReal ((Cp * r) ^ p) * chi q o →
      chi q o < ⊤ →
      chi q o ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((cluster ω o ∩ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂law q := by
  -- choose `C` with `(C_p / C)^p ≤ ε / (1 + ε)`
  set δ : ℝ := ε / (1 + ε) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hCp : (0 : ℝ) ≤ Cp := (NNReal.coe_nonneg Cp)
  set C : ℝ := (Cp + 1) / δ ^ p⁻¹ with hC_def
  have hδp : 0 < δ ^ p⁻¹ := Real.rpow_pos_of_pos hδ0 _
  have hC : 0 < C := div_pos (by linarith) hδp
  have hratio : ((Cp : ℝ) / C) ^ p ≤ δ := by
    have h1 : (Cp : ℝ) / C ≤ δ ^ p⁻¹ := by
      rw [hC_def, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ((Cp : ℝ) / C) ^ p ≤ (δ ^ p⁻¹) ^ p :=
          Real.rpow_le_rpow (div_nonneg hCp hC.le) h1 hp.le
      _ = δ := by rw [← Real.rpow_mul hδ0.le, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  refine ⟨C, hC, fun q o f r hr hS hfin => ?_⟩
  have hout := lintegral_encard_diff_le_of_lintegral_le q o hp hr hC hS
  set I := ∫⁻ ω, ((cluster ω o ∩ {x | f x ≤ C * r}).encard : ℝ≥0∞) ∂law q
  have hsplit := chi_eq_lintegral_encard_inter_add_diff q o {x | f x ≤ C * r}
  have h1 : chi q o ≤ I + ENNReal.ofReal δ * chi q o := by
    calc chi q o = I + _ := hsplit
      _ ≤ I + ENNReal.ofReal (((Cp : ℝ) / C) ^ p) * chi q o := add_le_add le_rfl hout
      _ ≤ I + ENNReal.ofReal δ * chi q o := by gcongr
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (by rw [hsplit]; exact le_self_add)
  have hχ := ENNReal.toReal_mono (by
    exact ENNReal.add_ne_top.2 ⟨hItop, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne⟩) h1
  rw [ENNReal.toReal_add hItop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ0.le] at hχ
  rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_toReal hItop,
    ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hχ0 : 0 ≤ (chi q o).toReal := ENNReal.toReal_nonneg
  have hkey : (chi q o).toReal * (1 - δ) ≤ I.toReal := by nlinarith
  have hone : (1 + ε) * (1 - δ) = 1 := by
    rw [hδ]; field_simp; ring
  nlinarith

/-- **Markov form.** The probability that `K_o` leaves `A` is at most the expected volume
of `K_o` outside `A`. -/
theorem law_encard_diff_pos_le [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (A : Set V) :
    law q {ω | 0 < (cluster ω o \ A).encard} ≤
      ∫⁻ ω, ((cluster ω o \ A).encard : ℝ≥0∞) ∂law q := by
  have hm : Measurable fun ω : Config V => ((cluster ω o \ A).encard : ℝ≥0∞) := by
    simpa only [sdiff_eq] using measurable_encard_cluster_inter o Aᶜ
  calc law q {ω | 0 < (cluster ω o \ A).encard}
      ≤ law q {ω | 1 ≤ ((cluster ω o \ A).encard : ℝ≥0∞)} := by
        refine measure_mono ?_
        intro ω hω
        simp only [mem_ofPred_eq] at hω ⊢
        have h1 : (1 : ℕ∞) ≤ (cluster ω o \ A).encard := Order.one_le_iff_pos.2 hω
        calc (1 : ℝ≥0∞) = ((1 : ℕ∞) : ℝ≥0∞) := by simp
          _ ≤ _ := ENat.toENNReal_le.2 h1
    _ = 1 * law q {ω | 1 ≤ ((cluster ω o \ A).encard : ℝ≥0∞)} := (one_mul _).symm
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hm.aemeasurable 1

/-! ### Metric forms -/

section Metric

variable [Countable V] [PseudoMetricSpace V]

omit [Countable V] in
/-- A correlation-length bound `ξ_p ≤ a`, with `ξ_p^p = E[∑_{x ∈ K_o} d(o, x)^p] / χ` and
`χ < ∞`, gives the spatial-moment bound `E[∑_{x ∈ K_o} d(x, o)^p] ≤ a^p χ`. -/
theorem lintegral_tsum_dist_rpow_le_of_rpow_inv_le (q : Sym2 V → unitInterval) (o : V)
    {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hχ : chi q o < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal a) :
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist x o ^ p)) x ∂law q ≤
      ENNReal.ofReal (a ^ p) * chi q o := by
  rw [ENNReal.rpow_inv_le_iff hp, ENNReal.ofReal_rpow_of_nonneg ha hp.le,
    ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hχ.ne)] at hξ
  simpa only [dist_comm] using hξ

/-- **32GP, first clause, for one profile.** If `0 < χ < ∞` and the correlation length
satisfies `ξ_p ≤ C_p r`, then `E|K_o \ B_{C r}| / χ ≤ (C_p / C)^p` for every `C > 0`. -/
theorem lintegral_encard_diff_closedBall_div_chi_le (q : Sym2 V → unitInterval) (o : V)
    {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C) (hχ0 : 0 < chi q o)
    (hχ : chi q o < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    (∫⁻ ω, ((cluster ω o \ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂law q) / chi q o ≤
      ENNReal.ofReal ((Cp / C) ^ p) := by
  have hS := lintegral_tsum_dist_rpow_le_of_rpow_inv_le q o hp
    (mul_nonneg (NNReal.coe_nonneg Cp) hr.le) hχ hξ
  rw [ENNReal.div_le_iff_le_mul (Or.inl hχ0.ne') (Or.inl hχ.ne)]
  exact lintegral_encard_diff_le_of_lintegral_le q o (f := (dist · o)) hp hr hC hS

/-- **32GP, second clause.** For every `ε > 0` there is `C > 0`, depending only on `p`, `C_p`
and `ε`, such that every profile and scale `r > 0` with `0 < χ < ∞` and `ξ_p ≤ C_p r`
satisfy `χ ≤ (1 + ε) E|K_o ∩ B_{C r}|`. -/
theorem exists_chi_le_mul_lintegral_encard_inter_closedBall {p : ℝ} {Cp : ℝ≥0} (hp : 0 < p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Sym2 V → unitInterval) (o : V) (r : ℝ), 0 < r →
      chi q o < ⊤ →
      ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r) →
      chi q o ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((cluster ω o ∩ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂law q := by
  obtain ⟨C, hC, h⟩ := exists_chi_le_mul_lintegral_encard_inter (V := V) (Cp := Cp) hp hε
  refine ⟨C, hC, fun q o r hr hχ hξ => ?_⟩
  exact h q o (dist · o) r hr
    (lintegral_tsum_dist_rpow_le_of_rpow_inv_le q o hp
      (mul_nonneg (NNReal.coe_nonneg Cp) hr.le) hχ hξ) hχ

/-- **32GP, third clause, for one profile.** If `χ < ∞` and `ξ_p ≤ C_p r`, then
`P(|K_o \ B_{C r}| > 0) ≤ χ (C_p / C)^p` for every `C > 0`. -/
theorem law_encard_diff_closedBall_pos_le (q : Sym2 V → unitInterval) (o : V)
    {p r C : ℝ} {Cp : ℝ≥0} (hp : 0 < p) (hr : 0 < r) (hC : 0 < C) (hχ : chi q o < ⊤)
    (hξ : ((∫⁻ ω, ∑' x, (cluster ω o).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x
        ∂law q) / chi q o) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    law q {ω | 0 < (cluster ω o \ Metric.closedBall o (C * r)).encard} ≤
      chi q o * ENNReal.ofReal ((Cp / C) ^ p) := by
  have hS := lintegral_tsum_dist_rpow_le_of_rpow_inv_le q o hp
    (mul_nonneg (NNReal.coe_nonneg Cp) hr.le) hχ hξ
  rw [mul_comm (chi q o)]
  exact (law_encard_diff_pos_le q o _).trans
    (lintegral_encard_diff_le_of_lintegral_le q o (f := (dist · o)) hp hr hC hS)

end Metric

end PercLib.Percolation.Bond
