/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied.
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Doob's `L²` maximal inequality

For a real martingale `X` with every `X k` in `L²`,

  `E[(max_{k ≤ n} |X_k|)²] ≤ 4 E[X_n²]`   (`lintegral_sup_abs_sq_le`).

Mathlib at the pin has the weak-type inequality `MeasureTheory.maximal_ineq` and notes that
the `Lᵖ` form is still to come. The proof applies `maximal_ineq` to the nonnegative
submartingale `|X|`, integrates it against `2t dt` (layer cake), exchanges the integrals, and
closes with `2ab ≤ 2a² + b²/2`.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}

/-- The absolute value of a real martingale is a submartingale. -/
theorem submartingale_abs_of_martingale (hX : Martingale X ℱ μ) :
    Submartingale (fun n ω => |X n ω|) ℱ μ := by
  have h := hX.submartingale.sup hX.neg.submartingale
  have e : (fun n ω => |X n ω|) = X ⊔ -X := by
    funext n ω
    rfl
  rw [e]
  exact h

/-- **Doob's `L²` maximal inequality.** For a real martingale `X` with each `X k ∈ L²` and a
finite measure, `∫⁻ (max_{k ≤ n} |X_k|)² ≤ 4 ∫⁻ X_n²`. -/
theorem lintegral_sup_abs_sq_le [IsFiniteMeasure μ] (hX : Martingale X ℱ μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
        fun k => |X k ω|) ^ 2) ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ := by
  set M : Ω → ℝ := fun ω => (range (n + 1)).sup' nonempty_range_add_one fun k => |X k ω|
    with hMdef
  have hY := submartingale_abs_of_martingale hX
  have hYnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω => |X n ω| := fun _ _ => abs_nonneg _
  have hXm : ∀ k, Measurable (X k) := fun k =>
    (hX.stronglyMeasurable k).measurable.le (ℱ.le k)
  have hMm : Measurable M :=
    Finset.measurable_range_sup'' fun k _ => continuous_abs.measurable.comp (hXm k)
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω =>
    (abs_nonneg _).trans (le_sup' (fun k => |X k ω|) (mem_range.2 n.succ_pos))
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal |X n ω| with hg
  have hgm : Measurable g := (continuous_abs.measurable.comp (hXm n)).ennreal_ofReal
  -- the weak-type bound
  have hweak : ∀ t : ℝ, 0 < t → μ {ω | t ≤ M ω} * ENNReal.ofReal t ≤
      ∫⁻ ω, (if t ≤ M ω then g ω else 0) ∂μ := by
    intro t ht
    have h := maximal_ineq hY hYnn (ε := t.toNNReal) n
    have hc : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [Real.coe_toNNReal t ht.le] at h
    have hset : MeasurableSet {ω | t ≤ M ω} := measurableSet_le measurable_const hMm
    rw [hc, ofReal_integral_eq_lintegral_ofReal ((hY.integrable n).integrableOn)
      (ae_of_all _ fun ω => abs_nonneg _)] at h
    rw [mul_comm]
    refine h.trans (le_of_eq ?_)
    rw [← lintegral_indicator hset]
    refine lintegral_congr fun ω => ?_
    simp only [indicator_apply, mem_ofPred_eq, hg]
  -- layer cake
  have hlc := lintegral_rpow_eq_lintegral_meas_le_mul μ (ae_of_all _ hM0) hMm.aemeasurable
    (p := 2) two_pos
  have hA : ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ ≤ 2 * ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ := by
    have e1 : ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ = ∫⁻ ω, ENNReal.ofReal (M ω ^ (2 : ℝ)) ∂μ := by
      simp_rw [Real.rpow_two]
    rw [e1, hlc, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_ofNat]
    gcongr
    calc ∫⁻ t in Set.Ioi 0, μ {a | t ≤ M a} * ENNReal.ofReal (t ^ (1 : ℝ))
        ≤ ∫⁻ t in Set.Ioi 0, ∫⁻ ω, (if t ≤ M ω then g ω else 0) ∂μ := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          rw [Real.rpow_one]
          exact hweak t ht
      _ = ∫⁻ ω, (∫⁻ t in Set.Ioi (0 : ℝ), (if t ≤ M ω then g ω else 0)) ∂μ := by
          refine lintegral_lintegral_swap ?_
          refine Measurable.aemeasurable ?_
          exact Measurable.ite (measurableSet_le measurable_fst (hMm.comp measurable_snd))
            (hgm.comp measurable_snd) measurable_const
      _ = ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ := by
          refine lintegral_congr fun ω => ?_
          have e2 : (fun t => if t ≤ M ω then g ω else 0) = (Set.Iic (M ω)).indicator fun _ =>
              g ω := by
            funext t
            simp only [indicator_apply, Set.mem_Iic]
          rw [e2, lintegral_indicator_const measurableSet_Iic,
            Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi, Real.volume_Ioc, sub_zero]
  -- finiteness of the left side
  have hfin : ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ ≠ ⊤ := by
    have hle : ∀ ω, M ω ^ 2 ≤ ∑ k ∈ range (n + 1), X k ω ^ 2 := fun ω => by
      obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one fun k => |X k ω|
      have : M ω = |X k ω| := hkeq
      rw [this, sq_abs]
      exact single_le_sum (f := fun k => X k ω ^ 2) (fun _ _ => sq_nonneg _) hk
    refine (lt_of_le_of_lt (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hle ω)) ?_).ne
    have hint : Integrable (fun ω => ∑ k ∈ range (n + 1), X k ω ^ 2) μ :=
      integrable_finsetSum _ fun k _ => (hL2 k).integrable_sq
    exact hint.lintegral_lt_top
  -- the elementary inequality `2ab ≤ 2a² + b²/2`
  have hpt : ∀ ω, 2 * (g ω * ENNReal.ofReal (M ω))
      ≤ 2 * ENNReal.ofReal (X n ω ^ 2) + ENNReal.ofReal (M ω ^ 2) / 2 := fun ω => by
    simp only [hg]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (2 * |X n ω| - M ω), sq_abs (X n ω)]
  have hB : 2 * ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ
      ≤ 2 * ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ + (∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ) / 2 := by
    have hm1 : Measurable fun ω => ENNReal.ofReal (X n ω ^ 2) :=
      ((hXm n).pow_const 2).ennreal_ofReal
    have hm2 : Measurable fun ω => ENNReal.ofReal (M ω ^ 2) := (hMm.pow_const 2).ennreal_ofReal
    calc 2 * ∫⁻ ω, g ω * ENNReal.ofReal (M ω) ∂μ
        = ∫⁻ ω, 2 * (g ω * ENNReal.ofReal (M ω)) ∂μ :=
          (lintegral_const_mul 2 (hgm.mul hMm.ennreal_ofReal)).symm
      _ ≤ ∫⁻ ω, (2 * ENNReal.ofReal (X n ω ^ 2) + ENNReal.ofReal (M ω ^ 2) / 2) ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ ω, 2 * ENNReal.ofReal (X n ω ^ 2) ∂μ + ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) * 2⁻¹ ∂μ := by
          simp_rw [div_eq_mul_inv]
          exact lintegral_add_left (hm1.const_mul 2) _
      _ = _ := by
          rw [lintegral_const_mul _ hm1, lintegral_mul_const _ hm2, div_eq_mul_inv]
  set A := ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ
  set B := ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ
  have h1 : A / 2 + A / 2 ≤ 2 * B + A / 2 := by
    rw [ENNReal.add_halves]
    exact hA.trans hB
  have hA2 : A / 2 ≠ ⊤ := ENNReal.div_ne_top hfin two_ne_zero
  have h2 : A / 2 ≤ 2 * B := (ENNReal.add_le_add_iff_right hA2).1 h1
  calc A = 2 * (A / 2) := (ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
    _ ≤ 2 * (2 * B) := by gcongr
    _ = 4 * B := by rw [← mul_assoc]; norm_num

/-! ### The predictable quadratic variation -/

/-- **The compensator of `X²`.** For a real martingale `X` with each `X k ∈ L²` and a finite
measure, `X_n² − Q_n` is a martingale, where
`Q_n = ∑_{i<n} μ[(X_{i+1} − X_i)² | ℱ_i]` is the predictable quadratic variation. -/
theorem martingale_sq_sub_predictableVariation [IsFiniteMeasure μ] (hX : Martingale X ℱ μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) :
    Martingale (fun n ω => X n ω ^ 2 - ∑ i ∈ range n,
      μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) ℱ μ := by
  set D : ℕ → Ω → ℝ := fun i ω => (X (i + 1) ω - X i ω) ^ 2 with hD
  set Δ : ℕ → Ω → ℝ := fun i ω => X (i + 1) ω - X i ω with hΔ
  have hXi : ∀ k, Integrable (X k) μ := fun k => hX.integrable k
  have hDi : ∀ i, Integrable (D i) μ := fun i => ((hL2 (i + 1)).sub (hL2 i)).integrable_sq
  have hΔi : ∀ i, Integrable (Δ i) μ := fun i => (hXi (i + 1)).sub (hXi i)
  have hsq : ∀ k, Integrable (fun ω => X k ω ^ 2) μ := fun k => (hL2 k).integrable_sq
  have hprod : ∀ i, Integrable (X i * Δ i) μ := fun i => by
    have hm : AEStronglyMeasurable (X i * Δ i) μ :=
      (((hX.stronglyMeasurable i).mono (ℱ.le i)).aestronglyMeasurable).mul
        (hΔi i).aestronglyMeasurable
    refine Integrable.mono' (((hsq i).add (hDi i)).div_const 2) hm
      (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, abs_mul, hD, hΔ]
    nlinarith [sq_nonneg (|X i ω| - |X (i + 1) ω - X i ω|), sq_abs (X i ω),
      sq_abs (X (i + 1) ω - X i ω)]
  refine martingale_of_condExp_sub_eq_zero_nat ?_ ?_ ?_
  · intro n
    refine ((hX.stronglyMeasurable n).pow 2).sub ?_
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
    exact stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range.1 hi).le)
  · intro n
    exact (hsq n).sub (integrable_finsetSum _ fun i _ => integrable_condExp)
  · intro i
    have hdiff : (fun ω => X (i + 1) ω ^ 2 - ∑ j ∈ range (i + 1), μ[D j | ℱ j] ω) -
        (fun ω => X i ω ^ 2 - ∑ j ∈ range i, μ[D j | ℱ j] ω)
        = D i + (2 : ℝ) • (X i * Δ i) - μ[D i | ℱ i] := by
      funext ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
        Finset.sum_range_succ, hD, hΔ]
      ring
    rw [hdiff]
    have hcondΔ : μ[Δ i | ℱ i] =ᵐ[μ] 0 := by
      have h1 := condExp_sub (hXi (i + 1)) (hXi i) (ℱ i)
      have h2 := hX.condExp_ae_eq (Nat.le_succ i)
      rw [condExp_of_stronglyMeasurable (ℱ.le i) (hX.stronglyMeasurable i) (hXi i)] at h1
      filter_upwards [h1, h2] with ω h1 h2
      simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
      rw [show Δ i = X (i + 1) - X i from rfl, h1, h2, sub_self]
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (hX.stronglyMeasurable i)
      (hprod i) (hΔi i)
    have hsm := condExp_smul (μ := μ) (2 : ℝ) (X i * Δ i) (ℱ i)
    have hadd := condExp_add (hDi i) ((hprod i).smul (2 : ℝ)) (ℱ i)
    have hsub := condExp_sub ((hDi i).add ((hprod i).smul (2 : ℝ))) (integrable_condExp
      (m := ℱ i) (f := D i)) (ℱ i)
    have hcc : μ[μ[D i | ℱ i] | ℱ i] = μ[D i | ℱ i] :=
      condExp_of_stronglyMeasurable (ℱ.le i) stronglyMeasurable_condExp integrable_condExp
    rw [hcc] at hsub
    filter_upwards [hsub, hadd, hsm, hpull, hcondΔ] with ω e1 e2 e3 e4 e5
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.zero_apply,
      smul_eq_mul] at e1 e2 e3 e4 e5 ⊢
    rw [e1, e2, e3, e4, e5]
    ring

/-! ### Non-vacuity witnesses -/

/-- The hypotheses of `lintegral_sup_abs_sq_le` hold for the zero martingale on any finite
measure space. -/
example [IsFiniteMeasure μ]
    (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
        fun k => |(0 : ℕ → Ω → ℝ) k ω|) ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((0 : ℕ → Ω → ℝ) n ω ^ 2) ∂μ :=
  lintegral_sup_abs_sq_le (martingale_zero ℝ ℱ μ) (fun _ => MemLp.zero) n

/-- The hypotheses of `lintegral_sup_abs_sq_le` hold for a constant nonzero martingale. -/
example [IsFiniteMeasure μ]
    (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
        fun k => |(fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) k ω|) ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) n ω ^ 2) ∂μ :=
  lintegral_sup_abs_sq_le (martingale_const ℱ μ (1 : ℝ)) (fun _ => memLp_const 1) n

/-- The hypotheses of `martingale_sq_sub_predictableVariation` hold for the constant martingale
`X ≡ 1` on any finite measure space. -/
example [IsFiniteMeasure μ] :
    Martingale (fun n ω => (fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) n ω ^ 2 - ∑ i ∈ range n,
      μ[fun ω => ((fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) (i + 1) ω -
        (fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) i ω) ^ 2 | ℱ i] ω) ℱ μ :=
  martingale_sq_sub_predictableVariation (martingale_const ℱ μ (1 : ℝ))
    (fun _ => memLp_const 1)


/-! ### Stopping before a variance overshoot -/

/-- A martingale transform by indicators of predictable sets: if `G i` is `ℱ i`-measurable,
then `∑_{i<n} 1_{G i} (X_{i+1} − X_i)` is a martingale. -/
theorem martingale_sum_indicator_mul_sub [IsFiniteMeasure μ] (hX : Martingale X ℱ μ)
    {G : ℕ → Set Ω} (hG : ∀ i, MeasurableSet[ℱ i] (G i)) :
    Martingale (fun n => ∑ i ∈ range n, (G i).indicator 1 * (X (i + 1) - X i)) ℱ μ := by
  have hξ : StronglyAdapted ℱ fun i => (G i).indicator (1 : Ω → ℝ) := fun i =>
    stronglyMeasurable_const.indicator (hG i)
  have hb : ∀ n ω, (G n).indicator (1 : Ω → ℝ) ω ≤ 1 := fun n ω => by
    by_cases h : ω ∈ G n <;> simp [h]
  have hp : ∀ n ω, 0 ≤ (G n).indicator (1 : Ω → ℝ) ω := fun n ω => by
    by_cases h : ω ∈ G n <;> simp [h]
  have h1 := hX.submartingale.sum_mul_sub hξ hb hp
  have h2 := (hX.neg.submartingale.sum_mul_sub hξ hb hp).neg
  refine martingale_iff.2 ⟨?_, h1⟩
  convert h2 using 1
  funext n ω
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The predictable quadratic variation of the indicator transform
`∑_{i<n} 1_{G i} (X_{i+1} − X_i)` has increments `1_{G i} μ[(X_{i+1} − X_i)² | ℱ i]`. -/
theorem condExp_sq_sub_sum_indicator_mul_sub_ae_eq (hL2 : ∀ k, MemLp (X k) 2 μ)
    {G : ℕ → Set Ω} (hG : ∀ i, MeasurableSet[ℱ i] (G i)) (i : ℕ) :
    μ[fun ω => ((∑ j ∈ range (i + 1), (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω -
        (∑ j ∈ range i, (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω) ^ 2 | ℱ i] =ᵐ[μ]
      (G i).indicator (μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i]) := by
  have e : (fun ω => ((∑ j ∈ range (i + 1), (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω -
        (∑ j ∈ range i, (G j).indicator 1 * (X (j + 1) - X j) : Ω → ℝ) ω) ^ 2) =
      (G i).indicator fun ω => (X (i + 1) ω - X i ω) ^ 2 := by
    funext ω
    rw [Finset.sum_range_succ, Pi.add_apply, add_sub_cancel_left]
    by_cases h : ω ∈ G i <;> simp [h]
  rw [e]
  exact condExp_indicator ((hL2 (i + 1)).sub (hL2 i)).integrable_sq (hG i)

/-- **Doob's maximal bound with a truncated predictable variance.** Let `X` be a real
martingale with `X 0 = 0` and every `X n` in `L²`, let
`Q n = ∑_{i<n} μ[(X_{i+1} − X_i)² | ℱ i]` be its predictable quadratic variation and `T` a
stopping time with values in `ℕ∞ = WithTop ℕ`. With `Q_T = sup_n Q_{n ∧ T}` (the
increasing limit) and `M_T = sup_{n ≤ T} |X_n|`, for every finite `λ ≥ 0`,
`∫_{Q_T ≤ λ} M_T² ≤ 4 ∫ min Q_T λ`. -/
theorem setLIntegral_iSup_abs_sq_le_four_mul_lintegral_min [IsFiniteMeasure μ]
    (hX : Martingale X ℱ μ) (hX0 : X 0 = 0) (hL2 : ∀ n, MemLp (X n) 2 μ)
    {T : Ω → WithTop ℕ} (hT : IsStoppingTime ℱ T) (l : ℝ≥0) :
    ∫⁻ ω in {ω | (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) ≤ l},
        (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, min (⨆ n : ℕ, ENNReal.ofReal (stoppedProcess (fun k ω => ∑ i ∈ range k,
          μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] ω) T n ω)) (l : ℝ≥0∞) ∂μ := by
  classical
  set q : ℕ → Ω → ℝ := fun i => μ[fun ω => (X (i + 1) ω - X i ω) ^ 2 | ℱ i] with hq
  set Q : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ range k, q i ω with hQ
  set QT : Ω → ℝ≥0∞ := fun ω => ⨆ n : ℕ, ENNReal.ofReal (stoppedProcess Q T n ω) with hQT
  change ∫⁻ ω in {ω | QT ω ≤ l}, _ ∂μ ≤ 4 * ∫⁻ ω, min (QT ω) (l : ℝ≥0∞) ∂μ
  -- basic measurability
  have hqm : ∀ i j, i ≤ j → Measurable[ℱ j] (q i) := fun i j hij =>
    (stronglyMeasurable_condExp.mono (ℱ.mono hij)).measurable
  have hQm : ∀ k, Measurable (Q k) := fun k =>
    Finset.measurable_sum _ fun i _ => (hqm i i le_rfl).mono (ℱ.le i) le_rfl
  have hQTm : Measurable QT := by
    refine Measurable.iSup fun n => Measurable.ennreal_ofReal ?_
    rw [stoppedProcess_eq]
    refine ((hQm n).indicator (ℱ.le n _ (hT.measurableSet_ge n))).add ?_
    rw [Finset.sum_fn]
    exact Finset.measurable_sum _ fun i _ => (hQm i).indicator (ℱ.le i _ (hT.measurableSet_eq i))
  have hE : MeasurableSet {ω | QT ω ≤ l} := measurableSet_le hQTm measurable_const
  -- `ofReal (Q k) ≤ Q_T` whenever `k ≤ T`
  have hQk : ∀ ω (k : ℕ), (k : WithTop ℕ) ≤ T ω → ENNReal.ofReal (Q k ω) ≤ QT ω := by
    intro ω k hk
    refine le_trans (le_of_eq ?_) (le_iSup (fun n : ℕ => ENNReal.ofReal (stoppedProcess Q T n ω)) k)
    rw [stoppedProcess_eq_of_le (u := Q) (i := k) hk]
  have hl : (l : ℝ≥0∞) = ENNReal.ofReal l := (ENNReal.ofReal_coe_nnreal).symm
  -- the predictable sets `{i < T} ∩ {Q_{j+1} ≤ λ for j ≤ i}`
  set G : ℕ → Set Ω := fun i => {ω | (i : WithTop ℕ) < T ω} ∩
    ⋂ j ∈ Finset.range (i + 1), {ω | Q (j + 1) ω ≤ l} with hGdef
  have hG : ∀ i, MeasurableSet[ℱ i] (G i) := by
    intro i
    refine MeasurableSet.inter ?_ (Finset.measurableSet_biInter _ fun j hj => ?_)
    · have : {ω | (i : WithTop ℕ) < T ω} = {ω | T ω ≤ i}ᶜ := by ext; simp
      rw [this]
      exact (hT i).compl
    · refine measurableSet_le (Finset.measurable_sum _ fun l' hl' => hqm l' i ?_) measurable_const
      have := Finset.mem_range.1 hj
      have := Finset.mem_range.1 hl'
      omega
  have hmemG : ∀ i ω, ω ∈ G i ↔ (i : WithTop ℕ) < T ω ∧ ∀ j < i + 1, Q (j + 1) ω ≤ l := by
    intro i ω
    simp [hGdef]
  -- the stopped martingale
  set Y : ℕ → Ω → ℝ := fun n => ∑ i ∈ range n, (G i).indicator 1 * (X (i + 1) - X i) with hYdef
  have hY : Martingale Y ℱ μ := martingale_sum_indicator_mul_sub hX hG
  have hYL2 : ∀ n, MemLp (Y n) 2 μ := fun n => by
    refine memLp_finsetSum' _ fun i _ => ?_
    have : (G i).indicator 1 * (X (i + 1) - X i) = (G i).indicator (X (i + 1) - X i) := by
      funext ω
      by_cases h : ω ∈ G i <;> simp [h]
    rw [this]
    exact ((hL2 (i + 1)).sub (hL2 i)).indicator (ℱ.le i _ (hG i)).nullMeasurableSet
  -- `E Y_n² = E ∑_{i<n} 1_{G i} q i`
  set R : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ range n, (G i).indicator (q i) ω with hRdef
  have hRint : ∀ n, Integrable (R n) μ := fun n =>
    integrable_finsetSum _ fun i _ => integrable_condExp.indicator (ℱ.le i _ (hG i))
  have hYsq : ∀ n, ∫ ω, Y n ω ^ 2 ∂μ = ∫ ω, R n ω ∂μ := by
    intro n
    have hmart := martingale_sq_sub_predictableVariation hY hYL2
    have h0 := hmart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
    simp only [setIntegral_univ] at h0
    have hY0 : Y 0 = 0 := by simp [hYdef]
    simp only [hY0, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.range_zero, Finset.sum_empty, sub_zero, integral_zero] at h0
    have hV : ∀ᵐ ω ∂μ, ∑ i ∈ range n, μ[fun ω => (Y (i + 1) ω - Y i ω) ^ 2 | ℱ i] ω = R n ω := by
      have := ae_all_iff.2 fun i => condExp_sq_sub_sum_indicator_mul_sub_ae_eq hL2 hG i
      filter_upwards [this] with ω hω
      exact Finset.sum_congr rfl fun i _ => hω i
    have hVint : Integrable (fun ω => ∑ i ∈ range n,
        μ[fun ω => (Y (i + 1) ω - Y i ω) ^ 2 | ℱ i] ω) μ :=
      integrable_finsetSum _ fun i _ => integrable_condExp
    rw [integral_sub (hYL2 n).integrable_sq hVint, integral_congr_ae hV] at h0
    linarith
  have hRnn : ∀ n, 0 ≤ᵐ[μ] R n := by
    intro n
    have := ae_all_iff.2 fun i => condExp_nonneg (m := ℱ i) (μ := μ)
      (f := fun ω => (X (i + 1) ω - X i ω) ^ 2) (Eventually.of_forall fun ω => sq_nonneg _)
    filter_upwards [this] with ω hω
    exact Finset.sum_nonneg fun i _ => Set.indicator_apply_nonneg fun _ => hω i
  -- the combinatorial bound `ofReal (R n) ≤ min Q_T λ`
  have hRle : ∀ n ω, ENNReal.ofReal (R n ω) ≤ min (QT ω) l := by
    intro n ω
    have hanti : ∀ i, ω ∈ G (i + 1) → ω ∈ G i := by
      intro i h
      rw [hmemG] at h ⊢
      refine ⟨lt_trans (WithTop.coe_lt_coe.2 i.lt_succ_self) h.1, fun j hj => h.2 j (by omega)⟩
    have hkn := Nat.findGreatest_le (P := fun k => ∀ i < k, ω ∈ G i) n
    have hspec : ∀ i < Nat.findGreatest (fun k => ∀ i < k, ω ∈ G i) n, ω ∈ G i :=
      Nat.findGreatest_spec (P := fun k => ∀ i < k, ω ∈ G i) (Nat.zero_le n)
        (fun i hi => absurd hi (Nat.not_lt_zero _))
    have hlarge : ∀ m, m ≤ n → (∀ i < m, ω ∈ G i) →
        m ≤ Nat.findGreatest (fun k => ∀ i < k, ω ∈ G i) n := fun m hm hP =>
      Nat.le_findGreatest (P := fun k => ∀ i < k, ω ∈ G i) hm hP
    generalize Nat.findGreatest (fun k => ∀ i < k, ω ∈ G i) n = k at hkn hspec hlarge
    have hiff : ∀ i < n, ω ∈ G i ↔ i < k := by
      intro i hi
      constructor
      · intro h
        by_contra hki
        have aux : ∀ d j, j + d = i → ω ∈ G j := by
          intro d
          induction d with
          | zero => intro j hj; rwa [show j = i by omega]
          | succ d ih => intro j hj; exact hanti j (ih (j + 1) (by omega))
        have hall : ∀ j < i + 1, ω ∈ G j := fun j hj => aux (i - j) j (by omega)
        have := hlarge (i + 1) (by omega) hall
        omega
      · exact hspec i
    have hRk : R n ω = Q k ω := by
      simp only [hRdef, hQ]
      rw [← Finset.sum_range_add_sum_Ico _ hkn]
      have h1 : ∑ i ∈ range k, (G i).indicator (q i) ω = ∑ i ∈ range k, q i ω :=
        Finset.sum_congr rfl fun i hi => Set.indicator_of_mem ((hiff i (by
          have := Finset.mem_range.1 hi; omega)).2 (Finset.mem_range.1 hi)) _
      have h2 : ∑ i ∈ Finset.Ico k n, (G i).indicator (q i) ω = 0 :=
        Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (fun h => by
          have := Finset.mem_Ico.1 hi
          have := (hiff i this.2).1 h
          omega) _
      rw [h1, h2, add_zero]
    rw [hRk]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · simp [h0, hQ]
    have hG' : ω ∈ G (k - 1) := (hiff (k - 1) (by omega)).2 (by omega)
    rw [hmemG] at hG'
    refine le_min (hQk ω k ?_) ?_
    · have h1 := hG'.1
      rcases hTω : T ω with _ | m
      · exact le_top
      · rw [hTω, Nat.cast_withTop] at h1
        have := WithTop.coe_lt_coe.1 h1
        rw [Nat.cast_withTop]
        exact WithTop.coe_le_coe.2 (by omega)
    · rw [hl]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hG'.2 (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
  -- `E Y_n² ≤ E min Q_T λ`
  have hYbd : ∀ n, ∫⁻ ω, ENNReal.ofReal (Y n ω ^ 2) ∂μ ≤ ∫⁻ ω, min (QT ω) l ∂μ := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hYL2 n).integrable_sq
      (Eventually.of_forall fun ω => sq_nonneg _), hYsq n,
      ofReal_integral_eq_lintegral_ofReal (hRint n) (hRnn n)]
    exact lintegral_mono fun ω => hRle n ω
  -- on `{Q_T ≤ λ}`, `Y_j = X_j` for `j ≤ T`
  have hYX : ∀ ω, QT ω ≤ l → ∀ j : ℕ, (j : WithTop ℕ) ≤ T ω → Y j ω = X j ω := by
    intro ω hω j hj
    have hsum : Y j ω = ∑ i ∈ range j, (X (i + 1) ω - X i ω) := by
      simp only [hYdef, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.1 hi
      have hmem : ω ∈ G i := by
        rw [hmemG]
        refine ⟨lt_of_lt_of_le (WithTop.coe_lt_coe.2 hi) hj, fun j' hj' => ?_⟩
        have hj1 : ((j' + 1 : ℕ) : WithTop ℕ) ≤ T ω :=
          le_trans (WithTop.coe_le_coe.2 (show j' + 1 ≤ j by omega)) hj
        have h1 := (hQk ω (j' + 1) hj1).trans hω
        rw [hl] at h1
        exact (ENNReal.ofReal_le_ofReal_iff l.coe_nonneg).1 h1
      simp [hmem]
    rw [hsum, Finset.sum_range_sub (fun i => X i ω), hX0, Pi.zero_apply, sub_zero]
  -- truncated maxima
  set MT : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ j : ℕ,
    {ω | (j : WithTop ℕ) ≤ T ω ∧ j ≤ n}.indicator (fun ω => ENNReal.ofReal |X j ω|) ω with hMT
  have hMTm : ∀ n, Measurable (MT n) := by
    intro n
    refine Measurable.iSup fun j => Measurable.indicator ?_ ?_
    · exact (continuous_abs.measurable.comp
        ((hX.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl)).ennreal_ofReal
    · rw [Set.ofPred_and]
      refine MeasurableSet.inter ?_ (MeasurableSet.const _)
      exact ℱ.le j _ (hT.measurableSet_ge j)
  have hMTmono : Monotone MT := by
    intro n n' hnn' ω
    refine iSup_mono fun j => Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le) ω
    intro ω' h
    exact ⟨h.1, h.2.trans hnn'⟩
  have hsup : ∀ ω, (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ≤
      ⨆ n, MT n ω ^ 2 := by
    intro ω
    have h1 : (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ≤ ⨆ n, MT n ω := by
      refine iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le j ?_)
      rw [Set.indicator_of_mem (show ω ∈ {ω | (j : WithTop ℕ) ≤ T ω ∧ j ≤ j} from ⟨hj, le_rfl⟩)]
    refine (pow_le_pow_left₀ zero_le h1 2).trans ?_
    rw [sq, ENNReal.iSup_mul]
    refine iSup_le fun a => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun b => le_iSup_of_le (max a b) ?_
    rw [sq]
    exact mul_le_mul' (hMTmono (le_max_left a b) ω) (hMTmono (le_max_right a b) ω)
  -- finite-horizon bound on the event
  have hfin : ∀ n, ∫⁻ ω in {ω | QT ω ≤ l}, MT n ω ^ 2 ∂μ ≤ 4 * ∫⁻ ω, min (QT ω) l ∂μ := by
    intro n
    calc ∫⁻ ω in {ω | QT ω ≤ l}, MT n ω ^ 2 ∂μ
        ≤ ∫⁻ ω in {ω | QT ω ≤ l}, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
            fun k => |Y k ω|) ^ 2) ∂μ := by
          refine setLIntegral_mono' hE fun ω hω => ?_
          have hs0 : 0 ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => |Y k ω| :=
            (abs_nonneg _).trans (le_sup' (fun k => |Y k ω|) (mem_range.2 n.succ_pos))
          rw [ENNReal.ofReal_pow hs0]
          refine pow_le_pow_left₀ zero_le (iSup_le fun j => ?_) 2
          by_cases hj : ω ∈ {ω | (j : WithTop ℕ) ≤ T ω ∧ j ≤ n}
          · rw [Set.indicator_of_mem hj, ← hYX ω hω j hj.1]
            exact ENNReal.ofReal_le_ofReal
              (le_sup' (fun k => |Y k ω|) (mem_range.2 (Nat.lt_succ_of_le hj.2)))
          · rw [Set.indicator_of_notMem hj]
            exact zero_le
      _ ≤ ∫⁻ ω, ENNReal.ofReal (((range (n + 1)).sup' nonempty_range_add_one
            fun k => |Y k ω|) ^ 2) ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (Y n ω ^ 2) ∂μ := lintegral_sup_abs_sq_le hY hYL2 n
      _ ≤ 4 * ∫⁻ ω, min (QT ω) l ∂μ := mul_le_mul_of_nonneg_left (hYbd n) zero_le
  calc ∫⁻ ω in {ω | QT ω ≤ l},
        (⨆ (n : ℕ) (_ : (n : WithTop ℕ) ≤ T ω), ENNReal.ofReal |X n ω|) ^ 2 ∂μ
      ≤ ∫⁻ ω in {ω | QT ω ≤ l}, ⨆ n, MT n ω ^ 2 ∂μ := lintegral_mono hsup
    _ = ⨆ n, ∫⁻ ω in {ω | QT ω ≤ l}, MT n ω ^ 2 ∂μ :=
        lintegral_iSup (fun n => (hMTm n).pow_const 2)
          (fun n n' h ω => pow_le_pow_left₀ zero_le (hMTmono h ω) 2)
    _ ≤ 4 * ∫⁻ ω, min (QT ω) l ∂μ := iSup_le hfin

end PercLib.Probability
