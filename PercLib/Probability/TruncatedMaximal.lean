/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

New proofs for issue 459 (Q-125), written on 2026-11-16 by PROVER-G, against pinned mathlib.
No upstream proof is copied.
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Doob's `L²` maximal inequality

Part 1 of Q-125 (HXNR). For a real martingale `X` with every `X k` in `L²`,

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
          have e2 : (fun t => if t ≤ M ω then g ω else 0) = (Set.Iic (M ω)).indicator fun _ => g ω := by
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

/-! ### D-5 witnesses -/

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

end PercLib.Probability
