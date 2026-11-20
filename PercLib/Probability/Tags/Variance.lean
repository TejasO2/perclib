/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrappers for odds-ratio monotonicity, covariance with a coordinate, and the
intensity-parametrised Russo formula on finite profiles. Every statement is assembled from
lemmas proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.VarianceTensorization
public import PercLib.Probability.CovarianceRusso

@[expose] public section
noncomputable section
open Finset
open scoped Classical

namespace PercLib.Probability.FiniteProfile
variable {E : Type*} [Fintype E]

/-- Odds-ratio monotonicity for a nontrivial increasing event under homogeneous product
laws: the odds inequality between parameters `a < b`, its equivalent monotone form, and the
solved lower bound for `P_b(A)` in terms of `P_a(A)`. -/
@[tag "6ITM"]
theorem odds_ratio_monotonicity {A : Set (Set E)} (hA : IsUpperSet A) (hne : A.Nonempty)
    (hnu : A ≠ Set.univ) :
    (∀ a b : unitInterval, 0 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < 1 →
      (prodBernoulli (fun _ : E => a)).real A / (1 - (prodBernoulli (fun _ : E => a)).real A) *
          (b * (1 - a) / (a * (1 - b))) ≤
        (prodBernoulli (fun _ : E => b)).real A /
          (1 - (prodBernoulli (fun _ : E => b)).real A)) ∧
    MonotoneOn (fun u => expectation (fun _ : E => u) (eventValue A) /
        (1 - expectation (fun _ : E => u) (eventValue A)) * ((1 - u) / u)) (Set.Ioo 0 1) ∧
    (∀ a b : unitInterval, 0 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < 1 →
      (prodBernoulli (fun _ : E => a)).real A * b * (1 - a) /
          ((prodBernoulli (fun _ : E => a)).real A * b * (1 - a) +
            (1 - (prodBernoulli (fun _ : E => a)).real A) * a * (1 - b)) ≤
        (prodBernoulli (fun _ : E => b)).real A) := by
  refine ⟨fun a b ha hab hb => prodBernoulli_odds_ratio_le hA hne hnu ha hab hb,
    odds_ratio_monotoneOn hA hne hnu, fun a b ha hab hb => ?_⟩
  have h := prodBernoulli_odds_ratio_le hA hne hnu ha hab hb
  have hreal : ∀ r : unitInterval, (prodBernoulli (fun _ : E => r)).real A =
      expectation (fun _ : E => (r : ℝ)) (eventValue A) := by
    intro r
    rw [← MeasureTheory.integral_indicator_one (Set.toFinite A).measurableSet,
      integral_prodBernoulli_eq_expectation]
    rfl
  have hmem : ∀ r : unitInterval, 0 < (r : ℝ) → (r : ℝ) < 1 →
      0 < (prodBernoulli (fun _ : E => r)).real A ∧
        (prodBernoulli (fun _ : E => r)).real A < 1 := by
    intro r h0 h1
    rw [hreal]
    exact ⟨expectation_eventValue_pos (fun _ => ⟨h0, h1⟩) hA hne,
      expectation_eventValue_lt_one (fun _ => ⟨h0, h1⟩) hA hnu⟩
  obtain ⟨hFa0, hFa1⟩ := hmem a ha (hab.trans hb)
  obtain ⟨hFb0, hFb1⟩ := hmem b (ha.trans hab) hb
  set Fa := (prodBernoulli (fun _ : E => a)).real A
  set Fb := (prodBernoulli (fun _ : E => b)).real A
  have ha1 : (0 : ℝ) < 1 - a := by linarith
  have hb1 : (0 : ℝ) < 1 - b := by linarith
  have hb0 : (0 : ℝ) < b := ha.trans hab
  have hX : 0 < Fa * b * (1 - a) := by positivity
  have hY : 0 < (1 - Fa) * a * (1 - b) := by
    have : 0 < 1 - Fa := by linarith
    positivity
  have hkey : Fa / (1 - Fa) * (b * (1 - a) / (a * (1 - b))) =
      (Fa * b * (1 - a)) / ((1 - Fa) * a * (1 - b)) := by
    have : (1 - Fa) ≠ 0 := by linarith
    field_simp
  rw [hkey, div_le_div_iff₀ hY (by linarith)] at h
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Covariance of an observable with a coordinate indicator equals `qₑ(1-qₑ) E_q[Δₑ f]`,
and is nonnegative for an increasing observable. -/
@[tag "VVDC"]
theorem covariance_coordinate_identity (q : E → ℝ) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (e : E) (f : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω * if ω e then 1 else 0) -
        expectation q f * expectation q (fun ω => if ω e then 1 else 0) =
      q e * (1 - q e) * expectation q (difference e f) ∧
    (Monotone f → 0 ≤ expectation q (fun ω => f ω * if ω e then 1 else 0) -
        expectation q f * expectation q (fun ω => if ω e then 1 else 0)) :=
  ⟨covariance_coordinate q e f, fun hf => covariance_coordinate_nonneg hq e hf⟩

/-- Russo's formula in the intensity parametrisation `q_β(e) = 1 - e^{-βJₑ}`, together with
the bounds on the coefficients `c_β(e) = Jₑ/(1 - e^{-βJₑ})`. -/
@[tag "DUYN"]
theorem intensity_russo_covariance (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e) {β : ℝ} (hβ : 0 < β)
    (f : (E → Bool) → ℝ) :
    HasDerivAt (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f)
      (∑ e ∈ univ.filter (fun e => 0 < J e), J e / (1 - Real.exp (-β * J e)) *
        (expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => f ω * if ω e then 1 else 0) -
          expectation (fun j => 1 - Real.exp (-β * J j)) f *
            expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0)))
      β ∧
    ∀ e, 0 < J e →
      (1 / β ≤ J e / (1 - Real.exp (-β * J e)) ∧
      0 < J e / (Real.exp (β * J e) - 1) ∧
      J e / (Real.exp (β * J e) - 1) = Real.exp (-β * J e) * (J e / (1 - Real.exp (-β * J e))) ∧
      J e / (Real.exp (β * J e) - 1) ≤ J e / (1 - Real.exp (-β * J e))) :=
  ⟨expectation_intensity_hasDerivAt_covariance J hJ hβ f,
    fun _ he => intensity_coefficient_bounds he hβ⟩

end PercLib.Probability.FiniteProfile
