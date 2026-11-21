/-
Two-point (Bernoulli) divergence inequalities for the exponential intensity family. New
proofs against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, using mathlib's
`InformationTheory.klFun`; no upstream proof is copied. The Bernoulli divergence
`d(a‖b) = a log(a/b) + (1−a) log((1−a)/(1−b))` is written out; no definition is introduced.
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Bernoulli divergence for the exponential intensity family

Quadratic bounds for `klFun` and comparison of the divergence between two Bernoulli laws with
parameters `1 - e^{-βJ}` with the Poisson divergence.

## Main results

* `two_mul_min_mul_klFun_le`
* `sq_sub_one_le_two_mul_max_mul_klFun`
* `bernoulliDivergence_exp_le`
* `mul_poissonDivergence_le`
* `bernoulliDivergence_exp_le_of_nonneg`
* `sq_sub_le_two_mul_max_mul_bernoulliDivergence`
-/

@[expose] public section

open Real Set InformationTheory

namespace PercLib.Probability

/-- A function whose derivative is nonnegative on `(a, b)` satisfies `f a ≤ f b`. -/
theorem le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s) (h : ∀ s ∈ Ioo a b, 0 ≤ f' s) :
    f a ≤ f b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hlt
    (fun s hs => (hf s hs).continuousAt.continuousWithinAt)
    (fun s hs => hf s (Ioo_subset_Icc_self hs))
  have h1 := h c hc
  rw [hcs, le_div_iff₀ (sub_pos.2 hlt), zero_mul, sub_nonneg] at h1
  exact h1

/-- A function whose derivative is nonpositive on `(a, b)` satisfies `f b ≤ f a`. -/
theorem le_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s) (h : ∀ s ∈ Ioo a b, f' s ≤ 0) :
    f b ≤ f a := by
  have := le_of_hasDerivAt_nonneg (f := fun s => -f s) (f' := fun s => -f' s) hab
    (fun s hs => (hf s hs).neg) (fun s hs => neg_nonneg.2 (h s hs))
  simpa using this

/-! ### Quadratic bounds for `klFun t = t log t + 1 − t` -/

/-- `2 min(t,1) · klFun t ≤ (t − 1)²` for `t > 0`. -/
theorem two_mul_min_mul_klFun_le {t : ℝ} (ht : 0 < t) :
    2 * min t 1 * klFun t ≤ (t - 1) ^ 2 := by
  rcases le_total 1 t with h1 | h1
  · -- `F s = (s − 1)² / 2 − klFun s` is nondecreasing on `[1, t]`.
    rw [min_eq_right h1]
    have := le_of_hasDerivAt_nonneg (f := fun s => (s - 1) ^ 2 / 2 - klFun s)
      (f' := fun s => (s - 1) - log s) h1
      (fun s hs => by
        have hs0 : s ≠ 0 := (zero_lt_one.trans_le hs.1).ne'
        have := ((((hasDerivAt_id s).sub_const 1).pow 2).div_const 2).sub (hasDerivAt_klFun hs0)
        exact this.congr_deriv (by simp))
      (fun s hs => by
        have := log_le_sub_one_of_pos (zero_lt_one.trans hs.1)
        linarith)
    simp only [klFun_one, sub_self] at this
    norm_num at this
    linarith
  · -- `F s = s⁻¹/2 − 1 + s/2 − klFun s` is nonincreasing on `[t, 1]`.
    rw [min_eq_left h1]
    have := le_of_hasDerivAt_nonpos (f := fun s => s⁻¹ / 2 - 1 + s / 2 - klFun s)
      (f' := fun s => -(s ^ 2)⁻¹ / 2 + 1 / 2 - log s) h1
      (fun s hs => by
        have hs0 : s ≠ 0 := (ht.trans_le hs.1).ne'
        have := ((((hasDerivAt_inv hs0).div_const 2).sub_const 1).add
          ((hasDerivAt_id s).div_const 2)).sub (hasDerivAt_klFun hs0)
        exact this)
      (fun s hs => by
        have hs0 : 0 < s := ht.trans hs.1
        -- `log (1/s) ≤ 1/s − 1 ≤ (1/s² − 1)/2`.
        have hl := log_le_sub_one_of_pos (inv_pos.2 hs0)
        rw [log_inv] at hl
        have hi : 1 ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs.2.le
        have : (s ^ 2)⁻¹ = s⁻¹ * s⁻¹ := by rw [pow_two, mul_inv]
        nlinarith)
    simp only [klFun_one, inv_one] at this
    have e : (t - 1) ^ 2 = 2 * t * (t⁻¹ / 2 - 1 + t / 2) := by field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (by linarith : klFun t ≤ t⁻¹ / 2 - 1 + t / 2)
      (by positivity : (0 : ℝ) ≤ 2 * t)
    linarith

/-- `(t − 1)² ≤ 2 max(t,1) · klFun t` for `t > 0`. -/
theorem sq_sub_one_le_two_mul_max_mul_klFun {t : ℝ} (ht : 0 < t) :
    (t - 1) ^ 2 ≤ 2 * max t 1 * klFun t := by
  rcases le_total 1 t with h1 | h1
  · -- `F s = klFun s − (s/2 − 1 + s⁻¹/2)` is nondecreasing on `[1, t]`.
    rw [max_eq_left h1]
    have := le_of_hasDerivAt_nonneg (f := fun s => klFun s - (s / 2 - 1 + s⁻¹ / 2))
      (f' := fun s => log s - (1 / 2 + -(s ^ 2)⁻¹ / 2)) h1
      (fun s hs => by
        have hs0 : s ≠ 0 := (zero_lt_one.trans_le hs.1).ne'
        exact (hasDerivAt_klFun hs0).sub ((((hasDerivAt_id s).div_const 2).sub_const 1).add
          ((hasDerivAt_inv hs0).div_const 2)))
      (fun s hs => by
        have hs0 : 0 < s := zero_lt_one.trans hs.1
        -- `log s ≥ 1 − 1/s ≥ (1 − 1/s²)/2`.
        have hl := log_le_sub_one_of_pos (inv_pos.2 hs0)
        rw [log_inv] at hl
        have hi : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs.1.le
        have hi0 : 0 < s⁻¹ := inv_pos.2 hs0
        have : (s ^ 2)⁻¹ = s⁻¹ * s⁻¹ := by rw [pow_two, mul_inv]
        nlinarith)
    simp only [klFun_one, inv_one] at this
    have e : (t - 1) ^ 2 = 2 * t * (t / 2 - 1 + t⁻¹ / 2) := by field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (by linarith : t / 2 - 1 + t⁻¹ / 2 ≤ klFun t)
      (by positivity : (0 : ℝ) ≤ 2 * t)
    linarith
  · -- `F s = klFun s − (s − 1)²/2` is nonincreasing on `[t, 1]`.
    rw [max_eq_right h1]
    have := le_of_hasDerivAt_nonpos (f := fun s => klFun s - (s - 1) ^ 2 / 2)
      (f' := fun s => log s - (s - 1)) h1
      (fun s hs => by
        have hs0 : s ≠ 0 := (ht.trans_le hs.1).ne'
        have := (hasDerivAt_klFun hs0).sub ((((hasDerivAt_id s).sub_const 1).pow 2).div_const 2)
        exact this.congr_deriv (by simp))
      (fun s hs => by
        have := log_le_sub_one_of_pos (ht.trans hs.1)
        linarith)
    simp only [klFun_one] at this
    norm_num at this
    linarith

/-! ### The secant inequality for `1 − e^{−s}` -/

/-- For `0 < u ≤ v`: `u (1 − e^{−v}) ≤ v (1 − e^{−u})`, i.e. `(1 − e^{−s})/s` decreases. -/
theorem mul_one_sub_exp_neg_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    u * (1 - exp (-v)) ≤ v * (1 - exp (-u)) := by
  have hv : 0 < v := hu.trans_le huv
  have hw0 : 0 ≤ u / v := (div_pos hu hv).le
  have hw1 : 0 ≤ 1 - u / v := sub_nonneg.2 ((div_le_one hv).2 huv)
  have := convexOn_exp.2 (mem_univ (-v)) (mem_univ 0) hw0 hw1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at this
  have e : u / v * -v = -u := by field_simp
  rw [e] at this
  have := mul_le_mul_of_nonneg_left this hv.le
  have e2 : v * (u / v * exp (-v) + (1 - u / v)) = u * exp (-v) + v - u := by
    field_simp; ring
  rw [e2] at this
  linarith

/-! ### KHB7 -/

/-- The Bernoulli law with parameter `1 − e^{−x}` is closer to that with parameter
`1 − e^{−y}` than the Poisson law of mean `x` is to that of mean `y`. -/
theorem bernoulli_exp_div_le_poisson {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 - exp (-x)) * log ((1 - exp (-x)) / (1 - exp (-y))) +
        (1 - (1 - exp (-x))) * log ((1 - (1 - exp (-x))) / (1 - (1 - exp (-y)))) ≤
      x * log (x / y) - x + y := by
  set A := 1 - exp (-x) with hAdef
  have hA : 0 < A := by simp only [hAdef, sub_pos, exp_lt_one_iff, neg_lt_zero]; exact hx
  have hB : 0 < 1 - exp (-y) := by simp only [sub_pos, exp_lt_one_iff, neg_lt_zero]; exact hy
  -- `G s = A log(1 − e^{−s}) − x log s + A s` is minimised at `s = x`.
  let G : ℝ → ℝ := fun s => A * log (1 - exp (-s)) - x * log s + A * s
  let G' : ℝ → ℝ := fun s => A / (1 - exp (-s)) - x / s
  have hG : ∀ s, 0 < s → HasDerivAt G (G' s) s := by
    intro s hs
    have hBs : 0 < 1 - exp (-s) := by simp only [sub_pos, exp_lt_one_iff, neg_lt_zero]; exact hs
    have h1 : HasDerivAt (fun s => 1 - exp (-s)) (exp (-s)) s := by
      simpa using ((hasDerivAt_neg s).exp).const_sub 1
    have := ((h1.log hBs.ne').const_mul A).sub ((hasDerivAt_log hs.ne').const_mul x) |>.add
      ((hasDerivAt_id s).const_mul A)
    refine this.congr_deriv ?_
    have := hBs.ne'
    simp only [G']
    field_simp
    ring
  have hGx : G x ≤ G y := by
    rcases le_total x y with hxy | hxy
    · refine le_of_hasDerivAt_nonneg hxy (fun s hs => hG s (hx.trans_le hs.1)) ?_
      intro s hs
      have hs0 : 0 < s := hx.trans hs.1
      have hBs : 0 < 1 - exp (-s) := by simp only [sub_pos, exp_lt_one_iff, neg_lt_zero]; exact hs0
      simp only [G', sub_nonneg]
      rw [div_le_div_iff₀ hs0 hBs]
      have := mul_one_sub_exp_neg_le hx hs.1.le
      rw [hAdef]; linarith
    · refine le_of_hasDerivAt_nonpos hxy (fun s hs => hG s (hy.trans_le hs.1)) ?_
      intro s hs
      have hs0 : 0 < s := hy.trans hs.1
      have hBs : 0 < 1 - exp (-s) := by simp only [sub_pos, exp_lt_one_iff, neg_lt_zero]; exact hs0
      simp only [G', sub_nonpos]
      rw [div_le_div_iff₀ hBs hs0]
      have := mul_one_sub_exp_neg_le hs0 hs.2.le
      rw [hAdef]; linarith
  simp only [G] at hGx
  have e1 : 1 - (1 - exp (-x)) = exp (-x) := by ring
  have e2 : 1 - (1 - exp (-y)) = exp (-y) := by ring
  rw [e1, e2, ← exp_sub, log_exp, log_div hA.ne' hB.ne', log_div hx.ne' hy.ne']
  have hsum : A * (y - x) + exp (-x) * (y - x) = y - x := by rw [hAdef]; ring
  nlinarith [hGx, hsum]

/-- **KHB7, first inequality.** For `J, β₁, β₂ > 0`,
`d(1 − e^{−β₁J} ‖ 1 − e^{−β₂J}) ≤ J (β₁ log(β₁/β₂) − β₁ + β₂)`. -/
theorem bernoulliDivergence_exp_le {J β₁ β₂ : ℝ} (hJ : 0 < J) (h₁ : 0 < β₁) (h₂ : 0 < β₂) :
    (1 - exp (-(β₁ * J))) * log ((1 - exp (-(β₁ * J))) / (1 - exp (-(β₂ * J)))) +
        (1 - (1 - exp (-(β₁ * J)))) *
          log ((1 - (1 - exp (-(β₁ * J)))) / (1 - (1 - exp (-(β₂ * J))))) ≤
      J * (β₁ * log (β₁ / β₂) - β₁ + β₂) := by
  refine (bernoulli_exp_div_le_poisson (mul_pos h₁ hJ) (mul_pos h₂ hJ)).trans_eq ?_
  rw [mul_div_mul_right _ _ hJ.ne']
  ring

/-- **KHB7, second inequality.** For `J ≥ 0` and `β₁, β₂ > 0`,
`J (β₁ log(β₁/β₂) − β₁ + β₂) ≤ J (β₁ − β₂)² / (2 min{β₁, β₂})`. -/
theorem mul_poissonDivergence_le {J β₁ β₂ : ℝ} (hJ : 0 ≤ J) (h₁ : 0 < β₁) (h₂ : 0 < β₂) :
    J * (β₁ * log (β₁ / β₂) - β₁ + β₂) ≤ J * (β₁ - β₂) ^ 2 / (2 * min β₁ β₂) := by
  have ht : 0 < β₁ / β₂ := div_pos h₁ h₂
  have hk := two_mul_min_mul_klFun_le ht
  have e1 : β₁ * log (β₁ / β₂) - β₁ + β₂ = β₂ * klFun (β₁ / β₂) := by
    rw [klFun_apply]; field_simp; ring
  have e2 : min β₁ β₂ = β₂ * min (β₁ / β₂) 1 := by
    rw [mul_min_of_nonneg _ _ h₂.le, mul_div_cancel₀ _ h₂.ne', mul_one]
  have e3 : (β₁ - β₂) ^ 2 = β₂ ^ 2 * (β₁ / β₂ - 1) ^ 2 := by field_simp
  have hm : 0 < min β₁ β₂ := lt_min h₁ h₂
  rw [e1, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hJ
  rw [le_div_iff₀ (by positivity), e2, e3]
  have := mul_le_mul_of_nonneg_left hk (sq_nonneg β₂)
  nlinarith [this]

/-- **KHB7, the case `J = 0`.** Both parameters vanish, and the explicit expression for
the divergence is `0` (with Lean's conventions `log 0 = 0` and `0 / 0 = 0`). -/
theorem bernoulliDivergence_exp_zero (β₁ β₂ : ℝ) :
    (1 - exp (-(β₁ * 0))) * log ((1 - exp (-(β₁ * 0))) / (1 - exp (-(β₂ * 0)))) +
        (1 - (1 - exp (-(β₁ * 0)))) *
          log ((1 - (1 - exp (-(β₁ * 0)))) / (1 - (1 - exp (-(β₂ * 0))))) = 0 := by
  simp

/-- The divergence bound of `bernoulliDivergence_exp_le` for every `J ≥ 0`; at `J = 0` both
sides vanish. -/
theorem bernoulliDivergence_exp_le_of_nonneg {J β₁ β₂ : ℝ} (hJ : 0 ≤ J) (h₁ : 0 < β₁)
    (h₂ : 0 < β₂) :
    (1 - exp (-(β₁ * J))) * log ((1 - exp (-(β₁ * J))) / (1 - exp (-(β₂ * J)))) +
        (1 - (1 - exp (-(β₁ * J)))) *
          log ((1 - (1 - exp (-(β₁ * J)))) / (1 - (1 - exp (-(β₂ * J))))) ≤
      J * (β₁ * log (β₁ / β₂) - β₁ + β₂) := by
  rcases hJ.eq_or_lt with h0 | hpos
  · subst h0
    rw [bernoulliDivergence_exp_zero, zero_mul]
  · exact bernoulliDivergence_exp_le hpos h₁ h₂

/-! ### 58HC, two-point form -/

/-- **58HC, two-point form.** For `a, b ∈ (0,1)`: `(a − b)² ≤ 2 max{a,b} · d(a‖b)`. -/
theorem sq_sub_le_two_mul_max_mul_bernoulliDivergence {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    (a - b) ^ 2 ≤ 2 * max a b * (a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))) := by
  have hb' : 0 < 1 - b := sub_pos.2 hb1
  have ha' : 0 < 1 - a := sub_pos.2 ha1
  -- `d(a‖b) = b klFun(a/b) + (1 − b) klFun((1 − a)/(1 − b))`.
  have e1 : a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b)) =
      b * klFun (a / b) + (1 - b) * klFun ((1 - a) / (1 - b)) := by
    rw [klFun_apply, klFun_apply]; field_simp; ring
  have h2 : 0 ≤ (1 - b) * klFun ((1 - a) / (1 - b)) :=
    mul_nonneg hb'.le (klFun_nonneg (div_pos ha' hb').le)
  have hk := sq_sub_one_le_two_mul_max_mul_klFun (div_pos ha hb)
  have e2 : max a b = b * max (a / b) 1 := by
    rw [mul_max_of_nonneg _ _ hb.le, mul_div_cancel₀ _ hb.ne', mul_one]
  have e3 : (a - b) ^ 2 = b ^ 2 * (a / b - 1) ^ 2 := by field_simp
  rw [e1, e2, e3]
  have := mul_le_mul_of_nonneg_left hk (sq_nonneg b)
  have hm : 0 ≤ b * max (a / b) 1 := by positivity
  nlinarith [mul_nonneg (mul_nonneg zero_le_two hm) h2]

/-! ### Non-vacuity witnesses (D-5) -/

/-- `β₁ = β₂`: both sides of KHB7 vanish. -/
example (J β : ℝ) :
    (1 - exp (-(β * J))) * log ((1 - exp (-(β * J))) / (1 - exp (-(β * J)))) +
        (1 - (1 - exp (-(β * J)))) *
          log ((1 - (1 - exp (-(β * J)))) / (1 - (1 - exp (-(β * J))))) = 0 ∧
      J * (β * log (β / β) - β + β) = 0 ∧ J * (β - β) ^ 2 / (2 * min β β) = 0 := by
  refine ⟨?_, by simp, by simp⟩
  rcases eq_or_ne (1 - exp (-(β * J))) 0 with h | h
  · rw [h]; simp
  · rw [div_self h]
    rcases eq_or_ne (1 - (1 - exp (-(β * J)))) 0 with h' | h'
    · rw [h']; simp
    · rw [div_self h']; simp

/-- `J = 1, β₁ = 2, β₂ = 1`: `d ≤ 2 log 2 − 1 ≤ 1/2`. -/
example :
    (1 - exp (-(2 * 1))) * log ((1 - exp (-(2 * 1))) / (1 - exp (-(1 * 1)))) +
        (1 - (1 - exp (-(2 * 1)))) *
          log ((1 - (1 - exp (-(2 * 1)))) / (1 - (1 - exp (-(1 * 1))))) ≤
      1 * (2 * log (2 / 1) - 2 + 1) ∧
      1 * (2 * log (2 / 1) - 2 + 1) ≤ 1 * ((2 : ℝ) - 1) ^ 2 / (2 * min 2 1) :=
  ⟨bernoulliDivergence_exp_le one_pos two_pos one_pos,
    mul_poissonDivergence_le zero_le_one two_pos one_pos⟩

/-- 58HC at `a = 1/2, b = 1/4`. -/
example : ((1 / 2 : ℝ) - 1 / 4) ^ 2 ≤ 2 * max (1 / 2) (1 / 4) *
    (1 / 2 * log ((1 / 2) / (1 / 4)) + (1 - 1 / 2) * log ((1 - 1 / 2) / (1 - 1 / 4))) :=
  sq_sub_le_two_mul_max_mul_bernoulliDivergence (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end PercLib.Probability
