/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: J. Basu and A. Sapozhnikov, Kesten's incipient infinite cluster and
quasi-multiplicativity of crossing probabilities, Electron. Commun. Probab. 22 (2017), paper 26,
arXiv:1603.06884v2, section 2 (the cross-ratio bound (2.7) and the contraction step that follows
it, there done with Hopf's theorem on the projective metric).
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Contraction of ratios under a cross-ratio bound

Let `M_0, M_1, …` be real matrices, `M_k` indexed by `ι k × ι (k + 1)` with every `ι k` finite,
satisfying the cross-ratio bound
`M_k(a, b) M_k(a', b') ≤ κ² M_k(a, b') M_k(a', b)`.
Push two row vectors `f_0`, `g_0` on `ι 0` forward: `f_{k+1}(b) = ∑_a f_k(a) M_k(a, b)`, and
likewise `g`. Then the ratio `⟨f_s, γ⟩ / ⟨g_s, γ⟩` hardly depends on the nonnegative weight `γ`
on `ι s`: if `0 ≤ f_0 ≤ g_0`, two weights `γ`, `γ'` give ratios within
`((κ² - 1) / (κ² + 1))^s`, hence within `(1 - κ⁻²)^s` when `κ ≥ 1`. In the backward
orientation, `⟨u', M_0 ⋯ M_{s-1} γ⟩ / ⟨u'', M_0 ⋯ M_{s-1} γ⟩` changes by at most as much when `γ`
changes. This is the step of Basu and Sapozhnikov's proof of the existence of Kesten's incipient
infinite cluster that they do with Hopf's contraction theorem.

The proof needs no positivity. Write `D(a, a') = f(a) g(a') - f(a') g(a)`. If
`D ≤ δ g(a) g(a')` for all `a`, `a'` (for `0 ≤ f ≤ g` this holds with `δ = 1`), then one step
gives the same with `δ (κ² - 1) / (κ² + 1)`. Indeed, with `x = M(·, b)`, `y = M(·, b')`, the
weights `c(a, a') = κ² x(a) y(a') - x(a') y(a)` are nonnegative by the cross-ratio bound, and
`∑ c D = (κ² + 1) ∑ x(a) y(a') D(a, a')` by antisymmetry of `D`. A last averaging against `γ`,
`γ'` gives the ratio bound.

Everything is stated for arbitrary finite index types and real entries; the iterated products
are written through the recursion hypotheses `hf`, `hg` (or `hw`, `hw'` backward), so no
definition is needed. Nothing here is about percolation. This file adds no definition.

## Main results

* `sum_mul_sum_sub_sum_mul_sum_eq`: the Lagrange-type identity behind every step.
* `sum_mul_sum_sub_sum_mul_sum_le`: averaging the pairwise bound against nonnegative weights.
* `sum_mul_sum_sub_sum_mul_sum_le_of_crossRatio`: one step contracts by `(κ² - 1) / (κ² + 1)`.
* `mul_sub_mul_le_pow_of_crossRatio`: `s` steps.
* `abs_div_sub_div_le_of_crossRatio`: the ratio bound `δ ((κ² - 1) / (κ² + 1))^s`.
* `abs_ratio_sub_ratio_le_of_crossRatio`: the same for `0 ≤ f_0 ≤ g_0`, bound
  `((κ² - 1) / (κ² + 1))^s`; `abs_ratio_sub_ratio_le_one_sub_inv_sq_pow_of_crossRatio`: bound
  `(1 - κ⁻²)^s` for `κ ≥ 1`.
* `sum_mul_eq_sum_mul_of_forall_lt`: pairing a forward and a backward recursion;
  `abs_ratio_sub_ratio_le_of_crossRatio_of_backward`: the ratio bound in the backward
  orientation `⟨u', M_0 ⋯ M_{s-1} γ⟩ / ⟨u'', M_0 ⋯ M_{s-1} γ⟩`.
-/

@[expose] public section

open Finset

namespace PercLib.Probability

/-! ### One step -/

/-- **Lagrange-type identity.** For row vectors `f`, `g` and columns `x`, `y`,
`⟨f, x⟩⟨g, y⟩ - ⟨f, y⟩⟨g, x⟩ = ∑_{a, a'} x(a) y(a') (f(a) g(a') - f(a') g(a))`. -/
theorem sum_mul_sum_sub_sum_mul_sum_eq {α : Type*} (s : Finset α) (f g x y : α → ℝ) :
    (∑ a ∈ s, f a * x a) * (∑ a ∈ s, g a * y a) - (∑ a ∈ s, f a * y a) * (∑ a ∈ s, g a * x a) =
      ∑ a ∈ s, ∑ a' ∈ s, x a * y a' * (f a * g a' - f a' * g a) := by
  rw [mul_comm (∑ a ∈ s, f a * y a), sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun a' _ => ?_
  ring

/-- **Averaging.** If `f(a) g(a') - f(a') g(a) ≤ δ g(a) g(a')` for all `a`, `a'`, then for
nonnegative weights `u`, `v`,
`⟨f, u⟩⟨g, v⟩ - ⟨f, v⟩⟨g, u⟩ ≤ δ ⟨g, u⟩⟨g, v⟩`. -/
theorem sum_mul_sum_sub_sum_mul_sum_le {α : Type*} (s : Finset α) {f g : α → ℝ} {δ : ℝ}
    (hfg : ∀ a ∈ s, ∀ a' ∈ s, f a * g a' - f a' * g a ≤ δ * (g a * g a')) {u v : α → ℝ}
    (hu : ∀ a ∈ s, 0 ≤ u a) (hv : ∀ a ∈ s, 0 ≤ v a) :
    (∑ a ∈ s, f a * u a) * (∑ a ∈ s, g a * v a) - (∑ a ∈ s, f a * v a) * (∑ a ∈ s, g a * u a) ≤
      δ * ((∑ a ∈ s, g a * u a) * (∑ a ∈ s, g a * v a)) := by
  rw [sum_mul_sum_sub_sum_mul_sum_eq, sum_mul_sum, mul_sum]
  refine sum_le_sum fun a ha => ?_
  rw [mul_sum]
  refine sum_le_sum fun a' ha' => ?_
  have h := mul_le_mul_of_nonneg_left (hfg a ha a' ha') (mul_nonneg (hu a ha) (hv a' ha'))
  linarith

/-- **One step of the contraction.** Under the cross-ratio bound
`M(a, b) M(a', b') ≤ κ² M(a, b') M(a', b)`, the pairwise bound
`f(a) g(a') - f(a') g(a) ≤ δ g(a) g(a')` passes to the row vectors `f M`, `g M` with
`δ (κ² - 1) / (κ² + 1)` in place of `δ`. No sign condition is needed. -/
theorem sum_mul_sum_sub_sum_mul_sum_le_of_crossRatio {α β : Type*} (s : Finset α)
    (M : α → β → ℝ) {κ δ : ℝ}
    (hM : ∀ a ∈ s, ∀ a' ∈ s, ∀ b b', M a b * M a' b' ≤ κ ^ 2 * (M a b' * M a' b))
    {f g : α → ℝ} (hfg : ∀ a ∈ s, ∀ a' ∈ s, f a * g a' - f a' * g a ≤ δ * (g a * g a'))
    (b b' : β) :
    (∑ a ∈ s, f a * M a b) * (∑ a ∈ s, g a * M a b') -
        (∑ a ∈ s, f a * M a b') * (∑ a ∈ s, g a * M a b) ≤
      δ * ((κ ^ 2 - 1) / (κ ^ 2 + 1)) *
        ((∑ a ∈ s, g a * M a b) * (∑ a ∈ s, g a * M a b')) := by
  rw [sum_mul_sum_sub_sum_mul_sum_eq]
  set K := κ ^ 2 with hK
  have hK1 : 0 < K + 1 := by rw [hK]; positivity
  set X := ∑ a ∈ s, g a * M a b with hX
  set Y := ∑ a ∈ s, g a * M a b' with hY
  set S := ∑ a ∈ s, ∑ a' ∈ s, M a b * M a' b' * (f a * g a' - f a' * g a) with hS
  -- the reversed double sum is `-S`
  have hswap : ∑ a ∈ s, ∑ a' ∈ s, M a' b * M a b' * (f a * g a' - f a' * g a) = -S := by
    rw [sum_comm, hS, ← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a' _ => ?_
    ring
  -- the weights `c(a, a') = K x(a) y(a') - x(a') y(a)` are nonnegative
  have hc : ∀ a ∈ s, ∀ a' ∈ s, 0 ≤ K * (M a b * M a' b') - M a' b * M a b' := by
    intro a ha a' ha'
    have := hM a' ha' a ha b b'
    linarith
  have hcD : ∑ a ∈ s, ∑ a' ∈ s, (K * (M a b * M a' b') - M a' b * M a b') *
      (f a * g a' - f a' * g a) = (K + 1) * S := by
    have : ∑ a ∈ s, ∑ a' ∈ s, (K * (M a b * M a' b') - M a' b * M a b') *
        (f a * g a' - f a' * g a) =
        K * S - ∑ a ∈ s, ∑ a' ∈ s, M a' b * M a b' * (f a * g a' - f a' * g a) := by
      rw [hS, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun a' _ => ?_
      ring
    rw [this, hswap]
    ring
  have hle : ∑ a ∈ s, ∑ a' ∈ s, (K * (M a b * M a' b') - M a' b * M a b') *
      (f a * g a' - f a' * g a) ≤
      ∑ a ∈ s, ∑ a' ∈ s, (K * (M a b * M a' b') - M a' b * M a b') * (δ * (g a * g a')) :=
    sum_le_sum fun a ha => sum_le_sum fun a' ha' =>
      mul_le_mul_of_nonneg_left (hfg a ha a' ha') (hc a ha a' ha')
  have hcg : ∑ a ∈ s, ∑ a' ∈ s, (K * (M a b * M a' b') - M a' b * M a b') * (δ * (g a * g a')) =
      δ * (K - 1) * (X * Y) := by
    have : ∑ a ∈ s, ∑ a' ∈ s, (K * (M a b * M a' b') - M a' b * M a b') * (δ * (g a * g a')) =
        K * δ * (X * Y) - δ * (Y * X) := by
      rw [hX, hY, sum_mul_sum, sum_mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun a' _ => ?_
      ring
    rw [this]
    ring
  rw [show δ * ((K - 1) / (K + 1)) * (X * Y) = δ * (K - 1) * (X * Y) / (K + 1) by ring,
    le_div_iff₀ hK1]
  linarith

/-! ### Iteration and the ratio bound -/

variable {ι : ℕ → Type*} [∀ k, Fintype (ι k)]

/-- **`s` steps.** Push `f`, `g` forward through matrices with the cross-ratio bound: the
pairwise bound contracts by `(κ² - 1) / (κ² + 1)` at each step. -/
theorem mul_sub_mul_le_pow_of_crossRatio (M : ∀ k, ι k → ι (k + 1) → ℝ) {κ δ : ℝ}
    (hM : ∀ k a a' b b', M k a b * M k a' b' ≤ κ ^ 2 * (M k a b' * M k a' b))
    {f g : ∀ k, ι k → ℝ} (hf : ∀ k b, f (k + 1) b = ∑ a, f k a * M k a b)
    (hg : ∀ k b, g (k + 1) b = ∑ a, g k a * M k a b)
    (h0 : ∀ a a', f 0 a * g 0 a' - f 0 a' * g 0 a ≤ δ * (g 0 a * g 0 a')) (s : ℕ)
    (b b' : ι s) :
    f s b * g s b' - f s b' * g s b ≤ δ * ((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ s * (g s b * g s b') := by
  induction s with
  | zero => simpa using h0 b b'
  | succ s ih =>
    rw [hf, hf, hg, hg, show δ * ((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ (s + 1) =
      δ * ((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ s * ((κ ^ 2 - 1) / (κ ^ 2 + 1)) by ring]
    exact sum_mul_sum_sub_sum_mul_sum_le_of_crossRatio _ (M s)
      (fun a _ a' _ b b' => hM s a a' b b') (fun a _ a' _ => ih a a') b b'

/-- **The ratio bound.** Under the cross-ratio bound, with `f`, `g` pushed forward and the
pairwise bound `δ` at the start, two nonnegative weights `γ`, `γ'` on `ι s` give ratios
`⟨f_s, γ⟩ / ⟨g_s, γ⟩` within `δ ((κ² - 1) / (κ² + 1))^s`. -/
theorem abs_div_sub_div_le_of_crossRatio (M : ∀ k, ι k → ι (k + 1) → ℝ) {κ δ : ℝ}
    (hM : ∀ k a a' b b', M k a b * M k a' b' ≤ κ ^ 2 * (M k a b' * M k a' b))
    {f g : ∀ k, ι k → ℝ} (hf : ∀ k b, f (k + 1) b = ∑ a, f k a * M k a b)
    (hg : ∀ k b, g (k + 1) b = ∑ a, g k a * M k a b)
    (h0 : ∀ a a', f 0 a * g 0 a' - f 0 a' * g 0 a ≤ δ * (g 0 a * g 0 a')) {s : ℕ}
    {γ γ' : ι s → ℝ} (hγ : ∀ b, 0 ≤ γ b) (hγ' : ∀ b, 0 ≤ γ' b)
    (hpos : 0 < ∑ b, g s b * γ b) (hpos' : 0 < ∑ b, g s b * γ' b) :
    |(∑ b, f s b * γ b) / (∑ b, g s b * γ b) - (∑ b, f s b * γ' b) / (∑ b, g s b * γ' b)| ≤
      δ * ((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ s := by
  have hs := mul_sub_mul_le_pow_of_crossRatio M hM hf hg h0 s
  have h₁ := sum_mul_sum_sub_sum_mul_sum_le univ (fun b _ b' _ => hs b b')
    (fun b _ => hγ b) (fun b _ => hγ' b)
  have h₂ := sum_mul_sum_sub_sum_mul_sum_le univ (fun b _ b' _ => hs b b')
    (fun b _ => hγ' b) (fun b _ => hγ b)
  rw [abs_sub_le_iff, div_sub_div _ _ hpos.ne' hpos'.ne', div_sub_div _ _ hpos'.ne' hpos.ne',
    div_le_iff₀ (mul_pos hpos hpos'), div_le_iff₀ (mul_pos hpos' hpos)]
  constructor <;> linarith

/-- **The ratio bound for `0 ≤ f_0 ≤ g_0`** (Basu–Sapozhnikov's contraction step). Under the
cross-ratio bound `M_k(a, b) M_k(a', b') ≤ κ² M_k(a, b') M_k(a', b)`, with `f`, `g` pushed
forward from `0 ≤ f_0 ≤ g_0`, two nonnegative weights `γ`, `γ'` on `ι s` give ratios
`⟨f_s, γ⟩ / ⟨g_s, γ⟩` within `((κ² - 1) / (κ² + 1))^s`. -/
theorem abs_ratio_sub_ratio_le_of_crossRatio (M : ∀ k, ι k → ι (k + 1) → ℝ) {κ : ℝ}
    (hM : ∀ k a a' b b', M k a b * M k a' b' ≤ κ ^ 2 * (M k a b' * M k a' b))
    {f g : ∀ k, ι k → ℝ} (hf : ∀ k b, f (k + 1) b = ∑ a, f k a * M k a b)
    (hg : ∀ k b, g (k + 1) b = ∑ a, g k a * M k a b) (hf0 : ∀ a, 0 ≤ f 0 a)
    (hfg0 : ∀ a, f 0 a ≤ g 0 a) {s : ℕ} {γ γ' : ι s → ℝ} (hγ : ∀ b, 0 ≤ γ b)
    (hγ' : ∀ b, 0 ≤ γ' b) (hpos : 0 < ∑ b, g s b * γ b) (hpos' : 0 < ∑ b, g s b * γ' b) :
    |(∑ b, f s b * γ b) / (∑ b, g s b * γ b) - (∑ b, f s b * γ' b) / (∑ b, g s b * γ' b)| ≤
      ((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ s := by
  have h0 : ∀ a a', f 0 a * g 0 a' - f 0 a' * g 0 a ≤ 1 * (g 0 a * g 0 a') := by
    intro a a'
    have h₁ := mul_le_mul_of_nonneg_right (hfg0 a) ((hf0 a').trans (hfg0 a'))
    have h₂ := mul_nonneg (hf0 a') ((hf0 a).trans (hfg0 a))
    linarith
  have h := abs_div_sub_div_le_of_crossRatio M hM hf hg h0 hγ hγ' hpos hpos'
  rwa [one_mul] at h

/-- For `κ ≥ 1`, `(κ² - 1) / (κ² + 1) ≤ 1 - κ⁻²`. -/
theorem div_le_one_sub_inv_sq {κ : ℝ} (hκ : 1 ≤ κ) :
    (κ ^ 2 - 1) / (κ ^ 2 + 1) ≤ 1 - κ⁻¹ ^ 2 := by
  have hK : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hK0 : κ ^ 2 ≠ 0 := by positivity
  have hinv : (κ ^ 2)⁻¹ * κ ^ 2 = 1 := inv_mul_cancel₀ hK0
  have hinv1 : (κ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  rw [inv_pow, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The ratio bound with `1 - κ⁻²`**, the form of the arms plan: for `κ ≥ 1` the two ratios
are within `(1 - κ⁻²)^s`. -/
theorem abs_ratio_sub_ratio_le_one_sub_inv_sq_pow_of_crossRatio (M : ∀ k, ι k → ι (k + 1) → ℝ)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hM : ∀ k a a' b b', M k a b * M k a' b' ≤ κ ^ 2 * (M k a b' * M k a' b))
    {f g : ∀ k, ι k → ℝ} (hf : ∀ k b, f (k + 1) b = ∑ a, f k a * M k a b)
    (hg : ∀ k b, g (k + 1) b = ∑ a, g k a * M k a b) (hf0 : ∀ a, 0 ≤ f 0 a)
    (hfg0 : ∀ a, f 0 a ≤ g 0 a) {s : ℕ} {γ γ' : ι s → ℝ} (hγ : ∀ b, 0 ≤ γ b)
    (hγ' : ∀ b, 0 ≤ γ' b) (hpos : 0 < ∑ b, g s b * γ b) (hpos' : 0 < ∑ b, g s b * γ' b) :
    |(∑ b, f s b * γ b) / (∑ b, g s b * γ b) - (∑ b, f s b * γ' b) / (∑ b, g s b * γ' b)| ≤
      (1 - κ⁻¹ ^ 2) ^ s := by
  refine (abs_ratio_sub_ratio_le_of_crossRatio M hM hf hg hf0 hfg0 hγ hγ' hpos hpos').trans ?_
  have hK : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  exact pow_le_pow_left₀ (div_nonneg (by linarith) (by positivity)) (div_le_one_sub_inv_sq hκ) s

/-! ### The backward orientation -/

/-- **Pairing a forward and a backward recursion.** If `h_{k+1} = h_k M_k` for every `k` and
`w_k = M_k w_{k+1}` for `k < s`, then `⟨h_0, w_0⟩ = ⟨h_k, w_k⟩` for every `k ≤ s`. -/
theorem sum_mul_eq_sum_mul_of_forall_lt (M : ∀ k, ι k → ι (k + 1) → ℝ) {h w : ∀ k, ι k → ℝ}
    (hh : ∀ k b, h (k + 1) b = ∑ a, h k a * M k a b) {s : ℕ}
    (hw : ∀ k < s, ∀ a, w k a = ∑ b, M k a b * w (k + 1) b) {k : ℕ} (hk : k ≤ s) :
    ∑ a, h 0 a * w 0 a = ∑ a, h k a * w k a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ih (Nat.le_of_succ_le hk)]
    simp_rw [hh, sum_mul, hw k (Nat.lt_of_succ_le hk), mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring

/-- **The ratio bound, backward orientation**: under the cross-ratio bound, for
`0 ≤ u' ≤ u''` on `ι 0` and two backward recursions `w_k = M_k w_{k+1}`, `w'_k = M_k w'_{k+1}`
(`k < s`) started from nonnegative `w_s`, `w'_s`, the ratios
`⟨u', w_0⟩ / ⟨u'', w_0⟩ = ⟨u', M_0 ⋯ M_{s-1} w_s⟩ / ⟨u'', M_0 ⋯ M_{s-1} w_s⟩` and the same for
`w'` are within `((κ² - 1) / (κ² + 1))^s`. -/
theorem abs_ratio_sub_ratio_le_of_crossRatio_of_backward (M : ∀ k, ι k → ι (k + 1) → ℝ)
    {κ : ℝ} (hM : ∀ k a a' b b', M k a b * M k a' b' ≤ κ ^ 2 * (M k a b' * M k a' b))
    {u' u'' : ι 0 → ℝ} (hu' : ∀ a, 0 ≤ u' a) (hu : ∀ a, u' a ≤ u'' a) {s : ℕ}
    {w w' : ∀ k, ι k → ℝ} (hw : ∀ k < s, ∀ a, w k a = ∑ b, M k a b * w (k + 1) b)
    (hw' : ∀ k < s, ∀ a, w' k a = ∑ b, M k a b * w' (k + 1) b) (hws : ∀ b, 0 ≤ w s b)
    (hws' : ∀ b, 0 ≤ w' s b) (hpos : 0 < ∑ a, u'' a * w 0 a)
    (hpos' : 0 < ∑ a, u'' a * w' 0 a) :
    |(∑ a, u' a * w 0 a) / (∑ a, u'' a * w 0 a) - (∑ a, u' a * w' 0 a) / (∑ a, u'' a * w' 0 a)| ≤
      ((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ s := by
  let f : ∀ k, ι k → ℝ := fun k =>
    Nat.rec (motive := fun k => ι k → ℝ) u' (fun k fk b => ∑ a, fk a * M k a b) k
  let g : ∀ k, ι k → ℝ := fun k =>
    Nat.rec (motive := fun k => ι k → ℝ) u'' (fun k gk b => ∑ a, gk a * M k a b) k
  have hf : ∀ k b, f (k + 1) b = ∑ a, f k a * M k a b := fun _ _ => rfl
  have hg : ∀ k b, g (k + 1) b = ∑ a, g k a * M k a b := fun _ _ => rfl
  have e₁ := sum_mul_eq_sum_mul_of_forall_lt M hf hw le_rfl
  have e₂ := sum_mul_eq_sum_mul_of_forall_lt M hg hw le_rfl
  have e₃ := sum_mul_eq_sum_mul_of_forall_lt M hf hw' le_rfl
  have e₄ := sum_mul_eq_sum_mul_of_forall_lt M hg hw' le_rfl
  change |(∑ a, f 0 a * w 0 a) / (∑ a, g 0 a * w 0 a) -
    (∑ a, f 0 a * w' 0 a) / (∑ a, g 0 a * w' 0 a)| ≤ _
  change 0 < ∑ a, g 0 a * w 0 a at hpos
  change 0 < ∑ a, g 0 a * w' 0 a at hpos'
  rw [e₂] at hpos
  rw [e₄] at hpos'
  rw [e₁, e₂, e₃, e₄]
  exact abs_ratio_sub_ratio_le_of_crossRatio M hM hf hg hu' hu hws hws' hpos hpos'

end PercLib.Probability
