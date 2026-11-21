/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for power-law convolution bounds on `ℤ^d`. All mathematical inputs are
proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.LatticeConvolution

/-!
# Power-law convolution bounds on `ℤ^d`: correspondence

Wiki correspondence for the power-law convolution bounds away from the logarithmic endpoints,
with `⟨x⟩ = max 1 √(∑ᵢ xᵢ²)` and `(f ⋆ g)(x) = ∑ y, f y g (x - y)`.

## Main results

* `abs_tsum_mul_sub_le_powerLaw`
-/

@[expose] public section

noncomputable section

namespace PercLib.Models.LongRange

/-- **Power-law convolution bounds away from logarithmic endpoints.** For `a, b > 0` there is a
constant `C` depending only on `a`, `b`, `d` such that, whenever `|f x| ≤ A ⟨x⟩^(-a)` and
`|g x| ≤ B ⟨x⟩^(-b)` with `A, B ≥ 0`, the sum `(f ⋆ g)(x)` converges absolutely and
`|(f ⋆ g)(x)| ≤ C A B ⟨x⟩^(-min a b)` if `max a b > d`, and
`|(f ⋆ g)(x)| ≤ C A B ⟨x⟩^(-(a + b - d))` if `a, b < d < a + b`. -/
@[tag "IDIL"]
theorem abs_tsum_mul_sub_le_powerLaw (d : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((d : ℝ) < max a b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℝ) (f g : (Fin d → ℤ) → ℝ), 0 ≤ A → 0 ≤ B →
        (∀ x, |f x| ≤ A * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) →
        (∀ x, |g x| ≤ B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-b)) →
        ∀ x, Summable (fun y => |f y * g (x - y)|) ∧
          |∑' y, f y * g (x - y)| ≤
            C * A * B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-min a b)) ∧
    (a < d → b < d → (d : ℝ) < a + b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℝ) (f g : (Fin d → ℤ) → ℝ), 0 ≤ A → 0 ≤ B →
        (∀ x, |f x| ≤ A * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) →
        (∀ x, |g x| ≤ B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-b)) →
        ∀ x, Summable (fun y => |f y * g (x - y)|) ∧
          |∑' y, f y * g (x - y)| ≤
            C * A * B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-(a + b - d))) :=
  ⟨exists_abs_tsum_mul_sub_le_of_lt_max d ha hb,
    exists_abs_tsum_mul_sub_le_of_lt_add d ha hb⟩

end PercLib.Models.LongRange
