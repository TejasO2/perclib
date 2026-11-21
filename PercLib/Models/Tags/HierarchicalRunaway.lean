/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's runaway theorems. No upstream code is copied and no
definition is added. Mathematical reference: T. Hutchcroft, *The critical two-point function for
long-range percolation on the hierarchical lattice*, arXiv:2103.17013v1, Proposition 2.2.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalRunawayInterval

/-!
# Hierarchical runaway bound (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `sq_tightnessScale_lt_and_le_of_chi_lt_top`: the block-quantile bound from finite
  susceptibility, strict at a parameter and non-strict up to the end of an interval.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ}

open Classical in
/-- On `ℕ →₀ (Fin d → ZMod L)` with `L ≥ 2`, `c, α > 0`, a translation-invariant kernel `J`
with `J(u,v) ≥ c L^{-(d+α)j}` at first common level `j`: with `R_n(β)` the quantile
`tightnessScale` of the origin's level-`n` block under the profile restricted to that block,
`N = L^{dℓ}`, `e^{-N/(8e)} ≤ 1/4`, `L^{(d-α)ℓ} ≥ 16e²` and `A = (4/c) L^{(d+α)ℓ} log(2N²)`:
if `β > 0` and `χ(β) < ∞` then `R_n(β)² < (A/β) L^{(d+α)n}` for every `n`; and if `a < b` and
`χ(β) < ∞` for every `β ∈ (a, b)` then `R_n(β)² ≤ (A/b) L^{(d+α)n}` for every `n` and every
`β ≤ b`. -/
@[tag "2XJX"]
theorem sq_tightnessScale_lt_and_le_of_chi_lt_top [NeZero L] (hL : 2 ≤ L) {α c : ℝ}
    (hc : 0 < c) (hα : 0 < α) (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (hJt : ∀ x u v, J s(u + x, v + x) = J s(u, v))
    (hJ : ∀ u v, u ≠ v →
      c * (L : ℝ) ^ (-(((d : ℝ) + α) * (((v - u).support.sup Nat.succ : ℕ) : ℝ))) ≤ J s(u, v))
    {ℓ : ℕ} (hexp : Real.exp (-((L : ℝ) ^ (d * ℓ) / (8 * Real.exp 1))) ≤ 1 / 4)
    (hℓ : 16 * Real.exp 1 ^ 2 ≤ (L : ℝ) ^ (((d : ℝ) - α) * ℓ)) :
    (∀ β : ℝ≥0, 0 < β → chi (intensityProfile J β) 0 < ⊤ → ∀ n : ℕ,
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
          (finite_level_ball n).toFinset : ℝ) ^ 2 <
        (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / β *
          (L : ℝ) ^ (((d : ℝ) + α) * n)) ∧
    (∀ a b : ℝ≥0, a < b → (∀ β : ℝ≥0, a < β → β < b → chi (intensityProfile J β) 0 < ⊤) →
      ∀ (n : ℕ) (β : ℝ≥0), β ≤ b →
      (tightnessScale (fun e => if e ∈ {z : ℕ →₀ (Fin d → ZMod L) |
          z.support.sup Nat.succ ≤ n}.sym2 then intensityProfile J β e else 0)
          (finite_level_ball n).toFinset : ℝ) ^ 2 ≤
        (4 / c) * (L : ℝ) ^ (((d : ℝ) + α) * ℓ) * Real.log (2 * ((L : ℝ) ^ (d * ℓ)) ^ 2) / b *
          (L : ℝ) ^ (((d : ℝ) + α) * n)) :=
  ⟨fun _ hβ hχ n => sq_tightnessScale_lt_of_chi_lt_top hL hc hα J hJt hJ hexp hℓ hβ hχ n,
    fun _ _ hab hχ n _ hβb =>
      sq_tightnessScale_le_of_chi_lt_top_on_Ioo hL hc hα J hJt hJ hexp hℓ hab hχ n hβb⟩

end PercLib.Models
