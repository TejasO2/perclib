/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-109 (issue 443), on the D-2 interface and the intensity
family `intensityProfile`. The statements follow the wiki tags 1EWX (bounds only) and MTYL.
No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Analysis.Complex.Exponential

/-!
# Normalized transitive models at small intensity

Let `J` be an intensity whose off-diagonal rows sum to exactly one, and let
`q = intensityProfile J β` with `0 < β < 1`. Writing
`Δ = ∑' u v, τ(o,u) τ(u,v) τ(v,o)` for the closed triangle at `o`:

* `chi_bounds` (1EWX): `1 + β - β²/2 ≤ χ(o) ≤ (1 - β)⁻¹`;
* `triangle_bounds` (1EWX): `1 ≤ Δ ≤ 1 + 3 m² + m³` with `m = β / (1 - β)`.

Neither bound uses transitivity: they hold at every root under the row hypothesis
alone. `chi_bounds_of_transitive` and `triangle_bounds_of_transitive` restate them with
the transitivity hypothesis of the package, which is then unused. The local Lipschitz
statement `χ' ≤ (1 - β)⁻²` of 1EWX needs MXGM (package Q-99) and is not proved here.

The deterministic core is `tsum_triangle_le`: for a nonnegative matrix that is one on the
diagonal and whose off-diagonal rows sum to at most `m`, the closed triangle at a vertex
is at most `1 + 3 m² + m³`.
-/

@[expose] public section
noncomputable section

open MeasureTheory PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal
open Classical

namespace PercLib.Models.NormalizedSmallIntensity

variable {V : Type*}

/-! ### Elementary estimates -/

/-- `1 - exp (-t) ≥ t (1 - t / 2)` for `t ≥ 0`. -/
theorem mul_one_sub_half_le_one_sub_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    t * (1 - t / 2) ≤ 1 - Real.exp (-t) := by
  have hE := Real.quadratic_le_exp_of_nonneg ht
  have hpos : 0 < 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
  have key : 1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hE hpos.le, sq_nonneg (t ^ 2)]
  have hneg : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
    calc Real.exp (-t) = Real.exp (-t) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-t) * (Real.exp t * (1 - t + t ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = 1 - t + t ^ 2 / 2 := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  nlinarith

/-- An intensity at most one opens a pair with probability at least `β (1 - β / 2) J e`. -/
theorem ofReal_mul_le_intensityProfile (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V)
    (he : J e ≤ 1) :
    ENNReal.ofReal ((β : ℝ) * (1 - (β : ℝ) / 2)) * (J e : ℝ≥0∞) ≤
      (unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0∞) := by
  have hJ : (J e : ℝ) ≤ 1 := by exact_mod_cast he
  have hJ0 : (0 : ℝ) ≤ J e := (J e).coe_nonneg
  have hβ0 : (0 : ℝ) ≤ β := β.coe_nonneg
  have hval : ((unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0) : ℝ) =
      1 - Real.exp (-((β : ℝ) * (J e : ℝ))) := by
    change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) = _
    rw [neg_mul]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul'
    (J e).coe_nonneg, hval]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_one_sub_half_le_one_sub_exp_neg (mul_nonneg hβ0 hJ0)
  have : (β : ℝ) * (1 - (β : ℝ) / 2) * (J e : ℝ) ≤
      (β : ℝ) * (J e : ℝ) * (1 - (β : ℝ) * (J e : ℝ) / 2) := by
    nlinarith [mul_nonneg hβ0 hβ0, mul_nonneg (mul_nonneg hβ0 hβ0) hJ0,
      mul_nonneg (mul_nonneg (mul_nonneg hβ0 hβ0) hJ0) (sub_nonneg.2 hJ)]
  linarith

/-! ### The deterministic triangle bound -/

/-- Picking the diagonal entry from the left. -/
theorem tsum_ite_eq_mul_left (u : V) (f : V → ℝ≥0∞) :
    ∑' v, (if u = v then (1 : ℝ≥0∞) else 0) * f v = f u := by
  rw [tsum_eq_single u (fun v hv => by simp [Ne.symm hv])]
  simp

/-- Picking the diagonal entry from the right. -/
theorem tsum_mul_ite_eq_right (o : V) (f : V → ℝ≥0∞) :
    ∑' v, f v * (if v = o then (1 : ℝ≥0∞) else 0) = f o := by
  rw [tsum_eq_single o (fun v hv => by simp [hv])]
  simp

/-- **Closed triangle of `δ + t`.** If `t` vanishes on the diagonal and its rows sum to at
most `m`, the closed triangle of `δ + t` at `o` is at most `1 + 3 m² + m³`. -/
theorem tsum_triangle_le_of_add (t : V → V → ℝ≥0∞) (m : ℝ≥0∞) (ht0 : ∀ x, t x x = 0)
    (hrow : ∀ x, ∑' y, t x y ≤ m) (o : V) :
    ∑' u, ∑' v, ((if o = u then 1 else 0) + t o u) * ((if u = v then 1 else 0) + t u v) *
      ((if v = o then 1 else 0) + t v o) ≤ 1 + 3 * m ^ 2 + m ^ 3 := by
  have hent : ∀ x y, t x y ≤ m := fun x y => (ENNReal.le_tsum y).trans (hrow x)
  -- the two-step sum from `u` back to `o`
  have hinner : ∀ u, ∑' v, ((if u = v then 1 else 0) + t u v) *
      ((if v = o then 1 else 0) + t v o) ≤ (if u = o then 1 else 0) + 2 * t u o + m ^ 2 := by
    intro u
    have hW : ∑' v, t u v * t v o ≤ m ^ 2 :=
      calc ∑' v, t u v * t v o ≤ ∑' v, t u v * m :=
            ENNReal.tsum_le_tsum fun v => by gcongr; exact hent v o
        _ = (∑' v, t u v) * m := ENNReal.tsum_mul_right
        _ ≤ m * m := by gcongr; exact hrow u
        _ = m ^ 2 := (sq m).symm
    simp_rw [add_mul, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, tsum_ite_eq_mul_left,
      tsum_ite_eq_mul_left, tsum_mul_ite_eq_right]
    calc (if u = o then (1 : ℝ≥0∞) else 0) + t u o + (t u o + ∑' v, t u v * t v o)
        ≤ (if u = o then 1 else 0) + t u o + (t u o + m ^ 2) := by gcongr
      _ = _ := by ring
  calc ∑' u, ∑' v, ((if o = u then 1 else 0) + t o u) * ((if u = v then 1 else 0) + t u v) *
        ((if v = o then 1 else 0) + t v o)
      = ∑' u, ((if o = u then 1 else 0) + t o u) * ∑' v, ((if u = v then 1 else 0) + t u v) *
          ((if v = o then 1 else 0) + t v o) := by
        simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u, ((if o = u then 1 else 0) + t o u) *
          ((if u = o then 1 else 0) + 2 * t u o + m ^ 2) :=
        ENNReal.tsum_le_tsum fun u => by gcongr; exact hinner u
    _ = ((if o = o then 1 else 0) + 2 * t o o + m ^ 2) +
          ∑' u, t o u * ((if u = o then 1 else 0) + 2 * t u o + m ^ 2) := by
        rw [← tsum_ite_eq_mul_left o (fun u => (if u = o then 1 else 0) + 2 * t u o + m ^ 2),
          ← ENNReal.tsum_add]
        exact tsum_congr fun u => by ring
    _ = (1 + 2 * t o o + m ^ 2) + (t o o + 2 * ∑' u, t o u * t u o + m ^ 2 * ∑' u, t o u) := by
        simp only [ite_true]
        congr 1
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_mul_ite_eq_right (f := fun u => t o u),
          ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 2
        all_goals first | exact tsum_congr fun u => by ring | (funext u; ring)
    _ ≤ (1 + 2 * 0 + m ^ 2) + (0 + 2 * m ^ 2 + m ^ 2 * m) := by
        rw [ht0 o]
        gcongr
        · calc ∑' u, t o u * t u o ≤ ∑' u, t o u * m :=
                ENNReal.tsum_le_tsum fun u => by gcongr; exact hent u o
            _ = (∑' u, t o u) * m := ENNReal.tsum_mul_right
            _ ≤ m * m := by gcongr; exact hrow o
            _ = m ^ 2 := (sq m).symm
        · exact hrow o
    _ = 1 + 3 * m ^ 2 + m ^ 3 := by ring

/-- **Closed triangle.** For `a` equal to one on the diagonal, with off-diagonal rows
summing to at most `m`, `∑' u v, a o u * a u v * a v o ≤ 1 + 3 m² + m³`. -/
theorem tsum_triangle_le (a : V → V → ℝ≥0∞) (m : ℝ≥0∞) (ha : ∀ x, a x x = 1)
    (hrow : ∀ x, (∑' y, if y = x then 0 else a x y) ≤ m) (o : V) :
    ∑' u, ∑' v, a o u * a u v * a v o ≤ 1 + 3 * m ^ 2 + m ^ 3 := by
  have hsplit : ∀ x y, a x y = (if x = y then 1 else 0) + (if y = x then 0 else a x y) := by
    intro x y
    by_cases h : x = y
    · subst h; simp [ha]
    · simp [h, Ne.symm h]
  have := tsum_triangle_le_of_add (fun x y => if y = x then 0 else a x y) m (by simp) hrow o
  refine Eq.trans_le ?_ this
  refine tsum_congr fun u => tsum_congr fun v => ?_
  rw [← hsplit o u, ← hsplit u v, ← hsplit v o]

/-! ### Susceptibility and triangle bounds for normalized rows -/

variable [Countable V]

/-- Below `β = 1`, `(1 - β)⁻¹ = 1 + β / (1 - β)`. -/
theorem inv_one_sub_eq_one_add (β : ℝ≥0) (hβ : β < 1) :
    (1 - (β : ℝ≥0∞))⁻¹ = 1 + (β : ℝ≥0∞) / (1 - β) := by
  have h1 : (1 - (β : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hβ)).ne'
  have h2 : (1 - (β : ℝ≥0∞)) ≠ ⊤ := by finiteness
  calc (1 - (β : ℝ≥0∞))⁻¹ = (1 - β + β) / (1 - β) := by
        rw [tsub_add_cancel_of_le (by exact_mod_cast hβ.le), one_div]
    _ = (1 - β) / (1 - β) + β / (1 - β) := (ENNReal.div_add_div_same).symm
    _ = 1 + (β : ℝ≥0∞) / (1 - β) := by rw [ENNReal.div_self h1 h2]

/-- If off-diagonal rows of `J` sum to at most one and `β < 1`, every off-diagonal row of
the two-point function sums to at most `β / (1 - β)`. -/
theorem tsum_tau_offDiag_le (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 1) (β : ℝ≥0)
    (hβ : β < 1) (x : V) :
    (∑' y, if y = x then 0 else tau (intensityProfile J β) x y) ≤ (β : ℝ≥0∞) / (1 - β) := by
  have hchi := chi_intensity_le J 1 (by simpa using hrow) β (by simpa using hβ) x
  rw [chi_eq_tsum_tau, ENNReal.tsum_eq_add_tsum_ite x, tau_self, ENNReal.coe_one, mul_one,
    inv_one_sub_eq_one_add β hβ] at hchi
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 hchi

/-- **1EWX, susceptibility bounds.** If every off-diagonal row of `J` sums to exactly one
and `0 ≤ β < 1`, then `1 + β - β²/2 ≤ χ(o) ≤ (1 - β)⁻¹` at every root. -/
theorem chi_bounds (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1) (β : ℝ≥0)
    (hβ : β < 1) (o : V) :
    ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) o ∧
      chi (intensityProfile J β) o ≤ (1 - (β : ℝ≥0∞))⁻¹ := by
  refine ⟨?_, by simpa using chi_intensity_le J 1 (fun v => (hrow v).le) β (by simpa using hβ) o⟩
  have hβ1 : (β : ℝ) < 1 := by exact_mod_cast hβ
  have hβ0 : (0 : ℝ) ≤ β := β.coe_nonneg
  have hc0 : 0 ≤ (β : ℝ) * (1 - (β : ℝ) / 2) := mul_nonneg hβ0 (by linarith)
  simp only [rowSum_def] at hrow
  have hJle : ∀ y, y ≠ o → J s(o, y) ≤ 1 := by
    intro y hy
    have h := ENNReal.le_tsum (f := fun w => if w = o then 0 else (J s(o, w) : ℝ≥0∞)) y
    simp only [hy, ite_false, hrow o] at h
    exact_mod_cast h
  calc ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2)
      = 1 + ENNReal.ofReal ((β : ℝ) * (1 - (β : ℝ) / 2)) * 1 := by
        rw [mul_one, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hc0]
        congr 1; ring
    _ = 1 + rowSum (fun e => ENNReal.ofReal ((β : ℝ) * (1 - (β : ℝ) / 2)) * (J e : ℝ≥0∞))
        o := by
        simp only [rowSum_def]
        rw [← hrow o, ← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun y => by split_ifs <;> simp
    _ ≤ 1 + rowSum (fun e => unitInterval.toENNReal (intensityProfile J β e)) o := by
        simp only [rowSum_def]
        gcongr with y
        split_ifs with hy
        · exact le_rfl
        · exact ofReal_mul_le_intensityProfile J β _ (hJle y hy)
    _ ≤ chi (intensityProfile J β) o := one_add_rowSum_le_chi _ o

/-- **1EWX, triangle bounds.** If every off-diagonal row of `J` sums to at most one and
`β < 1`, then `1 ≤ Δ ≤ 1 + 3 m² + m³` with `m = β / (1 - β)`, at every root. -/
theorem triangle_bounds (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ 1) (β : ℝ≥0)
    (hβ : β < 1) (o : V) :
    1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
        tau (intensityProfile J β) v o ∧
      ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v o ≤
        1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3 := by
  set q := intensityProfile J β
  refine ⟨?_, tsum_triangle_le (tau q) _ (tau_self q) (tsum_tau_offDiag_le J hrow β hβ) o⟩
  calc (1 : ℝ≥0∞) = tau q o o * tau q o o * tau q o o := by simp [tau_self]
    _ ≤ ∑' v, tau q o o * tau q o v * tau q v o :=
        ENNReal.le_tsum (f := fun v => tau q o o * tau q o v * tau q v o) o
    _ ≤ _ := ENNReal.le_tsum (f := fun u => ∑' v, tau q o u * tau q u v * tau q v o) o

/-- 1EWX bounds on `χ`, with the transitivity hypothesis of the package (unused). -/
theorem chi_bounds_of_transitive (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1)
    (_htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (β : ℝ≥0) (_hβ0 : 0 < β) (hβ : β < 1) (o : V) :
    ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) o ∧
      chi (intensityProfile J β) o ≤ (1 - (β : ℝ≥0∞))⁻¹ :=
  chi_bounds J hrow β hβ o

/-- 1EWX bounds on `Δ`, with the transitivity hypothesis of the package (unused). -/
theorem triangle_bounds_of_transitive (J : Sym2 V → ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1)
    (_htrans : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (β : ℝ≥0) (_hβ0 : 0 < β) (hβ : β < 1) (o : V) :
    1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
        tau (intensityProfile J β) v o ∧
      ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v o ≤
        1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3 :=
  triangle_bounds J (fun v => (hrow v).le) β hβ o

/-! ### Non-vacuity (D-5): the nearest-neighbour kernel `1/2` on `ℤ` -/

/-- The nearest-neighbour kernel of weight `1/2` on `ℤ` exists. -/
theorem exists_line_kernel :
    ∃ J : Sym2 ℤ → ℝ≥0, ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0 :=
  ⟨Sym2.lift ⟨fun a b => if |b - a| = 1 then 1 / 2 else 0, fun a b => by simp only [abs_sub_comm]⟩,
    fun _ _ => rfl⟩

/-- Every off-diagonal row of the nearest-neighbour kernel `1/2` sums to exactly one. -/
theorem line_rowSum (J : Sym2 ℤ → ℝ≥0) (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0)
    (v : ℤ) : rowSum (fun e => (J e : ℝ≥0∞)) v = 1 := by
  rw [rowSum_def, tsum_eq_sum (s := {v - 1, v + 1})]
  · rw [Finset.sum_pair (by omega)]
    simp only [hJ, show v - 1 ≠ v by omega, show v + 1 ≠ v by omega, ite_false,
      show v - 1 - v = -1 by ring, show v + 1 - v = 1 by ring, abs_neg, abs_one, ite_true]
    rw [← ENNReal.coe_add, add_halves, ENNReal.coe_one]
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    split_ifs with h
    · rfl
    · rw [hJ]
      have : |w - v| ≠ 1 := by
        intro h1
        rcases abs_eq (zero_le_one' ℤ) |>.1 h1 with h2 | h2 <;> omega
      simp [this]

/-- The nearest-neighbour kernel is transitive in the spelling of the package. -/
theorem line_transitive (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0) :
    ∀ x y : ℤ, ∃ σ : ℤ ≃ ℤ, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e := by
  intro x y
  refine ⟨Equiv.addRight (y - x), by simp, fun e => ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, Equiv.coe_addRight, hJ]
    congr 3
    ring

/-- D-5: the hypotheses of `chi_bounds_of_transitive` and `triangle_bounds_of_transitive`
hold on `ℤ` with the kernel `1/2` on nearest-neighbour pairs, for every `0 < β < 1`. -/
example (β : ℝ≥0) (hβ0 : 0 < β) (hβ : β < 1) :
    ∃ J : Sym2 ℤ → ℝ≥0,
      (ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) 0 ∧
        chi (intensityProfile J β) 0 ≤ (1 - (β : ℝ≥0∞))⁻¹) ∧
      (1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) 0 u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v 0 ∧
        ∑' u, ∑' v, tau (intensityProfile J β) 0 u * tau (intensityProfile J β) u v *
            tau (intensityProfile J β) v 0 ≤
          1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3) := by
  obtain ⟨J, hJ⟩ := exists_line_kernel
  exact ⟨J, chi_bounds_of_transitive J (fun v => by convert line_rowSum J hJ v)
      (line_transitive J hJ) β hβ0 hβ 0,
    triangle_bounds_of_transitive J (fun v => by convert line_rowSum J hJ v)
      (line_transitive J hJ) β hβ0 hβ 0⟩

end PercLib.Models.NormalizedSmallIntensity
