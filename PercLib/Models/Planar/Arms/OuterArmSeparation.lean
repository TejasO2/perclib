/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (Theorem 11, separation of arms, at the outer
boundary) and Section 4.5 (Proposition 16, extendability).
-/
module

public import PercLib.Models.Planar.Arms.MotionPlan
public import PercLib.Models.Planar.Arms.OuterSeparation
public import PercLib.Models.Planar.Arms.QuasiMultiplicativity

/-!
# Separation of arms at the outer boundary (Theorem 11, outer half)

Nolin's separation theorem at the outer boundary of an annulus, for colour sequences without packs
and uniformly over the laws with crossing bounds: up to a constant factor, the arms of the `j`-arm
event from `B_r(z)` to `∂B_R(z)` can be required to land in prescribed windows, and they can be
chosen separated, with fences whose size is proportional to `R`. Consequences: extendability of
the outer radius, `π(r, R) ≤ C π(r, 2R)`. The file also completes the upper half of
quasi-multiplicativity for radii that may coincide.

The proof is Nolin's induction on scales, assembled from the outer separation step
(`exists_law_multiArmEvent_inter_not_separated_le`) and the motion plan
(`exists_pos_le_law_target_windows`, `exists_pos_le_law_target_windows_of_separated`):

* **The separated event with parameters proportional to the radius.** For an integer
  `n ≥ 1000 (j + 1)²`, at radius `R` the unit is `u = ⌊R / n²⌋`, the fences are `(2u, u)` and the
  separation is `2Q - 1` with `Q = (64 n + 24 j + 24) u`.
* **The window step** (`exists_pos_le_law_window_step`): the motion plan carries this event at `N`
  to the same event at any `R ∈ [2N, 8N]`, ending in prescribed windows whose margins, gaps and
  lengths are at least `(96 n + 24 j + 38) ⌊R / n²⌋`; the constant does not depend on the
  separation scale `ε` of the outer step.
* **The gluing step** (`exists_pos_le_law_glue_step`): the first gluing into windows carries the
  separated event of the outer step at `2N + 1` (separation `4 √ε N`, fences `(⌊√ε N⌋, ⌊ε N⌋)`) to
  the event with proportional parameters at `R ∈ [4N + 2, 8N + 4]`; the constant depends on `ε`.
* **The induction** (`exists_law_multiArmEvent_le_law_outerSeparated`): with `N = ⌊R / 6⌋`,
  `π(r, R) ≤ π(r, 2N + 1) ≤ P(separated at 2N + 1) + δ π(r, N)`; the window-step constant is fixed
  first, then `δ`, then `ε` and the gluing constant. Small ratios come from the one-scale lower
  bound (`exists_pos_le_law_outerSeparated`).
* **Windows.** `exists_bottom_windows` places `j` windows on the bottom side (targets of the window
  step); `IsLanding.exists_windows` places them inside the windows of landing data, so that arms
  ending there land in `window (16 R) θ η`.

All the parameters are integers; the arithmetic of the two steps is in `window_step_bounds` and the
`glue_bounds_*` lemmas.

## Main results

* `exists_law_multiArmEvent_le_law_multiArmEventIn_window`: **Theorem 11, outer half**,
  `π_σ(r, R) ≤ C P(arms from B_r(z) to ∂B_R(z) landing in window (16 R) θ η)` for `r₀ ≤ r`,
  `2r ≤ R`, `R ≤ L`.
* `exists_law_multiArmEvent_le_law_outerSeparated`: the separated form, `π_σ(r, R) ≤ C P(the arms
  can be chosen separated at ∂B_R(z) with parameters proportional to R)` for `r₀ ≤ r`, `7r ≤ R`.
* `exists_law_multiArmEvent_le_law_multiArmEvent_two_mul`: **extendability of the outer radius**,
  `π_σ(r, R) ≤ C π_σ(r, 2R)` for `r₀ ≤ r ≤ R`, `2R ≤ L`.
* `law_multiArmEvent_le_mul_of_le`: **upper half of quasi-multiplicativity** for all
  `j ≤ r₁ ≤ r₂ ≤ r₃` and every law (`C = 1`), from `law_multiArmEvent_le_mul` and
  `multiArmEvent_self_eq_univ` (the arm event across an empty annulus is everything for `j ≤ r`).
* `exists_pos_le_law_window_step`, `exists_pos_le_law_window_step_landing`,
  `exists_pos_le_law_glue_step`, `exists_pos_le_law_outerSeparated`: the steps.
* `IsLanding.exists_core`, `IsLanding.exists_windows`, `exists_windows_of_ccw`,
  `exists_bottom_windows`: target windows.

## Implementation notes

The constants are chosen in the order of Nolin's proof: `n` (from `j` and the landing data), the
window-step constant `c_W`, `δ = min(c_W, 1) / 2`, the scale `ε` and threshold of the outer step,
the gluing constant, and `C`; the threshold `r₀` comes last. Every statement quantifies the
constants before the law `q`, the scale `L`, the centre `z` and the radii.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The window step -/

/-- **The arithmetic of the window step.** With the unit `u = ⌊N / n²⌋` at the inner radius `N`,
`u' = ⌊R / n²⌋` at the outer radius `R ∈ [2N, 8N]` and `n ≥ 1000 (j + 1)²`, the parameters of the
motion plan (`exists_pos_le_law_target_windows`) chosen in `exists_pos_le_law_window_step`
satisfy its hypotheses: bin width `u`, jog bound `2 ⌊R / n⌋ + u + 4`, fences `(2u, u)` and
`(2u', u')`, room `(64 n + 24 j + 24) u'` of the targets, and the targets need margins, gaps and
widths at most `(96 n + 24 j + 38) u'`. -/
theorem window_step_bounds {j n N R r : ℕ} (hn : 1000 * (j + 1) * (j + 1) ≤ n)
    (hN : n * (n * n) ≤ N) (hNR : 2 * N ≤ R) (hRN : R ≤ 8 * N) (hr : 2 * r + 2 ≤ N) :
    1 ≤ N / (n * n) ∧ 2 * (N / (n * n)) ≤ R / (n * n) ∧
    r + 2 * (N / (n * n)) + 1 < N ∧
    N + 12 * j * ((2 * (2 * (R / n) + N / (n * n) + 4) + 7 * (N / (n * n)) + 3 +
      2 * (12 * j) * (N / (n * n))) + 2 * (N / (n * n)) + N / (n * n) + 1) +
      n * (2 * (2 * (N / (n * n))) + N / (n * n) + 1) +
      (2 * (N / (n * n)) + 2 * (R / (n * n)) + N / (n * n) + 1) ≤ R ∧
    2 * R + 2 ≤ (32 * (n * n) + 2) * (N / (n * n)) ∧
    2 * R + 2 * n + n * (N / (n * n)) ≤ n * (2 * (R / n) + N / (n * n) + 4) ∧
    2 * (2 * (2 * (R / n) + N / (n * n) + 4) + 7 * (N / (n * n)) + 3 +
      2 * (12 * j) * (N / (n * n))) + 4 * (N / (n * n)) + 2 + 1 ≤
      2 * ((64 * n + 24 * j + 24) * (N / (n * n))) ∧
    (2 * (2 * (R / n) + N / (n * n) + 4) + 7 * (N / (n * n)) + 3) +
      (64 * n + 24 * j + 24) * (R / (n * n)) + 2 * (N / (n * n)) + 2 * (R / (n * n)) +
      N / (n * n) + 1 ≤ (96 * n + 24 * j + 38) * (R / (n * n)) ∧
    n + (2 * (12 * j) + 2 * n + 3) * (N / (n * n)) ≤ (96 * n + 24 * j + 38) * (R / (n * n)) ∧
    N / (n * n) + 2 * (2 * (N / (n * n))) + 2 * (R / (n * n)) + 3 ≤
      (64 * n + 24 * j + 24) * (R / (n * n)) := by
  obtain ⟨u, hu⟩ : ∃ u, u = N / (n * n) := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' = R / (n * n) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = R / n := ⟨_, rfl⟩
  rw [← hu, ← hu', ← hX]
  have hn1 : 1000 ≤ n := by nlinarith
  have hnn : 0 < n * n := by positivity
  have hun : n ≤ u := by rw [hu, Nat.le_div_iff_mul_le hnn]; linarith
  have hNu : n * n * u ≤ N := by rw [hu, mul_comm]; exact Nat.div_mul_le_self N (n * n)
  have hNu' : N < n * n * (u + 1) := by
    have := Nat.lt_div_mul_add (a := N) hnn
    rw [← hu] at this; linarith
  have hRu' : R < n * n * (u' + 1) := by
    have := Nat.lt_div_mul_add (a := R) hnn
    rw [← hu'] at this; linarith
  have hRX : n * X ≤ R := by rw [hX, mul_comm]; exact Nat.div_mul_le_self R n
  have hRX' : R < n * (X + 1) := by
    have := Nat.lt_div_mul_add (a := R) (by omega : 0 < n)
    rw [← hX] at this; linarith
  have hRu : n * n * u' ≤ R := by rw [hu', mul_comm]; exact Nat.div_mul_le_self R (n * n)
  have h2u : 2 * u ≤ u' := by
    rw [hu', Nat.le_div_iff_mul_le hnn]; nlinarith
  have hXu' : X + 1 ≤ n * (u' + 1) := by
    by_contra h; push Not at h
    have : n * (n * (u' + 1)) ≤ n * X := Nat.mul_le_mul_left n (by omega)
    nlinarith
  have hXu : X + 1 ≤ 8 * (n * u) + 8 * n := by
    by_contra h; push Not at h
    have : n * (8 * (n * u) + 8 * n) ≤ n * X := Nat.mul_le_mul_left n (by omega)
    nlinarith
  have hu1 : 1 ≤ u := le_trans (by omega) hun
  have hu'1 : 1 ≤ u' := by omega
  have hnu : n ≤ n * u := Nat.le_mul_of_pos_right n hu1
  have hnu' : n ≤ n * u' := Nat.le_mul_of_pos_right n hu'1
  have hnnu : n * n ≤ n * n * u := Nat.le_mul_of_pos_right _ hu1
  have h8u : 8 * u ≤ n * n * u := Nat.mul_le_mul_right u (by nlinarith)
  refine ⟨hu1, h2u, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hjX : j * X ≤ j * (8 * (n * u) + 8 * n) := Nat.mul_le_mul_left j (by omega)
    have hbig : 1000 * (j + 1) * (j + 1) * (n * u) ≤ n * (n * u) := Nat.mul_le_mul_right _ hn
    have e1 : n * (n * u) = n * n * u := by ring
    have hju : j * u ≤ j * (n * u) := Nat.mul_le_mul_left j (by nlinarith)
    have hjn : j * n ≤ j * (n * u) := Nat.mul_le_mul_left j hnu
    have hjju : j * (j * u) ≤ j * (j * (n * u)) := Nat.mul_le_mul_left j hju
    have hu8 : u' ≤ 8 * u + 7 := by
      by_contra h; push Not at h
      have : n * n * (8 * u + 8) ≤ n * n * u' := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have hjnu : j ≤ j * (n * u) := Nat.le_mul_of_pos_right j (by positivity)
    have hunu : u ≤ n * u := Nat.le_mul_of_pos_left u (by omega)
    have e2 : j * (8 * (n * u) + 8 * n) = 8 * (j * (n * u)) + 8 * (j * n) := by ring
    have e3 : 1000 * (j + 1) * (j + 1) * (n * u) =
        1000 * (j * (j * (n * u))) + 2000 * (j * (n * u)) + 1000 * (n * u) := by ring
    have z1 := Nat.zero_le (j * (j * (n * u)))
    have z2 := Nat.zero_le (j * (n * u))
    have z3 := Nat.zero_le (j * X)
    have z4 := Nat.zero_le (j * u)
    have z5 := Nat.zero_le (j * (j * u))
    linarith
  · have z1 := Nat.zero_le (n * n * u)
    linarith
  · have : n * (X + 1) = n * X + n := by ring
    linarith
  · have z1 := Nat.zero_le (j * u)
    linarith
  · have : n * (u' + 1) = n * u' + n := by ring
    have z1 := Nat.zero_le (j * u')
    linarith
  · have h1 : j * (2 * u) ≤ j * u' := Nat.mul_le_mul_left j h2u
    have h2 : n * (2 * u) ≤ n * u' := Nat.mul_le_mul_left n h2u
    have z1 := Nat.zero_le (j * u)
    linarith
  · have z1 := Nat.zero_le (n * u')
    have z2 := Nat.zero_le (j * u')
    linarith

/-- **The window step** (the motion plan between two scales of the separated event with
parameters proportional to the radius). For a colour sequence `σ` without packs and
`n ≥ 1000 (j + 1)²` there is `c₀ > 0` such that for every law with crossing bounds `c` up to
scale `L`: arms separated at the outer boundary of `B_N(z)` at scale `2 Q - 1` with fences
`(2u, u)`, where `u = ⌊N / n²⌋` and `Q = (64 n + 24 j + 24) u`, are carried to arms to
`∂B_R(z)`, `2N ≤ R ≤ 8N`, separated in the same way at `R` (with `u' = ⌊R / n²⌋`) and ending in
prescribed windows whose margins from the corners, gaps and lengths are at least
`(96 n + 24 j + 38) u'`, in the counterclockwise order of the arms: `c₀ P(separated at N) ≤
P(separated at R, ends in the windows)`. The constant depends only on `σ`, `c` and `n`. -/
theorem exists_pos_le_law_window_step {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {n : ℕ}
    (hn : 1000 * (j + 1) * (j + 1) ≤ n) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N R : ℕ) (tT : Fin j → Fin 4)
      (lamT αT βT : Fin j → ℤ),
      n * (n * n) ≤ N → 2 * N ≤ R → R ≤ 8 * N → 2 * r + 2 ≤ N → (R : ℕ∞) ≤ L →
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R +
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ αT i ∧
        βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R) →
      (∀ i, αT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ βT i) →
      (∀ i l, i < l → tT i = tT l →
        (tT i = 1 ∨ tT i = 2 → βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          αT i)) →
      c₀ * law q (outerSeparatedArmEvent σ z r N
          ((2 * (((64 * n + 24 * j + 24) * (N / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
          (2 * (N / (n * n))) (N / (n * n))) ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
            (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R
            ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
            (2 * (R / (n * n))) (R / (n * n)) γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
            (tT i = 0 ∧ b 1 = z 1 + R ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 1 ∧ b 0 = z 0 + R ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
            (tT i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)})} := by
  obtain ⟨c₀, hc₀, hp⟩ := exists_pos_le_law_target_windows σ hσ c (32 * (n * n) + 2) n
  refine ⟨c₀, hc₀, ?_⟩
  intro q L hCB z r N R tT lamT αT βT hN hNR hRN hr hL hlamT hlamT2 hcor hwid hgap
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := window_step_bounds hn hN hNR hRN hr
  have hA : 3 ≤ 32 * (n * n) + 2 := by nlinarith
  have hp' := hp q L hCB z r N R (N / (n * n)) (2 * (N / (n * n))) (N / (n * n))
    (2 * (R / (n * n))) (R / (n * n)) (2 * (R / n) + N / (n * n) + 4)
    (N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) + 2 * (2 * (N / (n * n))) +
      2 * (N / (n * n)) + 3)
    (N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) + 2 * (2 * (N / (n * n))) +
      2 * (N / (n * n)) + 3 + 2 * (12 * j) * (N / (n * n)))
    ((64 * n + 24 * j + 24) * (R / (n * n)))
    (n + (2 * (12 * j) + 2 * n + 3) * (N / (n * n)))
    ((2 * (((64 * n + 24 * j + 24) * (N / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
    (fun _ => univ) tT lamT αT βT h1 le_rfl (by omega) (by omega) (by omega)
    (le_trans (by omega) (Nat.mul_le_mul_right _ hA))
    (le_trans (by omega) (Nat.mul_le_mul_right _ hA)) le_rfl le_rfl (by omega)
    (by
      have : 2 * (N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) + 2 * (2 * (N / (n * n))) +
          2 * (N / (n * n)) + 3 + 2 * (12 * j) * (N / (n * n))) + 4 * (N / (n * n)) + 2 + 1 ≤
          2 * ((64 * n + 24 * j + 24) * (N / (n * n))) := by linarith
      have h' : ((2 * (N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) +
          2 * (2 * (N / (n * n))) + 2 * (N / (n * n)) + 3 + 2 * (12 * j) * (N / (n * n))) +
          4 * (N / (n * n)) + 2 : ℕ) : ℤ) ≤
          2 * (((64 * n + 24 * j + 24) * (N / (n * n)) : ℕ) : ℤ) - 1 := by
        push_cast at this ⊢
        linarith
      calc _ = (((2 * (N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) +
          2 * (2 * (N / (n * n))) + 2 * (N / (n * n)) + 3 + 2 * (12 * j) * (N / (n * n))) +
          4 * (N / (n * n)) + 2 : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
        _ ≤ _ := Int.cast_le.2 h')
    h3 (by linarith) h5 hL h6 le_rfl hlamT hlamT2
    (fun i => by
      have := hcor i
      have h8' : ((N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) + 2 * (2 * (N / (n * n))) +
          2 * (N / (n * n)) + 3 + (64 * n + 24 * j + 24) * (R / (n * n)) +
          2 * (N / (n * n)) + 2 * (R / (n * n)) + N / (n * n) + 1 : ℕ) : ℤ) ≤
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) := by
        exact_mod_cast (by linarith : N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) +
          2 * (2 * (N / (n * n))) + 2 * (N / (n * n)) + 3 +
          (64 * n + 24 * j + 24) * (R / (n * n)) + 2 * (N / (n * n)) + 2 * (R / (n * n)) +
          N / (n * n) + 1 ≤ (96 * n + 24 * j + 38) * (R / (n * n)))
      push_cast at this h8' ⊢
      constructor <;> linarith)
    (fun i => by
      have := hwid i
      have h9' : ((n + (2 * (12 * j) + 2 * n + 3) * (N / (n * n)) : ℕ) : ℤ) ≤
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) := by exact_mod_cast h9
      linarith)
    (fun i l hil ht => by
      obtain ⟨hg1, hg2⟩ := hgap i l hil ht
      have h8' : ((N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) + 2 * (2 * (N / (n * n))) +
          2 * (N / (n * n)) + 3 + (64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) ≤
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) := by
        exact_mod_cast (by linarith : N / (n * n) + 2 * (2 * (R / n) + N / (n * n) + 4) +
          2 * (2 * (N / (n * n))) + 2 * (N / (n * n)) + 3 +
          (64 * n + 24 * j + 24) * (R / (n * n)) ≤ (96 * n + 24 * j + 38) * (R / (n * n)))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hg1 h
        push_cast at this h8' ⊢
        linarith
      · have := hg2 h
        push_cast at this h8' ⊢
        linarith)
  refine le_trans ?_ (hp'.trans (measure_mono fun ω ⟨a, b, γ, hγ, hd, ho, hs, hw, _⟩ =>
    ⟨a, b, γ, hγ, hd, ho, hs, hw⟩))
  exact mul_le_mul' le_rfl (measure_mono fun ω ⟨a, b, γ, hγ, hd, ho, hs⟩ =>
    ⟨a, b, γ, hγ, hd, ho, hs, fun _ => mem_univ _⟩)

/-! ### The gluing step from the outer separation step -/

section GlueBounds

variable {j n E N R P V u' X g : ℕ}

variable {j n E N R P V u' X g : ℕ}

/-- **The arithmetic of the gluing step, the bin width.** With `V = ⌊N / P⌋`, the bin width is
small against `N / E²`, `N / E` and the unit `u'` at the target radius. -/
theorem glue_bounds_one (hE : 1 ≤ E) (hP1 : 4 * (E * E) ≤ P) (hP2 : 10 * E ≤ P)
    (hP5 : 1000 * (E * (n * n)) ≤ P) (hN : 4 * P ≤ N) (hρR : 2 * (2 * N + 1) ≤ R)
    (hVP : P * V ≤ N) (hVP' : N < P * (V + 1)) (hRu' : R < n * n * (u' + 1)) :
    4 ≤ V ∧ 4 * V ≤ N / (E * E) ∧ 10 * V ≤ N / E ∧ V ≤ u' := by
  have hP : 0 < P := by omega
  have hV1 : 4 ≤ V := by
    by_contra h; push Not at h
    have : P * (V + 1) ≤ P * 4 := Nat.mul_le_mul_left P (by omega)
    omega
  have hEa : N < E * (N / E + 1) := by
    have := Nat.lt_div_mul_add (a := N) (by omega : 0 < E)
    linarith
  have hEb : N < E * E * (N / (E * E) + 1) := by
    have := Nat.lt_div_mul_add (a := N) (by positivity : 0 < E * E)
    linarith
  have hPV1 : 4 * (E * E) * V ≤ P * V := Nat.mul_le_mul_right V hP1
  have hPV2 : 10 * E * V ≤ P * V := Nat.mul_le_mul_right V hP2
  have hPV5 : 1000 * (E * (n * n)) * V ≤ P * V := Nat.mul_le_mul_right V hP5
  refine ⟨hV1, ?_, ?_, ?_⟩
  · have h1 : E * E * (4 * V) < E * E * (N / (E * E) + 1) := by
      have : E * E * (4 * V) = 4 * (E * E) * V := by ring
      linarith
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  · have h1 : E * (10 * V) < E * (N / E + 1) := by
      have : E * (10 * V) = 10 * E * V := by ring
      linarith
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  · have hnnE : n * n ≤ 1000 * (E * (n * n)) := by
      have := Nat.le_mul_of_pos_left (n * n) (show 0 < E by omega)
      omega
    by_contra h; push Not at h
    have h1 : n * n * (u' + 1) ≤ n * n * V := Nat.mul_le_mul_left _ (by omega)
    have h2 : n * n * V ≤ 1000 * (E * (n * n)) * V := Nat.mul_le_mul_right V hnnE
    linarith

/-- **The arithmetic of the gluing step, the separation**: the room needed by the motion plan
fits in the separation `4 N / E` of the outer step. -/
theorem glue_bounds_sep (hn : 1000 ≤ n) (hE : 1 ≤ E) (hP2 : 10 * E ≤ P)
    (hP3 : 4 * ((46 + 48 * j) * E) ≤ P) (hN : 4 * P ≤ N) (hRρ : R ≤ 4 * (2 * N + 1))
    (hg : g = 32 * E * n) (hVP : P * V ≤ N) (hRX : g * X ≤ R) :
    2 * (V + 2 * (2 * X + V + 4) + 10 * V + 3 + 2 * (12 * j) * V) + 20 * V + 2 ≤ 4 * (N / E) := by
  refine Nat.le_of_mul_le_mul_left (c := E) ?_ (by omega)
  have hEa : N < E * (N / E + 1) := by
    have := Nat.lt_div_mul_add (a := N) (by omega : 0 < E)
    linarith
  have hPV3 : 4 * ((46 + 48 * j) * E) * V ≤ P * V := Nat.mul_le_mul_right V hP3
  have hgEX : g * X = 32 * n * (E * X) := by rw [hg]; ring
  have hnEX : 1000 * (E * X) ≤ n * (E * X) := Nat.mul_le_mul_right _ hn
  have e1 : E * (2 * (V + 2 * (2 * X + V + 4) + 10 * V + 3 + 2 * (12 * j) * V) + 20 * V + 2) =
      46 * (E * V) + 48 * (E * (j * V)) + 8 * (E * X) + 24 * E := by ring
  have e2 : E * (4 * (N / E)) = 4 * (E * (N / E)) := by ring
  have e3 : 4 * ((46 + 48 * j) * E) * V = 184 * (E * V) + 192 * (E * (j * V)) := by ring
  have e4 : E * (N / E + 1) = E * (N / E) + E := by ring
  rw [e1, e2]
  have z1 := Nat.zero_le (E * V)
  have z2 := Nat.zero_le (E * (j * V))
  linarith

/-- **The arithmetic of the gluing step, the radius budget** from `2N + 1` to `R ≥ 4N + 2`. -/
theorem glue_bounds_budget {M : ℕ} (hn : 1000 * (j + 1) * (j + 1) ≤ n) (hE : 1 ≤ E)
    (hP4 : 4 * (12 * j * (13 + 24 * j) + 60 * j + 9 * (32 * E * n) + 13) ≤ P)
    (hP5 : 1000 * (E * (n * n)) ≤ P) (hN : 4 * P ≤ N)
    (hρR : 2 * (2 * N + 1) ≤ R) (hMN : M ≤ N)
    (hg : g = 32 * E * n) (hVP : P * V ≤ N) (hRu : n * n * u' ≤ R) (hRX : g * X ≤ R) :
    2 * N + 1 + M + 1 + 8 * V + 12 * j * ((V + 2 * (2 * X + V + 4) +
      10 * V + 3 + 2 * (12 * j) * V) + 5 * V + 1) +
      g * (9 * V + 1) + (2 * u' + 5 * V + 1) ≤ R := by
  rw [← hg] at hP4
  have hn1 : 1000 ≤ n := by nlinarith
  have hjn : 1000 * j ≤ n := by nlinarith
  have hnn6 : 1000000 ≤ n * n := by nlinarith
  have hgj : 32000 * j ≤ g := by
    have : n ≤ E * n := Nat.le_mul_of_pos_left n (by omega)
    rw [hg, mul_assoc]; omega
  have hgn : g ≤ 32 * (E * (n * n)) := by
    have : E * n ≤ E * n * n := Nat.le_mul_of_pos_right _ (by omega)
    rw [hg, mul_assoc]; rw [← mul_assoc E n n]; omega
  have hPV4 : 4 * (12 * j * (13 + 24 * j) + 60 * j + 9 * g + 13) * V ≤ P * V :=
    Nat.mul_le_mul_right V hP4
  have e1 : 4 * (12 * j * (13 + 24 * j) + 60 * j + 9 * g + 13) * V =
      864 * (j * V) + 1152 * (j * (j * V)) + 36 * (g * V) + 52 * V := by ring
  have hjX : 32000 * (j * X) ≤ g * X := by
    have := Nat.mul_le_mul_right X hgj
    linarith [show 32000 * j * X = 32000 * (j * X) by ring]
  have hu'n : 1000000 * u' ≤ n * n * u' := Nat.mul_le_mul_right u' hnn6
  have hnP : n ≤ E * (n * n) := le_trans (Nat.le_mul_of_pos_right n (by omega))
    (Nat.le_mul_of_pos_left (n * n) (by omega))
  have z1 := Nat.zero_le (j * (j * V))
  have z2 := Nat.zero_le (j * V)
  have z3 := Nat.zero_le (g * V)
  linarith

/-- **The arithmetic of the gluing step, the margins** of the target windows. -/
theorem glue_bounds_corner (hn : 1000 ≤ n) (hE : 1 ≤ E) (hV : 4 ≤ V) (hVu : V ≤ u')
    (hg : g = 32 * E * n) (hRu' : R < n * n * (u' + 1)) (hRX : g * X ≤ R) :
    (V + 2 * (2 * X + V + 4) + 10 * V + 3) + (64 * n + 24 * j + 24) * u' + 4 * V + 2 * u' +
      V + 1 ≤ (96 * n + 24 * j + 38) * u' := by
  have hgEX : g * X = 32 * n * (E * X) := by rw [hg]; ring
  have hEX : X ≤ E * X := Nat.le_mul_of_pos_left X (by omega)
  have h1 : 32 * (E * X) < n * (u' + 1) := by
    refine Nat.lt_of_mul_lt_mul_left (a := n) ?_
    have : n * (n * (u' + 1)) = n * n * (u' + 1) := by ring
    have : n * (32 * (E * X)) = 32 * n * (E * X) := by ring
    linarith
  have : n * (u' + 1) = n * u' + n := by ring
  have hnu' : n ≤ n * u' := Nat.le_mul_of_pos_right n (by omega)
  have hu'nu : u' ≤ n * u' := Nat.le_mul_of_pos_left u' (by omega)
  have z1 := Nat.zero_le (j * u')
  linarith

/-- **The arithmetic of the gluing step, the lengths** of the target windows. -/
theorem glue_bounds_width {P : ℕ} (hE : 1 ≤ E) (hV : 4 ≤ V) (hVu : V ≤ u')
    (hP5 : 1000 * (E * (n * n)) ≤ P) (hρR : 2 * (2 * N + 1) ≤ R)
    (hg : g = 32 * E * n) (hVP : P * V ≤ N) (hRu' : R < n * n * (u' + 1)) :
    g + (2 * (12 * j) + 2 * g + 3) * V ≤ (96 * n + 24 * j + 38) * u' := by
  have hPV5 : 1000 * (E * (n * n)) * V ≤ P * V := Nat.mul_le_mul_right V hP5
  have h1 : 4000 * (E * V) < u' + 1 := by
    refine Nat.lt_of_mul_lt_mul_left (a := n * n) ?_
    have : n * n * (4000 * (E * V)) = 4 * (1000 * (E * (n * n)) * V) := by ring
    linarith
  have hEV : V ≤ E * V := Nat.le_mul_of_pos_left V (by omega)
  have hEV2 : E ≤ E * V := Nat.le_mul_of_pos_right E (by omega)
  have h2 : 32 * n * (E + 2 * (E * V)) ≤ 32 * n * (3 * u') :=
    Nat.mul_le_mul_left _ (by omega)
  have e1 : 32 * n * (E + 2 * (E * V)) = 32 * (E * n) + 64 * (E * n * V) := by ring
  have e2 : 32 * n * (3 * u') = 96 * (n * u') := by ring
  have hjV : j * V ≤ j * u' := Nat.mul_le_mul_left j hVu
  have e3 : (2 * (12 * j) + 2 * g + 3) * V = 24 * (j * V) + 2 * (g * V) + 3 * V := by ring
  have e4 : g * V = 32 * (E * n * V) := by rw [hg]; ring
  have e5 : g = 32 * (E * n) := by rw [hg]; ring
  rw [e3, e4, e5]
  have z1 := Nat.zero_le (n * u')
  linarith

end GlueBounds

/-- **The scales of the outer separation step** in integers: for `0 < ε ≤ 1` and `E √ε ≥ 1`, the
fence depth `⌊√ε N⌋` lies between `⌊N / E⌋` and `N`, the fence half-length `⌊ε N⌋` between
`⌊N / E²⌋` and `⌊√ε N⌋`, and `⌊N / E⌋ ≤ √ε N`. -/
theorem div_le_floor_sqrt_mul {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {E : ℕ}
    (hE : 1 ≤ (E : ℝ) * Real.sqrt ε) (N : ℕ) :
    N / E ≤ ⌊Real.sqrt ε * N⌋₊ ∧ ⌊Real.sqrt ε * N⌋₊ ≤ N ∧ N / (E * E) ≤ ⌊ε * N⌋₊ ∧
      ⌊ε * N⌋₊ ≤ ⌊Real.sqrt ε * N⌋₊ ∧ ((N / E : ℕ) : ℝ) ≤ Real.sqrt ε * N := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hE0 : (0 : ℝ) < E := by
    by_contra h
    push Not at h
    have : (E : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg E)
    rw [this, zero_mul] at hE
    linarith
  have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  have h1 : ((N / E : ℕ) : ℝ) ≤ Real.sqrt ε * N := by
    refine (Nat.cast_div_le).trans ?_
    rw [div_le_iff₀ hE0]
    nlinarith
  have h2 : ((N / (E * E) : ℕ) : ℝ) ≤ ε * N := by
    refine (Nat.cast_div_le).trans ?_
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have h3 : (1 : ℝ) ≤ (E : ℝ) * E * ε := by
      have : ((E : ℝ) * Real.sqrt ε) * ((E : ℝ) * Real.sqrt ε) =
          (E : ℝ) * E * (Real.sqrt ε * Real.sqrt ε) := by ring
      rw [hsq] at this
      nlinarith
    have := mul_le_mul_of_nonneg_left h3 hN
    linarith
  have hεs : ε ≤ Real.sqrt ε := by nlinarith
  refine ⟨Nat.le_floor h1, Nat.floor_le_of_le (by nlinarith), Nat.le_floor h2,
    Nat.floor_le_floor (by nlinarith), h1⟩

/-- **The gluing step** (the outer separated event of the outer step carried into the
separated event with parameters proportional to the radius). For a colour sequence `σ` without
packs, `n ≥ 1000 (j + 1)²` and `0 < ε ≤ 1` there are `c₀ > 0` and `N₁` such that for every law
with crossing bounds `c` up to scale `L`: arms separated at the outer boundary of `B_{2N+1}(z)` with
the parameters of the outer separation step at scale `ε` (`s = 4 √ε N`, `M = ⌊√ε N⌋`,
`K = ⌊ε N⌋`), `N ≥ N₁`, `r < N`, are carried to arms to `∂B_R(z)`, `4N + 2 ≤ R ≤ 8N + 4`,
separated at scale `2Q - 1` with fences `(2u', u')`, where `u' = ⌊R / n²⌋` and
`Q = (64 n + 24 j + 24) u'`, ending in prescribed windows whose margins from the corners, gaps and
lengths are at least `(96 n + 24 j + 38) u'`, in the counterclockwise order of the arms. The
constants depend only on `σ`, `c`, `n` and `ε`. -/
theorem exists_pos_le_law_glue_step {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {n : ℕ}
    (hn : 1000 * (j + 1) * (j + 1) ≤ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∃ N₁ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N R : ℕ) (tT : Fin j → Fin 4)
      (lamT αT βT : Fin j → ℤ),
      N₁ ≤ N → r < N → 2 * (2 * N + 1) ≤ R → R ≤ 4 * (2 * N + 1) → (R : ℕ∞) ≤ L →
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R +
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ αT i ∧
        βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R) →
      (∀ i, αT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ βT i) →
      (∀ i l, i < l → tT i = tT l →
        (tT i = 1 ∨ tT i = 2 → βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          αT i)) →
      c₀ * law q (outerSeparatedArmEvent σ z r (2 * N + 1) (4 * Real.sqrt ε * N)
          ⌊Real.sqrt ε * N⌋₊ ⌊ε * N⌋₊) ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
            (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R
            ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
            (2 * (R / (n * n))) (R / (n * n)) γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
            (tT i = 0 ∧ b 1 = z 1 + R ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 1 ∧ b 0 = z 0 + R ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
            (tT i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)})} := by
  -- the integer scale `E ≥ 1 / √ε`
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = ⌈1 / Real.sqrt ε⌉₊ := ⟨_, rfl⟩
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hEs : 1 ≤ (E : ℝ) * Real.sqrt ε := by
    have : 1 / Real.sqrt ε ≤ E := hE ▸ Nat.le_ceil _
    rw [div_le_iff₀ hs] at this
    exact this
  have hE1 : 1 ≤ E := by
    rw [hE, Nat.one_le_ceil_iff]
    positivity
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 4 * (E * E) + 10 * E + 4 * ((46 + 48 * j) * E) +
      4 * (12 * j * (13 + 24 * j) + 60 * j + 9 * (32 * E * n) + 13) +
      1000 * (E * (n * n)) := ⟨_, rfl⟩
  have hP1 : 4 * (E * E) ≤ P := by omega
  have hP2 : 10 * E ≤ P := by omega
  have hP3 : 4 * ((46 + 48 * j) * E) ≤ P := by omega
  have hP4 : 4 * (12 * j * (13 + 24 * j) + 60 * j + 9 * (32 * E * n) + 13) ≤ P := by omega
  have hP5 : 1000 * (E * (n * n)) ≤ P := by omega
  obtain ⟨c₀, hc₀, hp⟩ :=
    exists_pos_le_law_target_windows_of_separated σ hσ c (40 * P) (32 * E * n)
  refine ⟨c₀, hc₀, 4 * P, ?_⟩
  intro q L hCB z r N R tT lamT αT βT hN hr hρR hRρ hL hlamT hlamT2 hcor hwid hgap
  have hn1 : 1000 ≤ n := by nlinarith
  have hnn : 0 < n * n := by positivity
  have hPpos : 0 < P := by omega
  have hg0 : 0 < 32 * E * n := by positivity
  have hVP : P * (N / P) ≤ N := by rw [mul_comm]; exact Nat.div_mul_le_self N P
  have hVP' : N < P * (N / P + 1) := by
    have := Nat.lt_div_mul_add (a := N) hPpos
    linarith
  have hRu : n * n * (R / (n * n)) ≤ R := by rw [mul_comm]; exact Nat.div_mul_le_self R (n * n)
  have hRu' : R < n * n * (R / (n * n) + 1) := by
    have := Nat.lt_div_mul_add (a := R) hnn
    linarith
  have hRX : 32 * E * n * (R / (32 * E * n)) ≤ R := by
    rw [mul_comm]; exact Nat.div_mul_le_self R _
  have hRX' : R < 32 * E * n * (R / (32 * E * n) + 1) := by
    have := Nat.lt_div_mul_add (a := R) hg0
    linarith
  obtain ⟨hM1, hM2, hK1, hKM, hsN⟩ := div_le_floor_sqrt_mul hε hε1 hEs N
  obtain ⟨hV4, hVK, hVM, hVu⟩ := glue_bounds_one (n := n) hE1 hP1 hP2 hP5 hN hρR hVP hVP' hRu'
  have hsep := glue_bounds_sep (j := j) hn1 hE1 hP2 hP3 hN hRρ rfl hVP hRX
  have hbud := glue_bounds_budget hn hE1 hP4 hP5 hN hρR hM2 rfl hVP hRu hRX
  have hcor' := glue_bounds_corner (j := j) hn1 hE1 hV4 hVu rfl hRu' hRX
  have hwid' := glue_bounds_width (j := j) hE1 hV4 hVu hP5 hρR rfl hVP hRu'
  have hA : 3 ≤ 40 * P := by omega
  have hp' := hp q L hCB z r (2 * N + 1) R (N / P) ⌊Real.sqrt ε * N⌋₊ ⌊ε * N⌋₊
    (2 * (R / (n * n))) (R / (n * n)) (2 * (R / (32 * E * n)) + N / P + 4)
    (N / P + 2 * (2 * (R / (32 * E * n)) + N / P + 4) + 10 * (N / P) + 3)
    (N / P + 2 * (2 * (R / (32 * E * n)) + N / P + 4) + 10 * (N / P) + 3 +
      2 * (12 * j) * (N / P))
    ((64 * n + 24 * j + 24) * (R / (n * n)))
    (32 * E * n + (2 * (12 * j) + 2 * (32 * E * n) + 3) * (N / P))
    (4 * Real.sqrt ε * N) (fun _ => univ) tT lamT αT βT (by omega) (by omega) hKM (by omega)
    (by
      have : (⌊Real.sqrt ε * N⌋₊ : ℝ) ≤ Real.sqrt ε * N := Nat.floor_le (by positivity)
      linarith)
    (by omega) (by omega) (by omega)
    (le_trans (by omega) (Nat.mul_le_mul_right _ hA)) le_rfl le_rfl
    (by
      have : 14 * (R / (n * n)) ≤ (64 * n + 24 * j + 24) * (R / (n * n)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
    (by
      have h' : ((2 * (N / P + 2 * (2 * (R / (32 * E * n)) + N / P + 4) + 10 * (N / P) + 3 +
          2 * (12 * j) * (N / P)) + 20 * (N / P) + 2 : ℕ) : ℝ) ≤ ((4 * (N / E) : ℕ) : ℝ) := by
        exact_mod_cast hsep
      push_cast at h' hsN ⊢
      linarith)
    hbud
    (by
      have e1 : 40 * P * (N / P) = 40 * (P * (N / P)) := by ring
      have : P * (N / P + 1) = P * (N / P) + P := by ring
      rw [e1]
      omega)
    hL
    (by
      have : 32 * E * n * (R / (32 * E * n) + 1) =
          32 * E * n * (R / (32 * E * n)) + 32 * E * n := by ring
      have e1 : 32 * E * n * (2 * (R / (32 * E * n)) + N / P + 4) =
          2 * (32 * E * n * (R / (32 * E * n))) + 32 * E * n * (N / P) + 4 * (32 * E * n) := by
        ring
      rw [e1]
      omega)
    le_rfl hlamT hlamT2
    (fun i => by
      have := hcor i
      have h8' : ((N / P + 2 * (2 * (R / (32 * E * n)) + N / P + 4) + 10 * (N / P) + 3 +
          (64 * n + 24 * j + 24) * (R / (n * n)) + 4 * (N / P) + 2 * (R / (n * n)) +
          N / P + 1 : ℕ) : ℤ) ≤ (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) := by
        exact_mod_cast hcor'
      push_cast at this h8' ⊢
      constructor <;> linarith)
    (fun i => by
      have := hwid i
      have h9' : ((32 * E * n + (2 * (12 * j) + 2 * (32 * E * n) + 3) * (N / P) : ℕ) : ℤ) ≤
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) := by exact_mod_cast hwid'
      linarith)
    (fun i l hil ht => by
      obtain ⟨hg1, hg2⟩ := hgap i l hil ht
      have h8' : ((N / P + 2 * (2 * (R / (32 * E * n)) + N / P + 4) + 10 * (N / P) + 3 +
          (64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) ≤
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) := by
        exact_mod_cast (by omega : N / P + 2 * (2 * (R / (32 * E * n)) + N / P + 4) +
          10 * (N / P) + 3 + (64 * n + 24 * j + 24) * (R / (n * n)) ≤
          (96 * n + 24 * j + 38) * (R / (n * n)))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hg1 h
        push_cast at this h8' ⊢
        linarith
      · have := hg2 h
        push_cast at this h8' ⊢
        linarith)
  refine le_trans ?_ (hp'.trans (measure_mono fun ω ⟨a, b, γ, hγ, hd, ho, hs, hw, _⟩ =>
    ⟨a, b, γ, hγ, hd, ho, hs, hw⟩))
  exact mul_le_mul' le_rfl (measure_mono fun ω ⟨a, b, γ, hγ, hd, ho, hs⟩ =>
    ⟨a, b, γ, hγ, hd, ho, hs, fun _ => mem_univ _⟩)

/-! ### Target windows -/

/-- **Target windows from counterclockwise coordinates.** Windows `[u i, v i]` in counterclockwise
coordinates on the sides `t i` of `B_R(z)`, at least `Y` from the corners, of length at least `Y`
and at least `Y` apart on each side in the order of the index, give windows `[αT i, βT i]` in the
coordinates of the motion plan with the same margins, lengths and gaps; the ends of arms lying in
them are the same. -/
theorem exists_windows_of_ccw {j : ℕ} (z : LatticeSite 2) (R : ℕ) (Y : ℤ) (t : Fin j → Fin 4)
    (u v : Fin j → ℤ) (hcor : ∀ i, -(R : ℤ) + Y ≤ u i ∧ v i + Y ≤ R)
    (hwid : ∀ i, u i + Y ≤ v i) (hgap : ∀ i l, i < l → t i = t l → v i + Y ≤ u l) :
    ∃ αT βT : Fin j → ℤ,
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + Y ≤ αT i ∧
        βT i + Y ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) ∧
      (∀ i, αT i + Y ≤ βT i) ∧
      (∀ i l, i < l → t i = t l → (t i = 1 ∨ t i = 2 → βT i + Y ≤ αT l) ∧
        (t i = 0 ∨ t i = 3 → βT l + Y ≤ αT i)) ∧
      ∀ i (ρ : ℕ) (col : Bool) (p : LatticeSite 2),
        ((t i = 0 ∧ p 1 = z 1 + ρ ∧ αT i ≤ p 0 ∧ p 0 ≤ βT i) ∨
          (t i = 1 ∧ p 0 = z 0 + ρ ∧ αT i ≤ p 1 ∧ p 1 ≤ βT i) ∨
          (t i = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ αT i ≤ p 0 ∧ p 0 ≤ βT i) ∨
          (t i = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ αT i ≤ p 1 ∧ p 1 ≤ βT i)) →
        ((t i = 0 ∧ p 1 = z 1 + ρ ∧ z 0 - v i ≤ p 0 ∧ p 0 ≤ z 0 - u i) ∨
          (t i = 1 ∧ p 0 = z 0 + ρ ∧ z 1 + u i ≤ p 1 ∧ p 1 ≤ z 1 + v i) ∨
          (t i = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ z 0 + u i ≤ p 0 ∧ p 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ z 1 - v i ≤ p 1 ∧ p 1 ≤ z 1 - u i)) := by
  choose αT βT hαβ hiff using fun i => exists_side_window (t i) z (u i) (v i)
  have hc := fun i => side_center_eq (hαβ i)
  refine ⟨αT, βT, fun i => ?_, fun i => ?_, fun i l hil ht => ?_,
    fun i ρ col p hp => (hiff i ρ col p).2 hp⟩
  · have := hcor i
    rcases hc i with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2] <;> constructor <;> linarith
  · have := hwid i
    rcases hc i with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2] <;> linarith
  · have hg := hgap i l hil ht
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hc i with ⟨-, h1, h2⟩ | ⟨h0, h1, h2⟩
      · rcases hc l with ⟨-, h3, h4⟩ | ⟨h0', h3, h4⟩
        · rw [h2, h3, ← ht]; linarith
        · exfalso; rw [← ht] at h0'; rcases h with h | h <;> rcases h0' with h' | h' <;>
            rw [h] at h' <;> exact absurd h' (by decide)
      · exfalso; rcases h with h | h <;> rcases h0 with h' | h' <;> rw [h] at h' <;>
          exact absurd h' (by decide)
    · rcases hc i with ⟨h0, h1, h2⟩ | ⟨-, h1, h2⟩
      · exfalso; rcases h with h | h <;> rcases h0 with h' | h' <;> rw [h] at h' <;>
          exact absurd h' (by decide)
      · rcases hc l with ⟨h0', h3, h4⟩ | ⟨-, h3, h4⟩
        · exfalso; rw [← ht] at h0'; rcases h with h | h <;> rcases h0' with h' | h' <;>
            rw [h] at h' <;> exact absurd h' (by decide)
        · rw [h1, h4, ← ht]; linarith

/-- **Windows on the bottom side.** For `n ≥ 1000 (j + 1)²`, the bottom side of
`B_R(z)` carries `j` windows of length `Y = (96 n + 24 j + 38) ⌊R / n²⌋`, at least `Y` from the
corners and `2Y` apart, in the counterclockwise order of the index: the targets of the window step
between two scales. -/
theorem exists_bottom_windows {j n : ℕ} (hn : 1000 * (j + 1) * (j + 1) ≤ n) (z : LatticeSite 2)
    (R : ℕ) :
    ∃ (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i l, i ≤ l → lamT i ≤ lamT l) ∧
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R +
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ αT i ∧
        βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R) ∧
      (∀ i, αT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ βT i) ∧
      (∀ i l, i < l → tT i = tT l →
        (tT i = 1 ∨ tT i = 2 → βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          αT i)) := by
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = (96 * n + 24 * j + 38) * (R / (n * n)) := ⟨_, rfl⟩
  rw [← hY]
  have hYR : (2 * j + 1) * Y ≤ 2 * R := by
    have h1 : (2 * j + 1) * (96 * n + 24 * j + 38) ≤ 2 * (n * n) := by nlinarith
    have h2 := Nat.mul_le_mul_right (R / (n * n)) h1
    have h3 : n * n * (R / (n * n)) ≤ R := by rw [mul_comm]; exact Nat.div_mul_le_self R _
    rw [hY]
    nlinarith
  obtain ⟨αT, βT, h1, h2, h3, -⟩ := exists_windows_of_ccw z R Y (fun _ => 2)
    (fun i => -(R : ℤ) + Y + ((i : ℕ) : ℤ) * (2 * Y))
    (fun i => -(R : ℤ) + Y + ((i : ℕ) : ℤ) * (2 * Y) + Y)
    (fun i => by
      have hi : ((i : ℕ) : ℤ) + 1 ≤ j := by exact_mod_cast i.2
      have hY0 : (0 : ℤ) ≤ Y := Nat.cast_nonneg Y
      have : (((i : ℕ) : ℤ) + 1) * (2 * Y) ≤ (j : ℤ) * (2 * Y) :=
        mul_le_mul_of_nonneg_right hi (by positivity)
      have hYR' : (2 * (j : ℤ) + 1) * Y ≤ 2 * R := by exact_mod_cast hYR
      constructor <;> nlinarith)
    (fun i => le_refl _)
    (fun i l hil _ => by
      have hil' : ((i : ℕ) : ℤ) + 1 ≤ ((l : ℕ) : ℤ) := by exact_mod_cast hil
      have hY0 : (0 : ℤ) ≤ Y := Nat.cast_nonneg Y
      have : (((i : ℕ) : ℤ) + 1) * (2 * Y) ≤ ((l : ℕ) : ℤ) * (2 * Y) :=
        mul_le_mul_of_nonneg_right hil' (by positivity)
      linarith)
  exact ⟨fun _ => 2, fun _ => 0, αT, βT, fun _ => ⟨le_rfl, by norm_num, by norm_num⟩,
    fun _ _ _ => le_rfl, h1, h2, h3⟩

/-- **Core windows inside landing data.** Landing data `(η, θ)` contain windows `[a i, a i + μ]`
of the circle (in fractions of a turn), each inside one side `c i` of the box (`c i / 4 + μ ≤ a i`,
`a i + 2μ ≤ (c i + 1) / 4`), inside the window `[θ i, θ i + η]`, at least `μ` apart in the order of
the index; the sides `c i` are then nondecreasing. -/
theorem IsLanding.exists_core {j : ℕ} {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ) :
    ∃ μ : ℚ, 0 < μ ∧ ∃ (c : Fin j → ℕ) (a : Fin j → ℚ), (∀ i, c i ≤ 3) ∧
      (∀ i, (c i : ℚ) / 4 + μ ≤ a i) ∧ (∀ i, a i + 2 * μ ≤ ((c i : ℚ) + 1) / 4) ∧
      (∀ i, θ i ≤ a i) ∧ (∀ i, a i + μ ≤ θ i + η) ∧ (∀ i l, i < l → a i + 2 * μ ≤ a l) ∧
      (∀ i l, i ≤ l → c i ≤ c l) := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℚ, ℓ = min η (1 / 8) := ⟨_, rfl⟩
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact lt_min hθ.pos (by norm_num)
  have hℓη : ℓ ≤ η := hℓ ▸ min_le_left _ _
  have hℓ8 : ℓ ≤ 1 / 8 := hℓ ▸ min_le_right _ _
  have hm0 : ∀ i, 0 ≤ 4 * (θ i + ℓ / 2) := fun i => by have := hθ.nonneg i; positivity
  obtain ⟨c, hc⟩ : ∃ c : Fin j → ℕ, ∀ i, c i = ⌊4 * (θ i + ℓ / 2)⌋₊ := ⟨_, fun _ => rfl⟩
  have hc1 : ∀ i, (c i : ℚ) ≤ 4 * (θ i + ℓ / 2) := fun i => hc i ▸ Nat.floor_le (hm0 i)
  have hc2 : ∀ i, 4 * (θ i + ℓ / 2) < (c i : ℚ) + 1 := fun i => hc i ▸ Nat.lt_floor_add_one _
  have hc3 : ∀ i, c i ≤ 3 := fun i => by
    have h1 := hθ.add_le_one i
    have : 4 * (θ i + ℓ / 2) < 4 := by linarith
    have : (c i : ℚ) < 4 := lt_of_le_of_lt (hc1 i) this
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  obtain ⟨a, ha⟩ : ∃ a : Fin j → ℚ, ∀ i, a i = if θ i + ℓ / 2 - (c i : ℚ) / 4 < 1 / 8 then
      θ i + ℓ / 2 + ℓ / 8 else θ i + ℓ / 2 - 3 * ℓ / 8 := ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, (c i : ℚ) / 4 + ℓ / 8 ≤ a i := fun i => by
    have := hc1 i
    rw [ha i]; split_ifs with h <;> linarith
  have hhi : ∀ i, a i + 2 * (ℓ / 8) ≤ ((c i : ℚ) + 1) / 4 := fun i => by
    have := hc2 i
    rw [ha i]; split_ifs with h <;> linarith
  have hθa : ∀ i, θ i ≤ a i := fun i => by
    rw [ha i]; split_ifs <;> linarith
  have haη : ∀ i, a i + ℓ / 8 ≤ θ i + η := fun i => by
    rw [ha i]; split_ifs <;> linarith
  have hgap : ∀ i l, i < l → a i + 2 * (ℓ / 8) ≤ a l := fun i l hil => by
    have h1 := hθ.add_two_mul_le i l hil
    have h2 := haη i
    have h3 := hθa l
    linarith
  refine ⟨ℓ / 8, by positivity, c, a, hc3, hlo, hhi, hθa, haη, hgap, fun i l hil => ?_⟩
  rcases hil.lt_or_eq with hil | rfl
  · by_contra h
    push Not at h
    have h' : (c l : ℚ) + 1 ≤ c i := by exact_mod_cast h
    have := hgap i l hil
    have := hlo i
    have := hhi l
    linarith
  · exact le_rfl

/-- **Target windows inside landing data.** For landing data `(η, θ)` there is `Λ > 0` such that
for every `Y` and `R ≥ Λ (Y + 4)` the boundary of `B_R(z)` carries `j` windows in the format of the
motion plan, at least `Y` from the corners, of length at least `Y`, at least `Y` apart on each side
and in the counterclockwise order of the index, such that an arm to `∂B_R(z)` ending in window `i`
(and landing at least `4` from the doubled corners) has its landing position in the window of the
landing data, `landingPos ∈ window (16 R) θ η i`. -/
theorem IsLanding.exists_windows {j : ℕ} {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ) :
    ∃ Λ : ℕ, 0 < Λ ∧ ∀ (z : LatticeSite 2) (R Y : ℕ), Λ * (Y + 4) ≤ R →
      ∃ (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
        (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) ∧
        (∀ i l, i ≤ l → lamT i ≤ lamT l) ∧
        (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R + (Y : ℤ) ≤ αT i ∧
          βT i + (Y : ℤ) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R) ∧
        (∀ i, αT i + (Y : ℤ) ≤ βT i) ∧
        (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + (Y : ℤ) ≤ αT l) ∧
          (tT i = 0 ∨ tT i = 3 → βT l + (Y : ℤ) ≤ αT i)) ∧
        ∀ (ω : Config (LatticeSite 2)) (r : ℕ) (i : Fin j) (col : Bool) (a b : LatticeSite 2)
          (γ : (zdGraph 2).Walk a b), IsArm ω col z r (z - R) (z + R) γ → r < R →
          (∀ m' : ℕ, (4 : ℤ) ≤ |landingPos (z - R) (z + R) col γ - 4 * m' * R|) →
          ((tT i = 0 ∧ b 1 = z 1 + R ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 1 ∧ b 0 = z 0 + R ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
            (tT i = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)) →
          landingPos (z - R) (z + R) col γ ∈ window (16 * R) θ η i := by
  obtain ⟨μ, hμ, c, a, hc3, hlo, hhi, hθa, haη, hgap, hmono⟩ := hθ.exists_core
  refine ⟨⌈1 / (8 * μ)⌉₊ + 1, by omega, fun z R Y hRY => ?_⟩
  -- `8 μ R ≥ Y + 4`
  have hμR : (Y : ℚ) + 4 ≤ 8 * μ * R := by
    have h1 : 1 / (8 * μ) ≤ (⌈1 / (8 * μ)⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈1 / (8 * μ)⌉₊ + 1 : ℕ) : ℚ) * ((Y : ℚ) + 4) ≤ R := by exact_mod_cast hRY
    push_cast at h2
    have h3 : (1 / (8 * μ)) * ((Y : ℚ) + 4) ≤ R := by nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h3
    linarith
  obtain ⟨t, ht⟩ : ∃ t : Fin j → Fin 4, ∀ i, t i = if c i = 0 then 2 else if c i = 1 then 1 else
      if c i = 2 then 0 else 3 := ⟨_, fun _ => rfl⟩
  have htc : ∀ i, (((c i : ℕ) : ℤ) + ((t i : ℕ) : ℤ)) % 4 = 2 := fun i => by
    have h3 := hc3 i
    rw [ht i]
    obtain ⟨k, hk⟩ : ∃ k, k = c i := ⟨_, rfl⟩
    rw [← hk] at h3 ⊢
    interval_cases k <;> decide
  have htinj : ∀ i l, t i = t l → c i = c l := fun i l h => by
    have h1 := htc i
    have h2 := htc l
    rw [h] at h1
    have := hc3 i
    have := hc3 l
    omega
  obtain ⟨u, hu⟩ : ∃ u : Fin j → ℤ, ∀ i, u i = ⌈(8 * a i - 2 * c i - 1) * R⌉ + 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin j → ℤ, ∀ i, v i = ⌊(8 * (a i + μ) - 2 * c i - 1) * R⌋ - 1 :=
    ⟨_, fun _ => rfl⟩
  have hu1 : ∀ i, (8 * a i - 2 * c i - 1) * R + 1 ≤ (u i : ℚ) := fun i => by
    rw [hu i]; push_cast; linarith [Int.le_ceil ((8 * a i - 2 * c i - 1) * R)]
  have hu2 : ∀ i, (u i : ℚ) < (8 * a i - 2 * c i - 1) * R + 2 := fun i => by
    rw [hu i]; push_cast; linarith [Int.ceil_lt_add_one ((8 * a i - 2 * c i - 1) * (R : ℚ))]
  have hv1 : ∀ i, (v i : ℚ) ≤ (8 * (a i + μ) - 2 * c i - 1) * R - 1 := fun i => by
    rw [hv i]; push_cast; linarith [Int.floor_le ((8 * (a i + μ) - 2 * c i - 1) * (R : ℚ))]
  have hv2 : ∀ i, (8 * (a i + μ) - 2 * c i - 1) * R - 2 < (v i : ℚ) := fun i => by
    rw [hv i]; push_cast
    linarith [Int.lt_floor_add_one ((8 * (a i + μ) - 2 * c i - 1) * (R : ℚ))]
  have hR0 : (0 : ℚ) ≤ R := Nat.cast_nonneg R
  obtain ⟨αT, βT, h1, h2, h3, hiff⟩ := exists_windows_of_ccw z R Y t u v
    (fun i => by
      have e1 := hlo i
      have e2 := hhi i
      have k1 := hu1 i
      have k2 := hv1 i
      have m1 : 8 * μ * R ≤ 8 * (a i - (c i : ℚ) / 4 - 0) * R := by
        exact mul_le_mul_of_nonneg_right (by linarith) hR0
      have m2 : 8 * μ * R ≤ 8 * (((c i : ℚ) + 1) / 4 - (a i + μ)) * R := by
        exact mul_le_mul_of_nonneg_right (by linarith) hR0
      constructor
      · have : (-(R : ℤ) + Y : ℚ) ≤ u i := by push_cast; nlinarith
        exact_mod_cast this
      · have : (v i + Y : ℚ) ≤ (R : ℤ) := by push_cast; nlinarith
        exact_mod_cast this)
    (fun i => by
      have k1 := hu2 i
      have k2 := hv2 i
      have : (u i + Y : ℚ) < v i := by nlinarith
      have : u i + Y < v i := by exact_mod_cast this
      omega)
    (fun i l hil htl => by
      have hcl := htinj i l htl
      have k1 := hv1 i
      have k2 := hu1 l
      have g := hgap i l hil
      have m1 : 8 * μ * R ≤ 8 * (a l - (a i + μ)) * R :=
        mul_le_mul_of_nonneg_right (by linarith) hR0
      rw [← hcl] at k2
      have : (v i + Y : ℚ) ≤ u l := by nlinarith
      exact_mod_cast this)
  refine ⟨t, fun i => (c i : ℤ), αT, βT,
    fun i => ⟨by positivity, by have := hc3 i; dsimp only; omega, htc i⟩,
    fun i l hil => by have := hmono i l hil; dsimp only; omega, h1, h2, h3, ?_⟩
  intro ω r i col a' b γ hγ hrR hcor hw
  obtain ⟨c', x, hc'0, hc'3, hc't, hL, -, -, hx1, hx2, -, -⟩ :=
    hγ.exists_landingPos_eq_of_window hrR (le_refl 4) hcor (hiff i R col b hw)
  have hcc : c' = (c i : ℤ) := by
    have := htc i
    have := hc3 i
    omega
  rw [hcc] at hL
  have k1 := hu1 i
  have k2 := hv1 i
  have hx1' : (2 * u i + 2 * R - 1 : ℚ) ≤ x := by exact_mod_cast hx1
  have hx2' : (x : ℚ) ≤ 2 * v i + 2 * R + 1 := by exact_mod_cast hx2
  have hL' : (landingPos (z - R) (z + R) col γ : ℚ) = 4 * R * c i + x := by
    rw [hL]; push_cast; ring
  have ha1 := hθa i
  have ha2 := haη i
  refine ⟨?_, ?_⟩
  · rw [hL']
    push_cast
    have : θ i * (16 * R) ≤ a i * (16 * R) := mul_le_mul_of_nonneg_right ha1 (by positivity)
    nlinarith
  · rw [hL']
    push_cast
    have : (a i + μ) * (16 * R) ≤ (θ i + η) * (16 * R) :=
      mul_le_mul_of_nonneg_right ha2 (by positivity)
    nlinarith

/-! ### Theorem 11, outer half: arms separated at the outer boundary -/

/-- **Separated arms at one scale** (the a priori lower bound for the separated event with
parameters proportional to the radius, for annuli of bounded aspect ratio). For a colour sequence
`σ` without packs and `n ≥ 1000 (j + 1)²` there are `c₁ > 0` and `r₀` such that for every law with
crossing bounds `c` up to scale `L`, `r₀ ≤ r` and `7r ≤ R ≤ 48r`, `R ≤ L`: the arms from `B_r(z)`
to `∂B_R(z)` are separated at scale `2Q - 1` with fences `(2u, u)` (`u = ⌊R / n²⌋`,
`Q = (64 n + 24 j + 24) u`) with probability at least `c₁`. Proof: the one-scale lower bound
(`exists_pos_le_law_multiArmEvent`) at `ρ = 2 ⌊R / 6⌋ + 1`, the outer separation step at `ρ` with
`δ` half that bound, and the gluing step from `ρ` to `R` into windows on the bottom side. -/
theorem exists_pos_le_law_outerSeparated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {n : ℕ}
    (hn : 1000 * (j + 1) * (j + 1) ≤ n) :
    ∃ c₁ : ℝ≥0∞, 0 < c₁ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 7 * r ≤ R →
      R ≤ 48 * r → (R : ℕ∞) ≤ L →
      c₁ ≤ law q (outerSeparatedArmEvent σ z r R
          ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
          (2 * (R / (n * n))) (R / (n * n))) := by
  obtain ⟨c₀, hc₀, hone⟩ := exists_pos_le_law_multiArmEvent σ c 17
  -- normalise the one-scale constant to `(0, 1]`
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, d = min c₀ 1 := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ lt_min hc₀ one_pos
  have hd1 : d ≤ 1 := hd ▸ min_le_right _ _
  have hdc : d ≤ c₀ := hd ▸ min_le_left _ _
  have hdt : d / 2 ≠ ⊤ := ENNReal.div_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hd1)
    (by norm_num)
  obtain ⟨ε, hε, hε1, N₀, hstep⟩ := exists_law_multiArmEvent_inter_not_separated_le σ hσ c
    (ENNReal.half_pos hd0.ne')
  obtain ⟨cG, hcG, N₁, hglue⟩ := exists_pos_le_law_glue_step σ hσ c hn hε hε1
  obtain ⟨e, he⟩ : ∃ e : ℝ≥0∞, e = min cG 1 := ⟨_, rfl⟩
  have he0 : 0 < e := he ▸ lt_min hcG one_pos
  have heG : e ≤ cG := he ▸ min_le_left _ _
  refine ⟨e * (d / 2), ENNReal.mul_pos he0.ne' (ENNReal.half_pos hd0.ne').ne',
    max (max 7 (4 * j)) (max N₀ N₁), ?_⟩
  intro q L hCB z r R hr hR hR48 hRL
  have h7 : 7 ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hj : 4 * j ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hN₀ : N₀ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr)
  have hN₁ : N₁ ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr)
  have hrN : r + 1 ≤ R / 6 := by omega
  have hNL : ((R / 6 : ℕ) : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R / 6 ≤ R)) hRL
  have hρL : ((2 * (R / 6) + 1 : ℕ) : ℕ∞) ≤ L :=
    le_trans (by exact_mod_cast (by omega : 2 * (R / 6) + 1 ≤ R)) hRL
  -- the one-scale bound at `ρ = 2 ⌊R / 6⌋ + 1`
  have h1 : d ≤ law q (multiArmEvent σ z r (2 * (R / 6) + 1)) :=
    hdc.trans (hone q L hCB z r (2 * (R / 6) + 1) hj (by omega) (by omega) hρL)
  -- the outer separation step at `ρ`
  have h2 := hstep q L hCB z r (R / 6) (2 * (R / 6) + 1) rfl (by omega) (by omega) hNL
  obtain ⟨S, hS⟩ : ∃ S : Set (Config (LatticeSite 2)), S = outerSeparatedArmEvent σ z r
      (2 * (R / 6) + 1) (4 * Real.sqrt ε * (R / 6 : ℕ)) ⌊Real.sqrt ε * (R / 6 : ℕ)⌋₊
      ⌊ε * (R / 6 : ℕ)⌋₊ := ⟨_, rfl⟩
  rw [← hS] at h2
  have h3 : law q (multiArmEvent σ z r (2 * (R / 6) + 1)) ≤ law q S + d / 2 := by
    calc law q (multiArmEvent σ z r (2 * (R / 6) + 1))
        ≤ law q (S ∪ (multiArmEvent σ z r (2 * (R / 6) + 1) \ S)) :=
          measure_mono fun ω hω => by
            by_cases h : ω ∈ S
            · exact Or.inl h
            · exact Or.inr ⟨hω, h⟩
      _ ≤ law q S + law q (multiArmEvent σ z r (2 * (R / 6) + 1) \ S) := measure_union_le _ _
      _ ≤ law q S + d / 2 := by
          gcongr
          exact h2.trans ((mul_le_mul' le_rfl prob_le_one).trans (by rw [mul_one]))
  have h4 : d / 2 ≤ law q S := by
    have : d / 2 + d / 2 ≤ law q S + d / 2 := by rw [ENNReal.add_halves]; exact h1.trans h3
    exact (ENNReal.add_le_add_iff_right hdt).1 this
  -- the gluing step from `ρ` to `R`, into windows on the bottom side
  obtain ⟨tT, lamT, αT, βT, hw1, hw2, hw3, hw4, hw5⟩ := exists_bottom_windows hn z R
  have h5 := hglue q L hCB z r (R / 6) R tT lamT αT βT (by omega) (by omega) (by omega)
    (by omega) hRL hw1 hw2 hw3 hw4 hw5
  rw [← hS] at h5
  refine (mul_le_mul' heG h4).trans (h5.trans (measure_mono ?_))
  rintro ω ⟨a, b, γ, hγ, hd, ho, hs, -⟩
  exact ⟨a, b, γ, hγ, hd, ho, hs⟩

/-- **Theorem 11, outer half, separated form** (Nolin, Theorem 11, the external extremities). For a
colour sequence `σ` without packs and `n ≥ 1000 (j + 1)²` there are `C < ⊤` and `r₀` such that for
every law with crossing bounds `c` up to scale `L`, `r₀ ≤ r`, `7r ≤ R ≤ L`: the probability of the
`j`-arm event from `B_r(z)` to `∂B_R(z)` is at most `C` times the probability that the arms can be
chosen separated at the outer boundary at scale `2Q - 1` with fences `(2u, u)`, where
`u = ⌊R / n²⌋` and `Q = (64 n + 24 j + 24) u`: separation, fences and their room are proportional
to `R`.

Proof (Nolin's induction on scales): with `N = ⌊R / 6⌋` and `ρ = 2N + 1`,
`π(r, R) ≤ π(r, ρ) ≤ P(separated at ρ, scale ε) + δ π(r, N)` by the outer separation step; the
first term is at most `c_G⁻¹ P(separated at R)` by the gluing step, and by induction and the
window step from `N` to `R`, `δ π(r, N) ≤ δ C c_W⁻¹ P(separated at R) ≤ (C / 2) P(separated at R)`
once `δ ≤ c_W / 2`. The window-step constant `c_W` does not depend on `ε`; `δ` is chosen after
it, `ε` after `δ` (`exists_law_multiArmEvent_inter_not_separated_le`), and the gluing constant
`c_G` after `ε`. Small ratios `R < 42r + 42` are covered by `exists_pos_le_law_outerSeparated`. -/
theorem exists_law_multiArmEvent_le_law_outerSeparated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {n : ℕ}
    (hn : 1000 * (j + 1) * (j + 1) ≤ n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 7 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤ C * law q (outerSeparatedArmEvent σ z r R
          ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
          (2 * (R / (n * n))) (R / (n * n))) := by
  obtain ⟨c₁, hc₁, rB, hbase⟩ := exists_pos_le_law_outerSeparated σ hσ c hn
  obtain ⟨cW, hcW, hwin⟩ := exists_pos_le_law_window_step σ hσ c hn
  obtain ⟨w, hw⟩ : ∃ w : ℝ≥0∞, w = min cW 1 := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := (hw ▸ lt_min hcW one_pos).ne'
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ min_le_right _ _)
  have hwc : w ≤ cW := hw ▸ min_le_left _ _
  obtain ⟨ε, hε, hε1, N₀, hstep⟩ := exists_law_multiArmEvent_inter_not_separated_le σ hσ c
    (ENNReal.half_pos hw0)
  obtain ⟨cG, hcG, N₁, hglue⟩ := exists_pos_le_law_glue_step σ hσ c hn hε hε1
  obtain ⟨g, hg⟩ : ∃ g : ℝ≥0∞, g = min cG 1 := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := (hg ▸ lt_min hcG one_pos).ne'
  have hgt : g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hg ▸ min_le_right _ _)
  have hgc : g ≤ cG := hg ▸ min_le_left _ _
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0∞, D = g⁻¹ + c₁⁻¹ := ⟨_, rfl⟩
  have hDt : D ≠ ⊤ := hD ▸ ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hg0,
    ENNReal.inv_ne_top.2 hc₁.ne'⟩
  refine ⟨2 * D, ENNReal.mul_ne_top ENNReal.ofNat_ne_top hDt,
    max (max (rB + 7) (n * (n * n))) (max N₀ N₁), ?_⟩
  intro q L hCB z r R₀ hr
  have hrB : rB ≤ r := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr); omega
  have h7 : 7 ≤ r := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr); omega
  have hn3 : n * (n * n) ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hN₀ : N₀ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr)
  have hN₁ : N₁ ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr)
  induction R₀ using Nat.strong_induction_on with
  | _ R ih =>
  intro hR hRL
  by_cases hsmall : R < 42 * r + 42
  · -- small ratios: the one-scale bound for the separated event
    have hb := hbase q L hCB z r R hrB hR (by omega) hRL
    have hc₁t : c₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hb.trans prob_le_one)
    calc law q (multiArmEvent σ z r R) ≤ 1 := prob_le_one
      _ = c₁⁻¹ * c₁ := (ENNReal.inv_mul_cancel hc₁.ne' hc₁t).symm
      _ ≤ (2 * D) * law q _ := by
          refine mul_le_mul' ?_ hb
          rw [hD, two_mul]
          exact le_trans le_add_self (add_le_add le_rfl le_add_self)
  · -- the induction step at `N = ⌊R / 6⌋`, `ρ = 2N + 1`
    have hNL : ((R / 6 : ℕ) : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R / 6 ≤ R)) hRL
    obtain ⟨S, hS⟩ : ∃ S : Set (Config (LatticeSite 2)), S = outerSeparatedArmEvent σ z r
        (2 * (R / 6) + 1) (4 * Real.sqrt ε * (R / 6 : ℕ)) ⌊Real.sqrt ε * (R / 6 : ℕ)⌋₊
        ⌊ε * (R / 6 : ℕ)⌋₊ := ⟨_, rfl⟩
    have h2 := hstep q L hCB z r (R / 6) (2 * (R / 6) + 1) rfl (by omega) (by omega) hNL
    rw [← hS] at h2
    -- the gluing step from `ρ` to `R`
    obtain ⟨tT, lamT, αT, βT, hw1, hw2, hw3, hw4, hw5⟩ := exists_bottom_windows hn z R
    have hG := hglue q L hCB z r (R / 6) R tT lamT αT βT (by omega) (by omega) (by omega)
      (by omega) hRL hw1 hw2 hw3 hw4 hw5
    rw [← hS] at hG
    obtain ⟨B, hB⟩ : ∃ B : Set (Config (LatticeSite 2)), B = outerSeparatedArmEvent σ z r R
        ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
        (2 * (R / (n * n))) (R / (n * n)) := ⟨_, rfl⟩
    have hGB : g * law q S ≤ law q B := by
      refine (mul_le_mul' hgc le_rfl).trans (hG.trans (measure_mono ?_))
      rw [hB]
      rintro ω ⟨a, b, γ, hγ, hd, ho, hs, -⟩
      exact ⟨a, b, γ, hγ, hd, ho, hs⟩
    -- the window step from `N` to `R`
    have hW := hwin q L hCB z r (R / 6) R tT lamT αT βT (by omega) (by omega) (by omega)
      (by omega) hRL hw1 hw2 hw3 hw4 hw5
    have hWB : w * law q (outerSeparatedArmEvent σ z r (R / 6)
        ((2 * (((64 * n + 24 * j + 24) * (R / 6 / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
        (2 * (R / 6 / (n * n))) (R / 6 / (n * n))) ≤ law q B := by
      refine (mul_le_mul' hwc le_rfl).trans (hW.trans (measure_mono ?_))
      rw [hB]
      rintro ω ⟨a, b, γ, hγ, hd, ho, hs, -⟩
      exact ⟨a, b, γ, hγ, hd, ho, hs⟩
    -- the induction hypothesis at `N`
    have hih := ih (R / 6) (by omega) (by omega) hNL
    have hinv : ∀ {x y : ℝ≥0∞} {e : ℝ≥0∞}, e ≠ 0 → e ≠ ⊤ → e * x ≤ y → x ≤ e⁻¹ * y :=
      fun {x y e} he0 het h => by
        calc x = e⁻¹ * (e * x) := by rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
          _ ≤ e⁻¹ * y := mul_le_mul' le_rfl h
    rw [← hB]
    calc law q (multiArmEvent σ z r R)
        ≤ law q (multiArmEvent σ z r (2 * (R / 6) + 1)) :=
          measure_mono (multiArmEvent_subset_of_le le_rfl (by omega) (by omega))
      _ ≤ law q (S ∪ (multiArmEvent σ z r (2 * (R / 6) + 1) \ S)) :=
          measure_mono fun ω hω => by
            by_cases h : ω ∈ S
            · exact Or.inl h
            · exact Or.inr ⟨hω, h⟩
      _ ≤ law q S + law q (multiArmEvent σ z r (2 * (R / 6) + 1) \ S) := measure_union_le _ _
      _ ≤ g⁻¹ * law q B + w / 2 * (2 * D * (w⁻¹ * law q B)) := by
          refine add_le_add (hinv hg0 hgt hGB) (h2.trans (mul_le_mul' le_rfl ?_))
          exact hih.trans (mul_le_mul' le_rfl (hinv hw0 hwt hWB))
      _ = g⁻¹ * law q B + (2⁻¹ * 2) * (w * w⁻¹) * D * law q B := by
          rw [ENNReal.div_eq_inv_mul]; ring
      _ = g⁻¹ * law q B + D * law q B := by
          rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
            ENNReal.mul_inv_cancel hw0 hwt, one_mul, one_mul]
      _ ≤ D * law q B + D * law q B := by
          gcongr
          rw [hD]
          exact le_self_add
      _ = 2 * D * law q B := by ring

/-- **The window step into the windows of landing data**: with `n ≥ 1000 (j + 1)² (Λ + 1)`, where
`Λ` is given by `IsLanding.exists_windows`, separated arms at `N` are carried to arms to `∂B_R(z)`,
`2N ≤ R ≤ 8N`, landing in the windows `window (16 R) θ η`, at the cost of the window step. -/
theorem exists_pos_le_law_window_step_landing {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ)
    (c : ℕ → ℝ≥0∞) :
    ∃ n : ℕ, 1000 * (j + 1) * (j + 1) ≤ n ∧ ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ c₀ ≠ ⊤ ∧
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N R : ℕ),
      n * (n * n) ≤ N → 2 * N ≤ R → R ≤ 8 * N → 2 * r + 2 ≤ N → (R : ℕ∞) ≤ L →
      c₀ * law q (outerSeparatedArmEvent σ z r N
          ((2 * (((64 * n + 24 * j + 24) * (N / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
          (2 * (N / (n * n))) (N / (n * n))) ≤
        law q (multiArmEventIn σ z r R (fun _ => univ) (window (16 * R) θ η)) := by
  obtain ⟨Λ, hΛ, hwinθ⟩ := hθ.exists_windows
  refine ⟨1000 * (j + 1) * (j + 1) * (Λ + 1), Nat.le_mul_of_pos_right _ (by omega), ?_⟩
  obtain ⟨n, hn'⟩ : ∃ n, n = 1000 * (j + 1) * (j + 1) * (Λ + 1) := ⟨_, rfl⟩
  rw [← hn']
  have hn : 1000 * (j + 1) * (j + 1) ≤ n := by
    rw [hn']; exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨cW, hcW, hwin⟩ := exists_pos_le_law_window_step σ hσ c hn
  refine ⟨min cW 1, lt_min hcW one_pos, ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _),
    fun q L hCB z r N R hN hNR hRN hr hRL => ?_⟩
  have hΛn : Λ * (96 * n + 24 * j + 42) ≤ n * n := by
    have h1 : 24 * j + 42 ≤ n := by nlinarith
    have h2 : 1000 * (Λ + 1) ≤ n := by
      rw [hn']
      have : 1 ≤ (j + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      calc 1000 * (Λ + 1) = 1000 * 1 * (Λ + 1) := by ring
        _ ≤ 1000 * ((j + 1) * (j + 1)) * (Λ + 1) := by gcongr
        _ = _ := by ring
    have h3 : Λ * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    nlinarith
  have hu' : 1 ≤ R / (n * n) := by
    rw [Nat.le_div_iff_mul_le (by nlinarith)]
    have : n * n ≤ n * (n * n) := Nat.le_mul_of_pos_left _ (by nlinarith)
    omega
  have hRu : n * n * (R / (n * n)) ≤ R := by rw [mul_comm]; exact Nat.div_mul_le_self R _
  have hΛR : Λ * ((96 * n + 24 * j + 38) * (R / (n * n)) + 4) ≤ R := by
    have h1 : Λ * ((96 * n + 24 * j + 38) * (R / (n * n)) + 4) ≤
        Λ * (96 * n + 24 * j + 42) * (R / (n * n)) := by
      have : (96 * n + 24 * j + 38) * (R / (n * n)) + 4 ≤
          (96 * n + 24 * j + 42) * (R / (n * n)) := by nlinarith
      calc _ ≤ Λ * ((96 * n + 24 * j + 42) * (R / (n * n))) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have h2 := Nat.mul_le_mul_right (R / (n * n)) hΛn
    omega
  obtain ⟨tT, lamT, αT, βT, hw1, hw2, hw3, hw4, hw5, hland⟩ :=
    hwinθ z R ((96 * n + 24 * j + 38) * (R / (n * n))) hΛR
  have h := hwin q L hCB z r N R tT lamT αT βT hN hNR hRN hr hRL hw1 hw2 hw3 hw4 hw5
  refine (mul_le_mul' (min_le_left _ _) le_rfl).trans (h.trans (measure_mono ?_))
  rintro ω ⟨a, b, γ, hγ, hd, ho, hs, hw⟩
  have hrR : r < R := by omega
  refine ⟨a, b, γ, hγ, hd, fun i => ⟨mem_univ _, hland ω r i (σ i) (a i) (b i) (γ i) (hγ i) hrR
    (fun m => ?_) (hw i)⟩, ho⟩
  have h1 := hs.2.1 i m
  have hQ : (4 : ℝ) ≤ ((2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 : ℤ) : ℝ) := by
    have : 3 ≤ (64 * n + 24 * j + 24) * (R / (n * n)) := by nlinarith
    have : (3 : ℤ) ≤ (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) := by exact_mod_cast this
    have : (4 : ℤ) ≤ 2 * (((64 * n + 24 * j + 24) * (R / (n * n)) : ℕ) : ℤ) - 1 := by omega
    exact_mod_cast this
  have h2 := hQ.trans h1
  rw [← Int.cast_abs] at h2
  exact_mod_cast h2

/-- **Theorem 11, outer half** (Nolin, Theorem 11, the external extremities: arms landing in
prescribed windows). For a colour sequence `σ` without packs (`j ≤ 1` or no two cyclically
consecutive arms of the same colour) and landing data `(η, θ)` there are `C < ⊤` and `r₀` such that
for every law with crossing bounds `c` up to scale `L` and `r₀ ≤ r`, `2r ≤ R ≤ L`:
`π_σ(r, R) ≤ C P(the j arms from B_r(z) to ∂B_R(z) land in the windows window (16 R) θ η)`.

For `R ≥ 28r + 4`: `π(r, R) ≤ π(r, ⌊R / 4⌋) ≤ C₁ P(separated at ⌊R / 4⌋)` by the separated form
(`exists_law_multiArmEvent_le_law_outerSeparated`), and the window step into the windows of the
landing data. For `2r ≤ R < 28r + 4`, the event is bounded below: arms from the smaller box
`B_{⌊R / 32⌋}(z)` landing in the windows are arms from `B_r(z)` landing there
(`multiArmEventTo_subset_of_le`), and those have probability at least `c_W c₁` by the one-scale
bound for the separated event and the window step. -/
theorem exists_law_multiArmEvent_le_law_multiArmEventIn_window {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ)
    (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 2 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤
        C * law q (multiArmEventIn σ z r R (fun _ => univ) (window (16 * R) θ η)) := by
  obtain ⟨n, hn, w, hw0, hwt, hwin⟩ := exists_pos_le_law_window_step_landing σ hσ hθ c
  obtain ⟨C₁, hC₁, r₁, hsep⟩ := exists_law_multiArmEvent_le_law_outerSeparated σ hσ c hn
  obtain ⟨c₁, hc₁, rB, hbase⟩ := exists_pos_le_law_outerSeparated σ hσ c hn
  have hw0' : w ≠ 0 := hw0.ne'
  refine ⟨C₁ * w⁻¹ + (w * c₁)⁻¹,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC₁ (ENNReal.inv_ne_top.2 hw0'),
      ENNReal.inv_ne_top.2 (ENNReal.mul_pos hw0' hc₁.ne').ne'⟩,
    max (max r₁ (16 * rB + 32)) (2 * (n * (n * n)) + 64), ?_⟩
  intro q L hCB z r R hr hrR hRL
  have hr₁ : r₁ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hrB : 16 * rB + 32 ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hn3 : 2 * (n * (n * n)) + 64 ≤ r := le_trans (le_max_right _ _) hr
  have hinv : ∀ {x y : ℝ≥0∞} {e : ℝ≥0∞}, e ≠ 0 → e ≠ ⊤ → e * x ≤ y → x ≤ e⁻¹ * y :=
    fun {x y e} he0 het h => by
      calc x = e⁻¹ * (e * x) := by rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
        _ ≤ e⁻¹ * y := mul_le_mul' le_rfl h
  by_cases hbig : 28 * r + 4 ≤ R
  · -- large ratios: separation at `⌊R / 4⌋` and the window step to `R`
    have hNL : ((R / 4 : ℕ) : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R / 4 ≤ R)) hRL
    have h1 := hsep q L hCB z r (R / 4) hr₁ (by omega) hNL
    have h2 := hwin q L hCB z r (R / 4) R (by omega) (by omega) (by omega) (by omega) hRL
    calc law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent σ z r (R / 4)) :=
          measure_mono (multiArmEvent_subset_of_le le_rfl (by omega) (by omega))
      _ ≤ C₁ * (w⁻¹ * law q (multiArmEventIn σ z r R (fun _ => univ) (window (16 * R) θ η))) :=
          h1.trans (mul_le_mul' le_rfl (hinv hw0' hwt h2))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · -- small ratios: the event is bounded below
    have h1 := hbase q L hCB z (R / 32) (R / 4) (by omega) (by omega) (by omega)
      (le_trans (by exact_mod_cast (by omega : R / 4 ≤ R)) hRL)
    have h2 := hwin q L hCB z (R / 32) (R / 4) R (by omega) (by omega) (by omega) (by omega) hRL
    have h3 : multiArmEventIn σ z (R / 32) R (fun _ => univ) (window (16 * R) θ η) ⊆
        multiArmEventIn σ z r R (fun _ => univ) (window (16 * R) θ η) :=
      multiArmEventTo_subset_of_le (by omega) (Icc_subset_Icc_add_one_sub_one (by omega))
    have h4 : w * c₁ ≤ law q (multiArmEventIn σ z r R (fun _ => univ) (window (16 * R) θ η)) :=
      (mul_le_mul' le_rfl h1).trans (h2.trans (measure_mono h3))
    have hwct : w * c₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (h4.trans prob_le_one)
    calc law q (multiArmEvent σ z r R) ≤ 1 := prob_le_one
      _ = (w * c₁)⁻¹ * (w * c₁) :=
          (ENNReal.inv_mul_cancel (ENNReal.mul_pos hw0' hc₁.ne').ne' hwct).symm
      _ ≤ (C₁ * w⁻¹ + (w * c₁)⁻¹) * law q _ := mul_le_mul' le_add_self h4

/-- **Extendability, outwards** (Nolin, Proposition 16, the outer radius): for a colour sequence `σ`
without packs there are `C < ⊤` and `r₀` such that for every law with crossing bounds `c` up to
scale `L` and `r₀ ≤ r ≤ R`, `2R ≤ L`: `π_σ(r, R) ≤ C π_σ(r, 2R)`. For `R ≥ 7r` by the separated
form of Theorem 11's outer half and the window step from `R` to `2R`; for `R < 7r` by the one-scale
lower bound for `π(r, 2R)`. -/
theorem exists_law_multiArmEvent_le_law_multiArmEvent_two_mul {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → r ≤ R →
      ((2 * R : ℕ) : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤ C * law q (multiArmEvent σ z r (2 * R)) := by
  have hn : 1000 * (j + 1) * (j + 1) ≤ 1000 * (j + 1) * (j + 1) := le_rfl
  obtain ⟨C₁, hC₁, r₁, hsep⟩ := exists_law_multiArmEvent_le_law_outerSeparated σ hσ c hn
  obtain ⟨cW, hcW, hwin⟩ := exists_pos_le_law_window_step σ hσ c hn
  obtain ⟨c₂, hc₂, hone⟩ := exists_pos_le_law_multiArmEvent σ c 14
  obtain ⟨w, hw⟩ : ∃ w : ℝ≥0∞, w = min cW 1 := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := (hw ▸ lt_min hcW one_pos).ne'
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ min_le_right _ _)
  have hwc : w ≤ cW := hw ▸ min_le_left _ _
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, d = min c₂ 1 := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := (hd ▸ lt_min hc₂ one_pos).ne'
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hd ▸ min_le_right _ _)
  have hdc : d ≤ c₂ := hd ▸ min_le_left _ _
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 1000 * (j + 1) * (j + 1) := ⟨_, rfl⟩
  refine ⟨C₁ * w⁻¹ + d⁻¹, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC₁
      (ENNReal.inv_ne_top.2 hw0), ENNReal.inv_ne_top.2 hd0⟩,
    max (max r₁ (4 * j + 1)) (m * (m * m) + 2), ?_⟩
  rw [← hm] at hsep hwin
  intro q L hCB z r R hr hrR hRL
  have hr₁ : r₁ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hj : 4 * j + 1 ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hm3 : m * (m * m) + 2 ≤ r := le_trans (le_max_right _ _) hr
  have hinv : ∀ {x y : ℝ≥0∞} {e : ℝ≥0∞}, e ≠ 0 → e ≠ ⊤ → e * x ≤ y → x ≤ e⁻¹ * y :=
    fun {x y e} he0 het h => by
      calc x = e⁻¹ * (e * x) := by rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
        _ ≤ e⁻¹ * y := mul_le_mul' le_rfl h
  have hRL' : (R : ℕ∞) ≤ L := le_trans (by exact_mod_cast (by omega : R ≤ 2 * R)) hRL
  by_cases hbig : 7 * r ≤ R
  · have h1 := hsep q L hCB z r R hr₁ hbig hRL'
    obtain ⟨tT, lamT, αT, βT, hw1, hw2, hw3, hw4, hw5⟩ := exists_bottom_windows
      (n := m) (by rw [hm]) z (2 * R)
    have h2 := hwin q L hCB z r R (2 * R) tT lamT αT βT (by omega) le_rfl (by omega) (by omega)
      hRL hw1 hw2 hw3 hw4 hw5
    have h3 : w * law q (outerSeparatedArmEvent σ z r R
        ((2 * (((64 * m + 24 * j + 24) * (R / (m * m)) : ℕ) : ℤ) - 1 : ℤ) : ℝ)
        (2 * (R / (m * m))) (R / (m * m))) ≤ law q (multiArmEvent σ z r (2 * R)) := by
      refine (mul_le_mul' hwc le_rfl).trans (h2.trans (measure_mono ?_))
      rintro ω ⟨a, b, γ, hγ, hd, ho, -, -⟩
      exact mem_multiArmEvent_iff.2 ⟨a, b, γ, hγ, hd, ho⟩
    calc law q (multiArmEvent σ z r R)
        ≤ C₁ * (w⁻¹ * law q (multiArmEvent σ z r (2 * R))) :=
          h1.trans (mul_le_mul' le_rfl (hinv hw0 hwt h3))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · have h1 : d ≤ law q (multiArmEvent σ z r (2 * R)) :=
      hdc.trans (hone q L hCB z r (2 * R) (by omega) (by omega) (by omega) hRL)
    calc law q (multiArmEvent σ z r R) ≤ 1 := prob_le_one
      _ = d⁻¹ * d := (ENNReal.inv_mul_cancel hd0 hdt).symm
      _ ≤ (C₁ * w⁻¹ + d⁻¹) * law q (multiArmEvent σ z r (2 * R)) :=
          mul_le_mul' le_add_self h1

/-! ### Quasi-multiplicativity, upper half, for all ordered radii -/

/-- An arm of length zero on the left side of `B_r(z)`: the vertex `(z₀ - r, y)` (open) or the
face `(z₀ - r - 1, y)` just left of it (dual), for `z₁ - r < y < z₁ + r`, is an arm from `B_r(z)`
to its own boundary, landing at `12 r + 2 (z₁ + r - y) - [dual]`. -/
theorem isArm_nil_left (ω : Config (LatticeSite 2)) (col : Bool) (z : LatticeSite 2) {r : ℕ}
    {y : ℤ} (hy₁ : z 1 - r < y) (hy₂ : y < z 1 + r) :
    IsArm ω col z r (z - r) (z + r)
        (SimpleGraph.Walk.nil : (zdGraph 2).Walk ![z 0 - r - cond col 0 1, y]
          ![z 0 - r - cond col 0 1, y]) ∧
      landingPos (z - r) (z + r) col
          (SimpleGraph.Walk.nil : (zdGraph 2).Walk ![z 0 - r - cond col 0 1, y]
            ![z 0 - r - cond col 0 1, y]) =
        12 * r + 2 * (z 1 + r - y) - cond col 0 1 := by
  cases col
  · refine ⟨⟨SimpleGraph.Walk.isCrossing_nil_iff.2 ⟨?_, ?_⟩, by simp⟩, ?_⟩
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
        Pi.natCast_apply, Pi.one_apply, Bool.cond_false]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
        Pi.natCast_apply, Pi.one_apply, Bool.cond_false]
      omega
    · rw [landingPos_false, SimpleGraph.Walk.penultimate_nil]
      unfold perimeterPos
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
        nsmul_eq_mul, Nat.cast_ofNat, Bool.cond_false, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      split_ifs <;> omega
  · refine ⟨⟨SimpleGraph.Walk.isCrossing_nil_iff.2 ⟨?_, ?_⟩, by simp⟩, ?_⟩
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
        Pi.natCast_apply, Bool.cond_true]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
        Pi.natCast_apply, Pi.one_apply, Bool.cond_true]
      omega
    · rw [landingPos_true]
      unfold perimeterPos
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Bool.cond_true,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      split_ifs <;> omega

/-- **The arm event across an empty annulus.** For `j ≤ r` the `j`-arm event from `B_r(z)` to its
own boundary is everything: arms of length zero at the heights `z₁ + r - 1 - i` down the left
side of `B_r(z)` (open arms at its vertices, dual arms at the faces just left of it) form a disjoint
family landing in counterclockwise order, whatever the configuration. -/
theorem multiArmEvent_self_eq_univ {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) {r : ℕ}
    (hjr : j ≤ r) : multiArmEvent σ z r r = univ := by
  refine eq_univ_of_forall fun ω => ?_
  have hy : ∀ i : Fin j, z 1 - r < z 1 + r - 1 - ((i : ℕ) : ℤ) ∧
      z 1 + r - 1 - ((i : ℕ) : ℤ) < z 1 + r := fun i => by
    have := i.2
    omega
  refine mem_multiArmEvent_iff.2 ⟨fun i => ![z 0 - r - cond (σ i) 0 1, z 1 + r - 1 - (i : ℕ)],
    fun i => ![z 0 - r - cond (σ i) 0 1, z 1 + r - 1 - (i : ℕ)],
    fun i => SimpleGraph.Walk.nil, fun i => (isArm_nil_left ω (σ i) z (hy i).1 (hy i).2).1,
    ⟨fun i k _ _ _ v hv => by simp at hv, fun i k hik _ _ v hv hv' => ?_⟩, fun i k l hik hkl => ?_⟩
  · simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv hv'
    have := congrFun (hv.symm.trans hv') 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    exact hik (Fin.ext (by omega))
  · rw [(isArm_nil_left ω (σ i) z (hy i).1 (hy i).2).2,
      (isArm_nil_left ω (σ k) z (hy k).1 (hy k).2).2,
      (isArm_nil_left ω (σ l) z (hy l).1 (hy l).2).2]
    have hik' : (i : ℕ) < k := hik
    have hkl' : (k : ℕ) < l := hkl
    have e : ∀ m : Fin j, cond (σ m) (0 : ℤ) 1 = 0 ∨ cond (σ m) (0 : ℤ) 1 = 1 := fun m => by
      cases σ m <;> simp
    rcases e i with hi | hi <;> rcases e k with hk | hk <;> rcases e l with hl | hl <;>
      rw [hi, hk, hl] <;> exact Int.sbtw_iff.2 (Or.inl ⟨by omega, by omega⟩)

/-- **Upper half of quasi-multiplicativity for ordered radii.** For `j ≤ r₁ ≤ r₂ ≤ r₃` and every
product law, `π_σ(r₁, r₃) ≤ π_σ(r₁, r₂) π_σ(r₂, r₃)`: for strictly increasing radii this is
`law_multiArmEvent_le_mul`, and an empty annulus carries the whole space
(`multiArmEvent_self_eq_univ`). -/
theorem law_multiArmEvent_le_mul_of_le (q : Sym2 (LatticeSite 2) → unitInterval) {j : ℕ}
    (σ : Fin j → Bool) (z : LatticeSite 2) {r₁ r₂ r₃ : ℕ} (hj : j ≤ r₁) (h₁ : r₁ ≤ r₂)
    (h₂ : r₂ ≤ r₃) :
    law q (multiArmEvent σ z r₁ r₃) ≤
      law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃) := by
  rcases h₁.lt_or_eq with h₁ | rfl
  · rcases h₂.lt_or_eq with h₂ | rfl
    · exact law_multiArmEvent_le_mul q σ z h₁ h₂
    · rw [multiArmEvent_self_eq_univ σ z (hj.trans h₁.le), measure_univ, mul_one]
  · rw [multiArmEvent_self_eq_univ σ z hj, measure_univ, one_mul]

end PercLib.Models.Planar
