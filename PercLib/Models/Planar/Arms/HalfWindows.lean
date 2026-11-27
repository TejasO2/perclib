/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (arms landing in prescribed windows) and Section 4.6
(the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.OuterArmSeparation

/-!
# Target windows in the upper half of the boundary

The motion plan in the half-plane (`exists_pos_le_law_half_target_windows`) carries arms into
windows on the top side and the upper halves of the right and left sides of a box, at a margin
from the corners and from the two points of the line `{v | v₁ = z₁}` on the boundary. This file
provides such windows: inside the windows of landing data whose windows lie in the upper half of
the boundary, and `j` windows on the top side (the throwaway targets of the intermediate window
steps of Theorem 11 in the half-plane).

## Main results

* `exists_windows_of_ccw_half`: windows in counterclockwise coordinates on the top side and the
  upper half-sides, in the format of the motion plan, with the margin from the line.
* `exists_top_windows_half`: `j` windows on the top side of `B_R(z)`.
* `IsLanding.exists_windows_half`: for landing data `(η, θ)` with `θ i ∈ [3/8 + η, 7/8 - 2η]`
  (windows of the circle inside `(6R, 14R)` in landing positions), target windows in the format of
  the motion plan in the half-plane such that an arm ending in window `i` lands in
  `window (16 R) θ η i`.
* An `example`: such landing data exist.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

section Windows

variable {j : ℕ}

/-- **Target windows in the upper half of the boundary from counterclockwise coordinates**
(`exists_windows_of_ccw` with the margin from the line). Windows `[u i, v i]` in counterclockwise
coordinates on the sides `t i` of `B_R(z)`, at least `Y` from the corners and, on the right and
left sides, from the line (`u i ≥ Y` on the right side, `v i ≤ -Y` on the left side), of length at
least `Y` and at least `Y` apart on each side in the order of the index, give windows
`[αT i, βT i]` in the coordinates of the motion plan with the same margins, lengths and gaps; the
ends of arms lying in them are the same. -/
theorem exists_windows_of_ccw_half (z : LatticeSite 2) (R : ℕ) (Y : ℤ) (t : Fin j → Fin 4)
    (u v : Fin j → ℤ) (hcor : ∀ i, -(R : ℤ) + Y ≤ u i ∧ v i + Y ≤ R)
    (hline : ∀ i, (t i = 1 → Y ≤ u i) ∧ (t i = 3 → v i + Y ≤ 0))
    (hwid : ∀ i, u i + Y ≤ v i) (hgap : ∀ i l, i < l → t i = t l → v i + Y ≤ u l) :
    ∃ αT βT : Fin j → ℤ,
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + Y ≤ αT i ∧
        βT i + Y ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) ∧
      (∀ i, t i = 1 ∨ t i = 3 → z 1 + Y ≤ αT i) ∧
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
  refine ⟨αT, βT, fun i => ?_, fun i hi => ?_, fun i => ?_, fun i l hil ht => ?_,
    fun i ρ col p hp => (hiff i ρ col p).2 hp⟩
  · have := hcor i
    rcases hc i with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2] <;> constructor <;> linarith
  · obtain ⟨h1, h3⟩ := hline i
    rcases hi with e | e
    · have := h1 e
      rcases hαβ i with ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ <;> omega
    · have := h3 e
      rcases hαβ i with ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ <;> omega
  · have := hwid i
    rcases hc i with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2] <;> linarith
  · have hg := hgap i l hil ht
    have h₂ := hc l
    rw [← ht] at h₂
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    rcases hc i with ⟨ho, h1, h2⟩ | ⟨ho, h1, h2⟩ <;>
      rcases h₂ with ⟨ho', h3, h4⟩ | ⟨ho', h3, h4⟩ <;> omega

/-- **Windows on the top side** (`exists_bottom_windows` for the half-plane). For
`n ≥ 1000 (j + 1)²`, the top side of `B_R(z)` carries `j` windows of length
`Y = (96 n + 24 j + 38) ⌊R / n²⌋`, at least `Y` from the corners and `2Y` apart, in the
counterclockwise order of the index (lifted side `2`): the targets of the window step between two
scales in the half-plane (the margin from the line is void on the top side). -/
theorem exists_top_windows_half {n : ℕ} (hn : 1000 * (j + 1) * (j + 1) ≤ n) (z : LatticeSite 2)
    (R : ℕ) :
    ∃ (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      (∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i l, i ≤ l → lamT i ≤ lamT l) ∧
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R +
          (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ αT i ∧
        βT i + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤
          (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R) ∧
      (∀ i, tT i ≠ 0 → z 1 + (((96 * n + 24 * j + 38) * (R / (n * n)) : ℕ) : ℤ) ≤ αT i) ∧
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
  obtain ⟨αT, βT, h1, h2, h3, -⟩ := exists_windows_of_ccw z R Y (fun _ => 0)
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
  exact ⟨fun _ => 0, fun _ => 2, αT, βT, fun _ => ⟨by norm_num, by norm_num, by norm_num⟩,
    fun _ _ _ => le_rfl, h1, fun i h => absurd rfl h, h2, h3⟩

/-- **Target windows inside landing data in the upper half of the boundary**
(`IsLanding.exists_windows` for the half-plane). For landing data `(η, θ)` whose windows lie in the
upper half of the boundary with a margin `η` from the two points of the line
(`3/8 + η ≤ θ i`, `θ i + 2η ≤ 7/8`; landing positions in `(6R, 14R)`), there is `Λ > 0` such
that for every `Y` and `R ≥ Λ (Y + 4)` the top side and the upper halves of the right and left
sides of `B_R(z)` carry `j` windows in the format of the motion plan in the half-plane (lifted sides
`lamT i ∈ [1, 3]`, nondecreasing), at least `Y` from the corners and from the line, of length at
least `Y`, at least `Y` apart on each side and in the counterclockwise order of the index, such
that an arm to `∂B_R(z)` ending in window `i` (and landing at least `4` from the doubled corners)
has its landing position in the window of the landing data, `landingPos ∈ window (16 R) θ η i`. -/
theorem IsLanding.exists_windows_half {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ)
    (hθH : ∀ i, 3 / 8 + η ≤ θ i ∧ θ i + 2 * η ≤ 7 / 8) :
    ∃ Λ : ℕ, 0 < Λ ∧ ∀ (z : LatticeSite 2) (R Y : ℕ), Λ * (Y + 4) ≤ R →
      ∃ (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
        (∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) ∧
        (∀ i l, i ≤ l → lamT i ≤ lamT l) ∧
        (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R + (Y : ℤ) ≤ αT i ∧
          βT i + (Y : ℤ) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R) ∧
        (∀ i, tT i ≠ 0 → z 1 + (Y : ℤ) ≤ αT i) ∧
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
  -- the core windows are in the upper half of the boundary: not on the bottom side
  have hc1 : ∀ i, 0 < c i := fun i => by
    have e1 := hθa i
    have e2 := hhi i
    have e3 := (hθH i).1
    have e4 := hθ.pos
    have : (0 : ℚ) < c i := by linarith
    exact_mod_cast this
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
  obtain ⟨αT, βT, h1, hl, h2, h3, hiff⟩ := exists_windows_of_ccw_half z R Y t u v
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
      have e1 := hθa i
      have e2 := haη i
      have e3 := hθH i
      have k1 := hu1 i
      have k2 := hv1 i
      have hμη : 8 * μ * R ≤ 8 * η * R :=
        mul_le_mul_of_nonneg_right (by linarith) hR0
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have hc : c i = 1 := by
          have := htc i
          have := hc3 i
          omega
        have m : 8 * η * R ≤ (8 * a i - 2 * c i - 1) * R :=
          mul_le_mul_of_nonneg_right (by rw [hc]; push_cast; linarith) hR0
        have : (Y : ℚ) ≤ u i := by linarith
        exact_mod_cast this
      · have hc : c i = 3 := by
          have := htc i
          have := hc3 i
          omega
        have m : (8 * (a i + μ) - 2 * c i - 1) * R ≤ -(8 * η * R) := by
          have : (8 * (a i + μ) - 2 * c i - 1) ≤ -(8 * η) := by rw [hc]; push_cast; linarith
          nlinarith
        have : (v i + Y : ℚ) ≤ 0 := by linarith
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
    fun i => ⟨by have := hc1 i; dsimp only; omega, by have := hc3 i; dsimp only; omega, htc i⟩,
    fun i l hil => by have := hmono i l hil; dsimp only; omega, h1,
    fun i h0 => hl i (by have := htc i; have := hc3 i; have := hc1 i; omega), h2, h3, ?_⟩
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

/-- Landing data in the upper half of the boundary exist: two windows of length `1/16` of a turn,
at `1/2` and `5/8`, satisfy the hypotheses of `IsLanding.exists_windows_half`. -/
example : IsLanding (1 / 16 : ℚ) ![1 / 2, 5 / 8] ∧
    ∀ i, 3 / 8 + (1 / 16 : ℚ) ≤ ![(1 / 2 : ℚ), 5 / 8] i ∧
      ![(1 / 2 : ℚ), 5 / 8] i + 2 * (1 / 16) ≤ 7 / 8 := by
  refine ⟨⟨by norm_num, fun i => ?_, fun i => ?_, fun i k hik => ?_, fun i k => ?_⟩, fun i => ?_⟩
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num
  · revert hik
    fin_cases i <;> fin_cases k <;> norm_num
  · fin_cases i <;> fin_cases k <;> norm_num
  · fin_cases i <;> norm_num

end Windows

end PercLib.Models.Planar
