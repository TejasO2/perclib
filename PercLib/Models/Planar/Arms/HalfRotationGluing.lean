/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12, and the
arms landing in prescribed windows) and Section 4.6 (the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.HalfGluing
public import PercLib.Models.Planar.Arms.HalfTurnCorridors

/-!
# Moves of the arms of a half-plane between windows

The stage of moves of `RotationGluing.lean` for the arms of the half-plane `{v | z₁ ≤ v₁}`,
landing in increasing order, without two consecutive arms of one colour. The arms land on three
sides of `B_R(z)` (the top side and the two half-sides above the line), and every arm is moved along
its side (a jog), round the next corner counterclockwise (from the right side to the top side, from
the top side to the left side) or round the previous corner clockwise (from the top side to the
right side, from the left side to the top side; `HalfTurnCorridors.lean`). There is no bottom side,
so an arm cannot go round the box; clockwise turns are needed to reach windows on an earlier side.
The windows on the half-sides stay at least `S` above the line, so every corridor lies in the
half-plane and the glued arms do as well (`pow_mul_law_le_law_of_regions_half`).

## Main results

* `disjoint_regions_of_moves_half`: the regions of the moves of two arms are disjoint when their
  windows are far from the corners and from each other, a counterclockwise turning arm is the last
  of its side, a clockwise turning arm the first, and no corner is turned in both directions.
* `exists_corridor_move_half`: the corridor of one move in its region.
* `exists_pos_le_law_windows_of_moves_half`: **a stage of moves between windows in the
  half-plane**, with a constant depending only on `σ`, `c` and the ratios `A`, `N`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Regions of moves in the half-plane -/

section MoveRegions

/-- The case 0 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_0
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 0 ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = α₁ - D - M - K' ∧ b₁ = z₁ + R - M ∧ c₁ = β₁ + W + D + M + K' + 1 ∧
      d₁ = z₁ + R' + M' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).1 rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hw2 := _hcw₂ rfl rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 1 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_1
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 0 ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ + R - M ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ + R' + M' + 1 ∧
      d₁ = β₁ + W + D + M + K' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).2 rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 2 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_2
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 0 ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ - R' - M' - 1 ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ - R + M + 1 ∧
      d₁ = β₁ + W + D + M + K' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hw2 := _hcw₂ rfl rfl
    omega

/-- The case 3 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_3
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 1 ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ + R - M - K' ∧ b₁ = α₁ - M ∧ c₁ = z₀ + h + W + K' + 1 ∧
      d₁ = z₁ + R' + M' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).2 rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).2 rfl
    have hc2 := (_hccw₂ rfl rfl).2 rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    exact absurd ⟨rfl, rfl, rfl, rfl⟩ _hcorner.2.1
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 4 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_4
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 1 ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = z₀ - R' - M' - 1 ∧ b₁ = z₁ + R - M - K' ∧ c₁ = β₁ + W + M + 1 ∧
      d₁ = z₁ + h + W + K' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 rfl
    have hc2 := (_hccw₂ rfl rfl).1 rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 rfl
    have hw2 := _hcw₂ rfl rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    exact absurd ⟨rfl, rfl, rfl, rfl⟩ _hcorner.2.2.2

/-- The case 5 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_5
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 2 ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = α₁ - M ∧ b₁ = z₁ + R - M - K' ∧ c₁ = z₀ + R' + M' + 1 ∧
      d₁ = z₁ + h + W + K' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hw1 := _hcw₁ rfl rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    exact absurd ⟨rfl, rfl, rfl, rfl⟩ _hcorner.1
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).1 rfl
    have hw1 := _hcw₁ rfl rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hw1 := _hcw₁ rfl rfl
    have hw2 := _hcw₂ rfl rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 6 of the first move in `disjoint_regions_of_moves_half`. -/
theorem disjoint_regions_of_moves_half_6
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (_hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (_hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (_hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 2 ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ - h - W - K' ∧ b₁ = α₁ - M ∧ c₁ = z₀ - R + M + K' + 1 ∧
      d₁ = z₁ + R' + M' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hw1 := _hcw₁ rfl rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    exact absurd ⟨rfl, rfl, rfl, rfl⟩ _hcorner.2.2.1
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hw1 := _hcw₁ rfl rfl
    have hw2 := _hcw₂ rfl rfl
    omega

/-- **Regions of moves in the half-plane are disjoint** (integer form). Two arms with windows
`[α, β]` on the sides `t` of `B_R` other than the bottom (`0` top, `1` right, `3` left), at least
`S` from the corners, moving by a jog (`τ = 0`), a counterclockwise turn (`τ = 1`: from the right
side to the top side, or from the top side to the left side) or a clockwise turn (`τ = 2`: from the
top side to the right side, or from the left side to the top side), have the regions
`[a, c] × [b, d]` described below (one formula for each move); if windows on one side are `S`
apart, a counterclockwise turning arm is the last one on its side in counterclockwise order, a
clockwise turning arm the first one, no corner is turned in both directions, and
`S ≥ W + 2D + 2M + 2K' + 3`, the two regions are disjoint. -/
theorem disjoint_regions_of_moves_half
    {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} {t₁ t₂ : Fin 4}
    {τ₁ τ₂ : Fin 3}
    (hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (hR : M + K' + 1 < R) (hh : R + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R')
    (hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (hccw₁ : τ₁ = 1 → t₂ = t₁ → (t₁ = 0 → β₁ + S ≤ α₂) ∧ (t₁ = 1 → β₂ + S ≤ α₁))
    (hccw₂ : τ₂ = 1 → t₁ = t₂ → (t₂ = 0 → β₂ + S ≤ α₁) ∧ (t₂ = 1 → β₁ + S ≤ α₂))
    (hcw₁ : τ₁ = 2 → t₂ = t₁ → β₂ + S ≤ α₁)
    (hcw₂ : τ₂ = 2 → t₁ = t₂ → β₁ + S ≤ α₂)
    (hcorner : ¬(τ₁ = 2 ∧ t₁ = 0 ∧ τ₂ = 1 ∧ t₂ = 1) ∧ ¬(τ₂ = 2 ∧ t₂ = 0 ∧ τ₁ = 1 ∧ t₁ = 1) ∧
      ¬(τ₁ = 2 ∧ t₁ = 3 ∧ τ₂ = 1 ∧ t₂ = 0) ∧ ¬(τ₂ = 2 ∧ t₂ = 3 ∧ τ₁ = 1 ∧ t₁ = 0))
    (h₁ : (τ₁ = 0 ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = α₁ - D - M - K' ∧ b₁ = z₁ + R - M ∧ c₁ = β₁ + W + D + M + K' + 1 ∧
        d₁ = z₁ + R' + M' + 1) ∨
      (τ₁ = 0 ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ + R - M ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ + R' + M' + 1 ∧
        d₁ = β₁ + W + D + M + K' + 1) ∨
      (τ₁ = 0 ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ - R' - M' - 1 ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ - R + M + 1 ∧
        d₁ = β₁ + W + D + M + K' + 1) ∨
      (τ₁ = 1 ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ + R - M - K' ∧ b₁ = α₁ - M ∧ c₁ = z₀ + h + W + K' + 1 ∧
        d₁ = z₁ + R' + M' + 1) ∨
      (τ₁ = 1 ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = z₀ - R' - M' - 1 ∧ b₁ = z₁ + R - M - K' ∧ c₁ = β₁ + W + M + 1 ∧
        d₁ = z₁ + h + W + K' + 1) ∨
      (τ₁ = 2 ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = α₁ - M ∧ b₁ = z₁ + R - M - K' ∧ c₁ = z₀ + R' + M' + 1 ∧
        d₁ = z₁ + h + W + K' + 1) ∨
      (τ₁ = 2 ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ - h - W - K' ∧ b₁ = α₁ - M ∧ c₁ = z₀ - R + M + K' + 1 ∧
        d₁ = z₁ + R' + M' + 1))
    (h₂ : (τ₂ = 0 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 0 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧
        d₂ = β₂ + W + D + M + K' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = 1 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ + R - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧
        d₂ = z₁ + h + W + K' + 1) ∨
      (τ₂ = 2 ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ - R + M + K' + 1 ∧
        d₂ = z₁ + R' + M' + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁
  · exact disjoint_regions_of_moves_half_0 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂
  · exact disjoint_regions_of_moves_half_1 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂
  · exact disjoint_regions_of_moves_half_2 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂
  · exact disjoint_regions_of_moves_half_3 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂
  · exact disjoint_regions_of_moves_half_4 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂
  · exact disjoint_regions_of_moves_half_5 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂
  · exact disjoint_regions_of_moves_half_6 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ hcw₁ hcw₂
      hcorner h₁ h₂

end MoveRegions

/-! ### One move in the half-plane -/

section Moves

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}
  {col : Bool} {z : LatticeSite 2} {r R R' M K M' K' W D S κ : ℕ}

/-- **The corridor of one move in the half-plane.** An arm whose ends lie in a window `[α, β]` on a
side `t ≠ 2` of `B_R(z)` (at least `S` from the corners) and in the bin `[x, x + W]`, `α ≤ x ≤ β`,
is moved along its side by `d` (`τ = 0`: target window `[α + d, β + d + W]` on the same side of
`B_{R'}(z)`), turned counterclockwise round the next corner at the level `h` (`τ = 1`: from the
right side to the top side, window `[z₀ + h, z₀ + h + W]`, or from the top side to the left side,
window `[z₁ + h, z₁ + h + W]`) or turned clockwise round the previous corner (`τ = 2`: from the top
side to the right side, window `[z₁ + h, z₁ + h + W]`, or from the left side to the top side, window
`[z₀ - h - W, z₀ - h]`): its corridor of probability at least `c κ ^ 6` lies in the region
`Icc gl gh` given by one formula for each move (the formulas of `disjoint_regions_of_moves_half`),
and ends in the target window with an outer fence `(M', K')`. -/
theorem exists_corridor_move_half (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M')
    (hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) {h : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R') (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W)
    (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L)
    {t t' : Fin 4} {τ : Fin 3} {α β d α' β' x : ℤ} (ht : t ≠ 2) (hd : -(D : ℤ) ≤ d ∧ d ≤ D)
    (hwin : (if t = 0 ∨ t = 2 then z 0 else z 1) - R + S ≤ α ∧
      β + S ≤ (if t = 0 ∨ t = 2 then z 0 else z 1) + R)
    (hx : α ≤ x ∧ x ≤ β)
    (hout : (τ = 0 ∧ t' = t ∧ α' = α + d ∧ β' = β + d + W) ∨
      (τ = 1 ∧ ((t = 1 ∧ t' = 0 ∧ α' = z 0 + h ∧ β' = z 0 + h + W) ∨
        (t = 0 ∧ t' = 3 ∧ α' = z 1 + h ∧ β' = z 1 + h + W))) ∨
      (τ = 2 ∧ ((t = 0 ∧ t' = 1 ∧ α' = z 1 + h ∧ β' = z 1 + h + W) ∨
        (t = 3 ∧ t' = 0 ∧ α' = z 0 - h - W ∧ β' = z 0 - h))))
    (B : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, ((t = 0 ∧ b 1 = z 1 + R ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ α ≤ b 1 ∧ b 1 ≤ β) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ α ≤ b 1 ∧ b 1 ≤ β)) ∧
      ((t = 0 ∧ x ≤ b 0 ∧ b 0 ≤ x + W) ∨ (t = 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W) ∨
        (t = 2 ∧ x ≤ b 0 ∧ b 0 ≤ x + W) ∨ (t = 3 ∧ x ≤ b 1 ∧ b 1 ≤ x + W))) :
    ∃ gl gh : LatticeSite 2, ((τ = 0 ∧ t = 0 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = α - D - M - K' ∧ gl 1 = z 1 + R - M ∧ gh 0 = β + W + D + M + K' + 1 ∧
        gh 1 = z 1 + R' + M' + 1) ∨
      (τ = 0 ∧ t = 1 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 + R - M ∧ gl 1 = α - D - M - K' ∧ gh 0 = z 0 + R' + M' + 1 ∧
        gh 1 = β + W + D + M + K' + 1) ∨
      (τ = 0 ∧ t = 3 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = α - D - M - K' ∧ gh 0 = z 0 - R + M + 1 ∧
        gh 1 = β + W + D + M + K' + 1) ∨
      (τ = 1 ∧ t = 1 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 + R - M - K' ∧ gl 1 = α - M ∧ gh 0 = z 0 + h + W + K' + 1 ∧
        gh 1 = z 1 + R' + M' + 1) ∨
      (τ = 1 ∧ t = 0 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = z 1 + R - M - K' ∧ gh 0 = β + W + M + 1 ∧
        gh 1 = z 1 + h + W + K' + 1) ∨
      (τ = 2 ∧ t = 0 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = α - M ∧ gl 1 = z 1 + R - M - K' ∧ gh 0 = z 0 + R' + M' + 1 ∧
        gh 1 = z 1 + h + W + K' + 1) ∨
      (τ = 2 ∧ t = 3 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 - h - W - K' ∧ gl 1 = α - M ∧ gh 0 = z 0 - R + M + K' + 1 ∧
        gh 1 = z 1 + R' + M' + 1)) ∧
      ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc gl gh) ∧
      (∀ b ∈ B, Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ Icc gl gh) ∧
      Q ⊆ Icc gl gh ∧
      (∀ b ∈ B, ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
        v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
        IsArm ω col z r (z - R) (z + R) γ → b ∈ B → HasOuterFence ω col z R M K γ →
        ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
          x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            v ∈ {b : LatticeSite 2 | ((t' = 0 ∧ b 1 = z 1 + R' ∧ α' ≤ b 0 ∧ b 0 ≤ β') ∨
        (t' = 1 ∧ b 0 = z 0 + R' ∧ α' ≤ b 1 ∧ b 1 ≤ β') ∨
        (t' = 2 ∧ b 1 = z 1 - R' - cond col 0 1 ∧ α' ≤ b 0 ∧ b 0 ≤ β') ∨
        (t' = 3 ∧ b 0 = z 0 - R' - cond col 0 1 ∧ α' ≤ b 1 ∧ b 1 ≤ β'))} ∧
              HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rcases hout with ⟨rfl, ht', rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩ |
    ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩
  · subst t'
    rcases (by decide : ∀ u : Fin 4, u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3) t with rfl | rfl | rfl | rfl
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = α - D - M - K' ∧ gl 1 = z 1 + R - M :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = β + W + D + M + K' + 1 ∧ gh 1 = z 1 +
          R' + M' + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀,
          hgh₁⟩, ?_⟩
      exact exists_corridor_jogCap_top hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x - D)
          (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).1 rfl
          have h₂ := (side_cases (hB b hb).2).1 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inl ⟨rfl, hv₁, by omega, by omega⟩)
        gl gh (by omega) (by omega) (by omega) (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 + R - M ∧ gl 1 = α - D - M - K' :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 + R' + M' + 1 ∧ gh 1 = β + W + D
          + M + K' + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀,
          hgh₁⟩), ?_⟩
      exact exists_corridor_jogCap_right hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x -
          D) (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).2.1 rfl
          have h₂ := (side_cases (hB b hb).2).2.1 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inl ⟨rfl, hv₁, by omega, by omega⟩))
        gl gh (by omega) (by omega) (by omega) (by omega)
    · exact absurd rfl ht
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = α - D - M
          - K' :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 - R + M + 1 ∧ gh 1 = β + W + D +
          M + K' + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀,
          hgh₁⟩)), ?_⟩
      exact exists_corridor_jogCap_left hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x - D)
          (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).2.2.2 rfl
          have h₂ := (side_cases (hB b hb).2).2.2.2 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inr (Or.inr (⟨rfl, hv₁, by omega, by omega⟩))))
        gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 + R - M - K' ∧ gl 1 = α - M :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 + h + W + K' + 1 ∧ gh 1 = z 1 + R'
        + M' + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀,
        hgh₁⟩))), ?_⟩
    exact exists_corridor_turn_right_top hCB hM hWK hKM hW hM' hWM' (y := x) (h := h) (by omega)
        (by omega) hh hhR (by omega) hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).2.1 rfl
        have h₂ := (side_cases (hB b hb).2).2.1 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inl ⟨rfl, hv₁, hv₂, hv₃⟩)
      gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = z 1 + R - M
        - K' :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = β + W + M + 1 ∧ gh 1 = z 1 + h + W + K'
        + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀,
        hgl₁, hgh₀, hgh₁⟩)))), ?_⟩
    exact exists_corridor_turn_top_left hCB hM hWK hKM hW hM' hWM' (x := x) (h := h) (by omega)
        (by omega) hh hhR (by omega) hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).1 rfl
        have h₂ := (side_cases (hB b hb).2).1 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inr (Or.inr (⟨rfl, hv₁, hv₂, hv₃⟩))))
      gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = α - M ∧ gl 1 = z 1 + R - M - K' :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 + R' + M' + 1 ∧
        gh 1 = z 1 + h + W + K' + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2,
        hgl₀, hgl₁, hgh₀, hgh₁⟩))))), ?_⟩
    exact exists_corridor_turn_top_right hCB hM hWK hKM hW hM' hWM' (x := x) (h := h) (by omega)
        (by omega) hh hhR (by omega) hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).1 rfl
        have h₂ := (side_cases (hB b hb).2).1 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inl ⟨rfl, hv₁, hv₂, hv₃⟩))
      gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 - h - W - K' ∧ gl 1 = α - M :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 - R + M + K' + 1 ∧
        gh 1 = z 1 + R' + M' + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hwin.1, hwin.2,
        hgl₀, hgl₁, hgh₀, hgh₁⟩))))), ?_⟩
    exact exists_corridor_turn_left_top hCB hM hWK hKM hW hM' hWM' (y := x) (h := h) (by omega)
        (by omega) hh hhR hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).2.2.2 rfl
        have h₂ := (side_cases (hB b hb).2).2.2.2 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inl ⟨rfl, hv₁, hv₂, hv₃⟩)
      gl gh (by omega) (by omega) (by omega) (by omega)


end Moves

/-! ### The stage of moves in the half-plane -/

section Stages

variable {j : ℕ}

/-- **A stage of moves between windows in the half-plane** (`exists_pos_le_law_windows_of_moves`
for the arms of the half-plane `{v | z₁ ≤ v₁}`, landing in increasing order, without two
consecutive arms of one colour). Separated arms of the half-plane ending in windows `[α i, β i]` on
the sides `t i ≠ 2` of `B_R(z)` (`0` top, `1` right, `3` left; at least `S` from the corners and, on
the half-sides, at least `S` above the line; windows on one side `S` apart, each covered by `N`
bins of width `W`) are moved to `∂B_{R'}(z)`: arm `i` is moved along its side by `d i`
(`τ i = 0`), turned counterclockwise (`τ i = 1`; only the last arm of its side in counterclockwise
order; from the right side to `[z₀ + h, z₀ + h + W]` on the top side, from the top side to
`[z₁ + h, z₁ + h + W]` on the left side) or turned clockwise (`τ i = 2`; only the first arm of its
side; from the top side to `[z₁ + h, z₁ + h + W]` on the right side, from the left side to
`[z₀ - h - W, z₀ - h]` on the top side), no corner being turned in both directions. The new arms lie
in the half-plane, land in increasing order, have fences `(M', K')` with `W + K' ≤ M'`, and are
separated at scale `2g' - 1` when the target windows are at least `g'` from the corners of
`B_{R'}(z)` and from each other on one side: `c₀ P(windows at R) ≤ P(windows at R')`. The constant
`c₀ = c A ^ (6j) / (N + 1) ^ j` depends only on `σ`, `c`, `A`, `N`. -/
theorem exists_pos_le_law_windows_of_moves_half (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S : ℕ) (h : ℤ) (s : ℝ)
      (g' : ℤ) (J : Fin j → Set ℤ) (t t' : Fin j → Fin 4) (τ : Fin j → Fin 3)
      (α β d α' β' : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2 * D + 2 * M + 2 * K' + 3 ≤ S →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → (R : ℤ) + M + 1 ≤ h → h + W + M' ≤ R' →
      2 * R' + 2 ≤ A * W → W + 2 * K' ≤ A * (M' - 1) → (R' : ℕ∞) ≤ L →
      (∀ i, -(D : ℤ) ≤ d i ∧ d i ≤ D) → (∀ i, β i - α i + 1 ≤ N * ((W : ℤ) + 1)) →
      (∀ i, t i ≠ 2) →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + S ≤ α i ∧
        β i + S ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      (∀ i, t i ≠ 0 → z 1 + S ≤ α i) →
      (∀ i k, i ≠ k → t i = t k → β i + S ≤ α k ∨ β k + S ≤ α i) →
      (∀ i k, i ≠ k → τ i = 1 → t k = t i → (t i = 0 → β i + S ≤ α k) ∧
        (t i = 1 → β k + S ≤ α i)) →
      (∀ i k, i ≠ k → τ i = 2 → t k = t i → β k + S ≤ α i) →
      (∀ i k, τ i = 2 → τ k = 1 → ¬(t i = 0 ∧ t k = 1) ∧ ¬(t i = 3 ∧ t k = 0)) →
      (∀ i, (τ i = 0 ∧ t' i = t i ∧ α' i = α i + d i ∧ β' i = β i + d i + W) ∨
        (τ i = 1 ∧ ((t i = 1 ∧ t' i = 0 ∧ α' i = z 0 + h ∧ β' i = z 0 + h + W) ∨
          (t i = 0 ∧ t' i = 3 ∧ α' i = z 1 + h ∧ β' i = z 1 + h + W))) ∨
        (τ i = 2 ∧ ((t i = 0 ∧ t' i = 1 ∧ α' i = z 1 + h ∧ β' i = z 1 + h + W) ∨
          (t i = 3 ∧ t' i = 0 ∧ α' i = z 0 - h - W ∧ β' i = z 0 - h)))) →
      1 ≤ g' →
      (∀ i, (if t' i = 0 ∨ t' i = 2 then z 0 else z 1) - R' + g' ≤ α' i ∧
        β' i + g' ≤ (if t' i = 0 ∨ t' i = 2 then z 0 else z 1) + R') →
      (∀ i k, i ≠ k → t' i = t' k → β' i + g' ≤ α' k ∨ β' k + g' ≤ α' i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
            2 |
          (t' i = 0 ∧ b 1 = z 1 + R' ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 1 ∧ b 0 = z 0 + R' ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i) ∨
          (t' i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  by_cases hc : 0 < c A
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  have hX0 : ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    positivity
  have hXt : ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨c A ^ (6 * j) / ((((N + 1) ^ j : ℕ)) : ℝ≥0∞),
    ENNReal.div_pos (pow_ne_zero _ hc.ne') hXt, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S h s g' J t t' τ α β d α' β' hW hWK hKM hM' hWM' hS hs
    hrM hh hhR hAW hAM hR'L hd hN ht hwin hline hgap hccw hcw hcorner hout hg' hcor' hgap'
  have hM : 1 ≤ M := by omega
  have hκ₁ : 2 * (R' : ℤ) + 2 ≤ A * W := by exact_mod_cast hAW
  have hκ₂ : (W : ℤ) + 2 * K' ≤ A * ((M' : ℤ) - 1) := by
    have h₁ : ((W + 2 * K' : ℕ) : ℤ) ≤ ((A * (M' - 1) : ℕ) : ℤ) := by exact_mod_cast hAM
    push_cast [Nat.cast_sub (by omega : 1 ≤ M')] at h₁
    linarith
  -- the separated event with ends in given bins
  set E : (Fin j → Fin (N + 1)) → Set (Config (LatticeSite 2)) := fun n => {ω : Config
      (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧ (∀ i, b i ∈ {b :
              LatticeSite 2 |
          (t i = 0 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
              : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 1 ∧ (α i + (((n i : Fin (N + 1)) :
              ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
              W) ∨
          (t i = 2 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
              : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 3 ∧ (α i + (((n i : Fin (N + 1)) :
              ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
              W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} with hE
  -- every end in a window lies in a bin of the window
  have hbin : ∀ i (b : LatticeSite 2), b ∈ {b : LatticeSite 2 |
      (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)} → ∃ n : ℕ, n < N + 1 ∧
      b ∈ {b : LatticeSite 2 | (t i = 0 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (n : ℤ) *
          (W + 1)) + W) ∨ (t i = 1 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (n : ℤ) * (W +
          1)) + W) ∨
        (t i = 2 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (n : ℤ) * (W + 1)) + W) ∨ (t i =
            3 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (n : ℤ) * (W + 1)) + W)} := by
    intro i b hb
    simp only [mem_ofPred_eq] at hb
    rcases hb with ⟨ht, -, h₂, h₃⟩ | ⟨ht, -, h₂, h₃⟩ | ⟨ht, -, h₂, h₃⟩ | ⟨ht, -, h₂, h₃⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inl ⟨ht, hn₁, hn₂⟩⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inl ⟨ht, hn₁, hn₂⟩)⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inr (Or.inl ⟨ht, hn₁, hn₂⟩))⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inr (Or.inr ⟨ht, hn₁, hn₂⟩))⟩
  have hcover : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤ ∑ n, law q (E n) := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    rintro ω ⟨a, b, γ, hγ, hd', hH, ho, hsep, hw, hJ⟩
    choose n hn hb using fun i => hbin i (b i) (hw i)
    rw [mem_iUnion]
    refine ⟨fun i => ⟨n i, hn i⟩, ?_⟩
    rw [hE]
    exact ⟨a, b, γ, hγ, hd', hH, ho, hsep, hw, hb, hJ⟩
  -- the stage for each choice of bins
  have hβ : ∀ n, c A ^ (6 * j) * law q (E n) ≤ law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j
      → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
            2 |
          (t' i = 0 ∧ b 1 = z 1 + R' ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 1 ∧ b 0 = z 0 + R' ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i) ∨
          (t' i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    intro n
    -- the empty case
    by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
        (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
        (∀ i, b₀ i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, b₀ i ∈ {b : LatticeSite 2 | (t i = 0 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W +
            1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 1 ∧
            (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N
            + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨
          (t i = 2 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
              : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 3 ∧ (α i + (((n i : Fin (N + 1)) :
              ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
              W)}
    swap
    · refine le_trans (le_of_eq ?_) zero_le
      refine mul_eq_zero_of_right _ ?_
      convert measure_empty (μ := law q)
      ext ω
      simp only [hE, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨a, b, γ, -, -, -, -, -, h₅, h₆, -⟩
      exact hne ⟨ω, a, b, γ, h₅, h₆⟩
    obtain ⟨ω₀, a₀, b₀, γ₀, hW₀, hB₀⟩ := hne
    -- the bins start inside the windows
    have hx : ∀ i, α i ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ∧ (α i + (((n i : Fin
        (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ β i := by
      intro i
      have h₁ := hW₀ i
      have h₂ := hB₀ i
      have h₀ : (0 : ℤ) ≤ (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) := by positivity
      simp only [mem_ofPred_eq] at h₁ h₂
      rcases h₁ with ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ <;>
        rcases h₂ with ⟨ht', h₂, h₂'⟩ | ⟨ht', h₂, h₂'⟩ | ⟨ht', h₂, h₂'⟩ | ⟨ht', h₂, h₂'⟩ <;>
        exact ⟨by omega, by omega⟩
    have hm := fun i => exists_corridor_move_half (col := σ i) (z := z) (r := r) (R := R)
      (R' := R') (M := M) (K := K) (M' := M') (K' := K') (W := W) (D := D) (S := S) (κ := A) hCB hM
      hWK hKM hW hM' hWM' hS hh hhR hκ₁ hκ₂ hR'L (ht i) (hd i) (hwin i) (hx i) (hout i)
      {b : LatticeSite 2 | ((t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)) ∧
        ((t i = 0 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
            : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 1 ∧ (α i + (((n i : Fin (N + 1)) :
            ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
            W) ∨
        (t i = 2 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i :
            Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 3 ∧ (α i + (((n i : Fin (N + 1)) : ℕ)
            : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W))}
            (fun b hb => hb)
    choose gl gh hspec hcor using hm
    have hG : ∀ i k, i ≠ k → Disjoint (Icc (gl i) (gh i)) (Icc (gl k) (gh k)) := by
      intro i k hik
      refine disjoint_Icc_of_lt ?_
      have hR : (M : ℤ) + K' + 1 < R := by
        have := hwin i
        have := hx i
        omega
      exact disjoint_regions_of_moves_half (z₀ := z 0) (z₁ := z 1) (R := R) (R' := R') (h := h)
        (M := M) (M' := M') (K' := K') (W := W) (D := D) (S := S)
        ⟨by positivity, by positivity, by positivity, by positivity, by positivity⟩
        ⟨(hx i).1.trans (hx i).2, (hx k).1.trans (hx k).2⟩ (by exact_mod_cast hS) hR hh hhR
        (hgap i k hik) (hccw i k hik) (hccw k i (Ne.symm hik)) (hcw i k hik)
        (hcw k i (Ne.symm hik))
        ⟨fun h' => (hcorner i k h'.1 h'.2.2.1).1 ⟨h'.2.1, h'.2.2.2⟩,
          fun h' => (hcorner k i h'.1 h'.2.2.1).1 ⟨h'.2.1, h'.2.2.2⟩,
          fun h' => (hcorner i k h'.1 h'.2.2.1).2 ⟨h'.2.1, h'.2.2.2⟩,
          fun h' => (hcorner k i h'.1 h'.2.2.1).2 ⟨h'.2.1, h'.2.2.2⟩⟩ (hspec i) (hspec k)
    have hGH : ∀ i, ∀ v ∈ Icc (gl i) (gh i), z 1 ≤ v 1 := by
      intro i v hv
      rw [mem_Icc_two_iff] at hv
      have h₁ := hline i
      have h₂ := ht i
      have h₃ := hwin i
      have h₄ := hx i
      have hR : (M : ℤ) + K' + 1 < R := by omega
      rcases hspec i with h | h | h | h | h | h | h <;> omega
    refine le_trans (mul_le_mul' le_rfl (measure_mono fun ω hω => ?_))
      ((pow_mul_law_le_law_of_regions_half (q := q) (c := c) (κ := A) (σ := σ) (z := z) (r := r)
        (R := R) (s := s) (M := M) (K := K) (R' := R') (M' := M') (K' := K') hσ hKM hM hrM
        (by omega) hs J _ _ (fun i => Icc (gl i) (gh i)) hG hGH hcor).trans (measure_mono ?_))
    · obtain ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hω
      exact ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, fun i => ⟨h₆ i, h₇ i⟩, h₈⟩
    · rintro ω ⟨a, b', γ', hγ', hd', hH', ho', hJ', hB'⟩
      obtain ⟨hs₁, hs₂⟩ := le_abs_landingPos_sub_of_windows hγ' (by omega) hg' t' α' β'
        (fun i => (hB' i).1) hcor' hgap'
      refine ⟨a, b', γ', hγ', hd', hH', ho', ⟨fun i k hik => ?_, fun i m => ?_,
        fun i => (hB' i).2⟩,
        fun i => (hB' i).1, hJ'⟩
      · rw [← Int.cast_abs]
        exact_mod_cast hs₁ i k hik
      · rw [← Int.cast_abs]
        exact_mod_cast hs₂ i m
  refine (mul_le_mul' le_rfl hcover).trans ?_
  rw [Finset.mul_sum]
  calc ∑ n, c A ^ (6 * j) / ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) * law q (E n)
      ≤ ∑ _n : Fin j → Fin (N + 1), law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j →
          LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
            2 |
          (t' i = 0 ∧ b 1 = z 1 + R' ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 1 ∧ b 0 = z 0 + R' ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i) ∨
          (t' i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ((((N + 1) ^ j : ℕ) : ℝ≥0∞))⁻¹ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul_left (hβ n) _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hX0 hXt, mul_one]


end Stages

end PercLib.Models.Planar
