/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12, and the
arms landing in prescribed windows).
-/
module

public import PercLib.Models.Planar.Arms.RotationGluing

/-!
# The motion plan: separated arms carried into prescribed windows

Separated arms at the outer boundary of `B_R(z)` are carried, through a fixed number of stages of
moves (`exists_pos_le_law_windows_of_moves`), into prescribed windows on the sides of a larger box
`B_{R'}(z)`, in the same counterclockwise order. The plan has two phases: rounds of turns, in which
the last arm of each side turns round the next corner while it has turns left, until every arm is on
the side of its window; then a linear spreading along each side.

## Main results

* `exists_side_window`: a window on a side in counterclockwise coordinates (relative to the centre
  of the side, increasing counterclockwise) and in the coordinates of the stage lemmas.
* `exists_pos_le_law_ccw_of_moves`: the stage of moves (`exists_pos_le_law_windows_of_moves`) in
  counterclockwise coordinates, with the moved windows only required to contain the images.
* `exists_turn_step`: one round of turns (pure combinatorics): the last arm of each side turns
  while it has turns left; the counterclockwise order and the gaps are kept, and the number of
  turns left drops while positive.
* `exists_lift_of_separated`: the bins of separated arms in counterclockwise order, lifted to an
  order of sides and positions (the start of the plan).
* `exists_pos_le_law_target_windows`: **the motion plan**, `c₀ P(separated arms at R with room)
  ≤ P(separated arms ending in prescribed windows at R', fences (M', K'))`, the windows in the
  counterclockwise order of the arms, with `c₀` depending only on `σ`, `c` and the ratios `A`,
  `n`.
* `exists_pos_le_law_target_windows_of_separated`: the same from the separated event of the outer
  separation step (separation `s ≥ 4M` only), through the straight first gluing.

## Implementation notes

A window on side `t` (`0` top, `1` right, `2` bottom, `3` left) is an interval `[u, v]` of
counterclockwise coordinates: the coordinate along the side minus that of `z` on the right and
bottom sides, its negative on the top and left sides. A turn then always lands in `[-h - W, -h]`,
and the last arm of a side is the one with the largest coordinates. The sides are lifted to
integers `lam` (counterclockwise from the bottom side, `lam + t ≡ 2 (mod 4)`), and the arms are
kept in lexicographic order of `(lam, u)` along their index, wrapping once round the box.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Generic lemmas -/

/-- **A linear function above a bound at both ends of an interval** is above it inside. -/
theorem le_add_mul_of_le_of_le {g a b k n : ℤ} (h₀ : g ≤ a) (h₁ : g ≤ a + n * b) (hk : 0 ≤ k)
    (hkn : k ≤ n) : g ≤ a + k * b := by
  rcases le_or_gt 0 b with hb | hb
  · nlinarith
  · nlinarith

/-- **Iteration of a step with an invariant** in `ℝ≥0∞`: if from every state satisfying the
invariant at step `k < n` there is one satisfying it at step `k + 1` with `c u k x ≤ u (k + 1) x'`,
then `c ^ n u 0 x₀ ≤ u n x` for some state `x` satisfying the invariant at step `n`. -/
theorem exists_pow_mul_le_of_forall_exists {X : Type*} {u : ℕ → X → ℝ≥0∞} {I : ℕ → X → Prop}
    {c : ℝ≥0∞} (n : ℕ)
    (h : ∀ k < n, ∀ x, I k x → ∃ x', I (k + 1) x' ∧ c * u k x ≤ u (k + 1) x') (x₀ : X)
    (h₀ : I 0 x₀) : ∃ x, I n x ∧ c ^ n * u 0 x₀ ≤ u n x := by
  induction n with
  | zero => exact ⟨x₀, h₀, by simp⟩
  | succ n ih =>
    obtain ⟨x, hx, hle⟩ := ih fun k hk => h k (by omega)
    obtain ⟨x', hx', hle'⟩ := h n (by omega) x hx
    refine ⟨x', hx', ?_⟩
    calc c ^ (n + 1) * u 0 x₀ = c * (c ^ n * u 0 x₀) := by rw [pow_succ', mul_assoc]
      _ ≤ c * u n x := mul_le_mul' le_rfl hle
      _ ≤ u (n + 1) x' := hle'

/-! ### Windows in counterclockwise coordinates -/

/-- **A window on a side in counterclockwise coordinates.** The counterclockwise window `[u, v]`
on side `t` is the window `[α, β]` of the stage lemmas: `[z₀ - v, z₀ - u]` on the top side,
`[z₁ + u, z₁ + v]` on the right side, `[z₀ + u, z₀ + v]` on the bottom side and `[z₁ - v, z₁ - u]`
on the left side; the ends of arms lying in them are the same. -/
theorem exists_side_window (t : Fin 4) (z : LatticeSite 2) (u v : ℤ) :
    ∃ α β : ℤ, ((t = 0 ∧ α = z 0 - v ∧ β = z 0 - u) ∨ (t = 1 ∧ α = z 1 + u ∧ β = z 1 + v) ∨
      (t = 2 ∧ α = z 0 + u ∧ β = z 0 + v) ∨ (t = 3 ∧ α = z 1 - v ∧ β = z 1 - u)) ∧
      ∀ (ρ : ℕ) (col : Bool) (p : LatticeSite 2),
        ((t = 0 ∧ p 1 = z 1 + ρ ∧ z 0 - v ≤ p 0 ∧ p 0 ≤ z 0 - u) ∨
          (t = 1 ∧ p 0 = z 0 + ρ ∧ z 1 + u ≤ p 1 ∧ p 1 ≤ z 1 + v) ∨
          (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ z 0 + u ≤ p 0 ∧ p 0 ≤ z 0 + v) ∨
          (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ z 1 - v ≤ p 1 ∧ p 1 ≤ z 1 - u)) ↔
        ((t = 0 ∧ p 1 = z 1 + ρ ∧ α ≤ p 0 ∧ p 0 ≤ β) ∨
          (t = 1 ∧ p 0 = z 0 + ρ ∧ α ≤ p 1 ∧ p 1 ≤ β) ∨
          (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ α ≤ p 0 ∧ p 0 ≤ β) ∨
          (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ α ≤ p 1 ∧ p 1 ≤ β)) := by
  fin_cases t
  · exact ⟨z 0 - v, z 0 - u, Or.inl ⟨rfl, rfl, rfl⟩, fun ρ col p => by simp⟩
  · exact ⟨z 1 + u, z 1 + v, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), fun ρ col p => by simp⟩
  · exact ⟨z 0 + u, z 0 + v, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)), fun ρ col p => by simp⟩
  · exact ⟨z 1 - v, z 1 - u, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)), fun ρ col p => by simp⟩

/-- An end in a window lies in every larger window. -/
theorem mem_side_window_of_le {t : Fin 4} {z p : LatticeSite 2} {ρ : ℕ} {col : Bool}
    {α β α' β' : ℤ} (hα : α' ≤ α) (hβ : β ≤ β')
    (h : (t = 0 ∧ p 1 = z 1 + ρ ∧ α ≤ p 0 ∧ p 0 ≤ β) ∨
      (t = 1 ∧ p 0 = z 0 + ρ ∧ α ≤ p 1 ∧ p 1 ≤ β) ∨
      (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ α ≤ p 0 ∧ p 0 ≤ β) ∨
      (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ α ≤ p 1 ∧ p 1 ≤ β)) :
    (t = 0 ∧ p 1 = z 1 + ρ ∧ α' ≤ p 0 ∧ p 0 ≤ β') ∨
      (t = 1 ∧ p 0 = z 0 + ρ ∧ α' ≤ p 1 ∧ p 1 ≤ β') ∨
      (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ α' ≤ p 0 ∧ p 0 ≤ β') ∨
      (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ α' ≤ p 1 ∧ p 1 ≤ β') := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩
  · exact Or.inl ⟨h₀, h₁, hα.trans h₂, h₃.trans hβ⟩
  · exact Or.inr (Or.inl ⟨h₀, h₁, hα.trans h₂, h₃.trans hβ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h₀, h₁, hα.trans h₂, h₃.trans hβ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₀, h₁, hα.trans h₂, h₃.trans hβ⟩))

/-- **A window on a side, from the coordinates of the stage lemmas to counterclockwise
coordinates** (the converse of `exists_side_window`). -/
theorem exists_ccw_window (t : Fin 4) (z : LatticeSite 2) (α β : ℤ) :
    ∃ u v : ℤ, ((t = 0 ∧ α = z 0 - v ∧ β = z 0 - u) ∨ (t = 1 ∧ α = z 1 + u ∧ β = z 1 + v) ∨
      (t = 2 ∧ α = z 0 + u ∧ β = z 0 + v) ∨ (t = 3 ∧ α = z 1 - v ∧ β = z 1 - u)) ∧
      ∀ (ρ : ℕ) (col : Bool) (p : LatticeSite 2),
        ((t = 0 ∧ p 1 = z 1 + ρ ∧ α ≤ p 0 ∧ p 0 ≤ β) ∨
          (t = 1 ∧ p 0 = z 0 + ρ ∧ α ≤ p 1 ∧ p 1 ≤ β) ∨
          (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ α ≤ p 0 ∧ p 0 ≤ β) ∨
          (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ α ≤ p 1 ∧ p 1 ≤ β)) ↔
        ((t = 0 ∧ p 1 = z 1 + ρ ∧ z 0 - v ≤ p 0 ∧ p 0 ≤ z 0 - u) ∨
          (t = 1 ∧ p 0 = z 0 + ρ ∧ z 1 + u ≤ p 1 ∧ p 1 ≤ z 1 + v) ∨
          (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ z 0 + u ≤ p 0 ∧ p 0 ≤ z 0 + v) ∨
          (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ z 1 - v ≤ p 1 ∧ p 1 ≤ z 1 - u)) := by
  fin_cases t
  · exact ⟨z 0 - β, z 0 - α, Or.inl ⟨rfl, by ring, by ring⟩, fun ρ col p => by simp⟩
  · exact ⟨α - z 1, β - z 1, Or.inr (Or.inl ⟨rfl, by ring, by ring⟩), fun ρ col p => by simp⟩
  · exact ⟨α - z 0, β - z 0, Or.inr (Or.inr (Or.inl ⟨rfl, by ring, by ring⟩)),
      fun ρ col p => by simp⟩
  · exact ⟨z 1 - β, z 1 - α, Or.inr (Or.inr (Or.inr ⟨rfl, by ring, by ring⟩)),
      fun ρ col p => by simp⟩

/-- An end in a window in counterclockwise coordinates lies in every larger window. -/
theorem mem_ccw_window_of_le {t : Fin 4} {z p : LatticeSite 2} {ρ : ℕ} {col : Bool}
    {u v u' v' : ℤ} (hu : u' ≤ u) (hv : v ≤ v')
    (h : (t = 0 ∧ p 1 = z 1 + ρ ∧ z 0 - v ≤ p 0 ∧ p 0 ≤ z 0 - u) ∨
      (t = 1 ∧ p 0 = z 0 + ρ ∧ z 1 + u ≤ p 1 ∧ p 1 ≤ z 1 + v) ∨
      (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ z 0 + u ≤ p 0 ∧ p 0 ≤ z 0 + v) ∨
      (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ z 1 - v ≤ p 1 ∧ p 1 ≤ z 1 - u)) :
    (t = 0 ∧ p 1 = z 1 + ρ ∧ z 0 - v' ≤ p 0 ∧ p 0 ≤ z 0 - u') ∨
      (t = 1 ∧ p 0 = z 0 + ρ ∧ z 1 + u' ≤ p 1 ∧ p 1 ≤ z 1 + v') ∨
      (t = 2 ∧ p 1 = z 1 - ρ - cond col 0 1 ∧ z 0 + u' ≤ p 0 ∧ p 0 ≤ z 0 + v') ∨
      (t = 3 ∧ p 0 = z 0 - ρ - cond col 0 1 ∧ z 1 - v' ≤ p 1 ∧ p 1 ≤ z 1 - u') := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩
  · exact Or.inl ⟨h₀, h₁, by linarith, by linarith⟩
  · exact Or.inr (Or.inl ⟨h₀, h₁, by linarith, by linarith⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h₀, h₁, by linarith, by linarith⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₀, h₁, by linarith, by linarith⟩))

section Stage

variable {j : ℕ}

/-- The side coordinate of the centre `z` on side `t`, for a side window in counterclockwise
coordinates. -/
theorem side_center_eq {t : Fin 4} {z : LatticeSite 2} {α β u v : ℤ}
    (h : (t = 0 ∧ α = z 0 - v ∧ β = z 0 - u) ∨ (t = 1 ∧ α = z 1 + u ∧ β = z 1 + v) ∨
      (t = 2 ∧ α = z 0 + u ∧ β = z 0 + v) ∨ (t = 3 ∧ α = z 1 - v ∧ β = z 1 - u)) :
    ((t = 1 ∨ t = 2) ∧ α = (if t = 0 ∨ t = 2 then z 0 else z 1) + u ∧
        β = (if t = 0 ∨ t = 2 then z 0 else z 1) + v) ∨
      ((t = 0 ∨ t = 3) ∧ α = (if t = 0 ∨ t = 2 then z 0 else z 1) - v ∧
        β = (if t = 0 ∨ t = 2 then z 0 else z 1) - u) := by
  rcases h with ⟨rfl, hα, hβ⟩ | ⟨rfl, hα, hβ⟩ | ⟨rfl, hα, hβ⟩ | ⟨rfl, hα, hβ⟩
  · exact Or.inr ⟨Or.inl rfl, by simp [hα], by simp [hβ]⟩
  · exact Or.inl ⟨Or.inl rfl, by simp [hα], by simp [hβ]⟩
  · exact Or.inl ⟨Or.inr rfl, by simp [hα], by simp [hβ]⟩
  · exact Or.inr ⟨Or.inr rfl, by simp [hα], by simp [hβ]⟩

/-- **The stage of moves in counterclockwise coordinates** (`exists_pos_le_law_windows_of_moves`).
Windows `[u i, v i]` on the sides `t i` of `B_R(z)` in counterclockwise coordinates, at least `S`
from the corners and from each other on one side; arm `i` jogs by `e i` counterclockwise
(`τ i = false`) or, when it is the last of its side, turns round the next corner counterclockwise
at the level `h` (`τ i = true`, landing in `[-h - W, -h]` on the next side). The new windows
`[u' i, v' i]` only need to contain the images (`[u + e - W, v + e + W]` for a jog). The constant
depends only on `σ`, `c`, `A`, `N`. -/
theorem exists_pos_le_law_ccw_of_moves (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S : ℕ) (h : ℤ) (s : ℝ)
      (g' : ℤ) (J : Fin j → Set ℤ) (t t' : Fin j → Fin 4) (τ : Fin j → Bool)
      (u v e u' v' : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2 * D + 2 * M + 2 * K' + 3 ≤ S →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → (R : ℤ) + M + 1 ≤ h → h + W + M' ≤ R' →
      2 * R' + 2 ≤ A * W → W + 2 * K' ≤ A * (M' - 1) → (R' : ℕ∞) ≤ L →
      (∀ i, -(D : ℤ) ≤ e i ∧ e i ≤ D) → (∀ i, v i - u i + 1 ≤ N * ((W : ℤ) + 1)) →
      (∀ i, -(R : ℤ) + S ≤ u i ∧ v i + S ≤ R) →
      (∀ i k, i ≠ k → t i = t k → v i + S ≤ u k ∨ v k + S ≤ u i) →
      (∀ i k, i ≠ k → τ i = true → t k = t i → v k + S ≤ u i) →
      (∀ i, (τ i = false ∧ t' i = t i ∧ u' i ≤ u i + e i - W ∧ v i + e i + W ≤ v' i) ∨
        (τ i = true ∧ ((t i = 1 ∧ t' i = 0) ∨ (t i = 0 ∧ t' i = 3) ∨ (t i = 3 ∧ t' i = 2) ∨
          (t i = 2 ∧ t' i = 1)) ∧ u' i ≤ -h - W ∧ -h ≤ v' i)) →
      1 ≤ g' → (∀ i, -(R' : ℤ) + g' ≤ u' i ∧ v' i + g' ≤ R') →
      (∀ i k, i ≠ k → t' i = t' k → v' i + g' ≤ u' k ∨ v' k + g' ≤ u' i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + R ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
          (t i = 1 ∧ b i 0 = z 0 + R ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
          (t i = 2 ∧ b i 1 = z 1 - R - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧ b i 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ b i 0 = z 0 - R - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧ b i 1 ≤ z 1 - u i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i,
          (t' i = 0 ∧ b i 1 = z 1 + R' ∧ z 0 - v' i ≤ b i 0 ∧ b i 0 ≤ z 0 - u' i) ∨
          (t' i = 1 ∧ b i 0 = z 0 + R' ∧ z 1 + u' i ≤ b i 1 ∧ b i 1 ≤ z 1 + v' i) ∨
          (t' i = 2 ∧ b i 1 = z 1 - R' - cond (σ i) 0 1 ∧ z 0 + u' i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v' i) ∨
          (t' i = 3 ∧ b i 0 = z 0 - R' - cond (σ i) 0 1 ∧ z 1 - v' i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u' i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₀, hc₀, hst⟩ := exists_pos_le_law_windows_of_moves σ hσ c A N
  refine ⟨c₀, hc₀, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S h s g' J t t' τ u v e u' v' hW hWK hKM hM' hWM' hS hs
    hrM hh hhR hAW hAM hR'L he hN hwin hgap hccw hout hg' hcor' hgap'
  choose α β hαβ hmem using fun i => exists_side_window (t i) z (u i) (v i)
  choose α₁ β₁ hαβ₁ hmem₁ using fun i => exists_side_window (t' i) z (u' i) (v' i)
  -- the exact moves of the stage lemma, inside the given windows
  have hmove : ∀ i, ∃ d α' β' : ℤ, (-(D : ℤ) ≤ d ∧ d ≤ D) ∧
      ((τ i = false ∧ t' i = t i ∧ α' = α i + d ∧ β' = β i + d + W) ∨
        (τ i = true ∧ ((t i = 1 ∧ t' i = 0 ∧ α' = z 0 + h ∧ β' = z 0 + h + W) ∨
          (t i = 0 ∧ t' i = 3 ∧ α' = z 1 + h ∧ β' = z 1 + h + W) ∨
          (t i = 3 ∧ t' i = 2 ∧ α' = z 0 - h - W ∧ β' = z 0 - h) ∨
          (t i = 2 ∧ t' i = 1 ∧ α' = z 1 - h - W ∧ β' = z 1 - h)))) ∧
      α₁ i ≤ α' ∧ β' ≤ β₁ i := by
    intro i
    have hei := he i
    rcases hout i with ⟨hτ, ht, hu, hv⟩ | ⟨hτ, hturn, hu, hv⟩
    · rcases hαβ i with ⟨h₀, hα, hβ⟩ | ⟨h₀, hα, hβ⟩ | ⟨h₀, hα, hβ⟩ | ⟨h₀, hα, hβ⟩
      · refine ⟨-e i, α i + -e i, β i + -e i + W, by omega, Or.inl ⟨hτ, ht, rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨e i, α i + e i, β i + e i + W, by omega, Or.inl ⟨hτ, ht, rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨e i, α i + e i, β i + e i + W, by omega, Or.inl ⟨hτ, ht, rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨-e i, α i + -e i, β i + -e i + W, by omega, Or.inl ⟨hτ, ht, rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
    · rcases hturn with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · refine ⟨0, z 0 + h, z 0 + h + W, by omega, Or.inr ⟨hτ, Or.inl ⟨h₀, h₁, rfl, rfl⟩⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨0, z 1 + h, z 1 + h + W, by omega,
          Or.inr ⟨hτ, Or.inr (Or.inl ⟨h₀, h₁, rfl, rfl⟩)⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨0, z 0 - h - W, z 0 - h, by omega,
          Or.inr ⟨hτ, Or.inr (Or.inr (Or.inl ⟨h₀, h₁, rfl, rfl⟩))⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨0, z 1 - h - W, z 1 - h, by omega,
          Or.inr ⟨hτ, Or.inr (Or.inr (Or.inr ⟨h₀, h₁, rfl, rfl⟩))⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
  choose d α' β' hd hmv hle using hmove
  have hc := fun i => side_center_eq (hαβ i)
  have hc₁ := fun i => side_center_eq (hαβ₁ i)
  have key := hst q L hCB z r R R' W M K M' K' D S h s g' J t t' τ α β d α' β' hW hWK hKM hM'
    hWM' hS hs hrM hh hhR hAW hAM hR'L hd (fun i => by
      have : β i - α i = v i - u i := by rcases hc i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega
      linarith [hN i])
    (fun i => by have := hwin i; rcases hc i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega)
    (fun i k hik htk => by
      have h₁ := hgap i k hik htk
      have h₂ := hc k
      rw [← htk] at h₂
      rcases hc i with ⟨ho, hαi, hβi⟩ | ⟨ho, hαi, hβi⟩ <;>
        rcases h₂ with ⟨ho', hαk, hβk⟩ | ⟨ho', hαk, hβk⟩ <;> omega)
    (fun i k hik hτ htk => by
      have h₁ := hccw i k hik hτ htk
      have h₂ := hc k
      rw [htk] at h₂
      rcases hc i with ⟨ho, hαi, hβi⟩ | ⟨ho, hαi, hβi⟩ <;>
        rcases h₂ with ⟨ho', hαk, hβk⟩ | ⟨ho', hαk, hβk⟩ <;> omega)
    hmv hg'
    (fun i => by
      have := hcor' i
      have := hle i
      rcases hc₁ i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega)
    (fun i k hik htk => by
      have h₁ := hgap' i k hik htk
      have h₂ := hc₁ k
      have h₃ := hle i
      have h₄ := hle k
      rw [← htk] at h₂
      rcases hc₁ i with ⟨ho, hαi, hβi⟩ | ⟨ho, hαi, hβi⟩ <;>
        rcases h₂ with ⟨ho', hαk, hβk⟩ | ⟨ho', hαk, hβk⟩ <;> omega)
  refine (mul_le_mul' le_rfl (measure_mono ?_)).trans (key.trans (measure_mono ?_))
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, fun i => (hmem i R (σ i) (b i)).1 (h₅ i), h₆⟩
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, fun i => (hmem₁ i R' (σ i) (b i)).2
      (mem_side_window_of_le (hle i).1 (hle i).2 (h₅ i)), h₆⟩

end Stage

/-! ### Rounds of turns -/

section Turns

variable {m : ℕ}

/-- A counterclockwise turn changes the side `t` to `t - 1`. -/
theorem turn_side_rel (x : Fin 4) : (x = 1 ∧ x - 1 = 0) ∨ (x = 0 ∧ x - 1 = 3) ∨
    (x = 3 ∧ x - 1 = 2) ∨ (x = 2 ∧ x - 1 = 1) := by
  fin_cases x <;> decide

theorem val_sub_one_fin_four (x : Fin 4) : ((x - 1 : Fin 4) : ℕ) = ((x : ℕ) + 3) % 4 := by
  fin_cases x <;> rfl

/-- **Arms on one side are apart.** For windows in counterclockwise coordinates whose arms are in
lexicographic order of lifted side and position along their index, wrapping at most once round the
box (`lam (last) ≤ lam 0 + 4`), with gaps `G ≥ 0`: two arms on the same side are `G` apart. -/
theorem gap_of_lex {lam u v : Fin (m + 1) → ℤ} {t : Fin (m + 1) → Fin 4} {G : ℤ} (hG : 0 ≤ G)
    (hc : ∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2)
    (hL1 : ∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l))
    (hL2 : lam (Fin.last m) < lam 0 + 4 ∨
      (lam (Fin.last m) = lam 0 + 4 ∧ v (Fin.last m) + G ≤ u 0))
    (huv : ∀ i, u i ≤ v i) :
    ∀ i k, i ≠ k → t i = t k → v i + G ≤ u k ∨ v k + G ≤ u i := by
  have hmono : ∀ i l, i ≤ l → lam i ≤ lam l := fun i l hil => by
    rcases hil.lt_or_eq with h | h
    · rcases hL1 i l h with h | h <;> omega
    · rw [h]
  have hlo : ∀ i, lam 0 ≤ lam i := fun i => hmono 0 i (Fin.zero_le i)
  have hhi : ∀ i, lam i ≤ lam 0 + 4 := fun i => by
    have := hmono i (Fin.last m) (Fin.le_last i)
    rcases hL2 with h | h <;> omega
  -- the two arms of one side lifted four sides apart are the last and the first
  have key : ∀ i k, i < k → t i = t k → v i + G ≤ u k ∨ v k + G ≤ u i := by
    intro i k hik htk
    have h₁ := hc i
    have h₂ := hc k
    rw [htk] at h₁
    have h₃ := hmono i k hik.le
    have h₄ := hlo i
    have h₅ := hhi k
    rcases hL1 i k hik with h | h
    · -- `lam k = lam i + 4`: `i` is in the first block and `k` in the last
      right
      have hlast : v k ≤ v (Fin.last m) := by
        rcases (Fin.le_last k).lt_or_eq with h' | h'
        · have := hhi (Fin.last m)
          have := huv (Fin.last m)
          rcases hL1 k _ h' with h'' | h'' <;> omega
        · rw [h']
      have hfirst : u 0 ≤ u i := by
        rcases (Fin.zero_le i).lt_or_eq with h' | h'
        · have := huv 0
          rcases hL1 0 i h' with h'' | h'' <;> omega
        · rw [h']
      have := hmono k (Fin.last m) (Fin.le_last k)
      rcases hL2 with h' | h' <;> omega
    · exact Or.inl h.2
  intro i k hik htk
  rcases lt_or_gt_of_ne hik with h | h
  · exact key i k h htk
  · exact (key k i h htk.symm).symm

/-- **One round of turns** (pure combinatorics). Windows `[u i, v i]` in counterclockwise
coordinates on the sides `t i` of `B_ρ(z)`, at least `G` from the corners, with lifted sides
`lam i` (`lam i + t i ≡ 2 (mod 4)`) in lexicographic order of `(lam, u)` along the index with gaps
`G`, wrapping at most once round the box; target lifted sides `lamT ≥ lam`, nondecreasing, within
four sides. The last arm of each side turns round the next corner (landing in `[-h - W, -h]`) if it
has turns left; the other arms stay and their windows widen by `W` at both ends. Then the new arms
satisfy the same conditions at `B_{ρ'}(z)` with gaps `G - 2W`, every turning arm is the last of its
side, and the number of turns left, `Σ (lamT - lam)`, drops while positive. -/
theorem exists_turn_step {lam lamT u v : Fin (m + 1) → ℤ} {t : Fin (m + 1) → Fin 4}
    {ρ ρ' W G h : ℤ} (hW : 0 ≤ W) (hG : 2 * W ≤ G)
    (hc : ∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2)
    (hL1 : ∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l))
    (hL2 : lam (Fin.last m) < lam 0 + 4 ∨
      (lam (Fin.last m) = lam 0 + 4 ∧ v (Fin.last m) + G ≤ u 0))
    (hL3 : ∀ i, -ρ + G ≤ u i ∧ v i + G ≤ ρ ∧ u i ≤ v i)
    (hT1 : ∀ i, lam i ≤ lamT i) (hT2 : ∀ i l, i ≤ l → lamT i ≤ lamT l)
    (hT3 : lamT (Fin.last m) ≤ lamT 0 + 4)
    (hρh : ρ ≤ h + W) (hρ' : h + W + (G - 2 * W) ≤ ρ') (hρρ' : ρ ≤ ρ') :
    ∃ (τ : Fin (m + 1) → Bool) (lam' : Fin (m + 1) → ℤ) (t' : Fin (m + 1) → Fin 4)
      (u' v' : Fin (m + 1) → ℤ),
      (∀ i k, i ≠ k → τ i = true → t k = t i → v k + G ≤ u i) ∧
      (∀ i, (τ i = false ∧ t' i = t i ∧ lam' i = lam i ∧ u' i = u i - W ∧ v' i = v i + W) ∨
        (τ i = true ∧ ((t i = 1 ∧ t' i = 0) ∨ (t i = 0 ∧ t' i = 3) ∨ (t i = 3 ∧ t' i = 2) ∨
          (t i = 2 ∧ t' i = 1)) ∧ lam' i = lam i + 1 ∧ u' i = -h - W ∧ v' i = -h)) ∧
      (∀ i, (lam' i + ((t' i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i l, i < l → lam' i < lam' l ∨ (lam' i = lam' l ∧ v' i + (G - 2 * W) ≤ u' l)) ∧
      (lam' (Fin.last m) < lam' 0 + 4 ∨
        (lam' (Fin.last m) = lam' 0 + 4 ∧ v' (Fin.last m) + (G - 2 * W) ≤ u' 0)) ∧
      (∀ i, -ρ' + (G - 2 * W) ≤ u' i ∧ v' i + (G - 2 * W) ≤ ρ' ∧ u' i ≤ v' i) ∧
      (∀ i, lam' i ≤ lamT i) ∧
      (∑ i, (lamT i - lam' i) ≤ ∑ i, (lamT i - lam i)) ∧
      (0 < ∑ i, (lamT i - lam i) → ∑ i, (lamT i - lam' i) < ∑ i, (lamT i - lam i)) := by
  classical
  have hmono : ∀ i l, i ≤ l → lam i ≤ lam l := fun i l hil => by
    rcases hil.lt_or_eq with h | h
    · rcases hL1 i l h with h | h <;> omega
    · rw [h]
  have hlo : ∀ i, lam 0 ≤ lam i := fun i => hmono 0 i (Fin.zero_le i)
  have hhi : ∀ i, lam i ≤ lam 0 + 4 := fun i => by
    have := hmono i (Fin.last m) (Fin.le_last i)
    rcases hL2 with h | h <;> omega
  have hρG : G ≤ ρ := by have := hL3 0; omega
  -- the turning rule: the last arm of its side, with turns left
  obtain ⟨P, hP⟩ : ∃ P : Fin (m + 1) → Prop, ∀ i, P i ↔
      (lam i < lamT i ∧ (∀ l, i < l → lam i < lam l) ∧ lam i < lam 0 + 4) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨lam', hlam'⟩ : ∃ f : Fin (m + 1) → ℤ, ∀ i, f i = if P i then lam i + 1 else lam i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨t', ht'⟩ : ∃ f : Fin (m + 1) → Fin 4, ∀ i, f i = if P i then t i - 1 else t i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨u', hu'⟩ : ∃ f : Fin (m + 1) → ℤ, ∀ i, f i = if P i then -h - W else u i - W :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v', hv'⟩ : ∃ f : Fin (m + 1) → ℤ, ∀ i, f i = if P i then -h else v i + W :=
    ⟨_, fun _ => rfl⟩
  have hcase : ∀ i, (P i ∧ lam' i = lam i + 1 ∧ t' i = t i - 1 ∧ u' i = -h - W ∧ v' i = -h) ∨
      (¬ P i ∧ lam' i = lam i ∧ t' i = t i ∧ u' i = u i - W ∧ v' i = v i + W) := fun i => by
    by_cases hPi : P i
    · exact Or.inl ⟨hPi, by rw [hlam', ite_eq_left hPi], by rw [ht', ite_eq_left hPi],
        by rw [hu', ite_eq_left hPi], by rw [hv', ite_eq_left hPi]⟩
    · exact Or.inr ⟨hPi, by rw [hlam', ite_eq_right hPi], by rw [ht', ite_eq_right hPi],
        by rw [hu', ite_eq_right hPi], by rw [hv', ite_eq_right hPi]⟩
  -- a turning arm is the last of its side
  have hlast : ∀ i k, i ≠ k → P i → t k = t i → v k + G ≤ u i := by
    intro i k hik hPi htk
    obtain ⟨hTi, hall, h4⟩ := (hP i).1 hPi
    have h₁ := hc i
    have h₂ := hc k
    rw [htk] at h₂
    have := hlo k
    have := hhi k
    have := hlo i
    rcases lt_or_gt_of_ne hik with hlt | hlt
    · have := hall k hlt
      -- `lam k = lam i + 4 = lam 0 + 4`
      have hv : v k ≤ v (Fin.last m) := by
        rcases (Fin.le_last k).lt_or_eq with h' | h'
        · have := (hL3 (Fin.last m)).2.2
          have := hmono k (Fin.last m) (Fin.le_last k)
          rcases hL1 k _ h' with h'' | h'' <;> omega
        · rw [h']
      have hu : u 0 ≤ u i := by
        rcases (Fin.zero_le i).lt_or_eq with h' | h'
        · have := (hL3 0).2.2
          rcases hL1 0 i h' with h'' | h'' <;> omega
        · rw [h']
      have := hmono k (Fin.last m) (Fin.le_last k)
      rcases hL2 with h' | h' <;> omega
    · rcases hL1 k i hlt with h' | h' <;> omega
  refine ⟨fun i => decide (P i), lam', t', u', v', fun i k hik hτ htk => hlast i k hik
    (decide_eq_true_iff.1 hτ) htk, fun i => ?_, fun i => ?_, fun i l hil => ?_, ?_, fun i => ?_,
    fun i => ?_, ?_, fun hpos => ?_⟩
  · rcases hcase i with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩
    · refine Or.inr ⟨decide_eq_true hPi, ?_, h₁, h₃, h₄⟩
      rw [h₂]
      exact turn_side_rel (t i)
    · exact Or.inl ⟨decide_eq_false hPi, h₂, h₁, h₃, h₄⟩
  · have := hc i
    rcases hcase i with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩
    · rw [h₁, h₂, val_sub_one_fin_four]
      have := (t i).isLt
      omega
    · rw [h₁, h₂]
      exact this
  · have hli := hmono i l hil.le
    rcases hcase i with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩ <;>
      rcases hcase l with ⟨hPl, h₅, h₆, h₇, h₈⟩ | ⟨hPl, h₅, h₆, h₇, h₈⟩
    · have := ((hP i).1 hPi).2.1 l hil
      omega
    · have := ((hP i).1 hPi).2.1 l hil
      have := hL3 l
      omega
    · omega
    · rcases hL1 i l hil with h | h <;> omega
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      left
      change lam' 0 < lam' 0 + 4
      omega
    have hl0 : (0 : Fin (m + 1)) < Fin.last m := by
      rw [Fin.lt_def]
      simp only [Fin.val_zero, Fin.val_last]
      exact hm
    have := hmono 0 (Fin.last m) hl0.le
    have := hL3 0
    have := hL3 (Fin.last m)
    rcases hcase (Fin.last m) with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩ <;>
      rcases hcase 0 with ⟨hPl, h₅, h₆, h₇, h₈⟩ | ⟨hPl, h₅, h₆, h₇, h₈⟩
    · have := ((hP _).1 hPi).2.2
      omega
    · have := ((hP _).1 hPi).2.2
      omega
    · rcases hL2 with h | h <;> omega
    · rcases hL2 with h | h <;> omega
  · have := hL3 i
    rcases hcase i with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩ <;> omega
  · have := hT1 i
    rcases hcase i with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩
    · have := ((hP i).1 hPi).1
      omega
    · omega
  · refine Finset.sum_le_sum fun i _ => ?_
    rcases hcase i with ⟨hPi, h₁, h₂, h₃, h₄⟩ | ⟨hPi, h₁, h₂, h₃, h₄⟩ <;> omega
  · -- some arm turns
    have hex : ∃ i, P i := by
      obtain ⟨i₀, hi₀⟩ : ∃ i, lam i < lamT i := by
        by_contra hne
        push Not at hne
        have : ∑ i, (lamT i - lam i) ≤ 0 :=
          Finset.sum_nonpos fun i _ => by have := hne i; omega
        omega
      set S := Finset.univ.filter fun i => lam i < lamT i with hS
      have hSne : S.Nonempty := ⟨i₀, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi₀⟩⟩
      set i₁ := S.max' hSne with hi₁
      have hi₁S : lam i₁ < lamT i₁ := by
        have := S.max'_mem hSne
        rw [← hi₁, hS, Finset.mem_filter] at this
        exact this.2
      have hi₁max : ∀ l, i₁ < l → lamT l ≤ lam l := fun l hl => by
        by_contra hlt
        push Not at hlt
        have : l ≤ i₁ := S.le_max' l (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩)
        exact absurd hl (not_lt.2 this)
      by_cases hall : ∀ l, i₁ < l → lam i₁ < lam l
      · by_cases h4 : lam i₁ < lam 0 + 4
        · exact ⟨i₁, (hP i₁).2 ⟨hi₁S, hall, h4⟩⟩
        · -- the arms of the first block have turns left
          have h0T : lam 0 < lamT 0 := by
            have := hT2 i₁ (Fin.last m) (Fin.le_last _)
            have := hhi i₁
            omega
          set S₀ := Finset.univ.filter fun i => lam i = lam 0 with hS₀
          have hS₀ne : S₀.Nonempty :=
            ⟨0, by rw [hS₀, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩⟩
          set i₂ := S₀.max' hS₀ne with hi₂
          have hi₂S : lam i₂ = lam 0 := by
            have := S₀.max'_mem hS₀ne
            rw [← hi₂, hS₀, Finset.mem_filter] at this
            exact this.2
          refine ⟨i₂, (hP i₂).2 ⟨?_, fun l hl => ?_, by omega⟩⟩
          · have := hT2 0 i₂ (Fin.zero_le _)
            omega
          · have h₁ := hlo l
            have h₂ : lam l ≠ lam 0 := fun heq => by
              have : l ≤ i₂ :=
                S₀.le_max' l (by rw [hS₀, Finset.mem_filter]; exact ⟨Finset.mem_univ _, heq⟩)
              exact absurd hl (not_lt.2 this)
            omega
      · push Not at hall
        obtain ⟨l, hl, hle⟩ := hall
        have := hmono i₁ l hl.le
        have := hT2 i₁ l hl.le
        have := hi₁max l hl
        omega
    obtain ⟨i, hPi⟩ := hex
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rcases hcase k with ⟨hPk, h₁, h₂, h₃, h₄⟩ | ⟨hPk, h₁, h₂, h₃, h₄⟩ <;> omega
    · rcases hcase i with ⟨hPi', h₁, h₂, h₃, h₄⟩ | ⟨hPi', h₁, h₂, h₃, h₄⟩
      · omega
      · exact absurd hPi hPi'

end Turns

/-! ### The start of the plan -/

section Start

variable {m : ℕ}

/-- **Lifting a cyclic order.** Positions `L i` in `[S, Q - S]`, pairwise at least `S > 0` apart,
in counterclockwise cyclic order along the index: adding `Q` to the positions below `L 0` gives
positions increasing along the index by at least `S`, the last at least `S` below `L 0 + Q`. -/
theorem lift_add_le_of_sbtw {L P : Fin (m + 1) → ℤ} {Q S : ℤ} (hS : 0 < S)
    (hord : ∀ i k l, i < k → k < l → sbtw (L i) (L k) (L l))
    (hgap : ∀ i k, i ≠ k → S ≤ |L i - L k|) (hrange : ∀ i, S ≤ L i ∧ L i + S ≤ Q)
    (hP : ∀ i, (L i < L 0 ∧ P i = L i + Q) ∨ (L 0 ≤ L i ∧ P i = L i)) :
    (∀ i l, i < l → P i + S ≤ P l) ∧ P (Fin.last m) + S ≤ P 0 + Q := by
  have hP0 : P 0 = L 0 := by rcases hP 0 with h | h <;> omega
  refine ⟨fun i l hil => ?_, ?_⟩
  · have hl := hP l
    have hi := hP i
    have hrl := hrange l
    have hri := hrange i
    have hr0 := hrange 0
    have hgl := le_abs.1 (hgap i l hil.ne)
    rcases (Fin.zero_le i).lt_or_eq with h0 | h0
    · have h₁ := Int.sbtw_iff.1 (hord 0 i l h0 hil)
      omega
    · subst h0
      omega
  · rcases (Fin.zero_le (Fin.last m)).lt_or_eq with h0 | h0
    · have := le_abs.1 (hgap 0 (Fin.last m) h0.ne)
      have := hP (Fin.last m)
      have := hrange (Fin.last m)
      have := hrange 0
      omega
    · rw [← h0]
      have := hrange 0
      omega

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ}

/-- The landing position of an arm ending in a window on a side, in counterclockwise
coordinates: `L = 4R c + x` with `c` the side counted counterclockwise from the bottom side
(`c + t ≡ 2 (mod 4)`) and `x ∈ [2u + 2R - 1, 2v + 2R + 1]`; when the landing position is at least
`S ≥ 4` from the doubled corners, `x ∈ [S, 4R - S]`. -/
theorem IsArm.exists_landingPos_eq_of_window {col : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (hγ : IsArm ω col z r (z - R) (z + R) γ) (hrR : r < R) {S : ℤ}
    (hS : 4 ≤ S) (hcor : ∀ m' : ℕ, S ≤ |landingPos (z - R) (z + R) col γ - 4 * m' * R|)
    {t : Fin 4} {u v : ℤ}
    (hw : (t = 0 ∧ b 1 = z 1 + R ∧ z 0 - v ≤ b 0 ∧ b 0 ≤ z 0 - u) ∨
      (t = 1 ∧ b 0 = z 0 + R ∧ z 1 + u ≤ b 1 ∧ b 1 ≤ z 1 + v) ∨
      (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ z 0 + u ≤ b 0 ∧ b 0 ≤ z 0 + v) ∨
      (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ z 1 - v ≤ b 1 ∧ b 1 ≤ z 1 - u)) :
    ∃ c x : ℤ, 0 ≤ c ∧ c ≤ 3 ∧ (c + ((t : ℕ) : ℤ)) % 4 = 2 ∧
      landingPos (z - R) (z + R) col γ = 4 * R * c + x ∧ S ≤ x ∧ x + S ≤ 4 * R ∧
      2 * u + 2 * R - 1 ≤ x ∧ x ≤ 2 * v + 2 * R + 1 ∧
      S ≤ landingPos (z - R) (z + R) col γ ∧ landingPos (z - R) (z + R) col γ + S ≤ 16 * R := by
  have he : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  have hb := hγ.end_mem_Icc (Icc_subset_Icc_add_one_sub_one hrR)
  rw [mem_Icc_two_iff] at hb
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hb
  have c0 := le_abs.1 (hcor 0)
  have c1 := le_abs.1 (hcor 1)
  have c2 := le_abs.1 (hcor 2)
  have c3 := le_abs.1 (hcor 3)
  have c4 := le_abs.1 (hcor 4)
  push_cast at c0 c1 c2 c3 c4
  rcases hw with ⟨ht, hb₁, h₁, h₂⟩ | ⟨ht, hb₁, h₁, h₂⟩ | ⟨ht, hb₁, h₁, h₂⟩ | ⟨ht, hb₁, h₁, h₂⟩
  · have hL := hγ.landingPos_eq_of_top hrR hb₁
    subst ht
    refine ⟨2, landingPos (z - R) (z + R) col γ - 8 * R, by norm_num, by norm_num, by decide,
      by ring, ?_⟩
    rw [hL] at c0 c1 c2 c3 c4 ⊢
    omega
  · have hL := hγ.landingPos_eq_of_right hrR hb₁
    subst ht
    refine ⟨1, landingPos (z - R) (z + R) col γ - 4 * R, by norm_num, by norm_num, by decide,
      by ring, ?_⟩
    rw [hL] at c0 c1 c2 c3 c4 ⊢
    omega
  · have hL := hγ.landingPos_eq_of_bottom hrR hb₁
    subst ht
    refine ⟨0, landingPos (z - R) (z + R) col γ, by norm_num, by norm_num, by decide,
      by ring, ?_⟩
    rw [hL] at c0 c1 c2 c3 c4 ⊢
    omega
  · have hL := hγ.landingPos_eq_of_left hrR hb₁
    subst ht
    refine ⟨3, landingPos (z - R) (z + R) col γ - 12 * R, by norm_num, by norm_num, by decide,
      by ring, ?_⟩
    rw [hL] at c0 c1 c2 c3 c4 ⊢
    omega

/-- **The start of the plan.** Arms to `∂B_R(z)` in counterclockwise order, with landing
positions at least `S` apart and from the doubled corners, ending in windows `[u i, u i + W]` in
counterclockwise coordinates on the sides `t i`, with `2G + 4W + 2 ≤ S`: there are lifted sides
`lam i ∈ [0, 7]` (`lam i + t i ≡ 2 (mod 4)`) such that the windows are in lexicographic order of
`(lam, u)` along the index with gaps `G`, wrapping at most once round the box, and at least `G` from
the corners. -/
theorem exists_lift_of_separated {σ : Fin (m + 1) → Bool} {R : ℕ}
    {a b : Fin (m + 1) → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hrR : r < R)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
      (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l)))
    {S G W : ℤ} (hW : 0 ≤ W) (hG : 1 ≤ G) (hS : 2 * G + 4 * W + 2 ≤ S)
    (hsep : ∀ i k, i ≠ k → S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    (hcor : ∀ i (m' : ℕ), S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m' * R|)
    (t : Fin (m + 1) → Fin 4) (u v : Fin (m + 1) → ℤ) (hv : ∀ i, v i = u i + W)
    (hw : ∀ i, (t i = 0 ∧ b i 1 = z 1 + R ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
      (t i = 1 ∧ b i 0 = z 0 + R ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
      (t i = 2 ∧ b i 1 = z 1 - R - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧ b i 0 ≤ z 0 + v i) ∨
      (t i = 3 ∧ b i 0 = z 0 - R - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧ b i 1 ≤ z 1 - u i)) :
    ∃ lam : Fin (m + 1) → ℤ, (∀ i, 0 ≤ lam i ∧ lam i ≤ 7) ∧
      (∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l)) ∧
      (lam (Fin.last m) < lam 0 + 4 ∨
        (lam (Fin.last m) = lam 0 + 4 ∧ v (Fin.last m) + G ≤ u 0)) ∧
      (∀ i, -(R : ℤ) + G ≤ u i ∧ v i + G ≤ R ∧ u i ≤ v i) := by
  classical
  have h4 : 4 ≤ S := by omega
  choose c x hc0 hc3 hct hLx hx₁ hx₂ hx₃ hx₄ hL₁ hL₂ using fun i =>
    (hγ i).exists_landingPos_eq_of_window hrR h4 (hcor i) (hw i)
  set L : Fin (m + 1) → ℤ := fun i => landingPos (z - R) (z + R) (σ i) (γ i) with hLdef
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin (m + 1) → ℤ, ∀ i,
      (L i < L 0 ∧ lam i = c i + 4) ∨ (L 0 ≤ L i ∧ lam i = c i) :=
    ⟨fun i => if L i < L 0 then c i + 4 else c i, fun i => by
      by_cases h : L i < L 0
      · exact Or.inl ⟨h, ite_eq_left h⟩
      · exact Or.inr ⟨not_lt.1 h, ite_eq_right h⟩⟩
  have hR : (0 : ℤ) ≤ R := by positivity
  -- the lifted positions `4 R lam + x`
  have hlift := lift_add_le_of_sbtw (L := L) (P := fun i => 4 * R * lam i + x i) (Q := 16 * R)
    (by omega) ho hsep (fun i => ⟨hL₁ i, hL₂ i⟩) (fun i => by
      rcases hlam i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, by rw [h₂, hLdef]; simp only; rw [hLx i]; ring⟩
      · exact Or.inr ⟨h₁, by rw [h₂, hLdef]; simp only; rw [hLx i]⟩)
  obtain ⟨hl1, hl2⟩ := hlift
  -- comparing lifted positions with different lifted sides
  have hcmp : ∀ i l, 4 * R * lam i + x i + S ≤ 4 * R * lam l + x l + 16 * R * 0 →
      lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l) := by
    intro i l h
    rcases lt_trichotomy (lam i) (lam l) with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [heq] at h
      have := hx₃ i
      have := hx₄ l
      have := hv i
      have := hv l
      omega
    · exfalso
      have : 4 * (R : ℤ) * (lam l + 1) ≤ 4 * R * lam i :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have := hx₁ l
      have := hx₂ l
      have := hx₁ i
      nlinarith
  refine ⟨lam, fun i => ?_, fun i => ?_, fun i l hil => hcmp i l (by simpa using hl1 i l hil),
    ?_, fun i => ?_⟩
  · have := hc0 i
    have := hc3 i
    rcases hlam i with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  · have := hct i
    rcases hlam i with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  · -- the wrap: compare the last arm with the first one lifted by four sides
    rcases lt_trichotomy (lam (Fin.last m)) (lam 0 + 4) with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have h' : 4 * (R : ℤ) * lam (Fin.last m) = 4 * R * lam 0 + 16 * R := by rw [heq]; ring
      have := hx₃ (Fin.last m)
      have := hx₄ 0
      have := hv (Fin.last m)
      have := hv 0
      omega
    · exfalso
      have : 4 * (R : ℤ) * (lam 0 + 5) ≤ 4 * R * lam (Fin.last m) :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have := hx₁ (Fin.last m)
      have := hx₂ 0
      nlinarith
  · have := hx₁ i
    have := hx₂ i
    have := hx₃ i
    have := hx₄ i
    have := hv i
    omega

end Start

/-! ### The two phases of the plan -/

section Plan

variable {m : ℕ}

/-- **Rounds of turns** (phase 1 of the plan). Separated arms ending in windows `[u i, v i]` (in
counterclockwise coordinates, of width at most `W`) on the sides `t i` of `B_{ρ 0}(z)`, with
lifted sides `lam i` in lexicographic order with gaps `G` along the index, are carried through `n₁`
stages (radii `ρ k`, growing by at least `G + M + W + 1`) to arms ending on the sides of their
target lifted sides `lamT i`, when at most `n₁` turns are needed in all: the windows stay in
lexicographic order with gaps `G - 2 n₁ W` and widen to at most `(2 n₁ + 1) W`. The fences `(M, K)`
are kept. The constant depends only on `σ`, `c`, `A`, `N`, `n₁`. -/
theorem exists_pos_le_law_turns (σ : Fin (m + 1) → Bool)
    (hσ : m + 1 ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate (m + 1) i)) (c : ℕ → ℝ≥0∞) (A N n₁ : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r W M K G : ℕ) (ρ : ℕ → ℕ)
      (J : Fin (m + 1) → Set ℤ) (lamT lam u v : Fin (m + 1) → ℤ) (t : Fin (m + 1) → Fin 4),
      1 ≤ W → W ≤ K → W + K ≤ M → W + 2 * K ≤ A * (M - 1) → 2 * n₁ + 1 ≤ N →
      W + 2 * M + 2 * K + 3 + 2 * n₁ * W ≤ G → r + M + 1 < ρ 0 →
      (∀ k < n₁, ρ k + G + M + W + 1 ≤ ρ (k + 1) ∧ 2 * ρ (k + 1) + 2 ≤ A * W ∧
        (ρ (k + 1) : ℕ∞) ≤ L) →
      (∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l)) →
      (lam (Fin.last m) < lam 0 + 4 ∨
        (lam (Fin.last m) = lam 0 + 4 ∧ v (Fin.last m) + G ≤ u 0)) →
      (∀ i, -(ρ 0 : ℤ) + G ≤ u i ∧ v i + G ≤ ρ 0 ∧ u i ≤ v i ∧ v i - u i ≤ W) →
      (∀ i, lam i ≤ lamT i) → (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      lamT (Fin.last m) ≤ lamT 0 + 4 → ∑ i, (lamT i - lam i) ≤ n₁ →
      ∃ (t' : Fin (m + 1) → Fin 4) (u' v' : Fin (m + 1) → ℤ),
        (∀ i, (lamT i + ((t' i : ℕ) : ℤ)) % 4 = 2) ∧
        (∀ i l, i < l → lamT i < lamT l ∨
          (lamT i = lamT l ∧ v' i + ((G : ℤ) - 2 * n₁ * W) ≤ u' l)) ∧
        (∀ i, -(ρ n₁ : ℤ) + ((G : ℤ) - 2 * n₁ * W) ≤ u' i ∧
          v' i + ((G : ℤ) - 2 * n₁ * W) ≤ ρ n₁ ∧ u' i ≤ v' i ∧
          v' i - u' i ≤ (2 * n₁ + 1) * W) ∧
        c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin (m + 1) → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ 0)) (z + (ρ 0)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ i) (γ i))
          (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ k) (γ k)) (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ 0) ((2 * (G : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + (ρ 0) ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
          (t i = 1 ∧ b i 0 = z 0 + (ρ 0) ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
          (t i = 2 ∧ b i 1 = z 1 - (ρ 0) - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ b i 0 = z 0 - (ρ 0) - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
          law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin (m + 1) → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ n₁)) (z + (ρ n₁)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ n₁)) (z + (ρ n₁)) (σ i) (γ i))
          (landingPos (z - (ρ n₁)) (z + (ρ n₁)) (σ k) (γ k)) (landingPos (z - (ρ n₁)) (z + (ρ n₁))
              (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ n₁) ((2 * ((G : ℤ) - 2 * n₁ * W) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i,
          (t' i = 0 ∧ b i 1 = z 1 + (ρ n₁) ∧ z 0 - v' i ≤ b i 0 ∧ b i 0 ≤ z 0 - u' i) ∨
          (t' i = 1 ∧ b i 0 = z 0 + (ρ n₁) ∧ z 1 + u' i ≤ b i 1 ∧ b i 1 ≤ z 1 + v' i) ∨
          (t' i = 2 ∧ b i 1 = z 1 - (ρ n₁) - cond (σ i) 0 1 ∧ z 0 + u' i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v' i) ∨
          (t' i = 3 ∧ b i 0 = z 0 - (ρ n₁) - cond (σ i) 0 1 ∧ z 1 - v' i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u' i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  obtain ⟨c₁, hc₁, hst⟩ := exists_pos_le_law_ccw_of_moves σ hσ c A N
  refine ⟨c₁ ^ n₁, ENNReal.pow_pos hc₁ n₁, ?_⟩
  intro q L hCB z r W M K G ρ J lamT lam u v t hW hWK hWKM hAM hN hG hr0 hρ hc hL1 hL2 hL3 hT1
    hT2 hT3 hpot
  have hρmono : ∀ k ≤ n₁, ρ 0 ≤ ρ k := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have := (hρ k (by omega)).1
      have := ih (by omega)
      omega
  have hG' : (W : ℤ) + 2 * M + 2 * K + 3 + 2 * (n₁ : ℤ) * W ≤ G := by exact_mod_cast hG
  obtain ⟨x, hx, hle⟩ := exists_pow_mul_le_of_forall_exists (c := c₁)
    (u := fun kk (x : (Fin (m + 1) → ℤ) × (Fin (m + 1) → Fin 4) × (Fin (m + 1) → ℤ) ×
      (Fin (m + 1) → ℤ)) => law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin (m + 1) → LatticeSite
          2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - (ρ kk)) (z + (ρ kk)) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ kk)) (z + (ρ kk)) (σ i) (γ i))
            (landingPos (z - (ρ kk)) (z + (ρ kk)) (σ k) (γ k)) (landingPos (z - (ρ kk)) (z + (ρ
                kk)) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z (ρ kk) ((2 * ((G : ℤ) - 2 * (kk : ℤ) * W) - 1 : ℤ) : ℝ) M K γ ∧
              (∀ i,
            (x.2.1 i = 0 ∧ b i 1 = z 1 + (ρ kk) ∧ z 0 - x.2.2.2 i ≤ b i 0 ∧ b i 0 ≤ z 0 - x.2.2.1
                i) ∨
            (x.2.1 i = 1 ∧ b i 0 = z 0 + (ρ kk) ∧ z 1 + x.2.2.1 i ≤ b i 1 ∧ b i 1 ≤ z 1 + x.2.2.2
                i) ∨
            (x.2.1 i = 2 ∧ b i 1 = z 1 - (ρ kk) - cond (σ i) 0 1 ∧ z 0 + x.2.2.1 i ≤ b i 0 ∧
              b i 0 ≤ z 0 + x.2.2.2 i) ∨
            (x.2.1 i = 3 ∧ b i 0 = z 0 - (ρ kk) - cond (σ i) 0 1 ∧ z 1 - x.2.2.2 i ≤ b i 1 ∧
              b i 1 ≤ z 1 - x.2.2.1 i)) ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i})
    (I := fun kk x => (∀ i, (x.1 i + ((x.2.1 i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i l, i < l → x.1 i < x.1 l ∨
        (x.1 i = x.1 l ∧ x.2.2.2 i + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ x.2.2.1 l)) ∧
      (x.1 (Fin.last m) < x.1 0 + 4 ∨ (x.1 (Fin.last m) = x.1 0 + 4 ∧
        x.2.2.2 (Fin.last m) + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ x.2.2.1 0)) ∧
      (∀ i, -(ρ kk : ℤ) + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ x.2.2.1 i ∧
        x.2.2.2 i + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ ρ kk ∧ x.2.2.1 i ≤ x.2.2.2 i ∧
        x.2.2.2 i - x.2.2.1 i ≤ (2 * (kk : ℤ) + 1) * W) ∧
      (∀ i, x.1 i ≤ lamT i) ∧
      (∑ i, (lamT i - x.1 i) + kk ≤ n₁ ∨ ∑ i, (lamT i - x.1 i) = 0))
    n₁ (by
      -- one round of turns
      rintro k hk ⟨lam₀, t₀, u₀, v₀⟩ ⟨hc₀, hL1₀, hL2₀, hL3₀, hT1₀, hpot₀⟩
      simp only at hc₀ hL1₀ hL2₀ hL3₀ hT1₀ hpot₀
      obtain ⟨Gk, hGk⟩ : ∃ g : ℤ, g = (G : ℤ) - 2 * (k : ℤ) * W := ⟨_, rfl⟩
      have hGk1 : (G : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) * W = Gk - 2 * W := by rw [hGk]; push_cast; ring
      have hwk1 : (2 * ((k + 1 : ℕ) : ℤ) + 1) * W = (2 * (k : ℤ) + 1) * W + 2 * W := by
        push_cast; ring
      have hkW : (2 * (k : ℤ) + 1) * W + 1 ≤ N * ((W : ℤ) + 1) := by
        have h₁ : (k : ℤ) ≤ n₁ := by exact_mod_cast hk.le
        have h₂ : (2 * (n₁ : ℤ) + 1) ≤ N := by exact_mod_cast hN
        nlinarith
      have hknW : 2 * (k : ℤ) * W ≤ 2 * n₁ * W := by
        have h₁ : (k : ℤ) ≤ n₁ := by exact_mod_cast hk.le
        nlinarith
      have hkW0 : 0 ≤ 2 * (k : ℤ) * W := by positivity
      have hkW1 : 0 ≤ (2 * (k : ℤ) + 1) * W := by positivity
      rw [← hGk] at hL1₀ hL2₀ hL3₀
      obtain ⟨hρ₁, hρ₂, hρ₃⟩ := hρ k hk
      have hρk := hρmono k hk.le
      obtain ⟨τ, lam', t', u', v', hccw, hmv, hc', hL1', hL2', hL3', hT1', hsum, hsum'⟩ :=
        exists_turn_step (ρ := (ρ k : ℤ)) (ρ' := (ρ (k + 1) : ℤ)) (h := (ρ k : ℤ) + M + 1)
          (lamT := lamT) (W := (W : ℤ)) (G := Gk) (by positivity) (by omega) hc₀ hL1₀ hL2₀
          (fun i => ⟨(hL3₀ i).1, (hL3₀ i).2.1, (hL3₀ i).2.2.1⟩) hT1₀ hT2 hT3 (by omega)
          (by omega) (by exact_mod_cast (show ρ k ≤ ρ (k + 1) by omega))
      refine ⟨(lam', t', u', v'), ⟨hc', fun i l hil => ?_, ?_, fun i => ?_, hT1', ?_⟩, ?_⟩
      · rw [hGk1]
        exact hL1' i l hil
      · rw [hGk1]
        exact hL2'
      · dsimp only
        rw [hGk1, hwk1]
        have := hL3' i
        have := hL3₀ i
        rcases hmv i with ⟨-, -, -, h₁, h₂⟩ | ⟨-, -, -, h₁, h₂⟩ <;> omega
      · dsimp only
        have : 0 ≤ ∑ i, (lamT i - lam' i) := Finset.sum_nonneg fun i _ => by have := hT1' i; omega
        have h0 : 0 ≤ ∑ i, (lamT i - lam₀ i) := Finset.sum_nonneg fun i _ => by
          have := hT1₀ i; omega
        rcases hpot₀ with h | h
        · rcases h0.lt_or_eq with h' | h'
          · have := hsum' h'
            left
            push_cast
            omega
          · right
            omega
        · right
          omega
      · -- the probability step
        obtain ⟨Sk, hSk⟩ : ∃ S : ℕ, (S : ℤ) = Gk := ⟨Gk.toNat, by omega⟩
        have hs : 4 * (M : ℝ) ≤ ((2 * ((G : ℤ) - 2 * (k : ℤ) * W) - 1 : ℤ) : ℝ) := by
          rw [← hGk]
          have : (4 * M : ℤ) ≤ 2 * Gk - 1 := by omega
          exact_mod_cast this
        have key := hst q L hCB z r (ρ k) (ρ (k + 1)) W M K M K 0 Sk ((ρ k : ℤ) + M + 1)
          ((2 * ((G : ℤ) - 2 * (k : ℤ) * W) - 1 : ℤ) : ℝ) ((G : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) * W) J
          t₀ t' τ u₀ v₀ (fun _ => 0) u' v' hW hWK (by omega) (by omega) hWKM (by omega) hs
          (by have := hr0; omega) le_rfl (by omega) hρ₂ hAM hρ₃ (fun _ => by simp)
          (fun i => by have := hL3₀ i; omega)
          (fun i => by have := hL3₀ i; omega)
          (fun i l hil htl => by
            have := gap_of_lex (by omega) hc₀ hL1₀ hL2₀ (fun i => (hL3₀ i).2.2.1) i l hil htl
            omega)
          (fun i l hil hτ htl => by have := hccw i l hil hτ htl; omega)
          (fun i => by
            rcases hmv i with ⟨h₁, h₂, -, h₃, h₄⟩ | ⟨h₁, h₂, -, h₃, h₄⟩
            · exact Or.inl ⟨h₁, h₂, by omega, by omega⟩
            · exact Or.inr ⟨h₁, h₂, by omega, by omega⟩)
          (by rw [hGk1]; omega)
          (fun i => by rw [hGk1]; have := hL3' i; omega)
          (fun i l hil htl => by
            rw [hGk1]
            exact gap_of_lex (by omega) hc' hL1' hL2' (fun i => (hL3' i).2.2) i l hil htl)
        exact key)
    (lam, t, u, v) (by
      refine ⟨hc, fun i l hil => ?_, ?_, fun i => ?_, hT1, Or.inl (by simpa using hpot)⟩
      · simpa using hL1 i l hil
      · simpa using hL2
      · have := hL3 i
        push_cast
        omega)
  -- phase 1 at the end: no turns left
  obtain ⟨hxc, hx1, -, hx3, hxT, hxpot⟩ := hx
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ lamT i - x.1 i := fun i _ => by have := hxT i; omega
  have hsum0 : ∑ i, (lamT i - x.1 i) = 0 := by
    have := Finset.sum_nonneg hnn
    rcases hxpot with h | h <;> omega
  have hxlam : ∀ i, x.1 i = lamT i := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 i (Finset.mem_univ _)
    omega
  refine ⟨x.2.1, x.2.2.1, x.2.2.2, fun i => by rw [← hxlam]; exact hxc i,
    fun i l hil => by rw [← hxlam, ← hxlam]; exact hx1 i l hil, fun i => hx3 i, ?_⟩
  have e0 : ((2 * ((G : ℤ) - 2 * ((0 : ℕ) : ℤ) * W) - 1 : ℤ) : ℝ) =
      ((2 * (G : ℤ) - 1 : ℤ) : ℝ) := by push_cast; ring
  simp only [e0] at hle
  exact hle

/-- **Linear spreading along the sides** (phase 2 of the plan). Separated arms ending in windows
`[u i, v i]` (counterclockwise coordinates, width at most `w`) on the sides `t i` of `B_{ρ₀}(z)`, at
least `S` from the corners and in counterclockwise order on each side with gaps `S`, are moved in
`n` stages (radius growing by `Δ` per stage), each arm by the same amount at every stage, into
windows `[u' i, v' i] ⊆ [uT i, uT i + n + w + 2nW]` at `B_{ρ₀ + nΔ}(z)`; the targets are at least
`S` from the corners and in the same order with gaps `S` beyond their widths. The fences `(M, K)`
are kept. The constant depends only on `σ`, `c`, `A`, `N`, `n`. -/
theorem exists_pos_le_law_spread {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r W M K D S ρ₀ Δ w : ℕ)
      (J : Fin j → Set ℤ) (t : Fin j → Fin 4) (u v uT : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → W + 2 * K ≤ A * (M - 1) →
      W + 2 * D + 2 * M + 2 * K + 3 ≤ S → r + M + 1 < ρ₀ →
      2 * M + W + 1 ≤ Δ → 2 * (ρ₀ + n * Δ) + 2 ≤ A * W → ((ρ₀ + n * Δ : ℕ) : ℕ∞) ≤ L →
      2 * (ρ₀ + n * Δ) + 2 * n + n * W ≤ n * D → w + 2 * n * W + 1 ≤ N * (W + 1) →
      (∀ i, -(ρ₀ : ℤ) + S ≤ u i ∧ v i + S ≤ ρ₀ ∧ u i ≤ v i ∧ v i - u i ≤ w) →
      (∀ i l, i < l → t i = t l → v i + S ≤ u l) →
      (∀ i, -((ρ₀ + n * Δ : ℕ) : ℤ) + S ≤ uT i ∧
        uT i + n + w + 2 * n * W + S ≤ ((ρ₀ + n * Δ : ℕ) : ℤ)) →
      (∀ i l, i < l → t i = t l → uT i + n + w + 2 * n * W + S ≤ uT l) →
      ∃ u' v' : Fin j → ℤ, (∀ i, uT i ≤ u' i ∧ v' i ≤ uT i + n + w + 2 * n * W) ∧
        c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - ρ₀) (z + ρ₀) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - ρ₀) (z + ρ₀) (σ i) (γ i))
          (landingPos (z - ρ₀) (z + ρ₀) (σ k) (γ k)) (landingPos (z - ρ₀) (z + ρ₀) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z ρ₀ ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + ρ₀ ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
          (t i = 1 ∧ b i 0 = z 0 + ρ₀ ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
          (t i = 2 ∧ b i 1 = z 1 - ρ₀ - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ b i 0 = z 0 - ρ₀ - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
          law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ₀ + n * Δ : ℕ)) (z + (ρ₀ + n * Δ : ℕ)) (γ i)) ∧ ArmsDisjoint
            σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ₀ + n * Δ : ℕ)) (z + (ρ₀ + n * Δ : ℕ)) (σ
            i) (γ i))
          (landingPos (z - (ρ₀ + n * Δ : ℕ)) (z + (ρ₀ + n * Δ : ℕ)) (σ k) (γ k)) (landingPos (z -
              (ρ₀ + n * Δ : ℕ)) (z + (ρ₀ + n * Δ : ℕ)) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ₀ + n * Δ : ℕ) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + (ρ₀ + n * Δ : ℕ) ∧ z 0 - v' i ≤ b i 0 ∧ b i 0 ≤ z 0 - u' i) ∨
          (t i = 1 ∧ b i 0 = z 0 + (ρ₀ + n * Δ : ℕ) ∧ z 1 + u' i ≤ b i 1 ∧ b i 1 ≤ z 1 + v' i) ∨
          (t i = 2 ∧ b i 1 = z 1 - (ρ₀ + n * Δ : ℕ) - cond (σ i) 0 1 ∧ z 0 + u' i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v' i) ∨
          (t i = 3 ∧ b i 0 = z 0 - (ρ₀ + n * Δ : ℕ) - cond (σ i) 0 1 ∧ z 1 - v' i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u' i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  obtain ⟨c₁, hc₁, hst⟩ := exists_pos_le_law_ccw_of_moves σ hσ c A N
  refine ⟨c₁ ^ n, ENNReal.pow_pos hc₁ n, ?_⟩
  intro q L hCB z r W M K D S ρ₀ Δ w J t u v uT hW hWK hWKM hAM hS hr0 hΔ hAW hL hjog hN hwin hgap
    hTcor hTgap
  -- at least one stage
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [zero_mul, add_zero, mul_zero] at hjog
      omega
    · exact h
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  -- the shift of each arm per stage
  obtain ⟨e, he⟩ : ∃ e : Fin j → ℤ, ∀ i, e i = (uT i + n + n * W - u i) / n := ⟨_, fun _ => rfl⟩
  have he₁ : ∀ i, (n : ℤ) * e i ≤ uT i + n + n * W - u i := fun i => by
    rw [he]; exact Int.mul_ediv_self_le hn'.ne'
  have he₂ : ∀ i, uT i + n + n * W - u i < (n : ℤ) * e i + n := fun i => by
    rw [he]
    have := Int.lt_ediv_add_one_mul_self (uT i + n + n * W - u i) hn'
    linarith
  have hR' : ((ρ₀ + n * Δ : ℕ) : ℤ) = ρ₀ + n * Δ := by push_cast; ring
  have hjog' : 2 * ((ρ₀ : ℤ) + n * Δ) + 2 * n + n * W ≤ n * D := by exact_mod_cast hjog
  have hed : ∀ i, -(D : ℤ) ≤ e i ∧ e i ≤ D := fun i => by
    have h₁ := he₁ i
    have h₂ := he₂ i
    have h₃ := hTcor i
    have h₄ := hwin i
    rw [hR'] at h₃
    have h₅ : (0 : ℤ) ≤ n * Δ := by positivity
    have h₆ : (0 : ℤ) ≤ n * W := by positivity
    have h₇ : (n : ℤ) * e i ≤ n * D := by linarith
    have h₈ : (n : ℤ) * (-D) < n * e i + n := by linarith
    constructor
    · by_contra hlt
      push Not at hlt
      have : (n : ℤ) * (e i + 1) ≤ n * (-D) := mul_le_mul_of_nonneg_left (by omega) hn'.le
      linarith
    · exact le_of_mul_le_mul_left h₇ hn'
  -- the windows of every stage are at least `S` from the corners and apart
  have hcor : ∀ k ≤ n, ∀ i, -((ρ₀ + k * Δ : ℕ) : ℤ) + S ≤ u i + k * e i - k * W ∧
      v i + k * e i + k * W + S ≤ ((ρ₀ + k * Δ : ℕ) : ℤ) := by
    intro k hk i
    push_cast
    have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
    have h₁ := he₁ i
    have h₂ := he₂ i
    have h₃ := hTcor i
    have h₄ := hwin i
    rw [hR'] at h₃
    constructor
    · have := le_add_mul_of_le_of_le (g := 0) (a := u i + ρ₀ - S) (b := e i - W + Δ) (k := k)
        (n := n) (by linarith) (by linarith) (by positivity) hk'
      linarith
    · have := le_add_mul_of_le_of_le (g := 0) (a := ρ₀ - v i - S) (b := Δ - e i - W) (k := k)
        (n := n) (by linarith) (by linarith) (by positivity) hk'
      linarith
  have hgapk : ∀ k ≤ n, ∀ i l, i < l → t i = t l →
      v i + k * e i + k * W + S ≤ u l + k * e l - k * W := by
    intro k hk i l hil htl
    have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
    have h₁ := he₁ i
    have h₂ := he₂ l
    have h₃ := hTgap i l hil htl
    have h₄ := hwin i
    have h₅ := hgap i l hil htl
    have := le_add_mul_of_le_of_le (g := 0) (a := u l - v i - S) (b := e l - e i - 2 * W)
      (k := k) (n := n) (by linarith) (by linarith) (by positivity) hk'
    linarith
  obtain ⟨x, hx, hle⟩ := exists_pow_mul_le_of_forall_exists (c := c₁)
    (u := fun kk (x : (Fin j → ℤ) × (Fin j → ℤ)) => law q {ω : Config (LatticeSite 2) | ∃ (a b :
        Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - (ρ₀ + kk * Δ : ℕ)) (z + (ρ₀ + kk * Δ : ℕ)) (γ i)) ∧
              ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ₀ + kk * Δ : ℕ)) (z + (ρ₀ + kk * Δ :
              ℕ)) (σ i) (γ i))
            (landingPos (z - (ρ₀ + kk * Δ : ℕ)) (z + (ρ₀ + kk * Δ : ℕ)) (σ k) (γ k)) (landingPos (z
                - (ρ₀ + kk * Δ : ℕ)) (z + (ρ₀ + kk * Δ : ℕ)) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z (ρ₀ + kk * Δ : ℕ) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i,
            (t i = 0 ∧ b i 1 = z 1 + (ρ₀ + kk * Δ : ℕ) ∧ z 0 - x.2 i ≤ b i 0 ∧ b i 0 ≤ z 0 - x.1 i)
                ∨
            (t i = 1 ∧ b i 0 = z 0 + (ρ₀ + kk * Δ : ℕ) ∧ z 1 + x.1 i ≤ b i 1 ∧ b i 1 ≤ z 1 + x.2 i)
                ∨
            (t i = 2 ∧ b i 1 = z 1 - (ρ₀ + kk * Δ : ℕ) - cond (σ i) 0 1 ∧ z 0 + x.1 i ≤ b i 0 ∧
              b i 0 ≤ z 0 + x.2 i) ∨
            (t i = 3 ∧ b i 0 = z 0 - (ρ₀ + kk * Δ : ℕ) - cond (σ i) 0 1 ∧ z 1 - x.2 i ≤ b i 1 ∧
              b i 1 ≤ z 1 - x.1 i)) ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i})
    (I := fun kk x => ∀ i, x.1 i = u i + kk * e i - kk * W ∧ x.2 i = v i + kk * e i + kk * W)
    n (by
      rintro k hk ⟨x₁, x₂⟩ hI
      simp only at hI
      refine ⟨(fun i => u i + ((k + 1 : ℕ) : ℤ) * e i - ((k + 1 : ℕ) : ℤ) * W,
        fun i => v i + ((k + 1 : ℕ) : ℤ) * e i + ((k + 1 : ℕ) : ℤ) * W), fun i => ⟨rfl, rfl⟩, ?_⟩
      have hkn : (k : ℤ) + 1 ≤ n := by exact_mod_cast hk
      have hkW : (k : ℤ) * W ≤ n * W := mul_le_mul_of_nonneg_right (by omega) (by positivity)
      have hkΔ : (k + 1) * Δ ≤ n * Δ := Nat.mul_le_mul_right Δ hk
      have hkΔ' : (k + 1) * Δ = k * Δ + Δ := by ring
      have key := hst q L hCB z r (ρ₀ + k * Δ) (ρ₀ + (k + 1) * Δ) W M K M K D S
        (((ρ₀ + k * Δ : ℕ) : ℤ) + M + 1) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) S J t t (fun _ => false)
        x₁ x₂ e
        (fun i => u i + ((k + 1 : ℕ) : ℤ) * e i - ((k + 1 : ℕ) : ℤ) * W)
        (fun i => v i + ((k + 1 : ℕ) : ℤ) * e i + ((k + 1 : ℕ) : ℤ) * W) hW
        hWK (by omega) (by omega) hWKM (by omega)
        (by
          have : (4 * M : ℤ) ≤ 2 * (S : ℤ) - 1 := by omega
          exact_mod_cast this)
        (by have : 0 ≤ k * Δ := Nat.zero_le _; omega)
        le_rfl (by omega) (by omega) hAM
        (le_trans (by exact_mod_cast (show ρ₀ + (k + 1) * Δ ≤ ρ₀ + n * Δ by omega)) hL) hed
        (fun i => by
          have := hwin i
          have := hI i
          have h₁ : (w : ℤ) + 2 * n * W + 1 ≤ N * ((W : ℤ) + 1) := by exact_mod_cast hN
          linarith)
        (fun i => by have := hcor k hk.le i; have := hI i; omega)
        (fun i l hil htl => by
          have := hI i
          have := hI l
          rcases lt_or_gt_of_ne hil with h | h
          · have := hgapk k hk.le i l h htl; omega
          · have := hgapk k hk.le l i h htl.symm; omega)
        (fun i l _ hτ _ => absurd hτ Bool.false_ne_true)
        (fun i => Or.inl ⟨rfl, rfl, by have := hI i; push_cast; linarith,
          by have := hI i; push_cast; linarith⟩)
        (by omega) (fun i => hcor (k + 1) hk i)
        (fun i l hil htl => by
          rcases lt_or_gt_of_ne hil with h | h
          · exact Or.inl (hgapk (k + 1) hk i l h htl)
          · exact Or.inr (hgapk (k + 1) hk l i h htl.symm))
      exact key)
    (u, v) (fun i => ⟨by simp, by simp⟩)
  refine ⟨x.1, x.2, fun i => ?_, ?_⟩
  · obtain ⟨h₁, h₂⟩ := hx i
    have h₃ := he₁ i
    have h₄ := he₂ i
    have h₅ := hwin i
    constructor <;> linarith
  · simp only [zero_mul, add_zero] at hle
    exact hle

/-- A bound `c μ s ≤ μ t` holds when it holds for nonempty `s`. -/
theorem mul_measure_le_of_nonempty {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} {c : ℝ≥0∞} (h : s.Nonempty → c * μ s ≤ μ t) : c * μ s ≤ μ t := by
  rcases s.eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty, mul_zero]
    exact zero_le
  · exact h hne

/-- **The last stage: new fences in the target windows.** Separated arms with fences `(M, K)`
ending in windows `[u i, v i]` (counterclockwise coordinates) on the sides `t i` of
`B_{R' - (M + M' + W + 1)}(z)`, inside the target windows `[uT i + W, vT i - W]`, are carried
straight out to `∂B_{R'}(z)`, ending in the target windows with fences `(M', K')`, separated at
scale `2Q - 1`; the targets are at least `Q + M + M' + W + 1` from the corners and in
counterclockwise order on each side with gaps `Q`. The constant depends only on `σ`, `c`, `A`,
`N`. -/
theorem exists_pos_le_law_fences_of_windows {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R' W M K M' K' Q : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (t : Fin j → Fin 4) (u v uT vT : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2 * M + 2 * K' + 3 ≤ Q →
      4 * (M : ℝ) ≤ s → r + M + 1 < R' - (M + M' + W + 1) → 2 * R' + 2 ≤ A * W →
      W + 2 * K' ≤ A * (M' - 1) → (R' : ℕ∞) ≤ L →
      (∀ i, v i - u i + 1 ≤ N * ((W : ℤ) + 1)) → (∀ i, uT i + W ≤ u i ∧ v i + W ≤ vT i) →
      (∀ i, -(R' : ℤ) + (Q + M + M' + W + 1) ≤ uT i ∧ vT i + (Q + M + M' + W + 1) ≤ R') →
      (∀ i l, i < l → t i = t l → vT i + Q ≤ uT l) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (R' - (M + M' + W + 1) : ℕ)) (z + (R' - (M + M' + W + 1) : ℕ))
            (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (R' - (M + M' + W + 1) : ℕ)) (z + (R' - (M
            + M' + W + 1) : ℕ)) (σ i) (γ i))
          (landingPos (z - (R' - (M + M' + W + 1) : ℕ)) (z + (R' - (M + M' + W + 1) : ℕ)) (σ k) (γ
              k)) (landingPos (z - (R' - (M + M' + W + 1) : ℕ)) (z + (R' - (M + M' + W + 1) : ℕ))
              (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (R' - (M + M' + W + 1) : ℕ) s M K γ ∧ (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + (R' - (M + M' + W + 1) : ℕ) ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 -
              u i) ∨
          (t i = 1 ∧ b i 0 = z 0 + (R' - (M + M' + W + 1) : ℕ) ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 +
              v i) ∨
          (t i = 2 ∧ b i 1 = z 1 - (R' - (M + M' + W + 1) : ℕ) - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0
              ∧
            b i 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ b i 0 = z 0 - (R' - (M + M' + W + 1) : ℕ) - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1
              ∧
            b i 1 ≤ z 1 - u i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + R' ∧ z 0 - vT i ≤ b i 0 ∧ b i 0 ≤ z 0 - uT i) ∨
          (t i = 1 ∧ b i 0 = z 0 + R' ∧ z 1 + uT i ≤ b i 1 ∧ b i 1 ≤ z 1 + vT i) ∨
          (t i = 2 ∧ b i 1 = z 1 - R' - cond (σ i) 0 1 ∧ z 0 + uT i ≤ b i 0 ∧
            b i 0 ≤ z 0 + vT i) ∨
          (t i = 3 ∧ b i 0 = z 0 - R' - cond (σ i) 0 1 ∧ z 1 - vT i ≤ b i 1 ∧
            b i 1 ≤ z 1 - uT i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₃, hc₃, hP3⟩ := exists_pos_le_law_ccw_of_moves σ hσ c A N
  refine ⟨c₃, hc₃, ?_⟩
  intro q L hCB z r R' W M K M' K' Q s J t u v uT vT hW hWK hKM hM' hWKM' hQ hs hrM hAW hAM' hL hN
    hin hTcor hTgap
  have hgapT : ∀ i l, i ≠ l → t i = t l → vT i + Q ≤ uT l ∨ vT l + Q ≤ uT i := by
    intro i l hil htl
    rcases lt_or_gt_of_ne hil with h | h
    · exact Or.inl (hTgap i l h htl)
    · exact Or.inr (hTgap l i h htl.symm)
  refine hP3 q L hCB z r (R' - (M + M' + W + 1)) R' W M K M' K' 0 Q
    (((R' - (M + M' + W + 1) : ℕ) : ℤ) + M + 1) s Q J t t (fun _ => false) u v (fun _ => 0) uT vT
    hW hWK hKM hM' hWKM' (by omega) hs hrM le_rfl (by omega) hAW hAM' hL (fun _ => by simp) hN
    (fun i => by have := hin i; have := hTcor i; omega)
    (fun i l hil htl => by
      have := hin i
      have := hin l
      rcases hgapT i l hil htl with h | h <;> omega)
    (fun i l _ hτ _ => absurd hτ Bool.false_ne_true)
    (fun i => Or.inl ⟨rfl, rfl, by have := hin i; omega, by have := hin i; omega⟩)
    (by omega) (fun i => by have := hTcor i; omega) hgapT

/-- **The motion plan for arms ending in given bins** (`exists_pos_le_law_target_windows` for the
separated arms ending in bins `[αs i, αs i + W]` on the sides `ts i` of `B_R(z)`). -/
theorem exists_pos_le_law_target_windows_of_bins {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S G Q B : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ)
      (ts : Fin j → Fin 4) (αs : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → 2 ≤ M' → W + K' ≤ M' →
      W + 2 * K ≤ A * (M - 1) → W + 2 * K' ≤ A * (M' - 1) →
      W + 2 * D + 2 * M + 2 * K + 3 ≤ S → S + 2 * (12 * j) * W ≤ G →
      W + 2 * M + 2 * K' + 3 ≤ Q → ((2 * G + 4 * W + 2 : ℕ) : ℝ) ≤ s → r + M + 1 < R →
      R + 12 * j * (G + M + W + 1) + n * (2 * M + W + 1) + (M + M' + W + 1) ≤ R' →
      2 * R' + 2 ≤ A * W → (R' : ℕ∞) ≤ L → 2 * R' + 2 * n + n * W ≤ n * D →
      n + (2 * (12 * j) + 2 * n + 3) * W ≤ B →
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R' + (S + Q + M + M' + W + 1) ≤ αT i ∧
        βT i + (S + Q + M + M' + W + 1) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R') →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + S + Q ≤ αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + S + Q ≤ αT i)) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (ts i = 0 ∧ b 1 = z 1 + R ∧ αs i ≤ b 0 ∧ b 0 ≤ αs i + W) ∨
          (ts i = 1 ∧ b 0 = z 0 + R ∧ αs i ≤ b 1 ∧ b 1 ≤ αs i + W) ∨
          (ts i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ αs i ≤ b 0 ∧ b 0 ≤ αs i + W) ∨
          (ts i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ αs i ≤ b 1 ∧ b 1 ≤ αs i + W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
          (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i}  := by
  classical
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    refine ⟨1, one_pos, ?_⟩
    intro q L _ z r R R' W M K M' K' D S G Q B s J tT lamT αT βT ts αs
    intros
    rw [one_mul]
    refine measure_mono ?_
    rintro ω ⟨a, b, γ, -, hd, -, -, -, hJ⟩
    exact ⟨a, b, γ, fun i => i.elim0, hd, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, hJ⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, n₁ = 12 * (m + 1) := ⟨_, rfl⟩
  rw [← hn₁]
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * n₁ + 2 * n + 1 := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁, hP1⟩ := exists_pos_le_law_turns σ hσ c A N n₁
  obtain ⟨c₂, hc₂, hP2⟩ := exists_pos_le_law_spread σ hσ c A N n
  obtain ⟨c₃, hc₃, hP3⟩ := exists_pos_le_law_fences_of_windows σ hσ c A N
  refine ⟨c₁ * c₂ * c₃, ENNReal.mul_pos (mul_ne_zero hc₁.ne' hc₂.ne') hc₃.ne', ?_⟩
  intro q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT ts αs hW hWK hWKM hM' hWKM' hAM
    hAM' hS hG hQ hs hrM hRR' hAW hL hjog hB hlamT hlamT2 hTcor hTwid hTord
  have hrR : r < R := by omega
  have hRA : R ≤ A * W := by omega
  have hs' : ((2 * (G : ℤ) + 4 * W + 2 : ℤ) : ℝ) ≤ s := by push_cast at hs ⊢; linarith
  have hs4 : 4 * (M : ℝ) ≤ s := by
    refine le_trans ?_ hs'
    have : (4 * M : ℤ) ≤ 2 * (G : ℤ) + 4 * W + 2 := by omega
    exact_mod_cast this
  -- the radii of the plan
  obtain ⟨Δ₁, hΔ₁⟩ : ∃ d, d = G + M + W + 1 := ⟨_, rfl⟩
  obtain ⟨Δ₂, hΔ₂⟩ : ∃ d, d = 2 * M + W + 1 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ d, d = M + M' + W + 1 := ⟨_, rfl⟩
  rw [← hΔ₁, ← hΔ₂, ← hE] at hRR'
  have hnR' : n * Δ₂ ≤ R' - E := by omega
  obtain ⟨ρ₁, hρ₁, hρ₁n⟩ : ∃ f : ℕ → ℕ, (∀ k < n₁, f k = R + k * Δ₁) ∧
      f n₁ = R' - E - n * Δ₂ :=
    ⟨fun k => if k < n₁ then R + k * Δ₁ else R' - E - n * Δ₂, fun k hk => ite_eq_left hk,
      ite_eq_right (lt_irrefl _)⟩
  have hn₁0 : 0 < n₁ := by omega
  have hρ₁0 : ρ₁ 0 = R := by rw [hρ₁ 0 hn₁0]; simp
  have hρ₁step : ∀ k < n₁, ρ₁ k + G + M + W + 1 ≤ ρ₁ (k + 1) ∧ 2 * ρ₁ (k + 1) + 2 ≤ A * W ∧
      (ρ₁ (k + 1) : ℕ∞) ≤ L := by
    intro k hk
    have h₁ : (k + 1) * Δ₁ ≤ n₁ * Δ₁ := Nat.mul_le_mul_right _ hk
    have h₂ : (k + 1) * Δ₁ = k * Δ₁ + Δ₁ := by ring
    have hle : ρ₁ (k + 1) ≤ R' ∧ R + (k + 1) * Δ₁ ≤ ρ₁ (k + 1) := by
      rcases (show k + 1 ≤ n₁ by omega).lt_or_eq with h | h
      · rw [hρ₁ (k + 1) h]; omega
      · rw [h, hρ₁n]; omega
    refine ⟨?_, by omega, le_trans (by exact_mod_cast hle.1) hL⟩
    rw [hρ₁ k hk]
    omega
  have eW1 : ((2 * n₁ * W : ℕ) : ℤ) = 2 * (n₁ : ℤ) * W := by push_cast; ring
  have eW2 : (((2 * n₁ + 1) * W : ℕ) : ℤ) = (2 * (n₁ : ℤ) + 1) * W := by push_cast; ring
  have eW3 : ((2 * n * W : ℕ) : ℤ) = 2 * (n : ℤ) * W := by push_cast; ring
  have eW4 : ((2 * n₁ + 2 * n + 3) * W : ℕ) = (2 * n₁ + 1) * W + 2 * n * W + 2 * W := by ring
  -- the targets in counterclockwise coordinates
  choose uT vT hrelT hmemT using fun i => exists_ccw_window (tT i) z (αT i) (βT i)
  have hrelT' := fun i => side_center_eq (hrelT i)
  -- the plan for the arms ending in given bins
  refine mul_measure_le_of_nonempty fun ⟨ω₀, hω₀⟩ => ?_
  obtain ⟨a₀, b₀, γ₀, hγ₀, -, ho₀, hsep₀, hw₀, -⟩ := hω₀
  choose us vs hrels hmems using fun i => exists_ccw_window (ts i) z (αs i) (αs i + W)
  have hvs : ∀ i, vs i = us i + W := fun i => by
    rcases hrels i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega
  have hsepZ := hsep₀.le_abs_landingPos_sub hs'
  obtain ⟨lam, hlam, hc, hL1, hL2, hL3⟩ := exists_lift_of_separated hγ₀ hrR ho₀ (G := G)
    (W := W) (by positivity) (by omega) le_rfl hsepZ.1 hsepZ.2 ts us vs hvs
    (fun i => (hmems i R (σ i) (b₀ i)).1 (hw₀ i))
  -- phase 1: rounds of turns
  have hpot : ∑ i, ((lamT i + 8) - lam i) ≤ n₁ := by
    have h₁ : ∑ i, ((lamT i + 8) - lam i) ≤ ∑ _i : Fin (m + 1), (12 : ℤ) :=
      Finset.sum_le_sum fun i _ => by have := hlam i; have := hlamT i; omega
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁
    push_cast at h₁
    rw [hn₁]
    push_cast
    linarith
  obtain ⟨t₁, u₁, v₁, hc₁', hL1₁, hL3₁, hineq₁⟩ := hP1 q L hCB z r W M K G ρ₁ J
    (fun i => lamT i + 8) lam us vs ts hW hWK hWKM hAM (by omega) (by omega)
    (by rw [hρ₁0]; omega) hρ₁step hc hL1 hL2
    (fun i => by rw [hρ₁0]; have := hL3 i; have := hvs i; omega)
    (fun i => by have := hlam i; have := hlamT i; omega)
    (fun i l hil => by have := hlamT2 i l hil; omega)
    (by have := hlamT 0; have := hlamT (Fin.last m); omega) hpot
  rw [hρ₁0, hρ₁n] at hineq₁
  rw [hρ₁n] at hL3₁
  have ht₁ : ∀ i, t₁ i = tT i := fun i => by
    have h₁ := hc₁' i
    have h₂ := (hlamT i).2.2
    have := (t₁ i).isLt
    have := (tT i).isLt
    ext
    omega
  -- phase 2: spreading along the sides
  have hNW : (2 * n₁ + 1) * W + 2 * n * W + 1 ≤ N * (W + 1) := by
    rw [hN]
    have : (2 * n₁ + 2 * n + 1) * (W + 1) = (2 * n₁ + 2 * n + 1) * W + (2 * n₁ + 2 * n + 1) :=
      by ring
    have : (2 * n₁ + 2 * n + 1) * W = (2 * n₁ + 1) * W + 2 * n * W := by ring
    omega
  obtain ⟨u₂, v₂, hfin, hineq₂⟩ := hP2 q L hCB z r W M K D S (R' - E - n * Δ₂) Δ₂
    ((2 * n₁ + 1) * W) J tT u₁ v₁ (fun i => uT i + W) hW hWK hWKM hAM hS (by omega)
    (by omega) (by rw [Nat.sub_add_cancel hnR']; omega)
    (by rw [Nat.sub_add_cancel hnR']; exact le_trans (by exact_mod_cast (show R' - E ≤ R' by
      omega)) hL)
    (by rw [Nat.sub_add_cancel hnR']; omega) hNW
    (fun i => by
      have := hL3₁ i
      push_cast
      omega)
    (fun i l hil htl => by
      have h₁ := hL1₁ i l hil
      have h₂ := (hlamT i).2.2
      have h₃ := (hlamT l).2.2
      have h₄ := hlamT i
      have h₅ := hlamT l
      rw [htl] at h₂
      omega)
    (fun i => by
      have h₁ := hTcor i
      have h₂ := hTwid i
      rw [Nat.sub_add_cancel hnR']
      push_cast
      rcases hrelT' i with ⟨-, h₃, h₄⟩ | ⟨-, h₃, h₄⟩ <;> omega)
    (fun i l hil htl => by
      have h₁ := hTord i l hil htl
      have h₂ := hrelT' l
      have h₃ := hTwid i
      have h₄ := hTwid l
      rw [← htl] at h₂
      push_cast
      rcases hrelT' i with ⟨ho, h₅, h₆⟩ | ⟨ho, h₅, h₆⟩ <;>
        rcases h₂ with ⟨ho', h₇, h₈⟩ | ⟨ho', h₇, h₈⟩ <;> omega)
  rw [Nat.sub_add_cancel hnR'] at hineq₂
  -- the last stage: new fences `(M', K')` at `R'`
  have hv₂ : ∀ i, uT i + W ≤ u₂ i ∧ v₂ i + W ≤ vT i := fun i => by
    have h₁ := hfin i
    have h₂ := hTwid i
    push_cast at h₁
    rcases hrelT' i with ⟨-, h₃, h₄⟩ | ⟨-, h₃, h₄⟩ <;> omega
  have hineq₃ := hP3 q L hCB z r R' W M K M' K' Q ((2 * (S : ℤ) - 1 : ℤ) : ℝ) J tT u₂ v₂ uT vT
    hW hWK (by omega) hM' hWKM' hQ
    (by
      have : (4 * M : ℤ) ≤ 2 * (S : ℤ) - 1 := by omega
      exact_mod_cast this)
    (by omega) hAW hAM' hL
    (fun i => by
      have h₁ := hfin i
      have h₂ : (N : ℤ) * (W + 1) ≥ (2 * n₁ + 1) * W + 2 * n * W + n + 1 := by
        have : ((2 * n₁ + 1) * W + 2 * n * W + n + 1 : ℕ) ≤ N * (W + 1) := by
          rw [hN]
          have : (2 * n₁ + 2 * n + 1) * (W + 1) =
              (2 * n₁ + 2 * n + 1) * W + (2 * n₁ + 2 * n + 1) := by ring
          have : (2 * n₁ + 2 * n + 1) * W = (2 * n₁ + 1) * W + 2 * n * W := by ring
          omega
        exact_mod_cast this
      push_cast at h₁ h₂
      linarith)
    hv₂
    (fun i => by
      have h₂ := hTcor i
      rcases hrelT' i with ⟨-, h₃, h₄⟩ | ⟨-, h₃, h₄⟩ <;> omega)
    (fun i l hil htl => by
      have h₃ := hTord i l hil htl
      have h₄ := hrelT' l
      rw [← htl] at h₄
      rcases hrelT' i with ⟨ho, h₅, h₆⟩ | ⟨ho, h₅, h₆⟩ <;>
        rcases h₄ with ⟨ho', h₇, h₈⟩ | ⟨ho', h₇, h₈⟩ <;> omega)
  rw [← hE] at hineq₃
  rw [show c₁ * c₂ * c₃ * law q _ = c₃ * (c₂ * (c₁ * law q _)) from by ring]
  refine (mul_le_mul' le_rfl ((mul_le_mul' le_rfl ((mul_le_mul' le_rfl (measure_mono ?_)).trans
    hineq₁)).trans ((mul_le_mul' le_rfl (measure_mono ?_)).trans hineq₂))).trans
    (hineq₃.trans (measure_mono ?_))
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨a, b, γ, h₁, h₂, h₃, h₄.mono ?_ le_rfl, fun i => (hmems i R (σ i) (b i)).1 (h₅ i),
      h₆⟩
    refine le_trans ?_ hs'
    push_cast
    linarith
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨a, b, γ, h₁, h₂, h₃, h₄.mono ?_ le_rfl, fun i => by rw [← ht₁ i]; exact h₅ i, h₆⟩
    have : (2 * (S : ℤ) - 1 : ℤ) ≤ 2 * ((G : ℤ) - 2 * n₁ * W) - 1 := by
      have : (S : ℤ) + 2 * n₁ * W ≤ G := by exact_mod_cast hG
      omega
    exact_mod_cast this
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, fun i => (hmemT i R' (σ i) (b i)).2 (h₅ i), h₆⟩

/-- **The motion plan: separated arms carried into prescribed windows.** For a colour sequence
`σ` without packs and ratios `A`, `n` there is `c₀ > 0` such that for every law with crossing
bounds `c` up to scale `L`: separated arms at the outer boundary of `B_R(z)` (separation
`s ≥ 2G + 4W + 2`, fences `(M, K)`, inner positions in `J`) are carried to arms to `∂B_{R'}(z)`
ending in the prescribed windows `[αT i, βT i]` on the sides `tT i` (`0` top, `1` right, `2`
bottom, `3` left; coordinates along the side), separated at scale `2Q - 1`, with fences `(M', K')`:
`c₀ P(separated at R) ≤ P(separated at R', ends in the windows)`.

The windows are in the counterclockwise order of the arms, starting from the bottom side: `lamT i`
(the side counted counterclockwise from the bottom side, `lamT i + tT i ≡ 2 (mod 4)`) is
nondecreasing in `i`, windows on one side are in counterclockwise order with gaps `S + Q`, at
least `S + Q + M + M' + W + 1` from the corners of `B_{R'}(z)` and of length at least `B`. The plan
makes `12 j` rounds of turns (radius growing by `G + M + W + 1` per round), then `n` stages of
linear spreading (radius growing by `2M + W + 1` per stage), both with the fences `(M, K)` and the
room `S ≥ 2D + 2M + 2K + W + 3` (`D ≥ 2R'/n` bounds the moves of the spreading), and a last stage
from `R' - (M + M' + W + 1)` to `R'` that changes the fences to `(M', K')` in the room
`Q ≥ 2M + 2K' + W + 3` of the target windows; `B ≥ n + (24 j + 2n + 3) W` bounds the drift of the
windows. The constant depends only on `σ`, `c`, `A`, `n`. -/
theorem exists_pos_le_law_target_windows {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S G Q B : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → 2 ≤ M' → W + K' ≤ M' →
      W + 2 * K ≤ A * (M - 1) → W + 2 * K' ≤ A * (M' - 1) →
      W + 2 * D + 2 * M + 2 * K + 3 ≤ S → S + 2 * (12 * j) * W ≤ G →
      W + 2 * M + 2 * K' + 3 ≤ Q → ((2 * G + 4 * W + 2 : ℕ) : ℝ) ≤ s → r + M + 1 < R →
      R + 12 * j * (G + M + W + 1) + n * (2 * M + W + 1) + (M + M' + W + 1) ≤ R' →
      2 * R' + 2 ≤ A * W → (R' : ℕ∞) ≤ L → 2 * R' + 2 * n + n * W ≤ n * D →
      n + (2 * (12 * j) + 2 * n + 3) * W ≤ B →
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R' + (S + Q + M + M' + W + 1) ≤ αT i ∧
        βT i + (S + Q + M + M' + W + 1) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R') →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + S + Q ≤ αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + S + Q ≤ αT i)) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
          (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i}  := by
  classical
  obtain ⟨c₀, hc₀, hbins⟩ := exists_pos_le_law_target_windows_of_bins σ hσ c A n
  obtain ⟨X, hX⟩ : ∃ X : ℝ≥0∞, X = (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) := ⟨_, rfl⟩
  have hX0 : X ≠ 0 := by rw [hX, Nat.cast_ne_zero]; positivity
  have hXt : X ≠ ⊤ := by rw [hX]; exact ENNReal.natCast_ne_top _
  refine ⟨c₀ / X, ENNReal.div_pos hc₀.ne' hXt, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT hW hWK hWKM hM' hWKM' hAM
    hAM' hS hG hQ hs hrM hRR' hAW hL hjog hB hlamT hlamT2 hTcor hTwid hTord
  have hrR : r < R := by omega
  have hRA : R ≤ A * W := by omega
  have hs4 : 4 * (M : ℝ) ≤ s := by
    refine le_trans ?_ hs
    have : 4 * M ≤ 2 * G + 4 * W + 2 := by omega
    exact_mod_cast this
  refine (mul_le_mul' le_rfl (law_le_sum_law_windows_of_separated q (σ := σ) (z := z) (K := K)
    hrR (by omega : 1 ≤ M) hW hRA hs4 J)).trans ?_
  rw [Finset.mul_sum]
  calc ∑ p : Fin j → Fin 4 × Fin (2 * A + 1), c₀ / X * law q _
      ≤ ∑ _p : Fin j → Fin 4 × Fin (2 * A + 1), X⁻¹ * law q {ω : Config (LatticeSite 2) | ∃ (a b :
          Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
            (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b :
              LatticeSite 2 |
            (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
            (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
            (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [div_eq_mul_inv, mul_comm _ X⁻¹, mul_assoc]
        exact mul_le_mul' le_rfl (hbins q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT
          (fun i => (p i).1) (fun i => (if (p i).1 = 0 ∨ (p i).1 = 2 then z 0 else z 1) - R +
            (((p i).2 : ℕ) : ℤ) * (W + 1)) hW hWK hWKM hM' hWKM' hAM hAM' hS hG hQ hs hrM hRR'
          hAW hL hjog hB hlamT hlamT2 hTcor hTwid hTord)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        rw [← mul_assoc, ← hX, ENNReal.mul_inv_cancel hX0 hXt, one_mul]

/-- **The first gluing into prescribed windows** (Nolin, Proposition 12, landing in windows). For
a colour sequence `σ` without packs and ratios `A`, `n` there is `c₀ > 0` such that for every law
with crossing bounds `c` up to scale `L`: separated arms at the outer boundary of `B_R(z)` with
separation `s ≥ 4M` and fences `(M, K)` (the form produced by the outer separation step) are
carried to arms to `∂B_{R'}(z)` ending in prescribed windows, separated at scale `2Q - 1`, with
fences `(M', K')`: `c₀ P(separated at R) ≤ P(separated at R', ends in the windows)`. A straight
first gluing (`exists_pos_le_law_separated_of_separated`, corridors of width `4W`, new fences
`(4W, W)` at `R + M + 1 + 8W`) makes room; the motion plan (`exists_pos_le_law_target_windows`,
with the fences `(4W, W)`) does the rest. Hypotheses as there, with `4W ≤ K`, `8W + 2 ≤ M`,
`2G + 20W + 2 ≤ s` and the radius budget
`R + M + 1 + 8W + 12 j (G + 5W + 1) + n (9W + 1) + (M' + 5W + 1) ≤ R'`. The constant depends only
on `σ`, `c`, `A`, `n`. -/
theorem exists_pos_le_law_target_windows_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S G Q B : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      1 ≤ W → 4 * W ≤ K → K ≤ M → 8 * W + 2 ≤ M → 4 * (M : ℝ) ≤ s → r + M + 1 < R →
      2 ≤ M' → W + K' ≤ M' → W + 2 * K' ≤ A * (M' - 1) →
      W + 2 * D + 10 * W + 3 ≤ S → S + 2 * (12 * j) * W ≤ G → W + 8 * W + 2 * K' + 3 ≤ Q →
      ((2 * G + 20 * W + 2 : ℕ) : ℝ) ≤ s →
      R + M + 1 + 8 * W + 12 * j * (G + 5 * W + 1) + n * (9 * W + 1) + (M' + 5 * W + 1) ≤ R' →
      2 * R' + 2 ≤ A * W → (R' : ℕ∞) ≤ L → 2 * R' + 2 * n + n * W ≤ n * D →
      n + (2 * (12 * j) + 2 * n + 3) * W ≤ B →
      (∀ i, 0 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R' + (S + Q + 4 * W + M' + W + 1) ≤ αT i ∧
        βT i + (S + Q + 4 * W + M' + W + 1) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R') →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + S + Q ≤ αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + S + Q ≤ αT i)) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
          (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₁, hc₁, hg⟩ := exists_pos_le_law_separated_of_separated σ hσ c A (A + 4)
  obtain ⟨c₂, hc₂, hp⟩ := exists_pos_le_law_target_windows σ hσ c A n
  refine ⟨c₂ * c₁, ENNReal.mul_pos hc₂.ne' hc₁.ne', ?_⟩
  intro q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT hW hWK hKM hWM hs hrM hM' hWKM'
    hAM' hS hG hQ hs' hRR' hAW hL hjog hB hlamT hlamT2 hTcor hTwid hTord
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h
      omega
    · exact h
  have hWR : W ≤ R := by omega
  have hRA : R ≤ A * (4 * W) := by
    have : A * W ≤ A * (4 * W) := Nat.mul_le_mul_left A (by omega)
    omega
  have hRD : R + M + 1 + 8 * W + 4 * W ≤ (A + 4) * R := by
    have h₁ : (A + 4) * W ≤ (A + 4) * R := Nat.mul_le_mul_left _ hWR
    have h₂ : (A + 4) * W = A * W + 4 * W := by ring
    omega
  have h₁ := hg q L hCB z r R (R + M + 1 + 8 * W) (4 * W) M K (4 * W) W s J hW le_rfl hWK hKM
    (by omega) le_rfl hs hrM (by omega) hRD hRA
    (le_trans (by exact_mod_cast (show R + M + 1 + 8 * W ≤ R' by omega)) hL)
  have h₂ := hp q L hCB z r (R + M + 1 + 8 * W) R' W (4 * W) W M' K' D S G Q B
    (s - 4 * ((4 * W : ℕ) : ℝ)) J tT lamT αT βT hW le_rfl (by omega) hM' hWKM'
    (by
      have : 3 * W ≤ 4 * W - 1 := by omega
      have : 4 * W - 1 ≤ A * (4 * W - 1) := Nat.le_mul_of_pos_left _ hA
      omega)
    hAM' (by omega) hG (by omega) (by push_cast at hs' ⊢; linarith) (by omega) (by
      have : 12 * j * (G + 5 * W + 1) = 12 * j * (G + 4 * W + W + 1) := by ring
      have : n * (9 * W + 1) = n * (2 * (4 * W) + W + 1) := by ring
      omega) hAW hL hjog hB hlamT hlamT2 (fun i => by
        have := hTcor i
        constructor <;> omega) hTwid hTord
  calc c₂ * c₁ * law q _ = c₂ * (c₁ * law q _) := mul_assoc _ _ _
    _ ≤ c₂ * law q _ := mul_le_mul' le_rfl h₁
    _ ≤ _ := h₂

end Plan

end PercLib.Models.Planar
