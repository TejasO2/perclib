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

public import PercLib.Models.Planar.Arms.HalfFirstGluing
public import PercLib.Models.Planar.Arms.HalfRotationGluing
public import PercLib.Models.Planar.Arms.MotionPlan

/-!
# The motion plan in the half-plane: separated arms carried into prescribed windows

Separated arms of the half-plane `{v | z₁ ≤ v₁}` at the outer boundary of `B_R(z)` (landing in
increasing order, without two consecutive arms of one colour, at least `s` from each other, from
the corners and from the two points of the line on the boundary) are carried, through a fixed
number of stages of moves (`exists_pos_le_law_windows_of_moves_half`), into prescribed windows on
the top side and the upper halves of the right and left sides of a larger box `B_{R'}(z)`, in the
same order. The plan has three phases: rounds of turns at the two upper corners (counterclockwise
by the last arm of a side, clockwise by the first), until every arm is on the side of its window;
a linear spreading along each side; a last stage that changes the fences.

## Main results

* `exists_pos_le_law_ccw_of_moves_half`: the stage of moves in the half-plane in counterclockwise
  coordinates, with the moved windows only required to contain the images.
* `exists_turn_step_half`: one round of turns (pure combinatorics): at each upper corner the last
  arm of the side before it turns counterclockwise if its target lies beyond the corner, otherwise
  the first arm of the side after it turns clockwise if its target lies before the corner; the
  order, the gaps and the margins from the corners and the line are kept, and the number of turns
  left drops while positive.
* `exists_lift_of_separated_half`: the bins of separated arms of the half-plane as lifted sides
  `1` (right), `2` (top), `3` (left) in lexicographic order (the start of the plan).
* `exists_pos_le_law_turns_half`, `exists_pos_le_law_spread_half`,
  `exists_pos_le_law_fences_of_windows_half`: the three phases.
* `exists_pos_le_law_half_target_windows`: **the motion plan in the half-plane** (the window step
  of Theorem 11 for half-plane arms).
* `exists_pos_le_law_half_target_windows_of_separated`: the same from the separated event of the
  half-plane outer separation step, through the straight first gluing (the gluing step).

## Implementation notes

Windows are written in the counterclockwise coordinates of `MotionPlan.lean`: on the right side
`u = y - z₁`, on the top side `u = z₀ - x`, on the left side `u = z₁ - y`; the upper half of the
boundary is `u ≥ 0` on the right side and `u ≤ 0` on the left side. Lifted sides `lam ∈ {1, 2, 3}`
(`lam + t ≡ 2 (mod 4)`) order the sides from the right to the left; the arms stay in
lexicographic order of `(lam, u)` along their index. A counterclockwise turn lands in
`[-h - W, -h]` (the start of the next side), a clockwise turn in `[h, h + W]` (the end of the
previous side).
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The stage of moves in counterclockwise coordinates -/

section Stage

variable {j : ℕ}

/-- **The stage of moves in the half-plane in counterclockwise coordinates**
(`exists_pos_le_law_windows_of_moves_half`). Windows `[u i, v i]` on the sides `t i ≠ 2` of
`B_R(z)` in counterclockwise coordinates, at least `S` from the corners, from the line (on the
right and left sides) and from each other on one side; arm `i` jogs by `e i` (`τ i = 0`), turns
counterclockwise at the level `h` when it is the last of its side (`τ i = 1`, right → top,
top → left, landing in `[-h - W, -h]`), or turns clockwise when it is the first of its side
(`τ i = 2`, top → right, left → top, landing in `[h, h + W]`); no corner is turned both ways. The
new windows `[u' i, v' i]` only need to contain the images. The constant depends only on `σ`,
`c`, `A`, `N`. -/
theorem exists_pos_le_law_ccw_of_moves_half (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S : ℕ) (h : ℤ) (s : ℝ)
      (g' : ℤ) (J : Fin j → Set ℤ) (t t' : Fin j → Fin 4) (τ : Fin j → Fin 3)
      (u v e u' v' : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2 * D + 2 * M + 2 * K' + 3 ≤ S →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → (R : ℤ) + M + 1 ≤ h → h + W + M' ≤ R' →
      2 * R' + 2 ≤ A * W → W + 2 * K' ≤ A * (M' - 1) → (R' : ℕ∞) ≤ L →
      (∀ i, -(D : ℤ) ≤ e i ∧ e i ≤ D) → (∀ i, v i - u i + 1 ≤ N * ((W : ℤ) + 1)) →
      (∀ i, t i ≠ 2) → (∀ i, -(R : ℤ) + S ≤ u i ∧ v i + S ≤ R) →
      (∀ i, (t i = 1 → (S : ℤ) ≤ u i) ∧ (t i = 3 → v i + S ≤ 0)) →
      (∀ i k, i ≠ k → t i = t k → v i + S ≤ u k ∨ v k + S ≤ u i) →
      (∀ i k, i ≠ k → τ i = 1 → t k = t i → v k + S ≤ u i) →
      (∀ i k, i ≠ k → τ i = 2 → t k = t i → v i + S ≤ u k) →
      (∀ i k, τ i = 2 → τ k = 1 → ¬(t i = 0 ∧ t k = 1) ∧ ¬(t i = 3 ∧ t k = 0)) →
      (∀ i, (τ i = 0 ∧ t' i = t i ∧ u' i ≤ u i + e i - W ∧ v i + e i + W ≤ v' i) ∨
        (τ i = 1 ∧ ((t i = 1 ∧ t' i = 0) ∨ (t i = 0 ∧ t' i = 3)) ∧ u' i ≤ -h - W ∧ -h ≤ v' i) ∨
        (τ i = 2 ∧ ((t i = 0 ∧ t' i = 1) ∨ (t i = 3 ∧ t' i = 0)) ∧ u' i ≤ h ∧ h + W ≤ v' i)) →
      1 ≤ g' → (∀ i, -(R' : ℤ) + g' ≤ u' i ∧ v' i + g' ≤ R') →
      (∀ i k, i ≠ k → t' i = t' k → v' i + g' ≤ u' k ∨ v' k + g' ≤ u' i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + R ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
          (t i = 1 ∧ b i 0 = z 0 + R ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
          (t i = 2 ∧ b i 1 = z 1 - R - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ b i 0 = z 0 - R - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧
        (∀ i,
          (t' i = 0 ∧ b i 1 = z 1 + R' ∧ z 0 - v' i ≤ b i 0 ∧ b i 0 ≤ z 0 - u' i) ∨
          (t' i = 1 ∧ b i 0 = z 0 + R' ∧ z 1 + u' i ≤ b i 1 ∧ b i 1 ≤ z 1 + v' i) ∨
          (t' i = 2 ∧ b i 1 = z 1 - R' - cond (σ i) 0 1 ∧ z 0 + u' i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v' i) ∨
          (t' i = 3 ∧ b i 0 = z 0 - R' - cond (σ i) 0 1 ∧ z 1 - v' i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u' i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₀, hc₀, hst⟩ := exists_pos_le_law_windows_of_moves_half σ hσ c A N
  refine ⟨c₀, hc₀, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S h s g' J t t' τ u v e u' v' hW hWK hKM hM' hWM' hS hs
    hrM hh hhR hAW hAM hR'L he hN ht hwin hline hgap hccw hcw hcorner hout hg' hcor' hgap'
  choose α β hαβ hmem using fun i => exists_side_window (t i) z (u i) (v i)
  choose α₁ β₁ hαβ₁ hmem₁ using fun i => exists_side_window (t' i) z (u' i) (v' i)
  -- the exact moves of the stage lemma, inside the given windows
  have hmove : ∀ i, ∃ d α' β' : ℤ, (-(D : ℤ) ≤ d ∧ d ≤ D) ∧
      ((τ i = 0 ∧ t' i = t i ∧ α' = α i + d ∧ β' = β i + d + W) ∨
        (τ i = 1 ∧ ((t i = 1 ∧ t' i = 0 ∧ α' = z 0 + h ∧ β' = z 0 + h + W) ∨
          (t i = 0 ∧ t' i = 3 ∧ α' = z 1 + h ∧ β' = z 1 + h + W))) ∨
        (τ i = 2 ∧ ((t i = 0 ∧ t' i = 1 ∧ α' = z 1 + h ∧ β' = z 1 + h + W) ∨
          (t i = 3 ∧ t' i = 0 ∧ α' = z 0 - h - W ∧ β' = z 0 - h)))) ∧
      α₁ i ≤ α' ∧ β' ≤ β₁ i := by
    intro i
    have hei := he i
    rcases hout i with ⟨hτ, ht', hu, hv⟩ | ⟨hτ, hturn, hu, hv⟩ | ⟨hτ, hturn, hu, hv⟩
    · rcases hαβ i with ⟨h₀, hα, hβ⟩ | ⟨h₀, hα, hβ⟩ | ⟨h₀, hα, hβ⟩ | ⟨h₀, hα, hβ⟩
      · refine ⟨-e i, α i + -e i, β i + -e i + W, by omega, Or.inl ⟨hτ, ht', rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨e i, α i + e i, β i + e i + W, by omega, Or.inl ⟨hτ, ht', rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨e i, α i + e i, β i + e i + W, by omega, Or.inl ⟨hτ, ht', rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨-e i, α i + -e i, β i + -e i + W, by omega, Or.inl ⟨hτ, ht', rfl, rfl⟩, ?_⟩
        rcases hαβ₁ i with ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ | ⟨h₁, hα₁, hβ₁⟩ <;>
          omega
    · rcases hturn with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · refine ⟨0, z 0 + h, z 0 + h + W, by omega,
          Or.inr (Or.inl ⟨hτ, Or.inl ⟨h₀, h₁, rfl, rfl⟩⟩), ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨0, z 1 + h, z 1 + h + W, by omega,
          Or.inr (Or.inl ⟨hτ, Or.inr ⟨h₀, h₁, rfl, rfl⟩⟩), ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
    · rcases hturn with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · refine ⟨0, z 1 + h, z 1 + h + W, by omega,
          Or.inr (Or.inr ⟨hτ, Or.inl ⟨h₀, h₁, rfl, rfl⟩⟩), ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
      · refine ⟨0, z 0 - h - W, z 0 - h, by omega,
          Or.inr (Or.inr ⟨hτ, Or.inr ⟨h₀, h₁, rfl, rfl⟩⟩), ?_⟩
        rcases hαβ₁ i with ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ | ⟨h₂, hα₁, hβ₁⟩ <;>
          omega
  choose d α' β' hd hmv hle using hmove
  have hc := fun i => side_center_eq (hαβ i)
  have hc₁ := fun i => side_center_eq (hαβ₁ i)
  -- a clockwise turning arm is on the top side or the left side
  have hcwside : ∀ i, τ i = 2 → t i = 0 ∨ t i = 3 := fun i hτ => by
    rcases hout i with ⟨hτ', -⟩ | ⟨hτ', -⟩ | ⟨-, hturn, -⟩
    · rw [hτ] at hτ'
      exact absurd hτ' (by decide)
    · rw [hτ] at hτ'
      exact absurd hτ' (by decide)
    · rcases hturn with ⟨h₀, -⟩ | ⟨h₀, -⟩
      · exact Or.inl h₀
      · exact Or.inr h₀
  have key := hst q L hCB z r R R' W M K M' K' D S h s g' J t t' τ α β d α' β' hW hWK hKM hM'
    hWM' hS hs hrM hh hhR hAW hAM hR'L hd (fun i => by
      have : β i - α i = v i - u i := by rcases hc i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega
      linarith [hN i])
    ht (fun i => by have := hwin i; rcases hc i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega)
    (fun i hti => by
      obtain ⟨h1, h3⟩ := hline i
      rcases hαβ i with ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩ | ⟨h₀, hα, -⟩
      · exact absurd h₀ hti
      · have := h1 h₀
        omega
      · exact absurd h₀ (ht i)
      · have := h3 h₀
        omega)
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
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩ <;>
      rcases hc i with ⟨ho, hαi, hβi⟩ | ⟨ho, hαi, hβi⟩ <;>
        rcases h₂ with ⟨ho', hαk, hβk⟩ | ⟨ho', hαk, hβk⟩ <;> omega)
    (fun i k hik hτ htk => by
      have h₁ := hcw i k hik hτ htk
      have h₀ := hcwside i hτ
      have h₂ := hc k
      rw [htk] at h₂
      rcases hc i with ⟨ho, hαi, hβi⟩ | ⟨ho, hαi, hβi⟩ <;>
        rcases h₂ with ⟨ho', hαk, hβk⟩ | ⟨ho', hαk, hβk⟩ <;> omega)
    hcorner hmv hg'
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
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, fun i => (hmem i R (σ i) (b i)).1 (h₆ i), h₇⟩
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, fun i => (hmem₁ i R' (σ i) (b i)).2
      (mem_side_window_of_le (hle i).1 (hle i).2 (h₆ i)), h₇⟩

end Stage

/-! ### Rounds of turns at the two upper corners -/

section Turns

variable {j : ℕ}

/-- **Arms on one side are apart** (no wrap): for arms in lexicographic order of lifted side
`lam ∈ [1, 3]` and position along their index with gaps `G`, two arms on the same side are `G`
apart. -/
theorem gap_of_lex_half {lam u v : Fin j → ℤ} {t : Fin j → Fin 4} {G : ℤ}
    (hc : ∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2) (hlam : ∀ i, 1 ≤ lam i ∧ lam i ≤ 3)
    (hL1 : ∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l)) :
    ∀ i k, i ≠ k → t i = t k → v i + G ≤ u k ∨ v k + G ≤ u i := by
  intro i k hik htk
  have h₁ := hc i
  have h₂ := hc k
  rw [htk] at h₁
  have := hlam i
  have := hlam k
  have heq : lam i = lam k := by omega
  rcases lt_or_gt_of_ne hik with h | h
  · rcases hL1 i k h with h' | h' <;> omega
  · rcases hL1 k i h with h' | h' <;> omega

/-- The side of an arm from its lifted side: `1` right, `2` top, `3` left. -/
theorem side_of_lift_half {lam : ℤ} {t : Fin 4} (hc : (lam + ((t : ℕ) : ℤ)) % 4 = 2)
    (hlam : 1 ≤ lam ∧ lam ≤ 3) :
    (lam = 1 ∧ t = 1) ∨ (lam = 2 ∧ t = 0) ∨ (lam = 3 ∧ t = 3) := by
  have := t.isLt
  rcases (show lam = 1 ∨ lam = 2 ∨ lam = 3 by omega) with e | e | e
  · exact Or.inl ⟨e, Fin.ext (by simp only [Fin.val_one]; omega)⟩
  · exact Or.inr (Or.inl ⟨e, Fin.ext (by simp only [Fin.val_zero]; omega)⟩)
  · exact Or.inr (Or.inr ⟨e, Fin.ext (by
      change (t : ℕ) = 3
      omega)⟩)

/-- **One round of turns in the half-plane** (pure combinatorics). Windows `[u i, v i]` in
counterclockwise coordinates on the sides `t i` of `B_ρ(z)`, with lifted sides `lam i ∈ [1, 3]`
(`1` right, `2` top, `3` left; `lam i + t i ≡ 2 (mod 4)`) in lexicographic order of `(lam, u)`
along the index with gaps `G`, at least `G` from the corners and, on the right and left sides,
from the line; target lifted sides `lamT i ∈ [1, 3]`, nondecreasing. At the top-right corner the
last arm of the right side turns counterclockwise if its target is beyond the corner, otherwise
the first arm of the top side turns clockwise if its target is the right side; at the top-left
corner the last arm of the top side turns counterclockwise if its target is the left side,
otherwise the first arm of the left side turns clockwise if its target is before the corner.
Counterclockwise turns land in `[-h - W, -h]`, clockwise turns in `[h, h + W]`; the other arms
stay and their windows widen by `W` at both ends. Then the new arms satisfy the same conditions at
`B_{ρ'}(z)` with gaps `G - 2W`, and the number of turns left, `Σ |lamT - lam|`, drops while
positive. -/
theorem exists_turn_step_half {lam lamT u v : Fin j → ℤ} {t : Fin j → Fin 4}
    {ρ ρ' W G h : ℤ} (hW : 0 ≤ W) (hG : 2 * W ≤ G)
    (hc : ∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2) (hlam : ∀ i, 1 ≤ lam i ∧ lam i ≤ 3)
    (hL1 : ∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l))
    (hL3 : ∀ i, -ρ + G ≤ u i ∧ v i + G ≤ ρ ∧ u i ≤ v i)
    (hL4 : ∀ i, (lam i = 1 → G ≤ u i) ∧ (lam i = 3 → v i + G ≤ 0))
    (hT1 : ∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3) (hT2 : ∀ i l, i ≤ l → lamT i ≤ lamT l)
    (hρh : ρ ≤ h + W) (hρ' : h + W + (G - 2 * W) ≤ ρ') (hρρ' : ρ ≤ ρ') :
    ∃ (τ : Fin j → Fin 3) (lam' : Fin j → ℤ) (t' : Fin j → Fin 4) (u' v' : Fin j → ℤ),
      (∀ i k, i ≠ k → τ i = 1 → t k = t i → v k + G ≤ u i) ∧
      (∀ i k, i ≠ k → τ i = 2 → t k = t i → v i + G ≤ u k) ∧
      (∀ i k, τ i = 2 → τ k = 1 → ¬(t i = 0 ∧ t k = 1) ∧ ¬(t i = 3 ∧ t k = 0)) ∧
      (∀ i, (τ i = 0 ∧ t' i = t i ∧ lam' i = lam i ∧ u' i = u i - W ∧ v' i = v i + W) ∨
        (τ i = 1 ∧ ((t i = 1 ∧ t' i = 0) ∨ (t i = 0 ∧ t' i = 3)) ∧ lam' i = lam i + 1 ∧
          u' i = -h - W ∧ v' i = -h) ∨
        (τ i = 2 ∧ ((t i = 0 ∧ t' i = 1) ∨ (t i = 3 ∧ t' i = 0)) ∧ lam' i = lam i - 1 ∧
          u' i = h ∧ v' i = h + W)) ∧
      (∀ i, (lam' i + ((t' i : ℕ) : ℤ)) % 4 = 2) ∧ (∀ i, 1 ≤ lam' i ∧ lam' i ≤ 3) ∧
      (∀ i l, i < l → lam' i < lam' l ∨ (lam' i = lam' l ∧ v' i + (G - 2 * W) ≤ u' l)) ∧
      (∀ i, -ρ' + (G - 2 * W) ≤ u' i ∧ v' i + (G - 2 * W) ≤ ρ' ∧ u' i ≤ v' i) ∧
      (∀ i, (lam' i = 1 → G - 2 * W ≤ u' i) ∧ (lam' i = 3 → v' i + (G - 2 * W) ≤ 0)) ∧
      (∑ i, |lamT i - lam' i| ≤ ∑ i, |lamT i - lam i|) ∧
      (0 < ∑ i, |lamT i - lam i| → ∑ i, |lamT i - lam' i| < ∑ i, |lamT i - lam i|) := by
  classical
  have hmono : ∀ i l, i ≤ l → lam i ≤ lam l := fun i l hil => by
    rcases hil.lt_or_eq with h | h
    · rcases hL1 i l h with h | h <;> omega
    · rw [h]
  have hside := fun i => side_of_lift_half (hc i) (hlam i)
  have hρG : ∀ i, 2 * G ≤ 2 * ρ := fun i => by have := hL3 i; omega
  -- the turning rule
  obtain ⟨P₁, hP₁⟩ : ∃ P : Fin j → Prop, ∀ i, P i ↔
      (lam i < lamT i ∧ ∀ l, i < l → lam i < lam l) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P : Fin j → Prop, ∀ i, P i ↔
      (lamT i < lam i ∧ (∀ l, l < i → lam l < lam i) ∧ ∀ k, P₁ k → lam k ≠ lam i - 1) :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ f : Fin j → Fin 3, ∀ i, f i = if P₁ i then 1 else if P₂ i then 2 else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨lam', hlam'⟩ : ∃ f : Fin j → ℤ, ∀ i,
      f i = if P₁ i then lam i + 1 else if P₂ i then lam i - 1 else lam i := ⟨_, fun _ => rfl⟩
  obtain ⟨t', ht'⟩ : ∃ f : Fin j → Fin 4, ∀ i, f i = if P₁ i then (if t i = 1 then 0 else 3)
      else if P₂ i then (if t i = 0 then 1 else 0) else t i := ⟨_, fun _ => rfl⟩
  obtain ⟨u', hu'⟩ : ∃ f : Fin j → ℤ, ∀ i,
      f i = if P₁ i then -h - W else if P₂ i then h else u i - W := ⟨_, fun _ => rfl⟩
  obtain ⟨v', hv'⟩ : ∃ f : Fin j → ℤ, ∀ i,
      f i = if P₁ i then -h else if P₂ i then h + W else v i + W := ⟨_, fun _ => rfl⟩
  have hcase : ∀ i,
      (P₁ i ∧ τ i = 1 ∧ lam' i = lam i + 1 ∧ u' i = -h - W ∧ v' i = -h ∧
        ((lam i = 1 ∧ t i = 1 ∧ t' i = 0) ∨ (lam i = 2 ∧ t i = 0 ∧ t' i = 3))) ∨
      (¬ P₁ i ∧ P₂ i ∧ τ i = 2 ∧ lam' i = lam i - 1 ∧ u' i = h ∧ v' i = h + W ∧
        ((lam i = 2 ∧ t i = 0 ∧ t' i = 1) ∨ (lam i = 3 ∧ t i = 3 ∧ t' i = 0))) ∨
      (¬ P₁ i ∧ ¬ P₂ i ∧ τ i = 0 ∧ lam' i = lam i ∧ t' i = t i ∧ u' i = u i - W ∧
        v' i = v i + W) := fun i => by
    by_cases h₁ : P₁ i
    · left
      refine ⟨h₁, by rw [hτ, ite_eq_left h₁], by rw [hlam', ite_eq_left h₁], by rw [hu',
          ite_eq_left h₁],
        by rw [hv', ite_eq_left h₁], ?_⟩
      have hlt := ((hP₁ i).1 h₁).1
      have := hT1 i
      rw [ht', ite_eq_left h₁]
      rcases hside i with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
      · exact Or.inl ⟨e, e', by rw [ite_eq_left e']⟩
      · exact Or.inr ⟨e, e', by rw [ite_eq_right (by rw [e']; decide)]⟩
      · omega
    · by_cases h₂ : P₂ i
      · right; left
        refine ⟨h₁, h₂, by rw [hτ, ite_eq_right h₁, ite_eq_left h₂], by rw [hlam', ite_eq_right h₁,
            ite_eq_left h₂],
          by rw [hu', ite_eq_right h₁, ite_eq_left h₂], by rw [hv', ite_eq_right h₁, ite_eq_left
              h₂], ?_⟩
        have hlt := ((hP₂ i).1 h₂).1
        have := hT1 i
        rw [ht', ite_eq_right h₁, ite_eq_left h₂]
        rcases hside i with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
        · omega
        · exact Or.inl ⟨e, e', by rw [ite_eq_left e']⟩
        · exact Or.inr ⟨e, e', by rw [ite_eq_right (by rw [e']; decide)]⟩
      · right; right
        exact ⟨h₁, h₂, by rw [hτ, ite_eq_right h₁, ite_eq_right h₂], by rw [hlam', ite_eq_right h₁,
            ite_eq_right h₂],
          by rw [ht', ite_eq_right h₁, ite_eq_right h₂], by rw [hu', ite_eq_right h₁, ite_eq_right
              h₂],
          by rw [hv', ite_eq_right h₁, ite_eq_right h₂]⟩
  -- the lifted side is determined by the side
  have hlamt : ∀ i k, t k = t i → lam k = lam i := fun i k htk => by
    have h₁ := hc i
    have h₂ := hc k
    rw [htk] at h₂
    have := hlam i
    have := hlam k
    omega
  refine ⟨τ, lam', t', u', v', fun i k hik hτi htk => ?_, fun i k hik hτi htk => ?_,
    fun i k hτi hτk => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i l hil => ?_,
    fun i => ?_, fun i => ?_, ?_, fun hpos => ?_⟩
  · -- a counterclockwise turning arm is the last of its side
    have hP : P₁ i := by
      rcases hcase i with ⟨h₁, -⟩ | ⟨-, -, h₂, -⟩ | ⟨-, -, h₂, -⟩
      · exact h₁
      · rw [hτi] at h₂; exact absurd h₂ (by decide)
      · rw [hτi] at h₂; exact absurd h₂ (by decide)
    have heq := hlamt i k htk
    rcases lt_or_gt_of_ne hik with hlt | hlt
    · have := ((hP₁ i).1 hP).2 k hlt
      omega
    · rcases hL1 k i hlt with h' | h' <;> omega
  · -- a clockwise turning arm is the first of its side
    have hP : P₂ i := by
      rcases hcase i with ⟨-, h₂, -⟩ | ⟨-, h₁, -⟩ | ⟨-, -, h₂, -⟩
      · rw [hτi] at h₂; exact absurd h₂ (by decide)
      · exact h₁
      · rw [hτi] at h₂; exact absurd h₂ (by decide)
    have heq := hlamt i k htk
    rcases lt_or_gt_of_ne hik with hlt | hlt
    · rcases hL1 i k hlt with h' | h' <;> omega
    · have := ((hP₂ i).1 hP).2.1 k hlt
      omega
  · -- no corner is turned both ways
    have hP : P₂ i := by
      rcases hcase i with ⟨-, h₂, -⟩ | ⟨-, h₁, -⟩ | ⟨-, -, h₂, -⟩
      · rw [hτi] at h₂; exact absurd h₂ (by decide)
      · exact h₁
      · rw [hτi] at h₂; exact absurd h₂ (by decide)
    have hQ : P₁ k := by
      rcases hcase k with ⟨h₁, -⟩ | ⟨-, -, h₂, -⟩ | ⟨-, -, h₂, -⟩
      · exact h₁
      · rw [hτk] at h₂; exact absurd h₂ (by decide)
      · rw [hτk] at h₂; exact absurd h₂ (by decide)
    have hne := ((hP₂ i).1 hP).2.2 k hQ
    have hsi := hside i
    have hsk := hside k
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
    · rw [h₁] at hsi
      rw [h₂] at hsk
      simp at hsi hsk
      omega
    · rw [h₁] at hsi
      rw [h₂] at hsk
      simp at hsi hsk
      omega
  · rcases hcase i with ⟨-, h₁, h₂, h₃, h₄, h₅⟩ | ⟨-, -, h₁, h₂, h₃, h₄, h₅⟩ |
      ⟨-, -, h₁, h₂, h₃, h₄, h₅⟩
    · refine Or.inr (Or.inl ⟨h₁, ?_, h₂, h₃, h₄⟩)
      rcases h₅ with ⟨-, e, e'⟩ | ⟨-, e, e'⟩
      · exact Or.inl ⟨e, e'⟩
      · exact Or.inr ⟨e, e'⟩
    · refine Or.inr (Or.inr ⟨h₁, ?_, h₂, h₃, h₄⟩)
      rcases h₅ with ⟨-, e, e'⟩ | ⟨-, e, e'⟩
      · exact Or.inl ⟨e, e'⟩
      · exact Or.inr ⟨e, e'⟩
    · exact Or.inl ⟨h₁, h₃, h₂, h₄, h₅⟩
  · rcases hcase i with ⟨-, -, h₂, -, -, h₅⟩ | ⟨-, -, -, h₂, -, -, h₅⟩ |
      ⟨-, -, -, h₂, h₃, -, -⟩
    · rcases h₅ with ⟨e, -, e'⟩ | ⟨e, -, e'⟩ <;> rw [h₂, e'] <;> simp [e]
    · rcases h₅ with ⟨e, -, e'⟩ | ⟨e, -, e'⟩ <;> rw [h₂, e'] <;> simp [e]
    · rw [h₂, h₃]
      exact hc i
  · have := hlam i
    rcases hcase i with ⟨-, -, h₂, -, -, h₅⟩ | ⟨-, -, -, h₂, -, -, h₅⟩ |
      ⟨-, -, -, h₂, -⟩
    · rcases h₅ with ⟨e, -⟩ | ⟨e, -⟩ <;> omega
    · rcases h₅ with ⟨e, -⟩ | ⟨e, -⟩ <;> omega
    · omega
  · -- the lexicographic order after the round
    have hl1 := hL1 i l hil
    have hli := hmono i l hil.le
    have e₁ := hL3 i
    have e₂ := hL3 l
    have e₃ := hρG i
    rcases hcase i with ⟨hi₁, -, hi₃, hi₄, hi₅, -⟩ | ⟨hi₀, hi₁, -, hi₃, hi₄, hi₅, -⟩ |
        ⟨hi₀, hi₁, -, hi₃, -, hi₄, hi₅⟩ <;>
      rcases hcase l with ⟨hl₁, -, hl₃, hl₄, hl₅, -⟩ | ⟨hl₀, hl₁, -, hl₃, hl₄, hl₅, -⟩ |
        ⟨hl₀, hl₁, -, hl₃, -, hl₄, hl₅⟩
    · have := ((hP₁ i).1 hi₁).2 l hil
      omega
    · have := ((hP₁ i).1 hi₁).2 l hil
      have := ((hP₂ l).1 hl₁).2.2 i hi₁
      omega
    · have := ((hP₁ i).1 hi₁).2 l hil
      omega
    · omega
    · have := ((hP₂ l).1 hl₁).2.1 i hil
      omega
    · omega
    · omega
    · have := ((hP₂ l).1 hl₁).2.1 i hil
      omega
    · rcases hl1 with h' | h' <;> omega
  · have e₁ := hL3 i
    have e₂ := hρG i
    rcases hcase i with ⟨-, -, -, h₃, h₄, -⟩ | ⟨-, -, -, -, h₃, h₄, -⟩ | ⟨-, -, -, -, -, h₃, h₄⟩ <;>
      omega
  · have e₁ := hL3 i
    have e₂ := hρG i
    have e₃ := hL4 i
    rcases hcase i with ⟨-, -, h₂, h₃, h₄, h₅⟩ | ⟨-, -, -, h₂, h₃, h₄, h₅⟩ |
        ⟨-, -, -, h₂, -, h₃, h₄⟩
    · rcases h₅ with ⟨e, -⟩ | ⟨e, -⟩
      · exact ⟨fun h' => by omega, fun h' => by omega⟩
      · exact ⟨fun h' => by omega, fun _ => by omega⟩
    · rcases h₅ with ⟨e, -⟩ | ⟨e, -⟩
      · exact ⟨fun _ => by omega, fun h' => by omega⟩
      · exact ⟨fun h' => by omega, fun h' => by omega⟩
    · refine ⟨fun h' => ?_, fun h' => ?_⟩
      · have := e₃.1 (by omega)
        omega
      · have := e₃.2 (by omega)
        omega
  · -- the number of turns left does not grow
    refine Finset.sum_le_sum fun i _ => ?_
    have := hT1 i
    rcases abs_cases (lamT i - lam' i) with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩ <;>
      rcases abs_cases (lamT i - lam i) with ⟨b₁, b₂⟩ | ⟨b₁, b₂⟩ <;>
      rcases hcase i with ⟨h₁, -, h₂, -⟩ | ⟨-, h₁, -, h₂, -⟩ | ⟨-, -, -, h₂, -⟩
    all_goals first
      | omega
      | (have := ((hP₁ i).1 h₁).1; omega)
      | (have := ((hP₂ i).1 h₁).1; omega)
  · -- some arm turns
    have hex : ∃ i, P₁ i ∨ P₂ i := by
      obtain ⟨i₀, hi₀⟩ : ∃ i, lam i ≠ lamT i := by
        by_contra hne
        push Not at hne
        have : ∑ i, |lamT i - lam i| = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hne i, sub_self, abs_zero]
        omega
      by_cases hA : ∃ i, lam i < lamT i
      · set S := Finset.univ.filter fun i => lam i < lamT i with hS
        have hSne : S.Nonempty := by
          obtain ⟨i, hi⟩ := hA
          exact ⟨i, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩⟩
        set i₁ := S.max' hSne with hi₁
        have hi₁S : lam i₁ < lamT i₁ := by
          have := S.max'_mem hSne
          rw [← hi₁, hS, Finset.mem_filter] at this
          exact this.2
        refine ⟨i₁, Or.inl ((hP₁ i₁).2 ⟨hi₁S, fun l hl => ?_⟩)⟩
        by_contra hle
        have h₁ := hmono i₁ l hl.le
        have h₂ := hT2 i₁ l hl.le
        have : l ≤ i₁ :=
          S.le_max' l (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega⟩)
        exact absurd hl (not_lt.2 this)
      · push Not at hA
        set S := Finset.univ.filter fun i => lamT i < lam i with hS
        have hSne : S.Nonempty :=
          ⟨i₀, by
            rw [hS, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, lt_of_le_of_ne (hA i₀) (Ne.symm hi₀)⟩⟩
        set i₂ := S.min' hSne with hi₂
        have hi₂S : lamT i₂ < lam i₂ := by
          have := S.min'_mem hSne
          rw [← hi₂, hS, Finset.mem_filter] at this
          exact this.2
        refine ⟨i₂, Or.inr ((hP₂ i₂).2 ⟨hi₂S, fun l hl => ?_, fun k hk => ?_⟩)⟩
        · by_contra hle
          have h₁ := hmono l i₂ hl.le
          have h₂ := hT2 l i₂ hl.le
          have : i₂ ≤ l :=
            S.min'_le l (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega⟩)
          exact absurd hl (not_lt.2 this)
        · exact absurd ((hP₁ k).1 hk).1 (not_lt.2 (hA k))
    obtain ⟨i, hi⟩ := hex
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · have := hT1 k
      rcases abs_cases (lamT k - lam' k) with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩ <;>
        rcases abs_cases (lamT k - lam k) with ⟨b₁, b₂⟩ | ⟨b₁, b₂⟩ <;>
        rcases hcase k with ⟨h₁, -, h₂, -⟩ | ⟨-, h₁, -, h₂, -⟩ | ⟨-, -, -, h₂, -⟩
      all_goals first
        | omega
        | (have := ((hP₁ k).1 h₁).1; omega)
        | (have := ((hP₂ k).1 h₁).1; omega)
    · rcases abs_cases (lamT i - lam' i) with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩ <;>
        rcases abs_cases (lamT i - lam i) with ⟨b₁, b₂⟩ | ⟨b₁, b₂⟩ <;>
        rcases hcase i with ⟨h₁, -, h₂, -⟩ | ⟨h₀, h₁, -, h₂, -⟩ | ⟨h₀, h₁, -⟩
      all_goals first
        | omega
        | (have := ((hP₁ i).1 h₁).1; omega)
        | (have := ((hP₂ i).1 h₁).1; omega)
        | (rcases hi with hi | hi <;> contradiction)

end Turns

/-! ### The start of the plan -/

section Start

variable {j : ℕ} {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ}

/-- **The start of the plan in the half-plane.** Arms to `∂B_R(z)` landing in increasing order,
at least `S` apart, from the doubled corners and from the two points `6R`, `14R` of the line
(`6R + S ≤ L ≤ 14R - S`), ending in windows `[u i, u i + W]` in counterclockwise coordinates on
the sides `t i`, with `2G + 4W + 2 ≤ S`: there are lifted sides `lam i ∈ [1, 3]`
(`lam i + t i ≡ 2 (mod 4)`) such that the windows are in lexicographic order of `(lam, u)` along
the index with gaps `G`, at least `G` from the corners and, on the right and left sides, from the
line. -/
theorem exists_lift_of_separated_half {σ : Fin j → Bool} {R : ℕ}
    {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hrR : r < R)
    (ho : StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i))
    {S G W : ℤ} (hW : 0 ≤ W) (hG : 1 ≤ G) (hS : 2 * G + 4 * W + 2 ≤ S)
    (hsep : ∀ i k, i ≠ k → S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    (hcor : ∀ i (m' : ℕ), S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m' * R|)
    (hline : ∀ i, 6 * (R : ℤ) + S ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
      landingPos (z - R) (z + R) (σ i) (γ i) + S ≤ 14 * R)
    (t : Fin j → Fin 4) (u v : Fin j → ℤ) (hv : ∀ i, v i = u i + W)
    (hw : ∀ i, (t i = 0 ∧ b i 1 = z 1 + R ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
      (t i = 1 ∧ b i 0 = z 0 + R ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
      (t i = 2 ∧ b i 1 = z 1 - R - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧ b i 0 ≤ z 0 + v i) ∨
      (t i = 3 ∧ b i 0 = z 0 - R - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧ b i 1 ≤ z 1 - u i)) :
    ∃ lam : Fin j → ℤ, (∀ i, 1 ≤ lam i ∧ lam i ≤ 3) ∧
      (∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l)) ∧
      (∀ i, -(R : ℤ) + G ≤ u i ∧ v i + G ≤ R ∧ u i ≤ v i) ∧
      (∀ i, (lam i = 1 → G ≤ u i) ∧ (lam i = 3 → v i + G ≤ 0)) := by
  classical
  have h4 : 4 ≤ S := by omega
  choose c x hc0 hc3 hct hLx hx₁ hx₂ hx₃ hx₄ hL₁ hL₂ using fun i =>
    (hγ i).exists_landingPos_eq_of_window hrR h4 (hcor i) (hw i)
  have hR : (0 : ℤ) ≤ R := by positivity
  -- the side counted from the bottom side is at least one, and linear facts on each side
  have hcases : ∀ i, (c i = 1 ∧ landingPos (z - R) (z + R) (σ i) (γ i) = 4 * R + x i) ∨
      (c i = 2 ∧ landingPos (z - R) (z + R) (σ i) (γ i) = 8 * R + x i) ∨
      (c i = 3 ∧ landingPos (z - R) (z + R) (σ i) (γ i) = 12 * R + x i) := fun i => by
    have e := hLx i
    have := hline i
    have := hx₂ i
    have := hc0 i
    have := hc3 i
    rcases (show c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 by omega) with h | h | h | h <;>
      rw [h] at e
    · omega
    · exact Or.inl ⟨h, by rw [e]; ring⟩
    · exact Or.inr (Or.inl ⟨h, by rw [e]; ring⟩)
    · exact Or.inr (Or.inr ⟨h, by rw [e]; ring⟩)
  refine ⟨c, fun i => ?_, hct, fun i l hil => ?_, fun i => ?_, fun i => ?_⟩
  · rcases hcases i with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · have h₁ := ho hil
    have h₂ := le_abs.1 (hsep i l hil.ne)
    have := hx₁ i
    have := hx₂ i
    have := hx₁ l
    have := hx₂ l
    have := hx₃ i
    have := hx₄ i
    have := hx₃ l
    have := hx₄ l
    have := hv i
    have := hv l
    simp only at h₁
    rcases hcases i with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      rcases hcases l with ⟨f, f'⟩ | ⟨f, f'⟩ | ⟨f, f'⟩ <;> omega
  · have := hx₁ i
    have := hx₂ i
    have := hx₃ i
    have := hx₄ i
    have := hv i
    omega
  · have := hx₃ i
    have := hx₄ i
    have := hv i
    have := hline i
    rcases hcases i with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      exact ⟨fun h' => by omega, fun h' => by omega⟩

/-- **The separation from the line, read off windows.** An arm to `∂B_R(z)` ending in a window
`[α, β]` on the top side or on a half-side, at least `g ≥ 1` from the corners and, on a half-side,
at least `g` above the line, lands at least `2g - 1` from the two points `6R`, `14R` of the line. -/
theorem IsArm.line_le_of_window_half {col : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (hγ : IsArm ω col z r (z - R) (z + R) γ) (hrR : r < R)
    {t : Fin 4} {α β g : ℤ} (hg : 1 ≤ g)
    (hcor : (if t = 0 ∨ t = 2 then z 0 else z 1) - R + g ≤ α ∧
      β + g ≤ (if t = 0 ∨ t = 2 then z 0 else z 1) + R)
    (hline : t ≠ 0 → z 1 + g ≤ α) (ht : t ≠ 2)
    (hw : (t = 0 ∧ b 1 = z 1 + R ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
      (t = 1 ∧ b 0 = z 0 + R ∧ α ≤ b 1 ∧ b 1 ≤ β) ∨
      (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
      (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ α ≤ b 1 ∧ b 1 ≤ β)) :
    6 * (R : ℤ) + (2 * g - 1) ≤ landingPos (z - R) (z + R) col γ ∧
      landingPos (z - R) (z + R) col γ + (2 * g - 1) ≤ 14 * R := by
  have hc : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rcases hw with ⟨e, hb, h₁, h₂⟩ | ⟨e, hb, h₁, h₂⟩ | ⟨e, -⟩ | ⟨e, hb, h₁, h₂⟩
  · rw [hγ.landingPos_eq_of_top hrR hb]
    subst e
    simp only [true_or, ite_true] at hcor
    omega
  · rw [hγ.landingPos_eq_of_right hrR hb]
    subst e
    have := hline (by decide)
    simp only [show ¬((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) by decide, ite_false] at hcor
    omega
  · exact absurd e ht
  · rw [hγ.landingPos_eq_of_left hrR hb]
    subst e
    have := hline (by decide)
    simp only [show ¬((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 2) by decide, ite_false] at hcor
    omega

end Start

/-! ### The three phases of the plan -/

section Plan

variable {j : ℕ}

/-- **Rounds of turns in the half-plane** (phase 1 of the plan). Separated arms of the half-plane
ending in windows `[u i, v i]` (counterclockwise coordinates, width at most `W`) on the sides `t i`
of `B_{ρ 0}(z)`, with lifted sides `lam i ∈ [1, 3]` in lexicographic order with gaps `G` along the
index, at least `G` from the corners and from the line, are carried through `n₁` stages (radii
`ρ k`, growing by at least `G + M + W + 1`) to arms ending on the sides of their target lifted
sides `lamT i`, when at most `n₁` turns are needed in all (`Σ |lamT - lam| ≤ n₁`): the windows
stay in lexicographic order with gaps `G - 2 n₁ W`, as far from the corners and the line, and
widen to at most `(2 n₁ + 1) W`. The fences `(M, K)` are kept. The constant depends only on `σ`,
`c`, `A`, `N`, `n₁`. -/
theorem exists_pos_le_law_turns_half (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A N n₁ : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r W M K G : ℕ) (ρ : ℕ → ℕ)
      (J : Fin j → Set ℤ) (lamT lam u v : Fin j → ℤ) (t : Fin j → Fin 4),
      1 ≤ W → W ≤ K → W + K ≤ M → W + 2 * K ≤ A * (M - 1) → 2 * n₁ + 1 ≤ N →
      W + 2 * M + 2 * K + 3 + 2 * n₁ * W ≤ G → r + M + 1 < ρ 0 →
      (∀ k < n₁, ρ k + G + M + W + 1 ≤ ρ (k + 1) ∧ 2 * ρ (k + 1) + 2 ≤ A * W ∧
        (ρ (k + 1) : ℕ∞) ≤ L) →
      (∀ i, (lam i + ((t i : ℕ) : ℤ)) % 4 = 2) → (∀ i, 1 ≤ lam i ∧ lam i ≤ 3) →
      (∀ i l, i < l → lam i < lam l ∨ (lam i = lam l ∧ v i + G ≤ u l)) →
      (∀ i, -(ρ 0 : ℤ) + G ≤ u i ∧ v i + G ≤ ρ 0 ∧ u i ≤ v i ∧ v i - u i ≤ W) →
      (∀ i, (lam i = 1 → (G : ℤ) ≤ u i) ∧ (lam i = 3 → v i + G ≤ 0)) →
      (∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3) → (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      ∑ i, |lamT i - lam i| ≤ n₁ →
      ∃ (t' : Fin j → Fin 4) (u' v' : Fin j → ℤ),
        (∀ i, (lamT i + ((t' i : ℕ) : ℤ)) % 4 = 2) ∧
        (∀ i l, i < l → lamT i < lamT l ∨
          (lamT i = lamT l ∧ v' i + ((G : ℤ) - 2 * n₁ * W) ≤ u' l)) ∧
        (∀ i, -(ρ n₁ : ℤ) + ((G : ℤ) - 2 * n₁ * W) ≤ u' i ∧
          v' i + ((G : ℤ) - 2 * n₁ * W) ≤ ρ n₁ ∧ u' i ≤ v' i ∧
          v' i - u' i ≤ (2 * n₁ + 1) * W) ∧
        (∀ i, (lamT i = 1 → (G : ℤ) - 2 * n₁ * W ≤ u' i) ∧
          (lamT i = 3 → v' i + ((G : ℤ) - 2 * n₁ * W) ≤ 0)) ∧
        c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ 0)) (z + (ρ 0)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - (ρ 0)) (z + (ρ 0)) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z (ρ 0) ((2 * (G : ℤ) - 1 : ℤ) : ℝ) M K γ ∧
        (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + (ρ 0) ∧ z 0 - v i ≤ b i 0 ∧ b i 0 ≤ z 0 - u i) ∨
          (t i = 1 ∧ b i 0 = z 0 + (ρ 0) ∧ z 1 + u i ≤ b i 1 ∧ b i 1 ≤ z 1 + v i) ∨
          (t i = 2 ∧ b i 1 = z 1 - (ρ 0) - cond (σ i) 0 1 ∧ z 0 + u i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v i) ∨
          (t i = 3 ∧ b i 0 = z 0 - (ρ 0) - cond (σ i) 0 1 ∧ z 1 - v i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
          law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ n₁)) (z + (ρ n₁)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - (ρ n₁)) (z + (ρ n₁)) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z (ρ n₁) ((2 * ((G : ℤ) - 2 * n₁ * W) - 1 : ℤ) : ℝ) M K γ ∧
        (∀ i,
          (t' i = 0 ∧ b i 1 = z 1 + (ρ n₁) ∧ z 0 - v' i ≤ b i 0 ∧ b i 0 ≤ z 0 - u' i) ∨
          (t' i = 1 ∧ b i 0 = z 0 + (ρ n₁) ∧ z 1 + u' i ≤ b i 1 ∧ b i 1 ≤ z 1 + v' i) ∨
          (t' i = 2 ∧ b i 1 = z 1 - (ρ n₁) - cond (σ i) 0 1 ∧ z 0 + u' i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v' i) ∨
          (t' i = 3 ∧ b i 0 = z 0 - (ρ n₁) - cond (σ i) 0 1 ∧ z 1 - v' i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u' i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  obtain ⟨c₁, hc₁, hst⟩ := exists_pos_le_law_ccw_of_moves_half σ hσ c A N
  refine ⟨c₁ ^ n₁, ENNReal.pow_pos hc₁ n₁, ?_⟩
  intro q L hCB z r W M K G ρ J lamT lam u v t hW hWK hWKM hAM hN hG hr0 hρ hc hlam hL1 hL3 hL4
    hT1 hT2 hpot
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
    (u := fun kk (x : (Fin j → ℤ) × (Fin j → Fin 4) × (Fin j → ℤ) × (Fin j → ℤ)) =>
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ kk)) (z + (ρ kk)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - (ρ kk)) (z + (ρ kk)) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z (ρ kk) ((2 * ((G : ℤ) - 2 * (kk : ℤ) * W) - 1 : ℤ) : ℝ) M K γ ∧
        (∀ i,
          (x.2.1 i = 0 ∧ b i 1 = z 1 + (ρ kk) ∧ z 0 - x.2.2.2 i ≤ b i 0 ∧ b i 0 ≤ z 0 - x.2.2.1 i) ∨
          (x.2.1 i = 1 ∧ b i 0 = z 0 + (ρ kk) ∧ z 1 + x.2.2.1 i ≤ b i 1 ∧ b i 1 ≤ z 1 + x.2.2.2 i) ∨
          (x.2.1 i = 2 ∧ b i 1 = z 1 - (ρ kk) - cond (σ i) 0 1 ∧ z 0 + x.2.2.1 i ≤ b i 0 ∧
            b i 0 ≤ z 0 + x.2.2.2 i) ∨
          (x.2.1 i = 3 ∧ b i 0 = z 0 - (ρ kk) - cond (σ i) 0 1 ∧ z 1 - x.2.2.2 i ≤ b i 1 ∧
            b i 1 ≤ z 1 - x.2.2.1 i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i})
    (I := fun kk x => (∀ i, (x.1 i + ((x.2.1 i : ℕ) : ℤ)) % 4 = 2) ∧
      (∀ i, 1 ≤ x.1 i ∧ x.1 i ≤ 3) ∧
      (∀ i l, i < l → x.1 i < x.1 l ∨
        (x.1 i = x.1 l ∧ x.2.2.2 i + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ x.2.2.1 l)) ∧
      (∀ i, -(ρ kk : ℤ) + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ x.2.2.1 i ∧
        x.2.2.2 i + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ ρ kk ∧ x.2.2.1 i ≤ x.2.2.2 i ∧
        x.2.2.2 i - x.2.2.1 i ≤ (2 * (kk : ℤ) + 1) * W) ∧
      (∀ i, (x.1 i = 1 → (G : ℤ) - 2 * (kk : ℤ) * W ≤ x.2.2.1 i) ∧
        (x.1 i = 3 → x.2.2.2 i + ((G : ℤ) - 2 * (kk : ℤ) * W) ≤ 0)) ∧
      (∑ i, |lamT i - x.1 i| + kk ≤ n₁ ∨ ∑ i, |lamT i - x.1 i| = 0))
    n₁ (by
      -- one round of turns
      rintro k hk ⟨lam₀, t₀, u₀, v₀⟩ ⟨hc₀, hlam₀, hL1₀, hL3₀, hL4₀, hpot₀⟩
      simp only at hc₀ hlam₀ hL1₀ hL3₀ hL4₀ hpot₀
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
      rw [← hGk] at hL1₀ hL3₀ hL4₀
      obtain ⟨hρ₁, hρ₂, hρ₃⟩ := hρ k hk
      have hρk := hρmono k hk.le
      obtain ⟨τ, lam', t', u', v', hccw, hcw, hcorner, hmv, hc', hlam', hL1', hL3', hL4', hsum,
          hsum'⟩ :=
        exists_turn_step_half (ρ := (ρ k : ℤ)) (ρ' := (ρ (k + 1) : ℤ)) (h := (ρ k : ℤ) + M + 1)
          (lamT := lamT) (W := (W : ℤ)) (G := Gk) (by positivity) (by omega) hc₀ hlam₀ hL1₀
          (fun i => ⟨(hL3₀ i).1, (hL3₀ i).2.1, (hL3₀ i).2.2.1⟩) hL4₀ hT1 hT2 (by omega)
          (by omega) (by exact_mod_cast (show ρ k ≤ ρ (k + 1) by omega))
      refine ⟨(lam', t', u', v'), ⟨hc', hlam', fun i l hil => ?_, fun i => ?_, fun i => ?_, ?_⟩,
        ?_⟩
      · rw [hGk1]
        exact hL1' i l hil
      · dsimp only
        rw [hGk1, hwk1]
        have := hL3' i
        have := hL3₀ i
        rcases hmv i with ⟨-, -, -, h₁, h₂⟩ | ⟨-, -, -, h₁, h₂⟩ | ⟨-, -, -, h₁, h₂⟩ <;> omega
      · dsimp only
        rw [hGk1]
        exact hL4' i
      · dsimp only
        have : 0 ≤ ∑ i, |lamT i - lam' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        have h0 : 0 ≤ ∑ i, |lamT i - lam₀ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
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
          (fun i => by
            rcases side_of_lift_half (hc₀ i) (hlam₀ i) with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;>
              rw [e] <;> decide)
          (fun i => by have := hL3₀ i; omega)
          (fun i => by
            have h₁ := hL4₀ i
            rcases side_of_lift_half (hc₀ i) (hlam₀ i) with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩
            · rw [e']
              exact ⟨fun _ => by have := h₁.1 e; omega, fun h => absurd h (by decide)⟩
            · rw [e']
              exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
            · rw [e']
              exact ⟨fun h => absurd h (by decide), fun _ => by have := h₁.2 e; omega⟩)
          (fun i l hil htl => by
            have := gap_of_lex_half hc₀ hlam₀ hL1₀ i l hil htl
            omega)
          (fun i l hil hτ htl => by have := hccw i l hil hτ htl; omega)
          (fun i l hil hτ htl => by have := hcw i l hil hτ htl; omega)
          hcorner
          (fun i => by
            rcases hmv i with ⟨h₁, h₂, -, h₃, h₄⟩ | ⟨h₁, h₂, -, h₃, h₄⟩ | ⟨h₁, h₂, -, h₃, h₄⟩
            · exact Or.inl ⟨h₁, h₂, by omega, by omega⟩
            · exact Or.inr (Or.inl ⟨h₁, h₂, by omega, by omega⟩)
            · exact Or.inr (Or.inr ⟨h₁, h₂, by omega, by omega⟩))
          (by rw [hGk1]; omega)
          (fun i => by rw [hGk1]; have := hL3' i; omega)
          (fun i l hil htl => by
            rw [hGk1]
            exact gap_of_lex_half hc' hlam' hL1' i l hil htl)
        exact key)
    (lam, t, u, v) (by
      refine ⟨hc, hlam, fun i l hil => ?_, fun i => ?_, fun i => ?_, Or.inl (by simpa using hpot)⟩
      · simpa using hL1 i l hil
      · have := hL3 i
        push_cast
        omega
      · simpa using hL4 i)
  -- phase 1 at the end: no turns left
  obtain ⟨hxc, -, hx1, hx3, hx4, hxpot⟩ := hx
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ |lamT i - x.1 i| := fun i _ => abs_nonneg _
  have hsum0 : ∑ i, |lamT i - x.1 i| = 0 := by
    have := Finset.sum_nonneg hnn
    rcases hxpot with h | h <;> omega
  have hxlam : ∀ i, x.1 i = lamT i := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 i (Finset.mem_univ _)
    rw [abs_eq_zero] at this
    omega
  refine ⟨x.2.1, x.2.2.1, x.2.2.2, fun i => by rw [← hxlam]; exact hxc i,
    fun i l hil => by rw [← hxlam, ← hxlam]; exact hx1 i l hil, fun i => hx3 i,
    fun i => by rw [← hxlam]; exact hx4 i, ?_⟩
  have e0 : ((2 * ((G : ℤ) - 2 * ((0 : ℕ) : ℤ) * W) - 1 : ℤ) : ℝ) =
      ((2 * (G : ℤ) - 1 : ℤ) : ℝ) := by push_cast; ring
  simp only [e0] at hle
  exact hle

/-- **Linear spreading along the sides, in the half-plane** (phase 2 of the plan). Separated arms
of the half-plane ending in windows `[u i, v i]` (counterclockwise coordinates, width at most `w`)
on the sides `t i ≠ 2` of `B_{ρ₀}(z)`, at least `S` from the corners, from the line and in order on
each side with gaps `S`, are moved in `n` stages (radius growing by `Δ` per stage), each arm by the
same amount at every stage, into windows `[u' i, v' i] ⊆ [uT i, uT i + n + w + 2nW]` at
`B_{ρ₀ + nΔ}(z)`; the targets are at least `S` from the corners and the line and in the same order
with gaps `S` beyond their widths. The fences `(M, K)` are kept. The constant depends only on `σ`,
`c`, `A`, `N`, `n`. -/
theorem exists_pos_le_law_spread_half (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A N n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r W M K D S ρ₀ Δ w : ℕ)
      (J : Fin j → Set ℤ) (t : Fin j → Fin 4) (u v uT : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → W + 2 * K ≤ A * (M - 1) →
      W + 2 * D + 2 * M + 2 * K + 3 ≤ S → r + M + 1 < ρ₀ →
      2 * M + W + 1 ≤ Δ → 2 * (ρ₀ + n * Δ) + 2 ≤ A * W → ((ρ₀ + n * Δ : ℕ) : ℕ∞) ≤ L →
      2 * (ρ₀ + n * Δ) + 2 * n + n * W ≤ n * D → w + 2 * n * W + 1 ≤ N * (W + 1) →
      (∀ i, t i ≠ 2) →
      (∀ i, -(ρ₀ : ℤ) + S ≤ u i ∧ v i + S ≤ ρ₀ ∧ u i ≤ v i ∧ v i - u i ≤ w) →
      (∀ i, (t i = 1 → (S : ℤ) ≤ u i) ∧ (t i = 3 → v i + S ≤ 0)) →
      (∀ i l, i < l → t i = t l → v i + S ≤ u l) →
      (∀ i, -((ρ₀ + n * Δ : ℕ) : ℤ) + S ≤ uT i ∧
        uT i + n + w + 2 * n * W + S ≤ ((ρ₀ + n * Δ : ℕ) : ℤ)) →
      (∀ i, (t i = 1 → (S : ℤ) ≤ uT i) ∧ (t i = 3 → uT i + n + w + 2 * n * W + S ≤ 0)) →
      (∀ i l, i < l → t i = t l → uT i + n + w + 2 * n * W + S ≤ uT l) →
      ∃ u' v' : Fin j → ℤ, (∀ i, uT i ≤ u' i ∧ v' i ≤ uT i + n + w + 2 * n * W) ∧
        c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - ρ₀) (z + ρ₀) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - ρ₀) (z + ρ₀) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z ρ₀ ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧
        (∀ i,
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
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - (ρ₀ + n * Δ : ℕ)) (z + (ρ₀ + n * Δ : ℕ)) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z (ρ₀ + n * Δ : ℕ) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧
        (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + (ρ₀ + n * Δ : ℕ) ∧ z 0 - v' i ≤ b i 0 ∧ b i 0 ≤ z 0 - u' i) ∨
          (t i = 1 ∧ b i 0 = z 0 + (ρ₀ + n * Δ : ℕ) ∧ z 1 + u' i ≤ b i 1 ∧ b i 1 ≤ z 1 + v' i) ∨
          (t i = 2 ∧ b i 1 = z 1 - (ρ₀ + n * Δ : ℕ) - cond (σ i) 0 1 ∧ z 0 + u' i ≤ b i 0 ∧
            b i 0 ≤ z 0 + v' i) ∨
          (t i = 3 ∧ b i 0 = z 0 - (ρ₀ + n * Δ : ℕ) - cond (σ i) 0 1 ∧ z 1 - v' i ≤ b i 1 ∧
            b i 1 ≤ z 1 - u' i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  obtain ⟨c₁, hc₁, hst⟩ := exists_pos_le_law_ccw_of_moves_half σ hσ c A N
  refine ⟨c₁ ^ n, ENNReal.pow_pos hc₁ n, ?_⟩
  intro q L hCB z r W M K D S ρ₀ Δ w J t u v uT hW hWK hWKM hAM hS hr0 hΔ hAW hL hjog hN ht hwin
    hline hgap hTcor hTline hTgap
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
  -- the windows of every stage are at least `S` from the corners, the line and apart
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
  have hlinek : ∀ k ≤ n, ∀ i, (t i = 1 → (S : ℤ) ≤ u i + k * e i - k * W) ∧
      (t i = 3 → v i + k * e i + k * W + S ≤ 0) := by
    intro k hk i
    have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
    have h₁ := he₁ i
    have h₂ := he₂ i
    have h₃ := hwin i
    obtain ⟨hl₁, hl₃⟩ := hline i
    obtain ⟨hT₁, hT₃⟩ := hTline i
    refine ⟨fun ht1 => ?_, fun ht3 => ?_⟩
    · have a₁ := hl₁ ht1
      have a₂ := hT₁ ht1
      have := le_add_mul_of_le_of_le (g := 0) (a := u i - S) (b := e i - W) (k := k) (n := n)
        (by linarith) (by linarith) (by positivity) hk'
      linarith
    · have a₁ := hl₃ ht3
      have a₂ := hT₃ ht3
      have := le_add_mul_of_le_of_le (g := 0) (a := -v i - S) (b := -e i - W) (k := k) (n := n)
        (by linarith) (by linarith) (by positivity) hk'
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
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - (ρ₀ + kk * Δ : ℕ)) (z + (ρ₀ + kk * Δ : ℕ)) (σ i) (γ
            i)) ∧
        ArmsOuterSeparated ω σ z (ρ₀ + kk * Δ : ℕ) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧
        (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + (ρ₀ + kk * Δ : ℕ) ∧ z 0 - x.2 i ≤ b i 0 ∧ b i 0 ≤ z 0 - x.1 i) ∨
          (t i = 1 ∧ b i 0 = z 0 + (ρ₀ + kk * Δ : ℕ) ∧ z 1 + x.1 i ≤ b i 1 ∧ b i 1 ≤ z 1 + x.2 i) ∨
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
        (((ρ₀ + k * Δ : ℕ) : ℤ) + M + 1) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) S J t t (fun _ => 0)
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
        ht (fun i => by have := hcor k hk.le i; have := hI i; omega)
        (fun i => by
          obtain ⟨h₁, h₃⟩ := hlinek k hk.le i
          have := hI i
          exact ⟨fun e₁ => by have := h₁ e₁; omega, fun e₃ => by have := h₃ e₃; omega⟩)
        (fun i l hil htl => by
          have := hI i
          have := hI l
          rcases lt_or_gt_of_ne hil with h | h
          · have := hgapk k hk.le i l h htl; omega
          · have := hgapk k hk.le l i h htl.symm; omega)
        (fun i l _ hτ _ => absurd hτ (by decide))
        (fun i l _ hτ _ => absurd hτ (by decide))
        (fun i l hτ _ => absurd hτ (by decide))
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

/-- **The last stage in the half-plane: new fences in the target windows.** Separated arms of the
half-plane with fences `(M, K)` ending in windows `[u i, v i]` (counterclockwise coordinates) on
the sides `t i ≠ 2` of `B_{R' - (M + M' + W + 1)}(z)`, inside the target windows
`[uT i + W, vT i - W]`, are carried straight out to `∂B_{R'}(z)`, ending in the target windows with
fences `(M', K')`, separated at scale `2Q - 1`; the targets are at least `Q + M + M' + W + 1` from
the corners, at least `Q` from the line and in order on each side with gaps `Q`. The constant
depends only on `σ`, `c`, `A`, `N`. -/
theorem exists_pos_le_law_fences_of_windows_half (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R' W M K M' K' Q : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (t : Fin j → Fin 4) (u v uT vT : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2 * M + 2 * K' + 3 ≤ Q →
      4 * (M : ℝ) ≤ s → r + M + 1 < R' - (M + M' + W + 1) → 2 * R' + 2 ≤ A * W →
      W + 2 * K' ≤ A * (M' - 1) → (R' : ℕ∞) ≤ L →
      (∀ i, v i - u i + 1 ≤ N * ((W : ℤ) + 1)) → (∀ i, uT i + W ≤ u i ∧ v i + W ≤ vT i) →
      (∀ i, -(R' : ℤ) + (Q + M + M' + W + 1) ≤ uT i ∧ vT i + (Q + M + M' + W + 1) ≤ R') →
      (∀ i, t i ≠ 2) → (∀ i, (t i = 1 → (Q : ℤ) ≤ uT i) ∧ (t i = 3 → vT i + Q ≤ 0)) →
      (∀ i l, i < l → t i = t l → vT i + Q ≤ uT l) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (R' - (M + M' + W + 1) : ℕ)) (z + (R' - (M + M' + W + 1) : ℕ))
            (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - (R' - (M + M' + W + 1) : ℕ)) (z + (R' - (M + M' + W +
            1) : ℕ)) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z (R' - (M + M' + W + 1) : ℕ) s M K γ ∧
        (∀ i,
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
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧
        (∀ i,
          (t i = 0 ∧ b i 1 = z 1 + R' ∧ z 0 - vT i ≤ b i 0 ∧ b i 0 ≤ z 0 - uT i) ∨
          (t i = 1 ∧ b i 0 = z 0 + R' ∧ z 1 + uT i ≤ b i 1 ∧ b i 1 ≤ z 1 + vT i) ∨
          (t i = 2 ∧ b i 1 = z 1 - R' - cond (σ i) 0 1 ∧ z 0 + uT i ≤ b i 0 ∧
            b i 0 ≤ z 0 + vT i) ∨
          (t i = 3 ∧ b i 0 = z 0 - R' - cond (σ i) 0 1 ∧ z 1 - vT i ≤ b i 1 ∧
            b i 1 ≤ z 1 - uT i)) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₃, hc₃, hP3⟩ := exists_pos_le_law_ccw_of_moves_half σ hσ c A N
  refine ⟨c₃, hc₃, ?_⟩
  intro q L hCB z r R' W M K M' K' Q s J t u v uT vT hW hWK hKM hM' hWKM' hQ hs hrM hAW hAM' hL hN
    hin hTcor ht hTline hTgap
  have hgapT : ∀ i l, i ≠ l → t i = t l → vT i + Q ≤ uT l ∨ vT l + Q ≤ uT i := by
    intro i l hil htl
    rcases lt_or_gt_of_ne hil with h | h
    · exact Or.inl (hTgap i l h htl)
    · exact Or.inr (hTgap l i h htl.symm)
  refine hP3 q L hCB z r (R' - (M + M' + W + 1)) R' W M K M' K' 0 Q
    (((R' - (M + M' + W + 1) : ℕ) : ℤ) + M + 1) s Q J t t (fun _ => 0) u v (fun _ => 0) uT vT
    hW hWK hKM hM' hWKM' (by omega) hs hrM le_rfl (by omega) hAW hAM' hL (fun _ => by simp) hN
    ht (fun i => by have := hin i; have := hTcor i; omega)
    (fun i => by
      have := hin i
      obtain ⟨h₁, h₃⟩ := hTline i
      exact ⟨fun e₁ => by have := h₁ e₁; omega, fun e₃ => by have := h₃ e₃; omega⟩)
    (fun i l hil htl => by
      have := hin i
      have := hin l
      rcases hgapT i l hil htl with h | h <;> omega)
    (fun i l _ hτ _ => absurd hτ (by decide))
    (fun i l _ hτ _ => absurd hτ (by decide))
    (fun i l hτ _ => absurd hτ (by decide))
    (fun i => Or.inl ⟨rfl, rfl, by have := hin i; omega, by have := hin i; omega⟩)
    (by omega) (fun i => by have := hTcor i; omega) hgapT

end Plan

/-! ### The motion plan in the half-plane -/

section Targets

variable {j : ℕ}

/-- **The motion plan in the half-plane for arms ending in given bins**
(`exists_pos_le_law_half_target_windows` for the separated arms ending in bins `[αs i, αs i + W]`
on the sides `ts i` of `B_R(z)`). -/
theorem exists_pos_le_law_half_target_windows_of_bins (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A n n₁ : ℕ)
    (hn₁ : 2 * j ≤ n₁) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S G Q B : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ)
      (ts : Fin j → Fin 4) (αs : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → 2 ≤ M' → W + K' ≤ M' →
      W + 2 * K ≤ A * (M - 1) → W + 2 * K' ≤ A * (M' - 1) →
      W + 2 * D + 2 * M + 2 * K + 3 ≤ S → S + 2 * n₁ * W ≤ G →
      W + 2 * M + 2 * K' + 3 ≤ Q → ((2 * G + 4 * W + 2 : ℕ) : ℝ) ≤ s → r + M + 1 < R →
      R + n₁ * (G + M + W + 1) + n * (2 * M + W + 1) + (M + M' + W + 1) ≤ R' →
      2 * R' + 2 ≤ A * W → (R' : ℕ∞) ≤ L → 2 * R' + 2 * n + n * W ≤ n * D →
      n + (2 * n₁ + 2 * n + 3) * W ≤ B →
      (∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R' + (S + Q + M + M' + W + 1) ≤ αT i ∧
        βT i + (S + Q + M + M' + W + 1) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R') →
      (∀ i, tT i ≠ 0 → z 1 + (S + Q + M + M' + W + 1) ≤ αT i) →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + S + Q ≤ αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + S + Q ≤ αT i)) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        (∀ i, b i ∈ {b : LatticeSite 2 |
          (ts i = 0 ∧ b 1 = z 1 + R ∧ αs i ≤ b 0 ∧ b 0 ≤ αs i + W) ∨
          (ts i = 1 ∧ b 0 = z 0 + R ∧ αs i ≤ b 1 ∧ b 1 ≤ αs i + W) ∨
          (ts i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ αs i ≤ b 0 ∧ b 0 ≤ αs i + W) ∨
          (ts i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ αs i ≤ b 1 ∧ b 1 ≤ αs i + W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧
        (∀ i, 6 * (R' : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ landingPos (z - R') (z + R') (σ i) (γ i)
            ∧
          (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ 14 * R') ∧
        (∀ i, b i ∈ {b : LatticeSite 2 |
          (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
          (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    refine ⟨1, one_pos, ?_⟩
    intro q L _ z r R R' W M K M' K' D S G Q B s J tT lamT αT βT ts αs
    intros
    rw [one_mul]
    refine measure_mono ?_
    rintro ω ⟨a, b, γ, -, hd, -, -, -, -, -, hJ⟩
    exact ⟨a, b, γ, fun i => i.elim0, hd, fun i => i.elim0, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0,
      hJ⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * n₁ + 2 * n + 1 := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁, hP1⟩ := exists_pos_le_law_turns_half σ hσ c A N n₁
  obtain ⟨c₂, hc₂, hP2⟩ := exists_pos_le_law_spread_half σ hσ c A N n
  obtain ⟨c₃, hc₃, hP3⟩ := exists_pos_le_law_fences_of_windows_half σ hσ c A N
  refine ⟨c₁ * c₂ * c₃, ENNReal.mul_pos (mul_ne_zero hc₁.ne' hc₂.ne') hc₃.ne', ?_⟩
  intro q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT ts αs hW hWK hWKM hM' hWKM' hAM
    hAM' hS hG hQ hs hrM hRR' hAW hL hjog hB hlamT hlamT2 hTcor hTline hTwid hTord
  have hrR : r < R := by omega
  have hs' : ((2 * (G : ℤ) + 4 * W + 2 : ℤ) : ℝ) ≤ s := by push_cast at hs ⊢; linarith
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
  have htT : ∀ i, tT i ≠ 2 := fun i => by
    rcases side_of_lift_half (hlamT i).2.2 ⟨(hlamT i).1, (hlamT i).2.1⟩ with
      ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> decide
  -- the plan for the arms ending in given bins
  refine mul_measure_le_of_nonempty fun ⟨ω₀, hω₀⟩ => ?_
  obtain ⟨a₀, b₀, γ₀, hγ₀, -, -, ho₀, hsep₀, hline₀, hw₀, -⟩ := hω₀
  choose us vs hrels hmems using fun i => exists_ccw_window (ts i) z (αs i) (αs i + W)
  have hvs : ∀ i, vs i = us i + W := fun i => by
    rcases hrels i with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩ <;> omega
  have hsepZ := hsep₀.le_abs_landingPos_sub hs'
  have hlineZ : ∀ i, 6 * (R : ℤ) + (2 * (G : ℤ) + 4 * W + 2) ≤
      landingPos (z - R) (z + R) (σ i) (γ₀ i) ∧
      landingPos (z - R) (z + R) (σ i) (γ₀ i) + (2 * (G : ℤ) + 4 * W + 2) ≤ 14 * R := fun i => by
    have h₁ := hline₀ i
    constructor
    · have : ((6 * (R : ℤ) + (2 * (G : ℤ) + 4 * W + 2) : ℤ) : ℝ) ≤
          (landingPos (z - R) (z + R) (σ i) (γ₀ i) : ℝ) := by
        push_cast at hs' ⊢
        linarith [h₁.1]
      exact_mod_cast this
    · have : ((landingPos (z - R) (z + R) (σ i) (γ₀ i) + (2 * (G : ℤ) + 4 * W + 2) : ℤ) : ℝ) ≤
          ((14 * (R : ℤ) : ℤ) : ℝ) := by
        push_cast at hs' ⊢
        linarith [h₁.2]
      exact_mod_cast this
  obtain ⟨lam, hlam, hc, hL1, hL3, hL4⟩ := exists_lift_of_separated_half hγ₀ hrR ho₀ (G := G)
    (W := W) (by positivity) (by omega) le_rfl hsepZ.1 hsepZ.2 hlineZ ts us vs hvs
    (fun i => (hmems i R (σ i) (b₀ i)).1 (hw₀ i))
  -- phase 1: rounds of turns
  have hpot : ∑ i, |lamT i - lam i| ≤ n₁ := by
    have h₁ : ∑ i, |lamT i - lam i| ≤ ∑ _i : Fin j, (2 : ℤ) :=
      Finset.sum_le_sum fun i _ => by
        have := hlam i
        have := hlamT i
        rw [abs_le]
        constructor <;> omega
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁
    have : (2 * j : ℤ) ≤ n₁ := by exact_mod_cast hn₁
    linarith
  obtain ⟨t₁, u₁, v₁, hc₁', hL1₁, hL3₁, hL4₁, hineq₁⟩ := hP1 q L hCB z r W M K G ρ₁ J
    lamT lam us vs ts hW hWK hWKM hAM (by omega) (by omega)
    (by rw [hρ₁0]; omega) hρ₁step hc hlam hL1
    (fun i => by rw [hρ₁0]; have := hL3 i; have := hvs i; omega) hL4
    (fun i => ⟨(hlamT i).1, (hlamT i).2.1⟩) hlamT2 hpot
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
  have hG' : (S : ℤ) + 2 * (n₁ : ℤ) * W ≤ G := by exact_mod_cast hG
  have hBZ : (n : ℤ) + (((2 * n₁ + 1) * W : ℕ) : ℤ) + 2 * n * W + 2 * W ≤ B := by
    have e : n + (2 * n₁ + 2 * n + 3) * W = n + (2 * n₁ + 1) * W + 2 * n * W + 2 * W := by ring
    have h' := hB
    rw [e] at h'
    exact_mod_cast h'
  obtain ⟨u₂, v₂, hfin, hineq₂⟩ := hP2 q L hCB z r W M K D S (R' - E - n * Δ₂) Δ₂
    ((2 * n₁ + 1) * W) J tT u₁ v₁ (fun i => uT i + W) hW hWK hWKM hAM hS (by omega)
    (by omega) (by rw [Nat.sub_add_cancel hnR']; omega)
    (by rw [Nat.sub_add_cancel hnR']; exact le_trans (by exact_mod_cast (show R' - E ≤ R' by
      omega)) hL)
    (by rw [Nat.sub_add_cancel hnR']; omega) hNW htT
    (fun i => by
      have := hL3₁ i
      push_cast
      omega)
    (fun i => by
      have h₁ := hL4₁ i
      have h₂ := (hlamT i).2.2
      have h₃ := hlamT i
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := h₁.1 (by omega)
        omega
      · have := h₁.2 (by omega)
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
    (fun i => by
      have h₁ := hTwid i
      have h₂ := hTline i
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := h₂ (by rw [e]; decide)
        rcases hrelT i with ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ <;> omega
      · have := h₂ (by rw [e]; decide)
        rcases hrelT i with ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ <;> omega)
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
    htT
    (fun i => by
      have h₂ := hTline i
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := h₂ (by rw [e]; decide)
        rcases hrelT i with ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ <;> omega
      · have := h₂ (by rw [e]; decide)
        rcases hrelT i with ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ | ⟨h0, hα, hβ⟩ <;> omega)
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
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, -, h₆, h₇⟩
    refine ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅.mono ?_ le_rfl, fun i => (hmems i R (σ i) (b i)).1 (h₆ i),
      h₇⟩
    refine le_trans ?_ hs'
    push_cast
    linarith
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    refine ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅.mono ?_ le_rfl, fun i => by rw [← ht₁ i]; exact h₆ i, h₇⟩
    have : (2 * (S : ℤ) - 1 : ℤ) ≤ 2 * ((G : ℤ) - 2 * n₁ * W) - 1 := by omega
    exact_mod_cast this
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    refine ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, fun i => ?_, fun i => (hmemT i R' (σ i) (b i)).2 (h₆ i),
      h₇⟩
    have hl := (h₁ i).line_le_of_window_half (by omega : r < R') (g := (Q : ℤ)) (by omega)
      ⟨by have := hTcor i; omega, by have := hTcor i; omega⟩
      (fun h => by have := hTline i h; omega) (htT i) ((hmemT i R' (σ i) (b i)).2 (h₆ i))
    constructor
    · have : ((6 * (R' : ℤ) + (2 * (Q : ℤ) - 1) : ℤ) : ℝ) ≤
          (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) := by exact_mod_cast hl.1
      push_cast at this ⊢
      linarith
    · have : ((landingPos (z - R') (z + R') (σ i) (γ i) + (2 * (Q : ℤ) - 1) : ℤ) : ℝ) ≤
          ((14 * (R' : ℤ) : ℤ) : ℝ) := by exact_mod_cast hl.2
      push_cast at this ⊢
      linarith

/-- **The motion plan in the half-plane: separated arms carried into prescribed windows** (the
window step of Theorem 11 for the arms of the half-plane). For a colour sequence `σ` without two
consecutive arms of one colour, ratios `A`, `n` and a number of rounds `n₁ ≥ 2j`, there is
`c₀ > 0` such that for every law with crossing bounds `c` up to scale `L`: separated arms of the
half-plane at the outer boundary of `B_R(z)` (landing in increasing order, separation
`s ≥ 2G + 4W + 2` from each other, the corners and the two points of the line, fences `(M, K)`,
inner positions in `J`) are carried to arms of the half-plane to `∂B_{R'}(z)` ending in the
prescribed windows `[αT i, βT i]` on the sides `tT i` (`0` top, `1` right, `3` left; coordinates
along the side), separated at scale `2Q - 1` from each other, the corners and the line, with fences
`(M', K')`: `c₀ P(separated at R) ≤ P(separated at R', ends in the windows)`.

The windows are in the order of the arms: `lamT i ∈ [1, 3]` (the side counted from the right
side, `lamT i + tT i ≡ 2 (mod 4)`) is nondecreasing, windows on one side are in counterclockwise
order with gaps `S + Q`, at least `S + Q + M + M' + W + 1` from the corners of `B_{R'}(z)` and,
on the right and left sides, from the line, of length at least `B`. The plan makes `n₁` rounds of
turns at the two upper corners (radius growing by `G + M + W + 1` per round; every arm needs at most
two turns), then `n` stages of linear spreading (radius growing by `2M + W + 1`), and a last stage
from `R' - (M + M' + W + 1)` to `R'` that changes the fences. The hypotheses are those of
`exists_pos_le_law_target_windows` with `12 j` replaced by `n₁`, plus the margins from the line.
The constant depends only on `σ`, `c`, `A`, `n`, `n₁`. -/
theorem exists_pos_le_law_half_target_windows (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A n n₁ : ℕ)
    (hn₁ : 2 * j ≤ n₁) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S G Q B : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → 2 ≤ M' → W + K' ≤ M' →
      W + 2 * K ≤ A * (M - 1) → W + 2 * K' ≤ A * (M' - 1) →
      W + 2 * D + 2 * M + 2 * K + 3 ≤ S → S + 2 * n₁ * W ≤ G →
      W + 2 * M + 2 * K' + 3 ≤ Q → ((2 * G + 4 * W + 2 : ℕ) : ℝ) ≤ s → r + M + 1 < R →
      R + n₁ * (G + M + W + 1) + n * (2 * M + W + 1) + (M + M' + W + 1) ≤ R' →
      2 * R' + 2 ≤ A * W → (R' : ℕ∞) ≤ L → 2 * R' + 2 * n + n * W ≤ n * D →
      n + (2 * n₁ + 2 * n + 3) * W ≤ B →
      (∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R' + (S + Q + M + M' + W + 1) ≤ αT i ∧
        βT i + (S + Q + M + M' + W + 1) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R') →
      (∀ i, tT i ≠ 0 → z 1 + (S + Q + M + M' + W + 1) ≤ αT i) →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + S + Q ≤ αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + S + Q ≤ αT i)) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧
        (∀ i, 6 * (R' : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ landingPos (z - R') (z + R') (σ i) (γ i)
            ∧
          (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ 14 * R') ∧
        (∀ i, b i ∈ {b : LatticeSite 2 |
          (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
          (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  obtain ⟨c₀, hc₀, hbins⟩ := exists_pos_le_law_half_target_windows_of_bins σ hσ c A n n₁ hn₁
  obtain ⟨X, hX⟩ : ∃ X : ℝ≥0∞, X = (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) := ⟨_, rfl⟩
  have hX0 : X ≠ 0 := by rw [hX, Nat.cast_ne_zero]; positivity
  have hXt : X ≠ ⊤ := by rw [hX]; exact ENNReal.natCast_ne_top _
  refine ⟨c₀ / X, ENNReal.div_pos hc₀.ne' hXt, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT hW hWK hWKM hM' hWKM' hAM
    hAM' hS hG hQ hs hrM hRR' hAW hL hjog hB hlamT hlamT2 hTcor hTline hTwid hTord
  have hrR : r < R := by omega
  have hRA : R ≤ A * W := by omega
  have hs4 : 4 * (M : ℝ) ≤ s := by
    refine le_trans ?_ hs
    have : 4 * M ≤ 2 * G + 4 * W + 2 := by omega
    exact_mod_cast this
  refine (mul_le_mul' le_rfl (law_le_sum_law_windows_of_separated_half q (σ := σ) (z := z)
    (K := K) hrR (by omega : 1 ≤ M) hW hRA hs4 J)).trans ?_
  rw [Finset.mul_sum]
  calc ∑ p : Fin j → Fin 4 × Fin (2 * A + 1), c₀ / X * law q _
      ≤ ∑ _p : Fin j → Fin 4 × Fin (2 * A + 1), X⁻¹ * law q {ω : Config (LatticeSite 2) | ∃ (a b :
          Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
          (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
          ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧
          (∀ i, 6 * (R' : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ landingPos (z - R') (z + R') (σ i) (γ
              i) ∧
            (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ 14 * R')
                ∧
          (∀ i, b i ∈ {b : LatticeSite 2 |
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
          hAW hL hjog hB hlamT hlamT2 hTcor hTline hTwid hTord)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        rw [← mul_assoc, ← hX, ENNReal.mul_inv_cancel hX0 hXt, one_mul]

/-- **The first gluing into prescribed windows in the half-plane** (the gluing step of Theorem 11
for the arms of the half-plane). For a colour sequence `σ` without two consecutive arms of one
colour, ratios `A`, `n` and a number of rounds `n₁ ≥ 2j`, there is `c₀ > 0` such that for every law
with crossing bounds `c` up to scale `L`: separated arms of the half-plane at the outer boundary of
`B_R(z)` with separation `s ≥ 4M` from each other, the corners and the line, and fences `(M, K)`
(the form produced by the half-plane outer separation step, `exists_half_separating_event`) are
carried to arms of the half-plane to `∂B_{R'}(z)` ending in prescribed windows, separated at scale
`2Q - 1` from each other, the corners and the line, with fences `(M', K')`. A straight first gluing
(`exists_pos_le_law_separated_of_separated_half`, corridors of width `4W`, new fences `(4W, W)` at
`R + M + 1 + 8W`, ratios `A` and `A + 4`) makes room; the motion plan
(`exists_pos_le_law_half_target_windows`, with the fences `(4W, W)`) does the rest. Hypotheses as
in `exists_pos_le_law_target_windows_of_separated` with `12 j` replaced by `n₁`, plus `4M ≤ R` and
the margins of the targets from the line. The constant depends only on `σ`, `c`, `A`, `n`, `n₁`. -/
theorem exists_pos_le_law_half_target_windows_of_separated (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A n n₁ : ℕ)
    (hn₁ : 2 * j ≤ n₁) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S G Q B : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ) (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      1 ≤ W → 4 * W ≤ K → K ≤ M → 8 * W + 2 ≤ M → 4 * (M : ℝ) ≤ s → 4 * M ≤ R →
      r + M + 1 < R → 2 ≤ M' → W + K' ≤ M' → W + 2 * K' ≤ A * (M' - 1) →
      W + 2 * D + 10 * W + 3 ≤ S → S + 2 * n₁ * W ≤ G → W + 8 * W + 2 * K' + 3 ≤ Q →
      ((2 * G + 20 * W + 2 : ℕ) : ℝ) ≤ s →
      R + M + 1 + 8 * W + n₁ * (G + 5 * W + 1) + n * (9 * W + 1) + (M' + 5 * W + 1) ≤ R' →
      2 * R' + 2 ≤ A * W → (R' : ℕ∞) ≤ L → 2 * R' + 2 * n + n * W ≤ n * D →
      n + (2 * n₁ + 2 * n + 3) * W ≤ B →
      (∀ i, 1 ≤ lamT i ∧ lamT i ≤ 3 ∧ (lamT i + ((tT i : ℕ) : ℤ)) % 4 = 2) →
      (∀ i l, i ≤ l → lamT i ≤ lamT l) →
      (∀ i, (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) - R' + (S + Q + 4 * W + M' + W + 1) ≤ αT i ∧
        βT i + (S + Q + 4 * W + M' + W + 1) ≤ (if tT i = 0 ∨ tT i = 2 then z 0 else z 1) + R') →
      (∀ i, tT i ≠ 0 → z 1 + (S + Q + 4 * W + M' + W + 1) ≤ αT i) →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i l, i < l → tT i = tT l → (tT i = 1 ∨ tT i = 2 → βT i + S + Q ≤ αT l) ∧
        (tT i = 0 ∨ tT i = 3 → βT l + S + Q ≤ αT i)) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) M' K' γ ∧
        (∀ i, 6 * (R' : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ landingPos (z - R') (z + R') (σ i) (γ i)
            ∧
          (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + ((2 * (Q : ℤ) - 1 : ℤ) : ℝ) ≤ 14 * R') ∧
        (∀ i, b i ∈ {b : LatticeSite 2 |
          (tT i = 0 ∧ b 1 = z 1 + R' ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 1 ∧ b 0 = z 0 + R' ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i) ∨
          (tT i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 0 ∧ b 0 ≤ βT i) ∨
          (tT i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ αT i ≤ b 1 ∧ b 1 ≤ βT i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₁, hc₁, hg⟩ := exists_pos_le_law_separated_of_separated_half σ hσ c A (A + 4)
  obtain ⟨c₂, hc₂, hp⟩ := exists_pos_le_law_half_target_windows σ hσ c A n n₁ hn₁
  refine ⟨c₂ * c₁, ENNReal.mul_pos hc₂.ne' hc₁.ne', ?_⟩
  intro q L hCB z r R R' W M K M' K' D S G Q B s J tT lamT αT βT hW hWK hKM hWM hs hMR hrM hM'
    hWKM' hAM' hS hG hQ hs' hRR' hAW hL hjog hB hlamT hlamT2 hTcor hTline hTwid hTord
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
    (by omega) le_rfl hs hMR hrM (by omega) hRD hRA
    (le_trans (by exact_mod_cast (show R + M + 1 + 8 * W ≤ R' by omega)) hL)
  have h₂ := hp q L hCB z r (R + M + 1 + 8 * W) R' W (4 * W) W M' K' D S G Q B
    (s - 4 * ((4 * W : ℕ) : ℝ)) J tT lamT αT βT hW le_rfl (by omega) hM' hWKM'
    (by
      have : 3 * W ≤ 4 * W - 1 := by omega
      have : 4 * W - 1 ≤ A * (4 * W - 1) := Nat.le_mul_of_pos_left _ hA
      omega)
    hAM' (by omega) hG (by omega) (by push_cast at hs' ⊢; linarith) (by omega) (by
      have : n₁ * (G + 5 * W + 1) = n₁ * (G + 4 * W + W + 1) := by ring
      have : n * (9 * W + 1) = n * (2 * (4 * W) + W + 1) := by ring
      omega) hAW hL hjog hB hlamT hlamT2 (fun i => by
        have := hTcor i
        constructor <;> omega) (fun i h => by have := hTline i h; omega) hTwid hTord
  calc c₂ * c₁ * law q _ = c₂ * (c₁ * law q _) := mul_assoc _ _ _
    _ ≤ c₂ * law q _ := mul_le_mul' le_rfl h₁
    _ ≤ _ := h₂

end Targets

end PercLib.Models.Planar
