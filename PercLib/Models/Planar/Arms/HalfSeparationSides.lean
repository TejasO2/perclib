/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation), and Section 4.6
(the half-plane versions of the separation theorem).
-/
module

public import PercLib.Models.Planar.Arms.SeparationSides

/-!
# Local separation on the half-sides of a box

The half-plane versions of the separation of arms need Nolin's local separation lemma (Lemma 15)
on the three sides of the half-box `[z₀ - R, z₀ + R] × [z₁, z₁ + R]` that meet the arms of the
half-plane `{v | z₁ ≤ v₁}`: the top side of `B_R(z)` (`exists_law_separable_ge_top`) and the two
**half-sides**, the parts of the right and the left sides of `B_R(z)` above the line `y = z₁`.

An open arm of the half-plane lies in the rows `[z₁, z₁ + R - 1]` before its last vertex, and a dual
arm in the face rows `[z₁, z₁ + R - 1]` (faces are labelled by their lower-left corners). So the
strip along a half-side, read as a top-side strip by a symmetry of `ℤ²`, has its open and its dual
crossings in the same columns `[A, B]`, `B = A + 2N`, with dual edges crossing edges of the columns
`[A, B + 1]`: the box of faces is that of the open strip at the end on the line (`k = 0` in
`exists_law_separable_ge_aux_wide`) and one column wider at the end at the corner of `B_R(z)`
(`k' = 1`). The strip has height `N` and length `2N`, so with `R = 2N + 1` it covers the half-side.

* `exists_law_separable_ge_top_half`: Lemma 15 for such a strip along a top row `T`, columns
  `[A, B]`, `B = A + 2N` (width `2`, `k = 0`, `k' = 1`).
* `mem_separable_top_half_of_inter_eq`: the event is determined by the edges of the box
  `[A - M - K, B + 1 + M + K] × [T - N, T + M + 1]`, `M = ⌊√η N⌋`, `K = ⌊η N⌋`.
* `separable_right_half_of_top`, `separable_left_half_of_top`: the event for the configuration
  moved by the swap `(x, y) ↦ (y, x)` (by the quarter turn `(x, y) ↦ (y, -x)`) is the event along
  the column `T` (the column `X = -T`) for the rows `[A, B]`, as in `separable_right_of_top` and
  `separable_left_of_top`.

For the right half-side of `B_R(z)` take `A = z₁`, `B = z₁ + R - 1` and `T = z₀ + R`; for the left
half-side `A = z₁`, `B = z₁ + R - 1`, `X = z₀ - R`. The corners of the strip in doubled rows are
`2 z₁` (the line) and `2 (z₁ + R)` (the corner of `B_R(z)`).

## Main results

* `exists_law_separable_ge_top_half`: **Lemma 15 for the strip of a half-side.**
* `mem_separable_top_half_of_inter_eq`: determination.
* `separable_right_half_of_top`, `separable_left_half_of_top`: the right and the left half-sides.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The strip of a half-side, read on a top row -/

/-- **Local separation for the strip of a half-side** (Nolin's Lemma 15, read off
`exists_law_separable_ge_aux_wide_of_le` with width `2`, `k = 0` and `k' = 1`). For every `δ > 0`
there is `J₀` such that for every `J ≥ J₀`, with `η = (1 / (16 · 8^J))²` and `N₀ = (16 · 8^J)² + 2`,
uniformly over the laws with crossing bounds `c` up to `L`, for `N₀ ≤ N ≤ L` and columns `[A, B]`,
`B = A + 2N`, with probability at least `1 - δ` the following
holds for the strip of height `N` below the row `T`. Every finite family of crossings from the row
`T - N` (open, an open walk in `[A, B] × [T - N, T]`) or from the face row `T - N - 1` (dual, a walk
of faces of `[A, B] × [T - N - 1, T]` along dual-open dual edges crossing edges of
`[A, B + 1] × [T - N, T]`) to the row `T`, with crossings of the same colour disjoint, can be
replaced by a family with the same colours and starting points, with crossings of the same colour
disjoint, meeting the row `T` only at their ends, whose ends, in doubled columns (`2 x` for an open
end `(x, T)`, `2 x + 1` for a dual end), are at least `4 √η N` apart and at least `4 √η N` from
`2 A` and `2 (B + 1)`, and each of which carries a fence: a crossing of its colour from the left
side to the right side of `[x - ⌊η N⌋, x + ⌊η N⌋] × [T, T + ⌊√η N⌋]` above its end `(x, T)`, whose
left end is joined in its colour to a vertex of the new crossing inside the ball of radius
`⌊√η N⌋` around the end. -/
theorem exists_law_separable_ge_top_half (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ η : ℝ, η = (1 / ((16 * 8 ^ J : ℕ) : ℝ)) ^ 2 →
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (A B T : ℤ) (N : ℕ), B = A + 2 * N → (16 * 8 ^ J) ^ 2 + 2 ≤ N →
      (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = T - N ∧ b i 1 = T ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = T - N - 1 ∧ b i 1 = T ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]})) →
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
        ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = T - N ∧ b' i 1 = T ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
                ![B, T]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = T - N - 1 ∧ b' i 1 = T ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
                ![B, T]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2)
                  ![B + 1, T]})) ∧
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ T) ∧
          (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, T]
                ![b' i 0 + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨J₀, hsep⟩ := exists_law_separable_ge_aux_wide_of_le c 2 (by norm_num) hδ
  refine ⟨J₀, fun J hJ η hη q L h A B T N hB hN hNL => (hsep J hJ η hη q L h N hN hNL 0 1
    ![A, T - N] ![B, T] ![A, T - N - 1] ![B, T] ![A, T - N] ![B + 1, T] le_rfl zero_le_one
    zero_le_one le_rfl
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; push_cast; omega,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; ring⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero],
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)).trans
    (measure_mono fun ω hω => ?_)⟩
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨b'', γ'', h1, h2, h3, h4, h5, h6⟩ := hω m (fun k => σ (e.symm k))
    (fun k => a (e.symm k)) (fun k => b (e.symm k)) (fun k => γ (e.symm k))
    (fun k => hcr (e.symm k))
    (fun k k' hkk' hσ => hdisj _ _ (fun h => hkk' (e.symm.injective h)) hσ)
  refine ⟨fun i => b'' (e i),
    fun i => (γ'' (e i)).copy (congrArg a (e.symm_apply_apply i)) rfl, fun i => ?_,
    fun i k hik hσ x hx => ?_, fun i x hx => ?_, fun i k hik => ?_, fun i => ?_, fun i => ?_⟩
  · have := h1 (e i)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.edges_copy] using this
  · simp only [SimpleGraph.Walk.support_copy] at hx ⊢
    refine h2 (e i) (e k) (e.injective.ne hik) ?_ x hx
    simpa only [Equiv.symm_apply_apply] using hσ
  · simp only [SimpleGraph.Walk.support_copy] at hx
    exact h5 (e i) x hx
  · have := h3 (e i) (e k) (e.injective.ne hik)
    simpa only [Equiv.symm_apply_apply] using this
  · have := h4 (e i)
    simpa only [Equiv.symm_apply_apply, Matrix.cons_val_zero] using this
  · have := h6 (e i)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    simpa only [SimpleGraph.Walk.support_copy] using this


/-- **Local separation along the top side of `B_R(z)`, at every scale parameter from some on**
(`exists_law_separable_ge_top` with the explicit `η = (1 / (16 · 8^J))²` of
`exists_law_separable_ge_aux_wide_of_le`, width `4`, `k = k' = 1`): there is `J₀` such that for
every `J ≥ J₀` the event of `exists_law_separable_ge_top` with this `η` has probability at least
`1 - δ` for `(16 · 8^J)² + 4 ≤ N ≤ L`. Together with `exists_law_separable_ge_top_half` this gives
one `η` for the top side and the half-sides. -/
theorem exists_law_separable_ge_top_of_le (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ η : ℝ, η = (1 / ((16 * 8 ^ J : ℕ) : ℝ)) ^ 2 →
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ), R = 2 * N + 1 →
      (16 * 8 ^ J) ^ 2 + 4 ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = z 1 + R - N ∧ b i 1 = z 1 + R ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
              ![z 0 + R - 1, z 1 + R]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = z 1 + R - N - 1 ∧ b i 1 = z 1 + R ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
              ![z 0 + R - 1, z 1 + R]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2) ![z 0 + R, z 1 + R]})) →
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
        ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = z 1 + R - N ∧ b' i 1 = z 1 + R ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
                ![z 0 + R - 1, z 1 + R]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = z 1 + R - N - 1 ∧ b' i 1 = z 1 + R ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
                ![z 0 + R - 1, z 1 + R]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2)
                  ![z 0 + R, z 1 + R]})) ∧
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ z 1 + R) ∧
          (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z 0 - R) : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, z 1 + R]
                ![b' i 0 + ⌊η * N⌋₊, z 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨J₀, hsep⟩ := exists_law_separable_ge_aux_wide_of_le c 4 (by norm_num) hδ
  refine ⟨J₀, fun J hJ η hη q L h z N R hR hN hNL => (hsep J hJ η hη q L h N hN hNL 1 1
    ![z 0 - R + 1, z 1 + R - N] ![z 0 + R - 1, z 1 + R] ![z 0 - R, z 1 + R - N - 1]
    ![z 0 + R - 1, z 1 + R] ![z 0 - R, z 1 + R - N] ![z 0 + R, z 1 + R] zero_le_one le_rfl
    zero_le_one le_rfl
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; push_cast; omega,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; ring⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring,
      by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]⟩)).trans
    (measure_mono fun ω hω => ?_)⟩
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨b'', γ'', h1, h2, h3, h4, h5, h6⟩ := hω m (fun k => σ (e.symm k))
    (fun k => a (e.symm k)) (fun k => b (e.symm k)) (fun k => γ (e.symm k))
    (fun k => hcr (e.symm k))
    (fun k k' hkk' hσ => hdisj _ _ (fun h => hkk' (e.symm.injective h)) hσ)
  refine ⟨fun i => b'' (e i),
    fun i => (γ'' (e i)).copy (congrArg a (e.symm_apply_apply i)) rfl, fun i => ?_,
    fun i k hik hσ x hx => ?_, fun i x hx => ?_, fun i k hik => ?_, fun i => ?_, fun i => ?_⟩
  · have := h1 (e i)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.edges_copy] using this
  · simp only [SimpleGraph.Walk.support_copy] at hx ⊢
    refine h2 (e i) (e k) (e.injective.ne hik) ?_ x hx
    simpa only [Equiv.symm_apply_apply] using hσ
  · simp only [SimpleGraph.Walk.support_copy] at hx
    exact h5 (e i) x hx
  · have := h3 (e i) (e k) (e.injective.ne hik)
    simpa only [Equiv.symm_apply_apply] using this
  · have := h4 (e i)
    simpa only [Equiv.symm_apply_apply, Matrix.cons_val_zero] using this
  · have := h6 (e i)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    simpa only [SimpleGraph.Walk.support_copy] using this


/-! ### Determination -/

/-- **Determination of the half-side event.** The event of `exists_law_separable_ge_top_half`
depends only on the edges with both ends in the box
`[A - M - K, B + 1 + M + K] × [T - N, T + M + 1]`, `M = ⌊√η N⌋ ≤ N`, `K = ⌊η N⌋`. -/
theorem mem_separable_top_half_of_inter_eq {η : ℝ} {A B T : ℤ} {N : ℕ}
    (hM : ⌊Real.sqrt η * N⌋₊ ≤ N) {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc
        (![A - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊, T - N] : LatticeSite 2)
        ![B + 1 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊ + 1]} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ Icc
        (![A - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊, T - N] : LatticeSite 2)
        ![B + 1 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊ + 1]})
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = T - N ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = T - N - 1 ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = T - N ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = T - N - 1 ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2)
                ![B + 1, T]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ T) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, T]
              ![b' i 0 + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω' ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = T - N ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = T - N - 1 ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = T - N ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = T - N - 1 ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2)
                ![B + 1, T]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ T) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, T]
              ![b' i 0 + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  set M := ⌊Real.sqrt η * N⌋₊ with hMdef
  set K := ⌊η * N⌋₊ with hKdef
  set Tlo : LatticeSite 2 := ![A - M - K, T - N] with hTlo
  set Thi : LatticeSite 2 := ![B + 1 + M + K, T + M + 1] with hThi
  have hTlo0 : Tlo 0 = A - M - K := rfl
  have hTlo1 : Tlo 1 = T - N := rfl
  have hThi0 : Thi 0 = B + 1 + M + K := rfl
  have hThi1 : Thi 1 = T + M + 1 := rfl
  -- edges in the box are open in both or in neither
  have hedge : ∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, v ∈ Icc Tlo Thi) → (e ∈ ω ↔ e ∈ ω') := by
    intro e he
    have := congrArg (e ∈ ·) h
    simp only [mem_inter_iff, eq_iff_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
  -- the ends of the edges of a walk are vertices of the walk
  have hsupp : ∀ {u v : LatticeSite 2} (p : (zdGraph 2).Walk u v) (e : Sym2 (LatticeSite 2)),
      e ∈ p.edges → ∀ x ∈ e, x ∈ p.support := by
    intro u v p e he x hx
    induction e using Sym2.ind with
    | h s t =>
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact p.fst_mem_support_of_mem_edges he
      · exact p.snd_mem_support_of_mem_edges he
  have hbox : ∀ x : LatticeSite 2, A ≤ x 0 → x 0 ≤ B + 1 → T - N ≤ x 1 →
      x 1 ≤ T → x ∈ Icc Tlo Thi := by
    intro x h₁ h₂ h₃ h₄
    rw [mem_Icc_two_iff, hTlo0, hTlo1, hThi0, hThi1]
    omega
  -- the hypothesis and the first conclusion transfer between configurations agreeing on the box
  have key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      (∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, v ∈ Icc Tlo Thi) → (e ∈ ω₁ ↔ e ∈ ω₂)) →
      ∀ (c : Bool) {u v : LatticeSite 2} (p : (zdGraph 2).Walk u v), cond c
        (u 1 = T - N ∧ v 1 = T ∧
          (∀ x ∈ p.support, x ∈ Icc (![A, T - N] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ p.edges, e ∈ ω₁)
        (u 1 = T - N - 1 ∧ v 1 = T ∧
          (∀ x ∈ p.support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ p.edges, e ∈ dualConfig ω₁ ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]}) →
      cond c
        (u 1 = T - N ∧ v 1 = T ∧
          (∀ x ∈ p.support, x ∈ Icc (![A, T - N] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ p.edges, e ∈ ω₂)
        (u 1 = T - N - 1 ∧ v 1 = T ∧
          (∀ x ∈ p.support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ p.edges, e ∈ dualConfig ω₂ ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]}) := by
    intro ω₁ ω₂ h₁₂ c u v p hp
    cases c
    · obtain ⟨hu, hv, hS, hE⟩ := hp
      refine ⟨hu, hv, hS, fun e he => ?_⟩
      obtain ⟨hd, e₀, ⟨he₀, he₀B⟩, rfl⟩ := hE e he
      refine ⟨?_, e₀, ⟨he₀, he₀B⟩, rfl⟩
      rw [dualEdge_mem_dualConfig_iff he₀] at hd ⊢
      refine fun h' => hd ((h₁₂ e₀ fun x hx => ?_).2 h')
      have := mem_Icc_two_iff.1 (he₀B x hx)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      exact hbox x (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨hu, hv, hS, hE⟩ := hp
      refine ⟨hu, hv, hS, fun e he => (h₁₂ e fun x hx => ?_).1 (hE e he)⟩
      have := mem_Icc_two_iff.1 (hS x (hsupp p e he x hx))
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      exact hbox x (by omega) (by omega) (by omega) (by omega)
  -- connections inside boxes of `Icc Tlo (Thi - 1)` transfer
  have hD : dualConfig ω ∩ {f | ∀ g ∈ f, g ∈ Icc Tlo (Thi - 1)} =
      dualConfig ω' ∩ {f | ∀ g ∈ f, g ∈ Icc Tlo (Thi - 1)} :=
    dualConfig_inter_eq_of_inter_eq (by rwa [sub_add_cancel])
  have hconn : ∀ (c : Bool) (S : Set (LatticeSite 2)) (x y : LatticeSite 2),
      S ⊆ Icc Tlo (Thi - 1) →
      cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn S x y →
      cond c ω' (dualConfig ω') ∩ (zdGraph 2).edgeSet ∈ localConn S x y := by
    intro c S x y hS hxy
    cases c
    · exact (inter_mem_localConn_iff_of_inter_eq hS _ hD x y).1 hxy
    · exact (inter_mem_localConn_iff_of_inter_eq (hS.trans (Icc_subset_Icc le_rfl
        (sub_le_self _ zero_le_one))) _ h x y).1 hxy
  have hsub : ∀ A B : LatticeSite 2, Tlo 0 ≤ A 0 → Tlo 1 ≤ A 1 → B 0 ≤ Thi 0 - 1 →
      B 1 ≤ Thi 1 - 1 → Icc A B ⊆ Icc Tlo (Thi - 1) := by
    intro A B h₁ h₂ h₃ h₄
    refine Icc_subset_Icc ?_ ?_
    · rw [Pi.le_def, Fin.forall_fin_two]
      exact ⟨h₁, h₂⟩
    · rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Pi.sub_apply, Pi.one_apply]
      exact ⟨h₃, h₄⟩
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨b', γ', h1, h2, h3, h4, h5, h6⟩ := hω ι σ a b γ
    (fun i => key ω' ω (fun e he => (hedge e he).symm) (σ i) (γ i) (hcr i)) hdisj
  refine ⟨b', γ', fun i => key ω ω' hedge (σ i) (γ' i) (h1 i), h2, h3, h4, h5, fun i => ?_⟩
  -- the end of the new crossing lies in the strip
  have hb' : A ≤ b' i 0 ∧ b' i 0 ≤ B ∧ b' i 1 = T := by
    have hi := h1 i
    revert hi
    cases σ i
    · rintro ⟨-, hv, hS, -⟩
      have := mem_Icc_two_iff.1 (hS _ (γ' i).end_mem_support)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
    · rintro ⟨-, hv, hS, -⟩
      have := mem_Icc_two_iff.1 (hS _ (γ' i).end_mem_support)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  obtain ⟨x, hx, l, r, hl, hr, hlr, hxl⟩ := h6 i
  refine ⟨x, hx, l, r, hl, hr, hconn _ _ _ _ (hsub _ _ ?_ ?_ ?_ ?_) hlr,
    hconn _ _ _ _ (hsub _ _ ?_ ?_ ?_ ?_) hxl⟩ <;>
    simp only [hTlo0, hTlo1, hThi0, hThi1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] <;> omega


/-! ### The right half-side -/

/-- **Local separation along a half-side on the right, read off a top row.** If the configuration
swapped by `(x, y) ↦ (y, x)` has the property of `exists_law_separable_ge_top_half` for the columns
`[A, B]` and the row `T`, then the configuration has it along the column `T` for the rows
`[A, B]`: for the strip `[T - N, T] × [A, B]` crossed from left to right by open crossings, the
faces `[T - N - 1, T] × [A, B]` crossed by dual crossings whose dual edges cross edges of
`[T - N, T] × [A, B + 1]`, the doubled rows `2 y` (open end `(T, y)`) and `2 y + 1` (dual end), the
corners `2 A`, `2 (B + 1)`, and fences from the bottom side to the top side of the box
`[T, T + ⌊√η N⌋] × [y - ⌊η N⌋, y + ⌊η N⌋]` to the right of the end. The swap fixes the faces. -/
theorem separable_right_half_of_top {η : ℝ} {A B T : ℤ} {N : ℕ} {ω : Config (LatticeSite 2)}
    (h : Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) '' ω ∈
      {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = T - N ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = T - N - 1 ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = T - N ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = T - N - 1 ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2)
                ![B + 1, T]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ T) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, T]
              ![b' i 0 + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = T - N ∧ b i 0 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![T - N, A] : LatticeSite 2)
            ![T, B]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = T - N - 1 ∧ b i 0 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![T - N - 1, A] : LatticeSite 2)
            ![T, B]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![T - N, A] : LatticeSite 2) ![T, B + 1]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = T - N ∧ b' i 0 = T ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![T - N, A] : LatticeSite 2)
            ![T, B]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = T - N - 1 ∧ b' i 0 = T ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![T - N - 1, A] : LatticeSite 2)
            ![T, B]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![T - N, A] : LatticeSite 2) ![T, B + 1]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0, b' i 1 - ⌊η * N⌋₊]
              ![b' i 0 + ⌊Real.sqrt η * N⌋₊, b' i 1 + ⌊η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨g, hg⟩ := exists_iso_swap
  have hgf : (⇑g : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := funext hg
  have hgh : ∀ v, g.toHom v = ![v 1, v 0] := hg
  have hgg : ∀ v, g (g v) = v := fun v => by
    rw [hg, hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact (eq_vec_two v).symm
  have hgs : ∀ v, g.symm v = ![v 1, v 0] := fun v => by
    apply g.injective
    rw [RelIso.apply_symm_apply, hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact eq_vec_two v
  have hgg2 : ∀ e : Sym2 (LatticeSite 2), Sym2.map g (Sym2.map g e) = e := fun e => by
    rw [hgf]
    exact map_swap_map_swap e
  have hdual : dualConfig (Sym2.map g '' ω) = Sym2.map g '' dualConfig ω := by
    rw [hgf]
    exact dualConfig_image_swap ω
  have hdE : ∀ e ∈ (zdGraph 2).edgeSet, dualEdge (Sym2.map g e) = Sym2.map g (dualEdge e) :=
    fun e he => by
      rw [hgf]
      exact dualEdge_map_swap he
  have hE : ∀ e, Sym2.map g e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet := fun e => by
    rw [hgf]
    exact map_swap_mem_edgeSet_iff e
  rw [← hgf] at h
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨b'f, γ'f, h1, h2, h3, h4, h5, h6⟩ := h ι σ (fun i => g (a i)) (fun i => g (b i))
    (fun i => (γ i).map g.toHom) (fun i => by
      have hi := hcr i
      revert hi
      cases σ i
      · rintro ⟨ha, hb, hS, hE'⟩
        refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
        · rw [hg]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · rw [hg]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (hS y hy)
          rw [hgh, mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
          omega
        · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          obtain ⟨hd, e₁, ⟨he₁, he₁B⟩, rfl⟩ := hE' e₀ he₀
          refine ⟨?_, Sym2.map g e₁, ⟨(hE e₁).2 he₁, fun x hx => ?_⟩, hdE e₁ he₁⟩
          · rw [hdual]
            exact ⟨_, hd, rfl⟩
          · rw [Sym2.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := mem_Icc_two_iff.1 (he₁B y hy)
            rw [hg, mem_Icc_two_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
            omega
      · rintro ⟨ha, hb, hS, hE'⟩
        refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
        · rw [hg]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · rw [hg]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (hS y hy)
          rw [hgh, mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
          omega
        · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          exact ⟨e₀, hE' e₀ he₀, rfl⟩) (fun i k hik hσ x hx hx' => by
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hx'
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hx'
      exact hdisj i k hik hσ y hy (g.injective hyy' ▸ hy'))
  -- the ends of the new crossings lie on the top row of the swapped strip
  have hb1 : ∀ i, b'f i 1 = T := fun i => by
    have hi := h1 i
    revert hi
    cases σ i
    · exact fun hi => hi.2.1
    · exact fun hi => hi.2.1
  have hgb0 : ∀ i, g (b'f i) 0 = b'f i 1 := fun i => by
    rw [hg]
    simp only [Matrix.cons_val_zero]
  have hgb1 : ∀ i, g (b'f i) 1 = b'f i 0 := fun i => by
    rw [hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨fun i => g (b'f i), fun i => ((γ'f i).map g.toHom).copy (hgg (a i)) rfl,
    fun i => ?_, fun i k hik hσ x hx hx' => ?_, fun i x hx => ?_, fun i k hik => ?_,
    fun i => ?_, fun i => ?_⟩
  · have hi := h1 i
    revert hi
    cases σ i
    · rintro ⟨ha, hb, hS, hE'⟩
      refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
      · have ha' : g (a i) 1 = _ := ha
        rw [hg] at ha'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha'
        omega
      · change g (b'f i) 0 = _
        rw [hgb0]
        omega
      · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have := mem_Icc_two_iff.1 (hS y hy)
        rw [hgh, mem_Icc_two_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
        omega
      · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.mem_map] at he
        obtain ⟨e₀, he₀, rfl⟩ := he
        obtain ⟨hd, e₁, ⟨he₁, he₁B⟩, rfl⟩ := hE' e₀ he₀
        rw [hdual] at hd
        obtain ⟨e₂, he₂, he₂'⟩ := hd
        refine ⟨?_, Sym2.map g e₁, ⟨(hE e₁).2 he₁, fun x hx => ?_⟩, hdE e₁ he₁⟩
        · change Sym2.map g (dualEdge e₁) ∈ _
          rw [← he₂', hgg2]
          exact he₂
        · rw [Sym2.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (he₁B y hy)
          rw [hg, mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
          omega
    · rintro ⟨ha, hb, hS, hE'⟩
      refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
      · have ha' : g (a i) 1 = _ := ha
        rw [hg] at ha'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha'
        omega
      · change g (b'f i) 0 = _
        rw [hgb0]
        omega
      · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have := mem_Icc_two_iff.1 (hS y hy)
        rw [hgh, mem_Icc_two_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
        omega
      · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.mem_map] at he
        obtain ⟨e₀, he₀, rfl⟩ := he
        obtain ⟨e₂, he₂, he₂'⟩ := hE' e₀ he₀
        change Sym2.map g e₀ ∈ _
        rw [← he₂', hgg2]
        exact he₂
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hyy'⟩ := hx'
    exact h2 i k hik hσ y hy (g.injective hyy' ▸ hy')
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, ← List.map_dropLast,
      List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := h3 i y hy
    change g y 0 ≠ g (b'f i) 0
    rw [hgb0, hg]
    simp only [Matrix.cons_val_zero]
    rw [hb1]
    exact this
  · simpa only [hgb1] using h4 i k hik
  · simpa only [hgb1] using h5 i
  · obtain ⟨x, hx, l, r, hl, hr, hlr, hxl⟩ := h6 i
    have hcfg : cond (σ i) (Sym2.map g '' ω) (dualConfig (Sym2.map g '' ω)) =
        Sym2.map g '' cond (σ i) ω (dualConfig ω) := by
      cases σ i
      · exact hdual
      · rfl
    rw [hcfg] at hlr hxl
    have hgl : ∀ w, g w 0 = w 1 ∧ g w 1 = w 0 := fun w => by
      rw [hg]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨trivial, trivial⟩
    refine ⟨g x, ?_, g l, g r, ?_, ?_, inter_edgeSet_mem_localConn_of_image g _
      (fun v hv => ?_) (by rwa [hgg, hgg]), inter_edgeSet_mem_localConn_of_image g _
      (fun v hv => ?_) (by rwa [hgg, hgg])⟩
    · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem hx
    · change g l 1 = g (b'f i) 1 - _
      rw [(hgl l).2, hgb1, hl]
    · change g r 1 = g (b'f i) 1 + _
      rw [(hgl r).2, hgb1, hr]
    · rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      rw [hgs, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hgb0, hgb1, hb1]
      omega
    · rw [mem_Icc_two_iff] at hv
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
      rw [hgs, mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
        Pi.natCast_apply, hgb0, hgb1]
      omega


/-! ### The left half-side -/

/-- **Local separation along a half-side on the left, read off a top row.** If the configuration
turned by `(x, y) ↦ (y, -x)` has the property of `exists_law_separable_ge_top_half` for the columns
`[A, B]` and the row `T = -X`, then the configuration has it along the column `X` for the rows
`[A, B]`: for the strip `[X, X + N] × [A, B]` crossed from right to left by open crossings, the
faces `[X - 1, X + N] × [A, B]` crossed by dual crossings (from the face column `X + N` to the face
column `X - 1`) whose dual edges cross edges of `[X, X + N] × [A, B + 1]`, the doubled rows of the
ends as on the right, and fences from the bottom side to the top side of the box
`[x - ⌊√η N⌋, x] × [y - ⌊η N⌋, y + ⌊η N⌋]` to the left of the end `(x, y)`. The quarter turn moves
faces by one column. -/
theorem separable_left_half_of_top {η : ℝ} {A B T X : ℤ} {N : ℕ} (hT : T = -X)
    {ω : Config (LatticeSite 2)}
    (h : Sym2.map (fun v : LatticeSite 2 => ![v 1, 0 - v 0]) '' ω ∈
      {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = T - N ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = T - N - 1 ∧ b i 1 = T ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
            ![B, T]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2) ![B + 1, T]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = T - N ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = T - N - 1 ∧ b' i 1 = T ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![A, T - N - 1] : LatticeSite 2)
              ![B, T]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![A, T - N] : LatticeSite 2)
                ![B + 1, T]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ T) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, T]
              ![b' i 0 + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = X + N ∧ b i 0 = X ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![X, A] : LatticeSite 2)
            ![X + N, B]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = X + N ∧ b i 0 = X - 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![X - 1, A] : LatticeSite 2)
            ![X + N, B]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![X, A] : LatticeSite 2) ![X + N, B + 1]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = X + N ∧ b' i 0 = X ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![X, A] : LatticeSite 2)
            ![X + N, B]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = X + N ∧ b' i 0 = X - 1 ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![X - 1, A] : LatticeSite 2)
            ![X + N, B]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![X, A] : LatticeSite 2) ![X + N, B + 1]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * A : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (B + 1) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊Real.sqrt η * N⌋₊, b' i 1 - ⌊η * N⌋₊]
              ![b' i 0, b' i 1 + ⌊η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨sw, hsw⟩ := exists_iso_swap
  obtain ⟨g₁, hg₁⟩ := exists_iso_reflect_one 0
  obtain ⟨g₂, hg₂⟩ := exists_iso_reflect_one (-1)
  obtain ⟨F, hFt, hFf⟩ : ∃ F : Bool → (zdGraph 2 ≃g zdGraph 2),
      F true = sw.trans g₁ ∧ F false = sw.trans g₂ :=
    ⟨fun c => cond c (sw.trans g₁) (sw.trans g₂), rfl, rfl⟩
  have hFtv : ∀ v, F true v = g₁ (sw v) := fun v => by
    rw [hFt]
    rfl
  have hFfv : ∀ v, F false v = g₂ (sw v) := fun v => by
    rw [hFf]
    rfl
  -- the two maps in coordinates
  have hFt0 : ∀ v, F true v 0 = v 1 := fun v => by
    rw [hFtv, hg₁, hsw]
    simp only [Matrix.cons_val_zero]
  have hFt1 : ∀ v, F true v 1 = -v 0 := fun v => by
    rw [hFtv, hg₁, hsw]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, zero_sub]
  have hFf0 : ∀ v, F false v 0 = v 1 := fun v => by
    rw [hFfv, hg₂, hsw]
    simp only [Matrix.cons_val_zero]
  have hFf1 : ∀ v, F false v 1 = -1 - v 0 := fun v => by
    rw [hFfv, hg₂, hsw]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have hSt : ∀ v, (F true).symm v 0 = -v 1 ∧ (F true).symm v 1 = v 0 := fun v => by
    have h₀ := hFt0 ((F true).symm v)
    have h₁ := hFt1 ((F true).symm v)
    rw [RelIso.apply_symm_apply] at h₀ h₁
    omega
  have hSf : ∀ v, (F false).symm v 0 = -1 - v 1 ∧ (F false).symm v 1 = v 0 := fun v => by
    have h₀ := hFf0 ((F false).symm v)
    have h₁ := hFf1 ((F false).symm v)
    rw [RelIso.apply_symm_apply] at h₀ h₁
    omega
  have hfun : (⇑(F true) : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, 0 - v 0] := by
    funext v
    rw [hFtv, hg₁, hsw]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hft : (⇑(F true) : LatticeSite 2 → LatticeSite 2) =
      (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) ∘ fun v : LatticeSite 2 => ![v 1, v 0] := by
    funext v
    rw [Function.comp_apply, hFtv, hg₁, hsw]
  have hff : (⇑(F false) : LatticeSite 2 → LatticeSite 2) =
      (fun v : LatticeSite 2 => ![v 0, 0 - 1 - v 1]) ∘ fun v : LatticeSite 2 => ![v 1, v 0] := by
    funext v
    rw [Function.comp_apply, hFfv, hg₂, hsw, zero_sub]
  have hcomp : ∀ (f g : LatticeSite 2 → LatticeSite 2) (X : Config (LatticeSite 2)),
      Sym2.map (f ∘ g) '' X = Sym2.map f '' (Sym2.map g '' X) := fun f g X => by
    rw [Set.image_image]
    simp only [Sym2.map_map]
  have hdual : dualConfig (Sym2.map (F true) '' ω) = Sym2.map (F false) '' dualConfig ω := by
    rw [hft, hff, hcomp, hcomp, dualConfig_image_reflect 0, dualConfig_image_swap]
  have hdE : ∀ e ∈ (zdGraph 2).edgeSet,
      dualEdge (Sym2.map (F true) e) = Sym2.map (F false) (dualEdge e) := fun e he => by
    rw [hft, hff, ← Sym2.map_map, ← Sym2.map_map,
      dualEdge_map_reflect 0 ((map_swap_mem_edgeSet_iff e).2 he), dualEdge_map_swap he]
  have hE : ∀ e, Sym2.map (F true) e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet :=
    fun e => by
      rw [hft, ← Sym2.map_map, map_reflect_mem_edgeSet_iff, map_swap_mem_edgeSet_iff]
  have hss : ∀ (g : zdGraph 2 ≃g zdGraph 2) (e : Sym2 (LatticeSite 2)),
      Sym2.map g.symm (Sym2.map g e) = e := fun g e => by
    rw [Sym2.map_map, RelIso.symm_comp_self, Sym2.map_id, id]
  have hss' : ∀ (g : zdGraph 2 ≃g zdGraph 2) (e : Sym2 (LatticeSite 2)),
      Sym2.map g (Sym2.map g.symm e) = e := fun g e => by
    rw [Sym2.map_map, RelIso.self_comp_symm, Sym2.map_id, id]
  rw [← hfun] at h
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨b'f, γ'f, h1, h2, h3, h4, h5, h6⟩ := h ι σ (fun i => F (σ i) (a i))
    (fun i => F (σ i) (b i)) (fun i => (γ i).map (F (σ i)).toHom) (fun i => by
      have hi := hcr i
      revert hi
      cases σ i
      · rintro ⟨ha, hb, hS, hE'⟩
        refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
        · rw [hFf1]
          omega
        · rw [hFf1]
          omega
        · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (hS y hy)
          change F false y ∈ _
          rw [mem_Icc_two_iff, hFf0, hFf1]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
          omega
        · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          obtain ⟨hd, e₁, ⟨he₁, he₁B⟩, rfl⟩ := hE' e₀ he₀
          refine ⟨?_, Sym2.map (F true) e₁, ⟨(hE e₁).2 he₁, fun x hx => ?_⟩, hdE e₁ he₁⟩
          · rw [hdual]
            exact ⟨_, hd, rfl⟩
          · rw [Sym2.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx
            have := mem_Icc_two_iff.1 (he₁B y hy)
            rw [mem_Icc_two_iff, hFt0, hFt1]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
            omega
      · rintro ⟨ha, hb, hS, hE'⟩
        refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
        · rw [hFt1]
          omega
        · rw [hFt1]
          omega
        · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (hS y hy)
          change F true y ∈ _
          rw [mem_Icc_two_iff, hFt0, hFt1]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
          omega
        · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          exact ⟨e₀, hE' e₀ he₀, rfl⟩) (fun i k hik hσ x hx hx' => by
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hx'
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hx'
      rw [hσ] at hyy'
      exact hdisj i k hik hσ y hy ((F (σ k)).injective hyy' ▸ hy'))
  -- the ends of the new crossings lie on the top row of the reflected strip
  have hcond : ∀ {c : Bool} {A B P : Prop}, cond c A B → (A → P) → (B → P) → P := by
    intro c A B P h hA hB
    cases c
    · exact hB h
    · exact hA h
  have hcond_t : ∀ {c : Bool} {A B : Prop}, cond c A B → c = true → A := by
    rintro c A B h rfl
    exact h
  have hcond_f : ∀ {c : Bool} {A B : Prop}, cond c A B → c = false → B := by
    rintro c A B h rfl
    exact h
  have hcond_i : ∀ {c : Bool} {A B : Prop}, (c = true → A) → (c = false → B) → cond c A B := by
    intro c A B hA hB
    cases c
    · exact hB rfl
    · exact hA rfl
  have hb1 : ∀ i, b'f i 1 = T := fun i =>
    hcond (h1 i) (fun hi => hi.2.1) (fun hi => hi.2.1)
  have hS0 : ∀ c v, (F c).symm v 1 = v 0 := fun c v => by
    cases c
    · exact (hSf v).2
    · exact (hSt v).2
  have hS1 : ∀ c v w, (F c).symm v 0 - (F c).symm w 0 = w 1 - v 1 := fun c v w => by
    cases c
    · have := (hSf v).1
      have := (hSf w).1
      omega
    · have := (hSt v).1
      have := (hSt w).1
      omega
  refine ⟨fun i => (F (σ i)).symm (b'f i),
    fun i => ((γ'f i).map (F (σ i)).symm.toHom).copy ((F (σ i)).symm_apply_apply (a i)) rfl,
    fun i => ?_, fun i k hik hσ x hx hx' => ?_, fun i x hx => ?_, fun i k hik => ?_,
    fun i => ?_, fun i => ?_⟩
  · refine hcond_i (fun hσi => ?_) (fun hσi => ?_)
    · obtain ⟨ha, hb, hS, hE'⟩ := hcond_t (h1 i) hσi
      refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
      · have ha' : F (σ i) (a i) 1 = _ := ha
        rw [hσi, hFt1] at ha'
        omega
      · have := (hSt (b'f i)).1
        change (F (σ i)).symm (b'f i) 0 = _
        rw [hσi]
        omega
      · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have := mem_Icc_two_iff.1 (hS y hy)
        change (F (σ i)).symm y ∈ _
        rw [hσi, mem_Icc_two_iff, (hSt y).1, (hSt y).2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
        omega
      · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.mem_map] at he
        obtain ⟨e₀, he₀, rfl⟩ := he
        obtain ⟨e₂, he₂, he₂'⟩ := hE' e₀ he₀
        change Sym2.map (F (σ i)).symm e₀ ∈ _
        rw [hσi, ← he₂', hss]
        exact he₂
    · obtain ⟨ha, hb, hS, hE'⟩ := hcond_f (h1 i) hσi
      refine ⟨?_, ?_, fun x hx => ?_, fun e he => ?_⟩
      · have ha' : F (σ i) (a i) 1 = _ := ha
        rw [hσi, hFf1] at ha'
        omega
      · have := (hSf (b'f i)).1
        change (F (σ i)).symm (b'f i) 0 = _
        rw [hσi]
        omega
      · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have := mem_Icc_two_iff.1 (hS y hy)
        change (F (σ i)).symm y ∈ _
        rw [hσi, mem_Icc_two_iff, (hSf y).1, (hSf y).2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
        omega
      · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.mem_map] at he
        obtain ⟨e₀, he₀, rfl⟩ := he
        obtain ⟨hd, e₁, ⟨he₁, he₁B⟩, rfl⟩ := hE' e₀ he₀
        rw [hdual] at hd
        obtain ⟨e₂, he₂, he₂'⟩ := hd
        have hd₁ := hdE (Sym2.map (F true).symm e₁) ((hE _).1 (by rwa [hss']))
        rw [hss'] at hd₁
        refine ⟨?_, Sym2.map (F true).symm e₁, ⟨(hE _).1 (by rwa [hss']), fun x hx => ?_⟩, ?_⟩
        · change Sym2.map (F (σ i)).symm (dualEdge e₁) ∈ _
          rw [hσi, ← he₂', hss]
          exact he₂
        · rw [Sym2.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (he₁B y hy)
          rw [mem_Icc_two_iff, (hSt y).1, (hSt y).2]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
          omega
        · change _ = Sym2.map (F (σ i)).symm (dualEdge e₁)
          rw [hσi, hd₁, hss]
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hyy'⟩ := hx'
    rw [hσ] at hyy'
    exact h2 i k hik hσ y hy ((F (σ k)).symm.injective hyy' ▸ hy')
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, ← List.map_dropLast,
      List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := h3 i y hy
    have := hS1 (σ i) y (b'f i)
    have := hb1 i
    change (F (σ i)).symm y 0 ≠ (F (σ i)).symm (b'f i) 0
    omega
  · simpa only [hS0] using h4 i k hik
  · simpa only [hS0] using h5 i
  · obtain ⟨x, hx, l, r, hl, hr, hlr, hxl⟩ := h6 i
    have hcfg : cond (σ i) (Sym2.map (F true) '' ω) (dualConfig (Sym2.map (F true) '' ω)) =
        Sym2.map (F (σ i)) '' cond (σ i) ω (dualConfig ω) := by
      cases σ i
      · exact hdual
      · rfl
    rw [hcfg] at hlr hxl
    have hb' := hb1 i
    refine ⟨(F (σ i)).symm x, ?_, (F (σ i)).symm l, (F (σ i)).symm r, ?_, ?_,
      inter_edgeSet_mem_localConn_of_image (F (σ i)) _ (fun v hv => ?_)
        (by rwa [RelIso.apply_symm_apply, RelIso.apply_symm_apply]),
      inter_edgeSet_mem_localConn_of_image (F (σ i)) _ (fun v hv => ?_)
        (by rwa [RelIso.apply_symm_apply, RelIso.apply_symm_apply])⟩
    · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem hx
    · change (F (σ i)).symm l 1 = (F (σ i)).symm (b'f i) 1 - _
      rw [hS0, hS0, hl]
    · change (F (σ i)).symm r 1 = (F (σ i)).symm (b'f i) 1 + _
      rw [hS0, hS0, hr]
    · rw [mem_Icc_two_iff] at hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
      have := hS1 (σ i) v (b'f i)
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hS0]
      omega
    · rw [mem_Icc_two_iff] at hv
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
      have := hS1 (σ i) v (b'f i)
      rw [mem_Icc_two_iff]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, hS0]
      omega


end PercLib.Models.Planar
