/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-23. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation) and the proof of
Theorem 11 (the separation step uses Lemma 15 on strips along the four sides of a box).
-/
module

public import PercLib.Models.Planar.Arms.QuasiMultiplicativity

/-!
# Local separation on the four sides of a box

Nolin's local separation lemma (Lemma 15) is proved for the strip `[0, 4N] × [0, N]` crossed from
bottom to top (`exists_law_separable_ge`) and, in the geometry of the arms of a box, for the strip
along the top side of the box of radius `2N + 1` (`exists_law_separable_ge_arm`). The separation of
arms needs it along the four sides of `B_R(z)`, `R = 2N + 1`, at any centre `z`. The strip along
the top side is a translate of the arm box (`exists_law_separable_ge_top`). The other three sides
are reached through the swap `(x, y) ↦ (y, x)` (right side), the reflection `(x, y) ↦ (x, -y)`
(bottom side) and the quarter turn `(x, y) ↦ (y, -x)` (left side): if the configuration moved by
the symmetry has the top-side property at the moved centre, the configuration has the property of
the side, read in the coordinates of that side (`separable_right_of_top`, `separable_bottom_of_top`,
`separable_left_of_top`). Open crossings are moved by the symmetry and dual crossings by the
corresponding map of faces, which differs from it by one unit for the reflection and the quarter
turn, since faces are labelled by their lower-left corners. The laws of the moved configurations
have the same crossing bounds (`CrossingBounds.swap`, `CrossingBounds.reflect`), so each of the four
side events has probability at least `1 - δ` (`exists_law_separable_ge_sides`).

The families of crossings are indexed by any finite type, so that the statements apply to the arms
landing on one side. The top-side event depends only on the edges in a box above the inner row of
the strip (`mem_separable_top_of_inter_eq`); with the symmetries this makes the four side events
independent of the arm events inside `B_N(z)`.

## Main results

* `exists_law_separable_ge_top`: Lemma 15 along the top side of `B_R(z)`, at any centre.
* `mem_separable_top_of_inter_eq`: the top-side event is determined by the edges of a box above
  the inner row of the strip.
* `image_sym2Map_inter_edgeSet`, `inter_edgeSet_mem_localConn_of_image`: connections through an
  automorphism of `ℤ²`.
* `separable_right_of_top`, `separable_bottom_of_top`, `separable_left_of_top`: the top-side
  property of the swapped, reflected or turned configuration, read on the right, bottom and left
  sides.
* `exists_law_separable_ge_sides`: **Lemma 15 on the four sides of `B_R(z)`.**
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The top side -/

/-- **Local separation along the top side of `B_R(z)`**, `R = 2N + 1`, at any centre `z`
(Nolin's Lemma 15 in the geometry of the arms, `exists_law_separable_ge_arm`, translated). For every
`δ > 0` there are `0 < η ≤ 1` and `N₀` such that, uniformly over the laws with crossing bounds `c`
up to `L`, for `N₀ ≤ N ≤ L`, with probability at least `1 - δ` the following holds for the strip of
height `N` along the top side of `B_R(z)`. Every finite family of crossings of the strip from its
bottom row to the top row `z₁ + R` of `B_R(z)`, each open (an open walk in
`[z₀ - R + 1, z₀ + R - 1] × [z₁ + R - N, z₁ + R]`) or dual (a walk of faces of
`[z₀ - R, z₀ + R - 1] × [z₁ + R - N - 1, z₁ + R]` along dual-open dual edges crossing edges of
`[z₀ - R, z₀ + R] × [z₁ + R - N, z₁ + R]`), with crossings of the same colour disjoint, can be
replaced by a family with the same colours and starting points, with crossings of the same colour
disjoint, meeting the top row only at their ends, whose ends, in doubled columns (`2 x` for an open
end `(x, z₁ + R)`, `2 x + 1` for a dual end), are at least `4 √η N` apart and at least `4 √η N`
from the doubled corners `2 (z₀ - R)` and `2 (z₀ + R)`, and each of which carries a fence: a
crossing of its colour from the left side to the right side of the box
`[x - ⌊η N⌋, x + ⌊η N⌋] × [z₁ + R, z₁ + R + ⌊√η N⌋]` above its end `(x, z₁ + R)`, whose left end
is joined in its colour to a vertex of the new crossing inside the ball of radius `⌊√η N⌋` around
the end.

The families are indexed by any finite type, so that the statement applies to subfamilies of a
family of arms. The open strip and the faces are those of the arms of `B_R(z)` near its top side:
before its last vertex an open arm lies in the columns `[z₀ - R + 1, z₀ + R - 1]` and a dual arm in
the face columns `[z₀ - R, z₀ + R - 1]`. -/
theorem exists_law_separable_ge_top (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ), R = 2 * N + 1 → N₀ ≤ N →
      (N : ℕ∞) ≤ L →
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
  obtain ⟨η, hη, hη1, N₀, hsep⟩ := exists_law_separable_ge_aux c hδ
  refine ⟨η, hη, hη1, N₀, fun q L h z N R hR hN hNL => (hsep q L h N hN hNL 1
    ![z 0 - R + 1, z 1 + R - N] ![z 0 + R - 1, z 1 + R] ![z 0 - R, z 1 + R - N - 1]
    ![z 0 + R - 1, z 1 + R] ![z 0 - R, z 1 + R - N] ![z 0 + R, z 1 + R] zero_le_one le_rfl
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; omega,
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

/-! ### Determination of the top-side event -/

/-- **Determination of the top-side event.** The event of `exists_law_separable_ge_top` depends
only on the edges with both ends in the box
`[z₀ - R - M - K, z₀ + R + M + K] × [z₁ + R - N, z₁ + R + M + 1]`, `M = ⌊√η N⌋ ≤ N`,
`K = ⌊η N⌋`: the open crossings and the fences of open crossings use only such edges, and the
dual crossings and the fences of dual crossings cross only such edges. In particular it does not
depend on the edges below the row `z₁ + R - N` of the strip. -/
theorem mem_separable_top_of_inter_eq {η : ℝ} {z : LatticeSite 2} {N R : ℕ}
    (hM : ⌊Real.sqrt η * N⌋₊ ≤ N) {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc
        (![z 0 - R - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊, z 1 + R - N] : LatticeSite 2)
        ![z 0 + R + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊, z 1 + R + ⌊Real.sqrt η * N⌋₊ + 1]} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ Icc
        (![z 0 - R - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊, z 1 + R - N] : LatticeSite 2)
        ![z 0 + R + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊, z 1 + R + ⌊Real.sqrt η * N⌋₊ + 1]})
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
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
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω' ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
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
  set M := ⌊Real.sqrt η * N⌋₊ with hMdef
  set K := ⌊η * N⌋₊ with hKdef
  set Tlo : LatticeSite 2 := ![z 0 - R - M - K, z 1 + R - N] with hTlo
  set Thi : LatticeSite 2 := ![z 0 + R + M + K, z 1 + R + M + 1] with hThi
  have hTlo0 : Tlo 0 = z 0 - R - M - K := rfl
  have hTlo1 : Tlo 1 = z 1 + R - N := rfl
  have hThi0 : Thi 0 = z 0 + R + M + K := rfl
  have hThi1 : Thi 1 = z 1 + R + M + 1 := rfl
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
  have hbox : ∀ x : LatticeSite 2, z 0 - R ≤ x 0 → x 0 ≤ z 0 + R → z 1 + R - N ≤ x 1 →
      x 1 ≤ z 1 + R → x ∈ Icc Tlo Thi := by
    intro x h₁ h₂ h₃ h₄
    rw [mem_Icc_two_iff, hTlo0, hTlo1, hThi0, hThi1]
    omega
  -- the hypothesis and the first conclusion transfer between configurations agreeing on the box
  have key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      (∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, v ∈ Icc Tlo Thi) → (e ∈ ω₁ ↔ e ∈ ω₂)) →
      ∀ (c : Bool) {u v : LatticeSite 2} (p : (zdGraph 2).Walk u v), cond c
        (u 1 = z 1 + R - N ∧ v 1 = z 1 + R ∧
          (∀ x ∈ p.support, x ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ p.edges, e ∈ ω₁)
        (u 1 = z 1 + R - N - 1 ∧ v 1 = z 1 + R ∧
          (∀ x ∈ p.support, x ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ p.edges, e ∈ dualConfig ω₁ ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2) ![z 0 + R, z 1 + R]}) →
      cond c
        (u 1 = z 1 + R - N ∧ v 1 = z 1 + R ∧
          (∀ x ∈ p.support, x ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ p.edges, e ∈ ω₂)
        (u 1 = z 1 + R - N - 1 ∧ v 1 = z 1 + R ∧
          (∀ x ∈ p.support, x ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ p.edges, e ∈ dualConfig ω₂ ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2) ![z 0 + R, z 1 + R]}) := by
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
  have hb' : z 0 - R ≤ b' i 0 ∧ b' i 0 ≤ z 0 + R - 1 ∧ b' i 1 = z 1 + R := by
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

/-! ### Transport through automorphisms of `ℤ²` -/

/-- An automorphism of `ℤ²` maps the pairs of a configuration that are edges of `ℤ²` onto the
pairs of the image that are edges of `ℤ²`. -/
theorem image_sym2Map_inter_edgeSet (g : zdGraph 2 ≃g zdGraph 2) (X : Config (LatticeSite 2)) :
    Sym2.map g '' (X ∩ (zdGraph 2).edgeSet) = Sym2.map g '' X ∩ (zdGraph 2).edgeSet := by
  have hE : ∀ e : Sym2 (LatticeSite 2),
      Sym2.map g e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet := by
    intro e
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      exact g.map_adj_iff
  ext e
  constructor
  · rintro ⟨e₀, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨⟨e₀, h₁, rfl⟩, (hE e₀).2 h₂⟩
  · rintro ⟨⟨e₀, h₁, rfl⟩, h₂⟩
    exact ⟨e₀, ⟨h₁, (hE e₀).1 h₂⟩, rfl⟩

/-- **Connections through an automorphism of `ℤ²`.** A connection by the edges of `ℤ²` of the
image of `X` under `g`, inside `T`, between the images of two points gives a connection by the
edges of `X` inside any set containing the preimage of `T`. -/
theorem inter_edgeSet_mem_localConn_of_image (g : zdGraph 2 ≃g zdGraph 2)
    (X : Config (LatticeSite 2)) {S T : Set (LatticeSite 2)} (hST : ∀ v ∈ T, g.symm v ∈ S)
    {x y : LatticeSite 2}
    (h : Sym2.map g '' X ∩ (zdGraph 2).edgeSet ∈ localConn T (g x) (g y)) :
    X ∩ (zdGraph 2).edgeSet ∈ localConn S x y := by
  rw [← image_sym2Map_inter_edgeSet] at h
  exact localConn_of_image g.toEquiv _ hST h

/-! ### The right side -/

/-- **Local separation along the right side, read off the top side.** If the configuration swapped
by `(x, y) ↦ (y, x)` has the separation property of `exists_law_separable_ge_top` at the swapped
centre `zf = (z₁, z₀)`, then the configuration has it along the right side of `B_R(z)`: for the
strip `[z₀ + R - N, z₀ + R] × [z₁ - R + 1, z₁ + R - 1]` crossed from left to right by open
crossings, the faces `[z₀ + R - N - 1, z₀ + R] × [z₁ - R, z₁ + R - 1]` crossed by dual crossings,
the doubled rows `2 y` (open end `(z₀ + R, y)`) and `2 y + 1` (dual end), the corners
`2 (z₁ - R)`, `2 (z₁ + R)`, and fences from the bottom side to the top side of the box
`[z₀ + R, z₀ + R + ⌊√η N⌋] × [y - ⌊η N⌋, y + ⌊η N⌋]` to the right of the end. The swap fixes the
faces (`dualConfig_image_swap`). -/
theorem separable_right_of_top {η : ℝ} {z zf : LatticeSite 2} {N R : ℕ} (hzf0 : zf 0 = z 1)
    (hzf1 : zf 1 = z 0) {ω : Config (LatticeSite 2)}
    (h : Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) '' ω ∈
      {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = zf 1 + R - N ∧ b i 1 = zf 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![zf 0 - R + 1, zf 1 + R - N] : LatticeSite 2)
            ![zf 0 + R - 1, zf 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = zf 1 + R - N - 1 ∧ b i 1 = zf 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![zf 0 - R, zf 1 + R - N - 1] : LatticeSite 2)
            ![zf 0 + R - 1, zf 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![zf 0 - R, zf 1 + R - N] : LatticeSite 2) ![zf 0 + R, zf 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = zf 1 + R - N ∧ b' i 1 = zf 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![zf 0 - R + 1, zf 1 + R - N] : LatticeSite 2)
              ![zf 0 + R - 1, zf 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = zf 1 + R - N - 1 ∧ b' i 1 = zf 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![zf 0 - R, zf 1 + R - N - 1] : LatticeSite 2)
              ![zf 0 + R - 1, zf 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![zf 0 - R, zf 1 + R - N] : LatticeSite 2)
                ![zf 0 + R, zf 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ zf 1 + R) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (zf 0 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (zf 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, zf 1 + R]
              ![b' i 0 + ⌊η * N⌋₊, zf 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = z 0 + R - N ∧ b i 0 = z 0 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = z 0 + R - N - 1 ∧ b i 0 = z 0 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 + R - N ∧ b' i 0 = z 0 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = z 0 + R - N - 1 ∧ b' i 0 = z 0 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * (z 1 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
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
  have hb1 : ∀ i, b'f i 1 = zf 1 + R := fun i => by
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
  · simpa only [hgb1, hzf0] using h5 i
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

/-! ### The bottom side -/

/-- **Local separation along the bottom side, read off the top side.** If the configuration
reflected by `(x, y) ↦ (x, -y)` has the separation property of `exists_law_separable_ge_top` at the
reflected centre `zf = (z₀, -z₁)`, then the configuration has it along the bottom side of `B_R(z)`:
for the strip `[z₀ - R + 1, z₀ + R - 1] × [z₁ - R, z₁ - R + N]` crossed from top to bottom by open
crossings, the faces `[z₀ - R, z₀ + R - 1] × [z₁ - R - 1, z₁ - R + N]` crossed by dual crossings
(from the face row `z₁ - R + N` to the face row `z₁ - R - 1`), the doubled columns of the ends as
on the top side, and fences from the left side to the right side of the box
`[x - ⌊η N⌋, x + ⌊η N⌋] × [y - ⌊√η N⌋, y]` below the end `(x, y)`. The reflection moves faces by
one row (`dualConfig_image_reflect`), so the open and the dual crossings are reflected by
different maps. -/
theorem separable_bottom_of_top {η : ℝ} {z zf : LatticeSite 2} {N R : ℕ} (hzf0 : zf 0 = z 0)
    (hzf1 : zf 1 = -z 1) {ω : Config (LatticeSite 2)}
    (h : Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) '' ω ∈
      {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = zf 1 + R - N ∧ b i 1 = zf 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![zf 0 - R + 1, zf 1 + R - N] : LatticeSite 2)
            ![zf 0 + R - 1, zf 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = zf 1 + R - N - 1 ∧ b i 1 = zf 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![zf 0 - R, zf 1 + R - N - 1] : LatticeSite 2)
            ![zf 0 + R - 1, zf 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![zf 0 - R, zf 1 + R - N] : LatticeSite 2) ![zf 0 + R, zf 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = zf 1 + R - N ∧ b' i 1 = zf 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![zf 0 - R + 1, zf 1 + R - N] : LatticeSite 2)
              ![zf 0 + R - 1, zf 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = zf 1 + R - N - 1 ∧ b' i 1 = zf 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![zf 0 - R, zf 1 + R - N - 1] : LatticeSite 2)
              ![zf 0 + R - 1, zf 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![zf 0 - R, zf 1 + R - N] : LatticeSite 2)
                ![zf 0 + R, zf 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ zf 1 + R) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (zf 0 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (zf 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, zf 1 + R]
              ![b' i 0 + ⌊η * N⌋₊, zf 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = z 1 - R + N ∧ b i 1 = z 1 - R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = z 1 - R + N ∧ b i 1 = z 1 - R - 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = z 1 - R + N ∧ b' i 1 = z 1 - R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = z 1 - R + N ∧ b' i 1 = z 1 - R - 1 ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ b' i 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z 0 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, b' i 1 - ⌊Real.sqrt η * N⌋₊]
              ![b' i 0 + ⌊η * N⌋₊, b' i 1]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨g₁, hg₁⟩ := exists_iso_reflect_one 0
  obtain ⟨g₂, hg₂⟩ := exists_iso_reflect_one (-1)
  obtain ⟨F, hFt, hFf⟩ : ∃ F : Bool → (zdGraph 2 ≃g zdGraph 2), F true = g₁ ∧ F false = g₂ :=
    ⟨fun c => cond c g₁ g₂, rfl, rfl⟩
  -- the two maps in coordinates
  have hFt0 : ∀ v, F true v 0 = v 0 := fun v => by
    rw [hFt, hg₁]
    simp only [Matrix.cons_val_zero]
  have hFt1 : ∀ v, F true v 1 = -v 1 := fun v => by
    rw [hFt, hg₁]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, zero_sub]
  have hFf0 : ∀ v, F false v 0 = v 0 := fun v => by
    rw [hFf, hg₂]
    simp only [Matrix.cons_val_zero]
  have hFf1 : ∀ v, F false v 1 = -1 - v 1 := fun v => by
    rw [hFf, hg₂]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have hSt : ∀ v, (F true).symm v 0 = v 0 ∧ (F true).symm v 1 = -v 1 := fun v => by
    have h₀ := hFt0 ((F true).symm v)
    have h₁ := hFt1 ((F true).symm v)
    rw [RelIso.apply_symm_apply] at h₀ h₁
    omega
  have hSf : ∀ v, (F false).symm v 0 = v 0 ∧ (F false).symm v 1 = -1 - v 1 := fun v => by
    have h₀ := hFf0 ((F false).symm v)
    have h₁ := hFf1 ((F false).symm v)
    rw [RelIso.apply_symm_apply] at h₀ h₁
    omega
  have hfun : (⇑(F true) : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - v 1] := by
    rw [hFt]
    exact funext hg₁
  have hfun' : (⇑(F false) : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - 1 - v 1] := by
    rw [hFf]
    funext v
    rw [hg₂, zero_sub]
  have hdual : dualConfig (Sym2.map (F true) '' ω) = Sym2.map (F false) '' dualConfig ω := by
    rw [hfun, hfun']
    exact dualConfig_image_reflect 0 ω
  have hdE : ∀ e ∈ (zdGraph 2).edgeSet,
      dualEdge (Sym2.map (F true) e) = Sym2.map (F false) (dualEdge e) := fun e he => by
    rw [hfun, hfun']
    exact dualEdge_map_reflect 0 he
  have hE : ∀ e, Sym2.map (F true) e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet :=
    fun e => by
      rw [hfun]
      exact map_reflect_mem_edgeSet_iff 0 e
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
  have hb1 : ∀ i, b'f i 1 = zf 1 + R := fun i =>
    hcond (h1 i) (fun hi => hi.2.1) (fun hi => hi.2.1)
  have hS0 : ∀ c v, (F c).symm v 0 = v 0 := fun c v => by
    cases c
    · exact (hSf v).1
    · exact (hSt v).1
  have hS1 : ∀ c v w, (F c).symm v 1 - (F c).symm w 1 = w 1 - v 1 := fun c v w => by
    cases c
    · have := (hSf v).2
      have := (hSf w).2
      omega
    · have := (hSt v).2
      have := (hSt w).2
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
      · have := (hSt (b'f i)).2
        change (F (σ i)).symm (b'f i) 1 = _
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
      · have := (hSf (b'f i)).2
        change (F (σ i)).symm (b'f i) 1 = _
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
    change (F (σ i)).symm y 1 ≠ (F (σ i)).symm (b'f i) 1
    omega
  · simpa only [hS0] using h4 i k hik
  · simpa only [hS0, hzf0] using h5 i
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
    · change (F (σ i)).symm l 0 = (F (σ i)).symm (b'f i) 0 - _
      rw [hS0, hS0, hl]
    · change (F (σ i)).symm r 0 = (F (σ i)).symm (b'f i) 0 + _
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

/-! ### The left side -/

/-- **Local separation along the left side, read off the top side.** If the configuration turned by
the quarter turn `(x, y) ↦ (y, -x)` has the separation property of `exists_law_separable_ge_top` at
the turned centre `zf = (z₁, -z₀)`, then the configuration has it along the left side of `B_R(z)`:
for the strip `[z₀ - R, z₀ - R + N] × [z₁ - R + 1, z₁ + R - 1]` crossed from right to left by open
crossings, the faces `[z₀ - R - 1, z₀ - R + N] × [z₁ - R, z₁ + R - 1]` crossed by dual crossings
(from the face column `z₀ - R + N` to the face column `z₀ - R - 1`), the doubled rows of the ends
as on the right side, and fences from the bottom side to the top side of the box
`[x - ⌊√η N⌋, x] × [y - ⌊η N⌋, y + ⌊η N⌋]` to the left of the end `(x, y)`. The quarter turn moves
faces by one column, so the open and the dual crossings are turned by different maps. -/
theorem separable_left_of_top {η : ℝ} {z zf : LatticeSite 2} {N R : ℕ} (hzf0 : zf 0 = z 1)
    (hzf1 : zf 1 = -z 0) {ω : Config (LatticeSite 2)}
    (h : Sym2.map (fun v : LatticeSite 2 => ![v 1, 0 - v 0]) '' ω ∈
      {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = zf 1 + R - N ∧ b i 1 = zf 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![zf 0 - R + 1, zf 1 + R - N] : LatticeSite 2)
            ![zf 0 + R - 1, zf 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = zf 1 + R - N - 1 ∧ b i 1 = zf 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![zf 0 - R, zf 1 + R - N - 1] : LatticeSite 2)
            ![zf 0 + R - 1, zf 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![zf 0 - R, zf 1 + R - N] : LatticeSite 2) ![zf 0 + R, zf 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = zf 1 + R - N ∧ b' i 1 = zf 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![zf 0 - R + 1, zf 1 + R - N] : LatticeSite 2)
              ![zf 0 + R - 1, zf 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = zf 1 + R - N - 1 ∧ b' i 1 = zf 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![zf 0 - R, zf 1 + R - N - 1] : LatticeSite 2)
              ![zf 0 + R - 1, zf 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![zf 0 - R, zf 1 + R - N] : LatticeSite 2)
                ![zf 0 + R, zf 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ zf 1 + R) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (zf 0 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (zf 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, zf 1 + R]
              ![b' i 0 + ⌊η * N⌋₊, zf 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R - 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R - 1 ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * (z 1 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
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
  have hb1 : ∀ i, b'f i 1 = zf 1 + R := fun i =>
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
  · simpa only [hS0, hzf0] using h5 i
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

/-! ### The four sides -/

/-- **Local separation on the four sides of `B_R(z)`** (Nolin's Lemma 15 in the geometry of the
arms, `exists_law_separable_ge_arm`, transported to the four sides of a box of radius `R = 2N + 1`
at any centre `z` and read in the coordinates of each side). For every `δ > 0` there are
`0 < η ≤ 1` and `N₀` such that, uniformly over the laws with crossing bounds `c` up to `L`, for
`N₀ ≤ N ≤ L`, each of the four events below has probability at least `1 - δ`: every finite family
of crossings of the strip of height `N` along a side of `B_R(z)`, from its inner side to the side of
`B_R(z)`, open or dual, with crossings of the same colour disjoint, can be replaced by a family with
the same colours
and starting points, with crossings of the same colour disjoint, meeting the side of `B_R(z)` only
at their ends, whose ends are at least `4 √η N` apart in doubled coordinates along the side and at
least `4 √η N` from the doubled corners, each with a fence outside `B_R(z)` joined to it within
distance `⌊√η N⌋` of its end. The strips and the coordinates are those of
`exists_law_separable_ge_top` (top side), `separable_right_of_top`, `separable_bottom_of_top` and
`separable_left_of_top`; the laws of the other three sides are those of the top side for the law
seen through the swap, the reflection and the quarter turn (`CrossingBounds.swap`,
`CrossingBounds.reflect`, `law_comp_sym2Map_apply`). -/
theorem exists_law_separable_ge_sides (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ), R = 2 * N + 1 → N₀ ≤ N →
      (N : ℕ∞) ≤ L →
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
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} ∧
      1 - δ ≤ law q {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 + R - N ∧ b i 0 = z 0 + R ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
              ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 0 = z 0 + R - N - 1 ∧ b i 0 = z 0 + R ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
              ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]})) →
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
        ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 0 = z 0 + R - N ∧ b' i 0 = z 0 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
              ![z 0 + R, z 1 + R - 1]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 0 = z 0 + R - N - 1 ∧ b' i 0 = z 0 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
              ![z 0 + R, z 1 + R - 1]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]})) ∧
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
          (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
            |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * (z 1 - R) : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0, b' i 1 - ⌊η * N⌋₊]
                ![b' i 0 + ⌊Real.sqrt η * N⌋₊, b' i 1 + ⌊η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} ∧
      1 - δ ≤ law q {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = z 1 - R + N ∧ b i 1 = z 1 - R ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
              ![z 0 + R - 1, z 1 - R + N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = z 1 - R + N ∧ b i 1 = z 1 - R - 1 ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
              ![z 0 + R - 1, z 1 - R + N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]})) →
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
        ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = z 1 - R + N ∧ b' i 1 = z 1 - R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
              ![z 0 + R - 1, z 1 - R + N]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = z 1 - R + N ∧ b' i 1 = z 1 - R - 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
              ![z 0 + R - 1, z 1 - R + N]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]})) ∧
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ b' i 1) ∧
          (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z 0 - R) : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, b' i 1 - ⌊Real.sqrt η * N⌋₊]
                ![b' i 0 + ⌊η * N⌋₊, b' i 1]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} ∧
      1 - δ ≤ law q {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
              ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R - 1 ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
              ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]})) →
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
        ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
              ![z 0 - R + N, z 1 + R - 1]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R - 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
              ![z 0 - R + N, z 1 + R - 1]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]})) ∧
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
          (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
            |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * (z 1 - R) : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊Real.sqrt η * N⌋₊, b' i 1 - ⌊η * N⌋₊]
                ![b' i 0, b' i 1 + ⌊η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨η, hη, hη1, N₀, htop⟩ := exists_law_separable_ge_top c hδ
  refine ⟨η, hη, hη1, N₀, fun q L h z N R hR hN hNL =>
    ⟨htop q L h z N R hR hN hNL, ?_, ?_, ?_⟩⟩
  · -- the right side: the law seen through the swap
    obtain ⟨g, hg⟩ := exists_iso_swap
    have hgf : (⇑g.toEquiv : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := funext hg
    have hgs : (⇑g.toEquiv.symm : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := by
      funext v
      apply g.toEquiv.injective
      rw [Equiv.apply_symm_apply, hgf]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact eq_vec_two v
    have h1 := htop _ L h.swap ![z 1, z 0] N R hR hN hNL
    rw [← hgf, law_comp_sym2Map_apply q g.toEquiv, hgs] at h1
    exact h1.trans (measure_mono fun ω hω =>
      separable_right_of_top (z := z) (zf := ![z 1, z 0]) rfl rfl hω)
  · -- the bottom side: the law seen through the reflection
    obtain ⟨g, hg⟩ := exists_iso_reflect_one 0
    have hgf : (⇑g.toEquiv : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - v 1] :=
      funext hg
    have hgs : (⇑g.toEquiv.symm : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - v 1] := by
      funext v
      apply g.toEquiv.injective
      rw [Equiv.apply_symm_apply, hgf]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
      exact eq_vec_two v
    have h1 := htop _ L h.reflect ![z 0, -z 1] N R hR hN hNL
    rw [← hgf, law_comp_sym2Map_apply q g.toEquiv, hgs] at h1
    exact h1.trans (measure_mono fun ω hω =>
      separable_bottom_of_top (z := z) (zf := ![z 0, -z 1]) rfl rfl hω)
  · -- the left side: the law seen through the quarter turn
    obtain ⟨sw, hsw⟩ := exists_iso_swap
    obtain ⟨rf, hrf⟩ := exists_iso_reflect_one 0
    have hgf : (⇑(rf.trans sw).toEquiv : LatticeSite 2 → LatticeSite 2) =
        (fun v : LatticeSite 2 => ![v 1, v 0]) ∘ fun v : LatticeSite 2 => ![v 0, 0 - v 1] := by
      funext v
      change sw (rf v) = _
      rw [Function.comp_apply, hsw, hrf]
    have hgs : (⇑(rf.trans sw).toEquiv.symm : LatticeSite 2 → LatticeSite 2) =
        fun v => ![v 1, 0 - v 0] := by
      funext v
      apply (rf.trans sw).toEquiv.injective
      rw [Equiv.apply_symm_apply, hgf, Function.comp_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
      exact eq_vec_two v
    have h1 := htop _ L h.swap.reflect ![z 1, -z 0] N R hR hN hNL
    have hprof : (fun e => (fun e' => q (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e'))
        (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) =
        fun e => q (Sym2.map (rf.trans sw).toEquiv e) := by
      funext e
      rw [hgf, ← Sym2.map_map]
    rw [hprof, law_comp_sym2Map_apply q (rf.trans sw).toEquiv, hgs] at h1
    exact h1.trans (measure_mono fun ω hω =>
      separable_left_of_top (z := z) (zf := ![z 1, -z 0]) rfl rfl hω)

end PercLib.Models.Planar
