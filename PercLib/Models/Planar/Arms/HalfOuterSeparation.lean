/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, proof of Theorem 11 (separation at the outer
boundary), and Section 4.6 (the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.HalfSeparationSides
public import PercLib.Models.Planar.Arms.OuterSeparation

/-!
# Separation of arms at the outer boundary of a half-annulus

The outer step of Nolin's proof of the separation theorem (Theorem 11) for the arms of a
half-plane (Nolin §4.6), for colour sequences with no two consecutive arms of one colour (`OC`,
`OCO`; the first and the last arm may have one colour, the line separates them). Let the
half-plane `j`-arm event from `B_r(z)` to the boundary of `B_R(z)`, `R = 2N + 1`, `r < N`, occur:
`j` disjoint arms in `{v | z₁ ≤ v₁}`, landing in increasing order on the part of the boundary above
the line (doubled positions in `[6R, 14R]`, `IsArm.landingPos_mem_Icc_of_half`). The arms land on
three sides: the top side and the right and the left **half-sides** above the line.

* On the top side, Lemma 15 is used as in the plane (`exists_reroute_top`, whose new final crossings
  lie in the strip, above the line).
* On the half-sides, the strips stop at the line; an open arm of the half-plane lies in the rows
  `[z₁, z₁ + R - 1]` and a dual arm in the face rows `[z₁, z₁ + R - 1]`, so the strip is read as a
  top-side strip of width `2` with the boxes of `exists_law_separable_ge_top_half`
  (`IsArm.exists_append_eq_right_half`, `IsArm.exists_append_eq_left_half`,
  `exists_reroute_right_half`, `exists_reroute_left_half`). The new landing positions lie in
  `[6R + s, 8R - s]` and `[12R + s, 14R - s]`, away from the two points of the line on the boundary.
* One `η` for the three sides: `exists_law_separable_ge_top_of_le` and
  `exists_law_separable_ge_top_half` hold for every scale parameter from some on.
* **The barrier in the half-plane** (`armsDisjoint_and_strictMono_of_innerPos_eq_half`): in the
  configuration that agrees with `ω` above the line and carries a **virtual arm** straight down
  below `B_r(z)` (`exists_isArm_virtual`), of the colour opposite to the first arm, the arms of the
  half-plane are arms (`IsArm.of_agree_of_le`) and the virtual arm separates the first arm from
  the last one; the sector argument of `ArmsDisjoint.of_innerPos_eq` then works with two separators
  of the other colour for every two arms of one colour, through the order invariance of three arms
  (`sbtw_innerPos_iff_sbtw_landingPos_three`). The same virtual arm gives the monotonicity of the
  half-plane event in the outer radius (`halfArmEventIn_subset_halfArmEventIn_of_le`).

The intersection of the three strip events has probability at least `1 - δ`, is determined by the
edges of the annulus `B_{2R}(z) \ B_N(z)`, and on it the arms can be separated
(`exists_half_separating_event`); with the independence from the half-plane event at radius `N`
this gives the outer step `P(A⁺_J(r, R), not separated) ≤ δ P(A⁺(r, N))`
(`exists_law_halfArmEventIn_diff_separated_le`). The separated half-plane event is written inline:
`ArmsOuterSeparated` together with the half-plane condition, the increasing order and the
separation from the line.

## Main results

* `IsArm.exists_append_eq_right_half`, `IsArm.exists_append_eq_left_half`: final crossings on the
  half-sides.
* `exists_reroute_right_half`, `exists_reroute_left_half`: rerouting on the half-sides.
* `exists_walk_column`, `IsArm.of_agree_of_le`, `IsArm.landingPos_mem_Icc_of_half`,
  `exists_isArm_virtual`: the virtual arm below the line.
* `sbtw_innerPos_iff_sbtw_landingPos_three`, `ArmsDisjoint.pair`: order invariance for three arms.
* `armsDisjoint_and_strictMono_of_innerPos_eq_half`: **the barrier in the half-plane.**
* `halfArmEventIn_subset_halfArmEventIn_of_le`: monotonicity in the outer radius.
* `exists_half_separating_event`: **the half-plane outer step, event form.**
* `exists_law_halfArmEventIn_diff_separated_le`: **the half-plane outer step.**
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ}

/-! ### Final crossings on the half-sides -/

/-- **Dual edges above a row.** The edges crossed by the dual edges of a walk of faces whose
faces lie at height at least `y₀` have both ends at height at least `y₀`. -/
theorem le_of_mem_dualEdge_of_mem_edges {a b : LatticeSite 2} {q : (zdGraph 2).Walk a b}
    {y₀ : ℤ} (hq : ∀ v ∈ q.support, y₀ ≤ v 1) {e₁ : Sym2 (LatticeSite 2)}
    (he₁ : e₁ ∈ (zdGraph 2).edgeSet) (he : dualEdge e₁ ∈ q.edges) {x : LatticeSite 2}
    (hx : x ∈ e₁) : y₀ ≤ x 1 := by
  obtain ⟨u, hu⟩ : ∃ u, u ∈ dualEdge e₁ := ⟨(Quot.out (dualEdge e₁)).1, Sym2.out_fst_mem _⟩
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hu
  rw [hw] at he
  have h₁ := hq u (q.fst_mem_support_of_mem_edges he)
  have h₂ := (mem_Icc_two_iff.1 (mem_Icc_of_mem_dualEdge he₁ hx hu)).2.2.1
  omega

/-- **The final crossing of a half-plane arm landing on the right side.** For an arm of colour `c`
to `B_R(z)` in the half-plane `{v | z₁ ≤ v₁}` ending on the right side, the final crossing of
`IsArm.exists_append_eq_right` lies in the strip of the right half-side, in the sense of
`separable_right_half_of_top` with `A = z₁`, `B = z₁ + R - 1`, `T = z₀ + R`. -/
theorem IsArm.exists_append_eq_right_half {c : Bool} {N R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ)
    (hH : ∀ v ∈ γ.support, z 1 ≤ v 1) (hrN : r + N + 1 < R) (hb : b 0 = z 0 + R) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧ ¬p.Nil ∧
      cond c
        (x 0 = z 0 + R - N ∧ b 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 + R - N - 1 ∧ b 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N - 1, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2)
              ![z 0 + R, z 1 + R - 1 + 1]}) := by
  obtain ⟨x, p, q, hpq, hpne, hq⟩ := h.exists_append_eq_right hrN hb
  have hqH : ∀ v ∈ q.support, z 1 ≤ v 1 := fun v hv => hH v (by
    rw [← hpq, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv)
  refine ⟨x, p, q, hpq, hpne, ?_⟩
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hq
    refine ⟨h₁, h₂, fun v hv => ?_, fun e he => ?_⟩
    · have h₅ := mem_Icc_two_iff.1 (h₃ v hv)
      have h₆ := hqH v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₅ ⊢
      omega
    · obtain ⟨hd, e₁, ⟨he₁, hB⟩, rfl⟩ := h₄ e he
      refine ⟨hd, e₁, ⟨he₁, fun y hy => ?_⟩, rfl⟩
      have h₅ := mem_Icc_two_iff.1 (hB y hy)
      have h₆ := le_of_mem_dualEdge_of_mem_edges hqH he₁ he hy
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₅ ⊢
      omega
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hq
    refine ⟨h₁, h₂, fun v hv => ?_, h₄⟩
    have h₅ := mem_Icc_two_iff.1 (h₃ v hv)
    have h₆ := hqH v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₅ ⊢
    omega

/-- **The final crossing of a half-plane arm landing on the left side.** For an arm of colour `c`
to `B_R(z)` in the half-plane `{v | z₁ ≤ v₁}` ending on the left side, the final crossing of
`IsArm.exists_append_eq_left` lies in the strip of the left half-side, in the sense of
`separable_left_half_of_top` with `A = z₁`, `B = z₁ + R - 1`, `X = z₀ - R`. -/
theorem IsArm.exists_append_eq_left_half {c : Bool} {N R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ)
    (hH : ∀ v ∈ γ.support, z 1 ≤ v 1) (hrN : r + N + 1 < R) (hb : b 0 = z 0 - R - cond c 0 1) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧ ¬p.Nil ∧
      cond c
        (x 0 = z 0 - R + N ∧ b 0 = z 0 - R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 - R + N ∧ b 0 = z 0 - R - 1 ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R - 1, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1] : LatticeSite 2)
              ![z 0 - R + N, z 1 + R - 1 + 1]}) := by
  obtain ⟨x, p, q, hpq, hpne, hq⟩ := h.exists_append_eq_left hrN hb
  have hqH : ∀ v ∈ q.support, z 1 ≤ v 1 := fun v hv => hH v (by
    rw [← hpq, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv)
  refine ⟨x, p, q, hpq, hpne, ?_⟩
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hq
    refine ⟨h₁, h₂, fun v hv => ?_, fun e he => ?_⟩
    · have h₅ := mem_Icc_two_iff.1 (h₃ v hv)
      have h₆ := hqH v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₅ ⊢
      omega
    · obtain ⟨hd, e₁, ⟨he₁, hB⟩, rfl⟩ := h₄ e he
      refine ⟨hd, e₁, ⟨he₁, fun y hy => ?_⟩, rfl⟩
      have h₅ := mem_Icc_two_iff.1 (hB y hy)
      have h₆ := le_of_mem_dualEdge_of_mem_edges hqH he₁ he hy
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₅ ⊢
      omega
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hq
    refine ⟨h₁, h₂, fun v hv => ?_, h₄⟩
    have h₅ := mem_Icc_two_iff.1 (h₃ v hv)
    have h₆ := hqH v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₅ ⊢
    omega

/-! ### Rerouting on the half-sides -/

/-- **Rerouting the half-plane arms landing on the right side.** The analogue of
`exists_reroute_right` for the arms of a half-plane, under the separation property of
`separable_right_half_of_top` on the right half-side (`A = z₁`, `B = z₁ + R - 1`, `T = z₀ + R`):
the arms landing on the right side are replaced by half-plane arms with the same colours, starts and
inner positions, whose landing positions are at least `4 √η N` apart and in
`[6R + 4 √η N, 8R - 4 √η N]` (away from the line, at `6R`, and from the corner, at `8R`), each with
a fence to the right of its end as in `exists_reroute_right`. -/
theorem exists_reroute_right_half {η : ℝ} {N R : ℕ} (hR : R = 2 * N + 1) (hr : r < N)
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = z 0 + R - N ∧ b i 0 = z 0 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = z 0 + R - N - 1 ∧ b i 0 = z 0 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N - 1, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2) ![z 0 + R, z 1 + R - 1 + 1]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 + R - N ∧ b' i 0 = z 0 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = z 0 + R - N - 1 ∧ b' i 0 = z 0 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N - 1, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2)
                ![z 0 + R, z 1 + R - 1 + 1]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * z 1 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 1 + R - 1 + 1) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0, b' i 1 - ⌊η * N⌋₊]
              ![b' i 0 + ⌊Real.sqrt η * N⌋₊, b' i 1 + ⌊η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) :
    ∃ L : Fin j → ℤ,
      (∀ i, b i 0 = z 0 + R → ∃ (b' : LatticeSite 2) (Γ : (zdGraph 2).Walk (a i) b'),
        IsArm ω (σ i) z r (z - R) (z + R) Γ ∧
        innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
        landingPos (z - R) (z + R) (σ i) Γ = L i ∧
        (∀ v ∈ Γ.support, z 1 ≤ v 1) ∧
        ∃ x ∈ Γ.support, ∃ l r' : LatticeSite 2,
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l ∧
          b' 0 = z 0 + R ∧ l 1 = b' 1 - ⌊η * N⌋₊ ∧ r' 1 = b' 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' 0, b' 1 - ⌊η * N⌋₊] ![b' 0 + ⌊Real.sqrt η * N⌋₊, b' 1 + ⌊η * N⌋₊]) l r') ∧
      (∀ i k, b i 0 = z 0 + R → b k 0 = z 0 + R → i ≠ k →
        4 * Real.sqrt η * N ≤ |((L i - L k : ℤ) : ℝ)|) ∧
      (∀ i, b i 0 = z 0 + R →
        6 * (R : ℝ) + 4 * Real.sqrt η * N ≤ L i ∧ (L i : ℝ) + 4 * Real.sqrt η * N ≤ 8 * R) := by
  classical
  have hext : ∀ i, b i 0 = z 0 + R → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x)
      (q : (zdGraph 2).Walk x (b i)), p.append q = γ i ∧ ¬p.Nil ∧
      cond (σ i)
        (x 0 = z 0 + R - N ∧ b i 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 + R - N - 1 ∧ b i 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N - 1, z 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1] : LatticeSite 2) ![z 0 + R, z 1 + R - 1 + 1]}) :=
    fun i hi => (hγ i).exists_append_eq_right_half (hH i) (by omega) hi
  choose x p q hpq hpne hq using hext
  -- the final crossings lie in the arms after their first vertex
  have htail : ∀ i hi, ∀ v ∈ (q i hi).support, v ∈ (γ i).support.tail := by
    intro i hi v hv
    rw [← hpq i hi, SimpleGraph.Walk.tail_support_append, List.mem_append]
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hv with rfl | hv
    · exact Or.inl (SimpleGraph.Walk.end_mem_tail_support (hpne i hi))
    · exact Or.inr hv
  obtain ⟨b'', γ'', H1, -, H3, H4, H5, H6⟩ := hω {i // b i 0 = z 0 + R} (fun i => σ i.1)
    (fun i => x i.1 i.2) (fun i => b i.1) (fun i => q i.1 i.2) (fun i => hq i.1 i.2)
    (fun i k hik hσ v hv hv' => by
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hv₁ := htail i.1 i.2 v hv
      have hv₂ := List.mem_of_mem_tail (htail k.1 k.2 v hv')
      cases h : σ i.1
      · exact hd.2 i.1 k.1 hne h (hσ.symm.trans h) v (List.mem_of_mem_tail hv₁) hv₂
      · exact hd.1 i.1 k.1 hne h (hσ.symm.trans h) v hv₁ hv₂)
  -- the doubled coordinates of the new ends along the side
  set d : {i // b i 0 = z 0 + R} → ℤ := fun i => 2 * b'' i 1 + cond (σ i.1) 0 1
    with hd_def
  refine ⟨fun i => if hi : b i 0 = z 0 + R then 4 * R + d ⟨i, hi⟩ - 2 * (z 1 - R) else 0,
    fun i hi => ?_, fun i k hi hk hik => ?_, fun i hi => ?_⟩
  · have h1 := H1 ⟨i, hi⟩
    have h3 := H3 ⟨i, hi⟩
    obtain ⟨y, hy, l, r', hl, hr', hlr, hyl⟩ := H6 ⟨i, hi⟩
    beta_reduce at h1 h3 hlr hyl
    -- the new final crossing fits the arm
    obtain ⟨hb1, hS, hT, hE⟩ : b'' ⟨i, hi⟩ 0 = z 0 + R ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support, w ∉ cond (σ i) (Icc (z - r) (z + r))
          (Icc (z - r - 1) (z + r))) ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support.dropLast, w ∈ cond (σ i) (Icc (z - R + 1) (z + R - 1))
          (Icc (z - R) (z + R - 1))) ∧
        (∀ e ∈ (γ'' ⟨i, hi⟩).edges, e ∈ cond (σ i) ω (dualConfig ω)) := by
      revert h1
      cases σ i
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, fun e he => (hE e he).1⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply, Pi.one_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, hE⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
    have hb : b'' ⟨i, hi⟩ ∉ cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
      cases σ i
      · intro h
        have := (mem_Icc_two_iff.1 h).2.1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this
        omega
      · intro h
        have := (mem_Icc_two_iff.1 h).2.1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this
        omega
    have hArm : IsArm ω (σ i) z r (z - R) (z + R) ((p i hi).append (γ'' ⟨i, hi⟩)) := by
      have h0 := hγ i
      rw [← hpq i hi] at h0
      exact h0.append_right hS hT hb hE
    refine ⟨b'' ⟨i, hi⟩, (p i hi).append (γ'' ⟨i, hi⟩), hArm, ?_, ?_, ?_, y, ?_, l, r', hyl, hb1,
      hl, hr', hlr⟩
    · rw [innerPos_append _ (hpne i hi)]
      conv_rhs => rw [← hpq i hi]
      rw [innerPos_append _ (hpne i hi)]
    · beta_reduce
      rw [dite_eq_left hi, hArm.landingPos_eq_of_right (by omega) hb1]
    · intro v hv
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv
      · refine hH i v ?_
        rw [← hpq i hi, SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl hv
      · revert h1
        cases σ i <;> rintro ⟨-, -, hS, -⟩ <;> have := mem_Icc_two_iff.1 (hS v hv) <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this <;> omega
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hy
  · have h4 := H4 ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Subtype.val h))
    beta_reduce
    rw [dite_eq_left hi, dite_eq_left hk]
    have : (((4 * R + d ⟨i, hi⟩ - 2 * (z 1 - R)) - (4 * R + d ⟨k, hk⟩ - 2 * (z 1 - R)) : ℤ) : ℝ) =
        ((d ⟨i, hi⟩ : ℤ) : ℝ) - ((d ⟨k, hk⟩ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [this]
    exact h4
  · obtain ⟨h₁, h₂⟩ := H5 ⟨i, hi⟩
    beta_reduce
    rw [dite_eq_left hi]
    change 4 * Real.sqrt η * N ≤ ((d ⟨i, hi⟩ - 2 * z 1 : ℤ) : ℝ) at h₁
    change 4 * Real.sqrt η * N ≤ ((2 * (z 1 + R - 1 + 1) - d ⟨i, hi⟩ : ℤ) : ℝ) at h₂
    push_cast at h₁ h₂ ⊢
    constructor <;> linarith


/-- **Rerouting the half-plane arms landing on the left side.** The analogue of
`exists_reroute_left` for the arms of a half-plane, under the separation property of
`separable_left_half_of_top` on the left half-side (`A = z₁`, `B = z₁ + R - 1`, `X = z₀ - R`):
the landing positions of the new arms are at least `4 √η N` apart and in
`[12R + 4 √η N, 14R - 4 √η N]` (away from the corner, at `12R`, and from the line, at `14R`). -/
theorem exists_reroute_left_half {η : ℝ} {N R : ℕ} (hR : R = 2 * N + 1) (hr : r < N)
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R - 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R - 1, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1] : LatticeSite 2) ![z 0 - R + N, z 1 + R - 1 + 1]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R - 1 ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R - 1, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1] : LatticeSite 2)
                ![z 0 - R + N, z 1 + R - 1 + 1]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * z 1 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 1 + R - 1 + 1) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊Real.sqrt η * N⌋₊, b' i 1 - ⌊η * N⌋₊]
              ![b' i 0, b' i 1 + ⌊η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) :
    ∃ L : Fin j → ℤ,
      (∀ i, b i 0 = z 0 - R - cond (σ i) 0 1 → ∃ (b' : LatticeSite 2)
        (Γ : (zdGraph 2).Walk (a i) b'),
        IsArm ω (σ i) z r (z - R) (z + R) Γ ∧
        innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
        landingPos (z - R) (z + R) (σ i) Γ = L i ∧
        (∀ v ∈ Γ.support, z 1 ≤ v 1) ∧
        ∃ x ∈ Γ.support, ∃ l r' : LatticeSite 2,
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l ∧
          b' 0 = z 0 - R - cond (σ i) 0 1 ∧ l 1 = b' 1 - ⌊η * N⌋₊ ∧ r' 1 = b' 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' 0 - ⌊Real.sqrt η * N⌋₊, b' 1 - ⌊η * N⌋₊] ![b' 0, b' 1 + ⌊η * N⌋₊]) l r') ∧
      (∀ i k, b i 0 = z 0 - R - cond (σ i) 0 1 → b k 0 = z 0 - R - cond (σ k) 0 1 → i ≠ k →
        4 * Real.sqrt η * N ≤ |((L i - L k : ℤ) : ℝ)|) ∧
      (∀ i, b i 0 = z 0 - R - cond (σ i) 0 1 →
        12 * (R : ℝ) + 4 * Real.sqrt η * N ≤ L i ∧ (L i : ℝ) + 4 * Real.sqrt η * N ≤ 14 * R) := by
  classical
  have hext : ∀ i, b i 0 = z 0 - R - cond (σ i) 0 1 → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x)
      (q : (zdGraph 2).Walk x (b i)), p.append q = γ i ∧ ¬p.Nil ∧
      cond (σ i)
        (x 0 = z 0 - R + N ∧ b i 0 = z 0 - R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 - R + N ∧ b i 0 = z 0 - R - 1 ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R - 1, z 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1] : LatticeSite 2) ![z 0 - R + N, z 1 + R - 1 + 1]}) :=
    fun i hi => (hγ i).exists_append_eq_left_half (hH i) (by omega) hi
  choose x p q hpq hpne hq using hext
  -- the final crossings lie in the arms after their first vertex
  have htail : ∀ i hi, ∀ v ∈ (q i hi).support, v ∈ (γ i).support.tail := by
    intro i hi v hv
    rw [← hpq i hi, SimpleGraph.Walk.tail_support_append, List.mem_append]
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hv with rfl | hv
    · exact Or.inl (SimpleGraph.Walk.end_mem_tail_support (hpne i hi))
    · exact Or.inr hv
  obtain ⟨b'', γ'', H1, -, H3, H4, H5, H6⟩ := hω {i // b i 0 = z 0 - R - cond (σ i) 0 1}
    (fun i => σ i.1)
    (fun i => x i.1 i.2) (fun i => b i.1) (fun i => q i.1 i.2) (fun i => hq i.1 i.2)
    (fun i k hik hσ v hv hv' => by
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hv₁ := htail i.1 i.2 v hv
      have hv₂ := List.mem_of_mem_tail (htail k.1 k.2 v hv')
      cases h : σ i.1
      · exact hd.2 i.1 k.1 hne h (hσ.symm.trans h) v (List.mem_of_mem_tail hv₁) hv₂
      · exact hd.1 i.1 k.1 hne h (hσ.symm.trans h) v hv₁ hv₂)
  -- the doubled coordinates of the new ends along the side
  set d : {i // b i 0 = z 0 - R - cond (σ i) 0 1} → ℤ := fun i => 2 * b'' i 1 + cond (σ i.1) 0 1
    with hd_def
  refine ⟨fun i => if hi : b i 0 = z 0 - R - cond (σ i) 0 1 then
      12 * R + 2 * (z 1 + R) - d ⟨i, hi⟩ else 0,
    fun i hi => ?_, fun i k hi hk hik => ?_, fun i hi => ?_⟩
  · have h1 := H1 ⟨i, hi⟩
    have h3 := H3 ⟨i, hi⟩
    obtain ⟨y, hy, l, r', hl, hr', hlr, hyl⟩ := H6 ⟨i, hi⟩
    beta_reduce at h1 h3 hlr hyl
    -- the new final crossing fits the arm
    obtain ⟨hb1, hS, hT, hE⟩ : b'' ⟨i, hi⟩ 0 = z 0 - R - cond (σ i) 0 1 ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support, w ∉ cond (σ i) (Icc (z - r) (z + r))
          (Icc (z - r - 1) (z + r))) ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support.dropLast, w ∈ cond (σ i) (Icc (z - R + 1) (z + R - 1))
          (Icc (z - R) (z + R - 1))) ∧
        (∀ e ∈ (γ'' ⟨i, hi⟩).edges, e ∈ cond (σ i) ω (dualConfig ω)) := by
      revert h1
      cases σ i
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, fun e he => (hE e he).1⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply, Pi.one_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨(by rw [Bool.cond_true, sub_zero]; exact hb1), fun w hw hwB => ?_,
          fun w hw => ?_, hE⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
    have hb : b'' ⟨i, hi⟩ ∉ cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
      revert hb1
      cases σ i
      · intro hb1 h
        have := (mem_Icc_two_iff.1 h).1
        simp only [Pi.sub_apply, Pi.natCast_apply, Bool.cond_false] at this hb1
        omega
      · intro hb1 h
        have := (mem_Icc_two_iff.1 h).1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
          Bool.cond_true] at this hb1
        omega
    have hArm : IsArm ω (σ i) z r (z - R) (z + R) ((p i hi).append (γ'' ⟨i, hi⟩)) := by
      have h0 := hγ i
      rw [← hpq i hi] at h0
      exact h0.append_right hS hT hb hE
    refine ⟨b'' ⟨i, hi⟩, (p i hi).append (γ'' ⟨i, hi⟩), hArm, ?_, ?_, ?_, y, ?_, l, r', hyl, hb1,
      hl, hr', hlr⟩
    · rw [innerPos_append _ (hpne i hi)]
      conv_rhs => rw [← hpq i hi]
      rw [innerPos_append _ (hpne i hi)]
    · beta_reduce
      rw [dite_eq_left hi, hArm.landingPos_eq_of_left (by omega) hb1]
    · intro v hv
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv
      · refine hH i v ?_
        rw [← hpq i hi, SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl hv
      · revert h1
        cases σ i <;> rintro ⟨-, -, hS, -⟩ <;> have := mem_Icc_two_iff.1 (hS v hv) <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this <;> omega
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hy
  · have h4 := H4 ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Subtype.val h))
    beta_reduce
    rw [dite_eq_left hi, dite_eq_left hk]
    have : (((12 * R + 2 * (z 1 + R) - d ⟨i, hi⟩) - (12 * R + 2 * (z 1 + R) - d ⟨k, hk⟩) : ℤ) : ℝ) =
        ((d ⟨k, hk⟩ : ℤ) : ℝ) - ((d ⟨i, hi⟩ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [this, abs_sub_comm]
    exact h4
  · obtain ⟨h₁, h₂⟩ := H5 ⟨i, hi⟩
    beta_reduce
    rw [dite_eq_left hi]
    change 4 * Real.sqrt η * N ≤ ((d ⟨i, hi⟩ - 2 * z 1 : ℤ) : ℝ) at h₁
    change 4 * Real.sqrt η * N ≤ ((2 * (z 1 + R - 1 + 1) - d ⟨i, hi⟩ : ℤ) : ℝ) at h₂
    push_cast at h₁ h₂ ⊢
    constructor <;> linarith


/-! ### The virtual arm below the line -/

/-- A walk down the column `x` from `(x, b)` to `(x, a)`, for `a ≤ b`, through the points `(x, t)`
with `a ≤ t ≤ b` and the vertical edges between them; it leaves its first point at once and
reaches its last point only at the end. -/
theorem exists_walk_column (x : ℤ) {a b : ℤ} (hab : a ≤ b) :
    ∃ p : (zdGraph 2).Walk ![x, b] ![x, a],
      (∀ v ∈ p.support, v 0 = x ∧ a ≤ v 1 ∧ v 1 ≤ b) ∧
      (∀ v ∈ p.support.tail, v 1 < b) ∧ (∀ v ∈ p.support.dropLast, a < v 1) ∧
      ∀ e ∈ p.edges, ∃ t : ℤ, a ≤ t ∧ t + 1 ≤ b ∧ e = s(![x, t], ![x, t + 1]) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b - a = n := ⟨(b - a).toNat, by omega⟩
  induction n generalizing b with
  | zero =>
    obtain rfl : b = a := by push_cast at hn; omega
    refine ⟨.nil, fun v hv => ?_, fun v hv => by simp at hv, fun v hv => by simp at hv,
      fun e he => by simp at he⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    simp
  | succ n ih =>
    obtain ⟨p, hp, hpt, hpd, hpe⟩ := ih (b := b - 1) (by push_cast at hn; omega)
      (by push_cast at hn ⊢; omega)
    have hadj : (zdGraph 2).Adj ![x, b] ![x, b - 1] := by
      rw [zdGraph_two_adj_iff]
      simp
    refine ⟨.cons hadj p, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · refine ⟨by simp, ?_, by simp⟩
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        push_cast at hn
        omega
      · obtain ⟨h1, h2, h3⟩ := hp v hv
        omega
    · rw [SimpleGraph.Walk.support_cons, List.tail_cons] at hv
      have := (hp v hv).2.2
      omega
    · rw [SimpleGraph.Walk.support_cons,
        List.dropLast_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil p),
        List.mem_cons] at hv
      rcases hv with rfl | hv
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        push_cast at hn
        omega
      · exact hpd v hv
    · rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · refine ⟨b - 1, by push_cast at hn; omega, by omega, ?_⟩
        rw [sub_add_cancel, Sym2.eq_swap]
      · obtain ⟨t, ht1, ht2, rfl⟩ := hpe e he
        exact ⟨t, ht1, by omega, rfl⟩

/-- **Arms above a row keep their colour** in every configuration that agrees on the edges above
the row: an arm whose vertices (faces) lie at height at least `y₀` uses only open edges (crosses
only closed edges) with both ends at height at least `y₀`. -/
theorem IsArm.of_agree_of_le {ω' : Config (LatticeSite 2)} {c : Bool} {lo hi a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r lo hi γ) {y₀ : ℤ}
    (hH : ∀ v ∈ γ.support, y₀ ≤ v 1)
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, y₀ ≤ v 1) → (e ∈ ω ↔ e ∈ ω')) :
    IsArm ω' c z r lo hi γ := by
  cases c
  · have h' : IsDualArm ω z r lo hi γ := h
    change IsDualArm ω' z r lo hi γ
    refine ⟨h'.isCrossing, fun E hE => ?_⟩
    have hE' := h'.mem_of_mem_edges E hE
    rw [mem_dualConfig_iff] at hE' ⊢
    have heE : Sym2.map (· + 1) (dualEdge E) ∈ (zdGraph 2).edgeSet :=
      map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hE'.1)
    have hde : dualEdge (Sym2.map (· + 1) (dualEdge E)) = E :=
      congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨E, hE'.1⟩)
    refine ⟨hE'.1, fun h'' => hE'.2 ((hω _ heE fun v hv => ?_).2 h'')⟩
    exact le_of_mem_dualEdge_of_mem_edges hH heE (by rw [hde]; exact hE) hv
  · have h' : IsOpenArm ω z r lo hi γ := h
    change IsOpenArm ω' z r lo hi γ
    exact ⟨h'.isCrossing, fun e he => (hω e (γ.edges_subset_edgeSet he)
      (fun v hv => hH v (SimpleGraph.Walk.mem_support_of_mem_edges he hv))).1
        (h'.mem_of_mem_edges e he)⟩

/-- **Landing positions of half-plane arms.** An arm of `B_R(z)` in the half-plane
`{v | z₁ ≤ v₁}` lands in `[6R, 14R]`: on the part of the boundary above the line, between the
points `(z₀ + R, z₁)` (doubled position `6R`) and `(z₀ - R, z₁)` (doubled position `14R`). -/
theorem IsArm.landingPos_mem_Icc_of_half {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R)
    (hH : ∀ v ∈ γ.support, z 1 ≤ v 1) :
    6 * (R : ℤ) ≤ landingPos (z - R) (z + R) c γ ∧ landingPos (z - R) (z + R) c γ ≤ 14 * R := by
  have hb := hH b γ.end_mem_support
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  rcases h.end_mem_sides hrR with h1 | h1 | h1 | h1
  · rw [h.landingPos_eq_of_top hrR h1]
    cases c <;> simp only [Bool.cond_true, Bool.cond_false] at hp h1 ⊢ <;> omega
  · rw [h.landingPos_eq_of_right hrR h1]
    cases c <;> simp only [Bool.cond_true, Bool.cond_false] at hp h1 ⊢ <;> omega
  · cases c <;> simp only [Bool.cond_true, Bool.cond_false] at h1 <;> omega
  · rw [h.landingPos_eq_of_left hrR h1]
    cases c <;> simp only [Bool.cond_true, Bool.cond_false] at hp h1 ⊢ <;> omega

/-- **The virtual arm below the line.** Let `ω↓` be the configuration that agrees with `ω` on the
edges with both ends at height at least `z₁`, contains for `c = true` the vertical edges of the
column `z₀` below the row `z₁ - r`, and nothing else. Then the column `z₀` below `B_r(z)` carries
an arm of colour `c` of `ω↓` to the boundary of `B_R(z)`, `r < R`: open down the vertices
`(z₀, t)`, `t ≤ z₁ - r`, dual down the faces `(z₀, t)`, `t ≤ z₁ - r - 1`. It lands on the bottom
side at the doubled position `2R + [c = false]`. -/
theorem exists_isArm_virtual (c : Bool) {R : ℕ} (hrR : r < R) (ω : Config (LatticeSite 2)) :
    ∃ (a b : LatticeSite 2) (V : (zdGraph 2).Walk a b),
      IsArm ((ω ∩ {e | ∀ v ∈ e, z 1 ≤ v 1}) ∪
        cond c {e | ∃ t : ℤ, t + 1 ≤ z 1 - r ∧ e = s(![z 0, t], ![z 0, t + 1])} ∅)
        c z r (z - R) (z + R) V ∧
      (∀ v ∈ V.support, v 0 = z 0 ∧ v 1 ≤ z 1 - r - cond c 0 1) ∧
      (∀ v ∈ V.support.tail, v 1 < z 1 - r - cond c 0 1) ∧
      landingPos (z - R) (z + R) c V = 2 * R + cond c 0 1 ∧
      innerPos z r c V = 2 * r + 1 + cond c 0 1 := by
  cases c
  · obtain ⟨p, hp, hpt, hpd, hpe⟩ :=
      exists_walk_column (z 0) (show z 1 - R - 1 ≤ z 1 - r - 1 by omega)
    have hV : IsArm ((ω ∩ {e | ∀ v ∈ e, z 1 ≤ v 1}) ∪ cond false
        {e | ∃ t : ℤ, t + 1 ≤ z 1 - r ∧ e = s(![z 0, t], ![z 0, t + 1])} ∅)
        false z r (z - R) (z + R) p := by
      refine ⟨⟨?_, fun w hw hwS => ?_, fun hb => ?_, fun w hw => ?_⟩, fun E hE => ?_⟩
      · rw [mem_Icc_two_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply]
        omega
      · have h₁ := hpt w hw
        have h₂ := (mem_Icc_two_iff.1 hwS).2.2.1
        simp only [Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h₂
        omega
      · have := (mem_Icc_two_iff.1 hb).2.2.1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply,
          Pi.natCast_apply] at this
        omega
      · have h₁ := hp w (List.dropLast_subset _ hw)
        have h₂ := hpd w hw
        rw [mem_Icc_two_iff]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
        omega
      · obtain ⟨t, ht1, ht2, rfl⟩ := hpe E hE
        have hEe : s(![z 0, t], ![z 0, t + 1]) ∈ (zdGraph 2).edgeSet := p.edges_subset_edgeSet hE
        rw [mem_dualConfig_iff]
        refine ⟨hEe, fun h' => ?_⟩
        have heE : Sym2.map (· + 1) (dualEdge s(![z 0, t], ![z 0, t + 1])) ∈ (zdGraph 2).edgeSet :=
          map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hEe)
        have hde : dualEdge (Sym2.map (· + 1) (dualEdge s(![z 0, t], ![z 0, t + 1]))) =
            s(![z 0, t], ![z 0, t + 1]) :=
          congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨_, hEe⟩)
        obtain ⟨x, hx⟩ : ∃ x, x ∈ Sym2.map (· + 1) (dualEdge s(![z 0, t], ![z 0, t + 1])) :=
          ⟨(Quot.out (Sym2.map (· + 1) (dualEdge s(![z 0, t], ![z 0, t + 1])))).1,
            Sym2.out_fst_mem _⟩
        have hxB := mem_Icc_two_iff.1 (mem_Icc_of_mem_dualEdge heE hx
          (show ![z 0, t] ∈ dualEdge (Sym2.map (· + 1) (dualEdge s(![z 0, t], ![z 0, t + 1]))) by
            rw [hde]; exact Sym2.mem_mk_left _ _))
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply, Pi.one_apply] at hxB
        rcases h' with ⟨-, hup⟩ | h'
        · have := hup x hx
          omega
        · exact h'
    refine ⟨_, _, p, hV, fun v hv => ⟨(hp v hv).1, ?_⟩, fun v hv => ?_, ?_, ?_⟩
    · have := (hp v hv).2.2
      simp only [Bool.cond_false]
      omega
    · have := hpt v hv
      simp only [Bool.cond_false]
      omega
    · rw [hV.landingPos_eq_of_bottom hrR (by simp)]
      simp only [Matrix.cons_val_zero, Bool.cond_false]
      ring
    · rw [innerPos_false]
      unfold perimeterPos
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.ofNat_apply, Nat.cast_ofNat, Bool.cond_false, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      split_ifs <;> omega
  · obtain ⟨p, hp, hpt, hpd, hpe⟩ := exists_walk_column (z 0) (show z 1 - R ≤ z 1 - r by omega)
    have hV : IsArm ((ω ∩ {e | ∀ v ∈ e, z 1 ≤ v 1}) ∪ cond true
        {e | ∃ t : ℤ, t + 1 ≤ z 1 - r ∧ e = s(![z 0, t], ![z 0, t + 1])} ∅)
        true z r (z - R) (z + R) p := by
      refine ⟨⟨?_, fun w hw hwS => ?_, fun hb => ?_, fun w hw => ?_⟩, fun E hE => ?_⟩
      · rw [mem_Icc_two_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply]
        omega
      · have h₁ := hpt w hw
        have h₂ := (mem_Icc_two_iff.1 hwS).2.2.1
        simp only [Pi.sub_apply, Pi.natCast_apply] at h₂
        omega
      · have := (mem_Icc_two_iff.1 hb).2.2.1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at this
        omega
      · have h₁ := hp w (List.dropLast_subset _ hw)
        have h₂ := hpd w hw
        rw [mem_Icc_two_iff]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
        omega
      · obtain ⟨t, ht1, ht2, rfl⟩ := hpe E hE
        exact Or.inr ⟨t, ht2, rfl⟩
    have hne : ¬p.Nil := fun hn => by
      have := congrArg (· 1) hn.eq
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      omega
    have hs := hpt _ (SimpleGraph.Walk.snd_mem_tail_support hne)
    have hs' := hp _ (List.mem_of_mem_tail (SimpleGraph.Walk.snd_mem_tail_support hne))
    have hsa := (zdGraph_two_adj_iff _ _).1 (p.adj_snd hne)
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hsa
    refine ⟨_, _, p, hV, fun v hv => ⟨(hp v hv).1, ?_⟩, fun v hv => ?_, ?_, ?_⟩
    · have := (hp v hv).2.2
      simp only [Bool.cond_true]
      omega
    · have := hpt v hv
      simp only [Bool.cond_true]
      omega
    · rw [hV.landingPos_eq_of_bottom hrR (by simp)]
      simp only [Matrix.cons_val_zero, Bool.cond_true]
      ring
    · rw [innerPos_true]
      unfold perimeterPos
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.ofNat_apply, Nat.cast_ofNat, Bool.cond_true, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      split_ifs <;> omega

/-! ### The barrier in the half-plane -/

/-- **Order invariance for three arms** given one by one (`sbtw_innerPos_iff_sbtw_landingPos` for
the family of the three): if each two arms of one colour are disjoint in the sense of
`ArmsDisjoint` (two open arms share at most their first vertex, two dual arms no face), the inner
positions and the landing positions of the three arms are in the same cyclic order. -/
theorem sbtw_innerPos_iff_sbtw_landingPos_three {lo hi : LatticeSite 2}
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) {c₀ c₁ c₂ : Bool}
    {a₀ b₀ a₁ b₁ a₂ b₂ : LatticeSite 2} {W₀ : (zdGraph 2).Walk a₀ b₀}
    {W₁ : (zdGraph 2).Walk a₁ b₁} {W₂ : (zdGraph 2).Walk a₂ b₂}
    (h₀ : IsArm ω c₀ z r lo hi W₀) (h₁ : IsArm ω c₁ z r lo hi W₁) (h₂ : IsArm ω c₂ z r lo hi W₂)
    (h₀₁ : c₀ = c₁ → (∀ v ∈ cond c₀ W₀.support.tail W₀.support, v ∉ W₁.support) ∧
      ∀ v ∈ cond c₀ W₁.support.tail W₁.support, v ∉ W₀.support)
    (h₀₂ : c₀ = c₂ → (∀ v ∈ cond c₀ W₀.support.tail W₀.support, v ∉ W₂.support) ∧
      ∀ v ∈ cond c₀ W₂.support.tail W₂.support, v ∉ W₀.support)
    (h₁₂ : c₁ = c₂ → (∀ v ∈ cond c₁ W₁.support.tail W₁.support, v ∉ W₂.support) ∧
      ∀ v ∈ cond c₁ W₂.support.tail W₂.support, v ∉ W₁.support) :
    sbtw (innerPos z r c₀ W₀) (innerPos z r c₁ W₁) (innerPos z r c₂ W₂) ↔
      sbtw (landingPos lo hi c₀ W₀) (landingPos lo hi c₁ W₁) (landingPos lo hi c₂ W₂) := by
  let A : Fin 3 → LatticeSite 2 := ![a₀, a₁, a₂]
  let B : Fin 3 → LatticeSite 2 := ![b₀, b₁, b₂]
  let F : ∀ t, (zdGraph 2).Walk (A t) (B t) :=
    @Fin.cases 2 (fun t => (zdGraph 2).Walk (A t) (B t)) W₀
      (@Fin.cases 1 (fun t => (zdGraph 2).Walk (A t.succ) (B t.succ)) W₁
        (@Fin.cases 0 (fun t => (zdGraph 2).Walk (A t.succ.succ) (B t.succ.succ)) W₂
          fun t => t.elim0))
  have hF : ∀ t, IsArm ω (![c₀, c₁, c₂] t) z r lo hi (F t) := by
    intro t
    fin_cases t
    · exact h₀
    · exact h₁
    · exact h₂
  have hdF : ArmsDisjoint ![c₀, c₁, c₂] F := by
    refine ⟨fun t u htu ht hu v hv hv' => ?_, fun t u htu ht hu v hv hv' => ?_⟩
    · fin_cases t <;> fin_cases u
      · exact htu rfl
      · exact (h₀₁ (ht.trans hu.symm)).1 v (by rw [show c₀ = true from ht]; exact hv) hv'
      · exact (h₀₂ (ht.trans hu.symm)).1 v (by rw [show c₀ = true from ht]; exact hv) hv'
      · exact (h₀₁ (hu.trans ht.symm)).2 v (by rw [show c₀ = true from hu]; exact hv) hv'
      · exact htu rfl
      · exact (h₁₂ (ht.trans hu.symm)).1 v (by rw [show c₁ = true from ht]; exact hv) hv'
      · exact (h₀₂ (hu.trans ht.symm)).2 v (by rw [show c₀ = true from hu]; exact hv) hv'
      · exact (h₁₂ (hu.trans ht.symm)).2 v (by rw [show c₁ = true from hu]; exact hv) hv'
      · exact htu rfl
    · fin_cases t <;> fin_cases u
      · exact htu rfl
      · exact (h₀₁ (ht.trans hu.symm)).1 v (by rw [show c₀ = false from ht]; exact hv) hv'
      · exact (h₀₂ (ht.trans hu.symm)).1 v (by rw [show c₀ = false from ht]; exact hv) hv'
      · exact (h₀₁ (hu.trans ht.symm)).2 v (by rw [show c₀ = false from hu]; exact hv) hv'
      · exact htu rfl
      · exact (h₁₂ (ht.trans hu.symm)).1 v (by rw [show c₁ = false from ht]; exact hv) hv'
      · exact (h₀₂ (hu.trans ht.symm)).2 v (by rw [show c₀ = false from hu]; exact hv) hv'
      · exact (h₁₂ (hu.trans ht.symm)).2 v (by rw [show c₁ = false from hu]; exact hv) hv'
      · exact htu rfl
  exact sbtw_innerPos_iff_sbtw_landingPos hB hF hdF 0 1 2

/-- Two arms of one family of one colour are disjoint in the form of
`sbtw_innerPos_iff_sbtw_landingPos_three`. -/
theorem ArmsDisjoint.pair {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hd : ArmsDisjoint σ γ) {i k : Fin j} (hik : i ≠ k)
    (hσ : σ i = σ k) :
    (∀ v ∈ cond (σ i) (γ i).support.tail (γ i).support, v ∉ (γ k).support) ∧
      ∀ v ∈ cond (σ i) (γ k).support.tail (γ k).support, v ∉ (γ i).support := by
  cases h : σ i
  · rw [h] at hσ
    exact ⟨fun v hv => hd.2 i k hik h hσ.symm v hv, fun v hv => hd.2 k i hik.symm hσ.symm h v hv⟩
  · rw [h] at hσ
    exact ⟨fun v hv => hd.1 i k hik h hσ.symm v hv, fun v hv => hd.1 k i hik.symm hσ.symm h v hv⟩

/-- **Barrier in the half-plane.** Let `γ` be a disjoint family of arms of `B_R(z)`, `r < R`, in
the half-plane `{v | z₁ ≤ v₁}`, landing in increasing order, with no two consecutive arms of one
colour (`σ i ≠ σ (i + 1)`; the first and the last arm may have one colour). Then every family `γ'`
of arms in the half-plane with the colours and the inner positions of `γ` is disjoint and lands in
increasing order.

The proof reads the half-plane as a sector of the plane: in the configuration `ω↓` that agrees with
`ω` above the line and has the virtual arm of `exists_isArm_virtual` below it, of the colour
opposite to the first arm, the arms of the half-plane are arms, and the virtual arm, landing at
`2R` or `2R + 1` below all of them, separates the first arm from the last one. Two arms of one
colour of `γ` are separated by two arms of the other colour (their right neighbours, their left
and right neighbours, or the second arm and the virtual arm), and the sector argument of
`ArmsDisjoint.of_innerPos_eq` applies. -/
theorem armsDisjoint_and_strictMono_of_innerPos_eq_half {j : ℕ} {σ : Fin j → Bool}
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {R : ℕ} (hrR : r < R)
    {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1)
    (ho : StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i))
    {a' b' : Fin j → LatticeSite 2} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (hγ' : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ' i))
    (hH' : ∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1)
    (hin : ∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) :
    ArmsDisjoint σ γ' ∧ StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ' i) := by
  classical
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    exact ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) :=
    Icc_subset_Icc_add_one_sub_one hrR
  -- the virtual arm below the line, in the configuration `ω'`
  obtain ⟨cV, hcV⟩ : ∃ cV : Bool, cV = !σ ⟨0, hj⟩ := ⟨_, rfl⟩
  obtain ⟨aV, bV, V, hV, hVs, hVt, hLV, -⟩ := exists_isArm_virtual (z := z) cV hrR ω
  obtain ⟨ω', hω'⟩ : ∃ ω' : Config (LatticeSite 2), ω' = (ω ∩ {e | ∀ v ∈ e, z 1 ≤ v 1}) ∪
      cond cV {e | ∃ t : ℤ, t + 1 ≤ z 1 - r ∧ e = s(![z 0, t], ![z 0, t + 1])} ∅ := ⟨_, rfl⟩
  rw [← hω'] at hV
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, z 1 ≤ v 1) → (e ∈ ω ↔ e ∈ ω') := by
    intro e _ he
    rw [hω']
    refine ⟨fun h => Or.inl ⟨h, he⟩, fun h => ?_⟩
    rcases h with ⟨h, -⟩ | h
    · exact h
    · cases cV
      · exact absurd h (Set.notMem_empty e)
      · obtain ⟨t, ht, rfl⟩ := h
        have := he _ (Sym2.mem_mk_left _ _)
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
        omega
  have hup : ∀ {c : Bool} {x y : LatticeSite 2} {W : (zdGraph 2).Walk x y},
      IsArm ω c z r (z - R) (z + R) W → (∀ v ∈ W.support, z 1 ≤ v 1) →
      IsArm ω' c z r (z - R) (z + R) W := fun h hW => h.of_agree_of_le hW hagree
  -- the virtual arm is disjoint from the arms of the half-plane
  have hVd : ∀ {x y : LatticeSite 2} (W : (zdGraph 2).Walk x y),
      IsArm ω cV z r (z - R) (z + R) W → (∀ v ∈ W.support, z 1 ≤ v 1) →
      (∀ v ∈ cond cV W.support.tail W.support, v ∉ V.support) ∧
        ∀ v ∈ cond cV V.support.tail V.support, v ∉ W.support := by
    intro x y W hW hWH
    cases cV
    · refine ⟨fun v hv hv' => ?_, fun v hv hv' => ?_⟩
      · have h₁ := hWH v hv
        have h₂ := (hVs v hv').2
        simp only [Bool.cond_false] at h₂
        omega
      · have h₁ := hWH v hv'
        have h₂ := (hVs v hv).2
        simp only [Bool.cond_false] at h₂
        omega
    · refine ⟨fun v hv hv' => ?_, fun v hv hv' => ?_⟩
      · have h₁ := hWH v (List.mem_of_mem_tail hv)
        obtain ⟨h₂, h₃⟩ := hVs v hv'
        simp only [Bool.cond_true] at h₃
        have hW' : IsOpenArm ω z r (z - R) (z + R) W := hW
        refine hW'.isCrossing.notMem_of_mem_tail v hv ?_
        rw [mem_Icc_two_iff]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
        omega
      · have h₁ := hWH v hv'
        have h₂ := hVt v hv
        simp only [Bool.cond_true] at h₂
        omega
  have hL := fun i => (hγ i).landingPos_mem_Icc_of_half hrR (hH i)
  have hL' := fun i => (hγ' i).landingPos_mem_Icc_of_half hrR (hH' i)
  have hLV' : landingPos (z - R) (z + R) cV V ≤ 2 * R + 1 := by
    rw [hLV]
    cases cV <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
  -- separators: two disjoint arms of the other colour with `γ i` and `γ i'` on different sides
  have hsep : ∀ i i' : Fin j, i < i' → σ i = σ i' → ∃ cS : Bool, cS ≠ σ i ∧
      ∃ (x₁ y₁ : LatticeSite 2) (S₁ : (zdGraph 2).Walk x₁ y₁) (x₂ y₂ : LatticeSite 2)
        (S₂ : (zdGraph 2).Walk x₂ y₂),
        IsArm ω' cS z r (z - R) (z + R) S₁ ∧ IsArm ω' cS z r (z - R) (z + R) S₂ ∧
        (cS = cS → (∀ v ∈ cond cS S₁.support.tail S₁.support, v ∉ S₂.support) ∧
          ∀ v ∈ cond cS S₂.support.tail S₂.support, v ∉ S₁.support) ∧
        (sbtw (landingPos (z - R) (z + R) (σ i) (γ i)) (landingPos (z - R) (z + R) cS S₁)
            (landingPos (z - R) (z + R) cS S₂) ↔
          ¬sbtw (landingPos (z - R) (z + R) (σ i') (γ i')) (landingPos (z - R) (z + R) cS S₁)
            (landingPos (z - R) (z + R) cS S₂)) := by
    intro i i' hii' hσii'
    have hii'v : i.val < i'.val := hii'
    have hi1 : i.val + 1 < j := by have := i'.2; omega
    obtain ⟨k, hk⟩ : ∃ k : Fin j, k.val = i.val + 1 := ⟨⟨i.val + 1, hi1⟩, rfl⟩
    have hσk : σ k ≠ σ i := (hσ i k hk.symm).symm
    have hki' : k.val < i'.val := by
      rcases Nat.lt_or_ge k.val i'.val with h | h
      · exact h
      · exfalso
        have : k = i' := Fin.ext (by omega)
        exact hσk (by rw [this]; exact hσii'.symm)
    have hik : i < k := by rw [Fin.lt_def]; omega
    have hki'' : k < i' := hki'
    have hLik : landingPos (z - R) (z + R) (σ i) (γ i) <
        landingPos (z - R) (z + R) (σ k) (γ k) := ho hik
    have hLki' : landingPos (z - R) (z + R) (σ k) (γ k) <
        landingPos (z - R) (z + R) (σ i') (γ i') := ho hki''
    by_cases hlast : i'.val + 1 < j
    · obtain ⟨l, hl⟩ : ∃ l : Fin j, l.val = i'.val + 1 := ⟨⟨i'.val + 1, hlast⟩, rfl⟩
      have hσl : σ l ≠ σ i := fun h => hσ i' l hl.symm (hσii'.symm.trans h.symm)
      have hσkl : σ k = σ l := by
        revert hσk hσl
        generalize σ k = x
        generalize σ l = y
        generalize σ i = w
        cases x <;> cases y <;> cases w <;> simp
      have hkl : k ≠ l := fun h => by rw [h] at hk; omega
      have hi'l : i' < l := by rw [Fin.lt_def]; omega
      have hLi'l : landingPos (z - R) (z + R) (σ i') (γ i') <
          landingPos (z - R) (z + R) (σ l) (γ l) := ho hi'l
      refine ⟨σ k, hσk, _, _, γ k, _, _, γ l, hup (hγ k) (hH k), hσkl ▸ hup (hγ l) (hH l),
        fun _ => ?_, ?_⟩
      · have := hd.pair hkl hσkl
        exact this
      · rw [← hσkl] at hLi'l
        rw [Int.sbtw_iff, Int.sbtw_iff]
        omega
    · by_cases hi0 : 0 < i.val
      · obtain ⟨l, hl⟩ : ∃ l : Fin j, l.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
        have hσl : σ l ≠ σ i := hσ l i (by omega)
        have hσkl : σ l = σ k := by
          revert hσk hσl
          generalize σ k = x
          generalize σ l = y
          generalize σ i = w
          cases x <;> cases y <;> cases w <;> simp
        have hkl : l ≠ k := fun h => by rw [h] at hl; omega
        have hli : l < i := by rw [Fin.lt_def]; omega
        have hLli : landingPos (z - R) (z + R) (σ l) (γ l) <
            landingPos (z - R) (z + R) (σ i) (γ i) := ho hli
        refine ⟨σ k, hσk, _, _, γ l, _, _, γ k, hσkl ▸ hup (hγ l) (hH l), hup (hγ k) (hH k),
          fun _ => ?_, ?_⟩
        · have := hd.pair hkl hσkl
          rw [hσkl] at this
          exact this
        · rw [hσkl] at hLli
          rw [Int.sbtw_iff, Int.sbtw_iff]
          omega
      · -- the first and the last arm: the second arm and the virtual arm separate them
        have hi0' : i = ⟨0, hj⟩ := Fin.ext (by simp; omega)
        have hσkV : σ k = cV := by
          rw [hcV, ← hi0']
          revert hσk
          generalize σ k = x
          generalize σ i = w
          cases x <;> cases w <;> simp
        refine ⟨σ k, hσk, _, _, γ k, _, _, V, hup (hγ k) (hH k), hσkV ▸ hV, fun _ => ?_, ?_⟩
        · have := hVd (γ k) (hσkV ▸ hγ k) (hH k)
          rw [hσkV]
          exact ⟨this.1, this.2⟩
        · have hLV'' : landingPos (z - R) (z + R) (σ k) V ≤ 2 * R + 1 := hσkV ▸ hLV'
          have h₁ := (hL i).1
          rw [Int.sbtw_iff, Int.sbtw_iff]
          omega
  -- an arm with the inner position of `γ i` does not land where `γ' i'` lands
  have key : ∀ i i', i ≠ i' → σ i = σ i' → ∀ {x y : LatticeSite 2} (W : (zdGraph 2).Walk x y),
      IsArm ω (σ i) z r (z - R) (z + R) W → (∀ v ∈ W.support, z 1 ≤ v 1) →
      innerPos z r (σ i) W = innerPos z r (σ i) (γ i) →
      landingPos (z - R) (z + R) (σ i) W ≠ landingPos (z - R) (z + R) (σ i') (γ' i') := by
    intro i i' hii' hσii' x y W hW hWH hWin heq
    obtain ⟨cS, hcS, x₁, y₁, S₁, x₂, y₂, S₂, hS₁, hS₂, hS₁₂, hside⟩ : ∃ cS : Bool, cS ≠ σ i ∧
        ∃ (x₁ y₁ : LatticeSite 2) (S₁ : (zdGraph 2).Walk x₁ y₁) (x₂ y₂ : LatticeSite 2)
          (S₂ : (zdGraph 2).Walk x₂ y₂),
          IsArm ω' cS z r (z - R) (z + R) S₁ ∧ IsArm ω' cS z r (z - R) (z + R) S₂ ∧
          (cS = cS → (∀ v ∈ cond cS S₁.support.tail S₁.support, v ∉ S₂.support) ∧
            ∀ v ∈ cond cS S₂.support.tail S₂.support, v ∉ S₁.support) ∧
          (sbtw (landingPos (z - R) (z + R) (σ i) (γ i)) (landingPos (z - R) (z + R) cS S₁)
              (landingPos (z - R) (z + R) cS S₂) ↔
            ¬sbtw (landingPos (z - R) (z + R) (σ i') (γ i')) (landingPos (z - R) (z + R) cS S₁)
              (landingPos (z - R) (z + R) cS S₂)) := by
      rcases lt_or_gt_of_ne hii' with h | h
      · exact hsep i i' h hσii'
      · obtain ⟨cS, hcS, x₁, y₁, S₁, x₂, y₂, S₂, hS₁, hS₂, hS₁₂, hside⟩ :=
          hsep i' i h hσii'.symm
        exact ⟨cS, fun h' => hcS (h'.trans hσii'), x₁, y₁, S₁, x₂, y₂, S₂, hS₁, hS₂, hS₁₂,
          fun hA hB => hside.1 hB hA, fun hnB => Classical.byContradiction fun hA =>
            hnB (hside.2 hA)⟩
    have hcS' : cS ≠ σ i' := fun h => hcS (h.trans hσii'.symm)
    have e₁ := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup hW hWH) hS₁ hS₂
      (fun h => absurd h.symm hcS) (fun h => absurd h.symm hcS) hS₁₂
    have e₂ := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup (hγ i) (hH i)) hS₁ hS₂
      (fun h => absurd h.symm hcS) (fun h => absurd h.symm hcS) hS₁₂
    have e₃ := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup (hγ' i') (hH' i')) hS₁ hS₂
      (fun h => absurd h.symm hcS') (fun h => absurd h.symm hcS') hS₁₂
    have e₄ := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup (hγ i') (hH i')) hS₁ hS₂
      (fun h => absurd h.symm hcS') (fun h => absurd h.symm hcS') hS₁₂
    rw [hWin] at e₁
    rw [hin i'] at e₃
    have hW' := e₁.symm.trans e₂
    have hγ'' := e₃.symm.trans e₄
    rw [heq] at hW'
    have hAB := hW'.symm.trans hγ''
    by_cases hA : sbtw (landingPos (z - R) (z + R) (σ i) (γ i)) (landingPos (z - R) (z + R) cS S₁)
      (landingPos (z - R) (z + R) cS S₂)
    · exact hside.1 hA (hAB.1 hA)
    · exact hA (hside.2 fun hB => hA (hAB.2 hB))
  have hdisj : ArmsDisjoint σ γ' := by
    refine ⟨fun i i' hii' hσi hσi' v hv hv' => ?_, fun i i' hii' hσi hσi' v hv hv' => ?_⟩
    · -- open arms: join `γ' i` up to `v` to `γ' i'` from `v`
      have hσ' : σ i = σ i' := hσi.trans hσi'.symm
      have hvs := List.mem_of_mem_tail hv
      have h₁ := hγ' i
      have h₂ := hγ' i'
      rw [← SimpleGraph.Walk.take_spec (γ' i) hvs] at h₁
      rw [← SimpleGraph.Walk.take_spec (γ' i') hv', ← hσ'] at h₂
      have hW := IsArm.append_of_append h₁ h₂
      have hc : IsOpenArm ω z r (z - R) (z + R) (γ' i) := by
        have := hγ' i
        rw [hσi] at this
        exact this
      have hva : v ≠ a' i := fun h =>
        hc.isCrossing.notMem_of_mem_tail v hv (h ▸ hc.isCrossing.start_mem)
      have hq : ¬((γ' i).takeUntil v hvs).Nil := fun hn => hva hn.eq.symm
      refine key i i' hii' hσ' _ hW ?_ ?_ ?_
      · intro u hu
        rw [SimpleGraph.Walk.mem_support_append_iff] at hu
        rcases hu with hu | hu
        · exact hH' i u ((γ' i).support_takeUntil_subset_support hvs hu)
        · exact hH' i' u ((γ' i').support_dropUntil_subset_support hv' hu)
      · rw [innerPos_append _ hq, ← hin i]
        conv_rhs => rw [← SimpleGraph.Walk.take_spec (γ' i) hvs, innerPos_append _ hq]
      · rw [← hσ', hσi, landingPos_true, landingPos_true]
    · -- dual arms
      have hσ' : σ i = σ i' := hσi.trans hσi'.symm
      have hc : IsDualArm ω z r (z - R) (z + R) (γ' i) := by
        have := hγ' i
        rw [hσi] at this
        exact this
      have hc' : IsDualArm ω z r (z - R) (z + R) (γ' i') := by
        have := hγ' i'
        rw [hσi'] at this
        exact this
      by_cases hvb : v = b' i'
      · have hvb' : v = b' i := hc.isCrossing.eq_end_of_notMem hv
          (by rw [hvb]; exact hc'.isCrossing.end_notMem)
        have hpen := hc.penultimate_eq hc' ((hγ' i).not_nil hB) ((hγ' i').not_nil hB)
          (hvb'.symm.trans hvb)
        refine key i i' hii' hσ' (γ' i) (hγ' i) (hH' i) (hin i) ?_
        rw [← hσ', hσi, landingPos_false, landingPos_false, hpen, ← hvb', hvb]
      · have h₁ := hγ' i
        have h₂ := hγ' i'
        rw [← SimpleGraph.Walk.take_spec (γ' i) hv] at h₁
        rw [← SimpleGraph.Walk.take_spec (γ' i') hv', ← hσ'] at h₂
        have hW := IsArm.append_of_append h₁ h₂
        have hs : ¬((γ' i').dropUntil v hv').Nil := fun hn => hvb hn.eq
        refine key i i' hii' hσ' _ hW ?_ ?_ ?_
        · intro u hu
          rw [SimpleGraph.Walk.mem_support_append_iff] at hu
          rcases hu with hu | hu
          · exact hH' i u ((γ' i).support_takeUntil_subset_support hv hu)
          · exact hH' i' u ((γ' i').support_dropUntil_subset_support hv' hu)
        · rw [← hin i, hσi, innerPos_false, innerPos_false]
        · rw [landingPos_append _ hs, hσ']
          conv_rhs => rw [← SimpleGraph.Walk.take_spec (γ' i') hv', landingPos_append _ hs]
  -- the order, read off the virtual arm
  have hVpair : ∀ {x y : LatticeSite 2} {W : (zdGraph 2).Walk x y} {c : Bool},
      IsArm ω c z r (z - R) (z + R) W → (∀ v ∈ W.support, z 1 ≤ v 1) → c = cV →
      (∀ v ∈ cond c W.support.tail W.support, v ∉ V.support) ∧
        ∀ v ∈ cond c V.support.tail V.support, v ∉ W.support := by
    intro x y W c hW hWH hc
    subst hc
    exact hVd W hW hWH
  refine ⟨hdisj, fun i k hik => ?_⟩
  have hik' : i ≠ k := ne_of_lt hik
  have e' := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup (hγ' i) (hH' i))
    (hup (hγ' k) (hH' k)) hV (fun h => hdisj.pair hik' h) (hVpair (hγ' i) (hH' i))
    (hVpair (hγ' k) (hH' k))
  have e := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup (hγ i) (hH i))
    (hup (hγ k) (hH k)) hV (fun h => hd.pair hik' h) (hVpair (hγ i) (hH i))
    (hVpair (hγ k) (hH k))
  rw [hin i, hin k] at e'
  have hLik : landingPos (z - R) (z + R) (σ i) (γ i) <
      landingPos (z - R) (z + R) (σ k) (γ k) := ho hik
  have h₁ := (hL i).1
  have h₂ := e'.1 (e.2 (by rw [Int.sbtw_iff]; omega))
  rw [Int.sbtw_iff] at h₂
  have h₃ := (hL' i).1
  have h₄ := (hL' k).1
  change landingPos (z - R) (z + R) (σ i) (γ' i) < landingPos (z - R) (z + R) (σ k) (γ' k)
  omega

/-! ### The outer step in the half-plane -/

/-- **Separation of the arms of a half-plane at the outer boundary, event form** (the half-plane
outer step of Nolin's proof of Theorem 11). Let `σ` have no two consecutive arms of one colour
(`σ i ≠ σ (i + 1)`, as for `OC` and `OCO`). For every `δ > 0` there are `0 < η ≤ 1` and `N₀` such
that, uniformly over the laws with crossing bounds `c` up to `L`, for every centre `z`,
`R = 2N + 1` and `N₀ ≤ N ≤ L`, there is an event `G` of probability at least `1 - δ`, determined by
the edges of the annulus `B_{2R}(z) \ B_N(z)`, such that for `r < N` and all windows `J` of inner
positions, on the half-plane `j`-arm event from `B_r(z)` to the boundary of `B_R(z)` with inner
positions in `J` and `G`, the arms can be chosen separated with the same inner positions: a
disjoint family of arms of colours `σ` in the half-plane `{v | z₁ ≤ v₁}`, landing in increasing
order, separated as in `outerSeparatedArmEvent` (`ArmsOuterSeparated` with `s = 4 √η N`,
`M = ⌊√η N⌋`, `K = ⌊η N⌋`), with landing positions in `[6R + s, 14R - s]`, at least `s` from the two
points of the line on the boundary.

`G` is the intersection of the top-side event of Lemma 15 and of the half-side events of
`exists_law_separable_ge_top_half` read on the right and the left half-sides, all with one `η`
(`exists_law_separable_ge_top_of_le`). On it the final crossings of the arms landing on each side
are rerouted (`exists_reroute_top`, `exists_reroute_right_half`, `exists_reroute_left_half`), the
new arms stay in the half-plane, and the barrier of the half-plane
(`armsDisjoint_and_strictMono_of_innerPos_eq_half`) gives the disjointness and the order. -/
theorem exists_half_separating_event {j : ℕ} (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ), R = 2 * N + 1 → N₀ ≤ N →
      (N : ℕ∞) ≤ L → ∃ G : Set (Config (LatticeSite 2)), MeasurableSet G ∧
        (∀ ω ω' : Config (LatticeSite 2), ω ∩ {e | ∀ v ∈ e,
            v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
              Icc (z - (N : LatticeSite 2)) (z + N)} =
          ω' ∩ {e | ∀ v ∈ e,
            v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
              Icc (z - (N : LatticeSite 2)) (z + N)} → (ω ∈ G ↔ ω' ∈ G)) ∧
        1 - δ ≤ law q G ∧ ∀ r < N, ∀ (J : Fin j → Set ℤ),
          ∀ ω ∈ halfArmEventIn σ z r R J (fun _ => univ) ∩ G,
          ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
            (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
            (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
            ArmsOuterSeparated ω σ z R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ γ ∧
            (∀ i, 6 * (R : ℝ) + 4 * Real.sqrt η * N ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
              (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + 4 * Real.sqrt η * N ≤ 14 * R) ∧
            ∀ i, innerPos z r (σ i) (γ i) ∈ J i := by
  classical
  have hδ3 : 0 < δ / 3 := ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩
  obtain ⟨J₁, htop⟩ := exists_law_separable_ge_top_of_le c hδ3
  obtain ⟨J₂, hhalf⟩ := exists_law_separable_ge_top_half c hδ3
  set J := max J₁ J₂ with hJdef
  set η : ℝ := (1 / ((16 * 8 ^ J : ℕ) : ℝ)) ^ 2 with hηdef
  have hD1 : (1 : ℝ) ≤ ((16 * 8 ^ J : ℕ) : ℝ) := by
    have : 1 ≤ 16 * 8 ^ J := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hη1 : η ≤ 1 := by
    have h₁ : 1 / ((16 * 8 ^ J : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hD1
    have h₂ : (0 : ℝ) ≤ 1 / ((16 * 8 ^ J : ℕ) : ℝ) := by positivity
    calc η ≤ 1 ^ 2 := pow_le_pow_left₀ h₂ h₁ 2
      _ = 1 := one_pow 2
  refine ⟨η, by positivity, hη1, (16 * 8 ^ J) ^ 2 + 4, fun q L h z N R hR hN hNL => ?_⟩
  have hM : ⌊Real.sqrt η * N⌋₊ ≤ N := by
    refine Nat.floor_le_of_le ?_
    have h₁ : Real.sqrt η ≤ 1 := Real.sqrt_le_one.2 hη1
    have h₂ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hK : ⌊η * N⌋₊ ≤ N := by
    refine Nat.floor_le_of_le ?_
    have h₂ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  -- the maps to the frames of the right and left half-sides
  obtain ⟨gs, hgs⟩ := exists_iso_swap
  obtain ⟨gr, hgr⟩ := exists_iso_reflect_one 0
  obtain ⟨σr, hσr⟩ : ∃ e : LatticeSite 2 ≃ LatticeSite 2, ⇑e = fun v => ![v 1, v 0] :=
    ⟨gs.toEquiv, funext hgs⟩
  obtain ⟨σl, hσl⟩ : ∃ e : LatticeSite 2 ≃ LatticeSite 2, ⇑e = fun v => ![v 1, 0 - v 0] := by
    refine ⟨(gs.trans gr).toEquiv, funext fun v => ?_⟩
    change gr (gs v) = _
    rw [hgr, hgs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hσr' : ∀ v, σr.symm v = ![v 1, v 0] := fun v => by
    apply σr.injective
    rw [Equiv.apply_symm_apply, hσr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact eq_vec_two v
  have hσl' : ∀ v, σl.symm v = ![0 - v 1, v 0] := fun v => by
    apply σl.injective
    rw [Equiv.apply_symm_apply, hσl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
    exact eq_vec_two v
  -- the top-side event at `z` and the half-side event in the frames, with their boxes
  let E : LatticeSite 2 → Set (Config (LatticeSite 2)) := fun z' =>
    {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, cond (σ i)
      (a i 1 = z' 1 + R - N ∧ b i 1 = z' 1 + R ∧
        (∀ x ∈ (γ i).support, x ∈ Icc (![z' 0 - R + 1, z' 1 + R - N] : LatticeSite 2)
          ![z' 0 + R - 1, z' 1 + R]) ∧
        ∀ e ∈ (γ i).edges, e ∈ ω)
      (a i 1 = z' 1 + R - N - 1 ∧ b i 1 = z' 1 + R ∧
        (∀ x ∈ (γ i).support, x ∈ Icc (![z' 0 - R, z' 1 + R - N - 1] : LatticeSite 2)
          ![z' 0 + R - 1, z' 1 + R]) ∧
        ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
          ∀ x ∈ e, x ∈ Icc (![z' 0 - R, z' 1 + R - N] : LatticeSite 2) ![z' 0 + R, z' 1 + R]})) →
    (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
    ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, cond (σ i)
        (a i 1 = z' 1 + R - N ∧ b' i 1 = z' 1 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z' 0 - R + 1, z' 1 + R - N] : LatticeSite 2)
            ![z' 0 + R - 1, z' 1 + R]) ∧
          ∀ e ∈ (γ' i).edges, e ∈ ω)
        (a i 1 = z' 1 + R - N - 1 ∧ b' i 1 = z' 1 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z' 0 - R, z' 1 + R - N - 1] : LatticeSite 2)
            ![z' 0 + R - 1, z' 1 + R]) ∧
          ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z' 0 - R, z' 1 + R - N] : LatticeSite 2)
              ![z' 0 + R, z' 1 + R]})) ∧
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
      (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ z' 1 + R) ∧
      (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
        |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
      (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z' 0 - R) : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ ((2 * (z' 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
      ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
        l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b' i 0 - ⌊η * N⌋₊, z' 1 + R]
            ![b' i 0 + ⌊η * N⌋₊, z' 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
            (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}
  let H : ℤ → Set (Config (LatticeSite 2)) := fun T =>
    {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, cond (σ i)
            (a i 1 = T - N ∧ b i 1 = T ∧
              (∀ x ∈ (γ i).support, x ∈ Icc (![z 1, T - N] : LatticeSite 2)
                ![z 1 + R - 1, T]) ∧
              ∀ e ∈ (γ i).edges, e ∈ ω)
            (a i 1 = T - N - 1 ∧ b i 1 = T ∧
              (∀ x ∈ (γ i).support, x ∈ Icc (![z 1, T - N - 1] : LatticeSite 2)
                ![z 1 + R - 1, T]) ∧
              ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (![z 1, T - N] : LatticeSite 2) ![z 1 + R - 1 + 1, T]})) →
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
          ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
            (∀ i, cond (σ i)
              (a i 1 = T - N ∧ b' i 1 = T ∧
                (∀ x ∈ (γ' i).support, x ∈ Icc (![z 1, T - N] : LatticeSite 2)
                  ![z 1 + R - 1, T]) ∧
                ∀ e ∈ (γ' i).edges, e ∈ ω)
              (a i 1 = T - N - 1 ∧ b' i 1 = T ∧
                (∀ x ∈ (γ' i).support, x ∈ Icc (![z 1, T - N - 1] : LatticeSite 2)
                  ![z 1 + R - 1, T]) ∧
                ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                  ∀ x ∈ e, x ∈ Icc (![z 1, T - N] : LatticeSite 2)
                    ![z 1 + R - 1 + 1, T]})) ∧
            (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
            (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ T) ∧
            (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
              |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
            (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * z 1 : ℤ) : ℝ) ∧
              4 * Real.sqrt η * N ≤
                ((2 * (z 1 + R - 1 + 1) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
            ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
              l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
              cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
                (Icc ![b' i 0 - ⌊η * N⌋₊, T]
                  ![b' i 0 + ⌊η * N⌋₊, T + ⌊Real.sqrt η * N⌋₊]) l r ∧
              cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
                (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                  (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}
  set M := ⌊Real.sqrt η * N⌋₊ with hMdef
  set K := ⌊η * N⌋₊ with hKdef
  have hEW : ∀ ω ω' : Config (LatticeSite 2), ω ∩ {e | ∀ v ∈ e, v ∈ Icc
      (![z 0 - R - M - K, z 1 + R - N] : LatticeSite 2) ![z 0 + R + M + K, z 1 + R + M + 1]} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ Icc
      (![z 0 - R - M - K, z 1 + R - N] : LatticeSite 2) ![z 0 + R + M + K, z 1 + R + M + 1]} →
      (ω ∈ E z ↔ ω' ∈ E z) := fun ω ω' hωω' =>
    ⟨fun h' => mem_separable_top_of_inter_eq hM hωω' h',
      fun h' => mem_separable_top_of_inter_eq hM hωω'.symm h'⟩
  have hHW : ∀ (T : ℤ) (ω ω' : Config (LatticeSite 2)), ω ∩ {e | ∀ v ∈ e, v ∈ Icc
      (![z 1 - M - K, T - N] : LatticeSite 2) ![z 1 + R - 1 + 1 + M + K, T + M + 1]} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ Icc
      (![z 1 - M - K, T - N] : LatticeSite 2) ![z 1 + R - 1 + 1 + M + K, T + M + 1]} →
      (ω ∈ H T ↔ ω' ∈ H T) := fun T ω ω' hωω' =>
    ⟨fun h' => mem_separable_top_half_of_inter_eq hM hωω' h',
      fun h' => mem_separable_top_half_of_inter_eq hM hωω'.symm h'⟩
  -- frame events: determined and measurable
  have hframe : ∀ (τ : LatticeSite 2 ≃ LatticeSite 2) (S : Set (Config (LatticeSite 2)))
      (lo hi : LatticeSite 2),
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo hi} =
        ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo hi} → (ω ∈ S ↔ ω' ∈ S)) →
      MeasurableSet {ω | Sym2.map τ '' ω ∈ S} ∧
      ∀ ω ω' : Config (LatticeSite 2),
        ω ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} =
          ω' ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} →
        (ω ∈ {ω | Sym2.map τ '' ω ∈ S} ↔ ω' ∈ {ω | Sym2.map τ '' ω ∈ S}) := by
    intro τ S lo hi hSW
    have hdet : ∀ ω ω' : Config (LatticeSite 2),
        ω ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} =
          ω' ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} →
        (ω ∈ {ω | Sym2.map τ '' ω ∈ S} ↔ ω' ∈ {ω | Sym2.map τ '' ω ∈ S}) :=
      fun ω ω' hωω' => image_sym2Map_mem_iff_of_inter_eq τ hSW hωω'
    refine ⟨measurableSet_of_determined_finite
      ((finite_setOf_forall_mem (Set.finite_Icc lo hi)).image (Sym2.map τ.symm)) fun ω =>
        hdet ω (ω ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi}) ?_, hdet⟩
    rw [inter_assoc, inter_self]
  -- the frame events are determined by the edges of the annulus `B_{2R}(z) \ B_N(z)`
  set Q : Set (Sym2 (LatticeSite 2)) := {e | ∀ v ∈ e,
      v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
        Icc (z - (N : LatticeSite 2)) (z + N)} with hQ
  have hsubQ : ∀ (τ : LatticeSite 2 ≃ LatticeSite 2) (lo hi : LatticeSite 2),
      (∀ u ∈ Icc lo hi,
        τ.symm u ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
          Icc (z - (N : LatticeSite 2)) (z + N)) →
      ∀ ω ω' : Config (LatticeSite 2), ω ∩ Q = ω' ∩ Q →
        ω ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} =
          ω' ∩ Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} := by
    intro τ lo hi hτ ω ω' hωω'
    have hsub : Sym2.map τ.symm '' {e | ∀ v ∈ e, v ∈ Icc lo hi} ⊆ Q := by
      rintro _ ⟨e', he', rfl⟩ v hv
      obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.1 hv
      exact hτ u (he' u hu)
    ext e
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨((Set.ext_iff.1 hωω' e).1 ⟨h₁, hsub h₂⟩).1, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨((Set.ext_iff.1 hωω' e).2 ⟨h₁, hsub h₂⟩).1, h₂⟩
  have hτid : ∀ v, (Equiv.refl (LatticeSite 2)).symm v = v := fun v => rfl
  have hQt := hsubQ (Equiv.refl _) (![z 0 - R - M - K, z 1 + R - N] : LatticeSite 2)
    ![z 0 + R + M + K, z 1 + R + M + 1] fun u hu => by
    rw [hτid]
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hQr := hsubQ σr (![z 1 - M - K, z 0 + R - N] : LatticeSite 2)
    ![z 1 + R - 1 + 1 + M + K, z 0 + R + M + 1] fun u hu => by
    rw [hσr']
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hQl := hsubQ σl (![z 1 - M - K, -(z 0 - R) - N] : LatticeSite 2)
    ![z 1 + R - 1 + 1 + M + K, -(z 0 - R) + M + 1] fun u hu => by
    rw [hσl']
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hFt : {ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} = E z := by
    ext ω
    rw [mem_ofPred_eq, image_sym2Map_refl]
  -- the laws of the three events
  have hlawt : 1 - δ / 3 ≤ law q {ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} := by
    rw [hFt]
    exact htop J (le_max_left _ _) η rfl q L h z N R hR (by omega) hNL
  have hlawr : 1 - δ / 3 ≤ law q {ω | Sym2.map σr '' ω ∈ H (z 0 + R)} := by
    have h1 := hhalf J (le_max_right _ _) η rfl _ L h.swap (z 1) (z 1 + R - 1) (z 0 + R) N
      (by omega) (by omega) hNL
    rw [show (fun v : LatticeSite 2 => ![v 1, v 0]) = ⇑σr.symm from (funext hσr').symm,
      law_comp_sym2Map_apply] at h1
    exact h1
  have hlawl : 1 - δ / 3 ≤ law q {ω | Sym2.map σl '' ω ∈ H (-(z 0 - R))} := by
    have h1 := hhalf J (le_max_right _ _) η rfl _ L h.swap.reflect (z 1) (z 1 + R - 1)
      (-(z 0 - R)) N (by omega) (by omega) hNL
    have hprof : (fun e => (fun e' => q (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e'))
        (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) =
        fun e => q (Sym2.map σl.symm e) := by
      funext e
      beta_reduce
      rw [Sym2.map_map]
      congr 2
      funext v
      rw [Function.comp_apply, hσl']
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hprof, law_comp_sym2Map_apply] at h1
    exact h1
  have hft := hframe (Equiv.refl _) (E z) _ _ hEW
  have hfr := hframe σr (H (z 0 + R)) _ _ (hHW (z 0 + R))
  have hfl := hframe σl (H (-(z 0 - R))) _ _ (hHW (-(z 0 - R)))
  have hcompl : ∀ (S : Set (Config (LatticeSite 2))), MeasurableSet S → 1 - δ / 3 ≤ law q S →
      law q Sᶜ ≤ δ / 3 := by
    intro S hS hlaw
    rw [prob_compl_eq_one_sub hS, tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.1 hlaw
  refine ⟨{ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} ∩
      {ω | Sym2.map σr '' ω ∈ H (z 0 + R)} ∩ {ω | Sym2.map σl '' ω ∈ H (-(z 0 - R))},
    (hft.1.inter hfr.1).inter hfl.1, fun ω ω' hωω' => ?_, ?_, fun r hr J ω hω => ?_⟩
  · simp only [mem_inter_iff]
    rw [hft.2 ω ω' (hQt ω ω' hωω'), hfr.2 ω ω' (hQr ω ω' hωω'), hfl.2 ω ω' (hQl ω ω' hωω')]
  · have hGm := (hft.1.inter hfr.1).inter hfl.1
    have hGc : law q ({ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} ∩
        {ω | Sym2.map σr '' ω ∈ H (z 0 + R)} ∩ {ω | Sym2.map σl '' ω ∈ H (-(z 0 - R))})ᶜ ≤ δ := by
      rw [compl_inter, compl_inter]
      calc _ ≤ δ / 3 + δ / 3 + δ / 3 :=
            (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
              (add_le_add (hcompl _ hft.1 hlawt) (hcompl _ hfr.1 hlawr))) (hcompl _ hfl.1 hlawl))
        _ = 3 * (δ / 3) := by ring
        _ ≤ δ := ENNReal.mul_div_le
    rw [prob_compl_eq_one_sub hGm] at hGc
    rw [tsub_le_iff_right] at hGc ⊢
    calc 1 ≤ δ + law q _ := hGc
      _ = law q _ + δ := add_comm _ _
  obtain ⟨hA, ⟨hFt', hFr⟩, hFl⟩ := hω
  -- the three side events
  have hEt : ω ∈ E z := by rw [← hFt]; exact hFt'
  have hEr := separable_right_half_of_top (A := z 1) (B := z 1 + R - 1) (T := z 0 + R) (N := N)
    (η := η) (by rw [← hσr]; exact hFr)
  have hEl := separable_left_half_of_top (A := z 1) (B := z 1 + R - 1) (T := -(z 0 - R))
    (X := z 0 - R) (N := N) (η := η) rfl (by rw [← hσl]; exact hFl)
  obtain ⟨a, b, γ, hγ, hd, hH, hJI, ho⟩ := hA
  obtain ⟨Lt, ht1, ht2, ht3⟩ := exists_reroute_top hR hr hEt hγ hd
  obtain ⟨Lr, hr1, hr2, hr3⟩ := exists_reroute_right_half hR hr hEr hγ hd hH
  obtain ⟨Ll, hl1, hl2, hl3⟩ := exists_reroute_left_half hR hr hEl hγ hd hH
  -- the side of each arm, its index `n i` (right `1`, top `2`, left `3`) and the new landing
  -- positions
  obtain ⟨n, hn⟩ : ∃ n : Fin j → ℕ, ∀ i, n i = if b i 1 = z 1 + R then 2 else
      if b i 0 = z 0 + R then 1 else 3 := ⟨_, fun _ => rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Fin j → ℤ, ∀ i, Λ i = if b i 1 = z 1 + R then Lt i else
      if b i 0 = z 0 + R then Lr i else Ll i := ⟨_, fun _ => rfl⟩
  have hcase : ∀ i, (b i 1 = z 1 + R ∧ n i = 2 ∧ Λ i = Lt i) ∨
      (b i 0 = z 0 + R ∧ n i = 1 ∧ Λ i = Lr i) ∨
      (b i 0 = z 0 - R - cond (σ i) 0 1 ∧ n i = 3 ∧ Λ i = Ll i) := by
    intro i
    by_cases h1 : b i 1 = z 1 + R
    · exact Or.inl ⟨h1, by rw [hn, ite_eq_left h1], by rw [hΛ, ite_eq_left h1]⟩
    by_cases h2 : b i 0 = z 0 + R
    · exact Or.inr (Or.inl ⟨h2, by rw [hn, ite_eq_right h1, ite_eq_left h2],
        by rw [hΛ, ite_eq_right h1, ite_eq_left h2]⟩)
    have h4 : b i 0 = z 0 - R - cond (σ i) 0 1 := by
      have hbH := hH i (b i) (γ i).end_mem_support
      rcases (hγ i).end_mem_sides (by omega) with h' | h' | h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
      · exfalso
        have hc01 : (0 : ℤ) ≤ cond (σ i) 0 1 := by cases σ i <;> decide
        omega
      · exact h'
    exact Or.inr (Or.inr ⟨h4, by rw [hn, ite_eq_right h1, ite_eq_right h2],
      by rw [hΛ, ite_eq_right h1, ite_eq_right h2]⟩)
  -- the new arms
  have hnew : ∀ i, ∃ (b' : LatticeSite 2) (Γ : (zdGraph 2).Walk (a i) b'),
      IsArm ω (σ i) z r (z - R) (z + R) Γ ∧ innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
      landingPos (z - R) (z + R) (σ i) Γ = Λ i ∧ (∀ v ∈ Γ.support, z 1 ≤ v 1) ∧
      HasOuterFence ω (σ i) z R ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ := by
    intro i
    rcases hcase i with ⟨h1, -, hΛi⟩ | ⟨h1, -, hΛi⟩ | ⟨h1, -, hΛi⟩
    · obtain ⟨b', Γ, hΓ, hin, hL, hloc, x, hx, l, r', hxl, hfen⟩ := ht1 i h1
      refine ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, fun v hv => ?_, x, hx, l, r', hxl, Or.inl hfen⟩
      rcases hloc v hv with hv | hv
      · exact hH i v hv
      · omega
    · obtain ⟨b', Γ, hΓ, hin, hL, hloc, x, hx, l, r', hxl, hfen⟩ := hr1 i h1
      exact ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, hloc, x, hx, l, r', hxl, Or.inr (Or.inl hfen)⟩
    · obtain ⟨b', Γ, hΓ, hin, hL, hloc, x, hx, l, r', hxl, hfen⟩ := hl1 i h1
      exact ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, hloc, x, hx, l, r', hxl,
        Or.inr (Or.inr (Or.inr hfen))⟩
  choose b' Γ hΓ hin hL hΓH hfen using hnew
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  -- the new landing positions lie in the intervals of their sides, away from the line
  have hrange : ∀ i, 4 * (n i : ℝ) * R + 4 * Real.sqrt η * N ≤ Λ i ∧
      (Λ i : ℝ) + 4 * Real.sqrt η * N ≤ 4 * ((n i : ℝ) + 1) * R ∧
      6 * (R : ℝ) + 4 * Real.sqrt η * N ≤ Λ i ∧ (Λ i : ℝ) + 4 * Real.sqrt η * N ≤ 14 * R := by
    intro i
    rcases hcase i with ⟨h1, hni, hΛi⟩ | ⟨h1, hni, hΛi⟩ | ⟨h1, hni, hΛi⟩
    · obtain ⟨h₁, h₂⟩ := ht3 i h1
      rw [hni, hΛi]
      push_cast
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨h₁, h₂⟩ := hr3 i h1
      rw [hni, hΛi]
      push_cast
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨h₁, h₂⟩ := hl3 i h1
      rw [hni, hΛi]
      push_cast
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hsame : ∀ i k, i ≠ k → n i = n k → 4 * Real.sqrt η * N ≤ |((Λ i - Λ k : ℤ) : ℝ)| := by
    intro i k hik hnik
    rcases hcase i with ⟨hi1, hni, hΛi⟩ | ⟨hi1, hni, hΛi⟩ | ⟨hi1, hni, hΛi⟩ <;>
      rcases hcase k with ⟨hk1, hnk, hΛk⟩ | ⟨hk1, hnk, hΛk⟩ | ⟨hk1, hnk, hΛk⟩ <;>
      rw [hΛi, hΛk] <;>
      first
        | (exfalso; omega)
        | exact ht2 i k hi1 hk1 hik
        | exact hr2 i k hi1 hk1 hik
        | exact hl2 i k hi1 hk1 hik
  have hsep : ∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤ |((Λ i - Λ k : ℤ) : ℝ)| := by
    intro i k hik
    obtain ⟨hi₁, hi₂, -, -⟩ := hrange i
    obtain ⟨hk₁, hk₂, -, -⟩ := hrange k
    rcases Nat.lt_trichotomy (n i) (n k) with hnik | hnik | hnik
    · have h' : (n i : ℝ) + 1 ≤ n k := by exact_mod_cast hnik
      have h'' := mul_le_mul_of_nonneg_right h' hR0
      have hs : 0 ≤ 4 * Real.sqrt η * N := by positivity
      push_cast
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      linarith
    · exact hsame i k hik hnik
    · have h' : (n k : ℝ) + 1 ≤ n i := by exact_mod_cast hnik
      have h'' := mul_le_mul_of_nonneg_right h' hR0
      have hs : 0 ≤ 4 * Real.sqrt η * N := by positivity
      refine le_trans ?_ (le_abs_self _)
      push_cast
      linarith
  have hcorner : ∀ i (m : ℕ), 4 * Real.sqrt η * N ≤ |((Λ i - 4 * m * R : ℤ) : ℝ)| := by
    intro i m
    obtain ⟨hi₁, hi₂, -, -⟩ := hrange i
    rcases le_or_gt m (n i) with hm | hm
    · have h' : (m : ℝ) ≤ n i := by exact_mod_cast hm
      refine le_trans ?_ (le_abs_self _)
      push_cast
      nlinarith
    · have h' : (n i : ℝ) + 1 ≤ m := by exact_mod_cast hm
      refine le_trans ?_ (neg_le_abs _)
      push_cast
      nlinarith
  obtain ⟨hd', ho'⟩ := armsDisjoint_and_strictMono_of_innerPos_eq_half hσ (by omega : r < R) hγ hd
    hH ho hΓ hΓH hin
  refine ⟨a, b', Γ, hΓ, hd', hΓH, ho', ⟨fun i k hik => ?_, fun i m => ?_, hfen⟩, fun i => ?_,
    fun i => ?_⟩
  · rw [hL i, hL k]
    exact hsep i k hik
  · rw [hL i]
    exact hcorner i m
  · rw [hL i]
    exact ⟨(hrange i).2.2.1, (hrange i).2.2.2⟩
  · rw [hin i]
    exact (hJI i).1

/-- **Monotonicity in the outer radius, in the half-plane.** For `r < N ≤ R`, `j` disjoint arms of
colours `σ` in the half-plane `{v | z₁ ≤ v₁}` from `B_r(z)` to the boundary of `B_R(z)`, with inner
positions in `J` and landing in increasing order, give such arms to the boundary of `B_N(z)`: their
first parts, up to the first exit from the interior of `B_N(z)`. The order is read off a virtual
dual arm below the line (`exists_isArm_virtual`), which has the same inner position for both
radii. -/
theorem halfArmEventIn_subset_halfArmEventIn_of_le {j : ℕ} {σ : Fin j → Bool}
    {J : Fin j → Set ℤ} {N R : ℕ} (hrN : r < N) (hNR : N ≤ R) :
    halfArmEventIn σ z r R J (fun _ => univ) ⊆ halfArmEventIn σ z r N J (fun _ => univ) := by
  rintro ω ⟨a, b, γ, hγ, hd, hH, hw, ho⟩
  have hrR : r < R := by omega
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - N + 1) (z + N - 1) :=
    Icc_subset_Icc_add_one_sub_one hrN
  have hB₀ : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) :=
    Icc_subset_Icc_add_one_sub_one hrR
  choose x q s hqs hq using fun i => (hγ i).exists_append_eq_of_le_of_le
    (lo' := z - N) (hi' := z + N)
    (fun t => by simp only [Pi.sub_apply, Pi.natCast_apply]; omega)
    (fun t => by simp only [Pi.add_apply, Pi.natCast_apply]; omega)
  have hinner : ∀ i, innerPos z r (σ i) (q i) = innerPos z r (σ i) (γ i) := fun i => by
    rw [← hqs i, innerPos_append _ ((hq i).not_nil hB)]
  have hd' : ArmsDisjoint σ q := hd.mono (fun i v hv => by
      rw [← hqs i, SimpleGraph.Walk.support_append]
      exact List.mem_append_left _ hv) fun i v hv => by
      rw [← hqs i, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hv
  have hH' : ∀ i, ∀ v ∈ (q i).support, z 1 ≤ v 1 := fun i v hv => hH i v (by
    rw [← hqs i, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hv)
  refine ⟨a, x, q, hq, hd', hH', fun i => ⟨by rw [hinner]; exact (hw i).1, mem_univ _⟩,
    fun i k hik => ?_⟩
  -- the order, read off a virtual dual arm below the line
  obtain ⟨_, _, VN, hVN, hVNs, -, hLVN, hinVN⟩ := exists_isArm_virtual (z := z) false hrN ω
  obtain ⟨_, _, VR, hVR, hVRs, -, hLVR, hinVR⟩ := exists_isArm_virtual (z := z) false hrR ω
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, z 1 ≤ v 1) →
      (e ∈ ω ↔ e ∈ (ω ∩ {e | ∀ v ∈ e, z 1 ≤ v 1}) ∪ cond false
        {e | ∃ t : ℤ, t + 1 ≤ z 1 - r ∧ e = s(![z 0, t], ![z 0, t + 1])} ∅) := by
    intro e _ he
    refine ⟨fun h => Or.inl ⟨h, he⟩, fun h => ?_⟩
    rcases h with ⟨h, -⟩ | h
    · exact h
    · exact absurd h (Set.notMem_empty e)
  have hVd : ∀ {x y u w : LatticeSite 2} (W : (zdGraph 2).Walk x y) (V : (zdGraph 2).Walk u w)
      {c : Bool}, (∀ v ∈ W.support, z 1 ≤ v 1) →
      (∀ v ∈ V.support, v 0 = z 0 ∧ v 1 ≤ z 1 - r - cond false 0 1) → c = false →
      (∀ v ∈ cond c W.support.tail W.support, v ∉ V.support) ∧
        ∀ v ∈ cond c V.support.tail V.support, v ∉ W.support := by
    intro x y u w W V c hW hV hc
    subst hc
    refine ⟨fun v hv hv' => ?_, fun v hv hv' => ?_⟩
    · have h₁ := hW v hv
      have h₂ := (hV v hv').2
      simp only [Bool.cond_false] at h₂
      omega
    · have h₁ := hW v hv'
      have h₂ := (hV v hv).2
      simp only [Bool.cond_false] at h₂
      omega
  have hik' : i ≠ k := ne_of_lt hik
  have eN := sbtw_innerPos_iff_sbtw_landingPos_three hB ((hq i).of_agree_of_le (hH' i) hagree)
    ((hq k).of_agree_of_le (hH' k) hagree) hVN (fun h => hd'.pair hik' h)
    (fun h => hVd (q i) VN (hH' i) hVNs h) (fun h => hVd (q k) VN (hH' k) hVNs h)
  have eR := sbtw_innerPos_iff_sbtw_landingPos_three hB₀ ((hγ i).of_agree_of_le (hH i) hagree)
    ((hγ k).of_agree_of_le (hH k) hagree) hVR (fun h => hd.pair hik' h)
    (fun h => hVd (γ i) VR (hH i) hVRs h) (fun h => hVd (γ k) VR (hH k) hVRs h)
  rw [hinner i, hinner k, hinVN] at eN
  rw [hinVR] at eR
  have hLik : landingPos (z - R) (z + R) (σ i) (γ i) <
      landingPos (z - R) (z + R) (σ k) (γ k) := ho hik
  have h₁ := ((hγ i).landingPos_mem_Icc_of_half hrR (hH i)).1
  have h₂ := eN.1 (eR.2 (by
    rw [Int.sbtw_iff, hLVR]
    simp only [Bool.cond_false]
    omega))
  rw [Int.sbtw_iff, hLVN] at h₂
  simp only [Bool.cond_false] at h₂
  have h₃ := ((hq i).landingPos_mem_Icc_of_half hrN (hH' i)).1
  have h₄ := ((hq k).landingPos_mem_Icc_of_half hrN (hH' k)).1
  change landingPos (z - N) (z + N) (σ i) (q i) < landingPos (z - N) (z + N) (σ k) (q k)
  omega

/-- **Separation of the arms of a half-plane at the outer boundary** (the half-plane outer step,
probability form). Under the hypotheses of `exists_half_separating_event`, for `r < N` and any
windows `J` of inner positions: the probability that the half-plane `j`-arm event from `B_r(z)` to
the boundary of `B_R(z)`, `R = 2N + 1`, with inner positions in `J` occurs but no family with inner
positions in `J` can be chosen separated (with the parameters of `exists_half_separating_event`,
away from the line) is at most `δ` times the probability of the half-plane `j`-arm event from
`B_r(z)` to the boundary of `B_N(z)`. -/
theorem exists_law_halfArmEventIn_diff_separated_le {j : ℕ} (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N R : ℕ) (J : Fin j → Set ℤ),
      R = 2 * N + 1 → N₀ ≤ N → r < N → (N : ℕ∞) ≤ L →
      law q (halfArmEventIn σ z r R J (fun _ => univ) \
          {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
            (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
            (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
            (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
            ArmsOuterSeparated ω σ z R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ γ ∧
            (∀ i, 6 * (R : ℝ) + 4 * Real.sqrt η * N ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
              (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + 4 * Real.sqrt η * N ≤ 14 * R) ∧
            ∀ i, innerPos z r (σ i) (γ i) ∈ J i}) ≤
        δ * law q (halfArmEvent σ z r N) := by
  obtain ⟨η, hη, hη1, N₀, hG⟩ := exists_half_separating_event σ hσ c hδ
  refine ⟨η, hη, hη1, N₀, fun q L h z r N R J hR hN hr hNL => ?_⟩
  obtain ⟨G, hGm, hGd, hGl, hGsep⟩ := hG q L h z N R hR hN hNL
  have hAm : MeasurableSet (halfArmEvent σ z r N) := measurableSet_halfArmEvent σ z r N
  have hPQ : Disjoint
      {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ Icc (z - (N : LatticeSite 2)) (z + N)}
      {e | ∀ v ∈ e,
        v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
          Icc (z - (N : LatticeSite 2)) (z + N)} :=
    Set.disjoint_left.2 fun e heP heQ =>
      (heQ _ (Sym2.out_fst_mem e)).2 (heP _ (Sym2.out_fst_mem e))
  have hmem : ∀ {ω ω' : Config (LatticeSite 2)} {S : Set (Sym2 (LatticeSite 2))},
      ω ∩ S = ω' ∩ S → ∀ e ∈ S, (e ∈ ω ↔ e ∈ ω') := fun h e he => by
    have := congrArg (e ∈ ·) h
    simp only [mem_inter_iff, eq_iff_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
  have hind : law q (halfArmEvent σ z r N ∩ Gᶜ) = law q (halfArmEvent σ z r N) * law q Gᶜ :=
    PercLib.Probability.prodBernoulli_inter_of_determined q hPQ hAm hGm.compl
      (fun ω ω' hωω' => mem_halfArmEventTo_iff_of_agree fun e _ h₁ _ => hmem hωω' e h₁)
      fun ω ω' hωω' => not_congr (hGd ω ω' hωω')
  have hGc : law q Gᶜ ≤ δ := by
    rw [prob_compl_eq_one_sub hGm, tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.1 hGl
  calc _ ≤ law q (halfArmEvent σ z r N ∩ Gᶜ) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨hA, hnot⟩ := hω
        exact ⟨halfArmEventIn_subset_halfArmEvent (halfArmEventIn_subset_halfArmEventIn_of_le hr
          (by omega) hA), fun hωG => hnot (hGsep r hr J ω ⟨hA, hωG⟩)⟩
    _ = law q (halfArmEvent σ z r N) * law q Gᶜ := hind
    _ ≤ law q (halfArmEvent σ z r N) * δ := by gcongr
    _ = δ * law q (halfArmEvent σ z r N) := mul_comm _ _

end PercLib.Models.Planar
