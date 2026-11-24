/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12).
-/
module

public import PercLib.Models.Planar.Arms.JogCorridors

/-!
# Turn corridors and wide caps

Corridors that continue an arm separated at the outer boundary of `B_R(z)` to the boundary of
`B_{R'}(z)` and give it a new outer fence there of **any** length `2K'` (with `W + K' ≤ M'`), not
only of length at most the width of the corridor as in `JogCorridors.lean`. Two kinds:

* **Jogs with wide caps.** Out from the bin of the arm (`V₁`), along the side by a shift `d`
  (`H`), out again up to `∂B_{R'}(z)` (`V₂`), and the cap of `JogCorridors.lean` with a fence box
  wider than the corridor.
* **Turns** at the four corners, counterclockwise: from the right side to the top side, from the
  top side to the left side, from the left side to the bottom side, from the bottom side to the
  right side. Out from the bin (`V₁`), along a band at level `h` to the far boundary of
  `B_{R'}(z)` (`H`), and the cap of the next side on that band. The new end lies on the next side
  of `B_{R'}(z)`, at distance about `R' - h` from the corner.

Both consist of a leg of two crossings out of the old fence (`exists_walk_leg2_top` and the three
other sides) and a cap (`exists_walk_cap_top` and the three other sides, from
`JogCorridors.lean`, whose fence size is free).

## Main results

* `exists_walk_leg2_top`, `exists_walk_leg2_bottom`, `exists_walk_leg2_right`,
  `exists_walk_leg2_left`: from a fenced arm through two crossings.
* `exists_walk_jogCap_top` (and the three other sides): jogs with wide caps.
* `exists_walk_turn_right_top`, `exists_walk_turn_top_left`, `exists_walk_turn_left_bottom`,
  `exists_walk_turn_bottom_right`: the four counterclockwise turns.
* `exists_corridor_of_boxes`: six crossings in a region form a corridor event (measurable,
  determined by the boxes, monotone in the colour, probability at least `c κ ^ 6`).
* `exists_corridor_jogCap_top` (and the three other sides), `exists_corridor_turn_top_left` (and
  the three other corners): the corridor of one arm, inside a given rectangle `Icc gl gh`, in the
  form used by the gluing over disjoint regions (`RotationGluing.lean`).

## Implementation notes

The rows (columns) of the level `h` and of the band do not depend on the colour; only the rows
(columns) touching the old side or the new side carry the shift `δ = cond col 0 1` of a dual arm
on the bottom (left) side.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Legs of two crossings -/

section Legs

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R M K W : ℕ}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **A leg of two crossings on the top side.** An arm ending at `b` on the top side of `B_R(z)`,
in the columns `[x, x + W]`, at least `2M` from the corners, with an outer fence of length
`2K ≥ 2W` and depth `M`, is continued, on the crossings of `V₁ = [x, x + W] × [z₁ + R, z₁ + h + W]`
(bottom to top) and `H = [xl, xr] × [z₁ + h, z₁ + h + W]` (left to right, `xl ≤ x`,
`x + W ≤ xr`), by a walk of its colour from one of its vertices (faces) within `M` of `b`, through
the box of radius `M` about `b` and `V₁`, to a vertex of the crossing walk of `H`. -/
theorem exists_walk_leg2_top (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    {h x xl xr : ℤ} (hxl : xl ≤ x) (hxr : x + W ≤ xr) (hh : (R : ℤ) + M ≤ h) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 + R] ![x + W, z 1 + h + W])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![xl, z 1 + h] ![xr, z 1 + h + W])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₂ d₂ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₂ : (zdGraph 2).Walk c₂ d₂),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ w 0 ∧ w 0 ≤ x + W ∧ z 1 + R ≤ w 1 ∧ w 1 ≤ z 1 + h + W)) ∧
      (∀ w ∈ p₂.support, xl ≤ w 0 ∧ w 0 ≤ xr ∧ z 1 + h ≤ w 1 ∧ w 1 ≤ z 1 + h + W) ∧
      c₂ 0 = xl ∧ d₂ 0 = xr ∧ t ∈ p₂.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 1 = z 1 + R ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1] ![b 0 + K, b 1 + M]) u v := by
    rcases hfen with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exfalso; omega
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the two crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hV₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hH
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂
  have Cg₀ : ∀ w ∈ g₀.support, b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M ∧ b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 0 - K ≤ w 0 ∧ w 0 ≤ b 0 + K ∧ b 1 ≤ w 1 ∧ w 1 ≤ b 1 + M :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, x ≤ w 0 ∧ w 0 ≤ x + W ∧ z 1 + R ≤ w 1 ∧ w 1 ≤ z 1 + h + W :=
    fun w hw => by
      have := hp₁ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₂ : ∀ w ∈ p₂.support, xl ≤ w 0 ∧ w 0 ≤ xr ∧ z 1 + h ≤ w 1 ∧ w 1 ≤ z 1 + h + W :=
    fun w hw => by
      have := hp₂ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f p₁ (x₀ := x)
    (x₁ := x + W) (y₀ := b 1) (y₁ := b 1 + M) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₁ (x₀ := x)
    (x₁ := x + W) (y₀ := z 1 + h) (y₁ := z 1 + h + W) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  refine ⟨x₀, w₂, c₂, d₂, Q₂, p₂, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₂e, hp₂e, ?_, C₂, hc₂, hd₂,
    hw₂p₂⟩
  intro w hw
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  rcases hQ₂s w hw with hw | hw
  · rcases hQ₁s w hw with hw | hw
    · have := Cg₀ w hw
      exact Or.inl (by omega)
    · have := Cf w hw
      exact Or.inl (by omega)
  · exact Or.inr (C₁ w hw)

/-- **A leg of two crossings on the bottom side**: `exists_walk_leg2_top` reflected; the arm ends
on the row `z₁ - R - δ` (`δ = cond col 0 1`), `V₁ = [x, x + W] × [z₁ - h - W, z₁ - R - δ]` and
`H = [xl, xr] × [z₁ - h - W, z₁ - h]`. -/
theorem exists_walk_leg2_bottom (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    {h x xl xr : ℤ} (hxl : xl ≤ x) (hxr : x + W ≤ xr) (hh : (R : ℤ) + M + 1 ≤ h)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 - h - W]
      ![x + W, z 1 - R - cond col 0 1])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![xl, z 1 - h - W] ![xr, z 1 - h])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₂ d₂ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₂ : (zdGraph 2).Walk c₂ d₂),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ w 0 ∧ w 0 ≤ x + W ∧ z 1 - h - W ≤ w 1 ∧ w 1 ≤ z 1 - R - cond col 0 1)) ∧
      (∀ w ∈ p₂.support, xl ≤ w 0 ∧ w 0 ≤ xr ∧ z 1 - h - W ≤ w 1 ∧ w 1 ≤ z 1 - h) ∧
      c₂ 0 = xl ∧ d₂ 0 = xr ∧ t ∈ p₂.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 1 = z 1 - R - cond col 0 1 ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1 - M] ![b 0 + K, b 1]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩
    · exfalso; omega
    · exfalso; omega
    · exact h
    · exfalso; omega
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the two crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hV₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hH
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂
  have Cg₀ : ∀ w ∈ g₀.support, b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M ∧ b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 0 - K ≤ w 0 ∧ w 0 ≤ b 0 + K ∧ b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, x ≤ w 0 ∧ w 0 ≤ x + W ∧ z 1 - h - W ≤ w 1 ∧
      w 1 ≤ z 1 - R - cond col 0 1 := fun w hw => by
    have := hp₁ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have C₂ : ∀ w ∈ p₂.support, xl ≤ w 0 ∧ w 0 ≤ xr ∧ z 1 - h - W ≤ w 1 ∧ w 1 ≤ z 1 - h :=
    fun w hw => by
      have := hp₂ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f p₁ (x₀ := x)
    (x₁ := x + W) (y₀ := b 1 - M) (y₁ := b 1) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₁ (x₀ := x)
    (x₁ := x + W) (y₀ := z 1 - h - W) (y₁ := z 1 - h) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  refine ⟨x₀, w₂, c₂, d₂, Q₂, p₂, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₂e, hp₂e, ?_, C₂, hc₂, hd₂,
    hw₂p₂⟩
  intro w hw
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  rcases hQ₂s w hw with hw | hw
  · rcases hQ₁s w hw with hw | hw
    · have := Cg₀ w hw
      exact Or.inl (by omega)
    · have := Cf w hw
      exact Or.inl (by omega)
  · exact Or.inr (C₁ w hw)

/-- **A leg of two crossings on the right side**: `exists_walk_leg2_top` with the coordinates
exchanged; `H₁ = [z₀ + R, z₀ + h + W] × [y, y + W]` (left to right) and
`V = [z₀ + h, z₀ + h + W] × [yl, yr]` (bottom to top). -/
theorem exists_walk_leg2_right (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    {h y yl yr : ℤ} (hyl : yl ≤ y) (hyr : y + W ≤ yr) (hh : (R : ℤ) + M ≤ h) (hMR : M ≤ R)
    (hH₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, y] ![z 0 + h + W, y + W])
    (hV : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + h, yl] ![z 0 + h + W, yr])
    (hb₀ : b 0 = z 0 + R) (hb₁ : y ≤ b 1) (hb₁' : b 1 ≤ y + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₂ d₂ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₂ : (zdGraph 2).Walk c₂ d₂),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (y ≤ w 1 ∧ w 1 ≤ y + W ∧ z 0 + R ≤ w 0 ∧ w 0 ≤ z 0 + h + W)) ∧
      (∀ w ∈ p₂.support, yl ≤ w 1 ∧ w 1 ≤ yr ∧ z 0 + h ≤ w 0 ∧ w 0 ≤ z 0 + h + W) ∧
      c₂ 1 = yl ∧ d₂ 1 = yr ∧ t ∈ p₂.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 0 = z 0 + R ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0, b 1 - K] ![b 0 + M, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso; omega
    · exact h
    all_goals exfalso; omega
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the two crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hH₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hV
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂
  have Cg₀ : ∀ w ∈ g₀.support, b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M ∧ b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 1 - K ≤ w 1 ∧ w 1 ≤ b 1 + K ∧ b 0 ≤ w 0 ∧ w 0 ≤ b 0 + M :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, y ≤ w 1 ∧ w 1 ≤ y + W ∧ z 0 + R ≤ w 0 ∧ w 0 ≤ z 0 + h + W :=
    fun w hw => by
      have := hp₁ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₂ : ∀ w ∈ p₂.support, yl ≤ w 1 ∧ w 1 ≤ yr ∧ z 0 + h ≤ w 0 ∧ w 0 ≤ z 0 + h + W :=
    fun w hw => by
      have := hp₂ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f p₁ (x₀ := y)
    (x₁ := y + W) (y₀ := b 0) (y₁ := b 0 + M) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₁ (x₀ := y)
    (x₁ := y + W) (y₀ := z 0 + h) (y₁ := z 0 + h + W) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  refine ⟨x₀, w₂, c₂, d₂, Q₂, p₂, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₂e, hp₂e, ?_, C₂, hc₂, hd₂,
    hw₂p₂⟩
  intro w hw
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  rcases hQ₂s w hw with hw | hw
  · rcases hQ₁s w hw with hw | hw
    · have := Cg₀ w hw
      exact Or.inl (by omega)
    · have := Cf w hw
      exact Or.inl (by omega)
  · exact Or.inr (C₁ w hw)

/-- **A leg of two crossings on the left side**: `exists_walk_leg2_bottom` with the coordinates
exchanged; the arm ends on the column `z₀ - R - δ`, `H₁ = [z₀ - h - W, z₀ - R - δ] × [y, y + W]`
and `V = [z₀ - h - W, z₀ - h] × [yl, yr]`. -/
theorem exists_walk_leg2_left (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    {h y yl yr : ℤ} (hyl : yl ≤ y) (hyr : y + W ≤ yr) (hh : (R : ℤ) + M + 1 ≤ h)
    (hH₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W, y]
      ![z 0 - R - cond col 0 1, y + W])
    (hV : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - h - W, yl] ![z 0 - h, yr])
    (hb₀ : b 0 = z 0 - R - cond col 0 1) (hb₁ : y ≤ b 1) (hb₁' : b 1 ≤ y + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₂ d₂ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₂ : (zdGraph 2).Walk c₂ d₂),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (y ≤ w 1 ∧ w 1 ≤ y + W ∧ z 0 - h - W ≤ w 0 ∧ w 0 ≤ z 0 - R - cond col 0 1)) ∧
      (∀ w ∈ p₂.support, yl ≤ w 1 ∧ w 1 ≤ yr ∧ z 0 - h - W ≤ w 0 ∧ w 0 ≤ z 0 - h) ∧
      c₂ 1 = yl ∧ d₂ 1 = yr ∧ t ∈ p₂.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 0 = z 0 - R - cond col 0 1 ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - M, b 1 - K] ![b 0, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact h
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the two crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hH₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hV
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂
  have Cg₀ : ∀ w ∈ g₀.support, b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M ∧ b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 1 - K ≤ w 1 ∧ w 1 ≤ b 1 + K ∧ b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, y ≤ w 1 ∧ w 1 ≤ y + W ∧ z 0 - h - W ≤ w 0 ∧
      w 0 ≤ z 0 - R - cond col 0 1 := fun w hw => by
    have := hp₁ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have C₂ : ∀ w ∈ p₂.support, yl ≤ w 1 ∧ w 1 ≤ yr ∧ z 0 - h - W ≤ w 0 ∧ w 0 ≤ z 0 - h :=
    fun w hw => by
      have := hp₂ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f p₁ (x₀ := y)
    (x₁ := y + W) (y₀ := b 0 - M) (y₁ := b 0) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₁ (x₀ := y)
    (x₁ := y + W) (y₀ := z 0 - h - W) (y₁ := z 0 - h) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  refine ⟨x₀, w₂, c₂, d₂, Q₂, p₂, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₂e, hp₂e, ?_, C₂, hc₂, hd₂,
    hw₂p₂⟩
  intro w hw
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  rcases hQ₂s w hw with hw | hw
  · rcases hQ₁s w hw with hw | hw
    · have := Cg₀ w hw
      exact Or.inl (by omega)
    · have := Cf w hw
      exact Or.inl (by omega)
  · exact Or.inr (C₁ w hw)

end Legs

/-! ### Turns at the four corners -/

section Turns

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R R' M K M' K' W : ℕ}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **The turn from the top side to the left side** (counterclockwise, at the top-left corner).
An arm ending at `b` on the top side of `B_R(z)`, in the columns `[x, x + W]`, with an outer fence
`(M, K)`, `W ≤ K`, is continued on the crossings of `V₁ = [x, x + W] × [z₁ + R, z₁ + h + W]`, of
the band `H = [z₀ - R' + 1 - δ, x + W] × [z₁ + h, z₁ + h + W]` and of the left cap
(`exists_walk_cap_left`) on the rows `[z₁ + h, z₁ + h + W]`, to the first point `y` outside the
interior of `B_{R'}(z)`; `y` lies on the left side of `B_{R'}(z)` in those rows and has an outer
fence `(M', K')`, for any `K'` with `W + K' ≤ M'`. -/
theorem exists_walk_turn_top_left (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 + R] ![x + W, z 1 + h + W])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' + 1 - cond col 0 1, z 1 + h]
      ![x + W, z 1 + h + W])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - R' + 1 - cond col 0 1, z 1 + h]
      ![z 0 - R' + M' - cond col 0 1, z 1 + h + W])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' - M' - cond col 0 1, z 1 + h]
      ![z 0 - R' + M' - cond col 0 1, z 1 + h + W])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - R' - M' - cond col 0 1, z 1 + h - K']
      ![z 0 - R' - 1 - cond col 0 1, z 1 + h + W + K'])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W) ∨
        (z 0 - R' - M' - 1 ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + h + W)) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 - R' - cond col 0 1 ∧ z 1 + h ≤ y 1 ∧ y 1 ≤ z 1 + h + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_top hM hWK hKM hW (h := h) (x := x) (xl := z 0 - R' + 1 - cond col 0 1)
      (xr := x + W) (by omega) le_rfl (by omega) hMR hV₁ hH hb₁ hb₀ hb₀' hbR hbL hf
  have hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ w hw with h' | h'
    · rw [mem_Icc_two_iff] at h'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h'
      omega
    · omega
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₀, hy₁, hy₁', hfen⟩ := exists_walk_cap_left
    (R' := R') (M' := M') (K' := K') (c₀ := z 1 + h) (c₁ := z 1 + h + W) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe hQin p₂ hp₂e
    (fun w hw => by have := hp₂ w hw; omega) (by omega) (by omega) ht hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₀, hy₁, hy₁', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ w h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · have := hp₂ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **The turn from the right side to the top side** (counterclockwise, at the top-right corner):
on the crossings of `H₁ = [z₀ + R, z₀ + h + W] × [y, y + W]`, of the band
`V = [z₀ + h, z₀ + h + W] × [y, z₁ + R' - 1]` and of the top cap on the columns
`[z₀ + h, z₀ + h + W]`, a fenced arm ending on the right side in the rows `[y, y + W]` is continued
to a point of the top side of `B_{R'}(z)` in those columns with an outer fence `(M', K')`. -/
theorem exists_walk_turn_right_top (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h y : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hH₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, y] ![z 0 + h + W, y + W])
    (hV : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + h, y] ![z 0 + h + W, z 1 + R' - 1])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + h, z 1 + R' - M']
      ![z 0 + h + W, z 1 + R' - 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + h, z 1 + R' - M']
      ![z 0 + h + W, z 1 + R' + M'])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + h - K', z 1 + R' + 1]
      ![z 0 + h + W + K', z 1 + R' + M'])
    (hb₀ : b 0 = z 0 + R) (hb₁ : y ≤ b 1) (hb₁' : b 1 ≤ y + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y' : LatticeSite 2) (P : (zdGraph 2).Walk x' y'), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (y ≤ v 1 ∧ v 1 ≤ y + W ∧ z 0 + R ≤ v 0 ∧ v 0 ≤ z 0 + h + W) ∨
        (z 0 + h ≤ v 0 ∧ v 0 ≤ z 0 + h + W ∧ y ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y') ∧
      y' ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y' 1 = z 1 + R' ∧ z 0 + h ≤ y' 0 ∧ y' 0 ≤ z 0 + h + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y' y') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_right hM hWK hKM hW (h := h) (y := y) (yl := y) (yr := z 1 + R' - 1)
      le_rfl (by omega) (by omega) hMR hH₁ hV hb₀ hb₁ hb₁' hbT hbB hf
  have hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ w hw with h' | h'
    · rw [mem_Icc_two_iff] at h'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h'
      omega
    · omega
  obtain ⟨y', P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_top
    (R' := R') (M' := M') (K' := K') (c₀ := z 0 + h) (c₁ := z 0 + h + W) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe hQin p₂ hp₂e
    (fun w hw => by have := hp₂ w hw; omega) (by omega) (by omega) ht hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y', P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ w h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · have := hp₂ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **The turn from the left side to the bottom side** (counterclockwise, at the bottom-left
corner): on the crossings of `H₁ = [z₀ - h - W, z₀ - R - δ] × [y, y + W]`, of the band
`V = [z₀ - h - W, z₀ - h] × [z₁ - R' + 1 - δ, y + W]` and of the bottom cap on the columns
`[z₀ - h - W, z₀ - h]`, a fenced arm ending on the left side in the rows `[y, y + W]` is continued
to a point of the bottom side of `B_{R'}(z)` in those columns with an outer fence `(M', K')`. -/
theorem exists_walk_turn_left_bottom (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h y : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R')
    (hH₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W, y]
      ![z 0 - R - cond col 0 1, y + W])
    (hV : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - h - W, z 1 - R' + 1 - cond col 0 1]
      ![z 0 - h, y + W])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W, z 1 - R' + 1 - cond col 0 1]
      ![z 0 - h, z 1 - R' + M' - cond col 0 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - h - W, z 1 - R' - M' - cond col 0 1]
      ![z 0 - h, z 1 - R' + M' - cond col 0 1])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0
      ![z 0 - h - W - K', z 1 - R' - M' - cond col 0 1]
      ![z 0 - h + K', z 1 - R' - 1 - cond col 0 1])
    (hb₀ : b 0 = z 0 - R - cond col 0 1) (hb₁ : y ≤ b 1) (hb₁' : b 1 ≤ y + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y' : LatticeSite 2) (P : (zdGraph 2).Walk x' y'), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (y ≤ v 1 ∧ v 1 ≤ y + W ∧ z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - R - cond col 0 1) ∨
        (z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - h ∧ z 1 - R' - M' - 1 ≤ v 1 ∧ v 1 ≤ y + W)) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y') ∧
      y' ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y' 1 = z 1 - R' - cond col 0 1 ∧ z 0 - h - W ≤ y' 0 ∧ y' 0 ≤ z 0 - h ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y' y') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_left hM hWK hKM hW (h := h) (y := y) (yl := z 1 - R' + 1 - cond col 0 1)
      (yr := y + W) (by omega) le_rfl hh hH₁ hV hb₀ hb₁ hb₁' hbT hbB hf
  have hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ w hw with h' | h'
    · rw [mem_Icc_two_iff] at h'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h'
      omega
    · omega
  obtain ⟨y', P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_bottom
    (R' := R') (M' := M') (K' := K') (c₀ := z 0 - h - W) (c₁ := z 0 - h) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe hQin p₂ hp₂e
    (fun w hw => by have := hp₂ w hw; omega) (by omega) (by omega) ht hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y', P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ w h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · have := hp₂ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **The turn from the bottom side to the right side** (counterclockwise, at the bottom-right
corner): on the crossings of `V₁ = [x, x + W] × [z₁ - h - W, z₁ - R - δ]`, of the band
`H = [x, z₀ + R' - 1] × [z₁ - h - W, z₁ - h]` and of the right cap on the rows
`[z₁ - h - W, z₁ - h]`, a fenced arm ending on the bottom side in the columns `[x, x + W]` is
continued to a point of the right side of `B_{R'}(z)` in those rows with an outer fence
`(M', K')`. -/
theorem exists_walk_turn_bottom_right (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R')
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 - h - W]
      ![x + W, z 1 - R - cond col 0 1])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![x, z 1 - h - W] ![z 0 + R' - 1, z 1 - h])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' - M', z 1 - h - W]
      ![z 0 + R' - 1, z 1 - h])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R' - M', z 1 - h - W]
      ![z 0 + R' + M', z 1 - h])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' + 1, z 1 - h - W - K']
      ![z 0 + R' + M', z 1 - h + K'])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 - h - W ≤ v 1 ∧ v 1 ≤ z 1 - R - cond col 0 1) ∨
        (x ≤ v 0 ∧ v 0 ≤ z 0 + R' + M' ∧ z 1 - h - W ≤ v 1 ∧ v 1 ≤ z 1 - h)) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 + R' ∧ z 1 - h - W ≤ y 1 ∧ y 1 ≤ z 1 - h ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_bottom hM hWK hKM hW (h := h) (x := x) (xl := x) (xr := z 0 + R' - 1)
      le_rfl (by omega) hh hV₁ hH hb₁ hb₀ hb₀' hbR hbL hf
  have hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ w hw with h' | h'
    · rw [mem_Icc_two_iff] at h'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h'
      omega
    · omega
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₀, hy₁, hy₁', hfen⟩ := exists_walk_cap_right
    (R' := R') (M' := M') (K' := K') (c₀ := z 1 - h - W) (c₁ := z 1 - h) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe hQin p₂ hp₂e
    (fun w hw => by have := hp₂ w hw; omega) (by omega) (by omega) ht hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₀, hy₁, hy₁', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ w h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · have := hp₂ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

end Turns

/-! ### Jogs with wide caps -/

section JogCaps

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R R' M K M' K' W : ℕ}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **A jog with a wide cap on the top side.** On the crossings of `V₁ = [x, x + W] × [z₁ + R,
z₁ + h + W]`, `H = [xl, xr + W] × [z₁ + h, z₁ + h + W]`, `V₂ = [x + d, x + d + W] × [z₁ + h,
z₁ + R' - 1]` and of the top cap on the columns `[x + d, x + d + W]` (fence box
`[x + d - K', x + d + W + K'] × [z₁ + R' + 1, z₁ + R' + M']`), a fenced arm ending on the top side
in the columns `[x, x + W]` is continued to a point of the top side of `B_{R'}(z)` in the columns
`[x + d, x + d + W]` with an outer fence `(M', K')`, for any `K'` with `W + K' ≤ M'`. -/
theorem exists_walk_jogCap_top (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hcl : z 0 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 0 + R' - 1)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 + R] ![x + W, z 1 + h + W])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![xl, z 1 + h] ![xr + W, z 1 + h + W])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d, z 1 + h] ![x + d + W, z 1 + R' - 1])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d, z 1 + R' - M']
      ![x + d + W, z 1 + R' - 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d, z 1 + R' - M']
      ![x + d + W, z 1 + R' + M'])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d - K', z 1 + R' + 1]
      ![x + d + W + K', z 1 + R' + M'])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W) ∨
        (xl ≤ v 0 ∧ v 0 ≤ xr + W ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 1 = z 1 + R' ∧ x + d ≤ y 0 ∧ y 0 ≤ x + d + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_top hM hWK hKM hW (h := h) (x := x) (xl := xl) (xr := xr + W) hxl
      (by omega) (by omega) hMR hV₁ hH hb₁ hb₀ hb₀' hbR hbL hf
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₃ hd₃
  have C₃ : ∀ w ∈ p₃.support, x + d ≤ w 0 ∧ w 0 ≤ x + d + W ∧
      z 1 + h ≤ w 1 ∧ w 1 ≤ z 1 + R' - 1 := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₃
    (x₀ := x + d) (x₁ := x + d + W) (y₀ := z 1 + h) (y₁ := z 1 + h + W) (by omega) (by omega)
    (fun w hw => ⟨(hp₂ w hw).2.2.1, (hp₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q hQe p₂ hp₂e ht hw₃p₂
  have hQin : ∀ w ∈ Q₃.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ₃s w hw with h' | h'
    · rcases hQ w h' with h'' | h''
      · rw [mem_Icc_two_iff] at h''
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h''
        omega
      · omega
    · have := hp₂ w h'
      omega
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_top
    (R' := R') (M' := M') (K' := K') (c₀ := x + d) (c₁ := x + d + W) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q₃ hQ₃e hQin p₃ hp₃e
    (fun w hw => by have := C₃ w hw; omega) (by omega) (by omega) hw₃p₃ hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ₃s w h' with h'' | h''
    · rcases hQ w h'' with h''' | h'''
      · exact Or.inl h'''
      · exact Or.inr (Or.inl h''')
    · have := hp₂ w h''
      exact Or.inr (Or.inr (by omega))
  · have := C₃ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **A jog with a wide cap on the bottom side**: `exists_walk_jogCap_top` reflected;
`V₁ = [x, x + W] × [z₁ - h - W, z₁ - R - δ]`, `H = [xl, xr + W] × [z₁ - h - W, z₁ - h]`,
`V₂ = [x + d, x + d + W] × [z₁ - R' + 1 - δ, z₁ - h]` and the bottom cap. -/
theorem exists_walk_jogCap_bottom (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hcl : z 0 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 0 + R' - 1)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 - h - W]
      ![x + W, z 1 - R - cond col 0 1])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![xl, z 1 - h - W] ![xr + W, z 1 - h])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d, z 1 - R' + 1 - cond col 0 1]
      ![x + d + W, z 1 - h])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d, z 1 - R' + 1 - cond col 0 1]
      ![x + d + W, z 1 - R' + M' - cond col 0 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d, z 1 - R' - M' - cond col 0 1]
      ![x + d + W, z 1 - R' + M' - cond col 0 1])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d - K', z 1 - R' - M' - cond col 0 1]
      ![x + d + W + K', z 1 - R' - 1 - cond col 0 1])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 - h - W ≤ v 1 ∧ v 1 ≤ z 1 - R - cond col 0 1) ∨
        (xl ≤ v 0 ∧ v 0 ≤ xr + W ∧ z 1 - R' - M' - 1 ≤ v 1 ∧ v 1 ≤ z 1 - h)) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 1 = z 1 - R' - cond col 0 1 ∧ x + d ≤ y 0 ∧ y 0 ≤ x + d + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_bottom hM hWK hKM hW (h := h) (x := x) (xl := xl) (xr := xr + W) hxl
      (by omega) hh hV₁ hH hb₁ hb₀ hb₀' hbR hbL hf
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₃ hd₃
  have C₃ : ∀ w ∈ p₃.support, x + d ≤ w 0 ∧ w 0 ≤ x + d + W ∧
      z 1 - R' + 1 - cond col 0 1 ≤ w 1 ∧ w 1 ≤ z 1 - h := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₃
    (x₀ := x + d) (x₁ := x + d + W) (y₀ := z 1 - h - W) (y₁ := z 1 - h) (by omega) (by omega)
    (fun w hw => ⟨(hp₂ w hw).2.2.1, (hp₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q hQe p₂ hp₂e ht hw₃p₂
  have hQin : ∀ w ∈ Q₃.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ₃s w hw with h' | h'
    · rcases hQ w h' with h'' | h''
      · rw [mem_Icc_two_iff] at h''
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h''
        omega
      · omega
    · have := hp₂ w h'
      omega
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_bottom
    (R' := R') (M' := M') (K' := K') (c₀ := x + d) (c₁ := x + d + W) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q₃ hQ₃e hQin p₃ hp₃e
    (fun w hw => by have := C₃ w hw; omega) (by omega) (by omega) hw₃p₃ hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ₃s w h' with h'' | h''
    · rcases hQ w h'' with h''' | h'''
      · exact Or.inl h'''
      · exact Or.inr (Or.inl h''')
    · have := hp₂ w h''
      exact Or.inr (Or.inr (by omega))
  · have := C₃ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **A jog with a wide cap on the right side**: `exists_walk_jogCap_top` with the coordinates
exchanged; `H₁ = [z₀ + R, z₀ + h + W] × [y, y + W]`, `V = [z₀ + h, z₀ + h + W] × [yl, yr + W]`,
`H₂ = [z₀ + h, z₀ + R' - 1] × [y + d, y + d + W]` and the right cap. -/
theorem exists_walk_jogCap_right (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hcl : z 1 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 1 + R' - 1)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, x] ![z 0 + h + W, x + W])
    (hH : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + h, xl] ![z 0 + h + W, xr + W])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + h, x + d] ![z 0 + R' - 1, x + d + W])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' - M', x + d]
      ![z 0 + R' - 1, x + d + W])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R' - M', x + d]
      ![z 0 + R' + M', x + d + W])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' + 1, x + d - K']
      ![z 0 + R' + M', x + d + W + K'])
    (hb₀ : b 0 = z 0 + R) (hb₁ : x ≤ b 1) (hb₁' : b 1 ≤ x + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 1 ∧ v 1 ≤ x + W ∧ z 0 + R ≤ v 0 ∧ v 0 ≤ z 0 + h + W) ∨
        (xl ≤ v 1 ∧ v 1 ≤ xr + W ∧ z 0 + h ≤ v 0 ∧ v 0 ≤ z 0 + R' + M')) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 + R' ∧ x + d ≤ y 1 ∧ y 1 ≤ x + d + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_right hM hWK hKM hW (h := h) (y := x) (yl := xl) (yr := xr + W) hxl
      (by omega) (by omega) hMR hV₁ hH hb₀ hb₁ hb₁' hbT hbB hf
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero] at hc₃ hd₃
  have C₃ : ∀ w ∈ p₃.support, x + d ≤ w 1 ∧ w 1 ≤ x + d + W ∧
      z 0 + h ≤ w 0 ∧ w 0 ≤ z 0 + R' - 1 := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₃
    (x₀ := x + d) (x₁ := x + d + W) (y₀ := z 0 + h) (y₁ := z 0 + h + W) (by omega) (by omega)
    (fun w hw => ⟨(hp₂ w hw).2.2.1, (hp₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q hQe p₂ hp₂e ht hw₃p₂
  have hQin : ∀ w ∈ Q₃.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ₃s w hw with h' | h'
    · rcases hQ w h' with h'' | h''
      · rw [mem_Icc_two_iff] at h''
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h''
        omega
      · omega
    · have := hp₂ w h'
      omega
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_right
    (R' := R') (M' := M') (K' := K') (c₀ := x + d) (c₁ := x + d + W) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q₃ hQ₃e hQin p₃ hp₃e
    (fun w hw => by have := C₃ w hw; omega) (by omega) (by omega) hw₃p₃ hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ₃s w h' with h'' | h''
    · rcases hQ w h'' with h''' | h'''
      · exact Or.inl h'''
      · exact Or.inr (Or.inl h''')
    · have := hp₂ w h''
      exact Or.inr (Or.inr (by omega))
  · have := C₃ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **A jog with a wide cap on the left side**: `exists_walk_jogCap_bottom` with the coordinates
exchanged; `H₁ = [z₀ - h - W, z₀ - R - δ] × [y, y + W]`, `V = [z₀ - h - W, z₀ - h] × [yl, yr + W]`,
`H₂ = [z₀ - R' + 1 - δ, z₀ - h] × [y + d, y + d + W]` and the left cap. -/
theorem exists_walk_jogCap_left (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hcl : z 1 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 1 + R' - 1)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W, x]
      ![z 0 - R - cond col 0 1, x + W])
    (hH : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - h - W, xl] ![z 0 - h, xr + W])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' + 1 - cond col 0 1, x + d]
      ![z 0 - h, x + d + W])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - R' + 1 - cond col 0 1, x + d]
      ![z 0 - R' + M' - cond col 0 1, x + d + W])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' - M' - cond col 0 1, x + d]
      ![z 0 - R' + M' - cond col 0 1, x + d + W])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - R' - M' - cond col 0 1, x + d - K']
      ![z 0 - R' - 1 - cond col 0 1, x + d + W + K'])
    (hb₀ : b 0 = z 0 - R - cond col 0 1) (hb₁ : x ≤ b 1) (hb₁' : b 1 ≤ x + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 1 ∧ v 1 ≤ x + W ∧ z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - R - cond col 0 1) ∨
        (xl ≤ v 1 ∧ v 1 ≤ xr + W ∧ z 0 - R' - M' - 1 ≤ v 0 ∧ v 0 ≤ z 0 - h)) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 - R' - cond col 0 1 ∧ x + d ≤ y 1 ∧ y 1 ≤ x + d + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_left hM hWK hKM hW (h := h) (y := x) (yl := xl) (yr := xr + W) hxl
      (by omega) hh hV₁ hH hb₀ hb₁ hb₁' hbT hbB hf
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero] at hc₃ hd₃
  have C₃ : ∀ w ∈ p₃.support, x + d ≤ w 1 ∧ w 1 ≤ x + d + W ∧
      z 0 - R' + 1 - cond col 0 1 ≤ w 0 ∧ w 0 ≤ z 0 - h := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₃
    (x₀ := x + d) (x₁ := x + d + W) (y₀ := z 0 - h - W) (y₁ := z 0 - h) (by omega) (by omega)
    (fun w hw => ⟨(hp₂ w hw).2.2.1, (hp₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q hQe p₂ hp₂e ht hw₃p₂
  have hQin : ∀ w ∈ Q₃.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
    intro w hw
    rw [mem_cond_interior_iff]
    rcases hQ₃s w hw with h' | h'
    · rcases hQ w h' with h'' | h''
      · rw [mem_Icc_two_iff] at h''
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h''
        omega
      · omega
    · have := hp₂ w h'
      omega
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_left
    (R' := R') (M' := M') (K' := K') (c₀ := x + d) (c₁ := x + d + W) hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q₃ hQ₃e hQin p₃ hp₃e
    (fun w hw => by have := C₃ w hw; omega) (by omega) (by omega) hw₃p₃ hHc
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hU ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ hHf
    ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h' | h' | h'
  · rcases hQ₃s w h' with h'' | h''
    · rcases hQ w h'' with h''' | h'''
      · exact Or.inl h'''
      · exact Or.inr (Or.inl h''')
    · have := hp₂ w h''
      exact Or.inr (Or.inr (by omega))
  · have := C₃ w h'
    exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inr (by omega))

end JogCaps

/-! ### Corridor events from boxes -/

section CorridorEvents

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- A box of `ℤ²` (enlarged by one at its upper corner for the dual colour) lies in a region
`Icc gl gh` and misses the interior of `B_R(z)` when its corners do. -/
theorem box_mem_region {col : Bool} {z : LatticeSite 2} {R : ℕ} {a₀ a₁ b₀ b₁ : ℤ}
    {gl gh : LatticeSite 2} (h₀ : gl 0 ≤ a₀) (h₁ : gl 1 ≤ a₁) (h₂ : b₀ + 1 ≤ gh 0)
    (h₃ : b₁ + 1 ≤ gh 1)
    (hout : z 1 + R ≤ a₁ ∨ b₁ + cond col 0 1 ≤ z 1 - R ∨ z 0 + R ≤ a₀ ∨
      b₀ + cond col 0 1 ≤ z 0 - R) :
    ∀ v ∈ Icc (![a₀, a₁] : LatticeSite 2) (![b₀, b₁] + cond col 0 1),
      v ∈ Icc gl gh ∧ v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
  intro v hv
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rw [mem_Icc_two_iff] at hv
  simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv
  refine ⟨?_, fun h => ?_⟩
  · rw [mem_Icc_two_iff]
    omega
  · rw [mem_Icc_two_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h
    omega

/-- **Crossings of either colour, bottom to top**, for a box given by its corner coordinates:
`le_law_preimage_cond_crossing_one`. -/
theorem CrossingBounds.le_law_box_one (h : CrossingBounds q L c) (col : Bool) (κ : ℕ) {w : ℕ}
    (hw : 1 ≤ w) (hwL : (w : ℕ∞) ≤ L) {a₀ a₁ b₀ b₁ : ℤ} (h₁ : a₁ ≤ b₁) (h₁' : b₁ ≤ a₁ + κ * w)
    (h₀ : a₀ + w ≤ b₀) :
    c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing 1 ![a₀, a₁] ![b₀, b₁]) :=
  h.le_law_preimage_cond_crossing_one col κ hw hwL h₁ h₁' h₀

/-- **Crossings of either colour, left to right**, for a box given by its corner coordinates:
`le_law_preimage_cond_crossing_zero`. -/
theorem CrossingBounds.le_law_box_zero (h : CrossingBounds q L c) (col : Bool) (κ : ℕ) {w : ℕ}
    (hw : 1 ≤ w) (hwL : (w : ℕ∞) ≤ L) {a₀ a₁ b₀ b₁ : ℤ} (h₀ : a₀ ≤ b₀) (h₀' : b₀ ≤ a₀ + κ * w)
    (h₁ : a₁ + w ≤ b₁) :
    c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing 0 ![a₀, a₁] ![b₀, b₁]) :=
  h.le_law_preimage_cond_crossing_zero col κ hw hwL h₀ h₀' h₁

variable {col : Bool} {z : LatticeSite 2} {r R R' M K M' K' κ : ℕ}

/-- **A corridor event from six boxes.** If six boxes, each crossed with probability at least
`c κ` in the configuration of colour `col`, lie in a region `G` and miss the interior of
`B_R(z)`, then the event that all six are crossed is measurable, determined by the pairs inside
the boxes (enlarged by one at the upper corner for the dual colour), monotone in the colour and of
probability at least `c κ ^ 6`; together with the boxes of radius `M + 1` about the possible ends
`B`, a region `Q ⊆ G` meeting `Icc (z - R - 1) (z + R)` only near the ends, and a hook on the
event, this is the corridor data that the gluing over disjoint regions takes. -/
theorem exists_corridor_of_boxes (dir : Fin 6 → Fin 2) (lo hi : Fin 6 → LatticeSite 2)
    (G Q B B' : Set (LatticeSite 2))
    (hprob : ∀ m, c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing (dir m) (lo m) (hi m)))
    (hbox : ∀ m, ∀ v ∈ Icc (lo m) (hi m + cond col 0 1),
      v ∈ G ∧ v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hBG : ∀ b ∈ B, Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G)
    (hQG : Q ⊆ G)
    (hQloc : ∀ b ∈ B, ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
      v ∈ Icc (b - (M : LatticeSite 2)) (b + M))
    (hhook : ∀ ω : Config (LatticeSite 2),
      (∀ m, cond col ω (dualConfig ω) ∈ crossing (dir m) (lo m) (hi m)) →
      ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
        IsArm ω col z r (z - R) (z + R) γ → b ∈ B → HasOuterFence ω col z R M K γ →
        ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
          x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) :
    ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ G) ∧
      (∀ b ∈ B, Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G) ∧
      Q ⊆ G ∧
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  refine ⟨{ω | ∀ m, cond col ω (dualConfig ω) ∈ crossing (dir m) (lo m) (hi m)},
    {e | ∃ m, ∀ v ∈ e, v ∈ Icc (lo m) (hi m + cond col 0 1)}, Q,
    measurableSet_setOf_forall_cond_crossing col _ _ _,
    fun ω ω' hωω' => forall_cond_crossing_iff_of_inter_eq col _ _ _ hωω',
    fun ω ω' hωω' hω m => cond_mem_crossing_of_cond_subset hωω' (hω m),
    fun e he v hv => ?_, fun e he v hv => ?_, hBG, hQG, hQloc, fun ω hω => hhook ω hω, ?_⟩
  · obtain ⟨m, hm⟩ := he
    exact (hbox m v (hm v hv)).2
  · obtain ⟨m, hm⟩ := he
    exact (hbox m v (hm v hv)).1
  · have := Finset.pow_card_le_prod Finset.univ (fun m => law q ((fun ω : Config (LatticeSite 2) =>
      cond col ω (dualConfig ω)) ⁻¹' crossing (dir m) (lo m) (hi m))) (c κ) (fun m _ => hprob m)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.trans (prod_law_le_law_setOf_forall_cond_crossing q col _ _ _)

end CorridorEvents

/-! ### Corridors of jogs with wide caps and of turns -/

section MoveCorridors

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}
  {col : Bool} {z : LatticeSite 2} {r R R' M K M' K' W κ : ℕ}

/-- **The corridor of a jog with a wide cap on the top side** (`exists_walk_jogCap_top`): six
crossings in the region `Icc gl gh`, of probability at least `c κ ^ 6`, on which every fenced arm
ending in the bin `[x, x + W]` is continued to the columns `[x + d, x + d + W]` of the top side of
`B_{R'}(z)` with an outer fence `(M', K')`. -/
theorem exists_corridor_jogCap_top (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x d xl xr h : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hcl : z 0 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 0 + R' - 1)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
      b 0 + 2 * M ≤ z 0 + R)
    (hB' : ∀ v : LatticeSite 2, v 1 = z 1 + R' → x + d ≤ v 0 → v 0 ≤ x + d + W → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M + K' ≤ xl) (hgh₀ : xr + W + M + K' + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M ≤ z 1 + R) (hgh₁ : z 1 + R' + M' + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![1, 0, 1, 0, 1, 0]
    ![![x, z 1 + R],
      ![xl, z 1 + h],
      ![x + d, z 1 + h],
      ![x + d, z 1 + R' - M'],
      ![x + d, z 1 + R' - M'],
      ![x + d - K', z 1 + R' + 1]]
    ![![x + W, z 1 + h + W],
      ![xr + W, z 1 + h + W],
      ![x + d + W, z 1 + R' - 1],
      ![x + d + W, z 1 + R' - 1],
      ![x + d + W, z 1 + R' + M'],
      ![x + d + W + K', z 1 + R' + M']]
    (Icc gl gh) {v | (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W) ∨
      (xl ≤ v 0 ∧ v 0 ≤ xr + W ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')} B B' ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_jogCap_top (R' := R') (M' := M') (K' := K') (h := h) (d := d)
        (xl := xl) (xr := xr) hM hWK hKM hW hM' hWM' hxl hxl' hxr hxr' hh hhR hMR hcl hcr
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) (hω 5) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of a jog with a wide cap on the bottom side** (`exists_walk_jogCap_bottom`). -/
theorem exists_corridor_jogCap_bottom (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x d xl xr h : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hcl : z 0 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 0 + R' - 1)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
      z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R)
    (hB' : ∀ v : LatticeSite 2, v 1 = z 1 - R' - cond col 0 1 → x + d ≤ v 0 → v 0 ≤ x + d + W → v
      ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M + K' ≤ xl) (hgh₀ : xr + W + M + K' + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M' + 1 ≤ z 1 - R') (hgh₁ : z 1 - R + M + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![1, 0, 1, 0, 1, 0]
    ![![x, z 1 - h - W],
      ![xl, z 1 - h - W],
      ![x + d, z 1 - R' + 1 - cond col 0 1],
      ![x + d, z 1 - R' + 1 - cond col 0 1],
      ![x + d, z 1 - R' - M' - cond col 0 1],
      ![x + d - K', z 1 - R' - M' - cond col 0 1]]
    ![![x + W, z 1 - R - cond col 0 1],
      ![xr + W, z 1 - h],
      ![x + d + W, z 1 - h],
      ![x + d + W, z 1 - R' + M' - cond col 0 1],
      ![x + d + W, z 1 - R' + M' - cond col 0 1],
      ![x + d + W + K', z 1 - R' - 1 - cond col 0 1]]
    (Icc gl gh) {v | (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 - h - W ≤ v 1 ∧ v 1 ≤ z 1 - R - cond col 0 1) ∨
      (xl ≤ v 0 ∧ v 0 ≤ xr + W ∧ z 1 - R' - M' - 1 ≤ v 1 ∧ v 1 ≤ z 1 - h)} B B' ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_jogCap_bottom (R' := R') (M' := M') (K' := K') (h := h) (d := d)
        (xl := xl) (xr := xr) hM hWK hKM hW hM' hWM' hxl hxl' hxr hxr' hh hhR hcl hcr
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) (hω 5) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of a jog with a wide cap on the right side** (`exists_walk_jogCap_right`). -/
theorem exists_corridor_jogCap_right (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x d xl xr h : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hcl : z 1 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 1 + R' - 1)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
      b 1 + 2 * M ≤ z 1 + R)
    (hB' : ∀ v : LatticeSite 2, v 0 = z 0 + R' → x + d ≤ v 1 → v 1 ≤ x + d + W → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M ≤ z 0 + R) (hgh₀ : z 0 + R' + M' + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M + K' ≤ xl) (hgh₁ : xr + W + M + K' + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![0, 1, 0, 1, 0, 1]
    ![![z 0 + R, x],
      ![z 0 + h, xl],
      ![z 0 + h, x + d],
      ![z 0 + R' - M', x + d],
      ![z 0 + R' - M', x + d],
      ![z 0 + R' + 1, x + d - K']]
    ![![z 0 + h + W, x + W],
      ![z 0 + h + W, xr + W],
      ![z 0 + R' - 1, x + d + W],
      ![z 0 + R' - 1, x + d + W],
      ![z 0 + R' + M', x + d + W],
      ![z 0 + R' + M', x + d + W + K']]
    (Icc gl gh) {v | (x ≤ v 1 ∧ v 1 ≤ x + W ∧ z 0 + R ≤ v 0 ∧ v 0 ≤ z 0 + h + W) ∨
      (xl ≤ v 1 ∧ v 1 ≤ xr + W ∧ z 0 + h ≤ v 0 ∧ v 0 ≤ z 0 + R' + M')} B B' ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_jogCap_right (R' := R') (M' := M') (K' := K') (h := h) (d := d)
        (xl := xl) (xr := xr) hM hWK hKM hW hM' hWM' hxl hxl' hxr hxr' hh hhR hMR hcl hcr
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) (hω 5) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of a jog with a wide cap on the left side** (`exists_walk_jogCap_left`). -/
theorem exists_corridor_jogCap_left (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x d xl xr h : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hcl : z 1 - R' + 1 ≤ xl) (hcr : xr + W ≤ z 1 + R' - 1)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
      z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)
    (hB' : ∀ v : LatticeSite 2, v 0 = z 0 - R' - cond col 0 1 → x + d ≤ v 1 → v 1 ≤ x + d + W → v
      ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M' + 1 ≤ z 0 - R') (hgh₀ : z 0 - R + M + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M + K' ≤ xl) (hgh₁ : xr + W + M + K' + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![0, 1, 0, 1, 0, 1]
    ![![z 0 - h - W, x],
      ![z 0 - h - W, xl],
      ![z 0 - R' + 1 - cond col 0 1, x + d],
      ![z 0 - R' + 1 - cond col 0 1, x + d],
      ![z 0 - R' - M' - cond col 0 1, x + d],
      ![z 0 - R' - M' - cond col 0 1, x + d - K']]
    ![![z 0 - R - cond col 0 1, x + W],
      ![z 0 - h, xr + W],
      ![z 0 - h, x + d + W],
      ![z 0 - R' + M' - cond col 0 1, x + d + W],
      ![z 0 - R' + M' - cond col 0 1, x + d + W],
      ![z 0 - R' - 1 - cond col 0 1, x + d + W + K']]
    (Icc gl gh) {v | (x ≤ v 1 ∧ v 1 ≤ x + W ∧ z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - R - cond col 0 1) ∨
      (xl ≤ v 1 ∧ v 1 ≤ xr + W ∧ z 0 - R' - M' - 1 ≤ v 0 ∧ v 0 ≤ z 0 - h)} B B' ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_jogCap_left (R' := R') (M' := M') (K' := K') (h := h) (d := d)
        (xl := xl) (xr := xr) hM hWK hKM hW hM' hWM' hxl hxl' hxr hxr' hh hhR hcl hcr
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) (hω 5) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of the turn from the top side to the left side** (`exists_walk_turn_top_left`;
five crossings, the first counted twice): on it every fenced arm ending on the top side in the bin
`[x, x + W]` is continued to the rows `[z₁ + h, z₁ + h + W]` of the left side of `B_{R'}(z)` with an
outer fence `(M', K')`. -/
theorem exists_corridor_turn_top_left (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x h : ℤ}
    (hx₁ : z 0 - R + M ≤ x) (hx₂ : x + W ≤ z 0 + R - M)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
      b 0 + 2 * M ≤ z 0 + R)
    (hB' : ∀ v : LatticeSite 2, v 0 = z 0 - R' - cond col 0 1 → z 1 + h ≤ v 1 → v 1 ≤ z 1 + h + W
      → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M' + 1 ≤ z 0 - R') (hgh₀ : x + W + M + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M + K' ≤ z 1 + R) (hgh₁ : z 1 + h + W + K' + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![1, 0, 1, 0, 1, 1]
    ![![x, z 1 + R],
      ![z 0 - R' + 1 - cond col 0 1, z 1 + h],
      ![z 0 - R' + 1 - cond col 0 1, z 1 + h],
      ![z 0 - R' - M' - cond col 0 1, z 1 + h],
      ![z 0 - R' - M' - cond col 0 1, z 1 + h - K'],
      ![x, z 1 + R]]
    ![![x + W, z 1 + h + W],
      ![x + W, z 1 + h + W],
      ![z 0 - R' + M' - cond col 0 1, z 1 + h + W],
      ![z 0 - R' + M' - cond col 0 1, z 1 + h + W],
      ![z 0 - R' - 1 - cond col 0 1, z 1 + h + W + K'],
      ![x + W, z 1 + h + W]]
    (Icc gl gh) {v | (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W) ∨
      (z 0 - R' - M' - 1 ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + h + W)} B B' ?_ ?_ ?_
          ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_turn_top_left (R' := R') (M' := M') (K' := K') (h := h) hM hWK hKM hW hM' hWM'
          hh hhR hMR
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of the turn from the right side to the top side** (`exists_walk_turn_right_top`).
-/
theorem exists_corridor_turn_right_top (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {y h : ℤ}
    (hy₁ : z 1 - R + M ≤ y) (hy₂ : y + W ≤ z 1 + R - M)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 0 = z 0 + R ∧ y ≤ b 1 ∧ b 1 ≤ y + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
      b 1 + 2 * M ≤ z 1 + R)
    (hB' : ∀ v : LatticeSite 2, v 1 = z 1 + R' → z 0 + h ≤ v 0 → v 0 ≤ z 0 + h + W → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M + K' ≤ z 0 + R) (hgh₀ : z 0 + h + W + K' + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M ≤ y) (hgh₁ : z 1 + R' + M' + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![0, 1, 0, 1, 0, 0]
    ![![z 0 + R, y],
      ![z 0 + h, y],
      ![z 0 + h, z 1 + R' - M'],
      ![z 0 + h, z 1 + R' - M'],
      ![z 0 + h - K', z 1 + R' + 1],
      ![z 0 + R, y]]
    ![![z 0 + h + W, y + W],
      ![z 0 + h + W, z 1 + R' - 1],
      ![z 0 + h + W, z 1 + R' - 1],
      ![z 0 + h + W, z 1 + R' + M'],
      ![z 0 + h + W + K', z 1 + R' + M'],
      ![z 0 + h + W, y + W]]
    (Icc gl gh) {v | (y ≤ v 1 ∧ v 1 ≤ y + W ∧ z 0 + R ≤ v 0 ∧ v 0 ≤ z 0 + h + W) ∨
      (z 0 + h ≤ v 0 ∧ v 0 ≤ z 0 + h + W ∧ y ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')} B B' ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_turn_right_top (R' := R') (M' := M') (K' := K') (h := h) hM hWK hKM hW hM' hWM'
          hh hhR hMR
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of the turn from the left side to the bottom side**
(`exists_walk_turn_left_bottom`). -/
theorem exists_corridor_turn_left_bottom (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {y h : ℤ}
    (hy₁ : z 1 - R + M ≤ y) (hy₂ : y + W ≤ z 1 + R - M)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 0 = z 0 - R - cond col 0 1 ∧ y ≤ b 1 ∧ b 1 ≤ y + W ∧
      z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)
    (hB' : ∀ v : LatticeSite 2, v 1 = z 1 - R' - cond col 0 1 → z 0 - h - W ≤ v 0 → v 0 ≤ z 0 - h
      → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + W + K' ≤ z 0 - h) (hgh₀ : z 0 - R + M + K' + 1 ≤ gh 0)
    (hgl₁ : gl 1 + M' + 1 ≤ z 1 - R') (hgh₁ : y + W + M + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![0, 1, 0, 1, 0, 0]
    ![![z 0 - h - W, y],
      ![z 0 - h - W, z 1 - R' + 1 - cond col 0 1],
      ![z 0 - h - W, z 1 - R' + 1 - cond col 0 1],
      ![z 0 - h - W, z 1 - R' - M' - cond col 0 1],
      ![z 0 - h - W - K', z 1 - R' - M' - cond col 0 1],
      ![z 0 - h - W, y]]
    ![![z 0 - R - cond col 0 1, y + W],
      ![z 0 - h, y + W],
      ![z 0 - h, z 1 - R' + M' - cond col 0 1],
      ![z 0 - h, z 1 - R' + M' - cond col 0 1],
      ![z 0 - h + K', z 1 - R' - 1 - cond col 0 1],
      ![z 0 - R - cond col 0 1, y + W]]
    (Icc gl gh) {v | (y ≤ v 1 ∧ v 1 ≤ y + W ∧ z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - R - cond col 0 1) ∨
      (z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - h ∧ z 1 - R' - M' - 1 ≤ v 1 ∧ v 1 ≤ y + W)} B B' ?_ ?_ ?_
          ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_turn_left_bottom (R' := R') (M' := M') (K' := K') (h := h) hM hWK hKM hW hM'
          hWM' hh hhR
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

/-- **The corridor of the turn from the bottom side to the right side**
(`exists_walk_turn_bottom_right`). -/
theorem exists_corridor_turn_bottom_right (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x h : ℤ}
    (hx₁ : z 0 - R + M ≤ x) (hx₂ : x + W ≤ z 0 + R - M)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
      z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R)
    (hB' : ∀ v : LatticeSite 2, v 0 = z 0 + R' → z 1 - h - W ≤ v 1 → v 1 ≤ z 1 - h → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M ≤ x) (hgh₀ : z 0 + R' + M' + 1 ≤ gh 0)
    (hgl₁ : gl 1 + W + K' ≤ z 1 - h) (hgh₁ : z 1 - R + M + K' + 1 ≤ gh 1) :
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
            v ∈ B' ∧ HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hm'] at hκ₂
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
  refine exists_corridor_of_boxes (col := col) (z := z) (r := r) (R := R) (R' := R') (M := M)
    (K := K) (M' := M') (K' := K') (κ := κ) ![1, 0, 1, 0, 1, 1]
    ![![x, z 1 - h - W],
      ![x, z 1 - h - W],
      ![z 0 + R' - M', z 1 - h - W],
      ![z 0 + R' - M', z 1 - h - W],
      ![z 0 + R' + 1, z 1 - h - W - K'],
      ![x, z 1 - h - W]]
    ![![x + W, z 1 - R - cond col 0 1],
      ![z 0 + R' - 1, z 1 - h],
      ![z 0 + R' - 1, z 1 - h],
      ![z 0 + R' + M', z 1 - h],
      ![z 0 + R' + M', z 1 - h + K'],
      ![x + W, z 1 - R - cond col 0 1]]
    (Icc gl gh) {v | (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 - h - W ≤ v 1 ∧ v 1 ≤ z 1 - R - cond col 0 1) ∨
      (x ≤ v 0 ∧ v 0 ≤ z 0 + R' + M' ∧ z 1 - h - W ≤ v 1 ∧ v 1 ≤ z 1 - h)} B B' ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_zero col κ hW hWL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ (w := m) (by omega) hmL (by omega) (by omega) (by omega)
    · exact hCB.le_law_box_one col κ hW hWL (by omega) (by omega) (by omega)
  · intro i
    fin_cases i
    all_goals exact box_mem_region (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro b hb v hv
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv
    push_cast at hv
    omega
  · intro v hv
    rw [mem_Icc_two_iff]
    rcases hv with hv | hv <;> omega
  · intro b hb v hv hvR
    have hb' := hB b hb
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ _ hb hf
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_turn_bottom_right (R' := R') (M' := M') (K' := K') (h := h) hM hWK hKM hW hM'
          hWM' hh hhR
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

end MoveCorridors

end PercLib.Models.Planar
