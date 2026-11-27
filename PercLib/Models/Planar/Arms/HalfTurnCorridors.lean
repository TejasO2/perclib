/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12) and
Section 4.6 (the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.TurnCorridors

/-!
# Clockwise turns at the two upper corners

In the plane, arms are moved into prescribed windows by counterclockwise turns only
(`TurnCorridors.lean`): an arm may go round the whole box. In a half-plane the arms cannot pass the
line, so an arm on the top side whose window lies on the right half-side must turn clockwise. This
file gives the two clockwise turns at the upper corners of `B_R(z)`, built like the counterclockwise
ones from a leg of two crossings and a cap of the next side:

* **from the top side to the right side** (at the top-right corner): out of the top side
  (`V₁ = [x, x + W] × [z₁ + R, z₁ + h + W]`), along the band
  `H = [x, z₀ + R' - 1] × [z₁ + h, z₁ + h + W]` and the right cap on its rows; the new end lies on
  the right side of `B_{R'}(z)` in the rows `[z₁ + h, z₁ + h + W]`;
* **from the left side to the top side** (at the top-left corner): out of the left side
  (`H₁ = [z₀ - h - W, z₀ - R - δ] × [y, y + W]`), along the band
  `V = [z₀ - h - W, z₀ - h] × [y, z₁ + R' - 1]` and the top cap on its columns; the new end lies on
  the top side of `B_{R'}(z)` in the columns `[z₀ - h - W, z₀ - h]`.

## Main results

* `exists_walk_turn_top_right`, `exists_walk_turn_left_top`: the two clockwise turns.
* `exists_corridor_turn_top_right`, `exists_corridor_turn_left_top`: their corridors, in the form
  used by the gluing over disjoint regions.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The two clockwise turns -/

section Turns

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R R' M K M' K' W : ℕ}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **The turn from the top side to the right side** (clockwise, at the top-right corner). An arm
ending at `b` on the top side of `B_R(z)`, in the columns `[x, x + W]`, with an outer fence
`(M, K)`, `W ≤ K`, is continued on the crossings of `V₁ = [x, x + W] × [z₁ + R, z₁ + h + W]`, of
the band `H = [x, z₀ + R' - 1] × [z₁ + h, z₁ + h + W]` and of the right cap
(`exists_walk_cap_right`) on the rows `[z₁ + h, z₁ + h + W]`, to the first point `y` outside the
interior of `B_{R'}(z)`; `y` lies on the right side of `B_{R'}(z)` in those rows and has an outer
fence `(M', K')`, for any `K'` with `W + K' ≤ M'`. -/
theorem exists_walk_turn_top_right (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h x : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 + R] ![x + W, z 1 + h + W])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![x, z 1 + h] ![z 0 + R' - 1, z 1 + h + W])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' - M', z 1 + h]
      ![z 0 + R' - 1, z 1 + h + W])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R' - M', z 1 + h]
      ![z 0 + R' + M', z 1 + h + W])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' + 1, z 1 + h - K']
      ![z 0 + R' + M', z 1 + h + W + K'])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W) ∨
        (x ≤ v 0 ∧ v 0 ≤ z 0 + R' + M' ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + h + W)) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 + R' ∧ z 1 + h ≤ y 1 ∧ y 1 ≤ z 1 + h + W ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_top hM hWK hKM hW (h := h) (x := x) (xl := x) (xr := z 0 + R' - 1)
      le_rfl (by omega) (by omega) hMR hV₁ hH hb₁ hb₀ hb₀' hbR hbL hf
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

/-- **The turn from the left side to the top side** (clockwise, at the top-left corner): on the
crossings of `H₁ = [z₀ - h - W, z₀ - R - δ] × [y, y + W]`, of the band
`V = [z₀ - h - W, z₀ - h] × [y, z₁ + R' - 1]` and of the top cap on the columns
`[z₀ - h - W, z₀ - h]`, a fenced arm ending on the left side in the rows `[y, y + W]` is continued
to a point of the top side of `B_{R'}(z)` in those columns with an outer fence `(M', K')`. -/
theorem exists_walk_turn_left_top (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hW : 1 ≤ W)
    (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {h y : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R')
    (hH₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W, y]
      ![z 0 - R - cond col 0 1, y + W])
    (hV : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - h - W, y] ![z 0 - h, z 1 + R' - 1])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W, z 1 + R' - M']
      ![z 0 - h, z 1 + R' - 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - h - W, z 1 + R' - M']
      ![z 0 - h, z 1 + R' + M'])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - h - W - K', z 1 + R' + 1]
      ![z 0 - h + K', z 1 + R' + M'])
    (hb₀ : b 0 = z 0 - R - cond col 0 1) (hb₁ : y ≤ b 1) (hb₁' : b 1 ≤ y + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y' : LatticeSite 2) (P : (zdGraph 2).Walk x' y'), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        (y ≤ v 1 ∧ v 1 ≤ y + W ∧ z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - R - cond col 0 1) ∨
        (z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - h ∧ y ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y') ∧
      y' ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y' 1 = z 1 + R' ∧ z 0 - h - W ≤ y' 0 ∧ y' 0 ≤ z 0 - h ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y' y') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₂, d₂, Q, p₂, hx₀, hx₀M, hQe, hp₂e, hQ, hp₂, hc₂, hd₂, ht⟩ :=
    exists_walk_leg2_left hM hWK hKM hW (h := h) (y := y) (yl := y) (yr := z 1 + R' - 1)
      le_rfl (by omega) hh hH₁ hV hb₀ hb₁ hb₁' hbT hbB hf
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

end Turns

/-! ### Corridors of the clockwise turns -/

section Corridors

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}
  {col : Bool} {z : LatticeSite 2} {r R R' M K M' K' W κ : ℕ}

/-- **The corridor of the turn from the top side to the right side** (`exists_walk_turn_top_right`;
five crossings, the first counted twice): on it every fenced arm ending on the top side in the bin
`[x, x + W]` is continued to the rows `[z₁ + h, z₁ + h + W]` of the right side of `B_{R'}(z)` with
an outer fence `(M', K')`. -/
theorem exists_corridor_turn_top_right (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {x h : ℤ}
    (hx₁ : z 0 - R + M ≤ x) (hx₂ : x + W ≤ z 0 + R - M)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R') (hMR : M ≤ R)
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
      b 0 + 2 * M ≤ z 0 + R)
    (hB' : ∀ v : LatticeSite 2, v 0 = z 0 + R' → z 1 + h ≤ v 1 → v 1 ≤ z 1 + h + W → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + M ≤ x) (hgh₀ : z 0 + R' + M' + 1 ≤ gh 0)
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
      ![x, z 1 + h],
      ![z 0 + R' - M', z 1 + h],
      ![z 0 + R' - M', z 1 + h],
      ![z 0 + R' + 1, z 1 + h - K'],
      ![x, z 1 + R]]
    ![![x + W, z 1 + h + W],
      ![z 0 + R' - 1, z 1 + h + W],
      ![z 0 + R' - 1, z 1 + h + W],
      ![z 0 + R' + M', z 1 + h + W],
      ![z 0 + R' + M', z 1 + h + W + K'],
      ![x + W, z 1 + h + W]]
    (Icc gl gh) {v | (x ≤ v 0 ∧ v 0 ≤ x + W ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W) ∨
      (x ≤ v 0 ∧ v 0 ≤ z 0 + R' + M' ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + h + W)} B B' ?_ ?_ ?_
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
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₀, hy₁, hy₁', hfen⟩ :=
      exists_walk_turn_top_right (R' := R') (M' := M') (K' := K') (h := h) hM hWK hKM hW hM' hWM'
          hh hhR hMR
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) hb₁ hb₀ hb₀' hbR hbL hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₀ hy₁ hy₁', hfen⟩

/-- **The corridor of the turn from the left side to the top side** (`exists_walk_turn_left_top`;
five crossings, the first counted twice): on it every fenced arm ending on the left side in the
bin `[y, y + W]` is continued to the columns `[z₀ - h - W, z₀ - h]` of the top side of `B_{R'}(z)`
with an outer fence `(M', K')`. -/
theorem exists_corridor_turn_left_top (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M') {y h : ℤ}
    (hy₁ : z 1 - R + M ≤ y) (hy₂ : y + W ≤ z 1 + R - M)
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + W + M' ≤ R')
    (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W) (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1))
    (hL : (R' : ℕ∞) ≤ L) (B B' : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, b 0 = z 0 - R - cond col 0 1 ∧ y ≤ b 1 ∧ b 1 ≤ y + W ∧
      z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)
    (hB' : ∀ v : LatticeSite 2, v 1 = z 1 + R' → z 0 - h - W ≤ v 0 → v 0 ≤ z 0 - h → v ∈ B')
    (gl gh : LatticeSite 2) (hgl₀ : gl 0 + K' ≤ z 0 - h - W)
    (hgh₀ : z 0 - R + M + K' + 1 ≤ gh 0)
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
    ![![z 0 - h - W, y],
      ![z 0 - h - W, y],
      ![z 0 - h - W, z 1 + R' - M'],
      ![z 0 - h - W, z 1 + R' - M'],
      ![z 0 - h - W - K', z 1 + R' + 1],
      ![z 0 - h - W, y]]
    ![![z 0 - R - cond col 0 1, y + W],
      ![z 0 - h, z 1 + R' - 1],
      ![z 0 - h, z 1 + R' - 1],
      ![z 0 - h, z 1 + R' + M'],
      ![z 0 - h + K', z 1 + R' + M'],
      ![z 0 - R - cond col 0 1, y + W]]
    (Icc gl gh) {v | (y ≤ v 1 ∧ v 1 ≤ y + W ∧ z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - R - cond col 0 1) ∨
      (z 0 - h - W ≤ v 0 ∧ v 0 ≤ z 0 - h ∧ y ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')} B B' ?_ ?_ ?_
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
    obtain ⟨hb₀, hb₁, hb₁', hbB, hbT⟩ := hB b hb
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_turn_left_top (R' := R') (M' := M') (K' := K') (h := h) hM hWK hKM hW hM'
          hWM' hh hhR
        (hω 0) (hω 1) (hω 2) (hω 3) (hω 4) hb₀ hb₁ hb₁' hbT hbB hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rw [hPout v hv hvout]
      exact ⟨hB' y hy₁ hy₀ hy₀', hfen⟩

end Corridors

end PercLib.Models.Planar
