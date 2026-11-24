/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (Theorem 11, the internal extremities).
-/
module

public import PercLib.Models.Planar.Arms.InnerFamilyGluing
public import PercLib.Models.Planar.Arms.OuterArmSeparation

/-!
# Arms from inner windows at one scale

For landing data `(η, θ)` and an annulus of bounded aspect ratio, `j` arms of prescribed colours
from `B_r(z)` to `∂B_R(z)` with inner positions in the windows `window (16 r + 8) θ η` occur with
probability bounded below, uniformly over the laws with crossing bounds. The arms are crossings of
straight corridors standing on the four sides of `B_r(z)`, one in the core of each window
(`IsLanding.exists_core`); the corridors read disjoint sets of edges.

Corridors are described in counterclockwise coordinates: on the side `m` of the cycle of inner
positions (`0` bottom, `1` right, `2` top, `3` left) the corridor `[Y, Y + W]` starts at distance
`Y` from the corner where the side begins, counterclockwise. The inner positions of its arm lie in
`[m (4r + 2) + 2Y, m (4r + 2) + 2(Y + W) + 2]` and its landing positions in
`[4mR + 2(Y + R - r) - 1, 4mR + 2(Y + W + R - r) + 1]`.

## Main results

* `exists_isCrossing_of_mem_crossing`: a crossing of a box in either orientation contains a
  crossing walk from `S` out of `T`.
* `exists_isArm_of_mem_ccw_corridor`: an arm of either colour in a straight corridor on any side,
  with its inner and landing positions.
* `exists_ccw_corridor`, `CrossingBounds.le_law_ccw_corridor`, `disjoint_ccw_corridors`: the boxes
  of the corridors, their crossing bounds and the disjointness of their read sets.
* `exists_pos_le_law_multiArmEventIn_window_inner`: **the one-scale bound with inner windows**.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Crossing walks in boxes -/

/-- **From a crossing of a box to a crossing walk, in either orientation.** A crossing of the box
`Icc lo hi` in the direction `d` in a configuration `ζ` contains a walk along edges of `ζ`, inside
the box, that crosses from `S` out of `T`, as soon as one of the two sides of the box across `d`
lies in `S` and the opposite one outside `T`. -/
theorem exists_isCrossing_of_mem_crossing {ζ : Config (LatticeSite 2)} {d : Fin 2}
    {lo hi : LatticeSite 2} {S T : Set (LatticeSite 2)} (h : ζ ∈ crossing d lo hi)
    (hST : ((∀ v ∈ Icc lo hi, v d = lo d → v ∈ S) ∧ ∀ v ∈ Icc lo hi, v d = hi d → v ∉ T) ∨
      ((∀ v ∈ Icc lo hi, v d = hi d → v ∈ S) ∧ ∀ v ∈ Icc lo hi, v d = lo d → v ∉ T)) :
    ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), γ.IsCrossing S T ∧
      (∀ e ∈ γ.edges, e ∈ ζ) ∧ ∀ v ∈ γ.support, v ∈ Icc lo hi := by
  obtain ⟨a₀, ha₀, ha₀d, b₀, hb₀, hb₀d, hab₀⟩ := h
  obtain ⟨a, b, ha, hbT, hab⟩ : ∃ a b, a ∈ S ∧ b ∉ T ∧
      ζ ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a b := by
    rcases hST with ⟨hS, hT⟩ | ⟨hS, hT⟩
    · exact ⟨a₀, b₀, hS a₀ ha₀ ha₀d, hT b₀ hb₀ hb₀d, hab₀⟩
    · exact ⟨b₀, a₀, hS b₀ hb₀ hb₀d, hT a₀ ha₀ ha₀d, by rw [localConn_comm]; exact hab₀⟩
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hab
  have hpE : ∀ e ∈ p.edges, e ∈ (zdGraph 2).edgeSet ∧ e ∈ ζ := by
    intro e he
    have he' := p.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at he'
    exact ⟨he'.1.2, he'.1.1⟩
  set p' := p.transfer (zdGraph 2) fun e he => (hpE e he).1 with hp'
  have hp'S : ∀ v ∈ p'.support, v ∈ Icc lo hi := by
    intro v hv
    rw [hp', SimpleGraph.Walk.support_transfer] at hv
    exact hp v hv
  have hp'E : ∀ e ∈ p'.edges, e ∈ ζ := by
    intro e he
    rw [hp', SimpleGraph.Walk.edges_transfer] at he
    exact (hpE e he).2
  -- first exit from `T`, then last visit to `S`
  obtain ⟨c₁, q, s, hqs, hc₁, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem (T := T) p' hbT
  obtain ⟨c₀, hc₀, q₀, t, hq₀t, ht⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem (S := S) q
    ⟨a, q.start_mem_support, ha⟩
  have htq : ∀ v ∈ t.support, v ∈ q.support := by
    intro v hv
    rw [← hq₀t, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  have hqp : ∀ v ∈ q.support, v ∈ p'.support := by
    intro v hv
    rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hv
  refine ⟨c₀, c₁, t, ⟨hc₀, ht, hc₁, fun v hv => hq v ?_⟩, fun e he => hp'E e ?_,
    fun v hv => hp'S v (hqp v (htq v hv))⟩
  · rw [← hq₀t, SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil t)]
    exact List.mem_append_right _ hv
  · rw [← hqs, SimpleGraph.Walk.edges_append]
    refine List.mem_append_left _ ?_
    rw [← hq₀t, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he

/-! ### Straight corridors on the four sides, in counterclockwise coordinates -/

section Corridors

variable {z : LatticeSite 2} {r R W : ℕ} {Y : ℤ} {m : ℕ} {col : Bool} {d : Fin 2}
  {lo hi : LatticeSite 2}

/-- **The box of a straight corridor** from the side `m` of `B_r(z)` (`0` bottom, `1` right,
`2` top, `3` left) to the same side of `B_R(z)`, at the counterclockwise coordinates `[Y, Y + W]`
from the corner where the side begins; for the dual colour, a box of faces. -/
theorem exists_ccw_corridor (m : ℕ) (hm : m ≤ 3) (col : Bool) (z : LatticeSite 2) (r R W : ℕ)
    (Y : ℤ) : ∃ (d : Fin 2) (lo hi : LatticeSite 2),
      (m = 0 ∧ d = 1 ∧ lo = ![z 0 - r + Y, z 1 - R - cond col 0 1] ∧
        hi = ![z 0 - r + Y + W, z 1 - r - cond col 0 1]) ∨
      (m = 1 ∧ d = 0 ∧ lo = ![z 0 + r, z 1 - r + Y] ∧ hi = ![z 0 + R, z 1 - r + Y + W]) ∨
      (m = 2 ∧ d = 1 ∧ lo = ![z 0 + r - Y - W, z 1 + r] ∧ hi = ![z 0 + r - Y, z 1 + R]) ∨
      (m = 3 ∧ d = 0 ∧ lo = ![z 0 - R - cond col 0 1, z 1 + r - Y - W] ∧
        hi = ![z 0 - r - cond col 0 1, z 1 + r - Y]) := by
  interval_cases m
  · exact ⟨1, _, _, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨0, _, _, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
  · exact ⟨1, _, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))⟩
  · exact ⟨0, _, _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))⟩

/-- **An arm of either colour in a straight corridor on any side.** A crossing, in the
configuration of colour `col`, of the corridor `[Y, Y + W]` on the side `m` (as in
`exists_ccw_corridor`), away from the corners of `B_r(z)`, contains an arm of colour `col` from
`B_r(z)` to `∂B_R(z)` inside the corridor, whose inner position lies in
`[m (4r + 2) + 2Y, m (4r + 2) + 2(Y + W) + 2]` and whose landing position lies in
`[4mR + 2(Y + R - r) - 1, 4mR + 2(Y + W + R - r) + 1]`. -/
theorem exists_isArm_of_mem_ccw_corridor {ω : Config (LatticeSite 2)} (hrR : r < R) (hY : 1 ≤ Y)
    (hYW : Y + W + 1 ≤ 2 * r)
    (hbox : (m = 0 ∧ d = 1 ∧ lo = ![z 0 - r + Y, z 1 - R - cond col 0 1] ∧
        hi = ![z 0 - r + Y + W, z 1 - r - cond col 0 1]) ∨
      (m = 1 ∧ d = 0 ∧ lo = ![z 0 + r, z 1 - r + Y] ∧ hi = ![z 0 + R, z 1 - r + Y + W]) ∨
      (m = 2 ∧ d = 1 ∧ lo = ![z 0 + r - Y - W, z 1 + r] ∧ hi = ![z 0 + r - Y, z 1 + R]) ∨
      (m = 3 ∧ d = 0 ∧ lo = ![z 0 - R - cond col 0 1, z 1 + r - Y - W] ∧
        hi = ![z 0 - r - cond col 0 1, z 1 + r - Y]))
    (h : cond col ω (dualConfig ω) ∈ crossing d lo hi) :
    ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), IsArm ω col z r (z - R) (z + R) γ ∧
      (∀ v ∈ γ.support, v ∈ Icc lo hi) ∧
      (m : ℤ) * (4 * r + 2) + 2 * Y ≤ innerPos z r col γ ∧
      innerPos z r col γ ≤ (m : ℤ) * (4 * r + 2) + 2 * (Y + W) + 2 ∧
      (m : ℤ) * (4 * R) + 2 * (Y + R - r) - 1 ≤ landingPos (z - R) (z + R) col γ ∧
      landingPos (z - R) (z + R) col γ ≤ (m : ℤ) * (4 * R) + 2 * (Y + W + R - r) + 1 := by
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) :=
    Icc_subset_Icc_add_one_sub_one hrR
  obtain ⟨a, b, γ, hγ, hγE, hγS⟩ : ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      γ.IsCrossing (cond col (Icc (z - (r : LatticeSite 2)) (z + r))
        (Icc (z - (r : LatticeSite 2) - 1) (z + r)))
        (cond col (Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
          (Icc (z - (R : LatticeSite 2)) (z + R - 1))) ∧
      (∀ e ∈ γ.edges, e ∈ cond col ω (dualConfig ω)) ∧ ∀ v ∈ γ.support, v ∈ Icc lo hi := by
    refine exists_isCrossing_of_mem_crossing h ?_
    cases col <;>
    rcases hbox with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp only [Bool.cond_true, Bool.cond_false] <;>
    first
    | (left
       exact ⟨fun v hv hvd => by
          rw [mem_Icc_two_iff] at hv ⊢
          simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one] at hv hvd ⊢
          omega,
        fun v hv hvd hvT => by
          rw [mem_Icc_two_iff] at hv hvT
          simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one] at hv hvd hvT
          omega⟩)
    | (right
       exact ⟨fun v hv hvd => by
          rw [mem_Icc_two_iff] at hv ⊢
          simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one] at hv hvd ⊢
          omega,
        fun v hv hvd hvT => by
          rw [mem_Icc_two_iff] at hv hvT
          simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one] at hv hvd hvT
          omega⟩)
  have hArm : IsArm ω col z r (z - R) (z + R) γ := isArm_iff_cond.2 ⟨hγ, hγE⟩
  obtain ⟨-, hin⟩ := hArm.innerPos_cases hB
  have ha := hγS a γ.start_mem_support
  have haS := hγ.start_mem
  have hb := hγS b γ.end_mem_support
  have hbT := hγ.end_notMem
  refine ⟨a, b, γ, hArm, hγS, ?_⟩
  rcases hbox with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ <;>
  cases col <;>
  simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
    Pi.natCast_apply, Pi.one_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at ha haS hb hbT hin <;>
  first
  | (rw [hArm.landingPos_eq_of_top hrR (by omega)]
     simp only [Bool.cond_true, Bool.cond_false]
     omega)
  | (rw [hArm.landingPos_eq_of_right hrR (by omega)]
     simp only [Bool.cond_true, Bool.cond_false]
     omega)
  | (rw [hArm.landingPos_eq_of_bottom hrR (by simp only [Bool.cond_true, Bool.cond_false]; omega)]
     simp only [Bool.cond_true, Bool.cond_false]
     omega)
  | (rw [hArm.landingPos_eq_of_left hrR (by simp only [Bool.cond_true, Bool.cond_false]; omega)]
     simp only [Bool.cond_true, Bool.cond_false]
     omega)

/-- **The crossing bound of a straight corridor**: with `R ≤ r + A W`, the corridor is crossed in
the configuration of its colour with probability at least `c A`. -/
theorem CrossingBounds.le_law_ccw_corridor {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c) {A : ℕ} (hW : 1 ≤ W) (hWL : (W : ℕ∞) ≤ L)
    (hrR : r ≤ R) (hA : R ≤ r + A * W)
    (hbox : (m = 0 ∧ d = 1 ∧ lo = ![z 0 - r + Y, z 1 - R - cond col 0 1] ∧
        hi = ![z 0 - r + Y + W, z 1 - r - cond col 0 1]) ∨
      (m = 1 ∧ d = 0 ∧ lo = ![z 0 + r, z 1 - r + Y] ∧ hi = ![z 0 + R, z 1 - r + Y + W]) ∨
      (m = 2 ∧ d = 1 ∧ lo = ![z 0 + r - Y - W, z 1 + r] ∧ hi = ![z 0 + r - Y, z 1 + R]) ∨
      (m = 3 ∧ d = 0 ∧ lo = ![z 0 - R - cond col 0 1, z 1 + r - Y - W] ∧
        hi = ![z 0 - r - cond col 0 1, z 1 + r - Y])) :
    c A ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing d lo hi) := by
  have hA' : (R : ℤ) ≤ r + A * W := by exact_mod_cast hA
  rcases hbox with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ |
    ⟨-, rfl, rfl, rfl⟩
  · exact hCB.le_law_box_one col A hW hWL (by omega) (by omega) (by omega)
  · exact hCB.le_law_box_zero col A hW hWL (by omega) (by omega) (by omega)
  · exact hCB.le_law_box_one col A hW hWL (by omega) (by omega) (by omega)
  · exact hCB.le_law_box_zero col A hW hWL (by omega) (by omega) (by omega)

/-- **The read sets of two straight corridors are disjoint**: corridors at least `2` from the
corners of `B_r(z)` and, on one side, more than `W + 1` apart have disjoint boxes, even when
enlarged by one at their upper corners. -/
theorem disjoint_ccw_corridors {Y₁ Y₂ : ℤ} {m₁ m₂ : ℕ} {col₁ col₂ : Bool} {d₁ d₂ : Fin 2}
    {lo₁ hi₁ lo₂ hi₂ : LatticeSite 2}
    (hbox₁ : (m₁ = 0 ∧ d₁ = 1 ∧ lo₁ = ![z 0 - r + Y₁, z 1 - R - cond col₁ 0 1] ∧
        hi₁ = ![z 0 - r + Y₁ + W, z 1 - r - cond col₁ 0 1]) ∨
      (m₁ = 1 ∧ d₁ = 0 ∧ lo₁ = ![z 0 + r, z 1 - r + Y₁] ∧ hi₁ = ![z 0 + R, z 1 - r + Y₁ + W]) ∨
      (m₁ = 2 ∧ d₁ = 1 ∧ lo₁ = ![z 0 + r - Y₁ - W, z 1 + r] ∧ hi₁ = ![z 0 + r - Y₁, z 1 + R]) ∨
      (m₁ = 3 ∧ d₁ = 0 ∧ lo₁ = ![z 0 - R - cond col₁ 0 1, z 1 + r - Y₁ - W] ∧
        hi₁ = ![z 0 - r - cond col₁ 0 1, z 1 + r - Y₁]))
    (hbox₂ : (m₂ = 0 ∧ d₂ = 1 ∧ lo₂ = ![z 0 - r + Y₂, z 1 - R - cond col₂ 0 1] ∧
        hi₂ = ![z 0 - r + Y₂ + W, z 1 - r - cond col₂ 0 1]) ∨
      (m₂ = 1 ∧ d₂ = 0 ∧ lo₂ = ![z 0 + r, z 1 - r + Y₂] ∧ hi₂ = ![z 0 + R, z 1 - r + Y₂ + W]) ∨
      (m₂ = 2 ∧ d₂ = 1 ∧ lo₂ = ![z 0 + r - Y₂ - W, z 1 + r] ∧ hi₂ = ![z 0 + r - Y₂, z 1 + R]) ∨
      (m₂ = 3 ∧ d₂ = 0 ∧ lo₂ = ![z 0 - R - cond col₂ 0 1, z 1 + r - Y₂ - W] ∧
        hi₂ = ![z 0 - r - cond col₂ 0 1, z 1 + r - Y₂]))
    (h₁ : 2 ≤ Y₁) (h₁' : Y₁ + W + 2 ≤ 2 * r) (h₂ : 2 ≤ Y₂) (h₂' : Y₂ + W + 2 ≤ 2 * r)
    (hgap : m₁ = m₂ → Y₁ + W + 1 < Y₂ ∨ Y₂ + W + 1 < Y₁) :
    Disjoint (Icc lo₁ (hi₁ + 1)) (Icc lo₂ (hi₂ + 1)) := by
  have hc1 : cond col₁ (0 : ℤ) 1 = 0 ∨ cond col₁ (0 : ℤ) 1 = 1 := by cases col₁ <;> simp
  have hc2 : cond col₂ (0 : ℤ) 1 = 0 ∨ cond col₂ (0 : ℤ) 1 = 1 := by cases col₂ <;> simp
  have hgap' : m₁ ≠ m₂ ∨ Y₁ + W + 1 < Y₂ ∨ Y₂ + W + 1 < Y₁ := by
    by_cases h : m₁ = m₂
    · exact Or.inr (hgap h)
    · exact Or.inl h
  clear hgap
  refine disjoint_Icc_of_lt ?_
  rcases hbox₁ with ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ |
    ⟨rfl, -, rfl, rfl⟩ <;>
  rcases hbox₂ with ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ |
    ⟨rfl, -, rfl, rfl⟩ <;>
  simp only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
  omega

end Corridors

/-! ### Corridors in the cores of the windows -/

section Cores

/-- **A corridor in the core of a window.** For a core window `[a, a + μ]` of a turn inside the
side `m` (`m / 4 + μ ≤ a`, `a + 2μ ≤ (m + 1) / 4`) of landing data `[θ, θ + η]`, `μ n ≥ 1`,
`16 n ≤ r` and `W n ≤ r`: the corridor at the counterclockwise coordinate
`Y = ⌈(a - m / 4)(16 r + 8) / 2⌉` of width `W` is at least `2` from the corners of the side of
`B_r(z)`, and the inner positions `[m (4r + 2) + 2Y, m (4r + 2) + 2(Y + W) + 2]` of its arms lie in
the window of the landing data on the cycle of perimeter `16 r + 8`. -/
theorem ccw_core_bounds {μ a θ η : ℚ} {m n r W : ℕ} {Y : ℤ} (hμ : 0 < μ)
    (hlo : (m : ℚ) / 4 + μ ≤ a) (hhi : a + 2 * μ ≤ ((m : ℚ) + 1) / 4) (hθa : θ ≤ a)
    (haη : a + μ ≤ θ + η) (hnμ : 1 ≤ (n : ℚ) * μ) (hr : 16 * n ≤ r) (hWn : W * n ≤ r)
    (hY : Y = ⌈(a - (m : ℚ) / 4) * (16 * r + 8) / 2⌉) :
    2 ≤ Y ∧ Y + W + 2 ≤ 2 * r ∧ θ * (16 * r + 8) ≤ (m : ℚ) * (4 * r + 2) + 2 * Y ∧
      (m : ℚ) * (4 * r + 2) + 2 * (Y + W) + 2 ≤ (θ + η) * (16 * r + 8) := by
  have hY1 : (a - (m : ℚ) / 4) * (16 * r + 8) / 2 ≤ Y := hY ▸ Int.le_ceil _
  have hY2 : (Y : ℚ) < (a - (m : ℚ) / 4) * (16 * r + 8) / 2 + 1 := hY ▸ Int.ceil_lt_add_one _
  have hP : (0 : ℚ) ≤ 16 * r + 8 := by positivity
  have hWμ : (W : ℚ) ≤ μ * r := by
    have h1 : (W : ℚ) * n ≤ r := by exact_mod_cast hWn
    have h2 : (W : ℚ) ≤ W * (n * μ) := le_mul_of_one_le_right (by positivity) hnμ
    have h3 : μ * ((W : ℚ) * n) ≤ μ * r := mul_le_mul_of_nonneg_left h1 hμ.le
    linarith
  have hμr : 16 ≤ μ * r := by
    have h1 : (16 * n : ℚ) ≤ r := by exact_mod_cast hr
    have h2 : μ * (16 * n) ≤ μ * r := mul_le_mul_of_nonneg_left h1 hμ.le
    linarith
  have hA : μ * (16 * r + 8) ≤ (a - (m : ℚ) / 4) * (16 * r + 8) :=
    mul_le_mul_of_nonneg_right (by linarith) hP
  have hB : (a - (m : ℚ) / 4) * (16 * r + 8) ≤ (1 / 4 - 2 * μ) * (16 * r + 8) :=
    mul_le_mul_of_nonneg_right (by linarith) hP
  have hC : θ * (16 * r + 8) ≤ a * (16 * r + 8) := mul_le_mul_of_nonneg_right hθa hP
  have hD : (a + μ) * (16 * r + 8) ≤ (θ + η) * (16 * r + 8) := mul_le_mul_of_nonneg_right haη hP
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · have : (2 : ℚ) ≤ Y := by linarith
    exact_mod_cast this
  · have : (Y : ℚ) + W + 2 ≤ 2 * r := by linarith
    exact_mod_cast this

/-- **Two corridors in the cores of two windows on one side** (`ccw_core_bounds`) are more than
`W + 1` apart when the core windows are at least `2μ` apart. -/
theorem ccw_core_gap {μ a a' : ℚ} {m n r W : ℕ} {Y Y' : ℤ} (hμ : 0 < μ) (h : a + 2 * μ ≤ a')
    (hnμ : 1 ≤ (n : ℚ) * μ) (hr : 16 * n ≤ r) (hWn : W * n ≤ r)
    (hY : Y = ⌈(a - (m : ℚ) / 4) * (16 * r + 8) / 2⌉)
    (hY' : Y' = ⌈(a' - (m : ℚ) / 4) * (16 * r + 8) / 2⌉) : Y + W + 1 < Y' := by
  have hY2 : (Y : ℚ) < (a - (m : ℚ) / 4) * (16 * r + 8) / 2 + 1 := hY ▸ Int.ceil_lt_add_one _
  have hY1 : (a' - (m : ℚ) / 4) * (16 * r + 8) / 2 ≤ Y' := hY' ▸ Int.le_ceil _
  have hP : (0 : ℚ) ≤ 16 * r + 8 := by positivity
  have hWμ : (W : ℚ) ≤ μ * r := by
    have h1 : (W : ℚ) * n ≤ r := by exact_mod_cast hWn
    have h2 : (W : ℚ) ≤ W * (n * μ) := le_mul_of_one_le_right (by positivity) hnμ
    have h3 : μ * ((W : ℚ) * n) ≤ μ * r := mul_le_mul_of_nonneg_left h1 hμ.le
    linarith
  have hμr : 16 ≤ μ * r := by
    have h1 : (16 * n : ℚ) ≤ r := by exact_mod_cast hr
    have h2 : μ * (16 * n) ≤ μ * r := mul_le_mul_of_nonneg_left h1 hμ.le
    linarith
  have hA : (2 * μ) * (16 * r + 8) ≤ (a' - a) * (16 * r + 8) :=
    mul_le_mul_of_nonneg_right (by linarith) hP
  have : (Y : ℚ) + W + 1 < Y' := by linarith
  exact_mod_cast this

end Cores

/-! ### The one-scale bound with inner windows -/

/-- **Arms from inner windows across an annulus of bounded aspect ratio** (the one-scale bound
with inner windows). For landing data `(η, θ)`, a colour sequence `σ` and a ratio `K` there are
`c₀ > 0` and `r₀` such that, uniformly over the laws with crossing bounds `c` up to scale `L`, the
`j`-arm event from `B_r(z)` to `∂B_R(z)` with inner positions in the windows
`window (16 r + 8) θ η` has probability at least `c₀` when `r₀ ≤ r < R ≤ K r` and `R ≤ L`. The
arms are crossings of straight corridors of width `⌊r / n⌋` (`n μ ≥ 1`) standing on the four sides
of `B_r(z)` in the cores of the windows (`IsLanding.exists_core`); the corridors read disjoint
sets of edges, so their crossing events are independent, each of probability at least
`c (2 K n)`. -/
theorem exists_pos_le_law_multiArmEventIn_window_inner {j : ℕ} (σ : Fin j → Bool) {η : ℚ}
    {θ : Fin j → ℚ} (hθ : IsLanding η θ) (c : ℕ → ℝ≥0∞) (K : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → r < R → R ≤ K * r →
        (R : ℕ∞) ≤ L →
        c₀ ≤ law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η) fun _ => univ) := by
  classical
  obtain ⟨μ, hμ, cs, a, hc3, hlo, hhi, hθa, haη, hgap, hmono⟩ := hθ.exists_core
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈1 / μ⌉₊ := ⟨_, rfl⟩
  have hnμ : 1 ≤ (n : ℚ) * μ := by
    have : 1 / μ ≤ n := hn ▸ Nat.le_ceil _
    rw [div_le_iff₀ hμ] at this
    exact this
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_ceil_iff]
    positivity
  by_cases hc : 0 < c (2 * K * n)
  swap
  · exact ⟨1, one_pos, 0, fun q L hCB => absurd (hCB.pos _) hc⟩
  refine ⟨c (2 * K * n) ^ j, ENNReal.pow_pos hc j, 16 * n, ?_⟩
  intro q L hCB z r R hr hrR hRK hRL
  -- the width of the corridors
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = r / n := ⟨_, rfl⟩
  have hWn : W * n ≤ r := hW ▸ Nat.div_mul_le_self r n
  have hWn' : r < W * n + n := hW ▸ Nat.lt_div_mul_add (by omega)
  have hW1 : 1 ≤ W := by
    rw [hW]
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  -- the counterclockwise coordinates of the corridors
  obtain ⟨Y, hY⟩ : ∃ Y : Fin j → ℤ,
      ∀ i, Y i = ⌈(a i - (cs i : ℚ) / 4) * (16 * r + 8) / 2⌉ := ⟨_, fun _ => rfl⟩
  have hb := fun i => ccw_core_bounds hμ (hlo i) (hhi i) (hθa i) (haη i) hnμ hr hWn (hY i)
  have hgapY : ∀ i l, i < l → cs i = cs l → Y i + W + 1 < Y l := fun i l hil hcs =>
    ccw_core_gap hμ (hgap i l hil) hnμ hr hWn (hY i) (by rw [hY l, hcs])
  have hgapY' : ∀ i l, i ≠ l → cs i = cs l → Y i + W + 1 < Y l ∨ Y l + W + 1 < Y i := by
    intro i l hil hcs
    rcases lt_or_gt_of_ne hil with h | h
    · exact Or.inl (hgapY i l h hcs)
    · exact Or.inr (hgapY l i h hcs.symm)
  choose d lo hi hbox using fun i => exists_ccw_corridor (cs i) (hc3 i) (σ i) z r R W (Y i)
  set E : Fin j → Set (Config (LatticeSite 2)) := fun i =>
    (fun ω : Config (LatticeSite 2) => cond (σ i) ω (dualConfig ω)) ⁻¹'
      crossing (d i) (lo i) (hi i) with hE
  have hdisj : ∀ i k, i ≠ k → Disjoint (Icc (lo i) (hi i + 1)) (Icc (lo k) (hi k + 1)) :=
    fun i k hik => disjoint_ccw_corridors (hbox i) (hbox k) (hb i).1 (hb i).2.1 (hb k).1
      (hb k).2.1 (hgapY' i k hik)
  -- the corridor events give the arms
  have hsub : (⋂ i, E i) ⊆ multiArmEventIn σ z r R (window (16 * r + 8) θ η) fun _ => univ := by
    intro ω hω
    rw [mem_iInter] at hω
    choose a' b' γ hγ hsupp hin1 hin2 hl1 hl2 using fun i =>
      exists_isArm_of_mem_ccw_corridor (ω := ω) hrR (by have := (hb i).1; omega)
        (by have := (hb i).2.1; omega) (hbox i) (hω i)
    have hcol : ∀ i k, i ≠ k → ∀ v ∈ (γ i).support, v ∉ (γ k).support := by
      intro i k hik v hv hv'
      have h₁ : v ∈ Icc (lo i) (hi i + 1) := by
        have := hsupp i v hv
        exact ⟨this.1, fun l => (this.2 l).trans (by simp)⟩
      have h₂ : v ∈ Icc (lo k) (hi k + 1) := by
        have := hsupp k v hv'
        exact ⟨this.1, fun l => (this.2 l).trans (by simp)⟩
      exact Set.disjoint_left.1 (hdisj i k hik) h₁ h₂
    have hlt : ∀ i k : Fin j, i < k → landingPos (z - R) (z + R) (σ i) (γ i) <
        landingPos (z - R) (z + R) (σ k) (γ k) := by
      intro i k hik
      have h₁ := hl2 i
      have h₂ := hl1 k
      have hbi := (hb i).2.1
      have hbk := (hb k).1
      have hrR' : (r : ℤ) < R := by exact_mod_cast hrR
      rcases (hmono i k hik.le).lt_or_eq with hlt' | heq
      · have hp : ((cs i : ℤ) + 1) * (4 * R) ≤ (cs k : ℤ) * (4 * R) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hlt') (by positivity)
        linarith
      · have := hgapY i k hik heq
        rw [heq] at h₁
        linarith
    refine ⟨a', b', γ, hγ, ⟨fun i k hik _ _ v hv => hcol i k hik v (List.mem_of_mem_tail hv),
      fun i k hik _ _ v hv => hcol i k hik v hv⟩, fun i => ⟨?_, mem_univ _⟩,
      fun i k l hik hkl => Int.sbtw_iff.2 (Or.inl ⟨hlt i k hik, hlt k l hkl⟩)⟩
    obtain ⟨-, -, hb3, hb4⟩ := hb i
    have h₁ : (((cs i : ℤ) * (4 * r + 2) + 2 * Y i : ℤ) : ℚ) ≤ innerPos z r (σ i) (γ i) := by
      exact_mod_cast hin1 i
    have h₂ : (innerPos z r (σ i) (γ i) : ℚ) ≤ (((cs i : ℤ) * (4 * r + 2) + 2 * (Y i + W) + 2 :
        ℤ) : ℚ) := by
      exact_mod_cast hin2 i
    push_cast at h₁ h₂
    rw [mem_window_iff]
    push_cast
    constructor <;> linarith
  -- independence of the corridor events
  set P : Fin j → Set (Sym2 (LatticeSite 2)) := fun i =>
    {e | ∀ v ∈ e, v ∈ Icc (lo i) (hi i + 1)} with hP
  have hPd : Pairwise (Function.onFun Disjoint P) := by
    intro i k hik
    rw [Function.onFun, Set.disjoint_left]
    intro e hei hek
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨(Quot.out e).1, Sym2.out_fst_mem e⟩
    exact Set.disjoint_left.1 (hdisj i k hik) (hei v hv) (hek v hv)
  have hEm : ∀ i, MeasurableSet (E i) := fun i =>
    measurableSet_preimage_cond_crossing (σ i) (d i) (lo i) (hi i)
  have hEd : ∀ i, ∀ ω ω', ω ∩ P i = ω' ∩ P i → (ω ∈ E i ↔ ω' ∈ E i) := by
    intro i ω ω' h
    refine cond_mem_crossing_iff_of_agree (σ i) (d i) (lo i) (hi i) fun e he _ _ => ?_
    have heP : e ∈ P i := fun v hv => mem_Icc_add_one_of_mem_Icc_add_cond (σ i) (he v hv)
    constructor
    · intro h'
      exact ((Set.ext_iff.1 h e).1 ⟨h', heP⟩).1
    · intro h'
      exact ((Set.ext_iff.1 h e).2 ⟨h', heP⟩).1
  have hind : law q (⋂ i, E i) = ∏ i, law q (E i) :=
    PercLib.Probability.prodBernoulli_iInter_fin_of_determined q hPd hEm hEd
  -- each corridor is crossed with probability at least `c (2 K n)`
  have hWL : (W : ℕ∞) ≤ L := le_trans (by exact_mod_cast (show W ≤ R by
    have : W ≤ W * n := Nat.le_mul_of_pos_right W (by omega)
    omega)) hRL
  have hRA : R ≤ r + 2 * K * n * W := by
    have h₁ : K * r ≤ K * (W * n + n) := Nat.mul_le_mul_left K hWn'.le
    have h₂ : K * n * 1 ≤ K * n * W := Nat.mul_le_mul_left _ hW1
    have e₁ : K * (W * n + n) = K * n * W + K * n * 1 := by ring
    have e₂ : 2 * K * n * W = K * n * W + K * n * W := by ring
    rw [e₁] at h₁
    rw [e₂]
    omega
  have hle : ∀ i, c (2 * K * n) ≤ law q (E i) := fun i =>
    hCB.le_law_ccw_corridor hW1 hWL hrR.le hRA (hbox i)
  calc c (2 * K * n) ^ j = ∏ _i : Fin j, c (2 * K * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, law q (E i) := Finset.prod_le_prod fun i _ => hle i
    _ = law q (⋂ i, E i) := hind.symm
    _ ≤ _ := measure_mono hsub

end PercLib.Models.Planar
