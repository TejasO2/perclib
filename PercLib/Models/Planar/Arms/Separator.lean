/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (one-arm bounds, pp. 23-24); B. Bollobás and
O. Riordan, A short proof of the Harris-Kesten theorem, Bull. London Math. Soc. 38 (2006),
470-484 (arXiv math/0410359v3).
-/
module

public import PercLib.Models.Planar.Arms.Defs
public import PercLib.Models.Planar.RSW

/-!
# Open circuits in annuli of `ℤ²`

The four-strip event `fourStrip z n` of `Arms/Defs.lean` asks for long-direction open crossings
of the four strips of the annulus `2n ≤ ‖v - z‖∞ ≤ 4n`: left-right crossings of the top and
bottom strips `z + [-4n, 4n] × [2n, 4n]` and `z + [-4n, 4n] × [-4n, -2n]`, bottom-top crossings
of the right and left strips `z + [2n, 4n] × [-4n, 4n]` and `z + [-4n, -2n] × [-4n, 4n]`. It
plays the part of an open circuit around the box `B_{2n}(z) = z + [-2n, 2n]²` inside the box
`B_{4n}(z)`; the circuit itself is never extracted.

* **The crossings meet.** A left-right crossing of the top or bottom strip is also a left-right
  crossing of `B_{4n}(z)`, and a bottom-top crossing of the left or right strip a bottom-top
  crossing of `B_{4n}(z)`. By the gluing lemma of `Gluing.lean`
  (`inter_edgeSet_mem_localConn_of_crossings`) the four crossings are joined to each other
  inside `B_{4n}(z)`.
* **Circuit gluing** (`inter_edgeSet_mem_localConn_of_mem_fourStrip`). On the four-strip event,
  two open paths inside `B_{4n}(z)`, each from a vertex of `B_{2n}(z)` to the boundary of
  `B_{4n}(z)`, are joined inside `B_{4n}(z)`. A path from `B_{2n}(z)` to, say, the top side of
  `B_{4n}(z)` has a segment crossing the top strip from bottom to top (discrete intermediate
  value theorem along a walk, `SimpleGraph.Walk.exists_walk_mem_Icc`), and that segment meets
  the left-right crossing of the top strip, again by the gluing lemma. The other sides are the
  same with the roles of the coordinates and their signs changed.
* **Escape form** (`inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn`). The same for
  two open paths confined to no box, from `B_{2n}(z)` to vertices outside `B_{4n - 1}(z)`: each
  path, stopped on first reaching the boundary of `B_{4n}(z)`
  (`exists_boundary_mem_localConn_of_mem_conn`), is an arm of the first kind.
* **T4: circuits with probability bounded below** (`exists_pos_le_law_fourStrip`). At the
  self-dual point, where every edge is open with probability `1/2`, the four-strip event has
  probability at least a constant `c₀ > 0`, uniformly in the centre `z` and in `n ≥ 1`: each
  strip is an `8n × 2n` box crossed in its long direction, which has probability at least `c` by
  RSW (`exists_pos_le_law_crossing`), and Harris's inequality for the four increasing crossings
  (`prodBernoulli_harris`, tag X5SS) gives `c₀ = c⁴`.

This is the circuit construction of the one-arm bounds (wiki tag XB1U, "Extending an arm and
blocking it"), with the circuit replaced by the four crossings: the wiki's simple circuit is
used only through the fact that every arm crossing the annulus meets it, which is what circuit
gluing proves.

## Main results

* `PercLib.Models.Planar.inter_edgeSet_mem_localConn_of_mem_fourStrip`
* `PercLib.Models.Planar.inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn`
* `PercLib.Models.Planar.exists_pos_le_law_fourStrip`
* `PercLib.Models.Planar.exists_boundary_mem_localConn_of_mem_conn`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Stopping on first reaching the boundary of a box -/

/-- **Stopping on first reaching the boundary of a box.** An open nearest-neighbour path, confined
to no box, from a point `x` of the box `c + [-(r - 1), r - 1]^d` to a point `y` outside it has
an initial segment that stays in the box `c + [-r, r]^d` and ends on its boundary. -/
theorem exists_boundary_mem_localConn_of_mem_conn {d : ℕ} {c x y : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} (hx : x ∈ Icc (c - r + 1) (c + r - 1))
    (hy : y ∉ Icc (c - r + 1) (c + r - 1)) (h : ω ∩ (zdGraph d).edgeSet ∈ conn x y) :
    ∃ v ∈ Icc (c - r) (c + r), (∃ i, v i = c i - r ∨ v i = c i + r) ∧
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (c - r) (c + r)) x v := by
  obtain ⟨u, hu, w, hw, hxu, huw⟩ := exists_first_exit _ hx hy h
  have hadj : (zdGraph d).Adj u w := (SimpleGraph.mem_edgeSet _).1 huw.2
  have hwu := apply_le_apply_add_one_of_adj hadj
  have huw' := apply_le_apply_add_one_of_adj hadj.symm
  have hSB : Icc (c - r + 1) (c + r - 1) ⊆ Icc (c - r) (c + r) := by
    intro v hv
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      Pi.one_apply] at hv ⊢
    exact ⟨fun j => by have := hv.1 j; omega, fun j => by have := hv.2 j; omega⟩
  have hu' := hu
  simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Pi.one_apply, not_and_or, not_forall, not_le] at hu' hw
  have hwB : w ∈ Icc (c - r) (c + r) := by
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    exact ⟨fun j => by have := hu'.1 j; have := huw' j; omega,
      fun j => by have := hu'.2 j; have := hwu j; omega⟩
  have hwbd : ∃ i, w i = c i - r ∨ w i = c i + r := by
    rcases hw with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i, Or.inl (by have := hu'.1 i; have := huw' i; omega)⟩
    · exact ⟨i, Or.inr (by have := hu'.2 i; have := hwu i; omega)⟩
  refine ⟨w, hwB, hwbd, localConn_trans (localConn_mono_set hSB x u ⟨hx, hu, hxu⟩) ?_⟩
  exact ⟨hSB hu, hwB, SimpleGraph.Adj.reachable ((openGraph_adj_iff _ u w).2 ⟨huw, hadj.ne⟩)⟩

/-! ### Circuit gluing -/

/-- **Circuit gluing.** On the four-strip event of the annulus `2n ≤ ‖v - z‖∞ ≤ 4n`, two open
paths inside the box `B_{4n}(z) = z + [-4n, 4n]²`, each from a vertex of the inner box
`B_{2n}(z)` to a vertex on the boundary of `B_{4n}(z)`, are joined inside `B_{4n}(z)`. -/
theorem inter_edgeSet_mem_localConn_of_mem_fourStrip {ω : Config (LatticeSite 2)}
    {z : LatticeSite 2} {n : ℕ} (hω : ω ∈ fourStrip z n) {a a' b b' : LatticeSite 2}
    (ha : a ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (ha' : a' ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (hb : ∃ i, b i = z i - (4 * n : ℕ) ∨ b i = z i + (4 * n : ℕ))
    (hb' : ∃ i, b' i = z i - (4 * n : ℕ) ∨ b' i = z i + (4 * n : ℕ))
    (hab : ω ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2))) a b)
    (ha'b' : ω ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2))) a' b') :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2))) a a' := by
  classical
  -- radius zero: both points are the centre
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : ∀ v ∈ Icc (z - ((2 * 0 : ℕ) : LatticeSite 2)) (z + ((2 * 0 : ℕ) : LatticeSite 2)),
        v = z := fun v hv => by simpa using hv
    rw [hz a ha, hz a' ha', localConn_self (by simp)]
    exact mem_univ _
  set B : Set (LatticeSite 2) :=
    Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2)) with hBdef
  -- coordinates of the boxes involved
  have hbox : ∀ (r : ℕ) (v : LatticeSite 2),
      v ∈ Icc (z - (r : LatticeSite 2)) (z + (r : LatticeSite 2)) ↔
        z 0 - r ≤ v 0 ∧ v 0 ≤ z 0 + r ∧ z 1 - r ≤ v 1 ∧ v 1 ≤ z 1 + r := by
    intro r v
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  have hB : ∀ v : LatticeSite 2, v ∈ B ↔
      z 0 - (4 * n : ℕ) ≤ v 0 ∧ v 0 ≤ z 0 + (4 * n : ℕ) ∧ z 1 - (4 * n : ℕ) ≤ v 1 ∧
        v 1 ≤ z 1 + (4 * n : ℕ) := fun v => by
    rw [hBdef]
    exact hbox (4 * n) v
  have hS : ∀ (v : LatticeSite 2) (p q r s : ℤ), v ∈ Icc (z + ![p, q]) (z + ![r, s]) ↔
      z 0 + p ≤ v 0 ∧ v 0 ≤ z 0 + r ∧ z 1 + q ≤ v 1 ∧ v 1 ≤ z 1 + s := by
    intro v p q r s
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hSB : ∀ p q r s : ℤ, -(4 * (n : ℤ)) ≤ p → r ≤ 4 * n → -(4 * (n : ℤ)) ≤ q →
      s ≤ 4 * n → Icc (z + ![p, q]) (z + ![r, s]) ⊆ B := by
    intro p q r s hp hr hq hs v hv
    rw [hS] at hv
    rw [hB]
    omega
  -- the four crossings
  obtain ⟨⟨aT, -, haT0, bT, -, hbT0, hTc⟩, ⟨aD, -, haD0, bD, -, hbD0, hDc⟩,
    ⟨aR, -, haR1, bR, -, hbR1, hRc⟩, ⟨aL, -, haL1, bL, -, hbL1, hLc⟩⟩ := mem_fourStrip_iff.1 hω
  have hTB := hSB (-4 * n) (2 * n) (4 * n) (4 * n) (by omega) le_rfl (by omega) le_rfl
  have hDB := hSB (-4 * n) (-4 * n) (4 * n) (-2 * n) (by omega) le_rfl (by omega) (by omega)
  have hRB := hSB (2 * n) (-4 * n) (4 * n) (4 * n) (by omega) le_rfl (by omega) le_rfl
  have hLB := hSB (-4 * n) (-4 * n) (-2 * n) (4 * n) (by omega) (by omega) (by omega) le_rfl
  -- gluing a left-right and a bottom-top crossing of `B`
  have hglueB : ∀ {p p' r r' : LatticeSite 2}, ω ∩ (zdGraph 2).edgeSet ∈ localConn B p p' →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn B r r' → p 0 = z 0 - (4 * n : ℕ) →
      p' 0 = z 0 + (4 * n : ℕ) → r 1 = z 1 - (4 * n : ℕ) → r' 1 = z 1 + (4 * n : ℕ) →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn B p r := by
    intro p p' r r' hpp' hrr' hp hp' hr hr'
    refine inter_edgeSet_mem_localConn_of_crossings (lo := z - ((4 * n : ℕ) : LatticeSite 2))
      (hi := z + ((4 * n : ℕ) : LatticeSite 2)) ?_ hpp' hrr' ?_ ?_ ?_ ?_
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      omega
    · simpa only [Pi.sub_apply, Pi.natCast_apply] using hp
    · simpa only [Pi.add_apply, Pi.natCast_apply] using hp'
    · simpa only [Pi.sub_apply, Pi.natCast_apply] using hr
    · simpa only [Pi.add_apply, Pi.natCast_apply] using hr'
  simp only [Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at haT0 hbT0 haD0 hbD0 haR1 hbR1 haL1 hbL1
  have hTR : ω ∩ (zdGraph 2).edgeSet ∈ localConn B aT aR :=
    hglueB (localConn_mono_set hTB _ _ hTc) (localConn_mono_set hRB _ _ hRc) (by omega)
      (by omega) (by omega) (by omega)
  have hTL : ω ∩ (zdGraph 2).edgeSet ∈ localConn B aT aL :=
    hglueB (localConn_mono_set hTB _ _ hTc) (localConn_mono_set hLB _ _ hLc) (by omega)
      (by omega) (by omega) (by omega)
  have hDR : ω ∩ (zdGraph 2).edgeSet ∈ localConn B aD aR :=
    hglueB (localConn_mono_set hDB _ _ hDc) (localConn_mono_set hRB _ _ hRc) (by omega)
      (by omega) (by omega) (by omega)
  rw [localConn_comm] at hTR hTL
  -- every arm from `B_{2n}(z)` to the boundary of `B` is joined to the start of the top crossing
  have harm : ∀ x y : LatticeSite 2,
      x ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)) →
      (∃ i, y i = z i - (4 * n : ℕ) ∨ y i = z i + (4 * n : ℕ)) →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn B x y →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn B x aT := by
    intro x y hx hy hxy
    obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hxy
    have hx' := (hbox (2 * n) x).1 hx
    -- `x` is joined inside `B` to every vertex of the walk
    have hpre : ∀ v ∈ p.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn B x v := fun v hv =>
      mem_localConn_iff_exists_walk.2 ⟨p.takeUntil v hv,
        fun w hw => hp w (p.support_takeUntil_subset_support hv hw)⟩
    have hpB : ∀ v ∈ p.support, z 0 - (4 * n : ℕ) ≤ v 0 ∧ v 0 ≤ z 0 + (4 * n : ℕ) ∧
        z 1 - (4 * n : ℕ) ≤ v 1 ∧ v 1 ≤ z 1 + (4 * n : ℕ) := fun v hv => (hB v).1 (hp v hv)
    rw [Fin.exists_fin_two] at hy
    rcases hy with (hy | hy) | (hy | hy)
    · -- `y` on the left side: a segment crosses the left strip from right to left
      have hfx : -x 0 ≤ 2 * (n : ℤ) - z 0 := by omega
      have hfy : 4 * (n : ℤ) - z 0 ≤ -y 0 := by omega
      obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => -v 0)
        (fun u v h => by have := coord_le_add_one_of_adj h.symm 0; omega) p hfx
        (by omega) hfy
      have hu' : -u 0 = 2 * (n : ℤ) - z 0 := hu
      have hw' : -w 0 = 4 * (n : ℤ) - z 0 := hw
      have hqS : ∀ v ∈ q.support,
          v ∈ Icc (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n]) := by
        intro v hv
        obtain ⟨hvp, hv₁, hv₂⟩ := hq v hv
        have hv₁' : 2 * (n : ℤ) - z 0 ≤ -v 0 := hv₁
        have hv₂' : -v 0 ≤ 4 * (n : ℤ) - z 0 := hv₂
        have := hpB v hvp
        rw [hS]
        omega
      have hwu : ω ∩ (zdGraph 2).edgeSet ∈
          localConn (Icc (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n])) w u := by
        rw [localConn_comm]
        exact mem_localConn_iff_exists_walk.2 ⟨q, hqS⟩
      have hglue := inter_edgeSet_mem_localConn_of_crossings
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega) hwu hLc
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      exact localConn_trans (hpre w (hq w (SimpleGraph.Walk.end_mem_support _)).1)
        (localConn_trans (localConn_mono_set hLB _ _ hglue) hTL)
    · -- `y` on the right side: a segment crosses the right strip from left to right
      have hfx : x 0 ≤ z 0 + 2 * (n : ℤ) := by omega
      have hfy : z 0 + 4 * (n : ℤ) ≤ y 0 := by omega
      obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => v 0)
        (fun u v h => coord_le_add_one_of_adj h 0) p hfx (by omega) hfy
      have hu' : u 0 = z 0 + 2 * (n : ℤ) := hu
      have hw' : w 0 = z 0 + 4 * (n : ℤ) := hw
      have hqS : ∀ v ∈ q.support,
          v ∈ Icc (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) := by
        intro v hv
        obtain ⟨hvp, hv₁, hv₂⟩ := hq v hv
        have hv₁' : z 0 + 2 * (n : ℤ) ≤ v 0 := hv₁
        have hv₂' : v 0 ≤ z 0 + 4 * (n : ℤ) := hv₂
        have := hpB v hvp
        rw [hS]
        omega
      have huw : ω ∩ (zdGraph 2).edgeSet ∈
          localConn (Icc (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n])) u w :=
        mem_localConn_iff_exists_walk.2 ⟨q, hqS⟩
      have hglue := inter_edgeSet_mem_localConn_of_crossings
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega) huw hRc
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      exact localConn_trans (hpre u (hq u (SimpleGraph.Walk.start_mem_support _)).1)
        (localConn_trans (localConn_mono_set hRB _ _ hglue) hTR)
    · -- `y` on the bottom side: a segment crosses the bottom strip from top to bottom
      have hfx : -x 1 ≤ 2 * (n : ℤ) - z 1 := by omega
      have hfy : 4 * (n : ℤ) - z 1 ≤ -y 1 := by omega
      obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => -v 1)
        (fun u v h => by have := coord_le_add_one_of_adj h.symm 1; omega) p hfx
        (by omega) hfy
      have hu' : -u 1 = 2 * (n : ℤ) - z 1 := hu
      have hw' : -w 1 = 4 * (n : ℤ) - z 1 := hw
      have hqS : ∀ v ∈ q.support,
          v ∈ Icc (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) := by
        intro v hv
        obtain ⟨hvp, hv₁, hv₂⟩ := hq v hv
        have hv₁' : 2 * (n : ℤ) - z 1 ≤ -v 1 := hv₁
        have hv₂' : -v 1 ≤ 4 * (n : ℤ) - z 1 := hv₂
        have := hpB v hvp
        rw [hS]
        omega
      have hwu : ω ∩ (zdGraph 2).edgeSet ∈
          localConn (Icc (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n])) w u := by
        rw [localConn_comm]
        exact mem_localConn_iff_exists_walk.2 ⟨q, hqS⟩
      have hglue := inter_edgeSet_mem_localConn_of_crossings
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega) hDc hwu
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      rw [localConn_comm] at hglue
      exact localConn_trans (hpre w (hq w (SimpleGraph.Walk.end_mem_support _)).1)
        (localConn_trans (localConn_mono_set hDB _ _ hglue) (localConn_trans hDR hTR))
    · -- `y` on the top side: a segment crosses the top strip from bottom to top
      have hfx : x 1 ≤ z 1 + 2 * (n : ℤ) := by omega
      have hfy : z 1 + 4 * (n : ℤ) ≤ y 1 := by omega
      obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => v 1)
        (fun u v h => coord_le_add_one_of_adj h 1) p hfx (by omega) hfy
      have hu' : u 1 = z 1 + 2 * (n : ℤ) := hu
      have hw' : w 1 = z 1 + 4 * (n : ℤ) := hw
      have hqS : ∀ v ∈ q.support,
          v ∈ Icc (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) := by
        intro v hv
        obtain ⟨hvp, hv₁, hv₂⟩ := hq v hv
        have hv₁' : z 1 + 2 * (n : ℤ) ≤ v 1 := hv₁
        have hv₂' : v 1 ≤ z 1 + 4 * (n : ℤ) := hv₂
        have := hpB v hvp
        rw [hS]
        omega
      have huw : ω ∩ (zdGraph 2).edgeSet ∈
          localConn (Icc (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n])) u w :=
        mem_localConn_iff_exists_walk.2 ⟨q, hqS⟩
      have hglue := inter_edgeSet_mem_localConn_of_crossings
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega) hTc huw
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
        (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      rw [localConn_comm] at hglue
      exact localConn_trans (hpre u (hq u (SimpleGraph.Walk.start_mem_support _)).1)
        (localConn_mono_set hTB _ _ hglue)
  have h₁ := harm a b ha hb hab
  have h₂ := harm a' b' ha' hb' ha'b'
  rw [localConn_comm] at h₂
  exact localConn_trans h₁ h₂

/-- **Circuit gluing, escape form.** On the four-strip event of the annulus
`2n ≤ ‖v - z‖∞ ≤ 4n`, two open paths confined to no box, each from a vertex of the inner box
`B_{2n}(z)` to a vertex outside the box `B_{4n - 1}(z)`, have their starting points joined inside
the box `B_{4n}(z)`. -/
theorem inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn {ω : Config (LatticeSite 2)}
    {z : LatticeSite 2} {n : ℕ} (hω : ω ∈ fourStrip z n) {a a' y y' : LatticeSite 2}
    (ha : a ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (ha' : a' ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (hy : y ∉ Icc (z - ((4 * n : ℕ) : LatticeSite 2) + 1) (z + ((4 * n : ℕ) : LatticeSite 2) - 1))
    (hy' : y' ∉
      Icc (z - ((4 * n : ℕ) : LatticeSite 2) + 1) (z + ((4 * n : ℕ) : LatticeSite 2) - 1))
    (hay : ω ∩ (zdGraph 2).edgeSet ∈ conn a y) (ha'y' : ω ∩ (zdGraph 2).edgeSet ∈ conn a' y') :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2))) a a' := by
  -- radius zero: both points are the centre
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : ∀ v ∈ Icc (z - ((2 * 0 : ℕ) : LatticeSite 2)) (z + ((2 * 0 : ℕ) : LatticeSite 2)),
        v = z := fun v hv => by simpa using hv
    rw [hz a ha, hz a' ha', localConn_self (by simp)]
    exact mem_univ _
  -- the inner box lies inside `B_{4n - 1}(z)`
  have hin : ∀ x ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)),
      x ∈ Icc (z - ((4 * n : ℕ) : LatticeSite 2) + 1) (z + ((4 * n : ℕ) : LatticeSite 2) - 1) := by
    intro x hx
    rw [mem_Icc_two_iff] at hx ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hx ⊢
    omega
  obtain ⟨b, -, hb, hab⟩ := exists_boundary_mem_localConn_of_mem_conn (hin a ha) hy hay
  obtain ⟨b', -, hb', ha'b'⟩ := exists_boundary_mem_localConn_of_mem_conn (hin a' ha') hy' ha'y'
  exact inter_edgeSet_mem_localConn_of_mem_fourStrip hω ha ha' hb hb' hab ha'b'

/-! ### Circuits with probability bounded below -/

/-- **T4: circuits with probability bounded below.** At the self-dual point, where every edge of
`ℤ²` is open with probability `1/2`, there is `c₀ > 0` such that the four-strip event of the
annulus `2n ≤ ‖v - z‖∞ ≤ 4n` has probability at least `c₀` for every centre `z` and every
`n ≥ 1`. -/
theorem exists_pos_le_law_fourStrip :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ (z : LatticeSite 2) (n : ℕ), 1 ≤ n → c₀ ≤ law q (fourStrip z n) := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_le_law_crossing 4
  refine ⟨c ^ 4, ENNReal.pow_pos hc 4, fun q hq z n hn => ?_⟩
  -- each strip is an `8n × 2n` box crossed in its long direction
  have hH : ∀ lo hi : LatticeSite 2, hi 0 = lo 0 + 8 * n → hi 1 = lo 1 + 2 * n →
      c ≤ law q (crossing 0 lo hi) := by
    intro lo hi h0 h1
    have h := hcq q hq 0 lo (2 * n) (by omega)
    rw [ite_eq_left rfl] at h
    convert h using 3
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.add_apply, Matrix.cons_val_zero, Nat.cast_mul, Nat.cast_ofNat]
      omega
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_mul,
        Nat.cast_ofNat]
      omega
  have hV : ∀ lo hi : LatticeSite 2, hi 0 = lo 0 + 2 * n → hi 1 = lo 1 + 8 * n →
      c ≤ law q (crossing 1 lo hi) := by
    intro lo hi h0 h1
    have h := hcq q hq 1 lo (2 * n) (by omega)
    rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] at h
    convert h using 3
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.add_apply, Matrix.cons_val_zero, Nat.cast_mul, Nat.cast_ofNat]
      omega
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_mul,
        Nat.cast_ofNat]
      omega
  have hT := hH (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have hD := hH (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have hR := hV (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have hL := hV (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  -- Harris's inequality for the four increasing crossings
  rw [fourStrip]
  set A₁ := crossing 0 (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) with hA₁
  set A₂ := crossing 0 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) with hA₂
  set A₃ := crossing 1 (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) with hA₃
  set A₄ := crossing 1 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n]) with hA₄
  have hu₁ : IsUpperSet A₁ := isUpperSet_crossing _ _ _
  have hu₂ : IsUpperSet A₂ := isUpperSet_crossing _ _ _
  have hu₃ : IsUpperSet A₃ := isUpperSet_crossing _ _ _
  have hu₄ : IsUpperSet A₄ := isUpperSet_crossing _ _ _
  have hm₁ : MeasurableSet A₁ := measurableSet_crossing _ _ _
  have hm₂ : MeasurableSet A₂ := measurableSet_crossing _ _ _
  have hm₃ : MeasurableSet A₃ := measurableSet_crossing _ _ _
  have hm₄ : MeasurableSet A₄ := measurableSet_crossing _ _ _
  calc c ^ 4 = c * c * c * c := by ring
    _ ≤ law q A₁ * law q A₂ * law q A₃ * law q A₄ := by gcongr
    _ ≤ law q (A₁ ∩ A₂) * law q A₃ * law q A₄ := by
        gcongr
        exact prodBernoulli_harris q hu₁ hu₂ hm₁ hm₂
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃) * law q A₄ := by
        gcongr
        exact prodBernoulli_harris q (hu₁.inter hu₂) hu₃ (hm₁.inter hm₂) hm₃
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃ ∩ A₄) :=
        prodBernoulli_harris q ((hu₁.inter hu₂).inter hu₃) hu₄ ((hm₁.inter hm₂).inter hm₃) hm₄

end PercLib.Models.Planar
