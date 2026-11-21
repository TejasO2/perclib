/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: G. Grimmett, Percolation, 2nd ed., Springer, 1999, Section 11.2
(planar duality); B. Bollobás and O. Riordan, Percolation, Cambridge University Press, 2006,
Chapter 3 (pp. 50-57) and Section 5.4.
The proof below is a discrete parity argument and does not follow either text.
-/
module

public import PercLib.Models.Planar.Defs

/-!
# Planar duality of crossings on the square lattice

For a box `R = [lo₀, hi₀] × [lo₁, hi₁]` of `ℤ²` and a configuration `ω`, **exactly one** of the
following holds:

* `R` has an open left-right crossing (`crossing 0 lo hi`);
* the matching dual box `R* = [lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]` has a dual-open bottom-top
  crossing in the dual configuration (`crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1]`).

Both halves are parity arguments; no planar topology is used.

* *Not both.* Given a dual-open path `σ` from the bottom to the top of `R*`, the parity of
  the number of times `σ` crosses the horizontal half-line to the left of a vertex `v` is `0`
  on the left side of `R`, `1` on its right side, and does not change along an open edge,
  because `σ` never crosses an open edge. So no open path joins the two sides.
* *At least one.* The corners of the faces in `R*` at the vertices of `R` form a box of the
  corner lattice, on which `hPartner` and `vPartner` (with the boundary edges wired) are
  involutions. Every corner has both partners in the box except its four extreme corners.
  If neither crossing existed, the corners whose vertex is joined to the left side of `R`
  and whose face is joined to the bottom of `R*` would form a set closed under both
  partners, except for exactly one extreme corner; counting it in pairs of partners twice
  gives a contradiction modulo two.

## Main results

* `notMem_crossing_one_dualConfig_of_mem_crossing_zero`: not both.
* `mem_crossing_one_dualConfig_of_notMem_crossing_zero`: at least one.
* `mem_crossing_zero_iff_dualConfig_notMem_crossing_one`: exactly one.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

/-! ### Two general lemmas -/

namespace SimpleGraph.Walk

variable {W : Type*} {G : SimpleGraph W}

/-- Telescoping along a walk: the sum over its darts of the increments of a function is the
increment between the endpoints. -/
theorem sum_map_darts_sub {M : Type*} [AddCommGroup M] (f : W → M) :
    ∀ {u v : W} (p : G.Walk u v), (p.darts.map fun δ => f δ.snd - f δ.fst).sum = f v - f u
  | _, _, .nil => by simp
  | _, _, .cons _ p => by
    rw [darts_cons, List.map_cons, List.sum_cons, sum_map_darts_sub f p]
    dsimp only
    abel

/-- Telescoping along a walk, modulo two. -/
theorem sum_map_darts_add_zmod_two (f : W → ZMod 2) {u v : W} (p : G.Walk u v) :
    (p.darts.map fun δ => f δ.fst + f δ.snd).sum = f u + f v := by
  have h : ∀ a b : ZMod 2, a + b = b - a := by decide
  simp only [h]
  exact sum_map_darts_sub f p

end SimpleGraph.Walk

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A connection inside `S` extends along an open pair whose new end lies in `S`. -/
theorem mem_localConn_of_mem_localConn_of_mem {S : Set V} {a v w : V} {ω : Config V}
    (h : ω ∈ localConn S a v) (hw : w ∈ S) (hvw : s(v, w) ∈ ω) : ω ∈ localConn S a w := by
  obtain ⟨ha, hv, hav⟩ := h
  refine ⟨ha, hw, ?_⟩
  by_cases hne : v = w
  · subst hne
    exact hav
  · exact hav.trans (SimpleGraph.Adj.reachable (G := (openGraph ω).induce S)
      (u := ⟨v, hv⟩) (v := ⟨w, hw⟩) ((openGraph_adj_iff ω v w).2 ⟨hvw, hne⟩))

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

/-! ### Coordinates -/

theorem cornerVertex_eq_vec (s : LatticeSite 2) :
    cornerVertex s = ![(s 0 + 1) / 2, (s 1 + 1) / 2] :=
  eq_vec_two_iff.2 ⟨rfl, rfl⟩

theorem cornerFace_eq_vec (s : LatticeSite 2) : cornerFace s = ![s 0 / 2, s 1 / 2] :=
  eq_vec_two_iff.2 ⟨rfl, rfl⟩

theorem sym2_vec_two_eq_swap {a b c d a' b' c' d' : ℤ} (h₁ : a = c') (h₂ : b = d')
    (h₃ : c = a') (h₄ : d = b') : s(![a, b], ![c, d]) = s(![a', b'], ![c', d']) := by
  rw [Sym2.eq_swap]
  exact sym2_vec_two_eq h₃ h₄ h₁ h₂

/-! ### One step of the partner maps -/

theorem cornerFace_hPartner_of_mem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerHEdge s ∈ ω) : cornerFace (hPartner ω s) = cornerFace s := by
  rw [hPartner_of_mem h, cornerFace_eq_vec, cornerFace_eq_vec]
  rw [eq_vec_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_true]
  rcases Int.emod_two_eq_zero_or_one (s 0) with hp | hp <;> omega

/-- Across an open horizontal edge, the vertices of a corner and of its partner are the ends
of that edge. -/
theorem sym2_cornerVertex_hPartner_of_mem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerHEdge s ∈ ω) : s(cornerVertex s, cornerVertex (hPartner ω s)) = cornerHEdge s := by
  rw [hPartner_of_mem h, cornerVertex_eq_vec, cornerVertex_eq_vec, cornerHEdge_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases Int.emod_two_eq_zero_or_one (s 0) with hp | hp
  · exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · exact sym2_vec_two_eq_swap (by omega) (by omega) (by omega) (by omega)

theorem cornerVertex_hPartner_of_notMem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerHEdge s ∉ ω) : cornerVertex (hPartner ω s) = cornerVertex s := by
  rw [hPartner_of_notMem h, cornerVertex_eq_vec, cornerVertex_eq_vec]
  rw [eq_vec_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
  rcases Int.emod_two_eq_zero_or_one (s 1) with hp | hp <;> omega

/-- Across a closed horizontal edge, the faces of a corner and of its partner are the ends of
the dual edge. -/
theorem sym2_cornerFace_hPartner_of_notMem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerHEdge s ∉ ω) :
    s(cornerFace s, cornerFace (hPartner ω s)) = dualEdge (cornerHEdge s) := by
  rw [hPartner_of_notMem h, cornerFace_eq_vec, cornerFace_eq_vec, cornerHEdge_eq,
    dualEdge_horizontal]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases Int.emod_two_eq_zero_or_one (s 1) with hp | hp
  · exact sym2_vec_two_eq_swap (by omega) (by omega) (by omega) (by omega)
  · exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

theorem cornerFace_vPartner_of_mem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerVEdge s ∈ ω) : cornerFace (vPartner ω s) = cornerFace s := by
  rw [vPartner_of_mem h, cornerFace_eq_vec, cornerFace_eq_vec]
  rw [eq_vec_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
  rcases Int.emod_two_eq_zero_or_one (s 1) with hp | hp <;> omega

/-- Across an open vertical edge, the vertices of a corner and of its partner are the ends of
that edge. -/
theorem sym2_cornerVertex_vPartner_of_mem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerVEdge s ∈ ω) : s(cornerVertex s, cornerVertex (vPartner ω s)) = cornerVEdge s := by
  rw [vPartner_of_mem h, cornerVertex_eq_vec, cornerVertex_eq_vec, cornerVEdge_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases Int.emod_two_eq_zero_or_one (s 1) with hp | hp
  · exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · exact sym2_vec_two_eq_swap (by omega) (by omega) (by omega) (by omega)

theorem cornerVertex_vPartner_of_notMem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerVEdge s ∉ ω) : cornerVertex (vPartner ω s) = cornerVertex s := by
  rw [vPartner_of_notMem h, cornerVertex_eq_vec, cornerVertex_eq_vec]
  rw [eq_vec_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_true]
  rcases Int.emod_two_eq_zero_or_one (s 0) with hp | hp <;> omega

/-- Across a closed vertical edge, the faces of a corner and of its partner are the ends of the
dual edge. -/
theorem sym2_cornerFace_vPartner_of_notMem {ω : Config (LatticeSite 2)} {s : LatticeSite 2}
    (h : cornerVEdge s ∉ ω) :
    s(cornerFace s, cornerFace (vPartner ω s)) = dualEdge (cornerVEdge s) := by
  rw [vPartner_of_notMem h, cornerFace_eq_vec, cornerFace_eq_vec, cornerVEdge_eq,
    dualEdge_vertical]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases Int.emod_two_eq_zero_or_one (s 0) with hp | hp
  · exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · exact sym2_vec_two_eq_swap (by omega) (by omega) (by omega) (by omega)

/-! ### Not both -/

/-- Parity of crossing a horizontal line, for one step of the dual lattice. -/
theorem ite_row_eq_add {f g : LatticeSite 2} (hfg : (zdGraph 2).Adj f g) (y : ℤ) :
    (if (f 1 = y - 1 ∧ g 1 = y) ∨ (f 1 = y ∧ g 1 = y - 1) then (1 : ZMod 2) else 0) =
      (if f 1 ≤ y - 1 then 1 else 0) + (if g 1 ≤ y - 1 then 1 else 0) := by
  rcases (zdGraph_two_adj_iff f g).1 hfg with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;>
    split_ifs <;> first | rfl | (exfalso; omega)

/-- Parity of crossing the boundary of a half-row of faces, for one step of the dual
lattice. -/
theorem ite_halfRow_eq_add {f g : LatticeSite 2} (hfg : (zdGraph 2).Adj f g) (x y : ℤ) :
    (if f 0 < x ∧ ((f 1 = y - 1 ∧ g 1 = y) ∨ (f 1 = y ∧ g 1 = y - 1)) then (1 : ZMod 2)
        else 0) +
      (if f 0 < x ∧ ((f 1 = y + 1 - 1 ∧ g 1 = y + 1) ∨ (f 1 = y + 1 ∧ g 1 = y + 1 - 1)) then 1
        else 0) +
      (if f 1 = y ∧ g 1 = y ∧ ((f 0 = x - 1 ∧ g 0 = x) ∨ (f 0 = x ∧ g 0 = x - 1)) then 1
        else 0) =
      (if f 1 = y ∧ f 0 < x then 1 else 0) + (if g 1 = y ∧ g 0 < x then 1 else 0) := by
  rcases (zdGraph_two_adj_iff f g).1 hfg with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;>
    split_ifs <;> first | rfl | (exfalso; omega)

/-- A dual step between rows `y - 1` and `y` in column `x` crosses the edge
`{(x, y), (x + 1, y)}`. -/
theorem sym2_eq_dualEdge_horizontal {f g : LatticeSite 2} (hfg : (zdGraph 2).Adj f g)
    {x y : ℤ} (hx : f 0 = x) (hy : (f 1 = y - 1 ∧ g 1 = y) ∨ (f 1 = y ∧ g 1 = y - 1)) :
    s(f, g) = dualEdge s(![x, y], ![x + 1, y]) := by
  rw [dualEdge_horizontal, eq_vec_two f, eq_vec_two g]
  rcases (zdGraph_two_adj_iff f g).1 hfg with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
  · exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · exact sym2_vec_two_eq_swap (by omega) (by omega) (by omega) (by omega)
  · omega
  · omega

/-- A dual step between columns `x - 1` and `x` in row `y` crosses the edge
`{(x, y), (x, y + 1)}`. -/
theorem sym2_eq_dualEdge_vertical {f g : LatticeSite 2} {x y : ℤ} (hf : f 1 = y)
    (hg : g 1 = y) (hx : (f 0 = x - 1 ∧ g 0 = x) ∨ (f 0 = x ∧ g 0 = x - 1)) :
    s(f, g) = dualEdge s(![x, y], ![x, y + 1]) := by
  rw [dualEdge_vertical, eq_vec_two f, eq_vec_two g]
  rcases hx with ⟨h0, h0'⟩ | ⟨h0, h0'⟩
  · exact sym2_vec_two_eq_swap (by omega) (by omega) (by omega) (by omega)
  · exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- **Not both.** An open left-right crossing of a box of `ℤ²` and a dual-open bottom-top
crossing of the matching dual box never occur together. -/
theorem notMem_crossing_one_dualConfig_of_mem_crossing_zero {lo hi : LatticeSite 2}
    {ω : Config (LatticeSite 2)} (hω : ω ∈ crossing 0 lo hi) :
    dualConfig ω ∉ crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] := by
  rintro ⟨c, hc, hc1, d, hd, hd1, hcd⟩
  obtain ⟨a, ha, ha0, b, hb, hb0, hab⟩ := hω
  obtain ⟨hcR, hdR, ⟨σ⟩⟩ := hcd
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc1 hd1
  set Rs : Set (LatticeSite 2) := Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] with hRs
  -- the steps of `σ`: dual-open edges of `ℤ²` between vertices of `Rs`
  have hdart : ∀ δ ∈ σ.darts, (zdGraph 2).Adj δ.fst.1 δ.snd.1 ∧
      s(δ.fst.1, δ.snd.1) ∈ dualConfig ω ∧ lo 0 ≤ δ.fst.1 0 ∧ δ.fst.1 0 ≤ hi 0 - 1 := by
    intro δ _
    have hadj := (openGraph_adj_iff _ _ _).1 δ.adj
    have hf := δ.fst.2
    rw [mem_Icc_two_iff] at hf
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
    exact ⟨hadj.1.2, hadj.1.1, hf.1, hf.2.1⟩
  -- `N x y`: the parity of the number of crossings by `σ` of the half-line to the left of
  -- `(x, y)`
  set N : ℤ → ℤ → ZMod 2 := fun x y => (σ.darts.map fun δ =>
    if δ.fst.1 0 < x ∧ ((δ.fst.1 1 = y - 1 ∧ δ.snd.1 1 = y) ∨
      (δ.fst.1 1 = y ∧ δ.snd.1 1 = y - 1)) then (1 : ZMod 2) else 0).sum with hN
  -- left side
  have hleft : ∀ y, N (lo 0) y = 0 := by
    intro y
    simp only [hN]
    refine List.sum_eq_zero fun t ht => ?_
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 ht
    rw [ite_eq_right]
    have := (hdart δ hδ).2.2.1
    omega
  -- right side
  have hright : ∀ y, lo 1 ≤ y → y ≤ hi 1 → N (hi 0) y = 1 := by
    intro y hy1 hy2
    simp only [hN]
    have hcongr : ∀ δ ∈ σ.darts,
        (if δ.fst.1 0 < hi 0 ∧ ((δ.fst.1 1 = y - 1 ∧ δ.snd.1 1 = y) ∨
          (δ.fst.1 1 = y ∧ δ.snd.1 1 = y - 1)) then (1 : ZMod 2) else 0) =
        (fun w : Rs => if w.1 1 ≤ y - 1 then (1 : ZMod 2) else 0) δ.fst +
          (fun w : Rs => if w.1 1 ≤ y - 1 then (1 : ZMod 2) else 0) δ.snd := by
      intro δ hδ
      have hδ' := hdart δ hδ
      rw [← ite_row_eq_add hδ'.1 y]
      exact if_congr ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩ rfl rfl
    rw [List.map_congr_left hcongr, SimpleGraph.Walk.sum_map_darts_add_zmod_two
      (fun w : Rs => if w.1 1 ≤ y - 1 then (1 : ZMod 2) else 0) σ]
    simp only [hc1, hd1]
    split_ifs <;> first | rfl | (exfalso; omega)
  -- open horizontal edges are not crossed
  have hhor : ∀ x y, s(![x, y], ![x + 1, y]) ∈ ω → N (x + 1) y = N x y := by
    intro x y he
    simp only [hN]
    congr 1
    refine List.map_congr_left fun δ hδ => ?_
    have hδ' := hdart δ hδ
    by_cases hx : δ.fst.1 0 = x ∧ ((δ.fst.1 1 = y - 1 ∧ δ.snd.1 1 = y) ∨
        (δ.fst.1 1 = y ∧ δ.snd.1 1 = y - 1))
    · exfalso
      have h := hδ'.2.1
      rw [sym2_eq_dualEdge_horizontal hδ'.1 hx.1 hx.2,
        dualEdge_mem_dualConfig_iff (horizontal_mem_edgeSet x y)] at h
      exact h he
    · exact if_congr ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩ rfl rfl
  -- open vertical edges inside the box are not crossed
  have hver : ∀ x y, lo 1 ≤ y → y + 1 ≤ hi 1 → s(![x, y], ![x, y + 1]) ∈ ω →
      N x (y + 1) = N x y := by
    intro x y hy1 hy2 he
    have hsum : N x y + N x (y + 1) = 0 := by
      simp only [hN]
      rw [← List.sum_map_add]
      have hcongr : ∀ δ ∈ σ.darts,
          ((if δ.fst.1 0 < x ∧ ((δ.fst.1 1 = y - 1 ∧ δ.snd.1 1 = y) ∨
              (δ.fst.1 1 = y ∧ δ.snd.1 1 = y - 1)) then (1 : ZMod 2) else 0) +
            (if δ.fst.1 0 < x ∧ ((δ.fst.1 1 = y + 1 - 1 ∧ δ.snd.1 1 = y + 1) ∨
              (δ.fst.1 1 = y + 1 ∧ δ.snd.1 1 = y + 1 - 1)) then (1 : ZMod 2) else 0)) =
          (fun w : Rs => if w.1 1 = y ∧ w.1 0 < x then (1 : ZMod 2) else 0) δ.fst +
            (fun w : Rs => if w.1 1 = y ∧ w.1 0 < x then (1 : ZMod 2) else 0) δ.snd := by
        intro δ hδ
        have hδ' := hdart δ hδ
        have h3 : (if δ.fst.1 1 = y ∧ δ.snd.1 1 = y ∧ ((δ.fst.1 0 = x - 1 ∧ δ.snd.1 0 = x) ∨
            (δ.fst.1 0 = x ∧ δ.snd.1 0 = x - 1)) then (1 : ZMod 2) else 0) = 0 := by
          refine ite_eq_right fun ⟨hf, hg, hx⟩ => ?_
          have h := hδ'.2.1
          rw [sym2_eq_dualEdge_vertical hf hg hx,
            dualEdge_mem_dualConfig_iff (vertical_mem_edgeSet x y)] at h
          exact h he
        rw [← ite_halfRow_eq_add hδ'.1 x y, h3, add_zero]
      rw [List.map_congr_left hcongr, SimpleGraph.Walk.sum_map_darts_add_zmod_two
        (fun w : Rs => if w.1 1 = y ∧ w.1 0 < x then (1 : ZMod 2) else 0) σ]
      simp only [hc1, hd1]
      split_ifs <;> first | rfl | (exfalso; omega)
    have h2 : ∀ p q : ZMod 2, p + q = 0 → q = p := by decide
    exact h2 _ _ hsum
  -- `N` is constant along open paths inside the box
  have hstep : ∀ v w : Icc lo hi,
      ((openGraph (ω ∩ (zdGraph 2).edgeSet)).induce (Icc lo hi)).Adj v w →
        N (w.1 0) (w.1 1) = N (v.1 0) (v.1 1) := by
    intro v w hvw
    have hadj := (openGraph_adj_iff _ _ _).1 hvw
    have hvR := v.2
    have hwR := w.2
    rw [mem_Icc_two_iff] at hvR hwR
    have he : s(v.1, w.1) ∈ ω := hadj.1.1
    rcases (zdGraph_two_adj_iff v.1 w.1).1 hadj.1.2 with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
    · rw [eq_vec_two v.1, eq_vec_two w.1] at he
      simp only [← h0, ← h1] at he ⊢
      exact hver (v.1 0) (v.1 1) (by omega) (by omega) he
    · rw [eq_vec_two v.1, eq_vec_two w.1, Sym2.eq_swap] at he
      simp only [h0, ← h1] at he ⊢
      exact (hver (w.1 0) (w.1 1) (by omega) (by omega) he).symm
    · rw [eq_vec_two v.1, eq_vec_two w.1] at he
      simp only [← h0, ← h1] at he ⊢
      exact hhor (v.1 0) (v.1 1) he
    · rw [eq_vec_two v.1, eq_vec_two w.1, Sym2.eq_swap] at he
      simp only [← h0, h1] at he ⊢
      exact (hhor (w.1 0) (w.1 1) he).symm
  have hwalk : ∀ {u w : Icc lo hi}
      (p : ((openGraph (ω ∩ (zdGraph 2).edgeSet)).induce (Icc lo hi)).Walk u w),
      N (w.1 0) (w.1 1) = N (u.1 0) (u.1 1) := by
    intro u w p
    induction p with
    | nil => rfl
    | cons h _ ih => exact ih.trans (hstep _ _ h)
  obtain ⟨haR, hbR, ⟨p₀⟩⟩ := hab
  have hπ := hwalk p₀
  have hb' := hb
  rw [mem_Icc_two_iff] at hb'
  simp only at hπ
  rw [hb0, ha0, hleft, hright _ hb'.2.2.1 hb'.2.2.2] at hπ
  exact absurd hπ (by decide)

/-! ### At least one -/

/-- **At least one.** If a box of `ℤ²` has no open left-right crossing, the matching dual box
has a dual-open bottom-top crossing. -/
theorem mem_crossing_one_dualConfig_of_notMem_crossing_zero {lo hi : LatticeSite 2}
    (hle : lo ≤ hi) {ω : Config (LatticeSite 2)} (hω : ω ∉ crossing 0 lo hi) :
    dualConfig ω ∈ crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] := by
  classical
  by_contra hTB
  have hle0 : lo 0 ≤ hi 0 := hle 0
  have hle1 : lo 1 ≤ hi 1 := hle 1
  rcases hle0.eq_or_lt with h0 | h0
  · exact hω (by rw [crossing_eq_univ_of_eq hle h0]; exact mem_univ _)
  set L := (zdGraph 2).edgeSet with hL
  set R : Set (LatticeSite 2) := Icc lo hi with hR
  set Rs : Set (LatticeSite 2) := Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] with hRs
  -- the vertices joined to the left side of `R` and the faces joined to the bottom of `Rs`
  set A : Set (LatticeSite 2) := {v | ∃ a ∈ R, a 0 = lo 0 ∧ ω ∩ L ∈ localConn R a v} with hA
  set B : Set (LatticeSite 2) :=
    {f | ∃ c ∈ Rs, c 1 = lo 1 - 1 ∧ dualConfig ω ∩ L ∈ localConn Rs c f} with hB
  have hAright : ∀ v ∈ A, v 0 ≠ hi 0 := by
    rintro v ⟨a, ha, ha0, hav⟩ hv0
    exact hω ⟨a, ha, ha0, v, hav.2.1, hv0, hav⟩
  have hBtop : ∀ f ∈ B, f 1 ≠ hi 1 := by
    rintro f ⟨c, hc, hc1, hcf⟩ hf1
    exact hTB ⟨c, hc, by simpa using hc1, f, hcf.2.1, by simpa using hf1, hcf⟩
  have hRiff : ∀ v : LatticeSite 2, v ∈ R ↔ lo 0 ≤ v 0 ∧ v 0 ≤ hi 0 ∧ lo 1 ≤ v 1 ∧ v 1 ≤ hi 1 :=
    fun v => mem_Icc_two_iff
  have hRsiff : ∀ f : LatticeSite 2,
      f ∈ Rs ↔ lo 0 ≤ f 0 ∧ f 0 ≤ hi 0 - 1 ∧ lo 1 - 1 ≤ f 1 ∧ f 1 ≤ hi 1 := by
    intro f
    rw [hRs, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- the boundary edges wired: the vertical edges of the left and right sides of `R` open,
  -- the vertical edges leaving `R` downwards and upwards closed
  set Wo : Config (LatticeSite 2) := {e | ∀ v ∈ e, v 0 = lo 0} ∪ {e | ∀ v ∈ e, v 0 = hi 0}
    with hWo
  set Wc : Config (LatticeSite 2) := {e | ∃ v ∈ e, v 1 = lo 1 - 1} ∪ {e | ∃ v ∈ e, v 1 = hi 1 + 1}
    with hWc
  set ω' : Config (LatticeSite 2) := (ω ∪ Wo) \ Wc with hω'
  -- the box of corners
  set K : Finset (LatticeSite 2) := Finset.Icc ![2 * lo 0, 2 * lo 1 - 1] ![2 * hi 0 - 1, 2 * hi 1]
    with hK
  have hKiff : ∀ s : LatticeSite 2, s ∈ K ↔
      2 * lo 0 ≤ s 0 ∧ s 0 ≤ 2 * hi 0 - 1 ∧ 2 * lo 1 - 1 ≤ s 1 ∧ s 1 ≤ 2 * hi 1 := by
    intro s
    rw [hK, Finset.mem_Icc, ← mem_Icc, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hKR : ∀ s ∈ K, cornerVertex s ∈ R := by
    intro s hs
    rw [hKiff] at hs
    rw [hRiff]
    simp only [cornerVertex_apply]
    omega
  have hKRs : ∀ s ∈ K, cornerFace s ∈ Rs := by
    intro s hs
    rw [hKiff] at hs
    rw [hRsiff]
    simp only [cornerFace_apply]
    omega
  -- horizontal edges of corners are inside `R` and not wired
  have hHE : ∀ s ∈ K, (cornerHEdge s ∈ ω' ↔ cornerHEdge s ∈ ω) := by
    intro s hs
    rw [hKiff] at hs
    have hnWo : cornerHEdge s ∉ Wo := by
      simp only [hWo, cornerHEdge_eq, mem_union, mem_ofPred_eq, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, Matrix.cons_val_zero]
      omega
    have hnWc : cornerHEdge s ∉ Wc := by
      simp only [hWc, cornerHEdge_eq, mem_union, mem_ofPred_eq, Sym2.mem_iff, exists_eq_or_imp,
        exists_eq_left, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    simp only [hω', mem_sdiff, mem_union, hnWo, hnWc, or_false, not_false_eq_true, and_true]
  -- vertical edges of corners
  have hVEo : ∀ s ∈ K, cornerVEdge s ∈ ω' → cornerVEdge s ∈ ω ∨ cornerVEdge s ∈ Wo := by
    intro s _ h
    exact (mem_sdiff _ |>.1 h).1
  have hVEc : ∀ s ∈ K, cornerVEdge s ∉ ω' → cornerVEdge s ∉ ω ∨ cornerVEdge s ∈ Wc := by
    intro s _ h
    by_cases hc : cornerVEdge s ∈ Wc
    · exact Or.inr hc
    · exact Or.inl fun hω => h ⟨Or.inl hω, hc⟩
  have hleftWired : ∀ s ∈ K, s 0 = 2 * lo 0 ∨ s 0 = 2 * hi 0 - 1 →
      2 * lo 1 ≤ s 1 → s 1 ≤ 2 * hi 1 - 1 → cornerVEdge s ∈ ω' := by
    intro s hs hs0 hs1 hs1'
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [hWo, cornerVEdge_eq, mem_union, mem_ofPred_eq, Sym2.mem_iff, forall_eq_or_imp,
        forall_eq, Matrix.cons_val_zero]
      omega
    · simp only [hWc, cornerVEdge_eq, mem_union, mem_ofPred_eq, Sym2.mem_iff, exists_eq_or_imp,
        exists_eq_left, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  have hbottomWired : ∀ s : LatticeSite 2, s 1 = 2 * lo 1 - 1 ∨ s 1 = 2 * hi 1 →
      cornerVEdge s ∉ ω' := by
    intro s hs h
    refine (mem_sdiff _ |>.1 h).2 ?_
    simp only [hWc, cornerVEdge_eq, mem_union, mem_ofPred_eq, Sym2.mem_iff, exists_eq_or_imp,
      exists_eq_left, Matrix.cons_val_one, Matrix.cons_val_zero]
    omega
  -- partners stay in the box of corners
  have hhK : ∀ s ∈ K, hPartner ω' s ∈ K := by
    intro s hs
    rw [hKiff] at hs ⊢
    by_cases h : cornerHEdge s ∈ ω'
    · rw [hPartner_of_mem h]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [hPartner_of_notMem h]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  have hvK : ∀ s ∈ K, ¬((s 0 = 2 * lo 0 ∨ s 0 = 2 * hi 0 - 1) ∧
      (s 1 = 2 * lo 1 - 1 ∨ s 1 = 2 * hi 1)) → vPartner ω' s ∈ K := by
    intro s hs hcorner
    have hs' := (hKiff s).1 hs
    rw [hKiff]
    by_cases h : cornerVEdge s ∈ ω'
    · have h1 : ¬(s 1 = 2 * lo 1 - 1 ∨ s 1 = 2 * hi 1) := fun h1 => hbottomWired s h1 h
      rw [vPartner_of_mem h]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · have h0 : ¬(s 0 = 2 * lo 0 ∨ s 0 = 2 * hi 0 - 1) := by
        intro h0
        refine h (hleftWired s hs h0 ?_ ?_) <;> omega
      rw [vPartner_of_notMem h]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  -- the bottom-left extreme corner
  set BL : LatticeSite 2 := ![2 * lo 0, 2 * lo 1 - 1] with hBL
  have hBLK : BL ∈ K := by
    rw [hKiff]
    simp only [hBL, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hvBL : vPartner ω' BL ∉ K := by
    rw [hKiff]
    by_cases h : cornerVEdge BL ∈ ω'
    · rw [vPartner_of_mem h]
      simp only [hBL, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [vPartner_of_notMem h]
      simp only [hBL, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  -- the corners whose vertex is joined to the left and whose face is joined to the bottom
  set S : Finset (LatticeSite 2) := K.filter (fun s => cornerVertex s ∈ A ∧ cornerFace s ∈ B)
    with hS
  have hmemS : ∀ s, s ∈ S ↔ s ∈ K ∧ cornerVertex s ∈ A ∧ cornerFace s ∈ B := by
    intro s
    rw [hS, Finset.mem_filter]
  have hBLS : BL ∈ S := by
    rw [hmemS]
    refine ⟨hBLK, ⟨cornerVertex BL, hKR BL hBLK, ?_, ?_⟩, ⟨cornerFace BL, hKRs BL hBLK, ?_, ?_⟩⟩
    · simp only [hBL, cornerVertex_apply, Matrix.cons_val_zero]
      omega
    · rw [localConn_self (hKR BL hBLK)]
      exact mem_univ _
    · simp only [hBL, cornerFace_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · rw [localConn_self (hKRs BL hBLK)]
      exact mem_univ _
  -- extending the two kinds of connection
  have hAext : ∀ v w, v ∈ A → w ∈ R → s(v, w) ∈ ω ∩ L → w ∈ A := by
    rintro v w ⟨a, ha, ha0, hav⟩ hw hvw
    exact ⟨a, ha, ha0, mem_localConn_of_mem_localConn_of_mem hav hw hvw⟩
  have hBext : ∀ f g, f ∈ B → g ∈ Rs → s(f, g) ∈ dualConfig ω ∩ L → g ∈ B := by
    rintro f g ⟨c, hc, hc1, hcf⟩ hg hfg
    exact ⟨c, hc, hc1, mem_localConn_of_mem_localConn_of_mem hcf hg hfg⟩
  have hAleft : ∀ v ∈ R, v 0 = lo 0 → v ∈ A := fun v hv hv0 =>
    ⟨v, hv, hv0, by rw [localConn_self hv]; exact mem_univ _⟩
  have hBbot : ∀ f ∈ Rs, f 1 = lo 1 - 1 → f ∈ B := fun f hf hf1 =>
    ⟨f, hf, hf1, by rw [localConn_self hf]; exact mem_univ _⟩
  -- one horizontal step stays in `S`
  have hstepH : ∀ s ∈ S, hPartner ω' s ∈ S := by
    intro s hs
    rw [hmemS] at hs ⊢
    obtain ⟨hsK, hsA, hsB⟩ := hs
    have htK := hhK s hsK
    by_cases h : cornerHEdge s ∈ ω'
    · refine ⟨htK, ?_, by rw [cornerFace_hPartner_of_mem h]; exact hsB⟩
      refine hAext _ _ hsA (hKR _ htK) ?_
      rw [sym2_cornerVertex_hPartner_of_mem h]
      exact ⟨(hHE s hsK).1 h, cornerHEdge_mem_edgeSet s⟩
    · refine ⟨htK, by rw [cornerVertex_hPartner_of_notMem h]; exact hsA, ?_⟩
      refine hBext _ _ hsB (hKRs _ htK) ?_
      rw [sym2_cornerFace_hPartner_of_notMem h]
      exact ⟨(dualEdge_mem_dualConfig_iff (cornerHEdge_mem_edgeSet s)).2
        fun h' => h ((hHE s hsK).2 h'), dualEdge_mem_edgeSet (cornerHEdge_mem_edgeSet s)⟩
  -- one vertical step that stays in the box of corners stays in `S`
  have hstepV : ∀ s ∈ S, vPartner ω' s ∈ K → vPartner ω' s ∈ S := by
    intro s hs htK
    rw [hmemS] at hs ⊢
    obtain ⟨hsK, hsA, hsB⟩ := hs
    have hsK' := (hKiff s).1 hsK
    by_cases h : cornerVEdge s ∈ ω'
    · refine ⟨htK, ?_, by rw [cornerFace_vPartner_of_mem h]; exact hsB⟩
      rcases hVEo s hsK h with hω | hW
      · refine hAext _ _ hsA (hKR _ htK) ?_
        rw [sym2_cornerVertex_vPartner_of_mem h]
        exact ⟨hω, cornerVEdge_mem_edgeSet s⟩
      · have hmem : cornerVertex (vPartner ω' s) ∈ cornerVEdge s := by
          rw [← sym2_cornerVertex_vPartner_of_mem h]
          exact Sym2.mem_mk_right _ _
        rcases hW with hW | hW
        · exact hAleft _ (hKR _ htK) (hW _ hmem)
        · exact absurd (hW _ (cornerVertex_mem_cornerVEdge s)) (hAright _ hsA)
    · refine ⟨htK, by rw [cornerVertex_vPartner_of_notMem h]; exact hsA, ?_⟩
      rcases hVEc s hsK h with hω | hW
      · refine hBext _ _ hsB (hKRs _ htK) ?_
        rw [sym2_cornerFace_vPartner_of_notMem h]
        exact ⟨(dualEdge_mem_dualConfig_iff (cornerVEdge_mem_edgeSet s)).2 hω,
          dualEdge_mem_edgeSet (cornerVEdge_mem_edgeSet s)⟩
      · -- the vertical edge leaves `R`: the dual step runs along the bottom or top row of `Rs`
        have hrow : cornerFace (vPartner ω' s) 1 = s 1 / 2 := by
          rw [vPartner_of_notMem h]
          simp
        simp only [hWc, cornerVEdge_eq, mem_union, mem_ofPred_eq, Sym2.mem_iff,
          exists_eq_or_imp, exists_eq_left, Matrix.cons_val_one, Matrix.cons_val_zero] at hW
        rcases hW with hW | hW
        · refine hBbot _ (hKRs _ htK) ?_
          rw [hrow]
          omega
        · exact absurd (by rw [cornerFace_apply]; omega) (hBtop _ hsB)
  -- counting `S` in pairs of horizontal partners, and `S` without its extreme corner in pairs
  -- of vertical partners
  have hS1 : ∑ s ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun s _ => hPartner ω' s) (fun _ _ => rfl)
      (fun s _ _ => hPartner_ne ω' s) (fun s hs => hstepH s hs)
      (fun s _ => hPartner_hPartner ω' s)
  have hS2 : ∑ s ∈ S.erase BL, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun s _ => vPartner ω' s) (fun _ _ => rfl)
      (fun s _ _ => vPartner_ne ω' s) (fun s hs => ?_) (fun s _ => vPartner_vPartner ω' s)
    obtain ⟨hne, hs⟩ := Finset.mem_erase.1 hs
    have hsS := (hmemS s).1 hs
    have hcorner : ¬((s 0 = 2 * lo 0 ∨ s 0 = 2 * hi 0 - 1) ∧
        (s 1 = 2 * lo 1 - 1 ∨ s 1 = 2 * hi 1)) := by
      rintro ⟨h0 | h0, h1 | h1⟩
      · exact hne (by rw [hBL, eq_vec_two_iff]; exact ⟨h0, h1⟩)
      · exact hBtop _ hsS.2.2 (by rw [cornerFace_apply, h1]; omega)
      · exact hAright _ hsS.2.1 (by rw [cornerVertex_apply, h0]; omega)
      · exact hAright _ hsS.2.1 (by rw [cornerVertex_apply, h0]; omega)
    have htK := hvK s hsS.1 hcorner
    refine Finset.mem_erase.2 ⟨fun hBLt => ?_, hstepV s hs htK⟩
    apply hvBL
    rw [← hBLt, vPartner_vPartner]
    exact hsS.1
  have hsum : (1 : ZMod 2) + ∑ s ∈ S.erase BL, (1 : ZMod 2) = ∑ s ∈ S, (1 : ZMod 2) :=
    Finset.add_sum_erase S (fun _ => (1 : ZMod 2)) hBLS
  rw [hS1, hS2] at hsum
  exact absurd hsum (by decide)

/-! ### Exactly one -/

/-- **Planar duality of crossings.** A box `[lo₀, hi₀] × [lo₁, hi₁]` of `ℤ²` has an open
left-right crossing exactly when the matching dual box `[lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]` has
no dual-open bottom-top crossing. -/
theorem mem_crossing_zero_iff_dualConfig_notMem_crossing_one {lo hi : LatticeSite 2}
    (hle : lo ≤ hi) (ω : Config (LatticeSite 2)) :
    ω ∈ crossing 0 lo hi ↔ dualConfig ω ∉ crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] :=
  ⟨notMem_crossing_one_dualConfig_of_mem_crossing_zero,
    fun h => by_contra fun h' => h (mem_crossing_one_dualConfig_of_notMem_crossing_zero hle h')⟩

/-- **Planar duality of crossings**, as events: the left-right crossing of a box is the
complement of the dual bottom-top crossing of the matching dual box. -/
theorem crossing_zero_eq_compl_preimage_dualConfig {lo hi : LatticeSite 2} (hle : lo ≤ hi) :
    crossing 0 lo hi = (dualConfig ⁻¹' crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1])ᶜ := by
  ext ω
  exact mem_crossing_zero_iff_dualConfig_notMem_crossing_one hle ω

/-- With every edge open, every nonempty box is crossed from left to right. -/
theorem univ_mem_crossing_zero {lo hi : LatticeSite 2} (hle : lo ≤ hi) :
    (univ : Config (LatticeSite 2)) ∈ crossing 0 lo hi := by
  rw [mem_crossing_zero_iff_dualConfig_notMem_crossing_one hle, dualConfig_univ]
  refine empty_notMem_crossing ?_
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have : lo 1 ≤ hi 1 := hle 1
  omega

/-- With every edge closed, the dual box is crossed from bottom to top. -/
theorem dualConfig_empty_mem_crossing_one {lo hi : LatticeSite 2} (hle : lo ≤ hi)
    (h : lo 0 < hi 0) :
    dualConfig ∅ ∈ crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] := by
  by_contra h'
  exact empty_notMem_crossing h
    ((mem_crossing_zero_iff_dualConfig_notMem_crossing_one hle ∅).2 h')

end PercLib.Models.Planar
