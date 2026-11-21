/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: B. Bollobás and O. Riordan, A short proof of the Harris-Kesten theorem,
Bull. London Math. Soc. 38 (2006), 470-484; G. Grimmett, Percolation, 2nd ed., Springer, 1999,
Section 11.2.
-/
module

public import PercLib.Models.Planar.CrossingSymmetry

/-!
# Gluing crossings on `ℤ²`

The planar facts behind the Russo–Seymour–Welsh argument, proved from the duality of crossings
with no planar topology.

* **Ring lemma** (`dualConfig_inter_mem_localConn_of_walk`). Around a walk of `ℤ²` that no edge
  of a configuration `η` touches, the faces at its vertices are joined by dual-open edges of
  `dualConfig η`: the four faces at a vertex are joined by the duals of its four edges, and
  consecutive vertices share a face. The statement keeps the faces inside the dual box
  `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` of a box containing the walk.
* **Separation lemma** (`exists_mem_support_of_dualConfig_mem_localConn`). Let `τ` be a
  bottom-top walk of a box and `σ` a walk in the box starting on its right side. If a face at
  the far end of `σ` is joined to the left column of the dual box by dual edges crossing no
  edge of `τ`, then `σ` meets `τ`. Otherwise the ring around `σ` would extend that dual path to
  the right column, and the edges of `τ` would have both a bottom-top crossing and a dual
  left-right crossing, against vertical duality.
* **Crossing lemma** (`exists_mem_support_of_crossing_walks`). A left-right walk and a
  bottom-top walk of the same box share a vertex.
* **Gluing** (`inter_edgeSet_mem_localConn_of_crossings`). In a box, an open left-right
  connection and an open bottom-top connection are joined inside the box.

## Main results

* `PercLib.Models.Planar.dualConfig_inter_mem_localConn_of_walk`
* `PercLib.Models.Planar.exists_mem_support_of_dualConfig_mem_localConn`
* `PercLib.Models.Planar.exists_mem_support_of_crossing_walks`
* `PercLib.Models.Planar.inter_edgeSet_mem_localConn_of_crossings`
-/

@[expose] public section

noncomputable section

open Set PercLib.Percolation.Bond PercLib.Models.Site

namespace PercLib.Models.Planar

/-! ### Dual edges around a vertex -/

/-- If no edge of `η` touches the vertex `v`, the duals of the edges below, above and to the
left of `v` are open in the dual configuration. -/
theorem dual_mem_of_forall_notMem {η : Config (LatticeSite 2)} {v : LatticeSite 2}
    (hv : ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e) :
    s(![v 0, v 1 - 1], ![v 0 - 1, v 1 - 1]) ∈ dualConfig η ∩ (zdGraph 2).edgeSet ∧
      s(![v 0, v 1], ![v 0 - 1, v 1]) ∈ dualConfig η ∩ (zdGraph 2).edgeSet ∧
      s(![v 0 - 1, v 1 - 1], ![v 0 - 1, v 1]) ∈ dualConfig η ∩ (zdGraph 2).edgeSet := by
  have key : ∀ e ∈ (zdGraph 2).edgeSet, v ∈ e →
      dualEdge e ∈ dualConfig η ∩ (zdGraph 2).edgeSet := fun e he hve =>
    ⟨(dualEdge_mem_dualConfig_iff he).2 fun h => hv e ⟨h, he⟩ hve, dualEdge_mem_edgeSet he⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := key _ (vertical_mem_edgeSet (v 0) (v 1 - 1))
      (Sym2.mem_iff.2 (Or.inr (eq_vec_two_iff.2 ⟨rfl, by ring⟩)))
    rwa [dualEdge_vertical] at h
  · have h := key _ (vertical_mem_edgeSet (v 0) (v 1))
      (Sym2.mem_iff.2 (Or.inl (eq_vec_two v)))
    rwa [dualEdge_vertical] at h
  · have h := key _ (horizontal_mem_edgeSet (v 0 - 1) (v 1))
      (Sym2.mem_iff.2 (Or.inr (eq_vec_two_iff.2 ⟨by ring, rfl⟩)))
    rwa [dualEdge_horizontal] at h

/-- Extending a dual connection inside `T` by one dual edge, in either orientation. -/
theorem mem_localConn_of_mem_localConn_of_mem' {T : Set (LatticeSite 2)}
    {ζ : Config (LatticeSite 2)} {a f g : LatticeSite 2} (h : ζ ∈ localConn T a f)
    (hg : g ∈ T) (hfg : s(f, g) ∈ ζ ∨ s(g, f) ∈ ζ) : ζ ∈ localConn T a g := by
  rcases hfg with hfg | hfg
  · exact mem_localConn_of_mem_localConn_of_mem h hg hfg
  · exact mem_localConn_of_mem_localConn_of_mem h hg (Sym2.eq_swap ▸ hfg)

/-! ### The ring lemma -/

section Ring

variable {η : Config (LatticeSite 2)} {lo hi : LatticeSite 2}

/-- The faces at a vertex `v` of the box that lie in the dual box
`[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` are joined by dual-open edges inside the dual box, when no
edge of `η` touches `v`. -/
theorem mem_localConn_of_faces_of_forall_notMem {v : LatticeSite 2} (hvR : v ∈ Icc lo hi)
    (hv : ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e) {f g : LatticeSite 2}
    (hfT : f ∈ Icc ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1])
    (hf : v 0 - 1 ≤ f 0 ∧ f 0 ≤ v 0 ∧ v 1 - 1 ≤ f 1 ∧ f 1 ≤ v 1)
    (hgT : g ∈ Icc ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1])
    (hg : v 0 - 1 ≤ g 0 ∧ g 0 ≤ v 0 ∧ v 1 - 1 ≤ g 1 ∧ g 1 ≤ v 1) :
    dualConfig η ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1]) f g := by
  set T : Set (LatticeSite 2) := Icc ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1] with hT
  obtain ⟨hd₁, hd₂, hd₃⟩ := dual_mem_of_forall_notMem hv
  rw [mem_Icc_two_iff] at hvR
  have hTiff : ∀ x : LatticeSite 2,
      x ∈ T ↔ lo 0 - 1 ≤ x 0 ∧ x 0 ≤ hi 0 ∧ lo 1 ≤ x 1 ∧ x 1 ≤ hi 1 - 1 := by
    intro x
    rw [hT, mem_Icc_two_iff]
    simp
  -- move a face at `v` to the column `v 0 - 1`, in its own row
  have hcol : ∀ x : LatticeSite 2, x ∈ T →
      (v 0 - 1 ≤ x 0 ∧ x 0 ≤ v 0 ∧ v 1 - 1 ≤ x 1 ∧ x 1 ≤ v 1) →
      dualConfig η ∩ (zdGraph 2).edgeSet ∈ localConn T x ![v 0 - 1, x 1] := by
    intro x hxT hx
    have hmT : (![v 0 - 1, x 1] : LatticeSite 2) ∈ T := by
      rw [hTiff] at hxT ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    rcases (show x 0 = v 0 - 1 ∨ x 0 = v 0 by omega) with hx0 | hx0
    · have : x = ![v 0 - 1, x 1] := eq_vec_two_iff.2 ⟨hx0, rfl⟩
      rw [← this, localConn_self hxT]
      exact mem_univ _
    · refine mem_localConn_of_mem_localConn_of_mem'
        (by rw [localConn_self hxT]; exact mem_univ _) hmT ?_
      have hx' : x = ![v 0, x 1] := eq_vec_two_iff.2 ⟨hx0, rfl⟩
      rcases (show x 1 = v 1 - 1 ∨ x 1 = v 1 by omega) with hx1 | hx1
      · left
        rw [hx', hx1]
        exact hd₁
      · left
        rw [hx', hx1]
        exact hd₂
  -- move along the column `v 0 - 1` between the rows `v 1 - 1` and `v 1`
  have hrow : ∀ y y' : ℤ, (![v 0 - 1, y] : LatticeSite 2) ∈ T →
      (![v 0 - 1, y'] : LatticeSite 2) ∈ T → (y = v 1 - 1 ∨ y = v 1) →
      (y' = v 1 - 1 ∨ y' = v 1) →
      dualConfig η ∩ (zdGraph 2).edgeSet ∈ localConn T ![v 0 - 1, y] ![v 0 - 1, y'] := by
    intro y y' hy hy' hyv hy'v
    by_cases hyy : y = y'
    · subst hyy
      rw [localConn_self hy]
      exact mem_univ _
    · refine mem_localConn_of_mem_localConn_of_mem'
        (by rw [localConn_self hy]; exact mem_univ _) hy' ?_
      rcases hyv with rfl | rfl <;> rcases hy'v with rfl | rfl
      · exact absurd rfl hyy
      · exact Or.inl hd₃
      · exact Or.inr hd₃
      · exact absurd rfl hyy
  have h₁ := hcol f hfT hf
  have h₂ := hcol g hgT hg
  have hfm : (![v 0 - 1, f 1] : LatticeSite 2) ∈ T := h₁.2.1
  have hgm : (![v 0 - 1, g 1] : LatticeSite 2) ∈ T := h₂.2.1
  have h₃ := hrow (f 1) (g 1) hfm hgm (by omega) (by omega)
  rw [localConn_comm] at h₂
  exact localConn_trans (localConn_trans h₁ h₃) h₂

/-- Adjacent vertices of the box share a face of the dual box `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]`,
when the box has height at least one. -/
theorem exists_face_of_adj (h1 : lo 1 < hi 1) {v w : LatticeSite 2} (hvR : v ∈ Icc lo hi)
    (hwR : w ∈ Icc lo hi) (hvw : (zdGraph 2).Adj v w) :
    ∃ f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1],
      (v 0 - 1 ≤ f 0 ∧ f 0 ≤ v 0 ∧ v 1 - 1 ≤ f 1 ∧ f 1 ≤ v 1) ∧
      (w 0 - 1 ≤ f 0 ∧ f 0 ≤ w 0 ∧ w 1 - 1 ≤ f 1 ∧ f 1 ≤ w 1) := by
  rw [mem_Icc_two_iff] at hvR hwR
  rcases (zdGraph_two_adj_iff v w).1 hvw with ⟨h0, h1'⟩ | ⟨h1'', h0⟩
  · refine ⟨![v 0 - 1, min (v 1) (w 1)], ?_, ?_⟩
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![min (v 0) (w 0), min (v 1) (hi 1 - 1)], ?_, ?_⟩
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega

/-- **Ring lemma.** Let `σ` be a walk of `ℤ²` in the box `[lo₀, hi₀] × [lo₁, hi₁]`, of height
at least one, such that no edge of `η` touches a vertex of `σ`. Then any two faces at vertices
of `σ` that lie in the dual box `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` are joined inside the dual
box by dual-open edges of `dualConfig η`. -/
theorem dualConfig_inter_mem_localConn_of_walk (h1 : lo 1 < hi 1) {u w : LatticeSite 2}
    (σ : (zdGraph 2).Walk u w) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hη : ∀ v ∈ σ.support, ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e) {a b f g : LatticeSite 2}
    (ha : a ∈ σ.support) (hb : b ∈ σ.support)
    (hfT : f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
    (hf : a 0 - 1 ≤ f 0 ∧ f 0 ≤ a 0 ∧ a 1 - 1 ≤ f 1 ∧ f 1 ≤ a 1)
    (hgT : g ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
    (hg : b 0 - 1 ≤ g 0 ∧ g 0 ≤ b 0 ∧ b 1 - 1 ≤ g 1 ∧ g 1 ≤ b 1) :
    dualConfig η ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f g := by
  induction σ generalizing a b f g with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha hb
    subst ha hb
    exact mem_localConn_of_faces_of_forall_notMem (hσ _ (by simp)) (hη _ (by simp)) hfT hf hgT hg
  | @cons x y z hxy p ih =>
    have hσ' : ∀ v ∈ p.support, v ∈ Icc lo hi := fun v hv => hσ v (by simp [hv])
    have hη' : ∀ v ∈ p.support, ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e :=
      fun v hv => hη v (by simp [hv])
    have hxR := hσ x (by simp)
    have hyR := hσ' y (SimpleGraph.Walk.start_mem_support _)
    have hx := hη x (by simp)
    obtain ⟨k, hkT, hkx, hky⟩ := exists_face_of_adj h1 hxR hyR hxy
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact mem_localConn_of_faces_of_forall_notMem hxR hx hfT hf hgT hg
    · exact localConn_trans (mem_localConn_of_faces_of_forall_notMem hxR hx hfT hf hkT hkx)
        (ih hσ' hη' (SimpleGraph.Walk.start_mem_support _) hb hkT hky hgT hg)
    · have := localConn_trans (mem_localConn_of_faces_of_forall_notMem hxR hx hgT hg hkT hkx)
        (ih hσ' hη' (SimpleGraph.Walk.start_mem_support _) ha hkT hky hfT hf)
      rwa [localConn_comm] at this
    · exact ih hσ' hη' ha hb hfT hf hgT hg

end Ring

/-! ### Walks of open edges -/

/-- The edges of a walk of `ℤ²` form a configuration in which the walk is open. -/
theorem mem_localConn_edges_of_walk {S : Set (LatticeSite 2)} {a b : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (hp : ∀ v ∈ p.support, v ∈ S) :
    {e | e ∈ p.edges} ∩ (zdGraph 2).edgeSet ∈ localConn S a b := by
  refine mem_localConn_iff_exists_walk.2 ⟨p.transfer _ fun e he => ?_, ?_⟩
  · rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨he, p.edges_subset_edgeSet he⟩,
      SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩
  · intro v hv
    rw [SimpleGraph.Walk.support_transfer] at hv
    exact hp v hv

/-- A vertex lying on an edge of a walk lies on the walk. -/
theorem mem_support_of_mem_edge {a b v : LatticeSite 2} (p : (zdGraph 2).Walk a b)
    {e : Sym2 (LatticeSite 2)} (he : e ∈ p.edges) (hv : v ∈ e) : v ∈ p.support := by
  induction e using Sym2.ind with
  | h x y =>
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact p.fst_mem_support_of_mem_edges he
    · exact p.snd_mem_support_of_mem_edges he

/-- A walk of open edges of `ω ∩ L` is a walk of `ℤ²`. -/
theorem openGraph_inter_edgeSet_le (ω : Config (LatticeSite 2)) :
    openGraph (ω ∩ (zdGraph 2).edgeSet) ≤ zdGraph 2 := fun u v h =>
  ((openGraph_adj_iff _ u v).1 h).1.2

/-! ### Separation and crossing lemmas -/

/-- **Separation lemma.** Let `τ` be a bottom-top walk of the box `[lo₀, hi₀] × [lo₁, hi₁]`,
of height at least one, and `σ` a walk in the box from its right side to a vertex `w`. If a
face `f₁` at `w` is joined to the left column of the dual box `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]`
by dual edges crossing no edge of `τ`, then `σ` meets `τ`. -/
theorem exists_mem_support_of_dualConfig_mem_localConn {lo hi : LatticeSite 2}
    (h1 : lo 1 < hi 1) {c d : LatticeSite 2} (τ : (zdGraph 2).Walk c d)
    (hτ : ∀ v ∈ τ.support, v ∈ Icc lo hi) (hc : c 1 = lo 1) (hd : d 1 = hi 1)
    {u w : LatticeSite 2} (σ : (zdGraph 2).Walk u w) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hu : u 0 = hi 0) {f₀ f₁ : LatticeSite 2} (hf₀ : f₀ 0 = lo 0 - 1)
    (hf₁ : w 0 - 1 ≤ f₁ 0 ∧ f₁ 0 ≤ w 0 ∧ w 1 - 1 ≤ f₁ 1 ∧ f₁ 1 ≤ w 1)
    (hpath : dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f₁) :
    ∃ v ∈ σ.support, v ∈ τ.support := by
  by_contra hdis
  push Not at hdis
  set η : Config (LatticeSite 2) := {e | e ∈ τ.edges} with hη
  have hcR := hτ c (SimpleGraph.Walk.start_mem_support _)
  have hle : lo ≤ hi := (mem_Icc.1 hcR).1.trans (mem_Icc.1 hcR).2
  -- the edges of `τ` cross the box from bottom to top
  have hV : η ∈ crossing 1 lo hi :=
    ⟨c, hcR, hc, d, hτ d (SimpleGraph.Walk.end_mem_support _), hd,
      mem_localConn_edges_of_walk τ hτ⟩
  -- no edge of `τ` touches `σ`
  have hfree : ∀ v ∈ σ.support, ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e :=
    fun v hv e he hve => hdis v hv (mem_support_of_mem_edge τ he.1 hve)
  -- a face at the start of `σ`, in the right column of the dual box
  have huR := hσ u (SimpleGraph.Walk.start_mem_support _)
  rw [mem_Icc_two_iff] at huR
  set g : LatticeSite 2 := ![u 0, min (u 1) (hi 1 - 1)] with hg
  have hgT : g ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1] := by
    rw [mem_Icc_two_iff, hg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hf₁T := hpath.2.1
  have hring := dualConfig_inter_mem_localConn_of_walk h1 σ hσ hfree
    (SimpleGraph.Walk.end_mem_support _) (SimpleGraph.Walk.start_mem_support _) hf₁T hf₁ hgT
    (by rw [hg]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
  have hH : dualConfig η ∈ crossing 0 ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1] :=
    ⟨f₀, hpath.1, by simpa using hf₀, g, hgT, by rw [hg]; simp [hu],
      localConn_trans hpath hring⟩
  exact (mem_crossing_one_iff_dualConfig_notMem_crossing_zero hle η).1 hV hH

/-- **Crossing lemma.** A left-right walk and a bottom-top walk of the same box of `ℤ²`, of
height at least one, share a vertex. -/
theorem exists_mem_support_of_crossing_walks {lo hi : LatticeSite 2} (h1 : lo 1 < hi 1)
    {a b c d : LatticeSite 2} (p : (zdGraph 2).Walk a b) (q : (zdGraph 2).Walk c d)
    (hp : ∀ v ∈ p.support, v ∈ Icc lo hi) (hq : ∀ v ∈ q.support, v ∈ Icc lo hi)
    (ha : a 0 = lo 0) (hb : b 0 = hi 0) (hc : c 1 = lo 1) (hd : d 1 = hi 1) :
    ∃ v ∈ p.support, v ∈ q.support := by
  have haR := hp a (SimpleGraph.Walk.start_mem_support _)
  rw [mem_Icc_two_iff] at haR
  set f : LatticeSite 2 := ![a 0 - 1, min (a 1) (hi 1 - 1)] with hf
  have hfT : f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1] := by
    rw [mem_Icc_two_iff, hf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  obtain ⟨v, hv, hvq⟩ := exists_mem_support_of_dualConfig_mem_localConn h1 q hq hc hd p.reverse
    (fun v hv => hp v (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv)) hb
    (f₀ := f) (f₁ := f) (by rw [hf]; simp [ha])
    (by rw [hf]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    (by rw [localConn_self hfT]; exact mem_univ _)
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
  exact ⟨v, hv, hvq⟩

/-- **Gluing of crossings.** In a box of height at least one, the start of an open left-right
connection is joined inside the box to the start of an open bottom-top connection. -/
theorem inter_edgeSet_mem_localConn_of_crossings {ω : Config (LatticeSite 2)}
    {lo hi a b c d : LatticeSite 2} (h1 : lo 1 < hi 1)
    (hab : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a b)
    (hcd : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) c d)
    (ha : a 0 = lo 0) (hb : b 0 = hi 0) (hc : c 1 = lo 1) (hd : d 1 = hi 1) :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a c := by
  classical
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hab
  obtain ⟨q, hq⟩ := mem_localConn_iff_exists_walk.1 hcd
  have hle := openGraph_inter_edgeSet_le ω
  obtain ⟨v, hvp, hvq⟩ := exists_mem_support_of_crossing_walks h1 (p.mapLe hle) (q.mapLe hle)
    (fun v hv => hp v (by rwa [SimpleGraph.Walk.support_mapLe_eq_support] at hv))
    (fun v hv => hq v (by rwa [SimpleGraph.Walk.support_mapLe_eq_support] at hv)) ha hb hc hd
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hvp hvq
  have hav : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a v :=
    mem_localConn_iff_exists_walk.2 ⟨p.takeUntil v hvp, fun x hx =>
      hp x (p.support_takeUntil_subset_support hvp hx)⟩
  have hcv : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) c v :=
    mem_localConn_iff_exists_walk.2 ⟨q.takeUntil v hvq, fun x hx =>
      hq x (q.support_takeUntil_subset_support hvq hx)⟩
  rw [localConn_comm] at hcv
  exact localConn_trans hav hcv

end PercLib.Models.Planar
