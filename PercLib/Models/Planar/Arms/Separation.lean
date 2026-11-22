/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation, p. 1579); B. Bollobás
and O. Riordan, A short proof of the Harris-Kesten theorem, Bull. London Math. Soc. 38 (2006),
470-484, proof of Lemma 6 (exploration of the dual cluster of a side).
-/
module

public import PercLib.Models.Planar.Arms.ColourInversion

/-!
# Local separation of crossings: relative duality and the exploration step

Nolin's local separation lemma explores the crossings of a strip greedily from one side: the
first crossing is the one closest to the left side, the next one is the closest crossing that
avoids the first, and so on, and the region beyond the explored crossings is fresh. The library
never conditions on a crossing as a topological object. The explored object is the **dual cluster
of the left column** of the dual box, with that column wired, in a configuration `ζ` (later a
configuration in which the crossings already found are removed). This file proves the facts about
that exploration step, for every box `Icc lo hi` of height at least one and every configuration:

* **Relative duality.** A set of faces of the dual box that contains its left column and avoids
  its right column is a wired boundary arc: the edges of `ℤ²` separating it from the other faces
  of the dual box contain a bottom-top crossing of the box (`mem_crossing_one_of_leftColumn`).
  This is box duality applied to the configuration of those edges.
* **The explored cluster.** The dual cluster `D` of the left column lies in the dual box and
  contains the left column; every edge of `ℤ²` separating `D` from another face of the dual box is
  open in `ζ`; `D` avoids the right column exactly when `ζ` crosses the box from bottom to top,
  and then the separating edges contain such a crossing; `D` grows when `ζ` shrinks; the event
  `D = D₀` depends only on the edges whose duals meet `D₀`, and is measurable.

## Main results

* `mem_crossing_one_of_leftColumn`: relative duality for a set of faces containing the left column
  of the dual box and avoiding its right column.
* `mem_crossing_one_iff_forall_mem_exploredCluster_ne`: the explored cluster avoids the right
  column exactly when the box is crossed.
* `mem_of_mem_exploredCluster_of_notMem`: the edges separating the explored cluster from the rest
  of the dual box are open.
* `exploredCluster_eq_iff_of_agree`: the explored cluster is determined by the edges whose duals
  meet it.
* `exploredCluster_anti`: the explored cluster grows when the configuration shrinks.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Relative duality -/

/-- **Relative duality.** Let `D₀` be a set of faces of `ℤ²` that contains the left column of
the dual box `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` and avoids its right column. The edges of `ℤ²`
whose duals lie in the dual box and separate a face of `D₀` from a face outside `D₀` cross the box
`Icc lo hi` from bottom to top: the explored set acts as a wired boundary arc. -/
theorem mem_crossing_one_of_leftColumn {lo hi : LatticeSite 2} (hle : lo ≤ hi)
    {D₀ : Set (LatticeSite 2)}
    (hleft : ∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ D₀)
    (hright : ∀ f ∈ D₀, f 0 ≠ hi 0) :
    {e | e ∈ (zdGraph 2).edgeSet ∧
        (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
        (∃ f ∈ dualEdge e, f ∈ D₀) ∧ ∃ f ∈ dualEdge e, f ∉ D₀} ∈ crossing 1 lo hi := by
  set B : Config (LatticeSite 2) := {e | e ∈ (zdGraph 2).edgeSet ∧
    (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
    (∃ f ∈ dualEdge e, f ∈ D₀) ∧ ∃ f ∈ dualEdge e, f ∉ D₀} with hB
  rw [mem_crossing_one_iff_dualConfig_notMem_crossing_zero hle]
  rintro ⟨a, ha, ha0, b, hb, hb0, hab⟩
  simp only [Matrix.cons_val_zero] at ha0 hb0
  obtain ⟨p, hp, hpω⟩ := exists_walk_of_mem_localConn hab
  have haD : a ∈ D₀ := by
    have ha' := ha
    rw [mem_Icc_two_iff] at ha'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha'
    have := hleft (a 1) (by omega) (by omega)
    rwa [← eq_vec_two_iff.2 ⟨ha0, rfl⟩] at this
  have hbD : b ∉ D₀ := fun h => hright b h hb0
  obtain ⟨δ, hδ, hδ₁, hδ₂⟩ := p.exists_boundary_dart D₀ haD hbD
  have hδe : δ.edge ∈ p.edges := List.mem_map_of_mem hδ
  have hfst := hp _ (p.dart_fst_mem_support_of_mem_darts hδ)
  have hsnd := hp _ (p.dart_snd_mem_support_of_mem_darts hδ)
  have hopen := hpω _ hδe
  obtain ⟨e, heL, hee⟩ := exists_dualEdge_eq (p.edges_subset_edgeSet hδe)
  rw [← hee, dualEdge_mem_dualConfig_iff heL] at hopen
  apply hopen
  have hδedge : δ.edge = s(δ.fst, δ.snd) := rfl
  rw [hδedge] at hee
  refine ⟨heL, fun f hf => ?_, ⟨δ.fst, by rw [hee]; exact Sym2.mem_mk_left _ _, hδ₁⟩,
    ⟨δ.snd, by rw [hee]; exact Sym2.mem_mk_right _ _, hδ₂⟩⟩
  rw [hee, Sym2.mem_iff] at hf
  rcases hf with rfl | rfl
  · exact hfst
  · exact hsnd

/-! ### The explored cluster

Throughout, `ζ' = dualConfig ζ ∩ {s | ∀ v ∈ s, v ∈ T} ∪ W` where `T` is the dual box
`[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` and `W` wires its left column by its own dual edges, and the
explored cluster is `cluster ζ' ![lo 0 - 1, lo 1]`, the dual cluster of the bottom-left face of
`T`. The hypothesis `hζ'` spells this out. -/

section Explored

variable {lo hi : LatticeSite 2} {ζ ζ' : Config (LatticeSite 2)}

/-- The wired dual configuration uses only edges of `ℤ²` with both ends in the dual box. -/
theorem forall_mem_Icc_of_mem_wired (h1 : lo 1 < hi 1) (hle : lo 0 ≤ hi 0)
    (hζ' : ζ' = dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    {s : Sym2 (LatticeSite 2)} (hs : s ∈ ζ') :
    s ∈ (zdGraph 2).edgeSet ∧
      ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1] := by
  rw [hζ'] at hs
  rcases hs with ⟨hs, hsT⟩ | ⟨y, hy0, hy1, rfl⟩
  · exact ⟨dualConfig_subset_edgeSet ζ hs, hsT⟩
  · refine ⟨vertical_mem_edgeSet _ y, fun v hv => ?_⟩
    rw [Sym2.mem_iff] at hv
    rw [mem_Icc_two_iff]
    have := h1
    have := hle
    rcases hv with rfl | rfl <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

/-- Every face of the explored cluster is joined to the bottom-left face of the dual box by a walk
of faces in the cluster whose dual edges are open in the wired configuration. -/
theorem exists_walk_of_mem_exploredCluster {f : LatticeSite 2}
    (hf : f ∈ cluster ζ' ![lo 0 - 1, lo 1]) (hζ'L : ζ' ⊆ (zdGraph 2).edgeSet) :
    ∃ p : (zdGraph 2).Walk ![lo 0 - 1, lo 1] f,
      (∀ v ∈ p.support, v ∈ cluster ζ' ![lo 0 - 1, lo 1]) ∧ ∀ s ∈ p.edges, s ∈ ζ' := by
  obtain ⟨p⟩ := hf
  have hedge : ∀ s ∈ p.edges, s ∈ ζ' := fun s hs => by
    have := p.edges_subset_edgeSet hs
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  refine ⟨p.transfer (zdGraph 2) fun s hs => hζ'L (hedge s hs), fun v hv => ?_, fun s hs => ?_⟩
  · rw [SimpleGraph.Walk.support_transfer] at hv
    exact ⟨p.takeUntil v hv⟩
  · rw [SimpleGraph.Walk.edges_transfer] at hs
    exact hedge s hs

/-- The explored cluster lies in the dual box. -/
theorem exploredCluster_subset (h1 : lo 1 < hi 1) (hle : lo 0 ≤ hi 0)
    (hζ' : ζ' = dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) :
    cluster ζ' ![lo 0 - 1, lo 1] ⊆ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1] := by
  intro f hf
  by_cases hfa : f = ![lo 0 - 1, lo 1]
  · rw [hfa, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · obtain ⟨p, -, hpe⟩ := exists_walk_of_mem_exploredCluster hf
      (fun s hs => (forall_mem_Icc_of_mem_wired h1 hle hζ' hs).1)
    obtain ⟨w, h, p', hp'⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hfa p.reverse
    have hfw : s(f, w) ∈ p.edges := by
      have : s(f, w) ∈ p.reverse.edges := by
        rw [hp']
        simp
      rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
    exact (forall_mem_Icc_of_mem_wired h1 hle hζ' (hpe _ hfw)).2 f (Sym2.mem_mk_left _ _)

/-- The explored cluster contains the left column of the dual box. -/
theorem mem_exploredCluster_of_leftColumn
    (hζ' : ζ' = dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    (y : ℤ) (hy0 : lo 1 ≤ y) (hy1 : y ≤ hi 1 - 1) :
    (![lo 0 - 1, y] : LatticeSite 2) ∈ cluster ζ' ![lo 0 - 1, lo 1] := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, y = lo 1 + k := ⟨(y - lo 1).toNat, by omega⟩
  clear hy0
  induction k with
  | zero => simpa using mem_cluster_self ζ' ![lo 0 - 1, lo 1]
  | succ k ih =>
    have hprev : (openGraph ζ').Reachable ![lo 0 - 1, lo 1] ![lo 0 - 1, lo 1 + k] :=
      ih (by omega)
    have hs : s((![lo 0 - 1, lo 1 + k] : LatticeSite 2), ![lo 0 - 1, lo 1 + ↑(k + 1)]) ∈ ζ' := by
      rw [hζ']
      exact Or.inr ⟨lo 1 + k, by omega, by push_cast at hy1 ⊢; omega, by push_cast; ring_nf⟩
    have hne : (![lo 0 - 1, lo 1 + k] : LatticeSite 2) ≠ ![lo 0 - 1, lo 1 + ↑(k + 1)] := by
      intro h
      have := congrFun h 1
      simp at this
    exact hprev.trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨hs, hne⟩))

/-- The edges of `ℤ²` separating the explored cluster from another face of the dual box are open
in `ζ`. -/
theorem mem_of_mem_exploredCluster_of_notMem
    (hζ' : ζ' = dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    {e : Sym2 (LatticeSite 2)} (heL : e ∈ (zdGraph 2).edgeSet)
    (heT : ∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
    (hin : ∃ f ∈ dualEdge e, f ∈ cluster ζ' ![lo 0 - 1, lo 1])
    (hout : ∃ g ∈ dualEdge e, g ∉ cluster ζ' ![lo 0 - 1, lo 1]) : e ∈ ζ := by
  obtain ⟨f, hfe, hfD⟩ := hin
  obtain ⟨g, hge, hgD⟩ := hout
  by_contra heζ
  have hfg : f ≠ g := fun h => hgD (h ▸ hfD)
  have hs : dualEdge e = s(f, g) := (Sym2.mem_and_mem_iff hfg).1 ⟨hfe, hge⟩
  have hζe : dualEdge e ∈ ζ' := by
    rw [hζ']
    exact Or.inl ⟨(dualEdge_mem_dualConfig_iff heL).2 heζ, heT⟩
  rw [hs] at hζe
  have hfD' : (openGraph ζ').Reachable ![lo 0 - 1, lo 1] f := hfD
  exact hgD (hfD'.trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨hζe, hfg⟩)))

/-- If the box is crossed from bottom to top in `ζ`, the explored cluster avoids the right column
of the dual box. -/
theorem forall_mem_exploredCluster_ne_of_mem_crossing (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hζ' : ζ' = dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    (hζ : ζ ∈ crossing 1 lo hi) : ∀ f ∈ cluster ζ' ![lo 0 - 1, lo 1], f 0 ≠ hi 0 := by
  intro f hf hf0
  have hζ'L : ζ' ⊆ (zdGraph 2).edgeSet := fun s hs =>
    (forall_mem_Icc_of_mem_wired h1 (hle 0) hζ' hs).1
  rw [mem_crossing_one_iff_dualConfig_notMem_crossing_zero hle] at hζ
  apply hζ
  obtain ⟨p, hpD, hpe⟩ := exists_walk_of_mem_exploredCluster hf hζ'L
  obtain ⟨c, hc, q', hqsupp, hqedges, hqfirst⟩ :=
    SimpleGraph.Walk.exists_walk_first_mem (fun v : LatticeSite 2 => v 0 = lo 0 - 1) p.reverse
      ⟨![lo 0 - 1, lo 1], by simp, by simp⟩
  have hDT := exploredCluster_subset h1 (hle 0) hζ'
  have hqD : ∀ v ∈ q'.support, v ∈ cluster ζ' ![lo 0 - 1, lo 1] := fun v hv => by
    have := hqsupp v hv
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
    exact hpD v this
  have hqdual : ∀ s ∈ q'.reverse.edges, s ∈ dualConfig ζ := by
    intro s hs
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hs
    have hsζ : s ∈ ζ' := by
      have := hqedges s hs
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
      exact hpe s this
    obtain ⟨x, y, rfl, hxy, hx, hy⟩ := exists_ne_of_mem_edges q' hs
    rw [hζ'] at hsζ
    rcases hsζ with ⟨hs', -⟩ | ⟨t, -, -, ht⟩
    · exact hs'
    · have hx0 : x 0 = lo 0 - 1 := by
        rcases Sym2.eq_iff.1 ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      have hy0 : y 0 = lo 0 - 1 := by
        rcases Sym2.eq_iff.1 ht with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
      exact absurd ((hqfirst x hx hx0).trans (hqfirst y hy hy0).symm) hxy
  have hloc := mem_localConn_of_walk q'.reverse (fun v hv => by
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    exact hDT (hqD v hv)) hqdual
  have hcT := hDT (hqD c (SimpleGraph.Walk.end_mem_support _))
  exact ⟨c, hcT, by simpa using hc, f, hDT hf, by simpa using hf0, hloc⟩

/-- **The explored cluster avoids the right column exactly when the box is crossed.** Moreover,
when it does, the edges separating it from the rest of the dual box carry a bottom-top crossing,
open in `ζ`. -/
theorem mem_crossing_one_iff_forall_mem_exploredCluster_ne (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hζ' : ζ' = dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) :
    ζ ∈ crossing 1 lo hi ↔ ∀ f ∈ cluster ζ' ![lo 0 - 1, lo 1], f 0 ≠ hi 0 := by
  refine ⟨forall_mem_exploredCluster_ne_of_mem_crossing h1 hle hζ', fun hright => ?_⟩
  refine crossing_mono (fun e he => ?_) (mem_crossing_one_of_leftColumn hle
    (fun y hy0 hy1 => mem_exploredCluster_of_leftColumn hζ' y hy0 hy1) hright)
  obtain ⟨heL, heT, hin, hout⟩ := he
  exact mem_of_mem_exploredCluster_of_notMem hζ' heL heT hin hout

/-- **The explored cluster grows when the configuration shrinks.** -/
theorem exploredCluster_anti {ζ₁ ζ₂ ζ₁' ζ₂' : Config (LatticeSite 2)} (h : ζ₁ ⊆ ζ₂)
    (hζ₁ : ζ₁' = dualConfig ζ₁ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    (hζ₂ : ζ₂' = dualConfig ζ₂ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) :
    cluster ζ₂' ![lo 0 - 1, lo 1] ⊆ cluster ζ₁' ![lo 0 - 1, lo 1] := by
  have hsub : ζ₂' ⊆ ζ₁' := by
    rw [hζ₁, hζ₂]
    exact union_subset_union_left _ (inter_subset_inter_left _ (dualConfig_anti h))
  exact fun f hf => conn_mono hsub hf

/-- **Determination of the explored cluster.** Whether the explored cluster equals a finite set
`D₀` of faces depends only on the edges of `ℤ²` whose duals meet `D₀`. -/
theorem exploredCluster_eq_iff_of_agree {ζ₁ ζ₂ ζ₁' ζ₂' : Config (LatticeSite 2)}
    {D₀ : Finset (LatticeSite 2)} (hD₀ : (![lo 0 - 1, lo 1] : LatticeSite 2) ∈ D₀)
    (hζ₁ : ζ₁' = dualConfig ζ₁ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    (hζ₂ : ζ₂' = dualConfig ζ₂ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
    (hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D₀) → (e ∈ ζ₁ ↔ e ∈ ζ₂)) :
    cluster ζ₁' ![lo 0 - 1, lo 1] = ↑D₀ ↔ cluster ζ₂' ![lo 0 - 1, lo 1] = ↑D₀ := by
  have heq : ζ₁' ∩ {s | ∃ v ∈ s, v ∈ D₀} = ζ₂' ∩ {s | ∃ v ∈ s, v ∈ D₀} := by
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_left fun hsD => ?_
    rw [hζ₁, hζ₂]
    simp only [mem_union, mem_inter_iff]
    refine or_congr_left (and_congr_left fun _ => ?_)
    rw [mem_dualConfig_iff, mem_dualConfig_iff]
    refine and_congr_right fun hsL => not_congr ?_
    have heL : Sym2.map (· + 1) (dualEdge s) ∈ (zdGraph 2).edgeSet :=
      map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hsL)
    refine hagree _ heL ?_
    obtain ⟨v, hv, hvD⟩ := hsD
    exact ⟨v, by rwa [dualEdge_map_add, map_add_one_dualEdge_dualEdge hsL], hvD⟩
  have k₁ := cluster_eq_finset_determined (![lo 0 - 1, lo 1] : LatticeSite 2) D₀ hD₀ ζ₁'
  have k₂ := cluster_eq_finset_determined (![lo 0 - 1, lo 1] : LatticeSite 2) D₀ hD₀ ζ₂'
  simp only [mem_ofPred_eq] at k₁ k₂
  rw [k₁, k₂, heq]

/-- The wired dual configuration is a measurable function of the configuration. -/
theorem measurable_wired :
    Measurable fun ζ : Config (LatticeSite 2) => dualConfig ζ ∩
        {s | ∀ v ∈ s, v ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))} := by
  refine Measurable.of_mem fun s => ?_
  simp only [mem_union, mem_inter_iff]
  exact (((measurable_set_mem s).comp measurable_dualConfig).and measurable_const).or
    measurable_const

end Explored

/-! ### Greedy exploration of the crossings of a box

Fix a configuration `G` and a rule `Γ` choosing, for every finite set `A` of faces that contains
the left column of the dual box and avoids its right column, a bottom-top crossing of the box
through edges separating `A` from the other faces of the dual box (`exists_crossing_choice`).
The greedy exploration is the sequence of explored clusters `A 0 ⊆ A 1 ⊆ ⋯`: `A v` is the explored
cluster of `G` with every edge at a vertex of the crossings `Γ (A w)`, `w < v`, removed. The
crossings `Γ (A 0), Γ (A 1), …` are then the greedy crossings: each is the closest crossing on the
right of the explored region that avoids all earlier ones. A sequence `A` is the exploration of
`G` up to step `u` when

`∀ v ≤ u, cluster (wired (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support})) a₀ = A v`.

Since no definition is introduced, this condition is written out in each statement. -/

section Greedy

variable {lo hi : LatticeSite 2} {G : Config (LatticeSite 2)}
  {c d : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- **A choice rule for the greedy exploration.** For every finite set of faces containing the left
column of the dual box and avoiding its right column there is a bottom-top crossing of the box
through edges separating it from the other faces of the dual box; choose one for each such set. -/
theorem exists_crossing_choice (hle : lo ≤ hi) :
    ∃ (c d : Finset (LatticeSite 2) → LatticeSite 2) (Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)),
      ∀ A : Finset (LatticeSite 2),
        (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
        (∀ f ∈ A, f 0 ≠ hi 0) →
        c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
          (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
          ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
            (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
            (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A := by
  classical
  have hex : ∀ A : Finset (LatticeSite 2), ∃ (c d : LatticeSite 2) (γ : (zdGraph 2).Walk c d),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c ∈ Icc lo hi ∧ c 1 = lo 1 ∧ d ∈ Icc lo hi ∧ d 1 = hi 1 ∧
        (∀ x ∈ γ.support, x ∈ Icc lo hi) ∧
        ∀ e ∈ γ.edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A := by
    intro A
    by_cases hA : (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) ∧
        ∀ f ∈ A, f 0 ≠ hi 0
    · obtain ⟨c, hc, hc1, d, hd, hd1, hcd⟩ :=
        mem_crossing_one_of_leftColumn hle (D₀ := ↑A) hA.1 hA.2
      obtain ⟨γ, hγS, hγe⟩ := exists_walk_of_mem_localConn hcd
      exact ⟨c, d, γ, fun _ _ => ⟨hc, hc1, hd, hd1, hγS, hγe⟩⟩
    · exact ⟨0, 0, .nil, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hA⟩
  choose c d Γ hΓ using hex
  exact ⟨c, d, Γ, hΓ⟩

/-- **Uniqueness of the exploration.** Two explorations of the same configuration agree up to the
step where both are defined. -/
theorem exploration_unique {A A' : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    (hA' : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A' w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
          ↑(A' v)) :
    ∀ v ≤ u, A v = A' v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    have hR : {e : Sym2 (LatticeSite 2) | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support} =
        {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A' w)).support} := by
      ext e
      simp only [mem_ofPred_eq]
      refine exists_congr fun x => and_congr_right fun _ => exists_congr fun w =>
        and_congr_right fun hw => ?_
      rw [ih w hw (by omega)]
    have h := hA v hv
    rw [hR, hA' v hv] at h
    exact Finset.coe_injective h.symm

/-- **Existence of the exploration.** Every configuration has an exploration up to every step. -/
theorem exists_exploration (h1 : lo 1 < hi 1) (hle : lo 0 ≤ hi 0) (G : Config (LatticeSite 2))
    (Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)) (u : ℕ) :
    ∃ A : ℕ → Finset (LatticeSite 2),
      ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A v) := by
  classical
  -- the explored cluster of any configuration is finite
  have hfin : ∀ R : Config (LatticeSite 2), (cluster (dualConfig (G \ R) ∩
      {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))})
        ![lo 0 - 1, lo 1]).Finite := fun R =>
    (Set.finite_Icc _ _).subset (exploredCluster_subset h1 hle rfl)
  induction u with
  | zero =>
    refine ⟨fun _ => (hfin ∅).toFinset, fun v hv => ?_⟩
    obtain rfl : v = 0 := by omega
    rw [Set.Finite.coe_toFinset]
    congr 3
    ext e
    simp
  | succ u ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨fun v => if v ≤ u then A v else (hfin {e | ∃ x ∈ e, ∃ w < u + 1,
      x ∈ (Γ (A w)).support}).toFinset, fun v hv => ?_⟩
    have hR : {e : Sym2 (LatticeSite 2) | ∃ x ∈ e, ∃ w < v,
        x ∈ (Γ (if w ≤ u then A w else (hfin {e | ∃ x ∈ e, ∃ w < u + 1,
          x ∈ (Γ (A w)).support}).toFinset)).support} =
        {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support} := by
      ext e
      simp only [mem_ofPred_eq]
      refine exists_congr fun x => and_congr_right fun _ => exists_congr fun w =>
        and_congr_right fun hw => ?_
      rw [ite_eq_left (by omega)]
    rw [hR]
    dsimp only
    by_cases hvu : v ≤ u
    · rw [ite_eq_left hvu]
      exact hA v hvu
    · rw [ite_eq_right hvu, Set.Finite.coe_toFinset]
      obtain rfl : v = u + 1 := by omega
      rfl

/-- **The exploration grows.** -/
theorem exploration_mono {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v w : ℕ} (hvw : v ≤ w) (hw : w ≤ u) : A v ⊆ A w := by
  have hsub := exploredCluster_anti (lo := lo) (hi := hi)
    (ζ₁ := G \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support})
    (ζ₂ := G \ {e | ∃ x ∈ e, ∃ w' < v, x ∈ (Γ (A w')).support})
    (sdiff_subset_sdiff_right fun e ⟨x, hx, w', hw', hxw⟩ => ⟨x, hx, w', by omega, hxw⟩) rfl rfl
  rw [hA v (hvw.trans hw), hA w hw] at hsub
  exact Finset.coe_subset.1 hsub

/-- **Determination of the exploration.** For an increasing sequence `A` whose sets contain the
bottom-left face of the dual box, whether `A` is the exploration of `G` up to step `u` depends
only on the edges whose duals meet `A u`. -/
theorem exploration_iff_of_agree {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    {G' : Config (LatticeSite 2)}
    (hmono : ∀ v ≤ u, A v ⊆ A u) (ha₀ : ∀ v ≤ u, (![lo 0 - 1, lo 1] : LatticeSite 2) ∈ A v)
    (hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ A u) → (e ∈ G ↔ e ∈ G')) :
    (∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
          ↑(A v)) ↔
      ∀ v ≤ u, cluster (dualConfig (G' \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A v) := by
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  refine exploredCluster_eq_iff_of_agree (ha₀ v hv) rfl rfl fun e he hf => ?_
  obtain ⟨f, hfe, hfA⟩ := hf
  simp only [mem_sdiff]
  rw [hagree e he ⟨f, hfe, hmono v hv hfA⟩]

/-- **The greedy crossings are disjoint crossings of `G`.** If the explored cluster at step `v`
avoids the right column of the dual box, the chosen crossing `Γ (A v)` is open in `G` and meets
none of the earlier chosen crossings. -/
theorem forall_mem_of_exploration (h1 : lo 1 < hi 1)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {A : ℕ → Finset (LatticeSite 2)} {u v : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    (hv : v ≤ u) (hright : ∀ f ∈ A v, f 0 ≠ hi 0) :
    (∀ e ∈ (Γ (A v)).edges, e ∈ G) ∧
      ∀ x ∈ (Γ (A v)).support, ∀ w < v, x ∉ (Γ (A w)).support := by
  have hleft : ∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A v := by
    intro y hy0 hy1
    have := mem_exploredCluster_of_leftColumn (lo := lo) (hi := hi)
      (ζ := G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) rfl y hy0 hy1
    rw [hA v hv] at this
    exact this
  obtain ⟨-, hc1, -, hd1, -, hΓe⟩ := hΓ (A v) hleft hright
  have hmem : ∀ e ∈ (Γ (A v)).edges, e ∈ G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support} := by
    intro e he
    obtain ⟨heL, heT, ⟨f, hfe, hfA⟩, ⟨g, hge, hgA⟩⟩ := hΓe e he
    refine mem_of_mem_exploredCluster_of_notMem rfl heL heT ⟨f, hfe, ?_⟩ ⟨g, hge, ?_⟩
    · rw [hA v hv]
      exact hfA
    · rw [hA v hv]
      exact hgA
  refine ⟨fun e he => (hmem e he).1, fun x hx w hw hxw => ?_⟩
  have hnil : ¬(Γ (A v)).Nil := fun hn => by
    have := SimpleGraph.Walk.Nil.eq hn
    have h' := congrFun this 1
    omega
  obtain ⟨e, he, hxe⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).1 hx
  exact (hmem e he).2 ⟨x, hxe, w, hw, hxw⟩

/-- **Maximality of the greedy crossings.** Once the explored cluster reaches the right column of
the dual box, every bottom-top crossing of the box open in `G` meets one of the chosen
crossings. -/
theorem exists_mem_support_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    (hu : ∃ f ∈ A u, f 0 = hi 0) {a b : LatticeSite 2} (p : (zdGraph 2).Walk a b)
    (hp : ∀ x ∈ p.support, x ∈ Icc lo hi) (ha : a 1 = lo 1) (hb : b 1 = hi 1)
    (hpG : ∀ e ∈ p.edges, e ∈ G) :
    ∃ x ∈ p.support, ∃ w < u, x ∈ (Γ (A w)).support := by
  by_contra hno
  push Not at hno
  have hcross : G \ {e | ∃ x ∈ e, ∃ w < u, x ∈ (Γ (A w)).support} ∈ crossing 1 lo hi := by
    refine ⟨a, hp a p.start_mem_support, ha, b, hp b p.end_mem_support, hb, ?_⟩
    refine mem_localConn_of_walk p hp fun e he => ⟨hpG e he, ?_⟩
    rintro ⟨x, hxe, w, hw, hxw⟩
    exact hno x (mem_support_of_mem_edge p he hxe) w hw hxw
  obtain ⟨f, hf, hf0⟩ := hu
  have := forall_mem_exploredCluster_ne_of_mem_crossing h1 hle rfl hcross f
  rw [hA u le_rfl] at this
  exact this hf hf0

end Greedy

end PercLib.Models.Planar
