/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation, p. 1579), rerouting
step at the end of its proof. The rerouting rule proved here is not the one written there; see
the module docstring.
-/
module

public import PercLib.Models.Planar.Arms.Separation

/-!
# Local separation of crossings: rerouting a family of crossings to greedy tips

The last step of Nolin's local separation lemma replaces the top part of every crossing of a given
family of disjoint crossings by the top part of one of the greedy crossings, keeping the starting
points, so that the new crossings are still disjoint. This file proves that step for the greedy
exploration of `Separation.lean`, for any configuration `G` and any box.

The rule written in the source (each crossing is matched to the greedy crossing of least index that
it meets and is cut at its last intersection with it) can produce intersecting crossings, and so
can the same rule with the first intersection. The rule proved here works from right to left. The
crossings of the family are ordered by their starting points on the bottom row. The rightmost one
is followed to its first vertex on any greedy crossing; if that crossing has index `w`, the next
crossing to the left is followed to its first vertex on a greedy crossing of index `< w`, and so on.
Each crossing then continues along the greedy crossing it reached, to its top end.

All the planar topology goes through one tool, the separation lemma of `Gluing.lean`, applied in
the box extended by one row below the bottom row: a bottom-top walk `τ` separates the points of the
bottom row on its right from every face that is joined to the left column of the dual box without
crossing `τ`. Two cases are used: the face is a face of an explored cluster at a vertex of a greedy
crossing (the dual paths of the exploration cross no edge that is open after the removals), or a
face below a point of the bottom row on the left of `τ` (the dual path runs along the extra row).

## Main results

* `exists_mem_support_of_dualConfig_mem_localConn_below`: separation in the box extended by one
  row.
* `exists_mem_support_of_lt_of_localConn`, `exists_mem_support_of_lt_of_lt`: its two forms used
  here.
* `notMem_support_of_lt_of_lt`: a bottom-top walk separates the walks that start on the bottom row
  on its two sides.
* `exists_localConn_of_mem_support_of_exploration`: the faces of an explored cluster at a vertex of
  the chosen crossing reach the left column without crossing any walk that is open after the
  removals.
* `exists_reroute_of_exploration`: the rerouting of a family of disjoint crossings to distinct
  greedy tips, with the same starting points.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- In a path, the start vertex is not in the part after any other vertex. -/
theorem start_notMem_support_dropUntil {u v w : V} {p : G.Walk u v} (hp : p.IsPath)
    (hw : w ∈ p.support) (h : u ≠ w) : u ∉ (p.dropUntil w hw).support := by
  intro hu
  have hnd := hp.support_nodup
  rw [← p.take_spec hw, support_append, List.nodup_append] at hnd
  have hu' : u ∈ (p.dropUntil w hw).support.tail := by
    rcases (mem_support_iff _).1 hu with h' | h'
    · exact absurd h' h
    · exact h'
  exact hnd.2.2 u (p.takeUntil w hw).start_mem_support u hu' rfl

omit [DecidableEq V] in
/-- A vertex of a walk other than its end is in the support without its last entry. -/
theorem mem_dropLast_support_of_ne {u v w : V} {p : G.Walk u v} (hw : w ∈ p.support)
    (h : w ≠ v) : w ∈ p.support.dropLast := by
  rw [← p.dropLast_support_concat, List.mem_append, List.mem_singleton] at hw
  exact hw.resolve_right h

omit [DecidableEq V] in
/-- A vertex of the support of the first part of an appended walk, other than its last entry, is
in the support of the appended walk without its last entry. -/
theorem mem_dropLast_support_append_left {u v w x : V} {p : G.Walk u v} (q : G.Walk v w)
    (hx : x ∈ p.support.dropLast) : x ∈ (p.append q).support.dropLast := by
  rw [support_append]
  by_cases hq : q.support.tail = []
  · rwa [hq, List.append_nil]
  · rw [List.dropLast_append_of_ne_nil hq]
    exact List.mem_append_left _ (List.dropLast_subset _ hx)

/-- A vertex of the support of the part of a walk before one of its vertices, other than its last
entry, is in the support of the walk without its last entry. -/
theorem mem_dropLast_support_of_mem_dropLast_takeUntil {u v w x : V} {p : G.Walk u v}
    (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support.dropLast) :
    x ∈ p.support.dropLast := by
  rw [← p.take_spec hw]
  exact mem_dropLast_support_append_left _ hx

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Separation in the box extended by one row -/

/-- A walk along the row `y` from `(b, y)` to `(a, y)`, for `a ≤ b`, through the points `(t, y)`
with `a ≤ t ≤ b` and the horizontal edges between them. -/
theorem exists_walk_row (y : ℤ) {a b : ℤ} (hab : a ≤ b) :
    ∃ p : (zdGraph 2).Walk ![b, y] ![a, y],
      (∀ v ∈ p.support, v 1 = y ∧ a ≤ v 0 ∧ v 0 ≤ b) ∧
      ∀ e ∈ p.edges, ∃ t : ℤ, a ≤ t ∧ t + 1 ≤ b ∧ e = s(![t, y], ![t + 1, y]) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b - a = n := ⟨(b - a).toNat, by omega⟩
  induction n generalizing b with
  | zero =>
    obtain rfl : b = a := by push_cast at hn; omega
    refine ⟨.nil, fun v hv => ?_, fun e he => by simp at he⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    simp
  | succ n ih =>
    obtain ⟨p, hp, hpe⟩ := ih (b := b - 1) (by push_cast at hn; omega)
      (by push_cast at hn ⊢; omega)
    have hadj : (zdGraph 2).Adj ![b, y] ![b - 1, y] := by
      rw [zdGraph_two_adj_iff]
      simp
    refine ⟨.cons hadj p, fun v hv => ?_, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · refine ⟨by simp, ?_, by simp⟩
        simp only [Matrix.cons_val_zero]
        push_cast at hn
        omega
      · obtain ⟨h1, h2, h3⟩ := hp v hv
        omega
    · rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · refine ⟨b - 1, by push_cast at hn; omega, by omega, ?_⟩
        rw [sub_add_cancel, Sym2.eq_swap]
      · obtain ⟨t, ht1, ht2, rfl⟩ := hpe e he
        exact ⟨t, ht1, by omega, rfl⟩

/-- **Separation in the box extended by one row.** Let `τ` be a bottom-top walk of the box
`Icc lo hi` (of height at least one) from `c`, and `σ` a walk in the box from a point `s` of the
bottom row strictly right of `c` to a vertex `x`. If a face at `x` is joined to the left column of
the dual box extended by one row below, by dual edges crossing neither an edge of `τ` nor the
vertical edge below `c`, then `σ` meets `τ`. -/
theorem exists_mem_support_of_dualConfig_mem_localConn_below {lo hi : LatticeSite 2}
    (h1 : lo 1 < hi 1) {c d : LatticeSite 2} (τ : (zdGraph 2).Walk c d)
    (hτ : ∀ v ∈ τ.support, v ∈ Icc lo hi) (hc : c 1 = lo 1) (hd : d 1 = hi 1)
    {s x : LatticeSite 2} (σ : (zdGraph 2).Walk s x) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hs : s 1 = lo 1) (hcs : c 0 < s 0) {f₀ f₁ : LatticeSite 2} (hf₀ : f₀ 0 = lo 0 - 1)
    (hf₁ : x 0 - 1 ≤ f₁ 0 ∧ f₁ 0 ≤ x 0 ∧ x 1 - 1 ≤ f₁ 1 ∧ f₁ 1 ≤ x 1)
    (hpath : dualConfig ({e | e ∈ τ.edges} ∪ {s(![c 0, lo 1 - 1], c)}) ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1 - 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f₁) :
    ∃ v ∈ σ.support, v ∈ τ.support := by
  have hcR := mem_Icc_two_iff.1 (hτ c τ.start_mem_support)
  have hsR := mem_Icc_two_iff.1 (hσ s σ.start_mem_support)
  have hadjc : (zdGraph 2).Adj ![c 0, lo 1 - 1] c := by
    rw [zdGraph_two_adj_iff]
    left
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
    omega
  have hadjs : (zdGraph 2).Adj ![s 0, lo 1 - 1] s := by
    rw [zdGraph_two_adj_iff]
    left
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
    omega
  obtain ⟨ρ, hρ, -⟩ := exists_walk_row (lo 1 - 1) (show s 0 ≤ hi 0 by omega)
  set τ' : (zdGraph 2).Walk ![c 0, lo 1 - 1] d := .cons hadjc τ with hτ'
  set σ' : (zdGraph 2).Walk ![hi 0, lo 1 - 1] x := ρ.append (.cons hadjs σ) with hσ'
  have hbox : ∀ v : LatticeSite 2, v ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) hi ↔
      lo 0 ≤ v 0 ∧ v 0 ≤ hi 0 ∧ lo 1 - 1 ≤ v 1 ∧ v 1 ≤ hi 1 := by
    intro v
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hτ'S : ∀ v ∈ τ'.support, v ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) hi := by
    intro v hv
    rw [hτ', SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rw [hbox]
    rcases hv with rfl | hv
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · have := mem_Icc_two_iff.1 (hτ v hv)
      omega
  have hσ'S : ∀ v ∈ σ'.support, v ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) hi := by
    intro v hv
    rw [hσ', SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hv
    rw [hbox]
    rcases hv with hv | rfl | hv
    · have := hρ v hv
      omega
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · have := mem_Icc_two_iff.1 (hσ v hv)
      omega
  have hedges : {e | e ∈ τ'.edges} = {e | e ∈ τ.edges} ∪ {s(![c 0, lo 1 - 1], c)} := by
    ext e
    simp only [hτ', SimpleGraph.Walk.edges_cons, List.mem_cons, mem_ofPred_eq, mem_union,
      mem_singleton_iff]
    tauto
  have hpath' : dualConfig {e | e ∈ τ'.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![(![lo 0, lo 1 - 1] : LatticeSite 2) 0 - 1,
        (![lo 0, lo 1 - 1] : LatticeSite 2) 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f₁ := by
    rw [hedges]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using hpath
  obtain ⟨v, hvσ, hvτ⟩ := exists_mem_support_of_dualConfig_mem_localConn
    (lo := ![lo 0, lo 1 - 1]) (hi := hi)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega) τ' hτ'S
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]) hd σ' hσ'S
    (by simp only [Matrix.cons_val_zero]) (f₀ := f₀) (f₁ := f₁)
    (by simp only [Matrix.cons_val_zero]; exact hf₀) hf₁ hpath'
  rw [hτ', SimpleGraph.Walk.support_cons, List.mem_cons] at hvτ
  rw [hσ', SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
    List.mem_cons] at hvσ
  rcases hvτ with rfl | hvτ
  · -- the vertex below `c` is on no part of `σ'`
    exfalso
    rcases hvσ with hv | hv | hv
    · have := hρ _ hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      omega
    · have := congrFun hv 0
      simp only [Matrix.cons_val_zero] at this
      omega
    · have := mem_Icc_two_iff.1 (hσ _ hv)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      omega
  · refine ⟨v, ?_, hvτ⟩
    have hvR := mem_Icc_two_iff.1 (hτ v hvτ)
    rcases hvσ with hv | rfl | hv
    · have := hρ v hv
      omega
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hvR
      omega
    · exact hv

/-- **Separation from the right, faces in the dual box.** A bottom-top walk `τ` of the box meets
every walk in the box from a point of the bottom row strictly right of its start to a vertex `x`
with a face joined to the left column of the dual box by dual edges crossing no edge of `τ`. -/
theorem exists_mem_support_of_lt_of_localConn {lo hi : LatticeSite 2} (h1 : lo 1 < hi 1)
    {c d : LatticeSite 2} (τ : (zdGraph 2).Walk c d) (hτ : ∀ v ∈ τ.support, v ∈ Icc lo hi)
    (hc : c 1 = lo 1) (hd : d 1 = hi 1)
    {s x : LatticeSite 2} (σ : (zdGraph 2).Walk s x) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hs : s 1 = lo 1) (hcs : c 0 < s 0) {f₀ f₁ : LatticeSite 2} (hf₀ : f₀ 0 = lo 0 - 1)
    (hf₁ : x 0 - 1 ≤ f₁ 0 ∧ f₁ 0 ≤ x 0 ∧ x 1 - 1 ≤ f₁ 1 ∧ f₁ 1 ≤ x 1)
    (hpath : dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f₁) :
    ∃ v ∈ σ.support, v ∈ τ.support := by
  have hcR := mem_Icc_two_iff.1 (hτ c τ.start_mem_support)
  refine exists_mem_support_of_dualConfig_mem_localConn_below h1 τ hτ hc hd σ hσ hs hcs hf₀ hf₁
    ?_
  have hsub : Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1] ⊆
      Icc (![lo 0 - 1, lo 1 - 1] : LatticeSite 2) ![hi 0, hi 1 - 1] := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
    omega
  have hext : s(![c 0, lo 1 - 1], c) ∈ (zdGraph 2).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
    left
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
    omega
  obtain ⟨p, hpS, hpE⟩ := exists_walk_of_mem_localConn hpath
  refine mem_localConn_of_walk p (fun v hv => hsub (hpS v hv)) fun e he => ?_
  have heL := p.edges_subset_edgeSet he
  obtain ⟨a, b, rfl, -, ha, -⟩ := exists_ne_of_mem_edges p he
  have habD := hpE _ he
  rw [mem_dualConfig_iff] at habD ⊢
  refine ⟨habD.1, fun hmem => ?_⟩
  rcases hmem with hmem | hmem
  · exact habD.2 hmem
  · -- the dual of the edge below `c` joins two faces of the row below the dual box
    rw [mem_singleton_iff] at hmem
    have hdual : s(a, b) = dualEdge s(![c 0, lo 1 - 1], c) :=
      (dualEdge_map_add_one_dualEdge heL).symm.trans (congrArg dualEdge hmem)
    have ha' : a ∈ dualEdge s(![c 0, lo 1 - 1], c) := by
      rw [← hdual]
      exact Sym2.mem_mk_left _ _
    have := face_of_mem_dualEdge hext (Sym2.mem_mk_left _ _) ha'
    have haT := mem_Icc_two_iff.1 (hpS a ha)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this haT
    omega

/-- **Separation from the right, both ends on the bottom row.** A bottom-top walk `τ` of the box
meets every walk in the box between two points of the bottom row on either side of its start. -/
theorem exists_mem_support_of_lt_of_lt {lo hi : LatticeSite 2} (h1 : lo 1 < hi 1)
    {c d : LatticeSite 2} (τ : (zdGraph 2).Walk c d) (hτ : ∀ v ∈ τ.support, v ∈ Icc lo hi)
    (hc : c 1 = lo 1) (hd : d 1 = hi 1)
    {s x : LatticeSite 2} (σ : (zdGraph 2).Walk s x) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hs : s 1 = lo 1) (hcs : c 0 < s 0) (hx : x 1 = lo 1) (hxc : x 0 < c 0) :
    ∃ v ∈ σ.support, v ∈ τ.support := by
  have hxR := mem_Icc_two_iff.1 (hσ x σ.end_mem_support)
  obtain ⟨ρ, hρ, hρe⟩ := exists_walk_row (lo 1 - 1) (show lo 0 - 1 ≤ x 0 - 1 by omega)
  refine exists_mem_support_of_dualConfig_mem_localConn_below h1 τ hτ hc hd σ hσ hs hcs
    (f₀ := ![lo 0 - 1, lo 1 - 1]) (f₁ := ![x 0 - 1, lo 1 - 1]) (by simp)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega) ?_
  rw [localConn_comm]
  refine mem_localConn_of_walk ρ (fun v hv => ?_) (fun e he => ?_)
  · have := hρ v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · obtain ⟨t, ht1, ht2, rfl⟩ := hρe e he
    -- a horizontal dual edge of the row below is the dual of a vertical edge below the box
    have hv : s(![t + 1, lo 1 - 1], ![t + 1, lo 1 - 1 + 1]) ∈ (zdGraph 2).edgeSet :=
      vertical_mem_edgeSet _ _
    have hdual : dualEdge s(![t + 1, lo 1 - 1], ![t + 1, lo 1 - 1 + 1]) =
        s(![t, lo 1 - 1], ![t + 1, lo 1 - 1]) := by
      rw [dualEdge_vertical, Sym2.eq_swap, add_sub_cancel_right]
    rw [← hdual, dualEdge_mem_dualConfig_iff hv]
    rintro (hmem | hmem)
    · have := mem_Icc_two_iff.1 (hτ _ (τ.fst_mem_support_of_mem_edges hmem))
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      omega
    · rw [mem_singleton_iff] at hmem
      have hmem' : (![t + 1, lo 1 - 1] : LatticeSite 2) ∈ s(![c 0, lo 1 - 1], c) := by
        rw [← hmem]
        exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.1 hmem' with h' | h'
      · have := congrFun h' 0
        simp only [Matrix.cons_val_zero] at this
        omega
      · have := congrFun h' 0
        simp only [Matrix.cons_val_zero] at this
        omega

/-- **A bottom-top walk separates the box.** Let `ρ` be a bottom-top walk of the box from `c`,
and `ρ₁`, `ρ₂` walks in the box starting on the bottom row on the left and on the right of `c`. If
both avoid `ρ`, they are disjoint. -/
theorem notMem_support_of_lt_of_lt {lo hi : LatticeSite 2} (h1 : lo 1 < hi 1)
    {c d a₁ b₁ a₂ b₂ : LatticeSite 2} (ρ : (zdGraph 2).Walk c d) (ρ₁ : (zdGraph 2).Walk a₁ b₁)
    (ρ₂ : (zdGraph 2).Walk a₂ b₂) (hρ : ∀ v ∈ ρ.support, v ∈ Icc lo hi)
    (hρ₁ : ∀ v ∈ ρ₁.support, v ∈ Icc lo hi) (hρ₂ : ∀ v ∈ ρ₂.support, v ∈ Icc lo hi)
    (hc : c 1 = lo 1) (hd : d 1 = hi 1) (ha₁ : a₁ 1 = lo 1) (ha₂ : a₂ 1 = lo 1)
    (h₁ : a₁ 0 < c 0) (h₂ : c 0 < a₂ 0) (hd₁ : ∀ v ∈ ρ₁.support, v ∉ ρ.support)
    (hd₂ : ∀ v ∈ ρ₂.support, v ∉ ρ.support) : ∀ v ∈ ρ₁.support, v ∉ ρ₂.support := by
  classical
  intro p hp₁ hp₂
  set σ := (ρ₂.takeUntil p hp₂).append (ρ₁.takeUntil p hp₁).reverse with hσ
  have hmem : ∀ v ∈ σ.support, v ∈ ρ₂.support ∨ v ∈ ρ₁.support := by
    intro v hv
    rw [hσ, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hv
    rcases hv with hv | hv
    · exact Or.inl (ρ₂.support_takeUntil_subset_support hp₂ hv)
    · exact Or.inr (ρ₁.support_takeUntil_subset_support hp₁ hv)
  obtain ⟨v, hv, hvρ⟩ := exists_mem_support_of_lt_of_lt h1 ρ hρ hc hd σ
    (fun v hv => (hmem v hv).elim (hρ₂ v) (hρ₁ v)) ha₂ h₂ ha₁ h₁
  rcases hmem v hv with hv' | hv'
  · exact hd₂ v hv' hvρ
  · exact hd₁ v hv' hvρ


/-! ### The explored faces at a chosen crossing

As in `Separation.lean`, `Γ` is a choice rule for the greedy exploration and `A` is the
exploration of `G` up to step `u`; both conditions are written out. -/

section Greedy

variable {lo hi : LatticeSite 2} {G : Config (LatticeSite 2)}
  {c d : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- The explored clusters of the exploration contain the left column of the dual box. -/
theorem mem_leftColumn_of_exploration {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) (y : ℤ) (hy0 : lo 1 ≤ y) (hy1 : y ≤ hi 1 - 1) :
    (![lo 0 - 1, y] : LatticeSite 2) ∈ A v := by
  have := mem_exploredCluster_of_leftColumn (lo := lo) (hi := hi)
    (ζ := G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) rfl y hy0 hy1
  rw [hA v hv] at this
  exact this

/-- **The explored faces at a chosen crossing reach the left column.** Let `A v` be an admissible
set of the exploration of `G`. Every vertex of the chosen crossing `Γ (A v)` has a face joined to
the left column of the dual box by dual edges crossing no edge of a walk `τ` in the box whose edges
are open in `G` and have no end on an earlier chosen crossing: the dual edges of the explored
cluster cross edges that are closed after the removals, or wire the left column outside the
box. -/
theorem exists_localConn_of_mem_support_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) (hright : ∀ f ∈ A v, f 0 ≠ hi 0) {x : LatticeSite 2}
    (hx : x ∈ (Γ (A v)).support) {c₁ d₁ : LatticeSite 2} (τ : (zdGraph 2).Walk c₁ d₁)
    (hτ : ∀ y ∈ τ.support, y ∈ Icc lo hi)
    (hτG : ∀ e ∈ τ.edges, e ∈ G ∧ ∀ y ∈ e, ∀ w < v, y ∉ (Γ (A w)).support) :
    ∃ f₀ f₁ : LatticeSite 2, f₀ 0 = lo 0 - 1 ∧
      (x 0 - 1 ≤ f₁ 0 ∧ f₁ 0 ≤ x 0 ∧ x 1 - 1 ≤ f₁ 1 ∧ f₁ 1 ≤ x 1) ∧
      dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f₁ := by
  obtain ⟨-, hc1, -, hd1, -, hΓe⟩ :=
    hΓ (A v) (mem_leftColumn_of_exploration hA hv) hright
  have hnil : ¬(Γ (A v)).Nil := fun hn => by
    have h' := congrFun (SimpleGraph.Walk.Nil.eq hn) 1
    omega
  obtain ⟨e, he, hxe⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).1 hx
  obtain ⟨heL, -, ⟨f, hfe, hfA⟩, -⟩ := hΓe e he
  have hfC : f ∈ cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] := by
    rw [hA v hv]
    exact hfA
  obtain ⟨p, hpS, hpζ⟩ := exists_walk_of_mem_exploredCluster hfC
    fun s hs => (forall_mem_Icc_of_mem_wired h1 (hle 0) rfl hs).1
  refine ⟨![lo 0 - 1, lo 1], f, by simp, face_of_mem_dualEdge heL hxe hfe,
    mem_localConn_of_walk p (fun y hy => exploredCluster_subset h1 (hle 0) rfl (hpS y hy))
      fun s hs => ?_⟩
  rcases hpζ s hs with ⟨hsD, -⟩ | ⟨y, -, -, rfl⟩
  · rw [mem_dualConfig_iff] at hsD ⊢
    refine ⟨hsD.1, fun hmem => hsD.2 ?_⟩
    obtain ⟨hG, hR⟩ := hτG _ hmem
    exact ⟨hG, fun ⟨z, hz, w, hw, hzw⟩ => hR z hz w hw hzw⟩
  · -- a wired edge of the left column is the dual of an edge with an end left of the box
    rw [mem_dualConfig_iff]
    refine ⟨vertical_mem_edgeSet _ _, fun hmem => ?_⟩
    rw [mem_ofPred_eq, dualEdge_vertical, Sym2.map_mk] at hmem
    have := mem_Icc_two_iff.1 (hτ _ (τ.snd_mem_support_of_mem_edges hmem))
    simp only [Pi.add_apply, Matrix.cons_val_zero, Pi.one_apply] at this
    omega

/-- **A crossing on the left meets an earlier chosen crossing.** Let `A w` be admissible and `q` a
walk in the box from a point of the bottom row to a vertex of `Γ (A w)`. Every bottom-top crossing
open in `G`, disjoint from `q` and starting on the bottom row strictly left of `q`, meets a chosen
crossing `Γ (A w')` with `w' < w`. -/
theorem exists_mem_support_of_lt_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {w : ℕ} (hw : w ≤ u) (hright : ∀ f ∈ A w, f 0 ≠ hi 0)
    {a₁ b₁ : LatticeSite 2} (γ : (zdGraph 2).Walk a₁ b₁) (hγ : ∀ y ∈ γ.support, y ∈ Icc lo hi)
    (ha₁ : a₁ 1 = lo 1) (hb₁ : b₁ 1 = hi 1) (hγG : ∀ e ∈ γ.edges, e ∈ G)
    {a₂ x : LatticeSite 2} (q : (zdGraph 2).Walk a₂ x) (hq : ∀ y ∈ q.support, y ∈ Icc lo hi)
    (ha₂ : a₂ 1 = lo 1) (hlt : a₁ 0 < a₂ 0) (hx : x ∈ (Γ (A w)).support)
    (hdisj : ∀ y ∈ q.support, y ∉ γ.support) :
    ∃ y ∈ γ.support, ∃ w' < w, y ∈ (Γ (A w')).support := by
  by_contra hno
  push Not at hno
  obtain ⟨f₀, f₁, hf₀, hf₁, hpath⟩ := exists_localConn_of_mem_support_of_exploration h1 hle hΓ hA
    hw hright hx γ hγ fun e he =>
      ⟨hγG e he, fun y hy w' hw' => hno y (mem_support_of_mem_edge γ he hy) w' hw'⟩
  obtain ⟨y, hyq, hyγ⟩ :=
    exists_mem_support_of_lt_of_localConn h1 γ hγ ha₁ hb₁ q hq ha₂ hlt hf₀ hf₁ hpath
  exact hdisj y hyq hyγ

/-- **Neighbouring rerouted crossings are disjoint.** Let `q₁` be a path from the bottom row to a
vertex `x₁` of a chosen crossing `Γ (A w₁)`, open in `G`, that meets no chosen crossing of index
`< w₂` before `x₁`; and let `q₂` be a walk from a point of the bottom row strictly right of the
start of `q₁` to a vertex `x₂` of `Γ (A w₂)`, `w₁ < w₂`, that meets no chosen crossing of index
`< W` before `x₂`, disjoint from `q₁`. Then `q₁` avoids every path `r₂` from `x₂` along
`Γ (A w₂)`. -/
theorem notMem_support_of_lt_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {w₁ w₂ W : ℕ} (hw₁₂ : w₁ < w₂) (hw₂W : w₂ < W) (hWu : W ≤ u + 1)
    (hadm : ∀ w < W, ∀ f ∈ A w, f 0 ≠ hi 0)
    {a₁ x₁ : LatticeSite 2} (q₁ : (zdGraph 2).Walk a₁ x₁) (hq₁P : q₁.IsPath)
    (hq₁ : ∀ y ∈ q₁.support, y ∈ Icc lo hi) (ha₁ : a₁ 1 = lo 1) (hq₁G : ∀ e ∈ q₁.edges, e ∈ G)
    (hx₁ : x₁ ∈ (Γ (A w₁)).support)
    (hq₁first : ∀ y ∈ q₁.support, y ≠ x₁ → ∀ w < w₂, y ∉ (Γ (A w)).support)
    {a₂ x₂ : LatticeSite 2} (q₂ : (zdGraph 2).Walk a₂ x₂) (hq₂ : ∀ y ∈ q₂.support, y ∈ Icc lo hi)
    (ha₂ : a₂ 1 = lo 1) (hlt : a₁ 0 < a₂ 0) (hx₂ : x₂ ∈ (Γ (A w₂)).support)
    (hq₂first : ∀ y ∈ q₂.support, y ≠ x₂ → ∀ w < W, y ∉ (Γ (A w)).support)
    (r₂ : (zdGraph 2).Walk x₂ (d (A w₂))) (hr₂P : r₂.IsPath)
    (hr₂ : ∀ y ∈ r₂.support, y ∈ (Γ (A w₂)).support)
    (hr₂E : ∀ e ∈ r₂.edges, e ∈ (Γ (A w₂)).edges)
    (hdisj : ∀ y ∈ q₁.support, y ∉ q₂.support) :
    ∀ y ∈ q₁.support, y ∉ r₂.support := by
  classical
  intro p hp₁ hp₂
  have hu₂ : w₂ ≤ u := by omega
  have hdis₂ := forall_mem_of_exploration h1 hΓ hA hu₂ (hadm w₂ hw₂W)
  obtain ⟨-, -, -, hd₂, hΓS, -⟩ :=
    hΓ (A w₂) (mem_leftColumn_of_exploration hA hu₂) (hadm w₂ hw₂W)
  -- `p` is neither the end of `q₁` nor the start of `r₂`
  have hpx₁ : x₁ ≠ p := by
    rintro rfl
    exact hdis₂.2 x₁ (hr₂ x₁ hp₂) w₁ hw₁₂ hx₁
  have hpx₂ : x₂ ≠ p := by
    rintro rfl
    exact hdisj x₂ hp₁ q₂.end_mem_support
  have hx₁q := SimpleGraph.Walk.endpoint_notMem_support_takeUntil hq₁P hp₁ hpx₁
  have hx₂r := SimpleGraph.Walk.start_notMem_support_dropUntil hr₂P hp₂ hpx₂
  set τ := (q₁.takeUntil p hp₁).append (r₂.dropUntil p hp₂) with hτ
  have hτmem : ∀ y ∈ τ.support, y ∈ (q₁.takeUntil p hp₁).support ∨
      y ∈ (r₂.dropUntil p hp₂).support := fun y hy => by
    rwa [hτ, SimpleGraph.Walk.mem_support_append_iff] at hy
  have hτS : ∀ y ∈ τ.support, y ∈ Icc lo hi := fun y hy => by
    rcases hτmem y hy with hy | hy
    · exact hq₁ y (q₁.support_takeUntil_subset_support hp₁ hy)
    · exact hΓS y (hr₂ y (r₂.support_dropUntil_subset_support hp₂ hy))
  have hτG : ∀ e ∈ τ.edges, e ∈ G ∧ ∀ y ∈ e, ∀ w < w₂, y ∉ (Γ (A w)).support := by
    intro e he
    rw [hτ, SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · refine ⟨hq₁G e (q₁.edges_takeUntil_subset_edges hp₁ he), fun y hy w hw => ?_⟩
      have hy' := mem_support_of_mem_edge _ he hy
      exact hq₁first y (q₁.support_takeUntil_subset_support hp₁ hy')
        (fun h => hx₁q (h ▸ hy')) w hw
    · refine ⟨hdis₂.1 e (hr₂E e (r₂.edges_dropUntil_subset_edges hp₂ he)), fun y hy w hw => ?_⟩
      have hy' := mem_support_of_mem_edge _ he hy
      exact hdis₂.2 y (hr₂ y (r₂.support_dropUntil_subset_support hp₂ hy')) w hw
  obtain ⟨f₀, f₁, hf₀, hf₁, hpath⟩ := exists_localConn_of_mem_support_of_exploration h1 hle hΓ hA
    hu₂ (hadm w₂ hw₂W) hx₂ τ hτS hτG
  obtain ⟨y, hyq, hyτ⟩ :=
    exists_mem_support_of_lt_of_localConn h1 τ hτS ha₁ hd₂ q₂ hq₂ ha₂ hlt hf₀ hf₁ hpath
  rcases hτmem y hyτ with hy | hy
  · exact hdisj y (q₁.support_takeUntil_subset_support hp₁ hy) hyq
  · exact hq₂first y hyq (fun h => hx₂r (h ▸ hy)) w₂ hw₂W
      (hr₂ y (r₂.support_dropUntil_subset_support hp₂ hy))


/-! ### Rerouting a family of disjoint crossings -/

/-- **Rerouting, by induction from the right.** Let `S` be a finite family of disjoint bottom-top
crossings of the box, open in `G`, each meeting a chosen crossing of index `< W` (all admissible).
Each member `i` is cut at a vertex `(P i).2.1` of a chosen crossing `Γ (A (w i))`, `w i < W`: the
part before the cut is a path `(P i).2.2` inside the member, the part after it a path `(R i).2.2`
inside `Γ (A (w i))` to its top end. The indices increase from left to right, the rightmost member
is cut at its first vertex on a chosen crossing of index `< W`, and the new walks are pairwise
disjoint. The cuts are chosen from right to left: each member is cut at its first vertex on a chosen
crossing of index less than that of its right neighbour. -/
theorem exists_reroute_aux (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {ι : Type*} [DecidableEq ι] {a b : ι → LatticeSite 2} (γ : ∀ i, (zdGraph 2).Walk (a i) (b i))
    (S : Finset ι) :
    (∀ i ∈ S, ∀ x ∈ (γ i).support, x ∈ Icc lo hi) → (∀ i ∈ S, a i 1 = lo 1) →
      (∀ i ∈ S, b i 1 = hi 1) → (∀ i ∈ S, ∀ e ∈ (γ i).edges, e ∈ G) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
      ∀ W : ℕ, W ≤ u + 1 → (∀ w < W, ∀ f ∈ A w, f 0 ≠ hi 0) →
      (∀ i ∈ S, ∃ x ∈ (γ i).support, ∃ w < W, x ∈ (Γ (A w)).support) →
      ∃ (w : ι → ℕ) (P R : ι → Σ x y : LatticeSite 2, (zdGraph 2).Walk x y),
        (∀ i ∈ S, w i < W ∧ (P i).1 = a i ∧ (P i).2.1 = (R i).1 ∧ (R i).2.1 = d (A (w i)) ∧
          (P i).2.2.IsPath ∧ (R i).2.2.IsPath ∧
          (∀ x ∈ (P i).2.2.support, x ∈ (γ i).support) ∧
          (∀ e ∈ (P i).2.2.edges, e ∈ (γ i).edges) ∧
          (∀ x ∈ (R i).2.2.support, x ∈ (Γ (A (w i))).support) ∧
          ∀ e ∈ (R i).2.2.edges, e ∈ (Γ (A (w i))).edges) ∧
        (∀ i ∈ S, ∀ j ∈ S, a i 0 < a j 0 → w i < w j) ∧
        (∀ i ∈ S, (∀ j ∈ S, a j 0 ≤ a i 0) →
          ∀ x ∈ (P i).2.2.support, x ≠ (P i).2.1 → ∀ w' < W, x ∉ (Γ (A w')).support) ∧
        (∀ i ∈ S, ∀ x ∈ (P i).2.2.support, x ≠ (P i).2.1 → ∀ w' < w i,
          x ∉ (Γ (A w')).support) ∧
        (∀ i ∈ S, ∀ x ∈ (P i).2.2.support, x ≠ (P i).2.1 → x ∈ (γ i).support.dropLast) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x, x ∈ (P i).2.2.support ∨ x ∈ (R i).2.2.support →
          x ∉ (P j).2.2.support ∧ x ∉ (R j).2.2.support := by
  classical
  induction S using Finset.induction_on_max_value (fun i => a i 0) with
  | empty =>
    intro _ _ _ _ _ W _ _ _
    refine ⟨fun _ => 0, fun _ => ⟨0, 0, .nil⟩, fun _ => ⟨0, 0, .nil⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp
  | insert r S hrS hmax ih =>
    intro hS ha hb hG hdisj W hWu hadm hmeet
    have hS' : ∀ i ∈ S, i ∈ insert r S := fun i hi => Finset.mem_insert_of_mem hi
    have hr : r ∈ insert r S := Finset.mem_insert_self r S
    have hrne : ∀ k ∈ S, k ≠ r := fun k hk h => hrS (h ▸ hk)
    -- distinct members start at distinct points of the bottom row
    have hne : ∀ i ∈ insert r S, ∀ j ∈ insert r S, i ≠ j → a i 0 ≠ a j 0 := by
      intro i hi j hj hij h
      have haij : a i = a j :=
        (eq_vec_two_iff.2 ⟨h, (ha i hi).trans (ha j hj).symm⟩).trans (eq_vec_two (a j)).symm
      exact hdisj i hi j hj hij (a i) (γ i).start_mem_support
        (by rw [haij]; exact (γ j).start_mem_support)
    have hlt : ∀ k ∈ S, a k 0 < a r 0 := fun k hk =>
      lt_of_le_of_ne (hmax k hk) (hne k (hS' k hk) r hr (hrne k hk))
    have hΓdat : ∀ w' < W, d (A w') 1 = hi 1 ∧ ∀ y ∈ (Γ (A w')).support, y ∈ Icc lo hi := by
      intro w' hw'
      obtain ⟨-, -, -, hd', hS'', -⟩ :=
        hΓ (A w') (mem_leftColumn_of_exploration hA (by omega)) (hadm w' hw')
      exact ⟨hd', hS''⟩
    -- the rightmost member is cut at its first vertex on a chosen crossing of index `< W`
    obtain ⟨x, hx, w₀, hw₀, hxw₀⟩ := hmeet r hr
    obtain ⟨h₀, q₀, s₀, hqs, hh₀, hq₀⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
      (T := {y | ¬∃ w < W, y ∈ (Γ (A w)).support}) ((γ r).takeUntil x hx)
      (fun h => h ⟨w₀, hw₀, hxw₀⟩)
    obtain ⟨wr, hwr, hhr⟩ : ∃ w < W, h₀ ∈ (Γ (A w)).support := by
      by_contra h
      exact hh₀ h
    have hwru : wr ≤ u := by omega
    have hrr := forall_mem_of_exploration h1 hΓ hA hwru (hadm wr hwr)
    set qr := q₀.bypass with hqr
    set rr := ((Γ (A wr)).dropUntil h₀ hhr).bypass with hrr'
    have hqrγ : ∀ y ∈ qr.support, y ∈ (γ r).support := fun y hy => by
      have hy₀ : y ∈ ((γ r).takeUntil x hx).support := by
        rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl (q₀.support_bypass_subset_support hy)
      exact (γ r).support_takeUntil_subset_support hx hy₀
    have hqrE : ∀ e ∈ qr.edges, e ∈ (γ r).edges := fun e he => by
      have he₀ : e ∈ ((γ r).takeUntil x hx).edges := by
        rw [← hqs, SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ (q₀.edges_bypass_subset_edges he)
      exact (γ r).edges_takeUntil_subset_edges hx he₀
    have hqrfirst : ∀ y ∈ qr.support, y ≠ h₀ → ∀ w' < W, y ∉ (Γ (A w')).support :=
      fun y hy hyh w' hw' hyw => hq₀ y
        (SimpleGraph.Walk.mem_dropLast_support_of_ne (q₀.support_bypass_subset_support hy) hyh)
        ⟨w', hw', hyw⟩
    have hqrdrop : ∀ y ∈ qr.support, y ≠ h₀ → y ∈ (γ r).support.dropLast := fun y hy hyh => by
      have hy₀ : y ∈ q₀.support.dropLast :=
        SimpleGraph.Walk.mem_dropLast_support_of_ne (q₀.support_bypass_subset_support hy) hyh
      have hy₁ := SimpleGraph.Walk.mem_dropLast_support_append_left s₀ hy₀
      rw [hqs] at hy₁
      exact SimpleGraph.Walk.mem_dropLast_support_of_mem_dropLast_takeUntil hx hy₁
    have hrrΓ : ∀ y ∈ rr.support, y ∈ (Γ (A wr)).support := fun y hy =>
      (Γ (A wr)).support_dropUntil_subset_support hhr
        (((Γ (A wr)).dropUntil h₀ hhr).support_bypass_subset_support hy)
    have hrrE : ∀ e ∈ rr.edges, e ∈ (Γ (A wr)).edges := fun e he =>
      (Γ (A wr)).edges_dropUntil_subset_edges hhr
        (((Γ (A wr)).dropUntil h₀ hhr).edges_bypass_subset_edges he)
    have hqrS : ∀ y ∈ qr.support, y ∈ Icc lo hi := fun y hy => hS r hr y (hqrγ y hy)
    -- the other members meet a chosen crossing of index `< wr`: cut them first
    obtain ⟨w, P, R, hPR, hmono, hfirst, hfirst', hdrop, hdisj'⟩ :=
      ih (fun i hi => hS i (hS' i hi))
      (fun i hi => ha i (hS' i hi)) (fun i hi => hb i (hS' i hi)) (fun i hi => hG i (hS' i hi))
      (fun i hi j hj => hdisj i (hS' i hi) j (hS' j hj)) wr (by omega)
      (fun w' hw' => hadm w' (by omega)) fun k hk =>
        exists_mem_support_of_lt_of_exploration h1 hle hΓ hA hwru (hadm wr hwr) (γ k)
          (hS k (hS' k hk)) (ha k (hS' k hk)) (hb k (hS' k hk)) (hG k (hS' k hk)) qr hqrS
          (ha r hr) (hlt k hk) hhr fun y hy hyk =>
            hdisj r hr k (hS' k hk) (hrne k hk).symm y (hqrγ y hy) hyk
    -- the part of the new walk inside the rightmost member avoids every other new walk
    have hqpart : ∀ k ∈ S, ∀ y, y ∈ (P k).2.2.support ∨ y ∈ (R k).2.2.support →
        y ∉ qr.support := by
      intro k hk y hy hyq
      obtain ⟨hwk, -, -, -, -, -, hPγ, -, hRΓ, -⟩ := hPR k hk
      rcases hy with hy | hy
      · exact hdisj r hr k (hS' k hk) (hrne k hk).symm y (hqrγ y hyq) (hPγ y hy)
      · by_cases hyh : y = h₀
        · rw [hyh] at hy
          exact hrr.2 h₀ hhr (w k) hwk (hRΓ h₀ hy)
        · exact hqrfirst y hyq hyh (w k) (by omega) (hRΓ y hy)
    -- the new walks of the other members, as walks
    have hρ : ∀ i ∈ S, ∃ ρ : (zdGraph 2).Walk (a i) (d (A (w i))),
        ∀ y, y ∈ ρ.support ↔ y ∈ (P i).2.2.support ∨ y ∈ (R i).2.2.support := by
      intro i hi
      obtain ⟨-, hP1, hP2, hR2, -⟩ := hPR i hi
      refine ⟨((P i).2.2.append ((R i).2.2.copy hP2.symm rfl)).copy hP1 hR2, fun y => ?_⟩
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_copy]
    have hρS : ∀ i ∈ S, ∀ y, y ∈ (P i).2.2.support ∨ y ∈ (R i).2.2.support →
        y ∈ Icc lo hi := by
      intro i hi y hy
      obtain ⟨hwi, -, -, -, -, -, hPγ, -, hRΓ, -⟩ := hPR i hi
      rcases hy with hy | hy
      · exact hS i (hS' i hi) y (hPγ y hy)
      · exact (hΓdat (w i) (by omega)).2 y (hRΓ y hy)
    have hkey : ∀ k ∈ S, ∀ y, y ∈ (P k).2.2.support ∨ y ∈ (R k).2.2.support →
        y ∉ qr.support ∧ y ∉ rr.support := by
      intro k hk
      obtain ⟨r', hr'S, hr'max⟩ := Finset.exists_max_image S (fun i => a i 0) ⟨k, hk⟩
      -- the left neighbour `r'` of `r`: the separation argument
      have hpair : ∀ y, y ∈ (P r').2.2.support ∨ y ∈ (R r').2.2.support →
          y ∉ qr.support ∧ y ∉ rr.support := by
        intro y hy
        refine ⟨hqpart r' hr'S y hy, fun hyr => ?_⟩
        obtain ⟨hw', hP1, hP2, -, hPP, -, hPγ, hPE, hRΓ, -⟩ := hPR r' hr'S
        rcases hy with hy | hy
        · have hx₁ : (P r').2.1 ∈ (Γ (A (w r'))).support := by
            rw [hP2]
            exact hRΓ _ (R r').2.2.start_mem_support
          exact notMem_support_of_lt_of_exploration h1 hle hΓ hA hw' hwr hWu hadm (P r').2.2
            hPP (fun z hz => hS r' (hS' r' hr'S) z (hPγ z hz))
            (by rw [hP1]; exact ha r' (hS' r' hr'S))
            (fun e he => hG r' (hS' r' hr'S) e (hPE e he)) hx₁ (hfirst r' hr'S hr'max) qr hqrS
            (ha r hr) (by rw [hP1]; exact hlt r' hr'S) hhr hqrfirst rr
            (SimpleGraph.Walk.bypass_isPath _) hrrΓ hrrE
            (fun z hz hzq =>
              hdisj r' (hS' r' hr'S) r hr (hrne r' hr'S) z (hPγ z hz) (hqrγ z hzq))
            y hy hyr
        · exact hrr.2 y (hrrΓ y hyr) (w r') hw' (hRΓ y hy)
      by_cases hkr' : k = r'
      · subst hkr'
        exact hpair
      · -- the other members: `r'` separates them from `r`
        obtain ⟨ρk, hρk⟩ := hρ k hk
        obtain ⟨ρ', hρ'⟩ := hρ r' hr'S
        have hk' : a k 0 < a r' 0 :=
          lt_of_le_of_ne (hr'max k hk) (hne k (hS' k hk) r' (hS' r' hr'S) hkr')
        have hsep := notMem_support_of_lt_of_lt h1 ρ' ρk (qr.append rr)
          (fun z hz => hρS r' hr'S z ((hρ' z).1 hz)) (fun z hz => hρS k hk z ((hρk z).1 hz))
          (fun z hz => by
            rw [SimpleGraph.Walk.mem_support_append_iff] at hz
            rcases hz with hz | hz
            · exact hqrS z hz
            · exact (hΓdat wr hwr).2 z (hrrΓ z hz))
          (ha r' (hS' r' hr'S)) (hΓdat (w r') (by have := (hPR r' hr'S).1; omega)).1
          (ha k (hS' k hk)) (ha r hr) hk' (hlt r' hr'S)
          (fun z hz hz' => (hdisj' k hk r' hr'S hkr' z ((hρk z).1 hz)).elim fun h₁ h₂ =>
            ((hρ' z).1 hz').elim h₁ h₂)
          (fun z hz hz' => by
            rw [SimpleGraph.Walk.mem_support_append_iff] at hz
            have := hpair z ((hρ' z).1 hz')
            rcases hz with hz | hz
            · exact this.1 hz
            · exact this.2 hz)
        intro y hy
        have hy' := hsep y ((hρk y).2 hy)
        rw [SimpleGraph.Walk.mem_support_append_iff] at hy'
        exact ⟨fun h => hy' (Or.inl h), fun h => hy' (Or.inr h)⟩
    have hwr' : Function.update w r wr r = wr := Function.update_self _ _ _
    have hPr : Function.update P r ⟨a r, h₀, qr⟩ r = ⟨a r, h₀, qr⟩ := Function.update_self _ _ _
    have hRr : Function.update R r ⟨h₀, d (A wr), rr⟩ r = ⟨h₀, d (A wr), rr⟩ :=
      Function.update_self _ _ _
    have hwk : ∀ k ∈ S, Function.update w r wr k = w k := fun k hk =>
      Function.update_of_ne (hrne k hk) _ _
    have hPk : ∀ k ∈ S, Function.update P r ⟨a r, h₀, qr⟩ k = P k := fun k hk =>
      Function.update_of_ne (hrne k hk) _ _
    have hRk : ∀ k ∈ S, Function.update R r ⟨h₀, d (A wr), rr⟩ k = R k := fun k hk =>
      Function.update_of_ne (hrne k hk) _ _
    refine ⟨Function.update w r wr, Function.update P r ⟨a r, h₀, qr⟩,
      Function.update R r ⟨h₀, d (A wr), rr⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [hwr', hPr, hRr]
        exact ⟨hwr, rfl, rfl, rfl, SimpleGraph.Walk.bypass_isPath _,
          SimpleGraph.Walk.bypass_isPath _, hqrγ, hqrE, hrrΓ, hrrE⟩
      · rw [hwk i hi', hPk i hi', hRk i hi']
        obtain ⟨hwi, h2⟩ := hPR i hi'
        exact ⟨by omega, h2⟩
    · intro i hi j hj hij
      rcases Finset.mem_insert.1 hi with rfl | hi' <;>
        rcases Finset.mem_insert.1 hj with rfl | hj'
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (not_lt.2 (hlt j hj').le)
      · rw [hwk i hi', hwr']
        exact (hPR i hi').1
      · rw [hwk i hi', hwk j hj']
        exact hmono i hi' j hj' hij
    · intro i hi himax
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [hPr]
        exact hqrfirst
      · exact absurd (himax r hr) (not_le.2 (hlt i hi'))
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [hPr, hwr']
        exact fun y hy hyh w' hw' => hqrfirst y hy hyh w' (by omega)
      · rw [hPk i hi', hwk i hi']
        exact hfirst' i hi'
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [hPr]
        exact hqrdrop
      · rw [hPk i hi']
        exact hdrop i hi'
    · intro i hi j hj hij y hy
      rcases Finset.mem_insert.1 hi with rfl | hi' <;>
        rcases Finset.mem_insert.1 hj with rfl | hj'
      · exact absurd rfl hij
      · rw [hPr, hRr] at hy
        rw [hPk j hj', hRk j hj']
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have := hkey j hj' y (Or.inl h)
          rcases hy with hy | hy
          · exact this.1 hy
          · exact this.2 hy
        · have := hkey j hj' y (Or.inr h)
          rcases hy with hy | hy
          · exact this.1 hy
          · exact this.2 hy
      · rw [hPk i hi', hRk i hi'] at hy
        rw [hPr, hRr]
        exact hkey i hi' y hy
      · rw [hPk i hi', hRk i hi'] at hy
        rw [hPk j hj', hRk j hj']
        exact hdisj' i hi' j hj' hij y hy

/-- **Rerouting a family of disjoint crossings to greedy tips.** Once the explored cluster
reaches the right column of the dual box, every finite family `S` of pairwise disjoint bottom-top
crossings of the box open in `G` can be rerouted: each member `i` is replaced by a walk from its
own start to the top end `d (A (w i))` of an admissible chosen crossing, running inside the member
and that chosen crossing, open in `G`; the indices `w i` increase from left to right (so they are
distinct), and the new walks are pairwise disjoint. Moreover each new walk is open after the
removals of its step (its edges have no end on a chosen crossing of smaller index), and its
vertices and edges come from the chosen crossing or from the member, in which case the vertex is
not the last one of the member. Every vertex of a new walk before its last entry is a vertex of the
member before its last entry or a vertex of the chosen crossing other than its top end. -/
theorem exists_reroute_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    (hu : ∃ f ∈ A u, f 0 = hi 0) {ι : Type*} (S : Finset ι) {a b : ι → LatticeSite 2}
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)) (hγ : ∀ i ∈ S, ∀ x ∈ (γ i).support, x ∈ Icc lo hi)
    (ha : ∀ i ∈ S, a i 1 = lo 1) (hb : ∀ i ∈ S, b i 1 = hi 1)
    (hγG : ∀ i ∈ S, ∀ e ∈ (γ i).edges, e ∈ G)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) :
    ∃ (w : ι → ℕ) (γ' : ∀ i, Σ y : LatticeSite 2, (zdGraph 2).Walk (a i) y),
      (∀ i ∈ S, w i < u ∧ (∀ f ∈ A (w i), f 0 ≠ hi 0) ∧ (γ' i).1 = d (A (w i))) ∧
      (∀ i ∈ S, ∀ j ∈ S, a i 0 < a j 0 → w i < w j) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → w i ≠ w j) ∧
      (∀ i ∈ S, ∀ x ∈ (γ' i).2.support, x ∈ (γ i).support ∨ x ∈ (Γ (A (w i))).support) ∧
      (∀ i ∈ S, ∀ e ∈ (γ' i).2.edges, e ∈ G) ∧
      (∀ i ∈ S, ∀ x ∈ (γ' i).2.support, x ∈ Icc lo hi) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ (γ' i).2.support, x ∉ (γ' j).2.support) ∧
      (∀ i ∈ S, ∀ x ∈ (γ' i).2.support,
        x ∈ (γ i).support.dropLast ∨ x ∈ (Γ (A (w i))).support) ∧
      (∀ i ∈ S, ∀ e ∈ (γ' i).2.edges, ∀ y ∈ e, ∀ w' < w i, y ∉ (Γ (A w')).support) ∧
      (∀ i ∈ S, ∀ e ∈ (γ' i).2.edges, e ∈ (γ i).edges ∨ e ∈ (Γ (A (w i))).edges) ∧
      ∀ i ∈ S, ∀ x ∈ (γ' i).2.support.dropLast,
        x ∈ (γ i).support.dropLast ∨ (x ∈ (Γ (A (w i))).support ∧ x ≠ d (A (w i))) := by
  classical
  -- the first step at which the explored cluster reaches the right column
  have hex : ∃ v, v ≤ u ∧ ∃ f ∈ A v, f 0 = hi 0 := ⟨u, le_rfl, hu⟩
  obtain ⟨hu₀u, hu₀f⟩ := Nat.find_spec hex
  have hA₀ := fun v (hv : v ≤ Nat.find hex) => hA v (hv.trans hu₀u)
  have hadm : ∀ w < Nat.find hex, ∀ f ∈ A w, f 0 ≠ hi 0 := fun w hw f hf hf0 =>
    Nat.find_min hex hw ⟨by omega, f, hf, hf0⟩
  obtain ⟨w, P, R, hPR, hmono, -, hfirst', hdrop, hdisj'⟩ :=
    exists_reroute_aux h1 hle hΓ hA γ S hγ ha hb hγG
    hdisj (Nat.find hex) (by omega) hadm fun i hi =>
      exists_mem_support_of_exploration h1 hle hA₀ hu₀f (γ i) (hγ i hi) (ha i hi) (hb i hi)
        (hγG i hi)
  have hwd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → w i ≠ w j := by
    intro i hi j hj hij hw
    have hne : a i 0 ≠ a j 0 := fun h => by
      have haij : a i = a j :=
        (eq_vec_two_iff.2 ⟨h, (ha i hi).trans (ha j hj).symm⟩).trans (eq_vec_two (a j)).symm
      exact hdisj i hi j hj hij (a i) (γ i).start_mem_support
        (by rw [haij]; exact (γ j).start_mem_support)
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hmono i hi j hj h).ne hw
    · exact (hmono j hj i hi h).ne' hw
  set γ' : ∀ i, Σ y : LatticeSite 2, (zdGraph 2).Walk (a i) y := fun i =>
    if hi : i ∈ S then ⟨d (A (w i)), ((P i).2.2.append
      ((R i).2.2.copy (hPR i hi).2.2.1.symm rfl)).copy (hPR i hi).2.1 (hPR i hi).2.2.2.1⟩
    else ⟨a i, .nil⟩ with hγ'
  have hγ'S : ∀ i ∈ S, (γ' i).1 = d (A (w i)) ∧
      (∀ x, x ∈ (γ' i).2.support ↔ x ∈ (P i).2.2.support ∨ x ∈ (R i).2.2.support) ∧
      ∀ e ∈ (γ' i).2.edges, e ∈ (P i).2.2.edges ∨ e ∈ (R i).2.2.edges := by
    intro i hi
    rw [hγ']
    dsimp only
    rw [dite_eq_left hi]
    refine ⟨rfl, fun x => ?_, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_copy]
    · rwa [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_append, List.mem_append,
        SimpleGraph.Walk.edges_copy] at he
  have hdat : ∀ i ∈ S, (∀ e ∈ (Γ (A (w i))).edges, e ∈ G) ∧
      ∀ y ∈ (Γ (A (w i))).support, y ∈ Icc lo hi := by
    intro i hi
    have hwi : w i ≤ u := by have := (hPR i hi).1; omega
    obtain ⟨-, -, -, -, hS'', -⟩ :=
      hΓ (A (w i)) (mem_leftColumn_of_exploration hA hwi) (hadm _ (hPR i hi).1)
    exact ⟨(forall_mem_of_exploration h1 hΓ hA hwi (hadm _ (hPR i hi).1)).1, hS''⟩
  refine ⟨w, γ', fun i hi => ⟨by have := (hPR i hi).1; omega, hadm _ (hPR i hi).1,
    (hγ'S i hi).1⟩, hmono, hwd, fun i hi x hx => ?_, fun i hi e he => ?_,
    fun i hi x hx => ?_, fun i hi j hj hij x hx hx' => ?_, fun i hi x hx => ?_,
    fun i hi e he y hy w' hw' => ?_, fun i hi e he => ?_, fun i hi x hx => ?_⟩
  · obtain ⟨-, -, -, -, -, -, hPγ, -, hRΓ, -⟩ := hPR i hi
    rcases ((hγ'S i hi).2.1 x).1 hx with h | h
    · exact Or.inl (hPγ x h)
    · exact Or.inr (hRΓ x h)
  · obtain ⟨-, -, -, -, -, -, -, hPE, -, hRE⟩ := hPR i hi
    rcases (hγ'S i hi).2.2 e he with h | h
    · exact hγG i hi e (hPE e h)
    · exact (hdat i hi).1 e (hRE e h)
  · obtain ⟨-, -, -, -, -, -, hPγ, -, hRΓ, -⟩ := hPR i hi
    rcases ((hγ'S i hi).2.1 x).1 hx with h | h
    · exact hγ i hi x (hPγ x h)
    · exact (hdat i hi).2 x (hRΓ x h)
  · have h₁ := hdisj' i hi j hj hij x (((hγ'S i hi).2.1 x).1 hx)
    rcases ((hγ'S j hj).2.1 x).1 hx' with h | h
    · exact h₁.1 h
    · exact h₁.2 h
  · obtain ⟨-, -, hP2, -, -, -, -, -, hRΓ, -⟩ := hPR i hi
    rcases ((hγ'S i hi).2.1 x).1 hx with h | h
    · by_cases hxc : x = (P i).2.1
      · refine Or.inr (hRΓ x ?_)
        rw [hxc, hP2]
        exact (R i).2.2.start_mem_support
      · exact Or.inl (hdrop i hi x h hxc)
    · exact Or.inr (hRΓ x h)
  · obtain ⟨hwi, -, hP2, -, -, -, -, -, hRΓ, -⟩ := hPR i hi
    have hwiu : w i ≤ u := by omega
    have hΓdis := (forall_mem_of_exploration h1 hΓ hA hwiu (hadm _ hwi)).2
    have hRst : (P i).2.1 ∈ (Γ (A (w i))).support := by
      rw [hP2]
      exact hRΓ _ (R i).2.2.start_mem_support
    rcases (hγ'S i hi).2.2 e he with h | h
    · have hyP := mem_support_of_mem_edge _ h hy
      by_cases hyc : y = (P i).2.1
      · rw [hyc]
        exact hΓdis _ hRst w' hw'
      · exact hfirst' i hi y hyP hyc w' hw'
    · exact hΓdis y (hRΓ y (mem_support_of_mem_edge _ h hy)) w' hw'
  · obtain ⟨-, -, -, -, -, -, -, hPE, -, hRE⟩ := hPR i hi
    rcases (hγ'S i hi).2.2 e he with h | h
    · exact Or.inl (hPE e h)
    · exact Or.inr (hRE e h)
  · -- the part before the end: the member before the junction, the chosen crossing before its tip
    obtain ⟨-, -, hP2, hR2, hPp, hRp, -, -, hRΓ, -⟩ := hPR i hi
    have hsupp : (γ' i).2.support.dropLast =
        (P i).2.2.support.dropLast ++ (R i).2.2.support.dropLast := by
      rw [hγ']
      dsimp only
      rw [dite_eq_left hi, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_append_eq_support_dropLast_append, SimpleGraph.Walk.support_copy,
        List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil _)]
    rw [hsupp, List.mem_append] at hx
    rcases hx with hx | hx
    · -- a vertex of the path `P i` before its end is not its end
      have hnd := hPp.support_nodup
      rw [← (P i).2.2.dropLast_support_concat, List.nodup_append] at hnd
      have hne : x ≠ (P i).2.1 := fun h => hnd.2.2 x hx _ (List.mem_singleton_self _) h
      exact Or.inl (hdrop i hi x (List.dropLast_subset _ hx) hne)
    · have hnd := hRp.support_nodup
      rw [← (R i).2.2.dropLast_support_concat, List.nodup_append] at hnd
      have hne : x ≠ (R i).2.1 := fun h => hnd.2.2 x hx _ (List.mem_singleton_self _) h
      exact Or.inr ⟨hRΓ x (List.dropLast_subset _ hx), hR2 ▸ hne⟩

end Greedy

end PercLib.Models.Planar
