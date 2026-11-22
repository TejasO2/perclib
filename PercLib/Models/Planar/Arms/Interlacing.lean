/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55 (arms, their cyclic order, pivotal edges); G. Grimmett,
Percolation, 2nd ed., Springer, 1999, Section 11.2 (planar duality).
The proofs below derive these facts from quad duality and do not follow either text.
-/
module

public import PercLib.Models.Planar.Arms.QuadDuality
public import PercLib.Models.Planar.Gluing
public import PercLib.Percolation.Bond.Pivotal

/-!
# Interlacing, order of arms and pivotal edges on the square lattice

Consequences of quad duality (`mem_arcCrossing_iff_dualConfig_notMem_arcCrossing`) for paths in a
box `R = Icc lo hi` of `ℤ²`. Boundary points are compared by their perimeter positions
(`perimeterPos`, counterclockwise from `lo`). Two pairs of boundary points **interlace** when one
point of the second pair lies strictly between the two points of the first, and the other
strictly outside them; the pairs then alternate around the boundary. Faces are dual vertices, the
face `f` standing for the unit square with lower-left corner `f`; as in `QuadDuality.lean`, the
dual paths in the dual box `Icc (lo - 1) hi` cross only edges of `R` (both ends in `R`).

* **Interlacing lemma.** Two walks in `R` whose ends interlace on the boundary share a vertex
  (primal–primal); an open path and a dual-open path with interlaced ends never coexist (mixed);
  two dual walks whose ends have interlaced boundary corners share a face (dual–dual). The
  primal–primal form is proved from the mixed one: if the walks were disjoint, the faces around
  the first walk would form a dual path crossing no edge of the second (a ring lemma for the
  edges of `R`), and quad duality forbids it. The dual–dual form uses the ring of vertices around
  a dual walk.
* **Pivotal edges carry four alternating arms.** If an edge is pivotal for the left-right
  crossing of `R`, then with the edge closed its ends are joined to the left and right sides,
  and with it open the two faces of its dual edge are joined by dual-open paths to the bottom and
  top of the dual box. This is box duality applied with the edge open and closed.
* **Order invariance of arms.** Let a box `I` lie inside the interior of a box `O`, and let
  pairwise vertex-disjoint walks in `O` (arms) run from `∂I` to `∂O`, each meeting `I` only at its
  first vertex. Then the cyclic order of their starts on `∂I` is the cyclic order of their ends on
  `∂O` (with orientation, not only up to reflection), and the same holds at their first hits of
  the boundary of any intermediate box. The orientation comes from the **left side of a path**:
  the faces on the left of consecutive steps of a path are joined around the common vertex
  without crossing the path. For three arms whose starts are counterclockwise, the cross-cut
  (second arm reversed, counterclockwise arc of `∂I` to the third start, third arm) has the
  inside of `I` on its left; its left side reaches the outer face just before its first end, and
  the ring of faces around the first arm joins `I` to the outside at the first end; mixed
  interlacing then puts the first end on the left. Arms that touch `∂O` before their end are
  reduced to their first hits of `∂O` by the primal–primal interlacing lemma.

## Main results

* `exists_mem_support_of_interlaced`: interlacing, primal–primal (any box, segments included).
* `dualConfig_inter_notMem_localConn_of_interlaced`: interlacing, mixed.
* `exists_mem_support_of_interlaced_dual`: interlacing, dual–dual.
* `exists_arms_of_pivotal`: a pivotal edge for a left-right crossing has open arms to the left and
  right sides and dual arms to the bottom and top.
* `exists_inter_mem_localConn_of_pivotal`: a pivotal edge for a crossing of a box of `ℤ^d` has
  arms to the two opposite sides.
* `mem_localConn_of_walk_of_mem_dualEdge`: the ring of faces around a walk, along edges of the
  box; `inter_mem_localConn_of_walk_of_mem_Icc`: the ring of vertices around a dual walk.
* `cyclicallyOrdered_end_iff`: three disjoint arms from `∂I` to `∂O` have their starts in
  counterclockwise order exactly when their ends are;
  `cyclicallyOrdered_end_iff_of_pairwise_disjoint` is the form for a family `Fin j` of arms.
* `cyclicallyOrdered_firstHit_iff`: the same for arms meeting `∂O` only at their last vertex, for
  instance arms stopped at their first hit of the boundary of an intermediate box.
* `not_cyclicallyOrdered_of_cyclicallyOrdered`: the core step for three arms.
* `cyclicallyOrdered_of_cyclicallyOrdered_of_disjoint`: a walk with both ends on the boundary
  does not cross a disjoint walk with both ends on the boundary (same side).
* `mem_localConn_of_isPath_left`: the faces on the left of the steps of a path are joined.
* `exists_walk_boundary`, `exists_walk_boundary_of_ne`: walks along the boundary of a box,
  counterclockwise, through exactly the positions in between.

## Implementation notes

* The interlacing hypotheses are written with explicit inequalities between positions: mathlib's
  cyclic betweenness `sbtw` on `ℤ` needs `LinearOrder.toCircularOrder`, which is not an instance.
  Each form allows both orientations of the first pair.
* The mixed and dual–dual forms, like quad duality, assume a box of positive width and height:
  their dual arcs are the faces outside the box at a boundary corner.
* Three positions `a, b, c` are in counterclockwise order when
  `(a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)` (mathlib's `sbtw a b c` for
  `LinearOrder.toCircularOrder ℤ`), written out so that `omega` reads it. The face on the left
  of a step `u → v` is the face of `{u, v}` with the corner `u + L(v - u)`, `L` the quarter turn
  counterclockwise, written `![u 0 + u 1 - v 1, u 1 + v 0 - u 0]`.
* Order invariance is stated for arms of one colour (walks of `ℤ²`). Comparing the
  interlacing of pairs at both ends, the route first planned, gives the cyclic order only up to
  reflection; the orientation needs the left side of a path. Arms of the dual lattice and mixed
  families reduce to this statement in the doubled lattice, once arm events fix the encoding of
  dual arms.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- **First hit of a set along a walk.** A walk ending in a set `S` splits as a walk to its first
vertex in `S` followed by the rest. -/
theorem exists_append_eq_of_mem {S : Set V} :
    ∀ {a b : V} (p : G.Walk a b), b ∈ S → ∃ c ∈ S, ∃ (π : G.Walk a c) (σ : G.Walk c b),
      π.append σ = p ∧ ∀ v ∈ π.support, v ∈ S → v = c
  | a, _, .nil, hb => ⟨a, hb, .nil, .nil, rfl, fun v hv _ => by
      rwa [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv⟩
  | a, b, .cons h p, hb => by
    by_cases ha : a ∈ S
    · exact ⟨a, ha, .nil, .cons h p, rfl, fun v hv _ => by
        rwa [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv⟩
    · obtain ⟨c, hc, π, σ, hπσ, hπ⟩ := exists_append_eq_of_mem p hb
      refine ⟨c, hc, .cons h π, σ, by rw [SimpleGraph.Walk.cons_append, hπσ], fun v hv hvS => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact absurd hvS ha
      · exact hπ v hv hvS

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Faces at a vertex, restricted to the edges of a box -/

/-- **Two perpendicular edges at a vertex share a face.** -/
theorem exists_mem_dualEdge_of_adj {v v₁ v₂ : LatticeSite 2} (h₁ : (zdGraph 2).Adj v v₁)
    (h₂ : (zdGraph 2).Adj v v₂) (hperp : v₁ 0 = v 0 ↔ v₂ 0 ≠ v 0) :
    ∃ h, h ∈ dualEdge s(v, v₁) ∧ h ∈ dualEdge s(v, v₂) := by
  rw [zdGraph_two_adj_iff] at h₁ h₂
  refine ⟨![min (min (v 0) (v₁ 0)) (v₂ 0), min (min (v 1) (v₁ 1)) (v₂ 1)], ?_, ?_⟩ <;>
  · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- Two faces of a closed edge of the box at a vertex untouched by `η` are joined (in one step or
none) by dual edges of closed edges of the box. -/
theorem mem_localConn_of_mem_dualEdge_of_notMem {lo hi : LatticeSite 2}
    {η : Config (LatticeSite 2)} {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    (heR : ∀ x ∈ e, x ∈ Icc lo hi) (heη : e ∉ η) {f g : LatticeSite 2} (hf : f ∈ dualEdge e)
    (hg : g ∈ dualEdge e) :
    dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
    induction e using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
  have hfT := mem_Icc_sub_one_of_mem_Icc (heR x hx) (mem_Icc_of_mem_dualEdge he hx hf)
  have hgT := mem_Icc_sub_one_of_mem_Icc (heR x hx) (mem_Icc_of_mem_dualEdge he hx hg)
  by_cases hfg : f = g
  · subst hfg
    rw [localConn_self hfT]
    exact mem_univ _
  · have hfge : dualEdge e = s(f, g) := (Sym2.mem_and_mem_iff hfg).1 ⟨hf, hg⟩
    refine mem_localConn_of_mem_localConn_of_mem (by rw [localConn_self hfT]; exact mem_univ _)
      hgT ⟨?_, e, ⟨he, heR⟩, hfge⟩
    rw [← hfge, dualEdge_mem_dualConfig_iff he]
    exact heη

/-- **Faces around a vertex.** If no edge of `η` touches the vertex `v` of a box of positive width
and height, any two faces of edges of the box at `v` are joined inside `Icc (lo - 1) hi` by dual
edges of closed edges of the box. -/
theorem mem_localConn_of_forall_notMem_of_mem_dualEdge {lo hi : LatticeSite 2}
    (h₁ : lo 1 < hi 1) (h₀ : lo 0 < hi 0) {η : Config (LatticeSite 2)} {v : LatticeSite 2}
    (hvR : v ∈ Icc lo hi) (hv : ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e) {v₁ v₂ f g : LatticeSite 2}
    (he₁ : s(v, v₁) ∈ (zdGraph 2).edgeSet) (hv₁ : v₁ ∈ Icc lo hi) (hf : f ∈ dualEdge s(v, v₁))
    (he₂ : s(v, v₂) ∈ (zdGraph 2).edgeSet) (hv₂ : v₂ ∈ Icc lo hi) (hg : g ∈ dualEdge s(v, v₂)) :
    dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g := by
  -- one closed edge of the box at `v`
  have hstep : ∀ w h h', s(v, w) ∈ (zdGraph 2).edgeSet → w ∈ Icc lo hi →
      h ∈ dualEdge s(v, w) → h' ∈ dualEdge s(v, w) →
      dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) h h' := by
    intro w h h' hw hwR hh hh'
    refine mem_localConn_of_mem_dualEdge_of_notMem hw (fun x hx => ?_) (fun hη => ?_) hh hh'
    · rcases Sym2.mem_iff.1 hx with rfl | rfl
      exacts [hvR, hwR]
    · exact hv _ ⟨hη, hw⟩ (Sym2.mem_mk_left _ _)
  -- through one perpendicular edge
  have hperp : ∀ w₁ w₂ h h', s(v, w₁) ∈ (zdGraph 2).edgeSet → w₁ ∈ Icc lo hi →
      s(v, w₂) ∈ (zdGraph 2).edgeSet → w₂ ∈ Icc lo hi → (w₁ 0 = v 0 ↔ w₂ 0 ≠ v 0) →
      h ∈ dualEdge s(v, w₁) → h' ∈ dualEdge s(v, w₂) →
      dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) h h' := by
    intro w₁ w₂ h h' hw₁ hw₁R hw₂ hw₂R hp hh hh'
    obtain ⟨k, hk₁, hk₂⟩ := exists_mem_dualEdge_of_adj hw₁ hw₂ hp
    exact localConn_trans (hstep w₁ h k hw₁ hw₁R hh hk₁) (hstep w₂ k h' hw₂ hw₂R hk₂ hh')
  by_cases hp : v₁ 0 = v 0 ↔ v₂ 0 ≠ v 0
  · exact hperp v₁ v₂ f g he₁ hv₁ he₂ hv₂ hp hf hg
  -- both edges horizontal or both vertical: go round through a perpendicular edge
  have hadj₁ := (zdGraph_two_adj_iff v v₁).1 he₁
  have hR := hvR
  rw [mem_Icc_two_iff] at hR
  obtain ⟨v₃, he₃, hv₃, hp₁, hp₂⟩ : ∃ v₃, s(v, v₃) ∈ (zdGraph 2).edgeSet ∧ v₃ ∈ Icc lo hi ∧
      (v₁ 0 = v 0 ↔ v₃ 0 ≠ v 0) ∧ (v₃ 0 = v 0 ↔ v₂ 0 ≠ v 0) := by
    by_cases hv₁0 : v₁ 0 = v 0
    · -- vertical edges: use a horizontal one
      have hv₂0 : v₂ 0 = v 0 := by tauto
      rcases (show v 0 < hi 0 ∨ lo 0 < v 0 by omega) with h | h
      · refine ⟨![v 0 + 1, v 1], ?_, ?_, ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
          simp
        · rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · simp only [Matrix.cons_val_zero]
          omega
        · simp only [Matrix.cons_val_zero]
          omega
      · refine ⟨![v 0 - 1, v 1], ?_, ?_, ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
          simp
        · rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · simp only [Matrix.cons_val_zero]
          omega
        · simp only [Matrix.cons_val_zero]
          omega
    · -- horizontal edges: use a vertical one
      have hv₂0 : v₂ 0 ≠ v 0 := by tauto
      rcases (show v 1 < hi 1 ∨ lo 1 < v 1 by omega) with h | h
      · refine ⟨![v 0, v 1 + 1], ?_, ?_, ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
          simp
        · rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · simp only [Matrix.cons_val_zero]
          omega
        · simp only [Matrix.cons_val_zero, true_iff]
          exact hv₂0
      · refine ⟨![v 0, v 1 - 1], ?_, ?_, ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
          simp
        · rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · simp only [Matrix.cons_val_zero]
          omega
        · simp only [Matrix.cons_val_zero, true_iff]
          exact hv₂0
  obtain ⟨k, -, hk₃⟩ := exists_mem_dualEdge_of_adj he₁ he₃ hp₁
  exact localConn_trans (hperp v₁ v₃ f k he₁ hv₁ he₃ hv₃ hp₁ hf hk₃)
    (hperp v₃ v₂ k g he₃ hv₃ he₂ hv₂ hp₂ hk₃ hg)

/-- **Ring lemma along the edges of a box.** Let `σ` be a walk in a box of positive width and
height such that no edge of `η` touches a vertex of `σ`. Then any two faces of edges of the box at
vertices of `σ` are joined inside `Icc (lo - 1) hi` by dual edges of closed edges of the box. -/
theorem mem_localConn_of_walk_of_mem_dualEdge {lo hi : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1) {η : Config (LatticeSite 2)} {u w : LatticeSite 2}
    (σ : (zdGraph 2).Walk u w) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hη : ∀ v ∈ σ.support, ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e) {a b a' b' f g : LatticeSite 2}
    (ha : a ∈ σ.support) (hb : b ∈ σ.support) (hea : s(a, a') ∈ (zdGraph 2).edgeSet)
    (ha' : a' ∈ Icc lo hi) (hf : f ∈ dualEdge s(a, a')) (heb : s(b, b') ∈ (zdGraph 2).edgeSet)
    (hb' : b' ∈ Icc lo hi) (hg : g ∈ dualEdge s(b, b')) :
    dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g := by
  induction σ generalizing a b a' b' f g with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha hb
    subst ha hb
    exact mem_localConn_of_forall_notMem_of_mem_dualEdge h₁ h₀ (hσ _ (by simp)) (hη _ (by simp))
      hea ha' hf heb hb' hg
  | @cons x y z hxy p ih =>
    have hσ' : ∀ v ∈ p.support, v ∈ Icc lo hi := fun v hv => hσ v (by simp [hv])
    have hη' : ∀ v ∈ p.support, ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e :=
      fun v hv => hη v (by simp [hv])
    have hxR := hσ x (by simp)
    have hyR := hσ' y (SimpleGraph.Walk.start_mem_support _)
    have hx := hη x (by simp)
    have hxy' : s(x, y) ∈ (zdGraph 2).edgeSet := hxy
    have hyx' : s(y, x) ∈ (zdGraph 2).edgeSet := hxy.symm
    obtain ⟨k, hk⟩ : ∃ k, k ∈ dualEdge s(x, y) :=
      ⟨_, by rw [dualEdge_mk]; exact Sym2.mem_mk_left _ _⟩
    have hk' : k ∈ dualEdge s(y, x) := by
      rw [Sym2.eq_swap]
      exact hk
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact mem_localConn_of_forall_notMem_of_mem_dualEdge h₁ h₀ hxR hx hea ha' hf heb hb' hg
    · exact localConn_trans
        (mem_localConn_of_forall_notMem_of_mem_dualEdge h₁ h₀ hxR hx hea ha' hf hxy' hyR hk)
        (ih hσ' hη' (SimpleGraph.Walk.start_mem_support _) hb hyx' hxR hk' heb hb' hg)
    · have := localConn_trans
        (mem_localConn_of_forall_notMem_of_mem_dualEdge h₁ h₀ hxR hx heb hb' hg hxy' hyR hk)
        (ih hσ' hη' (SimpleGraph.Walk.start_mem_support _) ha hyx' hxR hk' hea ha' hf)
      rwa [localConn_comm] at this
    · exact ih hσ' hη' ha hb hea ha' hf heb hb' hg

/-- **The outer face of a boundary edge at a boundary point.** Every point of the boundary of a
box of positive width and height is an end of an edge of the box with a face outside the box. -/
theorem exists_notMem_Icc_mem_dualEdge_of_mem_boxBoundary {lo hi : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {a : LatticeSite 2} (ha : a ∈ boxBoundary lo hi) :
    ∃ a' f, s(a, a') ∈ (zdGraph 2).edgeSet ∧ a' ∈ Icc lo hi ∧ f ∉ Icc lo (hi - 1) ∧
      f ∈ dualEdge s(a, a') := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  obtain ⟨v, w, f, hv, hpv, hw, hpw, hf, hvf, hwf, -⟩ :=
    exists_notMem_Icc_of_perimeterPos h₀ h₁ (perimeterPos_nonneg ha.1) (perimeterPos_lt hne ha.1)
  have hva : v = a := perimeterPos_injOn lo hi hv ha hpv
  subst hva
  have hvw : v ≠ w := fun h => by
    rw [← h] at hpw
    omega
  obtain ⟨hE, hfE⟩ := mem_edgeSet_and_mem_dualEdge_of_notMem_Icc hv.1 hw.1 hvw hf hvf hwf
  exact ⟨w, f, hE, hw.1, hf, hfE⟩

/-! ### Interlacing -/

/-- **Interlacing, mixed form.** In a box of positive width and height, let `a` and `b` be
boundary points joined by an open path inside the box, and `f`, `g` faces outside the box with
boundary corners `x`, `y`. If `x` and `y` separate `a` from `b` on the boundary (their positions
interlace), then no dual-open path in the dual box `Icc (lo - 1) hi` crossing only edges of the
box joins `f` to `g`. -/
theorem dualConfig_inter_notMem_localConn_of_interlaced {lo hi : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {ω : Config (LatticeSite 2)}
    {a b x y f g : LatticeSite 2} (hab : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a b)
    (ha : a ∈ boxBoundary lo hi) (hb : b ∈ boxBoundary lo hi) (hf : f ∉ Icc lo (hi - 1))
    (hx : x ∈ boxBoundary lo hi) (hxf : x ∈ Icc f (f + 1)) (hg : g ∉ Icc lo (hi - 1))
    (hy : y ∈ boxBoundary lo hi) (hyg : y ∈ Icc g (g + 1))
    (hint : (perimeterPos lo hi a < perimeterPos lo hi x ∧
        perimeterPos lo hi x < perimeterPos lo hi b ∧
        (perimeterPos lo hi y < perimeterPos lo hi a ∨
          perimeterPos lo hi b < perimeterPos lo hi y)) ∨
      (perimeterPos lo hi b < perimeterPos lo hi x ∧
        perimeterPos lo hi x < perimeterPos lo hi a ∧
        (perimeterPos lo hi y < perimeterPos lo hi b ∨
          perimeterPos lo hi a < perimeterPos lo hi y))) :
    dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∉
      localConn (Icc (lo - 1) hi) f g := by
  intro hfg
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  set P := 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) with hP
  have pa := perimeterPos_lt hne ha.1
  have pb := perimeterPos_lt hne hb.1
  have px := perimeterPos_lt hne hx.1
  have py := perimeterPos_lt hne hy.1
  have pa' := perimeterPos_nonneg ha.1
  have pb' := perimeterPos_nonneg hb.1
  have px' := perimeterPos_nonneg hx.1
  have py' := perimeterPos_nonneg hy.1
  have hba : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) b a := by
    rwa [localConn_comm] at hab
  rcases hint with ⟨h₂, h₃, h₄ | h₄⟩ | ⟨h₂, h₃, h₄ | h₄⟩
  · exact not_exists_dualConfig_inter_mem_localConn_of_exists h₀ h₁
      (a := perimeterPos lo hi a) (c := perimeterPos lo hi x) (b := perimeterPos lo hi b)
      (d := perimeterPos lo hi y + P) ⟨by omega, by omega, by omega, by omega⟩
      ⟨a, b, ha, ⟨0, by rw [zero_mul, add_zero]; exact ⟨le_rfl, by omega⟩⟩, hb,
        ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩, hab⟩
      ⟨f, g, ⟨hf, x, hx, hxf, ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩⟩,
        ⟨hg, y, hy, hyg, ⟨1, by rw [one_mul]; exact ⟨by omega, by omega⟩⟩⟩, hfg⟩
  · exact not_exists_dualConfig_inter_mem_localConn_of_exists h₀ h₁
      (a := perimeterPos lo hi a) (c := perimeterPos lo hi x) (b := perimeterPos lo hi b)
      (d := perimeterPos lo hi y) ⟨by omega, by omega, by omega, by omega⟩
      ⟨a, b, ha, ⟨0, by rw [zero_mul, add_zero]; exact ⟨le_rfl, by omega⟩⟩, hb,
        ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩, hab⟩
      ⟨f, g, ⟨hf, x, hx, hxf, ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩⟩,
        ⟨hg, y, hy, hyg, ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩⟩, hfg⟩
  · exact not_exists_dualConfig_inter_mem_localConn_of_exists h₀ h₁
      (a := perimeterPos lo hi b) (c := perimeterPos lo hi x) (b := perimeterPos lo hi a)
      (d := perimeterPos lo hi y + P) ⟨by omega, by omega, by omega, by omega⟩
      ⟨b, a, hb, ⟨0, by rw [zero_mul, add_zero]; exact ⟨le_rfl, by omega⟩⟩, ha,
        ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩, hba⟩
      ⟨f, g, ⟨hf, x, hx, hxf, ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩⟩,
        ⟨hg, y, hy, hyg, ⟨1, by rw [one_mul]; exact ⟨by omega, by omega⟩⟩⟩, hfg⟩
  · exact not_exists_dualConfig_inter_mem_localConn_of_exists h₀ h₁
      (a := perimeterPos lo hi b) (c := perimeterPos lo hi x) (b := perimeterPos lo hi a)
      (d := perimeterPos lo hi y) ⟨by omega, by omega, by omega, by omega⟩
      ⟨b, a, hb, ⟨0, by rw [zero_mul, add_zero]; exact ⟨le_rfl, by omega⟩⟩, ha,
        ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩, hba⟩
      ⟨f, g, ⟨hf, x, hx, hxf, ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩⟩,
        ⟨hg, y, hy, hyg, ⟨0, by rw [zero_mul, add_zero]; exact ⟨by omega, by omega⟩⟩⟩, hfg⟩

/-- **Interlacing lemma** (primal–primal form) in a box of positive width and height: two walks
in the box whose ends lie on the boundary at interlaced positions share a vertex. -/
theorem exists_mem_support_of_interlaced_of_lt {lo hi : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1) {a b u w : LatticeSite 2} (p : (zdGraph 2).Walk a b)
    (q : (zdGraph 2).Walk u w) (hp : ∀ v ∈ p.support, v ∈ Icc lo hi)
    (hq : ∀ v ∈ q.support, v ∈ Icc lo hi) (ha : a ∈ boxBoundary lo hi)
    (hb : b ∈ boxBoundary lo hi) (hu : u ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (hint : (perimeterPos lo hi a < perimeterPos lo hi u ∧
        perimeterPos lo hi u < perimeterPos lo hi b ∧
        (perimeterPos lo hi w < perimeterPos lo hi a ∨
          perimeterPos lo hi b < perimeterPos lo hi w)) ∨
      (perimeterPos lo hi b < perimeterPos lo hi u ∧
        perimeterPos lo hi u < perimeterPos lo hi a ∧
        (perimeterPos lo hi w < perimeterPos lo hi b ∨
          perimeterPos lo hi a < perimeterPos lo hi w))) :
    ∃ v ∈ p.support, v ∈ q.support := by
  by_contra hdis
  push Not at hdis
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  -- the edges of `q` are open; no edge of `q` touches `p`
  have hopen : {e | e ∈ q.edges} ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u w :=
    mem_localConn_edges_of_walk q hq
  have hfree : ∀ v ∈ p.support, ∀ e ∈ {e | e ∈ q.edges} ∩ (zdGraph 2).edgeSet, v ∉ e :=
    fun v hv e he hve => hdis v hv (mem_support_of_mem_edge q he.1 hve)
  -- the ring of faces around `p`, between outer faces at `a` and at `b`
  obtain ⟨a', fa, hea, ha', hfa, hfae⟩ := exists_notMem_Icc_mem_dualEdge_of_mem_boxBoundary h₀ h₁ ha
  obtain ⟨b', fb, heb, hb', hfb, hfbe⟩ := exists_notMem_Icc_mem_dualEdge_of_mem_boxBoundary h₀ h₁ hb
  have hring := mem_localConn_of_walk_of_mem_dualEdge h₀ h₁ p hp hfree
    (SimpleGraph.Walk.start_mem_support _) (SimpleGraph.Walk.end_mem_support _) hea ha' hfae heb
    hb' hfbe
  have hring' := hring
  rw [localConn_comm] at hring'
  have hafa := mem_Icc_of_mem_dualEdge hea (Sym2.mem_mk_left _ _) hfae
  have hbfb := mem_Icc_of_mem_dualEdge heb (Sym2.mem_mk_left _ _) hfbe
  have pa := perimeterPos_lt hne ha.1
  have pb := perimeterPos_lt hne hb.1
  have pu := perimeterPos_lt hne hu.1
  have pw := perimeterPos_lt hne hw.1
  have pa' := perimeterPos_nonneg ha.1
  have pb' := perimeterPos_nonneg hb.1
  have pu' := perimeterPos_nonneg hu.1
  have pw' := perimeterPos_nonneg hw.1
  -- the positions of `a`, `b` interlace with those of `u`, `w`
  rcases hint with ⟨h₂, h₃, h₄ | h₄⟩ | ⟨h₂, h₃, h₄ | h₄⟩
  · exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hopen hu hw hfa ha hafa hfb hb
      hbfb (Or.inr ⟨by omega, by omega, by omega⟩) hring
  · exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hopen hu hw hfb hb hbfb hfa ha
      hafa (Or.inl ⟨by omega, by omega, by omega⟩) hring'
  · exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hopen hu hw hfb hb hbfb hfa ha
      hafa (Or.inr ⟨by omega, by omega, by omega⟩) hring'
  · exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hopen hu hw hfa ha hafa hfb hb
      hbfb (Or.inl ⟨by omega, by omega, by omega⟩) hring

/-- **Interlacing lemma** (primal–primal form). Two walks in a box of `ℤ²` whose ends lie on the
boundary at interlaced positions (the ends `u`, `w` of the second walk separate the ends `a`, `b`
of the first on the boundary: one strictly between them, the other strictly outside) share a
vertex. On a segment the positions are a coordinate and the intermediate value theorem along
walks applies. -/
theorem exists_mem_support_of_interlaced {lo hi : LatticeSite 2} {a b u w : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (q : (zdGraph 2).Walk u w) (hp : ∀ v ∈ p.support, v ∈ Icc lo hi)
    (hq : ∀ v ∈ q.support, v ∈ Icc lo hi) (ha : a ∈ boxBoundary lo hi)
    (hb : b ∈ boxBoundary lo hi) (hu : u ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (hint : (perimeterPos lo hi a < perimeterPos lo hi u ∧
        perimeterPos lo hi u < perimeterPos lo hi b ∧
        (perimeterPos lo hi w < perimeterPos lo hi a ∨
          perimeterPos lo hi b < perimeterPos lo hi w)) ∨
      (perimeterPos lo hi b < perimeterPos lo hi u ∧
        perimeterPos lo hi u < perimeterPos lo hi a ∧
        (perimeterPos lo hi w < perimeterPos lo hi b ∨
          perimeterPos lo hi a < perimeterPos lo hi w))) :
    ∃ v ∈ p.support, v ∈ q.support := by
  by_cases hlt : lo 0 < hi 0 ∧ lo 1 < hi 1
  · exact exists_mem_support_of_interlaced_of_lt hlt.1 hlt.2 p q hp hq ha hb hu hw hint
  -- on a segment, the intermediate value theorem for a coordinate `F` that determines the point
  have key : ∀ F : LatticeSite 2 → ℤ, (∀ v w, (zdGraph 2).Adj v w → F w ≤ F v + 1) →
      (∀ v ∈ Icc lo hi, ∀ w ∈ Icc lo hi, F v = F w → v = w) →
      ((F a < F u ∧ F u < F b) ∨ (F b < F u ∧ F u < F a)) → ∃ v ∈ p.support, v ∈ q.support := by
    intro F hF hinj h
    rcases h with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · obtain ⟨c, hc, r, hr⟩ := SimpleGraph.Walk.exists_walk_eq_of_le F hF p h₂.le h₃.le
      have hcp := (hr c (SimpleGraph.Walk.end_mem_support _)).1
      refine ⟨c, hcp, ?_⟩
      rw [hinj c (hp c hcp) u hu.1 hc]
      exact SimpleGraph.Walk.start_mem_support _
    · obtain ⟨c, hc, r, hr⟩ := SimpleGraph.Walk.exists_walk_eq_of_le F hF p.reverse h₂.le h₃.le
      have hcp := (hr c (SimpleGraph.Walk.end_mem_support _)).1
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hcp
      refine ⟨c, hcp, ?_⟩
      rw [hinj c (hp c hcp) u hu.1 hc]
      exact SimpleGraph.Walk.start_mem_support _
  have hR := ha.1
  rw [mem_Icc_two_iff] at hR
  have hadj : ∀ i : Fin 2, ∀ v w, (zdGraph 2).Adj v w → w i ≤ v i + 1 := by
    intro i v w h
    rw [zdGraph_two_adj_iff] at h
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> omega
  have hpa := ha.1
  have hpb := hb.1
  have hpu := hu.1
  have hpw := hw.1
  rw [mem_Icc_two_iff] at hpa hpb hpu hpw
  rcases (show lo 1 = hi 1 ∨ (lo 0 = hi 0 ∧ lo 1 < hi 1) by omega) with h | ⟨h, -⟩
  · -- a horizontal segment: the position is the first coordinate
    have hpos : ∀ v ∈ Icc lo hi, perimeterPos lo hi v = v 0 - lo 0 := fun v hv => by
      rw [mem_Icc_two_iff] at hv
      exact perimeterPos_of_bottom (by omega)
    refine key (fun v => v 0) (hadj 0) (fun v hv w hw hvw => ?_) ?_
    · rw [mem_Icc_two_iff] at hv hw
      exact funext (Fin.forall_fin_two.2 ⟨hvw, by omega⟩)
    · rw [hpos a ha.1, hpos b hb.1, hpos u hu.1, hpos w hw.1] at hint
      omega
  · -- a vertical segment: the position is the second coordinate
    have hpos : ∀ v ∈ Icc lo hi, perimeterPos lo hi v = v 1 - lo 1 := fun v hv => by
      rw [mem_Icc_two_iff] at hv
      unfold perimeterPos
      split_ifs <;> omega
    refine key (fun v => v 1) (hadj 1) (fun v hv w hw hvw => ?_) ?_
    · rw [mem_Icc_two_iff] at hv hw
      exact funext (Fin.forall_fin_two.2 ⟨by omega, hvw⟩)
    · rw [hpos a ha.1, hpos b hb.1, hpos u hu.1, hpos w hw.1] at hint
      omega

/-! ### The ring of vertices around a dual walk -/

/-- Two adjacent corners of a face span an edge whose dual edge has that face as an end. -/
theorem mem_dualEdge_of_adj_of_mem_Icc {x z h : LatticeSite 2} (hxz : (zdGraph 2).Adj x z)
    (hx : x ∈ Icc h (h + 1)) (hz : z ∈ Icc h (h + 1)) : h ∈ dualEdge s(x, z) := by
  rw [zdGraph_two_adj_iff] at hxz
  rw [mem_Icc_two_iff] at hx hz
  simp only [Pi.add_apply, Pi.one_apply] at hx hz
  rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
  omega

/-- **The corners of a face.** If every edge of the box having the face `h` as a face is open,
any two corners of `h` in the box are joined inside the box. -/
theorem inter_mem_localConn_of_mem_Icc {lo hi : LatticeSite 2} {ω : Config (LatticeSite 2)}
    {h : LatticeSite 2}
    (hω : ∀ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) → h ∈ dualEdge e → e ∈ ω)
    {x z : LatticeSite 2} (hxR : x ∈ Icc lo hi) (hzR : z ∈ Icc lo hi) (hx : x ∈ Icc h (h + 1))
    (hz : z ∈ Icc h (h + 1)) : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x z := by
  -- one step between corners that differ in one coordinate
  have hone : ∀ x z, x ∈ Icc lo hi → z ∈ Icc lo hi → x ∈ Icc h (h + 1) → z ∈ Icc h (h + 1) →
      (x 0 = z 0 ∨ x 1 = z 1) → ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x z := by
    intro x z hxR hzR hx hz hxz
    by_cases he : x = z
    · subst he
      rw [localConn_self hxR]
      exact mem_univ _
    · have hadj : (zdGraph 2).Adj x z := by
        have hne : x 0 ≠ z 0 ∨ x 1 ≠ z 1 := by
          by_contra hc
          push Not at hc
          exact he (funext (Fin.forall_fin_two.2 hc))
        rw [zdGraph_two_adj_iff]
        rw [mem_Icc_two_iff] at hx hz
        simp only [Pi.add_apply, Pi.one_apply] at hx hz
        omega
      refine mem_localConn_of_mem_localConn_of_mem (by rw [localConn_self hxR]; exact mem_univ _)
        hzR ⟨hω _ hadj (fun v hv => ?_) (mem_dualEdge_of_adj_of_mem_Icc hadj hx hz), hadj⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      exacts [hxR, hzR]
  -- through the corner `(x₀, z₁)`
  have hmR : (![x 0, z 1] : LatticeSite 2) ∈ Icc lo hi := by
    rw [mem_Icc_two_iff] at hxR hzR ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hm : (![x 0, z 1] : LatticeSite 2) ∈ Icc h (h + 1) := by
    rw [mem_Icc_two_iff] at hx hz ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply] at hx hz ⊢
    omega
  exact localConn_trans (hone x _ hxR hmR hx hm (Or.inl (by simp)))
    (hone _ z hmR hzR hm hz (Or.inr (by simp)))

/-- **The ring of vertices around a dual walk.** Let `σ` be a walk of faces whose steps are dual
edges of edges of the box, and suppose every edge of the box having a face of `σ` as a face is
open in `ω`. Then any two points of the box that are corners of faces of `σ` are joined inside
the box. -/
theorem inter_mem_localConn_of_walk_of_mem_Icc {lo hi : LatticeSite 2}
    {D ω : Config (LatticeSite 2)}
    (hD : ∀ E ∈ D, ∃ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) ∧ dualEdge e = E)
    {f g : LatticeSite 2} (σ : (openGraph D).Walk f g)
    (hω : ∀ h ∈ σ.support, ∀ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) →
      h ∈ dualEdge e → e ∈ ω)
    {h h' x z : LatticeSite 2} (hh : h ∈ σ.support) (hh' : h' ∈ σ.support)
    (hxR : x ∈ Icc lo hi) (hzR : z ∈ Icc lo hi) (hx : x ∈ Icc h (h + 1))
    (hz : z ∈ Icc h' (h' + 1)) : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x z := by
  induction σ generalizing h h' x z with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hh hh'
    subst hh hh'
    exact inter_mem_localConn_of_mem_Icc (hω _ (by simp)) hxR hzR hx hz
  | @cons k₀ k₁ k₂ hadj p ih =>
    have hω' : ∀ h ∈ p.support, ∀ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) →
        h ∈ dualEdge e → e ∈ ω := fun h hh => hω h (by simp [hh])
    obtain ⟨e, he, heR, hee⟩ := hD _ ((openGraph_adj_iff _ _ _).1 hadj).1
    obtain ⟨c, hc⟩ : ∃ c, c ∈ e := by
      induction e using Sym2.ind with
      | h a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
    have hc₀ : c ∈ Icc k₀ (k₀ + 1) :=
      mem_Icc_of_mem_dualEdge he hc (by rw [hee]; exact Sym2.mem_mk_left _ _)
    have hc₁ : c ∈ Icc k₁ (k₁ + 1) :=
      mem_Icc_of_mem_dualEdge he hc (by rw [hee]; exact Sym2.mem_mk_right _ _)
    have hcR := heR c hc
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hh hh'
    rcases hh with rfl | hh <;> rcases hh' with rfl | hh'
    · exact inter_mem_localConn_of_mem_Icc (hω _ (by simp)) hxR hzR hx hz
    · exact localConn_trans (inter_mem_localConn_of_mem_Icc (hω _ (by simp)) hxR hcR hx hc₀)
        (ih hω' (SimpleGraph.Walk.start_mem_support _) hh' hcR hzR hc₁ hz)
    · have := localConn_trans (inter_mem_localConn_of_mem_Icc (hω _ (by simp)) hzR hcR hz hc₀)
        (ih hω' (SimpleGraph.Walk.start_mem_support _) hh hcR hxR hc₁ hx)
      rwa [localConn_comm] at this
    · exact ih hω' hh hh' hxR hzR hx hz

/-- **Interlacing lemma** (dual–dual form). In a box of positive width and height, let `σ` and
`τ` be walks of faces whose steps are dual edges of edges of the box, `τ` inside
`Icc (lo - 1) hi` and between faces outside the box. If boundary corners `x`, `y` of the ends of
`σ` and boundary corners `x'`, `y'` of the ends of `τ` have interlaced positions, then `σ` and `τ`
share a face. -/
theorem exists_mem_support_of_interlaced_dual {lo hi : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1) {D D' : Config (LatticeSite 2)}
    (hD : ∀ E ∈ D, ∃ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) ∧ dualEdge e = E)
    (hD' : ∀ E ∈ D', ∃ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) ∧ dualEdge e = E)
    {f g f' g' x y x' y' : LatticeSite 2} (σ : (openGraph D).Walk f g)
    (τ : (openGraph D').Walk f' g') (hτ : ∀ h ∈ τ.support, h ∈ Icc (lo - 1) hi)
    (hx : x ∈ boxBoundary lo hi) (hxf : x ∈ Icc f (f + 1)) (hy : y ∈ boxBoundary lo hi)
    (hyg : y ∈ Icc g (g + 1)) (hf' : f' ∉ Icc lo (hi - 1)) (hx' : x' ∈ boxBoundary lo hi)
    (hx'f : x' ∈ Icc f' (f' + 1)) (hg' : g' ∉ Icc lo (hi - 1)) (hy' : y' ∈ boxBoundary lo hi)
    (hy'g : y' ∈ Icc g' (g' + 1))
    (hint : (perimeterPos lo hi x < perimeterPos lo hi x' ∧
        perimeterPos lo hi x' < perimeterPos lo hi y ∧
        (perimeterPos lo hi y' < perimeterPos lo hi x ∨
          perimeterPos lo hi y < perimeterPos lo hi y')) ∨
      (perimeterPos lo hi y < perimeterPos lo hi x' ∧
        perimeterPos lo hi x' < perimeterPos lo hi x ∧
        (perimeterPos lo hi y' < perimeterPos lo hi y ∨
          perimeterPos lo hi x < perimeterPos lo hi y'))) :
    ∃ h ∈ σ.support, h ∈ τ.support := by
  by_contra hdis
  push Not at hdis
  -- the edges not crossed by `τ`
  set ω : Config (LatticeSite 2) := {e | ∀ δ ∈ τ.darts, s(δ.fst, δ.snd) ≠ dualEdge e} with hω
  -- `τ` is a dual-open path for `ω`
  have hτω : dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f' g' := by
    refine mem_localConn_iff_exists_walk.2 ⟨τ.transfer _ fun E hE => ?_, fun h hh => hτ h (by
      rwa [SimpleGraph.Walk.support_transfer] at hh)⟩
    have hE' := τ.edges_subset_edgeSet hE
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at hE' ⊢
    obtain ⟨hED', hEd⟩ := hE'
    obtain ⟨e, he, heR, hee⟩ := hD' E hED'
    refine ⟨⟨?_, e, ⟨he, heR⟩, hee⟩, hEd⟩
    rw [← hee, dualEdge_mem_dualConfig_iff he]
    intro heω
    obtain ⟨δ, hδ, hδE⟩ := List.mem_map.1 hE
    exact heω δ hδ (by rw [hee]; exact hδE)
  -- every edge with a face of `σ` as a face is open for `ω`
  have hωσ : ∀ h ∈ σ.support, ∀ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) →
      h ∈ dualEdge e → e ∈ ω := by
    intro h hh e he heR hhe δ hδ hδe
    rw [← hδe] at hhe
    rcases Sym2.mem_iff.1 hhe with rfl | rfl
    · exact hdis _ hh (τ.dart_fst_mem_support_of_mem_darts hδ)
    · exact hdis _ hh (τ.dart_snd_mem_support_of_mem_darts hδ)
  have hxy := inter_mem_localConn_of_walk_of_mem_Icc hD σ hωσ
    (SimpleGraph.Walk.start_mem_support _) (SimpleGraph.Walk.end_mem_support _) hx.1 hy.1 hxf hyg
  exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxy hx hy hf' hx' hx'f hg' hy' hy'g
    hint hτω

/-! ### Pivotal edges carry four alternating arms -/

/-- **Arms of a pivotal edge to two opposite sides.** If the edge `{x, y}` of `ℤ^d` is pivotal for
the crossing of a box in direction `i` (the crossing occurs with the edge open and fails with it
closed), then both ends lie in the box, and with the edge closed one end is joined inside the box
to the side `{v i = lo i}` and the other to the side `{v i = hi i}`. -/
theorem exists_inter_mem_localConn_of_pivotal {d : ℕ} {i : Fin d} {lo hi x y : LatticeSite d}
    {ω : Config (LatticeSite d)} (hxy : s(x, y) ∈ (zdGraph d).edgeSet)
    (hpiv : insert s(x, y) ω ∈ crossing i lo hi ∧ ω \ {s(x, y)} ∉ crossing i lo hi) :
    x ∈ Icc lo hi ∧ y ∈ Icc lo hi ∧ ∃ a ∈ Icc lo hi, a i = lo i ∧ ∃ b ∈ Icc lo hi, b i = hi i ∧
      (((ω \ {s(x, y)}) ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a x ∧
          (ω \ {s(x, y)}) ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) y b) ∨
        ((ω \ {s(x, y)}) ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a y ∧
          (ω \ {s(x, y)}) ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) x b)) := by
  obtain ⟨⟨a, haR, ha, b, hbR, hb, hab⟩, hnot⟩ := hpiv
  have hins : insert s(x, y) ω ∩ (zdGraph d).edgeSet =
      insert s(x, y) (ω ∩ (zdGraph d).edgeSet) := insert_inter_of_mem hxy
  have hdel : (ω \ {s(x, y)}) ∩ (zdGraph d).edgeSet =
      (ω ∩ (zdGraph d).edgeSet) \ {s(x, y)} := inter_sdiff_right_comm.symm
  rw [hins] at hab
  have hnot' : (ω ∩ (zdGraph d).edgeSet) \ {s(x, y)} ∉ localConn (Icc lo hi) a b := fun h =>
    hnot ⟨a, haR, ha, b, hbR, hb, by rw [hdel]; exact h⟩
  obtain ⟨ha', hb', hreach⟩ := hab
  -- the edge lies in the box
  have hint : ∀ v ∈ s(x, y), v ∈ Icc lo hi := by
    by_contra hc
    exact not_pivotal_localConn_of_not_internal (ω ∩ (zdGraph d).edgeSet) (Icc lo hi)
      ⟨a, haR⟩ ⟨b, hbR⟩ hc ⟨hreach, fun h => hnot' ⟨haR, hbR, h⟩⟩
  have hx := hint x (Sym2.mem_mk_left _ _)
  have hy := hint y (Sym2.mem_mk_right _ _)
  have hne : (⟨x, hx⟩ : Icc lo hi) ≠ ⟨y, hy⟩ := fun h =>
    ((SimpleGraph.mem_edgeSet _).1 hxy).ne (congrArg Subtype.val h)
  obtain ⟨-, h | h⟩ := (pivotal_localConn_iff (ω ∩ (zdGraph d).edgeSet) (Icc lo hi) ⟨a, haR⟩
    ⟨b, hbR⟩ ⟨x, hx⟩ ⟨y, hy⟩ hne).1 ⟨hreach, fun h => hnot' ⟨haR, hbR, h⟩⟩
  · refine ⟨hx, hy, a, haR, ha, b, hbR, hb, Or.inl ⟨?_, ?_⟩⟩ <;> rw [hdel]
    · exact ⟨haR, hx, h.1⟩
    · exact ⟨hy, hbR, h.2.symm⟩
  · refine ⟨hx, hy, a, haR, ha, b, hbR, hb, Or.inr ⟨?_, ?_⟩⟩ <;> rw [hdel]
    · exact ⟨haR, hy, h.1⟩
    · exact ⟨hx, hbR, h.2.symm⟩

/-- The dual configurations of a configuration with one edge closed and with it open differ by
the dual of that edge. -/
theorem dualConfig_sdiff_singleton_dualEdge {ω : Config (LatticeSite 2)}
    {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    dualConfig (ω \ {e}) \ {dualEdge e} = dualConfig (insert e ω) := by
  ext E
  simp only [mem_sdiff, mem_singleton_iff, mem_dualConfig_iff', mem_insert_iff, not_or,
    not_and, not_not]
  constructor
  · rintro ⟨⟨e', he', hω, rfl⟩, hne⟩
    refine ⟨e', he', ⟨fun h => hne (by rw [h]), fun h => ?_⟩, rfl⟩
    exact hne (by rw [hω h])
  · rintro ⟨e', he', ⟨hne, hω⟩, rfl⟩
    refine ⟨⟨e', he', fun h => absurd h hω, rfl⟩, fun h => hne (dualEdge_injOn he' he h)⟩

/-- **Pivotal edges carry four alternating arms** (box duality). If the edge `{x, y}` of `ℤ²` is
pivotal for the left-right crossing of the box `R = Icc lo hi`, then, with the edge closed, one
end is joined inside `R` to the left side and the other to the right side; and the two faces `f`,
`g` of its dual edge lie in the dual box `R* = [lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]`, one joined to its
bottom row and the other to its top row by dual-open paths of the configuration with the edge
open. -/
theorem exists_arms_of_pivotal {lo hi x y : LatticeSite 2} {ω : Config (LatticeSite 2)}
    (hxy : s(x, y) ∈ (zdGraph 2).edgeSet)
    (hpiv : insert s(x, y) ω ∈ crossing 0 lo hi ∧ ω \ {s(x, y)} ∉ crossing 0 lo hi) :
    (∃ a ∈ Icc lo hi, a 0 = lo 0 ∧ ∃ b ∈ Icc lo hi, b 0 = hi 0 ∧
      (((ω \ {s(x, y)}) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a x ∧
          (ω \ {s(x, y)}) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) y b) ∨
        ((ω \ {s(x, y)}) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a y ∧
          (ω \ {s(x, y)}) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x b))) ∧
    ∃ f g, dualEdge s(x, y) = s(f, g) ∧
      ∃ c ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1], c 1 = lo 1 - 1 ∧
      ∃ d ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1], d 1 = hi 1 ∧
      ((dualConfig (insert s(x, y) ω) ∩ (zdGraph 2).edgeSet ∈
            localConn (Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1]) c f ∧
          dualConfig (insert s(x, y) ω) ∩ (zdGraph 2).edgeSet ∈
            localConn (Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1]) g d) ∨
        (dualConfig (insert s(x, y) ω) ∩ (zdGraph 2).edgeSet ∈
            localConn (Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1]) c g ∧
          dualConfig (insert s(x, y) ω) ∩ (zdGraph 2).edgeSet ∈
            localConn (Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1]) f d)) := by
  obtain ⟨hx, -, harms⟩ := exists_inter_mem_localConn_of_pivotal hxy hpiv
  refine ⟨harms, ?_⟩
  have hle : lo ≤ hi := (mem_Icc.1 hx).1.trans (mem_Icc.1 hx).2
  -- the dual edge is pivotal for the bottom-top dual crossing of the dual box
  obtain ⟨f, g, hfg⟩ : ∃ f g, dualEdge s(x, y) = s(f, g) := by
    induction h : dualEdge s(x, y) using Sym2.ind with
    | h f g => exact ⟨f, g, rfl⟩
  have hmem : dualEdge s(x, y) ∈ dualConfig (ω \ {s(x, y)}) :=
    (dualEdge_mem_dualConfig_iff hxy).2 fun h => h.2 rfl
  have h₁ : insert s(f, g) (dualConfig (ω \ {s(x, y)})) ∈
      crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] := by
    rw [← hfg, insert_eq_of_mem hmem]
    exact mem_crossing_one_dualConfig_of_notMem_crossing_zero hle hpiv.2
  have h₂ : dualConfig (ω \ {s(x, y)}) \ {s(f, g)} ∉
      crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] := by
    rw [← hfg, dualConfig_sdiff_singleton_dualEdge hxy]
    exact notMem_crossing_one_dualConfig_of_mem_crossing_zero hpiv.1
  obtain ⟨-, -, c, hc, hc1, d, hd, hd1, h⟩ := exists_inter_mem_localConn_of_pivotal
    (by rw [← hfg]; exact dualEdge_mem_edgeSet hxy) ⟨h₁, h₂⟩
  rw [← hfg, dualConfig_sdiff_singleton_dualEdge hxy] at h
  exact ⟨f, g, hfg, c, hc, by simpa using hc1, d, hd, by simpa using hd1, h⟩

/-! ### Faces on the left of a path -/

/-- The face on the left of a step `u → v` (the face of `{u, v}` having the corner
`u + L(v - u)`, `L` the counterclockwise quarter turn) is unique. -/
theorem eq_of_mem_dualEdge_of_mem_Icc_left {u v f g : LatticeSite 2}
    (hf : f ∈ dualEdge s(u, v))
    (hf' : ![u 0 + u 1 - v 1, u 1 + v 0 - u 0] ∈ Icc f (f + 1)) (hg : g ∈ dualEdge s(u, v))
    (hg' : ![u 0 + u 1 - v 1, u 1 + v 0 - u 0] ∈ Icc g (g + 1)) : f = g := by
  rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hf hg
  rw [mem_Icc_two_iff] at hf' hg'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply] at hf hg hf' hg'
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> omega

/-- Every step `u → v` has a face on its left. -/
theorem exists_mem_dualEdge_left {u v : LatticeSite 2} (huv : (zdGraph 2).Adj u v) :
    ∃ f, f ∈ dualEdge s(u, v) ∧ ![u 0 + u 1 - v 1, u 1 + v 0 - u 0] ∈ Icc f (f + 1) := by
  rw [zdGraph_two_adj_iff] at huv
  rcases huv with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
  · refine ⟨![u 0 - 1, u 1], ?_, ?_⟩
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply]
      omega
  · refine ⟨![u 0, v 1], ?_, ?_⟩
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply]
      omega
  · refine ⟨![u 0, u 1], ?_, ?_⟩
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply]
      omega
  · refine ⟨![v 0, u 1 - 1], ?_, ?_⟩
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply]
      omega

/-- **Left faces at a vertex.** Let `u → v → w` be two steps with `w ≠ u`, at a vertex `v` of
the interior of the box `Icc lo hi`, and suppose the only edges of `η` at `v` are the two steps.
Then the faces on the left of the two steps are joined, around `v` on the left, by dual edges of
closed edges of the box. -/
theorem mem_localConn_of_mem_dualEdge_left {lo hi : LatticeSite 2} {η : Config (LatticeSite 2)}
    {u v w f g : LatticeSite 2} (huv : (zdGraph 2).Adj u v) (hvw : (zdGraph 2).Adj v w)
    (huw : u ≠ w) (hv : v ∈ Icc (lo + 1) (hi - 1))
    (hη : ∀ e ∈ η, v ∈ e → e = s(u, v) ∨ e = s(v, w)) (hf : f ∈ dualEdge s(u, v))
    (hf' : ![u 0 + u 1 - v 1, u 1 + v 0 - u 0] ∈ Icc f (f + 1)) (hg : g ∈ dualEdge s(v, w))
    (hg' : ![v 0 + v 1 - w 1, v 1 + w 0 - v 0] ∈ Icc g (g + 1)) :
    dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g := by
  have hfu := mem_Icc_of_mem_dualEdge huv (Sym2.mem_mk_left _ _) hf
  have hfv := mem_Icc_of_mem_dualEdge huv (Sym2.mem_mk_right _ _) hf
  have hgv := mem_Icc_of_mem_dualEdge hvw (Sym2.mem_mk_left _ _) hg
  have hgw := mem_Icc_of_mem_dualEdge hvw (Sym2.mem_mk_right _ _) hg
  have hvR : v ∈ Icc lo hi := by
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hv
    omega
  have hfR : f ∈ Icc (lo - 1) hi := mem_Icc_sub_one_of_mem_Icc hvR hfv
  have hadj := (zdGraph_two_adj_iff u v).1 huv
  have hadj' := (zdGraph_two_adj_iff v w).1 hvw
  have hne : u 0 ≠ w 0 ∨ u 1 ≠ w 1 := by
    by_contra hc
    push Not at hc
    exact huw (funext (Fin.forall_fin_two.2 hc))
  rw [mem_Icc_two_iff] at hv hfu hfv hgv hgw hf' hg'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
    Pi.one_apply] at hv hfu hfv hgv hgw hf' hg'
  -- the points `a = v + L(v - u)` and `b = v + (v - u)`
  obtain ⟨a, ha0, ha1⟩ : ∃ a : LatticeSite 2, a 0 = v 0 + u 1 - v 1 ∧ a 1 = v 1 + v 0 - u 0 :=
    ⟨![_, _], rfl, rfl⟩
  obtain ⟨b, hb0, hb1⟩ : ∃ b : LatticeSite 2, b 0 = 2 * v 0 - u 0 ∧ b 1 = 2 * v 1 - u 1 :=
    ⟨![_, _], rfl, rfl⟩
  have hva : (zdGraph 2).Adj v a := by
    rw [zdGraph_two_adj_iff]
    omega
  have hvb : (zdGraph 2).Adj v b := by
    rw [zdGraph_two_adj_iff]
    omega
  have haR : a ∈ Icc lo hi := by
    rw [mem_Icc_two_iff]
    omega
  have hbR : b ∈ Icc lo hi := by
    rw [mem_Icc_two_iff]
    omega
  have hvf : v ∈ Icc f (f + 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  have hvg : v ∈ Icc g (g + 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  have haf : a ∈ Icc f (f + 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  have hfa : f ∈ dualEdge s(v, a) := mem_dualEdge_of_adj_of_mem_Icc hva hvf haf
  -- crossing a closed edge of the box at `v` other than the two steps
  have hcross : ∀ x, (zdGraph 2).Adj v x → x ∈ Icc lo hi → x ≠ u → x ≠ w → ∀ h h',
      h ∈ dualEdge s(v, x) → h' ∈ dualEdge s(v, x) →
      dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) h h' := by
    intro x hx hxR hxu hxw h h' hh hh'
    refine mem_localConn_of_mem_dualEdge_of_notMem hx (fun y hy => ?_) (fun hxη => ?_) hh hh'
    · rcases Sym2.mem_iff.1 hy with rfl | rfl
      exacts [hvR, hxR]
    · rcases hη _ hxη (Sym2.mem_mk_left _ _) with h | h
      · rcases Sym2.eq_iff.1 h with ⟨h₁, -⟩ | ⟨-, h₂⟩
        · exact huv.ne h₁.symm
        · exact hxu h₂
      · rcases Sym2.eq_iff.1 h with ⟨-, h₂⟩ | ⟨h₁, -⟩
        · exact hxw h₂
        · exact hvw.ne h₁
  have hau : a ≠ u := fun h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    omega
  have hbu : b ≠ u := fun h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    omega
  by_cases hwa : w 0 = a 0 ∧ w 1 = a 1
  · -- a left turn: the two faces coincide
    have hfg : f = g := funext (Fin.forall_fin_two.2 ⟨by omega, by omega⟩)
    subst hfg
    rw [localConn_self hfR]
    exact mem_univ _
  have hwa' : a ≠ w := fun h => hwa ⟨by rw [h], by rw [h]⟩
  by_cases hwb : w 0 = b 0 ∧ w 1 = b 1
  · -- straight on: cross the edge from `v` to the left
    have hag : a ∈ Icc g (g + 1) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    exact hcross a hva haR hau hwa' f g hfa (mem_dualEdge_of_adj_of_mem_Icc hva hvg hag)
  -- a right turn: cross the edge to the left, then the edge straight on
  have hwb' : b ≠ w := fun h => hwb ⟨by rw [h], by rw [h]⟩
  have hbg : b ∈ Icc g (g + 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  obtain ⟨h, hh₁, hh₂⟩ := exists_mem_dualEdge_of_adj hva hvb (by omega)
  exact localConn_trans (hcross a hva haR hau hwa' f h hfa hh₁)
    (hcross b hvb hbR hbu hwb' h g hh₂ (mem_dualEdge_of_adj_of_mem_Icc hvb hvg hbg))

/-- **Left faces along a path.** Let `u → v` followed by `p` be a path whose vertices after `u`
and before its last vertex lie in the interior of the box `Icc lo hi`, and such that every edge of
`η` at those vertices is an edge of the path. Then the face on the left of the first step is
joined to the face on the left of every step by dual edges of closed edges of the box. -/
theorem mem_localConn_of_isPath_left {lo hi : LatticeSite 2} {η : Config (LatticeSite 2)} :
    ∀ {u v w : LatticeSite 2} (huv : (zdGraph 2).Adj u v) (p : (zdGraph 2).Walk v w),
      (SimpleGraph.Walk.cons huv p).IsPath → u ∈ Icc lo hi →
      (∀ x ∈ p.support, x ≠ w → x ∈ Icc (lo + 1) (hi - 1)) →
      (∀ x ∈ p.support, x ≠ w → ∀ e ∈ η, x ∈ e → e ∈ (SimpleGraph.Walk.cons huv p).edges) →
      ∀ f, f ∈ dualEdge s(u, v) → ![u 0 + u 1 - v 1, u 1 + v 0 - u 0] ∈ Icc f (f + 1) →
      ∀ δ ∈ (SimpleGraph.Walk.cons huv p).darts, ∀ g, g ∈ dualEdge s(δ.fst, δ.snd) →
        ![δ.fst 0 + δ.fst 1 - δ.snd 1, δ.fst 1 + δ.snd 0 - δ.fst 0] ∈ Icc g (g + 1) →
        dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
          localConn (Icc (lo - 1) hi) f g := by
  intro u v w huv p
  induction p generalizing u with
  | nil =>
    intro _ hu _ _ f hf hf' δ hδ g hg hg'
    rw [SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.mem_singleton] at hδ
    subst hδ
    rw [eq_of_mem_dualEdge_of_mem_Icc_left hf hf' hg hg',
      localConn_self (mem_Icc_sub_one_of_mem_Icc hu
        (mem_Icc_of_mem_dualEdge huv (Sym2.mem_mk_left _ _) hg))]
    exact mem_univ _
  | @cons v x w hvx p ih =>
    intro hpath hu hint hη f hf hf' δ hδ g hg hg'
    rw [SimpleGraph.Walk.darts_cons, List.mem_cons] at hδ
    rcases hδ with rfl | hδ
    · rw [eq_of_mem_dualEdge_of_mem_Icc_left hf hf' hg hg',
        localConn_self (mem_Icc_sub_one_of_mem_Icc hu
          (mem_Icc_of_mem_dualEdge huv (Sym2.mem_mk_left _ _) hg))]
      exact mem_univ _
    have hpath' := hpath.of_cons
    have hu_notin : u ∉ (SimpleGraph.Walk.cons hvx p).support :=
      ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hpath).2
    have hv_notin : v ∉ p.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hpath').2
    have hvw : v ≠ w := fun h => hv_notin (h ▸ p.end_mem_support)
    have hux : u ≠ x := fun h => hu_notin (by
      rw [h, SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ p.start_mem_support)
    have hvint := hint v (SimpleGraph.Walk.start_mem_support _) hvw
    have hvR : v ∈ Icc lo hi := by
      rw [mem_Icc_two_iff] at hvint ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hvint
      omega
    obtain ⟨f₁, hf₁, hf₁'⟩ := exists_mem_dualEdge_left hvx
    have step := mem_localConn_of_mem_dualEdge_left huv hvx hux hvint (fun e he hve => by
      have := hη v (SimpleGraph.Walk.start_mem_support _) hvw e he hve
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, List.mem_cons,
        List.mem_cons] at this
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (mem_support_of_mem_edge p h hve) hv_notin) hf hf' hf₁ hf₁'
    refine localConn_trans step (ih hvx hpath' hvR (fun y hy hyw => hint y (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ hy) hyw) (fun y hy hyw e he hye => ?_) f₁ hf₁ hf₁' δ hδ g hg
      hg')
    have := hη y (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ hy) hyw e he hye
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at this
    rcases this with rfl | h
    · rcases Sym2.mem_iff.1 hye with rfl | rfl
      · exact absurd (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hy) hu_notin
      · exact absurd hy hv_notin
    · exact h

/-! ### Walking along the boundary of a box -/

/-- **Consecutive boundary points are neighbours.** On the boundary of a box of positive width and
height, two points whose perimeter positions are consecutive (modulo the perimeter) are
adjacent. -/
theorem adj_of_perimeterPos_eq_add_one {lo hi u w : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1) (hu : u ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (h : perimeterPos lo hi w = perimeterPos lo hi u + 1 ∨
      (perimeterPos lo hi w = 0 ∧
        perimeterPos lo hi u = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1)) :
    (zdGraph 2).Adj u w := by
  rw [mem_boxBoundary_two_iff] at hu hw
  rw [zdGraph_two_adj_iff]
  unfold perimeterPos at h
  split_ifs at h <;> omega

/-- **The inside is on the left.** Walking counterclockwise along the boundary of a box of
positive width and height, the face on the left of each step lies inside the box. -/
theorem mem_Icc_sub_one_of_perimeterPos_eq_add_one {lo hi u w f : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hu : u ∈ boxBoundary lo hi)
    (hw : w ∈ boxBoundary lo hi)
    (h : perimeterPos lo hi w = perimeterPos lo hi u + 1 ∨
      (perimeterPos lo hi w = 0 ∧
        perimeterPos lo hi u = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1))
    (hf : f ∈ dualEdge s(u, w)) (hf' : ![u 0 + u 1 - w 1, u 1 + w 0 - u 0] ∈ Icc f (f + 1)) :
    f ∈ Icc lo (hi - 1) := by
  have huw := adj_of_perimeterPos_eq_add_one h₀ h₁ hu hw h
  have hfu := mem_Icc_of_mem_dualEdge huw (Sym2.mem_mk_left _ _) hf
  have hfw := mem_Icc_of_mem_dualEdge huw (Sym2.mem_mk_right _ _) hf
  clear huw hf
  rw [mem_boxBoundary_two_iff] at hu hw
  obtain ⟨⟨hu0, hu0', hu1, hu1'⟩, hu⟩ := hu
  obtain ⟨⟨hw0, hw0', hw1, hw1'⟩, hw⟩ := hw
  rw [mem_Icc_two_iff] at hfu hfw hf' ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply,
    Pi.sub_apply] at hfu hfw hf' ⊢
  unfold perimeterPos at h
  split_ifs at h <;> omega

/-- **The outer end of a step inward.** If `e` lies on the boundary of a box and `q` is an
interior neighbour, the point `x = e + L(q - e)` on the left of the step `e → q` is the boundary
point just before `e` (counterclockwise), and it is a neighbour of `e` other than `q`. -/
theorem mem_boxBoundary_of_adj_of_mem_Icc {lo hi e q x : LatticeSite 2}
    (he : e ∈ boxBoundary lo hi) (hq : q ∈ Icc (lo + 1) (hi - 1)) (heq : (zdGraph 2).Adj e q)
    (hx0 : x 0 = e 0 + e 1 - q 1) (hx1 : x 1 = e 1 + q 0 - e 0) :
    x ∈ boxBoundary lo hi ∧
      (perimeterPos lo hi x + 1 = perimeterPos lo hi e ∨
        (perimeterPos lo hi e = 0 ∧
          perimeterPos lo hi x = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1)) ∧
      (zdGraph 2).Adj e x ∧ x ≠ q := by
  rw [mem_boxBoundary_two_iff] at he ⊢
  rw [mem_Icc_two_iff] at hq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hq
  rw [zdGraph_two_adj_iff] at heq ⊢
  refine ⟨by omega, ?_, by omega, fun h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    omega⟩
  unfold perimeterPos
  split_ifs <;> omega

/-- **Walking along the boundary.** On the boundary of a box of positive width and height, from a
point `u` at position `t` (modulo the perimeter `P`) there is a walk of `n` steps along the
boundary, counterclockwise, through the points at positions `t, t + 1, …, t + n` (modulo `P`),
each step joining consecutive positions. Positions are read on `[0, 2P)` so that no reduction is
needed. -/
theorem exists_walk_boundary {lo hi : LatticeSite 2} (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) :
    ∀ (n : ℕ) (u : LatticeSite 2) (t : ℤ), u ∈ boxBoundary lo hi →
      (perimeterPos lo hi u = t ∨
        perimeterPos lo hi u + (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) = t) →
      t + n < 2 * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) →
      ∃ w, w ∈ boxBoundary lo hi ∧ (perimeterPos lo hi w = t + n ∨
          perimeterPos lo hi w + (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) = t + n) ∧
        ∃ p : (zdGraph 2).Walk u w,
          (∀ x ∈ p.support, x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, 0 ≤ k ∧ k ≤ n ∧
            (perimeterPos lo hi x = t + k ∨
              perimeterPos lo hi x + (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) = t + k)) ∧
          ∀ δ ∈ p.darts, ∃ k : ℤ, 0 ≤ k ∧ k < n ∧
            (perimeterPos lo hi δ.fst = t + k ∨
              perimeterPos lo hi δ.fst + (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) = t + k) ∧
            (perimeterPos lo hi δ.snd = t + k + 1 ∨
              perimeterPos lo hi δ.snd + (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) =
                t + k + 1) := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  intro n
  induction n with
  | zero =>
    intro u t hu ht _
    refine ⟨u, hu, by simpa using ht, SimpleGraph.Walk.nil, fun x hx => ?_, fun δ hδ => by
      simp at hδ⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨hu, 0, le_rfl, le_rfl, by simpa using ht⟩
  | succ n ih =>
    intro u t hu ht htn
    have pu := perimeterPos_nonneg hu.1
    have pu' := perimeterPos_lt hne hu.1
    obtain ⟨v, w', f, hv, hpv, hw', hpw', -, -, -, -⟩ :=
      exists_notMem_Icc_of_perimeterPos h₀ h₁ pu pu'
    have hvu : v = u := perimeterPos_injOn lo hi hv hu hpv
    subst hvu
    have pw := perimeterPos_nonneg hw'.1
    have hadj := adj_of_perimeterPos_eq_add_one h₀ h₁ hv hw' (by omega)
    push_cast at htn
    obtain ⟨w, hw, hpw, p, hps, hpd⟩ := ih w' (t + 1) hw' (by omega) (by omega)
    refine ⟨w, hw, by push_cast; omega, SimpleGraph.Walk.cons hadj p, fun x hx => ?_,
      fun δ hδ => ?_⟩
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hv, 0, le_rfl, by positivity, by omega⟩
      · obtain ⟨hxb, k, hk0, hkn, hk⟩ := hps x hx
        exact ⟨hxb, k + 1, by omega, by push_cast; omega, by omega⟩
    · rw [SimpleGraph.Walk.darts_cons, List.mem_cons] at hδ
      rcases hδ with rfl | hδ
      · exact ⟨0, le_rfl, by positivity, by simp only [add_zero]; omega,
          by simp only [add_zero]; omega⟩
      · obtain ⟨k, hk0, hkn, hk1, hk2⟩ := hpd δ hδ
        exact ⟨k + 1, by omega, by push_cast; omega, by omega, by omega⟩

/-- **The counterclockwise arc between two boundary points.** On the boundary of a box of
positive width and height, two distinct points `s`, `s'` are joined by a walk along the
boundary each of whose vertices is `s`, `s'` or strictly between them counterclockwise from `s`. -/
theorem exists_walk_boundary_of_ne {lo hi s s' : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1) (hs : s ∈ boxBoundary lo hi) (hs' : s' ∈ boxBoundary lo hi) (hss' : s ≠ s') :
    ∃ p : (zdGraph 2).Walk s s', ∀ v ∈ p.support, v ∈ boxBoundary lo hi ∧ (v = s ∨ v = s' ∨
      ((perimeterPos lo hi s < perimeterPos lo hi v ∧
          perimeterPos lo hi v < perimeterPos lo hi s') ∨
        (perimeterPos lo hi v < perimeterPos lo hi s' ∧
          perimeterPos lo hi s' < perimeterPos lo hi s) ∨
        (perimeterPos lo hi s' < perimeterPos lo hi s ∧
          perimeterPos lo hi s < perimeterPos lo hi v))) := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have ps := perimeterPos_nonneg hs.1
  have ps' := perimeterPos_lt hne hs.1
  have pt := perimeterPos_nonneg hs'.1
  have pt' := perimeterPos_lt hne hs'.1
  have hpne : perimeterPos lo hi s ≠ perimeterPos lo hi s' :=
    fun h => hss' (perimeterPos_injOn lo hi hs hs' h)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (perimeterPos lo hi s < perimeterPos lo hi s' ∧
      (n : ℤ) = perimeterPos lo hi s' - perimeterPos lo hi s) ∨
      (perimeterPos lo hi s' < perimeterPos lo hi s ∧
      (n : ℤ) = perimeterPos lo hi s' - perimeterPos lo hi s +
        (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1))) := by
    rcases lt_or_gt_of_ne hpne with h | h
    · exact ⟨(perimeterPos lo hi s' - perimeterPos lo hi s).toNat,
        Or.inl ⟨h, Int.toNat_of_nonneg (by omega)⟩⟩
    · exact ⟨(perimeterPos lo hi s' - perimeterPos lo hi s +
        (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1))).toNat, Or.inr ⟨h, Int.toNat_of_nonneg (by omega)⟩⟩
  obtain ⟨w, hw, hpw, p, hps, -⟩ :=
    exists_walk_boundary h₀ h₁ n s (perimeterPos lo hi s) hs (Or.inl rfl) (by omega)
  have hws : w = s' := perimeterPos_injOn lo hi hw hs' (by
    have := perimeterPos_nonneg hw.1
    have := perimeterPos_lt hne hw.1
    omega)
  subst w
  refine ⟨p, fun v hv => ?_⟩
  obtain ⟨hvb, k, hk0, hkn, hk⟩ := hps v hv
  refine ⟨hvb, ?_⟩
  have pv := perimeterPos_nonneg hvb.1
  have pv' := perimeterPos_lt hne hvb.1
  by_cases h₂ : perimeterPos lo hi v = perimeterPos lo hi s
  · exact Or.inl (perimeterPos_injOn lo hi hvb hs h₂)
  by_cases h₃ : perimeterPos lo hi v = perimeterPos lo hi s'
  · exact Or.inr (Or.inl (perimeterPos_injOn lo hi hvb hs' h₃))
  exact Or.inr (Or.inr (by omega))

/-- **Faces inside a box are joined.** If every edge of `η` has a face outside the box
`Icc lo hi`, any two faces inside it are joined inside it by dual edges of closed edges; the
statement allows a larger box `Icc lo' hi'` for the edges and faces. -/
theorem mem_localConn_of_mem_Icc_sub_one {lo hi lo' hi' : LatticeSite 2} (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') {η : Config (LatticeSite 2)}
    (hη : ∀ e ∈ η ∩ (zdGraph 2).edgeSet, ∃ h ∈ dualEdge e, h ∉ Icc lo (hi - 1))
    {f g : LatticeSite 2} (hf : f ∈ Icc lo (hi - 1)) (hg : g ∈ Icc lo (hi - 1)) :
    dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo' hi'} ∈
      localConn (Icc (lo' - 1) hi') f g := by
  have hsub : Icc lo (hi - 1) ⊆ Icc (lo' - 1) hi' := fun x hx =>
    ⟨fun i => by
      have h₁ : lo i ≤ x i := hx.1 i
      have h₂ : lo' i ≤ lo i := hlo i
      change lo' i - 1 ≤ x i
      omega, fun i => by
      have h₁ : x i ≤ hi i - 1 := hx.2 i
      have h₂ : hi i ≤ hi' i := hhi i
      change x i ≤ hi' i
      omega⟩
  have key : ∀ a ∈ Icc lo (hi - 1), ∀ b ∈ Icc lo (hi - 1), s(a, b) ∈ (zdGraph 2).edgeSet →
      s(a, b) ∈ dualConfig η ∩
        dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo' hi'} := by
    intro a ha b hb hab
    have he : Sym2.map (· + 1) (dualEdge s(a, b)) ∈ (zdGraph 2).edgeSet :=
      map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hab)
    have hee : dualEdge (Sym2.map (· + 1) (dualEdge s(a, b))) = s(a, b) := by
      rw [dualEdge_map_add, map_add_one_dualEdge_dualEdge hab]
    refine ⟨?_, _, ⟨he, fun x hx => Icc_subset_Icc hlo hhi (mem_Icc_of_mem_Icc_sub_one ha
      (mem_Icc_of_mem_dualEdge he hx (by rw [hee]; exact Sym2.mem_mk_left _ _)))⟩, hee⟩
    rw [← hee, dualEdge_mem_dualConfig_iff he]
    intro hη'
    obtain ⟨h, hh, hh'⟩ := hη _ ⟨hη', he⟩
    rw [hee, Sym2.mem_iff] at hh
    rcases hh with rfl | rfl
    exacts [hh' ha, hh' hb]
  refine localConn_mono_set hsub f g ?_
  obtain ⟨hf', hg', hr⟩ := edgeSet_mem_localConn_Icc hf hg
  refine ⟨hf', hg', hr.mono fun a b hab => ?_⟩
  simp only [SimpleGraph.induce, SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
    openGraph_adj_iff] at hab ⊢
  exact ⟨key a a.2 b b.2 hab.1, hab.2⟩

/-- **The next boundary point.** Every point of the boundary of a box of positive width and
height has a successor at the next position (modulo the perimeter). -/
theorem exists_mem_boxBoundary_perimeterPos_eq_add_one {lo hi u : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hu : u ∈ boxBoundary lo hi) :
    ∃ w, w ∈ boxBoundary lo hi ∧ (perimeterPos lo hi w = perimeterPos lo hi u + 1 ∨
      (perimeterPos lo hi w = 0 ∧
        perimeterPos lo hi u = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1)) := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  obtain ⟨v, w, f, hv, hpv, hw, hpw, -⟩ :=
    exists_notMem_Icc_of_perimeterPos h₀ h₁ (perimeterPos_nonneg hu.1) (perimeterPos_lt hne hu.1)
  exact ⟨w, hw, by omega⟩

/-- **The outer face of a boundary edge.** On the boundary of a box of positive width and
height, the edge between two points at consecutive positions has a face outside the box. -/
theorem exists_notMem_Icc_mem_dualEdge_of_perimeterPos_eq_add_one {lo hi u w : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hu : u ∈ boxBoundary lo hi)
    (hw : w ∈ boxBoundary lo hi)
    (h : perimeterPos lo hi w = perimeterPos lo hi u + 1 ∨
      (perimeterPos lo hi w = 0 ∧
        perimeterPos lo hi u = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1)) :
    ∃ f, f ∉ Icc lo (hi - 1) ∧ u ∈ Icc f (f + 1) ∧ w ∈ Icc f (f + 1) ∧
      f ∈ dualEdge s(u, w) := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  obtain ⟨v, w', f, hv, hpv, hw', hpw', hf, hvf, hw'f, -⟩ :=
    exists_notMem_Icc_of_perimeterPos h₀ h₁ (perimeterPos_nonneg hu.1) (perimeterPos_lt hne hu.1)
  have hvu : v = u := perimeterPos_injOn lo hi hv hu hpv
  have hw'w : w' = w := perimeterPos_injOn lo hi hw' hw (by
    have := perimeterPos_lt hne hw.1
    have := perimeterPos_lt hne hw'.1
    omega)
  subst hvu hw'w
  have hvw : v ≠ w' := fun h' => by
    rw [h'] at hpw'
    omega
  exact ⟨f, hf, hvf, hw'f,
    (mem_edgeSet_and_mem_dualEdge_of_notMem_Icc hv.1 hw'.1 hvw hf hvf hw'f).2⟩

/-- The faces of the edges of a walk that meets a box only at its first vertex lie outside the
box. -/
theorem notMem_Icc_of_mem_dualEdge_of_mem_edges {lo hi s t : LatticeSite 2}
    (γ : (zdGraph 2).Walk s t) (hγ : ∀ v ∈ γ.support, v ∈ Icc lo hi → v = s)
    (e : Sym2 (LatticeSite 2)) (he : e ∈ γ.edges) (h : LatticeSite 2) (hh : h ∈ dualEdge e) :
    h ∉ Icc lo (hi - 1) := by
  intro hhI
  induction e using Sym2.ind with
  | h a b =>
    have hab := γ.adj_of_mem_edges he
    have ha := hγ a (γ.fst_mem_support_of_mem_edges he) (mem_Icc_of_mem_Icc_sub_one hhI
      (mem_Icc_of_mem_dualEdge hab (Sym2.mem_mk_left _ _) hh))
    have hb := hγ b (γ.snd_mem_support_of_mem_edges he) (mem_Icc_of_mem_Icc_sub_one hhI
      (mem_Icc_of_mem_dualEdge hab (Sym2.mem_mk_right _ _) hh))
    exact hab.ne (ha.trans hb.symm)

/-- **The left side of a path from the boundary.** Let `e → q` followed by `ρ` be a path from a
point `e` of the boundary of a box of positive width and height, entering the interior at its
first step and staying there until its last vertex `t`, such that every edge of `η` at a vertex
other than `t` is an edge of the path. Let `x` be the boundary point just before `e`
(counterclockwise) and `F` the face outside the box of the boundary edge `{x, e}`. Then `F` is
joined to the face on the left of every step of the path by dual edges of closed edges of the
box. -/
theorem exists_mem_boxBoundary_localConn_left {lo hi : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1) {η : Config (LatticeSite 2)} {e q t : LatticeSite 2}
    (hq : (zdGraph 2).Adj e q) (ρ : (zdGraph 2).Walk q t)
    (hpath : (SimpleGraph.Walk.cons hq ρ).IsPath) (he : e ∈ boxBoundary lo hi)
    (hqint : q ∈ Icc (lo + 1) (hi - 1))
    (hint : ∀ x ∈ ρ.support, x ≠ t → x ∈ Icc (lo + 1) (hi - 1))
    (hη : ∀ x ∈ (SimpleGraph.Walk.cons hq ρ).support, x ≠ t → ∀ e' ∈ η, x ∈ e' →
      e' ∈ (SimpleGraph.Walk.cons hq ρ).edges) :
    ∃ x F, x ∈ boxBoundary lo hi ∧
      (perimeterPos lo hi x + 1 = perimeterPos lo hi e ∨
        (perimeterPos lo hi e = 0 ∧
          perimeterPos lo hi x = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1)) ∧
      F ∉ Icc lo (hi - 1) ∧ x ∈ Icc F (F + 1) ∧
      ∀ δ ∈ (SimpleGraph.Walk.cons hq ρ).darts, ∀ g, g ∈ dualEdge s(δ.fst, δ.snd) →
        ![δ.fst 0 + δ.fst 1 - δ.snd 1, δ.fst 1 + δ.snd 0 - δ.fst 0] ∈ Icc g (g + 1) →
        dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
          localConn (Icc (lo - 1) hi) F g := by
  obtain ⟨hx, hpx, hex, hxq⟩ := mem_boxBoundary_of_adj_of_mem_Icc
    (x := ![e 0 + e 1 - q 1, e 1 + q 0 - e 0]) he hqint hq rfl rfl
  obtain ⟨F, hF, hxF, -, hFe⟩ :=
    exists_notMem_Icc_mem_dualEdge_of_perimeterPos_eq_add_one h₀ h₁ hx he (by omega)
  obtain ⟨f₀, hf₀, hf₀'⟩ := exists_mem_dualEdge_left hq
  have hef₀ := mem_Icc_of_mem_dualEdge hq (Sym2.mem_mk_left _ _) hf₀
  have hf₀x : f₀ ∈ dualEdge s(e, ![e 0 + e 1 - q 1, e 1 + q 0 - e 0]) :=
    mem_dualEdge_of_adj_of_mem_Icc hex hef₀ hf₀'
  have het : e ≠ t := fun h => ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hpath).2
    (h ▸ ρ.end_mem_support)
  have hstart : dualConfig η ∩
      dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) F f₀ := by
    refine mem_localConn_of_mem_dualEdge_of_notMem hex (fun y hy => ?_) (fun hη' => ?_)
      (by rw [Sym2.eq_swap]; exact hFe) hf₀x
    · rcases Sym2.mem_iff.1 hy with rfl | rfl
      exacts [he.1, hx.1]
    · exact hxq ((hpath.eq_snd_of_mem_edges
        (hη e (SimpleGraph.Walk.start_mem_support _) het _ hη' (Sym2.mem_mk_left _ _))).trans
        (SimpleGraph.Walk.snd_cons _ _))
  refine ⟨_, F, hx, hpx, hF, hxF, fun δ hδ g hg hg' => localConn_trans hstart
    (mem_localConn_of_isPath_left hq ρ hpath he.1 hint (fun y hy hyt => hη y (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ hy) hyt) f₀ hf₀ hf₀' δ hδ g hg hg')⟩

/-! ### Order invariance of arms -/

/-- **Order of three arms, the core step.** Let `I = Icc lo hi` (positive width and height) lie
inside the interior of `O = Icc lo' hi'`, and let `γ₁, γ₂, γ₃` be pairwise vertex-disjoint walks in
`O` from points `sᵢ` of `∂I` to points `eᵢ` of `∂O`, each meeting `I` only at its first vertex, and
`γ₂` meeting `∂O` only at its last vertex. If the starts are in counterclockwise order on `∂I` and
`e₃` is not the boundary point just before `e₂`, then `e₁` does not lie strictly between `e₂` and
`e₃` counterclockwise.

The many hypotheses describe three arms (ends, boxes, disjointness); a structure for arms is an
interface matter (left to the arm-event package).

Proof: the cross-cut `Q` = (`γ₂` reversed, the counterclockwise arc of `∂I` from `s₂` to `s₃`,
`γ₃`) is open in the configuration of its edges. Its left side runs from the outer face just
before `e₂`, along `γ₂` (left faces of a path), into `I` across the arc; the faces of `I` are
joined;
the ring of faces around `γ₁` (which avoids `Q`) reaches an outer face at `e₁`. If `e₁` were
between `e₂` and `e₃`, this dual path would cross the open path `Q` with interlaced ends. -/
theorem not_cyclicallyOrdered_of_cyclicallyOrdered {lo hi lo' hi' : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hlo : lo' + 1 ≤ lo) (hhi : hi + 1 ≤ hi')
    {s₁ s₂ s₃ e₁ e₂ e₃ : LatticeSite 2} (γ₁ : (zdGraph 2).Walk s₁ e₁)
    (γ₂ : (zdGraph 2).Walk s₂ e₂) (γ₃ : (zdGraph 2).Walk s₃ e₃)
    (hs₁ : s₁ ∈ boxBoundary lo hi) (hs₂ : s₂ ∈ boxBoundary lo hi)
    (hs₃ : s₃ ∈ boxBoundary lo hi) (he₁ : e₁ ∈ boxBoundary lo' hi')
    (he₂ : e₂ ∈ boxBoundary lo' hi') (he₃ : e₃ ∈ boxBoundary lo' hi')
    (hγ₁ : ∀ v ∈ γ₁.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₁))
    (hγ₂ : ∀ v ∈ γ₂.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₂) ∧
      (v ∈ boxBoundary lo' hi' → v = e₂))
    (hγ₃ : ∀ v ∈ γ₃.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₃))
    (h₁₂ : ∀ v ∈ γ₁.support, v ∉ γ₂.support) (h₁₃ : ∀ v ∈ γ₁.support, v ∉ γ₃.support)
    (h₂₃ : ∀ v ∈ γ₂.support, v ∉ γ₃.support)
    (hs : (perimeterPos lo hi s₁ < perimeterPos lo hi s₂ ∧
        perimeterPos lo hi s₂ < perimeterPos lo hi s₃) ∨
      (perimeterPos lo hi s₂ < perimeterPos lo hi s₃ ∧
        perimeterPos lo hi s₃ < perimeterPos lo hi s₁) ∨
      (perimeterPos lo hi s₃ < perimeterPos lo hi s₁ ∧
        perimeterPos lo hi s₁ < perimeterPos lo hi s₂))
    (hgap : ¬ (perimeterPos lo' hi' e₃ + 1 = perimeterPos lo' hi' e₂ ∨
      (perimeterPos lo' hi' e₂ = 0 ∧
        perimeterPos lo' hi' e₃ = 2 * (hi' 0 - lo' 0) + 2 * (hi' 1 - lo' 1) - 1))) :
    ¬ ((perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₁ ∧
        perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₃) ∨
      (perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₃ ∧
        perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₂) ∨
      (perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₂ ∧
        perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₁)) := by
  intro hcyc
  -- the boxes
  have hl0 : lo' 0 + 1 ≤ lo 0 := hlo 0
  have hl1 : lo' 1 + 1 ≤ lo 1 := hlo 1
  have hh0 : hi 0 + 1 ≤ hi' 0 := hhi 0
  have hh1 : hi 1 + 1 ≤ hi' 1 := hhi 1
  have h₀' : lo' 0 < hi' 0 := by omega
  have h₁' : lo' 1 < hi' 1 := by omega
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have hne' : lo' ≠ hi' := fun h => by
    rw [h] at h₀'
    exact lt_irrefl _ h₀'
  have hlo' : lo' ≤ lo := fun i => by
    have h : lo' i + 1 ≤ lo i := hlo i
    change lo' i ≤ lo i
    omega
  have hhi' : hi ≤ hi' := fun i => by
    have h : hi i + 1 ≤ hi' i := hhi i
    change hi i ≤ hi' i
    omega
  have hIO : ∀ v ∈ Icc lo hi, v ∈ Icc lo' hi' := fun v hv => Icc_subset_Icc hlo' hhi' hv
  have hIint : ∀ v ∈ Icc lo hi, v ∈ Icc (lo' + 1) (hi' - 1) := fun v hv => by
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
    omega
  have hIb : ∀ v ∈ Icc lo hi, v ∉ boxBoundary lo' hi' := fun v hv hvb => by
    rw [boxBoundary_eq_Icc_diff_Icc] at hvb
    exact hvb.2 (hIint v hv)
  have hint : ∀ v ∈ Icc lo' hi', v ∉ boxBoundary lo' hi' → v ∈ Icc (lo' + 1) (hi' - 1) :=
    fun v hv hvb => by
      rw [boxBoundary_eq_Icc_diff_Icc] at hvb
      by_contra h
      exact hvb ⟨hv, h⟩
  -- positions
  have ps₁ := perimeterPos_nonneg hs₁.1
  have ps₁' := perimeterPos_lt hne hs₁.1
  have ps₂ := perimeterPos_nonneg hs₂.1
  have ps₂' := perimeterPos_lt hne hs₂.1
  have ps₃ := perimeterPos_nonneg hs₃.1
  have ps₃' := perimeterPos_lt hne hs₃.1
  have pe₁ := perimeterPos_nonneg he₁.1
  have pe₁' := perimeterPos_lt hne' he₁.1
  have pe₂ := perimeterPos_nonneg he₂.1
  have pe₂' := perimeterPos_lt hne' he₂.1
  have pe₃ := perimeterPos_nonneg he₃.1
  have pe₃' := perimeterPos_lt hne' he₃.1
  -- a path along `γ₂`
  have hγp : γ₂.bypass.IsPath := γ₂.bypass_isPath
  have hγs : ∀ v ∈ γ₂.bypass.support, v ∈ γ₂.support :=
    fun v hv => γ₂.support_bypass_subset_support hv
  -- the point `t₂` after `s₂`, and the arc of `∂I` from `t₂` to `s₃`
  obtain ⟨t₂, ht₂, hpt₂⟩ := exists_mem_boxBoundary_perimeterPos_eq_add_one h₀ h₁ hs₂
  have hadj₂ := adj_of_perimeterPos_eq_add_one h₀ h₁ hs₂ ht₂ hpt₂
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (perimeterPos lo hi s₂ < perimeterPos lo hi s₃ ∧
      (n : ℤ) = perimeterPos lo hi s₃ - perimeterPos lo hi s₂ - 1) ∨
      (perimeterPos lo hi s₃ < perimeterPos lo hi s₂ ∧
      (n : ℤ) = perimeterPos lo hi s₃ - perimeterPos lo hi s₂ - 1 +
        (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1))) := by
    rcases lt_or_gt_of_ne (show perimeterPos lo hi s₂ ≠ perimeterPos lo hi s₃ by omega) with h | h
    · exact ⟨(perimeterPos lo hi s₃ - perimeterPos lo hi s₂ - 1).toNat,
        Or.inl ⟨h, Int.toNat_of_nonneg (by omega)⟩⟩
    · exact ⟨(perimeterPos lo hi s₃ - perimeterPos lo hi s₂ - 1 +
        (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1))).toNat, Or.inr ⟨h, Int.toNat_of_nonneg (by omega)⟩⟩
  obtain ⟨w, hw, hpw, arc, harcs, harcd⟩ :=
    exists_walk_boundary h₀ h₁ n t₂ (perimeterPos lo hi s₂ + 1) ht₂ (by omega) (by omega)
  have hws : w = s₃ := perimeterPos_injOn lo hi hw hs₃ (by
    have := perimeterPos_nonneg hw.1
    have := perimeterPos_lt hne hw.1
    omega)
  subst w
  have harcI : ∀ v ∈ arc.support, v ∈ Icc lo hi := fun v hv => (harcs v hv).1.1
  have hs₂arc : s₂ ∉ arc.support := fun h => by
    obtain ⟨-, k, hk0, hkn, hk⟩ := harcs s₂ h
    omega
  have hs₁arc : s₁ ∉ arc.support := fun h => by
    obtain ⟨-, k, hk0, hkn, hk⟩ := harcs s₁ h
    omega
  -- the path `W`: back along `γ₂` from `e₂` to `s₂`, then one step to `t₂`
  have he₂s₂ : e₂ ≠ s₂ := fun h => hIb s₂ hs₂.1 (h ▸ he₂)
  obtain ⟨q, hq, ρ, hρ⟩ := γ₂.bypass.reverse.exists_eq_cons_of_ne he₂s₂
  have hrevp : (SimpleGraph.Walk.cons hq ρ).IsPath := by
    rw [← hρ]
    exact hγp.reverse
  have hρs : ∀ v ∈ ρ.support, v ∈ γ₂.support := fun v hv => hγs v (by
    have : v ∈ γ₂.bypass.reverse.support := by
      rw [hρ, SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ hv
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)
  have hρe : ∀ e ∈ (SimpleGraph.Walk.cons hq ρ).edges, e ∈ γ₂.edges := fun e he => by
    rw [← hρ, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact γ₂.edges_bypass_subset_edges he
  have he₂ρ : e₂ ∉ ρ.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hrevp).2
  have hρp : ρ.IsPath := hrevp.of_cons
  have hγ₂e : e₂ ∈ γ₂.support := γ₂.end_mem_support
  have ht₂s₂ : t₂ ≠ s₂ := fun h => by
    rw [h] at hpt₂
    omega
  have ht₂ρ : t₂ ∉ ρ.support := fun h => ht₂s₂ ((hγ₂ t₂ (hρs t₂ h)).2.1 ht₂.1)
  have he₂t₂ : e₂ ≠ t₂ := fun h => hIb t₂ ht₂.1 (h ▸ he₂)
  have hWp : (SimpleGraph.Walk.cons hq (ρ.concat hadj₂)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨hρp.concat ht₂ρ hadj₂, ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
    rintro (h | h)
    exacts [he₂ρ h, he₂t₂ h]
  have hWs : ∀ v ∈ (SimpleGraph.Walk.cons hq (ρ.concat hadj₂)).support,
      v = e₂ ∨ v ∈ ρ.support ∨ v = t₂ := by
    intro v hv
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat, List.mem_cons,
      List.mem_append, List.mem_singleton] at hv
    exact hv
  -- the cross-cut `Q` and its edges
  set W := SimpleGraph.Walk.cons hq (ρ.concat hadj₂) with hW
  set Q := W.append (arc.append γ₃) with hQ
  set η : Config (LatticeSite 2) := {e | e ∈ Q.edges} with hη
  have hQe : ∀ e, e ∈ Q.edges → e ∈ W.edges ∨ e ∈ arc.edges ∨ e ∈ γ₃.edges := by
    intro e he
    rwa [hQ, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append, List.mem_append,
      List.mem_append] at he
  have hQs : ∀ v ∈ Q.support, v ∈ Icc lo' hi' := by
    intro v hv
    rw [hQ, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv | hv
    · rcases hWs v hv with rfl | hv | rfl
      · exact he₂.1
      · exact (hγ₂ v (hρs v hv)).1
      · exact hIO _ ht₂.1
    · exact hIO v (harcI v hv)
    · exact (hγ₃ v hv).1
  have hQconn : η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo' hi') e₂ e₃ :=
    mem_localConn_edges_of_walk Q hQs
  -- edges of `η` at the vertices of `W` other than `t₂` are edges of `W`
  have hηW : ∀ x ∈ W.support, x ≠ t₂ → ∀ e ∈ η, x ∈ e → e ∈ W.edges := by
    intro x hx hxt e he hxe
    rcases hQe e he with h | h | h
    · exact h
    · exfalso
      have hxa := mem_support_of_mem_edge arc h hxe
      rcases hWs x hx with rfl | hxρ | rfl
      · exact hIb _ (harcI _ hxa) he₂
      · have := (hγ₂ x (hρs x hxρ)).2.1 (harcI x hxa)
        rw [this] at hxa
        exact hs₂arc hxa
      · exact hxt rfl
    · exfalso
      have hx3 := mem_support_of_mem_edge γ₃ h hxe
      rcases hWs x hx with rfl | hxρ | rfl
      · exact h₂₃ _ hγ₂e hx3
      · exact h₂₃ x (hρs x hxρ) hx3
      · exact hxt rfl
  -- no edge of `η` touches `γ₁`
  have hη₁ : ∀ v ∈ γ₁.support, ∀ e ∈ η ∩ (zdGraph 2).edgeSet, v ∉ e := by
    intro v hv e he hve
    rcases hQe e he.1 with h | h | h
    · rcases hWs v (mem_support_of_mem_edge W h hve) with rfl | hvρ | rfl
      · exact h₁₂ _ hv hγ₂e
      · exact h₁₂ v hv (hρs v hvρ)
      · have := (hγ₁ _ hv).2 ht₂.1
        rw [this] at hpt₂
        omega
    · have hva := mem_support_of_mem_edge arc h hve
      have := (hγ₁ v hv).2 (harcI v hva)
      rw [this] at hva
      exact hs₁arc hva
    · exact h₁₃ v hv (mem_support_of_mem_edge γ₃ h hve)
  -- every edge of `η` has a face outside `I`
  have hηI : ∀ e ∈ η ∩ (zdGraph 2).edgeSet, ∃ h ∈ dualEdge e, h ∉ Icc lo (hi - 1) := by
    intro e he
    obtain ⟨h, hh⟩ : ∃ h, h ∈ dualEdge e := by
      induction e using Sym2.ind with
      | h a b => exact ⟨_, by rw [dualEdge_mk]; exact Sym2.mem_mk_left _ _⟩
    rcases hQe e he.1 with hW' | ha | h3
    · rw [hW, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_concat, List.mem_cons,
        List.concat_eq_append, List.mem_append, List.mem_singleton] at hW'
      rcases hW' with rfl | hρe' | rfl
      · exact ⟨h, hh, notMem_Icc_of_mem_dualEdge_of_mem_edges γ₂
          (fun v hv hvI => (hγ₂ v hv).2.1 hvI) _ (hρe _ (by simp)) h hh⟩
      · exact ⟨h, hh, notMem_Icc_of_mem_dualEdge_of_mem_edges γ₂
          (fun v hv hvI => (hγ₂ v hv).2.1 hvI) _ (hρe _ (by simp [hρe'])) h hh⟩
      · obtain ⟨F, hF, -, -, hFe⟩ :=
          exists_notMem_Icc_mem_dualEdge_of_perimeterPos_eq_add_one h₀ h₁ hs₂ ht₂ hpt₂
        exact ⟨F, hFe, hF⟩
    · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 ha
      obtain ⟨k, hk0, hkn, hk1, hk2⟩ := harcd δ hδ
      have hδ1 := harcs _ (arc.dart_fst_mem_support_of_mem_darts hδ)
      have hδ2 := harcs _ (arc.dart_snd_mem_support_of_mem_darts hδ)
      obtain ⟨F, hF, -, -, hFe⟩ :=
        exists_notMem_Icc_mem_dualEdge_of_perimeterPos_eq_add_one h₀ h₁ hδ1.1 hδ2.1 (by
          have := perimeterPos_nonneg hδ1.1.1
          have := perimeterPos_lt hne hδ1.1.1
          have := perimeterPos_nonneg hδ2.1.1
          have := perimeterPos_lt hne hδ2.1.1
          omega)
      exact ⟨F, hFe, hF⟩
    · exact ⟨h, hh, notMem_Icc_of_mem_dualEdge_of_mem_edges γ₃
        (fun v hv hvI => (hγ₃ v hv).2 hvI) e h3 h hh⟩
  -- the left side of `W`, from the outer face just before `e₂` to the inside of `I`
  have hqint : q ∈ Icc (lo' + 1) (hi' - 1) := by
    have hqρ : q ∈ ρ.support := ρ.start_mem_support
    have hq2 := hγ₂ q (hρs q hqρ)
    exact hint q hq2.1 (fun hqb => he₂ρ (hq2.2.2 hqb ▸ hqρ))
  have hWint : ∀ y ∈ (ρ.concat hadj₂).support, y ≠ t₂ → y ∈ Icc (lo' + 1) (hi' - 1) := by
    intro y hy hyt
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · have h2 := hγ₂ y (hρs y hy)
      exact hint y h2.1 (fun hyb => he₂ρ (h2.2.2 hyb ▸ hy))
    · exact absurd hy hyt
  obtain ⟨x, FL, hx, hpx, hFL, hxFL, hchain⟩ :=
    exists_mem_boxBoundary_localConn_left h₀' h₁' hq (ρ.concat hadj₂) hWp he₂ hqint hWint hηW
  obtain ⟨g₀, hg₀, hg₀'⟩ := exists_mem_dualEdge_left hadj₂
  have hg₀I := mem_Icc_sub_one_of_perimeterPos_eq_add_one h₀ h₁ hs₂ ht₂ hpt₂ hg₀ hg₀'
  have hc₁ := hchain ⟨(s₂, t₂), hadj₂⟩ (by
    rw [SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_concat]
    simp) g₀ hg₀ hg₀'
  -- the faces of `I` are joined, and the ring of faces around `γ₁` reaches the outside
  obtain ⟨t₁, ht₁, hpt₁⟩ := exists_mem_boxBoundary_perimeterPos_eq_add_one h₀ h₁ hs₁
  have hadj₁ := adj_of_perimeterPos_eq_add_one h₀ h₁ hs₁ ht₁ hpt₁
  obtain ⟨g₁, hg₁, hg₁'⟩ := exists_mem_dualEdge_left hadj₁
  have hg₁I := mem_Icc_sub_one_of_perimeterPos_eq_add_one h₀ h₁ hs₁ ht₁ hpt₁ hg₁ hg₁'
  have hc₂ := mem_localConn_of_mem_Icc_sub_one hlo' hhi' hηI hg₀I hg₁I
  obtain ⟨a', F₁, hea', ha', hF₁, hF₁e⟩ :=
    exists_notMem_Icc_mem_dualEdge_of_mem_boxBoundary h₀' h₁' he₁
  have hc₃ := mem_localConn_of_walk_of_mem_dualEdge h₀' h₁' γ₁ (fun v hv => (hγ₁ v hv).1) hη₁
    γ₁.start_mem_support γ₁.end_mem_support hadj₁ (hIO t₁ ht₁.1) hg₁ hea' ha' hF₁e
  have hconn := localConn_trans (localConn_trans hc₁ hc₂) hc₃
  have he₁F₁ := mem_Icc_of_mem_dualEdge hea' (Sym2.mem_mk_left _ _) hF₁e
  -- the dual path from just before `e₂` to `e₁` crosses the open path `Q`
  have px := perimeterPos_nonneg hx.1
  have px' := perimeterPos_lt hne' hx.1
  rcases lt_or_gt_of_ne (show perimeterPos lo' hi' e₂ ≠ perimeterPos lo' hi' e₃ by omega) with
    h | h
  · refine dualConfig_inter_notMem_localConn_of_interlaced h₀' h₁' hQconn he₂ he₃ hF₁ he₁ he₁F₁
      hFL hx hxFL (Or.inl ⟨by omega, by omega, by omega⟩) ?_
    rw [localConn_comm]
    exact hconn
  · exact dualConfig_inter_notMem_localConn_of_interlaced h₀' h₁' hQconn he₂ he₃ hFL hx hxFL hF₁
      he₁ he₁F₁ (Or.inr ⟨by omega, by omega, by omega⟩) hconn

/-- **Same side.** Let `p` and `q` be vertex-disjoint walks in a box of `ℤ²`, `p` from `a` to `b`
and `q` from `u` to `w`, all four ends on the boundary. If `a` and `b` follow `u` in this
counterclockwise order, so they follow `w`: the walk `q` cannot cross `p`. -/
theorem cyclicallyOrdered_of_cyclicallyOrdered_of_disjoint {lo hi a b u w : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (q : (zdGraph 2).Walk u w) (hp : ∀ v ∈ p.support, v ∈ Icc lo hi)
    (hq : ∀ v ∈ q.support, v ∈ Icc lo hi) (ha : a ∈ boxBoundary lo hi)
    (hb : b ∈ boxBoundary lo hi) (hu : u ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (hpq : ∀ v ∈ p.support, v ∉ q.support)
    (h : ((perimeterPos lo hi u < perimeterPos lo hi a ∧
          perimeterPos lo hi a < perimeterPos lo hi b) ∨
        (perimeterPos lo hi a < perimeterPos lo hi b ∧
          perimeterPos lo hi b < perimeterPos lo hi u) ∨
        (perimeterPos lo hi b < perimeterPos lo hi u ∧
          perimeterPos lo hi u < perimeterPos lo hi a))) :
    ((perimeterPos lo hi w < perimeterPos lo hi a ∧
        perimeterPos lo hi a < perimeterPos lo hi b) ∨
      (perimeterPos lo hi a < perimeterPos lo hi b ∧
        perimeterPos lo hi b < perimeterPos lo hi w) ∨
      (perimeterPos lo hi b < perimeterPos lo hi w ∧
        perimeterPos lo hi w < perimeterPos lo hi a)) := by
  have hwa : perimeterPos lo hi w ≠ perimeterPos lo hi a := fun h' =>
    hpq a p.start_mem_support (perimeterPos_injOn lo hi hw ha h' ▸ q.end_mem_support)
  have hwb : perimeterPos lo hi w ≠ perimeterPos lo hi b := fun h' =>
    hpq b p.end_mem_support (perimeterPos_injOn lo hi hw hb h' ▸ q.end_mem_support)
  by_contra hc
  rcases lt_or_gt_of_ne (show perimeterPos lo hi a ≠ perimeterPos lo hi b by omega) with h' | h'
  · obtain ⟨v, hvp, hvq⟩ := exists_mem_support_of_interlaced p q.reverse hp
      (fun v hv => hq v (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv)) ha hb
      hw hu (Or.inl ⟨by omega, by omega, by omega⟩)
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hvq
    exact hpq v hvp hvq
  · obtain ⟨v, hvp, hvq⟩ := exists_mem_support_of_interlaced p q hp hq ha hb hu hw
      (Or.inr ⟨by omega, by omega, by omega⟩)
    exact hpq v hvp hvq

/-- **Order invariance, first-hit form, one direction.** See `cyclicallyOrdered_firstHit_iff`. -/
theorem cyclicallyOrdered_firstHit {lo hi lo' hi' : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hlo : lo' + 1 ≤ lo) (hhi : hi + 1 ≤ hi')
    {s₁ s₂ s₃ e₁ e₂ e₃ : LatticeSite 2} (γ₁ : (zdGraph 2).Walk s₁ e₁)
    (γ₂ : (zdGraph 2).Walk s₂ e₂) (γ₃ : (zdGraph 2).Walk s₃ e₃)
    (hs₁ : s₁ ∈ boxBoundary lo hi) (hs₂ : s₂ ∈ boxBoundary lo hi)
    (hs₃ : s₃ ∈ boxBoundary lo hi) (he₁ : e₁ ∈ boxBoundary lo' hi')
    (he₂ : e₂ ∈ boxBoundary lo' hi') (he₃ : e₃ ∈ boxBoundary lo' hi')
    (hγ₁ : ∀ v ∈ γ₁.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₁) ∧
      (v ∈ boxBoundary lo' hi' → v = e₁))
    (hγ₂ : ∀ v ∈ γ₂.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₂) ∧
      (v ∈ boxBoundary lo' hi' → v = e₂))
    (hγ₃ : ∀ v ∈ γ₃.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₃) ∧
      (v ∈ boxBoundary lo' hi' → v = e₃))
    (h₁₂ : ∀ v ∈ γ₁.support, v ∉ γ₂.support) (h₁₃ : ∀ v ∈ γ₁.support, v ∉ γ₃.support)
    (h₂₃ : ∀ v ∈ γ₂.support, v ∉ γ₃.support)
    (hs : ((perimeterPos lo hi s₁ < perimeterPos lo hi s₂ ∧
          perimeterPos lo hi s₂ < perimeterPos lo hi s₃) ∨
        (perimeterPos lo hi s₂ < perimeterPos lo hi s₃ ∧
          perimeterPos lo hi s₃ < perimeterPos lo hi s₁) ∨
        (perimeterPos lo hi s₃ < perimeterPos lo hi s₁ ∧
          perimeterPos lo hi s₁ < perimeterPos lo hi s₂))) :
    ((perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂ ∧
        perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃) ∨
      (perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃ ∧
        perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁) ∨
      (perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁ ∧
        perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂)) := by
  have hl0 : lo' 0 + 1 ≤ lo 0 := hlo 0
  have hl1 : lo' 1 + 1 ≤ lo 1 := hlo 1
  have hh0 : hi 0 + 1 ≤ hi' 0 := hhi 0
  have hh1 : hi 1 + 1 ≤ hi' 1 := hhi 1
  have hne' : lo' ≠ hi' := fun h => by
    rw [h] at hl0
    omega
  have pe₁ := perimeterPos_nonneg he₁.1
  have pe₁' := perimeterPos_lt hne' he₁.1
  have pe₂ := perimeterPos_nonneg he₂.1
  have pe₂' := perimeterPos_lt hne' he₂.1
  have pe₃ := perimeterPos_nonneg he₃.1
  have pe₃' := perimeterPos_lt hne' he₃.1
  have d₁₂ : perimeterPos lo' hi' e₁ ≠ perimeterPos lo' hi' e₂ := fun h => h₁₂ e₁
    γ₁.end_mem_support (perimeterPos_injOn lo' hi' he₁ he₂ h ▸ γ₂.end_mem_support)
  have d₁₃ : perimeterPos lo' hi' e₁ ≠ perimeterPos lo' hi' e₃ := fun h => h₁₃ e₁
    γ₁.end_mem_support (perimeterPos_injOn lo' hi' he₁ he₃ h ▸ γ₃.end_mem_support)
  have d₂₃ : perimeterPos lo' hi' e₂ ≠ perimeterPos lo' hi' e₃ := fun h => h₂₃ e₂
    γ₂.end_mem_support (perimeterPos_injOn lo' hi' he₂ he₃ h ▸ γ₃.end_mem_support)
  have h₂₁ : ∀ v ∈ γ₂.support, v ∉ γ₁.support := fun v hv h => h₁₂ v h hv
  have h₃₁ : ∀ v ∈ γ₃.support, v ∉ γ₁.support := fun v hv h => h₁₃ v h hv
  have h₃₂ : ∀ v ∈ γ₃.support, v ∉ γ₂.support := fun v hv h => h₂₃ v h hv
  have hγ₁' : ∀ v ∈ γ₁.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₁) :=
    fun v hv => ⟨(hγ₁ v hv).1, (hγ₁ v hv).2.1⟩
  have hγ₂' : ∀ v ∈ γ₂.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₂) :=
    fun v hv => ⟨(hγ₂ v hv).1, (hγ₂ v hv).2.1⟩
  have hγ₃' : ∀ v ∈ γ₃.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₃) :=
    fun v hv => ⟨(hγ₃ v hv).1, (hγ₃ v hv).2.1⟩
  by_contra hE
  -- one of the three gaps between consecutive ends is not empty
  by_cases g₁ : perimeterPos lo' hi' e₃ + 1 = perimeterPos lo' hi' e₂ ∨
      (perimeterPos lo' hi' e₂ = 0 ∧
        perimeterPos lo' hi' e₃ = 2 * (hi' 0 - lo' 0) + 2 * (hi' 1 - lo' 1) - 1)
  · by_cases g₂ : perimeterPos lo' hi' e₁ + 1 = perimeterPos lo' hi' e₃ ∨
        (perimeterPos lo' hi' e₃ = 0 ∧
          perimeterPos lo' hi' e₁ = 2 * (hi' 0 - lo' 0) + 2 * (hi' 1 - lo' 1) - 1)
    · by_cases g₃ : perimeterPos lo' hi' e₂ + 1 = perimeterPos lo' hi' e₁ ∨
          (perimeterPos lo' hi' e₁ = 0 ∧
            perimeterPos lo' hi' e₂ = 2 * (hi' 0 - lo' 0) + 2 * (hi' 1 - lo' 1) - 1)
      · omega
      · exact not_cyclicallyOrdered_of_cyclicallyOrdered h₀ h₁ hlo hhi γ₃ γ₁ γ₂ hs₃ hs₁ hs₂ he₃
          he₁ he₂ hγ₃' hγ₁ hγ₂' h₃₁ h₃₂ h₁₂ (by omega) g₃ (by omega)
    · exact not_cyclicallyOrdered_of_cyclicallyOrdered h₀ h₁ hlo hhi γ₂ γ₃ γ₁ hs₂ hs₃ hs₁ he₂
        he₃ he₁ hγ₂' hγ₃ hγ₁' h₂₃ h₂₁ h₃₁ (by omega) g₂ (by omega)
  · exact not_cyclicallyOrdered_of_cyclicallyOrdered h₀ h₁ hlo hhi γ₁ γ₂ γ₃ hs₁ hs₂ hs₃ he₁ he₂
      he₃ hγ₁' hγ₂ hγ₃' h₁₂ h₁₃ h₂₃ hs g₁ (by omega)

/-- **Order invariance of three arms, first-hit form.** Let `I = Icc lo hi` (positive width and
height) lie inside the interior of `O = Icc lo' hi'`, and let `γ₁, γ₂, γ₃` be pairwise
vertex-disjoint walks in `O` from points `sᵢ` of `∂I` to points `eᵢ` of `∂O`, each meeting `I` only
at its first vertex and `∂O` only at its last vertex (for instance, arms stopped at their first
hit of `∂O`). Then the starts are in counterclockwise order on `∂I` exactly when the ends are in
counterclockwise order on `∂O`.

The hypotheses describe three arms; a structure for arms is an interface matter. -/
theorem cyclicallyOrdered_firstHit_iff {lo hi lo' hi' : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hlo : lo' + 1 ≤ lo) (hhi : hi + 1 ≤ hi')
    {s₁ s₂ s₃ e₁ e₂ e₃ : LatticeSite 2} (γ₁ : (zdGraph 2).Walk s₁ e₁)
    (γ₂ : (zdGraph 2).Walk s₂ e₂) (γ₃ : (zdGraph 2).Walk s₃ e₃)
    (hs₁ : s₁ ∈ boxBoundary lo hi) (hs₂ : s₂ ∈ boxBoundary lo hi)
    (hs₃ : s₃ ∈ boxBoundary lo hi) (he₁ : e₁ ∈ boxBoundary lo' hi')
    (he₂ : e₂ ∈ boxBoundary lo' hi') (he₃ : e₃ ∈ boxBoundary lo' hi')
    (hγ₁ : ∀ v ∈ γ₁.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₁) ∧
      (v ∈ boxBoundary lo' hi' → v = e₁))
    (hγ₂ : ∀ v ∈ γ₂.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₂) ∧
      (v ∈ boxBoundary lo' hi' → v = e₂))
    (hγ₃ : ∀ v ∈ γ₃.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₃) ∧
      (v ∈ boxBoundary lo' hi' → v = e₃))
    (h₁₂ : ∀ v ∈ γ₁.support, v ∉ γ₂.support) (h₁₃ : ∀ v ∈ γ₁.support, v ∉ γ₃.support)
    (h₂₃ : ∀ v ∈ γ₂.support, v ∉ γ₃.support) :
    ((perimeterPos lo hi s₁ < perimeterPos lo hi s₂ ∧
        perimeterPos lo hi s₂ < perimeterPos lo hi s₃) ∨
      (perimeterPos lo hi s₂ < perimeterPos lo hi s₃ ∧
        perimeterPos lo hi s₃ < perimeterPos lo hi s₁) ∨
      (perimeterPos lo hi s₃ < perimeterPos lo hi s₁ ∧
        perimeterPos lo hi s₁ < perimeterPos lo hi s₂)) ↔
      ((perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂ ∧
          perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃) ∨
        (perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃ ∧
          perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁) ∨
        (perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁ ∧
          perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂)) := by
  refine ⟨cyclicallyOrdered_firstHit h₀ h₁ hlo hhi γ₁ γ₂ γ₃ hs₁ hs₂ hs₃ he₁ he₂ he₃ hγ₁ hγ₂ hγ₃
    h₁₂ h₁₃ h₂₃, fun hE => ?_⟩
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have ps₁ := perimeterPos_nonneg hs₁.1
  have ps₂ := perimeterPos_nonneg hs₂.1
  have ps₃ := perimeterPos_nonneg hs₃.1
  have d₁₂ : perimeterPos lo hi s₁ ≠ perimeterPos lo hi s₂ := fun h => h₁₂ s₁
    γ₁.start_mem_support (perimeterPos_injOn lo hi hs₁ hs₂ h ▸ γ₂.start_mem_support)
  have d₁₃ : perimeterPos lo hi s₁ ≠ perimeterPos lo hi s₃ := fun h => h₁₃ s₁
    γ₁.start_mem_support (perimeterPos_injOn lo hi hs₁ hs₃ h ▸ γ₃.start_mem_support)
  have d₂₃ : perimeterPos lo hi s₂ ≠ perimeterPos lo hi s₃ := fun h => h₂₃ s₂
    γ₂.start_mem_support (perimeterPos_injOn lo hi hs₂ hs₃ h ▸ γ₃.start_mem_support)
  by_contra hS
  have := cyclicallyOrdered_firstHit h₀ h₁ hlo hhi γ₁ γ₃ γ₂ hs₁ hs₃ hs₂ he₁ he₃ he₂ hγ₁ hγ₃ hγ₂
    h₁₃ h₁₂ (fun v hv h => h₂₃ v h hv) (by omega)
  omega

/-- **Order invariance, one direction.** See `cyclicallyOrdered_end_iff`. -/
theorem cyclicallyOrdered_end {lo hi lo' hi' : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hlo : lo' + 1 ≤ lo) (hhi : hi + 1 ≤ hi')
    {s₁ s₂ s₃ e₁ e₂ e₃ : LatticeSite 2} (γ₁ : (zdGraph 2).Walk s₁ e₁)
    (γ₂ : (zdGraph 2).Walk s₂ e₂) (γ₃ : (zdGraph 2).Walk s₃ e₃)
    (hs₁ : s₁ ∈ boxBoundary lo hi) (hs₂ : s₂ ∈ boxBoundary lo hi)
    (hs₃ : s₃ ∈ boxBoundary lo hi) (he₁ : e₁ ∈ boxBoundary lo' hi')
    (he₂ : e₂ ∈ boxBoundary lo' hi') (he₃ : e₃ ∈ boxBoundary lo' hi')
    (hγ₁ : ∀ v ∈ γ₁.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₁))
    (hγ₂ : ∀ v ∈ γ₂.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₂))
    (hγ₃ : ∀ v ∈ γ₃.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₃))
    (h₁₂ : ∀ v ∈ γ₁.support, v ∉ γ₂.support) (h₁₃ : ∀ v ∈ γ₁.support, v ∉ γ₃.support)
    (h₂₃ : ∀ v ∈ γ₂.support, v ∉ γ₃.support)
    (hs : ((perimeterPos lo hi s₁ < perimeterPos lo hi s₂ ∧
          perimeterPos lo hi s₂ < perimeterPos lo hi s₃) ∨
        (perimeterPos lo hi s₂ < perimeterPos lo hi s₃ ∧
          perimeterPos lo hi s₃ < perimeterPos lo hi s₁) ∨
        (perimeterPos lo hi s₃ < perimeterPos lo hi s₁ ∧
          perimeterPos lo hi s₁ < perimeterPos lo hi s₂))) :
    ((perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂ ∧
        perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃) ∨
      (perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃ ∧
        perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁) ∨
      (perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁ ∧
        perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂)) := by
  have hl0 : lo' 0 + 1 ≤ lo 0 := hlo 0
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have hne' : lo' ≠ hi' := fun h => by
    have hh0 : hi 0 + 1 ≤ hi' 0 := hhi 0
    rw [h] at hl0
    omega
  have ps₁ := perimeterPos_nonneg hs₁.1
  have ps₂ := perimeterPos_nonneg hs₂.1
  have ps₃ := perimeterPos_nonneg hs₃.1
  have d₁₂ : s₁ ≠ s₂ := fun h => h₁₂ s₁ γ₁.start_mem_support (h ▸ γ₂.start_mem_support)
  have d₁₃ : s₁ ≠ s₃ := fun h => h₁₃ s₁ γ₁.start_mem_support (h ▸ γ₃.start_mem_support)
  have d₂₃ : s₂ ≠ s₃ := fun h => h₂₃ s₂ γ₂.start_mem_support (h ▸ γ₃.start_mem_support)
  -- the arms up to their first hits of `∂O`, and the rest
  obtain ⟨h₁', hh₁, π₁, σ₁, hπσ₁, hπ₁⟩ := γ₁.exists_append_eq_of_mem he₁
  obtain ⟨h₂', hh₂, π₂, σ₂, hπσ₂, hπ₂⟩ := γ₂.exists_append_eq_of_mem he₂
  obtain ⟨h₃', hh₃, π₃, σ₃, hπσ₃, hπ₃⟩ := γ₃.exists_append_eq_of_mem he₃
  have sπ₁ : ∀ v ∈ π₁.support, v ∈ γ₁.support := fun v hv => by
    rw [← hπσ₁, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hv
  have sσ₁ : ∀ v ∈ σ₁.support, v ∈ γ₁.support := fun v hv => by
    rw [← hπσ₁, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  have sπ₂ : ∀ v ∈ π₂.support, v ∈ γ₂.support := fun v hv => by
    rw [← hπσ₂, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hv
  have sσ₂ : ∀ v ∈ σ₂.support, v ∈ γ₂.support := fun v hv => by
    rw [← hπσ₂, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  have sπ₃ : ∀ v ∈ π₃.support, v ∈ γ₃.support := fun v hv => by
    rw [← hπσ₃, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hv
  have sσ₃ : ∀ v ∈ σ₃.support, v ∈ γ₃.support := fun v hv => by
    rw [← hπσ₃, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  -- the first hits are in counterclockwise order
  have hH := cyclicallyOrdered_firstHit h₀ h₁ hlo hhi π₁ π₂ π₃ hs₁ hs₂ hs₃ hh₁ hh₂ hh₃
    (fun v hv => ⟨(hγ₁ v (sπ₁ v hv)).1, (hγ₁ v (sπ₁ v hv)).2, hπ₁ v hv⟩)
    (fun v hv => ⟨(hγ₂ v (sπ₂ v hv)).1, (hγ₂ v (sπ₂ v hv)).2, hπ₂ v hv⟩)
    (fun v hv => ⟨(hγ₃ v (sπ₃ v hv)).1, (hγ₃ v (sπ₃ v hv)).2, hπ₃ v hv⟩)
    (fun v hv h => h₁₂ v (sπ₁ v hv) (sπ₂ v h)) (fun v hv h => h₁₃ v (sπ₁ v hv) (sπ₃ v h))
    (fun v hv h => h₂₃ v (sπ₂ v hv) (sπ₃ v h)) hs
  -- arcs of `∂I` between the starts
  obtain ⟨a₂₃, ha₂₃⟩ := exists_walk_boundary_of_ne h₀ h₁ hs₂ hs₃ d₂₃
  obtain ⟨a₃₁, ha₃₁⟩ := exists_walk_boundary_of_ne h₀ h₁ hs₃ hs₁ d₁₃.symm
  obtain ⟨a₁₂, ha₁₂⟩ := exists_walk_boundary_of_ne h₀ h₁ hs₁ hs₂ d₁₂
  have hIO : ∀ v ∈ Icc lo hi, v ∈ Icc lo' hi' := fun v hv => by
    have hh0 : hi 0 + 1 ≤ hi' 0 := hhi 0
    have hl1 : lo' 1 + 1 ≤ lo 1 := hlo 1
    have hh1 : hi 1 + 1 ≤ hi' 1 := hhi 1
    rw [mem_Icc_two_iff] at hv ⊢
    omega
  -- a cross-cut `π₂⁻¹ · arc · ρ` lies in `O`
  have hcut : ∀ {x y z w : LatticeSite 2} (π : (zdGraph 2).Walk x y) (α : (zdGraph 2).Walk x z)
      (ρ : (zdGraph 2).Walk z w), (∀ v ∈ π.support, v ∈ Icc lo' hi') →
      (∀ v ∈ α.support, v ∈ boxBoundary lo hi) → (∀ v ∈ ρ.support, v ∈ Icc lo' hi') →
      ∀ v ∈ (π.reverse.append (α.append ρ)).support, v ∈ Icc lo' hi' := by
    intro x y z w π α ρ hπ hα hρ v hv
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    rcases hv with hv | hv | hv
    exacts [hπ v hv, hIO v (hα v hv).1, hρ v hv]
  -- exchange the first hits for the ends, one arm at a time
  have hE₁ := cyclicallyOrdered_of_cyclicallyOrdered_of_disjoint
    (π₂.reverse.append (a₂₃.append π₃)) σ₁
    (hcut π₂ a₂₃ π₃ (fun v hv => (hγ₂ v (sπ₂ v hv)).1) (fun v hv => (ha₂₃ v hv).1)
      (fun v hv => (hγ₃ v (sπ₃ v hv)).1)) (fun v hv => (hγ₁ v (sσ₁ v hv)).1) hh₂ hh₃ hh₁ he₁
    (fun v hv hv' => by
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      rcases hv with hv | hv | hv
      · exact h₁₂ v (sσ₁ v hv') (sπ₂ v hv)
      · obtain ⟨hvb, hv⟩ := ha₂₃ v hv
        have := (hγ₁ v (sσ₁ v hv')).2 hvb.1
        subst this
        rcases hv with h | h | h
        · exact d₁₂ h
        · exact d₁₃ h
        · omega
      · exact h₁₃ v (sσ₁ v hv') (sπ₃ v hv)) (by omega)
  have hE₂ := cyclicallyOrdered_of_cyclicallyOrdered_of_disjoint
    (π₃.reverse.append (a₃₁.append γ₁)) σ₂
    (hcut π₃ a₃₁ γ₁ (fun v hv => (hγ₃ v (sπ₃ v hv)).1) (fun v hv => (ha₃₁ v hv).1)
      (fun v hv => (hγ₁ v hv).1)) (fun v hv => (hγ₂ v (sσ₂ v hv)).1) hh₃ he₁ hh₂ he₂
    (fun v hv hv' => by
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      rcases hv with hv | hv | hv
      · exact h₂₃ v (sσ₂ v hv') (sπ₃ v hv)
      · obtain ⟨hvb, hv⟩ := ha₃₁ v hv
        have := (hγ₂ v (sσ₂ v hv')).2 hvb.1
        subst this
        rcases hv with h | h | h
        · exact d₂₃ h
        · exact d₁₂ h.symm
        · omega
      · exact h₁₂ v hv (sσ₂ v hv')) (by omega)
  have hE₃ := cyclicallyOrdered_of_cyclicallyOrdered_of_disjoint
    (γ₁.reverse.append (a₁₂.append γ₂)) σ₃
    (hcut γ₁ a₁₂ γ₂ (fun v hv => (hγ₁ v hv).1) (fun v hv => (ha₁₂ v hv).1)
      (fun v hv => (hγ₂ v hv).1)) (fun v hv => (hγ₃ v (sσ₃ v hv)).1) he₁ he₂ hh₃ he₃
    (fun v hv hv' => by
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      rcases hv with hv | hv | hv
      · exact h₁₃ v hv (sσ₃ v hv')
      · obtain ⟨hvb, hv⟩ := ha₁₂ v hv
        have := (hγ₃ v (sσ₃ v hv')).2 hvb.1
        subst this
        rcases hv with h | h | h
        · exact d₁₃ h.symm
        · exact d₂₃ h.symm
        · omega
      · exact h₂₃ v hv (sσ₃ v hv')) (by omega)
  omega

/-- **Order invariance of three arms.** Let `I = Icc lo hi` (positive width and height) lie
inside the interior of `O = Icc lo' hi'`, and let `γ₁, γ₂, γ₃` be pairwise vertex-disjoint walks in
`O` from points `sᵢ` of `∂I` to points `eᵢ` of `∂O`, each meeting `I` only at its first vertex (arms
crossing the annulus between `∂I` and `∂O`; they may touch `∂O` before their end). Then the starts
are in counterclockwise order on `∂I` exactly when the ends are in counterclockwise order on `∂O`.

The hypotheses describe three arms; a structure for arms is an interface matter. -/
theorem cyclicallyOrdered_end_iff {lo hi lo' hi' : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hlo : lo' + 1 ≤ lo) (hhi : hi + 1 ≤ hi')
    {s₁ s₂ s₃ e₁ e₂ e₃ : LatticeSite 2} (γ₁ : (zdGraph 2).Walk s₁ e₁)
    (γ₂ : (zdGraph 2).Walk s₂ e₂) (γ₃ : (zdGraph 2).Walk s₃ e₃)
    (hs₁ : s₁ ∈ boxBoundary lo hi) (hs₂ : s₂ ∈ boxBoundary lo hi)
    (hs₃ : s₃ ∈ boxBoundary lo hi) (he₁ : e₁ ∈ boxBoundary lo' hi')
    (he₂ : e₂ ∈ boxBoundary lo' hi') (he₃ : e₃ ∈ boxBoundary lo' hi')
    (hγ₁ : ∀ v ∈ γ₁.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₁))
    (hγ₂ : ∀ v ∈ γ₂.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₂))
    (hγ₃ : ∀ v ∈ γ₃.support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s₃))
    (h₁₂ : ∀ v ∈ γ₁.support, v ∉ γ₂.support) (h₁₃ : ∀ v ∈ γ₁.support, v ∉ γ₃.support)
    (h₂₃ : ∀ v ∈ γ₂.support, v ∉ γ₃.support) :
    ((perimeterPos lo hi s₁ < perimeterPos lo hi s₂ ∧
        perimeterPos lo hi s₂ < perimeterPos lo hi s₃) ∨
      (perimeterPos lo hi s₂ < perimeterPos lo hi s₃ ∧
        perimeterPos lo hi s₃ < perimeterPos lo hi s₁) ∨
      (perimeterPos lo hi s₃ < perimeterPos lo hi s₁ ∧
        perimeterPos lo hi s₁ < perimeterPos lo hi s₂)) ↔
      ((perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂ ∧
          perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃) ∨
        (perimeterPos lo' hi' e₂ < perimeterPos lo' hi' e₃ ∧
          perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁) ∨
        (perimeterPos lo' hi' e₃ < perimeterPos lo' hi' e₁ ∧
          perimeterPos lo' hi' e₁ < perimeterPos lo' hi' e₂)) := by
  refine ⟨cyclicallyOrdered_end h₀ h₁ hlo hhi γ₁ γ₂ γ₃ hs₁ hs₂ hs₃ he₁ he₂ he₃ hγ₁ hγ₂ hγ₃
    h₁₂ h₁₃ h₂₃, fun hE => ?_⟩
  have ps₁ := perimeterPos_nonneg hs₁.1
  have ps₂ := perimeterPos_nonneg hs₂.1
  have ps₃ := perimeterPos_nonneg hs₃.1
  have d₁₂ : perimeterPos lo hi s₁ ≠ perimeterPos lo hi s₂ := fun h => h₁₂ s₁
    γ₁.start_mem_support (perimeterPos_injOn lo hi hs₁ hs₂ h ▸ γ₂.start_mem_support)
  have d₁₃ : perimeterPos lo hi s₁ ≠ perimeterPos lo hi s₃ := fun h => h₁₃ s₁
    γ₁.start_mem_support (perimeterPos_injOn lo hi hs₁ hs₃ h ▸ γ₃.start_mem_support)
  have d₂₃ : perimeterPos lo hi s₂ ≠ perimeterPos lo hi s₃ := fun h => h₂₃ s₂
    γ₂.start_mem_support (perimeterPos_injOn lo hi hs₂ hs₃ h ▸ γ₃.start_mem_support)
  by_contra hS
  have := cyclicallyOrdered_end h₀ h₁ hlo hhi γ₁ γ₃ γ₂ hs₁ hs₃ hs₂ he₁ he₃ he₂ hγ₁ hγ₃ hγ₂
    h₁₃ h₁₂ (fun v hv h => h₂₃ v h hv) (by omega)
  omega

/-- **Order invariance of a family of arms.** Let `I = Icc lo hi` (positive width and height)
lie inside the interior of `O = Icc lo' hi'`, and let `γ i` (`i : Fin j`) be pairwise
vertex-disjoint walks in `O` from points `s i` of `∂I` to points `e i` of `∂O`, each meeting `I`
only at its first vertex. Then for all `i, k, l` the starts `s i, s k, s l` are in
counterclockwise order on `∂I` exactly when the ends `e i, e k, e l` are in counterclockwise
order on `∂O`: the arms have the same cyclic order at both ends. Applied to the arms stopped at
their first hits of the boundary of an intermediate box, the same holds at those first hits. -/
theorem cyclicallyOrdered_end_iff_of_pairwise_disjoint {lo hi lo' hi' : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) (hlo : lo' + 1 ≤ lo) (hhi : hi + 1 ≤ hi') {j : ℕ}
    {s e : Fin j → LatticeSite 2} (γ : ∀ i, (zdGraph 2).Walk (s i) (e i))
    (hs : ∀ i, s i ∈ boxBoundary lo hi) (he : ∀ i, e i ∈ boxBoundary lo' hi')
    (hγ : ∀ i, ∀ v ∈ (γ i).support, v ∈ Icc lo' hi' ∧ (v ∈ Icc lo hi → v = s i))
    (hdisj : ∀ i k, i ≠ k → ∀ v ∈ (γ i).support, v ∉ (γ k).support) (i k l : Fin j) :
    ((perimeterPos lo hi (s i) < perimeterPos lo hi (s k) ∧
        perimeterPos lo hi (s k) < perimeterPos lo hi (s l)) ∨
      (perimeterPos lo hi (s k) < perimeterPos lo hi (s l) ∧
        perimeterPos lo hi (s l) < perimeterPos lo hi (s i)) ∨
      (perimeterPos lo hi (s l) < perimeterPos lo hi (s i) ∧
        perimeterPos lo hi (s i) < perimeterPos lo hi (s k))) ↔
      ((perimeterPos lo' hi' (e i) < perimeterPos lo' hi' (e k) ∧
          perimeterPos lo' hi' (e k) < perimeterPos lo' hi' (e l)) ∨
        (perimeterPos lo' hi' (e k) < perimeterPos lo' hi' (e l) ∧
          perimeterPos lo' hi' (e l) < perimeterPos lo' hi' (e i)) ∨
        (perimeterPos lo' hi' (e l) < perimeterPos lo' hi' (e i) ∧
          perimeterPos lo' hi' (e i) < perimeterPos lo' hi' (e k))) := by
  by_cases hik : i = k
  · subst hik
    constructor <;> intro h <;> omega
  by_cases hil : i = l
  · subst hil
    constructor <;> intro h <;> omega
  by_cases hkl : k = l
  · subst hkl
    constructor <;> intro h <;> omega
  exact cyclicallyOrdered_end_iff h₀ h₁ hlo hhi (γ i) (γ k) (γ l) (hs i) (hs k) (hs l) (he i)
    (he k) (he l) (hγ i) (hγ k) (hγ l) (hdisj i k hik) (hdisj i l hil) (hdisj k l hkl)

end PercLib.Models.Planar
