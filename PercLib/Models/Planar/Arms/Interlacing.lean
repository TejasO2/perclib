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
# Interlacing and pivotal edges on the square lattice

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

## Implementation notes

* The interlacing hypotheses are written with explicit inequalities between positions: mathlib's
  cyclic betweenness `sbtw` on `ℤ` needs `LinearOrder.toCircularOrder`, which is not an instance.
  Each form allows both orientations of the first pair.
* The mixed and dual–dual forms, like quad duality, assume a box of positive width and height:
  their dual arcs are the faces outside the box at a boundary corner.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

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

end PercLib.Models.Planar
