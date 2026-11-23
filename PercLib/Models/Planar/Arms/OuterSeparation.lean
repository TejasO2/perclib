/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-23. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, proof of Theorem 11 (separation of the arms at the
outer boundary with Lemma 15 on strips along the sides).
-/
module

public import PercLib.Models.Planar.Arms.Sectors
public import PercLib.Models.Planar.Arms.Separation.Defs
public import PercLib.Models.Planar.Arms.SeparationSides
public import PercLib.Percolation.Bond.CrossEdge

/-!
# Separation of arms at the outer boundary of an annulus

The outer step of Nolin's proof of the separation theorem (Theorem 11), for colour sequences
without packs (no two cyclically consecutive arms of the same colour, or at most one arm). Let the
`j`-arm event from `B_r(z)` to the boundary of `B_R(z)`, `R = 2N + 1`, `r < N`, occur, and let the
four strips of height `N` along the sides of `B_R(z)` have the separation property of Lemma 15
(`exists_law_separable_ge_sides`). On each side, the final crossings of the arms landing there
(their parts after the last visit to the inner row of the strip, `IsArm.exists_append_eq_top` and
its analogues) are crossings of the strip. Lemma 15 reroutes them, and each arm followed by its
rerouted final crossing is again an arm with the same inner position (`IsArm.append_right`), whose
end is well separated and carries a fence (`exists_reroute_top`, `exists_reroute_right`,
`exists_reroute_bottom`, `exists_reroute_left`). Without packs the barrier
(`ArmsDisjoint.of_innerPos_eq`, `sbtw_landingPos_of_innerPos_eq`) makes the new family disjoint and
in the old order, also across the sides and at the corners. The landing positions are read off the
ends (`IsArm.landingPos_eq_of_top` and its analogues), so the new ends are separated in landing
positions and away from the corners.

The intersection of the four strip events is an event of probability at least `1 - δ`, determined
by the edges of the annulus `B_{2R}(z) \ B_N(z)`, on which the arms of every `j`-arm event from
`B_r(z)`, `r < N`, can be separated (`exists_separating_event`; the separated event is
`outerSeparatedArmEvent` with separation `4 √η N` and fences of length `2 ⌊η N⌋` and depth
`⌊√η N⌋`). The `j`-arm event to the boundary of `B_N(z)` depends only on edges inside
`B_N(z)`, so the two are independent, which gives the outer step
`P(A(r, R), not separated) ≤ δ P(A(r, N))` (`exists_law_multiArmEvent_inter_not_separated_le`).

## Main results

* `SimpleGraph.Walk.IsCrossing.append_right`, `IsArm.append_right`: replacing the end of a crossing,
  of an arm.
* `mem_image_dualEdge_of_forall_mem_edges`: the dual edges of a walk of faces cross edges of a box.
* `PercLib.Percolation.Bond.finite_setOf_forall_mem`,
  `PercLib.Percolation.Bond.image_sym2Map_mem_iff_of_inter_eq`: events determined by finitely many
  pairs, moved by a bijection.
* `IsArm.landingPos_eq_of_top`, `IsArm.landingPos_eq_of_right`, `IsArm.landingPos_eq_of_bottom`,
  `IsArm.landingPos_eq_of_left`, `IsArm.end_mem_sides`: landing on the four sides.
* `IsArm.exists_append_eq_top` (and `_right`, `_bottom`, `_left`): the final crossing of an arm in
  the strip along its side.
* `exists_reroute_top` (and `_right`, `_bottom`, `_left`): rerouting the arms landing on one side.
* `exists_separating_event`: **the outer separation step, event form.**
* `exists_law_multiArmEvent_inter_not_separated_le`: **the outer separation step.**
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

/-! ### Replacing the end of a crossing -/

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {S T : Set V}

/-- **Replacing the end of a crossing.** If `q.append s` crosses from `S` out of `T`, so does
`q.append s'` for every walk `s'` from the same vertex that avoids `S`, stays in `T` before its last
vertex and ends outside `T`. -/
theorem IsCrossing.append_right {u x v v' : V} {q : G.Walk u x} {s : G.Walk x v}
    {s' : G.Walk x v'} (h : (q.append s).IsCrossing S T) (hS : ∀ w ∈ s'.support, w ∉ S)
    (hT : ∀ w ∈ s'.support.dropLast, w ∈ T) (hv : v' ∉ T) : (q.append s').IsCrossing S T := by
  refine ⟨h.start_mem, fun w hw => ?_, hv, fun w hw => ?_⟩
  · rw [tail_support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.notMem_of_mem_tail w (by
        rw [tail_support_append]
        exact List.mem_append_left _ hw)
    · exact hS w (List.mem_of_mem_tail hw)
  · rw [support_append_eq_support_dropLast_append,
      List.dropLast_append_of_ne_nil (support_ne_nil s'), List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.mem_of_mem_dropLast w (by
        rw [support_append_eq_support_dropLast_append,
          List.dropLast_append_of_ne_nil (support_ne_nil s)]
        exact List.mem_append_left _ hw)
    · exact hT w hw

end SimpleGraph.Walk

/-! ### Events determined by finitely many pairs, moved by a bijection -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The pairs with both ends in a finite set form a finite set. -/
theorem finite_setOf_forall_mem {S : Set V} (hS : S.Finite) :
    Set.Finite {e : Sym2 V | ∀ v ∈ e, v ∈ S} := by
  refine Set.Finite.subset ((hS.prod hS).image fun p : V × V => s(p.1, p.2)) ?_
  intro e he
  induction e using Sym2.ind with
  | h u v => exact ⟨(u, v), ⟨he u (Sym2.mem_mk_left u v), he v (Sym2.mem_mk_right u v)⟩, rfl⟩

/-- **Determination through a bijection.** If an event `S` is determined by the pairs in `W`, the
event that the configuration moved by `σ` lies in `S` is determined by the pairs in the preimage
`σ⁻¹ W`. -/
theorem image_sym2Map_mem_iff_of_inter_eq (σ : V ≃ V) {S : Set (Config V)} {W : Set (Sym2 V)}
    (hS : ∀ ω ω' : Config V, ω ∩ W = ω' ∩ W → (ω ∈ S ↔ ω' ∈ S)) {ω ω' : Config V}
    (h : ω ∩ Sym2.map σ.symm '' W = ω' ∩ Sym2.map σ.symm '' W) :
    Sym2.map σ '' ω ∈ S ↔ Sym2.map σ '' ω' ∈ S := by
  refine hS _ _ (Set.ext fun e => ?_)
  have hW : e ∈ W ↔ Sym2.map σ.symm e ∈ Sym2.map σ.symm '' W :=
    ((Sym2.map.injective σ.symm.injective).mem_set_image).symm
  have := congrArg (Sym2.map σ.symm e ∈ ·) h
  simp only [mem_inter_iff, eq_iff_iff] at this
  rw [mem_inter_iff, mem_inter_iff, mem_image_sym2Map_iff, mem_image_sym2Map_iff, hW]
  exact this

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}

/-- **Replacing the end of an arm.** If `q.append s` is an arm of colour `c`, so is `q.append s'`
for every walk `s'` of that colour from the same vertex (face) that avoids `B_r(z)` (the faces
touching it), stays in the interior of the outer box (in its faces) before its end and ends
outside. -/
theorem IsArm.append_right {c : Bool} {a x b b' : LatticeSite 2} {q : (zdGraph 2).Walk a x}
    {s : (zdGraph 2).Walk x b} {s' : (zdGraph 2).Walk x b'} (h : IsArm ω c z r lo hi (q.append s))
    (hS : ∀ w ∈ s'.support, w ∉ cond c (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)))
    (hT : ∀ w ∈ s'.support.dropLast, w ∈ cond c (Icc (lo + 1) (hi - 1)) (Icc lo (hi - 1)))
    (hb : b' ∉ cond c (Icc (lo + 1) (hi - 1)) (Icc lo (hi - 1)))
    (hE : ∀ e ∈ s'.edges, e ∈ cond c ω (dualConfig ω)) : IsArm ω c z r lo hi (q.append s') := by
  have hq : ∀ e ∈ q.edges, e ∈ (q.append s).edges := fun e he => by
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ he
  cases c
  · have h₁ : IsDualArm ω z r lo hi (q.append s) := h
    refine ⟨h₁.isCrossing.append_right hS hT hb, fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact h₁.mem_of_mem_edges e (hq e he)
    · exact hE e he
  · have h₁ : IsOpenArm ω z r lo hi (q.append s) := h
    refine ⟨h₁.isCrossing.append_right hS hT hb, fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact h₁.mem_of_mem_edges e (hq e he)
    · exact hE e he

/-- **Dual edges crossing the edges of a box.** Every dual edge `{x, y}` of a walk of faces
crosses an edge of `ℤ²` with both ends in `Icc lo hi` as soon as, in each coordinate, one of the
two faces is at least `lo` and one is at most `hi - 1`: the edge crossed by `{x, y}` lies in the
closed unit squares of both faces. -/
theorem mem_image_dualEdge_of_forall_mem_edges {a b : LatticeSite 2} (p : (zdGraph 2).Walk a b)
    {lo hi : LatticeSite 2}
    (h : ∀ x y, s(x, y) ∈ p.edges → ∀ i,
      (lo i ≤ x i ∨ lo i ≤ y i) ∧ (x i + 1 ≤ hi i ∨ y i + 1 ≤ hi i))
    {e : Sym2 (LatticeSite 2)} (he : e ∈ p.edges) :
    e ∈ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} := by
  obtain ⟨x, y, rfl, -, -, -⟩ := exists_ne_of_mem_edges p he
  have heL := p.edges_subset_edgeSet he
  refine ⟨Sym2.map (· + 1) (dualEdge s(x, y)),
    ⟨map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet heL), fun w hw => ?_⟩,
    dualEdge_map_add_one_dualEdge heL⟩
  have h₁ := le_of_mem_map_add_one_dualEdge heL (Sym2.mem_mk_left x y) hw
  have h₂ := le_of_mem_map_add_one_dualEdge heL (Sym2.mem_mk_right x y) hw
  have h₀ := h x y he 0
  have h₁' := h x y he 1
  rw [mem_Icc_two_iff]
  omega

/-! ### Landing positions on the four sides -/

/-- The box `B_r(z)` lies in the interior of `B_R(z)` when `r < R`. -/
theorem Icc_subset_Icc_add_one_sub_one {R : ℕ} (hrR : r < R) :
    Icc (z - r) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) := by
  refine Icc_subset_Icc ?_ ?_ <;> intro i <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] <;> omega

/-- The last two vertices (faces) of an arm to `B_R(z)`, in coordinates: the last but one lies in
the interior (in the faces of the box), is adjacent to the last, and the last vertex lies on the
box (the last face outside its faces). -/
theorem IsArm.penultimate_mem {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R) :
    (γ.penultimate 0 = b 0 ∧ (γ.penultimate 1 + 1 = b 1 ∨ b 1 + 1 = γ.penultimate 1) ∨
      γ.penultimate 1 = b 1 ∧ (γ.penultimate 0 + 1 = b 0 ∨ b 0 + 1 = γ.penultimate 0)) ∧
    cond c
      (z 0 - R + 1 ≤ γ.penultimate 0 ∧ γ.penultimate 0 ≤ z 0 + R - 1 ∧
        z 1 - R + 1 ≤ γ.penultimate 1 ∧ γ.penultimate 1 ≤ z 1 + R - 1 ∧
        ¬(z 0 - R + 1 ≤ b 0 ∧ b 0 ≤ z 0 + R - 1 ∧ z 1 - R + 1 ≤ b 1 ∧ b 1 ≤ z 1 + R - 1))
      (z 0 - R ≤ γ.penultimate 0 ∧ γ.penultimate 0 ≤ z 0 + R - 1 ∧
        z 1 - R ≤ γ.penultimate 1 ∧ γ.penultimate 1 ≤ z 1 + R - 1 ∧
        ¬(z 0 - R ≤ b 0 ∧ b 0 ≤ z 0 + R - 1 ∧ z 1 - R ≤ b 1 ∧ b 1 ≤ z 1 + R - 1)) := by
  have hne := h.not_nil (Icc_subset_Icc_add_one_sub_one hrR)
  refine ⟨(zdGraph_two_adj_iff _ _).1 (γ.adj_penultimate hne), ?_⟩
  cases c
  · have h' : IsDualArm ω z r (z - R) (z + R) γ := h
    have hp := h'.isCrossing.penultimate_mem hne
    have hb := h'.isCrossing.end_notMem
    rw [mem_Icc_two_iff] at hp hb
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hp hb
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hb⟩
  · have h' : IsOpenArm ω z r (z - R) (z + R) γ := h
    have hp := h'.isCrossing.penultimate_mem hne
    have hb := h'.isCrossing.end_notMem
    rw [mem_Icc_two_iff] at hp hb
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hp hb
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hb⟩

/-- **Landing on the top side.** An arm of colour `c` to `B_R(z)` ending on the top side
(`b₁ = z₁ + R`; `b` is the last vertex of an open arm or the last face of a dual arm) has landing
position `8R + 2 (z₀ + R) - (2 b₀ + [c = dual])`. -/
theorem IsArm.landingPos_eq_of_top {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R)
    (hb : b 1 = z 1 + R) :
    landingPos (z - R) (z + R) c γ = 8 * R + 2 * (z 0 + R) - (2 * b 0 + cond c 0 1) := by
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_false]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
      nsmul_eq_mul, Nat.cast_ofNat, Bool.cond_false] at hb ⊢
    split_ifs <;> omega
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_true]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Bool.cond_true] at hb ⊢
    split_ifs <;> omega

/-- **Landing on the right side.** An arm of colour `c` to `B_R(z)` ending on the right side
(`b₀ = z₀ + R`) has landing position `4R + (2 b₁ + [c = dual]) - 2 (z₁ - R)`. -/
theorem IsArm.landingPos_eq_of_right {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R)
    (hb : b 0 = z 0 + R) :
    landingPos (z - R) (z + R) c γ = 4 * R + (2 * b 1 + cond c 0 1) - 2 * (z 1 - R) := by
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_false]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
      nsmul_eq_mul, Nat.cast_ofNat, Bool.cond_false] at hb ⊢
    split_ifs <;> omega
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_true]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Bool.cond_true] at hb ⊢
    split_ifs <;> omega

/-- **Landing on the bottom side.** An arm of colour `c` to `B_R(z)` ending on the bottom side
(`b₁ = z₁ - R` for an open arm, `z₁ - R - 1` for a dual arm) has landing position
`(2 b₀ + [c = dual]) - 2 (z₀ - R)`. -/
theorem IsArm.landingPos_eq_of_bottom {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R)
    (hb : b 1 = z 1 - R - cond c 0 1) :
    landingPos (z - R) (z + R) c γ = 2 * b 0 + cond c 0 1 - 2 * (z 0 - R) := by
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_false]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
      nsmul_eq_mul, Nat.cast_ofNat, Bool.cond_false] at hb ⊢
    split_ifs <;> omega
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_true]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Bool.cond_true] at hb ⊢
    split_ifs <;> omega

/-- **Landing on the left side.** An arm of colour `c` to `B_R(z)` ending on the left side
(`b₀ = z₀ - R` for an open arm, `z₀ - R - 1` for a dual arm) has landing position
`12R + 2 (z₁ + R) - (2 b₁ + [c = dual])`. -/
theorem IsArm.landingPos_eq_of_left {c : Bool} {R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R)
    (hb : b 0 = z 0 - R - cond c 0 1) :
    landingPos (z - R) (z + R) c γ = 12 * R + 2 * (z 1 + R) - (2 * b 1 + cond c 0 1) := by
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_false]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
      nsmul_eq_mul, Nat.cast_ofNat, Bool.cond_false] at hb ⊢
    split_ifs <;> omega
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    rw [landingPos_true]
    unfold perimeterPos
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Bool.cond_true] at hb ⊢
    split_ifs <;> omega

/-! ### The top side: final crossings and rerouting -/

/-- **The final crossing of an arm landing on the top side.** An arm of colour `c` to `B_R(z)`
ending on the top side splits, at its last vertex (face) at or below the bottom row of the strip
of height `N` along the top side, into a nonempty first part and a crossing of that strip in the
sense of `exists_law_separable_ge_top`, when `r + N + 1 < R`. -/
theorem IsArm.exists_append_eq_top {c : Bool} {N R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrN : r + N + 1 < R)
    (hb : b 1 = z 1 + R) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧ ¬p.Nil ∧
      cond c
        (x 1 = z 1 + R - N ∧ b 1 = z 1 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 1 = z 1 + R - N - 1 ∧ b 1 = z 1 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2) ![z 0 + R, z 1 + R]}) := by
  have hrR : r < R := by omega
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  have hqe : ∀ {x : LatticeSite 2} {p : (zdGraph 2).Walk a x} {q : (zdGraph 2).Walk x b},
      p.append q = γ → ∀ e ∈ q.edges, e ∈ γ.edges := fun hpq e he => by
    rw [← hpq, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases c
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    have h' : IsDualArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | v 1 ≤ z 1 + R - N - 1}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv
        change v 1 ≤ _
        omega)
    have hx : x 1 ≤ z 1 + R - N - 1 := hq.start_mem
    have hqne : ¬q.Nil := fun hn => by
      have : x 1 = b 1 := congrArg (· 1) hn.eq
      omega
    have hsnd : ¬q.snd 1 ≤ z 1 + R - N - 1 := hq.snd_notMem hqne
    have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
    have hx' : x 1 = z 1 + R - N - 1 := by omega
    -- the faces of the final crossing
    have hbot : ∀ v ∈ q.support, z 1 + R - N - 1 ≤ v 1 ∧ (v 1 = z 1 + R - N - 1 → v = x) := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · exact ⟨hx'.ge, fun _ => rfl⟩
      · have : ¬v 1 ≤ z 1 + R - N - 1 := hq.notMem_of_mem_tail v hv
        exact ⟨by omega, fun h => absurd h.le this⟩
    have hT : ∀ v ∈ q.support, (z 0 - R ≤ v 0 ∧ v 0 ≤ z 0 + R - 1 ∧ v 1 ≤ z 1 + R - 1) ∨ v = b := by
      intro v hv
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        exact Or.inl ⟨hvT.1, hvT.2.1, hvT.2.2.2⟩
      · exact Or.inr (hq.eq_end_of_notMem hv hvT)
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
        ![z 0 + R - 1, z 1 + R] := by
      intro v hv
      have h₁ := (hbot v hv).1
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases hT v hv with h₂ | rfl
      · omega
      · omega
    have htop : ∀ v ∈ q.support, v 1 = z 1 + R → v = b := by
      intro v hv hv1
      rcases hT v hv with h₂ | h₂
      · omega
      · exact h₂
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => ⟨h'.mem_of_mem_edges e
      (hqe hpq e he), mem_image_dualEdge_of_forall_mem_edges q (fun x' y' he' i => ?_) he⟩⟩
    · have := congrArg (· 1) hn.eq
      have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at this ha
      omega
    · have hx'' := q.fst_mem_support_of_mem_edges he'
      have hy'' := q.snd_mem_support_of_mem_edges he'
      have hne : x' ≠ y' := (q.adj_of_mem_edges he').ne
      have bx := mem_Icc_two_iff.1 (hbox x' hx'')
      have bY := mem_Icc_two_iff.1 (hbox y' hy'')
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at bx bY
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        omega
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        refine ⟨?_, ?_⟩
        · by_contra hc
          exact hne (((hbot x' hx'').2 (by omega)).trans ((hbot y' hy'').2 (by omega)).symm)
        · by_contra hc
          exact hne ((htop x' hx'' (by omega)).trans (htop y' hy'' (by omega)).symm)
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    have h' : IsOpenArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | v 1 ≤ z 1 + R - N}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
        change v 1 ≤ _
        omega)
    have hx : x 1 ≤ z 1 + R - N := hq.start_mem
    have hx' : x 1 = z 1 + R - N := by
      by_cases hqne : q.Nil
      · have : x 1 = b 1 := congrArg (· 1) hqne.eq
        omega
      · have hsnd : ¬q.snd 1 ≤ z 1 + R - N := hq.snd_notMem hqne
        have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
        omega
    have hbot : ∀ v ∈ q.support, z 1 + R - N ≤ v 1 := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · exact hx'.ge
      · have : ¬v 1 ≤ z 1 + R - N := hq.notMem_of_mem_tail v hv
        omega
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
        ![z 0 + R - 1, z 1 + R] := by
      intro v hv
      have h₁ := hbot v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        omega
      · rw [hq.eq_end_of_notMem hv hvT]
        omega
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => h'.mem_of_mem_edges e
      (hqe hpq e he)⟩
    have := congrArg (· 1) hn.eq
    have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at this ha
    omega

/-- **Rerouting the arms landing on the top side.** Let `γ` be a disjoint family of arms to
`B_R(z)`, `R = 2N + 1`, `r < N`, and let the configuration have the separation property of
`exists_law_separable_ge_top` along the top side. Then the arms landing on the top side can be
replaced, each by an arm with the same colour, the same start and the same inner position (its first
part followed by a rerouted final crossing), whose landing positions `L i` are at least `4 √η N`
apart and in `[8R + 4 √η N, 12R - 4 √η N]`, and each of which carries a fence above its end `b'`:
a crossing of its colour from the left side to the right side of
`[b'₀ - ⌊η N⌋, b'₀ + ⌊η N⌋] × [b'₁, b'₁ + ⌊√η N⌋]` whose left end is joined in its colour to a
vertex of the new arm inside the ball of radius `⌊√η N⌋` around `b'`. -/
theorem exists_reroute_top {η : ℝ} {N R : ℕ} (hR : R = 2 * N + 1) (hr : r < N)
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = z 1 + R - N ∧ b i 1 = z 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = z 1 + R - N - 1 ∧ b i 1 = z 1 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2) ![z 0 + R, z 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = z 1 + R - N ∧ b' i 1 = z 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
              ![z 0 + R - 1, z 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = z 1 + R - N - 1 ∧ b' i 1 = z 1 + R ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
              ![z 0 + R - 1, z 1 + R]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2)
                ![z 0 + R, z 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ z 1 + R) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z 0 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, z 1 + R]
              ![b' i 0 + ⌊η * N⌋₊, z 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ) :
    ∃ L : Fin j → ℤ,
      (∀ i, b i 1 = z 1 + R → ∃ (b' : LatticeSite 2) (Γ : (zdGraph 2).Walk (a i) b'),
        IsArm ω (σ i) z r (z - R) (z + R) Γ ∧
        innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
        landingPos (z - R) (z + R) (σ i) Γ = L i ∧
        ∃ x ∈ Γ.support, ∃ l r' : LatticeSite 2,
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l ∧
          b' 1 = z 1 + R ∧ l 0 = b' 0 - ⌊η * N⌋₊ ∧ r' 0 = b' 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' 0 - ⌊η * N⌋₊, b' 1] ![b' 0 + ⌊η * N⌋₊, b' 1 + ⌊Real.sqrt η * N⌋₊]) l r') ∧
      (∀ i k, b i 1 = z 1 + R → b k 1 = z 1 + R → i ≠ k →
        4 * Real.sqrt η * N ≤ |((L i - L k : ℤ) : ℝ)|) ∧
      (∀ i, b i 1 = z 1 + R →
        8 * (R : ℝ) + 4 * Real.sqrt η * N ≤ L i ∧ (L i : ℝ) + 4 * Real.sqrt η * N ≤ 12 * R) := by
  classical
  have hext : ∀ i, b i 1 = z 1 + R → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x)
      (q : (zdGraph 2).Walk x (b i)), p.append q = γ i ∧ ¬p.Nil ∧
      cond (σ i)
        (x 1 = z 1 + R - N ∧ b i 1 = z 1 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R + 1, z 1 + R - N] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 1 = z 1 + R - N - 1 ∧ b i 1 = z 1 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 + R - N - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 + R]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 + R - N] : LatticeSite 2) ![z 0 + R, z 1 + R]}) :=
    fun i hi => (hγ i).exists_append_eq_top (by omega) hi
  choose x p q hpq hpne hq using hext
  -- the final crossings lie in the arms after their first vertex
  have htail : ∀ i hi, ∀ v ∈ (q i hi).support, v ∈ (γ i).support.tail := by
    intro i hi v hv
    rw [← hpq i hi, SimpleGraph.Walk.tail_support_append, List.mem_append]
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hv with rfl | hv
    · exact Or.inl (SimpleGraph.Walk.end_mem_tail_support (hpne i hi))
    · exact Or.inr hv
  obtain ⟨b'', γ'', H1, -, H3, H4, H5, H6⟩ := hω {i // b i 1 = z 1 + R} (fun i => σ i.1)
    (fun i => x i.1 i.2) (fun i => b i.1) (fun i => q i.1 i.2) (fun i => hq i.1 i.2)
    (fun i k hik hσ v hv hv' => by
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hv₁ := htail i.1 i.2 v hv
      have hv₂ := List.mem_of_mem_tail (htail k.1 k.2 v hv')
      cases h : σ i.1
      · exact hd.2 i.1 k.1 hne h (hσ.symm.trans h) v (List.mem_of_mem_tail hv₁) hv₂
      · exact hd.1 i.1 k.1 hne h (hσ.symm.trans h) v hv₁ hv₂)
  -- the doubled columns of the new ends
  set d : {i // b i 1 = z 1 + R} → ℤ := fun i => 2 * b'' i 0 + cond (σ i.1) 0 1 with hd_def
  refine ⟨fun i => if hi : b i 1 = z 1 + R then 8 * R + 2 * (z 0 + R) - d ⟨i, hi⟩ else 0,
    fun i hi => ?_, fun i k hi hk hik => ?_, fun i hi => ?_⟩
  · have h1 := H1 ⟨i, hi⟩
    have h3 := H3 ⟨i, hi⟩
    obtain ⟨y, hy, l, r', hl, hr', hlr, hyl⟩ := H6 ⟨i, hi⟩
    beta_reduce at h1 h3 hlr hyl
    -- the new final crossing fits the arm
    obtain ⟨hb1, hS, hT, hE⟩ : b'' ⟨i, hi⟩ 1 = z 1 + R ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support, w ∉ cond (σ i) (Icc (z - r) (z + r))
          (Icc (z - r - 1) (z + r))) ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support.dropLast, w ∈ cond (σ i) (Icc (z - R + 1) (z + R - 1))
          (Icc (z - R) (z + R - 1))) ∧
        (∀ e ∈ (γ'' ⟨i, hi⟩).edges, e ∈ cond (σ i) ω (dualConfig ω)) := by
      revert h1
      cases σ i
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, fun e he => (hE e he).1⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply, Pi.one_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, hE⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
    have hb : b'' ⟨i, hi⟩ ∉ cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
      cases σ i
      · intro h
        have := (mem_Icc_two_iff.1 h).2.2.2
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this
        omega
      · intro h
        have := (mem_Icc_two_iff.1 h).2.2.2
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this
        omega
    have hArm : IsArm ω (σ i) z r (z - R) (z + R) ((p i hi).append (γ'' ⟨i, hi⟩)) := by
      have h0 := hγ i
      rw [← hpq i hi] at h0
      exact h0.append_right hS hT hb hE
    refine ⟨b'' ⟨i, hi⟩, (p i hi).append (γ'' ⟨i, hi⟩), hArm, ?_, ?_, y, ?_, l, r', hyl, hb1, hl,
      hr', by rwa [hb1]⟩
    · rw [innerPos_append _ (hpne i hi)]
      conv_rhs => rw [← hpq i hi]
      rw [innerPos_append _ (hpne i hi)]
    · beta_reduce
      rw [dite_eq_left hi, hArm.landingPos_eq_of_top (by omega) hb1]
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hy
  · have h4 := H4 ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Subtype.val h))
    beta_reduce
    rw [dite_eq_left hi, dite_eq_left hk]
    have : (((8 * R + 2 * (z 0 + R) - d ⟨i, hi⟩) - (8 * R + 2 * (z 0 + R) - d ⟨k, hk⟩) : ℤ) : ℝ) =
        ((d ⟨k, hk⟩ : ℤ) : ℝ) - ((d ⟨i, hi⟩ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [this, abs_sub_comm]
    exact h4
  · obtain ⟨h₁, h₂⟩ := H5 ⟨i, hi⟩
    beta_reduce
    rw [dite_eq_left hi]
    change 4 * Real.sqrt η * N ≤ ((d ⟨i, hi⟩ - 2 * (z 0 - R) : ℤ) : ℝ) at h₁
    change 4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - d ⟨i, hi⟩ : ℤ) : ℝ) at h₂
    push_cast at h₁ h₂ ⊢
    constructor <;> linarith

/-- **The final crossing of an arm landing on the right side.** An arm of colour `c` to `B_R(z)`
ending on the right side splits, at its last vertex (face) at or left of the inner column of the
strip of width `N` along the right side, into a nonempty first part and a crossing of that strip in
the sense of `separable_right_of_top`, when `r + N + 1 < R`. -/
theorem IsArm.exists_append_eq_right {c : Bool} {N R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrN : r + N + 1 < R)
    (hb : b 0 = z 0 + R) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧ ¬p.Nil ∧
      cond c
        (x 0 = z 0 + R - N ∧ b 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 + R - N - 1 ∧ b 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]}) := by
  have hrR : r < R := by omega
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  have hqe : ∀ {x : LatticeSite 2} {p : (zdGraph 2).Walk a x} {q : (zdGraph 2).Walk x b},
      p.append q = γ → ∀ e ∈ q.edges, e ∈ γ.edges := fun hpq e he => by
    rw [← hpq, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases c
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    have h' : IsDualArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | v 0 ≤ z 0 + R - N - 1}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv
        change v 0 ≤ z 0 + R - N - 1
        omega)
    have hx : x 0 ≤ z 0 + R - N - 1 := hq.start_mem
    have hqne : ¬q.Nil := fun hn => by
      have : x 0 = b 0 := congrArg (· 0) hn.eq
      omega
    have hsnd : ¬q.snd 0 ≤ z 0 + R - N - 1 := hq.snd_notMem hqne
    have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
    have hx' : x 0 = z 0 + R - N - 1 := by omega
    have hbot : ∀ v ∈ q.support, z 0 + R - N - 1 ≤ v 0 ∧ (v 0 = z 0 + R - N - 1 → v = x) := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · exact ⟨by omega, fun _ => rfl⟩
      · have : ¬v 0 ≤ z 0 + R - N - 1 := hq.notMem_of_mem_tail v hv
        exact ⟨by omega, fun h => absurd (by omega) this⟩
    have hT : ∀ v ∈ q.support, (z 1 - R ≤ v 1 ∧ v 1 ≤ z 1 + R - 1 ∧ v 0 ≤ z 0 + R - 1) ∨ v = b := by
      intro v hv
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        exact Or.inl ⟨hvT.2.2.1, hvT.2.2.2, hvT.2.1⟩
      · exact Or.inr (hq.eq_end_of_notMem hv hvT)
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
        ![z 0 + R, z 1 + R - 1] := by
      intro v hv
      have h₁ := (hbot v hv).1
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases hT v hv with h₂ | rfl
      · omega
      · omega
    have htop : ∀ v ∈ q.support, v 0 = z 0 + R → v = b := by
      intro v hv hv1
      rcases hT v hv with h₂ | h₂
      · omega
      · exact h₂
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => ⟨h'.mem_of_mem_edges e
      (hqe hpq e he), mem_image_dualEdge_of_forall_mem_edges q (fun x' y' he' i => ?_) he⟩⟩
    · have : a 0 = x 0 := congrArg (· 0) hn.eq
      have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at ha
      omega
    · have hx'' := q.fst_mem_support_of_mem_edges he'
      have hy'' := q.snd_mem_support_of_mem_edges he'
      have hne : x' ≠ y' := (q.adj_of_mem_edges he').ne
      have bx := mem_Icc_two_iff.1 (hbox x' hx'')
      have bY := mem_Icc_two_iff.1 (hbox y' hy'')
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at bx bY
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        refine ⟨?_, ?_⟩
        · by_contra hc
          exact hne (((hbot x' hx'').2 (by omega)).trans ((hbot y' hy'').2 (by omega)).symm)
        · by_contra hc
          exact hne ((htop x' hx'' (by omega)).trans (htop y' hy'' (by omega)).symm)
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        omega
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    have h' : IsOpenArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | v 0 ≤ z 0 + R - N}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
        change v 0 ≤ z 0 + R - N
        omega)
    have hx : x 0 ≤ z 0 + R - N := hq.start_mem
    have hx' : x 0 = z 0 + R - N := by
      by_cases hqne : q.Nil
      · have : x 0 = b 0 := congrArg (· 0) hqne.eq
        omega
      · have hsnd : ¬q.snd 0 ≤ z 0 + R - N := hq.snd_notMem hqne
        have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
        omega
    have hbot : ∀ v ∈ q.support, z 0 + R - N ≤ v 0 := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · omega
      · have : ¬v 0 ≤ z 0 + R - N := hq.notMem_of_mem_tail v hv
        omega
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
        ![z 0 + R, z 1 + R - 1] := by
      intro v hv
      have h₁ := hbot v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        omega
      · rw [hq.eq_end_of_notMem hv hvT]
        omega
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => h'.mem_of_mem_edges e
      (hqe hpq e he)⟩
    have : a 0 = x 0 := congrArg (· 0) hn.eq
    have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at ha
    omega

/-- **The final crossing of an arm landing on the bottom side.** An arm of colour `c` to `B_R(z)`
ending on the bottom side splits, at its last vertex (face) at or above the inner row of the strip
of height `N` along the bottom side, into a nonempty first part and a crossing of that strip in the
sense of `separable_bottom_of_top`, when `r + N + 1 < R`. -/
theorem IsArm.exists_append_eq_bottom {c : Bool} {N R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrN : r + N + 1 < R)
    (hb : b 1 = z 1 - R - cond c 0 1) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧ ¬p.Nil ∧
      cond c
        (x 1 = z 1 - R + N ∧ b 1 = z 1 - R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 1 = z 1 - R + N ∧ b 1 = z 1 - R - 1 ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]}) := by
  have hrR : r < R := by omega
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  have hqe : ∀ {x : LatticeSite 2} {p : (zdGraph 2).Walk a x} {q : (zdGraph 2).Walk x b},
      p.append q = γ → ∀ e ∈ q.edges, e ∈ γ.edges := fun hpq e he => by
    rw [← hpq, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases c
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    simp only [Bool.cond_false] at hb
    have h' : IsDualArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | z 1 - R + N ≤ v 1}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv
        change z 1 - R + N ≤ v 1
        omega)
    have hx : z 1 - R + N ≤ x 1 := hq.start_mem
    have hqne : ¬q.Nil := fun hn => by
      have : x 1 = b 1 := congrArg (· 1) hn.eq
      omega
    have hsnd : ¬z 1 - R + N ≤ q.snd 1 := hq.snd_notMem hqne
    have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
    have hx' : x 1 = z 1 - R + N := by omega
    have hbot : ∀ v ∈ q.support, v 1 ≤ z 1 - R + N ∧ (v 1 = z 1 - R + N → v = x) := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · exact ⟨by omega, fun _ => rfl⟩
      · have : ¬z 1 - R + N ≤ v 1 := hq.notMem_of_mem_tail v hv
        exact ⟨by omega, fun h => absurd (by omega) this⟩
    have hT : ∀ v ∈ q.support, (z 0 - R ≤ v 0 ∧ v 0 ≤ z 0 + R - 1 ∧ z 1 - R ≤ v 1) ∨ v = b := by
      intro v hv
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        exact Or.inl ⟨hvT.1, hvT.2.1, hvT.2.2.1⟩
      · exact Or.inr (hq.eq_end_of_notMem hv hvT)
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
        ![z 0 + R - 1, z 1 - R + N] := by
      intro v hv
      have h₁ := (hbot v hv).1
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases hT v hv with h₂ | rfl
      · omega
      · omega
    have htop : ∀ v ∈ q.support, v 1 = z 1 - R - 1 → v = b := by
      intro v hv hv1
      rcases hT v hv with h₂ | h₂
      · omega
      · exact h₂
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => ⟨h'.mem_of_mem_edges e
      (hqe hpq e he), mem_image_dualEdge_of_forall_mem_edges q (fun x' y' he' i => ?_) he⟩⟩
    · have : a 1 = x 1 := congrArg (· 1) hn.eq
      have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at ha
      omega
    · have hx'' := q.fst_mem_support_of_mem_edges he'
      have hy'' := q.snd_mem_support_of_mem_edges he'
      have hne : x' ≠ y' := (q.adj_of_mem_edges he').ne
      have bx := mem_Icc_two_iff.1 (hbox x' hx'')
      have bY := mem_Icc_two_iff.1 (hbox y' hy'')
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at bx bY
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        omega
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        refine ⟨?_, ?_⟩
        · by_contra hc
          exact hne ((htop x' hx'' (by omega)).trans (htop y' hy'' (by omega)).symm)
        · by_contra hc
          exact hne (((hbot x' hx'').2 (by omega)).trans ((hbot y' hy'').2 (by omega)).symm)
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    simp only [Bool.cond_true, sub_zero] at hb
    have h' : IsOpenArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | z 1 - R + N ≤ v 1}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
        change z 1 - R + N ≤ v 1
        omega)
    have hx : z 1 - R + N ≤ x 1 := hq.start_mem
    have hx' : x 1 = z 1 - R + N := by
      by_cases hqne : q.Nil
      · have : x 1 = b 1 := congrArg (· 1) hqne.eq
        omega
      · have hsnd : ¬z 1 - R + N ≤ q.snd 1 := hq.snd_notMem hqne
        have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
        omega
    have hbot : ∀ v ∈ q.support, v 1 ≤ z 1 - R + N := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · omega
      · have : ¬z 1 - R + N ≤ v 1 := hq.notMem_of_mem_tail v hv
        omega
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
        ![z 0 + R - 1, z 1 - R + N] := by
      intro v hv
      have h₁ := hbot v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        omega
      · rw [hq.eq_end_of_notMem hv hvT]
        omega
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => h'.mem_of_mem_edges e
      (hqe hpq e he)⟩
    have : a 1 = x 1 := congrArg (· 1) hn.eq
    have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at ha
    omega

/-- **The final crossing of an arm landing on the left side.** An arm of colour `c` to `B_R(z)`
ending on the left side splits, at its last vertex (face) at or right of the inner column of the
strip of width `N` along the left side, into a nonempty first part and a crossing of that strip in
the sense of `separable_left_of_top`, when `r + N + 1 < R`. -/
theorem IsArm.exists_append_eq_left {c : Bool} {N R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z r (z - R) (z + R) γ) (hrN : r + N + 1 < R)
    (hb : b 0 = z 0 - R - cond c 0 1) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧ ¬p.Nil ∧
      cond c
        (x 0 = z 0 - R + N ∧ b 0 = z 0 - R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 - R + N ∧ b 0 = z 0 - R - 1 ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]}) := by
  have hrR : r < R := by omega
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  have hqe : ∀ {x : LatticeSite 2} {p : (zdGraph 2).Walk a x} {q : (zdGraph 2).Walk x b},
      p.append q = γ → ∀ e ∈ q.edges, e ∈ γ.edges := fun hpq e he => by
    rw [← hpq, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases c
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    simp only [Bool.cond_false] at hb
    have h' : IsDualArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | z 0 - R + N ≤ v 0}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv
        change z 0 - R + N ≤ v 0
        omega)
    have hx : z 0 - R + N ≤ x 0 := hq.start_mem
    have hqne : ¬q.Nil := fun hn => by
      have : x 0 = b 0 := congrArg (· 0) hn.eq
      omega
    have hsnd : ¬z 0 - R + N ≤ q.snd 0 := hq.snd_notMem hqne
    have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
    have hx' : x 0 = z 0 - R + N := by omega
    have hbot : ∀ v ∈ q.support, v 0 ≤ z 0 - R + N ∧ (v 0 = z 0 - R + N → v = x) := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · exact ⟨by omega, fun _ => rfl⟩
      · have : ¬z 0 - R + N ≤ v 0 := hq.notMem_of_mem_tail v hv
        exact ⟨by omega, fun h => absurd (by omega) this⟩
    have hT : ∀ v ∈ q.support, (z 1 - R ≤ v 1 ∧ v 1 ≤ z 1 + R - 1 ∧ z 0 - R ≤ v 0) ∨ v = b := by
      intro v hv
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        exact Or.inl ⟨hvT.2.2.1, hvT.2.2.2, hvT.1⟩
      · exact Or.inr (hq.eq_end_of_notMem hv hvT)
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
        ![z 0 - R + N, z 1 + R - 1] := by
      intro v hv
      have h₁ := (hbot v hv).1
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases hT v hv with h₂ | rfl
      · omega
      · omega
    have htop : ∀ v ∈ q.support, v 0 = z 0 - R - 1 → v = b := by
      intro v hv hv1
      rcases hT v hv with h₂ | h₂
      · omega
      · exact h₂
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => ⟨h'.mem_of_mem_edges e
      (hqe hpq e he), mem_image_dualEdge_of_forall_mem_edges q (fun x' y' he' i => ?_) he⟩⟩
    · have : a 0 = x 0 := congrArg (· 0) hn.eq
      have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at ha
      omega
    · have hx'' := q.fst_mem_support_of_mem_edges he'
      have hy'' := q.snd_mem_support_of_mem_edges he'
      have hne : x' ≠ y' := (q.adj_of_mem_edges he').ne
      have bx := mem_Icc_two_iff.1 (hbox x' hx'')
      have bY := mem_Icc_two_iff.1 (hbox y' hy'')
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at bx bY
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        refine ⟨?_, ?_⟩
        · by_contra hc
          exact hne ((htop x' hx'' (by omega)).trans (htop y' hy'' (by omega)).symm)
        · by_contra hc
          exact hne (((hbot x' hx'').2 (by omega)).trans ((hbot y' hy'').2 (by omega)).symm)
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        omega
  · obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    simp only [Bool.cond_true, sub_zero] at hb
    have h' : IsOpenArm ω z r (z - R) (z + R) γ := h
    obtain ⟨x, p, q, hpq, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := {v | z 0 - R + N ≤ v 0}) (fun v hv => by
        rw [mem_Icc_two_iff] at hv
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
        change z 0 - R + N ≤ v 0
        omega)
    have hx : z 0 - R + N ≤ x 0 := hq.start_mem
    have hx' : x 0 = z 0 - R + N := by
      by_cases hqne : q.Nil
      · have : x 0 = b 0 := congrArg (· 0) hqne.eq
        omega
      · have hsnd : ¬z 0 - R + N ≤ q.snd 0 := hq.snd_notMem hqne
        have hxsnd := (zdGraph_two_adj_iff _ _).1 (q.adj_snd hqne)
        omega
    have hbot : ∀ v ∈ q.support, v 0 ≤ z 0 - R + N := by
      intro v hv
      rcases (SimpleGraph.Walk.mem_support_iff q).1 hv with rfl | hv
      · omega
      · have : ¬z 0 - R + N ≤ v 0 := hq.notMem_of_mem_tail v hv
        omega
    have hbox : ∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
        ![z 0 - R + N, z 1 + R - 1] := by
      intro v hv
      have h₁ := hbot v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      by_cases hvT : v ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
      · rw [mem_Icc_two_iff] at hvT
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvT
        omega
      · rw [hq.eq_end_of_notMem hv hvT]
        omega
    refine ⟨x, p, q, hpq, fun hn => ?_, hx', hb, hbox, fun e he => h'.mem_of_mem_edges e
      (hqe hpq e he)⟩
    have : a 0 = x 0 := congrArg (· 0) hn.eq
    have ha := mem_Icc_two_iff.1 h'.isCrossing.start_mem
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at ha
    omega

/-- **Rerouting the arms landing on the right side.** The analogue of `exists_reroute_top` for the
right side, under the separation property of `separable_right_of_top`: the arms landing on the
right side are replaced by arms with the same colours, starts and inner positions, whose landing
positions are at least `4 √η N` apart and in `[4R + 4 √η N, 8R - 4 √η N]`, each with a fence to the
right of its end `b'`: a crossing of its colour from the bottom side to the top side of the box
`[b'₀, b'₀ + ⌊√η N⌋] × [b'₁ - ⌊η N⌋, b'₁ + ⌊η N⌋]`, whose bottom end is joined in its colour to a
vertex of the new arm inside the ball of radius `⌊√η N⌋` around `b'`. -/
theorem exists_reroute_right {η : ℝ} {N R : ℕ} (hR : R = 2 * N + 1) (hr : r < N)
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = z 0 + R - N ∧ b i 0 = z 0 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = z 0 + R - N - 1 ∧ b i 0 = z 0 + R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 + R - N ∧ b' i 0 = z 0 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = z 0 + R - N - 1 ∧ b' i 0 = z 0 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * (z 1 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0, b' i 1 - ⌊η * N⌋₊]
              ![b' i 0 + ⌊Real.sqrt η * N⌋₊, b' i 1 + ⌊η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ) :
    ∃ L : Fin j → ℤ,
      (∀ i, b i 0 = z 0 + R → ∃ (b' : LatticeSite 2) (Γ : (zdGraph 2).Walk (a i) b'),
        IsArm ω (σ i) z r (z - R) (z + R) Γ ∧
        innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
        landingPos (z - R) (z + R) (σ i) Γ = L i ∧
        ∃ x ∈ Γ.support, ∃ l r' : LatticeSite 2,
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l ∧
          b' 0 = z 0 + R ∧ l 1 = b' 1 - ⌊η * N⌋₊ ∧ r' 1 = b' 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' 0, b' 1 - ⌊η * N⌋₊] ![b' 0 + ⌊Real.sqrt η * N⌋₊, b' 1 + ⌊η * N⌋₊]) l r') ∧
      (∀ i k, b i 0 = z 0 + R → b k 0 = z 0 + R → i ≠ k →
        4 * Real.sqrt η * N ≤ |((L i - L k : ℤ) : ℝ)|) ∧
      (∀ i, b i 0 = z 0 + R →
        4 * (R : ℝ) + 4 * Real.sqrt η * N ≤ L i ∧ (L i : ℝ) + 4 * Real.sqrt η * N ≤ 8 * R) := by
  classical
  have hext : ∀ i, b i 0 = z 0 + R → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x)
      (q : (zdGraph 2).Walk x (b i)), p.append q = γ i ∧ ¬p.Nil ∧
      cond (σ i)
        (x 0 = z 0 + R - N ∧ b i 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N, z 1 - R + 1] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 + R - N - 1 ∧ b i 0 = z 0 + R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 + R - N - 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 + R - N, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 + R]}) :=
    fun i hi => (hγ i).exists_append_eq_right (by omega) hi
  choose x p q hpq hpne hq using hext
  -- the final crossings lie in the arms after their first vertex
  have htail : ∀ i hi, ∀ v ∈ (q i hi).support, v ∈ (γ i).support.tail := by
    intro i hi v hv
    rw [← hpq i hi, SimpleGraph.Walk.tail_support_append, List.mem_append]
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hv with rfl | hv
    · exact Or.inl (SimpleGraph.Walk.end_mem_tail_support (hpne i hi))
    · exact Or.inr hv
  obtain ⟨b'', γ'', H1, -, H3, H4, H5, H6⟩ := hω {i // b i 0 = z 0 + R} (fun i => σ i.1)
    (fun i => x i.1 i.2) (fun i => b i.1) (fun i => q i.1 i.2) (fun i => hq i.1 i.2)
    (fun i k hik hσ v hv hv' => by
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hv₁ := htail i.1 i.2 v hv
      have hv₂ := List.mem_of_mem_tail (htail k.1 k.2 v hv')
      cases h : σ i.1
      · exact hd.2 i.1 k.1 hne h (hσ.symm.trans h) v (List.mem_of_mem_tail hv₁) hv₂
      · exact hd.1 i.1 k.1 hne h (hσ.symm.trans h) v hv₁ hv₂)
  -- the doubled coordinates of the new ends along the side
  set d : {i // b i 0 = z 0 + R} → ℤ := fun i => 2 * b'' i 1 + cond (σ i.1) 0 1
    with hd_def
  refine ⟨fun i => if hi : b i 0 = z 0 + R then 4 * R + d ⟨i, hi⟩ - 2 * (z 1 - R) else 0,
    fun i hi => ?_, fun i k hi hk hik => ?_, fun i hi => ?_⟩
  · have h1 := H1 ⟨i, hi⟩
    have h3 := H3 ⟨i, hi⟩
    obtain ⟨y, hy, l, r', hl, hr', hlr, hyl⟩ := H6 ⟨i, hi⟩
    beta_reduce at h1 h3 hlr hyl
    -- the new final crossing fits the arm
    obtain ⟨hb1, hS, hT, hE⟩ : b'' ⟨i, hi⟩ 0 = z 0 + R ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support, w ∉ cond (σ i) (Icc (z - r) (z + r))
          (Icc (z - r - 1) (z + r))) ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support.dropLast, w ∈ cond (σ i) (Icc (z - R + 1) (z + R - 1))
          (Icc (z - R) (z + R - 1))) ∧
        (∀ e ∈ (γ'' ⟨i, hi⟩).edges, e ∈ cond (σ i) ω (dualConfig ω)) := by
      revert h1
      cases σ i
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, fun e he => (hE e he).1⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply, Pi.one_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, hE⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
    have hb : b'' ⟨i, hi⟩ ∉ cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
      cases σ i
      · intro h
        have := (mem_Icc_two_iff.1 h).2.1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this
        omega
      · intro h
        have := (mem_Icc_two_iff.1 h).2.1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this
        omega
    have hArm : IsArm ω (σ i) z r (z - R) (z + R) ((p i hi).append (γ'' ⟨i, hi⟩)) := by
      have h0 := hγ i
      rw [← hpq i hi] at h0
      exact h0.append_right hS hT hb hE
    refine ⟨b'' ⟨i, hi⟩, (p i hi).append (γ'' ⟨i, hi⟩), hArm, ?_, ?_, y, ?_, l, r', hyl, hb1, hl,
      hr', hlr⟩
    · rw [innerPos_append _ (hpne i hi)]
      conv_rhs => rw [← hpq i hi]
      rw [innerPos_append _ (hpne i hi)]
    · beta_reduce
      rw [dite_eq_left hi, hArm.landingPos_eq_of_right (by omega) hb1]
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hy
  · have h4 := H4 ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Subtype.val h))
    beta_reduce
    rw [dite_eq_left hi, dite_eq_left hk]
    have : (((4 * R + d ⟨i, hi⟩ - 2 * (z 1 - R)) - (4 * R + d ⟨k, hk⟩ - 2 * (z 1 - R)) : ℤ) : ℝ) =
        ((d ⟨i, hi⟩ : ℤ) : ℝ) - ((d ⟨k, hk⟩ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [this]
    exact h4
  · obtain ⟨h₁, h₂⟩ := H5 ⟨i, hi⟩
    beta_reduce
    rw [dite_eq_left hi]
    change 4 * Real.sqrt η * N ≤ ((d ⟨i, hi⟩ - 2 * (z 1 - R) : ℤ) : ℝ) at h₁
    change 4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - d ⟨i, hi⟩ : ℤ) : ℝ) at h₂
    push_cast at h₁ h₂ ⊢
    constructor <;> linarith

/-- **Rerouting the arms landing on the bottom side.** The analogue of `exists_reroute_top` for
the bottom side, under the separation property of `separable_bottom_of_top`: the arms landing on the
bottom side are replaced by arms with the same colours, starts and inner positions, whose landing
positions are at least `4 √η N` apart and in `[4 √η N, 4R - 4 √η N]`, each with a fence below its
end `b'`: a crossing of its colour from the left side to the right side of the box
`[b'₀ - ⌊η N⌋, b'₀ + ⌊η N⌋] × [b'₁ - ⌊√η N⌋, b'₁]`, whose left end is joined in its colour to a
vertex of the new arm inside the ball of radius `⌊√η N⌋` around `b'`. -/
theorem exists_reroute_bottom {η : ℝ} {N R : ℕ} (hR : R = 2 * N + 1) (hr : r < N)
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = z 1 - R + N ∧ b i 1 = z 1 - R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = z 1 - R + N ∧ b i 1 = z 1 - R - 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = z 1 - R + N ∧ b' i 1 = z 1 - R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = z 1 - R + N ∧ b' i 1 = z 1 - R - 1 ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ b' i 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z 0 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, b' i 1 - ⌊Real.sqrt η * N⌋₊]
              ![b' i 0 + ⌊η * N⌋₊, b' i 1]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ) :
    ∃ L : Fin j → ℤ,
      (∀ i, b i 1 = z 1 - R - cond (σ i) 0 1 → ∃ (b' : LatticeSite 2)
        (Γ : (zdGraph 2).Walk (a i) b'),
        IsArm ω (σ i) z r (z - R) (z + R) Γ ∧
        innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
        landingPos (z - R) (z + R) (σ i) Γ = L i ∧
        ∃ x ∈ Γ.support, ∃ l r' : LatticeSite 2,
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l ∧
          b' 1 = z 1 - R - cond (σ i) 0 1 ∧ l 0 = b' 0 - ⌊η * N⌋₊ ∧ r' 0 = b' 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' 0 - ⌊η * N⌋₊, b' 1 - ⌊Real.sqrt η * N⌋₊] ![b' 0 + ⌊η * N⌋₊, b' 1]) l r') ∧
      (∀ i k, b i 1 = z 1 - R - cond (σ i) 0 1 → b k 1 = z 1 - R - cond (σ k) 0 1 → i ≠ k →
        4 * Real.sqrt η * N ≤ |((L i - L k : ℤ) : ℝ)|) ∧
      (∀ i, b i 1 = z 1 - R - cond (σ i) 0 1 →
        4 * Real.sqrt η * N ≤ L i ∧ (L i : ℝ) + 4 * Real.sqrt η * N ≤ 4 * R) := by
  classical
  have hext : ∀ i, b i 1 = z 1 - R - cond (σ i) 0 1 → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x)
      (q : (zdGraph 2).Walk x (b i)), p.append q = γ i ∧ ¬p.Nil ∧
      cond (σ i)
        (x 1 = z 1 - R + N ∧ b i 1 = z 1 - R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R + 1, z 1 - R] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 1 = z 1 - R + N ∧ b i 1 = z 1 - R - 1 ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 - R - 1] : LatticeSite 2)
            ![z 0 + R - 1, z 1 - R + N]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 + R, z 1 - R + N]}) :=
    fun i hi => (hγ i).exists_append_eq_bottom (by omega) hi
  choose x p q hpq hpne hq using hext
  -- the final crossings lie in the arms after their first vertex
  have htail : ∀ i hi, ∀ v ∈ (q i hi).support, v ∈ (γ i).support.tail := by
    intro i hi v hv
    rw [← hpq i hi, SimpleGraph.Walk.tail_support_append, List.mem_append]
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hv with rfl | hv
    · exact Or.inl (SimpleGraph.Walk.end_mem_tail_support (hpne i hi))
    · exact Or.inr hv
  obtain ⟨b'', γ'', H1, -, H3, H4, H5, H6⟩ := hω {i // b i 1 = z 1 - R - cond (σ i) 0 1}
    (fun i => σ i.1)
    (fun i => x i.1 i.2) (fun i => b i.1) (fun i => q i.1 i.2) (fun i => hq i.1 i.2)
    (fun i k hik hσ v hv hv' => by
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hv₁ := htail i.1 i.2 v hv
      have hv₂ := List.mem_of_mem_tail (htail k.1 k.2 v hv')
      cases h : σ i.1
      · exact hd.2 i.1 k.1 hne h (hσ.symm.trans h) v (List.mem_of_mem_tail hv₁) hv₂
      · exact hd.1 i.1 k.1 hne h (hσ.symm.trans h) v hv₁ hv₂)
  -- the doubled coordinates of the new ends along the side
  set d : {i // b i 1 = z 1 - R - cond (σ i) 0 1} → ℤ := fun i => 2 * b'' i 0 + cond (σ i.1) 0 1
    with hd_def
  refine ⟨fun i => if hi : b i 1 = z 1 - R - cond (σ i) 0 1 then d ⟨i, hi⟩ - 2 * (z 0 - R) else 0,
    fun i hi => ?_, fun i k hi hk hik => ?_, fun i hi => ?_⟩
  · have h1 := H1 ⟨i, hi⟩
    have h3 := H3 ⟨i, hi⟩
    obtain ⟨y, hy, l, r', hl, hr', hlr, hyl⟩ := H6 ⟨i, hi⟩
    beta_reduce at h1 h3 hlr hyl
    -- the new final crossing fits the arm
    obtain ⟨hb1, hS, hT, hE⟩ : b'' ⟨i, hi⟩ 1 = z 1 - R - cond (σ i) 0 1 ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support, w ∉ cond (σ i) (Icc (z - r) (z + r))
          (Icc (z - r - 1) (z + r))) ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support.dropLast, w ∈ cond (σ i) (Icc (z - R + 1) (z + R - 1))
          (Icc (z - R) (z + R - 1))) ∧
        (∀ e ∈ (γ'' ⟨i, hi⟩).edges, e ∈ cond (σ i) ω (dualConfig ω)) := by
      revert h1
      cases σ i
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, fun e he => (hE e he).1⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply, Pi.one_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨(by rw [Bool.cond_true, sub_zero]; exact hb1), fun w hw hwB => ?_,
          fun w hw => ?_, hE⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
    have hb : b'' ⟨i, hi⟩ ∉ cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
      revert hb1
      cases σ i
      · intro hb1 h
        have := (mem_Icc_two_iff.1 h).2.2.1
        simp only [Pi.sub_apply, Pi.natCast_apply, Bool.cond_false] at this hb1
        omega
      · intro hb1 h
        have := (mem_Icc_two_iff.1 h).2.2.1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
          Bool.cond_true] at this hb1
        omega
    have hArm : IsArm ω (σ i) z r (z - R) (z + R) ((p i hi).append (γ'' ⟨i, hi⟩)) := by
      have h0 := hγ i
      rw [← hpq i hi] at h0
      exact h0.append_right hS hT hb hE
    refine ⟨b'' ⟨i, hi⟩, (p i hi).append (γ'' ⟨i, hi⟩), hArm, ?_, ?_, y, ?_, l, r', hyl, hb1, hl,
      hr', hlr⟩
    · rw [innerPos_append _ (hpne i hi)]
      conv_rhs => rw [← hpq i hi]
      rw [innerPos_append _ (hpne i hi)]
    · beta_reduce
      rw [dite_eq_left hi, hArm.landingPos_eq_of_bottom (by omega) hb1]
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hy
  · have h4 := H4 ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Subtype.val h))
    beta_reduce
    rw [dite_eq_left hi, dite_eq_left hk]
    have : (((d ⟨i, hi⟩ - 2 * (z 0 - R)) - (d ⟨k, hk⟩ - 2 * (z 0 - R)) : ℤ) : ℝ) =
        ((d ⟨i, hi⟩ : ℤ) : ℝ) - ((d ⟨k, hk⟩ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [this]
    exact h4
  · obtain ⟨h₁, h₂⟩ := H5 ⟨i, hi⟩
    beta_reduce
    rw [dite_eq_left hi]
    change 4 * Real.sqrt η * N ≤ ((d ⟨i, hi⟩ - 2 * (z 0 - R) : ℤ) : ℝ) at h₁
    change 4 * Real.sqrt η * N ≤ ((2 * (z 0 + R) - d ⟨i, hi⟩ : ℤ) : ℝ) at h₂
    push_cast at h₁ h₂ ⊢
    constructor <;> linarith

/-- **Rerouting the arms landing on the left side.** The analogue of `exists_reroute_top` for the
left side, under the separation property of `separable_left_of_top`: the arms landing on the left
side are replaced by arms with the same colours, starts and inner positions, whose landing positions
are at least `4 √η N` apart and in `[12R + 4 √η N, 16R - 4 √η N]`, each with a fence to the left of
its end `b'`: a crossing of its colour from the bottom side to the top side of the box
`[b'₀ - ⌊√η N⌋, b'₀] × [b'₁ - ⌊η N⌋, b'₁ + ⌊η N⌋]`, whose bottom end is joined in its colour to a
vertex of the new arm inside the ball of radius `⌊√η N⌋` around `b'`. -/
theorem exists_reroute_left {η : ℝ} {N R : ℕ} (hR : R = 2 * N + 1) (hr : r < N)
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 0 = z 0 - R + N ∧ b i 0 = z 0 - R - 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 0 = z 0 - R + N ∧ b' i 0 = z 0 - R - 1 ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 0 ≠ b' i 0) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 1 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 1 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 1 + cond (σ i) 0 1 - 2 * (z 1 - R) : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - (2 * b' i 1 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 1 = b' i 1 - ⌊η * N⌋₊ ∧ r 1 = b' i 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊Real.sqrt η * N⌋₊, b' i 1 - ⌊η * N⌋₊]
              ![b' i 0, b' i 1 + ⌊η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ) :
    ∃ L : Fin j → ℤ,
      (∀ i, b i 0 = z 0 - R - cond (σ i) 0 1 → ∃ (b' : LatticeSite 2)
        (Γ : (zdGraph 2).Walk (a i) b'),
        IsArm ω (σ i) z r (z - R) (z + R) Γ ∧
        innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
        landingPos (z - R) (z + R) (σ i) Γ = L i ∧
        ∃ x ∈ Γ.support, ∃ l r' : LatticeSite 2,
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l ∧
          b' 0 = z 0 - R - cond (σ i) 0 1 ∧ l 1 = b' 1 - ⌊η * N⌋₊ ∧ r' 1 = b' 1 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' 0 - ⌊Real.sqrt η * N⌋₊, b' 1 - ⌊η * N⌋₊] ![b' 0, b' 1 + ⌊η * N⌋₊]) l r') ∧
      (∀ i k, b i 0 = z 0 - R - cond (σ i) 0 1 → b k 0 = z 0 - R - cond (σ k) 0 1 → i ≠ k →
        4 * Real.sqrt η * N ≤ |((L i - L k : ℤ) : ℝ)|) ∧
      (∀ i, b i 0 = z 0 - R - cond (σ i) 0 1 →
        12 * (R : ℝ) + 4 * Real.sqrt η * N ≤ L i ∧ (L i : ℝ) + 4 * Real.sqrt η * N ≤ 16 * R) := by
  classical
  have hext : ∀ i, b i 0 = z 0 - R - cond (σ i) 0 1 → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x)
      (q : (zdGraph 2).Walk x (b i)), p.append q = γ i ∧ ¬p.Nil ∧
      cond (σ i)
        (x 0 = z 0 - R + N ∧ b i 0 = z 0 - R ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R, z 1 - R + 1] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ ω)
        (x 0 = z 0 - R + N ∧ b i 0 = z 0 - R - 1 ∧
          (∀ v ∈ q.support, v ∈ Icc (![z 0 - R - 1, z 1 - R] : LatticeSite 2)
            ![z 0 - R + N, z 1 + R - 1]) ∧
          ∀ e ∈ q.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z 0 - R, z 1 - R] : LatticeSite 2) ![z 0 - R + N, z 1 + R]}) :=
    fun i hi => (hγ i).exists_append_eq_left (by omega) hi
  choose x p q hpq hpne hq using hext
  -- the final crossings lie in the arms after their first vertex
  have htail : ∀ i hi, ∀ v ∈ (q i hi).support, v ∈ (γ i).support.tail := by
    intro i hi v hv
    rw [← hpq i hi, SimpleGraph.Walk.tail_support_append, List.mem_append]
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hv with rfl | hv
    · exact Or.inl (SimpleGraph.Walk.end_mem_tail_support (hpne i hi))
    · exact Or.inr hv
  obtain ⟨b'', γ'', H1, -, H3, H4, H5, H6⟩ := hω {i // b i 0 = z 0 - R - cond (σ i) 0 1}
    (fun i => σ i.1)
    (fun i => x i.1 i.2) (fun i => b i.1) (fun i => q i.1 i.2) (fun i => hq i.1 i.2)
    (fun i k hik hσ v hv hv' => by
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hv₁ := htail i.1 i.2 v hv
      have hv₂ := List.mem_of_mem_tail (htail k.1 k.2 v hv')
      cases h : σ i.1
      · exact hd.2 i.1 k.1 hne h (hσ.symm.trans h) v (List.mem_of_mem_tail hv₁) hv₂
      · exact hd.1 i.1 k.1 hne h (hσ.symm.trans h) v hv₁ hv₂)
  -- the doubled coordinates of the new ends along the side
  set d : {i // b i 0 = z 0 - R - cond (σ i) 0 1} → ℤ := fun i => 2 * b'' i 1 + cond (σ i.1) 0 1
    with hd_def
  refine ⟨fun i => if hi : b i 0 = z 0 - R - cond (σ i) 0 1 then
      12 * R + 2 * (z 1 + R) - d ⟨i, hi⟩ else 0,
    fun i hi => ?_, fun i k hi hk hik => ?_, fun i hi => ?_⟩
  · have h1 := H1 ⟨i, hi⟩
    have h3 := H3 ⟨i, hi⟩
    obtain ⟨y, hy, l, r', hl, hr', hlr, hyl⟩ := H6 ⟨i, hi⟩
    beta_reduce at h1 h3 hlr hyl
    -- the new final crossing fits the arm
    obtain ⟨hb1, hS, hT, hE⟩ : b'' ⟨i, hi⟩ 0 = z 0 - R - cond (σ i) 0 1 ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support, w ∉ cond (σ i) (Icc (z - r) (z + r))
          (Icc (z - r - 1) (z + r))) ∧
        (∀ w ∈ (γ'' ⟨i, hi⟩).support.dropLast, w ∈ cond (σ i) (Icc (z - R + 1) (z + R - 1))
          (Icc (z - R) (z + R - 1))) ∧
        (∀ e ∈ (γ'' ⟨i, hi⟩).edges, e ∈ cond (σ i) ω (dualConfig ω)) := by
      revert h1
      cases σ i
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨hb1, fun w hw hwB => ?_, fun w hw => ?_, fun e he => (hE e he).1⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply, Pi.one_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2)) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
      · rintro ⟨-, hb1, hS, hE⟩
        refine ⟨(by rw [Bool.cond_true, sub_zero]; exact hb1), fun w hw hwB => ?_,
          fun w hw => ?_, hE⟩
        · have h₁ := mem_Icc_two_iff.1 (hS w hw)
          have h₂ := mem_Icc_two_iff.1 hwB
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
            Pi.natCast_apply] at h₁ h₂
          omega
        · have h₁ := mem_Icc_two_iff.1 (hS w (List.dropLast_subset _ hw))
          have h₂ := h3 w hw
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
          change w ∈ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)
          rw [mem_Icc_two_iff]
          simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
          omega
    have hb : b'' ⟨i, hi⟩ ∉ cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)) := by
      revert hb1
      cases σ i
      · intro hb1 h
        have := (mem_Icc_two_iff.1 h).1
        simp only [Pi.sub_apply, Pi.natCast_apply, Bool.cond_false] at this hb1
        omega
      · intro hb1 h
        have := (mem_Icc_two_iff.1 h).1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
          Bool.cond_true] at this hb1
        omega
    have hArm : IsArm ω (σ i) z r (z - R) (z + R) ((p i hi).append (γ'' ⟨i, hi⟩)) := by
      have h0 := hγ i
      rw [← hpq i hi] at h0
      exact h0.append_right hS hT hb hE
    refine ⟨b'' ⟨i, hi⟩, (p i hi).append (γ'' ⟨i, hi⟩), hArm, ?_, ?_, y, ?_, l, r', hyl, hb1, hl,
      hr', hlr⟩
    · rw [innerPos_append _ (hpne i hi)]
      conv_rhs => rw [← hpq i hi]
      rw [innerPos_append _ (hpne i hi)]
    · beta_reduce
      rw [dite_eq_left hi, hArm.landingPos_eq_of_left (by omega) hb1]
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hy
  · have h4 := H4 ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Subtype.val h))
    beta_reduce
    rw [dite_eq_left hi, dite_eq_left hk]
    have : (((12 * R + 2 * (z 1 + R) - d ⟨i, hi⟩) - (12 * R + 2 * (z 1 + R) - d ⟨k, hk⟩) : ℤ) : ℝ) =
        ((d ⟨k, hk⟩ : ℤ) : ℝ) - ((d ⟨i, hi⟩ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [this, abs_sub_comm]
    exact h4
  · obtain ⟨h₁, h₂⟩ := H5 ⟨i, hi⟩
    beta_reduce
    rw [dite_eq_left hi]
    change 4 * Real.sqrt η * N ≤ ((d ⟨i, hi⟩ - 2 * (z 1 - R) : ℤ) : ℝ) at h₁
    change 4 * Real.sqrt η * N ≤ ((2 * (z 1 + R) - d ⟨i, hi⟩ : ℤ) : ℝ) at h₂
    push_cast at h₁ h₂ ⊢
    constructor <;> linarith

/-- **The side of the landing.** An arm of colour `c` to `B_R(z)` ends on one of the four sides:
`b₁ = z₁ + R` (top), `b₀ = z₀ + R` (right), `b₁ = z₁ - R - [c = dual]` (bottom) or
`b₀ = z₀ - R - [c = dual]` (left), where `b` is its last vertex (open) or face (dual). -/
theorem IsArm.end_mem_sides {c : Bool} {R : ℕ} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    (h : IsArm ω c z r (z - R) (z + R) γ) (hrR : r < R) :
    b 1 = z 1 + R ∨ b 0 = z 0 + R ∨ b 1 = z 1 - R - cond c 0 1 ∨ b 0 = z 0 - R - cond c 0 1 := by
  obtain ⟨hadj, hp⟩ := h.penultimate_mem hrR
  cases c
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    simp only [Bool.cond_false]
    omega
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp
    simp only [Bool.cond_true, sub_zero]
    omega

/-! ### The outer separation step -/

/-- **A separating event at the outer boundary of an annulus** (the outer step of Nolin's proof of
Theorem 11, event form, for colour sequences without packs). Let `σ` be a colour sequence with no
two cyclically consecutive arms of the same colour (or with at most one arm). For every `δ > 0`
there are `0 < η ≤ 1` and `N₀` such that, uniformly over the laws with crossing bounds `c` up to
`L`, for `R = 2N + 1` and `N₀ ≤ N ≤ L`, there is an event `G` of probability at least `1 - δ`,
determined by the edges with both ends in the annulus `B_{2R}(z) \ B_N(z)`, such that for every
`r < N`, on the `j`-arm event from `B_r(z)` to the boundary of `B_R(z)` and `G`, the arms can be
chosen separated (`outerSeparatedArmEvent` with `s = 4 √η N`, `M = ⌊√η N⌋`, `K = ⌊η N⌋`): there is
a disjoint family of arms of colours `σ` from `B_r(z)` to the boundary of `B_R(z)`, landing in
counterclockwise order, whose landing positions are at least `4 √η N` apart and at least `4 √η N`
from the doubled corners `4 m R`, and each of which carries a fence outside `B_R(z)` next to its end
`b` (its last vertex, resp. face): a path of its colour across the box of length `2 ⌊η N⌋` along the
side where it lands and depth `⌊√η N⌋`, centred at `b` along the side, whose first end is joined in
its colour to a vertex of the arm inside the ball of radius `⌊√η N⌋` around `b`
(`HasOuterFence`).

The event `G` is the intersection of the four strip events of Lemma 15 along the sides
(`exists_law_separable_ge_top`, read on the other sides by `separable_right_of_top`, ...); on it the
final crossings of the arms landing on each side are rerouted (`exists_reroute_top`, ...), and the
barrier (`ArmsDisjoint.of_innerPos_eq`, `sbtw_landingPos_of_innerPos_eq`) gives the disjointness and
the order of the new family. -/
theorem exists_separating_event {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ), R = 2 * N + 1 → N₀ ≤ N →
      (N : ℕ∞) ≤ L → ∃ G : Set (Config (LatticeSite 2)), MeasurableSet G ∧
        (∀ ω ω' : Config (LatticeSite 2), ω ∩ {e | ∀ v ∈ e,
            v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
              Icc (z - (N : LatticeSite 2)) (z + N)} =
          ω' ∩ {e | ∀ v ∈ e,
            v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
              Icc (z - (N : LatticeSite 2)) (z + N)} → (ω ∈ G ↔ ω' ∈ G)) ∧
        1 - δ ≤ law q G ∧ ∀ r < N, ∀ ω ∈ multiArmEvent σ z r R ∩ G,
          ω ∈ outerSeparatedArmEvent σ z r R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊
            ⌊η * N⌋₊ := by
  classical
  have hδ4 : 0 < δ / 4 := ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩
  obtain ⟨η, hη, hη1, N₀, htop⟩ := exists_law_separable_ge_top c hδ4
  refine ⟨η, hη, hη1, N₀, fun q L h z N R hR hN hNL => ?_⟩
  have hM : ⌊Real.sqrt η * N⌋₊ ≤ N := by
    refine Nat.floor_le_of_le ?_
    have h₁ : Real.sqrt η ≤ 1 := Real.sqrt_le_one.2 hη1
    have h₂ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hs : (0 : ℝ) ≤ 4 * Real.sqrt η * N := by positivity
  -- the maps to the frames of the right, bottom and left sides
  obtain ⟨gs, hgs⟩ := exists_iso_swap
  obtain ⟨gr, hgr⟩ := exists_iso_reflect_one 0
  obtain ⟨σr, hσr⟩ : ∃ e : LatticeSite 2 ≃ LatticeSite 2, ⇑e = fun v => ![v 1, v 0] :=
    ⟨gs.toEquiv, funext hgs⟩
  obtain ⟨σb, hσb⟩ : ∃ e : LatticeSite 2 ≃ LatticeSite 2, ⇑e = fun v => ![v 0, 0 - v 1] :=
    ⟨gr.toEquiv, funext hgr⟩
  obtain ⟨σl, hσl⟩ : ∃ e : LatticeSite 2 ≃ LatticeSite 2, ⇑e = fun v => ![v 1, 0 - v 0] := by
    refine ⟨(gs.trans gr).toEquiv, funext fun v => ?_⟩
    change gr (gs v) = _
    rw [hgr, hgs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hσr' : ∀ v, σr.symm v = ![v 1, v 0] := fun v => by
    apply σr.injective
    rw [Equiv.apply_symm_apply, hσr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact eq_vec_two v
  have hσb' : ∀ v, σb.symm v = ![v 0, 0 - v 1] := fun v => by
    apply σb.injective
    rw [Equiv.apply_symm_apply, hσb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
    exact eq_vec_two v
  have hσl' : ∀ v, σl.symm v = ![0 - v 1, v 0] := fun v => by
    apply σl.injective
    rw [Equiv.apply_symm_apply, hσl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
    exact eq_vec_two v
  -- the top-side event at any centre and its determining box
  let E : LatticeSite 2 → Set (Config (LatticeSite 2)) := fun z' =>
    {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, cond (σ i)
      (a i 1 = z' 1 + R - N ∧ b i 1 = z' 1 + R ∧
        (∀ x ∈ (γ i).support, x ∈ Icc (![z' 0 - R + 1, z' 1 + R - N] : LatticeSite 2)
          ![z' 0 + R - 1, z' 1 + R]) ∧
        ∀ e ∈ (γ i).edges, e ∈ ω)
      (a i 1 = z' 1 + R - N - 1 ∧ b i 1 = z' 1 + R ∧
        (∀ x ∈ (γ i).support, x ∈ Icc (![z' 0 - R, z' 1 + R - N - 1] : LatticeSite 2)
          ![z' 0 + R - 1, z' 1 + R]) ∧
        ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
          ∀ x ∈ e, x ∈ Icc (![z' 0 - R, z' 1 + R - N] : LatticeSite 2) ![z' 0 + R, z' 1 + R]})) →
    (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
    ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, cond (σ i)
        (a i 1 = z' 1 + R - N ∧ b' i 1 = z' 1 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z' 0 - R + 1, z' 1 + R - N] : LatticeSite 2)
            ![z' 0 + R - 1, z' 1 + R]) ∧
          ∀ e ∈ (γ' i).edges, e ∈ ω)
        (a i 1 = z' 1 + R - N - 1 ∧ b' i 1 = z' 1 + R ∧
          (∀ x ∈ (γ' i).support, x ∈ Icc (![z' 0 - R, z' 1 + R - N - 1] : LatticeSite 2)
            ![z' 0 + R - 1, z' 1 + R]) ∧
          ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![z' 0 - R, z' 1 + R - N] : LatticeSite 2)
              ![z' 0 + R, z' 1 + R]})) ∧
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
      (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ z' 1 + R) ∧
      (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
        |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
      (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * (z' 0 - R) : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ ((2 * (z' 0 + R) - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
      ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
        l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b' i 0 - ⌊η * N⌋₊, z' 1 + R]
            ![b' i 0 + ⌊η * N⌋₊, z' 1 + R + ⌊Real.sqrt η * N⌋₊]) l r ∧
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
            (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}
  let W : LatticeSite 2 → Set (Sym2 (LatticeSite 2)) := fun z' => {e | ∀ v ∈ e, v ∈ Icc
    (![z' 0 - R - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊, z' 1 + R - N] : LatticeSite 2)
    ![z' 0 + R + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊, z' 1 + R + ⌊Real.sqrt η * N⌋₊ + 1]}
  have hEW : ∀ z' (ω ω' : Config (LatticeSite 2)), ω ∩ W z' = ω' ∩ W z' →
      (ω ∈ E z' ↔ ω' ∈ E z') := fun z' ω ω' hωω' =>
    ⟨fun h' => mem_separable_top_of_inter_eq hM hωω' h',
      fun h' => mem_separable_top_of_inter_eq hM hωω'.symm h'⟩
  have hWfin : ∀ z', (W z').Finite := fun z' => finite_setOf_forall_mem (Set.finite_Icc _ _)
  have hEz : ∀ q' : Sym2 (LatticeSite 2) → unitInterval, CrossingBounds q' L c →
      ∀ z', 1 - δ / 4 ≤ law q' (E z') := fun q' h' z' => htop q' L h' z' N R hR hN hNL
  -- the four frame events: determined, measurable, of probability at least `1 - δ / 4`
  have hframe : ∀ (τ : LatticeSite 2 ≃ LatticeSite 2) (z' : LatticeSite 2),
      MeasurableSet {ω | Sym2.map τ '' ω ∈ E z'} ∧
      ∀ ω ω' : Config (LatticeSite 2), ω ∩ Sym2.map τ.symm '' W z' = ω' ∩ Sym2.map τ.symm '' W z' →
        (ω ∈ {ω | Sym2.map τ '' ω ∈ E z'} ↔ ω' ∈ {ω | Sym2.map τ '' ω ∈ E z'}) := by
    intro τ z'
    have hdet : ∀ ω ω' : Config (LatticeSite 2),
        ω ∩ Sym2.map τ.symm '' W z' = ω' ∩ Sym2.map τ.symm '' W z' →
        (ω ∈ {ω | Sym2.map τ '' ω ∈ E z'} ↔ ω' ∈ {ω | Sym2.map τ '' ω ∈ E z'}) :=
      fun ω ω' hωω' => image_sym2Map_mem_iff_of_inter_eq τ (hEW z') hωω'
    refine ⟨measurableSet_of_determined_finite ((hWfin z').image (Sym2.map τ.symm)) fun ω =>
      hdet ω (ω ∩ Sym2.map τ.symm '' W z') ?_, hdet⟩
    rw [inter_assoc, inter_self]
  have hlawr : 1 - δ / 4 ≤ law q {ω | Sym2.map σr '' ω ∈ E ![z 1, z 0]} := by
    have h1 := hEz _ h.swap ![z 1, z 0]
    rw [show (fun v : LatticeSite 2 => ![v 1, v 0]) = ⇑σr.symm from (funext hσr').symm,
      law_comp_sym2Map_apply] at h1
    exact h1
  have hlawb : 1 - δ / 4 ≤ law q {ω | Sym2.map σb '' ω ∈ E ![z 0, -z 1]} := by
    have h1 := hEz _ h.reflect ![z 0, -z 1]
    rw [show (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) = ⇑σb.symm from (funext hσb').symm,
      law_comp_sym2Map_apply] at h1
    exact h1
  have hlawl : 1 - δ / 4 ≤ law q {ω | Sym2.map σl '' ω ∈ E ![z 1, -z 0]} := by
    have h1 := hEz _ h.swap.reflect ![z 1, -z 0]
    have hprof : (fun e => (fun e' => q (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e'))
        (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) =
        fun e => q (Sym2.map σl.symm e) := by
      funext e
      beta_reduce
      rw [Sym2.map_map]
      congr 2
      funext v
      rw [Function.comp_apply, hσl']
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hprof, law_comp_sym2Map_apply] at h1
    exact h1
  have hK : ⌊η * N⌋₊ ≤ N := by
    refine Nat.floor_le_of_le ?_
    have h₂ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  -- the frame events are determined by the edges of the annulus `B_{2R}(z) \ B_N(z)`
  set Q : Set (Sym2 (LatticeSite 2)) := {e | ∀ v ∈ e,
      v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
        Icc (z - (N : LatticeSite 2)) (z + N)} with hQ
  have hsubQ : ∀ (τ : LatticeSite 2 ≃ LatticeSite 2) (z' : LatticeSite 2),
      (∀ u ∈ Icc (![z' 0 - R - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊, z' 1 + R - N] : LatticeSite 2)
          ![z' 0 + R + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊, z' 1 + R + ⌊Real.sqrt η * N⌋₊ + 1],
        τ.symm u ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
          Icc (z - (N : LatticeSite 2)) (z + N)) →
      ∀ ω ω' : Config (LatticeSite 2), ω ∩ Q = ω' ∩ Q →
        ω ∩ Sym2.map τ.symm '' W z' = ω' ∩ Sym2.map τ.symm '' W z' := by
    intro τ z' hτ ω ω' hωω'
    have hsub : Sym2.map τ.symm '' W z' ⊆ Q := by
      rintro _ ⟨e', he', rfl⟩ v hv
      obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.1 hv
      exact hτ u (he' u hu)
    ext e
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨((Set.ext_iff.1 hωω' e).1 ⟨h₁, hsub h₂⟩).1, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨((Set.ext_iff.1 hωω' e).2 ⟨h₁, hsub h₂⟩).1, h₂⟩
  have hτid : ∀ v, (Equiv.refl (LatticeSite 2)).symm v = v := fun v => rfl
  have hQt := hsubQ (Equiv.refl _) z fun u hu => by
    rw [hτid]
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hQr := hsubQ σr ![z 1, z 0] fun u hu => by
    rw [hσr']
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hQb := hsubQ σb ![z 0, -z 1] fun u hu => by
    rw [hσb']
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hQl := hsubQ σl ![z 1, -z 0] fun u hu => by
    rw [hσl']
    rw [mem_Icc_two_iff] at hu
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply] at hu ⊢
    omega
  have hFt : {ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} = E z := by
    ext ω
    rw [mem_ofPred_eq, image_sym2Map_refl]
  have hlawt : 1 - δ / 4 ≤ law q {ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} := by
    rw [hFt]
    exact hEz q h z
  -- the complement of a frame event has probability at most `δ / 4`
  have hcompl : ∀ (τ : LatticeSite 2 ≃ LatticeSite 2) (z' : LatticeSite 2),
      1 - δ / 4 ≤ law q {ω | Sym2.map τ '' ω ∈ E z'} →
      law q {ω | Sym2.map τ '' ω ∈ E z'}ᶜ ≤ δ / 4 := by
    intro τ z' hlaw
    rw [prob_compl_eq_one_sub (hframe τ z').1, tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.1 hlaw
  refine ⟨{ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} ∩
      {ω | Sym2.map σr '' ω ∈ E ![z 1, z 0]} ∩ {ω | Sym2.map σb '' ω ∈ E ![z 0, -z 1]} ∩
      {ω | Sym2.map σl '' ω ∈ E ![z 1, -z 0]},
    (((hframe _ _).1.inter (hframe _ _).1).inter (hframe _ _).1).inter (hframe _ _).1,
    fun ω ω' hωω' => ?_, ?_, fun r hr ω hω => ?_⟩
  · simp only [mem_inter_iff]
    rw [(hframe _ _).2 ω ω' (hQt ω ω' hωω'), (hframe _ _).2 ω ω' (hQr ω ω' hωω'),
      (hframe _ _).2 ω ω' (hQb ω ω' hωω'), (hframe _ _).2 ω ω' (hQl ω ω' hωω')]
  · have hGm := (((hframe (Equiv.refl _) z).1.inter (hframe σr ![z 1, z 0]).1).inter
      (hframe σb ![z 0, -z 1]).1).inter (hframe σl ![z 1, -z 0]).1
    have hGc : law q ({ω | Sym2.map (Equiv.refl (LatticeSite 2)) '' ω ∈ E z} ∩
        {ω | Sym2.map σr '' ω ∈ E ![z 1, z 0]} ∩ {ω | Sym2.map σb '' ω ∈ E ![z 0, -z 1]} ∩
        {ω | Sym2.map σl '' ω ∈ E ![z 1, -z 0]})ᶜ ≤ δ := by
      rw [compl_inter, compl_inter, compl_inter]
      calc _ ≤ δ / 4 + δ / 4 + δ / 4 + δ / 4 :=
            (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
              (add_le_add ((measure_union_le _ _).trans (add_le_add (hcompl _ _ hlawt)
                (hcompl _ _ hlawr))) (hcompl _ _ hlawb))) (hcompl _ _ hlawl))
        _ = 4 * (δ / 4) := by ring
        _ ≤ δ := ENNReal.mul_div_le
    rw [prob_compl_eq_one_sub hGm] at hGc
    rw [tsub_le_iff_right] at hGc ⊢
    calc 1 ≤ δ + law q _ := hGc
      _ = law q _ + δ := add_comm _ _
  obtain ⟨hA, ⟨⟨hFt', hFr⟩, hFb⟩, hFl⟩ := hω
  -- the four side events
  have hEt : ω ∈ E z := by rw [← hFt]; exact hFt'
  have hEr := separable_right_of_top (z := z) (zf := ![z 1, z 0]) rfl rfl
    (by rw [← hσr]; exact hFr)
  have hEb := separable_bottom_of_top (z := z) (zf := ![z 0, -z 1]) rfl rfl
    (by rw [← hσb]; exact hFb)
  have hEl := separable_left_of_top (z := z) (zf := ![z 1, -z 0]) rfl rfl
    (by rw [← hσl]; exact hFl)
  obtain ⟨a, b, γ, hγ, hd, ho⟩ := mem_multiArmEvent_iff.1 hA
  obtain ⟨Lt, ht1, ht2, ht3⟩ := exists_reroute_top hR hr hEt hγ hd
  obtain ⟨Lr, hr1, hr2, hr3⟩ := exists_reroute_right hR hr hEr hγ hd
  obtain ⟨Lb, hb1, hb2, hb3⟩ := exists_reroute_bottom hR hr hEb hγ hd
  obtain ⟨Ll, hl1, hl2, hl3⟩ := exists_reroute_left hR hr hEl hγ hd
  -- the side of each arm, its index `n i` (bottom `0`, right `1`, top `2`, left `3`) and the new
  -- landing positions
  obtain ⟨n, hn⟩ : ∃ n : Fin j → ℕ, ∀ i, n i = if b i 1 = z 1 + R then 2 else
      if b i 0 = z 0 + R then 1 else if b i 1 = z 1 - R - cond (σ i) 0 1 then 0 else 3 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Fin j → ℤ, ∀ i, Λ i = if b i 1 = z 1 + R then Lt i else
      if b i 0 = z 0 + R then Lr i else if b i 1 = z 1 - R - cond (σ i) 0 1 then Lb i
        else Ll i :=
    ⟨_, fun _ => rfl⟩
  have hcase : ∀ i, (b i 1 = z 1 + R ∧ n i = 2 ∧ Λ i = Lt i) ∨
      (b i 0 = z 0 + R ∧ n i = 1 ∧ Λ i = Lr i) ∨
      (b i 1 = z 1 - R - cond (σ i) 0 1 ∧ n i = 0 ∧ Λ i = Lb i) ∨
      (b i 0 = z 0 - R - cond (σ i) 0 1 ∧ n i = 3 ∧ Λ i = Ll i) := by
    intro i
    by_cases h1 : b i 1 = z 1 + R
    · exact Or.inl ⟨h1, by rw [hn, ite_eq_left h1], by rw [hΛ, ite_eq_left h1]⟩
    by_cases h2 : b i 0 = z 0 + R
    · exact Or.inr (Or.inl ⟨h2, by rw [hn, ite_eq_right h1, ite_eq_left h2],
        by rw [hΛ, ite_eq_right h1, ite_eq_left h2]⟩)
    by_cases h3 : b i 1 = z 1 - R - cond (σ i) 0 1
    · exact Or.inr (Or.inr (Or.inl ⟨h3, by rw [hn, ite_eq_right h1, ite_eq_right h2,
        ite_eq_left h3], by rw [hΛ, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]⟩))
    have h4 : b i 0 = z 0 - R - cond (σ i) 0 1 := by
      rcases (hγ i).end_mem_sides (by omega) with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact h
    exact Or.inr (Or.inr (Or.inr ⟨h4, by rw [hn, ite_eq_right h1, ite_eq_right h2,
      ite_eq_right h3], by rw [hΛ, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]⟩))
  -- the new arms
  have hnew : ∀ i, ∃ (b' : LatticeSite 2) (Γ : (zdGraph 2).Walk (a i) b'),
      IsArm ω (σ i) z r (z - R) (z + R) Γ ∧ innerPos z r (σ i) Γ = innerPos z r (σ i) (γ i) ∧
      landingPos (z - R) (z + R) (σ i) Γ = Λ i ∧
      HasOuterFence ω (σ i) z R ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ := by
    intro i
    rcases hcase i with ⟨h1, -, hΛi⟩ | ⟨h1, -, hΛi⟩ | ⟨h1, -, hΛi⟩ | ⟨h1, -, hΛi⟩
    · obtain ⟨b', Γ, hΓ, hin, hL, x, hx, l, r', hxl, hfen⟩ := ht1 i h1
      exact ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, x, hx, l, r', hxl, Or.inl hfen⟩
    · obtain ⟨b', Γ, hΓ, hin, hL, x, hx, l, r', hxl, hfen⟩ := hr1 i h1
      exact ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, x, hx, l, r', hxl, Or.inr (Or.inl hfen)⟩
    · obtain ⟨b', Γ, hΓ, hin, hL, x, hx, l, r', hxl, hfen⟩ := hb1 i h1
      exact ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, x, hx, l, r', hxl, Or.inr (Or.inr (Or.inl hfen))⟩
    · obtain ⟨b', Γ, hΓ, hin, hL, x, hx, l, r', hxl, hfen⟩ := hl1 i h1
      exact ⟨b', Γ, hΓ, hin, hL.trans hΛi.symm, x, hx, l, r', hxl, Or.inr (Or.inr (Or.inr hfen))⟩
  choose b' Γ hΓ hin hL hfen using hnew
  -- the new landing positions lie in the intervals of their sides
  have hrange : ∀ i, 4 * (n i : ℝ) * R + 4 * Real.sqrt η * N ≤ Λ i ∧
      (Λ i : ℝ) + 4 * Real.sqrt η * N ≤ 4 * ((n i : ℝ) + 1) * R := by
    intro i
    rcases hcase i with ⟨h1, hni, hΛi⟩ | ⟨h1, hni, hΛi⟩ | ⟨h1, hni, hΛi⟩ | ⟨h1, hni, hΛi⟩
    · obtain ⟨h₁, h₂⟩ := ht3 i h1
      rw [hni, hΛi]
      push_cast
      constructor <;> linarith
    · obtain ⟨h₁, h₂⟩ := hr3 i h1
      rw [hni, hΛi]
      push_cast
      constructor <;> linarith
    · obtain ⟨h₁, h₂⟩ := hb3 i h1
      rw [hni, hΛi]
      push_cast
      constructor <;> linarith
    · obtain ⟨h₁, h₂⟩ := hl3 i h1
      rw [hni, hΛi]
      push_cast
      constructor <;> linarith
  have hsame : ∀ i k, i ≠ k → n i = n k → 4 * Real.sqrt η * N ≤ |((Λ i - Λ k : ℤ) : ℝ)| := by
    intro i k hik hnik
    rcases hcase i with ⟨hi1, hni, hΛi⟩ | ⟨hi1, hni, hΛi⟩ | ⟨hi1, hni, hΛi⟩ | ⟨hi1, hni, hΛi⟩ <;>
      rcases hcase k with ⟨hk1, hnk, hΛk⟩ | ⟨hk1, hnk, hΛk⟩ | ⟨hk1, hnk, hΛk⟩ | ⟨hk1, hnk, hΛk⟩ <;>
      rw [hΛi, hΛk] <;>
      first
        | (exfalso; omega)
        | exact ht2 i k hi1 hk1 hik
        | exact hr2 i k hi1 hk1 hik
        | exact hb2 i k hi1 hk1 hik
        | exact hl2 i k hi1 hk1 hik
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hsep : ∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤ |((Λ i - Λ k : ℤ) : ℝ)| := by
    intro i k hik
    have hi := hrange i
    have hk := hrange k
    rcases Nat.lt_trichotomy (n i) (n k) with hnik | hnik | hnik
    · have h' : (n i : ℝ) + 1 ≤ n k := by exact_mod_cast hnik
      push_cast
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      nlinarith
    · exact hsame i k hik hnik
    · have h' : (n k : ℝ) + 1 ≤ n i := by exact_mod_cast hnik
      refine le_trans ?_ (le_abs_self _)
      push_cast
      nlinarith
  have hcorner : ∀ i (m : ℕ), 4 * Real.sqrt η * N ≤ |((Λ i - 4 * m * R : ℤ) : ℝ)| := by
    intro i m
    have hi := hrange i
    rcases le_or_gt m (n i) with hm | hm
    · have h' : (m : ℝ) ≤ n i := by exact_mod_cast hm
      refine le_trans ?_ (le_abs_self _)
      push_cast
      nlinarith
    · have h' : (n i : ℝ) + 1 ≤ m := by exact_mod_cast hm
      refine le_trans ?_ (neg_le_abs _)
      push_cast
      nlinarith
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) :=
    Icc_subset_Icc_add_one_sub_one (by omega)
  refine ⟨a, b', Γ, hΓ, ArmsDisjoint.of_innerPos_eq hσ hB hγ hd ho hΓ hin,
    fun i k l hik hkl => sbtw_landingPos_of_innerPos_eq hσ hB hγ hd ho hΓ hin i k l hik hkl,
    fun i k hik => ?_, fun i m => ?_, hfen⟩
  · rw [hL i, hL k]
    exact hsep i k hik
  · rw [hL i]
    exact hcorner i m


/-- **Separation of arms at the outer boundary of an annulus** (the outer step of Nolin's proof of
Theorem 11, for colour sequences without packs). Under the hypotheses of `exists_separating_event`,
for `r < N`: the probability that the `j`-arm event from `B_r(z)` to the boundary of `B_R(z)`,
`R = 2N + 1`, occurs but the arms cannot be chosen separated (`outerSeparatedArmEvent`, with the
parameters of `exists_separating_event`) is at most `δ` times the probability of the `j`-arm event
from `B_r(z)` to the boundary of `B_N(z)`. The separating event of `exists_separating_event`
depends only on edges outside `B_N(z)`, the `j`-arm event to the boundary of `B_N(z)` only on edges
inside, and the latter contains the `j`-arm event to the boundary of `B_R(z)`. -/
theorem exists_law_multiArmEvent_inter_not_separated_le {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N R : ℕ), R = 2 * N + 1 → N₀ ≤ N →
      r < N → (N : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R \
          outerSeparatedArmEvent σ z r R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊) ≤
        δ * law q (multiArmEvent σ z r N) := by
  obtain ⟨η, hη, hη1, N₀, hG⟩ := exists_separating_event σ hσ c hδ
  refine ⟨η, hη, hη1, N₀, fun q L h z r N R hR hN hr hNL => ?_⟩
  obtain ⟨G, hGm, hGd, hGl, hGsep⟩ := hG q L h z N R hR hN hNL
  have hAm : MeasurableSet (multiArmEvent σ z r N) := measurableSet_multiArmEvent σ z r N
  have hPQ : Disjoint
      {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ Icc (z - (N : LatticeSite 2)) (z + N)}
      {e | ∀ v ∈ e,
        v ∈ Icc (z - ((2 * R : ℕ) : LatticeSite 2)) (z + ((2 * R : ℕ) : LatticeSite 2)) \
          Icc (z - (N : LatticeSite 2)) (z + N)} :=
    Set.disjoint_left.2 fun e heP heQ =>
      (heQ _ (Sym2.out_fst_mem e)).2 (heP _ (Sym2.out_fst_mem e))
  have hind : law q (multiArmEvent σ z r N ∩ Gᶜ) = law q (multiArmEvent σ z r N) * law q Gᶜ :=
    PercLib.Probability.prodBernoulli_inter_of_determined q hPQ hAm hGm.compl
      (fun ω ω' hωω' => mem_multiArmEventTo_iff_of_inter_eq sdiff_subset hωω')
      fun ω ω' hωω' => not_congr (hGd ω ω' hωω')
  have hGc : law q Gᶜ ≤ δ := by
    rw [prob_compl_eq_one_sub hGm, tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.1 hGl
  calc _ ≤ law q (multiArmEvent σ z r N ∩ Gᶜ) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨hA, hnot⟩ := hω
        exact ⟨multiArmEvent_subset_of_le le_rfl (by omega) hr hA,
          fun hωG => hnot (hGsep r hr ω ⟨hA, hωG⟩)⟩
    _ = law q (multiArmEvent σ z r N) * law q Gᶜ := hind
    _ ≤ law q (multiArmEvent σ z r N) * δ := by gcongr
    _ = δ * law q (multiArmEvent σ z r N) := mul_comm _ _

end PercLib.Models.Planar
