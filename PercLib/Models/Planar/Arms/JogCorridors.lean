/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12).
-/
module

public import PercLib.Models.Planar.Arms.CorridorGluing

/-!
# Jog corridors with caps

Corridors that continue an arm separated at the outer boundary of `B_R(z)` to the boundary of a
larger box `B_{R'}(z)`, moving it along its side and ending it with a new outer fence there.

* **Jogs.** A jog on a side of `B_R(z)` is a chain of three crossings: out from the bin of the arm
  (`V₁`), along the side by a shift `d` (`H`), and out again up to the row (column) just inside
  `∂B_{R'}(z)` (`V₂`). The fence of the arm meets `V₁`, and consecutive crossings meet in their
  common squares (`exists_mem_support_of_mem_Icc_of_mem_Icc`).
* **Caps.** A cap is a connector `H_c`, a crossing `U` through `∂B_{R'}(z)` and a crossing `H_f`
  beyond it. The continuation is cut at its first exit from the interior of `B_{R'}(z)`; that point
  `y` lies on `U`, and the part of `U` after `y` together with `H_f` is a new outer fence at `y`
  (`HasOuterFence` of length `2K'` and depth `M'`).
* **Corridors.** For one arm, the six crossings form an event of the colour of the arm,
  determined by the pairs inside a straight box from the bin out to distance `R' + M'`, of
  probability at least `c κ ^ 6` for laws with crossing bounds `c`.

## Main results

* `exists_walk_of_jog_top`, `exists_walk_of_jog_right`, `exists_walk_of_jog_bottom`,
  `exists_walk_of_jog_left`: on the six crossings, a fenced arm ending in its bin is continued to
  a point of the same side of `B_{R'}(z)`, shifted by `d`, with a new outer fence; from the legs
  `exists_walk_leg_top` (and the three other sides) and the caps `exists_walk_cap_top` (and the
  three other sides).
* `exists_corridor_jog`: the corridor event of one arm on any side, in the form used by the
  gluing (`law_mul_prod_le_law_of_sides`).

## Implementation notes

* The bottom and left sides are shifted by one for dual arms (`cond col 0 1`), as in
  `HasOuterFence`; the right and left statements are the top and bottom ones with the
  coordinates exchanged (`exists_mem_support_of_mem_Icc_of_mem_Icc_swap`,
  `exists_mem_localConn_of_walk_one`).
* The interior of `B_{R'}(z)` for either colour is handled through `mem_cond_interior_iff`.
* Boxes of the caps are passed as variables with coordinate equations, so the jogs can pass
  their own boxes without rewriting.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar


/-! ### Fences at a point -/

/-- A fence at the end `b` of an arm depends only on `b`: a fence of the trivial walk at `b` is a
fence of every walk ending at `b`. -/
theorem HasOuterFence.of_nil {ω : Config (LatticeSite 2)} {c : Bool} {z : LatticeSite 2}
    {R M K : ℕ} {a b : LatticeSite 2}
    (h : HasOuterFence ω c z R M K (SimpleGraph.Walk.nil : (zdGraph 2).Walk b b))
    (γ : (zdGraph 2).Walk a b) : HasOuterFence ω c z R M K γ := by
  obtain ⟨x, hx, u, v, h₁, h₂⟩ := h
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
  subst hx
  exact ⟨x, γ.end_mem_support, u, v, h₁, h₂⟩

/-! ### Walks -/

/-- **Joining a walk to a second walk** through a common vertex `w`: a walk ending at `w` and a
walk through `w` and `t` give a walk to `t` through the two supports. -/
theorem exists_walk_join {ζ : Config (LatticeSite 2)} {a w c d t : LatticeSite 2}
    (P : (zdGraph 2).Walk a w) (hPe : ∀ e ∈ P.edges, e ∈ ζ)
    (V : (zdGraph 2).Walk c d) (hVe : ∀ e ∈ V.edges, e ∈ ζ)
    (hw : w ∈ V.support) (ht : t ∈ V.support) :
    ∃ P' : (zdGraph 2).Walk a t, (∀ e ∈ P'.edges, e ∈ ζ) ∧
      ∀ v ∈ P'.support, v ∈ P.support ∨ v ∈ V.support := by
  obtain ⟨g, hg, hge⟩ := exists_walk_of_mem_support_of_mem_support V hw ht
  refine ⟨P.append g, fun e he => ?_, fun v hv => ?_⟩
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact hPe e he
    · exact hVe e (hge e he)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    exact hv.imp id (hg v)

/-- A vertex of a walk is a vertex before the last one or the end. -/
theorem SimpleGraph.Walk.mem_dropLast_or_eq_of_mem_support {V : Type*} {G : SimpleGraph V}
    {u v w : V} {p : G.Walk u v} (hw : w ∈ p.support) : w ∈ p.support.dropLast ∨ w = v := by
  rw [← List.dropLast_append_getLast p.support_ne_nil, SimpleGraph.Walk.getLast_support,
    List.mem_append, List.mem_singleton] at hw
  exact hw

/-- A walk of `ℤ²` all of whose edges lie in `ζ` is a walk of the open graph of
`ζ ∩ (zdGraph 2).edgeSet`. -/
theorem mem_edgeSet_openGraph_of_mem {ζ : Config (LatticeSite 2)} {a b : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (hp : ∀ e ∈ p.edges, e ∈ ζ) :
    ∀ e ∈ p.edges, e ∈ (openGraph (ζ ∩ (zdGraph 2).edgeSet)).edgeSet := fun e he => by
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨⟨hp e he, p.edges_subset_edgeSet he⟩,
    SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩

/-- **A fence inside a crossing.** A walk of `ζ` in the rows `[y₀, y₁]` from a column `≤ x₀ - K`
to a column `≥ x₀ + K` contains a connection of `ζ`, inside
`Icc ![x₀ - K, y₀] ![x₀ + K, y₁]`, from a vertex of column `x₀ - K` to a vertex of column `x₀ + K`;
its first end is a vertex of the walk. -/
theorem exists_mem_localConn_of_walk_zero {ζ : Config (LatticeSite 2)} {a b : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (hp : ∀ e ∈ p.edges, e ∈ ζ) {x₀ y₀ y₁ : ℤ} {K : ℕ}
    (hrow : ∀ v ∈ p.support, y₀ ≤ v 1 ∧ v 1 ≤ y₁) (ha : a 0 ≤ x₀ - K) (hb : x₀ + K ≤ b 0) :
    ∃ u v : LatticeSite 2, u ∈ p.support ∧ u 0 = x₀ - K ∧ v 0 = x₀ + K ∧
      ζ ∩ (zdGraph 2).edgeSet ∈ localConn (Icc ![x₀ - K, y₀] ![x₀ + K, y₁]) u v := by
  obtain ⟨u, v, hu, hv, g, hg⟩ := SimpleGraph.Walk.exists_walk_mem_Icc
    (fun w : LatticeSite 2 => w 0) (fun _ _ h => coord_le_add_one_of_adj h 0)
    (p.transfer _ (mem_edgeSet_openGraph_of_mem p hp)) ha (by omega) hb
  have hu' : u ∈ p.support := by
    have := (hg u g.start_mem_support).1
    rwa [SimpleGraph.Walk.support_transfer] at this
  refine ⟨u, v, hu', hu, hv, mem_localConn_iff_exists_walk.2 ⟨g, fun w hw => ?_⟩⟩
  obtain ⟨h₁, h₂, h₃⟩ := hg w hw
  rw [SimpleGraph.Walk.support_transfer] at h₁
  have := hrow w h₁
  rw [mem_Icc_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- **A fence inside a crossing**, `exists_mem_localConn_of_walk_zero` with the coordinates
exchanged: a walk of `ζ` in the columns `[y₀, y₁]` from a row `≤ x₀ - K` to a row `≥ x₀ + K`. -/
theorem exists_mem_localConn_of_walk_one {ζ : Config (LatticeSite 2)} {a b : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (hp : ∀ e ∈ p.edges, e ∈ ζ) {x₀ y₀ y₁ : ℤ} {K : ℕ}
    (hrow : ∀ v ∈ p.support, y₀ ≤ v 0 ∧ v 0 ≤ y₁) (ha : a 1 ≤ x₀ - K) (hb : x₀ + K ≤ b 1) :
    ∃ u v : LatticeSite 2, u ∈ p.support ∧ u 1 = x₀ - K ∧ v 1 = x₀ + K ∧
      ζ ∩ (zdGraph 2).edgeSet ∈ localConn (Icc ![y₀, x₀ - K] ![y₁, x₀ + K]) u v := by
  obtain ⟨u, v, hu, hv, g, hg⟩ := SimpleGraph.Walk.exists_walk_mem_Icc
    (fun w : LatticeSite 2 => w 1) (fun _ _ h => coord_le_add_one_of_adj h 1)
    (p.transfer _ (mem_edgeSet_openGraph_of_mem p hp)) ha (by omega) hb
  have hu' : u ∈ p.support := by
    have := (hg u g.start_mem_support).1
    rwa [SimpleGraph.Walk.support_transfer] at this
  refine ⟨u, v, hu', hu, hv, mem_localConn_iff_exists_walk.2 ⟨g, fun w hw => ?_⟩⟩
  obtain ⟨h₁, h₂, h₃⟩ := hg w hw
  rw [SimpleGraph.Walk.support_transfer] at h₁
  have := hrow w h₁
  rw [mem_Icc_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- `exists_mem_support_of_mem_Icc_of_mem_Icc` with the coordinates exchanged: a walk in the
columns `[y₀, y₁]` from a row `≤ x₀` to a row `≥ x₁` and a walk in the rows `[x₀, x₁]` from a
column `≤ y₀` to a column `≥ y₁` share a vertex. -/
theorem exists_mem_support_of_mem_Icc_of_mem_Icc_swap {a b c d : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (q : (zdGraph 2).Walk c d) {x₀ x₁ y₀ y₁ : ℤ} (hx : x₀ < x₁)
    (hy : y₀ ≤ y₁) (hp : ∀ v ∈ p.support, y₀ ≤ v 0 ∧ v 0 ≤ y₁) (ha : a 1 ≤ x₀) (hb : x₁ ≤ b 1)
    (hq : ∀ v ∈ q.support, x₀ ≤ v 1 ∧ v 1 ≤ x₁) (hc : c 0 ≤ y₀) (hd : y₁ ≤ d 0) :
    ∃ v ∈ p.support, v ∈ q.support := by
  obtain ⟨v, hvq, hvp⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc q p (x₀ := y₀) (x₁ := y₁)
    (y₀ := x₀) (y₁ := x₁) hy hx hq hc hd hp ha hb
  exact ⟨v, hvp, hvq⟩

/-! ### Corridors made of several crossings -/

section Events

variable {n : ℕ}

/-- The event that the boxes `Icc (lo m) (hi m)` are all crossed, in the directions `dir m`, in the
configuration of colour `col`, is measurable. -/
theorem measurableSet_setOf_forall_cond_crossing (col : Bool) (dir : Fin n → Fin 2)
    (lo hi : Fin n → LatticeSite 2) :
    MeasurableSet {ω : Config (LatticeSite 2) |
      ∀ m, cond col ω (dualConfig ω) ∈ crossing (dir m) (lo m) (hi m)} := by
  have : {ω : Config (LatticeSite 2) |
      ∀ m, cond col ω (dualConfig ω) ∈ crossing (dir m) (lo m) (hi m)} =
      ⋂ m, (fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing (dir m) (lo m) (hi m) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun m => measurableSet_preimage_cond_crossing col _ _ _

/-- The crossings of several boxes in the configuration of colour `col` are determined by the
pairs with both ends in one of the boxes, enlarged by one at the upper corner for the dual
colour. -/
theorem forall_cond_crossing_iff_of_inter_eq (col : Bool) (dir : Fin n → Fin 2)
    (lo hi : Fin n → LatticeSite 2) {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∃ m, ∀ v ∈ e, v ∈ Icc (lo m) (hi m + cond col 0 1)} =
      ω' ∩ {e | ∃ m, ∀ v ∈ e, v ∈ Icc (lo m) (hi m + cond col 0 1)}) :
    (∀ m, cond col ω (dualConfig ω) ∈ crossing (dir m) (lo m) (hi m)) ↔
      ∀ m, cond col ω' (dualConfig ω') ∈ crossing (dir m) (lo m) (hi m) := by
  refine forall_congr' fun m => preimage_cond_crossing_iff_of_inter_eq col (dir m) (lo m) (hi m) ?_
  ext e
  have := Set.ext_iff.1 h e
  simp only [mem_inter_iff, mem_ofPred_eq] at this ⊢
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(this.1 ⟨h₁, m, h₂⟩).1, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(this.2 ⟨h₁, m, h₂⟩).1, h₂⟩

/-- **Harris inside one corridor**: the probability that several boxes are all crossed in the
configuration of one colour is at least the product of the probabilities. -/
theorem prod_law_le_law_setOf_forall_cond_crossing (q : Sym2 (LatticeSite 2) → unitInterval)
    (col : Bool) (dir : Fin n → Fin 2) (lo hi : Fin n → LatticeSite 2) :
    ∏ m, law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing (dir m) (lo m) (hi m)) ≤
    law q {ω : Config (LatticeSite 2) |
      ∀ m, cond col ω (dualConfig ω) ∈ crossing (dir m) (lo m) (hi m)} := by
  classical
  have hmix : ∀ m ∈ Finset.univ, ∀ ω ω' : Config (LatticeSite 2),
      ω \ (cond col ∅ univ) ⊆ ω' \ (cond col ∅ univ) →
      ω' ∩ (cond col ∅ univ) ⊆ ω ∩ (cond col ∅ univ) →
      ω ∈ (fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing (dir m) (lo m) (hi m) →
      ω' ∈ (fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing (dir m) (lo m) (hi m) := by
    intro m _ ω ω' h₁ h₂ hω
    refine cond_mem_crossing_of_cond_subset ?_ hω
    cases col
    · simpa using h₂
    · simpa using h₁
  have := PercLib.Probability.prodBernoulli_prod_le_biInter_of_mixed q (cond col ∅ univ)
    Finset.univ hmix (fun m _ => measurableSet_preimage_cond_crossing col _ _ _)
  simp only [Finset.mem_univ, iInter_true] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  ext ω
  simp only [mem_iInter, mem_preimage, mem_ofPred_eq]

end Events

/-! ### Interiors -/

/-- A point of the interior of `B_{R'}(z)` lies in the interior of either colour. -/
theorem mem_cond_Icc_of_mem_Icc {col : Bool} {z v : LatticeSite 2} {R' : ℕ}
    (h : v ∈ Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1)) :
    v ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := by
  cases col
  · refine Icc_subset_Icc_left (fun i => ?_) h
    simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
    omega
  · exact h

/-- A point of the interior of `B_{R'}(z)` for either colour lies in `Icc (z - R') (z + R' - 1)`. -/
theorem mem_Icc_of_mem_cond_interior {col : Bool} {z v : LatticeSite 2} {R' : ℕ}
    (h : v ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1))) :
    v ∈ Icc (z - (R' : LatticeSite 2)) (z + R' - 1) := by
  cases col
  · exact h
  · refine Icc_subset_Icc_left (fun i => ?_) h
    simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
    omega

/-- **The interior of `B_{R'}(z)` for either colour**, in coordinates: `Icc (z - R' + 1) (z + R' -
1)`
for the open colour, `Icc (z - R') (z + R' - 1)` (faces) for the dual colour. -/
theorem mem_cond_interior_iff {col : Bool} {z v : LatticeSite 2} {R' : ℕ} :
    v ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
      (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ↔
      z 0 - R' + 1 - cond col 0 1 ≤ v 0 ∧ v 0 ≤ z 0 + R' - 1 ∧
        z 1 - R' + 1 - cond col 0 1 ≤ v 1 ∧ v 1 ≤ z 1 + R' - 1 := by
  cases col <;>
    simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] <;> omega



/-! ### Jogs with a cap: from a fence at `∂B_R(z)` to a fence at `∂B_{R'}(z)`

A jog moves an arm from its bin on a side of `B_R(z)` to a column (row) range shifted by `d`, and a
cap ends it on the same side of `B_{R'}(z)` with a new fence. Each side has three lemmas: the leg
(from the old fence through `V₁`, `H`, `V₂` into the interior of `B_{R'}(z)`), the cap (through
`H_c`, `U` to the first exit, and the new fence in `H_f`) and the jog (both). The bottom and left
sides are shifted by one for dual arms (`cond col 0 1`), as in `HasOuterFence`. -/

section Jogs

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R R' M K M' K' W : ℕ}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **The cap on the top side of `B_{R'}(z)`.** Let `Q` be a walk of the configuration `ζ` of colour
`col` inside the interior of `B_{R'}(z)` (for colour `col`), ending at a vertex `t` of a walk `p` of
`ζ` that runs in the columns `[c₀, c₁]` up to the row `z₁ + R' - 1` from a row `≤ z₁ + R' - M'`. If
the connector `H_c = [c₀, c₁] × [z₁ + R' - M', z₁ + R' - 1]` is crossed from left to right, the cap
`U = [c₀, c₁] × [z₁ + R' - M', z₁ + R' + M']` from bottom to top and the fence box
`H_f = [c₀ - K', c₁ + K'] × [z₁ + R' + 1, z₁ + R' + M']` from left to right (boxes given by their
corners), then `Q` is continued to the first point `y` outside the interior of `B_{R'}(z)`; `y` lies
on
the top side in the columns `[c₀, c₁]` and has an outer fence of length `2K'` and depth `M'`. -/
theorem exists_walk_cap_top {c₀ c₁ : ℤ} (hM' : 2 ≤ M') (hc₀₁ : c₀ < c₁) (hWc : c₁ - c₀ + K' ≤ M')
    (hcx : z 0 - R' + 1 ≤ c₀) (hcx' : c₁ ≤ z 0 + R' - 1) (hRM' : M' ≤ R')
    {x₀ t c d : LatticeSite 2} (Q : (zdGraph 2).Walk x₀ t)
    (hQe : ∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω))
    (hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)))
    (p : (zdGraph 2).Walk c d) (hpe : ∀ e ∈ p.edges, e ∈ cond col ω (dualConfig ω))
    (hp : ∀ w ∈ p.support, c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 - R' + 1 - cond col 0 1 ≤ w 1 ∧
      w 1 ≤ z 1 + R' - 1)
    (hc : c 1 ≤ z 1 + R' - M') (hd : z 1 + R' - 1 ≤ d 1) (ht : t ∈ p.support)
    {lc hc' lu hu lf hf : LatticeSite 2}
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 lc hc')
    (hlc : lc 0 = c₀ ∧ lc 1 = z 1 + R' - M') (hhc : hc' 0 = c₁ ∧ hc' 1 = z 1 + R' - 1)
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 lu hu)
    (hlu : lu 0 = c₀ ∧ lu 1 = z 1 + R' - M') (hhu : hu 0 = c₁ ∧ hu 1 = z 1 + R' + M')
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 lf hf)
    (hlf : lf 0 = c₀ - K' ∧ lf 1 = z 1 + R' + 1) (hhf : hf 0 = c₁ + K' ∧ hf 1 = z 1 + R' + M') :
    ∃ (y : LatticeSite 2) (P : (zdGraph 2).Walk x₀ y),
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ P.support, w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 + R' - M' ≤ w 1 ∧ w 1 ≤ z 1 + R' + M')) ∧
      (∀ w ∈ P.support, w ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → w = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 1 = z 1 + R' ∧ c₀ ≤ y 0 ∧ y 0 ≤ c₁ ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨c₄, -, hc₄, d₄, -, hd₄, h₄⟩ := hHc
  obtain ⟨p₄, hp₄, hp₄e⟩ := exists_walk_of_mem_localConn h₄
  obtain ⟨c₅, -, hc₅, d₅, -, hd₅, h₅⟩ := hU
  obtain ⟨p₅, hp₅, hp₅e⟩ := exists_walk_of_mem_localConn h₅
  obtain ⟨c₆, -, hc₆, d₆, -, hd₆, h₆⟩ := hHf
  obtain ⟨p₆, hp₆, hp₆e⟩ := exists_walk_of_mem_localConn h₆
  have C₄ : ∀ w ∈ p₄.support, c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 + R' - M' ≤ w 1 ∧
      w 1 ≤ z 1 + R' - 1 := fun w hw => by
    have := hp₄ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₅ : ∀ w ∈ p₅.support, c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 + R' - M' ≤ w 1 ∧
      w 1 ≤ z 1 + R' + M' := fun w hw => by
    have := hp₅ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₆ : ∀ w ∈ p₆.support, c₀ - K' ≤ w 0 ∧ w 0 ≤ c₁ + K' ∧ z 1 + R' + 1 ≤ w 1 ∧
      w 1 ≤ z 1 + R' + M' := fun w hw => by
    have := hp₆ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have hin : ∀ w : LatticeSite 2, c₀ ≤ w 0 → w 0 ≤ c₁ → z 1 - R' + 1 - cond col 0 1 ≤ w 1 →
      w 1 ≤ z 1 + R' - 1 → w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun w h₁ h₂ h₃ h₄ =>
    mem_cond_interior_iff.2 ⟨by omega, by omega, by omega, by omega⟩
  -- junctions of `p` with the connector and of the connector with the cap
  obtain ⟨w₄, hw₄p₄, hw₄p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₄ p (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 1 + R' - M') (y₁ := z 1 + R' - 1) (by omega) (by omega)
    (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(hp w hw).1, (hp w hw).2.1⟩) hc hd
  obtain ⟨w₅, hw₅p₄, hw₅p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₄ p₅ (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 1 + R' - M') (y₁ := z 1 + R' - 1) (by omega) (by omega)
    (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w hw).1, (C₅ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join Q hQe p hpe ht hw₄p
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₄ hp₄e hw₄p₄ hw₅p₄
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₅ hp₅e hw₅p₅ p₅.end_mem_support
  have GQ₂ : ∀ w ∈ Q₂.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      (w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 + R' - M' ≤ w 1 ∧ w 1 ≤ z 1 + R' + M')) := by
    intro w hw
    rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · exact ⟨hQin w hw, Or.inl hw⟩
      · have := hp w hw
        exact ⟨hin w this.1 this.2.1 this.2.2.1 this.2.2.2, Or.inr (Or.inl hw)⟩
    · have := C₄ w hw
      exact ⟨hin w this.1 this.2.1 (by omega) this.2.2.2, Or.inr (Or.inr (by omega))⟩
  -- cut at the first exit from the interior
  have hd₅out : d₅ ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun hmem => by
    have := mem_cond_interior_iff.1 hmem
    omega
  obtain ⟨y, P, P', hPP', hy, hPin⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem Q₃ hd₅out
  have hPsub : ∀ w ∈ P.support, w ∈ Q₃.support := fun w hw => by
    rw [← hPP', SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  have hy₅ : y ∈ p₅.support := by
    rcases hQ₃s y (hPsub y P.end_mem_support) with h | h
    · exact absurd (GQ₂ y h).1 hy
    · exact h
  have hnil : ¬P.Nil := fun hn => hy (hn.eq ▸ (GQ₂ x₀ Q₂.start_mem_support).1)
  have hpen := mem_cond_interior_iff.1
    (hPin _ (SimpleGraph.Walk.penultimate_mem_dropLast_support hnil))
  have hadj := apply_le_apply_add_one_of_adj (SimpleGraph.Walk.adj_penultimate hnil) 1
  have Cy := C₅ y hy₅
  have hy₁ : y 1 = z 1 + R' := by
    by_contra hne
    exact hy (hin y Cy.1 Cy.2.1 (by omega) (by omega))
  -- the new fence
  obtain ⟨p₅', hp₅'s, hp₅'e⟩ := exists_walk_of_mem_support_of_mem_support p₅ hy₅
    p₅.end_mem_support
  obtain ⟨w₆, hw₆p₆, hw₆p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₆ p₅' (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 1 + R' + 1) (y₁ := z 1 + R' + M') (by omega) (by omega)
    (fun w hw => ⟨(C₆ w hw).2.2.1, (C₆ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w (hp₅'s w hw)).1, (C₅ w (hp₅'s w hw)).2.1⟩) (by omega) (by omega)
  obtain ⟨u', v', hu'p, hu', hv', hfen'⟩ := exists_mem_localConn_of_walk_zero p₆ hp₆e
    (x₀ := y 0) (y₀ := y 1) (y₁ := y 1 + M') (K := K')
    (fun w hw => ⟨by have := C₆ w hw; omega, by have := C₆ w hw; omega⟩) (by omega) (by omega)
  obtain ⟨k₁, hk₁s, hk₁e⟩ := exists_walk_of_mem_support_of_mem_support p₅' p₅'.start_mem_support
    hw₆p₅
  obtain ⟨k₂, hk₂s, hk₂e⟩ := exists_walk_of_mem_support_of_mem_support p₆ hw₆p₆ hu'p
  have hconn : cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (y - (M' : LatticeSite 2)) (y + M')) y u' := by
    refine mem_localConn_of_walk (k₁.append k₂) (fun w hw => ?_) (fun e he => ?_)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hw
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      rcases hw with hw | hw
      · have := C₅ w (hp₅'s w (hk₁s w hw))
        omega
      · have := C₆ w (hk₂s w hw)
        omega
    · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hp₅e e (hp₅'e e (hk₁e e he))
      · exact hp₆e e (hk₂e e he)
  refine ⟨y, P, fun e he => ?_, fun w hw => ?_, fun w hw hwout => ?_, hy, hy₁, Cy.1, Cy.2.1,
    y, SimpleGraph.Walk.start_mem_support _, u', v', hconn, Or.inl ⟨hy₁, hu', hv', hfen'⟩⟩
  · have he' : e ∈ Q₃.edges := by
      rw [← hPP', SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    exact hQ₃e e he'
  · rcases hQ₃s w (hPsub w hw) with h | h
    · exact (GQ₂ w h).2
    · have := C₅ w h
      exact Or.inr (Or.inr (by omega))
  · rcases SimpleGraph.Walk.mem_dropLast_or_eq_of_mem_support hw with h | h
    · exact absurd (hPin w h) hwout
    · exact h

/-- **The leg of a jog on the top side.** An arm ending at `b` on the top side of `B_R(z)`, in the
columns `[x, x + W]`, with an outer fence of length `2K ≥ 2W` and depth `M`, is continued, on the
crossings of `V₁ = [x + K', x + W - K'] × [z₁ + R, z₁ + h + W₀]`,
`H = [xl + K', xr + W - K'] × [z₁ + h, z₁ + h + W₀]` (`W₀ = W - 2K'`) and
`V₂ = [x + d + K', x + d + W - K'] × [z₁ + h, z₁ + R' - 1]`, by a walk of its colour inside the
interior of `B_{R'}(z)` from one of its vertices (faces) within `M` of `b` to a vertex of the
crossing
walk of `V₂`. -/
theorem exists_walk_leg_top (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W)
    {h x d xl xr : ℤ} (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + 1 ≤ R')
    (hcl : z 0 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 0 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + K', z 1 + R]
      ![x + W - K', z 1 + h + ((W : ℤ) - 2 * K')])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![xl + K', z 1 + h]
      ![xr + W - K', z 1 + h + ((W : ℤ) - 2 * K')])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d + K', z 1 + h]
      ![x + d + W - K', z 1 + R' - 1])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₃ d₃ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₃ : (zdGraph 2).Walk c₃ d₃),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₃.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
        (w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
          w ∈ Icc (![x, z 1 + R] : LatticeSite 2) ![x + W, z 1 + h + W] ∨
          w ∈ Icc (![xl, z 1 + h] : LatticeSite 2) ![xr + W, z 1 + R' - 1])) ∧
      (∀ w ∈ p₃.support, x + d + K' ≤ w 0 ∧ w 0 ≤ x + d + W - K' ∧ z 1 + h ≤ w 1 ∧
        w 1 ≤ z 1 + R' - 1) ∧
      c₃ 1 = z 1 + h ∧ d₃ 1 = z 1 + R' - 1 ∧ t ∈ p₃.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 1 = z 1 + R ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1] ![b 0 + K, b 1 + M]) u v := by
    rcases hfen with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exfalso; omega
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the three crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hV₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hH
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂ hc₃ hd₃
  have Cg₀ : ∀ w ∈ g₀.support, b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M ∧ b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 0 - K ≤ w 0 ∧ w 0 ≤ b 0 + K ∧ b 1 ≤ w 1 ∧ w 1 ≤ b 1 + M :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, x + K' ≤ w 0 ∧ w 0 ≤ x + W - K' ∧ z 1 + R ≤ w 1 ∧
      w 1 ≤ z 1 + h + ((W : ℤ) - 2 * K') := fun w hw => by
    have := hp₁ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have C₂ : ∀ w ∈ p₂.support, xl + K' ≤ w 0 ∧ w 0 ≤ xr + W - K' ∧ z 1 + h ≤ w 1 ∧
      w 1 ≤ z 1 + h + ((W : ℤ) - 2 * K') := fun w hw => by
    have := hp₂ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have C₃ : ∀ w ∈ p₃.support, x + d + K' ≤ w 0 ∧ w 0 ≤ x + d + W - K' ∧ z 1 + h ≤ w 1 ∧
      w 1 ≤ z 1 + R' - 1 := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := b 1) (y₁ := b 1 + M) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := z 1 + h) (y₁ := z 1 + h + ((W : ℤ) - 2 * K')) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₃
    (x₀ := x + d + K') (x₁ := x + d + W - K') (y₀ := z 1 + h)
    (y₁ := z 1 + h + ((W : ℤ) - 2 * K')) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₂ hp₂e hw₂p₂ hw₃p₂
  refine ⟨x₀, w₃, c₃, d₃, Q₃, p₃, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₃e, hp₃e, ?_, C₃, hc₃, hd₃,
    hw₃p₃⟩
  intro w hw
  rw [mem_cond_interior_iff]
  simp only [mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hQ₃s w hw with hw | hw
  · rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · have := Cg₀ w hw
        exact ⟨by omega, Or.inl (by omega)⟩
      · have := Cf w hw
        exact ⟨by omega, Or.inl (by omega)⟩
    · have := C₁ w hw
      exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
  · have := C₂ w hw
    exact ⟨by omega, Or.inr (Or.inr (by omega))⟩

/-- **The jog with a cap on the top side**: leg (`exists_walk_leg_top`) and cap
(`exists_walk_cap_top`). Let an arm end at `b` on the top side of `B_R(z)` in the columns
`[x, x + W]`, with an outer fence of length `2K ≥ 2W` and depth `M`, and let `V₁, H, V₂` (the leg,
shifting the columns by `d`) and `H_c, U, H_f` (the cap at `∂B_{R'}(z)` above the columns
`[x + d + K', x + d + W - K']`) be crossed in the configuration of the colour of the arm. Then the
arm
is continued by a walk of its colour, through the box of radius `M` about `b`, the leg and the cap,
to the first point `y` outside the interior of `B_{R'}(z)`; `y` is on the top side above
`[x + d + K', x + d + W - K']` and has an outer fence of length `2K'` and depth `M'`. -/
theorem exists_walk_of_jog_top (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M)
    (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W ≤ M' + K') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R')
    (hcl : z 0 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 0 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + K', z 1 + R]
      ![x + W - K', z 1 + h + ((W : ℤ) - 2 * K')])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0 ![xl + K', z 1 + h]
      ![xr + W - K', z 1 + h + ((W : ℤ) - 2 * K')])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d + K', z 1 + h]
      ![x + d + W - K', z 1 + R' - 1])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d + K', z 1 + R' - M']
      ![x + d + W - K', z 1 + R' - 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d + K', z 1 + R' - M']
      ![x + d + W - K', z 1 + R' + M'])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d, z 1 + R' + 1]
      ![x + d + W, z 1 + R' + M'])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![x, z 1 + R] : LatticeSite 2) ![x + W, z 1 + h + W] ∨
        v ∈ Icc (![xl, z 1 + h] : LatticeSite 2) ![xr + W, z 1 + R' + M']) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 1 = z 1 + R' ∧ x + d + K' ≤ y 0 ∧ y 0 ≤ x + d + W - K' ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₃, d₃, Q, p₃, hx₀, hx₀M, hQe, hp₃e, hQ, hp₃, hc₃, hd₃, ht⟩ :=
    exists_walk_leg_top hM hWK hKM hK' hxl hxl' hxr hxr' hh (by omega) hcl hcr hMR hV₁ hH hV₂ hb₁
        hb₀
      hb₀' hbR hbL hf
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_top
    (R' := R') (M' := M') (K' := K') (c₀ := x + d + K') (c₁ := x + d + W - K') hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe (fun w hw => (hQ w hw).1) p₃ hp₃e
    (fun w hw => by have := hp₃ w hw; omega) (by omega) (by omega) ht hHc
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hU
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hHf
    ⟨by simp, by simp⟩
    ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h | h | h
  · rcases (hQ w h).2 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · right
      right
      rw [mem_Icc_two_iff] at h' ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h' ⊢
      omega
  · have := hp₃ w h
    right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- **The cap on the bottom side of `B_{R'}(z)`**: `exists_walk_cap_top` reflected (`δ = cond col 0
1`
shifts the rows of a dual arm): connector `H_c = [c₀, c₁] × [z₁ - R' + 1 - δ, z₁ - R' + M' - δ]`,
cap
`U = [c₀, c₁] × [z₁ - R' - M' - δ, z₁ - R' + M' - δ]`, fence box
`H_f = [c₀ - K', c₁ + K'] × [z₁ - R' - M' - δ, z₁ - R' - 1 - δ]`; the first exit `y` lies on the row
`z₁ - R' - δ`. -/
theorem exists_walk_cap_bottom {c₀ c₁ : ℤ} (hM' : 2 ≤ M') (hc₀₁ : c₀ < c₁)
    (hWc : c₁ - c₀ + K' ≤ M') (hcx : z 0 - R' + 1 ≤ c₀) (hcx' : c₁ ≤ z 0 + R' - 1)
    (hRM' : M' ≤ R') {x₀ t c d : LatticeSite 2} (Q : (zdGraph 2).Walk x₀ t)
    (hQe : ∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω))
    (hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)))
    (p : (zdGraph 2).Walk c d) (hpe : ∀ e ∈ p.edges, e ∈ cond col ω (dualConfig ω))
    (hp : ∀ w ∈ p.support, c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 - R' + 1 - cond col 0 1 ≤ w 1 ∧
      w 1 ≤ z 1 + R' - 1)
    (hc : c 1 ≤ z 1 - R' + 1 - cond col 0 1) (hd : z 1 - R' + M' - cond col 0 1 ≤ d 1)
    (ht : t ∈ p.support) {lc hc' lu hu lf hf : LatticeSite 2}
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 lc hc')
    (hlc : lc 0 = c₀ ∧ lc 1 = z 1 - R' + 1 - cond col 0 1)
    (hhc : hc' 0 = c₁ ∧ hc' 1 = z 1 - R' + M' - cond col 0 1)
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 lu hu)
    (hlu : lu 0 = c₀ ∧ lu 1 = z 1 - R' - M' - cond col 0 1)
    (hhu : hu 0 = c₁ ∧ hu 1 = z 1 - R' + M' - cond col 0 1)
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 lf hf)
    (hlf : lf 0 = c₀ - K' ∧ lf 1 = z 1 - R' - M' - cond col 0 1)
    (hhf : hf 0 = c₁ + K' ∧ hf 1 = z 1 - R' - 1 - cond col 0 1) :
    ∃ (y : LatticeSite 2) (P : (zdGraph 2).Walk x₀ y),
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ P.support, w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 - R' - M' - cond col 0 1 ≤ w 1 ∧
          w 1 ≤ z 1 - R' + M' - cond col 0 1)) ∧
      (∀ w ∈ P.support, w ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → w = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 1 = z 1 - R' - cond col 0 1 ∧ c₀ ≤ y 0 ∧ y 0 ≤ c₁ ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨c₄, -, hc₄, d₄, -, hd₄, h₄⟩ := hHc
  obtain ⟨p₄, hp₄, hp₄e⟩ := exists_walk_of_mem_localConn h₄
  obtain ⟨c₅, -, hc₅, d₅, -, hd₅, h₅⟩ := hU
  obtain ⟨p₅, hp₅, hp₅e⟩ := exists_walk_of_mem_localConn h₅
  obtain ⟨c₆, -, hc₆, d₆, -, hd₆, h₆⟩ := hHf
  obtain ⟨p₆, hp₆, hp₆e⟩ := exists_walk_of_mem_localConn h₆
  have C₄ : ∀ w ∈ p₄.support, c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 - R' + 1 - cond col 0 1 ≤ w 1 ∧
      w 1 ≤ z 1 - R' + M' - cond col 0 1 := fun w hw => by
    have := hp₄ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₅ : ∀ w ∈ p₅.support, c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 - R' - M' - cond col 0 1 ≤ w 1 ∧
      w 1 ≤ z 1 - R' + M' - cond col 0 1 := fun w hw => by
    have := hp₅ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₆ : ∀ w ∈ p₆.support, c₀ - K' ≤ w 0 ∧ w 0 ≤ c₁ + K' ∧
      z 1 - R' - M' - cond col 0 1 ≤ w 1 ∧ w 1 ≤ z 1 - R' - 1 - cond col 0 1 := fun w hw => by
    have := hp₆ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have hin : ∀ w : LatticeSite 2, c₀ ≤ w 0 → w 0 ≤ c₁ → z 1 - R' + 1 - cond col 0 1 ≤ w 1 →
      w 1 ≤ z 1 + R' - 1 → w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun w h₁ h₂ h₃ h₄ =>
    mem_cond_interior_iff.2 ⟨by omega, by omega, by omega, by omega⟩
  -- junctions of `p` with the connector and of the connector with the cap
  obtain ⟨w₄, hw₄p₄, hw₄p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₄ p (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 1 - R' + 1 - cond col 0 1) (y₁ := z 1 - R' + M' - cond col 0 1) (by omega)
    (by omega) (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(hp w hw).1, (hp w hw).2.1⟩) hc hd
  obtain ⟨w₅, hw₅p₄, hw₅p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₄ p₅ (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 1 - R' + 1 - cond col 0 1) (y₁ := z 1 - R' + M' - cond col 0 1) (by omega)
    (by omega) (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w hw).1, (C₅ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join Q hQe p hpe ht hw₄p
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₄ hp₄e hw₄p₄ hw₅p₄
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₅ hp₅e hw₅p₅ p₅.start_mem_support
  have GQ₂ : ∀ w ∈ Q₂.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      (w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 0 ∧ w 0 ≤ c₁ ∧ z 1 - R' - M' - cond col 0 1 ≤ w 1 ∧
          w 1 ≤ z 1 - R' + M' - cond col 0 1)) := by
    intro w hw
    rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · exact ⟨hQin w hw, Or.inl hw⟩
      · have := hp w hw
        exact ⟨hin w this.1 this.2.1 this.2.2.1 this.2.2.2, Or.inr (Or.inl hw)⟩
    · have := C₄ w hw
      exact ⟨hin w this.1 this.2.1 this.2.2.1 (by omega), Or.inr (Or.inr (by omega))⟩
  -- cut at the first exit from the interior
  have hc₅out : c₅ ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun hmem => by
    have := mem_cond_interior_iff.1 hmem
    omega
  obtain ⟨y, P, P', hPP', hy, hPin⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem Q₃ hc₅out
  have hPsub : ∀ w ∈ P.support, w ∈ Q₃.support := fun w hw => by
    rw [← hPP', SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  have hy₅ : y ∈ p₅.support := by
    rcases hQ₃s y (hPsub y P.end_mem_support) with h | h
    · exact absurd (GQ₂ y h).1 hy
    · exact h
  have hnil : ¬P.Nil := fun hn => hy (hn.eq ▸ (GQ₂ x₀ Q₂.start_mem_support).1)
  have hpen := mem_cond_interior_iff.1
    (hPin _ (SimpleGraph.Walk.penultimate_mem_dropLast_support hnil))
  have hadj := apply_le_apply_add_one_of_adj (SimpleGraph.Walk.adj_penultimate hnil).symm 1
  have Cy := C₅ y hy₅
  have hy₁ : y 1 = z 1 - R' - cond col 0 1 := by
    by_contra hne
    exact hy (hin y Cy.1 Cy.2.1 (by omega) (by omega))
  -- the new fence
  obtain ⟨p₅', hp₅'s, hp₅'e⟩ := exists_walk_of_mem_support_of_mem_support p₅
    p₅.start_mem_support hy₅
  obtain ⟨w₆, hw₆p₆, hw₆p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₆ p₅' (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 1 - R' - M' - cond col 0 1) (y₁ := z 1 - R' - 1 - cond col 0 1) (by omega)
    (by omega) (fun w hw => ⟨(C₆ w hw).2.2.1, (C₆ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w (hp₅'s w hw)).1, (C₅ w (hp₅'s w hw)).2.1⟩) (by omega) (by omega)
  obtain ⟨u', v', hu'p, hu', hv', hfen'⟩ := exists_mem_localConn_of_walk_zero p₆ hp₆e
    (x₀ := y 0) (y₀ := y 1 - M') (y₁ := y 1) (K := K')
    (fun w hw => ⟨by have := C₆ w hw; omega, by have := C₆ w hw; omega⟩) (by omega) (by omega)
  obtain ⟨k₁, hk₁s, hk₁e⟩ := exists_walk_of_mem_support_of_mem_support p₅' p₅'.end_mem_support
    hw₆p₅
  obtain ⟨k₂, hk₂s, hk₂e⟩ := exists_walk_of_mem_support_of_mem_support p₆ hw₆p₆ hu'p
  have hconn : cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (y - (M' : LatticeSite 2)) (y + M')) y u' := by
    refine mem_localConn_of_walk (k₁.append k₂) (fun w hw => ?_) (fun e he => ?_)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hw
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      rcases hw with hw | hw
      · have := C₅ w (hp₅'s w (hk₁s w hw))
        omega
      · have := C₆ w (hk₂s w hw)
        omega
    · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hp₅e e (hp₅'e e (hk₁e e he))
      · exact hp₆e e (hk₂e e he)
  refine ⟨y, P, fun e he => ?_, fun w hw => ?_, fun w hw hwout => ?_, hy, hy₁, Cy.1, Cy.2.1,
    y, SimpleGraph.Walk.start_mem_support _, u', v', hconn,
    Or.inr (Or.inr (Or.inl ⟨hy₁, hu', hv', hfen'⟩))⟩
  · have he' : e ∈ Q₃.edges := by
      rw [← hPP', SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    exact hQ₃e e he'
  · rcases hQ₃s w (hPsub w hw) with h | h
    · exact (GQ₂ w h).2
    · have := C₅ w h
      exact Or.inr (Or.inr (by omega))
  · rcases SimpleGraph.Walk.mem_dropLast_or_eq_of_mem_support hw with h | h
    · exact absurd (hPin w h) hwout
    · exact h

/-- **The leg of a jog on the bottom side**: `exists_walk_leg_top` reflected, with the rows of a
dual
arm shifted by `δ = cond col 0 1`: `V₁ = [x + K', x + W - K'] × [z₁ - h - W₀ - δ, z₁ - R - δ]`,
`H = [xl + K', xr + W - K'] × [z₁ - h - W₀ - δ, z₁ - h - δ]`,
`V₂ = [x + d + K', x + d + W - K'] × [z₁ - R' + 1 - δ, z₁ - h - δ]`. -/
theorem exists_walk_leg_bottom (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W)
    {h x d xl xr : ℤ} (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + 1 ≤ R')
    (hcl : z 0 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 0 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1
      ![x + K', z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1] ![x + W - K', z 1 - R - cond col 0 1])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0
      ![xl + K', z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1] ![xr + W - K', z 1 - h - cond col 0
          1])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d + K', z 1 - R' + 1 - cond col 0 1]
      ![x + d + W - K', z 1 - h - cond col 0 1])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₃ d₃ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₃ : (zdGraph 2).Walk c₃ d₃),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₃.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
        (w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
          w ∈ Icc (![x, z 1 - h - W - cond col 0 1] : LatticeSite 2)
            ![x + W, z 1 - R - cond col 0 1] ∨
          w ∈ Icc (![xl, z 1 - R' + 1 - cond col 0 1] : LatticeSite 2)
            ![xr + W, z 1 - h - cond col 0 1])) ∧
      (∀ w ∈ p₃.support, x + d + K' ≤ w 0 ∧ w 0 ≤ x + d + W - K' ∧
        z 1 - R' + 1 - cond col 0 1 ≤ w 1 ∧ w 1 ≤ z 1 - h - cond col 0 1) ∧
      c₃ 1 = z 1 - R' + 1 - cond col 0 1 ∧ d₃ 1 = z 1 - h - cond col 0 1 ∧ t ∈ p₃.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 1 = z 1 - R - cond col 0 1 ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1 - M] ![b 0 + K, b 1]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩
    · exfalso; omega
    · exfalso; omega
    · exact h
    · exfalso; omega
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the three crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hV₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hH
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂ hc₃ hd₃
  have Cg₀ : ∀ w ∈ g₀.support, b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M ∧ b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 0 - K ≤ w 0 ∧ w 0 ≤ b 0 + K ∧ b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, x + K' ≤ w 0 ∧ w 0 ≤ x + W - K' ∧
      z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1 ≤ w 1 ∧ w 1 ≤ z 1 - R - cond col 0 1 :=
    fun w hw => by
      have := hp₁ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₂ : ∀ w ∈ p₂.support, xl + K' ≤ w 0 ∧ w 0 ≤ xr + W - K' ∧
      z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1 ≤ w 1 ∧ w 1 ≤ z 1 - h - cond col 0 1 :=
    fun w hw => by
      have := hp₂ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₃ : ∀ w ∈ p₃.support, x + d + K' ≤ w 0 ∧ w 0 ≤ x + d + W - K' ∧
      z 1 - R' + 1 - cond col 0 1 ≤ w 1 ∧ w 1 ≤ z 1 - h - cond col 0 1 := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := b 1 - M) (y₁ := b 1) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1)
    (y₁ := z 1 - h - cond col 0 1) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc p₂ p₃
    (x₀ := x + d + K') (x₁ := x + d + W - K') (y₀ := z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1)
    (y₁ := z 1 - h - cond col 0 1) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₂ hp₂e hw₂p₂ hw₃p₂
  refine ⟨x₀, w₃, c₃, d₃, Q₃, p₃, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₃e, hp₃e, ?_, C₃, hc₃, hd₃,
    hw₃p₃⟩
  intro w hw
  rw [mem_cond_interior_iff]
  simp only [mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hQ₃s w hw with hw | hw
  · rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · have := Cg₀ w hw
        exact ⟨by omega, Or.inl (by omega)⟩
      · have := Cf w hw
        exact ⟨by omega, Or.inl (by omega)⟩
    · have := C₁ w hw
      exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
  · have := C₂ w hw
    exact ⟨by omega, Or.inr (Or.inr (by omega))⟩

/-- **The jog with a cap on the bottom side**: `exists_walk_of_jog_top` reflected, with the rows of
a
dual arm shifted by `δ = cond col 0 1`; the first exit `y` lies on the row `z₁ - R' - δ`. -/
theorem exists_walk_of_jog_bottom (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M)
    (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W ≤ M' + K') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R')
    (hcl : z 0 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 0 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 1
      ![x + K', z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1] ![x + W - K', z 1 - R - cond col 0 1])
    (hH : cond col ω (dualConfig ω) ∈ crossing 0
      ![xl + K', z 1 - h - ((W : ℤ) - 2 * K') - cond col 0 1] ![xr + W - K', z 1 - h - cond col 0
          1])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d + K', z 1 - R' + 1 - cond col 0 1]
      ![x + d + W - K', z 1 - h - cond col 0 1])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d + K', z 1 - R' + 1 - cond col 0 1]
      ![x + d + W - K', z 1 - R' + M' - cond col 0 1])
    (hU : cond col ω (dualConfig ω) ∈ crossing 1 ![x + d + K', z 1 - R' - M' - cond col 0 1]
      ![x + d + W - K', z 1 - R' + M' - cond col 0 1])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 0 ![x + d, z 1 - R' - M' - cond col 0 1]
      ![x + d + W, z 1 - R' - 1 - cond col 0 1])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hb₀ : x ≤ b 0) (hb₀' : b 0 ≤ x + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![x, z 1 - h - W - cond col 0 1] : LatticeSite 2)
          ![x + W, z 1 - R - cond col 0 1] ∨
        v ∈ Icc (![xl, z 1 - R' - M' - cond col 0 1] : LatticeSite 2)
          ![xr + W, z 1 - h - cond col 0 1]) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 1 = z 1 - R' - cond col 0 1 ∧ x + d + K' ≤ y 0 ∧ y 0 ≤ x + d + W - K' ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₃, d₃, Q, p₃, hx₀, hx₀M, hQe, hp₃e, hQ, hp₃, hc₃, hd₃, ht⟩ :=
    exists_walk_leg_bottom hM hWK hKM hK' hxl hxl' hxr hxr' hh (by omega) hcl hcr hMR hV₁ hH hV₂
      hb₁ hb₀ hb₀' hbR hbL hf
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_bottom
    (R' := R') (M' := M') (K' := K') (c₀ := x + d + K') (c₁ := x + d + W - K') hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe (fun w hw => (hQ w hw).1) p₃ hp₃e
    (fun w hw => by have := hp₃ w hw; omega) (by omega) (by omega) ht hHc
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hU
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hHf
    ⟨by simp, by simp⟩
    ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h | h | h
  · rcases (hQ w h).2 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · right
      right
      rw [mem_Icc_two_iff] at h' ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h' ⊢
      omega
  · have := hp₃ w h
    right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- `exists_walk_cap_top` with the coordinates exchanged (the right side). -/
theorem exists_walk_cap_right {c₀ c₁ : ℤ} (hM' : 2 ≤ M') (hc₀₁ : c₀ < c₁) (hWc : c₁ - c₀ + K' ≤ M')
    (hcx : z 1 - R' + 1 ≤ c₀) (hcx' : c₁ ≤ z 1 + R' - 1) (hRM' : M' ≤ R')
    {x₀ t c d : LatticeSite 2} (Q : (zdGraph 2).Walk x₀ t)
    (hQe : ∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω))
    (hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)))
    (p : (zdGraph 2).Walk c d) (hpe : ∀ e ∈ p.edges, e ∈ cond col ω (dualConfig ω))
    (hp : ∀ w ∈ p.support, c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 - R' + 1 - cond col 0 1 ≤ w 0 ∧
      w 0 ≤ z 0 + R' - 1)
    (hc : c 0 ≤ z 0 + R' - M') (hd : z 0 + R' - 1 ≤ d 0) (ht : t ∈ p.support)
    {lc hc' lu hu lf hf : LatticeSite 2}
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 lc hc')
    (hlc : lc 1 = c₀ ∧ lc 0 = z 0 + R' - M') (hhc : hc' 1 = c₁ ∧ hc' 0 = z 0 + R' - 1)
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 lu hu)
    (hlu : lu 1 = c₀ ∧ lu 0 = z 0 + R' - M') (hhu : hu 1 = c₁ ∧ hu 0 = z 0 + R' + M')
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 lf hf)
    (hlf : lf 1 = c₀ - K' ∧ lf 0 = z 0 + R' + 1) (hhf : hf 1 = c₁ + K' ∧ hf 0 = z 0 + R' + M') :
    ∃ (y : LatticeSite 2) (P : (zdGraph 2).Walk x₀ y),
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ P.support, w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 + R' - M' ≤ w 0 ∧ w 0 ≤ z 0 + R' + M')) ∧
      (∀ w ∈ P.support, w ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → w = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 + R' ∧ c₀ ≤ y 1 ∧ y 1 ≤ c₁ ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨c₄, -, hc₄, d₄, -, hd₄, h₄⟩ := hHc
  obtain ⟨p₄, hp₄, hp₄e⟩ := exists_walk_of_mem_localConn h₄
  obtain ⟨c₅, -, hc₅, d₅, -, hd₅, h₅⟩ := hU
  obtain ⟨p₅, hp₅, hp₅e⟩ := exists_walk_of_mem_localConn h₅
  obtain ⟨c₆, -, hc₆, d₆, -, hd₆, h₆⟩ := hHf
  obtain ⟨p₆, hp₆, hp₆e⟩ := exists_walk_of_mem_localConn h₆
  have C₄ : ∀ w ∈ p₄.support, c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 + R' - M' ≤ w 0 ∧
      w 0 ≤ z 0 + R' - 1 := fun w hw => by
    have := hp₄ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₅ : ∀ w ∈ p₅.support, c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 + R' - M' ≤ w 0 ∧
      w 0 ≤ z 0 + R' + M' := fun w hw => by
    have := hp₅ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₆ : ∀ w ∈ p₆.support, c₀ - K' ≤ w 1 ∧ w 1 ≤ c₁ + K' ∧ z 0 + R' + 1 ≤ w 0 ∧
      w 0 ≤ z 0 + R' + M' := fun w hw => by
    have := hp₆ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have hin : ∀ w : LatticeSite 2, c₀ ≤ w 1 → w 1 ≤ c₁ → z 0 - R' + 1 - cond col 0 1 ≤ w 0 →
      w 0 ≤ z 0 + R' - 1 → w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun w h₁ h₂ h₃ h₄ =>
    mem_cond_interior_iff.2 ⟨by omega, by omega, by omega, by omega⟩
  -- junctions of `p` with the connector and of the connector with the cap
  obtain ⟨w₄, hw₄p₄, hw₄p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₄ p (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 0 + R' - M') (y₁ := z 0 + R' - 1) (by omega) (by omega)
    (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(hp w hw).1, (hp w hw).2.1⟩) hc hd
  obtain ⟨w₅, hw₅p₄, hw₅p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₄ p₅ (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 0 + R' - M') (y₁ := z 0 + R' - 1) (by omega) (by omega)
    (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w hw).1, (C₅ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join Q hQe p hpe ht hw₄p
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₄ hp₄e hw₄p₄ hw₅p₄
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₅ hp₅e hw₅p₅ p₅.end_mem_support
  have GQ₂ : ∀ w ∈ Q₂.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      (w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 + R' - M' ≤ w 0 ∧ w 0 ≤ z 0 + R' + M')) := by
    intro w hw
    rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · exact ⟨hQin w hw, Or.inl hw⟩
      · have := hp w hw
        exact ⟨hin w this.1 this.2.1 this.2.2.1 this.2.2.2, Or.inr (Or.inl hw)⟩
    · have := C₄ w hw
      exact ⟨hin w this.1 this.2.1 (by omega) this.2.2.2, Or.inr (Or.inr (by omega))⟩
  -- cut at the first exit from the interior
  have hd₅out : d₅ ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun hmem => by
    have := mem_cond_interior_iff.1 hmem
    omega
  obtain ⟨y, P, P', hPP', hy, hPin⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem Q₃ hd₅out
  have hPsub : ∀ w ∈ P.support, w ∈ Q₃.support := fun w hw => by
    rw [← hPP', SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  have hy₅ : y ∈ p₅.support := by
    rcases hQ₃s y (hPsub y P.end_mem_support) with h | h
    · exact absurd (GQ₂ y h).1 hy
    · exact h
  have hnil : ¬P.Nil := fun hn => hy (hn.eq ▸ (GQ₂ x₀ Q₂.start_mem_support).1)
  have hpen := mem_cond_interior_iff.1
    (hPin _ (SimpleGraph.Walk.penultimate_mem_dropLast_support hnil))
  have hadj := apply_le_apply_add_one_of_adj (SimpleGraph.Walk.adj_penultimate hnil) 0
  have Cy := C₅ y hy₅
  have hy₁ : y 0 = z 0 + R' := by
    by_contra hne
    exact hy (hin y Cy.1 Cy.2.1 (by omega) (by omega))
  -- the new fence
  obtain ⟨p₅', hp₅'s, hp₅'e⟩ := exists_walk_of_mem_support_of_mem_support p₅ hy₅
    p₅.end_mem_support
  obtain ⟨w₆, hw₆p₆, hw₆p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₆ p₅' (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 0 + R' + 1) (y₁ := z 0 + R' + M') (by omega) (by omega)
    (fun w hw => ⟨(C₆ w hw).2.2.1, (C₆ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w (hp₅'s w hw)).1, (C₅ w (hp₅'s w hw)).2.1⟩) (by omega) (by omega)
  obtain ⟨u', v', hu'p, hu', hv', hfen'⟩ := exists_mem_localConn_of_walk_one p₆ hp₆e
    (x₀ := y 1) (y₀ := y 0) (y₁ := y 0 + M') (K := K')
    (fun w hw => ⟨by have := C₆ w hw; omega, by have := C₆ w hw; omega⟩) (by omega) (by omega)
  obtain ⟨k₁, hk₁s, hk₁e⟩ := exists_walk_of_mem_support_of_mem_support p₅' p₅'.start_mem_support
    hw₆p₅
  obtain ⟨k₂, hk₂s, hk₂e⟩ := exists_walk_of_mem_support_of_mem_support p₆ hw₆p₆ hu'p
  have hconn : cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (y - (M' : LatticeSite 2)) (y + M')) y u' := by
    refine mem_localConn_of_walk (k₁.append k₂) (fun w hw => ?_) (fun e he => ?_)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hw
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      rcases hw with hw | hw
      · have := C₅ w (hp₅'s w (hk₁s w hw))
        omega
      · have := C₆ w (hk₂s w hw)
        omega
    · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hp₅e e (hp₅'e e (hk₁e e he))
      · exact hp₆e e (hk₂e e he)
  refine ⟨y, P, fun e he => ?_, fun w hw => ?_, fun w hw hwout => ?_, hy, hy₁, Cy.1, Cy.2.1,
    y, SimpleGraph.Walk.start_mem_support _, u', v', hconn, Or.inr (Or.inl ⟨hy₁, hu', hv', hfen'⟩)⟩
  · have he' : e ∈ Q₃.edges := by
      rw [← hPP', SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    exact hQ₃e e he'
  · rcases hQ₃s w (hPsub w hw) with h | h
    · exact (GQ₂ w h).2
    · have := C₅ w h
      exact Or.inr (Or.inr (by omega))
  · rcases SimpleGraph.Walk.mem_dropLast_or_eq_of_mem_support hw with h | h
    · exact absurd (hPin w h) hwout
    · exact h

/-- `exists_walk_leg_top` with the coordinates exchanged (the right side). -/
theorem exists_walk_leg_right (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W)
    {h x d xl xr : ℤ} (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + 1 ≤ R')
    (hcl : z 1 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 1 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, x + K']
      ![z 0 + h + ((W : ℤ) - 2 * K'), x + W - K'])
    (hH : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + h, xl + K']
      ![z 0 + h + ((W : ℤ) - 2 * K'), xr + W - K'])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + h, x + d + K']
      ![z 0 + R' - 1, x + d + W - K'])
    (hb₁ : b 0 = z 0 + R) (hb₀ : x ≤ b 1) (hb₀' : b 1 ≤ x + W)
    (hbR : b 1 + 2 * M ≤ z 1 + R) (hbL : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₃ d₃ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₃ : (zdGraph 2).Walk c₃ d₃),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₃.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
        (w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
          w ∈ Icc (![z 0 + R, x] : LatticeSite 2) ![z 0 + h + W, x + W] ∨
          w ∈ Icc (![z 0 + h, xl] : LatticeSite 2) ![z 0 + R' - 1, xr + W])) ∧
      (∀ w ∈ p₃.support, x + d + K' ≤ w 1 ∧ w 1 ≤ x + d + W - K' ∧ z 0 + h ≤ w 0 ∧
        w 0 ≤ z 0 + R' - 1) ∧
      c₃ 0 = z 0 + h ∧ d₃ 0 = z 0 + R' - 1 ∧ t ∈ p₃.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 0 = z 0 + R ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0, b 1 - K] ![b 0 + M, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso; omega
    · exact h
    all_goals exfalso; omega
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the three crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hV₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hH
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂ hc₃ hd₃
  have Cg₀ : ∀ w ∈ g₀.support, b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M ∧ b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 1 - K ≤ w 1 ∧ w 1 ≤ b 1 + K ∧ b 0 ≤ w 0 ∧ w 0 ≤ b 0 + M :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, x + K' ≤ w 1 ∧ w 1 ≤ x + W - K' ∧ z 0 + R ≤ w 0 ∧
      w 0 ≤ z 0 + h + ((W : ℤ) - 2 * K') := fun w hw => by
    have := hp₁ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have C₂ : ∀ w ∈ p₂.support, xl + K' ≤ w 1 ∧ w 1 ≤ xr + W - K' ∧ z 0 + h ≤ w 0 ∧
      w 0 ≤ z 0 + h + ((W : ℤ) - 2 * K') := fun w hw => by
    have := hp₂ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have C₃ : ∀ w ∈ p₃.support, x + d + K' ≤ w 1 ∧ w 1 ≤ x + d + W - K' ∧ z 0 + h ≤ w 0 ∧
      w 0 ≤ z 0 + R' - 1 := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := b 0) (y₁ := b 0 + M) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := z 0 + h) (y₁ := z 0 + h + ((W : ℤ) - 2 * K')) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₃
    (x₀ := x + d + K') (x₁ := x + d + W - K') (y₀ := z 0 + h)
    (y₁ := z 0 + h + ((W : ℤ) - 2 * K')) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₂ hp₂e hw₂p₂ hw₃p₂
  refine ⟨x₀, w₃, c₃, d₃, Q₃, p₃, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₃e, hp₃e, ?_, C₃, hc₃, hd₃,
    hw₃p₃⟩
  intro w hw
  rw [mem_cond_interior_iff]
  simp only [mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hQ₃s w hw with hw | hw
  · rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · have := Cg₀ w hw
        exact ⟨by omega, Or.inl (by omega)⟩
      · have := Cf w hw
        exact ⟨by omega, Or.inl (by omega)⟩
    · have := C₁ w hw
      exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
  · have := C₂ w hw
    exact ⟨by omega, Or.inr (Or.inr (by omega))⟩

/-- `exists_walk_of_jog_top` with the coordinates exchanged (the right side). -/
theorem exists_walk_of_jog_right (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M)
    (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W ≤ M' + K') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R')
    (hcl : z 1 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 1 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, x + K']
      ![z 0 + h + ((W : ℤ) - 2 * K'), x + W - K'])
    (hH : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + h, xl + K']
      ![z 0 + h + ((W : ℤ) - 2 * K'), xr + W - K'])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + h, x + d + K']
      ![z 0 + R' - 1, x + d + W - K'])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' - M', x + d + K']
      ![z 0 + R' - 1, x + d + W - K'])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R' - M', x + d + K']
      ![z 0 + R' + M', x + d + W - K'])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 + R' + 1, x + d]
      ![z 0 + R' + M', x + d + W])
    (hb₁ : b 0 = z 0 + R) (hb₀ : x ≤ b 1) (hb₀' : b 1 ≤ x + W)
    (hbR : b 1 + 2 * M ≤ z 1 + R) (hbL : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![z 0 + R, x] : LatticeSite 2) ![z 0 + h + W, x + W] ∨
        v ∈ Icc (![z 0 + h, xl] : LatticeSite 2) ![z 0 + R' + M', xr + W]) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 + R' ∧ x + d + K' ≤ y 1 ∧ y 1 ≤ x + d + W - K' ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₃, d₃, Q, p₃, hx₀, hx₀M, hQe, hp₃e, hQ, hp₃, hc₃, hd₃, ht⟩ :=
    exists_walk_leg_right hM hWK hKM hK' hxl hxl' hxr hxr' hh (by omega) hcl hcr hMR hV₁ hH hV₂ hb₁
        hb₀
      hb₀' hbR hbL hf
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_right
    (R' := R') (M' := M') (K' := K') (c₀ := x + d + K') (c₁ := x + d + W - K') hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe (fun w hw => (hQ w hw).1) p₃ hp₃e
    (fun w hw => by have := hp₃ w hw; omega) (by omega) (by omega) ht hHc
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hU
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hHf
    ⟨by simp, by simp⟩
    ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h | h | h
  · rcases (hQ w h).2 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · right
      right
      rw [mem_Icc_two_iff] at h' ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h' ⊢
      omega
  · have := hp₃ w h
    right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- `exists_walk_cap_bottom` with the coordinates exchanged (the left side). -/
theorem exists_walk_cap_left {c₀ c₁ : ℤ} (hM' : 2 ≤ M') (hc₀₁ : c₀ < c₁)
    (hWc : c₁ - c₀ + K' ≤ M') (hcx : z 1 - R' + 1 ≤ c₀) (hcx' : c₁ ≤ z 1 + R' - 1)
    (hRM' : M' ≤ R') {x₀ t c d : LatticeSite 2} (Q : (zdGraph 2).Walk x₀ t)
    (hQe : ∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω))
    (hQin : ∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)))
    (p : (zdGraph 2).Walk c d) (hpe : ∀ e ∈ p.edges, e ∈ cond col ω (dualConfig ω))
    (hp : ∀ w ∈ p.support, c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 - R' + 1 - cond col 0 1 ≤ w 0 ∧
      w 0 ≤ z 0 + R' - 1)
    (hc : c 0 ≤ z 0 - R' + 1 - cond col 0 1) (hd : z 0 - R' + M' - cond col 0 1 ≤ d 0)
    (ht : t ∈ p.support) {lc hc' lu hu lf hf : LatticeSite 2}
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 lc hc')
    (hlc : lc 1 = c₀ ∧ lc 0 = z 0 - R' + 1 - cond col 0 1)
    (hhc : hc' 1 = c₁ ∧ hc' 0 = z 0 - R' + M' - cond col 0 1)
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 lu hu)
    (hlu : lu 1 = c₀ ∧ lu 0 = z 0 - R' - M' - cond col 0 1)
    (hhu : hu 1 = c₁ ∧ hu 0 = z 0 - R' + M' - cond col 0 1)
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 lf hf)
    (hlf : lf 1 = c₀ - K' ∧ lf 0 = z 0 - R' - M' - cond col 0 1)
    (hhf : hf 1 = c₁ + K' ∧ hf 0 = z 0 - R' - 1 - cond col 0 1) :
    ∃ (y : LatticeSite 2) (P : (zdGraph 2).Walk x₀ y),
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ P.support, w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 - R' - M' - cond col 0 1 ≤ w 0 ∧
          w 0 ≤ z 0 - R' + M' - cond col 0 1)) ∧
      (∀ w ∈ P.support, w ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → w = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 - R' - cond col 0 1 ∧ c₀ ≤ y 1 ∧ y 1 ≤ c₁ ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨c₄, -, hc₄, d₄, -, hd₄, h₄⟩ := hHc
  obtain ⟨p₄, hp₄, hp₄e⟩ := exists_walk_of_mem_localConn h₄
  obtain ⟨c₅, -, hc₅, d₅, -, hd₅, h₅⟩ := hU
  obtain ⟨p₅, hp₅, hp₅e⟩ := exists_walk_of_mem_localConn h₅
  obtain ⟨c₆, -, hc₆, d₆, -, hd₆, h₆⟩ := hHf
  obtain ⟨p₆, hp₆, hp₆e⟩ := exists_walk_of_mem_localConn h₆
  have C₄ : ∀ w ∈ p₄.support, c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 - R' + 1 - cond col 0 1 ≤ w 0 ∧
      w 0 ≤ z 0 - R' + M' - cond col 0 1 := fun w hw => by
    have := hp₄ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₅ : ∀ w ∈ p₅.support, c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 - R' - M' - cond col 0 1 ≤ w 0 ∧
      w 0 ≤ z 0 - R' + M' - cond col 0 1 := fun w hw => by
    have := hp₅ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have C₆ : ∀ w ∈ p₆.support, c₀ - K' ≤ w 1 ∧ w 1 ≤ c₁ + K' ∧
      z 0 - R' - M' - cond col 0 1 ≤ w 0 ∧ w 0 ≤ z 0 - R' - 1 - cond col 0 1 := fun w hw => by
    have := hp₆ w hw
    rw [mem_Icc_two_iff] at this
    omega
  have hin : ∀ w : LatticeSite 2, c₀ ≤ w 1 → w 1 ≤ c₁ → z 0 - R' + 1 - cond col 0 1 ≤ w 0 →
      w 0 ≤ z 0 + R' - 1 → w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun w h₁ h₂ h₃ h₄ =>
    mem_cond_interior_iff.2 ⟨by omega, by omega, by omega, by omega⟩
  -- junctions of `p` with the connector and of the connector with the cap
  obtain ⟨w₄, hw₄p₄, hw₄p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₄ p (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 0 - R' + 1 - cond col 0 1) (y₁ := z 0 - R' + M' - cond col 0 1) (by omega)
    (by omega) (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(hp w hw).1, (hp w hw).2.1⟩) hc hd
  obtain ⟨w₅, hw₅p₄, hw₅p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₄ p₅ (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 0 - R' + 1 - cond col 0 1) (y₁ := z 0 - R' + M' - cond col 0 1) (by omega)
    (by omega) (fun w hw => ⟨(C₄ w hw).2.2.1, (C₄ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w hw).1, (C₅ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join Q hQe p hpe ht hw₄p
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₄ hp₄e hw₄p₄ hw₅p₄
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₅ hp₅e hw₅p₅ p₅.start_mem_support
  have GQ₂ : ∀ w ∈ Q₂.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      (w ∈ Q.support ∨ w ∈ p.support ∨
        (c₀ ≤ w 1 ∧ w 1 ≤ c₁ ∧ z 0 - R' - M' - cond col 0 1 ≤ w 0 ∧
          w 0 ≤ z 0 - R' + M' - cond col 0 1)) := by
    intro w hw
    rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · exact ⟨hQin w hw, Or.inl hw⟩
      · have := hp w hw
        exact ⟨hin w this.1 this.2.1 this.2.2.1 this.2.2.2, Or.inr (Or.inl hw)⟩
    · have := C₄ w hw
      exact ⟨hin w this.1 this.2.1 this.2.2.1 (by omega), Or.inr (Or.inr (by omega))⟩
  -- cut at the first exit from the interior
  have hc₅out : c₅ ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) := fun hmem => by
    have := mem_cond_interior_iff.1 hmem
    omega
  obtain ⟨y, P, P', hPP', hy, hPin⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem Q₃ hc₅out
  have hPsub : ∀ w ∈ P.support, w ∈ Q₃.support := fun w hw => by
    rw [← hPP', SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  have hy₅ : y ∈ p₅.support := by
    rcases hQ₃s y (hPsub y P.end_mem_support) with h | h
    · exact absurd (GQ₂ y h).1 hy
    · exact h
  have hnil : ¬P.Nil := fun hn => hy (hn.eq ▸ (GQ₂ x₀ Q₂.start_mem_support).1)
  have hpen := mem_cond_interior_iff.1
    (hPin _ (SimpleGraph.Walk.penultimate_mem_dropLast_support hnil))
  have hadj := apply_le_apply_add_one_of_adj (SimpleGraph.Walk.adj_penultimate hnil).symm 0
  have Cy := C₅ y hy₅
  have hy₁ : y 0 = z 0 - R' - cond col 0 1 := by
    by_contra hne
    exact hy (hin y Cy.1 Cy.2.1 (by omega) (by omega))
  -- the new fence
  obtain ⟨p₅', hp₅'s, hp₅'e⟩ := exists_walk_of_mem_support_of_mem_support p₅
    p₅.start_mem_support hy₅
  obtain ⟨w₆, hw₆p₆, hw₆p₅⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₆ p₅' (x₀ := c₀)
    (x₁ := c₁) (y₀ := z 0 - R' - M' - cond col 0 1) (y₁ := z 0 - R' - 1 - cond col 0 1) (by omega)
    (by omega) (fun w hw => ⟨(C₆ w hw).2.2.1, (C₆ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₅ w (hp₅'s w hw)).1, (C₅ w (hp₅'s w hw)).2.1⟩) (by omega) (by omega)
  obtain ⟨u', v', hu'p, hu', hv', hfen'⟩ := exists_mem_localConn_of_walk_one p₆ hp₆e
    (x₀ := y 1) (y₀ := y 0 - M') (y₁ := y 0) (K := K')
    (fun w hw => ⟨by have := C₆ w hw; omega, by have := C₆ w hw; omega⟩) (by omega) (by omega)
  obtain ⟨k₁, hk₁s, hk₁e⟩ := exists_walk_of_mem_support_of_mem_support p₅' p₅'.end_mem_support
    hw₆p₅
  obtain ⟨k₂, hk₂s, hk₂e⟩ := exists_walk_of_mem_support_of_mem_support p₆ hw₆p₆ hu'p
  have hconn : cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (y - (M' : LatticeSite 2)) (y + M')) y u' := by
    refine mem_localConn_of_walk (k₁.append k₂) (fun w hw => ?_) (fun e he => ?_)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hw
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      rcases hw with hw | hw
      · have := C₅ w (hp₅'s w (hk₁s w hw))
        omega
      · have := C₆ w (hk₂s w hw)
        omega
    · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hp₅e e (hp₅'e e (hk₁e e he))
      · exact hp₆e e (hk₂e e he)
  refine ⟨y, P, fun e he => ?_, fun w hw => ?_, fun w hw hwout => ?_, hy, hy₁, Cy.1, Cy.2.1,
    y, SimpleGraph.Walk.start_mem_support _, u', v', hconn,
    Or.inr (Or.inr (Or.inr ⟨hy₁, hu', hv', hfen'⟩))⟩
  · have he' : e ∈ Q₃.edges := by
      rw [← hPP', SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    exact hQ₃e e he'
  · rcases hQ₃s w (hPsub w hw) with h | h
    · exact (GQ₂ w h).2
    · have := C₅ w h
      exact Or.inr (Or.inr (by omega))
  · rcases SimpleGraph.Walk.mem_dropLast_or_eq_of_mem_support hw with h | h
    · exact absurd (hPin w h) hwout
    · exact h

/-- `exists_walk_leg_bottom` with the coordinates exchanged (the left side). -/
theorem exists_walk_leg_left (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W)
    {h x d xl xr : ℤ} (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + 1 ≤ R')
    (hcl : z 1 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 1 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 0
      ![z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1, x + K'] ![z 0 - R - cond col 0 1, x + W - K'])
    (hH : cond col ω (dualConfig ω) ∈ crossing 1
      ![z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1, xl + K'] ![z 0 - h - cond col 0 1, xr + W -
          K'])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' + 1 - cond col 0 1, x + d + K']
      ![z 0 - h - cond col 0 1, x + d + W - K'])
    (hb₁ : b 0 = z 0 - R - cond col 0 1) (hb₀ : x ≤ b 1) (hb₀' : b 1 ≤ x + W)
    (hbR : b 1 + 2 * M ≤ z 1 + R) (hbL : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x₀ t c₃ d₃ : LatticeSite 2) (Q : (zdGraph 2).Walk x₀ t) (p₃ : (zdGraph 2).Walk c₃ d₃),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ Q.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ p₃.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ w ∈ Q.support, w ∈ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
        (w ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
          w ∈ Icc (![z 0 - h - W - cond col 0 1, x] : LatticeSite 2)
            ![z 0 - R - cond col 0 1, x + W] ∨
          w ∈ Icc (![z 0 - R' + 1 - cond col 0 1, xl] : LatticeSite 2)
            ![z 0 - h - cond col 0 1, xr + W])) ∧
      (∀ w ∈ p₃.support, x + d + K' ≤ w 1 ∧ w 1 ≤ x + d + W - K' ∧
        z 0 - R' + 1 - cond col 0 1 ≤ w 0 ∧ w 0 ≤ z 0 - h - cond col 0 1) ∧
      c₃ 0 = z 0 - R' + 1 - cond col 0 1 ∧ d₃ 0 = z 0 - h - cond col 0 1 ∧ t ∈ p₃.support := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  -- the old fence
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 0 = z 0 - R - cond col 0 1 ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - M, b 1 - K] ![b 0, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact h
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  -- the three crossings
  obtain ⟨c₁, -, hc₁, d₁, -, hd₁, h₁⟩ := hV₁
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn h₁
  obtain ⟨c₂, -, hc₂, d₂, -, hd₂, h₂⟩ := hH
  obtain ⟨p₂, hp₂, hp₂e⟩ := exists_walk_of_mem_localConn h₂
  obtain ⟨c₃, -, hc₃, d₃, -, hd₃, h₃⟩ := hV₂
  obtain ⟨p₃, hp₃, hp₃e⟩ := exists_walk_of_mem_localConn h₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₁ hd₁ hc₂ hd₂ hc₃ hd₃
  have Cg₀ : ∀ w ∈ g₀.support, b 1 - M ≤ w 1 ∧ w 1 ≤ b 1 + M ∧ b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 + M :=
    fun w hw => by
      have := hg₀ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
      omega
  have Cf : ∀ w ∈ f.support, b 1 - K ≤ w 1 ∧ w 1 ≤ b 1 + K ∧ b 0 - M ≤ w 0 ∧ w 0 ≤ b 0 :=
    fun w hw => by
      have := hfs w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₁ : ∀ w ∈ p₁.support, x + K' ≤ w 1 ∧ w 1 ≤ x + W - K' ∧
      z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1 ≤ w 0 ∧ w 0 ≤ z 0 - R - cond col 0 1 :=
    fun w hw => by
      have := hp₁ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₂ : ∀ w ∈ p₂.support, xl + K' ≤ w 1 ∧ w 1 ≤ xr + W - K' ∧
      z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1 ≤ w 0 ∧ w 0 ≤ z 0 - h - cond col 0 1 :=
    fun w hw => by
      have := hp₂ w hw
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have C₃ : ∀ w ∈ p₃.support, x + d + K' ≤ w 1 ∧ w 1 ≤ x + d + W - K' ∧
      z 0 - R' + 1 - cond col 0 1 ≤ w 0 ∧ w 0 ≤ z 0 - h - cond col 0 1 := fun w hw => by
    have := hp₃ w hw
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  -- the junctions
  obtain ⟨w₁, hw₁f, hw₁p⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := b 0 - M) (y₁ := b 0) (by omega) (by omega)
    (fun w hw => ⟨(Cf w hw).2.2.1, (Cf w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂p₂, hw₂p₁⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₁ (x₀ := x + K')
    (x₁ := x + W - K') (y₀ := z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1)
    (y₁ := z 0 - h - cond col 0 1) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₁ w hw).1, (C₁ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨w₃, hw₃p₂, hw₃p₃⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap p₂ p₃
    (x₀ := x + d + K') (x₁ := x + d + W - K') (y₀ := z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1)
    (y₁ := z 0 - h - cond col 0 1) (by omega) (by omega)
    (fun w hw => ⟨(C₂ w hw).2.2.1, (C₂ w hw).2.2.2⟩) (by omega) (by omega)
    (fun w hw => ⟨(C₃ w hw).1, (C₃ w hw).2.1⟩) (by omega) (by omega)
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join g₀ hg₀e f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e p₁ hp₁e hw₁p hw₂p₁
  obtain ⟨Q₃, hQ₃e, hQ₃s⟩ := exists_walk_join Q₂ hQ₂e p₂ hp₂e hw₂p₂ hw₃p₂
  refine ⟨x₀, w₃, c₃, d₃, Q₃, p₃, hx₀, hg₀ x₀ g₀.start_mem_support, hQ₃e, hp₃e, ?_, C₃, hc₃, hd₃,
    hw₃p₃⟩
  intro w hw
  rw [mem_cond_interior_iff]
  simp only [mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hQ₃s w hw with hw | hw
  · rcases hQ₂s w hw with hw | hw
    · rcases hQ₁s w hw with hw | hw
      · have := Cg₀ w hw
        exact ⟨by omega, Or.inl (by omega)⟩
      · have := Cf w hw
        exact ⟨by omega, Or.inl (by omega)⟩
    · have := C₁ w hw
      exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
  · have := C₂ w hw
    exact ⟨by omega, Or.inr (Or.inr (by omega))⟩

/-- `exists_walk_of_jog_bottom` with the coordinates exchanged (the left side). -/
theorem exists_walk_of_jog_left (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M)
    (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W ≤ M' + K') {h x d xl xr : ℤ}
    (hxl : xl ≤ x) (hxl' : xl ≤ x + d) (hxr : x ≤ xr) (hxr' : x + d ≤ xr)
    (hh : (R : ℤ) + M ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R')
    (hcl : z 1 - R' + 1 ≤ xl - M) (hcr : xr + W + M ≤ z 1 + R' - 1) (hMR : M ≤ R)
    (hV₁ : cond col ω (dualConfig ω) ∈ crossing 0
      ![z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1, x + K'] ![z 0 - R - cond col 0 1, x + W - K'])
    (hH : cond col ω (dualConfig ω) ∈ crossing 1
      ![z 0 - h - ((W : ℤ) - 2 * K') - cond col 0 1, xl + K'] ![z 0 - h - cond col 0 1, xr + W -
          K'])
    (hV₂ : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' + 1 - cond col 0 1, x + d + K']
      ![z 0 - h - cond col 0 1, x + d + W - K'])
    (hHc : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - R' + 1 - cond col 0 1, x + d + K']
      ![z 0 - R' + M' - cond col 0 1, x + d + W - K'])
    (hU : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' - M' - cond col 0 1, x + d + K']
      ![z 0 - R' + M' - cond col 0 1, x + d + W - K'])
    (hHf : cond col ω (dualConfig ω) ∈ crossing 1 ![z 0 - R' - M' - cond col 0 1, x + d]
      ![z 0 - R' - 1 - cond col 0 1, x + d + W])
    (hb₁ : b 0 = z 0 - R - cond col 0 1) (hb₀ : x ≤ b 1) (hb₀' : b 1 ≤ x + W)
    (hbR : b 1 + 2 * M ≤ z 1 + R) (hbL : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![z 0 - h - W - cond col 0 1, x] : LatticeSite 2)
          ![z 0 - R - cond col 0 1, x + W] ∨
        v ∈ Icc (![z 0 - R' - M' - cond col 0 1, xl] : LatticeSite 2)
          ![z 0 - h - cond col 0 1, xr + W]) ∧
      (∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v = y) ∧
      y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
        (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
      y 0 = z 0 - R' - cond col 0 1 ∧ x + d + K' ≤ y 1 ∧ y 1 ≤ x + d + W - K' ∧
      HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk y y) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, t, c₃, d₃, Q, p₃, hx₀, hx₀M, hQe, hp₃e, hQ, hp₃, hc₃, hd₃, ht⟩ :=
    exists_walk_leg_left hM hWK hKM hK' hxl hxl' hxr hxr' hh (by omega) hcl hcr hMR hV₁ hH hV₂
      hb₁ hb₀ hb₀' hbR hbL hf
  obtain ⟨y, P, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ := exists_walk_cap_left
    (R' := R') (M' := M') (K' := K') (c₀ := x + d + K') (c₁ := x + d + W - K') hM' (by omega)
    (by omega) (by omega) (by omega) (by omega) Q hQe (fun w hw => (hQ w hw).1) p₃ hp₃e
    (fun w hw => by have := hp₃ w hw; omega) (by omega) (by omega) ht hHc
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hU
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨trivial, trivial⟩) hHf
    ⟨by simp, by simp⟩
    ⟨by simp, by simp⟩
  refine ⟨x₀, y, P, hx₀, hx₀M, hPe, fun w hw => ?_, hPout, hy, hy₁, hy₀, hy₀', hfen⟩
  rcases hPs w hw with h | h | h
  · rcases (hQ w h).2 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · right
      right
      rw [mem_Icc_two_iff] at h' ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h' ⊢
      omega
  · have := hp₃ w h
    right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · right
    right
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

end Jogs

/-! ### Jog corridors for one arm -/

section JogCorridors

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}
  {col : Bool} {z : LatticeSite 2} {R R' M K M' K' W₀ D κ S : ℕ} {x d h : ℤ}

/-- **The jog corridor of one arm on the top side.** For a bin `[x + D, x + D + W₀]` on the top side
of `B_R(z)`, a shift `|d| ≤ D` and a level `h`, the six crossings of `exists_walk_of_jog_top` (with
`xl = x`, `xr = x + 2D`) form an event `C` of the colour `col`, determined by pairs inside the box
`[x, x + W₀ + 2D] × [z₁ + R, z₁ + R' + M']` (enlarged by one at its upper corner for the dual
colour), of probability at least `c κ ^ 6` under the aspect bounds `hκV`, `hκH`, `hκC`; on `C` every
fenced arm ending in the bin is continued, through a region `Q` of that box which meets
`Icc (z - R - 1) (z + R)` only near the end, to the first exit from the interior of `B_{R'}(z)`, a
point of the top side above `[x + D + d + K', x + D + d + W₀ - K']` with an outer fence of length
`2K'` and depth `M'`. -/
theorem exists_corridor_jog_top (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W₀ ≤ K)
    (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K')
    (hd : -(D : ℤ) ≤ d) (hd' : d ≤ D) (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hMR : M ≤ R) (hMS : M ≤ S)
    (hS : M + D + W₀ + 1 ≤ 2 * S)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) :
    ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc (![x, z 1 + R] : LatticeSite 2) (![x + ↑(W₀ + 2 * D), z 1 + ↑(R' +
          M')] + cond col 0 1)) ∧
      Q ⊆ Icc (![x, z 1 + R] : LatticeSite 2) ![x + ↑(W₀ + 2 * D), z 1 + ↑(R' + M')] ∧
      (∀ b : LatticeSite 2, b 1 = z 1 + R → x + D ≤ b 0 → b 0 ≤ x + D + W₀ →
        ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
          v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), b 1 = z 1 + R →
        x + D ≤ b 0 → b 0 ≤ x + D + W₀ → z 0 - R + 2 * S ≤ b 0 → b 0 + 2 * S ≤ z 0 + R →
        HasOuterFence ω col z R M K γ →
        ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
          x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            (v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D + d + W₀ - K') ∧
              HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w + 2 * K' = W₀ := ⟨W₀ - 2 * K', by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hw' : (W₀ : ℤ) - 2 * K' = w := by omega
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hw'] at hκV hκH
  rw [hm'] at hκC
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  refine ⟨{ω | ∀ k, cond col ω (dualConfig ω) ∈ crossing (![1, 0, 1, 0, 1, 0] k) (![![x + D + K', z
      1 + R],
      ![x + K', z 1 + h],
      ![x + D + d + K', z 1 + h],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d, z 1 + R' + 1]] k) (![![x + D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + 2 * D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' + M'],
      ![x + D + d + W₀, z 1 + R' + M']] k)},
    {e | ∃ k, ∀ v ∈ e, v ∈ Icc ((![![x + D + K', z 1 + R],
      ![x + K', z 1 + h],
      ![x + D + d + K', z 1 + h],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d, z 1 + R' + 1]] : Fin 6 → LatticeSite 2) k)
      ((![![x + D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + 2 * D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' + M'],
      ![x + D + d + W₀, z 1 + R' + M']] : Fin 6 → LatticeSite 2) k + cond col 0 1)},
    {v | (x + D ≤ v 0 ∧ v 0 ≤ x + D + W₀ ∧ z 1 + R ≤ v 1 ∧ v 1 ≤ z 1 + h + W₀) ∨
      (x ≤ v 0 ∧ v 0 ≤ x + 2 * D + W₀ ∧ z 1 + h ≤ v 1 ∧ v 1 ≤ z 1 + R' + M')},
    measurableSet_setOf_forall_cond_crossing col _ _ _,
    fun ω ω' hωω' => forall_cond_crossing_iff_of_inter_eq col _ _ _ hωω',
    fun ω ω' hωω' hω k => cond_mem_crossing_of_cond_subset hωω' (hω k), ?_, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨k, hk⟩ v hv
    have hk' := hk v hv
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    fin_cases k
    · change v ∈ Icc (![x + D + K', z 1 + R] : LatticeSite 2) (![x + D + W₀ - K', z 1 + h + ((W₀ :
        ℤ) - 2 * K')] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + K', z 1 + h] : LatticeSite 2) (![x + 2 * D + W₀ - K', z 1 + h + ((W₀ :
        ℤ) - 2 * K')] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d + K', z 1 + h] : LatticeSite 2) (![x + D + d + W₀ - K', z 1 + R' -
        1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d + K', z 1 + R' - M'] : LatticeSite 2) (![x + D + d + W₀ - K', z 1
        + R' - 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d + K', z 1 + R' - M'] : LatticeSite 2) (![x + D + d + W₀ - K', z 1
        + R' + M'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d, z 1 + R' + 1] : LatticeSite 2) (![x + D + d + W₀, z 1 + R' + M']
        + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
  · intro v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hv with hv | hv <;> omega
  · intro b hb₁ hb₀ hb₀' v hv hvR
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_of_jog_top (M' := M') (K' := K') (R' := R') (h := h) (x := x + D) (d := d)
        (xl := x) (xr := x + 2 * D) hM hWK hKM hK' hM' hWM' (by omega) (by omega) (by omega)
        (by omega) (by omega) (by rw [hw']; omega) (by omega) (by omega) hMR (hω (0 : Fin 6))
        (hω (1 : Fin 6)) (hω (2 : Fin 6)) (hω (3 : Fin 6)) (hω (4 : Fin 6)) (hω (5 : Fin 6)) hb₁
        hb₀ hb₀' (by omega) (by omega) hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · right
        left
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
      · right
        right
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
    · rw [hPout v hv hvout]
      exact ⟨⟨hy₁, hy₀, hy₀'⟩, hfen⟩
  · have hwL : (w : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have b₀ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![x + D + K', z 1 + R] : LatticeSite 2) ![x + D + W₀ - K', z 1 + h + ((W₀ : ℤ) -
            2 * K')]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₁ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![x + K', z 1 + h] : LatticeSite 2) ![x + 2 * D + W₀ - K', z 1 + h + ((W₀ : ℤ) -
            2 * K')]) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₂ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![x + D + d + K', z 1 + h] : LatticeSite 2) ![x + D + d + W₀ - K', z 1 + R' -
            1]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₃ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![x + D + d + K', z 1 + R' - M'] : LatticeSite 2) ![x + D + d + W₀ - K', z 1 +
            R' - 1]) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₄ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![x + D + d + K', z 1 + R' - M'] : LatticeSite 2) ![x + D + d + W₀ - K', z 1 +
            R' + M']) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₅ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![x + D + d, z 1 + R' + 1] : LatticeSite 2) ![x + D + d + W₀, z 1 + R' + M']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have hκ : ∀ k : Fin 6, c κ ≤ law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![1, 0, 1, 0, 1, 0] k) (![![x + D + K', z 1 + R],
      ![x + K', z 1 + h],
      ![x + D + d + K', z 1 + h],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d, z 1 + R' + 1]] k) (![![x + D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + 2 * D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' + M'],
      ![x + D + d + W₀, z 1 + R' + M']] k)) := by
      intro k
      fin_cases k
      exacts [b₀, b₁, b₂, b₃, b₄, b₅]
    have := Finset.pow_card_le_prod Finset.univ (fun k => law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![1, 0, 1, 0, 1, 0] k) (![![x + D + K', z 1 + R],
      ![x + K', z 1 + h],
      ![x + D + d + K', z 1 + h],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d + K', z 1 + R' - M'],
      ![x + D + d, z 1 + R' + 1]] k) (![![x + D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + 2 * D + W₀ - K', z 1 + h + ((W₀ : ℤ) - 2 * K')],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' - 1],
      ![x + D + d + W₀ - K', z 1 + R' + M'],
      ![x + D + d + W₀, z 1 + R' + M']] k))) (c κ)
      (fun k _ => hκ k)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.trans (prod_law_le_law_setOf_forall_cond_crossing q col _ _ _)

/-- **The jog corridor of one arm on the bottom side**: `exists_corridor_jog_top` reflected
(`exists_walk_of_jog_bottom`), with the rows of a dual arm shifted by `cond col 0 1`. -/
theorem exists_corridor_jog_bottom (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W₀ ≤ K)
    (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K')
    (hd : -(D : ℤ) ≤ d) (hd' : d ≤ D) (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hMR : M ≤ R) (hMS : M ≤ S)
    (hS : M + D + W₀ + 1 ≤ 2 * S)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) :
    ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc (![x, z 1 - ↑(R' + M') - cond col 0 1] : LatticeSite 2) (![x + ↑(W₀
          + 2 * D), z 1 - R - cond col 0 1] + cond col 0 1)) ∧
      Q ⊆ Icc (![x, z 1 - ↑(R' + M') - cond col 0 1] : LatticeSite 2) ![x + ↑(W₀ + 2 * D), z 1 - R -
          cond col 0 1] ∧
      (∀ b : LatticeSite 2, b 1 = z 1 - R - cond col 0 1 → x + D ≤ b 0 → b 0 ≤ x + D + W₀ →
        ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
          v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), b 1 = z 1 - R - cond col 0 1 →
        x + D ≤ b 0 → b 0 ≤ x + D + W₀ → z 0 - R + 2 * S ≤ b 0 → b 0 + 2 * S ≤ z 0 + R →
        HasOuterFence ω col z R M K γ →
        ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
          x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            (v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D + d + W₀ - K') ∧
              HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w + 2 * K' = W₀ := ⟨W₀ - 2 * K', by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hw' : (W₀ : ℤ) - 2 * K' = w := by omega
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hw'] at hκV hκH
  rw [hm'] at hκC
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  refine ⟨{ω | ∀ k, cond col ω (dualConfig ω) ∈ crossing (![1, 0, 1, 0, 1, 0] k) (![![x + D + K', z
      1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' - M' - cond col 0 1],
      ![x + D + d, z 1 - R' - M' - cond col 0 1]] k) (![![x + D + W₀ - K', z 1 - R - cond col 0 1],
      ![x + 2 * D + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀, z 1 - R' - 1 - cond col 0 1]] k)},
    {e | ∃ k, ∀ v ∈ e, v ∈ Icc ((![![x + D + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' - M' - cond col 0 1],
      ![x + D + d, z 1 - R' - M' - cond col 0 1]] : Fin 6 → LatticeSite 2) k)
      ((![![x + D + W₀ - K', z 1 - R - cond col 0 1],
      ![x + 2 * D + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀, z 1 - R' - 1 - cond col 0 1]] : Fin 6 → LatticeSite 2) k + cond col 0 1)},
    {v | (x + D ≤ v 0 ∧ v 0 ≤ x + D + W₀ ∧ z 1 - h - W₀ - cond col 0 1 ≤ v 1 ∧ v 1 ≤ z 1 - R - cond
        col 0 1) ∨
      (x ≤ v 0 ∧ v 0 ≤ x + 2 * D + W₀ ∧ z 1 - R' - M' - cond col 0 1 ≤ v 1 ∧ v 1 ≤ z 1 - h - cond
          col 0 1)},
    measurableSet_setOf_forall_cond_crossing col _ _ _,
    fun ω ω' hωω' => forall_cond_crossing_iff_of_inter_eq col _ _ _ hωω',
    fun ω ω' hωω' hω k => cond_mem_crossing_of_cond_subset hωω' (hω k), ?_, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨k, hk⟩ v hv
    have hk' := hk v hv
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    fin_cases k
    · change v ∈ Icc (![x + D + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1] : LatticeSite 2)
        (![x + D + W₀ - K', z 1 - R - cond col 0 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1] : LatticeSite 2) (![x
        + 2 * D + W₀ - K', z 1 - h - cond col 0 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d + K', z 1 - R' + 1 - cond col 0 1] : LatticeSite 2) (![x + D + d +
        W₀ - K', z 1 - h - cond col 0 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d + K', z 1 - R' + 1 - cond col 0 1] : LatticeSite 2) (![x + D + d +
        W₀ - K', z 1 - R' + M' - cond col 0 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d + K', z 1 - R' - M' - cond col 0 1] : LatticeSite 2) (![x + D + d
        + W₀ - K', z 1 - R' + M' - cond col 0 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![x + D + d, z 1 - R' - M' - cond col 0 1] : LatticeSite 2) (![x + D + d + W₀,
        z 1 - R' - 1 - cond col 0 1] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
  · intro v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hv with hv | hv <;> omega
  · intro b hb₁ hb₀ hb₀' v hv hvR
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_of_jog_bottom (M' := M') (K' := K') (R' := R') (h := h) (x := x + D) (d := d)
        (xl := x) (xr := x + 2 * D) hM hWK hKM hK' hM' hWM' (by omega) (by omega) (by omega)
        (by omega) (by omega) (by rw [hw']; omega) (by omega) (by omega) hMR (hω (0 : Fin 6))
        (hω (1 : Fin 6)) (hω (2 : Fin 6)) (hω (3 : Fin 6)) (hω (4 : Fin 6)) (hω (5 : Fin 6)) hb₁
        hb₀ hb₀' (by omega) (by omega) hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · right
        left
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
      · right
        right
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
    · rw [hPout v hv hvout]
      exact ⟨⟨hy₁, hy₀, hy₀'⟩, hfen⟩
  · have hwL : (w : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have b₀ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![x + D + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1] : LatticeSite 2) ![x
            + D + W₀ - K', z 1 - R - cond col 0 1]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₁ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![x + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1] : LatticeSite 2) ![x + 2
            * D + W₀ - K', z 1 - h - cond col 0 1]) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₂ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![x + D + d + K', z 1 - R' + 1 - cond col 0 1] : LatticeSite 2) ![x + D + d + W₀
            - K', z 1 - h - cond col 0 1]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₃ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![x + D + d + K', z 1 - R' + 1 - cond col 0 1] : LatticeSite 2) ![x + D + d + W₀
            - K', z 1 - R' + M' - cond col 0 1]) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₄ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![x + D + d + K', z 1 - R' - M' - cond col 0 1] : LatticeSite 2) ![x + D + d +
            W₀ - K', z 1 - R' + M' - cond col 0 1]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₅ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![x + D + d, z 1 - R' - M' - cond col 0 1] : LatticeSite 2) ![x + D + d + W₀, z
            1 - R' - 1 - cond col 0 1]) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have hκ : ∀ k : Fin 6, c κ ≤ law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![1, 0, 1, 0, 1, 0] k) (![![x + D + K', z 1 - h -
            ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' - M' - cond col 0 1],
      ![x + D + d, z 1 - R' - M' - cond col 0 1]] k) (![![x + D + W₀ - K', z 1 - R - cond col 0 1],
      ![x + 2 * D + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀, z 1 - R' - 1 - cond col 0 1]] k)) := by
      intro k
      fin_cases k
      exacts [b₀, b₁, b₂, b₃, b₄, b₅]
    have := Finset.pow_card_le_prod Finset.univ (fun k => law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![1, 0, 1, 0, 1, 0] k) (![![x + D + K', z 1 - h -
            ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + K', z 1 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' + 1 - cond col 0 1],
      ![x + D + d + K', z 1 - R' - M' - cond col 0 1],
      ![x + D + d, z 1 - R' - M' - cond col 0 1]] k) (![![x + D + W₀ - K', z 1 - R - cond col 0 1],
      ![x + 2 * D + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - h - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀ - K', z 1 - R' + M' - cond col 0 1],
      ![x + D + d + W₀, z 1 - R' - 1 - cond col 0 1]] k))) (c κ)
      (fun k _ => hκ k)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.trans (prod_law_le_law_setOf_forall_cond_crossing q col _ _ _)

/-- `exists_corridor_jog_top` with the coordinates exchanged (the right side). -/
theorem exists_corridor_jog_right (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W₀ ≤ K)
    (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K')
    (hd : -(D : ℤ) ≤ d) (hd' : d ≤ D) (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hMR : M ≤ R) (hMS : M ≤ S)
    (hS : M + D + W₀ + 1 ≤ 2 * S)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) :
    ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc (![z 0 + R, x] : LatticeSite 2) (![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 *
          D)] + cond col 0 1)) ∧
      Q ⊆ Icc (![z 0 + R, x] : LatticeSite 2) ![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 * D)] ∧
      (∀ b : LatticeSite 2, b 0 = z 0 + R → x + D ≤ b 1 → b 1 ≤ x + D + W₀ →
        ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
          v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), b 0 = z 0 + R →
        x + D ≤ b 1 → b 1 ≤ x + D + W₀ → z 1 - R + 2 * S ≤ b 1 → b 1 + 2 * S ≤ z 1 + R →
        HasOuterFence ω col z R M K γ →
        ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
          x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            (v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀ - K') ∧
              HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w + 2 * K' = W₀ := ⟨W₀ - 2 * K', by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hw' : (W₀ : ℤ) - 2 * K' = w := by omega
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hw'] at hκV hκH
  rw [hm'] at hκC
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  refine ⟨{ω | ∀ k, cond col ω (dualConfig ω) ∈ crossing (![0, 1, 0, 1, 0, 1] k) (![![z 0 + R, x + D
      + K'],
      ![z 0 + h, x + K'],
      ![z 0 + h, x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' + 1, x + D + d]] k) (![![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + D + W₀ - K'],
      ![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + 2 * D + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀]] k)},
    {e | ∃ k, ∀ v ∈ e, v ∈ Icc ((![![z 0 + R, x + D + K'],
      ![z 0 + h, x + K'],
      ![z 0 + h, x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' + 1, x + D + d]] : Fin 6 → LatticeSite 2) k)
      ((![![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + D + W₀ - K'],
      ![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + 2 * D + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀]] : Fin 6 → LatticeSite 2) k + cond col 0 1)},
    {v | (x + D ≤ v 1 ∧ v 1 ≤ x + D + W₀ ∧ z 0 + R ≤ v 0 ∧ v 0 ≤ z 0 + h + W₀) ∨
      (x ≤ v 1 ∧ v 1 ≤ x + 2 * D + W₀ ∧ z 0 + h ≤ v 0 ∧ v 0 ≤ z 0 + R' + M')},
    measurableSet_setOf_forall_cond_crossing col _ _ _,
    fun ω ω' hωω' => forall_cond_crossing_iff_of_inter_eq col _ _ _ hωω',
    fun ω ω' hωω' hω k => cond_mem_crossing_of_cond_subset hωω' (hω k), ?_, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨k, hk⟩ v hv
    have hk' := hk v hv
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    fin_cases k
    · change v ∈ Icc (![z 0 + R, x + D + K'] : LatticeSite 2) (![z 0 + h + ((W₀ : ℤ) - 2 * K'), x +
        D + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 + h, x + K'] : LatticeSite 2) (![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + 2 *
        D + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 + h, x + D + d + K'] : LatticeSite 2) (![z 0 + R' - 1, x + D + d + W₀ -
        K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 + R' - M', x + D + d + K'] : LatticeSite 2) (![z 0 + R' - 1, x + D + d +
        W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 + R' - M', x + D + d + K'] : LatticeSite 2) (![z 0 + R' + M', x + D + d
        + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 + R' + 1, x + D + d] : LatticeSite 2) (![z 0 + R' + M', x + D + d + W₀]
        + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
  · intro v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hv with hv | hv <;> omega
  · intro b hb₁ hb₀ hb₀' v hv hvR
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_of_jog_right (M' := M') (K' := K') (R' := R') (h := h) (x := x + D) (d := d)
        (xl := x) (xr := x + 2 * D) hM hWK hKM hK' hM' hWM' (by omega) (by omega) (by omega)
        (by omega) (by omega) (by rw [hw']; omega) (by omega) (by omega) hMR (hω (0 : Fin 6))
        (hω (1 : Fin 6)) (hω (2 : Fin 6)) (hω (3 : Fin 6)) (hω (4 : Fin 6)) (hω (5 : Fin 6)) hb₁
        hb₀ hb₀' (by omega) (by omega) hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · right
        left
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
      · right
        right
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
    · rw [hPout v hv hvout]
      exact ⟨⟨hy₁, hy₀, hy₀'⟩, hfen⟩
  · have hwL : (w : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have b₀ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![z 0 + R, x + D + K'] : LatticeSite 2) ![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + D +
            W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₁ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![z 0 + h, x + K'] : LatticeSite 2) ![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + 2 * D +
            W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₂ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![z 0 + h, x + D + d + K'] : LatticeSite 2) ![z 0 + R' - 1, x + D + d + W₀ -
            K']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₃ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![z 0 + R' - M', x + D + d + K'] : LatticeSite 2) ![z 0 + R' - 1, x + D + d + W₀
            - K']) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₄ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![z 0 + R' - M', x + D + d + K'] : LatticeSite 2) ![z 0 + R' + M', x + D + d +
            W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₅ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![z 0 + R' + 1, x + D + d] : LatticeSite 2) ![z 0 + R' + M', x + D + d + W₀]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have hκ : ∀ k : Fin 6, c κ ≤ law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![0, 1, 0, 1, 0, 1] k) (![![z 0 + R, x + D + K'],
      ![z 0 + h, x + K'],
      ![z 0 + h, x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' + 1, x + D + d]] k) (![![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + D + W₀ - K'],
      ![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + 2 * D + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀]] k)) := by
      intro k
      fin_cases k
      exacts [b₀, b₁, b₂, b₃, b₄, b₅]
    have := Finset.pow_card_le_prod Finset.univ (fun k => law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![0, 1, 0, 1, 0, 1] k) (![![z 0 + R, x + D + K'],
      ![z 0 + h, x + K'],
      ![z 0 + h, x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' - M', x + D + d + K'],
      ![z 0 + R' + 1, x + D + d]] k) (![![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + D + W₀ - K'],
      ![z 0 + h + ((W₀ : ℤ) - 2 * K'), x + 2 * D + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' - 1, x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀ - K'],
      ![z 0 + R' + M', x + D + d + W₀]] k))) (c κ)
      (fun k _ => hκ k)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.trans (prod_law_le_law_setOf_forall_cond_crossing q col _ _ _)

/-- `exists_corridor_jog_bottom` with the coordinates exchanged (the left side). -/
theorem exists_corridor_jog_left (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W₀ ≤ K)
    (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K')
    (hd : -(D : ℤ) ≤ d) (hd' : d ≤ D) (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hMR : M ≤ R) (hMS : M ≤ S)
    (hS : M + D + W₀ + 1 ≤ 2 * S)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) :
    ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc (![z 0 - ↑(R' + M') - cond col 0 1, x] : LatticeSite 2) (![z 0 - R
          - cond col 0 1, x + ↑(W₀ + 2 * D)] + cond col 0 1)) ∧
      Q ⊆ Icc (![z 0 - ↑(R' + M') - cond col 0 1, x] : LatticeSite 2) ![z 0 - R - cond col 0 1, x +
          ↑(W₀ + 2 * D)] ∧
      (∀ b : LatticeSite 2, b 0 = z 0 - R - cond col 0 1 → x + D ≤ b 1 → b 1 ≤ x + D + W₀ →
        ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
          v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), b 0 = z 0 - R - cond col 0 1 →
        x + D ≤ b 1 → b 1 ≤ x + D + W₀ → z 1 - R + 2 * S ≤ b 1 → b 1 + 2 * S ≤ z 1 + R →
        HasOuterFence ω col z R M K γ →
        ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
          x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            (v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀ - K') ∧
              HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w + 2 * K' = W₀ := ⟨W₀ - 2 * K', by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = M' := ⟨M' - 1, by omega⟩
  have hw' : (W₀ : ℤ) - 2 * K' = w := by omega
  have hm' : (M' : ℤ) - 1 = m := by omega
  rw [hw'] at hκV hκH
  rw [hm'] at hκC
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  refine ⟨{ω | ∀ k, cond col ω (dualConfig ω) ∈ crossing (![0, 1, 0, 1, 0, 1] k) (![![z 0 - h - ((W₀
      : ℤ) - 2 * K') - cond col 0 1, x + D + K'],
      ![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d]] k) (![![z 0 - R - cond col 0 1, x + D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + 2 * D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' - 1 - cond col 0 1, x + D + d + W₀]] k)},
    {e | ∃ k, ∀ v ∈ e, v ∈ Icc ((![![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + D + K'],
      ![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d]] : Fin 6 → LatticeSite 2) k)
      ((![![z 0 - R - cond col 0 1, x + D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + 2 * D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' - 1 - cond col 0 1, x + D + d + W₀]] : Fin 6 → LatticeSite 2) k + cond col 0 1)},
    {v | (x + D ≤ v 1 ∧ v 1 ≤ x + D + W₀ ∧ z 0 - h - W₀ - cond col 0 1 ≤ v 0 ∧ v 0 ≤ z 0 - R - cond
        col 0 1) ∨
      (x ≤ v 1 ∧ v 1 ≤ x + 2 * D + W₀ ∧ z 0 - R' - M' - cond col 0 1 ≤ v 0 ∧ v 0 ≤ z 0 - h - cond
          col 0 1)},
    measurableSet_setOf_forall_cond_crossing col _ _ _,
    fun ω ω' hωω' => forall_cond_crossing_iff_of_inter_eq col _ _ _ hωω',
    fun ω ω' hωω' hω k => cond_mem_crossing_of_cond_subset hωω' (hω k), ?_, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨k, hk⟩ v hv
    have hk' := hk v hv
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    fin_cases k
    · change v ∈ Icc (![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + D + K'] : LatticeSite 2)
        (![z 0 - R - cond col 0 1, x + D + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + K'] : LatticeSite 2) (![z
        0 - h - cond col 0 1, x + 2 * D + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 - R' + 1 - cond col 0 1, x + D + d + K'] : LatticeSite 2) (![z 0 - h -
        cond col 0 1, x + D + d + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 - R' + 1 - cond col 0 1, x + D + d + K'] : LatticeSite 2) (![z 0 - R' +
        M' - cond col 0 1, x + D + d + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 - R' - M' - cond col 0 1, x + D + d + K'] : LatticeSite 2) (![z 0 - R' +
        M' - cond col 0 1, x + D + d + W₀ - K'] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
    · change v ∈ Icc (![z 0 - R' - M' - cond col 0 1, x + D + d] : LatticeSite 2) (![z 0 - R' - 1 -
        cond col 0 1, x + D + d + W₀] + cond col 0 1) at hk'
      rw [mem_Icc_two_iff] at hk'
      simp only [Pi.add_apply, cond_zero_one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hk'
      omega
  · intro v hv
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hv with hv | hv <;> omega
  · intro b hb₁ hb₀ hb₀' v hv hvR
    rw [mem_Icc_two_iff] at hvR ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
    rcases hv with hv | hv <;> omega
  · intro ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
    obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hPout, hy, hy₁, hy₀, hy₀', hfen⟩ :=
      exists_walk_of_jog_left (M' := M') (K' := K') (R' := R') (h := h) (x := x + D) (d := d)
        (xl := x) (xr := x + 2 * D) hM hWK hKM hK' hM' hWM' (by omega) (by omega) (by omega)
        (by omega) (by omega) (by rw [hw']; omega) (by omega) (by omega) hMR (hω (0 : Fin 6))
        (hω (1 : Fin 6)) (hω (2 : Fin 6)) (hω (3 : Fin 6)) (hω (4 : Fin 6)) (hω (5 : Fin 6)) hb₁
        hb₀ hb₀' (by omega) (by omega) hf
    refine ⟨x', y, P, hx', hx'M, hPe, fun v hv => ?_, hy, fun v hv hvout => ?_⟩
    · rcases hPs v hv with h' | h' | h'
      · exact Or.inl h'
      · right
        left
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
      · right
        right
        rw [mem_Icc_two_iff] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h'
        exact ⟨by omega, by omega, by omega, by omega⟩
    · rw [hPout v hv hvout]
      exact ⟨⟨hy₁, hy₀, hy₀'⟩, hfen⟩
  · have hwL : (w : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have hmL : (m : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hL
    have b₀ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + D + K'] : LatticeSite 2) ![z
            0 - R - cond col 0 1, x + D + W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₁ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + K'] : LatticeSite 2) ![z 0 -
            h - cond col 0 1, x + 2 * D + W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₂ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![z 0 - R' + 1 - cond col 0 1, x + D + d + K'] : LatticeSite 2) ![z 0 - h - cond
            col 0 1, x + D + d + W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₃ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![z 0 - R' + 1 - cond col 0 1, x + D + d + K'] : LatticeSite 2) ![z 0 - R' + M'
            - cond col 0 1, x + D + d + W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have b₄ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 0 (![z 0 - R' - M' - cond col 0 1, x + D + d + K'] : LatticeSite 2) ![z 0 - R' + M'
            - cond col 0 1, x + D + d + W₀ - K']) :=
      hCB.le_law_preimage_cond_crossing_zero col κ (w := w) (by omega) hwL
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    have b₅ : c κ ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
        crossing 1 (![z 0 - R' - M' - cond col 0 1, x + D + d] : LatticeSite 2) ![z 0 - R' - 1 -
            cond col 0 1, x + D + d + W₀]) :=
      hCB.le_law_preimage_cond_crossing_one col κ (w := m) (by omega) hmL
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
        (by simp only [Matrix.cons_val_zero]; omega)
    have hκ : ∀ k : Fin 6, c κ ≤ law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![0, 1, 0, 1, 0, 1] k) (![![z 0 - h - ((W₀ : ℤ) - 2
            * K') - cond col 0 1, x + D + K'],
      ![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d]] k) (![![z 0 - R - cond col 0 1, x + D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + 2 * D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' - 1 - cond col 0 1, x + D + d + W₀]] k)) := by
      intro k
      fin_cases k
      exacts [b₀, b₁, b₂, b₃, b₄, b₅]
    have := Finset.pow_card_le_prod Finset.univ (fun k => law q ((fun ω : Config (LatticeSite 2) =>
        cond col ω (dualConfig ω)) ⁻¹' crossing (![0, 1, 0, 1, 0, 1] k) (![![z 0 - h - ((W₀ : ℤ) - 2
            * K') - cond col 0 1, x + D + K'],
      ![z 0 - h - ((W₀ : ℤ) - 2 * K') - cond col 0 1, x + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' + 1 - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d + K'],
      ![z 0 - R' - M' - cond col 0 1, x + D + d]] k) (![![z 0 - R - cond col 0 1, x + D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + 2 * D + W₀ - K'],
      ![z 0 - h - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' + M' - cond col 0 1, x + D + d + W₀ - K'],
      ![z 0 - R' - 1 - cond col 0 1, x + D + d + W₀]] k))) (c κ)
      (fun k _ => hκ k)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.trans (prod_law_le_law_setOf_forall_cond_crossing q col _ _ _)

/-- **The jog corridor of one arm**, on any side (`hjog`: top, right, bottom, left): the box
`Icc lo hi` from the fat bin `Bf` (`[x, x + W₀ + 2D]` along the side) straight out to distance
`R' + M'`, the bin `B ⊆ Bf` (`[x + D, x + D + W₀]`) and the target `B'` on the same side of
`B_{R'}(z)` (`[x + D + d + K', x + D + d + W₀ - K']`). Packages `exists_corridor_jog_top` and the
three
other sides in the form used by `law_mul_prod_le_law_of_sides`. -/
theorem exists_corridor_jog (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W₀ ≤ K)
    (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K')
    (hd : -(D : ℤ) ≤ d) (hd' : d ≤ D) (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hMR : M ≤ R) (hMS : M ≤ S)
    (hS : M + D + W₀ + 1 ≤ 2 * S)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) {dir : Fin 2}
    {lo hi : LatticeSite 2} {Bf B B' : Set (LatticeSite 2)}
    (hjog : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + ↑(W₀ + 2 * D), z 1 + ↑(R' + M')] ∧
        (∀ b, b ∈ Bf ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        (∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        ∀ v, v ∈ B' ↔ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D + d + W₀ - K') ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 * D)] ∧
        (∀ b, b ∈ Bf ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + ↑(W₀ + 2 * D) ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        (∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D + W₀ ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        ∀ v, v ∈ B' ↔ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀ - K') ∨
      (dir = 1 ∧ lo = ![x, z 1 - ↑(R' + M') - cond col 0 1] ∧
        hi = ![x + ↑(W₀ + 2 * D), z 1 - R - cond col 0 1] ∧
        (∀ b, b ∈ Bf ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        (∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        ∀ v, v ∈ B' ↔ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧
          v 0 ≤ x + D + d + W₀ - K') ∨
      (dir = 0 ∧ lo = ![z 0 - ↑(R' + M') - cond col 0 1, x] ∧
        hi = ![z 0 - R - cond col 0 1, x + ↑(W₀ + 2 * D)] ∧
        (∀ b, b ∈ Bf ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + ↑(W₀ + 2 * D) ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        (∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D + W₀ ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        ∀ v, v ∈ B' ↔ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧
          v 1 ≤ x + D + d + W₀ - K')) :
    ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc lo (hi + cond col 0 1)) ∧ Q ⊆ Icc lo hi ∧
      (∀ b ∈ B, ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
          v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), b ∈ B →
        HasOuterFence ω col z R M K γ →
        ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
          x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) → v ∈ B' ∧
            HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  rcases hjog with ⟨-, rfl, rfl, -, hB, hB'⟩ | ⟨-, rfl, rfl, -, hB, hB'⟩ | ⟨-, rfl, rfl, -, hB, hB'⟩
      |
    ⟨-, rfl, rfl, -, hB, hB'⟩
  · obtain ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := exists_corridor_jog_top (col := col)
      (z := z) (h := h) (d := d) hCB hM hWK hKM hK' hM' hWM' hd hd' hh hhR hMR hMS hS hκV hκH hκC hL
    refine ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, fun b hb => ?_, fun ω hω a b γ hb hf => ?_, h₈⟩
    · obtain ⟨hb₁, hb₀, hb₀', -, -⟩ := (hB b).1 hb
      exact h₆ b hb₁ hb₀ hb₀'
    · obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := (hB b).1 hb
      obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hy, hPout⟩ := h₇ ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
      exact ⟨x', y, P, hx', hx'M, hPe, hPs, hy, fun v hv hvout =>
        ⟨(hB' v).2 (hPout v hv hvout).1, (hPout v hv hvout).2⟩⟩
  · obtain ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := exists_corridor_jog_right (col := col)
      (z := z) (h := h) (d := d) hCB hM hWK hKM hK' hM' hWM' hd hd' hh hhR hMR hMS hS hκV hκH hκC hL
    refine ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, fun b hb => ?_, fun ω hω a b γ hb hf => ?_, h₈⟩
    · obtain ⟨hb₁, hb₀, hb₀', -, -⟩ := (hB b).1 hb
      exact h₆ b hb₁ hb₀ hb₀'
    · obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := (hB b).1 hb
      obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hy, hPout⟩ := h₇ ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
      exact ⟨x', y, P, hx', hx'M, hPe, hPs, hy, fun v hv hvout =>
        ⟨(hB' v).2 (hPout v hv hvout).1, (hPout v hv hvout).2⟩⟩
  · obtain ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := exists_corridor_jog_bottom (col := col)
      (z := z) (h := h) (d := d) hCB hM hWK hKM hK' hM' hWM' hd hd' hh hhR hMR hMS hS hκV hκH hκC hL
    refine ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, fun b hb => ?_, fun ω hω a b γ hb hf => ?_, h₈⟩
    · obtain ⟨hb₁, hb₀, hb₀', -, -⟩ := (hB b).1 hb
      exact h₆ b hb₁ hb₀ hb₀'
    · obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := (hB b).1 hb
      obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hy, hPout⟩ := h₇ ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
      exact ⟨x', y, P, hx', hx'M, hPe, hPs, hy, fun v hv hvout =>
        ⟨(hB' v).2 (hPout v hv hvout).1, (hPout v hv hvout).2⟩⟩
  · obtain ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := exists_corridor_jog_left (col := col)
      (z := z) (h := h) (d := d) hCB hM hWK hKM hK' hM' hWM' hd hd' hh hhR hMR hMS hS hκV hκH hκC hL
    refine ⟨C, T, Q, h₁, h₂, h₃, h₄, h₅, fun b hb => ?_, fun ω hω a b γ hb hf => ?_, h₈⟩
    · obtain ⟨hb₁, hb₀, hb₀', -, -⟩ := (hB b).1 hb
      exact h₆ b hb₁ hb₀ hb₀'
    · obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := (hB b).1 hb
      obtain ⟨x', y, P, hx', hx'M, hPe, hPs, hy, hPout⟩ := h₇ ω hω a b γ hb₁ hb₀ hb₀' hbL hbR hf
      exact ⟨x', y, P, hx', hx'M, hPe, hPs, hy, fun v hv hvout =>
        ⟨(hB' v).2 (hPout v hv hvout).1, (hPout v hv hvout).2⟩⟩

end JogCorridors

end PercLib.Models.Planar
