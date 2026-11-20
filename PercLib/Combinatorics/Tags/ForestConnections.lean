/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for the finite-forest branch-vertex assertion 4K33, proved from
`ForestBranching.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.ForestBranching

@[expose] public section
noncomputable section

open Finset
open scoped Classical

namespace PercLib

variable {W : Type*} [Fintype W]

/-- An isolated vertex is alone in its connected component, so there are at most as many
isolated vertices as components. -/
theorem card_isolated_le_card_connectedComponent (T : SimpleGraph W) [DecidableRel T.Adj] :
    (univ.filter fun v => T.degree v = 0).card ≤ Nat.card T.ConnectedComponent := by
  let : Fintype T.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← card_univ]
  refine card_le_card_of_injOn (fun v => T.connectedComponentMk v)
    (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  intro u hu v _ huv
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp huv
  cases p with
  | nil => rfl
  | cons hadj _ =>
    have h0 := (mem_filter.mp (mem_coe.mp hu)).2
    have hp := (T.degree_pos_iff_exists_adj _).mpr ⟨_, hadj⟩
    omega

/-- **4K33.** Let `T` be a finite forest with `c` connected components and `i` isolated vertices,
let `L` be its set of degree-one vertices and `B` its set of vertices of degree at least three.
Then `∑_v (deg v - 2) = -2c` (signed subtraction) and `|B| ≤ |L| - 2(c - i) ≤ |L|`. A finite tree
with at least two vertices has `|B| + 2 ≤ |L|`, and if a set `A` of at least two vertices contains
every leaf of a finite tree, then `|B| ≤ |A| - 2`. -/
@[tag "4K33"]
theorem forest_degree_excess_and_branch_bounds (T : SimpleGraph W) [DecidableRel T.Adj] :
    (T.IsAcyclic →
      ∑ v : W, ((T.degree v : ℤ) - 2) = -2 * Nat.card T.ConnectedComponent ∧
      ((univ.filter fun v => 3 ≤ T.degree v).card : ℤ) ≤
        (univ.filter fun v => T.degree v = 1).card -
          2 * ((Nat.card T.ConnectedComponent : ℤ) - (univ.filter fun v => T.degree v = 0).card) ∧
      ((univ.filter fun v => T.degree v = 1).card : ℤ) -
          2 * ((Nat.card T.ConnectedComponent : ℤ) - (univ.filter fun v => T.degree v = 0).card) ≤
        (univ.filter fun v => T.degree v = 1).card) ∧
    (T.IsTree → 2 ≤ Fintype.card W →
      (univ.filter fun v => 3 ≤ T.degree v).card + 2 ≤
        (univ.filter fun v => T.degree v = 1).card) ∧
    (T.IsTree → ∀ A : Finset W, (∀ v, T.degree v = 1 → v ∈ A) → 2 ≤ A.card →
      (univ.filter fun v => 3 ≤ T.degree v).card ≤ A.card - 2) := by
  refine ⟨fun hT => ?_, fun hT hW => ?_, fun hT A hA hcard =>
    tree_card_branch_le_card_sub_two T hT A hA hcard⟩
  · have hsum := forest_sum_degree_sub_two T hT
    have hic := card_isolated_le_card_connectedComponent T
    refine ⟨hsum, ?_, by omega⟩
    -- pointwise: `[deg ≥ 3] - [deg = 1] - 2 [deg = 0] ≤ deg - 2`
    have hpoint (v : W) : (if 3 ≤ T.degree v then (1 : ℤ) else 0) -
        (if T.degree v = 1 then 1 else 0) - 2 * (if T.degree v = 0 then 1 else 0) ≤
        (T.degree v : ℤ) - 2 := by
      split_ifs <;> omega
    have hle := sum_le_sum (s := (univ : Finset W)) (fun v _ => hpoint v)
    rw [hsum, sum_sub_distrib, sum_sub_distrib, ← mul_sum] at hle
    have hb : (∑ v : W, if 3 ≤ T.degree v then (1 : ℤ) else 0) =
        (univ.filter fun v => 3 ≤ T.degree v).card := by simp
    have hl : (∑ v : W, if T.degree v = 1 then (1 : ℤ) else 0) =
        (univ.filter fun v => T.degree v = 1).card := by simp
    have hi : (∑ v : W, if T.degree v = 0 then (1 : ℤ) else 0) =
        (univ.filter fun v => T.degree v = 0).card := by simp
    rw [hb, hl, hi] at hle
    linarith
  · have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact tree_card_branch_add_two_le_leaves T hT

end PercLib
