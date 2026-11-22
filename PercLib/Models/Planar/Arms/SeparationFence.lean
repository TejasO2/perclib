/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.2, condition (4.5) of Definition 6 (the free space and
its crossing, called a fence below), and Section 4.4, Lemma 15 (local separation, p. 1579).
-/
module

public import PercLib.Models.Planar.Arms.SeparationProtection

/-!
# Local separation of crossings: fences at the greedy tips

Nolin's well-separated crossings carry, at the top end `z` of each crossing, a small crossing of
the same colour in a box above `z` that is joined to the crossing inside a ball around `z` (his
condition (4.5); the box is the free space, its crossing the fence). This file proves the
deterministic step that produces it at the tip `z` of a greedy crossing, for any configuration `G`
and any box `Icc lo hi`.

Let `E` be the set of edges with a dual face in the explored set `A v`. Suppose that `G ∪ E`
crosses the four boxes around the annulus `t ≤ ‖· - z‖∞ ≤ 3t + 1` in their long directions (an
open circuit in which the explored edges count as open). Then every walk `γ` in the box from its
bottom row to `z`, meeting the top row only at `z`, open in `G` after the removals of step `v`
(in particular every rerouted crossing landing at `z`), is joined inside the ball of radius
`3t + 1` around `z`, by edges of `G`, to the left end of a left-right crossing of `G` of the top
box (`exists_fence_of_exploration`).

The proof follows the circuit clockwise: from the left end of the top crossing to the corner
square it shares with the right crossing, down the right crossing to the bottom crossing, along it
to the left crossing and up the left crossing to the top row. This walk enters the box only from
above and on the right of `z` (the circuit lies inside the box apart from its upper part), and its
last piece ends on the top row on the left of `z`, so by top separation it meets `γ`. Cut it at
its first vertex on `γ` or at a face of `A v`: top separation again shows that this vertex is on
`γ`, and every edge before it has no dual face in `A v`, so it is an edge of `G`.

The event "`G ∪ E` crosses the four boxes" is determined by the edges outside `E` and contains the
circuit event of `G`, so its probability is bounded below by the crossing bounds.

## Main results

* `exists_mem_support_of_mem_Icc_of_mem_Icc`: two walks crossing a rectangle in the two
  directions share a vertex.
* `exists_walk_entry_of_above`: the last entry from above of a walk into a half-plane.
* `exists_fence_of_exploration`: the fence at a greedy tip.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Walks in the plane -/

/-- A walk between two vertices of a walk, through vertices and edges of that walk. -/
theorem exists_walk_of_mem_support_of_mem_support {a b x y : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : (zdGraph 2).Walk x y, (∀ v ∈ q.support, v ∈ p.support) ∧
      ∀ e ∈ q.edges, e ∈ p.edges := by
  classical
  refine ⟨(p.takeUntil x hx).reverse.append (p.takeUntil y hy), fun v hv => ?_, fun e he => ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hv
    rcases hv with hv | hv
    · exact p.support_takeUntil_subset_support hx hv
    · exact p.support_takeUntil_subset_support hy hv
  · rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    rcases he with he | he
    · exact p.edges_takeUntil_subset_edges hx he
    · exact p.edges_takeUntil_subset_edges hy he

/-- **Two crossings of a rectangle.** A walk whose vertices stay in the rows `[y₀, y₁]` and that
runs from a column `≤ x₀` to a column `≥ x₁`, and a walk whose vertices stay in the columns
`[x₀, x₁]` and that runs from a row `≤ y₀` to a row `≥ y₁`, share a vertex. -/
theorem exists_mem_support_of_mem_Icc_of_mem_Icc {a b c d : LatticeSite 2}
    (p : (zdGraph 2).Walk a b) (q : (zdGraph 2).Walk c d) {x₀ x₁ y₀ y₁ : ℤ} (hx : x₀ ≤ x₁)
    (hy : y₀ < y₁) (hp : ∀ v ∈ p.support, y₀ ≤ v 1 ∧ v 1 ≤ y₁) (ha : a 0 ≤ x₀) (hb : x₁ ≤ b 0)
    (hq : ∀ v ∈ q.support, x₀ ≤ v 0 ∧ v 0 ≤ x₁) (hc : c 1 ≤ y₀) (hd : y₁ ≤ d 1) :
    ∃ v ∈ p.support, v ∈ q.support := by
  obtain ⟨u, w, hu, hw, p', hp'⟩ := SimpleGraph.Walk.exists_walk_mem_Icc
    (fun v : LatticeSite 2 => v 0) (fun u v h => apply_le_apply_add_one_of_adj h 0) p ha hx hb
  obtain ⟨u', w', hu', hw', q', hq'⟩ := SimpleGraph.Walk.exists_walk_mem_Icc
    (fun v : LatticeSite 2 => v 1) (fun u v h => apply_le_apply_add_one_of_adj h 1) q hc hy.le hd
  have hp'S : ∀ v ∈ p'.support, v ∈ Icc (![x₀, y₀] : LatticeSite 2) ![x₁, y₁] := by
    intro v hv
    obtain ⟨h₁, h₂, h₃⟩ := hp' v hv
    have := hp v h₁
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hq'S : ∀ v ∈ q'.support, v ∈ Icc (![x₀, y₀] : LatticeSite 2) ![x₁, y₁] := by
    intro v hv
    obtain ⟨h₁, h₂, h₃⟩ := hq' v hv
    have := hq v h₁
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  obtain ⟨v, hv, hv'⟩ := exists_mem_support_of_crossing_walks (lo := ![x₀, y₀]) (hi := ![x₁, y₁])
    (by simpa using hy) p' q' hp'S hq'S (by simpa using hu) (by simpa using hw)
    (by simpa using hu') (by simpa using hw')
  exact ⟨v, (hp' v hv).1, (hq' v hv').1⟩

/-- **Entering a half-plane from above.** A walk starting strictly above the row `y` and ending
on or below it has a vertex `o` on the row `y + 1` followed by a walk, inside it, from the point
of the row `y` directly below `o` to its end, all of whose vertices lie on or below the row
`y`. -/
theorem exists_walk_entry_of_above {a b : LatticeSite 2} (p : (zdGraph 2).Walk a b) {y : ℤ}
    (ha : y < a 1) (hb : b 1 ≤ y) :
    ∃ o ∈ p.support, o 1 = y + 1 ∧ ∃ r : (zdGraph 2).Walk ![o 0, y] b,
      (∀ v ∈ r.support, v ∈ p.support ∧ v 1 ≤ y) ∧ ∀ e ∈ r.edges, e ∈ p.edges := by
  obtain ⟨c, hc, q, r₀, hqr, hr₀⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
    (S := {v : LatticeSite 2 | y < v 1}) p ⟨a, p.start_mem_support, ha⟩
  have hsub : ∀ v ∈ r₀.support, v ∈ p.support := fun v hv => by
    rw [← hqr]
    exact (SimpleGraph.Walk.mem_support_append_iff q r₀).2 (Or.inr hv)
  have hesub : ∀ e ∈ r₀.edges, e ∈ p.edges := fun e he => by
    rw [← hqr, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases r₀ with
  | nil =>
    exfalso
    have : y < b 1 := hc
    omega
  | cons hadj r =>
    rename_i s
    have hr : ∀ v ∈ r.support, v 1 ≤ y := fun v hv => by
      have := hr₀ v (by rw [SimpleGraph.Walk.support_cons, List.tail_cons]; exact hv)
      simpa using this
    have hs := hr s r.start_mem_support
    have hc' : y < c 1 := hc
    rw [zdGraph_two_adj_iff] at hadj
    have hc1 : c 1 = y + 1 := by omega
    have hc0 : c 0 = s 0 := by omega
    have hs' : s = ![c 0, y] := eq_vec_two_iff.2 ⟨hc0.symm, by omega⟩
    subst hs'
    refine ⟨c, hsub c (SimpleGraph.Walk.start_mem_support _), hc1, r, fun v hv =>
      ⟨hsub v ?_, hr v hv⟩, fun e he => hesub e ?_⟩
    · rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ hv
    · rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_of_mem _ he

/-! ### The fence at a greedy tip -/

section Greedy

variable {lo hi : LatticeSite 2} {G : Config (LatticeSite 2)}
  {c d : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- **The fence at a greedy tip.** Let `A` be the exploration of `G` up to step `u`, `v ≤ u`, and
let `E` be the set of edges with a dual face in `A v`. Let `z` be a point of the top row of the
box and `t ≥ 1` a scale such that the annulus `t ≤ ‖· - z‖∞ ≤ 3t + 1` fits horizontally in the box
and has height at most that of the box. If `G ∪ E` crosses the four boxes around this annulus in
their long directions, then every walk `γ` in the box from its bottom row to `z`, meeting the top
row only at `z`, whose edges are open in `G` and have no end on a chosen crossing before step
`v`, has a vertex `x` joined inside the ball of radius `3t + 1` around `z`, by edges of `G`, to the
left end `l` of a left-right crossing, by edges of `G`, of the top box
`[z₀ - 3t, z₀ + 3t + 1] × [z₁ + t + 1, z₁ + 3t]`. -/
theorem exists_fence_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) {z : LatticeSite 2} (hz : z 1 = hi 1) {t : ℕ} (ht : 1 ≤ t)
    (hx₀ : lo 0 + 3 * t ≤ z 0) (hx₁ : z 0 + 3 * t + 1 ≤ hi 0) (hy₀ : lo 1 + 3 * t ≤ hi 1)
    (hT : G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
      crossing 0 (z + ![-3 * (t : ℤ), t + 1]) (z + ![3 * (t : ℤ) + 1, 3 * t]))
    (hB : G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
      crossing 0 (z + ![-3 * (t : ℤ), -3 * t + 1]) (z + ![3 * (t : ℤ) + 1, -t]))
    (hR : G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
      crossing 1 (z + ![(t : ℤ) + 1, -3 * t]) (z + ![3 * (t : ℤ), 3 * t + 1]))
    (hL : G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
      crossing 1 (z + ![-3 * (t : ℤ) + 1, -3 * t]) (z + ![-(t : ℤ), 3 * t + 1]))
    {a₁ : LatticeSite 2} (γ : (zdGraph 2).Walk a₁ z) (hγ : ∀ x ∈ γ.support, x ∈ Icc lo hi)
    (ha₁ : a₁ 1 = lo 1) (htop : ∀ x ∈ γ.support, x 1 = hi 1 → x = z)
    (hγG : ∀ e ∈ γ.edges, e ∈ G ∧ ∀ y ∈ e, ∀ w < v, y ∉ (Γ (A w)).support) :
    ∃ x ∈ γ.support, ∃ l r : LatticeSite 2, l 0 = z 0 - 3 * t ∧ r 0 = z 0 + 3 * t + 1 ∧
      G ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc (z + ![-3 * (t : ℤ), t + 1]) (z + ![3 * (t : ℤ) + 1, 3 * t])) l r ∧
      G ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ) + 1, 3 * t + 1])) x l := by
  classical
  -- the explored faces lie in the dual box
  have hAT : ∀ f ∈ A v, f 1 ≤ hi 1 - 1 := by
    intro f hf
    have hsub := exploredCluster_subset h1 (hle 0)
      (ζ := G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) rfl
    rw [hA v hv] at hsub
    have := mem_Icc_two_iff.1 (hsub hf)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  -- the four crossings
  obtain ⟨aT, -, haT0, bT, -, hbT0, hkT⟩ := hT
  obtain ⟨kT, hkTS, hkTE⟩ := exists_walk_of_mem_localConn hkT
  obtain ⟨aB, -, haB0, bB, -, hbB0, hkB⟩ := hB
  obtain ⟨kB, hkBS, hkBE⟩ := exists_walk_of_mem_localConn hkB
  obtain ⟨aR, -, haR1, bR, -, hbR1, hkR⟩ := hR
  obtain ⟨kR, hkRS, hkRE⟩ := exists_walk_of_mem_localConn hkR
  obtain ⟨aL, -, haL1, bL, -, hbL1, hkL⟩ := hL
  obtain ⟨kL, hkLS, hkLE⟩ := exists_walk_of_mem_localConn hkL
  simp only [Pi.add_apply, Matrix.cons_val_zero] at haT0 hbT0 haB0 hbB0
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at haR1 hbR1 haL1 hbL1
  have hT' : ∀ y ∈ kT.support, z 0 - 3 * t ≤ y 0 ∧ y 0 ≤ z 0 + 3 * t + 1 ∧
      z 1 + t + 1 ≤ y 1 ∧ y 1 ≤ z 1 + 3 * t := by
    intro y hy
    have := mem_Icc_two_iff.1 (hkTS y hy)
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have hB' : ∀ y ∈ kB.support, z 0 - 3 * t ≤ y 0 ∧ y 0 ≤ z 0 + 3 * t + 1 ∧
      z 1 - 3 * t + 1 ≤ y 1 ∧ y 1 ≤ z 1 - t := by
    intro y hy
    have := mem_Icc_two_iff.1 (hkBS y hy)
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have hR' : ∀ y ∈ kR.support, z 0 + t + 1 ≤ y 0 ∧ y 0 ≤ z 0 + 3 * t ∧
      z 1 - 3 * t ≤ y 1 ∧ y 1 ≤ z 1 + 3 * t + 1 := by
    intro y hy
    have := mem_Icc_two_iff.1 (hkRS y hy)
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have hL' : ∀ y ∈ kL.support, z 0 - 3 * t + 1 ≤ y 0 ∧ y 0 ≤ z 0 - t ∧
      z 1 - 3 * t ≤ y 1 ∧ y 1 ≤ z 1 + 3 * t + 1 := by
    intro y hy
    have := mem_Icc_two_iff.1 (hkLS y hy)
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  -- the three corners where consecutive crossings meet
  obtain ⟨pTR, hpTR, hpTR'⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc kT kR
    (x₀ := z 0 + t + 1) (x₁ := z 0 + 3 * t) (y₀ := z 1 + t + 1) (y₁ := z 1 + 3 * t)
    (by omega) (by omega) (fun y hy => ⟨(hT' y hy).2.2.1, (hT' y hy).2.2.2⟩) (by omega)
    (by omega) (fun y hy => ⟨(hR' y hy).1, (hR' y hy).2.1⟩) (by omega) (by omega)
  obtain ⟨pBR, hpBR, hpBR'⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc kB kR
    (x₀ := z 0 + t + 1) (x₁ := z 0 + 3 * t) (y₀ := z 1 - 3 * t + 1) (y₁ := z 1 - t)
    (by omega) (by omega) (fun y hy => ⟨(hB' y hy).2.2.1, (hB' y hy).2.2.2⟩) (by omega)
    (by omega) (fun y hy => ⟨(hR' y hy).1, (hR' y hy).2.1⟩) (by omega) (by omega)
  obtain ⟨pBL, hpBL, hpBL'⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc kB kL
    (x₀ := z 0 - 3 * t + 1) (x₁ := z 0 - t) (y₀ := z 1 - 3 * t + 1) (y₁ := z 1 - t)
    (by omega) (by omega) (fun y hy => ⟨(hB' y hy).2.2.1, (hB' y hy).2.2.2⟩) (by omega)
    (by omega) (fun y hy => ⟨(hL' y hy).1, (hL' y hy).2.1⟩) (by omega) (by omega)
  -- the walk around the circuit, clockwise from the left end of the top crossing
  obtain ⟨wT, hwTS, hwTE⟩ :=
    exists_walk_of_mem_support_of_mem_support kT kT.start_mem_support hpTR
  obtain ⟨wR, hwRS, hwRE⟩ := exists_walk_of_mem_support_of_mem_support kR hpTR' hpBR'
  obtain ⟨wB, hwBS, hwBE⟩ := exists_walk_of_mem_support_of_mem_support kB hpBR hpBL
  obtain ⟨wL₀, hwL₀S, hwL₀E⟩ :=
    exists_walk_of_mem_support_of_mem_support kL hpBL' kL.end_mem_support
  obtain ⟨o, ho, -, rL, hrLS, hrLE⟩ := exists_walk_entry_of_above wL₀.reverse (y := z 1)
    (by omega) (by have := hB' pBL hpBL; omega)
  have hoL : o ∈ kL.support := by
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ho
    exact hwL₀S o ho
  set W := wT.append (wR.append (wB.append rL.reverse)) with hW
  have hWS : ∀ y ∈ W.support, y ∈ kT.support ∨ y ∈ kR.support ∨ y ∈ kB.support ∨
      (y ∈ kL.support ∧ y 1 ≤ z 1) := by
    intro y hy
    rw [hW, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hy
    rcases hy with hy | hy | hy | hy
    · exact Or.inl (hwTS y hy)
    · exact Or.inr (Or.inl (hwRS y hy))
    · exact Or.inr (Or.inr (Or.inl (hwBS y hy)))
    · obtain ⟨hy', hy1⟩ := hrLS y hy
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy'
      exact Or.inr (Or.inr (Or.inr ⟨hwL₀S y hy', hy1⟩))
  have hWE : ∀ e ∈ W.edges, e ∈ G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} := by
    intro e he
    rw [hW, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_append, List.mem_append, List.mem_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he | he | he
    · exact hkTE e (hwTE e he)
    · exact hkRE e (hwRE e he)
    · exact hkBE e (hwBE e he)
    · have he' := hrLE e he
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he'
      exact hkLE e (hwL₀E e he')
  have hball : ∀ y ∈ W.support,
      y ∈ Icc (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ) + 1, 3 * t + 1]) := by
    intro y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hWS y hy with h | h | h | ⟨h, -⟩
    · have := hT' y h
      omega
    · have := hR' y h
      omega
    · have := hB' y h
      omega
    · have := hL' y h
      omega
  have habove : ∀ y ∈ W.support, hi 1 < y 1 → z 1 + t + 1 ≤ y 1 ∨ z 0 + t + 1 ≤ y 0 := by
    intro y hy hy1
    rcases hWS y hy with h | h | h | ⟨h, h'⟩
    · exact Or.inl (hT' y h).2.2.1
    · exact Or.inr (hR' y h).1
    · have := hB' y h
      omega
    · omega
  have hinbox : ∀ y ∈ W.support, y 1 ≤ hi 1 → y ∈ Icc lo hi := by
    intro y hy hy1
    have := mem_Icc_two_iff.1 (hball y hy)
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [mem_Icc_two_iff]
    omega
  have hstart : hi 1 < aT 1 := by
    have := hT' aT kT.start_mem_support
    omega
  -- the walk meets `γ`: its last piece in the box runs from the right of `z` on the top row to
  -- the left of `z` on the top row
  obtain ⟨o₀, ho₀, ho₀1, r₀, hr₀S, -⟩ := exists_walk_entry_of_above W (y := hi 1) hstart
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have ho₀0 : z 0 < o₀ 0 := by
    rcases habove o₀ ho₀ (by omega) with h | h <;> omega
  have hoL' := hL' o hoL
  have hrow : dualConfig {e | e ∈ γ.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
        ![lo 0 - 1, hi 1 - 1] ![o 0 - 1, hi 1 - 1] := by
    obtain ⟨ρ, hρ, hρe⟩ := exists_walk_row (hi 1 - 1) (show lo 0 - 1 ≤ o 0 - 1 by omega)
    rw [localConn_comm]
    refine mem_localConn_of_walk ρ (fun y hy => ?_) fun e he => ?_
    · obtain ⟨h₁, h₂, h₃⟩ := hρ y hy
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · obtain ⟨t', ht1, ht2, rfl⟩ := hρe e he
      have hv' : s(![t' + 1, hi 1 - 1], ![t' + 1, hi 1 - 1 + 1]) ∈ (zdGraph 2).edgeSet :=
        vertical_mem_edgeSet _ _
      have hdual : dualEdge s(![t' + 1, hi 1 - 1], ![t' + 1, hi 1 - 1 + 1]) =
          s(![t', hi 1 - 1], ![t' + 1, hi 1 - 1]) := by
        rw [dualEdge_vertical, Sym2.eq_swap, add_sub_cancel_right]
      rw [← hdual, dualEdge_mem_dualConfig_iff hv']
      intro hmem
      have hd' := htop _ (γ.snd_mem_support_of_mem_edges hmem) (by simp)
      have h0 := congrFun hd' 0
      simp only [Matrix.cons_val_zero] at h0
      omega
  obtain ⟨x₀, hx₀r, hx₀γ⟩ := exists_mem_support_of_lt_top h1 γ hγ ha₁ hz htop r₀
    (fun y hy => hinbox y (hr₀S y hy).1 (hr₀S y hy).2) (by simp) (by simpa using ho₀0)
    (f₀ := ![lo 0 - 1, hi 1 - 1]) (f₁ := ![o 0 - 1, hi 1 - 1]) (by simp)
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega) hrow
  have hx₀W : x₀ ∈ W.support := (hr₀S x₀ hx₀r).1
  -- cut the walk at its first vertex on `γ` or at an explored face
  obtain ⟨xs, W₁, s₁, hW₁, hxsR, hW₁R⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := {y | ¬(y ∈ γ.support ∨
      ∃ f ∈ A v, y 0 - 1 ≤ f 0 ∧ f 0 ≤ y 0 ∧ y 1 - 1 ≤ f 1 ∧ f 1 ≤ y 1)})
    (W.takeUntil x₀ hx₀W) (by simp [hx₀γ])
  have hW₁S : ∀ y ∈ W₁.support, y ∈ W.support := fun y hy => by
    have : y ∈ (W₁.append s₁).support := (SimpleGraph.Walk.mem_support_append_iff W₁ s₁).2
      (Or.inl hy)
    rw [hW₁] at this
    exact W.support_takeUntil_subset_support hx₀W this
  have hW₁E : ∀ e ∈ W₁.edges, e ∈ W.edges := fun e he => by
    have : e ∈ (W₁.append s₁).edges := by
      rw [SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    rw [hW₁] at this
    exact W.edges_takeUntil_subset_edges hx₀W this
  have hxsR' : xs ∈ γ.support ∨
      ∃ f ∈ A v, xs 0 - 1 ≤ f 0 ∧ f 0 ≤ xs 0 ∧ xs 1 - 1 ≤ f 1 ∧ f 1 ≤ xs 1 := by
    by_contra h
    exact hxsR h
  -- the cut vertex is on `γ`
  have hxsγ : xs ∈ γ.support := by
    by_contra hxs
    obtain ⟨f, hfA, hfx⟩ := hxsR'.resolve_left hxs
    have hxs1 : xs 1 ≤ hi 1 := by
      have := hAT f hfA
      omega
    obtain ⟨o₁, ho₁, ho₁1, r₁, hr₁S, -⟩ := exists_walk_entry_of_above W₁ (y := hi 1) hstart hxs1
    have ho₁0 : z 0 < o₁ 0 := by
      rcases habove o₁ (hW₁S o₁ ho₁) (by omega) with h | h <;> omega
    obtain ⟨y, hyr, hyγ⟩ := exists_mem_support_of_lt_top h1 γ hγ ha₁ hz htop r₁
      (fun y hy => hinbox y (hW₁S y (hr₁S y hy).1) (hr₁S y hy).2) (by simp)
      (by simpa using ho₁0) (f₀ := ![lo 0 - 1, lo 1]) (by simp) hfx
      (localConn_of_mem_exploration h1 hle hA hv hfA γ hγ hγG)
    have hyW₁ := (hr₁S y hyr).1
    by_cases hyx : y = xs
    · exact hxs (hyx ▸ hyγ)
    · exact hW₁R y (SimpleGraph.Walk.mem_dropLast_support_of_ne hyW₁ hyx) (Or.inl hyγ)
  -- the edges before the cut are fresh, hence edges of `G`
  have hW₁G : ∀ e ∈ W₁.edges, e ∈ G := by
    intro e he
    obtain ⟨y₁, y₂, rfl, hne, hy₁, hy₂⟩ := exists_ne_of_mem_edges W₁ he
    rcases hWE _ (hW₁E _ he) with hG | ⟨f, hf, hfA⟩
    · exact hG
    · exfalso
      have heL := W₁.edges_subset_edgeSet he
      by_cases h₁ : y₁ = xs
      · have h₂ : y₂ ≠ xs := fun h => hne (h₁.trans h.symm)
        exact hW₁R y₂ (SimpleGraph.Walk.mem_dropLast_support_of_ne hy₂ h₂)
          (Or.inr ⟨f, hfA, face_of_mem_dualEdge heL (Sym2.mem_mk_right _ _) hf⟩)
      · exact hW₁R y₁ (SimpleGraph.Walk.mem_dropLast_support_of_ne hy₁ h₁)
          (Or.inr ⟨f, hfA, face_of_mem_dualEdge heL (Sym2.mem_mk_left _ _) hf⟩)
  -- the top crossing lies above the box, so it is fresh
  have hkTG : ∀ e ∈ kT.edges, e ∈ G := by
    intro e he
    rcases hkTE e he with hG | ⟨f, hf, hfA⟩
    · exact hG
    · exfalso
      obtain ⟨y₁, y₂, rfl, -, hy₁, -⟩ := exists_ne_of_mem_edges kT he
      have h₁ := face_of_mem_dualEdge (kT.edges_subset_edgeSet he) (Sym2.mem_mk_left _ _) hf
      have h₂ := hT' y₁ hy₁
      have h₃ := hAT f hfA
      omega
  refine ⟨xs, hxsγ, aT, bT, by omega, by omega, mem_localConn_of_walk kT hkTS hkTG, ?_⟩
  refine mem_localConn_of_walk W₁.reverse (fun y hy => ?_) fun e he => ?_
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
    exact hball y (hW₁S y hy)
  · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact hW₁G e he

end Greedy

end PercLib.Models.Planar
