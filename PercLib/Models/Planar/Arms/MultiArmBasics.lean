/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Sections 3.1 and 4.1 (crossing bounds, arm events,
pp. 1570-1573).
-/
module

public import PercLib.Models.Planar.Arms.Interlacing
public import PercLib.Models.Planar.RSW
public import PercLib.Models.Planar.SelfDuality
public import PercLib.Probability.DeterminedIndependence

/-!
# Basic facts about multi-arm events

First consequences of the arms and multi-arm events of `Arms/Defs.lean` on the square lattice,
for families of arms of both colours: open arms (walks of `ℤ²` along open edges) and dual arms
(walks of faces along dual-open dual edges, the dual vertex `f` standing for the unit square
with lower-left corner `f`).

* **Crossing bounds at one half.** At the self-dual point the Russo–Seymour–Welsh bounds give
  open crossing bounds in any position and either direction at every scale, and self-duality
  gives the same bounds for dual crossings. So one `c` gives `CrossingBounds q ⊤ c` for every law
  with all edges of `ℤ²` open with probability `1/2`.
* **Doubled arms.** In the doubled lattice a point `v` becomes `2v`, a face `f` its centre
  `2f + (1, 1)` and an edge its midpoint. An open arm `v₀, …, v_m` becomes the walk
  `v₀ + v₁, 2v₁, v₁ + v₂, …, 2v_m` of `ℤ²` and a dual arm `f₀, …, f_m` the walk
  `2f₀ + 1, f₀ + f₁ + 1, 2f₁ + 1, …, f_{m-1} + f_m + 1`. With `B_r(z)` in the interior of the
  outer box `Icc lo hi`, the doubled arm starts on the boundary of the doubled inner box
  `2z + [-(2r + 1), 2r + 1]²` at the point of the inner position of the arm, meets that box
  nowhere else, stays in `Icc (2 lo) (2 hi)` and ends on its boundary at the point of the landing
  position. The doubled arms of a disjoint family are disjoint: doubled vertices of open arms come
  from their tails, which avoid each other; dual arms share no face; doubled vertices are
  even–even and doubled faces odd–odd; equal midpoints come from one edge; and an edge open in `ω`
  is never crossed by a dual edge open in `dualConfig ω`.
* **Order invariance for both colours.** The order invariance of `Interlacing.lean`, for disjoint
  walks of one lattice, applied to the doubled arms: three arms of a disjoint family have their
  inner positions in counterclockwise order exactly when their landing positions are.
* **Monotonicity in the radii.** Starting each arm at its last vertex or face touching a larger
  inner box keeps the landing positions; stopping each arm at its first exit from a smaller outer
  box keeps the inner positions, and order invariance at both boxes keeps the counterclockwise
  order of the landing positions. So `A_σ(r, R) ⊆ A_σ(r', R')` for `r ≤ r' < R' ≤ R`.
* **Upper half of quasi-multiplicativity.** `A_σ(r₁, r₂)` reads only edges inside `B_{r₂}(z)` and
  `A_σ(r₂, r₃)` only edges with an end outside `B_{r₂}(z)`, so the two events are independent, and
  by monotonicity `π_σ(r₁, r₃) ≤ π_σ(r₁, r₂) π_σ(r₂, r₃)` for every product law and
  `r₁ < r₂ < r₃`.

## Main results

* `exists_crossingBounds_half`: crossing bounds of both colours at every scale at `1/2`.
* `IsOpenArm.exists_double`, `IsDualArm.exists_double`, `IsArm.exists_double`: doubled arms, from
  `exists_walk_double`, `exists_walk_double_tail` and `exists_walk_double_dropLast`;
  `IsArm.double_disjoint`: the doubled arms of a disjoint family are disjoint.
* `sbtw_innerPos_iff_sbtw_landingPos`: order invariance for disjoint families of arms of both
  colours.
* `IsArm.exists_append_eq_of_le`, `IsArm.exists_append_eq_of_le_of_le`: an arm cut at a larger
  inner box or a smaller outer box is an arm.
* `multiArmEventTo_subset_of_le` (inner radius, landing windows kept),
  `multiArmEventTo_subset_of_le_of_le` (outer box, inner windows kept),
  `multiArmEvent_subset_of_le`: monotonicity in the radii.
* `law_multiArmEvent_le_mul`: the upper half of quasi-multiplicativity.
* `SimpleGraph.Walk.IsCrossing.exists_append_eq_isCrossing`,
  `SimpleGraph.Walk.IsCrossing.exists_append_eq_isCrossing_of_subset`: a crossing stopped at its
  first exit from a smaller set, or started at its last visit of a larger set, is a crossing.

## Implementation notes

* The monotonicity in the radii needs `r' < R'`. For `r' = R'` an arm from `B_{R'}(z)` to the
  boundary of `B_{R'}(z)` has no step, and the event no longer depends on the configuration. For
  instance, with twelve open arms `A_σ(1, 3)` contains the configuration with every edge open
  (twelve straight arms, one along each edge leaving `B_1(z)`), while `A_σ(1, 1)` is empty
  (twelve arms of length zero would need twelve distinct positions among the eight points of the
  boundary of `B_1(z)`). The same example shows that the upper half of quasi-multiplicativity
  needs `r₁ < r₂`.
* The doubled walks are given by existence statements with their supports described pointwise;
  no walk-valued function is defined.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- The second vertex of a walk followed by another walk is the second vertex of the first walk,
when it has a step. -/
theorem snd_append_of_not_nil {u v w : V} {p : G.Walk u v} (q : G.Walk v w) (hp : ¬p.Nil) :
    (p.append q).snd = p.snd := by
  cases p with
  | nil => exact absurd Nil.nil hp
  | cons h p => rw [cons_append, snd_cons, snd_cons]

/-- The last vertex but one of a walk followed by another walk is that of the second walk, when
it has a step. -/
theorem penultimate_append_of_not_nil {u v w : V} (p : G.Walk u v) {q : G.Walk v w}
    (hq : ¬q.Nil) : (p.append q).penultimate = q.penultimate := by
  rw [← snd_reverse, reverse_append, snd_append_of_not_nil _ (by rwa [nil_reverse]),
    snd_reverse]

/-- A dart of a walk leaving its start, when the walk never returns to its start, is the first
dart: it ends at the second vertex. -/
theorem snd_eq_of_mem_darts_of_fst_eq {u v : V} {p : G.Walk u v} {δ : G.Dart}
    (hδ : δ ∈ p.darts) (hfst : δ.fst = u) (hu : u ∉ p.support.tail) : δ.snd = p.snd := by
  cases p with
  | nil => simp at hδ
  | cons h q =>
    rw [darts_cons, List.mem_cons] at hδ
    rcases hδ with rfl | hδ
    · rw [snd_cons]
    · rw [support_cons, List.tail_cons] at hu
      exact absurd (hfst ▸ q.dart_fst_mem_support_of_mem_darts hδ) hu

/-- **First exit.** A walk ending outside a set `T` splits as a walk to its first vertex outside
`T` followed by the rest. -/
theorem exists_append_eq_of_notMem {T : Set V} :
    ∀ {u v : V} (p : G.Walk u v), v ∉ T → ∃ c, ∃ (q : G.Walk u c) (s : G.Walk c v),
      q.append s = p ∧ c ∉ T ∧ ∀ w ∈ q.support.dropLast, w ∈ T
  | u, _, .nil, hv => ⟨u, .nil, .nil, rfl, hv, by simp⟩
  | u, v, .cons h p, hv => by
    by_cases hu : u ∈ T
    · obtain ⟨c, q, s, hqs, hc, hq⟩ := exists_append_eq_of_notMem p hv
      refine ⟨c, .cons h q, s, by rw [cons_append, hqs], hc, fun w hw => ?_⟩
      rw [support_cons, List.dropLast_cons_of_ne_nil (support_ne_nil q), List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hu
      · exact hq w hw
    · exact ⟨u, .nil, .cons h p, rfl, hu, by simp⟩

/-- **Last visit.** A walk visiting a set `S` splits as a walk to its last vertex in `S` followed
by a walk that never returns to `S`. -/
theorem exists_append_eq_of_exists_mem {S : Set V} :
    ∀ {u v : V} (p : G.Walk u v), (∃ w ∈ p.support, w ∈ S) → ∃ c ∈ S,
      ∃ (q : G.Walk u c) (s : G.Walk c v), q.append s = p ∧ ∀ w ∈ s.support.tail, w ∉ S
  | u, _, .nil, hS => ⟨u, by simpa using hS, .nil, .nil, rfl, by simp⟩
  | u, v, .cons h p, hS => by
    by_cases hp : ∃ w ∈ p.support, w ∈ S
    · obtain ⟨c, hc, q, s, hqs, hs⟩ := exists_append_eq_of_exists_mem p hp
      exact ⟨c, hc, .cons h q, s, by rw [cons_append, hqs], hs⟩
    · have hu : u ∈ S := by
        obtain ⟨w, hw, hwS⟩ := hS
        rw [support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hwS
        · exact absurd ⟨w, hw, hwS⟩ hp
      refine ⟨u, hu, .nil, .cons h p, rfl, fun w hw hwS => hp ⟨w, ?_, hwS⟩⟩
      rwa [support_cons, List.tail_cons] at hw

variable {S T : Set V} {u v : V} {p : G.Walk u v}

/-- **Stopping a crossing earlier.** A crossing from `S` out of `T` stopped at its first vertex
outside a smaller set `T'` is a crossing from `S` out of `T'`. -/
theorem IsCrossing.exists_append_eq_isCrossing {T' : Set V} (h : p.IsCrossing S T)
    (hT' : T' ⊆ T) : ∃ c, ∃ (q : G.Walk u c) (s : G.Walk c v), q.append s = p ∧
      q.IsCrossing S T' := by
  obtain ⟨c, q, s, hqs, hc, hq⟩ := exists_append_eq_of_notMem (T := T') p
    fun hv => h.end_notMem (hT' hv)
  refine ⟨c, q, s, hqs, ⟨h.start_mem, fun w hw => h.notMem_of_mem_tail w ?_, hc, hq⟩⟩
  rw [← hqs, tail_support_append]
  exact List.mem_append_left _ hw

/-- **Starting a crossing later.** A crossing from `S` out of `T`, started at its last vertex in a
larger set `S'`, is a crossing from `S'` out of `T`. -/
theorem IsCrossing.exists_append_eq_isCrossing_of_subset {S' : Set V} (h : p.IsCrossing S T)
    (hS' : S ⊆ S') : ∃ c, ∃ (q : G.Walk u c) (s : G.Walk c v), q.append s = p ∧
      s.IsCrossing S' T := by
  obtain ⟨c, hc, q, s, hqs, hs⟩ := exists_append_eq_of_exists_mem (S := S') p
    ⟨u, p.start_mem_support, hS' h.start_mem⟩
  refine ⟨c, q, s, hqs, ⟨hc, hs, h.end_notMem, fun w hw => h.mem_of_mem_dropLast w ?_⟩⟩
  rw [← hqs, support_append_eq_support_dropLast_append,
    List.dropLast_append_of_ne_nil (support_ne_nil s)]
  exact List.mem_append_right _ hw

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Crossing bounds at one half -/

/-- **Crossing bounds at the self-dual point.** There are bounds `c` such that every law with
every edge of `ℤ²` open with probability `1/2` has crossing bounds of both colours at every scale:
the open bounds are the Russo–Seymour–Welsh bounds, and the dual crossings have the same
probabilities by self-duality. -/
theorem exists_crossingBounds_half :
    ∃ c : ℕ → ℝ≥0∞, ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → CrossingBounds q ⊤ c := by
  choose c hc hle using exists_pos_le_law_crossing
  refine ⟨c, fun q hq => ⟨hc, fun k i lo n hn _ => hle k q hq i lo n hn,
    fun k i lo n hn _ => ?_⟩⟩
  rw [law_preimage_dualConfig_eq hq (measurableSet_crossing _ _ _)
    (inter_edgeSet_mem_crossing_iff _ _ _)]
  exact hle k q hq i lo n hn

/-- Crossing bounds at every scale hold for the law with every pair open with probability
`1/2`. -/
example : ∃ c : ℕ → ℝ≥0∞,
    CrossingBounds (fun _ => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) ⊤ c := by
  obtain ⟨c, hc⟩ := exists_crossingBounds_half
  exact ⟨c, hc _ fun _ _ => rfl⟩

/-! ### Doubled walks -/

/-- **Doubling a walk.** A walk `v₀, v₁, …, v_m` of `ℤ²` gives the walk
`2v₀ + c, v₀ + v₁ + c, 2v₁ + c, …, 2v_m + c` of `ℤ²`, through the doubled vertices and the
midpoints of the steps (doubled), all translated by `c`. -/
theorem exists_walk_double (c : LatticeSite 2) {u v : LatticeSite 2}
    (γ : (zdGraph 2).Walk u v) :
    ∃ D : (zdGraph 2).Walk (2 • u + c) (2 • v + c), ∀ x, x ∈ D.support ↔
      (∃ w ∈ γ.support, x = 2 • w + c) ∨ ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + c := by
  induction γ with
  | nil => exact ⟨.nil, fun x => by simp⟩
  | @cons u u' v h p ih =>
    obtain ⟨D, hD⟩ := ih
    have h' := (zdGraph_two_adj_iff u u').1 h
    have h₁ : (zdGraph 2).Adj (2 • u + c) (u + u' + c) := by
      rw [zdGraph_two_adj_iff]
      simp only [Pi.add_apply, two_nsmul]
      omega
    have h₂ : (zdGraph 2).Adj (u + u' + c) (2 • u' + c) := by
      rw [zdGraph_two_adj_iff]
      simp only [Pi.add_apply, two_nsmul]
      omega
    refine ⟨.cons h₁ (.cons h₂ D), fun x => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hD, SimpleGraph.Walk.darts_cons,
      exists_eq_or_imp]
    constructor
    · rintro (rfl | rfl | (h | h))
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · rintro ((rfl | h) | (rfl | h))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr h))

/-- **Doubling a walk, without its first vertex.** A walk `v₀, v₁, …, v_m` of `ℤ²` with at least
one step gives the walk `v₀ + v₁ + c, 2v₁ + c, v₁ + v₂ + c, …, 2v_m + c`: the doubled walk cut
after its first step. This is the doubled walk of an open arm. -/
theorem exists_walk_double_tail (c : LatticeSite 2) {u v : LatticeSite 2}
    (γ : (zdGraph 2).Walk u v) (hγ : ¬γ.Nil) :
    ∃ D : (zdGraph 2).Walk (u + γ.snd + c) (2 • v + c), ∀ x, x ∈ D.support ↔
      (∃ w ∈ γ.support.tail, x = 2 • w + c) ∨ ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + c := by
  cases γ with
  | nil => exact absurd SimpleGraph.Walk.Nil.nil hγ
  | cons h p =>
    rename_i u'
    obtain ⟨D, hD⟩ := exists_walk_double c p
    have h' := (zdGraph_two_adj_iff _ _).1 h
    have h₂ : (zdGraph 2).Adj (u + u' + c) (2 • u' + c) := by
      rw [zdGraph_two_adj_iff]
      simp only [Pi.add_apply, two_nsmul]
      omega
    rw [SimpleGraph.Walk.snd_cons]
    refine ⟨.cons h₂ D, fun x => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons, List.mem_cons, hD,
      SimpleGraph.Walk.darts_cons, exists_eq_or_imp]
    constructor
    · rintro (rfl | h | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)

/-- **Doubling a walk, without its last vertex.** A walk `f₀, f₁, …, f_m` of `ℤ²` with at least
one step gives the walk `2f₀ + c, f₀ + f₁ + c, 2f₁ + c, …, 2f_{m-1} + c, f_{m-1} + f_m + c`: the
doubled walk cut before its last step. With `c = (1, 1)` this is the doubled walk of a dual arm
(faces become their centres in the doubled lattice). -/
theorem exists_walk_double_dropLast (c : LatticeSite 2) {u v : LatticeSite 2}
    (γ : (zdGraph 2).Walk u v) (hγ : ¬γ.Nil) :
    ∃ D : (zdGraph 2).Walk (2 • u + c) (γ.penultimate + v + c), ∀ x, x ∈ D.support ↔
      (∃ w ∈ γ.support.dropLast, x = 2 • w + c) ∨ ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + c := by
  have hr : ¬γ.reverse.Nil := by
    rwa [SimpleGraph.Walk.nil_reverse]
  obtain ⟨D, hD⟩ := exists_walk_double_tail c γ.reverse hr
  refine ⟨D.reverse.copy rfl (by rw [SimpleGraph.Walk.snd_reverse]; abel), fun x => ?_⟩
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse, List.mem_reverse, hD,
    SimpleGraph.Walk.support_reverse, List.tail_reverse, SimpleGraph.Walk.darts_reverse]
  simp only [List.mem_reverse, List.mem_map]
  constructor
  · rintro (h | ⟨δ, ⟨δ', hδ', rfl⟩, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨δ', hδ', ?_⟩
      simp only [SimpleGraph.Dart.symm, Prod.fst_swap, Prod.snd_swap]
      abel
  · rintro (h | ⟨δ, hδ, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨δ.symm, ⟨δ, hδ, rfl⟩, ?_⟩
      simp only [SimpleGraph.Dart.symm, Prod.fst_swap, Prod.snd_swap]
      abel

/-! ### Points of the doubled boxes -/

/-- Points of the doubled inner box `2z + [-(2r + 1), 2r + 1]²`, coordinate by coordinate. -/
theorem mem_Icc_innerBox_iff {z x : LatticeSite 2} {r : ℕ} :
    x ∈ Icc (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) ↔
      z 0 + z 0 - ((2 * r + 1 : ℕ) : ℤ) ≤ x 0 ∧ x 0 ≤ z 0 + z 0 + ((2 * r + 1 : ℕ) : ℤ) ∧
        z 1 + z 1 - ((2 * r + 1 : ℕ) : ℤ) ≤ x 1 ∧ x 1 ≤ z 1 + z 1 + ((2 * r + 1 : ℕ) : ℤ) := by
  rw [mem_Icc_two_iff]
  simp only [Pi.sub_apply, Pi.add_apply, two_nsmul, Pi.natCast_apply]

/-- Boundary points of the doubled inner box, coordinate by coordinate. -/
theorem mem_boxBoundary_innerBox_iff {z x : LatticeSite 2} {r : ℕ} :
    x ∈ boxBoundary (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) ↔
      (z 0 + z 0 - ((2 * r + 1 : ℕ) : ℤ) ≤ x 0 ∧ x 0 ≤ z 0 + z 0 + ((2 * r + 1 : ℕ) : ℤ) ∧
        z 1 + z 1 - ((2 * r + 1 : ℕ) : ℤ) ≤ x 1 ∧ x 1 ≤ z 1 + z 1 + ((2 * r + 1 : ℕ) : ℤ)) ∧
      (x 0 = z 0 + z 0 - ((2 * r + 1 : ℕ) : ℤ) ∨ x 0 = z 0 + z 0 + ((2 * r + 1 : ℕ) : ℤ) ∨
        x 1 = z 1 + z 1 - ((2 * r + 1 : ℕ) : ℤ) ∨ x 1 = z 1 + z 1 + ((2 * r + 1 : ℕ) : ℤ)) := by
  rw [mem_boxBoundary_two_iff]
  simp only [Pi.sub_apply, Pi.add_apply, two_nsmul, Pi.natCast_apply]

/-- Points of the doubled outer box `Icc (2 lo) (2 hi)`, coordinate by coordinate. -/
theorem mem_Icc_two_nsmul_iff {lo hi x : LatticeSite 2} :
    x ∈ Icc (2 • lo) (2 • hi) ↔ lo 0 + lo 0 ≤ x 0 ∧ x 0 ≤ hi 0 + hi 0 ∧
      lo 1 + lo 1 ≤ x 1 ∧ x 1 ≤ hi 1 + hi 1 := by
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, two_nsmul]

/-- Boundary points of the doubled outer box, coordinate by coordinate. -/
theorem mem_boxBoundary_two_nsmul_iff {lo hi x : LatticeSite 2} :
    x ∈ boxBoundary (2 • lo) (2 • hi) ↔ (lo 0 + lo 0 ≤ x 0 ∧ x 0 ≤ hi 0 + hi 0 ∧
      lo 1 + lo 1 ≤ x 1 ∧ x 1 ≤ hi 1 + hi 1) ∧
      (x 0 = lo 0 + lo 0 ∨ x 0 = hi 0 + hi 0 ∨ x 1 = lo 1 + lo 1 ∨ x 1 = hi 1 + hi 1) := by
  rw [mem_boxBoundary_two_iff]
  simp only [Pi.add_apply, two_nsmul]

/-- A box `B_r(z)` inside the interior of `Icc lo hi`, coordinate by coordinate. -/
theorem add_one_le_of_Icc_subset {z lo hi : LatticeSite 2} {r : ℕ}
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) :
    lo 0 + 1 ≤ z 0 - r ∧ z 0 + r ≤ hi 0 - 1 ∧ lo 1 + 1 ≤ z 1 - r ∧ z 1 + r ≤ hi 1 - 1 := by
  have hzr : z - (r : LatticeSite 2) ≤ z + r := fun i => by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    omega
  have h₁ := hB (left_mem_Icc.2 hzr)
  have h₂ := hB (right_mem_Icc.2 hzr)
  rw [mem_Icc_two_iff] at h₁ h₂
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ h₂
  omega

/-- **Midpoints determine edges.** Two edges of `ℤ²` with the same midpoint are equal. -/
theorem eq_and_eq_or_of_add_eq {u u' f f' : LatticeSite 2} (hu : (zdGraph 2).Adj u u')
    (hf : (zdGraph 2).Adj f f') (h : u + u' = f + f') : (u = f ∧ u' = f') ∨ (u = f' ∧ u' = f) := by
  rw [zdGraph_two_adj_iff] at hu hf
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply] at h0 h1
  simp only [funext_iff, Fin.forall_fin_two]
  omega

/-- **An edge and the dual edge crossing it have the same midpoint.** In the doubled lattice the
midpoint of the edge `{u, u'}` is `u + u'` and that of the dual edge `{f, f'}` is
`f + f' + (1, 1)`; when they agree, `{f, f'}` is the dual edge of `{u, u'}`. -/
theorem dualEdge_eq_of_add_eq {u u' f f' : LatticeSite 2} (hu : (zdGraph 2).Adj u u')
    (hf : (zdGraph 2).Adj f f') (h : u + u' = f + f' + 1) : dualEdge s(u, u') = s(f, f') := by
  rw [zdGraph_two_adj_iff] at hu hf
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.one_apply] at h0 h1
  rw [dualEdge_mk, Sym2.eq_iff]
  simp only [funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-! ### Doubled arms -/

section Doubling

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **The doubled open arm.** An open arm `v₀, …, v_m` from `B_r(z)` to the boundary of
`Icc lo hi` (with `B_r(z)` in the interior) gives a walk `v₀ + v₁, 2v₁, v₁ + v₂, …, 2v_m` of the
doubled lattice from the boundary of the doubled inner box `2z + [-(2r + 1), 2r + 1]²` to the
boundary of `Icc (2 lo) (2 hi)`, in `Icc (2 lo) (2 hi)` and meeting the inner box only at its
start. -/
theorem IsOpenArm.exists_double (h : IsOpenArm ω z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) :
    ∃ D : (zdGraph 2).Walk (a + γ.snd) (2 • b),
      (∀ x, x ∈ D.support ↔ (∃ w ∈ γ.support.tail, x = 2 • w + 0) ∨
        ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + 0) ∧
      a + γ.snd ∈ boxBoundary (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
        (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) ∧
      2 • b ∈ boxBoundary (2 • lo) (2 • hi) ∧
      ∀ x ∈ D.support, x ∈ Icc (2 • lo) (2 • hi) ∧
        (x ∈ Icc (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
          (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) → x = a + γ.snd) := by
  have hγ := h.not_nil hB
  have hc := add_one_le_of_Icc_subset hB
  obtain ⟨D, hD⟩ := exists_walk_double_tail 0 γ hγ
  have ha := h.isCrossing.start_mem
  have hs := h.isCrossing.snd_notMem hγ
  have hadj := (zdGraph_two_adj_iff _ _).1 (SimpleGraph.Walk.adj_snd hγ)
  have hb := h.end_mem_boxBoundary hγ
  rw [mem_Icc_two_iff] at ha hs
  rw [mem_boxBoundary_two_iff] at hb
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at ha hs
  refine ⟨D.copy (add_zero _) (add_zero _), fun x => by rw [SimpleGraph.Walk.support_copy, hD],
    ?_, ?_, fun x hx => ?_⟩
  · rw [mem_boxBoundary_innerBox_iff]
    simp only [Pi.add_apply]
    omega
  · rw [mem_boxBoundary_two_nsmul_iff]
    simp only [two_nsmul, Pi.add_apply]
    omega
  rw [SimpleGraph.Walk.support_copy, hD] at hx
  rcases hx with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩
  · have hwB := h.isCrossing.notMem_of_mem_tail w hw
    have hwO := h.mem_Icc hγ (List.mem_of_mem_tail hw)
    rw [mem_Icc_two_iff] at hwB hwO
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hwB
    rw [mem_Icc_two_nsmul_iff, mem_Icc_innerBox_iff]
    simp only [two_nsmul, Pi.add_apply, Pi.zero_apply, add_zero]
    exact ⟨by omega, fun hx => absurd hx (by omega)⟩
  · have hfst : δ.fst ∈ Icc (lo + 1) (hi - 1) := h.isCrossing.mem_of_mem_dropLast _ (by
      rw [← SimpleGraph.Walk.map_fst_darts]
      exact List.mem_map_of_mem hδ)
    have hsnd : δ.snd ∉ Icc (z - r) (z + r) := h.isCrossing.notMem_of_mem_tail _ (by
      rw [← SimpleGraph.Walk.map_snd_darts]
      exact List.mem_map_of_mem hδ)
    have hδadj := (zdGraph_two_adj_iff _ _).1 δ.adj
    have hO : δ.fst + δ.snd + 0 ∈ Icc (2 • lo) (2 • hi) := by
      rw [mem_Icc_two_iff] at hfst
      simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hfst
      rw [mem_Icc_two_nsmul_iff]
      simp only [Pi.add_apply, Pi.zero_apply, add_zero]
      omega
    refine ⟨hO, fun hx => ?_⟩
    rcases (SimpleGraph.Walk.mem_support_iff γ).1 (γ.dart_fst_mem_support_of_mem_darts hδ) with
      hf | hf
    · have hsnd' := SimpleGraph.Walk.snd_eq_of_mem_darts_of_fst_eq hδ hf
        (fun ha' => h.isCrossing.notMem_of_mem_tail a ha' h.isCrossing.start_mem)
      rw [hf, hsnd', add_zero]
    · have hfB := h.isCrossing.notMem_of_mem_tail _ hf
      rw [mem_Icc_two_iff] at hfB hsnd
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hfB hsnd
      rw [mem_Icc_innerBox_iff] at hx
      simp only [Pi.add_apply, Pi.zero_apply, add_zero] at hx
      omega

/-- **The doubled dual arm.** A dual arm `f₀, …, f_m` from `B_r(z)` to the boundary of
`Icc lo hi` (with `B_r(z)` in the interior) gives a walk
`2f₀ + 1, f₀ + f₁ + 1, 2f₁ + 1, …, 2f_{m-1} + 1, f_{m-1} + f_m + 1` of the doubled lattice
(faces become their centres) from the boundary of the doubled inner box
`2z + [-(2r + 1), 2r + 1]²` to the boundary of `Icc (2 lo) (2 hi)`, in `Icc (2 lo) (2 hi)` and
meeting the inner box only at its start. -/
theorem IsDualArm.exists_double (h : IsDualArm ω z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) :
    ∃ D : (zdGraph 2).Walk (2 • a + 1) (γ.penultimate + b + 1),
      (∀ x, x ∈ D.support ↔ (∃ w ∈ γ.support.dropLast, x = 2 • w + 1) ∨
        ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + 1) ∧
      2 • a + 1 ∈ boxBoundary (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
        (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) ∧
      γ.penultimate + b + 1 ∈ boxBoundary (2 • lo) (2 • hi) ∧
      ∀ x ∈ D.support, x ∈ Icc (2 • lo) (2 • hi) ∧
        (x ∈ Icc (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
          (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) → x = 2 • a + 1) := by
  have hγ := h.not_nil hB
  have hc := add_one_le_of_Icc_subset hB
  obtain ⟨D, hD⟩ := exists_walk_double_dropLast 1 γ hγ
  have ha := h.start_mem_boxBoundary hγ
  have hpen := h.isCrossing.penultimate_mem hγ
  have hbn := h.isCrossing.end_notMem
  have hadj := (zdGraph_two_adj_iff _ _).1 (SimpleGraph.Walk.adj_penultimate hγ)
  rw [mem_boxBoundary_two_iff] at ha
  rw [mem_Icc_two_iff] at hpen hbn
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at ha hpen hbn
  refine ⟨D, hD, ?_, ?_, fun x hx => ?_⟩
  · rw [mem_boxBoundary_innerBox_iff]
    simp only [Pi.add_apply, two_nsmul, Pi.one_apply]
    omega
  · rw [mem_boxBoundary_two_nsmul_iff]
    simp only [Pi.add_apply, Pi.one_apply]
    omega
  rw [hD] at hx
  rcases hx with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩
  · have hwO := h.isCrossing.mem_of_mem_dropLast w hw
    rw [mem_Icc_two_iff] at hwO
    simp only [Pi.sub_apply, Pi.one_apply] at hwO
    refine ⟨?_, fun hx => ?_⟩
    · rw [mem_Icc_two_nsmul_iff]
      simp only [two_nsmul, Pi.add_apply, Pi.one_apply]
      omega
    rcases (SimpleGraph.Walk.mem_support_iff γ).1 (List.mem_of_mem_dropLast hw) with rfl | hwt
    · rfl
    · have hwB := h.isCrossing.notMem_of_mem_tail w hwt
      rw [mem_Icc_two_iff] at hwB
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hwB
      rw [mem_Icc_innerBox_iff] at hx
      simp only [two_nsmul, Pi.add_apply, Pi.one_apply] at hx
      omega
  · have hfst : δ.fst ∈ Icc lo (hi - 1) := h.isCrossing.mem_of_mem_dropLast _ (by
      rw [← SimpleGraph.Walk.map_fst_darts]
      exact List.mem_map_of_mem hδ)
    have hsnd : δ.snd ∉ Icc (z - r - 1) (z + r) := h.isCrossing.notMem_of_mem_tail _ (by
      rw [← SimpleGraph.Walk.map_snd_darts]
      exact List.mem_map_of_mem hδ)
    have hδadj := (zdGraph_two_adj_iff _ _).1 δ.adj
    rw [mem_Icc_two_iff] at hfst hsnd
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hfst hsnd
    refine ⟨?_, fun hx => ?_⟩
    · rw [mem_Icc_two_nsmul_iff]
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    rw [mem_Icc_innerBox_iff] at hx
    simp only [Pi.add_apply, Pi.one_apply] at hx
    rcases (SimpleGraph.Walk.mem_support_iff γ).1 (γ.dart_fst_mem_support_of_mem_darts hδ) with
      hf | hf
    · rw [hf] at hδadj hx
      omega
    · have hfB := h.isCrossing.notMem_of_mem_tail _ hf
      rw [mem_Icc_two_iff] at hfB
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hfB
      omega

/-- **The doubled arm** of either colour (`IsOpenArm.exists_double`, `IsDualArm.exists_double`):
it starts at the point whose position is the inner position of the arm and ends at the point
whose position is its landing position. -/
theorem IsArm.exists_double {c : Bool} (h : IsArm ω c z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) :
    ∃ D : (zdGraph 2).Walk (cond c (a + γ.snd) (2 • a + 1))
        (cond c (2 • b) (γ.penultimate + b + 1)),
      (∀ x, x ∈ D.support ↔
        (∃ w ∈ cond c γ.support.tail γ.support.dropLast, x = 2 • w + cond c 0 1) ∨
          ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + cond c 0 1) ∧
      cond c (a + γ.snd) (2 • a + 1) ∈ boxBoundary (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
        (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) ∧
      cond c (2 • b) (γ.penultimate + b + 1) ∈ boxBoundary (2 • lo) (2 • hi) ∧
      ∀ x ∈ D.support, x ∈ Icc (2 • lo) (2 • hi) ∧
        (x ∈ Icc (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
          (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) → x = cond c (a + γ.snd) (2 • a + 1)) := by
  cases c
  · exact IsDualArm.exists_double h hB
  · exact IsOpenArm.exists_double h hB

/-- **Doubled arms of a disjoint family are disjoint.** Two doubled open arms share no point:
their doubled vertices come from the tails, which avoid each other, and equal midpoints are
midpoints of one edge. Two doubled dual arms share no point likewise. A doubled open arm and a
doubled dual arm share no point: doubled vertices are even–even, doubled faces odd–odd, and an
edge open in `ω` and a dual edge open in `dualConfig ω` never cross. -/
theorem IsArm.double_disjoint {c c' : Bool} {a' b' : LatticeSite 2} {γ' : (zdGraph 2).Walk a' b'}
    (h : IsArm ω c z r lo hi γ) (h' : IsArm ω c' z r lo hi γ')
    (hoo : c = true → c' = true → ∀ v ∈ γ.support.tail, v ∉ γ'.support)
    (hdd : c = false → c' = false → ∀ v ∈ γ.support, v ∉ γ'.support) {x : LatticeSite 2}
    (hx : (∃ w ∈ cond c γ.support.tail γ.support.dropLast, x = 2 • w + cond c 0 1) ∨
      ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + cond c 0 1)
    (hx' : (∃ w ∈ cond c' γ'.support.tail γ'.support.dropLast, x = 2 • w + cond c' 0 1) ∨
      ∃ δ ∈ γ'.darts, x = δ.fst + δ.snd + cond c' 0 1) : False := by
  -- an open edge is not crossed by an open dual edge
  have cross : ∀ {u u' f f' : LatticeSite 2}, (zdGraph 2).Adj u u' → (zdGraph 2).Adj f f' →
      u + u' = f + f' + 1 → s(u, u') ∈ ω → s(f, f') ∈ dualConfig ω → False := by
    intro u u' f f' hu hf heq hω hd
    rw [← dualEdge_eq_of_add_eq hu hf heq, dualEdge_mem_dualConfig_iff hu] at hd
    exact hd hω
  have hsnd : ∀ {u v : LatticeSite 2} {p : (zdGraph 2).Walk u v} {δ : (zdGraph 2).Dart},
      δ ∈ p.darts → δ.snd ∈ p.support.tail := fun hδ => by
    rw [← SimpleGraph.Walk.map_snd_darts]
    exact List.mem_map_of_mem hδ
  have hfst : ∀ {u v : LatticeSite 2} {p : (zdGraph 2).Walk u v} {δ : (zdGraph 2).Dart},
      δ ∈ p.darts → δ.fst ∈ p.support := fun hδ =>
    SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hδ
  have hsnd' : ∀ {u v : LatticeSite 2} {p : (zdGraph 2).Walk u v} {δ : (zdGraph 2).Dart},
      δ ∈ p.darts → δ.snd ∈ p.support := fun hδ =>
    SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hδ
  have hedge : ∀ {u v : LatticeSite 2} {p : (zdGraph 2).Walk u v} {δ : (zdGraph 2).Dart},
      δ ∈ p.darts → s(δ.fst, δ.snd) ∈ p.edges := fun hδ => List.mem_map_of_mem hδ
  cases c <;> cases c' <;> simp only [Bool.cond_true, Bool.cond_false] at hx hx'
  · -- two dual arms
    have hd := hdd rfl rfl
    rcases hx with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩ <;>
      rcases hx' with ⟨w', hw', heq⟩ | ⟨δ', hδ', heq⟩
    · have hww : w = w' := by
        funext i
        have := congrFun heq i
        simp only [Pi.add_apply, two_nsmul, Pi.one_apply] at this
        omega
      exact hd w (List.mem_of_mem_dropLast hw) (hww ▸ List.mem_of_mem_dropLast hw')
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ'.adj
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply] at e0 e1
      omega
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ.adj
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply] at e0 e1
      omega
    · rcases eq_and_eq_or_of_add_eq δ.adj δ'.adj (add_right_cancel heq) with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · exact hd _ (hfst hδ) (h₁ ▸ hfst hδ')
      · exact hd _ (hfst hδ) (h₁ ▸ hsnd' hδ')
  · -- a dual arm and an open arm
    rcases hx with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩ <;>
      rcases hx' with ⟨w', hw', heq⟩ | ⟨δ', hδ', heq⟩
    · have e0 := congrFun heq 0
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply, Pi.zero_apply] at e0
      omega
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ'.adj
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply, Pi.zero_apply] at e0 e1
      omega
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ.adj
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply, Pi.zero_apply] at e0 e1
      omega
    · rw [add_zero] at heq
      exact cross δ'.adj δ.adj heq.symm (h'.mem_of_mem_edges _ (hedge hδ'))
        (h.mem_of_mem_edges _ (hedge hδ))
  · -- an open arm and a dual arm
    rcases hx with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩ <;>
      rcases hx' with ⟨w', hw', heq⟩ | ⟨δ', hδ', heq⟩
    · have e0 := congrFun heq 0
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply, Pi.zero_apply] at e0
      omega
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ'.adj
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply, Pi.zero_apply] at e0 e1
      omega
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ.adj
      simp only [Pi.add_apply, two_nsmul, Pi.one_apply, Pi.zero_apply] at e0 e1
      omega
    · rw [add_zero] at heq
      exact cross δ.adj δ'.adj heq (h.mem_of_mem_edges _ (hedge hδ))
        (h'.mem_of_mem_edges _ (hedge hδ'))
  · -- two open arms
    have hd := hoo rfl rfl
    rcases hx with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩ <;>
      rcases hx' with ⟨w', hw', heq⟩ | ⟨δ', hδ', heq⟩
    · have hww : w = w' := by
        funext i
        have := congrFun heq i
        simp only [Pi.add_apply, two_nsmul, Pi.zero_apply] at this
        omega
      exact hd w hw (hww ▸ List.mem_of_mem_tail hw')
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ'.adj
      simp only [Pi.add_apply, two_nsmul, Pi.zero_apply] at e0 e1
      omega
    · have e0 := congrFun heq 0
      have e1 := congrFun heq 1
      have := (zdGraph_two_adj_iff _ _).1 δ.adj
      simp only [Pi.add_apply, two_nsmul, Pi.zero_apply] at e0 e1
      omega
    · rcases eq_and_eq_or_of_add_eq δ.adj δ'.adj (add_right_cancel heq) with ⟨-, h₂⟩ | ⟨-, h₂⟩
      · exact hd _ (hsnd hδ) (h₂ ▸ hsnd' hδ')
      · exact hd _ (hsnd hδ) (h₂ ▸ hfst hδ')

end Doubling

/-! ### Order invariance of arms of both colours -/

/-- **Order invariance of a disjoint family of arms of both colours.** Let `B_r(z)` lie in the
interior of `Icc lo hi` and let `γ` be a disjoint family of arms of colours `σ` from `B_r(z)` to
the boundary of `Icc lo hi`. Then three arms have their inner positions in counterclockwise
order exactly when they have their landing positions in counterclockwise order. This is the
order invariance of `Interlacing.lean` applied to the doubled arms, which are disjoint walks of
the doubled lattice from the doubled inner box to `Icc (2 lo) (2 hi)`. -/
theorem sbtw_innerPos_iff_sbtw_landingPos {j : ℕ} {σ : Fin j → Bool}
    {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i))
    (hd : ArmsDisjoint σ γ) (i k l : Fin j) :
    sbtw (innerPos z r (σ i) (γ i)) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) ↔
      sbtw (landingPos lo hi (σ i) (γ i)) (landingPos lo hi (σ k) (γ k))
        (landingPos lo hi (σ l) (γ l)) := by
  obtain ⟨c₁, c₂, c₃, c₄⟩ := add_one_le_of_Icc_subset hB
  choose D hDs hs he hDO using fun i => (hγ i).exists_double hB
  have h₀ : (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2)) 0 <
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) 0 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    omega
  have h₁ : (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2)) 1 <
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) 1 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    omega
  have hlo : 2 • lo + 1 ≤ 2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2) := by
    refine Pi.le_def.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, two_nsmul, Pi.one_apply]
      omega
  have hhi : 2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2) + 1 ≤ 2 • hi := by
    refine Pi.le_def.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    · simp only [Pi.add_apply, Pi.natCast_apply, two_nsmul, Pi.one_apply]
      omega
  have key := cyclicallyOrdered_end_iff_of_pairwise_disjoint h₀ h₁ hlo hhi D hs he hDO
    (fun i k hik x hx hx' => (hγ i).double_disjoint (hγ k) (hd.1 i k hik) (hd.2 i k hik)
      ((hDs i x).1 hx) ((hDs k x).1 hx')) i k l
  rw [Int.sbtw_iff, Int.sbtw_iff]
  exact key

/-! ### Cutting arms -/

section Cutting

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- An arm from a box inside the interior of the outer box has at least one step. -/
theorem IsArm.not_nil {c : Bool} (h : IsArm ω c z r lo hi γ)
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) : ¬γ.Nil := by
  cases c
  · exact IsDualArm.not_nil h hB
  · exact IsOpenArm.not_nil h hB

/-- The landing position of a walk depends only on its last step. -/
theorem landingPos_append {c : Bool} {x : LatticeSite 2} (q : (zdGraph 2).Walk a x)
    {s : (zdGraph 2).Walk x b} (hs : ¬s.Nil) :
    landingPos lo hi c (q.append s) = landingPos lo hi c s := by
  cases c
  · rw [landingPos_false, landingPos_false, SimpleGraph.Walk.penultimate_append_of_not_nil q hs]
  · rw [landingPos_true, landingPos_true]

/-- The inner position of a walk depends only on its first step. -/
theorem innerPos_append {c : Bool} {x : LatticeSite 2} {q : (zdGraph 2).Walk a x}
    (s : (zdGraph 2).Walk x b) (hq : ¬q.Nil) : innerPos z r c (q.append s) = innerPos z r c q := by
  cases c
  · rw [innerPos_false, innerPos_false]
  · rw [innerPos_true, innerPos_true, SimpleGraph.Walk.snd_append_of_not_nil s hq]

/-- **Cutting an arm at a larger inner box.** An arm from `B_r(z)`, started at its last vertex (open
arm) or face (dual arm) touching `B_{r'}(z)` for `r ≤ r'`, is an arm from `B_{r'}(z)`. -/
theorem IsArm.exists_append_eq_of_le {c : Bool} (h : IsArm ω c z r lo hi γ) {r' : ℕ}
    (hr : r ≤ r') : ∃ x, ∃ (q : (zdGraph 2).Walk a x) (s : (zdGraph 2).Walk x b),
      q.append s = γ ∧ IsArm ω c z r' lo hi s := by
  have hedges : ∀ {x : LatticeSite 2} {q : (zdGraph 2).Walk a x} {s : (zdGraph 2).Walk x b},
      q.append s = γ → ∀ e ∈ s.edges, e ∈ γ.edges := fun hqs e he => by
    rw [← hqs, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases c
  · have h' : IsDualArm ω z r lo hi γ := h
    obtain ⟨x, q, s, hqs, hs⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := Icc (z - r' - 1) (z + r')) (Icc_subset_Icc (fun i => by
        simp only [Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
        omega) fun i => by
        simp only [Pi.add_apply, Pi.natCast_apply]
        omega)
    exact ⟨x, q, s, hqs, hs, fun e he => h'.mem_of_mem_edges e (hedges hqs e he)⟩
  · have h' : IsOpenArm ω z r lo hi γ := h
    obtain ⟨x, q, s, hqs, hs⟩ := h'.isCrossing.exists_append_eq_isCrossing_of_subset
      (S' := Icc (z - r') (z + r')) (Icc_subset_Icc (fun i => by
        simp only [Pi.sub_apply, Pi.natCast_apply]
        omega) fun i => by
        simp only [Pi.add_apply, Pi.natCast_apply]
        omega)
    exact ⟨x, q, s, hqs, hs, fun e he => h'.mem_of_mem_edges e (hedges hqs e he)⟩

/-- **Cutting an arm at a smaller outer box.** An arm to the boundary of `Icc lo hi`, stopped at
its first vertex on the boundary of a smaller box `Icc lo' hi'` (open arm) or its first face
outside it (dual arm), is an arm to the boundary of `Icc lo' hi'`. -/
theorem IsArm.exists_append_eq_of_le_of_le {c : Bool} (h : IsArm ω c z r lo hi γ)
    {lo' hi' : LatticeSite 2} (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    ∃ x, ∃ (q : (zdGraph 2).Walk a x) (s : (zdGraph 2).Walk x b),
      q.append s = γ ∧ IsArm ω c z r lo' hi' q := by
  have hedges : ∀ {x : LatticeSite 2} {q : (zdGraph 2).Walk a x} {s : (zdGraph 2).Walk x b},
      q.append s = γ → ∀ e ∈ q.edges, e ∈ γ.edges := fun hqs e he => by
    rw [← hqs, SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ he
  cases c
  · have h' : IsDualArm ω z r lo hi γ := h
    obtain ⟨x, q, s, hqs, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing
      (T' := Icc lo' (hi' - 1)) (Icc_subset_Icc hlo (sub_le_sub_right hhi 1))
    exact ⟨x, q, s, hqs, hq, fun e he => h'.mem_of_mem_edges e (hedges hqs e he)⟩
  · have h' : IsOpenArm ω z r lo hi γ := h
    obtain ⟨x, q, s, hqs, hq⟩ := h'.isCrossing.exists_append_eq_isCrossing
      (T' := Icc (lo' + 1) (hi' - 1))
      (Icc_subset_Icc ((add_le_add_iff_right 1).2 hlo) (sub_le_sub_right hhi 1))
    exact ⟨x, q, s, hqs, hq, fun e he => h'.mem_of_mem_edges e (hedges hqs e he)⟩

end Cutting

/-- **Disjointness passes to pieces.** A family of walks each lying in the corresponding walk of a
disjoint family, with tails in the tails, is disjoint. -/
theorem ArmsDisjoint.mono {j : ℕ} {σ : Fin j → Bool} {a b a' b' : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (h : ArmsDisjoint σ γ) (hs : ∀ i, ∀ v ∈ (γ' i).support, v ∈ (γ i).support)
    (ht : ∀ i, ∀ v ∈ (γ' i).support.tail, v ∈ (γ i).support.tail) : ArmsDisjoint σ γ' :=
  ⟨fun i k hik hi hk v hv hv' => h.1 i k hik hi hk v (ht i v hv) (hs k v hv'),
    fun i k hik hi hk v hv hv' => h.2 i k hik hi hk v (hs i v hv) (hs k v hv')⟩

/-! ### Monotonicity in the radii -/

section Monotone

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
  {J I : Fin j → Set ℤ}

/-- **Monotonicity in the inner radius.** Arms from `B_r(z)` give arms from any larger box
`B_{r'}(z)` inside the interior of the outer box, with the same landing positions: start each
arm at its last vertex (open) or face (dual) touching `B_{r'}(z)`. -/
theorem multiArmEventTo_subset_of_le {r' : ℕ} (hr : r ≤ r')
    (hB : Icc (z - r') (z + r') ⊆ Icc (lo + 1) (hi - 1)) :
    multiArmEventTo σ z r lo hi (fun _ => univ) I ⊆
      multiArmEventTo σ z r' lo hi (fun _ => univ) I := by
  rintro ω ⟨a, b, γ, hγ, hd, hw, ho⟩
  choose x q s hqs hs using fun i => (hγ i).exists_append_eq_of_le hr
  have hland : ∀ i, landingPos lo hi (σ i) (s i) = landingPos lo hi (σ i) (γ i) := fun i => by
    rw [← hqs i, landingPos_append _ ((hs i).not_nil hB)]
  refine ⟨x, b, s, hs, hd.mono (fun i v hv => ?_) (fun i v hv => ?_),
    fun i => ⟨mem_univ _, by rw [hland]; exact (hw i).2⟩, fun i k l hik hkl => ?_⟩
  · rw [← hqs i, SimpleGraph.Walk.support_append_eq_support_dropLast_append]
    exact List.mem_append_right _ hv
  · rw [← hqs i, SimpleGraph.Walk.tail_support_append]
    exact List.mem_append_right _ hv
  · rw [hland i, hland k, hland l]
    exact ho i k l hik hkl

/-- **Monotonicity in the outer box.** Arms to the boundary of `Icc lo hi` give arms to the
boundary of any smaller box `Icc lo' hi'` whose interior contains `B_r(z)`, with the same inner
positions: stop each arm at its first vertex on the boundary of `Icc lo' hi'` (open) or its first
face outside it (dual). The new landing positions are in counterclockwise order because the inner
positions are, by order invariance at both boxes. -/
theorem multiArmEventTo_subset_of_le_of_le {lo' hi' : LatticeSite 2} (hlo : lo ≤ lo')
    (hhi : hi' ≤ hi) (hB : Icc (z - r) (z + r) ⊆ Icc (lo' + 1) (hi' - 1)) :
    multiArmEventTo σ z r lo hi J (fun _ => univ) ⊆
      multiArmEventTo σ z r lo' hi' J (fun _ => univ) := by
  rintro ω ⟨a, b, γ, hγ, hd, hw, ho⟩
  have hB₀ : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1) :=
    hB.trans (Icc_subset_Icc ((add_le_add_iff_right 1).2 hlo) (sub_le_sub_right hhi 1))
  choose x q s hqs hq using fun i => (hγ i).exists_append_eq_of_le_of_le hlo hhi
  have hinner : ∀ i, innerPos z r (σ i) (q i) = innerPos z r (σ i) (γ i) := fun i => by
    rw [← hqs i, innerPos_append _ ((hq i).not_nil hB)]
  have hd' : ArmsDisjoint σ q := hd.mono (fun i v hv => by
      rw [← hqs i, SimpleGraph.Walk.support_append]
      exact List.mem_append_left _ hv) fun i v hv => by
      rw [← hqs i, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hv
  refine ⟨a, x, q, hq, hd', fun i => ⟨by rw [hinner]; exact (hw i).1, mem_univ _⟩,
    fun i k l hik hkl => ?_⟩
  rw [← sbtw_innerPos_iff_sbtw_landingPos hB hq hd', hinner i, hinner k, hinner l,
    sbtw_innerPos_iff_sbtw_landingPos hB₀ hγ hd]
  exact ho i k l hik hkl

/-- **Monotonicity in the radii.** For `r ≤ r' < R' ≤ R`, `j` arms of colours `σ` in
counterclockwise order across the annulus between `B_r(z)` and `B_R(z)` give such arms across the
annulus between `B_{r'}(z)` and `B_{R'}(z)`. The inner radius must stay below the outer one: for
`r' = R'` the arms have no step and the event no longer depends on the configuration. -/
theorem multiArmEvent_subset_of_le {r' R R' : ℕ} (hr : r ≤ r') (hR : R' ≤ R) (hr' : r' < R') :
    multiArmEvent σ z r R ⊆ multiArmEvent σ z r' R' := by
  have hB : ∀ {s : ℕ}, s < R' →
      Icc (z - (s : LatticeSite 2)) (z + s) ⊆ Icc (z - R' + 1) (z + R' - 1) := fun hs =>
    Icc_subset_Icc (fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  intro ω hω
  have h₁ := multiArmEventTo_subset_of_le_of_le (lo' := z - R') (hi' := z + R')
    (fun i => by
      simp only [Pi.sub_apply, Pi.natCast_apply]
      omega) (fun i => by
      simp only [Pi.add_apply, Pi.natCast_apply]
      omega) (hB (hr.trans_lt hr')) hω
  exact multiArmEventTo_subset_of_le hr (hB hr') h₁

end Monotone

/-! ### Upper half of quasi-multiplicativity -/

/-- **Upper half of quasi-multiplicativity.** For `r₁ < r₂ < r₃` and every product law,
`π_σ(r₁, r₃) ≤ π_σ(r₁, r₂) π_σ(r₂, r₃)`: arms across the annulus between `B_{r₁}(z)` and
`B_{r₃}(z)` cross both smaller annuli (monotonicity in the radii), and the two smaller events
read disjoint sets of edges, those inside `B_{r₂}(z)` and those with an end outside it, so they
are independent. No gap between the two annuli is needed. -/
theorem law_multiArmEvent_le_mul (q : Sym2 (LatticeSite 2) → unitInterval) {j : ℕ}
    (σ : Fin j → Bool) (z : LatticeSite 2) {r₁ r₂ r₃ : ℕ} (h₁ : r₁ < r₂) (h₂ : r₂ < r₃) :
    law q (multiArmEvent σ z r₁ r₃) ≤
      law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃) := by
  have hsub : multiArmEvent σ z r₁ r₃ ⊆ multiArmEvent σ z r₁ r₂ ∩ multiArmEvent σ z r₂ r₃ :=
    fun ω hω => ⟨multiArmEvent_subset_of_le le_rfl h₂.le h₁ hω,
      multiArmEvent_subset_of_le h₁.le le_rfl h₂ hω⟩
  refine (MeasureTheory.measure_mono hsub).trans (le_of_eq ?_)
  set P : Set (Sym2 (LatticeSite 2)) := {e | ∀ v ∈ e, v ∈ Icc (z - r₂) (z + r₂)} with hP
  set Q : Set (Sym2 (LatticeSite 2)) := {e | ∃ v ∈ e, v ∉ Icc (z - r₂) (z + r₂)} with hQ
  have hPQ : Disjoint P Q := Set.disjoint_left.2 fun e he ⟨v, hv, hvB⟩ => hvB (he v hv)
  have hmem : ∀ {ω ω' : Config (LatticeSite 2)} {S : Set (Sym2 (LatticeSite 2))},
      ω ∩ S = ω' ∩ S → ∀ e ∈ S, (e ∈ ω ↔ e ∈ ω') := fun h e he => by
    have := congrArg (e ∈ ·) h
    simp only [mem_inter_iff, eq_iff_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
  exact PercLib.Probability.prodBernoulli_inter_of_determined q hPQ
    (measurableSet_multiArmEvent _ _ _ _) (measurableSet_multiArmEvent _ _ _ _)
    (fun ω ω' h => mem_multiArmEventTo_iff_of_agree fun e _ he _ => hmem h e he)
    (fun ω ω' h => mem_multiArmEventTo_iff_of_agree fun e _ _ he => hmem h e he)

end PercLib.Models.Planar
