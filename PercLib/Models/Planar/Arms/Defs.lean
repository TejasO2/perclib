/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions and proofs, written on 2026-11-21 and 2026-11-22. No upstream code is copied.
Mathematical references: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (one-arm bounds, pp. 23-24); P. Nolin, Near-critical
percolation in two dimensions, Electron. J. Probab. 13 (2008), paper no. 55, Sections 3.1 and
4.1 (crossing bounds below the characteristic length and arm events, pp. 1570-1573).
-/
module

public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import PercLib.Models.Planar.Defs
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.FirstExit

/-!
# Arm events, box boundaries and crossing bounds

Events and notions of bond percolation on `ℤ^d` used by the arm estimates, on the bond interface
of the library: a configuration is a `Set (Sym2 (LatticeSite d))`, and only its
nearest-neighbour pairs are read.

* **The one-arm event.** `armEvent x r` is the event that the centre `x` of the box
  `x + [-r, r]^d` is joined to the boundary of the box, the points at sup distance exactly `r`
  from `x`, by a path of open nearest-neighbour edges all of whose vertices lie in the box. It
  is an event on the edges inside the box. An arm that leaves the box can be stopped on first
  reaching the boundary, so it is also the event that `x` is joined to the boundary by an open
  path confined to no box (`mem_armEvent_iff_exists_conn`). Its probability is the one-arm
  probability `π(r)`.
* **The four-strip event.** `fourStrip z n` is the event that the four strips of the annulus
  `2n ≤ ‖v - z‖∞ ≤ 4n` of `ℤ²` are crossed in their long direction by open paths: left-right
  crossings of the top and bottom strips, bottom-top crossings of the right and left strips.
  It stands for the open circuit of the one-arm bounds: two adjacent strips share a corner
  square, which their crossings cross in perpendicular directions, so the four crossings
  together surround the box of radius `2n - 1` (proved where the event is used).
* **The boundary of a box.** `boxBoundary lo hi` is the set of points of the box `Icc lo hi` of
  `ℤ^d` with some coordinate at an end of its range. For the box `x + [-r, r]^d` it is the
  boundary that the one-arm event reaches (`mem_armEvent_iff_exists_mem_boxBoundary`), the
  sphere of radius `r` about `x` for the sup metric (`boxBoundary_sub_add_eq_sphere`).
* **Perimeter positions.** `perimeterPos lo hi v` is the position of a boundary point `v` of a
  box of `ℤ²` along the boundary, counted counterclockwise from the lower-left corner `lo`.
  Distinct boundary points have distinct positions, all in `[0, 2(hi₀ - lo₀) + 2(hi₁ - lo₁))`,
  so the counterclockwise cyclic order of boundary points is the cyclic order of their
  positions (mathlib's `CircularOrder ℤ`).
* **Crossing bounds.** `CrossingBounds q L c` says that under `law q`, for every aspect ratio
  `k`, every `k n × n` box of `ℤ²` with `1 ≤ n ≤ L`, in either orientation and at any position,
  is crossed in its long direction by open edges and by dual-open edges with probability at
  least `c k > 0`. It is the hypothesis under which arm estimates hold uniformly in the law.

Boxes stay `Set.Icc lo hi`, with `(r : LatticeSite d)` the constant vector `r`;
`Site.closedBall_eq_Icc` identifies the box `x + [-r, r]^d` with the closed ball of the sup
metric.

## Main definitions

* `PercLib.Models.Planar.armEvent`
* `PercLib.Models.Planar.fourStrip`
* `PercLib.Models.Planar.boxBoundary`
* `PercLib.Models.Planar.perimeterPos`
* `PercLib.Models.Planar.CrossingBounds`

## Main results

* `mem_armEvent_iff_exists_conn`, `mem_armEvent_iff_exists_notMem_conn`,
  `mem_armEvent_of_mem_conn`: the arm may be stopped on first reaching the boundary, so the
  one-arm event is the event that `x` is joined to the boundary of the box, or to any point
  outside the box of radius `r - 1`, by open nearest-neighbour edges.
* `armEvent_anti` (decreasing in the radius), `armEvent_zero`, `armEvent_mono`,
  `isUpperSet_armEvent`, `measurableSet_armEvent`, `mem_armEvent_iff_of_inter_eq`
  (determined by the pairs inside the box), `image_add_mem_armEvent_iff` (translation).
* `fourStrip_mono`, `isUpperSet_fourStrip`, `measurableSet_fourStrip`,
  `mem_fourStrip_iff_of_inter_eq` (determined by the pairs inside the annulus),
  `image_add_mem_fourStrip_iff` (translation), `univ_mem_fourStrip`.
* `mem_armEvent_iff_exists_mem_boxBoundary`, `boxBoundary_sub_add_eq_sphere`: the one-arm event
  joins `x` to `boxBoundary (x - r) (x + r)`, the sphere of radius `r` of the sup metric.
* `boxBoundary_eq_Icc_diff_Icc` (the box minus the box one step inside it),
  `image_add_const_boxBoundary` (translation), `rotate_mem_boxBoundary_iff` (quarter turn).
* `perimeterPos_injOn`, `perimeterPos_nonneg`, `perimeterPos_lt`, the values on each side
  (`perimeterPos_of_bottom`, `perimeterPos_of_right`, `perimeterPos_of_top`,
  `perimeterPos_of_left`), `perimeterPos_add` (translation) and `perimeterPos_rotate` (a quarter
  turn shifts positions by the height of the box, modulo the perimeter).
* `CrossingBounds.mono`, `CrossingBounds.translate`, `crossingBounds_zero` (the trivial case),
  and the four orientations `CrossingBounds.le_law_crossing_zero` and its companions.
* `edgeSet_mem_localConn_Icc`: any two points of a box of `ℤ^d` are joined by nearest-neighbour
  edges inside the box.
* `image_add_inter_edgeSet_mem_localConn_iff`, `image_add_mem_crossing_iff`,
  `dualConfig_image_add`: translations carry connections inside a set and crossings of boxes,
  and commute with taking the dual configuration.
* `Bond.inter_mem_localConn_iff_of_inter_eq`: a connection inside `S` is determined by the pairs
  inside any `T ⊇ S`.
* `Site.closedBall_eq_Icc`, `Site.apply_le_apply_add_one_of_adj`: sup-metric balls of `ℤ^d` are
  boxes, and a nearest-neighbour step moves each coordinate by at most one.
-/

@[expose] public section

noncomputable section

open Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

/-! ### Connections inside a set are determined by the pairs inside it -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A connection inside `S` by the open pairs of `ω` that lie in `E` is determined by the pairs
of `ω` inside any set `T` containing `S`. -/
theorem inter_mem_localConn_iff_of_inter_eq {S T : Set V} (hST : S ⊆ T) (E : Set (Sym2 V))
    {ω ω' : Config V} (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) (a b : V) :
    ω ∩ E ∈ localConn S a b ↔ ω' ∩ E ∈ localConn S a b := by
  have hagree : ∀ x ∈ S, ∀ y ∈ S, (s(x, y) ∈ ω ∩ E ↔ s(x, y) ∈ ω' ∩ E) := by
    intro x hx y hy
    have hxy : s(x, y) ∈ {e : Sym2 V | ∀ v ∈ e, v ∈ T} := by
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hST hx
      · exact hST hy
    have hmem := congrArg (s(x, y) ∈ ·) h
    simp only [eq_iff_iff, mem_inter_iff] at hmem
    simp only [mem_inter_iff]
    exact and_congr_left fun _ =>
      ⟨fun h₁ => (hmem.1 ⟨h₁, hxy⟩).1, fun h₁ => (hmem.2 ⟨h₁, hxy⟩).1⟩
  constructor
  · rintro ⟨ha, hb, hr⟩
    exact ⟨ha, hb, (localConn_iff_of_agree S ⟨a, ha⟩ ⟨b, hb⟩ hagree).1 hr⟩
  · rintro ⟨ha, hb, hr⟩
    exact ⟨ha, hb, (localConn_iff_of_agree S ⟨a, ha⟩ ⟨b, hb⟩ hagree).2 hr⟩

end PercLib.Percolation.Bond

/-! ### Coordinates and balls of `ℤ^d` -/

namespace PercLib.Models.Site

variable {d : ℕ}

/-- One nearest-neighbour step changes each coordinate by at most one. -/
theorem apply_le_apply_add_one_of_adj {u v : LatticeSite d} (h : (zdGraph d).Adj u v)
    (j : Fin d) : v j ≤ u j + 1 := by
  obtain ⟨i, hi, hj⟩ := (zdGraph_adj_iff_exists u v).1 h
  by_cases hji : j = i
  · rw [hji]
    omega
  · have := hj j hji
    omega

/-- The closed ball of radius `r` about `x` for the sup metric of `Fin d → ℤ` is the box
`x + [-r, r]^d`. -/
theorem closedBall_eq_Icc (x : LatticeSite d) (r : ℕ) :
    Metric.closedBall x r = Icc (x - r) (x + r) := by
  rw [closedBall_pi x (Nat.cast_nonneg r), ← pi_univ_Icc]
  refine pi_congr rfl fun i _ => ?_
  have h₁ : (x i : ℝ) - (r : ℝ) = ((x i - r : ℤ) : ℝ) := by simp
  have h₂ : (x i : ℝ) + (r : ℝ) = ((x i + r : ℤ) : ℝ) := by simp
  rw [Int.closedBall_eq_Icc, h₁, h₂, Int.ceil_intCast, Int.floor_intCast, Pi.sub_apply,
    Pi.add_apply, Pi.natCast_apply]

end PercLib.Models.Site

namespace PercLib.Models.Planar

variable {d : ℕ}

/-! ### Translations and boxes of `ℤ^d` -/

/-- **Translations carry connections.** Translating the configuration and the set by `c` carries
a connection by open nearest-neighbour edges inside the set to one between the translated
points. -/
theorem image_add_inter_edgeSet_mem_localConn_iff (c : LatticeSite d)
    (ω : Config (LatticeSite d)) (S : Set (LatticeSite d)) (a b : LatticeSite d) :
    Sym2.map (· + c) '' ω ∩ (zdGraph d).edgeSet ∈ localConn ((· + c) '' S) (a + c) (b + c) ↔
      ω ∩ (zdGraph d).edgeSet ∈ localConn S a b := by
  set σ : LatticeSite d ≃ LatticeSite d := Equiv.addRight c with hσ
  -- translations preserve the nearest-neighbour edges
  have hL : ∀ e, Sym2.map (· + c) e ∈ (zdGraph d).edgeSet ↔ e ∈ (zdGraph d).edgeSet := by
    intro e
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      exact zdGraph_adj_iff_of_sub fun i => by
        simp only [Pi.add_apply, add_sub_add_right_eq_sub]
  have himage : Sym2.map (· + c) '' ω ∩ (zdGraph d).edgeSet =
      Sym2.map σ '' (ω ∩ (zdGraph d).edgeSet) := by
    ext e
    constructor
    · rintro ⟨⟨e₀, he₀, rfl⟩, he⟩
      exact ⟨e₀, ⟨he₀, (hL e₀).1 he⟩, rfl⟩
    · rintro ⟨e₀, ⟨he₀, he⟩, rfl⟩
      exact ⟨⟨e₀, he₀, rfl⟩, (hL e₀).2 he⟩
  rw [himage]
  constructor
  · intro h'
    refine localConn_of_image (a := a) (b := b) σ _ (fun v hv => ?_) h'
    obtain ⟨w, hw, rfl⟩ := hv
    change σ.symm (σ w) ∈ S
    rw [Equiv.symm_apply_apply]
    exact hw
  · intro h'
    have ha : σ.symm (a + c) = a := σ.symm_apply_apply a
    have hb : σ.symm (b + c) = b := σ.symm_apply_apply b
    refine localConn_of_image (a := a + c) (b := b + c) σ.symm _ (S := (· + c) '' S) (T := S)
      (fun v hv => ⟨v, hv, rfl⟩) ?_
    rw [image_sym2Map_symm_image, ha, hb]
    exact h'

/-- **Boxes are connected.** Any two points of a box of `ℤ^d` are joined by a path of
nearest-neighbour edges all of whose vertices lie in the box. -/
theorem edgeSet_mem_localConn_Icc {lo hi a b : LatticeSite d} (ha : a ∈ Icc lo hi)
    (hb : b ∈ Icc lo hi) : (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b := by
  suffices h : ∀ N : ℕ, ∀ a ∈ Icc lo hi, ∑ i, (b i - a i).natAbs = N →
      (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b from h _ a ha rfl
  intro N
  induction N with
  | zero =>
    intro a ha hN
    have hab : a = b := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 hN) i (Finset.mem_univ i)
      omega
    subst hab
    rw [localConn_self ha]
    exact mem_univ _
  | succ N ih =>
    intro a ha hN
    obtain ⟨i, -, hne⟩ : ∃ i ∈ (Finset.univ : Finset (Fin d)), (b i - a i).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero hc] at hN
      exact Nat.zero_ne_add_one N hN
    set a' := Function.update a i (a i + if a i < b i then 1 else -1) with ha'
    have hadj : (zdGraph d).Adj a a' := (zdGraph_adj_iff_eq_update a a').2
      ⟨(i, decide (a i < b i)), by simp [ha']⟩
    have hsum : ∑ j, (b j - a j).natAbs = ∑ j, (b j - a' j).natAbs + 1 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i, (b j - a j).natAbs =
          ∑ j ∈ Finset.univ.erase i, (b j - a' j).natAbs :=
        Finset.sum_congr rfl fun j hj => by
          rw [ha', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest, ha', Function.update_self]
      split_ifs <;> omega
    have ha'mem : a' ∈ Icc lo hi := by
      simp only [mem_Icc, Pi.le_def] at ha hb ⊢
      refine ⟨fun j => ?_, fun j => ?_⟩
      · by_cases hj : j = i
        · rw [hj, ha', Function.update_self]
          have := ha.1 i
          have := hb.1 i
          split_ifs <;> omega
        · rw [ha', Function.update_of_ne hj]
          exact ha.1 j
      · by_cases hj : j = i
        · rw [hj, ha', Function.update_self]
          have := ha.2 i
          have := hb.2 i
          split_ifs <;> omega
        · rw [ha', Function.update_of_ne hj]
          exact ha.2 j
    have hstep : (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a a' :=
      ⟨ha, ha'mem, SimpleGraph.Adj.reachable
        ((openGraph_adj_iff _ a a').2 ⟨(SimpleGraph.mem_edgeSet _).2 hadj, hadj.ne⟩)⟩
    exact localConn_trans hstep (ih a' ha'mem (by omega))

/-! ### Translations of crossings and of the dual configuration -/

/-- **Translations carry crossings.** Translating the configuration and the box by `c` carries a
crossing of the box in direction `i` to a crossing of the translated box. -/
theorem image_add_mem_crossing_iff (c : LatticeSite d) (i : Fin d) (lo hi : LatticeSite d)
    (ω : Config (LatticeSite d)) :
    Sym2.map (· + c) '' ω ∈ crossing i (lo + c) (hi + c) ↔ ω ∈ crossing i lo hi := by
  rw [mem_crossing_iff, mem_crossing_iff, ← image_add_const_Icc]
  constructor
  · rintro ⟨a', ⟨a, ha, rfl⟩, hai, b', ⟨b, hb, rfl⟩, hbi, hab⟩
    refine ⟨a, ha, ?_, b, hb, ?_, (image_add_inter_edgeSet_mem_localConn_iff c ω _ a b).1 hab⟩
    · simpa only [Pi.add_apply, add_left_inj] using hai
    · simpa only [Pi.add_apply, add_left_inj] using hbi
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    refine ⟨a + c, ⟨a, ha, rfl⟩, ?_, b + c, ⟨b, hb, rfl⟩, ?_,
      (image_add_inter_edgeSet_mem_localConn_iff c ω _ a b).2 hab⟩
    · simp only [Pi.add_apply, hai]
    · simp only [Pi.add_apply, hbi]

/-- **The dual configuration commutes with translations.** The dual edges open in the
translated configuration are the translates of those open in the configuration. -/
theorem dualConfig_image_add (c : LatticeSite 2) (ω : Config (LatticeSite 2)) :
    dualConfig (Sym2.map (· + c) '' ω) = Sym2.map (· + c) '' dualConfig ω := by
  have hinj : Function.Injective (Sym2.map (· + c) : Sym2 (LatticeSite 2) → _) :=
    Sym2.map.injective (add_left_injective c)
  have hback : ∀ e : Sym2 (LatticeSite 2), Sym2.map (· + c) (Sym2.map (· + -c) e) = e := by
    intro e
    have h : ((fun v : LatticeSite 2 => v + c) ∘ fun v => v + -c) = id := by
      funext v
      simp
    rw [Sym2.map_map, h, Sym2.map_id, id]
  ext f
  rw [mem_dualConfig_iff']
  constructor
  · rintro ⟨e, he, heω, rfl⟩
    refine ⟨dualEdge (Sym2.map (· + -c) e), (mem_dualConfig_iff' ω _).2
      ⟨Sym2.map (· + -c) e, map_add_mem_edgeSet (-c) he, fun h => heω ⟨_, h, hback e⟩, rfl⟩, ?_⟩
    rw [← dualEdge_map_add, hback]
  · rintro ⟨f₀, hf₀, rfl⟩
    obtain ⟨e₀, he₀, heω, rfl⟩ := (mem_dualConfig_iff' ω f₀).1 hf₀
    refine ⟨Sym2.map (· + c) e₀, map_add_mem_edgeSet c he₀, ?_, dualEdge_map_add c e₀⟩
    rintro ⟨e', he', hee'⟩
    rw [hinj hee'] at he'
    exact heω he'

/-! ### The one-arm event -/

/-- The **one-arm event** of radius `r` at `x`: the centre `x` of the box `x + [-r, r]^d` is
joined to the boundary of the box, the points `v` of the box with `v i = x i - r` or
`v i = x i + r` for some `i`, by a path of open nearest-neighbour edges all of whose vertices
lie in the box. Open pairs that are not edges of `zdGraph d` are ignored. It is an event on the
edges inside the box; since an arm can be stopped on first reaching the boundary, it is also
the event that `x` is joined to the boundary by an open path confined to no box
(`mem_armEvent_iff_exists_conn`). Here `(r : LatticeSite d)` is the constant vector `r`, and
the box is the closed ball of radius `r` of the sup metric (`closedBall_eq_Icc`). In dimension
zero the box has no boundary and the event is empty. -/
def armEvent (x : LatticeSite d) (r : ℕ) : Set (Config (LatticeSite d)) :=
  {ω | ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
    ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v}

theorem mem_armEvent_iff {x : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v :=
  Iff.rfl

/-- The one-arm event depends only on the nearest-neighbour edges. -/
@[simp]
theorem inter_edgeSet_mem_armEvent_iff {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∩ (zdGraph d).edgeSet ∈ armEvent x r ↔ ω ∈ armEvent x r := by
  simp only [mem_armEvent_iff, inter_assoc, inter_self]

/-- The one-arm event is an increasing event. -/
theorem armEvent_mono {x : LatticeSite d} {r : ℕ} {ω ω' : Config (LatticeSite d)}
    (h : ω ⊆ ω') (hω : ω ∈ armEvent x r) : ω' ∈ armEvent x r := by
  obtain ⟨v, hv, hvx, hc⟩ := hω
  exact ⟨v, hv, hvx, localConn_mono (inter_subset_inter_left _ h) hc⟩

theorem isUpperSet_armEvent (x : LatticeSite d) (r : ℕ) : IsUpperSet (armEvent x r) :=
  fun _ _ h hω => armEvent_mono h hω

/-- The one-arm event is a measurable event. -/
theorem measurableSet_armEvent (x : LatticeSite d) (r : ℕ) : MeasurableSet (armEvent x r) := by
  have h : armEvent x r =
      ⋃ v ∈ {v | v ∈ Icc (x - r) (x + r) ∧ ∃ i, v i = x i - r ∨ v i = x i + r},
        (fun ω : Config (LatticeSite d) => ω ∩ (zdGraph d).edgeSet) ⁻¹'
          localConn (Icc (x - r) (x + r)) x v := by
    ext ω
    simp only [mem_armEvent_iff, mem_iUnion, mem_preimage, mem_ofPred_eq, exists_prop, and_assoc]
  rw [h]
  exact MeasurableSet.biUnion (to_countable _) fun v _ =>
    (measurableSet_localConn _ x v).preimage (by fun_prop)

/-- In the box of radius zero the centre is on the boundary, so the one-arm event of radius
zero holds in every configuration as soon as there is a coordinate. -/
theorem mem_armEvent_zero (x : LatticeSite d) (i : Fin d) (ω : Config (LatticeSite d)) :
    ω ∈ armEvent x 0 := by
  have hx : x ∈ Icc (x - ((0 : ℕ) : LatticeSite d)) (x + ((0 : ℕ) : LatticeSite d)) := by
    simp
  refine ⟨x, hx, ⟨i, Or.inl (by simp)⟩, ?_⟩
  rw [localConn_self hx]
  exact mem_univ _

/-- **The trivial case.** In positive dimension the one-arm event of radius zero is
everything. -/
@[simp]
theorem armEvent_zero [NeZero d] (x : LatticeSite d) : armEvent x 0 = univ :=
  eq_univ_of_forall (mem_armEvent_zero x 0)

/-- **Stopping on first reaching the boundary.** An open nearest-neighbour path from `x` to a
point `y` outside the box `x + [-(r - 1), r - 1]^d` (to any point when `r = 0`), confined to no
box, gives an arm from `x` to the boundary of `x + [-r, r]^d` inside that box. -/
theorem mem_armEvent_of_mem_conn {x y : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)}
    (hy : y ∉ Icc (x - r + 1) (x + r - 1)) (h : ω ∩ (zdGraph d).edgeSet ∈ conn x y) :
    ω ∈ armEvent x r := by
  by_cases hx : x ∈ Icc (x - r + 1) (x + r - 1)
  · obtain ⟨u, hu, w, hw, hxu, huw⟩ := exists_first_exit _ hx hy h
    have hadj : (zdGraph d).Adj u w := (SimpleGraph.mem_edgeSet _).1 huw.2
    have hwu := apply_le_apply_add_one_of_adj hadj
    have huw' := apply_le_apply_add_one_of_adj hadj.symm
    have hSB : Icc (x - r + 1) (x + r - 1) ⊆ Icc (x - r) (x + r) := by
      intro v hv
      simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
        Pi.one_apply] at hv ⊢
      exact ⟨fun j => by have := hv.1 j; omega, fun j => by have := hv.2 j; omega⟩
    have hu' := hu
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      Pi.one_apply, not_and_or, not_forall, not_le] at hu' hw
    have hwB : w ∈ Icc (x - r) (x + r) := by
      simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      exact ⟨fun j => by have := hu'.1 j; have := huw' j; omega,
        fun j => by have := hu'.2 j; have := hwu j; omega⟩
    have hwbd : ∃ i, w i = x i - r ∨ w i = x i + r := by
      rcases hw with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, Or.inl (by have := hu'.1 i; have := huw' i; omega)⟩
      · exact ⟨i, Or.inr (by have := hu'.2 i; have := hwu i; omega)⟩
    refine ⟨w, hwB, hwbd, localConn_trans (localConn_mono_set hSB x u ⟨hx, hu, hxu⟩) ?_⟩
    exact ⟨hSB hu, hwB, SimpleGraph.Adj.reachable ((openGraph_adj_iff _ u w).2 ⟨huw, hadj.ne⟩)⟩
  · simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
      Pi.one_apply, not_and_or, not_forall, not_le] at hx
    obtain ⟨i, hr⟩ : ∃ _ : Fin d, (r : ℤ) = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, by omega⟩
      · exact ⟨i, by omega⟩
    obtain rfl : r = 0 := by omega
    exact mem_armEvent_zero x i ω

/-- **The one-arm event as an escape event.** `ω` has the one-arm event of radius `r` at `x`
exactly when an open nearest-neighbour path, confined to no box, joins `x` to a point outside
the box `x + [-(r - 1), r - 1]^d`. -/
theorem mem_armEvent_iff_exists_notMem_conn {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔
      ∃ y ∉ Icc (x - r + 1) (x + r - 1), ω ∩ (zdGraph d).edgeSet ∈ conn x y := by
  constructor
  · rintro ⟨v, -, ⟨i, hvi⟩, hc⟩
    refine ⟨v, fun hv => ?_, localConn_subset_conn _ x v hc⟩
    have h₁ := hv.1 i
    have h₂ := hv.2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h₁ h₂
    omega
  · rintro ⟨y, hy, hc⟩
    exact mem_armEvent_of_mem_conn hy hc

/-- **The one-arm event is the event `x ↔ ∂B_r(x)`.** Since an arm can be stopped on first
reaching the boundary, `ω` has the one-arm event exactly when `x` is joined to a point of the
boundary of the box by an open nearest-neighbour path confined to no box. -/
theorem mem_armEvent_iff_exists_conn {x : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
      ω ∩ (zdGraph d).edgeSet ∈ conn x v := by
  constructor
  · rintro ⟨v, hv, hvx, hc⟩
    exact ⟨v, hv, hvx, localConn_subset_conn _ x v hc⟩
  · rintro ⟨v, -, ⟨i, hvi⟩, hc⟩
    refine mem_armEvent_of_mem_conn (y := v) (fun hv => ?_) hc
    have h₁ := hv.1 i
    have h₂ := hv.2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h₁ h₂
    omega

/-- For a configuration of nearest-neighbour edges, the one-arm event is the event that `x` is
joined to the boundary of the box by an open path. -/
theorem mem_armEvent_iff_exists_conn_of_subset {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} (hω : ω ⊆ (zdGraph d).edgeSet) :
    ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
      ω ∈ conn x v := by
  rw [mem_armEvent_iff_exists_conn, inter_eq_left.2 hω]

/-- **Monotonicity in the radius.** The one-arm event decreases as the radius grows: an arm to
the boundary of a box, stopped on first reaching the boundary of a smaller box, is an arm of
the smaller box. -/
theorem armEvent_anti (x : LatticeSite d) : Antitone (armEvent x) := by
  intro r s hrs ω hω
  obtain ⟨y, hy, hc⟩ := mem_armEvent_iff_exists_notMem_conn.1 hω
  refine mem_armEvent_of_mem_conn (fun hyr => hy ?_) hc
  have hrs' : (r : ℤ) ≤ s := Nat.cast_le.2 hrs
  simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply,
    Pi.one_apply] at hyr ⊢
  exact ⟨fun j => by have := hyr.1 j; omega, fun j => by have := hyr.2 j; omega⟩

/-- **Determination.** The one-arm event is determined by the pairs inside any set containing
the box. -/
theorem mem_armEvent_iff_of_inter_eq {x : LatticeSite d} {r : ℕ} {T : Set (LatticeSite d)}
    (hT : Icc (x - r) (x + r) ⊆ T) {ω ω' : Config (LatticeSite d)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ armEvent x r ↔ ω' ∈ armEvent x r := by
  simp only [mem_armEvent_iff, inter_mem_localConn_iff_of_inter_eq hT (zdGraph d).edgeSet h]

/-- **Translation.** Translating the configuration by `c` carries the one-arm event at `x` to the
one-arm event at `x + c`. -/
theorem image_add_mem_armEvent_iff (c x : LatticeSite d) (r : ℕ) (ω : Config (LatticeSite d)) :
    Sym2.map (· + c) '' ω ∈ armEvent (x + c) r ↔ ω ∈ armEvent x r := by
  have hbox : Icc (x + c - r) (x + c + r) = (· + c) '' Icc (x - r) (x + r) := by
    rw [image_add_const_Icc, add_sub_right_comm, add_right_comm x c]
  rw [mem_armEvent_iff, mem_armEvent_iff, hbox]
  constructor
  · rintro ⟨v', ⟨v, hv, rfl⟩, ⟨i, hvi⟩, hc⟩
    refine ⟨v, hv, ⟨i, ?_⟩, (image_add_inter_edgeSet_mem_localConn_iff c ω _ x v).1 hc⟩
    simp only [Pi.add_apply] at hvi
    omega
  · rintro ⟨v, hv, ⟨i, hvi⟩, hc⟩
    refine ⟨v + c, ⟨v, hv, rfl⟩, ⟨i, ?_⟩,
      (image_add_inter_edgeSet_mem_localConn_iff c ω _ x v).2 hc⟩
    simp only [Pi.add_apply]
    omega

/-- Translation, as an identity of events. -/
theorem preimage_image_add_armEvent (c x : LatticeSite d) (r : ℕ) :
    (fun ω : Config (LatticeSite d) => Sym2.map (· + c) '' ω) ⁻¹' armEvent (x + c) r =
      armEvent x r :=
  ext fun ω => image_add_mem_armEvent_iff c x r ω

/-- With every edge closed there is no arm of positive radius. -/
theorem empty_notMem_armEvent {x : LatticeSite d} {r : ℕ} (hr : 1 ≤ r) :
    (∅ : Config (LatticeSite d)) ∉ armEvent x r := by
  rintro ⟨v, -, ⟨i, hvi⟩, hc⟩
  rw [empty_inter] at hc
  have hxv := (empty_mem_conn_iff x v).1 (localConn_subset_conn _ x v hc)
  subst hxv
  omega

/-- With every edge open, every box of positive dimension has an arm. -/
theorem univ_mem_armEvent [NeZero d] (x : LatticeSite d) (r : ℕ) :
    (univ : Config (LatticeSite d)) ∈ armEvent x r := by
  have hx : x ∈ Icc (x - r) (x + r) := by
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    exact ⟨fun j => by omega, fun j => by omega⟩
  have hxr : x + r ∈ Icc (x - r) (x + r) := by
    simp only [mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    exact ⟨fun j => by omega, fun j => le_rfl⟩
  refine ⟨x + r, hxr, ⟨0, Or.inr (by simp)⟩, ?_⟩
  rw [univ_inter]
  exact edgeSet_mem_localConn_Icc hx hxr

/-! ### The four-strip event -/

/-- The **four-strip event** of the annulus `2n ≤ ‖v - z‖∞ ≤ 4n` of `ℤ²`: open crossings of its
four strips in their long direction, namely left-right crossings of the top strip
`z + [-4n, 4n] × [2n, 4n]` and of the bottom strip `z + [-4n, 4n] × [-4n, -2n]`, and bottom-top
crossings of the right strip `z + [2n, 4n] × [-4n, 4n]` and of the left strip
`z + [-4n, -2n] × [-4n, 4n]`. Two adjacent strips share a corner square, which their crossings
cross in perpendicular directions; the event stands for the open circuit around the box of
radius `2n - 1` in the one-arm bounds. -/
def fourStrip (z : LatticeSite 2) (n : ℕ) : Set (Config (LatticeSite 2)) :=
  crossing 0 (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∩
  crossing 0 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) ∩
  crossing 1 (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∩
  crossing 1 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n])

theorem mem_fourStrip_iff {z : LatticeSite 2} {n : ℕ} {ω : Config (LatticeSite 2)} :
    ω ∈ fourStrip z n ↔
      ω ∈ crossing 0 (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∧
      ω ∈ crossing 0 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) ∧
      ω ∈ crossing 1 (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∧
      ω ∈ crossing 1 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n]) := by
  simp only [fourStrip, mem_inter_iff, and_assoc]

/-- The four-strip event depends only on the nearest-neighbour edges. -/
@[simp]
theorem inter_edgeSet_mem_fourStrip_iff {z : LatticeSite 2} {n : ℕ}
    {ω : Config (LatticeSite 2)} :
    ω ∩ (zdGraph 2).edgeSet ∈ fourStrip z n ↔ ω ∈ fourStrip z n := by
  simp only [mem_fourStrip_iff, inter_edgeSet_mem_crossing_iff]

/-- The four-strip event is an increasing event. -/
theorem fourStrip_mono {z : LatticeSite 2} {n : ℕ} {ω ω' : Config (LatticeSite 2)}
    (h : ω ⊆ ω') (hω : ω ∈ fourStrip z n) : ω' ∈ fourStrip z n := by
  rw [mem_fourStrip_iff] at hω ⊢
  exact ⟨crossing_mono h hω.1, crossing_mono h hω.2.1, crossing_mono h hω.2.2.1,
    crossing_mono h hω.2.2.2⟩

theorem isUpperSet_fourStrip (z : LatticeSite 2) (n : ℕ) : IsUpperSet (fourStrip z n) :=
  fun _ _ h hω => fourStrip_mono h hω

/-- The four-strip event is a measurable event. -/
theorem measurableSet_fourStrip (z : LatticeSite 2) (n : ℕ) : MeasurableSet (fourStrip z n) :=
  (((measurableSet_crossing _ _ _).inter (measurableSet_crossing _ _ _)).inter
    (measurableSet_crossing _ _ _)).inter (measurableSet_crossing _ _ _)

/-- **Determination.** The four-strip event is determined by the pairs inside any set containing
the annulus `2n ≤ ‖v - z‖∞ ≤ 4n`. -/
theorem mem_fourStrip_iff_of_inter_eq {z : LatticeSite 2} {n : ℕ} {T : Set (LatticeSite 2)}
    (hT : {v : LatticeSite 2 | z 0 - 4 * n ≤ v 0 ∧ v 0 ≤ z 0 + 4 * n ∧ z 1 - 4 * n ≤ v 1 ∧
      v 1 ≤ z 1 + 4 * n ∧
      (v 0 ≤ z 0 - 2 * n ∨ z 0 + 2 * n ≤ v 0 ∨ v 1 ≤ z 1 - 2 * n ∨ z 1 + 2 * n ≤ v 1)} ⊆ T)
    {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T}) :
    ω ∈ fourStrip z n ↔ ω' ∈ fourStrip z n := by
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2), Icc lo hi ⊆ T →
      (ω ∈ crossing i lo hi ↔ ω' ∈ crossing i lo hi) := fun i lo hi hsub => by
    simp only [mem_crossing_iff,
      inter_mem_localConn_iff_of_inter_eq hsub (zdGraph 2).edgeSet h]
  have hsub : ∀ lo hi : LatticeSite 2, (∀ v : LatticeSite 2, lo 0 ≤ v 0 → v 0 ≤ hi 0 →
      lo 1 ≤ v 1 → v 1 ≤ hi 1 → v ∈ T) → Icc lo hi ⊆ T := fun lo hi hT' v hv => by
    rw [mem_Icc_two_iff] at hv
    exact hT' v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  rw [mem_fourStrip_iff, mem_fourStrip_iff]
  refine and_congr (hcross 0 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_)) (and_congr
    (hcross 0 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_)) (and_congr
    (hcross 1 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_))
    (hcross 1 _ _ (hsub _ _ fun v h₁ h₂ h₃ h₄ => hT ?_)))) <;>
  · simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **Translation.** Translating the configuration by `c` carries the four-strip event at `z` to
the four-strip event at `z + c`. -/
theorem image_add_mem_fourStrip_iff (c z : LatticeSite 2) (n : ℕ) (ω : Config (LatticeSite 2)) :
    Sym2.map (· + c) '' ω ∈ fourStrip (z + c) n ↔ ω ∈ fourStrip z n := by
  simp only [mem_fourStrip_iff, add_right_comm z c, image_add_mem_crossing_iff]

/-- With every edge open, the four strips are crossed. -/
theorem univ_mem_fourStrip (z : LatticeSite 2) (n : ℕ) :
    (univ : Config (LatticeSite 2)) ∈ fourStrip z n := by
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2), lo ≤ hi →
      (univ : Config (LatticeSite 2)) ∈ crossing i lo hi := by
    intro i lo hi hle
    have hb : Function.update lo i (hi i) ∈ Icc lo hi := by
      simp only [mem_Icc, Pi.le_def]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · by_cases hj : j = i
        · rw [hj, Function.update_self]
          exact hle i
        · rw [Function.update_of_ne hj]
      · by_cases hj : j = i
        · rw [hj, Function.update_self]
        · rw [Function.update_of_ne hj]
          exact hle j
    refine ⟨lo, left_mem_Icc.2 hle, rfl, _, hb, Function.update_self .., ?_⟩
    rw [univ_inter]
    exact edgeSet_mem_localConn_Icc (left_mem_Icc.2 hle) hb
  have hle : ∀ a b a' b' : ℤ, a ≤ a' → b ≤ b' → z + ![a, b] ≤ z + ![a', b'] := by
    intro a b a' b' ha hb
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rw [mem_fourStrip_iff]
  exact ⟨hcross 0 _ _ (hle _ _ _ _ (by omega) (by omega)),
    hcross 0 _ _ (hle _ _ _ _ (by omega) (by omega)),
    hcross 1 _ _ (hle _ _ _ _ (by omega) (by omega)),
    hcross 1 _ _ (hle _ _ _ _ (by omega) (by omega))⟩

/-! ### The boundary of a box -/

/-- The **boundary of the box** `Icc lo hi` of `ℤ^d`: the points of the box with some coordinate
at an end of its range, `v i = lo i` or `v i = hi i`. For the box `x + [-r, r]^d` it is the
boundary reached by the one-arm event (`mem_armEvent_iff_exists_mem_boxBoundary`) and the sphere
of radius `r` about `x` for the sup metric (`boxBoundary_sub_add_eq_sphere`). In dimension zero
it is empty. -/
def boxBoundary (lo hi : LatticeSite d) : Set (LatticeSite d) :=
  {v | v ∈ Icc lo hi ∧ ∃ i, v i = lo i ∨ v i = hi i}

theorem mem_boxBoundary_iff {lo hi v : LatticeSite d} :
    v ∈ boxBoundary lo hi ↔ v ∈ Icc lo hi ∧ ∃ i, v i = lo i ∨ v i = hi i :=
  Iff.rfl

theorem boxBoundary_subset_Icc (lo hi : LatticeSite d) : boxBoundary lo hi ⊆ Icc lo hi :=
  fun _ hv => hv.1

/-- The boundary of a box is the box minus the box one step inside it. -/
theorem boxBoundary_eq_Icc_diff_Icc (lo hi : LatticeSite d) :
    boxBoundary lo hi = Icc lo hi \ Icc (lo + 1) (hi - 1) := by
  ext v
  simp only [mem_boxBoundary_iff, mem_sdiff, mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply,
    Pi.one_apply, not_and_or, not_forall, not_le]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, i, hvi | hvi⟩
    · exact ⟨⟨h₁, h₂⟩, Or.inl ⟨i, by omega⟩⟩
    · exact ⟨⟨h₁, h₂⟩, Or.inr ⟨i, by omega⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨i, hvi⟩ | ⟨i, hvi⟩⟩
    · exact ⟨⟨h₁, h₂⟩, i, Or.inl (by have := h₁ i; omega)⟩
    · exact ⟨⟨h₁, h₂⟩, i, Or.inr (by have := h₂ i; omega)⟩

/-- **The trivial case.** In positive dimension the boundary of a one-point box is the point. -/
@[simp]
theorem boxBoundary_self [NeZero d] (v : LatticeSite d) : boxBoundary v v = {v} := by
  ext w
  simp only [mem_boxBoundary_iff, Icc_self, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, 0, Or.inl rfl⟩

/-- The lower corner of a nonempty box of positive dimension is on its boundary. -/
theorem left_mem_boxBoundary [NeZero d] {lo hi : LatticeSite d} (h : lo ≤ hi) :
    lo ∈ boxBoundary lo hi :=
  ⟨left_mem_Icc.2 h, 0, Or.inl rfl⟩

/-- The upper corner of a nonempty box of positive dimension is on its boundary. -/
theorem right_mem_boxBoundary [NeZero d] {lo hi : LatticeSite d} (h : lo ≤ hi) :
    hi ∈ boxBoundary lo hi :=
  ⟨right_mem_Icc.2 h, 0, Or.inr rfl⟩

/-- **Translation.** Translating a point and the box by `c` keeps the point on the boundary. -/
@[simp]
theorem add_mem_boxBoundary_add_iff {lo hi v : LatticeSite d} (c : LatticeSite d) :
    v + c ∈ boxBoundary (lo + c) (hi + c) ↔ v ∈ boxBoundary lo hi := by
  simp only [mem_boxBoundary_iff, mem_Icc, Pi.le_def, Pi.add_apply, add_le_add_iff_right,
    add_left_inj]

/-- **Translation.** The translate of the boundary of a box is the boundary of the translated
box. -/
theorem image_add_const_boxBoundary (c lo hi : LatticeSite d) :
    (· + c) '' boxBoundary lo hi = boxBoundary (lo + c) (hi + c) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (add_mem_boxBoundary_add_iff c).2 hv
  · intro hw
    refine ⟨w - c, ?_, sub_add_cancel w c⟩
    rw [← add_mem_boxBoundary_add_iff c, sub_add_cancel]
    exact hw

/-- The boundary of the box `x + [-r, r]^d`, coordinate by coordinate: the points of the box
with some coordinate at distance exactly `r` from that of `x`. This is the boundary used by
`armEvent x r`. -/
theorem mem_boxBoundary_sub_add_iff {x v : LatticeSite d} {r : ℕ} :
    v ∈ boxBoundary (x - r : LatticeSite d) (x + r) ↔
      v ∈ Icc (x - r) (x + r) ∧ ∃ i, v i = x i - r ∨ v i = x i + r := by
  simp only [mem_boxBoundary_iff, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]

/-- In positive dimension the boundary of the box `x + [-r, r]^d` is the sphere of radius `r`
about `x` for the sup metric of `Fin d → ℤ` (compare `Site.closedBall_eq_Icc`). -/
theorem boxBoundary_sub_add_eq_sphere [NeZero d] (x : LatticeSite d) (r : ℕ) :
    boxBoundary (x - r : LatticeSite d) (x + r) = Metric.sphere x r := by
  rw [sphere_pi x (Or.inr inferInstance), closedBall_eq_Icc]
  ext v
  have key : ∀ a b : ℤ, dist a b = (r : ℝ) ↔ a = b - r ∨ a = b + r := by
    intro a b
    rw [Int.dist_eq, abs_eq (Nat.cast_nonneg r)]
    constructor
    · rintro (h | h)
      · right
        have h' : ((a - b : ℤ) : ℝ) = ((r : ℤ) : ℝ) := by push_cast; linarith
        have := Int.cast_injective h'
        omega
      · left
        have h' : ((a - b : ℤ) : ℝ) = ((-(r : ℤ) : ℤ) : ℝ) := by push_cast; linarith
        have := Int.cast_injective h'
        omega
    · rintro (h | h)
      · right
        rw [h]
        push_cast
        ring
      · left
        rw [h]
        push_cast
        ring
  simp only [mem_boxBoundary_sub_add_iff, mem_inter_iff, mem_iUnion, mem_preimage,
    Function.eval, Metric.mem_sphere, key]
  exact and_comm

/-- **The one-arm event reaches the boundary of the box.** `ω` has the one-arm event of radius
`r` at `x` exactly when `x` is joined to a point of `boxBoundary (x - r) (x + r)` by open
nearest-neighbour edges inside the box. This restates `armEvent` with `boxBoundary`. -/
theorem mem_armEvent_iff_exists_mem_boxBoundary {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ boxBoundary (x - r : LatticeSite d) (x + r),
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v := by
  simp only [mem_armEvent_iff, mem_boxBoundary_sub_add_iff, and_assoc]

/-- **The one-arm event as `x ↔ ∂B_r(x)`, with `boxBoundary`.** The path to the boundary may be
confined to no box (`mem_armEvent_iff_exists_conn`). -/
theorem mem_armEvent_iff_exists_mem_boxBoundary_conn {x : LatticeSite d} {r : ℕ}
    {ω : Config (LatticeSite d)} :
    ω ∈ armEvent x r ↔ ∃ v ∈ boxBoundary (x - r : LatticeSite d) (x + r),
      ω ∩ (zdGraph d).edgeSet ∈ conn x v := by
  simp only [mem_armEvent_iff_exists_conn, mem_boxBoundary_sub_add_iff, and_assoc]

/-- The boundary of a box of `ℤ²`, coordinate by coordinate. -/
theorem mem_boxBoundary_two_iff {lo hi v : LatticeSite 2} :
    v ∈ boxBoundary lo hi ↔ (lo 0 ≤ v 0 ∧ v 0 ≤ hi 0 ∧ lo 1 ≤ v 1 ∧ v 1 ≤ hi 1) ∧
      (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = lo 1 ∨ v 1 = hi 1) := by
  rw [mem_boxBoundary_iff, mem_Icc_two_iff, Fin.exists_fin_two, or_assoc]

/-- **Quarter turn.** The counterclockwise quarter turn `(x, y) ↦ (-y, x)` of `ℤ²` maps the
boundary of `Icc lo hi` onto the boundary of the turned box `[-hi₁, -lo₁] × [lo₀, hi₀]`. -/
@[simp]
theorem rotate_mem_boxBoundary_iff {lo hi v : LatticeSite 2} :
    ![-v 1, v 0] ∈ boxBoundary (d := 2) ![-hi 1, lo 0] ![-lo 1, hi 0] ↔
      v ∈ boxBoundary lo hi := by
  simp only [mem_boxBoundary_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> omega

/-! ### Perimeter positions on the boundary of a box of `ℤ²` -/

/-- The **perimeter position** of a point `v` of the boundary of the box `Icc lo hi` of `ℤ²`:
its distance from the lower-left corner `lo` along the boundary, counterclockwise. The bottom
side, both corners included, has positions `0` to `hi₀ - lo₀`; then come the right side above
the lower-right corner, the top side left of the upper-right corner, and the left side strictly
between the upper-left and lower-left corners. Each corner other than `lo` belongs to the side
that ends at it. Distinct boundary points have distinct positions (`perimeterPos_injOn`), all in
`[0, 2(hi₀ - lo₀) + 2(hi₁ - lo₁))` unless the box is a point (`perimeterPos_nonneg`,
`perimeterPos_lt`), so the counterclockwise cyclic order of boundary points is the cyclic order
of their positions (mathlib's `CircularOrder ℤ`). Off the boundary the value is that of the last
case and has no meaning. -/
def perimeterPos (lo hi v : LatticeSite 2) : ℤ :=
  if v 1 = lo 1 then v 0 - lo 0
  else if v 0 = hi 0 then (hi 0 - lo 0) + (v 1 - lo 1)
  else if v 1 = hi 1 then (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 0 - v 0)
  else 2 * (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 1 - v 1)

/-- The position of a point of the bottom side. -/
theorem perimeterPos_of_bottom {lo hi v : LatticeSite 2} (h : v 1 = lo 1) :
    perimeterPos lo hi v = v 0 - lo 0 :=
  ite_eq_left h

/-- The position of a point of the right side above the lower-right corner. -/
theorem perimeterPos_of_right {lo hi v : LatticeSite 2} (h₀ : v 0 = hi 0) (h₁ : v 1 ≠ lo 1) :
    perimeterPos lo hi v = (hi 0 - lo 0) + (v 1 - lo 1) := by
  rw [perimeterPos, ite_eq_right h₁, ite_eq_left h₀]

/-- The position of a point of the top side left of the upper-right corner. -/
theorem perimeterPos_of_top {lo hi v : LatticeSite 2} (h₁ : v 1 = hi 1) (h₀ : v 0 ≠ hi 0)
    (h₁' : v 1 ≠ lo 1) :
    perimeterPos lo hi v = (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 0 - v 0) := by
  rw [perimeterPos, ite_eq_right h₁', ite_eq_right h₀, ite_eq_left h₁]

/-- The position of a point off the bottom, right and top sides, in particular of a point of the
left side strictly between its corners. -/
theorem perimeterPos_of_left {lo hi v : LatticeSite 2} (h₀ : v 0 ≠ hi 0) (h₁ : v 1 ≠ lo 1)
    (h₁' : v 1 ≠ hi 1) :
    perimeterPos lo hi v = 2 * (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 1 - v 1) := by
  rw [perimeterPos, ite_eq_right h₁, ite_eq_right h₀, ite_eq_right h₁']

/-- The lower-left corner has position zero. -/
@[simp]
theorem perimeterPos_self (lo hi : LatticeSite 2) : perimeterPos lo hi lo = 0 := by
  rw [perimeterPos_of_bottom rfl, sub_self]

/-- Positions of points of the box are nonnegative. -/
theorem perimeterPos_nonneg {lo hi v : LatticeSite 2} (hv : v ∈ Icc lo hi) :
    0 ≤ perimeterPos lo hi v := by
  rw [mem_Icc_two_iff] at hv
  unfold perimeterPos
  split_ifs <;> omega

/-- **Bound by the perimeter.** Positions of points of a box that is not a point are smaller than
its perimeter `2(hi₀ - lo₀) + 2(hi₁ - lo₁)`. -/
theorem perimeterPos_lt {lo hi v : LatticeSite 2} (hne : lo ≠ hi) (hv : v ∈ Icc lo hi) :
    perimeterPos lo hi v < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) := by
  rw [mem_Icc_two_iff] at hv
  have hlt : lo 0 < hi 0 ∨ lo 1 < hi 1 := by
    by_contra hc
    refine hne (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)) <;> omega
  unfold perimeterPos
  split_ifs <;> omega

/-- **Injectivity.** Distinct points of the boundary of a box have distinct positions. -/
theorem perimeterPos_injOn (lo hi : LatticeSite 2) :
    InjOn (perimeterPos lo hi) (boxBoundary lo hi) := by
  intro u hu v hv huv
  rw [mem_boxBoundary_two_iff] at hu hv
  unfold perimeterPos at huv
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> split_ifs at huv <;> omega

/-- **Translation.** Translating a point and the box by `c` keeps its position. -/
@[simp]
theorem perimeterPos_add (c lo hi v : LatticeSite 2) :
    perimeterPos (lo + c) (hi + c) (v + c) = perimeterPos lo hi v := by
  simp only [perimeterPos, Pi.add_apply, add_left_inj, add_sub_add_right_eq_sub]

/-- **Quarter turn.** The counterclockwise quarter turn `(x, y) ↦ (-y, x)` maps the box
`Icc lo hi` onto `[-hi₁, -lo₁] × [lo₀, hi₀]` and its lower-left corner to the lower-right corner
of the turned box, so it shifts the position of each boundary point by the height
`hi₁ - lo₁` of the box, modulo the perimeter. The box must have positive width and height: on a
segment the positions run along it only once. -/
theorem perimeterPos_rotate {lo hi v : LatticeSite 2} (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    (hv : v ∈ boxBoundary lo hi) :
    perimeterPos ![-hi 1, lo 0] ![-lo 1, hi 0] ![-v 1, v 0] =
      (perimeterPos lo hi v + (hi 1 - lo 1)) % (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) := by
  rw [mem_boxBoundary_two_iff] at hv
  have key : ∀ X Y P : ℤ, 0 ≤ X → X < P → (Y = X ∨ Y = X + P) → X = Y % P := by
    rintro X Y P hX hXP (rfl | rfl)
    · exact (Int.emod_eq_of_lt hX hXP).symm
    · rw [Int.add_emod_right, Int.emod_eq_of_lt hX hXP]
  unfold perimeterPos
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine key _ _ _ ?_ ?_ ?_ <;> split_ifs <;> omega

/-! ### Crossing bounds -/

/-- **Crossing bounds of both colours up to scale `L`.** Under `law q`, for every aspect ratio
`k`, every box of `ℤ²` of size `k n × n` with `1 ≤ n ≤ L`, in either orientation and at any
position, is crossed in its long direction with probability at least `c k > 0`, both by open
edges and by dual-open edges, the edges open in `dualConfig ω` (the box is then a box of faces,
the dual vertex `f` standing for the face with lower-left corner `f`). Direction `i = 0` is the
box `[lo, lo + (k n, n)]` crossed from left to right, direction `i = 1` the box
`[lo, lo + (n, k n)]` crossed from bottom to top. At `1/2` such bounds hold at every scale,
`L = ⊤`, by the Russo–Seymour–Welsh bounds; near `1/2` they hold below the characteristic
length. -/
structure CrossingBounds (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞) (c : ℕ → ℝ≥0∞) :
    Prop where
  /-- The bounds are positive. -/
  pos : ∀ k, 0 < c k
  /-- Open crossings in the long direction. -/
  le_law_crossing : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n → (n : ℕ∞) ≤ L →
    c k ≤ law q (crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]))
  /-- Dual-open crossings in the long direction. -/
  le_law_dualConfig_crossing : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n →
    (n : ℕ∞) ≤ L →
    c k ≤ law q (dualConfig ⁻¹'
      crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]))

namespace CrossingBounds

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- Left-right open crossings of the boxes `[lo, lo + (k n, n)]`. -/
theorem le_law_crossing_zero (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2) {n : ℕ}
    (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (crossing 0 lo (lo + ![(k : ℤ) * n, n])) :=
  h.le_law_crossing k 0 lo n hn hnL

/-- Bottom-top open crossings of the boxes `[lo, lo + (n, k n)]`. -/
theorem le_law_crossing_one (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2) {n : ℕ}
    (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (crossing 1 lo (lo + ![(n : ℤ), k * n])) :=
  h.le_law_crossing k 1 lo n hn hnL

/-- Left-right dual-open crossings of the boxes of faces `[lo, lo + (k n, n)]`. -/
theorem le_law_dualConfig_crossing_zero (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (dualConfig ⁻¹' crossing 0 lo (lo + ![(k : ℤ) * n, n])) :=
  h.le_law_dualConfig_crossing k 0 lo n hn hnL

/-- Bottom-top dual-open crossings of the boxes of faces `[lo, lo + (n, k n)]`. -/
theorem le_law_dualConfig_crossing_one (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    c k ≤ law q (dualConfig ⁻¹' crossing 1 lo (lo + ![(n : ℤ), k * n])) :=
  h.le_law_dualConfig_crossing k 1 lo n hn hnL

/-- **Monotonicity.** Crossing bounds up to scale `L` give smaller positive bounds up to any
smaller scale. -/
theorem mono {L' : ℕ∞} {c' : ℕ → ℝ≥0∞} (h : CrossingBounds q L c) (hL : L' ≤ L) (hc : c' ≤ c)
    (hpos : ∀ k, 0 < c' k) : CrossingBounds q L' c' where
  pos := hpos
  le_law_crossing k i lo n hn hnL :=
    (hc k).trans (h.le_law_crossing k i lo n hn (hnL.trans hL))
  le_law_dualConfig_crossing k i lo n hn hnL :=
    (hc k).trans (h.le_law_dualConfig_crossing k i lo n hn (hnL.trans hL))

/-- **Translation.** Crossing bounds pass to the law seen from `a`, with profile
`e ↦ q (e + a)`: its configuration is that of `law q` translated by `-a`. -/
theorem translate (h : CrossingBounds q L c) (a : LatticeSite 2) :
    CrossingBounds (fun e => q (Sym2.map (· + a) e)) L c := by
  have hlaw : ∀ A : Set (Config (LatticeSite 2)),
      law (fun e => q (Sym2.map (· + a) e)) A =
        law q ((fun ω => Sym2.map (· + -a) '' ω) ⁻¹' A) := by
    intro A
    have hmap := PercLib.Probability.prodBernoulli_map_image_sym2 q (Equiv.addRight (-a))
    have hq : (q ∘ Sym2.map (Equiv.addRight (-a)).symm) = fun e => q (Sym2.map (· + a) e) := by
      funext e
      simp only [Function.comp_apply, Equiv.addRight_symm, neg_neg, Equiv.coe_addRight]
    rw [hq] at hmap
    unfold law
    rw [← hmap]
    exact map_image_sym2Map_apply _ _ _
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      (fun ω => Sym2.map (· + -a) '' ω) ⁻¹' crossing i lo hi = crossing i (lo + a) (hi + a) := by
    intro i lo hi
    ext ω
    have := image_add_mem_crossing_iff (-a) i (lo + a) (hi + a) ω
    rw [add_neg_cancel_right, add_neg_cancel_right] at this
    rw [mem_preimage]
    exact this
  have hdual : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      (fun ω => Sym2.map (· + -a) '' ω) ⁻¹' (dualConfig ⁻¹' crossing i lo hi) =
        dualConfig ⁻¹' crossing i (lo + a) (hi + a) := by
    intro i lo hi
    ext ω
    have := image_add_mem_crossing_iff (-a) i (lo + a) (hi + a) (dualConfig ω)
    rw [add_neg_cancel_right, add_neg_cancel_right, ← dualConfig_image_add] at this
    simp only [mem_preimage]
    exact this
  refine ⟨h.pos, fun k i lo n hn hnL => ?_, fun k i lo n hn hnL => ?_⟩
  · rw [hlaw, hcross, add_right_comm lo]
    exact h.le_law_crossing k i (lo + a) n hn hnL
  · rw [hlaw, hdual, add_right_comm lo]
    exact h.le_law_dualConfig_crossing k i (lo + a) n hn hnL

end CrossingBounds

/-- **The trivial case.** Every law has crossing bounds up to scale zero, with any positive
bounds: no box has `1 ≤ n ≤ 0`. -/
theorem crossingBounds_zero (q : Sym2 (LatticeSite 2) → unitInterval) {c : ℕ → ℝ≥0∞}
    (hc : ∀ k, 0 < c k) : CrossingBounds q 0 c where
  pos := hc
  le_law_crossing _ _ _ n hn hn0 := by
    have : n ≤ 0 := by exact_mod_cast hn0
    omega
  le_law_dualConfig_crossing _ _ _ n hn hn0 := by
    have : n ≤ 0 := by exact_mod_cast hn0
    omega

/-! ### Faces of boxes and of dual edges -/

section Faces

variable {d : ℕ}

/-- A corner `x` of a face `f` of the box `Icc lo hi`, the face `f` read as a dual vertex in the
box `Icc lo (hi - 1)` of the faces of the box, lies in the box. -/
theorem mem_Icc_of_mem_Icc_sub_one {lo hi f x : LatticeSite d} (hf : f ∈ Icc lo (hi - 1))
    (hx : x ∈ Icc f (f + 1)) : x ∈ Icc lo hi :=
  ⟨hf.1.trans hx.1, fun i => by
    have h₁ : x i ≤ f i + 1 := hx.2 i
    have h₂ : f i ≤ hi i - 1 := hf.2 i
    change x i ≤ hi i
    omega⟩

/-- A face with a corner in the box `Icc lo hi` lies in the box `Icc (lo - 1) hi` of the faces
touching it. -/
theorem mem_Icc_sub_one_of_mem_Icc {lo hi f x : LatticeSite d} (hx : x ∈ Icc lo hi)
    (hxf : x ∈ Icc f (f + 1)) : f ∈ Icc (lo - 1) hi :=
  ⟨fun i => by
    have h₁ : lo i ≤ x i := hx.1 i
    have h₂ : x i ≤ f i + 1 := hxf.2 i
    change lo i - 1 ≤ f i
    omega, fun i => (hxf.1 i).trans (hx.2 i)⟩

end Faces

/-- The ends of an edge are corners of both faces of its dual edge. -/
theorem mem_Icc_of_mem_dualEdge {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    {x h : LatticeSite 2} (hx : x ∈ e) (hh : h ∈ dualEdge e) : x ∈ Icc h (h + 1) := by
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.one_apply]
  obtain ⟨a, b, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hh
    rw [Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hx
    omega
  · rw [dualEdge_vertical, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hh
    rw [Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hx
    omega

/-! ### Non-vacuity -/

/-- With no open edge there is no arm of radius one in `ℤ²`. -/
example : (∅ : Config (LatticeSite 2)) ∉ armEvent 0 1 :=
  empty_notMem_armEvent le_rfl

/-- With every edge open there is an arm of radius one in `ℤ²`. -/
example : (univ : Config (LatticeSite 2)) ∈ armEvent 0 1 :=
  univ_mem_armEvent 0 1

/-- With every edge open the four strips of an annulus are crossed. -/
example (z : LatticeSite 2) : (univ : Config (LatticeSite 2)) ∈ fourStrip z 1 :=
  univ_mem_fourStrip z 1

/-- With no open edge the four strips of an annulus are not crossed: the event is not
everything. -/
example (z : LatticeSite 2) : (∅ : Config (LatticeSite 2)) ∉ fourStrip z 1 := fun h =>
  empty_notMem_crossing (by simp) (mem_fourStrip_iff.1 h).1

/-- The corners of `[0, 2]²` are on its boundary and its centre is not. -/
example : ![0, 2] ∈ boxBoundary (0 : LatticeSite 2) ![2, 2] ∧
    ![1, 1] ∉ boxBoundary (0 : LatticeSite 2) ![2, 2] := by
  norm_num [mem_boxBoundary_two_iff]

/-- Counterclockwise around the unit square: the corners `(0, 0)`, `(1, 0)`, `(1, 1)` and
`(0, 1)` have positions `0`, `1`, `2` and `3`. -/
example : perimeterPos 0 1 ![0, 0] = 0 ∧ perimeterPos 0 1 ![1, 0] = 1 ∧
    perimeterPos 0 1 ![1, 1] = 2 ∧ perimeterPos 0 1 ![0, 1] = 3 := by
  norm_num [perimeterPos]

/-- Crossing bounds can hold: every law has them up to scale zero. The bounds at `1/2` at every
scale need the Russo–Seymour–Welsh bounds and are proved with them. -/
example (q : Sym2 (LatticeSite 2) → unitInterval) : CrossingBounds q 0 fun _ => 1 :=
  crossingBounds_zero q fun _ => one_pos

end PercLib.Models.Planar
