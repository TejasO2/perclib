/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions and proofs, written on 2026-11-21. No upstream code is copied.
Mathematical reference: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (one-arm bounds, pp. 23-24).
-/
module

public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import PercLib.Models.Planar.Defs
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.FirstExit

/-!
# Arm events and the four-strip event

Two events of bond percolation on `ℤ^d`, on the bond interface of the library: a configuration
is a `Set (Sym2 (LatticeSite d))`, and only its nearest-neighbour pairs are read.

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

Boxes stay `Set.Icc lo hi`, with `(r : LatticeSite d)` the constant vector `r`;
`Site.closedBall_eq_Icc` identifies the box `x + [-r, r]^d` with the closed ball of the sup
metric.

## Main definitions

* `PercLib.Models.Planar.armEvent`
* `PercLib.Models.Planar.fourStrip`

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
* `edgeSet_mem_localConn_Icc`: any two points of a box of `ℤ^d` are joined by nearest-neighbour
  edges inside the box.
* `image_add_inter_edgeSet_mem_localConn_iff`: translations carry connections inside a set.
* `Bond.inter_mem_localConn_iff_of_inter_eq`: a connection inside `S` is determined by the pairs
  inside any `T ⊇ S`.
* `Site.closedBall_eq_Icc`, `Site.apply_le_apply_add_one_of_adj`: sup-metric balls of `ℤ^d` are
  boxes, and a nearest-neighbour step moves each coordinate by at most one.
-/

@[expose] public section

noncomputable section

open Set PercLib.Percolation.Bond PercLib.Models.Site

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
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      Sym2.map (· + c) '' ω ∈ crossing i (lo + c) (hi + c) ↔ ω ∈ crossing i lo hi := by
    intro i lo hi
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
  simp only [mem_fourStrip_iff, add_right_comm z c, hcross]

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

end PercLib.Models.Planar
