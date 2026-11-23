/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: W. Werner, Lectures on two-dimensional critical percolation, IAS/Park City
Mathematics Series 16 (2009), arXiv:0710.0856, first exercise sheet (two-arm exponent in the
half-plane); P. Nolin, Near-critical percolation in two dimensions, Electron. J. Probab. 13 (2008),
paper no. 55, Theorem 24(1).
-/
module

public import PercLib.Models.Planar.Arms.QuasiMultiplicativity

/-!
# Two arms in the half-plane

At `1/2`, the probability that the boundary vertex `0` of the upper half-plane has an open arm and,
counterclockwise after it, a dual arm to distance `R` inside the half-plane is of order `1/R`
(`halfArmEvent ![true, false] 0 0 R`). The proof is Werner's elementary count; it uses no
separation of arms and no quasi-multiplicativity.

* **Upper bound.** In the half-box `[-3s, 3s] × [0, 3s]` with `4s + 1 ≤ R`, consider the bottom
  points `x = (k, 0)`, `|k| ≤ s`. If `x` has the two arms, then after closing the edge on the left
  of `x` (and possibly the edge above it), or the mirror edges on the right, `x` is joined inside
  the half-box to its left, right or top side, and to no bottom point two or more steps to one side:
  the dual arm, prolonged through the closed edges to the face below the line, separates them
  (mixed interlacing). Closing one edge of probability `1/2` at most doubles a probability. Points
  of one parity with this property lie in distinct clusters of the half-box, each joining `B_s(0)`
  to sup-norm `3s`, so `k` of them give `k` disjoint occurrences of that event; by BK and a dual
  circuit the expected number of such points is bounded. With translation invariance,
  `(2s + 1) P(A₂⁺(R)) ≤ C`.
* **Lower bound.** With probability bounded below, the strip `[R, 2R] × [0, 4R]` has an open
  bottom-top crossing and the strip of faces `[-2R, -R] × [-1, 4R]` a dual one (independent
  events). In the half-box `[-4R, 4R] × [0, 4R]`, let `x` be the leftmost bottom point joined to
  the open crossing. The dual crossing keeps `x` in `(-2R, 2R]` (interlacing). The cluster gives an
  open arm from `x`; quad duality, for the configuration with every other bottom edge opened, gives
  a dual path from the face on the upper left of `x` to the boundary, above the bottom row; and
  interlacing in the upper half of `B_R(x)` puts the open arm first. So some `x = (k, 0)`,
  `k ∈ (-2R, 2R]`, has the two arms, and `c ≤ 4R P(A₂⁺(R))`.

## Main results

* `exists_halfArmEvent_two_bounds`: `c / R ≤ P(A₂⁺(R)) ≤ C / R` for `R ≥ 1`, at `1/2`.
* `exists_mul_law_halfArmEvent_two_le`, `exists_pos_le_mul_law_halfArmEvent_two`: the two bounds,
  `R P(A₂⁺(R)) ≤ C` and `c ≤ 4R P(A₂⁺(R))`.
* `mem_or_mem_of_mem_halfArmEvent_two`: a two-arm point becomes an extreme point of its cluster
  in the half-box after closing at most two edges at it.
* `exists_mem_halfArmEvent_two_of_mem_crossing`: two strip crossings give a two-arm point.
* `exists_dualWalk_of_forall_notMem_localConn`: a dual path from the edge on the left of a bottom
  point that no open path crosses, by quad duality.
* `landingPos_lt_of_dualWalk`: the landing order of an open arm and a dual walk from the upper left
  face, by interlacing in the upper half-box.
* `law_setOf_diff_singleton_mem_le`,
  `PercLib.Probability.prodBernoulli_setOf_diff_singleton_mem_le`: closing a coordinate.
* `sum_law_le_sum_pow_of_forall_mem_foldl`: counting events with the BK inequality.
* `law_halfArmEvent_eq_law_halfArmEvent_zero`: translation invariance of half-plane arm events.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

namespace PercLib.Probability

/-- **Closing one coordinate.** The configurations that land in `F` once the coordinate `i` is
closed have probability at most `P(F) / P(i closed)`. -/
theorem prodBernoulli_setOf_diff_singleton_mem_le {ι : Type*} [Countable ι]
    (p : ι → unitInterval) (i : ι) (F : Set (Set ι)) :
    (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) *
        prodBernoulli p {ω | ω \ {i} ∈ F} ≤
      prodBernoulli p F := by
  classical
  set M := toMeasurable (prodBernoulli p) F
  have hFM : F ⊆ M := subset_toMeasurable _ _
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hsub : {ω : Set ι | ω \ {i} ∈ F} ⊆ (fun ω => ω \ {i}) ⁻¹' M := fun ω hω => hFM hω
  have hmap := prodBernoulli_map_diff_singleton p i
  have h1 : prodBernoulli p ((fun ω => ω \ {i}) ⁻¹' M) =
      PercLib.Probability.prodBernoulli (Function.update p i 0) M := by
    rw [← hmap, Measure.map_apply (measurable_diff_singleton i) hM]
  have h2 := prodBernoulli_eq_smul_add_smul p i
  calc (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) *
        prodBernoulli p {ω | ω \ {i} ∈ F}
      ≤ (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) *
          PercLib.Probability.prodBernoulli (Function.update p i 0) M := by
        rw [← h1]; gcongr
    _ ≤ prodBernoulli p M := by
        conv_rhs => rw [h2]
        simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ENNReal.smul_def]
        exact le_add_self
    _ = prodBernoulli p F := measure_toMeasurable F

end PercLib.Probability

namespace PercLib.Models.Planar

section HalfPlaneTwoArms

variable {lo hi : LatticeSite 2} {ω : Config (LatticeSite 2)}

/-- **A dual walk crossing edges of the box.** A walk of faces of `Icc (lo - 1) hi` along dual-open
edges, each with a face inside the box, is a dual-open path crossing only edges of the box, as in
quad duality. -/
theorem dualConfig_inter_image_mem_localConn_of_walk {f g : LatticeSite 2}
    (δ : (zdGraph 2).Walk f g)
    (hδ : ∀ h ∈ δ.support, h ∈ Icc (lo - 1) hi)
    (hE : ∀ E ∈ δ.edges, E ∈ dualConfig ω ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1)) :
    dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g := by
  refine localConn_mono inter_subset_left (mem_localConn_of_walk δ hδ fun E hE' => ?_)
  obtain ⟨hEd, h, hhE, hh⟩ := hE E hE'
  refine ⟨hEd, ?_⟩
  obtain ⟨e, he, -, rfl⟩ := (mem_dualConfig_iff' ω E).1 hEd
  exact ⟨e, ⟨he, fun x hx => mem_Icc_of_mem_Icc_sub_one hh (mem_Icc_of_mem_dualEdge he hx hhE)⟩,
    rfl⟩

/-- A point of the bottom side comes before every boundary point above the bottom row. -/
theorem perimeterPos_lt_perimeterPos_of_bottom {u y : LatticeSite 2} (hu : u 1 = lo 1)
    (hu0 : u 0 ≤ hi 0) (hy : y ∈ boxBoundary lo hi) (hy1 : lo 1 < y 1) :
    perimeterPos lo hi u < perimeterPos lo hi y := by
  rw [mem_boxBoundary_two_iff] at hy
  rw [perimeterPos_of_bottom hu]
  unfold perimeterPos
  split_ifs <;> omega

/-- **Interlacing at a bottom point, on the left.** In a box, let a dual path, crossing only edges
of the box, join the face below the edge on the left of a bottom point `x` to a face outside the box
with a corner above the bottom row. Then no open path inside the box joins `x` to a bottom point
two or more steps to its left. -/
theorem notMem_localConn_of_dualConfig_left (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {x a f g y : LatticeSite 2} (hx1 : x 1 = lo 1) (hx0 : lo 0 < x 0) (hxh : x 0 ≤ hi 0)
    (ha1 : a 1 = lo 1) (ha0 : lo 0 ≤ a 0) (hax : a 0 + 2 ≤ x 0) (hf0 : f 0 + 1 = x 0)
    (hf1 : f 1 + 1 = x 1) (hg : g ∉ Icc lo (hi - 1)) (hy : y ∈ boxBoundary lo hi)
    (hyg : y ∈ Icc g (g + 1)) (hy1 : lo 1 < y 1)
    (hδ : dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g) :
    ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a := by
  intro hxa
  obtain ⟨x', hx'0, hx'1⟩ : ∃ p : LatticeSite 2, p 0 = x 0 - 1 ∧ p 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  have hxB : x ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have haB : a ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hx'B : x' ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hfo : f ∉ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  have hx'f : x' ∈ Icc f (f + 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
  have hpy := perimeterPos_lt_perimeterPos_of_bottom hx1 hxh hy hy1
  refine dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxa hxB haB hfo hx'B hx'f hg hy hyg
    (Or.inr ⟨?_, ?_, Or.inr hpy⟩) hδ
  · rw [perimeterPos_of_bottom ha1, perimeterPos_of_bottom (hx'1.trans hx1)]; omega
  · rw [perimeterPos_of_bottom (hx'1.trans hx1), perimeterPos_of_bottom hx1]; omega

/-- **Interlacing at a bottom point, on the right.** The mirror image of
`notMem_localConn_of_dualConfig_left`: a dual path from the face below the edge on the right of `x`
to a face outside the box above the bottom row separates `x` from the bottom points two or more
steps to its right. -/
theorem notMem_localConn_of_dualConfig_right (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {x a f g y : LatticeSite 2} (hx1 : x 1 = lo 1) (hx0 : lo 0 ≤ x 0) (hxh : x 0 < hi 0)
    (ha1 : a 1 = lo 1) (ha0 : a 0 ≤ hi 0) (hax : x 0 + 2 ≤ a 0) (hf0 : f 0 = x 0)
    (hf1 : f 1 + 1 = x 1) (hg : g ∉ Icc lo (hi - 1)) (hy : y ∈ boxBoundary lo hi)
    (hyg : y ∈ Icc g (g + 1)) (hy1 : lo 1 < y 1)
    (hδ : dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g) :
    ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a := by
  intro hxa
  obtain ⟨x', hx'0, hx'1⟩ : ∃ p : LatticeSite 2, p 0 = x 0 + 1 ∧ p 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  have hxB : x ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have haB : a ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hx'B : x' ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hfo : f ∉ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  have hx'f : x' ∈ Icc f (f + 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
  have hpy := perimeterPos_lt_perimeterPos_of_bottom ha1 ha0 hy hy1
  refine dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxa hxB haB hfo hx'B hx'f hg hy hyg
    (Or.inl ⟨?_, ?_, Or.inr hpy⟩) hδ
  · rw [perimeterPos_of_bottom hx1, perimeterPos_of_bottom (hx'1.trans hx1)]; omega
  · rw [perimeterPos_of_bottom (hx'1.trans hx1), perimeterPos_of_bottom ha1]; omega

/-- **The open arm up to its exit from a box.** An open arm of `B_R(x)` from `x`, above the
bottom row of a box lying in the interior of `B_R(x)` and containing its start, reaches the left,
right or top side of the box along edges of the box; this holds in every configuration containing
the edges of the arm. -/
theorem exists_inter_mem_localConn_of_isOpenArm {x a b : LatticeSite 2} {R : ℕ}
    {α : (zdGraph 2).Walk a b} (hα : IsOpenArm ω x 0 (x - R) (x + R) α)
    (hlo : ∀ v ∈ α.support, lo 1 ≤ v 1) (ha : a ∈ Icc lo hi)
    (hsub : Icc lo hi ⊆ Icc (x - R + 1) (x + R - 1)) {ω' : Config (LatticeSite 2)}
    (hω' : ∀ e ∈ α.edges, e ∈ ω') :
    ∃ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
      ω' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) a v := by
  have hb : b ∉ Icc lo hi := fun h => hα.isCrossing.end_notMem (hsub h)
  obtain ⟨c, q, s, hqs, hc, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem α hb
  have hqn : ¬q.Nil := fun hn => hc (by rw [← hn.eq]; exact ha)
  have hqα : ∀ w ∈ q.support, w ∈ α.support := fun w hw => by
    rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hw
  have hqe : ∀ e ∈ q.edges, e ∈ α.edges := fun e he => by
    rw [← hqs, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he
  have hvd : q.penultimate ∈ q.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hqn]; exact SimpleGraph.Walk.end_mem_support _
  have hvH := hq _ hvd
  have hadj := q.adj_penultimate hqn
  have hc1 := hlo c (hqα c (SimpleGraph.Walk.end_mem_support _))
  refine ⟨q.penultimate, hvH, ?_, mem_localConn_of_walk q.dropLast (fun w hw => ?_) fun e he => ?_⟩
  · rw [zdGraph_two_adj_iff] at hadj
    rw [mem_Icc_two_iff] at hvH hc
    omega
  · rw [SimpleGraph.Walk.support_dropLast hqn] at hw
    exact hq w hw
  · rw [SimpleGraph.Walk.edges_dropLast] at he
    exact hω' e (hqe e (List.dropLast_subset _ he))

/-- **The dual arm up to its exit from a box.** A dual arm of `B_R(x)`, above the bottom row of a
box whose faces lie in those of `B_R(x)` and contain its first face, contains a dual walk from its
first face to a face outside the box with a corner above the bottom row, every step of which has a
face inside the box. -/
theorem exists_walk_of_isDualArm {x a b : LatticeSite 2} {R : ℕ}
    {β : (zdGraph 2).Walk a b} (hβ : IsDualArm ω x 0 (x - R) (x + R) β)
    (hlo : ∀ f ∈ β.support, lo 1 ≤ f 1) (ha : a ∈ Icc lo (hi - 1))
    (hsub : Icc lo (hi - 1) ⊆ Icc (x - R) (x + R - 1)) :
    ∃ g y, g ∉ Icc lo (hi - 1) ∧ y ∈ boxBoundary lo hi ∧ y ∈ Icc g (g + 1) ∧ lo 1 < y 1 ∧
      ∃ q : (zdGraph 2).Walk a g, (∀ h ∈ q.support, h ∈ Icc (lo - 1) hi) ∧
        ∀ E ∈ q.edges, E ∈ dualConfig ω ∧ ∃ h ∈ E, h ∈ Icc lo (hi - 1) := by
  have hb : b ∉ Icc lo (hi - 1) := fun h => hβ.isCrossing.end_notMem (hsub h)
  obtain ⟨g, q, s, hqs, hg, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem β hb
  have hqn : ¬q.Nil := fun hn => hg (by rw [← hn.eq]; exact ha)
  have hqβ : ∀ w ∈ q.support, w ∈ β.support := fun w hw => by
    rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inl hw
  have hqe : ∀ e ∈ q.edges, e ∈ β.edges := fun e he => by
    rw [← hqs, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he
  have hvd : q.penultimate ∈ q.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hqn]; exact SimpleGraph.Walk.end_mem_support _
  have hhT := hq _ hvd
  have hadj := q.adj_penultimate hqn
  have hg1 := hlo g (hqβ g (SimpleGraph.Walk.end_mem_support _))
  set h := q.penultimate with hh
  rw [mem_Icc_two_iff] at hhT
  simp only [Pi.sub_apply, Pi.one_apply] at hhT
  have hg' := hg
  rw [mem_Icc_two_iff] at hg'
  simp only [Pi.sub_apply, Pi.one_apply] at hg'
  rw [zdGraph_two_adj_iff] at hadj
  obtain ⟨y, hy0, hy1⟩ : ∃ y : LatticeSite 2, y 0 = max (g 0) (h 0) ∧
      y 1 = if g 1 = h 1 + 1 then g 1 else g 1 + 1 := ⟨![_, _], rfl, rfl⟩
  have hy1' : (g 1 = h 1 + 1 ∧ y 1 = g 1) ∨ (g 1 ≠ h 1 + 1 ∧ y 1 = g 1 + 1) := by
    rw [hy1]; split_ifs with h' <;> simp [h']
  refine ⟨g, y, hg, ?_, ?_, ?_, q, fun w hw => ?_,
    fun E hE => ⟨hβ.mem_of_mem_edges E (hqe E hE), ?_⟩⟩
  · rw [mem_boxBoundary_two_iff]; omega
  · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
  · omega
  · rw [← SimpleGraph.Walk.dropLast_support_concat q, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · have := hq w hw
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
      omega
    · rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hE
    refine ⟨d.fst, Sym2.mem_mk_left _ _, hq _ ?_⟩
    rw [← SimpleGraph.Walk.map_fst_darts]
    exact List.mem_map_of_mem hd


/-- **The first edge of an open arm from a vertex.** An edge of an open arm from `B_0(x) = {x}`
containing `x` is its first edge. -/
theorem IsOpenArm.eq_of_mem_edges_of_mem {x a b lo' hi' : LatticeSite 2}
    {α : (zdGraph 2).Walk a b} (hα : IsOpenArm ω x 0 lo' hi' α) {e : Sym2 (LatticeSite 2)}
    (he : e ∈ α.edges) (hx : x ∈ e) : e = s(a, α.snd) := by
  cases α with
  | nil => simp at he
  | cons h p =>
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · exfalso
      have hxp := mem_support_of_mem_edge p he hx
      refine hα.isCrossing.notMem_of_mem_tail x ?_ (by simp)
      rw [SimpleGraph.Walk.support_cons, List.tail_cons]
      exact hxp

/-- Faces of a closed edge of the box are joined by its dual edge. -/
theorem mem_localConn_of_adj_of_notMem {η : Config (LatticeSite 2)} {u v f g : LatticeSite 2}
    (huv : (zdGraph 2).Adj u v) (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi) (hη : s(u, v) ∉ η)
    (hf : f ∈ dualEdge s(u, v)) (hg : g ∈ dualEdge s(u, v)) :
    dualConfig η ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g :=
  mem_localConn_of_mem_dualEdge_of_notMem huv (fun w hw => by
    rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption) hη hf hg

/-- **Extreme points from two half-plane arms** (the upper bound, deterministic part). Let `x`
have an open arm and a dual arm to distance `R` in the upper half-plane through `x`, and let the
box `Icc lo hi` stand on the line through `x`, inside the interior of `B_R(x)`. Closing the edge
on the left of `x`, possibly also the edge above `x`, makes `x` a point of the bottom side joined
inside the box to its left, right or top side, and joined inside the box to no bottom point two or
more steps to its left; or the same holds on the right. The closed edges are never edges of the
open arm, and the dual arm, prolonged through them, separates `x` from that part of the bottom
side. -/
theorem mem_or_mem_of_mem_halfArmEvent_two {R : ℕ} {x xl xr xu : LatticeSite 2}
    (hxl : xl 0 + 1 = x 0 ∧ xl 1 = x 1) (hxr : xr 0 = x 0 + 1 ∧ xr 1 = x 1)
    (hxu : xu 0 = x 0 ∧ xu 1 = x 1 + 1) (hlo1 : lo 1 = x 1) (hlx : lo 0 < x 0)
    (hxh : x 0 < hi 0) (h₁ : lo 1 < hi 1) (hsub : Icc lo hi ⊆ Icc (x - R + 1) (x + R - 1))
    (hω : ω ∈ halfArmEvent ![true, false] x 0 R) :
    ((ω \ {s(xl, x)} ∈ {η : Config (LatticeSite 2) | (∃ v ∈ Icc lo hi,
        (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
        ∀ a : LatticeSite 2, a 1 = lo 1 → a 0 + 2 ≤ x 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a}) ∨
      ((ω \ {s(xl, x)}) \ {s(x, xu)} ∈ {η : Config (LatticeSite 2) | (∃ v ∈ Icc lo hi,
        (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
        ∀ a : LatticeSite 2, a 1 = lo 1 → a 0 + 2 ≤ x 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a})) ∨
    ((ω \ {s(x, xr)} ∈ {η : Config (LatticeSite 2) | (∃ v ∈ Icc lo hi,
        (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
        ∀ a : LatticeSite 2, a 1 = lo 1 → x 0 + 2 ≤ a 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a}) ∨
      ((ω \ {s(x, xr)}) \ {s(x, xu)} ∈ {η : Config (LatticeSite 2) | (∃ v ∈ Icc lo hi,
        (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
        ∀ a : LatticeSite 2, a 1 = lo 1 → x 0 + 2 ≤ a 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a})) := by
  obtain ⟨a, b, γ, hγ, -, hH, -⟩ := mem_halfArmEvent_iff.1 hω
  have hα : IsOpenArm ω x 0 (x - R) (x + R) (γ 0) := hγ 0
  have hβ : IsDualArm ω x 0 (x - R) (x + R) (γ 1) := hγ 1
  have hHα : ∀ v ∈ (γ 0).support, lo 1 ≤ v 1 := fun v hv => hlo1 ▸ hH 0 v hv
  have hHβ : ∀ v ∈ (γ 1).support, lo 1 ≤ v 1 := fun v hv => hlo1 ▸ hH 1 v hv
  have ha0 : a 0 = x := by
    have := hα.isCrossing.start_mem
    simpa using this
  have h₀ : lo 0 < hi 0 := by omega
  -- the faces at `x`
  obtain ⟨f₀, hf₀0, hf₀1⟩ : ∃ f : LatticeSite 2, f 0 + 1 = x 0 ∧ f 1 + 1 = x 1 :=
    ⟨![x 0 - 1, x 1 - 1], by simp, by simp⟩
  obtain ⟨f₀', hf₀'0, hf₀'1⟩ : ∃ f : LatticeSite 2, f 0 = x 0 ∧ f 1 + 1 = x 1 :=
    ⟨![x 0, x 1 - 1], by simp, by simp⟩
  obtain ⟨fL, hfL0, hfL1⟩ : ∃ f : LatticeSite 2, f 0 + 1 = x 0 ∧ f 1 = x 1 :=
    ⟨![x 0 - 1, x 1], by simp, by simp⟩
  obtain ⟨fR, hfR0, hfR1⟩ : ∃ f : LatticeSite 2, f 0 = x 0 ∧ f 1 = x 1 :=
    ⟨![x 0, x 1], by simp, by simp⟩
  -- boxes
  have hxH : x ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxlH : xl ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxrH : xr ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hxuH : xu ∈ Icc lo hi := by rw [mem_Icc_two_iff]; omega
  have hsub' : Icc lo (hi - 1) ⊆ Icc (x - R) (x + R - 1) := by
    intro f hf
    have h₁' := hsub (mem_Icc_of_mem_Icc_sub_one hf (left_mem_Icc.2 (by
      intro i; simp)))
    have h₂' := hsub (mem_Icc_of_mem_Icc_sub_one hf (right_mem_Icc.2 (by
      intro i; simp)))
    rw [mem_Icc_two_iff] at hf h₁' h₂' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, Pi.natCast_apply] at hf h₁' h₂' ⊢
    omega
  -- adjacency and dual edges
  have hadjl : (zdGraph 2).Adj xl x := by rw [zdGraph_two_adj_iff]; omega
  have hadjr : (zdGraph 2).Adj x xr := by rw [zdGraph_two_adj_iff]; omega
  have hadju : (zdGraph 2).Adj x xu := by rw [zdGraph_two_adj_iff]; omega
  have hd₁ : f₀ ∈ dualEdge s(xl, x) ∧ fL ∈ dualEdge s(xl, x) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hd₂ : fL ∈ dualEdge s(x, xu) ∧ fR ∈ dualEdge s(x, xu) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hd₃ : f₀' ∈ dualEdge s(x, xr) ∧ fR ∈ dualEdge s(x, xr) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  -- the first step of the open arm
  have hαn : ¬(γ 0).Nil := by
    intro hn
    have := hn.eq
    have hb := hα.isCrossing.end_notMem
    rw [← this, ha0] at hb
    exact hb (hsub hxH)
  have hsnd : (zdGraph 2).Adj x (γ 0).snd := by rw [← ha0]; exact (γ 0).adj_snd hαn
  have hsnd1 := hHα _ (List.mem_of_mem_tail ((γ 0).snd_mem_tail_support hαn))
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  have hsndc : (γ 0).snd = xr ∨ (γ 0).snd = xu ∨ (γ 0).snd = xl := by
    rw [zdGraph_two_adj_iff] at hsnd
    rcases hsnd with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
    · exact Or.inr (Or.inl (hpt _ _ (by omega) (by omega)))
    · omega
    · exact Or.inl (hpt _ _ (by omega) (by omega))
    · exact Or.inr (Or.inr (hpt _ _ (by omega) (by omega)))
  -- edges of the open arm at `x`
  have hedge : ∀ e ∈ (γ 0).edges, x ∈ e → e = s(x, (γ 0).snd) := fun e he hx => by
    exact (IsOpenArm.eq_of_mem_edges_of_mem hα he hx).trans
      (congrArg (fun p => s(p, (γ 0).snd)) ha0)
  have hne : ∀ p p' : LatticeSite 2, p ≠ p' → s(x, p) ≠ s(x, p') := fun p p' hpp' h => by
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, h'⟩
    · exact hpp' h
    · exact hpp' (h'.trans h)
  have hrl : xr ≠ xl := fun h => by have := congrFun h 0; omega
  have hul : xu ≠ xl := fun h => by have := congrFun h 1; omega
  have hur : xu ≠ xr := fun h => by have := congrFun h 1; omega
  have hlx' : s(xl, x) = s(x, xl) := Sym2.eq_swap
  -- the start of the dual arm
  have hstart : a 1 = fL ∨ a 1 = fR := by
    have h₁' := hβ.isCrossing.start_mem
    have h₂' := hHβ _ (SimpleGraph.Walk.start_mem_support _)
    simp only [Nat.cast_zero, sub_zero, add_zero] at h₁'
    rw [mem_Icc_two_iff] at h₁'
    simp only [Pi.sub_apply, Pi.one_apply] at h₁'
    rcases (show (a 1) 0 + 1 = x 0 ∨ (a 1) 0 = x 0 by omega) with h | h
    · exact Or.inl (hpt _ _ (by omega) (by omega))
    · exact Or.inr (hpt _ _ (by omega) (by omega))
  have ha1H : a 1 ∈ Icc lo (hi - 1) := by
    rcases hstart with h | h <;>
    · rw [h, mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  obtain ⟨g, y, hg, hy, hyg, hy1, q, hqs, hqE⟩ := exists_walk_of_isDualArm hβ hHβ ha1H hsub'
  have Lq : ∀ ω' : Config (LatticeSite 2), ω' ⊆ ω →
      dualConfig ω' ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) (a 1) g := fun ω' hω' =>
    dualConfig_inter_image_mem_localConn_of_walk q hqs fun E hE =>
      ⟨dualConfig_anti hω' (hqE E hE).1, (hqE E hE).2⟩
  have Lo : ∀ ω' : Config (LatticeSite 2), (∀ e ∈ (γ 0).edges, e ∈ ω') →
      ∃ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
        ω' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v := fun ω' hT => by
    have := exists_inter_mem_localConn_of_isOpenArm hα hHα (ha0 ▸ hxH) hsub hT
    rwa [ha0] at this
  -- the two sides
  have hFL : ∀ ω' : Config (LatticeSite 2), (∀ e ∈ (γ 0).edges, e ∈ ω') →
      dualConfig ω' ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f₀ g →
      ω' ∈ {η : Config (LatticeSite 2) | (∃ v ∈ Icc lo hi,
        (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
        ∀ a : LatticeSite 2, a 1 = lo 1 → a 0 + 2 ≤ x 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a} := fun ω' hT hδ => by
    refine ⟨Lo ω' hT, fun a' ha'1 hax => ?_⟩
    by_cases ha'0 : lo 0 ≤ a' 0
    · exact notMem_localConn_of_dualConfig_left h₀ h₁ hlo1.symm hlx hxh.le ha'1 ha'0 hax hf₀0
        hf₀1 hg hy hyg hy1 hδ
    · rw [localConn_of_notMem_right (by rw [mem_Icc_two_iff]; omega)]
      exact notMem_empty _
  have hFR : ∀ ω' : Config (LatticeSite 2), (∀ e ∈ (γ 0).edges, e ∈ ω') →
      dualConfig ω' ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f₀' g →
      ω' ∈ {η : Config (LatticeSite 2) | (∃ v ∈ Icc lo hi,
        (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
          η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x v) ∧
        ∀ a : LatticeSite 2, a 1 = lo 1 → x 0 + 2 ≤ a 0 →
          η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) x a} := fun ω' hT hδ => by
    refine ⟨Lo ω' hT, fun a' ha'1 hax => ?_⟩
    by_cases ha'0 : a' 0 ≤ hi 0
    · exact notMem_localConn_of_dualConfig_right h₀ h₁ hlo1.symm (by omega) hxh ha'1 ha'0 hax
        hf₀'0 hf₀'1 hg hy hyg hy1 hδ
    · rw [localConn_of_notMem_right (by rw [mem_Icc_two_iff]; omega)]
      exact notMem_empty _
  rcases hsndc with hs | hs | hs <;> rcases hstart with hb | hb
  · -- right step, dual arm at the upper-left face: close the left edge
    refine Or.inl (Or.inl (hFL _ (fun e he => ⟨hα.mem_of_mem_edges e he, fun h => ?_⟩) ?_))
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_right _ _)
      rw [hs, hlx'] at this
      exact hne _ _ hrl.symm this
    · exact localConn_trans (mem_localConn_of_adj_of_notMem hadjl hxlH hxH
        (fun h => h.2 rfl) hd₁.1 hd₁.2) (hb ▸ Lq _ sdiff_subset)
  · -- right step, dual arm at the upper-right face: close the left and the upper edges
    refine Or.inl (Or.inr (hFL _ (fun e he => ⟨⟨hα.mem_of_mem_edges e he, fun h => ?_⟩,
      fun h => ?_⟩) ?_))
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_right _ _)
      rw [hs, hlx'] at this
      exact hne _ _ hrl.symm this
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_left _ _)
      rw [hs] at this
      exact hne _ _ hur this
    · exact localConn_trans (localConn_trans (mem_localConn_of_adj_of_notMem hadjl hxlH hxH
        (fun h => h.1.2 rfl) hd₁.1 hd₁.2) (mem_localConn_of_adj_of_notMem hadju hxH hxuH
        (fun h => h.2 rfl) hd₂.1 hd₂.2)) (hb ▸ Lq _ (sdiff_subset.trans sdiff_subset))
  · -- upward step, dual arm at the upper-left face: close the left edge
    refine Or.inl (Or.inl (hFL _ (fun e he => ⟨hα.mem_of_mem_edges e he, fun h => ?_⟩) ?_))
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_right _ _)
      rw [hs, hlx'] at this
      exact hne _ _ hul.symm this
    · exact localConn_trans (mem_localConn_of_adj_of_notMem hadjl hxlH hxH
        (fun h => h.2 rfl) hd₁.1 hd₁.2) (hb ▸ Lq _ sdiff_subset)
  · -- upward step, dual arm at the upper-right face: close the right edge
    refine Or.inr (Or.inl (hFR _ (fun e he => ⟨hα.mem_of_mem_edges e he, fun h => ?_⟩) ?_))
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_left _ _)
      rw [hs] at this
      exact hne _ _ hur.symm this
    · exact localConn_trans (mem_localConn_of_adj_of_notMem hadjr hxH hxrH
        (fun h => h.2 rfl) hd₃.1 hd₃.2) (hb ▸ Lq _ sdiff_subset)
  · -- left step, dual arm at the upper-left face: close the right and the upper edges
    refine Or.inr (Or.inr (hFR _ (fun e he => ⟨⟨hα.mem_of_mem_edges e he, fun h => ?_⟩,
      fun h => ?_⟩) ?_))
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_left _ _)
      rw [hs] at this
      exact hne _ _ hrl this
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_left _ _)
      rw [hs] at this
      exact hne _ _ hul this
    · exact localConn_trans (localConn_trans (mem_localConn_of_adj_of_notMem hadjr hxH hxrH
        (fun h => h.1.2 rfl) hd₃.1 hd₃.2) (mem_localConn_of_adj_of_notMem hadju hxH hxuH
        (fun h => h.2 rfl) hd₂.2 hd₂.1)) (hb ▸ Lq _ (sdiff_subset.trans sdiff_subset))
  · -- left step, dual arm at the upper-right face: close the right edge
    refine Or.inr (Or.inl (hFR _ (fun e he => ⟨hα.mem_of_mem_edges e he, fun h => ?_⟩) ?_))
    · rw [mem_singleton_iff] at h
      subst h
      have := hedge _ he (Sym2.mem_mk_left _ _)
      rw [hs] at this
      exact hne _ _ hrl this
    · exact localConn_trans (mem_localConn_of_adj_of_notMem hadjr hxH hxrH
        (fun h => h.2 rfl) hd₃.1 hd₃.2) (hb ▸ Lq _ sdiff_subset)


/-! ### Probability: closing an edge, counting with BK, translation -/

/-- **Closing an edge of probability one half** at most doubles the probability. -/
theorem law_setOf_diff_singleton_mem_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {e : Sym2 (LatticeSite 2)} (he : (q e : ℝ) = 1 / 2) (F : Set (Config (LatticeSite 2))) :
    law q {ω | ω \ {e} ∈ F} ≤ 2 * law q F := by
  have h := PercLib.Probability.prodBernoulli_setOf_diff_singleton_mem_le q e F
  have hσ : (unitInterval.toNNReal (unitInterval.symm (q e)) : ℝ≥0∞) = 2⁻¹ := by
    have hof : ∀ t : unitInterval, (unitInterval.toNNReal t : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) :=
      fun t => by rw [ENNReal.ofReal, Real.toNNReal_of_nonneg t.2.1]; rfl
    rw [hof, unitInterval.coe_symm_eq, he,
      show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  rw [hσ] at h
  calc law q {ω | ω \ {e} ∈ F} = 2 * (2⁻¹ * law q {ω | ω \ {e} ∈ F}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * law q F := by gcongr; exact h

/-- **Counting with the BK inequality.** If any `k` of the events `F i`, `i ∈ S`, occurring
together give `k` disjoint occurrences of an increasing event `C`, the expected number of the
events that occur is at most `∑_{k ≤ |S|} P(C)^k`. -/
theorem sum_law_le_sum_pow_of_forall_mem_foldl {ι : Type*}
    (q : Sym2 (LatticeSite 2) → unitInterval) {C : Set (Config (LatticeSite 2))}
    (hC : IsUpperSet C) (S : Finset ι) (F : ι → Set (Config (LatticeSite 2)))
    (hF : ∀ i, MeasurableSet (F i))
    (hw : ∀ (ω : Config (LatticeSite 2)) (T : Finset ι), T ⊆ S → (∀ i ∈ T, ω ∈ F i) →
      ω ∈ (List.replicate T.card C).foldl disjointOccurrence univ) :
    ∑ i ∈ S, law q (F i) ≤ ∑ k ∈ Finset.range S.card, law q C ^ (k + 1) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Set (Config (LatticeSite 2)), M = fun k =>
      toMeasurable (law q) ((List.replicate (k + 1) C).foldl disjointOccurrence univ) :=
    ⟨_, rfl⟩
  have hMm : ∀ k, MeasurableSet (M k) := fun k => by
    rw [hM]; exact measurableSet_toMeasurable _ _
  have hMs : ∀ k, (List.replicate (k + 1) C).foldl disjointOccurrence univ ⊆ M k := fun k => by
    rw [hM]; exact subset_toMeasurable _ _
  have hMl : ∀ k, law q (M k) ≤ law q C ^ (k + 1) := fun k => by
    rw [hM, measure_toMeasurable]
    exact prodBernoulli_foldl_replicate_le_pow q hC (k + 1)
  have hpt : ∀ ω, ∑ i ∈ S, (F i).indicator (1 : Config (LatticeSite 2) → ℝ≥0∞) ω ≤
      ∑ k ∈ Finset.range S.card, (M k).indicator (1 : Config (LatticeSite 2) → ℝ≥0∞) ω := by
    intro ω
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole, Finset.sum_boole]
    norm_cast
    have hsub : Finset.range (S.filter fun i => ω ∈ F i).card ⊆
        (Finset.range S.card).filter fun k => ω ∈ M k := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨lt_of_lt_of_le hk (Finset.card_filter_le _ _), ?_⟩
      obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq
        (show k + 1 ≤ (S.filter fun i => ω ∈ F i).card by omega)
      have := hw ω T (hT.trans (Finset.filter_subset _ _))
        (fun i hi => (Finset.mem_filter.1 (hT hi)).2)
      rw [hTc] at this
      exact hMs k this
    calc (S.filter fun i => ω ∈ F i).card = (Finset.range _).card := (Finset.card_range _).symm
      _ ≤ _ := Finset.card_le_card hsub
  calc ∑ i ∈ S, law q (F i)
      = ∫⁻ ω, ∑ i ∈ S, (F i).indicator (1 : Config (LatticeSite 2) → ℝ≥0∞) ω ∂(law q) := by
        rw [lintegral_finsetSum _ fun i _ => measurable_one.indicator (hF i)]
        simp only [lintegral_indicator_one (hF _)]
    _ ≤ ∫⁻ ω, ∑ k ∈ Finset.range S.card,
          (M k).indicator (1 : Config (LatticeSite 2) → ℝ≥0∞) ω ∂(law q) := lintegral_mono hpt
    _ = ∑ k ∈ Finset.range S.card, law q (M k) := by
        rw [lintegral_finsetSum _ fun k _ => measurable_one.indicator (hMm k)]
        simp only [lintegral_indicator_one (hMm _)]
    _ ≤ ∑ k ∈ Finset.range S.card, law q C ^ (k + 1) := Finset.sum_le_sum fun k _ => hMl k

/-- A connection inside a countable set is a measurable event of the configuration. -/
theorem measurableSet_setOf_inter_mem_localConn (S : Set (LatticeSite 2)) (u v : LatticeSite 2) :
    MeasurableSet {η : Config (LatticeSite 2) | η ∩ (zdGraph 2).edgeSet ∈ localConn S u v} :=
  (measurableSet_localConn S u v).preimage (by fun_prop)

/-- **Disjoint witnesses.** Points of `B_s(0)` joined inside a set `H` to points at sup-norm at
least `3s`, no two of them joined inside `H`, give disjoint occurrences of the event that `B_s(0)`
is joined to sup-norm `3s`. -/
theorem mem_foldl_of_pairwise_notMem_localConn {ι : Type*} {ω : Config (LatticeSite 2)}
    {H : Set (LatticeSite 2)} {s : ℕ} (T : Finset ι) (x : ι → LatticeSite 2)
    (hx : ∀ i ∈ T, |x i 0| ≤ s ∧ |x i 1| ≤ s)
    (hv : ∀ i ∈ T, ∃ v, (3 * (s : ℤ) ≤ |v 0| ∨ 3 * (s : ℤ) ≤ |v 1|) ∧
      ω ∩ (zdGraph 2).edgeSet ∈ localConn H (x i) v)
    (hd : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ω ∩ (zdGraph 2).edgeSet ∉ localConn H (x i) (x j)) :
    ω ∈ (List.replicate T.card {η : Config (LatticeSite 2) | ∃ u v : LatticeSite 2,
      (|u 0| ≤ s ∧ |u 1| ≤ s) ∧ (3 * (s : ℤ) ≤ |v 0| ∨ 3 * (s : ℤ) ≤ |v 1|) ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn univ u v}).foldl disjointOccurrence univ := by
  classical
  set e := T.equivFin
  have h' : ∀ k : Fin T.card, ∃ v, (3 * (s : ℤ) ≤ |v 0| ∨ 3 * (s : ℤ) ≤ |v 1|) ∧
      ∃ p : (zdGraph 2).Walk (x (e.symm k)) v, (∀ w ∈ p.support, w ∈ H) ∧ ∀ f ∈ p.edges, f ∈ ω :=
    fun k => by
      obtain ⟨v, hv₁, hv₂⟩ := hv _ (e.symm k).2
      obtain ⟨p, hp, hpe⟩ := exists_walk_of_mem_localConn hv₂
      exact ⟨v, hv₁, p, hp, hpe⟩
  choose v hvs p hp hpe using h'
  have hconn : ∀ k, ∀ w ∈ (p k).support,
      ω ∩ (zdGraph 2).edgeSet ∈ localConn H (x (e.symm k)) w := fun k w hw =>
    mem_localConn_of_walk ((p k).takeUntil w hw)
      (fun u hu => hp k u ((p k).support_takeUntil_subset_support hw hu))
      (fun f hf => hpe k f ((p k).edges_takeUntil_subset_edges hw hf))
  refine mem_foldl_replicate_disjointOccurrence (fun a b hab ha => by
    obtain ⟨u, w, hu, hw, h⟩ := ha
    exact ⟨u, w, hu, hw, localConn_mono (inter_subset_inter_left _ hab) h⟩) T.card isUpperSet_univ ∅
    (fun k => {f | f ∈ (p k).edges}) finite_empty (fun k => (p k).edges.finite_toSet)
    (empty_subset _) (fun k f hf => hpe k f hf) (mem_univ _) (fun k => ?_)
    (fun _ => empty_disjoint _) fun k l hkl => ?_
  · exact ⟨x (e.symm k), v k, hx _ (e.symm k).2, hvs k,
      mem_localConn_edges_of_walk (p k) fun _ _ => mem_univ _⟩
  · refine disjoint_left.2 fun f hfk hfl => ?_
    obtain ⟨w, hw⟩ : ∃ w, w ∈ f := ⟨(Quot.out f).1, Sym2.out_fst_mem f⟩
    have h₁ := hconn k w (mem_support_of_mem_edge (p k) hfk hw)
    have h₂ := hconn l w (mem_support_of_mem_edge (p l) hfl hw)
    rw [localConn_comm] at h₂
    have hne : (e.symm k : ι) ≠ e.symm l := fun h => hkl (e.symm.injective (Subtype.ext h))
    exact hd _ (e.symm k).2 _ (e.symm l).2 hne (localConn_trans h₁ h₂)

/-- **Translation.** If the profile is constant on the edges of `ℤ²`, a half-plane arm event has
the probability of its translate. -/
theorem law_halfArmEventTo_add {q : Sym2 (LatticeSite 2) → unitInterval} {p : ℝ}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = p) {j : ℕ} (col : Fin j → Bool)
    (z c : LatticeSite 2) (r : ℕ) (lo hi : LatticeSite 2) (J I : Fin j → Set ℤ) :
    law q (halfArmEventTo col (z + c) r (lo + c) (hi + c) J I) =
      law q (halfArmEventTo col z r lo hi J I) := by
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := 2) c
  have hφf : (⇑φ : LatticeSite 2 → LatticeSite 2) = fun v => v + c := funext hφ
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q (Sym2.map φ e) = q e := by
    intro e he
    have he' : Sym2.map φ e ∈ (zdGraph 2).edgeSet := by
      rw [← image_sym2Map_edgeSet φ]
      exact mem_image_of_mem _ he
    exact Subtype.ext (by rw [hq _ he', hq _ he])
  have hAG : ∀ ω : Config (LatticeSite 2),
      ω ∩ (zdGraph 2).edgeSet ∈ halfArmEventTo col (z + c) r (lo + c) (hi + c) J I ↔
        ω ∈ halfArmEventTo col (z + c) r (lo + c) (hi + c) J I := fun ω =>
    mem_halfArmEventTo_iff_of_agree fun e he _ _ => ⟨fun h => h.1, fun h => ⟨h, he⟩⟩
  rw [← law_preimage_image_sym2Map_eq φ hq' (measurableSet_halfArmEventTo _ _ _ _ _ _ _) hAG,
    hφf]
  congr 1
  ext ω
  exact image_add_mem_halfArmEventTo_iff c

/-- **Translation of half-plane arm events** to the origin, when the profile is constant on the
edges of `ℤ²`. -/
theorem law_halfArmEvent_eq_law_halfArmEvent_zero {q : Sym2 (LatticeSite 2) → unitInterval}
    {p : ℝ} (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = p) {j : ℕ} (col : Fin j → Bool)
    (z : LatticeSite 2) (r R : ℕ) :
    law q (halfArmEvent col z r R) = law q (halfArmEvent col 0 r R) := by
  have h := law_halfArmEventTo_add hq col 0 z r (0 - (R : LatticeSite 2))
    (0 + (R : LatticeSite 2)) (fun _ => univ) (fun _ => univ)
  have e₁ : (0 : LatticeSite 2) + z = z := zero_add _
  have e₂ : (0 : LatticeSite 2) - R + z = z - R := by abel
  have e₃ : (0 : LatticeSite 2) + R + z = z + R := by abel
  rw [e₁, e₂, e₃] at h
  exact h


/-- The events used in the count of extreme points are measurable. -/
theorem measurableSet_setOf_exists_localConn_and_forall (H : Set (LatticeSite 2))
    (x : LatticeSite 2) (P Q₁ Q₂ : LatticeSite 2 → Prop) :
    MeasurableSet {η : Config (LatticeSite 2) | (∃ v ∈ H, P v ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn H x v) ∧
      ∀ a : LatticeSite 2, Q₁ a → Q₂ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a} := by
  have h : {η : Config (LatticeSite 2) | (∃ v ∈ H, P v ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn H x v) ∧
      ∀ a : LatticeSite 2, Q₁ a → Q₂ a → η ∩ (zdGraph 2).edgeSet ∉ localConn H x a} =
      (⋃ v ∈ {v | v ∈ H ∧ P v},
        {η : Config (LatticeSite 2) | η ∩ (zdGraph 2).edgeSet ∈ localConn H x v}) ∩
      ⋂ a ∈ {a : LatticeSite 2 | Q₁ a ∧ Q₂ a},
        {η : Config (LatticeSite 2) | η ∩ (zdGraph 2).edgeSet ∈ localConn H x a}ᶜ := by
    ext η
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_compl_iff,
      exists_prop, and_imp, and_assoc]
  rw [h]
  exact (MeasurableSet.biUnion (to_countable _) fun v _ =>
    measurableSet_setOf_inter_mem_localConn _ _ _).inter
    (MeasurableSet.biInter (to_countable _) fun a _ =>
      (measurableSet_setOf_inter_mem_localConn _ _ _).compl)

/-- A geometric sum of powers of `λ ≤ 1 - β` is at most `β⁻¹`. -/
theorem sum_range_pow_succ_le_inv {l β : ℝ≥0∞} (hβ : β ≤ 1) (hl : l ≤ 1 - β) (N : ℕ) :
    ∑ k ∈ Finset.range N, l ^ (k + 1) ≤ β⁻¹ := by
  have hl1 : l ≤ 1 := hl.trans tsub_le_self
  calc ∑ k ∈ Finset.range N, l ^ (k + 1) ≤ ∑ k ∈ Finset.range N, l ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc l ^ (k + 1) = l ^ k * l := pow_succ _ _
          _ ≤ l ^ k * 1 := mul_le_mul_right hl1 _
          _ = l ^ k := mul_one _
    _ ≤ ∑' k, l ^ k := ENNReal.sum_le_tsum _
    _ = (1 - l)⁻¹ := ENNReal.tsum_geometric l
    _ ≤ β⁻¹ := by
        refine ENNReal.inv_le_inv.2 (ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top
          ENNReal.one_ne_top hl1) ?_)
        calc l + β ≤ 1 - β + β := by gcongr
          _ = 1 := tsub_add_cancel_of_le hβ

/-- **Two arms in the half-plane, upper bound** (Werner's count of extreme points). There is
`C < ∞` such that `R · P(A₂⁺(R)) ≤ C` for every profile equal to `1/2` on the edges of `ℤ²`. -/
theorem exists_mul_law_halfArmEvent_two_le :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ,
        (R : ℝ≥0∞) * law q (halfArmEvent ![true, false] 0 0 R) ≤ C := by
  obtain ⟨c, hc⟩ := exists_crossingBounds_half
  set q₀ : Sym2 (LatticeSite 2) → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
  have hq₀ : ∀ e ∈ (zdGraph 2).edgeSet, (q₀ e : ℝ) = 1 / 2 := fun _ _ => rfl
  set β := c 7 ^ 4 with hβ
  have hβ0 : β ≠ 0 := (ENNReal.pow_pos ((hc q₀ hq₀).pos 7) 4).ne'
  have hβ1 : β ≤ 1 :=
    (pow_le_law_compl_crossing_inter (hc q₀ hq₀) (t := 1) (m := 1) rfl le_top).trans prob_le_one
  refine ⟨96 * β⁻¹ + 4, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.inv_ne_top.2 hβ0), ENNReal.ofNat_ne_top⟩, fun q hq R => ?_⟩
  have hCB := hc q hq
  set s := (R - 1) / 4 with hs
  by_cases hs1 : s = 0
  · have hR : (R : ℝ≥0∞) ≤ 4 := by exact_mod_cast (show R ≤ 4 by omega)
    calc (R : ℝ≥0∞) * law q (halfArmEvent ![true, false] 0 0 R) ≤ 4 * 1 :=
          mul_le_mul' hR prob_le_one
      _ ≤ 96 * β⁻¹ + 4 := by rw [mul_one]; exact le_add_self
  -- the event joining `B_s(0)` to sup-norm `3s`, and its probability
  set Cs := {η : Config (LatticeSite 2) | ∃ u v : LatticeSite 2,
      (|u 0| ≤ s ∧ |u 1| ≤ s) ∧ (3 * (s : ℤ) ≤ |v 0| ∨ 3 * (s : ℤ) ≤ |v 1|) ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn univ u v} with hCs
  have hCup : IsUpperSet Cs := fun a b hab ha => by
    obtain ⟨u, w, hu, hw, h⟩ := ha
    exact ⟨u, w, hu, hw, localConn_mono (inter_subset_inter_left _ hab) h⟩
  have hlam : law q Cs ≤ 1 - β := by
    have hK := pow_le_law_compl_crossing_inter hCB (t := s) (m := 2 * s - 1) (by omega) le_top
    set K := (crossing 1 ![-3 * (s : ℤ), s] ![3 * s, 3 * s])ᶜ ∩
      (crossing 1 ![-3 * (s : ℤ), -3 * s] ![3 * s, -s])ᶜ ∩
      (crossing 0 ![(s : ℤ), -3 * s] ![3 * s, 3 * s])ᶜ ∩
      (crossing 0 ![-3 * (s : ℤ), -3 * s] ![-s, 3 * s])ᶜ with hKdef
    have hKm : MeasurableSet K := (((measurableSet_crossing _ _ _).compl.inter
      (measurableSet_crossing _ _ _).compl).inter (measurableSet_crossing _ _ _).compl).inter
      (measurableSet_crossing _ _ _).compl
    have hsub : Cs ⊆ Kᶜ := fun η hη hK' => by
      obtain ⟨u, v, hu, hv, h⟩ := hη
      exact notMem_localConn_of_notMem_crossing hK'.1.1.1 hK'.1.1.2 hK'.1.2 hK'.2 hu hv univ h
    calc law q Cs ≤ law q Kᶜ := measure_mono hsub
      _ = 1 - law q K := prob_compl_eq_one_sub hKm
      _ ≤ 1 - β := tsub_le_tsub_left hK 1
  -- the half-box and its extreme points
  set lo : LatticeSite 2 := ![-(3 * (s : ℤ)), 0] with hlo
  set hi : LatticeSite 2 := ![3 * (s : ℤ), 3 * s] with hhi
  have hlo0 : lo 0 = -(3 * (s : ℤ)) := rfl
  have hlo1 : lo 1 = 0 := rfl
  have hhi0 : hi 0 = 3 * (s : ℤ) := rfl
  have hhi1 : hi 1 = 3 * (s : ℤ) := rfl
  set FL : ℤ → Set (Config (LatticeSite 2)) := fun k => {η : Config (LatticeSite 2) |
      (∃ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) ![k, 0] v) ∧
      ∀ a : LatticeSite 2, a 1 = lo 1 → a 0 + 2 ≤ (![k, 0] : LatticeSite 2) 0 →
        η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) ![k, 0] a} with hFL
  set FR : ℤ → Set (Config (LatticeSite 2)) := fun k => {η : Config (LatticeSite 2) |
      (∃ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) ![k, 0] v) ∧
      ∀ a : LatticeSite 2, a 1 = lo 1 → (![k, 0] : LatticeSite 2) 0 + 2 ≤ a 0 →
        η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) ![k, 0] a} with hFR
  have hFLm : ∀ k, MeasurableSet (FL k) := fun k =>
    measurableSet_setOf_exists_localConn_and_forall _ _ _ _ _
  have hFRm : ∀ k, MeasurableSet (FR k) := fun k =>
    measurableSet_setOf_exists_localConn_and_forall _ _ _ _ _
  -- the end of a path to the curved boundary is at sup-norm `3s`
  have hfar : ∀ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) →
      3 * (s : ℤ) ≤ |v 0| ∨ 3 * (s : ℤ) ≤ |v 1| := fun v hv h => by
    rw [mem_Icc_two_iff, hlo0, hlo1, hhi0, hhi1] at hv
    rw [hlo0, hhi0, hhi1] at h
    rw [le_abs, le_abs]
    omega
  -- counting the extreme points of one parity
  have hcount : ∀ (F : ℤ → Set (Config (LatticeSite 2))), (∀ k, MeasurableSet (F k)) →
      (∀ k η, η ∈ F k → ∃ v ∈ Icc lo hi, (v 0 = lo 0 ∨ v 0 = hi 0 ∨ v 1 = hi 1) ∧
        η ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) ![k, 0] v) →
      (∀ k l η, k + 2 ≤ l → η ∈ F k → η ∈ F l →
        η ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) ![k, 0] ![l, 0]) →
      ∀ r : ℤ, ∑ k ∈ (Finset.Icc (-(s : ℤ)) s).filter (fun k => k % 2 = r), law q (F k) ≤
        β⁻¹ := by
    intro F hFm hFv hFd r
    refine (sum_law_le_sum_pow_of_forall_mem_foldl q hCup _ F hFm fun η T hT hTF => ?_).trans
      (sum_range_pow_succ_le_inv hβ1 hlam _)
    refine mem_foldl_of_pairwise_notMem_localConn (H := Icc lo hi) T (fun k => ![k, 0])
      (fun k hk => ?_)
      (fun k hk => ?_) fun k hk l hl hkl => ?_
    · have := (Finset.mem_Icc.1 (Finset.mem_filter.1 (hT hk)).1)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, Nat.cast_nonneg,
        and_true]
      rw [abs_le]
      omega
    · obtain ⟨v, hv, hv', h⟩ := hFv k η (hTF k hk)
      exact ⟨v, hfar v hv hv', h⟩
    · have hk' := (Finset.mem_filter.1 (hT hk)).2
      have hl' := (Finset.mem_filter.1 (hT hl)).2
      rcases (show k + 2 ≤ l ∨ l + 2 ≤ k by omega) with h | h
      · exact hFd k l η h (hTF k hk) (hTF l hl)
      · rw [localConn_comm]
        exact hFd l k η h (hTF l hl) (hTF k hk)
  have hsumL : ∑ k ∈ Finset.Icc (-(s : ℤ)) s, law q (FL k) ≤ 2 * β⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => k % 2 = 0), two_mul]
    have hno : ∀ k : ℤ, ¬k % 2 = 0 ↔ k % 2 = 1 := fun k => by omega
    simp only [hno]
    refine add_le_add (hcount FL hFLm (fun k η h => h.1) ?_ 0)
      (hcount FL hFLm (fun k η h => h.1) ?_ 1)
    all_goals
      intro k l η hkl _ hl
      rw [localConn_comm]
      exact hl.2 _ rfl (by simpa using hkl)
  have hsumR : ∑ k ∈ Finset.Icc (-(s : ℤ)) s, law q (FR k) ≤ 2 * β⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => k % 2 = 0), two_mul]
    have hno : ∀ k : ℤ, ¬k % 2 = 0 ↔ k % 2 = 1 := fun k => by omega
    simp only [hno]
    refine add_le_add (hcount FR hFRm (fun k η h => h.1) ?_ 0)
      (hcount FR hFRm (fun k η h => h.1) ?_ 1)
    all_goals
      intro k l η hkl hk _
      exact hk.2 _ rfl (by simpa using hkl)
  -- each two-arm point is, after closing at most two edges, an extreme point
  have hs4 : 4 * s + 1 ≤ R := by omega
  have hpt : ∀ k ∈ Finset.Icc (-(s : ℤ)) s,
      law q (halfArmEvent ![true, false] ![k, 0] 0 R) ≤ 6 * law q (FL k) + 6 * law q (FR k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hsubk : Icc lo hi ⊆ Icc ((![k, 0] : LatticeSite 2) - R + 1) (![k, 0] + R - 1) := by
      intro v hv
      rw [mem_Icc_two_iff, hlo0, hlo1, hhi0, hhi1] at hv
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, Pi.natCast_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    have hkey : ∀ ω ∈ halfArmEvent ![true, false] ![k, 0] 0 R,
        ((ω \ {s(![k - 1, 0], ![k, 0])} ∈ FL k ∨
          (ω \ {s(![k - 1, 0], ![k, 0])}) \ {s(![k, 0], ![k, 1])} ∈ FL k) ∨
        (ω \ {s(![k, 0], ![k + 1, 0])} ∈ FR k ∨
          (ω \ {s(![k, 0], ![k + 1, 0])}) \ {s(![k, 0], ![k, 1])} ∈ FR k)) := fun ω hω =>
      mem_or_mem_of_mem_halfArmEvent_two (lo := lo) (hi := hi) (x := ![k, 0])
        (xl := ![k - 1, 0]) (xr := ![k + 1, 0]) (xu := ![k, 1]) (by simp) (by simp) (by simp)
        (by simp [hlo1]) (by simp [hlo0]; omega) (by simp [hhi0]; omega)
        (by rw [hlo1, hhi1]; omega) hsubk hω
    have hedge : ∀ u v : LatticeSite 2, (zdGraph 2).Adj u v → (q s(u, v) : ℝ) = 1 / 2 :=
      fun u v h => hq _ h
    have he₁ := hedge ![k - 1, 0] ![k, 0] (by rw [zdGraph_two_adj_iff]; simp)
    have he₂ := hedge ![k, 0] ![k, 1] (by rw [zdGraph_two_adj_iff]; simp)
    have he₃ := hedge ![k, 0] ![k + 1, 0] (by rw [zdGraph_two_adj_iff]; simp)
    calc law q (halfArmEvent ![true, false] ![k, 0] 0 R)
        ≤ law q (({ω | ω \ {s(![k - 1, 0], ![k, 0])} ∈ FL k} ∪
            {ω | ω \ {s(![k - 1, 0], ![k, 0])} ∈ {η | η \ {s(![k, 0], ![k, 1])} ∈ FL k}}) ∪
          ({ω | ω \ {s(![k, 0], ![k + 1, 0])} ∈ FR k} ∪
            {ω | ω \ {s(![k, 0], ![k + 1, 0])} ∈ {η | η \ {s(![k, 0], ![k, 1])} ∈ FR k}})) :=
          measure_mono fun ω hω => hkey ω hω
      _ ≤ (2 * law q (FL k) + 2 * (2 * law q (FL k))) +
          (2 * law q (FR k) + 2 * (2 * law q (FR k))) := by
          refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add ?_ ?_)) ((measure_union_le _ _).trans (add_le_add ?_ ?_)))
          · exact law_setOf_diff_singleton_mem_le he₁ _
          · exact (law_setOf_diff_singleton_mem_le he₁ _).trans
              (mul_le_mul_right (law_setOf_diff_singleton_mem_le he₂ _) _)
          · exact law_setOf_diff_singleton_mem_le he₃ _
          · exact (law_setOf_diff_singleton_mem_le he₃ _).trans
              (mul_le_mul_right (law_setOf_diff_singleton_mem_le he₂ _) _)
      _ = 6 * law q (FL k) + 6 * law q (FR k) := by ring
  -- translation invariance
  have htr : ∀ k : ℤ, law q (halfArmEvent ![true, false] ![k, 0] 0 R) =
      law q (halfArmEvent ![true, false] 0 0 R) := fun k =>
    law_halfArmEvent_eq_law_halfArmEvent_zero hq _ _ _ _
  have hsum : (2 * s + 1 : ℝ≥0∞) * law q (halfArmEvent ![true, false] 0 0 R) ≤ 24 * β⁻¹ := by
    calc (2 * s + 1 : ℝ≥0∞) * law q (halfArmEvent ![true, false] 0 0 R)
        = ∑ k ∈ Finset.Icc (-(s : ℤ)) s, law q (halfArmEvent ![true, false] ![k, 0] 0 R) := by
          simp only [htr, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
          congr 1
          rw [show ((s : ℤ) + 1 - -(s : ℤ)).toNat = 2 * s + 1 by omega]
          push_cast
          ring
      _ ≤ ∑ k ∈ Finset.Icc (-(s : ℤ)) s, (6 * law q (FL k) + 6 * law q (FR k)) :=
          Finset.sum_le_sum hpt
      _ = 6 * ∑ k ∈ Finset.Icc (-(s : ℤ)) s, law q (FL k) +
            6 * ∑ k ∈ Finset.Icc (-(s : ℤ)) s, law q (FR k) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 6 * (2 * β⁻¹) + 6 * (2 * β⁻¹) := add_le_add (mul_le_mul_right hsumL _)
          (mul_le_mul_right hsumR _)
      _ = 24 * β⁻¹ := by ring
  have hR : (R : ℝ≥0∞) ≤ 4 * (2 * s + 1) := by exact_mod_cast (show R ≤ 4 * (2 * s + 1) by omega)
  calc (R : ℝ≥0∞) * law q (halfArmEvent ![true, false] 0 0 R)
      ≤ 4 * (2 * s + 1) * law q (halfArmEvent ![true, false] 0 0 R) := mul_le_mul' hR le_rfl
    _ = 4 * ((2 * s + 1) * law q (halfArmEvent ![true, false] 0 0 R)) := by ring
    _ ≤ 4 * (24 * β⁻¹) := mul_le_mul_right hsum _
    _ = 96 * β⁻¹ := by ring
    _ ≤ 96 * β⁻¹ + 4 := le_self_add


/-! ### The landing order of two arms -/

/-- **A crossing inside a walk.** A walk from `S` to a point outside `T` contains a walk crossing
from `S` out of `T`. -/
theorem _root_.SimpleGraph.Walk.exists_isCrossing_of_start_mem {V : Type*} {G : SimpleGraph V}
    {S T : Set V} {u v : V} (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ T) :
    ∃ (c d : V) (q : G.Walk c d), q.IsCrossing S T ∧ (∀ w ∈ q.support, w ∈ p.support) ∧
      ∀ e ∈ q.edges, e ∈ p.edges := by
  obtain ⟨c, hc, q₁, s₁, hqs, hs⟩ :=
    SimpleGraph.Walk.exists_append_eq_of_exists_mem p ⟨u, p.start_mem_support, hu⟩
  obtain ⟨d, q, s, hqs', hd, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem s₁ hv
  refine ⟨c, d, q, ⟨hc, fun w hw => hs w ?_, hd, hq⟩, fun w hw => ?_, fun e he => ?_⟩
  · rw [← hqs', SimpleGraph.Walk.tail_support_append]
    exact List.mem_append_left _ hw
  · rw [← hqs, SimpleGraph.Walk.mem_support_append_iff, ← hqs',
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (Or.inl hw)
  · rw [← hqs, SimpleGraph.Walk.edges_append, ← hqs', SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ (List.mem_append_left _ he)

/-- **Interlacing at a bottom point.** In a box, let `x` be a point of the bottom side, joined
inside the box to a boundary point `w`, and let a dual path, crossing only edges of the box, join
the face below the edge on the left of `x` to a face outside the box with a boundary corner `y`
after `x`. Then `w` comes after the left neighbour of `x` and not after `y`. -/
theorem le_perimeterPos_of_dualConfig_left {lo hi : LatticeSite 2} {ω : Config (LatticeSite 2)}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {x w f g y : LatticeSite 2} (hx1 : x 1 = lo 1) (hx0 : lo 0 < x 0) (hxh : x 0 ≤ hi 0)
    (hw : w ∈ boxBoundary lo hi) (hf0 : f 0 + 1 = x 0) (hf1 : f 1 + 1 = x 1)
    (hg : g ∉ Icc lo (hi - 1)) (hy : y ∈ boxBoundary lo hi) (hyg : y ∈ Icc g (g + 1))
    (hxy : perimeterPos lo hi x < perimeterPos lo hi y)
    (hxw : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) x w)
    (hδ : dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc lo hi} ∈
      localConn (Icc (lo - 1) hi) f g) :
    perimeterPos lo hi x - 1 ≤ perimeterPos lo hi w ∧
      perimeterPos lo hi w ≤ perimeterPos lo hi y := by
  obtain ⟨x', hx'0, hx'1⟩ : ∃ p : LatticeSite 2, p 0 = x 0 - 1 ∧ p 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  have hxB : x ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hx'B : x' ∈ boxBoundary lo hi := by rw [mem_boxBoundary_two_iff]; omega
  have hfo : f ∉ Icc lo (hi - 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  have hx'f : x' ∈ Icc f (f + 1) := by
    rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
  have hpx : perimeterPos lo hi x = x 0 - lo 0 := perimeterPos_of_bottom hx1
  have hpx' : perimeterPos lo hi x' = x 0 - 1 - lo 0 := by
    rw [perimeterPos_of_bottom (hx'1.trans hx1), hx'0]
  constructor
  · by_contra hc
    exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxw hxB hw hfo hx'B hx'f hg hy hyg
      (Or.inr ⟨by omega, by omega, Or.inr hxy⟩) hδ
  · by_contra hc
    rw [localConn_comm] at hδ
    exact dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxw hxB hw hg hy hyg hfo hx'B hx'f
      (Or.inl ⟨hxy, by omega, Or.inl (by omega)⟩) hδ

/-- Positions on the upper half of the boundary of `B_R(x)` and on the boundary of its upper
half-box differ by `R`, except at the lower-left corner of the half-box. -/
theorem perimeterPos_eq_add_of_mem_boxBoundary {x p qlo qhi : LatticeSite 2} {R : ℕ}
    (hR : 1 ≤ R) (hql : qlo 0 = x 0 - R ∧ qlo 1 = x 1) (hqh : qhi 0 = x 0 + R ∧ qhi 1 = x 1 + R)
    (hp : p ∈ boxBoundary (x - (R : LatticeSite 2)) (x + R)) (hp1 : x 1 ≤ p 1)
    (hpne : ¬(p 0 = x 0 - R ∧ p 1 = x 1)) :
    perimeterPos (x - (R : LatticeSite 2)) (x + R) p = perimeterPos qlo qhi p + R := by
  rw [mem_boxBoundary_two_iff] at hp
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hp
  unfold perimeterPos
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
  split_ifs <;> omega

/-- **The landing position of a dual step out of `B_R(x)`**, above the line through `x`: twice
the position of the counterclockwise-first end of the boundary edge it crosses, plus one; that
end lies on the boundary of the upper half-box, after `x`. -/
theorem exists_perimeterPos_two_nsmul_eq {x h g qlo qhi : LatticeSite 2} {R : ℕ} (hR : 1 ≤ R)
    (hql : qlo 0 = x 0 - R ∧ qlo 1 = x 1) (hqh : qhi 0 = x 0 + R ∧ qhi 1 = x 1 + R)
    (hh : h ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hadj : (zdGraph 2).Adj h g) (hh1 : x 1 ≤ h 1) (hg1 : x 1 ≤ g 1) :
    ∃ u ∈ boxBoundary qlo qhi, u ∈ Icc g (g + 1) ∧ x 0 - qlo 0 < perimeterPos qlo qhi u ∧
      perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2))) (h + g + 1) =
        2 * perimeterPos qlo qhi u + 2 * R + 1 := by
  rw [mem_Icc_two_iff] at hh hg
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hh hg
  rw [zdGraph_two_adj_iff] at hadj
  have key : ∀ u : LatticeSite 2, u ∈ Icc g (g + 1) → u ∈ boxBoundary qlo qhi →
      x 0 - qlo 0 < perimeterPos qlo qhi u →
      perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2))) (h + g + 1) =
        2 * perimeterPos qlo qhi u + 2 * R + 1 →
      ∃ u ∈ boxBoundary qlo qhi, u ∈ Icc g (g + 1) ∧ x 0 - qlo 0 < perimeterPos qlo qhi u ∧
        perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2)))
          (h + g + 1) = 2 * perimeterPos qlo qhi u + 2 * R + 1 :=
    fun u h₁ h₂ h₃ h₄ => ⟨u, h₂, h₁, h₃, h₄⟩
  rcases hadj with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
  · -- `g` above `h`
    obtain ⟨u, hu0, hu1⟩ : ∃ u : LatticeSite 2, u 0 = h 0 + 1 ∧ u 1 = g 1 := ⟨![_, _], rfl, rfl⟩
    refine key u ?_ ?_ ?_ ?_
    · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    · rw [mem_boxBoundary_two_iff]; omega
    · unfold perimeterPos; split_ifs <;> omega
    · simp only [perimeterPos, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        Pi.one_apply, nsmul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega
  · omega
  · -- `g` right of `h`
    obtain ⟨u, hu0, hu1⟩ : ∃ u : LatticeSite 2, u 0 = g 0 ∧ u 1 = g 1 := ⟨![_, _], rfl, rfl⟩
    refine key u ?_ ?_ ?_ ?_
    · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    · rw [mem_boxBoundary_two_iff]; omega
    · unfold perimeterPos; split_ifs <;> omega
    · simp only [perimeterPos, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        Pi.one_apply, nsmul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega
  · -- `g` left of `h`
    obtain ⟨u, hu0, hu1⟩ : ∃ u : LatticeSite 2, u 0 = h 0 ∧ u 1 = g 1 + 1 := ⟨![_, _], rfl, rfl⟩
    refine key u ?_ ?_ ?_ ?_
    · rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega
    · rw [mem_boxBoundary_two_iff]; omega
    · unfold perimeterPos; split_ifs <;> omega
    · simp only [perimeterPos, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        Pi.one_apply, nsmul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega

/-- **The landing order.** Let the edge on the left of `x` be closed, and let `α` be an open arm
of `B_R(x)` from `x` and `δ` a dual walk from the face above that edge, both above the line
through `x`, with `δ` leaving the faces of `B_R(x)` at its last step only. Then the open arm lands
before the dual step, counterclockwise from the right end of the line. -/
theorem landingPos_lt_of_dualWalk {ω : Config (LatticeSite 2)} {x xl fL : LatticeSite 2} {R : ℕ}
    (hR : 1 ≤ R) (hxl : xl 0 + 1 = x 0 ∧ xl 1 = x 1) (hfL : fL 0 + 1 = x 0 ∧ fL 1 = x 1)
    {p : LatticeSite 2} {α : (zdGraph 2).Walk x p} (hα : IsOpenArm ω x 0 (x - R) (x + R) α)
    (hαH : ∀ v ∈ α.support, x 1 ≤ v 1) (he₁ : s(xl, x) ∉ ω)
    {g : LatticeSite 2} (δ : (zdGraph 2).Walk fL g) (hδn : ¬δ.Nil)
    (hδ : ∀ f ∈ δ.support.dropLast, f ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδ1 : ∀ f ∈ δ.support, x 1 ≤ f 1) (hg : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1))
    (hδE : ∀ E ∈ δ.edges, E ∈ dualConfig ω) :
    landingPos (x - R) (x + R) true α <
      perimeterPos (2 • (x - (R : LatticeSite 2))) (2 • (x + (R : LatticeSite 2)))
        (δ.penultimate + g + 1) := by
  obtain ⟨qlo, hql0, hql1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 - R ∧ v 1 = x 1 := ⟨![_, _], rfl, rfl⟩
  obtain ⟨qhi, hqh0, hqh1⟩ : ∃ v : LatticeSite 2, v 0 = x 0 + R ∧ v 1 = x 1 + R :=
    ⟨![_, _], rfl, rfl⟩
  obtain ⟨f₀, hf₀0, hf₀1⟩ : ∃ v : LatticeSite 2, v 0 + 1 = x 0 ∧ v 1 + 1 = x 1 :=
    ⟨![x 0 - 1, x 1 - 1], by simp, by simp⟩
  have hB : Icc (x - ((0 : ℕ) : LatticeSite 2)) (x + ((0 : ℕ) : LatticeSite 2)) ⊆
      Icc (x - R + 1) (x + R - 1) := by
    intro v hv
    simp only [Nat.cast_zero, sub_zero, add_zero, Icc_self, mem_singleton_iff] at hv
    subst hv
    rw [mem_Icc_two_iff]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hαn := hα.not_nil hB
  have hpB := hα.end_mem_boxBoundary hαn
  have hp1 := hαH p α.end_mem_support
  -- the open walk in the upper half-box
  have hαQ : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc qlo qhi) x p :=
    mem_localConn_of_walk α (fun v hv => by
      have h₁ := hα.mem_Icc hαn hv
      have h₂ := hαH v hv
      rw [mem_Icc_two_iff] at h₁ ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at h₁
      omega) hα.mem_of_mem_edges
  have hpQ : p ∈ boxBoundary qlo qhi := by
    rw [mem_boxBoundary_two_iff] at hpB ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hpB
    omega
  -- the last dual step
  have hpen : δ.penultimate ∈ δ.support.dropLast := by
    rw [← SimpleGraph.Walk.support_dropLast hδn]; exact SimpleGraph.Walk.end_mem_support _
  have hadj := δ.adj_penultimate hδn
  have hpenB := hδ _ hpen
  have hpen1 := hδ1 _ (List.mem_of_mem_dropLast hpen)
  have hg1 := hδ1 g δ.end_mem_support
  obtain ⟨u, huQ, hug, hxu, hland⟩ := exists_perimeterPos_two_nsmul_eq hR ⟨hql0, hql1⟩
    ⟨hqh0, hqh1⟩ hpenB hg hadj hpen1 hg1
  -- the dual path in the upper half-box, from the face below the closed edge
  have hxQ : x ∈ Icc qlo qhi := by rw [mem_Icc_two_iff]; omega
  have hxlQ : xl ∈ Icc qlo qhi := by rw [mem_Icc_two_iff]; omega
  have hd₁ : f₀ ∈ dualEdge s(xl, x) ∧ fL ∈ dualEdge s(xl, x) := by
    constructor <;>
    · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]; omega
  have hgQ : g ∉ Icc qlo (qhi - 1) := fun h => hg (by
    rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    omega)
  have hδQ := dualConfig_inter_image_mem_localConn_of_walk (lo := qlo) (hi := qhi) δ
    (fun f hf => by
      rw [← SimpleGraph.Walk.dropLast_support_concat δ, List.mem_append,
        List.mem_singleton] at hf
      rcases hf with hf | rfl
      · have h₁ := hδ f hf
        have h₂ := hδ1 f (List.mem_of_mem_dropLast hf)
        rw [mem_Icc_two_iff] at h₁ ⊢
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ ⊢
        omega
      · rw [mem_Icc_two_iff] at hpenB ⊢
        rw [zdGraph_two_adj_iff] at hadj
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hpenB ⊢
        omega)
    (fun E hE => ⟨hδE E hE, by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hE
      refine ⟨d.fst, Sym2.mem_mk_left _ _, ?_⟩
      have hd' : d.fst ∈ δ.support.dropLast := by
        rw [← SimpleGraph.Walk.map_fst_darts]; exact List.mem_map_of_mem hd
      have h₁ := hδ _ hd'
      have h₂ := hδ1 _ (List.mem_of_mem_dropLast hd')
      rw [mem_Icc_two_iff] at h₁ ⊢
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at h₁ ⊢
      omega⟩)
  have hfδ := localConn_trans (mem_localConn_of_adj_of_notMem (lo := qlo) (hi := qhi)
    (by rw [zdGraph_two_adj_iff]; omega) hxlQ hxQ he₁ hd₁.1 hd₁.2) hδQ
  obtain ⟨hlow, hup⟩ := le_perimeterPos_of_dualConfig_left (by omega) (by omega)
    hql1.symm (by omega) (by omega) hpQ hf₀0 hf₀1 hgQ huQ hug
    (by rw [perimeterPos_of_bottom hql1.symm]; omega) hαQ hfδ
  have hposx : perimeterPos qlo qhi x = x 0 - qlo 0 := perimeterPos_of_bottom hql1.symm
  -- the open arm does not land at the lower-left corner of the half-box
  have hpne : ¬(p 0 = x 0 - R ∧ p 1 = x 1) := by
    rintro ⟨hp0, hp1'⟩
    have hp0' : perimeterPos qlo qhi p = 0 := by
      rw [perimeterPos_of_bottom (by omega)]; omega
    have hR1 : R = 1 := by omega
    subst hR1
    have hpen' := hα.isCrossing.mem_of_mem_dropLast α.penultimate (by
      rw [← SimpleGraph.Walk.support_dropLast hαn]; exact SimpleGraph.Walk.end_mem_support _)
    have hlast : s(α.penultimate, p) ∈ α.edges := α.mk_penultimate_end_mem_edges hαn
    rw [mem_Icc_two_iff] at hpen'
    simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply, Nat.cast_one] at hpen'
    have hpenx : α.penultimate = x := funext (Fin.forall_fin_two.2 ⟨by omega, by omega⟩)
    have hpxl : p = xl := funext (Fin.forall_fin_two.2 ⟨by omega, by omega⟩)
    have he : s(α.penultimate, p) = s(xl, x) :=
      (congrArg₂ (fun a b => s(a, b)) hpenx hpxl).trans Sym2.eq_swap
    exact he₁ (hα.mem_of_mem_edges _ (he ▸ hlast))
  rw [landingPos_true, perimeterPos_eq_add_of_mem_boxBoundary hR
    ⟨hql0, hql1⟩ ⟨hqh0, hqh1⟩ hpB hp1 hpne, hland]
  omega


/-! ### A dual arm from the edge on the left of an extreme point -/

/-- **A dual path from the left of a bottom point.** In a box, let no open path inside the box
join a point of the bottom side left of `x` to a point of the bottom side at or right of `x`.
Then a dual-open walk joins the face above the edge on the left of `x` to a face outside the box,
through faces at or above the bottom row. This is quad duality for the configuration with every
other edge of the bottom side opened. -/
theorem exists_dualWalk_of_forall_notMem_localConn {ω : Config (LatticeSite 2)}
    {lo hi x fL : LatticeSite 2} (h₁ : lo 1 < hi 1) (hx1 : x 1 = lo 1) (hlx : lo 0 < x 0)
    (hxh : x 0 < hi 0) (hfL : fL 0 + 1 = x 0 ∧ fL 1 = x 1)
    (hsep : ∀ a b : LatticeSite 2, a 1 = lo 1 → b 1 = lo 1 → a 0 < x 0 → x 0 ≤ b 0 →
      ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) a b) :
    ∃ g, ∃ δ : (zdGraph 2).Walk fL g, g ∉ Icc lo (hi - 1) ∧ (∀ f ∈ δ.support, lo 1 ≤ f 1) ∧
      ∀ E ∈ δ.edges, E ∈ dualConfig ω := by
  classical
  have h₀ : lo 0 < hi 0 := by omega
  have hne : lo ≠ hi := fun h => by rw [h] at h₀; exact lt_irrefl _ h₀
  set B : Set (Sym2 (LatticeSite 2)) := {e | ∃ j : ℤ, lo 0 ≤ j ∧ j < hi 0 ∧ j ≠ x 0 - 1 ∧
    e = s(![j, lo 1], ![j + 1, lo 1])} with hB
  have hP0 : 0 < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) := by omega
  have hpos : ∀ v ∈ boxBoundary lo hi, 0 ≤ perimeterPos lo hi v ∧
      perimeterPos lo hi v < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) :=
    fun v hv => ⟨perimeterPos_nonneg hv.1, perimeterPos_lt hne hv.1⟩
  have hbot : ∀ v ∈ boxBoundary lo hi, perimeterPos lo hi v ≤ hi 0 - lo 0 → v 1 = lo 1 := by
    intro v hv h
    rw [mem_boxBoundary_two_iff] at hv
    unfold perimeterPos at h
    split_ifs at h <;> omega
  -- no open path joins the two parts of the bottom side once the other bottom edges are open
  have hω : ¬∃ u v, u ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi u + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈
        Ico 0 (x 0 - lo 0)) ∧ v ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi v + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈
        Ico (x 0 - lo 0 + 1) (hi 0 - lo 0 + 1)) ∧
      (ω ∪ B) ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v := by
    rintro ⟨u, v, hu, hk, hv, hk', huv⟩
    have hu' := (Int.exists_add_mul_mem_Ico_iff hP0 (hpos u hu).1 (hpos u hu).2 le_rfl
      (by omega)).1 hk
    have hv' := (Int.exists_add_mul_mem_Ico_iff hP0 (hpos v hv).1 (hpos v hv).2 (by omega)
      (by omega)).1 hk'
    simp only [mem_Ico] at hu' hv'
    have hu1 : u 1 = lo 1 := hbot u hu (by omega)
    have hv1 : v 1 = lo 1 := hbot v hv (by omega)
    rw [perimeterPos_of_bottom hu1] at hu'
    rw [perimeterPos_of_bottom hv1] at hv'
    have huB := hu.1
    have hvB := hv.1
    rw [mem_Icc_two_iff] at huB hvB
    obtain ⟨p, hp, hpe⟩ := exists_walk_of_mem_localConn huv
    obtain ⟨b, hbR, q, hqs, hqe, hqb⟩ := SimpleGraph.Walk.exists_walk_first_mem
      (fun w : LatticeSite 2 => w 1 = lo 1 ∧ x 0 ≤ w 0) p
      ⟨v, p.end_mem_support, hv1, by omega⟩
    obtain ⟨a, haL, q₁, r, hqr, hr⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
      (S := {w : LatticeSite 2 | w 1 = lo 1 ∧ w 0 < x 0}) q
      ⟨u, q.start_mem_support, hu1, by omega⟩
    have hrq : ∀ w ∈ r.support, w ∈ q.support := fun w hw => by
      rw [← hqr, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inr hw
    refine hsep a b haL.1 hbR.1 haL.2 hbR.2
      (mem_localConn_of_walk r (fun w hw => hp w (hqs w (hrq w hw))) fun e he => ?_)
    have heq : e ∈ q.edges := by
      rw [← hqr, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ he
    rcases hpe e (hqe e heq) with h | ⟨j, hj0, hjh, hjx, rfl⟩
    · exact h
    · exfalso
      have key : ∀ w ∈ r.support, w 1 = lo 1 → w = a ∨ w = b := by
        intro w hw hw1
        by_cases hwx : w 0 < x 0
        · left
          rcases (SimpleGraph.Walk.mem_support_iff r).1 hw with hw | hw
          · exact hw
          · exact absurd ⟨hw1, hwx⟩ (hr w hw)
        · exact Or.inr (hqb w (hrq w hw) ⟨hw1, by omega⟩)
      have hA := key _ (mem_support_of_mem_edge r he (Sym2.mem_mk_left _ _)) (by simp)
      have hB' := key _ (mem_support_of_mem_edge r he (Sym2.mem_mk_right _ _)) (by simp)
      have ha0 := haL.2
      have hb0 := hbR.2
      rcases hA with hA | hA <;> rcases hB' with hB' | hB'
      · have := congrFun (hA.trans hB'.symm) 0
        simp at this
      · have h₁' := congrFun hA 0
        have h₂' := congrFun hB' 0
        simp only [Matrix.cons_val_zero] at h₁' h₂'
        omega
      · have h₁' := congrFun hA 0
        have h₂' := congrFun hB' 0
        simp only [Matrix.cons_val_zero] at h₁' h₂'
        omega
      · have := congrFun (hA.trans hB'.symm) 0
        simp at this
  obtain ⟨f, g, ⟨hf, x', hx'B, hx'f, hx'k⟩, ⟨hg, y', hy'B, hy'g, hy'k⟩, hfg⟩ :=
    exists_dualConfig_inter_mem_localConn_of_not_exists h₀ h₁ (a := 0) (c := x 0 - lo 0)
      (b := x 0 - lo 0 + 1) (d := hi 0 - lo 0 + 1) ⟨by omega, by omega, by omega, by omega⟩ hω
  -- the face `f` lies below `x`, and `g` above the bottom row
  have hx'' := (Int.exists_add_mul_mem_Ico_iff hP0 (hpos x' hx'B).1 (hpos x' hx'B).2 (by omega)
    (by omega)).1 hx'k
  have hy'' := (Int.exists_add_mul_mem_Ico_iff hP0 (hpos y' hy'B).1 (hpos y' hy'B).2 (by omega)
    (by omega)).1 hy'k
  simp only [mem_Ico] at hx'' hy''
  have hx'p := hpos x' hx'B
  have hy'p := hpos y' hy'B
  have hx'1 : x' 1 = lo 1 := hbot x' hx'B (by omega)
  rw [perimeterPos_of_bottom hx'1] at hx'' hx'p
  have hx'0 : x' 0 = x 0 := by omega
  have hy'1 : lo 1 < y' 1 := by
    by_contra hc
    have hy1 : y' 1 = lo 1 := by
      have := hy'B.1; rw [mem_Icc_two_iff] at this; omega
    rw [perimeterPos_of_bottom hy1] at hy''
    have := hy'B.1; rw [mem_Icc_two_iff] at this; omega
  rw [mem_Icc_two_iff] at hx'f hy'g
  simp only [Pi.add_apply, Pi.one_apply] at hx'f hy'g
  have hf1 : f 1 = lo 1 - 1 := by
    by_contra hc
    refine hf ?_
    rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply]; omega
  -- a dual walk from `f` to `g`
  have hdL : dualConfig (ω ∪ B) ∩
      dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ⊆ (zdGraph 2).edgeSet :=
    fun E hE => by
      obtain ⟨e, he, -, rfl⟩ := (mem_dualConfig_iff' _ E).1 hE.1
      exact dualEdge_mem_edgeSet he
  rw [← inter_eq_left.2 hdL] at hfg
  obtain ⟨δ₀, hδ₀s, hδ₀e⟩ := exists_walk_of_mem_localConn hfg
  -- its last face below the bottom row, and the step up from there
  obtain ⟨h, hh, q, s, hqs, hs⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
    (S := {f : LatticeSite 2 | f 1 = lo 1 - 1}) δ₀ ⟨f, δ₀.start_mem_support, hf1⟩
  have hsδ : ∀ w ∈ s.support, w ∈ δ₀.support := fun w hw => by
    rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inr hw
  have hseδ : ∀ e ∈ s.edges, e ∈ δ₀.edges := fun e he => by
    rw [← hqs, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ he
  have hsn : ¬s.Nil := fun hn => by
    have := hn.eq
    rw [mem_ofPred_eq, this] at hh
    omega
  have hsnd := s.adj_snd hsn
  have hsndt : s.snd ∈ s.support.tail := s.snd_mem_tail_support hsn
  have hsnd1 : s.snd 1 ≠ lo 1 - 1 := hs _ hsndt
  have hsndB := hδ₀s _ (hsδ _ (List.mem_of_mem_tail hsndt))
  have hhB := hδ₀s _ (hsδ _ s.start_mem_support)
  rw [mem_ofPred_eq] at hh
  rw [mem_Icc_two_iff] at hsndB hhB
  simp only [Pi.sub_apply, Pi.one_apply] at hsndB hhB
  rw [zdGraph_two_adj_iff] at hsnd
  have hsnd1' : s.snd 1 = lo 1 := by omega
  have hsnd0 : s.snd 0 = h 0 := by omega
  -- the edge crossed by that step
  have hE := hδ₀e _ (hseδ _ (s.mk_start_snd_mem_edges hsn))
  obtain ⟨e, he, heω, hee⟩ := (mem_dualConfig_iff' _ _).1 hE.1
  obtain ⟨e₂, ⟨he₂, he₂H⟩, he₂e⟩ := hE.2
  have hcorner : ∀ e' : Sym2 (LatticeSite 2), e' ∈ (zdGraph 2).edgeSet →
      dualEdge e' = s(h, s.snd) → ∀ v ∈ e', v 1 = lo 1 ∧ (v 0 = h 0 ∨ v 0 = h 0 + 1) := by
    intro e' he' hee' v hv
    have h₁' := mem_Icc_of_mem_dualEdge he' hv (hee' ▸ Sym2.mem_mk_left _ _)
    have h₂' := mem_Icc_of_mem_dualEdge he' hv (hee' ▸ Sym2.mem_mk_right _ _)
    rw [mem_Icc_two_iff] at h₁' h₂'
    simp only [Pi.add_apply, Pi.one_apply] at h₁' h₂'
    omega
  -- the crossed edge is the bottom edge `{(h₀, lo₁), (h₀ + 1, lo₁)}`, inside the box
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  have hbox : lo 0 ≤ h 0 ∧ h 0 < hi 0 := by
    induction e₂ using Sym2.ind with
    | h p₁ p₂ =>
      have hadj : (zdGraph 2).Adj p₁ p₂ := he₂
      have c₁ := hcorner _ he₂ he₂e p₁ (Sym2.mem_mk_left _ _)
      have c₂ := hcorner _ he₂ he₂e p₂ (Sym2.mem_mk_right _ _)
      have b₁ := he₂H p₁ (Sym2.mem_mk_left _ _)
      have b₂ := he₂H p₂ (Sym2.mem_mk_right _ _)
      rw [mem_Icc_two_iff] at b₁ b₂
      rw [zdGraph_two_adj_iff] at hadj
      omega
  have heq : e = s(![h 0, lo 1], ![h 0 + 1, lo 1]) := by
    induction e using Sym2.ind with
    | h p₁ p₂ =>
      have hadj : (zdGraph 2).Adj p₁ p₂ := he
      have c₁ := hcorner _ he hee p₁ (Sym2.mem_mk_left _ _)
      have c₂ := hcorner _ he hee p₂ (Sym2.mem_mk_right _ _)
      rw [zdGraph_two_adj_iff] at hadj
      rcases c₁.2 with h₁' | h₁'
      · have e₁ : p₁ = ![h 0, lo 1] := hpt _ _ (by simp [h₁']) (by simp [c₁.1])
        have e₂ : p₂ = ![h 0 + 1, lo 1] := hpt _ _ (by simp; omega) (by simp [c₂.1])
        rw [e₁, e₂]
      · have e₁ : p₁ = ![h 0 + 1, lo 1] := hpt _ _ (by simp [h₁']) (by simp [c₁.1])
        have e₂ : p₂ = ![h 0, lo 1] := hpt _ _ (by simp; omega) (by simp [c₂.1])
        rw [e₁, e₂, Sym2.eq_swap]
  have hh0 : h 0 = x 0 - 1 := by
    by_contra hc
    exact heω (Or.inr ⟨h 0, hbox.1, hbox.2, hc, heq⟩)
  have hsndfL : s.snd = fL := hpt _ _ (by omega) (by omega)
  -- the dual walk from the face above the closed edge
  refine ⟨g, s.tail.copy hsndfL rfl, hg, fun w hw => ?_, fun E hE => ?_⟩
  · rw [SimpleGraph.Walk.support_copy, s.support_tail_of_not_nil hsn] at hw
    have h₁' := hs w hw
    have h₂' := hδ₀s w (hsδ w (List.mem_of_mem_tail hw))
    rw [mem_ofPred_eq] at h₁'
    rw [mem_Icc_two_iff] at h₂'
    simp only [Pi.sub_apply, Pi.one_apply] at h₂'
    omega
  · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_tail] at hE
    exact dualConfig_anti subset_union_left
      (hδ₀e E (hseδ E (List.mem_of_mem_tail hE))).1


/-- A vertex of a walk inside `S` along open edges is joined to its start inside `S`. -/
theorem mem_localConn_of_mem_support {ω : Config (LatticeSite 2)} {S : Set (LatticeSite 2)}
    {a b z : LatticeSite 2} (p : (zdGraph 2).Walk a b) (hp : ∀ v ∈ p.support, v ∈ S)
    (hpe : ∀ e ∈ p.edges, e ∈ ω) (hz : z ∈ p.support) :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn S a z := by
  classical
  exact mem_localConn_of_walk (p.takeUntil z hz)
    (fun u hu => hp u (p.support_takeUntil_subset_support hz hu))
    (fun f hf => hpe f (p.edges_takeUntil_subset_edges hz hf))

/-- **Two half-plane arms from crossings of two strips** (the lower bound, deterministic part).
Let the strip `[R, 2R] × [0, 4R]` have an open bottom-top crossing and the strip of faces
`[-2R, -R] × [-1, 4R]` a dual bottom-top crossing. In the half-box `[-4R, 4R] × [0, 4R]`, the
leftmost point `x` of the bottom side joined to the open crossing has an open arm to distance
`R` (along the cluster) and a dual arm from the face on its upper left (along the left boundary of
the cluster), landing after the open arm; and `x` lies in `(-2R, 2R]`. -/
theorem exists_mem_halfArmEvent_two_of_mem_crossing {ω : Config (LatticeSite 2)} {R : ℕ}
    (hR : 1 ≤ R) (hO : ω ∈ crossing 1 ![(R : ℤ), 0] ![2 * (R : ℤ), 4 * R])
    (hD : dualConfig ω ∈ crossing 1 ![-(2 * (R : ℤ)), -1] ![-(R : ℤ), 4 * R]) :
    ∃ k : ℤ, k ∈ Finset.Ioc (-(2 * (R : ℤ))) (2 * R) ∧
      ω ∈ halfArmEvent ![true, false] ![k, 0] 0 R := by
  classical
  set lo : LatticeSite 2 := ![-(4 * (R : ℤ)), 0] with hlo
  set hi : LatticeSite 2 := ![4 * (R : ℤ), 4 * R] with hhi
  have hlo0 : lo 0 = -(4 * (R : ℤ)) := rfl
  have hlo1 : lo 1 = 0 := rfl
  have hhi0 : hi 0 = 4 * (R : ℤ) := rfl
  have hhi1 : hi 1 = 4 * (R : ℤ) := rfl
  have h₀ : lo 0 < hi 0 := by rw [hlo0, hhi0]; omega
  have h₁ : lo 1 < hi 1 := by rw [hlo1, hhi1]; omega
  have hpt : ∀ u v : LatticeSite 2, u 0 = v 0 → u 1 = v 1 → u = v :=
    fun u v h0 h1 => funext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  have hmemH : ∀ v : LatticeSite 2, v ∈ Icc lo hi ↔
      -(4 * (R : ℤ)) ≤ v 0 ∧ v 0 ≤ 4 * R ∧ 0 ≤ v 1 ∧ v 1 ≤ 4 * R := fun v => by
    rw [mem_Icc_two_iff, hlo0, hlo1, hhi0, hhi1]
  -- the open crossing, inside the half-box
  obtain ⟨u, huI, hu1, w, hwI, hw1, huw⟩ := (mem_crossing_iff 1 _ _ ω).1 hO
  rw [mem_Icc_two_iff] at huI hwI
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huI hwI hu1 hw1
  have hsubO : Icc (![(R : ℤ), 0] : LatticeSite 2) ![2 * (R : ℤ), 4 * R] ⊆ Icc lo hi := by
    intro v hv
    rw [mem_Icc_two_iff] at hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
    rw [hmemH]
    omega
  have huwH := localConn_mono_set hsubO _ _ huw
  have huH : u ∈ Icc lo hi := (hmemH u).2 (by omega)
  -- the leftmost point of the bottom side joined to `u`
  set K := (Finset.Icc (-(4 * (R : ℤ))) (4 * R)).filter
    (fun k => ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) ![k, 0] u) with hK
  have huK : u 0 ∈ K := by
    rw [hK, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    rw [show (![u 0, 0] : LatticeSite 2) = u from hpt _ _ (by simp) (by simp [hu1]),
      localConn_self huH]
    exact mem_univ _
  have hk₀K := K.min'_mem ⟨u 0, huK⟩
  have hk₀u : K.min' ⟨u 0, huK⟩ ≤ u 0 := K.min'_le _ huK
  have hKmin : ∀ k ∈ K, K.min' ⟨u 0, huK⟩ ≤ k := fun k hk => K.min'_le _ hk
  set k₀ := K.min' ⟨u 0, huK⟩ with hk₀
  rw [hK, Finset.mem_filter, Finset.mem_Icc] at hk₀K
  obtain ⟨⟨hk₀lo, hk₀hi⟩, hxu⟩ := hk₀K
  set x : LatticeSite 2 := ![k₀, 0] with hxdef
  have hx0 : x 0 = k₀ := rfl
  have hx1 : x 1 = 0 := rfl
  have hmin : ∀ a : LatticeSite 2, a 1 = 0 → a 0 < k₀ →
      ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) a u := by
    intro a ha1 ha0 hau
    have haH := (hmemH a).1 hau.1
    have haK : a 0 ∈ K := by
      rw [hK, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rwa [show (![a 0, 0] : LatticeSite 2) = a from hpt _ _ (by simp) (by simp [ha1])]
    have := hKmin _ haK
    omega
  -- the dual crossing keeps `x` to the right of `-2R`
  obtain ⟨fb, hfbI, hfb1, ft, hftI, hft1, hfbt⟩ := (mem_crossing_iff 1 _ _ _).1 hD
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfb1 hft1
  obtain ⟨δD, hδDs, hδDe⟩ := exists_walk_of_mem_localConn hfbt
  have hδDs' : ∀ f ∈ δD.support, -(2 * (R : ℤ)) ≤ f 0 ∧ f 0 ≤ -(R : ℤ) ∧ -1 ≤ f 1 ∧
      f 1 ≤ 4 * R := fun f hf => by
    have := hδDs f hf
    rw [mem_Icc_two_iff] at this
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using this
  obtain ⟨fb', hfb', q₀, s₀, hqs₀, hs₀⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
    (S := {f : LatticeSite 2 | f 1 = -1}) δD ⟨fb, δD.start_mem_support, hfb1⟩
  have hs₀δ : ∀ f ∈ s₀.support, f ∈ δD.support := fun f hf => by
    rw [← hqs₀, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inr hf
  have hs₀e : ∀ e ∈ s₀.edges, e ∈ δD.edges := fun e he => by
    rw [← hqs₀, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ he
  obtain ⟨ft', hft', s', hs's, hs'e, hs'b⟩ := SimpleGraph.Walk.exists_walk_first_mem
    (fun f : LatticeSite 2 => f 1 = 4 * (R : ℤ)) s₀ ⟨ft, s₀.end_mem_support, hft1⟩
  rw [mem_ofPred_eq] at hfb'
  have hrow : ∀ f ∈ s'.support, f 1 = -1 → f = fb' := fun f hf hf1 => by
    rcases (SimpleGraph.Walk.mem_support_iff s₀).1 (hs's f hf) with h | h
    · exact h
    · exact absurd hf1 (hs₀ f h)
  have hfb'' := hδDs' _ (hs₀δ _ s₀.start_mem_support)
  have hft'' := hδDs' _ (hs₀δ _ (hs's _ s'.end_mem_support))
  have hdualH : dualConfig ω ∩
      dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) fb' ft' := by
    refine dualConfig_inter_image_mem_localConn_of_walk s' (fun f hf => ?_) fun E hE => ?_
    · have := hδDs' f (hs₀δ f (hs's f hf))
      rw [mem_Icc_two_iff]
      simp only [Pi.sub_apply, Pi.one_apply, hlo0, hlo1, hhi0, hhi1]
      omega
    · refine ⟨hδDe E (hs₀e E (hs'e E hE)), ?_⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hE
      have hfst := s'.dart_fst_mem_support_of_mem_darts hd
      have hsnd := s'.dart_snd_mem_support_of_mem_darts hd
      have hadj := d.adj
      have c₁ := hδDs' _ (hs₀δ _ (hs's _ hfst))
      have c₂ := hδDs' _ (hs₀δ _ (hs's _ hsnd))
      have hne : d.fst ≠ d.snd := hadj.ne
      rw [zdGraph_two_adj_iff] at hadj
      by_cases hin : 0 ≤ d.fst 1 ∧ d.fst 1 < 4 * (R : ℤ)
      · refine ⟨d.fst, Sym2.mem_mk_left _ _, ?_⟩
        rw [mem_Icc_two_iff]
        simp only [Pi.sub_apply, Pi.one_apply, hlo0, hlo1, hhi0, hhi1]
        omega
      · refine ⟨d.snd, Sym2.mem_mk_right _ _, ?_⟩
        rw [mem_Icc_two_iff]
        simp only [Pi.sub_apply, Pi.one_apply, hlo0, hlo1, hhi0, hhi1]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · by_contra hc
          have e₁ := hrow _ hsnd (by omega)
          rcases (show d.fst 1 = -1 ∨ d.fst 1 = 4 * (R : ℤ) by omega) with h | h
          · exact hne ((hrow _ hfst h).trans e₁.symm)
          · omega
        · by_contra hc
          have e₂ := hs'b _ hsnd (by omega)
          rcases (show d.fst 1 = -1 ∨ d.fst 1 = 4 * (R : ℤ) by omega) with h | h
          · omega
          · exact hne ((hs'b _ hfst h).trans e₂.symm)
  have hk₀lo' : -(2 * (R : ℤ)) < k₀ := by
    by_contra hc
    obtain ⟨yb, hyb0, hyb1⟩ : ∃ y : LatticeSite 2, y 0 = fb' 0 + 1 ∧ y 1 = 0 :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨yt, hyt0, hyt1⟩ : ∃ y : LatticeSite 2, y 0 = ft' 0 ∧ y 1 = 4 * (R : ℤ) :=
      ⟨![_, _], rfl, rfl⟩
    have hxB : x ∈ boxBoundary lo hi := by
      rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
    have huB : u ∈ boxBoundary lo hi := by
      rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
    have hybB : yb ∈ boxBoundary lo hi := by
      rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
    have hytB : yt ∈ boxBoundary lo hi := by
      rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
    have hpyt := perimeterPos_lt_perimeterPos_of_bottom (show u 1 = lo 1 by rw [hlo1]; exact hu1)
      (by rw [hhi0]; omega) hytB (by rw [hlo1]; omega)
    refine dualConfig_inter_notMem_localConn_of_interlaced h₀ h₁ hxu hxB huB (f := fb')
      (by rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply, hlo1]; omega) hybB
      (by rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega) (g := ft')
      (by rw [mem_Icc_two_iff]; simp only [Pi.sub_apply, Pi.one_apply, hhi1]; omega) hytB
      (by rw [mem_Icc_two_iff]; simp only [Pi.add_apply, Pi.one_apply]; omega)
      (Or.inl ⟨?_, ?_, Or.inr hpyt⟩) hdualH
    · rw [perimeterPos_of_bottom (show x 1 = lo 1 by rw [hlo1, hx1]),
        perimeterPos_of_bottom (show yb 1 = lo 1 by rw [hlo1]; exact hyb1)]
      omega
    · rw [perimeterPos_of_bottom (show yb 1 = lo 1 by rw [hlo1]; exact hyb1),
        perimeterPos_of_bottom (show u 1 = lo 1 by rw [hlo1]; exact hu1)]
      omega
  have hk₀hi' : k₀ ≤ 2 * (R : ℤ) := by omega
  have hxH : x ∈ Icc lo hi := (hmemH x).2 (by rw [hx0, hx1]; omega)
  -- the closed edge on the left of `x`, and the face above it
  obtain ⟨xl, hxl0, hxl1⟩ : ∃ v : LatticeSite 2, v 0 + 1 = x 0 ∧ v 1 = x 1 :=
    ⟨![k₀ - 1, 0], by simp [hxdef], by simp [hxdef]⟩
  obtain ⟨fL, hfL0, hfL1⟩ : ∃ v : LatticeSite 2, v 0 + 1 = x 0 ∧ v 1 = x 1 :=
    ⟨![k₀ - 1, 0], by simp [hxdef], by simp [hxdef]⟩
  have he₁ : s(xl, x) ∉ ω := by
    intro h
    have hxlH : xl ∈ Icc lo hi := (hmemH xl).2 (by omega)
    have hl : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) xl x :=
      mem_localConn_of_mem_localConn_of_mem (by rw [localConn_self hxlH]; exact mem_univ _) hxH
        ⟨h, by rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]; omega⟩
    exact hmin xl (by omega) (by omega) (localConn_trans hl hxu)
  -- no open path joins the bottom side left of `x` to the bottom side at or right of `x`
  obtain ⟨pw, hpws, hpwe⟩ := exists_walk_of_mem_localConn (localConn_trans hxu huwH)
  have hwB : w ∈ boxBoundary lo hi := by
    rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
  have hxB : x ∈ boxBoundary lo hi := by
    rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; rw [hx0, hx1]; omega
  have hsep : ∀ a b : LatticeSite 2, a 1 = lo 1 → b 1 = lo 1 → a 0 < x 0 → x 0 ≤ b 0 →
      ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc lo hi) a b := by
    intro a b ha1 hb1 ha0 hb0 hab
    have haH := (hmemH a).1 hab.1
    have hbH := (hmemH b).1 hab.2.1
    rw [hlo1] at ha1 hb1
    rcases (show b 0 = x 0 ∨ x 0 < b 0 by omega) with hbx | hbx
    · have hbx' : b = x := hpt _ _ hbx (by rw [hb1, hx1])
      rw [hbx'] at hab
      exact hmin a ha1 (by omega) (localConn_trans hab hxu)
    · obtain ⟨pab, hpabs, hpabe⟩ := exists_walk_of_mem_localConn hab
      have haB : a ∈ boxBoundary lo hi := by
        rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
      have hbB : b ∈ boxBoundary lo hi := by
        rw [mem_boxBoundary_two_iff, hlo0, hlo1, hhi0, hhi1]; omega
      have hpw := perimeterPos_lt_perimeterPos_of_bottom (show b 1 = lo 1 by rw [hlo1, hb1])
        (by rw [hhi0]; omega) hwB (by rw [hlo1]; omega)
      obtain ⟨z, hz₁, hz₂⟩ := exists_mem_support_of_interlaced pab pw hpabs hpws haB hbB hxB hwB
        (Or.inl ⟨by rw [perimeterPos_of_bottom (show a 1 = lo 1 by rw [hlo1, ha1]),
          perimeterPos_of_bottom (show x 1 = lo 1 by rw [hlo1, hx1])]; omega,
          by rw [perimeterPos_of_bottom (show x 1 = lo 1 by rw [hlo1, hx1]),
            perimeterPos_of_bottom (show b 1 = lo 1 by rw [hlo1, hb1])]; omega, Or.inr hpw⟩)
      have h₁' := mem_localConn_of_mem_support pab hpabs hpabe hz₁
      have h₂' := mem_localConn_of_mem_support pw hpws hpwe hz₂
      rw [localConn_comm] at h₂'
      exact hmin a ha1 (by omega) (localConn_trans (localConn_trans h₁' h₂') hxu)
  -- the dual walk from the face on the upper left of `x`
  obtain ⟨g, δ, hg, hδ1, hδE⟩ := exists_dualWalk_of_forall_notMem_localConn h₁
    (show x 1 = lo 1 by rw [hlo1, hx1]) (by rw [hlo0, hx0]; omega) (by rw [hhi0, hx0]; omega)
    ⟨hfL0, hfL1⟩ hsep
  -- the open arm
  have hwT : w ∉ Icc (x - (R : LatticeSite 2) + 1) (x + R - 1) := by
    intro h
    rw [mem_Icc_two_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h
    rw [hx1] at h
    omega
  obtain ⟨c, d, α, hαc, hαs, hαe⟩ := pw.exists_isCrossing_of_start_mem
    (S := Icc (x - ((0 : ℕ) : LatticeSite 2)) (x + ((0 : ℕ) : LatticeSite 2))) (by simp) hwT
  have hcx : c = x := by
    have := hαc.start_mem
    simpa using this
  subst hcx
  have hα : IsOpenArm ω x 0 (x - R) (x + R) α := ⟨hαc, fun e he => hpwe e (hαe e he)⟩
  have hαH : ∀ v ∈ α.support, x 1 ≤ v 1 := fun v hv => by
    have := (hmemH v).1 (hpws v (hαs v hv))
    rw [hx1]
    omega
  -- the dual arm: a path, cut at its first exit from the faces of `B_R(x)`
  have hgT : g ∉ Icc (x - (R : LatticeSite 2)) (x + R - 1) := by
    intro h
    have hg1 := hδ1 g δ.end_mem_support
    refine hg ?_
    rw [mem_Icc_two_iff] at h ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at h ⊢
    rw [hx0, hx1] at h
    rw [hlo0, hhi0, hlo1, hhi1] at *
    omega
  have hfLT : fL ∈ Icc (x - (R : LatticeSite 2)) (x + R - 1) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    rw [hx1] at hfL1 ⊢
    omega
  obtain ⟨g₁, δ₁, s₁, hδs₁, hg₁, hδ₁⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem δ.bypass hgT
  have hδ₁p : δ₁.IsPath := by
    have := δ.bypass_isPath
    rw [← hδs₁] at this
    exact this.of_append_left
  have hδ₁n : ¬δ₁.Nil := fun hn => hg₁ (by rw [← hn.eq]; exact hfLT)
  have hδ₁s : ∀ f ∈ δ₁.support, f ∈ δ.support := fun f hf => by
    refine δ.support_bypass_subset_support ?_
    rw [← hδs₁, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hf
  have hδ₁e : ∀ E ∈ δ₁.edges, E ∈ δ.edges := fun E hE => by
    refine δ.edges_bypass_subset_edges ?_
    rw [← hδs₁, SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ hE
  have hδ₁c : δ₁.IsCrossing {fL} (Icc (x - (R : LatticeSite 2)) (x + R - 1)) := by
    refine ⟨rfl, fun v hv hvf => ?_, hg₁, hδ₁⟩
    have hnd := hδ₁p.support_nodup
    rw [← SimpleGraph.Walk.cons_support_tail hδ₁n, List.nodup_cons] at hnd
    rw [← SimpleGraph.Walk.support_tail_of_not_nil δ₁ hδ₁n] at hv
    rw [mem_singleton_iff] at hvf
    exact hnd.1 (hvf ▸ hv)
  obtain ⟨c', q', β, hqβ, hβc⟩ := hδ₁c.exists_append_eq_isCrossing_of_subset
    (S' := Icc (x - ((0 : ℕ) : LatticeSite 2) - 1) (x + ((0 : ℕ) : LatticeSite 2))) (by
      intro v hv
      rw [mem_singleton_iff] at hv
      subst hv
      rw [mem_Icc_two_iff]
      simp only [Nat.cast_zero, sub_zero, add_zero, Pi.sub_apply, Pi.one_apply]
      omega)
  have hβs : ∀ f ∈ β.support, f ∈ δ.support := fun f hf => hδ₁s f (by
    rw [← hqβ, SimpleGraph.Walk.mem_support_append_iff]; exact Or.inr hf)
  have hβ : IsDualArm ω x 0 (x - R) (x + R) β := ⟨hβc, fun E hE => hδE E (hδ₁e E (by
    rw [← hqβ, SimpleGraph.Walk.edges_append]; exact List.mem_append_right _ hE))⟩
  have hβH : ∀ f ∈ β.support, x 1 ≤ f 1 := fun f hf => by
    have := hδ1 f (hβs f hf)
    rw [hx1]
    rw [hlo1] at this
    exact this
  have hβn : ¬β.Nil := hβc.not_nil (by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp at hv ⊢
    omega)
  have hβpen : β.penultimate = δ₁.penultimate := by
    rw [← hqβ, SimpleGraph.Walk.penultimate_append_of_not_nil _ hβn]
  -- the landing order
  have hlt := landingPos_lt_of_dualWalk hR ⟨hxl0, hxl1⟩ ⟨hfL0, hfL1⟩ hα hαH he₁ δ₁ hδ₁n hδ₁
    (fun f hf => by
      have := hδ1 f (hδ₁s f hf)
      rw [hx1]
      rw [hlo1] at this
      exact this) hg₁ (fun E hE => hδE E (hδ₁e E hE))
  -- the two arms form the half-plane two-arm event
  refine ⟨k₀, Finset.mem_Ioc.2 ⟨hk₀lo', hk₀hi'⟩, ?_⟩
  have hfam : ∀ i : Fin 2, ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (![true, false] i) x 0 (x - R) (x + R) γ ∧ (∀ v ∈ γ.support, x 1 ≤ v 1) ∧
      landingPos (x - R) (x + R) (![true, false] i) γ =
        ![landingPos (x - R) (x + R) true α, landingPos (x - R) (x + R) false β] i := by
    intro i
    fin_cases i
    · exact ⟨_, _, α, hα, hαH, rfl⟩
    · exact ⟨_, _, β, hβ, hβH, rfl⟩
  choose a b γ hγ hγH hγL using hfam
  refine mem_halfArmEvent_iff.2 ⟨a, b, γ, hγ, ⟨fun i k hik hi hk => ?_, fun i k hik hi hk => ?_⟩,
    hγH, ?_⟩
  · revert hik hi hk
    fin_cases i <;> fin_cases k <;> simp
  · revert hik hi hk
    fin_cases i <;> fin_cases k <;> simp
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    rw [hγL, hγL]
    change landingPos (x - R) (x + R) true α < landingPos (x - R) (x + R) false β
    rw [landingPos_false, hβpen]
    exact hlt


/-- **Two arms in the half-plane, lower bound** (Werner's leftmost points). There is `c₁ > 0`
with `c₁ ≤ 4R · P(A₂⁺(R))` for every `R ≥ 1` and every profile equal to `1/2` on the edges. -/
theorem exists_pos_le_mul_law_halfArmEvent_two :
    ∃ c₁ : ℝ≥0∞, 0 < c₁ ∧ c₁ ≠ ∞ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c₁ ≤ 4 * R * law q (halfArmEvent ![true, false] 0 0 R) := by
  obtain ⟨c, hc⟩ := exists_crossingBounds_half
  set q₀ : Sym2 (LatticeSite 2) → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
  have hq₀ : ∀ e ∈ (zdGraph 2).edgeSet, (q₀ e : ℝ) = 1 / 2 := fun _ _ => rfl
  have hc4 := (hc q₀ hq₀).pos 4
  have hc5 := (hc q₀ hq₀).pos 5
  refine ⟨min (c 4 * c 5) 1, lt_min (ENNReal.mul_pos hc4.ne' hc5.ne') one_pos,
    ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne, fun q hq R hR => ?_⟩
  have hCB := hc q hq
  set O := crossing 1 (![(R : ℤ), 0] : LatticeSite 2) ![2 * (R : ℤ), 4 * R] with hOdef
  set D := dualConfig ⁻¹' crossing 1 (![-(2 * (R : ℤ)), -1] : LatticeSite 2) ![-(R : ℤ), 4 * R]
    with hDdef
  have hO : c 4 ≤ law q O := hCB.le_law_crossing_one_of_le 4 (m := R) hR le_top
    (by simp) (by simp) (by simp; ring_nf; omega)
  have hDl : c 5 ≤ law q D := hCB.le_law_dualConfig_crossing_one_of_le 5 (m := R) hR le_top
    (by simp; omega) (by simp; omega) (by simp; omega)
  -- the two strip events read disjoint sets of edges
  have hind : law q (O ∩ D) = law q O * law q D := by
    refine prodBernoulli_inter_of_determined q
      (P := {e | ∀ v ∈ e, v ∈ Icc (![(R : ℤ), 0] : LatticeSite 2) ![2 * (R : ℤ), 4 * R]})
      (Q := {e | ∀ v ∈ e, v ∈ Icc (![-(2 * (R : ℤ)), -1] : LatticeSite 2)
        (![-(R : ℤ), 4 * R] + 1)}) ?_ (measurableSet_crossing _ _ _)
      (measurable_dualConfig (measurableSet_crossing _ _ _))
      (fun ω ω' h => mem_crossing_iff_of_inter_eq subset_rfl h)
      (fun ω ω' h => mem_crossing_iff_of_inter_eq subset_rfl (dualConfig_inter_eq_of_inter_eq h))
    rw [Set.disjoint_left]
    intro e he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨(Quot.out e).1, Sym2.out_fst_mem e⟩
    have h₁ := he v hv
    have h₂ := he' v hv
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply] at h₁ h₂
    omega
  -- both crossings give a two-arm point in `(-2R, 2R]`
  have hsub : O ∩ D ⊆ ⋃ k ∈ Finset.Ioc (-(2 * (R : ℤ))) (2 * R),
      halfArmEvent ![true, false] ![k, 0] 0 R := fun ω hω => by
    obtain ⟨k, hk, h⟩ := exists_mem_halfArmEvent_two_of_mem_crossing hR hω.1 hω.2
    exact mem_iUnion₂.2 ⟨k, hk, h⟩
  calc min (c 4 * c 5) 1 ≤ c 4 * c 5 := min_le_left _ _
    _ ≤ law q O * law q D := mul_le_mul' hO hDl
    _ = law q (O ∩ D) := hind.symm
    _ ≤ law q (⋃ k ∈ Finset.Ioc (-(2 * (R : ℤ))) (2 * R),
          halfArmEvent ![true, false] ![k, 0] 0 R) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.Ioc (-(2 * (R : ℤ))) (2 * R),
          law q (halfArmEvent ![true, false] ![k, 0] 0 R) := measure_biUnion_finset_le _ _
    _ = 4 * R * law q (halfArmEvent ![true, false] 0 0 R) := by
        simp only [law_halfArmEvent_eq_law_halfArmEvent_zero hq, Finset.sum_const, Int.card_Ioc,
          nsmul_eq_mul]
        congr 1
        rw [show (2 * (R : ℤ) - -(2 * (R : ℤ))).toNat = 4 * R by omega]
        push_cast
        ring

/-- **Two arms in the half-plane, exponent 1** (Nolin, Theorem 24(1); Werner, *Lectures on
two-dimensional critical percolation*, first exercise sheet). At `1/2`, the probability that the
boundary vertex `0` of the upper half-plane has an open arm and, to its left, a dual arm to
distance `R` in the half-plane is of order `1/R`. -/
theorem exists_halfArmEvent_two_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → ∀ R : ℕ, 1 ≤ R →
        c / R ≤ (law q).real (halfArmEvent ![true, false] 0 0 R) ∧
          (law q).real (halfArmEvent ![true, false] 0 0 R) ≤ C / R := by
  obtain ⟨C₀, hC₀, hup⟩ := exists_mul_law_halfArmEvent_two_le
  obtain ⟨c₁, hc₁, hc₁', hlow⟩ := exists_pos_le_mul_law_halfArmEvent_two
  have hc₁r : 0 < c₁.toReal := ENNReal.toReal_pos hc₁.ne' hc₁'
  refine ⟨c₁.toReal / 4, C₀.toReal + 1, by positivity, by positivity, fun q hq R hR => ⟨?_, ?_⟩⟩
  · have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top R)) (measure_ne_top _ _)) (hlow q hq R hR)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
    rw [measureReal_def, div_div, div_le_iff₀ (by positivity)]
    linarith
  · have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have h := ENNReal.toReal_mono hC₀ (hup q hq R)
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
    rw [measureReal_def, le_div_iff₀ hR']
    linarith

end HalfPlaneTwoArms

end PercLib.Models.Planar
