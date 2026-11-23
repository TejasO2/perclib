/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation, p. 1579), the
conditioning on the explored crossings in its proof.
-/
module

public import PercLib.Models.Planar.Arms.SeparationFence

/-!
# Local separation of crossings: conditioning on the greedy exploration

Nolin's local separation lemma bounds the probability that the tip of a greedy crossing is not
protected, conditionally on the crossings found so far. The library does not condition: it sums
over the possible explorations. For each finite sequence `B` of explored sets, the event "the
exploration up to step `v` is `B`" is measurable, determined by the pairs whose duals meet the last
set, and these events are pairwise disjoint (uniqueness of the exploration). A protection event at
the tip of `Γ (B v)` that is determined by other pairs, at `J` independent scales of probability at
least `β`, then fails at every scale with probability at most `(1 - β)^J`
(`law_exploration_forall_notMem_le`). The exploration may run on any measurable function of the
configuration, in particular on the dual configuration.

The protection events are built from the pairs `Q` of an annulus that the exploration has not
looked at, in four forms, according to the colour of the strips and to the sign of the event:
`ω ∩ Q` crosses none of three strips, the dual configuration of `ω ∪ Qᶜ` crosses none of them,
`ω ∪ Qᶜ` crosses four boxes, and the dual configuration of `ω ∩ Q` crosses four boxes. Each is
determined by `Q` by construction and contains a circuit event, so it has probability at least
`c 7 ^ 4` under crossing bounds.

The first step of the lemma (few greedy crossings) is also proved here for an exploration in a
box narrower than the boxes of the crossing bounds (`law_exploration_le_pow_of_le`,
`law_exploration_dualConfig_le_pow_of_le`): the strip `[0, 4N] × [0, N]` lies in the box of width
`5 (N - 1)` and height `N`.

## Main results

* `MeasureTheory.measure_iUnion_inter_le`: summing conditional bounds over a countable partition;
  `MeasureTheory.one_sub_le_measure_of_forall_notMem`: the complement of a small event.
* `measurableSet_exploration`, `exploration_iff_of_inter_eq`: the exploration event is measurable
  and determined by the pairs meeting its last set.
* `law_exploration_forall_notMem_le`: protection at `J` scales fails with probability at most
  `(1 - β)^J`, uniformly over the explorations.
* `law_exploration_le_pow_of_le`, `law_exploration_dualConfig_le_pow_of_le`: few greedy
  crossings, for explorations of the open and of the dual configuration in a narrower box.
* `pow_le_law_inter_notMem_crossing_add`, `pow_le_law_dualConfig_union_notMem_crossing_add`,
  `pow_le_law_union_mem_crossing_add`, `pow_le_law_dualConfig_inter_mem_crossing_add`: the four
  forms of protection events have probability at least `c 7 ^ 4`.
* `law_exploration_forall_notMem_inter_le`, `law_exploration_forall_notMem_dualConfig_union_le`,
  `law_exploration_forall_notMem_union_le`, `law_exploration_forall_notMem_dualConfig_inter_le`:
  the four forms fail at all scales `s j` (growing by a factor `8`) around a point attached to the
  last explored set with probability at most `(1 - c 7 ^ 4)^J`; `law_forall_notMem_inter_le`,
  `law_forall_notMem_dualConfig_union_le`: the same at a fixed centre (the corners).
* `notMem_crossing_sdiff_of_inter`, `notMem_crossing_dualConfig_union_of`,
  `mem_crossing_union_of`, `notMem_crossing_dualConfig_sdiff_of`,
  `notMem_crossing_dualConfig_dualConfig_union_of`, `mem_crossing_dualConfig_union_of`,
  `notMem_crossing_inter_of`, `notMem_crossing_dualConfig_inter_of`: each protection event gives
  the hypotheses of the blocking and fence lemmas of `SeparationProtection.lean` and
  `SeparationFence.lean`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace MeasureTheory

/-- **Summing over a countable partition.** Let `X i` be pairwise disjoint measurable events and
`F i` events with `μ (X i ∩ F i) ≤ μ (X i) * r`. Then the union of the `X i ∩ F i` has
probability at most `r`. -/
theorem measure_iUnion_inter_le {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    [IsProbabilityMeasure μ] {X F : ι → Set α} (hX : ∀ i, MeasurableSet (X i))
    (hdisj : Pairwise (Function.onFun Disjoint X)) {r : ℝ≥0∞}
    (h : ∀ i, μ (X i ∩ F i) ≤ μ (X i) * r) :
    μ (⋃ i, X i ∩ F i) ≤ r :=
  calc μ (⋃ i, X i ∩ F i) ≤ ∑' i, μ (X i ∩ F i) := measure_iUnion_le _
    _ ≤ ∑' i, μ (X i) * r := ENNReal.tsum_le_tsum h
    _ = μ (⋃ i, X i) * r := by rw [ENNReal.tsum_mul_right, measure_iUnion hdisj hX]
    _ ≤ 1 * r := mul_le_mul_left prob_le_one r
    _ = r := one_mul r

/-- The union bound, with bounds for both events. -/
theorem measure_union_le_add_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B : Set α}
    {a b : ℝ≥0∞} (hA : μ A ≤ a) (hB : μ B ≤ b) : μ (A ∪ B) ≤ a + b :=
  (measure_union_le A B).trans (add_le_add hA hB)

/-- The union bound over the first `n` indices, with a common bound. -/
theorem measure_biUnion_range_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → Set α} {r : ℝ≥0∞} (n : ℕ) (h : ∀ v < n, μ (F v) ≤ r) :
    μ (⋃ v ∈ Finset.range n, F v) ≤ n * r := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ v ∈ Finset.range n, μ (F v) ≤ ∑ _v ∈ Finset.range n, r :=
        Finset.sum_le_sum fun v hv => h v (Finset.mem_range.1 hv)
    _ = n * r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Complement of a small event.** If every outcome outside `B` is in `F` and `μ B ≤ δ`, then
`μ F ≥ 1 - δ`; no measurability is needed. -/
theorem one_sub_le_measure_of_forall_notMem {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F B : Set α} {δ : ℝ≥0∞} (hB : μ B ≤ δ) (hF : ∀ ω ∉ B, ω ∈ F) :
    1 - δ ≤ μ F := by
  have h1 : 1 ≤ μ Bᶜ + μ B := by
    rw [← measure_univ (μ := μ), ← compl_union_self B]
    exact measure_union_le _ _
  calc 1 - δ ≤ 1 - μ B := tsub_le_tsub_left hB 1
    _ ≤ μ Bᶜ := tsub_le_iff_right.2 h1
    _ ≤ μ F := measure_mono fun ω hω => hF ω hω

end MeasureTheory

namespace PercLib.Models.Planar

/-! ### The exploration event -/

section Greedy

variable {lo hi : LatticeSite 2} {c d : Finset (LatticeSite 2) → LatticeSite 2}
  {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- The exploration condition up to step `v` depends only on the sets up to step `v`. -/
theorem exploration_congr {G : Config (LatticeSite 2)} {A A' : ℕ → Finset (LatticeSite 2)}
    {v : ℕ} (h : ∀ w ≤ v, A w = A' w) :
    (∀ w ≤ v, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
          ↑(A w)) ↔
      ∀ w ≤ v, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A' w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A' w) := by
  refine forall_congr' fun w => forall_congr' fun hw => ?_
  have hR : {e : Sym2 (LatticeSite 2) | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support} =
      {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A' w')).support} := by
    ext e
    simp only [mem_ofPred_eq]
    refine exists_congr fun x => and_congr_right fun _ => exists_congr fun w' =>
      and_congr_right fun hw' => ?_
    rw [h w' (by omega)]
  rw [hR, h w hw]

/-- The wired dual configuration of `g ω` with a fixed set of pairs removed is a measurable
function of `ω`, for every measurable `g`. -/
theorem measurable_wired_comp {g : Config (LatticeSite 2) → Config (LatticeSite 2)}
    (hg : Measurable g) (R : Set (Sym2 (LatticeSite 2))) :
    Measurable fun ω : Config (LatticeSite 2) => dualConfig (g ω \ R) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))} := by
  refine Measurable.of_mem fun s => ?_
  simp only [mem_union, mem_inter_iff, mem_dualConfig_iff, mem_sdiff]
  exact ((measurable_const.and (((measurable_set_mem _).comp hg).and
    measurable_const).not).and measurable_const).or measurable_const

/-- **The exploration event is measurable**, for the exploration of any measurable function of
the configuration. -/
theorem measurableSet_exploration {g : Config (LatticeSite 2) → Config (LatticeSite 2)}
    (hg : Measurable g) (A : ℕ → Finset (LatticeSite 2)) (v : ℕ) :
    MeasurableSet {ω : Config (LatticeSite 2) | ∀ w ≤ v,
      cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)} := by
  have hw : ∀ w, MeasurableSet {ω : Config (LatticeSite 2) |
      cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)} := by
    intro w
    by_cases ha : (![lo 0 - 1, lo 1] : LatticeSite 2) ∈ A w
    · exact measurable_wired_comp hg _ (measurableSet_cluster_eq_finset _ _ ha)
    · convert MeasurableSet.empty
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      apply ha
      rw [← Finset.mem_coe, ← h]
      exact mem_cluster_self _ _
  have hset : {ω : Config (LatticeSite 2) | ∀ w ≤ v,
      cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)} = ⋂ w, ⋂ (_ : w ≤ v), {ω : Config (LatticeSite 2) |
      cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun w => MeasurableSet.iInter fun _ => hw w

/-- **The exploration event is determined by the pairs meeting its last set.** Let `g` be a
function of configurations such that, for every finite set `D` of faces, `g ω` and `g ω'` agree on
the edges of `ℤ²` with a dual face in `D` as soon as `ω` and `ω'` agree on `P D`. Then whether `A`
is the exploration of `g ω` up to step `v` depends only on `ω ∩ P (A v)`. -/
theorem exploration_iff_of_inter_eq {g : Config (LatticeSite 2) → Config (LatticeSite 2)}
    {P : Finset (LatticeSite 2) → Set (Sym2 (LatticeSite 2))}
    (hP : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)), ω ∩ P D = ω' ∩ P D →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ g ω ↔ e ∈ g ω'))
    (A : ℕ → Finset (LatticeSite 2)) (v : ℕ) {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ P (A v) = ω' ∩ P (A v)) :
    (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
          ↑(A w)) ↔
      ∀ w ≤ v, cluster (dualConfig (g ω' \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w) := by
  have key := fun (hm : ∀ w ≤ v, A w ⊆ A v)
      (ha : ∀ w ≤ v, (![lo 0 - 1, lo 1] : LatticeSite 2) ∈ A w) =>
    exploration_iff_of_agree (Γ := Γ) (lo := lo) (hi := hi) (G := g ω) (G' := g ω') hm ha
      fun e he hf => hP _ ω ω' h e he hf
  have hm : ∀ (G : Config (LatticeSite 2)), (∀ w ≤ v, cluster (dualConfig
      (G \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
          ↑(A w)) →
      (∀ w ≤ v, A w ⊆ A v) ∧ ∀ w ≤ v, (![lo 0 - 1, lo 1] : LatticeSite 2) ∈ A w := by
    intro G hA
    refine ⟨fun w hw => exploration_mono hA hw le_rfl, fun w hw => ?_⟩
    rw [← Finset.mem_coe, ← hA w hw]
    exact mem_cluster_self _ _
  constructor
  · intro hA
    exact (key (hm _ hA).1 (hm _ hA).2).1 hA
  · intro hA
    exact (key (hm _ hA).1 (hm _ hA).2).2 hA

/-- **Protection at many scales, uniformly over the explorations.** Let `g` be a measurable
function of configurations whose exploration events are determined as in
`exploration_iff_of_inter_eq`. For each finite set `D` of faces let `K D j`, `j < J`, be
measurable events, determined by pairwise disjoint sets `Q D j` of pairs disjoint from `P D`, each
of probability at least `β`. Then the probability that the exploration of `g ω` up to step `v`
ends with a set `A v` such that `ω` is in none of the `K (A v) j` is at most `(1 - β)^J`. -/
theorem law_exploration_forall_notMem_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {g : Config (LatticeSite 2) → Config (LatticeSite 2)} (hg : Measurable g)
    {P : Finset (LatticeSite 2) → Set (Sym2 (LatticeSite 2))}
    (hP : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)), ω ∩ P D = ω' ∩ P D →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ g ω ↔ e ∈ g ω'))
    (v J : ℕ) {β : ℝ≥0∞} {K : Finset (LatticeSite 2) → ℕ → Set (Config (LatticeSite 2))}
    {Q : Finset (LatticeSite 2) → ℕ → Set (Sym2 (LatticeSite 2))}
    (hKm : ∀ D, ∀ j < J, MeasurableSet (K D j))
    (hKQ : ∀ D j, ∀ ω ω' : Config (LatticeSite 2), ω ∩ Q D j = ω' ∩ Q D j →
      (ω ∈ K D j ↔ ω' ∈ K D j))
    (hPQ : ∀ D, ∀ j < J, Disjoint (P D) (Q D j))
    (hQ : ∀ D, Set.PairwiseDisjoint (↑(Finset.range J)) (Q D))
    (hβ : ∀ D, ∀ j < J, β ≤ law q (K D j)) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) ∧
      ∀ j < J, ω ∉ K (A v) j} ≤ (1 - β) ^ J := by
  classical
  -- explorations up to step `v`, as functions on `Fin (v + 1)`
  set ext : (Fin (v + 1) → Finset (LatticeSite 2)) → ℕ → Finset (LatticeSite 2) :=
    fun B w => if h : w < v + 1 then B ⟨w, h⟩ else ∅ with hext
  have hextv : ∀ B, ext B v = B (Fin.last v) := fun B => by
    rw [hext]
    dsimp only
    rw [dite_eq_left (by omega)]
    rfl
  set X : (Fin (v + 1) → Finset (LatticeSite 2)) → Set (Config (LatticeSite 2)) := fun B =>
    {ω | ∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w,
        x ∈ (Γ (ext B w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(ext B w)} with hX
  have hXm : ∀ B, MeasurableSet (X B) := fun B => measurableSet_exploration hg (ext B) v
  have hXdisj : Pairwise (Function.onFun Disjoint X) := by
    intro B B' hBB'
    refine Set.disjoint_left.2 fun ω h h' => hBB' (funext fun i => ?_)
    have := exploration_unique h h' i (by omega)
    rw [hext] at this
    simp only [dite_eq_left (show (i : ℕ) < v + 1 from i.2)] at this
    exact this
  have hsub : {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) ∧
      ∀ j < J, ω ∉ K (A v) j} ⊆
      ⋃ B, X B ∩ ⋂ j ∈ Finset.range J, (K (B (Fin.last v)) j)ᶜ := by
    rintro ω ⟨A, hA, hK⟩
    have hagree : ∀ w ≤ v, A w = ext (fun i => A i) w := fun w hw => by
      rw [hext]
      dsimp only
      rw [dite_eq_left (by omega)]
    refine mem_iUnion.2 ⟨fun i => A i, (exploration_congr hagree).1 hA, ?_⟩
    refine mem_iInter₂.2 fun j hj => ?_
    exact hK j (Finset.mem_range.1 hj)
  refine (measure_mono hsub).trans (measure_iUnion_inter_le (law q) hXm hXdisj fun B => ?_)
  refine law_inter_biInter_compl_le q (hXm B) (fun ω ω' h => ?_) (hKm _) (hKQ _) (hPQ _) (hQ _)
    (hβ _)
  rw [← hextv B] at h
  exact exploration_iff_of_inter_eq hP (ext B) v h

end Greedy

/-! ### Few greedy crossings in a narrower box -/

/-- **The greedy exploration finds few crossings, in a narrower box.** The exploration of the open
configuration in a box of height `n + 1` and width at most `k n` finds at least `u + 1` crossings
with probability at most `(1 - c (k + 1))^(u + 1)`: its chosen crossings are disjoint open
crossings of the box of width `k n` with the same lower left corner. -/
theorem law_exploration_le_pow_of_le {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (h : CrossingBounds q L c) (k : ℕ) {lo hi : LatticeSite 2} {n : ℕ}
    (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) (hhi1 : hi 1 = lo 1 + (n + 1))
    (hhi0 : hi 0 ≤ lo 0 + k * n)
    {c₁ d₁ : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c₁ A) (d₁ A)}
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c₁ A ∈ Icc lo hi ∧ c₁ A 1 = lo 1 ∧ d₁ A ∈ Icc lo hi ∧ d₁ A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    (u : ℕ) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ v ≤ u, cluster (dualConfig (ω \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A v)) ∧
      ∀ v ≤ u, ∀ f ∈ A v, f 0 ≠ hi 0} ≤ (1 - c (k + 1)) ^ (u + 1) := by
  have h1 : lo 1 < hi 1 := by omega
  have hsub : ∀ x ∈ Icc lo hi, x ∈ Icc lo (lo + ![(k : ℤ) * n, n + 1]) := fun x hx => by
    rw [mem_Icc_two_iff] at hx ⊢
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  refine le_trans (MeasureTheory.measure_mono fun ω hω => ?_)
    (law_foldl_crossing_one_le_pow h k lo hn hnL (u + 1))
  obtain ⟨A, hA, hright⟩ := hω
  have hprop := fun j : Fin (u + 1) =>
    forall_mem_of_exploration h1 hΓ hA (Nat.lt_succ_iff.1 j.2) (hright j (Nat.lt_succ_iff.1 j.2))
  have hdata := fun j : Fin (u + 1) => hΓ (A j)
    (mem_leftColumn_of_exploration hA (Nat.lt_succ_iff.1 j.2)) (hright j (Nat.lt_succ_iff.1 j.2))
  refine mem_foldl_crossing_of_walks (fun j : Fin (u + 1) => Γ (A j)) (fun j => (hdata j).2.1)
    (fun j => by
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [(hdata j).2.2.2.1]
      omega)
    (fun j x hx => hsub x ((hdata j).2.2.2.2.1 x hx)) (fun j => (hprop j).1) ?_
  intro j l hjl e hej hel
  -- an edge shared by two chosen crossings would give them a common vertex
  obtain ⟨x, y, rfl, -, hx, -⟩ := exists_ne_of_mem_edges (Γ (A j)) hej
  have hxl : x ∈ (Γ (A l)).support := (Γ (A l)).fst_mem_support_of_mem_edges hel
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjl) with hlt | hlt
  · exact (hprop l).2 x hxl j hlt hx
  · exact (hprop j).2 x hx l hlt hxl

/-- **The greedy exploration finds few dual crossings, in a narrower box.** The same bound for the
exploration of the dual configuration in a box of faces of height `n + 1` and width at most
`k n`. -/
theorem law_exploration_dualConfig_le_pow_of_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {L : ℕ∞} {c : ℕ → ℝ≥0∞} (h : CrossingBounds q L c) (k : ℕ) {lo hi : LatticeSite 2} {n : ℕ}
    (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) (hhi1 : hi 1 = lo 1 + (n + 1))
    (hhi0 : hi 0 ≤ lo 0 + k * n)
    {c₁ d₁ : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c₁ A) (d₁ A)}
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c₁ A ∈ Icc lo hi ∧ c₁ A 1 = lo 1 ∧ d₁ A ∈ Icc lo hi ∧ d₁ A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    (u : ℕ) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ v ≤ u, cluster (dualConfig (dualConfig ω \
          {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A v)) ∧
      ∀ v ≤ u, ∀ f ∈ A v, f 0 ≠ hi 0} ≤ (1 - c (k + 1)) ^ (u + 1) := by
  have h1 : lo 1 < hi 1 := by omega
  have hsub : ∀ x ∈ Icc lo hi, x ∈ Icc lo (lo + ![(k : ℤ) * n, n + 1]) := fun x hx => by
    rw [mem_Icc_two_iff] at hx ⊢
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  refine le_trans (MeasureTheory.measure_mono fun ω hω => ?_)
    (law_foldl_dualConfig_crossing_one_le_pow h k lo hn hnL (u + 1))
  obtain ⟨A, hA, hright⟩ := hω
  have hprop := fun j : Fin (u + 1) =>
    forall_mem_of_exploration h1 hΓ hA (Nat.lt_succ_iff.1 j.2) (hright j (Nat.lt_succ_iff.1 j.2))
  have hdata := fun j : Fin (u + 1) => hΓ (A j)
    (mem_leftColumn_of_exploration hA (Nat.lt_succ_iff.1 j.2)) (hright j (Nat.lt_succ_iff.1 j.2))
  refine mem_foldl_dualConfig_crossing_of_walks (fun j : Fin (u + 1) => Γ (A j))
    (fun j => (hdata j).2.1)
    (fun j => by
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [(hdata j).2.2.2.1]
      omega)
    (fun j x hx => hsub x ((hdata j).2.2.2.2.1 x hx)) (fun j => (hprop j).1) ?_
  intro j l hjl e hej hel
  -- an edge shared by two chosen crossings would give them a common vertex
  obtain ⟨x, y, rfl, -, hx, -⟩ := exists_ne_of_mem_edges (Γ (A j)) hej
  have hxl : x ∈ (Γ (A l)).support := (Γ (A l)).fst_mem_support_of_mem_edges hel
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjl) with hlt | hlt
  · exact (hprop l).2 x hxl j hlt hx
  · exact (hprop j).2 x hx l hlt hxl

/-! ### Protection events built from a set of fresh pairs -/

section Protection

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- **Open strips uncrossed, on fresh pairs.** Under crossing bounds up to `L ≥ 2t - 1`, the pairs
of `ω` in any set `Q` cross none of the bottom, right and left strips of the annulus
`t ≤ ‖· - z‖∞ ≤ 3t` in their short directions with probability at least `c 7 ^ 4`. -/
theorem pow_le_law_inter_notMem_crossing_add (h : CrossingBounds q L c) (z : LatticeSite 2)
    {t m : ℕ} (hm : 2 * t = m + 1) (hmL : (m : ℕ∞) ≤ L) (Q : Set (Sym2 (LatticeSite 2))) :
    c 7 ^ 4 ≤ law q {ω |
      ω ∩ Q ∉ crossing 1 (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ), -t]) ∧
      ω ∩ Q ∉ crossing 0 (z + ![(t : ℤ), -3 * t]) (z + ![3 * (t : ℤ), 3 * t]) ∧
      ω ∩ Q ∉ crossing 0 (z + ![-3 * (t : ℤ), -3 * t]) (z + ![-(t : ℤ), 3 * t])} := by
  refine (pow_le_law_compl_crossing_inter_add h z hm hmL).trans
    (MeasureTheory.measure_mono fun ω hω => ?_)
  obtain ⟨⟨⟨-, hB⟩, hR⟩, hL⟩ := hω
  exact ⟨fun hc => hB (crossing_mono inter_subset_left hc),
    fun hc => hR (crossing_mono inter_subset_left hc),
    fun hc => hL (crossing_mono inter_subset_left hc)⟩

/-- **Dual strips uncrossed, on fresh pairs.** Under crossing bounds up to `L ≥ 2t - 1`, the dual
configuration of `ω ∪ Qᶜ` (the pairs outside `Q` count as open) crosses none of the bottom, right
and left strips of faces of the annulus `t ≤ ‖· - z‖∞ ≤ 3t` in their short directions with
probability at least `c 7 ^ 4`. -/
theorem pow_le_law_dualConfig_union_notMem_crossing_add (h : CrossingBounds q L c)
    (z : LatticeSite 2) {t m : ℕ} (hm : 2 * t = m + 1) (hmL : (m : ℕ∞) ≤ L)
    (Q : Set (Sym2 (LatticeSite 2))) :
    c 7 ^ 4 ≤ law q {ω |
      dualConfig (ω ∪ Qᶜ) ∉ crossing 1 (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ), -t]) ∧
      dualConfig (ω ∪ Qᶜ) ∉ crossing 0 (z + ![(t : ℤ), -3 * t]) (z + ![3 * (t : ℤ), 3 * t]) ∧
      dualConfig (ω ∪ Qᶜ) ∉
        crossing 0 (z + ![-3 * (t : ℤ), -3 * t]) (z + ![-(t : ℤ), 3 * t])} := by
  refine (pow_le_law_dualConfig_notMem_crossing_add h z hm hmL).trans
    (MeasureTheory.measure_mono fun ω hω => ?_)
  obtain ⟨-, hB, hR, hL⟩ := hω
  have hsub := dualConfig_anti (subset_union_left (s := ω) (t := Qᶜ))
  exact ⟨fun hc => hB (crossing_mono hsub hc), fun hc => hR (crossing_mono hsub hc),
    fun hc => hL (crossing_mono hsub hc)⟩

/-- **Open circuit, with the pairs outside `Q` open.** Under crossing bounds up to `L ≥ 2t - 1`,
`ω ∪ Qᶜ` crosses the four boxes around the annulus `t ≤ ‖· - z‖∞ ≤ 3t + 1` in their long
directions with probability at least `c 7 ^ 4`. -/
theorem pow_le_law_union_mem_crossing_add (h : CrossingBounds q L c) (z : LatticeSite 2)
    {t m : ℕ} (hm : 2 * t = m + 1) (hmL : (m : ℕ∞) ≤ L) (Q : Set (Sym2 (LatticeSite 2))) :
    c 7 ^ 4 ≤ law q {ω |
      ω ∪ Qᶜ ∈ crossing 0 (z + ![-3 * (t : ℤ), t + 1]) (z + ![3 * (t : ℤ) + 1, 3 * t]) ∧
      ω ∪ Qᶜ ∈ crossing 0 (z + ![-3 * (t : ℤ), -3 * t + 1]) (z + ![3 * (t : ℤ) + 1, -t]) ∧
      ω ∪ Qᶜ ∈ crossing 1 (z + ![(t : ℤ) + 1, -3 * t]) (z + ![3 * (t : ℤ), 3 * t + 1]) ∧
      ω ∪ Qᶜ ∈ crossing 1 (z + ![-3 * (t : ℤ) + 1, -3 * t]) (z + ![-(t : ℤ), 3 * t + 1])} := by
  refine (pow_le_law_crossing_inter_add h z hm hmL).trans
    (MeasureTheory.measure_mono fun ω hω => ?_)
  obtain ⟨⟨⟨hT, hB⟩, hR⟩, hL⟩ := hω
  exact ⟨crossing_mono subset_union_left hT, crossing_mono subset_union_left hB,
    crossing_mono subset_union_left hR, crossing_mono subset_union_left hL⟩

/-- **Dual circuit of faces, on fresh pairs.** Under crossing bounds up to `L ≥ 2t - 1`, the dual
configuration of `ω ∩ Q` (the pairs outside `Q` count as closed) crosses the four boxes of faces
around the annulus `t ≤ ‖· - z‖∞ ≤ 3t + 1` in their long directions with probability at least
`c 7 ^ 4`: by box duality this contains the absence of open crossings of the four strips around
`z + (1, 1)`. -/
theorem pow_le_law_dualConfig_inter_mem_crossing_add (h : CrossingBounds q L c)
    (z : LatticeSite 2) {t m : ℕ} (hm : 2 * t = m + 1) (hmL : (m : ℕ∞) ≤ L)
    (Q : Set (Sym2 (LatticeSite 2))) :
    c 7 ^ 4 ≤ law q {ω |
      dualConfig (ω ∩ Q) ∈
        crossing 0 (z + ![-3 * (t : ℤ), t + 1]) (z + ![3 * (t : ℤ) + 1, 3 * t]) ∧
      dualConfig (ω ∩ Q) ∈
        crossing 0 (z + ![-3 * (t : ℤ), -3 * t + 1]) (z + ![3 * (t : ℤ) + 1, -t]) ∧
      dualConfig (ω ∩ Q) ∈
        crossing 1 (z + ![(t : ℤ) + 1, -3 * t]) (z + ![3 * (t : ℤ), 3 * t + 1]) ∧
      dualConfig (ω ∩ Q) ∈
        crossing 1 (z + ![-3 * (t : ℤ) + 1, -3 * t]) (z + ![-(t : ℤ), 3 * t + 1])} := by
  refine (pow_le_law_compl_crossing_inter_add h (z + 1) hm hmL).trans
    (MeasureTheory.measure_mono fun ω hω => ?_)
  obtain ⟨⟨⟨hT, hB⟩, hR⟩, hL⟩ := hω
  have hle : ∀ x₀ y₀ x₁ y₁ : ℤ, x₀ ≤ x₁ → y₀ ≤ y₁ → (![x₀, y₀] : LatticeSite 2) ≤ ![x₁, y₁] :=
    fun x₀ y₀ x₁ y₁ hx hy => by
      rw [Pi.le_def, Fin.forall_fin_two]
      exact ⟨hx, hy⟩
  have hv : ∀ (a b : ℤ), z + 1 + ![a, b] = ![z 0 + 1 + a, z 1 + 1 + b] := fun a b => by
    ext i
    fin_cases i <;> simp
  have hw : ∀ (a b : ℤ), z + ![a, b] = ![z 0 + a, z 1 + b] := fun a b => by
    ext i
    fin_cases i <;> simp
  have hsub := dualConfig_anti (inter_subset_left (s := ω) (t := Q))
  rw [hv, hv] at hT hB hR hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (mem_crossing_one_iff_dualConfig_notMem_crossing_zero
      (hle _ _ _ _ (by omega) (by omega)) ω).not.1 hT
    rw [not_not] at this
    refine crossing_mono hsub ?_
    rw [hw, hw]
    convert this using 2 <;> ext i <;> fin_cases i <;> simp <;> ring
  · have := (mem_crossing_one_iff_dualConfig_notMem_crossing_zero
      (hle _ _ _ _ (by omega) (by omega)) ω).not.1 hB
    rw [not_not] at this
    refine crossing_mono hsub ?_
    rw [hw, hw]
    convert this using 2 <;> ext i <;> fin_cases i <;> simp <;> ring
  · have := (mem_crossing_zero_iff_dualConfig_notMem_crossing_one
      (hle _ _ _ _ (by omega) (by omega)) ω).not.1 hR
    rw [not_not] at this
    refine crossing_mono hsub ?_
    rw [hw, hw]
    convert this using 2 <;> ext i <;> fin_cases i <;> simp <;> ring
  · have := (mem_crossing_zero_iff_dualConfig_notMem_crossing_one
      (hle _ _ _ _ (by omega) (by omega)) ω).not.1 hL
    rw [not_not] at this
    refine crossing_mono hsub ?_
    rw [hw, hw]
    convert this using 2 <;> ext i <;> fin_cases i <;> simp <;> ring

end Protection

/-! ### From fresh pairs to the blocking hypotheses -/

/-- A crossing of a box by `ζ` is a crossing by every `ζ'` containing the pairs of `ζ` inside the
box. -/
theorem mem_crossing_of_inter_subset {d : ℕ} {i : Fin d} {lo hi : LatticeSite d}
    {ζ ζ' : Config (LatticeSite d)} (hsub : ζ ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ⊆ ζ')
    (h : ζ ∈ crossing i lo hi) : ζ' ∈ crossing i lo hi := by
  refine crossing_mono hsub ((mem_crossing_iff_of_inter_eq (le_refl (Icc lo hi)) ?_).1 h)
  rw [inter_assoc, inter_self]

/-- If `ζ'` contains the pairs of `ζ` inside a box and does not cross it, neither does `ζ`. -/
theorem notMem_crossing_of_inter_subset {d : ℕ} {i : Fin d} {lo hi : LatticeSite d}
    {ζ ζ' : Config (LatticeSite d)} (hsub : ζ ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ⊆ ζ')
    (h : ζ' ∉ crossing i lo hi) : ζ ∉ crossing i lo hi :=
  fun hζ => h (mem_crossing_of_inter_subset hsub hζ)

/-- The ends of the edge of `ℤ²` crossed by a dual edge `p` are corners of each face of `p`. -/
theorem le_of_mem_map_add_one_dualEdge {p : Sym2 (LatticeSite 2)}
    (hp : p ∈ (zdGraph 2).edgeSet) {f x : LatticeSite 2} (hf : f ∈ p)
    (hx : x ∈ Sym2.map (· + 1) (dualEdge p)) :
    f 0 ≤ x 0 ∧ x 0 ≤ f 0 + 1 ∧ f 1 ≤ x 1 ∧ x 1 ≤ f 1 + 1 := by
  have he := map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hp)
  have hf' : f ∈ dualEdge (Sym2.map (· + 1) (dualEdge p)) := by
    rw [dualEdge_map_add_one_dualEdge hp]
    exact hf
  have := face_of_mem_dualEdge he hx hf'
  omega

/-- Distinct dual edges cross distinct edges of `ℤ²`. -/
theorem map_add_one_dualEdge_injOn :
    InjOn (fun p : Sym2 (LatticeSite 2) => Sym2.map (· + 1) (dualEdge p)) (zdGraph 2).edgeSet :=
  fun p hp p' hp' h => by
    have := congrArg dualEdge h
    simp only at this
    rwa [dualEdge_map_add_one_dualEdge hp, dualEdge_map_add_one_dualEdge hp'] at this

/-- The edge crossed by the dual edge crossed by a dual edge of the dual lattice `p` is `p`
translated by `(1, 1)`. -/
theorem map_add_one_dualEdge_map_add_one_dualEdge {p : Sym2 (LatticeSite 2)}
    (hp : p ∈ (zdGraph 2).edgeSet) :
    Sym2.map (· + 1) (dualEdge (Sym2.map (· + 1) (dualEdge p))) = Sym2.map (· + 1) p := by
  rw [dualEdge_map_add, dualEdge_dualEdge hp, Sym2.map_map, Sym2.map_map]
  congr 1
  funext v
  simp only [Function.comp_apply]
  abel

/-- **Same colour, dual configuration.** Let `S` be a box of faces whose faces, moved by at most
one step up and right, lie in a set `R` of vertices, and let `Q` be the pairs inside `R` other than
the edges crossed by the dual edges of `E`. The dual edges of `ω` outside `E` with both faces in
`S` are open in the dual configuration of `ω ∪ Qᶜ`. -/
theorem dualConfig_sdiff_inter_subset {ω : Config (LatticeSite 2)}
    {E : Set (Sym2 (LatticeSite 2))} {R S : Set (LatticeSite 2)}
    (hSR : ∀ f ∈ S, ∀ x : LatticeSite 2, f 0 ≤ x 0 → x 0 ≤ f 0 + 1 → f 1 ≤ x 1 →
      x 1 ≤ f 1 + 1 → x ∈ R) (B : Set (Sym2 (LatticeSite 2))) :
    (dualConfig ω \ E) ∩ B ∩ {p | ∀ f ∈ p, f ∈ S} ⊆
      dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ R} \
        (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))ᶜ) := by
  rintro p ⟨⟨⟨hpω, hpE⟩, -⟩, hpS⟩
  rw [mem_dualConfig_iff] at hpω ⊢
  refine ⟨hpω.1, ?_⟩
  rintro (h | h)
  · exact hpω.2 h
  · apply h
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨f, hf⟩ : ∃ f, f ∈ p := ⟨p.out.1, Sym2.out_fst_mem p⟩
      obtain ⟨h₁, h₂, h₃, h₄⟩ := le_of_mem_map_add_one_dualEdge hpω.1 hf hx
      exact hSR f (hpS f hf) x h₁ h₂ h₃ h₄
    · rintro ⟨e, ⟨heE, he⟩, hep⟩
      exact hpE (map_add_one_dualEdge_injOn he hpω.1 hep ▸ heE)

/-- **Other colour, open exploration.** With `R`, `S` as in `dualConfig_sdiff_inter_subset` and
`Q` the pairs inside `R` that are not edges of `E`, the dual edges with both faces in `S` that are
open in the dual configuration of `ω ∪ E` are open in the dual configuration of `ω ∪ Qᶜ`. -/
theorem dualConfig_union_inter_subset {ω : Config (LatticeSite 2)}
    {E : Set (Sym2 (LatticeSite 2))} {R S : Set (LatticeSite 2)}
    (hSR : ∀ f ∈ S, ∀ x : LatticeSite 2, f 0 ≤ x 0 → x 0 ≤ f 0 + 1 → f 1 ≤ x 1 →
      x 1 ≤ f 1 + 1 → x ∈ R) (B : Set (Sym2 (LatticeSite 2))) :
    dualConfig (ω ∪ E) ∩ B ∩ {p | ∀ f ∈ p, f ∈ S} ⊆
      dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ R} \ (E ∩ (zdGraph 2).edgeSet))ᶜ) := by
  rintro p ⟨⟨hpω, -⟩, hpS⟩
  rw [mem_dualConfig_iff] at hpω ⊢
  refine ⟨hpω.1, ?_⟩
  rintro (h | h)
  · exact hpω.2 (Or.inl h)
  · apply h
    refine ⟨fun x hx => ?_, fun hE => hpω.2 (Or.inr hE.1)⟩
    obtain ⟨f, hf⟩ : ∃ f, f ∈ p := ⟨p.out.1, Sym2.out_fst_mem p⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := le_of_mem_map_add_one_dualEdge hpω.1 hf hx
    exact hSR f (hpS f hf) x h₁ h₂ h₃ h₄

/-- **Fence, dual configuration.** With `R`, `S` as in `dualConfig_sdiff_inter_subset`, the dual
edges with both faces in `S` that are open in the dual configuration of `ω ∩ Q` are open in the
dual configuration of `ω` or are in `E`. -/
theorem dualConfig_inter_inter_subset {ω : Config (LatticeSite 2)}
    {E : Set (Sym2 (LatticeSite 2))} {R S : Set (LatticeSite 2)}
    (hSR : ∀ f ∈ S, ∀ x : LatticeSite 2, f 0 ≤ x 0 → x 0 ≤ f 0 + 1 → f 1 ≤ x 1 →
      x 1 ≤ f 1 + 1 → x ∈ R) :
    dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ R} \
        (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))) ∩
      {p | ∀ f ∈ p, f ∈ S} ⊆ dualConfig ω ∪ E := by
  rintro p ⟨hpω, hpS⟩
  rw [mem_dualConfig_iff] at hpω
  by_cases hω : Sym2.map (· + 1) (dualEdge p) ∈ ω
  · right
    by_contra hpE
    refine hpω.2 ⟨hω, fun x hx => ?_, ?_⟩
    · obtain ⟨f, hf⟩ : ∃ f, f ∈ p := ⟨p.out.1, Sym2.out_fst_mem p⟩
      obtain ⟨h₁, h₂, h₃, h₄⟩ := le_of_mem_map_add_one_dualEdge hpω.1 hf hx
      exact hSR f (hpS f hf) x h₁ h₂ h₃ h₄
    · rintro ⟨e, ⟨heE, he⟩, hep⟩
      exact hpE (map_add_one_dualEdge_injOn he hpω.1 hep ▸ heE)
  · left
    exact (mem_dualConfig_iff ω p).2 ⟨hpω.1, hω⟩

/-- **Other colour, dual exploration.** Let `Q` be the pairs inside `R` other than the edges crossed
by the dual edges of `E`. Translated by `(1, 1)`, the edges of the dual configuration of
`dualConfig ω ∪ E` (edges of the lattice of faces of faces) that land in `R` are edges of `ω` in
`Q`. -/
theorem image_dualConfig_union_inter_subset {ω : Config (LatticeSite 2)}
    {E : Set (Sym2 (LatticeSite 2))} {R : Set (LatticeSite 2)} (B : Set (Sym2 (LatticeSite 2))) :
    Sym2.map (· + 1) '' (dualConfig (dualConfig ω ∪ E) ∩ B) ∩ {e | ∀ x ∈ e, x ∈ R} ⊆
      ω ∩ ({e | ∀ x ∈ e, x ∈ R} \
        (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet)) := by
  rintro _ ⟨⟨p, ⟨hp, -⟩, rfl⟩, hpR⟩
  rw [mem_dualConfig_iff] at hp
  obtain ⟨hpL, hpX⟩ := hp
  have hp' : Sym2.map (· + 1) (dualEdge p) ∈ (zdGraph 2).edgeSet :=
    map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hpL)
  have hω : Sym2.map (· + 1) (dualEdge (Sym2.map (· + 1) (dualEdge p))) ∈ ω := by
    by_contra h
    exact hpX (Or.inl ((mem_dualConfig_iff ω _).2 ⟨hp', h⟩))
  rw [map_add_one_dualEdge_map_add_one_dualEdge hpL] at hω
  refine ⟨hω, hpR, ?_⟩
  rintro ⟨e, ⟨heE, he⟩, hep⟩
  rw [← map_add_one_dualEdge_map_add_one_dualEdge hpL] at hep
  exact hpX (Or.inr (map_add_one_dualEdge_injOn he hp' hep ▸ heE))

/-! ### Annuli at scales growing by a factor `8` -/

/-- The annuli `s - 2 ≤ ‖· - z‖∞ ≤ 3s + 2` at scales `s ≥ 1` and `s' ≥ 8s` are disjoint. -/
theorem disjoint_annulus (z : LatticeSite 2) {s s' : ℕ} (hs : 1 ≤ s) (h : 8 * s ≤ s') :
    Disjoint {x : LatticeSite 2 | z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
        z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
        (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)}
      {x : LatticeSite 2 | z 0 - (3 * s' + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s' + 2) ∧
        z 1 - (3 * s' + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s' + 2) ∧
        (x 0 + s' ≤ z 0 + 2 ∨ z 0 + s' ≤ x 0 + 2 ∨ x 1 + s' ≤ z 1 + 2 ∨
          z 1 + s' ≤ x 1 + 2)} := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  simp only [mem_ofPred_eq] at hx hx'
  have : (8 * s : ℤ) ≤ s' := by exact_mod_cast h
  omega

/-- **Pairs in annuli at scales growing by a factor `8`.** The sets of pairs inside the annuli
`s j - 2 ≤ ‖· - z‖∞ ≤ 3 s j + 2`, `j < J`, for scales `s j ≥ 1` with `8 s j ≤ s j'` for `j < j'`,
with any fixed set of pairs removed, are pairwise disjoint. -/
theorem pairwiseDisjoint_annulus (z : LatticeSite 2) {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ s j)
    (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (P : Set (Sym2 (LatticeSite 2))) (J : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range J)) fun j => {e : Sym2 (LatticeSite 2) | ∀ x ∈ e,
      x ∈ {x : LatticeSite 2 | z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
        z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
        (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
          z 1 + s j ≤ x 1 + 2)}} \ P := by
  have hdisj : ∀ j j' : ℕ, j < j' → Disjoint
      {e : Sym2 (LatticeSite 2) | ∀ x ∈ e,
        x ∈ {x : LatticeSite 2 | z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}}
      {e : Sym2 (LatticeSite 2) | ∀ x ∈ e,
        x ∈ {x : LatticeSite 2 | z 0 - (3 * s j' + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j' + 2) ∧
          z 1 - (3 * s j' + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j' + 2) ∧
          (x 0 + s j' ≤ z 0 + 2 ∨ z 0 + s j' ≤ x 0 + 2 ∨ x 1 + s j' ≤ z 1 + 2 ∨
            z 1 + s j' ≤ x 1 + 2)}} := by
    intro j j' hjj'
    have hd := disjoint_annulus z (hs j) (hs8 j j' hjj')
    refine Set.disjoint_left.2 fun e he he' => ?_
    obtain ⟨x, hx⟩ : ∃ x, x ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
    exact Set.disjoint_left.1 hd (he x hx) (he' x hx)
  intro j _ j' _ hjj'
  refine Disjoint.mono sdiff_le sdiff_le ?_
  rcases lt_or_gt_of_ne hjj' with h | h
  · exact hdisj j j' h
  · exact (hdisj j' j h).symm

/-! ### Protection at many scales, uniformly over the explorations

The annulus at scale `s` around `z` is `s - 2 ≤ ‖· - z‖∞ ≤ 3s + 2`; the fresh pairs at that scale
are the pairs inside it that the exploration has not looked at. -/

section Scales

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}
  {lo hi : LatticeSite 2} {c₁ d₁ : Finset (LatticeSite 2) → LatticeSite 2}
  {Γ : ∀ A, (zdGraph 2).Walk (c₁ A) (d₁ A)}

/-- A configuration restricted to a fixed set of pairs is a measurable function of it. -/
theorem measurable_inter_const (Q : Set (Sym2 (LatticeSite 2))) :
    Measurable fun ω : Config (LatticeSite 2) => ω ∩ Q :=
  Measurable.of_mem fun s => by
    simp only [mem_inter_iff]
    exact (measurable_set_mem s).and measurable_const

/-- A configuration with a fixed set of pairs added is a measurable function of it. -/
theorem measurable_union_const (Q : Set (Sym2 (LatticeSite 2))) :
    Measurable fun ω : Config (LatticeSite 2) => ω ∪ Q :=
  Measurable.of_mem fun s => by
    simp only [mem_union]
    exact (measurable_set_mem s).or measurable_const

/-- Two configurations agreeing on `Q` agree once the pairs outside `Q` are added. -/
theorem union_compl_eq_of_inter_eq {ω ω' : Config (LatticeSite 2)}
    {Q : Set (Sym2 (LatticeSite 2))} (h : ω ∩ Q = ω' ∩ Q) : ω ∪ Qᶜ = ω' ∪ Qᶜ := by
  ext e
  have := congrArg (e ∈ ·) h
  simp only [mem_inter_iff, eq_iff_iff] at this
  simp only [mem_union, mem_compl_iff]
  by_cases he : e ∈ Q <;> simp_all

/-- **Open strips, at many scales.** For every exploration determined as in
`exploration_iff_of_inter_eq`, the fresh pairs at the scales `s j` (growing by a factor `8`)
around the point `z (A v)` attached to the last explored set are, at every scale `j < J`, crossing
one of the bottom, right and left strips, with probability at most `(1 - c 7 ^ 4)^J`. -/
theorem law_exploration_forall_notMem_inter_le (h : CrossingBounds q L c)
    {g : Config (LatticeSite 2) → Config (LatticeSite 2)} (hg : Measurable g)
    {P : Finset (LatticeSite 2) → Set (Sym2 (LatticeSite 2))}
    (hP : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)), ω ∩ P D = ω' ∩ P D →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ g ω ↔ e ∈ g ω'))
    (z : Finset (LatticeSite 2) → LatticeSite 2) {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ s j)
    (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (v J : ℕ)
    (hJ : ∀ j < J, ((2 * s j - 1 : ℕ) : ℕ∞) ≤ L) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) ∧
      ∀ j < J, ω ∉ {ω : Config (LatticeSite 2) |
        ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v)) ∉
          crossing 1 (z (A v) + ![-3 * (s j : ℤ), -3 * s j]) (z (A v) + ![3 * (s j : ℤ), -s j]) ∧
        ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v)) ∉
          crossing 0 (z (A v) + ![(s j : ℤ), -3 * s j]) (z (A v) + ![3 * (s j : ℤ), 3 * s j]) ∧
        ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v)) ∉
          crossing 0 (z (A v) + ![-3 * (s j : ℤ), -3 * s j])
            (z (A v) + ![-(s j : ℤ), 3 * s j])}} ≤ (1 - c 7 ^ 4) ^ J := by
  set R : Finset (LatticeSite 2) → ℕ → Set (Sym2 (LatticeSite 2)) := fun D j =>
    {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z D 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z D 0 + (3 * s j + 2) ∧
      z D 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z D 1 + (3 * s j + 2) ∧
      (x 0 + s j ≤ z D 0 + 2 ∨ z D 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z D 1 + 2 ∨
        z D 1 + s j ≤ x 1 + 2)}} \ P D with hR
  have key := law_exploration_forall_notMem_le (q := q) (Γ := Γ) (lo := lo) (hi := hi) hg hP v J
    (β := c 7 ^ 4) (Q := R) (K := fun D j => {ω : Config (LatticeSite 2) |
      ω ∩ R D j ∉ crossing 1 (z D + ![-3 * (s j : ℤ), -3 * s j]) (z D + ![3 * (s j : ℤ), -s j]) ∧
      ω ∩ R D j ∉ crossing 0 (z D + ![(s j : ℤ), -3 * s j]) (z D + ![3 * (s j : ℤ), 3 * s j]) ∧
      ω ∩ R D j ∉ crossing 0 (z D + ![-3 * (s j : ℤ), -3 * s j]) (z D + ![-(s j : ℤ), 3 * s j])})
    (fun D j _ => ?_) (fun D j ω ω' hωω' => ?_) (fun D j _ => disjoint_sdiff_right)
    (fun D => pairwiseDisjoint_annulus (z D) hs hs8 (P D) J) (fun D j hj => ?_)
  · exact key
  · have hm := measurable_inter_const (R D j)
    exact (hm (measurableSet_crossing _ _ _).compl).inter
      ((hm (measurableSet_crossing _ _ _).compl).inter (hm (measurableSet_crossing _ _ _).compl))
  · simp only [mem_ofPred_eq]
    rw [hωω']
  · exact pow_le_law_inter_notMem_crossing_add h (z D) (t := s j) (m := 2 * s j - 1)
      (by have := hs j; omega) (hJ j hj) _

/-- **Dual strips, at many scales.** As `law_exploration_forall_notMem_inter_le`, for the dual
configuration of `ω` with the pairs outside the fresh pairs added (counted as open). -/
theorem law_exploration_forall_notMem_dualConfig_union_le
    (h : CrossingBounds q L c)
    {g : Config (LatticeSite 2) → Config (LatticeSite 2)} (hg : Measurable g)
    {P : Finset (LatticeSite 2) → Set (Sym2 (LatticeSite 2))}
    (hP : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)), ω ∩ P D = ω' ∩ P D →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ g ω ↔ e ∈ g ω'))
    (z : Finset (LatticeSite 2) → LatticeSite 2) {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ s j)
    (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (v J : ℕ)
    (hJ : ∀ j < J, ((2 * s j - 1 : ℕ) : ℕ∞) ≤ L) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) ∧
      ∀ j < J, ω ∉ {ω : Config (LatticeSite 2) |
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ) ∉
          crossing 1 (z (A v) + ![-3 * (s j : ℤ), -3 * s j]) (z (A v) + ![3 * (s j : ℤ), -s j]) ∧
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ) ∉
          crossing 0 (z (A v) + ![(s j : ℤ), -3 * s j]) (z (A v) + ![3 * (s j : ℤ), 3 * s j]) ∧
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ) ∉
          crossing 0 (z (A v) + ![-3 * (s j : ℤ), -3 * s j])
            (z (A v) + ![-(s j : ℤ), 3 * s j])}} ≤ (1 - c 7 ^ 4) ^ J := by
  set R : Finset (LatticeSite 2) → ℕ → Set (Sym2 (LatticeSite 2)) := fun D j =>
    {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z D 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z D 0 + (3 * s j + 2) ∧
      z D 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z D 1 + (3 * s j + 2) ∧
      (x 0 + s j ≤ z D 0 + 2 ∨ z D 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z D 1 + 2 ∨
        z D 1 + s j ≤ x 1 + 2)}} \ P D with hR
  have key := law_exploration_forall_notMem_le (q := q) (Γ := Γ) (lo := lo) (hi := hi) hg hP v J
    (β := c 7 ^ 4) (Q := R) (K := fun D j => {ω : Config (LatticeSite 2) |
      dualConfig (ω ∪ (R D j)ᶜ) ∉
        crossing 1 (z D + ![-3 * (s j : ℤ), -3 * s j]) (z D + ![3 * (s j : ℤ), -s j]) ∧
      dualConfig (ω ∪ (R D j)ᶜ) ∉
        crossing 0 (z D + ![(s j : ℤ), -3 * s j]) (z D + ![3 * (s j : ℤ), 3 * s j]) ∧
      dualConfig (ω ∪ (R D j)ᶜ) ∉
        crossing 0 (z D + ![-3 * (s j : ℤ), -3 * s j]) (z D + ![-(s j : ℤ), 3 * s j])})
    (fun D j _ => ?_) (fun D j ω ω' hωω' => ?_) (fun D j _ => disjoint_sdiff_right)
    (fun D => pairwiseDisjoint_annulus (z D) hs hs8 (P D) J) (fun D j hj => ?_)
  · exact key
  · have hm := measurable_dualConfig.comp (measurable_union_const (R D j)ᶜ)
    exact (hm (measurableSet_crossing _ _ _).compl).inter
      ((hm (measurableSet_crossing _ _ _).compl).inter (hm (measurableSet_crossing _ _ _).compl))
  · simp only [mem_ofPred_eq]
    rw [union_compl_eq_of_inter_eq hωω']
  · exact pow_le_law_dualConfig_union_notMem_crossing_add h (z D) (t := s j) (m := 2 * s j - 1)
      (by have := hs j; omega) (hJ j hj) _

/-- **Open circuits, at many scales.** As `law_exploration_forall_notMem_inter_le`, for `ω` with the
pairs outside the fresh pairs added (counted as open) crossing the four boxes of an annulus in their
long directions. -/
theorem law_exploration_forall_notMem_union_le
    (h : CrossingBounds q L c)
    {g : Config (LatticeSite 2) → Config (LatticeSite 2)} (hg : Measurable g)
    {P : Finset (LatticeSite 2) → Set (Sym2 (LatticeSite 2))}
    (hP : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)), ω ∩ P D = ω' ∩ P D →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ g ω ↔ e ∈ g ω'))
    (z : Finset (LatticeSite 2) → LatticeSite 2) {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ s j)
    (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (v J : ℕ)
    (hJ : ∀ j < J, ((2 * s j - 1 : ℕ) : ℕ∞) ≤ L) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) ∧
      ∀ j < J, ω ∉ {ω : Config (LatticeSite 2) |
        ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ ∈
          crossing 0 (z (A v) + ![-3 * (s j : ℤ), s j + 1])
            (z (A v) + ![3 * (s j : ℤ) + 1, 3 * s j]) ∧
        ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ ∈
          crossing 0 (z (A v) + ![-3 * (s j : ℤ), -3 * s j + 1])
            (z (A v) + ![3 * (s j : ℤ) + 1, -s j]) ∧
        ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ ∈
          crossing 1 (z (A v) + ![(s j : ℤ) + 1, -3 * s j])
            (z (A v) + ![3 * (s j : ℤ), 3 * s j + 1]) ∧
        ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))ᶜ ∈
          crossing 1 (z (A v) + ![-3 * (s j : ℤ) + 1, -3 * s j])
            (z (A v) + ![-(s j : ℤ), 3 * s j + 1])}} ≤ (1 - c 7 ^ 4) ^ J := by
  set R : Finset (LatticeSite 2) → ℕ → Set (Sym2 (LatticeSite 2)) := fun D j =>
    {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z D 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z D 0 + (3 * s j + 2) ∧
      z D 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z D 1 + (3 * s j + 2) ∧
      (x 0 + s j ≤ z D 0 + 2 ∨ z D 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z D 1 + 2 ∨
        z D 1 + s j ≤ x 1 + 2)}} \ P D with hR
  have key := law_exploration_forall_notMem_le (q := q) (Γ := Γ) (lo := lo) (hi := hi) hg hP v J
    (β := c 7 ^ 4) (Q := R) (K := fun D j => {ω : Config (LatticeSite 2) |
      ω ∪ (R D j)ᶜ ∈
        crossing 0 (z D + ![-3 * (s j : ℤ), s j + 1]) (z D + ![3 * (s j : ℤ) + 1, 3 * s j]) ∧
      ω ∪ (R D j)ᶜ ∈
        crossing 0 (z D + ![-3 * (s j : ℤ), -3 * s j + 1]) (z D + ![3 * (s j : ℤ) + 1, -s j]) ∧
      ω ∪ (R D j)ᶜ ∈
        crossing 1 (z D + ![(s j : ℤ) + 1, -3 * s j]) (z D + ![3 * (s j : ℤ), 3 * s j + 1]) ∧
      ω ∪ (R D j)ᶜ ∈
        crossing 1 (z D + ![-3 * (s j : ℤ) + 1, -3 * s j]) (z D + ![-(s j : ℤ), 3 * s j + 1])})
    (fun D j _ => ?_) (fun D j ω ω' hωω' => ?_) (fun D j _ => disjoint_sdiff_right)
    (fun D => pairwiseDisjoint_annulus (z D) hs hs8 (P D) J) (fun D j hj => ?_)
  · exact key
  · have hm := measurable_union_const (R D j)ᶜ
    exact (hm (measurableSet_crossing _ _ _)).inter ((hm (measurableSet_crossing _ _ _)).inter
      ((hm (measurableSet_crossing _ _ _)).inter (hm (measurableSet_crossing _ _ _))))
  · simp only [mem_ofPred_eq]
    rw [union_compl_eq_of_inter_eq hωω']
  · exact pow_le_law_union_mem_crossing_add h (z D) (t := s j) (m := 2 * s j - 1)
      (by have := hs j; omega) (hJ j hj) _

/-- **Dual circuits of faces, at many scales.** As `law_exploration_forall_notMem_inter_le`, for the
dual configuration of the fresh pairs of `ω` crossing the four boxes of faces of an annulus in their
long directions. -/
theorem law_exploration_forall_notMem_dualConfig_inter_le
    (h : CrossingBounds q L c)
    {g : Config (LatticeSite 2) → Config (LatticeSite 2)} (hg : Measurable g)
    {P : Finset (LatticeSite 2) → Set (Sym2 (LatticeSite 2))}
    (hP : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)), ω ∩ P D = ω' ∩ P D →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ g ω ↔ e ∈ g ω'))
    (z : Finset (LatticeSite 2) → LatticeSite 2) {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ s j)
    (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (v J : ℕ)
    (hJ : ∀ j < J, ((2 * s j - 1 : ℕ) : ℕ∞) ≤ L) :
    law q {ω | ∃ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (g ω \ {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) ∧
      ∀ j < J, ω ∉ {ω : Config (LatticeSite 2) |
        dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))) ∈
          crossing 0 (z (A v) + ![-3 * (s j : ℤ), s j + 1])
            (z (A v) + ![3 * (s j : ℤ) + 1, 3 * s j]) ∧
        dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))) ∈
          crossing 0 (z (A v) + ![-3 * (s j : ℤ), -3 * s j + 1])
            (z (A v) + ![3 * (s j : ℤ) + 1, -s j]) ∧
        dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))) ∈
          crossing 1 (z (A v) + ![(s j : ℤ) + 1, -3 * s j])
            (z (A v) + ![3 * (s j : ℤ), 3 * s j + 1]) ∧
        dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z (A v) 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z (A v) 0 + (3 * s j + 2) ∧
          z (A v) 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z (A v) 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z (A v) 0 + 2 ∨ z (A v) 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z (A v) 1 + 2 ∨
            z (A v) 1 + s j ≤ x 1 + 2)}} \ P (A v))) ∈
          crossing 1 (z (A v) + ![-3 * (s j : ℤ) + 1, -3 * s j])
            (z (A v) + ![-(s j : ℤ), 3 * s j + 1])}} ≤ (1 - c 7 ^ 4) ^ J := by
  set R : Finset (LatticeSite 2) → ℕ → Set (Sym2 (LatticeSite 2)) := fun D j =>
    {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z D 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z D 0 + (3 * s j + 2) ∧
      z D 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z D 1 + (3 * s j + 2) ∧
      (x 0 + s j ≤ z D 0 + 2 ∨ z D 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z D 1 + 2 ∨
        z D 1 + s j ≤ x 1 + 2)}} \ P D with hR
  have key := law_exploration_forall_notMem_le (q := q) (Γ := Γ) (lo := lo) (hi := hi) hg hP v J
    (β := c 7 ^ 4) (Q := R) (K := fun D j => {ω : Config (LatticeSite 2) |
      dualConfig (ω ∩ R D j) ∈
        crossing 0 (z D + ![-3 * (s j : ℤ), s j + 1]) (z D + ![3 * (s j : ℤ) + 1, 3 * s j]) ∧
      dualConfig (ω ∩ R D j) ∈
        crossing 0 (z D + ![-3 * (s j : ℤ), -3 * s j + 1]) (z D + ![3 * (s j : ℤ) + 1, -s j]) ∧
      dualConfig (ω ∩ R D j) ∈
        crossing 1 (z D + ![(s j : ℤ) + 1, -3 * s j]) (z D + ![3 * (s j : ℤ), 3 * s j + 1]) ∧
      dualConfig (ω ∩ R D j) ∈
        crossing 1 (z D + ![-3 * (s j : ℤ) + 1, -3 * s j]) (z D + ![-(s j : ℤ), 3 * s j + 1])})
    (fun D j _ => ?_) (fun D j ω ω' hωω' => ?_) (fun D j _ => disjoint_sdiff_right)
    (fun D => pairwiseDisjoint_annulus (z D) hs hs8 (P D) J) (fun D j hj => ?_)
  · exact key
  · have hm := measurable_dualConfig.comp (measurable_inter_const (R D j))
    exact (hm (measurableSet_crossing _ _ _)).inter ((hm (measurableSet_crossing _ _ _)).inter
      ((hm (measurableSet_crossing _ _ _)).inter (hm (measurableSet_crossing _ _ _))))
  · simp only [mem_ofPred_eq]
    rw [hωω']
  · exact pow_le_law_dualConfig_inter_mem_crossing_add h (z D) (t := s j) (m := 2 * s j - 1)
      (by have := hs j; omega) (hJ j hj) _

/-- **Open strips at a fixed centre, at many scales.** The pairs of `ω` in the annuli at the
scales `s j` around `z` cross, at every scale, one of the bottom, right and left strips with
probability at most `(1 - c 7 ^ 4)^J`. -/
theorem law_forall_notMem_inter_le (h : CrossingBounds q L c) (z : LatticeSite 2) {s : ℕ → ℕ}
    (hs : ∀ j, 1 ≤ s j) (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (J : ℕ)
    (hJ : ∀ j < J, ((2 * s j - 1 : ℕ) : ℕ∞) ≤ L) :
    law q {ω | ∀ j < J, ω ∉ {ω : Config (LatticeSite 2) |
        ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}} ∉
          crossing 1 (z + ![-3 * (s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), -s j]) ∧
        ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}} ∉
          crossing 0 (z + ![(s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), 3 * s j]) ∧
        ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}} ∉
          crossing 0 (z + ![-3 * (s j : ℤ), -3 * s j])
            (z + ![-(s j : ℤ), 3 * s j])}} ≤ (1 - c 7 ^ 4) ^ J := by
  set R : ℕ → Set (Sym2 (LatticeSite 2)) := fun j =>
    {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
      z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
      (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
        z 1 + s j ≤ x 1 + 2)}} with hR
  have hQ : Set.PairwiseDisjoint (↑(Finset.range J)) R := fun i hi j hj hij => by
    have := pairwiseDisjoint_annulus z hs hs8 ∅ J hi hj hij
    simpa only [Function.onFun, sdiff_empty] using this
  have key := law_inter_biInter_compl_le q (X := univ) (P := ∅) (Q := R) (J := J)
    (β := c 7 ^ 4) (K := fun j => {ω : Config (LatticeSite 2) |
      ω ∩ R j ∉
        crossing 1 (z + ![-3 * (s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), -s j]) ∧
      ω ∩ R j ∉
        crossing 0 (z + ![(s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), 3 * s j]) ∧
      ω ∩ R j ∉
        crossing 0 (z + ![-3 * (s j : ℤ), -3 * s j]) (z + ![-(s j : ℤ), 3 * s j])})
    MeasurableSet.univ (fun _ _ _ => Iff.rfl) (fun j _ => ?_) (fun j ω ω' hωω' => ?_)
    (fun j _ => empty_disjoint _) hQ (fun j hj => ?_)
  · refine le_trans (MeasureTheory.measure_mono fun ω hω => ?_) (key.trans_eq ?_)
    · exact ⟨mem_univ _, mem_iInter₂.2 fun j hj => hω j (Finset.mem_range.1 hj)⟩
    · rw [MeasureTheory.measure_univ, one_mul]
  · have hm := measurable_inter_const (R j)
    exact (hm (measurableSet_crossing _ _ _).compl).inter
      ((hm (measurableSet_crossing _ _ _).compl).inter (hm (measurableSet_crossing _ _ _).compl))
  · simp only [mem_ofPred_eq]
    rw [hωω']
  · exact pow_le_law_inter_notMem_crossing_add h z (t := s j) (m := 2 * s j - 1)
      (by have := hs j; omega) (hJ j hj) _

/-- **Dual strips at a fixed centre, at many scales.** The same for the dual configuration of `ω`
with the pairs outside the annuli added. -/
theorem law_forall_notMem_dualConfig_union_le (h : CrossingBounds q L c) (z : LatticeSite 2)
    {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ s j) (hs8 : ∀ j j', j < j' → 8 * s j ≤ s j') (J : ℕ)
    (hJ : ∀ j < J, ((2 * s j - 1 : ℕ) : ℕ∞) ≤ L) :
    law q {ω | ∀ j < J, ω ∉ {ω : Config (LatticeSite 2) |
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}})ᶜ) ∉
          crossing 1 (z + ![-3 * (s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), -s j]) ∧
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}})ᶜ) ∉
          crossing 0 (z + ![(s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), 3 * s j]) ∧
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
          z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
          (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
            z 1 + s j ≤ x 1 + 2)}})ᶜ) ∉
          crossing 0 (z + ![-3 * (s j : ℤ), -3 * s j])
            (z + ![-(s j : ℤ), 3 * s j])}} ≤ (1 - c 7 ^ 4) ^ J := by
  set R : ℕ → Set (Sym2 (LatticeSite 2)) := fun j =>
    {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s j + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s j + 2) ∧
      z 1 - (3 * s j + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s j + 2) ∧
      (x 0 + s j ≤ z 0 + 2 ∨ z 0 + s j ≤ x 0 + 2 ∨ x 1 + s j ≤ z 1 + 2 ∨
        z 1 + s j ≤ x 1 + 2)}} with hR
  have hQ : Set.PairwiseDisjoint (↑(Finset.range J)) R := fun i hi j hj hij => by
    have := pairwiseDisjoint_annulus z hs hs8 ∅ J hi hj hij
    simpa only [Function.onFun, sdiff_empty] using this
  have key := law_inter_biInter_compl_le q (X := univ) (P := ∅) (Q := R) (J := J)
    (β := c 7 ^ 4) (K := fun j => {ω : Config (LatticeSite 2) |
      dualConfig (ω ∪ (R j)ᶜ) ∉
        crossing 1 (z + ![-3 * (s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), -s j]) ∧
      dualConfig (ω ∪ (R j)ᶜ) ∉
        crossing 0 (z + ![(s j : ℤ), -3 * s j]) (z + ![3 * (s j : ℤ), 3 * s j]) ∧
      dualConfig (ω ∪ (R j)ᶜ) ∉
        crossing 0 (z + ![-3 * (s j : ℤ), -3 * s j]) (z + ![-(s j : ℤ), 3 * s j])})
    MeasurableSet.univ (fun _ _ _ => Iff.rfl) (fun j _ => ?_) (fun j ω ω' hωω' => ?_)
    (fun j _ => empty_disjoint _) hQ (fun j hj => ?_)
  · refine le_trans (MeasureTheory.measure_mono fun ω hω => ?_) (key.trans_eq ?_)
    · exact ⟨mem_univ _, mem_iInter₂.2 fun j hj => hω j (Finset.mem_range.1 hj)⟩
    · rw [MeasureTheory.measure_univ, one_mul]
  · have hm := measurable_dualConfig.comp (measurable_union_const (R j)ᶜ)
    exact (hm (measurableSet_crossing _ _ _).compl).inter
      ((hm (measurableSet_crossing _ _ _).compl).inter (hm (measurableSet_crossing _ _ _).compl))
  · simp only [mem_ofPred_eq]
    rw [union_compl_eq_of_inter_eq hωω']
  · exact pow_le_law_dualConfig_union_notMem_crossing_add h z (t := s j) (m := 2 * s j - 1)
      (by have := hs j; omega) (hJ j hj) _

end Scales

/-! ### From the protection events to the blocking hypotheses -/

section Unpack

variable {ω : Config (LatticeSite 2)} {E : Set (Sym2 (LatticeSite 2))} (z : LatticeSite 2) (s : ℕ)

/-- **Same colour, open.** The fresh open strips at `z` uncrossed give the hypotheses of
`lt_sub_of_exploration`. -/
theorem notMem_crossing_sdiff_of_inter (B : Set (Sym2 (LatticeSite 2)))
    (h : ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)}} \
        (E ∩ (zdGraph 2).edgeSet)) ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)}} \
        (E ∩ (zdGraph 2).edgeSet)) ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)}} \
        (E ∩ (zdGraph 2).edgeSet)) ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s])) :
    (ω \ E) ∩ B ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    (ω \ E) ∩ B ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    (ω \ E) ∩ B ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s]) := by
  have hR : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s ≤ x 1)) →
      ∀ x ∈ Icc lo' hi', x ∈ {x : LatticeSite 2 |
        z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
        z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
        (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)} :=
    fun lo' hi' h x hx => by
      have := h x hx
      simp only [mem_ofPred_eq]
      omega
  have hRf : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s - 1 ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s + 1 ∧ z 1 - 3 * s - 1 ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s + 1 ∧
      (x 0 ≤ z 0 - s + 1 ∨ z 0 + s - 1 ≤ x 0 ∨ x 1 ≤ z 1 - s + 1 ∨ z 1 + s - 1 ≤ x 1)) →
      ∀ f ∈ Icc lo' hi', ∀ x : LatticeSite 2, f 0 ≤ x 0 → x 0 ≤ f 0 + 1 → f 1 ≤ x 1 →
        x 1 ≤ f 1 + 1 → x ∈ {x : LatticeSite 2 |
        z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
        z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
        (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)} :=
    fun lo' hi' h f hf x h₁ h₂ h₃ h₄ => by
      have := h f hf
      simp only [mem_ofPred_eq]
      omega
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s ≤ x 1)) →
      (ω \ E) ∩ B ∩ {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆ ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
        z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
        z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
        (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨ z 1 + s ≤ x 1 + 2)}} \
        (E ∩ (zdGraph 2).edgeSet)) := by
    rintro lo' hi' hX e ⟨⟨⟨heω, heE⟩, -⟩, heX⟩
    exact ⟨heω, fun x hx => hR lo' hi' hX x (heX x hx), fun he => heE he.1⟩
  refine ⟨notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Other colour, open exploration.** The fresh dual strips at `z` uncrossed give the hypotheses
of `false_of_localConn_of_exploration`. -/
theorem notMem_crossing_dualConfig_union_of (B : Set (Sym2 (LatticeSite 2)))
    (h : dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ) ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ) ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ) ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s])) :
    dualConfig (ω ∪ E) ∩ B ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    dualConfig (ω ∪ E) ∩ B ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    dualConfig (ω ∪ E) ∩ B ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s ≤ x 1)) →
      dualConfig (ω ∪ E) ∩ B ∩ {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
          z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
          (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
            z 1 + s ≤ x 1 + 2)}} \
          (E ∩ (zdGraph 2).edgeSet))ᶜ) := fun lo' hi' hX =>
    dualConfig_union_inter_subset (fun f hf x h₁ h₂ h₃ h₄ => by
      have := hX f hf
      simp only [mem_ofPred_eq]
      omega) B
  refine ⟨notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Fence, open exploration.** The fresh open circuit at `z` gives the hypotheses of
`exists_fence_of_exploration`. -/
theorem mem_crossing_union_of
    (h : ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ ∈
      crossing 0 (z + ![-3 * (s : ℤ), s + 1]) (z + ![3 * (s : ℤ) + 1, 3 * s]) ∧
    ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ ∈
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s + 1]) (z + ![3 * (s : ℤ) + 1, -s]) ∧
    ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ ∈
      crossing 1 (z + ![(s : ℤ) + 1, -3 * s]) (z + ![3 * (s : ℤ), 3 * s + 1]) ∧
    ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (E ∩ (zdGraph 2).edgeSet))ᶜ ∈
      crossing 1 (z + ![-3 * (s : ℤ) + 1, -3 * s]) (z + ![-(s : ℤ), 3 * s + 1])) :
    ω ∪ E ∈
      crossing 0 (z + ![-3 * (s : ℤ), s + 1]) (z + ![3 * (s : ℤ) + 1, 3 * s]) ∧
    ω ∪ E ∈
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s + 1]) (z + ![3 * (s : ℤ) + 1, -s]) ∧
    ω ∪ E ∈
      crossing 1 (z + ![(s : ℤ) + 1, -3 * s]) (z + ![3 * (s : ℤ), 3 * s + 1]) ∧
    ω ∪ E ∈
      crossing 1 (z + ![-3 * (s : ℤ) + 1, -3 * s]) (z + ![-(s : ℤ), 3 * s + 1]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s + 1 ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s + 1 ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s + 1 ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s + 1 ≤ x 1)) →
      (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
          z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
          (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
            z 1 + s ≤ x 1 + 2)}} \
          (E ∩ (zdGraph 2).edgeSet))ᶜ) ∩ {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆ ω ∪ E := by
    rintro lo' hi' hX e ⟨he | he, heX⟩
    · exact Or.inl he
    · right
      by_contra hE
      refine he ⟨fun x hx => ?_, fun h' => hE h'.1⟩
      have := hX x (heX x hx)
      simp only [mem_ofPred_eq]
      omega
  refine ⟨mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2.1,
    mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Same colour, dual exploration.** The fresh dual strips at `z` uncrossed give the hypotheses
of `lt_sub_of_exploration` for the exploration of the dual configuration. -/
theorem notMem_crossing_dualConfig_sdiff_of (B : Set (Sym2 (LatticeSite 2)))
    (h : dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))ᶜ) ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))ᶜ) ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))ᶜ) ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s])) :
    (dualConfig ω \ E) ∩ B ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    (dualConfig ω \ E) ∩ B ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    (dualConfig ω \ E) ∩ B ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s ≤ x 1)) →
      (dualConfig ω \ E) ∩ B ∩ {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
          z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
          (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
            z 1 + s ≤ x 1 + 2)}} \
          (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))ᶜ) :=
    fun lo' hi' hX =>
    dualConfig_sdiff_inter_subset (fun f hf x h₁ h₂ h₃ h₄ => by
      have := hX f hf
      simp only [mem_ofPred_eq]
      omega) B
  refine ⟨notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Fence, dual exploration.** The fresh dual circuit of faces at `z` gives the hypotheses of
`exists_fence_of_exploration` for the exploration of the dual configuration. -/
theorem mem_crossing_dualConfig_union_of
    (h : dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))) ∈
      crossing 0 (z + ![-3 * (s : ℤ), s + 1]) (z + ![3 * (s : ℤ) + 1, 3 * s]) ∧
    dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))) ∈
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s + 1]) (z + ![3 * (s : ℤ) + 1, -s]) ∧
    dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))) ∈
      crossing 1 (z + ![(s : ℤ) + 1, -3 * s]) (z + ![3 * (s : ℤ), 3 * s + 1]) ∧
    dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))) ∈
      crossing 1 (z + ![-3 * (s : ℤ) + 1, -3 * s]) (z + ![-(s : ℤ), 3 * s + 1])) :
    dualConfig ω ∪ E ∈
      crossing 0 (z + ![-3 * (s : ℤ), s + 1]) (z + ![3 * (s : ℤ) + 1, 3 * s]) ∧
    dualConfig ω ∪ E ∈
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s + 1]) (z + ![3 * (s : ℤ) + 1, -s]) ∧
    dualConfig ω ∪ E ∈
      crossing 1 (z + ![(s : ℤ) + 1, -3 * s]) (z + ![3 * (s : ℤ), 3 * s + 1]) ∧
    dualConfig ω ∪ E ∈
      crossing 1 (z + ![-3 * (s : ℤ) + 1, -3 * s]) (z + ![-(s : ℤ), 3 * s + 1]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s + 1 ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s + 1 ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s + 1 ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s + 1 ≤ x 1)) →
      dualConfig (ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
          z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
          (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
            z 1 + s ≤ x 1 + 2)}} \
          (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet))) ∩
        {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆ dualConfig ω ∪ E :=
    fun lo' hi' hX => dualConfig_inter_inter_subset (fun f hf x h₁ h₂ h₃ h₄ => by
      have := hX f hf
      simp only [mem_ofPred_eq]
      omega)
  refine ⟨mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2.1,
    mem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Corner, open.** The open strips at `z` uncrossed by the pairs of the annulus give the
hypotheses of `false_of_le_add_corner_right` and `false_of_le_add_corner_left`. -/
theorem notMem_crossing_inter_of (B : Set (Sym2 (LatticeSite 2)))
    (h : ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}} ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s])) :
    ω ∩ B ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    ω ∩ B ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    ω ∩ B ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s ≤ x 1)) →
      ω ∩ B ∩ {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆ ω ∩ {e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
          z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
          (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
            z 1 + s ≤ x 1 + 2)}} := by
    rintro lo' hi' hX e ⟨⟨heω, -⟩, heX⟩
    refine ⟨heω, fun x hx => ?_⟩
    have := hX x (heX x hx)
    simp only [mem_ofPred_eq]
    omega
  refine ⟨notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Corner, dual.** The dual strips at `z` uncrossed, with the pairs outside the annulus open,
give the corner hypotheses for the exploration of the dual configuration. -/
theorem notMem_crossing_dualConfig_inter_of (B : Set (Sym2 (LatticeSite 2)))
    (h : dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}})ᶜ) ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}})ᶜ) ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)}})ᶜ) ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s])) :
    dualConfig ω ∩ B ∉
      crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]) ∧
    dualConfig ω ∩ B ∉
      crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]) ∧
    dualConfig ω ∩ B ∉
      crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (z + ![a, b]) (z + ![a', b']),
      z 0 + a ≤ x 0 ∧ x 0 ≤ z 0 + a' ∧ z 1 + b ≤ x 1 ∧ x 1 ≤ z 1 + b' := fun a b a' b' x hx => by
    have := mem_Icc_two_iff.1 hx
    simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ lo' hi' : LatticeSite 2, (∀ x ∈ Icc lo' hi', z 0 - 3 * s ≤ x 0 ∧
      x 0 ≤ z 0 + 3 * s ∧ z 1 - 3 * s ≤ x 1 ∧ x 1 ≤ z 1 + 3 * s ∧
      (x 0 ≤ z 0 - s ∨ z 0 + s ≤ x 0 ∨ x 1 ≤ z 1 - s ∨ z 1 + s ≤ x 1)) →
      dualConfig ω ∩ B ∩ {e | ∀ x ∈ e, x ∈ Icc lo' hi'} ⊆
        dualConfig (ω ∪ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
          z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
          (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
            z 1 + s ≤ x 1 + 2)}})ᶜ) := by
    intro lo' hi' hX
    have := dualConfig_sdiff_inter_subset (ω := ω) (E := ∅) (R := {x : LatticeSite 2 |
      z 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ z 0 + (3 * s + 2) ∧
      z 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ z 1 + (3 * s + 2) ∧
      (x 0 + s ≤ z 0 + 2 ∨ z 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ z 1 + 2 ∨
        z 1 + s ≤ x 1 + 2)})
      (S := Icc lo' hi') (fun f hf x h₁ h₂ h₃ h₄ => by
        have := hX f hf
        simp only [mem_ofPred_eq]
        omega) B
    simpa only [sdiff_empty, empty_inter, image_empty] using this
  refine ⟨notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.1,
    notMem_crossing_of_inter_subset (key _ _ fun x hx => ?_) h.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    omega

/-- **Other colour, dual exploration.** The fresh open strips at `y + (1, 1)` uncrossed give the
hypotheses of `false_of_localConn_of_exploration` at `y` for the exploration of the dual
configuration, whose dual configuration is `ω` moved by `(-1, -1)`. -/
theorem notMem_crossing_dualConfig_dualConfig_union_of (y : LatticeSite 2)
    (B : Set (Sym2 (LatticeSite 2)))
    (h : ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      (y + 1) 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ (y + 1) 0 + (3 * s + 2) ∧
      (y + 1) 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ (y + 1) 1 + (3 * s + 2) ∧
      (x 0 + s ≤ (y + 1) 0 + 2 ∨ (y + 1) 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ (y + 1) 1 + 2 ∨
        (y + 1) 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet)) ∉
      crossing 1 ((y + 1) + ![-3 * (s : ℤ), -3 * s]) ((y + 1) + ![3 * (s : ℤ), -s]) ∧
    ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      (y + 1) 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ (y + 1) 0 + (3 * s + 2) ∧
      (y + 1) 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ (y + 1) 1 + (3 * s + 2) ∧
      (x 0 + s ≤ (y + 1) 0 + 2 ∨ (y + 1) 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ (y + 1) 1 + 2 ∨
        (y + 1) 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet)) ∉
      crossing 0 ((y + 1) + ![(s : ℤ), -3 * s]) ((y + 1) + ![3 * (s : ℤ), 3 * s]) ∧
    ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
      (y + 1) 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ (y + 1) 0 + (3 * s + 2) ∧
      (y + 1) 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ (y + 1) 1 + (3 * s + 2) ∧
      (x 0 + s ≤ (y + 1) 0 + 2 ∨ (y + 1) 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ (y + 1) 1 + 2 ∨
        (y + 1) 1 + s ≤ x 1 + 2)}} \
      (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet)) ∉
      crossing 0 ((y + 1) + ![-3 * (s : ℤ), -3 * s]) ((y + 1) + ![-(s : ℤ), 3 * s])) :
    dualConfig (dualConfig ω ∪ E) ∩ B ∉
      crossing 1 (y + ![-3 * (s : ℤ), -3 * s]) (y + ![3 * (s : ℤ), -s]) ∧
    dualConfig (dualConfig ω ∪ E) ∩ B ∉
      crossing 0 (y + ![(s : ℤ), -3 * s]) (y + ![3 * (s : ℤ), 3 * s]) ∧
    dualConfig (dualConfig ω ∪ E) ∩ B ∉
      crossing 0 (y + ![-3 * (s : ℤ), -3 * s]) (y + ![-(s : ℤ), 3 * s]) := by
  have hbox : ∀ a b a' b' : ℤ, ∀ x ∈ Icc (y + 1 + ![a, b]) (y + 1 + ![a', b']),
      y 0 + 1 + a ≤ x 0 ∧ x 0 ≤ y 0 + 1 + a' ∧ y 1 + 1 + b ≤ x 1 ∧ x 1 ≤ y 1 + 1 + b' :=
    fun a b a' b' x hx => by
      have := mem_Icc_two_iff.1 hx
      simpa only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using this
  have key : ∀ (i : Fin 2) (a b a' b' : ℤ), (∀ x ∈ Icc (y + 1 + ![a, b]) (y + 1 + ![a', b']),
      x ∈ {x : LatticeSite 2 |
          (y + 1) 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ (y + 1) 0 + (3 * s + 2) ∧
          (y + 1) 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ (y + 1) 1 + (3 * s + 2) ∧
          (x 0 + s ≤ (y + 1) 0 + 2 ∨ (y + 1) 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ (y + 1) 1 + 2 ∨
            (y + 1) 1 + s ≤ x 1 + 2)}) →
      ω ∩ ({e | ∀ x ∈ e, x ∈ {x : LatticeSite 2 |
          (y + 1) 0 - (3 * s + 2) ≤ x 0 ∧ x 0 ≤ (y + 1) 0 + (3 * s + 2) ∧
          (y + 1) 1 - (3 * s + 2) ≤ x 1 ∧ x 1 ≤ (y + 1) 1 + (3 * s + 2) ∧
          (x 0 + s ≤ (y + 1) 0 + 2 ∨ (y + 1) 0 + s ≤ x 0 + 2 ∨ x 1 + s ≤ (y + 1) 1 + 2 ∨
            (y + 1) 1 + s ≤ x 1 + 2)}} \
          (fun p => Sym2.map (· + 1) (dualEdge p)) '' (E ∩ (zdGraph 2).edgeSet)) ∉
        crossing i (y + 1 + ![a, b]) (y + 1 + ![a', b']) →
      dualConfig (dualConfig ω ∪ E) ∩ B ∉ crossing i (y + ![a, b]) (y + ![a', b']) := by
    intro i a b a' b' hX hn hζ
    refine hn (mem_crossing_of_inter_subset (fun e ⟨he, heX⟩ =>
      image_dualConfig_union_inter_subset B ⟨he, fun x hx => hX x (heX x hx)⟩) ?_)
    have := (image_add_mem_crossing_iff 1 i _ _ _).2 hζ
    rwa [add_right_comm y ![a, b] 1, add_right_comm y ![a', b'] 1] at this
  refine ⟨key 1 _ _ _ _ (fun x hx => ?_) h.1, key 0 _ _ _ _ (fun x hx => ?_) h.2.1,
    key 0 _ _ _ _ (fun x hx => ?_) h.2.2⟩ <;>
  · have := hbox _ _ _ _ x hx
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.one_apply]
    omega

end Unpack

end PercLib.Models.Planar
