/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4: Proposition 14, upper half (p. 1578), and Lemma 15,
first step of the proof (p. 1579).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import PercLib.Models.Planar.Arms.MultiArmBasics
public import PercLib.Models.Planar.CriticalProbability
public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Probability.LocallyMonotone

/-!
# Bounds on crossing and multi-arm events

Consequences of crossing bounds of both colours (`CrossingBounds q L c`) for families of
disjoint crossings and for multi-arm events on the square lattice.

* **Crossings in the short direction.** By planar duality a box of `ℤ²` is crossed by open
  edges from bottom to top exactly when the matching box of faces is not crossed by dual-open
  edges from left to right. For a box of width `k n` and height `n + 1` that box of faces is a
  little wider than `k n` and of height `n`, so it is crossed from left to right with
  probability at least `c (k + 1)`. Hence the box is crossed from bottom to top with probability
  at most `1 - c (k + 1)`. The same holds for dual-open crossings, and for left-right crossings
  of boxes of width `n + 1` and height `k n`.
* **Geometric tail of the number of disjoint crossings** (first step of Nolin's Lemma 15). By BK,
  for increasing events and, after complementing configurations, for decreasing ones, `h`
  disjoint occurrences of such a crossing have probability at most `(1 - c (k + 1))^h`.
  A family of `h` walks along open (or dual-open) edges crossing the box, with pairwise disjoint
  sets of edges, gives `h` disjoint occurrences of the crossing event.
* **A priori upper bound for multi-arm events** (Nolin, Proposition 14, upper half). An open arm
  from `B_r(0)` to the boundary of `B_R(0)` crosses every annulus `t ≤ ‖·‖∞ ≤ 3t` with
  `r ≤ t`, `3t ≤ R`, so it is blocked when the four strips around the annulus have no open
  crossing in their short direction, that is when they carry a dual circuit; a dual arm is
  blocked by an open circuit made of four open crossings of boxes in their long direction.
  Under crossing bounds each circuit has probability at least `c 7 ^ 4` (Harris), and the
  circuits at the scales `(r + 2) 4^i` are independent. So a multi-arm event with an arm of a
  given colour has probability at most `C ((r + 1) / (R + 1))^a`, with `C` and `a > 0` depending
  only on `c`, uniformly in the law, the centre and the radii up to `L`.

## Main results

* `law_crossing_one_le_one_sub`, `law_crossing_zero_le_one_sub`,
  `law_dualConfig_crossing_one_le_one_sub`, `law_dualConfig_crossing_zero_le_one_sub`: crossings
  in the short direction, of both colours, have probability at most `1 - c (k + 1)`.
* `law_foldl_crossing_one_le_pow`, `law_foldl_crossing_zero_le_pow`,
  `law_foldl_dualConfig_crossing_one_le_pow`, `law_foldl_dualConfig_crossing_zero_le_pow`: `h`
  disjoint such crossings have probability at most `(1 - c (k + 1))^h`.
* `mem_foldl_crossing_of_walks`, `mem_foldl_dualConfig_crossing_of_walks`: `h` crossing walks
  with pairwise disjoint sets of edges give `h` disjoint occurrences of the crossing event.
* `CrossingBounds.le_law_crossing_zero_of_le` and its three companions: crossing bounds for
  boxes of other shapes.
* `notMem_multiArmEvent_of_notMem_crossing`, `notMem_multiArmEvent_of_mem_crossing`: circuits
  of the other colour block arms; `law_le_one_sub_pow_of_blocking`: blocking at many
  independent scales.
* `law_multiArmEvent_zero_le_one_sub_pow`: the bound `(1 - c 7 ^ 4)^N` at the origin;
  `exists_law_multiArmEvent_le_rpow`: **the a priori upper bound**, for both colours.
* `law_translate_apply`: the law seen from another centre.

## Implementation notes

* The a priori bound needs no relation between `r` and `R`: for `R < 3 (r + 2)` there is no
  scale and the bound is at least `1`.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Families of crossing walks -/

/-- A walk along open edges inside a box from its face `{v | v i = lo i}` to its face
`{v | v i = hi i}` makes the box crossed in direction `i`. -/
theorem mem_crossing_of_walk {d : ℕ} {i : Fin d} {lo hi a b : LatticeSite d}
    {ω : Config (LatticeSite d)} (γ : (zdGraph d).Walk a b) (ha : a i = lo i) (hb : b i = hi i)
    (hs : ∀ v ∈ γ.support, v ∈ Icc lo hi) (hω : ∀ e ∈ γ.edges, e ∈ ω) :
    ω ∈ crossing i lo hi :=
  ⟨a, hs a γ.start_mem_support, ha, b, hs b γ.end_mem_support, hb, mem_localConn_of_walk γ hs hω⟩

/-- **Disjoint open crossings.** `h` walks along open edges, each crossing the box `Icc lo hi`
in direction `i`, with pairwise disjoint sets of edges, give `h` disjoint occurrences of the
crossing event. -/
theorem mem_foldl_crossing_of_walks {d : ℕ} {i : Fin d} {lo hi : LatticeSite d}
    {ω : Config (LatticeSite d)} {h : ℕ} {a b : Fin h → LatticeSite d}
    (γ : ∀ j, (zdGraph d).Walk (a j) (b j)) (ha : ∀ j, a j i = lo i) (hb : ∀ j, b j i = hi i)
    (hs : ∀ j, ∀ v ∈ (γ j).support, v ∈ Icc lo hi) (hω : ∀ j, ∀ e ∈ (γ j).edges, e ∈ ω)
    (hd : Pairwise fun j l => ∀ e ∈ (γ j).edges, e ∉ (γ l).edges) :
    ω ∈ (List.replicate h (crossing i lo hi)).foldl disjointOccurrence univ :=
  mem_foldl_replicate_disjointOccurrence (isUpperSet_crossing i lo hi) h isUpperSet_univ ∅
    (fun j => {e | e ∈ (γ j).edges}) finite_empty (fun j => (γ j).edges.finite_toSet)
    (empty_subset _) (fun j e he => hω j e he) (mem_univ _)
    (fun j => mem_crossing_of_walk (γ j) (ha j) (hb j) (hs j) fun _ he => he)
    (fun _ => empty_disjoint _) fun _ _ hjl => disjoint_left.2 fun e hej hel => hd hjl e hej hel

/-- The edge of `ℤ²` crossed by the dual edge `f`. -/
theorem dualEdge_map_add_one_dualEdge {f : Sym2 (LatticeSite 2)}
    (hf : f ∈ (zdGraph 2).edgeSet) : dualEdge (Sym2.map (· + 1) (dualEdge f)) = f :=
  congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨f, hf⟩)

/-- **Disjoint dual-open crossings.** `h` walks of faces along dual-open edges, each crossing
the box of faces `Icc lo hi` in direction `i`, with pairwise disjoint sets of dual edges, give
`h` disjoint occurrences of the dual crossing event. The certificates are the closed edges of
`ℤ²` crossed by the walks. -/
theorem mem_foldl_dualConfig_crossing_of_walks {i : Fin 2} {lo hi : LatticeSite 2}
    {ω : Config (LatticeSite 2)} {h : ℕ} {a b : Fin h → LatticeSite 2}
    (γ : ∀ j, (zdGraph 2).Walk (a j) (b j)) (ha : ∀ j, a j i = lo i) (hb : ∀ j, b j i = hi i)
    (hs : ∀ j, ∀ v ∈ (γ j).support, v ∈ Icc lo hi)
    (hω : ∀ j, ∀ e ∈ (γ j).edges, e ∈ dualConfig ω)
    (hd : Pairwise fun j l => ∀ e ∈ (γ j).edges, e ∉ (γ l).edges) :
    ω ∈ (List.replicate h (dualConfig ⁻¹' crossing i lo hi)).foldl disjointOccurrence univ := by
  set G : Fin h → Set (Sym2 (LatticeSite 2)) :=
    fun j => {e | e ∈ (zdGraph 2).edgeSet ∧ dualEdge e ∈ (γ j).edges} with hG
  have hGf : ∀ j, (G j).Finite := fun j =>
    (((γ j).edges.finite_toSet).image fun f => Sym2.map (· + 1) (dualEdge f)).subset
      fun e ⟨he, hej⟩ => ⟨dualEdge e, hej, map_add_one_dualEdge_dualEdge he⟩
  have hGω : ∀ j, G j ⊆ ωᶜ := fun j e ⟨he, hej⟩ =>
    (dualEdge_mem_dualConfig_iff he).1 (hω j _ hej)
  have hGB : ∀ j, G j ∈ compl ⁻¹' (dualConfig ⁻¹' crossing i lo hi) := by
    intro j
    refine mem_crossing_of_walk (γ j) (ha j) (hb j) (hs j) fun f hf => ?_
    have hfE := (γ j).edges_subset_edgeSet hf
    refine (mem_dualConfig_iff _ f).2 ⟨hfE, not_not.2 ?_⟩
    exact ⟨map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hfE), by
      rw [dualEdge_map_add_one_dualEdge hfE]; exact hf⟩
  have hGd : Pairwise fun j l => Disjoint (G j) (G l) := fun j l hjl =>
    disjoint_left.2 fun e ⟨_, hej⟩ ⟨_, hel⟩ => hd hjl _ hej hel
  have key := mem_foldl_replicate_disjointOccurrence
    (B := compl ⁻¹' (dualConfig ⁻¹' crossing i lo hi))
    (fun _ _ hab hx => crossing_mono (dualConfig_anti (compl_le_compl hab)) hx) h
    isUpperSet_univ ∅ G finite_empty hGf (empty_subset _) hGω (mem_univ _) hGB
    (fun _ => empty_disjoint _) hGd
  have hc := preimage_compl_foldl_disjointOccurrence
    (List.replicate h (dualConfig ⁻¹' crossing i lo hi)) univ
  rw [List.map_replicate, preimage_univ] at hc
  rw [← hc] at key
  simpa only [mem_preimage, compl_compl] using key

/-! ### Crossings in the short direction -/

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- An event containing a measurable event of probability at least `c` has a complement of
probability at most `1 - c`. -/
theorem law_le_one_sub_of_subset_compl {A B : Set (Config (LatticeSite 2))}
    (hA : MeasurableSet A) (hBA : B ⊆ Aᶜ) {t : ℝ≥0∞} (ht : t ≤ law q B) :
    law q A ≤ 1 - t := by
  rw [← compl_compl A, MeasureTheory.prob_compl_eq_one_sub hA.compl]
  exact tsub_le_tsub_left (ht.trans (MeasureTheory.measure_mono hBA)) 1

/-- **Open bottom-top crossings of a wide box.** Under crossing bounds up to scale `L`, the box of
width `k n` and height `n + 1` is crossed from bottom to top with probability at most
`1 - c (k + 1)`, for `1 ≤ n ≤ L`: its complement contains a dual-open left-right crossing of a
box of faces of size `(k + 1) n × n`. -/
theorem law_crossing_one_le_one_sub (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    law q (crossing 1 lo (lo + ![(k : ℤ) * n, n + 1])) ≤ 1 - c (k + 1) := by
  have hle : lo ≤ lo + ![(k : ℤ) * n, n + 1] := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> nlinarith
  refine law_le_one_sub_of_subset_compl (measurableSet_crossing _ _ _) ?_
    (h.le_law_dualConfig_crossing_zero (k + 1) (lo + ![-1, 0]) hn hnL)
  rw [compl_crossing_one_eq_preimage_dualConfig hle]
  refine preimage_mono (crossing_zero_subset_crossing_zero ?_ ?_ ?_ ?_ ?_) <;>
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> push_cast <;> nlinarith

/-- **Open left-right crossings of a tall box.** The box of width `n + 1` and height `k n` is
crossed from left to right with probability at most `1 - c (k + 1)`. -/
theorem law_crossing_zero_le_one_sub (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    law q (crossing 0 lo (lo + ![(n : ℤ) + 1, k * n])) ≤ 1 - c (k + 1) := by
  have hle : lo ≤ lo + ![(n : ℤ) + 1, k * n] := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> nlinarith
  refine law_le_one_sub_of_subset_compl (measurableSet_crossing _ _ _) ?_
    (h.le_law_dualConfig_crossing_one (k + 1) (lo + ![0, -1]) hn hnL)
  rw [crossing_zero_eq_compl_preimage_dualConfig hle, compl_compl]
  refine preimage_mono (crossing_one_subset_crossing_one ?_ ?_ ?_ ?_ ?_) <;>
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> push_cast <;> nlinarith

/-- **Dual-open bottom-top crossings of a wide box of faces.** The box of faces of width `k n`
and height `n + 1` is crossed from bottom to top by dual-open edges with probability at most
`1 - c (k + 1)`: such a crossing blocks every open left-right crossing of a box of size
`(k n + 1) × n`. -/
theorem law_dualConfig_crossing_one_le_one_sub (h : CrossingBounds q L c) (k : ℕ)
    (lo : LatticeSite 2) {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    law q (dualConfig ⁻¹' crossing 1 lo (lo + ![(k : ℤ) * n, n + 1])) ≤ 1 - c (k + 1) := by
  set a : LatticeSite 2 := ![lo 0, lo 1 + 1]
  set b : LatticeSite 2 := ![lo 0 + k * n + 1, lo 1 + n + 1]
  have hab : a ≤ b := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [a, b, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> nlinarith
  have hlo : (![a 0, a 1 - 1] : LatticeSite 2) = lo := by
    rw [eq_vec_two lo]; simp [a]
  have hhi : (![b 0 - 1, b 1] : LatticeSite 2) = lo + ![(k : ℤ) * n, n + 1] := by
    ext j; fin_cases j
    · simp [b]
    · simp [b]; ring
  refine law_le_one_sub_of_subset_compl
    (measurable_dualConfig (measurableSet_crossing _ _ _)) ?_
    (h.le_law_crossing_zero (k + 1) a hn hnL)
  intro ω hω hdual
  have := (mem_crossing_zero_iff_dualConfig_notMem_crossing_one hab ω).1
    (crossing_zero_subset_crossing_zero (lo := a) (hi := a + ![((k + 1 : ℕ) : ℤ) * n, n])
      (lo' := a) (hi' := b) le_rfl
      (by simp only [a, b, Matrix.cons_val_zero]; nlinarith)
      (by simp only [a, b, Pi.add_apply, Matrix.cons_val_zero]; push_cast; nlinarith)
      le_rfl
      (by simp only [a, b, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega) hω)
  rw [hlo, hhi] at this
  exact this hdual

/-- **Dual-open left-right crossings of a tall box of faces.** The box of faces of width `n + 1`
and height `k n` is crossed from left to right by dual-open edges with probability at most
`1 - c (k + 1)`. -/
theorem law_dualConfig_crossing_zero_le_one_sub (h : CrossingBounds q L c) (k : ℕ)
    (lo : LatticeSite 2) {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) :
    law q (dualConfig ⁻¹' crossing 0 lo (lo + ![(n : ℤ) + 1, k * n])) ≤ 1 - c (k + 1) := by
  set a : LatticeSite 2 := ![lo 0 + 1, lo 1]
  set b : LatticeSite 2 := ![lo 0 + n + 1, lo 1 + k * n + 1]
  have hab : a ≤ b := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [a, b, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> nlinarith
  have hlo : (![a 0 - 1, a 1] : LatticeSite 2) = lo := by
    rw [eq_vec_two lo]; simp [a]
  have hhi : (![b 0, b 1 - 1] : LatticeSite 2) = lo + ![(n : ℤ) + 1, k * n] := by
    ext j; fin_cases j
    · simp [b]; ring
    · simp [b]
  refine law_le_one_sub_of_subset_compl
    (measurable_dualConfig (measurableSet_crossing _ _ _)) ?_
    (h.le_law_crossing_one (k + 1) a hn hnL)
  intro ω hω hdual
  have := (mem_crossing_one_iff_dualConfig_notMem_crossing_zero hab ω).1
    (crossing_one_subset_crossing_one (lo := a) (hi := a + ![(n : ℤ), ((k + 1 : ℕ) : ℤ) * n])
      (lo' := a) (hi' := b) le_rfl
      (by simp only [a, b, Matrix.cons_val_one, Matrix.cons_val_zero]; nlinarith)
      (by simp only [a, b, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
          nlinarith)
      le_rfl
      (by simp only [a, b, Pi.add_apply, Matrix.cons_val_zero]; omega) hω)
  rw [hlo, hhi] at this
  exact this hdual

/-! ### Crossing bounds for boxes of other shapes -/

namespace CrossingBounds

/-- **Left-right crossings of short wide boxes.** A box at most `k m` wide and at least `m` tall
is crossed from left to right with probability at least `c k`. -/
theorem le_law_crossing_zero_of_le (h : CrossingBounds q L c) (k : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (hmL : (m : ℕ∞) ≤ L) {lo hi : LatticeSite 2} (h₀ : lo 0 ≤ hi 0)
    (h₀' : hi 0 ≤ lo 0 + k * m) (h₁ : lo 1 + m ≤ hi 1) :
    c k ≤ law q (crossing 0 lo hi) :=
  (h.le_law_crossing_zero k lo hm hmL).trans <| MeasureTheory.measure_mono <|
    crossing_zero_subset_crossing_zero le_rfl h₀ (by simpa using h₀') le_rfl (by simpa using h₁)

/-- **Bottom-top crossings of narrow tall boxes.** A box at least `m` wide and at most `k m`
tall is crossed from bottom to top with probability at least `c k`. -/
theorem le_law_crossing_one_of_le (h : CrossingBounds q L c) (k : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (hmL : (m : ℕ∞) ≤ L) {lo hi : LatticeSite 2} (h₁ : lo 1 ≤ hi 1)
    (h₁' : hi 1 ≤ lo 1 + k * m) (h₀ : lo 0 + m ≤ hi 0) :
    c k ≤ law q (crossing 1 lo hi) :=
  (h.le_law_crossing_one k lo hm hmL).trans <| MeasureTheory.measure_mono <|
    crossing_one_subset_crossing_one le_rfl h₁ (by simpa using h₁') le_rfl (by simpa using h₀)

/-- **Dual left-right crossings of short wide boxes of faces.** -/
theorem le_law_dualConfig_crossing_zero_of_le (h : CrossingBounds q L c) (k : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (hmL : (m : ℕ∞) ≤ L) {lo hi : LatticeSite 2} (h₀ : lo 0 ≤ hi 0)
    (h₀' : hi 0 ≤ lo 0 + k * m) (h₁ : lo 1 + m ≤ hi 1) :
    c k ≤ law q (dualConfig ⁻¹' crossing 0 lo hi) :=
  (h.le_law_dualConfig_crossing_zero k lo hm hmL).trans <| MeasureTheory.measure_mono <|
    preimage_mono <|
      crossing_zero_subset_crossing_zero le_rfl h₀ (by simpa using h₀') le_rfl (by simpa using h₁)

/-- **Dual bottom-top crossings of narrow tall boxes of faces.** -/
theorem le_law_dualConfig_crossing_one_of_le (h : CrossingBounds q L c) (k : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (hmL : (m : ℕ∞) ≤ L) {lo hi : LatticeSite 2} (h₁ : lo 1 ≤ hi 1)
    (h₁' : hi 1 ≤ lo 1 + k * m) (h₀ : lo 0 + m ≤ hi 0) :
    c k ≤ law q (dualConfig ⁻¹' crossing 1 lo hi) :=
  (h.le_law_dualConfig_crossing_one k lo hm hmL).trans <| MeasureTheory.measure_mono <|
    preimage_mono <|
      crossing_one_subset_crossing_one le_rfl h₁ (by simpa using h₁') le_rfl (by simpa using h₀)

end CrossingBounds

/-! ### Blocking arms at many scales -/

/-- The annulus `t ≤ ‖v‖∞ ≤ 3t + 1` (in the coordinates of the upper right corner), which
contains the four strips of `notMem_localConn_of_notMem_crossing` at scale `t` and the four
boxes of the matching open circuit. -/
theorem mem_blockingAnnulus_of_mem_Icc {t : ℕ} {lo hi v : LatticeSite 2} (hv : v ∈ Icc lo hi)
    (hbox : -(3 * (t : ℤ)) ≤ lo 0 ∧ hi 0 ≤ 3 * t + 1 ∧ -(3 * (t : ℤ)) ≤ lo 1 ∧
      hi 1 ≤ 3 * t + 1)
    (hout : (t : ℤ) ≤ lo 0 ∨ hi 0 ≤ -t ∨ (t : ℤ) ≤ lo 1 ∨ hi 1 ≤ -t) :
    ((t : ℤ) ≤ v 0 ∨ v 0 ≤ -t ∨ (t : ℤ) ≤ v 1 ∨ v 1 ≤ -t) ∧
      -(3 * (t : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * t + 1 ∧ -(3 * (t : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * t + 1 := by
  rw [mem_Icc_two_iff] at hv
  omega

/-- **Blocking at many scales.** If an event `E` misses the blocking events `K (s j)`, `j < N`,
each of probability at least `β` and determined by the edges inside `D (s j)`, with the sets
`D (s j)` pairwise disjoint, then `E` has probability at most `(1 - β)^N`. -/
theorem law_le_one_sub_pow_of_blocking {E : Set (Config (LatticeSite 2))}
    {K : ℕ → Set (Config (LatticeSite 2))} {D : ℕ → Set (LatticeSite 2)} {s : ℕ → ℕ} {N : ℕ}
    {β : ℝ≥0∞} (hK : ∀ j < N, β ≤ law q (K (s j))) (hKm : ∀ j, MeasurableSet (K (s j)))
    (hKD : ∀ j, ∀ ω ω' : Config (LatticeSite 2),
      ω ∩ {e | ∀ v ∈ e, v ∈ D (s j)} = ω' ∩ {e | ∀ v ∈ e, v ∈ D (s j)} →
        (ω ∈ K (s j) ↔ ω' ∈ K (s j)))
    (hD : Set.PairwiseDisjoint (↑(Finset.range N)) fun j => D (s j))
    (hE : ∀ j < N, E ⊆ (K (s j))ᶜ) :
    law q E ≤ (1 - β) ^ N := by
  have hsub : E ⊆ ⋂ j ∈ Finset.range N, (K (s j))ᶜ := fun ω hω =>
    mem_iInter₂.2 fun j hj => hE j (Finset.mem_range.1 hj) hω
  calc law q E ≤ law q (⋂ j ∈ Finset.range N, (K (s j))ᶜ) := MeasureTheory.measure_mono hsub
    _ = ∏ j ∈ Finset.range N, law q (K (s j))ᶜ :=
        law_biInter_of_determined_internalPairs q (Finset.range N) hD
          (fun j _ => (hKm j).compl) fun j ω ω' h => not_congr (hKD j ω ω' h)
    _ ≤ (1 - β) ^ (Finset.range N).card := by
        refine Finset.prod_le_pow_card _ _ _ fun j hj => ?_
        rw [MeasureTheory.prob_compl_eq_one_sub (hKm j)]
        exact tsub_le_tsub_left (hK j (Finset.mem_range.1 hj)) 1
    _ = (1 - β) ^ N := by rw [Finset.card_range]

/-- **Open arms are blocked by dual circuits.** If none of the four strips around the annulus
`t ≤ ‖·‖∞ ≤ 3t` has an open crossing in its short direction, there is no open arm from `B_r(0)`
to the boundary of `B_R(0)` for `r ≤ t` and `3t ≤ R`. -/
theorem notMem_multiArmEvent_of_notMem_crossing {j : ℕ} {σ : Fin j → Bool}
    (hσ : ∃ i, σ i = true) {ω : Config (LatticeSite 2)} {r t R : ℕ}
    (hT : ω ∉ crossing 1 ![-3 * (t : ℤ), t] ![3 * t, 3 * t])
    (hB : ω ∉ crossing 1 ![-3 * (t : ℤ), -3 * t] ![3 * t, -t])
    (hR : ω ∉ crossing 0 ![(t : ℤ), -3 * t] ![3 * t, 3 * t])
    (hL : ω ∉ crossing 0 ![-3 * (t : ℤ), -3 * t] ![-t, 3 * t]) (hrt : r ≤ t) (htR : 3 * t ≤ R) :
    ω ∉ multiArmEvent σ 0 r R := by
  intro hω
  obtain ⟨a, b, γ, hγ, -, -⟩ := mem_multiArmEvent_iff.1 hω
  obtain ⟨i, hi⟩ := hσ
  have hγi : IsOpenArm ω 0 r (0 - R) (0 + R) (γ i) := by
    have := hγ i
    rw [hi] at this
    exact this
  have ha := hγi.isCrossing.start_mem
  have hb := hγi.isCrossing.end_notMem
  refine notMem_localConn_of_notMem_crossing hT hB hR hL (a := a i) (v := b i) ?_ ?_ univ
    (mem_localConn_of_walk (γ i) (fun _ _ => mem_univ _) hγi.mem_of_mem_edges)
  · simp [mem_Icc_two_iff, -mem_Icc] at ha
    exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
  · simp [mem_Icc_two_iff, -mem_Icc] at hb
    rw [le_abs, le_abs]
    omega

/-- **Dual arms are blocked by open circuits.** If the four boxes around the annulus
`t ≤ ‖·‖∞ ≤ 3t + 1` are crossed by open edges in their long direction, there is no dual arm from
`B_r(0)` to the boundary of `B_R(0)` for `r < t` and `3t ≤ R`: the four open crossings block
every dual-open crossing of the four strips of faces in their short direction. -/
theorem notMem_multiArmEvent_of_mem_crossing {j : ℕ} {σ : Fin j → Bool}
    (hσ : ∃ i, σ i = false) {ω : Config (LatticeSite 2)} {r t R : ℕ}
    (hT : ω ∈ crossing 0 ![-3 * (t : ℤ), t + 1] ![3 * t + 1, 3 * t])
    (hB : ω ∈ crossing 0 ![-3 * (t : ℤ), -3 * t + 1] ![3 * t + 1, -t])
    (hR : ω ∈ crossing 1 ![(t : ℤ) + 1, -3 * t] ![3 * t, 3 * t + 1])
    (hL : ω ∈ crossing 1 ![-3 * (t : ℤ) + 1, -3 * t] ![-t, 3 * t + 1]) (hrt : r < t)
    (htR : 3 * t ≤ R) :
    ω ∉ multiArmEvent σ 0 r R := by
  intro hω
  obtain ⟨a, b, γ, hγ, -, -⟩ := mem_multiArmEvent_iff.1 hω
  obtain ⟨i, hi⟩ := hσ
  have hγi : IsDualArm ω 0 r (0 - R) (0 + R) (γ i) := by
    have := hγ i
    rw [hi] at this
    exact this
  have ha := hγi.isCrossing.start_mem
  have hb := hγi.isCrossing.end_notMem
  -- the open crossings block the dual crossings of the strips of faces
  have hT' : dualConfig ω ∉ crossing 1 ![-3 * (t : ℤ), t] ![3 * t, 3 * t] := by
    have := (mem_crossing_zero_iff_dualConfig_notMem_crossing_one (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega) ω).1 hT
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_right] using this
  have hB' : dualConfig ω ∉ crossing 1 ![-3 * (t : ℤ), -3 * t] ![3 * t, -t] := by
    have := (mem_crossing_zero_iff_dualConfig_notMem_crossing_one (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega) ω).1 hB
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_right] using this
  have hR' : dualConfig ω ∉ crossing 0 ![(t : ℤ), -3 * t] ![3 * t, 3 * t] := by
    have := (mem_crossing_one_iff_dualConfig_notMem_crossing_zero (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega) ω).1 hR
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_right] using this
  have hL' : dualConfig ω ∉ crossing 0 ![-3 * (t : ℤ), -3 * t] ![-t, 3 * t] := by
    have := (mem_crossing_one_iff_dualConfig_notMem_crossing_zero (by
      rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega) ω).1 hL
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_right] using this
  refine notMem_localConn_of_notMem_crossing hT' hB' hR' hL' (a := a i) (v := b i) ?_ ?_ univ
    (mem_localConn_of_walk (γ i) (fun _ _ => mem_univ _) hγi.mem_of_mem_edges)
  · simp [mem_Icc_two_iff, -mem_Icc] at ha
    exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
  · simp [mem_Icc_two_iff, -mem_Icc] at hb
    rw [le_abs, le_abs]
    omega

/-- The blocking annuli at the scales `(r + 2) 4^j` are pairwise disjoint. -/
theorem pairwiseDisjoint_blockingAnnulus (r N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range N)) fun j => {v : LatticeSite 2 |
      (((r + 2) * 4 ^ j : ℕ) ≤ v 0 ∨ v 0 ≤ -(((r + 2) * 4 ^ j : ℕ) : ℤ) ∨
        (((r + 2) * 4 ^ j : ℕ) : ℤ) ≤ v 1 ∨ v 1 ≤ -(((r + 2) * 4 ^ j : ℕ) : ℤ)) ∧
      -(3 * (((r + 2) * 4 ^ j : ℕ) : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * (((r + 2) * 4 ^ j : ℕ) : ℤ) + 1 ∧
      -(3 * (((r + 2) * 4 ^ j : ℕ) : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * (((r + 2) * 4 ^ j : ℕ) : ℤ) + 1} := by
  have h2 : ∀ j, 2 ≤ (r + 2) * 4 ^ j := fun j =>
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  have h4 : ∀ {j k : ℕ}, j < k → 4 * ((r + 2) * 4 ^ j) ≤ (r + 2) * 4 ^ k := by
    intro j k hjk
    calc 4 * ((r + 2) * 4 ^ j) = (r + 2) * 4 ^ (j + 1) := by ring
      _ ≤ (r + 2) * 4 ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjk)
  have hcontra : ∀ a b : ℕ, 2 ≤ a → 4 * a ≤ b → ∀ v : LatticeSite 2,
      (-(3 * (a : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * a + 1 ∧ -(3 * (a : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * a + 1) →
      ((b : ℤ) ≤ v 0 ∨ v 0 ≤ -b ∨ (b : ℤ) ≤ v 1 ∨ v 1 ≤ -b) → False := by
    intro a b ha hab v hv hb
    omega
  intro j _ k _ hjk
  rw [Function.onFun, Set.disjoint_left]
  rintro v ⟨hj, hj0, hj1, hj2, hj3⟩ ⟨hk, hk0, hk1, hk2, hk3⟩
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hcontra _ _ (h2 j) (h4 h) v ⟨hj0, hj1, hj2, hj3⟩ hk
  · exact hcontra _ _ (h2 k) (h4 h) v ⟨hk0, hk1, hk2, hk3⟩ hj

/-- **The dual circuit blocking open arms is likely.** Under crossing bounds up to `L ≥ 2t - 1`,
the four strips around the annulus `t ≤ ‖·‖∞ ≤ 3t` are all uncrossed in their short direction
with probability at least `c 7 ^ 4`: each is crossed in its long direction by dual-open edges
with probability at least `c 7`, and these events are decreasing (Harris). -/
theorem pow_le_law_compl_crossing_inter (h : CrossingBounds q L c) {t m : ℕ} (hm : 2 * t = m + 1)
    (hmL : (m : ℕ∞) ≤ L) :
    c 7 ^ 4 ≤ law q ((crossing 1 ![-3 * (t : ℤ), t] ![3 * t, 3 * t])ᶜ ∩
      (crossing 1 ![-3 * (t : ℤ), -3 * t] ![3 * t, -t])ᶜ ∩
      (crossing 0 ![(t : ℤ), -3 * t] ![3 * t, 3 * t])ᶜ ∩
      (crossing 0 ![-3 * (t : ℤ), -3 * t] ![-t, 3 * t])ᶜ) := by
  have hm1 : 1 ≤ m := by omega
  have hle : ∀ x₀ y₀ x₁ y₁ : ℤ, x₀ ≤ x₁ → y₀ ≤ y₁ → (![x₀, y₀] : LatticeSite 2) ≤ ![x₁, y₁] :=
    fun x₀ y₀ x₁ y₁ hx hy => by
      rw [Pi.le_def, Fin.forall_fin_two]; exact ⟨hx, hy⟩
  have e₁ : c 7 ≤ law q (crossing 1 ![-3 * (t : ℤ), t] ![3 * t, 3 * t])ᶜ := by
    rw [compl_crossing_one_eq_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega))]
    refine h.le_law_dualConfig_crossing_zero_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have e₂ : c 7 ≤ law q (crossing 1 ![-3 * (t : ℤ), -3 * t] ![3 * t, -t])ᶜ := by
    rw [compl_crossing_one_eq_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega))]
    refine h.le_law_dualConfig_crossing_zero_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have e₃ : c 7 ≤ law q (crossing 0 ![(t : ℤ), -3 * t] ![3 * t, 3 * t])ᶜ := by
    rw [crossing_zero_eq_compl_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega)),
      compl_compl]
    refine h.le_law_dualConfig_crossing_one_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have e₄ : c 7 ≤ law q (crossing 0 ![-3 * (t : ℤ), -3 * t] ![-t, 3 * t])ᶜ := by
    rw [crossing_zero_eq_compl_preimage_dualConfig (hle _ _ _ _ (by omega) (by omega)),
      compl_compl]
    refine h.le_law_dualConfig_crossing_one_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have hl : ∀ (i : Fin 2) (lo hi : LatticeSite 2), IsLowerSet (crossing i lo hi)ᶜ :=
    fun i lo hi => (isUpperSet_crossing i lo hi).compl
  have hmc : ∀ (i : Fin 2) (lo hi : LatticeSite 2), MeasurableSet (crossing i lo hi)ᶜ :=
    fun i lo hi => (measurableSet_crossing i lo hi).compl
  calc c 7 ^ 4 = c 7 * c 7 * c 7 * c 7 := by ring
    _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' e₁ e₂) e₃) e₄
    _ ≤ _ := mul_le_mul' (mul_le_mul' (prodBernoulli_harris_of_isLowerSet q
        (hl _ _ _) (hl _ _ _) (hmc _ _ _) (hmc _ _ _)) le_rfl) le_rfl
    _ ≤ _ := mul_le_mul' (prodBernoulli_harris_of_isLowerSet q
        ((hl _ _ _).inter (hl _ _ _)) (hl _ _ _) ((hmc _ _ _).inter (hmc _ _ _)) (hmc _ _ _)) le_rfl
    _ ≤ _ := prodBernoulli_harris_of_isLowerSet q
        (((hl _ _ _).inter (hl _ _ _)).inter (hl _ _ _)) (hl _ _ _)
        (((hmc _ _ _).inter (hmc _ _ _)).inter (hmc _ _ _)) (hmc _ _ _)

/-- **The open circuit blocking dual arms is likely.** Under crossing bounds up to `L ≥ 2t - 1`,
the four boxes around the annulus `t ≤ ‖·‖∞ ≤ 3t + 1` are all crossed in their long direction
by open edges with probability at least `c 7 ^ 4` (Harris). -/
theorem pow_le_law_crossing_inter (h : CrossingBounds q L c) {t m : ℕ} (hm : 2 * t = m + 1)
    (hmL : (m : ℕ∞) ≤ L) :
    c 7 ^ 4 ≤ law q (crossing 0 ![-3 * (t : ℤ), t + 1] ![3 * t + 1, 3 * t] ∩
      crossing 0 ![-3 * (t : ℤ), -3 * t + 1] ![3 * t + 1, -t] ∩
      crossing 1 ![(t : ℤ) + 1, -3 * t] ![3 * t, 3 * t + 1] ∩
      crossing 1 ![-3 * (t : ℤ) + 1, -3 * t] ![-t, 3 * t + 1]) := by
  have hm1 : 1 ≤ m := by omega
  have e₁ : c 7 ≤ law q (crossing 0 ![-3 * (t : ℤ), t + 1] ![3 * t + 1, 3 * t]) := by
    refine h.le_law_crossing_zero_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have e₂ : c 7 ≤ law q (crossing 0 ![-3 * (t : ℤ), -3 * t + 1] ![3 * t + 1, -t]) := by
    refine h.le_law_crossing_zero_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have e₃ : c 7 ≤ law q (crossing 1 ![(t : ℤ) + 1, -3 * t] ![3 * t, 3 * t + 1]) := by
    refine h.le_law_crossing_one_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have e₄ : c 7 ≤ law q (crossing 1 ![-3 * (t : ℤ) + 1, -3 * t] ![-t, 3 * t + 1]) := by
    refine h.le_law_crossing_one_of_le 7 hm1 hmL ?_ ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  have hu := isUpperSet_crossing (d := 2)
  have hmc := measurableSet_crossing (d := 2)
  calc c 7 ^ 4 = c 7 * c 7 * c 7 * c 7 := by ring
    _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' e₁ e₂) e₃) e₄
    _ ≤ _ := mul_le_mul' (mul_le_mul' (prodBernoulli_harris q
        (hu _ _ _) (hu _ _ _) (hmc _ _ _) (hmc _ _ _)) le_rfl) le_rfl
    _ ≤ _ := mul_le_mul' (prodBernoulli_harris q
        ((hu _ _ _).inter (hu _ _ _)) (hu _ _ _) ((hmc _ _ _).inter (hmc _ _ _)) (hmc _ _ _)) le_rfl
    _ ≤ _ := prodBernoulli_harris q
        (((hu _ _ _).inter (hu _ _ _)).inter (hu _ _ _)) (hu _ _ _)
        (((hmc _ _ _).inter (hmc _ _ _)).inter (hmc _ _ _)) (hmc _ _ _)

/-- **A priori bound at the origin.** Under crossing bounds up to `L ≥ R`, if some arm of `σ` has
colour `col`, the `j`-arm event from `B_r(0)` to the boundary of `B_R(0)` has probability at
most `(1 - c 7 ^ 4)^N` whenever the `N` scales `s = (r + 2) 4^i`, `i < N`, satisfy `3 s ≤ R`:
at each scale a circuit of the other colour around the annulus `s ≤ ‖·‖∞ ≤ 3s` blocks the arm,
and the circuits at different scales are independent. -/
theorem law_multiArmEvent_zero_le_one_sub_pow (h : CrossingBounds q L c) {j : ℕ}
    {σ : Fin j → Bool} {col : Bool} (hσ : ∃ i, σ i = col) {r R N : ℕ}
    (hN : ∀ i < N, 3 * ((r + 2) * 4 ^ i) ≤ R) (hRL : (R : ℕ∞) ≤ L) :
    law q (multiArmEvent σ 0 r R) ≤ (1 - c 7 ^ 4) ^ N := by
  have hs2 : ∀ i, r + 2 ≤ (r + 2) * 4 ^ i := fun i => Nat.le_mul_of_pos_right _ (by positivity)
  have hm : ∀ i < N, ∃ m : ℕ, 2 * ((r + 2) * 4 ^ i) = m + 1 ∧ (m : ℕ∞) ≤ L := fun i hi =>
    ⟨2 * ((r + 2) * 4 ^ i) - 1, by have := hs2 i; omega,
      (Nat.cast_le.2 (by have := hN i hi; omega)).trans hRL⟩
  have hsub : ∀ {t : ℕ} {lo hi : LatticeSite 2},
      -(3 * (t : ℤ)) ≤ lo 0 ∧ hi 0 ≤ 3 * t + 1 ∧ -(3 * (t : ℤ)) ≤ lo 1 ∧ hi 1 ≤ 3 * t + 1 →
      ((t : ℤ) ≤ lo 0 ∨ hi 0 ≤ -t ∨ (t : ℤ) ≤ lo 1 ∨ hi 1 ≤ -t) →
      Icc lo hi ⊆ {v : LatticeSite 2 | ((t : ℤ) ≤ v 0 ∨ v 0 ≤ -(t : ℤ) ∨ (t : ℤ) ≤ v 1 ∨
        v 1 ≤ -(t : ℤ)) ∧ -(3 * (t : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * (t : ℤ) + 1 ∧
        -(3 * (t : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * (t : ℤ) + 1} :=
    fun hbox hout v hv => mem_blockingAnnulus_of_mem_Icc hv hbox hout
  cases col with
  | true =>
    refine law_le_one_sub_pow_of_blocking (s := fun i => (r + 2) * 4 ^ i)
      (D := fun t : ℕ => {v : LatticeSite 2 | ((t : ℤ) ≤ v 0 ∨ v 0 ≤ -(t : ℤ) ∨ (t : ℤ) ≤ v 1 ∨
        v 1 ≤ -(t : ℤ)) ∧ -(3 * (t : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * (t : ℤ) + 1 ∧
        -(3 * (t : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * (t : ℤ) + 1})
      (K := fun t => (crossing 1 ![-3 * (t : ℤ), t] ![3 * t, 3 * t])ᶜ ∩
        (crossing 1 ![-3 * (t : ℤ), -3 * t] ![3 * t, -t])ᶜ ∩
        (crossing 0 ![(t : ℤ), -3 * t] ![3 * t, 3 * t])ᶜ ∩
        (crossing 0 ![-3 * (t : ℤ), -3 * t] ![-t, 3 * t])ᶜ)
      (fun i hi => ?_) (fun i => ?_) (fun i ω ω' hωω' => ?_) (pairwiseDisjoint_blockingAnnulus r N)
      fun i hi ω hω hK => ?_
    · obtain ⟨m, hm2, hmL⟩ := hm i hi
      exact pow_le_law_compl_crossing_inter h hm2 hmL
    · exact (((measurableSet_crossing _ _ _).compl.inter (measurableSet_crossing _ _ _).compl).inter
        (measurableSet_crossing _ _ _).compl).inter (measurableSet_crossing _ _ _).compl
    · have h₁ := mem_crossing_iff_of_inter_eq (i := 1)
        (lo := ![-3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), ((r + 2) * 4 ^ i : ℕ)])
        (hi := ![3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), 3 * ((r + 2) * 4 ^ i : ℕ)])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      have h₂ := mem_crossing_iff_of_inter_eq (i := 1)
        (lo := ![-3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), -3 * ((r + 2) * 4 ^ i : ℕ)])
        (hi := ![3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), -((r + 2) * 4 ^ i : ℕ)])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      have h₃ := mem_crossing_iff_of_inter_eq (i := 0)
        (lo := ![(((r + 2) * 4 ^ i : ℕ) : ℤ), -3 * ((r + 2) * 4 ^ i : ℕ)])
        (hi := ![3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), 3 * ((r + 2) * 4 ^ i : ℕ)])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      have h₄ := mem_crossing_iff_of_inter_eq (i := 0)
        (lo := ![-3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), -3 * ((r + 2) * 4 ^ i : ℕ)])
        (hi := ![-(((r + 2) * 4 ^ i : ℕ) : ℤ), 3 * ((r + 2) * 4 ^ i : ℕ)])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      simp only [mem_inter_iff, mem_compl_iff, h₁, h₂, h₃, h₄]
    · exact notMem_multiArmEvent_of_notMem_crossing hσ hK.1.1.1 hK.1.1.2 hK.1.2 hK.2
        (by have := hs2 i; omega) (hN i hi) hω
  | false =>
    refine law_le_one_sub_pow_of_blocking (s := fun i => (r + 2) * 4 ^ i)
      (D := fun t : ℕ => {v : LatticeSite 2 | ((t : ℤ) ≤ v 0 ∨ v 0 ≤ -(t : ℤ) ∨ (t : ℤ) ≤ v 1 ∨
        v 1 ≤ -(t : ℤ)) ∧ -(3 * (t : ℤ)) ≤ v 0 ∧ v 0 ≤ 3 * (t : ℤ) + 1 ∧
        -(3 * (t : ℤ)) ≤ v 1 ∧ v 1 ≤ 3 * (t : ℤ) + 1})
      (K := fun t => crossing 0 ![-3 * (t : ℤ), t + 1] ![3 * t + 1, 3 * t] ∩
        crossing 0 ![-3 * (t : ℤ), -3 * t + 1] ![3 * t + 1, -t] ∩
        crossing 1 ![(t : ℤ) + 1, -3 * t] ![3 * t, 3 * t + 1] ∩
        crossing 1 ![-3 * (t : ℤ) + 1, -3 * t] ![-t, 3 * t + 1])
      (fun i hi => ?_) (fun i => ?_) (fun i ω ω' hωω' => ?_) (pairwiseDisjoint_blockingAnnulus r N)
      fun i hi ω hω hK => ?_
    · obtain ⟨m, hm2, hmL⟩ := hm i hi
      exact pow_le_law_crossing_inter h hm2 hmL
    · exact (((measurableSet_crossing _ _ _).inter (measurableSet_crossing _ _ _)).inter
        (measurableSet_crossing _ _ _)).inter (measurableSet_crossing _ _ _)
    · have h₁ := mem_crossing_iff_of_inter_eq (i := 0)
        (lo := ![-3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), ((r + 2) * 4 ^ i : ℕ) + 1])
        (hi := ![3 * (((r + 2) * 4 ^ i : ℕ) : ℤ) + 1, 3 * ((r + 2) * 4 ^ i : ℕ)])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      have h₂ := mem_crossing_iff_of_inter_eq (i := 0)
        (lo := ![-3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), -3 * ((r + 2) * 4 ^ i : ℕ) + 1])
        (hi := ![3 * (((r + 2) * 4 ^ i : ℕ) : ℤ) + 1, -((r + 2) * 4 ^ i : ℕ)])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      have h₃ := mem_crossing_iff_of_inter_eq (i := 1)
        (lo := ![(((r + 2) * 4 ^ i : ℕ) : ℤ) + 1, -3 * ((r + 2) * 4 ^ i : ℕ)])
        (hi := ![3 * (((r + 2) * 4 ^ i : ℕ) : ℤ), 3 * ((r + 2) * 4 ^ i : ℕ) + 1])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      have h₄ := mem_crossing_iff_of_inter_eq (i := 1)
        (lo := ![-3 * (((r + 2) * 4 ^ i : ℕ) : ℤ) + 1, -3 * ((r + 2) * 4 ^ i : ℕ)])
        (hi := ![-(((r + 2) * 4 ^ i : ℕ) : ℤ), 3 * ((r + 2) * 4 ^ i : ℕ) + 1])
        (hsub (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)) hωω'
      simp only [mem_inter_iff, h₁, h₂, h₃, h₄]
    · exact notMem_multiArmEvent_of_mem_crossing hσ hK.1.1.1 hK.1.1.2 hK.1.2 hK.2
        (by have := hs2 i; omega) (hN i hi) hω

/-- **The law seen from `a`.** Under the profile `e ↦ q (e + a)` an event has the probability,
under `q`, of the configurations whose translate by `-a` lies in it. -/
theorem law_translate_apply {d : ℕ} (q : Sym2 (LatticeSite d) → unitInterval)
    (a : LatticeSite d) (A : Set (Config (LatticeSite d))) :
    law (fun e => q (Sym2.map (· + a) e)) A =
      law q ((fun ω => Sym2.map (· + -a) '' ω) ⁻¹' A) := by
  have hmap := PercLib.Probability.prodBernoulli_map_image_sym2 q (Equiv.addRight (-a))
  have hq : (q ∘ Sym2.map (Equiv.addRight (-a)).symm) = fun e => q (Sym2.map (· + a) e) := by
    funext e
    simp only [Function.comp_apply, Equiv.addRight_symm, neg_neg, Equiv.coe_addRight]
  rw [hq] at hmap
  unfold law
  rw [← hmap]
  exact map_image_sym2Map_apply _ _ _

/-- **A priori upper bound for multi-arm events** (Nolin, Proposition 14, upper half). For
every sequence of colours `σ` with an arm of colour `col` and every positive sequence `c`
there are `C` and `a > 0` such that, for every law with crossing bounds `c` up to scale `L`,
every centre `z` and all radii `r` and `R ≤ L`, `π_σ(r, R) ≤ C ((r + 1) / (R + 1))^a`. With
`col = true` this is the bound for sequences with an open arm, with `col = false` its dual
version. The constants depend only on `c`. -/
theorem exists_law_multiArmEvent_le_rpow {j : ℕ} (σ : Fin j → Bool) {col : Bool}
    (hσ : ∃ i, σ i = col) (c : ℕ → ℝ≥0∞) :
    ∃ C a : ℝ, 0 < a ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), (R : ℕ∞) ≤ L →
        (law q).real (multiArmEvent σ z r R) ≤ C * ((r + 1 : ℝ) / (R + 1)) ^ a := by
  -- without `0 < c 7` no law has crossing bounds `c`
  by_cases hc7 : c 7 = 0
  · exact ⟨0, 1, one_pos, fun q L h => absurd hc7 (h.pos 7).ne'⟩
  set βE : ℝ≥0∞ := min (c 7 ^ 4) 2⁻¹ with hβE
  have h2 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have hβ1 : βE < 1 := (min_le_right _ _).trans_lt h2
  set ρE : ℝ≥0∞ := 1 - βE with hρE_def
  have hρE1 : ρE < 1 := by
    refine ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (lt_min ?_ ?_).ne'
    · exact pos_iff_ne_zero.2 (pow_ne_zero 4 hc7)
    · exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hρE : 0 < ρE := tsub_pos_of_lt hβ1
  have hρE' : ρE ≠ ⊤ := (hρE1.trans ENNReal.one_lt_top).ne
  set ρ := ρE.toReal with hρ_def
  have hρ : 0 < ρ := ENNReal.toReal_pos hρE.ne' hρE'
  have hρ1 : ρ < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hρE' ENNReal.one_ne_top).2 hρE1
  set a := -Real.logb 4 ρ with ha_def
  have ha : 0 < a := neg_pos.2 (Real.logb_neg (by norm_num) hρ hρ1)
  have h4a : (4 : ℝ) ^ (-a) = ρ := by
    rw [ha_def, neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hρ
  refine ⟨6 ^ a, a, ha, fun q L h z r R hRL => ?_⟩
  -- translate the centre to the origin
  have hpre : (fun ω => Sym2.map (· + -z) '' ω) ⁻¹' multiArmEvent σ 0 r R =
      multiArmEvent σ z r R := by
    ext ω
    have := image_add_mem_multiArmEvent_iff (σ := σ) (z := z) (r := r) (ω := ω) (-z) (R := R)
    rwa [add_neg_cancel] at this
  have heq : law q (multiArmEvent σ z r R) =
      law (fun e => q (Sym2.map (· + z) e)) (multiArmEvent σ 0 r R) := by
    rw [law_translate_apply, hpre]
  -- the number of scales
  classical
  have hex : ∃ N : ℕ, R < 3 * ((r + 2) * 4 ^ N) := by
    refine ⟨R, ?_⟩
    have h1 : R < 4 ^ R := Nat.lt_pow_self (by norm_num)
    have h2 : 4 ^ R ≤ (r + 2) * 4 ^ R := Nat.le_mul_of_pos_left _ (by omega)
    omega
  set N := Nat.find hex with hN_def
  have hN : R < 3 * ((r + 2) * 4 ^ N) := Nat.find_spec hex
  have hNmin : ∀ i < N, 3 * ((r + 2) * 4 ^ i) ≤ R := fun i hi =>
    not_lt.1 (Nat.find_min hex hi)
  -- the bound in `ℝ≥0∞`
  have hE : law q (multiArmEvent σ z r R) ≤ ρE ^ N := by
    rw [heq]
    exact (law_multiArmEvent_zero_le_one_sub_pow (h.translate z) hσ hNmin hRL).trans
      (pow_le_pow_left₀ zero_le (tsub_le_tsub_left (min_le_left _ _) 1) N)
  have hreal : (law q).real (multiArmEvent σ z r R) ≤ ρ ^ N := by
    have := ENNReal.toReal_mono (ENNReal.pow_ne_top hρE') hE
    rwa [ENNReal.toReal_pow] at this
  -- from `ρ^N` to a power of `(r + 1) / (R + 1)`
  have hX0 : (0 : ℝ) < ((R : ℝ) + 1) / ((r : ℝ) + 1) := by positivity
  have h4N : ((R : ℝ) + 1) / ((r : ℝ) + 1) / 6 ≤ (4 : ℝ) ^ N := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have h1 : (r + 2) * 4 ^ N ≤ 2 * (r + 1) * 4 ^ N := Nat.mul_le_mul_right _ (by omega)
    have h2 : 4 ^ N * ((r + 1) * 6) = 3 * (2 * (r + 1) * 4 ^ N) := by ring
    have h3 : R + 1 ≤ 4 ^ N * ((r + 1) * 6) := by omega
    exact_mod_cast h3
  calc (law q).real (multiArmEvent σ z r R) ≤ ρ ^ N := hreal
    _ = ((4 : ℝ) ^ N) ^ (-a) := by
        rw [← h4a, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4), mul_comm]
    _ ≤ (((R : ℝ) + 1) / ((r : ℝ) + 1) / 6) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hX0 (by norm_num)) h4N (by linarith)
    _ = 6 ^ a * (((R : ℝ) + 1) / ((r : ℝ) + 1)) ^ (-a) := by
        rw [Real.div_rpow hX0.le (by norm_num : (0 : ℝ) ≤ 6),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6) a, div_inv_eq_mul, mul_comm]
    _ = 6 ^ a * ((r + 1 : ℝ) / (R + 1)) ^ a := by
        rw [Real.rpow_neg hX0.le, ← Real.inv_rpow hX0.le, inv_div]

/-! ### Geometric tail of the number of disjoint crossings -/

/-- **Disjoint open bottom-top crossings** (Nolin, Lemma 15, first step). `m` disjoint open
bottom-top crossings of the box of width `k n` and height `n + 1` have probability at most
`(1 - c (k + 1))^m`. -/
theorem law_foldl_crossing_one_le_pow (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) (m : ℕ) :
    law q ((List.replicate m (crossing 1 lo (lo + ![(k : ℤ) * n, n + 1]))).foldl
      disjointOccurrence univ) ≤ (1 - c (k + 1)) ^ m :=
  (prodBernoulli_foldl_replicate_le_pow q (isUpperSet_crossing _ _ _) m).trans
    (pow_le_pow_left₀ zero_le (law_crossing_one_le_one_sub h k lo hn hnL) m)

/-- **Disjoint open left-right crossings.** `m` disjoint open left-right crossings of the box of
width `n + 1` and height `k n` have probability at most `(1 - c (k + 1))^m`. -/
theorem law_foldl_crossing_zero_le_pow (h : CrossingBounds q L c) (k : ℕ) (lo : LatticeSite 2)
    {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) (m : ℕ) :
    law q ((List.replicate m (crossing 0 lo (lo + ![(n : ℤ) + 1, k * n]))).foldl
      disjointOccurrence univ) ≤ (1 - c (k + 1)) ^ m :=
  (prodBernoulli_foldl_replicate_le_pow q (isUpperSet_crossing _ _ _) m).trans
    (pow_le_pow_left₀ zero_le (law_crossing_zero_le_one_sub h k lo hn hnL) m)

/-- **Disjoint dual-open bottom-top crossings.** `m` disjoint dual-open bottom-top crossings of
the box of faces of width `k n` and height `n + 1` have probability at most
`(1 - c (k + 1))^m`. -/
theorem law_foldl_dualConfig_crossing_one_le_pow (h : CrossingBounds q L c) (k : ℕ)
    (lo : LatticeSite 2) {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) (m : ℕ) :
    law q ((List.replicate m (dualConfig ⁻¹' crossing 1 lo (lo + ![(k : ℤ) * n, n + 1]))).foldl
      disjointOccurrence univ) ≤ (1 - c (k + 1)) ^ m :=
  (prodBernoulli_foldl_replicate_le_pow_of_isLowerSet q (D := dualConfig ⁻¹' crossing _ _ _)
    (fun _ _ hab hx => crossing_mono (dualConfig_anti hab) hx)
    (measurable_dualConfig (measurableSet_crossing _ _ _)) m).trans
    (pow_le_pow_left₀ zero_le (law_dualConfig_crossing_one_le_one_sub h k lo hn hnL) m)

/-- **Disjoint dual-open left-right crossings.** `m` disjoint dual-open left-right crossings of
the box of faces of width `n + 1` and height `k n` have probability at most
`(1 - c (k + 1))^m`. -/
theorem law_foldl_dualConfig_crossing_zero_le_pow (h : CrossingBounds q L c) (k : ℕ)
    (lo : LatticeSite 2) {n : ℕ} (hn : 1 ≤ n) (hnL : (n : ℕ∞) ≤ L) (m : ℕ) :
    law q ((List.replicate m (dualConfig ⁻¹' crossing 0 lo (lo + ![(n : ℤ) + 1, k * n]))).foldl
      disjointOccurrence univ) ≤ (1 - c (k + 1)) ^ m :=
  (prodBernoulli_foldl_replicate_le_pow_of_isLowerSet q (D := dualConfig ⁻¹' crossing _ _ _)
    (fun _ _ hab hx => crossing_mono (dualConfig_anti hab) hx)
    (measurable_dualConfig (measurableSet_crossing _ _ _)) m).trans
    (pow_le_pow_left₀ zero_le (law_dualConfig_crossing_zero_le_one_sub h k lo hn hnL) m)

end PercLib.Models.Planar
