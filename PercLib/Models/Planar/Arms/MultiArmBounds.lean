/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4: Lemma 15, first step of the proof (p. 1579).
-/
module

public import PercLib.Models.Planar.Arms.MultiArmBasics
public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Probability.LocallyMonotone

/-!
# Bounds on crossing and multi-arm events

Consequences of crossing bounds of both colours (`CrossingBounds q L c`) for families of
disjoint crossings on the square lattice.

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

## Main results

* `law_crossing_one_le_one_sub`, `law_crossing_zero_le_one_sub`,
  `law_dualConfig_crossing_one_le_one_sub`, `law_dualConfig_crossing_zero_le_one_sub`: crossings
  in the short direction, of both colours, have probability at most `1 - c (k + 1)`.
* `law_foldl_crossing_one_le_pow`, `law_foldl_crossing_zero_le_pow`,
  `law_foldl_dualConfig_crossing_one_le_pow`, `law_foldl_dualConfig_crossing_zero_le_pow`: `h`
  disjoint such crossings have probability at most `(1 - c (k + 1))^h`.
* `mem_foldl_crossing_of_walks`, `mem_foldl_dualConfig_crossing_of_walks`: `h` crossing walks
  with pairwise disjoint sets of edges give `h` disjoint occurrences of the crossing event.
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
