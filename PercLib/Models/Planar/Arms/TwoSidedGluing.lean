/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12) and
Section 4.5 (quasi-multiplicativity, Proposition 17).
-/
module

public import PercLib.Models.Planar.Arms.InnerGluing
public import PercLib.Models.Planar.Arms.RotationGluing

/-!
# The two-sided gluing

Arms from `B_r(z)` separated at the outer boundary of `B_R(z)` (`ArmsOuterSeparated`) and arms
from `B_{R'}(z)` to the boundary of `B_{R₃}(z)` separated at the inner boundary
(`ArmsInnerSeparated`), with `R < R'`, are glued through one corridor per arm in the annulus
between `B_R(z)` and `B_{R'}(z)` into `j` arms from `B_r(z)` to the boundary of `B_{R₃}(z)`, at a
cost bounded below. This is the gluing step of the lower half of quasi-multiplicativity,
`π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)` (Nolin, Proposition 17): after separation at both ends and
alignment of the windows, the two families are glued.

The proof:

1. *Independence.* The first event is determined by the pairs inside `B_{R + M + K + 1}(z)`, the
   second by the pairs outside it (`law_inter_eq_mul_of_separated`).
2. *Corridors.* The corridor events are crossings of one colour in disjoint regions; by Harris for
   a mixed order their intersection has probability at least the product.
3. *Conditioning on both families.* With the ends and the starts confined to fixed windows, both
   events are upper for the mixed order off the corridors (`separated_of_mixed_of_forall_mem`,
   `innerSeparated_of_mixed_of_forall_mem`), and so is their intersection; the conditional form of
   Harris for a mixed order applies.
4. *Gluing.* On the intersection, each arm of the first family is continued through its outer
   fence, its corridor, the inner fence of the matching arm of the second family, and that arm.
   The continuations of two arms of one colour are disjoint: the corridors lie in disjoint regions,
   the second family is disjoint, the corridors meet the second family only at its starts, and the
   piece next to the inner fence misses the other arms of the second family by the barrier at the
   inner boundary (`notMem_support_of_subset_Icc_start`). `exists_isArm_of_glue` then gives the
   arms.

## Main results

* `cond_mem_crossing_iff_of_agree`: a crossing of either colour is determined by the pairs it
  reads; for the dual colour these have an end in the box and an end in the box shifted by
  `(1, 1)`.
* `exists_walks_of_fences`: joining an outer fence, a corridor and an inner fence.
* `exists_walks_two_sided_top` (and the three other sides), `exists_walks_two_sided`: the
  straight two-sided hook.
* `exists_two_sided_side`, `two_sided_side_facts`, `disjoint_two_sided_regions`,
  `CrossingBounds.le_law_two_sided_side`: the geometry and the crossing bound of the straight
  corridors.
* `law_mul_mul_prod_le_law_of_two_sided`: the two-sided gluing through given corridors in
  disjoint regions.
* `exists_pos_le_law_two_sided`: **the two-sided gluing** with straight corridors from windows on
  the sides: `c₀ · P(outer-separated at R, ends in the windows) · P(inner-separated at R', starts
  in the windows) ≤ P(j arms from B_r(z) to ∂B_{R₃}(z))`, with `c₀ = c A ^ j` for `R' - R ≤ A W`.
* `exists_pos_mul_le_of_separated_of_separated`: the lower half of quasi-multiplicativity, modulo
  the separation of the two families (taken as plain inequalities).

## Implementation notes

* The windows of the two families are aligned with one straight corridor per arm: the corridor
  `[x, x + W]` along the side lies inside both fences of every arm ending (starting) in the window
  (`β ≤ x + K`, `x + W ≤ α + K`, and the same with `K'`), so no bins and no jogs are needed and the
  constant is `c A ^ j`. Aligning the windows of the two families beforehand is the job of the
  motion plan (`MotionPlan.lean`) and of binning.
* A dual corridor on the top side reads pairs one row outside `B_{R'}(z)`. Its event is restated as
  determined by the pairs it actually reads (`cond_mem_crossing_iff_of_agree`), each with an end in
  `B_{R'}(z)`; this keeps the corridors away from the arms of the second family beyond their first
  step.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Corridors read only the pairs they need -/

/-- **The edge crossed by a dual edge** between two faces of a box `Icc lo hi` has both ends in
`Icc lo (hi + 1)`, an end in `Icc lo hi` and an end in `Icc (lo + 1) (hi + 1)`. -/
theorem mem_Icc_of_map_dualEdge {lo hi : LatticeSite 2} {f : Sym2 (LatticeSite 2)}
    (hf : f ∈ (zdGraph 2).edgeSet) (hfg : ∀ g ∈ f, g ∈ Icc lo hi) :
    (∀ v ∈ Sym2.map (· + 1) (dualEdge f), v ∈ Icc lo (hi + 1)) ∧
      (∃ v ∈ Sym2.map (· + 1) (dualEdge f), v ∈ Icc lo hi) ∧
      ∃ v ∈ Sym2.map (· + 1) (dualEdge f), v ∈ Icc (lo + 1) (hi + 1) := by
  have heE : Sym2.map (· + 1) (dualEdge f) ∈ (zdGraph 2).edgeSet :=
    map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hf)
  have hde : dualEdge (Sym2.map (· + 1) (dualEdge f)) = f :=
    congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨f, hf⟩)
  generalize Sym2.map (· + 1) (dualEdge f) = e at heE hde ⊢
  induction f using Sym2.ind with
  | h g₁ g₂ =>
  have hg₁ := hfg g₁ (Sym2.mem_mk_left _ _)
  have hg₂ := hfg g₂ (Sym2.mem_mk_right _ _)
  have hadjg : (zdGraph 2).Adj g₁ g₂ := hf
  have key : ∀ v ∈ e, v ∈ Icc g₁ (g₁ + 1) ∧ v ∈ Icc g₂ (g₂ + 1) := fun v hv =>
    ⟨mem_Icc_of_mem_dualEdge heE hv (hde ▸ Sym2.mem_mk_left _ _),
      mem_Icc_of_mem_dualEdge heE hv (hde ▸ Sym2.mem_mk_right _ _)⟩
  induction e using Sym2.ind with
  | h u w =>
  have hadj : (zdGraph 2).Adj u w := heE
  obtain ⟨hu₁, hu₂⟩ := key u (Sym2.mem_mk_left _ _)
  obtain ⟨hw₁, hw₂⟩ := key w (Sym2.mem_mk_right _ _)
  rw [zdGraph_two_adj_iff] at hadj hadjg
  rw [mem_Icc_two_iff] at hg₁ hg₂ hu₁ hu₂ hw₁ hw₂
  simp only [Pi.add_apply, Pi.one_apply] at hu₁ hu₂ hw₁ hw₂
  refine ⟨fun v hv => ?_, ?_, ?_⟩
  · rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.one_apply]
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> omega
  · by_cases hu : u ∈ Icc lo hi
    · exact ⟨u, Sym2.mem_mk_left _ _, hu⟩
    · refine ⟨w, Sym2.mem_mk_right _ _, ?_⟩
      rw [mem_Icc_two_iff] at hu ⊢
      omega
  · by_cases hu : u ∈ Icc (lo + 1) (hi + 1)
    · exact ⟨u, Sym2.mem_mk_left _ _, hu⟩
    · refine ⟨w, Sym2.mem_mk_right _ _, ?_⟩
      rw [mem_Icc_two_iff] at hu ⊢
      simp only [Pi.add_apply, Pi.one_apply] at hu ⊢
      omega

/-- **A crossing of either colour is determined by the pairs it reads.** For the open colour these
are the pairs inside the box; for the dual colour, the edges crossed by dual edges between faces of
the box, which have both ends in `Icc lo (hi + 1)`, an end in `Icc lo hi` and an end in
`Icc (lo + 1) (hi + 1)`. -/
theorem cond_mem_crossing_iff_of_agree (col : Bool) (d : Fin 2) (lo hi : LatticeSite 2)
    {ω ω' : Config (LatticeSite 2)}
    (h : ∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, v ∈ Icc lo (hi + cond col 0 1)) →
      (∃ v ∈ e, v ∈ Icc lo hi) → (∃ v ∈ e, v ∈ Icc (lo + cond col 0 1) (hi + cond col 0 1)) →
      (e ∈ ω ↔ e ∈ ω')) :
    cond col ω (dualConfig ω) ∈ crossing d lo hi ↔
      cond col ω' (dualConfig ω') ∈ crossing d lo hi := by
  cases col
  · refine mem_crossing_iff_of_inter_eq le_rfl ?_
    ext f
    simp only [Bool.cond_false, mem_inter_iff, mem_ofPred_eq, mem_dualConfig_iff]
    constructor
    · rintro ⟨⟨hf, hω⟩, hfg⟩
      obtain ⟨h₁, h₂, h₃⟩ := mem_Icc_of_map_dualEdge hf hfg
      exact ⟨⟨hf, fun h' => hω ((h _ h₁ h₂ h₃).2 h')⟩, hfg⟩
    · rintro ⟨⟨hf, hω⟩, hfg⟩
      obtain ⟨h₁, h₂, h₃⟩ := mem_Icc_of_map_dualEdge hf hfg
      exact ⟨⟨hf, fun h' => hω ((h _ h₁ h₂ h₃).1 h')⟩, hfg⟩
  · refine mem_crossing_iff_of_inter_eq le_rfl ?_
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq, Bool.cond_true]
    constructor
    · rintro ⟨he, hev⟩
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
      refine ⟨(h e (fun w hw => by simpa using hev w hw) ⟨v, hv, hev v hv⟩
        ⟨v, hv, by simpa using hev v hv⟩).1 he, hev⟩
    · rintro ⟨he, hev⟩
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
      refine ⟨(h e (fun w hw => by simpa using hev w hw) ⟨v, hv, hev v hv⟩
        ⟨v, hv, by simpa using hev v hv⟩).2 he, hev⟩

/-! ### Joining two fences through a corridor -/

/-- **Joining an outer fence, a corridor and an inner fence.** A connection from `x` to `u` inside
the box of radius `M` about `b`, a walk `f` from `u` inside that box, a walk `V` meeting `f` at
`w₁` and a walk `f'` inside the box of radius `M'` about `a'` at `w₂`, and a connection from `x'`
to the start `u'` of `f'` inside that box, all of configuration `ζ`, give a walk of `ζ` from `x` to
`w₂` through the first box and `V`, and a walk of `ζ` from `w₂` to `x'` inside the second box. -/
theorem exists_walks_of_fences {ζ : Config (LatticeSite 2)}
    {b a' x u v x' u' v' c d w₁ w₂ : LatticeSite 2} {M M' : ℕ}
    (hxu : ζ ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (b - (M : LatticeSite 2)) (b + M)) x u)
    (f : (zdGraph 2).Walk u v) (hf : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M))
    (hfe : ∀ e ∈ f.edges, e ∈ ζ) (V : (zdGraph 2).Walk c d) (hVe : ∀ e ∈ V.edges, e ∈ ζ)
    (f' : (zdGraph 2).Walk u' v')
    (hf' : ∀ y ∈ f'.support, y ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M'))
    (hf'e : ∀ e ∈ f'.edges, e ∈ ζ)
    (hxu' : ζ ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (a' - (M' : LatticeSite 2)) (a' + M')) x' u')
    (hw₁f : w₁ ∈ f.support) (hw₁V : w₁ ∈ V.support) (hw₂f' : w₂ ∈ f'.support)
    (hw₂V : w₂ ∈ V.support) :
    ∃ (P₁ : (zdGraph 2).Walk x w₂) (P₂ : (zdGraph 2).Walk w₂ x'),
      (∀ e ∈ P₁.edges, e ∈ ζ) ∧ (∀ e ∈ P₂.edges, e ∈ ζ) ∧
      (∀ y ∈ P₁.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ y ∈ V.support) ∧
      ∀ y ∈ P₂.support, y ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := by
  obtain ⟨p, hp, hpe⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨Q₁, hQ₁e, hQ₁s⟩ := exists_walk_join p hpe f hfe f.start_mem_support hw₁f
  obtain ⟨Q₂, hQ₂e, hQ₂s⟩ := exists_walk_join Q₁ hQ₁e V hVe hw₁V hw₂V
  obtain ⟨g, hg, hge⟩ := exists_walk_of_mem_support_of_mem_support f' hw₂f' f'.start_mem_support
  obtain ⟨p', hp', hp'e⟩ := exists_walk_of_mem_localConn hxu'
  refine ⟨Q₂, g.append p'.reverse, hQ₂e, fun e he => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    rcases he with he | he
    · exact hf'e e (hge e he)
    · exact hp'e e he
  · rcases hQ₂s y hy with hy | hy
    · rcases hQ₁s y hy with hy | hy
      · exact Or.inl (hp y hy)
      · exact Or.inl (hf y hy)
    · exact Or.inr hy
  · rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hy
    rcases hy with hy | hy
    · exact hf' y (hg y hy)
    · exact hp' y hy

/-! ### Straight two-sided hooks -/

section Hooks

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R R' M K M' K' W : ℕ}
  {a b a' b' : LatticeSite 2} {γ : (zdGraph 2).Walk a b} {δ : (zdGraph 2).Walk a' b'}

/-- **The straight two-sided hook on the top side.** On the bottom-top crossing of the corridor
`[x, x + W] × [z₁ + R, z₁ + R']` in the configuration of colour `col`, an arm `γ` ending at `b` on
the top side of `B_R(z)` (not at a corner) with an outer fence of length `2K` and depth `M`, and an
arm `δ` starting at `a'` on the top side of `B_{R'}(z)` (not at a corner) with an inner fence of
length `2K'` and depth `M'`, both fences spanning the columns of the corridor, are joined by a walk
of colour `col` from a vertex (face) of `γ` within `M` of `b`, through the box of radius `M` about
`b` and the corridor, to a point `w`, followed by a walk from `w` to a vertex (face) of `δ` inside
the box of radius `M'` about `a'`. -/
theorem exists_walks_two_sided_top (hM : 1 ≤ M) (hKM : K ≤ M) (hM' : 1 ≤ M') (hK'M' : K' ≤ M')
    (hRM : R + M ≤ R') (hRM' : R + M' ≤ R') {x : ℤ}
    (hC : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 + R] ![x + W, z 1 + R'])
    (hb₁ : b 1 = z 1 + R) (hbx : b 0 - K ≤ x) (hbx' : x + W ≤ b 0 + K)
    (hbL : z 0 - R + 1 ≤ b 0) (hbR : b 0 + 1 ≤ z 0 + R)
    (ha₁ : a' 1 = z 1 + R') (hax : a' 0 - K' ≤ x) (hax' : x + W ≤ a' 0 + K')
    (haL : z 0 - R' + 1 ≤ a' 0) (haR : a' 0 + 1 ≤ z 0 + R')
    (hf : HasOuterFence ω col z R M K γ) (hf' : HasInnerFence ω col z R' M' K' δ) :
    ∃ (x₀ w x₁ : LatticeSite 2) (P₁ : (zdGraph 2).Walk x₀ w) (P₂ : (zdGraph 2).Walk w x₁),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧ x₁ ∈ δ.support ∧
      (∀ e ∈ P₁.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ P₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P₁.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![x, z 1 + R] : LatticeSite 2) ![x + W, z 1 + R']) ∧
      ∀ v ∈ P₂.support, v ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨hu, hv, huv⟩ : u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1] ![b 0 + K, b 1 + M]) u v := by
    rcases hfen with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exfalso; omega
  obtain ⟨x₁, hx₁, u', v', hxu', hfen'⟩ := hf'
  obtain ⟨hu', hv', huv'⟩ : u' 0 = a' 0 - K' ∧ v' 0 = a' 0 + K' ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![a' 0 - K', a' 1 - M'] ![a' 0 + K', a' 1]) u' v' := by
    rcases hfen' with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exfalso; omega
  obtain ⟨c', -, hc'1, d, -, hd1, hcd⟩ := hC
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc'1 hd1
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  obtain ⟨f', hf's, hf'e⟩ := exists_walk_of_mem_localConn huv'
  have CV : ∀ y ∈ V.support, x ≤ y 0 ∧ y 0 ≤ x + W ∧ z 1 + R ≤ y 1 ∧ y 1 ≤ z 1 + R' :=
    fun y hy => by
      have := hV y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have Cf : ∀ y ∈ f.support, b 0 - K ≤ y 0 ∧ y 0 ≤ b 0 + K ∧ b 1 ≤ y 1 ∧ y 1 ≤ b 1 + M :=
    fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have Cf' : ∀ y ∈ f'.support,
      a' 0 - K' ≤ y 0 ∧ y 0 ≤ a' 0 + K' ∧ a' 1 - M' ≤ y 1 ∧ y 1 ≤ a' 1 := fun y hy => by
    have := hf's y hy
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₁, hw₁f, hw₁V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f V (x₀ := x)
    (x₁ := x + W) (y₀ := b 1) (y₁ := b 1 + M) (by omega) (by omega)
    (fun y hy => ⟨(Cf y hy).2.2.1, (Cf y hy).2.2.2⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).1, (CV y hy).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂f', hw₂V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f' V (x₀ := x)
    (x₁ := x + W) (y₀ := a' 1 - M') (y₁ := a' 1) (by omega) (by omega)
    (fun y hy => ⟨(Cf' y hy).2.2.1, (Cf' y hy).2.2.2⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).1, (CV y hy).2.1⟩) (by omega) (by omega)
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := fun y hy => by
    have := Cf y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  have hf'B : ∀ y ∈ f'.support, y ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := fun y hy => by
    have := Cf' y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨P₁, P₂, h₁, h₂, h₃, h₄⟩ := exists_walks_of_fences hxu f hfB hfe V hVe f' hf'B hf'e hxu'
    hw₁f hw₁V hw₂f' hw₂V
  obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
  exact ⟨x₀, w₂, x₁, P₁, P₂, hx₀, hp x₀ p.start_mem_support, hx₁, h₁, h₂,
    fun y hy => (h₃ y hy).imp id (hV y), h₄⟩

/-- **The straight two-sided hook on the right side**: `exists_walks_two_sided_top` with the
coordinates exchanged, for the left-right crossing of `[z₀ + R, z₀ + R'] × [x, x + W]`. -/
theorem exists_walks_two_sided_right (hM : 1 ≤ M) (hKM : K ≤ M) (hK'M' : K' ≤ M')
    (hW : 1 ≤ W) (hRM : R + M ≤ R') (hRM' : R + M' ≤ R') {x : ℤ}
    (hC : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, x] ![z 0 + R', x + W])
    (hb₀ : b 0 = z 0 + R) (hbx : b 1 - K ≤ x) (hbx' : x + W ≤ b 1 + K)
    (hbB : z 1 - R + 1 ≤ b 1) (hbT : b 1 + 1 ≤ z 1 + R)
    (ha₀ : a' 0 = z 0 + R') (hax : a' 1 - K' ≤ x) (hax' : x + W ≤ a' 1 + K')
    (haB : z 1 - R' + 1 ≤ a' 1) (haT : a' 1 + 1 ≤ z 1 + R')
    (hf : HasOuterFence ω col z R M K γ) (hf' : HasInnerFence ω col z R' M' K' δ) :
    ∃ (x₀ w x₁ : LatticeSite 2) (P₁ : (zdGraph 2).Walk x₀ w) (P₂ : (zdGraph 2).Walk w x₁),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧ x₁ ∈ δ.support ∧
      (∀ e ∈ P₁.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ P₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P₁.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![z 0 + R, x] : LatticeSite 2) ![z 0 + R', x + W]) ∧
      ∀ v ∈ P₂.support, v ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨hu, hv, huv⟩ : u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0, b 1 - K] ![b 0 + M, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso; omega
    · exact h
    all_goals exfalso; omega
  obtain ⟨x₁, hx₁, u', v', hxu', hfen'⟩ := hf'
  obtain ⟨hu', hv', huv'⟩ : u' 1 = a' 1 - K' ∧ v' 1 = a' 1 + K' ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![a' 0 - M', a' 1 - K'] ![a' 0, a' 1 + K']) u' v' := by
    rcases hfen' with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso; omega
    · exact h
    all_goals exfalso; omega
  obtain ⟨c', -, hc'0, d, -, hd0, hcd⟩ := hC
  simp only [Matrix.cons_val_zero] at hc'0 hd0
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  obtain ⟨f', hf's, hf'e⟩ := exists_walk_of_mem_localConn huv'
  have CV : ∀ y ∈ V.support, z 0 + R ≤ y 0 ∧ y 0 ≤ z 0 + R' ∧ x ≤ y 1 ∧ y 1 ≤ x + W :=
    fun y hy => by
      have := hV y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have Cf : ∀ y ∈ f.support, b 0 ≤ y 0 ∧ y 0 ≤ b 0 + M ∧ b 1 - K ≤ y 1 ∧ y 1 ≤ b 1 + K :=
    fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have Cf' : ∀ y ∈ f'.support,
      a' 0 - M' ≤ y 0 ∧ y 0 ≤ a' 0 ∧ a' 1 - K' ≤ y 1 ∧ y 1 ≤ a' 1 + K' := fun y hy => by
    have := hf's y hy
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₁, hw₁f, hw₁V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f V (x₀ := x)
    (x₁ := x + W) (y₀ := b 0) (y₁ := b 0 + M) (by omega) (by omega)
    (fun y hy => ⟨(Cf y hy).1, (Cf y hy).2.1⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).2.2.1, (CV y hy).2.2.2⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂f', hw₂V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f' V (x₀ := x)
    (x₁ := x + W) (y₀ := a' 0 - M') (y₁ := a' 0) (by omega) (by omega)
    (fun y hy => ⟨(Cf' y hy).1, (Cf' y hy).2.1⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).2.2.1, (CV y hy).2.2.2⟩) (by omega) (by omega)
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := fun y hy => by
    have := Cf y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  have hf'B : ∀ y ∈ f'.support, y ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := fun y hy => by
    have := Cf' y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨P₁, P₂, h₁, h₂, h₃, h₄⟩ := exists_walks_of_fences hxu f hfB hfe V hVe f' hf'B hf'e hxu'
    hw₁f hw₁V hw₂f' hw₂V
  obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
  exact ⟨x₀, w₂, x₁, P₁, P₂, hx₀, hp x₀ p.start_mem_support, hx₁, h₁, h₂,
    fun y hy => (h₃ y hy).imp id (hV y), h₄⟩

/-- **The straight two-sided hook on the bottom side**: `exists_walks_two_sided_top` reflected,
for the bottom-top crossing of `[x, x + W] × [z₁ - R' - δ, z₁ - R - δ]`, `δ = cond col 0 1`. -/
theorem exists_walks_two_sided_bottom (hM : 1 ≤ M) (hKM : K ≤ M) (hM' : 1 ≤ M')
    (hK'M' : K' ≤ M') (hRM : R + M ≤ R') (hRM' : R + M' ≤ R') {x : ℤ}
    (hC : cond col ω (dualConfig ω) ∈ crossing 1 ![x, z 1 - R' - cond col 0 1]
      ![x + W, z 1 - R - cond col 0 1])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hbx : b 0 - K ≤ x) (hbx' : x + W ≤ b 0 + K)
    (hbL : z 0 - R + 1 ≤ b 0) (hbR : b 0 + 1 ≤ z 0 + R)
    (ha₁ : a' 1 = z 1 - R' - cond col 0 1) (hax : a' 0 - K' ≤ x) (hax' : x + W ≤ a' 0 + K')
    (haL : z 0 - R' + 1 ≤ a' 0) (haR : a' 0 + 1 ≤ z 0 + R')
    (hf : HasOuterFence ω col z R M K γ) (hf' : HasInnerFence ω col z R' M' K' δ) :
    ∃ (x₀ w x₁ : LatticeSite 2) (P₁ : (zdGraph 2).Walk x₀ w) (P₂ : (zdGraph 2).Walk w x₁),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧ x₁ ∈ δ.support ∧
      (∀ e ∈ P₁.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ P₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P₁.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![x, z 1 - R' - cond col 0 1] : LatticeSite 2)
          ![x + W, z 1 - R - cond col 0 1]) ∧
      ∀ v ∈ P₂.support, v ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨hu, hv, huv⟩ : u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1 - M] ![b 0 + K, b 1]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exfalso; omega
    · exfalso; omega
    · exact h
    · exfalso; omega
  obtain ⟨x₁, hx₁, u', v', hxu', hfen'⟩ := hf'
  obtain ⟨hu', hv', huv'⟩ : u' 0 = a' 0 - K' ∧ v' 0 = a' 0 + K' ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![a' 0 - K', a' 1] ![a' 0 + K', a' 1 + M']) u' v' := by
    rcases hfen' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exfalso; omega
    · exfalso; omega
    · exact h
    · exfalso; omega
  obtain ⟨c', -, hc'1, d, -, hd1, hcd⟩ := hC
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc'1 hd1
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  obtain ⟨f', hf's, hf'e⟩ := exists_walk_of_mem_localConn huv'
  have CV : ∀ y ∈ V.support, x ≤ y 0 ∧ y 0 ≤ x + W ∧ z 1 - R' - cond col 0 1 ≤ y 1 ∧
      y 1 ≤ z 1 - R - cond col 0 1 := fun y hy => by
    have := hV y hy
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have Cf : ∀ y ∈ f.support, b 0 - K ≤ y 0 ∧ y 0 ≤ b 0 + K ∧ b 1 - M ≤ y 1 ∧ y 1 ≤ b 1 :=
    fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have Cf' : ∀ y ∈ f'.support,
      a' 0 - K' ≤ y 0 ∧ y 0 ≤ a' 0 + K' ∧ a' 1 ≤ y 1 ∧ y 1 ≤ a' 1 + M' := fun y hy => by
    have := hf's y hy
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₁, hw₁f, hw₁V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f V (x₀ := x)
    (x₁ := x + W) (y₀ := b 1 - M) (y₁ := b 1) (by omega) (by omega)
    (fun y hy => ⟨(Cf y hy).2.2.1, (Cf y hy).2.2.2⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).1, (CV y hy).2.1⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂f', hw₂V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f' V (x₀ := x)
    (x₁ := x + W) (y₀ := a' 1) (y₁ := a' 1 + M') (by omega) (by omega)
    (fun y hy => ⟨(Cf' y hy).2.2.1, (Cf' y hy).2.2.2⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).1, (CV y hy).2.1⟩) (by omega) (by omega)
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := fun y hy => by
    have := Cf y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  have hf'B : ∀ y ∈ f'.support, y ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := fun y hy => by
    have := Cf' y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨P₁, P₂, h₁, h₂, h₃, h₄⟩ := exists_walks_of_fences hxu f hfB hfe V hVe f' hf'B hf'e hxu'
    hw₁f hw₁V hw₂f' hw₂V
  obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
  exact ⟨x₀, w₂, x₁, P₁, P₂, hx₀, hp x₀ p.start_mem_support, hx₁, h₁, h₂,
    fun y hy => (h₃ y hy).imp id (hV y), h₄⟩

/-- **The straight two-sided hook on the left side**: `exists_walks_two_sided_right` reflected,
for the left-right crossing of `[z₀ - R' - δ, z₀ - R - δ] × [x, x + W]`, `δ = cond col 0 1`. -/
theorem exists_walks_two_sided_left (hM : 1 ≤ M) (hKM : K ≤ M) (hK'M' : K' ≤ M')
    (hW : 1 ≤ W) (hRM : R + M ≤ R') (hRM' : R + M' ≤ R') {x : ℤ}
    (hC : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' - cond col 0 1, x]
      ![z 0 - R - cond col 0 1, x + W])
    (hb₀ : b 0 = z 0 - R - cond col 0 1) (hbx : b 1 - K ≤ x) (hbx' : x + W ≤ b 1 + K)
    (hbB : z 1 - R + 1 ≤ b 1) (hbT : b 1 + 1 ≤ z 1 + R)
    (ha₀ : a' 0 = z 0 - R' - cond col 0 1) (hax : a' 1 - K' ≤ x) (hax' : x + W ≤ a' 1 + K')
    (haB : z 1 - R' + 1 ≤ a' 1) (haT : a' 1 + 1 ≤ z 1 + R')
    (hf : HasOuterFence ω col z R M K γ) (hf' : HasInnerFence ω col z R' M' K' δ) :
    ∃ (x₀ w x₁ : LatticeSite 2) (P₁ : (zdGraph 2).Walk x₀ w) (P₂ : (zdGraph 2).Walk w x₁),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧ x₁ ∈ δ.support ∧
      (∀ e ∈ P₁.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ P₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P₁.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![z 0 - R' - cond col 0 1, x] : LatticeSite 2)
          ![z 0 - R - cond col 0 1, x + W]) ∧
      ∀ v ∈ P₂.support, v ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x₀, hx₀, u, v, hxu, hfen⟩ := hf
  obtain ⟨hu, hv, huv⟩ : u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - M, b 1 - K] ![b 0, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact h
  obtain ⟨x₁, hx₁, u', v', hxu', hfen'⟩ := hf'
  obtain ⟨hu', hv', huv'⟩ : u' 1 = a' 1 - K' ∧ v' 1 = a' 1 + K' ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![a' 0, a' 1 - K'] ![a' 0 + M', a' 1 + K']) u' v' := by
    rcases hfen' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact h
  obtain ⟨c', -, hc'0, d, -, hd0, hcd⟩ := hC
  simp only [Matrix.cons_val_zero] at hc'0 hd0
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  obtain ⟨f', hf's, hf'e⟩ := exists_walk_of_mem_localConn huv'
  have CV : ∀ y ∈ V.support, z 0 - R' - cond col 0 1 ≤ y 0 ∧ y 0 ≤ z 0 - R - cond col 0 1 ∧
      x ≤ y 1 ∧ y 1 ≤ x + W := fun y hy => by
    have := hV y hy
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  have Cf : ∀ y ∈ f.support, b 0 - M ≤ y 0 ∧ y 0 ≤ b 0 ∧ b 1 - K ≤ y 1 ∧ y 1 ≤ b 1 + K :=
    fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  have Cf' : ∀ y ∈ f'.support,
      a' 0 ≤ y 0 ∧ y 0 ≤ a' 0 + M' ∧ a' 1 - K' ≤ y 1 ∧ y 1 ≤ a' 1 + K' := fun y hy => by
    have := hf's y hy
    rw [mem_Icc_two_iff] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    omega
  obtain ⟨w₁, hw₁f, hw₁V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f V (x₀ := x)
    (x₁ := x + W) (y₀ := b 0 - M) (y₁ := b 0) (by omega) (by omega)
    (fun y hy => ⟨(Cf y hy).1, (Cf y hy).2.1⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).2.2.1, (CV y hy).2.2.2⟩) (by omega) (by omega)
  obtain ⟨w₂, hw₂f', hw₂V⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc_swap f' V (x₀ := x)
    (x₁ := x + W) (y₀ := a' 0) (y₁ := a' 0 + M') (by omega) (by omega)
    (fun y hy => ⟨(Cf' y hy).1, (Cf' y hy).2.1⟩) (by omega) (by omega)
    (fun y hy => ⟨(CV y hy).2.2.1, (CV y hy).2.2.2⟩) (by omega) (by omega)
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := fun y hy => by
    have := Cf y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  have hf'B : ∀ y ∈ f'.support, y ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := fun y hy => by
    have := Cf' y hy
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨P₁, P₂, h₁, h₂, h₃, h₄⟩ := exists_walks_of_fences hxu f hfB hfe V hVe f' hf'B hf'e hxu'
    hw₁f hw₁V hw₂f' hw₂V
  obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
  exact ⟨x₀, w₂, x₁, P₁, P₂, hx₀, hp x₀ p.start_mem_support, hx₁, h₁, h₂,
    fun y hy => (h₃ y hy).imp id (hV y), h₄⟩

end Hooks

/-! ### Straight two-sided corridors from windows on the sides -/

section Windows

variable {z : LatticeSite 2} {R R' M K M' K' W S : ℕ} {col : Bool} {t : Fin 4}
  {x α β α' β' : ℤ} {dir : Fin 2} {lo hi gl gh : LatticeSite 2}

/-- **The data of one straight two-sided corridor** on the side `t` (`0` top, `1` right, `2`
bottom, `3` left): its direction `dir`, the box `Icc lo hi` of width `W` from the side of `B_R(z)`
to the side of `B_{R'}(z)` at the side coordinates `[x, x + W]`, and its region `Icc gl gh`,
which contains the box, the boxes about the ends of the inner arms and about the starts of the
outer arms, up to `S` on both sides along the side. -/
theorem exists_two_sided_side (t : Fin 4) (col : Bool) (z : LatticeSite 2) (R R' M M' W S : ℕ)
    (x : ℤ) : ∃ (dir : Fin 2) (lo hi gl gh : LatticeSite 2),
      (t = 0 ∧ dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        gl = ![x - S, z 1 + R - M - 1] ∧ gh = ![x + W + S, z 1 + R' + M' + 1]) ∨
      (t = 1 ∧ dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        gl = ![z 0 + R - M - 1, x - S] ∧ gh = ![z 0 + R' + M' + 1, x + W + S]) ∨
      (t = 2 ∧ dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧
        hi = ![x + W, z 1 - R - cond col 0 1] ∧
        gl = ![x - S, z 1 - R' - M' - 2] ∧ gh = ![x + W + S, z 1 - R + M + 1]) ∨
      (t = 3 ∧ dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧
        hi = ![z 0 - R - cond col 0 1, x + W] ∧
        gl = ![z 0 - R' - M' - 2, x - S] ∧ gh = ![z 0 - R + M + 1, x + W + S]) := by
  fin_cases t
  · exact ⟨1, _, _, _, _, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨0, _, _, _, _, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩
  · exact ⟨1, _, _, _, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
  · exact ⟨0, _, _, _, _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩

/-- **The geometry of one straight two-sided corridor.** For a corridor as in
`exists_two_sided_side`, at least `2S` from the corners of `B_R(z)` along the side, with the
windows `[α, β]` (ends at `B_R(z)`) and `[α', β']` (starts at `B_{R'}(z)`) aligned with it: the
pairs read by the corridor miss the interior of `B_R(z)`, have an end in `B_{R'}(z)` and lie in
the region; the corridor lies in the start box of `B_{R'}(z)` for its colour; the boxes about the
possible ends and starts lie in the region; the corridor meets `Icc (z - R - 1) (z + R)` only near
the possible ends; and the boxes about the possible starts miss `Icc (z - R - 1) (z + R)`. -/
theorem two_sided_side_facts (hW : 1 ≤ W) (hWK : W ≤ K) (hKM : K ≤ M) (hWK' : W ≤ K')
    (hK'M' : K' ≤ M') (hS : M + K + M' + K' + 2 ≤ S)
    (hRR' : R + M + K + 1 + M' + K' + 1 < R')
    (hside : (t = 0 ∧ dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        gl = ![x - S, z 1 + R - M - 1] ∧ gh = ![x + W + S, z 1 + R' + M' + 1]) ∨
      (t = 1 ∧ dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        gl = ![z 0 + R - M - 1, x - S] ∧ gh = ![z 0 + R' + M' + 1, x + W + S]) ∨
      (t = 2 ∧ dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧
        hi = ![x + W, z 1 - R - cond col 0 1] ∧
        gl = ![x - S, z 1 - R' - M' - 2] ∧ gh = ![x + W + S, z 1 - R + M + 1]) ∨
      (t = 3 ∧ dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧
        hi = ![z 0 - R - cond col 0 1, x + W] ∧
        gl = ![z 0 - R' - M' - 2, x - S] ∧ gh = ![z 0 - R + M + 1, x + W + S]))
    (hc0 : t = 0 ∨ t = 2 → z 0 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 0 + R)
    (hc1 : t = 1 ∨ t = 3 → z 1 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 1 + R)
    (hal : β ≤ x + K ∧ x + W ≤ α + K ∧ β' ≤ x + K' ∧ x + W ≤ α' + K') :
    (∀ v ∈ Icc lo (hi + cond col 0 1), v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∧
    ((∀ v ∈ Icc lo hi, v ∈ Icc (z - (R' : LatticeSite 2)) (z + R')) ∨
      ∀ v ∈ Icc (lo + cond col 0 1) (hi + cond col 0 1),
        v ∈ Icc (z - (R' : LatticeSite 2)) (z + R')) ∧
    (∀ v ∈ Icc lo (hi + cond col 0 1), v ∈ Icc gl gh) ∧ (∀ v ∈ Icc lo hi, v ∈ Icc gl gh) ∧
    (∀ v ∈ Icc lo hi, v ∈ cond col (Icc (z - (R' : LatticeSite 2)) (z + R'))
      (Icc (z - (R' : LatticeSite 2) - 1) (z + R'))) ∧
    (∀ b : LatticeSite 2, ((t = 0 ∧ b 1 = z 1 + R ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ α ≤ b 1 ∧ b 1 ≤ β) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ α ≤ b 1 ∧ b 1 ≤ β)) →
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ Icc gl gh ∧
      ∀ v ∈ Icc lo hi, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
        v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
    ∀ a : LatticeSite 2, ((t = 0 ∧ a 1 = z 1 + R' ∧ α' ≤ a 0 ∧ a 0 ≤ β') ∨
        (t = 1 ∧ a 0 = z 0 + R' ∧ α' ≤ a 1 ∧ a 1 ≤ β') ∨
        (t = 2 ∧ a 1 = z 1 - R' - cond col 0 1 ∧ α' ≤ a 0 ∧ a 0 ≤ β') ∨
        (t = 3 ∧ a 0 = z 0 - R' - cond col 0 1 ∧ α' ≤ a 1 ∧ a 1 ≤ β')) →
      Icc (a - (M' : LatticeSite 2)) (a + ((M' + 1 : ℕ) : LatticeSite 2)) ⊆ Icc gl gh ∧
      ∀ v ∈ Icc (a - (M' : LatticeSite 2)) (a + M'),
        v ∉ Icc (z - (R : LatticeSite 2) - 1) (z + R) := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  have hcor : ((t = 0 ∨ t = 2) ∧ z 0 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 0 + R) ∨
      ((t = 1 ∨ t = 3) ∧ z 1 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t = 0 ∨ t = 2
    · exact Or.inl ⟨h, hc0 h⟩
    · exact Or.inr ⟨by omega, hc1 (by omega)⟩
  clear hc0 hc1
  rcases hside with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  rcases hcor with ⟨ht, h₁, h₂⟩ | ⟨ht, h₁, h₂⟩ <;>
  (try exact absurd ht (by decide)) <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro v hv hvR
       rw [mem_Icc_two_iff] at hv hvR
       simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, cond_zero_one_apply] at hv hvR
       omega)
    | (left
       intro v hv
       rw [mem_Icc_two_iff] at hv ⊢
       simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hv ⊢
       omega)
    | (right
       intro v hv
       rw [mem_Icc_two_iff] at hv ⊢
       simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, cond_zero_one_apply] at hv ⊢
       omega)
    | (intro v hv
       rw [mem_Icc_two_iff] at hv ⊢
       simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
         cond_zero_one_apply] at hv ⊢
       omega)
    | (intro v hv
       rw [mem_Icc_two_iff] at hv
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv
       cases col <;> simp only [Bool.cond_true, Bool.cond_false] at hv hcol ⊢ <;>
         rw [mem_Icc_two_iff] <;>
         simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] <;> omega)
    | (intro b hb
       rcases hb with ⟨ht, e₁, e₂, e₃⟩ | ⟨ht, e₁, e₂, e₃⟩ | ⟨ht, e₁, e₂, e₃⟩ |
         ⟨ht, e₁, e₂, e₃⟩ <;> (try exact absurd ht (by decide))
       refine ⟨fun v hv => ?_, fun v hv hvR => ?_⟩
       · rw [mem_Icc_two_iff] at hv ⊢
         simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hv ⊢
         push_cast at hv
         omega
       · rw [mem_Icc_two_iff] at hv hvR
         try rw [mem_Icc_two_iff]
         simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
           Matrix.cons_val_zero, Matrix.cons_val_one] at hv hvR ⊢
         omega)

/-- **The crossing bound of a straight two-sided corridor**: with `R' ≤ R + A W`, the corridor is
crossed in the configuration of its colour with probability at least `c A`. -/
theorem CrossingBounds.le_law_two_sided_side {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c) {A : ℕ} (hW : 1 ≤ W) (hWL : (W : ℕ∞) ≤ L)
    (hRR' : R ≤ R') (hA : R' ≤ R + A * W)
    (hside : (t = 0 ∧ dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        gl = ![x - S, z 1 + R - M - 1] ∧ gh = ![x + W + S, z 1 + R' + M' + 1]) ∨
      (t = 1 ∧ dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        gl = ![z 0 + R - M - 1, x - S] ∧ gh = ![z 0 + R' + M' + 1, x + W + S]) ∨
      (t = 2 ∧ dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧
        hi = ![x + W, z 1 - R - cond col 0 1] ∧
        gl = ![x - S, z 1 - R' - M' - 2] ∧ gh = ![x + W + S, z 1 - R + M + 1]) ∨
      (t = 3 ∧ dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧
        hi = ![z 0 - R - cond col 0 1, x + W] ∧
        gl = ![z 0 - R' - M' - 2, x - S] ∧ gh = ![z 0 - R + M + 1, x + W + S])) :
    c A ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing dir lo hi) := by
  have hA' : (R' : ℤ) ≤ R + A * W := by exact_mod_cast hA
  rcases hside with ⟨-, rfl, rfl, rfl, -, -⟩ | ⟨-, rfl, rfl, rfl, -, -⟩ |
    ⟨-, rfl, rfl, rfl, -, -⟩ | ⟨-, rfl, rfl, rfl, -, -⟩
  · exact hCB.le_law_box_one col A hW hWL (by omega) (by omega) (by omega)
  · exact hCB.le_law_box_zero col A hW hWL (by omega) (by omega) (by omega)
  · exact hCB.le_law_box_one col A hW hWL (by omega) (by omega) (by omega)
  · exact hCB.le_law_box_zero col A hW hWL (by omega) (by omega) (by omega)

/-- **The straight two-sided hook, on any side**: for a corridor as in `exists_two_sided_side`, an
arm ending in the window `[α, β]` at `B_R(z)` with an outer fence and an arm starting in the window
`[α', β']` at `B_{R'}(z)` with an inner fence, the windows aligned with the corridor, are joined
through the corridor (`exists_walks_two_sided_top` and the three other sides). -/
theorem exists_walks_two_sided {ω : Config (LatticeSite 2)} {a b a' b' : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} {δ : (zdGraph 2).Walk a' b'}
    (hW : 1 ≤ W) (hWK : W ≤ K) (hKM : K ≤ M) (hWK' : W ≤ K') (hK'M' : K' ≤ M')
    (hS : M + K + M' + K' + 2 ≤ S) (hRR' : R + M + K + 1 + M' + K' + 1 < R')
    (hside : (t = 0 ∧ dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        gl = ![x - S, z 1 + R - M - 1] ∧ gh = ![x + W + S, z 1 + R' + M' + 1]) ∨
      (t = 1 ∧ dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        gl = ![z 0 + R - M - 1, x - S] ∧ gh = ![z 0 + R' + M' + 1, x + W + S]) ∨
      (t = 2 ∧ dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧
        hi = ![x + W, z 1 - R - cond col 0 1] ∧
        gl = ![x - S, z 1 - R' - M' - 2] ∧ gh = ![x + W + S, z 1 - R + M + 1]) ∨
      (t = 3 ∧ dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧
        hi = ![z 0 - R - cond col 0 1, x + W] ∧
        gl = ![z 0 - R' - M' - 2, x - S] ∧ gh = ![z 0 - R + M + 1, x + W + S]))
    (hc0 : t = 0 ∨ t = 2 → z 0 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 0 + R)
    (hc1 : t = 1 ∨ t = 3 → z 1 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 1 + R)
    (hal : β ≤ x + K ∧ x + W ≤ α + K ∧ β' ≤ x + K' ∧ x + W ≤ α' + K')
    (hC : cond col ω (dualConfig ω) ∈ crossing dir lo hi)
    (hb : (t = 0 ∧ b 1 = z 1 + R ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ α ≤ b 1 ∧ b 1 ≤ β) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ α ≤ b 1 ∧ b 1 ≤ β))
    (ha : (t = 0 ∧ a' 1 = z 1 + R' ∧ α' ≤ a' 0 ∧ a' 0 ≤ β') ∨
        (t = 1 ∧ a' 0 = z 0 + R' ∧ α' ≤ a' 1 ∧ a' 1 ≤ β') ∨
        (t = 2 ∧ a' 1 = z 1 - R' - cond col 0 1 ∧ α' ≤ a' 0 ∧ a' 0 ≤ β') ∨
        (t = 3 ∧ a' 0 = z 0 - R' - cond col 0 1 ∧ α' ≤ a' 1 ∧ a' 1 ≤ β'))
    (hf : HasOuterFence ω col z R M K γ) (hf' : HasInnerFence ω col z R' M' K' δ) :
    ∃ (x₀ w x₁ : LatticeSite 2) (P₁ : (zdGraph 2).Walk x₀ w) (P₂ : (zdGraph 2).Walk w x₁),
      x₀ ∈ γ.support ∧ x₀ ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧ x₁ ∈ δ.support ∧
      (∀ e ∈ P₁.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ e ∈ P₂.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P₁.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Icc lo hi) ∧
      ∀ v ∈ P₂.support, v ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M') := by
  have hM : 1 ≤ M := by omega
  have hM' : 1 ≤ M' := by omega
  have hcor : ((t = 0 ∨ t = 2) ∧ z 0 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 0 + R) ∨
      ((t = 1 ∨ t = 3) ∧ z 1 - R + 2 * S ≤ x ∧ x + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t = 0 ∨ t = 2
    · exact Or.inl ⟨h, hc0 h⟩
    · exact Or.inr ⟨by omega, hc1 (by omega)⟩
  clear hc0 hc1
  obtain ⟨hal₁, hal₂, hal₃, hal₄⟩ := hal
  rcases hside with ⟨rfl, rfl, rfl, rfl, -, -⟩ | ⟨rfl, rfl, rfl, rfl, -, -⟩ |
    ⟨rfl, rfl, rfl, rfl, -, -⟩ | ⟨rfl, rfl, rfl, rfl, -, -⟩ <;>
  rcases hcor with ⟨ht, h₁, h₂⟩ | ⟨ht, h₁, h₂⟩ <;> (try exact absurd ht (by decide)) <;>
  rcases hb with ⟨hbt, hb₁, hb₂, hb₃⟩ | ⟨hbt, hb₁, hb₂, hb₃⟩ | ⟨hbt, hb₁, hb₂, hb₃⟩ |
    ⟨hbt, hb₁, hb₂, hb₃⟩ <;> (try exact absurd hbt (by decide)) <;>
  rcases ha with ⟨hat, ha₁, ha₂, ha₃⟩ | ⟨hat, ha₁, ha₂, ha₃⟩ | ⟨hat, ha₁, ha₂, ha₃⟩ |
    ⟨hat, ha₁, ha₂, ha₃⟩ <;> (try exact absurd hat (by decide))
  · exact exists_walks_two_sided_top hM hKM hM' hK'M' (by omega) (by omega) hC hb₁ (by omega)
      (by omega) (by omega) (by omega) ha₁ (by omega) (by omega) (by omega) (by omega) hf hf'
  · exact exists_walks_two_sided_right hM hKM hK'M' hW (by omega) (by omega) hC hb₁ (by omega)
      (by omega) (by omega) (by omega) ha₁ (by omega) (by omega) (by omega) (by omega) hf hf'
  · exact exists_walks_two_sided_bottom hM hKM hM' hK'M' (by omega) (by omega) hC hb₁ (by omega)
      (by omega) (by omega) (by omega) ha₁ (by omega) (by omega) (by omega) (by omega) hf hf'
  · exact exists_walks_two_sided_left hM hKM hK'M' hW (by omega) (by omega) hC hb₁ (by omega)
      (by omega) (by omega) (by omega) ha₁ (by omega) (by omega) (by omega) (by omega) hf hf'

/-- **The regions of two straight two-sided corridors are disjoint** when the corridors are at
least `2S` from the corners of `B_R(z)` and, on one side, more than `W + 2S` apart. -/
theorem disjoint_two_sided_regions {t₁ t₂ : Fin 4} {col₁ col₂ : Bool} {x₁ x₂ : ℤ}
    {dir₁ dir₂ : Fin 2} {lo₁ hi₁ gl₁ gh₁ lo₂ hi₂ gl₂ gh₂ : LatticeSite 2}
    (hMS : M + 2 ≤ S) (hMR : M + 1 < R)
    (hside₁ : (t₁ = 0 ∧ dir₁ = 1 ∧ lo₁ = ![x₁, z 1 + R] ∧ hi₁ = ![x₁ + W, z 1 + R'] ∧
        gl₁ = ![x₁ - S, z 1 + R - M - 1] ∧ gh₁ = ![x₁ + W + S, z 1 + R' + M' + 1]) ∨
      (t₁ = 1 ∧ dir₁ = 0 ∧ lo₁ = ![z 0 + R, x₁] ∧ hi₁ = ![z 0 + R', x₁ + W] ∧
        gl₁ = ![z 0 + R - M - 1, x₁ - S] ∧ gh₁ = ![z 0 + R' + M' + 1, x₁ + W + S]) ∨
      (t₁ = 2 ∧ dir₁ = 1 ∧ lo₁ = ![x₁, z 1 - R' - cond col₁ 0 1] ∧
        hi₁ = ![x₁ + W, z 1 - R - cond col₁ 0 1] ∧
        gl₁ = ![x₁ - S, z 1 - R' - M' - 2] ∧ gh₁ = ![x₁ + W + S, z 1 - R + M + 1]) ∨
      (t₁ = 3 ∧ dir₁ = 0 ∧ lo₁ = ![z 0 - R' - cond col₁ 0 1, x₁] ∧
        hi₁ = ![z 0 - R - cond col₁ 0 1, x₁ + W] ∧
        gl₁ = ![z 0 - R' - M' - 2, x₁ - S] ∧ gh₁ = ![z 0 - R + M + 1, x₁ + W + S]))
    (hside₂ : (t₂ = 0 ∧ dir₂ = 1 ∧ lo₂ = ![x₂, z 1 + R] ∧ hi₂ = ![x₂ + W, z 1 + R'] ∧
        gl₂ = ![x₂ - S, z 1 + R - M - 1] ∧ gh₂ = ![x₂ + W + S, z 1 + R' + M' + 1]) ∨
      (t₂ = 1 ∧ dir₂ = 0 ∧ lo₂ = ![z 0 + R, x₂] ∧ hi₂ = ![z 0 + R', x₂ + W] ∧
        gl₂ = ![z 0 + R - M - 1, x₂ - S] ∧ gh₂ = ![z 0 + R' + M' + 1, x₂ + W + S]) ∨
      (t₂ = 2 ∧ dir₂ = 1 ∧ lo₂ = ![x₂, z 1 - R' - cond col₂ 0 1] ∧
        hi₂ = ![x₂ + W, z 1 - R - cond col₂ 0 1] ∧
        gl₂ = ![x₂ - S, z 1 - R' - M' - 2] ∧ gh₂ = ![x₂ + W + S, z 1 - R + M + 1]) ∨
      (t₂ = 3 ∧ dir₂ = 0 ∧ lo₂ = ![z 0 - R' - cond col₂ 0 1, x₂] ∧
        hi₂ = ![z 0 - R - cond col₂ 0 1, x₂ + W] ∧
        gl₂ = ![z 0 - R' - M' - 2, x₂ - S] ∧ gh₂ = ![z 0 - R + M + 1, x₂ + W + S]))
    (hc0₁ : t₁ = 0 ∨ t₁ = 2 → z 0 - R + 2 * S ≤ x₁ ∧ x₁ + W + 2 * S ≤ z 0 + R)
    (hc1₁ : t₁ = 1 ∨ t₁ = 3 → z 1 - R + 2 * S ≤ x₁ ∧ x₁ + W + 2 * S ≤ z 1 + R)
    (hc0₂ : t₂ = 0 ∨ t₂ = 2 → z 0 - R + 2 * S ≤ x₂ ∧ x₂ + W + 2 * S ≤ z 0 + R)
    (hc1₂ : t₂ = 1 ∨ t₂ = 3 → z 1 - R + 2 * S ≤ x₂ ∧ x₂ + W + 2 * S ≤ z 1 + R)
    (hgap : t₁ = t₂ → x₁ + W + 2 * S < x₂ ∨ x₂ + W + 2 * S < x₁) :
    Disjoint (Icc gl₁ gh₁) (Icc gl₂ gh₂) := by
  have hcor₁ : ((t₁ = 0 ∨ t₁ = 2) ∧ z 0 - R + 2 * S ≤ x₁ ∧ x₁ + W + 2 * S ≤ z 0 + R) ∨
      ((t₁ = 1 ∨ t₁ = 3) ∧ z 1 - R + 2 * S ≤ x₁ ∧ x₁ + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t₁ = 0 ∨ t₁ = 2
    · exact Or.inl ⟨h, hc0₁ h⟩
    · exact Or.inr ⟨by omega, hc1₁ (by omega)⟩
  have hcor₂ : ((t₂ = 0 ∨ t₂ = 2) ∧ z 0 - R + 2 * S ≤ x₂ ∧ x₂ + W + 2 * S ≤ z 0 + R) ∨
      ((t₂ = 1 ∨ t₂ = 3) ∧ z 1 - R + 2 * S ≤ x₂ ∧ x₂ + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t₂ = 0 ∨ t₂ = 2
    · exact Or.inl ⟨h, hc0₂ h⟩
    · exact Or.inr ⟨by omega, hc1₂ (by omega)⟩
  have hgap' : (t₁ = t₂ ∧ (x₁ + W + 2 * S < x₂ ∨ x₂ + W + 2 * S < x₁)) ∨ t₁ ≠ t₂ := by
    by_cases h : t₁ = t₂
    · exact Or.inl ⟨h, hgap h⟩
    · exact Or.inr h
  clear hc0₁ hc1₁ hc0₂ hc1₂ hgap
  refine disjoint_Icc_of_lt ?_
  rcases hside₁ with ⟨rfl, -, -, -, rfl, rfl⟩ | ⟨rfl, -, -, -, rfl, rfl⟩ |
    ⟨rfl, -, -, -, rfl, rfl⟩ | ⟨rfl, -, -, -, rfl, rfl⟩ <;>
  rcases hside₂ with ⟨rfl, -, -, -, rfl, rfl⟩ | ⟨rfl, -, -, -, rfl, rfl⟩ |
    ⟨rfl, -, -, -, rfl, rfl⟩ | ⟨rfl, -, -, -, rfl, rfl⟩ <;>
  rcases hcor₁ with ⟨ht₁, h₁, h₂⟩ | ⟨ht₁, h₁, h₂⟩ <;> (try exact absurd ht₁ (by decide)) <;>
  rcases hcor₂ with ⟨ht₂, h₃, h₄⟩ | ⟨ht₂, h₃, h₄⟩ <;> (try exact absurd ht₂ (by decide)) <;>
  rcases hgap' with ⟨hteq, hg⟩ | hne <;> (try exact absurd hteq (by decide)) <;>
  (try exact absurd rfl hne) <;>
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

end Windows

/-! ### The two-sided gluing through given corridors -/

section Corridors

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- Two points in different regions of a family of pairwise disjoint regions are different. -/
theorem eq_of_mem_of_mem_of_disjoint {G : Fin j → Set (LatticeSite 2)}
    (hG : ∀ i k, i ≠ k → Disjoint (G i) (G k)) {i k : Fin j} {v : LatticeSite 2} (hi : v ∈ G i)
    (hk : v ∈ G k) : i = k := by
  by_contra hik
  exact disjoint_left.1 (hG i k hik) hi hk

/-- **The two-sided gluing through given corridors.** Let `γ` range over the families of arms from
`B_r(z)` to the boundary of `B_R(z)`, separated at the outer boundary (separation `s ≥ 2M + 1`,
fences of length `2K ≤ 2M` and depth `M ≥ 1`), with ends in the sets `B i` and inner positions in
the sets `J i`, and `δ` over the families of arms from `B_{R'}(z)` to the boundary of `B_{R₃}(z)`,
separated at the inner boundary (separation `s' ≥ 2M' + 2`, fences of length `2K' ≤ 2M'` and depth
`M' ≥ 1`), with starts in the sets `B' i`, where `R + M + K + M' + K' + 2 < R'` and
`R' + M' + 1 < R₃`. For each arm `i` let `C i` be an event (the corridor) determined by the pairs
`T i`, increasing for an open arm and decreasing for a dual arm, and `Q i` a region. Suppose that

* the pairs read by the corridors have no end in the interior of `B_R(z)` (`hT`) and an end in
  `B_{R'}(z)` (`hT'`);
* the pairs of the corridor of arm `i`, its region `Q i` and the boxes of radius `M + 1` (`M' + 1`)
  about the possible ends `B i` (starts `B' i`) lie in a region `G i`, the regions of different
  arms being disjoint;
* `Q i` meets `Icc (z - R - 1) (z + R)` only near the possible ends of arm `i` and lies in the
  start box of `B_{R'}(z)` for the colour of arm `i` (`hQloc`, `hQin`), and the boxes of radius `M'`
  about the possible starts miss `Icc (z - R - 1) (z + R)` (`hB'loc`);
* on `C i`, every arm `γ` of colour `σ i` ending in `B i` and fenced and every arm `δ` of that
  colour starting in `B' i` and fenced are joined (`hhook`) by a walk of their colour from a vertex
  (face) of `γ` within `M` of its end, through the box of radius `M` about that end and `Q i`, to a
  point `w`, followed by a walk from `w` to a vertex (face) of `δ` inside the box of radius `M'`
  about its start.

Then `P(γ) · P(δ) · ∏ P(C i)` is at most the probability of `j` disjoint arms from `B_r(z)` to the
boundary of `B_{R₃}(z)`, in counterclockwise order, with inner positions in `J`. -/
theorem law_mul_mul_prod_le_law_of_two_sided (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' R₃ M' K' : ℕ} {s' : ℝ}
    (hKM : K ≤ M) (hM : 1 ≤ M) (hK'M' : K' ≤ M') (hM' : 1 ≤ M')
    (hrM : r + M + 1 < R) (hRR' : R + M + K + 1 + M' + K' + 1 < R') (hR'R₃ : R' + M' + 1 < R₃)
    (hs : 2 * (M : ℝ) + 1 ≤ s) (hs' : 2 * (M' : ℝ) + 2 ≤ s')
    (B B' : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ)
    (C : Fin j → Set (Config (LatticeSite 2))) (T : Fin j → Set (Sym2 (LatticeSite 2)))
    (Q G : Fin j → Set (LatticeSite 2))
    (hCm : ∀ i, MeasurableSet (C i))
    (hCT : ∀ i (ω ω' : Config (LatticeSite 2)), ω ∩ T i = ω' ∩ T i → (ω ∈ C i ↔ ω' ∈ C i))
    (hCmono : ∀ i (ω ω' : Config (LatticeSite 2)), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω →
      ω ∈ C i → ω' ∈ C i)
    (hT : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hT' : ∀ i, ∀ e ∈ T i, ∃ v ∈ e, v ∈ Icc (z - (R' : LatticeSite 2)) (z + R'))
    (hTG : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∈ G i)
    (hBG : ∀ i, ∀ b ∈ B i,
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G i)
    (hB'G : ∀ i, ∀ a ∈ B' i,
      Icc (a - (M' : LatticeSite 2)) (a + ((M' + 1 : ℕ) : LatticeSite 2)) ⊆ G i)
    (hQG : ∀ i, Q i ⊆ G i) (hG : ∀ i k, i ≠ k → Disjoint (G i) (G k))
    (hQloc : ∀ i, ∀ b ∈ B i, ∀ v ∈ Q i, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
      v ∈ Icc (b - (M : LatticeSite 2)) (b + M))
    (hQin : ∀ i, Q i ⊆ cond (σ i) (Icc (z - (R' : LatticeSite 2)) (z + R'))
      (Icc (z - (R' : LatticeSite 2) - 1) (z + R')))
    (hB'loc : ∀ i, ∀ a ∈ B' i, ∀ v ∈ Icc (a - (M' : LatticeSite 2)) (a + M'),
      v ∉ Icc (z - (R : LatticeSite 2) - 1) (z + R))
    (hhook : ∀ i, ∀ ω ∈ C i, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
      ∀ (a' b' : LatticeSite 2) (δ : (zdGraph 2).Walk a' b'),
      IsArm ω (σ i) z R' (z - R₃) (z + R₃) δ → a' ∈ B' i → HasInnerFence ω (σ i) z R' M' K' δ →
      ∃ (x w x' : LatticeSite 2) (P₁ : (zdGraph 2).Walk x w) (P₂ : (zdGraph 2).Walk w x'),
        x ∈ γ.support ∧ x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧ x' ∈ δ.support ∧
        (∀ e ∈ P₁.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ e ∈ P₂.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ v ∈ P₁.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q i) ∧
        ∀ v ∈ P₂.support, v ∈ Icc (a' - (M' : LatticeSite 2)) (a' + M')) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} *
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z R' (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
        (landingPos (z - R₃) (z + R₃) (σ k) (γ k)) (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
      ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ B' i} *
    ∏ i, law q (C i) ≤ law q (multiArmEventIn σ z r R₃ J fun _ => univ) := by
  classical
  have hrR : r < R := by omega
  set D : Set (Sym2 (LatticeSite 2)) := {e | ∃ i, σ i = false ∧ e ∈ T i} with hD
  set Tall : Set (Sym2 (LatticeSite 2)) := {e | ∃ i, e ∈ T i} with hTall
  -- a pair read by the corridor of `k` inside the region of `i` is read by `i` only
  have hreg : ∀ i k e, e ∈ T k → (∀ v ∈ e, v ∈ G i) → k = i := by
    intro i k e he hei
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact eq_of_mem_of_mem_of_disjoint hG (hTG k e he v hv) (hei v hv)
  -- each corridor event is upper for the mixed order of `D`
  have hmix : ∀ i, ∀ ω ω' : Config (LatticeSite 2), ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D →
      ω ∈ C i → ω' ∈ C i := by
    intro i
    cases hc : σ i
    · refine mixed_of_determined_of_decreasing (hCT i) (fun ω ω' h => ?_)
        (fun e he => ⟨i, hc, he⟩)
      have := hCmono i ω ω'
      rw [hc] at this
      exact this h
    · refine mixed_of_determined_of_increasing (hCT i) (fun ω ω' h => ?_) ?_
      · have := hCmono i ω ω'
        rw [hc] at this
        exact this h
      · rw [disjoint_left]
        rintro e he ⟨k, hk, hek⟩
        have hki := hreg i k e hek (hTG i e he)
        rw [hki, hc] at hk
        simp at hk
  have hCI : ∀ ω ω' : Config (LatticeSite 2), ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D →
      ω ∈ ⋂ i, C i → ω' ∈ ⋂ i, C i := fun ω ω' h₁ h₂ hω =>
    mem_iInter.2 fun i => hmix i ω ω' h₁ h₂ (mem_iInter.1 hω i)
  have hCIT : ∀ ω ω' : Config (LatticeSite 2), ω ∩ Tall = ω' ∩ Tall →
      (ω ∈ ⋂ i, C i ↔ ω' ∈ ⋂ i, C i) := by
    intro ω ω' h
    simp only [mem_iInter]
    refine forall_congr' fun i => hCT i ω ω' ?_
    ext e
    have := Set.ext_iff.1 h e
    simp only [mem_inter_iff, hTall, mem_ofPred_eq] at this ⊢
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨(this.1 ⟨h₁, i, h₂⟩).1, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨(this.2 ⟨h₁, i, h₂⟩).1, h₂⟩
  have hCIm : MeasurableSet (⋂ i, C i) := MeasurableSet.iInter hCm
  have hprod : ∏ i, law q (C i) ≤ law q (⋂ i, C i) := by
    have := PercLib.Probability.prodBernoulli_prod_le_biInter_of_mixed q D Finset.univ
      (fun i _ => hmix i) (fun i _ => hCm i)
    simp only [Finset.mem_univ, iInter_true] at this
    exact this
  -- the two families are independent
  have hind := law_inter_eq_mul_of_separated (σ := σ) (z := z) (r := r) (s := s) (M := M)
    (K := K) (R := R) (R' := R') (s' := s') (M' := M') (K' := K') (lo := z - R₃) (hi := z + R₃)
    q hrR hRR' B B' J
  -- conditioning on both families
  have hTB : ∀ i, ∀ b ∈ B i, ∀ e ∈ Tall, (∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false) := by
    rintro i b hb e ⟨k, hk⟩ hbox
    have hki := hreg i k e hk fun v hv => hBG i b hb (hbox v hv)
    subst hki
    constructor
    · rintro ⟨l, hl, hel⟩
      rwa [← hreg k l e hel fun v hv => hBG k b hb (hbox v hv)]
    · intro hσk
      exact ⟨k, hσk, hk⟩
  have hTB' : ∀ i, ∀ a ∈ B' i, ∀ e ∈ Tall, (∀ v ∈ e, v ∈ Icc (a - (M' : LatticeSite 2))
      (a + ((M' + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false) := by
    rintro i a ha e ⟨k, hk⟩ hbox
    have hki := hreg i k e hk fun v hv => hB'G i a ha (hbox v hv)
    subst hki
    constructor
    · rintro ⟨l, hl, hel⟩
      rwa [← hreg k l e hel fun v hv => hB'G k a ha (hbox v hv)]
    · intro hσk
      exact ⟨k, hσk, hk⟩
  have hTi : ∀ e ∈ Tall, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
    rintro e ⟨k, hk⟩
    exact hT k e hk
  have hTo : ∀ e ∈ Tall, ∃ v ∈ e, v ∈ Icc (z - (R' : LatticeSite 2)) (z + R') := by
    rintro e ⟨k, hk⟩
    exact hT' k e hk
  have hcond := PercLib.Probability.prodBernoulli_mul_le_inter_of_mixed_of_determined q
    (T := Tall) (D := D) (fun ω ω' h₀ h₁ h₂ hω => by
      obtain ⟨⟨a, b, γ, hγ, hd, ho, hsep, hB, hJ⟩, ⟨a', b', δ, hδ, hd', ho', hsep', hB'⟩⟩ := hω
      obtain ⟨hγ', hsep₁⟩ := separated_of_mixed_of_forall_mem hKM hTi hTB h₀ h₁ h₂ hγ hsep hB
      obtain ⟨hδ', hsep₂⟩ :=
        innerSeparated_of_mixed_of_forall_mem hK'M' hM' hTo hTB' h₀ h₁ h₂ hδ hsep' hB'
      exact ⟨⟨a, b, γ, hγ', hd, ho, hsep₁, hB, hJ⟩, ⟨a', b', δ, hδ', hd', ho', hsep₂, hB'⟩⟩)
    hCI hCIT ((measurableSet_setOf_separated_forall_mem_innerPos σ z r R s M K B J).inter
      (measurableSet_setOf_innerSeparated_forall_mem σ z R' (z - R₃) (z + R₃) s' M' K' B')) hCIm
  refine (mul_le_mul' le_rfl hprod).trans ((hind ▸ hcond).trans (measure_mono ?_))
  -- the gluing
  rintro ω ⟨⟨⟨a, b, γ, hγ, hd, ho, hsep, hB, hJ⟩, ⟨a', b', δ, hδ, hd', ho', hsep', hB'⟩⟩, hωC⟩
  rw [mem_iInter] at hωC
  choose x w x' P₁ P₂ hx hxM hx' hP₁e hP₂e hP₁s hP₂s using fun i =>
    hhook i ω (hωC i) _ _ (γ i) (hγ i) (hB i) (hsep.2.2 i) _ _ (δ i) (hδ i) (hB' i) (hsep'.2.2 i)
  choose D₁ D₂ hD₁₂ using fun i => (⟨_, _, SimpleGraph.Walk.take_spec _ (hx' i)⟩ :
    ∃ (D₁ : (zdGraph 2).Walk (a' i) (x' i)) (D₂ : (zdGraph 2).Walk (x' i) (b' i)),
      D₁.append D₂ = δ i)
  have hR'R₃' : R' < R₃ := by omega
  have hBo : Icc (z - (R' : LatticeSite 2)) (z + R') ⊆ Icc (z - R₃ + 1) (z + R₃ - 1) :=
    Icc_subset_Icc_add_one_sub_one hR'R₃'
  have hcrδ := fun i => isArm_iff_cond.1 (hδ i)
  have hD₂ : ∀ i, ∀ v ∈ (D₂ i).support, v ∈ (δ i).support := fun i v hv => by
    rw [← hD₁₂ i, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  -- the start box of the second family contains the boxes about the ends of the first
  have hbS : ∀ i, ∀ v ∈ Icc (b i - (M : LatticeSite 2)) (b i + M),
      v ∈ cond (σ i) (Icc (z - (R' : LatticeSite 2)) (z + R'))
        (Icc (z - (R' : LatticeSite 2) - 1) (z + R')) := by
    intro i v hv
    have hb := (hγ i).end_mem_Icc (Icc_subset_Icc_add_one_sub_one hrR)
    rw [mem_Icc_two_iff] at hb hv
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hb hv
    cases σ i <;> simp only [Bool.cond_true, Bool.cond_false] <;> rw [mem_Icc_two_iff] <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] <;> omega
  have hS₁ : ∀ i, ∀ v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R),
      v ∈ cond (σ i) (Icc (z - (R' : LatticeSite 2)) (z + R'))
        (Icc (z - (R' : LatticeSite 2) - 1) (z + R')) := by
    intro i v hv
    rw [mem_Icc_two_iff] at hv
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv
    cases σ i <;> simp only [Bool.cond_true, Bool.cond_false] <;> rw [mem_Icc_two_iff] <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] <;> omega
  have hbox' : ∀ i, a' i ∈ Icc (a' i - (M' : LatticeSite 2)) (a' i + M') := fun i => by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  -- the joined walks lie in the regions
  have hP₁G : ∀ i, ∀ v ∈ (P₁ i).support, v ∈ G i := fun i v hv =>
    (hP₁s i v hv).elim (fun h => hBG i (b i) (hB i) (Icc_sub_add_subset_Icc_sub_add_succ _ _ h))
      (fun h => hQG i h)
  have hP₂G : ∀ i, ∀ v ∈ (P₂ i).support, v ∈ G i := fun i v hv =>
    hB'G i (a' i) (hB' i) (Icc_sub_add_subset_Icc_sub_add_succ _ _ (hP₂s i v hv))
  have ha'G : ∀ i, a' i ∈ G i := fun i =>
    hB'G i (a' i) (hB' i) (Icc_sub_add_subset_Icc_sub_add_succ _ _ (hbox' i))
  -- integer separation of the two families
  have hsepZ : ∀ i k, i ≠ k → 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)| := by
    intro i k hik
    have h₁ := hsep.1 i k hik
    have h₂ : (2 * M + 1 : ℝ) ≤ ((|landingPos (z - R) (z + R) (σ i) (γ i) -
        landingPos (z - R) (z + R) (σ k) (γ k)| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      linarith
    have h₃ : (2 * M + 1 : ℤ) ≤ |landingPos (z - R) (z + R) (σ i) (γ i) -
        landingPos (z - R) (z + R) (σ k) (γ k)| := by exact_mod_cast h₂
    omega
  have hcorZ : ∀ i (m : ℕ), 2 * (M : ℤ) <
      |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| := by
    intro i m
    have h₁ := hsep.2.1 i m
    have h₂ : (2 * M + 1 : ℝ) ≤
        ((|landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      push_cast at h₁
      linarith
    have h₃ : (2 * M + 1 : ℤ) ≤ |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| := by
      exact_mod_cast h₂
    omega
  have hsepZ' : ∀ i k, i ≠ k → 2 * (M' : ℤ) <
      |innerPos z R' (σ i) (δ i) - innerPos z R' (σ k) (δ k)| := by
    intro i k hik
    have h₁ := hsep'.1 i k hik
    have h₂ : (2 * M' + 2 : ℝ) ≤
        ((|innerPos z R' (σ i) (δ i) - innerPos z R' (σ k) (δ k)| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      linarith
    have h₃ : (2 * M' + 2 : ℤ) ≤ |innerPos z R' (σ i) (δ i) - innerPos z R' (σ k) (δ k)| := by
      exact_mod_cast h₂
    omega
  have hcorZ' : ∀ i (m : ℕ), 2 * (M' : ℤ) + 1 <
      |innerPos z R' (σ i) (δ i) - m * (4 * R' + 2)| := by
    intro i m
    have h₁ := hsep'.2.1 i m
    have h₂ : (2 * M' + 2 : ℝ) ≤
        ((|innerPos z R' (σ i) (δ i) - m * (4 * R' + 2)| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      push_cast at h₁
      linarith
    have h₃ : (2 * M' + 2 : ℤ) ≤ |innerPos z R' (σ i) (δ i) - m * (4 * R' + 2)| := by
      exact_mod_cast h₂
    omega
  -- the joined walk of an arm of the first family misses the other arms of the second family
  have hFδ : ∀ i k, i ≠ k → σ i = σ k → ∀ v, (v ∈ (P₁ i).support ∨ v ∈ (P₂ i).support) →
      v ∉ (δ k).support := by
    intro i k hik hσik v hv hvk
    rcases hv with hv | hv
    · have hvS : v ∈ cond (σ k) (Icc (z - (R' : LatticeSite 2)) (z + R'))
          (Icc (z - (R' : LatticeSite 2) - 1) (z + R')) := by
        rw [← hσik]
        rcases hP₁s i v hv with h | h
        · exact hbS i v h
        · exact hQin i h
      have hva : v = a' k := by
        rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at hvk
        rcases hvk with h | h
        · exact h
        · exact absurd hvS ((hcrδ k).1.notMem_of_mem_tail v h)
      exact hik (eq_of_mem_of_mem_of_disjoint hG (hP₁G i v hv) (hva ▸ ha'G k))
    · refine notMem_support_of_subset_Icc_start hσ hR'R₃ hδ hd' ho' hsepZ' hcorZ' hik hσik
        (P₂ i).reverse (hx' i) (fun e he => ?_) (fun y hy => ?_) v ?_ hvk
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
        exact hP₂e i e he
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
        exact hP₂s i y hy
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
        exact hv
  -- arms of the second family of one colour are disjoint, also at their starts
  have hδδ : ∀ i k, i ≠ k → σ i = σ k → ∀ v ∈ (δ i).support, v ∉ (δ k).support := by
    intro i k hik hσik v hvi hvk
    cases hc : σ i
    · exact hd'.2 i k hik hc (hσik ▸ hc) v hvi hvk
    · have hck : σ k = true := hσik ▸ hc
      have hvi' := hvi
      have hvk' := hvk
      rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at hvi' hvk'
      rcases hvi' with rfl | hti
      · rcases hvk' with hvk' | htk
        · exact hik (eq_of_mem_of_mem_of_disjoint hG (ha'G i) (hvk' ▸ ha'G k))
        · exact hd'.1 k i hik.symm hck hc _ htk hvi
      · exact hd'.1 i k hik hc hck v hti hvk
  -- the gluing
  obtain ⟨b'', γ', hγ', hd'', ho'', hin, -⟩ := exists_isArm_of_glue (R' := R₃) hσ hrM
    (by omega) hγ hd ho hsepZ hcorZ (fun i => (P₁ i).append ((P₂ i).append (D₂ i))) hx hxM
    (fun i e he => by
      rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append, List.mem_append,
        List.mem_append] at he
      rcases he with he | he | he
      · exact hP₁e i e he
      · exact hP₂e i e he
      · refine (hcrδ i).2 e ?_
        rw [← hD₁₂ i, SimpleGraph.Walk.edges_append]
        exact List.mem_append_right _ he)
    (fun i v hv hvR => by
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv | hv
      · rcases hP₁s i v hv with h | h
        · exact h
        · exact hQloc i (b i) (hB i) v h hvR
      · exact absurd hvR (hB'loc i (a' i) (hB' i) v (hP₂s i v hv))
      · have hvδ := hD₂ i v hv
        rw [← SimpleGraph.Walk.cons_tail_support, List.mem_cons] at hvδ
        rcases hvδ with rfl | h
        · exact absurd hvR (hB'loc i (a' i) (hB' i) _ (hbox' i))
        · exact absurd (hS₁ i v hvR) ((hcrδ i).1.notMem_of_mem_tail v h))
    (fun i => (hcrδ i).1.end_notMem)
    (fun i k hik hσik v hvi hvk => by
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff] at hvi hvk
      rcases hvi with hvi | hvi | hvi <;> rcases hvk with hvk | hvk | hvk
      · exact hik (eq_of_mem_of_mem_of_disjoint hG (hP₁G i v hvi) (hP₁G k v hvk))
      · exact hik (eq_of_mem_of_mem_of_disjoint hG (hP₁G i v hvi) (hP₂G k v hvk))
      · exact hFδ i k hik hσik v (Or.inl hvi) (hD₂ k v hvk)
      · exact hik (eq_of_mem_of_mem_of_disjoint hG (hP₂G i v hvi) (hP₁G k v hvk))
      · exact hik (eq_of_mem_of_mem_of_disjoint hG (hP₂G i v hvi) (hP₂G k v hvk))
      · exact hFδ i k hik hσik v (Or.inr hvi) (hD₂ k v hvk)
      · exact hFδ k i hik.symm hσik.symm v (Or.inl hvk) (hD₂ i v hvi)
      · exact hFδ k i hik.symm hσik.symm v (Or.inr hvk) (hD₂ i v hvi)
      · exact hδδ i k hik hσik v (hD₂ i v hvi) (hD₂ k v hvk))
  exact ⟨a, b'', γ', hγ', hd'', fun i => ⟨hin i ▸ hJ i, mem_univ _⟩, ho''⟩

end Corridors

/-! ### The two-sided gluing with straight corridors -/

section Main

variable {j : ℕ}

/-- **The two-sided gluing** (the gluing step of the lower half of quasi-multiplicativity, Nolin's
Proposition 17). For a colour sequence `σ` without packs and a ratio `A` there is `c₀ > 0` such
that for every law with crossing bounds `c` up to scale `L` the following holds. Let `γ` range over
the families of arms from `B_r(z)` to the boundary of `B_R(z)` separated at the outer boundary
(separation `s ≥ 2M + 1`, fences `(M, K)`), with inner positions in `J` and ends in windows
`[α i, β i]` on the sides `t i` of `B_R(z)` (`0` top, `1` right, `2` bottom, `3` left, side
coordinates as in `exists_pos_le_law_windows_of_moves`), and `δ` over the families of arms from
`B_{R'}(z)` to the boundary of `B_{R₃}(z)` separated at the inner boundary (separation
`s' ≥ 2M' + 2`, fences `(M', K')`), with starts in windows `[α' i, β' i]` on the same sides `t i`
of `B_{R'}(z)`. Suppose that each pair of windows is aligned with a corridor `[x i, x i + W]`
spanned by both fences (`β i ≤ x i + K`, `x i + W ≤ α i + K`, and the same with `K'`), that the
corridors are at least `2S` from the corners of `B_R(z)` and, on one side, more than `W + 2S`
apart, where `S ≥ M + K + M' + K' + 2`, and `W ≤ K ≤ M`, `W ≤ K' ≤ M'`,
`R + M + K + M' + K' + 2 < R'`, `R' + M' + 1 < R₃`, `R' ≤ R + A W`. Then
`c₀ · P(γ) · P(δ) ≤ P(j arms from B_r(z) to ∂B_{R₃}(z) with inner positions in J)`,
with `c₀ = c A ^ j`: one straight corridor of width `W` and length `R' - R ≤ A W` per arm. -/
theorem exists_pos_le_law_two_sided (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' R₃ W M K M' K' S : ℕ) (s s' : ℝ)
      (J : Fin j → Set ℤ) (t : Fin j → Fin 4) (x α β α' β' : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → W ≤ K' → K' ≤ M' → M + K + M' + K' + 2 ≤ S →
      2 * (M : ℝ) + 1 ≤ s → 2 * (M' : ℝ) + 2 ≤ s' →
      r + M + 1 < R → R + M + K + 1 + M' + K' + 1 < R' → R' + M' + 1 < R₃ →
      R' ≤ R + A * W → (W : ℕ∞) ≤ L →
      (∀ i, β i ≤ x i + K ∧ x i + W ≤ α i + K ∧ β' i ≤ x i + K' ∧ x i + W ≤ α' i + K') →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + 2 * S ≤ x i ∧
        x i + W + 2 * S ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      (∀ i k, i ≠ k → t i = t k → x i + W + 2 * S < x k ∨ x k + W + 2 * S < x i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} *
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z R' (z - R₃) (z + R₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R₃) (z + R₃) (σ i) (γ i))
          (landingPos (z - R₃) (z + R₃) (σ k) (γ k)) (landingPos (z - R₃) (z + R₃) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ {a : LatticeSite 2 |
          (t i = 0 ∧ a 1 = z 1 + R' ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
          (t i = 1 ∧ a 0 = z 0 + R' ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i) ∨
          (t i = 2 ∧ a 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
          (t i = 3 ∧ a 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i)}} ≤
      law q (multiArmEventIn σ z r R₃ J fun _ => univ) := by
  classical
  by_cases hc : 0 < c A
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  refine ⟨c A ^ j, ENNReal.pow_pos hc _, ?_⟩
  intro q L hCB z r R R' R₃ W M K M' K' S s s' J t x α β α' β' hW hWK hKM hWK' hK'M' hS hs hs'
    hrM hRR' hR'R₃ hA hWL hal hcor hgap
  have hM : 1 ≤ M := by omega
  have hM' : 1 ≤ M' := by omega
  have hc0 : ∀ i, t i = 0 ∨ t i = 2 → z 0 - R + 2 * S ≤ x i ∧ x i + W + 2 * S ≤ z 0 + R :=
    fun i h => by
      have := hcor i
      rwa [ite_eq_left h] at this
  have hc1 : ∀ i, t i = 1 ∨ t i = 3 → z 1 - R + 2 * S ≤ x i ∧ x i + W + 2 * S ≤ z 1 + R :=
    fun i h => by
      have hn : ¬(t i = 0 ∨ t i = 2) := by omega
      have := hcor i
      rwa [ite_eq_right hn] at this
  choose dir lo hi gl gh hside using fun i =>
    exists_two_sided_side (t i) (σ i) z R R' M M' W S (x i)
  have hfacts := fun i => two_sided_side_facts (α := α i) (β := β i) (α' := α' i) (β' := β' i)
    hW hWK hKM hWK' hK'M' hS hRR' (hside i) (hc0 i) (hc1 i) (hal i)
  have hmain := law_mul_mul_prod_le_law_of_two_sided (σ := σ) (z := z) (r := r) (R := R) (s := s)
    (M := M) (K := K) (R' := R') (R₃ := R₃) (M' := M') (K' := K') (s' := s') q hσ hKM hM hK'M' hM'
    hrM hRR' hR'R₃ hs hs'
    (fun i => {b : LatticeSite 2 |
      (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
      (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
      (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
      (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)})
    (fun i => {a : LatticeSite 2 |
      (t i = 0 ∧ a 1 = z 1 + R' ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
      (t i = 1 ∧ a 0 = z 0 + R' ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i) ∨
      (t i = 2 ∧ a 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
      (t i = 3 ∧ a 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i)}) J
    (fun i => (fun ω : Config (LatticeSite 2) => cond (σ i) ω (dualConfig ω)) ⁻¹'
      crossing (dir i) (lo i) (hi i))
    (fun i => {e : Sym2 (LatticeSite 2) | (∀ v ∈ e, v ∈ Icc (lo i) (hi i + cond (σ i) 0 1)) ∧
      (∃ v ∈ e, v ∈ Icc (lo i) (hi i)) ∧
      ∃ v ∈ e, v ∈ Icc (lo i + cond (σ i) 0 1) (hi i + cond (σ i) 0 1)})
    (fun i => Icc (lo i) (hi i)) (fun i => Icc (gl i) (gh i))
    (fun i => measurableSet_preimage_cond_crossing (σ i) (dir i) (lo i) (hi i))
    (fun i ω ω' h => cond_mem_crossing_iff_of_agree (σ i) (dir i) (lo i) (hi i)
      fun e h₁ h₂ h₃ => by
        have := Set.ext_iff.1 h e
        exact ⟨fun he => (this.1 ⟨he, h₁, h₂, h₃⟩).1, fun he => (this.2 ⟨he, h₁, h₂, h₃⟩).1⟩)
    (fun i ω ω' h hω => cond_mem_crossing_of_cond_subset h hω)
    (fun i e he v hv => (hfacts i).1 v (he.1 v hv))
    (fun i e he => (hfacts i).2.1.elim
      (fun h => by
        obtain ⟨v, hv, hv'⟩ := he.2.1
        exact ⟨v, hv, h v hv'⟩)
      (fun h => by
        obtain ⟨v, hv, hv'⟩ := he.2.2
        exact ⟨v, hv, h v hv'⟩))
    (fun i e he v hv => (hfacts i).2.2.1 v (he.1 v hv))
    (fun i b hb => ((hfacts i).2.2.2.2.2.1 b hb).1)
    (fun i a ha => ((hfacts i).2.2.2.2.2.2 a ha).1)
    (fun i v hv => (hfacts i).2.2.2.1 v hv)
    (fun i k hik => disjoint_two_sided_regions (by omega) (by omega) (hside i) (hside k) (hc0 i)
      (hc1 i) (hc0 k) (hc1 k) (hgap i k hik))
    (fun i b hb v hv hvR => ((hfacts i).2.2.2.2.2.1 b hb).2 v hv hvR)
    (fun i v hv => (hfacts i).2.2.2.2.1 v hv)
    (fun i a ha => ((hfacts i).2.2.2.2.2.2 a ha).2)
    (fun i ω hω a b γ _ hb hf a' b' δ _ ha hf' => exists_walks_two_sided hW hWK hKM hWK' hK'M'
      hS hRR' (hside i) (hc0 i) (hc1 i) (hal i) hω hb ha hf hf')
  have hprod : c A ^ j ≤ ∏ i, law q ((fun ω : Config (LatticeSite 2) =>
      cond (σ i) ω (dualConfig ω)) ⁻¹' crossing (dir i) (lo i) (hi i)) := by
    calc c A ^ j = ∏ _i : Fin j, c A := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod fun i _ =>
          hCB.le_law_two_sided_side hW hWL (by omega) hA (hside i)
  calc c A ^ j * law q _ * law q _ = law q _ * law q _ * c A ^ j := by ring
    _ ≤ _ := mul_le_mul' le_rfl hprod
    _ ≤ _ := hmain

/-- **The lower half of quasi-multiplicativity, modulo the separation of both families.** For a
colour sequence `σ` without packs and a ratio `A` there is `c₀ > 0` such that for every law with
crossing bounds `c` up to scale `L`: if the arms of the annulus `(r₁, r₂)` can be chosen separated
at the outer boundary of `B_R(z)` with ends in the windows `[α i, β i]`, at a cost `C₁`
(`P(A(r₁, r₂)) ≤ C₁ P(separated)`), and the arms of the annulus `(r₂, r₃)` can be chosen separated
at the inner boundary of `B_{R'}(z)` with starts in the windows `[α' i, β' i]`, at a cost `C₂`, the
windows and the parameters being as in `exists_pos_le_law_two_sided`, then
`c₀ · P(A(r₁, r₂)) · P(A(r₂, r₃)) ≤ C₁ C₂ · P(A(r₁, r₃))`. Theorem 11 (outer and inner halves) and
the alignment of the windows provide the two hypotheses; they are taken here as plain
inequalities. -/
theorem exists_pos_mul_le_of_separated_of_separated (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r₁ r₂ r₃ R R' W M K M' K' S : ℕ) (s s' : ℝ)
      (t : Fin j → Fin 4) (x α β α' β' : Fin j → ℤ) (C₁ C₂ : ℝ≥0∞),
      1 ≤ W → W ≤ K → K ≤ M → W ≤ K' → K' ≤ M' → M + K + M' + K' + 2 ≤ S →
      2 * (M : ℝ) + 1 ≤ s → 2 * (M' : ℝ) + 2 ≤ s' →
      r₁ + M + 1 < R → R + M + K + 1 + M' + K' + 1 < R' → R' + M' + 1 < r₃ →
      R' ≤ R + A * W → (W : ℕ∞) ≤ L →
      (∀ i, β i ≤ x i + K ∧ x i + W ≤ α i + K ∧ β' i ≤ x i + K' ∧ x i + W ≤ α' i + K') →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + 2 * S ≤ x i ∧
        x i + W + 2 * S ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      (∀ i k, i ≠ k → t i = t k → x i + W + 2 * S < x k ∨ x k + W + 2 * S < x i) →
      law q (multiArmEvent σ z r₁ r₂) ≤ C₁ * law q {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r₁ (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r₁ (σ i) (γ i) ∈ (univ : Set ℤ)} →
      law q (multiArmEvent σ z r₂ r₃) ≤ C₂ * law q {ω : Config (LatticeSite 2) |
        ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z R' (z - r₃) (z + r₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - r₃) (z + r₃) (σ i) (γ i))
          (landingPos (z - r₃) (z + r₃) (σ k) (γ k)) (landingPos (z - r₃) (z + r₃) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ {a : LatticeSite 2 |
          (t i = 0 ∧ a 1 = z 1 + R' ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
          (t i = 1 ∧ a 0 = z 0 + R' ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i) ∨
          (t i = 2 ∧ a 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
          (t i = 3 ∧ a 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i)}} →
      c₀ * (law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃)) ≤
        C₁ * C₂ * law q (multiArmEvent σ z r₁ r₃) := by
  obtain ⟨c₀, hc₀, h⟩ := exists_pos_le_law_two_sided σ hσ c A
  refine ⟨c₀, hc₀, ?_⟩
  intro q L hCB z r₁ r₂ r₃ R R' W M K M' K' S s s' t x α β α' β' C₁ C₂ hW hWK hKM hWK' hK'M' hS
    hs hs' hrM hRR' hR'r₃ hA hWL hal hcor hgap h₁ h₂
  have hglue : c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r₁ (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
            (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
            (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
            (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
            (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
            (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
          ∀ i, innerPos z r₁ (σ i) (γ i) ∈ (univ : Set ℤ)} *
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z R' (z - r₃) (z + r₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - r₃) (z + r₃) (σ i) (γ i))
            (landingPos (z - r₃) (z + r₃) (σ k) (γ k)) (landingPos (z - r₃) (z + r₃) (σ l) (γ l))) ∧
          ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ {a : LatticeSite 2 |
            (t i = 0 ∧ a 1 = z 1 + R' ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
            (t i = 1 ∧ a 0 = z 0 + R' ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i) ∨
            (t i = 2 ∧ a 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
            (t i = 3 ∧ a 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i)}} ≤
      law q (multiArmEvent σ z r₁ r₃) :=
    h q L hCB z r₁ R R' r₃ W M K M' K' S s s' (fun _ => univ) t x α β α' β' hW hWK hKM
      hWK' hK'M' hS hs hs' hrM hRR' hR'r₃ hA hWL hal hcor hgap
  calc c₀ * (law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃))
      ≤ c₀ * ((C₁ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
            (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
            (∀ i, IsArm ω (σ i) z r₁ (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
              (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
            ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
              (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
              (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
              (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
              (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
            ∀ i, innerPos z r₁ (σ i) (γ i) ∈ (univ : Set ℤ)}) *
        (C₂ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
            (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
            (∀ i, IsArm ω (σ i) z R' (z - r₃) (z + r₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i k l, i < k → k < l → sbtw (landingPos (z - r₃) (z + r₃) (σ i) (γ i))
              (landingPos (z - r₃) (z + r₃) (σ k) (γ k))
                (landingPos (z - r₃) (z + r₃) (σ l) (γ l))) ∧
            ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ {a : LatticeSite 2 |
              (t i = 0 ∧ a 1 = z 1 + R' ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
              (t i = 1 ∧ a 0 = z 0 + R' ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i) ∨
              (t i = 2 ∧ a 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
              (t i = 3 ∧ a 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i)}})) :=
        mul_le_mul' le_rfl (mul_le_mul' h₁ h₂)
    _ = C₁ * C₂ * (c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
            (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
            (∀ i, IsArm ω (σ i) z r₁ (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
              (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
            ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
              (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
              (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
              (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
              (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
            ∀ i, innerPos z r₁ (σ i) (γ i) ∈ (univ : Set ℤ)} *
        law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
            (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
            (∀ i, IsArm ω (σ i) z R' (z - r₃) (z + r₃) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i k l, i < k → k < l → sbtw (landingPos (z - r₃) (z + r₃) (σ i) (γ i))
              (landingPos (z - r₃) (z + r₃) (σ k) (γ k))
                (landingPos (z - r₃) (z + r₃) (σ l) (γ l))) ∧
            ArmsInnerSeparated ω σ z R' s' M' K' γ ∧ ∀ i, a i ∈ {a : LatticeSite 2 |
              (t i = 0 ∧ a 1 = z 1 + R' ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
              (t i = 1 ∧ a 0 = z 0 + R' ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i) ∨
              (t i = 2 ∧ a 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 0 ∧ a 0 ≤ β' i) ∨
              (t i = 3 ∧ a 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ a 1 ∧ a 1 ≤ β' i)}}) := by ring
    _ ≤ C₁ * C₂ * law q (multiArmEvent σ z r₁ r₃) := mul_le_mul' le_rfl hglue


end Main

end PercLib.Models.Planar
