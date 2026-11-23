/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.2, Definitions 6-8 and condition (4.5), and Section
4.4, Lemma 15 (local separation, p. 1579).
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecificLimits.Basic
public import PercLib.Models.Planar.Arms.SeparationEvents

/-!
# Local separation of crossings

Nolin's local separation lemma: in the strip `Q = [0, 4N] × [0, N]`, with probability close to
one, every family of disjoint crossings of `Q` from bottom to top, open or dual, can be replaced
by a family with the same colours and the same starting points whose top ends are well separated
from each other and from the two top corners, and each of which carries a fence: a crossing of the
same colour of a small box above its end, joined to the crossing inside a ball around its end.

The proof runs one greedy exploration for each colour: of the open configuration in `Q`, and of
the dual configuration in the box of faces `[0, 4N - 1] × [-1, N]`. Each family of crossings of one
colour is rerouted to tips of greedy crossings of its colour (`exists_reroute_of_exploration`), and
with high probability every greedy tip is protected: no greedy tip of the same colour and no
crossing of the other colour lands close to it on its right, and it carries a fence; the two top
corners are protected too. Separation of tips of different colours uses the protection of the
left one against the other colour, applied to the greedy crossing of the right one, trimmed
(`exists_walk_trim`) or translated by `(-1, -1)` into the dual box of the left one's
exploration.

The constants: `T` steps of the explorations, `J` scales, `D = 16 · 8^J`, `η = 1 / D²`,
`N₀ = D²`; with `M = ⌊N / D⌋ = ⌊√η N⌋` and `K = ⌊N / D²⌋ = ⌊η N⌋`, the separation and corner
scales are `2 (M + 1) 8^j` and the fence scales `(K + 1) 8^j`, `j < J`. The lemma fails for small
`N` (the corners cannot be protected), so the statement has `N₀ ≤ N`.

The same proof works when the box of faces is one column wider on each side than the open box,
`[0, 4N + 1] × [-1, N]` around the open box `[1, 4N + 1] × [0, N]`: this is how the open and the
dual arms of a box of radius `2N + 1` meet a strip along its top side, so this form
(`exists_law_separable_ge_arm`) is the one that fits the arms. Both forms are instances of
`exists_law_separable_ge_aux`, and the new crossings meet the top row only at their ends.

## Main results

* `exists_fence_of_le`: a fence of the fence lemma gives a fence in a narrower box.
* `exists_reroute_fence_of_exploration`: a family of crossings of one colour is rerouted to greedy
  tips, each with a fence.
* `exists_walk_trim`, `add_lt_of_exploration_of_dualConfig`, `add_lt_of_exploration_dualConfig`:
  separation of tips of different colours.
* `lt_tip_of_corner`, `lt_abs_sub_of_exploration`: greedy tips away from the corners and from each
  other.
* `separable_of_forall`: the deterministic part of the lemma, for both geometries.
* `exists_law_separable_ge_aux`: the lemma for a strip of either geometry.
* `exists_law_separable_ge`: **Nolin's local separation lemma.**
* `exists_law_separable_ge_arm`: **the lemma in the geometry of the arms of a box.**
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Fences in a narrower box -/

/-- **A fence in a narrower box.** A left-right crossing of the box `[z₀ - 3t, z₀ + 3t + 1] ×
[z₁ + t + 1, z₁ + 3t]` whose left end is joined to `x` inside `[z₀ - 3t, z₀ + 3t + 1] ×
[z₁ - 3t, z₁ + 3t + 1]` gives, for `K ≤ 3t` and `3t + 1 ≤ M`, a left-right crossing of the fence
box `[z₀ - K, z₀ + K] × [z₁, z₁ + M]` whose left end is joined to `x` inside the ball of radius `M`
around `z`. -/
theorem exists_fence_of_le {G : Config (LatticeSite 2)} {z x l r : LatticeSite 2} {t K M : ℕ}
    (hK : K ≤ 3 * t) (hM : 3 * t + 1 ≤ M) (hl : l 0 = z 0 - 3 * t) (hr : r 0 = z 0 + 3 * t + 1)
    (hlr : G ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (z + ![-3 * (t : ℤ), t + 1]) (z + ![3 * (t : ℤ) + 1, 3 * t])) l r)
    (hxl : G ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ) + 1, 3 * t + 1])) x l) :
    ∃ l' r' : LatticeSite 2, l' 0 = z 0 - K ∧ r' 0 = z 0 + K ∧
      G ∩ (zdGraph 2).edgeSet ∈ localConn (Icc ![z 0 - K, z 1] ![z 0 + K, z 1 + M]) l' r' ∧
      G ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc (z - (M : LatticeSite 2)) (z + (M : LatticeSite 2))) x l' := by
  classical
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hlr
  have hf : ∀ u v, (openGraph (G ∩ (zdGraph 2).edgeSet)).Adj u v → v 0 ≤ u 0 + 1 :=
    fun u v h => apply_le_apply_add_one_of_adj ((openGraph_adj_iff _ _ _).1 h).1.2 0
  obtain ⟨u', w', hu', hw', q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc
    (fun v : LatticeSite 2 => v 0) hf p (s := z 0 - K) (t := z 0 + K)
    (show l 0 ≤ z 0 - K by omega) (by omega) (show z 0 + K ≤ r 0 by omega)
  have hball : ∀ v ∈ Icc (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ) + 1, 3 * t + 1]),
      v ∈ Icc (z - (M : LatticeSite 2)) (z + (M : LatticeSite 2)) := fun v hv => by
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hv ⊢
    omega
  have htop : ∀ v ∈ Icc (z + ![-3 * (t : ℤ), t + 1]) (z + ![3 * (t : ℤ) + 1, 3 * t]),
      v ∈ Icc (z + ![-3 * (t : ℤ), -3 * t]) (z + ![3 * (t : ℤ) + 1, 3 * t + 1]) := fun v hv => by
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
    omega
  refine ⟨u', w', hu', hw', mem_localConn_iff_exists_walk.2 ⟨q, fun v hv => ?_⟩, ?_⟩
  · obtain ⟨hvp, h₁, h₂⟩ := hq v hv
    have := mem_Icc_two_iff.1 (hp v hvp)
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this h₁ h₂
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have hu'p : u' ∈ p.support := (hq u' q.start_mem_support).1
    have hlu : G ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc (z - (M : LatticeSite 2)) (z + (M : LatticeSite 2))) l u' :=
      mem_localConn_iff_exists_walk.2 ⟨p.takeUntil u' hu'p, fun v hv =>
        hball v (htop v (hp v (p.support_takeUntil_subset_support hu'p hv)))⟩
    exact localConn_trans (localConn_mono_set hball x l hxl) hlu

/-! ### Rerouting a family of one colour, with fences -/

section Greedy

variable {lo hi : LatticeSite 2} {G : Config (LatticeSite 2)}
  {c d : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- **Rerouting to greedy tips with fences.** Let `A` be the exploration of `G` up to a step `u`
where it reaches the right column, for a clean choice rule. Suppose that each admissible step
`v < u` has a fence annulus at its tip (`G` with the explored edges added crosses the four boxes of
an annulus of scale `t` with `K ≤ 3t`, `3t + 1 ≤ M`, fitting in the box). Then every finite family
of disjoint bottom-top crossings of the box open in `G` is rerouted to walks from the same starts
to distinct admissible greedy tips, inside the box, along edges of the members and of the greedy
crossings, pairwise disjoint, meeting the top row only at their ends, and each new walk has a
vertex `x` joined inside the ball of radius `M` around its end to the left end of a left-right
crossing of the fence box `[z₀ - K, z₀ + K] × [z₁, z₁ + M]` above its end `z`. -/
theorem exists_reroute_fence_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    (hu : ∃ f ∈ A u, f 0 = hi 0) {K M : ℕ}
    (hfence : ∀ v < u, (∀ f ∈ A v, f 0 ≠ hi 0) → ∃ t : ℕ, 1 ≤ t ∧ K ≤ 3 * t ∧ 3 * t + 1 ≤ M ∧
      lo 0 + 3 * t ≤ d (A v) 0 ∧ d (A v) 0 + 3 * t + 1 ≤ hi 0 ∧ lo 1 + 3 * t ≤ hi 1 ∧
      G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 0 (d (A v) + ![-3 * (t : ℤ), t + 1]) (d (A v) + ![3 * (t : ℤ) + 1, 3 * t]) ∧
      G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 0 (d (A v) + ![-3 * (t : ℤ), -3 * t + 1]) (d (A v) + ![3 * (t : ℤ) + 1, -t]) ∧
      G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 1 (d (A v) + ![(t : ℤ) + 1, -3 * t]) (d (A v) + ![3 * (t : ℤ), 3 * t + 1]) ∧
      G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 1 (d (A v) + ![-3 * (t : ℤ) + 1, -3 * t]) (d (A v) + ![-(t : ℤ), 3 * t + 1]))
    {ι : Type*} (S : Finset ι) {a b : ι → LatticeSite 2} (γ : ∀ i, (zdGraph 2).Walk (a i) (b i))
    (hγ : ∀ i ∈ S, ∀ x ∈ (γ i).support, x ∈ Icc lo hi) (ha : ∀ i ∈ S, a i 1 = lo 1)
    (hb : ∀ i ∈ S, b i 1 = hi 1) (hγG : ∀ i ∈ S, ∀ e ∈ (γ i).edges, e ∈ G)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) :
    ∃ (w : ι → ℕ) (γ' : ∀ i, Σ y : LatticeSite 2, (zdGraph 2).Walk (a i) y),
      (∀ i ∈ S, w i < u ∧ (∀ f ∈ A (w i), f 0 ≠ hi 0) ∧ (γ' i).1 = d (A (w i))) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → w i ≠ w j) ∧
      (∀ i ∈ S, ∀ x ∈ (γ' i).2.support, x ∈ Icc lo hi) ∧
      (∀ i ∈ S, ∀ e ∈ (γ' i).2.edges, e ∈ G) ∧
      (∀ i ∈ S, ∀ e ∈ (γ' i).2.edges, e ∈ (γ i).edges ∨ e ∈ (Γ (A (w i))).edges) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ (γ' i).2.support, x ∉ (γ' j).2.support) ∧
      (∀ i ∈ S, ∀ x ∈ (γ' i).2.support.dropLast, x 1 ≠ hi 1) ∧
      ∀ i ∈ S, ∃ x ∈ (γ' i).2.support, ∃ l r : LatticeSite 2,
        l 0 = (γ' i).1 0 - K ∧ r 0 = (γ' i).1 0 + K ∧
        G ∩ (zdGraph 2).edgeSet ∈
          localConn (Icc ![(γ' i).1 0 - K, hi 1] ![(γ' i).1 0 + K, hi 1 + M]) l r ∧
        G ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ((γ' i).1 - (M : LatticeSite 2)) ((γ' i).1 + (M : LatticeSite 2))) x l := by
  classical
  -- clean the members: cut each at its first vertex on the top row
  have hcl : ∀ i, ∃ y : LatticeSite 2, ∃ q : (zdGraph 2).Walk (a i) y, i ∈ S →
      y 1 = hi 1 ∧ (∀ x ∈ q.support.dropLast, x 1 ≠ hi 1) ∧
        (∀ x ∈ q.support, x ∈ (γ i).support) ∧ ∀ e ∈ q.edges, e ∈ (γ i).edges := by
    intro i
    by_cases hiS : i ∈ S
    · obtain ⟨y, q, s, hqs, hy, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
        (T := {x : LatticeSite 2 | x 1 ≠ hi 1}) (γ i) (fun h => h (hb i hiS))
      refine ⟨y, q, fun _ => ⟨not_not.1 hy, fun x hx => hq x hx, fun x hx => ?_, fun e he => ?_⟩⟩
      · rw [← hqs]
        exact (SimpleGraph.Walk.mem_support_append_iff q s).2 (Or.inl hx)
      · rw [← hqs, SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ he
    · exact ⟨a i, .nil, fun h => absurd h hiS⟩
  choose bc γc hγc using hcl
  obtain ⟨w, γ', hw, -, hwd, -, hG, hbox, hdisj', hdrop, hopen, hedge, htopd⟩ :=
    exists_reroute_of_exploration h1 hle (fun A' h₁ h₂ => (hΓ A' h₁ h₂).1) hA hu S γc
      (fun i hi x hx => hγ i hi x ((hγc i hi).2.2.1 x hx)) ha (fun i hi => (hγc i hi).1)
      (fun i hi e he => hγG i hi e ((hγc i hi).2.2.2 e he))
      fun i hi j hj hij x hx hx' =>
        hdisj i hi j hj hij x ((hγc i hi).2.2.1 x hx) ((hγc j hj).2.2.1 x hx')
  refine ⟨w, γ', hw, hwd, hbox, hG, fun i hi e he => ?_, hdisj', fun i hi x hx hx1 => ?_,
    fun i hi => ?_⟩
  · rcases hedge i hi e he with h | h
    · exact Or.inl ((hγc i hi).2.2.2 e h)
    · exact Or.inr h
  · -- the top row is met only at the end
    obtain ⟨hwu, hadm, -⟩ := hw i hi
    obtain ⟨-, -, -, htopΓ⟩ := hΓ (A (w i)) (mem_leftColumn_of_exploration hA hwu.le) hadm
    rcases htopd i hi x hx with h | ⟨h, hne⟩
    · exact (hγc i hi).2.1 x h hx1
    · exact hne (htopΓ x h hx1)
  · obtain ⟨hwu, hadm, hend⟩ := hw i hi
    obtain ⟨t, ht, hKt, htM, hx₀, hx₁, hy₀, hT, hB, hR, hL⟩ := hfence (w i) hwu hadm
    obtain ⟨⟨-, -, -, hd1, -, -⟩, -, -, htopΓ⟩ :=
      hΓ (A (w i)) (mem_leftColumn_of_exploration hA hwu.le) hadm
    set γi : (zdGraph 2).Walk (a i) (d (A (w i))) := (γ' i).2.copy rfl hend with hγi
    have hγiS : ∀ x, x ∈ γi.support ↔ x ∈ (γ' i).2.support := fun x => by
      rw [hγi, SimpleGraph.Walk.support_copy]
    have hγiE : ∀ e, e ∈ γi.edges ↔ e ∈ (γ' i).2.edges := fun e => by
      rw [hγi, SimpleGraph.Walk.edges_copy]
    obtain ⟨x, hx, l, r, hl, hr, hlr, hxl⟩ := exists_fence_of_exploration h1 hle hA hwu.le hd1 ht
      hx₀ hx₁ hy₀ hT hB hR hL γi (fun x hx => hbox i hi x ((hγiS x).1 hx)) (ha i hi)
      (fun x hx hx1 => by
        rcases hdrop i hi x ((hγiS x).1 hx) with h | h
        · exact absurd hx1 ((hγc i hi).2.1 x h)
        · exact htopΓ x h hx1)
      fun e he => ⟨hG i hi e ((hγiE e).1 he), hopen i hi e ((hγiE e).1 he)⟩
    obtain ⟨l', r', hl', hr', hlr', hxl'⟩ := exists_fence_of_le hKt htM hl hr hlr hxl
    refine ⟨x, (hγiS x).1 hx, l', r', ?_, ?_, ?_, ?_⟩
    · rw [hend]
      exact hl'
    · rw [hend]
      exact hr'
    · rw [hend, ← hd1]
      exact hlr'
    · rw [hend]
      exact hxl'

end Greedy

/-! ### Separation of tips of different colours -/

/-- **Trimming a clean crossing.** A path `p` in the box `Icc lo hi`, with `lo 1 + 1 < hi 1`, from
its bottom row to its top row, meeting the bottom row only at its start and the top row only at
its end `b`, contains a walk from a vertex of the row `lo 1 + 1` to the vertex `(b₀, hi 1 - 1)`
below `b`, along edges of `p`, whose vertices lie in `Icc lo hi` between the rows `lo 1 + 1` and
`hi 1 - 1`. -/
theorem exists_walk_trim {lo hi a b : LatticeSite 2} (h : lo 1 + 1 < hi 1)
    (p : (zdGraph 2).Walk a b) (hp : p.IsPath) (hS : ∀ x ∈ p.support, x ∈ Icc lo hi)
    (ha : a 1 = lo 1) (hb : b 1 = hi 1) (hbot : ∀ x ∈ p.support, x 1 = lo 1 → x = a)
    (htop : ∀ x ∈ p.support, x 1 = hi 1 → x = b) :
    ∃ y : LatticeSite 2, ∃ q : (zdGraph 2).Walk y ![b 0, hi 1 - 1], y 1 = lo 1 + 1 ∧
      (∀ x ∈ q.support, x ∈ Icc ![lo 0, lo 1 + 1] ![hi 0, hi 1 - 1]) ∧
      ∀ e ∈ q.edges, e ∈ p.edges := by
  -- the last vertex `c` of `p` below the top row
  obtain ⟨c, hc, q₁, s, hqs, hs⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
    (S := {x : LatticeSite 2 | x 1 ≤ hi 1 - 1}) p ⟨a, p.start_mem_support, by
      change a 1 ≤ hi 1 - 1
      omega⟩
  change c 1 ≤ hi 1 - 1 at hc
  have hsubp : ∀ x ∈ q₁.support, x ∈ p.support := fun x hx => by
    rw [← hqs]
    exact (SimpleGraph.Walk.mem_support_append_iff q₁ s).2 (Or.inl hx)
  have hcb : c ≠ b := fun h => by
    rw [h] at hc
    omega
  obtain ⟨y₁, hcy, s', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hcb s
  -- the step after `c` lands on the top row, hence at `b`, directly above `c`
  have hy₁p : y₁ ∈ p.support := by
    rw [← hqs]
    exact (SimpleGraph.Walk.mem_support_append_iff q₁ _).2 (Or.inr (by simp))
  have hy₁ : y₁ = b := by
    refine htop y₁ hy₁p ?_
    have h₁ := hs y₁ (by simp)
    have h₂ := mem_Icc_two_iff.1 (hS y₁ hy₁p)
    change ¬y₁ 1 ≤ hi 1 - 1 at h₁
    omega
  subst hy₁
  have hcadj := (zdGraph_two_adj_iff _ _).1 hcy
  have hceq : c = ![y₁ 0, hi 1 - 1] := eq_vec_two_iff.2 ⟨by omega, by omega⟩
  -- the step after `a` lands on the row `lo 1 + 1`
  have hac : a ≠ c := fun h => by
    rw [h] at ha
    omega
  obtain ⟨y, hay, q', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hac q₁
  have hnd := hp.support_nodup
  rw [← hqs, SimpleGraph.Walk.support_append, List.nodup_append] at hnd
  have haq' : a ∉ q'.support := by
    have := hnd.1
    rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at this
    exact this.1
  have hbq' : ∀ x ∈ q'.support, x ≠ y₁ := fun x hx hxb => by
    subst hxb
    exact hnd.2.2 x (by simp [hx]) x (by simp) rfl
  have hrow : ∀ x ∈ q'.support, lo 1 + 1 ≤ x 1 ∧ x 1 ≤ hi 1 - 1 ∧ x ∈ Icc lo hi := by
    intro x hx
    have hxp := hsubp x (by simp [hx])
    have hxS := mem_Icc_two_iff.1 (hS x hxp)
    have h₁ : x 1 ≠ lo 1 := fun h' => haq' (hbot x hxp h' ▸ hx)
    have h₂ : x 1 ≠ hi 1 := fun h' => hbq' x hx (htop x hxp h')
    exact ⟨by omega, by omega, hS x hxp⟩
  have hyrow := hrow y q'.start_mem_support
  have hayadj := (zdGraph_two_adj_iff _ _).1 hay
  refine ⟨y, q'.copy rfl hceq, by omega, fun x hx => ?_, fun e he => ?_⟩
  · rw [SimpleGraph.Walk.support_copy] at hx
    obtain ⟨h₁, h₂, h₃⟩ := hrow x hx
    have := mem_Icc_two_iff.1 h₃
    rw [mem_Icc_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [SimpleGraph.Walk.edges_copy] at he
    rw [← hqs, SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ (by simp [he])

section Greedy

variable {lo hi : LatticeSite 2} {c d : Finset (LatticeSite 2) → LatticeSite 2}
  {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- **An open tip protected against dual crossings.** Let `A v` be an admissible set of the
exploration of the open configuration `ω` in the box `Icc lo hi`, with the fresh part of the dual
configuration crossing none of the three strips of scale `s` around the face below the right of its
tip. A clean dual path `p` in the box of faces `[lo₀ - 1, hi₀] × [lo₁ - 1, hi₁]` (all faces touching
the box, with one more row below and above) from its bottom row to its top row, landing at or right
of the tip, lands more than `s` to its right. -/
theorem add_lt_of_exploration_of_dualConfig (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {ω : Config (LatticeSite 2)} {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (ω \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) (hvr : ∀ f ∈ A v, f 0 ≠ hi 0) {s : ℕ} (hs : 1 ≤ s)
    (hs3 : lo 1 + 3 * s ≤ hi 1 - 1)
    (hB : dualConfig (ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 1 (![d (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), -s]))
    (hR : dualConfig (ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 0 (![d (A v) 0, hi 1 - 1] + ![(s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), 3 * s]))
    (hL : dualConfig (ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 0 (![d (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![-(s : ℤ), 3 * s]))
    {a' b' : LatticeSite 2} (p : (zdGraph 2).Walk a' b') (hp : p.IsPath)
    (hpS : ∀ x ∈ p.support, x ∈ Icc (![lo 0 - 1, lo 1 - 1] : LatticeSite 2) ![hi 0, hi 1])
    (ha' : a' 1 = lo 1 - 1) (hb' : b' 1 = hi 1)
    (hbot : ∀ x ∈ p.support, x 1 = lo 1 - 1 → x = a')
    (htop : ∀ x ∈ p.support, x 1 = hi 1 → x = b')
    (hpG : ∀ e ∈ p.edges, e ∈ dualConfig ω) (hdb : d (A v) 0 ≤ b' 0) :
    d (A v) 0 + s < b' 0 := by
  obtain ⟨y, q, hy, hqS, hqE⟩ := exists_walk_trim (lo := ![lo 0 - 1, lo 1 - 1])
    (hi := ![hi 0, hi 1]) (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
    p hp hpS (by simpa using ha') (by simpa using hb')
    (fun x hx h => hbot x hx (by simpa using h)) (fun x hx h => htop x hx (by simpa using h))
  by_contra hfar
  push Not at hfar
  refine false_of_localConn_of_exploration h1 hle hΓ hA hv hvr hs hs3 hB hR hL q
    (fun x hx => ?_) (fun e he => hpG e (hqE e he)) (by simpa using hy) (by simp)
    (by simpa using hdb) (by simpa using hfar)
  have := mem_Icc_two_iff.1 (hqS x hx)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [mem_Icc_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- **A dual tip protected against open crossings.** Let `A v` be an admissible set of the
exploration of the dual configuration `dualConfig ω` in the box of faces `Icc lo hi`, with the fresh
part of the dual configuration of `dualConfig ω` (edges of the lattice of faces of faces, that is
of `ℤ²` moved by `(-1, -1)`) crossing none of the three strips of scale `s` around the point below
the right of its tip. An open walk `p` in the box `[lo₀, hi₀ + 1] × [lo₁ + 1, hi₁]` from its bottom
row to its top row, landing at `b` with `b₀ - 1` at or right of the tip, has `b₀ - 1` more than `s`
to the right of the tip. -/
theorem add_lt_of_exploration_dualConfig (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {ω : Config (LatticeSite 2)} {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (dualConfig ω \
        {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) (hvr : ∀ f ∈ A v, f 0 ≠ hi 0) {s : ℕ} (hs : 1 ≤ s)
    (hs3 : lo 1 + 3 * s ≤ hi 1 - 1)
    (hB : dualConfig (dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 1 (![d (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), -s]))
    (hR : dualConfig (dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 0 (![d (A v) 0, hi 1 - 1] + ![(s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), 3 * s]))
    (hL : dualConfig (dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 0 (![d (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![-(s : ℤ), 3 * s]))
    {a' b' : LatticeSite 2} (p : (zdGraph 2).Walk a' b')
    (hpS : ∀ x ∈ p.support, x ∈ Icc (![lo 0, lo 1 + 1] : LatticeSite 2) ![hi 0 + 1, hi 1])
    (ha' : a' 1 = lo 1 + 1) (hb' : b' 1 = hi 1) (hpG : ∀ e ∈ p.edges, e ∈ ω)
    (hdb : d (A v) 0 ≤ b' 0 - 1) :
    d (A v) 0 + s < b' 0 - 1 := by
  let g : zdGraph 2 →g zdGraph 2 := ⟨(· - 1), fun {x y} hxy =>
    (zdGraph_adj_iff_of_sub fun i => by simp only [Pi.sub_apply, sub_sub_sub_cancel_right]).2 hxy⟩
  have hg : ∀ x, g x = x - 1 := fun _ => rfl
  by_contra hfar
  push Not at hfar
  refine false_of_localConn_of_exploration h1 hle hΓ hA hv hvr hs hs3 hB hR hL (p.map g)
    (fun x hx => ?_) (fun e he => ?_) (by simp [hg, ha']) (by simp [hg, hb'])
    (by simpa [hg] using hdb) (by simpa [hg] using hfar)
  · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    have := mem_Icc_two_iff.1 (hpS x hx)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [mem_Icc_two_iff, hg]
    simp only [Pi.sub_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e, he, rfl⟩ := he
    rw [dualConfig_dualConfig]
    exact ⟨e, ⟨hpG e he, p.edges_subset_edgeSet he⟩, rfl⟩

/-- **Greedy tips away from the corners.** If the configuration `G` restricted to the box crosses
neither of the two strips at the top right corner at a scale `s ≥ s₀`, nor the two strips at the
top left corner at a scale `s' ≥ s₀`, every admissible greedy tip lies more than `s₀` from both
sides of the box. -/
theorem lt_tip_of_corner (h1 : lo 1 < hi 1)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A)
    {G : Config (LatticeSite 2)} {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {s₀ : ℕ} (hs₀ : 1 ≤ s₀)
    (hR : ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 ∧
      G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 1 (![hi 0, hi 1] + ![-3 * (s : ℤ), -3 * s]) (![hi 0, hi 1] + ![3 * (s : ℤ), -s]) ∧
      G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (![hi 0, hi 1] + ![-3 * (s : ℤ), -3 * s]) (![hi 0, hi 1] + ![-(s : ℤ), 3 * s]))
    (hL : ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 ∧
      G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 1 (![lo 0, hi 1] + ![-3 * (s : ℤ), -3 * s]) (![lo 0, hi 1] + ![3 * (s : ℤ), -s]) ∧
      G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (![lo 0, hi 1] + ![(s : ℤ), -3 * s]) (![lo 0, hi 1] + ![3 * (s : ℤ), 3 * s]))
    {v : ℕ} (hv : v ≤ u) (hvr : ∀ f ∈ A v, f 0 ≠ hi 0) :
    lo 0 + s₀ < d (A v) 0 ∧ d (A v) 0 + s₀ < hi 0 := by
  obtain ⟨-, hc1, -, hd1, hS, -⟩ := hΓ (A v) (mem_leftColumn_of_exploration hA hv) hvr
  have hG := (forall_mem_of_exploration h1 hΓ hA hv hvr).1
  obtain ⟨s, hs, hs3, hB, hL'⟩ := hR
  obtain ⟨s', hs', hs3', hB', hR'⟩ := hL
  refine ⟨?_, ?_⟩
  · by_contra h
    exact false_of_le_add_corner_left (by omega) hs3' hB' hR' (Γ (A v)) hS hG hc1 hd1 (by omega)
  · by_contra h
    exact false_of_le_add_corner_right (by omega) hs3 hB hL' (Γ (A v)) hS hG hc1 hd1 (by omega)

/-- **Same-colour separation of greedy tips.** If every admissible greedy tip up to step `u` has
three uncrossed strips of the fresh part of `G` at some scale `s ≥ s₀`, two distinct admissible
greedy tips are more than `s₀` apart. -/
theorem lt_abs_sub_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {G : Config (LatticeSite 2)} {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {s₀ : ℕ} (hs₀ : 1 ≤ s₀)
    (hsame : ∀ v ≤ u, (∀ f ∈ A v, f 0 ≠ hi 0) → ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 ∧
      (G \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 1 (d (A v) + ![-3 * (s : ℤ), -3 * s]) (d (A v) + ![3 * (s : ℤ), -s]) ∧
      (G \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (d (A v) + ![(s : ℤ), -3 * s]) (d (A v) + ![3 * (s : ℤ), 3 * s]) ∧
      (G \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (d (A v) + ![-3 * (s : ℤ), -3 * s]) (d (A v) + ![-(s : ℤ), 3 * s]))
    {v w : ℕ} (hvw : v ≠ w) (hvu : v ≤ u) (hwu : w ≤ u) (hv : ∀ f ∈ A v, f 0 ≠ hi 0)
    (hw : ∀ f ∈ A w, f 0 ≠ hi 0) : (s₀ : ℤ) < |d (A v) 0 - d (A w) 0| := by
  rcases lt_or_gt_of_ne hvw with h | h
  · obtain ⟨s, hs, hs3, hB, hR, hL⟩ := hsame v hvu hv
    have := lt_sub_of_exploration h1 hle hΓ hA h hwu hv hw (by omega) hs3 hB hR hL
    rw [abs_sub_comm, lt_abs]
    left
    omega
  · obtain ⟨s, hs, hs3, hB, hR, hL⟩ := hsame w hwu hw
    have := lt_sub_of_exploration h1 hle hΓ hA h hvu hw hv (by omega) hs3 hB hR hL
    rw [lt_abs]
    left
    omega

end Greedy

/-- **Clean dual crossings cross edges of the box.** A walk of faces of the box of faces
`[lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]` meeting its bottom row only at its start and its top row only at
its end uses only dual edges of edges of `ℤ²` with both ends in `Icc lo hi`. -/
theorem mem_image_dualEdge_of_mem_edges {lo hi a b : LatticeSite 2} (p : (zdGraph 2).Walk a b)
    (hS : ∀ x ∈ p.support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1])
    (hbot : ∀ x ∈ p.support, x 1 = lo 1 - 1 → x = a) (htop : ∀ x ∈ p.support, x 1 = hi 1 → x = b)
    {e : Sym2 (LatticeSite 2)} (he : e ∈ p.edges) :
    e ∈ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} := by
  obtain ⟨x, y, rfl, hxy, hx, hy⟩ := exists_ne_of_mem_edges p he
  have heL := p.edges_subset_edgeSet he
  have hx' := mem_Icc_two_iff.1 (hS x hx)
  have hy' := mem_Icc_two_iff.1 (hS y hy)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx' hy'
  have hbot' : ¬(x 1 = lo 1 - 1 ∧ y 1 = lo 1 - 1) := fun h =>
    hxy ((hbot x hx h.1).trans (hbot y hy h.2).symm)
  have htop' : ¬(x 1 = hi 1 ∧ y 1 = hi 1) := fun h =>
    hxy ((htop x hx h.1).trans (htop y hy h.2).symm)
  refine ⟨Sym2.map (· + 1) (dualEdge s(x, y)),
    ⟨map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet heL), fun z hz => ?_⟩,
    dualEdge_map_add_one_dualEdge heL⟩
  have h₁ := le_of_mem_map_add_one_dualEdge heL (Sym2.mem_mk_left x y) hz
  have h₂ := le_of_mem_map_add_one_dualEdge heL (Sym2.mem_mk_right x y) hz
  rw [mem_Icc_two_iff]
  omega

/-! ### The scales -/

/-- **The scales of the proof.** With `D = 16 · 8^J` and `N ≥ D²`, put `M = ⌊N / D⌋` and
`K = ⌊N / D²⌋`. Then `K ≥ 1`, `M ≥ 16`, and for `j < J` the separation scale `2 (M + 1) 8^j`
satisfies `3 s + 1 ≤ N` and the fence scale `t = (K + 1) 8^j` satisfies `3 t + 1 ≤ M`. -/
theorem scale_bounds {N J : ℕ} (hN : (16 * 8 ^ J) ^ 2 ≤ N) :
    1 ≤ N / (16 * 8 ^ J) ^ 2 ∧ 16 ≤ N / (16 * 8 ^ J) ∧
    ∀ j < J, 3 * (2 * (N / (16 * 8 ^ J) + 1) * 8 ^ j) + 1 ≤ N ∧
      3 * ((N / (16 * 8 ^ J) ^ 2 + 1) * 8 ^ j) + 1 ≤ N / (16 * 8 ^ J) := by
  have hY1 : 1 ≤ 8 ^ J := Nat.one_le_pow _ _ (by norm_num)
  set Y := 8 ^ J with hY
  set D := 16 * Y with hD
  have hD16 : 16 ≤ D := by omega
  have hDpos : 0 < D := by omega
  have hMD : N / D * D ≤ N := Nat.div_mul_le_self N D
  have hMge : D ≤ N / D := (Nat.le_div_iff_mul_le hDpos).2 (by rw [← sq]; exact hN)
  have hK : N / D ^ 2 = N / D / D := by rw [sq, Nat.div_div_eq_div_mul]
  have hKD : N / D ^ 2 * D ≤ N / D := by
    rw [hK]
    exact Nat.div_mul_le_self _ _
  have hK1 : 1 ≤ N / D ^ 2 := (Nat.one_le_div_iff (by positivity)).2 hN
  refine ⟨hK1, by omega, fun j hj => ?_⟩
  have h8 : 8 * 8 ^ j ≤ Y := by
    calc 8 * 8 ^ j = 8 ^ (j + 1) := by ring
      _ ≤ 8 ^ J := Nat.pow_le_pow_right (by norm_num) hj
  have hX1 : 1 ≤ 8 ^ j := Nat.one_le_pow _ _ (by norm_num)
  set X := 8 ^ j with hX
  set M := N / D with hM
  set K := N / D ^ 2 with hK'
  have hMX : M * (8 * X) ≤ M * Y := Nat.mul_le_mul_left _ h8
  have hKX : K * (8 * X) ≤ K * Y := Nat.mul_le_mul_left _ h8
  have hMX1 : X ≤ M * X := Nat.le_mul_of_pos_left _ (by omega)
  have hKX1 : X ≤ K * X := Nat.le_mul_of_pos_left _ (by omega)
  have hMY : M * (16 * Y) ≤ N := hMD
  have hKY : K * (16 * Y) ≤ M := hKD
  have hN256 : 256 ≤ N := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-! ### The deterministic part of the lemma -/

/-- **Local separation, deterministic part.** Let `k ∈ {0, 1}` and let `ω` be a configuration
such that the greedy explorations of `ω` in the box `Icc lo hi` and of `dualConfig ω` in the box of
faces `Icc lo₂ hi₂ = [lo₀ - k, hi₀ - 1 + k] × [lo₁ - 1, hi₁]` reach the right column within `T`
steps, every admissible greedy tip up to step `T` is protected at some scale `s ≥ s₀` against later
greedy tips of its colour and against walks of the other colour, and carries a fence annulus at
some scale `t` with `K ≤ 3t`, `3t + 1 ≤ M ≤ s₀`, and the four top corners are protected at some
scale `s ≥ s₀`. Then every family of disjoint crossings, open crossings of `Icc lo hi` or dual
crossings of `Icc lo₂ hi₂` (whose dual edges cross edges of `[lo₀ - k, hi₀ + k] × [lo₁, hi₁]`), is
rerouted to a family with the same colours and starts, meeting the top row only at their ends, whose
ends, in doubled positions, are more than `2 s₀` apart and more than `2 s₀` from the two ends
`2 (lo₀ - k)` and `2 (hi₀ + k)` of the doubled top side, each with a fence in the box
`[z₀ - K, z₀ + K] × [hi₁, hi₁ + M]` above its end `z`, arm-joined inside the ball of radius `M`
around `z`. For `k = 0` the two boxes span the same columns (Nolin's strip); for `k = 1` the box of
faces is one column wider on each side, as for the open and dual arms of a box landing on its top
side. -/
theorem separable_of_forall {ω : Config (LatticeSite 2)} {lo hi lo₂ hi₂ : LatticeSite 2} {k : ℤ}
    (hk : 0 ≤ k) (hk1 : k ≤ 1) (hlo₂ : lo₂ = ![lo 0 - k, lo 1 - 1])
    (hhi₂ : hi₂ = ![hi 0 - 1 + k, hi 1]) (h1 : lo 1 + 1 < hi 1)
    (h0 : lo 0 < hi 0) {T s₀ K M : ℕ} (hs₀ : 1 ≤ s₀) (hMs : M ≤ s₀)
    {c₁ d₁ : Finset (LatticeSite 2) → LatticeSite 2} {Γ₁ : ∀ A, (zdGraph 2).Walk (c₁ A) (d₁ A)}
    (hΓ₁ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c₁ A ∈ Icc lo hi ∧ c₁ A 1 = lo 1 ∧ d₁ A ∈ Icc lo hi ∧ d₁ A 1 = hi 1 ∧
        (∀ x ∈ (Γ₁ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ₁ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ₁ A).IsPath ∧ (∀ x ∈ (Γ₁ A).support, x 1 = lo 1 → x = c₁ A) ∧
        ∀ x ∈ (Γ₁ A).support, x 1 = hi 1 → x = d₁ A)
    {c₂ d₂ : Finset (LatticeSite 2) → LatticeSite 2} {Γ₂ : ∀ A, (zdGraph 2).Walk (c₂ A) (d₂ A)}
    (hΓ₂ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo₂ 1 ≤ y → y ≤ hi₂ 1 - 1 → (![lo₂ 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi₂ 0) →
      (c₂ A ∈ Icc lo₂ hi₂ ∧ c₂ A 1 = lo₂ 1 ∧ d₂ A ∈ Icc lo₂ hi₂ ∧ d₂ A 1 = hi₂ 1 ∧
        (∀ x ∈ (Γ₂ A).support, x ∈ Icc lo₂ hi₂) ∧
        ∀ e ∈ (Γ₂ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ₂ A).IsPath ∧ (∀ x ∈ (Γ₂ A).support, x 1 = lo₂ 1 → x = c₂ A) ∧
        ∀ x ∈ (Γ₂ A).support, x 1 = hi₂ 1 → x = d₂ A)
    (hO : ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ T, cluster (dualConfig (ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₁ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) →
      ∃ v ≤ T, ∃ f ∈ A v, f 0 = hi 0)
    (hD : ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ T, cluster (dualConfig (dualConfig ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₂ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∪
        {s | ∃ y : ℤ, lo₂ 1 ≤ y ∧ y + 1 ≤ hi₂ 1 - 1 ∧
          s = s(![lo₂ 0 - 1, y], (![lo₂ 0 - 1, y + 1] : LatticeSite 2))}) ![lo₂ 0 - 1, lo₂ 1] =
            ↑(A w)) →
      ∃ v ≤ T, ∃ f ∈ A v, f 0 = hi₂ 0)
    (hOs : ∀ v ≤ T, ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₁ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) →
      (∀ f ∈ A v, f 0 ≠ hi 0) → ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 - 1 ∧
      (ω \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 1 (d₁ (A v) + ![-3 * (s : ℤ), -3 * s])
          (d₁ (A v) + ![3 * (s : ℤ), -s]) ∧
      (ω \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (d₁ (A v) + ![(s : ℤ), -3 * s])
          (d₁ (A v) + ![3 * (s : ℤ), 3 * s]) ∧
      (ω \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (d₁ (A v) + ![-3 * (s : ℤ), -3 * s])
          (d₁ (A v) + ![-(s : ℤ), 3 * s]))
    (hOo : ∀ v ≤ T, ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₁ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) →
      (∀ f ∈ A v, f 0 ≠ hi 0) → ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 - 1 ∧
      dualConfig (ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
        crossing 1 (![d₁ (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
          (![d₁ (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), -s]) ∧
      dualConfig (ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
        crossing 0 (![d₁ (A v) 0, hi 1 - 1] + ![(s : ℤ), -3 * s])
          (![d₁ (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), 3 * s]) ∧
      dualConfig (ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
        crossing 0 (![d₁ (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
          (![d₁ (A v) 0, hi 1 - 1] + ![-(s : ℤ), 3 * s]))
    (hOf : ∀ v ≤ T, ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₁ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
        {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
          s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] =
            ↑(A w)) →
      (∀ f ∈ A v, f 0 ≠ hi 0) → ∃ t : ℕ, 1 ≤ t ∧ K ≤ 3 * t ∧ 3 * t + 1 ≤ M ∧ lo 1 + 3 * t ≤ hi 1 ∧
      ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 0 (d₁ (A v) + ![-3 * (t : ℤ), t + 1]) (d₁ (A v) + ![3 * (t : ℤ) + 1, 3 * t]) ∧
      ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 0 (d₁ (A v) + ![-3 * (t : ℤ), -3 * t + 1]) (d₁ (A v) + ![3 * (t : ℤ) + 1, -t]) ∧
      ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 1 (d₁ (A v) + ![(t : ℤ) + 1, -3 * t]) (d₁ (A v) + ![3 * (t : ℤ), 3 * t + 1]) ∧
      ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 1 (d₁ (A v) + ![-3 * (t : ℤ) + 1, -3 * t]) (d₁ (A v) + ![-(t : ℤ), 3 * t + 1]))
    (hDs : ∀ v ≤ T, ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (dualConfig ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₂ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∪
        {s | ∃ y : ℤ, lo₂ 1 ≤ y ∧ y + 1 ≤ hi₂ 1 - 1 ∧
          s = s(![lo₂ 0 - 1, y], (![lo₂ 0 - 1, y + 1] : LatticeSite 2))}) ![lo₂ 0 - 1, lo₂ 1] =
            ↑(A w)) →
      (∀ f ∈ A v, f 0 ≠ hi₂ 0) → ∃ s : ℕ, s₀ ≤ s ∧ lo₂ 1 + 3 * s ≤ hi₂ 1 - 1 ∧
      (dualConfig ω \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 1 (d₂ (A v) + ![-3 * (s : ℤ), -3 * s])
          (d₂ (A v) + ![3 * (s : ℤ), -s]) ∧
      (dualConfig ω \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 0 (d₂ (A v) + ![(s : ℤ), -3 * s])
          (d₂ (A v) + ![3 * (s : ℤ), 3 * s]) ∧
      (dualConfig ω \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 0 (d₂ (A v) + ![-3 * (s : ℤ), -3 * s])
          (d₂ (A v) + ![-(s : ℤ), 3 * s]))
    (hDo : ∀ v ≤ T, ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (dualConfig ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₂ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∪
        {s | ∃ y : ℤ, lo₂ 1 ≤ y ∧ y + 1 ≤ hi₂ 1 - 1 ∧
          s = s(![lo₂ 0 - 1, y], (![lo₂ 0 - 1, y + 1] : LatticeSite 2))}) ![lo₂ 0 - 1, lo₂ 1] =
            ↑(A w)) →
      (∀ f ∈ A v, f 0 ≠ hi₂ 0) → ∃ s : ℕ, s₀ ≤ s ∧ lo₂ 1 + 3 * s ≤ hi₂ 1 - 1 ∧
      dualConfig (dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∉
        crossing 1 (![d₂ (A v) 0, hi₂ 1 - 1] + ![-3 * (s : ℤ), -3 * s])
          (![d₂ (A v) 0, hi₂ 1 - 1] + ![3 * (s : ℤ), -s]) ∧
      dualConfig (dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∉
        crossing 0 (![d₂ (A v) 0, hi₂ 1 - 1] + ![(s : ℤ), -3 * s])
          (![d₂ (A v) 0, hi₂ 1 - 1] + ![3 * (s : ℤ), 3 * s]) ∧
      dualConfig (dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∉
        crossing 0 (![d₂ (A v) 0, hi₂ 1 - 1] + ![-3 * (s : ℤ), -3 * s])
          (![d₂ (A v) 0, hi₂ 1 - 1] + ![-(s : ℤ), 3 * s]))
    (hDf : ∀ v ≤ T, ∀ A : ℕ → Finset (LatticeSite 2),
      (∀ w ≤ v, cluster (dualConfig (dualConfig ω \
          {e | ∃ x ∈ e, ∃ w' < w, x ∈ (Γ₂ (A w')).support}) ∩
          {s | ∀ x ∈ s, x ∈ Icc (![lo₂ 0 - 1, lo₂ 1] : LatticeSite 2) ![hi₂ 0, hi₂ 1 - 1]} ∪
        {s | ∃ y : ℤ, lo₂ 1 ≤ y ∧ y + 1 ≤ hi₂ 1 - 1 ∧
          s = s(![lo₂ 0 - 1, y], (![lo₂ 0 - 1, y + 1] : LatticeSite 2))}) ![lo₂ 0 - 1, lo₂ 1] =
            ↑(A w)) →
      (∀ f ∈ A v, f 0 ≠ hi₂ 0) → ∃ t : ℕ, 1 ≤ t ∧ K ≤ 3 * t ∧ 3 * t + 1 ≤ M ∧
      lo₂ 1 + 3 * t ≤ hi₂ 1 ∧
      dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 0 (d₂ (A v) + ![-3 * (t : ℤ), t + 1]) (d₂ (A v) + ![3 * (t : ℤ) + 1, 3 * t]) ∧
      dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 0 (d₂ (A v) + ![-3 * (t : ℤ), -3 * t + 1]) (d₂ (A v) + ![3 * (t : ℤ) + 1, -t]) ∧
      dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 1 (d₂ (A v) + ![(t : ℤ) + 1, -3 * t]) (d₂ (A v) + ![3 * (t : ℤ), 3 * t + 1]) ∧
      dualConfig ω ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v} ∈
        crossing 1 (d₂ (A v) + ![-3 * (t : ℤ) + 1, -3 * t]) (d₂ (A v) + ![-(t : ℤ), 3 * t + 1]))
    (hOR : ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 ∧
      ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 1 (![hi 0, hi 1] + ![-3 * (s : ℤ), -3 * s])
          (![hi 0, hi 1] + ![3 * (s : ℤ), -s]) ∧
      ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (![hi 0, hi 1] + ![-3 * (s : ℤ), -3 * s])
          (![hi 0, hi 1] + ![-(s : ℤ), 3 * s]))
    (hOL : ∃ s : ℕ, s₀ ≤ s ∧ lo 1 + 3 * s ≤ hi 1 ∧
      ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 1 (![lo 0, hi 1] + ![-3 * (s : ℤ), -3 * s])
          (![lo 0, hi 1] + ![3 * (s : ℤ), -s]) ∧
      ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
        crossing 0 (![lo 0, hi 1] + ![(s : ℤ), -3 * s])
          (![lo 0, hi 1] + ![3 * (s : ℤ), 3 * s]))
    (hDR : ∃ s : ℕ, s₀ ≤ s ∧ lo₂ 1 + 3 * s ≤ hi₂ 1 ∧
      dualConfig ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 1 (![hi₂ 0, hi₂ 1] + ![-3 * (s : ℤ), -3 * s])
          (![hi₂ 0, hi₂ 1] + ![3 * (s : ℤ), -s]) ∧
      dualConfig ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 0 (![hi₂ 0, hi₂ 1] + ![-3 * (s : ℤ), -3 * s])
          (![hi₂ 0, hi₂ 1] + ![-(s : ℤ), 3 * s]))
    (hDL : ∃ s : ℕ, s₀ ≤ s ∧ lo₂ 1 + 3 * s ≤ hi₂ 1 ∧
      dualConfig ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 1 (![lo₂ 0, hi₂ 1] + ![-3 * (s : ℤ), -3 * s])
          (![lo₂ 0, hi₂ 1] + ![3 * (s : ℤ), -s]) ∧
      dualConfig ω ∩ {e | ∀ x ∈ e, x ∈ Icc lo₂ hi₂} ∉
        crossing 0 (![lo₂ 0, hi₂ 1] + ![(s : ℤ), -3 * s])
          (![lo₂ 0, hi₂ 1] + ![3 * (s : ℤ), 3 * s])) :
    ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lo 1 ∧ b i 1 = hi 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lo₂ 1 ∧ b i 1 = hi₂ 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo₂ hi₂) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc (![lo 0 - k, lo 1] : LatticeSite 2) ![hi 0 + k, hi 1]})) →
      (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
      ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lo 1 ∧ b' i 1 = hi 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo hi) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lo₂ 1 ∧ b' i 1 = hi₂ 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo₂ hi₂) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (![lo 0 - k, lo 1] : LatticeSite 2) ![hi 0 + k, hi 1]})) ∧
        (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ' i).support, x ∉ (γ' j).support) ∧
        (∀ i j, i ≠ j → 2 * (s₀ : ℤ) <
          |(2 * b' i 0 + cond (σ i) 0 1) - (2 * b' j 0 + cond (σ j) 0 1)|) ∧
        (∀ i, 2 * (s₀ : ℤ) < 2 * b' i 0 + cond (σ i) 0 1 - 2 * (lo 0 - k) ∧
          2 * (s₀ : ℤ) < 2 * (hi 0 + k) - (2 * b' i 0 + cond (σ i) 0 1)) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hi 1) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2, l 0 = b' i 0 - K ∧ r 0 = b' i 0 + K ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈
            localConn (Icc ![b' i 0 - K, hi 1] ![b' i 0 + K, hi 1 + M]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈
            localConn (Icc (b' i - (M : LatticeSite 2)) (b' i + (M : LatticeSite 2))) x l := by
  intro m σ a b γ hcr hdisj
  classical
  have hl₂0 : lo₂ 0 = lo 0 - k := by rw [hlo₂]; rfl
  have hl₂1 : lo₂ 1 = lo 1 - 1 := by rw [hlo₂]; rfl
  have hh₂0 : hi₂ 0 = hi 0 - 1 + k := by rw [hhi₂]; rfl
  have hh₂1 : hi₂ 1 = hi 1 := by rw [hhi₂]; rfl
  have hle : lo ≤ hi := by
    rw [Pi.le_def, Fin.forall_fin_two]
    exact ⟨h0.le, by omega⟩
  have hle₂ : lo₂ ≤ hi₂ := by
    rw [Pi.le_def, Fin.forall_fin_two, hl₂0, hl₂1, hh₂0, hh₂1]
    omega
  have h1' : lo 1 < hi 1 := by omega
  have h1₂ : lo₂ 1 < hi₂ 1 := by
    rw [hl₂1, hh₂1]
    omega
  have hΓ₁' := fun A' h₁ h₂ => (hΓ₁ A' h₁ h₂).1
  have hΓ₂' := fun A' h₁ h₂ => (hΓ₂ A' h₁ h₂).1
  -- the two explorations, up to the first step where they reach the right column
  obtain ⟨A₁, hA₁⟩ := exists_exploration h1' (hle 0) ω Γ₁ T
  obtain ⟨A₂, hA₂⟩ := exists_exploration h1₂ (hle₂ 0) (dualConfig ω) Γ₂ T
  obtain ⟨u₁, hu₁T, hu₁⟩ := hO A₁ hA₁
  obtain ⟨u₂, hu₂T, hu₂⟩ := hD A₂ hA₂
  have hA₁u := fun w (hw : w ≤ u₁) => hA₁ w (hw.trans hu₁T)
  have hA₂u := fun w (hw : w ≤ u₂) => hA₂ w (hw.trans hu₂T)
  -- the greedy tips are away from the corners
  have hc₁ := fun v (hv : v ≤ u₁) (hvr : ∀ f ∈ A₁ v, f 0 ≠ hi 0) =>
    lt_tip_of_corner h1' hΓ₁' hA₁u hs₀ hOR hOL hv hvr
  have hc₂ := fun v (hv : v ≤ u₂) (hvr : ∀ f ∈ A₂ v, f 0 ≠ hi₂ 0) =>
    lt_tip_of_corner h1₂ hΓ₂' hA₂u hs₀ hDR hDL hv hvr
  -- the members of each colour
  have hcr₁ : ∀ i, σ i = true → a i 1 = lo 1 ∧ b i 1 = hi 1 ∧
      (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧ ∀ e ∈ (γ i).edges, e ∈ ω := fun i hσ => by
    have := hcr i
    rw [hσ] at this
    exact this
  have hcr₂ : ∀ i, σ i = false → a i 1 = lo₂ 1 ∧ b i 1 = hi₂ 1 ∧
      (∀ x ∈ (γ i).support, x ∈ Icc lo₂ hi₂) ∧ ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩
        dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
          ∀ x ∈ e, x ∈ Icc (![lo 0 - k, lo 1] : LatticeSite 2) ![hi 0 + k, hi 1]} := fun i hσ => by
    have := hcr i
    rw [hσ] at this
    exact this
  have hS₁ : ∀ i, i ∈ Finset.univ.filter (fun i => σ i = true) ↔ σ i = true := fun i => by
    simp
  have hS₂ : ∀ i, i ∈ Finset.univ.filter (fun i => σ i = false) ↔ σ i = false := fun i => by
    simp
  -- rerouting each colour, with fences
  obtain ⟨w₁, γ₁, hw₁, hwd₁, hbox₁, hG₁, -, hdisj₁, htop₁, hfen₁⟩ :=
    exists_reroute_fence_of_exploration h1' hle hΓ₁ hA₁u hu₁ (K := K) (M := M)
      (fun v hv hvr => by
        obtain ⟨t, ht, hKt, htM, hy, hT, hB, hR, hL⟩ :=
          hOf v (by omega) A₁ (fun w hw => hA₁ w (le_trans hw (by omega))) hvr
        have := hc₁ v hv.le hvr
        exact ⟨t, ht, hKt, htM, by omega, by omega, hy, hT, hB, hR, hL⟩)
      (Finset.univ.filter fun i => σ i = true) γ
      (fun i hi => (hcr₁ i ((hS₁ i).1 hi)).2.2.1) (fun i hi => (hcr₁ i ((hS₁ i).1 hi)).1)
      (fun i hi => (hcr₁ i ((hS₁ i).1 hi)).2.1) (fun i hi => (hcr₁ i ((hS₁ i).1 hi)).2.2.2)
      (fun i hi j hj hij => hdisj i j hij (((hS₁ i).1 hi).trans ((hS₁ j).1 hj).symm))
  obtain ⟨w₂, γ₂, hw₂, hwd₂, hbox₂, hG₂, hedge₂, hdisj₂, htop₂, hfen₂⟩ :=
    exists_reroute_fence_of_exploration h1₂ hle₂ hΓ₂ hA₂u hu₂ (K := K) (M := M)
      (fun v hv hvr => by
        obtain ⟨t, ht, hKt, htM, hy, hT, hB, hR, hL⟩ :=
          hDf v (by omega) A₂ (fun w hw => hA₂ w (le_trans hw (by omega))) hvr
        have := hc₂ v hv.le hvr
        exact ⟨t, ht, hKt, htM, by omega, by omega, hy, hT, hB, hR, hL⟩)
      (Finset.univ.filter fun i => σ i = false) γ
      (fun i hi => (hcr₂ i ((hS₂ i).1 hi)).2.2.1) (fun i hi => (hcr₂ i ((hS₂ i).1 hi)).1)
      (fun i hi => (hcr₂ i ((hS₂ i).1 hi)).2.1)
      (fun i hi e he => ((hcr₂ i ((hS₂ i).1 hi)).2.2.2 e he).1)
      (fun i hi j hj hij => hdisj i j hij (((hS₂ i).1 hi).trans ((hS₂ j).1 hj).symm))
  -- data of the greedy crossings at the tips
  have hdat₁ : ∀ i, σ i = true → w₁ i < u₁ ∧ (∀ f ∈ A₁ (w₁ i), f 0 ≠ hi 0) ∧
      (γ₁ i).1 = d₁ (A₁ (w₁ i)) ∧ d₁ (A₁ (w₁ i)) 1 = hi 1 := fun i hσ => by
    obtain ⟨hwu, hadm, hend⟩ := hw₁ i ((hS₁ i).2 hσ)
    exact ⟨hwu, hadm, hend,
      (hΓ₁' (A₁ (w₁ i)) (mem_leftColumn_of_exploration hA₁u hwu.le) hadm).2.2.2.1⟩
  have hdat₂ : ∀ i, σ i = false → w₂ i < u₂ ∧ (∀ f ∈ A₂ (w₂ i), f 0 ≠ hi₂ 0) ∧
      (γ₂ i).1 = d₂ (A₂ (w₂ i)) ∧ d₂ (A₂ (w₂ i)) 1 = hi₂ 1 := fun i hσ => by
    obtain ⟨hwu, hadm, hend⟩ := hw₂ i ((hS₂ i).2 hσ)
    exact ⟨hwu, hadm, hend,
      (hΓ₂' (A₂ (w₂ i)) (mem_leftColumn_of_exploration hA₂u hwu.le) hadm).2.2.2.1⟩
  -- separation of tips of the same colour
  have hsep₁ : ∀ i j, σ i = true → σ j = true → i ≠ j →
      (s₀ : ℤ) < |(γ₁ i).1 0 - (γ₁ j).1 0| := by
    intro i j hσi hσj hij
    obtain ⟨hwi, hai, hei, -⟩ := hdat₁ i hσi
    obtain ⟨hwj, haj, hej, -⟩ := hdat₁ j hσj
    rw [hei, hej]
    refine lt_abs_sub_of_exploration h1' hle hΓ₁ hA₁u hs₀ (fun v hv hvr => ?_)
      (hwd₁ i ((hS₁ i).2 hσi) j ((hS₁ j).2 hσj) hij) hwi.le hwj.le hai haj
    obtain ⟨s, hs, hs3, hB, hR, hL⟩ :=
      hOs v (by omega) A₁ (fun w hw => hA₁ w (le_trans hw (by omega))) hvr
    exact ⟨s, hs, by omega, hB, hR, hL⟩
  have hsep₂ : ∀ i j, σ i = false → σ j = false → i ≠ j →
      (s₀ : ℤ) < |(γ₂ i).1 0 - (γ₂ j).1 0| := by
    intro i j hσi hσj hij
    obtain ⟨hwi, hai, hei, -⟩ := hdat₂ i hσi
    obtain ⟨hwj, haj, hej, -⟩ := hdat₂ j hσj
    rw [hei, hej]
    refine lt_abs_sub_of_exploration h1₂ hle₂ hΓ₂ hA₂u hs₀ (fun v hv hvr => ?_)
      (hwd₂ i ((hS₂ i).2 hσi) j ((hS₂ j).2 hσj) hij) hwi.le hwj.le hai haj
    obtain ⟨s, hs, hs3, hB, hR, hL⟩ :=
      hDs v (by omega) A₂ (fun w hw => hA₂ w (le_trans hw (by omega))) hvr
    exact ⟨s, hs, by omega, hB, hR, hL⟩
  -- separation of tips of different colours
  have hmix : ∀ i j, σ i = true → σ j = false →
      2 * (s₀ : ℤ) + 1 < |2 * (γ₁ i).1 0 - (2 * (γ₂ j).1 0 + 1)| := by
    intro i j hσi hσj
    obtain ⟨hwi, hai, hei, hdi⟩ := hdat₁ i hσi
    obtain ⟨hwj, haj, hej, hdj⟩ := hdat₂ j hσj
    rw [hei, hej]
    obtain ⟨⟨-, hcj1, -, -, hSj, -⟩, hPj, hbotj, htopj⟩ :=
      hΓ₂ (A₂ (w₂ j)) (mem_leftColumn_of_exploration hA₂u hwj.le) haj
    obtain ⟨⟨-, hci1, -, -, hSi, -⟩, -, -, -⟩ :=
      hΓ₁ (A₁ (w₁ i)) (mem_leftColumn_of_exploration hA₁u hwi.le) hai
    by_cases hzf : d₁ (A₁ (w₁ i)) 0 ≤ d₂ (A₂ (w₂ j)) 0
    · obtain ⟨s, hs, hs3, hB, hR, hL⟩ :=
        hOo (w₁ i) (by omega) A₁ (fun w hw => hA₁ w (le_trans hw (by omega))) hai
      have := add_lt_of_exploration_of_dualConfig h1' hle hΓ₁ hA₁u hwi.le hai (by omega) hs3
        hB hR hL (Γ₂ (A₂ (w₂ j))) hPj (fun x hx => by
          have := mem_Icc_two_iff.1 (hSj x hx)
          rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega)
        (by rw [hcj1, hl₂1]) (by rw [hdj, hh₂1]) (fun x hx h => hbotj x hx (by rw [hl₂1]; exact h))
        (fun x hx h => htopj x hx (by rw [hh₂1]; exact h))
        (forall_mem_of_exploration h1₂ hΓ₂' hA₂u hwj.le haj).1 hzf
      rw [lt_abs]
      right
      omega
    · obtain ⟨s, hs, hs3, hB, hR, hL⟩ :=
        hDo (w₂ j) (by omega) A₂ (fun w hw => hA₂ w (le_trans hw (by omega))) haj
      have := add_lt_of_exploration_dualConfig h1₂ hle₂ hΓ₂ hA₂u hwj.le haj (by omega) hs3
        hB hR hL (Γ₁ (A₁ (w₁ i))) (fun x hx => by
          have := mem_Icc_two_iff.1 (hSi x hx)
          rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega)
        (by omega) (by rw [hdi, hh₂1])
        (forall_mem_of_exploration h1' hΓ₁' hA₁u hwi.le hai).1 (by omega)
      rw [lt_abs]
      left
      omega
  -- the new family
  set Γ'' : ∀ i, Σ y : LatticeSite 2, (zdGraph 2).Walk (a i) y :=
    fun i => cond (σ i) (γ₁ i) (γ₂ i) with hΓ''
  have hΓt : ∀ i, σ i = true → Γ'' i = γ₁ i := fun i hσ => by
    change cond (σ i) (γ₁ i) (γ₂ i) = γ₁ i
    rw [hσ]
    rfl
  have hΓf : ∀ i, σ i = false → Γ'' i = γ₂ i := fun i hσ => by
    change cond (σ i) (γ₁ i) (γ₂ i) = γ₂ i
    rw [hσ]
    rfl
  refine ⟨fun i => (Γ'' i).1, fun i => (Γ'' i).2, fun i => ?_, fun i j hij hσij x hx hx' => ?_,
    fun i j hij => ?_, fun i => ?_, fun i x hx hx1 => ?_, fun i => ?_⟩
  · -- crossings of the right colour
    cases hσ : σ i
    · obtain ⟨hwi, hai, hei, hdi⟩ := hdat₂ i hσ
      have hiS := (hS₂ i).2 hσ
      change a i 1 = lo₂ 1 ∧ (Γ'' i).1 1 = hi₂ 1 ∧ (∀ x ∈ (Γ'' i).2.support, x ∈ Icc lo₂ hi₂) ∧
        ∀ e ∈ (Γ'' i).2.edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
          ∀ x ∈ e, x ∈ Icc (![lo 0 - k, lo 1] : LatticeSite 2) ![hi 0 + k, hi 1]}
      rw [hΓf i hσ]
      refine ⟨(hcr₂ i hσ).1, by rw [hei, hdi], hbox₂ i hiS, fun e he => ⟨hG₂ i hiS e he, ?_⟩⟩
      rcases hedge₂ i hiS e he with h | h
      · exact ((hcr₂ i hσ).2.2.2 e h).2
      · obtain ⟨⟨-, hc1, -, -, hS, -⟩, -, hbot, htop⟩ :=
          hΓ₂ (A₂ (w₂ i)) (mem_leftColumn_of_exploration hA₂u hwi.le) hai
        refine mem_image_dualEdge_of_mem_edges (lo := ![lo 0 - k, lo 1]) (hi := ![hi 0 + k, hi 1])
          _ (fun x hx => ?_) (fun x hx h => hbot x hx ?_) (fun x hx h => htop x hx ?_) h
        · have := mem_Icc_two_iff.1 (hS x hx)
          rw [mem_Icc_two_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          omega
        · simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
          rw [hl₂1]
          exact h
        · simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
          rw [hh₂1]
          exact h
    · obtain ⟨-, -, hei, hdi⟩ := hdat₁ i hσ
      have hiS := (hS₁ i).2 hσ
      change a i 1 = lo 1 ∧ (Γ'' i).1 1 = hi 1 ∧ (∀ x ∈ (Γ'' i).2.support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ'' i).2.edges, e ∈ ω
      rw [hΓt i hσ]
      exact ⟨(hcr₁ i hσ).1, by rw [hei, hdi], hbox₁ i hiS, hG₁ i hiS⟩
  · -- disjointness within each colour
    change x ∈ (Γ'' i).2.support at hx
    change x ∈ (Γ'' j).2.support at hx'
    cases hσ : σ i
    · have hσj : σ j = false := hσij ▸ hσ
      rw [hΓf i hσ] at hx
      rw [hΓf j hσj] at hx'
      exact hdisj₂ i ((hS₂ i).2 hσ) j ((hS₂ j).2 hσj) hij x hx hx'
    · have hσj : σ j = true := hσij ▸ hσ
      rw [hΓt i hσ] at hx
      rw [hΓt j hσj] at hx'
      exact hdisj₁ i ((hS₁ i).2 hσ) j ((hS₁ j).2 hσj) hij x hx hx'
  · -- separation
    change 2 * (s₀ : ℤ) < |(2 * (Γ'' i).1 0 + cond (σ i) 0 1) - (2 * (Γ'' j).1 0 + cond (σ j) 0 1)|
    cases hσi : σ i <;> cases hσj : σ j
    · rw [hΓf i hσi, hΓf j hσj]
      have := hsep₂ i j hσi hσj hij
      simp only [Bool.cond_false]
      rw [lt_abs] at this ⊢
      omega
    · rw [hΓf i hσi, hΓt j hσj]
      have := hmix j i hσj hσi
      simp only [Bool.cond_false, Bool.cond_true]
      rw [lt_abs] at this ⊢
      omega
    · rw [hΓt i hσi, hΓf j hσj]
      have := hmix i j hσi hσj
      simp only [Bool.cond_false, Bool.cond_true]
      rw [lt_abs] at this ⊢
      omega
    · rw [hΓt i hσi, hΓt j hσj]
      have := hsep₁ i j hσi hσj hij
      simp only [Bool.cond_true]
      rw [lt_abs] at this ⊢
      omega
  · -- away from the corners
    change 2 * (s₀ : ℤ) < 2 * (Γ'' i).1 0 + cond (σ i) 0 1 - 2 * (lo 0 - k) ∧
      2 * (s₀ : ℤ) < 2 * (hi 0 + k) - (2 * (Γ'' i).1 0 + cond (σ i) 0 1)
    cases hσ : σ i
    · obtain ⟨hwi, hai, hei, -⟩ := hdat₂ i hσ
      have := hc₂ (w₂ i) hwi.le hai
      rw [hΓf i hσ, hei]
      simp only [Bool.cond_false]
      omega
    · obtain ⟨hwi, hai, hei, -⟩ := hdat₁ i hσ
      have := hc₁ (w₁ i) hwi.le hai
      rw [hΓt i hσ, hei]
      simp only [Bool.cond_true]
      omega
  · -- the top row is met only at the ends
    change x ∈ (Γ'' i).2.support.dropLast at hx
    cases hσ : σ i
    · rw [hΓf i hσ] at hx
      exact htop₂ i ((hS₂ i).2 hσ) x hx (by rw [hh₂1]; exact hx1)
    · rw [hΓt i hσ] at hx
      exact htop₁ i ((hS₁ i).2 hσ) x hx hx1
  · -- fences
    change ∃ x ∈ (Γ'' i).2.support, ∃ l r : LatticeSite 2, l 0 = (Γ'' i).1 0 - K ∧
      r 0 = (Γ'' i).1 0 + K ∧
      cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc ![(Γ'' i).1 0 - K, hi 1] ![(Γ'' i).1 0 + K, hi 1 + M]) l r ∧
      cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc ((Γ'' i).1 - (M : LatticeSite 2)) ((Γ'' i).1 + (M : LatticeSite 2))) x l
    cases hσ : σ i
    · rw [hΓf i hσ, ← hh₂1]
      exact hfen₂ i ((hS₂ i).2 hσ)
    · rw [hΓt i hσ]
      exact hfen₁ i ((hS₁ i).2 hσ)

/-! ### Nolin's local separation lemma -/

/-- **Local separation in a strip, any of the two geometries.** For every `δ > 0` there are `η > 0`
and `N₀` such that, uniformly over the laws with crossing bounds `c` up to `L`, for `N₀ ≤ N ≤ L`
and `k ∈ {0, 1}`, with probability at least `1 - δ` the following holds for the open box
`Icc lo hi = [lo₀, lo₀ + 4N] × [lo₁, lo₁ + N]` and the box of faces
`Icc lo₂ hi₂ = [lo₀ - k, hi₀ - 1 + k] × [lo₁ - 1, hi₁]`. Every family of crossings from bottom to
top, each open (an open walk in `Icc lo hi` from its bottom row to its top row) or dual (a walk of
faces of `Icc lo₂ hi₂` from its bottom row to its top row along dual-open dual edges crossing edges
of `Icc elo ehi = [lo₀ - k, hi₀ + k] × [lo₁, hi₁]`), with crossings of the same colour disjoint, can
be replaced by a family with the same colours and the same starting points, with crossings of the
same colour disjoint, meeting the top row only at their ends, whose ends, in doubled positions, are
at least `4 √η N` apart and at least `4 √η N` from the two ends `2 elo₀` and `2 ehi₀` of the
doubled top side, and each of which carries a fence as in `exists_law_separable_ge`.

The boxes enter as variables with their defining equations (eleven hypotheses in all), so that
the two instances, `exists_law_separable_ge` (`k = 0`) and `exists_law_separable_ge_arm` (`k = 1`),
are read off without rewriting the event. -/
theorem exists_law_separable_ge_aux (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ N : ℕ, N₀ ≤ N → (N : ℕ∞) ≤ L →
      ∀ (k : ℤ) (lo hi lo₂ hi₂ elo ehi : LatticeSite 2), 0 ≤ k → k ≤ 1 →
      hi = ![lo 0 + 4 * N, lo 1 + N] → lo₂ = ![lo 0 - k, lo 1 - 1] → hi₂ = ![hi 0 - 1 + k, hi 1] →
      elo = ![lo 0 - k, lo 1] → ehi = ![hi 0 + k, hi 1] →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = lo 1 ∧ b i 1 = hi 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = lo₂ 1 ∧ b i 1 = hi₂ 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo₂ hi₂) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc elo ehi})) →
        (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
        ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = lo 1 ∧ b' i 1 = hi 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo hi) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = lo₂ 1 ∧ b' i 1 = hi₂ 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo₂ hi₂) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc elo ehi})) ∧
          (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ' i).support, x ∉ (γ' j).support) ∧
          (∀ i j, i ≠ j → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' j 0 + cond (σ j) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * elo 0 : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * ehi 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hi 1) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, hi 1] ![b' i 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊])
              l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  by_cases hc : 0 < c 6 ∧ 0 < c 7
  swap
  · exact ⟨1, one_pos, 0, fun q L h => absurd ⟨h.pos 6, h.pos 7⟩ hc⟩
  obtain ⟨hc6, hc7⟩ := hc
  -- the number of steps of the explorations and the number of scales
  have hr₁ : 1 - c 6 < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc6.ne'
  have hr₂ : 1 - c 7 ^ 4 < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (pow_ne_zero 4 hc7.ne')
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hδ4 : 0 < δ / 2 / 2 := ENNReal.half_pos hδ2.ne'
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr₁).eventually (gt_mem_nhds hδ4))
  have hε : 0 < δ / 2 / ((6 * (T + 1) + 4 : ℕ) : ℝ≥0∞) :=
    ENNReal.div_pos_iff.2 ⟨hδ2.ne', ENNReal.natCast_ne_top _⟩
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr₂).eventually (gt_mem_nhds hε))
  refine ⟨(1 / ((16 * 8 ^ J : ℕ) : ℝ)) ^ 2, by positivity, (16 * 8 ^ J) ^ 2,
    fun q L h N hN hNL k lo hi lo₂ hi₂ elo ehi hk hk1 hhi hlo₂ hhi₂ helo hehi => ?_⟩
  subst helo hehi
  -- the coordinates of the boxes
  have hhi0 : hi 0 = lo 0 + 4 * N := by rw [hhi]; rfl
  have hhi1 : hi 1 = lo 1 + N := by rw [hhi]; rfl
  have hl₂0 : lo₂ 0 = lo 0 - k := by rw [hlo₂]; rfl
  have hl₂1 : lo₂ 1 = lo 1 - 1 := by rw [hlo₂]; rfl
  have hh₂0 : hi₂ 0 = hi 0 - 1 + k := by rw [hhi₂]; rfl
  have hh₂1 : hi₂ 1 = hi 1 := by rw [hhi₂]; rfl
  obtain ⟨hK1, hM16, hscale⟩ := scale_bounds hN
  set D := 16 * 8 ^ J with hD
  set M := N / D with hM
  set K := N / D ^ 2 with hK
  set s₀ := 2 * (M + 1) with hs₀
  -- the real parameters
  have hDpos : (0 : ℝ) < D := by positivity
  have hsqrt : Real.sqrt ((1 / (D : ℝ)) ^ 2) = 1 / D := Real.sqrt_sq (by positivity)
  have hKfl : ⌊(1 / (D : ℝ)) ^ 2 * N⌋₊ = K := by
    rw [show (1 / (D : ℝ)) ^ 2 * N = ((N : ℕ) : ℝ) / ((D ^ 2 : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_div_eq_div N (D ^ 2)
  have hMfl : ⌊Real.sqrt ((1 / (D : ℝ)) ^ 2) * N⌋₊ = M := by
    rw [hsqrt, show 1 / (D : ℝ) * N = ((N : ℕ) : ℝ) / ((D : ℕ) : ℝ) by ring]
    exact Nat.floor_div_eq_div N D
  have hsep : 4 * Real.sqrt ((1 / (D : ℝ)) ^ 2) * N ≤ 2 * (s₀ : ℝ) := by
    have h₁ : (N : ℝ) / D < M + 1 := by
      have := Nat.lt_floor_add_one ((N : ℝ) / D)
      rwa [Nat.floor_div_eq_div] at this
    rw [hsqrt, hs₀]
    push_cast
    have h₂ : 4 * (1 / (D : ℝ)) * N = 4 * ((N : ℝ) / D) := by ring
    rw [h₂]
    linarith
  -- the scales
  have hNL' : ∀ n : ℕ, n ≤ N → (n : ℕ∞) ≤ L := fun n hn => le_trans (Nat.cast_le.2 hn) hNL
  have hMN : M ≤ N := Nat.div_le_self N D
  have h8 : ∀ a j j' : ℕ, j < j' → 8 * (a * 8 ^ j) ≤ a * 8 ^ j' := fun a j j' hjj' => by
    calc 8 * (a * 8 ^ j) = a * 8 ^ (j + 1) := by ring
      _ ≤ a * 8 ^ j' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjj')
  have hsc1 : ∀ j, 1 ≤ s₀ * 8 ^ j := fun j =>
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by positivity))
  have htc1 : ∀ j, 1 ≤ (K + 1) * 8 ^ j := fun j =>
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by positivity))
  have hscN : ∀ j < J, 3 * (s₀ * 8 ^ j) + 1 ≤ N := fun j hj => (hscale j hj).1
  have htcM : ∀ j < J, 3 * ((K + 1) * 8 ^ j) + 1 ≤ M := fun j hj => (hscale j hj).2
  have hJs : ∀ j < J, ((2 * (s₀ * 8 ^ j) - 1 : ℕ) : ℕ∞) ≤ L := fun j hj =>
    hNL' _ (by have := hscN j hj; omega)
  have hJt : ∀ j < J, ((2 * ((K + 1) * 8 ^ j) - 1 : ℕ) : ℕ∞) ≤ L := fun j hj =>
    hNL' _ (by have := htcM j hj; omega)
  have hs₀le : ∀ j, s₀ ≤ s₀ * 8 ^ j := fun j => Nat.le_mul_of_pos_right _ (by positivity)
  have hKle : ∀ j, K ≤ 3 * ((K + 1) * 8 ^ j) := fun j => by
    have := Nat.le_mul_of_pos_right (K + 1) (show 0 < 8 ^ j by positivity)
    omega
  have hsO : ∀ j < J, lo 1 + 3 * ((s₀ * 8 ^ j : ℕ) : ℤ) ≤ hi 1 - 1 := fun j hj => by
    have := hscN j hj
    omega
  have hsD : ∀ j < J, lo₂ 1 + 3 * ((s₀ * 8 ^ j : ℕ) : ℤ) ≤ hi₂ 1 - 1 := fun j hj => by
    have := hscN j hj
    omega
  have htO : ∀ j < J, lo 1 + 3 * (((K + 1) * 8 ^ j : ℕ) : ℤ) ≤ hi 1 := fun j hj => by
    have := htcM j hj
    omega
  have htD : ∀ j < J, lo₂ 1 + 3 * (((K + 1) * 8 ^ j : ℕ) : ℤ) ≤ hi₂ 1 := fun j hj => by
    have := htcM j hj
    omega
  -- the two boxes and the clean choice rules
  have hle : lo ≤ hi := by
    rw [Pi.le_def, Fin.forall_fin_two]
    omega
  have hle₂ : lo₂ ≤ hi₂ := by
    rw [Pi.le_def, Fin.forall_fin_two]
    omega
  obtain ⟨c₁, d₁, Γ₁, hΓ₁⟩ := exists_crossing_choice_clean hle
  obtain ⟨c₂, d₂, Γ₂, hΓ₂⟩ := exists_crossing_choice_clean hle₂
  -- the explorations are determined by the pairs meeting their last set
  have hPo : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)),
      ω ∩ ({e | ∃ f ∈ dualEdge e, f ∈ D} ∩ (zdGraph 2).edgeSet) =
        ω' ∩ ({e | ∃ f ∈ dualEdge e, f ∈ D} ∩ (zdGraph 2).edgeSet) →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) → (e ∈ id ω ↔ e ∈ id ω') := by
    intro D ω ω' hωω' e he hf
    have := congrArg (e ∈ ·) hωω'
    simp only [mem_inter_iff, eq_iff_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', hf, he⟩).1, fun h' => (this.2 ⟨h', hf, he⟩).1⟩
  have hPd : ∀ (D : Finset (LatticeSite 2)) (ω ω' : Config (LatticeSite 2)),
      ω ∩ ((fun p => Sym2.map (· + 1) (dualEdge p)) ''
          ({e | ∃ f ∈ dualEdge e, f ∈ D} ∩ (zdGraph 2).edgeSet)) =
        ω' ∩ ((fun p => Sym2.map (· + 1) (dualEdge p)) ''
          ({e | ∃ f ∈ dualEdge e, f ∈ D} ∩ (zdGraph 2).edgeSet)) →
      ∀ e ∈ (zdGraph 2).edgeSet, (∃ f ∈ dualEdge e, f ∈ D) →
        (e ∈ dualConfig ω ↔ e ∈ dualConfig ω') := by
    intro D ω ω' hωω' e he hf
    have := congrArg (Sym2.map (· + 1) (dualEdge e) ∈ ·) hωω'
    simp only [mem_inter_iff, eq_iff_iff] at this
    have hmem : Sym2.map (· + 1) (dualEdge e) ∈ (fun p => Sym2.map (· + 1) (dualEdge p)) ''
        ({e | ∃ f ∈ dualEdge e, f ∈ D} ∩ (zdGraph 2).edgeSet) := ⟨e, ⟨hf, he⟩, rfl⟩
    rw [mem_dualConfig_iff, mem_dualConfig_iff]
    exact and_congr_right fun _ => not_congr ⟨fun h' => (this.1 ⟨h', hmem⟩).1,
      fun h' => (this.2 ⟨h', hmem⟩).1⟩
  -- the bad events and their probabilities
  have bO := law_exploration_le_pow_of_le h 5 (lo := lo) (hi := hi) (n := N - 1)
    (by omega) (hNL' _ (by omega)) (by omega) (by omega) (Γ := Γ₁)
    (fun A h₁ h₂ => (hΓ₁ A h₁ h₂).1) T
  have bD := law_exploration_dualConfig_le_pow_of_le h 5 (lo := lo₂) (hi := hi₂) (n := N)
    (by omega) (hNL' _ le_rfl) (by omega) (by omega) (Γ := Γ₂) (fun A h₁ h₂ => (hΓ₂ A h₁ h₂).1) T
  have b1 := fun v => law_exploration_forall_notMem_inter_le h (lo := lo) (hi := hi) (Γ := Γ₁)
    measurable_id hPo d₁ hsc1 (h8 s₀) v J hJs
  have b2 := fun v => law_exploration_forall_notMem_dualConfig_union_le h (lo := lo) (hi := hi)
    (Γ := Γ₁) measurable_id hPo (fun D => ![d₁ D 0, hi 1 - 1]) hsc1 (h8 s₀) v J hJs
  have b3 := fun v => law_exploration_forall_notMem_union_le h (lo := lo) (hi := hi) (Γ := Γ₁)
    measurable_id hPo d₁ htc1 (h8 (K + 1)) v J hJt
  have b4 := fun v => law_exploration_forall_notMem_dualConfig_union_le h (lo := lo₂) (hi := hi₂)
    (Γ := Γ₂) measurable_dualConfig hPd d₂ hsc1 (h8 s₀) v J hJs
  have b5 := fun v => law_exploration_forall_notMem_inter_le h (lo := lo₂) (hi := hi₂) (Γ := Γ₂)
    measurable_dualConfig hPd (fun D => ![d₂ D 0, hi₂ 1 - 1] + 1) hsc1 (h8 s₀) v J hJs
  have b6 := fun v => law_exploration_forall_notMem_dualConfig_inter_le h (lo := lo₂) (hi := hi₂)
    (Γ := Γ₂) measurable_dualConfig hPd d₂ htc1 (h8 (K + 1)) v J hJt
  have b7 := law_forall_notMem_inter_le h ![hi 0, hi 1] hsc1 (h8 s₀) J hJs
  have b8 := law_forall_notMem_inter_le h ![lo 0, hi 1] hsc1 (h8 s₀) J hJs
  have b9 := law_forall_notMem_dualConfig_union_le h ![hi₂ 0, hi₂ 1] hsc1 (h8 s₀) J hJs
  have b10 := law_forall_notMem_dualConfig_union_le h ![lo₂ 0, hi₂ 1] hsc1 (h8 s₀) J hJs
  have hbad := measure_union_le_add_of_le bO (measure_union_le_add_of_le bD
    (measure_union_le_add_of_le (measure_biUnion_range_le (T + 1) fun v _ => b1 v)
    (measure_union_le_add_of_le (measure_biUnion_range_le (T + 1) fun v _ => b2 v)
    (measure_union_le_add_of_le (measure_biUnion_range_le (T + 1) fun v _ => b3 v)
    (measure_union_le_add_of_le (measure_biUnion_range_le (T + 1) fun v _ => b4 v)
    (measure_union_le_add_of_le (measure_biUnion_range_le (T + 1) fun v _ => b5 v)
    (measure_union_le_add_of_le (measure_biUnion_range_le (T + 1) fun v _ => b6 v)
    (measure_union_le_add_of_le b7 (measure_union_le_add_of_le b8
    (measure_union_le_add_of_le b9 b10))))))))))
  refine one_sub_le_measure_of_forall_notMem (hbad.trans ?_) fun ω hω => ?_
  · -- the sum of the bounds
    have hT' := (hT (T + 1) (by omega)).le
    have hJ' := (hJ J le_rfl).le
    calc _ = ((1 - c 6) ^ (T + 1) + (1 - c 6) ^ (T + 1)) +
          ((6 * (T + 1) + 4 : ℕ) : ℝ≥0∞) * (1 - c 7 ^ 4) ^ J := by
          push_cast
          ring
      _ ≤ (δ / 2 / 2 + δ / 2 / 2) +
          ((6 * (T + 1) + 4 : ℕ) : ℝ≥0∞) * (δ / 2 / ((6 * (T + 1) + 4 : ℕ) : ℝ≥0∞)) := by
          gcongr
      _ ≤ δ / 2 + δ / 2 := by
          rw [ENNReal.add_halves]
          gcongr
          exact ENNReal.mul_div_le
      _ = δ := ENNReal.add_halves δ
  · -- outside the bad events, the separation holds
    simp only [mem_union, not_or] at hω
    obtain ⟨hO, hD', hU1, hU2, hU3, hU4, hU5, hU6, hC1, hC2, hC3, hC4⟩ := hω
    have hF : ∀ {F : ℕ → Set (Config (LatticeSite 2))},
        ω ∉ ⋃ v ∈ Finset.range (T + 1), F v → ∀ v ≤ T, ω ∉ F v :=
      fun hU v hv hv' => hU (mem_iUnion₂.2 ⟨v, Finset.mem_range.2 (by omega), hv'⟩)
    intro m σ a b γ hcr hdisj
    obtain ⟨b', γ', h1, h2, h3, h4, h5, h6⟩ := separable_of_forall (lo := lo) (hi := hi)
      (lo₂ := lo₂) (hi₂ := hi₂) hk hk1 hlo₂ hhi₂ (by omega) (by omega) (T := T) (s₀ := s₀)
      (K := K) (M := M) (by omega) (by omega) hΓ₁ hΓ₂
      (fun A hA => by
        by_contra hcon
        push Not at hcon
        exact hO ⟨A, hA, hcon⟩)
      (fun A hA => by
        by_contra hcon
        push Not at hcon
        exact hD' ⟨A, hA, hcon⟩)
      (fun v hv A hA hadm => by
        by_contra hcon
        exact hF hU1 v hv ⟨A, hA, fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j,
          hsO j hj, notMem_crossing_sdiff_of_inter _ _ _ hK⟩⟩)
      (fun v hv A hA hadm => by
        by_contra hcon
        exact hF hU2 v hv ⟨A, hA, fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j,
          hsO j hj, notMem_crossing_dualConfig_union_of _ _ _ hK⟩⟩)
      (fun v hv A hA hadm => by
        by_contra hcon
        exact hF hU3 v hv ⟨A, hA, fun j hj hK => hcon ⟨(K + 1) * 8 ^ j, htc1 j, hKle j,
          htcM j hj, htO j hj, mem_crossing_union_of _ _ hK⟩⟩)
      (fun v hv A hA hadm => by
        by_contra hcon
        exact hF hU4 v hv ⟨A, hA, fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j,
          hsD j hj, notMem_crossing_dualConfig_sdiff_of _ _ _ hK⟩⟩)
      (fun v hv A hA hadm => by
        by_contra hcon
        exact hF hU5 v hv ⟨A, hA, fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j,
          hsD j hj,
          notMem_crossing_dualConfig_dualConfig_union_of _ _ _ hK⟩⟩)
      (fun v hv A hA hadm => by
        by_contra hcon
        exact hF hU6 v hv ⟨A, hA, fun j hj hK => hcon ⟨(K + 1) * 8 ^ j, htc1 j, hKle j,
          htcM j hj, htD j hj, mem_crossing_dualConfig_union_of _ _ hK⟩⟩)
      (by
        by_contra hcon
        exact hC1 fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j, by have := hsO j hj; omega,
          (notMem_crossing_inter_of _ _ _ hK).1, (notMem_crossing_inter_of _ _ _ hK).2.2⟩)
      (by
        by_contra hcon
        exact hC2 fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j, by have := hsO j hj; omega,
          (notMem_crossing_inter_of _ _ _ hK).1, (notMem_crossing_inter_of _ _ _ hK).2.1⟩)
      (by
        by_contra hcon
        exact hC3 fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j, by have := hsD j hj; omega,
          (notMem_crossing_dualConfig_inter_of _ _ _ hK).1,
          (notMem_crossing_dualConfig_inter_of _ _ _ hK).2.2⟩)
      (by
        by_contra hcon
        exact hC4 fun j hj hK => hcon ⟨s₀ * 8 ^ j, hs₀le j, by have := hsD j hj; omega,
          (notMem_crossing_dualConfig_inter_of _ _ _ hK).1,
          (notMem_crossing_dualConfig_inter_of _ _ _ hK).2.1⟩)
      m σ a b γ hcr hdisj
    refine ⟨b', γ', h1, h2, fun i j hij => ?_, fun i => ?_, h5, fun i => ?_⟩
    · have h' := Int.cast_lt (R := ℝ) |>.2 (h3 i j hij)
      push_cast at h' ⊢
      linarith
    · obtain ⟨h₁, h₂⟩ := h4 i
      have h₁' := Int.cast_lt (R := ℝ) |>.2 h₁
      have h₂' := Int.cast_lt (R := ℝ) |>.2 h₂
      simp only [Matrix.cons_val_zero]
      push_cast at h₁' h₂' ⊢
      constructor <;> linarith
    · rw [hKfl, hMfl]
      exact h6 i


/-- **Nolin's local separation lemma** (EJP 2008, Lemma 15). For every `δ > 0` there are `η > 0`
and `N₀` such that, uniformly over the laws with crossing bounds `c` up to `L`, for `N₀ ≤ N ≤ L`,
with probability at least `1 - δ` the following holds in the strip `Q = [0, 4N] × [0, N]`. Every
family of crossings of `Q` from bottom to top, each open (`σ i = true`: a walk of `ℤ²` in `Q` from
the bottom row to the top row along open edges) or dual (`σ i = false`: a walk of faces of
`[0, 4N - 1] × [-1, N]` from the row `-1` to the row `N` along dual-open dual edges crossing edges
of `Q`), with crossings of the same colour disjoint, can be replaced by a family with the same
colours and the same starting points, with crossings of the same colour disjoint, whose ends `b' i`,
in doubled positions (`2 x` for an open end `(x, N)`, `2 x + 1` for a dual end `(x, N)`), are at
least `4 √η N` apart and at least `4 √η N` from both ends `0` and `8 N` of the doubled top side,
and each of which carries a fence (Nolin's condition (4.5)): some vertex of the new crossing is
joined, in its colour and inside the ball of radius `⌊√η N⌋` around its end, to the left end of a
left-right crossing of its colour of the box `[x - ⌊η N⌋, x + ⌊η N⌋] × [N, N + ⌊√η N⌋]` above its
end `(x, N)`. -/
theorem exists_law_separable_ge (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ N : ℕ, N₀ ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = 0 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ), N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = -1 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![0, -1] : LatticeSite 2) ![4 * (N : ℤ) - 1, N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ), N]})) →
        (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
        ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = 0 ∧ b' i 1 = N ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ), N]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = -1 ∧ b' i 1 = N ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![0, -1] : LatticeSite 2) ![4 * (N : ℤ) - 1, N]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ), N]})) ∧
          (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ' i).support, x ∉ (γ' j).support) ∧
          (∀ i j, i ≠ j → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' j 0 + cond (σ j) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ 8 * N - ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, N] ![b' i 0 + ⌊η * N⌋₊, N + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨η, hη, N₀, hsep⟩ := exists_law_separable_ge_aux c hδ
  refine ⟨η, hη, N₀, fun q L h N hN hNL => (hsep q L h N hN hNL 0 0 ![4 * (N : ℤ), N] ![0, -1]
    ![4 * (N : ℤ) - 1, N] 0 ![4 * (N : ℤ), N] le_rfl zero_le_one
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩) (eq_vec_two_iff.2 ⟨by simp, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩) (eq_vec_two_iff.2 ⟨by simp, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩)).trans (measure_mono fun ω hω => ?_)⟩
  intro m σ a b γ hcr hdisj
  obtain ⟨b', γ', h1, h2, h3, h4, -, h5⟩ := hω m σ a b γ hcr hdisj
  refine ⟨b', γ', h1, h2, h3, fun i => ?_, h5⟩
  obtain ⟨h₁, h₂⟩ := h4 i
  simp only [Pi.zero_apply, mul_zero, sub_zero, Matrix.cons_val_zero] at h₁ h₂
  push_cast at h₁ h₂ ⊢
  exact ⟨h₁, by linarith⟩

/-- **Nolin's local separation lemma in the arm box** (EJP 2008, Lemma 15, in the geometry of the
arms of a box). The statement of `exists_law_separable_ge` with the box of faces one column wider
on each side than the open box: open crossings of `[1, 4N + 1] × [0, N]` (`σ i = true`), dual
crossings (`σ i = false`) of the faces `[0, 4N + 1] × [-1, N]` from the row `-1` to the row `N`
along dual-open dual edges crossing edges of `[0, 4N + 2] × [0, N]`; the new crossings meet the
top row `N` only at their ends, and their ends, in doubled positions (`2 x` for an open end
`(x, N)`, `2 x + 1` for a dual end `(x, N)`), are at least `4 √η N` apart and at least `4 √η N`
from both ends `0` and `8 N + 4` of the doubled top side; each carries the fence of
`exists_law_separable_ge`.

This is the geometry of the arms to the box `[0, 4N + 2] × [-3N - 2, N]` (centre
`(2N + 1, -N - 1)`, radius `2N + 1`) near its top side: before its last vertex an open arm lies in
the columns `[1, 4N + 1]` and a dual arm in the face columns `[0, 4N + 1]`, the last vertex of an
open arm landing on the top side is `(x, N)` with `1 ≤ x ≤ 4N + 1`, the last face of a dual arm
landing there is `(x, N)` with `0 ≤ x ≤ 4N + 1`, and the doubled positions are the top-side
columns of `landingPos`. -/
theorem exists_law_separable_ge_arm (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ N : ℕ, N₀ ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = 0 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![1, 0] : LatticeSite 2) ![4 * (N : ℤ) + 1, N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = -1 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![0, -1] : LatticeSite 2) ![4 * (N : ℤ) + 1, N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ) + 2, N]})) →
        (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
        ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = 0 ∧ b' i 1 = N ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![1, 0] : LatticeSite 2) ![4 * (N : ℤ) + 1, N]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = -1 ∧ b' i 1 = N ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![0, -1] : LatticeSite 2) ![4 * (N : ℤ) + 1, N]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ) + 2, N]})) ∧
          (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ' i).support, x ∉ (γ' j).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ N) ∧
          (∀ i j, i ≠ j → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' j 0 + cond (σ j) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ 8 * N + 4 - ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, N] ![b' i 0 + ⌊η * N⌋₊, N + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨η, hη, N₀, hsep⟩ := exists_law_separable_ge_aux c hδ
  refine ⟨η, hη, N₀, fun q L h N hN hNL => (hsep q L h N hN hNL 1 ![1, 0] ![4 * (N : ℤ) + 1, N]
    ![0, -1] ![4 * (N : ℤ) + 1, N] 0 ![4 * (N : ℤ) + 2, N] zero_le_one le_rfl
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩) (eq_vec_two_iff.2 ⟨by simp, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp only [Matrix.cons_val_zero]; ring, by simp⟩)).trans
    (measure_mono fun ω hω => ?_)⟩
  intro m σ a b γ hcr hdisj
  obtain ⟨b', γ', h1, h2, h3, h4, h5, h6⟩ := hω m σ a b γ hcr hdisj
  refine ⟨b', γ', h1, h2, h5, h3, fun i => ?_, h6⟩
  obtain ⟨h₁, h₂⟩ := h4 i
  simp only [Pi.zero_apply, mul_zero, sub_zero, Matrix.cons_val_zero] at h₁ h₂
  push_cast at h₁ h₂ ⊢
  exact ⟨h₁, by linarith⟩

end PercLib.Models.Planar
