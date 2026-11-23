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
(`exists_walk_trim`) or translated (`exists_walk_map_sub_one`) into the dual box of the left one's
exploration.

## Main results

* `exists_fence_of_le`: a fence of the fence lemma gives a fence in a narrower box.
* `exists_reroute_fence_of_exploration`: a family of crossings of one colour is rerouted to greedy
  tips, each with a fence.
* `exists_law_separable_ge`: **Nolin's local separation lemma.**
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
crossings, pairwise disjoint, and each new walk has a vertex `x` joined inside the ball of radius
`M` around its end to the left end of a left-right crossing of the fence box
`[z₀ - K, z₀ + K] × [z₁, z₁ + M]` above its end `z`. -/
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
  obtain ⟨w, γ', hw, -, hwd, -, hG, hbox, hdisj', hdrop, hopen, hedge⟩ :=
    exists_reroute_of_exploration h1 hle (fun A' h₁ h₂ => (hΓ A' h₁ h₂).1) hA hu S γc
      (fun i hi x hx => hγ i hi x ((hγc i hi).2.2.1 x hx)) ha (fun i hi => (hγc i hi).1)
      (fun i hi e he => hγG i hi e ((hγc i hi).2.2.2 e he))
      fun i hi j hj hij x hx hx' =>
        hdisj i hi j hj hij x ((hγc i hi).2.2.1 x hx) ((hγc j hj).2.2.1 x hx')
  refine ⟨w, γ', hw, hwd, hbox, hG, fun i hi e he => ?_, hdisj', fun i hi => ?_⟩
  · rcases hedge i hi e he with h | h
    · exact Or.inl ((hγc i hi).2.2.2 e h)
    · exact Or.inr h
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
tip. A clean dual path `p` in the box of faces `[lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]` from its bottom row
to its top row, landing at or right of the tip, lands more than `s` to its right. -/
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
    (hpS : ∀ x ∈ p.support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1])
    (ha' : a' 1 = lo 1 - 1) (hb' : b' 1 = hi 1)
    (hbot : ∀ x ∈ p.support, x 1 = lo 1 - 1 → x = a')
    (htop : ∀ x ∈ p.support, x 1 = hi 1 → x = b')
    (hpG : ∀ e ∈ p.edges, e ∈ dualConfig ω) (hdb : d (A v) 0 ≤ b' 0) :
    d (A v) 0 + s < b' 0 := by
  obtain ⟨y, q, hy, hqS, hqE⟩ := exists_walk_trim (lo := ![lo 0, lo 1 - 1])
    (hi := ![hi 0 - 1, hi 1]) (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
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

end PercLib.Models.Planar
