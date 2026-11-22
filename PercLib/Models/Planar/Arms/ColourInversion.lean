/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.1 (arm events, p. 1572) and Remark 26 (p. 1592, colour
exchange); H. Kesten, Percolation theory for mathematicians, Birkhäuser, 1982 (self-duality of
bond percolation on the square lattice at one half).
-/
module

public import PercLib.Models.Planar.Arms.MultiArmBounds

/-!
# Colour inversion of multi-arm events at one half

On the square lattice the dual of bond percolation with parameter `1/2` is again bond percolation
with parameter `1/2`, on the lattice of faces. An open arm of `ω` is a dual arm of the dual
configuration, translated by half a lattice step in each direction, and a dual arm of `ω` is an
open arm of the dual configuration. So, at one half, a multi-arm event and the event with all
colours inverted have comparable probabilities. Because the dual lattice is shifted, the inverted
arms are cut at both ends, and the inequality loses one unit at each radius:

`π_σ(r, R) ≤ π_{not ∘ σ}(r + 1, R - 1)` for `r + 2 < R`.

* **Cutting the arms.** An open arm of `ω` from `B_r(z)` to the boundary of `B_R(z)` is started at
  its last vertex in `Icc (z - r - 1) (z + r + 2)` and stopped at its first vertex outside
  `Icc (z - R + 2) (z + R - 1)`; translated by `(-1, -1)` it is a dual arm of `dualConfig ω` from
  `B_{r+1}(z)` to the boundary of `B_{R - 1}(z)`. A dual arm of `ω` is started at its last face in
  `Icc (z - r - 1) (z + r + 1)` and stopped at its first face outside
  `Icc (z - R + 2) (z + R - 2)`; it is an open arm of `dualConfig ω`. The second vertex of an open
  arm lies in the larger inner box, so the cut open arms lie in the tails of the old ones and the
  new family is disjoint.
* **Order.** In the doubled lattice of `ω`, the new landing positions are the positions, on the
  boundary of the intermediate box `Icc (2 (z - R') + 1) (2 (z + R') + 1)` with `R' = R - 1`, of
  the points where the old doubled arms first leave its interior. Order invariance for walks that
  run inside the doubled arms of a disjoint family, from their starts to the boundary of an
  intermediate box (`sbtw_innerPos_iff_sbtw_perimeterPos`), and order invariance of the old family
  then carry the counterclockwise order of the old landing positions to the new ones.
* **Probability.** The multi-arm event reads only edges of `ℤ²`, so self-duality at one half
  (`law_preimage_dualConfig_eq`) gives the inequality.

## Main results

* `dualConfig_mem_multiArmEvent`: `ω ∈ A_σ(z, r, R)` implies
  `dualConfig ω ∈ A_{not ∘ σ}(z, r + 1, R - 1)` for `r + 2 < R`, for every configuration.
* `law_multiArmEvent_comp_not_le`: colour inversion at one half,
  `law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent (not ∘ σ) z (r + 1) (R - 1))`.
* `sbtw_innerPos_iff_sbtw_perimeterPos`: order invariance for walks inside the doubled arms of a
  disjoint family, ending on the boundary of an intermediate box.
* `IsArm.exists_dualConfig`: the inverted arm cut out of an arm, with a walk of the doubled lattice
  from the start of the doubled arm to the point of the new landing position.
* `exists_walk_double_tail_dropLast`: the doubled walk without its first and last vertices.
* `SimpleGraph.Walk.IsCrossing.exists_append_append_eq`: a crossing cut at both ends.

## Implementation notes

* The loss of one unit at each radius comes from the half-lattice shift between `ℤ²` and its dual:
  the faces touching `B_r(z)` reach `B_{r+1}(z)` after the translation, and the faces of `B_R(z)`
  reach out to its boundary.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {S T : Set V} {u v : V} {p : G.Walk u v}

/-- **Cutting a crossing at both ends.** A crossing from `S` out of `T`, stopped at its first vertex
outside a smaller set `T'` and then started at its last vertex in a larger set `S'`, is a crossing
from `S'` out of `T'`; the part up to the first exit is a crossing from `S` out of `T'`. -/
theorem IsCrossing.exists_append_append_eq {S' T' : Set V} (h : p.IsCrossing S T) (hS' : S ⊆ S')
    (hT' : T' ⊆ T) : ∃ x y, ∃ (q : G.Walk u x) (s : G.Walk x y) (t : G.Walk y v),
      (q.append s).append t = p ∧ (q.append s).IsCrossing S T' ∧ s.IsCrossing S' T' := by
  obtain ⟨y, q₁, t, h₁, hq₁⟩ := h.exists_append_eq_isCrossing hT'
  obtain ⟨x, q, s, h₂, hs⟩ := hq₁.exists_append_eq_isCrossing_of_subset hS'
  subst h₂
  exact ⟨x, y, q, s, t, h₁, hq₁, hs⟩

/-- A walk followed by a crossing from `S'` has a step before the crossing when the combined walk
meets `S'` after its first vertex. -/
theorem IsCrossing.not_nil_of_mem_tail_support_append {S' T' : Set V} {x y : V} {q : G.Walk u x}
    {s : G.Walk x y} (hs : s.IsCrossing S' T') {w : V} (hw : w ∈ (q.append s).support.tail)
    (hwS : w ∈ S') : ¬q.Nil := by
  cases q with
  | nil =>
    rw [nil_append] at hw
    exact absurd hwS (hs.notMem_of_mem_tail w hw)
  | cons h q => exact not_nil_cons

/-- The vertices of the second part of `q.append s` lie in the tail of its support when `q` has a
step. -/
theorem mem_tail_support_append_of_mem_support {x y : V} {q : G.Walk u x} (s : G.Walk x y)
    (hq : ¬q.Nil) {w : V} (hw : w ∈ s.support) : w ∈ (q.append s).support.tail := by
  rw [tail_support_append, List.mem_append]
  rcases (mem_support_iff s).1 hw with rfl | hw
  · exact Or.inl (end_mem_tail_support hq)
  · exact Or.inr hw

/-- A vertex of a walk other than its last vertex is a vertex of the support without its last
entry (`List.mem_dropLast_of_mem_of_ne_getLast` for the support). -/
theorem mem_dropLast_support_of_mem_of_ne {w : V} (hw : w ∈ p.support) (hwv : w ≠ v) :
    w ∈ p.support.dropLast :=
  List.mem_dropLast_of_mem_of_ne_getLast hw (by rwa [getLast_support])

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Doubled walks and points of the doubled boxes -/

/-- **Doubling a walk, without its first and last vertices.** A walk `v₀, v₁, …, v_m` of `ℤ²` with
at least one step gives the walk `v₀ + v₁ + c, 2v₁ + c, v₁ + v₂ + c, …, 2v_{m-1} + c,
v_{m-1} + v_m + c`, from the midpoint of its first step to the midpoint of its last step (in the
doubled lattice, translated by `c`). -/
theorem exists_walk_double_tail_dropLast (c : LatticeSite 2) {u v : LatticeSite 2}
    (γ : (zdGraph 2).Walk u v) (hγ : ¬γ.Nil) :
    ∃ D : (zdGraph 2).Walk (u + γ.snd + c) (γ.penultimate + v + c), ∀ x, x ∈ D.support ↔
      (∃ w ∈ γ.support.tail.dropLast, x = 2 • w + c) ∨ ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + c := by
  cases γ with
  | nil => exact absurd SimpleGraph.Walk.Nil.nil hγ
  | cons h p =>
    rename_i u'
    by_cases hp : p.Nil
    · cases p with
      | nil =>
        rw [SimpleGraph.Walk.snd_cons, SimpleGraph.Walk.penultimate_cons_nil]
        refine ⟨.nil, fun x => ?_⟩
        simp
      | cons h' p' => exact absurd hp SimpleGraph.Walk.not_nil_cons
    · obtain ⟨D, hD⟩ := exists_walk_double_dropLast c p hp
      have h' := (zdGraph_two_adj_iff _ _).1 h
      have h₁ : (zdGraph 2).Adj (u + u' + c) (2 • u' + c) := by
        rw [zdGraph_two_adj_iff]
        simp only [Pi.add_apply, two_nsmul]
        omega
      rw [SimpleGraph.Walk.snd_cons, SimpleGraph.Walk.penultimate_cons_of_not_nil h p hp]
      refine ⟨.cons h₁ D, fun x => ?_⟩
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

/-- The last vertex of a walk of `ℤ²` crossing out of the interior `Icc (lo + 1) (hi - 1)`, with at
least one step, lies in `Icc lo hi`, as do all its vertices. -/
theorem mem_Icc_of_isCrossing {S : Set (LatticeSite 2)} {lo hi u v : LatticeSite 2}
    {p : (zdGraph 2).Walk u v} (hp : p.IsCrossing S (Icc (lo + 1) (hi - 1))) (hn : ¬p.Nil)
    {w : LatticeSite 2} (hw : w ∈ p.support) : w ∈ Icc lo hi := by
  rw [← SimpleGraph.Walk.dropLast_support_concat p, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · have hw' := hp.mem_of_mem_dropLast w hw
    rw [mem_Icc_two_iff] at hw' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hw'
    omega
  · exact mem_Icc_of_adj_of_mem_Icc_sub_one (SimpleGraph.Walk.adj_penultimate hn)
      (hp.penultimate_mem hn)

/-- The midpoint of an edge leaving a point of `Icc (lo + 1) hi` lies in the doubled box
`Icc (2 lo + 1) (2 hi + 1)`. -/
theorem add_mem_Icc_of_adj {lo hi u v : LatticeSite 2} (huv : (zdGraph 2).Adj u v)
    (hu : u ∈ Icc (lo + 1) hi) : u + v ∈ Icc (2 • lo + 1) (2 • hi + 1) := by
  have h := (zdGraph_two_adj_iff u v).1 huv
  rw [mem_Icc_two_iff] at hu ⊢
  simp only [Pi.add_apply, Pi.one_apply, two_nsmul] at hu ⊢
  omega

/-- The midpoint of an edge from a point of `Icc (lo + 1) hi` to a point outside lies on the
boundary of the doubled box `Icc (2 lo + 1) (2 hi + 1)`. -/
theorem add_mem_boxBoundary_of_adj {lo hi u v : LatticeSite 2} (huv : (zdGraph 2).Adj u v)
    (hu : u ∈ Icc (lo + 1) hi) (hv : v ∉ Icc (lo + 1) hi) :
    u + v ∈ boxBoundary (2 • lo + 1) (2 • hi + 1) := by
  have h := (zdGraph_two_adj_iff u v).1 huv
  rw [mem_Icc_two_iff] at hu hv
  rw [mem_boxBoundary_two_iff]
  simp only [Pi.add_apply, Pi.one_apply, two_nsmul] at hu hv ⊢
  omega

/-- The doubled centre `2v + (1, 1)` of a face of `Icc lo hi` lies in
`Icc (2 lo + 1) (2 hi + 1)`. -/
theorem two_nsmul_add_one_mem_Icc {lo hi v : LatticeSite 2} (hv : v ∈ Icc lo hi) :
    2 • v + 1 ∈ Icc (2 • lo + 1) (2 • hi + 1) := by
  rw [mem_Icc_two_iff] at hv ⊢
  simp only [Pi.add_apply, Pi.one_apply, two_nsmul]
  omega

/-- A boundary point `v` of `Icc lo hi` gives the boundary point `2v + (1, 1)` of
`Icc (2 lo + 1) (2 hi + 1)`. -/
theorem two_nsmul_add_one_mem_boxBoundary {lo hi v : LatticeSite 2} (hv : v ∈ boxBoundary lo hi) :
    2 • v + 1 ∈ boxBoundary (2 • lo + 1) (2 • hi + 1) := by
  rw [mem_boxBoundary_two_iff] at hv ⊢
  simp only [Pi.add_apply, Pi.one_apply, two_nsmul]
  omega

/-! ### Order invariance for walks inside doubled arms -/

/-- **Order invariance for walks inside the doubled arms.** Let `B_r(z)` lie in the interior of
`Icc lo hi` and let `γ` be a disjoint family of arms of colours `σ` from `B_r(z)` to the boundary of
`Icc lo hi`. Let `P i` be walks of the doubled lattice from the starts of the doubled arms (the
points of the inner positions), each through points of the doubled arm `i` only, inside a box
`Icc lo' hi'` whose interior contains the doubled inner box, and ending on its boundary at `e i`.
Then three arms have their inner positions in counterclockwise order exactly when the points `e i`
are in counterclockwise order on the boundary of `Icc lo' hi'`. The walks `P i` need not stop at
their first exit from the interior of `Icc lo' hi'`. -/
theorem sbtw_innerPos_iff_sbtw_perimeterPos {j : ℕ} {σ : Fin j → Bool}
    {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)) {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i))
    (hd : ArmsDisjoint σ γ) {lo' hi' : LatticeSite 2}
    (hlo : lo' + 1 ≤ 2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
    (hhi : 2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2) + 1 ≤ hi') {e : Fin j → LatticeSite 2}
    (P : ∀ i, (zdGraph 2).Walk (cond (σ i) (a i + (γ i).snd) (2 • a i + 1)) (e i))
    (hP : ∀ i, ∀ x ∈ (P i).support,
      (∃ w ∈ cond (σ i) (γ i).support.tail (γ i).support.dropLast, x = 2 • w + cond (σ i) 0 1) ∨
        ∃ δ ∈ (γ i).darts, x = δ.fst + δ.snd + cond (σ i) 0 1)
    (hPO : ∀ i, ∀ x ∈ (P i).support, x ∈ Icc lo' hi') (he : ∀ i, e i ∈ boxBoundary lo' hi')
    (i k l : Fin j) :
    sbtw (innerPos z r (σ i) (γ i)) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) ↔
      sbtw (perimeterPos lo' hi' (e i)) (perimeterPos lo' hi' (e k))
        (perimeterPos lo' hi' (e l)) := by
  have h₀ : (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2)) 0 <
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) 0 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    omega
  have h₁ : (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2)) 1 <
      (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) 1 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    omega
  have hs : ∀ i, cond (σ i) (a i + (γ i).snd) (2 • a i + 1) ∈
      boxBoundary (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
        (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) := fun i => by
    obtain ⟨-, -, hs, -⟩ := (hγ i).exists_double hB
    exact hs
  have key := cyclicallyOrdered_end_iff_of_pairwise_disjoint h₀ h₁ hlo hhi P hs he
    (fun i x hx => by
      obtain ⟨D, hDs, -, -, hDO⟩ := (hγ i).exists_double hB
      exact ⟨hPO i x hx, (hDO x ((hDs x).2 (hP i x hx))).2⟩)
    (fun i k hik x hx hx' => (hγ i).double_disjoint (hγ k) (hd.1 i k hik) (hd.2 i k hik)
      (hP i x hx) (hP k x hx')) i k l
  rw [Int.sbtw_iff, Int.sbtw_iff]
  exact key

/-! ### Inverting the colour of one arm -/

section Inversion

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r R : ℕ} {lo hi : LatticeSite 2}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **An open walk, translated by `(-1, -1)`, is a dual arm of the dual configuration.** A walk of
`ℤ²` along edges open in `ω` crossing from `Icc (z - r) (z + r + 1)` out of `Icc (lo + 1) hi`,
translated by `(-1, -1)`, is a dual arm of `dualConfig ω` from `B_r(z)` to the boundary of
`Icc lo hi`. Here `g` is the translation by `(-1, -1)`. -/
theorem isDualArm_dualConfig_map_of_isCrossing {g : zdGraph 2 →g zdGraph 2}
    (hg : ∀ v, g v = v - 1) {x y : LatticeSite 2} {p : (zdGraph 2).Walk x y}
    (hp : p.IsCrossing (Icc (z - r) (z + r + 1)) (Icc (lo + 1) hi))
    (hpω : ∀ e ∈ p.edges, e ∈ ω) : IsDualArm (dualConfig ω) z r lo hi (p.map g) := by
  have hg' : (⇑g : LatticeSite 2 → LatticeSite 2) = (· + -1) :=
    funext fun v => (hg v).trans (sub_eq_add_neg v 1)
  have hinj : Function.Injective g := by
    rw [hg']
    exact add_left_injective _
  have himage : ∀ p q : LatticeSite 2, ⇑g '' Icc p q = Icc (p - 1) (q - 1) := fun p q => by
    rw [hg', image_add_const_Icc, ← sub_eq_add_neg, ← sub_eq_add_neg]
  refine ⟨?_, fun e he => ?_⟩
  · have := (SimpleGraph.Walk.isCrossing_map_iff hinj).2 hp
    rwa [himage, himage, add_sub_cancel_right, add_sub_cancel_right] at this
  · rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    rw [dualConfig_dualConfig]
    refine ⟨e₀, ⟨hpω e₀ he₀, p.edges_subset_edgeSet he₀⟩, ?_⟩
    congr 1
    funext v
    exact (hg v).symm

/-- **Colour inversion of an open arm.** An open arm of `ω` from `B_r(z)` to the boundary of
`B_{R+1}(z)`, started at its last vertex in `Icc (z - r - 1) (z + r + 2)` and stopped at its first
vertex outside `Icc (z - R + 1) (z + R)`, then translated by `(-1, -1)`, is a dual arm of
`dualConfig ω` from `B_{r+1}(z)` to the boundary of `B_R(z)`, whose vertices translated back lie in
the tail of the open arm. Its landing position is the position, on the boundary of
`Icc (2 (z - R) + 1) (2 (z + R) + 1)`, of the end of a walk through the doubled open arm from its
start. -/
theorem IsOpenArm.exists_isDualArm_dualConfig
    (h : IsOpenArm ω z r (z - ((R + 1 : ℕ) : LatticeSite 2)) (z + ((R + 1 : ℕ) : LatticeSite 2)) γ)
    (hrR : r + 1 < R) :
    ∃ (x y : LatticeSite 2) (γ' : (zdGraph 2).Walk x y),
      IsDualArm (dualConfig ω) z (r + 1) (z - R) (z + R) γ' ∧
      (∀ v ∈ γ'.support, v + 1 ∈ γ.support.tail) ∧
      ∃ (e : LatticeSite 2) (P : (zdGraph 2).Walk (a + γ.snd) e),
        (∀ x ∈ P.support, (∃ w ∈ γ.support.tail, x = 2 • w + 0) ∨
          ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + 0) ∧
        (∀ x ∈ P.support,
          x ∈ Icc (2 • (z - (R : LatticeSite 2)) + 1) (2 • (z + (R : LatticeSite 2)) + 1)) ∧
        e ∈ boxBoundary (2 • (z - (R : LatticeSite 2)) + 1) (2 • (z + (R : LatticeSite 2)) + 1) ∧
        landingPos (z - R) (z + R) false γ' =
          perimeterPos (2 • (z - (R : LatticeSite 2)) + 1)
            (2 • (z + (R : LatticeSite 2)) + 1) e := by
  have hS' : Icc (z - (r : LatticeSite 2)) (z + r) ⊆
      Icc (z - ((r + 1 : ℕ) : LatticeSite 2)) (z + ((r + 1 : ℕ) : LatticeSite 2) + 1) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.sub_apply, Pi.natCast_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  have hT' : Icc (z - (R : LatticeSite 2) + 1) (z + R) ⊆
      Icc (z - ((R + 1 : ℕ) : LatticeSite 2) + 1) (z + ((R + 1 : ℕ) : LatticeSite 2) - 1) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  obtain ⟨x, y, q, s, t, hqst, hQ, hs⟩ := h.isCrossing.exists_append_append_eq hS' hT'
  have hQn : ¬(q.append s).Nil := hQ.not_nil (Icc_subset_Icc (fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.natCast_apply]
      omega)
  have hsn : ¬s.Nil := hs.not_nil (Icc_subset_Icc (fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
      omega)
  have hsnd : (q.append s).snd = γ.snd := by
    rw [← hqst, SimpleGraph.Walk.snd_append_of_not_nil _ hQn]
  -- the second vertex of the arm lies in the larger inner box, so the cut starts after it
  have hsndS : (q.append s).snd ∈
      Icc (z - ((r + 1 : ℕ) : LatticeSite 2)) (z + ((r + 1 : ℕ) : LatticeSite 2) + 1) := by
    have ha := hQ.start_mem
    have hadj := (zdGraph_two_adj_iff _ _).1 (SimpleGraph.Walk.adj_snd hQn)
    rw [mem_Icc_two_iff] at ha ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at ha ⊢
    omega
  have hqn : ¬q.Nil :=
    hs.not_nil_of_mem_tail_support_append (SimpleGraph.Walk.snd_mem_tail_support hQn) hsndS
  have hpen : (q.append s).penultimate = s.penultimate :=
    SimpleGraph.Walk.penultimate_append_of_not_nil q hsn
  have htail : ∀ w ∈ (q.append s).support.tail, w ∈ γ.support.tail := fun w hw => by
    rw [← hqst, SimpleGraph.Walk.tail_support_append]
    exact List.mem_append_left _ hw
  have hdarts : ∀ δ ∈ (q.append s).darts, δ ∈ γ.darts := fun δ hδ => by
    rw [← hqst, SimpleGraph.Walk.darts_append]
    exact List.mem_append_left _ hδ
  let g : zdGraph 2 →g zdGraph 2 := ⟨(· - 1), fun {x y} hxy =>
    (zdGraph_adj_iff_of_sub fun i => by simp only [Pi.sub_apply, sub_sub_sub_cancel_right]).2 hxy⟩
  have hg : ∀ v, g v = v - 1 := fun _ => rfl
  obtain ⟨D, hD⟩ := exists_walk_double_tail_dropLast 0 (q.append s) hQn
  refine ⟨g x, g y, s.map g, isDualArm_dualConfig_map_of_isCrossing hg hs fun e he =>
      h.mem_of_mem_edges e ?_, fun v hv => ?_, (q.append s).penultimate + y,
    D.copy (by rw [hsnd, add_zero]) (add_zero _), fun v hv => ?_, fun v hv => ?_, ?_, ?_⟩
  · rw [← hqst, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ (List.mem_append_right _ he)
  · rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    rw [hg, sub_add_cancel]
    exact htail w (SimpleGraph.Walk.mem_tail_support_append_of_mem_support s hqn hw)
  · rw [SimpleGraph.Walk.support_copy, hD] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩
    · exact Or.inl ⟨w, htail w (List.mem_of_mem_dropLast hw), rfl⟩
    · exact Or.inr ⟨δ, hdarts δ hδ, rfl⟩
  · rw [SimpleGraph.Walk.support_copy, hD] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩
    · rw [← List.tail_dropLast] at hw
      have hwT := hQ.mem_of_mem_dropLast w (List.mem_of_mem_tail hw)
      rw [add_zero]
      rw [mem_Icc_two_iff] at hwT ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply, two_nsmul] at hwT ⊢
      omega
    · rw [add_zero]
      exact add_mem_Icc_of_adj δ.adj (hQ.mem_of_mem_dropLast _ (by
        rw [← SimpleGraph.Walk.map_fst_darts]
        exact List.mem_map_of_mem hδ))
  · exact add_mem_boxBoundary_of_adj (SimpleGraph.Walk.adj_penultimate hQn)
      (hQ.penultimate_mem hQn) hQ.end_notMem
  · have hpm : (s.map g).penultimate = g s.penultimate := by
      rw [SimpleGraph.Walk.penultimate, SimpleGraph.Walk.penultimate,
        SimpleGraph.Walk.getVert_map, SimpleGraph.Walk.length_map]
    rw [landingPos_false, hpm, hg, hg, hpen,
      ← perimeterPos_add 1 (2 • (z - (R : LatticeSite 2)))]
    congr 1
    abel

/-- **Colour inversion of a dual arm.** A dual arm of `ω` from `B_r(z)` to the boundary of
`B_{R+1}(z)`, started at its last face in `Icc (z - r - 1) (z + r + 1)` and stopped at its first
face outside `Icc (z - R + 1) (z + R - 1)`, is an open arm of `dualConfig ω` from `B_{r+1}(z)` to
the boundary of `B_R(z)`. Its landing position is the position, on the boundary of
`Icc (2 (z - R) + 1) (2 (z + R) + 1)`, of the end of a walk through the doubled dual arm from its
start. -/
theorem IsDualArm.exists_isOpenArm_dualConfig
    (h : IsDualArm ω z r (z - ((R + 1 : ℕ) : LatticeSite 2)) (z + ((R + 1 : ℕ) : LatticeSite 2)) γ)
    (hrR : r + 1 < R) :
    ∃ (x y : LatticeSite 2) (γ' : (zdGraph 2).Walk x y),
      IsOpenArm (dualConfig ω) z (r + 1) (z - R) (z + R) γ' ∧
      (∀ v ∈ γ'.support, v ∈ γ.support) ∧
      ∃ (e : LatticeSite 2) (P : (zdGraph 2).Walk (2 • a + 1) e),
        (∀ x ∈ P.support, (∃ w ∈ γ.support.dropLast, x = 2 • w + 1) ∨
          ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + 1) ∧
        (∀ x ∈ P.support,
          x ∈ Icc (2 • (z - (R : LatticeSite 2)) + 1) (2 • (z + (R : LatticeSite 2)) + 1)) ∧
        e ∈ boxBoundary (2 • (z - (R : LatticeSite 2)) + 1) (2 • (z + (R : LatticeSite 2)) + 1) ∧
        landingPos (z - R) (z + R) true γ' =
          perimeterPos (2 • (z - (R : LatticeSite 2)) + 1)
            (2 • (z + (R : LatticeSite 2)) + 1) e := by
  have hS' : Icc (z - (r : LatticeSite 2) - 1) (z + r) ⊆
      Icc (z - ((r + 1 : ℕ) : LatticeSite 2)) (z + ((r + 1 : ℕ) : LatticeSite 2)) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.natCast_apply]
      omega
  have hT' : Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) ⊆
      Icc (z - ((R + 1 : ℕ) : LatticeSite 2)) (z + ((R + 1 : ℕ) : LatticeSite 2) - 1) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  obtain ⟨x, y, q, s, t, hqst, hQ, hs⟩ := h.isCrossing.exists_append_append_eq hS' hT'
  have hQn : ¬(q.append s).Nil := hQ.not_nil (Icc_subset_Icc (fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega)
  have hsupp : ∀ w ∈ (q.append s).support, w ∈ γ.support := fun w hw => by
    rw [← hqst, SimpleGraph.Walk.support_append]
    exact List.mem_append_left _ hw
  have hdarts : ∀ δ ∈ (q.append s).darts, δ ∈ γ.darts := fun δ hδ => by
    rw [← hqst, SimpleGraph.Walk.darts_append]
    exact List.mem_append_left _ hδ
  have hbox : ∀ w ∈ (q.append s).support, w ∈ Icc (z - (R : LatticeSite 2)) (z + R) :=
    fun w hw => mem_Icc_of_isCrossing hQ hQn hw
  obtain ⟨D, hD⟩ := exists_walk_double 1 (q.append s)
  refine ⟨x, y, s, ⟨hs, fun e he => h.mem_of_mem_edges e ?_⟩, fun v hv => hsupp v ?_, 2 • y + 1,
    D, fun v hv => ?_, fun v hv => ?_, ?_, ?_⟩
  · rw [← hqst, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ (List.mem_append_right _ he)
  · rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
    exact List.mem_append_right _ hv
  · rw [hD] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩
    · refine Or.inl ⟨w, SimpleGraph.Walk.mem_dropLast_support_of_mem_of_ne (hsupp w hw) ?_, rfl⟩
      rintro rfl
      have hwb := hbox _ hw
      have hb := h.isCrossing.end_notMem
      rw [mem_Icc_two_iff] at hwb hb
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hwb hb
      omega
    · exact Or.inr ⟨δ, hdarts δ hδ, rfl⟩
  · rw [hD] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨δ, hδ, rfl⟩
    · exact two_nsmul_add_one_mem_Icc (hbox w hw)
    · have hfst := hQ.mem_of_mem_dropLast _ (by
        rw [← SimpleGraph.Walk.map_fst_darts]
        exact List.mem_map_of_mem hδ)
      have hadj := (zdGraph_two_adj_iff _ _).1 δ.adj
      rw [mem_Icc_two_iff] at hfst ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
        two_nsmul] at hfst ⊢
      omega
  · refine two_nsmul_add_one_mem_boxBoundary ?_
    rw [boxBoundary_eq_Icc_diff_Icc]
    exact ⟨hbox y (q.append s).end_mem_support, hQ.end_notMem⟩
  · rw [landingPos_true, perimeterPos_add, perimeterPos_two_smul]

/-- **Colour inversion of an arm** of either colour (`IsOpenArm.exists_isDualArm_dualConfig`,
`IsDualArm.exists_isOpenArm_dualConfig`): an arm of `ω` of colour `c` from `B_r(z)` to the boundary
of `B_{R+1}(z)` contains an arm of `dualConfig ω` of colour `!c` from `B_{r+1}(z)` to the boundary
of `B_R(z)` (translated by `(-1, -1)` when `c = true`), and a walk through the doubled arm from its
start to the point whose position on the boundary of `Icc (2 (z - R) + 1) (2 (z + R) + 1)` is the
landing position of the new arm. -/
theorem IsArm.exists_dualConfig {c : Bool}
    (h : IsArm ω c z r (z - ((R + 1 : ℕ) : LatticeSite 2)) (z + ((R + 1 : ℕ) : LatticeSite 2)) γ)
    (hrR : r + 1 < R) :
    ∃ (x y : LatticeSite 2) (γ' : (zdGraph 2).Walk x y),
      IsArm (dualConfig ω) (!c) z (r + 1) (z - R) (z + R) γ' ∧
      (∀ v ∈ γ'.support, cond c (v + 1 ∈ γ.support.tail) (v ∈ γ.support)) ∧
      ∃ (e : LatticeSite 2) (P : (zdGraph 2).Walk (cond c (a + γ.snd) (2 • a + 1)) e),
        (∀ x ∈ P.support, (∃ w ∈ cond c γ.support.tail γ.support.dropLast,
          x = 2 • w + cond c 0 1) ∨ ∃ δ ∈ γ.darts, x = δ.fst + δ.snd + cond c 0 1) ∧
        (∀ x ∈ P.support,
          x ∈ Icc (2 • (z - (R : LatticeSite 2)) + 1) (2 • (z + (R : LatticeSite 2)) + 1)) ∧
        e ∈ boxBoundary (2 • (z - (R : LatticeSite 2)) + 1) (2 • (z + (R : LatticeSite 2)) + 1) ∧
        landingPos (z - R) (z + R) (!c) γ' =
          perimeterPos (2 • (z - (R : LatticeSite 2)) + 1)
            (2 • (z + (R : LatticeSite 2)) + 1) e := by
  cases c
  · exact IsDualArm.exists_isOpenArm_dualConfig h hrR
  · exact IsOpenArm.exists_isDualArm_dualConfig h hrR

end Inversion

/-! ### Colour inversion of multi-arm events -/

/-- **Colour inversion of the multi-arm event.** For `r + 2 < R`, if `ω` has `j` disjoint arms of
colours `σ` in counterclockwise order from `B_r(z)` to the boundary of `B_R(z)`, then the dual
configuration has `j` disjoint arms of the inverted colours `not ∘ σ` in counterclockwise order
from `B_{r+1}(z)` to the boundary of `B_{R - 1}(z)`. This holds for every configuration. -/
theorem dualConfig_mem_multiArmEvent {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ}
    (h : r + 2 < R) {ω : Config (LatticeSite 2)} (hω : ω ∈ multiArmEvent σ z r R) :
    dualConfig ω ∈ multiArmEvent (not ∘ σ) z (r + 1) (R - 1) := by
  obtain ⟨R, rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hrR : r + 1 < R := by omega
  obtain ⟨a, b, γ, hγ, hd, -, ho⟩ := hω
  choose x y γ' hγ' hsupp e P hP hPO he hland using fun i => (hγ i).exists_dualConfig hrR
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆
      Icc (z - ((R + 1 : ℕ) : LatticeSite 2) + 1) (z + ((R + 1 : ℕ) : LatticeSite 2) - 1) :=
    Icc_subset_Icc (fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega) fun i => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega
  have hlo : 2 • (z - (R : LatticeSite 2)) + 1 + 1 ≤ 2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2) := by
    refine Pi.le_def.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply, two_nsmul]
      omega
  have hhi : 2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2) + 1 ≤ 2 • (z + (R : LatticeSite 2)) + 1 := by
    refine Pi.le_def.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    · simp only [Pi.add_apply, Pi.natCast_apply, Pi.one_apply, two_nsmul]
      omega
  refine ⟨x, y, γ', hγ', ⟨fun i k hik hi hk v hv hv' => ?_, fun i k hik hi hk v hv hv' => ?_⟩,
    fun i => ⟨mem_univ _, mem_univ _⟩, fun i k l hik hkl => ?_⟩
  · -- two new open arms come from two old dual arms
    have hi' : σ i = false := by simpa using hi
    have hk' : σ k = false := by simpa using hk
    have h₁ := hsupp i v (List.mem_of_mem_tail hv)
    have h₂ := hsupp k v hv'
    rw [hi', Bool.cond_false] at h₁
    rw [hk', Bool.cond_false] at h₂
    exact hd.2 i k hik hi' hk' v h₁ h₂
  · -- two new dual arms come from two old open arms
    have hi' : σ i = true := by simpa using hi
    have hk' : σ k = true := by simpa using hk
    have h₁ := hsupp i v hv
    have h₂ := hsupp k v hv'
    rw [hi', Bool.cond_true] at h₁
    rw [hk', Bool.cond_true] at h₂
    exact hd.1 i k hik hi' hk' (v + 1) h₁ (List.mem_of_mem_tail h₂)
  · simp only [Function.comp_apply]
    rw [hland i, hland k, hland l]
    exact (sbtw_innerPos_iff_sbtw_perimeterPos hB hγ hd hlo hhi P hP hPO he i k l).1
      ((sbtw_innerPos_iff_sbtw_landingPos hB hγ hd i k l).2 (ho i k l hik hkl))

/-- **Colour inversion at one half.** When every edge of `ℤ²` is open with probability `1/2`, the
probability of `j` disjoint arms of colours `σ` in counterclockwise order from `B_r(z)` to the
boundary of `B_R(z)` is at most that of `j` such arms of the inverted colours `not ∘ σ` from
`B_{r+1}(z)` to the boundary of `B_{R - 1}(z)`, for `r + 2 < R`:
`π_σ(r, R) ≤ π_{not ∘ σ}(r + 1, R - 1)`.
The dual configuration has the law of the configuration on the events that read only edges of
`ℤ²` (self-duality), and it lies in the inverted event whenever the configuration lies in the
event (`dualConfig_mem_multiArmEvent`). -/
theorem law_multiArmEvent_comp_not_le {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {j : ℕ} (σ : Fin j → Bool)
    (z : LatticeSite 2) {r R : ℕ} (h : r + 2 < R) :
    law q (multiArmEvent σ z r R) ≤ law q (multiArmEvent (not ∘ σ) z (r + 1) (R - 1)) := by
  calc law q (multiArmEvent σ z r R)
      ≤ law q (dualConfig ⁻¹' multiArmEvent (not ∘ σ) z (r + 1) (R - 1)) :=
        MeasureTheory.measure_mono fun ω hω => dualConfig_mem_multiArmEvent h hω
    _ = law q (multiArmEvent (not ∘ σ) z (r + 1) (R - 1)) :=
        law_preimage_dualConfig_eq hq (measurableSet_multiArmEvent _ _ _ _)
          fun ω => mem_multiArmEventTo_iff_of_agree fun e he _ _ =>
            ⟨fun h' => h'.1, fun h' => ⟨h', he⟩⟩

end PercLib.Models.Planar
