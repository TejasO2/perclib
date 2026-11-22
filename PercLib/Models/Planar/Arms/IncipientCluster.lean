/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: D. Basu and A. Sapozhnikov, Kesten's incipient infinite cluster and
quasi-multiplicativity of crossing probabilities, Electron. Commun. Probab. 22 (2017),
arXiv:1603.06884v2, Section 2 (the decomposition (2.3), the estimates (2.2)-(2.7), and the
Cauchy property (2.1), (2.8)).
-/
module

public import PercLib.Models.Planar.Arms.ConnectionComparison
public import PercLib.Models.Planar.Arms.OneArm
public import PercLib.Probability.CylinderLimit
public import PercLib.Probability.RatioContraction

/-!
# Kesten's incipient infinite cluster on `ℤ²`: the Basu–Sapozhnikov decomposition

Work in progress; see the module docstring of the final version.

## Main results

* `PercLib.Models.Planar.mem_localConn_of_cut`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

/-! ### Walks: the step into a set -/

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- **The step into a set.** A walk from a vertex outside `P` to a vertex in `P` has an initial
segment that avoids `P` and ends at a neighbour `u` of a vertex `c ∈ P` of the walk. -/
theorem exists_adj_walk_forall_not (P : V → Prop) :
    ∀ {a b : V} (p : G.Walk a b), ¬ P a → P b →
      ∃ u c, P c ∧ G.Adj u c ∧ c ∈ p.support ∧ ∃ q : G.Walk a u,
        (∀ v ∈ q.support, ¬ P v) ∧ ∀ v ∈ q.support, v ∈ p.support
  | _, _, .nil, ha, hb => absurd hb ha
  | a, _, .cons (v := a') h p, ha, hb => by
    by_cases ha' : P a'
    · refine ⟨a, a', ha', h, by simp, .nil, fun v hv => ?_, fun v hv => ?_⟩
      · rw [support_nil, List.mem_singleton] at hv
        rw [hv]
        exact ha
      · rw [support_nil, List.mem_singleton] at hv
        rw [hv]
        simp
    · obtain ⟨u, c, hc, huc, hcp, q, hq, hqp⟩ := exists_adj_walk_forall_not P p ha' hb
      refine ⟨u, c, hc, huc, ?_, .cons h q, fun v hv => ?_, fun v hv => ?_⟩
      · rw [support_cons]
        exact List.mem_cons_of_mem _ hcp
      · rw [support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ha
        · exact hq v hv
      · rw [support_cons, List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (hqp v hv)

end SimpleGraph.Walk

/-! ### Connections from a set closed under open pairs -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- An open pair inside `S` is a connection inside `S`. -/
theorem mem_localConn_of_mem {S : Set V} {η : Config V} {v u : V} (hv : v ∈ S) (hu : u ∈ S)
    (h : s(v, u) ∈ η) : η ∈ localConn S v u := by
  by_cases hvu : v = u
  · subst hvu
    rw [localConn_self hv]
    exact mem_univ η
  · refine mem_localConn_iff_exists_walk.2
      ⟨SimpleGraph.Walk.cons ((openGraph_adj_iff η v u).2 ⟨h, hvu⟩) .nil, fun w hw => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hv
    · exact hu

/-- A connection inside `S` survives in every configuration that keeps the open pairs inside
`S`. -/
theorem localConn_mono_of_forall_mem {S : Set V} {η η' : Config V}
    (hag : ∀ a ∈ S, ∀ b ∈ S, s(a, b) ∈ η → s(a, b) ∈ η') {x y : V}
    (h : η ∈ localConn S x y) : η' ∈ localConn S x y := by
  obtain ⟨hx, hy, hr⟩ := h
  refine ⟨hx, hy, hr.mono fun a b hab => ?_⟩
  simp only [SimpleGraph.induce, SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
    openGraph_adj_iff] at hab ⊢
  exact ⟨hag a a.2 b b.2 hab.1, hab.2⟩

/-- **Connections from a closed set stay in it.** If no open pair joins a vertex of `W` to a
vertex of `S` outside `W`, every connection inside `S` from a vertex of `W` runs inside
`S ∩ W`. -/
theorem mem_localConn_inter_of_closed {S W : Set V} {η : Config V}
    (hW : ∀ v ∈ W, ∀ u ∈ S, s(v, u) ∈ η → u ∈ W) {x y : V} (hx : x ∈ W)
    (h : η ∈ localConn S x y) : η ∈ localConn (S ∩ W) x y := by
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 h
  have key : ∀ {a b : V} (p : (openGraph η).Walk a b), a ∈ W → (∀ v ∈ p.support, v ∈ S) →
      ∀ v ∈ p.support, v ∈ W := by
    intro a b p
    induction p with
    | nil =>
      intro ha _ v hv
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      rw [hv]
      exact ha
    | @cons a a' b h p ih =>
      intro ha hS v hv
      have ha'S : a' ∈ S := hS a' (by simp)
      have ha'W : a' ∈ W := hW a ha a' ha'S ((openGraph_adj_iff η a a').1 h).1
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ha
      · exact ih ha'W (fun w hw => hS w (by simp [hw])) v hv
  exact mem_localConn_iff_exists_walk.2 ⟨p, fun v hv => ⟨hp v hv, key p hx hp v hv⟩⟩

/-- **Connections from a closed set are determined by the pairs that meet it.** If no open pair
of `η` joins `W` to `S \ W`, and `η`, `η'` agree on every pair meeting `W`, then connections
inside `S` from a vertex of `W` are the same for `η` and `η'`. -/
theorem localConn_iff_of_closed {S W : Set V} {η η' : Config V}
    (hcl : ∀ v ∈ W, ∀ u ∈ S, s(v, u) ∈ η → u ∈ W)
    (hag : ∀ v ∈ W, ∀ u, (s(v, u) ∈ η ↔ s(v, u) ∈ η')) {x y : V} (hx : x ∈ W) :
    η ∈ localConn S x y ↔ η' ∈ localConn S x y := by
  have hcl' : ∀ v ∈ W, ∀ u ∈ S, s(v, u) ∈ η' → u ∈ W :=
    fun v hv u hu h => hcl v hv u hu ((hag v hv u).2 h)
  constructor
  · intro h
    exact localConn_mono_set inter_subset_left _ _ (localConn_mono_of_forall_mem
      (fun a ha b _ hab => (hag a ha.2 b).1 hab) (mem_localConn_inter_of_closed hcl hx h))
  · intro h
    exact localConn_mono_set inter_subset_left _ _ (localConn_mono_of_forall_mem
      (fun a ha b _ hab => (hag a ha.2 b).2 hab) (mem_localConn_inter_of_closed hcl' hx h))

/-- The vertices joined inside `A` to a set `T` are closed under the open pairs inside `A`. -/
theorem exists_mem_localConn_of_mem {A T : Set V} {η : Config V} {v u : V}
    (hv : ∃ w ∈ T, η ∈ localConn A v w) (hu : u ∈ A) (h : s(v, u) ∈ η) :
    ∃ w ∈ T, η ∈ localConn A u w := by
  obtain ⟨w, hw, hvw⟩ := hv
  have hvA := hvw.fst
  rw [Sym2.eq_swap] at h
  exact ⟨w, hw, localConn_trans (mem_localConn_of_mem hu hvA h) hvw⟩

/-- **The cluster of a set inside `A` is determined by the pairs that meet it.** The set
`W(η) = {v | v ↔ T inside A}` (`T ⊆ A`) is the same for every `η'` that agrees with `η` on the
pairs meeting `W(η)`. -/
theorem setOf_exists_mem_localConn_eq_of_agree {A T : Set V} (hTA : T ⊆ A) {η η' : Config V}
    (hag : ∀ v ∈ {v | ∃ w ∈ T, η ∈ localConn A v w}, ∀ u, (s(v, u) ∈ η ↔ s(v, u) ∈ η')) :
    {v | ∃ w ∈ T, η' ∈ localConn A v w} = {v | ∃ w ∈ T, η ∈ localConn A v w} := by
  have hcl : ∀ v ∈ {v | ∃ w ∈ T, η ∈ localConn A v w}, ∀ u ∈ A, s(v, u) ∈ η →
      u ∈ {v | ∃ w ∈ T, η ∈ localConn A v w} :=
    fun v hv u hu h => exists_mem_localConn_of_mem hv hu h
  have hTW : ∀ w ∈ T, w ∈ {v | ∃ w ∈ T, η ∈ localConn A v w} := fun w hw =>
    ⟨w, hw, by rw [localConn_self (hTA hw)]; exact mem_univ η⟩
  ext v
  constructor
  · rintro ⟨w, hw, h⟩
    rw [localConn_comm] at h
    refine ⟨w, hw, ?_⟩
    rw [localConn_comm]
    exact (localConn_iff_of_closed hcl hag (hTW w hw)).2 h
  · rintro ⟨w, hw, h⟩
    rw [localConn_comm] at h
    refine ⟨w, hw, ?_⟩
    rw [localConn_comm]
    exact (localConn_iff_of_closed hcl hag (hTW w hw)).1 h

/-- Agreement of two configurations on a set of pairs passes to its subsets. -/
theorem inter_eq_inter_of_inter_eq_of_subset {ω ω' Q Q' : Set (Sym2 V)} (h : ω ∩ Q = ω' ∩ Q)
    (hQ : Q' ⊆ Q) : ω ∩ Q' = ω' ∩ Q' := by
  rw [← inter_eq_right.2 hQ, ← inter_assoc, ← inter_assoc, h]

end PercLib.Percolation.Bond

/-! ### Two real-number lemmas -/

namespace PercLib.Probability

/-- **A rank-one sandwich gives the cross-ratio bound.** If `c f(a) g(b) ≤ M(a, b) ≤ f(a) g(b)`
with `c > 0` and `f, g ≥ 0`, then `M(a, b) M(a', b') ≤ c⁻² M(a, b') M(a', b)`. -/
theorem mul_le_inv_sq_mul_of_le_mul {α β : Type*} {M : α → β → ℝ} {f : α → ℝ} {g : β → ℝ}
    {c : ℝ} (hc : 0 < c) (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b)
    (hlo : ∀ a b, c * (f a * g b) ≤ M a b) (hhi : ∀ a b, M a b ≤ f a * g b) (a a' : α)
    (b b' : β) : M a b * M a' b' ≤ c⁻¹ ^ 2 * (M a b' * M a' b) := by
  have h0 : ∀ a b, 0 ≤ M a b := fun a b =>
    (mul_nonneg hc.le (mul_nonneg (hf a) (hg b))).trans (hlo a b)
  have hc0 : c ≠ 0 := hc.ne'
  calc M a b * M a' b' ≤ (f a * g b) * (f a' * g b') :=
        mul_le_mul (hhi a b) (hhi a' b') (h0 _ _) (mul_nonneg (hf a) (hg b))
    _ = c⁻¹ ^ 2 * ((c * (f a * g b')) * (c * (f a' * g b))) := by
        field_simp
    _ ≤ c⁻¹ ^ 2 * (M a b' * M a' b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hlo a b') (hlo a' b)
          (mul_nonneg hc.le (mul_nonneg (hf a') (hg b))) (h0 _ _)) (sq_nonneg _)

/-- **Approximate numerators and denominators.** If `0 ≤ A ≤ B`, `B > 0`, `0 ≤ δ ≤ 1/2`,
`(1 - δ) A ≤ P ≤ A` and `(1 - δ) B ≤ Q ≤ B`, then `|A / B - P / Q| ≤ 2δ`. -/
theorem abs_div_sub_div_le_two_mul {A B P Q δ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 0 < B)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hP : (1 - δ) * A ≤ P) (hPA : P ≤ A)
    (hQ : (1 - δ) * B ≤ Q) (hQB : Q ≤ B) : |A / B - P / Q| ≤ 2 * δ := by
  have h1δ : 0 < 1 - δ := by linarith
  have hQpos : 0 < Q := lt_of_lt_of_le (mul_pos h1δ hB) hQ
  have hP0 : 0 ≤ P := le_trans (mul_nonneg h1δ.le hA) hP
  have hr1 : A / B ≤ 1 := (div_le_one hB).2 hAB
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
  constructor
  · have h₁ : P / B ≤ P / Q := div_le_div_of_nonneg_left hP0 hQpos hQB
    have h₂ : (1 - δ) * A / B ≤ P / B := div_le_div_of_nonneg_right hP hB.le
    have h₃ : δ * (A / B) ≤ δ := mul_le_of_le_one_right hδ hr1
    have h₄ : A / B = (1 - δ) * A / B + δ * (A / B) := by
      rw [mul_div_assoc]
      ring
    linarith
  · have h₁ : P / Q ≤ A / Q := div_le_div_of_nonneg_right hPA hQpos.le
    have h₂ : A / Q ≤ A / ((1 - δ) * B) := div_le_div_of_nonneg_left hA (mul_pos h1δ hB) hQ
    have h₃ : A / ((1 - δ) * B) ≤ 2 * δ + A / B := by
      rw [div_le_iff₀ (mul_pos h1δ hB)]
      have hAB' : A / B * B = A := div_mul_cancel₀ A hB.ne'
      have hk : 2 * δ * B ≤ B := by nlinarith
      nlinarith [mul_nonneg hδ (by linarith : 0 ≤ 2 * B - 2 * δ * B - A)]
    linarith

end PercLib.Probability

namespace PercLib.Models.Planar

/-! ### The cut of an annulus

A cut has radii `a < c < b` and centre `z`. Its cluster `W` is the set of vertices joined to the
middle sphere `∂B_c(z)` inside the annulus `B_b(z) \ B_{a-1}(z)`; its inner port `Y` is the set of
vertices of `B_{a-1}(z)` with an open edge to `W`, its outer port `R` the set of vertices outside
`B_b(z)` with an open edge to `W`. In the lemmas below `W`, `Y`, `R` are functions of the
configuration given by these descriptions (`hW`, `hY`, `hR`). -/

/-- A vertex of a box with a neighbour outside it lies on the boundary of the box. -/
theorem mem_boxBoundary_of_adj_of_notMem {ω : Config (LatticeSite 2)} {z u v : LatticeSite 2}
    {r : ℕ} (h : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj u v)
    (hu : u ∈ Icc (z - (r : LatticeSite 2)) (z + r))
    (hv : v ∉ Icc (z - (r : LatticeSite 2)) (z + r)) :
    u ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r) := by
  have h0 := coord_le_add_one_of_adj h 0
  have h0' := coord_le_add_one_of_adj h.symm 0
  have h1 := coord_le_add_one_of_adj h 1
  have h1' := coord_le_add_one_of_adj h.symm 1
  rw [mem_Icc_two_iff] at hu hv
  rw [mem_boxBoundary_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hu hv ⊢
  omega

/-- The middle sphere of a cut lies in its annulus. -/
theorem boxBoundary_subset_annulus {z : LatticeSite 2} {a c b : ℕ} (hac : a ≤ c) (hcb : c ≤ b) :
    boxBoundary (z - (c : LatticeSite 2)) (z + c) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
  intro v hv
  rw [mem_boxBoundary_two_iff] at hv
  rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
  omega

/-- **The path up to a cut.** An open path inside `D` from a point of `B_{a-1}(z)` to a point
outside `B_c(z)` has an initial segment inside `B_c(z) ∩ D`, avoiding the cluster `W` of the cut,
that ends at a point of the inner port `Y`. -/
theorem exists_mem_localConn_cut_inner {ω : Config (LatticeSite 2)} {z : LatticeSite 2}
    {a c b : ℕ} (hac : a < c) (hcb : c < b) {W Y : Config (LatticeSite 2) → Set (LatticeSite 2)}
    (hW : ∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hY : ∀ ω y, y ∈ Y ω ↔ y ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∧
      ∃ v ∈ W ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet)
    {D : Set (LatticeSite 2)} {p w : LatticeSite 2}
    (hp : p ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1))
    (hw : w ∉ Icc (z - (c : LatticeSite 2)) (z + c))
    (h : ω ∩ (zdGraph 2).edgeSet ∈ localConn D p w) :
    ∃ y ∈ Y ω, ω ∩ (zdGraph 2).edgeSet ∈
      localConn ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ W ω) p y := by
  obtain ⟨π, hπ⟩ := mem_localConn_iff_exists_walk.1 h
  have hWA : ∀ v ∈ W ω, v ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := fun v hv => by
    obtain ⟨_, _, hvA, -, -⟩ := (hW ω v).1 hv
    exact hvA
  have hSp : ∀ v ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c), v ∈ W ω := fun v hv =>
    (hW ω v).2 ⟨v, hv, by
      rw [localConn_self (boxBoundary_subset_annulus hac.le hcb.le hv)]
      exact mem_univ _⟩
  have hpc : p ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
    rw [mem_Icc_two_iff] at hp ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hp ⊢
    omega
  have hpW : p ∉ W ω := fun hpW => (hWA p hpW).2 hp
  obtain ⟨u, c₁, hc₁, huc, -, γ, hγ, hγπ⟩ :=
    π.exists_adj_walk_forall_not
      (fun v => v ∈ W ω ∨ v ∉ Icc (z - (c : LatticeSite 2)) (z + c))
      (by simp only [not_or, not_not]; exact ⟨hpW, hpc⟩) (Or.inr hw)
  have hu : u ∉ W ω ∧ u ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
    simpa only [not_or, not_not] using hγ u γ.end_mem_support
  have huc' := ((openGraph_adj_iff _ u c₁).1 huc).1
  have hc₁W : c₁ ∈ W ω := by
    rcases hc₁ with hc₁ | hc₁
    · exact hc₁
    · exact absurd (hSp u (mem_boxBoundary_of_adj_of_notMem huc hu.2 hc₁)) hu.1
  have hua : u ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    by_contra hua
    have hub : u ∈ Icc (z - (b : LatticeSite 2)) (z + b) := by
      have := hu.2
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
      omega
    rw [Sym2.eq_swap] at huc'
    exact hu.1 ((hW ω u).2 (exists_mem_localConn_of_mem ((hW ω c₁).1 hc₁W) ⟨hub, hua⟩ huc'))
  rw [Sym2.eq_swap] at huc'
  refine ⟨u, (hY ω u).2 ⟨hua, c₁, hc₁W, huc'⟩, ?_⟩
  refine mem_localConn_iff_exists_walk.2 ⟨γ, fun v hv => ?_⟩
  have hv' : v ∉ W ω ∧ v ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
    simpa only [not_or, not_not] using hγ v hv
  exact ⟨⟨hv'.2, hπ v (hγπ v hv)⟩, hv'.1⟩

/-- **The path after a cut.** An open path inside `D` from a point of `B_c(z)` to a point outside
`B_b(z)` has a final segment inside `D`, avoiding the cluster `W` of the cut and `B_c(z)`, that
starts at a point of the outer port `R`. -/
theorem exists_mem_localConn_cut_outer {ω : Config (LatticeSite 2)} {z : LatticeSite 2}
    {a c b : ℕ} (hac : a < c) (hcb : c < b) {W R : Config (LatticeSite 2) → Set (LatticeSite 2)}
    (hW : ∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hR : ∀ ω r, r ∈ R ω ↔ r ∉ Icc (z - (b : LatticeSite 2)) (z + b) ∧
      ∃ v ∈ W ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet)
    {D : Set (LatticeSite 2)} {p w : LatticeSite 2}
    (hp : p ∈ Icc (z - (c : LatticeSite 2)) (z + c))
    (hw : w ∉ Icc (z - (b : LatticeSite 2)) (z + b))
    (h : ω ∩ (zdGraph 2).edgeSet ∈ localConn D p w) :
    ∃ r ∈ R ω, ω ∩ (zdGraph 2).edgeSet ∈
      localConn (D \ (W ω ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w := by
  obtain ⟨π, hπ⟩ := mem_localConn_iff_exists_walk.1 h
  have hWA : ∀ v ∈ W ω, v ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := fun v hv => by
    obtain ⟨_, _, hvA, -, -⟩ := (hW ω v).1 hv
    exact hvA
  have hSp : ∀ v ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c), v ∈ W ω := fun v hv =>
    (hW ω v).2 ⟨v, hv, by
      rw [localConn_self (boxBoundary_subset_annulus hac.le hcb.le hv)]
      exact mem_univ _⟩
  have hwc : w ∉ Icc (z - (c : LatticeSite 2)) (z + c) := by
    rw [mem_Icc_two_iff] at hw ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hw ⊢
    omega
  have hwW : w ∉ W ω := fun h => hw (hWA w h).1
  obtain ⟨u, c₂, hc₂, huc, -, γ, hγ, hγπ⟩ :=
    π.reverse.exists_adj_walk_forall_not
      (fun v => v ∈ W ω ∨ v ∈ Icc (z - (c : LatticeSite 2)) (z + c))
      (by simp only [not_or]; exact ⟨hwW, hwc⟩) (Or.inr hp)
  have hu : u ∉ W ω ∧ u ∉ Icc (z - (c : LatticeSite 2)) (z + c) := by
    simpa only [not_or] using hγ u γ.end_mem_support
  have huc' := ((openGraph_adj_iff _ u c₂).1 huc).1
  have hc₂W : c₂ ∈ W ω := by
    rcases hc₂ with hc₂ | hc₂
    · exact hc₂
    · exact hSp c₂ (mem_boxBoundary_of_adj_of_notMem huc.symm hc₂ hu.2)
  rw [Sym2.eq_swap] at huc'
  have hub : u ∉ Icc (z - (b : LatticeSite 2)) (z + b) := by
    intro hub
    have hua : u ∉ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
      have := hu.2
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
      omega
    exact hu.1 ((hW ω u).2 (exists_mem_localConn_of_mem ((hW ω c₂).1 hc₂W) ⟨hub, hua⟩ huc'))
  refine ⟨u, (hR ω u).2 ⟨hub, c₂, hc₂W, huc'⟩, ?_⟩
  refine mem_localConn_iff_exists_walk.2 ⟨γ.reverse, fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
  have hv' : v ∉ W ω ∧ v ∉ Icc (z - (c : LatticeSite 2)) (z + c) := by
    simpa only [not_or] using hγ v hv
  have hvπ := hγπ v hv
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hvπ
  exact ⟨hπ v hvπ, fun h' => h'.elim hv'.1 hv'.2⟩

/-- **Gluing through a cut.** If the crossings of the two halves of the annulus of a cut are
linked (`hlink`), an open path inside `D` from `p` to a point of the inner port `Y` and an open
path inside `D` from a point of the outer port `R` to `w` give an open path inside `D` from `p` to
`w`, provided `D` contains the annulus. -/
theorem mem_localConn_of_cut {ω : Config (LatticeSite 2)} {z : LatticeSite 2}
    {a c b : ℕ} (hac : a < c) (hcb : c < b)
    {W Y R : Config (LatticeSite 2) → Set (LatticeSite 2)}
    (hW : ∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hY : ∀ ω y, y ∈ Y ω ↔ y ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∧
      ∃ v ∈ W ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet)
    (hR : ∀ ω r, r ∈ R ω ↔ r ∉ Icc (z - (b : LatticeSite 2)) (z + b) ∧
      ∃ v ∈ W ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet)
    (hlink : ∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y)
    {D : Set (LatticeSite 2)}
    (hD : Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ⊆ D)
    {p y r w : LatticeSite 2} (hy : y ∈ Y ω) (hr : r ∈ R ω)
    (hpy : ω ∩ (zdGraph 2).edgeSet ∈ localConn D p y)
    (hrw : ω ∩ (zdGraph 2).edgeSet ∈ localConn D r w) :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn D p w := by
  obtain ⟨hya, v, hvW, hvy⟩ := (hY ω y).1 hy
  obtain ⟨hrb, v', hv'W, hv'r⟩ := (hR ω r).1 hr
  obtain ⟨w₁, hw₁, hvw₁⟩ := (hW ω v).1 hvW
  obtain ⟨w₂, hw₂, hv'w₂⟩ := (hW ω v').1 hv'W
  have hvA := hvw₁.fst
  have hv'A := hv'w₂.fst
  have hyD : y ∈ D := hpy.snd.fst
  have hrD : r ∈ D := hrw.fst
  have hvy_adj : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj v y :=
    (openGraph_adj_iff _ v y).2 ⟨hvy, fun h => hvA.2 (by rw [h]; exact hya)⟩
  have hv'r_adj : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj v' r :=
    (openGraph_adj_iff _ v' r).2 ⟨hv'r, fun h => hrb (by rw [← h]; exact hv'A.1)⟩
  have hvSa : v ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a) := by
    have h0 := coord_le_add_one_of_adj hvy_adj 0
    have h0' := coord_le_add_one_of_adj hvy_adj.symm 0
    have h1 := coord_le_add_one_of_adj hvy_adj 1
    have h1' := coord_le_add_one_of_adj hvy_adj.symm 1
    have hvA' := hvA
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff] at hvA'
    rw [mem_Icc_two_iff] at hya
    rw [mem_boxBoundary_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvA' hya ⊢
    omega
  have hv'Sb : v' ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b) :=
    mem_boxBoundary_of_adj_of_notMem hv'r_adj hv'A.1 hrb
  have hvc : v ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
    have := hvSa
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
    omega
  have hw₁c : w₁ ∉ Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) := by
    have := hw₁
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  have hv'c : v' ∉ Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) := by
    have := hv'Sb
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  have hw₂c : w₂ ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
    have := hw₂
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
    omega
  obtain ⟨m, hm, hvm⟩ := exists_mem_boxBoundary_mem_localConn_inter hvc hw₁c hvw₁
  obtain ⟨m', hm', hv'm'⟩ := exists_mem_boxBoundary_mem_localConn_diff hv'c hw₂c hv'w₂
  have hsub₁ : (Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) ∩ Icc (z - (c : LatticeSite 2)) (z + c) ⊆
      Icc (z - (c : LatticeSite 2)) (z + c) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    intro u hu
    simp only [mem_inter_iff, mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have hsub₂ : (Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) \
      Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) := by
    intro u hu
    simp only [mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have hlk := hlink v hvSa m hm m' hm' v' hv'Sb (localConn_mono_set hsub₁ _ _ hvm)
    (by rw [localConn_comm]; exact localConn_mono_set hsub₂ _ _ hv'm')
  rw [Sym2.eq_swap] at hvy
  have h₁ : ω ∩ (zdGraph 2).edgeSet ∈ localConn D y v := mem_localConn_of_mem hyD (hD hvA) hvy
  have h₂ := localConn_mono_set hD _ _ hlk
  have h₃ : ω ∩ (zdGraph 2).edgeSet ∈ localConn D v' r := mem_localConn_of_mem (hD hv'A) hrD hv'r
  exact localConn_trans hpy (localConn_trans h₁ (localConn_trans h₂ (localConn_trans h₃ hrw)))

/-- **The cut is determined by the pairs meeting its cluster.** If `ω` and `ω'` agree on the open
edges meeting the cluster `W ω` of a cut, they have the same cluster and the same ports. -/
theorem cut_eq_of_agree {z : LatticeSite 2} {a c b : ℕ} (hac : a < c) (hcb : c < b)
    {W Y R : Config (LatticeSite 2) → Set (LatticeSite 2)}
    (hW : ∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hY : ∀ ω y, y ∈ Y ω ↔ y ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∧
      ∃ v ∈ W ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet)
    (hR : ∀ ω r, r ∈ R ω ↔ r ∉ Icc (z - (b : LatticeSite 2)) (z + b) ∧
      ∃ v ∈ W ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet)
    {ω ω' : Config (LatticeSite 2)}
    (hag : ∀ v ∈ W ω, ∀ u, (s(v, u) ∈ ω ∩ (zdGraph 2).edgeSet ↔
      s(v, u) ∈ ω' ∩ (zdGraph 2).edgeSet)) :
    W ω' = W ω ∧ Y ω' = Y ω ∧ R ω' = R ω := by
  have hWW : W ω' = W ω := by
    ext v
    rw [hW ω' v, hW ω v]
    exact Set.ext_iff.1 (setOf_exists_mem_localConn_eq_of_agree
      (boxBoundary_subset_annulus hac.le hcb.le) (fun v hv u => hag v ((hW ω v).2 hv) u)) v
  refine ⟨hWW, ?_, ?_⟩
  · ext y
    rw [hY ω' y, hY ω y, hWW]
    exact and_congr_right fun _ => exists_congr fun v =>
      and_congr_right fun hv => (hag v hv y).symm
  · ext r
    rw [hR ω' r, hR ω r, hWW]
    exact and_congr_right fun _ => exists_congr fun v =>
      and_congr_right fun hv => (hag v hv r).symm

/-- **The link event of a cut is determined by the pairs meeting its cluster.** The event that
every crossing of the inner half `B_c \ B_{a-1}` of the annulus is joined inside the annulus to
every crossing of the outer half `B_b \ B_{c-1}` is the same for `η` and `η'` when they agree on
the pairs meeting the cluster `W₀` of `∂B_c` in the annulus. -/
theorem link_iff_of_agree {z : LatticeSite 2} {a c b : ℕ} (hac : a < c) (hcb : c < b)
    {W₀ : Set (LatticeSite 2)} {η η' : Config (LatticeSite 2)}
    (hW₀ : ∀ v, v ∈ W₀ ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      η ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hag : ∀ v ∈ W₀, ∀ u, (s(v, u) ∈ η ↔ s(v, u) ∈ η')) :
    (∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        η ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        η ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        η ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y) ↔
    (∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        η' ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        η' ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        η' ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y) := by
  have hcl : ∀ v ∈ W₀, ∀ u ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1), s(v, u) ∈ η → u ∈ W₀ :=
    fun v hv u hu h => (hW₀ u).2 (exists_mem_localConn_of_mem ((hW₀ v).1 hv) hu h)
  have hSp : ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c), m ∈ W₀ := fun m hm =>
    (hW₀ m).2 ⟨m, hm, by
      rw [localConn_self (boxBoundary_subset_annulus hac.le hcb.le hm)]
      exact mem_univ _⟩
  have hsac : Icc (z - (c : LatticeSite 2)) (z + c) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    intro u hu
    simp only [mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have hscb : Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    intro u hu
    simp only [mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have key : ∀ S ⊆ Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1), ∀ x ∈ W₀, ∀ y,
      η ∈ localConn S x y ↔ η' ∈ localConn S x y := fun S hS x hx y =>
    localConn_iff_of_closed (fun v hv u hu h => hcl v hv u (hS hu) h) hag hx
  have conv : ∀ x, ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      (η ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m ↔
      η' ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m) := fun x m hm => by
    rw [localConn_comm]
    exact key _ hsac m (hSp m hm) x
  have hmem : ∀ x, ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      η ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m → x ∈ W₀ :=
    fun x m hm h => (hW₀ x).2 ⟨m, hm, localConn_mono_set hsac _ _ h⟩
  constructor
  · intro hL x hx m hm m' hm' y hy h₁ h₂
    have h₁' := (conv x m hm).2 h₁
    have h₂' := (key _ hscb m' (hSp m' hm') y).2 h₂
    exact (key _ subset_rfl x (hmem x m hm h₁') y).1 (hL x hx m hm m' hm' y hy h₁' h₂')
  · intro hL x hx m hm m' hm' y hy h₁ h₂
    have h₁' := (conv x m hm).1 h₁
    have h₂' := (key _ hscb m' (hSp m' hm') y).1 h₂
    exact (key _ subset_rfl x (hmem x m hm h₁) y).2 (hL x hx m hm m' hm' y hy h₁' h₂')

/-- **Independence across a cut.** For a fixed value `x = (W₀, Y₀, R₀)` of the cut, the event `E`
with the connection from `P` to `Y₀` avoiding `W₀`, the cut event `{W = W₀, Y = Y₀, R = R₀}`
with the link event, and the connection from `R₀` outwards avoiding `W₀ ∪ B_c` with the event `H`,
are determined by disjoint sets of pairs; so the probability of their intersection is the
product. The intersection is measurable. -/
theorem measurableSet_inter_and_law_inter_eq_mul_of_cut (q : Sym2 (LatticeSite 2) → unitInterval)
    {z : LatticeSite 2} {a c b n : ℕ} (hac : a < c) (hcb : c < b)
    {W Y R : Config (LatticeSite 2) → Set (LatticeSite 2)}
    (hW : ∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hY : ∀ ω y, y ∈ Y ω ↔ y ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∧
      ∃ v ∈ W ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet)
    (hR : ∀ ω r, r ∈ R ω ↔ r ∉ Icc (z - (b : LatticeSite 2)) (z + b) ∧
      ∃ v ∈ W ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet)
    {G : Set (Config (LatticeSite 2))}
    (hG : ∀ ω, ω ∈ G ↔ ∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y)
    {P D : Set (LatticeSite 2)} {E H : Set (Config (LatticeSite 2))} (hEm : MeasurableSet E)
    (hE : ∀ ω ω', ω ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∩ D} =
      ω' ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∩ D} → (ω ∈ E ↔ ω' ∈ E))
    (hHm : MeasurableSet H)
    (hH : ∀ ω ω', ω ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} =
      ω' ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} → (ω ∈ H ↔ ω' ∈ H))
    (x : Finset (LatticeSite 2) × Finset (LatticeSite 2) × Finset (LatticeSite 2)) :
    MeasurableSet ((E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) ∩
      ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) ∩
      ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H)) ∧
    law q ((E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) ∩
      ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) ∩
      ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H)) =
    law q (E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) *
      law q ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) *
      law q ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) := by
  classical
  by_cases hx : ∃ ω₀, W ω₀ = ↑x.1 ∧ Y ω₀ = ↑x.2.1 ∧ R ω₀ = ↑x.2.2
  swap
  · have h0 : {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun h _ => hx ⟨ω, h⟩
    simp only [h0, inter_empty, empty_inter, MeasurableSet.empty, measure_empty, mul_zero,
      zero_mul, and_self]
  obtain ⟨ω₀, h₀, -, -⟩ := hx
  have hxA : ∀ v ∈ (x.1 : Set (LatticeSite 2)), v ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := fun v hv => by
    rw [← h₀] at hv
    obtain ⟨_, _, hvA, -, -⟩ := (hW ω₀ v).1 hv
    exact hvA
  -- the three sets of pairs
  set Q₁ : Set (Sym2 (LatticeSite 2)) := {e | e ∉ (zdGraph 2).edgeSet ∨
    ∀ v ∈ e, v ∈ (Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1} with hQ₁
  set Q₂ : Set (Sym2 (LatticeSite 2)) := {e | e ∈ (zdGraph 2).edgeSet ∧
    ∃ v ∈ e, v ∈ (x.1 : Set (LatticeSite 2))} with hQ₂
  set Q₃ : Set (Sym2 (LatticeSite 2)) := {e | e ∈ (zdGraph 2).edgeSet ∧
    ∀ v ∈ e, v ∉ (x.1 : Set (LatticeSite 2)) ∧ v ∉ Icc (z - (c : LatticeSite 2)) (z + c)}
    with hQ₃
  have hne : ∀ e : Sym2 (LatticeSite 2), ∃ v, v ∈ e := fun e => by
    induction e using Sym2.ind with
    | h v w => exact ⟨v, Sym2.mem_mk_left v w⟩
  have hd₁ : Disjoint Q₁ (Q₂ ∪ Q₃) := by
    rw [Set.disjoint_union_right]
    constructor
    · refine Set.disjoint_left.2 fun e he₁ he₂ => ?_
      obtain ⟨heL, v, hv, hvx⟩ := he₂
      rcases he₁ with h | h
      · exact h heL
      · exact (h v hv).2 hvx
    · refine Set.disjoint_left.2 fun e he₁ he₂ => ?_
      obtain ⟨heL, h₃⟩ := he₂
      obtain ⟨v, hv⟩ := hne e
      rcases he₁ with h | h
      · exact h heL
      · exact (h₃ v hv).2 (h v hv).1.1
  have hd₂ : Disjoint Q₂ Q₃ := Set.disjoint_left.2 fun e he₂ he₃ => by
    obtain ⟨-, v, hv, hvx⟩ := he₂
    exact (he₃.2 v hv).1 hvx
  -- determination of the first event
  have hdet₁ : ∀ ω ω', ω ∩ Q₁ = ω' ∩ Q₁ →
      (ω ∈ E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y} ↔
      ω' ∈ E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) := by
    intro ω ω' h
    have hE' := hE ω ω' (inter_eq_inter_of_inter_eq_of_subset h fun e he => by
      rcases he with he | he
      · exact Or.inl he
      · refine Or.inr fun v hv => ⟨⟨?_, (he v hv).2⟩, fun hvx => (hxA v hvx).2 (he v hv).1⟩
        have := (he v hv).1
        rw [mem_Icc_two_iff] at this ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
        omega)
    have hC := inter_mem_localConn_iff_of_inter_eq subset_rfl (zdGraph 2).edgeSet
      (inter_eq_inter_of_inter_eq_of_subset h (Q' := {e | ∀ v ∈ e,
        v ∈ (Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1}) fun e he => Or.inr he)
    simp only [mem_inter_iff, mem_ofPred_eq, hE', hC]
  -- determination of the cut event
  have hdet₂' : ∀ ω ω', ω ∩ Q₂ = ω' ∩ Q₂ →
      ω ∈ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G →
      ω' ∈ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G := by
    rintro ω ω' h ⟨⟨h₁, h₂, h₃⟩, hGω⟩
    have hag : ∀ v ∈ W ω, ∀ u, (s(v, u) ∈ ω ∩ (zdGraph 2).edgeSet ↔
        s(v, u) ∈ ω' ∩ (zdGraph 2).edgeSet) := by
      intro v hv u
      have hvx : v ∈ (x.1 : Set (LatticeSite 2)) := by rw [← h₁]; exact hv
      have hex : ∃ w ∈ s(v, u), w ∈ (x.1 : Set (LatticeSite 2)) :=
        ⟨v, Sym2.mem_mk_left v u, hvx⟩
      have e₁ : s(v, u) ∈ ω ∩ (zdGraph 2).edgeSet ↔ s(v, u) ∈ ω ∩ Q₂ :=
        ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂, hex⟩, fun ⟨h₁, h₂, _⟩ => ⟨h₁, h₂⟩⟩
      have e₂ : s(v, u) ∈ ω' ∩ (zdGraph 2).edgeSet ↔ s(v, u) ∈ ω' ∩ Q₂ :=
        ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂, hex⟩, fun ⟨h₁, h₂, _⟩ => ⟨h₁, h₂⟩⟩
      rw [e₁, e₂, h]
    obtain ⟨hWW, hYY, hRR⟩ := cut_eq_of_agree hac hcb hW hY hR hag
    refine ⟨⟨hWW.trans h₁, hYY.trans h₂, hRR.trans h₃⟩, ?_⟩
    rw [hG] at hGω ⊢
    exact (link_iff_of_agree hac hcb (hW ω) hag).1 hGω
  have hdet₂ : ∀ ω ω', ω ∩ Q₂ = ω' ∩ Q₂ →
      (ω ∈ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G ↔
        ω' ∈ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) :=
    fun ω ω' h => ⟨hdet₂' ω ω' h, hdet₂' ω' ω h.symm⟩
  -- determination of the third event
  have hdet₃ : ∀ ω ω', ω ∩ Q₃ = ω' ∩ Q₃ →
      (ω ∈ {ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H ↔
      ω' ∈ {ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) := by
    intro ω ω' h
    have hH' := hH ω ω' (inter_eq_inter_of_inter_eq_of_subset h fun e he => by
      refine ⟨he.1, fun v hv => ⟨fun hvx => (he.2 v hv) (hxA v hvx).1, fun hvc => he.2 v hv ?_⟩⟩
      rw [mem_Icc_two_iff] at hvc ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hvc ⊢
      omega)
    have hC₀ : (ω ∩ (zdGraph 2).edgeSet) ∩ {e | ∀ v ∈ e, v ∈ (Icc (z - (n : LatticeSite 2))
        (z + n) ∩ D) \ (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))} =
        (ω' ∩ (zdGraph 2).edgeSet) ∩ {e | ∀ v ∈ e, v ∈ (Icc (z - (n : LatticeSite 2))
        (z + n) ∩ D) \ (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))} := by
      rw [inter_assoc, inter_assoc]
      refine inter_eq_inter_of_inter_eq_of_subset h fun e he => ⟨he.1, fun v hv => ?_⟩
      have := (he.2 v hv).2
      rw [mem_union, not_or] at this
      exact this
    have hC := inter_mem_localConn_iff_of_inter_eq subset_rfl (zdGraph 2).edgeSet hC₀
    simp only [inter_assoc, inter_self] at hC
    simp only [mem_inter_iff, mem_ofPred_eq, hH', hC]
  -- measurability
  have hm₁ : MeasurableSet (E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn
        ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) :=
    hEm.inter (measurableSet_setOf_exists_inter_mem_localConn _ _ _ _)
  have hm₃ : MeasurableSet ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
      ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
        (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) :=
    (measurableSet_setOf_exists_inter_mem_localConn _ _ _ _).inter hHm
  have hQ₂F : Q₂ ⊆ ↑(Finset.Icc (z - ((b + 1 : ℕ) : LatticeSite 2))
      (z + ((b + 1 : ℕ) : LatticeSite 2))).sym2 := by
    rintro e ⟨heL, w, hwe, hwx⟩
    obtain ⟨w', rfl⟩ := Sym2.mem_iff_exists.1 hwe
    rw [Finset.mem_coe, Finset.mem_sym2_iff]
    have hadj : (zdGraph 2).Adj w w' := heL
    rw [zdGraph_two_adj_iff] at hadj
    have hw := hxA w hwx
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff] at hw
    intro u hu
    rw [← Finset.mem_coe, Finset.coe_Icc, mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw ⊢
    rcases Sym2.mem_iff.1 hu with rfl | rfl <;> omega
  have hm₂ : MeasurableSet ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) :=
    measurableSet_of_determined_finset fun ω => hdet₂ ω _ (by
      rw [inter_assoc, inter_eq_right.2 hQ₂F])
  refine ⟨(hm₁.inter hm₂).inter hm₃, ?_⟩
  rw [inter_assoc]
  have h₁ : law q ((E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) ∩
      (({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) ∩
      ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H))) = _ :=
    prodBernoulli_inter_of_determined q hd₁ hm₁ (hm₂.inter hm₃) hdet₁ fun ω ω' h => by
      have h₂ := hdet₂ ω ω' (inter_eq_inter_of_inter_eq_of_subset h subset_union_left)
      have h₃ := hdet₃ ω ω' (inter_eq_inter_of_inter_eq_of_subset h subset_union_right)
      exact and_congr h₂ h₃
  have h₂ := prodBernoulli_inter_of_determined q hd₂ hm₂ hm₃ hdet₂ hdet₃
  rw [h₁, law, h₂, mul_assoc]

/-- **The Basu–Sapozhnikov decomposition at one cut** ((2.3) on `ℤ²`). For a cut with radii
`a < c < b`, sources `P ⊆ B_{a-1}(z)`, a region `D` containing its annulus, an event `E` of the
pairs inside `B_{a-1}(z) ∩ D` and the pairs off the edges, an event `H` of the edges outside
`B_b(z)`, and `n > b`, the probability that `E` holds, `P` is joined to `∂B_n(z)` inside
`B_n(z) ∩ D`, the cut is linked and `H` holds is the sum, over the values `(W₀, Y₀, R₀)` of the
cut, of the product of three probabilities: `E` with `P ↔ Y₀` inside `(B_c ∩ D) \ W₀`; the cut
event with the link event; `R₀ ↔ ∂B_n` inside `(B_n ∩ D) \ (W₀ ∪ B_c)` with `H`. Any finite set
`T` of values that contains the value of every configuration may be summed over. -/
theorem law_inter_eq_sum_of_cut (q : Sym2 (LatticeSite 2) → unitInterval)
    {z : LatticeSite 2} {a c b n : ℕ} (hac : a < c) (hcb : c < b) (hbn : b < n)
    {W Y R : Config (LatticeSite 2) → Set (LatticeSite 2)}
    (hW : ∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w)
    (hY : ∀ ω y, y ∈ Y ω ↔ y ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∧
      ∃ v ∈ W ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet)
    (hR : ∀ ω r, r ∈ R ω ↔ r ∉ Icc (z - (b : LatticeSite 2)) (z + b) ∧
      ∃ v ∈ W ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet)
    {G : Set (Config (LatticeSite 2))}
    (hG : ∀ ω, ω ∈ G ↔ ∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y)
    {P D : Set (LatticeSite 2)} (hP : P ⊆ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1))
    (hD : Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ⊆ D)
    {E H : Set (Config (LatticeSite 2))} (hEm : MeasurableSet E)
    (hE : ∀ ω ω', ω ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∩ D} =
      ω' ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∩ D} → (ω ∈ E ↔ ω' ∈ E))
    (hHm : MeasurableSet H)
    (hH : ∀ ω ω', ω ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} =
      ω' ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} → (ω ∈ H ↔ ω' ∈ H))
    (T : Finset (Finset (LatticeSite 2) × Finset (LatticeSite 2) × Finset (LatticeSite 2)))
    (hT : ∀ ω, ∃ x ∈ T, W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2) :
    law q (E ∩ {ω | ∃ p ∈ P, ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) p w} ∩
      G ∩ H) =
    ∑ x ∈ T, law q (E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) *
      law q ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) *
      law q ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) := by
  classical
  have hcn : Icc (z - (c : LatticeSite 2)) (z + c) ⊆ Icc (z - (n : LatticeSite 2)) (z + n) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv ⊢
    omega
  have hDn : Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ⊆ Icc (z - (n : LatticeSite 2)) (z + n) ∩ D :=
    fun v hv => ⟨by
      have := hv.1
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
      omega, hD hv⟩
  have hset : ∀ x ∈ T, (E ∩ {ω | ∃ p ∈ P, ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) p w} ∩
      G ∩ H) ∩ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} =
      (E ∩ {ω | ∃ p ∈ P, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) p y}) ∩
      ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) ∩
      ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) := by
    intro x _
    ext ω
    constructor
    · rintro ⟨⟨⟨⟨hEω, p, hp, w, hw, hpw⟩, hGω⟩, hHω⟩, h₁, h₂, h₃⟩
      have hpa := hP hp
      have hwc : w ∉ Icc (z - (c : LatticeSite 2)) (z + c) := by
        rw [mem_boxBoundary_two_iff] at hw
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hw ⊢
        omega
      have hwb : w ∉ Icc (z - (b : LatticeSite 2)) (z + b) := by
        rw [mem_boxBoundary_two_iff] at hw
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hw ⊢
        omega
      have hpc : p ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
        rw [mem_Icc_two_iff] at hpa ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hpa ⊢
        omega
      obtain ⟨y, hy, hpy⟩ := exists_mem_localConn_cut_inner hac hcb hW hY hpa hwc hpw
      obtain ⟨r, hr, hrw⟩ := exists_mem_localConn_cut_outer hac hcb hW hR hpc hwb hpw
      rw [h₂] at hy
      rw [h₃] at hr
      rw [h₁] at hpy hrw
      refine ⟨⟨⟨hEω, p, hp, y, hy, localConn_mono_set ?_ _ _ hpy⟩, ⟨h₁, h₂, h₃⟩, hGω⟩,
        ⟨r, hr, w, hw, hrw⟩, hHω⟩
      exact fun v ⟨⟨hv₁, _, hv₂⟩, hv₃⟩ => ⟨⟨hv₁, hv₂⟩, hv₃⟩
    · rintro ⟨⟨⟨hEω, p, hp, y, hy, hpy⟩, ⟨h₁, h₂, h₃⟩, hGω⟩, ⟨r, hr, w, hw, hrw⟩, hHω⟩
      rw [← h₂] at hy
      rw [← h₃] at hr
      refine ⟨⟨⟨⟨hEω, p, hp, w, hw, ?_⟩, hGω⟩, hHω⟩, h₁, h₂, h₃⟩
      exact mem_localConn_of_cut hac hcb hW hY hR ((hG ω).1 hGω) hDn hy hr
        (localConn_mono_set (fun v (hv : v ∈ (Icc (z - (c : LatticeSite 2)) (z + c) ∩ D) \ ↑x.1) =>
          (⟨hcn hv.1.1, hv.1.2⟩ : v ∈ Icc (z - (n : LatticeSite 2)) (z + n) ∩ D)) _ _ hpy)
        (localConn_mono_set sdiff_subset _ _ hrw)
  have hcover : E ∩ {ω | ∃ p ∈ P, ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) p w} ∩
      G ∩ H = ⋃ x ∈ T, (E ∩ {ω | ∃ p ∈ P, ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) p w} ∩
      G ∩ H) ∩ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} := by
    ext ω
    simp only [mem_iUnion, exists_prop]
    constructor
    · intro h
      obtain ⟨x, hx, hxω⟩ := hT ω
      exact ⟨x, hx, h, hxω⟩
    · rintro ⟨x, -, h, -⟩
      exact h
  have hdisj : (↑T : Set (Finset (LatticeSite 2) × Finset (LatticeSite 2) ×
      Finset (LatticeSite 2))).PairwiseDisjoint fun x =>
      (E ∩ {ω | ∃ p ∈ P, ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) ∩ D) p w} ∩
      G ∩ H) ∩ {ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} := by
    intro x _ x' _ hne
    refine Set.disjoint_left.2 fun ω h h' => hne ?_
    obtain ⟨-, h₁, h₂, h₃⟩ := h
    obtain ⟨-, h₁', h₂', h₃'⟩ := h'
    exact Prod.ext (Finset.coe_injective (h₁.symm.trans h₁'))
      (Prod.ext (Finset.coe_injective (h₂.symm.trans h₂'))
        (Finset.coe_injective (h₃.symm.trans h₃')))
  rw [hcover, measure_biUnion_finset hdisj fun x hx => by
    rw [hset x hx]
    exact (measurableSet_inter_and_law_inter_eq_mul_of_cut q hac hcb hW hY hR hG hEm hE hHm hH
      x).1]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hset x hx]
  exact (measurableSet_inter_and_law_inter_eq_mul_of_cut q hac hcb hW hY hR hG hEm hE hHm hH x).2

end PercLib.Models.Planar
