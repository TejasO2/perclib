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
public import PercLib.Models.Planar.Arms.TwoPoint
public import PercLib.Probability.CylinderLimit
public import PercLib.Probability.RatioContraction

/-!
# Kesten's incipient infinite cluster on `ℤ²`: the Basu–Sapozhnikov decomposition

The first half of the proof of Kesten's incipient infinite cluster on `ℤ²` (wiki FM8D) along
Basu and Sapozhnikov's Section 2: the decomposition of `P(E, z ↔ ∂B_n(z))` along a chain of cuts,
the estimates (2.2)-(2.7), and the uniform Cauchy property (2.1), (2.8) of the conditional
probabilities `P(A | z ↔ ∂B_n(z))`, uniformly over every profile that opens each edge with
probability at least `1/2` (on the edges, `p = 1 - e^{-β}` with `β ≥ log 2`). The limits, the law
`ν` and the uniqueness of the infinite cluster under `ν` are not in this file.

Boxes are `B_r(z) = Icc (z - r) (z + r)`, `B_{r-1}(z)` is `Icc (z - r + 1) (z + r - 1)`, and
`∂B_r(z)` is `boxBoundary (z - r) (z + r)`; only the open edges `ω ∩ (zdGraph 2).edgeSet` are
read; `z ↔ ∂B_n(z)` is `armEvent z n`.

* **Cuts.** A cut has radii `a < c < b`. Its cluster `W` is the set of vertices joined to the
  middle sphere `∂B_c` inside the annulus `B_b \ B_{a-1}`; its inner port `Y` is the set of points
  of `B_{a-1}` with an open edge to `W`, its outer port `R` the set of points outside `B_b` with an
  open edge to `W`. The cut is *linked* when every crossing of `B_c \ B_{a-1}` is joined inside the
  annulus to every crossing of `B_b \ B_{c-1}`. The cut event `{W = W₀, Y = Y₀, R = R₀}` with the
  link event is determined by the pairs meeting `W₀` (`cut_eq_of_agree`, `link_iff_of_agree`),
  through a general fact: connections from a set closed under open pairs are determined by the
  pairs meeting it (`localConn_iff_of_closed`, `setOf_exists_mem_localConn_eq_of_agree`). In the
  lemmas `W`, `Y`, `R` are functions of the configuration given by these descriptions.
* **One cut** (Basu–Sapozhnikov (2.3)). An open path from inside to outside a cut splits at its
  first visit to `W` (it arrives from `Y`) and its last visit to `W ∪ B_c` (it leaves to `R`)
  (`exists_mem_localConn_cut_inner`, `exists_mem_localConn_cut_outer`); conversely, on the link
  event, paths into `Y` and out of `R` are glued through `W` (`mem_localConn_of_cut`). The three
  pieces are determined by disjoint sets of pairs, so `law_inter_eq_sum_of_cut` writes the
  probability as a sum, over the values of the cut, of products of three probabilities.
* **The chain** (Basu–Sapozhnikov (2.5), (2.6)). Iterating over cuts with radii
  `4 (b_k + 1) + 2 ≤ a_{k+1}` gives `P(E, z ↔ ∂B_n, all cuts linked) = ⟨u', M_0 ⋯ M_{S - 1} w_S⟩`,
  with matrices `M_k` and weights `u' ≤ u''` that do not depend on `n`
  (`law_inter_eq_sum_of_cut_of_prev`, `law_inter_armEvent_eq_sum_of_cut`, `exists_chain_of_cuts`).
* **(2.7).** The middle factor `P(R ↔ Y inside (B_{c'} \ U) \ X)` lies between `c f g` and `f g`,
  with `f` depending only on the inner cut and `g` only on the outer one
  (`exists_law_localConn_comparable_of_cut`, from (A2) of `ConnectionComparison.lean`); hence the
  cross-ratio bound `M x y · M x' y' ≤ κ² M x y' · M x' y` (`exists_crossRatio_of_cuts`).
* **(2.2), (2.4).** On `z ↔ ∂B_n`, a cut that is not linked has two crossing clusters in one half
  of its annulus (`mem_setOf_crossing_clusters_of_mem_armEvent`), which has probability at most
  `(1 - c₀)^K` relative to any increasing event by (A1)
  (`exists_law_inter_armEvent_inter_not_link_le`, `exists_law_inter_armEvent_le_add_of_cuts`).
* **The Cauchy property** (Basu–Sapozhnikov (2.1), (2.8)). The ratio contraction of
  `RatioContraction.lean` bounds the dependence on `n` by `((κ² - 1)/(κ² + 1))^S`; with the errors
  of the cuts this gives `exists_abs_toReal_cond_armEvent_sub_le_of_isUpperSet` for increasing
  events, and inclusion–exclusion (`CylinderLimit.lean`) every cylinder event,
  `exists_abs_toReal_cond_armEvent_sub_le`.

## Main results

* `PercLib.Models.Planar.law_inter_eq_sum_of_cut`
* `PercLib.Models.Planar.exists_law_localConn_comparable_of_cut`
* `PercLib.Models.Planar.exists_crossRatio_of_cuts`
* `PercLib.Models.Planar.exists_law_inter_armEvent_inter_not_link_le`
* `PercLib.Models.Planar.exists_chain_of_cuts`
* `PercLib.Models.Planar.exists_law_inter_armEvent_le_add_of_cuts`
* `PercLib.Models.Planar.exists_abs_toReal_cond_armEvent_sub_le_of_isUpperSet`
* `PercLib.Models.Planar.exists_abs_toReal_cond_armEvent_sub_le`
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

/-- **The cross-ratio bound from a sandwich of probabilities.** If `B b ≠ 0` implies
`c f(a) g(b) ≤ P(a, b) ≤ f(a) g(b)` (all finite, `0 < c ≤ 1`), then the real matrix
`M(a, b) = P(a, b) B(b)` satisfies `M(a, b) M(a', b') ≤ c⁻² M(a, b') M(a', b)`. -/
theorem toReal_mul_le_inv_sq_mul_of_le_mul {α β : Type*} {P : α → β → ℝ≥0∞} {B g : β → ℝ≥0∞}
    {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hc1 : c ≤ 1) (hf : ∀ a, f a ≠ ⊤)
    (hg : ∀ b, g b ≠ ⊤)
    (h : ∀ a b, B b ≠ 0 → c * f a * g b ≤ P a b ∧ P a b ≤ f a * g b) (a a' : α) (b b' : β) :
    ((P a b).toReal * (B b).toReal) * ((P a' b').toReal * (B b').toReal) ≤
      c.toReal⁻¹ ^ 2 * (((P a b').toReal * (B b').toReal) * ((P a' b).toReal * (B b).toReal)) := by
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hct
  refine mul_le_inv_sq_mul_of_le_mul (M := fun a b => (P a b).toReal * (B b).toReal)
    (f := fun a => (f a).toReal) (g := fun b => (g b).toReal * (B b).toReal) hcr
    (fun _ => ENNReal.toReal_nonneg) (fun _ => mul_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg) (fun a b => ?_) (fun a b => ?_) a a' b b'
  · by_cases hb : B b = 0
    · simp [hb]
    · have h₁ := (h a b hb).1
      have hfin : P a b ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (hf a) (hg b)) (h a b hb).2
      have h₂ := ENNReal.toReal_mono hfin h₁
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h₂
      calc c.toReal * ((f a).toReal * ((g b).toReal * (B b).toReal))
          = c.toReal * (f a).toReal * (g b).toReal * (B b).toReal := by ring
        _ ≤ (P a b).toReal * (B b).toReal :=
          mul_le_mul_of_nonneg_right h₂ ENNReal.toReal_nonneg
  · by_cases hb : B b = 0
    · simp [hb]
    · have h₂ := ENNReal.toReal_mono (ENNReal.mul_ne_top (hf a) (hg b)) (h a b hb).2
      rw [ENNReal.toReal_mul] at h₂
      calc (P a b).toReal * (B b).toReal ≤ (f a).toReal * (g b).toReal * (B b).toReal :=
          mul_le_mul_of_nonneg_right h₂ ENNReal.toReal_nonneg
        _ = (f a).toReal * ((g b).toReal * (B b).toReal) := by ring

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

/-- **(A2) for the middle factors** (Basu–Sapozhnikov (2.7) on `ℤ²`). There is `c ∈ (0, 1]` such
that for every profile at least `1/2` on the edges, all `m ≥ 1` and `4m < a ≤ c'`, every
`U ⊆ B_{m-1}(z)`, `R ⊆ B_m(z)`, every `X` outside `B_{a-1}(z)` and every `Y` outside `B_{4m}(z)`,
the probability that `R ↔ Y` inside `(B_{c'}(z) \ U) \ X` lies between `c f g` and `f g`, where
`f = P(R ↔ ∂B_{2m}(z) inside B_{2m}(z) \ U)` does not depend on `(X, Y)` and
`g = P(Y ↔ ∂B_{2m}(z) inside (B_{c'}(z) \ B_{2m-1}(z)) \ X)` does not depend on `(U, R)`. The radii
`2m` and `4m` are passed as `m₂` and `m₄`. -/
theorem exists_law_localConn_comparable_of_cut :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (m m₂ m₄ a c' : ℕ), 1 ≤ m → m₂ = 2 * m → m₄ = 4 * m → m₄ < a →
      a ≤ c' → ∀ U R X Y : Set (LatticeSite 2),
        U ⊆ Icc (z - (m : LatticeSite 2) + 1) (z + m - 1) →
        R ⊆ Icc (z - (m : LatticeSite 2)) (z + m) →
        (∀ v ∈ X, v ∉ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) →
        (∀ y ∈ Y, y ∉ Icc (z - (m₄ : LatticeSite 2)) (z + m₄)) →
        c * law q {ω | ∃ r ∈ R, ∃ w ∈ boxBoundary (z - (m₂ : LatticeSite 2)) (z + m₂),
              ω ∩ (zdGraph 2).edgeSet ∈
                localConn (Icc (z - (m₂ : LatticeSite 2)) (z + m₂) ∩ Uᶜ) r w} *
            law q {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - (m₂ : LatticeSite 2)) (z + m₂),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c' : LatticeSite 2)) (z + c') \
                Icc (z - (m₂ : LatticeSite 2) + 1) (z + m₂ - 1)) \ X) y w} ≤
          law q {ω | ∃ r ∈ R, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn
            ((Icc (z - (c' : LatticeSite 2)) (z + c') ∩ Uᶜ) \ X) r y} ∧
        law q {ω | ∃ r ∈ R, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn
            ((Icc (z - (c' : LatticeSite 2)) (z + c') ∩ Uᶜ) \ X) r y} ≤
          law q {ω | ∃ r ∈ R, ∃ w ∈ boxBoundary (z - (m₂ : LatticeSite 2)) (z + m₂),
              ω ∩ (zdGraph 2).edgeSet ∈
                localConn (Icc (z - (m₂ : LatticeSite 2)) (z + m₂) ∩ Uᶜ) r w} *
            law q {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - (m₂ : LatticeSite 2)) (z + m₂),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c' : LatticeSite 2)) (z + c') \
                Icc (z - (m₂ : LatticeSite 2) + 1) (z + m₂ - 1)) \ X) y w} := by
  obtain ⟨c, hc, hcq⟩ := exists_law_setOf_localConn_comparable
  refine ⟨min c 1, lt_min hc one_pos, min_le_right _ _,
    fun q hq z m m₂ m₄ a c' hm hm₂ hm₄ hma hac' U R X Y hU hR hX hY => ?_⟩
  subst hm₂ hm₄
  have hAZ : Icc (z - ((4 * m : ℕ) : LatticeSite 2)) (z + ((4 * m : ℕ) : LatticeSite 2)) \
      Icc (z - (m : LatticeSite 2) + 1) (z + m - 1) ⊆
      (Icc (z - (c' : LatticeSite 2)) (z + c') ∩ Uᶜ) \ X := by
    intro v hv
    refine ⟨⟨?_, fun hvU => hv.2 (hU hvU)⟩, fun hvX => hX v hvX ?_⟩
    · have := hv.1
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
      omega
    · have := hv.1
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
      omega
  have h := hcq q hq z m hm R Y _ hAZ hR hY
  have ef : {ω : Config (LatticeSite 2) | ∃ r ∈ R,
      ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c' : LatticeSite 2)) (z + c') ∩ Uᶜ) \ X)
        r w} = {ω | ∃ r ∈ R,
      ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - ((2 * m : ℕ) : LatticeSite 2))
        (z + ((2 * m : ℕ) : LatticeSite 2)) ∩ Uᶜ) r w} := by
    ext ω
    constructor
    · rintro ⟨r, hr, w, hw, hrw⟩
      have hr2 : r ∈ Icc (z - ((2 * m : ℕ) : LatticeSite 2))
          (z + ((2 * m : ℕ) : LatticeSite 2)) := by
        have := hR hr
        rw [mem_Icc_two_iff] at this ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
        omega
      have hw2 : w ∉ Icc (z - ((2 * m : ℕ) : LatticeSite 2) + 1)
          (z + ((2 * m : ℕ) : LatticeSite 2) - 1) := by
        rw [mem_boxBoundary_two_iff] at hw
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw ⊢
        omega
      obtain ⟨w', hw', hrw'⟩ := exists_mem_boxBoundary_mem_localConn_inter hr2 hw2 hrw
      refine ⟨r, hr, w', hw', localConn_mono_set ?_ _ _ hrw'⟩
      exact fun v hv => ⟨hv.2, hv.1.1.2⟩
    · rintro ⟨r, hr, w, hw, hrw⟩
      refine ⟨r, hr, w, hw, localConn_mono_set ?_ _ _ hrw⟩
      intro v hv
      refine ⟨⟨?_, hv.2⟩, fun hvX => hX v hvX ?_⟩
      · have := hv.1
        rw [mem_Icc_two_iff] at this ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
        omega
      · have := hv.1
        rw [mem_Icc_two_iff] at this ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
        omega
  have eg : {ω : Config (LatticeSite 2) | ∃ y ∈ Y,
      ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c' : LatticeSite 2)) (z + c') ∩ Uᶜ) \ X)
        y w} = {ω | ∃ y ∈ Y,
      ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c' : LatticeSite 2)) (z + c') \
        Icc (z - ((2 * m : ℕ) : LatticeSite 2) + 1) (z + ((2 * m : ℕ) : LatticeSite 2) - 1)) \ X)
        y w} := by
    ext ω
    constructor
    · rintro ⟨y, hy, w, hw, hyw⟩
      have hy2 : y ∉ Icc (z - ((2 * m : ℕ) : LatticeSite 2) + 1)
          (z + ((2 * m : ℕ) : LatticeSite 2) - 1) := by
        have := hY y hy
        rw [mem_Icc_two_iff] at this ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
        omega
      obtain ⟨w', hw', hyw'⟩ :=
        exists_mem_boxBoundary_mem_localConn_diff hy2 (mem_boxBoundary_iff.1 hw).1 hyw
      refine ⟨y, hy, w', hw', localConn_mono_set ?_ _ _ hyw'⟩
      exact fun v hv => ⟨⟨hv.1.1.1, hv.2⟩, hv.1.2⟩
    · rintro ⟨y, hy, w, hw, hyw⟩
      refine ⟨y, hy, w, hw, localConn_mono_set ?_ _ _ hyw⟩
      intro v hv
      refine ⟨⟨hv.1.1, fun hvU => hv.1.2 ?_⟩, hv.2⟩
      have := hU hvU
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
      omega
  rw [ef, eg] at h
  refine ⟨le_trans ?_ h.1, h.2⟩
  gcongr
  exact min_le_left _ _

/-- **A failed link on the arm event gives two crossing clusters.** If `z ↔ ∂B_n(z)` with
`n > b`, and some crossing of the inner half `B_c \ B_{a-1}` of the annulus of a cut is not joined
inside the annulus to some crossing of the outer half `B_b \ B_{c-1}`, then one of the two halves
has two distinct open crossing clusters. -/
theorem mem_setOf_crossing_clusters_of_mem_armEvent {ω : Config (LatticeSite 2)}
    {z : LatticeSite 2} {a c b n : ℕ} (ha : 1 ≤ a) (hac : a < c) (hcb : c < b) (hbn : b < n)
    (harm : ω ∈ armEvent z n)
    (hlink : ¬ ∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y) :
    ω ∈ {ω | ∃ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
        ∃ x' ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
        ∃ y ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
        ∃ y' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
            Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
            Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x' y' ∧
          ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
            Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x x'} ∨
    ω ∈ {ω | ∃ x ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
        ∃ x' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
        ∃ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ∃ y' ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
            Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) x y ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
            Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) x' y' ∧
          ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
            Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) x x'} := by
  by_contra hno
  rw [not_or] at hno
  obtain ⟨h₁, h₂⟩ := hno
  apply hlink
  rw [mem_armEvent_iff_exists_mem_boxBoundary] at harm
  obtain ⟨v, hv, hzv⟩ := harm
  have hzb : z ∈ Icc (z - (b : LatticeSite 2)) (z + b) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  have hvb : v ∉ Icc (z - (b : LatticeSite 2) + 1) (z + b - 1) := by
    rw [mem_boxBoundary_two_iff] at hv
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    omega
  obtain ⟨b₀, hb₀, hzb₀⟩ := exists_mem_boxBoundary_mem_localConn_inter hzb hvb hzv
  rw [localConn_comm] at hzb₀
  have hb₀a : b₀ ∉ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    have := hb₀
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  have hza : z ∈ Icc (z - (a : LatticeSite 2)) (z + a) := by
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨a₀, ha₀, hb₀a₀⟩ := exists_mem_boxBoundary_mem_localConn_diff hb₀a hza hzb₀
  have hcross : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) b₀ a₀ :=
    by refine localConn_mono_set ?_ _ _ hb₀a₀; exact fun u hu => ⟨hu.1.2, hu.2⟩
  have ha₀c : a₀ ∈ Icc (z - (c : LatticeSite 2)) (z + c) := by
    have := ha₀
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
    omega
  have hb₀c : b₀ ∉ Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) := by
    have := hb₀
    rw [mem_boxBoundary_two_iff] at this
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  obtain ⟨m₀, hm₀, ha₀m₀⟩ := exists_mem_boxBoundary_mem_localConn_inter ha₀c hb₀c
    (by rw [localConn_comm]; exact hcross)
  obtain ⟨m₁, hm₁, hb₀m₁⟩ := exists_mem_boxBoundary_mem_localConn_diff hb₀c ha₀c hcross
  have hsac : (Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) ∩ Icc (z - (c : LatticeSite 2)) (z + c) ⊆
      Icc (z - (c : LatticeSite 2)) (z + c) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    intro u hu
    simp only [mem_inter_iff, mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have hscb : (Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) \
      Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) := by
    intro u hu
    simp only [mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have hac' : Icc (z - (c : LatticeSite 2)) (z + c) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    intro u hu
    simp only [mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have hcb' : Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (c : LatticeSite 2) + 1) (z + c - 1) ⊆
      Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    intro u hu
    simp only [mem_sdiff, mem_Icc_two_iff, Pi.add_apply, Pi.sub_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    omega
  have ha₀m₀' := localConn_mono_set hsac _ _ ha₀m₀
  have hb₀m₁' := localConn_mono_set hscb _ _ hb₀m₁
  intro x hx m hm m' hm' y hy hxm hm'y
  have e₁ : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x a₀ := by
    by_contra hne
    exact h₁ ⟨x, hx, a₀, ha₀, m, hm, m₀, hm₀, hxm, ha₀m₀', hne⟩
  have e₂ : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' m₁ := by
    by_contra hne
    exact h₂ ⟨m', hm', m₁, hm₁, y, hy, b₀, hb₀, hm'y, by rw [localConn_comm]; exact hb₀m₁', hne⟩
  rw [localConn_comm] at hcross e₂
  exact localConn_trans (localConn_mono_set hac' _ _ e₁) (localConn_trans hcross
    (localConn_trans (localConn_mono_set hcb' _ _ hb₀m₁') (localConn_trans
      (localConn_mono_set hcb' _ _ e₂) (localConn_mono_set hcb' _ _ hm'y))))

/-- **A link fails rarely on the arm event** (Basu–Sapozhnikov (2.2) and the error of (2.4) on
`ℤ²`). There is `c₀ > 0` such that for every profile at least `1/2` on the edges, every
measurable increasing event `E`, every cut with radii `1 ≤ a < c < b`, `4^K a ≤ c`, `4^K c ≤ b`,
and every `n > b`, the probability that `E` holds, `z ↔ ∂B_n(z)`, and the link event of the cut
fails is at most `2 (1 - c₀)^K` times the probability of `E` with `z ↔ ∂B_n(z)`. -/
theorem exists_law_inter_armEvent_inter_not_link_le :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ E : Set (Config (LatticeSite 2)), IsUpperSet E → MeasurableSet E →
      ∀ (z : LatticeSite 2) (a c b n K : ℕ), 1 ≤ a → a < c → c < b → b < n →
        4 ^ K * a ≤ c → 4 ^ K * c ≤ b →
        law q (E ∩ armEvent z n ∩ {ω | ¬ ∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
          ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
          ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
          ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
            ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
              Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
            ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
              Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
            ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
              Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y}) ≤
          2 * (1 - c₀) ^ K * law q (E ∩ armEvent z n) := by
  obtain ⟨c₀, hc₀, hcq⟩ := exists_law_inter_setOf_crossing_clusters_le
  refine ⟨c₀, hc₀, fun q hq E hEu hEm z a c b n K ha hac hcb hbn hK₁ hK₂ => ?_⟩
  have hu : IsUpperSet (E ∩ armEvent z n) := hEu.inter (isUpperSet_armEvent z n)
  have hm : MeasurableSet (E ∩ armEvent z n) := hEm.inter (measurableSet_armEvent z n)
  have h₁ := hcq q hq _ hu hm z a c K ha hK₁
  have h₂ := hcq q hq _ hu hm z c b K (by omega) hK₂
  refine le_trans (measure_mono fun ω hω => ?_) ((measure_union_le _ _).trans
    ((add_le_add h₁ h₂).trans_eq (by ring)))
  obtain ⟨⟨hE, harm⟩, hl⟩ := hω
  rcases mem_setOf_crossing_clusters_of_mem_armEvent ha hac hcb hbn harm hl with h | h
  · exact Or.inl ⟨⟨hE, harm⟩, h⟩
  · exact Or.inr ⟨⟨hE, harm⟩, h⟩

/-- **The link event of a cut is determined by the edges inside its annulus.** -/
theorem link_iff_of_inter_eq {z : LatticeSite 2} {a c b : ℕ} (hac : a < c) (hcb : c < b)
    {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)} =
      ω' ∩ {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ v ∈ e, v ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)}) :
    (∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y) ↔
    (∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω' ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y) := by
  have key : ∀ S ⊆ Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1), ∀ x y,
      ω ∩ (zdGraph 2).edgeSet ∈ localConn S x y ↔ ω' ∩ (zdGraph 2).edgeSet ∈ localConn S x y := by
    intro S hS x y
    have h' := inter_mem_localConn_iff_of_inter_eq hS (zdGraph 2).edgeSet
      (ω := ω ∩ (zdGraph 2).edgeSet) (ω' := ω' ∩ (zdGraph 2).edgeSet)
      (by rw [inter_assoc, inter_assoc]; exact h) x y
    simpa only [inter_assoc, inter_self] using h'
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
  constructor
  · intro hL x hx m hm m' hm' y hy h₁ h₂
    exact (key _ subset_rfl x y).1 (hL x hx m hm m' hm' y hy ((key _ hsac x m).2 h₁)
      ((key _ hscb m' y).2 h₂))
  · intro hL x hx m hm m' hm' y hy h₁ h₂
    exact (key _ subset_rfl x y).2 (hL x hx m hm m' hm' y hy ((key _ hsac x m).1 h₁)
      ((key _ hscb m' y).1 h₂))

/-- The link event of a cut is measurable. -/
theorem measurableSet_setOf_link {z : LatticeSite 2} {a c b : ℕ} (hac : a < c) (hcb : c < b) :
    MeasurableSet {ω : Config (LatticeSite 2) | ∀ x ∈ boxBoundary (z - (a : LatticeSite 2)) (z + a),
      ∀ m ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ m' ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
      ∀ y ∈ boxBoundary (z - (b : LatticeSite 2)) (z + b),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c : LatticeSite 2)) (z + c) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (c : LatticeSite 2) + 1) (z + c - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) x y} := by
  have hQF : {e : Sym2 (LatticeSite 2) | e ∈ (zdGraph 2).edgeSet ∧
      ∀ v ∈ e, v ∈ Icc (z - (b : LatticeSite 2)) (z + b) \
        Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)} ⊆
      ↑(Finset.Icc (z - (b : LatticeSite 2)) (z + b)).sym2 := by
    rintro e ⟨-, he⟩
    rw [Finset.mem_coe, Finset.mem_sym2_iff]
    intro v hv
    rw [← Finset.mem_coe, Finset.coe_Icc]
    exact (he v hv).1
  refine measurableSet_of_determined_finset (F := (Finset.Icc (z - (b : LatticeSite 2))
    (z + b)).sym2) fun ω => link_iff_of_inter_eq hac hcb ?_
  rw [inter_assoc, inter_eq_right.2 hQF]

/-- **One step of the chain** (Basu–Sapozhnikov (2.5) on `ℤ²`). Let the previous cut leave the set
`U₀ ⊆ B_{b₀}(z)` (its cluster with the ball inside its middle sphere) and the outer port
`R₀ ⊆ B_{b₀+1}(z)`, and let the next cut have radii `a < c < b` with `b₀ + 2 ≤ a`. Then
`P(R₀ ↔ ∂B_n inside B_n \ U₀, the cut is linked, H)` is the sum over the values of the cut of
`P(R₀ ↔ Y₀ inside (B_c \ U₀) \ W₀) · P(cut value, link) · P(R₀' ↔ ∂B_n inside B_n \ (W₀ ∪ B_c), H)`.
-/
theorem law_inter_eq_sum_of_cut_of_prev (q : Sym2 (LatticeSite 2) → unitInterval)
    {z : LatticeSite 2} {a c b n b₀ : ℕ} (hac : a < c) (hcb : c < b) (hbn : b < n)
    (hb₀ : b₀ + 2 ≤ a)
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
    {H : Set (Config (LatticeSite 2))} (hHm : MeasurableSet H)
    (hH : ∀ ω ω', ω ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} =
      ω' ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} → (ω ∈ H ↔ ω' ∈ H))
    (T : Finset (Finset (LatticeSite 2) × Finset (LatticeSite 2) × Finset (LatticeSite 2)))
    (hT : ∀ ω, ∃ x ∈ T, W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2)
    {U₀ R₀ : Set (LatticeSite 2)} (hU₀ : U₀ ⊆ Icc (z - (b₀ : LatticeSite 2)) (z + b₀))
    (hR₀ : R₀ ⊆ Icc (z - ((b₀ + 1 : ℕ) : LatticeSite 2)) (z + ((b₀ + 1 : ℕ) : LatticeSite 2))) :
    law q ({ω | ∃ r ∈ R₀, ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) \ U₀) r w} ∩
      G ∩ H) =
    ∑ x ∈ T, law q {ω | ∃ r ∈ R₀, ∃ y ∈ (x.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ U₀ᶜ) \ ↑x.1) r y} *
      law q ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) *
      law q ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) := by
  have hUc : U₀ ⊆ Icc (z - (c : LatticeSite 2)) (z + c) := fun v hv => by
    have := hU₀ hv
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
    omega
  have hP : R₀ ⊆ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := fun v hv => by
    have := hR₀ hv
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  have hD : Icc (z - (b : LatticeSite 2)) (z + b) \
      Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ⊆ U₀ᶜ := fun v hv hvU => hv.2 (by
    have := hU₀ hvU
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega)
  have h := law_inter_eq_sum_of_cut q hac hcb hbn hW hY hR hG hP hD MeasurableSet.univ
    (fun _ _ _ => iff_of_true (mem_univ _) (mem_univ _)) hHm hH T hT
  have hreg : ∀ X : Set (LatticeSite 2), (Icc (z - (n : LatticeSite 2)) (z + n) ∩ U₀ᶜ) \
      (X ∪ Icc (z - (c : LatticeSite 2)) (z + c)) =
      Icc (z - (n : LatticeSite 2)) (z + n) \ (X ∪ Icc (z - (c : LatticeSite 2)) (z + c)) :=
    fun X => by
      ext v
      simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_union, not_or]
      exact ⟨fun ⟨⟨hn, _⟩, hX, hc⟩ => ⟨hn, hX, hc⟩,
        fun ⟨hn, hX, hc⟩ => ⟨⟨hn, fun hU => hc (hUc hU)⟩, hX, hc⟩⟩
  simp only [univ_inter, hreg] at h
  rw [Set.sdiff_eq (Icc (z - (n : LatticeSite 2)) (z + n)) U₀]
  exact h

/-- **The start of the chain** (Basu–Sapozhnikov (2.3)-(2.4) at the first cut). For a cut with
radii `1 ≤ a < c < b` and `n > b`, an event `E` of the pairs inside `B_{a-1}(z)` and off the
edges, and an event `H` of the edges outside `B_b(z)`,
`P(E, z ↔ ∂B_n, the cut is linked, H)` is the sum over the values of the cut of
`P(E, z ↔ Y₀ inside B_c \ W₀) · P(cut value, link) · P(R₀ ↔ ∂B_n inside B_n \ (W₀ ∪ B_c), H)`. -/
theorem law_inter_armEvent_eq_sum_of_cut (q : Sym2 (LatticeSite 2) → unitInterval)
    {z : LatticeSite 2} {a c b n : ℕ} (ha : 1 ≤ a) (hac : a < c) (hcb : c < b) (hbn : b < n)
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
    {E : Set (Config (LatticeSite 2))} (hEm : MeasurableSet E)
    (hE : ∀ ω ω', ω ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)} =
      ω' ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)} → (ω ∈ E ↔ ω' ∈ E))
    {H : Set (Config (LatticeSite 2))} (hHm : MeasurableSet H)
    (hH : ∀ ω ω', ω ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} =
      ω' ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
        ∀ v ∈ e, v ∉ Icc (z - (b : LatticeSite 2)) (z + b)} → (ω ∈ H ↔ ω' ∈ H))
    (T : Finset (Finset (LatticeSite 2) × Finset (LatticeSite 2) × Finset (LatticeSite 2)))
    (hT : ∀ ω, ∃ x ∈ T, W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2) :
    law q (E ∩ armEvent z n ∩ G ∩ H) =
    ∑ x ∈ T, law q (E ∩ {ω | ∃ p ∈ ({z} : Set (LatticeSite 2)),
        ∃ y ∈ (x.2.1 : Set (LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c : LatticeSite 2)) (z + c) ∩ univ) \ ↑x.1) p y}) *
      law q ({ω | W ω = ↑x.1 ∧ Y ω = ↑x.2.1 ∧ R ω = ↑x.2.2} ∩ G) *
      law q ({ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
        ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) \
          (↑x.1 ∪ Icc (z - (c : LatticeSite 2)) (z + c))) r w} ∩ H) := by
  have hP : ({z} : Set (LatticeSite 2)) ⊆ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := by
    rintro v rfl
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have h := law_inter_eq_sum_of_cut q hac hcb hbn hW hY hR hG hP (subset_univ _) hEm
    (fun ω ω' h => hE ω ω' (by simpa only [inter_univ] using h)) hHm hH T hT
  have harm : armEvent z n = {ω | ∃ p ∈ ({z} : Set (LatticeSite 2)),
      ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) ∩ univ) p w} := by
    ext ω
    rw [mem_armEvent_iff_exists_mem_boxBoundary]
    simp only [mem_ofPred_eq, mem_singleton_iff, exists_eq_left, inter_univ]
  have hreg : ∀ X : Set (LatticeSite 2), (Icc (z - (n : LatticeSite 2)) (z + n) ∩ univ) \
      (X ∪ Icc (z - (c : LatticeSite 2)) (z + c)) =
      Icc (z - (n : LatticeSite 2)) (z + n) \ (X ∪ Icc (z - (c : LatticeSite 2)) (z + c)) :=
    fun X => by rw [inter_univ]
  simp only [hreg] at h
  rw [harm]
  exact h

/-- **The cross-ratio bound for the transfer matrices** (Basu–Sapozhnikov (2.7) on `ℤ²`). There is
`κ ≥ 1` such that for every profile at least `1/2` on the edges and two consecutive cuts (the
first with middle radius `c₁ ≤ b₁` and outer radius `b₁`, the second with radii `a < c < b`,
`4 (b₁ + 1) + 2 ≤ a`), the matrix
`M(x, y) = P(R_x ↔ Y_y inside (B_c \ (W_x ∪ B_{c₁})) \ W_y) · P(second cut has value y, link)`
satisfies `M(x, y) M(x', y') ≤ κ² M(x, y') M(x', y)` for all values `x, x'` of the first cut
(`W_x ⊆ B_{b₁}`, `R_x ⊆ B_{b₁+1}`) and all values `y, y'` of the second. -/
theorem exists_crossRatio_of_cuts :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (c₁ b₁ a c b : ℕ), c₁ ≤ b₁ → 4 * (b₁ + 1) + 2 ≤ a → a < c →
      ∀ (W Y R : Config (LatticeSite 2) → Set (LatticeSite 2)),
      (∀ ω v, v ∈ W ω ↔ ∃ w ∈ boxBoundary (z - (c : LatticeSite 2)) (z + c),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2)) (z + b) \
          Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w) →
      (∀ ω y, y ∈ Y ω ↔ y ∈ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) ∧
        ∃ v ∈ W ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet) →
      ∀ (G : Set (Config (LatticeSite 2)))
        (x x' y y' : Finset (LatticeSite 2) × Finset (LatticeSite 2) × Finset (LatticeSite 2)),
      (↑x.1 : Set (LatticeSite 2)) ⊆ Icc (z - (b₁ : LatticeSite 2)) (z + b₁) →
      (↑x.2.2 : Set (LatticeSite 2)) ⊆
        Icc (z - ((b₁ + 1 : ℕ) : LatticeSite 2)) (z + ((b₁ + 1 : ℕ) : LatticeSite 2)) →
      (↑x'.1 : Set (LatticeSite 2)) ⊆ Icc (z - (b₁ : LatticeSite 2)) (z + b₁) →
      (↑x'.2.2 : Set (LatticeSite 2)) ⊆
        Icc (z - ((b₁ + 1 : ℕ) : LatticeSite 2)) (z + ((b₁ + 1 : ℕ) : LatticeSite 2)) →
        ((law q {ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
            ∃ v ∈ (y.2.1 : Set (LatticeSite 2)),
            ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c : LatticeSite 2)) (z + c) ∩
              (↑x.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁))ᶜ) \ ↑y.1) r v}).toReal *
          (law q ({ω | W ω = ↑y.1 ∧ Y ω = ↑y.2.1 ∧ R ω = ↑y.2.2} ∩ G)).toReal) *
        ((law q {ω | ∃ r ∈ (x'.2.2 : Set (LatticeSite 2)),
            ∃ v ∈ (y'.2.1 : Set (LatticeSite 2)),
            ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c : LatticeSite 2)) (z + c) ∩
              (↑x'.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁))ᶜ) \ ↑y'.1) r v}).toReal *
          (law q ({ω | W ω = ↑y'.1 ∧ Y ω = ↑y'.2.1 ∧ R ω = ↑y'.2.2} ∩ G)).toReal) ≤
        κ ^ 2 * (((law q {ω | ∃ r ∈ (x.2.2 : Set (LatticeSite 2)),
              ∃ v ∈ (y'.2.1 : Set (LatticeSite 2)),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c : LatticeSite 2)) (z + c) ∩
                (↑x.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁))ᶜ) \ ↑y'.1) r v}).toReal *
            (law q ({ω | W ω = ↑y'.1 ∧ Y ω = ↑y'.2.1 ∧ R ω = ↑y'.2.2} ∩ G)).toReal) *
          ((law q {ω | ∃ r ∈ (x'.2.2 : Set (LatticeSite 2)),
              ∃ v ∈ (y.2.1 : Set (LatticeSite 2)),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c : LatticeSite 2)) (z + c) ∩
                (↑x'.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁))ᶜ) \ ↑y.1) r v}).toReal *
            (law q ({ω | W ω = ↑y.1 ∧ Y ω = ↑y.2.1 ∧ R ω = ↑y.2.2} ∩ G)).toReal)) := by
  obtain ⟨cs, hcs, hcs1, hsand⟩ := exists_law_localConn_comparable_of_cut
  have hct : cs ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcs1
  have hcr : 0 < cs.toReal := ENNReal.toReal_pos hcs.ne' hct
  have hcr1 : cs.toReal ≤ 1 := by
    have := (ENNReal.toReal_le_toReal hct ENNReal.one_ne_top).2 hcs1
    rwa [ENNReal.toReal_one] at this
  refine ⟨cs.toReal⁻¹, (one_le_inv₀ hcr).2 hcr1, fun q hq z c₁ b₁ a c b hcb₁ hgap hac W Y R hW hY
    G x x' y y' hx₁ hx₂ hx₁' hx₂' => ?_⟩
  have key := toReal_mul_le_inv_sq_mul_of_le_mul
    (α := {x : Finset (LatticeSite 2) × Finset (LatticeSite 2) × Finset (LatticeSite 2) //
      (↑x.1 : Set (LatticeSite 2)) ⊆ Icc (z - (b₁ : LatticeSite 2)) (z + b₁) ∧
      (↑x.2.2 : Set (LatticeSite 2)) ⊆
        Icc (z - ((b₁ + 1 : ℕ) : LatticeSite 2)) (z + ((b₁ + 1 : ℕ) : LatticeSite 2))})
    (P := fun x y => law q {ω | ∃ r ∈ (x.1.2.2 : Set (LatticeSite 2)),
      ∃ v ∈ (y.2.1 : Set (LatticeSite 2)),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c : LatticeSite 2)) (z + c) ∩
          (↑x.1.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁))ᶜ) \ ↑y.1) r v})
    (B := fun y => law q ({ω | W ω = ↑y.1 ∧ Y ω = ↑y.2.1 ∧ R ω = ↑y.2.2} ∩ G))
    (f := fun x => law q {ω | ∃ r ∈ (x.1.2.2 : Set (LatticeSite 2)),
      ∃ w ∈ boxBoundary (z - ((2 * (b₁ + 1) : ℕ) : LatticeSite 2))
        (z + ((2 * (b₁ + 1) : ℕ) : LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - ((2 * (b₁ + 1) : ℕ) : LatticeSite 2))
        (z + ((2 * (b₁ + 1) : ℕ) : LatticeSite 2)) ∩
          (↑x.1.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁))ᶜ) r w})
    (g := fun y => law q {ω | ∃ v ∈ (y.2.1 : Set (LatticeSite 2)),
      ∃ w ∈ boxBoundary (z - ((2 * (b₁ + 1) : ℕ) : LatticeSite 2))
        (z + ((2 * (b₁ + 1) : ℕ) : LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c : LatticeSite 2)) (z + c) \
        Icc (z - ((2 * (b₁ + 1) : ℕ) : LatticeSite 2) + 1)
          (z + ((2 * (b₁ + 1) : ℕ) : LatticeSite 2) - 1)) \ ↑y.1) v w})
    hcs hcs1 (fun _ => measure_ne_top _ _) (fun _ => measure_ne_top _ _) ?_
    ⟨x, hx₁, hx₂⟩ ⟨x', hx₁', hx₂'⟩ y y'
  · exact key
  rintro ⟨x, hx₁, hx₂⟩ y hB
  obtain ⟨ω₀, ⟨hW₀, hY₀, -⟩, -⟩ := nonempty_of_measure_ne_zero hB
  have hX : ∀ v ∈ (↑y.1 : Set (LatticeSite 2)),
      v ∉ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1) := fun v hv => by
    rw [← hW₀] at hv
    obtain ⟨_, _, hvA, -, -⟩ := (hW ω₀ v).1 hv
    exact hvA.2
  have hYp : ∀ u ∈ (↑y.2.1 : Set (LatticeSite 2)), u ∉
      Icc (z - ((4 * (b₁ + 1) : ℕ) : LatticeSite 2)) (z + ((4 * (b₁ + 1) : ℕ) : LatticeSite 2)) :=
    fun u hu => by
      rw [← hY₀] at hu
      obtain ⟨-, v, hv, hvu⟩ := (hY ω₀ u).1 hu
      obtain ⟨_, _, hvA, -, -⟩ := (hW ω₀ v).1 hv
      have hadj : (zdGraph 2).Adj v u := hvu.2
      rw [zdGraph_two_adj_iff] at hadj
      rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff] at hvA
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvA ⊢
      omega
  have hU : (↑x.1 ∪ Icc (z - (c₁ : LatticeSite 2)) (z + c₁) : Set (LatticeSite 2)) ⊆
      Icc (z - ((b₁ + 1 : ℕ) : LatticeSite 2) + 1) (z + ((b₁ + 1 : ℕ) : LatticeSite 2) - 1) := by
    intro v hv
    have hv' : v ∈ Icc (z - (b₁ : LatticeSite 2)) (z + b₁) := by
      rcases hv with hv | hv
      · exact hx₁ hv
      · rw [mem_Icc_two_iff] at hv ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv ⊢
        omega
    rw [mem_Icc_two_iff] at hv' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv' ⊢
    omega
  exact hsand q hq z (b₁ + 1) (2 * (b₁ + 1)) (4 * (b₁ + 1)) a c (by omega) rfl rfl (by omega)
    hac.le _ _ _ _ hU hx₂ hX hYp

/-- **The Basu–Sapozhnikov chain** ((2.3)-(2.6) on `ℤ²`). There is `κ ≥ 1` such that for every
profile at least `1/2` on the edges, every sequence of cuts with radii `a k < c k < b k`,
`1 ≤ a 0`, `4 (b k + 1) + 2 ≤ a (k + 1)`, every `S` and every measurable event `E` of the pairs
inside `B_{a 0 - 1}(z)` and off the edges, there are finite sets `T k` of cut values, matrices
`M k` with the cross-ratio bound `M x y · M x' y' ≤ κ² M x y' · M x' y`, and weights `0 ≤ u' ≤ u''`
such that for every `n > b S` a backward chain `w` (`w k = M k w (k + 1)` for `k < S`,
`w S ≥ 0`) gives `⟨u', w 0⟩ = P(E, z ↔ ∂B_n(z), cuts 0, …, S linked)` and
`⟨u'', w 0⟩ = P(z ↔ ∂B_n(z), cuts 0, …, S linked)`. The matrices and weights do not depend on
`n`. -/
theorem exists_chain_of_cuts :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (a c b : ℕ → ℕ), 1 ≤ a 0 → (∀ k, a k < c k) → (∀ k, c k < b k) →
      (∀ k, 4 * (b k + 1) + 2 ≤ a (k + 1)) → ∀ (S : ℕ) (E : Set (Config (LatticeSite 2))),
      MeasurableSet E →
      (∀ ω ω', ω ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
          ∀ v ∈ e, v ∈ Icc (z - (a 0 : LatticeSite 2) + 1) (z + a 0 - 1)} =
        ω' ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
          ∀ v ∈ e, v ∈ Icc (z - (a 0 : LatticeSite 2) + 1) (z + a 0 - 1)} → (ω ∈ E ↔ ω' ∈ E)) →
      ∃ (T : ℕ → Finset (Finset (LatticeSite 2) × Finset (LatticeSite 2) ×
          Finset (LatticeSite 2)))
        (M : ∀ k, T k → T (k + 1) → ℝ) (u' u'' : T 0 → ℝ),
        (∀ k x x' y y', M k x y * M k x' y' ≤ κ ^ 2 * (M k x y' * M k x' y)) ∧
        (∀ x, 0 ≤ u' x) ∧ (∀ x, u' x ≤ u'' x) ∧
        ∀ n, b S < n → ∃ w : ∀ k, T k → ℝ,
          (∀ k < S, ∀ x, w k x = ∑ y, M k x y * w (k + 1) y) ∧ (∀ x, 0 ≤ w S x) ∧
          ∑ x, u' x * w 0 x = (law q (E ∩ armEvent z n ∩ {ω | ∀ k ≤ S,
            ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
              ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y})).toReal ∧
          ∑ x, u'' x * w 0 x = (law q (armEvent z n ∩ {ω | ∀ k ≤ S,
            ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
              ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y})).toReal := by
  classical
  obtain ⟨κ, hκ, hcross⟩ := exists_crossRatio_of_cuts
  refine ⟨κ, hκ, fun q hq z a c b ha hac hcb hgap S E hEm hE => ?_⟩
  have hab : ∀ k, a k < b k := fun k => (hac k).trans (hcb k)
  have hamono : Monotone a := monotone_nat_of_le_succ fun k => by
    have := hgap k
    have := hab k
    omega
  have hbmono : Monotone b := monotone_nat_of_le_succ fun k => by
    have := hgap k
    have := hab (k + 1)
    omega
  have hsep : ∀ k j, k < j → b k + 2 ≤ a j := fun k j hkj => by
    have := hamono (show k + 1 ≤ j from hkj)
    have := hgap k
    omega
  -- the cuts
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Config (LatticeSite 2) → Set (LatticeSite 2), ∀ k ω v,
      v ∈ W k ω ↔ ∃ w ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
          Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) v w :=
    ⟨fun k ω => {v | ∃ w ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
        Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) v w}, fun _ _ _ => Iff.rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Config (LatticeSite 2) → Set (LatticeSite 2), ∀ k ω y,
      y ∈ Y k ω ↔ y ∈ Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1) ∧
        ∃ v ∈ W k ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet :=
    ⟨fun k ω => {y | y ∈ Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1) ∧
      ∃ v ∈ W k ω, s(v, y) ∈ ω ∩ (zdGraph 2).edgeSet}, fun _ _ _ => Iff.rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Config (LatticeSite 2) → Set (LatticeSite 2), ∀ k ω r,
      r ∈ R k ω ↔ r ∉ Icc (z - (b k : LatticeSite 2)) (z + b k) ∧
        ∃ v ∈ W k ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet :=
    ⟨fun k ω => {r | r ∉ Icc (z - (b k : LatticeSite 2)) (z + b k) ∧
      ∃ v ∈ W k ω, s(v, r) ∈ ω ∩ (zdGraph 2).edgeSet}, fun _ _ _ => Iff.rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Set (Config (LatticeSite 2)), ∀ k ω, ω ∈ G k ↔
      ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
      ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
      ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
      ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
          Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
          Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
          Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y :=
    ⟨fun k => {ω | ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
      ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
      ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
      ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
          Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
          Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
          Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y}, fun _ _ => Iff.rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Finset (Finset (LatticeSite 2) × Finset (LatticeSite 2) ×
      Finset (LatticeSite 2)), ∀ k, T k =
      (Finset.Icc (z - (b k : LatticeSite 2)) (z + b k)).powerset ×ˢ
        (Finset.Icc (z - (a k : LatticeSite 2)) (z + a k)).powerset ×ˢ
        (Finset.Icc (z - ((b k + 1 : ℕ) : LatticeSite 2))
          (z + ((b k + 1 : ℕ) : LatticeSite 2))).powerset := ⟨_, fun _ => rfl⟩
  obtain ⟨Hk, hHk⟩ : ∃ Hk : ℕ → Set (Config (LatticeSite 2)),
      ∀ k, Hk k = {ω | ∀ j, k < j → j ≤ S → ω ∈ G j} := ⟨_, fun _ => rfl⟩
  -- positions
  have hWpos : ∀ k ω v, v ∈ W k ω → v ∈ Icc (z - (b k : LatticeSite 2)) (z + b k) :=
    fun k ω v hv => by
      obtain ⟨_, _, hvA, -, -⟩ := (hW k ω v).1 hv
      exact hvA.1
  have hYpos : ∀ k ω y, y ∈ Y k ω → y ∈ Icc (z - (a k : LatticeSite 2)) (z + a k) :=
    fun k ω y hy => by
      have := ((hY k ω y).1 hy).1
      rw [mem_Icc_two_iff] at this ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
      omega
  have hRpos : ∀ k ω r, r ∈ R k ω →
      r ∈ Icc (z - ((b k + 1 : ℕ) : LatticeSite 2)) (z + ((b k + 1 : ℕ) : LatticeSite 2)) :=
    fun k ω r hr => by
      obtain ⟨-, v, hv, hvr⟩ := (hR k ω r).1 hr
      have hvb := hWpos k ω v hv
      have hadj : (zdGraph 2).Adj v r := hvr.2
      rw [zdGraph_two_adj_iff] at hadj
      rw [mem_Icc_two_iff] at hvb ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hvb ⊢
      omega
  have hTpos : ∀ k (x : T k), (↑x.1.1 : Set (LatticeSite 2)) ⊆
      Icc (z - (b k : LatticeSite 2)) (z + b k) ∧ (↑x.1.2.2 : Set (LatticeSite 2)) ⊆
      Icc (z - ((b k + 1 : ℕ) : LatticeSite 2)) (z + ((b k + 1 : ℕ) : LatticeSite 2)) := by
    intro k x
    obtain ⟨t, hx⟩ := x
    rw [hT k, Finset.mem_product, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset,
      Finset.mem_powerset] at hx
    refine ⟨?_, ?_⟩
    · rw [← Finset.coe_Icc]
      exact Finset.coe_subset.2 hx.1
    · rw [← Finset.coe_Icc]
      exact Finset.coe_subset.2 hx.2.2
  have hTcover : ∀ k ω, ∃ x ∈ T k, W k ω = ↑x.1 ∧ Y k ω = ↑x.2.1 ∧ R k ω = ↑x.2.2 := by
    intro k ω
    refine ⟨((Finset.Icc (z - (b k : LatticeSite 2)) (z + b k)).filter (· ∈ W k ω),
      (Finset.Icc (z - (a k : LatticeSite 2)) (z + a k)).filter (· ∈ Y k ω),
      (Finset.Icc (z - ((b k + 1 : ℕ) : LatticeSite 2))
        (z + ((b k + 1 : ℕ) : LatticeSite 2))).filter (· ∈ R k ω)), ?_, ?_, ?_, ?_⟩
    · rw [hT k, Finset.mem_product, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_powerset, Finset.mem_powerset]
      exact ⟨Finset.filter_subset _ _, Finset.filter_subset _ _, Finset.filter_subset _ _⟩
    · ext v
      refine ⟨fun hv => Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 (hWpos k ω v hv), hv⟩), fun hv => ?_⟩
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
    · ext v
      refine ⟨fun hv => Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 (hYpos k ω v hv), hv⟩), fun hv => ?_⟩
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
    · ext v
      refine ⟨fun hv => Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 (hRpos k ω v hv), hv⟩), fun hv => ?_⟩
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
  -- the later link events
  have hGm : ∀ k, MeasurableSet (G k) := fun k => by
    convert measurableSet_setOf_link (z := z) (hac k) (hcb k) using 1
    ext ω
    exact hG k ω
  have hHkm : ∀ k, MeasurableSet (Hk k) := fun k => by
    rw [hHk k]
    exact measurableSet_setOfPred.2 (Measurable.forall fun j => measurable_const.imp
      (measurable_const.imp ((measurableSet_setOfPred (p := fun ω => ω ∈ G j)).1 (hGm j))))
  have hHkd : ∀ k ω ω', ω ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
      ∀ v ∈ e, v ∉ Icc (z - (b k : LatticeSite 2)) (z + b k)} =
      ω' ∩ {e | e ∈ (zdGraph 2).edgeSet ∧
      ∀ v ∈ e, v ∉ Icc (z - (b k : LatticeSite 2)) (z + b k)} → (ω ∈ Hk k ↔ ω' ∈ Hk k) := by
    intro k ω ω' h
    rw [hHk k]
    simp only [mem_ofPred_eq]
    refine forall_congr' fun j => forall_congr' fun hkj => forall_congr' fun _ => ?_
    rw [hG j ω, hG j ω']
    refine link_iff_of_inter_eq (hac j) (hcb j) (inter_eq_inter_of_inter_eq_of_subset h ?_)
    rintro e ⟨heL, he⟩
    refine ⟨heL, fun v hv hvb => (he v hv).2 ?_⟩
    have := hsep k j hkj
    rw [mem_Icc_two_iff] at hvb ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvb ⊢
    omega
  have hHks : ∀ k < S, Hk k = G (k + 1) ∩ Hk (k + 1) := by
    intro k hk
    ext ω
    rw [hHk k, hHk (k + 1)]
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro h
      exact ⟨h (k + 1) (Nat.lt_succ_self k) hk, fun j hj hjS => h j (by omega) hjS⟩
    · rintro ⟨h₁, h₂⟩ j hkj hjS
      rcases (show j = k + 1 ∨ k + 1 < j by omega) with rfl | hj
      · exact h₁
      · exact h₂ j hj hjS
  have hGood : {ω : Config (LatticeSite 2) | ∀ k ≤ S,
      ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
        ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
        ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
        ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
            Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
            Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
            Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y} = G 0 ∩ Hk 0 := by
    ext ω
    rw [hHk 0]
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro h
      exact ⟨(hG 0 ω).2 (h 0 (Nat.zero_le _)), fun j _ hj => (hG j ω).2 (h j hj)⟩
    · rintro ⟨h₀, h⟩ k hk
      rcases Nat.eq_zero_or_pos k with rfl | hk₀
      · exact (hG 0 ω).1 h₀
      · exact (hG k ω).1 (h k hk₀ hk)
  have hfin : ∀ (A B C : Set (Config (LatticeSite 2))), law q A * law q B * law q C ≠ ⊤ :=
    fun A B C => ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)) (measure_ne_top _ _)
  refine ⟨T, fun k x y => (law q {ω | ∃ r ∈ (x.1.2.2 : Set (LatticeSite 2)),
      ∃ v ∈ (y.1.2.1 : Set (LatticeSite 2)),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn ((Icc (z - (c (k + 1) : LatticeSite 2)) (z + c (k + 1)) ∩
        (↑x.1.1 ∪ Icc (z - (c k : LatticeSite 2)) (z + c k))ᶜ) \ ↑y.1.1) r v}).toReal *
      (law q ({ω | W (k + 1) ω = ↑y.1.1 ∧ Y (k + 1) ω = ↑y.1.2.1 ∧ R (k + 1) ω = ↑y.1.2.2} ∩
        G (k + 1))).toReal,
    fun x => (law q (E ∩ {ω | ∃ p ∈ ({z} : Set (LatticeSite 2)),
        ∃ y ∈ (x.1.2.1 : Set (LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c 0 : LatticeSite 2)) (z + c 0) ∩ univ) \ ↑x.1.1) p y})).toReal *
      (law q ({ω | W 0 ω = ↑x.1.1 ∧ Y 0 ω = ↑x.1.2.1 ∧ R 0 ω = ↑x.1.2.2} ∩ G 0)).toReal,
    fun x => (law q (univ ∩ {ω | ∃ p ∈ ({z} : Set (LatticeSite 2)),
        ∃ y ∈ (x.1.2.1 : Set (LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn
          ((Icc (z - (c 0 : LatticeSite 2)) (z + c 0) ∩ univ) \ ↑x.1.1) p y})).toReal *
      (law q ({ω | W 0 ω = ↑x.1.1 ∧ Y 0 ω = ↑x.1.2.1 ∧ R 0 ω = ↑x.1.2.2} ∩ G 0)).toReal,
    fun k x x' y y' => hcross q hq z (c k) (b k) (a (k + 1)) (c (k + 1)) (b (k + 1)) (hcb k).le
      (hgap k) (hac (k + 1)) (W (k + 1)) (Y (k + 1)) (R (k + 1)) (hW (k + 1)) (hY (k + 1))
      (G (k + 1)) x.1 x'.1 y.1 y'.1 (hTpos k x).1 (hTpos k x).2 (hTpos k x').1 (hTpos k x').2,
    fun x => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    fun x => mul_le_mul_of_nonneg_right (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (inter_subset_inter_left _ (subset_univ E)))) ENNReal.toReal_nonneg, ?_⟩
  intro n hn
  refine ⟨fun k x => (law q ({ω | ∃ r ∈ (x.1.2.2 : Set (LatticeSite 2)),
      ∃ w ∈ boxBoundary (z - (n : LatticeSite 2)) (z + n),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (n : LatticeSite 2)) (z + n) \
        (↑x.1.1 ∪ Icc (z - (c k : LatticeSite 2)) (z + c k))) r w} ∩ Hk k)).toReal,
    ?_, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro k hk x
    have hU₀ : (↑x.1.1 ∪ Icc (z - (c k : LatticeSite 2)) (z + c k) : Set (LatticeSite 2)) ⊆
        Icc (z - (b k : LatticeSite 2)) (z + b k) := by
      refine union_subset (hTpos k x).1 fun v hv => ?_
      have := hcb k
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv ⊢
      omega
    have hstep := law_inter_eq_sum_of_cut_of_prev q (hac (k + 1)) (hcb (k + 1))
      (lt_of_le_of_lt (hbmono (Nat.succ_le_of_lt hk)) hn) (hsep k (k + 1) (Nat.lt_succ_self k))
      (hW (k + 1)) (hY (k + 1)) (hR (k + 1)) (hG (k + 1)) (hHkm (k + 1)) (hHkd (k + 1))
      (T (k + 1)) (hTcover (k + 1)) hU₀ (hTpos k x).2
    beta_reduce
    rw [hHks k hk, ← inter_assoc, hstep, ENNReal.toReal_sum fun y _ => hfin _ _ _,
      ← Finset.sum_coe_sort (T (k + 1))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  · have hstart := law_inter_armEvent_eq_sum_of_cut q ha (hac 0) (hcb 0)
      (lt_of_le_of_lt (hbmono (Nat.zero_le S)) hn) (hW 0) (hY 0) (hR 0) (hG 0) hEm hE
      (hHkm 0) (hHkd 0) (T 0) (hTcover 0)
    rw [hGood, ← inter_assoc, hstart, ENNReal.toReal_sum fun x _ => hfin _ _ _,
      ← Finset.sum_coe_sort (T 0)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  · have hstart := law_inter_armEvent_eq_sum_of_cut q ha (hac 0) (hcb 0)
      (lt_of_le_of_lt (hbmono (Nat.zero_le S)) hn) (hW 0) (hY 0) (hR 0) (hG 0)
      MeasurableSet.univ (fun _ _ _ => iff_of_true (mem_univ _) (mem_univ _))
      (hHkm 0) (hHkd 0) (T 0) (hTcover 0)
    rw [univ_inter] at hstart
    rw [hGood, ← inter_assoc, hstart, ENNReal.toReal_sum fun x _ => hfin _ _ _,
      ← Finset.sum_coe_sort (T 0)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]

/-- **All cuts are linked, up to a small error** (Basu–Sapozhnikov (2.4), summed over the cuts).
There is `c₀ > 0` such that for every profile at least `1/2` on the edges, every measurable
increasing event `E`, cuts with radii `1 ≤ a k < c k < b k`, `4^K a k ≤ c k`, `4^K c k ≤ b k`, and
`n > b k` for `k ≤ S`, `P(E, z ↔ ∂B_n)` is at most `P(E, z ↔ ∂B_n, cuts 0, …, S linked)` plus
`(S + 1) · 2 (1 - c₀)^K · P(E, z ↔ ∂B_n)`. -/
theorem exists_law_inter_armEvent_le_add_of_cuts :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ E : Set (Config (LatticeSite 2)), IsUpperSet E → MeasurableSet E →
      ∀ (z : LatticeSite 2) (a c b : ℕ → ℕ) (S K n : ℕ), (∀ k, 1 ≤ a k) → (∀ k, a k < c k) →
      (∀ k, c k < b k) → (∀ k, 4 ^ K * a k ≤ c k) → (∀ k, 4 ^ K * c k ≤ b k) →
      (∀ k ≤ S, b k < n) →
        law q (E ∩ armEvent z n) ≤ law q (E ∩ armEvent z n ∩ {ω | ∀ k ≤ S,
            ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
              ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y}) +
          ((S + 1 : ℕ) : ℝ≥0∞) * (2 * (1 - c₀) ^ K) * law q (E ∩ armEvent z n) := by
  obtain ⟨c₀, hc₀, herr⟩ := exists_law_inter_armEvent_inter_not_link_le
  refine ⟨c₀, hc₀, fun q hq E hEu hEm z a c b S K n ha hac hcb hK₁ hK₂ hbn => ?_⟩
  refine (measure_le_inter_add_sdiff (law q) _ _).trans (add_le_add_right ?_ _)
  calc law q ((E ∩ armEvent z n) \ {ω | ∀ k ≤ S,
          ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
              ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
              ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
                ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                  Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y}) ≤
        ∑ k ∈ Finset.range (S + 1), law q (E ∩ armEvent z n ∩ {ω |
          ¬ ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
            ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
            ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
            ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
                Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
              ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
              ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
                Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y}) := by
        refine (measure_mono ?_).trans (measure_biUnion_finset_le _ _)
        rintro ω ⟨hω, hG⟩
        simp only [mem_ofPred_eq] at hG
        obtain ⟨k, hk'⟩ := Classical.not_forall.1 hG
        obtain ⟨hk, hl⟩ := Classical.not_imp.1 hk'
        simp only [mem_iUnion]
        exact ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), hω, hl⟩
    _ ≤ ∑ k ∈ Finset.range (S + 1), 2 * (1 - c₀) ^ K * law q (E ∩ armEvent z n) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact herr q hq E hEu hEm z (a k) (c k) (b k) n K (ha k) (hac k) (hcb k)
          (hbn k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) (hK₁ k) (hK₂ k)
    _ = ((S + 1 : ℕ) : ℝ≥0∞) * (2 * (1 - c₀) ^ K) * law q (E ∩ armEvent z n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- For a profile at least `1/2` on the edges, `z ↔ ∂B_n(z)` has positive probability. -/
theorem law_armEvent_pos {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) (z : LatticeSite 2) (n : ℕ) :
    0 < law q (armEvent z n) := by
  obtain ⟨q₀, hq₀, hle⟩ := exists_law_le_of_half_le hq
  have h₁ := inv_two_pow_le_law_armEvent hq₀ n
  rw [← law_armEvent_eq_law_armEvent_zero hq₀ z n] at h₁
  exact lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
    (h₁.trans (hle _ (measurableSet_armEvent z n) (isUpperSet_armEvent z n)))

/-- The conditional probability given `z ↔ ∂B_n(z)`, as a ratio of real numbers. -/
theorem toReal_cond_armEvent (q : Sym2 (LatticeSite 2) → unitInterval) (z : LatticeSite 2)
    (n : ℕ) (A : Set (Config (LatticeSite 2))) :
    (ProbabilityTheory.cond (law q) (armEvent z n) A).toReal =
      (law q (A ∩ armEvent z n)).toReal / (law q (armEvent z n)).toReal := by
  rw [ProbabilityTheory.cond_apply (measurableSet_armEvent z n), ENNReal.toReal_mul,
    ENNReal.toReal_inv, inter_comm, div_eq_inv_mul]

/-- **The uniform Cauchy property for increasing events** (Basu–Sapozhnikov (2.1), (2.8) on
`ℤ²`). For every centre `z`, every `N` and every `ε > 0` there is `n₀` such that for every profile
opening each edge with probability at least `1/2` (in particular `p = 1 - e^{-β}` on the edges,
`β ≥ log 2`), every measurable increasing event `E` determined by the edges inside `B_N(z)` and
the pairs off the edges, and all `m, n ≥ n₀`,
`|P(E | z ↔ ∂B_m(z)) - P(E | z ↔ ∂B_n(z))| ≤ ε`. -/
theorem exists_abs_toReal_cond_armEvent_sub_le_of_isUpperSet (z : LatticeSite 2) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ E : Set (Config (LatticeSite 2)), IsUpperSet E → MeasurableSet E →
      (∀ ω ω', ω ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
          ∀ v ∈ e, v ∈ Icc (z - (N : LatticeSite 2)) (z + N)} =
        ω' ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
          ∀ v ∈ e, v ∈ Icc (z - (N : LatticeSite 2)) (z + N)} → (ω ∈ E ↔ ω' ∈ E)) →
      ∀ m n, n₀ ≤ m → n₀ ≤ n →
        |(ProbabilityTheory.cond (law q) (armEvent z m) E).toReal -
          (ProbabilityTheory.cond (law q) (armEvent z n) E).toReal| ≤ ε := by
  obtain ⟨κ, hκ, hchain⟩ := exists_chain_of_cuts
  obtain ⟨c₀, hc₀, herr⟩ := exists_law_inter_armEvent_le_add_of_cuts
  -- the contraction factor of one matrix
  have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hθ0 : 0 ≤ (κ ^ 2 - 1) / (κ ^ 2 + 1) := div_nonneg (by linarith) (by linarith)
  have hθ1 : (κ ^ 2 - 1) / (κ ^ 2 + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨S, hS⟩ := exists_pow_lt_of_lt_one (half_pos hε) hθ1
  -- the failure rate of one cut
  have hρ0 : 0 ≤ (1 - c₀).toReal := ENNReal.toReal_nonneg
  have hρ1 : (1 - c₀).toReal < 1 := by
    have h : 1 - c₀ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc₀.ne'
    have := (ENNReal.toReal_lt_toReal (h.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).2 h
    rwa [ENNReal.toReal_one] at this
  have hη : 0 < min (ε / (16 * (S + 1))) (1 / (4 * (S + 1))) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hη hρ1
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (S + 1) * (2 * (1 - c₀).toReal ^ K) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hK₁' : (1 - c₀).toReal ^ K < ε / (16 * (S + 1)) := hK.trans_le (min_le_left _ _)
  have hK₂' : (1 - c₀).toReal ^ K < 1 / (4 * (S + 1)) := hK.trans_le (min_le_right _ _)
  have hS1 : (0 : ℝ) < S + 1 := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδ]
    have := (lt_div_iff₀ (by positivity)).1 hK₂'
    nlinarith
  have hδε : 4 * δ ≤ ε / 2 := by
    rw [hδ]
    have := (lt_div_iff₀ (by positivity)).1 hK₁'
    nlinarith
  -- the radii of the cuts
  obtain ⟨a, ha0, has⟩ : ∃ a : ℕ → ℕ, a 0 = N + 2 ∧
      ∀ k, a (k + 1) = 4 * (4 ^ K * (4 ^ K * a k + 1) + 2) + 2 :=
    ⟨fun k => Nat.rec (N + 2) (fun _ x => 4 * (4 ^ K * (4 ^ K * x + 1) + 2) + 2) k, rfl,
      fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, ∀ k, c k = 4 ^ K * a k + 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ k, b k = 4 ^ K * c k + 1 := ⟨_, fun _ => rfl⟩
  have h4K : 0 < 4 ^ K := by positivity
  have ha1 : ∀ k, 1 ≤ a k := fun k => by
    cases k with
    | zero => omega
    | succ k => rw [has k]; omega
  have hac : ∀ k, a k < c k := fun k => by
    have := Nat.le_mul_of_pos_left (a k) h4K
    rw [hc k]
    omega
  have hcb : ∀ k, c k < b k := fun k => by
    have := Nat.le_mul_of_pos_left (c k) h4K
    rw [hb k]
    omega
  have hgap : ∀ k, 4 * (b k + 1) + 2 ≤ a (k + 1) := fun k =>
    le_of_eq (by rw [has k, hb k, hc k])
  have hK₁ : ∀ k, 4 ^ K * a k ≤ c k := fun k => by rw [hc k]; exact Nat.le_succ _
  have hK₂ : ∀ k, 4 ^ K * c k ≤ b k := fun k => by rw [hb k]; exact Nat.le_succ _
  have hbmono : Monotone b := monotone_nat_of_le_succ fun k => by
    have := hgap k
    have := hac (k + 1)
    have := hcb (k + 1)
    omega
  refine ⟨b S + 1, fun q hq E hEu hEm hE m n hm hn => ?_⟩
  have hE' : ∀ ω ω', ω ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
      ∀ v ∈ e, v ∈ Icc (z - (a 0 : LatticeSite 2) + 1) (z + a 0 - 1)} =
      ω' ∩ {e | e ∉ (zdGraph 2).edgeSet ∨
      ∀ v ∈ e, v ∈ Icc (z - (a 0 : LatticeSite 2) + 1) (z + a 0 - 1)} → (ω ∈ E ↔ ω' ∈ E) :=
    fun ω ω' h => hE ω ω' (inter_eq_inter_of_inter_eq_of_subset h fun e he => by
      rcases he with he | he
      · exact Or.inl he
      · refine Or.inr fun v hv => ?_
        have := he v hv
        rw [ha0]
        rw [mem_Icc_two_iff] at this ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
        push_cast
        omega)
  obtain ⟨T, M, u', u'', hM, hu'0, hu', hw⟩ :=
    hchain q hq z a c b (by rw [ha0]; omega) hac hcb hgap S E hEm hE'
  obtain ⟨Good, hGood⟩ : ∃ Good : Set (Config (LatticeSite 2)), Good = {ω | ∀ k ≤ S,
      ∀ x ∈ boxBoundary (z - (a k : LatticeSite 2)) (z + a k),
        ∀ m ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
        ∀ m' ∈ boxBoundary (z - (c k : LatticeSite 2)) (z + c k),
        ∀ y ∈ boxBoundary (z - (b k : LatticeSite 2)) (z + b k),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (c k : LatticeSite 2)) (z + c k) \
            Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x m →
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
            Icc (z - (c k : LatticeSite 2) + 1) (z + c k - 1)) m' y →
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b k : LatticeSite 2)) (z + b k) \
            Icc (z - (a k : LatticeSite 2) + 1) (z + a k - 1)) x y} := ⟨_, rfl⟩
  rw [← hGood] at hw
  obtain ⟨wm, hwm, hwmS, hPm, hQm⟩ := hw m (by omega)
  obtain ⟨wn, hwn, hwnS, hPn, hQn⟩ := hw n (by omega)
  -- the error of the decomposition
  have hδ' : (((S + 1 : ℕ) : ℝ≥0∞) * (2 * (1 - c₀) ^ K)).toReal = δ := by
    rw [hδ, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
    push_cast
    ring
  have key : ∀ E' : Set (Config (LatticeSite 2)), IsUpperSet E' → MeasurableSet E' →
      ∀ r, b S < r → (law q (E' ∩ armEvent z r)).toReal ≤
        (law q (E' ∩ armEvent z r ∩ Good)).toReal + δ * (law q (E' ∩ armEvent z r)).toReal := by
    intro E' hu hm' r hr
    have h := herr q hq E' hu hm' z a c b S K r ha1 hac hcb hK₁ hK₂
      fun k hk => lt_of_le_of_lt (hbmono hk) hr
    rw [← hGood] at h
    have hfin : ((S + 1 : ℕ) : ℝ≥0∞) * (2 * (1 - c₀) ^ K) * law q (E' ∩ armEvent z r) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top
          (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)))) (measure_ne_top _ _)
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hfin⟩) h
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hfin, ENNReal.toReal_mul, hδ'] at h'
  have hbound : ∀ r, b S < r →
      |(law q (E ∩ armEvent z r)).toReal / (law q (armEvent z r)).toReal -
        (law q (E ∩ armEvent z r ∩ Good)).toReal / (law q (armEvent z r ∩ Good)).toReal| ≤
        2 * δ := by
    intro r hr
    have h₁ := key E hEu hEm r hr
    have h₂ := key univ isUpperSet_univ MeasurableSet.univ r hr
    simp only [univ_inter] at h₂
    refine abs_div_sub_div_le_two_mul ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_right))
      (ENNReal.toReal_pos (law_armEvent_pos hq z r).ne' (measure_ne_top _ _)) hδ0 hδ2
      (by linarith) (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_left))
      (by linarith) (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_left))
  have hQpos : ∀ r, b S < r → 0 < (law q (armEvent z r ∩ Good)).toReal := by
    intro r hr
    have h₂ := key univ isUpperSet_univ MeasurableSet.univ r hr
    simp only [univ_inter] at h₂
    have hB := ENNReal.toReal_pos (law_armEvent_pos hq z r).ne' (measure_ne_top _ _)
    nlinarith
  have hcontr := abs_ratio_sub_ratio_le_of_crossRatio_of_backward M hM hu'0 hu' hwm hwn hwmS
    hwnS (by rw [hQm]; exact hQpos m (by omega)) (by rw [hQn]; exact hQpos n (by omega))
  rw [hPm, hQm, hPn, hQn] at hcontr
  rw [toReal_cond_armEvent, toReal_cond_armEvent]
  have hbm := hbound m (by omega)
  have hbn := hbound n (by omega)
  rw [abs_sub_comm] at hbn
  calc _ ≤ |(law q (E ∩ armEvent z m)).toReal / (law q (armEvent z m)).toReal -
          (law q (E ∩ armEvent z m ∩ Good)).toReal / (law q (armEvent z m ∩ Good)).toReal| +
        |(law q (E ∩ armEvent z m ∩ Good)).toReal / (law q (armEvent z m ∩ Good)).toReal -
          (law q (E ∩ armEvent z n)).toReal / (law q (armEvent z n)).toReal| := abs_sub_le _ _ _
    _ ≤ 2 * δ + (((κ ^ 2 - 1) / (κ ^ 2 + 1)) ^ S + 2 * δ) := by
        refine add_le_add hbm ((abs_sub_le _ _ _).trans (add_le_add hcontr hbn))
    _ ≤ ε := by linarith

/-- Every finite set of pairs of `ℤ²` lies inside some box around `z`. -/
theorem exists_forall_mem_Icc_of_finset (z : LatticeSite 2) (F : Finset (Sym2 (LatticeSite 2))) :
    ∃ N : ℕ, ∀ e ∈ F, ∀ v ∈ e, v ∈ Icc (z - (N : LatticeSite 2)) (z + N) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert e F he ih =>
    obtain ⟨N, hN⟩ := ih
    induction e using Sym2.ind with
    | h u w =>
      refine ⟨N + (u 0 - z 0).natAbs + (u 1 - z 1).natAbs + (w 0 - z 0).natAbs +
        (w 1 - z 1).natAbs, fun e' he' v hv => ?_⟩
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      rcases Finset.mem_insert.1 he' with rfl | he'
      · rcases Sym2.mem_iff.1 hv with rfl | rfl
        · omega
        · omega
      · have := hN e' he' v hv
        rw [mem_Icc_two_iff] at this
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this
        omega

/-- **The uniform Cauchy property** (Basu–Sapozhnikov (2.1) on `ℤ²`; arms plan §4.2, step 5).
For every centre `z`, every finite set `F` of pairs and every `ε > 0` there is `n₀` such that for
every profile opening each edge with probability at least `1/2` (in particular
`p = 1 - e^{-β}` on the edges, `β ≥ log 2`), every event `A` determined by `F` and all
`m, n ≥ n₀`, `|P(A | z ↔ ∂B_m(z)) - P(A | z ↔ ∂B_n(z))| ≤ ε`. Inclusion–exclusion writes
`P(A | ·)` as a combination of the probabilities of the all-open events `{S ⊆ ω}`, `S ⊆ F`, with
coefficients at most `2^{|F|}` in absolute value; these events are increasing. -/
theorem exists_abs_toReal_cond_armEvent_sub_le (z : LatticeSite 2)
    (F : Finset (Sym2 (LatticeSite 2))) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ A : Set (Config (LatticeSite 2)), (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
      ∀ m n, n₀ ≤ m → n₀ ≤ n →
        |(ProbabilityTheory.cond (law q) (armEvent z m) A).toReal -
          (ProbabilityTheory.cond (law q) (armEvent z n) A).toReal| ≤ ε := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_mem_Icc_of_finset z F
  have h4 : (0 : ℝ) < 4 ^ F.card := by positivity
  obtain ⟨n₀, hn₀⟩ := exists_abs_toReal_cond_armEvent_sub_le_of_isUpperSet z N (div_pos hε h4)
  refine ⟨n₀, fun q hq A hA m n hm hn => ?_⟩
  have : IsProbabilityMeasure (ProbabilityTheory.cond (law q) (armEvent z m)) :=
    ProbabilityTheory.cond_isProbabilityMeasure (law_armEvent_pos hq z m).ne'
  have : IsProbabilityMeasure (ProbabilityTheory.cond (law q) (armEvent z n)) :=
    ProbabilityTheory.cond_isProbabilityMeasure (law_armEvent_pos hq z n).ne'
  -- the all-open events
  have hS : ∀ S ∈ F.powerset,
      |(ProbabilityTheory.cond (law q) (armEvent z m)).real
          {ω | (S : Set (Sym2 (LatticeSite 2))) ⊆ ω} -
        (ProbabilityTheory.cond (law q) (armEvent z n)).real
          {ω | (S : Set (Sym2 (LatticeSite 2))) ⊆ ω}| ≤ ε / 4 ^ F.card := by
    intro S hS
    rw [measureReal_def, measureReal_def]
    refine hn₀ q hq _ (fun ω ω' h hSω => hSω.trans h) (measurableSet_setOf_finset_coe_subset S)
      ?_ m n hm hn
    intro ω ω' h
    have hSQ : (↑S : Set (Sym2 (LatticeSite 2))) ⊆ {e | e ∉ (zdGraph 2).edgeSet ∨
        ∀ v ∈ e, v ∈ Icc (z - (N : LatticeSite 2)) (z + N)} :=
      fun e he => Or.inr (hN e (Finset.mem_powerset.1 hS (Finset.mem_coe.1 he)))
    have h₁ := inter_eq_inter_of_inter_eq_of_subset h hSQ
    simp only [mem_ofPred_eq]
    rw [← inter_eq_right, h₁, inter_eq_right]
  -- the coefficients of inclusion–exclusion
  have hc : ∀ S ∈ F.powerset, |∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
      A.indicator 1 (T : Set (Sym2 (LatticeSite 2)))| ≤ 2 ^ F.card := by
    intro S hSF
    calc |∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
          A.indicator 1 (T : Set (Sym2 (LatticeSite 2)))|
        ≤ ∑ T ∈ S.powerset, |(-1 : ℝ) ^ (S.card - T.card) *
          A.indicator 1 (T : Set (Sym2 (LatticeSite 2)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ S.powerset, (1 : ℝ) := Finset.sum_le_sum fun T _ => by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          by_cases hT : (T : Set (Sym2 (LatticeSite 2))) ∈ A
          · rw [Set.indicator_of_mem hT]
            simp
          · rw [Set.indicator_of_notMem hT]
            simp
      _ = 2 ^ S.card := by
          rw [Finset.sum_const, Finset.card_powerset]
          simp
      _ ≤ 2 ^ F.card :=
          pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.mem_powerset.1 hSF))
  rw [← measureReal_def, ← measureReal_def,
    measureReal_eq_sum_subset_of_determined (ProbabilityTheory.cond (law q) (armEvent z m)) hA,
    measureReal_eq_sum_subset_of_determined (ProbabilityTheory.cond (law q) (armEvent z n)) hA,
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ S ∈ F.powerset, |(∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
          A.indicator 1 (T : Set (Sym2 (LatticeSite 2)))) *
          (ProbabilityTheory.cond (law q) (armEvent z m)).real
            {ω | (S : Set (Sym2 (LatticeSite 2))) ⊆ ω} -
        (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
          A.indicator 1 (T : Set (Sym2 (LatticeSite 2)))) *
          (ProbabilityTheory.cond (law q) (armEvent z n)).real
            {ω | (S : Set (Sym2 (LatticeSite 2))) ⊆ ω}| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ F.powerset, (2 : ℝ) ^ F.card * (ε / 4 ^ F.card) :=
        Finset.sum_le_sum fun S hSF => by
          rw [← mul_sub, abs_mul]
          exact mul_le_mul (hc S hSF) (hS S hSF) (abs_nonneg _) (by positivity)
    _ = ε := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
          show (4 : ℝ) ^ F.card = 2 ^ F.card * 2 ^ F.card by rw [← mul_pow]; norm_num]
        push_cast
        field_simp

end PercLib.Models.Planar

/-! ### Cylinder events: intersections, continuity, events of the pairs inside a finite set -/

namespace PercLib.Probability

variable {ι : Type*}

/-- **Intersections of cylinder events.** If `A` is determined by the finite set `F` and `B` by
`G`, then `A ∩ B` is determined by `F ∪ G`. -/
theorem mem_inter_iff_inter_union_mem_of_determined [DecidableEq ι] {F G : Finset ι}
    {A B : Set (Set ι)} (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) (hB : ∀ ω, ω ∈ B ↔ ω ∩ ↑G ∈ B)
    (ω : Set ι) : ω ∈ A ∩ B ↔ ω ∩ ↑(F ∪ G) ∈ A ∩ B := by
  have hF : ω ∩ ↑(F ∪ G) ∩ ↑F = ω ∩ ↑F := by
    rw [inter_assoc, Finset.coe_union, union_inter_cancel_left]
  have hG : ω ∩ ↑(F ∪ G) ∩ ↑G = ω ∩ ↑G := by
    rw [inter_assoc, Finset.coe_union, union_inter_cancel_right]
  rw [mem_inter_iff, mem_inter_iff, hA ω, hB ω, hA (ω ∩ ↑(F ∪ G)), hB (ω ∩ ↑(F ∪ G)), hF, hG]

/-- **Cylinder probabilities are continuous in the profile.** The probability of an event
determined by a finite set of coordinates is a continuous function of the profile, for the
product topology. -/
theorem continuous_prodBernoulli_of_determined {F : Finset ι} {A : Set (Set ι)}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) :
    Continuous fun p : ι → unitInterval => prodBernoulli p A := by
  have hset : {ω : Set ι | (Subtype.val ⁻¹' ω : Set F) ∈ {η : Set F | Subtype.val '' η ∈ A}} =
      A := by
    ext ω
    have h : Subtype.val '' (Subtype.val ⁻¹' ω : Set F) = ω ∩ ↑F := by
      ext x
      simp [and_comm]
    simp only [mem_ofPred_eq, h]
    exact (hA ω).symm
  have hc := continuous_prodBernoulli_cylinder F {η : Set F | Subtype.val '' η ∈ A}
  rwa [hset] at hc

end PercLib.Probability

namespace PercLib.Percolation.Bond

/-- **Events of the pairs inside a finite set are cylinder events.** An event determined by the
pairs with both ends in the finite set `T` is determined by the finite set `T.sym2` of these
pairs. -/
theorem mem_iff_inter_sym2_mem_of_determined {V : Type*} {T : Finset V} {E : Set (Config V)}
    (hE : ∀ ω ω' : Config V, ω ∩ {e | ∀ v ∈ e, v ∈ (T : Set V)} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ (T : Set V)} → (ω ∈ E ↔ ω' ∈ E)) (ω : Config V) :
    ω ∈ E ↔ ω ∩ ↑T.sym2 ∈ E := by
  have hT : (↑T.sym2 : Set (Sym2 V)) = {e | ∀ v ∈ e, v ∈ (T : Set V)} := by
    ext e
    simp only [Finset.mem_coe, Finset.mem_sym2_iff, mem_ofPred_eq]
  refine hE ω _ ?_
  rw [hT, inter_assoc, inter_self]

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

open Filter Topology
open scoped NNReal ProbabilityTheory

/-! ### The infinite cluster and the arm events -/

/-- **The arm event is a cylinder event.** `z ↔ ∂B_n(z)` is determined by the finite set of pairs
inside the box `B_n(z)`. -/
theorem mem_armEvent_iff_inter_sym2_mem {d : ℕ} (z : LatticeSite d) (n : ℕ)
    (ω : Config (LatticeSite d)) :
    ω ∈ armEvent z n ↔
      ω ∩ ↑(Finset.Icc (z - (n : LatticeSite d)) (z + n)).sym2 ∈ armEvent z n :=
  mem_iff_inter_sym2_mem_of_determined
    (fun _ _ h => mem_armEvent_iff_of_inter_eq (Finset.coe_Icc _ _).ge h) ω

/-- **The infinite cluster as a limit of arm events.** The open cluster of `x` is infinite exactly
when `x ↔ ∂B_{r + 1}(x)` for every `r`: an infinite cluster leaves every box, and a finite one
lies in some box. -/
theorem setOf_cluster_infinite_eq_iInter_armEvent {d : ℕ} (x : LatticeSite d) :
    {ω : Config (LatticeSite d) | (cluster (ω ∩ (zdGraph d).edgeSet) x).Infinite} =
      ⋂ r : ℕ, armEvent x (r + 1) := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter]
  constructor
  · intro h r
    obtain ⟨y, hy, hyB⟩ := h.exists_notMem_finite (finite_Icc
      (x - ((r + 1 : ℕ) : LatticeSite d) + 1) (x + ((r + 1 : ℕ) : LatticeSite d) - 1))
    exact mem_armEvent_iff_exists_notMem_conn.2 ⟨y, hyB, hy⟩
  · intro h hfin
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hfin.isBounded
    obtain ⟨y, hy, hc⟩ := mem_armEvent_iff_exists_notMem_conn.1 (h ⌈R⌉₊)
    have h₁ : y ∈ Metric.closedBall x (⌈R⌉₊ : ℝ) :=
      Metric.closedBall_subset_closedBall (Nat.le_ceil R) (hR hc)
    rw [closedBall_eq_Icc] at h₁
    refine hy ?_
    have e₁ : x - ((⌈R⌉₊ + 1 : ℕ) : LatticeSite d) + 1 = x - (⌈R⌉₊ : LatticeSite d) := by
      push_cast
      ring
    have e₂ : x + ((⌈R⌉₊ + 1 : ℕ) : LatticeSite d) - 1 = x + (⌈R⌉₊ : LatticeSite d) := by
      push_cast
      ring
    rw [e₁, e₂]
    exact h₁

/-- The event that the open cluster of `x` is infinite is measurable. -/
theorem measurableSet_setOf_cluster_inter_edgeSet_infinite {d : ℕ} (x : LatticeSite d) :
    MeasurableSet
      {ω : Config (LatticeSite d) | (cluster (ω ∩ (zdGraph d).edgeSet) x).Infinite} := by
  rw [setOf_cluster_infinite_eq_iInter_armEvent]
  exact MeasurableSet.iInter fun r => measurableSet_armEvent x (r + 1)

/-- **Conditioning on the infinite cluster as a limit** (continuity from above along the arm
events). For every profile under which the open cluster of `z` is infinite with positive
probability and every measurable event `A`, `P(A | z ↔ ∂B_n(z)) → P(A | |K_z| = ∞)`. -/
theorem tendsto_cond_armEvent_cond_setOf_cluster_infinite {d : ℕ}
    (q : Sym2 (LatticeSite d) → unitInterval) (z : LatticeSite d)
    (hpos : law q {ω | (cluster (ω ∩ (zdGraph d).edgeSet) z).Infinite} ≠ 0)
    {A : Set (Config (LatticeSite d))} (hA : MeasurableSet A) :
    Tendsto (fun n => (law q)[A | armEvent z n]) atTop
      (𝓝 ((law q)[A | {ω | (cluster (ω ∩ (zdGraph d).edgeSet) z).Infinite}])) := by
  have hK := setOf_cluster_infinite_eq_iInter_armEvent z
  have hanti : Antitone fun r : ℕ => armEvent z (r + 1) :=
    fun r s h => armEvent_anti z (Nat.add_le_add_right h 1)
  have h₁ : Tendsto (fun r : ℕ => law q (armEvent z (r + 1))) atTop
      (𝓝 (law q {ω | (cluster (ω ∩ (zdGraph d).edgeSet) z).Infinite})) := by
    rw [hK]
    exact tendsto_measure_iInter_atTop
      (fun r => (measurableSet_armEvent z (r + 1)).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
  have h₂ : Tendsto (fun r : ℕ => law q (armEvent z (r + 1) ∩ A)) atTop
      (𝓝 (law q ({ω | (cluster (ω ∩ (zdGraph d).edgeSet) z).Infinite} ∩ A))) := by
    rw [hK, iInter_inter]
    exact tendsto_measure_iInter_atTop
      (fun r => ((measurableSet_armEvent z (r + 1)).inter hA).nullMeasurableSet)
      (fun r s h => inter_subset_inter_left _ (hanti h)) ⟨0, measure_ne_top _ _⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [ProbabilityTheory.cond_apply (measurableSet_armEvent z _),
    ProbabilityTheory.cond_apply (measurableSet_setOf_cluster_inter_edgeSet_infinite z)]
  exact ENNReal.Tendsto.mul (tendsto_inv_iff.2 h₁) (Or.inr (measure_ne_top _ _)) h₂
    (Or.inr (ENNReal.inv_ne_top.2 hpos))

/-! ### The intensities `β ≥ log 2` -/

/-- **The profiles of the intensities `β ≥ log 2`.** At intensity `β ≥ log 2` every edge of `ℤ²` is
open with probability `1 - e^{-β} ≥ 1/2`. -/
theorem half_le_intensityProfile_indicator_edgeSet {β : ℝ≥0} (hβ : Real.log 2 ≤ β)
    {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    (1 / 2 : ℝ) ≤ intensityProfile ((zdGraph 2).edgeSet.indicator 1) β e := by
  have hle : (Real.log 2).toNNReal ≤ β := Real.toNNReal_le_iff_le_coe.2 hβ
  rw [← intensityProfile_indicator_edgeSet_log_two he]
  exact intensityProfile_mono _ hle e

/-- **Percolation above `log 2`, nearest-neighbour edges.** At intensity `β > log 2` the cluster
of every vertex in the open nearest-neighbour edges is infinite with positive probability. -/
theorem law_setOf_cluster_inter_edgeSet_infinite_pos {β : ℝ≥0} (hβ : Real.log 2 < β)
    (x : LatticeSite 2) :
    0 < law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)
      {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} := by
  have h₀ : ∀ e, e ∉ (zdGraph 2).edgeSet →
      intensityProfile ((zdGraph 2).edgeSet.indicator 1) β e = 0 := fun e he =>
    Subtype.ext (by simp [intensityProfile, indicator_of_notMem he])
  have hae : {ω : Config (LatticeSite 2) | (cluster ω x).Infinite} =ᵐ[law
      (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)]
      {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite} := by
    filter_upwards [ae_config_subset_host (zdGraph 2) _ h₀] with ω hω
    rw [inter_eq_left.2 hω]
  rw [← measure_congr hae]
  exact law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt hβ x

/-- **Conditional arm probabilities are continuous in the profile.** For a continuous family of
profiles that are at least `1/2` on the edges on a set `s`, `P(A | z ↔ ∂B_n(z))` is continuous on
`s` for every cylinder event `A` (both probabilities are cylinder probabilities, and the
denominator is positive). -/
theorem continuousOn_toReal_cond_armEvent {X : Type*} [TopologicalSpace X]
    {q : X → Sym2 (LatticeSite 2) → unitInterval} (hqc : Continuous q) {s : Set X}
    (hq : ∀ x ∈ s, ∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q x e) (z : LatticeSite 2) (n : ℕ)
    {F : Finset (Sym2 (LatticeSite 2))} {A : Set (Config (LatticeSite 2))}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) :
    ContinuousOn (fun x => ((law (q x))[A | armEvent z n]).toReal) s := by
  classical
  have hB := mem_armEvent_iff_inter_sym2_mem z n
  have hAB := mem_inter_iff_inter_union_mem_of_determined hA hB
  have hnum : Continuous fun x => (law (q x) (A ∩ armEvent z n)).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous
      ((continuous_prodBernoulli_of_determined hAB).comp hqc) fun x => measure_ne_top _ _
  have hden : Continuous fun x => (law (q x) (armEvent z n)).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous
      ((continuous_prodBernoulli_of_determined hB).comp hqc) fun x => measure_ne_top _ _
  simp_rw [toReal_cond_armEvent]
  exact hnum.continuousOn.div hden.continuousOn fun x hx =>
    (ENNReal.toReal_pos (law_armEvent_pos (hq x hx) z n).ne' (measure_ne_top _ _)).ne'

/-! ### The first limit -/

/-- **The first limit** (Kesten; Basu–Sapozhnikov (2.1) on `ℤ²`). For every profile at least
`1/2` on the edges, every centre `z` and every cylinder event `A`, `P(A | z ↔ ∂B_n(z))` converges
as `n → ∞`. -/
theorem exists_tendsto_cond_armEvent {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) (z : LatticeSite 2)
    {F : Finset (Sym2 (LatticeSite 2))} {A : Set (Config (LatticeSite 2))}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) :
    ∃ l, Tendsto (fun n => (law q)[A | armEvent z n]) atTop (𝓝 l) := by
  have hc : CauchySeq fun n => ((law q)[A | armEvent z n]).toReal := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨n₀, hn₀⟩ := exists_abs_toReal_cond_armEvent_sub_le z F (half_pos hε)
    refine ⟨n₀, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact (hn₀ q hq A hA n n₀ hn le_rfl).trans_lt (half_lt_self hε)
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨ENNReal.ofReal l, (ENNReal.tendsto_ofReal hl).congr fun n =>
    ENNReal.ofReal_toReal (measure_ne_top _ _)⟩

/-- **The first limit is uniform in the profile.** For every centre `z`, every finite set `F` of
pairs and every `ε > 0` there is `n₀` such that for every profile at least `1/2` on the edges
(in particular `p = 1 - e^{-β}` on the edges, `β ≥ log 2`) and every event `A` determined by `F`,
`P(A | z ↔ ∂B_n(z))` lies within `ε` of its limit for all `n ≥ n₀`. -/
theorem exists_abs_toReal_cond_armEvent_sub_toReal_le (z : LatticeSite 2)
    (F : Finset (Sym2 (LatticeSite 2))) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ A : Set (Config (LatticeSite 2)), (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
      ∀ l : ℝ≥0∞, Tendsto (fun n => (law q)[A | armEvent z n]) atTop (𝓝 l) →
      ∀ n, n₀ ≤ n → |((law q)[A | armEvent z n]).toReal - l.toReal| ≤ ε := by
  obtain ⟨n₀, hn₀⟩ := exists_abs_toReal_cond_armEvent_sub_le z F hε
  refine ⟨n₀, fun q hq A hA l hl n hn => ?_⟩
  have hlt : l ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_tendsto' hl fun m => prob_le_one)
  have hl' : Tendsto (fun m => ((law q)[A | armEvent z m]).toReal) atTop (𝓝 l.toReal) :=
    (ENNReal.tendsto_toReal hlt).comp hl
  refine le_of_tendsto ((tendsto_const_nhds.sub hl').abs) ?_
  filter_upwards [eventually_ge_atTop n₀] with m hm
  exact hn₀ q hq A hA n m hn hm

/-! ### The law `ν` -/

/-- **The limit law** (Kesten). For every profile at least `1/2` on the edges and every centre `z`,
the conditional laws given `z ↔ ∂B_n(z)` converge on every cylinder event to a probability law
`ν`. -/
theorem exists_measure_tendsto_cond_armEvent {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) (z : LatticeSite 2) :
    ∃ ν : Measure (Config (LatticeSite 2)), IsProbabilityMeasure ν ∧
      ∀ (F : Finset (Sym2 (LatticeSite 2))) (A : Set (Config (LatticeSite 2))),
        (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
        Tendsto (fun n => (law q)[A | armEvent z n]) atTop (𝓝 (ν A)) := by
  have hP : ∀ n, IsProbabilityMeasure ((law q)[|armEvent z n]) :=
    fun n => ProbabilityTheory.cond_isProbabilityMeasure (law_armEvent_pos hq z n).ne'
  exact exists_measure_of_tendsto_cylinder (fun n => (law q)[|armEvent z n])
    fun F A hA => exists_tendsto_cond_armEvent hq z hA

/-! ### Continuity in the intensity and the second limit -/

/-- **The limit is continuous in the profile.** For a continuous family of profiles that are at
least `1/2` on the edges on a set `s` and every cylinder event `A`, the limit of
`P(A | z ↔ ∂B_n(z))` as `n → ∞` is continuous on `s`: by the uniform first limit it is a uniform
limit of continuous functions. In particular `β ↦ lim_n P_β(A | z ↔ ∂B_n(z))` is continuous on
`β ≥ log 2` (`continuous_intensityProfile_pi`). -/
theorem continuousOn_toReal_of_tendsto_cond_armEvent {X : Type*} [TopologicalSpace X]
    {q : X → Sym2 (LatticeSite 2) → unitInterval} (hqc : Continuous q) {s : Set X}
    (hq : ∀ x ∈ s, ∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q x e) (z : LatticeSite 2)
    {F : Finset (Sym2 (LatticeSite 2))} {A : Set (Config (LatticeSite 2))}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) {l : X → ℝ≥0∞}
    (hl : ∀ x ∈ s, Tendsto (fun n => (law (q x))[A | armEvent z n]) atTop (𝓝 (l x))) :
    ContinuousOn (fun x => (l x).toReal) s := by
  refine TendstoUniformlyOn.continuousOn
    (F := fun n x => ((law (q x))[A | armEvent z n]).toReal) ?_
    (Eventually.of_forall (f := (atTop : Filter ℕ)) fun n =>
      continuousOn_toReal_cond_armEvent hqc hq z n hA).frequently
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  obtain ⟨n₀, hn₀⟩ := exists_abs_toReal_cond_armEvent_sub_toReal_le z F (half_pos hε)
  filter_upwards [eventually_ge_atTop n₀] with n hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (hn₀ _ (hq x hx) A hA _ (hl x hx) n hn).trans_lt (half_lt_self hε)

/-- **The second limit** (Kesten). For every centre `z` and every cylinder event `A`, if
`P_{log 2}(A | z ↔ ∂B_n(z)) → l`, then `P_β(A | |K_z| = ∞) → l` as `β ↓ log 2`; here `P_β` is
nearest-neighbour bond percolation on `ℤ²` at intensity `β` (`p = 1 - e^{-β}` on the edges, `0`
off them). For `β > log 2`, `P_β(A | |K_z| = ∞)` is the limit of `P_β(A | z ↔ ∂B_n(z))`
(continuity from above, since `|K_z| = ∞` has positive probability), and the limit is continuous
in `β ≥ log 2`. -/
theorem tendsto_cond_setOf_cluster_infinite_nhdsGT (z : LatticeSite 2)
    {F : Finset (Sym2 (LatticeSite 2))} {A : Set (Config (LatticeSite 2))}
    (hA : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) {l : ℝ≥0∞}
    (hl : Tendsto (fun n => (law (intensityProfile ((zdGraph 2).edgeSet.indicator 1)
      ⟨Real.log 2, (Real.log_pos one_lt_two).le⟩))[A | armEvent z n]) atTop (𝓝 l)) :
    Tendsto (fun β : ℝ≥0 => (law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β))[A |
        {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) z).Infinite}])
      (𝓝[>] ⟨Real.log 2, (Real.log_pos one_lt_two).le⟩) (𝓝 l) := by
  classical
  set β₀ : ℝ≥0 := ⟨Real.log 2, (Real.log_pos one_lt_two).le⟩ with hβ₀
  have hq : ∀ β ∈ Ici β₀, ∀ e ∈ (zdGraph 2).edgeSet,
      (1 / 2 : ℝ) ≤ intensityProfile ((zdGraph 2).edgeSet.indicator 1) β e :=
    fun β hβ e he => half_le_intensityProfile_indicator_edgeSet (NNReal.coe_le_coe.2 hβ) he
  have hAm : MeasurableSet A := measurableSet_of_determined_finset hA
  have hlt : l ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_tendsto' hl fun n => prob_le_one)
  -- the limits for `β ≥ log 2`: `l` at `log 2`, `P_β(A | |K_z| = ∞)` above it
  have hl' : ∀ β ∈ Ici β₀, Tendsto
      (fun n => (law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β))[A | armEvent z n])
      atTop (𝓝 (if β = β₀ then l else
        (law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β))[A |
          {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) z).Infinite}])) := by
    intro β hβ
    by_cases h : β = β₀
    · rw [ite_eq_left h, h]
      exact hl
    · rw [ite_eq_right h]
      have hβ' : β₀ < β := lt_of_le_of_ne hβ (Ne.symm h)
      exact tendsto_cond_armEvent_cond_setOf_cluster_infinite _ z
        (law_setOf_cluster_inter_edgeSet_infinite_pos (NNReal.coe_lt_coe.2 hβ') z).ne' hAm
  have hc := (continuousOn_toReal_of_tendsto_cond_armEvent
    (continuous_intensityProfile_pi ((zdGraph 2).edgeSet.indicator 1)) hq z hA hl' β₀
    self_mem_Ici).tendsto
  rw [ite_eq_left (rfl : β₀ = β₀)] at hc
  refine (ENNReal.tendsto_toReal_iff (fun β => measure_ne_top _ _) hlt).1
    ((hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with β hβ
  rw [ite_eq_right (ne_of_gt (mem_Ioi.1 hβ))]

end PercLib.Models.Planar
