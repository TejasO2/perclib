/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.5 (quasi-multiplicativity, Proposition 17).
-/
module

public import PercLib.Models.Planar.Arms.InnerSeparation
public import PercLib.Models.Planar.Arms.OuterArmSeparation

/-!
# The far inner family and its bins

The inner separation step (`exists_inner_separating_event`) excludes, on its good event, arms of
either colour from the box of radius `N` about a corner of `B_ρ(z)` to the boundary of the box of
radius `ρ` about it. Every arm of a family from `B_ρ(z)` to a far boundary therefore starts at
least `N + 1` from the ends of its side. This file records that property in the probability form
of the inner step, covers the starts by bins of a fixed width on the four sides, and reads off the
side, the coordinate along the side and the inner position of an arm starting in a bin, in the
integer form that the motion plan and the two-sided gluing consume
(`exists_pos_mul_le_law_of_plan_two_sided`).

## Main results

* `exists_law_multiArmEvent_diff_far_le`: the inner separation step, probability form, with the
  starts far from the corners: `P(A(ρ, R) \ far separated family) ≤ δ P(A(2ρ + 1, R))`.
* `far_of_isArm`: an arm starting in no corner zone has its start at least `N + 1` from the ends
  of its side.
* `exists_bin`, `exists_mem_bin`, `exists_bin_assignment`: every start lies in one of `NB` bins on
  one of the four sides.
* `exists_side_data`: the coordinate of a start in a bin and its inner position.
* `side_facts_single`, `side_facts_pair`: the margins, gaps and side order of starts in bins, in
  integers.
* `le_abs_sub_of_eq_colour`: inner positions of two arms of one colour are twice as far apart.
* `floor_sqrt_mul_bounds`: the integer scales `⌊√η N⌋` and `⌊η N⌋` for `η ≤ 1 / 256`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)}

/-! ### Starts far from the corners -/

/-- **Far from the corners.** A point `a` of `B_ρ(z)` (an open start) or of the faces touching it
(a dual start) that lies in none of the four corner zones of radius `N` (the boxes `κ ± N`,
enlarged by one face row for a dual start, about the corners `κ` of `B_ρ(z)`) has one coordinate
at least `N + 1` from both ends of its range. -/
theorem far_of_notMem_corner {c : Bool} {z a : LatticeSite 2} {N ρ : ℕ}
    (ha : a ∈ cond c (Icc (z - (ρ : LatticeSite 2)) (z + ρ)) (Icc (z - ρ - 1) (z + ρ)))
    (hκ : ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) →
      a ∉ cond c (Icc (κ - (N : LatticeSite 2)) (κ + N)) (Icc (κ - N - 1) (κ + N))) :
    (z 0 - ρ + N + 1 ≤ a 0 ∧ a 0 + N + 1 ≤ z 0 + ρ) ∨
      (z 1 - ρ + N + 1 ≤ a 1 ∧ a 1 + N + 1 ≤ z 1 + ρ) := by
  have hd : (0 : ℤ) ≤ cond c 0 1 ∧ (cond c 0 1 : ℤ) ≤ 1 := by cases c <;> simp
  have hlo : z 0 - ρ - cond c 0 1 ≤ a 0 ∧ a 0 ≤ z 0 + ρ ∧ z 1 - ρ - cond c 0 1 ≤ a 1 ∧
      a 1 ≤ z 1 + ρ := by
    cases c <;> simp only [Bool.cond_true, Bool.cond_false] at ha ⊢ <;>
      rw [mem_Icc_two_iff] at ha <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at ha <;> omega
  have key : ∀ κ0 κ1 : ℤ, (κ0 = z 0 - ρ ∨ κ0 = z 0 + ρ) → (κ1 = z 1 - ρ ∨ κ1 = z 1 + ρ) →
      κ0 - N - cond c 0 1 ≤ a 0 → a 0 ≤ κ0 + N → κ1 - N - cond c 0 1 ≤ a 1 →
      a 1 ≤ κ1 + N → False := by
    intro κ0 κ1 e0 e1 l0 u0 l1 u1
    refine hκ ![κ0, κ1] (by simpa using e0) (by simpa using e1) ?_
    cases c <;> simp only [Bool.cond_true, Bool.cond_false] at l0 l1 ⊢ <;>
      rw [mem_Icc_two_iff] <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  by_contra hcon
  have h0 : a 0 ≤ z 0 - ρ + N ∨ z 0 + ρ - N ≤ a 0 := by omega
  have h1 : a 1 ≤ z 1 - ρ + N ∨ z 1 + ρ - N ≤ a 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact key (z 0 - ρ) (z 1 - ρ) (Or.inl rfl) (Or.inl rfl) (by omega) (by omega) (by omega)
      (by omega)
  · exact key (z 0 - ρ) (z 1 + ρ) (Or.inl rfl) (Or.inr rfl) (by omega) (by omega) (by omega)
      (by omega)
  · exact key (z 0 + ρ) (z 1 - ρ) (Or.inr rfl) (Or.inl rfl) (by omega) (by omega) (by omega)
      (by omega)
  · exact key (z 0 + ρ) (z 1 + ρ) (Or.inr rfl) (Or.inr rfl) (by omega) (by omega) (by omega)
      (by omega)

/-- **Arms start far from the corners** when no arm of their colour runs from the box of radius
`N` about a corner of `B_ρ(z)` to the boundary of the box of radius `ρ` about it: the start of an
arm from `B_ρ(z)` to the boundary of `B_R(z)`, `2ρ + 1 ≤ R`, has one coordinate at least `N + 1`
from both ends of its range. -/
theorem far_of_isArm {c : Bool} {z : LatticeSite 2} {N ρ R : ℕ} {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z ρ (z - R) (z + R) γ) (hR : 2 * ρ + 1 ≤ R)
    (hcor : ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ω ∉ multiArmEvent ![c] κ N ρ) :
    (z 0 - ρ + N + 1 ≤ a 0 ∧ a 0 + N + 1 ≤ z 0 + ρ) ∨
      (z 1 - ρ + N + 1 ≤ a 1 ∧ a 1 + N + 1 ≤ z 1 + ρ) := by
  rw [isArm_iff_cond] at h
  obtain ⟨hc, hE⟩ := h
  refine far_of_notMem_corner hc.start_mem fun κ h0 h1 hmem => hcor κ h0 h1
    (mem_multiArmEvent_one_of_walk γ hE γ.start_mem_support hmem fun hb => hc.end_notMem ?_)
  cases c <;> simp only [Bool.cond_true, Bool.cond_false] at hb ⊢ <;>
    rw [mem_Icc_two_iff] at hb ⊢ <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hb ⊢ <;> omega

/-- **The inner separation step with starts far from the corners** (probability form). Under the
constants of `exists_inner_separating_event` (which also say that the width `w` is odd), for
`2ρ + 1 = wN`, `N₀ ≤ N`, `2ρ + 2 ≤ R` and `ρ ≤ L`: the probability that the `j`-arm event from
`B_ρ(z)` to the boundary of `B_R(z)` occurs but no family of its arms is separated at the inner
boundary (separation `4 √η N`, fences `(⌊√η N⌋, ⌊η N⌋)`) with every start at least `N + 1` from
the ends of its side is at most `δ` times the probability of the `j`-arm event from `B_{2ρ+1}(z)`
to the boundary of `B_R(z)`. -/
theorem exists_law_multiArmEvent_diff_far_le {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 256 ∧ ∃ w N₀ : ℕ, 7 ≤ w ∧ w % 2 = 1 ∧
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞), CrossingBounds q L c →
      ∀ (z : LatticeSite 2) (N ρ R : ℕ), 2 * ρ + 1 = w * N → N₀ ≤ N → 2 * ρ + 2 ≤ R →
      (ρ : ℕ∞) ≤ L →
      law q (multiArmEvent σ z ρ R \ {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z ρ (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsInnerSeparated ω σ z ρ (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ γ ∧
        ∀ i, (z 0 - ρ + N + 1 ≤ a i 0 ∧ a i 0 + N + 1 ≤ z 0 + ρ) ∨
          (z 1 - ρ + N + 1 ≤ a i 1 ∧ a i 1 + N + 1 ≤ z 1 + ρ)}) ≤
        δ * law q (multiArmEvent σ z (2 * ρ + 1) R) := by
  obtain ⟨η, hη, hη1, w, N₀, hw, hwo, hG⟩ := exists_inner_separating_event σ hσ c hδ
  refine ⟨η, hη, hη1, w, N₀, hw, hwo, fun q L h z N ρ R hρ hN hR hρL => ?_⟩
  obtain ⟨G, hGm, hGd, hGl, hGcor, hGsep⟩ := hG q L h z N ρ hρ hN hρL
  have hAm : MeasurableSet (multiArmEvent σ z (2 * ρ + 1) R) := measurableSet_multiArmEvent σ z _ R
  set Q : Set (LatticeSite 2) :=
    Icc (z - ((2 * ρ : ℕ) : LatticeSite 2)) (z + ((2 * ρ : ℕ) : LatticeSite 2)) with hQ
  have hPQ : Disjoint
      {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ Icc (z - (R : LatticeSite 2)) (z + R) \ Q}
      {e | ∀ v ∈ e, v ∈ Q} :=
    Set.disjoint_left.2 fun e heP heQ =>
      (heP _ (Sym2.out_fst_mem e)).2 (heQ _ (Sym2.out_fst_mem e))
  have hind : law q (multiArmEvent σ z (2 * ρ + 1) R ∩ Gᶜ) =
      law q (multiArmEvent σ z (2 * ρ + 1) R) * law q Gᶜ :=
    PercLib.Probability.prodBernoulli_inter_of_determined q hPQ hAm hGm.compl
      (fun ω ω' hωω' => mem_multiArmEventTo_iff_of_inter_eq
        (T := Icc (z - (R : LatticeSite 2)) (z + R) \ Q) (fun v hv => ⟨hv.1, fun hvQ => hv.2 (by
        rw [hQ, mem_Icc_two_iff] at hvQ
        rw [mem_Icc_two_iff]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hvQ ⊢
        push_cast at hvQ ⊢
        omega)⟩) hωω')
      fun ω ω' hωω' => not_congr (hGd ω ω' hωω')
  have hGc : law q Gᶜ ≤ δ := by
    rw [prob_compl_eq_one_sub hGm, tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.1 hGl
  calc _ ≤ law q (multiArmEvent σ z (2 * ρ + 1) R ∩ Gᶜ) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨hA, hnot⟩ := hω
        refine ⟨multiArmEvent_subset_of_le (by omega) le_rfl (by omega) hA, fun hωG => hnot ?_⟩
        obtain ⟨a, b, γ, hγ, hd, ho, hsep⟩ := hGsep R (by omega) ω ⟨hA, hωG⟩
        exact ⟨a, b, γ, hγ, hd, ho, hsep, fun i =>
          far_of_isArm (hγ i) (by omega) fun κ h0 h1 => hGcor ω hωG (σ i) κ h0 h1⟩
    _ = law q (multiArmEvent σ z (2 * ρ + 1) R) * law q Gᶜ := hind
    _ ≤ law q (multiArmEvent σ z (2 * ρ + 1) R) * δ := by gcongr
    _ = δ * law q (multiArmEvent σ z (2 * ρ + 1) R) := mul_comm _ _

/-! ### Bins on the four sides -/

/-- **Bins.** An integer `v` with `0 ≤ v < NB (bw + 1)` lies in one of the `NB` bins
`[g (bw + 1), g (bw + 1) + bw]`. -/
theorem exists_bin {NB bw : ℕ} {v : ℤ} (h0 : 0 ≤ v) (h1 : v < NB * (bw + 1)) :
    ∃ g : Fin NB, ((g : ℕ) : ℤ) * (bw + 1) ≤ v ∧ v ≤ ((g : ℕ) : ℤ) * (bw + 1) + bw := by
  obtain ⟨v', rfl⟩ : ∃ v' : ℕ, v = v' := ⟨v.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hb : 0 < bw + 1 := Nat.succ_pos bw
  have h1' : v' < NB * (bw + 1) := by exact_mod_cast h1
  have hlt : v' / (bw + 1) < NB := by
    rw [Nat.div_lt_iff_lt_mul hb]
    exact h1'
  have e₁ := Nat.div_mul_le_self v' (bw + 1)
  have e₂ := Nat.lt_div_mul_add (a := v') hb
  refine ⟨⟨v' / (bw + 1), hlt⟩, ?_, ?_⟩
  · change (((v' / (bw + 1) : ℕ) : ℤ)) * (bw + 1) ≤ v'
    exact_mod_cast e₁
  · change (v' : ℤ) ≤ ((v' / (bw + 1) : ℕ) : ℤ) * (bw + 1) + bw
    have : v' ≤ v' / (bw + 1) * (bw + 1) + bw := by omega
    exact_mod_cast this

/-- **Every start lies in a bin.** The start of an arm from `B_ρ(z)` lies on one of the four sides
`t` of `B_ρ(z)` (the faces touching it for a dual arm), in one of the `NB` bins of width `bw + 1`
covering the side from its lower (left) end `Z - ρ - 1`, where `Z` is the coordinate of `z` along
the side, when `NB (bw + 1) > 2ρ + 1`. -/
theorem exists_mem_bin {c : Bool} {z lo hi a b : LatticeSite 2} {ρ NB bw : ℕ}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z ρ lo hi γ)
    (hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆ Icc (lo + 1) (hi - 1))
    (hNB : 2 * ρ + 1 < NB * (bw + 1)) :
    ∃ (t : Fin 4) (g : Fin NB),
      (t = 0 ∧ a 1 = z 1 + ρ ∧ z 0 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) ≤ a 0 ∧
        a 0 ≤ z 0 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) + bw) ∨
      (t = 1 ∧ a 0 = z 0 + ρ ∧ z 1 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) ≤ a 1 ∧
        a 1 ≤ z 1 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) + bw) ∨
      (t = 2 ∧ a 1 = z 1 - ρ - cond c 0 1 ∧ z 0 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) ≤ a 0 ∧
        a 0 ≤ z 0 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) + bw) ∨
      (t = 3 ∧ a 0 = z 0 - ρ - cond c 0 1 ∧ z 1 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) ≤ a 1 ∧
        a 1 ≤ z 1 - ρ - 1 + ((g : ℕ) : ℤ) * (bw + 1) + bw) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, hcases⟩ := h.innerPos_cases hB
  have hd : (0 : ℤ) ≤ cond c 0 1 ∧ (cond c 0 1 : ℤ) ≤ 1 := by cases c <;> simp
  have hNB' : (2 * ρ + 1 : ℤ) < NB * (bw + 1) := by exact_mod_cast hNB
  rcases hcases with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_bin (NB := NB) (bw := bw) (v := a 0 - (z 0 - ρ - 1))
      (by omega) (by omega)
    exact ⟨0, g, Or.inl ⟨rfl, e, by omega, by omega⟩⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_bin (NB := NB) (bw := bw) (v := a 1 - (z 1 - ρ - 1))
      (by omega) (by omega)
    exact ⟨1, g, Or.inr (Or.inl ⟨rfl, e, by omega, by omega⟩)⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_bin (NB := NB) (bw := bw) (v := a 0 - (z 0 - ρ - 1))
      (by omega) (by omega)
    exact ⟨2, g, Or.inr (Or.inr (Or.inl ⟨rfl, e, by omega, by omega⟩))⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_bin (NB := NB) (bw := bw) (v := a 1 - (z 1 - ρ - 1))
      (by omega) (by omega)
    exact ⟨3, g, Or.inr (Or.inr (Or.inr ⟨rfl, e, by omega, by omega⟩))⟩

/-- **A bin assignment for a family.** For arms from `B_ρ(z)`, when `NB (k + 1) > 2ρ + 1`, some
assignment `p` of a side and one of `NB` bins to every arm puts the start of arm `i` on the side
`(p i).1` in the window `[X (p i), X (p i) + k]`, where `X (t, g) = Z_t - ρ - 1 + g (k + 1)` and
`Z_t` is the coordinate of `z` along the side `t`. -/
theorem exists_bin_assignment {j : ℕ} {σ : Fin j → Bool} {z lo hi : LatticeSite 2} {ρ NB k : ℕ}
    {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z ρ lo hi (γ i))
    (hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆ Icc (lo + 1) (hi - 1))
    (hNB : 2 * ρ + 1 < NB * (k + 1)) {X : Fin 4 × Fin NB → ℤ}
    (hX : ∀ p, X p = (if p.1 = 0 ∨ p.1 = 2 then z 0 else z 1) - ρ - 1 +
      ((p.2 : ℕ) : ℤ) * (k + 1)) :
    ∃ p : Fin j → Fin 4 × Fin NB, ∀ i,
      ((p i).1 = 0 ∧ a i 1 = z 1 + ρ ∧ X (p i) ≤ a i 0 ∧ a i 0 ≤ X (p i) + k) ∨
      ((p i).1 = 1 ∧ a i 0 = z 0 + ρ ∧ X (p i) ≤ a i 1 ∧ a i 1 ≤ X (p i) + k) ∨
      ((p i).1 = 2 ∧ a i 1 = z 1 - ρ - cond (σ i) 0 1 ∧ X (p i) ≤ a i 0 ∧
        a i 0 ≤ X (p i) + k) ∨
      ((p i).1 = 3 ∧ a i 0 = z 0 - ρ - cond (σ i) 0 1 ∧ X (p i) ≤ a i 1 ∧
        a i 1 ≤ X (p i) + k) := by
  choose t g hbin using fun i => exists_mem_bin (hγ i) hB hNB
  refine ⟨fun i => (t i, g i), fun i => ?_⟩
  have hX' := hX (t i, g i)
  dsimp only at hX' ⊢
  rcases hbin i with ⟨ht, e, l, u⟩ | ⟨ht, e, l, u⟩ | ⟨ht, e, l, u⟩ | ⟨ht, e, l, u⟩
  · rw [ite_eq_left (Or.inl ht)] at hX'
    exact Or.inl ⟨ht, e, by omega, by omega⟩
  · rw [ite_eq_right (by rw [ht]; decide)] at hX'
    exact Or.inr (Or.inl ⟨ht, e, by omega, by omega⟩)
  · rw [ite_eq_left (Or.inr ht)] at hX'
    exact Or.inr (Or.inr (Or.inl ⟨ht, e, by omega, by omega⟩))
  · rw [ite_eq_right (by rw [ht]; decide)] at hX'
    exact Or.inr (Or.inr (Or.inr ⟨ht, e, by omega, by omega⟩))

/-- **The coordinate and the inner position of a start in a bin.** For an arm from `B_ρ(z)`
starting on the side `t` in the window `[x, x + bw]` of that side, at least `N + 1` from the ends of
its side, the coordinate `y` of the start along the side lies in the window and at least `N + 1`
from the ends of the side, and the inner position is the side's formula in `y`
(`IsArm.innerPos_cases`). -/
theorem exists_side_data {c : Bool} {z lo hi a b : LatticeSite 2} {ρ N bw : ℕ}
    {γ : (zdGraph 2).Walk a b} (h : IsArm ω c z ρ lo hi γ)
    (hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆ Icc (lo + 1) (hi - 1)) {t : Fin 4} {x : ℤ}
    (hbin : (t = 0 ∧ a 1 = z 1 + ρ ∧ x ≤ a 0 ∧ a 0 ≤ x + bw) ∨
      (t = 1 ∧ a 0 = z 0 + ρ ∧ x ≤ a 1 ∧ a 1 ≤ x + bw) ∨
      (t = 2 ∧ a 1 = z 1 - ρ - cond c 0 1 ∧ x ≤ a 0 ∧ a 0 ≤ x + bw) ∨
      (t = 3 ∧ a 0 = z 0 - ρ - cond c 0 1 ∧ x ≤ a 1 ∧ a 1 ≤ x + bw))
    (hfar : (z 0 - ρ + N + 1 ≤ a 0 ∧ a 0 + N + 1 ≤ z 0 + ρ) ∨
      (z 1 - ρ + N + 1 ≤ a 1 ∧ a 1 + N + 1 ≤ z 1 + ρ)) :
    ∃ y : ℤ, x ≤ y ∧ y ≤ x + bw ∧
      ((t = 0 ∧ z 0 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z 0 + ρ ∧
          innerPos z ρ c γ = 10 * ρ + 5 + 2 * z 0 - (2 * y + cond c 0 1)) ∨
        (t = 1 ∧ z 1 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z 1 + ρ ∧
          innerPos z ρ c γ = 6 * ρ + 3 + (2 * y + cond c 0 1) - 2 * z 1) ∨
        (t = 2 ∧ z 0 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z 0 + ρ ∧
          innerPos z ρ c γ = 2 * y + cond c 0 1 - 2 * z 0 + 2 * ρ + 1) ∨
        (t = 3 ∧ z 1 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z 1 + ρ ∧
          innerPos z ρ c γ = 14 * ρ + 7 + 2 * z 1 - (2 * y + cond c 0 1))) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, hcases⟩ := h.innerPos_cases hB
  have hd : (0 : ℤ) ≤ cond c 0 1 ∧ (cond c 0 1 : ℤ) ≤ 1 := by cases c <;> simp
  rcases hbin with ⟨ht, e, hx1, hx2⟩ | ⟨ht, e, hx1, hx2⟩ | ⟨ht, e, hx1, hx2⟩ | ⟨ht, e, hx1, hx2⟩
  · have hr : z 0 - ρ + N + 1 ≤ a 0 ∧ a 0 + N + 1 ≤ z 0 + ρ := by
      rcases hfar with h | h
      · exact h
      · omega
    clear hfar
    have hP : innerPos z ρ c γ = 10 * ρ + 5 + 2 * z 0 - (2 * a 0 + cond c 0 1) := by
      rcases hcases with ⟨e', hP⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩
      · exact hP
      all_goals omega
    exact ⟨a 0, hx1, hx2, Or.inl ⟨ht, hr.1, hr.2, hP⟩⟩
  · have hr : z 1 - ρ + N + 1 ≤ a 1 ∧ a 1 + N + 1 ≤ z 1 + ρ := by
      rcases hfar with h | h
      · omega
      · exact h
    clear hfar
    have hP : innerPos z ρ c γ = 6 * ρ + 3 + (2 * a 1 + cond c 0 1) - 2 * z 1 := by
      rcases hcases with ⟨e', -⟩ | ⟨e', hP⟩ | ⟨e', -⟩ | ⟨e', -⟩
      · omega
      · exact hP
      all_goals omega
    exact ⟨a 1, hx1, hx2, Or.inr (Or.inl ⟨ht, hr.1, hr.2, hP⟩)⟩
  · have hr : z 0 - ρ + N + 1 ≤ a 0 ∧ a 0 + N + 1 ≤ z 0 + ρ := by
      rcases hfar with h | h
      · exact h
      · omega
    clear hfar
    have hP : innerPos z ρ c γ = 2 * a 0 + cond c 0 1 - 2 * z 0 + 2 * ρ + 1 := by
      rcases hcases with ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', hP⟩ | ⟨e', -⟩
      · omega
      · omega
      · exact hP
      · omega
    exact ⟨a 0, hx1, hx2, Or.inr (Or.inr (Or.inl ⟨ht, hr.1, hr.2, hP⟩))⟩
  · have hr : z 1 - ρ + N + 1 ≤ a 1 ∧ a 1 + N + 1 ≤ z 1 + ρ := by
      rcases hfar with h | h
      · omega
      · exact h
    clear hfar
    have hP : innerPos z ρ c γ = 14 * ρ + 7 + 2 * z 1 - (2 * a 1 + cond c 0 1) := by
      rcases hcases with ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', hP⟩
      · omega
      · omega
      · omega
      · exact hP
    exact ⟨a 1, hx1, hx2, Or.inr (Or.inr (Or.inr ⟨ht, hr.1, hr.2, hP⟩))⟩

/-! ### Margins, gaps and order of starts in bins, in integers -/

section SideFacts

variable {z0 z1 : ℤ} {ρ N bw : ℕ}

/-- **Margins of a start in a bin.** A start on side `t` with coordinate `y` in the window
`[x, x + bw]`, at least `N + 1` from the ends of its side, leaves room `V` (resp. `2S`) between the
window `[x, x + B]` (resp. `[x, x + W]`) and the ends of the side of `B_R(z)`, `R + S + 1 = ρ`, when
`N` is large enough; and the side index `(6 - t) % 4` of the motion plan's linear order lies in
`[0, 3]`. -/
theorem side_facts_single {t : Fin 4} {x y d P : ℤ} {R S V B W : ℕ}
    (hx : x ≤ y ∧ y ≤ x + bw)
    (hdat : (t = 0 ∧ z0 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z0 + ρ ∧
          P = 10 * ρ + 5 + 2 * z0 - (2 * y + d)) ∨
        (t = 1 ∧ z1 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z1 + ρ ∧ P = 6 * ρ + 3 + (2 * y + d) - 2 * z1) ∨
        (t = 2 ∧ z0 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z0 + ρ ∧ P = 2 * y + d - 2 * z0 + 2 * ρ + 1) ∨
        (t = 3 ∧ z1 - ρ + N + 1 ≤ y ∧ y + N + 1 ≤ z1 + ρ ∧
          P = 14 * ρ + 7 + 2 * z1 - (2 * y + d)))
    (hRS : R + S + 1 = ρ) (h₁ : S + 1 + V + bw ≤ N) (h₂ : S + 1 + V + B ≤ N)
    (h₃ : 3 * S + bw ≤ N) (h₄ : W + 3 * S ≤ N) :
    (0 ≤ (((6 - (t : ℕ)) % 4 : ℕ) : ℤ) ∧ (((6 - (t : ℕ)) % 4 : ℕ) : ℤ) ≤ 3 ∧
      ((((6 - (t : ℕ)) % 4 : ℕ) : ℤ) + ((t : ℕ) : ℤ)) % 4 = 2) ∧
    ((if t = 0 ∨ t = 2 then z0 else z1) - R + V ≤ x ∧
      x + B + V ≤ (if t = 0 ∨ t = 2 then z0 else z1) + R) ∧
    ((if t = 0 ∨ t = 2 then z0 else z1) - R + 2 * S ≤ x ∧
      x + W + 2 * S ≤ (if t = 0 ∨ t = 2 then z0 else z1) + R) := by
  have ht : (t : ℕ) < 4 := t.isLt
  refine ⟨⟨by omega, by omega, by omega⟩, ?_, ?_⟩ <;>
  rcases hdat with ⟨e, l, u, -⟩ | ⟨e, l, u, -⟩ | ⟨e, l, u, -⟩ | ⟨e, l, u, -⟩ <;>
  split_ifs with hc <;> omega

/-- **Order and gaps of two starts in bins.** For two starts on the sides `t₁`, `t₂`, with
coordinates `y₁`, `y₂` in the windows `[x₁, x₁ + bw]`, `[x₂, x₂ + bw]`, at least `N + 1` from the
ends of their sides, whose inner positions satisfy `P₁ + D ≤ P₂`: the side index of the first is at
most that of the second, and on a common side the windows are at least `G` apart in the
counterclockwise direction when `2 (G + bw) + 1 ≤ D`. -/
theorem side_facts_pair {t₁ t₂ : Fin 4} {x₁ x₂ y₁ y₂ d₁ d₂ P₁ P₂ D G : ℤ}
    (hx₁ : x₁ ≤ y₁ ∧ y₁ ≤ x₁ + bw) (hx₂ : x₂ ≤ y₂ ∧ y₂ ≤ x₂ + bw)
    (hd₁ : 0 ≤ d₁ ∧ d₁ ≤ 1) (hd₂ : 0 ≤ d₂ ∧ d₂ ≤ 1)
    (hdat₁ : (t₁ = 0 ∧ z0 - ρ + N + 1 ≤ y₁ ∧ y₁ + N + 1 ≤ z0 + ρ ∧
          P₁ = 10 * ρ + 5 + 2 * z0 - (2 * y₁ + d₁)) ∨
        (t₁ = 1 ∧ z1 - ρ + N + 1 ≤ y₁ ∧ y₁ + N + 1 ≤ z1 + ρ ∧
          P₁ = 6 * ρ + 3 + (2 * y₁ + d₁) - 2 * z1) ∨
        (t₁ = 2 ∧ z0 - ρ + N + 1 ≤ y₁ ∧ y₁ + N + 1 ≤ z0 + ρ ∧
          P₁ = 2 * y₁ + d₁ - 2 * z0 + 2 * ρ + 1) ∨
        (t₁ = 3 ∧ z1 - ρ + N + 1 ≤ y₁ ∧ y₁ + N + 1 ≤ z1 + ρ ∧
          P₁ = 14 * ρ + 7 + 2 * z1 - (2 * y₁ + d₁)))
    (hdat₂ : (t₂ = 0 ∧ z0 - ρ + N + 1 ≤ y₂ ∧ y₂ + N + 1 ≤ z0 + ρ ∧
          P₂ = 10 * ρ + 5 + 2 * z0 - (2 * y₂ + d₂)) ∨
        (t₂ = 1 ∧ z1 - ρ + N + 1 ≤ y₂ ∧ y₂ + N + 1 ≤ z1 + ρ ∧
          P₂ = 6 * ρ + 3 + (2 * y₂ + d₂) - 2 * z1) ∨
        (t₂ = 2 ∧ z0 - ρ + N + 1 ≤ y₂ ∧ y₂ + N + 1 ≤ z0 + ρ ∧
          P₂ = 2 * y₂ + d₂ - 2 * z0 + 2 * ρ + 1) ∨
        (t₂ = 3 ∧ z1 - ρ + N + 1 ≤ y₂ ∧ y₂ + N + 1 ≤ z1 + ρ ∧
          P₂ = 14 * ρ + 7 + 2 * z1 - (2 * y₂ + d₂)))
    (hD : P₁ + D ≤ P₂) (hDpos : 1 ≤ D) (hG : 2 * (G + bw) + 1 ≤ D) :
    (((6 - (t₁ : ℕ)) % 4 : ℕ) : ℤ) ≤ (((6 - (t₂ : ℕ)) % 4 : ℕ) : ℤ) ∧
      (t₁ = t₂ → (t₁ = 1 ∨ t₁ = 2 → x₁ + G ≤ x₂) ∧ (t₁ = 0 ∨ t₁ = 3 → x₂ + G ≤ x₁)) := by
  rcases hdat₁ with ⟨e₁, l₁, u₁, p₁⟩ | ⟨e₁, l₁, u₁, p₁⟩ | ⟨e₁, l₁, u₁, p₁⟩ | ⟨e₁, l₁, u₁, p₁⟩ <;>
  rcases hdat₂ with ⟨e₂, l₂, u₂, p₂⟩ | ⟨e₂, l₂, u₂, p₂⟩ | ⟨e₂, l₂, u₂, p₂⟩ | ⟨e₂, l₂, u₂, p₂⟩ <;>
  subst e₁ e₂ <;> simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] <;> omega

end SideFacts

/-- **Arms of one colour are twice as far apart.** For a family without packs whose integer
positions `P` are in strict cyclic order along the indices and pairwise at least `D` apart, two
arms of one colour have positions at least `2D` apart: an arm of the other colour lies between
them. -/
theorem le_abs_sub_of_eq_colour {j : ℕ} {σ : Fin j → Bool}
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {P : Fin j → ℤ}
    (ho : ∀ i k l, i < k → k < l → sbtw (P i) (P k) (P l)) {D : ℤ}
    (hsep : ∀ i k, i ≠ k → D ≤ |P i - P k|) {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) :
    2 * D ≤ |P i - P k| := by
  rcases hσ with hj | hσ
  · exact absurd (Fin.ext (by omega)) hik
  rcases lt_trichotomy (P k) (P i) with hlt | heq | hlt
  · obtain ⟨⟨l, hl, h₁, h₂⟩, -⟩ := exists_lt_lt_of_eq hσ ho hik hσik hlt
    have hli : l ≠ i := fun h => hl (congrArg σ h)
    have hlk : l ≠ k := fun h => hl ((congrArg σ h).trans hσik.symm)
    have e₁ := hsep l i hli
    have e₂ := hsep l k hlk
    rw [abs_of_neg (by omega)] at e₁
    rw [abs_of_pos (by omega)] at e₂
    rw [abs_of_pos (by omega)]
    omega
  · have e := hsep i k hik
    rw [heq, sub_self, abs_zero] at e
    rw [heq, sub_self, abs_zero]
    omega
  · obtain ⟨⟨l, hl, h₁, h₂⟩, -⟩ := exists_lt_lt_of_eq hσ ho hik.symm hσik.symm hlt
    have hlk : l ≠ k := fun h => hl (congrArg σ h)
    have hli : l ≠ i := fun h => hl ((congrArg σ h).trans hσik)
    have e₁ := hsep l i hli
    have e₂ := hsep l k hlk
    rw [abs_of_pos (by omega)] at e₁
    rw [abs_of_neg (by omega)] at e₂
    rw [abs_of_neg (by omega)]
    omega

/-- **The integer scales of the inner step** for `0 < η ≤ 1 / 256` and an integer `E` with
`E √η ≥ 1`, at `N ≥ E²`: `M = ⌊√η N⌋` and `K = ⌊η N⌋` satisfy `⌊N / E⌋ ≤ M`, `16 M ≤ N`,
`⌊N / E²⌋ ≤ K`, `16 K ≤ M`, and the separation `4 √η N` is at least `4M` and at least `2M + 2`. -/
theorem floor_sqrt_mul_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 256) {E N : ℕ}
    (hE : 1 ≤ (E : ℝ) * Real.sqrt η) (hN : E * E ≤ N) :
    N / E ≤ ⌊Real.sqrt η * N⌋₊ ∧ 16 * ⌊Real.sqrt η * N⌋₊ ≤ N ∧ N / (E * E) ≤ ⌊η * N⌋₊ ∧
      16 * ⌊η * N⌋₊ ≤ ⌊Real.sqrt η * N⌋₊ ∧ 1 ≤ Real.sqrt η * N ∧
      4 * (⌊Real.sqrt η * N⌋₊ : ℝ) ≤ 4 * Real.sqrt η * N ∧
      2 * (⌊Real.sqrt η * N⌋₊ : ℝ) + 2 ≤ 4 * Real.sqrt η * N := by
  obtain ⟨h₁, -, h₃, -, -⟩ := div_le_floor_sqrt_mul hη (by linarith) hE N
  have hs : 0 ≤ Real.sqrt η := Real.sqrt_nonneg η
  have hsq : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
  have hs16 : Real.sqrt η ≤ 1 / 16 := by nlinarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hE16 : (16 : ℝ) ≤ E := by nlinarith
  have hNE : ((E * E : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hNE
  have hsN : 1 ≤ Real.sqrt η * N := by
    have : (E : ℝ) ≤ Real.sqrt η * ((E : ℝ) * E) := by nlinarith
    nlinarith
  have hfl : (⌊Real.sqrt η * N⌋₊ : ℝ) ≤ Real.sqrt η * N := Nat.floor_le (by positivity)
  have hfk : (⌊η * N⌋₊ : ℝ) ≤ η * N := Nat.floor_le (by positivity)
  refine ⟨h₁, ?_, h₃, ?_, hsN, by linarith, by linarith⟩
  · have : ((16 * ⌊Real.sqrt η * N⌋₊ : ℕ) : ℝ) ≤ N := by
      push_cast
      nlinarith
    exact_mod_cast this
  · refine Nat.le_floor ?_
    push_cast
    have : η * N ≤ Real.sqrt η * N / 16 := by nlinarith
    linarith

end PercLib.Models.Planar
