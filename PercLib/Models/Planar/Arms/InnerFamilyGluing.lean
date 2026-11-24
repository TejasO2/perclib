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

public import PercLib.Models.Planar.Arms.TwoSidedGluing

/-!
# The two-sided gluing with regions disjoint by colour

The inner separation step (`exists_inner_separating_event`) produces families separated at the
inner boundary with separation `4 √η N` and fences of depth `M' = ⌊√η N⌋`: neighbouring starts
are only about `2M'` apart, too close for the two-sided gluing of `TwoSidedGluing.lean`, whose
regions (which contain the boxes of radius `M' + 1` about the starts) must be disjoint for all
pairs of arms. Only arms of one colour need disjoint regions: those are at least twice as far apart
when the colour sequence has no packs. This file proves the two-sided gluing in that form, and
the reindexing of families by rotations of the indices, which brings the arms of a cyclically
ordered family into the linear order from the lower-left corner that the motion plan asks for.

## Main results

* `sbtw_comp_finRotate_pow`, `sbtw_of_comp_finRotate_pow`: rotating the indices keeps the cyclic
  order of a family; `ArmsDisjoint.comp_perm`, `ArmsDisjoint.of_comp_perm`;
  `multiArmEventTo_subset_comp_finRotate_pow`, `multiArmEventTo_comp_finRotate_pow_subset`.
* `disjoint_two_sided_boxes`, `disjoint_two_sided_box_of_window`: the read sets of two straight
  two-sided corridors are disjoint, and a corridor misses the box about an end or a start of
  another arm.
* `law_mul_mul_prod_le_law_of_two_sided_of_colour`: the two-sided gluing through given corridors
  with regions disjoint by colour.
* `exists_pos_le_law_two_sided_of_colour`: the two-sided gluing with straight corridors, the gaps
  between corridors of one colour at least `W + 2S` and between any two at least
  `W + M + K + M' + K' + 2`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

/-! ### Rotating the indices of a family -/

section Rotation

variable {α : Type*} [CircularOrder α] {n : ℕ}

/-- The image of an index under `finRotate`: the next index, or `0` after the last. -/
theorem val_finRotate_succ {m : ℕ} (x : Fin (m + 1)) :
    ((finRotate (m + 1) x : Fin (m + 1)) : ℕ) = if x = Fin.last m then 0 else (x : ℕ) + 1 := by
  split_ifs with h
  · rw [h, finRotate_last]
    rfl
  · exact coe_finRotate_of_ne_last h

/-- **Rotating the indices keeps the cyclic order.** If `f` takes increasing triples of indices to
triples in strict cyclic order, so does `f ∘ finRotate n`. -/
theorem sbtw_comp_finRotate {f : Fin n → α}
    (hf : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l)) (i k l : Fin n) (hik : i < k)
    (hkl : k < l) : sbtw (f (finRotate n i)) (f (finRotate n k)) (f (finRotate n l)) := by
  rcases n with _ | m
  · exact i.elim0
  have hi := val_finRotate_succ i
  have hk := val_finRotate_succ k
  have hl := val_finRotate_succ l
  have hil : i ≠ Fin.last m := fun h => by
    have := Fin.le_last l
    rw [Fin.lt_def] at hik hkl
    rw [Fin.le_def, ← h] at this
    omega
  have hkl' : k ≠ Fin.last m := fun h => by
    have := Fin.le_last l
    rw [Fin.lt_def] at hkl
    rw [Fin.le_def, ← h] at this
    omega
  rw [ite_eq_right hil] at hi
  rw [ite_eq_right hkl'] at hk
  by_cases hll : l = Fin.last m
  · rw [ite_eq_left hll] at hl
    have h0 : finRotate (m + 1) l = 0 := Fin.ext (by rw [hl]; rfl)
    rw [h0]
    refine sbtw_cyclic_left (hf 0 _ _ ?_ ?_)
    · rw [Fin.lt_def, hi]
      exact Nat.succ_pos _
    · rw [Fin.lt_def, hi, hk]
      rw [Fin.lt_def] at hik
      omega
  · rw [ite_eq_right hll] at hl
    refine hf _ _ _ ?_ ?_
    · rw [Fin.lt_def, hi, hk]
      rw [Fin.lt_def] at hik
      omega
    · rw [Fin.lt_def, hk, hl]
      rw [Fin.lt_def] at hkl
      omega

/-- **The converse**: if `f ∘ finRotate n` takes increasing triples to triples in strict cyclic
order, so does `f`. -/
theorem sbtw_of_comp_finRotate {f : Fin n → α}
    (hf : ∀ i k l, i < k → k < l → sbtw (f (finRotate n i)) (f (finRotate n k)) (f (finRotate n l)))
    (i k l : Fin n) (hik : i < k) (hkl : k < l) : sbtw (f i) (f k) (f l) := by
  rcases n with _ | m
  · exact i.elim0
  obtain ⟨i', rfl⟩ := (finRotate (m + 1)).surjective i
  obtain ⟨k', rfl⟩ := (finRotate (m + 1)).surjective k
  obtain ⟨l', rfl⟩ := (finRotate (m + 1)).surjective l
  have hi := val_finRotate_succ i'
  have hk := val_finRotate_succ k'
  have hl := val_finRotate_succ l'
  rw [Fin.lt_def] at hik hkl
  have hk' : k' ≠ Fin.last m := fun h => by
    rw [ite_eq_left h] at hk
    omega
  have hl' : l' ≠ Fin.last m := fun h => by
    rw [ite_eq_left h] at hl
    omega
  rw [ite_eq_right hk'] at hk
  rw [ite_eq_right hl'] at hl
  have hkl'' : k' < l' := by
    rw [Fin.lt_def]
    omega
  by_cases hi' : i' = Fin.last m
  · subst hi'
    have hlast : l' < Fin.last m := lt_of_le_of_ne (Fin.le_last l') hl'
    exact sbtw_cyclic_right (hf k' l' (Fin.last m) hkl'' hlast)
  · rw [ite_eq_right hi'] at hi
    exact hf i' k' l' (by rw [Fin.lt_def]; omega) hkl''

/-- **Rotating the indices by any power keeps the cyclic order.** -/
theorem sbtw_comp_finRotate_pow (m : ℕ) {f : Fin n → α}
    (hf : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l)) :
    ∀ i k l, i < k → k < l →
      sbtw (f ((finRotate n ^ m) i)) (f ((finRotate n ^ m) k)) (f ((finRotate n ^ m) l)) := by
  induction m with
  | zero =>
    simpa only [pow_zero, Equiv.Perm.one_apply] using hf
  | succ m ih =>
    intro i k l hik hkl
    simp only [pow_succ, Equiv.Perm.mul_apply]
    exact sbtw_comp_finRotate (f := fun x => f ((finRotate n ^ m) x)) ih i k l hik hkl

/-- **The converse for powers.** -/
theorem sbtw_of_comp_finRotate_pow (m : ℕ) {f : Fin n → α}
    (hf : ∀ i k l, i < k → k < l →
      sbtw (f ((finRotate n ^ m) i)) (f ((finRotate n ^ m) k)) (f ((finRotate n ^ m) l))) :
    ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l) := by
  induction m with
  | zero =>
    simpa only [pow_zero, Equiv.Perm.one_apply] using hf
  | succ m ih =>
    refine ih ?_
    refine sbtw_of_comp_finRotate (f := fun x => f ((finRotate n ^ m) x)) ?_
    intro i k l hik hkl
    have := hf i k l hik hkl
    simp only [pow_succ, Equiv.Perm.mul_apply] at this
    exact this

/-- **Rotating a colour sequence keeps it free of packs.** -/
theorem comp_finRotate_pow_of_noPack {j : ℕ} {σ : Fin j → Bool}
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (m : ℕ) :
    j ≤ 1 ∨ ∀ i, σ ((finRotate j ^ m) i) ≠ σ ((finRotate j ^ m) (finRotate j i)) := by
  rcases hσ with h | h
  · exact Or.inl h
  · refine Or.inr fun i => ?_
    have hc : (finRotate j ^ m) (finRotate j i) = finRotate j ((finRotate j ^ m) i) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_succ, ← pow_succ']
    rw [hc]
    exact h _

end Rotation

namespace PercLib.Models.Planar

section Reindex

variable {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **Disjointness after reindexing** by a permutation. -/
theorem ArmsDisjoint.comp_perm (e : Equiv.Perm (Fin j)) (h : ArmsDisjoint σ γ) :
    ArmsDisjoint (fun i => σ (e i)) (fun i => γ (e i)) :=
  ⟨fun i k hik => h.1 (e i) (e k) (e.injective.ne hik),
    fun i k hik => h.2 (e i) (e k) (e.injective.ne hik)⟩

/-- **Disjointness before reindexing.** -/
theorem ArmsDisjoint.of_comp_perm (e : Equiv.Perm (Fin j))
    (h : ArmsDisjoint (fun i => σ (e i)) (fun i => γ (e i))) : ArmsDisjoint σ γ := by
  refine ⟨fun i k hik => ?_, fun i k hik => ?_⟩
  · obtain ⟨i', rfl⟩ := e.surjective i
    obtain ⟨k', rfl⟩ := e.surjective k
    exact h.1 i' k' fun h' => hik (congrArg e h')
  · obtain ⟨i', rfl⟩ := e.surjective i
    obtain ⟨k', rfl⟩ := e.surjective k
    exact h.2 i' k' fun h' => hik (congrArg e h')

/-- **The arm event after rotating the indices.** -/
theorem multiArmEventTo_subset_comp_finRotate_pow (m : ℕ) {z : LatticeSite 2} {r : ℕ}
    {lo hi : LatticeSite 2} {J I : Fin j → Set ℤ} :
    multiArmEventTo σ z r lo hi J I ⊆ multiArmEventTo (fun i => σ ((finRotate j ^ m) i)) z r lo hi
      (fun i => J ((finRotate j ^ m) i)) (fun i => I ((finRotate j ^ m) i)) := by
  rintro ω ⟨a, b, γ, hγ, hd, hw, ho⟩
  exact ⟨fun i => a ((finRotate j ^ m) i), fun i => b ((finRotate j ^ m) i),
    fun i => γ ((finRotate j ^ m) i), fun i => hγ _, hd.comp_perm _, fun i => hw _,
    sbtw_comp_finRotate_pow m (f := fun i => landingPos lo hi (σ i) (γ i)) ho⟩

/-- **The arm event before rotating the indices.** -/
theorem multiArmEventTo_comp_finRotate_pow_subset (m : ℕ) {z : LatticeSite 2} {r : ℕ}
    {lo hi : LatticeSite 2} {J I : Fin j → Set ℤ} :
    multiArmEventTo (fun i => σ ((finRotate j ^ m) i)) z r lo hi
      (fun i => J ((finRotate j ^ m) i)) (fun i => I ((finRotate j ^ m) i)) ⊆
      multiArmEventTo σ z r lo hi J I := by
  rintro ω ⟨a, b, γ, hγ, hd, hw, ho⟩
  set e := finRotate j ^ m with he
  refine ⟨fun i => a (e.symm i), fun i => b (e.symm i), fun i => γ (e.symm i), fun i => ?_, ?_,
    fun i => ?_, ?_⟩
  · have := hγ (e.symm i)
    simpa only [Equiv.apply_symm_apply] using this
  · refine ⟨fun i k hik hi hk => ?_, fun i k hik hi hk => ?_⟩
    · exact hd.1 (e.symm i) (e.symm k) (e.symm.injective.ne hik)
        (by simp only [Equiv.apply_symm_apply]; exact hi)
        (by simp only [Equiv.apply_symm_apply]; exact hk)
    · exact hd.2 (e.symm i) (e.symm k) (e.symm.injective.ne hik)
        (by simp only [Equiv.apply_symm_apply]; exact hi)
        (by simp only [Equiv.apply_symm_apply]; exact hk)
  · simpa only [Equiv.apply_symm_apply] using hw (e.symm i)
  · refine sbtw_of_comp_finRotate_pow m
      (f := fun i => landingPos lo hi (σ i) (γ (e.symm i))) ?_
    intro i k l hik hkl
    have key : ∀ x y : Fin j, x = y →
        landingPos lo hi (σ (e y)) (γ x) = landingPos lo hi (σ (e y)) (γ y) := by
      rintro x y rfl
      rfl
    have h₁ := key _ i (e.symm_apply_apply i)
    have h₂ := key _ k (e.symm_apply_apply k)
    have h₃ := key _ l (e.symm_apply_apply l)
    change sbtw (landingPos lo hi (σ (e i)) (γ (e.symm (e i))))
      (landingPos lo hi (σ (e k)) (γ (e.symm (e k))))
      (landingPos lo hi (σ (e l)) (γ (e.symm (e l))))
    rw [h₁, h₂, h₃]
    exact ho i k l hik hkl

end Reindex

/-! ### Straight two-sided corridors: read sets and the boxes of other arms -/

section Windows

variable {z : LatticeSite 2} {R R' M K M' K' W S : ℕ}

/-- A point of the box of a corridor enlarged by its colour's offset lies in the box enlarged by one
at its upper corner. -/
theorem mem_Icc_add_one_of_mem_Icc_add_cond (c : Bool) {lo hi v : LatticeSite 2}
    (h : v ∈ Icc lo (hi + cond c 0 1)) : v ∈ Icc lo (hi + 1) := by
  refine ⟨h.1, fun m => ?_⟩
  have := h.2 m
  cases c <;> simp only [Bool.cond_true, Bool.cond_false, Pi.add_apply, Pi.zero_apply, add_zero,
    Pi.one_apply] at this ⊢ <;> omega

/-- **The read sets of two straight two-sided corridors are disjoint**: corridors at least
`2S ≥ 2` from the corners of `B_R(z)` and, on one side, more than `W + 1` apart have disjoint boxes,
even when enlarged by one at their upper corners. -/
theorem disjoint_two_sided_boxes {t1 t2 : Fin 4} {col1 col2 : Bool} {x1 x2 : ℤ}
    {dir1 dir2 : Fin 2} {lo1 hi1 gl1 gh1 lo2 hi2 gl2 gh2 : LatticeSite 2}
    (hS : 1 ≤ S)
    (hside1 : (t1 = 0 ∧ dir1 = 1 ∧ lo1 = ![x1, z 1 + R] ∧ hi1 = ![x1 + W, z 1 + R'] ∧
        gl1 = ![x1 - S, z 1 + R - M - 1] ∧ gh1 = ![x1 + W + S, z 1 + R' + M' + 1]) ∨
      (t1 = 1 ∧ dir1 = 0 ∧ lo1 = ![z 0 + R, x1] ∧ hi1 = ![z 0 + R', x1 + W] ∧
        gl1 = ![z 0 + R - M - 1, x1 - S] ∧ gh1 = ![z 0 + R' + M' + 1, x1 + W + S]) ∨
      (t1 = 2 ∧ dir1 = 1 ∧ lo1 = ![x1, z 1 - R' - cond col1 0 1] ∧
        hi1 = ![x1 + W, z 1 - R - cond col1 0 1] ∧
        gl1 = ![x1 - S, z 1 - R' - M' - 2] ∧ gh1 = ![x1 + W + S, z 1 - R + M + 1]) ∨
      (t1 = 3 ∧ dir1 = 0 ∧ lo1 = ![z 0 - R' - cond col1 0 1, x1] ∧
        hi1 = ![z 0 - R - cond col1 0 1, x1 + W] ∧
        gl1 = ![z 0 - R' - M' - 2, x1 - S] ∧ gh1 = ![z 0 - R + M + 1, x1 + W + S]))
    (hside2 : (t2 = 0 ∧ dir2 = 1 ∧ lo2 = ![x2, z 1 + R] ∧ hi2 = ![x2 + W, z 1 + R'] ∧
        gl2 = ![x2 - S, z 1 + R - M - 1] ∧ gh2 = ![x2 + W + S, z 1 + R' + M' + 1]) ∨
      (t2 = 1 ∧ dir2 = 0 ∧ lo2 = ![z 0 + R, x2] ∧ hi2 = ![z 0 + R', x2 + W] ∧
        gl2 = ![z 0 + R - M - 1, x2 - S] ∧ gh2 = ![z 0 + R' + M' + 1, x2 + W + S]) ∨
      (t2 = 2 ∧ dir2 = 1 ∧ lo2 = ![x2, z 1 - R' - cond col2 0 1] ∧
        hi2 = ![x2 + W, z 1 - R - cond col2 0 1] ∧
        gl2 = ![x2 - S, z 1 - R' - M' - 2] ∧ gh2 = ![x2 + W + S, z 1 - R + M + 1]) ∨
      (t2 = 3 ∧ dir2 = 0 ∧ lo2 = ![z 0 - R' - cond col2 0 1, x2] ∧
        hi2 = ![z 0 - R - cond col2 0 1, x2 + W] ∧
        gl2 = ![z 0 - R' - M' - 2, x2 - S] ∧ gh2 = ![z 0 - R + M + 1, x2 + W + S]))
    (hc0₁ : t1 = 0 ∨ t1 = 2 → z 0 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 0 + R)
    (hc1₁ : t1 = 1 ∨ t1 = 3 → z 1 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 1 + R)
    (hc0₂ : t2 = 0 ∨ t2 = 2 → z 0 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 0 + R)
    (hc1₂ : t2 = 1 ∨ t2 = 3 → z 1 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 1 + R)
    (hgap : t1 = t2 → x1 + W + 1 < x2 ∨ x2 + W + 1 < x1) :
    Disjoint (Icc lo1 (hi1 + 1)) (Icc lo2 (hi2 + 1)) := by
  have hcc1 : cond col1 (0 : ℤ) 1 = 0 ∨ cond col1 (0 : ℤ) 1 = 1 := by cases col1 <;> simp
  have hcc2 : cond col2 (0 : ℤ) 1 = 0 ∨ cond col2 (0 : ℤ) 1 = 1 := by cases col2 <;> simp
  have hcor1 : ((t1 = 0 ∨ t1 = 2) ∧ z 0 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 0 + R) ∨
      ((t1 = 1 ∨ t1 = 3) ∧ z 1 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t1 = 0 ∨ t1 = 2
    · exact Or.inl ⟨h, hc0₁ h⟩
    · exact Or.inr ⟨by omega, hc1₁ (by omega)⟩
  have hcor2 : ((t2 = 0 ∨ t2 = 2) ∧ z 0 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 0 + R) ∨
      ((t2 = 1 ∨ t2 = 3) ∧ z 1 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t2 = 0 ∨ t2 = 2
    · exact Or.inl ⟨h, hc0₂ h⟩
    · exact Or.inr ⟨by omega, hc1₂ (by omega)⟩
  have hgap' : (t1 = t2 ∧ (x1 + W + 1 < x2 ∨ x2 + W + 1 < x1)) ∨ t1 ≠ t2 := by
    by_cases h : t1 = t2
    · exact Or.inl ⟨h, hgap h⟩
    · exact Or.inr h
  clear hc0₁ hc1₁ hc0₂ hc1₂ hgap
  refine disjoint_Icc_of_lt ?_
  rcases hside1 with ⟨rfl, -, rfl, rfl, -, -⟩ | ⟨rfl, -, rfl, rfl, -, -⟩ |
    ⟨rfl, -, rfl, rfl, -, -⟩ | ⟨rfl, -, rfl, rfl, -, -⟩ <;>
  rcases hside2 with ⟨rfl, -, rfl, rfl, -, -⟩ | ⟨rfl, -, rfl, rfl, -, -⟩ |
    ⟨rfl, -, rfl, rfl, -, -⟩ | ⟨rfl, -, rfl, rfl, -, -⟩ <;>
  rcases hcor1 with ⟨ht₁, h₁, h₂⟩ | ⟨ht₁, h₁, h₂⟩ <;> (try exact absurd ht₁ (by decide)) <;>
  rcases hcor2 with ⟨ht₂, h₃, h₄⟩ | ⟨ht₂, h₃, h₄⟩ <;> (try exact absurd ht₂ (by decide)) <;>
  rcases hgap' with ⟨hteq, hg⟩ | hne <;> (try exact absurd hteq (by decide)) <;>
  (try exact absurd rfl hne) <;>
  simp only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

/-- **A corridor misses the box about the end or the start of another arm.** Let `b` lie in the
window `[α, β]` on the side `t₁` of `B_ρ'(z)`, `R ≤ ρ'`, `Mb + 1 < R + ρ'`, aligned with the
corridor `[x₁, x₁ + W]` of its own arm (`β ≤ x₁ + Kb`, `x₁ + W ≤ α + Kb`), and let a second corridor
`[x₂, x₂ + W]` stand on the side `t₂`, both at least `2S` from the corners of `B_R(z)` and, on one
side, more than `W + Gp` apart, `Gp ≥ Kb + Mb + 2`, `2S ≥ Kb + Mb + 2`. Then the box of the second
corridor, enlarged by one at its upper corner, misses the box of radius `Mb + 1` about `b`. -/
theorem disjoint_two_sided_box_of_window {t1 t2 : Fin 4} {col1 col2 : Bool}
    {x1 x2 α β : ℤ} {dir2 : Fin 2} {lo2 hi2 gl2 gh2 b : LatticeSite 2} {ρ' Mb Kb Gp : ℕ}
    (hRρ : R ≤ ρ') (hMb : Mb + 1 < R + ρ') (hSb : Kb + Mb + 2 ≤ 2 * S)
    (hGp : Kb + Mb + 2 ≤ Gp)
    (hside2 : (t2 = 0 ∧ dir2 = 1 ∧ lo2 = ![x2, z 1 + R] ∧ hi2 = ![x2 + W, z 1 + R'] ∧
        gl2 = ![x2 - S, z 1 + R - M - 1] ∧ gh2 = ![x2 + W + S, z 1 + R' + M' + 1]) ∨
      (t2 = 1 ∧ dir2 = 0 ∧ lo2 = ![z 0 + R, x2] ∧ hi2 = ![z 0 + R', x2 + W] ∧
        gl2 = ![z 0 + R - M - 1, x2 - S] ∧ gh2 = ![z 0 + R' + M' + 1, x2 + W + S]) ∨
      (t2 = 2 ∧ dir2 = 1 ∧ lo2 = ![x2, z 1 - R' - cond col2 0 1] ∧
        hi2 = ![x2 + W, z 1 - R - cond col2 0 1] ∧
        gl2 = ![x2 - S, z 1 - R' - M' - 2] ∧ gh2 = ![x2 + W + S, z 1 - R + M + 1]) ∨
      (t2 = 3 ∧ dir2 = 0 ∧ lo2 = ![z 0 - R' - cond col2 0 1, x2] ∧
        hi2 = ![z 0 - R - cond col2 0 1, x2 + W] ∧
        gl2 = ![z 0 - R' - M' - 2, x2 - S] ∧ gh2 = ![z 0 - R + M + 1, x2 + W + S]))
    (hc0₁ : t1 = 0 ∨ t1 = 2 → z 0 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 0 + R)
    (hc1₁ : t1 = 1 ∨ t1 = 3 → z 1 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 1 + R)
    (hc0₂ : t2 = 0 ∨ t2 = 2 → z 0 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 0 + R)
    (hc1₂ : t2 = 1 ∨ t2 = 3 → z 1 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 1 + R)
    (hal : β ≤ x1 + Kb ∧ x1 + W ≤ α + Kb)
    (hb : (t1 = 0 ∧ b 1 = z 1 + ρ' ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
      (t1 = 1 ∧ b 0 = z 0 + ρ' ∧ α ≤ b 1 ∧ b 1 ≤ β) ∨
      (t1 = 2 ∧ b 1 = z 1 - ρ' - cond col1 0 1 ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
      (t1 = 3 ∧ b 0 = z 0 - ρ' - cond col1 0 1 ∧ α ≤ b 1 ∧ b 1 ≤ β))
    (hgap : t1 = t2 → x1 + W + Gp < x2 ∨ x2 + W + Gp < x1) :
    Disjoint (Icc lo2 (hi2 + 1))
      (Icc (b - (Mb : LatticeSite 2)) (b + ((Mb + 1 : ℕ) : LatticeSite 2))) := by
  have hcc1 : cond col1 (0 : ℤ) 1 = 0 ∨ cond col1 (0 : ℤ) 1 = 1 := by cases col1 <;> simp
  have hcc2 : cond col2 (0 : ℤ) 1 = 0 ∨ cond col2 (0 : ℤ) 1 = 1 := by cases col2 <;> simp
  have hcor1 : ((t1 = 0 ∨ t1 = 2) ∧ z 0 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 0 + R) ∨
      ((t1 = 1 ∨ t1 = 3) ∧ z 1 - R + 2 * S ≤ x1 ∧ x1 + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t1 = 0 ∨ t1 = 2
    · exact Or.inl ⟨h, hc0₁ h⟩
    · exact Or.inr ⟨by omega, hc1₁ (by omega)⟩
  have hcor2 : ((t2 = 0 ∨ t2 = 2) ∧ z 0 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 0 + R) ∨
      ((t2 = 1 ∨ t2 = 3) ∧ z 1 - R + 2 * S ≤ x2 ∧ x2 + W + 2 * S ≤ z 1 + R) := by
    by_cases h : t2 = 0 ∨ t2 = 2
    · exact Or.inl ⟨h, hc0₂ h⟩
    · exact Or.inr ⟨by omega, hc1₂ (by omega)⟩
  have hgap' : (t1 = t2 ∧ (x1 + W + Gp < x2 ∨ x2 + W + Gp < x1)) ∨ t1 ≠ t2 := by
    by_cases h : t1 = t2
    · exact Or.inl ⟨h, hgap h⟩
    · exact Or.inr h
  obtain ⟨hal₁, hal₂⟩ := hal
  clear hc0₁ hc1₁ hc0₂ hc1₂ hgap
  refine disjoint_Icc_of_lt ?_
  rcases hside2 with ⟨rfl, -, rfl, rfl, -, -⟩ | ⟨rfl, -, rfl, rfl, -, -⟩ |
    ⟨rfl, -, rfl, rfl, -, -⟩ | ⟨rfl, -, rfl, rfl, -, -⟩ <;>
  rcases hb with ⟨rfl, hb₁, hb₂, hb₃⟩ | ⟨rfl, hb₁, hb₂, hb₃⟩ | ⟨rfl, hb₁, hb₂, hb₃⟩ |
    ⟨rfl, hb₁, hb₂, hb₃⟩ <;>
  rcases hcor1 with ⟨ht₁, h₁, h₂⟩ | ⟨ht₁, h₁, h₂⟩ <;> (try exact absurd ht₁ (by decide)) <;>
  rcases hcor2 with ⟨ht₂, h₃, h₄⟩ | ⟨ht₂, h₃, h₄⟩ <;> (try exact absurd ht₂ (by decide)) <;>
  rcases hgap' with ⟨hteq, hg⟩ | hne <;> (try exact absurd hteq (by decide)) <;>
  (try exact absurd rfl hne) <;>
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, Pi.natCast_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> omega

end Windows

/-! ### The two-sided gluing through given corridors, regions disjoint by colour -/

section Corridors

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- Two points of the regions of two arms of one colour, for regions disjoint by colour, are the
same arm. -/
theorem eq_of_mem_of_mem_of_disjoint_of_eq {G : Fin j → Set (LatticeSite 2)}
    (hG : ∀ i k, i ≠ k → σ i = σ k → Disjoint (G i) (G k)) {i k : Fin j} (hσik : σ i = σ k)
    {v : LatticeSite 2} (hi : v ∈ G i) (hk : v ∈ G k) : i = k := by
  by_contra hik
  exact disjoint_left.1 (hG i k hik hσik) hi hk

/-- **The two-sided gluing through given corridors, regions disjoint by colour.** As
`law_mul_mul_prod_le_law_of_two_sided`, with the disjointness of the regions `G i` asked only for
arms of one colour; in exchange, the pairs read by different corridors are different (`hTT`), and
no corridor reads a pair inside the box of radius `M + 1` (`M' + 1`) about a possible end (start)
of an arm of the other colour (`hTBx`, `hTB'x`). This fits the families of the inner separation
step, whose starts are only `≍ M'` apart: arms of one colour are twice as far apart (pack-free). -/
theorem law_mul_mul_prod_le_law_of_two_sided_of_colour (q : Sym2 (LatticeSite 2) → unitInterval)
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
    (hBG : ∀ i, ∀ b ∈ B i,
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G i)
    (hB'G : ∀ i, ∀ a ∈ B' i,
      Icc (a - (M' : LatticeSite 2)) (a + ((M' + 1 : ℕ) : LatticeSite 2)) ⊆ G i)
    (hQG : ∀ i, Q i ⊆ G i) (hG : ∀ i k, i ≠ k → σ i = σ k → Disjoint (G i) (G k))
    (hTT : ∀ i k, i ≠ k → Disjoint (T i) (T k))
    (hTBx : ∀ i k, σ i ≠ σ k → ∀ b ∈ B i, ∀ e ∈ T k,
      ¬∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)))
    (hTB'x : ∀ i k, σ i ≠ σ k → ∀ a ∈ B' i, ∀ e ∈ T k,
      ¬∀ v ∈ e, v ∈ Icc (a - (M' : LatticeSite 2)) (a + ((M' + 1 : ℕ) : LatticeSite 2)))
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
  -- a pair is read by at most one corridor
  have hreg : ∀ i k e, e ∈ T k → e ∈ T i → k = i := by
    intro i k e hk hi
    by_contra hki
    exact disjoint_left.1 (hTT k i hki) hk hi
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
        have hki := hreg i k e hek he
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
    have hσk : σ k = σ i := by
      by_contra h
      exact hTBx i k (Ne.symm h) b hb e hk hbox
    constructor
    · rintro ⟨l, hl, hel⟩
      rw [← hσk, ← hreg k l e hel hk]
      exact hl
    · intro hσi
      exact ⟨k, hσk.trans hσi, hk⟩
  have hTB' : ∀ i, ∀ a ∈ B' i, ∀ e ∈ Tall, (∀ v ∈ e, v ∈ Icc (a - (M' : LatticeSite 2))
      (a + ((M' + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false) := by
    rintro i a ha e ⟨k, hk⟩ hbox
    have hσk : σ k = σ i := by
      by_contra h
      exact hTB'x i k (Ne.symm h) a ha e hk hbox
    constructor
    · rintro ⟨l, hl, hel⟩
      rw [← hσk, ← hreg k l e hel hk]
      exact hl
    · intro hσi
      exact ⟨k, hσk.trans hσi, hk⟩
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
      exact hik (eq_of_mem_of_mem_of_disjoint_of_eq hG hσik (hP₁G i v hv) (hva ▸ ha'G k))
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
        · exact hik (eq_of_mem_of_mem_of_disjoint_of_eq hG hσik (ha'G i) (hvk' ▸ ha'G k))
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
      · exact hik (eq_of_mem_of_mem_of_disjoint_of_eq hG hσik (hP₁G i v hvi) (hP₁G k v hvk))
      · exact hik (eq_of_mem_of_mem_of_disjoint_of_eq hG hσik (hP₁G i v hvi) (hP₂G k v hvk))
      · exact hFδ i k hik hσik v (Or.inl hvi) (hD₂ k v hvk)
      · exact hik (eq_of_mem_of_mem_of_disjoint_of_eq hG hσik (hP₂G i v hvi) (hP₁G k v hvk))
      · exact hik (eq_of_mem_of_mem_of_disjoint_of_eq hG hσik (hP₂G i v hvi) (hP₂G k v hvk))
      · exact hFδ i k hik hσik v (Or.inr hvi) (hD₂ k v hvk)
      · exact hFδ k i hik.symm hσik.symm v (Or.inl hvk) (hD₂ i v hvi)
      · exact hFδ k i hik.symm hσik.symm v (Or.inr hvk) (hD₂ i v hvi)
      · exact hδδ i k hik hσik v (hD₂ i v hvi) (hD₂ k v hvk))
  exact ⟨a, b'', γ', hγ', hd'', fun i => ⟨hin i ▸ hJ i, mem_univ _⟩, ho''⟩


end Corridors

/-! ### The two-sided gluing with straight corridors, regions disjoint by colour -/

section Main

variable {j : ℕ}

/-- **The two-sided gluing with regions disjoint by colour** (as `exists_pos_le_law_two_sided`,
Nolin's Proposition 17). The same statement, with the gaps between corridors on one side asked to
exceed `W + 2S` only for arms of one colour, and `W + M + K + M' + K' + 2` for any two arms. The
families of the inner separation step satisfy this. Constant `c A ^ j`. -/
theorem exists_pos_le_law_two_sided_of_colour (σ : Fin j → Bool)
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
      (∀ i k, i ≠ k → σ i = σ k → t i = t k → x i + W + 2 * S < x k ∨ x k + W + 2 * S < x i) →
      (∀ i k, i ≠ k → t i = t k → x i + W + (M + K + M' + K' + 2) < x k ∨
        x k + W + (M + K + M' + K' + 2) < x i) →
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
    hrM hRR' hR'R₃ hA hWL hal hcor hgap hgap'
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
  have hmain := law_mul_mul_prod_le_law_of_two_sided_of_colour (σ := σ) (z := z) (r := r)
    (R := R) (s := s) (M := M) (K := K) (R' := R') (R₃ := R₃) (M' := M') (K' := K') (s' := s') q
    hσ hKM hM hK'M' hM'
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
    (fun i b hb => ((hfacts i).2.2.2.2.2.1 b hb).1)
    (fun i a ha => ((hfacts i).2.2.2.2.2.2 a ha).1)
    (fun i v hv => (hfacts i).2.2.2.1 v hv)
    (fun i k hik hσik => disjoint_two_sided_regions (by omega) (by omega) (hside i) (hside k)
      (hc0 i) (hc1 i) (hc0 k) (hc1 k) (hgap i k hik hσik))
    (fun i k hik => disjoint_left.2 fun e he he' => by
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
      exact disjoint_left.1 (disjoint_two_sided_boxes (by omega) (hside i)
        (hside k) (hc0 i) (hc1 i) (hc0 k) (hc1 k)
        (fun ht => (hgap' i k hik ht).imp (fun h => by omega) (fun h => by omega)))
        (mem_Icc_add_one_of_mem_Icc_add_cond (σ i) (he.1 v hv))
        (mem_Icc_add_one_of_mem_Icc_add_cond (σ k) (he'.1 v hv)))
    (fun i k hσik b hb e he hbox => by
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
      exact disjoint_left.1 (disjoint_two_sided_box_of_window (ρ' := R) (Mb := M) (Kb := K)
        (Gp := M + K + M' + K' + 2) le_rfl (by omega) (by omega) (by omega) (hside k)
        (hc0 i) (hc1 i) (hc0 k) (hc1 k) ⟨(hal i).1, (hal i).2.1⟩ hb
        (hgap' i k fun h => hσik (congrArg σ h)))
        (mem_Icc_add_one_of_mem_Icc_add_cond (σ k) (he.1 v hv)) (hbox v hv))
    (fun i k hσik a ha e he hbox => by
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
      exact disjoint_left.1 (disjoint_two_sided_box_of_window (ρ' := R') (Mb := M') (Kb := K')
        (Gp := M + K + M' + K' + 2) (by omega) (by omega) (by omega) (by omega) (hside k)
        (hc0 i) (hc1 i) (hc0 k) (hc1 k) ⟨(hal i).2.2.1, (hal i).2.2.2⟩ ha
        (hgap' i k fun h => hσik (congrArg σ h)))
        (mem_Icc_add_one_of_mem_Icc_add_cond (σ k) (he.1 v hv)) (hbox v hv))
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

end Main

end PercLib.Models.Planar
