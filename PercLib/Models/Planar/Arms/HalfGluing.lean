/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12) and
Section 4.6 (the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.HalfOuterSeparation
public import PercLib.Models.Planar.Arms.RotationGluing

/-!
# Gluing separated arms in a half-plane

The gluing of arms separated at the outer boundary of `B_R(z)`
(`law_mul_prod_le_law_of_corridors`, `law_mul_prod_le_law_of_regions`) for the arms of the
half-plane `{v | z₁ ≤ v₁}`, landing in increasing order, for colour sequences with no two
consecutive arms of one colour (`σ i ≠ σ (i + 1)`; the first and the last arm may have one colour,
as in `OCO`). The corridors and their continuations lie in the half-plane, so the glued arms do as
well.

The colour hypothesis of the plane (no two cyclically consecutive arms of one colour) enters the
plane's gluing only through the barrier (`notMem_support_of_mem_Icc`, an arm with the inner position
of one arm cannot land next to another arm of its colour) and the order. In the half-plane both come
from the barrier of `HalfOuterSeparation.lean` (`armsDisjoint_and_strictMono_of_innerPos_eq_half`,
with the virtual arm below the line).

## Main results

* `false_of_innerPos_eq_of_abs_lt_half`: an arm of the half-plane with the inner position of one arm
  does not land closer to another arm of its colour than every arm of the other colour.
* `strictMono_landingPos_of_innerPos_eq_half`: a disjoint family of arms of the half-plane to
  `∂B_{R'}(z)` with the colours and inner positions of a family to `∂B_R(z)` landing in increasing
  order lands in increasing order.
* `notMem_support_of_mem_Icc_half`: the fence-connection argument (barrier beyond the boundary).
* `exists_isArm_of_glue_half`: the glued family of arms of the half-plane.
* `law_mul_prod_le_law_of_corridors_half`: **the gluing through given corridors.**
* `law_mul_prod_le_law_of_regions_half`, `pow_mul_law_le_law_of_regions_half`: the gluing over
  disjoint regions of the half-plane.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ}

/-! ### Sectors and order in the half-plane -/

section Sectors

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **An arm stays in its sector** (half-plane). Let `γ` be a disjoint family of arms of the
half-plane to the boundary of `B_R(z)`, landing in increasing order, with no two consecutive arms
of one colour, and `i ≠ k` two arms of one colour. An arm of the half-plane with the inner position
of `γ k` cannot land closer to `γ i` than every arm of the other colour does. -/
theorem false_of_innerPos_eq_of_abs_lt_half
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (hrR : r < R)
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1)
    (ho : StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i))
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) {a' b' : LatticeSite 2}
    {W : (zdGraph 2).Walk a' b'} (hW : IsArm ω (σ i) z r (z - R) (z + R) W)
    (hWH : ∀ v ∈ W.support, z 1 ≤ v 1)
    (hin : innerPos z r (σ i) W = innerPos z r (σ k) (γ k))
    (hnear : ∀ l, σ l ≠ σ i → |landingPos (z - R) (z + R) (σ i) W -
      landingPos (z - R) (z + R) (σ i) (γ i)| < |landingPos (z - R) (z + R) (σ l) (γ l) -
        landingPos (z - R) (z + R) (σ i) (γ i)|) : False := by
  classical
  -- the family with arm `k` replaced by `W`
  set F : Fin j → Σ u v : LatticeSite 2, (zdGraph 2).Walk u v :=
    Function.update (fun m => ⟨a m, b m, γ m⟩) k ⟨a', b', W⟩ with hF
  have hFk : F k = ⟨a', b', W⟩ := Function.update_self _ _ _
  have hFm : ∀ m, m ≠ k → F m = ⟨a m, b m, γ m⟩ := fun m hm => Function.update_of_ne hm _ _
  have hγ' : ∀ m, IsArm ω (σ m) z r (z - R) (z + R) (F m).2.2 := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · rw [hFk]
      exact hσik ▸ hW
    · rw [hFm m hm]
      exact hγ m
  have hH' : ∀ m, ∀ v ∈ (F m).2.2.support, z 1 ≤ v 1 := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · rw [hFk]
      exact hWH
    · rw [hFm m hm]
      exact hH m
  have hin' : ∀ m, innerPos z r (σ m) (F m).2.2 = innerPos z r (σ m) (γ m) := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · rw [hFk]
      exact hσik ▸ hin
    · rw [hFm m hm]
  obtain ⟨-, hmono⟩ := armsDisjoint_and_strictMono_of_innerPos_eq_half hσ hrR hγ hd hH ho
    (γ' := fun m => (F m).2.2) hγ' hH' hin'
  have hLk : landingPos (z - R) (z + R) (σ k) (F k).2.2 = landingPos (z - R) (z + R) (σ i) W := by
    rw [hFk, hσik]
  rcases lt_or_gt_of_ne hik with hlt | hlt
  · -- `i < k`: the right neighbour of `i` lies between them
    have hik' : i.val + 1 < j := by have := k.2; have : i.val < k.val := hlt; omega
    obtain ⟨l, hl⟩ : ∃ l : Fin j, l.val = i.val + 1 := ⟨⟨i.val + 1, hik'⟩, rfl⟩
    have hσl : σ l ≠ σ i := fun h => hσ i l hl.symm h.symm
    have hlk : l ≠ k := fun h => hσl (by rw [h, hσik])
    have hil : i < l := by rw [Fin.lt_def]; omega
    have hlk' : l < k := by
      rw [Fin.lt_def]
      have : i.val < k.val := hlt
      have : l.val ≠ k.val := fun h => hlk (Fin.ext h)
      omega
    have h₁ : landingPos (z - R) (z + R) (σ i) (γ i) < landingPos (z - R) (z + R) (σ l) (γ l) :=
      ho hil
    have h₂ : landingPos (z - R) (z + R) (σ l) (F l).2.2 <
        landingPos (z - R) (z + R) (σ k) (F k).2.2 := hmono hlk'
    rw [hFm l hlk, hLk] at h₂
    dsimp only at h₂
    have h₃ := hnear l hσl
    rw [abs_lt] at h₃
    rw [abs_of_pos (by omega)] at h₃
    omega
  · -- `k < i`: the left neighbour of `i` lies between them
    have hi0 : 0 < i.val := by have : k.val < i.val := hlt; omega
    obtain ⟨l, hl⟩ : ∃ l : Fin j, l.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
    have hσl : σ l ≠ σ i := hσ l i (by omega)
    have hlk : l ≠ k := fun h => hσl (by rw [h, hσik])
    have hli : l < i := by rw [Fin.lt_def]; omega
    have hkl : k < l := by
      rw [Fin.lt_def]
      have : k.val < i.val := hlt
      have : l.val ≠ k.val := fun h => hlk (Fin.ext h)
      omega
    have h₁ : landingPos (z - R) (z + R) (σ l) (γ l) < landingPos (z - R) (z + R) (σ i) (γ i) :=
      ho hli
    have h₂ : landingPos (z - R) (z + R) (σ k) (F k).2.2 <
        landingPos (z - R) (z + R) (σ l) (F l).2.2 := hmono hkl
    rw [hFm l hlk, hLk] at h₂
    dsimp only at h₂
    have h₃ := hnear l hσl
    rw [abs_lt] at h₃
    rw [abs_of_neg (by omega)] at h₃
    omega

/-- **The order of a glued family** (half-plane). A disjoint family `γ'` of arms of the half-plane
to the boundary of `B_{R'}(z)` with the colours and the inner positions of a disjoint family `γ` of
arms of the half-plane to the boundary of `B_R(z)` landing in increasing order lands in increasing
order. The virtual arm below the line (`exists_isArm_virtual`), at both radii, lands below every arm
of the half-plane and has the same inner position at both radii, so the order invariance for three
arms (`sbtw_innerPos_iff_sbtw_landingPos_three`) transfers the order. -/
theorem strictMono_landingPos_of_innerPos_eq_half {R' : ℕ} (hrR : r < R) (hrR' : r < R')
    (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1)
    (ho : StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i))
    {a' b' : Fin j → LatticeSite 2} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (hγ' : ∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) (hd' : ArmsDisjoint σ γ')
    (hH' : ∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1)
    (hin : ∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) :
    StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i) := by
  classical
  have hB : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R + 1) (z + R - 1) :=
    Icc_subset_Icc_add_one_sub_one hrR
  have hB' : Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (z - R' + 1) (z + R' - 1) :=
    Icc_subset_Icc_add_one_sub_one hrR'
  -- the virtual arm below the line, open, at both radii
  obtain ⟨aV, bV, V, hV, hVs, hVt, hLV, hIV⟩ := exists_isArm_virtual (z := z) true hrR ω
  obtain ⟨aV', bV', V', hV', hVs', hVt', hLV', hIV'⟩ := exists_isArm_virtual (z := z) true hrR' ω
  obtain ⟨ω', hω'⟩ : ∃ ω' : Config (LatticeSite 2), ω' = (ω ∩ {e | ∀ v ∈ e, z 1 ≤ v 1}) ∪
      cond true {e | ∃ t : ℤ, t + 1 ≤ z 1 - r ∧ e = s(![z 0, t], ![z 0, t + 1])} ∅ := ⟨_, rfl⟩
  rw [← hω'] at hV hV'
  have hagree : ∀ e ∈ (zdGraph 2).edgeSet, (∀ v ∈ e, z 1 ≤ v 1) → (e ∈ ω ↔ e ∈ ω') := by
    intro e _ he
    rw [hω']
    refine ⟨fun h => Or.inl ⟨h, he⟩, fun h => ?_⟩
    rcases h with ⟨h, -⟩ | h
    · exact h
    · obtain ⟨t, ht, rfl⟩ := h
      have := he _ (Sym2.mem_mk_left _ _)
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      omega
  have hup : ∀ {c : Bool} {x y : LatticeSite 2} {lo hi : LatticeSite 2}
      {W : (zdGraph 2).Walk x y}, IsArm ω c z r lo hi W → (∀ v ∈ W.support, z 1 ≤ v 1) →
      IsArm ω' c z r lo hi W := fun h hW => h.of_agree_of_le hW hagree
  -- the virtual arms are disjoint from the open arms of the half-plane
  have hVd : ∀ {x y : LatticeSite 2} {lo hi : LatticeSite 2} {aU bU : LatticeSite 2}
      (U : (zdGraph 2).Walk aU bU), (∀ v ∈ U.support, v 0 = z 0 ∧ v 1 ≤ z 1 - r - cond true 0 1) →
      (∀ v ∈ U.support.tail, v 1 < z 1 - r - cond true 0 1) →
      Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (lo + 1) (hi - 1) →
      ∀ (W : (zdGraph 2).Walk x y), IsArm ω true z r lo hi W → (∀ v ∈ W.support, z 1 ≤ v 1) →
      (∀ v ∈ cond true W.support.tail W.support, v ∉ U.support) ∧
        ∀ v ∈ cond true U.support.tail U.support, v ∉ W.support := by
    intro x y lo hi aU bU U hUs hUt _ W hW hWH
    refine ⟨fun v hv hv' => ?_, fun v hv hv' => ?_⟩
    · have h₁ := hWH v (List.mem_of_mem_tail hv)
      obtain ⟨h₂, h₃⟩ := hUs v hv'
      simp only [Bool.cond_true] at h₃
      have hW' : IsOpenArm ω z r lo hi W := hW
      refine hW'.isCrossing.notMem_of_mem_tail v hv ?_
      rw [mem_Icc_two_iff]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
      omega
    · have h₁ := hWH v hv'
      have h₂ := hUt v hv
      simp only [Bool.cond_true] at h₂
      omega
  have hVpair : ∀ {x y : LatticeSite 2} {lo hi : LatticeSite 2} {aU bU : LatticeSite 2}
      (U : (zdGraph 2).Walk aU bU), (∀ v ∈ U.support, v 0 = z 0 ∧ v 1 ≤ z 1 - r - cond true 0 1) →
      (∀ v ∈ U.support.tail, v 1 < z 1 - r - cond true 0 1) →
      Icc (z - (r : LatticeSite 2)) (z + r) ⊆ Icc (lo + 1) (hi - 1) →
      ∀ {c : Bool} (W : (zdGraph 2).Walk x y), IsArm ω c z r lo hi W →
      (∀ v ∈ W.support, z 1 ≤ v 1) → c = true →
      (∀ v ∈ cond c W.support.tail W.support, v ∉ U.support) ∧
        ∀ v ∈ cond c U.support.tail U.support, v ∉ W.support := by
    intro x y lo hi aU bU U hUs hUt hBB c W hW hWH hc
    subst hc
    exact hVd U hUs hUt hBB W hW hWH
  have hL := fun i => (hγ i).landingPos_mem_Icc_of_half hrR (hH i)
  have hL' := fun i => (hγ' i).landingPos_mem_Icc_of_half hrR' (hH' i)
  intro i k hik
  have hik' : i ≠ k := ne_of_lt hik
  have e := sbtw_innerPos_iff_sbtw_landingPos_three hB (hup (hγ i) (hH i))
    (hup (hγ k) (hH k)) hV (fun h => hd.pair hik' h) (hVpair V hVs hVt hB (γ i) (hγ i) (hH i))
    (hVpair V hVs hVt hB (γ k) (hγ k) (hH k))
  have e' := sbtw_innerPos_iff_sbtw_landingPos_three hB' (hup (hγ' i) (hH' i))
    (hup (hγ' k) (hH' k)) hV' (fun h => hd'.pair hik' h)
    (hVpair V' hVs' hVt' hB' (γ' i) (hγ' i) (hH' i))
    (hVpair V' hVs' hVt' hB' (γ' k) (hγ' k) (hH' k))
  rw [hin i, hin k, hIV', ← hIV] at e'
  have hLik : landingPos (z - R) (z + R) (σ i) (γ i) <
      landingPos (z - R) (z + R) (σ k) (γ k) := ho hik
  have h₁ := (hL i).1
  simp only [Bool.cond_true] at hLV hLV'
  have h₂ := e'.1 (e.2 (by rw [Int.sbtw_iff, hLV]; omega))
  rw [Int.sbtw_iff, hLV'] at h₂
  have h₃ := (hL' i).1
  have h₄ := (hL' k).1
  change landingPos (z - R') (z + R') (σ i) (γ' i) < landingPos (z - R') (z + R') (σ k) (γ' k)
  omega

end Sectors

/-! ### The glued family -/

section Glue

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **The fence-connection argument in the half-plane** (`notMem_support_of_mem_Icc` for the arms
of a half-plane, without packs in the linear order). Let `γ` be a disjoint family of arms of the
half-plane to the boundary of `B_R(z)`, landing in increasing order, with landing positions more
than `2M` apart and more than `2M` from the doubled corners, and `r + M + 1 < R`. A walk `P` in the
half-plane, of the colour of arm `i`, starting at a vertex (face) of arm `i` within sup-distance `M`
of its end, whose points in `Icc (z - R - 1) (z + R)` lie within sup-distance `M` of that end,
meets no other arm of the colour of `i`. -/
theorem notMem_support_of_mem_Icc_half
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {M : ℕ}
    (hrM : r + M + 1 < R) (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i))
    (hd : ArmsDisjoint σ γ) (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1)
    (ho : StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i))
    (hsep : ∀ i k, i ≠ k → 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    (hcor : ∀ i (m : ℕ), 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R|)
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) {x y : LatticeSite 2}
    (P : (zdGraph 2).Walk x y) (hx : x ∈ (γ i).support)
    (hxM : x ∈ Icc (b i - M) (b i + M))
    (hP : ∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω))
    (hPH : ∀ v ∈ P.support, z 1 ≤ v 1)
    (hloc : ∀ v ∈ P.support, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b i - M) (b i + M)) :
    ∀ v ∈ P.support, v ∉ (γ k).support := by
  intro v hvP hvk
  have hrR : r < R := by omega
  have hB := Icc_subset_Icc_add_one_sub_one (z := z) hrR
  obtain ⟨hcri, hEi⟩ := isArm_iff_cond.1 (hγ i)
  have hγk : IsArm ω (σ i) z r (z - R) (z + R) (γ k) := hσik ▸ hγ k
  obtain ⟨hcrk, hEk⟩ := isArm_iff_cond.1 hγk
  have hBS : ∀ w ∈ Icc (b i - M) (b i + M),
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) :=
    fun w hw hwS => notMem_Icc_of_mem_Icc_end (hγ i) hrM hw (mem_Icc_of_mem_cond_Icc hwS)
  have hPS : ∀ w ∈ P.support,
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) := by
    intro w hw hwS
    refine hBS w (hloc w hw ?_) hwS
    have := mem_Icc_of_mem_cond_Icc hwS
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at this ⊢
    omega
  have hvM : v ∈ Icc (b i - M) (b i + M) := hloc v hvP (hγk.mem_Icc_of_mem_support hB hvk)
  -- split the arms and the walk
  obtain ⟨Q, Sk, hQS⟩ : ∃ (Q : (zdGraph 2).Walk (a k) v) (Sk : (zdGraph 2).Walk v (b k)),
      Q.append Sk = γ k := ⟨_, _, SimpleGraph.Walk.take_spec _ hvk⟩
  obtain ⟨P₁, P₂, hP₁₂⟩ : ∃ (P₁ : (zdGraph 2).Walk x v) (P₂ : (zdGraph 2).Walk v y),
      P₁.append P₂ = P := ⟨_, _, SimpleGraph.Walk.take_spec _ hvP⟩
  obtain ⟨q', s', hq's'⟩ : ∃ (q' : (zdGraph 2).Walk (a i) x) (s' : (zdGraph 2).Walk x (b i)),
      q'.append s' = γ i := ⟨_, _, SimpleGraph.Walk.take_spec _ hx⟩
  have hQnil : ¬Q.Nil := fun h => hBS v hvM (h.eq ▸ hcrk.start_mem)
  have hq'nil : ¬q'.Nil := fun h => hBS x hxM (h.eq ▸ hcri.start_mem)
  have hP₁ : ∀ w ∈ P₁.support, w ∈ P.support := fun w hw => by
    rw [← hP₁₂, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw
  -- the walk from the start of arm `k` to the end of arm `i`
  set W := Q.append (P₁.reverse.append s') with hW
  have hWE : ∀ e ∈ W.edges, e ∈ cond (σ i) ω (dualConfig ω) := by
    intro e he
    rw [hW, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_append, List.mem_reverse] at he
    rcases he with he | he | he
    · refine hEk e ?_
      rw [← hQS, SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    · refine hP e ?_
      rw [← hP₁₂, SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ he
    · refine hEi e ?_
      rw [← hq's', SimpleGraph.Walk.edges_append]
      exact List.mem_append_right _ he
  have hWH : ∀ w ∈ W.support, z 1 ≤ w 1 := by
    intro w hw
    rw [hW, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
    rcases hw with hw | hw | hw
    · refine hH k w ?_
      rw [← hQS, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hw
    · exact hPH w (hP₁ w hw)
    · refine hH i w ?_
      rw [← hq's', SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr hw
  have hWS : ∀ w ∈ W.support.tail,
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) := by
    intro w hw
    rw [hW, SimpleGraph.Walk.tail_support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · refine hcrk.notMem_of_mem_tail w ?_
      rw [← hQS, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw
    · have hw' := List.mem_of_mem_tail hw
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] at hw'
      rcases hw' with hw' | hw'
      · exact hPS w (hP₁ w hw')
      · refine hcri.notMem_of_mem_tail w ?_
        rw [← hq's']
        exact SimpleGraph.Walk.mem_support_tail_append_of_mem_right s' hq'nil hw'
  -- its first exit from the interior of `B_R(z)`
  obtain ⟨e, q, t, hqt, heT, hqT⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := cond (σ i) (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)))
    W hcri.end_notMem
  have hqcr : q.IsCrossing _ _ := ⟨hcrk.start_mem, fun w hw => hWS w (by
      rw [← hqt, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw), heT, hqT⟩
  have hqarm : IsArm ω (σ i) z r (z - R) (z + R) q := isArm_iff_cond.2 ⟨hqcr, fun e' he' =>
    hWE e' (by rw [← hqt, SimpleGraph.Walk.edges_append]; exact List.mem_append_left _ he')⟩
  have hqH : ∀ w ∈ q.support, z 1 ≤ w 1 := fun w hw => hWH w (by
    rw [← hqt, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hw)
  have hqnil : ¬q.Nil := fun h =>
    heT (h.eq ▸ cond_Icc_subset_cond_Icc hrR hcrk.start_mem)
  -- its end is next to the end of arm `i`
  have heM : e ∈ Icc (b i - M) (b i + M) := by
    have he : e ∈ W.support := by
      rw [← hqt, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl q.end_mem_support
    rw [hW, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at he
    rcases he with he | he | he
    · rw [← hQS] at hcrk
      rw [hcrk.eq_of_mem_support_left he heT]
      exact hvM
    · exact hloc e (hP₁ e he) (hqarm.end_mem_Icc hB)
    · have hb : e = b i := hcri.eq_end_of_notMem (by
        rw [← hq's', SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inr he) heT
      rw [hb, mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      omega
  -- it has the inner position of arm `k`
  have hin : innerPos z r (σ i) q = innerPos z r (σ k) (γ k) := by
    calc innerPos z r (σ i) q = innerPos z r (σ i) (q.append t) :=
          (innerPos_append t hqnil).symm
      _ = innerPos z r (σ i) Q := by rw [hqt, hW, innerPos_append _ hQnil]
      _ = innerPos z r (σ i) (γ k) := by rw [← hQS, innerPos_append _ hQnil]
      _ = innerPos z r (σ k) (γ k) := by rw [hσik]
  -- and lands next to arm `i`: a contradiction with the sectors
  have hnear := abs_landingPos_sub_le hqarm (hγ i) hrR hrR heM (by omega) (hcor i)
  refine false_of_innerPos_eq_of_abs_lt_half hσ hrR hγ hd hH ho hik hσik hqarm hqH hin
    fun l hl => ?_
  exact lt_of_le_of_lt hnear (hsep l i fun h => hl (h ▸ rfl))

/-- **Gluing in the half-plane** (`exists_isArm_of_glue` for the arms of a half-plane, without
packs in the linear order). Let `γ` be a disjoint family of arms of the half-plane to the boundary
of `B_R(z)`, landing in increasing order, with landing positions more than `2M` apart and more than
`2M` from the doubled corners, `r + M + 1 < R`, `R + 2 ≤ R'`. Continue each arm `i` by a walk `P i`
in the half-plane, of its colour, from one of its vertices (faces) within sup-distance `M` of its
end, whose points in `Icc (z - R - 1) (z + R)` lie within sup-distance `M` of that end and whose
last point lies outside the interior of `B_{R'}(z)`; suppose the continuations of two arms of one
colour are disjoint. Then the arms up to `x i` followed by `P i`, cut where they first leave the
interior of `B_{R'}(z)`, form a disjoint family of arms of the half-plane to the boundary of
`B_{R'}(z)` with the inner positions of `γ`, landing in increasing order, each ending on its
continuation. -/
theorem exists_isArm_of_glue_half
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {M R' : ℕ}
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hγ : ∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i))
    (hd : ArmsDisjoint σ γ) (hH : ∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1)
    (ho : StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i))
    (hsep : ∀ i k, i ≠ k → 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|)
    (hcor : ∀ i (m : ℕ), 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R|)
    {x y : Fin j → LatticeSite 2} (P : ∀ i, (zdGraph 2).Walk (x i) (y i))
    (hx : ∀ i, x i ∈ (γ i).support) (hxM : ∀ i, x i ∈ Icc (b i - M) (b i + M))
    (hP : ∀ i, ∀ e ∈ (P i).edges, e ∈ cond (σ i) ω (dualConfig ω))
    (hPH : ∀ i, ∀ v ∈ (P i).support, z 1 ≤ v 1)
    (hloc : ∀ i, ∀ v ∈ (P i).support, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b i - M) (b i + M))
    (hy : ∀ i, y i ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
      (Icc (z - R') (z + R' - 1)))
    (hdisj : ∀ i k, i ≠ k → σ i = σ k → ∀ v ∈ (P i).support, v ∉ (P k).support) :
    ∃ (b' : Fin j → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i)) ∧
      (∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) ∧
      ∀ i, b' i ∈ (P i).support := by
  have hrR : r < R := by omega
  have hB := Icc_subset_Icc_add_one_sub_one (z := z) hrR
  -- the first part of each arm, up to `x i`
  choose q' s' hq's' using fun i => (⟨_, _, SimpleGraph.Walk.take_spec _ (hx i)⟩ :
    ∃ (q' : (zdGraph 2).Walk (a i) (x i)) (s' : (zdGraph 2).Walk (x i) (b i)),
      q'.append s' = γ i)
  have hcr := fun i => isArm_iff_cond.1 (hγ i)
  have hq'nil : ∀ i, ¬(q' i).Nil := fun i h => notMem_Icc_of_mem_Icc_end (hγ i) hrM (hxM i)
    (mem_Icc_of_mem_cond_Icc (h.eq ▸ (hcr i).1.start_mem))
  have hPS : ∀ i, ∀ w ∈ (P i).support,
      w ∉ cond (σ i) (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)) := by
    intro i w hw hwS
    have hw' := mem_Icc_of_mem_cond_Icc hwS
    refine notMem_Icc_of_mem_Icc_end (hγ i) hrM (hloc i w hw ?_) hw'
    rw [mem_Icc_two_iff] at hw' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hw' ⊢
    omega
  -- the glued walks, cut at their first exit from the interior of `B_{R'}(z)`
  choose e q t hqt heT hqT using fun i => SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
      (Icc (z - R') (z + R' - 1))) ((q' i).append (P i)) (hy i)
  have hmemt : ∀ i, ∀ w ∈ (q i).support.tail, w ∈ (γ i).support.tail ∨ w ∈ (P i).support := by
    intro i w hw
    have hw' : w ∈ ((q' i).append (P i)).support.tail := by
      rw [← hqt i, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw
    rw [SimpleGraph.Walk.tail_support_append, List.mem_append] at hw'
    rcases hw' with hw' | hw'
    · left
      rw [← hq's' i, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw'
    · exact Or.inr (List.mem_of_mem_tail hw')
  have hmem : ∀ i, ∀ w ∈ (q i).support, w ∈ (γ i).support ∨ w ∈ (P i).support := by
    intro i w hw
    rcases (SimpleGraph.Walk.mem_support_iff _).1 hw with rfl | hw
    · exact Or.inl (γ i).start_mem_support
    · rcases hmemt i w hw with h | h
      · exact Or.inl (List.mem_of_mem_tail h)
      · exact Or.inr h
  have hγ' : ∀ i, IsArm ω (σ i) z r (z - R') (z + R') (q i) := by
    intro i
    refine isArm_iff_cond.2 ⟨⟨(hcr i).1.start_mem, fun w hw => ?_, heT i, hqT i⟩, fun e' he' => ?_⟩
    · rcases hmemt i w hw with h | h
      · exact (hcr i).1.notMem_of_mem_tail w h
      · exact hPS i w h
    · have he'' : e' ∈ ((q' i).append (P i)).edges := by
        rw [← hqt i, SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ he'
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at he''
      rcases he'' with he'' | he''
      · refine (hcr i).2 e' ?_
        rw [← hq's' i, SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ he''
      · exact hP i e' he''
  have hH' : ∀ i, ∀ v ∈ (q i).support, z 1 ≤ v 1 := by
    intro i v hv
    rcases hmem i v hv with h | h
    · exact hH i v h
    · exact hPH i v h
  have hin : ∀ i, innerPos z r (σ i) (q i) = innerPos z r (σ i) (γ i) := by
    intro i
    have hqnil : ¬(q i).Nil := fun h => heT i (h.eq ▸ Icc_subset_cond_Icc hRR'
      ((hγ i).mem_Icc_of_mem_support hB (γ i).start_mem_support))
    rw [← innerPos_append (t i) hqnil, hqt i, innerPos_append _ (hq'nil i), ← hq's' i,
      innerPos_append _ (hq'nil i)]
  have hd' : ArmsDisjoint σ q := by
    have noMeet := fun {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) =>
      notMem_support_of_mem_Icc_half hσ hrM hγ hd hH ho hsep hcor hik hσik (P i) (hx i) (hxM i)
        (hP i) (hPH i) (hloc i)
    refine ⟨fun i k hik hσi hσk v hv hv' => ?_, fun i k hik hσi hσk v hv hv' => ?_⟩
    · rcases hmemt i v hv with h | h <;> rcases hmem k v hv' with h' | h'
      · exact hd.1 i k hik hσi hσk v h h'
      · exact noMeet hik.symm (hσk.trans hσi.symm) v h' (List.mem_of_mem_tail h)
      · exact noMeet hik (hσi.trans hσk.symm) v h h'
      · exact hdisj i k hik (hσi.trans hσk.symm) v h h'
    · rcases hmem i v hv with h | h <;> rcases hmem k v hv' with h' | h'
      · exact hd.2 i k hik hσi hσk v h h'
      · exact noMeet hik.symm (hσk.trans hσi.symm) v h' h
      · exact noMeet hik (hσi.trans hσk.symm) v h h'
      · exact hdisj i k hik (hσi.trans hσk.symm) v h h'
  refine ⟨e, q, hγ', hd', hH',
    strictMono_landingPos_of_innerPos_eq_half hrR (by omega) hγ hd hH ho hγ' hd' hH' hin, hin,
    fun i => ?_⟩
  rcases hmem i (e i) (q i).end_mem_support with h | h
  · exact absurd (Icc_subset_cond_Icc hRR' ((hγ i).mem_Icc_of_mem_support hB h)) (heT i)
  · exact h

end Glue

/-! ### Conditioning on the separated event of the half-plane -/

section Conditioning

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Measurability** of the separated event of the half-plane with confined ends and inner
windows. -/
theorem measurableSet_setOf_separated_half (σ : Fin j → Bool) (z : LatticeSite 2)
    (r R : ℕ) (s : ℝ) (M K : ℕ) (B : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ) :
    MeasurableSet {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  have : ∀ u v : LatticeSite 2, Countable ((zdGraph 2).Walk u v) := fun _ _ =>
    SimpleGraph.Walk.support_injective.countable
  refine measurableSet_setOfPred.2 (Measurable.exists fun a => Measurable.exists fun b =>
    Measurable.exists fun γ => ?_)
  have hsep : Measurable fun ω => ArmsOuterSeparated ω σ z R s M K γ :=
    measurable_const.and (measurable_const.and (Measurable.forall fun i =>
      measurableSet_setOfPred.1 (measurableSet_setOf_hasOuterFence _ z R M K (γ i))))
  exact (Measurable.forall fun i => measurableSet_setOfPred.1
    (measurableSet_setOf_isArm _ z r _ _ (γ i))).and (measurable_const.and (measurable_const.and
      (measurable_const.and (hsep.and (measurable_const.and measurable_const)))))

/-- **Conditioning on the separated event of the half-plane** (`law_mul_le_law_inter_of_mixed`
with the half-plane condition, the increasing order and inner windows): the event is positively
correlated with every measurable event `C` determined by the corridors `T` and upper for the mixed
order of the dual corridors `D`. -/
theorem law_mul_le_law_inter_of_mixed_half (q : Sym2 (LatticeSite 2) → unitInterval)
    (hKM : K ≤ M) {B : Fin j → Set (LatticeSite 2)} {J : Fin j → Set ℤ}
    {T D : Set (Sym2 (LatticeSite 2))}
    (hT : ∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTB : ∀ i, ∀ b ∈ B i, ∀ e ∈ T, (∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2))) → (e ∈ D ↔ σ i = false))
    {C : Set (Config (LatticeSite 2))} (hCm : MeasurableSet C)
    (hC : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ C → ω' ∈ C)
    (hCT : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * law q C ≤
    law q ({ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ∩ C) :=
  PercLib.Probability.prodBernoulli_mul_le_inter_of_mixed_of_determined q
    (fun _ _ h₀ h₁ h₂ hω => by
      obtain ⟨a, b, γ, hγ, hd, hH, ho, hsep, hB, hJ⟩ := hω
      obtain ⟨hγ', hsep'⟩ := separated_of_mixed_of_forall_mem hKM hT hTB h₀ h₁ h₂ hγ hsep hB
      exact ⟨a, b, γ, hγ', hd, hH, ho, hsep', hB, hJ⟩) hC hCT
    (measurableSet_setOf_separated_half σ z r R s M K B J) hCm

end Conditioning

/-! ### The gluing through given corridors -/

section Corridors

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing separated arms of the half-plane through given corridors**
(`law_mul_prod_le_law_of_corridors` for the arms of the half-plane `{v | z₁ ≤ v₁}`, landing in
increasing order, without two consecutive arms of one colour). The hypotheses are those of the
plane, with the regions `Q i` of the continuations and the boxes of radius `M` about the possible
ends in the half-plane (`hQH`, `hBH`). Then `P(separated in the half-plane, ends in B, inner
positions in J) · ∏ P(C i)` is at most the probability that there are `j` disjoint arms of the
half-plane to the boundary of `B_{R'}(z)`, landing in increasing order, with inner positions in
`J`, whose ends satisfy `Φ`. -/
theorem law_mul_prod_le_law_of_corridors_half (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {R' : ℕ} (hKM : K ≤ M) (hM : 1 ≤ M)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hs : 4 * (M : ℝ) ≤ s)
    (B : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ)
    (C : Fin j → Set (Config (LatticeSite 2))) (T : Fin j → Set (Sym2 (LatticeSite 2)))
    (Q : Fin j → Set (LatticeSite 2)) (Φ : Fin j → Config (LatticeSite 2) → LatticeSite 2 → Prop)
    (hCm : ∀ i, MeasurableSet (C i))
    (hCT : ∀ i (ω ω' : Config (LatticeSite 2)), ω ∩ T i = ω' ∩ T i → (ω ∈ C i ↔ ω' ∈ C i))
    (hCmono : ∀ i (ω ω' : Config (LatticeSite 2)), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω →
      ω ∈ C i → ω' ∈ C i)
    (hTT : ∀ i k, σ i = true → σ k = false → Disjoint (T i) (T k))
    (hT : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTB : ∀ i k, σ i ≠ σ k → ∀ b ∈ B i, ∀ e ∈ T k, ¬∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2)))
    (hQloc : ∀ i, ∀ b ∈ B i, ∀ v ∈ Q i, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b - M) (b + M))
    (hQH : ∀ i, ∀ v ∈ Q i, z 1 ≤ v 1)
    (hBH : ∀ i, ∀ b ∈ B i, ∀ v ∈ Icc (b - (M : LatticeSite 2)) (b + M), z 1 ≤ v 1)
    (hQdisj : ∀ (ω : Config (LatticeSite 2)) (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) → ArmsDisjoint σ γ →
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) →
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) →
      ArmsOuterSeparated ω σ z R s M K γ → (∀ i, b i ∈ B i) →
      ∀ i k, i ≠ k → σ i = σ k → ∀ v, (v ∈ Icc (b i - M) (b i + M) ∨ v ∈ Q i) →
        (v ∈ Icc (b k - M) (b k + M) ∨ v ∈ Q k) → False)
    (hhook : ∀ i, ∀ ω ∈ C i, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
      ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
        x ∈ Icc (b - M) (b + M) ∧ (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ v ∈ P.support, v ∈ Icc (b - M) (b + M) ∨ v ∈ Q i) ∧
        y ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) ∧
        ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
          (Icc (z - R') (z + R' - 1)) → Φ i ω v) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ∏ i, law q (C i) ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i)) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧ ∀ i, Φ i ω (b' i)} := by
  set D : Set (Sym2 (LatticeSite 2)) := {e | ∃ i, σ i = false ∧ e ∈ T i} with hD
  set Tall : Set (Sym2 (LatticeSite 2)) := {e | ∃ i, e ∈ T i} with hTall
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
        exact disjoint_left.1 (hTT i k hc hk) he hek
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
  -- Harris for the corridors
  have hprod : ∏ i, law q (C i) ≤ law q (⋂ i, C i) := by
    have := PercLib.Probability.prodBernoulli_prod_le_biInter_of_mixed q D Finset.univ
      (fun i _ => hmix i) (fun i _ => hCm i)
    simp only [Finset.mem_univ, iInter_true] at this
    exact this
  -- conditioning on the separated event
  have hcond := law_mul_le_law_inter_of_mixed_half (σ := σ) (z := z) (r := r) (R := R)
    (s := s) q hKM (B := B) (J := J) (T := Tall) (D := D)
    (fun e he => by
      obtain ⟨i, hi⟩ := he
      exact hT i e hi)
    (fun i b hb e he hbox => by
      obtain ⟨k, hk⟩ := he
      by_cases hik : σ i = σ k
      · constructor
        · rintro ⟨l, hl, hel⟩
          by_contra hσi
          have hσi' : σ i = true := by simpa using hσi
          exact disjoint_left.1 (hTT k l (hik ▸ hσi') hl) hk hel
        · intro hσi
          exact ⟨k, hik ▸ hσi, hk⟩
      · exact absurd hbox (hTB i k hik b hb e hk))
    hCIm hCI hCIT
  refine (mul_le_mul_right hprod _).trans (hcond.trans (measure_mono ?_))
  -- the gluing
  rintro ω ⟨⟨a, b, γ, hγ, hd, hH, ho, hsep, hB, hJ⟩, hωC⟩
  rw [mem_iInter] at hωC
  have hrR : r < R := by omega
  choose x y P hx hxM hP hPQ hy hΦ using fun i =>
    hhook i ω (hωC i) (a i) (b i) (γ i) (hγ i) (hB i) (hsep.2.2 i)
  have hsep' : ∀ i k, i ≠ k → 2 * (M : ℤ) < |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)| := by
    intro i k hik
    have h₁ := hsep.1 i k hik
    have h₂ : (4 * M : ℝ) ≤ ((|landingPos (z - R) (z + R) (σ i) (γ i) -
        landingPos (z - R) (z + R) (σ k) (γ k)| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      linarith
    have h₃ : (4 * M : ℤ) ≤ |landingPos (z - R) (z + R) (σ i) (γ i) -
        landingPos (z - R) (z + R) (σ k) (γ k)| := by exact_mod_cast h₂
    omega
  have hcor' : ∀ i (m : ℕ), 2 * (M : ℤ) <
      |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| := by
    intro i m
    have h₁ := hsep.2.1 i m
    have h₂ : (4 * M : ℝ) ≤ ((|landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      push_cast at h₁
      linarith
    have h₃ : (4 * M : ℤ) ≤ |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| := by
      exact_mod_cast h₂
    omega
  obtain ⟨b', γ', hγ', hd', hH', ho', hin, hb'⟩ := exists_isArm_of_glue_half hσ hrM hRR' hγ hd hH
    ho hsep' hcor' P hx hxM hP
    (fun i v hv => by
      rcases hPQ i v hv with h | h
      · exact hBH i (b i) (hB i) v h
      · exact hQH i v h)
    (fun i v hv hvR => by
      rcases hPQ i v hv with h | h
      · exact h
      · exact hQloc i (b i) (hB i) v h hvR)
    hy
    (fun i k hik hσik v hvi hvk => hQdisj ω a b γ hγ hd hH ho hsep hB i k hik hσik v
      (hPQ i v hvi) (hPQ k v hvk))
  refine ⟨a, b', γ', hγ', hd', hH', ho', fun i => hin i ▸ hJ i, fun i => hΦ i _ (hb' i) ?_⟩
  exact (isArm_iff_cond.1 (hγ' i)).1.end_notMem

end Corridors

/-! ### Gluing over disjoint regions of the half-plane -/

section Regions

variable {j : ℕ} {σ : Fin j → Bool} {R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing over disjoint regions of the half-plane** (`law_mul_prod_le_law_of_regions` for the
arms of the half-plane): `law_mul_prod_le_law_of_corridors_half` when each corridor's pairs, its
continuation region and the boxes of radius `M + 1` about the possible ends lie in a region `G i`
of the half-plane `{v | z₁ ≤ v₁}`, the regions of different arms disjoint. -/
theorem law_mul_prod_le_law_of_regions_half (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {R' : ℕ} (hKM : K ≤ M) (hM : 1 ≤ M)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hs : 4 * (M : ℝ) ≤ s)
    (B : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ)
    (C : Fin j → Set (Config (LatticeSite 2))) (T : Fin j → Set (Sym2 (LatticeSite 2)))
    (Q G : Fin j → Set (LatticeSite 2))
    (Φ : Fin j → Config (LatticeSite 2) → LatticeSite 2 → Prop)
    (hCm : ∀ i, MeasurableSet (C i))
    (hCT : ∀ i (ω ω' : Config (LatticeSite 2)), ω ∩ T i = ω' ∩ T i → (ω ∈ C i ↔ ω' ∈ C i))
    (hCmono : ∀ i (ω ω' : Config (LatticeSite 2)), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω →
      ω ∈ C i → ω' ∈ C i)
    (hT : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTG : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∈ G i)
    (hBG : ∀ i, ∀ b ∈ B i,
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G i)
    (hQG : ∀ i, Q i ⊆ G i) (hG : ∀ i k, i ≠ k → Disjoint (G i) (G k))
    (hGH : ∀ i, ∀ v ∈ G i, z 1 ≤ v 1)
    (hQloc : ∀ i, ∀ b ∈ B i, ∀ v ∈ Q i, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b - M) (b + M))
    (hhook : ∀ i, ∀ ω ∈ C i, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
      ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
        x ∈ Icc (b - M) (b + M) ∧ (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ v ∈ P.support, v ∈ Icc (b - M) (b + M) ∨ v ∈ Q i) ∧
        y ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) ∧
        ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
          (Icc (z - R') (z + R' - 1)) → Φ i ω v) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ∏ i, law q (C i) ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i)) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧ ∀ i, Φ i ω (b' i)} := by
  refine law_mul_prod_le_law_of_corridors_half q hσ hKM hM hrM hRR' hs B J C T Q Φ hCm hCT hCmono
    ?_ hT ?_ hQloc (fun i v hv => hGH i v (hQG i hv))
    (fun i b hb v hv => hGH i v (hBG i b hb (Icc_sub_add_subset_Icc_sub_add_succ b M hv))) ?_ hhook
  · intro i k hi hk
    have hik : i ≠ k := fun h => by
      rw [h, hk] at hi
      exact Bool.false_ne_true hi
    rw [disjoint_left]
    intro e he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact disjoint_left.1 (hG i k hik) (hTG i e he v hv) (hTG k e he' v hv)
  · intro i k hik b hb e he hbox
    have hik' : i ≠ k := fun h => hik (h ▸ rfl)
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact disjoint_left.1 (hG i k hik') (hBG i b hb (hbox v hv)) (hTG k e he v hv)
  · intro ω a b γ _ _ _ _ _ hB i k hik _ v hvi hvk
    have hmem : ∀ l, (v ∈ Icc (b l - M) (b l + M) ∨ v ∈ Q l) → v ∈ G l := fun l h => by
      rcases h with h | h
      · exact hBG l (b l) (hB l) (Icc_sub_add_subset_Icc_sub_add_succ (b l) M h)
      · exact hQG l h
    exact disjoint_left.1 (hG i k hik) (hmem i hvi) (hmem k hvk)

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞} {κ : ℕ}

/-- **A stage of moves for fixed bins in the half-plane** (`pow_mul_law_le_law_of_regions` for the
arms of the half-plane): given, for each arm `i`, a corridor of its colour in a region `G i` of the
half-plane, the regions pairwise disjoint, separated arms of the half-plane ending in the bins
`B i` are continued to arms of the half-plane to `∂B_{R'}(z)`, landing in increasing order, ending
in the targets `B' i` with outer fences `(M', K')`, at the cost `c κ ^ (6j)`. -/
theorem pow_mul_law_le_law_of_regions_half
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k)
    {R' M' K' : ℕ} (hKM : K ≤ M) (hM : 1 ≤ M) (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R')
    (hs : 4 * (M : ℝ) ≤ s) (J : Fin j → Set ℤ) (B B' G : Fin j → Set (LatticeSite 2))
    (hG : ∀ i k, i ≠ k → Disjoint (G i) (G k)) (hGH : ∀ i, ∀ v ∈ G i, z 1 ≤ v 1)
    (hcor : ∀ i, ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ G i) ∧
      (∀ b ∈ B i, Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G i) ∧
      Q ⊆ G i ∧
      (∀ b ∈ B i, ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
        v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
        IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
        ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
          x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond (σ i) (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            v ∈ B' i ∧
              HasOuterFence ω (σ i) z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i, ∀ v ∈ (γ' i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ' i)) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧
      ∀ i, b' i ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K' (γ' i)} := by
  classical
  choose C T Q hCm hCT hCmono hT hTG hBG hQG hQloc hhook hprob using hcor
  have hmain := law_mul_prod_le_law_of_regions_half (σ := σ) (z := z) (r := r) (R := R) (s := s)
    (M := M) (K := K) (R' := R') q hσ hKM hM hrM hRR' hs B J C T Q G
    (fun i ω v => v ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K'
      (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v))
    hCm hCT hCmono hT hTG hBG hQG hG hGH hQloc hhook
  have hprod : c κ ^ (6 * j) ≤ ∏ i, law q (C i) := by
    calc c κ ^ (6 * j) = ∏ _i : Fin j, c κ ^ 6 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
      _ ≤ ∏ i, law q (C i) := Finset.prod_le_prod fun i _ => hprob i
  calc c κ ^ (6 * j) * law q _ ≤ law q _ * ∏ i, law q (C i) := by
        rw [mul_comm]
        exact mul_le_mul' le_rfl hprod
    _ ≤ _ := hmain.trans (measure_mono fun ω hω => by
        obtain ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hω
        exact ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅, fun i => ⟨(h₆ i).1, (h₆ i).2.of_nil (γ' i)⟩⟩)

end Regions

end PercLib.Models.Planar
