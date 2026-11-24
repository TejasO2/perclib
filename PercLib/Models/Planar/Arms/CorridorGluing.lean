/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-23. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12).
-/
module

public import PercLib.Models.Planar.Arms.OuterGluing

/-!
# Gluing separated arms through corridors

Arms separated at the outer boundary of `B_R(z)` (`outerSeparatedArmEvent`) are extended to a
larger box `B_{R'}(z)` at the cost of a constant factor (Nolin's Proposition 12, straight case):
each arm is continued, through its fence, along a corridor of its colour that runs from the end of
the arm straight out to the boundary of `B_{R'}(z)`.

* **The gluing through given corridors** (`law_mul_prod_le_law_of_corridors`). For any family of
  corridor events (determined by given sets of pairs, increasing for open arms and decreasing for
  dual arms) and any regions, if open and dual corridors read disjoint pairs, avoid the interior of
  `B_R(z)` and the boxes about the ends of the other colour, and every fenced arm ending in its bin
  is continued on its corridor event by a walk of its colour through its region, then
  `P(separated, ends in the bins) · ∏ P(corridor i)` is at most the probability of `j` arms to the
  boundary of `B_{R'}(z)` with the old inner positions and ends satisfying any given property `Φ`.
  This is the part of the gluing that later corridor shapes (turning corridors, fences at
  `∂B_{R'}`) reuse.
* **Bins.** The end of a separated arm lies on a side of `B_R(z)`, at least `2M` from the corners,
  in one of `2A + 1` bins of width `W` on that side when `R ≤ A W` (`IsArm.exists_mem_bin`).
* **Straight corridors.** The corridor of a bin is the box of width `W` from the bin straight out to
  the boundary of `B_{R'}(z)`, crossed in its long direction in the configuration of the colour of
  the arm; the fence of the arm, of length `2K ≥ 2W`, crosses it (`exists_walk_of_corridor_top` and
  the three other sides). The geometric conditions of the gluing reduce to integer inequalities on
  the four sides (`false_of_corridor_of_corridor`, `false_of_box_of_corridor`,
  `false_of_region_of_region`); for arms of one colour near a common corner they use the absence of
  packs a second time: an arm of the other colour lands between them (`le_or_le_of_lt_of_lt`).

## Main results

* `law_mul_prod_le_law_of_corridors`: the gluing through given corridors.
* `pow_mul_law_le_law_multiArmEventIn_of_sides`: straight corridors for fixed bins.
* `exists_pos_le_law_multiArmEventIn_of_separated`: **the gluing statement**, `c₀ P(arms to
  ∂B_R(z) separated with separation s ≥ 4M and fences, inner positions in J) ≤ P(arms to
  ∂B_{R'}(z), inner positions in J)` for `1 ≤ W ≤ K ≤ M`, `2W + 2 ≤ M`, `r + M + 1 < R`,
  `R + M ≤ R' ≤ D R`, `R ≤ A W`, `R' ≤ L`, uniformly over laws with crossing bounds `c` up to `L`;
  `exists_pos_le_law_multiArmEvent_of_separated`: the same with `outerSeparatedArmEvent` and
  `multiArmEvent`.

## Implementation notes

* Bins and corridors are written out with explicit coordinates; a side of `B_R(z)` is described by
  a four-case disjunction (`hside`, top, right, bottom, left), and the dual colour shifts the bottom
  and left sides by one (`cond col 0 1`).
* The geometric lemmas are stated over `ℤ` and split by sides so that each `omega` call stays small.
* The colour sequence has no packs (`hσ`); the separation `s ≥ 4M` is what the outer separation
  step gives (`s = 4 √η N`, `M = ⌊√η N⌋`).
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Arms of one colour and the corners -/

section Between

variable {j : ℕ} {σ : Fin j → Bool} {f : Fin j → ℤ}

/-- **Between two arms of one colour there are arms of the other colour on both arcs.** For a
family without packs, landing in counterclockwise order at the integer positions `f`, and two arms
`i ≠ k` of one colour with `f k < f i`, some arm of the other colour lands strictly between them and
some arm of the other colour lands outside `[f k, f i]`. -/
theorem exists_lt_lt_of_eq (hσ : ∀ i, σ i ≠ σ (finRotate j i))
    (ho : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l)) {i k : Fin j} (hik : i ≠ k)
    (hσik : σ i = σ k) (hlt : f k < f i) :
    (∃ l, σ l ≠ σ i ∧ f k < f l ∧ f l < f i) ∧ ∃ l, σ l ≠ σ i ∧ (f l < f k ∨ f i < f l) := by
  set l₁ := finRotate j i
  set l₂ := finRotate j k
  have h₁ : σ l₁ ≠ σ i := (hσ i).symm
  have h₂ : σ l₂ ≠ σ i := fun h => hσ k (h.trans hσik).symm
  have hl₂i : l₂ ≠ i := fun h => h₂ (congrArg σ h)
  have hl₁k : l₁ ≠ k := fun h => h₁ ((congrArg σ h).trans hσik.symm)
  have s₃ : sbtw (f i) (f l₁) (f k) := sbtw_apply_finRotate_apply ho hik.symm hl₁k.symm
  have s₄ : sbtw (f k) (f l₂) (f i) := sbtw_apply_finRotate_apply ho hik hl₂i.symm
  rw [Int.sbtw_iff] at s₃ s₄
  exact ⟨⟨l₂, h₂, by omega, by omega⟩, l₁, h₁, by omega⟩

/-- **Arms of one colour on both sides of a corner.** In a family without packs landing in
counterclockwise order, with any two landing positions at least `S` apart and every landing
position at least `S` from the point `C`, two arms of one colour landing on both sides of `C` are
not both within `2S` of `C`. -/
theorem le_or_le_of_lt_of_lt (hσ : ∀ i, σ i ≠ σ (finRotate j i))
    (ho : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l)) {S : ℤ}
    (hsep : ∀ i k, i ≠ k → S ≤ |f i - f k|) {C : ℤ} (hC : ∀ l, S ≤ |f l - C|) {i k : Fin j}
    (hik : i ≠ k) (hσik : σ i = σ k) (hkC : f k < C) (hCi : C < f i) :
    C + 2 * S ≤ f i ∨ f k ≤ C - 2 * S := by
  obtain ⟨⟨l, hl, hkl, hli⟩, -⟩ := exists_lt_lt_of_eq hσ ho hik hσik (hkC.trans hCi)
  have hli' : l ≠ i := fun h => hl (congrArg σ h)
  have hlk' : l ≠ k := fun h => hl ((congrArg σ h).trans hσik.symm)
  have e₁ := hsep l i hli'
  have e₂ := hsep l k hlk'
  have e₃ := hC l
  rw [le_abs] at e₁ e₂ e₃
  omega

/-- **Arms of one colour on both sides of the corner at `0`.** In a family without packs landing in
counterclockwise order at positions in `[S, P - S]`, with any two landing positions at least `S`
apart, two arms of one colour are not within `2S` of `0` and of `P` respectively. -/
theorem le_or_le_of_lt (hσ : ∀ i, σ i ≠ σ (finRotate j i))
    (ho : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l)) {S P : ℤ}
    (hsep : ∀ i k, i ≠ k → S ≤ |f i - f k|) (hlo : ∀ l, S ≤ f l) (hhi : ∀ l, f l + S ≤ P)
    {i k : Fin j} (hik : i ≠ k) (hσik : σ i = σ k) (hlt : f k < f i) :
    f i + 2 * S ≤ P ∨ 2 * S ≤ f k := by
  obtain ⟨-, l, hl, hl'⟩ := exists_lt_lt_of_eq hσ ho hik hσik hlt
  have hli' : l ≠ i := fun h => hl (congrArg σ h)
  have hlk' : l ≠ k := fun h => hl ((congrArg σ h).trans hσik.symm)
  have e₁ := hsep l i hli'
  have e₂ := hsep l k hlk'
  have e₃ := hlo l
  have e₄ := hhi l
  rw [le_abs] at e₁ e₂
  omega

end Between

/-! ### Conditioning with inner windows -/

section Conditioning

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Measurability** of the separated event with confined ends and inner windows. -/
theorem measurableSet_setOf_separated_forall_mem_innerPos (σ : Fin j → Bool) (z : LatticeSite 2)
    (r R : ℕ) (s : ℝ) (M K : ℕ) (B : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ) :
    MeasurableSet {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
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
      (hsep.and (measurable_const.and measurable_const))))

/-- **Conditioning on the separated event with inner windows**: `law_mul_le_law_inter_of_mixed`
with the inner positions of the arms confined to sets `J i`. -/
theorem law_mul_le_law_inter_of_mixed_of_innerPos (q : Sym2 (LatticeSite 2) → unitInterval)
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
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * law q C ≤
    law q ({ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ∩ C) :=
  PercLib.Probability.prodBernoulli_mul_le_inter_of_mixed_of_determined q
    (fun _ _ h₀ h₁ h₂ hω => by
      obtain ⟨a, b, γ, hγ, hd, ho, hsep, hB, hJ⟩ := hω
      obtain ⟨hγ', hsep'⟩ := separated_of_mixed_of_forall_mem hKM hT hTB h₀ h₁ h₂ hγ hsep hB
      exact ⟨a, b, γ, hγ', hd, ho, hsep', hB, hJ⟩) hC hCT
    (measurableSet_setOf_separated_forall_mem_innerPos σ z r R s M K B J) hCm

end Conditioning

/-! ### Mixed order for events of one colour -/

section Mixed

variable {ι : Type*}

/-- An event determined by the coordinates in `T`, increasing, with `T` disjoint from `D`, is upper
for the mixed order of `D`. -/
theorem mixed_of_determined_of_increasing {T D : Set ι} {A : Set (Set ι)}
    (hAT : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ A ↔ ω' ∈ A)) (hA : ∀ ω ω', ω ⊆ ω' → ω ∈ A → ω' ∈ A)
    (hTD : Disjoint T D) : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A := by
  intro ω ω' h₁ _ hω
  set ω'' := (ω ∩ T) ∪ (ω' \ T) with hω''
  have h'' : ω'' ∈ A := by
    refine (hAT ω ω'' ?_).1 hω
    ext x
    simp only [hω'', mem_inter_iff, mem_union, mem_sdiff]
    tauto
  refine hA ω'' ω' (fun x hx => ?_) h''
  rcases hx with ⟨hxω, hxT⟩ | ⟨hx, -⟩
  · have hxD : x ∉ D := fun h => disjoint_left.1 hTD hxT h
    exact (h₁ ⟨hxω, hxD⟩).1
  · exact hx

/-- An event determined by the coordinates in `T`, decreasing, with `T ⊆ D`, is upper for the
mixed order of `D`. -/
theorem mixed_of_determined_of_decreasing {T D : Set ι} {A : Set (Set ι)}
    (hAT : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ A ↔ ω' ∈ A)) (hA : ∀ ω ω', ω' ⊆ ω → ω ∈ A → ω' ∈ A)
    (hTD : T ⊆ D) : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A := by
  intro ω ω' _ h₂ hω
  set ω'' := (ω' ∩ T) ∪ (ω \ T) with hω''
  have h'' : ω'' ∈ A := by
    refine hA ω ω'' (fun x hx => ?_) hω
    rcases hx with ⟨hxω, hxT⟩ | ⟨hx, -⟩
    · exact (h₂ ⟨hxω, hTD hxT⟩).1
    · exact hx
  refine (hAT ω'' ω' ?_).1 h''
  ext x
  simp only [hω'', mem_inter_iff, mem_union, mem_sdiff]
  tauto

end Mixed

/-! ### The gluing through given corridors -/

section Corridors

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing separated arms through given corridors.** Let `γ` range over the families of arms
separated at the outer boundary of `B_R(z)` (separation `s ≥ 4M`, fences of length `2K ≤ 2M` and
depth `M ≥ 1`), with ends in the sets `B i` and inner positions in the sets `J i`. For each arm `i`
let `C i` be an event (the corridor of arm `i`) determined by the pairs `T i`, increasing for an
open arm and decreasing for a dual arm, and `Q i` a region. Suppose that

* open and dual corridors read disjoint pairs (`hTT`), no corridor reads a pair with an end in the
  interior of `B_R(z)` (`hT`), and no corridor of one colour reads a pair inside the box of radius
  `M + 1` about a possible end of an arm of the other colour (`hTB`);
* on `C i`, every arm `γ` of colour `σ i` ending in `B i` and fenced is continued by a walk `P` of
  its colour (`hhook`) from a vertex (face) `x` of `γ` within `M` of its end, running through the
  box of radius `M` about the end and through `Q i`, ending outside the interior of `B_{R'}(z)`,
  whose points outside that interior satisfy `Φ i ω`;
* `Q i` meets `Icc (z - R - 1) (z + R)` only near the possible ends of arm `i` (`hQloc`), and for
  separated families, the regions of two arms of one colour are disjoint (`hQdisj`).

Then `P(separated, ends in B, inner positions in J) · ∏ P(C i)` is at most the probability that
there are `j` disjoint arms to the boundary of `B_{R'}(z)`, in counterclockwise order, with inner
positions in `J`, whose ends satisfy `Φ`. -/
theorem law_mul_prod_le_law_of_corridors (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' : ℕ} (hKM : K ≤ M) (hM : 1 ≤ M)
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
    (hQdisj : ∀ (ω : Config (LatticeSite 2)) (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) → ArmsDisjoint σ γ →
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) →
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
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ∏ i, law q (C i) ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ' i))
        (landingPos (z - R') (z + R') (σ k) (γ' k)) (landingPos (z - R') (z + R') (σ l) (γ' l))) ∧
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
  have hcond := law_mul_le_law_inter_of_mixed_of_innerPos (σ := σ) (z := z) (r := r) (R := R)
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
  rintro ω ⟨⟨a, b, γ, hγ, hd, ho, hsep, hB, hJ⟩, hωC⟩
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
  obtain ⟨b', γ', hγ', hd', ho', hin, hb'⟩ := exists_isArm_of_glue hσ hrM hRR' hγ hd ho hsep'
    hcor' P hx hxM hP
    (fun i v hv hvR => by
      rcases hPQ i v hv with h | h
      · exact h
      · exact hQloc i (b i) (hB i) v h hvR)
    hy
    (fun i k hik hσik v hvi hvk => hQdisj ω a b γ hγ hd ho hsep hB i k hik hσik v
      (hPQ i v hvi) (hPQ k v hvk))
  refine ⟨a, b', γ', hγ', hd', ho', fun i => hin i ▸ hJ i, fun i => hΦ i _ (hb' i) ?_⟩
  exact (isArm_iff_cond.1 (hγ' i)).1.end_notMem

end Corridors

/-! ### Corridor events -/

section CorridorEvents

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- The crossing of a box in the configuration of colour `col` (open edges for `col = true`, the
dual configuration for `col = false`) is measurable. -/
theorem measurableSet_preimage_cond_crossing (col : Bool) (d : Fin 2) (lo hi : LatticeSite 2) :
    MeasurableSet ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing d lo hi) := by
  cases col
  · exact measurable_dualConfig (measurableSet_crossing d lo hi)
  · exact measurableSet_crossing d lo hi

/-- The crossing of a box in the configuration of colour `col` is determined by the pairs with
both ends in the box, enlarged by one at its upper corner for the dual colour. -/
theorem preimage_cond_crossing_iff_of_inter_eq (col : Bool) (d : Fin 2) (lo hi : LatticeSite 2)
    {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + cond col 0 1)} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + cond col 0 1)}) :
    cond col ω (dualConfig ω) ∈ crossing d lo hi ↔
      cond col ω' (dualConfig ω') ∈ crossing d lo hi := by
  cases col
  · exact mem_crossing_iff_of_inter_eq le_rfl (dualConfig_inter_eq_of_inter_eq h)
  · simp only [Bool.cond_true, add_zero] at h ⊢
    exact mem_crossing_iff_of_inter_eq le_rfl h

/-- The crossing of a box in the configuration of colour `col` is increasing in `ω` for the open
colour and decreasing for the dual colour. -/
theorem cond_mem_crossing_of_cond_subset {col : Bool} {d : Fin 2} {lo hi : LatticeSite 2}
    {ω ω' : Config (LatticeSite 2)} (h : cond col ω ω' ⊆ cond col ω' ω)
    (hω : cond col ω (dualConfig ω) ∈ crossing d lo hi) :
    cond col ω' (dualConfig ω') ∈ crossing d lo hi := by
  cases col
  · exact crossing_mono (dualConfig_anti h) hω
  · exact crossing_mono h hω

namespace CrossingBounds

/-- **Corridors of either colour, bottom to top.** A box of width `w ≥ 1` and height at most `k w`
is crossed from bottom to top in the configuration of colour `col` with probability at least
`c k`. -/
theorem le_law_preimage_cond_crossing_one (h : CrossingBounds q L c) (col : Bool) (k : ℕ) {w : ℕ}
    (hw : 1 ≤ w) (hwL : (w : ℕ∞) ≤ L) {lo hi : LatticeSite 2} (h₁ : lo 1 ≤ hi 1)
    (h₁' : hi 1 ≤ lo 1 + k * w) (h₀ : lo 0 + w ≤ hi 0) :
    c k ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing 1 lo hi) := by
  cases col
  · exact h.le_law_dualConfig_crossing_one_of_le k hw hwL h₁ h₁' h₀
  · exact h.le_law_crossing_one_of_le k hw hwL h₁ h₁' h₀

/-- **Corridors of either colour, left to right.** -/
theorem le_law_preimage_cond_crossing_zero (h : CrossingBounds q L c) (col : Bool) (k : ℕ)
    {w : ℕ} (hw : 1 ≤ w) (hwL : (w : ℕ∞) ≤ L) {lo hi : LatticeSite 2} (h₀ : lo 0 ≤ hi 0)
    (h₀' : hi 0 ≤ lo 0 + k * w) (h₁ : lo 1 + w ≤ hi 1) :
    c k ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing 0 lo hi) := by
  cases col
  · exact h.le_law_dualConfig_crossing_zero_of_le k hw hwL h₀ h₀' h₁
  · exact h.le_law_crossing_zero_of_le k hw hwL h₀ h₀' h₁

end CrossingBounds

end CorridorEvents

/-! ### Hooks: from a fence into a corridor -/

section Hooks

/-- **From an arm through its fence into a corridor.** A connection from `x` to `u` inside the box
of radius `M` about `b`, a walk `f` from `u` inside that box, and a walk `V` meeting `f`, all of
configuration `ζ`, give a walk of `ζ` from `x` to the end of `V` through the box and `V`. -/
theorem exists_walk_of_mem_support_of_mem_support_fence {ζ : Config (LatticeSite 2)}
    {b x u v c d w : LatticeSite 2} {M : ℕ}
    (hxu : ζ ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (b - (M : LatticeSite 2)) (b + M)) x u)
    (f : (zdGraph 2).Walk u v) (hf : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M))
    (hfe : ∀ e ∈ f.edges, e ∈ ζ) (V : (zdGraph 2).Walk c d) (hVe : ∀ e ∈ V.edges, e ∈ ζ)
    (hwf : w ∈ f.support) (hwV : w ∈ V.support) :
    ∃ P : (zdGraph 2).Walk x d, (∀ e ∈ P.edges, e ∈ ζ) ∧
      ∀ y ∈ P.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ y ∈ V.support := by
  classical
  obtain ⟨p₁, hp₁, hp₁e⟩ := exists_walk_of_mem_localConn hxu
  obtain ⟨g, hg, hge⟩ := exists_walk_of_mem_support_of_mem_support V hwV V.end_mem_support
  refine ⟨p₁.append ((f.takeUntil w hwf).append g), fun e he => ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append, List.mem_append,
      List.mem_append] at he
    rcases he with he | he | he
    · exact hp₁e e he
    · exact hfe e (f.edges_takeUntil_subset_edges hwf he)
    · exact hVe e (hge e he)
  · rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.mem_support_append_iff] at hy
    rcases hy with hy | hy | hy
    · exact Or.inl (hp₁ y hy)
    · exact Or.inl (hf y (f.support_takeUntil_subset_support hwf hy))
    · exact Or.inr (hg y hy)

variable {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2} {R R' M K W : ℕ} {x₀ : ℤ}
  {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}

/-- **The hook on the top side.** On the bottom-top crossing of the corridor
`[x₀, x₀ + W] × [z₁ + R, z₁ + R']` in the configuration of colour `col`, an arm ending at `b` on the
top side of `B_R(z)`, in the columns of the corridor and at least `2M` from the corners, with an
outer fence of length `2K ≥ 2W` and depth `M`, is continued by a walk of its colour through the box
of radius `M` about `b` and the corridor, from one of its vertices (faces) within `M` of `b` to the
top row of the corridor. -/
theorem exists_walk_of_corridor_top (hM : 1 ≤ M) (hKM : K ≤ M) (hWK : W ≤ K) (hRM : R + M ≤ R')
    (hC : cond col ω (dualConfig ω) ∈ crossing 1 ![x₀, z 1 + R] ![x₀ + W, z 1 + R'])
    (hb₁ : b 1 = z 1 + R) (hb₀ : x₀ ≤ b 0) (hb₀' : b 0 ≤ x₀ + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
      x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![x₀, z 1 + R] : LatticeSite 2) ![x₀ + W, z 1 + R']) ∧
      y 1 = z 1 + R' := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 1 = z 1 + R ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1] ![b 0 + K, b 1 + M]) u v := by
    rcases hfen with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exfalso; omega
  obtain ⟨c', hc', hc'1, d, hd, hd1, hcd⟩ := hC
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := by
    intro y hy
    have := hfs y hy
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨w, hwf, hwV⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f V (x₀ := x₀) (x₁ := x₀ + W)
    (y₀ := b 1) (y₁ := b 1 + M) (by omega) (by omega)
    (fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by omega) (by omega)
    (fun y hy => by
      have := hV y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc'1; omega)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hd1; omega)
  obtain ⟨P, hPe, hPs⟩ :=
    exists_walk_of_mem_support_of_mem_support_fence hxu f hfB hfe V hVe hwf hwV
  refine ⟨x, d, P, hx, ?_, hPe, fun y hy => (hPs y hy).imp id (hV y), by simpa using hd1⟩
  obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
  exact hp x p.start_mem_support

/-- **The hook on the right side**, for the left-right crossing of the corridor
`[z₀ + R, z₀ + R'] × [x₀, x₀ + W]`. -/
theorem exists_walk_of_corridor_right (hM : 1 ≤ M) (hKM : K ≤ M) (hW : 1 ≤ W) (hWK : W ≤ K)
    (hRM : R + M ≤ R')
    (hC : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 + R, x₀] ![z 0 + R', x₀ + W])
    (hb₀ : b 0 = z 0 + R) (hb₁ : x₀ ≤ b 1) (hb₁' : b 1 ≤ x₀ + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
      x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![z 0 + R, x₀] : LatticeSite 2) ![z 0 + R', x₀ + W]) ∧
      y 0 = z 0 + R' := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 0 = z 0 + R ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0, b 1 - K] ![b 0 + M, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso; omega
    · exact h
    all_goals exfalso; omega
  obtain ⟨c', hc', hc'0, d, hd, hd0, hcd⟩ := hC
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := by
    intro y hy
    have := hfs y hy
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨w, hwV, hwf⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc V f (x₀ := b 0)
    (x₁ := b 0 + M) (y₀ := x₀) (y₁ := x₀ + W) (by omega) (by omega)
    (fun y hy => by
      have := hV y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by simp only [Matrix.cons_val_zero] at hc'0; omega)
    (by simp only [Matrix.cons_val_zero] at hd0; omega)
    (fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by omega) (by omega)
  obtain ⟨P, hPe, hPs⟩ :=
    exists_walk_of_mem_support_of_mem_support_fence hxu f hfB hfe V hVe hwf hwV
  refine ⟨x, d, P, hx, ?_, hPe, fun y hy => (hPs y hy).imp id (hV y), by simpa using hd0⟩
  obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
  exact hp x p.start_mem_support

/-- **The hook on the bottom side**, for the bottom-top crossing of the corridor
`[x₀, x₀ + W] × [z₁ - R' - δ, z₁ - R - δ]` (`δ = 1` for a dual arm, `0` for an open one), walked
from top to bottom. -/
theorem exists_walk_of_corridor_bottom (hM : 1 ≤ M) (hKM : K ≤ M) (hWK : W ≤ K)
    (hRM : R + M ≤ R')
    (hC : cond col ω (dualConfig ω) ∈ crossing 1 ![x₀, z 1 - R' - cond col 0 1]
      ![x₀ + W, z 1 - R - cond col 0 1])
    (hb₁ : b 1 = z 1 - R - cond col 0 1) (hb₀ : x₀ ≤ b 0) (hb₀' : b 0 ≤ x₀ + W)
    (hbR : b 0 + 2 * M ≤ z 0 + R) (hbL : z 0 - R + 2 * M ≤ b 0)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
      x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![x₀, z 1 - R' - cond col 0 1] : LatticeSite 2)
          ![x₀ + W, z 1 - R - cond col 0 1]) ∧
      y 1 = z 1 - R' - cond col 0 1 := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 1 = z 1 - R - cond col 0 1 ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - K, b 1 - M] ![b 0 + K, b 1]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩
    · exfalso; omega
    · exfalso; omega
    · exact h
    · exfalso; omega
  obtain ⟨c', hc', hc'1, d, hd, hd1, hcd⟩ := hC
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := by
    intro y hy
    have := hfs y hy
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨w, hwf, hwV⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc f V (x₀ := x₀) (x₁ := x₀ + W)
    (y₀ := b 1 - M) (y₁ := b 1) (by omega) (by omega)
    (fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by omega) (by omega)
    (fun y hy => by
      have := hV y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc'1; omega)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hd1; omega)
  have hwV' : w ∈ V.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact hwV
  obtain ⟨P, hPe, hPs⟩ := exists_walk_of_mem_support_of_mem_support_fence hxu f hfB hfe V.reverse
    (fun e he => hVe e (by rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he)) hwf hwV'
  refine ⟨x, c', P, hx, ?_, hPe, fun y hy => (hPs y hy).imp id fun h => hV y ?_,
    by simpa using hc'1⟩
  · obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
    exact hp x p.start_mem_support
  · rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h

/-- **The hook on the left side**, for the left-right crossing of the corridor
`[z₀ - R' - δ, z₀ - R - δ] × [x₀, x₀ + W]`, walked from right to left. -/
theorem exists_walk_of_corridor_left (hM : 1 ≤ M) (hKM : K ≤ M) (hW : 1 ≤ W) (hWK : W ≤ K)
    (hRM : R + M ≤ R')
    (hC : cond col ω (dualConfig ω) ∈ crossing 0 ![z 0 - R' - cond col 0 1, x₀]
      ![z 0 - R - cond col 0 1, x₀ + W])
    (hb₀ : b 0 = z 0 - R - cond col 0 1) (hb₁ : x₀ ≤ b 1) (hb₁' : b 1 ≤ x₀ + W)
    (hbT : b 1 + 2 * M ≤ z 1 + R) (hbB : z 1 - R + 2 * M ≤ b 1)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
      x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨
        v ∈ Icc (![z 0 - R' - cond col 0 1, x₀] : LatticeSite 2)
          ![z 0 - R - cond col 0 1, x₀ + W]) ∧
      y 0 = z 0 - R' - cond col 0 1 := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  obtain ⟨x, hx, u, v, hxu, hfen⟩ := hf
  obtain ⟨-, hu, hv, huv⟩ : b 0 = z 0 - R - cond col 0 1 ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
      cond col ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
        (Icc ![b 0 - M, b 1 - K] ![b 0, b 1 + K]) u v := by
    rcases hfen with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact h
  obtain ⟨c', hc', hc'0, d, hd, hd0, hcd⟩ := hC
  obtain ⟨V, hV, hVe⟩ := exists_walk_of_mem_localConn hcd
  obtain ⟨f, hfs, hfe⟩ := exists_walk_of_mem_localConn huv
  have hfB : ∀ y ∈ f.support, y ∈ Icc (b - (M : LatticeSite 2)) (b + M) := by
    intro y hy
    have := hfs y hy
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  obtain ⟨w, hwV, hwf⟩ := exists_mem_support_of_mem_Icc_of_mem_Icc V f (x₀ := b 0 - M)
    (x₁ := b 0) (y₀ := x₀) (y₁ := x₀ + W) (by omega) (by omega)
    (fun y hy => by
      have := hV y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by simp only [Matrix.cons_val_zero] at hc'0; omega)
    (by simp only [Matrix.cons_val_zero] at hd0; omega)
    (fun y hy => by
      have := hfs y hy
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega)
    (by omega) (by omega)
  have hwV' : w ∈ V.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact hwV
  obtain ⟨P, hPe, hPs⟩ := exists_walk_of_mem_support_of_mem_support_fence hxu f hfB hfe V.reverse
    (fun e he => hVe e (by rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he)) hwf hwV'
  refine ⟨x, c', P, hx, ?_, hPe, fun y hy => (hPs y hy).imp id fun h => hV y ?_,
    by simpa using hc'0⟩
  · obtain ⟨p, hp, -⟩ := exists_walk_of_mem_localConn hxu
    exact hp x p.start_mem_support
  · rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h

end Hooks

/-! ### Straight corridors from bins -/

section Straight

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- The coordinates of the vector `cond col 0 1`. -/
theorem cond_zero_one_apply (col : Bool) (m : Fin 2) :
    (cond col (0 : LatticeSite 2) 1) m = cond col (0 : ℤ) 1 := by
  cases col <;> rfl

/-- **Integer separation.** Separated arms with separation `s ≥ S`, `S` an integer, land at
least `S` apart and at least `S` from the doubled corners. -/
theorem ArmsOuterSeparated.le_abs_landingPos_sub {ω : Config (LatticeSite 2)}
    {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (h : ArmsOuterSeparated ω σ z R s M K γ) {S : ℤ} (hS : (S : ℝ) ≤ s) :
    (∀ i k, i ≠ k → S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k)|) ∧
    ∀ i (m : ℕ), S ≤ |landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| := by
  refine ⟨fun i k hik => ?_, fun i m => ?_⟩
  · have h₁ := h.1 i k hik
    have h₂ : (S : ℝ) ≤ ((|landingPos (z - R) (z + R) (σ i) (γ i) -
        landingPos (z - R) (z + R) (σ k) (γ k)| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      push_cast at h₁
      linarith
    exact_mod_cast h₂
  · have h₁ := h.2.1 i m
    have h₂ : (S : ℝ) ≤ ((|landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      push_cast at h₁
      linarith
    exact_mod_cast h₂

/-! ### The integer geometry of straight corridors

In the next three lemmas an arm is described by its colour offset `e` (`0` open, `1` dual), the
start `x` of its bin, its end `(p0, p1)`, its corridor `[X0, X1] × [Y0, Y1]` and its landing
  position
`L`, as one of four cases (top, right, bottom, left side of `B_R(z)`, `z = (z0, z1)`), the corridor
running straight out to the boundary of `B_{R'}(z)`. -/

/-- **Open and dual corridors are disjoint.** The pairs read by the corridor of an open arm and of a
dual arm (the dual corridor enlarged by one at its upper corner) are disjoint when the arms land at
least `4M` apart. -/
theorem false_of_corridor_of_corridor {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : e = 0) (he' : e' = 1)
    (h : ((p1 = z1 + R ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R') ∧
        L = 8 * R + 2 * (z0 + R) - (2 * p0 + e)) ∨
      ((p0 = z0 + R ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
        X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W) ∧
        L = 4 * R + (2 * p1 + e) - 2 * (z1 - R)) ∨
      ((p1 = z1 - R - e ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
        X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e) ∧
        L = 2 * p0 + e - 2 * (z0 - R)) ∨
      ((p0 = z0 - R - e ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
        X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W) ∧
        L = 12 * R + 2 * (z1 + R) - (2 * p1 + e)))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 4 * M ≤ |L - L'|) (hv : X0 ≤ v0 ∧ v0 ≤ X1 + e ∧ Y0 ≤ v1 ∧ v1 ≤ Y1 + e)
    (hv' : X0' ≤ v0 ∧ v0 ≤ X1' + e' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1' + e') : False := by
  rw [le_abs] at hs
  rcases h with h | h | h | h <;> rcases h' with h' | h' | h' | h' <;> omega

/-- `false_of_box_of_corridor` when the first arm ends on the top side. -/
theorem false_of_box_of_corridor_top {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L c0 c1 : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : e = 0 ∧ e' = 1 ∨ e = 1 ∧ e' = 0)
    (h : (p1 = z1 + R ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧ X0 = x ∧
      Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R') ∧
      L = 8 * R + 2 * (z0 + R) - (2 * p0 + e))
    (hc : c1 = z1 + R ∧ x ≤ c0 ∧ c0 ≤ x + W ∧ z0 - R + 2 * M ≤ c0 ∧ c0 + 2 * M ≤ z0 + R ∧ X0 = x ∧
      Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R')
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 4 * M ≤ |L - L'|)
    (hv : c0 - M ≤ v0 ∧ v0 ≤ c0 + M + 1 ∧ c1 - M ≤ v1 ∧ v1 ≤ c1 + M + 1)
    (hv' : X0' ≤ v0 ∧ v0 ≤ X1' + e' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1' + e') : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h' <;> omega

/-- `false_of_box_of_corridor` when the first arm ends on the right side. -/
theorem false_of_box_of_corridor_right {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L c0 c1 : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : e = 0 ∧ e' = 1 ∨ e = 1 ∧ e' = 0)
    (h : (p0 = z0 + R ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
      X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W) ∧
      L = 4 * R + (2 * p1 + e) - 2 * (z1 - R))
    (hc : c0 = z0 + R ∧ x ≤ c1 ∧ c1 ≤ x + W ∧ z1 - R + 2 * M ≤ c1 ∧ c1 + 2 * M ≤ z1 + R ∧
      X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W)
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 4 * M ≤ |L - L'|)
    (hv : c0 - M ≤ v0 ∧ v0 ≤ c0 + M + 1 ∧ c1 - M ≤ v1 ∧ v1 ≤ c1 + M + 1)
    (hv' : X0' ≤ v0 ∧ v0 ≤ X1' + e' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1' + e') : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h' <;> omega

/-- `false_of_box_of_corridor` when the first arm ends on the bottom side. -/
theorem false_of_box_of_corridor_bottom {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L c0 c1 : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : e = 0 ∧ e' = 1 ∨ e = 1 ∧ e' = 0)
    (h : (p1 = z1 - R - e ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e) ∧
      L = 2 * p0 + e - 2 * (z0 - R))
    (hc : c1 = z1 - R - e ∧ x ≤ c0 ∧ c0 ≤ x + W ∧ z0 - R + 2 * M ≤ c0 ∧ c0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e)
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 4 * M ≤ |L - L'|)
    (hv : c0 - M ≤ v0 ∧ v0 ≤ c0 + M + 1 ∧ c1 - M ≤ v1 ∧ v1 ≤ c1 + M + 1)
    (hv' : X0' ≤ v0 ∧ v0 ≤ X1' + e' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1' + e') : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h' <;> omega

/-- `false_of_box_of_corridor` when the first arm ends on the left side. -/
theorem false_of_box_of_corridor_left {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L c0 c1 : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : e = 0 ∧ e' = 1 ∨ e = 1 ∧ e' = 0)
    (h : (p0 = z0 - R - e ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
      X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W) ∧
      L = 12 * R + 2 * (z1 + R) - (2 * p1 + e))
    (hc : c0 = z0 - R - e ∧ x ≤ c1 ∧ c1 ≤ x + W ∧ z1 - R + 2 * M ≤ c1 ∧ c1 + 2 * M ≤ z1 + R ∧
      X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W)
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 4 * M ≤ |L - L'|)
    (hv : c0 - M ≤ v0 ∧ v0 ≤ c0 + M + 1 ∧ c1 - M ≤ v1 ∧ v1 ≤ c1 + M + 1)
    (hv' : X0' ≤ v0 ∧ v0 ≤ X1' + e' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1' + e') : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h' <;> omega

/-- **Corridors of one colour avoid the end boxes of the other colour.** The box of radius `M + 1`
about any point `(c0, c1)` of the bin of an arm (whose end `(p0, p1)` lies in the same bin) misses
  the
pairs read by the corridor of an arm of the other colour landing at least `4M` away. -/
theorem false_of_box_of_corridor {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L c0 c1 : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (hRR : R ≤ R') (he : e = 0 ∧ e' = 1 ∨ e = 1 ∧ e' = 0)
    (h : ((p1 = z1 + R ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R') ∧
        L = 8 * R + 2 * (z0 + R) - (2 * p0 + e)) ∨
      ((p0 = z0 + R ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
        X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W) ∧
        L = 4 * R + (2 * p1 + e) - 2 * (z1 - R)) ∨
      ((p1 = z1 - R - e ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
        X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e) ∧
        L = 2 * p0 + e - 2 * (z0 - R)) ∨
      ((p0 = z0 - R - e ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
        X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W) ∧
        L = 12 * R + 2 * (z1 + R) - (2 * p1 + e)))
    (hc : (c1 = z1 + R ∧ x ≤ c0 ∧ c0 ≤ x + W ∧ z0 - R + 2 * M ≤ c0 ∧ c0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R') ∨
      (c0 = z0 + R ∧ x ≤ c1 ∧ c1 ≤ x + W ∧ z1 - R + 2 * M ≤ c1 ∧ c1 + 2 * M ≤ z1 + R ∧
        X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W) ∨
      (c1 = z1 - R - e ∧ x ≤ c0 ∧ c0 ≤ x + W ∧ z0 - R + 2 * M ≤ c0 ∧ c0 + 2 * M ≤ z0 + R ∧
        X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e) ∨
      (c0 = z0 - R - e ∧ x ≤ c1 ∧ c1 ≤ x + W ∧ z1 - R + 2 * M ≤ c1 ∧ c1 + 2 * M ≤ z1 + R ∧
        X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 4 * M ≤ |L - L'|)
    (hv : c0 - M ≤ v0 ∧ v0 ≤ c0 + M + 1 ∧ c1 - M ≤ v1 ∧ v1 ≤ c1 + M + 1)
    (hv' : X0' ≤ v0 ∧ v0 ≤ X1' + e' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1' + e') : False := by
  rcases h with h | h | h | h <;> rcases hc with hc | hc | hc | hc
  · exact false_of_box_of_corridor_top hW hWM he h hc h' hs hv hv'
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · exact false_of_box_of_corridor_right hW hWM he h hc h' hs hv hv'
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · exact false_of_box_of_corridor_bottom hW hWM he h hc h' hs hv hv'
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · clear h' hs hv hv'
    omega
  · exact false_of_box_of_corridor_left hW hWM he h hc h' hs hv hv'

/-- `false_of_region_of_region` when the first arm ends on the top side. -/
theorem false_of_region_of_region_top {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L : ℤ}
    {x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : 0 ≤ e ∧ e ≤ 1)
    (h : (p1 = z1 + R ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧ X0 = x ∧
      Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R') ∧
      L = 8 * R + 2 * (z0 + R) - (2 * p0 + e))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e)) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e) - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e ∧ X1' = x' + W ∧ Y1' = z1 - R - e) ∧
        L' = 2 * q0 + e - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e ∧ Y0' = x' ∧ X1' = z0 - R - e ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e)))
    (hs : 8 * M ≤ |L - L'|)
    (hcor : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R →
      (L' < C → C < L → C + 8 * M ≤ L ∨ L' ≤ C - 8 * M) ∧
      (L < C → C < L' → C + 8 * M ≤ L' ∨ L ≤ C - 8 * M))
    (_hwr : ∀ P : ℤ, P = 16 * R → (L' < L → L + 8 * M ≤ P ∨ 8 * M ≤ L') ∧
      (L < L' → L' + 8 * M ≤ P ∨ 8 * M ≤ L))
    (hv : (p0 - M ≤ v0 ∧ v0 ≤ p0 + M ∧ p1 - M ≤ v1 ∧ v1 ≤ p1 + M) ∨
      (X0 ≤ v0 ∧ v0 ≤ X1 ∧ Y0 ≤ v1 ∧ v1 ≤ Y1))
    (hv' : (q0 - M ≤ v0 ∧ v0 ≤ q0 + M ∧ q1 - M ≤ v1 ∧ v1 ≤ q1 + M) ∨
      (X0' ≤ v0 ∧ v0 ≤ X1' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1')) : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h'
  · omega
  · have := (hcor (8 * R) (by omega)).1
    omega
  · omega
  · have := (hcor (12 * R) (by omega)).2
    omega

/-- `false_of_region_of_region` when the first arm ends on the right side. -/
theorem false_of_region_of_region_right {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L : ℤ}
    {x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : 0 ≤ e ∧ e ≤ 1)
    (h : (p0 = z0 + R ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
      X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W) ∧
      L = 4 * R + (2 * p1 + e) - 2 * (z1 - R))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e)) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e) - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e ∧ X1' = x' + W ∧ Y1' = z1 - R - e) ∧
        L' = 2 * q0 + e - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e ∧ Y0' = x' ∧ X1' = z0 - R - e ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e)))
    (hs : 8 * M ≤ |L - L'|)
    (hcor : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R →
      (L' < C → C < L → C + 8 * M ≤ L ∨ L' ≤ C - 8 * M) ∧
      (L < C → C < L' → C + 8 * M ≤ L' ∨ L ≤ C - 8 * M))
    (_hwr : ∀ P : ℤ, P = 16 * R → (L' < L → L + 8 * M ≤ P ∨ 8 * M ≤ L') ∧
      (L < L' → L' + 8 * M ≤ P ∨ 8 * M ≤ L))
    (hv : (p0 - M ≤ v0 ∧ v0 ≤ p0 + M ∧ p1 - M ≤ v1 ∧ v1 ≤ p1 + M) ∨
      (X0 ≤ v0 ∧ v0 ≤ X1 ∧ Y0 ≤ v1 ∧ v1 ≤ Y1))
    (hv' : (q0 - M ≤ v0 ∧ v0 ≤ q0 + M ∧ q1 - M ≤ v1 ∧ v1 ≤ q1 + M) ∨
      (X0' ≤ v0 ∧ v0 ≤ X1' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1')) : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h'
  · have := (hcor (8 * R) (by omega)).2
    omega
  · omega
  · have := (hcor (4 * R) (by omega)).1
    omega
  · omega

/-- `false_of_region_of_region` when the first arm ends on the bottom side. -/
theorem false_of_region_of_region_bottom {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L : ℤ}
    {x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : 0 ≤ e ∧ e ≤ 1)
    (h : (p1 = z1 - R - e ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e) ∧
      L = 2 * p0 + e - 2 * (z0 - R))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e)) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e) - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e ∧ X1' = x' + W ∧ Y1' = z1 - R - e) ∧
        L' = 2 * q0 + e - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e ∧ Y0' = x' ∧ X1' = z0 - R - e ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e)))
    (hs : 8 * M ≤ |L - L'|)
    (hcor : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R →
      (L' < C → C < L → C + 8 * M ≤ L ∨ L' ≤ C - 8 * M) ∧
      (L < C → C < L' → C + 8 * M ≤ L' ∨ L ≤ C - 8 * M))
    (hwr : ∀ P : ℤ, P = 16 * R → (L' < L → L + 8 * M ≤ P ∨ 8 * M ≤ L') ∧
      (L < L' → L' + 8 * M ≤ P ∨ 8 * M ≤ L))
    (hv : (p0 - M ≤ v0 ∧ v0 ≤ p0 + M ∧ p1 - M ≤ v1 ∧ v1 ≤ p1 + M) ∨
      (X0 ≤ v0 ∧ v0 ≤ X1 ∧ Y0 ≤ v1 ∧ v1 ≤ Y1))
    (hv' : (q0 - M ≤ v0 ∧ v0 ≤ q0 + M ∧ q1 - M ≤ v1 ∧ v1 ≤ q1 + M) ∨
      (X0' ≤ v0 ∧ v0 ≤ X1' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1')) : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h'
  · omega
  · have := (hcor (4 * R) (by omega)).2
    omega
  · omega
  · have := (hwr (16 * R) rfl).2
    omega

/-- `false_of_region_of_region` when the first arm ends on the left side. -/
theorem false_of_region_of_region_left {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L : ℤ}
    {x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : 0 ≤ e ∧ e ≤ 1)
    (h : (p0 = z0 - R - e ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
      X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W) ∧
      L = 12 * R + 2 * (z1 + R) - (2 * p1 + e))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e)) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e) - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e ∧ X1' = x' + W ∧ Y1' = z1 - R - e) ∧
        L' = 2 * q0 + e - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e ∧ Y0' = x' ∧ X1' = z0 - R - e ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e)))
    (hs : 8 * M ≤ |L - L'|)
    (hcor : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R →
      (L' < C → C < L → C + 8 * M ≤ L ∨ L' ≤ C - 8 * M) ∧
      (L < C → C < L' → C + 8 * M ≤ L' ∨ L ≤ C - 8 * M))
    (hwr : ∀ P : ℤ, P = 16 * R → (L' < L → L + 8 * M ≤ P ∨ 8 * M ≤ L') ∧
      (L < L' → L' + 8 * M ≤ P ∨ 8 * M ≤ L))
    (hv : (p0 - M ≤ v0 ∧ v0 ≤ p0 + M ∧ p1 - M ≤ v1 ∧ v1 ≤ p1 + M) ∨
      (X0 ≤ v0 ∧ v0 ≤ X1 ∧ Y0 ≤ v1 ∧ v1 ≤ Y1))
    (hv' : (q0 - M ≤ v0 ∧ v0 ≤ q0 + M ∧ q1 - M ≤ v1 ∧ v1 ≤ q1 + M) ∨
      (X0' ≤ v0 ∧ v0 ≤ X1' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1')) : False := by
  rw [le_abs] at hs
  rcases h' with h' | h' | h' | h'
  · have := (hcor (12 * R) (by omega)).1
    omega
  · omega
  · have := (hwr (16 * R) rfl).1
    omega
  · omega

/-- **Regions of arms of one colour are disjoint.** For two arms of one colour landing at least `8M`
apart, such that when they land on both sides of a corner `C` one of them lands at least `8M` from
`C` (`hcor`, `hwr`), the box of radius `M` about the end of one arm together with its corridor
  misses
the box about the end of the other together with its corridor. -/
theorem false_of_region_of_region {z0 z1 R R' M W e x p0 p1 X0 Y0 X1 Y1 L : ℤ}
    {e' x' q0 q1 X0' Y0' X1' Y1' L' v0 v1 : ℤ}
    (hW : 0 ≤ W) (hWM : 2 * W + 2 ≤ M) (he : 0 ≤ e ∧ e ≤ 1) (he' : e' = e)
    (h : ((p1 = z1 + R ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
      X0 = x ∧ Y0 = z1 + R ∧ X1 = x + W ∧ Y1 = z1 + R') ∧
        L = 8 * R + 2 * (z0 + R) - (2 * p0 + e)) ∨
      ((p0 = z0 + R ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
        X0 = z0 + R ∧ Y0 = x ∧ X1 = z0 + R' ∧ Y1 = x + W) ∧
        L = 4 * R + (2 * p1 + e) - 2 * (z1 - R)) ∨
      ((p1 = z1 - R - e ∧ x ≤ p0 ∧ p0 ≤ x + W ∧ z0 - R + 2 * M ≤ p0 ∧ p0 + 2 * M ≤ z0 + R ∧
        X0 = x ∧ Y0 = z1 - R' - e ∧ X1 = x + W ∧ Y1 = z1 - R - e) ∧
        L = 2 * p0 + e - 2 * (z0 - R)) ∨
      ((p0 = z0 - R - e ∧ x ≤ p1 ∧ p1 ≤ x + W ∧ z1 - R + 2 * M ≤ p1 ∧ p1 + 2 * M ≤ z1 + R ∧
        X0 = z0 - R' - e ∧ Y0 = x ∧ X1 = z0 - R - e ∧ Y1 = x + W) ∧
        L = 12 * R + 2 * (z1 + R) - (2 * p1 + e)))
    (h' : ((q1 = z1 + R ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
      X0' = x' ∧ Y0' = z1 + R ∧ X1' = x' + W ∧ Y1' = z1 + R') ∧
        L' = 8 * R + 2 * (z0 + R) - (2 * q0 + e')) ∨
      ((q0 = z0 + R ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 + R ∧ Y0' = x' ∧ X1' = z0 + R' ∧ Y1' = x' + W) ∧
        L' = 4 * R + (2 * q1 + e') - 2 * (z1 - R)) ∨
      ((q1 = z1 - R - e' ∧ x' ≤ q0 ∧ q0 ≤ x' + W ∧ z0 - R + 2 * M ≤ q0 ∧ q0 + 2 * M ≤ z0 + R ∧
        X0' = x' ∧ Y0' = z1 - R' - e' ∧ X1' = x' + W ∧ Y1' = z1 - R - e') ∧
        L' = 2 * q0 + e' - 2 * (z0 - R)) ∨
      ((q0 = z0 - R - e' ∧ x' ≤ q1 ∧ q1 ≤ x' + W ∧ z1 - R + 2 * M ≤ q1 ∧ q1 + 2 * M ≤ z1 + R ∧
        X0' = z0 - R' - e' ∧ Y0' = x' ∧ X1' = z0 - R - e' ∧ Y1' = x' + W) ∧
        L' = 12 * R + 2 * (z1 + R) - (2 * q1 + e')))
    (hs : 8 * M ≤ |L - L'|)
    (hcor : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R →
      (L' < C → C < L → C + 8 * M ≤ L ∨ L' ≤ C - 8 * M) ∧
      (L < C → C < L' → C + 8 * M ≤ L' ∨ L ≤ C - 8 * M))
    (hwr : ∀ P : ℤ, P = 16 * R → (L' < L → L + 8 * M ≤ P ∨ 8 * M ≤ L') ∧
      (L < L' → L' + 8 * M ≤ P ∨ 8 * M ≤ L))
    (hv : (p0 - M ≤ v0 ∧ v0 ≤ p0 + M ∧ p1 - M ≤ v1 ∧ v1 ≤ p1 + M) ∨
      (X0 ≤ v0 ∧ v0 ≤ X1 ∧ Y0 ≤ v1 ∧ v1 ≤ Y1))
    (hv' : (q0 - M ≤ v0 ∧ v0 ≤ q0 + M ∧ q1 - M ≤ v1 ∧ v1 ≤ q1 + M) ∨
      (X0' ≤ v0 ∧ v0 ≤ X1' ∧ Y0' ≤ v1 ∧ v1 ≤ Y1')) : False := by
  subst he'
  rcases h with h | h | h | h
  · exact false_of_region_of_region_top hW hWM he h h' hs hcor hwr hv hv'
  · exact false_of_region_of_region_right hW hWM he h h' hs hcor hwr hv hv'
  · exact false_of_region_of_region_bottom hW hWM he h h' hs hcor hwr hv hv'
  · exact false_of_region_of_region_left hW hWM he h h' hs hcor hwr hv hv'

/-! ### One straight corridor

In the next lemmas the corridor of an arm of colour `col` is described by `hside`: according to the
side of `B_R(z)` of its bin (top, right, bottom, left), the bin `B` is the set of possible ends on
  that
side whose coordinate along the side lies in `[x, x + W]`, at least `2M` from the corners, and the
corridor is the box `Icc lo hi` of width `W` from the bin straight out to the boundary of
`B_{R'}(z)`, crossed in direction `dir`. -/

/-- **The possible ends of a bin**, as integer facts. -/
theorem sideP_of_side {col : Bool} {z : LatticeSite 2} {R R' M W : ℕ} {x : ℤ} {dir : Fin 2}
    {lo hi : LatticeSite 2} {B : Set (LatticeSite 2)} {b : LatticeSite 2}
    (hside : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧ hi = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧ hi = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R))
    (hb : b ∈ B) :
    (b 1 = z 1 + (R : ℤ) ∧ x ≤ b 0 ∧ b 0 ≤ x + (W : ℤ) ∧ z 0 - (R : ℤ) + 2 * (M : ℤ) ≤ b 0 ∧
      b 0 + 2 * (M : ℤ) ≤ z 0 + (R : ℤ) ∧ lo 0 = x ∧ lo 1 = z 1 + (R : ℤ) ∧ hi 0 = x + (W : ℤ) ∧
        hi 1 = z 1 + (R' : ℤ)) ∨
      (b 0 = z 0 + (R : ℤ) ∧ x ≤ b 1 ∧ b 1 ≤ x + (W : ℤ) ∧ z 1 - (R : ℤ) + 2 * (M : ℤ) ≤ b 1 ∧
        b 1 + 2 * (M : ℤ) ≤ z 1 + (R : ℤ) ∧ lo 0 = z 0 + (R : ℤ) ∧ lo 1 = x ∧
          hi 0 = z 0 + (R' : ℤ) ∧ hi 1 = x + (W : ℤ)) ∨
      (b 1 = z 1 - (R : ℤ) - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + (W : ℤ) ∧
        z 0 - (R : ℤ) + 2 * (M : ℤ) ≤ b 0 ∧ b 0 + 2 * (M : ℤ) ≤ z 0 + (R : ℤ) ∧ lo 0 = x ∧
          lo 1 = z 1 - (R' : ℤ) - cond col 0 1 ∧ hi 0 = x + (W : ℤ) ∧
            hi 1 = z 1 - (R : ℤ) - cond col 0 1) ∨
      (b 0 = z 0 - (R : ℤ) - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + (W : ℤ) ∧
        z 1 - (R : ℤ) + 2 * (M : ℤ) ≤ b 1 ∧ b 1 + 2 * (M : ℤ) ≤ z 1 + (R : ℤ) ∧
          lo 0 = z 0 - (R' : ℤ) - cond col 0 1 ∧ lo 1 = x ∧ hi 0 = z 0 - (R : ℤ) - cond col 0 1 ∧
            hi 1 = x + (W : ℤ)) := by
  rcases hside with ⟨-, rfl, rfl, hB⟩ | ⟨-, rfl, rfl, hB⟩ | ⟨-, rfl, rfl, hB⟩ | ⟨-, rfl, rfl, hB⟩
    <;>
    rw [hB] at hb <;> obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hb <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact Or.inl ⟨h₁, h₂, h₃, h₄, h₅, trivial, trivial, trivial, trivial⟩
  · exact Or.inr (Or.inl ⟨h₁, h₂, h₃, h₄, h₅, trivial, trivial, trivial, trivial⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, h₄, h₅, trivial, trivial, trivial, trivial⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, h₄, h₅, trivial, trivial, trivial, trivial⟩))

/-- **The landing position of an arm ending in a bin**, as integer facts. -/
theorem IsArm.sideL_of_side {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2}
    {r R R' M W : ℕ} {x : ℤ} {dir : Fin 2} {lo hi : LatticeSite 2} {B : Set (LatticeSite 2)}
    {a b : LatticeSite 2}
    {γ : (zdGraph 2).Walk a b}
    (hγ : IsArm ω col z r (z - R) (z + R) γ) (hrR : r < R) (hM : 1 ≤ M)
    (hside : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧ hi = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧ hi = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R))
    (hb : b ∈ B) :
    ((b 1 = z 1 + (R : ℤ) ∧ x ≤ b 0 ∧ b 0 ≤ x + (W : ℤ) ∧ z 0 - (R : ℤ) + 2 * (M : ℤ) ≤ b 0 ∧
      b 0 + 2 * (M : ℤ) ≤ z 0 + (R : ℤ) ∧ lo 0 = x ∧ lo 1 = z 1 + (R : ℤ) ∧ hi 0 = x + (W : ℤ) ∧
        hi 1 = z 1 + (R' : ℤ)) ∧
        landingPos (z - R) (z + R) col γ = 8 * (R : ℤ) + 2 * (z 0 + (R : ℤ)) - (2 * b 0 + cond col
          0 1)) ∨
      ((b 0 = z 0 + (R : ℤ) ∧ x ≤ b 1 ∧ b 1 ≤ x + (W : ℤ) ∧ z 1 - (R : ℤ) + 2 * (M : ℤ) ≤ b 1 ∧
        b 1 + 2 * (M : ℤ) ≤ z 1 + (R : ℤ) ∧ lo 0 = z 0 + (R : ℤ) ∧ lo 1 = x ∧
          hi 0 = z 0 + (R' : ℤ) ∧ hi 1 = x + (W : ℤ)) ∧
        landingPos (z - R) (z + R) col γ = 4 * (R : ℤ) + (2 * b 1 + cond col 0 1) - 2 * (z 1 - (R :
          ℤ))) ∨
      ((b 1 = z 1 - (R : ℤ) - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + (W : ℤ) ∧
        z 0 - (R : ℤ) + 2 * (M : ℤ) ≤ b 0 ∧ b 0 + 2 * (M : ℤ) ≤ z 0 + (R : ℤ) ∧ lo 0 = x ∧
          lo 1 = z 1 - (R' : ℤ) - cond col 0 1 ∧ hi 0 = x + (W : ℤ) ∧
            hi 1 = z 1 - (R : ℤ) - cond col 0 1) ∧
        landingPos (z - R) (z + R) col γ = 2 * b 0 + cond col 0 1 - 2 * (z 0 - (R : ℤ))) ∨
      ((b 0 = z 0 - (R : ℤ) - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + (W : ℤ) ∧
        z 1 - (R : ℤ) + 2 * (M : ℤ) ≤ b 1 ∧ b 1 + 2 * (M : ℤ) ≤ z 1 + (R : ℤ) ∧
          lo 0 = z 0 - (R' : ℤ) - cond col 0 1 ∧ lo 1 = x ∧ hi 0 = z 0 - (R : ℤ) - cond col 0 1 ∧
            hi 1 = x + (W : ℤ)) ∧
        landingPos (z - R) (z + R) col γ = 12 * (R : ℤ) + 2 * (z 1 + (R : ℤ)) - (2 * b 1 + cond col
          0 1)) := by
  have h₁ := sideP_of_side hside hb
  have h₂ := hγ.landingPos_cases hrR
  have hc : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rcases h₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩ <;>
    first
    | (exfalso; omega)
    | exact Or.inl ⟨h₁, h₂'⟩
    | exact Or.inr (Or.inl ⟨h₁, h₂'⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂'⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨h₁, h₂'⟩))

/-- **A corridor misses the interior of `B_R(z)`**, together with the pairs it reads. -/
theorem notMem_Icc_of_side {col : Bool} {z : LatticeSite 2} {R R' M W : ℕ} {x : ℤ} {dir : Fin 2}
    {lo hi : LatticeSite 2} {B : Set (LatticeSite 2)} {v : LatticeSite 2}
    (hside : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧ hi = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧ hi = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R))
    (hv : v ∈ Icc lo (hi + cond col 0 1)) :
    v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
  have hc : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  intro hvI
  rw [mem_Icc_two_iff] at hv hvI
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvI
  simp only [Pi.add_apply, cond_zero_one_apply] at hv
  rcases hside with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv <;> omega

/-- **A corridor meets `Icc (z - R - 1) (z + R)` only next to its bin.** -/
theorem mem_Icc_of_side {col : Bool} {z : LatticeSite 2} {R R' M W : ℕ} {x : ℤ} {dir : Fin 2}
    {lo hi : LatticeSite 2} {B : Set (LatticeSite 2)} {b v : LatticeSite 2}
    (hside : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧ hi = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧ hi = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R))
    (hM : 1 ≤ M) (hWM : W ≤ M) (hb : b ∈ B) (hv : v ∈ Icc lo hi) (hvR : v ∈ Icc (z - R - 1) (z +
      R)) :
    v ∈ Icc (b - M) (b + M) := by
  have h₁ := sideP_of_side hside hb
  have hc : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rw [mem_Icc_two_iff] at hv hvR ⊢
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvR ⊢
  omega

/-- **The hook into a straight corridor**, on any side: on the crossing of the corridor, an arm
  ending
in the bin and fenced is continued by a walk of its colour through the box of radius `M` about its
  end
and the corridor, ending outside the interior of `B_{R'}(z)`. -/
theorem exists_walk_of_side {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2}
    {R R' M K W : ℕ} {x : ℤ} {dir : Fin 2} {lo hi : LatticeSite 2} {B : Set (LatticeSite 2)}
    {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    (hM : 1 ≤ M) (hKM : K ≤ M) (hW : 1 ≤ W) (hWK : W ≤ K) (hRM : R + M ≤ R')
    (hside : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧ hi = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧ hi = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R))
    (hC : cond col ω (dualConfig ω) ∈ crossing dir lo hi) (hb : b ∈ B)
    (hf : HasOuterFence ω col z R M K γ) :
    ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ.support ∧
      x' ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
      (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
      (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Icc lo hi) ∧
      y ∉ cond col (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) := by
  have hy : ∀ y : LatticeSite 2, (y 1 = z 1 + R' ∨ y 0 = z 0 + R' ∨
      y 1 = z 1 - R' - cond col 0 1 ∨ y 0 = z 0 - R' - cond col 0 1) →
      y ∉ cond col (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) := by
    intro y hy hmem
    cases col <;> simp only [Bool.cond_true, Bool.cond_false] at hmem hy <;>
      rw [mem_Icc_two_iff] at hmem <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hmem <;> omega
  rcases hside with ⟨rfl, rfl, rfl, hB⟩ | ⟨rfl, rfl, rfl, hB⟩ | ⟨rfl, rfl, rfl, hB⟩ |
    ⟨rfl, rfl, rfl, hB⟩ <;> rw [hB] at hb
  · obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hb
    obtain ⟨x', y, P, hx', hxM, hPe, hPs, hy'⟩ :=
      exists_walk_of_corridor_top hM hKM hWK hRM hC hb₁ hb₀ hb₀' hbR hbL hf
    exact ⟨x', y, P, hx', hxM, hPe, hPs, hy y (Or.inl hy')⟩
  · obtain ⟨hb₀, hb₁, hb₁', hbB, hbT⟩ := hb
    obtain ⟨x', y, P, hx', hxM, hPe, hPs, hy'⟩ :=
      exists_walk_of_corridor_right hM hKM hW hWK hRM hC hb₀ hb₁ hb₁' hbT hbB hf
    exact ⟨x', y, P, hx', hxM, hPe, hPs, hy y (Or.inr (Or.inl hy'))⟩
  · obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hb
    obtain ⟨x', y, P, hx', hxM, hPe, hPs, hy'⟩ :=
      exists_walk_of_corridor_bottom hM hKM hWK hRM hC hb₁ hb₀ hb₀' hbR hbL hf
    exact ⟨x', y, P, hx', hxM, hPe, hPs, hy y (Or.inr (Or.inr (Or.inl hy')))⟩
  · obtain ⟨hb₀, hb₁, hb₁', hbB, hbT⟩ := hb
    obtain ⟨x', y, P, hx', hxM, hPe, hPs, hy'⟩ :=
      exists_walk_of_corridor_left hM hKM hW hWK hRM hC hb₀ hb₁ hb₁' hbT hbB hf
    exact ⟨x', y, P, hx', hxM, hPe, hPs, hy y (Or.inr (Or.inr (Or.inr hy')))⟩

/-- **The crossing bound of a straight corridor**: with `R' ≤ k W`, the corridor is crossed in the
configuration of its colour with probability at least `c k`. -/
theorem CrossingBounds.le_law_of_side {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c) {k : ℕ} {col : Bool} {z : LatticeSite 2} {R R' M W
      : ℕ} {x : ℤ} {dir : Fin 2}
    {lo hi : LatticeSite 2} {B : Set (LatticeSite 2)}
    (hW : 1 ≤ W) (hWL : (W : ℕ∞) ≤ L) (hRR' : R ≤ R') (hk : R' ≤ k * W)
    (hside : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir = 1 ∧ lo = ![x, z 1 - R' - cond col 0 1] ∧ hi = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir = 0 ∧ lo = ![z 0 - R' - cond col 0 1, x] ∧ hi = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)) :
    c k ≤ law q ((fun ω : Config (LatticeSite 2) => cond col ω (dualConfig ω)) ⁻¹'
      crossing dir lo hi) := by
  have hk' : (R' : ℤ) ≤ k * W := by exact_mod_cast hk
  rcases hside with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ |
    ⟨rfl, rfl, rfl, -⟩
  · exact hCB.le_law_preimage_cond_crossing_one col k hW hWL (by simp; omega) (by simp; omega)
      (by simp)
  · exact hCB.le_law_preimage_cond_crossing_zero col k hW hWL (by simp; omega) (by simp; omega)
      (by simp)
  · exact hCB.le_law_preimage_cond_crossing_one col k hW hWL (by simp; omega) (by simp; omega)
      (by simp)
  · exact hCB.le_law_preimage_cond_crossing_zero col k hW hWL (by simp; omega) (by simp; omega)
      (by simp)

/-! ### Straight corridors from fixed bins -/

/-- **Gluing through straight corridors, for fixed bins.** Let each arm `i` have a bin `B i` on a
side of `B_R(z)` with coordinates `[x i, x i + W]` along the side, at least `2M` from the corners,
  and
the straight corridor `Icc (lo i) (hi i)` of width `W` from the bin to the boundary of `B_{R'}(z)`
(`hside`). With `c κ` the crossing bound for boxes of aspect ratio `κ ≥ R' / W`, `c κ ^ j` times the
probability of the separated event with ends in the bins and inner positions in `J` is at most the
probability of `j` arms to the boundary of `B_{R'}(z)` with inner positions in `J`. -/
theorem pow_mul_law_le_law_multiArmEventIn_of_sides (q : Sym2 (LatticeSite 2) → unitInterval)
    {L : ℕ∞} {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' W κ : ℕ} (hW : 1 ≤ W) (hWK : W ≤ K)
    (hKM : K ≤ M) (hWM : 2 * W + 2 ≤ M) (hs : 4 * (M : ℝ) ≤ s) (hrM : r + M + 1 < R)
    (hRM : R + M ≤ R') (hk : R' ≤ κ * W) (hR'L : (R' : ℕ∞) ≤ L) (J : Fin j → Set ℤ)
    (x : Fin j → ℤ) (dir : Fin j → Fin 2) (lo hi : Fin j → LatticeSite 2)
    (B : Fin j → Set (LatticeSite 2))
    (hside : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧ hi i = ![x i + W, z 1 + R'] ∧
        ∀ b, b ∈ B i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + R', x i + W] ∧
        ∀ b, b ∈ B i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      (dir i = 1 ∧ lo i = ![x i, z 1 - R' - cond (σ i) 0 1] ∧
        hi i = ![x i + W, z 1 - R - cond (σ i) 0 1] ∧
        ∀ b, b ∈ B i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧ b 0 ≤ x i + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 - R' - cond (σ i) 0 1, x i] ∧
        hi i = ![z 0 - R - cond (σ i) 0 1, x i + W] ∧
        ∀ b, b ∈ B i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧ b 1 ≤ x i + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)) :
    c κ ^ j * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤ law q (multiArmEventIn σ z r R' J fun _ => univ) := by
  classical
  have hM : 1 ≤ M := by omega
  have hrR : r < R := by omega
  have hWL : (W : ℕ∞) ≤ L := (Nat.cast_le.2 (by omega)).trans hR'L
  have hc : ∀ i, 0 ≤ cond (σ i) (0 : ℤ) 1 ∧ cond (σ i) (0 : ℤ) 1 ≤ 1 := fun i => by
    cases σ i <;> simp
  obtain ⟨C, hC⟩ : ∃ C : Fin j → Set (Config (LatticeSite 2)), C = fun i =>
      (fun ω : Config (LatticeSite 2) => cond (σ i) ω (dualConfig ω)) ⁻¹'
        crossing (dir i) (lo i) (hi i) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Fin j → Set (Sym2 (LatticeSite 2)), T = fun i =>
      {e | ∀ v ∈ e, v ∈ Icc (lo i) (hi i + cond (σ i) 0 1)} := ⟨_, rfl⟩
  have hprod : c κ ^ j ≤ ∏ i, law q (C i) := by
    have := Finset.pow_card_le_prod Finset.univ (fun i => law q (C i)) (c κ) (fun i _ => by
      rw [hC]
      exact hCB.le_law_of_side hW hWL (by omega) hk (hside i))
    simpa using this
  -- the empty case
  by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
      (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
      (∀ i, IsArm ω₀ (σ i) z r (z - R) (z + R) (γ₀ i)) ∧ ArmsOuterSeparated ω₀ σ z R s M K γ₀ ∧
        ∀ i, b₀ i ∈ B i
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine mul_eq_zero_of_right _ ?_
    convert measure_empty (μ := law q)
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨a, b, γ, h₁, -, -, h₄, h₅, -⟩
    exact hne ⟨ω, a, b, γ, h₁, h₄, h₅⟩
  obtain ⟨ω₀, a₀, b₀, γ₀, hγ₀, hsep₀, hB₀⟩ := hne
  have hsep₀' := hsep₀.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)
  have SL₀ := fun i => (hγ₀ i).sideL_of_side hrR hM (hside i) (hB₀ i)
  -- open and dual corridors read disjoint pairs
  have hTT : ∀ i k, σ i = true → σ k = false → Disjoint (T i) (T k) := by
    intro i k hi hk
    rw [disjoint_left]
    intro e he he'
    rw [hT] at he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have h₁ := he v hv
    have h₂ := he' v hv
    have hik : i ≠ k := fun h => by
      rw [h, hk] at hi
      exact Bool.false_ne_true hi
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Pi.add_apply, cond_zero_one_apply] at h₁ h₂
    exact false_of_corridor_of_corridor (by omega) (by omega) (by simp [hi]) (by simp [hk])
      (SL₀ i) (SL₀ k) (hsep₀'.1 i k hik) h₁ h₂
  -- corridors of one colour avoid the end boxes of the other colour
  have hTB : ∀ i k, σ i ≠ σ k → ∀ b ∈ B i, ∀ e ∈ T k, ¬∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2)) := by
    intro i k hik b hb e he hbox
    rw [hT] at he
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have h₁ := he v hv
    have h₂ := hbox v hv
    have hik' : i ≠ k := fun h => hik (h ▸ rfl)
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, cond_zero_one_apply] at h₁ h₂
    refine false_of_box_of_corridor (by omega) (by omega) (by omega) ?_ (SL₀ i) (sideP_of_side
      (hside i) hb)
      (SL₀ k) (hsep₀'.1 i k hik') ⟨by omega, by omega, by omega, by omega⟩ h₁
    rcases Bool.eq_false_or_eq_true (σ i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (σ k) with h' | h' <;> simp_all
  -- the regions of arms of one colour are disjoint
  have hQdisj : ∀ (ω : Config (LatticeSite 2)) (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) → ArmsDisjoint σ γ →
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) →
      ArmsOuterSeparated ω σ z R s M K γ → (∀ i, b i ∈ B i) →
      ∀ i k, i ≠ k → σ i = σ k → ∀ v, (v ∈ Icc (b i - M) (b i + M) ∨ v ∈ Icc (lo i) (hi i)) →
        (v ∈ Icc (b k - M) (b k + M) ∨ v ∈ Icc (lo k) (hi k)) → False := by
    intro ω a b γ hγ _ ho hsep hBw i k hik hσik v hvi hvk
    rcases hσ with hj | hσ'
    · exact hik (Fin.ext (by omega))
    have hsep' := hsep.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)
    have hbd : ∀ l, 0 ≤ landingPos (z - R) (z + R) (σ l) (γ l) ∧
        landingPos (z - R) (z + R) (σ l) (γ l) ≤ 16 * R := fun l => by
      have := (hγ l).sideL_of_side hrR hM (hside l) (hBw l)
      have := hc l
      omega
    have hlo' : ∀ l, 4 * (M : ℤ) ≤ landingPos (z - R) (z + R) (σ l) (γ l) := fun l => by
      have h₁ := hsep'.2 l 0
      have h₂ := hbd l
      rw [le_abs] at h₁
      push_cast at h₁
      omega
    have hhi' : ∀ l, landingPos (z - R) (z + R) (σ l) (γ l) + 4 * M ≤ 16 * R := fun l => by
      have h₁ := hsep'.2 l 4
      have h₂ := hbd l
      rw [le_abs] at h₁
      push_cast at h₁
      omega
    have h8 := two_mul_le_abs_landingPos_sub (Or.inr hσ') ho hsep'.1 hik hσik
    have hcorC : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R → ∀ l,
        4 * (M : ℤ) ≤ |landingPos (z - R) (z + R) (σ l) (γ l) - C| := by
      intro C hC l
      have h₁ := hsep'.2 l 1
      have h₂ := hsep'.2 l 2
      have h₃ := hsep'.2 l 3
      rw [le_abs] at h₁ h₂ h₃ ⊢
      push_cast at h₁ h₂ h₃
      omega
    rw [mem_Icc_two_iff, mem_Icc_two_iff] at hvi hvk
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hvi hvk
    refine false_of_region_of_region (by omega) (by omega) (hc i) (by rw [hσik])
      ((hγ i).sideL_of_side hrR hM (hside i) (hBw i))
      ((hγ k).sideL_of_side hrR hM (hside k) (hBw k)) (by linarith) (fun C hC => ⟨?_, ?_⟩)
      (fun P hP => ⟨?_, ?_⟩) hvi hvk
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 (hcorC C hC) hik hσik h₁ h₂
      omega
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 (hcorC C hC) hik.symm hσik.symm h₁ h₂
      omega
    · intro h₁
      have := le_or_le_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 hlo' hhi' hik hσik h₁
      omega
    · intro h₁
      have := le_or_le_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 hlo' hhi' hik.symm hσik.symm h₁
      omega
  -- the hooks
  have hhook : ∀ i, ∀ ω ∈ C i, ∀ (a' b' : LatticeSite 2) (γ' : (zdGraph 2).Walk a' b'),
      IsArm ω (σ i) z r (z - R) (z + R) γ' → b' ∈ B i → HasOuterFence ω (σ i) z R M K γ' →
      ∃ (x' y : LatticeSite 2) (P : (zdGraph 2).Walk x' y), x' ∈ γ'.support ∧
        x' ∈ Icc (b' - M) (b' + M) ∧ (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ v ∈ P.support, v ∈ Icc (b' - M) (b' + M) ∨ v ∈ Icc (lo i) (hi i)) ∧
        y ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) ∧
        ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
          (Icc (z - R') (z + R' - 1)) → True := by
    intro i ω hω a' b' γ' _ hb' hf
    rw [hC] at hω
    obtain ⟨x', y, P, hx', hxM, hPe, hPs, hy⟩ :=
      exists_walk_of_side hM hKM hW hWK hRM (hside i) hω hb' hf
    exact ⟨x', y, P, hx', hxM, hPe, hPs, hy, fun _ _ _ => trivial⟩
  refine (mul_le_mul_left hprod _).trans ?_
  rw [mul_comm]
  refine (law_mul_prod_le_law_of_corridors q hσ hKM hM hrM (by omega) hs B J C T
    (fun i => Icc (lo i) (hi i)) (fun _ _ _ => True) (fun i => ?_) (fun i ω ω' h => ?_)
    (fun i ω ω' h hω => ?_) hTT (fun i e he v hv => ?_) hTB
    (fun i b hb v hv hvR => mem_Icc_of_side (hside i) hM (by omega) hb hv hvR) hQdisj
    hhook).trans (measure_mono ?_)
  · rw [hC]
    exact measurableSet_preimage_cond_crossing _ _ _ _
  · rw [hC]
    rw [hT] at h
    exact preimage_cond_crossing_iff_of_inter_eq _ _ _ _ h
  · rw [hC] at hω ⊢
    exact cond_mem_crossing_of_cond_subset h hω
  · rw [hT] at he
    exact notMem_Icc_of_side (hside i) (he v hv)
  · rintro ω ⟨a, b', γ', h₁, h₂, h₃, h₄, -⟩
    exact ⟨a, b', γ', h₁, h₂, fun i => ⟨h₄ i, mem_univ _⟩, h₃⟩

/-! ### Bins and the gluing statement -/

/-- **The bin of a coordinate.** A coordinate `ℓ ∈ [a, a + 2R]` lies in one of the `2A + 1` bins
`[a + n (W + 1), a + n (W + 1) + W]`, `n < 2A + 1`, when `R ≤ A W`. -/
theorem exists_lt_le_le {a ℓ : ℤ} {W R A : ℕ} (hW : 1 ≤ W) (hRA : R ≤ A * W) (h₁ : a ≤ ℓ)
    (h₂ : ℓ ≤ a + 2 * R) :
    ∃ n : ℕ, n < 2 * A + 1 ∧ a + n * (W + 1) ≤ ℓ ∧ ℓ ≤ a + n * (W + 1) + W := by
  have hW1 : (0 : ℤ) < W + 1 := by positivity
  have hq0 : 0 ≤ (ℓ - a) / (W + 1) := Int.ediv_nonneg (by omega) hW1.le
  have hq1 : (ℓ - a) / (W + 1) * (W + 1) ≤ ℓ - a := Int.ediv_mul_le _ hW1.ne'
  have hq2 : ℓ - a < ((ℓ - a) / (W + 1) + 1) * (W + 1) := Int.lt_ediv_add_one_mul_self _ hW1
  have hRA' : (R : ℤ) ≤ A * W := by exact_mod_cast hRA
  have hq3 : (ℓ - a) / (W + 1) < 2 * A + 1 := Int.ediv_lt_of_lt_mul hW1 (by nlinarith)
  rw [add_one_mul] at hq2
  refine ⟨((ℓ - a) / (W + 1)).toNat, by omega, ?_, ?_⟩ <;> rw [Int.toNat_of_nonneg hq0] <;> omega

/-- **Every separated end lies in a bin.** An arm to the boundary of `B_R(z)` landing at least `4M`
from the doubled corners ends on a side `t` (`0` top, `1` right, `2` bottom, `3` left), at least
  `2M`
from the corners, in one of the `2A + 1` bins of width `W` on that side. -/
theorem IsArm.exists_mem_bin {ω : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2}
    {r R M W A : ℕ} {a b : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    (hγ : IsArm ω col z r (z - R) (z + R) γ) (hrR : r < R) (hM : 1 ≤ M) (hW : 1 ≤ W)
    (hRA : R ≤ A * W) (hcor : ∀ m : ℕ, 4 * (M : ℤ) ≤ |landingPos (z - R) (z + R) col γ - 4 * m *
      R|) :
    ∃ (t : Fin 4) (n : ℕ), n < 2 * A + 1 ∧ ((t = 0 ∧ b 1 = z 1 + R ∧
      ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) ≤ b 0 ∧
        b 0 ≤ ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧
          ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) ≤ b 1 ∧
            b 1 ≤ ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧
          ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) ≤ b 0 ∧
            b 0 ≤ ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧
          ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) ≤ b 1 ∧
            b 1 ≤ ((if t = 0 ∨ t = 2 then z 0 else z 1) - R + (n : ℤ) * (W + 1)) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)) := by
  have hc : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  have hb := hγ.end_mem_Icc (Icc_subset_Icc_add_one_sub_one hrR)
  rw [mem_Icc_two_iff] at hb
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hb
  have c0 := hcor 0
  have c1 := hcor 1
  have c2 := hcor 2
  have c3 := hcor 3
  have c4 := hcor 4
  rw [le_abs] at c0 c1 c2 c3 c4
  push_cast at c0 c1 c2 c3 c4
  rcases hγ.landingPos_cases hrR with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have e₁ : z 0 - (R : ℤ) ≤ b 0 := by omega
    have e₂ : b 0 ≤ z 0 - (R : ℤ) + 2 * R := by omega
    obtain ⟨n, hn, h₃, h₄⟩ := exists_lt_le_le hW hRA e₁ e₂
    exact ⟨0, n, hn, Or.inl ⟨rfl, h₁, by simp only [true_or, ite_true]; omega,
      by simp only [true_or, ite_true]; omega, by omega, by omega⟩⟩
  · have e₁ : z 1 - (R : ℤ) ≤ b 1 := by omega
    have e₂ : b 1 ≤ z 1 - (R : ℤ) + 2 * R := by omega
    obtain ⟨n, hn, h₃, h₄⟩ := exists_lt_le_le hW hRA e₁ e₂
    exact ⟨1, n, hn, Or.inr (Or.inl ⟨rfl, h₁, by simp; omega, by simp; omega, by omega,
      by omega⟩)⟩
  · have e₁ : z 0 - (R : ℤ) ≤ b 0 := by omega
    have e₂ : b 0 ≤ z 0 - (R : ℤ) + 2 * R := by omega
    obtain ⟨n, hn, h₃, h₄⟩ := exists_lt_le_le hW hRA e₁ e₂
    exact ⟨2, n, hn, Or.inr (Or.inr (Or.inl ⟨rfl, h₁, by simp; omega, by simp; omega, by omega,
      by omega⟩))⟩
  · have e₁ : z 1 - (R : ℤ) ≤ b 1 := by omega
    have e₂ : b 1 ≤ z 1 - (R : ℤ) + 2 * R := by omega
    obtain ⟨n, hn, h₃, h₄⟩ := exists_lt_le_le hW hRA e₁ e₂
    exact ⟨3, n, hn, Or.inr (Or.inr (Or.inr ⟨rfl, h₁, by simp; omega, by simp; omega, by omega,
      by omega⟩))⟩

/-- **The straight corridor of a bin**: the bin of side `t` starting at `x` and its corridor satisfy
the description `hside` used by the gluing. -/
theorem side_of_bin (col : Bool) (z : LatticeSite 2) (R R' M W : ℕ) (t : Fin 4) (x : ℤ) :
    ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 1 ∧
      (if t = 0 then ![x, z 1 + R] else if t = 1 then ![z 0 + R, x]
      else if t = 2 then ![x, z 1 - R' - cond col 0 1] else ![z 0 - R' - cond col 0 1, x]) = ![x, z
        1 + R] ∧ (if t = 0 then ![x + W, z 1 + R'] else if t = 1 then ![z 0 + R', x + W]
      else if t = 2 then ![x + W, z 1 - R - cond col 0 1]
      else ![z 0 - R - cond col 0 1, x + W]) = ![x + W, z 1 + R'] ∧
        ∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)} ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧
            b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
          b 0 + 2 * M ≤ z 0 + R) ∨
      ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 0 ∧
        (if t = 0 then ![x, z 1 + R] else if t = 1 then ![z 0 + R, x]
      else if t = 2 then ![x, z 1 - R' - cond col 0 1] else ![z 0 - R' - cond col 0 1, x]) = ![z 0
        + R, x] ∧ (if t = 0 then ![x + W, z 1 + R'] else if t = 1 then ![z 0 + R', x + W]
      else if t = 2 then ![x + W, z 1 - R - cond col 0 1]
      else ![z 0 - R - cond col 0 1, x + W]) = ![z 0 + R', x + W] ∧
        ∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)} ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧
            b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
          b 1 + 2 * M ≤ z 1 + R) ∨
      ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 1 ∧
        (if t = 0 then ![x, z 1 + R] else if t = 1 then ![z 0 + R, x]
      else if t = 2 then ![x, z 1 - R' - cond col 0 1] else ![z 0 - R' - cond col 0 1, x]) = ![x, z
        1 - R' - cond col 0 1] ∧
          (if t = 0 then ![x + W, z 1 + R'] else if t = 1 then ![z 0 + R', x + W]
      else if t = 2 then ![x + W, z 1 - R - cond col 0 1]
      else ![z 0 - R - cond col 0 1, x + W]) = ![x + W, z 1 - R - cond col 0 1] ∧
        ∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)} ↔ b 1 = z 1 - R - cond col 0 1 ∧
            x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 0 ∧
        (if t = 0 then ![x, z 1 + R] else if t = 1 then ![z 0 + R, x]
      else if t = 2 then ![x, z 1 - R' - cond col 0 1] else ![z 0 - R' - cond col 0 1, x]) = ![z 0
        - R' - cond col 0 1, x] ∧
          (if t = 0 then ![x + W, z 1 + R'] else if t = 1 then ![z 0 + R', x + W]
      else if t = 2 then ![x + W, z 1 - R - cond col 0 1]
      else ![z 0 - R - cond col 0 1, x + W]) = ![z 0 - R - cond col 0 1, x + W] ∧
        ∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)} ↔ b 0 = z 0 - R - cond col 0 1 ∧
            x ≤ b 1 ∧ b 1 ≤ x + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) := by
  rcases (by decide : ∀ t : Fin 4, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) t with rfl | rfl | rfl | rfl <;>
    simp

/-- **Gluing separated arms through straight corridors** (Nolin, Proposition 12, the straight
case). For a colour sequence `σ` without packs and ratios `A`, `D` there is `c₀ > 0` such that for
every law with crossing bounds `c` up to scale `L`, every centre `z`, radii `r < R ≤ R' ≤ L`, bin
width `W`, fences of length `2K` and depth `M`, separation `s` and inner windows `J`, with
`1 ≤ W ≤ K ≤ M`, `2W + 2 ≤ M`, `4M ≤ s`, `r + M + 1 < R`, `R + M ≤ R' ≤ D R` and `R ≤ A W`:
`c₀ P(j arms to ∂B_R(z) separated at scale s with fences, inner positions in J)
≤ P(j arms to ∂B_{R'}(z), inner positions in J)`. -/
theorem exists_pos_le_law_multiArmEventIn_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ), 1 ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → 4 * (M : ℝ) ≤ s →
      r + M + 1 < R → R + M ≤ R' → R' ≤ D * R → R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q (multiArmEventIn σ z r R' J fun _ => univ) := by
  classical
  by_cases hc : 0 < c (D * A)
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  have hX0 : (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    positivity
  have hXt : (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨c (D * A) ^ j / (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞),
    ENNReal.div_pos (pow_ne_zero _ hc.ne') hXt, ?_⟩
  intro q L hCB z r R R' W M K s J hW hWK hKM hWM hs hrM hRM hRD hRA hR'L
  have hrR : r < R := by omega
  have hk : R' ≤ D * A * W := by
    calc R' ≤ D * R := hRD
      _ ≤ D * (A * W) := Nat.mul_le_mul_left _ hRA
      _ = D * A * W := by ring
  -- the separated event with ends in given bins
  set E : (Fin j → Fin 4 × Fin (2 * A + 1)) → Set (Config (LatticeSite 2)) :=
      fun β => {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | ((β i).1 = 0 ∧
          b 1 = z 1 + R ∧
            ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1))
              ≤ b 0 ∧
                b 0 ≤ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) *
                  (W + 1)) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        ((β i).1 = 1 ∧ b 0 = z 0 + R ∧
          ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) ≤
            b 1 ∧
              b 1 ≤ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) *
                (W + 1)) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        ((β i).1 = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧
          ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) ≤
            b 0 ∧
              b 0 ≤ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) *
                (W + 1)) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        ((β i).1 = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧
          ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) ≤
            b 1 ∧
              b 1 ≤ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) *
                (W + 1)) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} with hE
  -- every separated configuration has its ends in some bins
  have hcover : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      ∑ β, law q (E β) := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    rintro ω ⟨a, b, γ, hγ, hd, ho, hsep, hJ⟩
    have hsep' := hsep.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)
    choose t n hn hb using fun i => (hγ i).exists_mem_bin hrR (by omega) hW hRA (hsep'.2 i)
    rw [mem_iUnion]
    refine ⟨fun i => (t i, ⟨n i, hn i⟩), ?_⟩
    rw [hE]
    exact ⟨a, b, γ, hγ, hd, ho, hsep, hb, hJ⟩
  -- the gluing for each choice of bins
  have hβ : ∀ β, c (D * A) ^ j * law q (E β) ≤ law q (multiArmEventIn σ z r R' J fun _ => univ) :=
    by
    intro β
    rw [hE]
    exact pow_mul_law_le_law_multiArmEventIn_of_sides q hCB hσ hW hWK hKM hWM hs hrM hRM hk hR'L J
      _ _ _ _ _ fun i => side_of_bin (σ i) z R R' M W (β i).1 _
  refine (mul_le_mul' le_rfl hcover).trans ?_
  rw [Finset.mul_sum]
  calc ∑ β, c (D * A) ^ j / (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) * law q (E β)
      ≤ ∑ _β : Fin j → Fin 4 × Fin (2 * A + 1),
          law q (multiArmEventIn σ z r R' J fun _ => univ) *
            ((((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞))⁻¹ := by
        refine Finset.sum_le_sum fun β _ => ?_
        rw [div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul_left (hβ β) _
    _ = law q (multiArmEventIn σ z r R' J fun _ => univ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hX0 hXt, mul_one]

/-- **Gluing separated arms through straight corridors**, without inner windows:
`c₀ P(outerSeparatedArmEvent σ z r R s M K) ≤ P(multiArmEvent σ z r R')`. -/
theorem exists_pos_le_law_multiArmEvent_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K : ℕ) (s : ℝ),
      1 ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → 4 * (M : ℝ) ≤ s →
      r + M + 1 < R → R + M ≤ R' → R' ≤ D * R → R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q (outerSeparatedArmEvent σ z r R s M K) ≤ law q (multiArmEvent σ z r R') := by
  obtain ⟨c₀, hc₀, h⟩ := exists_pos_le_law_multiArmEventIn_of_separated σ hσ c A D
  refine ⟨c₀, hc₀, fun q L hCB z r R R' W M K s hW hWK hKM hWM hs hrM hRM hRD hRA hR'L => ?_⟩
  refine le_trans (le_of_eq ?_)
    (h q L hCB z r R R' W M K s (fun _ => univ) hW hWK hKM hWM hs hrM hRM hRD hRA hR'L)
  congr 2
  ext ω
  exact ⟨fun ⟨a, b, γ, h₁, h₂, h₃, h₄⟩ => ⟨a, b, γ, h₁, h₂, h₃, h₄, fun _ => mem_univ _⟩,
    fun ⟨a, b, γ, h₁, h₂, h₃, h₄, _⟩ => ⟨a, b, γ, h₁, h₂, h₃, h₄⟩⟩


end Straight

end PercLib.Models.Planar
