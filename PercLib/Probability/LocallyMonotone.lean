/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied: everything is derived from
Harris's inequality (`PercLib.Probability.prodBernoulli_harris` and its decreasing companion),
the independence of determined events (`PercLib.Probability.prodBernoulli_inter_of_determined`)
and BK for increasing events (`PercLib.Probability.countable_profile_bk_foldl`).
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Lemma 13 (p. 1577) and the first step of the proof of
Lemma 15 (p. 1579).
-/
module

public import PercLib.Probability.CountableBK
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.Superposition

/-!
# Correlation inequalities for events of mixed monotonicity

Three tools for events that are increasing in some coordinates and decreasing in others, under
the product law `prodBernoulli p` on an arbitrary index type `ι` with an arbitrary profile `p`.

* **Splicing.** Take two independent configurations `ω₁, ω₂` with law `prodBernoulli p` and keep
  `ω₁` on a set `S` of coordinates and `ω₂` off it: the result `(ω₁ ∩ S) ∪ (ω₂ \ S)` again has
  law `prodBernoulli p`. So the probability of an event is the average over `ω₁` of the
  probability of its section at `ω₁`; this is conditioning on the coordinates in `S`.
* **FKG for locally monotone events** (Nolin, Lemma 13). Let `S`, `Sinc`, `Sdec` be pairwise
  disjoint sets of coordinates, `Ainc` and `Binc` increasing events, `Adec` and `Bdec`
  decreasing events, with `Ainc` determined by `S ∪ Sinc`, `Adec` by `S ∪ Sdec`, `Binc` by
  `Sinc` and `Bdec` by `Sdec`. Then
  `P(Ainc ∩ Adec) P(Binc) P(Bdec) ≤ P(Ainc ∩ Adec ∩ Binc ∩ Bdec)`, that is,
  `P(Binc ∩ Bdec | Ainc ∩ Adec) ≥ P(Binc) P(Bdec)`. The proof conditions on the coordinates in
  `S`: the sections of `Ainc ∩ Binc` and `Adec ∩ Bdec` are determined by the disjoint sets
  `Sinc` and `Sdec`, hence independent, and Harris's inequality applies to each.
* **Iterated disjoint occurrence.** BK for increasing events bounds the probability of `h`
  disjoint occurrences of an increasing event `C` by `P(C)^h`. The same holds for a measurable
  decreasing event: disjoint occurrence commutes with taking complements of configurations, and
  the complement of a configuration with law `prodBernoulli p` has law
  `prodBernoulli (1 - p)`. This is the first step of Nolin's Lemma 15: the number of disjoint
  crossings of a domain has a geometric tail.

Nothing here is planar. This file adds no definition.

## Main results

* `prodBernoulli_prod_map_splice`: the spliced configuration has law `prodBernoulli p`;
  `prodBernoulli_eq_lintegral_splice`: the probability of a measurable event is the integral of
  the probabilities of its sections.
* `prodBernoulli_mul_mul_le_inter_of_determined`: **FKG for locally monotone events**
  (Nolin, Lemma 13).
* `preimage_compl_disjointOccurrence`, `preimage_compl_foldl_disjointOccurrence`: disjoint
  occurrence commutes with complementing configurations.
* `prodBernoulli_foldl_replicate_le_pow` (increasing events) and
  `prodBernoulli_foldl_replicate_le_pow_of_isLowerSet` (measurable decreasing events): `h`
  disjoint occurrences have probability at most `P(C)^h`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Splicing two independent configurations -/

/-- The spliced configuration `(ω₁ ∩ S) ∪ (ω₂ \ S)` is a measurable function of the pair. -/
theorem measurable_splice (S : Set ι) :
    Measurable (fun ω : Set ι × Set ι => (ω.1 ∩ S) ∪ (ω.2 \ S)) := by
  fun_prop

/-- For a fixed first configuration, splicing is a measurable function of the second one. -/
theorem measurable_splice_right (S x : Set ι) :
    Measurable (fun y : Set ι => (x ∩ S) ∪ (y \ S)) := by
  fun_prop

/-- **Splicing.** Keeping one configuration on `S` and an independent copy off `S` gives a
configuration with the same product law. -/
theorem prodBernoulli_prod_map_splice (p : ι → unitInterval) (S : Set ι) :
    ((prodBernoulli p).prod (prodBernoulli p)).map (fun ω => (ω.1 ∩ S) ∪ (ω.2 \ S)) =
      prodBernoulli p := by
  classical
  have hm := measurable_splice S
  have : IsProbabilityMeasure (((prodBernoulli p).prod (prodBernoulli p)).map
      (fun ω : Set ι × Set ι => (ω.1 ∩ S) ∪ (ω.2 \ S))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  have hF : MeasurableSet {ω : Set ι | (F : Set ι) ⊆ ω} :=
    generateFrom_finset_subset (ι := ι) ▸
      MeasurableSpace.measurableSet_generateFrom ⟨F, rfl⟩
  rw [Measure.map_apply hm hF]
  have hpre : (fun ω : Set ι × Set ι => (ω.1 ∩ S) ∪ (ω.2 \ S)) ⁻¹' {ω | (F : Set ι) ⊆ ω} =
      {ω : Set ι | ((F.filter (· ∈ S) : Finset ι) : Set ι) ⊆ ω} ×ˢ
        {ω : Set ι | ((F.filter (· ∉ S) : Finset ι) : Set ι) ⊆ ω} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_prod, Finset.coe_filter]
    constructor
    · intro h
      refine ⟨fun i ⟨hi, hiS⟩ => ?_, fun i ⟨hi, hiS⟩ => ?_⟩
      · rcases h hi with h' | h'
        · exact h'.1
        · exact absurd h'.2 (not_not.2 hiS)
      · rcases h hi with h' | h'
        · exact absurd h'.2 hiS
        · exact h'.1
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hiS : i ∈ S
      · exact Or.inl ⟨h₁ ⟨hi, hiS⟩, hiS⟩
      · exact Or.inr ⟨h₂ ⟨hi, hiS⟩, hiS⟩
  rw [hpre, Measure.prod_prod, prodBernoulli_subset, prodBernoulli_subset,
    prodBernoulli_subset, Finset.prod_filter_mul_prod_filter_not]

/-- **Conditioning on the coordinates in `S`.** The probability of a measurable event is the
integral, over the configuration `x` on `S`, of the probability of its section at `x`. -/
theorem prodBernoulli_eq_lintegral_splice (p : ι → unitInterval) (S : Set ι)
    {E : Set (Set ι)} (hE : MeasurableSet E) :
    prodBernoulli p E =
      ∫⁻ x, prodBernoulli p ((fun y => (x ∩ S) ∪ (y \ S)) ⁻¹' E) ∂prodBernoulli p := by
  conv_lhs => rw [← prodBernoulli_prod_map_splice p S]
  rw [Measure.map_apply (measurable_splice S) hE,
    Measure.prod_apply (measurable_splice S hE)]
  rfl

/-- The section of an event determined by `T` at a configuration on `S` is determined by
`T \ S`. -/
theorem splice_determined {S T : Set ι} {A : Set (Set ι)}
    (hA : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ A ↔ ω' ∈ A)) (x : Set ι) :
    ∀ ω ω', ω ∩ (T \ S) = ω' ∩ (T \ S) →
      (ω ∈ (fun y => (x ∩ S) ∪ (y \ S)) ⁻¹' A ↔ ω' ∈ (fun y => (x ∩ S) ∪ (y \ S)) ⁻¹' A) := by
  intro ω ω' h
  refine hA _ _ ?_
  ext i
  have hi := congrArg (i ∈ ·) h
  simp only [mem_inter_iff, mem_sdiff, eq_iff_iff] at hi
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp_all

/-- The section, at any configuration on `S`, of an event determined by a set disjoint from `S`
is the event itself. -/
theorem splice_preimage_eq_of_disjoint {S T : Set ι} (hST : Disjoint S T) {A : Set (Set ι)}
    (hA : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ A ↔ ω' ∈ A)) (x : Set ι) :
    (fun y => (x ∩ S) ∪ (y \ S)) ⁻¹' A = A := by
  ext y
  refine hA _ _ ?_
  ext i
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  by_cases hiT : i ∈ T
  · have hiS : i ∉ S := fun h => hST.ne_of_mem h hiT rfl
    simp [hiS, hiT]
  · simp [hiT]

/-! ### FKG for locally monotone events -/

/-- **FKG for locally monotone events** (Nolin, Lemma 13). Let `S`, `Sinc`, `Sdec` be pairwise
disjoint sets of coordinates, `Ainc` and `Binc` increasing events, `Adec` and `Bdec` decreasing
events, all measurable, with `Ainc` determined by `S ∪ Sinc`, `Adec` by `S ∪ Sdec`, `Binc` by
`Sinc` and `Bdec` by `Sdec`. Then
`P(Ainc ∩ Adec) P(Binc) P(Bdec) ≤ P(Ainc ∩ Adec ∩ (Binc ∩ Bdec))`.

There are fifteen hypotheses: the three disjointness conditions, the four monotonicity
conditions and the four determination conditions of Nolin's statement, and four measurability
conditions. Nolin's sets of coordinates are finite, which makes every determined event
measurable; here they are arbitrary. -/
theorem prodBernoulli_mul_mul_le_inter_of_determined (p : ι → unitInterval) {S Sinc Sdec : Set ι}
    (hSinc : Disjoint S Sinc) (hSdec : Disjoint S Sdec) (hSincdec : Disjoint Sinc Sdec)
    {Ainc Adec Binc Bdec : Set (Set ι)}
    (hAinc : IsUpperSet Ainc) (hAdec : IsLowerSet Adec) (hBinc : IsUpperSet Binc)
    (hBdec : IsLowerSet Bdec)
    (hAincm : MeasurableSet Ainc) (hAdecm : MeasurableSet Adec) (hBincm : MeasurableSet Binc)
    (hBdecm : MeasurableSet Bdec)
    (hAincd : ∀ ω ω', ω ∩ (S ∪ Sinc) = ω' ∩ (S ∪ Sinc) → (ω ∈ Ainc ↔ ω' ∈ Ainc))
    (hAdecd : ∀ ω ω', ω ∩ (S ∪ Sdec) = ω' ∩ (S ∪ Sdec) → (ω ∈ Adec ↔ ω' ∈ Adec))
    (hBincd : ∀ ω ω', ω ∩ Sinc = ω' ∩ Sinc → (ω ∈ Binc ↔ ω' ∈ Binc))
    (hBdecd : ∀ ω ω', ω ∩ Sdec = ω' ∩ Sdec → (ω ∈ Bdec ↔ ω' ∈ Bdec)) :
    prodBernoulli p (Ainc ∩ Adec) * prodBernoulli p Binc * prodBernoulli p Bdec ≤
      prodBernoulli p (Ainc ∩ Adec ∩ (Binc ∩ Bdec)) := by
  set μ := prodBernoulli p
  -- sections at a configuration `x` on `S`
  set sec : Set ι → Set (Set ι) → Set (Set ι) :=
    fun x A => (fun y => (x ∩ S) ∪ (y \ S)) ⁻¹' A with hsec
  have hsecm : ∀ x {A : Set (Set ι)}, MeasurableSet A → MeasurableSet (sec x A) :=
    fun x _ hA => measurable_splice_right S x hA
  have hmono : ∀ x, Monotone (fun y : Set ι => (x ∩ S) ∪ (y \ S)) :=
    fun x _ _ h => union_subset_union_right _ (sdiff_subset_sdiff_left h)
  have hupper : ∀ x {A : Set (Set ι)}, IsUpperSet A → IsUpperSet (sec x A) :=
    fun x _ hA _ _ h hy => hA (hmono x h) hy
  have hlower : ∀ x {A : Set (Set ι)}, IsLowerSet A → IsLowerSet (sec x A) :=
    fun x _ hA _ _ h hy => hA (hmono x h) hy
  -- the sections of `Ainc` and `Adec` are determined by `Sinc` and `Sdec`
  have hsubp : (S ∪ Sinc) \ S = Sinc := by
    rw [union_sdiff_left]; exact sdiff_eq_left.2 hSinc.symm
  have hsubm : (S ∪ Sdec) \ S = Sdec := by
    rw [union_sdiff_left]; exact sdiff_eq_left.2 hSdec.symm
  have hdp : ∀ x, ∀ ω ω', ω ∩ Sinc = ω' ∩ Sinc → (ω ∈ sec x Ainc ↔ ω' ∈ sec x Ainc) := fun x => by
    have := splice_determined (S := S) hAincd x
    rwa [hsubp] at this
  have hdm : ∀ x, ∀ ω ω', ω ∩ Sdec = ω' ∩ Sdec → (ω ∈ sec x Adec ↔ ω' ∈ sec x Adec) := fun x => by
    have := splice_determined (S := S) hAdecd x
    rwa [hsubm] at this
  have hBincs : ∀ x, sec x Binc = Binc := splice_preimage_eq_of_disjoint hSinc hBincd
  have hBdecs : ∀ x, sec x Bdec = Bdec := splice_preimage_eq_of_disjoint hSdec hBdecd
  -- the pointwise inequality
  have hpt : ∀ x, μ (sec x (Ainc ∩ Adec)) * (μ Binc * μ Bdec) ≤
      μ (sec x (Ainc ∩ Adec ∩ (Binc ∩ Bdec))) := by
    intro x
    have hE : sec x (Ainc ∩ Adec ∩ (Binc ∩ Bdec)) = (sec x Ainc ∩ Binc) ∩ (sec x Adec ∩ Bdec) := by
      rw [show sec x (Ainc ∩ Adec ∩ (Binc ∩ Bdec)) =
          sec x Ainc ∩ sec x Adec ∩ (sec x Binc ∩ sec x Bdec) from rfl, hBincs x, hBdecs x]
      ext y; simp only [mem_inter_iff]; tauto
    have hA : sec x (Ainc ∩ Adec) = sec x Ainc ∩ sec x Adec := preimage_inter
    have hindA : μ (sec x Ainc ∩ sec x Adec) = μ (sec x Ainc) * μ (sec x Adec) :=
      prodBernoulli_inter_of_determined p hSincdec (hsecm x hAincm) (hsecm x hAdecm) (hdp x) (hdm x)
    have hdBinc : ∀ ω ω', ω ∩ Sinc = ω' ∩ Sinc →
        (ω ∈ sec x Ainc ∩ Binc ↔ ω' ∈ sec x Ainc ∩ Binc) := fun ω ω' h => by
      simp only [mem_inter_iff]; rw [hdp x ω ω' h, hBincd ω ω' h]
    have hdBdec : ∀ ω ω', ω ∩ Sdec = ω' ∩ Sdec →
        (ω ∈ sec x Adec ∩ Bdec ↔ ω' ∈ sec x Adec ∩ Bdec) := fun ω ω' h => by
      simp only [mem_inter_iff]; rw [hdm x ω ω' h, hBdecd ω ω' h]
    have hindE : μ ((sec x Ainc ∩ Binc) ∩ (sec x Adec ∩ Bdec)) =
        μ (sec x Ainc ∩ Binc) * μ (sec x Adec ∩ Bdec) :=
      prodBernoulli_inter_of_determined p hSincdec ((hsecm x hAincm).inter hBincm)
        ((hsecm x hAdecm).inter hBdecm) hdBinc hdBdec
    have hhp : μ (sec x Ainc) * μ Binc ≤ μ (sec x Ainc ∩ Binc) :=
      prodBernoulli_harris p (hupper x hAinc) hBinc (hsecm x hAincm) hBincm
    have hhm : μ (sec x Adec) * μ Bdec ≤ μ (sec x Adec ∩ Bdec) :=
      prodBernoulli_harris_of_isLowerSet p (hlower x hAdec) hBdec (hsecm x hAdecm) hBdecm
    rw [hE, hindE, hA, hindA]
    calc μ (sec x Ainc) * μ (sec x Adec) * (μ Binc * μ Bdec)
        = (μ (sec x Ainc) * μ Binc) * (μ (sec x Adec) * μ Bdec) := by ring
      _ ≤ μ (sec x Ainc ∩ Binc) * μ (sec x Adec ∩ Bdec) := mul_le_mul' hhp hhm
  -- integrate over the configuration on `S`
  have hfin : μ Binc * μ Bdec ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [mul_assoc, prodBernoulli_eq_lintegral_splice p S (hAincm.inter hAdecm),
    prodBernoulli_eq_lintegral_splice p S ((hAincm.inter hAdecm).inter (hBincm.inter hBdecm)),
    ← lintegral_mul_const' _ _ hfin]
  exact lintegral_mono hpt

/-! ### Iterated disjoint occurrence -/

/-- Fixing coordinates of the complement forces an event exactly when fixing the same
coordinates of the configuration forces its preimage under complementing. -/
theorem forcesOn_preimage_compl_iff {A : Set (Set ι)} {ω F : Set ι} :
    ForcesOn (compl ⁻¹' A) ω F ↔ ForcesOn A ωᶜ F := by
  constructor
  · intro h η hη
    have := h ηᶜ fun i hi => by rw [mem_compl_iff, hη i hi, mem_compl_iff, not_not]
    simpa only [mem_preimage, compl_compl] using this
  · intro h η hη
    exact h ηᶜ fun i hi => by rw [mem_compl_iff, mem_compl_iff, hη i hi]

/-- **Disjoint occurrence commutes with complementing configurations.** -/
theorem preimage_compl_disjointOccurrence (A B : Set (Set ι)) :
    compl ⁻¹' disjointOccurrence A B = disjointOccurrence (compl ⁻¹' A) (compl ⁻¹' B) := by
  ext ω
  simp only [mem_preimage, disjointOccurrence, mem_ofPred_eq, forcesOn_preimage_compl_iff]

/-- Iterated disjoint occurrence commutes with complementing configurations. -/
theorem preimage_compl_foldl_disjointOccurrence (Bs : List (Set (Set ι))) (A : Set (Set ι)) :
    compl ⁻¹' Bs.foldl disjointOccurrence A =
      (Bs.map (compl ⁻¹' ·)).foldl disjointOccurrence (compl ⁻¹' A) := by
  induction Bs generalizing A with
  | nil => rfl
  | cons B Bs ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, preimage_compl_disjointOccurrence]

/-- **`h` disjoint occurrences of an increasing event** have probability at most `P(C)^h`, by BK,
on a countable index set and for every profile. The event `C` need not be measurable. -/
theorem prodBernoulli_foldl_replicate_le_pow [Countable ι] (p : ι → unitInterval)
    {C : Set (Set ι)} (hC : IsUpperSet C) (h : ℕ) :
    prodBernoulli p ((List.replicate h C).foldl disjointOccurrence univ) ≤
      prodBernoulli p C ^ h := by
  have := countable_profile_bk_foldl p (List.replicate h C)
    (fun B hB => (List.eq_of_mem_replicate hB) ▸ hC) isUpperSet_univ
  simpa only [measure_univ, one_mul, List.map_replicate, List.prod_replicate] using this

/-- **`h` disjoint occurrences of a measurable decreasing event** have probability at most
`P(D)^h`: BK applied to the complements of the configurations. -/
theorem prodBernoulli_foldl_replicate_le_pow_of_isLowerSet [Countable ι]
    (p : ι → unitInterval) {D : Set (Set ι)} (hD : IsLowerSet D) (hDm : MeasurableSet D)
    (h : ℕ) :
    prodBernoulli p ((List.replicate h D).foldl disjointOccurrence univ) ≤
      prodBernoulli p D ^ h := by
  set p' : ι → unitInterval := fun i => unitInterval.symm (p i)
  have hcc : (compl ⁻¹' (compl ⁻¹' D) : Set (Set ι)) = D := by
    ext ω; simp
  have hX : (List.replicate h D).foldl disjointOccurrence univ =
      compl ⁻¹' (List.replicate h (compl ⁻¹' D)).foldl disjointOccurrence univ := by
    rw [preimage_compl_foldl_disjointOccurrence, List.map_replicate, hcc, preimage_univ]
  have hD' : prodBernoulli p' (compl ⁻¹' D) = prodBernoulli p D := by
    rw [← prodBernoulli_map_compl, Measure.map_apply measurable_compl (measurable_compl hDm),
      hcc]
  rw [hX]
  calc prodBernoulli p (compl ⁻¹' (List.replicate h (compl ⁻¹' D)).foldl disjointOccurrence univ)
      ≤ (prodBernoulli p).map compl
          ((List.replicate h (compl ⁻¹' D)).foldl disjointOccurrence univ) :=
        Measure.le_map_apply measurable_compl.aemeasurable _
    _ = prodBernoulli p' ((List.replicate h (compl ⁻¹' D)).foldl disjointOccurrence univ) := by
        rw [prodBernoulli_map_compl]
    _ ≤ prodBernoulli p' (compl ⁻¹' D) ^ h :=
        prodBernoulli_foldl_replicate_le_pow p' (C := compl ⁻¹' D)
          (fun _ _ hab hb => hD (compl_le_compl hab) hb) h
    _ = prodBernoulli p D ^ h := by rw [hD']

end PercLib.Probability

/-! ### Non-vacuity -/

section Witnesses

open PercLib.Probability

-- Nolin's Lemma 13 with all four events nontrivial: `Ainc = {0 open}`, `Adec = {1 closed}`,
-- `Binc = {2 open}`, `Bdec = {3 closed}`, `S = ∅`, `Sinc = {0, 2}`, `Sdec = {1, 3}`.
example (p : ℕ → unitInterval) :
    prodBernoulli p ({ω : Set ℕ | 0 ∈ ω} ∩ {ω | 1 ∉ ω}) * prodBernoulli p {ω | 2 ∈ ω} *
        prodBernoulli p {ω | 3 ∉ ω} ≤
      prodBernoulli p ({ω : Set ℕ | 0 ∈ ω} ∩ {ω | 1 ∉ ω} ∩ ({ω | 2 ∈ ω} ∩ {ω | 3 ∉ ω})) := by
  refine prodBernoulli_mul_mul_le_inter_of_determined p (S := ∅) (Sinc := {0, 2}) (Sdec := {1, 3})
    (Set.empty_disjoint _) (Set.empty_disjoint _) (by simp)
    (fun _ _ h hx => h hx) (fun _ _ h hx hy => hx (h hy)) (fun _ _ h hx => h hx)
    (fun _ _ h hx hy => hx (h hy)) (measurableSet_mem 0) (measurableSet_mem 1).compl
    (measurableSet_mem 2) (measurableSet_mem 3).compl
    (fun ω ω' h => by simpa using congrArg (0 ∈ ·) h)
    (fun ω ω' h => by have := congrArg (1 ∈ ·) h; simp at this; simp [this])
    (fun ω ω' h => by simpa using congrArg (2 ∈ ·) h)
    (fun ω ω' h => by have := congrArg (3 ∈ ·) h; simp at this; simp [this])

-- Two disjoint occurrences of "coordinate `0` or coordinate `1` is closed".
example (p : ℕ → unitInterval) :
    prodBernoulli p ((List.replicate 2 {ω : Set ℕ | 0 ∉ ω ∨ 1 ∉ ω}).foldl disjointOccurrence
      Set.univ) ≤ prodBernoulli p {ω : Set ℕ | 0 ∉ ω ∨ 1 ∉ ω} ^ 2 :=
  prodBernoulli_foldl_replicate_le_pow_of_isLowerSet p
    (fun _ _ h hb => hb.imp (fun h0 h0' => h0 (h h0')) (fun h1 h1' => h1 (h h1')))
    ((measurableSet_mem 0).compl.union (measurableSet_mem 1).compl) 2

end Witnesses
