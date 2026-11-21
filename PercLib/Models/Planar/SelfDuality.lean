/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: G. Grimmett, Percolation, 2nd ed., Springer, 1999, Sections 11.2
and 11.3; B. Bollobás and O. Riordan, Percolation, Cambridge University Press, 2006, Chapter 3
(pp. 50-57).
-/
module

public import PercLib.Models.Planar.Duality
public import PercLib.Percolation.Bond.Transport
public import PercLib.Probability.DeterministicModification
public import PercLib.Probability.HarrisDecreasing
public import PercLib.Probability.Transport.Reindexing

/-!
# Crossing probability one half at the self-dual point

For bond percolation on `ℤ²` with every edge open with probability `1/2`, the box
`[lo₀, lo₀ + n + 1] × [lo₁, lo₁ + n]` has an open left-right crossing with probability exactly
`1/2`. The proof combines three facts.

* **Duality** (`crossing_zero_eq_compl_preimage_dualConfig`): the left-right crossing is the
  complement of the dual bottom-top crossing of the dual box
  `[lo₀, lo₀ + n] × [lo₁ - 1, lo₁ + n]`.
* **Self-duality of the law** (`law_preimage_dualConfig_eq`): when every edge of `ℤ²` is
  open with probability `1/2`, the dual configuration has the same law on the edges of `ℤ²`
  as the configuration, because the dual map is a bijection of the edges and closing an
  edge has the same probability as opening it.
* **Symmetry** (`law_preimage_image_sym2Map_eq`, `image_mem_crossing_iff`): exchanging the
  two coordinates and translating maps the dual box onto the box and its bottom-top
  crossing onto the left-right crossing, and leaves the law unchanged.

So the left-right crossing has probability `x = 1 - x`.

## Main results

* `PercLib.Models.Planar.law_crossing_zero_eq_half`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability

/-! ### Events that depend on the coordinates in a set -/

namespace PercLib.Probability

variable {ι : Type*}

/-- Under a product of Bernoulli laws, the probability of an event that depends only on the
coordinates in `E` depends only on the profile on `E`. -/
theorem prodBernoulli_eq_of_eqOn (E : Set ι) {p p' : ι → unitInterval} (h : EqOn p p' E)
    {A : Set (Set ι)} (hA : MeasurableSet A) (hAE : ∀ ω, ω ∩ E ∈ A ↔ ω ∈ A) :
    prodBernoulli p A = prodBernoulli p' A := by
  classical
  have hpre : A = (fun ω : Set ι => ω ∩ E) ⁻¹' A := by
    ext ω
    exact (hAE ω).symm
  have hm : Measurable fun ω : Set ι => ω ∩ E := by fun_prop
  rw [hpre, ← Measure.map_apply hm hA, ← Measure.map_apply hm hA, prodBernoulli_map_inter,
    prodBernoulli_map_inter]
  congr 2
  funext i
  split_ifs with hi
  · exact h hi
  · rfl

end PercLib.Probability

/-! ### Transport of connections inside a set -/

namespace PercLib.Percolation.Bond

variable {V W : Type*}

/-- Connections inside a set are carried along a bijection of the vertices. -/
theorem image_mem_localConn_iff (σ : V ≃ W) (ω : Config V) (S : Set V) (x y : V) :
    Sym2.map σ '' ω ∈ localConn (σ '' S) (σ x) (σ y) ↔ ω ∈ localConn S x y := by
  let φ : (openGraph ω).induce S ≃g (openGraph (Sym2.map σ '' ω)).induce (σ '' S) :=
    { toEquiv := Equiv.Set.image σ S σ.injective
      map_rel_iff' := fun {a b} => openGraph_image_adj_iff σ ω a.1 b.1 }
  constructor
  · rintro ⟨hx, hy, h⟩
    have hx' : x ∈ S := σ.injective.mem_set_image.1 hx
    have hy' : y ∈ S := σ.injective.mem_set_image.1 hy
    exact ⟨hx', hy', (SimpleGraph.Iso.reachable_iff (φ := φ) (u := ⟨x, hx'⟩)
      (v := ⟨y, hy'⟩)).1 h⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨mem_image_of_mem σ hx, mem_image_of_mem σ hy,
      (SimpleGraph.Iso.reachable_iff (φ := φ) (u := ⟨x, hx⟩) (v := ⟨y, hy⟩)).2 h⟩

/-- A graph automorphism maps the edge set onto itself. -/
theorem image_sym2Map_edgeSet {G : SimpleGraph V} (σ : G ≃g G) :
    Sym2.map σ '' G.edgeSet = G.edgeSet := by
  ext f
  constructor
  · rintro ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h u v => exact σ.map_adj_iff.2 he
  · intro hf
    refine ⟨Sym2.map σ.symm f, ?_, ?_⟩
    · induction f using Sym2.ind with
      | h u v =>
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, ← σ.map_adj_iff, σ.apply_symm_apply,
          σ.apply_symm_apply]
        exact hf
    · have h : (⇑σ ∘ ⇑σ.symm) = id := funext σ.apply_symm_apply
      rw [Sym2.map_map, h, Sym2.map_id, id]

/-- **Symmetry of the law.** A graph automorphism of `G` that preserves the profile on the edges
of `G` preserves the probability of every event that depends only on the edges of `G`. -/
theorem law_preimage_image_sym2Map_eq {G : SimpleGraph V} (σ : G ≃g G)
    {q : Sym2 V → unitInterval} (hq : ∀ e ∈ G.edgeSet, q (Sym2.map σ e) = q e)
    {A : Set (Config V)} (hA : MeasurableSet A) (hAG : ∀ ω, ω ∩ G.edgeSet ∈ A ↔ ω ∈ A) :
    law q ((fun ω : Config V => Sym2.map σ '' ω) ⁻¹' A) = law q A := by
  have hm : Measurable fun ω : Config V => Sym2.map σ.toEquiv '' ω :=
    (measurable_image_sym2Map σ.toEquiv)
  change prodBernoulli q ((fun ω : Config V => Sym2.map σ.toEquiv '' ω) ⁻¹' A) = prodBernoulli q A
  rw [← Measure.map_apply hm hA, prodBernoulli_map_image_sym2]
  refine prodBernoulli_eq_of_eqOn G.edgeSet (fun e he => ?_) hA hAG
  have he' : Sym2.map σ.symm e ∈ G.edgeSet := by
    rw [← image_sym2Map_edgeSet σ.symm]
    exact mem_image_of_mem _ he
  have hσσ : Sym2.map σ (Sym2.map σ.symm e) = e := by
    have h : (⇑σ ∘ ⇑σ.symm) = id := funext σ.apply_symm_apply
    rw [Sym2.map_map, h, Sym2.map_id, id]
  have h := hq _ he'
  rw [hσσ] at h
  exact h.symm

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

/-! ### Transport of crossings -/

/-- A crossing is carried along an automorphism of `ℤ^d` that maps the box onto a box and the
two faces in direction `i` onto the two faces in direction `j`. -/
theorem image_mem_crossing_iff {d : ℕ} (σ : zdGraph d ≃g zdGraph d) {i j : Fin d}
    {lo hi lo' hi' : LatticeSite d} (hbox : σ '' Icc lo hi = Icc lo' hi')
    (hlo : ∀ v ∈ Icc lo hi, σ v j = lo' j ↔ v i = lo i)
    (hhi : ∀ v ∈ Icc lo hi, σ v j = hi' j ↔ v i = hi i) (ω : Config (LatticeSite d)) :
    Sym2.map σ '' ω ∈ crossing j lo' hi' ↔ ω ∈ crossing i lo hi := by
  have hL : Sym2.map σ '' ω ∩ (zdGraph d).edgeSet =
      Sym2.map σ '' (ω ∩ (zdGraph d).edgeSet) := by
    rw [image_inter (Sym2.map.injective σ.injective)]
    congr 1
    exact (image_sym2Map_edgeSet σ).symm
  constructor
  · rintro ⟨a', ha', ha'j, b', hb', hb'j, hab⟩
    rw [← hbox] at ha' hb'
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, rfl⟩ := hb'
    rw [hL, ← hbox] at hab
    exact ⟨a, ha, (hlo a ha).1 ha'j, b, hb, (hhi b hb).1 hb'j,
      (image_mem_localConn_iff σ.toEquiv _ _ a b).1 hab⟩
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    refine ⟨σ a, hbox ▸ mem_image_of_mem σ ha, (hlo a ha).2 hai, σ b,
      hbox ▸ mem_image_of_mem σ hb, (hhi b hb).2 hbi, ?_⟩
    rw [hL, ← hbox]
    exact (image_mem_localConn_iff σ.toEquiv _ _ a b).2 hab

/-! ### Self-duality of the law at one half -/

/-- **Self-duality.** When every edge of `ℤ²` is open with probability `1/2`, an event that
depends only on the edges of `ℤ²` has the same probability for the dual configuration as for
the configuration. -/
theorem law_preimage_dualConfig_eq {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {A : Set (Config (LatticeSite 2))}
    (hA : MeasurableSet A) (hAL : ∀ ω, ω ∩ (zdGraph 2).edgeSet ∈ A ↔ ω ∈ A) :
    law q (dualConfig ⁻¹' A) = law q A := by
  classical
  set L := (zdGraph 2).edgeSet with hL
  -- the dual map, extended by the identity off the edges of `ℤ²`
  set T : Equiv.Perm (Sym2 (LatticeSite 2)) := Equiv.Perm.ofSubtype dualEdgeEquiv with hT
  have hTL : ∀ e, T e ∈ L ↔ e ∈ L := fun e => Equiv.Perm.ofSubtype_apply_mem_iff_mem _ e
  have hTe : ∀ e (he : e ∈ L), T e = dualEdge e := fun e he => by
    rw [hT, Equiv.Perm.ofSubtype_apply_of_mem _ he, dualEdgeEquiv_apply]
  have hdual : ∀ ω, dualConfig ω ∩ L = T '' ωᶜ ∩ L := by
    intro ω
    ext f
    constructor
    · rintro ⟨⟨e, ⟨he, heω⟩, rfl⟩, hf⟩
      exact ⟨⟨e, heω, hTe e he⟩, hf⟩
    · rintro ⟨⟨e, heω, rfl⟩, hf⟩
      have he := (hTL e).1 hf
      exact ⟨⟨e, ⟨he, heω⟩, (hTe e he).symm⟩, hf⟩
  have hpre : dualConfig ⁻¹' A = ((fun ω => T '' ω) ∘ compl) ⁻¹' A := by
    ext ω
    simp only [mem_preimage, Function.comp_apply]
    rw [← hAL (dualConfig ω), ← hAL (T '' ωᶜ), hdual]
  have hmT : Measurable fun ω : Config (LatticeSite 2) => T '' ω := measurable_image_equiv T
  change prodBernoulli q (dualConfig ⁻¹' A) = prodBernoulli q A
  rw [hpre, ← Measure.map_apply (hmT.comp measurable_compl) hA,
    ← Measure.map_map hmT measurable_compl, prodBernoulli_map_compl,
    prodBernoulli_map_image_equiv]
  refine prodBernoulli_eq_of_eqOn L (fun e he => ?_) hA hAL
  have he' : T.symm e ∈ L := by
    rw [← hTL, Equiv.apply_symm_apply]
    exact he
  apply Subtype.ext
  simp only [Function.comp_apply, unitInterval.coe_symm_eq]
  rw [hq _ he', hq _ he]
  norm_num

/-! ### Crossing probability one half -/

/-- **The crossing probability of a box at the self-dual point.** If every edge of `ℤ²` is
open with probability `1/2` (whatever the profile off the edges of `ℤ²`), the box
`[lo₀, lo₀ + n + 1] × [lo₁, lo₁ + n]` has an open left-right crossing with probability
`1/2`. -/
theorem law_crossing_zero_eq_half (lo : LatticeSite 2) (n : ℕ)
    {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) :
    law q (crossing 0 lo (lo + ![(n : ℤ) + 1, n])) = 1 / 2 := by
  set hi : LatticeSite 2 := lo + ![(n : ℤ) + 1, n] with hhi
  have hhi0 : hi 0 = lo 0 + (n + 1) := by
    rw [hhi, Pi.add_apply, Matrix.cons_val_zero]
  have hhi1 : hi 1 = lo 1 + n := by
    rw [hhi, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hle : lo ≤ hi := by
    refine Pi.le_def.2 fun i => ?_
    fin_cases i
    · change lo 0 ≤ hi 0
      omega
    · change lo 1 ≤ hi 1
      omega
  set E := crossing 0 lo hi with hE
  set D := crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] with hD
  have hEm : MeasurableSet E := measurableSet_crossing _ _ _
  have hDm : MeasurableSet D := measurableSet_crossing _ _ _
  -- duality
  have h1 : law q E = 1 - law q (dualConfig ⁻¹' D) := by
    rw [hE, crossing_zero_eq_compl_preimage_dualConfig hle, prob_compl_eq_one_sub
      (measurable_dualConfig hDm)]
  -- self-duality
  have h2 : law q (dualConfig ⁻¹' D) = law q D :=
    law_preimage_dualConfig_eq hq hDm (inter_edgeSet_mem_crossing_iff _ _ _)
  -- symmetry: exchange the coordinates and translate
  have h3 : law q D = law q E := by
    obtain ⟨φ₁, hφ₁⟩ := exists_zdGraph_iso_perm (d := 2) (Equiv.swap 0 1)
    obtain ⟨φ₂, hφ₂⟩ := exists_zdGraph_iso_add (d := 2) ![lo 0 + 1 - lo 1, lo 1 - lo 0]
    set φ := φ₁.trans φ₂ with hφdef
    have hφ : ∀ v, φ v 0 = v 1 + (lo 0 + 1 - lo 1) ∧ φ v 1 = v 0 + (lo 1 - lo 0) := by
      intro v
      refine ⟨?_, ?_⟩ <;> simp [hφdef, hφ₁, hφ₂]
    have hbox : φ '' Icc ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] = Icc lo hi := by
      ext w
      simp only [mem_image, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor
      · rintro ⟨v, hv, rfl⟩
        have := hφ v
        omega
      · intro hw
        refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
        have := hφ (φ.symm w)
        rw [φ.apply_symm_apply] at this
        omega
    have hlo : ∀ v ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1],
        φ v 0 = lo 0 ↔ v 1 = (![lo 0, lo 1 - 1] : LatticeSite 2) 1 := by
      intro v _
      have := hφ v
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    have hhi' : ∀ v ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1],
        φ v 0 = hi 0 ↔ v 1 = (![hi 0 - 1, hi 1] : LatticeSite 2) 1 := by
      intro v _
      have := hφ v
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    have hDE : D = (fun ω => Sym2.map φ '' ω) ⁻¹' E := by
      ext ω
      exact (image_mem_crossing_iff φ hbox hlo hhi' ω).symm
    have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q (Sym2.map φ e) = q e := by
      intro e he
      have he' : Sym2.map φ e ∈ (zdGraph 2).edgeSet := by
        rw [← image_sym2Map_edgeSet φ]
        exact mem_image_of_mem _ he
      exact Subtype.ext (by rw [hq _ he', hq _ he])
    rw [hDE]
    exact law_preimage_image_sym2Map_eq φ hq' hEm (inter_edgeSet_mem_crossing_iff _ _ _)
  -- `x = 1 - x`
  have hx : law q E = 1 - law q E := by
    conv_lhs => rw [h1, h2, h3]
  have hsum : law q E + law q E = 1 := by
    conv_rhs => rw [← add_tsub_cancel_of_le (prob_le_one : law q E ≤ 1)]
    rw [← hx]
  rw [ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top, two_mul, hsum]

/-! ### Non-vacuity -/

/-- The hypothesis holds for the homogeneous law at one half: the box `[0, 2] × [0, 1]` is
crossed from left to right with probability `1/2`. -/
example : law (fun _ : Sym2 (LatticeSite 2) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
    (crossing 0 0 (0 + ![((1 : ℕ) : ℤ) + 1, (1 : ℕ)])) = 1 / 2 :=
  law_crossing_zero_eq_half 0 1 fun _ _ => rfl

end PercLib.Models.Planar
