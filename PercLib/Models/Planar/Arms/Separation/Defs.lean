/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22 and 2026-11-23. No upstream code is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (separated arms, Theorem 11 and Lemma 15).
-/
module

public import PercLib.Models.Planar.Arms.Defs

/-!
# Separated arms

Notions for the separation of arms (Nolin, Section 4.4), on the arm events of
`PercLib.Models.Planar.Arms.Defs`.

## Main results

* `dualConfig_inter_eq_of_inter_eq`: the dual edges between faces of a box are determined by the
  edges of the box enlarged by one.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

namespace PercLib.Models.Planar

/-- **Duals inside a box of faces.** Whether the dual edges between faces of the box
`Icc lo hi` are open in `dualConfig ω` depends only on the edges of `ℤ²` with both ends in
`Icc lo (hi + 1)`: such a dual edge crosses an edge whose ends are corners of its two faces. -/
theorem dualConfig_inter_eq_of_inter_eq {lo hi : LatticeSite 2} {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} = ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)}) :
    dualConfig ω ∩ {f | ∀ g ∈ f, g ∈ Icc lo hi} = dualConfig ω' ∩ {f | ∀ g ∈ f, g ∈ Icc lo hi} := by
  have key : ∀ f : Sym2 (LatticeSite 2), f ∈ (zdGraph 2).edgeSet → (∀ g ∈ f, g ∈ Icc lo hi) →
      (Sym2.map (· + 1) (dualEdge f) ∈ ω ↔ Sym2.map (· + 1) (dualEdge f) ∈ ω') := by
    intro f hf hfg
    set e := Sym2.map (· + 1) (dualEdge f) with he
    have heE : e ∈ (zdGraph 2).edgeSet := map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hf)
    have hde : dualEdge e = f := congrArg Subtype.val (dualEdgeEquiv.right_inv ⟨f, hf⟩)
    have heP : ∀ v ∈ e, v ∈ Icc lo (hi + 1) := by
      intro v hv
      obtain ⟨g, hg⟩ : ∃ g, g ∈ f := ⟨(Quot.out f).1, Sym2.out_fst_mem f⟩
      have hvg := mem_Icc_of_mem_dualEdge heE hv (hde ▸ hg)
      have hgB := hfg g hg
      refine ⟨hgB.1.trans hvg.1, fun i => ?_⟩
      have h₁ : v i ≤ (g + 1) i := hvg.2 i
      have h₂ : g i ≤ hi i := hgB.2 i
      simp only [Pi.add_apply, Pi.one_apply] at h₁ ⊢
      omega
    constructor
    · intro hω
      have : e ∈ ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} := ⟨hω, heP⟩
      rw [h] at this
      exact this.1
    · intro hω
      have : e ∈ ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} := ⟨hω, heP⟩
      rw [← h] at this
      exact this.1
  ext f
  simp only [mem_inter_iff, mem_ofPred_eq, mem_dualConfig_iff]
  constructor
  · rintro ⟨⟨hf, hω⟩, hfg⟩
    exact ⟨⟨hf, fun h' => hω ((key f hf hfg).2 h')⟩, hfg⟩
  · rintro ⟨⟨hf, hω⟩, hfg⟩
    exact ⟨⟨hf, fun h' => hω ((key f hf hfg).1 h')⟩, hfg⟩

end PercLib.Models.Planar
