/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation) and the proof of
Theorem 11 (separation at the internal extremities).
-/
module

public import PercLib.Models.Planar.Arms.SeparationSides
public import PercLib.Probability.HarrisDecreasing
public import PercLib.Probability.Transport.Reindexing

/-!
# Local separation in wide strips and in the dual lattice

Nolin's local separation lemma (Lemma 15) for strips `[lo₀, lo₀ + wN] × [lo₁, lo₁ + N]` of any
width `w ≥ 1` (`exists_law_separable_ge_strip`), the finite box of edges that determines its event
(`mem_separable_strip_of_inter_eq`), and its use for the dual configuration.

At the inner boundary of an annulus the crossings to be rerouted run towards the inner box, and
the dual arms start in the faces next to it. A reflection of the lattice moves faces by one row
against vertices, so no image of Lemma 15 under a symmetry of `ℤ²` fits both colours at the inner
boundary. Lemma 15 applied to the dual configuration, with the faces as the vertices of a copy of
`ℤ²`, fits: its open crossings are our dual walks and its dual crossings are our open walks moved
by `(-1, -1)`. The dual configuration is the image of the configuration under a measurable
bijection of configurations (`exists_measurableEquiv_dualConfig`): the complement followed by the
relabelling of every edge by its dual edge. Its law is a product law with the same crossing bounds.

## Main results

* `exists_law_separable_ge_strip`: Lemma 15 in a strip of any width, at any position.
* `mem_separable_strip_of_inter_eq`: its event is determined by a finite box of edges.
* `exists_equiv_dualEdge`, `exists_measurableEquiv_dualConfig`: the dual configuration as a
  measurable bijection of configurations, its law and its crossing bounds.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site

open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Lemma 15 in a wide strip -/

/-- **Local separation in a strip of any width** (Nolin's Lemma 15,
`exists_law_separable_ge_aux_wide` at `k = 0`), for families indexed by any finite type. For every
width `w ≥ 1` and every `δ > 0` there are `0 < η ≤ 1` and `N₀` such that, uniformly over the laws
with crossing bounds `c` up to `L`, for `N₀ ≤ N ≤ L`, with probability at least `1 - δ` the
separation property holds in the open box `Icc lo hi = [lo₀, lo₀ + wN] × [lo₁, lo₁ + N]` with the
faces `[lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]`, at any position. -/
theorem exists_law_separable_ge_strip (c : ℕ → ℝ≥0∞) (w : ℕ) (hw : 1 ≤ w) {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (lo hi : LatticeSite 2) (N : ℕ), hi 0 = lo 0 + w * N →
      hi 1 = lo 1 + N → N₀ ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = lo 1 ∧ b i 1 = hi 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = lo 1 - 1 ∧ b i 1 = hi 1 ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
              ![hi 0 - 1, hi 1]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lo hi})) →
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
        ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i)
            (a i 1 = lo 1 ∧ b' i 1 = hi 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo hi) ∧
              ∀ e ∈ (γ' i).edges, e ∈ ω)
            (a i 1 = lo 1 - 1 ∧ b' i 1 = hi 1 ∧
              (∀ x ∈ (γ' i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
                ![hi 0 - 1, hi 1]) ∧
              ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
                ∀ x ∈ e, x ∈ Icc lo hi})) ∧
          (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hi 1) ∧
          (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lo 0 : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ ((2 * hi 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, hi 1]
                ![b' i 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  obtain ⟨η, hη, hη1, N₀, hsep⟩ := exists_law_separable_ge_aux_wide c w hw hδ
  refine ⟨η, hη, hη1, N₀, fun q L h lo hi N hhi0 hhi1 hN hNL => (hsep q L h N hN hNL 0
    lo hi ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1] lo hi le_rfl zero_le_one
    (eq_vec_two_iff.2 ⟨hhi0, hhi1⟩) (eq_vec_two_iff.2 ⟨by simp, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩) (eq_vec_two_iff.2 ⟨by simp, by simp⟩)
    (eq_vec_two_iff.2 ⟨by simp, by simp⟩)).trans
    (measure_mono fun ω hω => ?_)⟩
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨b'', γ'', h1, h2, h3, h4, h5, h6⟩ := hω m (fun k => σ (e.symm k))
    (fun k => a (e.symm k)) (fun k => b (e.symm k)) (fun k => γ (e.symm k))
    (fun k => hcr (e.symm k))
    (fun k k' hkk' hσ => hdisj _ _ (fun h => hkk' (e.symm.injective h)) hσ)
  refine ⟨fun i => b'' (e i),
    fun i => (γ'' (e i)).copy (congrArg a (e.symm_apply_apply i)) rfl, fun i => ?_,
    fun i k hik hσ x hx => ?_, fun i x hx => ?_, fun i k hik => ?_, fun i => ?_, fun i => ?_⟩
  · have := h1 (e i)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.edges_copy] using this
  · simp only [SimpleGraph.Walk.support_copy] at hx ⊢
    refine h2 (e i) (e k) (e.injective.ne hik) ?_ x hx
    simpa only [Equiv.symm_apply_apply] using hσ
  · simp only [SimpleGraph.Walk.support_copy] at hx
    exact h5 (e i) x hx
  · have := h3 (e i) (e k) (e.injective.ne hik)
    simpa only [Equiv.symm_apply_apply] using this
  · have := h4 (e i)
    simpa only [Equiv.symm_apply_apply] using this
  · have := h6 (e i)
    simp only [Equiv.symm_apply_apply] at this
    simpa only [SimpleGraph.Walk.support_copy] using this

/-- **Determination of the strip event.** The event of `exists_law_separable_ge_strip` depends
only on the edges with both ends in the box
`[lo₀ - M - K - 1, hi₀ + M + K + 1] × [lo₁ - 1, hi₁ + M + 1]`, `M = ⌊√η N⌋`, `K = ⌊η N⌋`, when
`lo₁ + M ≤ hi₁`: the open crossings and their fences use only such edges, and the dual crossings
and their fences cross only such edges. -/
theorem mem_separable_strip_of_inter_eq {η : ℝ} {N : ℕ} {lo hi : LatticeSite 2}
    (hM : lo 1 + ⌊Real.sqrt η * N⌋₊ ≤ hi 1) {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc
        (![lo 0 - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊ - 1, lo 1 - 1] : LatticeSite 2)
        ![hi 0 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊ + 1, hi 1 + ⌊Real.sqrt η * N⌋₊ + 1]} =
      ω' ∩ {e | ∀ v ∈ e, v ∈ Icc
        (![lo 0 - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊ - 1, lo 1 - 1] : LatticeSite 2)
        ![hi 0 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊ + 1, hi 1 + ⌊Real.sqrt η * N⌋₊ + 1]})
    (hω : ω ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lo 1 ∧ b i 1 = hi 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lo 1 - 1 ∧ b i 1 = hi 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
            ![hi 0 - 1, hi 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lo hi})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lo 1 ∧ b' i 1 = hi 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo hi) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lo 1 - 1 ∧ b' i 1 = hi 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
              ![hi 0 - 1, hi 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lo hi})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hi 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lo 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hi 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hi 1]
              ![b' i 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}) :
    ω' ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lo 1 ∧ b i 1 = hi 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lo 1 - 1 ∧ b i 1 = hi 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
            ![hi 0 - 1, hi 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lo hi})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lo 1 ∧ b' i 1 = hi 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo hi) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lo 1 - 1 ∧ b' i 1 = hi 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
              ![hi 0 - 1, hi 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lo hi})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hi 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lo 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hi 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hi 1]
              ![b' i 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := by
  set M := ⌊Real.sqrt η * N⌋₊ with hMdef
  set K := ⌊η * N⌋₊ with hKdef
  set Tlo : LatticeSite 2 := ![lo 0 - M - K - 1, lo 1 - 1] with hTlo
  set Thi : LatticeSite 2 := ![hi 0 + M + K + 1, hi 1 + M + 1] with hThi
  have hTlo0 : Tlo 0 = lo 0 - M - K - 1 := rfl
  have hTlo1 : Tlo 1 = lo 1 - 1 := rfl
  have hThi0 : Thi 0 = hi 0 + M + K + 1 := rfl
  have hThi1 : Thi 1 = hi 1 + M + 1 := rfl
  -- edges in the box are open in both or in neither
  have hedge : ∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, v ∈ Icc Tlo Thi) → (e ∈ ω ↔ e ∈ ω') := by
    intro e he
    have := congrArg (e ∈ ·) h
    simp only [mem_inter_iff, eq_iff_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
  -- the ends of the edges of a walk are vertices of the walk
  have hsupp : ∀ {u v : LatticeSite 2} (p : (zdGraph 2).Walk u v) (e : Sym2 (LatticeSite 2)),
      e ∈ p.edges → ∀ x ∈ e, x ∈ p.support := by
    intro u v p e he x hx
    induction e using Sym2.ind with
    | h s t =>
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact p.fst_mem_support_of_mem_edges he
      · exact p.snd_mem_support_of_mem_edges he
  have hbox : ∀ x : LatticeSite 2, x ∈ Icc lo hi → x ∈ Icc Tlo Thi := by
    intro x hx
    have := mem_Icc_two_iff.1 hx
    rw [mem_Icc_two_iff, hTlo0, hTlo1, hThi0, hThi1]
    omega
  -- the hypothesis and the first conclusion transfer between configurations agreeing on the box
  have key : ∀ ω₁ ω₂ : Config (LatticeSite 2),
      (∀ e : Sym2 (LatticeSite 2), (∀ v ∈ e, v ∈ Icc Tlo Thi) → (e ∈ ω₁ ↔ e ∈ ω₂)) →
      ∀ (c : Bool) {u v : LatticeSite 2} (p : (zdGraph 2).Walk u v), cond c
        (u 1 = lo 1 ∧ v 1 = hi 1 ∧ (∀ x ∈ p.support, x ∈ Icc lo hi) ∧
          ∀ e ∈ p.edges, e ∈ ω₁)
        (u 1 = lo 1 - 1 ∧ v 1 = hi 1 ∧
          (∀ x ∈ p.support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1]) ∧
          ∀ e ∈ p.edges, e ∈ dualConfig ω₁ ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lo hi}) →
      cond c
        (u 1 = lo 1 ∧ v 1 = hi 1 ∧ (∀ x ∈ p.support, x ∈ Icc lo hi) ∧
          ∀ e ∈ p.edges, e ∈ ω₂)
        (u 1 = lo 1 - 1 ∧ v 1 = hi 1 ∧
          (∀ x ∈ p.support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2) ![hi 0 - 1, hi 1]) ∧
          ∀ e ∈ p.edges, e ∈ dualConfig ω₂ ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lo hi}) := by
    intro ω₁ ω₂ h₁₂ c u v p hp
    cases c
    · obtain ⟨hu, hv, hS, hE⟩ := hp
      refine ⟨hu, hv, hS, fun e he => ?_⟩
      obtain ⟨hd, e₀, ⟨he₀, he₀B⟩, rfl⟩ := hE e he
      refine ⟨?_, e₀, ⟨he₀, he₀B⟩, rfl⟩
      rw [dualEdge_mem_dualConfig_iff he₀] at hd ⊢
      exact fun h' => hd ((h₁₂ e₀ fun x hx => hbox x (he₀B x hx)).2 h')
    · obtain ⟨hu, hv, hS, hE⟩ := hp
      exact ⟨hu, hv, hS, fun e he =>
        (h₁₂ e fun x hx => hbox x (hS x (hsupp p e he x hx))).1 (hE e he)⟩
  -- connections inside boxes of `Icc Tlo (Thi - 1)` transfer
  have hD : dualConfig ω ∩ {f | ∀ g ∈ f, g ∈ Icc Tlo (Thi - 1)} =
      dualConfig ω' ∩ {f | ∀ g ∈ f, g ∈ Icc Tlo (Thi - 1)} :=
    dualConfig_inter_eq_of_inter_eq (by rwa [sub_add_cancel])
  have hconn : ∀ (c : Bool) (S : Set (LatticeSite 2)) (x y : LatticeSite 2),
      S ⊆ Icc Tlo (Thi - 1) →
      cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn S x y →
      cond c ω' (dualConfig ω') ∩ (zdGraph 2).edgeSet ∈ localConn S x y := by
    intro c S x y hS hxy
    cases c
    · exact (inter_mem_localConn_iff_of_inter_eq hS _ hD x y).1 hxy
    · exact (inter_mem_localConn_iff_of_inter_eq (hS.trans (Icc_subset_Icc le_rfl
        (sub_le_self _ zero_le_one))) _ h x y).1 hxy
  have hsub : ∀ A B : LatticeSite 2, Tlo 0 ≤ A 0 → Tlo 1 ≤ A 1 → B 0 ≤ Thi 0 - 1 →
      B 1 ≤ Thi 1 - 1 → Icc A B ⊆ Icc Tlo (Thi - 1) := by
    intro A B h₁ h₂ h₃ h₄
    refine Icc_subset_Icc ?_ ?_
    · rw [Pi.le_def, Fin.forall_fin_two]
      exact ⟨h₁, h₂⟩
    · rw [Pi.le_def, Fin.forall_fin_two]
      simp only [Pi.sub_apply, Pi.one_apply]
      exact ⟨h₃, h₄⟩
  intro ι _ σ a b γ hcr hdisj
  obtain ⟨b', γ', h1, h2, h3, h4, h5, h6⟩ := hω ι σ a b γ
    (fun i => key ω' ω (fun e he => (hedge e he).symm) (σ i) (γ i) (hcr i)) hdisj
  refine ⟨b', γ', fun i => key ω ω' hedge (σ i) (γ' i) (h1 i), h2, h3, h4, h5, fun i => ?_⟩
  -- the end of the new crossing lies in the strip
  have hb' : lo 0 ≤ b' i 0 ∧ b' i 0 ≤ hi 0 ∧ b' i 1 = hi 1 := by
    have hi := h1 i
    revert hi
    cases σ i
    · rintro ⟨-, hv, hS, -⟩
      have := mem_Icc_two_iff.1 (hS _ (γ' i).end_mem_support)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
    · rintro ⟨-, hv, hS, -⟩
      have := mem_Icc_two_iff.1 (hS _ (γ' i).end_mem_support)
      omega
  obtain ⟨x, hx, l, r, hl, hr, hlr, hxl⟩ := h6 i
  refine ⟨x, hx, l, r, hl, hr, hconn _ _ _ _ (hsub _ _ ?_ ?_ ?_ ?_) hlr,
    hconn _ _ _ _ (hsub _ _ ?_ ?_ ?_ ?_) hxl⟩ <;>
    simp only [hTlo0, hTlo1, hThi0, hThi1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] <;> omega

/-! ### The dual configuration as a bijection of configurations -/

/-- **The relabelling by dual edges**: a bijection of the pairs of `ℤ²` that maps every edge of
`ℤ²` to its dual edge and fixes the other pairs. -/
theorem exists_equiv_dualEdge : ∃ E : Sym2 (LatticeSite 2) ≃ Sym2 (LatticeSite 2),
    (∀ e ∈ (zdGraph 2).edgeSet, E e = dualEdge e) ∧ ∀ e ∉ (zdGraph 2).edgeSet, E e = e := by
  classical
  refine ⟨Equiv.Perm.subtypeCongr dualEdgeEquiv (Equiv.refl _), fun e he => ?_, fun e he => ?_⟩
  · rw [Equiv.Perm.subtypeCongr.apply, dite_eq_left_of_eq_true (eq_true he)]
    rfl
  · rw [Equiv.Perm.subtypeCongr.apply, dite_eq_right_of_eq_false (eq_false he)]
    rfl

/-- **The dual configuration as a measurable bijection of configurations.** There is a measurable
bijection `Φ` of configurations (the complement, followed by the relabelling of every edge by its
dual edge) whose pairs that are edges of `ℤ²` form the dual configuration. The image of every
product law under `Φ` is a product law with the same crossing bounds: its open crossings are the
dual crossings of the original law, and its dual crossings are the open crossings moved by
`(-1, -1)`. Its pairs inside a box `Icc A B` are determined by the pairs of the configuration inside
`Icc A (B + 1)` (an edge between faces of `Icc A B` crosses an edge inside `Icc A (B + 1)`). -/
theorem exists_measurableEquiv_dualConfig :
    ∃ Φ : Config (LatticeSite 2) ≃ᵐ Config (LatticeSite 2),
      (∀ ω, Φ ω ∩ (zdGraph 2).edgeSet = dualConfig ω) ∧
      (∀ (A B : LatticeSite 2) (ω ω' : Config (LatticeSite 2)),
        ω ∩ {e | ∀ v ∈ e, v ∈ Icc A (B + 1)} = ω' ∩ {e | ∀ v ∈ e, v ∈ Icc A (B + 1)} →
        Φ ω ∩ {e | ∀ v ∈ e, v ∈ Icc A B} = Φ ω' ∩ {e | ∀ v ∈ e, v ∈ Icc A B}) ∧
      ∀ q : Sym2 (LatticeSite 2) → unitInterval, ∃ q' : Sym2 (LatticeSite 2) → unitInterval,
        (law q).map Φ = law q' ∧ ∀ (L : ℕ∞) (c : ℕ → ℝ≥0∞), CrossingBounds q L c →
          CrossingBounds q' L c := by
  classical
  obtain ⟨E, hE₁, hE₂⟩ := exists_equiv_dualEdge
  have hEE : ∀ e, E e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet := by
    intro e
    by_cases he : e ∈ (zdGraph 2).edgeSet
    · rw [hE₁ e he]
      exact ⟨fun _ => he, fun _ => dualEdge_mem_edgeSet he⟩
    · rw [hE₂ e he]
  let Φ : Config (LatticeSite 2) ≃ᵐ Config (LatticeSite 2) :=
    { toFun := fun X => E '' Xᶜ
      invFun := fun Y => (E.symm '' Y)ᶜ
      left_inv := fun X => by
        simp only [Equiv.symm_image_image, compl_compl]
      right_inv := fun Y => by
        simp only [compl_compl, Equiv.image_symm_image]
      measurable_toFun := (PercLib.Probability.measurable_image_equiv E).comp measurable_compl
      measurable_invFun :=
        measurable_compl.comp (PercLib.Probability.measurable_image_equiv E.symm) }
  have hΦapp : ∀ X, Φ X = E '' Xᶜ := fun X => rfl
  have hΦ : ∀ ω, Φ ω ∩ (zdGraph 2).edgeSet = dualConfig ω := by
    intro ω
    ext f
    rw [hΦapp]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hf⟩
      have he' : e ∈ (zdGraph 2).edgeSet := (hEE e).1 hf
      rw [hE₁ e he']
      exact (mem_dualConfig_iff' ω _).2 ⟨e, he', he, rfl⟩
    · intro hf
      obtain ⟨e, he, heω, rfl⟩ := (mem_dualConfig_iff' ω f).1 hf
      exact ⟨⟨e, heω, hE₁ e he⟩, dualEdge_mem_edgeSet he⟩
  have hdet : ∀ (A B : LatticeSite 2) (ω ω' : Config (LatticeSite 2)),
      ω ∩ {e | ∀ v ∈ e, v ∈ Icc A (B + 1)} = ω' ∩ {e | ∀ v ∈ e, v ∈ Icc A (B + 1)} →
      Φ ω ∩ {e | ∀ v ∈ e, v ∈ Icc A B} = Φ ω' ∩ {e | ∀ v ∈ e, v ∈ Icc A B} := by
    intro A B ω ω' h
    -- the pair relabelled to `f` has its ends in `Icc A (B + 1)`
    have hpre : ∀ f : Sym2 (LatticeSite 2), (∀ v ∈ f, v ∈ Icc A B) →
        ∀ v ∈ E.symm f, v ∈ Icc A (B + 1) := by
      intro f hf v hv
      by_cases hfe : f ∈ (zdGraph 2).edgeSet
      · have hEs : E.symm f = Sym2.map (· + 1) (dualEdge f) := by
          apply E.injective
          rw [Equiv.apply_symm_apply, hE₁ _ (map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hfe)),
            dualEdge_map_add, map_add_one_dualEdge_dualEdge hfe]
        rw [hEs] at hv
        obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff f).1 hfe
        · have hx := mem_Icc_two_iff.1 (hf _ (Sym2.mem_mk_left _ _))
          have hy := mem_Icc_two_iff.1 (hf _ (Sym2.mem_mk_right _ _))
          rw [dualEdge_horizontal, Sym2.map_mk, Sym2.mem_iff] at hv
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
          rw [mem_Icc_two_iff]
          rcases hv with rfl | rfl <;>
            simp only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
            omega
        · have hx := mem_Icc_two_iff.1 (hf _ (Sym2.mem_mk_left _ _))
          have hy := mem_Icc_two_iff.1 (hf _ (Sym2.mem_mk_right _ _))
          rw [dualEdge_vertical, Sym2.map_mk, Sym2.mem_iff] at hv
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
          rw [mem_Icc_two_iff]
          rcases hv with rfl | rfl <;>
            simp only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
            omega
      · rw [E.symm_apply_eq.2 (hE₂ f hfe).symm] at hv
        refine Icc_subset_Icc_right (fun i => ?_) (hf v hv)
        simp only [Pi.add_apply, Pi.one_apply]
        omega
    ext f
    simp only [mem_inter_iff, mem_ofPred_eq, hΦapp, Equiv.image_eq_preimage_symm, mem_preimage,
      mem_compl_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun h₃ => h₁ ?_, h₂⟩
      have := congrArg (E.symm f ∈ ·) h
      simp only [mem_inter_iff, mem_ofPred_eq, eq_iff_iff] at this
      exact (this.2 ⟨h₃, hpre f h₂⟩).1
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun h₃ => h₁ ?_, h₂⟩
      have := congrArg (E.symm f ∈ ·) h
      simp only [mem_inter_iff, mem_ofPred_eq, eq_iff_iff] at this
      exact (this.1 ⟨h₃, hpre f h₂⟩).1
  refine ⟨Φ, hΦ, hdet, fun q => ⟨fun f => unitInterval.symm (q (E.symm f)), ?_, fun L c h => ?_⟩⟩
  · have h1 := PercLib.Probability.prodBernoulli_map_compl q
    have h2 := PercLib.Probability.prodBernoulli_map_image_equiv
      (fun i => unitInterval.symm (q i)) E
    have hcomp : (Φ : Config (LatticeSite 2) → Config (LatticeSite 2)) =
        (fun ω => E '' ω) ∘ compl := rfl
    unfold law
    rw [hcomp, ← Measure.map_map (PercLib.Probability.measurable_image_equiv E)
      measurable_compl, h1, h2]
    rfl
  · have hmap : (law q).map Φ = law (fun f => unitInterval.symm (q (E.symm f))) := by
      have h1 := PercLib.Probability.prodBernoulli_map_compl q
      have h2 := PercLib.Probability.prodBernoulli_map_image_equiv
        (fun i => unitInterval.symm (q i)) E
      have hcomp : (Φ : Config (LatticeSite 2) → Config (LatticeSite 2)) =
          (fun ω => E '' ω) ∘ compl := rfl
      unfold law
      rw [hcomp, ← Measure.map_map (PercLib.Probability.measurable_image_equiv E)
        measurable_compl, h1, h2]
      rfl
    have hlaw : ∀ A, law (fun f => unitInterval.symm (q (E.symm f))) A = law q (Φ ⁻¹' A) := by
      intro A
      rw [← hmap, MeasurableEquiv.map_apply]
    have hsub : (fun v : LatticeSite 2 => v - 1) = (· + -1) := funext fun v => sub_eq_add_neg v 1
    refine ⟨h.pos, fun k i lo n hn hnL => ?_, fun k i lo n hn hnL => ?_⟩
    · rw [hlaw]
      have hset : ∀ B : LatticeSite 2, Φ ⁻¹' crossing i lo B = dualConfig ⁻¹' crossing i lo B := by
        intro B
        ext ω
        rw [mem_preimage, mem_preimage, ← inter_edgeSet_mem_crossing_iff, hΦ]
      rw [hset]
      exact h.le_law_dualConfig_crossing k i lo n hn hnL
    · rw [hlaw]
      have hset : ∀ B : LatticeSite 2, Φ ⁻¹' (dualConfig ⁻¹' crossing i lo B) =
          crossing i (lo + 1) (B + 1) := by
        intro B
        ext ω
        rw [mem_preimage, mem_preimage, ← dualConfig_inter_edgeSet, hΦ, dualConfig_dualConfig,
          hsub, ← inter_edgeSet_mem_crossing_iff i (lo + 1)]
        have := image_add_mem_crossing_iff (-1) i (lo + 1) (B + 1) (ω ∩ (zdGraph 2).edgeSet)
        rwa [add_neg_cancel_right, add_neg_cancel_right] at this
      rw [hset, add_right_comm]
      exact h.le_law_crossing k i (lo + 1) n hn hnL

/-! ### Lemma 15 read through a frame of the dual lattice -/

/-- The dual configuration consists of edges of `ℤ²`. -/
theorem dualConfig_inter_edgeSet_eq (X : Config (LatticeSite 2)) :
    dualConfig X ∩ (zdGraph 2).edgeSet = dualConfig X := by
  refine inter_eq_left.2 fun f hf => ?_
  obtain ⟨e, he, -, rfl⟩ := (mem_dualConfig_iff' X f).1 hf
  exact dualEdge_mem_edgeSet he

/-- **Lemma 15 read through a frame.** Let `Y` be a configuration whose edges are the image of
the dual configuration of `ω` under an automorphism `F false` of `ℤ²` and whose dual configuration
is the image of the open edges of `ω` under an automorphism `F true` (for instance `Y` the dual
configuration of `ω` itself, with `F false` the identity and `F true` the translation by
`(-1, -1)`). If `Y` has the separation property of `exists_law_separable_ge_strip` in the strip
`Icc lo hi`, then every finite family of walks of `ω`, open (`σ i = true`) or dual, whose images
are crossings of that strip in the sense of the event (open walks of `ω` are dual crossings of `Y`,
dual walks of `ω` are open crossings of `Y`), with walks of the same colour disjoint, can be
replaced by a family with the same colours and starting points whose images have the conclusions of
the event: they are crossings of the strip, disjoint in each colour, meeting the top row only at
their ends, with ends at least `4 √η N` apart and from the ends of the strip in doubled columns
(the dual crossings of `Y`, i.e. the open walks of `ω`, carry the half step), and with fences. The
boxes of the fences are written as preimages under the frame. -/
theorem separable_of_frame {η : ℝ} {N : ℕ} {lo hi : LatticeSite 2}
    (F : Bool → zdGraph 2 ≃g zdGraph 2) {ω Y : Config (LatticeSite 2)}
    (hY : Y ∩ (zdGraph 2).edgeSet = Sym2.map (F false) '' dualConfig ω)
    (hYd : dualConfig Y = Sym2.map (F true) '' (ω ∩ (zdGraph 2).edgeSet))
    (hE : Y ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lo 1 ∧ b i 1 = hi 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lo hi) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lo 1 - 1 ∧ b i 1 = hi 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
            ![hi 0 - 1, hi 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lo hi})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lo 1 ∧ b' i 1 = hi 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lo hi) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lo 1 - 1 ∧ b' i 1 = hi 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lo 0, lo 1 - 1] : LatticeSite 2)
              ![hi 0 - 1, hi 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lo hi})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hi 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lo 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hi 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hi 1]
              ![b' i 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    {ι : Type} [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i))
    (hcr : ∀ i, (∀ e ∈ (γ i).edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
      F (σ i) (a i) 1 = lo 1 - cond (σ i) 1 0 ∧ F (σ i) (b i) 1 = hi 1 ∧
      (∀ x ∈ (γ i).support, F (σ i) x ∈ Icc (![lo 0, lo 1 - cond (σ i) 1 0] : LatticeSite 2)
        ![hi 0 - cond (σ i) 1 0, hi 1]) ∧
      (σ i = true → ∀ e ∈ (γ i).edges, Sym2.map (F true) e ∈
        dualEdge '' {f | f ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ f, x ∈ Icc lo hi}))
    (hdisj : ∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) :
    ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, (∀ e ∈ (γ' i).edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧ F (σ i) (b' i) 1 = hi 1 ∧
        ∀ x ∈ (γ' i).support, F (σ i) x ∈ Icc (![lo 0, lo 1 - cond (σ i) 1 0] : LatticeSite 2)
          ![hi 0 - cond (σ i) 1 0, hi 1]) ∧
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
      (∀ i, ∀ x ∈ (γ' i).support.dropLast, F (σ i) x 1 ≠ hi 1) ∧
      (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
        |((2 * F (σ i) (b' i) 0 + cond (σ i) 1 0 : ℤ) : ℝ) -
          ((2 * F (σ k) (b' k) 0 + cond (σ k) 1 0 : ℤ) : ℝ)|) ∧
      (∀ i, 4 * Real.sqrt η * N ≤ ((2 * F (σ i) (b' i) 0 + cond (σ i) 1 0 - 2 * lo 0 : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ ((2 * hi 0 - (2 * F (σ i) (b' i) 0 + cond (σ i) 1 0) : ℤ) : ℝ)) ∧
      ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
        F (σ i) l 0 = F (σ i) (b' i) 0 - ⌊η * N⌋₊ ∧ F (σ i) r 0 = F (σ i) (b' i) 0 + ⌊η * N⌋₊ ∧
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          {v | F (σ i) v ∈ Icc ![F (σ i) (b' i) 0 - ⌊η * N⌋₊, hi 1]
            ![F (σ i) (b' i) 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊]} l r ∧
        cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          {v | F (σ i) v ∈ Icc (F (σ i) (b' i) - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
            (F (σ i) (b' i) + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))} x l := by
  have hcond_t : ∀ {c : Bool} {A B : Prop}, cond c A B → c = true → A := by
    rintro c A B h rfl
    exact h
  have hcond_f : ∀ {c : Bool} {A B : Prop}, cond c A B → c = false → B := by
    rintro c A B h rfl
    exact h
  have hcond_i : ∀ {c : Bool} {A B : Prop}, (c = true → A) → (c = false → B) → cond c A B := by
    intro c A B hA hB
    cases c
    · exact hB rfl
    · exact hA rfl
  have hss : ∀ (g : zdGraph 2 ≃g zdGraph 2) (e : Sym2 (LatticeSite 2)),
      Sym2.map g.symm (Sym2.map g e) = e := fun g e => by
    rw [Sym2.map_map, RelIso.symm_comp_self, Sym2.map_id, id]
  have hss' : ∀ (g : zdGraph 2 ≃g zdGraph 2) (e : Sym2 (LatticeSite 2)),
      Sym2.map g (Sym2.map g.symm e) = e := fun g e => by
    rw [Sym2.map_map, RelIso.self_comp_symm, Sym2.map_id, id]
  have hEmap : ∀ (g : zdGraph 2 ≃g zdGraph 2) (e : Sym2 (LatticeSite 2)),
      Sym2.map g e ∈ (zdGraph 2).edgeSet ↔ e ∈ (zdGraph 2).edgeSet := by
    intro g e
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      exact g.map_adj_iff
  -- the edges of the frame configuration and of its dual configuration
  have hYe : ∀ e ∈ (zdGraph 2).edgeSet, Sym2.map (F false) e ∈ Y ↔ e ∈ dualConfig ω := by
    intro e he
    have h₁ : Sym2.map (F false) e ∈ Y ↔ Sym2.map (F false) e ∈ Y ∩ (zdGraph 2).edgeSet :=
      ⟨fun h => ⟨h, (hEmap _ e).2 he⟩, fun h => h.1⟩
    rw [h₁, hY]
    exact ⟨fun ⟨e', he', hee'⟩ => by
      rw [← hss (F false) e, ← hee', hss]
      exact he', fun h => ⟨e, h, rfl⟩⟩
  have hYde : ∀ e ∈ (zdGraph 2).edgeSet, Sym2.map (F true) e ∈ dualConfig Y ↔ e ∈ ω := by
    intro e he
    rw [hYd]
    exact ⟨fun ⟨e', he', hee'⟩ => by
      rw [← hss (F true) e, ← hee', hss]
      exact he'.1, fun h => ⟨e, ⟨h, he⟩, rfl⟩⟩
  have hcfg : ∀ c : Bool, Sym2.map (F c) '' cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet =
      cond (!c) Y (dualConfig Y) ∩ (zdGraph 2).edgeSet := by
    intro c
    cases c
    · change Sym2.map (F false) '' dualConfig ω ∩ (zdGraph 2).edgeSet = Y ∩ (zdGraph 2).edgeSet
      rw [← image_sym2Map_inter_edgeSet, dualConfig_inter_edgeSet_eq, ← hY]
    · change Sym2.map (F true) '' ω ∩ (zdGraph 2).edgeSet = dualConfig Y ∩ (zdGraph 2).edgeSet
      rw [← image_sym2Map_inter_edgeSet, ← hYd, dualConfig_inter_edgeSet_eq]
  -- the images of the walks are crossings of the strip
  obtain ⟨b'f, γ'f, h1, h2, h3, h4, h5, h6⟩ := hE ι (fun i => !σ i) (fun i => F (σ i) (a i))
    (fun i => F (σ i) (b i)) (fun i => (γ i).map (F (σ i)).toHom) (fun i => by
      obtain ⟨hE', ha, hb, hS, hD⟩ := hcr i
      refine hcond_i (fun hσi => ?_) (fun hσi => ?_)
      · have hσ : σ i = false := by simpa using hσi
        have hc : cond (σ i) (1 : ℤ) 0 = 0 := by rw [hσ]; rfl
        have hG : cond (σ i) ω (dualConfig ω) = dualConfig ω := by rw [hσ]; rfl
        refine ⟨by rw [ha, hc, sub_zero], hb, fun x hx => ?_, fun e he => ?_⟩
        · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := mem_Icc_two_iff.1 (hS y hy)
          simp only [hc, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one] at this
          rw [mem_Icc_two_iff]
          exact this
        · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          have hF : F (σ i) = F false := by rw [hσ]
          change Sym2.map (F (σ i)) e₀ ∈ Y
          rw [hF]
          exact (hYe e₀ ((γ i).edges_subset_edgeSet he₀)).2 (hG ▸ hE' e₀ he₀)
      · have hσ : σ i = true := by simpa using hσi
        have hD' := hD hσ
        have hc : cond (σ i) (1 : ℤ) 0 = 1 := by rw [hσ]; rfl
        have hG : cond (σ i) ω (dualConfig ω) = ω := by rw [hσ]; rfl
        refine ⟨by rw [ha, hc], hb, fun x hx => ?_, fun e he => ?_⟩
        · rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hS y hy
          rw [hc] at this
          exact this
        · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          have hF : F (σ i) = F true := by rw [hσ]
          change Sym2.map (F (σ i)) e₀ ∈ _
          rw [hF]
          exact ⟨(hYde e₀ ((γ i).edges_subset_edgeSet he₀)).2 (hG ▸ hE' e₀ he₀), hD' e₀ he₀⟩)
    (fun i k hik hσ x hx hx' => by
      have hσ' : σ i = σ k := by simpa using hσ
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hx'
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hx'
      rw [← hσ'] at hyy'
      exact hdisj i k hik hσ' y hy ((F (σ i)).injective hyy' ▸ hy'))
  have hFb : ∀ i, F (σ i) ((F (σ i)).symm (b'f i)) = b'f i := fun i =>
    RelIso.apply_symm_apply _ _
  have hcol : ∀ c : Bool, (cond (!c) 0 1 : ℤ) = cond c 1 0 := by
    intro c
    cases c <;> rfl
  -- the facts of the new crossings, read in the frame
  have hU : ∀ i, b'f i 1 = hi 1 ∧ (∀ y ∈ (γ'f i).support,
      y ∈ Icc (![lo 0, lo 1 - cond (σ i) 1 0] : LatticeSite 2) ![hi 0 - cond (σ i) 1 0, hi 1]) ∧
      ∀ e ∈ (γ'f i).edges, Sym2.map (F (σ i)).symm e ∈ cond (σ i) ω (dualConfig ω) := by
    intro i
    rcases (σ i).eq_false_or_eq_true.symm with hσ | hσ
    · obtain ⟨-, hb, hS, hE'⟩ := hcond_t (h1 i) (by simp [hσ])
      have hc : cond (σ i) (1 : ℤ) 0 = 0 := by rw [hσ]; rfl
      have hG : cond (σ i) ω (dualConfig ω) = dualConfig ω := by rw [hσ]; rfl
      have hF : F (σ i) = F false := by rw [hσ]
      refine ⟨hb, fun y hy => ?_, fun e he => ?_⟩
      · have := mem_Icc_two_iff.1 (hS y hy)
        rw [mem_Icc_two_iff]
        simp only [hc, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
        exact this
      · have he' := (γ'f i).edges_subset_edgeSet he
        have := hE' e he
        rw [← hss' (F false) e] at this he'
        rw [hG, hF]
        exact (hYe _ ((hEmap _ _).1 he')).1 this
    · obtain ⟨-, hb, hS, hE'⟩ := hcond_f (h1 i) (by simp [hσ])
      have hc : cond (σ i) (1 : ℤ) 0 = 1 := by rw [hσ]; rfl
      have hG : cond (σ i) ω (dualConfig ω) = ω := by rw [hσ]; rfl
      have hF : F (σ i) = F true := by rw [hσ]
      refine ⟨hb, fun y hy => by rw [hc]; exact hS y hy, fun e he => ?_⟩
      have he' := (γ'f i).edges_subset_edgeSet he
      have := (hE' e he).1
      rw [← hss' (F true) e] at this he'
      rw [hG, hF]
      exact (hYde _ ((hEmap _ _).1 he')).1 this
  refine ⟨fun i => (F (σ i)).symm (b'f i),
    fun i => ((γ'f i).map (F (σ i)).symm.toHom).copy ((F (σ i)).symm_apply_apply (a i)) rfl,
    fun i => ⟨fun e he => ?_, ?_, fun x hx => ?_⟩, fun i k hik hσ x hx hx' => ?_,
    fun i x hx => ?_, fun i k hik => ?_, fun i => ?_, fun i => ?_⟩
  · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact (hU i).2.2 e₀ he₀
  · rw [hFb]
    exact (hU i).1
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change F (σ i) ((F (σ i)).symm y) ∈ _
    rw [RelIso.apply_symm_apply]
    exact (hU i).2.1 y hy
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hyy'⟩ := hx'
    rw [← hσ] at hyy'
    exact h2 i k hik (by simp [hσ]) y hy ((F (σ i)).symm.injective hyy' ▸ hy')
  · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, ← List.map_dropLast,
      List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change F (σ i) ((F (σ i)).symm y) 1 ≠ _
    rw [RelIso.apply_symm_apply]
    exact h3 i y hy
  · have := h4 i k hik
    simp only [hcol] at this
    rwa [hFb, hFb]
  · have := h5 i
    simp only [hcol] at this
    rwa [hFb]
  · obtain ⟨x, hx, l, r, hl, hr, hlr, hxl⟩ := h6 i
    rw [← hcfg] at hlr hxl
    refine ⟨(F (σ i)).symm x, ?_, (F (σ i)).symm l, (F (σ i)).symm r, ?_, ?_,
      inter_edgeSet_mem_localConn_of_image (F (σ i)) _ (fun v hv => ?_)
        (by rwa [RelIso.apply_symm_apply, RelIso.apply_symm_apply]),
      inter_edgeSet_mem_localConn_of_image (F (σ i)) _ (fun v hv => ?_)
        (by rwa [RelIso.apply_symm_apply, RelIso.apply_symm_apply])⟩
    · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem hx
    · rw [RelIso.apply_symm_apply, hFb, hl]
    · rw [RelIso.apply_symm_apply, hFb, hr]
    · simp only [Set.mem_ofPred_eq, RelIso.apply_symm_apply]
      exact hv
    · simp only [Set.mem_ofPred_eq, RelIso.apply_symm_apply]
      exact hv

end PercLib.Models.Planar
