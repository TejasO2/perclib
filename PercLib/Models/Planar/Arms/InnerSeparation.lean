/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, proof of Theorem 11 (separation at the internal
extremities of the arms).
-/
module

public import PercLib.Models.Planar.Arms.InnerGluing
public import PercLib.Models.Planar.Arms.InnerSeparationSides
public import PercLib.Models.Planar.Arms.MultiArmBounds
public import PercLib.Models.Planar.Arms.OuterSeparation

/-!
# The inner separation step

The arms of an annulus are rerouted near the inner box `B_ρ(z)` into a family separated at the
inner boundary. Each arm starts on one side of `B_ρ(z)`; its initial piece, up to its first visit
to the far row of a strip of depth `N` along that side, is a crossing of the strip, and Lemma 15 in
the dual lattice (`separable_of_frame`) reroutes these crossings towards new starts that are far
apart, far from the corners and carry inner fences. The new arms are the reversed new crossings
followed by the old arms; they have the old landing positions, so they are disjoint and in the old
order (`ArmsDisjoint.of_landingPos_eq`).

An initial piece is a crossing of the strip of its side as long as the arm does not come near a
corner of `B_ρ(z)`: turning a corner within the depth `N` of the strip passes within `N` of it. Arms
that come near a corner give a one-arm event from a small box at the corner, which is unlikely; this
is why the strips are long and thin (`exists_law_separable_ge_strip` of any width).

## Main results

* `IsArm.append_left`: replacing the start of an arm.
* `exists_append_eq_far`: the first visit of a walk to the far row of a frame.
* `ArmsDisjoint.of_landingPos_eq`: the barrier for new starts (colour sequences without packs).
* `exists_reroute_of_frame`: rerouting the initial pieces of the arms starting on one side, read
  through a frame of the dual lattice.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site

open scoped ENNReal

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}

/-! ### Replacing the start of an arm -/

/-- **Replacing the start of an arm.** If `q.append s` is an arm of colour `c`, so is `p'.append s`
for every walk `p'` of that colour to the same vertex (face) that starts in `B_r(z)` (the faces
touching it), avoids it afterwards and stays in the interior of the outer box (its faces). -/
theorem IsArm.append_left {c : Bool} {a a' x b : LatticeSite 2} {q : (zdGraph 2).Walk a x}
    {s : (zdGraph 2).Walk x b} {p' : (zdGraph 2).Walk a' x}
    (h : IsArm ω c z r lo hi (q.append s))
    (ha' : a' ∈ cond c (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)))
    (hS : ∀ w ∈ p'.support.tail, w ∉ cond c (Icc (z - r) (z + r)) (Icc (z - r - 1) (z + r)))
    (hT : ∀ w ∈ p'.support, w ∈ cond c (Icc (lo + 1) (hi - 1)) (Icc lo (hi - 1)))
    (hE : ∀ e ∈ p'.edges, e ∈ cond c ω (dualConfig ω)) : IsArm ω c z r lo hi (p'.append s) := by
  rw [isArm_iff_cond] at h ⊢
  obtain ⟨hc, he⟩ := h
  refine ⟨⟨ha', fun w hw => ?_, hc.end_notMem, fun w hw => ?_⟩, fun e he' => ?_⟩
  · rw [SimpleGraph.Walk.tail_support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hS w hw
    · exact hc.notMem_of_mem_tail w (by
        rw [SimpleGraph.Walk.tail_support_append]
        exact List.mem_append_right _ hw)
  · rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil s), List.mem_append] at hw
    rcases hw with hw | hw
    · exact hT w (List.dropLast_subset _ hw)
    · exact hc.mem_of_mem_dropLast w (by
        rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append,
          List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil s)]
        exact List.mem_append_right _ hw)
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he'
    rcases he' with he' | he'
    · exact hE e he'
    · exact he e (by
        rw [SimpleGraph.Walk.edges_append]
        exact List.mem_append_right _ he')

/-! ### The first visit to the far row of a frame -/

/-- **The first visit to the far row of a frame.** Let `F` be an automorphism of `ℤ²` (a frame),
and let a walk start on the row `hi₁` of the frame inside the columns `[lo₀, hi₀ - d]` and end
outside the points of the frame in these columns strictly above the row `lo₁ - d` and at most at
the row `hi₁`. If after its start the walk never visits the points of the frame in these columns on
the rows `hi₁` and `hi₁ + 1`, and never visits the points outside these columns on the rows
`[lo₁ - d, hi₁]`, then it splits, at its first visit to the row `lo₁ - d`, into a walk inside the
box `[lo₀, hi₀ - d] × [lo₁ - d, hi₁]` of the frame, meeting the row `lo₁ - d` only at its end and
the row `hi₁` only at its start, followed by the rest. -/
theorem exists_append_eq_far (F : zdGraph 2 ≃g zdGraph 2) {lo hi a b : LatticeSite 2} {d : ℤ}
    (hlh : lo 1 - d < hi 1) (γ : (zdGraph 2).Walk a b)
    (ha : F a 1 = hi 1) (ha0 : lo 0 ≤ F a 0 ∧ F a 0 ≤ hi 0 - d)
    (hb : ¬(lo 0 ≤ F b 0 ∧ F b 0 ≤ hi 0 - d ∧ lo 1 - d < F b 1 ∧ F b 1 ≤ hi 1))
    (hin : ∀ v ∈ γ.support.tail, lo 0 ≤ F v 0 → F v 0 ≤ hi 0 - d → hi 1 ≤ F v 1 →
      F v 1 ≤ hi 1 + 1 → False)
    (hcor : ∀ v ∈ γ.support, (F v 0 < lo 0 ∨ hi 0 - d < F v 0) → lo 1 - d ≤ F v 1 →
      F v 1 ≤ hi 1 → False) :
    ∃ x, ∃ (p : (zdGraph 2).Walk a x) (q : (zdGraph 2).Walk x b), p.append q = γ ∧
      F x 1 = lo 1 - d ∧
      (∀ v ∈ p.support, lo 0 ≤ F v 0 ∧ F v 0 ≤ hi 0 - d ∧ lo 1 - d ≤ F v 1 ∧ F v 1 ≤ hi 1) ∧
      (∀ v ∈ p.support.dropLast, lo 1 - d < F v 1) ∧ ∀ v ∈ p.support.tail, F v 1 < hi 1 := by
  obtain ⟨x, p, q, hpq, hx, hp⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := {v | lo 0 ≤ F v 0 ∧ F v 0 ≤ hi 0 - d ∧ lo 1 - d < F v 1 ∧ F v 1 ≤ hi 1}) γ hb
  have hpne : ¬p.Nil := fun hn => by
    have : a = x := hn.eq
    subst this
    exact hx ⟨ha0.1, ha0.2, by omega, ha.le⟩
  have hxγ : x ∈ γ.support := by
    rw [← hpq]
    exact (SimpleGraph.Walk.mem_support_append_iff p q).2 (Or.inl p.end_mem_support)
  have hxt : x ∈ γ.support.tail := by
    rw [← hpq, SimpleGraph.Walk.tail_support_append]
    exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_tail_support hpne)
  have hy := hp _ (SimpleGraph.Walk.penultimate_mem_dropLast_support hpne)
  have hadj := (zdGraph_two_adj_iff _ _).1 (F.map_adj_iff.2 (p.adj_penultimate hpne))
  simp only [mem_ofPred_eq] at hy hx
  have hc1 : ¬((F x 0 < lo 0 ∨ hi 0 - d < F x 0) ∧ lo 1 - d ≤ F x 1 ∧ F x 1 ≤ hi 1) :=
    fun ⟨h₁, h₂, h₃⟩ => hcor x hxγ h₁ h₂ h₃
  have hi1 : ¬(lo 0 ≤ F x 0 ∧ F x 0 ≤ hi 0 - d ∧ hi 1 ≤ F x 1 ∧ F x 1 ≤ hi 1 + 1) :=
    fun ⟨h₁, h₂, h₃, h₄⟩ => hin x hxt h₁ h₂ h₃ h₄
  have hx1 : F x 1 = lo 1 - d ∧ lo 0 ≤ F x 0 ∧ F x 0 ≤ hi 0 - d := by omega
  have hsupp : ∀ v ∈ p.support, v ∈ p.support.dropLast ∨ v = x := by
    intro v hv
    rw [← SimpleGraph.Walk.dropLast_support_concat p, List.mem_append,
      List.mem_singleton] at hv
    exact hv
  refine ⟨x, p, q, hpq, hx1.1, fun v hv => ?_, fun v hv => (hp v hv).2.2.1, fun v hv => ?_⟩
  · rcases hsupp v hv with hv | rfl
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := hp v hv
      exact ⟨h₁, h₂, h₃.le, h₄⟩
    · exact ⟨hx1.2.1, hx1.2.2, hx1.1.ge, by omega⟩
  · rcases hsupp v (List.mem_of_mem_tail hv) with hv' | rfl
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := hp v hv'
      have hvt : v ∈ γ.support.tail := by
        rw [← hpq, SimpleGraph.Walk.tail_support_append]
        exact List.mem_append_left _ hv
      by_contra hcon
      exact hin v hvt h₁ h₂ (by omega) (by omega)
    · omega

/-! ### The barrier for new starts -/

/-- **The barrier, for new starts.** Every family of arms with the colours and the landing
positions of a disjoint family of arms landing in counterclockwise order, for a colour sequence
without packs, is disjoint. (Two arms of one colour sharing a point would give an arm with the inner
position of one landing where the other lands; the sector lemma forbids it.) -/
theorem ArmsDisjoint.of_landingPos_eq {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)} (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
      (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l)))
    {a' b' : Fin j → LatticeSite 2} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (hγ' : ∀ i, IsArm ω (σ i) z r lo hi (γ' i))
    (hlan : ∀ i, landingPos lo hi (σ i) (γ' i) = landingPos lo hi (σ i) (γ i)) :
    ArmsDisjoint σ γ' := by
  rcases hσ with hj | hσ
  · exact armsDisjoint_of_subsingleton hj σ γ'
  -- an arm with the inner position of `γ' i'` does not land where `γ i` lands, for `i ≠ i'` of
  -- one colour
  have key : ∀ i i', i ≠ i' → σ i = σ i' → ∀ {x y : LatticeSite 2} (W : (zdGraph 2).Walk x y),
      IsArm ω (σ i) z r lo hi W → innerPos z r (σ i) W = innerPos z r (σ i) (γ' i') →
      landingPos lo hi (σ i) W ≠ landingPos lo hi (σ i) (γ i) := by
    intro i i' hii' hσii' x y W hW hWin heq
    set k := finRotate j i with hk_def
    set l := finRotate j i' with hl_def
    have hk : σ k ≠ σ i := (hσ i).symm
    have hl : σ l ≠ σ i := fun h => hσ i' (h.trans hσii').symm
    have hkl : k ≠ l := fun h => hii' ((finRotate j).injective h)
    have hσkl : σ k = σ l := by
      revert hk hl
      generalize σ k = x
      generalize σ l = y
      generalize σ i = w
      cases x <;> cases y <;> cases w <;> simp
    have hli : l ≠ i := fun h => hl (congrArg σ h)
    have hki' : k ≠ i' := fun h => hk ((congrArg σ h).trans hσii'.symm)
    have h₁ := sbtw_apply_finRotate_apply (f := fun i => landingPos lo hi (σ i) (γ i)) ho hli
      hkl.symm
    have h₂ := sbtw_apply_finRotate_apply (f := fun i => landingPos lo hi (σ i) (γ i)) ho hki' hkl
    have h₃ : ¬sbtw (landingPos lo hi (σ i') (γ i')) (landingPos lo hi (σ k) (γ k))
        (landingPos lo hi (σ l) (γ l)) := fun h => sbtw_asymm h (sbtw_cyclic_left h₂)
    have hγi' : IsArm ω (σ i) z r lo hi (γ' i') := hσii' ▸ hγ' i'
    have hW' := sbtw_landingPos_iff_of_innerPos_eq hB hγ hd hkl hσkl hk.symm hW hγi' hWin
    have hL : landingPos lo hi (σ i) (γ' i') = landingPos lo hi (σ i') (γ i') := by
      rw [hσii']
      exact hlan i'
    rw [heq, hL] at hW'
    exact h₃ (hW'.1 h₁)
  refine ⟨fun i i' hii' hσi hσi' v hv hv' => ?_, fun i i' hii' hσi hσi' v hv hv' => ?_⟩
  · -- open arms: join `γ' i'` up to `v` to `γ' i` from `v`
    have hσ' : σ i = σ i' := hσi.trans hσi'.symm
    have hvs := List.mem_of_mem_tail hv
    have hc : IsOpenArm ω z r lo hi (γ' i) := by
      have := hγ' i
      rw [hσi] at this
      exact this
    have hc' : IsOpenArm ω z r lo hi (γ' i') := by
      have := hγ' i'
      rw [hσi'] at this
      exact this
    have h₁ := hγ' i
    have h₂ := hγ' i'
    rw [← SimpleGraph.Walk.take_spec (γ' i) hvs] at h₁
    rw [← SimpleGraph.Walk.take_spec (γ' i') hv', ← hσ'] at h₂
    have hW := IsArm.append_of_append h₂ h₁
    have hq : ¬((γ' i').takeUntil v hv').Nil := fun hn =>
      hc.isCrossing.notMem_of_mem_tail v hv (hn.eq ▸ hc'.isCrossing.start_mem)
    refine key i i' hii' hσ' _ hW ?_ ?_
    · rw [innerPos_append _ hq]
      conv_rhs => rw [← SimpleGraph.Walk.take_spec (γ' i') hv', innerPos_append _ hq]
    · rw [← hlan i, hσi, landingPos_true, landingPos_true]
  · -- dual arms
    have hσ' : σ i = σ i' := hσi.trans hσi'.symm
    have hc : IsDualArm ω z r lo hi (γ' i) := by
      have := hγ' i
      rw [hσi] at this
      exact this
    have hc' : IsDualArm ω z r lo hi (γ' i') := by
      have := hγ' i'
      rw [hσi'] at this
      exact this
    by_cases hvb : v = b' i
    · -- both arms end at the face `v`, so they end with the same dual edge
      have hvb' : v = b' i' := hc'.isCrossing.eq_end_of_notMem hv'
        (by rw [hvb]; exact hc.isCrossing.end_notMem)
      have hpen := hc.penultimate_eq hc' ((hγ' i).not_nil hB) ((hγ' i').not_nil hB)
        (hvb.symm.trans hvb')
      refine key i i' hii' hσ' (γ' i') (hσ' ▸ hγ' i') rfl ?_
      rw [← hlan i, hσi, landingPos_false, landingPos_false, hpen]
      exact congrArg (fun t => perimeterPos (2 • lo) (2 • hi) ((γ' i').penultimate + t + 1))
        (hvb'.symm.trans hvb)
    · -- join `γ' i'` up to `v` to `γ' i` from `v`
      have h₁ := hγ' i
      have h₂ := hγ' i'
      rw [← SimpleGraph.Walk.take_spec (γ' i) hv] at h₁
      rw [← SimpleGraph.Walk.take_spec (γ' i') hv', ← hσ'] at h₂
      have hW := IsArm.append_of_append h₂ h₁
      have hs : ¬((γ' i).dropUntil v hv).Nil := fun hn => hvb hn.eq
      refine key i i' hii' hσ' _ hW ?_ ?_
      · rw [hσi, innerPos_false, innerPos_false]
      · rw [landingPos_append _ hs, ← hlan i]
        conv_rhs => rw [← SimpleGraph.Walk.take_spec (γ' i) hv, landingPos_append _ hs]

/-! ### Rerouting the initial pieces on one side -/

/-- **Rerouting the arms starting on one side, through a frame.** Let `Y` be a frame configuration
of the dual lattice (`separable_of_frame`) with the separation property in the strip `Icc lo hi`,
and let the frame `F` map the side of `B_ρ(z)` to the top row `hi₁` of the strip: points of the
frame in the strip's columns on the rows `hi₁`, `hi₁ + 1` lie in `B_ρ(z)` (the faces touching it),
the other points of the strip lie outside it and inside the interior of `B_R(z)`. Let `γ` be a
disjoint family of arms from `B_ρ(z)` to the boundary of `B_R(z)`, and `P` a set of arms starting
on the top row of the frame and never visiting the points outside the strip's columns on its rows.
Then each arm of `P` can be replaced by an arm with the same colour and landing position, starting
on the top row of the frame, whose doubled frame columns `D i` are at least `4 √η N` apart and from
the ends of the strip, and which carries a fence read through the frame. -/
theorem exists_reroute_of_frame {η : ℝ} {N ρ R : ℕ} {lo hi : LatticeSite 2}
    (F : Bool → zdGraph 2 ≃g zdGraph 2) {Y : Config (LatticeSite 2)}
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
    (hlh : lo 1 + 1 ≤ hi 1)
    (hGB : ∀ (c : Bool) (v : LatticeSite 2), lo 0 ≤ F c v 0 → F c v 0 ≤ hi 0 - cond c 1 0 →
      hi 1 ≤ F c v 1 → F c v 1 ≤ hi 1 + 1 →
      v ∈ cond c (Icc (z - ρ) (z + ρ)) (Icc (z - ρ - 1) (z + ρ)))
    (hGD : ∀ (c : Bool) (v : LatticeSite 2), lo 0 ≤ F c v 0 → F c v 0 ≤ hi 0 - cond c 1 0 →
      lo 1 - cond c 1 0 ≤ F c v 1 → F c v 1 < hi 1 →
      v ∉ cond c (Icc (z - ρ) (z + ρ)) (Icc (z - ρ - 1) (z + ρ)) ∧
        v ∈ cond c (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)))
    (hGF : ∀ (c : Bool) (v : LatticeSite 2),
      v ∈ cond c (Icc (z - ρ) (z + ρ)) (Icc (z - ρ - 1) (z + ρ)) →
        v ∈ cond c (Icc (z - R + 1) (z + R - 1)) (Icc (z - R) (z + R - 1)))
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z ρ (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (P : Fin j → Prop)
    (hP : ∀ i, P i → F (σ i) (a i) 1 = hi 1 ∧ lo 0 ≤ F (σ i) (a i) 0 ∧
      F (σ i) (a i) 0 ≤ hi 0 - cond (σ i) 1 0)
    (hcor : ∀ i, P i → ∀ v ∈ (γ i).support,
      (F (σ i) v 0 < lo 0 ∨ hi 0 - cond (σ i) 1 0 < F (σ i) v 0) →
      lo 1 - cond (σ i) 1 0 ≤ F (σ i) v 1 → F (σ i) v 1 ≤ hi 1 → False) :
    ∃ D : Fin j → ℤ,
      (∀ i, P i → ∃ (a' : LatticeSite 2) (Γ : (zdGraph 2).Walk a' (b i)),
        IsArm ω (σ i) z ρ (z - R) (z + R) Γ ∧
        landingPos (z - R) (z + R) (σ i) Γ = landingPos (z - R) (z + R) (σ i) (γ i) ∧
        F (σ i) a' 1 = hi 1 ∧ lo 0 ≤ F (σ i) a' 0 ∧ F (σ i) a' 0 ≤ hi 0 - cond (σ i) 1 0 ∧
        2 * F (σ i) a' 0 + cond (σ i) 1 0 = D i ∧
        ∃ x ∈ Γ.support, ∃ l r : LatticeSite 2,
          F (σ i) l 0 = F (σ i) a' 0 - ⌊η * N⌋₊ ∧ F (σ i) r 0 = F (σ i) a' 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            {v | F (σ i) v ∈ Icc ![F (σ i) a' 0 - ⌊η * N⌋₊, hi 1]
              ![F (σ i) a' 0 + ⌊η * N⌋₊, hi 1 + ⌊Real.sqrt η * N⌋₊]} l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            {v | F (σ i) v ∈ Icc (F (σ i) a' - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (F (σ i) a' + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))} x l) ∧
      (∀ i k, P i → P k → i ≠ k → 4 * Real.sqrt η * N ≤ |((D i - D k : ℤ) : ℝ)|) ∧
      (∀ i, P i → 4 * Real.sqrt η * N ≤ ((D i - 2 * lo 0 : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ ((2 * hi 0 - D i : ℤ) : ℝ)) := by
  classical
  have hd01 : ∀ c : Bool, 0 ≤ cond c (1 : ℤ) 0 ∧ cond c (1 : ℤ) 0 ≤ 1 := fun c => by
    cases c <;> simp
  -- the first visit of each arm of `P` to the far row
  have hcut : ∀ i, P i → ∃ x, ∃ (p : (zdGraph 2).Walk (a i) x) (q : (zdGraph 2).Walk x (b i)),
      p.append q = γ i ∧ F (σ i) x 1 = lo 1 - cond (σ i) 1 0 ∧
      (∀ v ∈ p.support, lo 0 ≤ F (σ i) v 0 ∧ F (σ i) v 0 ≤ hi 0 - cond (σ i) 1 0 ∧
        lo 1 - cond (σ i) 1 0 ≤ F (σ i) v 1 ∧ F (σ i) v 1 ≤ hi 1) ∧
      (∀ v ∈ p.support.dropLast, lo 1 - cond (σ i) 1 0 < F (σ i) v 1) ∧
      ∀ v ∈ p.support.tail, F (σ i) v 1 < hi 1 := by
    intro i hi'
    obtain ⟨hc, -⟩ := isArm_iff_cond.1 (hγ i)
    have h01 := hd01 (σ i)
    obtain ⟨ha1, ha0, ha0'⟩ := hP i hi'
    refine exists_append_eq_far (F (σ i)) (by omega) (γ i) ha1 ⟨ha0, ha0'⟩ (fun h => ?_)
      (fun v hv h₁ h₂ h₃ h₄ => hc.notMem_of_mem_tail v hv (hGB _ _ h₁ h₂ h₃ h₄))
      (fun v hv => hcor i hi' v hv)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    rcases lt_or_eq_of_le h₄ with h₄ | h₄
    · exact hc.end_notMem (hGD _ _ h₁ h₂ h₃.le h₄).2
    · exact hc.end_notMem (hGF _ _ (hGB _ _ h₁ h₂ h₄.ge (by omega)))
  choose x p q hpq hx hbox hdl htl using hcut
  have hpe : ∀ i hi', ∀ e ∈ (p i hi').edges, e ∈ (γ i).edges := fun i hi' e he => by
    rw [← hpq i hi', SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ he
  have hps : ∀ i hi', ∀ v ∈ (p i hi').support, v ∈ (γ i).support := fun i hi' v hv => by
    rw [← hpq i hi']
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inl hv)
  have hpt : ∀ i hi', ∀ v ∈ (p i hi').support.tail, v ∈ (γ i).support.tail := fun i hi' v hv => by
    rw [← hpq i hi', SimpleGraph.Walk.tail_support_append]
    exact List.mem_append_left _ hv
  have hpne : ∀ i hi', ¬(p i hi').Nil := fun i hi' hn => by
    have := hn.eq
    have h1 := (hP i hi').1
    have h2 := hx i hi'
    have h01 := hd01 (σ i)
    rw [← this] at h2
    omega
  have hqne : ∀ i hi', ¬(q i hi').Nil := fun i hi' hn => by
    obtain ⟨hc, -⟩ := isArm_iff_cond.1 (hγ i)
    have hxb := hn.eq
    have h01 := hd01 (σ i)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hbox i hi' _ (p i hi').end_mem_support
    have hin := (hGD _ _ h₁ h₂ h₃ (by rw [hx i hi']; omega)).2
    rw [hxb] at hin
    exact hc.end_notMem hin
  -- a vertex of a walk other than its end lies before its end; other than its start, after it
  have hdrop : ∀ {u v w : LatticeSite 2} (s : (zdGraph 2).Walk u v), w ∈ s.support → w ≠ v →
      w ∈ s.support.dropLast := fun s hw hne => by
    rw [← SimpleGraph.Walk.dropLast_support_concat s, List.mem_append, List.mem_singleton] at hw
    exact hw.resolve_right hne
  have htail : ∀ {u v w : LatticeSite 2} (s : (zdGraph 2).Walk u v), w ∈ s.support → w ≠ u →
      w ∈ s.support.tail := fun s hw hne =>
    ((SimpleGraph.Walk.mem_support_iff s).1 hw).resolve_left hne
  -- the reversed initial pieces are crossings of the strip in the frame
  obtain ⟨b'', γ'', H1, H2, H3, H4, H5, H6⟩ := separable_of_frame (η := η) (N := N) F hY hYd hE
    (ι := {i // P i}) (fun i => σ i.1) (fun i => x i.1 i.2) (fun i => a i.1)
    (fun i => (p i.1 i.2).reverse) (fun i => by
      obtain ⟨-, hE'⟩ := isArm_iff_cond.1 (hγ i.1)
      have h01 := hd01 (σ i.1)
      refine ⟨fun e he => hE' e (hpe i.1 i.2 e ?_), hx i.1 i.2, (hP i.1 i.2).1, fun v hv => ?_,
        fun hσi e he => ?_⟩
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
        exact he
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
        obtain ⟨h₁, h₂, h₃, h₄⟩ := hbox i.1 i.2 v hv
        rw [mem_Icc_two_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
      · have he' : Sym2.map (F true) e ∈ ((p i.1 i.2).reverse.map (F true).toHom).edges := by
          rw [SimpleGraph.Walk.edges_map]
          exact List.mem_map_of_mem he
        refine mem_image_dualEdge_of_forall_mem_edges _ (fun u v huv k => ?_) he'
        rw [SimpleGraph.Walk.edges_map, List.mem_map] at huv
        obtain ⟨e₀, he₀, hee⟩ := huv
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he₀
        induction e₀ using Sym2.ind with
        | h u₀ v₀ =>
          have hu₀ := (p i.1 i.2).fst_mem_support_of_mem_edges he₀
          have hv₀ := (p i.1 i.2).snd_mem_support_of_mem_edges he₀
          have hne : u₀ ≠ v₀ := ((p i.1 i.2).adj_of_mem_edges he₀).ne
          have hσ1 : σ i.1 = true := hσi
          have bu := hbox i.1 i.2 u₀ hu₀
          have bv := hbox i.1 i.2 v₀ hv₀
          rw [hσ1] at bu bv
          simp only [Bool.cond_true] at bu bv
          -- one end is before the far vertex, one is after the start
          have hfar : lo 1 - 1 < F true u₀ 1 ∨ lo 1 - 1 < F true v₀ 1 := by
            by_cases hu : u₀ = x i.1 i.2
            · have := hdl i.1 i.2 v₀ (hdrop _ hv₀ (fun h => hne (hu.trans h.symm)))
              rw [hσ1] at this
              simp only [Bool.cond_true] at this
              exact Or.inr this
            · have := hdl i.1 i.2 u₀ (hdrop _ hu₀ hu)
              rw [hσ1] at this
              simp only [Bool.cond_true] at this
              exact Or.inl this
          have hnear : F true u₀ 1 < hi 1 ∨ F true v₀ 1 < hi 1 := by
            by_cases hu : u₀ = a i.1
            · have := htl i.1 i.2 v₀ (htail _ hv₀ (fun h => hne (hu.trans h.symm)))
              rw [hσ1] at this
              exact Or.inr this
            · have := htl i.1 i.2 u₀ (htail _ hu₀ hu)
              rw [hσ1] at this
              exact Or.inl this
          have e1 : ∀ v, (F true).toHom v = F true v := fun v => rfl
          rw [Sym2.map_mk, Sym2.eq_iff, e1, e1] at hee
          rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases k <;>
            simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] <;> omega)
    (fun i k hik hσ w hw hw' => by
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw hw'
      have hik' : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      have hwi := hps i.1 i.2 w hw
      have hwk := hps k.1 k.2 w hw'
      cases hσi : σ i.1
      · exact hd.2 i.1 k.1 hik' hσi (hσ.symm.trans hσi) w hwi hwk
      · have hσk : σ k.1 = true := hσ.symm.trans hσi
        by_cases hwa : w = a i.1
        · by_cases hwa' : w = a k.1
          · -- two open arms with the same start leave it by the same step
            have hs : ∀ (m : {i // P i}), σ m.1 = true →
                F true (p m.1 m.2).snd 0 = F true (a m.1) 0 ∧
                  F true (p m.1 m.2).snd 1 = hi 1 - 1 := by
              intro m hσm
              have hsnd := htl m.1 m.2 _ (SimpleGraph.Walk.snd_mem_tail_support (hpne m.1 m.2))
              have hadj := (zdGraph_two_adj_iff _ _).1
                ((F true).map_adj_iff.2 ((p m.1 m.2).adj_snd (hpne m.1 m.2)))
              have ha1 := (hP m.1 m.2).1
              rw [hσm] at hsnd ha1
              omega
            obtain ⟨hi0, hi1⟩ := hs i hσi
            obtain ⟨hk0, hk1⟩ := hs k hσk
            have hak : F true (a i.1) 0 = F true (a k.1) 0 := by rw [← hwa, ← hwa']
            have heq : (p i.1 i.2).snd = (p k.1 k.2).snd := (F true).injective (by
              funext m
              fin_cases m <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] <;> omega)
            exact hd.1 i.1 k.1 hik' hσi hσk _
              (hpt i.1 i.2 _ (SimpleGraph.Walk.snd_mem_tail_support (hpne i.1 i.2)))
              (heq ▸ hps k.1 k.2 _ (List.mem_of_mem_tail
                (SimpleGraph.Walk.snd_mem_tail_support (hpne k.1 k.2))))
          · exact hd.1 k.1 i.1 hik'.symm hσk hσi w (htail _ hwk hwa') hwi
        · exact hd.1 i.1 k.1 hik' hσi hσk w (htail _ hwi hwa) hwk)
  -- the new arms: the reversed new crossings followed by the old arms
  refine ⟨fun i => if h : P i then 2 * F (σ i) (b'' ⟨i, h⟩) 0 + cond (σ i) 1 0 else 0,
    fun i hi' => ?_, fun i k hi' hk' hik => ?_, fun i hi' => ?_⟩
  · obtain ⟨hE'', hb1, hS''⟩ := H1 ⟨i, hi'⟩
    have h01 := hd01 (σ i)
    have hpt'' : ∀ w ∈ (γ'' ⟨i, hi'⟩).support, lo 0 ≤ F (σ i) w 0 ∧
        F (σ i) w 0 ≤ hi 0 - cond (σ i) 1 0 ∧ lo 1 - cond (σ i) 1 0 ≤ F (σ i) w 1 ∧
        F (σ i) w 1 ≤ hi 1 := fun w hw => by
      have := mem_Icc_two_iff.1 (hS'' w hw)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
    have hend := hpt'' _ (γ'' ⟨i, hi'⟩).end_mem_support
    have hzone := hGB _ _ hend.1 hend.2.1 hb1.ge (by omega)
    have hArm : IsArm ω (σ i) z ρ (z - R) (z + R)
        ((γ'' ⟨i, hi'⟩).reverse.append (q i hi')) := by
      have h0 := hγ i
      rw [← hpq i hi'] at h0
      refine h0.append_left hzone (fun w hw => ?_) (fun w hw => ?_) (fun e he => ?_)
      · rw [SimpleGraph.Walk.support_reverse, List.tail_reverse, List.mem_reverse] at hw
        have h₃ := H3 ⟨i, hi'⟩ w hw
        have hb := hpt'' w (List.dropLast_subset _ hw)
        exact (hGD _ _ hb.1 hb.2.1 hb.2.2.1 (lt_of_le_of_ne hb.2.2.2 h₃)).1
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
        have hb := hpt'' w hw
        rcases lt_or_eq_of_le hb.2.2.2 with h₄ | h₄
        · exact (hGD _ _ hb.1 hb.2.1 hb.2.2.1 h₄).2
        · exact hGF _ _ (hGB _ _ hb.1 hb.2.1 h₄.ge (by omega))
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
        exact hE'' e he
    obtain ⟨y, hy, l, r, hl, hr, hlr, hyl⟩ := H6 ⟨i, hi'⟩
    refine ⟨b'' ⟨i, hi'⟩, (γ'' ⟨i, hi'⟩).reverse.append (q i hi'), hArm, ?_, hb1, hend.1,
      hend.2.1, by simp [hi'], y, ?_, l, r, hl, hr, hlr, hyl⟩
    · rw [landingPos_append _ (hqne i hi')]
      conv_rhs => rw [← hpq i hi', landingPos_append _ (hqne i hi')]
    · refine (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inl ?_)
      rw [SimpleGraph.Walk.support_reverse]
      exact List.mem_reverse.2 hy
  · have := H4 ⟨i, hi'⟩ ⟨k, hk'⟩ (fun h => hik (congrArg Subtype.val h))
    simp only [hi', hk', dite_true]
    push_cast at this ⊢
    exact this
  · have := H5 ⟨i, hi'⟩
    simp only [hi', dite_true]
    exact this

end PercLib.Models.Planar
