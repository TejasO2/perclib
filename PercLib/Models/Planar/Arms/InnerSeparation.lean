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
* `exists_reroute_inner_bottom`, `_right`, `_top`, `_left`: the four sides, with inner positions
  and inner fences.
* `frame_relations`, `law_frame_apply`, `exists_frame_bottom`, `_top`, `_left`, `_right`: the four
  frames of the dual lattice and their laws.
* `mem_multiArmEvent_one_of_walk`: an arm passing near a corner gives a one-arm event there.
* `mem_innerSeparatedArmEvent_of_frames`: the deterministic part of the inner step.
* `exists_inner_separating_event`: **the inner separation step** (event form: an event of
  probability at least `1 - δ`, determined by `B_{2ρ}(z)`, on which the arms of `B_ρ(z)` can be
  separated at the inner boundary).
* `exists_law_multiArmEvent_diff_innerSeparated_le`: **the inner separation step**, probability
  form: `P(A(ρ, R) \ inner-separated) ≤ δ P(A(2ρ + 1, R))`.
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
the rows `hi₁` and `hi₁ + 1`, and never visits the two columns next to these columns on the rows
`(lo₁ - d, hi₁]`, then it splits, at its first visit to the row `lo₁ - d`, into a walk inside the
box `[lo₀, hi₀ - d] × [lo₁ - d, hi₁]` of the frame, meeting the row `lo₁ - d` only at its end and
the row `hi₁` only at its start, followed by the rest. -/
theorem exists_append_eq_far (F : zdGraph 2 ≃g zdGraph 2) {lo hi a b : LatticeSite 2} {d : ℤ}
    (hlh : lo 1 - d < hi 1) (γ : (zdGraph 2).Walk a b)
    (ha : F a 1 = hi 1) (ha0 : lo 0 ≤ F a 0 ∧ F a 0 ≤ hi 0 - d)
    (hb : ¬(lo 0 ≤ F b 0 ∧ F b 0 ≤ hi 0 - d ∧ lo 1 - d < F b 1 ∧ F b 1 ≤ hi 1))
    (hin : ∀ v ∈ γ.support.tail, lo 0 ≤ F v 0 → F v 0 ≤ hi 0 - d → hi 1 ≤ F v 1 →
      F v 1 ≤ hi 1 + 1 → False)
    (hcor : ∀ v ∈ γ.support, (F v 0 = lo 0 - 1 ∨ F v 0 = hi 0 - d + 1) → lo 1 - d < F v 1 →
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
  have hc1 : ¬((F x 0 = lo 0 - 1 ∨ F x 0 = hi 0 - d + 1) ∧ lo 1 - d < F x 1 ∧ F x 1 ≤ hi 1) :=
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
on the top row of the frame and never visiting the two columns next to the strip on its rows.
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
      (F (σ i) v 0 = lo 0 - 1 ∨ F (σ i) v 0 = hi 0 - cond (σ i) 1 0 + 1) →
      lo 1 - cond (σ i) 1 0 < F (σ i) v 1 → F (σ i) v 1 ≤ hi 1 → False) :
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

/-! ### The four sides -/

/-- **Rerouting the arms starting on the bottom side of `B_ρ(z)`.** Let `F` be the frame of the
bottom side (its coordinates are given by `hF0`, `hF1`) and let the frame configuration `Y` have the
separation property in the strip of depth `N` along the bottom side. Let `γ` be a disjoint family of
arms from `B_ρ(z)` to the boundary of `B_R(z)` none of which comes within `N` of a corner of
`B_ρ(z)` (the faces of a dual arm touching that box). Then each arm starting on the bottom side can
be replaced by an arm with the same colour and landing position, with inner positions `P i` at least
`4 √η N` apart and at least `4 √η N` inside the bottom side (`[m (4ρ + 2), (m + 1)(4ρ + 2)]` with `m
= 0`), carrying an inner fence of depth `⌊√η N⌋` and half-length `⌊η N⌋`. -/
theorem exists_reroute_inner_bottom {η : ℝ} {N ρ R : ℕ} (hN : 1 ≤ N) (hρ : 1 ≤ ρ)
    (hρR : ρ + N + 2 ≤ R) (hsN : 1 ≤ Real.sqrt η * N)
    (F : Bool → zdGraph 2 ≃g zdGraph 2)
    (hF0 : ∀ (c : Bool) (v : LatticeSite 2), F c v 0 = v 0 - cond c 1 0)
    (hF1 : ∀ (c : Bool) (v : LatticeSite 2), F c v 1 = v 1 - cond c 1 0) {lo hi : LatticeSite 2}
    (hlo : lo = ![z 0 - ρ - 1, z 1 - ρ - 1 - N]) (hhi : hi = ![z 0 + ρ, z 1 - ρ - 1])
    {Y : Config (LatticeSite 2)}
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
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z ρ (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hcor : ∀ i, ∀ v ∈ (γ i).support, ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ¬(κ 0 - N - cond (σ i) 0 1 ≤ v 0 ∧ v 0 ≤ κ 0 + N ∧
        κ 1 - N - cond (σ i) 0 1 ≤ v 1 ∧ v 1 ≤ κ 1 + N)) :
    ∃ P : Fin j → ℤ,
      (∀ i, a i 1 = z 1 - ρ - cond (σ i) 0 1 →
        ∃ (a' : LatticeSite 2) (Γ : (zdGraph 2).Walk a' (b i)),
        IsArm ω (σ i) z ρ (z - R) (z + R) Γ ∧
        landingPos (z - R) (z + R) (σ i) Γ = landingPos (z - R) (z + R) (σ i) (γ i) ∧
        innerPos z ρ (σ i) Γ = P i ∧
        HasInnerFence ω (σ i) z ρ ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ) ∧
      (∀ i k, a i 1 = z 1 - ρ - cond (σ i) 0 1 →
        a k 1 = z 1 - ρ - cond (σ k) 0 1 → i ≠ k →
        4 * Real.sqrt η * N ≤ |((P i - P k : ℤ) : ℝ)|) ∧
      (∀ i, a i 1 = z 1 - ρ - cond (σ i) 0 1 →
        4 * Real.sqrt η * N ≤ ((P i - 0 * (4 * ρ + 2) : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ (((0 + 1) * (4 * ρ + 2) - P i : ℤ) : ℝ)) := by
  classical
  subst hlo hhi
  have hd01 : ∀ c : Bool, 0 ≤ cond c (1 : ℤ) 0 ∧ cond c (1 : ℤ) 0 ≤ 1 ∧
      cond c (0 : ℤ) 1 = 1 - cond c (1 : ℤ) 0 := fun c => by
    cases c <;> simp
  have hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆
      Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    omega
  obtain ⟨D, hD1, hD2, hD3⟩ := exists_reroute_of_frame (η := η) (N := N) (ρ := ρ) (R := R)
    F hY hYd hE (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h => by
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h ⊢ <;> omega)
    hγ hd (fun i => a i 1 = z 1 - ρ - cond (σ i) 0 1) (fun i hi' => by
      obtain ⟨⟨h₁, h₂, h₃, h₄⟩, -⟩ := (hγ i).innerPos_cases hB
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcr := hcor i (a i) (γ i).start_mem_support
      by_contra hcon
      omega)
    (fun i hi' v hv h₁ h₂ h₃ => by
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃
      have hcr := hcor i v hv
      rcases h₁ with h₁ | h₁
      · exact hcr ![z 0 - ρ, z 1 - ρ] (Or.inl rfl) (Or.inl rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      · exact hcr ![z 0 + ρ, z 1 - ρ] (Or.inr rfl) (Or.inl rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega))
  refine ⟨fun i => D i - 2 * z 0 + 2 * ρ + 2, fun i hi' => ?_, fun i k hi' hk' hik => ?_,
    fun i hi' => ?_⟩
  · obtain ⟨a', Γ, hΓ, hland, ha1, ha0, ha0', hDi, x, hx, l, r, hl, hr, hlr, hxl⟩ := hD1 i hi'
    obtain ⟨c1, c2⟩ := hD3 i hi'
    obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
    have hs4 : (4 : ℝ) ≤ 4 * Real.sqrt η * N := by linarith
    have hc1 := hs4.trans c1
    have hc2 := hs4.trans c2
    norm_cast at hc1 hc2
    simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at ha1 ha0 ha0' hc1 hc2
    simp only [hF0] at hDi hl hr
    refine ⟨a', Γ, hΓ, hland, ?_, x, hx, l, r, localConn_mono_set (fun v hv => ?_) _ _ hxl,
      Or.inr (Or.inr (Or.inl ⟨?_, by omega, by omega,
        localConn_mono_set (fun v hv => ?_) _ _ hlr⟩))⟩
    · obtain ⟨-, hcases⟩ := hΓ.innerPos_cases hB
      beta_reduce
      rcases hcases with ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ <;> omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        hF0, hF1] at hv ⊢
      omega
    · omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one, hF0,
        hF1] at hv ⊢
      omega
  · have := hD2 i k hi' hk' hik
    have hPP : (D i - 2 * z 0 + 2 * ρ + 2) - (D k - 2 * z 0 + 2 * ρ + 2) = (D i - D k) := by ring
    rw [hPP]
    push_cast at this ⊢
    exact this
  · obtain ⟨c1, c2⟩ := hD3 i hi'
    simp only [Matrix.cons_val_zero] at c1 c2
    constructor
    · convert c1 using 2
      push_cast
      ring
    · convert c2 using 2
      push_cast
      ring

/-- **Rerouting the arms starting on the right side of `B_ρ(z)`.** Let `F` be the frame of the right
side (its coordinates are given by `hF0`, `hF1`) and let the frame configuration `Y` have the
separation property in the strip of depth `N` along the right side. Let `γ` be a disjoint family of
arms from `B_ρ(z)` to the boundary of `B_R(z)` none of which comes within `N` of a corner of
`B_ρ(z)` (the faces of a dual arm touching that box). Then each arm starting on the right side can
be replaced by an arm with the same colour and landing position, with inner positions `P i` at least
`4 √η N` apart and at least `4 √η N` inside the right side (`[m (4ρ + 2), (m + 1)(4ρ + 2)]` with `m
= 1`), carrying an inner fence of depth `⌊√η N⌋` and half-length `⌊η N⌋`. -/
theorem exists_reroute_inner_right {η : ℝ} {N ρ R : ℕ} (hN : 1 ≤ N) (hρ : 1 ≤ ρ)
    (hρR : ρ + N + 2 ≤ R) (hsN : 1 ≤ Real.sqrt η * N)
    (F : Bool → zdGraph 2 ≃g zdGraph 2)
    (hF0 : ∀ (c : Bool) (v : LatticeSite 2), F c v 0 = v 1 - cond c 1 0)
    (hF1 : ∀ (c : Bool) (v : LatticeSite 2), F c v 1 = -v 0) {lo hi : LatticeSite 2}
    (hlo : lo = ![z 1 - ρ - 1, -z 0 - ρ - N]) (hhi : hi = ![z 1 + ρ, -z 0 - ρ])
    {Y : Config (LatticeSite 2)}
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
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z ρ (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hcor : ∀ i, ∀ v ∈ (γ i).support, ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ¬(κ 0 - N - cond (σ i) 0 1 ≤ v 0 ∧ v 0 ≤ κ 0 + N ∧
        κ 1 - N - cond (σ i) 0 1 ≤ v 1 ∧ v 1 ≤ κ 1 + N)) :
    ∃ P : Fin j → ℤ,
      (∀ i, a i 0 = z 0 + ρ →
        ∃ (a' : LatticeSite 2) (Γ : (zdGraph 2).Walk a' (b i)),
        IsArm ω (σ i) z ρ (z - R) (z + R) Γ ∧
        landingPos (z - R) (z + R) (σ i) Γ = landingPos (z - R) (z + R) (σ i) (γ i) ∧
        innerPos z ρ (σ i) Γ = P i ∧
        HasInnerFence ω (σ i) z ρ ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ) ∧
      (∀ i k, a i 0 = z 0 + ρ →
        a k 0 = z 0 + ρ → i ≠ k →
        4 * Real.sqrt η * N ≤ |((P i - P k : ℤ) : ℝ)|) ∧
      (∀ i, a i 0 = z 0 + ρ →
        4 * Real.sqrt η * N ≤ ((P i - 1 * (4 * ρ + 2) : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ (((1 + 1) * (4 * ρ + 2) - P i : ℤ) : ℝ)) := by
  classical
  subst hlo hhi
  have hd01 : ∀ c : Bool, 0 ≤ cond c (1 : ℤ) 0 ∧ cond c (1 : ℤ) 0 ≤ 1 ∧
      cond c (0 : ℤ) 1 = 1 - cond c (1 : ℤ) 0 := fun c => by
    cases c <;> simp
  have hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆
      Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    omega
  obtain ⟨D, hD1, hD2, hD3⟩ := exists_reroute_of_frame (η := η) (N := N) (ρ := ρ) (R := R)
    F hY hYd hE (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h => by
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h ⊢ <;> omega)
    hγ hd (fun i => a i 0 = z 0 + ρ) (fun i hi' => by
      obtain ⟨⟨h₁, h₂, h₃, h₄⟩, -⟩ := (hγ i).innerPos_cases hB
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcr := hcor i (a i) (γ i).start_mem_support
      by_contra hcon
      omega)
    (fun i hi' v hv h₁ h₂ h₃ => by
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃
      have hcr := hcor i v hv
      rcases h₁ with h₁ | h₁
      · exact hcr ![z 0 + ρ, z 1 - ρ] (Or.inr rfl) (Or.inl rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      · exact hcr ![z 0 + ρ, z 1 + ρ] (Or.inr rfl) (Or.inr rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega))
  refine ⟨fun i => 6 * ρ + 4 + D i - 2 * z 1, fun i hi' => ?_, fun i k hi' hk' hik => ?_,
    fun i hi' => ?_⟩
  · obtain ⟨a', Γ, hΓ, hland, ha1, ha0, ha0', hDi, x, hx, l, r, hl, hr, hlr, hxl⟩ := hD1 i hi'
    obtain ⟨c1, c2⟩ := hD3 i hi'
    obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
    have hs4 : (4 : ℝ) ≤ 4 * Real.sqrt η * N := by linarith
    have hc1 := hs4.trans c1
    have hc2 := hs4.trans c2
    norm_cast at hc1 hc2
    simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at ha1 ha0 ha0' hc1 hc2
    simp only [hF0] at hDi hl hr
    refine ⟨a', Γ, hΓ, hland, ?_, x, hx, l, r, localConn_mono_set (fun v hv => ?_) _ _ hxl,
      Or.inr (Or.inl ⟨?_, by omega, by omega,
        localConn_mono_set (fun v hv => ?_) _ _ hlr⟩)⟩
    · obtain ⟨-, hcases⟩ := hΓ.innerPos_cases hB
      beta_reduce
      rcases hcases with ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ <;> omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        hF0, hF1] at hv ⊢
      omega
    · omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one, hF0,
        hF1] at hv ⊢
      omega
  · have := hD2 i k hi' hk' hik
    have hPP : (6 * ρ + 4 + D i - 2 * z 1) - (6 * ρ + 4 + D k - 2 * z 1) = (D i - D k) := by ring
    rw [hPP]
    push_cast at this ⊢
    exact this
  · obtain ⟨c1, c2⟩ := hD3 i hi'
    simp only [Matrix.cons_val_zero] at c1 c2
    constructor
    · convert c1 using 2
      push_cast
      ring
    · convert c2 using 2
      push_cast
      ring

/-- **Rerouting the arms starting on the top side of `B_ρ(z)`.** Let `F` be the frame of the top
side (its coordinates are given by `hF0`, `hF1`) and let the frame configuration `Y` have the
separation property in the strip of depth `N` along the top side. Let `γ` be a disjoint family of
arms from `B_ρ(z)` to the boundary of `B_R(z)` none of which comes within `N` of a corner of
`B_ρ(z)` (the faces of a dual arm touching that box). Then each arm starting on the top side can be
replaced by an arm with the same colour and landing position, with inner positions `P i` at least `4
√η N` apart and at least `4 √η N` inside the top side (`[m (4ρ + 2), (m + 1)(4ρ + 2)]` with `m =
2`), carrying an inner fence of depth `⌊√η N⌋` and half-length `⌊η N⌋`. -/
theorem exists_reroute_inner_top {η : ℝ} {N ρ R : ℕ} (hN : 1 ≤ N) (hρ : 1 ≤ ρ)
    (hρR : ρ + N + 2 ≤ R) (hsN : 1 ≤ Real.sqrt η * N)
    (F : Bool → zdGraph 2 ≃g zdGraph 2)
    (hF0 : ∀ (c : Bool) (v : LatticeSite 2), F c v 0 = v 0 - cond c 1 0)
    (hF1 : ∀ (c : Bool) (v : LatticeSite 2), F c v 1 = -v 1) {lo hi : LatticeSite 2}
    (hlo : lo = ![z 0 - ρ - 1, -z 1 - ρ - N]) (hhi : hi = ![z 0 + ρ, -z 1 - ρ])
    {Y : Config (LatticeSite 2)}
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
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z ρ (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hcor : ∀ i, ∀ v ∈ (γ i).support, ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ¬(κ 0 - N - cond (σ i) 0 1 ≤ v 0 ∧ v 0 ≤ κ 0 + N ∧
        κ 1 - N - cond (σ i) 0 1 ≤ v 1 ∧ v 1 ≤ κ 1 + N)) :
    ∃ P : Fin j → ℤ,
      (∀ i, a i 1 = z 1 + ρ →
        ∃ (a' : LatticeSite 2) (Γ : (zdGraph 2).Walk a' (b i)),
        IsArm ω (σ i) z ρ (z - R) (z + R) Γ ∧
        landingPos (z - R) (z + R) (σ i) Γ = landingPos (z - R) (z + R) (σ i) (γ i) ∧
        innerPos z ρ (σ i) Γ = P i ∧
        HasInnerFence ω (σ i) z ρ ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ) ∧
      (∀ i k, a i 1 = z 1 + ρ →
        a k 1 = z 1 + ρ → i ≠ k →
        4 * Real.sqrt η * N ≤ |((P i - P k : ℤ) : ℝ)|) ∧
      (∀ i, a i 1 = z 1 + ρ →
        4 * Real.sqrt η * N ≤ ((P i - 2 * (4 * ρ + 2) : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ (((2 + 1) * (4 * ρ + 2) - P i : ℤ) : ℝ)) := by
  classical
  subst hlo hhi
  have hd01 : ∀ c : Bool, 0 ≤ cond c (1 : ℤ) 0 ∧ cond c (1 : ℤ) 0 ≤ 1 ∧
      cond c (0 : ℤ) 1 = 1 - cond c (1 : ℤ) 0 := fun c => by
    cases c <;> simp
  have hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆
      Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    omega
  obtain ⟨D, hD1, hD2, hD3⟩ := exists_reroute_of_frame (η := η) (N := N) (ρ := ρ) (R := R)
    F hY hYd hE (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h => by
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h ⊢ <;> omega)
    hγ hd (fun i => a i 1 = z 1 + ρ) (fun i hi' => by
      obtain ⟨⟨h₁, h₂, h₃, h₄⟩, -⟩ := (hγ i).innerPos_cases hB
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcr := hcor i (a i) (γ i).start_mem_support
      by_contra hcon
      omega)
    (fun i hi' v hv h₁ h₂ h₃ => by
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃
      have hcr := hcor i v hv
      rcases h₁ with h₁ | h₁
      · exact hcr ![z 0 - ρ, z 1 + ρ] (Or.inl rfl) (Or.inr rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      · exact hcr ![z 0 + ρ, z 1 + ρ] (Or.inr rfl) (Or.inr rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega))
  refine ⟨fun i => 10 * ρ + 4 + 2 * z 0 - D i, fun i hi' => ?_, fun i k hi' hk' hik => ?_,
    fun i hi' => ?_⟩
  · obtain ⟨a', Γ, hΓ, hland, ha1, ha0, ha0', hDi, x, hx, l, r, hl, hr, hlr, hxl⟩ := hD1 i hi'
    obtain ⟨c1, c2⟩ := hD3 i hi'
    obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
    have hs4 : (4 : ℝ) ≤ 4 * Real.sqrt η * N := by linarith
    have hc1 := hs4.trans c1
    have hc2 := hs4.trans c2
    norm_cast at hc1 hc2
    simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at ha1 ha0 ha0' hc1 hc2
    simp only [hF0] at hDi hl hr
    refine ⟨a', Γ, hΓ, hland, ?_, x, hx, l, r, localConn_mono_set (fun v hv => ?_) _ _ hxl,
      Or.inl ⟨?_, by omega, by omega,
        localConn_mono_set (fun v hv => ?_) _ _ hlr⟩⟩
    · obtain ⟨-, hcases⟩ := hΓ.innerPos_cases hB
      beta_reduce
      rcases hcases with ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ <;> omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        hF0, hF1] at hv ⊢
      omega
    · omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one, hF0,
        hF1] at hv ⊢
      omega
  · have := hD2 i k hi' hk' hik
    have hPP : (10 * ρ + 4 + 2 * z 0 - D i) - (10 * ρ + 4 + 2 * z 0 - D k) = -(D i - D k) := by ring
    rw [hPP]
    push_cast at this ⊢
    rw [abs_neg]
    exact this
  · obtain ⟨c1, c2⟩ := hD3 i hi'
    simp only [Matrix.cons_val_zero] at c1 c2
    constructor
    · convert c2 using 2
      push_cast
      ring
    · convert c1 using 2
      push_cast
      ring

/-- **Rerouting the arms starting on the left side of `B_ρ(z)`.** Let `F` be the frame of the left
side (its coordinates are given by `hF0`, `hF1`) and let the frame configuration `Y` have the
separation property in the strip of depth `N` along the left side. Let `γ` be a disjoint family of
arms from `B_ρ(z)` to the boundary of `B_R(z)` none of which comes within `N` of a corner of
`B_ρ(z)` (the faces of a dual arm touching that box). Then each arm starting on the left side can be
replaced by an arm with the same colour and landing position, with inner positions `P i` at least `4
√η N` apart and at least `4 √η N` inside the left side (`[m (4ρ + 2), (m + 1)(4ρ + 2)]` with `m =
3`), carrying an inner fence of depth `⌊√η N⌋` and half-length `⌊η N⌋`. -/
theorem exists_reroute_inner_left {η : ℝ} {N ρ R : ℕ} (hN : 1 ≤ N) (hρ : 1 ≤ ρ)
    (hρR : ρ + N + 2 ≤ R) (hsN : 1 ≤ Real.sqrt η * N)
    (F : Bool → zdGraph 2 ≃g zdGraph 2)
    (hF0 : ∀ (c : Bool) (v : LatticeSite 2), F c v 0 = v 1 - cond c 1 0)
    (hF1 : ∀ (c : Bool) (v : LatticeSite 2), F c v 1 = v 0 - cond c 1 0) {lo hi : LatticeSite 2}
    (hlo : lo = ![z 1 - ρ - 1, z 0 - ρ - 1 - N]) (hhi : hi = ![z 1 + ρ, z 0 - ρ - 1])
    {Y : Config (LatticeSite 2)}
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
    {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
    {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z ρ (z - R) (z + R) (γ i)) (hd : ArmsDisjoint σ γ)
    (hcor : ∀ i, ∀ v ∈ (γ i).support, ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ¬(κ 0 - N - cond (σ i) 0 1 ≤ v 0 ∧ v 0 ≤ κ 0 + N ∧
        κ 1 - N - cond (σ i) 0 1 ≤ v 1 ∧ v 1 ≤ κ 1 + N)) :
    ∃ P : Fin j → ℤ,
      (∀ i, a i 0 = z 0 - ρ - cond (σ i) 0 1 →
        ∃ (a' : LatticeSite 2) (Γ : (zdGraph 2).Walk a' (b i)),
        IsArm ω (σ i) z ρ (z - R) (z + R) Γ ∧
        landingPos (z - R) (z + R) (σ i) Γ = landingPos (z - R) (z + R) (σ i) (γ i) ∧
        innerPos z ρ (σ i) Γ = P i ∧
        HasInnerFence ω (σ i) z ρ ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ) ∧
      (∀ i k, a i 0 = z 0 - ρ - cond (σ i) 0 1 →
        a k 0 = z 0 - ρ - cond (σ k) 0 1 → i ≠ k →
        4 * Real.sqrt η * N ≤ |((P i - P k : ℤ) : ℝ)|) ∧
      (∀ i, a i 0 = z 0 - ρ - cond (σ i) 0 1 →
        4 * Real.sqrt η * N ≤ ((P i - 3 * (4 * ρ + 2) : ℤ) : ℝ) ∧
        4 * Real.sqrt η * N ≤ (((3 + 1) * (4 * ρ + 2) - P i : ℤ) : ℝ)) := by
  classical
  subst hlo hhi
  have hd01 : ∀ c : Bool, 0 ≤ cond c (1 : ℤ) 0 ∧ cond c (1 : ℤ) 0 ≤ 1 ∧
      cond c (0 : ℤ) 1 = 1 - cond c (1 : ℤ) 0 := fun c => by
    cases c <;> simp
  have hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆
      Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    omega
  obtain ⟨D, hD1, hD2, hD3⟩ := exists_reroute_of_frame (η := η) (N := N) (ρ := ρ) (R := R)
    F hY hYd hE (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h₁ h₂ h₃ h₄ => by
      rw [hF0] at h₁ h₂
      rw [hF1] at h₃ h₄
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃ h₄
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h₁ h₂ h₃ h₄ ⊢ <;> omega)
    (fun c v h => by
      cases c <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at h ⊢ <;> omega)
    hγ hd (fun i => a i 0 = z 0 - ρ - cond (σ i) 0 1) (fun i hi' => by
      obtain ⟨⟨h₁, h₂, h₃, h₄⟩, -⟩ := (hγ i).innerPos_cases hB
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hcr := hcor i (a i) (γ i).start_mem_support
      by_contra hcon
      omega)
    (fun i hi' v hv h₁ h₂ h₃ => by
      obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
      simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃
      have hcr := hcor i v hv
      rcases h₁ with h₁ | h₁
      · exact hcr ![z 0 - ρ, z 1 - ρ] (Or.inl rfl) (Or.inl rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      · exact hcr ![z 0 - ρ, z 1 + ρ] (Or.inl rfl) (Or.inr rfl) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega))
  refine ⟨fun i => 14 * ρ + 6 + 2 * z 1 - D i, fun i hi' => ?_, fun i k hi' hk' hik => ?_,
    fun i hi' => ?_⟩
  · obtain ⟨a', Γ, hΓ, hland, ha1, ha0, ha0', hDi, x, hx, l, r, hl, hr, hlr, hxl⟩ := hD1 i hi'
    obtain ⟨c1, c2⟩ := hD3 i hi'
    obtain ⟨e0, e1, e2⟩ := hd01 (σ i)
    have hs4 : (4 : ℝ) ≤ 4 * Real.sqrt η * N := by linarith
    have hc1 := hs4.trans c1
    have hc2 := hs4.trans c2
    norm_cast at hc1 hc2
    simp only [hF0, hF1, Matrix.cons_val_zero, Matrix.cons_val_one] at ha1 ha0 ha0' hc1 hc2
    simp only [hF0] at hDi hl hr
    refine ⟨a', Γ, hΓ, hland, ?_, x, hx, l, r, localConn_mono_set (fun v hv => ?_) _ _ hxl,
      Or.inr (Or.inr (Or.inr ⟨?_, by omega, by omega,
        localConn_mono_set (fun v hv => ?_) _ _ hlr⟩))⟩
    · obtain ⟨-, hcases⟩ := hΓ.innerPos_cases hB
      beta_reduce
      rcases hcases with ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ <;> omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        hF0, hF1] at hv ⊢
      omega
    · omega
    · simp only [mem_ofPred_eq, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one, hF0,
        hF1] at hv ⊢
      omega
  · have := hD2 i k hi' hk' hik
    have hPP : (14 * ρ + 6 + 2 * z 1 - D i) - (14 * ρ + 6 + 2 * z 1 - D k) = -(D i - D k) := by ring
    rw [hPP]
    push_cast at this ⊢
    rw [abs_neg]
    exact this
  · obtain ⟨c1, c2⟩ := hD3 i hi'
    simp only [Matrix.cons_val_zero] at c1 c2
    constructor
    · convert c2 using 2
      push_cast
      ring
    · convert c1 using 2
      push_cast
      ring

/-! ### Frames of the dual lattice -/

/-- **Frames of the dual lattice.** If an automorphism `Fd` of `ℤ²` moves dual configurations by
the map `g` of faces, then the frame configuration `Fd(Φ ω)` has the image of the dual
configuration of `ω` as its edges and the image of the open edges of `ω` under `v ↦ g (v - 1)` as
its dual configuration. -/
theorem frame_relations {Φ : Config (LatticeSite 2) ≃ᵐ Config (LatticeSite 2)}
    (hΦ : ∀ ω, Φ ω ∩ (zdGraph 2).edgeSet = dualConfig ω) (Fd Fo : zdGraph 2 ≃g zdGraph 2)
    (g : LatticeSite 2 → LatticeSite 2)
    (hFd : ∀ X, dualConfig (Sym2.map Fd '' X) = Sym2.map g '' dualConfig X)
    (hFo : ∀ v, Fo v = g (v - 1)) (ω : Config (LatticeSite 2)) :
    Sym2.map Fd '' Φ ω ∩ (zdGraph 2).edgeSet = Sym2.map Fd '' dualConfig ω ∧
    dualConfig (Sym2.map Fd '' Φ ω) = Sym2.map Fo '' (ω ∩ (zdGraph 2).edgeSet) := by
  refine ⟨by rw [← image_sym2Map_inter_edgeSet, hΦ], ?_⟩
  rw [hFd, ← dualConfig_inter_edgeSet (Φ ω), hΦ, dualConfig_dualConfig, Set.image_image]
  refine Set.image_congr fun e _ => ?_
  rw [Sym2.map_map]
  congr 1
  funext v
  exact (hFo v).symm

/-- The law of a frame configuration. -/
theorem law_frame_apply {Φ : Config (LatticeSite 2) ≃ᵐ Config (LatticeSite 2)}
    {q q' : Sym2 (LatticeSite 2) → unitInterval} (hq : (law q).map Φ = law q')
    (Fd : zdGraph 2 ≃g zdGraph 2) (A : Set (Config (LatticeSite 2))) :
    law q {ω | Sym2.map Fd '' Φ ω ∈ A} = law (fun e => q' (Sym2.map Fd.symm e)) A := by
  have h := law_comp_sym2Map_apply q' Fd.symm.toEquiv A
  change _ = law (fun e => q' (Sym2.map Fd.symm.toEquiv e)) A
  rw [h, ← hq, MeasurableEquiv.map_apply]
  rfl

/-- The frame of the bottom side: faces as they are, vertices moved by `(-1, -1)`. -/
theorem exists_frame_bottom : ∃ Fd Fo : zdGraph 2 ≃g zdGraph 2,
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 0 = v 0 - cond c 1 0) ∧
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 1 = v 1 - cond c 1 0) ∧
    (∀ v, Fd.symm v = v) ∧ ∃ g : LatticeSite 2 → LatticeSite 2,
      (∀ X, dualConfig (Sym2.map Fd '' X) = Sym2.map g '' dualConfig X) ∧
      ∀ v, Fo v = g (v - 1) := by
  obtain ⟨tr, htr⟩ := exists_zdGraph_iso_add (d := 2) (-1)
  refine ⟨RelIso.refl _, tr, fun c v => ?_, fun c v => ?_, fun v => rfl, id, fun X => ?_,
    fun v => ?_⟩
  · cases c
    · simp
    · simp [htr, sub_eq_add_neg]
  · cases c
    · simp
    · simp [htr, sub_eq_add_neg]
  · have : (⇑(RelIso.refl (zdGraph 2).Adj) : LatticeSite 2 → LatticeSite 2) = id := rfl
    rw [this, Sym2.map_id, Set.image_id, Set.image_id]
  · rw [htr, sub_eq_add_neg]
    rfl

/-- The frame of the top side: the reflection `(x, y) ↦ (x, -y)` of faces, vertices moved to
`(x - 1, -y)`. -/
theorem exists_frame_top : ∃ Fd Fo : zdGraph 2 ≃g zdGraph 2,
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 0 = v 0 - cond c 1 0) ∧
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 1 = -v 1) ∧
    (∀ v, Fd.symm v = ![v 0, 0 - v 1]) ∧ ∃ g : LatticeSite 2 → LatticeSite 2,
      (∀ X, dualConfig (Sym2.map Fd '' X) = Sym2.map g '' dualConfig X) ∧
      ∀ v, Fo v = g (v - 1) := by
  obtain ⟨tr, htr⟩ := exists_zdGraph_iso_add (d := 2) (-1)
  obtain ⟨rf, hrf⟩ := exists_iso_reflect_one 0
  obtain ⟨rf', hrf'⟩ := exists_iso_reflect_one (-1)
  have hrfs : ∀ v, rf.symm v = ![v 0, 0 - v 1] := fun v => by
    apply rf.injective
    rw [RelIso.apply_symm_apply, hrf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
    exact eq_vec_two v
  refine ⟨rf, tr.trans rf', fun c v => ?_, fun c v => ?_, hrfs,
    fun v : LatticeSite 2 => ![v 0, 0 - 1 - v 1], fun X => ?_, fun v => ?_⟩
  · cases c
    · simp [hrf]
    · simp [htr, hrf', sub_eq_add_neg]
  · cases c
    · simp [hrf]
    · simp [htr, hrf']
  · have : (⇑rf : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - v 1] := funext hrf
    rw [this]
    exact dualConfig_image_reflect 0 X
  · change rf' (tr v) = _
    rw [hrf', htr]
    simp [sub_eq_add_neg]

/-- The frame of the left side: the swap `(x, y) ↦ (y, x)` of faces, vertices moved to
`(y - 1, x - 1)`. -/
theorem exists_frame_left : ∃ Fd Fo : zdGraph 2 ≃g zdGraph 2,
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 0 = v 1 - cond c 1 0) ∧
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 1 = v 0 - cond c 1 0) ∧
    (∀ v, Fd.symm v = ![v 1, v 0]) ∧ ∃ g : LatticeSite 2 → LatticeSite 2,
      (∀ X, dualConfig (Sym2.map Fd '' X) = Sym2.map g '' dualConfig X) ∧
      ∀ v, Fo v = g (v - 1) := by
  obtain ⟨tr, htr⟩ := exists_zdGraph_iso_add (d := 2) (-1)
  obtain ⟨sw, hsw⟩ := exists_iso_swap
  have hsws : ∀ v, sw.symm v = ![v 1, v 0] := fun v => by
    apply sw.injective
    rw [RelIso.apply_symm_apply, hsw]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact eq_vec_two v
  refine ⟨sw, tr.trans sw, fun c v => ?_, fun c v => ?_, hsws,
    fun v : LatticeSite 2 => ![v 1, v 0], fun X => ?_, fun v => ?_⟩
  · cases c
    · simp [hsw]
    · simp [htr, hsw, sub_eq_add_neg]
  · cases c
    · simp [hsw]
    · simp [htr, hsw, sub_eq_add_neg]
  · have : (⇑sw : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := funext hsw
    rw [this]
    exact dualConfig_image_swap X
  · change sw (tr v) = _
    rw [hsw, htr]
    simp [sub_eq_add_neg]

/-- The frame of the right side: the quarter turn `(x, y) ↦ (y, -x)` of faces, vertices moved to
`(y - 1, -x)`. -/
theorem exists_frame_right : ∃ Fd Fo : zdGraph 2 ≃g zdGraph 2,
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 0 = v 1 - cond c 1 0) ∧
    (∀ (c : Bool) (v : LatticeSite 2), (cond c Fo Fd) v 1 = -v 0) ∧
    (∀ v, Fd.symm v = ![0 - v 1, v 0]) ∧ ∃ g : LatticeSite 2 → LatticeSite 2,
      (∀ X, dualConfig (Sym2.map Fd '' X) = Sym2.map g '' dualConfig X) ∧
      ∀ v, Fo v = g (v - 1) := by
  obtain ⟨tr, htr⟩ := exists_zdGraph_iso_add (d := 2) (-1)
  obtain ⟨sw, hsw⟩ := exists_iso_swap
  obtain ⟨rf, hrf⟩ := exists_iso_reflect_one 0
  obtain ⟨rf', hrf'⟩ := exists_iso_reflect_one (-1)
  have hFs : ∀ v, (sw.trans rf).symm v = ![0 - v 1, v 0] := fun v => by
    apply (sw.trans rf).injective
    rw [RelIso.apply_symm_apply]
    change v = rf (sw _)
    rw [hsw, hrf]
    funext i
    fin_cases i <;> simp
  refine ⟨sw.trans rf, tr.trans (sw.trans rf'), fun c v => ?_, fun c v => ?_, hFs,
    fun v : LatticeSite 2 => ![v 1, 0 - 1 - v 0], fun X => ?_, fun v => ?_⟩
  · cases c
    · change rf (sw v) 0 = _
      simp [hsw, hrf]
    · change rf' (sw (tr v)) 0 = _
      simp [htr, hsw, hrf', sub_eq_add_neg]
  · cases c
    · change rf (sw v) 1 = _
      simp [hsw, hrf]
    · change rf' (sw (tr v)) 1 = _
      simp [htr, hsw, hrf']
  · have h₁ : (⇑(sw.trans rf) : LatticeSite 2 → LatticeSite 2) =
        (fun v => ![v 0, 0 - v 1]) ∘ fun v : LatticeSite 2 => ![v 1, v 0] := by
      funext v
      change rf (sw v) = _
      rw [hsw, hrf]
      rfl
    have h₂ : (fun v : LatticeSite 2 => ![v 1, 0 - 1 - v 0]) =
        (fun v => ![v 0, 0 - 1 - v 1]) ∘ fun v : LatticeSite 2 => ![v 1, v 0] := by
      funext v
      simp
    rw [h₁, h₂, Sym2.map_comp, Sym2.map_comp, Set.image_comp, Set.image_comp,
      dualConfig_image_reflect 0, dualConfig_image_swap]
  · change rf' (sw (tr v)) = _
    rw [hrf', hsw, htr]
    simp [sub_eq_add_neg]

/-! ### Arms near the corners -/

/-- **A walk passing near a point gives a one-arm event.** A walk of colour `c` (its edges open,
resp. dual-open) that visits the box of radius `n` about `κ` (the faces touching it) and ends
outside the interior of the box of radius `P` about `κ` (its faces) contains an arm of colour `c`
from `B_n(κ)` to the boundary of `B_P(κ)`. -/
theorem mem_multiArmEvent_one_of_walk {c : Bool} {κ : LatticeSite 2} {n P : ℕ}
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b)
    (hE : ∀ e ∈ γ.edges, e ∈ cond c ω (dualConfig ω)) {v : LatticeSite 2} (hv : v ∈ γ.support)
    (hvS : v ∈ cond c (Icc (κ - n) (κ + n)) (Icc (κ - n - 1) (κ + n)))
    (hb : b ∉ cond c (Icc (κ - P + 1) (κ + P - 1)) (Icc (κ - P) (κ + P - 1))) :
    ω ∈ multiArmEvent ![c] κ n P := by
  obtain ⟨x, hx, p₁, s, hps, hs⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem
    (S := cond c (Icc (κ - n) (κ + n)) (Icc (κ - n - 1) (κ + n))) γ ⟨v, hv, hvS⟩
  obtain ⟨y, t, u, htu, hy, ht⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem
    (T := cond c (Icc (κ - P + 1) (κ + P - 1)) (Icc (κ - P) (κ + P - 1))) s hb
  have hArm : IsArm ω c κ n (κ - P) (κ + P) t := by
    rw [isArm_iff_cond]
    refine ⟨⟨hx, fun w hw => hs w ?_, hy, ht⟩, fun e he => hE e ?_⟩
    · rw [← htu, SimpleGraph.Walk.tail_support_append]
      exact List.mem_append_left _ hw
    · rw [← hps, SimpleGraph.Walk.edges_append, ← htu, SimpleGraph.Walk.edges_append]
      exact List.mem_append_right _ (List.mem_append_left _ he)
  refine (mem_multiArmEventTo_iff).2 ⟨fun _ => x, fun _ => y, fun _ => t, fun i => ?_,
    armsDisjoint_of_subsingleton le_rfl _ _, fun _ => ⟨trivial, trivial⟩,
    fun i k l hik _ => ?_⟩
  · rw [Fin.fin_one_eq_zero i]
    exact hArm
  · have := Subsingleton.elim i k
    subst this
    exact absurd hik (lt_irrefl _)

/-! ### The inner separation step -/

/-- **The inner separation step, deterministic part.** Let the four frame configurations of the
dual lattice have the separation property of Lemma 15 in the strips of depth `N` along the four
sides of `B_ρ(z)`, and let no arm of either colour run from `B_N(κ)` to the boundary of `B_ρ(κ)` for
the four corners `κ` of `B_ρ(z)`. Then every disjoint family of arms from `B_ρ(z)` to the boundary
of `B_R(z)` in counterclockwise order, for a colour sequence without packs, can be rerouted near
`B_ρ(z)` into a family with the same landing positions that is separated at the inner boundary,
with separation `4 √η N` and inner fences of depth `⌊√η N⌋` and half-length `⌊η N⌋`. -/
theorem mem_innerSeparatedArmEvent_of_frames {j : ℕ} {σ : Fin j → Bool}
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℝ} {N ρ R : ℕ} (hN : 1 ≤ N)
    (hNρ : N + 2 ≤ ρ) (hρR : 2 * ρ + 1 ≤ R) (hsN : 1 ≤ Real.sqrt η * N)
    (Fb Fr Ft Fl : Bool → zdGraph 2 ≃g zdGraph 2)
    (hFb0 : ∀ (c : Bool) (v : LatticeSite 2), Fb c v 0 = v 0 - cond c 1 0)
    (hFb1 : ∀ (c : Bool) (v : LatticeSite 2), Fb c v 1 = v 1 - cond c 1 0)
    (hFr0 : ∀ (c : Bool) (v : LatticeSite 2), Fr c v 0 = v 1 - cond c 1 0)
    (hFr1 : ∀ (c : Bool) (v : LatticeSite 2), Fr c v 1 = -v 0)
    (hFt0 : ∀ (c : Bool) (v : LatticeSite 2), Ft c v 0 = v 0 - cond c 1 0)
    (hFt1 : ∀ (c : Bool) (v : LatticeSite 2), Ft c v 1 = -v 1)
    (hFl0 : ∀ (c : Bool) (v : LatticeSite 2), Fl c v 0 = v 1 - cond c 1 0)
    (hFl1 : ∀ (c : Bool) (v : LatticeSite 2), Fl c v 1 = v 0 - cond c 1 0)
    {Yb Yr Yt Yl : Config (LatticeSite 2)}
    (hYb : Yb ∩ (zdGraph 2).edgeSet = Sym2.map (Fb false) '' dualConfig ω)
    (hYdb : dualConfig Yb = Sym2.map (Fb true) '' (ω ∩ (zdGraph 2).edgeSet))
    (hYr : Yr ∩ (zdGraph 2).edgeSet = Sym2.map (Fr false) '' dualConfig ω)
    (hYdr : dualConfig Yr = Sym2.map (Fr true) '' (ω ∩ (zdGraph 2).edgeSet))
    (hYt : Yt ∩ (zdGraph 2).edgeSet = Sym2.map (Ft false) '' dualConfig ω)
    (hYdt : dualConfig Yt = Sym2.map (Ft true) '' (ω ∩ (zdGraph 2).edgeSet))
    (hYl : Yl ∩ (zdGraph 2).edgeSet = Sym2.map (Fl false) '' dualConfig ω)
    (hYdl : dualConfig Yl = Sym2.map (Fl true) '' (ω ∩ (zdGraph 2).edgeSet))
    {lob hib lor hir lot hit lol hil : LatticeSite 2}
    (hlob : lob = ![z 0 - ρ - 1, z 1 - ρ - 1 - N]) (hhib : hib = ![z 0 + ρ, z 1 - ρ - 1])
    (hlor : lor = ![z 1 - ρ - 1, -z 0 - ρ - N]) (hhir : hir = ![z 1 + ρ, -z 0 - ρ])
    (hlot : lot = ![z 0 - ρ - 1, -z 1 - ρ - N]) (hhit : hit = ![z 0 + ρ, -z 1 - ρ])
    (hlol : lol = ![z 1 - ρ - 1, z 0 - ρ - 1 - N]) (hhil : hil = ![z 1 + ρ, z 0 - ρ - 1])
    (hEb : Yb ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lob 1 ∧ b i 1 = hib 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lob hib) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lob 1 - 1 ∧ b i 1 = hib 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lob 0, lob 1 - 1] : LatticeSite 2)
            ![hib 0 - 1, hib 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lob hib})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lob 1 ∧ b' i 1 = hib 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lob hib) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lob 1 - 1 ∧ b' i 1 = hib 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lob 0, lob 1 - 1] : LatticeSite 2)
              ![hib 0 - 1, hib 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lob hib})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hib 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lob 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hib 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hib 1]
              ![b' i 0 + ⌊η * N⌋₊, hib 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    (hEr : Yr ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lor 1 ∧ b i 1 = hir 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lor hir) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lor 1 - 1 ∧ b i 1 = hir 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lor 0, lor 1 - 1] : LatticeSite 2)
            ![hir 0 - 1, hir 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lor hir})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lor 1 ∧ b' i 1 = hir 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lor hir) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lor 1 - 1 ∧ b' i 1 = hir 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lor 0, lor 1 - 1] : LatticeSite 2)
              ![hir 0 - 1, hir 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lor hir})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hir 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lor 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hir 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hir 1]
              ![b' i 0 + ⌊η * N⌋₊, hir 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    (hEt : Yt ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lot 1 ∧ b i 1 = hit 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lot hit) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lot 1 - 1 ∧ b i 1 = hit 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lot 0, lot 1 - 1] : LatticeSite 2)
            ![hit 0 - 1, hit 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lot hit})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lot 1 ∧ b' i 1 = hit 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lot hit) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lot 1 - 1 ∧ b' i 1 = hit 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lot 0, lot 1 - 1] : LatticeSite 2)
              ![hit 0 - 1, hit 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lot hit})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hit 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lot 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hit 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hit 1]
              ![b' i 0 + ⌊η * N⌋₊, hit 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    (hEl : Yl ∈ {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool) (a b : ι → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, cond (σ i)
        (a i 1 = lol 1 ∧ b i 1 = hil 1 ∧ (∀ x ∈ (γ i).support, x ∈ Icc lol hil) ∧
          ∀ e ∈ (γ i).edges, e ∈ ω)
        (a i 1 = lol 1 - 1 ∧ b i 1 = hil 1 ∧
          (∀ x ∈ (γ i).support, x ∈ Icc (![lol 0, lol 1 - 1] : LatticeSite 2)
            ![hil 0 - 1, hil 1]) ∧
          ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
            ∀ x ∈ e, x ∈ Icc lol hil})) →
      (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ i).support, x ∉ (γ k).support) →
      ∃ (b' : ι → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
        (∀ i, cond (σ i)
          (a i 1 = lol 1 ∧ b' i 1 = hil 1 ∧ (∀ x ∈ (γ' i).support, x ∈ Icc lol hil) ∧
            ∀ e ∈ (γ' i).edges, e ∈ ω)
          (a i 1 = lol 1 - 1 ∧ b' i 1 = hil 1 ∧
            (∀ x ∈ (γ' i).support, x ∈ Icc (![lol 0, lol 1 - 1] : LatticeSite 2)
              ![hil 0 - 1, hil 1]) ∧
            ∀ e ∈ (γ' i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc lol hil})) ∧
        (∀ i k, i ≠ k → σ i = σ k → ∀ x ∈ (γ' i).support, x ∉ (γ' k).support) ∧
        (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ hil 1) ∧
        (∀ i k, i ≠ k → 4 * Real.sqrt η * N ≤
          |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' k 0 + cond (σ k) 0 1 : ℤ) : ℝ)|) ∧
        (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 - 2 * lol 0 : ℤ) : ℝ) ∧
          4 * Real.sqrt η * N ≤ ((2 * hil 0 - (2 * b' i 0 + cond (σ i) 0 1) : ℤ) : ℝ)) ∧
        ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
          l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc ![b' i 0 - ⌊η * N⌋₊, hil 1]
              ![b' i 0 + ⌊η * N⌋₊, hil 1 + ⌊Real.sqrt η * N⌋₊]) l r ∧
          cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
            (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
              (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l})
    (hcorner : ∀ (c : Bool) (κ : LatticeSite 2), (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ω ∉ multiArmEvent ![c] κ N ρ)
    (hω : ω ∈ multiArmEvent σ z ρ R) :
    ω ∈ innerSeparatedArmEvent σ z ρ R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ := by
  classical
  obtain ⟨a, b, γ, hγ, hd, -, ho⟩ := (mem_multiArmEventTo_iff).1 hω
  have hB : Icc (z - (ρ : LatticeSite 2)) (z + ρ) ⊆
      Icc (z - (R : LatticeSite 2) + 1) (z + R - 1) := by
    intro v hv
    rw [mem_Icc_two_iff] at hv ⊢
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    omega
  -- no arm comes near a corner
  have hcor : ∀ i, ∀ v ∈ (γ i).support, ∀ κ : LatticeSite 2, (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
      (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ¬(κ 0 - N - cond (σ i) 0 1 ≤ v 0 ∧ v 0 ≤ κ 0 + N ∧
        κ 1 - N - cond (σ i) 0 1 ≤ v 1 ∧ v 1 ≤ κ 1 + N) := by
    intro i v hv κ hκ0 hκ1 hzone
    obtain ⟨hc, hE'⟩ := isArm_iff_cond.1 (hγ i)
    refine hcorner (σ i) κ hκ0 hκ1 (mem_multiArmEvent_one_of_walk (γ i) hE' hv ?_ fun hb => ?_)
    · cases hσi : σ i <;> rw [hσi] at hzone <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at hzone ⊢ <;> omega
    · apply hc.end_notMem
      cases hσi : σ i <;> rw [hσi] at hb <;>
        simp only [Bool.cond_true, Bool.cond_false, mem_Icc_two_iff, Pi.sub_apply, Pi.add_apply,
          Pi.natCast_apply, Pi.one_apply] at hb ⊢ <;> omega
  -- the four sides
  obtain ⟨Pb, hPb1, hPb2, hPb3⟩ := exists_reroute_inner_bottom (η := η) hN (by omega) (by omega)
    hsN Fb hFb0 hFb1 hlob hhib hYb hYdb hEb hγ hd hcor
  obtain ⟨Pr, hPr1, hPr2, hPr3⟩ := exists_reroute_inner_right (η := η) hN (by omega) (by omega)
    hsN Fr hFr0 hFr1 hlor hhir hYr hYdr hEr hγ hd hcor
  obtain ⟨Pt, hPt1, hPt2, hPt3⟩ := exists_reroute_inner_top (η := η) hN (by omega) (by omega)
    hsN Ft hFt0 hFt1 hlot hhit hYt hYdt hEt hγ hd hcor
  obtain ⟨Pl, hPl1, hPl2, hPl3⟩ := exists_reroute_inner_left (η := η) hN (by omega) (by omega)
    hsN Fl hFl0 hFl1 hlol hhil hYl hYdl hEl hγ hd hcor
  -- every arm starts on a side
  obtain ⟨P, hP⟩ : ∃ P : Fin j → ℤ, P = fun i =>
      if a i 1 = z 1 - ρ - cond (σ i) 0 1 then Pb i else if a i 0 = z 0 + ρ then Pr i
      else if a i 1 = z 1 + ρ then Pt i else Pl i := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Fin j → ℤ, m = fun i =>
      if a i 1 = z 1 - ρ - cond (σ i) 0 1 then 0 else if a i 0 = z 0 + ρ then 1
      else if a i 1 = z 1 + ρ then 2 else 3 := ⟨_, rfl⟩
  have hcase : ∀ i, (a i 1 = z 1 - ρ - cond (σ i) 0 1 ∧ P i = Pb i ∧ m i = 0) ∨
      (a i 0 = z 0 + ρ ∧ P i = Pr i ∧ m i = 1) ∨ (a i 1 = z 1 + ρ ∧ P i = Pt i ∧ m i = 2) ∨
      (a i 0 = z 0 - ρ - cond (σ i) 0 1 ∧ P i = Pl i ∧ m i = 3) := by
    intro i
    obtain ⟨-, hs⟩ := (hγ i).innerPos_cases hB
    by_cases h1 : a i 1 = z 1 - ρ - cond (σ i) 0 1
    · exact Or.inl ⟨h1, by simp only [hP, h1, ↓reduceIte], by simp only [hm, h1, ↓reduceIte]⟩
    by_cases h2 : a i 0 = z 0 + ρ
    · exact Or.inr (Or.inl ⟨h2, by simp only [hP, h1, h2, ↓reduceIte],
        by simp only [hm, h1, h2, ↓reduceIte]⟩)
    by_cases h3 : a i 1 = z 1 + ρ
    · refine Or.inr (Or.inr (Or.inl ⟨h3, ?_, ?_⟩))
      · simp only [hP, h1, h2, ↓reduceIte]
        simp only [h3, ↓reduceIte]
      · simp only [hm, h1, h2, ↓reduceIte]
        simp only [h3, ↓reduceIte]
    have h4 : a i 0 = z 0 - ρ - cond (σ i) 0 1 := by
      rcases hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h h3
      · exact absurd h h2
      · exact absurd h h1
      · exact h
    exact Or.inr (Or.inr (Or.inr ⟨h4, by simp only [hP, h1, h2, h3, ↓reduceIte],
      by simp only [hm, h1, h2, h3, ↓reduceIte]⟩))
  -- the new arms
  have hnew : ∀ i, ∃ (a' : LatticeSite 2) (Γ : (zdGraph 2).Walk a' (b i)),
      IsArm ω (σ i) z ρ (z - R) (z + R) Γ ∧
      landingPos (z - R) (z + R) (σ i) Γ = landingPos (z - R) (z + R) (σ i) (γ i) ∧
      innerPos z ρ (σ i) Γ = P i ∧
      HasInnerFence ω (σ i) z ρ ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊ Γ := by
    intro i
    rcases hcase i with ⟨hi, hPi, -⟩ | ⟨hi, hPi, -⟩ | ⟨hi, hPi, -⟩ | ⟨hi, hPi, -⟩ <;> rw [hPi]
    · exact hPb1 i hi
    · exact hPr1 i hi
    · exact hPt1 i hi
    · exact hPl1 i hi
  choose a' Γ hΓarm hΓland hΓin hΓfen using hnew
  -- each inner position lies inside its side
  have hint : ∀ i, 4 * Real.sqrt η * N ≤ ((P i - m i * (4 * ρ + 2) : ℤ) : ℝ) ∧
      4 * Real.sqrt η * N ≤ (((m i + 1) * (4 * ρ + 2) - P i : ℤ) : ℝ) := by
    intro i
    rcases hcase i with ⟨hi, hPi, hmi⟩ | ⟨hi, hPi, hmi⟩ | ⟨hi, hPi, hmi⟩ | ⟨hi, hPi, hmi⟩ <;>
      rw [hPi, hmi]
    · exact hPb3 i hi
    · exact hPr3 i hi
    · exact hPt3 i hi
    · exact hPl3 i hi
  have hs0 : (0 : ℝ) ≤ 4 * Real.sqrt η * N := by positivity
  have hdiff : ∀ i k, m i < m k → 4 * Real.sqrt η * N ≤ |((P i - P k : ℤ) : ℝ)| := by
    intro i k hik
    obtain ⟨h₁, h₂⟩ := hint i
    obtain ⟨h₃, h₄⟩ := hint k
    have hW : ((m i : ℝ) + 1) * (4 * ρ + 2) ≤ (m k : ℝ) * (4 * ρ + 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hik) (by positivity)
    push_cast at h₁ h₂ h₃ h₄ ⊢
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  refine ⟨a', b, Γ, hΓarm, ArmsDisjoint.of_landingPos_eq hσ hB hγ hd ho hΓarm hΓland,
    fun i k l hik hkl => ?_, fun i k hik => ?_, fun i mm => ?_, hΓfen⟩
  · rw [hΓland i, hΓland k, hΓland l]
    exact ho i k l hik hkl
  · rw [hΓin i, hΓin k]
    rcases hcase i with ⟨hi, hPi, hmi⟩ | ⟨hi, hPi, hmi⟩ | ⟨hi, hPi, hmi⟩ | ⟨hi, hPi, hmi⟩ <;>
    rcases hcase k with ⟨hk, hPk, hmk⟩ | ⟨hk, hPk, hmk⟩ | ⟨hk, hPk, hmk⟩ | ⟨hk, hPk, hmk⟩ <;>
    first
    | (rw [hPi, hPk]; first
        | exact hPb2 i k hi hk hik
        | exact hPr2 i k hi hk hik
        | exact hPt2 i k hi hk hik
        | exact hPl2 i k hi hk hik)
    | exact hdiff i k (by omega)
    | (rw [← neg_sub, Int.cast_neg, abs_neg]; exact hdiff k i (by omega))
  · rw [hΓin i]
    obtain ⟨h₁, h₂⟩ := hint i
    push_cast at h₁ h₂ ⊢
    rcases le_or_gt (mm : ℤ) (m i) with hmm | hmm
    · have hW : (mm : ℝ) * (4 * ρ + 2) ≤ (m i : ℝ) * (4 * ρ + 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmm) (by positivity)
      exact le_trans (by linarith) (le_abs_self _)
    · have hW : ((m i : ℝ) + 1) * (4 * ρ + 2) ≤ (mm : ℝ) * (4 * ρ + 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmm) (by positivity)
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)

/-- **The budget of the inner step**: if `B` has probability at most `8x` and four events fail with
probability at most `2x` each, then the complement of `B` intersected with the four events has
probability at least `1 - 16x`. -/
theorem one_sub_le_measure_compl_inter {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B E₁ E₂ E₃ E₄ : Set Ω} {x δ : ℝ≥0∞}
    (hm : MeasurableSet (Bᶜ ∩ (E₁ ∩ E₂ ∩ E₃ ∩ E₄))) (hB : μ B ≤ 8 * x) (h₁ : μ E₁ᶜ ≤ 2 * x)
    (h₂ : μ E₂ᶜ ≤ 2 * x) (h₃ : μ E₃ᶜ ≤ 2 * x) (h₄ : μ E₄ᶜ ≤ 2 * x) (hx : 16 * x = δ) :
    1 - δ ≤ μ (Bᶜ ∩ (E₁ ∩ E₂ ∩ E₃ ∩ E₄)) := by
  have hGc : μ (Bᶜ ∩ (E₁ ∩ E₂ ∩ E₃ ∩ E₄))ᶜ ≤ δ := by
    have hsub : (Bᶜ ∩ (E₁ ∩ E₂ ∩ E₃ ∩ E₄))ᶜ ⊆ B ∪ E₁ᶜ ∪ E₂ᶜ ∪ E₃ᶜ ∪ E₄ᶜ := by
      intro ω hω
      simp only [mem_compl_iff, mem_inter_iff, not_and_or, not_not, mem_union] at hω ⊢
      tauto
    calc _ ≤ μ (B ∪ E₁ᶜ ∪ E₂ᶜ ∪ E₃ᶜ ∪ E₄ᶜ) := measure_mono hsub
      _ ≤ μ (B ∪ E₁ᶜ ∪ E₂ᶜ ∪ E₃ᶜ) + μ E₄ᶜ := measure_union_le _ _
      _ ≤ μ (B ∪ E₁ᶜ ∪ E₂ᶜ) + μ E₃ᶜ + μ E₄ᶜ := by
        gcongr
        exact measure_union_le _ _
      _ ≤ μ (B ∪ E₁ᶜ) + μ E₂ᶜ + μ E₃ᶜ + μ E₄ᶜ := by
        gcongr
        exact measure_union_le _ _
      _ ≤ μ B + μ E₁ᶜ + μ E₂ᶜ + μ E₃ᶜ + μ E₄ᶜ := by
        gcongr
        exact measure_union_le _ _
      _ ≤ 8 * x + 2 * x + 2 * x + 2 * x + 2 * x := by gcongr
      _ = 16 * x := by ring
      _ = δ := hx
  rw [prob_compl_eq_one_sub hm] at hGc
  exact tsub_le_iff_right.2 (by rw [add_comm]; exact tsub_le_iff_right.1 hGc)

/-- **The corner events of the inner step**, read at any corner: a configuration outside the union
`B` of the eight one-arm events at the four corners `κ s₀ s₁` of `B_ρ(z)` (both colours) has no
one-arm event of either colour from `B_N(κ')` to the boundary of `B_ρ(κ')` at any corner `κ'`. -/
theorem notMem_multiArmEvent_corner_of_notMem {z : LatticeSite 2} {N ρ : ℕ}
    {κ : Bool → Bool → LatticeSite 2}
    (hκ : κ = fun s₀ s₁ => ![if s₀ then z 0 + ρ else z 0 - ρ, if s₁ then z 1 + ρ else z 1 - ρ])
    {B : Set (Config (LatticeSite 2))}
    (hB : B = ⋃ t : Bool × Bool × Bool, multiArmEvent ![t.1] (κ t.2.1 t.2.2) N ρ)
    (ω : Config (LatticeSite 2)) (hnB : ω ∉ B) (col : Bool) (κ' : LatticeSite 2)
    (hκ0 : κ' 0 = z 0 - ρ ∨ κ' 0 = z 0 + ρ) (hκ1 : κ' 1 = z 1 - ρ ∨ κ' 1 = z 1 + ρ) :
    ω ∉ multiArmEvent ![col] κ' N ρ := by
  intro hmem
  apply hnB
  rw [hB, mem_iUnion]
  rcases hκ0 with h0 | h0 <;> rcases hκ1 with h1 | h1
  · refine ⟨(col, false, false), ?_⟩
    have : κ' = κ false false := by
      rw [hκ]
      funext i
      fin_cases i <;> simp [h0, h1]
    rwa [this] at hmem
  · refine ⟨(col, false, true), ?_⟩
    have : κ' = κ false true := by
      rw [hκ]
      funext i
      fin_cases i <;> simp [h0, h1]
    rwa [this] at hmem
  · refine ⟨(col, true, false), ?_⟩
    have : κ' = κ true false := by
      rw [hκ]
      funext i
      fin_cases i <;> simp [h0, h1]
    rwa [this] at hmem
  · refine ⟨(col, true, true), ?_⟩
    have : κ' = κ true true := by
      rw [hκ]
      funext i
      fin_cases i <;> simp [h0, h1]
    rwa [this] at hmem

/-- **The inner separation step** (the internal extremities in Nolin's proof of Theorem 11, for
colour sequences without packs). For every `δ > 0` there are `0 < η ≤ 1 / 256`, an odd width
`w ≥ 7` and `N₀` such that, uniformly over the laws with crossing bounds `c` up to `L`, for
`N₀ ≤ N`, `2ρ + 1 = wN` and `ρ ≤ L`, there is an event `G` of probability at least `1 - δ`,
determined by the edges inside `B_{2ρ}(z)`, on which every family of `j` arms from `B_ρ(z)` to the
boundary of `B_R(z)` (`2ρ + 1 ≤ R`) can be rerouted into a family separated at the inner boundary
(`innerSeparatedArmEvent`, separation `4 √η N`, fences of depth `⌊√η N⌋` and half-length `⌊η N⌋`),
with the same landing positions. `G` consists of Lemma 15 in the dual lattice on four strips of
depth `N` along the sides of `B_ρ(z)` and of the absence of arms of either colour from `B_N(κ)` to
the boundary of `B_ρ(κ)` at the four corners `κ` (the one-arm bound makes these rare for `w`
large); the statement records the latter, so that no arm of any family starts near a corner. -/
theorem exists_inner_separating_event {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 256 ∧ ∃ w N₀ : ℕ, 7 ≤ w ∧ w % 2 = 1 ∧
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval)
      (L : ℕ∞), CrossingBounds q L c → ∀ (z : LatticeSite 2) (N ρ : ℕ), 2 * ρ + 1 = w * N →
      N₀ ≤ N → (ρ : ℕ∞) ≤ L → ∃ G : Set (Config (LatticeSite 2)), MeasurableSet G ∧
        (∀ ω ω' : Config (LatticeSite 2), ω ∩ {e | ∀ v ∈ e, v ∈ Icc
            (z - ((2 * ρ : ℕ) : LatticeSite 2)) (z + ((2 * ρ : ℕ) : LatticeSite 2))} =
          ω' ∩ {e | ∀ v ∈ e, v ∈ Icc
            (z - ((2 * ρ : ℕ) : LatticeSite 2)) (z + ((2 * ρ : ℕ) : LatticeSite 2))} →
          (ω ∈ G ↔ ω' ∈ G)) ∧
        1 - δ ≤ law q G ∧
        (∀ ω ∈ G, ∀ (col : Bool) (κ : LatticeSite 2), (κ 0 = z 0 - ρ ∨ κ 0 = z 0 + ρ) →
          (κ 1 = z 1 - ρ ∨ κ 1 = z 1 + ρ) → ω ∉ multiArmEvent ![col] κ N ρ) ∧
        ∀ R : ℕ, 2 * ρ + 1 ≤ R → ∀ ω ∈ multiArmEvent σ z ρ R ∩ G,
          ω ∈ innerSeparatedArmEvent σ z ρ R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊
            ⌊η * N⌋₊ := by
  classical
  -- the one-arm bounds at the corners
  obtain ⟨Ct, at₁, hat, hCt⟩ :=
    exists_law_multiArmEvent_le_rpow (![true] : Fin 1 → Bool) (col := true) ⟨0, rfl⟩ c
  obtain ⟨Cf, af, haf, hCf⟩ :=
    exists_law_multiArmEvent_le_rpow (![false] : Fin 1 → Bool) (col := false) ⟨0, rfl⟩ c
  -- the budget: `δ' = min δ 1 = 16 x`, eight corner events of probability at most `x` and four
  -- side events failing with probability at most `2 x`
  set δ' : ℝ≥0∞ := min δ 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ one_pos
  have hδ'top : δ' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set x : ℝ≥0∞ := δ' / 16 with hx
  have hxpos : 0 < x := ENNReal.div_pos_iff.2 ⟨hδ'pos.ne', by norm_num⟩
  have h16 : (16 : ℝ≥0∞) * x = δ' := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  set ε : ℝ := x.toReal with hε
  have hxtop : x ≠ ⊤ := ENNReal.div_ne_top hδ'top (by norm_num)
  have hεpos : 0 < ε := ENNReal.toReal_pos hxpos.ne' hxtop
  have hεx : ENNReal.ofReal ε = x := ENNReal.ofReal_toReal hxtop
  -- the width
  have htend : ∀ C a : ℝ, 0 < a → Filter.Tendsto (fun w : ℕ => C * ((4 : ℝ) / w) ^ a)
      Filter.atTop (nhds 0) := by
    intro C a ha
    have h1 : Filter.Tendsto (fun w : ℕ => (w : ℝ) ^ (-a)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (C * 4 ^ a)
    rw [mul_zero] at h2
    refine h2.congr' (Filter.eventually_atTop.2 ⟨1, fun w hw => ?_⟩)
    have hw' : (0 : ℝ) < w := by exact_mod_cast hw
    change C * 4 ^ a * (w : ℝ) ^ (-a) = C * (4 / (w : ℝ)) ^ a
    rw [Real.div_rpow (by norm_num) hw'.le, Real.rpow_neg hw'.le]
    ring
  obtain ⟨w₁, hw₁⟩ := Filter.eventually_atTop.1 ((htend Ct at₁ hat).eventually (Iio_mem_nhds hεpos))
  obtain ⟨w₂, hw₂⟩ := Filter.eventually_atTop.1 ((htend Cf af haf).eventually (Iio_mem_nhds hεpos))
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = 2 * (w₁ + w₂ + 4) + 1 := ⟨_, rfl⟩
  have h2x : (0 : ℝ≥0∞) < 2 * x := by positivity
  obtain ⟨η, hη, hη1, N₁, hstrip⟩ := exists_law_separable_ge_strip c w (by omega) h2x
  have hη1' : η ≤ 1 := hη1.trans (by norm_num)
  refine ⟨η, hη, hη1, w, N₁ + ⌈1 / η⌉₊ + 3, by omega, by omega, fun q L h z N ρ hρ hN hρL => ?_⟩
  -- the scales
  have hwN : 9 * N ≤ w * N := Nat.mul_le_mul_right N (by omega)
  have hN3 : 3 ≤ N := by omega
  have hNρ : 4 * N ≤ ρ := by omega
  have hNL : (N : ℕ∞) ≤ L := le_trans (Nat.cast_le.2 (by omega)) hρL
  have hηN : 1 ≤ η * N := by
    have h₁ : (1 / η) ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h₂ : ((⌈1 / η⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈1 / η⌉₊ ≤ N)
    have h₃ : 1 / η * η = 1 := by field_simp
    nlinarith
  have hsq : η ≤ Real.sqrt η := by
    have := Real.sqrt_le_one.2 hη1'
    have h₁ := Real.mul_self_sqrt hη.le
    nlinarith [Real.sqrt_nonneg η]
  have hsN : 1 ≤ Real.sqrt η * N := le_trans hηN (by gcongr)
  have hMN : ⌊Real.sqrt η * N⌋₊ ≤ N := Nat.floor_le_of_le (by
    have := Real.sqrt_le_one.2 hη1'
    have h₂ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith)
  have hKN : ⌊η * N⌋₊ ≤ N := Nat.floor_le_of_le (by
    have h₂ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith)
  have hρZ : (2 * ρ + 1 : ℤ) = (w : ℤ) * N := by exact_mod_cast hρ
  -- the dual lattice and the four frames
  obtain ⟨Φ, hΦ, hΦdet, hΦlaw⟩ := exists_measurableEquiv_dualConfig
  obtain ⟨q', hq'map, hq'CB⟩ := hΦlaw q
  have hCB' := hq'CB L c h
  obtain ⟨Fdb, Fob, hFb0, hFb1, hFbs, gb, hgb, hgob⟩ := exists_frame_bottom
  obtain ⟨Fdr, For, hFr0, hFr1, hFrs, gr, hgr, hgor⟩ := exists_frame_right
  obtain ⟨Fdt, Fot, hFt0, hFt1, hFts, gt, hgt, hgot⟩ := exists_frame_top
  obtain ⟨Fdl, Fol, hFl0, hFl1, hFls, gl, hgl, hgol⟩ := exists_frame_left
  -- the strip events in the frames
  obtain ⟨EV, hEV⟩ : ∃ EV : LatticeSite 2 → LatticeSite 2 → Set (Config (LatticeSite 2)),
      EV = fun lo hi : LatticeSite 2 => {ω | ∀ (ι : Type) [Finite ι] (σ : ι → Bool)
        (a b : ι → LatticeSite 2)
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
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l} := ⟨_, rfl⟩
  -- the box of the annulus `B_{2ρ}(z)` that determines everything
  set D : Set (Sym2 (LatticeSite 2)) := {e | ∀ v ∈ e, v ∈ Icc
    (z - ((2 * ρ : ℕ) : LatticeSite 2)) (z + ((2 * ρ : ℕ) : LatticeSite 2))} with hD
  have hDfin : D.Finite := finite_setOf_forall_mem (Set.finite_Icc _ _)
  -- a side event is determined by `D` when the frame box lies in `B_{2ρ}(z)`
  have hdetS : ∀ (Fd : zdGraph 2 ≃g zdGraph 2) (lo hi : LatticeSite 2),
      lo 1 + ⌊Real.sqrt η * N⌋₊ ≤ hi 1 →
      (∀ u ∈ Icc (![lo 0 - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊ - 1, lo 1 - 1] : LatticeSite 2)
          ![hi 0 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊ + 1, hi 1 + ⌊Real.sqrt η * N⌋₊ + 1],
        Fd.symm u ∈ Icc (z - ((2 * ρ : ℕ) : LatticeSite 2))
          (z + ((2 * ρ : ℕ) : LatticeSite 2) - 1)) →
      ∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D →
        (ω ∈ {ω | Sym2.map Fd '' Φ ω ∈ EV lo hi} ↔ ω' ∈ {ω | Sym2.map Fd '' Φ ω ∈ EV lo hi}) := by
    intro Fd lo hi hM hbox ω ω' hωω'
    have hΦω := hΦdet (z - ((2 * ρ : ℕ) : LatticeSite 2)) (z + ((2 * ρ : ℕ) : LatticeSite 2) - 1)
      ω ω' (by rwa [sub_add_cancel])
    refine image_sym2Map_mem_iff_of_inter_eq Fd.toEquiv (W := {e : Sym2 (LatticeSite 2) | ∀ v ∈ e,
      v ∈ Icc (![lo 0 - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊ - 1, lo 1 - 1] : LatticeSite 2)
        ![hi 0 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊ + 1, hi 1 + ⌊Real.sqrt η * N⌋₊ + 1]})
      (fun X X' hXX' => ?_) ?_
    · rw [hEV]
      exact ⟨fun h' => mem_separable_strip_of_inter_eq hM hXX' h',
        fun h' => mem_separable_strip_of_inter_eq hM hXX'.symm h'⟩
    · have hsub : Sym2.map Fd.toEquiv.symm '' {e : Sym2 (LatticeSite 2) | ∀ v ∈ e, v ∈ Icc
          (![lo 0 - ⌊Real.sqrt η * N⌋₊ - ⌊η * N⌋₊ - 1, lo 1 - 1] : LatticeSite 2)
          ![hi 0 + ⌊Real.sqrt η * N⌋₊ + ⌊η * N⌋₊ + 1, hi 1 + ⌊Real.sqrt η * N⌋₊ + 1]} ⊆
          {e | ∀ v ∈ e, v ∈ Icc (z - ((2 * ρ : ℕ) : LatticeSite 2))
            (z + ((2 * ρ : ℕ) : LatticeSite 2) - 1)} := by
        rintro _ ⟨e', he', rfl⟩ v hv
        obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.1 hv
        exact hbox u (he' u hu)
      ext e
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨((Set.ext_iff.1 hΦω e).1 ⟨h₁, hsub h₂⟩).1, h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨((Set.ext_iff.1 hΦω e).2 ⟨h₁, hsub h₂⟩).1, h₂⟩
  -- the four side events
  obtain ⟨Eb, hEb⟩ : ∃ E : Set (Config (LatticeSite 2)), E = {ω | Sym2.map Fdb '' Φ ω ∈
      EV ![z 0 - ρ - 1, z 1 - ρ - 1 - N] ![z 0 + ρ, z 1 - ρ - 1]} := ⟨_, rfl⟩
  obtain ⟨Er, hEr⟩ : ∃ E : Set (Config (LatticeSite 2)), E = {ω | Sym2.map Fdr '' Φ ω ∈
      EV ![z 1 - ρ - 1, -z 0 - ρ - N] ![z 1 + ρ, -z 0 - ρ]} := ⟨_, rfl⟩
  obtain ⟨Et, hEt⟩ : ∃ E : Set (Config (LatticeSite 2)), E = {ω | Sym2.map Fdt '' Φ ω ∈
      EV ![z 0 - ρ - 1, -z 1 - ρ - N] ![z 0 + ρ, -z 1 - ρ]} := ⟨_, rfl⟩
  obtain ⟨El, hEl⟩ : ∃ E : Set (Config (LatticeSite 2)), E = {ω | Sym2.map Fdl '' Φ ω ∈
      EV ![z 1 - ρ - 1, z 0 - ρ - 1 - N] ![z 1 + ρ, z 0 - ρ - 1]} := ⟨_, rfl⟩
  have hdb : ∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D → (ω ∈ Eb ↔ ω' ∈ Eb) := by
    rw [hEb]
    refine hdetS Fdb _ _ (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      fun u hu => ?_
    rw [hFbs]
    rw [mem_Icc_two_iff] at hu ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    push_cast
    omega
  have hdr : ∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D → (ω ∈ Er ↔ ω' ∈ Er) := by
    rw [hEr]
    refine hdetS Fdr _ _ (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      fun u hu => ?_
    rw [hFrs]
    rw [mem_Icc_two_iff] at hu ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    push_cast
    omega
  have hdt : ∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D → (ω ∈ Et ↔ ω' ∈ Et) := by
    rw [hEt]
    refine hdetS Fdt _ _ (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      fun u hu => ?_
    rw [hFts]
    rw [mem_Icc_two_iff] at hu ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    push_cast
    omega
  have hdl : ∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D → (ω ∈ El ↔ ω' ∈ El) := by
    rw [hEl]
    refine hdetS Fdl _ _ (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
      fun u hu => ?_
    rw [hFls]
    rw [mem_Icc_two_iff] at hu ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.add_apply,
      Pi.natCast_apply, Pi.one_apply] at hu ⊢
    push_cast
    omega
  have hmeas : ∀ E : Set (Config (LatticeSite 2)),
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D → (ω ∈ E ↔ ω' ∈ E)) → MeasurableSet E :=
    fun E hE => measurableSet_of_determined_finite hDfin fun ω =>
      hE ω (ω ∩ D) (by rw [inter_assoc, inter_self])
  -- their probabilities
  have hprof : ∀ (Fd : zdGraph 2 ≃g zdGraph 2) (f : LatticeSite 2 → LatticeSite 2),
      (∀ v, Fd.symm v = f v) →
      (fun e => q' (Sym2.map Fd.symm e)) = fun e => q' (Sym2.map f e) := fun Fd f hf =>
    funext fun e => by rw [show (⇑Fd.symm : LatticeSite 2 → LatticeSite 2) = f from funext hf]
  have hcompl : ∀ E : Set (Config (LatticeSite 2)), MeasurableSet E → 1 - 2 * x ≤ law q E →
      law q Eᶜ ≤ 2 * x := fun E hE hl => by
    rw [prob_compl_eq_one_sub hE]
    exact tsub_le_iff_right.2 (by rw [add_comm]; exact tsub_le_iff_right.1 hl)
  have hlb : law q Ebᶜ ≤ 2 * x := by
    refine hcompl _ (hmeas _ hdb) ?_
    have hid : (fun e => q' (Sym2.map id e)) = q' := funext fun e => by rw [Sym2.map_id, id]
    rw [hEb, law_frame_apply hq'map Fdb, hprof Fdb id hFbs, hEV, hid]
    exact hstrip _ L hCB' _ _ N (by simp only [Matrix.cons_val_zero]; omega)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega) (by omega) hNL
  have hlr : law q Erᶜ ≤ 2 * x := by
    refine hcompl _ (hmeas _ hdr) ?_
    rw [hEr, law_frame_apply hq'map Fdr, hprof Fdr _ hFrs, hEV]
    have hCB : CrossingBounds (fun e => q' (Sym2.map (fun v : LatticeSite 2 => ![0 - v 1, v 0]) e))
        L c := by
      have h₁ := hCB'.swap.reflect
      have h₂ : (fun e => (fun e' => q' (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e'))
          (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) =
          fun e => q' (Sym2.map (fun v : LatticeSite 2 => ![0 - v 1, v 0]) e) := by
        funext e
        simp only [Sym2.map_map]
        congr 2
      rwa [h₂] at h₁
    exact hstrip _ L hCB _ _ N (by simp only [Matrix.cons_val_zero]; omega)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega) (by omega) hNL
  have hlt : law q Etᶜ ≤ 2 * x := by
    refine hcompl _ (hmeas _ hdt) ?_
    rw [hEt, law_frame_apply hq'map Fdt, hprof Fdt _ hFts, hEV]
    exact hstrip _ L hCB'.reflect _ _ N (by simp only [Matrix.cons_val_zero]; omega)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega) (by omega) hNL
  have hll : law q Elᶜ ≤ 2 * x := by
    refine hcompl _ (hmeas _ hdl) ?_
    rw [hEl, law_frame_apply hq'map Fdl, hprof Fdl _ hFls, hEV]
    exact hstrip _ L hCB'.swap _ _ N (by simp only [Matrix.cons_val_zero]; omega)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; omega) (by omega) hNL
  -- the corner events
  obtain ⟨κ, hκ⟩ : ∃ κ : Bool → Bool → LatticeSite 2, κ = fun s₀ s₁ =>
      ![if s₀ then z 0 + ρ else z 0 - ρ, if s₁ then z 1 + ρ else z 1 - ρ] := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (Config (LatticeSite 2)),
      B = ⋃ t : Bool × Bool × Bool, multiArmEvent ![t.1] (κ t.2.1 t.2.2) N ρ := ⟨_, rfl⟩
  have hratio : ((N : ℝ) + 1) / ((ρ : ℝ) + 1) ≤ 4 / (w : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast (by omega : 0 < w))]
    have h₁ : ((w : ℝ) * N) = 2 * ρ + 1 := by exact_mod_cast hρ.symm
    have h₂ : (w : ℝ) ≤ (w : ℝ) * N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      nlinarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
    nlinarith
  have hgen : ∀ (C a : ℝ), 0 < a → C * ((4 : ℝ) / w) ^ a < ε →
      ∀ A : Set (Config (LatticeSite 2)),
      (law q).real A ≤ C * (((N : ℝ) + 1) / ((ρ : ℝ) + 1)) ^ a → law q A ≤ x := by
    intro C a ha hCa A hA
    have hmono : (((N : ℝ) + 1) / ((ρ : ℝ) + 1)) ^ a ≤ ((4 : ℝ) / w) ^ a :=
      Real.rpow_le_rpow (by positivity) hratio ha.le
    have hle : (law q).real A ≤ ε := by
      rcases le_or_gt 0 C with hC | hC
      · nlinarith [mul_le_mul_of_nonneg_left hmono hC]
      · have : 0 ≤ (((N : ℝ) + 1) / ((ρ : ℝ) + 1)) ^ a := by positivity
        nlinarith
    rw [← ofReal_measureReal, ← hεx]
    exact ENNReal.ofReal_le_ofReal hle
  have hcorP : ∀ t : Bool × Bool × Bool,
      law q (multiArmEvent ![t.1] (κ t.2.1 t.2.2) N ρ) ≤ x := by
    rintro ⟨col, s₀, s₁⟩
    cases col
    · exact hgen Cf af haf (hw₂ w (by omega)) _ (hCf q L h _ N ρ hρL)
    · exact hgen Ct at₁ hat (hw₁ w (by omega)) _ (hCt q L h _ N ρ hρL)
  have hlB : law q B ≤ 8 * x := by
    rw [hB]
    calc law q (⋃ t : Bool × Bool × Bool, multiArmEvent ![t.1] (κ t.2.1 t.2.2) N ρ)
        ≤ ∑ t : Bool × Bool × Bool, law q (multiArmEvent ![t.1] (κ t.2.1 t.2.2) N ρ) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _t : Bool × Bool × Bool, x := Finset.sum_le_sum fun t _ => hcorP t
      _ = 8 * x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
            Fintype.card_bool, nsmul_eq_mul]
          norm_num
  have hBm : MeasurableSet B := by
    rw [hB]
    exact MeasurableSet.iUnion fun t => measurableSet_multiArmEvent _ _ _ _
  have hdB : ∀ ω ω' : Config (LatticeSite 2), ω ∩ D = ω' ∩ D → (ω ∈ B ↔ ω' ∈ B) := by
    intro ω ω' hωω'
    rw [hB, mem_iUnion, mem_iUnion]
    refine exists_congr fun t => mem_multiArmEventTo_iff_of_inter_eq (fun v hv => ?_) hωω'
    have := mem_Icc_two_iff.1 hv.1
    rw [mem_Icc_two_iff]
    rw [hκ] at this
    obtain ⟨col, s₀, s₁⟩ := t
    cases s₀ <;> cases s₁ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢ <;> push_cast <;> omega
  -- no arm at a corner off `B`
  have hcorG : ∀ ω : Config (LatticeSite 2), ω ∉ B → ∀ (col : Bool) (κ' : LatticeSite 2),
      (κ' 0 = z 0 - ρ ∨ κ' 0 = z 0 + ρ) → (κ' 1 = z 1 - ρ ∨ κ' 1 = z 1 + ρ) →
      ω ∉ multiArmEvent ![col] κ' N ρ := notMem_multiArmEvent_corner_of_notMem hκ hB
  -- the separating event
  refine ⟨Bᶜ ∩ (Eb ∩ Er ∩ Et ∩ El), hBm.compl.inter ((((hmeas _ hdb).inter (hmeas _ hdr)).inter
    (hmeas _ hdt)).inter (hmeas _ hdl)), fun ω ω' hωω' => ?_, ?_,
    fun ω hω => hcorG ω hω.1, fun R hR ω hω => ?_⟩
  · simp only [mem_inter_iff, mem_compl_iff]
    rw [hdB ω ω' hωω', hdb ω ω' hωω', hdr ω ω' hωω', hdt ω ω' hωω', hdl ω ω' hωω']
  · have hGm : MeasurableSet (Bᶜ ∩ (Eb ∩ Er ∩ Et ∩ El)) := hBm.compl.inter
      ((((hmeas _ hdb).inter (hmeas _ hdr)).inter (hmeas _ hdt)).inter (hmeas _ hdl))
    exact le_trans (tsub_le_tsub_left (min_le_left _ _) _)
      (one_sub_le_measure_compl_inter hGm hlB hlb hlr hlt hll h16)
  · obtain ⟨hA, hnB, ⟨⟨⟨hb, hr⟩, ht⟩, hl⟩⟩ := hω
    rw [hEb, mem_ofPred_eq, hEV] at hb
    rw [hEr, mem_ofPred_eq, hEV] at hr
    rw [hEt, mem_ofPred_eq, hEV] at ht
    rw [hEl, mem_ofPred_eq, hEV] at hl
    obtain ⟨hYb, hYdb⟩ := frame_relations hΦ Fdb Fob gb hgb hgob ω
    obtain ⟨hYr, hYdr⟩ := frame_relations hΦ Fdr For gr hgr hgor ω
    obtain ⟨hYt, hYdt⟩ := frame_relations hΦ Fdt Fot gt hgt hgot ω
    obtain ⟨hYl, hYdl⟩ := frame_relations hΦ Fdl Fol gl hgl hgol ω
    refine mem_innerSeparatedArmEvent_of_frames hσ (by omega) (by omega) hR hsN
      (fun c => cond c Fob Fdb) (fun c => cond c For Fdr) (fun c => cond c Fot Fdt)
      (fun c => cond c Fol Fdl) hFb0 hFb1 hFr0 hFr1 hFt0 hFt1 hFl0 hFl1 hYb hYdb hYr hYdr hYt
      hYdt hYl hYdl rfl rfl rfl rfl rfl rfl rfl rfl hb hr ht hl (hcorG ω hnB) hA

/-- **Separation of arms at the inner boundary of an annulus** (the internal extremities in Nolin's
proof of Theorem 11, for colour sequences without packs). Under the constants of
`exists_inner_separating_event`, for `2ρ + 1 = wN`, `N₀ ≤ N`, `2ρ + 2 ≤ R` and `ρ ≤ L`: the
probability that the `j`-arm event from `B_ρ(z)` to the boundary of `B_R(z)` occurs but the arms
cannot be chosen separated at the inner boundary is at most `δ` times the probability of the
`j`-arm event from `B_{2ρ+1}(z)` to the boundary of `B_R(z)`. The separating event depends only on
the edges inside `B_{2ρ}(z)`, the latter arm event only on the edges outside, and it contains the
former. -/
theorem exists_law_multiArmEvent_diff_innerSeparated_le {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ w N₀ : ℕ, 7 ≤ w ∧ w % 2 = 1 ∧
      ∀ (q : Sym2 (LatticeSite 2) → unitInterval)
      (L : ℕ∞), CrossingBounds q L c → ∀ (z : LatticeSite 2) (N ρ R : ℕ), 2 * ρ + 1 = w * N →
      N₀ ≤ N → 2 * ρ + 2 ≤ R → (ρ : ℕ∞) ≤ L →
      law q (multiArmEvent σ z ρ R \ innerSeparatedArmEvent σ z ρ R (4 * Real.sqrt η * N)
          ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊) ≤
        δ * law q (multiArmEvent σ z (2 * ρ + 1) R) := by
  obtain ⟨η, hη, hη1, w, N₀, hw, hwo, hG⟩ := exists_inner_separating_event σ hσ c hδ
  refine ⟨η, hη, le_trans hη1 (by norm_num), w, N₀, hw, hwo,
    fun q L h z N ρ R hρ hN hR hρL => ?_⟩
  obtain ⟨G, hGm, hGd, hGl, -, hGsep⟩ := hG q L h z N ρ hρ hN hρL
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
        exact ⟨multiArmEvent_subset_of_le (by omega) le_rfl (by omega) hA,
          fun hωG => hnot (hGsep R (by omega) ω ⟨hA, hωG⟩)⟩
    _ = law q (multiArmEvent σ z (2 * ρ + 1) R) * law q Gᶜ := hind
    _ ≤ law q (multiArmEvent σ z (2 * ρ + 1) R) * δ := by gcongr
    _ = δ * law q (multiArmEvent σ z (2 * ρ + 1) R) := mul_comm _ _

end PercLib.Models.Planar
