/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-23. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (proof of Theorem 11: the arms after the
separation step must stay disjoint and in order).
-/
module

public import PercLib.Models.Planar.Arms.MultiArmBasics

/-!
# Sectors of a family of arms without packs

Let `γ` be a disjoint family of arms of colours `σ` from `B_r(z)` to the boundary of a box, landing
in counterclockwise order. The colour sequence has **no pack** when cyclically consecutive arms have
different colours. Then the arms of one colour cut the annulus into sectors, one for each arm of the
other colour, and an arm of one colour cannot cross the arms of the other colour. In terms of
positions: an arm with the inner position of arm `i` lands between the landing positions of the two
neighbours of `i`, and two arms of one colour with the inner positions of two different arms of that
colour cannot meet, since joining them at a common vertex or face would give an arm in two sectors
at once.

So, without packs, **any** family of arms with the inner positions of `γ` is again disjoint and
lands in the same counterclockwise order. This is the barrier argument behind the separation of arms
(Nolin's proof of Theorem 11, which reroutes the final pieces of the arms without checking them
against the other arms): after rerouting, only the arm property and the inner positions need to be
checked.

## Main results

* `sbtw_apply_finRotate_apply`: in a family in cyclic order, an element, the next one and any third
  one are in cyclic order.
* `SimpleGraph.Walk.IsCrossing.append_of_append`, `IsArm.append_of_append`: joining the first part
  of one crossing (arm) to the last part of another at a common vertex gives a crossing (arm).
* `sbtw_landingPos_iff_of_innerPos_eq`: two arms of one colour with the same inner position lie on
  the same side of any two disjoint arms of the other colour.
* `ArmsDisjoint.of_innerPos_eq` (the barrier) and `sbtw_landingPos_of_innerPos_eq`: without packs,
  a family of arms with the inner positions of a disjoint family in counterclockwise order is
  disjoint and lands in the same order.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

/-! ### Cyclic order along `Fin n` -/

/-- **The next element in a cyclic order.** If `f` takes increasing triples of `Fin n` to triples
in strict cyclic order, then `f x`, `f` of the next index `finRotate n x` and `f w` for any other
index `w` are in strict cyclic order. -/
theorem sbtw_apply_finRotate_apply {α : Type*} [CircularOrder α] {n : ℕ} {f : Fin n → α}
    (hf : ∀ i k l, i < k → k < l → sbtw (f i) (f k) (f l)) {x w : Fin n} (hwx : w ≠ x)
    (hw : w ≠ finRotate n x) : sbtw (f x) (f (finRotate n x)) (f w) := by
  rcases n with _ | m
  · exact x.elim0
  by_cases hx : x = Fin.last m
  · subst hx
    rw [finRotate_last] at hw ⊢
    have h0 : (0 : Fin (m + 1)) < w := Fin.pos_iff_ne_zero.2 hw
    have hl : w < Fin.last m := lt_of_le_of_ne (Fin.le_last w) hwx
    exact sbtw_cyclic_right (hf 0 w (Fin.last m) h0 hl)
  · have hlt : x.val < m := Fin.val_lt_last hx
    have hval : (finRotate (m + 1) x).val = x.val + 1 := by
      have := finRotate_of_lt hlt
      rw [Fin.eta] at this
      rw [this]
    have hw' : w.val ≠ x.val + 1 := fun h => hw (Fin.ext (by rw [hval, h]))
    have hwx' : w.val ≠ x.val := fun h => hwx (Fin.ext h)
    rcases lt_or_gt_of_ne hwx' with h | h
    · exact sbtw_cyclic_left (hf w x _ h (by rw [Fin.lt_def, hval]; omega))
    · exact hf x _ w (by rw [Fin.lt_def, hval]; omega) (by rw [Fin.lt_def, hval]; omega)

/-! ### Joining crossings at a common vertex -/

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {S T : Set V}

/-- **Joining two crossings.** If `q.append s` and `q'.append s'` both cross from `S` out of `T`,
so does `q.append s'`: the first part of one crossing, up to a vertex it shares with the other,
followed by the last part of the other. -/
theorem IsCrossing.append_of_append {u v u' v' x : V} {q : G.Walk u x} {s : G.Walk x v}
    {q' : G.Walk u' x} {s' : G.Walk x v'} (h : (q.append s).IsCrossing S T)
    (h' : (q'.append s').IsCrossing S T) : (q.append s').IsCrossing S T := by
  refine ⟨h.start_mem, fun w hw => ?_, h'.end_notMem, fun w hw => ?_⟩
  · rw [tail_support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.notMem_of_mem_tail w (by
        rw [tail_support_append]
        exact List.mem_append_left _ hw)
    · exact h'.notMem_of_mem_tail w (by
        rw [tail_support_append]
        exact List.mem_append_right _ hw)
  · rw [support_append_eq_support_dropLast_append,
      List.dropLast_append_of_ne_nil (support_ne_nil s'), List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.mem_of_mem_dropLast w (by
        rw [support_append_eq_support_dropLast_append,
          List.dropLast_append_of_ne_nil (support_ne_nil s)]
        exact List.mem_append_left _ hw)
    · exact h'.mem_of_mem_dropLast w (by
        rw [support_append_eq_support_dropLast_append,
          List.dropLast_append_of_ne_nil (support_ne_nil s')]
        exact List.mem_append_right _ hw)

end SimpleGraph.Walk

namespace PercLib.Models.Planar

variable {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r : ℕ} {lo hi : LatticeSite 2}

/-- **Joining two arms.** If `q.append s` and `q'.append s'` are arms of colour `c`, so is
`q.append s'`. -/
theorem IsArm.append_of_append {c : Bool} {a b a' b' x : LatticeSite 2}
    {q : (zdGraph 2).Walk a x} {s : (zdGraph 2).Walk x b} {q' : (zdGraph 2).Walk a' x}
    {s' : (zdGraph 2).Walk x b'} (h : IsArm ω c z r lo hi (q.append s))
    (h' : IsArm ω c z r lo hi (q'.append s')) : IsArm ω c z r lo hi (q.append s') := by
  have hq : ∀ e ∈ q.edges, e ∈ (q.append s).edges := fun e he => by
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ he
  have hs : ∀ e ∈ s'.edges, e ∈ (q'.append s').edges := fun e he => by
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he
  cases c
  · have h₁ : IsDualArm ω z r lo hi (q.append s) := h
    have h₂ : IsDualArm ω z r lo hi (q'.append s') := h'
    refine ⟨h₁.isCrossing.append_of_append h₂.isCrossing, fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact h₁.mem_of_mem_edges e (hq e he)
    · exact h₂.mem_of_mem_edges e (hs e he)
  · have h₁ : IsOpenArm ω z r lo hi (q.append s) := h
    have h₂ : IsOpenArm ω z r lo hi (q'.append s') := h'
    refine ⟨h₁.isCrossing.append_of_append h₂.isCrossing, fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact h₁.mem_of_mem_edges e (hq e he)
    · exact h₂.mem_of_mem_edges e (hs e he)

/-- **The last face of a dual arm determines its last dual edge.** Two dual arms to the boundary of
`Icc lo hi` that end at the same face end with the same dual edge: the last face lies outside the
faces of the box and is adjacent to exactly one of them. -/
theorem IsDualArm.penultimate_eq {a b a' b' : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    {γ' : (zdGraph 2).Walk a' b'} (h : IsDualArm ω z r lo hi γ) (h' : IsDualArm ω z r lo hi γ')
    (hγ : ¬γ.Nil) (hγ' : ¬γ'.Nil) (hb : b = b') : γ.penultimate = γ'.penultimate := by
  subst hb
  have hp := h.isCrossing.penultimate_mem hγ
  have hp' := h'.isCrossing.penultimate_mem hγ'
  have hb := h.isCrossing.end_notMem
  have ha := (zdGraph_two_adj_iff _ _).1 (γ.adj_penultimate hγ)
  have ha' := (zdGraph_two_adj_iff _ _).1 (γ'.adj_penultimate hγ')
  rw [mem_Icc_two_iff] at hp hp' hb
  simp only [Pi.sub_apply, Pi.one_apply] at hp hp' hb
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> omega

/-! ### Sectors -/

section Sectors

variable {j : ℕ} {σ : Fin j → Bool} {a b : Fin j → LatticeSite 2}
  {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}

/-- **Sectors.** Let `γ` be a disjoint family of arms and `k ≠ l` two of its arms of one colour.
Two arms of the other colour with the same inner position land on the same side of the arms `k`
and `l`: the landing positions of the three arms are in the same cyclic order. -/
theorem sbtw_landingPos_iff_of_innerPos_eq (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ) {k l : Fin j} (hkl : k ≠ l)
    (hσkl : σ k = σ l) {c : Bool} (hc : c ≠ σ k) {a₁ b₁ a₂ b₂ : LatticeSite 2}
    {W₁ : (zdGraph 2).Walk a₁ b₁} {W₂ : (zdGraph 2).Walk a₂ b₂} (h₁ : IsArm ω c z r lo hi W₁)
    (h₂ : IsArm ω c z r lo hi W₂) (hin : innerPos z r c W₁ = innerPos z r c W₂) :
    sbtw (landingPos lo hi c W₁) (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l)) ↔
      sbtw (landingPos lo hi c W₂) (landingPos lo hi (σ k) (γ k))
        (landingPos lo hi (σ l) (γ l)) := by
  -- order invariance for the three arms `W, γ k, γ l`
  have key : ∀ {a₀ b₀ : LatticeSite 2} (W : (zdGraph 2).Walk a₀ b₀), IsArm ω c z r lo hi W →
      (sbtw (innerPos z r c W) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) ↔
        sbtw (landingPos lo hi c W) (landingPos lo hi (σ k) (γ k))
          (landingPos lo hi (σ l) (γ l))) := by
    intro a₀ b₀ W hW
    let A : Fin 3 → LatticeSite 2 := ![a₀, a k, a l]
    let B : Fin 3 → LatticeSite 2 := ![b₀, b k, b l]
    let F : ∀ t, (zdGraph 2).Walk (A t) (B t) :=
      @Fin.cases 2 (fun t => (zdGraph 2).Walk (A t) (B t)) W
        (@Fin.cases 1 (fun t => (zdGraph 2).Walk (A t.succ) (B t.succ)) (γ k)
          (@Fin.cases 0 (fun t => (zdGraph 2).Walk (A t.succ.succ) (B t.succ.succ)) (γ l)
            fun t => t.elim0))
    have hF : ∀ t, IsArm ω (![c, σ k, σ l] t) z r lo hi (F t) := by
      intro t
      fin_cases t
      · exact hW
      · exact hγ k
      · exact hγ l
    have hlk : σ l ≠ c := fun h => hc (h ▸ hσkl).symm
    have hdF : ArmsDisjoint ![c, σ k, σ l] F := by
      refine ⟨fun t u htu ht hu v hv hv' => ?_, fun t u htu ht hu v hv hv' => ?_⟩
      · fin_cases t <;> fin_cases u
        · exact htu rfl
        · exact hc (ht.trans hu.symm)
        · exact hlk (hu.trans ht.symm)
        · exact hc (hu.trans ht.symm)
        · exact htu rfl
        · exact hd.1 k l hkl ht hu v hv hv'
        · exact hlk (ht.trans hu.symm)
        · exact hd.1 l k hkl.symm ht hu v hv hv'
        · exact htu rfl
      · fin_cases t <;> fin_cases u
        · exact htu rfl
        · exact hc (ht.trans hu.symm)
        · exact hlk (hu.trans ht.symm)
        · exact hc (hu.trans ht.symm)
        · exact htu rfl
        · exact hd.2 k l hkl ht hu v hv hv'
        · exact hlk (ht.trans hu.symm)
        · exact hd.2 l k hkl.symm ht hu v hv hv'
        · exact htu rfl
    exact sbtw_innerPos_iff_sbtw_landingPos hB hF hdF 0 1 2
  rw [← key W₁ h₁, ← key W₂ h₂, hin]

/-- **Barrier.** Let `γ` be a disjoint family of arms landing in counterclockwise order, with no two
cyclically consecutive arms of the same colour (or at most one arm). Then every family of arms with
the colours and the inner positions of `γ` is disjoint. -/
theorem ArmsDisjoint.of_innerPos_eq (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
      (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l)))
    {a' b' : Fin j → LatticeSite 2} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (hγ' : ∀ i, IsArm ω (σ i) z r lo hi (γ' i))
    (hin : ∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) : ArmsDisjoint σ γ' := by
  rcases hσ with hj | hσ
  · exact armsDisjoint_of_subsingleton hj σ γ'
  -- an arm with the inner position of `γ i` does not land where `γ' i'` lands, for `i ≠ i'` of
  -- one colour
  have key : ∀ i i', i ≠ i' → σ i = σ i' → ∀ {x y : LatticeSite 2} (W : (zdGraph 2).Walk x y),
      IsArm ω (σ i) z r lo hi W → innerPos z r (σ i) W = innerPos z r (σ i) (γ i) →
      landingPos lo hi (σ i) W ≠ landingPos lo hi (σ i') (γ' i') := by
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
    -- the sector of `i` and the sector of `i'`
    have h₁ := sbtw_apply_finRotate_apply (f := fun i => landingPos lo hi (σ i) (γ i)) ho hli
      hkl.symm
    have h₂ := sbtw_apply_finRotate_apply (f := fun i => landingPos lo hi (σ i) (γ i)) ho hki' hkl
    have h₃ : ¬sbtw (landingPos lo hi (σ i') (γ i')) (landingPos lo hi (σ k) (γ k))
        (landingPos lo hi (σ l) (γ l)) := fun h => sbtw_asymm h (sbtw_cyclic_left h₂)
    have hW₁ := sbtw_landingPos_iff_of_innerPos_eq hB hγ hd hkl hσkl hk.symm hW (hγ i) hWin
    have hW₂ := sbtw_landingPos_iff_of_innerPos_eq hB hγ hd hkl hσkl
      (fun h => hk (h.symm.trans hσii'.symm)) (hγ' i') (hγ i') (hin i')
    exact h₃ (hW₂.1 (heq ▸ hW₁.2 h₁))
  refine ⟨fun i i' hii' hσi hσi' v hv hv' => ?_, fun i i' hii' hσi hσi' v hv hv' => ?_⟩
  · -- open arms: join `γ' i` up to `v` to `γ' i'` from `v`
    have hσ' : σ i = σ i' := hσi.trans hσi'.symm
    have hvs := List.mem_of_mem_tail hv
    have h₁ := hγ' i
    have h₂ := hγ' i'
    rw [← SimpleGraph.Walk.take_spec (γ' i) hvs] at h₁
    rw [← SimpleGraph.Walk.take_spec (γ' i') hv', ← hσ'] at h₂
    have hW := IsArm.append_of_append h₁ h₂
    have hc : IsOpenArm ω z r lo hi (γ' i) := by
      have := hγ' i
      rw [hσi] at this
      exact this
    have hva : v ≠ a' i := fun h =>
      hc.isCrossing.notMem_of_mem_tail v hv (h ▸ hc.isCrossing.start_mem)
    have hq : ¬((γ' i).takeUntil v hvs).Nil := fun hn => hva hn.eq.symm
    refine key i i' hii' hσ' _ hW ?_ ?_
    · rw [innerPos_append _ hq, ← hin i]
      conv_rhs => rw [← SimpleGraph.Walk.take_spec (γ' i) hvs, innerPos_append _ hq]
    · rw [← hσ', hσi, landingPos_true, landingPos_true]
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
    by_cases hvb : v = b' i'
    · -- both arms end at the face `v`, so they end with the same dual edge
      have hvb' : v = b' i := hc.isCrossing.eq_end_of_notMem hv
        (by rw [hvb]; exact hc'.isCrossing.end_notMem)
      have hpen := hc.penultimate_eq hc' ((hγ' i).not_nil hB) ((hγ' i').not_nil hB)
        (hvb'.symm.trans hvb)
      refine key i i' hii' hσ' (γ' i) (hγ' i) (hin i) ?_
      rw [← hσ', hσi, landingPos_false, landingPos_false, hpen, ← hvb', hvb]
    · -- join `γ' i` up to `v` to `γ' i'` from `v`
      have h₁ := hγ' i
      have h₂ := hγ' i'
      rw [← SimpleGraph.Walk.take_spec (γ' i) hv] at h₁
      rw [← SimpleGraph.Walk.take_spec (γ' i') hv', ← hσ'] at h₂
      have hW := IsArm.append_of_append h₁ h₂
      have hs : ¬((γ' i').dropUntil v hv').Nil := fun hn => hvb hn.eq
      refine key i i' hii' hσ' _ hW ?_ ?_
      · rw [← hin i, hσi, innerPos_false, innerPos_false]
      · rw [landingPos_append _ hs, hσ']
        conv_rhs => rw [← SimpleGraph.Walk.take_spec (γ' i') hv', landingPos_append _ hs]

/-- **Order.** Under the hypotheses of `ArmsDisjoint.of_innerPos_eq`, every family of arms with the
colours and the inner positions of `γ` lands in the same counterclockwise order. -/
theorem sbtw_landingPos_of_innerPos_eq (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    (hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1))
    (hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)) (hd : ArmsDisjoint σ γ)
    (ho : ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
      (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l)))
    {a' b' : Fin j → LatticeSite 2} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (hγ' : ∀ i, IsArm ω (σ i) z r lo hi (γ' i))
    (hin : ∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) (i k l : Fin j)
    (hik : i < k) (hkl : k < l) :
    sbtw (landingPos lo hi (σ i) (γ' i)) (landingPos lo hi (σ k) (γ' k))
      (landingPos lo hi (σ l) (γ' l)) := by
  have hd' := ArmsDisjoint.of_innerPos_eq hσ hB hγ hd ho hγ' hin
  rw [← sbtw_innerPos_iff_sbtw_landingPos hB hγ' hd', hin, hin, hin,
    sbtw_innerPos_iff_sbtw_landingPos hB hγ hd]
  exact ho i k l hik hkl

end Sectors

end PercLib.Models.Planar
