/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4, Lemma 15 (local separation, p. 1579), protection
of the greedy crossings in its proof.
-/
module

public import PercLib.Models.Planar.Arms.SeparationSurgery

/-!
# Local separation of crossings: protection of the greedy tips

Nolin's local separation lemma protects the top end of each greedy crossing: with high
probability no other crossing, of either colour, lands close to it on its right. This file proves
the deterministic half of that protection for the greedy exploration of `Separation.lean`, for
any configuration `G` and any box `Icc lo hi`.

* **Clean greedy crossings.** The choice rule can take paths that meet the bottom row only at
  their start and the top row only at their end (`exists_crossing_choice_clean`).
* **Top separation.** A clean bottom-top walk `τ` ending at `d` separates the faces of the dual
  box joined to its left column from the top row on the right of `d`: no such face is joined,
  without crossing `τ`, to a face of the top row at or right of `d` (`not_localConn_top`), and
  a walk from the top row right of `d` to a vertex with such a face meets `τ`
  (`exists_mem_support_of_lt_top`).
* **Order and freshness.** The tips of the greedy crossings increase from left to right
  (`lt_of_exploration`). A later greedy crossing has no vertex at a face explored earlier
  (`not_le_of_mem_support_of_exploration`), and a walk of faces with dual edges crossing only
  edges closed in `G`, joined to the top row at or right of a tip, avoids the faces explored up
  to that tip (`notMem_of_localConn_of_exploration`). So both meet only fresh edges, on which the
  exploration up to that tip has not looked.
* **Blocking.** At scale `s` around a tip, the three strips of the annulus `s ≤ ‖·‖∞ ≤ 3s`
  inside the box carry no short crossing of the fresh part of `G` (explored edges removed) or of
  the fresh part of the dual configuration (explored edges added to `G`). Then no later greedy
  crossing lands within `s` on the right of the tip (`lt_sub_of_exploration`), and no walk of
  faces crossing only closed edges of `G` lands there either
  (`false_of_localConn_of_exploration`). Near the two top corners the same strips, for `G` itself,
  keep every crossing of `G` away (`false_of_le_add_corner_right`, `false_of_le_add_corner_left`).

The strips are the four strips of `notMem_localConn_of_notMem_crossing` translated to the tip
(`notMem_localConn_of_notMem_crossing_add`); the fourth strip lies outside the box. The events
"no short crossing of the fresh part" are determined by the edges the exploration has not looked
at, and they contain the standard circuit events, so their probability is bounded below by the
crossing bounds without any extraction of paths.

## Main results

* `exists_crossing_choice_clean`: a choice rule with clean paths.
* `not_localConn_top`, `exists_mem_support_of_lt_top`: top separation, dual and primal forms.
* `lt_of_exploration`: the greedy tips increase.
* `lt_sub_of_exploration`: same-colour blocking.
* `false_of_localConn_of_exploration`: blocking of the other colour.
* `false_of_le_add_corner_right`, `false_of_le_add_corner_left`: blocking at the top corners.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- **Cleaning a walk.** A walk from a vertex satisfying `P` to a vertex satisfying `Q` contains a
path from a vertex satisfying `P` to a vertex satisfying `Q` that meets `P` only at its start and
`Q` only at its end. -/
theorem exists_isPath_clean (P Q : V → Prop) {u v : V} (p : G.Walk u v) (hu : P u) (hv : Q v) :
    ∃ (a b : V) (q : G.Walk a b), q.IsPath ∧ P a ∧ Q b ∧ (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ e ∈ q.edges, e ∈ p.edges) ∧ (∀ x ∈ q.support, P x → x = a) ∧
      ∀ x ∈ q.support, Q x → x = b := by
  obtain ⟨b, q₁, s₁, hqs₁, hb, hq₁⟩ := exists_append_eq_of_notMem (T := {x | ¬Q x}) p.bypass
    (by simpa using hv)
  have hP₁ : q₁.IsPath := by
    have h := p.bypass_isPath
    rw [← hqs₁] at h
    exact h.of_append_left
  obtain ⟨a, q₂, s₂, hqs₂, ha, hq₂⟩ := exists_append_eq_of_notMem (T := {x | ¬P x}) q₁.reverse
    (by simpa using hu)
  have hP₂ : q₂.IsPath := by
    have h := hP₁.reverse
    rw [← hqs₂] at h
    exact h.of_append_left
  have hsub₂ : ∀ x ∈ q₂.support, x ∈ q₁.support := fun x hx => by
    have : x ∈ (q₂.append s₂).support := (mem_support_append_iff q₂ s₂).2 (Or.inl hx)
    rwa [hqs₂, support_reverse, List.mem_reverse] at this
  have hsub₁ : ∀ x ∈ q₁.support, x ∈ p.support := fun x hx => by
    have : x ∈ (q₁.append s₁).support := (mem_support_append_iff q₁ s₁).2 (Or.inl hx)
    rw [hqs₁] at this
    exact p.support_bypass_subset_support this
  have hesub₂ : ∀ e ∈ q₂.edges, e ∈ q₁.edges := fun e he => by
    have : e ∈ (q₂.append s₂).edges := by
      rw [edges_append]
      exact List.mem_append_left _ he
    rwa [hqs₂, edges_reverse, List.mem_reverse] at this
  have hesub₁ : ∀ e ∈ q₁.edges, e ∈ p.edges := fun e he => by
    have : e ∈ (q₁.append s₁).edges := by
      rw [edges_append]
      exact List.mem_append_left _ he
    rw [hqs₁] at this
    exact p.edges_bypass_subset_edges this
  refine ⟨a, b, q₂.reverse, hP₂.reverse, by simpa using ha, by simpa using hb, fun x hx => ?_,
    fun e he => ?_, fun x hx hPx => ?_, fun x hx hQx => ?_⟩
  · rw [support_reverse, List.mem_reverse] at hx
    exact hsub₁ x (hsub₂ x hx)
  · rw [edges_reverse, List.mem_reverse] at he
    exact hesub₁ e (hesub₂ e he)
  · rw [support_reverse, List.mem_reverse] at hx
    by_contra hne
    exact hq₂ x (mem_dropLast_support_of_ne hx hne) hPx
  · rw [support_reverse, List.mem_reverse] at hx
    by_contra hne
    exact hq₁ x (mem_dropLast_support_of_ne (hsub₂ x hx) hne) hQx

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Top separation -/

/-- **No crossing of a strip outside the support of a configuration.** If every edge of `ζ` has
its ends strictly below or strictly above the range `[lo' i, hi' i]` in direction `i`, then `ζ`
does not cross the box `Icc lo' hi'` in direction `i`. -/
theorem notMem_crossing_of_forall {ζ : Config (LatticeSite 2)} {i : Fin 2}
    {lo' hi' : LatticeSite 2} (h : lo' i < hi' i)
    (hζ : ∀ e ∈ ζ, ∀ x ∈ e, x i < lo' i ∨ hi' i < x i) : ζ ∉ crossing i lo' hi' := by
  rintro ⟨a, -, ha, b, -, hb, hab⟩
  obtain ⟨p, -, hpE⟩ := exists_walk_of_mem_localConn hab
  cases p with
  | nil => omega
  | cons hadj q =>
    rename_i v'
    have hmem : s(a, v') ∈ (SimpleGraph.Walk.cons hadj q).edges := by simp
    have := hζ _ (hpE _ hmem) a (Sym2.mem_mk_left _ _)
    omega

/-- **Top separation, dual form.** Let `τ` be a walk in the box `Icc lo hi` from its bottom row to
its top row that meets the top row only at its end `d`. No dual path of the dual box crossing no
edge of `τ` joins its left column to a face of its top row at or right of `d`. -/
theorem not_localConn_top {lo hi : LatticeSite 2} (h1 : lo 1 < hi 1) {c d : LatticeSite 2}
    (τ : (zdGraph 2).Walk c d) (hτ : ∀ v ∈ τ.support, v ∈ Icc lo hi) (hc : c 1 = lo 1)
    (hd : d 1 = hi 1) (htop : ∀ v ∈ τ.support, v 1 = hi 1 → v = d) {f₀ f : LatticeSite 2}
    (hf₀ : f₀ 0 = lo 0 - 1) (hf : f 1 = hi 1 - 1) (hdf : d 0 ≤ f 0) :
    dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∉
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f := by
  intro hpath
  have hcR := hτ c τ.start_mem_support
  have hle : lo ≤ hi := (mem_Icc.1 hcR).1.trans (mem_Icc.1 hcR).2
  have hV : {e | e ∈ τ.edges} ∈ crossing 1 lo hi :=
    ⟨c, hcR, hc, d, hτ d τ.end_mem_support, hd, mem_localConn_edges_of_walk τ hτ⟩
  have hfT := mem_Icc_two_iff.1 hpath.2.1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfT
  -- the top row of faces from the right column to `f`
  obtain ⟨ρ, hρ, hρe⟩ := exists_walk_row (hi 1 - 1) (show f 0 ≤ hi 0 by omega)
  have hrow : dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
        ![hi 0, hi 1 - 1] ![f 0, hi 1 - 1] := by
    refine mem_localConn_of_walk ρ (fun v hv => ?_) fun e he => ?_
    · obtain ⟨h₁, h₂, h₃⟩ := hρ v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · obtain ⟨t, ht1, ht2, rfl⟩ := hρe e he
      -- the dual edge crosses the vertical edge below the top row point `(t + 1, hi 1)`
      have hv : s(![t + 1, hi 1 - 1], ![t + 1, hi 1 - 1 + 1]) ∈ (zdGraph 2).edgeSet :=
        vertical_mem_edgeSet _ _
      have hdual : dualEdge s(![t + 1, hi 1 - 1], ![t + 1, hi 1 - 1 + 1]) =
          s(![t, hi 1 - 1], ![t + 1, hi 1 - 1]) := by
        rw [dualEdge_vertical, Sym2.eq_swap, add_sub_cancel_right]
      rw [← hdual, dualEdge_mem_dualConfig_iff hv]
      intro hmem
      have hd' := htop _ (τ.snd_mem_support_of_mem_edges hmem) (by simp)
      have h0 := congrFun hd' 0
      simp only [Matrix.cons_val_zero] at h0
      omega
  have hf' : f = ![f 0, hi 1 - 1] := eq_vec_two_iff.2 ⟨rfl, hf⟩
  rw [hf'] at hpath
  have hH : dualConfig {e | e ∈ τ.edges} ∈ crossing 0 ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1] := by
    refine ⟨f₀, hpath.1, by simpa using hf₀, ![hi 0, hi 1 - 1], ?_, by simp, ?_⟩
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [localConn_comm] at hrow
      exact localConn_trans hpath hrow
  exact (mem_crossing_one_iff_dualConfig_notMem_crossing_zero hle _).1 hV hH

/-- **Top separation, primal form.** Let `τ` be a walk in the box from its bottom row to its top
row that meets the top row only at its end `d`, and `σ` a walk in the box from a point `s` of the
top row strictly right of `d` to a vertex `x`. If a face at `x` is joined to the left column of
the dual box by dual edges crossing no edge of `τ`, then `σ` meets `τ`. -/
theorem exists_mem_support_of_lt_top {lo hi : LatticeSite 2} (h1 : lo 1 < hi 1)
    {c d : LatticeSite 2} (τ : (zdGraph 2).Walk c d) (hτ : ∀ v ∈ τ.support, v ∈ Icc lo hi)
    (hc : c 1 = lo 1) (hd : d 1 = hi 1) (htop : ∀ v ∈ τ.support, v 1 = hi 1 → v = d)
    {s x : LatticeSite 2} (σ : (zdGraph 2).Walk s x) (hσ : ∀ v ∈ σ.support, v ∈ Icc lo hi)
    (hs : s 1 = hi 1) (hds : d 0 < s 0) {f₀ f₁ : LatticeSite 2} (hf₀ : f₀ 0 = lo 0 - 1)
    (hf₁ : x 0 - 1 ≤ f₁ 0 ∧ f₁ 0 ≤ x 0 ∧ x 1 - 1 ≤ f₁ 1 ∧ f₁ 1 ≤ x 1)
    (hpath : dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) f₀ f₁) :
    ∃ v ∈ σ.support, v ∈ τ.support := by
  have hsR := mem_Icc_two_iff.1 (hσ s σ.start_mem_support)
  obtain ⟨ρ, hρ, -⟩ := exists_walk_row (hi 1) (show s 0 ≤ hi 0 by omega)
  have hs' : (![s 0, hi 1] : LatticeSite 2) = s := ((eq_vec_two_iff (v := s)).2 ⟨rfl, hs⟩).symm
  set σ' : (zdGraph 2).Walk ![hi 0, hi 1] x := ρ.append (σ.copy hs'.symm rfl) with hσ'
  have hσ'S : ∀ v ∈ σ'.support, v ∈ Icc lo hi := by
    intro v hv
    rw [hσ', SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy] at hv
    rcases hv with hv | hv
    · obtain ⟨h₁, h₂, h₃⟩ := hρ v hv
      rw [mem_Icc_two_iff]
      omega
    · exact hσ v hv
  obtain ⟨v, hv, hvτ⟩ := exists_mem_support_of_dualConfig_mem_localConn h1 τ hτ hc hd σ' hσ'S
    (by simp) hf₀ hf₁ hpath
  rw [hσ', SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy] at hv
  rcases hv with hv | hv
  · obtain ⟨h₁, h₂, -⟩ := hρ v hv
    have hvd := htop v hvτ h₁
    rw [hvd] at h₂
    exfalso
    omega
  · exact ⟨v, hv, hvτ⟩

/-! ### Blocking by the strips of an annulus -/

/-- **Blocking at any centre.** If none of the four strips around the annulus
`s ≤ ‖· - z‖∞ ≤ 3s` is crossed by `ω` in its short direction, no path of `ω` joins a point within
`s` of `z` to a point at distance at least `3s` from `z`. -/
theorem notMem_localConn_of_notMem_crossing_add {ω : Config (LatticeSite 2)} (z : LatticeSite 2)
    {s : ℕ} (hT : ω ∉ crossing 1 (z + ![-3 * (s : ℤ), s]) (z + ![3 * (s : ℤ), 3 * s]))
    (hB : ω ∉ crossing 1 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), -s]))
    (hR : ω ∉ crossing 0 (z + ![(s : ℤ), -3 * s]) (z + ![3 * (s : ℤ), 3 * s]))
    (hL : ω ∉ crossing 0 (z + ![-3 * (s : ℤ), -3 * s]) (z + ![-(s : ℤ), 3 * s]))
    {a v : LatticeSite 2} (ha : |a 0 - z 0| ≤ s ∧ |a 1 - z 1| ≤ s)
    (hv : 3 * s ≤ |v 0 - z 0| ∨ 3 * s ≤ |v 1 - z 1|) (S : Set (LatticeSite 2)) :
    ω ∩ (zdGraph 2).edgeSet ∉ localConn S a v := by
  have key : ∀ (i : Fin 2) (lo hi : LatticeSite 2), ω ∉ crossing i (z + lo) (z + hi) →
      Sym2.map (· + -z) '' ω ∉ crossing i lo hi := by
    intro i lo hi h h'
    apply h
    have e := image_add_mem_crossing_iff (-z) i (z + lo) (z + hi) ω
    have h₁ : z + lo + -z = lo := by abel
    have h₂ : z + hi + -z = hi := by abel
    rw [h₁, h₂] at e
    exact e.1 h'
  intro hav
  have hav' := (image_add_inter_edgeSet_mem_localConn_iff (-z) ω S a v).2 hav
  refine notMem_localConn_of_notMem_crossing (key 1 _ _ hT) (key 1 _ _ hB) (key 0 _ _ hR)
    (key 0 _ _ hL) (a := a + -z) (v := v + -z) ?_ ?_ _ hav'
  · simp only [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
    exact ha
  · simp only [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
    exact hv

/-- **Blocking at the top right corner.** If the configuration `G`, restricted to the edges of the
box, crosses neither the strip below the top right corner from bottom to top nor the strip left
of it from left to right, at scale `s`, then no walk of `G` in the box from its bottom row lands on
its top row within `s` of the corner. -/
theorem false_of_le_add_corner_right {G : Config (LatticeSite 2)} {lo hi : LatticeSite 2}
    {s : ℕ} (hs : 1 ≤ s) (hs3 : lo 1 + 3 * s ≤ hi 1)
    (hB : G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 1 (![hi 0, hi 1] + ![-3 * (s : ℤ), -3 * s]) (![hi 0, hi 1] + ![3 * (s : ℤ), -s]))
    (hL : G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 0 (![hi 0, hi 1] + ![-3 * (s : ℤ), -3 * s]) (![hi 0, hi 1] + ![-(s : ℤ), 3 * s]))
    {a b : LatticeSite 2} (p : (zdGraph 2).Walk a b) (hp : ∀ x ∈ p.support, x ∈ Icc lo hi)
    (hpG : ∀ e ∈ p.edges, e ∈ G) (ha : a 1 = lo 1) (hb : b 1 = hi 1) (hbs : hi 0 ≤ b 0 + s) :
    False := by
  have hbR := mem_Icc_two_iff.1 (hp b p.end_mem_support)
  refine notMem_localConn_of_notMem_crossing_add ![hi 0, hi 1] (s := s) ?_ hB ?_ hL
    (a := b) (v := a) ?_ ?_ univ ?_
  · refine notMem_crossing_of_forall ?_ fun e he x hx => ?_
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · have := mem_Icc_two_iff.1 (he.2 x hx)
      left
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · refine notMem_crossing_of_forall ?_ fun e he x hx => ?_
    · simp only [Pi.add_apply, Matrix.cons_val_zero]
      omega
    · have := mem_Icc_two_iff.1 (he.2 x hx)
      left
      simp only [Pi.add_apply, Matrix.cons_val_zero]
      omega
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> rw [abs_le] <;> omega
  · right
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [le_abs]
    omega
  · refine mem_localConn_of_walk p.reverse (fun _ _ => mem_univ _) fun e he => ?_
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact ⟨hpG e he, fun x hx => hp x (mem_support_of_mem_edge _ he hx)⟩

/-- **Blocking at the top left corner.** The mirror image of `false_of_le_add_corner_right`: the
strip below the top left corner and the strip right of it. -/
theorem false_of_le_add_corner_left {G : Config (LatticeSite 2)} {lo hi : LatticeSite 2}
    {s : ℕ} (hs : 1 ≤ s) (hs3 : lo 1 + 3 * s ≤ hi 1)
    (hB : G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 1 (![lo 0, hi 1] + ![-3 * (s : ℤ), -3 * s]) (![lo 0, hi 1] + ![3 * (s : ℤ), -s]))
    (hR : G ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 0 (![lo 0, hi 1] + ![(s : ℤ), -3 * s]) (![lo 0, hi 1] + ![3 * (s : ℤ), 3 * s]))
    {a b : LatticeSite 2} (p : (zdGraph 2).Walk a b) (hp : ∀ x ∈ p.support, x ∈ Icc lo hi)
    (hpG : ∀ e ∈ p.edges, e ∈ G) (ha : a 1 = lo 1) (hb : b 1 = hi 1) (hbs : b 0 ≤ lo 0 + s) :
    False := by
  have hbR := mem_Icc_two_iff.1 (hp b p.end_mem_support)
  refine notMem_localConn_of_notMem_crossing_add ![lo 0, hi 1] (s := s) ?_ hB hR ?_
    (a := b) (v := a) ?_ ?_ univ ?_
  · refine notMem_crossing_of_forall ?_ fun e he x hx => ?_
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · have := mem_Icc_two_iff.1 (he.2 x hx)
      left
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · refine notMem_crossing_of_forall ?_ fun e he x hx => ?_
    · simp only [Pi.add_apply, Matrix.cons_val_zero]
      omega
    · have := mem_Icc_two_iff.1 (he.2 x hx)
      right
      simp only [Pi.add_apply, Matrix.cons_val_zero]
      omega
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> rw [abs_le] <;> omega
  · right
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [le_abs]
    omega
  · refine mem_localConn_of_walk p.reverse (fun _ _ => mem_univ _) fun e he => ?_
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact ⟨hpG e he, fun x hx => hp x (mem_support_of_mem_edge _ he hx)⟩

/-! ### A clean choice rule -/

/-- **A clean choice rule for the greedy exploration.** For every finite set of faces containing
the left column of the dual box and avoiding its right column, choose a bottom-top crossing of
the box through edges separating it from the other faces of the dual box, which is a path meeting
the bottom row only at its start and the top row only at its end. -/
theorem exists_crossing_choice_clean {lo hi : LatticeSite 2} (hle : lo ≤ hi) :
    ∃ (c d : Finset (LatticeSite 2) → LatticeSite 2) (Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)),
      ∀ A : Finset (LatticeSite 2),
        (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
        (∀ f ∈ A, f 0 ≠ hi 0) →
        (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
          (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
          ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
            (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
            (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
        (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
          ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A := by
  classical
  obtain ⟨c₀, d₀, Γ₀, hΓ₀⟩ := exists_crossing_choice (lo := lo) (hi := hi) hle
  have hex : ∀ A : Finset (LatticeSite 2), ∃ (c d : LatticeSite 2) (γ : (zdGraph 2).Walk c d),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c ∈ Icc lo hi ∧ c 1 = lo 1 ∧ d ∈ Icc lo hi ∧ d 1 = hi 1 ∧
        (∀ x ∈ γ.support, x ∈ Icc lo hi) ∧
        ∀ e ∈ γ.edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      γ.IsPath ∧ (∀ x ∈ γ.support, x 1 = lo 1 → x = c) ∧
        ∀ x ∈ γ.support, x 1 = hi 1 → x = d := by
    intro A
    by_cases hA : (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) ∧
        ∀ f ∈ A, f 0 ≠ hi 0
    · obtain ⟨-, hc1, -, hd1, hS, hE⟩ := hΓ₀ A hA.1 hA.2
      obtain ⟨a, b, q, hq, ha, hb, hqS, hqE, hqa, hqb⟩ :=
        SimpleGraph.Walk.exists_isPath_clean (fun x : LatticeSite 2 => x 1 = lo 1)
          (fun x => x 1 = hi 1) (Γ₀ A) hc1 hd1
      exact ⟨a, b, q, fun _ _ => ⟨⟨hS a (hqS a q.start_mem_support), ha,
        hS b (hqS b q.end_mem_support), hb, fun x hx => hS x (hqS x hx),
        fun e he => hE e (hqE e he)⟩, hq, hqa, hqb⟩⟩
    · exact ⟨0, 0, .nil, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hA⟩
  choose c d Γ hΓ using hex
  exact ⟨c, d, Γ, hΓ⟩

/-! ### Order and freshness of the greedy crossings

As in `Separation.lean`, `Γ` is a choice rule, here a clean one, and `A` is the exploration of `G`
up to step `u`; both conditions are written out. -/

section Greedy

variable {lo hi : LatticeSite 2} {G : Config (LatticeSite 2)}
  {c d : Finset (LatticeSite 2) → LatticeSite 2} {Γ : ∀ A, (zdGraph 2).Walk (c A) (d A)}

/-- **The explored faces reach the left column.** Every face of the explored cluster at step `v`
is joined to the bottom-left face of the dual box by dual edges crossing no edge of a walk `τ` in
the box whose edges are open in `G` and have no end on a chosen crossing before step `v`. -/
theorem localConn_of_mem_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) {f : LatticeSite 2} (hf : f ∈ A v) {c₁ d₁ : LatticeSite 2}
    (τ : (zdGraph 2).Walk c₁ d₁) (hτ : ∀ y ∈ τ.support, y ∈ Icc lo hi)
    (hτG : ∀ e ∈ τ.edges, e ∈ G ∧ ∀ y ∈ e, ∀ w < v, y ∉ (Γ (A w)).support) :
    dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
        ![lo 0 - 1, lo 1] f := by
  have hfC : f ∈ cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] := by
    rw [hA v hv]
    exact hf
  obtain ⟨p, hpS, hpζ⟩ := exists_walk_of_mem_exploredCluster hfC
    fun s hs => (forall_mem_Icc_of_mem_wired h1 (hle 0) rfl hs).1
  refine mem_localConn_of_walk p (fun y hy => exploredCluster_subset h1 (hle 0) rfl (hpS y hy))
    fun s hs => ?_
  rcases hpζ s hs with ⟨hsD, -⟩ | ⟨y, -, -, rfl⟩
  · rw [mem_dualConfig_iff] at hsD ⊢
    refine ⟨hsD.1, fun hmem => hsD.2 ?_⟩
    obtain ⟨hG, hR⟩ := hτG _ hmem
    exact ⟨hG, fun ⟨z, hz, w, hw, hzw⟩ => hR z hz w hw hzw⟩
  · -- a wired edge of the left column is the dual of an edge with an end left of the box
    rw [mem_dualConfig_iff]
    refine ⟨vertical_mem_edgeSet _ _, fun hmem => ?_⟩
    rw [mem_ofPred_eq, dualEdge_vertical, Sym2.map_mk] at hmem
    have := mem_Icc_two_iff.1 (hτ _ (τ.snd_mem_support_of_mem_edges hmem))
    simp only [Pi.add_apply, Matrix.cons_val_zero, Pi.one_apply] at this
    omega

/-- **The greedy tips increase from left to right.** If `A v` and `A w`, `v < w`, are admissible,
the top end of `Γ (A w)` lies strictly right of the top end of `Γ (A v)`. -/
theorem lt_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v w : ℕ} (hvw : v < w) (hwu : w ≤ u) (hv : ∀ f ∈ A v, f 0 ≠ hi 0)
    (hw : ∀ f ∈ A w, f 0 ≠ hi 0) : d (A v) 0 < d (A w) 0 := by
  have hvu : v ≤ u := by omega
  have hbig := fun A' h₁ h₂ => (hΓ A' h₁ h₂).1
  obtain ⟨⟨-, hcw1, -, hdw1, hΓwS, -⟩, -, -, hwtop⟩ :=
    hΓ (A w) (mem_leftColumn_of_exploration hA hwu) hw
  obtain ⟨⟨-, -, -, hdv1, -, -⟩, -, -, -⟩ := hΓ (A v) (mem_leftColumn_of_exploration hA hvu) hv
  have hdisj := forall_mem_of_exploration h1 hbig hA hwu hw
  by_contra hlt
  push Not at hlt
  have hne : d (A w) 0 ≠ d (A v) 0 := by
    intro h
    have hdd : d (A w) = d (A v) :=
      (eq_vec_two_iff.2 ⟨h, hdw1.trans hdv1.symm⟩).trans (eq_vec_two _).symm
    refine hdisj.2 _ (Γ (A w)).end_mem_support v hvw ?_
    rw [hdd]
    exact (Γ (A v)).end_mem_support
  -- the explored face at the tip of `Γ (A v)` reaches the left column without crossing `Γ (A w)`
  obtain ⟨f₀, f₁, hf₀, hf₁, hpath⟩ := exists_localConn_of_mem_support_of_exploration h1 hle
    hbig hA hvu hv (Γ (A v)).end_mem_support (Γ (A w)) hΓwS fun e he =>
      ⟨hdisj.1 e he, fun y hy w' hw' =>
        hdisj.2 y (mem_support_of_mem_edge _ he hy) w' (by omega)⟩
  have hf₁T := mem_Icc_two_iff.1 hpath.2.1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf₁T
  exact not_localConn_top h1 (Γ (A w)) hΓwS hcw1 hdw1 hwtop hf₀ (f := f₁) (by omega)
    (by omega) hpath

/-- **Later greedy crossings are fresh.** If `A v` and `A w`, `v < w`, are admissible, no vertex
of `Γ (A w)` has a face in `A v`: the exploration up to step `v` has not looked at its edges. -/
theorem not_le_of_mem_support_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v w : ℕ} (hvw : v < w) (hwu : w ≤ u) (hv : ∀ f ∈ A v, f 0 ≠ hi 0)
    (hw : ∀ f ∈ A w, f 0 ≠ hi 0) {x : LatticeSite 2} (hx : x ∈ (Γ (A w)).support)
    {f : LatticeSite 2} (hf : f ∈ A v) :
    ¬(x 0 - 1 ≤ f 0 ∧ f 0 ≤ x 0 ∧ x 1 - 1 ≤ f 1 ∧ f 1 ≤ x 1) := by
  intro hfx
  have hvu : v ≤ u := by omega
  have hbig := fun A' h₁ h₂ => (hΓ A' h₁ h₂).1
  obtain ⟨⟨-, hcv1, -, hdv1, hΓvS, -⟩, -, -, hvtop⟩ :=
    hΓ (A v) (mem_leftColumn_of_exploration hA hvu) hv
  obtain ⟨⟨-, -, -, hdw1, hΓwS, -⟩, -, -, -⟩ := hΓ (A w) (mem_leftColumn_of_exploration hA hwu) hw
  have hGw := forall_mem_of_exploration h1 hbig hA hwu hw
  have hGv := forall_mem_of_exploration h1 hbig hA hvu hv
  have hpath := localConn_of_mem_exploration h1 hle hA hvu hf (Γ (A v)) hΓvS fun e he =>
    ⟨hGv.1 e he, fun y hy w' hw' => hGv.2 y (mem_support_of_mem_edge _ he hy) w' hw'⟩
  have hlt := lt_of_exploration h1 hle hΓ hA hvw hwu hv hw
  have hsub : ∀ y ∈ ((Γ (A w)).dropUntil x hx).reverse.support, y ∈ (Γ (A w)).support := by
    intro y hy
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
    exact (Γ (A w)).support_dropUntil_subset_support hx hy
  obtain ⟨y, hyσ, hyτ⟩ := exists_mem_support_of_lt_top h1 (Γ (A v)) hΓvS hcv1 hdv1 hvtop
    ((Γ (A w)).dropUntil x hx).reverse (fun y hy => hΓwS y (hsub y hy)) hdw1 hlt
    (f₀ := ![lo 0 - 1, lo 1]) (by simp) hfx hpath
  exact hGw.2 y (hsub y hyσ) v hvw hyτ

/-- **Walks of the other colour landing right of a tip are fresh.** Let `A v` be admissible. A
face joined by dual edges crossing no edge of `Γ (A v)` to a face of the top row of the dual box
at or right of the tip of `Γ (A v)` is not in `A v`. -/
theorem notMem_of_localConn_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) (hvr : ∀ f ∈ A v, f 0 ≠ hi 0) {g f : LatticeSite 2}
    (hgf : dualConfig {e | e ∈ (Γ (A v)).edges} ∩ (zdGraph 2).edgeSet ∈
      localConn (Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) g f)
    (hf : f 1 = hi 1 - 1) (hdf : d (A v) 0 ≤ f 0) : g ∉ A v := by
  intro hg
  have hbig := fun A' h₁ h₂ => (hΓ A' h₁ h₂).1
  obtain ⟨⟨-, hcv1, -, hdv1, hΓvS, -⟩, -, -, hvtop⟩ :=
    hΓ (A v) (mem_leftColumn_of_exploration hA hv) hvr
  have hGv := forall_mem_of_exploration h1 hbig hA hv hvr
  have hpath := localConn_of_mem_exploration h1 hle hA hv hg (Γ (A v)) hΓvS fun e he =>
    ⟨hGv.1 e he, fun y hy w' hw' => hGv.2 y (mem_support_of_mem_edge _ he hy) w' hw'⟩
  exact not_localConn_top h1 (Γ (A v)) hΓvS hcv1 hdv1 hvtop (f₀ := ![lo 0 - 1, lo 1]) (by simp)
    hf hdf (localConn_trans hpath hgf)

/-- **Same-colour blocking.** Let `A v` and `A w`, `v < w`, be admissible, and `s ≥ 1` with
`3s` at most the height of the box. Remove from `G` the edges with a dual face in `A v` (the edges
the exploration up to step `v` has looked at) and keep the edges of the box. If this fresh part of
`G` crosses none of the three strips of the annulus `s ≤ ‖· - z‖∞ ≤ 3s` around the tip `z` of
`Γ (A v)` that meet the box, in their short directions, then the tip of `Γ (A w)` lies more than
`s` to the right of `z`. -/
theorem lt_sub_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v w : ℕ} (hvw : v < w) (hwu : w ≤ u) (hv : ∀ f ∈ A v, f 0 ≠ hi 0)
    (hw : ∀ f ∈ A w, f 0 ≠ hi 0) {s : ℕ} (hs : 1 ≤ s) (hs3 : lo 1 + 3 * s ≤ hi 1)
    (hB : (G \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 1 (d (A v) + ![-3 * (s : ℤ), -3 * s]) (d (A v) + ![3 * (s : ℤ), -s]))
    (hR : (G \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 0 (d (A v) + ![(s : ℤ), -3 * s]) (d (A v) + ![3 * (s : ℤ), 3 * s]))
    (hL : (G \ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩ {e | ∀ x ∈ e, x ∈ Icc lo hi} ∉
      crossing 0 (d (A v) + ![-3 * (s : ℤ), -3 * s]) (d (A v) + ![-(s : ℤ), 3 * s])) :
    d (A v) 0 + s < d (A w) 0 := by
  have hvu : v ≤ u := by omega
  have hbig := fun A' h₁ h₂ => (hΓ A' h₁ h₂).1
  obtain ⟨⟨-, -, -, hdv1, -, -⟩, -, -, -⟩ := hΓ (A v) (mem_leftColumn_of_exploration hA hvu) hv
  obtain ⟨⟨-, hcw1, -, hdw1, hΓwS, -⟩, -, -, -⟩ :=
    hΓ (A w) (mem_leftColumn_of_exploration hA hwu) hw
  have hGw := forall_mem_of_exploration h1 hbig hA hwu hw
  have hlt := lt_of_exploration h1 hle hΓ hA hvw hwu hv hw
  by_contra hfar
  push Not at hfar
  refine notMem_localConn_of_notMem_crossing_add (d (A v)) (s := s) ?_ hB hR hL
    (a := d (A w)) (v := c (A w)) ?_ ?_ univ ?_
  · -- the top strip lies above the box
    refine notMem_crossing_of_forall ?_ fun e he x hx => ?_
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · have := mem_Icc_two_iff.1 (he.2 x hx)
      left
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · constructor <;> rw [abs_le] <;> omega
  · right
    rw [le_abs]
    omega
  · refine mem_localConn_of_walk (Γ (A w)).reverse (fun _ _ => mem_univ _) fun e he => ?_
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    refine ⟨⟨hGw.1 e he, ?_⟩, fun x hx => hΓwS x (mem_support_of_mem_edge _ he hx)⟩
    rintro ⟨f, hfe, hfA⟩
    obtain ⟨x, y, rfl, -, hx, -⟩ := exists_ne_of_mem_edges (Γ (A w)) he
    exact not_le_of_mem_support_of_exploration h1 hle hΓ hA hvw hwu hv hw hx hfA
      (face_of_mem_dualEdge ((Γ (A w)).edges_subset_edgeSet he) (Sym2.mem_mk_left _ _) hfe)

/-- **Blocking of the other colour.** Let `A v` be admissible and `s ≥ 1`. Add to `G` the edges
with a dual face in `A v` and keep the dual edges between faces of the dual box. If the dual
configuration of this, the fresh part of the dual configuration of `G`, crosses none of the three
strips of the annulus of scale `s` around the face `(z₀, hi₁ - 1)` below the right of the tip `z`
of `Γ (A v)` that meet the dual box, in their short directions, then no walk of faces in the dual
box along dual edges crossing only edges closed in `G` runs from its bottom row to a face of its
top row within `s` to the right of `z`. -/
theorem false_of_localConn_of_exploration (h1 : lo 1 < hi 1) (hle : lo ≤ hi)
    (hΓ : ∀ A : Finset (LatticeSite 2),
      (∀ y : ℤ, lo 1 ≤ y → y ≤ hi 1 - 1 → (![lo 0 - 1, y] : LatticeSite 2) ∈ A) →
      (∀ f ∈ A, f 0 ≠ hi 0) →
      (c A ∈ Icc lo hi ∧ c A 1 = lo 1 ∧ d A ∈ Icc lo hi ∧ d A 1 = hi 1 ∧
        (∀ x ∈ (Γ A).support, x ∈ Icc lo hi) ∧
        ∀ e ∈ (Γ A).edges, e ∈ (zdGraph 2).edgeSet ∧
          (∀ f ∈ dualEdge e, f ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]) ∧
          (∃ f ∈ dualEdge e, f ∈ A) ∧ ∃ f ∈ dualEdge e, f ∉ A) ∧
      (Γ A).IsPath ∧ (∀ x ∈ (Γ A).support, x 1 = lo 1 → x = c A) ∧
        ∀ x ∈ (Γ A).support, x 1 = hi 1 → x = d A)
    {A : ℕ → Finset (LatticeSite 2)} {u : ℕ}
    (hA : ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
        {s | ∀ x ∈ s, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∪
      {s | ∃ y : ℤ, lo 1 ≤ y ∧ y + 1 ≤ hi 1 - 1 ∧
        s = s(![lo 0 - 1, y], (![lo 0 - 1, y + 1] : LatticeSite 2))}) ![lo 0 - 1, lo 1] = ↑(A v))
    {v : ℕ} (hv : v ≤ u) (hvr : ∀ f ∈ A v, f 0 ≠ hi 0) {s : ℕ} (hs : 1 ≤ s)
    (hs3 : lo 1 + 3 * s ≤ hi 1 - 1)
    (hB : dualConfig (G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 1 (![d (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), -s]))
    (hR : dualConfig (G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 0 (![d (A v) 0, hi 1 - 1] + ![(s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![3 * (s : ℤ), 3 * s]))
    (hL : dualConfig (G ∪ {e | ∃ f ∈ dualEdge e, f ∈ A v}) ∩
        {e | ∀ x ∈ e, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1]} ∉
      crossing 0 (![d (A v) 0, hi 1 - 1] + ![-3 * (s : ℤ), -3 * s])
        (![d (A v) 0, hi 1 - 1] + ![-(s : ℤ), 3 * s]))
    {g f : LatticeSite 2} (π : (zdGraph 2).Walk g f)
    (hπ : ∀ x ∈ π.support, x ∈ Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1])
    (hπG : ∀ e ∈ π.edges, e ∈ dualConfig G) (hg : g 1 = lo 1) (hf : f 1 = hi 1 - 1)
    (hdf : d (A v) 0 ≤ f 0) (hfs : f 0 ≤ d (A v) 0 + s) : False := by
  have hbig := fun A' h₁ h₂ => (hΓ A' h₁ h₂).1
  have hGv := forall_mem_of_exploration h1 hbig hA hv hvr
  -- the walk crosses no edge of `Γ (A v)`, so its faces are fresh
  have hπΓ : ∀ e ∈ π.edges, e ∈ dualConfig {e | e ∈ (Γ (A v)).edges} :=
    fun e he => dualConfig_anti (fun e' he' => hGv.1 e' he') (hπG e he)
  have hfresh : ∀ x ∈ π.support, x ∉ A v := by
    intro x hx
    refine notMem_of_localConn_of_exploration h1 hle hΓ hA hv hvr (f := f) ?_ hf hdf
    exact mem_localConn_of_walk (π.dropUntil x hx)
      (fun y hy => hπ y (π.support_dropUntil_subset_support hx hy))
      fun e he => hπΓ e (π.edges_dropUntil_subset_edges hx he)
  refine notMem_localConn_of_notMem_crossing_add (![d (A v) 0, hi 1 - 1]) (s := s) ?_ hB hR hL
    (a := f) (v := g) ?_ ?_ univ ?_
  · -- the top strip lies above the dual box
    refine notMem_crossing_of_forall ?_ fun e he x hx => ?_
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · have := mem_Icc_two_iff.1 (he.2 x hx)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      left
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> rw [abs_le] <;> omega
  · right
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [le_abs]
    omega
  · refine mem_localConn_of_walk π.reverse (fun _ _ => mem_univ _) fun e he => ?_
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    refine ⟨?_, fun x hx => hπ x (mem_support_of_mem_edge _ he hx)⟩
    obtain ⟨e', he', he'G, rfl⟩ := (mem_dualConfig_iff' G e).1 (hπG e he)
    refine (mem_dualConfig_iff' _ _).2 ⟨e', he', ?_, rfl⟩
    rintro (h | ⟨f', hf', hf'A⟩)
    · exact he'G h
    · exact hfresh f' (mem_support_of_mem_edge π he hf') hf'A

end Greedy

end PercLib.Models.Planar
