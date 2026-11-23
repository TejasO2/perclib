/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Sections 4.4-4.6 (separation of arms, quasi-multiplicativity,
extendability).
-/
module

public import PercLib.Models.Planar.Arms.SeparationLemma

/-!
# Towards quasi-multiplicativity: symmetries of crossing bounds and arms in corridors

First steps towards Nolin's separation of arms and quasi-multiplicativity (Nolin, Theorem 11 and
Propositions 12, 16, 17). Nolin's separation lemma (`exists_law_separable_ge`) is stated for one
strip, crossed from bottom to top. Arms of an annulus land on its four sides, so the lemma is
needed for the strips along the other sides too: this file transports crossing bounds along the
symmetries of `ℤ²`. It also builds arms from crossings of corridors, the construction behind the
gluing of separated arms and the a priori lower bound, and proves the a priori lower bound for one
annulus of bounded aspect ratio.

* **The law seen through a bijection.** For a bijection `g` of `ℤ²`, the law with profile
  `e ↦ q (g e)` is the law of `g⁻¹ ω` under `law q`.
* **The coordinate swap and the reflection in the horizontal axis.** The swap `(x, y) ↦ (y, x)`
  maps a box crossed in direction `0` onto a box crossed in direction `1` with the same aspect
  ratio and scale, and commutes with taking duals. The reflection `(x, y) ↦ (x, b - y)` maps boxes
  onto boxes, keeps the direction of crossing, and maps duals to duals up to the shift of faces:
  the face with lower-left corner `f` goes to the face with lower-left corner `(f₀, b - 1 - f₁)`.
  So crossing bounds of both colours pass to the swapped and to the reflected law with the same
  bounds `c` and the same scale `L`. With translations (`CrossingBounds.translate`) these
  generate all symmetries of `ℤ²`; a quarter turn is a swap followed by a reflection.
* **Arms in a corridor.** A bottom-top crossing, open or dual, of a vertical corridor standing on
  the top side of `B_r(z)` and reaching the top side of `B_R(z)` contains an arm of that colour,
  inside the corridor, landing on the top side; its landing position is read off the columns of
  the corridor.
* **Arms across one annulus.** With `j` corridors of width `⌊r / 2j⌋` side by side, separated by
  gaps of the same width and arranged from right to left, the corridor crossings are independent
  (they read disjoint sets of edges; the dual crossing of a box of faces reads only the edges with
  both ends in the box enlarged by one), and together they give the `j`-arm event, in
  counterclockwise order. So under crossing bounds the `j`-arm event from `B_r(z)` to the boundary
  of `B_R(z)` has probability bounded below uniformly when `4j ≤ r < R ≤ K r`.

## Main results

* `law_comp_sym2Map_apply`: the law with a relabelled profile is a push-forward.
* `dualEdge_map_reflect`, `dualConfig_image_reflect`: the reflection `(x, y) ↦ (x, b - y)`
  commutes with taking duals, up to the shift of faces.
* `CrossingBounds.swap`, `CrossingBounds.reflect`: crossing bounds are invariant under the
  coordinate swap and the reflections in horizontal lines.
* `exists_isCrossing_of_mem_crossing_one`: a bottom-top crossing of a box contains a walk that
  crosses from a set containing the bottom row out of a set missing the top row.
* `exists_isArm_of_mem_corridor`: an arm of either colour in a vertical corridor, with its
  landing position.
* `dualConfig_inter_eq_of_inter_eq`: the dual edges between faces of a box are determined by the
  edges of the box enlarged by one.
* `exists_pos_le_law_multiArmEvent`: the a priori lower bound for one annulus of bounded aspect
  ratio, uniformly under crossing bounds, for `4j ≤ r < R ≤ K r`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The law seen through a bijection of `ℤ²` -/

/-- **Relabelling the profile.** For a bijection `g` of the sites, the law whose profile is `q`
read through `g` is the law of the configuration moved by `g⁻¹`. -/
theorem law_comp_sym2Map_apply {V : Type*} (q : Sym2 V → unitInterval) (g : V ≃ V)
    (A : Set (Config V)) :
    law (fun e => q (Sym2.map g e)) A = law q ((fun ω => Sym2.map g.symm '' ω) ⁻¹' A) := by
  have hmap := PercLib.Probability.prodBernoulli_map_image_sym2 q g.symm
  have hq : (q ∘ Sym2.map g.symm.symm) = fun e => q (Sym2.map g e) := by
    funext e
    simp only [Function.comp_apply, Equiv.symm_symm]
  rw [hq] at hmap
  unfold law
  rw [← hmap]
  exact map_image_sym2Map_apply _ _ _

/-! ### The reflection in a horizontal line and duality -/

/-- The reflection `(x, y) ↦ (x, b - y)` maps a box onto a box. -/
theorem image_reflect_one_Icc {b : ℤ} {σ : zdGraph 2 ≃g zdGraph 2}
    (hσ : ∀ v, σ v = ![v 0, b - v 1]) (lo hi : LatticeSite 2) :
    σ '' Icc lo hi = Icc ![lo 0, b - hi 1] ![hi 0, b - lo 1] := by
  ext w
  simp only [mem_image, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [hσ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · intro hw
    refine ⟨![w 0, b - w 1], ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [hσ, eq_comm, eq_vec_two_iff]
      simp

/-- The reflection `(x, y) ↦ (x, b - y)` preserves the edges of `ℤ²`. -/
theorem map_reflect_mem_edgeSet_iff (b : ℤ) (e : Sym2 (LatticeSite 2)) :
    Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1]) e ∈ (zdGraph 2).edgeSet ↔
      e ∈ (zdGraph 2).edgeSet := by
  obtain ⟨σ, hσ⟩ := exists_iso_reflect_one b
  have h : (⇑σ : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, b - v 1] := funext hσ
  rw [← h]
  induction e using Sym2.ind with
  | h u v => exact σ.map_adj_iff

/-- The reflection `(x, y) ↦ (x, b - y)` is an involution of unordered pairs. -/
theorem map_reflect_map_reflect (b : ℤ) (e : Sym2 (LatticeSite 2)) :
    Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1])
      (Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1]) e) = e := by
  induction e using Sym2.ind with
  | h u v =>
    simp only [Sym2.map_mk, Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
    rw [← eq_vec_two u, ← eq_vec_two v]

/-- **The reflection and the dual edge.** Reflecting an edge of `ℤ²` in the line `y = b/2`
reflects its dual edge in the line `y = (b - 1)/2`: the face with lower-left corner `f` becomes
the face with lower-left corner `(f₀, b - 1 - f₁)`. -/
theorem dualEdge_map_reflect (b : ℤ) {e : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) :
    dualEdge (Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1]) e) =
      Sym2.map (fun v : LatticeSite 2 => ![v 0, b - 1 - v 1]) (dualEdge e) := by
  obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal]
    simp only [Sym2.map_mk, dualEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Sym2.eq_swap]
    exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)
  · rw [dualEdge_vertical]
    simp only [Sym2.map_mk, dualEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Sym2.eq_swap]
    exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- **The reflection commutes with taking duals**, up to the shift of faces: the dual of the
reflection of `ω` in the line `y = b/2` is the reflection of the dual of `ω` in the line
`y = (b - 1)/2`. -/
theorem dualConfig_image_reflect (b : ℤ) (ω : Config (LatticeSite 2)) :
    dualConfig (Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1]) '' ω) =
      Sym2.map (fun v : LatticeSite 2 => ![v 0, b - 1 - v 1]) '' dualConfig ω := by
  set rf : Sym2 (LatticeSite 2) → Sym2 (LatticeSite 2) :=
    Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1]) with hrf
  have hmem : ∀ e, e ∈ rf '' ω ↔ rf e ∈ ω := by
    intro e
    constructor
    · rintro ⟨e', he', rfl⟩
      rwa [hrf, map_reflect_map_reflect]
    · intro h
      exact ⟨rf e, h, map_reflect_map_reflect b e⟩
  ext f
  rw [mem_dualConfig_iff']
  constructor
  · rintro ⟨e, he, heω, rfl⟩
    rw [hmem] at heω
    refine ⟨dualEdge (rf e), (mem_dualConfig_iff' ω _).2
      ⟨rf e, (map_reflect_mem_edgeSet_iff b e).2 he, heω, rfl⟩, ?_⟩
    rw [hrf, dualEdge_map_reflect b he, map_reflect_map_reflect (b - 1)]
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨e, he, heω, rfl⟩ := (mem_dualConfig_iff' ω g).1 hg
    refine ⟨rf e, (map_reflect_mem_edgeSet_iff b e).2 he, ?_, dualEdge_map_reflect b he⟩
    rwa [hmem, hrf, map_reflect_map_reflect]

/-! ### Crossing bounds under the swap and the reflections -/

namespace CrossingBounds

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}

/-- **The coordinate swap.** Crossing bounds pass to the law seen through the swap
`(x, y) ↦ (y, x)`, with the same bounds and scale: a box crossed in one direction is the swap of
a box of the same size crossed in the other direction, and the swap commutes with duality. -/
theorem swap (h : CrossingBounds q L c) :
    CrossingBounds (fun e => q (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e)) L c := by
  obtain ⟨σ, hσ⟩ := exists_iso_swap
  have hσf : (⇑σ : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := funext hσ
  have hσs : ∀ v, σ.toEquiv.symm v = ![v 1, v 0] := by
    intro v
    apply σ.toEquiv.injective
    rw [Equiv.apply_symm_apply]
    change v = σ ![v 1, v 0]
    rw [hσ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact eq_vec_two v
  have hσsf : (⇑σ.toEquiv.symm : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] :=
    funext hσs
  have hlaw : ∀ A : Set (Config (LatticeSite 2)),
      law (fun e => q (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e)) A =
        law q ((fun ω => Sym2.map σ '' ω) ⁻¹' A) := by
    intro A
    have := law_comp_sym2Map_apply q σ.toEquiv A
    rw [hσsf] at this
    change law (fun e => q (Sym2.map (⇑σ) e)) A = _ at this
    rw [hσf] at this
    rw [this, ← hσf]
  -- the swapped box
  have hbox : ∀ lo hi : LatticeSite 2,
      σ '' Icc ![lo 1, lo 0] ![hi 1, hi 0] = Icc lo hi := by
    intro lo hi
    rw [image_swap_Icc hσ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← eq_vec_two lo, ← eq_vec_two hi]
  have hcross : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      (fun ω => Sym2.map σ '' ω) ⁻¹' crossing i lo hi =
        crossing (1 - i) ![lo 1, lo 0] ![hi 1, hi 0] := by
    intro i lo hi
    ext ω
    rw [mem_preimage]
    refine image_mem_crossing_iff σ (hbox lo hi) (fun v _ => ?_) (fun v _ => ?_) ω <;>
      · rw [hσ]
        fin_cases i <;> simp
  have hdual : ∀ (i : Fin 2) (lo hi : LatticeSite 2),
      (fun ω => Sym2.map σ '' ω) ⁻¹' (dualConfig ⁻¹' crossing i lo hi) =
        dualConfig ⁻¹' crossing (1 - i) ![lo 1, lo 0] ![hi 1, hi 0] := by
    intro i lo hi
    ext ω
    simp only [mem_preimage]
    rw [hσf, dualConfig_image_swap, ← hσf]
    refine image_mem_crossing_iff σ (hbox lo hi) (fun v _ => ?_) (fun v _ => ?_) _ <;>
      · rw [hσ]
        fin_cases i <;> simp
  have hshape : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ),
      (![(lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) 1,
          (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) 0] : LatticeSite 2) =
        ![lo 1, lo 0] + if 1 - i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n] := by
    intro k i lo n
    fin_cases i <;> simp
  refine ⟨h.pos, fun k i lo n hn hnL => ?_, fun k i lo n hn hnL => ?_⟩
  · rw [hlaw, hcross, hshape]
    exact h.le_law_crossing k (1 - i) _ n hn hnL
  · rw [hlaw, hdual, hshape]
    exact h.le_law_dualConfig_crossing k (1 - i) _ n hn hnL

/-- **The reflection in a horizontal line.** Crossing bounds pass to the law seen through the
reflection `(x, y) ↦ (x, -y)`, with the same bounds and scale: boxes are reflected onto boxes of
the same size, crossed in the same direction, and the dual configuration is reflected with the
shift of faces. -/
theorem reflect (h : CrossingBounds q L c) :
    CrossingBounds (fun e => q (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) L c := by
  obtain ⟨σ, hσ⟩ := exists_iso_reflect_one 0
  obtain ⟨σ', hσ'⟩ := exists_iso_reflect_one (-1)
  have hσf : (⇑σ : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - v 1] := funext hσ
  have hσ'f : (⇑σ' : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - 1 - v 1] := by
    funext v
    rw [hσ', eq_vec_two_iff]
    simp
  have hσs : ∀ v, σ.toEquiv.symm v = ![v 0, 0 - v 1] := by
    intro v
    apply σ.toEquiv.injective
    rw [Equiv.apply_symm_apply]
    change v = σ ![v 0, 0 - v 1]
    rw [hσ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_sub_cancel]
    exact eq_vec_two v
  have hσsf : (⇑σ.toEquiv.symm : LatticeSite 2 → LatticeSite 2) = fun v => ![v 0, 0 - v 1] :=
    funext hσs
  have hlaw : ∀ A : Set (Config (LatticeSite 2)),
      law (fun e => q (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) A =
        law q ((fun ω => Sym2.map σ '' ω) ⁻¹' A) := by
    intro A
    have := law_comp_sym2Map_apply q σ.toEquiv A
    rw [hσsf] at this
    change law (fun e => q (Sym2.map (⇑σ) e)) A = _ at this
    rw [hσf] at this
    rw [this, ← hσf]
  -- open crossings, both directions
  have hcross : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ),
      (fun ω => Sym2.map σ '' ω) ⁻¹'
          crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) =
        crossing i (![lo 0, -(lo 1 + if i = 0 then (n : ℤ) else k * n)])
          (![lo 0, -(lo 1 + if i = 0 then (n : ℤ) else k * n)] +
            if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) := by
    intro k i lo n
    have hbox : σ '' Icc (![lo 0, -(lo 1 + if i = 0 then (n : ℤ) else k * n)])
        (![lo 0, -(lo 1 + if i = 0 then (n : ℤ) else k * n)] +
          if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) =
        Icc lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) := by
      rw [image_reflect_one_Icc hσ]
      congr 1 <;> rw [eq_comm, eq_vec_two_iff] <;> fin_cases i <;> simp
    ext ω
    rw [mem_preimage]
    fin_cases i
    · refine image_mem_crossing_iff σ hbox (fun v _ => ?_) (fun v _ => ?_) ω <;>
      · rw [hσ]
        simp
    · refine image_mem_crossing_iff_of_rev σ hbox (fun v _ => ?_) (fun v _ => ?_) ω <;>
      · rw [hσ]
        simp
        omega
  -- dual crossings, both directions
  have hdual : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ),
      (fun ω => Sym2.map σ '' ω) ⁻¹' (dualConfig ⁻¹'
          crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n])) =
        dualConfig ⁻¹' crossing i (![lo 0, -1 - (lo 1 + if i = 0 then (n : ℤ) else k * n)])
          (![lo 0, -1 - (lo 1 + if i = 0 then (n : ℤ) else k * n)] +
            if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) := by
    intro k i lo n
    have hbox : σ' '' Icc (![lo 0, -1 - (lo 1 + if i = 0 then (n : ℤ) else k * n)])
        (![lo 0, -1 - (lo 1 + if i = 0 then (n : ℤ) else k * n)] +
          if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) =
        Icc lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]) := by
      rw [image_reflect_one_Icc hσ']
      congr 1 <;> rw [eq_comm, eq_vec_two_iff] <;> fin_cases i <;> simp <;> ring
    ext ω
    simp only [mem_preimage]
    rw [hσf, dualConfig_image_reflect, ← hσ'f]
    fin_cases i
    · refine image_mem_crossing_iff σ' hbox (fun v _ => ?_) (fun v _ => ?_) _ <;>
      · rw [hσ']
        simp
    · refine image_mem_crossing_iff_of_rev σ' hbox (fun v _ => ?_) (fun v _ => ?_) _ <;>
      · rw [hσ']
        simp
        omega
  refine ⟨h.pos, fun k i lo n hn hnL => ?_, fun k i lo n hn hnL => ?_⟩
  · rw [hlaw, hcross]
    exact h.le_law_crossing k i _ n hn hnL
  · rw [hlaw, hdual]
    exact h.le_law_dualConfig_crossing k i _ n hn hnL

end CrossingBounds

/-! ### Arms in a vertical corridor -/

/-- **From a bottom-top crossing to a crossing walk.** A bottom-top crossing of the box
`Icc lo hi` in a configuration `ζ` contains a walk of `ℤ²` along edges of `ζ`, inside the box,
that crosses from `S` out of `T`, as soon as the bottom row of the box lies in `S` and its top
row outside `T`: the part of the crossing from its last vertex in `S` before its first vertex
outside `T` to that vertex. -/
theorem exists_isCrossing_of_mem_crossing_one {ζ : Config (LatticeSite 2)}
    {lo hi : LatticeSite 2} {S T : Set (LatticeSite 2)} (h : ζ ∈ crossing 1 lo hi)
    (hS : ∀ v ∈ Icc lo hi, v 1 = lo 1 → v ∈ S) (hT : ∀ v ∈ Icc lo hi, v 1 = hi 1 → v ∉ T) :
    ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), γ.IsCrossing S T ∧
      (∀ e ∈ γ.edges, e ∈ ζ) ∧ ∀ v ∈ γ.support, v ∈ Icc lo hi := by
  obtain ⟨a, ha, ha1, b, hb, hb1, hab⟩ := h
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hab
  have hpE : ∀ e ∈ p.edges, e ∈ (zdGraph 2).edgeSet ∧ e ∈ ζ := by
    intro e he
    have he' := p.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at he'
    exact ⟨he'.1.2, he'.1.1⟩
  set p' := p.transfer (zdGraph 2) fun e he => (hpE e he).1 with hp'
  have hp'S : ∀ v ∈ p'.support, v ∈ Icc lo hi := by
    intro v hv
    rw [hp', SimpleGraph.Walk.support_transfer] at hv
    exact hp v hv
  have hp'E : ∀ e ∈ p'.edges, e ∈ ζ := by
    intro e he
    rw [hp', SimpleGraph.Walk.edges_transfer] at he
    exact (hpE e he).2
  -- first exit from `T`, then last visit to `S`
  obtain ⟨c₁, q, s, hqs, hc₁, hq⟩ := SimpleGraph.Walk.exists_append_eq_of_notMem (T := T) p'
    (hT b hb hb1)
  obtain ⟨c₀, hc₀, q₀, t, hq₀t, ht⟩ := SimpleGraph.Walk.exists_append_eq_of_exists_mem (S := S) q
    ⟨a, q.start_mem_support, hS a ha ha1⟩
  have htq : ∀ v ∈ t.support, v ∈ q.support := by
    intro v hv
    rw [← hq₀t, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  have hqp : ∀ v ∈ q.support, v ∈ p'.support := by
    intro v hv
    rw [← hqs, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hv
  refine ⟨c₀, c₁, t, ⟨hc₀, ht, hc₁, fun v hv => hq v ?_⟩, fun e he => hp'E e ?_,
    fun v hv => hp'S v (hqp v (htq v hv))⟩
  · rw [← hq₀t, SimpleGraph.Walk.support_append_eq_support_dropLast_append,
      List.dropLast_append_of_ne_nil (SimpleGraph.Walk.support_ne_nil t)]
    exact List.mem_append_right _ hv
  · rw [← hqs, SimpleGraph.Walk.edges_append]
    refine List.mem_append_left _ ?_
    rw [← hq₀t, SimpleGraph.Walk.edges_append]
    exact List.mem_append_right _ he

/-- **An arm of either colour in a vertical corridor.** Let the corridor `[x, x + w] × [z₁ + r,
z₁ + R]` stand on the top side of `B_r(z)`, with `r < R`. A bottom-top crossing of it of colour
`col` (open edges for an open arm, dual-open edges of the box of faces for a dual arm) contains an
arm of colour `col` from `B_r(z)` to the boundary of `B_R(z)`, inside the corridor, landing on the
top side of `B_R(z)` at a position between `8R + 2(z₀ + R - x - w) - 1` and
`8R + 2(z₀ + R - x)`. -/
theorem exists_isArm_of_mem_corridor {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r R : ℕ}
    {x w : ℤ} (col : Bool) (hx : z 0 - r ≤ x) (hxw : x + w ≤ z 0 + r) (hrR : r < R)
    (h : ω ∈ cond col (crossing 1 ![x, z 1 + r] ![x + w, z 1 + R])
      (dualConfig ⁻¹' crossing 1 ![x, z 1 + r] ![x + w, z 1 + R])) :
    ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), IsArm ω col z r (z - R) (z + R) γ ∧
      (∀ v ∈ γ.support, x ≤ v 0 ∧ v 0 ≤ x + w) ∧
      8 * (R : ℤ) + 2 * (z 0 + R - x - w) - 1 ≤ landingPos (z - R) (z + R) col γ ∧
      landingPos (z - R) (z + R) col γ ≤ 8 * (R : ℤ) + 2 * (z 0 + R - x) := by
  have hR : (0 : ℤ) < R := by omega
  cases col with
  | true =>
    have h' : ω ∈ crossing 1 ![x, z 1 + r] ![x + w, z 1 + R] := h
    obtain ⟨a, b, γ, hγ, hγE, hγS⟩ := exists_isCrossing_of_mem_crossing_one
      (S := Icc (z - (r : LatticeSite 2)) (z + r))
      (T := Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) h'
      (fun v hv hv1 => by
        rw [mem_Icc_two_iff] at hv ⊢
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv hv1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
        omega)
      (fun v hv hv1 hT => by
        rw [mem_Icc_two_iff] at hv hT
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv hv1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hT
        omega)
    have hb := hγS b γ.end_mem_support
    have hbT := hγ.end_notMem
    rw [mem_Icc_two_iff] at hb hbT
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hbT
    have hb1 : b 1 = z 1 + R := by omega
    refine ⟨a, b, γ, ⟨hγ, hγE⟩, fun v hv => ?_, ?_⟩
    · have := hγS v hv
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
    · rw [landingPos_true, perimeterPos_of_top (by simp [hb1]) (by simp; omega) (by simp; omega)]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      omega
  | false =>
    have h' : dualConfig ω ∈ crossing 1 ![x, z 1 + r] ![x + w, z 1 + R] := h
    obtain ⟨a, b, γ, hγ, hγE, hγS⟩ := exists_isCrossing_of_mem_crossing_one
      (S := Icc (z - (r : LatticeSite 2) - 1) (z + r))
      (T := Icc (z - (R : LatticeSite 2)) (z + R - 1)) h'
      (fun v hv hv1 => by
        rw [mem_Icc_two_iff] at hv ⊢
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv hv1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
        omega)
      (fun v hv hv1 hT => by
        rw [mem_Icc_two_iff] at hv hT
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv hv1
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hT
        omega)
    have hb := hγS b γ.end_mem_support
    have hbT := hγ.end_notMem
    rw [mem_Icc_two_iff] at hb hbT
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hbT
    have hb1 : b 1 = z 1 + R := by omega
    -- the last face but one is just below the last face
    have hnil : ¬γ.Nil := hγ.not_nil (by
      intro v hv
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
      omega)
    have hpT := hγ.penultimate_mem hnil
    have hpS := hγS _ (List.mem_of_mem_dropLast (γ.penultimate_mem_dropLast_support hnil))
    have hadj := γ.adj_penultimate hnil
    rw [zdGraph_two_adj_iff] at hadj
    rw [mem_Icc_two_iff] at hpT hpS
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpS
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hpT
    have hp0 : γ.penultimate 0 = b 0 := by omega
    have hp1 : γ.penultimate 1 = z 1 + R - 1 := by omega
    refine ⟨a, b, γ, ⟨hγ, hγE⟩, fun v hv => ?_, ?_⟩
    · have := hγS v hv
      rw [mem_Icc_two_iff] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
    · rw [landingPos_false, perimeterPos_of_top (by simp [hp1, hb1]; ring) (by simp [hp0]; omega)
          (by simp [hp1, hb1]; omega)]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply, Pi.smul_apply,
        nsmul_eq_mul, Nat.cast_ofNat, hp0]
      omega

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
    have hde : dualEdge e = f := dualEdge_map_add_one_dualEdge hf
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

/-- **Arms across an annulus of bounded aspect ratio.** For every colour sequence `σ` of `j`
arms and every ratio `K`, there is `c₀ > 0` such that, uniformly over laws with crossing bounds
`c` up to `L`, the `j`-arm event from `B_r(z)` to the boundary of `B_R(z)` has probability at least
`c₀` when `4j ≤ r < R ≤ K r` and `R ≤ L`. The arms are crossings of `j` vertical corridors of
width `w = ⌊r / 2j⌋` standing on the top side of `B_r(z)`, separated by gaps of width `w`, arranged
from right to left so that they land in counterclockwise order; the corridors read disjoint sets
of edges, so their crossing events are independent, each of probability at least `c (4jK)`. -/
theorem exists_pos_le_law_multiArmEvent {j : ℕ} (σ : Fin j → Bool) (c : ℕ → ℝ≥0∞) (K : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), 4 * j ≤ r → r < R → R ≤ K * r →
        (R : ℕ∞) ≤ L → c₀ ≤ law q (multiArmEvent σ z r R) := by
  by_cases hc : 0 < c (4 * j * K)
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  refine ⟨c (4 * j * K) ^ j, ENNReal.pow_pos hc j, ?_⟩
  intro q L hCB z r R hjr hrR hRK hRL
  set w : ℕ := r / (2 * j) with hw
  -- the corridors
  set x : Fin j → ℤ := fun i => z 0 + r - (2 * (i : ℤ) + 2) * w with hx
  set lo : Fin j → LatticeSite 2 := fun i => ![x i, z 1 + r] with hlo
  set hi : Fin j → LatticeSite 2 := fun i => ![x i + w, z 1 + R] with hhi
  set E : Fin j → Set (Config (LatticeSite 2)) := fun i =>
    cond (σ i) (crossing 1 (lo i) (hi i)) (dualConfig ⁻¹' crossing 1 (lo i) (hi i)) with hE
  -- arithmetic of the corridors, for `j ≥ 1`
  have harith : ∀ i : Fin j, 2 ≤ w ∧ 2 * (j * w) ≤ r ∧ r ≤ 4 * (j * w) := by
    intro i
    have hj : 0 < j := Fin.pos i
    have h₁ : w * (2 * j) ≤ r := Nat.div_mul_le_self r (2 * j)
    have h₂ : r < (2 * j) * (r / (2 * j) + 1) := Nat.lt_mul_div_succ r (by omega)
    have h₃ : 2 ≤ w := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    rw [← hw] at h₂
    refine ⟨h₃, by nlinarith, by nlinarith⟩
  have hxi : ∀ i : Fin j, z 0 - r ≤ x i ∧ x i + w ≤ z 0 + r := by
    intro i
    obtain ⟨h2, h₁, -⟩ := harith i
    have hi1 : (i : ℕ) + 1 ≤ j := i.2
    have hle : ((2 * (i : ℤ) + 2) * w) ≤ 2 * ((j : ℤ) * w) := by
      have : (2 * (i : ℤ) + 2) ≤ 2 * j := by exact_mod_cast (by omega : 2 * (i : ℕ) + 2 ≤ 2 * j)
      nlinarith
    have hr : 2 * ((j : ℤ) * w) ≤ r := by exact_mod_cast h₁
    simp only [hx]
    constructor <;> nlinarith
  have hsep : ∀ i k : Fin j, i < k → x k + w + 1 < x i := by
    intro i k hik
    obtain ⟨h2, -, -⟩ := harith i
    have hik' : (i : ℤ) + 1 ≤ k := by exact_mod_cast hik
    have hw2 : (2 : ℤ) ≤ w := by exact_mod_cast h2
    simp only [hx]
    nlinarith
  -- the corridor events give the arms
  have hsub : (⋂ i, E i) ⊆ multiArmEvent σ z r R := by
    intro ω hω
    rw [mem_iInter] at hω
    choose a b γ hγ hsupp hpos₁ hpos₂ using fun i =>
      exists_isArm_of_mem_corridor (ω := ω) (z := z) (σ i) (hxi i).1 (hxi i).2 hrR (hω i)
    have hcol : ∀ i k : Fin j, i ≠ k → ∀ v ∈ (γ i).support, v ∉ (γ k).support := by
      intro i k hik v hvi hvk
      have h₁ := hsupp i v hvi
      have h₂ := hsupp k v hvk
      rcases lt_or_gt_of_ne hik with h | h
      · have := hsep i k h
        omega
      · have := hsep k i h
        omega
    refine ⟨a, b, γ, hγ, ⟨fun i k hik _ _ v hv => hcol i k hik v (List.mem_of_mem_tail hv),
      fun i k hik _ _ v hv => hcol i k hik v hv⟩, fun _ => ⟨mem_univ _, mem_univ _⟩,
      fun i k l hik hkl => ?_⟩
    have hlt : ∀ i k : Fin j, i < k → landingPos (z - R) (z + R) (σ i) (γ i) <
        landingPos (z - R) (z + R) (σ k) (γ k) := by
      intro i k hik
      have h₁ := hpos₂ i
      have h₂ := hpos₁ k
      have := hsep i k hik
      omega
    exact Int.sbtw_iff.2 (Or.inl ⟨hlt i k hik, hlt k l hkl⟩)
  -- independence of the corridor events
  set P : Fin j → Set (Sym2 (LatticeSite 2)) := fun i =>
    {e | ∀ v ∈ e, v ∈ Icc (lo i) (hi i + 1)} with hP
  have hPd : Pairwise (Function.onFun Disjoint P) := by
    intro i k hik
    rw [Function.onFun, Set.disjoint_left]
    intro e hei hek
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨(Quot.out e).1, Sym2.out_fst_mem e⟩
    have h₁ := hei v hv
    have h₂ := hek v hv
    simp only [hlo, hhi, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply, Pi.one_apply] at h₁ h₂
    rcases lt_or_gt_of_ne hik with h | h
    · have := hsep i k h
      omega
    · have := hsep k i h
      omega
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    simp only [hE]
    cases σ i
    · exact measurable_dualConfig (measurableSet_crossing _ _ _)
    · exact measurableSet_crossing _ _ _
  have hEd : ∀ i, ∀ ω ω', ω ∩ P i = ω' ∩ P i → (ω ∈ E i ↔ ω' ∈ E i) := by
    intro i ω ω' h
    have hsub' : Icc (lo i) (hi i) ⊆ Icc (lo i) (hi i + 1) := by
      intro v hv
      exact ⟨hv.1, fun l => (hv.2 l).trans (by simp)⟩
    simp only [hE]
    cases σ i
    · exact mem_crossing_iff_of_inter_eq le_rfl (dualConfig_inter_eq_of_inter_eq h)
    · exact mem_crossing_iff_of_inter_eq hsub' h
  have hind : law q (⋂ i, E i) = ∏ i, law q (E i) :=
    PercLib.Probability.prodBernoulli_iInter_fin_of_determined q hPd hEm hEd
  -- each corridor is crossed with probability at least `c (4 j K)`
  have hle : ∀ i, c (4 * j * K) ≤ law q (E i) := by
    intro i
    obtain ⟨h2, -, h₄⟩ := harith i
    have hwL : (w : ℕ∞) ≤ L := by
      refine le_trans ?_ hRL
      have := Nat.div_le_self r (2 * j)
      exact_mod_cast (show w ≤ R by omega)
    have hRw : (R : ℤ) ≤ r + ((4 * j * K : ℕ) : ℤ) * w := by
      have h₅ : R ≤ 4 * j * K * w := by
        calc R ≤ K * r := hRK
          _ ≤ K * (4 * (j * w)) := Nat.mul_le_mul_left K h₄
          _ = 4 * j * K * w := by ring
      have : (R : ℤ) ≤ ((4 * j * K : ℕ) : ℤ) * w := by exact_mod_cast h₅
      omega
    have h₁ : (lo i) 1 ≤ (hi i) 1 := by
      simp only [hlo, hhi, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    have h₁' : (hi i) 1 ≤ (lo i) 1 + ((4 * j * K : ℕ) : ℤ) * (w : ℤ) := by
      simp only [hlo, hhi, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    have h₀ : (lo i) 0 + w ≤ (hi i) 0 := by simp [hlo, hhi]
    simp only [hE]
    cases σ i
    · exact hCB.le_law_dualConfig_crossing_one_of_le (4 * j * K) (by omega) hwL h₁
        (by exact_mod_cast h₁') h₀
    · exact hCB.le_law_crossing_one_of_le (4 * j * K) (by omega) hwL h₁
        (by exact_mod_cast h₁') h₀
  calc c (4 * j * K) ^ j = ∏ _i : Fin j, c (4 * j * K) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, law q (E i) := Finset.prod_le_prod fun i _ => hle i
    _ = law q (⋂ i, E i) := hind.symm
    _ ≤ law q (multiArmEvent σ z r R) := measure_mono hsub

end PercLib.Models.Planar
