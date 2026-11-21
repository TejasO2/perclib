/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: G. Grimmett, Percolation, 2nd ed., Springer, 1999, Section 11.2;
B. Bollobás and O. Riordan, A short proof of the Harris-Kesten theorem, Bull. London Math. Soc.
38 (2006), 470-484.
-/
module

public import PercLib.Models.Planar.SelfDuality

/-!
# Symmetries of crossing events on `ℤ²`

Tools for comparing crossing events of boxes of `ℤ²`, used by the Russo–Seymour–Welsh
argument.

* **Walks and connections inside a set.** `mem_localConn_iff_exists_walk` describes a
  connection inside `S` by a walk of open edges with all vertices in `S`, and
  `SimpleGraph.Walk.exists_walk_mem_Icc` is a discrete intermediate value theorem: along a walk
  on which a function changes by at most one per step, a segment runs between any two
  intermediate levels without leaving them.
* **Sub-crossings** (`crossing_zero_subset_crossing_zero`, `crossing_one_subset_crossing_one`):
  a crossing of a box contains a crossing of every box that is narrower in the crossing
  direction and at least as wide in the other.
* **Automorphisms of `ℤ²`**: the coordinate swap and the reflections in a vertical or
  horizontal line, as graph automorphisms with explicit coordinates.
* **Vertical duality** (`mem_crossing_one_iff_dualConfig_notMem_crossing_zero`): a box has an
  open bottom-top crossing exactly when the dual box `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` has no
  dual-open left-right crossing. It is the duality of `Duality.lean` transported by the
  coordinate swap, which commutes with taking duals (`dualConfig_image_swap`).
* **Symmetries of the law** (`law_crossing_eq_of_iso`, `law_crossing_add`,
  `law_crossing_one_eq_law_crossing_zero`): for a profile constant on the edges of `ℤ²`,
  crossing probabilities are invariant under translations, the coordinate swap and
  reflections.
* **Complement of a vertical crossing at `1/2`** (`law_compl_crossing_one_eq`): it has the
  probability of a left-right crossing of a box of the size of the dual box.

## Main results

* `PercLib.Models.Planar.mem_crossing_one_iff_dualConfig_notMem_crossing_zero`
* `PercLib.Models.Planar.crossing_zero_subset_crossing_zero`
* `PercLib.Models.Planar.law_crossing_add`
* `PercLib.Models.Planar.law_crossing_one_eq_law_crossing_zero`
* `PercLib.Models.Planar.law_compl_crossing_one_eq`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site

/-! ### A discrete intermediate value theorem along walks -/

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- **First passage to a level.** If a function increases by at most one along each step of
`G`, a walk starting at or below level `t` and ending at or above it has an initial segment
that ends at level `t` and stays at or below it. -/
theorem exists_walk_eq_of_le (f : V → ℤ) (hf : ∀ u v, G.Adj u v → f v ≤ f u + 1) {t : ℤ} :
    ∀ {a b : V} (p : G.Walk a b), f a ≤ t → t ≤ f b →
      ∃ c, f c = t ∧ ∃ q : G.Walk a c, ∀ v ∈ q.support, v ∈ p.support ∧ f v ≤ t
  | a, _, .nil, ha, hb => ⟨a, le_antisymm ha hb, .nil, fun v hv => by
      rw [support_nil, List.mem_singleton] at hv
      subst hv
      exact ⟨start_mem_support _, ha⟩⟩
  | a, _, .cons h p, ha, hb => by
    rcases ha.eq_or_lt with ha' | ha'
    · refine ⟨a, ha', .nil, fun v hv => ?_⟩
      rw [support_nil, List.mem_singleton] at hv
      subst hv
      exact ⟨start_mem_support _, ha'.le⟩
    · obtain ⟨c, hc, q, hq⟩ := exists_walk_eq_of_le f hf p (by have := hf _ _ h; omega) hb
      refine ⟨c, hc, .cons h q, fun v hv => ?_⟩
      rw [support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨start_mem_support _, ha'.le⟩
      · refine ⟨?_, (hq v hv).2⟩
        rw [support_cons]
        exact List.mem_cons_of_mem _ (hq v hv).1

/-- **Discrete intermediate value theorem along a walk.** If a function changes by at most one
along each step of `G`, a walk from level at most `s` to level at least `t ≥ s` contains a
segment from a vertex at level `s` to a vertex at level `t` all of whose vertices lie between
the two levels. -/
theorem exists_walk_mem_Icc (f : V → ℤ) (hf : ∀ u v, G.Adj u v → f v ≤ f u + 1) {s t : ℤ}
    {a b : V} (p : G.Walk a b) (ha : f a ≤ s) (hst : s ≤ t) (hb : t ≤ f b) :
    ∃ u w, f u = s ∧ f w = t ∧
      ∃ q : G.Walk u w, ∀ v ∈ q.support, v ∈ p.support ∧ s ≤ f v ∧ f v ≤ t := by
  obtain ⟨c, hc, q₁, hq₁⟩ := exists_walk_eq_of_le f hf p (ha.trans hst) hb
  have hf' : ∀ u v, G.Adj u v → -f v ≤ -f u + 1 := fun u v h => by
    have := hf v u h.symm
    omega
  obtain ⟨u, hu, q₂, hq₂⟩ := exists_walk_eq_of_le (t := -s) (fun v => -f v) hf' q₁.reverse
    (show -f c ≤ -s by omega) (show -s ≤ -f a by omega)
  have hu' : -f u = -s := hu
  refine ⟨u, c, by omega, hc, q₂.reverse, fun v hv => ?_⟩
  rw [support_reverse, List.mem_reverse] at hv
  obtain ⟨hv₁, hv₂⟩ := hq₂ v hv
  have hv₂' : -f v ≤ -s := hv₂
  rw [support_reverse, List.mem_reverse] at hv₁
  exact ⟨(hq₁ v hv₁).1, by omega, (hq₁ v hv₁).2⟩

end SimpleGraph.Walk

/-! ### Connections inside a set as walks -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A connection inside `S` is a walk of open edges all of whose vertices lie in `S`. -/
theorem mem_localConn_iff_exists_walk {S : Set V} {x y : V} {ω : Config V} :
    ω ∈ localConn S x y ↔ ∃ p : (openGraph ω).Walk x y, ∀ v ∈ p.support, v ∈ S := by
  constructor
  · rintro ⟨hx, hy, ⟨p⟩⟩
    let p' := p.map (SimpleGraph.Embedding.induce S).toHom
    refine ⟨p', fun v hv => ?_⟩
    change v ∈ p'.support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hv
    subst hw
    exact w.2
  · rintro ⟨p, hp⟩
    induction p with
    | nil =>
      rw [localConn_self (hp _ (SimpleGraph.Walk.start_mem_support _))]
      exact mem_univ _
    | @cons u v w h p ih =>
      have hu : u ∈ S := hp u (SimpleGraph.Walk.start_mem_support _)
      have hv : v ∈ S := hp v (by simp)
      refine localConn_trans ⟨hu, hv, SimpleGraph.Adj.reachable
        (G := (openGraph ω).induce S) (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) h⟩
        (ih fun x hx => hp x ?_)
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ hx

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

/-! ### Sub-crossings -/

/-- One step of the open graph of `ω ∩ L` changes each coordinate by at most one. -/
theorem coord_le_add_one_of_adj {ω : Config (LatticeSite 2)} {u v : LatticeSite 2}
    (h : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj u v) (i : Fin 2) : v i ≤ u i + 1 := by
  have hL := ((openGraph_adj_iff _ u v).1 h).1.2
  rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff] at hL
  fin_cases i <;> simp <;> omega

/-- **Sub-crossings.** A left-right crossing of a box contains a left-right crossing of every
box that is narrower horizontally and at least as tall. -/
theorem crossing_zero_subset_crossing_zero {lo hi lo' hi' : LatticeSite 2}
    (h0 : lo 0 ≤ lo' 0) (h0' : lo' 0 ≤ hi' 0) (h0'' : hi' 0 ≤ hi 0)
    (h1 : lo' 1 ≤ lo 1) (h1' : hi 1 ≤ hi' 1) :
    crossing 0 lo hi ⊆ crossing 0 lo' hi' := by
  rintro ω ⟨a, ha, ha0, b, hb, hb0, hab⟩
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hab
  obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => v 0)
    (fun u v h => coord_le_add_one_of_adj h 0) p (by omega) h0'
    (by omega)
  have hbox : ∀ v ∈ q.support, v ∈ Icc lo' hi' := by
    intro v hv
    obtain ⟨hvp, hv₁, hv₂⟩ := hq v hv
    have := hp v hvp
    rw [mem_Icc_two_iff] at this ⊢
    omega
  exact ⟨u, hbox u (SimpleGraph.Walk.start_mem_support _), hu, w,
    hbox w (SimpleGraph.Walk.end_mem_support _), hw, mem_localConn_iff_exists_walk.2 ⟨q, hbox⟩⟩

/-- **Sub-crossings, vertical form.** -/
theorem crossing_one_subset_crossing_one {lo hi lo' hi' : LatticeSite 2}
    (h1 : lo 1 ≤ lo' 1) (h1' : lo' 1 ≤ hi' 1) (h1'' : hi' 1 ≤ hi 1)
    (h0 : lo' 0 ≤ lo 0) (h0' : hi 0 ≤ hi' 0) :
    crossing 1 lo hi ⊆ crossing 1 lo' hi' := by
  rintro ω ⟨a, ha, ha1, b, hb, hb1, hab⟩
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hab
  obtain ⟨u, w, hu, hw, q, hq⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => v 1)
    (fun u v h => coord_le_add_one_of_adj h 1) p (by omega) h1'
    (by omega)
  have hbox : ∀ v ∈ q.support, v ∈ Icc lo' hi' := by
    intro v hv
    obtain ⟨hvp, hv₁, hv₂⟩ := hq v hv
    have := hp v hvp
    rw [mem_Icc_two_iff] at this ⊢
    omega
  exact ⟨u, hbox u (SimpleGraph.Walk.start_mem_support _), hu, w,
    hbox w (SimpleGraph.Walk.end_mem_support _), hw, mem_localConn_iff_exists_walk.2 ⟨q, hbox⟩⟩

/-! ### Automorphisms of `ℤ²` -/

/-- The coordinate swap is an automorphism of `ℤ²`. -/
theorem exists_iso_swap : ∃ σ : zdGraph 2 ≃g zdGraph 2, ∀ v, σ v = ![v 1, v 0] := by
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_perm (d := 2) (Equiv.swap 0 1)
  refine ⟨φ, fun v => ?_⟩
  rw [hφ, eq_vec_two_iff]
  simp

/-- The reflection in the vertical line `x = a/2` is an automorphism of `ℤ²`. -/
theorem exists_iso_reflect_zero (a : ℤ) :
    ∃ σ : zdGraph 2 ≃g zdGraph 2, ∀ v, σ v = ![a - v 0, v 1] := by
  obtain ⟨φ₁, hφ₁⟩ := exists_zdGraph_iso_neg (d := 2) ![true, false]
  obtain ⟨φ₂, hφ₂⟩ := exists_zdGraph_iso_add (d := 2) ![a, 0]
  refine ⟨φ₁.trans φ₂, fun v => ?_⟩
  rw [RelIso.trans_apply, hφ₂, eq_vec_two_iff]
  constructor <;> simp [hφ₁]; ring

/-- The reflection in the horizontal line `y = b/2` is an automorphism of `ℤ²`. -/
theorem exists_iso_reflect_one (b : ℤ) :
    ∃ σ : zdGraph 2 ≃g zdGraph 2, ∀ v, σ v = ![v 0, b - v 1] := by
  obtain ⟨φ₁, hφ₁⟩ := exists_zdGraph_iso_neg (d := 2) ![false, true]
  obtain ⟨φ₂, hφ₂⟩ := exists_zdGraph_iso_add (d := 2) ![0, b]
  refine ⟨φ₁.trans φ₂, fun v => ?_⟩
  rw [RelIso.trans_apply, hφ₂, eq_vec_two_iff]
  constructor <;> simp [hφ₁]; ring

/-- The coordinate swap maps a box onto the swapped box. -/
theorem image_swap_Icc {σ : zdGraph 2 ≃g zdGraph 2} (hσ : ∀ v, σ v = ![v 1, v 0])
    (lo hi : LatticeSite 2) : σ '' Icc lo hi = Icc ![lo 1, lo 0] ![hi 1, hi 0] := by
  ext w
  simp only [mem_image, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [hσ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · intro hw
    refine ⟨![w 1, w 0], ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [hσ, eq_comm, eq_vec_two_iff]
      simp

/-! ### Transport of crossings with the faces exchanged -/

/-- A crossing read from the high face to the low face. -/
theorem mem_crossing_iff_rev {d : ℕ} (i : Fin d) (lo hi : LatticeSite d)
    (ω : Config (LatticeSite d)) :
    ω ∈ crossing i lo hi ↔ ∃ a ∈ Icc lo hi, a i = hi i ∧ ∃ b ∈ Icc lo hi, b i = lo i ∧
      ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc lo hi) a b := by
  constructor
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    exact ⟨b, hb, hbi, a, ha, hai, by rwa [localConn_comm]⟩
  · rintro ⟨a, ha, hai, b, hb, hbi, hab⟩
    exact ⟨b, hb, hbi, a, ha, hai, by rwa [localConn_comm]⟩

/-- A crossing is carried along an automorphism of `ℤ^d` that maps the box onto a box, the low
face in direction `i` onto the high face in direction `j`, and the high face onto the low
face. -/
theorem image_mem_crossing_iff_of_rev {d : ℕ} (σ : zdGraph d ≃g zdGraph d) {i j : Fin d}
    {lo hi lo' hi' : LatticeSite d} (hbox : σ '' Icc lo hi = Icc lo' hi')
    (hlo : ∀ v ∈ Icc lo hi, σ v j = hi' j ↔ v i = lo i)
    (hhi : ∀ v ∈ Icc lo hi, σ v j = lo' j ↔ v i = hi i) (ω : Config (LatticeSite d)) :
    Sym2.map σ '' ω ∈ crossing j lo' hi' ↔ ω ∈ crossing i lo hi := by
  have hL : Sym2.map σ '' ω ∩ (zdGraph d).edgeSet =
      Sym2.map σ '' (ω ∩ (zdGraph d).edgeSet) := by
    rw [image_inter (Sym2.map.injective σ.injective)]
    congr 1
    exact (image_sym2Map_edgeSet σ).symm
  rw [mem_crossing_iff_rev]
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

/-! ### Vertical duality -/

/-- The coordinate swap commutes with taking the dual edge. -/
theorem dualEdge_map_swap {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    dualEdge (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e) =
      Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) (dualEdge e) := by
  obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal]
    simp only [Sym2.map_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dualEdge_vertical, Sym2.eq_swap]
  · rw [dualEdge_vertical]
    simp only [Sym2.map_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dualEdge_horizontal, Sym2.eq_swap]

/-- The coordinate swap preserves the edges of `ℤ²`. -/
theorem map_swap_mem_edgeSet_iff (e : Sym2 (LatticeSite 2)) :
    Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e ∈ (zdGraph 2).edgeSet ↔
      e ∈ (zdGraph 2).edgeSet := by
  obtain ⟨σ, hσ⟩ := exists_iso_swap
  have h : (⇑σ : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := funext hσ
  rw [← h]
  induction e using Sym2.ind with
  | h u v => exact σ.map_adj_iff

/-- The coordinate swap is an involution of unordered pairs. -/
theorem map_swap_map_swap (e : Sym2 (LatticeSite 2)) :
    Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0])
      (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e) = e := by
  induction e using Sym2.ind with
  | h u v =>
    simp only [Sym2.map_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← eq_vec_two u, ← eq_vec_two v]

/-- **The coordinate swap commutes with taking duals.** -/
theorem dualConfig_image_swap (ω : Config (LatticeSite 2)) :
    dualConfig (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) '' ω) =
      Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) '' dualConfig ω := by
  set sw : Sym2 (LatticeSite 2) → Sym2 (LatticeSite 2) :=
    Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) with hsw
  have hmem : ∀ e, e ∈ sw '' ω ↔ sw e ∈ ω := by
    intro e
    constructor
    · rintro ⟨e', he', rfl⟩
      rwa [hsw, map_swap_map_swap]
    · intro h
      exact ⟨sw e, h, map_swap_map_swap e⟩
  ext f
  rw [mem_dualConfig_iff']
  constructor
  · rintro ⟨e, he, heω, rfl⟩
    rw [hmem] at heω
    refine ⟨dualEdge (sw e), ⟨sw e, ⟨(map_swap_mem_edgeSet_iff e).2 he, heω⟩, rfl⟩, ?_⟩
    rw [hsw, dualEdge_map_swap he, map_swap_map_swap]
  · rintro ⟨g, ⟨e, ⟨he, heω⟩, rfl⟩, rfl⟩
    refine ⟨sw e, (map_swap_mem_edgeSet_iff e).2 he, ?_, dualEdge_map_swap he⟩
    rwa [hmem, hsw, map_swap_map_swap]

/-- **Vertical duality.** A box of `ℤ²` has an open bottom-top crossing exactly when the dual
box `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` has no dual-open left-right crossing. -/
theorem mem_crossing_one_iff_dualConfig_notMem_crossing_zero {lo hi : LatticeSite 2}
    (hle : lo ≤ hi) (ω : Config (LatticeSite 2)) :
    ω ∈ crossing 1 lo hi ↔ dualConfig ω ∉ crossing 0 ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1] := by
  obtain ⟨σ, hσ⟩ := exists_iso_swap
  have hσf : (⇑σ : LatticeSite 2 → LatticeSite 2) = fun v => ![v 1, v 0] := funext hσ
  have hle' : (![lo 1, lo 0] : LatticeSite 2) ≤ ![hi 1, hi 0] := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hle 1, hle 0⟩
  -- transport the crossing to the swapped box
  have h₁ : Sym2.map σ '' ω ∈ crossing 0 ![lo 1, lo 0] ![hi 1, hi 0] ↔ ω ∈ crossing 1 lo hi :=
    image_mem_crossing_iff σ (image_swap_Icc hσ lo hi)
      (fun v _ => by rw [hσ]; simp) (fun v _ => by rw [hσ]; simp) ω
  -- horizontal duality in the swapped box
  have h₂ := mem_crossing_zero_iff_dualConfig_notMem_crossing_one hle' (Sym2.map σ '' ω)
  -- transport the dual crossing back
  have hbox : σ '' Icc (![lo 0 - 1, lo 1] : LatticeSite 2) ![hi 0, hi 1 - 1] =
      Icc ![(![lo 1, lo 0] : LatticeSite 2) 0, (![lo 1, lo 0] : LatticeSite 2) 1 - 1]
        ![(![hi 1, hi 0] : LatticeSite 2) 0 - 1, (![hi 1, hi 0] : LatticeSite 2) 1] := by
    rw [image_swap_Icc hσ]
    simp
  have h₃ : Sym2.map σ '' dualConfig ω ∈ crossing 1
      ![(![lo 1, lo 0] : LatticeSite 2) 0, (![lo 1, lo 0] : LatticeSite 2) 1 - 1]
      ![(![hi 1, hi 0] : LatticeSite 2) 0 - 1, (![hi 1, hi 0] : LatticeSite 2) 1] ↔
      dualConfig ω ∈ crossing 0 ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1] :=
    image_mem_crossing_iff σ hbox (fun v _ => by rw [hσ]; simp) (fun v _ => by rw [hσ]; simp) _
  rw [← h₁, h₂, hσf, dualConfig_image_swap, ← hσf, h₃]

/-- **Vertical duality**, as events. -/
theorem compl_crossing_one_eq_preimage_dualConfig {lo hi : LatticeSite 2} (hle : lo ≤ hi) :
    (crossing 1 lo hi)ᶜ = dualConfig ⁻¹' crossing 0 ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1] := by
  ext ω
  rw [mem_compl_iff, mem_crossing_one_iff_dualConfig_notMem_crossing_zero hle, not_not,
    mem_preimage]

/-! ### Symmetries of crossing probabilities -/

/-- **Invariance of crossing probabilities under automorphisms.** For a profile constant on the
edges of `ℤ^d`, an automorphism carrying one box onto another and the faces in direction `i`
onto those in direction `j` preserves the crossing probability. -/
theorem law_crossing_eq_of_iso {d : ℕ} {q : Sym2 (LatticeSite d) → unitInterval}
    {p : unitInterval} (hq : ∀ e ∈ (zdGraph d).edgeSet, q e = p) (σ : zdGraph d ≃g zdGraph d)
    {i j : Fin d} {lo hi lo' hi' : LatticeSite d} (hbox : σ '' Icc lo hi = Icc lo' hi')
    (hlo : ∀ v ∈ Icc lo hi, σ v j = lo' j ↔ v i = lo i)
    (hhi : ∀ v ∈ Icc lo hi, σ v j = hi' j ↔ v i = hi i) :
    law q (crossing j lo' hi') = law q (crossing i lo hi) := by
  have hpre : crossing i lo hi = (fun ω => Sym2.map σ '' ω) ⁻¹' crossing j lo' hi' := by
    ext ω
    exact (image_mem_crossing_iff σ hbox hlo hhi ω).symm
  have hq' : ∀ e ∈ (zdGraph d).edgeSet, q (Sym2.map σ e) = q e := fun e he => by
    rw [hq e he, hq _ (image_sym2Map_edgeSet σ ▸ mem_image_of_mem _ he)]
  rw [hpre, law_preimage_image_sym2Map_eq σ hq' (measurableSet_crossing _ _ _)
    (inter_edgeSet_mem_crossing_iff _ _ _)]

/-- **Invariance of crossing probabilities under automorphisms exchanging the faces.** -/
theorem law_crossing_eq_of_iso_of_rev {d : ℕ} {q : Sym2 (LatticeSite d) → unitInterval}
    {p : unitInterval} (hq : ∀ e ∈ (zdGraph d).edgeSet, q e = p) (σ : zdGraph d ≃g zdGraph d)
    {i j : Fin d} {lo hi lo' hi' : LatticeSite d} (hbox : σ '' Icc lo hi = Icc lo' hi')
    (hlo : ∀ v ∈ Icc lo hi, σ v j = hi' j ↔ v i = lo i)
    (hhi : ∀ v ∈ Icc lo hi, σ v j = lo' j ↔ v i = hi i) :
    law q (crossing j lo' hi') = law q (crossing i lo hi) := by
  have hpre : crossing i lo hi = (fun ω => Sym2.map σ '' ω) ⁻¹' crossing j lo' hi' := by
    ext ω
    exact (image_mem_crossing_iff_of_rev σ hbox hlo hhi ω).symm
  have hq' : ∀ e ∈ (zdGraph d).edgeSet, q (Sym2.map σ e) = q e := fun e he => by
    rw [hq e he, hq _ (image_sym2Map_edgeSet σ ▸ mem_image_of_mem _ he)]
  rw [hpre, law_preimage_image_sym2Map_eq σ hq' (measurableSet_crossing _ _ _)
    (inter_edgeSet_mem_crossing_iff _ _ _)]

/-- **Translation invariance of crossing probabilities.** -/
theorem law_crossing_add {d : ℕ} {q : Sym2 (LatticeSite d) → unitInterval} {p : unitInterval}
    (hq : ∀ e ∈ (zdGraph d).edgeSet, q e = p) (i : Fin d) (lo hi c : LatticeSite d) :
    law q (crossing i (lo + c) (hi + c)) = law q (crossing i lo hi) := by
  obtain ⟨σ, hσ⟩ := exists_zdGraph_iso_add (d := d) c
  have hσf : (⇑σ : LatticeSite d → LatticeSite d) = fun v => v + c := funext hσ
  refine law_crossing_eq_of_iso hq σ ?_ (fun v _ => ?_) (fun v _ => ?_)
  · rw [hσf, image_add_const_Icc]
  · rw [hσ, Pi.add_apply, Pi.add_apply, add_left_inj]
  · rw [hσ, Pi.add_apply, Pi.add_apply, add_left_inj]

/-- **Swap invariance of crossing probabilities.** A bottom-top crossing of a box has the
probability of a left-right crossing of the swapped box. -/
theorem law_crossing_one_eq_law_crossing_zero {q : Sym2 (LatticeSite 2) → unitInterval}
    {p : unitInterval} (hq : ∀ e ∈ (zdGraph 2).edgeSet, q e = p) (lo hi : LatticeSite 2) :
    law q (crossing 1 lo hi) = law q (crossing 0 ![lo 1, lo 0] ![hi 1, hi 0]) := by
  obtain ⟨σ, hσ⟩ := exists_iso_swap
  exact (law_crossing_eq_of_iso hq σ (image_swap_Icc hσ lo hi)
    (fun v _ => by rw [hσ]; simp) (fun v _ => by rw [hσ]; simp)).symm

/-- **Reflection invariance of crossing probabilities**, in a vertical line. -/
theorem law_crossing_reflect_zero {q : Sym2 (LatticeSite 2) → unitInterval} {p : unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, q e = p) (i : Fin 2) (a : ℤ) (lo hi : LatticeSite 2) :
    law q (crossing i ![a - hi 0, lo 1] ![a - lo 0, hi 1]) = law q (crossing i lo hi) := by
  obtain ⟨σ, hσ⟩ := exists_iso_reflect_zero a
  have hbox : σ '' Icc lo hi = Icc ![a - hi 0, lo 1] ![a - lo 0, hi 1] := by
    ext w
    simp only [mem_image, mem_Icc_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hσ]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · intro hw
      refine ⟨![a - w 0, w 1], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
      · rw [hσ, eq_comm, eq_vec_two_iff]
        simp
  fin_cases i
  · refine law_crossing_eq_of_iso_of_rev hq σ hbox (fun v _ => ?_) (fun v _ => ?_)
    · rw [hσ]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      omega
    · rw [hσ]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      omega
  · refine law_crossing_eq_of_iso hq σ hbox (fun v _ => ?_) (fun v _ => ?_)
    · rw [hσ]
      simp
    · rw [hσ]
      simp

/-- **Reflection invariance of crossing probabilities**, in a horizontal line. -/
theorem law_crossing_reflect_one {q : Sym2 (LatticeSite 2) → unitInterval} {p : unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, q e = p) (i : Fin 2) (b : ℤ) (lo hi : LatticeSite 2) :
    law q (crossing i ![lo 0, b - hi 1] ![hi 0, b - lo 1]) = law q (crossing i lo hi) := by
  obtain ⟨σ, hσ⟩ := exists_iso_reflect_one b
  have hbox : σ '' Icc lo hi = Icc ![lo 0, b - hi 1] ![hi 0, b - lo 1] := by
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
  fin_cases i
  · refine law_crossing_eq_of_iso hq σ hbox (fun v _ => ?_) (fun v _ => ?_)
    · rw [hσ]
      simp
    · rw [hσ]
      simp
  · refine law_crossing_eq_of_iso_of_rev hq σ hbox (fun v _ => ?_) (fun v _ => ?_)
    · rw [hσ]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · rw [hσ]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega

/-! ### The complement of a vertical crossing at one half -/

/-- **The complement of a vertical crossing at `1/2`.** If every edge of `ℤ²` is open with
probability `1/2`, a box has no open bottom-top crossing with the probability that the box
`[0, hi₀ - lo₀ + 1] × [0, hi₁ - lo₁ - 1]`, of the size of the dual box, has an open left-right
crossing. -/
theorem law_compl_crossing_one_eq {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {lo hi : LatticeSite 2} (hle : lo ≤ hi) :
    law q (crossing 1 lo hi)ᶜ = law q (crossing 0 0 ![hi 0 - lo 0 + 1, hi 1 - lo 1 - 1]) := by
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q e = ⟨1 / 2, by norm_num, by norm_num⟩ :=
    fun e he => Subtype.ext (hq e he)
  rw [compl_crossing_one_eq_preimage_dualConfig hle,
    law_preimage_dualConfig_eq hq (measurableSet_crossing _ _ _)
      (inter_edgeSet_mem_crossing_iff _ _ _)]
  have h := law_crossing_add hq' 0 0 ![hi 0 - lo 0 + 1, hi 1 - lo 1 - 1] ![lo 0 - 1, lo 1]
  rw [← h]
  congr 2
  · rw [zero_add]
  · rw [vec_two_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1 <;> ring_nf

end PercLib.Models.Planar
