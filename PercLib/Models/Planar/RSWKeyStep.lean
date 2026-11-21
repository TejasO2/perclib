/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: B. Bollobás and O. Riordan, A short proof of the Harris-Kesten theorem,
Bull. London Math. Soc. 38 (2006), 470-484 (arXiv math/0410359v3), Lemma 6.
-/
module

public import PercLib.Models.Planar.Gluing
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Probability.DeterminedIndependence

/-!
# The key step of the Russo–Seymour–Welsh argument

For `1 ≤ n ≤ m`, let `S = [0, n]²` and `R = [0, m] × [0, 2n]`. For bond percolation with any
profile constant on the edges of `ℤ²`,
`P(H(R)) · P(V(S)) ≤ 2 · P(X(R))`, where `H` and `V` are left-right and bottom-top crossings
and `X(R)` is the event that some vertex `c` of `S` is joined inside `S` to the bottom and to
the top of `S`, and inside `R` to the right side of `R`
(`law_crossing_zero_mul_law_crossing_one_le`). This is Lemma 6 of Bollobás and Riordan.

The proof conditions on the dual cluster `D` of the left column of the dual box
`Sv = [-1, n] × [0, n - 1]`, with the left column wired by its own dual edges. The event
`D = D₀` depends only on the edges whose duals meet `D₀`. When `D₀` avoids the right column
of `Sv`, the edges of `ℤ²` leaving `D₀` (`∂D₀`) contain a bottom-top crossing `γ₀` of `S`
(`mem_crossing_one_boundary`), open on `{D = D₀}`. Every left-right crossing of `R` reaches
`γ₀` or its reflection in the line `y = n` along edges not explored by `D₀`
(`exists_mem_localConn_explored_compl`); this uses the separation lemma of `Gluing.lean`, with
the dual path inside `D₀`. Independence and the reflection symmetry give the inequality.

## Main results

* `PercLib.Models.Planar.law_crossing_zero_mul_law_crossing_one_le`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability

/-! ### First visit to a set along a walk -/

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- **First visit.** If a walk visits a set, it has an initial segment that ends at its first
visit to the set. -/
theorem exists_walk_first_mem (P : V → Prop) :
    ∀ {a b : V} (p : G.Walk a b), (∃ x ∈ p.support, P x) →
      ∃ c, P c ∧ ∃ q : G.Walk a c, (∀ v ∈ q.support, v ∈ p.support) ∧
        (∀ e ∈ q.edges, e ∈ p.edges) ∧ ∀ v ∈ q.support, P v → v = c
  | a, _, .nil, ⟨x, hx, hPx⟩ => by
    rw [support_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨x, hPx, .nil, by simp, by simp, by simp⟩
  | a, _, .cons h p, ⟨x, hx, hPx⟩ => by
    by_cases hPa : P a
    · exact ⟨a, hPa, .nil, by simp, by simp, by simp⟩
    · have hx' : ∃ x ∈ p.support, P x := by
        rw [support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd hPx hPa
        · exact ⟨x, hx, hPx⟩
      obtain ⟨c, hc, q, hq₁, hq₂, hq₃⟩ := exists_walk_first_mem P p hx'
      refine ⟨c, hc, .cons h q, fun v hv => ?_, fun e he => ?_, fun v hv hPv => ?_⟩
      · rw [support_cons, List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (hq₁ v hv)
      · rw [edges_cons, List.mem_cons] at he ⊢
        rcases he with rfl | he
        · exact Or.inl rfl
        · exact Or.inr (hq₂ e he)
      · rw [support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact absurd hPv hPa
        · exact hq₃ v hv hPv

end SimpleGraph.Walk

namespace PercLib.Models.Planar

/-! ### Walks of `ℤ²` and connections -/

/-- A connection inside `S` through open nearest-neighbour edges is a walk of `ℤ²` in `S` all of
whose edges are open. -/
theorem exists_walk_of_mem_localConn {d : ℕ} {ω : Config (LatticeSite d)}
    {S : Set (LatticeSite d)} {a b : LatticeSite d}
    (h : ω ∩ (zdGraph d).edgeSet ∈ localConn S a b) :
    ∃ p : (zdGraph d).Walk a b, (∀ v ∈ p.support, v ∈ S) ∧ ∀ e ∈ p.edges, e ∈ ω := by
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 h
  have hedge : ∀ e ∈ p.edges, e ∈ ω ∩ (zdGraph d).edgeSet := fun e he => by
    have := p.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  refine ⟨p.transfer _ fun e he => (hedge e he).2, fun v hv => ?_, fun e he => ?_⟩
  · rw [SimpleGraph.Walk.support_transfer] at hv
    exact hp v hv
  · rw [SimpleGraph.Walk.edges_transfer] at he
    exact (hedge e he).1

/-- A walk of `ℤ²` in `S` all of whose edges are open gives a connection inside `S`. -/
theorem mem_localConn_of_walk {d : ℕ} {ω : Config (LatticeSite d)} {S : Set (LatticeSite d)}
    {a b : LatticeSite d} (p : (zdGraph d).Walk a b) (hp : ∀ v ∈ p.support, v ∈ S)
    (hω : ∀ e ∈ p.edges, e ∈ ω) : ω ∩ (zdGraph d).edgeSet ∈ localConn S a b := by
  refine mem_localConn_iff_exists_walk.2 ⟨p.transfer _ fun e he => ?_, ?_⟩
  · rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨hω e he, p.edges_subset_edgeSet he⟩,
      SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩
  · intro v hv
    rw [SimpleGraph.Walk.support_transfer] at hv
    exact hp v hv

/-- The two ends of an edge of a walk are distinct vertices of the walk. -/
theorem exists_ne_of_mem_edges {d : ℕ} {a b : LatticeSite d} (p : (zdGraph d).Walk a b)
    {e : Sym2 (LatticeSite d)} (he : e ∈ p.edges) :
    ∃ x y, e = s(x, y) ∧ x ≠ y ∧ x ∈ p.support ∧ y ∈ p.support := by
  induction e using Sym2.ind with
  | h x y =>
    refine ⟨x, y, rfl, ?_, p.fst_mem_support_of_mem_edges he,
      p.snd_mem_support_of_mem_edges he⟩
    exact ((zdGraph d).mem_edgeSet.1 (p.edges_subset_edgeSet he)).ne

/-! ### Faces of dual edges -/

/-- The ends of the dual of an edge are faces at each end of the edge. -/
theorem face_of_mem_dualEdge {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    {v f : LatticeSite 2} (hv : v ∈ e) (hf : f ∈ dualEdge e) :
    v 0 - 1 ≤ f 0 ∧ f 0 ≤ v 0 ∧ v 1 - 1 ≤ f 1 ∧ f 1 ≤ v 1 := by
  obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal] at hf
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> rcases Sym2.mem_iff.1 hf with rfl | rfl <;>
      simp
  · rw [dualEdge_vertical] at hf
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> rcases Sym2.mem_iff.1 hf with rfl | rfl <;>
      simp

/-- An edge whose dual lies in the rows `≤ t` has an end in the rows `≤ t`. -/
theorem exists_mem_le_of_dualEdge {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    {t : ℤ} (h : ∀ f ∈ dualEdge e, f 1 ≤ t) : ∃ v ∈ e, v 1 ≤ t := by
  obtain ⟨x, y, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal] at h
    exact ⟨![x, y], Sym2.mem_mk_left _ _, by simpa using h _ (Sym2.mem_mk_right _ _)⟩
  · rw [dualEdge_vertical] at h
    exact ⟨![x, y], Sym2.mem_mk_left _ _, by simpa using h _ (Sym2.mem_mk_left _ _)⟩

/-- The primal edge of a dual edge of `ℤ²`. -/
theorem exists_dualEdge_eq {s : Sym2 (LatticeSite 2)} (hs : s ∈ (zdGraph 2).edgeSet) :
    ∃ e ∈ (zdGraph 2).edgeSet, dualEdge e = s :=
  ⟨_, map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hs), by
    rw [dualEdge_map_add, map_add_one_dualEdge_dualEdge hs]⟩

/-! ### The boundary of a dual cluster contains a crossing -/

/-- **The boundary of a dual set crossing the dual box.** Let `D₀` be a set of faces of
`Sv = [-1, n] × [0, n - 1]` that contains the left column and avoids the right column. The
edges of `ℤ²` whose duals lie in `Sv` and leave `D₀` cross the square `[0, n]²` from bottom
to top. -/
theorem mem_crossing_one_boundary {n : ℕ} {D₀ : Set (LatticeSite 2)}
    (hleft : ∀ y : ℤ, 0 ≤ y → y ≤ n - 1 → ![-1, y] ∈ D₀)
    (hright : ∀ f ∈ D₀, f 0 ≠ n) :
    {e | e ∈ (zdGraph 2).edgeSet ∧
        (∀ f ∈ dualEdge e, f ∈ Icc (![-1, 0] : LatticeSite 2) ![(n : ℤ), n - 1]) ∧
        (∃ f ∈ dualEdge e, f ∈ D₀) ∧ ∃ f ∈ dualEdge e, f ∉ D₀} ∈
      crossing 1 0 ![(n : ℤ), n] := by
  set B : Config (LatticeSite 2) := {e | e ∈ (zdGraph 2).edgeSet ∧
    (∀ f ∈ dualEdge e, f ∈ Icc (![-1, 0] : LatticeSite 2) ![(n : ℤ), n - 1]) ∧
    (∃ f ∈ dualEdge e, f ∈ D₀) ∧ ∃ f ∈ dualEdge e, f ∉ D₀} with hB
  have hle : (0 : LatticeSite 2) ≤ ![(n : ℤ), n] := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp
  rw [mem_crossing_one_iff_dualConfig_notMem_crossing_zero hle]
  rintro ⟨a, ha, ha0, b, hb, hb0, hab⟩
  simp only [Pi.zero_apply, zero_sub, Matrix.cons_val_zero,
    Matrix.cons_val_one] at ha ha0 hb hb0 hab
  obtain ⟨p, hp, hpω⟩ := exists_walk_of_mem_localConn hab
  have haD : a ∈ D₀ := by
    rw [mem_Icc_two_iff] at ha
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
    have := hleft (a 1) (by omega) (by omega)
    rwa [← eq_vec_two_iff.2 ⟨ha0, rfl⟩] at this
  have hbD : b ∉ D₀ := fun h => hright b h (by simpa using hb0)
  obtain ⟨δ, hδ, hδ₁, hδ₂⟩ := p.exists_boundary_dart D₀ haD hbD
  have hδe : δ.edge ∈ p.edges := List.mem_map_of_mem hδ
  have hfst := hp _ (p.dart_fst_mem_support_of_mem_darts hδ)
  have hsnd := hp _ (p.dart_snd_mem_support_of_mem_darts hδ)
  have hopen := hpω _ hδe
  obtain ⟨e, heL, hee⟩ := exists_dualEdge_eq (p.edges_subset_edgeSet hδe)
  rw [← hee, dualEdge_mem_dualConfig_iff heL] at hopen
  apply hopen
  have hδedge : δ.edge = s(δ.fst, δ.snd) := rfl
  rw [hδedge] at hee
  refine ⟨heL, fun f hf => ?_, ⟨δ.fst, by rw [hee]; exact Sym2.mem_mk_left _ _, hδ₁⟩,
    ⟨δ.snd, by rw [hee]; exact Sym2.mem_mk_right _ _, hδ₂⟩⟩
  rw [hee, Sym2.mem_iff] at hf
  rw [mem_Icc_two_iff] at hfst hsnd ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfst hsnd ⊢
  rcases hf with rfl | rfl
  · omega
  · omega

/-! ### Every left-right crossing reaches the chosen crossing -/

/-- **Separation in the key step.** Let `D₀ ⊆ Sv = [-1, n] × [0, n - 1]` be a set of faces
joined to the left column by walks inside `D₀`, and let `γ` be a bottom-top walk of `[0, n]²`
each of whose edges has a dual end outside `D₀`. Let `ρ` be the reflection in `y = n`. Every
left-right crossing of `R = [0, m] × [0, 2n]` in `ω` gives, in `ω` or in its reflection, a walk
inside `R` from the right side of `R` to a vertex of `γ` along edges that are open and
unexplored: neither their duals nor the duals of their reflections meet `D₀`. -/
theorem exists_walk_unexplored {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    {D₀ : Set (LatticeSite 2)} (hD₀ : D₀ ⊆ Icc (![-1, 0] : LatticeSite 2) ![(n : ℤ), n - 1])
    (hconn : ∀ f ∈ D₀, ∃ f₀ : LatticeSite 2, f₀ 0 = -1 ∧
      ∃ p : (zdGraph 2).Walk f₀ f, ∀ v ∈ p.support, v ∈ D₀)
    {c₀ d₀ : LatticeSite 2} (γ : (zdGraph 2).Walk c₀ d₀) (hc₀ : c₀ 1 = 0) (hd₀ : d₀ 1 = n)
    (hγS : ∀ v ∈ γ.support, v ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n])
    (hγ : ∀ e ∈ γ.edges, ∃ f ∈ dualEdge e, f ∉ D₀)
    (ρ : zdGraph 2 ≃g zdGraph 2) (hρ : ∀ v, ρ v = ![v 0, 2 * n - v 1])
    {ω : Config (LatticeSite 2)} (hω : ω ∈ crossing 0 0 ![(m : ℤ), 2 * n]) :
    ∃ ω' ∈ ({ω, Sym2.map ρ '' ω} : Set (Config (LatticeSite 2))),
      ∃ u ∈ Icc (0 : LatticeSite 2) ![(m : ℤ), 2 * n], u 0 = m ∧ ∃ g ∈ γ.support,
        ∃ σ : (zdGraph 2).Walk u g,
          (∀ v ∈ σ.support, v ∈ Icc (0 : LatticeSite 2) ![(m : ℤ), 2 * n]) ∧
          ∀ e ∈ σ.edges, e ∈ ω' ∧ (∀ f ∈ dualEdge e, f ∉ D₀) ∧
            ∀ f ∈ dualEdge (Sym2.map ρ e), f ∉ D₀ := by
  classical
  set R : Set (LatticeSite 2) := Icc 0 ![(m : ℤ), 2 * n] with hR
  have hRiff : ∀ v : LatticeSite 2, v ∈ R ↔ 0 ≤ v 0 ∧ v 0 ≤ m ∧ 0 ≤ v 1 ∧ v 1 ≤ 2 * n := by
    intro v
    rw [hR, mem_Icc_two_iff]
    simp
  have hSiff : ∀ v : LatticeSite 2, v ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n] ↔
      0 ≤ v 0 ∧ v 0 ≤ n ∧ 0 ≤ v 1 ∧ v 1 ≤ n := by
    intro v
    rw [mem_Icc_two_iff]
    simp
  have hSviff : ∀ v : LatticeSite 2, v ∈ Icc (![-1, 0] : LatticeSite 2) ![(n : ℤ), n - 1] ↔
      -1 ≤ v 0 ∧ v 0 ≤ n ∧ 0 ≤ v 1 ∧ v 1 ≤ n - 1 := by
    intro v
    rw [mem_Icc_two_iff]
    simp
  have hρ0 : ∀ v, ρ v 0 = v 0 := fun v => by rw [hρ]; simp
  have hρ1 : ∀ v, ρ v 1 = 2 * n - v 1 := fun v => by rw [hρ]; simp
  have hρρ : ∀ v, ρ (ρ v) = v := fun v => by
    funext i
    fin_cases i
    · change ρ (ρ v) 0 = v 0
      rw [hρ0, hρ0]
    · change ρ (ρ v) 1 = v 1
      rw [hρ1, hρ1]
      ring
  have hρR : ∀ v, v ∈ R → ρ v ∈ R := fun v hv => by
    rw [hRiff] at hv ⊢
    rw [hρ0, hρ1]
    omega
  obtain ⟨a, ha, ha0, b, hb, hb0, hab⟩ := hω
  obtain ⟨π, hπR, hπω⟩ := exists_walk_of_mem_localConn hab
  -- the bottom-top walk `τ` of `R`: `γ` followed by its reflection
  have hρd : ρ.toHom d₀ = d₀ := by
    change ρ d₀ = d₀
    funext i
    fin_cases i
    · change ρ d₀ 0 = d₀ 0
      rw [hρ0]
    · change ρ d₀ 1 = d₀ 1
      rw [hρ1, hd₀]
      ring
  set γρ := (γ.map ρ.toHom).copy rfl hρd with hγρ
  set τ := γ.append γρ.reverse with hτ
  have hτsupp : ∀ v, v ∈ τ.support ↔ v ∈ γ.support ∨ ρ v ∈ γ.support := by
    intro v
    rw [hτ, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse, hγρ, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    refine or_congr Iff.rfl ⟨?_, fun h => ⟨ρ v, h, hρρ v⟩⟩
    rintro ⟨w, hw, rfl⟩
    change ρ (ρ w) ∈ γ.support
    rwa [hρρ]
  have hτedges : ∀ e ∈ τ.edges, e ∈ γ.edges ∨ ∃ e' ∈ γ.edges, Sym2.map ρ e' = e := by
    intro e he
    rw [hτ, SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse, hγρ, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
      List.mem_map] at he
    exact he
  have hτR : ∀ v ∈ τ.support, v ∈ R := by
    intro v hv
    rcases (hτsupp v).1 hv with h | h
    · have := (hSiff v).1 (hγS v h)
      rw [hRiff]
      omega
    · have := (hSiff _).1 (hγS _ h)
      rw [hρ0, hρ1] at this
      rw [hRiff]
      omega
  have h1 : (0 : LatticeSite 2) 1 < (![(m : ℤ), 2 * n] : LatticeSite 2) 1 := by
    simp only [Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    have := hn
    omega
  have hτc : c₀ 1 = (0 : LatticeSite 2) 1 := by rw [hc₀]; rfl
  have hτd : (ρ.toHom c₀) 1 = (![(m : ℤ), 2 * n] : LatticeSite 2) 1 := by
    change ρ c₀ 1 = _
    rw [hρ1, hc₀]
    simp
  -- `π` meets `τ`
  obtain ⟨x₀, hx₀π, hx₀τ⟩ :=
    exists_mem_support_of_crossing_walks h1 π τ hπR hτR ha0 hb0 hτc hτd
  -- the vertices touched by explored edges
  set U : Set (LatticeSite 2) := {v | ∃ e ∈ (zdGraph 2).edgeSet, v ∈ e ∧ ∃ f ∈ dualEdge e, f ∈ D₀}
    with hU
  set P : LatticeSite 2 → Prop := fun v => v ∈ τ.support ∨ v ∈ U ∨ ρ v ∈ U with hP
  -- the first visit of the reversed crossing to `τ ∪ U ∪ ρU`
  obtain ⟨k, hPk, σ, hσsupp, hσedges, hσfirst⟩ :=
    SimpleGraph.Walk.exists_walk_first_mem P π.reverse
      ⟨x₀, by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse], Or.inl hx₀τ⟩
  have hσR : ∀ v ∈ σ.support, v ∈ R := fun v hv => by
    have := hσsupp v hv
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
    exact hπR v this
  have hσω : ∀ e ∈ σ.edges, e ∈ ω := fun e he => by
    have := hσedges e he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
    exact hπω e this
  -- the dual path inside `D₀` crosses no edge of `τ`
  have hdual : ∀ f ∈ D₀, ∃ f₀ : LatticeSite 2, f₀ 0 = -1 ∧
      dualConfig {e | e ∈ τ.edges} ∩ (zdGraph 2).edgeSet ∈
        localConn (Icc (![(0 : LatticeSite 2) 0 - 1, (0 : LatticeSite 2) 1] : LatticeSite 2)
          ![(![(m : ℤ), 2 * n] : LatticeSite 2) 0, (![(m : ℤ), 2 * n] : LatticeSite 2) 1 - 1])
          f₀ f := by
    intro f hf
    obtain ⟨f₀, hf₀, p₀, hp₀⟩ := hconn f hf
    refine ⟨f₀, hf₀, mem_localConn_of_walk p₀ (fun v hv => ?_) (fun s hs => ?_)⟩
    · have := (hSviff v).1 (hD₀ (hp₀ v hv))
      rw [mem_Icc_two_iff]
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · obtain ⟨y₁, y₂, rfl, -, hy₁, hy₂⟩ := exists_ne_of_mem_edges p₀ hs
      obtain ⟨e', he'L, he's⟩ := exists_dualEdge_eq (p₀.edges_subset_edgeSet hs)
      rw [← he's, dualEdge_mem_dualConfig_iff he'L]
      intro he'τ
      rcases hτedges e' he'τ with he'γ | ⟨e'', he''γ, rfl⟩
      · obtain ⟨g, hg, hgD⟩ := hγ _ he'γ
        rw [he's, Sym2.mem_iff] at hg
        rcases hg with rfl | rfl
        · exact hgD (hp₀ _ hy₁)
        · exact hgD (hp₀ _ hy₂)
      · obtain ⟨v, hv, hv1⟩ := exists_mem_le_of_dualEdge he'L (t := n - 1) (fun g hg => by
          rw [he's, Sym2.mem_iff] at hg
          rcases hg with rfl | rfl
          · exact ((hSviff _).1 (hD₀ (hp₀ _ hy₁))).2.2.2
          · exact ((hSviff _).1 (hD₀ (hp₀ _ hy₂))).2.2.2)
        obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hv
        have hwS := (hSiff w).1 (hγS w (mem_support_of_mem_edge γ he''γ hw))
        rw [hρ1] at hv1
        omega
  -- the first visited vertex lies on `τ`
  have hkτ : k ∈ τ.support := by
    rcases hPk with h | h | h
    · exact h
    · obtain ⟨e, heL, hke, f, hfe, hfD⟩ := h
      obtain ⟨f₀, hf₀, hpath⟩ := hdual f hfD
      obtain ⟨v, hvσ, hvτ⟩ := exists_mem_support_of_dualConfig_mem_localConn h1 τ hτR hτc hτd
        σ hσR hb0 (f₀ := f₀) (by simpa using hf₀) (face_of_mem_dualEdge heL hke hfe) hpath
      rwa [← hσfirst v hvσ (Or.inl hvτ)]
    · obtain ⟨e, heL, hke, f, hfe, hfD⟩ := h
      obtain ⟨f₀, hf₀, hpath⟩ := hdual f hfD
      have hσρR : ∀ v ∈ (σ.map ρ.toHom).support, v ∈ R := by
        intro v hv
        rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact hρR w (hσR w hw)
      obtain ⟨v, hvσ, hvτ⟩ := exists_mem_support_of_dualConfig_mem_localConn h1 τ hτR hτc hτd
        (σ.map ρ.toHom) hσρR (by change ρ b 0 = _; rw [hρ0]; exact hb0) (f₀ := f₀)
        (by simpa using hf₀) (face_of_mem_dualEdge heL hke hfe) hpath
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hvσ
      obtain ⟨w, hwσ, rfl⟩ := hvσ
      have hwτ : w ∈ τ.support := by
        rw [hτsupp] at hvτ ⊢
        change ρ w ∈ γ.support ∨ ρ (ρ w) ∈ γ.support at hvτ
        rw [hρρ] at hvτ
        exact hvτ.symm
      rwa [← hσfirst w hwσ (Or.inl hwτ)]
  -- the edges of `σ` are unexplored
  have hunexp : ∀ e ∈ σ.edges,
      (∀ f ∈ dualEdge e, f ∉ D₀) ∧ ∀ f ∈ dualEdge (Sym2.map ρ e), f ∉ D₀ := by
    intro e he
    obtain ⟨x, y, rfl, hxy, hx, hy⟩ := exists_ne_of_mem_edges σ he
    have heL : s(x, y) ∈ (zdGraph 2).edgeSet := σ.edges_subset_edgeSet he
    have heρL : Sym2.map ρ s(x, y) ∈ (zdGraph 2).edgeSet :=
      image_sym2Map_edgeSet ρ ▸ mem_image_of_mem _ heL
    refine ⟨fun f hf hfD => hxy ?_, fun f hf hfD => hxy ?_⟩
    · rw [hσfirst x hx (Or.inr (Or.inl ⟨_, heL, Sym2.mem_mk_left _ _, f, hf, hfD⟩)),
        hσfirst y hy (Or.inr (Or.inl ⟨_, heL, Sym2.mem_mk_right _ _, f, hf, hfD⟩))]
    · rw [hσfirst x hx (Or.inr (Or.inr ⟨_, heρL, by simp, f, hf, hfD⟩)),
        hσfirst y hy (Or.inr (Or.inr ⟨_, heρL, by simp, f, hf, hfD⟩))]
  rcases (hτsupp k).1 hkτ with hkγ | hkγ
  · exact ⟨ω, Or.inl rfl, b, hb, hb0, k, hkγ, σ, hσR, fun e he => ⟨hσω e he, hunexp e he⟩⟩
  · refine ⟨Sym2.map ρ '' ω, Or.inr rfl, ρ b, hρR b hb, by rw [hρ0]; exact hb0, ρ k, hkγ,
      σ.map ρ.toHom, fun v hv => ?_, fun e he => ?_⟩
    · rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact hρR w (hσR w hw)
    · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      have hcomp : ((⇑ρ : LatticeSite 2 → LatticeSite 2) ∘ ⇑ρ) = id := funext hρρ
      have hmap : Sym2.map ρ (Sym2.map ρ e') = e' := by
        rw [Sym2.map_map, hcomp, Sym2.map_id, id]
      change Sym2.map ρ e' ∈ Sym2.map ρ '' ω ∧ (∀ f ∈ dualEdge (Sym2.map ρ e'), f ∉ D₀) ∧
        ∀ f ∈ dualEdge (Sym2.map ρ (Sym2.map ρ e')), f ∉ D₀
      rw [hmap]
      exact ⟨mem_image_of_mem _ (hσω e' he'), (hunexp e' he').2, (hunexp e' he').1⟩

end PercLib.Models.Planar
