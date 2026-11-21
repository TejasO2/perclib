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
(`exists_walk_unexplored`); this uses the separation lemma of `Gluing.lean`, with
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

/-! ### The key step -/

/-- **RSW key step** (Bollobás–Riordan, Lemma 6). For `1 ≤ n ≤ m` and any profile constant on
the edges of `ℤ²`, let `S = [0, n]²` and `R = [0, m] × [0, 2n]`. Then
`P(H(R)) · P(V(S)) ≤ 2 · P(X(R))`, where `X(R)` is the event that some vertex `c` of `S` is
joined inside `S` to the bottom and to the top of `S`, and inside `R` to the right side of
`R`. -/
theorem law_crossing_zero_mul_law_crossing_one_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {p : unitInterval} (hq : ∀ e ∈ (zdGraph 2).edgeSet, q e = p) {n m : ℕ} (hn : 1 ≤ n)
    (hnm : n ≤ m) :
    law q (crossing 0 0 ![(m : ℤ), 2 * n]) * law q (crossing 1 0 ![(n : ℤ), n]) ≤
      2 * law q {ω | ∃ c ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n],
        (∃ a ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n], a 1 = 0 ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc 0 ![(n : ℤ), n]) a c) ∧
        (∃ b ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n], b 1 = n ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc 0 ![(n : ℤ), n]) c b) ∧
        (∃ r ∈ Icc (0 : LatticeSite 2) ![(m : ℤ), 2 * n], r 0 = m ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc 0 ![(m : ℤ), 2 * n]) c r)} := by
  classical
  set L := (zdGraph 2).edgeSet with hL
  set S : Set (LatticeSite 2) := Icc 0 ![(n : ℤ), n] with hS
  set R : Set (LatticeSite 2) := Icc 0 ![(m : ℤ), 2 * n] with hR
  set a₀ : LatticeSite 2 := ![-1, 0] with ha₀
  set Sv : Set (LatticeSite 2) := Icc a₀ ![(n : ℤ), n - 1] with hSv
  set X : Set (Config (LatticeSite 2)) := {ω | ∃ c ∈ S,
    (∃ a ∈ S, a 1 = 0 ∧ ω ∩ L ∈ localConn S a c) ∧ (∃ b ∈ S, b 1 = n ∧ ω ∩ L ∈ localConn S c b) ∧
    (∃ r ∈ R, r 0 = m ∧ ω ∩ L ∈ localConn R c r)} with hX
  set W : Config (LatticeSite 2) :=
    {s | ∃ y : ℤ, 0 ≤ y ∧ y + 1 ≤ n - 1 ∧ s = s(![-1, y], ![-1, y + 1])} with hW
  set ζ : Config (LatticeSite 2) → Config (LatticeSite 2) :=
    fun ω => dualConfig ω ∩ {s | ∀ v ∈ s, v ∈ Sv} ∪ W with hζ
  set D : Config (LatticeSite 2) → Set (LatticeSite 2) := fun ω => cluster (ζ ω) a₀ with hD
  have hSviff : ∀ v : LatticeSite 2, v ∈ Sv ↔ -1 ≤ v 0 ∧ v 0 ≤ n ∧ 0 ≤ v 1 ∧ v 1 ≤ n - 1 := by
    intro v
    rw [hSv, ha₀, mem_Icc_two_iff]
    simp
  have ha₀Sv : a₀ ∈ Sv := by
    rw [hSviff, ha₀]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  -- the configuration `ζ ω`: dual-open edges inside `Sv`, and the left column wired
  have hWSv : ∀ s ∈ W, ∀ v ∈ s, v ∈ Sv ∧ v 0 = -1 := by
    rintro s ⟨y, hy0, hy1, rfl⟩ v hv
    rw [Sym2.mem_iff] at hv
    rw [hSviff]
    rcases hv with rfl | rfl <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      and_true] <;> omega
  have hζSv : ∀ ω, ∀ s ∈ ζ ω, ∀ v ∈ s, v ∈ Sv := by
    intro ω s hs v hv
    rcases hs with ⟨-, hs⟩ | hs
    · exact hs v hv
    · exact (hWSv s hs v hv).1
  have hζL : ∀ ω, ζ ω ⊆ L := by
    intro ω s hs
    rcases hs with ⟨hs, -⟩ | ⟨y, -, -, rfl⟩
    · exact dualConfig_subset_edgeSet ω hs
    · exact vertical_mem_edgeSet (-1) y
  have hζmeas : Measurable ζ := by
    refine Measurable.of_mem fun s => ?_
    simp only [hζ, mem_union, mem_inter_iff]
    exact (((measurable_set_mem s).comp measurable_dualConfig).and measurable_const).or
      measurable_const
  -- walks in the dual cluster
  have hDwalk : ∀ ω, ∀ f ∈ D ω, ∃ p : (zdGraph 2).Walk a₀ f,
      (∀ v ∈ p.support, v ∈ D ω) ∧ ∀ s ∈ p.edges, s ∈ ζ ω := by
    intro ω f hf
    obtain ⟨p⟩ := hf
    have hedge : ∀ s ∈ p.edges, s ∈ ζ ω := fun s hs => by
      have := p.edges_subset_edgeSet hs
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
      exact this.1
    refine ⟨p.transfer (zdGraph 2) fun s hs => hζL ω (hedge s hs), fun v hv => ?_,
      fun s hs => ?_⟩
    · rw [SimpleGraph.Walk.support_transfer] at hv
      exact ⟨p.takeUntil v hv⟩
    · rw [SimpleGraph.Walk.edges_transfer] at hs
      exact hedge s hs
  have hDSv : ∀ ω, D ω ⊆ Sv := by
    intro ω f hf
    by_cases hfa : f = a₀
    · rw [hfa]
      exact ha₀Sv
    · obtain ⟨p, -, hpe⟩ := hDwalk ω f hf
      obtain ⟨w, h, p', hp'⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hfa p.reverse
      have hfw : s(f, w) ∈ p.edges := by
        have : s(f, w) ∈ p.reverse.edges := by
          rw [hp']
          simp
        rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
      exact hζSv ω _ (hpe _ hfw) f (Sym2.mem_mk_left _ _)
  have hDleft : ∀ ω, ∀ k : ℕ, (k : ℤ) ≤ n - 1 → (![-1, (k : ℤ)] : LatticeSite 2) ∈ D ω := by
    intro ω k
    induction k with
    | zero =>
      intro _
      have h0 : (![-1, ((0 : ℕ) : ℤ)] : LatticeSite 2) = a₀ := by
        rw [ha₀]
        simp
      rw [h0]
      exact mem_cluster_self (ζ ω) a₀
    | succ k ih =>
      intro hk
      have hprev : (openGraph (ζ ω)).Reachable a₀ ![-1, (k : ℤ)] := ih (by omega)
      have hs : s(![-1, (k : ℤ)], ![-1, ((k + 1 : ℕ) : ℤ)]) ∈ ζ ω :=
        Or.inr ⟨k, by omega, by push_cast at hk ⊢; omega, by push_cast; rfl⟩
      have hne : (![-1, (k : ℤ)] : LatticeSite 2) ≠ ![-1, ((k + 1 : ℕ) : ℤ)] := by
        intro h
        have := congrFun h 1
        simp at this
      exact hprev.trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨hs, hne⟩))
  have hleS : (0 : LatticeSite 2) ≤ ![(n : ℤ), n] := by
    rw [Pi.le_def, Fin.forall_fin_two]
    simp
  have hSvbox : Icc (![(0 : LatticeSite 2) 0 - 1, (0 : LatticeSite 2) 1] : LatticeSite 2)
      ![(![(n : ℤ), n] : LatticeSite 2) 0, (![(n : ℤ), n] : LatticeSite 2) 1 - 1] = Sv := by
    rw [hSv, ha₀]
    simp
  have hDright : ∀ ω, ω ∈ crossing 1 0 ![(n : ℤ), n] → ∀ f ∈ D ω, f 0 ≠ n := by
    intro ω hω f hf hf0
    rw [mem_crossing_one_iff_dualConfig_notMem_crossing_zero hleS] at hω
    apply hω
    obtain ⟨p, hpD, hpe⟩ := hDwalk ω f hf
    obtain ⟨c, hc, q', hqsupp, hqedges, hqfirst⟩ :=
      SimpleGraph.Walk.exists_walk_first_mem (fun v : LatticeSite 2 => v 0 = -1) p.reverse
        ⟨a₀, by simp, by simp [ha₀]⟩
    have hqD : ∀ v ∈ q'.support, v ∈ D ω := fun v hv => by
      have := hqsupp v hv
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
      exact hpD v this
    have hqdual : ∀ s ∈ q'.reverse.edges, s ∈ dualConfig ω := by
      intro s hs
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hs
      have hsζ : s ∈ ζ ω := by
        have := hqedges s hs
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
        exact hpe s this
      obtain ⟨x, y, rfl, hxy, hx, hy⟩ := exists_ne_of_mem_edges q' hs
      rcases hsζ with ⟨hs', -⟩ | hsW
      · exact hs'
      · exact absurd ((hqfirst x hx (hWSv _ hsW x (Sym2.mem_mk_left _ _)).2).trans
          (hqfirst y hy (hWSv _ hsW y (Sym2.mem_mk_right _ _)).2).symm) hxy
    have hloc := mem_localConn_of_walk q'.reverse (fun v hv => by
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      exact hDSv ω (hqD v hv)) hqdual
    have hcSv := hDSv ω (hqD c (SimpleGraph.Walk.end_mem_support _))
    have hfSv := hDSv ω hf
    rw [← hSvbox] at hloc hcSv hfSv
    exact ⟨c, hcSv, by simpa using hc, f, hfSv, by simpa using hf0, hloc⟩
  have hDbdry : ∀ ω, ∀ e ∈ L, (∀ f ∈ dualEdge e, f ∈ Sv) → (∃ f ∈ dualEdge e, f ∈ D ω) →
      (∃ g ∈ dualEdge e, g ∉ D ω) → e ∈ ω := by
    rintro ω e heL hSv' ⟨f, hfe, hfD⟩ ⟨g, hge, hgD⟩
    by_contra heω
    have hfg : f ≠ g := fun h => hgD (h ▸ hfD)
    have hs : dualEdge e = s(f, g) := (Sym2.mem_and_mem_iff hfg).1 ⟨hfe, hge⟩
    have hζe : dualEdge e ∈ ζ ω := Or.inl ⟨(dualEdge_mem_dualConfig_iff heL).2 heω, hSv'⟩
    rw [hs] at hζe
    have hfD' : (openGraph (ζ ω)).Reachable a₀ f := hfD
    exact hgD (hfD'.trans (SimpleGraph.Adj.reachable ((openGraph_adj_iff _ _ _).2 ⟨hζe, hfg⟩)))
  -- the admissible values of the dual cluster
  set 𝒜 : Finset (Finset (LatticeSite 2)) :=
    (Finset.Icc (![-1, 0] : LatticeSite 2) ![(n : ℤ), n - 1]).powerset.filter
      (fun D₀ => (∃ ω₀, D ω₀ = ↑D₀) ∧ ∀ f ∈ D₀, f 0 ≠ n) with h𝒜
  have hmem𝒜 : ∀ D₀ ∈ 𝒜, ↑D₀ ⊆ Sv ∧ (∃ ω₀, D ω₀ = ↑D₀) ∧ ∀ f ∈ D₀, f 0 ≠ n := by
    intro D₀ hD₀
    rw [h𝒜, Finset.mem_filter, Finset.mem_powerset] at hD₀
    refine ⟨fun f hf => ?_, hD₀.2⟩
    have := hD₀.1 hf
    rw [Finset.mem_Icc] at this
    exact this
  have ha₀D : ∀ D₀ ∈ 𝒜, a₀ ∈ D₀ := by
    intro D₀ hD₀
    obtain ⟨-, ⟨ω₀, hω₀⟩, -⟩ := hmem𝒜 D₀ hD₀
    have : a₀ ∈ D ω₀ := mem_cluster_self (ζ ω₀) a₀
    rw [hω₀] at this
    exact this
  have hleftD : ∀ D₀ ∈ 𝒜, ∀ y : ℤ, 0 ≤ y → y ≤ n - 1 →
      (![-1, y] : LatticeSite 2) ∈ (↑D₀ : Set (LatticeSite 2)) := by
    intro D₀ hD₀ y hy0 hy1
    obtain ⟨-, ⟨ω₀, hω₀⟩, -⟩ := hmem𝒜 D₀ hD₀
    have := hDleft ω₀ y.toNat (by omega)
    rw [Int.toNat_of_nonneg hy0, hω₀] at this
    exact this
  have hconnD : ∀ D₀ ∈ 𝒜, ∀ f ∈ (↑D₀ : Set (LatticeSite 2)), ∃ f₀ : LatticeSite 2, f₀ 0 = -1 ∧
      ∃ p : (zdGraph 2).Walk f₀ f, ∀ v ∈ p.support, v ∈ (↑D₀ : Set (LatticeSite 2)) := by
    intro D₀ hD₀ f hf
    obtain ⟨-, ⟨ω₀, hω₀⟩, -⟩ := hmem𝒜 D₀ hD₀
    rw [← hω₀] at hf
    obtain ⟨p, hpD, -⟩ := hDwalk ω₀ f hf
    exact ⟨a₀, by simp [ha₀], p, fun v hv => hω₀ ▸ hpD v hv⟩
  -- the chosen crossing in the boundary of each admissible value
  have hγex : ∀ D₀ : Finset (LatticeSite 2), ∃ c₀ d₀ : LatticeSite 2,
      ∃ γ : (zdGraph 2).Walk c₀ d₀, D₀ ∈ 𝒜 → c₀ 1 = 0 ∧ d₀ 1 = n ∧
        (∀ v ∈ γ.support, v ∈ S) ∧ ∀ e ∈ γ.edges, e ∈ L ∧ (∀ f ∈ dualEdge e, f ∈ Sv) ∧
          (∃ f ∈ dualEdge e, f ∈ (↑D₀ : Set (LatticeSite 2))) ∧
          ∃ f ∈ dualEdge e, f ∉ (↑D₀ : Set (LatticeSite 2)) := by
    intro D₀
    by_cases hD₀ : D₀ ∈ 𝒜
    · obtain ⟨-, -, hright⟩ := hmem𝒜 D₀ hD₀
      obtain ⟨c₀, hc₀, hc₀1, d₀, hd₀, hd₀1, hcd⟩ :=
        mem_crossing_one_boundary (n := n) (D₀ := ↑D₀) (hleftD D₀ hD₀) (fun f hf => hright f hf)
      obtain ⟨γ, hγS, hγe⟩ := exists_walk_of_mem_localConn hcd
      exact ⟨c₀, d₀, γ, fun _ => ⟨by simpa using hc₀1, by simpa using hd₀1, hγS, hγe⟩⟩
    · exact ⟨0, 0, .nil, fun h => absurd h hD₀⟩
  choose c₀ d₀ γ hγ using hγex
  obtain ⟨ρ, hρ⟩ := exists_iso_reflect_one (2 * (n : ℤ))
  have hqρ : ∀ e ∈ L, q (Sym2.map ρ e) = q e := fun e he => by
    rw [hq e he, hq _ ((image_sym2Map_edgeSet ρ).subset (mem_image_of_mem _ he))]
  -- unexplored edges and the fresh event
  set Eout : Finset (LatticeSite 2) → Config (LatticeSite 2) := fun D₀ =>
    {e | e ∈ L ∧ (∀ f ∈ dualEdge e, f ∉ (↑D₀ : Set (LatticeSite 2))) ∧
      ∀ f ∈ dualEdge (Sym2.map ρ e), f ∉ (↑D₀ : Set (LatticeSite 2))} with hEout
  set E : Finset (LatticeSite 2) → Config (LatticeSite 2) := fun D₀ =>
    {e | e ∈ L ∧ ∃ f ∈ dualEdge e, f ∈ (↑D₀ : Set (LatticeSite 2))} with hE
  set F : Finset (LatticeSite 2) → Set (Config (LatticeSite 2)) := fun D₀ =>
    {ω | ∃ u ∈ R, u 0 = m ∧ ∃ g ∈ (γ D₀).support, ω ∩ Eout D₀ ∈ localConn R u g} with hF
  have hEoutL : ∀ D₀, Eout D₀ ⊆ L := fun D₀ e he => he.1
  have hFmeas : ∀ D₀, MeasurableSet (F D₀) := by
    intro D₀
    have : F D₀ = ⋃ u ∈ {u | u ∈ R ∧ u 0 = m}, ⋃ g ∈ {g | g ∈ (γ D₀).support},
        (fun ω : Config (LatticeSite 2) => ω ∩ Eout D₀) ⁻¹' localConn R u g := by
      ext ω
      simp only [hF, mem_iUnion, mem_preimage, mem_ofPred_eq, exists_prop, and_assoc]
    rw [this]
    exact MeasurableSet.biUnion (to_countable _) fun u _ =>
      MeasurableSet.biUnion (to_countable _) fun g _ =>
        (measurableSet_localConn R u g).preimage (by fun_prop)
  have hFL : ∀ D₀, ∀ ω, ω ∩ L ∈ F D₀ ↔ ω ∈ F D₀ := by
    intro D₀ ω
    have : ω ∩ L ∩ Eout D₀ = ω ∩ Eout D₀ := by
      rw [inter_assoc, inter_eq_right.2 (hEoutL D₀)]
    simp only [hF, mem_ofPred_eq, this]
  have hDmeas : ∀ D₀ ∈ 𝒜, MeasurableSet {ω | D ω = ↑D₀} := fun D₀ hD₀ =>
    (measurableSet_cluster_eq_finset a₀ D₀ (ha₀D D₀ hD₀)).preimage hζmeas
  -- (1) a left-right crossing of `R` gives the fresh event or its reflection
  have hHF : ∀ D₀ ∈ 𝒜, law q (crossing 0 0 ![(m : ℤ), 2 * n]) ≤ 2 * law q (F D₀) := by
    intro D₀ hD₀
    obtain ⟨hD₀Sv, -, -⟩ := hmem𝒜 D₀ hD₀
    obtain ⟨hc₀, hd₀, hγS, hγe⟩ := hγ D₀ hD₀
    have hsub : crossing 0 0 ![(m : ℤ), 2 * n] ⊆
        F D₀ ∪ (fun ω => Sym2.map ρ '' ω) ⁻¹' F D₀ := by
      intro ω hω
      obtain ⟨ω', hω', u, hu, hu0, g, hg, σ, hσ, hσe⟩ :=
        exists_walk_unexplored hn hnm hD₀Sv (hconnD D₀ hD₀) (γ D₀) hc₀ hd₀ hγS
          (fun e he => (hγe e he).2.2.2) ρ hρ hω
      have hloc : ω' ∩ Eout D₀ ∈ localConn R u g := by
        have := mem_localConn_of_walk (ω := ω' ∩ Eout D₀) σ hσ fun e he =>
          ⟨(hσe e he).1, σ.edges_subset_edgeSet he, (hσe e he).2.1, (hσe e he).2.2⟩
        rwa [inter_eq_left.2 (inter_subset_right.trans (hEoutL D₀))] at this
      rcases hω' with rfl | rfl
      · exact Or.inl ⟨u, hu, hu0, g, hg, hloc⟩
      · exact Or.inr ⟨u, hu, hu0, g, hg, hloc⟩
    have hρF : law q ((fun ω => Sym2.map ρ '' ω) ⁻¹' F D₀) = law q (F D₀) :=
      law_preimage_image_sym2Map_eq ρ hqρ (hFmeas D₀) (hFL D₀)
    calc law q (crossing 0 0 ![(m : ℤ), 2 * n])
        ≤ law q (F D₀ ∪ (fun ω => Sym2.map ρ '' ω) ⁻¹' F D₀) := measure_mono hsub
      _ ≤ law q (F D₀) + law q ((fun ω => Sym2.map ρ '' ω) ⁻¹' F D₀) := measure_union_le _ _
      _ = 2 * law q (F D₀) := by rw [hρF, two_mul]
  -- (2) on `{D = D₀}`, the fresh event gives `X(R)`
  have hFX : ∀ D₀ ∈ 𝒜, {ω | D ω = ↑D₀} ∩ F D₀ ⊆ X := by
    rintro D₀ hD₀ ω ⟨hωD, u, hu, hu0, g, hg, hug⟩
    obtain ⟨hc₀, hd₀, hγS, hγe⟩ := hγ D₀ hD₀
    have hωD' : D ω = ↑D₀ := hωD
    have hγω : ∀ e ∈ (γ D₀).edges, e ∈ ω := fun e he => by
      obtain ⟨heL, heSv, hin, hout⟩ := hγe e he
      exact hDbdry ω e heL heSv (hωD' ▸ hin) (hωD' ▸ hout)
    refine ⟨g, hγS g hg, ⟨c₀ D₀, hγS _ (SimpleGraph.Walk.start_mem_support _), hc₀,
      mem_localConn_of_walk ((γ D₀).takeUntil g hg)
        (fun v hv => hγS v ((γ D₀).support_takeUntil_subset_support hg hv))
        (fun e he => hγω e ((γ D₀).edges_takeUntil_subset_edges hg he))⟩,
      ⟨d₀ D₀, hγS _ (SimpleGraph.Walk.end_mem_support _), hd₀,
      mem_localConn_of_walk ((γ D₀).dropUntil g hg)
        (fun v hv => hγS v ((γ D₀).support_dropUntil_subset_support hg hv))
        (fun e he => hγω e ((γ D₀).edges_dropUntil_subset_edges hg he))⟩, u, hu, hu0, ?_⟩
    have := localConn_mono (inter_subset_inter_right ω (hEoutL D₀)) hug
    rwa [localConn_comm] at this
  -- (3) `{D = D₀}` and the fresh event are independent
  have hindep : ∀ D₀ ∈ 𝒜, law q ({ω | D ω = ↑D₀} ∩ F D₀) =
      law q {ω | D ω = ↑D₀} * law q (F D₀) := by
    intro D₀ hD₀
    change prodBernoulli q _ = prodBernoulli q _ * prodBernoulli q _
    refine prodBernoulli_inter_of_determined q (P := E D₀) (Q := Eout D₀) ?_ (hDmeas D₀ hD₀)
      (hFmeas D₀) ?_ ?_
    · rw [Set.disjoint_left]
      rintro e ⟨-, f, hf, hfD⟩ ⟨-, hall, -⟩
      exact hall f hf hfD
    · intro ω ω' hωω'
      have hζeq : ζ ω ∩ {s | ∃ v ∈ s, v ∈ D₀} = ζ ω' ∩ {s | ∃ v ∈ s, v ∈ D₀} := by
        ext s
        simp only [mem_inter_iff, mem_ofPred_eq]
        refine and_congr_left fun hsD => ?_
        simp only [hζ, mem_union, mem_inter_iff]
        refine or_congr_left (and_congr_left fun _ => ?_)
        rw [mem_dualConfig_iff, mem_dualConfig_iff]
        refine and_congr_right fun hsL => not_congr ?_
        have heE : Sym2.map (· + 1) (dualEdge s) ∈ E D₀ := by
          refine ⟨map_add_mem_edgeSet 1 (dualEdge_mem_edgeSet hsL), ?_⟩
          obtain ⟨v, hv, hvD⟩ := hsD
          exact ⟨v, by rwa [dualEdge_map_add, map_add_one_dualEdge_dualEdge hsL], hvD⟩
        constructor
        · intro h
          have : _ ∈ ω ∩ E D₀ := ⟨h, heE⟩
          rw [hωω'] at this
          exact this.1
        · intro h
          have : _ ∈ ω' ∩ E D₀ := ⟨h, heE⟩
          rw [← hωω'] at this
          exact this.1
      change cluster (ζ ω) a₀ = ↑D₀ ↔ cluster (ζ ω') a₀ = ↑D₀
      have k₁ := cluster_eq_finset_determined a₀ D₀ (ha₀D D₀ hD₀) (ζ ω)
      have k₂ := cluster_eq_finset_determined a₀ D₀ (ha₀D D₀ hD₀) (ζ ω')
      simp only [mem_ofPred_eq] at k₁ k₂
      rw [k₁, k₂, hζeq]
    · intro ω ω' hωω'
      change (∃ u ∈ R, u 0 = m ∧ ∃ g ∈ (γ D₀).support, ω ∩ Eout D₀ ∈ localConn R u g) ↔
        (∃ u ∈ R, u 0 = m ∧ ∃ g ∈ (γ D₀).support, ω' ∩ Eout D₀ ∈ localConn R u g)
      rw [hωω']
  -- (4) the vertical crossing of `S` is the disjoint union of the admissible values
  have hVdecomp : crossing 1 0 ![(n : ℤ), n] = ⋃ D₀ ∈ 𝒜, {ω | D ω = ↑D₀} := by
    ext ω
    simp only [mem_iUnion, exists_prop, mem_ofPred_eq]
    constructor
    · intro hω
      have hfin : (D ω).Finite := (Set.finite_Icc _ _).subset (hDSv ω)
      refine ⟨hfin.toFinset, ?_, by rw [Set.Finite.coe_toFinset]⟩
      rw [h𝒜, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun f hf => ?_, ⟨ω, by rw [Set.Finite.coe_toFinset]⟩,
        fun f hf => hDright ω hω f (hfin.mem_toFinset.1 hf)⟩
      rw [Finset.mem_Icc]
      exact hDSv ω (hfin.mem_toFinset.1 hf)
    · rintro ⟨D₀, hD₀, hωD⟩
      obtain ⟨-, -, hright⟩ := hmem𝒜 D₀ hD₀
      refine crossing_mono (fun e he => ?_)
        (mem_crossing_one_boundary (n := n) (D₀ := ↑D₀) (hleftD D₀ hD₀)
          (fun f hf => hright f hf))
      obtain ⟨heL, heSv, hin, hout⟩ := he
      exact hDbdry ω e heL heSv (hωD ▸ hin) (hωD ▸ hout)
  -- assembly
  have hdisj : (↑𝒜 : Set (Finset (LatticeSite 2))).PairwiseDisjoint
      fun D₀ => {ω | D ω = ↑D₀} := by
    intro D₁ _ D₂ _ hne
    exact Set.disjoint_left.2 fun ω h₁ h₂ =>
      hne (Finset.coe_injective ((show D ω = ↑D₁ from h₁).symm.trans h₂))
  have hdisj' : (↑𝒜 : Set (Finset (LatticeSite 2))).PairwiseDisjoint
      fun D₀ => {ω | D ω = ↑D₀} ∩ F D₀ :=
    hdisj.mono fun D₀ => inter_subset_left
  calc law q (crossing 0 0 ![(m : ℤ), 2 * n]) * law q (crossing 1 0 ![(n : ℤ), n])
      = law q (crossing 0 0 ![(m : ℤ), 2 * n]) * ∑ D₀ ∈ 𝒜, law q {ω | D ω = ↑D₀} := by
        rw [hVdecomp, measure_biUnion_finset hdisj hDmeas]
    _ = ∑ D₀ ∈ 𝒜, law q (crossing 0 0 ![(m : ℤ), 2 * n]) * law q {ω | D ω = ↑D₀} :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ D₀ ∈ 𝒜, 2 * law q (F D₀) * law q {ω | D ω = ↑D₀} :=
        Finset.sum_le_sum fun D₀ hD₀ => mul_le_mul_left (hHF D₀ hD₀) _
    _ = 2 * ∑ D₀ ∈ 𝒜, law q ({ω | D ω = ↑D₀} ∩ F D₀) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun D₀ hD₀ => ?_
        rw [hindep D₀ hD₀]
        ring
    _ = 2 * law q (⋃ D₀ ∈ 𝒜, {ω | D ω = ↑D₀} ∩ F D₀) := by
        rw [measure_biUnion_finset hdisj' fun D₀ hD₀ => (hDmeas D₀ hD₀).inter (hFmeas D₀)]
    _ ≤ 2 * law q X :=
        mul_le_mul_right (measure_mono (iUnion₂_subset fun D₀ hD₀ => hFX D₀ hD₀)) _

end PercLib.Models.Planar
