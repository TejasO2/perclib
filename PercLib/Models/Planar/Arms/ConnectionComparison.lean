/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: D. Basu and A. Sapozhnikov, Kesten's incipient infinite cluster and
quasi-multiplicativity of crossing probabilities, Electron. Commun. Probab. 22 (2017),
arXiv:1603.06884v2, Section 1 (assumptions (A1) and (A2), equations (1.2)-(1.4)) and Section 2.
-/
module

public import Mathlib.Probability.ConditionalProbability
public import PercLib.Models.Planar.Arms.Separator
public import PercLib.Percolation.Bond.DomainIndependence
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.HarrisDecreasing

/-!
# Connection comparison across annuli of `ℤ²`

The two inputs of Basu and Sapozhnikov's construction of Kesten's incipient infinite cluster,
proved on `ℤ²` uniformly for every profile that opens each edge with probability at least `1/2`.
Boxes are `B_r(z) = Icc (z - r) (z + r)` (`(r : LatticeSite 2)` the constant vector), their
boundaries `boxBoundary (z - r) (z + r)`, and only the open nearest-neighbour edges
`ω ∩ (zdGraph 2).edgeSet` are read. "`X ↔ Y` in `Z`" is the event that some `x ∈ X` and
`y ∈ Y` are joined by an open path all of whose vertices lie in `Z`.

* **Circuit gluing in annulus form** (`inter_edgeSet_mem_localConn_of_mem_annulus_crossings`).
  Long-direction open crossings of the four strips of the annulus `a ≤ ‖v - z‖∞ ≤ b` join any
  two open paths that cross the annulus, inside the union of the annulus and the sets the two
  paths live in. Adjacent strip crossings meet in a corner square, and a path crossing the
  annulus meets the crossing of the strip through which it first leaves `B_b(z)`; both by the
  crossing lemma of `Gluing.lean`. `Separator.lean` joins the paths inside `B_b(z)` only; here
  every connection uses only the annulus and the paths. The four-strip form is
  `inter_edgeSet_mem_localConn_union_of_mem_fourStrip`.
* **(A2), lower bound** (`exists_pos_mul_le_law_setOf_localConn`; Basu–Sapozhnikov (1.2)).
  There is `c > 0` such that for every profile at least `1/2` on the edges, every `m ≥ 1`, every
  `Z` containing the annulus `B_{4m}(z) \ B_{m-1}(z)`, every `X ⊆ B_m(z)` and every `Y` outside
  `B_{4m}(z)`, `c · P(X ↔ ∂B_{2m} in Z) · P(Y ↔ ∂B_{2m} in Z) ≤ P(X ↔ Y in Z)`. Proof: circuits
  in the annuli `[m, 2m]` and `[2m, 4m]` and a crossing of the rectangle `z + [m, 4m] × [0, m]`,
  all increasing; Harris and RSW.
* **(A2), upper bounds** (`law_setOf_localConn_le_mul`,
  `law_setOf_localConn_le_mul_inside_outside`).
  For every profile, `X ⊆ B_r(z)` and `Y` outside `B_r(z)`,
  `P(X ↔ Y in Z) ≤ P(X ↔ ∂B_r in Z) · P(Y ↔ ∂B_r in Z)`: the path from `Y` up to its first
  visit to `B_r(z)` uses only pairs not inside `B_r(z)`, the path from `X` up to its first visit
  to `∂B_r(z)` only pairs inside it. The second form,
  `P(X ↔ Y in Z) ≤ P(X ↔ ∂B_r in Z ∩ B_r) · P(∂B_{r+1} ↔ Y in Z \ B_r)`, is the one of the plan.
  Both directions together: `exists_law_setOf_localConn_comparable`.
* **(A1), uniqueness of crossing clusters**
  (`exists_law_inter_setOf_crossing_clusters_le`; Basu–Sapozhnikov (1.3)-(1.4)). There is
  `c₀ > 0` such that for every profile at least `1/2` on the edges, every increasing event `E`
  and all `N ≥ 1`, `M ≥ 4^k N`, the probability of `E` together with two distinct open crossing
  clusters of the annulus `B_M(z) \ B_{N-1}(z)` is at most `(1 - c₀)^k P(E)`. The annulus
  contains the `k` disjoint four-strip annuli of radii `2 · 4^j N`, `4^{j+1} N`; a four-strip
  event in any of them glues all crossings of the big annulus inside it. The conditional form
  is `exists_cond_setOf_crossing_clusters_le`.

## Main results

* `PercLib.Models.Planar.inter_edgeSet_mem_localConn_of_mem_annulus_crossings`
* `PercLib.Models.Planar.inter_edgeSet_mem_localConn_union_of_mem_fourStrip`
* `PercLib.Models.Planar.exists_pos_mul_le_law_setOf_localConn`
* `PercLib.Models.Planar.law_setOf_localConn_le_mul`
* `PercLib.Models.Planar.law_setOf_localConn_le_mul_inside_outside`
* `PercLib.Models.Planar.exists_law_setOf_localConn_comparable`
* `PercLib.Models.Planar.exists_law_inter_biInter_compl_fourStrip_le`
* `PercLib.Models.Planar.exists_law_inter_setOf_crossing_clusters_le`
* `PercLib.Models.Planar.exists_cond_setOf_crossing_clusters_le`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

/-! ### Connections between two sets -/

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A connection between two sets inside `S`, by the open pairs of `ω` in `E`, is measurable. -/
theorem measurableSet_setOf_exists_inter_mem_localConn [Countable V] (X Y S : Set V)
    (E : Set (Sym2 V)) :
    MeasurableSet {ω : Config V | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ E ∈ localConn S x y} := by
  have h : {ω : Config V | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ E ∈ localConn S x y} =
      ⋃ x ∈ X, ⋃ y ∈ Y, (fun ω : Config V => ω ∩ E) ⁻¹' localConn S x y := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, exists_prop]
  rw [h]
  exact MeasurableSet.biUnion (to_countable _) fun x _ =>
    MeasurableSet.biUnion (to_countable _) fun y _ =>
      (measurableSet_localConn _ x y).preimage (by fun_prop)

/-- A connection between two sets inside `S`, by the open pairs of `ω` in `E`, is an increasing
event. -/
theorem isUpperSet_setOf_exists_inter_mem_localConn (X Y S : Set V) (E : Set (Sym2 V)) :
    IsUpperSet {ω : Config V | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ E ∈ localConn S x y} := by
  rintro ω ω' h ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy, localConn_mono (inter_subset_inter_left _ h) hxy⟩

end PercLib.Percolation.Bond

namespace PercLib.Models.Planar

/-! ### Profiles at least `1/2` -/

/-- **Comparison with the self-dual point.** If `q` opens every edge of `ℤ²` with probability at
least `1/2`, some profile equal to `1/2` on the edges makes every measurable increasing event at
most as likely as under `q`. -/
theorem exists_law_le_of_half_le {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) :
    ∃ q₀ : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q₀ e : ℝ) = 1 / 2) ∧
      ∀ A : Set (Config (LatticeSite 2)), MeasurableSet A → IsUpperSet A →
        law q₀ A ≤ law q A := by
  classical
  refine ⟨fun e => if e ∈ (zdGraph 2).edgeSet then ⟨1 / 2, by norm_num, by norm_num⟩ else q e,
    fun e he => by simp only [he, ↓reduceIte], fun A hA hup => ?_⟩
  refine prodBernoulli_mono_event _ _ (fun e => ?_) hA hup
  by_cases he : e ∈ (zdGraph 2).edgeSet
  · simp only [he, ↓reduceIte]
    exact hq e he
  · simp only [he, ↓reduceIte, le_refl]

/-- **RSW for profiles at least `1/2`.** For each `k` there is `c > 0` such that for every profile
opening each edge with probability at least `1/2`, every `n ≥ 1` and every corner `lo`, the
`kn × n` box at `lo` is crossed from left to right, and the `n × kn` box at `lo` from bottom to
top, with probability at least `c`. -/
theorem exists_pos_le_law_crossing_of_half_le (k : ℕ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n →
        c ≤ law q (crossing i lo
          (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n])) := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_le_law_crossing k
  refine ⟨c, hc, fun q hq i lo n hn => ?_⟩
  obtain ⟨q₀, hq₀, hle⟩ := exists_law_le_of_half_le hq
  exact (hcq q₀ hq₀ i lo n hn).trans
    (hle _ (measurableSet_crossing _ _ _) (isUpperSet_crossing _ _ _))

/-- **T4 for profiles at least `1/2`.** There is `c₀ > 0` such that for every profile opening each
edge with probability at least `1/2`, every centre `z` and every `n ≥ 1`, the four-strip event
of the annulus `2n ≤ ‖v - z‖∞ ≤ 4n` has probability at least `c₀`. -/
theorem exists_pos_le_law_fourStrip_of_half_le :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (n : ℕ), 1 ≤ n → c₀ ≤ law q (fourStrip z n) := by
  obtain ⟨c₀, hc₀, hcq⟩ := exists_pos_le_law_fourStrip
  refine ⟨c₀, hc₀, fun q hq z n hn => ?_⟩
  obtain ⟨q₀, hq₀, hle⟩ := exists_law_le_of_half_le hq
  exact (hcq q₀ hq₀ z n hn).trans
    (hle _ (measurableSet_fourStrip _ _) (isUpperSet_fourStrip _ _))

/-! ### First passage to the boundary of a box -/

/-- **First passage to the boundary of a box.** An open path inside `U` from a point of
`B_r(z) = z + [-r, r]²` to a point outside `B_{r-1}(z)` has an initial segment that stays inside
`U ∩ B_r(z)` and ends on the boundary of `B_r(z)`. -/
theorem exists_mem_boxBoundary_mem_localConn_inter {ω : Config (LatticeSite 2)}
    {z x y : LatticeSite 2} {r : ℕ} {U : Set (LatticeSite 2)}
    (hx : x ∈ Icc (z - (r : LatticeSite 2)) (z + r))
    (hy : y ∉ Icc (z - (r : LatticeSite 2) + 1) (z + r - 1))
    (h : ω ∩ (zdGraph 2).edgeSet ∈ localConn U x y) :
    ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (U ∩ Icc (z - (r : LatticeSite 2)) (z + r)) x w := by
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 h
  obtain ⟨g, hg⟩ : ∃ g : LatticeSite 2 → ℤ,
      g = fun v => max (max (v 0 - z 0) (z 0 - v 0)) (max (v 1 - z 1) (z 1 - v 1)) := ⟨_, rfl⟩
  have hgv : ∀ v, g v = max (max (v 0 - z 0) (z 0 - v 0)) (max (v 1 - z 1) (z 1 - v 1)) :=
    fun v => by rw [hg]
  have hf : ∀ u v, (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj u v → g v ≤ g u + 1 := by
    intro u v huv
    have h0 := coord_le_add_one_of_adj huv 0
    have h0' := coord_le_add_one_of_adj huv.symm 0
    have h1 := coord_le_add_one_of_adj huv 1
    have h1' := coord_le_add_one_of_adj huv.symm 1
    rw [hgv u, hgv v]
    omega
  have hx' : g x ≤ r := by
    rw [mem_Icc_two_iff] at hx
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hx
    rw [hgv]
    omega
  have hy' : (r : ℤ) ≤ g y := by
    rw [mem_Icc_two_iff] at hy
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hy
    rw [hgv]
    omega
  obtain ⟨c, hc, q, hq⟩ := SimpleGraph.Walk.exists_walk_eq_of_le g hf p hx' hy'
  refine ⟨c, ?_, mem_localConn_iff_exists_walk.2 ⟨q, fun v hv => ⟨hp v (hq v hv).1, ?_⟩⟩⟩
  · rw [mem_boxBoundary_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    rw [hgv] at hc
    omega
  · have hv' := (hq v hv).2
    rw [hgv] at hv'
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega

/-- **First passage to the boundary of a box, from outside.** An open path inside `U` from a point
outside `B_{r-1}(z)` to a point of `B_r(z)` has an initial segment that stays inside `U` and
outside `B_{r-1}(z)` and ends on the boundary of `B_r(z)`. -/
theorem exists_mem_boxBoundary_mem_localConn_diff {ω : Config (LatticeSite 2)}
    {z x y : LatticeSite 2} {r : ℕ} {U : Set (LatticeSite 2)}
    (hx : x ∉ Icc (z - (r : LatticeSite 2) + 1) (z + r - 1))
    (hy : y ∈ Icc (z - (r : LatticeSite 2)) (z + r))
    (h : ω ∩ (zdGraph 2).edgeSet ∈ localConn U x y) :
    ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
      ω ∩ (zdGraph 2).edgeSet ∈
        localConn (U \ Icc (z - (r : LatticeSite 2) + 1) (z + r - 1)) x w := by
  obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 h
  obtain ⟨g, hg⟩ : ∃ g : LatticeSite 2 → ℤ,
      g = fun v => -max (max (v 0 - z 0) (z 0 - v 0)) (max (v 1 - z 1) (z 1 - v 1)) := ⟨_, rfl⟩
  have hgv : ∀ v, g v = -max (max (v 0 - z 0) (z 0 - v 0)) (max (v 1 - z 1) (z 1 - v 1)) :=
    fun v => by rw [hg]
  have hf : ∀ u v, (openGraph (ω ∩ (zdGraph 2).edgeSet)).Adj u v → g v ≤ g u + 1 := by
    intro u v huv
    have h0 := coord_le_add_one_of_adj huv 0
    have h0' := coord_le_add_one_of_adj huv.symm 0
    have h1 := coord_le_add_one_of_adj huv 1
    have h1' := coord_le_add_one_of_adj huv.symm 1
    rw [hgv u, hgv v]
    omega
  have hx' : g x ≤ -(r : ℤ) := by
    rw [mem_Icc_two_iff] at hx
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hx
    rw [hgv]
    omega
  have hy' : -(r : ℤ) ≤ g y := by
    rw [mem_Icc_two_iff] at hy
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hy
    rw [hgv]
    omega
  obtain ⟨c, hc, q, hq⟩ := SimpleGraph.Walk.exists_walk_eq_of_le g hf p hx' hy'
  refine ⟨c, ?_, mem_localConn_iff_exists_walk.2 ⟨q, fun v hv => ⟨hp v (hq v hv).1, ?_⟩⟩⟩
  · rw [mem_boxBoundary_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    rw [hgv] at hc
    omega
  · have hv' := (hq v hv).2
    rw [hgv] at hv'
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    omega

/-! ### Circuit gluing in annulus form -/

/-- **Crossings of perpendicular strips meet.** An open walk from a vertex left of the column
`l₀` to a vertex right of the column `h₀` that stays between the rows `l₁` and `h₁`, and an open
walk from a vertex below the row `l₁` to a vertex above the row `h₁` that stays between the
columns `l₀` and `h₀`, share a vertex. -/
theorem exists_mem_support_of_walks_of_rows_of_cols {ω : Config (LatticeSite 2)}
    {s₁ t₁ s₂ t₂ : LatticeSite 2} {l₀ h₀ l₁ h₁ : ℤ} (h0 : l₀ ≤ h₀) (h1 : l₁ < h₁)
    (p₁ : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s₁ t₁)
    (p₂ : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s₂ t₂)
    (hp₁ : ∀ v ∈ p₁.support, l₁ ≤ v 1 ∧ v 1 ≤ h₁)
    (hp₂ : ∀ v ∈ p₂.support, l₀ ≤ v 0 ∧ v 0 ≤ h₀)
    (hs₁ : s₁ 0 ≤ l₀) (ht₁ : h₀ ≤ t₁ 0) (hs₂ : s₂ 1 ≤ l₁) (ht₂ : h₁ ≤ t₂ 1) :
    ∃ v ∈ p₁.support, v ∈ p₂.support := by
  obtain ⟨u₁, w₁, hu₁, hw₁, q₁, hq₁⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => v 0)
    (fun u v h => coord_le_add_one_of_adj h 0) p₁ hs₁ h0 ht₁
  obtain ⟨u₂, w₂, hu₂, hw₂, q₂, hq₂⟩ := SimpleGraph.Walk.exists_walk_mem_Icc (fun v => v 1)
    (fun u v h => coord_le_add_one_of_adj h 1) p₂ hs₂ h1.le ht₂
  have hle := openGraph_inter_edgeSet_le ω
  obtain ⟨v, hv₁, hv₂⟩ := exists_mem_support_of_crossing_walks
    (lo := ![l₀, l₁]) (hi := ![h₀, h₁])
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; exact h1)
    (q₁.mapLe hle) (q₂.mapLe hle)
    (fun v hv => by
      rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
      obtain ⟨hvp, hv₁, hv₂⟩ := hq₁ v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ⟨hv₁, hv₂, (hp₁ v hvp).1, (hp₁ v hvp).2⟩)
    (fun v hv => by
      rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
      obtain ⟨hvp, hv₁, hv₂⟩ := hq₂ v hv
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ⟨(hp₂ v hvp).1, (hp₂ v hvp).2, hv₁, hv₂⟩)
    (by simp only [Matrix.cons_val_zero]; exact hu₁)
    (by simp only [Matrix.cons_val_zero]; exact hw₁)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; exact hu₂)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; exact hw₂)
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv₁ hv₂
  exact ⟨v, (hq₁ v hv₁).1, (hq₂ v hv₂).1⟩

/-- **The crossings of the four strips of an annulus.** Let `a < b` and let `ω` have
long-direction open crossings of the four strips of the annulus `a ≤ ‖v - z‖∞ ≤ b`. There is a
vertex `w₀` such that every open walk crossing one of the four strips in its short direction,
while staying between the outer lines of the annulus, has a vertex joined to `w₀` inside the
annulus. The four clauses are the left, right, bottom and top strips; the walks of the first two
run from left to right, those of the last two from bottom to top. -/
theorem exists_forall_walk_mem_localConn_of_mem_annulus_crossings {ω : Config (LatticeSite 2)}
    {z : LatticeSite 2} {a b : ℕ} (hab : a < b)
    (hC : ω ∈ crossing 0 (z + ![-(b : ℤ), a]) (z + ![(b : ℤ), b]) ∩
      crossing 0 (z + ![-(b : ℤ), -(b : ℤ)]) (z + ![(b : ℤ), -(a : ℤ)]) ∩
      crossing 1 (z + ![(a : ℤ), -(b : ℤ)]) (z + ![(b : ℤ), b]) ∩
      crossing 1 (z + ![-(b : ℤ), -(b : ℤ)]) (z + ![-(a : ℤ), b])) :
    ∃ w₀ : LatticeSite 2,
      (∀ (s t : LatticeSite 2) (r : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s t),
        (∀ v ∈ r.support, z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 + b) → s 0 ≤ z 0 - b → z 0 - a ≤ t 0 →
        ∃ v ∈ r.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2))
          (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w₀) ∧
      (∀ (s t : LatticeSite 2) (r : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s t),
        (∀ v ∈ r.support, z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 + b) → s 0 ≤ z 0 + a → z 0 + b ≤ t 0 →
        ∃ v ∈ r.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2))
          (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w₀) ∧
      (∀ (s t : LatticeSite 2) (r : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s t),
        (∀ v ∈ r.support, z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 + b) → s 1 ≤ z 1 - b → z 1 - a ≤ t 1 →
        ∃ v ∈ r.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2))
          (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w₀) ∧
      (∀ (s t : LatticeSite 2) (r : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s t),
        (∀ v ∈ r.support, z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 + b) → s 1 ≤ z 1 + a → z 1 + b ≤ t 1 →
        ∃ v ∈ r.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (b : LatticeSite 2))
          (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)) v w₀) := by
  classical
  set A : Set (LatticeSite 2) :=
    Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)
    with hAdef
  have hab' : (a : ℤ) < b := Nat.cast_lt.2 hab
  have ha0 : (0 : ℤ) ≤ a := Nat.cast_nonneg a
  -- coordinates of the annulus and of the strips
  have hA : ∀ v : LatticeSite 2, z 0 - b ≤ v 0 → v 0 ≤ z 0 + b → z 1 - b ≤ v 1 →
      v 1 ≤ z 1 + b → (v 0 ≤ z 0 - a ∨ z 0 + a ≤ v 0 ∨ v 1 ≤ z 1 - a ∨ z 1 + a ≤ v 1) →
      v ∈ A := by
    intro v h₁ h₂ h₃ h₄ h₅
    rw [hAdef, mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  have hS : ∀ (v : LatticeSite 2) (p₁ p₂ p₃ p₄ : ℤ), v ∈ Icc (z + ![p₁, p₂]) (z + ![p₃, p₄]) ↔
      z 0 + p₁ ≤ v 0 ∧ v 0 ≤ z 0 + p₃ ∧ z 1 + p₂ ≤ v 1 ∧ v 1 ≤ z 1 + p₄ := by
    intro v p₁ p₂ p₃ p₄
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- two vertices of an open walk inside `A` are joined inside `A`
  have hjoin : ∀ {s t : LatticeSite 2} (p : (openGraph (ω ∩ (zdGraph 2).edgeSet)).Walk s t),
      (∀ v ∈ p.support, v ∈ A) → ∀ v ∈ p.support, ∀ v' ∈ p.support,
      ω ∩ (zdGraph 2).edgeSet ∈ localConn A v v' := fun p hp v hv v' hv' => by
    have h₁ : ω ∩ (zdGraph 2).edgeSet ∈ localConn A _ v :=
      mem_localConn_iff_exists_walk.2 ⟨p.takeUntil v hv, fun w hw =>
        hp w (p.support_takeUntil_subset_support hv hw)⟩
    have h₂ : ω ∩ (zdGraph 2).edgeSet ∈ localConn A _ v' :=
      mem_localConn_iff_exists_walk.2 ⟨p.takeUntil v' hv', fun w hw =>
        hp w (p.support_takeUntil_subset_support hv' hw)⟩
    rw [localConn_comm] at h₁
    exact localConn_trans h₁ h₂
  -- the four crossings as walks
  obtain ⟨⟨⟨⟨aT, -, haT, bT, -, hbT, hTc⟩, ⟨aD, -, haD, bD, -, hbD, hDc⟩⟩,
    ⟨aR, -, haR, bR, -, hbR, hRc⟩⟩, ⟨aL, -, haL, bL, -, hbL, hLc⟩⟩ := hC
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← sub_eq_add_neg] at haT hbT haD hbD haR hbR haL hbL
  obtain ⟨pT, hpT⟩ := mem_localConn_iff_exists_walk.1 hTc
  obtain ⟨pD, hpD⟩ := mem_localConn_iff_exists_walk.1 hDc
  obtain ⟨pR, hpR⟩ := mem_localConn_iff_exists_walk.1 hRc
  obtain ⟨pL, hpL⟩ := mem_localConn_iff_exists_walk.1 hLc
  have hpT' : ∀ v ∈ pT.support,
      z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 + b ∧ z 1 + a ≤ v 1 ∧ v 1 ≤ z 1 + b := fun v hv => by
    simpa only [← sub_eq_add_neg] using (hS v _ _ _ _).1 (hpT v hv)
  have hpD' : ∀ v ∈ pD.support,
      z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 + b ∧ z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 - a := fun v hv => by
    simpa only [← sub_eq_add_neg] using (hS v _ _ _ _).1 (hpD v hv)
  have hpR' : ∀ v ∈ pR.support,
      z 0 + a ≤ v 0 ∧ v 0 ≤ z 0 + b ∧ z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 + b := fun v hv => by
    simpa only [← sub_eq_add_neg] using (hS v _ _ _ _).1 (hpR v hv)
  have hpL' : ∀ v ∈ pL.support,
      z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 - a ∧ z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 + b := fun v hv => by
    simpa only [← sub_eq_add_neg] using (hS v _ _ _ _).1 (hpL v hv)
  have hpTA : ∀ v ∈ pT.support, v ∈ A := fun v hv => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hpT' v hv
    exact hA v h₁ h₂ (by omega) h₄ (Or.inr (Or.inr (Or.inr h₃)))
  have hpDA : ∀ v ∈ pD.support, v ∈ A := fun v hv => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hpD' v hv
    exact hA v h₁ h₂ h₃ (by omega) (Or.inr (Or.inr (Or.inl h₄)))
  have hpRA : ∀ v ∈ pR.support, v ∈ A := fun v hv => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hpR' v hv
    exact hA v (by omega) h₂ h₃ h₄ (Or.inr (Or.inl h₁))
  have hpLA : ∀ v ∈ pL.support, v ∈ A := fun v hv => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hpL' v hv
    exact hA v h₁ (by omega) h₃ h₄ (Or.inl h₂)
  -- adjacent crossings meet in the corner squares
  have e₁ : z 0 + (a : ℤ) ≤ z 0 + b := by omega
  have e₂ : z 1 + (a : ℤ) < z 1 + b := by omega
  have e₃ : z 0 - (b : ℤ) ≤ z 0 - a := by omega
  have e₄ : z 1 - (b : ℤ) < z 1 - a := by omega
  have e₅ : z 1 - (b : ℤ) < z 1 + b := by omega
  have e₆ : z 0 - (b : ℤ) ≤ z 0 + b := by omega
  have e₇ : z 0 - (b : ℤ) ≤ z 0 + a := by omega
  have e₈ : z 1 - (b : ℤ) ≤ z 1 + a := by omega
  have e₉ : z 0 - (a : ℤ) ≤ z 0 + b := by omega
  have e₁₀ : z 1 - (a : ℤ) ≤ z 1 + b := by omega
  obtain ⟨vTR, hvTR, hvTR'⟩ := exists_mem_support_of_walks_of_rows_of_cols e₁ e₂ pT pR
    (fun v hv => (hpT' v hv).2.2) (fun v hv => ⟨(hpR' v hv).1, (hpR' v hv).2.1⟩)
    (haT.trans_le e₇) hbT.ge (haR.trans_le e₈) hbR.ge
  obtain ⟨vTL, hvTL, hvTL'⟩ := exists_mem_support_of_walks_of_rows_of_cols e₃ e₂ pT pL
    (fun v hv => (hpT' v hv).2.2) (fun v hv => ⟨(hpL' v hv).1, (hpL' v hv).2.1⟩)
    haT.le (e₉.trans hbT.ge) (haL.trans_le e₈) hbL.ge
  obtain ⟨vDR, hvDR, hvDR'⟩ := exists_mem_support_of_walks_of_rows_of_cols e₁ e₄ pD pR
    (fun v hv => (hpD' v hv).2.2) (fun v hv => ⟨(hpR' v hv).1, (hpR' v hv).2.1⟩)
    (haD.trans_le e₇) hbD.ge haR.le (e₁₀.trans hbR.ge)
  -- every vertex of the four crossings is joined inside the annulus to `aT`
  have hTall : ∀ v ∈ pT.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn A v aT := fun v hv =>
    hjoin pT hpTA v hv aT (SimpleGraph.Walk.start_mem_support _)
  have hRall : ∀ v ∈ pR.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn A v aT := fun v hv =>
    localConn_trans (hjoin pR hpRA v hv vTR hvTR') (hTall vTR hvTR)
  have hLall : ∀ v ∈ pL.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn A v aT := fun v hv =>
    localConn_trans (hjoin pL hpLA v hv vTL hvTL') (hTall vTL hvTL)
  have hDall : ∀ v ∈ pD.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn A v aT := fun v hv =>
    localConn_trans (hjoin pD hpDA v hv vDR hvDR) (hRall vDR hvDR')
  refine ⟨aT, fun s t r hr hs ht => ?_, fun s t r hr hs ht => ?_, fun s t r hr hs ht => ?_,
    fun s t r hr hs ht => ?_⟩
  · obtain ⟨v, hv₁, hv₂⟩ := exists_mem_support_of_walks_of_rows_of_cols e₃ e₅ r pL hr
      (fun v hv => ⟨(hpL' v hv).1, (hpL' v hv).2.1⟩) hs ht haL.le hbL.ge
    exact ⟨v, hv₁, hLall v hv₂⟩
  · obtain ⟨v, hv₁, hv₂⟩ := exists_mem_support_of_walks_of_rows_of_cols e₁ e₅ r pR hr
      (fun v hv => ⟨(hpR' v hv).1, (hpR' v hv).2.1⟩) hs ht haR.le hbR.ge
    exact ⟨v, hv₁, hRall v hv₂⟩
  · obtain ⟨v, hv₁, hv₂⟩ := exists_mem_support_of_walks_of_rows_of_cols e₆ e₄ pD r
      (fun v hv => (hpD' v hv).2.2) hr haD.le hbD.ge hs ht
    exact ⟨v, hv₂, hDall v hv₁⟩
  · obtain ⟨v, hv₁, hv₂⟩ := exists_mem_support_of_walks_of_rows_of_cols e₆ e₂ pT r
      (fun v hv => (hpT' v hv).2.2) hr haT.le hbT.ge hs ht
    exact ⟨v, hv₂, hTall v hv₁⟩

/-- **Circuit gluing in an annulus.** Let `a < b` and let `ω` have long-direction open crossings
of the four strips of the annulus `a ≤ ‖v - z‖∞ ≤ b`: left-right crossings of the top strip
`z + [-b, b] × [a, b]` and of the bottom strip `z + [-b, b] × [-b, -a]`, bottom-top crossings of
the right strip `z + [a, b] × [-b, b]` and of the left strip `z + [-b, -a] × [-b, b]`. If `x` and
`x'` lie in `B_a(z)`, `y` and `y'` outside `B_{b-1}(z)`, `x` is joined to `y` inside `W` and `x'`
to `y'` inside `W'`, then `x` is joined to `x'` inside the union of `W`, `W'` and the annulus. -/
theorem inter_edgeSet_mem_localConn_of_mem_annulus_crossings {ω : Config (LatticeSite 2)}
    {z : LatticeSite 2} {a b : ℕ} (hab : a < b)
    (hC : ω ∈ crossing 0 (z + ![-(b : ℤ), a]) (z + ![(b : ℤ), b]) ∩
      crossing 0 (z + ![-(b : ℤ), -(b : ℤ)]) (z + ![(b : ℤ), -(a : ℤ)]) ∩
      crossing 1 (z + ![(a : ℤ), -(b : ℤ)]) (z + ![(b : ℤ), b]) ∩
      crossing 1 (z + ![-(b : ℤ), -(b : ℤ)]) (z + ![-(a : ℤ), b]))
    {W W' : Set (LatticeSite 2)} {x y x' y' : LatticeSite 2}
    (hx : x ∈ Icc (z - (a : LatticeSite 2)) (z + a))
    (hy : y ∉ Icc (z - (b : LatticeSite 2) + 1) (z + b - 1))
    (hx' : x' ∈ Icc (z - (a : LatticeSite 2)) (z + a))
    (hy' : y' ∉ Icc (z - (b : LatticeSite 2) + 1) (z + b - 1))
    (hxy : ω ∩ (zdGraph 2).edgeSet ∈ localConn W x y)
    (hx'y' : ω ∩ (zdGraph 2).edgeSet ∈ localConn W' x' y') :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn (W ∪ W' ∪
      (Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)))
      x x' := by
  classical
  obtain ⟨w₀, hLft, hRgt, hBot, hTop⟩ :=
    exists_forall_walk_mem_localConn_of_mem_annulus_crossings hab hC
  set A : Set (LatticeSite 2) :=
    Icc (z - (b : LatticeSite 2)) (z + b) \ Icc (z - (a : LatticeSite 2) + 1) (z + a - 1)
    with hAdef
  -- a path crossing the annulus is joined to `w₀`
  have harm : ∀ (U : Set (LatticeSite 2)) (s t : LatticeSite 2),
      s ∈ Icc (z - (a : LatticeSite 2)) (z + a) →
      t ∉ Icc (z - (b : LatticeSite 2) + 1) (z + b - 1) →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn U s t →
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (U ∪ A) s w₀ := by
    intro U s t hs ht hst
    have hs' : z 0 - a ≤ s 0 ∧ s 0 ≤ z 0 + a ∧ z 1 - a ≤ s 1 ∧ s 1 ≤ z 1 + a := by
      rw [mem_Icc_two_iff] at hs
      simpa only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] using hs
    have hsB : s ∈ Icc (z - (b : LatticeSite 2)) (z + b) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      omega
    obtain ⟨c, hc, hsc⟩ := exists_mem_boxBoundary_mem_localConn_inter hsB ht hst
    obtain ⟨r, hr⟩ := mem_localConn_iff_exists_walk.1 hsc
    have hr' : ∀ v ∈ r.support,
        z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 + b ∧ z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 + b := by
      intro v hv
      have hvB := (hr v hv).2
      rw [mem_Icc_two_iff] at hvB
      simpa only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] using hvB
    have hr'' : ∀ v ∈ r.reverse.support,
        z 0 - b ≤ v 0 ∧ v 0 ≤ z 0 + b ∧ z 1 - b ≤ v 1 ∧ v 1 ≤ z 1 + b := by
      intro v hv
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      exact hr' v hv
    have hsU : ∀ v ∈ r.support, ω ∩ (zdGraph 2).edgeSet ∈ localConn (U ∪ A) s v := fun v hv =>
      localConn_mono_set subset_union_left _ _ (mem_localConn_iff_exists_walk.2
        ⟨r.takeUntil v hv, fun w hw => (hr w (r.support_takeUntil_subset_support hv hw)).1⟩)
    rw [mem_boxBoundary_two_iff] at hc
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hc
    obtain ⟨-, hc | hc | hc | hc⟩ := hc
    · -- `c` on the left side: the reversed path crosses the left strip
      obtain ⟨v, hv₁, hv₂⟩ := hLft c s r.reverse (fun v hv => (hr'' v hv).2.2) hc.le hs'.1
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv₁
      exact localConn_trans (hsU v hv₁) (localConn_mono_set subset_union_right _ _ hv₂)
    · -- `c` on the right side: the path crosses the right strip
      obtain ⟨v, hv₁, hv₂⟩ := hRgt s c r (fun v hv => (hr' v hv).2.2) hs'.2.1 hc.ge
      exact localConn_trans (hsU v hv₁) (localConn_mono_set subset_union_right _ _ hv₂)
    · -- `c` on the bottom side: the reversed path crosses the bottom strip
      obtain ⟨v, hv₁, hv₂⟩ := hBot c s r.reverse
        (fun v hv => ⟨(hr'' v hv).1, (hr'' v hv).2.1⟩) hc.le hs'.2.2.1
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv₁
      exact localConn_trans (hsU v hv₁) (localConn_mono_set subset_union_right _ _ hv₂)
    · -- `c` on the top side: the path crosses the top strip
      obtain ⟨v, hv₁, hv₂⟩ := hTop s c r
        (fun v hv => ⟨(hr' v hv).1, (hr' v hv).2.1⟩) hs'.2.2.2 hc.ge
      exact localConn_trans (hsU v hv₁) (localConn_mono_set subset_union_right _ _ hv₂)
  have h₁ := harm W x y hx hy hxy
  have h₂ := harm W' x' y' hx' hy' hx'y'
  rw [localConn_comm] at h₂
  exact localConn_trans (localConn_mono_set (union_subset_union_left A subset_union_left) _ _ h₁)
    (localConn_mono_set (union_subset_union_left A subset_union_right) _ _ h₂)

/-- **Circuit gluing in annulus form, four-strip event.** On the four-strip event of the annulus
`2n ≤ ‖v - z‖∞ ≤ 4n`, if `x` and `x'` lie in `B_{2n}(z)`, `y` and `y'` outside `B_{4n-1}(z)`,
`x` is joined to `y` inside `W` and `x'` to `y'` inside `W'`, then `x` is joined to `x'` inside
the union of `W`, `W'` and the annulus. -/
theorem inter_edgeSet_mem_localConn_union_of_mem_fourStrip {ω : Config (LatticeSite 2)}
    {z : LatticeSite 2} {n : ℕ} (hω : ω ∈ fourStrip z n) {W W' : Set (LatticeSite 2)}
    {x y x' y' : LatticeSite 2}
    (hx : x ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (hy : y ∉ Icc (z - ((4 * n : ℕ) : LatticeSite 2) + 1) (z + ((4 * n : ℕ) : LatticeSite 2) - 1))
    (hx' : x' ∈ Icc (z - ((2 * n : ℕ) : LatticeSite 2)) (z + ((2 * n : ℕ) : LatticeSite 2)))
    (hy' : y' ∉
      Icc (z - ((4 * n : ℕ) : LatticeSite 2) + 1) (z + ((4 * n : ℕ) : LatticeSite 2) - 1))
    (hxy : ω ∩ (zdGraph 2).edgeSet ∈ localConn W x y)
    (hx'y' : ω ∩ (zdGraph 2).edgeSet ∈ localConn W' x' y') :
    ω ∩ (zdGraph 2).edgeSet ∈ localConn (W ∪ W' ∪
      (Icc (z - ((4 * n : ℕ) : LatticeSite 2)) (z + ((4 * n : ℕ) : LatticeSite 2)) \
        Icc (z - ((2 * n : ℕ) : LatticeSite 2) + 1) (z + ((2 * n : ℕ) : LatticeSite 2) - 1)))
      x x' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- radius zero: both points are the centre
    have hz : ∀ v ∈ Icc (z - ((2 * 0 : ℕ) : LatticeSite 2)) (z + ((2 * 0 : ℕ) : LatticeSite 2)),
        v = z := fun v hv => by simpa using hv
    have hzW : z ∈ W := hz x hx ▸ hxy.1
    rw [hz x hx, hz x' hx']
    exact ⟨Or.inl (Or.inl hzW), Or.inl (Or.inl hzW), SimpleGraph.Reachable.refl _⟩
  refine inter_edgeSet_mem_localConn_of_mem_annulus_crossings (by omega) ?_ hx hy hx' hy' hxy hx'y'
  have h := hω
  rw [fourStrip] at h
  push_cast
  simpa only [neg_mul] using h

/-! ### Circuits in annuli of ratio two -/

/-- **Circuits in annuli of ratio two.** There is `c > 0` such that for every profile opening each
edge with probability at least `1/2`, every centre `z` and every `a ≥ 1`, the four strips of the
annulus `a ≤ ‖v - z‖∞ ≤ 2a` are all crossed in their long direction with probability at least
`c`. For even `a` this is the four-strip event of radius `a / 2`. -/
theorem exists_pos_le_law_annulus_crossings :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (a b : ℕ), 1 ≤ a → b = 2 * a →
        c ≤ law q (crossing 0 (z + ![-(b : ℤ), a]) (z + ![(b : ℤ), b]) ∩
          crossing 0 (z + ![-(b : ℤ), -(b : ℤ)]) (z + ![(b : ℤ), -(a : ℤ)]) ∩
          crossing 1 (z + ![(a : ℤ), -(b : ℤ)]) (z + ![(b : ℤ), b]) ∩
          crossing 1 (z + ![-(b : ℤ), -(b : ℤ)]) (z + ![-(a : ℤ), b])) := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_le_law_crossing_of_half_le 4
  refine ⟨c ^ 4, ENNReal.pow_pos hc 4, fun q hq z a b ha hb => ?_⟩
  subst hb
  -- each strip is a `4a × a` box crossed in its long direction
  have hH : ∀ lo hi : LatticeSite 2, hi 0 = lo 0 + 4 * a → hi 1 = lo 1 + a →
      c ≤ law q (crossing 0 lo hi) := by
    intro lo hi h0 h1
    have h := hcq q hq 0 lo a ha
    rw [ite_eq_left rfl] at h
    convert h using 3
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.add_apply, Matrix.cons_val_zero, Nat.cast_ofNat]
      omega
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  have hV : ∀ lo hi : LatticeSite 2, hi 0 = lo 0 + a → hi 1 = lo 1 + 4 * a →
      c ≤ law q (crossing 1 lo hi) := by
    intro lo hi h0 h1
    have h := hcq q hq 1 lo a ha
    rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] at h
    convert h using 3
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.add_apply, Matrix.cons_val_zero]
      omega
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_ofNat]
      omega
  have hT := hH (z + ![-((2 * a : ℕ) : ℤ), a]) (z + ![((2 * a : ℕ) : ℤ), (2 * a : ℕ)])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have hD := hH (z + ![-((2 * a : ℕ) : ℤ), -((2 * a : ℕ) : ℤ)]) (z + ![((2 * a : ℕ) : ℤ), -(a : ℤ)])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have hR := hV (z + ![(a : ℤ), -((2 * a : ℕ) : ℤ)]) (z + ![((2 * a : ℕ) : ℤ), (2 * a : ℕ)])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  have hL := hV (z + ![-((2 * a : ℕ) : ℤ), -((2 * a : ℕ) : ℤ)]) (z + ![-(a : ℤ), (2 * a : ℕ)])
    (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega)
    (by simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; omega)
  -- Harris's inequality for the four increasing crossings
  set A₁ := crossing 0 (z + ![-((2 * a : ℕ) : ℤ), a]) (z + ![((2 * a : ℕ) : ℤ), (2 * a : ℕ)])
    with hA₁
  set A₂ := crossing 0 (z + ![-((2 * a : ℕ) : ℤ), -((2 * a : ℕ) : ℤ)])
    (z + ![((2 * a : ℕ) : ℤ), -(a : ℤ)]) with hA₂
  set A₃ := crossing 1 (z + ![(a : ℤ), -((2 * a : ℕ) : ℤ)])
    (z + ![((2 * a : ℕ) : ℤ), (2 * a : ℕ)]) with hA₃
  set A₄ := crossing 1 (z + ![-((2 * a : ℕ) : ℤ), -((2 * a : ℕ) : ℤ)])
    (z + ![-(a : ℤ), (2 * a : ℕ)]) with hA₄
  have hu₁ : IsUpperSet A₁ := isUpperSet_crossing _ _ _
  have hu₂ : IsUpperSet A₂ := isUpperSet_crossing _ _ _
  have hu₃ : IsUpperSet A₃ := isUpperSet_crossing _ _ _
  have hu₄ : IsUpperSet A₄ := isUpperSet_crossing _ _ _
  have hm₁ : MeasurableSet A₁ := measurableSet_crossing _ _ _
  have hm₂ : MeasurableSet A₂ := measurableSet_crossing _ _ _
  have hm₃ : MeasurableSet A₃ := measurableSet_crossing _ _ _
  have hm₄ : MeasurableSet A₄ := measurableSet_crossing _ _ _
  calc c ^ 4 = c * c * c * c := by ring
    _ ≤ law q A₁ * law q A₂ * law q A₃ * law q A₄ := by gcongr
    _ ≤ law q (A₁ ∩ A₂) * law q A₃ * law q A₄ := by
        gcongr
        exact prodBernoulli_harris q hu₁ hu₂ hm₁ hm₂
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃) * law q A₄ := by
        gcongr
        exact prodBernoulli_harris q (hu₁.inter hu₂) hu₃ (hm₁.inter hm₂) hm₃
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃ ∩ A₄) :=
        prodBernoulli_harris q ((hu₁.inter hu₂).inter hu₃) hu₄ ((hm₁.inter hm₂).inter hm₃) hm₄

/-! ### (A2): comparison of connections across an annulus -/

/-- **(A2), lower bound** (Basu–Sapozhnikov (1.2) on `ℤ²`). There is `c > 0` such that for every
profile opening each edge with probability at least `1/2`, every centre `z`, every `m ≥ 1`,
every set `Z` containing the annulus `B_{4m}(z) \ B_{m-1}(z)`, every `X ⊆ B_m(z)` and every `Y`
outside `B_{4m}(z)`,
`c · P(X ↔ ∂B_{2m}(z) in Z) · P(Y ↔ ∂B_{2m}(z) in Z) ≤ P(X ↔ Y in Z)`. -/
theorem exists_pos_mul_le_law_setOf_localConn :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (m : ℕ), 1 ≤ m → ∀ X Y Z : Set (LatticeSite 2),
        Icc (z - ((4 * m : ℕ) : LatticeSite 2)) (z + ((4 * m : ℕ) : LatticeSite 2)) \
          Icc (z - (m : LatticeSite 2) + 1) (z + m - 1) ⊆ Z →
        X ⊆ Icc (z - (m : LatticeSite 2)) (z + m) →
        (∀ y ∈ Y, y ∉
          Icc (z - ((4 * m : ℕ) : LatticeSite 2)) (z + ((4 * m : ℕ) : LatticeSite 2))) →
        c * law q {ω | ∃ x ∈ X, ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2))
              (z + ((2 * m : ℕ) : LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x w} *
          law q {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2))
              (z + ((2 * m : ℕ) : LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w} ≤
          law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} := by
  obtain ⟨cC, hcC, hcCq⟩ := exists_pos_le_law_annulus_crossings
  obtain ⟨cR, hcR, hcRq⟩ := exists_pos_le_law_crossing_of_half_le 3
  refine ⟨cC * cC * cR, ENNReal.mul_pos (ENNReal.mul_pos hcC.ne' hcC.ne').ne' hcR.ne',
    fun q hq z m hm X Y Z hZ hX hY => ?_⟩
  have hS : ∀ (v : LatticeSite 2) (p₁ p₂ p₃ p₄ : ℤ), v ∈ Icc (z + ![p₁, p₂]) (z + ![p₃, p₄]) ↔
      z 0 + p₁ ≤ v 0 ∧ v 0 ≤ z 0 + p₃ ∧ z 1 + p₂ ≤ v 1 ∧ v 1 ≤ z 1 + p₄ := by
    intro v p₁ p₂ p₃ p₄
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hZ' : ∀ v : LatticeSite 2, z 0 - 4 * m ≤ v 0 → v 0 ≤ z 0 + 4 * m → z 1 - 4 * m ≤ v 1 →
      v 1 ≤ z 1 + 4 * m → (v 0 ≤ z 0 - m ∨ z 0 + m ≤ v 0 ∨ v 1 ≤ z 1 - m ∨ z 1 + m ≤ v 1) →
      v ∈ Z := by
    intro v h₁ h₂ h₃ h₄ h₅
    apply hZ
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
    omega
  -- the events
  set AX := {ω : Config (LatticeSite 2) | ∃ x ∈ X, ∃ w ∈ boxBoundary
    (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)),
    ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x w} with hAX
  set AY := {ω : Config (LatticeSite 2) | ∃ y ∈ Y, ∃ w ∈ boxBoundary
    (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)),
    ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w} with hAY
  set Cin := crossing 0 (z + ![-((2 * m : ℕ) : ℤ), m]) (z + ![((2 * m : ℕ) : ℤ), (2 * m : ℕ)]) ∩
    crossing 0 (z + ![-((2 * m : ℕ) : ℤ), -((2 * m : ℕ) : ℤ)])
      (z + ![((2 * m : ℕ) : ℤ), -(m : ℤ)]) ∩
    crossing 1 (z + ![(m : ℤ), -((2 * m : ℕ) : ℤ)]) (z + ![((2 * m : ℕ) : ℤ), (2 * m : ℕ)]) ∩
    crossing 1 (z + ![-((2 * m : ℕ) : ℤ), -((2 * m : ℕ) : ℤ)]) (z + ![-(m : ℤ), (2 * m : ℕ)])
    with hCin
  set Cout := crossing 0 (z + ![-((4 * m : ℕ) : ℤ), (2 * m : ℕ)])
      (z + ![((4 * m : ℕ) : ℤ), (4 * m : ℕ)]) ∩
    crossing 0 (z + ![-((4 * m : ℕ) : ℤ), -((4 * m : ℕ) : ℤ)])
      (z + ![((4 * m : ℕ) : ℤ), -((2 * m : ℕ) : ℤ)]) ∩
    crossing 1 (z + ![((2 * m : ℕ) : ℤ), -((4 * m : ℕ) : ℤ)])
      (z + ![((4 * m : ℕ) : ℤ), (4 * m : ℕ)]) ∩
    crossing 1 (z + ![-((4 * m : ℕ) : ℤ), -((4 * m : ℕ) : ℤ)])
      (z + ![-((2 * m : ℕ) : ℤ), (4 * m : ℕ)]) with hCout
  set R := crossing 0 (z + ![(m : ℤ), 0]) (z + ![((4 * m : ℕ) : ℤ), m]) with hR
  -- their probabilities
  have hCinb : cC ≤ law q Cin := hcCq q hq z m (2 * m) hm rfl
  have hCoutb : cC ≤ law q Cout := hcCq q hq z (2 * m) (4 * m) (by omega) (by ring)
  have hRb : cR ≤ law q R := by
    have h := hcRq q hq 0 (z + ![(m : ℤ), 0]) m hm
    rw [ite_eq_left rfl] at h
    convert h using 3
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [Pi.add_apply, Matrix.cons_val_zero, Nat.cast_ofNat]
      omega
    · simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  -- the two arms, the two circuits and the radial crossing give the connection
  have hsub : AX ∩ AY ∩ Cin ∩ Cout ∩ R ⊆
      {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} := by
    rintro ω ⟨⟨⟨⟨⟨x, hxX, w₁, hw₁, hxw₁⟩, ⟨y, hyY, w₂, hw₂, hyw₂⟩⟩, hin⟩, hout⟩,
      ⟨r₀, hr₀, hr₀0, r₁, -, hr₁0, hr⟩⟩
    have hr₀' := (hS r₀ _ _ _ _).1 hr₀
    simp only [Pi.add_apply, Matrix.cons_val_zero] at hr₀0 hr₁0
    have hRZ : Icc (z + ![(m : ℤ), 0]) (z + ![((4 * m : ℕ) : ℤ), m]) ⊆ Z := fun v hv => by
      rw [hS] at hv
      exact hZ' v (by omega) (by omega) (by omega) (by omega) (by omega)
    have hAin : Icc (z - ((2 * m : ℕ) : LatticeSite 2)) (z + ((2 * m : ℕ) : LatticeSite 2)) \
        Icc (z - (m : LatticeSite 2) + 1) (z + m - 1) ⊆ Z := fun v hv => by
      rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff] at hv
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv
      exact hZ' v (by omega) (by omega) (by omega) (by omega) (by omega)
    have hAout : Icc (z - ((4 * m : ℕ) : LatticeSite 2)) (z + ((4 * m : ℕ) : LatticeSite 2)) \
        Icc (z - ((2 * m : ℕ) : LatticeSite 2) + 1) (z + ((2 * m : ℕ) : LatticeSite 2) - 1) ⊆
        Z := fun v hv => by
      rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff] at hv
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv
      exact hZ' v (by omega) (by omega) (by omega) (by omega) (by omega)
    have hw₁' := mem_boxBoundary_two_iff.1 hw₁
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hw₁'
    have hyB := hY y hyY
    rw [mem_Icc_two_iff] at hyB
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hyB
    -- inner circuit: `x` is joined to the start of the radial crossing
    have h₁ := inter_edgeSet_mem_localConn_of_mem_annulus_crossings (a := m) (b := 2 * m)
      (by omega) hin (hX hxX)
      (by
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
        omega)
      (by
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
        omega)
      (by
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
        omega) hxw₁ hr
    have h₁' := localConn_mono_set (union_subset (union_subset Subset.rfl hRZ) hAin) _ _ h₁
    -- outer circuit: the end of the arm from `Y` is joined to the start of the radial crossing
    rw [localConn_comm] at hyw₂
    have h₂ := inter_edgeSet_mem_localConn_of_mem_annulus_crossings (a := 2 * m) (b := 4 * m)
      (by omega) hout (boxBoundary_subset_Icc _ _ hw₂)
      (by
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
        omega)
      (by
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
        omega)
      (by
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
        omega) hyw₂ hr
    have h₂' := localConn_mono_set (union_subset (union_subset Subset.rfl hRZ) hAout) _ _ h₂
    rw [localConn_comm] at h₂'
    exact ⟨x, hxX, y, hyY, localConn_trans h₁' (localConn_trans h₂' hyw₂)⟩
  -- Harris's inequality for the five increasing events
  have hAXm : MeasurableSet AX := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hAYm : MeasurableSet AY := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hAXu : IsUpperSet AX := isUpperSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hAYu : IsUpperSet AY := isUpperSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hCinm : MeasurableSet Cin := (((measurableSet_crossing _ _ _).inter
    (measurableSet_crossing _ _ _)).inter (measurableSet_crossing _ _ _)).inter
    (measurableSet_crossing _ _ _)
  have hCinu : IsUpperSet Cin := (((isUpperSet_crossing _ _ _).inter
    (isUpperSet_crossing _ _ _)).inter (isUpperSet_crossing _ _ _)).inter
    (isUpperSet_crossing _ _ _)
  have hCoutm : MeasurableSet Cout := (((measurableSet_crossing _ _ _).inter
    (measurableSet_crossing _ _ _)).inter (measurableSet_crossing _ _ _)).inter
    (measurableSet_crossing _ _ _)
  have hCoutu : IsUpperSet Cout := (((isUpperSet_crossing _ _ _).inter
    (isUpperSet_crossing _ _ _)).inter (isUpperSet_crossing _ _ _)).inter
    (isUpperSet_crossing _ _ _)
  have hRm : MeasurableSet R := measurableSet_crossing _ _ _
  have hRu : IsUpperSet R := isUpperSet_crossing _ _ _
  calc cC * cC * cR * law q AX * law q AY = law q AX * law q AY * cC * cC * cR := by ring
    _ ≤ law q AX * law q AY * law q Cin * law q Cout * law q R := by gcongr
    _ ≤ law q (AX ∩ AY) * law q Cin * law q Cout * law q R := by
        gcongr
        exact prodBernoulli_harris q hAXu hAYu hAXm hAYm
    _ ≤ law q (AX ∩ AY ∩ Cin) * law q Cout * law q R := by
        gcongr
        exact prodBernoulli_harris q (hAXu.inter hAYu) hCinu (hAXm.inter hAYm) hCinm
    _ ≤ law q (AX ∩ AY ∩ Cin ∩ Cout) * law q R := by
        gcongr
        exact prodBernoulli_harris q ((hAXu.inter hAYu).inter hCinu) hCoutu
          ((hAXm.inter hAYm).inter hCinm) hCoutm
    _ ≤ law q (AX ∩ AY ∩ Cin ∩ Cout ∩ R) :=
        prodBernoulli_harris q (((hAXu.inter hAYu).inter hCinu).inter hCoutu) hRu
          (((hAXm.inter hAYm).inter hCinm).inter hCoutm) hRm
    _ ≤ _ := measure_mono hsub

/-- **(A2), upper bound.** For every profile, every centre `z` and radius `r`, every `X ⊆ B_r(z)`,
every `Y` outside `B_r(z)` and every set `Z`,
`P(X ↔ Y in Z) ≤ P(X ↔ ∂B_r(z) in Z) · P(Y ↔ ∂B_r(z) in Z)`. The path from `X` up to its first
visit to `∂B_r(z)` uses only pairs inside `B_r(z)`; the path from `Y` up to its first visit to
`B_r(z)` uses only pairs not inside `B_r(z)`, and these two families of pairs are disjoint. -/
theorem law_setOf_localConn_le_mul (q : Sym2 (LatticeSite 2) → unitInterval)
    (z : LatticeSite 2) (r : ℕ) {X Y Z : Set (LatticeSite 2)}
    (hX : X ⊆ Icc (z - (r : LatticeSite 2)) (z + r))
    (hY : ∀ y ∈ Y, y ∉ Icc (z - (r : LatticeSite 2)) (z + r)) :
    law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} ≤
      law q {ω | ∃ x ∈ X, ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x w} *
        law q {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w} := by
  classical
  set B := Icc (z - (r : LatticeSite 2)) (z + r) with hB
  set P : Set (Sym2 (LatticeSite 2)) := {e | ∀ v ∈ e, v ∈ B} with hP
  set E₁ := {ω : Config (LatticeSite 2) | ∃ x ∈ X, ∃ w ∈ boxBoundary
    (z - (r : LatticeSite 2)) (z + r), ω ∩ (zdGraph 2).edgeSet ∈ localConn (Z ∩ B) x w} with hE₁
  set E₂ := {ω : Config (LatticeSite 2) | ∃ y ∈ Y, ∃ w ∈ B,
    ω ∩ ((zdGraph 2).edgeSet ∩ Pᶜ) ∈ localConn Z y w} with hE₂
  have hBin : ∀ v, v ∉ B → v ∉ Icc (z - (r : LatticeSite 2) + 1) (z + r - 1) := by
    intro v hv hv'
    apply hv
    rw [hB, mem_Icc_two_iff]
    rw [mem_Icc_two_iff] at hv'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv' ⊢
    omega
  -- a connection from `X` to `Y` gives both pieces
  have hsub : {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} ⊆ E₁ ∩ E₂ := by
    rintro ω ⟨x, hxX, y, hyY, hxy⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hxw⟩ :=
        exists_mem_boxBoundary_mem_localConn_inter (hX hxX) (hBin y (hY y hyY)) hxy
      exact ⟨x, hxX, w, hw, hxw⟩
    · obtain ⟨p, hp⟩ := mem_localConn_iff_exists_walk.1 hxy
      obtain ⟨c, hcB, q, hq₁, -, hq₃⟩ := SimpleGraph.Walk.exists_walk_first_mem (· ∈ B) p.reverse
        ⟨x, by simp, hX hxX⟩
      have hqZ : ∀ v ∈ q.support, v ∈ Z := fun v hv => by
        have := hq₁ v hv
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
        exact hp v this
      have hqE : ∀ e ∈ q.edges,
          e ∈ (openGraph (ω ∩ ((zdGraph 2).edgeSet ∩ Pᶜ))).edgeSet := by
        intro e he
        have he' := q.edges_subset_edgeSet he
        induction e using Sym2.ind with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet, openGraph_adj_iff] at he' ⊢
          refine ⟨⟨he'.1.1, he'.1.2, fun hPe => he'.2 ?_⟩, he'.2⟩
          have hu := hq₃ u (q.fst_mem_support_of_mem_edges he) (hPe u (Sym2.mem_mk_left u v))
          have hv := hq₃ v (q.snd_mem_support_of_mem_edges he) (hPe v (Sym2.mem_mk_right u v))
          rw [hu, hv]
      refine ⟨y, hyY, c, hcB, mem_localConn_iff_exists_walk.2 ⟨q.transfer _ hqE, ?_⟩⟩
      rw [SimpleGraph.Walk.support_transfer]
      exact hqZ
  -- the two pieces are independent
  have hE₁m : MeasurableSet E₁ := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hE₂m : MeasurableSet E₂ := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hind : law q (E₁ ∩ E₂) = law q E₁ * law q E₂ := by
    refine prodBernoulli_inter_of_determined q (disjoint_compl_right : Disjoint P Pᶜ) hE₁m hE₂m
      (fun ω ω' h => ?_) (fun ω ω' h => ?_)
    · simp only [hE₁, mem_ofPred_eq,
        inter_mem_localConn_iff_of_inter_eq inter_subset_right (zdGraph 2).edgeSet h]
    · have h' : ω ∩ ((zdGraph 2).edgeSet ∩ Pᶜ) = ω' ∩ ((zdGraph 2).edgeSet ∩ Pᶜ) := by
        rw [inter_left_comm, h, inter_left_comm]
      simp only [hE₂, mem_ofPred_eq, h']
  -- each piece is contained in the corresponding connection to `∂B_r(z)`
  have h₁ : E₁ ⊆ {ω | ∃ x ∈ X, ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x w} := fun ω ⟨x, hx, w, hw, hxw⟩ =>
    ⟨x, hx, w, hw, localConn_mono_set inter_subset_left _ _ hxw⟩
  have h₂ : E₂ ⊆ {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w} := by
    rintro ω ⟨y, hyY, w, hwB, hyw⟩
    have hyw' : ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w :=
      localConn_mono (inter_subset_inter_right ω inter_subset_left) hyw
    obtain ⟨c, hc, hyc⟩ := exists_mem_boxBoundary_mem_localConn_diff (hBin y (hY y hyY)) hwB hyw'
    exact ⟨y, hyY, c, hc, localConn_mono_set sdiff_subset _ _ hyc⟩
  calc law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y}
      ≤ law q (E₁ ∩ E₂) := measure_mono hsub
    _ = law q E₁ * law q E₂ := hind
    _ ≤ _ := by gcongr

/-- **(A2), upper bound, inside-outside form.** For every profile, every centre `z` and radius `r`,
every `X ⊆ B_r(z)`, every `Y` outside `B_r(z)` and every set `Z`,
`P(X ↔ Y in Z) ≤ P(X ↔ ∂B_r(z) in Z ∩ B_r(z)) · P(∂B_{r+1}(z) ↔ Y in Z \ B_r(z))`, by
independence of the pairs inside `B_r(z)` and those inside its complement. -/
theorem law_setOf_localConn_le_mul_inside_outside (q : Sym2 (LatticeSite 2) → unitInterval)
    (z : LatticeSite 2) (r : ℕ) {X Y Z : Set (LatticeSite 2)}
    (hX : X ⊆ Icc (z - (r : LatticeSite 2)) (z + r))
    (hY : ∀ y ∈ Y, y ∉ Icc (z - (r : LatticeSite 2)) (z + r)) :
    law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} ≤
      law q {ω | ∃ x ∈ X, ∃ w ∈ boxBoundary (z - (r : LatticeSite 2)) (z + r),
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Z ∩ Icc (z - (r : LatticeSite 2)) (z + r)) x w} *
        law q {ω | ∃ w ∈ boxBoundary (z - ((r + 1 : ℕ) : LatticeSite 2))
            (z + ((r + 1 : ℕ) : LatticeSite 2)), ∃ y ∈ Y,
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Z \ Icc (z - (r : LatticeSite 2)) (z + r)) w y} := by
  set B := Icc (z - (r : LatticeSite 2)) (z + r) with hB
  set E₁ := {ω : Config (LatticeSite 2) | ∃ x ∈ X, ∃ w ∈ boxBoundary
    (z - (r : LatticeSite 2)) (z + r), ω ∩ (zdGraph 2).edgeSet ∈ localConn (Z ∩ B) x w} with hE₁
  set E₂ := {ω : Config (LatticeSite 2) | ∃ w ∈ boxBoundary (z - ((r + 1 : ℕ) : LatticeSite 2))
    (z + ((r + 1 : ℕ) : LatticeSite 2)), ∃ y ∈ Y,
    ω ∩ (zdGraph 2).edgeSet ∈ localConn (Z \ B) w y} with hE₂
  have hsub : {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} ⊆ E₁ ∩ E₂ := by
    rintro ω ⟨x, hxX, y, hyY, hxy⟩
    have hxB := hX hxX
    have hyB := hY y hyY
    rw [hB, mem_Icc_two_iff] at hxB hyB
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hxB hyB
    have hy₁ : y ∉ Icc (z - (r : LatticeSite 2) + 1) (z + r - 1) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega
    have hy₂ : y ∉ Icc (z - ((r + 1 : ℕ) : LatticeSite 2) + 1)
        (z + ((r + 1 : ℕ) : LatticeSite 2) - 1) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
      omega
    have hx₂ : x ∈ Icc (z - ((r + 1 : ℕ) : LatticeSite 2)) (z + ((r + 1 : ℕ) : LatticeSite 2)) := by
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      omega
    have hsubset : Z \ Icc (z - ((r + 1 : ℕ) : LatticeSite 2) + 1)
        (z + ((r + 1 : ℕ) : LatticeSite 2) - 1) ⊆ Z \ B := by
      intro v hv
      refine ⟨hv.1, fun hvB => hv.2 ?_⟩
      rw [hB, mem_Icc_two_iff] at hvB
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hvB ⊢
      omega
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hxw⟩ := exists_mem_boxBoundary_mem_localConn_inter (hX hxX) hy₁ hxy
      exact ⟨x, hxX, w, hw, hxw⟩
    · rw [localConn_comm] at hxy
      obtain ⟨w, hw, hyw⟩ := exists_mem_boxBoundary_mem_localConn_diff hy₂ hx₂ hxy
      refine ⟨w, hw, y, hyY, ?_⟩
      rw [localConn_comm]
      exact localConn_mono_set hsubset _ _ hyw
  have hE₁m : MeasurableSet E₁ := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hE₂m : MeasurableSet E₂ := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hind : law q (E₁ ∩ E₂) = law q E₁ * law q E₂ := by
    refine law_inter_of_determined_internalPairs q (disjoint_compl_right : Disjoint B Bᶜ) hE₁m hE₂m
      (fun ω ω' h => ?_) (fun ω ω' h => ?_)
    · simp only [hE₁, mem_ofPred_eq,
        inter_mem_localConn_iff_of_inter_eq inter_subset_right (zdGraph 2).edgeSet h]
    · simp only [hE₂, mem_ofPred_eq,
        inter_mem_localConn_iff_of_inter_eq (sdiff_subset_compl Z B) (zdGraph 2).edgeSet h]
  calc law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y}
      ≤ law q (E₁ ∩ E₂) := measure_mono hsub
    _ = law q E₁ * law q E₂ := hind

/-- **(A2) in both directions.** There is `c > 0` such that for every profile opening each edge
with probability at least `1/2`, every centre `z`, every `m ≥ 1`, every set `Z` containing the
annulus `B_{4m}(z) \ B_{m-1}(z)`, every `X ⊆ B_m(z)` and every `Y` outside `B_{4m}(z)`, the
probability `P(X ↔ Y in Z)` lies between `c` times and one times
`P(X ↔ ∂B_{2m}(z) in Z) · P(Y ↔ ∂B_{2m}(z) in Z)`. -/
theorem exists_law_setOf_localConn_comparable :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (m : ℕ), 1 ≤ m → ∀ X Y Z : Set (LatticeSite 2),
        Icc (z - ((4 * m : ℕ) : LatticeSite 2)) (z + ((4 * m : ℕ) : LatticeSite 2)) \
          Icc (z - (m : LatticeSite 2) + 1) (z + m - 1) ⊆ Z →
        X ⊆ Icc (z - (m : LatticeSite 2)) (z + m) →
        (∀ y ∈ Y, y ∉
          Icc (z - ((4 * m : ℕ) : LatticeSite 2)) (z + ((4 * m : ℕ) : LatticeSite 2))) →
        c * law q {ω | ∃ x ∈ X, ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2))
              (z + ((2 * m : ℕ) : LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x w} *
          law q {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2))
              (z + ((2 * m : ℕ) : LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w} ≤
          law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} ∧
        law q {ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y} ≤
          law q {ω | ∃ x ∈ X, ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2))
              (z + ((2 * m : ℕ) : LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x w} *
          law q {ω | ∃ y ∈ Y, ∃ w ∈ boxBoundary (z - ((2 * m : ℕ) : LatticeSite 2))
              (z + ((2 * m : ℕ) : LatticeSite 2)), ω ∩ (zdGraph 2).edgeSet ∈ localConn Z y w} := by
  obtain ⟨c, hc, hcq⟩ := exists_pos_mul_le_law_setOf_localConn
  refine ⟨c, hc, fun q hq z m hm X Y Z hZ hX hY =>
    ⟨hcq q hq z m hm X Y Z hZ hX hY, law_setOf_localConn_le_mul q z (2 * m) ?_ ?_⟩⟩
  · intro x hx
    have := hX hx
    rw [mem_Icc_two_iff] at this ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at this ⊢
    omega
  · intro y hy hy'
    apply hY y hy
    rw [mem_Icc_two_iff] at hy' ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hy' ⊢
    omega

/-! ### (A1): uniqueness of the open crossing cluster of an annulus -/

/-- **No circuit at many scales is unlikely, even given an increasing event.** There is `c₀ > 0`
such that for every profile opening each edge with probability at least `1/2`, every measurable
increasing event `E`, every centre `z` and all scales `n j ≥ 1` (`j ∈ s`) with
`2 n_j < n_{j'}` for `j < j'`, the probability that `E` holds and no four-strip event of these
scales does is at most `(1 - c₀)^{#s} P(E)`. The four-strip annuli are disjoint, so their events
are independent; the event that none holds is decreasing, hence negatively correlated with `E`. -/
theorem exists_law_inter_biInter_compl_fourStrip_le :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ E : Set (Config (LatticeSite 2)), IsUpperSet E → MeasurableSet E →
      ∀ (z : LatticeSite 2) (s : Finset ℕ) (n : ℕ → ℕ), (∀ j ∈ s, 1 ≤ n j) →
        (∀ j ∈ s, ∀ j' ∈ s, j < j' → 2 * n j < n j') →
        law q (E ∩ ⋂ j ∈ s, (fourStrip z (n j))ᶜ) ≤ (1 - c₀) ^ s.card * law q E := by
  obtain ⟨c₀, hc₀, hcq⟩ := exists_pos_le_law_fourStrip_of_half_le
  refine ⟨c₀, hc₀, fun q hq E hEu hEm z s n hn hsep => ?_⟩
  have hDm : MeasurableSet (⋂ j ∈ s, (fourStrip z (n j))ᶜ) :=
    Finset.measurableSet_biInter s fun j _ => (measurableSet_fourStrip _ _).compl
  have hDl : IsLowerSet (⋂ j ∈ s, (fourStrip z (n j))ᶜ) :=
    isLowerSet_iInter₂ fun j _ => (isUpperSet_fourStrip _ _).compl
  -- the four-strip annuli are pairwise disjoint
  set S : ℕ → Set (LatticeSite 2) := fun j => {v : LatticeSite 2 | z 0 - 4 * n j ≤ v 0 ∧
    v 0 ≤ z 0 + 4 * n j ∧ z 1 - 4 * n j ≤ v 1 ∧ v 1 ≤ z 1 + 4 * n j ∧
    (v 0 ≤ z 0 - 2 * n j ∨ z 0 + 2 * n j ≤ v 0 ∨ v 1 ≤ z 1 - 2 * n j ∨ z 1 + 2 * n j ≤ v 1)}
    with hSdef
  have hdisj : Set.PairwiseDisjoint (s : Set ℕ) S := by
    intro j hj j' hj' hne
    refine Set.disjoint_left.2 fun v hv hv' => ?_
    simp only [hSdef, mem_ofPred_eq] at hv hv'
    rcases lt_or_gt_of_ne hne with h | h
    · have := hsep j hj j' hj' h
      omega
    · have := hsep j' hj' j hj h
      omega
  have hind : law q (⋂ j ∈ s, (fourStrip z (n j))ᶜ) = ∏ j ∈ s, law q (fourStrip z (n j))ᶜ :=
    law_biInter_of_determined_internalPairs q s hdisj
      (fun j _ => (measurableSet_fourStrip _ _).compl)
      (fun j ω ω' h => by
        rw [mem_compl_iff, mem_compl_iff, mem_fourStrip_iff_of_inter_eq subset_rfl h])
  have hbound : law q (⋂ j ∈ s, (fourStrip z (n j))ᶜ) ≤ (1 - c₀) ^ s.card := by
    rw [hind]
    refine Finset.prod_le_pow_card _ _ _ fun j hj => ?_
    rw [prob_compl_eq_one_sub (measurableSet_fourStrip _ _)]
    exact tsub_le_tsub_left (hcq q hq z (n j) (hn j hj)) 1
  calc law q (E ∩ ⋂ j ∈ s, (fourStrip z (n j))ᶜ)
      ≤ law q E * law q (⋂ j ∈ s, (fourStrip z (n j))ᶜ) :=
        prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet q hEu hDl hEm hDm
    _ ≤ law q E * (1 - c₀) ^ s.card := by gcongr
    _ = (1 - c₀) ^ s.card * law q E := mul_comm _ _

/-- **(A1): uniqueness of the open crossing cluster of an annulus** (Basu–Sapozhnikov
(1.3)-(1.4) on `ℤ²`). There is `c₀ > 0` such that for every profile opening each edge with
probability at least `1/2`, every measurable increasing event `E`, every centre `z` and all
`N ≥ 1`, `k` and `M ≥ 4^k N`, the probability that `E` holds and the annulus
`A = B_M(z) \ B_{N-1}(z)` has two distinct open crossing clusters (points `a, a'` of `∂B_N(z)`
and `b, b'` of `∂B_M(z)` with `a ↔ b` and `a' ↔ b'` but not `a ↔ a'`, all inside `A`) is at most
`(1 - c₀)^k P(E)`. -/
theorem exists_law_inter_setOf_crossing_clusters_le :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ E : Set (Config (LatticeSite 2)), IsUpperSet E → MeasurableSet E →
      ∀ (z : LatticeSite 2) (N M k : ℕ), 1 ≤ N → 4 ^ k * N ≤ M →
        law q (E ∩ {ω | ∃ a ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
          ∃ a' ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
          ∃ b ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
          ∃ b' ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
            ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
              Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a b ∧
            ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
              Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a' b' ∧
            ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
              Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a a'}) ≤
          (1 - c₀) ^ k * law q E := by
  obtain ⟨c₀, hc₀, hcq⟩ := exists_law_inter_biInter_compl_fourStrip_le
  refine ⟨c₀, hc₀, fun q hq E hEu hEm z N M k hN hM => ?_⟩
  -- the scales `n j = 4^j N`
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, n = fun j => 4 ^ j * N := ⟨_, rfl⟩
  have hn1 : ∀ j, 1 ≤ n j := fun j => by
    rw [hn]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hnN : ∀ j, N ≤ n j := fun j => by
    rw [hn]
    exact Nat.le_mul_of_pos_left N (by positivity)
  have hn4 : ∀ j, n (j + 1) = 4 * n j := fun j => by
    rw [hn]
    ring
  have hnmono : Monotone n := monotone_nat_of_le_succ fun j => by
    have := hn4 j
    omega
  have hnM : ∀ j < k, 4 * n j ≤ M := fun j hj => by
    have h₁ := hnmono (show j + 1 ≤ k from hj)
    have h₂ : n k ≤ M := by
      rw [hn]
      exact hM
    have := hn4 j
    omega
  have hsep : ∀ j ∈ Finset.range k, ∀ j' ∈ Finset.range k, j < j' → 2 * n j < n j' := by
    intro j _ j' _ hjj'
    have := hnmono (show j + 1 ≤ j' from hjj')
    have := hn4 j
    have := hn1 j
    omega
  -- two distinct crossing clusters exclude every four-strip event of these scales
  have hsub : {ω | ∃ a ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
      ∃ a' ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
      ∃ b ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
      ∃ b' ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
          Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a b ∧
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
          Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a' b' ∧
        ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
          Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a a'} ⊆
      ⋂ j ∈ Finset.range k, (fourStrip z (n j))ᶜ := by
    rintro ω ⟨a, ha, a', ha', b, hb, b', hb', hab, ha'b', hna⟩
    simp only [mem_iInter, Finset.mem_range, mem_compl_iff]
    intro j hj hω
    have hin : ∀ v ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
        v ∈ Icc (z - ((2 * n j : ℕ) : LatticeSite 2)) (z + ((2 * n j : ℕ) : LatticeSite 2)) :=
      fun v hv => by
        rw [mem_boxBoundary_two_iff] at hv
        rw [mem_Icc_two_iff]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hv ⊢
        have := hnN j
        omega
    have hout : ∀ v ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
        v ∉ Icc (z - ((4 * n j : ℕ) : LatticeSite 2) + 1)
          (z + ((4 * n j : ℕ) : LatticeSite 2) - 1) := fun v hv => by
      rw [mem_boxBoundary_two_iff] at hv
      rw [mem_Icc_two_iff]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
      have := hnM j hj
      omega
    apply hna
    refine localConn_mono_set (union_subset (union_subset Subset.rfl Subset.rfl) ?_) _ _
      (inter_edgeSet_mem_localConn_union_of_mem_fourStrip hω (hin a ha) (hout b hb)
        (hin a' ha') (hout b' hb') hab ha'b')
    intro v hv
    rw [mem_sdiff, mem_Icc_two_iff, mem_Icc_two_iff] at hv ⊢
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply] at hv ⊢
    have := hnM j hj
    have := hnN j
    omega
  calc law q (E ∩ _)
      ≤ law q (E ∩ ⋂ j ∈ Finset.range k, (fourStrip z (n j))ᶜ) :=
        measure_mono (inter_subset_inter_right E hsub)
    _ ≤ (1 - c₀) ^ (Finset.range k).card * law q E :=
        hcq q hq E hEu hEm z (Finset.range k) n (fun j _ => hn1 j) hsep
    _ = (1 - c₀) ^ k * law q E := by rw [Finset.card_range]

/-- **(A1), conditional form** (Basu–Sapozhnikov (1.4) on `ℤ²`). There is `c₀ > 0` such that for
every profile opening each edge with probability at least `1/2`, every centre `z` and all
`N ≥ 1`, `k` and `M ≥ 4^k N`, the conditional probability, given that the annulus
`A = B_M(z) \ B_{N-1}(z)` is crossed (`∂B_N(z) ↔ ∂B_M(z)` inside `A`), that `A` has two distinct
open crossing clusters is at most `(1 - c₀)^k`. -/
theorem exists_cond_setOf_crossing_clusters_le :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e) →
      ∀ (z : LatticeSite 2) (N M k : ℕ), 1 ≤ N → 4 ^ k * N ≤ M →
        ProbabilityTheory.cond (law q)
          {ω | ∃ a ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
            ∃ b ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
                Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a b}
          {ω | ∃ a ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
            ∃ a' ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
            ∃ b ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
            ∃ b' ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
              ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
                Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a b ∧
              ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
                Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a' b' ∧
              ω ∩ (zdGraph 2).edgeSet ∉ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
                Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a a'} ≤
          (1 - c₀) ^ k := by
  obtain ⟨c₀, hc₀, hcq⟩ := exists_law_inter_setOf_crossing_clusters_le
  refine ⟨c₀, hc₀, fun q hq z N M k hN hM => ?_⟩
  set E₁ := {ω : Config (LatticeSite 2) | ∃ a ∈ boxBoundary (z - (N : LatticeSite 2)) (z + N),
    ∃ b ∈ boxBoundary (z - (M : LatticeSite 2)) (z + M),
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc (z - (M : LatticeSite 2)) (z + M) \
        Icc (z - (N : LatticeSite 2) + 1) (z + N - 1)) a b} with hE₁
  have hE₁m : MeasurableSet E₁ := measurableSet_setOf_exists_inter_mem_localConn _ _ _ _
  have hE₁u : IsUpperSet E₁ := isUpperSet_setOf_exists_inter_mem_localConn _ _ _ _
  have h := hcq q hq E₁ hE₁u hE₁m z N M k hN hM
  rw [ProbabilityTheory.cond_apply hE₁m]
  by_cases h0 : law q E₁ = 0
  · rw [measure_mono_null inter_subset_left h0, mul_zero]
    exact zero_le
  · calc (law q E₁)⁻¹ * law q (E₁ ∩ _) ≤ (law q E₁)⁻¹ * ((1 - c₀) ^ k * law q E₁) := by
          gcongr
      _ = (1 - c₀) ^ k := by
          rw [mul_comm ((1 - c₀) ^ k), ← mul_assoc, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _),
            one_mul]

end PercLib.Models.Planar
