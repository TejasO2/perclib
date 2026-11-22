/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: G. Grimmett, Percolation, 2nd ed., Springer, 1999, Section 11.2
(planar duality). The statement for four arcs of the boundary of a box is the square-lattice
form of the duality of crossings of quadrilaterals used in P. Nolin, Near-critical percolation
in two dimensions, Electron. J. Probab. 13 (2008), paper no. 55.
The proof below is a discrete parity argument and does not follow either text.
-/
module

public import PercLib.Models.Planar.Arms.Defs
public import PercLib.Models.Planar.Duality

/-!
# Quad duality on the square lattice

Let `R = Icc lo hi` be a box of `ℤ²` of positive width and height, with perimeter
`P = 2 (hi₀ - lo₀) + 2 (hi₁ - lo₁)`, and let `a < c < b < d < P + a`. Reading the perimeter
positions of boundary points (`perimeterPos`, counterclockwise from `lo`) modulo `P`, the boundary
of `R` splits into four consecutive arcs: `A` (positions in `[a, c)`), `C` (`[c, b)`), `B`
(`[b, d)`) and `D` (`[d, P + a)`). Faces are dual vertices, the face `f` standing for the unit
square with lower-left corner `f`; the faces inside `R` form the box `Icc lo (hi - 1)`, and the
faces touching `R` the box `Icc (lo - 1) hi`.

* The **dual arc** of `C` is the set of faces not inside `R` with a corner in `C`: the faces just
  outside `R` along `C`, including the outer faces of the two boundary edges that join `C` to `A`
  and to `B`. Likewise for `D`.
* A **dual-open path in the dual box** is a path of faces of `Icc (lo - 1) hi` whose steps are
  dual edges crossing edges of `R` (both ends in `R`) that are closed in `ω`: a path open in
  `dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi}`.

**Quad duality** says that exactly one holds: an open path inside `R` joins `A` to `B`, or a
dual-open path in the dual box joins the dual arc of `C` to that of `D`.

*At least one.* The proof generalises the parity argument of
`mem_crossing_one_dualConfig_of_notMem_crossing_zero`, the case of the four sides. The corners
(vertex in `R`, face inside `R` or in a dual arc) form a finite set on which, with the arcs wired
(the edges inside `A` or `B` and the edges leaving `R` from `A` or `B` open, the edges leaving `R`
from `C` or `D` closed), the partner maps `hPartner` and `vPartner` are involutions. Of the four
corners at the junctions of the arcs, only the one at the junction of `A` and `C` has its vertex
joined to `A` and its face joined to the dual arc of `C`, and exactly one of its two partners
leaves the set. If neither crossing existed, the corners whose vertex is joined to `A` and whose
face is joined to the dual arc of `C` would be counted in pairs by one partner map and, all but
one, by the other: a contradiction modulo two.

*Not both.* This generalises `notMem_crossing_one_dualConfig_of_mem_crossing_zero`. For a dual
path `σ` from the dual arc of `C` to that of `D`, let `N v` count modulo two the crossings by `σ`
of the path from `lo` up the left side of `R` and then along the row of `v` to `v`. Since `σ` has
no end at a face inside `R`, `N` changes across every edge of `R` by the crossings of that edge
(the crossings of the four edges of a face add up to the number of ends of `σ` at that face), so
`N` is constant on open clusters. Along the boundary it changes only at the boundary edges whose
outer face is an end of `σ`, which are one edge next to `C` and one next to `D`; these separate
`A` from `B`, so `N` differs on `A` and on `B`.

## Main results

* `mem_arcCrossing_iff_dualConfig_notMem_arcCrossing`: quad duality, exactly one.
* `exists_dualConfig_inter_mem_localConn_of_not_exists`: quad duality, at least one.
* `not_exists_dualConfig_inter_mem_localConn_of_exists`: quad duality, not both.
* `exists_dualConfig_inter_mem_localConn_of_arcs`: the parity argument, for any four sets of
  points with the properties of the arcs used by it.
* `perimeterPos_eq_add_one_or_of_notMem_Icc`, `eq_of_notMem_Icc_sub_one`,
  `exists_notMem_Icc_of_perimeterPos`: faces outside the box and perimeter positions.
* `eq_of_mem_localConn`, `eq_add_sum_of_perimeterPos`: the parity function of a dual walk is
  constant on open clusters and telescopes along the boundary.
* `ite_mem_eq_sum_ite_dualEdge`, `eq_of_mem_dualEdge_of_mem_dualEdge`,
  `eq_of_mem_dualEdge_of_notMem_Icc`, `exists_perimeterPos_eq_add_one_of_mem_dualEdge`: dual edges
  at a face, and the boundary edge of a face outside the box.
* `Finset.apply_mem_of_involutive_of_mapsTo`: counting a finite set with two involutions.

## Implementation notes

* The dual path uses only dual edges crossing edges of `R`. With every dual edge of the dual box
  allowed, quad duality would fail: if `A` is a single boundary point `x` that is not a corner of
  `R`, the outer faces on either side of `x` lie in the dual arcs of `D` and `C` and are joined by
  the dual edge crossing the edge from `x` out of `R`, which is open whenever that edge is
  closed, whatever happens inside `R`. Restricted to edges of `R`, both crossing events depend
  only on the edges of `R`.
* The box has positive width and height. On a segment `perimeterPos` runs along the boundary only
  once, so positions in `(hi₀ - lo₀, P)` (or `(hi₁ - lo₁, P)`) belong to no boundary point, and an
  arc can be empty: for `A` and `C` empty and every edge open neither crossing exists.
-/

@[expose] public section

open Set PercLib.Percolation.Bond PercLib.Models.Site

/-! ### Counting with two involutions -/

namespace Finset

/-- **Two involutions on a finite set.** Let `φ` and `ψ` be involutions without fixed points. If
`φ` maps a finite set `S` into itself and `ψ` maps every element of `S` except `J ∈ S` into `S`,
then `ψ` maps `J` into `S` as well: otherwise `S` would have an even number of elements (paired
by `φ`) and an odd number (all but `J` paired by `ψ`). -/
theorem apply_mem_of_involutive_of_mapsTo {α : Type*} [DecidableEq α] {S : Finset α} {J : α}
    (hJ : J ∈ S) {φ ψ : α → α} (hφ : Function.Involutive φ) (hφne : ∀ s, φ s ≠ s)
    (hψ : Function.Involutive ψ) (hψne : ∀ s, ψ s ≠ s) (hφS : ∀ s ∈ S, φ s ∈ S)
    (hψS : ∀ s ∈ S, s ≠ J → ψ s ∈ S) : ψ J ∈ S := by
  by_contra hψJ
  have h₁ : ∑ s ∈ S, (1 : ZMod 2) = 0 :=
    sum_involution (fun s _ => φ s) (fun _ _ => rfl) (fun s _ _ => hφne s)
      (fun s hs => hφS s hs) (fun s _ => hφ s)
  have h₂ : ∑ s ∈ S.erase J, (1 : ZMod 2) = 0 := by
    refine sum_involution (fun s _ => ψ s) (fun _ _ => rfl) (fun s _ _ => hψne s)
      (fun s hs => ?_) (fun s _ => hψ s)
    obtain ⟨hne, hs⟩ := mem_erase.1 hs
    refine mem_erase.2 ⟨fun h => hψJ ?_, hψS s hs hne⟩
    rw [← h, hψ s]
    exact hs
  have hsum := add_sum_erase S (fun _ => (1 : ZMod 2)) hJ
  rw [h₁, h₂] at hsum
  exact absurd hsum (by decide)

end Finset

/-! ### Positions read modulo the perimeter -/

namespace Int

/-- Reading a position `p ∈ [0, P)` modulo `P` in an interval inside `[0, 2P)`: only the shifts
by `0` and `P` can land in it. -/
theorem exists_add_mul_mem_Ico_iff {P p x y : ℤ} (hP : 0 < P) (hp : 0 ≤ p) (hpP : p < P)
    (hx : 0 ≤ x) (hy : y ≤ 2 * P) :
    (∃ k : ℤ, p + k * P ∈ Ico x y) ↔ p ∈ Ico x y ∨ p + P ∈ Ico x y := by
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have : k * P ≤ -P := by nlinarith
      exfalso
      linarith
    · left
      simpa using And.intro hk₁ hk₂
    · rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk'
      · right
        simpa using And.intro hk₁ hk₂
      · have : 2 * P ≤ k * P := by nlinarith
        exfalso
        linarith
  · rintro (h | h)
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩

/-- Reading a position modulo `P`: shifting the interval by a multiple of `P` changes nothing. -/
theorem exists_add_mul_mem_Ico_sub_mul_iff {P p x y m : ℤ} :
    (∃ k : ℤ, p + k * P ∈ Ico (x - m * P) (y - m * P)) ↔ ∃ k : ℤ, p + k * P ∈ Ico x y := by
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨k + m, by rw [add_mul]; linarith, by rw [add_mul]; linarith⟩
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨k - m, by rw [sub_mul]; linarith, by rw [sub_mul]; linarith⟩

/-- Reading a position modulo `P` in an interval `[x, y)` inside `[a, P + a)`: after shifting by
the multiple `a / P * P` of `P`, only the position itself and its shift by `P` can land in it. -/
theorem exists_add_mul_mem_Ico_iff_of_le {P p a x y : ℤ} (hP : 0 < P) (hp : 0 ≤ p)
    (hpP : p < P) (hx : a ≤ x) (hy : y ≤ P + a) :
    (∃ k : ℤ, p + k * P ∈ Ico x y) ↔
      p ∈ Ico (x - a / P * P) (y - a / P * P) ∨ p + P ∈ Ico (x - a / P * P) (y - a / P * P) := by
  have h₁ := Int.emod_nonneg a hP.ne'
  have h₂ := Int.emod_lt_of_pos a hP
  have h₃ := Int.emod_def a P
  rw [mul_comm] at h₃
  rw [← Int.exists_add_mul_mem_Ico_sub_mul_iff (m := a / P)]
  exact Int.exists_add_mul_mem_Ico_iff hP hp hpP (by linarith) (by linarith)

end Int

namespace Sym2

/-- An unordered pair of distinct points meets a point `h` once if `h` is one of them: the
indicators of `x = h` and `y = h` add up to the indicator of `h ∈ s(x, y)`. -/
theorem ite_add_ite_eq_ite_mem {α M : Type*} [DecidableEq α] [AddZeroClass M] {x y : α}
    (hxy : x ≠ y) (h : α) (m : M) :
    (if x = h then m else 0) + (if y = h then m else 0) = if h ∈ s(x, y) then m else 0 := by
  by_cases hx : x = h
  · subst hx
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hxy), ite_eq_left (Sym2.mem_mk_left _ _),
      add_zero]
  · by_cases hy : y = h
    · subst hy
      rw [ite_eq_right hx, ite_eq_left rfl, ite_eq_left (Sym2.mem_mk_right _ _), zero_add]
    · rw [ite_eq_right hx, ite_eq_right hy, ite_eq_right, add_zero]
      rw [Sym2.mem_iff]
      rintro (h' | h')
      exacts [hx h'.symm, hy h'.symm]

end Sym2

/-! ### Faces and boxes -/

namespace PercLib.Models.Planar

section Faces

variable {d : ℕ}

/-- A corner `x` of a face `f` of the box `Icc lo hi`, the face `f` read as a dual vertex in the
box `Icc lo (hi - 1)` of the faces of the box, lies in the box. -/
theorem mem_Icc_of_mem_Icc_sub_one {lo hi f x : LatticeSite d} (hf : f ∈ Icc lo (hi - 1))
    (hx : x ∈ Icc f (f + 1)) : x ∈ Icc lo hi :=
  ⟨hf.1.trans hx.1, fun i => by
    have h₁ : x i ≤ f i + 1 := hx.2 i
    have h₂ : f i ≤ hi i - 1 := hf.2 i
    change x i ≤ hi i
    omega⟩

/-- A face with a corner in the box `Icc lo hi` lies in the box `Icc (lo - 1) hi` of the faces
touching it. -/
theorem mem_Icc_sub_one_of_mem_Icc {lo hi f x : LatticeSite d} (hx : x ∈ Icc lo hi)
    (hxf : x ∈ Icc f (f + 1)) : f ∈ Icc (lo - 1) hi :=
  ⟨fun i => by
    have h₁ : lo i ≤ x i := hx.1 i
    have h₂ : x i ≤ f i + 1 := hxf.2 i
    change lo i - 1 ≤ f i
    omega, fun i => (hxf.1 i).trans (hx.2 i)⟩

/-- A point of the box `Icc lo hi` that is a corner of a face outside `Icc lo (hi - 1)` (a face
not inside the box) lies on the boundary of the box. -/
theorem mem_boxBoundary_of_notMem_Icc {lo hi f x : LatticeSite d} (hx : x ∈ Icc lo hi)
    (hf : f ∉ Icc lo (hi - 1)) (hxf : x ∈ Icc f (f + 1)) : x ∈ boxBoundary lo hi := by
  refine ⟨hx, ?_⟩
  by_contra h
  push Not at h
  refine hf ⟨fun i => ?_, fun i => ?_⟩
  · have h₁ := h i
    have h₂ : lo i ≤ x i := hx.1 i
    have h₃ : x i ≤ f i + 1 := hxf.2 i
    change lo i ≤ f i
    omega
  · have h₁ := h i
    have h₂ : x i ≤ hi i := hx.2 i
    have h₃ : f i ≤ x i := hxf.1 i
    change f i ≤ hi i - 1
    omega

end Faces

/-! ### Corners -/

/-- The vertex of a corner is a corner of its face. -/
theorem cornerVertex_mem_Icc_cornerFace (s : LatticeSite 2) :
    cornerVertex s ∈ Icc (cornerFace s) (cornerFace s + 1) := by
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.one_apply, cornerFace_apply, cornerVertex_apply]
  omega

/-- The ends of the horizontal edge of a corner are corners of its face. -/
theorem mem_Icc_cornerFace_of_mem_cornerHEdge {s x : LatticeSite 2} (hx : x ∈ cornerHEdge s) :
    x ∈ Icc (cornerFace s) (cornerFace s + 1) := by
  rw [cornerHEdge, Sym2.mem_iff] at hx
  rw [mem_Icc_two_iff]
  rcases hx with rfl | rfl <;>
    simp only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      cornerFace_apply, cornerVertex_apply] <;> omega

/-- The ends of the vertical edge of a corner are corners of its face. -/
theorem mem_Icc_cornerFace_of_mem_cornerVEdge {s x : LatticeSite 2} (hx : x ∈ cornerVEdge s) :
    x ∈ Icc (cornerFace s) (cornerFace s + 1) := by
  rw [cornerVEdge, Sym2.mem_iff] at hx
  rw [mem_Icc_two_iff]
  rcases hx with rfl | rfl <;>
    simp only [Pi.add_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      cornerFace_apply, cornerVertex_apply] <;> omega

/-- The corner `v + f` of a face `f` at its corner `v` has vertex `v`. -/
theorem cornerVertex_add {v f : LatticeSite 2} (h : v ∈ Icc f (f + 1)) :
    cornerVertex (v + f) = v := by
  rw [mem_Icc_two_iff] at h
  simp only [Pi.add_apply, Pi.one_apply] at h
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    simp only [cornerVertex_apply, Pi.add_apply] <;> omega

/-- The corner `v + f` of a face `f` at its corner `v` has face `f`. -/
theorem cornerFace_add {v f : LatticeSite 2} (h : v ∈ Icc f (f + 1)) :
    cornerFace (v + f) = f := by
  rw [mem_Icc_two_iff] at h
  simp only [Pi.add_apply, Pi.one_apply] at h
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    simp only [cornerFace_apply, Pi.add_apply] <;> omega

/-! ### Faces outside the box and perimeter positions -/

section Perimeter

variable {lo hi : LatticeSite 2}

/-- **Two boundary points of one outer face are neighbours on the boundary.** If two distinct
points of the boundary of a box of positive width and height are corners of one face that is
not inside the box, their perimeter positions differ by one, modulo the perimeter. -/
theorem perimeterPos_eq_add_one_or_of_notMem_Icc (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {v w f : LatticeSite 2} (hv : v ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (hvw : v ≠ w) (hf : f ∉ Icc lo (hi - 1)) (hvf : v ∈ Icc f (f + 1))
    (hwf : w ∈ Icc f (f + 1)) :
    perimeterPos lo hi w = perimeterPos lo hi v + 1 ∨
      perimeterPos lo hi v = perimeterPos lo hi w + 1 ∨
      (perimeterPos lo hi v = 0 ∧
        perimeterPos lo hi w = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1) ∨
      (perimeterPos lo hi w = 0 ∧
        perimeterPos lo hi v = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1) := by
  rw [mem_boxBoundary_two_iff] at hv hw
  rw [mem_Icc_two_iff] at hvf hwf hf
  simp only [Pi.add_apply, Pi.one_apply, Pi.sub_apply] at hvf hwf hf
  have hne : v 0 ≠ w 0 ∨ v 1 ≠ w 1 := by
    by_contra h
    push Not at h
    exact hvw (funext (Fin.forall_fin_two.2 h))
  obtain ⟨⟨hv0, hv0', hv1, hv1'⟩, -⟩ := hv
  obtain ⟨⟨hw0, hw0', hw1, hw1'⟩, -⟩ := hw
  have hf' : f 0 = lo 0 - 1 ∨ f 0 = hi 0 ∨ f 1 = lo 1 - 1 ∨ f 1 = hi 1 := by omega
  unfold perimeterPos
  rcases hf' with h | h | h | h <;> split_ifs <;> omega

/-- **An outer face is determined by two of its boundary corners.** Two faces not inside a box of
positive width and height that share two distinct corners in the box are equal. -/
theorem eq_of_notMem_Icc_sub_one (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {v w f g : LatticeSite 2}
    (hv : v ∈ Icc lo hi) (hw : w ∈ Icc lo hi) (hvw : v ≠ w) (hf : f ∉ Icc lo (hi - 1))
    (hg : g ∉ Icc lo (hi - 1)) (hvfg : v ∈ Icc f (f + 1) ∩ Icc g (g + 1))
    (hwfg : w ∈ Icc f (f + 1) ∩ Icc g (g + 1)) : f = g := by
  obtain ⟨hvf, hvg⟩ := hvfg
  obtain ⟨hwf, hwg⟩ := hwfg
  rw [mem_Icc_two_iff] at hv hw hvf hwf hvg hwg hf hg
  simp only [Pi.add_apply, Pi.one_apply, Pi.sub_apply] at hvf hwf hvg hwg hf hg
  have hne : v 0 ≠ w 0 ∨ v 1 ≠ w 1 := by
    by_contra h
    push Not at h
    exact hvw (funext (Fin.forall_fin_two.2 h))
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> omega

/-- **The outer face at a perimeter position.** For a box of positive width and height and a
position `p` in `[0, P)`, `P` the perimeter, the boundary points `v` at position `p` and `w` at
the next position (modulo `P`) are corners of a face `f` not inside the box, the outer face of
the boundary edge from `v` to `w`. Of the two edges of `f` at `v`, one (that boundary edge) lies
in the box and the other leaves it. -/
theorem exists_notMem_Icc_of_perimeterPos (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {p : ℤ}
    (hp : 0 ≤ p) (hpP : p < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) :
    ∃ v w f : LatticeSite 2, v ∈ boxBoundary lo hi ∧ perimeterPos lo hi v = p ∧
      w ∈ boxBoundary lo hi ∧ (perimeterPos lo hi w = p + 1 ∨
        (p + 1 = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) ∧ perimeterPos lo hi w = 0)) ∧
      f ∉ Icc lo (hi - 1) ∧ v ∈ Icc f (f + 1) ∧ w ∈ Icc f (f + 1) ∧
      ((∀ x ∈ cornerHEdge (v + f), x ∈ Icc lo hi) ↔
        ¬ ∀ x ∈ cornerVEdge (v + f), x ∈ Icc lo hi) := by
  rcases (show p < hi 0 - lo 0 ∨ (hi 0 - lo 0 ≤ p ∧ p < (hi 0 - lo 0) + (hi 1 - lo 1)) ∨
      ((hi 0 - lo 0) + (hi 1 - lo 1) ≤ p ∧ p < 2 * (hi 0 - lo 0) + (hi 1 - lo 1)) ∨
      2 * (hi 0 - lo 0) + (hi 1 - lo 1) ≤ p by omega) with hp' | hp' | hp' | hp'
  -- the bottom, right, top and left sides
  on_goal 1 => refine ⟨![lo 0 + p, lo 1], ![lo 0 + p + 1, lo 1], ![lo 0 + p, lo 1 - 1], ?_⟩
  on_goal 2 =>
    refine ⟨![hi 0, lo 1 + (p - (hi 0 - lo 0))], ![hi 0, lo 1 + (p - (hi 0 - lo 0)) + 1],
      ![hi 0, lo 1 + (p - (hi 0 - lo 0))], ?_⟩
  on_goal 3 =>
    refine ⟨![hi 0 - (p - (hi 0 - lo 0) - (hi 1 - lo 1)), hi 1],
      ![hi 0 - (p - (hi 0 - lo 0) - (hi 1 - lo 1)) - 1, hi 1],
      ![hi 0 - (p - (hi 0 - lo 0) - (hi 1 - lo 1)) - 1, hi 1], ?_⟩
  on_goal 4 =>
    refine ⟨![lo 0, hi 1 - (p - 2 * (hi 0 - lo 0) - (hi 1 - lo 1))],
      ![lo 0, hi 1 - (p - 2 * (hi 0 - lo 0) - (hi 1 - lo 1)) - 1],
      ![lo 0 - 1, hi 1 - (p - 2 * (hi 0 - lo 0) - (hi 1 - lo 1)) - 1], ?_⟩
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_boxBoundary_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, le_refl, true_or, or_true, true_and,
        and_true]
      all_goals omega
    · unfold perimeterPos
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      split_ifs <;> omega
    · rw [mem_boxBoundary_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, le_refl, true_or, or_true, true_and,
        and_true]
      all_goals omega
    · unfold perimeterPos
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      split_ifs <;> omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.one_apply]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply]
      omega
    · rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.one_apply]
      omega
    · simp only [cornerHEdge_eq, cornerVEdge_eq, Pi.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_Icc_two_iff]
      omega

end Perimeter

/-! ### One step of a partner map

Standing notation for the parity argument. `A, B, C, D` are sets of points (in the application,
the four arcs of the boundary of the box `Icc lo hi`). The **wired configuration** opens, besides
the open edges of `ω` inside the box, every edge all of whose points in the box lie in `A`, and
every edge all of whose points in the box lie in `B`: the edges inside `A` or inside `B` and the
edges leaving the box from `A` or from `B`. The edges leaving the box from `C` or `D` are closed.
The **dual arc** of `C` is the set of faces not inside the box with a corner in `C`. Dual paths
use the dual edges crossing closed edges of the box (both ends in the box), inside the box
`Icc (lo - 1) hi` of the faces touching it. -/

section Steps

variable {lo hi : LatticeSite 2} {A B C D : Set (LatticeSite 2)} {ω : Config (LatticeSite 2)}

/-- **A step of the vertex.** If `v` is joined to `A` inside the box and the edge from `v` to a
point `v'` of the box is open in the wired configuration, then `v'` is joined to `A` inside the
box, unless `A` and `B` are joined. -/
theorem exists_inter_mem_localConn_of_wired
    (hω : ¬ ∃ u ∈ A, ∃ w ∈ B, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u w)
    {v v' : LatticeSite 2} (hv : ∃ u ∈ A, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v)
    (hv' : v' ∈ Icc lo hi) (hvv' : s(v, v') ∈ (zdGraph 2).edgeSet)
    (he : (s(v, v') ∈ ω ∧ ∀ x ∈ s(v, v'), x ∈ Icc lo hi) ∨
      (∀ x ∈ s(v, v'), x ∈ A ∨ x ∉ Icc lo hi) ∨ ∀ x ∈ s(v, v'), x ∈ B ∨ x ∉ Icc lo hi) :
    ∃ u ∈ A, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v' := by
  obtain ⟨u, hu, huv⟩ := hv
  rcases he with ⟨he, -⟩ | he | he
  · exact ⟨u, hu, mem_localConn_of_mem_localConn_of_mem huv hv' ⟨he, hvv'⟩⟩
  · rcases he v' (Sym2.mem_mk_right _ _) with h | h
    · exact ⟨v', h, by rw [localConn_self hv']; exact mem_univ _⟩
    · exact absurd hv' h
  · rcases he v (Sym2.mem_mk_left _ _) with h | h
    · exact absurd ⟨u, hu, v, h, huv⟩ hω
    · exact absurd huv.2.1 h

/-- **A step of the face.** Let `e` be an edge at a point `v` of the box, closed in the wired
configuration, and `f, f'` the two faces on either side of it. If `f` is joined to the dual arc
of `C` by a dual path and `f'` lies in the dual box, then `f'` is joined to the dual arc of `C`,
unless the dual arcs of `C` and `D` are joined. -/
theorem exists_dualConfig_inter_mem_localConn_of_not_wired
    (hpart : ∀ x ∈ boxBoundary lo hi, x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D)
    (hCD : ¬ ∃ f ∈ {f | f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc f (f + 1)},
      ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g)
    {e : Sym2 (LatticeSite 2)} {v f f' : LatticeSite 2} (he : e ∈ (zdGraph 2).edgeSet)
    (hff' : s(f, f') = dualEdge e) (hve : v ∈ e) (hvR : v ∈ Icc lo hi)
    (hef : ∀ x ∈ e, x ∈ Icc f (f + 1) ∧ x ∈ Icc f' (f' + 1))
    (hclosed : ¬ ((e ∈ ω ∧ ∀ x ∈ e, x ∈ Icc lo hi) ∨ (∀ x ∈ e, x ∈ A ∨ x ∉ Icc lo hi) ∨
      ∀ x ∈ e, x ∈ B ∨ x ∉ Icc lo hi))
    (hf : ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) g f)
    (hf'T : f' ∈ Icc (lo - 1) hi) :
    ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) g f' := by
  by_cases hin : ∀ x ∈ e, x ∈ Icc lo hi
  · -- an edge of the box, closed in `ω`: its dual edge is a step of a dual path
    have hω : e ∉ ω := fun h => hclosed (Or.inl ⟨h, hin⟩)
    obtain ⟨g, hg, hgf⟩ := hf
    refine ⟨g, hg, mem_localConn_of_mem_localConn_of_mem hgf hf'T ?_⟩
    rw [hff']
    exact ⟨(dualEdge_mem_dualConfig_iff he).2 hω, e, ⟨he, hin⟩, rfl⟩
  · -- an edge leaving the box at `v`, which lies in `C` or `D`
    push Not at hin
    obtain ⟨x, hxe, hxR⟩ := hin
    have hvx : v ≠ x := fun h => hxR (h ▸ hvR)
    have hex : e = s(v, x) := (Sym2.mem_and_mem_iff hvx).1 ⟨hve, hxe⟩
    have hfin : f ∉ Icc lo (hi - 1) := fun h =>
      hxR (mem_Icc_of_mem_Icc_sub_one h (hef x hxe).1)
    have hf'in : f' ∉ Icc lo (hi - 1) := fun h =>
      hxR (mem_Icc_of_mem_Icc_sub_one h (hef x hxe).2)
    have hvA : v ∉ A := fun h => hclosed (Or.inr (Or.inl fun y hy => by
      rw [hex, Sym2.mem_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact Or.inl h
      · rw [hy]
        exact Or.inr hxR))
    have hvB : v ∉ B := fun h => hclosed (Or.inr (Or.inr fun y hy => by
      rw [hex, Sym2.mem_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact Or.inl h
      · rw [hy]
        exact Or.inr hxR))
    rcases hpart v (mem_boxBoundary_of_notMem_Icc hvR hf'in (hef v hve).2) with h | h | h | h
    · exact absurd h hvA
    · exact absurd h hvB
    · exact ⟨f', ⟨hf'in, v, h, (hef v hve).2⟩, by rw [localConn_self hf'T]; exact mem_univ _⟩
    · obtain ⟨g, hg, hgf⟩ := hf
      exact absurd ⟨g, hg, f, ⟨hfin, v, h, (hef v hve).1⟩, hgf⟩ hCD

/-- **A step of the face stays among the faces used.** If an edge `e` at a point `v` of the box
is closed in the wired configuration, every face `f` with corners at the ends of `e` lies inside
the box or in the dual arc of `C` or of `D`, provided no face outside the box has corners in both
`A` and `B`. -/
theorem mem_Icc_or_mem_of_not_wired
    (hpart : ∀ x ∈ boxBoundary lo hi, x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, ∀ f, f ∉ Icc lo (hi - 1) → x ∈ Icc f (f + 1) →
      y ∈ Icc f (f + 1) → False)
    {e : Sym2 (LatticeSite 2)} {v f : LatticeSite 2} (hve : v ∈ e) (hvR : v ∈ Icc lo hi)
    (hef : ∀ x ∈ e, x ∈ Icc f (f + 1))
    (hclosed : ¬ ((e ∈ ω ∧ ∀ x ∈ e, x ∈ Icc lo hi) ∨ (∀ x ∈ e, x ∈ A ∨ x ∉ Icc lo hi) ∨
      ∀ x ∈ e, x ∈ B ∨ x ∉ Icc lo hi)) :
    f ∈ Icc lo (hi - 1) ∨ f ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)} ∨
      f ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)} := by
  by_cases hf : f ∈ Icc lo (hi - 1)
  · exact Or.inl hf
  right
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hve
  have hvf := hef v (Sym2.mem_mk_left _ _)
  have hxf := hef x (Sym2.mem_mk_right _ _)
  have hvbd := mem_boxBoundary_of_notMem_Icc hvR hf hvf
  have hCD : ∀ y, y ∈ Icc f (f + 1) → y ∈ C ∨ y ∈ D →
      f ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)} ∨
        f ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)} := by
    rintro y hy (h | h)
    exacts [Or.inl ⟨hf, y, h, hy⟩, Or.inr ⟨hf, y, h, hy⟩]
  -- the wired configuration opens an edge whose points in the box all lie in `A`, or all in `B`
  have hwire : ∀ P : Set (LatticeSite 2), (v ∈ P ∨ v ∉ Icc lo hi) → (x ∈ P ∨ x ∉ Icc lo hi) →
      ∀ y ∈ s(v, x), y ∈ P ∨ y ∉ Icc lo hi := by
    intro P hv hx y hy
    rcases Sym2.mem_iff.1 hy with hy | hy
    · rw [hy]
      exact hv
    · rw [hy]
      exact hx
  by_cases hxR : x ∈ Icc lo hi
  · have hxbd := mem_boxBoundary_of_notMem_Icc hxR hf hxf
    have hnA : ¬ (v ∈ A ∧ x ∈ A) := fun h =>
      hclosed (Or.inr (Or.inl (hwire A (Or.inl h.1) (Or.inl h.2))))
    have hnB : ¬ (v ∈ B ∧ x ∈ B) := fun h =>
      hclosed (Or.inr (Or.inr (hwire B (Or.inl h.1) (Or.inl h.2))))
    rcases hpart v hvbd with hv | hv | hv | hv
    · rcases hpart x hxbd with hx | hx | hx | hx
      · exact absurd ⟨hv, hx⟩ hnA
      · exact (hAB v hv x hx f hf hvf hxf).elim
      · exact hCD x hxf (Or.inl hx)
      · exact hCD x hxf (Or.inr hx)
    · rcases hpart x hxbd with hx | hx | hx | hx
      · exact (hAB x hx v hv f hf hxf hvf).elim
      · exact absurd ⟨hv, hx⟩ hnB
      · exact hCD x hxf (Or.inl hx)
      · exact hCD x hxf (Or.inr hx)
    · exact hCD v hvf (Or.inl hv)
    · exact hCD v hvf (Or.inr hv)
  · have hvA : v ∉ A := fun h =>
      hclosed (Or.inr (Or.inl (hwire A (Or.inl h) (Or.inr hxR))))
    have hvB : v ∉ B := fun h =>
      hclosed (Or.inr (Or.inr (hwire B (Or.inl h) (Or.inr hxR))))
    rcases hpart v hvbd with hv | hv | hv | hv
    · exact absurd hv hvA
    · exact absurd hv hvB
    · exact hCD v hvf (Or.inl hv)
    · exact hCD v hvf (Or.inr hv)

/-- **A step of the vertex out of the box.** If `v` is joined to `A`, a face `f` at `v` is joined
to the dual arc of `C`, and the edge of `f` from `v` to a point `v'` outside the box is open in
the wired configuration, then `v` lies in `A` and `f` in the dual arc of `C`, so `(v, f)` is the
corner at the junction of `A` and `C` (hypothesis `hJ`); unless `A` and `B`, or the dual arcs of
`C` and `D`, are joined. -/
theorem eq_and_eq_of_wired_of_notMem
    (hω : ¬ ∃ u ∈ A, ∃ w ∈ B, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u w)
    (hCD : ¬ ∃ f ∈ {f | f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc f (f + 1)},
      ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g)
    {v₀ f₀ : LatticeSite 2}
    (hJ : ∀ x ∈ A, ∀ w ∈ C, ∀ g, g ∉ Icc lo (hi - 1) → x ∈ Icc g (g + 1) →
      w ∈ Icc g (g + 1) → x = v₀ ∧ g = f₀)
    {v v' f : LatticeSite 2} (hv : ∃ u ∈ A, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v)
    (hf : ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) g f)
    (hfK : f ∈ Icc lo (hi - 1) ∨ f ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)} ∨
      f ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)})
    (hv' : v' ∉ Icc lo hi) (hvf : v ∈ Icc f (f + 1) ∧ v' ∈ Icc f (f + 1))
    (he : (s(v, v') ∈ ω ∧ ∀ x ∈ s(v, v'), x ∈ Icc lo hi) ∨
      (∀ x ∈ s(v, v'), x ∈ A ∨ x ∉ Icc lo hi) ∨ ∀ x ∈ s(v, v'), x ∈ B ∨ x ∉ Icc lo hi) :
    v = v₀ ∧ f = f₀ := by
  obtain ⟨u, hu, huv⟩ := hv
  have hvR : v ∈ Icc lo hi := huv.2.1
  have hfin : f ∉ Icc lo (hi - 1) := fun h => hv' (mem_Icc_of_mem_Icc_sub_one h hvf.2)
  have hvA : v ∈ A := by
    rcases he with ⟨-, h⟩ | h | h
    · exact absurd (h v' (Sym2.mem_mk_right _ _)) hv'
    · exact (h v (Sym2.mem_mk_left _ _)).resolve_right (not_not.2 hvR)
    · rcases h v (Sym2.mem_mk_left _ _) with h | h
      · exact absurd ⟨u, hu, v, h, huv⟩ hω
      · exact absurd hvR h
  rcases hfK with h | ⟨-, w, hw, hwf⟩ | hD
  · exact absurd h hfin
  · exact hJ v hvA w hw f hfin hvf.1 hwf
  · obtain ⟨g, hg, hgf⟩ := hf
    exact absurd ⟨g, hg, f, hD, hgf⟩ hCD

end Steps

/-! ### The parity argument -/

/-- **Quad duality, at least one, in abstract form.** Let `A, B, C, D` be sets of points such
that every point of the boundary of the box `Icc lo hi` lies in one of them, `A`, `C` and `D`
lie in the box, and no face outside the box has corners in both `A` and `B`. Suppose that the
faces outside the box with corners in both `A` and `C` are all the single face `f₀`, at the
single corner `v₀ ∈ A`, with `f₀` a face of the dual arc of `C`, and that exactly one of the two
edges of `f₀` at `v₀` leaves the box. If no open path inside the box joins `A` to `B`, a dual path
joins the dual arcs of `C` and `D`.

The hypotheses are what the four arcs of the boundary provide; there are nine because the proof
uses each property of the arcs separately. The proof is the parity argument of
`mem_crossing_one_dualConfig_of_notMem_crossing_zero`. The corners whose vertex lies in the box
and whose face is inside the box or in the dual arc of `C` or of `D` form a finite set `K`. With
the boundary wired, both partner maps keep the set `S` of corners of `K` whose vertex is joined
to `A` and whose face is joined to the dual arc of `C`, except at the corner `v₀ + f₀`, whose
partner across the edge leaving the box leaves `K`. Counting `S` in pairs of horizontal partners
and in pairs of vertical partners gives a contradiction modulo two. -/
theorem exists_dualConfig_inter_mem_localConn_of_arcs {lo hi : LatticeSite 2}
    {A B C D : Set (LatticeSite 2)}
    (hpart : ∀ x ∈ boxBoundary lo hi, x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D)
    (hsub : A ∪ C ∪ D ⊆ Icc lo hi)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, ∀ f, f ∉ Icc lo (hi - 1) → x ∈ Icc f (f + 1) →
      y ∈ Icc f (f + 1) → False)
    {v₀ f₀ : LatticeSite 2}
    (hJ : ∀ x ∈ A, ∀ w ∈ C, ∀ g, g ∉ Icc lo (hi - 1) → x ∈ Icc g (g + 1) →
      w ∈ Icc g (g + 1) → x = v₀ ∧ g = f₀)
    (hv₀ : v₀ ∈ A) (hf₀ : f₀ ∈ {f | f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc f (f + 1)})
    (hv₀f₀ : v₀ ∈ Icc f₀ (f₀ + 1))
    (hone : (∀ x ∈ cornerHEdge (v₀ + f₀), x ∈ Icc lo hi) ↔
      ¬ ∀ x ∈ cornerVEdge (v₀ + f₀), x ∈ Icc lo hi)
    {ω : Config (LatticeSite 2)}
    (hω : ¬ ∃ u ∈ A, ∃ w ∈ B, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u w) :
    ∃ f ∈ {f | f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc f (f + 1)},
      ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g := by
  classical
  by_contra hCD
  have hv₀R : v₀ ∈ Icc lo hi := hsub (Or.inl (Or.inl hv₀))
  -- the faces of the corners used lie in the dual box
  have hKT : ∀ g, g ∈ Icc lo (hi - 1) ∨
      g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)} ∨
      g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)} → g ∈ Icc (lo - 1) hi := by
    rintro g (h | ⟨-, x, hx, hxg⟩ | ⟨-, x, hx, hxg⟩)
    · refine ⟨fun i => ?_, fun i => ?_⟩
      · have h₁ : lo i ≤ g i := h.1 i
        change lo i - 1 ≤ g i
        omega
      · have h₁ : g i ≤ hi i - 1 := h.2 i
        change g i ≤ hi i
        omega
    · exact mem_Icc_sub_one_of_mem_Icc (hsub (Or.inl (Or.inr hx))) hxg
    · exact mem_Icc_sub_one_of_mem_Icc (hsub (Or.inr hx)) hxg
  -- the wired configuration
  set ω' : Config (LatticeSite 2) := {e | (e ∈ ω ∧ ∀ x ∈ e, x ∈ Icc lo hi) ∨
    (∀ x ∈ e, x ∈ A ∨ x ∉ Icc lo hi) ∨ ∀ x ∈ e, x ∈ B ∨ x ∉ Icc lo hi} with hω'
  -- the corners with vertex in the box and face inside the box or in a dual arc
  set K : Finset (LatticeSite 2) :=
    (Finset.Icc ![2 * lo 0 - 1, 2 * lo 1 - 1] ![2 * hi 0, 2 * hi 1]).filter (fun s =>
      cornerVertex s ∈ Icc lo hi ∧ (cornerFace s ∈ Icc lo (hi - 1) ∨
        cornerFace s ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)} ∨
        cornerFace s ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)})) with hK
  have hmemK : ∀ s, s ∈ K ↔ cornerVertex s ∈ Icc lo hi ∧ (cornerFace s ∈ Icc lo (hi - 1) ∨
      cornerFace s ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)} ∨
      cornerFace s ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ D, x ∈ Icc g (g + 1)}) := by
    intro s
    rw [hK, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have hv := h.1
    have hf := hKT _ h.2
    rw [mem_Icc_two_iff] at hv hf
    simp only [cornerVertex_apply, cornerFace_apply, Pi.sub_apply, Pi.one_apply] at hv hf
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  -- the corners whose vertex is joined to `A` and whose face is joined to the dual arc of `C`
  set S : Finset (LatticeSite 2) := K.filter (fun s =>
    (∃ u ∈ A, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u (cornerVertex s)) ∧
    ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)},
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) g (cornerFace s)) with hS
  have hmemS : ∀ s, s ∈ S ↔ s ∈ K ∧
      (∃ u ∈ A, ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u (cornerVertex s)) ∧
      ∃ g ∈ {g | g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ C, x ∈ Icc g (g + 1)},
        dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
          localConn (Icc (lo - 1) hi) g (cornerFace s) := fun s => by
    rw [hS, Finset.mem_filter]
  -- one horizontal step stays in `S`, except across an edge leaving the box at `v₀ + f₀`
  have hstepH : ∀ s ∈ S, hPartner ω' s ∈ S ∨
      (s = v₀ + f₀ ∧ ¬ ∀ x ∈ cornerHEdge s, x ∈ Icc lo hi) := by
    intro s hs
    obtain ⟨hsK, hsA, hsB⟩ := (hmemS s).1 hs
    obtain ⟨hvR, hfK⟩ := (hmemK s).1 hsK
    by_cases h : cornerHEdge s ∈ ω'
    · have hf' := cornerFace_hPartner_of_mem h
      have hvv' := sym2_cornerVertex_hPartner_of_mem h
      have he := h
      rw [← hvv'] at he
      have hL : s(cornerVertex s, cornerVertex (hPartner ω' s)) ∈ (zdGraph 2).edgeSet := by
        rw [hvv']
        exact cornerHEdge_mem_edgeSet s
      by_cases hv'R : cornerVertex (hPartner ω' s) ∈ Icc lo hi
      · left
        rw [hmemS, hmemK, hf']
        exact ⟨⟨hv'R, hfK⟩, exists_inter_mem_localConn_of_wired hω hsA hv'R hL he, hsB⟩
      · right
        have hv'f : cornerVertex (hPartner ω' s) ∈ Icc (cornerFace s) (cornerFace s + 1) := by
          rw [← hf']
          exact cornerVertex_mem_Icc_cornerFace _
        obtain ⟨h₁, h₂⟩ := eq_and_eq_of_wired_of_notMem hω hCD hJ hsA hsB hfK hv'R
          ⟨cornerVertex_mem_Icc_cornerFace s, hv'f⟩ he
        refine ⟨by rw [← cornerVertex_add_cornerFace s, h₁, h₂], fun hall => hv'R (hall _ ?_)⟩
        rw [← hvv']
        exact Sym2.mem_mk_right _ _
    · left
      have hv' := cornerVertex_hPartner_of_notMem h
      have hff' := sym2_cornerFace_hPartner_of_notMem h
      have hef : ∀ x ∈ cornerHEdge s, x ∈ Icc (cornerFace s) (cornerFace s + 1) ∧
          x ∈ Icc (cornerFace (hPartner ω' s)) (cornerFace (hPartner ω' s) + 1) := fun x hx =>
        ⟨mem_Icc_cornerFace_of_mem_cornerHEdge hx,
          mem_Icc_cornerFace_of_mem_cornerHEdge (by rw [cornerHEdge_hPartner]; exact hx)⟩
      have hK' := mem_Icc_or_mem_of_not_wired hpart hAB (cornerVertex_mem_cornerHEdge s) hvR
        (fun x hx => (hef x hx).2) h
      rw [hmemS, hmemK, hv']
      exact ⟨⟨hvR, hK'⟩, hsA, exists_dualConfig_inter_mem_localConn_of_not_wired hpart hCD
        (cornerHEdge_mem_edgeSet s) hff' (cornerVertex_mem_cornerHEdge s) hvR hef h hsB
        (hKT _ hK')⟩
  -- one vertical step stays in `S`, except across an edge leaving the box at `v₀ + f₀`
  have hstepV : ∀ s ∈ S, vPartner ω' s ∈ S ∨
      (s = v₀ + f₀ ∧ ¬ ∀ x ∈ cornerVEdge s, x ∈ Icc lo hi) := by
    intro s hs
    obtain ⟨hsK, hsA, hsB⟩ := (hmemS s).1 hs
    obtain ⟨hvR, hfK⟩ := (hmemK s).1 hsK
    by_cases h : cornerVEdge s ∈ ω'
    · have hf' := cornerFace_vPartner_of_mem h
      have hvv' := sym2_cornerVertex_vPartner_of_mem h
      have he := h
      rw [← hvv'] at he
      have hL : s(cornerVertex s, cornerVertex (vPartner ω' s)) ∈ (zdGraph 2).edgeSet := by
        rw [hvv']
        exact cornerVEdge_mem_edgeSet s
      by_cases hv'R : cornerVertex (vPartner ω' s) ∈ Icc lo hi
      · left
        rw [hmemS, hmemK, hf']
        exact ⟨⟨hv'R, hfK⟩, exists_inter_mem_localConn_of_wired hω hsA hv'R hL he, hsB⟩
      · right
        have hv'f : cornerVertex (vPartner ω' s) ∈ Icc (cornerFace s) (cornerFace s + 1) := by
          rw [← hf']
          exact cornerVertex_mem_Icc_cornerFace _
        obtain ⟨h₁, h₂⟩ := eq_and_eq_of_wired_of_notMem hω hCD hJ hsA hsB hfK hv'R
          ⟨cornerVertex_mem_Icc_cornerFace s, hv'f⟩ he
        refine ⟨by rw [← cornerVertex_add_cornerFace s, h₁, h₂], fun hall => hv'R (hall _ ?_)⟩
        rw [← hvv']
        exact Sym2.mem_mk_right _ _
    · left
      have hv' := cornerVertex_vPartner_of_notMem h
      have hff' := sym2_cornerFace_vPartner_of_notMem h
      have hef : ∀ x ∈ cornerVEdge s, x ∈ Icc (cornerFace s) (cornerFace s + 1) ∧
          x ∈ Icc (cornerFace (vPartner ω' s)) (cornerFace (vPartner ω' s) + 1) := fun x hx =>
        ⟨mem_Icc_cornerFace_of_mem_cornerVEdge hx,
          mem_Icc_cornerFace_of_mem_cornerVEdge (by rw [cornerVEdge_vPartner]; exact hx)⟩
      have hK' := mem_Icc_or_mem_of_not_wired hpart hAB (cornerVertex_mem_cornerVEdge s) hvR
        (fun x hx => (hef x hx).2) h
      rw [hmemS, hmemK, hv']
      exact ⟨⟨hvR, hK'⟩, hsA, exists_dualConfig_inter_mem_localConn_of_not_wired hpart hCD
        (cornerVEdge_mem_edgeSet s) hff' (cornerVertex_mem_cornerVEdge s) hvR hef h hsB
        (hKT _ hK')⟩
  -- the extreme corner `v₀ + f₀` lies in `S`
  have hJv : cornerVertex (v₀ + f₀) = v₀ := cornerVertex_add hv₀f₀
  have hJf : cornerFace (v₀ + f₀) = f₀ := cornerFace_add hv₀f₀
  have hJS : v₀ + f₀ ∈ S := by
    rw [hmemS, hmemK, hJv, hJf]
    exact ⟨⟨hv₀R, Or.inr (Or.inl hf₀)⟩, ⟨v₀, hv₀, by rw [localConn_self hv₀R]; exact mem_univ _⟩,
      ⟨f₀, hf₀, by rw [localConn_self (hKT _ (Or.inr (Or.inl hf₀)))]; exact mem_univ _⟩⟩
  -- an edge at `v₀` leaving the box is open in `ω'`, and leads out of the box
  have hJout : ∀ e, v₀ ∈ e → (¬ ∀ x ∈ e, x ∈ Icc lo hi) →
      e ∈ ω' ∧ ∀ y, s(v₀, y) = e → y ∉ Icc lo hi := by
    intro e hve hout
    push Not at hout
    obtain ⟨x, hxe, hxR⟩ := hout
    have hne : v₀ ≠ x := fun h => hxR (h ▸ hv₀R)
    have hex : e = s(v₀, x) := (Sym2.mem_and_mem_iff hne).1 ⟨hve, hxe⟩
    refine ⟨Or.inr (Or.inl fun y hy => ?_), fun y hy => ?_⟩
    · rw [hex, Sym2.mem_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact Or.inl hv₀
      · rw [hy]
        exact Or.inr hxR
    · rw [hex, Sym2.congr_right] at hy
      rw [hy]
      exact hxR
  have hJH : (¬ ∀ x ∈ cornerHEdge (v₀ + f₀), x ∈ Icc lo hi) → hPartner ω' (v₀ + f₀) ∉ S := by
    intro hout hmem
    have hve := cornerVertex_mem_cornerHEdge (v₀ + f₀)
    rw [hJv] at hve
    obtain ⟨hopen, hy⟩ := hJout _ hve hout
    have hvv' := sym2_cornerVertex_hPartner_of_mem hopen
    rw [hJv] at hvv'
    exact hy _ hvv' ((hmemK _).1 ((hmemS _).1 hmem).1).1
  have hJV : (¬ ∀ x ∈ cornerVEdge (v₀ + f₀), x ∈ Icc lo hi) → vPartner ω' (v₀ + f₀) ∉ S := by
    intro hout hmem
    have hve := cornerVertex_mem_cornerVEdge (v₀ + f₀)
    rw [hJv] at hve
    obtain ⟨hopen, hy⟩ := hJout _ hve hout
    have hvv' := sym2_cornerVertex_vPartner_of_mem hopen
    rw [hJv] at hvv'
    exact hy _ hvv' ((hmemK _).1 ((hmemS _).1 hmem).1).1
  -- counting: one partner map pairs off `S`, the other pairs off `S` without `v₀ + f₀`
  by_cases hHin : ∀ x ∈ cornerHEdge (v₀ + f₀), x ∈ Icc lo hi
  · refine hJV (hone.1 hHin) (Finset.apply_mem_of_involutive_of_mapsTo hJS
      (hPartner_involutive ω') (hPartner_ne ω') (vPartner_involutive ω') (vPartner_ne ω')
      (fun s hs => ?_) (fun s hs hne => ?_))
    · rcases hstepH s hs with h | ⟨h, hout⟩
      · exact h
      · rw [h] at hout
        exact absurd hHin hout
    · rcases hstepV s hs with h | ⟨h, -⟩
      · exact h
      · exact absurd h hne
  · have hVin : ∀ x ∈ cornerVEdge (v₀ + f₀), x ∈ Icc lo hi := by
      by_contra h
      exact hHin (hone.2 h)
    refine hJH hHin (Finset.apply_mem_of_involutive_of_mapsTo hJS
      (vPartner_involutive ω') (vPartner_ne ω') (hPartner_involutive ω') (hPartner_ne ω')
      (fun s hs => ?_) (fun s hs hne => ?_))
    · rcases hstepV s hs with h | ⟨h, hout⟩
      · exact h
      · rw [h] at hout
        exact absurd hVin hout
    · rcases hstepH s hs with h | ⟨h, -⟩
      · exact h
      · exact absurd h hne

/-! ### Quad duality, at least one -/

/-- **Quad duality, at least one.** Let `R = Icc lo hi` be a box of `ℤ²` of positive width and
height, with perimeter `P = 2 (hi₀ - lo₀) + 2 (hi₁ - lo₁)`, and let `a < c < b < d < P + a`.
Reading perimeter positions modulo `P`, the boundary of `R` splits into the arcs `A = [a, c)`,
`C = [c, b)`, `B = [b, d)` and `D = [d, P + a)`. If no open path inside `R` joins a point of `A`
to a point of `B`, then a dual-open path in the dual box `Icc (lo - 1) hi` joins the dual arc of
`C` to the dual arc of `D`. The dual arc of an arc is the set of faces not inside `R` (not in
`Icc lo (hi - 1)`) with a corner in the arc; the dual path crosses only edges of `R`, closed in
`ω`, so it is open in `dualConfig ω ∩ dualEdge '' {edges of R}`. -/
theorem exists_dualConfig_inter_mem_localConn_of_not_exists {lo hi : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {a c b d : ℤ}
    (hacbd : a < c ∧ c < b ∧ b < d ∧ d < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)
    {ω : Config (LatticeSite 2)}
    (hω : ¬ ∃ u v, u ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi u + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico a c) ∧
      v ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi v + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico b d) ∧
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v) :
    ∃ f g, (f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc f (f + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico c b) ∧
      (g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc g (g + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈
          Ico d (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)) ∧
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g := by
  classical
  obtain ⟨hac, hcb, hbd, hda⟩ := hacbd
  -- the perimeter
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) := ⟨_, rfl⟩
  rw [← hP] at hω hda ⊢
  have hP0 : 0 < P := by omega
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have hpos : ∀ x ∈ boxBoundary lo hi, 0 ≤ perimeterPos lo hi x ∧ perimeterPos lo hi x < P :=
    fun x hx => ⟨perimeterPos_nonneg hx.1, by rw [hP]; exact perimeterPos_lt hne hx.1⟩
  -- shifting the arcs by a multiple of `P` so that `a` lies in `[0, P)`
  obtain ⟨a', ha'⟩ : ∃ a' : ℤ, a' = a - a / P * P := ⟨_, rfl⟩
  have hmod := Int.emod_def a P
  have ha'0 : 0 ≤ a' := by
    have := Int.emod_nonneg a hP0.ne'
    rw [ha']
    linarith [mul_comm (a / P) P]
  have ha'P : a' < P := by
    have := Int.emod_lt_of_pos a hP0
    rw [ha']
    linarith [mul_comm (a / P) P]
  have harc : ∀ x y, a ≤ x → y ≤ P + a → ∀ v ∈ boxBoundary lo hi,
      (∃ k : ℤ, perimeterPos lo hi v + k * P ∈ Ico x y) ↔
        (perimeterPos lo hi v ∈ Ico (x - a + a') (y - a + a') ∨
          perimeterPos lo hi v + P ∈ Ico (x - a + a') (y - a + a')) := by
    intro x y hx hy v hv
    have hx' : x - a + a' = x - a / P * P := by rw [ha']; ring
    have hy' : y - a + a' = y - a / P * P := by rw [ha']; ring
    have hx0 : 0 ≤ x - a / P * P := by rw [← hx']; omega
    have hy0 : y - a / P * P ≤ 2 * P := by rw [← hy']; omega
    rw [← Int.exists_add_mul_mem_Ico_sub_mul_iff (m := a / P),
      Int.exists_add_mul_mem_Ico_iff hP0 (hpos v hv).1 (hpos v hv).2 hx0 hy0, hx', hy']
  -- the four arcs
  obtain ⟨A, hA⟩ : ∃ A : Set (LatticeSite 2), ∀ x, x ∈ A ↔
      x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico a c :=
    ⟨{x | x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico a c},
      fun _ => Iff.rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (LatticeSite 2), ∀ x, x ∈ B ↔
      x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico b d :=
    ⟨{x | x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico b d},
      fun _ => Iff.rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Set (LatticeSite 2), ∀ x, x ∈ C ↔
      x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico c b :=
    ⟨{x | x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico c b},
      fun _ => Iff.rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Set (LatticeSite 2), ∀ x, x ∈ D ↔
      x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico d (P + a) :=
    ⟨{x | x ∈ boxBoundary lo hi ∧ ∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico d (P + a)},
      fun _ => Iff.rfl⟩
  -- positions in the arcs, normalized
  have hAp : ∀ x ∈ A, x ∈ boxBoundary lo hi ∧
      (perimeterPos lo hi x ∈ Ico (a - a + a') (c - a + a') ∨
        perimeterPos lo hi x + P ∈ Ico (a - a + a') (c - a + a')) := fun x hx =>
    ⟨((hA x).1 hx).1, (harc a c le_rfl (by omega) x ((hA x).1 hx).1).1 ((hA x).1 hx).2⟩
  have hBp : ∀ x ∈ B, x ∈ boxBoundary lo hi ∧
      (perimeterPos lo hi x ∈ Ico (b - a + a') (d - a + a') ∨
        perimeterPos lo hi x + P ∈ Ico (b - a + a') (d - a + a')) := fun x hx =>
    ⟨((hB x).1 hx).1, (harc b d (by omega) (by omega) x ((hB x).1 hx).1).1 ((hB x).1 hx).2⟩
  have hCp : ∀ x ∈ C, x ∈ boxBoundary lo hi ∧
      (perimeterPos lo hi x ∈ Ico (c - a + a') (b - a + a') ∨
        perimeterPos lo hi x + P ∈ Ico (c - a + a') (b - a + a')) := fun x hx =>
    ⟨((hC x).1 hx).1, (harc c b (by omega) (by omega) x ((hC x).1 hx).1).1 ((hC x).1 hx).2⟩
  -- every boundary point lies in an arc
  have hpart : ∀ x ∈ boxBoundary lo hi, x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D := by
    intro x hx
    rw [hA, hB, hC, hD, harc a c le_rfl (by omega) x hx, harc b d (by omega) (by omega) x hx,
      harc c b (by omega) (by omega) x hx, harc d (P + a) (by omega) le_rfl x hx]
    have := hpos x hx
    simp only [hx, true_and, mem_Ico]
    omega
  have hsub : A ∪ C ∪ D ⊆ Icc lo hi := by
    rintro x ((hx | hx) | hx)
    · exact ((hA x).1 hx).1.1
    · exact ((hC x).1 hx).1.1
    · exact ((hD x).1 hx).1.1
  -- no face outside the box has corners in both `A` and `B`
  have hAB : ∀ x ∈ A, ∀ y ∈ B, ∀ f, f ∉ Icc lo (hi - 1) → x ∈ Icc f (f + 1) →
      y ∈ Icc f (f + 1) → False := by
    intro x hx y hy f hf hxf hyf
    obtain ⟨hxbd, hxa⟩ := hAp x hx
    obtain ⟨hybd, hyb⟩ := hBp y hy
    have := hpos x hxbd
    have := hpos y hybd
    simp only [mem_Ico] at hxa hyb
    have hxy : x ≠ y := by
      rintro rfl
      omega
    have hadj := perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ hxbd hybd hxy hf hxf hyf
    rw [← hP] at hadj
    omega
  -- the corner at the junction of `A` and `C`
  obtain ⟨p₀, hp₀0, hp₀P, hp₀⟩ : ∃ p₀ : ℤ, 0 ≤ p₀ ∧ p₀ < P ∧
      (p₀ = c - a + a' - 1 ∨ p₀ = c - a + a' - 1 - P) := by
    by_cases h : c - a + a' ≤ P
    · exact ⟨c - a + a' - 1, by omega, by omega, Or.inl rfl⟩
    · exact ⟨c - a + a' - 1 - P, by omega, by omega, Or.inr rfl⟩
  obtain ⟨v₀, w₀, f₀, hv₀, hpv₀, hw₀, hpw₀, hf₀, hv₀f₀, hw₀f₀, hone⟩ :=
    exists_notMem_Icc_of_perimeterPos h₀ h₁ hp₀0 (by rw [← hP]; exact hp₀P)
  rw [← hP] at hpw₀
  have hv₀A : v₀ ∈ A := by
    rw [hA, harc a c le_rfl (by omega) v₀ hv₀]
    have := hpos v₀ hv₀
    simp only [hv₀, true_and, mem_Ico]
    omega
  have hw₀C : w₀ ∈ C := by
    rw [hC, harc c b (by omega) (by omega) w₀ hw₀]
    have := hpos w₀ hw₀
    simp only [hw₀, true_and, mem_Ico]
    omega
  -- the junction corner is the only corner with vertex in `A` and face in the dual arc of `C`
  have hJ : ∀ x ∈ A, ∀ w ∈ C, ∀ g, g ∉ Icc lo (hi - 1) → x ∈ Icc g (g + 1) →
      w ∈ Icc g (g + 1) → x = v₀ ∧ g = f₀ := by
    intro x hx w hw g hg hxg hwg
    obtain ⟨hxbd, hxa⟩ := hAp x hx
    obtain ⟨hwbd, hwc⟩ := hCp w hw
    have := hpos x hxbd
    have := hpos w hwbd
    have := hpos w₀ hw₀
    simp only [mem_Ico] at hxa hwc
    have hxw : x ≠ w := by
      rintro rfl
      omega
    have hadj := perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ hxbd hwbd hxw hg hxg hwg
    rw [← hP] at hadj
    have hx₀ : x = v₀ := perimeterPos_injOn lo hi hxbd hv₀ (by omega)
    have hw₀' : w = w₀ := perimeterPos_injOn lo hi hwbd hw₀ (by omega)
    subst hx₀ hw₀'
    exact ⟨rfl, eq_of_notMem_Icc_sub_one h₀ h₁ hxbd.1 hwbd.1 hxw hg hf₀ ⟨hxg, hv₀f₀⟩
      ⟨hwg, hw₀f₀⟩⟩
  obtain ⟨f, ⟨hf, x, hxC, hxf⟩, g, ⟨hg, y, hyD, hyg⟩, hfg⟩ :=
    exists_dualConfig_inter_mem_localConn_of_arcs hpart hsub hAB hJ hv₀A ⟨hf₀, w₀, hw₀C, hw₀f₀⟩
      hv₀f₀ hone (fun ⟨u, hu, w, hw, h⟩ =>
        hω ⟨u, w, ((hA u).1 hu).1, ((hA u).1 hu).2, ((hB w).1 hw).1, ((hB w).1 hw).2, h⟩)
  exact ⟨f, g, ⟨hf, x, ((hC x).1 hxC).1, hxf, ((hC x).1 hxC).2⟩,
    ⟨hg, y, ((hD y).1 hyD).1, hyg, ((hD y).1 hyD).2⟩, hfg⟩

/-! ### Dual edges at a face, and faces outside the box -/

/-- **The four dual edges at a face.** An edge `E` of `ℤ²` (read as a dual edge) contains the
face `(x, y)` exactly when it is the dual edge of one of the four edges of that face, and then of
exactly one of them. -/
theorem ite_mem_eq_sum_ite_dualEdge {E : Sym2 (LatticeSite 2)} (hE : E ∈ (zdGraph 2).edgeSet)
    (x y : ℤ) :
    (if ![x, y] ∈ E then (1 : ℤ) else 0) =
      (if E = dualEdge s(![x, y], ![x + 1, y]) then 1 else 0) +
        (if E = dualEdge s(![x, y + 1], ![x + 1, y + 1]) then 1 else 0) +
        (if E = dualEdge s(![x, y], ![x, y + 1]) then 1 else 0) +
        (if E = dualEdge s(![x + 1, y], ![x + 1, y + 1]) then 1 else 0) := by
  rw [dualEdge_horizontal, dualEdge_horizontal, dualEdge_vertical, dualEdge_vertical,
    add_sub_cancel_right, add_sub_cancel_right]
  by_cases hm : ![x, y] ∈ E
  · rw [ite_eq_left hm]
    obtain ⟨n, rfl⟩ := Sym2.mem_iff_exists.1 hm
    rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff] at hE
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hE
    rw [Sym2.eq_swap (a := ![x, y - 1]), Sym2.eq_swap (a := ![x + 1, y])]
    simp only [Sym2.congr_right, eq_vec_two_iff]
    split_ifs <;> omega
  · have k : ∀ D : Sym2 (LatticeSite 2), ![x, y] ∈ D → ¬ E = D := fun D hD hED => hm (hED ▸ hD)
    rw [ite_eq_right hm, ite_eq_right (k _ (Sym2.mem_mk_right _ _)),
      ite_eq_right (k _ (Sym2.mem_mk_left _ _)), ite_eq_right (k _ (Sym2.mem_mk_left _ _)),
      ite_eq_right (k _ (Sym2.mem_mk_right _ _))]
    norm_num

/-- The ends of an edge are corners of both faces of its dual edge. -/
theorem mem_Icc_of_mem_dualEdge {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    {x h : LatticeSite 2} (hx : x ∈ e) (hh : h ∈ dualEdge e) : x ∈ Icc h (h + 1) := by
  rw [mem_Icc_two_iff]
  simp only [Pi.add_apply, Pi.one_apply]
  obtain ⟨a, b, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · rw [dualEdge_horizontal, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hh
    rw [Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hx
    omega
  · rw [dualEdge_vertical, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hh
    rw [Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hx
    omega

section Outer

variable {lo hi : LatticeSite 2}

/-- The coordinates of an edge of `ℤ²` inside the box `Icc lo hi` and of a face of its dual edge
not inside the box. -/
theorem exists_of_mem_dualEdge_of_notMem_Icc {e : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) (heR : ∀ x ∈ e, x ∈ Icc lo hi) {h : LatticeSite 2}
    (hh : h ∉ Icc lo (hi - 1)) (hhe : h ∈ dualEdge e) :
    ∃ x y : ℤ, lo 0 ≤ x ∧ x ≤ hi 0 ∧ lo 1 ≤ y ∧ y ≤ hi 1 ∧
      ((e = s(![x, y], ![x + 1, y]) ∧ x + 1 ≤ hi 0 ∧ h 0 = x ∧
          ((y = lo 1 ∧ h 1 = y - 1) ∨ (y = hi 1 ∧ h 1 = y))) ∨
        (e = s(![x, y], ![x, y + 1]) ∧ y + 1 ≤ hi 1 ∧ h 1 = y ∧
          ((x = lo 0 ∧ h 0 = x - 1) ∨ (x = hi 0 ∧ h 0 = x)))) := by
  rw [mem_Icc_two_iff] at hh
  simp only [Pi.sub_apply, Pi.one_apply] at hh
  obtain ⟨a, b, rfl | rfl⟩ := (mem_edgeSet_zdGraph_two_iff e).1 he
  · have h₁ := heR _ (Sym2.mem_mk_left _ _)
    have h₂ := heR _ (Sym2.mem_mk_right _ _)
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂
    rw [dualEdge_horizontal, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hhe
    refine ⟨a, b, by omega, by omega, by omega, by omega, Or.inl ⟨rfl, by omega, by omega, ?_⟩⟩
    omega
  · have h₁ := heR _ (Sym2.mem_mk_left _ _)
    have h₂ := heR _ (Sym2.mem_mk_right _ _)
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂
    rw [dualEdge_vertical, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff] at hhe
    refine ⟨a, b, by omega, by omega, by omega, by omega, Or.inr ⟨rfl, by omega, by omega, ?_⟩⟩
    omega

/-- **An outer face crosses one edge of the box.** A face not inside the box lies in the dual
edges of at most one edge of the box. -/
theorem eq_of_mem_dualEdge_of_mem_dualEdge {e e' : Sym2 (LatticeSite 2)}
    (he : e ∈ (zdGraph 2).edgeSet) (he' : e' ∈ (zdGraph 2).edgeSet)
    (heR : ∀ x ∈ e, x ∈ Icc lo hi) (heR' : ∀ x ∈ e', x ∈ Icc lo hi) {h : LatticeSite 2}
    (hh : h ∉ Icc lo (hi - 1)) (hhe : h ∈ dualEdge e) (hhe' : h ∈ dualEdge e') : e = e' := by
  obtain ⟨x, y, h₁, h₂, h₃, h₄, ⟨rfl, h₅, hx, hy⟩ | ⟨rfl, h₅, hy, hx⟩⟩ :=
    exists_of_mem_dualEdge_of_notMem_Icc he heR hh hhe <;>
  obtain ⟨x', y', h₁', h₂', h₃', h₄', ⟨rfl, h₅', hx', hy'⟩ | ⟨rfl, h₅', hy', hx'⟩⟩ :=
    exists_of_mem_dualEdge_of_notMem_Icc he' heR' hh hhe' <;>
  exact sym2_vec_two_eq (by omega) (by omega) (by omega) (by omega)

/-- **An edge of the box has at most one outer face.** In a box of positive width and height, at
most one of the two faces of the dual of an edge of the box is not inside the box. -/
theorem eq_of_mem_dualEdge_of_notMem_Icc (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) (heR : ∀ x ∈ e, x ∈ Icc lo hi)
    {h h' : LatticeSite 2} (hh : h ∉ Icc lo (hi - 1)) (hh' : h' ∉ Icc lo (hi - 1))
    (hhe : h ∈ dualEdge e) (hhe' : h' ∈ dualEdge e) : h = h' := by
  obtain ⟨x, y, h₁, h₂, h₃, h₄, ⟨rfl, h₅, hx, hy⟩ | ⟨rfl, h₅, hy, hx⟩⟩ :=
    exists_of_mem_dualEdge_of_notMem_Icc he heR hh hhe <;>
  obtain ⟨x', y', h₁', h₂', h₃', h₄', ⟨he', h₅', hx', hy'⟩ | ⟨he', h₅', hy', hx'⟩⟩ :=
    exists_of_mem_dualEdge_of_notMem_Icc he heR hh' hhe' <;>
  · simp only [Sym2.eq_iff, eq_vec_two_iff, Matrix.cons_val_zero, Matrix.cons_val_one] at he'
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> omega

/-- **Two boundary corners of an outer face span an edge.** Two distinct points of the box that are
corners of one face not inside the box are the ends of an edge of `ℤ²`, whose dual edge has
that face as an end. -/
theorem mem_edgeSet_and_mem_dualEdge_of_notMem_Icc {v w f : LatticeSite 2} (hv : v ∈ Icc lo hi)
    (hw : w ∈ Icc lo hi) (hvw : v ≠ w) (hf : f ∉ Icc lo (hi - 1)) (hvf : v ∈ Icc f (f + 1))
    (hwf : w ∈ Icc f (f + 1)) : s(v, w) ∈ (zdGraph 2).edgeSet ∧ f ∈ dualEdge s(v, w) := by
  have hne : v 0 ≠ w 0 ∨ v 1 ≠ w 1 := by
    by_contra h
    push Not at h
    exact hvw (funext (Fin.forall_fin_two.2 h))
  rw [mem_Icc_two_iff] at hv hw hvf hwf hf
  simp only [Pi.add_apply, Pi.one_apply, Pi.sub_apply] at hvf hwf hf
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff]
    omega
  · rw [dualEdge_mk, Sym2.mem_iff, eq_vec_two_iff, eq_vec_two_iff]
    omega

end Outer

/-! ### Crossings of a dual walk -/

section Walk

variable {D : Config (LatticeSite 2)} {f g : LatticeSite 2}

/-- **Crossings of the four edges of a face.** Let `σ` be a walk of the dual lattice from `f` to
`g`, and `X e` the number of steps of `σ` along the dual edge of `e`, modulo two. The values of
`X` on the four edges of the face `(x, y)` add up to the number of ends of `σ` at that face. -/
theorem add_add_add_eq_of_walk (hD : D ⊆ (zdGraph 2).edgeSet) (σ : (openGraph D).Walk f g)
    {X : Sym2 (LatticeSite 2) → ZMod 2}
    (hX : ∀ e, X e = (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then 1 else 0).sum)
    (x y : ℤ) :
    X s(![x, y], ![x + 1, y]) + X s(![x, y + 1], ![x + 1, y + 1]) + X s(![x, y], ![x, y + 1]) +
        X s(![x + 1, y], ![x + 1, y + 1]) =
      (if f = ![x, y] then 1 else 0) + (if g = ![x, y] then 1 else 0) := by
  rw [hX, hX, hX, hX, ← List.sum_map_add, ← List.sum_map_add, ← List.sum_map_add,
    ← SimpleGraph.Walk.sum_map_darts_add_zmod_two
      (fun w => if w = ![x, y] then (1 : ZMod 2) else 0) σ]
  congr 1
  refine List.map_congr_left fun δ _ => ?_
  have hadj := (openGraph_adj_iff _ _ _).1 δ.adj
  have h₁ := congrArg (Int.cast : ℤ → ZMod 2) (ite_mem_eq_sum_ite_dualEdge (hD hadj.1) x y)
  push_cast at h₁
  rw [Sym2.ite_add_ite_eq_ite_mem hadj.2 ![x, y] (1 : ZMod 2), h₁]

/-- A walk along dual edges of closed edges crosses no open edge. -/
theorem sum_map_ite_eq_zero_of_mem {ω : Config (LatticeSite 2)} (hD : D ⊆ dualConfig ω)
    (σ : (openGraph D).Walk f g) {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet)
    (heω : e ∈ ω) :
    (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then (1 : ZMod 2) else 0).sum = 0 := by
  refine List.sum_eq_zero fun t ht => ?_
  obtain ⟨δ, -, rfl⟩ := List.mem_map.1 ht
  refine ite_eq_right fun h => ?_
  have := hD ((openGraph_adj_iff _ _ _).1 δ.adj).1
  rw [h, dualEdge_mem_dualConfig_iff he] at this
  exact this heω

/-- **Crossings of a boundary edge.** Let `σ` be a walk from `f` to `g`, two faces not inside a box
of positive width and height, whose steps are dual edges of edges of the box. Then `σ` crosses an
edge `e` of the box with a face `h` outside the box an odd number of times exactly when one of
`f` and `g` is that outer face, an end of the dual edge of `e`. -/
theorem sum_map_ite_eq_add_of_notMem_Icc {lo hi : LatticeSite 2} (h₀ : lo 0 < hi 0)
    (h₁ : lo 1 < hi 1)
    (hD : ∀ E ∈ D, ∃ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) ∧ dualEdge e = E)
    (σ : (openGraph D).Walk f g) (hf : f ∉ Icc lo (hi - 1)) (hg : g ∉ Icc lo (hi - 1))
    {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) (heR : ∀ x ∈ e, x ∈ Icc lo hi)
    {h : LatticeSite 2} (hh : h ∉ Icc lo (hi - 1)) (hhe : h ∈ dualEdge e) :
    (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then (1 : ZMod 2) else 0).sum =
      (if f ∈ dualEdge e then 1 else 0) + (if g ∈ dualEdge e then 1 else 0) := by
  classical
  have key := SimpleGraph.Walk.sum_map_darts_add_zmod_two
    (fun w => if w ∉ Icc lo (hi - 1) ∧ w ∈ dualEdge e then (1 : ZMod 2) else 0) σ
  simp only [hf, hg, not_false_eq_true, true_and] at key
  rw [← key]
  congr 1
  refine List.map_congr_left fun δ _ => ?_
  obtain ⟨hDδ, hne⟩ := (openGraph_adj_iff _ _ _).1 δ.adj
  obtain ⟨e', he', he'R, hee'⟩ := hD _ hDδ
  by_cases hc : s(δ.fst, δ.snd) = dualEdge e
  · rw [ite_eq_left hc]
    have hhm : h ∈ s(δ.fst, δ.snd) := hc ▸ hhe
    rcases Sym2.mem_iff.1 hhm with rfl | rfl
    · have hφ := And.intro hh hhe
      rw [ite_eq_left hφ, ite_eq_right, add_zero]
      rintro ⟨hs, hse⟩
      exact hne (eq_of_mem_dualEdge_of_notMem_Icc h₀ h₁ he heR hh hs hhe hse)
    · have hφ := And.intro hh hhe
      rw [ite_eq_left hφ, ite_eq_right, zero_add]
      rintro ⟨hs, hse⟩
      exact hne (eq_of_mem_dualEdge_of_notMem_Icc h₀ h₁ he heR hs hh hse hhe)
  · have k : ∀ w ∈ s(δ.fst, δ.snd), ¬ (w ∉ Icc lo (hi - 1) ∧ w ∈ dualEdge e) := by
      rintro w hw ⟨hwR, hwe⟩
      rw [← hee'] at hw
      exact hc (by rw [← hee', eq_of_mem_dualEdge_of_mem_dualEdge he' he he'R heR hwR hw hwe])
    rw [ite_eq_right hc, ite_eq_right (k _ (Sym2.mem_mk_left _ _)),
      ite_eq_right (k _ (Sym2.mem_mk_right _ _)), add_zero]

end Walk

/-! ### A parity function on the vertices of the box -/

section Parity

variable {lo hi : LatticeSite 2} {X : Sym2 (LatticeSite 2) → ZMod 2} {N : LatticeSite 2 → ZMod 2}

/-- The parity function across a horizontal edge: it changes by the crossings of that edge. -/
theorem eq_add_of_horizontal
    (hN : ∀ v, N v = ∑ x ∈ Finset.Ico (lo 0) (v 0), X s(![x, v 1], ![x + 1, v 1]) +
      ∑ y ∈ Finset.Ico (lo 1) (v 1), X s(![lo 0, y], ![lo 0, y + 1]))
    {x y : ℤ} (hx : lo 0 ≤ x) : N ![x + 1, y] = N ![x, y] + X s(![x, y], ![x + 1, y]) := by
  rw [hN, hN]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hx, add_right_comm]

/-- The parity function across a vertical edge of the box: it changes by the crossings of that
edge, as long as the walk has no end at a face inside the box. -/
theorem eq_add_of_vertical {D : Config (LatticeSite 2)} {f g : LatticeSite 2}
    (hD : D ⊆ (zdGraph 2).edgeSet) (σ : (openGraph D).Walk f g) (hf : f ∉ Icc lo (hi - 1))
    (hg : g ∉ Icc lo (hi - 1))
    (hX : ∀ e, X e = (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then 1 else 0).sum)
    (hN : ∀ v, N v = ∑ x ∈ Finset.Ico (lo 0) (v 0), X s(![x, v 1], ![x + 1, v 1]) +
      ∑ y ∈ Finset.Ico (lo 1) (v 1), X s(![lo 0, y], ![lo 0, y + 1]))
    {x y : ℤ} (hx₀ : lo 0 ≤ x) (hx₁ : x ≤ hi 0) (hy₀ : lo 1 ≤ y) (hy₁ : y + 1 ≤ hi 1) :
    N ![x, y + 1] = N ![x, y] + X s(![x, y], ![x, y + 1]) := by
  rw [hN, hN]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hy₀]
  -- the faces `(x', y)` with `lo 0 ≤ x' < x` lie inside the box
  have hface : ∀ x' ∈ Finset.Ico (lo 0) x,
      X s(![x', y], ![x' + 1, y]) + X s(![x', y + 1], ![x' + 1, y + 1]) =
        X s(![x', y], ![x', y + 1]) + X s(![x' + 1, y], ![x' + 1, y + 1]) := by
    intro x' hx'
    rw [Finset.mem_Ico] at hx'
    have hin : ![x', y] ∈ Icc lo (hi - 1) := by
      rw [mem_Icc_two_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, Pi.one_apply]
      omega
    have h4 := add_add_add_eq_of_walk hD σ hX x' y
    have hfx : ¬ f = ![x', y] := fun h => hf (h ▸ hin)
    have hgx : ¬ g = ![x', y] := fun h => hg (h ▸ hin)
    rw [ite_eq_right hfx, ite_eq_right hgx] at h4
    have h2 : ∀ a b c d : ZMod 2, a + b + c + d = 0 + 0 → a + b = c + d := by decide
    exact h2 _ _ _ _ h4
  -- telescoping along the row
  have htel : ∀ b : ℤ, lo 0 ≤ b → ∑ i ∈ Finset.Ico (lo 0) b,
      (X s(![i, y], ![i, y + 1]) + X s(![i + 1, y], ![i + 1, y + 1])) =
        X s(![lo 0, y], ![lo 0, y + 1]) + X s(![b, y], ![b, y + 1]) := by
    intro b hb
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = lo 0 + n := ⟨(b - lo 0).toNat, by omega⟩
    induction n with
    | zero =>
      have h0 : ∀ p : ZMod 2, 0 = p + p := by decide
      rw [Nat.cast_zero, add_zero, Finset.Ico_self, Finset.sum_empty]
      exact h0 _
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc, ← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega),
        ih (by omega)]
      have h3 : ∀ p q r : ZMod 2, p + q + (q + r) = p + r := by decide
      exact h3 _ _ _
  have hsum := htel x hx₀
  rw [← Finset.sum_congr rfl hface, Finset.sum_add_distrib] at hsum
  have h5 : ∀ A A' S V₀ V : ZMod 2, A + A' = V₀ + V → A' + (S + V₀) = A + S + V := by decide
  exact h5 _ _ _ _ _ hsum

/-- **The parity function across an edge of the box.** It changes by the crossings of that edge. -/
theorem eq_add_of_mem_edgeSet {D : Config (LatticeSite 2)} {f g : LatticeSite 2}
    (hD : D ⊆ (zdGraph 2).edgeSet) (σ : (openGraph D).Walk f g) (hf : f ∉ Icc lo (hi - 1))
    (hg : g ∉ Icc lo (hi - 1))
    (hX : ∀ e, X e = (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then 1 else 0).sum)
    (hN : ∀ v, N v = ∑ x ∈ Finset.Ico (lo 0) (v 0), X s(![x, v 1], ![x + 1, v 1]) +
      ∑ y ∈ Finset.Ico (lo 1) (v 1), X s(![lo 0, y], ![lo 0, y + 1]))
    {v w : LatticeSite 2} (hv : v ∈ Icc lo hi) (hw : w ∈ Icc lo hi)
    (hvw : s(v, w) ∈ (zdGraph 2).edgeSet) : N w = N v + X s(v, w) := by
  have h2 : ∀ p q r : ZMod 2, p = q + r → q = p + r := by decide
  rw [mem_Icc_two_iff] at hv hw
  rw [SimpleGraph.mem_edgeSet, zdGraph_two_adj_iff] at hvw
  rw [eq_vec_two v, eq_vec_two w]
  rcases hvw with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
  · rw [← h0, ← h1]
    exact eq_add_of_vertical hD σ hf hg hX hN (by omega) (by omega) (by omega) (by omega)
  · rw [h0, ← h1, Sym2.eq_swap]
    exact h2 _ _ _
      (eq_add_of_vertical hD σ hf hg hX hN (by omega) (by omega) (by omega) (by omega))
  · rw [← h1, ← h0]
    exact eq_add_of_horizontal hN (by omega)
  · rw [h1, ← h0, Sym2.eq_swap]
    exact h2 _ _ _ (eq_add_of_horizontal hN (by omega))

/-- **The parity function is constant on open clusters of the box**, for a walk crossing only
closed edges. -/
theorem eq_of_mem_localConn {D : Config (LatticeSite 2)} {f g : LatticeSite 2}
    {ω : Config (LatticeSite 2)} (hD : D ⊆ (zdGraph 2).edgeSet) (hDω : D ⊆ dualConfig ω)
    (σ : (openGraph D).Walk f g) (hf : f ∉ Icc lo (hi - 1)) (hg : g ∉ Icc lo (hi - 1))
    (hX : ∀ e, X e = (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then 1 else 0).sum)
    (hN : ∀ v, N v = ∑ x ∈ Finset.Ico (lo 0) (v 0), X s(![x, v 1], ![x + 1, v 1]) +
      ∑ y ∈ Finset.Ico (lo 1) (v 1), X s(![lo 0, y], ![lo 0, y + 1]))
    {u v : LatticeSite 2} (huv : ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v) :
    N u = N v := by
  obtain ⟨hu, hv, ⟨p⟩⟩ := huv
  have hstep : ∀ v w : Icc lo hi,
      ((openGraph (ω ∩ (zdGraph 2).edgeSet)).induce (Icc lo hi)).Adj v w → N w.1 = N v.1 := by
    intro v w hvw
    have hadj : s(v.1, w.1) ∈ ω ∩ (zdGraph 2).edgeSet := ((openGraph_adj_iff _ _ _).1 hvw).1
    rw [eq_add_of_mem_edgeSet hD σ hf hg hX hN v.2 w.2 hadj.2, hX,
      sum_map_ite_eq_zero_of_mem hDω σ hadj.2 hadj.1, add_zero]
  have hwalk : ∀ {v w : Icc lo hi}
      (p : ((openGraph (ω ∩ (zdGraph 2).edgeSet)).induce (Icc lo hi)).Walk v w),
      N w.1 = N v.1 := by
    intro v w p
    induction p with
    | nil => rfl
    | cons h _ ih => exact ih.trans (hstep _ _ h)
  exact (hwalk p).symm

end Parity

/-! ### Walking along the boundary -/

section Boundary

variable {lo hi : LatticeSite 2}

/-- **Telescoping along the boundary.** If a function `N` changes by `T p` from the boundary point
at position `p` to the one at position `p + 1`, then from `v` to `w` (further along) it changes by
the sum of `T` over the positions from that of `v` to that of `w`. -/
theorem eq_add_sum_of_perimeterPos (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {N : LatticeSite 2 → ZMod 2} {T : ℤ → ZMod 2}
    (hstep : ∀ v w, v ∈ boxBoundary lo hi → w ∈ boxBoundary lo hi →
      perimeterPos lo hi w = perimeterPos lo hi v + 1 → N w = N v + T (perimeterPos lo hi v))
    {v w : LatticeSite 2} (hv : v ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (hvw : perimeterPos lo hi v ≤ perimeterPos lo hi w) :
    N w = N v + ∑ i ∈ Finset.Ico (perimeterPos lo hi v) (perimeterPos lo hi w), T i := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have hv0 := perimeterPos_nonneg hv.1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, perimeterPos lo hi w = perimeterPos lo hi v + n :=
    ⟨(perimeterPos lo hi w - perimeterPos lo hi v).toNat, by omega⟩
  clear hvw
  induction n generalizing w with
  | zero =>
    have : w = v := perimeterPos_injOn lo hi hw hv (by simpa using hn)
    subst this
    rw [Finset.Ico_self, Finset.sum_empty, add_zero]
  | succ n ih =>
    have hlt := perimeterPos_lt hne hw.1
    obtain ⟨w', -, -, hw', hpw', -⟩ :=
      exists_notMem_Icc_of_perimeterPos h₀ h₁ (p := perimeterPos lo hi v + n) (by omega)
        (by push_cast at hn; omega)
    rw [hstep w' w hw' hw (by push_cast at hn; omega), ih hw' hpw', hpw', hn, Nat.cast_succ,
      ← add_assoc, ← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega), add_assoc]

/-- **The boundary edge of an outer face, oriented along the boundary.** An edge of a box of
positive width and height with a face outside the box joins two boundary points at consecutive
positions (modulo the perimeter). -/
theorem exists_perimeterPos_eq_add_one_of_mem_dualEdge (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {e : Sym2 (LatticeSite 2)} (he : e ∈ (zdGraph 2).edgeSet) (heR : ∀ x ∈ e, x ∈ Icc lo hi)
    {f : LatticeSite 2} (hf : f ∉ Icc lo (hi - 1)) (hfe : f ∈ dualEdge e) :
    ∃ y₁ y₂, y₁ ∈ boxBoundary lo hi ∧ y₂ ∈ boxBoundary lo hi ∧ e = s(y₁, y₂) ∧
      (perimeterPos lo hi y₂ = perimeterPos lo hi y₁ + 1 ∨
        (perimeterPos lo hi y₁ = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1 ∧
          perimeterPos lo hi y₂ = 0)) := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := ((SimpleGraph.mem_edgeSet _).1 he).ne
    have ha := mem_boxBoundary_of_notMem_Icc (heR a (Sym2.mem_mk_left _ _)) hf
      (mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_left _ _) hfe)
    have hb := mem_boxBoundary_of_notMem_Icc (heR b (Sym2.mem_mk_right _ _)) hf
      (mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_right _ _) hfe)
    rcases perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ ha hb hab hf
      (mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_left _ _) hfe)
      (mem_Icc_of_mem_dualEdge he (Sym2.mem_mk_right _ _) hfe) with h | h | h | h
    · exact ⟨a, b, ha, hb, rfl, Or.inl h⟩
    · exact ⟨b, a, hb, ha, Sym2.eq_swap, Or.inl h⟩
    · exact ⟨b, a, hb, ha, Sym2.eq_swap, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨a, b, ha, hb, rfl, Or.inr ⟨h.2, h.1⟩⟩

/-- **An outer face has two boundary corners.** In a box of positive width and height, a third
boundary corner of a face outside the box is one of two given distinct ones. -/
theorem eq_or_eq_of_notMem_Icc (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {f y y₁ y₂ : LatticeSite 2}
    (hf : f ∉ Icc lo (hi - 1)) (hy : y ∈ boxBoundary lo hi) (hy₁ : y₁ ∈ boxBoundary lo hi)
    (hy₂ : y₂ ∈ boxBoundary lo hi) (h₁₂ : y₁ ≠ y₂) (hyf : y ∈ Icc f (f + 1))
    (hy₁f : y₁ ∈ Icc f (f + 1)) (hy₂f : y₂ ∈ Icc f (f + 1)) : y = y₁ ∨ y = y₂ := by
  by_contra h
  push Not at h
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have a₁ := perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ hy hy₁ h.1 hf hyf hy₁f
  have a₂ := perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ hy hy₂ h.2 hf hyf hy₂f
  have a₃ := perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ hy₁ hy₂ h₁₂ hf hy₁f hy₂f
  have d₁ : perimeterPos lo hi y ≠ perimeterPos lo hi y₁ := fun hp =>
    h.1 (perimeterPos_injOn lo hi hy hy₁ hp)
  have d₂ : perimeterPos lo hi y ≠ perimeterPos lo hi y₂ := fun hp =>
    h.2 (perimeterPos_injOn lo hi hy hy₂ hp)
  have b := perimeterPos_lt hne hy.1
  have b₁ := perimeterPos_lt hne hy₁.1
  have b₂ := perimeterPos_lt hne hy₂.1
  have c := perimeterPos_nonneg hy.1
  have c₁ := perimeterPos_nonneg hy₁.1
  have c₂ := perimeterPos_nonneg hy₂.1
  omega

/-- **Which boundary edge has a given outer face.** If the face `f` outside the box is a face of
the boundary edge from `y₁` to the next boundary point `y₂`, then `f` is a face of the boundary
edge from `v` to the next boundary point `w` exactly when `v = y₁`, read on positions. -/
theorem mem_dualEdge_iff_perimeterPos_eq (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1)
    {f y₁ y₂ v w : LatticeSite 2} (hf : f ∉ Icc lo (hi - 1)) (hy₁ : y₁ ∈ boxBoundary lo hi)
    (hy₂ : y₂ ∈ boxBoundary lo hi) (hy : s(y₁, y₂) ∈ (zdGraph 2).edgeSet)
    (hfy : f ∈ dualEdge s(y₁, y₂))
    (hpos : perimeterPos lo hi y₂ = perimeterPos lo hi y₁ + 1 ∨
      (perimeterPos lo hi y₁ = 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) - 1 ∧
        perimeterPos lo hi y₂ = 0))
    (hv : v ∈ boxBoundary lo hi) (hw : w ∈ boxBoundary lo hi)
    (hvw : s(v, w) ∈ (zdGraph 2).edgeSet)
    (hpvw : perimeterPos lo hi w = perimeterPos lo hi v + 1) :
    f ∈ dualEdge s(v, w) ↔ perimeterPos lo hi v = perimeterPos lo hi y₁ := by
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  have hR : ∀ x y : LatticeSite 2, x ∈ boxBoundary lo hi → y ∈ boxBoundary lo hi →
      ∀ z ∈ s(x, y), z ∈ Icc lo hi := by
    intro x y hx hy z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    exacts [hx.1, hy.1]
  have b := perimeterPos_lt hne hw.1
  constructor
  · intro hfvw
    have he := eq_of_mem_dualEdge_of_mem_dualEdge hvw hy (hR v w hv hw) (hR y₁ y₂ hy₁ hy₂) hf
      hfvw hfy
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · omega
  · intro hp
    have hv₁ : v = y₁ := perimeterPos_injOn lo hi hv hy₁ hp
    have hw₂ : w = y₂ := perimeterPos_injOn lo hi hw hy₂ (by omega)
    rw [hv₁, hw₂]
    exact hfy

end Boundary

/-! ### Quad duality, not both -/

/-- **Quad duality, not both.** Let `R = Icc lo hi` be a box of `ℤ²` of positive width and
height, with perimeter `P = 2 (hi₀ - lo₀) + 2 (hi₁ - lo₁)`, and let `a < c < b < d < P + a`.
Reading perimeter positions modulo `P`, the boundary of `R` splits into the arcs `A = [a, c)`,
`C = [c, b)`, `B = [b, d)` and `D = [d, P + a)`. An open path inside `R` from `A` to `B` and a
dual-open path in the dual box `Icc (lo - 1) hi`, crossing only edges of `R`, from the dual arc of
`C` to the dual arc of `D` never coexist. The sets are those of
`exists_dualConfig_inter_mem_localConn_of_not_exists`.

The proof is a parity argument. For the dual path `σ` and each vertex `(x, y)` of `R`, `N (x, y)`
counts modulo two the crossings by `σ` of the path from `lo` up the left side to `(lo₀, y)` and
then along the row to `(x, y)`. Across every edge of `R` it changes by the crossings of that edge,
because `σ` has no end at a face inside `R`; so it is constant on open clusters. Along the
boundary it changes only at the two boundary edges where `σ` leaves `R` (one of them next to `C`,
the other next to `D`), and those separate `A` from `B`. -/
theorem not_exists_dualConfig_inter_mem_localConn_of_exists {lo hi : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {a c b d : ℤ}
    (hacbd : a < c ∧ c < b ∧ b < d ∧ d < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)
    {ω : Config (LatticeSite 2)}
    (hω : ∃ u v, u ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi u + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico a c) ∧
      v ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi v + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico b d) ∧
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v) :
    ¬ ∃ f g, (f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc f (f + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico c b) ∧
      (g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc g (g + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈
          Ico d (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)) ∧
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g := by
  classical
  rintro ⟨f, g, ⟨hf, y, hy, hyf, hyC⟩, ⟨hg, z, hz, hzg, hzD⟩, hfg⟩
  obtain ⟨u, v, hu, huA, hv, hvB, huv⟩ := hω
  obtain ⟨hac, hcb, hbd, hda⟩ := hacbd
  have hne : lo ≠ hi := fun h => by
    rw [h] at h₀
    exact lt_irrefl _ h₀
  set P := 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) with hP
  have hP0 : 0 < P := by omega
  have hpos : ∀ x ∈ boxBoundary lo hi, 0 ≤ perimeterPos lo hi x ∧ perimeterPos lo hi x < P :=
    fun x hx => ⟨perimeterPos_nonneg hx.1, perimeterPos_lt hne hx.1⟩
  -- positions normalized: shift the arcs by the multiple `M` of `P` that brings `a` to `[0, P)`
  have key : ∀ x ∈ boxBoundary lo hi, ∀ s t : ℤ, a ≤ s → t ≤ P + a →
      ((∃ k : ℤ, perimeterPos lo hi x + k * P ∈ Ico s t) ↔
        (perimeterPos lo hi x ∈ Ico (s - a / P * P) (t - a / P * P) ∨
          perimeterPos lo hi x + P ∈ Ico (s - a / P * P) (t - a / P * P))) :=
    fun x hx s t hs ht =>
      Int.exists_add_mul_mem_Ico_iff_of_le hP0 (hpos x hx).1 (hpos x hx).2 hs ht
  rw [key u hu a c le_rfl (by omega)] at huA
  rw [key v hv b d (by omega) (by omega)] at hvB
  rw [key y hy c b (by omega) (by omega)] at hyC
  rw [key z hz d (P + a) (by omega) le_rfl] at hzD
  have hM₀ := Int.emod_nonneg a hP0.ne'
  have hM₁ := Int.emod_lt_of_pos a hP0
  have hM₂ := Int.emod_def a P
  rw [mul_comm] at hM₂
  set M := a / P * P with hM
  simp only [mem_Ico] at huA hvB hyC hzD
  have pu := hpos u hu
  have pv := hpos v hv
  have py := hpos y hy
  have pz := hpos z hz
  -- the dual edges used
  set D := dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi}
    with hD
  have hD₁ : D ⊆ (zdGraph 2).edgeSet := fun E hE => dualConfig_subset_edgeSet ω hE.1
  have hD₂ : D ⊆ dualConfig ω := fun E hE => hE.1
  have hD₃ : ∀ E ∈ D, ∃ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) ∧ dualEdge e = E := by
    rintro E ⟨-, e, ⟨he, heR⟩, rfl⟩
    exact ⟨e, he, heR, rfl⟩
  -- the dual walk, between distinct faces
  obtain ⟨hfT, hgT, ⟨σ₀⟩⟩ := hfg
  let σ : (openGraph D).Walk f g := σ₀.map (SimpleGraph.Embedding.induce _).toHom
  have hfg : f ≠ g := by
    rintro rfl
    have hyz : y ≠ z := by
      rintro rfl
      omega
    have := perimeterPos_eq_add_one_or_of_notMem_Icc h₀ h₁ hy hz hyz hf hyf hzg
    omega
  -- the boundary edges through which the walk leaves the box at its two ends
  have hend : ∀ {f' g' : LatticeSite 2} (τ : (openGraph D).Walk f' g'), f' ≠ g' →
      ∃ e ∈ (zdGraph 2).edgeSet, (∀ x ∈ e, x ∈ Icc lo hi) ∧ f' ∈ dualEdge e := by
    intro f' g' τ hne'
    cases τ with
    | nil => exact absurd rfl hne'
    | cons hadj _ =>
      obtain ⟨e, he, heR, hee⟩ := hD₃ _ ((openGraph_adj_iff _ _ _).1 hadj).1
      exact ⟨e, he, heR, hee ▸ Sym2.mem_mk_left _ _⟩
  obtain ⟨ef, hef, hefR, hfef⟩ := hend σ hfg
  obtain ⟨eg, heg, hegR, hgeg⟩ := hend σ.reverse hfg.symm
  obtain ⟨y₁, y₂, hy₁, hy₂, rfl, hy₁₂⟩ :=
    exists_perimeterPos_eq_add_one_of_mem_dualEdge h₀ h₁ hef hefR hf hfef
  obtain ⟨z₁, z₂, hz₁, hz₂, rfl, hz₁₂⟩ :=
    exists_perimeterPos_eq_add_one_of_mem_dualEdge h₀ h₁ heg hegR hg hgeg
  have hyy : perimeterPos lo hi y = perimeterPos lo hi y₁ ∨
      perimeterPos lo hi y = perimeterPos lo hi y₂ := by
    rcases eq_or_eq_of_notMem_Icc h₀ h₁ hf hy hy₁ hy₂ ((SimpleGraph.mem_edgeSet _).1 hef).ne hyf
      (mem_Icc_of_mem_dualEdge hef (Sym2.mem_mk_left _ _) hfef)
      (mem_Icc_of_mem_dualEdge hef (Sym2.mem_mk_right _ _) hfef) with h | h <;> rw [h] <;> simp
  have hzz : perimeterPos lo hi z = perimeterPos lo hi z₁ ∨
      perimeterPos lo hi z = perimeterPos lo hi z₂ := by
    rcases eq_or_eq_of_notMem_Icc h₀ h₁ hg hz hz₁ hz₂ ((SimpleGraph.mem_edgeSet _).1 heg).ne hzg
      (mem_Icc_of_mem_dualEdge heg (Sym2.mem_mk_left _ _) hgeg)
      (mem_Icc_of_mem_dualEdge heg (Sym2.mem_mk_right _ _) hgeg) with h | h <;> rw [h] <;> simp
  have py₁ := hpos y₁ hy₁
  have py₂ := hpos y₂ hy₂
  have pz₁ := hpos z₁ hz₁
  have pz₂ := hpos z₂ hz₂
  -- the crossing counts and the parity function
  obtain ⟨X, hX⟩ : ∃ X : Sym2 (LatticeSite 2) → ZMod 2, ∀ e, X e =
      (σ.darts.map fun δ => if s(δ.fst, δ.snd) = dualEdge e then 1 else 0).sum :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : LatticeSite 2 → ZMod 2, ∀ w, N w =
      ∑ x ∈ Finset.Ico (lo 0) (w 0), X s(![x, w 1], ![x + 1, w 1]) +
        ∑ y ∈ Finset.Ico (lo 1) (w 1), X s(![lo 0, y], ![lo 0, y + 1]) :=
    ⟨_, fun _ => rfl⟩
  have huvN := eq_of_mem_localConn hD₁ hD₂ σ hf hg hX hN huv
  -- along the boundary, `N` changes only at the two edges where the walk leaves the box
  have hstep : ∀ v' w', v' ∈ boxBoundary lo hi → w' ∈ boxBoundary lo hi →
      perimeterPos lo hi w' = perimeterPos lo hi v' + 1 →
      N w' = N v' + ((if perimeterPos lo hi v' = perimeterPos lo hi y₁ then 1 else 0) +
        (if perimeterPos lo hi v' = perimeterPos lo hi z₁ then 1 else 0)) := by
    intro v' w' hv' hw' hp
    have hlt := (hpos w' hw').2
    obtain ⟨v'', w'', h, hv'', hpv'', hw'', hpw'', hh, hv''h, hw''h, -⟩ :=
      exists_notMem_Icc_of_perimeterPos h₀ h₁ (hpos v' hv').1 (p := perimeterPos lo hi v')
        (by omega)
    have e₁ : v'' = v' := perimeterPos_injOn lo hi hv'' hv' (by omega)
    have e₂ : w'' = w' := perimeterPos_injOn lo hi hw'' hw' (by omega)
    subst e₁ e₂
    have hvw : v'' ≠ w'' := fun h => by
      rw [h] at hp
      omega
    obtain ⟨hE, hhE⟩ := mem_edgeSet_and_mem_dualEdge_of_notMem_Icc hv''.1 hw''.1 hvw hh hv''h hw''h
    have hER : ∀ x ∈ s(v'', w''), x ∈ Icc lo hi := by
      intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      exacts [hv''.1, hw''.1]
    rw [eq_add_of_mem_edgeSet hD₁ σ hf hg hX hN hv''.1 hw''.1 hE, hX,
      sum_map_ite_eq_add_of_notMem_Icc h₀ h₁ hD₃ σ hf hg hE hER hh hhE]
    congr 2
    · exact if_congr (mem_dualEdge_iff_perimeterPos_eq h₀ h₁ hf hy₁ hy₂ hef hfef hy₁₂ hv'' hw''
        hE hp) rfl rfl
    · exact if_congr (mem_dualEdge_iff_perimeterPos_eq h₀ h₁ hg hz₁ hz₂ heg hgeg hz₁₂ hv'' hw''
        hE hp) rfl rfl
  -- the contradiction
  have k₁ : ∀ p : ZMod 2, p = p + (1 + 0) → False := by decide
  have k₂ : ∀ p : ZMod 2, p = p + (0 + 1) → False := by decide
  have htel := fun {v' w' : LatticeSite 2} (hv' : v' ∈ boxBoundary lo hi)
      (hw' : w' ∈ boxBoundary lo hi) (hle : perimeterPos lo hi v' ≤ perimeterPos lo hi w') =>
    eq_add_sum_of_perimeterPos (T := fun i =>
      (if i = perimeterPos lo hi y₁ then (1 : ZMod 2) else 0) +
        (if i = perimeterPos lo hi z₁ then 1 else 0)) h₀ h₁ hstep hv' hw' hle
  rcases lt_trichotomy (perimeterPos lo hi u) (perimeterPos lo hi v) with hlt | heq | hgt
  · have h := htel hu hv hlt.le
    rw [← huvN, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
    simp only [Finset.mem_Ico] at h
    split_ifs at h with c₁ c₂ c₂
    · omega
    · exact k₁ _ h
    · exact k₂ _ h
    · omega
  · omega
  · have h := htel hv hu hgt.le
    rw [huvN, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
    simp only [Finset.mem_Ico] at h
    split_ifs at h with c₁ c₂ c₂
    · omega
    · exact k₁ _ h
    · exact k₂ _ h
    · omega

/-- **Quad duality.** Let `R = Icc lo hi` be a box of `ℤ²` of positive width and height, with
perimeter `P = 2 (hi₀ - lo₀) + 2 (hi₁ - lo₁)`, and let `a < c < b < d < P + a`. Reading perimeter
positions modulo `P`, the boundary of `R` splits into the arcs `A = [a, c)`, `C = [c, b)`,
`B = [b, d)` and `D = [d, P + a)`. Exactly one holds: an open path inside `R` joins `A` to `B`,
or a dual-open path in the dual box `Icc (lo - 1) hi`, crossing only edges of `R`, joins the dual
arc of `C` to the dual arc of `D` (the faces not inside `R` with a corner in the arc). -/
theorem mem_arcCrossing_iff_dualConfig_notMem_arcCrossing {lo hi : LatticeSite 2}
    (h₀ : lo 0 < hi 0) (h₁ : lo 1 < hi 1) {a c b d : ℤ}
    (hacbd : a < c ∧ c < b ∧ b < d ∧ d < 2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)
    (ω : Config (LatticeSite 2)) :
    (∃ u v, u ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi u + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico a c) ∧
      v ∈ boxBoundary lo hi ∧
      (∃ k : ℤ, perimeterPos lo hi v + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico b d) ∧
      ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc lo hi) u v) ↔
    ¬ ∃ f g, (f ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc f (f + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈ Ico c b) ∧
      (g ∉ Icc lo (hi - 1) ∧ ∃ x ∈ boxBoundary lo hi, x ∈ Icc g (g + 1) ∧
        ∃ k : ℤ, perimeterPos lo hi x + k * (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1)) ∈
          Ico d (2 * (hi 0 - lo 0) + 2 * (hi 1 - lo 1) + a)) ∧
      dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧ ∀ x ∈ e, x ∈ Icc lo hi} ∈
        localConn (Icc (lo - 1) hi) f g :=
  ⟨not_exists_dualConfig_inter_mem_localConn_of_exists h₀ h₁ hacbd, fun h => by
    by_contra hn
    exact h (exists_dualConfig_inter_mem_localConn_of_not_exists h₀ h₁ hacbd hn)⟩

end PercLib.Models.Planar
