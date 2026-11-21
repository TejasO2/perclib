/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs, written on 2026-11-16. Statements from the wiki article `multipoint-trees` (tags CS13,
9YE6); T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.2. No upstream
proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.Multipoint.Geometry

/-!
# The sweep product: positivity, monotonicity and scaling; the three-point distance

For a finite set `A` in a metric space, `sweepProduct A` is the minimum over rooted trees on
`A` of `∏_{x ∈ A} diam(A_x)` (CS13). As the wiki article says, the three properties hold for
every tree before the minimum is taken.

* `sweepProduct_pos` (item 1): `0 < Sweep(A)` when `|A| ≥ 2`;
* `pow_card_mul_sweepProduct_le_image` (item 2 with a factor): if `f` is injective on `A` and
  `c d(x, y) ≤ d(f x, f y)` on `A` with `c ≥ 0`, then `c^|A| Sweep(A) ≤ Sweep(f A)`;
  `sweepProduct_le_image` is `c = 1`;
* `sweepProduct_image_smul` (item 3): `Sweep(c • A) = c^|A| Sweep(A)` for `c > 0` in a
  normed space;
* `threePartDistance_triple` (item 4, 9YE6): `S({x, y, z}) = d(x, y) d(y, z) d(z, x)` for
  distinct points.
-/

@[expose] public section

noncomputable section

open Finset

namespace PercLib.Percolation.Bond

variable {X : Type*} [MetricSpace X] [DecidableEq X]

/-! ### Rooted trees and their products -/

omit [MetricSpace X] in
open Classical in
/-- The star tree at `r` (every vertex has parent `r`) is a rooted tree. -/
theorem star_mem_rootedTrees {A : Finset X} (r : A) :
    (r, fun _ : A => r) ∈ (Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x, ∃ n, t.2^[n] x = t.1 :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, fun _ => ⟨1, rfl⟩⟩

open Classical in
/-- The sweep product is at most the product of any rooted tree. -/
theorem sweepProduct_le {A : Finset X} {t : A × (A → A)} (ht : t.2 t.1 = t.1)
    (hr : ∀ x, ∃ n, t.2^[n] x = t.1) :
    sweepProduct A ≤ ∏ x : A, Metric.diam (if x = t.1 then (A : Set X)
      else insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x})) := by
  have hmem : t ∈ (Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x, ∃ n, t.2^[n] x = t.1 := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht, hr⟩
  rw [sweepProduct, dite_eq_left_of_eq_true (eq_true ⟨t, hmem⟩)]
  exact Finset.inf'_le _ hmem

open Classical in
/-- The sweep product of a nonempty set is the minimum of the tree products. -/
theorem le_sweepProduct {A : Finset X} (hA : A.Nonempty) {m : ℝ}
    (hm : ∀ t : A × (A → A), t.2 t.1 = t.1 → (∀ x, ∃ n, t.2^[n] x = t.1) →
      m ≤ ∏ x : A, Metric.diam (if x = t.1 then (A : Set X)
        else insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x}))) :
    m ≤ sweepProduct A := by
  obtain ⟨a, ha⟩ := hA
  have hne : ((Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x, ∃ n, t.2^[n] x = t.1).Nonempty := ⟨_, star_mem_rootedTrees ⟨a, ha⟩⟩
  rw [sweepProduct, dite_eq_left_of_eq_true (eq_true hne)]
  refine Finset.le_inf' _ _ fun t ht => ?_
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ht
  exact hm t h1 h2

/-- The sweep product is nonnegative. -/
theorem sweepProduct_nonneg (A : Finset X) : 0 ≤ sweepProduct A := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · classical
    rw [sweepProduct]
    split_ifs with h
    · obtain ⟨t, -⟩ := h
      exact absurd t.1.2 (Finset.notMem_empty _)
    · exact le_rfl
  · exact le_sweepProduct hA fun t _ _ => Finset.prod_nonneg fun x _ => Metric.diam_nonneg

/-! ### Item 1: positivity -/

/-- **Item 1.** `Sweep(A) > 0` when `|A| ≥ 2`. -/
theorem sweepProduct_pos {A : Finset X} (hA : 2 ≤ A.card) : 0 < sweepProduct A := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < A.card)
  have hdiamA : 0 < Metric.diam (A : Set X) :=
    lt_of_lt_of_le (dist_pos.2 hab)
      (Metric.dist_le_diam_of_mem (A.finite_toSet.isBounded) ha hb)
  -- every tree product is at least the (positive) minimum of its factors
  set m := ((Finset.univ : Finset (A × (A → A))).filter fun t =>
      t.2 t.1 = t.1 ∧ ∀ x, ∃ n, t.2^[n] x = t.1) with hm_def
  have hne : m.Nonempty := ⟨_, star_mem_rootedTrees ⟨a, ha⟩⟩
  rw [sweepProduct, dite_eq_left_of_eq_true (eq_true hne), Finset.lt_inf'_iff]
  intro t ht
  obtain ⟨-, hroot, hreach⟩ := Finset.mem_filter.1 ht
  refine Finset.prod_pos fun x _ => ?_
  split_ifs with hx
  · exact hdiamA
  · have hpx : t.2 x ≠ x := by
      intro hfix
      obtain ⟨n, hn⟩ := hreach x
      exact hx (by rw [← hn, Function.iterate_fixed hfix])
    have hxmem : (x : X) ∈ insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x}) :=
      Set.mem_insert_of_mem _ ⟨x, ⟨0, rfl⟩, rfl⟩
    have hbdd : (insert (t.2 x : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x})).Finite :=
      (Set.toFinite _).insert _
    refine lt_of_lt_of_le (dist_pos.2 ?_)
      (Metric.dist_le_diam_of_mem hbdd.isBounded (Set.mem_insert _ _) hxmem)
    exact fun h => hpx (Subtype.ext h)

/-! ### Item 2: monotonicity -/

section Image

variable {Y : Type*} [MetricSpace Y] [DecidableEq Y]

omit [DecidableEq X] [DecidableEq Y] in
/-- `c diam(S) ≤ diam(f S)` for a finite `S` when `c d ≤ d ∘ f` on `S`, `c ≥ 0`. -/
theorem mul_diam_le_diam_image {f : X → Y} {c : ℝ} (hc : 0 ≤ c) {S : Set X} (hS : S.Finite)
    (hf : ∀ x ∈ S, ∀ y ∈ S, c * dist x y ≤ dist (f x) (f y)) :
    c * Metric.diam S ≤ Metric.diam (f '' S) := by
  rcases hc.eq_or_lt with rfl | hc'
  · rw [zero_mul]; exact Metric.diam_nonneg
  rw [← le_div_iff₀' hc']
  refine Metric.diam_le_of_forall_dist_le (div_nonneg Metric.diam_nonneg hc'.le) fun x hx y hy => ?_
  rw [le_div_iff₀' hc']
  exact (hf x hx y hy).trans (Metric.dist_le_diam_of_mem (hS.image f).isBounded
    (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

open Classical in
/-- **Item 2 with a factor.** If `f` is injective on `A` and `c d(x, y) ≤ d(f x, f y)` on `A`
with `c ≥ 0`, then `c^|A| Sweep(A) ≤ Sweep(f A)`. -/
theorem pow_card_mul_sweepProduct_le_image {f : X → Y} {c : ℝ} (hc : 0 ≤ c) {A : Finset X}
    (hinj : Set.InjOn f A) (hf : ∀ x ∈ A, ∀ y ∈ A, c * dist x y ≤ dist (f x) (f y)) :
    c ^ A.card * sweepProduct A ≤ sweepProduct (A.image f) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [card_empty, pow_zero, one_mul, image_empty]
    exact le_rfl
  -- the bijection `A ≃ f A`
  set e : A ≃ (A.image f : Finset Y) := Equiv.ofBijective
    (fun a => ⟨f a, Finset.mem_image_of_mem f a.2⟩) ⟨fun a b h => Subtype.ext (hinj a.2 b.2
      (congrArg Subtype.val h)), fun b => by
        obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩ with he_def
  have he : ∀ a : A, ((e a : Y)) = f a := fun a => rfl
  refine le_sweepProduct (hA.image f) fun t' hroot hreach => ?_
  -- the pulled-back tree
  set t : A × (A → A) := (e.symm t'.1, fun x => e.symm (t'.2 (e x))) with ht_def
  have hiter : ∀ n (x : A), t.2^[n] x = e.symm (t'.2^[n] (e x)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [ht_def]
  have htroot : t.2 t.1 = t.1 := by simp [ht_def, hroot]
  have htreach : ∀ x, ∃ n, t.2^[n] x = t.1 := by
    intro x
    obtain ⟨n, hn⟩ := hreach (e x)
    exact ⟨n, by rw [hiter, hn]⟩
  refine le_trans (mul_le_mul_of_nonneg_left (sweepProduct_le htroot htreach)
    (pow_nonneg hc _)) ?_
  have hcardA : A.card = (Finset.univ : Finset A).card := by simp
  rw [hcardA, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← e.prod_comp]
  refine Finset.prod_le_prod₀ (fun x _ => mul_nonneg hc Metric.diam_nonneg) fun x _ => ?_
  -- the factor at `x` and at `e x`
  have hdesc : ((↑) '' {y' : (A.image f : Finset Y) | ∃ n, t'.2^[n] y' = e x} : Set Y) =
      f '' ((↑) '' {y : A | ∃ n, t.2^[n] y = x}) := by
    ext z
    constructor
    · rintro ⟨y', ⟨n, hn⟩, rfl⟩
      refine ⟨e.symm y', ⟨⟨e.symm y', ⟨n, ?_⟩, rfl⟩, ?_⟩⟩
      · rw [hiter, e.apply_symm_apply, hn, e.symm_apply_apply]
      · rw [← he, e.apply_symm_apply]
    · rintro ⟨_, ⟨y, ⟨n, hn⟩, rfl⟩, rfl⟩
      refine ⟨e y, ⟨n, ?_⟩, he y⟩
      rw [hiter] at hn
      rw [← e.apply_symm_apply (t'.2^[n] (e y)), hn]
  have hfin : ∀ S : Set A, ((↑) '' S : Set X).Finite := fun S => (Set.toFinite S).image _
  have hsub : ∀ S : Set A, ∀ x ∈ ((↑) '' S : Set X), x ∈ (A : Set X) := by
    rintro S _ ⟨y, -, rfl⟩
    exact y.2
  by_cases hx : x = t.1
  · have hx' : e x = t'.1 := by rw [hx, ht_def]; simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true hx), ite_eq_left_of_eq_true _ _ (eq_true hx')]
    have h := mul_diam_le_diam_image hc A.finite_toSet hf
    rwa [← Finset.coe_image] at h
  · have hx' : e x ≠ t'.1 := fun h => hx (by rw [ht_def]; simp [← h])
    rw [ite_eq_right_of_eq_false _ _ (eq_false hx), ite_eq_right_of_eq_false _ _ (eq_false hx'),
      hdesc]
    have hpar : ((t'.2 (e x) : (A.image f : Finset Y)) : Y) = f (t.2 x) := by
      rw [← he]; simp [ht_def]
    rw [hpar]
    set S : Set X := insert ((t.2 x : A) : X) ((↑) '' {y : A | ∃ n, t.2^[n] y = x}) with hS_def
    have hSA : ∀ u ∈ S, u ∈ A := by
      intro u hu
      rcases hu with rfl | hu
      · exact (t.2 x).2
      · exact hsub _ u hu
    have key := mul_diam_le_diam_image (S := S) hc ((hfin _).insert _)
      fun u hu v hv => hf u (hSA u hu) v (hSA v hv)
    rwa [hS_def, Set.image_insert_eq] at key

/-- **Item 2.** An expanding map injective on `A` does not decrease the sweep product. -/
theorem sweepProduct_le_image {f : X → Y} {A : Finset X} (hinj : Set.InjOn f A)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist (f x) (f y)) :
    sweepProduct A ≤ sweepProduct (A.image f) := by
  simpa using pow_card_mul_sweepProduct_le_image (f := f) zero_le_one hinj
    fun x hx y hy => by rw [one_mul]; exact hf x hx y hy

end Image

/-! ### Item 3: scaling -/

/-- **Item 3.** In a normed space, `Sweep(c • A) = c^|A| Sweep(A)` for `c > 0`. -/
theorem sweepProduct_image_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] {c : ℝ} (hc : 0 < c) (A : Finset E) :
    sweepProduct (A.image (c • ·)) = c ^ A.card * sweepProduct A := by
  have hinj : ∀ (B : Finset E) (a : ℝ), a ≠ 0 → Set.InjOn (a • · : E → E) B :=
    fun _ a ha x _ y _ h => smul_right_injective E ha h
  have hd : ∀ (a : ℝ), 0 < a → ∀ x y : E, a * dist x y ≤ dist (a • x) (a • y) :=
    fun a ha x y => by rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ha]
  refine le_antisymm ?_ (pow_card_mul_sweepProduct_le_image hc.le (hinj A c hc.ne')
    fun x _ y _ => hd c hc x y)
  have h := pow_card_mul_sweepProduct_le_image (inv_pos.2 hc).le
    (hinj (A.image (c • ·)) _ (inv_ne_zero hc.ne')) fun x _ y _ => hd _ (inv_pos.2 hc) x y
  rw [image_image, card_image_of_injOn (hinj A c hc.ne')] at h
  have hid : ((c⁻¹ • ·) ∘ (c • ·) : E → E) = id := by
    funext x; simp [smul_smul, inv_mul_cancel₀ hc.ne']
  rw [hid, image_id] at h
  have hpos : 0 < c ^ A.card := pow_pos hc _
  rw [inv_pow] at h
  calc sweepProduct (A.image (c • ·))
      = c ^ A.card * ((c ^ A.card)⁻¹ * sweepProduct (A.image (c • ·))) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ c ^ A.card * sweepProduct A := mul_le_mul_of_nonneg_left h hpos.le

/-! ### Item 4: three points -/

/-- **Item 4 (9YE6), three points.** `S({x, y, z}) = d(x, y) d(y, z) d(z, x)` for distinct
`x, y, z`. -/
theorem threePartDistance_triple {x y z : X} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    threePartDistance ({x, y, z} : Finset X) = dist x y * dist y z * dist z x := by
  set A : Finset X := {x, y, z} with hA_def
  have hcard : A.card = 3 := by
    rw [hA_def, card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  obtain ⟨p₁, p₂, h₁, h₂, hd, hn₁, hn₂, hn₃, heq⟩ := exists_threePartDistance_eq (A := A)
    (by omega)
  rw [heq]
  obtain ⟨-, -, -, hsum⟩ := card_partition_parts h₁ h₂ hd
  have c₁ : p₁.card = 1 := by
    have := hn₂.card_pos; have := hn₃.card_pos; have := hn₁.card_pos; omega
  have c₂ : p₂.card = 1 := by
    have := hn₂.card_pos; have := hn₃.card_pos; have := hn₁.card_pos; omega
  have c₃ : (A \ (p₁ ∪ p₂)).card = 1 := by
    have := hn₂.card_pos; have := hn₃.card_pos; have := hn₁.card_pos; omega
  obtain ⟨a, rfl⟩ := card_eq_one.1 c₁
  obtain ⟨b, rfl⟩ := card_eq_one.1 c₂
  obtain ⟨c, hc⟩ := card_eq_one.1 c₃
  rw [hc]
  have hab : a ≠ b := fun h => (disjoint_singleton.1 hd) h
  have hcmem : c ∈ A \ ({a} ∪ {b}) := by rw [hc]; exact mem_singleton_self c
  have hca : c ≠ a := fun h => (mem_sdiff.1 hcmem).2 (by simp [h])
  have hcb : c ≠ b := fun h => (mem_sdiff.1 hcmem).2 (by simp [h])
  have ha : a ∈ A := h₁ (mem_singleton_self a)
  have hb : b ∈ A := h₂ (mem_singleton_self b)
  have hcA : c ∈ A := (mem_sdiff.1 hcmem).1
  rw [show ({a} : Finset X) ∪ {b} = {a, b} from rfl, show ({b} : Finset X) ∪ {c} = {b, c} from rfl,
    show ({c} : Finset X) ∪ {a} = {c, a} from rfl, threePartDistance_pair, threePartDistance_pair,
    threePartDistance_pair, ← mul_pow, ← mul_pow,
    Real.sqrt_sq (by positivity)]
  simp only [hA_def, mem_insert, mem_singleton] at ha hb hcA
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hcA with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl hca
    | exact absurd rfl hcb
    | ring1
    | (rw [dist_comm a b, dist_comm b c, dist_comm c a]; ring1)

/-! ### Witnesses -/

/-- `A = {0, 1, 3} ⊆ ℝ`: `Sweep(A) > 0`, `Sweep(2 • A) = 2³ Sweep(A)`, and
`S(A) = 1 · 2 · 3 = 6`. -/
example : 0 < sweepProduct ({0, 1, 3} : Finset ℝ) :=
  sweepProduct_pos (by
    rw [card_insert_of_notMem (by norm_num), card_pair (by norm_num)]; norm_num)

example : sweepProduct (({0, 1, 3} : Finset ℝ).image ((2 : ℝ) • ·)) =
    2 ^ 3 * sweepProduct ({0, 1, 3} : Finset ℝ) := by
  rw [sweepProduct_image_smul two_pos, card_insert_of_notMem (by norm_num),
    card_pair (by norm_num)]

example : threePartDistance ({0, 1, 3} : Finset ℝ) = 6 := by
  rw [threePartDistance_triple (by norm_num) (by norm_num) (by norm_num)]
  simp only [Real.dist_eq]
  norm_num

end PercLib.Percolation.Bond
