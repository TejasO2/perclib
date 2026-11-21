/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: B. Bollobás and O. Riordan, A short proof of the Harris-Kesten theorem,
Bull. London Math. Soc. 38 (2006), 470-484 (arXiv math/0410359v3), Corollary 7.
-/
module

public import PercLib.Models.Planar.RSWKeyStep
public import PercLib.Probability.Harris

/-!
# The Russo–Seymour–Welsh estimate on `ℤ²`

At the self-dual point, where every edge of `ℤ²` is open with probability `1/2`, boxes of any
fixed aspect ratio are crossed in the long direction with probability bounded below uniformly in
their size.

* **Doubling** (`law_crossing_zero_sq_mul_pow_three_le`, `law_crossing_zero_sq_le`). For
  `1 ≤ n ≤ m`, write `H(w)` for a left-right crossing of `[0, w] × [0, 2n]` and `S = [0, n]²`.
  For every profile constant on the edges, `P(H(m))² P(H(S))³ ≤ 4 P(H(2m - n))`; at `1/2`,
  `P(H(m))² ≤ 2⁵ P(H(2m - n))`. The event `X(R)` of the key step
  (`law_crossing_zero_mul_law_crossing_one_le`), its reflection in the line `x = n/2` and `H(S)`
  together give a left-right crossing of `[n - m, m] × [0, 2n]`, by the gluing lemma of
  `Gluing.lean` in `S`; Harris's inequality and the key step give the bound. This is
  Corollary 7 of Bollobás and Riordan.
* **Iteration** (`le_law_crossing_zero_two_pow_add_one_mul`). Along the widths
  `(2^j + 1) n`, the doubling gives `P(H((2^j + 1) n)) ≥ 2⁵ · 2^(-6 · 2^j)`.
* **RSW** (`exists_pos_le_law_crossing_zero`). For each `k ≥ 2` there is `c_k > 0` with
  `P([0, 2kn] × [0, 2n] has an open left-right crossing) ≥ c_k` for every `n ≥ 1`.
* **Any position and direction** (`exists_pos_le_law_crossing`). The same for the `kn × n`
  box at any corner, crossed in its long direction, for every `k`, by translation, the
  coordinate swap and, for `n = 1`, a row of open edges (`inv_two_pow_le_law_crossing_zero`).

## Main results

* `PercLib.Models.Planar.law_crossing_zero_sq_le`
* `PercLib.Models.Planar.le_law_crossing_zero_two_pow_add_one_mul`
* `PercLib.Models.Planar.exists_pos_le_law_crossing_zero`
* `PercLib.Models.Planar.exists_pos_le_law_crossing`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Crossings of nearly square boxes and of rows -/

/-- At the self-dual point, a box whose width exceeds its height by at most one is crossed from
left to right with probability at least `1/2`. -/
theorem one_half_le_law_crossing_zero {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {lo hi : LatticeSite 2} (hle : lo ≤ hi)
    (hw : hi 0 - lo 0 ≤ hi 1 - lo 1 + 1) :
    1 / 2 ≤ law q (crossing 0 lo hi) := by
  have h0 : lo 0 ≤ hi 0 := hle 0
  have h1 : lo 1 ≤ hi 1 := hle 1
  have hn : (((hi 1 - lo 1).toNat : ℕ) : ℤ) = hi 1 - lo 1 := Int.toNat_of_nonneg (by omega)
  refine (law_crossing_zero_eq_half lo (hi 1 - lo 1).toNat hq).symm.le.trans
    (measure_mono (crossing_zero_subset_crossing_zero le_rfl h0 ?_ le_rfl ?_))
  · simp only [Pi.add_apply, Matrix.cons_val_zero]
    omega
  · simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- At the self-dual point, a row of `k` edges, the box `[0, k] × [0, 0]`, is crossed from left
to right with probability at least `2^(-k)`. -/
theorem inv_two_pow_le_law_crossing_zero {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) (k : ℕ) :
    2⁻¹ ^ k ≤ law q (crossing 0 0 ![(k : ℤ), 0]) := by
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q e = ⟨1 / 2, by norm_num, by norm_num⟩ :=
    fun e he => Subtype.ext (hq e he)
  induction k with
  | zero =>
    have hle : (0 : LatticeSite 2) ≤ ![((0 : ℕ) : ℤ), 0] :=
      Pi.le_def.2 fun i => by fin_cases i <;> simp
    rw [pow_zero, crossing_eq_univ_of_eq hle (by simp), measure_univ]
  | succ k ih =>
    -- a single edge is open with probability `1/2`
    have hedge : law q (crossing 0 ![(k : ℤ), 0] ![(k : ℤ) + 1, 0]) = 2⁻¹ := by
      have h₁ := law_crossing_zero_eq_half 0 0 hq
      have h₂ := law_crossing_add hq' 0 0 (0 + ![((0 : ℕ) : ℤ) + 1, ((0 : ℕ) : ℤ)])
        ![(k : ℤ), 0]
      rw [h₁, one_div] at h₂
      rw [← h₂]
      congr 2
      · rw [zero_add]
      · ext i
        fin_cases i
        · simp
          ring
        · simp
    -- the row of `k` edges and the next edge make the row of `k + 1` edges
    have hglue : crossing 0 0 ![(k : ℤ), 0] ∩ crossing 0 ![(k : ℤ), 0] ![(k : ℤ) + 1, 0] ⊆
        crossing 0 0 ![((k + 1 : ℕ) : ℤ), 0] := by
      rintro ω ⟨⟨a, ha, ha0, b, hb, hb0, hab⟩, ⟨a', ha', ha'0, b', hb', hb'0, hab'⟩⟩
      have hb1 : b 1 = a' 1 := by
        rw [mem_Icc_two_iff] at hb ha'
        simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hb ha'
        omega
      have hba : b = a' := by
        ext i
        fin_cases i
        exacts [hb0.trans ha'0.symm, hb1]
      subst hba
      have hsub₁ : Icc (0 : LatticeSite 2) ![(k : ℤ), 0] ⊆
          Icc (0 : LatticeSite 2) ![((k + 1 : ℕ) : ℤ), 0] := by
        intro v hv
        rw [mem_Icc_two_iff] at hv ⊢
        simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
        omega
      have hsub₂ : Icc (![(k : ℤ), 0] : LatticeSite 2) ![(k : ℤ) + 1, 0] ⊆
          Icc (0 : LatticeSite 2) ![((k + 1 : ℕ) : ℤ), 0] := by
        intro v hv
        rw [mem_Icc_two_iff] at hv ⊢
        simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
        omega
      refine ⟨a, hsub₁ ha, ha0, b', hsub₂ hb', ?_,
        localConn_trans (localConn_mono_set hsub₁ _ _ hab) (localConn_mono_set hsub₂ _ _ hab')⟩
      simp only [Matrix.cons_val_zero] at hb'0 ⊢
      omega
    calc (2⁻¹ : ℝ≥0∞) ^ (k + 1) = 2⁻¹ ^ k * 2⁻¹ := pow_succ _ _
      _ ≤ law q (crossing 0 0 ![(k : ℤ), 0]) *
          law q (crossing 0 ![(k : ℤ), 0] ![(k : ℤ) + 1, 0]) := by
        rw [hedge]
        gcongr
      _ ≤ law q (crossing 0 0 ![(k : ℤ), 0] ∩ crossing 0 ![(k : ℤ), 0] ![(k : ℤ) + 1, 0]) :=
        prodBernoulli_harris q (isUpperSet_crossing _ _ _) (isUpperSet_crossing _ _ _)
          (measurableSet_crossing _ _ _) (measurableSet_crossing _ _ _)
      _ ≤ law q (crossing 0 0 ![((k + 1 : ℕ) : ℤ), 0]) := measure_mono hglue

/-! ### The doubling inequality -/

/-- **RSW doubling** (Bollobás–Riordan, Corollary 7), for every profile constant on the edges of
`ℤ²`. For `1 ≤ n ≤ m`, with `S = [0, n]²`,
`P(H([0, m] × [0, 2n]))² · P(H(S))³ ≤ 4 · P(H([0, 2m - n] × [0, 2n]))`, where `H` is a
left-right crossing. -/
theorem law_crossing_zero_sq_mul_pow_three_le {q : Sym2 (LatticeSite 2) → unitInterval}
    {p : unitInterval} (hq : ∀ e ∈ (zdGraph 2).edgeSet, q e = p) {n m : ℕ} (hn : 1 ≤ n)
    (hnm : n ≤ m) :
    law q (crossing 0 0 ![(m : ℤ), 2 * n]) ^ 2 * law q (crossing 0 0 ![(n : ℤ), n]) ^ 3 ≤
      4 * law q (crossing 0 0 ![2 * (m : ℤ) - n, 2 * n]) := by
  have hkey := law_crossing_zero_mul_law_crossing_one_le hq hn hnm
  set X : Set (Config (LatticeSite 2)) := {ω | ∃ c ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n],
        (∃ a ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n], a 1 = 0 ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc 0 ![(n : ℤ), n]) a c) ∧
        (∃ b ∈ Icc (0 : LatticeSite 2) ![(n : ℤ), n], b 1 = n ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc 0 ![(n : ℤ), n]) c b) ∧
        (∃ r ∈ Icc (0 : LatticeSite 2) ![(m : ℤ), 2 * n], r 0 = m ∧
          ω ∩ (zdGraph 2).edgeSet ∈ localConn (Icc 0 ![(m : ℤ), 2 * n]) c r)} with hX
  -- a bottom-top crossing of the square has the probability of a left-right one
  have hVH : law q (crossing 1 0 ![(n : ℤ), n]) = law q (crossing 0 0 ![(n : ℤ), n]) := by
    rw [law_crossing_one_eq_law_crossing_zero hq]
    congr 2
    ext i
    fin_cases i <;> rfl
  rw [hVH] at hkey
  -- the event `X` is measurable, increasing and depends only on the edges of `ℤ²`
  have hconn : ∀ (T : Set (LatticeSite 2)) (x y : LatticeSite 2),
      Measurable fun ω : Config (LatticeSite 2) => ω ∩ (zdGraph 2).edgeSet ∈ localConn T x y :=
    fun T x y => measurableSet_setOfPred.1
      ((measurableSet_localConn T x y).preimage (by fun_prop))
  have hXm : MeasurableSet X := by
    rw [hX]
    exact measurableSet_setOfPred.2 (Measurable.exists fun c => measurable_const.and
      ((Measurable.exists fun a => measurable_const.and (measurable_const.and (hconn _ _ _))).and
      ((Measurable.exists fun b => measurable_const.and (measurable_const.and (hconn _ _ _))).and
      (Measurable.exists fun r => measurable_const.and (measurable_const.and (hconn _ _ _))))))
  have hXu : IsUpperSet X := by
    intro ω ω' hωω' hω
    rw [hX] at hω ⊢
    obtain ⟨c, hc, ⟨a, ha, ha1, hac⟩, ⟨b, hb, hb1, hcb⟩, ⟨r, hr, hr0, hcr⟩⟩ := hω
    have hmono := inter_subset_inter_left (zdGraph 2).edgeSet hωω'
    exact ⟨c, hc, ⟨a, ha, ha1, localConn_mono hmono hac⟩, ⟨b, hb, hb1, localConn_mono hmono hcb⟩,
      ⟨r, hr, hr0, localConn_mono hmono hcr⟩⟩
  have hXL : ∀ ω, ω ∩ (zdGraph 2).edgeSet ∈ X ↔ ω ∈ X := by
    intro ω
    simp only [hX, mem_ofPred_eq, inter_assoc, inter_self]
  -- the reflection in the line `x = n/2`
  obtain ⟨σ, hσ⟩ := exists_iso_reflect_zero (n : ℤ)
  have hσσ : ∀ v, σ (σ v) = v := fun v => by
    rw [hσ, hσ, eq_comm, eq_vec_two_iff]
    simp
  have hinv : ∀ e, Sym2.map σ (Sym2.map σ e) = e := fun e => by
    rw [Sym2.map_map]
    have h : (⇑σ ∘ ⇑σ : LatticeSite 2 → LatticeSite 2) = id := funext hσσ
    rw [h, Sym2.map_id, id]
  have hqσ : ∀ e ∈ (zdGraph 2).edgeSet, q (Sym2.map σ e) = q e := fun e he => by
    rw [hq e he, hq _ ((image_sym2Map_edgeSet σ).subset (mem_image_of_mem _ he))]
  set Y : Set (Config (LatticeSite 2)) := (fun ω => Sym2.map σ '' ω) ⁻¹' X with hY
  have hYlaw : law q Y = law q X := law_preimage_image_sym2Map_eq σ hqσ hXm hXL
  have hYm : MeasurableSet Y := hXm.preimage (measurable_image_sym2Map σ.toEquiv)
  have hYu : IsUpperSet Y := fun ω ω' h hω => hXu (image_mono h) hω
  -- a connection of the reflected configuration is the reflection of a connection
  have htr : ∀ (ω : Config (LatticeSite 2)) (T : Set (LatticeSite 2)) (x y : LatticeSite 2),
      Sym2.map σ '' ω ∩ (zdGraph 2).edgeSet ∈ localConn T x y →
        ω ∩ (zdGraph 2).edgeSet ∈ localConn (σ '' T) (σ x) (σ y) := by
    intro ω T x y h
    have hback : Sym2.map σ '' (Sym2.map σ '' ω ∩ (zdGraph 2).edgeSet) =
        ω ∩ (zdGraph 2).edgeSet := by
      rw [image_inter (Sym2.map.injective σ.injective), image_sym2Map_edgeSet σ, image_image]
      simp only [hinv, image_id']
    rw [← hback]
    exact (image_mem_localConn_iff σ.toEquiv _ T x y).2 h
  -- `X`, its reflection and a left-right crossing of the square glue to a long crossing
  have hsub : X ∩ Y ∩ crossing 0 0 ![(n : ℤ), n] ⊆
      crossing 0 ![(n : ℤ) - m, 0] ![(m : ℤ), 2 * n] := by
    rintro ω ⟨⟨hωX, hωY⟩, a₀, ha₀, ha₀0, b₀, hb₀, hb₀0, hab₀⟩
    rw [hX] at hωX
    rw [hY, mem_preimage, hX] at hωY
    obtain ⟨c, hc, ⟨a, ha, ha1, hac⟩, ⟨b, hb, hb1, hcb⟩, ⟨r, hr, hr0, hcr⟩⟩ := hωX
    obtain ⟨c', hc', ⟨a', ha', ha'1, hac'⟩, ⟨b', hb', hb'1, hcb'⟩, ⟨r', hr', hr'0, hcr'⟩⟩ := hωY
    have hσS : σ '' Icc (0 : LatticeSite 2) ![(n : ℤ), n] ⊆ Icc 0 ![(n : ℤ), n] := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hσ]
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
      omega
    have hSB : Icc (0 : LatticeSite 2) ![(n : ℤ), n] ⊆
        Icc ![(n : ℤ) - m, 0] ![(m : ℤ), 2 * n] := by
      intro v hv
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
      omega
    have hRB : Icc (0 : LatticeSite 2) ![(m : ℤ), 2 * n] ⊆
        Icc ![(n : ℤ) - m, 0] ![(m : ℤ), 2 * n] := by
      intro v hv
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
      omega
    have hσRB : σ '' Icc (0 : LatticeSite 2) ![(m : ℤ), 2 * n] ⊆
        Icc ![(n : ℤ) - m, 0] ![(m : ℤ), 2 * n] := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hσ]
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv ⊢
      omega
    have h1 : (0 : LatticeSite 2) 1 < (![(n : ℤ), n] : LatticeSite 2) 1 := by
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    -- the left-right crossing of the square meets the vertical crossing through `c`
    have h₁ := inter_edgeSet_mem_localConn_of_crossings h1 hab₀ (localConn_trans hac hcb) ha₀0
      hb₀0 ha1 hb1
    -- and the reflected vertical crossing through `σ c'`
    have hac'' := localConn_mono_set hσS _ _ (htr ω _ a' c' hac')
    have hcb'' := localConn_mono_set hσS _ _ (htr ω _ c' b' hcb')
    have hσa' : (σ a') 1 = (0 : LatticeSite 2) 1 := by
      rw [hσ]
      simpa using ha'1
    have hσb' : (σ b') 1 = (![(n : ℤ), n] : LatticeSite 2) 1 := by
      rw [hσ]
      simpa using hb'1
    have h₂ := inter_edgeSet_mem_localConn_of_crossings h1 hab₀ (localConn_trans hac'' hcb'')
      ha₀0 hb₀0 hσa' hσb'
    have hcr'' := localConn_mono_set hσRB _ _ (htr ω _ c' r' hcr')
    rw [localConn_comm] at hcr''
    have h₂c := localConn_mono_set hSB _ _ (localConn_trans h₂ hac'')
    rw [localConn_comm] at h₂c
    refine ⟨σ r', hσRB (mem_image_of_mem σ hr'), ?_, r, hRB hr, hr0,
      localConn_trans (localConn_trans hcr'' h₂c)
        (localConn_trans (localConn_mono_set hSB _ _ (localConn_trans h₁ hac))
          (localConn_mono_set hRB _ _ hcr))⟩
    rw [hσ]
    simp [hr'0]
  -- translation
  have htrans : law q (crossing 0 ![(n : ℤ) - m, 0] ![(m : ℤ), 2 * n]) =
      law q (crossing 0 0 ![2 * (m : ℤ) - n, 2 * n]) := by
    rw [← law_crossing_add hq 0 0 ![2 * (m : ℤ) - n, 2 * n] ![(n : ℤ) - m, 0]]
    congr 2
    · rw [zero_add]
    · rw [eq_comm, eq_vec_two_iff]
      constructor <;> simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        ring
  -- Harris's inequality for the three increasing events
  have hharris : law q X * law q Y * law q (crossing 0 0 ![(n : ℤ), n]) ≤
      law q (X ∩ Y ∩ crossing 0 0 ![(n : ℤ), n]) :=
    calc law q X * law q Y * law q (crossing 0 0 ![(n : ℤ), n])
        ≤ law q (X ∩ Y) * law q (crossing 0 0 ![(n : ℤ), n]) := by
          gcongr
          exact prodBernoulli_harris q hXu hYu hXm hYm
      _ ≤ law q (X ∩ Y ∩ crossing 0 0 ![(n : ℤ), n]) :=
          prodBernoulli_harris q (hXu.inter hYu) (isUpperSet_crossing _ _ _) (hXm.inter hYm)
            (measurableSet_crossing _ _ _)
  calc law q (crossing 0 0 ![(m : ℤ), 2 * n]) ^ 2 * law q (crossing 0 0 ![(n : ℤ), n]) ^ 3
      = (law q (crossing 0 0 ![(m : ℤ), 2 * n]) * law q (crossing 0 0 ![(n : ℤ), n])) *
          (law q (crossing 0 0 ![(m : ℤ), 2 * n]) * law q (crossing 0 0 ![(n : ℤ), n])) *
          law q (crossing 0 0 ![(n : ℤ), n]) := by ring
    _ ≤ (2 * law q X) * (2 * law q X) * law q (crossing 0 0 ![(n : ℤ), n]) := by gcongr
    _ = 4 * (law q X * law q Y * law q (crossing 0 0 ![(n : ℤ), n])) := by
        rw [hYlaw]
        ring
    _ ≤ 4 * law q (X ∩ Y ∩ crossing 0 0 ![(n : ℤ), n]) := by gcongr
    _ ≤ 4 * law q (crossing 0 ![(n : ℤ) - m, 0] ![(m : ℤ), 2 * n]) := by gcongr
    _ = 4 * law q (crossing 0 0 ![2 * (m : ℤ) - n, 2 * n]) := by rw [htrans]

/-- **RSW doubling** at the self-dual point (Bollobás–Riordan, Corollary 7). If every edge of
`ℤ²` is open with probability `1/2`, then for `1 ≤ n ≤ m`,
`P(H([0, m] × [0, 2n]))² ≤ 2⁵ · P(H([0, 2m - n] × [0, 2n]))`, where `H` is a left-right
crossing. -/
theorem law_crossing_zero_sq_le {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    law q (crossing 0 0 ![(m : ℤ), 2 * n]) ^ 2 ≤
      2 ^ 5 * law q (crossing 0 0 ![2 * (m : ℤ) - n, 2 * n]) := by
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q e = ⟨1 / 2, by norm_num, by norm_num⟩ :=
    fun e he => Subtype.ext (hq e he)
  have h := law_crossing_zero_sq_mul_pow_three_le hq' hn hnm
  have hle : (0 : LatticeSite 2) ≤ ![(n : ℤ), n] := Pi.le_def.2 fun i => by fin_cases i <;> simp
  have hs : 1 ≤ 2 * law q (crossing 0 0 ![(n : ℤ), n]) :=
    calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
          rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
      _ ≤ 2 * law q (crossing 0 0 ![(n : ℤ), n]) := by
          gcongr
          exact one_half_le_law_crossing_zero hq hle (by simp)
  calc law q (crossing 0 0 ![(m : ℤ), 2 * n]) ^ 2
      ≤ law q (crossing 0 0 ![(m : ℤ), 2 * n]) ^ 2 *
          (2 * law q (crossing 0 0 ![(n : ℤ), n])) ^ 3 := le_mul_of_one_le_right' (one_le_pow₀ hs)
    _ = 2 ^ 3 * (law q (crossing 0 0 ![(m : ℤ), 2 * n]) ^ 2 *
          law q (crossing 0 0 ![(n : ℤ), n]) ^ 3) := by ring
    _ ≤ 2 ^ 3 * (4 * law q (crossing 0 0 ![2 * (m : ℤ) - n, 2 * n])) := by gcongr
    _ = 2 ^ 5 * law q (crossing 0 0 ![2 * (m : ℤ) - n, 2 * n]) := by ring

/-! ### Iteration and RSW -/

/-- **Iteration of the doubling.** At the self-dual point, for every `n ≥ 1` and `j`, the box
`[0, (2^j + 1) n] × [0, 2n]` is crossed from left to right with probability at least
`2⁵ · 2^(-6 · 2^j)`. -/
theorem le_law_crossing_zero_two_pow_add_one_mul {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    2 ^ 5 * 2⁻¹ ^ (6 * 2 ^ j) ≤ law q (crossing 0 0 ![(2 ^ j + 1) * (n : ℤ), 2 * n]) := by
  induction j with
  | zero =>
    have h : (2 : ℝ≥0∞) ^ 5 * 2⁻¹ ^ (6 * 2 ^ 0) = 1 / 2 := by
      rw [show (2 : ℝ≥0∞) ^ 5 * 2⁻¹ ^ (6 * 2 ^ 0) = (2 * 2⁻¹) ^ 5 * 2⁻¹ by ring,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul, one_div]
    rw [h]
    refine one_half_le_law_crossing_zero hq (Pi.le_def.2 fun i => ?_) ?_
    · fin_cases i <;> simp
    · simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, sub_zero]
      omega
  | succ j ih =>
    have hd := law_crossing_zero_sq_le hq hn (m := (2 ^ j + 1) * n)
      (Nat.le_mul_of_pos_left n (Nat.succ_pos _))
    have e₁ : (((2 ^ j + 1) * n : ℕ) : ℤ) = (2 ^ j + 1) * (n : ℤ) := by push_cast; ring
    have e₂ : 2 * (((2 ^ j + 1) * n : ℕ) : ℤ) - n = (2 ^ (j + 1) + 1) * (n : ℤ) := by
      push_cast
      ring
    rw [e₂, e₁] at hd
    have h32 : (2 : ℝ≥0∞) ^ 5 ≠ 0 := pow_ne_zero _ two_ne_zero
    have h32' : (2 : ℝ≥0∞) ^ 5 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    rw [← ENNReal.mul_le_mul_iff_right h32 h32']
    have hexp : 6 * 2 ^ (j + 1) = 6 * 2 ^ j * 2 := by ring
    calc (2 : ℝ≥0∞) ^ 5 * (2 ^ 5 * 2⁻¹ ^ (6 * 2 ^ (j + 1)))
        = (2 ^ 5 * 2⁻¹ ^ (6 * 2 ^ j)) ^ 2 := by
          rw [hexp, pow_mul]
          ring
      _ ≤ law q (crossing 0 0 ![(2 ^ j + 1) * (n : ℤ), 2 * n]) ^ 2 := by gcongr
      _ ≤ 2 ^ 5 * law q (crossing 0 0 ![(2 ^ (j + 1) + 1) * (n : ℤ), 2 * n]) := hd

/-- **RSW** (the crossing conjunct of tag WD31). At the self-dual point, for each `k ≥ 2` there
is `c > 0` such that for every `n ≥ 1` the box `[0, 2kn] × [0, 2n]` is crossed from left to
right with probability at least `c`. -/
theorem exists_pos_le_law_crossing_zero (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ n : ℕ, 1 ≤ n → c ≤ law q (crossing 0 0 ![2 * (k : ℤ) * n, 2 * n]) := by
  refine ⟨2 ^ 5 * 2⁻¹ ^ (6 * 2 ^ (k + 1)), ENNReal.mul_pos (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)), fun q hq n hn => ?_⟩
  refine (le_law_crossing_zero_two_pow_add_one_mul hq hn (k + 1)).trans
    (measure_mono (crossing_zero_subset_crossing_zero ?_ ?_ ?_ ?_ ?_))
  all_goals simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, le_refl]
  · positivity
  · have hk2 : (k : ℤ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have hk3 : 2 * (k : ℤ) ≤ 2 ^ (k + 1) + 1 := by
      rw [pow_succ]
      omega
    exact mul_le_mul_of_nonneg_right hk3 (Nat.cast_nonneg n)

/-- **RSW in any position and either direction.** At the self-dual point, for each `k` there is
`c > 0` such that for every `n ≥ 1` and every corner `lo`, the `kn × n` box at `lo` is crossed
from left to right, and the `n × kn` box at `lo` from bottom to top, with probability at
least `c`. -/
theorem exists_pos_le_law_crossing (k : ℕ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n →
        c ≤ law q (crossing i lo
          (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n])) := by
  have h2 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  refine ⟨min (2 ^ 5 * 2⁻¹ ^ (6 * 2 ^ (k + 2))) (2⁻¹ ^ k),
    lt_min (ENNReal.mul_pos (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ h2.ne'))
      (ENNReal.pow_pos h2 k), fun q hq i lo n hn => ?_⟩
  have hq' : ∀ e ∈ (zdGraph 2).edgeSet, q e = ⟨1 / 2, by norm_num, by norm_num⟩ :=
    fun e he => Subtype.ext (hq e he)
  -- reduce to the box `[0, kn] × [0, n]` crossed from left to right
  have hred : law q (crossing i lo
      (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n])) =
      law q (crossing 0 0 ![(k : ℤ) * n, n]) := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      have h := law_crossing_add hq' 0 0 ![(k : ℤ) * n, n] lo
      rwa [zero_add, add_comm] at h
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      have h := law_crossing_add hq' 1 0 ![(n : ℤ), k * n] lo
      rw [zero_add, add_comm] at h
      rw [h, law_crossing_one_eq_law_crossing_zero hq']
      congr 2
      ext i
      fin_cases i <;> rfl
  rw [hred]
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · -- height one: a row of open edges
    refine (min_le_right _ _).trans ((inv_two_pow_le_law_crossing_zero hq k).trans
      (measure_mono ?_))
    rintro ω ⟨a, ha, ha0, b, hb, hb0, hab⟩
    have hsub : Icc (0 : LatticeSite 2) ![(k : ℤ), 0] ⊆
        Icc (0 : LatticeSite 2) ![(k : ℤ) * ((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ)] := by
      intro v hv
      rw [mem_Icc_two_iff] at hv ⊢
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_one,
        mul_one] at hv ⊢
      omega
    refine ⟨a, hsub ha, ha0, b, hsub hb, ?_, localConn_mono_set hsub _ _ hab⟩
    simp only [Matrix.cons_val_zero, Nat.cast_one, mul_one] at hb0 ⊢
    exact hb0
  · -- height at least two: the iteration at height `2 ⌊n/2⌋`
    have hn' : 1 ≤ n / 2 := by omega
    refine (min_le_left _ _).trans ((le_law_crossing_zero_two_pow_add_one_mul hq hn' (k + 2)).trans
      (measure_mono (crossing_zero_subset_crossing_zero ?_ ?_ ?_ ?_ ?_)))
    all_goals simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, le_refl]
    · positivity
    · have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
      have hk3 : 3 * k ≤ 2 ^ (k + 2) + 1 := by
        have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
        omega
      have hkn : k * n ≤ (2 ^ (k + 2) + 1) * (n / 2) :=
        calc k * n ≤ k * (3 * (n / 2)) := Nat.mul_le_mul_left _ (by omega)
          _ = 3 * k * (n / 2) := by ring
          _ ≤ (2 ^ (k + 2) + 1) * (n / 2) := Nat.mul_le_mul_right _ hk3
      exact_mod_cast hkn
    · omega

end PercLib.Models.Planar
