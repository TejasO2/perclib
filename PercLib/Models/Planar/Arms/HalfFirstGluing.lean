/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-27. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12) and
Section 4.6 (the half-plane versions).
-/
module

public import PercLib.Models.Planar.Arms.HalfCapGluing

/-!
# The first gluing in the half-plane, with fences at the new boundary

Separated arms of the half-plane `{v | z₁ ≤ v₁}` (landing in increasing order, without two
consecutive arms of one colour, separated at scale `s` from each other, from the corners and from
the two points of the line on the boundary) are continued straight out to a larger box, where they
get small new fences and keep their separation, also from the line. This is the half-plane version
of the straight first gluing of `CapGluing.lean`; the input is the output of the half-plane outer
separation step (`exists_half_separating_event`).

## Main results

* `le_sub_of_shift_half`: a landing position at least `S` from the two points of the line stays
  at least `S - 2E` from them after a jog by at most `E`.
* `pow_mul_law_le_law_separated_of_bins_half`: the straight first gluing for fixed bins.
* `exists_pos_le_law_separated_of_separated_half`: the straight first gluing,
  `c₀ P(separated at R, s) ≤ P(separated at R', s - 4W)`, with the separation from the line kept.
* `law_le_sum_law_windows_of_separated_half`: the separated half-plane event is covered by the
  events in which the arms end in given bins.

## Implementation notes

The separated half-plane event is written out: the arms of `ArmsOuterSeparated`, in the
half-plane, landing in increasing order, with landing positions in `[6R + s, 14R - s]`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### The line after a jog -/

section Shift

/-- **Distance to the line after a jog.** A landing position `L` on the boundary of `B_R`, at least
`S ≥ 0` from the corners `4 m R` and with `6R + S ≤ L ≤ 14R - S` (at least `S` above the two
points of the line), moves by the growth `(4t + 2)(R' - R)` of the perimeter up to its side `t`
plus at most `2E` to a position `L'` with `6R' + S - 2E ≤ L' ≤ 14R' - S + 2E`. -/
theorem le_sub_of_shift_half {R R' E S L L' : ℤ} (hRR' : R ≤ R') (hS : 0 ≤ S)
    (h : (0 < L ∧ L < 4 * R ∧ L + 2 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 2 * (R' - R) + 2 * E) ∨
      (4 * R < L ∧ L < 8 * R ∧ L + 6 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 6 * (R' - R) + 2 * E) ∨
      (8 * R < L ∧ L < 12 * R ∧ L + 10 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 10 * (R' - R) + 2 * E) ∨
      (12 * R < L ∧ L < 16 * R ∧ L + 14 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 14 * (R' - R) + 2 * E))
    (hcor : ∀ m : ℕ, S ≤ |L - 4 * m * R|) (hline : 6 * R + S ≤ L ∧ L + S ≤ 14 * R) :
    6 * R' + (S - 2 * E) ≤ L' ∧ L' + (S - 2 * E) ≤ 14 * R' := by
  have c2 := le_abs.1 (hcor 2)
  have c3 := le_abs.1 (hcor 3)
  push_cast at c2 c3
  rcases h with h | h | h | h <;> omega

end Shift

/-! ### The first gluing, straight, with fences at the new boundary -/

section Straight

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Fences at `∂B_{R'}(z)` for fixed bins, in the half-plane**
(`pow_mul_law_le_law_separated_of_bins` for the arms of the half-plane). Separated arms of the
half-plane ending in fixed bins of width `W` on the sides of `B_R(z)` (separation `s ≥ 4M` from
each other, the corners and the line, fences `(M, K)`) are continued straight out to arms of the
half-plane to `∂B_{R'}(z)`, landing in increasing order, separated at scale `s - 4W` from each
other, the corners and the line, with fences `(M', K')`, at the cost `c κ ^ (6j)`. The bins on
the half-sides lie above the line (read off a configuration of the event); `4M ≤ R`. -/
theorem pow_mul_law_le_law_separated_of_bins_half (q : Sym2 (LatticeSite 2) → unitInterval)
    {L : ℕ∞} {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) {R' M' K' W κ : ℕ} {h : ℤ} (hM : 1 ≤ M)
    (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W ≤ M' + K')
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R') (hrM : r + M + 1 < R)
    (hWM : 2 * W + 2 ≤ M) (hs : 4 * (M : ℝ) ≤ s) (hMR : 4 * M ≤ R)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W : ℤ) - 2 * K'))
    (hκH : (W : ℤ) - 2 * K' ≤ κ * ((W : ℤ) - 2 * K'))
    (hκC : (W : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) (J : Fin j → Set ℤ)
    (t : Fin j → Fin 4) (x : Fin j → ℤ) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧
      (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
        (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
      (∀ i, b i ∈ {b : LatticeSite 2 |
        (t i = 0 ∧ b 1 = z 1 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0 :
            ℕ) : ℤ) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 :
            ℕ) : ℤ) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
      (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
      ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧
      (∀ i, 6 * (R' : ℝ) + (s - 4 * W) ≤ landingPos (z - R') (z + R') (σ i) (γ i) ∧
        (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + (s - 4 * W) ≤ 14 * R') ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  have hrR : r < R := by omega
  have hRR' : R ≤ R' := by omega
  -- the empty case
  by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
      (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
      (∀ i, IsArm ω₀ (σ i) z r (z - R) (z + R) (γ₀ i)) ∧
        (∀ i, ∀ v ∈ (γ₀ i).support, z 1 ≤ v 1) ∧ ArmsOuterSeparated ω₀ σ z R s M K γ₀ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ₀ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ₀ i) : ℝ) + s ≤ 14 * R) ∧
        ∀ i, b₀ i ∈ {b : LatticeSite 2 |
            (t i = 0 ∧ b 1 = z 1 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
              z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
            (t i = 1 ∧ b 0 = z 0 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
              z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
            (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0
                : ℕ) : ℤ) + W ∧
              z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
            (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0
                : ℕ) : ℤ) + W ∧
              z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine mul_eq_zero_of_right _ ?_
    convert measure_empty (μ := law q)
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨a, b, γ, h₁, -, h₃, -, h₅, h₆, h₇, -⟩
    exact hne ⟨ω, a, b, γ, h₁, h₃, h₅, h₆, h₇⟩
  obtain ⟨ω₀, a₀, b₀, γ₀, hγ₀, hH₀, hsep₀, hline₀, hB₀⟩ := hne
  -- the bins of the configuration `ω₀` lie above the line, at least `2M` on the half-sides
  have hx : ∀ i, t i ≠ 2 ∧ (t i ≠ 0 → z 1 + 2 * M ≤ x i + W) := by
    intro i
    have hc : cond (σ i) (0 : ℤ) 1 = 0 ∨ cond (σ i) (0 : ℤ) 1 = 1 := by cases σ i <;> simp
    have hl₁ : ((6 * (R : ℤ) + 4 * M : ℤ) : ℝ) ≤
        (landingPos (z - R) (z + R) (σ i) (γ₀ i) : ℝ) := by
      push_cast
      linarith [(hline₀ i).1]
    have hl₂ : ((landingPos (z - R) (z + R) (σ i) (γ₀ i) + 4 * M : ℤ) : ℝ) ≤
        ((14 * (R : ℤ) : ℤ) : ℝ) := by
      push_cast
      linarith [(hline₀ i).2]
    have hl₁' : 6 * (R : ℤ) + 4 * M ≤ landingPos (z - R) (z + R) (σ i) (γ₀ i) := by
      exact_mod_cast hl₁
    have hl₂' : landingPos (z - R) (z + R) (σ i) (γ₀ i) + 4 * M ≤ 14 * (R : ℤ) := by
      exact_mod_cast hl₂
    have hb := hH₀ i (b₀ i) (γ₀ i).end_mem_support
    rcases hB₀ i with ⟨e, hb₁, h₁, h₂, -⟩ | ⟨e, hb₀, h₁, h₂, -⟩ | ⟨e, hb₁, -⟩ |
        ⟨e, hb₀, h₁, h₂, -⟩
    · exact ⟨by rw [e]; decide, fun h => absurd e h⟩
    · rw [(hγ₀ i).landingPos_eq_of_right hrR hb₀] at hl₁'
      exact ⟨by rw [e]; decide, fun _ => by push_cast at h₂; omega⟩
    · omega
    · rw [(hγ₀ i).landingPos_eq_of_left hrR hb₀] at hl₂'
      exact ⟨by rw [e]; decide, fun _ => by push_cast at h₂; omega⟩
  have hjog := fun i => jog_of_bin (σ i) z R R' M' K' W 0 M (t i) (x i) 0
  refine le_trans (mul_le_mul' le_rfl (measure_mono ?_)) ((pow_mul_law_le_law_of_jogs_half
    (σ := σ) (z := z) (r := r) (R := R) (s := s) (M := M)
    (K := K) q hCB hσ (R' := R') (M' := M') (K' := K') (W₀ := W) (D := 0) (κ := κ) (S := M)
    (h := h) hM hWK hKM hK' hM' hWM' hh hhR hrM le_rfl (by omega) hs hκV (by simpa using hκH) hκC
    hL J x (fun _ => 0) (fun _ => ⟨by simp, by simp⟩) _ _ _ _ _ _ hjog hMR (fun i => ?_)
    (fun i b hb v hv => ?_)).trans (measure_mono ?_))
  · rintro ω ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, -, h₇, h₈⟩
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₇, h₈⟩
  · obtain ⟨h2, h0⟩ := hx i
    split_ifs with e₀ e₁
    · simp
    · have := h0 (by rw [e₁]; decide)
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
    · have := h0 e₀
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · obtain ⟨h2, h0⟩ := hx i
    rw [mem_Icc_two_iff] at hv
    simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at hv
    rcases hb with ⟨e, hb1, -⟩ | ⟨e, -, hb1, -⟩ | ⟨e, -⟩ | ⟨e, -, hb1, -⟩
    · omega
    · have := h0 (by rw [e]; decide)
      push_cast at hb1
      omega
    · exact absurd e h2
    · have := h0 (by rw [e]; decide)
      push_cast at hb1
      omega
  rintro ω ⟨a, b', γ', hγ', hd', hH', ho', hJ', hB'⟩
  have hsh := fun i => (hγ₀ i).shift_of_jog (hγ' i) hrR hRR' (by omega) ⟨by simp, by simp⟩
    (hjog i) (hB₀ i) (hB' i).1
  have hs0 : (0 : ℝ) ≤ s := le_trans (by positivity) hs
  refine ⟨a, b', γ', hγ', hd', hH', ho', ⟨fun i k hik => ?_, fun i m => ?_, fun i => (hB' i).2⟩,
    fun i => ?_, hJ'⟩
  · have h₁ := hsep₀.1 i k hik
    have h₂ := abs_sub_sub_le_abs_of_shift (by omega) (hsh i) (hsh k)
    have h₃ : ((|landingPos (z - R) (z + R) (σ i) (γ₀ i) -
        landingPos (z - R) (z + R) (σ k) (γ₀ k)| - 4 * ((W : ℤ) + ((0 : ℕ) : ℤ)) : ℤ) : ℝ) ≤
        ((|landingPos (z - R') (z + R') (σ i) (γ' i) -
          landingPos (z - R') (z + R') (σ k) (γ' k)| : ℤ) : ℝ) := by exact_mod_cast h₂
    push_cast at h₁ h₃ ⊢
    linarith
  · have h₁ : ∀ m : ℕ, ⌈s⌉ ≤ |landingPos (z - R) (z + R) (σ i) (γ₀ i) - 4 * m * R| :=
      fun m => by
        have := hsep₀.2.1 i m
        rw [← Int.cast_abs] at this
        exact Int.ceil_le.2 (by exact_mod_cast this)
    have h₂ := sub_le_abs_sub_of_shift (by omega) (by omega) (hsh i) h₁ m
    have h₃ : ((⌈s⌉ - 2 * ((W : ℤ) + ((0 : ℕ) : ℤ)) : ℤ) : ℝ) ≤
        ((|landingPos (z - R') (z + R') (σ i) (γ' i) - 4 * m * R'| : ℤ) : ℝ) := by
      exact_mod_cast h₂
    push_cast at h₃ ⊢
    have h₄ := Int.le_ceil s
    have h₅ : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    linarith
  · have h₁ : ∀ m : ℕ, ⌈s⌉ ≤ |landingPos (z - R) (z + R) (σ i) (γ₀ i) - 4 * m * R| :=
      fun m => by
        have := hsep₀.2.1 i m
        rw [← Int.cast_abs] at this
        exact Int.ceil_le.2 (by exact_mod_cast this)
    have hl : 6 * (R : ℤ) + ⌈s⌉ ≤ landingPos (z - R) (z + R) (σ i) (γ₀ i) ∧
        landingPos (z - R) (z + R) (σ i) (γ₀ i) + ⌈s⌉ ≤ 14 * R := by
      have e₁ : ⌈s⌉ ≤ landingPos (z - R) (z + R) (σ i) (γ₀ i) - 6 * (R : ℤ) :=
        Int.ceil_le.2 (by push_cast; linarith [(hline₀ i).1])
      have e₂ : ⌈s⌉ ≤ 14 * (R : ℤ) - landingPos (z - R) (z + R) (σ i) (γ₀ i) :=
        Int.ceil_le.2 (by push_cast; linarith [(hline₀ i).2])
      constructor <;> omega
    have h₂ := le_sub_of_shift_half (by omega) (Int.ceil_nonneg hs0) (hsh i) h₁ hl
    have h₃ : ((6 * (R' : ℤ) + (⌈s⌉ - 2 * ((W : ℤ) + ((0 : ℕ) : ℤ))) : ℤ) : ℝ) ≤
        (landingPos (z - R') (z + R') (σ i) (γ' i) : ℝ) := by exact_mod_cast h₂.1
    have h₃' : ((landingPos (z - R') (z + R') (σ i) (γ' i) +
        (⌈s⌉ - 2 * ((W : ℤ) + ((0 : ℕ) : ℤ))) : ℤ) : ℝ) ≤ ((14 * (R' : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast h₂.2
    push_cast at h₃ h₃' ⊢
    have h₄ := Int.le_ceil s
    have h₅ : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    constructor <;> linarith

/-- **The first gluing with fences at the new boundary, in the half-plane**
(`exists_pos_le_law_separated_of_separated` for the arms of the half-plane). For a colour sequence
`σ` without two consecutive arms of one colour and ratios `A`, `D` there is `c₀ > 0` such that for
every law with crossing bounds `c` up to scale `L`, every centre `z`, radii `r < R < R' ≤ L`, bin
width `W`, fences `(M, K)` and `(M', K')`, separation `s` and inner windows `J`, with `1 ≤ K'`,
`4K' ≤ W ≤ K ≤ M`, `2W + 2 ≤ M`, `W ≤ M'`, `4M ≤ s`, `4M ≤ R`, `r + M + 1 < R`,
`R + M + 1 + W + M' ≤ R'`, `R' + M' ≤ D R` and `R ≤ A W`: `c₀ P(j arms of the half-plane to
∂B_R(z), increasing, separated at scale s from each other, the corners and the line, fences (M, K),
inner positions in J) ≤ P(the same at ∂B_{R'}(z) at scale s - 4W with fences (M', K'))`. The input
is the output of `exists_half_separating_event`. -/
theorem exists_pos_le_law_separated_of_separated_half {j : ℕ} (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ), 1 ≤ K' → 4 * K' ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → W ≤ M' →
      4 * (M : ℝ) ≤ s → 4 * M ≤ R → r + M + 1 < R → R + M + 1 + W + M' ≤ R' →
      R' + M' ≤ D * R → R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧
        (∀ i, 6 * (R' : ℝ) + (s - 4 * W) ≤ landingPos (z - R') (z + R') (σ i) (γ i) ∧
          (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + (s - 4 * W) ≤ 14 * R') ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  set κ : ℕ := 2 * D * A + 2 with hκeq
  by_cases hc : 0 < c κ
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  have hX0 : (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    positivity
  have hXt : (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨c κ ^ (6 * j) / (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞),
    ENNReal.div_pos (pow_ne_zero _ hc.ne') hXt, ?_⟩
  intro q L hCB z r R R' W M K M' K' s J hK'1 hK'W hWK hKM hWM hWM' hs hMR hrM hRR' hRD hRA hR'L
  have hrR : r < R := by omega
  have hW : 1 ≤ W := by omega
  -- the aspect ratios
  have hκV : (R' : ℤ) + M' - R ≤ κ * ((W : ℤ) - 2 * K') := by
    have e₁ : ((R' + M' : ℕ) : ℤ) ≤ ((D * (A * W) : ℕ) : ℤ) := by
      exact_mod_cast hRD.trans (Nat.mul_le_mul_left _ hRA)
    push_cast at e₁
    have e₂ : (0 : ℤ) ≤ (D : ℤ) * A * ((W : ℤ) - 4 * K') := mul_nonneg (by positivity) (by omega)
    rw [hκeq]
    push_cast
    nlinarith
  have hκH : (W : ℤ) - 2 * K' ≤ κ * ((W : ℤ) - 2 * K') :=
    le_mul_of_one_le_left (by omega) (by rw [hκeq]; push_cast; nlinarith)
  have hκC : (W : ℤ) ≤ κ * ((M' : ℤ) - 1) := by
    have : (2 : ℤ) * ((M' : ℤ) - 1) ≤ κ * ((M' : ℤ) - 1) :=
      mul_le_mul_of_nonneg_right (by rw [hκeq]; push_cast; nlinarith) (by omega)
    omega
  -- the separated event with ends in given bins
  set E : (Fin j → Fin 4 × Fin (2 * A + 1)) → Set (Config (LatticeSite 2)) :=
      fun β => {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        (∀ i, b i ∈ {b : LatticeSite 2 |
          ((β i).1 = 0 ∧ b 1 = z 1 + R ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R +
              (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ ((if (β i).1 = 0 ∨ (β
              i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) + W ∧
            z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
          ((β i).1 = 1 ∧ b 0 = z 0 + R ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R +
              (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ ((if (β i).1 = 0 ∨ (β
              i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) + W ∧
            z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
          ((β i).1 = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0
              else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ ((if (β
              i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0
              : ℕ) : ℤ) + W ∧
            z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
          ((β i).1 = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0
              else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ ((if (β
              i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0
              : ℕ) : ℤ) + W ∧
            z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} with hE
  -- every separated configuration has its ends in some bins
  have hcover : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      ∑ β, law q (E β) := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    rintro ω ⟨a, b, γ, hγ, hd, hH, ho, hsep, hline, hJ⟩
    have hsep' := hsep.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)
    choose t n hn hb using fun i => (hγ i).exists_mem_bin hrR (by omega) hW hRA (hsep'.2 i)
    rw [mem_iUnion]
    refine ⟨fun i => (t i, ⟨n i, hn i⟩), ?_⟩
    rw [hE]
    exact ⟨a, b, γ, hγ, hd, hH, ho, hsep, hline, fun i => mem_bin_zero_of_mem_bin (hb i), hJ⟩
  -- the gluing for each choice of bins
  have hβ : ∀ β, c κ ^ (6 * j) * law q (E β) ≤ law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j →
      LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧
        (∀ i, 6 * (R' : ℝ) + (s - 4 * W) ≤ landingPos (z - R') (z + R') (σ i) (γ i) ∧
          (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + (s - 4 * W) ≤ 14 * R') ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    intro β
    rw [hE]
    exact pow_mul_law_le_law_separated_of_bins_half q hCB hσ (h := R + M + 1) (by omega) hWK hKM
      (by omega) (by omega) (by omega) le_rfl (by omega) hrM hWM hs hMR hκV hκH hκC hR'L J
      (fun i => (β i).1)
      (fun i => (if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W +
          1))
  refine (mul_le_mul' le_rfl hcover).trans ?_
  rw [Finset.mul_sum]
  calc ∑ β, c κ ^ (6 * j) / (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) * law q (E β)
      ≤ ∑ _β : Fin j → Fin 4 × Fin (2 * A + 1), law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j
          → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
          (StrictMono fun i => landingPos (z - R') (z + R') (σ i) (γ i)) ∧
          ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧
          (∀ i, 6 * (R' : ℝ) + (s - 4 * W) ≤ landingPos (z - R') (z + R') (σ i) (γ i) ∧
            (landingPos (z - R') (z + R') (σ i) (γ i) : ℝ) + (s - 4 * W) ≤ 14 * R') ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i} *
            ((((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞))⁻¹ := by
        refine Finset.sum_le_sum fun β _ => ?_
        rw [div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul_left (hβ β) _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hX0 hXt, mul_one]

end Straight

/-! ### Covering by bins -/

section Cover

variable {j : ℕ}

/-- **Covering the separated half-plane event by windows of bins**
(`law_le_sum_law_windows_of_separated` for the arms of the half-plane, with the separation from
the line kept). Separated arms at the outer boundary of `B_R(z)` (separation `s ≥ 4M`) end in
bins of width `W` on the sides: the event is covered by the `(4 (2A + 1)) ^ j` events in which arm
`i` ends in the window of the bin `p i` (a side and an index), `R ≤ A W`. -/
theorem law_le_sum_law_windows_of_separated_half (q : Sym2 (LatticeSite 2) → unitInterval)
    {σ : Fin j → Bool} {z : LatticeSite 2} {r R W M K A : ℕ} {s : ℝ} (hrR : r < R) (hM : 1 ≤ M)
    (hW : 1 ≤ W) (hRA : R ≤ A * W) (hs : 4 * (M : ℝ) ≤ s) (J : Fin j → Set ℤ) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      ∑ p : Fin j → Fin 4 × Fin (2 * A + 1), law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j →
          LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
        (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        (∀ i, 6 * (R : ℝ) + s ≤ landingPos (z - R) (z + R) (σ i) (γ i) ∧
          (landingPos (z - R) (z + R) (σ i) (γ i) : ℝ) + s ≤ 14 * R) ∧
        (∀ i, b i ∈ {b : LatticeSite 2 |
          ((p i).1 = 0 ∧ b 1 = z 1 + R ∧ ((if (p i).1 = 0 ∨ (p i).1 = 2 then z 0 else z 1) - R +
              (((p i).2 : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ ((if (p i).1 = 0 ∨ (p i).1 = 2 then z 0
              else z 1) - R + (((p i).2 : ℕ) : ℤ) * (W + 1)) + W) ∨
          ((p i).1 = 1 ∧ b 0 = z 0 + R ∧ ((if (p i).1 = 0 ∨ (p i).1 = 2 then z 0 else z 1) - R +
              (((p i).2 : ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ ((if (p i).1 = 0 ∨ (p i).1 = 2 then z 0
              else z 1) - R + (((p i).2 : ℕ) : ℤ) * (W + 1)) + W) ∨
          ((p i).1 = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ ((if (p i).1 = 0 ∨ (p i).1 = 2 then z 0
              else z 1) - R + (((p i).2 : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ ((if (p i).1 = 0 ∨ (p
              i).1 = 2 then z 0 else z 1) - R + (((p i).2 : ℕ) : ℤ) * (W + 1)) + W) ∨
          ((p i).1 = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ ((if (p i).1 = 0 ∨ (p i).1 = 2 then z 0
              else z 1) - R + (((p i).2 : ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ ((if (p i).1 = 0 ∨ (p
              i).1 = 2 then z 0 else z 1) - R + (((p i).2 : ℕ) : ℤ) * (W + 1)) + W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
  rintro ω ⟨a, b, γ, hγ, hd, hH, ho, hsep, hline, hJ⟩
  have hcor := (hsep.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)).2
  have hbin := fun i => (hγ i).exists_mem_bin hrR hM hW hRA (fun m => hcor i m)
  choose t n hn hb using hbin
  rw [mem_iUnion]
  refine ⟨fun i => (t i, ⟨n i, hn i⟩), a, b, γ, hγ, hd, hH, ho, hsep, hline, fun i => ?_, hJ⟩
  rcases hb i with ⟨h₀, h₁, h₂, h₃, -⟩ | ⟨h₀, h₁, h₂, h₃, -⟩ | ⟨h₀, h₁, h₂, h₃, -⟩ |
      ⟨h₀, h₁, h₂, h₃, -⟩
  · exact Or.inl ⟨h₀, h₁, h₂, h₃⟩
  · exact Or.inr (Or.inl ⟨h₀, h₁, h₂, h₃⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h₀, h₁, h₂, h₃⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₀, h₁, h₂, h₃⟩))

end Cover

end PercLib.Models.Planar
