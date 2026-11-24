/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12).
-/
module

public import PercLib.Models.Planar.Arms.JogCorridors

/-!
# Gluing separated arms with fences at the new boundary

Arms separated at the outer boundary of `B_R(z)` (`outerSeparatedArmEvent`) are continued to the
boundary of `B_{R'}(z)`, moved along their sides by given shifts, and given new outer fences there,
at the cost of a constant factor (Nolin's Proposition 12, with fences at the new boundary).

* **Gluing inside straight boxes** (`law_mul_prod_le_law_of_sides`): the gluing through given
  corridors (`law_mul_prod_le_law_of_corridors`) when every corridor reads only pairs inside a
  straight box from its bin out to distance `R''`; the geometric conditions are those of the
  straight gluing, with a margin `S ≥ M` for the separation of the arms.
* **Jogs with caps for fixed bins** (`pow_mul_law_le_law_of_jogs`): the corridors of
  `exists_corridor_jog`.
* **The first gluing with fences at the new boundary**
  (`exists_pos_le_law_separated_of_separated`): straight corridors with caps from bins of
  width `W`; the separation `s` at `∂B_R(z)` becomes `s - 4W` at `∂B_{R'}(z)`
  (`IsArm.shift_of_jog`, `abs_sub_sub_le_abs_of_shift`, `sub_le_abs_sub_of_shift`), and the new
  fences have any size `M' ≥ W`, `K' ≤ W / 4`.

* **Window-to-window steps** (`exists_pos_le_law_windows_of_windows`): arms ending in windows
  on the sides of `B_R(z)` are moved along their sides by fixed shifts (jogs) and capped at
  `∂B_{R'}(z)`, ending in the shifted windows; the separation at `R'` is read off the windows
  (`le_abs_landingPos_sub_of_windows`), so the constant does not depend on the separation scale
  of the first gluing.

## Main results

* `law_mul_prod_le_law_of_sides`: the gluing inside straight boxes.
* `pow_mul_law_le_law_of_jogs`: jogs with caps for fixed bins.
* `jog_of_bin`: the jog of a bin, on any side.
* `exists_pos_le_law_separated_of_separated`,
  `exists_pos_le_law_outerSeparatedArmEvent_of_separated`: **the first gluing with fences at
  `∂B_{R'}(z)`**, `c₀ P(separated at R, scale s, fences (M, K)) ≤ P(separated at R', scale s - 4W,
  fences (M', K'))`, inner windows carried.
* `le_abs_landingPos_sub_of_windows`: arms ending in separated windows on the sides are
  separated.
* `exists_pos_le_law_windows_of_windows`: **the window-to-window step**, `c₀ P(separated, ends in
  windows [α i, β i] at R) ≤ P(separated at scale 2g' - 1 with fences (M', K'), ends in windows
  [α i + d i, β i + d i + W] at R')`.
-/


@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Gluing through corridors inside straight boxes -/

section Sides

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing through arbitrary corridors inside straight boxes.** Let each arm `i` have a straight
box `Icc (lo i) (hi i)` of width `W`, running from its side of `B_R(z)` straight out to distance
`R''` (`hside`, as in `pow_mul_law_le_law_multiArmEventIn_of_sides`, with the corner distance `2S`
for a margin `S ≥ M`), and let the possible ends `B i` of arm `i` lie at the foot of its box. Let
the corridor event `C i` read only pairs inside its box (enlarged by one at the upper corner for a
dual arm), and let the continuations run, apart from the box of radius `M` about the end, through a
region `Q i` inside the box that meets `Icc (z - R - 1) (z + R)` only near the end. With
separation `s ≥ 4S` and `2W + 2 ≤ S`, every fenced separated family ending in the sets `B i` is
glued: `P(separated, ends in B, inner positions in J) · ∏ P(C i) ≤ P(arms to ∂B_{R'}(z) with inner
positions in J and ends satisfying Φ)`. The margin `S` may exceed the fence size `M`: wide boxes
need well separated arms, not deep fences. -/
theorem law_mul_prod_le_law_of_sides (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' R'' W S : ℕ}
    (hKM : K ≤ M) (hM : 1 ≤ M) (hMS : M ≤ S) (hWS : 2 * W + 2 ≤ S) (hs : 4 * (S : ℝ) ≤ s)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hRR'' : R ≤ R'')
    (J : Fin j → Set ℤ) (x : Fin j → ℤ) (dir : Fin j → Fin 2) (lo hi : Fin j → LatticeSite 2)
    (Bf B : Fin j → Set (LatticeSite 2))
    (hside : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧ hi i = ![x i + W, z 1 + R''] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + W ∧ z 0 - R + 2 * S ≤ b 0 ∧
          b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + R'', x i + W] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + W ∧ z 1 - R + 2 * S ≤ b 1 ∧
          b 1 + 2 * S ≤ z 1 + R) ∨
      (dir i = 1 ∧ lo i = ![x i, z 1 - R'' - cond (σ i) 0 1] ∧
        hi i = ![x i + W, z 1 - R - cond (σ i) 0 1] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧ b 0 ≤ x i + W ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 - R'' - cond (σ i) 0 1, x i] ∧
        hi i = ![z 0 - R - cond (σ i) 0 1, x i + W] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧ b 1 ≤ x i + W ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R))
    (hB : ∀ i, B i ⊆ Bf i)
    (C : Fin j → Set (Config (LatticeSite 2))) (T : Fin j → Set (Sym2 (LatticeSite 2)))
    (Q : Fin j → Set (LatticeSite 2)) (Φ : Fin j → Config (LatticeSite 2) → LatticeSite 2 → Prop)
    (hCm : ∀ i, MeasurableSet (C i))
    (hCT : ∀ i (ω ω' : Config (LatticeSite 2)), ω ∩ T i = ω' ∩ T i → (ω ∈ C i ↔ ω' ∈ C i))
    (hCmono : ∀ i (ω ω' : Config (LatticeSite 2)), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω →
      ω ∈ C i → ω' ∈ C i)
    (hTsub : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∈ Icc (lo i) (hi i + cond (σ i) 0 1))
    (hQsub : ∀ i, Q i ⊆ Icc (lo i) (hi i))
    (hQloc : ∀ i, ∀ b ∈ B i, ∀ v ∈ Q i, v ∈ Icc (z - R - 1) (z + R) →
      v ∈ Icc (b - M) (b + M))
    (hhook : ∀ i, ∀ ω ∈ C i, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
      IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
      ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
        x ∈ Icc (b - M) (b + M) ∧ (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
        (∀ v ∈ P.support, v ∈ Icc (b - M) (b + M) ∨ v ∈ Q i) ∧
        y ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)) ∧
        ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1))
          (Icc (z - R') (z + R' - 1)) → Φ i ω v) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ∏ i, law q (C i) ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ' i))
        (landingPos (z - R') (z + R') (σ k) (γ' k)) (landingPos (z - R') (z + R') (σ l) (γ' l))) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧ ∀ i, Φ i ω (b' i)} := by
  classical
  have hrR : r < R := by omega
  have hS : 1 ≤ S := by omega
  have hc : ∀ i, 0 ≤ cond (σ i) (0 : ℤ) 1 ∧ cond (σ i) (0 : ℤ) 1 ≤ 1 := fun i => by
    cases σ i <;> simp
  have hMS' : (M : ℝ) ≤ S := by exact_mod_cast hMS
  have hsM : 4 * (M : ℝ) ≤ s := by linarith
  -- the empty case
  by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
      (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
      (∀ i, IsArm ω₀ (σ i) z r (z - R) (z + R) (γ₀ i)) ∧ ArmsOuterSeparated ω₀ σ z R s M K γ₀ ∧
        ∀ i, b₀ i ∈ B i
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine mul_eq_zero_of_left ?_ _
    convert measure_empty (μ := law q)
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨a, b, γ, h₁, -, -, h₄, h₅, -⟩
    exact hne ⟨ω, a, b, γ, h₁, h₄, h₅⟩
  obtain ⟨ω₀, a₀, b₀, γ₀, hγ₀, hsep₀, hB₀⟩ := hne
  have hsep₀' := hsep₀.le_abs_landingPos_sub (S := 4 * S) (by push_cast; linarith)
  have SL₀ := fun i => (hγ₀ i).sideL_of_side hrR hS (hside i) (hB i (hB₀ i))
  -- open and dual corridors read disjoint pairs
  have hTT : ∀ i k, σ i = true → σ k = false → Disjoint (T i) (T k) := by
    intro i k hi hk
    rw [disjoint_left]
    intro e he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have h₁ := hTsub i e he v hv
    have h₂ := hTsub k e he' v hv
    have hik : i ≠ k := fun h => by
      rw [h, hk] at hi
      exact Bool.false_ne_true hi
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Pi.add_apply, cond_zero_one_apply] at h₁ h₂
    exact false_of_corridor_of_corridor (by omega) (by omega) (by simp [hi]) (by simp [hk])
      (SL₀ i) (SL₀ k) (hsep₀'.1 i k hik) h₁ h₂
  -- corridors of one colour avoid the end boxes of the other colour
  have hTB : ∀ i k, σ i ≠ σ k → ∀ b ∈ B i, ∀ e ∈ T k, ¬∀ v ∈ e, v ∈ Icc (b - (M : LatticeSite 2))
      (b + ((M + 1 : ℕ) : LatticeSite 2)) := by
    intro i k hik b hb e he hbox
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have h₁ := hTsub k e he v hv
    have h₂ := hbox v hv
    have hik' : i ≠ k := fun h => hik (h ▸ rfl)
    rw [mem_Icc_two_iff] at h₁ h₂
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, cond_zero_one_apply] at h₁ h₂
    refine false_of_box_of_corridor (by omega) (by omega) (by omega) ?_ (SL₀ i)
      (sideP_of_side (hside i) (hB i hb)) (SL₀ k) (hsep₀'.1 i k hik')
      ⟨by omega, by omega, by omega, by omega⟩ h₁
    rcases Bool.eq_false_or_eq_true (σ i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (σ k) with h' | h'
    · exact absurd (h.trans h'.symm) hik
    · rw [h, h']
      exact Or.inl ⟨rfl, rfl⟩
    · rw [h, h']
      exact Or.inr ⟨rfl, rfl⟩
    · exact absurd (h.trans h'.symm) hik
  -- the regions of arms of one colour are disjoint
  have hQdisj : ∀ (ω : Config (LatticeSite 2)) (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) → ArmsDisjoint σ γ →
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) →
      ArmsOuterSeparated ω σ z R s M K γ → (∀ i, b i ∈ B i) →
      ∀ i k, i ≠ k → σ i = σ k → ∀ v, (v ∈ Icc (b i - M) (b i + M) ∨ v ∈ Q i) →
        (v ∈ Icc (b k - M) (b k + M) ∨ v ∈ Q k) → False := by
    intro ω a b γ hγ _ ho hsep hBw i k hik hσik v hvi hvk
    rcases hσ with hj | hσ'
    · exact hik (Fin.ext (by omega))
    have hsep' := hsep.le_abs_landingPos_sub (S := 4 * S) (by push_cast; linarith)
    have hbd : ∀ l, 0 ≤ landingPos (z - R) (z + R) (σ l) (γ l) ∧
        landingPos (z - R) (z + R) (σ l) (γ l) ≤ 16 * R := fun l => by
      have := (hγ l).sideL_of_side hrR hS (hside l) (hB l (hBw l))
      have := hc l
      omega
    have hlo' : ∀ l, 4 * (S : ℤ) ≤ landingPos (z - R) (z + R) (σ l) (γ l) := fun l => by
      have h₁ := hsep'.2 l 0
      have h₂ := hbd l
      rw [le_abs] at h₁
      push_cast at h₁
      omega
    have hhi' : ∀ l, landingPos (z - R) (z + R) (σ l) (γ l) + 4 * S ≤ 16 * R := fun l => by
      have h₁ := hsep'.2 l 4
      have h₂ := hbd l
      rw [le_abs] at h₁
      push_cast at h₁
      omega
    have h8 := two_mul_le_abs_landingPos_sub (Or.inr hσ') ho hsep'.1 hik hσik
    have hcorC : ∀ C : ℤ, C = 4 * R ∨ C = 8 * R ∨ C = 12 * R → ∀ l,
        4 * (S : ℤ) ≤ |landingPos (z - R) (z + R) (σ l) (γ l) - C| := by
      intro C hC l
      have h₁ := hsep'.2 l 1
      have h₂ := hsep'.2 l 2
      have h₃ := hsep'.2 l 3
      rw [le_abs] at h₁ h₂ h₃ ⊢
      push_cast at h₁ h₂ h₃
      omega
    have hvi' : v ∈ Icc (b i - S) (b i + S) ∨ v ∈ Icc (lo i) (hi i) := by
      rcases hvi with h | h
      · left
        rw [mem_Icc_two_iff] at h ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h ⊢
        omega
      · exact Or.inr (hQsub i h)
    have hvk' : v ∈ Icc (b k - S) (b k + S) ∨ v ∈ Icc (lo k) (hi k) := by
      rcases hvk with h | h
      · left
        rw [mem_Icc_two_iff] at h ⊢
        simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at h ⊢
        omega
      · exact Or.inr (hQsub k h)
    rw [mem_Icc_two_iff, mem_Icc_two_iff] at hvi' hvk'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hvi' hvk'
    refine false_of_region_of_region (by omega) (by omega) (hc i) (by rw [hσik])
      ((hγ i).sideL_of_side hrR hS (hside i) (hB i (hBw i)))
      ((hγ k).sideL_of_side hrR hS (hside k) (hB k (hBw k))) (by linarith)
      (fun C hC => ⟨?_, ?_⟩) (fun P hP => ⟨?_, ?_⟩) hvi' hvk'
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 (hcorC C hC) hik hσik h₁ h₂
      omega
    · intro h₁ h₂
      have := le_or_le_of_lt_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 (hcorC C hC) hik.symm hσik.symm h₁ h₂
      omega
    · intro h₁
      have := le_or_le_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 hlo' hhi' hik hσik h₁
      omega
    · intro h₁
      have := le_or_le_of_lt (f := fun l => landingPos (z - R) (z + R) (σ l) (γ l)) hσ' ho
        hsep'.1 hlo' hhi' hik.symm hσik.symm h₁
      omega
  refine law_mul_prod_le_law_of_corridors q hσ hKM hM hrM hRR' hsM B J C T Q Φ hCm hCT hCmono hTT
    (fun i e he v hv => ?_) hTB hQloc hQdisj hhook
  have h₁ := hTsub i e he v hv
  have h₂ := sideP_of_side (hside i) (hB i (hB₀ i))
  have hc' := hc i
  intro hvI
  rw [mem_Icc_two_iff] at h₁ hvI
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply,
    cond_zero_one_apply] at h₁ hvI
  omega

end Sides

/-! ### Gluing through jogs with caps, for fixed bins -/

section JogGluing

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Gluing separated arms through jogs with caps, for fixed bins.** Let each arm `i` end in a bin
`B i` of width `W₀` on a side of `B_R(z)` (inside the fat bin `Bf i` of width `W₀ + 2D`, at least
`2S`
from the corners), and let it be moved along its side by `d i`, `|d i| ≤ D`, and capped at
`∂B_{R'}(z)` above the target `B' i` (`hjog`). With separation `s ≥ 4S`, `2(W₀ + 2D) + 2 ≤ S`,
`M ≤ S`, the level `h` and the aspect bounds `hκV`, `hκH`, `hκC` of `exists_corridor_jog`:
`c κ ^ (6j) · P(separated with ends in B, inner positions in J) ≤ P(arms to ∂B_{R'}(z), disjoint,
ordered, inner positions in J, ending in B' with outer fences of length 2K' and depth M')`. -/
theorem pow_mul_law_le_law_of_jogs (q : Sym2 (LatticeSite 2) → unitInterval) {L : ℕ∞}
    {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c) (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    {R' M' K' W₀ D κ S : ℕ} {h : ℤ} (hM : 1 ≤ M) (hWK : W₀ ≤ K) (hKM : K ≤ M)
    (hK' : 2 * K' + 1 ≤ W₀) (hM' : 2 ≤ M') (hWM' : W₀ ≤ M' + K') (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + ((W₀ : ℤ) - 2 * K') + M' ≤ R') (hrM : r + M + 1 < R) (hMS : M ≤ S)
    (hWS : 2 * (W₀ + 2 * D) + 2 ≤ S) (hs : 4 * (S : ℝ) ≤ s)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W₀ - 2 * K' ≤ κ * ((W₀ : ℤ) - 2 * K'))
    (hκC : (W₀ : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) (J : Fin j → Set ℤ)
    (x d : Fin j → ℤ) (hd : ∀ i, -(D : ℤ) ≤ d i ∧ d i ≤ D) (dir : Fin j → Fin 2)
    (lo hi : Fin j → LatticeSite 2) (Bf B B' : Fin j → Set (LatticeSite 2))
    (hjog : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧ hi i = ![x i + ↑(W₀ + 2 * D), z 1 + ↑(R' +
        M')] ∧
          (∀ b, b ∈ Bf i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          (∀ b, b ∈ B i ↔ b 1 = z 1 + R ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W₀ ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          ∀ v, v ∈ B' i ↔ v 1 = z 1 + R' ∧ x i + D + d i + K' ≤ v 0 ∧ v 0 ≤ x i + D + d i + W₀ - K')
              ∨
        (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + ↑(R' + M'), x i + ↑(W₀ + 2 * D)] ∧
          (∀ b, b ∈ Bf i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          (∀ b, b ∈ B i ↔ b 0 = z 0 + R ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W₀ ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          ∀ v, v ∈ B' i ↔ v 0 = z 0 + R' ∧ x i + D + d i + K' ≤ v 1 ∧ v 1 ≤ x i + D + d i + W₀ - K')
              ∨
        (dir i = 1 ∧ lo i = ![x i, z 1 - ↑(R' + M') - cond (σ i) 0 1] ∧
          hi i = ![x i + ↑(W₀ + 2 * D), z 1 - R - cond (σ i) 0 1] ∧
          (∀ b, b ∈ Bf i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧ b 0 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          (∀ b, b ∈ B i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W₀ ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          ∀ v, v ∈ B' i ↔ v 1 = z 1 - R' - cond (σ i) 0 1 ∧ x i + D + d i + K' ≤ v 0 ∧
            v 0 ≤ x i + D + d i + W₀ - K') ∨
        (dir i = 0 ∧ lo i = ![z 0 - ↑(R' + M') - cond (σ i) 0 1, x i] ∧
          hi i = ![z 0 - R - cond (σ i) 0 1, x i + ↑(W₀ + 2 * D)] ∧
          (∀ b, b ∈ Bf i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧ b 1 ≤ x i + ↑(W₀ + 2 * D) ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          (∀ b, b ∈ B i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W₀ ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          ∀ v, v ∈ B' i ↔ v 0 = z 0 - R' - cond (σ i) 0 1 ∧ x i + D + d i + K' ≤ v 1 ∧
            v 1 ≤ x i + D + d i + W₀ - K')) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ B i) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b' : Fin j → LatticeSite 2)
      (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ' i))
        (landingPos (z - R') (z + R') (σ k) (γ' k)) (landingPos (z - R') (z + R') (σ l) (γ' l))) ∧
      (∀ i, innerPos z r (σ i) (γ' i) ∈ J i) ∧
      ∀ i, b' i ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K' (γ' i)} := by
  classical
  have hMR : M ≤ R := by omega
  choose C T Q hCm hCT hCmono hTsub hQsub hQloc hhook hprob using fun i =>
    exists_corridor_jog (col := σ i) (z := z) (h := h) (d := d i) hCB hM hWK hKM hK' hM' hWM'
      (hd i).1 (hd i).2 hh hhR hMR hMS (by omega) hκV hκH hκC hL (hjog i)
  have hside : ∀ i, (dir i = 1 ∧ lo i = ![x i, z 1 + R] ∧
        hi i = ![x i + ↑(W₀ + 2 * D), z 1 + ↑(R' + M')] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 + R ∧ x i ≤ b 0 ∧ b 0 ≤ x i + ↑(W₀ + 2 * D) ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 + R, x i] ∧ hi i = ![z 0 + ↑(R' + M'), x i + ↑(W₀ + 2 * D)] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 + R ∧ x i ≤ b 1 ∧ b 1 ≤ x i + ↑(W₀ + 2 * D) ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨
      (dir i = 1 ∧ lo i = ![x i, z 1 - ↑(R' + M') - cond (σ i) 0 1] ∧
        hi i = ![x i + ↑(W₀ + 2 * D), z 1 - R - cond (σ i) 0 1] ∧
        ∀ b, b ∈ Bf i ↔ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i ≤ b 0 ∧
          b 0 ≤ x i + ↑(W₀ + 2 * D) ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
      (dir i = 0 ∧ lo i = ![z 0 - ↑(R' + M') - cond (σ i) 0 1, x i] ∧
        hi i = ![z 0 - R - cond (σ i) 0 1, x i + ↑(W₀ + 2 * D)] ∧
        ∀ b, b ∈ Bf i ↔ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i ≤ b 1 ∧
          b 1 ≤ x i + ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) := by
    intro i
    rcases hjog i with ⟨h₁, h₂, h₃, h₄, -⟩ | ⟨h₁, h₂, h₃, h₄, -⟩ | ⟨h₁, h₂, h₃, h₄, -⟩ |
      ⟨h₁, h₂, h₃, h₄, -⟩
    · exact Or.inl ⟨h₁, h₂, h₃, h₄⟩
    · exact Or.inr (Or.inl ⟨h₁, h₂, h₃, h₄⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, h₄⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, h₄⟩))
  have hBsub : ∀ i, B i ⊆ Bf i := by
    intro i b hb
    rcases hjog i with ⟨-, -, -, h₄, h₅, -⟩ | ⟨-, -, -, h₄, h₅, -⟩ | ⟨-, -, -, h₄, h₅, -⟩ |
      ⟨-, -, -, h₄, h₅, -⟩ <;> rw [h₄] <;> rw [h₅] at hb <;> push_cast <;> omega
  have hmain := law_mul_prod_le_law_of_sides (σ := σ) (z := z) (r := r) (R := R) (s := s) (M := M)
    (K := K) (R' := R') (R'' := R' + M') (W := W₀ + 2 * D) (S := S) q hσ hKM hM hMS hWS hs hrM
    (by omega) (by omega) J x dir lo hi Bf B hside hBsub C T Q
    (fun i ω v => v ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K'
      (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v))
    hCm hCT hCmono hTsub hQsub hQloc
    (fun i ω hω a b γ _ hb hf => hhook i ω hω a b γ hb hf)
  have hprod : c κ ^ (6 * j) ≤ ∏ i, law q (C i) := by
    calc c κ ^ (6 * j) = ∏ _i : Fin j, c κ ^ 6 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ ∏ i, law q (C i) := Finset.prod_le_prod fun i _ => hprob i
  calc c κ ^ (6 * j) * law q _ ≤ law q _ * ∏ i, law q (C i) := by
        rw [mul_comm]
        exact mul_le_mul' le_rfl hprod
    _ ≤ _ := hmain.trans (measure_mono fun ω hω => by
        obtain ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅⟩ := hω
        exact ⟨a, b', γ', h₁, h₂, h₃, h₄, fun i => ⟨(h₅ i).1, (h₅ i).2.of_nil (γ' i)⟩⟩)

end JogGluing

/-! ### Bins with jogs -/

/-- **The jog of a bin**: the bin of side `t` (`0` top, `1` right, `2` bottom, `3` left) starting at
`x + D`, its fat bin, its straight box out to distance `R' + M'` and its target at `∂B_{R'}(z)`
shifted by `d` satisfy the description `hjog` used by `pow_mul_law_le_law_of_jogs`. -/
theorem jog_of_bin (col : Bool) (z : LatticeSite 2) (R R' M' K' W₀ D S : ℕ) (t : Fin 4)
    (x d : ℤ) :
    ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 1 ∧ (if t = 0 then ![x, z 1 + R] else if t = 1
        then ![z 0 + R, x] else if t = 2 then ![x, z 1 - ↑(R' + M') - cond col 0 1] else ![z 0 -
        ↑(R' + M') - cond col 0 1, x]) = ![x, z 1 + R] ∧ (if t = 0 then ![x + ↑(W₀ + 2 * D), z 1 +
        ↑(R' + M')] else if t = 1 then ![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 * D)] else if t = 2 then ![x
        + ↑(W₀ + 2 * D), z 1 - R - cond col 0 1] else ![z 0 - R - cond col 0 1, x + ↑(W₀ + 2 * D)])
        = ![x + ↑(W₀ + 2 * D), z 1 + ↑(R' +
        M')] ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D)
              ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧
              b 1 ≤ x + ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b
              1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧ z 0 - R + 2 * S ≤ b 0
              ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x +
              ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 1 = z 1 + R ∧ x ≤
              b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z
              0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧
              b 1 ≤ x + D + W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b 1 = z 1
              - R - cond col 0 1 ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2
              * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D +
              W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b
              0 ≤ x + D + W₀ ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          ∀ v, v ∈ {v : LatticeSite 2 | (t = 0 ∧ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D
              + d + W₀ - K') ∨ (t = 1 ∧ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀
              - K') ∨ (t = 2 ∧ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D +
              d + W₀ - K') ∨ (t = 3 ∧ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x
              + D + d + W₀ - K')} ↔ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D + d + W₀ -
              K')
              ∨
        ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 0 ∧ (if t = 0 then ![x, z 1 + R] else if t = 1
            then ![z 0 + R, x] else if t = 2 then ![x, z 1 - ↑(R' + M') - cond col 0 1] else ![z 0 -
            ↑(R' + M') - cond col 0 1, x]) = ![z 0 + R, x] ∧ (if t = 0 then ![x + ↑(W₀ + 2 * D), z 1
            + ↑(R' + M')] else if t = 1 then ![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 * D)] else if t = 2
            then ![x + ↑(W₀ + 2 * D), z 1 - R - cond col 0 1] else ![z 0 - R - cond col 0 1, x +
            ↑(W₀ + 2 * D)]) = ![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 * D)] ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D)
              ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧
              b 1 ≤ x + ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b
              1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧ z 0 - R + 2 * S ≤ b 0
              ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x +
              ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 0 = z 0 + R ∧ x ≤
              b 1 ∧ b 1 ≤ x + ↑(W₀ + 2 * D) ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z
              0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧
              b 1 ≤ x + D + W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b 1 = z 1
              - R - cond col 0 1 ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2
              * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D +
              W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧ b
              1 ≤ x + D + W₀ ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          ∀ v, v ∈ {v : LatticeSite 2 | (t = 0 ∧ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D
              + d + W₀ - K') ∨ (t = 1 ∧ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀
              - K') ∨ (t = 2 ∧ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D +
              d + W₀ - K') ∨ (t = 3 ∧ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x
              + D + d + W₀ - K')} ↔ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀ -
              K')
              ∨
        ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 1 ∧ (if t = 0 then ![x, z 1 + R] else if t = 1
            then ![z 0 + R, x] else if t = 2 then ![x, z 1 - ↑(R' + M') - cond col 0 1] else ![z 0 -
            ↑(R' + M') - cond col 0 1, x]) = ![x, z 1 - ↑(R' + M') - cond col 0 1] ∧
          (if t = 0 then ![x + ↑(W₀ + 2 * D), z 1 + ↑(R' + M')] else if t = 1 then ![z 0 + ↑(R' +
              M'), x + ↑(W₀ + 2 * D)] else if t = 2 then ![x + ↑(W₀ + 2 * D), z 1 - R - cond col 0
              1] else ![z 0 - R - cond col 0 1, x + ↑(W₀ + 2 * D)]) = ![x + ↑(W₀ + 2 * D), z 1 - R -
              cond col 0 1] ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D)
              ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧
              b 1 ≤ x + ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b
              1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧ z 0 - R + 2 * S ≤ b 0
              ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x +
              ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 1 = z 1 - R - cond
              col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z
              0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧
              b 1 ≤ x + D + W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b 1 = z 1
              - R - cond col 0 1 ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2
              * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D +
              W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 1 = z 1 - R - cond col 0 1 ∧
              x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
          ∀ v, v ∈ {v : LatticeSite 2 | (t = 0 ∧ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D
              + d + W₀ - K') ∨ (t = 1 ∧ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀
              - K') ∨ (t = 2 ∧ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D +
              d + W₀ - K') ∨ (t = 3 ∧ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x
              + D + d + W₀ - K')} ↔ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧
            v 0 ≤ x + D + d + W₀ - K') ∨
        ((if t = 0 ∨ t = 2 then (1 : Fin 2) else 0) = 0 ∧ (if t = 0 then ![x, z 1 + R] else if t = 1
            then ![z 0 + R, x] else if t = 2 then ![x, z 1 - ↑(R' + M') - cond col 0 1] else ![z 0 -
            ↑(R' + M') - cond col 0 1, x]) = ![z 0 - ↑(R' + M') - cond col 0 1, x] ∧
          (if t = 0 then ![x + ↑(W₀ + 2 * D), z 1 + ↑(R' + M')] else if t = 1 then ![z 0 + ↑(R' +
              M'), x + ↑(W₀ + 2 * D)] else if t = 2 then ![x + ↑(W₀ + 2 * D), z 1 - R - cond col 0
              1] else ![z 0 - R - cond col 0 1, x + ↑(W₀ + 2 * D)]) = ![z 0 - R - cond col 0 1, x +
              ↑(W₀ + 2 * D)] ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D)
              ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧
              b 1 ≤ x + ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b
              1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧ z 0 - R + 2 * S ≤ b 0
              ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x +
              ↑(W₀ + 2 * D) ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 0 = z 0 - R - cond
              col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + ↑(W₀ + 2 * D) ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          (∀ b, b ∈ {b : LatticeSite 2 | (t = 0 ∧ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z
              0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨ (t = 1 ∧ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧
              b 1 ≤ x + D + W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨ (t = 2 ∧ b 1 = z 1
              - R - cond col 0 1 ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧ z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2
              * S ≤ z 0 + R) ∨ (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D +
              W₀ ∧ z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} ↔ b 0 = z 0 - R - cond col 0 1 ∧
              x + D ≤ b 1 ∧ b 1 ≤ x + D + W₀ ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
          ∀ v, v ∈ {v : LatticeSite 2 | (t = 0 ∧ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D
              + d + W₀ - K') ∨ (t = 1 ∧ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀
              - K') ∨ (t = 2 ∧ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D +
              d + W₀ - K') ∨ (t = 3 ∧ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x
              + D + d + W₀ - K')} ↔ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧
            v 1 ≤ x + D + d + W₀ - K') := by
  rcases (by decide : ∀ t : Fin 4, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) t with rfl | rfl | rfl | rfl <;>
    simp

/-! ### Landing positions after a jog -/

section Shift

/-- **Separation after a jog, two arms.** If two landing positions `L₁, L₂` on the boundary of
`B_R` move to `L₁', L₂'` on the boundary of `B_{R'}`, each by the growth `(4t + 2)(R' - R)` of the
perimeter up to its side `t` plus at most `2E`, then their distance drops by at most `4E`; here in
linear form. -/
theorem sub_le_sub_of_shift {R R' E L₁ L₁' L₂ L₂' : ℤ} (hRR' : R ≤ R')
    (h₁ : (0 < L₁ ∧ L₁ < 4 * R ∧ L₁ + 2 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 2 * (R' - R) + 2 * E) ∨
      (4 * R < L₁ ∧ L₁ < 8 * R ∧ L₁ + 6 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 6 * (R' - R) + 2 * E) ∨
      (8 * R < L₁ ∧ L₁ < 12 * R ∧ L₁ + 10 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 10 * (R' - R) + 2 * E) ∨
      (12 * R < L₁ ∧ L₁ < 16 * R ∧ L₁ + 14 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 14 * (R' - R) + 2 * E))
    (h₂ : (0 < L₂ ∧ L₂ < 4 * R ∧ L₂ + 2 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 2 * (R' - R) + 2 * E) ∨
      (4 * R < L₂ ∧ L₂ < 8 * R ∧ L₂ + 6 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 6 * (R' - R) + 2 * E) ∨
      (8 * R < L₂ ∧ L₂ < 12 * R ∧ L₂ + 10 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 10 * (R' - R) + 2 * E) ∨
      (12 * R < L₂ ∧ L₂ < 16 * R ∧ L₂ + 14 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 14 * (R' - R) + 2 * E)) :
    (L₂ ≤ L₁ → L₁ - L₂ - 4 * E ≤ L₁' - L₂') ∧ (L₁ ≤ L₂ → L₁' - L₂' ≤ L₁ - L₂ + 4 * E) := by
  rcases h₁ with h₁ | h₁ | h₁ | h₁ <;> rcases h₂ with h₂ | h₂ | h₂ | h₂ <;>
    exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- **Separation after a jog, two arms**: `|L₁ - L₂| - 4E ≤ |L₁' - L₂'|`. -/
theorem abs_sub_sub_le_abs_of_shift {R R' E L₁ L₁' L₂ L₂' : ℤ} (hRR' : R ≤ R')
    (h₁ : (0 < L₁ ∧ L₁ < 4 * R ∧ L₁ + 2 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 2 * (R' - R) + 2 * E) ∨
      (4 * R < L₁ ∧ L₁ < 8 * R ∧ L₁ + 6 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 6 * (R' - R) + 2 * E) ∨
      (8 * R < L₁ ∧ L₁ < 12 * R ∧ L₁ + 10 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 10 * (R' - R) + 2 * E) ∨
      (12 * R < L₁ ∧ L₁ < 16 * R ∧ L₁ + 14 * (R' - R) - 2 * E ≤ L₁' ∧
        L₁' ≤ L₁ + 14 * (R' - R) + 2 * E))
    (h₂ : (0 < L₂ ∧ L₂ < 4 * R ∧ L₂ + 2 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 2 * (R' - R) + 2 * E) ∨
      (4 * R < L₂ ∧ L₂ < 8 * R ∧ L₂ + 6 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 6 * (R' - R) + 2 * E) ∨
      (8 * R < L₂ ∧ L₂ < 12 * R ∧ L₂ + 10 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 10 * (R' - R) + 2 * E) ∨
      (12 * R < L₂ ∧ L₂ < 16 * R ∧ L₂ + 14 * (R' - R) - 2 * E ≤ L₂' ∧
        L₂' ≤ L₂ + 14 * (R' - R) + 2 * E)) :
    |L₁ - L₂| - 4 * E ≤ |L₁' - L₂'| := by
  obtain ⟨e₁, e₂⟩ := sub_le_sub_of_shift hRR' h₁ h₂
  rcases le_total L₂ L₁ with h | h
  · have := e₁ h
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ L₁ - L₂)]
    exact this.trans (le_abs_self _)
  · have := e₂ h
    rw [abs_of_nonpos (by omega : L₁ - L₂ ≤ 0)]
    exact (by omega : -(L₁ - L₂) - 4 * E ≤ -(L₁' - L₂')).trans (neg_le_abs _)

/-- **Distance to the corners after a jog.** A landing position at least `S` from the corners
`4 m R` of the boundary of `B_R` moves to a position at least `S - 2E` from the corners `4 m R'`. -/
theorem sub_le_abs_sub_of_shift {R R' E S L L' : ℤ} (hR : 0 ≤ R) (hRR' : R ≤ R')
    (h : (0 < L ∧ L < 4 * R ∧ L + 2 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 2 * (R' - R) + 2 * E) ∨
      (4 * R < L ∧ L < 8 * R ∧ L + 6 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 6 * (R' - R) + 2 * E) ∨
      (8 * R < L ∧ L < 12 * R ∧ L + 10 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 10 * (R' - R) + 2 * E) ∨
      (12 * R < L ∧ L < 16 * R ∧ L + 14 * (R' - R) - 2 * E ≤ L' ∧
        L' ≤ L + 14 * (R' - R) + 2 * E))
    (hS : ∀ m : ℕ, S ≤ |L - 4 * m * R|) (m : ℕ) : S - 2 * E ≤ |L' - 4 * m * R'| := by
  have key : ∀ t : ℕ, (4 * t * R ≤ L ∧ L ≤ 4 * (t + 1) * R ∧
      L + (4 * t + 2) * (R' - R) - 2 * E ≤ L' ∧ L' ≤ L + (4 * t + 2) * (R' - R) + 2 * E) →
      S - 2 * E ≤ |L' - 4 * m * R'| := by
    intro t ⟨h₁, h₂, h₃, h₄⟩
    have e₁ := hS t
    have e₂ := hS (t + 1)
    push_cast at e₁ e₂
    rw [abs_of_nonneg (by linarith)] at e₁
    rw [abs_of_nonpos (by linarith)] at e₂
    rcases le_or_gt m t with hm | hm
    · have : (m : ℤ) * R' ≤ t * R' := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by omega)
      exact le_abs.2 (Or.inl (by nlinarith))
    · have : ((t : ℤ) + 1) * R' ≤ m * R' :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by omega)
      exact le_abs.2 (Or.inr (by nlinarith))
  rcases h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · exact key 0 ⟨by push_cast; linarith, by push_cast; linarith, by push_cast; linarith,
      by push_cast; linarith⟩
  · exact key 1 ⟨by push_cast; linarith, by push_cast; linarith, by push_cast; linarith,
      by push_cast; linarith⟩
  · exact key 2 ⟨by push_cast; linarith, by push_cast; linarith, by push_cast; linarith,
      by push_cast; linarith⟩
  · exact key 3 ⟨by push_cast; linarith, by push_cast; linarith, by push_cast; linarith,
      by push_cast; linarith⟩

/-- **The landing position of an arm after a jog.** An arm to `∂B_R(z)` ending in the bin of a jog
and an arm to `∂B_{R'}(z)` ending in its target: the second landing position is the first one plus
the growth `(4t + 2)(R' - R)` of the perimeter up to the side `t` of the bin, up to `2(W₀ + D)`;
both lie strictly inside the range `[4tR, 4(t + 1)R]` of that side for the first. -/
theorem IsArm.shift_of_jog {ω ω' : Config (LatticeSite 2)} {col : Bool} {z : LatticeSite 2}
    {r R R' M' K' W₀ D S : ℕ} {x d : ℤ} {dir : Fin 2} {lo hi : LatticeSite 2}
    {Bf B B' : Set (LatticeSite 2)} {a b a' b' : LatticeSite 2} {γ : (zdGraph 2).Walk a b}
    {γ' : (zdGraph 2).Walk a' b'} (hγ : IsArm ω col z r (z - R) (z + R) γ)
    (hγ' : IsArm ω' col z r (z - R') (z + R') γ') (hrR : r < R) (hRR' : R ≤ R') (hS : 1 ≤ S)
    (hd : -(D : ℤ) ≤ d ∧ d ≤ D) (hjog : (dir = 1 ∧ lo = ![x, z 1 + R] ∧ hi = ![x + ↑(W₀ + 2 * D), z
        1 + ↑(R' + M')] ∧
        (∀ b, b ∈ Bf ↔ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        (∀ b, b ∈ B ↔ b 1 = z 1 + R ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        ∀ v, v ∈ B' ↔ v 1 = z 1 + R' ∧ x + D + d + K' ≤ v 0 ∧ v 0 ≤ x + D + d + W₀ - K') ∨
      (dir = 0 ∧ lo = ![z 0 + R, x] ∧ hi = ![z 0 + ↑(R' + M'), x + ↑(W₀ + 2 * D)] ∧
        (∀ b, b ∈ Bf ↔ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + ↑(W₀ + 2 * D) ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        (∀ b, b ∈ B ↔ b 0 = z 0 + R ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D + W₀ ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        ∀ v, v ∈ B' ↔ v 0 = z 0 + R' ∧ x + D + d + K' ≤ v 1 ∧ v 1 ≤ x + D + d + W₀ - K') ∨
      (dir = 1 ∧ lo = ![x, z 1 - ↑(R' + M') - cond col 0 1] ∧
        hi = ![x + ↑(W₀ + 2 * D), z 1 - R - cond col 0 1] ∧
        (∀ b, b ∈ Bf ↔ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + ↑(W₀ + 2 * D) ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        (∀ b, b ∈ B ↔ b 1 = z 1 - R - cond col 0 1 ∧ x + D ≤ b 0 ∧ b 0 ≤ x + D + W₀ ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∧
        ∀ v, v ∈ B' ↔ v 1 = z 1 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 0 ∧
          v 0 ≤ x + D + d + W₀ - K') ∨
      (dir = 0 ∧ lo = ![z 0 - ↑(R' + M') - cond col 0 1, x] ∧
        hi = ![z 0 - R - cond col 0 1, x + ↑(W₀ + 2 * D)] ∧
        (∀ b, b ∈ Bf ↔ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + ↑(W₀ + 2 * D) ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        (∀ b, b ∈ B ↔ b 0 = z 0 - R - cond col 0 1 ∧ x + D ≤ b 1 ∧ b 1 ≤ x + D + W₀ ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∧
        ∀ v, v ∈ B' ↔ v 0 = z 0 - R' - cond col 0 1 ∧ x + D + d + K' ≤ v 1 ∧
          v 1 ≤ x + D + d + W₀ - K')) (hb : b ∈ B) (hb' : b' ∈ B') :
    (0 < landingPos (z - R) (z + R) col γ ∧ landingPos (z - R) (z + R) col γ < 4 * R ∧ landingPos (z
        - R) (z + R) col γ + 2 * ((R' : ℤ) - R) - 2 * ((W₀ : ℤ) + D) ≤ landingPos (z - R') (z + R')
        col γ' ∧
        landingPos (z - R') (z + R') col γ' ≤ landingPos (z - R) (z + R) col γ + 2 * ((R' : ℤ) - R)
            + 2 * ((W₀ : ℤ) + D)) ∨
      (4 * R < landingPos (z - R) (z + R) col γ ∧ landingPos (z - R) (z + R) col γ < 8 * R ∧
          landingPos (z - R) (z + R) col γ + 6 * ((R' : ℤ) - R) - 2 * ((W₀ : ℤ) + D) ≤ landingPos (z
          - R') (z + R') col γ' ∧
        landingPos (z - R') (z + R') col γ' ≤ landingPos (z - R) (z + R) col γ + 6 * ((R' : ℤ) - R)
            + 2 * ((W₀ : ℤ) + D)) ∨
      (8 * R < landingPos (z - R) (z + R) col γ ∧ landingPos (z - R) (z + R) col γ < 12 * R ∧
          landingPos (z - R) (z + R) col γ + 10 * ((R' : ℤ) - R) - 2 * ((W₀ : ℤ) + D) ≤ landingPos
          (z - R') (z + R') col γ' ∧
        landingPos (z - R') (z + R') col γ' ≤ landingPos (z - R) (z + R) col γ + 10 * ((R' : ℤ) - R)
            + 2 * ((W₀ : ℤ) + D)) ∨
      (12 * R < landingPos (z - R) (z + R) col γ ∧ landingPos (z - R) (z + R) col γ < 16 * R ∧
          landingPos (z - R) (z + R) col γ + 14 * ((R' : ℤ) - R) - 2 * ((W₀ : ℤ) + D) ≤ landingPos
          (z - R') (z + R') col γ' ∧
        landingPos (z - R') (z + R') col γ' ≤ landingPos (z - R) (z + R) col γ + 14 * ((R' : ℤ) - R)
            + 2 * ((W₀ : ℤ) + D)) := by
  have hc : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rcases hjog with ⟨-, -, -, -, hB, hB'⟩ | ⟨-, -, -, -, hB, hB'⟩ | ⟨-, -, -, -, hB, hB'⟩ |
    ⟨-, -, -, -, hB, hB'⟩ <;> rw [hB] at hb <;> rw [hB'] at hb' <;>
    obtain ⟨hb₁, hb₀, hb₀', hbL, hbR⟩ := hb <;> obtain ⟨hb'₁, hb'₀, hb'₀'⟩ := hb'
  · rw [hγ.landingPos_eq_of_top hrR hb₁, hγ'.landingPos_eq_of_top (by omega) hb'₁]
    exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
  · rw [hγ.landingPos_eq_of_right hrR hb₁, hγ'.landingPos_eq_of_right (by omega) hb'₁]
    exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
  · rw [hγ.landingPos_eq_of_bottom hrR hb₁, hγ'.landingPos_eq_of_bottom (by omega) hb'₁]
    exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
  · rw [hγ.landingPos_eq_of_left hrR hb₁, hγ'.landingPos_eq_of_left (by omega) hb'₁]
    exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩))

end Shift

/-! ### Fences at the new boundary from the separated event (the first gluing, straight) -/

section Straight

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **Fences at `∂B_{R'}(z)` for fixed bins.** Separated arms ending in fixed bins of width `W` on
the sides of `B_R(z)` (separation `s ≥ 4M`, fences of length `2K ≤ 2M` and depth `M`) are continued
straight out (`pow_mul_law_le_law_of_jogs` with `D = 0`, `d = 0`) to arms of `∂B_{R'}(z)`
that are separated at scale `s - 4W` with fences of length `2K'` and depth `M'`, at the cost
`c κ ^ (6j)`. The separation at `R'` is read off a separated family ending in the bins
(`IsArm.shift_of_jog`). -/
theorem pow_mul_law_le_law_separated_of_bins (q : Sym2 (LatticeSite 2) → unitInterval)
    {L : ℕ∞} {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' M' K' W κ : ℕ} {h : ℤ} (hM : 1 ≤ M)
    (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W ≤ M' + K')
    (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R') (hrM : r + M + 1 < R)
    (hWM : 2 * W + 2 ≤ M) (hs : 4 * (M : ℝ) ≤ s)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W : ℤ) - 2 * K'))
    (hκH : (W : ℤ) - 2 * K' ≤ κ * ((W : ℤ) - 2 * K'))
    (hκC : (W : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) (J : Fin j → Set ℤ)
    (t : Fin j → Fin 4) (x : Fin j → ℤ) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R
          ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0 : ℕ)
            : ℤ) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 : ℕ)
            : ℤ) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
        (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  have hrR : r < R := by omega
  have hRR' : R ≤ R' := by omega
  -- the empty case
  by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
      (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
      (∀ i, IsArm ω₀ (σ i) z r (z - R) (z + R) (γ₀ i)) ∧ ArmsOuterSeparated ω₀ σ z R s M K γ₀ ∧
        ∀ i, b₀ i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0
            ≤ x i + ((0 : ℕ) : ℤ) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 : ℕ) : ℤ) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x i + ((0 : ℕ)
            : ℤ) + W ∧
          z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x i + ((0 : ℕ)
            : ℤ) + W ∧
          z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine mul_eq_zero_of_right _ ?_
    convert measure_empty (μ := law q)
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨a, b, γ, h₁, -, -, h₄, h₅, -⟩
    exact hne ⟨ω, a, b, γ, h₁, h₄, h₅⟩
  obtain ⟨ω₀, a₀, b₀, γ₀, hγ₀, hsep₀, hB₀⟩ := hne
  have hjog := fun i => jog_of_bin (σ i) z R R' M' K' W 0 M (t i) (x i) 0
  refine (pow_mul_law_le_law_of_jogs (σ := σ) (z := z) (r := r) (R := R) (s := s) (M := M)
    (K := K) q hCB hσ (R' := R') (M' := M') (K' := K') (W₀ := W) (D := 0) (κ := κ) (S := M)
    (h := h) hM hWK hKM hK' hM' hWM' hh hhR hrM le_rfl (by omega) hs hκV (by simpa using hκH) hκC
    hL J x (fun _ => 0) (fun _ => ⟨by simp, by simp⟩) _ _ _ _ _ _ hjog).trans (measure_mono ?_)
  rintro ω ⟨a, b', γ', hγ', hd', ho', hJ', hB'⟩
  have hsh := fun i => (hγ₀ i).shift_of_jog (hγ' i) hrR hRR' (by omega) ⟨by simp, by simp⟩
    (hjog i) (hB₀ i) (hB' i).1
  refine ⟨a, b', γ', hγ', hd', ho', ⟨fun i k hik => ?_, fun i m => ?_, fun i => (hB' i).2⟩, hJ'⟩
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

/-- A bin in the form of `IsArm.exists_mem_bin` is a bin in the form of `jog_of_bin` with `D = 0`.
-/
theorem mem_bin_zero_of_mem_bin {col : Bool} {z : LatticeSite 2} {R M W : ℕ} {t : Fin 4} {x : ℤ}
    {b : LatticeSite 2}
    (h : (t = 0 ∧ b 1 = z 1 + R ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
        b 0 + 2 * M ≤ z 0 + R) ∨
      (t = 1 ∧ b 0 = z 0 + R ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
        b 1 + 2 * M ≤ z 1 + R) ∨
      (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ x ≤ b 0 ∧ b 0 ≤ x + W ∧ z 0 - R + 2 * M ≤ b 0 ∧
        b 0 + 2 * M ≤ z 0 + R) ∨
      (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W ∧ z 1 - R + 2 * M ≤ b 1 ∧
        b 1 + 2 * M ≤ z 1 + R)) :
    (t = 0 ∧ b 1 = z 1 + R ∧ x + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ x + ((0 : ℕ) : ℤ) + W ∧
        z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (t = 1 ∧ b 0 = z 0 + R ∧ x + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ x + ((0 : ℕ) : ℤ) + W ∧
        z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
      (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ x + ((0 : ℕ) : ℤ) ≤ b 0 ∧
        b 0 ≤ x + ((0 : ℕ) : ℤ) + W ∧ z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
      (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ x + ((0 : ℕ) : ℤ) ≤ b 1 ∧
        b 1 ≤ x + ((0 : ℕ) : ℤ) + W ∧ z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) := by
  simpa only [Nat.cast_zero, add_zero] using h

/-- **The first gluing with fences at the new boundary** (Nolin, Proposition 12, straight case,
with fences at `∂B_{R'}(z)`). For a colour sequence `σ` without packs and ratios `A`, `D` there is
`c₀ > 0` such that for every law with crossing bounds `c` up to scale `L`, every centre `z`, radii
`r < R < R' ≤ L`, bin width `W`, old fences of length `2K` and depth `M`, new fences of length
`2K'` and depth `M'`, separation `s` and inner windows `J`, with `1 ≤ K'`, `4K' ≤ W ≤ K ≤ M`,
`2W + 2 ≤ M`, `W ≤ M'`, `4M ≤ s`, `r + M + 1 < R`, `R + M + 1 + W + M' ≤ R'`, `R' + M' ≤ D R`
and `R ≤ A W`: `c₀ P(j arms to ∂B_R(z) separated at scale s with fences (M, K), inner positions
in J) ≤ P(j arms to ∂B_{R'}(z) separated at scale s - 4W with fences (M', K'), inner positions in
J)`. With `W ≪ M` the new fences are much smaller than the separation, which the later gluings
need. -/
theorem exists_pos_le_law_separated_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ), 1 ≤ K' → 4 * K' ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → W ≤ M' →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → R + M + 1 + W + M' ≤ R' → R' + M' ≤ D * R →
      R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
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
  intro q L hCB z r R R' W M K M' K' s J hK'1 hK'W hWK hKM hWM hWM' hs hrM hRR' hRD hRA hR'L
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
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | ((β i).1 = 0 ∧ b 1 = z
            1 + R ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W
            + 1)) + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) -
            R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) + W ∧
            z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
          ((β i).1 = 1 ∧ b 0 = z 0 + R ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R +
              (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ ((if (β i).1 = 0 ∨ (β
              i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) + W ∧
            z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R) ∨
          ((β i).1 = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0
              else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ ((if (β
              i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 :
              ℕ) : ℤ) + W ∧
            z 0 - R + 2 * M ≤ b 0 ∧ b 0 + 2 * M ≤ z 0 + R) ∨
          ((β i).1 = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ ((if (β i).1 = 0 ∨ (β i).1 = 2 then z 0
              else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 : ℕ) : ℤ) ≤ b 1 ∧ b 1 ≤ ((if (β
              i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W + 1)) + ((0 :
              ℕ) : ℤ) + W ∧
            z 1 - R + 2 * M ≤ b 1 ∧ b 1 + 2 * M ≤ z 1 + R)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} with hE
  -- every separated configuration has its ends in some bins
  have hcover : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      ∑ β, law q (E β) := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    rintro ω ⟨a, b, γ, hγ, hd, ho, hsep, hJ⟩
    have hsep' := hsep.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)
    choose t n hn hb using fun i => (hγ i).exists_mem_bin hrR (by omega) hW hRA (hsep'.2 i)
    rw [mem_iUnion]
    refine ⟨fun i => (t i, ⟨n i, hn i⟩), ?_⟩
    rw [hE]
    exact ⟨a, b, γ, hγ, hd, ho, hsep, fun i => mem_bin_zero_of_mem_bin (hb i), hJ⟩
  -- the gluing for each choice of bins
  have hβ : ∀ β, c κ ^ (6 * j) * law q (E β) ≤ law q {ω : Config (LatticeSite 2) |
      ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧ ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    intro β
    rw [hE]
    exact pow_mul_law_le_law_separated_of_bins q hCB hσ (h := R + M + 1) (by omega) hWK hKM
      (by omega) (by omega) (by omega) le_rfl (by omega) hrM hWM hs hκV hκH hκC hR'L J
      (fun i => (β i).1)
      (fun i => (if (β i).1 = 0 ∨ (β i).1 = 2 then z 0 else z 1) - R + (((β i).2 : ℕ) : ℤ) * (W +
          1))
  refine (mul_le_mul' le_rfl hcover).trans ?_
  rw [Finset.mul_sum]
  calc ∑ β, c κ ^ (6 * j) / (((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞) * law q (E β)
      ≤ ∑ _β : Fin j → Fin 4 × Fin (2 * A + 1), law q {ω : Config (LatticeSite 2) |
          ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
            (landingPos (z - R') (z + R') (σ k) (γ k))
            (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R' (s - 4 * W) M' K' γ ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i} *
            ((((4 * (2 * A + 1)) ^ j : ℕ) : ℝ≥0∞))⁻¹ := by
        refine Finset.sum_le_sum fun β _ => ?_
        rw [div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul_left (hβ β) _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hX0 hXt, mul_one]

/-- **The first gluing with fences at the new boundary**, for `outerSeparatedArmEvent`:
`c₀ P(outerSeparatedArmEvent σ z r R s M K) ≤ P(outerSeparatedArmEvent σ z r R' (s - 4W) M' K')`
under the hypotheses of `exists_pos_le_law_separated_of_separated`. -/
theorem exists_pos_le_law_outerSeparatedArmEvent_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' : ℕ) (s : ℝ),
      1 ≤ K' → 4 * K' ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → W ≤ M' →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → R + M + 1 + W + M' ≤ R' → R' + M' ≤ D * R →
      R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q (outerSeparatedArmEvent σ z r R s M K) ≤
        law q (outerSeparatedArmEvent σ z r R' (s - 4 * W) M' K') := by
  obtain ⟨c₀, hc₀, h⟩ := exists_pos_le_law_separated_of_separated σ hσ c A D
  refine ⟨c₀, hc₀, fun q L hCB z r R R' W M K M' K' s h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ => ?_⟩
  have := h q L hCB z r R R' W M K M' K' s (fun _ => univ) h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · congr 2
    ext ω
    exact ⟨fun ⟨a, b, γ, h₁, h₂, h₃, h₄⟩ => ⟨a, b, γ, h₁, h₂, h₃, h₄, fun _ => mem_univ _⟩,
      fun ⟨a, b, γ, h₁, h₂, h₃, h₄, _⟩ => ⟨a, b, γ, h₁, h₂, h₃, h₄⟩⟩
  · congr 1
    ext ω
    exact ⟨fun ⟨a, b, γ, h₁, h₂, h₃, h₄, _⟩ => ⟨a, b, γ, h₁, h₂, h₃, h₄⟩,
      fun ⟨a, b, γ, h₁, h₂, h₃, h₄⟩ => ⟨a, b, γ, h₁, h₂, h₃, h₄, fun _ => mem_univ _⟩⟩


end Straight

/-! ### Separation from windows on the sides -/

section Windows

/-- **Landing positions of two ends in windows on the sides**, integer form. Two ends on sides
`t₁, t₂` of `B_ρ`, with coordinates `p₁, p₂` along their sides at least `g` from the corners, land
at least `2g - 1` apart if they lie on different sides or, on one side, at least `g` apart. -/
theorem le_abs_sub_of_windows {z0 z1 ρ g L₁ L₂ p₁ p₂ e₁ e₂ : ℤ} {t₁ t₂ : Fin 4}
    (he₁ : 0 ≤ e₁ ∧ e₁ ≤ 1) (he₂ : 0 ≤ e₂ ∧ e₂ ≤ 1)
    (h₁ : (t₁ = 0 ∧ L₁ = 8 * ρ + 2 * (z0 + ρ) - (2 * p₁ + e₁) ∧ z0 - ρ + g ≤ p₁ ∧
        p₁ + g ≤ z0 + ρ) ∨
      (t₁ = 1 ∧ L₁ = 4 * ρ + (2 * p₁ + e₁) - 2 * (z1 - ρ) ∧ z1 - ρ + g ≤ p₁ ∧ p₁ + g ≤ z1 + ρ) ∨
      (t₁ = 2 ∧ L₁ = 2 * p₁ + e₁ - 2 * (z0 - ρ) ∧ z0 - ρ + g ≤ p₁ ∧ p₁ + g ≤ z0 + ρ) ∨
      (t₁ = 3 ∧ L₁ = 12 * ρ + 2 * (z1 + ρ) - (2 * p₁ + e₁) ∧ z1 - ρ + g ≤ p₁ ∧ p₁ + g ≤ z1 + ρ))
    (h₂ : (t₂ = 0 ∧ L₂ = 8 * ρ + 2 * (z0 + ρ) - (2 * p₂ + e₂) ∧ z0 - ρ + g ≤ p₂ ∧
        p₂ + g ≤ z0 + ρ) ∨
      (t₂ = 1 ∧ L₂ = 4 * ρ + (2 * p₂ + e₂) - 2 * (z1 - ρ) ∧ z1 - ρ + g ≤ p₂ ∧ p₂ + g ≤ z1 + ρ) ∨
      (t₂ = 2 ∧ L₂ = 2 * p₂ + e₂ - 2 * (z0 - ρ) ∧ z0 - ρ + g ≤ p₂ ∧ p₂ + g ≤ z0 + ρ) ∨
      (t₂ = 3 ∧ L₂ = 12 * ρ + 2 * (z1 + ρ) - (2 * p₂ + e₂) ∧ z1 - ρ + g ≤ p₂ ∧ p₂ + g ≤ z1 + ρ))
    (hgap : t₁ = t₂ → p₁ + g ≤ p₂ ∨ p₂ + g ≤ p₁) :
    2 * g - 1 ≤ |L₁ - L₂| := by
  rw [le_abs]
  rcases h₁ with ⟨ht₁, h₁⟩ | ⟨ht₁, h₁⟩ | ⟨ht₁, h₁⟩ | ⟨ht₁, h₁⟩ <;>
    rcases h₂ with ⟨ht₂, h₂⟩ | ⟨ht₂, h₂⟩ | ⟨ht₂, h₂⟩ | ⟨ht₂, h₂⟩ <;>
    first
    | (have := hgap (ht₁.trans ht₂.symm); omega)
    | omega

/-- **Distance to the corners of an end in a window on a side**, integer form. -/
theorem le_abs_sub_corner_of_window {z0 z1 ρ g L p e : ℤ} {t : Fin 4} (he : 0 ≤ e ∧ e ≤ 1)
    (hg : 1 ≤ g)
    (h : (t = 0 ∧ L = 8 * ρ + 2 * (z0 + ρ) - (2 * p + e) ∧ z0 - ρ + g ≤ p ∧ p + g ≤ z0 + ρ) ∨
      (t = 1 ∧ L = 4 * ρ + (2 * p + e) - 2 * (z1 - ρ) ∧ z1 - ρ + g ≤ p ∧ p + g ≤ z1 + ρ) ∨
      (t = 2 ∧ L = 2 * p + e - 2 * (z0 - ρ) ∧ z0 - ρ + g ≤ p ∧ p + g ≤ z0 + ρ) ∨
      (t = 3 ∧ L = 12 * ρ + 2 * (z1 + ρ) - (2 * p + e) ∧ z1 - ρ + g ≤ p ∧ p + g ≤ z1 + ρ))
    (m : ℕ) : 2 * g - 1 ≤ |L - 4 * m * ρ| := by
  have key : ∀ k : ℕ, (4 * k * ρ + 2 * g - 1 ≤ L ∧ L + 2 * g - 1 ≤ 4 * (k + 1) * ρ) →
      2 * g - 1 ≤ |L - 4 * m * ρ| := by
    intro k ⟨h₁, h₂⟩
    have hρ : 0 ≤ ρ := by nlinarith
    rcases le_or_gt m k with hm | hm
    · have : (m : ℤ) * ρ ≤ k * ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hρ
      exact le_abs.2 (Or.inl (by nlinarith))
    · have : ((k : ℤ) + 1) * ρ ≤ m * ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hρ
      exact le_abs.2 (Or.inr (by nlinarith))
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact key 2 ⟨by push_cast; omega, by push_cast; omega⟩
  · exact key 1 ⟨by push_cast; omega, by push_cast; omega⟩
  · exact key 0 ⟨by push_cast; omega, by push_cast; omega⟩
  · exact key 3 ⟨by push_cast; omega, by push_cast; omega⟩

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r : ℕ}

/-- **Arms ending in separated windows are separated.** Let the arms of a family to `∂B_ρ(z)` end in
windows `[α i, β i]` on the sides `t i` (`0` top, `1` right, `2` bottom, `3` left; coordinates along
the side), at least `g` from the corners, windows on one side at least `g` apart. Then any two
landing positions are at least `2g - 1` apart and every landing position is at least `2g - 1`
from the doubled corners. -/
theorem le_abs_landingPos_sub_of_windows {ω : Config (LatticeSite 2)} {ρ : ℕ}
    {a b : Fin j → LatticeSite 2} {γ : ∀ i, (zdGraph 2).Walk (a i) (b i)}
    (hγ : ∀ i, IsArm ω (σ i) z r (z - ρ) (z + ρ) (γ i)) (hrρ : r < ρ) {g : ℤ} (hg : 1 ≤ g)
    (t : Fin j → Fin 4) (α β : Fin j → ℤ)
    (hwin : ∀ i, (t i = 0 ∧ b i 1 = z 1 + ρ ∧ α i ≤ b i 0 ∧ b i 0 ≤ β i) ∨
      (t i = 1 ∧ b i 0 = z 0 + ρ ∧ α i ≤ b i 1 ∧ b i 1 ≤ β i) ∨
      (t i = 2 ∧ b i 1 = z 1 - ρ - cond (σ i) 0 1 ∧ α i ≤ b i 0 ∧ b i 0 ≤ β i) ∨
      (t i = 3 ∧ b i 0 = z 0 - ρ - cond (σ i) 0 1 ∧ α i ≤ b i 1 ∧ b i 1 ≤ β i))
    (hcor : ∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - ρ + g ≤ α i ∧
      β i + g ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + ρ)
    (hgap : ∀ i k, i ≠ k → t i = t k → β i + g ≤ α k ∨ β k + g ≤ α i) :
    (∀ i k, i ≠ k → 2 * g - 1 ≤ |landingPos (z - ρ) (z + ρ) (σ i) (γ i) -
      landingPos (z - ρ) (z + ρ) (σ k) (γ k)|) ∧
    ∀ i (m : ℕ), 2 * g - 1 ≤ |landingPos (z - ρ) (z + ρ) (σ i) (γ i) - 4 * m * ρ| := by
  have he : ∀ i, 0 ≤ cond (σ i) (0 : ℤ) 1 ∧ cond (σ i) (0 : ℤ) 1 ≤ 1 := fun i => by
    cases σ i <;> simp
  -- the position of each end along its side
  have hpos : ∀ i, ∃ p : ℤ, α i ≤ p ∧ p ≤ β i ∧
      ((t i = 0 ∧ landingPos (z - ρ) (z + ρ) (σ i) (γ i) =
          8 * ρ + 2 * (z 0 + ρ) - (2 * p + cond (σ i) 0 1) ∧ z 0 - ρ + g ≤ p ∧ p + g ≤ z 0 + ρ) ∨
        (t i = 1 ∧ landingPos (z - ρ) (z + ρ) (σ i) (γ i) =
          4 * ρ + (2 * p + cond (σ i) 0 1) - 2 * (z 1 - ρ) ∧ z 1 - ρ + g ≤ p ∧ p + g ≤ z 1 + ρ) ∨
        (t i = 2 ∧ landingPos (z - ρ) (z + ρ) (σ i) (γ i) =
          2 * p + cond (σ i) 0 1 - 2 * (z 0 - ρ) ∧ z 0 - ρ + g ≤ p ∧ p + g ≤ z 0 + ρ) ∨
        (t i = 3 ∧ landingPos (z - ρ) (z + ρ) (σ i) (γ i) =
          12 * ρ + 2 * (z 1 + ρ) - (2 * p + cond (σ i) 0 1) ∧ z 1 - ρ + g ≤ p ∧
            p + g ≤ z 1 + ρ)) := by
    intro i
    have hc := hcor i
    rcases hwin i with ⟨ht, hb, h₁, h₂⟩ | ⟨ht, hb, h₁, h₂⟩ | ⟨ht, hb, h₁, h₂⟩ | ⟨ht, hb, h₁, h₂⟩ <;>
      simp only [ht, Fin.isValue, true_or, or_true, ite_true, ite_false, Fin.reduceEq,
        or_self] at hc
    · exact ⟨b i 0, h₁, h₂, Or.inl ⟨ht, (hγ i).landingPos_eq_of_top hrρ hb, by omega, by omega⟩⟩
    · exact ⟨b i 1, h₁, h₂, Or.inr (Or.inl ⟨ht, (hγ i).landingPos_eq_of_right hrρ hb, by omega,
        by omega⟩)⟩
    · exact ⟨b i 0, h₁, h₂, Or.inr (Or.inr (Or.inl ⟨ht, (hγ i).landingPos_eq_of_bottom hrρ hb,
        by omega, by omega⟩))⟩
    · exact ⟨b i 1, h₁, h₂, Or.inr (Or.inr (Or.inr ⟨ht, (hγ i).landingPos_eq_of_left hrρ hb,
        by omega, by omega⟩))⟩
  choose p hpα hpβ hp using hpos
  refine ⟨fun i k hik => le_abs_sub_of_windows (he i) (he k) (hp i) (hp k) fun htt => ?_,
    fun i m => le_abs_sub_corner_of_window (he i) hg (hp i) m⟩
  rcases hgap i k hik htt with h | h
  · exact Or.inl (by linarith [hpβ i, hpα k])
  · exact Or.inr (by linarith [hpβ k, hpα i])

end Windows

/-! ### Window-to-window steps -/

section WindowSteps

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- **The bin of a coordinate in a window.** A coordinate `ℓ ∈ [α, β]` lies in one of the `N` bins
`[α + n (W + 1), α + n (W + 1) + W]`, `n < N`, when `β - α + 1 ≤ N (W + 1)`. -/
theorem exists_lt_mem_bin {α β ℓ : ℤ} {W N : ℕ} (h₁ : α ≤ ℓ) (h₂ : ℓ ≤ β)
    (hN : β - α + 1 ≤ N * ((W : ℤ) + 1)) :
    ∃ n : ℕ, n < N ∧ α + n * ((W : ℤ) + 1) ≤ ℓ ∧ ℓ ≤ α + n * ((W : ℤ) + 1) + W := by
  have hW1 : (0 : ℤ) < W + 1 := by positivity
  have hq0 : 0 ≤ (ℓ - α) / (W + 1) := Int.ediv_nonneg (by omega) hW1.le
  have hq1 : (ℓ - α) / (W + 1) * (W + 1) ≤ ℓ - α := Int.ediv_mul_le _ hW1.ne'
  have hq2 : ℓ - α < ((ℓ - α) / (W + 1) + 1) * (W + 1) := Int.lt_ediv_add_one_mul_self _ hW1
  have hq3 : (ℓ - α) / (W + 1) < N := Int.ediv_lt_of_lt_mul hW1 (by linarith)
  rw [add_one_mul] at hq2
  refine ⟨((ℓ - α) / (W + 1)).toNat, by omega, ?_, ?_⟩ <;> rw [Int.toNat_of_nonneg hq0] <;>
    nlinarith

/-- **A window-to-window step for fixed bins.** Separated arms (separation `s ≥ 4S`, fences
`(M, K)`) ending in windows `[α i, β i]` on the sides `t i` of `B_R(z)` and in the bins
`[x i + D, x i + D + W]` are moved along their sides by `d i` (`|d i| ≤ D`) and capped at
`∂B_{R'}(z)`: they end in the windows `[α i + d i, β i + d i + W]` with fences `(M', K')`, separated
at scale `2g' - 1` when these windows are at least `g'` from the corners and from each other on one
side. Cost `c κ ^ (6j)`. -/
theorem pow_mul_law_le_law_windows_of_bins (q : Sym2 (LatticeSite 2) → unitInterval)
    {L : ℕ∞} {c : ℕ → ℝ≥0∞} (hCB : CrossingBounds q L c)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' M' K' W D κ S : ℕ} {h g' : ℤ}
    (hM : 1 ≤ M) (hWK : W ≤ K) (hKM : K ≤ M) (hK' : 2 * K' + 1 ≤ W) (hM' : 2 ≤ M')
    (hWM' : W ≤ M' + K') (hh : (R : ℤ) + M + 1 ≤ h) (hhR : h + ((W : ℤ) - 2 * K') + M' ≤ R')
    (hrM : r + M + 1 < R) (hMS : M ≤ S) (hWS : 2 * (W + 2 * D) + 2 ≤ S) (hs : 4 * (S : ℝ) ≤ s)
    (hκV : (R' : ℤ) + M' - R ≤ κ * ((W : ℤ) - 2 * K'))
    (hκH : 2 * (D : ℤ) + W - 2 * K' ≤ κ * ((W : ℤ) - 2 * K'))
    (hκC : (W : ℤ) ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L) (J : Fin j → Set ℤ)
    (t : Fin j → Fin 4) (x α β d : Fin j → ℤ) (hd : ∀ i, -(D : ℤ) ≤ d i ∧ d i ≤ D)
    (hxα : ∀ i, α i ≤ x i + D) (hg' : 1 ≤ g')
    (hcor' : ∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R' + g' ≤ α i + d i ∧
      β i + d i + W + g' ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R')
    (hgap' : ∀ i k, i ≠ k → t i = t k →
      β i + d i + W + g' ≤ α k + d k ∨ β k + d k + W + g' ≤ α i + d i) :
    c κ ^ (6 * j) * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
        (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R
          ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧ (∀ i, b i ∈ {b :
              LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)}) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
      (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
      (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
      (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
        (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
      ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R' ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 1 ∧ b 0 = z 0 + R' ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W) ∨
          (t i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W)}) ∧
      ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  have hrR : r < R := by omega
  have hRR' : R ≤ R' := by omega
  -- the empty case
  by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
      (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
      (∀ i, b₀ i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧ ∀ i, b₀ i ∈ {b :
              LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 0 ∧ b 0 ≤ x i + D + W ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ x i + D ≤ b 1 ∧ b 1 ≤ x i + D + W ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)}
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine mul_eq_zero_of_right _ ?_
    convert measure_empty (μ := law q)
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨a, b, γ, -, -, -, -, h₅, h₆, -⟩
    exact hne ⟨ω, a, b, γ, h₅, h₆⟩
  obtain ⟨ω₀, a₀, b₀, γ₀, hW₀, hB₀⟩ := hne
  -- the bins start inside the windows
  have hxβ : ∀ i, x i + D ≤ β i ∧ α i ≤ x i + D + W := by
    intro i
    have h₁ := hW₀ i
    have h₂ := hB₀ i
    simp only [mem_ofPred_eq] at h₁ h₂
    rcases h₁ with ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ <;>
      rcases h₂ with ⟨ht', -, h₂, h₂', -⟩ | ⟨ht', -, h₂, h₂', -⟩ | ⟨ht', -, h₂, h₂', -⟩ |
        ⟨ht', -, h₂, h₂', -⟩ <;>
      exact ⟨by omega, by omega⟩
  have hjog := fun i => jog_of_bin (σ i) z R R' M' K' W D S (t i) (x i) (d i)
  refine le_trans (mul_le_mul' le_rfl (measure_mono fun ω hω => ?_))
    ((pow_mul_law_le_law_of_jogs (σ := σ) (z := z) (r := r) (R := R) (s := s) (M := M)
    (K := K) q hCB hσ (R' := R') (M' := M') (K' := K') (W₀ := W) (D := D) (κ := κ) (S := S)
    (h := h) hM hWK hKM hK' hM' hWM' hh hhR hrM hMS hWS hs hκV hκH hκC hL J x d hd _ _ _ _ _ _
    hjog).trans (measure_mono ?_))
  · obtain ⟨a, b, γ, h₁, h₂, h₃, h₄, -, h₆, h₇⟩ := hω
    exact ⟨a, b, γ, h₁, h₂, h₃, h₄, h₆, h₇⟩
  rintro ω ⟨a, b', γ', hγ', hd', ho', hJ', hB'⟩
  -- the new ends lie in the new windows
  have hwin : ∀ i, (t i = 0 ∧ b' i 1 = z 1 + R' ∧ α i + d i ≤ b' i 0 ∧
        b' i 0 ≤ β i + d i + W) ∨
      (t i = 1 ∧ b' i 0 = z 0 + R' ∧ α i + d i ≤ b' i 1 ∧ b' i 1 ≤ β i + d i + W) ∨
      (t i = 2 ∧ b' i 1 = z 1 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b' i 0 ∧
        b' i 0 ≤ β i + d i + W) ∨
      (t i = 3 ∧ b' i 0 = z 0 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b' i 1 ∧
        b' i 1 ≤ β i + d i + W) := by
    intro i
    have h := (hB' i).1
    have hx := hxβ i
    have hx' := hxα i
    simp only [mem_ofPred_eq] at h
    rcases h with ⟨ht, h₁, h₂, h₃⟩ | ⟨ht, h₁, h₂, h₃⟩ | ⟨ht, h₁, h₂, h₃⟩ | ⟨ht, h₁, h₂, h₃⟩
    · exact Or.inl ⟨ht, h₁, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨ht, h₁, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ht, h₁, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ht, h₁, by omega, by omega⟩))
  obtain ⟨hs₁, hs₂⟩ := le_abs_landingPos_sub_of_windows hγ' (by omega) hg' t
    (fun i => α i + d i) (fun i => β i + d i + W) hwin
    (fun i => ⟨(hcor' i).1, by have := (hcor' i).2; linarith⟩)
    (fun i k hik htt => by
      rcases hgap' i k hik htt with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith))
  refine ⟨a, b', γ', hγ', hd', ho', ⟨fun i k hik => ?_, fun i m => ?_, fun i => (hB' i).2⟩,
    fun i => hwin i, hJ'⟩
  · rw [← Int.cast_abs]
    exact_mod_cast hs₁ i k hik
  · rw [← Int.cast_abs]
    exact_mod_cast hs₂ i m

/-- **The window-to-window step** (the gluing that A3b-3 iterates). For a colour sequence `σ`
without packs and ratios `A`, `N` there is `c₀ > 0` such that for every law with crossing bounds `c`
up to scale `L`: separated arms (separation `s ≥ 4S`, fences `(M, K)`) ending in windows
`[α i, β i]` on the sides `t i` of `B_R(z)` (at least `2S` from the corners, each covered by `N`
bins of width `W`) are moved along their sides by `d i` (`|d i| ≤ D`) and end, with fences
`(M', K')`, in the windows `[α i + d i, β i + d i + W]` of `∂B_{R'}(z)`, separated at scale
`2g' - 1` when these windows are at least `g'` from the corners and from each other on one side:
`c₀ P(windows at R) ≤ P(windows at R')`. The constant depends only on `σ`, `c`, `A`, `N`; with
windows and fences proportional to the radius it does not depend on the separation scale of the
first gluing. -/
theorem exists_pos_le_law_windows_of_windows {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S : ℕ) (s : ℝ) (g' : ℤ)
      (J : Fin j → Set ℤ) (t : Fin j → Fin 4) (α β d : Fin j → ℤ),
      1 ≤ K' → 4 * K' ≤ W → W ≤ K → K ≤ M → M ≤ S → 2 * (W + 2 * D) + 2 ≤ S → W ≤ M' →
      4 * (S : ℝ) ≤ s → r + M + 1 < R → R + M + 1 + W + M' ≤ R' → R' + M' ≤ R + A * W →
      D ≤ A * W → (R' : ℕ∞) ≤ L → (∀ i, -(D : ℤ) ≤ d i ∧ d i ≤ D) →
      (∀ i, β i - α i + 1 ≤ N * ((W : ℤ) + 1)) →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + 2 * S ≤ α i ∧
        β i + 2 * S ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      1 ≤ g' →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R' + g' ≤ α i + d i ∧
        β i + d i + W + g' ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R') →
      (∀ i k, i ≠ k → t i = t k →
        β i + d i + W + g' ≤ α k + d k ∨ β k + d k + W + g' ≤ α i + d i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 +
            R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite 2
            | (t i = 0 ∧ b 1 = z 1 + R' ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 1 ∧ b 0 = z 0 + R' ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W) ∨
          (t i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  set κ : ℕ := 4 * A + 2 with hκeq
  by_cases hc : 0 < c κ
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  have hX0 : ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    positivity
  have hXt : ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨c κ ^ (6 * j) / ((((N + 1) ^ j : ℕ)) : ℝ≥0∞),
    ENNReal.div_pos (pow_ne_zero _ hc.ne') hXt, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S s g' J t α β d hK'1 hK'W hWK hKM hMS hWS hWM' hs hrM
    hRR' hRA hDA hR'L hd hN hcor hg' hcor' hgap'
  have hW : 1 ≤ W := by omega
  -- the aspect ratios
  have e₀ : (0 : ℤ) ≤ (A : ℤ) * ((W : ℤ) - 4 * K') := mul_nonneg (by positivity) (by omega)
  have hRA' : ((R' + M' : ℕ) : ℤ) ≤ ((R + A * W : ℕ) : ℤ) := by exact_mod_cast hRA
  have hDA' : ((D : ℕ) : ℤ) ≤ ((A * W : ℕ) : ℤ) := by exact_mod_cast hDA
  push_cast at hRA' hDA'
  have hκV : (R' : ℤ) + M' - R ≤ κ * ((W : ℤ) - 2 * K') := by
    rw [hκeq]
    push_cast
    nlinarith
  have hκH : 2 * (D : ℤ) + W - 2 * K' ≤ κ * ((W : ℤ) - 2 * K') := by
    rw [hκeq]
    push_cast
    nlinarith
  have hκC : (W : ℤ) ≤ κ * ((M' : ℤ) - 1) := by
    have : (2 : ℤ) * ((M' : ℤ) - 1) ≤ κ * ((M' : ℤ) - 1) :=
      mul_le_mul_of_nonneg_right (by rw [hκeq]; push_cast; nlinarith) (by omega)
    omega
  -- the separated event with ends in given bins
  set E : (Fin j → Fin (N + 1)) → Set (Config (LatticeSite 2)) :=
      fun n => {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 +
            R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧ (∀ i, b i ∈ {b :
              LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W
              + 1) - D) + D ≤ b 0 ∧ b 0 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) - D) + D
              + W ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) - D) + D ≤ b 1
              ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) - D) + D + W ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W +
              1) - D) + D ≤ b 0 ∧ b 0 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) - D) + D +
              W ∧
            z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W +
              1) - D) + D ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) - D) + D +
              W ∧
            z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} with hE
  -- every end in a window lies in a bin of the window
  have hbin : ∀ i (b : LatticeSite 2), b ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0
      ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)} → ∃ n : ℕ, n < N + 1 ∧
      b ∈ {b : LatticeSite 2 |
        (t i = 0 ∧ b 1 = z 1 + R ∧ α i + (n : ℤ) * (W + 1) - D + D ≤ b 0 ∧
          b 0 ≤ α i + (n : ℤ) * (W + 1) - D + D + W ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ α i + (n : ℤ) * (W + 1) - D + D ≤ b 1 ∧
          b 1 ≤ α i + (n : ℤ) * (W + 1) - D + D + W ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i + (n : ℤ) * (W + 1) - D + D ≤ b 0 ∧
          b 0 ≤ α i + (n : ℤ) * (W + 1) - D + D + W ∧
          z 0 - R + 2 * S ≤ b 0 ∧ b 0 + 2 * S ≤ z 0 + R) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i + (n : ℤ) * (W + 1) - D + D ≤ b 1 ∧
          b 1 ≤ α i + (n : ℤ) * (W + 1) - D + D + W ∧
          z 1 - R + 2 * S ≤ b 1 ∧ b 1 + 2 * S ≤ z 1 + R)} := by
    intro i b hb
    have hc' := hcor i
    simp only [mem_ofPred_eq] at hb
    rcases hb with ⟨ht, h₁, h₂, h₃⟩ | ⟨ht, h₁, h₂, h₃⟩ | ⟨ht, h₁, h₂, h₃⟩ | ⟨ht, h₁, h₂, h₃⟩ <;>
      simp only [ht, Fin.isValue, true_or, or_true, ite_true, ite_false, Fin.reduceEq,
        or_self] at hc'
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inl ⟨ht, h₁, by omega, by omega, by omega, by omega⟩⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inl ⟨ht, h₁, by omega, by omega, by omega, by omega⟩)⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inr (Or.inl ⟨ht, h₁, by omega, by omega, by omega,
        by omega⟩))⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inr (Or.inr ⟨ht, h₁, by omega, by omega, by omega,
        by omega⟩))⟩
  have hcover : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 +
            R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤ ∑ n, law q (E n) := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    rintro ω ⟨a, b, γ, hγ, hd', ho, hsep, hw, hJ⟩
    choose n hn hb using fun i => hbin i (b i) (hw i)
    rw [mem_iUnion]
    refine ⟨fun i => ⟨n i, hn i⟩, ?_⟩
    rw [hE]
    exact ⟨a, b, γ, hγ, hd', ho, hsep, hw, hb, hJ⟩
  -- the gluing for each choice of bins
  have hβ : ∀ n, c κ ^ (6 * j) * law q (E n) ≤ law q {ω : Config (LatticeSite 2) |
      ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite 2
            | (t i = 0 ∧ b 1 = z 1 + R' ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 1 ∧ b 0 = z 0 + R' ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W) ∨
          (t i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    intro n
    rw [hE]
    exact pow_mul_law_le_law_windows_of_bins q hCB hσ (h := R + M + 1) (by omega) hWK hKM
      (by omega) (by omega) (by omega) le_rfl (by omega) hrM hMS hWS hs hκV hκH hκC hR'L J t
      (fun i => α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) - D) α β d hd
      (fun i => by have : (0 : ℤ) ≤ ((n i : ℕ) : ℤ) * (W + 1) := by positivity
                   omega) hg' hcor' hgap'
  refine (mul_le_mul' le_rfl hcover).trans ?_
  rw [Finset.mul_sum]
  calc ∑ n, c κ ^ (6 * j) / ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) * law q (E n)
      ≤ ∑ _n : Fin j → Fin (N + 1), law q {ω : Config (LatticeSite 2) |
          ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
          (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
            (landingPos (z - R') (z + R') (σ k) (γ k))
            (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
          ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
              2 | (t i = 0 ∧ b 1 = z 1 + R' ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 1 ∧ b 0 = z 0 + R' ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W) ∨
          (t i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 0 ∧ b 0 ≤ β i + d i + W) ∨
          (t i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α i + d i ≤ b 1 ∧ b 1 ≤ β i + d i + W)}) ∧
          ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ((((N + 1) ^ j : ℕ) : ℝ≥0∞))⁻¹ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul_left (hβ n) _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hX0 hXt, mul_one]


end WindowSteps

end PercLib.Models.Planar
