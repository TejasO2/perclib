/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-24. No upstream proof is copied.
Mathematical reference: P. Nolin, Near-critical percolation in two dimensions, Electron. J.
Probab. 13 (2008), paper no. 55, Section 4.4 (gluing of separated arms, Proposition 12, and the
arms landing in prescribed windows).
-/
module

public import PercLib.Models.Planar.Arms.CapGluing
public import PercLib.Models.Planar.Arms.TurnCorridors

/-!
# Gluing over disjoint regions; moves of arms between windows, with turns at the corners

Arms separated at the outer boundary of `B_R(z)` are continued to the boundary of `B_{R'}(z)`
through corridors that lie in pairwise disjoint regions; each arm is moved along its side (a jog)
or round the next corner counterclockwise (a turn), and receives a new outer fence of any size.

## Main results

* `law_mul_prod_le_law_of_regions`: the gluing through given corridors
  (`law_mul_prod_le_law_of_corridors`) when each corridor, its region and the boxes about the
  possible ends of its arm lie in a region of its own, the regions pairwise disjoint.
* `pow_mul_law_le_law_of_regions`: for fixed bins, `c κ ^ (6j) P(separated, ends in B) ≤
  P(arms to ∂B_{R'}(z), ends in B' with fences (M', K'))`, given one corridor per arm.
* `disjoint_regions_of_moves`: the regions of the moves of two arms (one formula for each side and
  kind of move) are disjoint when their windows are far enough from the corners and from each
  other and a turning arm is the last of its side in counterclockwise order.
* `exists_corridor_move`: the corridor of one move (a jog with a wide cap on any side, or a turn
  at any corner) in its region.
* `exists_pos_le_law_windows_of_moves`: **a stage of moves between windows**, `c₀ P(separated
  arms in windows at R) ≤ P(separated arms in the moved windows at R', fences (M', K'))`, with
  `c₀` depending only on `σ`, `c` and the ratios `A`, `N`. With no turn it is the
  window-to-window step with fences of any size (`W + K' ≤ M'`), which can be iterated with the
  same fences at every step.
* `exists_pos_le_law_windows_of_stages`: **a chain of `n` stages**, `c₀ P(separated arms in the
  windows of stage 0 at ρ 0) ≤ P(separated arms in the windows of stage n at ρ n)`, with the same
  fences `(M, K)` throughout; `c₀` depends only on `σ`, `c`, `A`, `N`, `n`. Given a plan of moves
  from the bins of the separated arms to prescribed windows, this is the rotation into fixed
  windows.
* `law_le_sum_law_windows_of_separated`: the separated event is covered by the events in which
  the arms end in given bins (the windows a chain starts from).

## Implementation notes

The regions are rectangles given by one formula for each side and kind of move; their
disjointness is checked case by case (`disjoint_regions_of_moves_0` to `_7`) by `omega`.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Models.Planar

/-! ### Gluing over disjoint regions -/

section Regions

variable {j : ℕ} {σ : Fin j → Bool} {z : LatticeSite 2} {r R : ℕ} {s : ℝ} {M K : ℕ}

/-- The box of radius `M` about a point lies in the box of radius `M + 1` about it, enlarged at
the upper corner. -/
theorem Icc_sub_add_subset_Icc_sub_add_succ (b : LatticeSite 2) (M : ℕ) :
    Icc (b - (M : LatticeSite 2)) (b + M) ⊆
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) := by
  refine Icc_subset_Icc le_rfl fun m => ?_
  simp only [Pi.add_apply, Pi.natCast_apply]
  push_cast
  omega

/-- **Gluing over disjoint regions.** `law_mul_prod_le_law_of_corridors` when the pairs read by
the corridor of arm `i`, its region `Q i` and the boxes of radius `M + 1` about the possible ends
`B i` all lie in a region `G i`, and the regions of different arms are disjoint: the conditions on
corridors of the other colour and on regions of the same colour then hold automatically. -/
theorem law_mul_prod_le_law_of_regions (q : Sym2 (LatticeSite 2) → unitInterval)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {R' : ℕ} (hKM : K ≤ M) (hM : 1 ≤ M)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hs : 4 * (M : ℝ) ≤ s)
    (B : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ)
    (C : Fin j → Set (Config (LatticeSite 2))) (T : Fin j → Set (Sym2 (LatticeSite 2)))
    (Q G : Fin j → Set (LatticeSite 2))
    (Φ : Fin j → Config (LatticeSite 2) → LatticeSite 2 → Prop)
    (hCm : ∀ i, MeasurableSet (C i))
    (hCT : ∀ i (ω ω' : Config (LatticeSite 2)), ω ∩ T i = ω' ∩ T i → (ω ∈ C i ↔ ω' ∈ C i))
    (hCmono : ∀ i (ω ω' : Config (LatticeSite 2)), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω →
      ω ∈ C i → ω' ∈ C i)
    (hT : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1))
    (hTG : ∀ i, ∀ e ∈ T i, ∀ v ∈ e, v ∈ G i)
    (hBG : ∀ i, ∀ b ∈ B i,
      Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G i)
    (hQG : ∀ i, Q i ⊆ G i) (hG : ∀ i k, i ≠ k → Disjoint (G i) (G k))
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
  refine law_mul_prod_le_law_of_corridors q hσ hKM hM hrM hRR' hs B J C T Q Φ hCm hCT hCmono
    ?_ hT ?_ hQloc ?_ hhook
  · intro i k hi hk
    have hik : i ≠ k := fun h => by
      rw [h, hk] at hi
      exact Bool.false_ne_true hi
    rw [disjoint_left]
    intro e he he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact disjoint_left.1 (hG i k hik) (hTG i e he v hv) (hTG k e he' v hv)
  · intro i k hik b hb e he hbox
    have hik' : i ≠ k := fun h => hik (h ▸ rfl)
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact disjoint_left.1 (hG i k hik') (hBG i b hb (hbox v hv)) (hTG k e he v hv)
  · intro ω a b γ _ _ _ _ hB i k hik _ v hvi hvk
    have hmem : ∀ l, (v ∈ Icc (b l - M) (b l + M) ∨ v ∈ Q l) → v ∈ G l := fun l h => by
      rcases h with h | h
      · exact hBG l (b l) (hB l) (Icc_sub_add_subset_Icc_sub_add_succ (b l) M h)
      · exact hQG l h
    exact disjoint_left.1 (hG i k hik) (hmem i hvi) (hmem k hvk)

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞} {κ : ℕ}

/-- **A stage of moves for fixed bins.** Given, for each arm `i`, a corridor of its colour in a
region `G i` (in the form produced by `exists_corridor_jogCap_top`, `exists_corridor_turn_top_left`
and their variants), with the regions pairwise disjoint: separated arms ending in the bins `B i`
are continued to arms to `∂B_{R'}(z)` ending in the targets `B' i` with outer fences `(M', K')`,
at the cost `c κ ^ (6j)`. -/
theorem pow_mul_law_le_law_of_regions (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i))
    {R' M' K' : ℕ} (hKM : K ≤ M) (hM : 1 ≤ M) (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R')
    (hs : 4 * (M : ℝ) ≤ s) (J : Fin j → Set ℤ) (B B' G : Fin j → Set (LatticeSite 2))
    (hG : ∀ i k, i ≠ k → Disjoint (G i) (G k))
    (hcor : ∀ i, ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond (σ i) ω ω' ⊆ cond (σ i) ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ G i) ∧
      (∀ b ∈ B i, Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ G i) ∧
      Q ⊆ G i ∧
      (∀ b ∈ B i, ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
        v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
        IsArm ω (σ i) z r (z - R) (z + R) γ → b ∈ B i → HasOuterFence ω (σ i) z R M K γ →
        ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
          x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond (σ i) ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond (σ i) (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond (σ i) (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            v ∈ B' i ∧
              HasOuterFence ω (σ i) z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C) :
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
  choose C T Q hCm hCT hCmono hT hTG hBG hQG hQloc hhook hprob using hcor
  have hmain := law_mul_prod_le_law_of_regions (σ := σ) (z := z) (r := r) (R := R) (s := s)
    (M := M) (K := K) (R' := R') q hσ hKM hM hrM hRR' hs B J C T Q G
    (fun i ω v => v ∈ B' i ∧ HasOuterFence ω (σ i) z R' M' K'
      (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v))
    hCm hCT hCmono hT hTG hBG hQG hG hQloc hhook
  have hprod : c κ ^ (6 * j) ≤ ∏ i, law q (C i) := by
    calc c κ ^ (6 * j) = ∏ _i : Fin j, c κ ^ 6 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
      _ ≤ ∏ i, law q (C i) := Finset.prod_le_prod fun i _ => hprob i
  calc c κ ^ (6 * j) * law q _ ≤ law q _ * ∏ i, law q (C i) := by
        rw [mul_comm]
        exact mul_le_mul' le_rfl hprod
    _ ≤ _ := hmain.trans (measure_mono fun ω hω => by
        obtain ⟨a, b', γ', h₁, h₂, h₃, h₄, h₅⟩ := hω
        exact ⟨a, b', γ', h₁, h₂, h₃, h₄, fun i => ⟨(h₅ i).1, (h₅ i).2.of_nil (γ' i)⟩⟩)

end Regions

/-! ### Regions of moves -/

section MoveRegions

/-- The case 0 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_0 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = false ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = α₁ - D - M - K' ∧ b₁ = z₁ + R - M ∧ c₁ = β₁ + W + D + M + K' + 1 ∧ d₁ = z₁ + R' + M' +
          1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).1 (Or.inl rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 1 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_1 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = false ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ + R - M ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ + R' + M' + 1 ∧ d₁ = β₁ + W + D + M + K' +
          1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).2 (Or.inl rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 2 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_2 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = false ∧ t₁ = 2 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = α₁ - D - M - K' ∧ b₁ = z₁ - R' - M' - 1 ∧ c₁ = β₁ + W + D + M + K' + 1 ∧ d₁ = z₁ - R +
          M + 1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).2 (Or.inr rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 3 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_3 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = false ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ - R' - M' - 1 ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ - R + M + 1 ∧ d₁ = β₁ + W + D + M +
          K' + 1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc2 := (_hccw₂ rfl rfl).1 (Or.inr rfl)
    omega

/-- The case 4 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_4 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = true ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = z₀ - R' - M' - 1 ∧ b₁ = z₁ + R - M - K' ∧ c₁ = β₁ + W + M + 1 ∧ d₁ = z₁ + h + W + K' +
          1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 (Or.inl rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 (Or.inl rfl)
    have hc2 := (_hccw₂ rfl rfl).1 (Or.inl rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 5 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_5 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = true ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ + R - M - K' ∧ b₁ = α₁ - M ∧ c₁ = z₀ + h + W + K' + 1 ∧ d₁ = z₁ + R' + M' + 1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).2 (Or.inl rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).2 (Or.inl rfl)
    have hc2 := (_hccw₂ rfl rfl).2 (Or.inl rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 6 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_6 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = true ∧ t₁ = 2 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
      a₁ = α₁ - M ∧ b₁ = z₁ - h - W - K' ∧ c₁ = z₀ + R' + M' + 1 ∧ d₁ = z₁ - R + M + K' + 1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).2 (Or.inr rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).2 (Or.inr rfl)
    have hc2 := (_hccw₂ rfl rfl).2 (Or.inr rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega

/-- The case 7 of the first move in `disjoint_regions_of_moves`. -/
theorem disjoint_regions_of_moves_7 {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂
    d₂ : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (_hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (_hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (_hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (_hR : M + K' + 1 < R) (_hh : R + M + 1 ≤ h)
    (_hhR : h + W + M' ≤ R')
    (_hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (_hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (_hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = true ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
      a₁ = z₀ - h - W - K' ∧ b₁ = z₁ - R' - M' - 1 ∧ c₁ = z₀ - R + M + K' + 1 ∧ d₁ = β₁ + W + M +
          1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  obtain ⟨rfl, rfl, hw₁, hw₁', rfl, rfl, rfl, rfl⟩ := h₁
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 (Or.inr rfl)
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    omega
  · obtain ⟨rfl, rfl, hw₂, hw₂', rfl, rfl, rfl, rfl⟩ := h₂
    have hg := _hgap rfl
    have hc1 := (_hccw₁ rfl rfl).1 (Or.inr rfl)
    have hc2 := (_hccw₂ rfl rfl).1 (Or.inr rfl)
    omega

/-- **Regions of moves are disjoint** (integer form). Two arms with windows `[α, β]` on the sides
`t` of `B_R` (`0` top, `1` right, `2` bottom, `3` left), at least `S` from the corners, moving by a
jog (`τ = false`) or by a counterclockwise turn (`τ = true`), have the regions `[a, c] × [b, d]`
described below (one formula for each side and kind of move); if windows on one side are `S`
apart and a turning arm is the last one on its side in counterclockwise order, with
`S ≥ W + 2D + 2M + 2K' + 3`, the two regions are disjoint. -/
theorem disjoint_regions_of_moves {z₀ z₁ R R' h M M' K' W D S α₁ β₁ α₂ β₂ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂
    : ℤ} {t₁ t₂ : Fin 4} {τ₁ τ₂ : Bool}
    (hpos : 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ K' ∧ 0 ≤ W ∧ 0 ≤ D) (hαβ : α₁ ≤ β₁ ∧ α₂ ≤ β₂)
    (hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) (hR : M + K' + 1 < R) (hh : R + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R')
    (hgap : t₁ = t₂ → β₁ + S ≤ α₂ ∨ β₂ + S ≤ α₁)
    (hccw₁ : τ₁ = true → t₂ = t₁ → (t₁ = 0 ∨ t₁ = 3 → β₁ + S ≤ α₂) ∧
      (t₁ = 1 ∨ t₁ = 2 → β₂ + S ≤ α₁))
    (hccw₂ : τ₂ = true → t₁ = t₂ → (t₂ = 0 ∨ t₂ = 3 → β₂ + S ≤ α₁) ∧
      (t₂ = 1 ∨ t₂ = 2 → β₁ + S ≤ α₂))
    (h₁ : (τ₁ = false ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = α₁ - D - M - K' ∧ b₁ = z₁ + R - M ∧ c₁ = β₁ + W + D + M + K' + 1 ∧ d₁ = z₁ + R' + M'
            + 1) ∨
      (τ₁ = false ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ + R - M ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ + R' + M' + 1 ∧ d₁ = β₁ + W + D + M + K'
            + 1) ∨
      (τ₁ = false ∧ t₁ = 2 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = α₁ - D - M - K' ∧ b₁ = z₁ - R' - M' - 1 ∧ c₁ = β₁ + W + D + M + K' + 1 ∧ d₁ = z₁ - R
            + M + 1) ∨
      (τ₁ = false ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ - R' - M' - 1 ∧ b₁ = α₁ - D - M - K' ∧ c₁ = z₀ - R + M + 1 ∧ d₁ = β₁ + W + D + M +
            K' + 1) ∨
      (τ₁ = true ∧ t₁ = 0 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = z₀ - R' - M' - 1 ∧ b₁ = z₁ + R - M - K' ∧ c₁ = β₁ + W + M + 1 ∧ d₁ = z₁ + h + W + K'
            + 1) ∨
      (τ₁ = true ∧ t₁ = 1 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ + R - M - K' ∧ b₁ = α₁ - M ∧ c₁ = z₀ + h + W + K' + 1 ∧ d₁ = z₁ + R' + M' + 1) ∨
      (τ₁ = true ∧ t₁ = 2 ∧ z₀ - R + S ≤ α₁ ∧ β₁ + S ≤ z₀ + R ∧
        a₁ = α₁ - M ∧ b₁ = z₁ - h - W - K' ∧ c₁ = z₀ + R' + M' + 1 ∧ d₁ = z₁ - R + M + K' + 1) ∨
      (τ₁ = true ∧ t₁ = 3 ∧ z₁ - R + S ≤ α₁ ∧ β₁ + S ≤ z₁ + R ∧
        a₁ = z₀ - h - W - K' ∧ b₁ = z₁ - R' - M' - 1 ∧ c₁ = z₀ - R + M + K' + 1 ∧ d₁ = β₁ + W + M
            + 1))
    (h₂ : (τ₂ = false ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ + R - M ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ + R' + M'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = β₂ + W + D + M + K'
            + 1) ∨
      (τ₂ = false ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - D - M - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = β₂ + W + D + M + K' + 1 ∧ d₂ = z₁ - R
            + M + 1) ∨
      (τ₂ = false ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = α₂ - D - M - K' ∧ c₂ = z₀ - R + M + 1 ∧ d₂ = β₂ + W + D + M +
            K' + 1) ∨
      (τ₂ = true ∧ t₂ = 0 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = z₀ - R' - M' - 1 ∧ b₂ = z₁ + R - M - K' ∧ c₂ = β₂ + W + M + 1 ∧ d₂ = z₁ + h + W + K'
            + 1) ∨
      (τ₂ = true ∧ t₂ = 1 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ + R - M - K' ∧ b₂ = α₂ - M ∧ c₂ = z₀ + h + W + K' + 1 ∧ d₂ = z₁ + R' + M' + 1) ∨
      (τ₂ = true ∧ t₂ = 2 ∧ z₀ - R + S ≤ α₂ ∧ β₂ + S ≤ z₀ + R ∧
        a₂ = α₂ - M ∧ b₂ = z₁ - h - W - K' ∧ c₂ = z₀ + R' + M' + 1 ∧ d₂ = z₁ - R + M + K' + 1) ∨
      (τ₂ = true ∧ t₂ = 3 ∧ z₁ - R + S ≤ α₂ ∧ β₂ + S ≤ z₁ + R ∧
        a₂ = z₀ - h - W - K' ∧ b₂ = z₁ - R' - M' - 1 ∧ c₂ = z₀ - R + M + K' + 1 ∧ d₂ = β₂ + W + M
            + 1)) :
    c₁ < a₂ ∨ c₂ < a₁ ∨ d₁ < b₂ ∨ d₂ < b₁ := by
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁
  · exact disjoint_regions_of_moves_0 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_1 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_2 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_3 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_4 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_5 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_6 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂
  · exact disjoint_regions_of_moves_7 hpos hαβ hS hR hh hhR hgap hccw₁ hccw₂ h₁ h₂

end MoveRegions

/-! ### One move, any side and kind -/

section Moves

variable {q : Sym2 (LatticeSite 2) → unitInterval} {L : ℕ∞} {c : ℕ → ℝ≥0∞}
  {col : Bool} {z : LatticeSite 2} {r R R' M K M' K' W D S κ : ℕ}

/-- A four-case side description, read on a known side. -/
theorem side_cases {t : Fin 4} {P₀ P₁ P₂ P₃ : Prop}
    (h : (t = 0 ∧ P₀) ∨ (t = 1 ∧ P₁) ∨ (t = 2 ∧ P₂) ∨ (t = 3 ∧ P₃)) :
    (t = 0 → P₀) ∧ (t = 1 → P₁) ∧ (t = 2 → P₂) ∧ (t = 3 → P₃) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by decide), fun h' => absurd h' (by decide),
      fun h' => absurd h' (by decide)⟩
  · exact ⟨fun h' => absurd h' (by decide), fun _ => h, fun h' => absurd h' (by decide),
      fun h' => absurd h' (by decide)⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (by decide), fun _ => h,
      fun h' => absurd h' (by decide)⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (by decide),
      fun h' => absurd h' (by decide), fun _ => h⟩

/-- **The corridor of one move.** An arm whose ends lie in a window `[α, β]` on the side `t` of
`B_R(z)` (at least `S` from the corners) and in the bin `[x, x + W]`, `α ≤ x ≤ β`, is either moved
along its side by `d` (`τ = false`: target window `[α + d, β + d + W]` on the same side of
`B_{R'}(z)`) or turned counterclockwise round the next corner at the level `h` (`τ = true`: target
window `[z₀ + h, z₀ + h + W]` on the top side for an arm on the right side, and so on): its corridor
of probability at least `c κ ^ 6` lies in the region `Icc gl gh` given by one formula for each side
and kind of move (the formulas of `disjoint_regions_of_moves`), and ends in the target window with
an outer fence `(M', K')`. -/
theorem exists_corridor_move (hCB : CrossingBounds q L c) (hM : 1 ≤ M) (hWK : W ≤ K)
    (hKM : K ≤ M) (hW : 1 ≤ W) (hM' : 2 ≤ M') (hWM' : W + K' ≤ M')
    (hS : W + 2 * D + 2 * M + 2 * K' + 3 ≤ S) {h : ℤ} (hh : (R : ℤ) + M + 1 ≤ h)
    (hhR : h + W + M' ≤ R') (hκ₁ : 2 * (R' : ℤ) + 2 ≤ κ * W)
    (hκ₂ : (W : ℤ) + 2 * K' ≤ κ * ((M' : ℤ) - 1)) (hL : (R' : ℕ∞) ≤ L)
    {t t' : Fin 4} {τ : Bool} {α β d α' β' x : ℤ} (hd : -(D : ℤ) ≤ d ∧ d ≤ D)
    (hwin : (if t = 0 ∨ t = 2 then z 0 else z 1) - R + S ≤ α ∧
      β + S ≤ (if t = 0 ∨ t = 2 then z 0 else z 1) + R)
    (hx : α ≤ x ∧ x ≤ β)
    (hout : (τ = false ∧ t' = t ∧ α' = α + d ∧ β' = β + d + W) ∨
      (τ = true ∧ ((t = 1 ∧ t' = 0 ∧ α' = z 0 + h ∧ β' = z 0 + h + W) ∨
        (t = 0 ∧ t' = 3 ∧ α' = z 1 + h ∧ β' = z 1 + h + W) ∨
        (t = 3 ∧ t' = 2 ∧ α' = z 0 - h - W ∧ β' = z 0 - h) ∨
        (t = 2 ∧ t' = 1 ∧ α' = z 1 - h - W ∧ β' = z 1 - h))))
    (B : Set (LatticeSite 2))
    (hB : ∀ b ∈ B, ((t = 0 ∧ b 1 = z 1 + R ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 1 ∧ b 0 = z 0 + R ∧ α ≤ b 1 ∧ b 1 ≤ β) ∨
        (t = 2 ∧ b 1 = z 1 - R - cond col 0 1 ∧ α ≤ b 0 ∧ b 0 ≤ β) ∨
        (t = 3 ∧ b 0 = z 0 - R - cond col 0 1 ∧ α ≤ b 1 ∧ b 1 ≤ β)) ∧
      ((t = 0 ∧ x ≤ b 0 ∧ b 0 ≤ x + W) ∨ (t = 1 ∧ x ≤ b 1 ∧ b 1 ≤ x + W) ∨
        (t = 2 ∧ x ≤ b 0 ∧ b 0 ≤ x + W) ∨ (t = 3 ∧ x ≤ b 1 ∧ b 1 ≤ x + W))) :
    ∃ gl gh : LatticeSite 2, ((τ = false ∧ t = 0 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = α - D - M - K' ∧ gl 1 = z 1 + R - M ∧ gh 0 = β + W + D + M + K' + 1 ∧
        gh 1 = z 1 + R' + M' + 1) ∨
      (τ = false ∧ t = 1 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 + R - M ∧ gl 1 = α - D - M - K' ∧ gh 0 = z 0 + R' + M' + 1 ∧
        gh 1 = β + W + D + M + K' + 1) ∨
      (τ = false ∧ t = 2 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = α - D - M - K' ∧ gl 1 = z 1 - R' - M' - 1 ∧ gh 0 = β + W + D + M + K' + 1 ∧
        gh 1 = z 1 - R + M + 1) ∨
      (τ = false ∧ t = 3 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = α - D - M - K' ∧ gh 0 = z 0 - R + M + 1 ∧
        gh 1 = β + W + D + M + K' + 1) ∨
      (τ = true ∧ t = 0 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = z 1 + R - M - K' ∧ gh 0 = β + W + M + 1 ∧
        gh 1 = z 1 + h + W + K' + 1) ∨
      (τ = true ∧ t = 1 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 + R - M - K' ∧ gl 1 = α - M ∧ gh 0 = z 0 + h + W + K' + 1 ∧
        gh 1 = z 1 + R' + M' + 1) ∨
      (τ = true ∧ t = 2 ∧ z 0 - R + S ≤ α ∧ β + S ≤ z 0 + R ∧
        gl 0 = α - M ∧ gl 1 = z 1 - h - W - K' ∧ gh 0 = z 0 + R' + M' + 1 ∧
        gh 1 = z 1 - R + M + K' + 1) ∨
      (τ = true ∧ t = 3 ∧ z 1 - R + S ≤ α ∧ β + S ≤ z 1 + R ∧
        gl 0 = z 0 - h - W - K' ∧ gl 1 = z 1 - R' - M' - 1 ∧ gh 0 = z 0 - R + M + K' + 1 ∧
        gh 1 = β + W + M + 1)) ∧
      ∃ (C : Set (Config (LatticeSite 2))) (T : Set (Sym2 (LatticeSite 2)))
      (Q : Set (LatticeSite 2)), MeasurableSet C ∧
      (∀ ω ω' : Config (LatticeSite 2), ω ∩ T = ω' ∩ T → (ω ∈ C ↔ ω' ∈ C)) ∧
      (∀ ω ω' : Config (LatticeSite 2), cond col ω ω' ⊆ cond col ω' ω → ω ∈ C → ω' ∈ C) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - (R : LatticeSite 2) + 1) (z + R - 1)) ∧
      (∀ e ∈ T, ∀ v ∈ e, v ∈ Icc gl gh) ∧
      (∀ b ∈ B, Icc (b - (M : LatticeSite 2)) (b + ((M + 1 : ℕ) : LatticeSite 2)) ⊆ Icc gl gh) ∧
      Q ⊆ Icc gl gh ∧
      (∀ b ∈ B, ∀ v ∈ Q, v ∈ Icc (z - (R : LatticeSite 2) - 1) (z + R) →
        v ∈ Icc (b - (M : LatticeSite 2)) (b + M)) ∧
      (∀ ω ∈ C, ∀ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b),
        IsArm ω col z r (z - R) (z + R) γ → b ∈ B → HasOuterFence ω col z R M K γ →
        ∃ (x y : LatticeSite 2) (P : (zdGraph 2).Walk x y), x ∈ γ.support ∧
          x ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∧
          (∀ e ∈ P.edges, e ∈ cond col ω (dualConfig ω)) ∧
          (∀ v ∈ P.support, v ∈ Icc (b - (M : LatticeSite 2)) (b + M) ∨ v ∈ Q) ∧
          y ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) ∧
          ∀ v ∈ P.support, v ∉ cond col (Icc (z - (R' : LatticeSite 2) + 1) (z + R' - 1))
          (Icc (z - (R' : LatticeSite 2)) (z + R' - 1)) →
            v ∈ {b : LatticeSite 2 | ((t' = 0 ∧ b 1 = z 1 + R' ∧ α' ≤ b 0 ∧ b 0 ≤ β') ∨
        (t' = 1 ∧ b 0 = z 0 + R' ∧ α' ≤ b 1 ∧ b 1 ≤ β') ∨
        (t' = 2 ∧ b 1 = z 1 - R' - cond col 0 1 ∧ α' ≤ b 0 ∧ b 0 ≤ β') ∨
        (t' = 3 ∧ b 0 = z 0 - R' - cond col 0 1 ∧ α' ≤ b 1 ∧ b 1 ≤ β'))} ∧
              HasOuterFence ω col z R' M' K' (SimpleGraph.Walk.nil : (zdGraph 2).Walk v v)) ∧
      c κ ^ 6 ≤ law q C := by
  have hcol : cond col (0 : ℤ) 1 = 0 ∨ cond col (0 : ℤ) 1 = 1 := by cases col <;> simp
  rcases hout with ⟨rfl, ht', rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩
  · subst t'
    rcases (by decide : ∀ u : Fin 4, u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3) t with rfl | rfl | rfl | rfl
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = α - D - M - K' ∧ gl 1 = z 1 + R - M :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = β + W + D + M + K' + 1 ∧ gh 1 = z 1 +
          R' + M' + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀, hgh₁⟩, ?_⟩
      exact exists_corridor_jogCap_top hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x - D)
          (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).1 rfl
          have h₂ := (side_cases (hB b hb).2).1 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inl ⟨rfl, hv₁, by omega, by omega⟩)
        gl gh (by omega) (by omega) (by omega) (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 + R - M ∧ gl 1 = α - D - M - K' :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 + R' + M' + 1 ∧ gh 1 = β + W + D
          + M + K' + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀, hgh₁⟩), ?_⟩
      exact exists_corridor_jogCap_right hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x -
          D) (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).2.1 rfl
          have h₂ := (side_cases (hB b hb).2).2.1 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inl ⟨rfl, hv₁, by omega, by omega⟩))
        gl gh (by omega) (by omega) (by omega) (by omega)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = α - D - M - K' ∧ gl 1 = z 1 - R' - M'
          - 1 :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = β + W + D + M + K' + 1 ∧ gh 1 = z 1 -
          R + M + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀, hgh₁⟩)),
          ?_⟩
      exact exists_corridor_jogCap_bottom hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x -
          D) (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).2.2.1 rfl
          have h₂ := (side_cases (hB b hb).2).2.2.1 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inr (Or.inl ⟨rfl, hv₁, by omega, by omega⟩)))
        gl gh (by omega) (by omega) (by omega) (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
      obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = α - D - M
          - K' :=
        ⟨![_, _], rfl, rfl⟩
      obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 - R + M + 1 ∧ gh 1 = β + W + D +
          M + K' + 1 :=
        ⟨![_, _], rfl, rfl⟩
      refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁, hgh₀,
          hgh₁⟩))), ?_⟩
      exact exists_corridor_jogCap_left hCB hM hWK hKM hW hM' hWM' (x := x) (d := d) (xl := x - D)
          (xr := x + D) (h := h) (by omega) (by omega)
        (by omega) (by omega) hh hhR (by omega) (by omega) hκ₁ hκ₂ hL
        B _ (fun b hb => by
          have h₁ := (side_cases (hB b hb).1).2.2.2 rfl
          have h₂ := (side_cases (hB b hb).2).2.2.2 rfl
          omega)
        (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inr (Or.inr (⟨rfl, hv₁, by omega, by omega⟩))))
        gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 + R - M - K' ∧ gl 1 = α - M :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 + h + W + K' + 1 ∧ gh 1 = z 1 + R'
        + M' + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2,
        hgl₀, hgl₁, hgh₀, hgh₁⟩))))), ?_⟩
    exact exists_corridor_turn_right_top hCB hM hWK hKM hW hM' hWM' (y := x) (h := h) (by omega)
        (by omega) hh hhR (by omega) hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).2.1 rfl
        have h₂ := (side_cases (hB b hb).2).2.1 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inl ⟨rfl, hv₁, hv₂, hv₃⟩)
      gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 - R' - M' - 1 ∧ gl 1 = z 1 + R - M
        - K' :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = β + W + M + 1 ∧ gh 1 = z 1 + h + W + K'
        + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1, hwin.2, hgl₀, hgl₁,
        hgh₀, hgh₁⟩)))), ?_⟩
    exact exists_corridor_turn_top_left hCB hM hWK hKM hW hM' hWM' (x := x) (h := h) (by omega)
        (by omega) hh hhR (by omega) hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).1 rfl
        have h₂ := (side_cases (hB b hb).2).1 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inr (Or.inr (⟨rfl, hv₁, hv₂, hv₃⟩))))
      gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = z 0 - h - W - K' ∧ gl 1 = z 1 - R' - M'
        - 1 :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 - R + M + K' + 1 ∧ gh 1 = β + W + M
        + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, hwin.1,
        hwin.2, hgl₀, hgl₁, hgh₀, hgh₁⟩))))))), ?_⟩
    exact exists_corridor_turn_left_bottom hCB hM hWK hKM hW hM' hWM' (y := x) (h := h) (by omega)
        (by omega) hh hhR hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).2.2.2 rfl
        have h₂ := (side_cases (hB b hb).2).2.2.2 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inr (Or.inl ⟨rfl, hv₁, hv₂, hv₃⟩)))
      gl gh (by omega) (by omega) (by omega) (by omega)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at hwin
    obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl : LatticeSite 2, gl 0 = α - M ∧ gl 1 = z 1 - h - W - K' :=
      ⟨![_, _], rfl, rfl⟩
    obtain ⟨gh, hgh₀, hgh₁⟩ : ∃ gh : LatticeSite 2, gh 0 = z 0 + R' + M' + 1 ∧ gh 1 = z 1 - R + M
        + K' + 1 :=
      ⟨![_, _], rfl, rfl⟩
    refine ⟨gl, gh, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hwin.1,
        hwin.2, hgl₀, hgl₁, hgh₀, hgh₁⟩)))))), ?_⟩
    exact exists_corridor_turn_bottom_right hCB hM hWK hKM hW hM' hWM' (x := x) (h := h) (by
        omega) (by omega) hh hhR hκ₁ hκ₂ hL
      B _ (fun b hb => by
        have h₁ := (side_cases (hB b hb).1).2.2.1 rfl
        have h₂ := (side_cases (hB b hb).2).2.2.1 rfl
        omega)
      (fun v hv₁ hv₂ hv₃ => Or.inr (Or.inl ⟨rfl, hv₁, hv₂, hv₃⟩))
      gl gh (by omega) (by omega) (by omega) (by omega)

end Moves

/-! ### The stage step: moves of arms between windows -/

section Stages

variable {j : ℕ}

/-- Two boxes of `ℤ²` separated along one coordinate are disjoint. -/
theorem disjoint_Icc_of_lt {gl₁ gh₁ gl₂ gh₂ : LatticeSite 2}
    (h : gh₁ 0 < gl₂ 0 ∨ gh₂ 0 < gl₁ 0 ∨ gh₁ 1 < gl₂ 1 ∨ gh₂ 1 < gl₁ 1) :
    Disjoint (Icc gl₁ gh₁) (Icc gl₂ gh₂) := by
  rw [Set.disjoint_left]
  intro v hv hv'
  rw [mem_Icc_two_iff] at hv hv'
  omega

/-- **A stage of moves between windows** (the step of the rotation into fixed windows, and with
`τ = false` the window-to-window step with fences of any size). For a colour sequence `σ` without
packs and ratios `A`, `N` there is `c₀ > 0` such that for every law with crossing bounds `c` up to
scale `L`: separated arms (separation `s ≥ 4M`, fences `(M, K)`, `W ≤ K ≤ M`) ending in windows
`[α i, β i]` on the sides `t i` of `B_R(z)` (`0` top, `1` right, `2` bottom, `3` left; at least `S`
from the corners, windows on one side `S` apart, each covered by `N` bins of width `W`) are moved
to `∂B_{R'}(z)`: arm `i` is moved along its side by `d i` (`τ i = false`, `|d i| ≤ D`, target window
`[α i + d i, β i + d i + W]` on the same side) or turned counterclockwise round the next corner at
the level `h` (`τ i = true`; only the last arm of its side in counterclockwise order; target window
`[z₀ + h, z₀ + h + W]` on the top side for an arm on the right side, `[z₁ + h, z₁ + h + W]` on the
left side for an arm on the top side, `[z₀ - h - W, z₀ - h]` on the bottom side for an arm on the
left side, `[z₁ - h - W, z₁ - h]` on the right side for an arm on the bottom side). The new arms
have fences `(M', K')` of any size with `W + K' ≤ M'`, and are separated at scale `2g' - 1` when
the target windows are at least `g'` from the corners of `B_{R'}(z)` and from each other on one
side: `c₀ P(windows at R) ≤ P(windows at R')`. The constant depends only on `σ`, `c`, `A`, `N`. -/
theorem exists_pos_le_law_windows_of_moves (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K M' K' D S : ℕ) (h : ℤ) (s : ℝ)
      (g' : ℤ) (J : Fin j → Set ℤ) (t t' : Fin j → Fin 4) (τ : Fin j → Bool)
      (α β d α' β' : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2 * D + 2 * M + 2 * K' + 3 ≤ S →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → (R : ℤ) + M + 1 ≤ h → h + W + M' ≤ R' →
      2 * R' + 2 ≤ A * W → W + 2 * K' ≤ A * (M' - 1) → (R' : ℕ∞) ≤ L →
      (∀ i, -(D : ℤ) ≤ d i ∧ d i ≤ D) → (∀ i, β i - α i + 1 ≤ N * ((W : ℤ) + 1)) →
      (∀ i, (if t i = 0 ∨ t i = 2 then z 0 else z 1) - R + S ≤ α i ∧
        β i + S ≤ (if t i = 0 ∨ t i = 2 then z 0 else z 1) + R) →
      (∀ i k, i ≠ k → t i = t k → β i + S ≤ α k ∨ β k + S ≤ α i) →
      (∀ i k, i ≠ k → τ i = true → t k = t i → (t i = 0 ∨ t i = 3 → β i + S ≤ α k) ∧
        (t i = 1 ∨ t i = 2 → β k + S ≤ α i)) →
      (∀ i, (τ i = false ∧ t' i = t i ∧ α' i = α i + d i ∧ β' i = β i + d i + W) ∨
        (τ i = true ∧ ((t i = 1 ∧ t' i = 0 ∧ α' i = z 0 + h ∧ β' i = z 0 + h + W) ∨
          (t i = 0 ∧ t' i = 3 ∧ α' i = z 1 + h ∧ β' i = z 1 + h + W) ∨
          (t i = 3 ∧ t' i = 2 ∧ α' i = z 0 - h - W ∧ β' i = z 0 - h) ∨
          (t i = 2 ∧ t' i = 1 ∧ α' i = z 1 - h - W ∧ β' i = z 1 - h)))) →
      1 ≤ g' →
      (∀ i, (if t' i = 0 ∨ t' i = 2 then z 0 else z 1) - R' + g' ≤ α' i ∧
        β' i + g' ≤ (if t' i = 0 ∨ t' i = 2 then z 0 else z 1) + R') →
      (∀ i k, i ≠ k → t' i = t' k → β' i + g' ≤ α' k ∨ β' k + g' ≤ α' i) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
            2 |
          (t' i = 0 ∧ b 1 = z 1 + R' ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 1 ∧ b 0 = z 0 + R' ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i) ∨
          (t' i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  classical
  by_cases hc : 0 < c A
  swap
  · exact ⟨1, one_pos, fun q L hCB => absurd (hCB.pos _) hc⟩
  have hX0 : ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    positivity
  have hXt : ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ⟨c A ^ (6 * j) / ((((N + 1) ^ j : ℕ)) : ℝ≥0∞),
    ENNReal.div_pos (pow_ne_zero _ hc.ne') hXt, ?_⟩
  intro q L hCB z r R R' W M K M' K' D S h s g' J t t' τ α β d α' β' hW hWK hKM hM' hWM' hS hs
    hrM hh hhR hAW hAM hR'L hd hN hwin hgap hccw hout hg' hcor' hgap'
  have hM : 1 ≤ M := by omega
  have hκ₁ : 2 * (R' : ℤ) + 2 ≤ A * W := by exact_mod_cast hAW
  have hκ₂ : (W : ℤ) + 2 * K' ≤ A * ((M' : ℤ) - 1) := by
    have h₁ : ((W + 2 * K' : ℕ) : ℤ) ≤ ((A * (M' - 1) : ℕ) : ℤ) := by exact_mod_cast hAM
    push_cast [Nat.cast_sub (by omega : 1 ≤ M')] at h₁
    linarith
  -- the separated event with ends in given bins
  set E : (Fin j → Fin (N + 1)) → Set (Config (LatticeSite 2)) := fun n => {ω : Config
      (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧ (∀ i, b i ∈ {b :
              LatticeSite 2 |
          (t i = 0 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
              : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 1 ∧ (α i + (((n i : Fin (N + 1)) :
              ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
              W) ∨
          (t i = 2 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
              : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 3 ∧ (α i + (((n i : Fin (N + 1)) :
              ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
              W)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} with hE
  -- every end in a window lies in a bin of the window
  have hbin : ∀ i (b : LatticeSite 2), b ∈ {b : LatticeSite 2 |
      (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)} → ∃ n : ℕ, n < N + 1 ∧
      b ∈ {b : LatticeSite 2 | (t i = 0 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (n : ℤ) *
          (W + 1)) + W) ∨ (t i = 1 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (n : ℤ) * (W +
          1)) + W) ∨
        (t i = 2 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (n : ℤ) * (W + 1)) + W) ∨ (t i =
            3 ∧ (α i + (n : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (n : ℤ) * (W + 1)) + W)} := by
    intro i b hb
    simp only [mem_ofPred_eq] at hb
    rcases hb with ⟨ht, -, h₂, h₃⟩ | ⟨ht, -, h₂, h₃⟩ | ⟨ht, -, h₂, h₃⟩ | ⟨ht, -, h₂, h₃⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inl ⟨ht, hn₁, hn₂⟩⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inl ⟨ht, hn₁, hn₂⟩)⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inr (Or.inl ⟨ht, hn₁, hn₂⟩))⟩
    · obtain ⟨n, hn, hn₁, hn₂⟩ := exists_lt_mem_bin h₂ h₃ (hN i)
      exact ⟨n, by omega, Or.inr (Or.inr (Or.inr ⟨ht, hn₁, hn₂⟩))⟩
  have hcover : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
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
  -- the stage for each choice of bins
  have hβ : ∀ n, c A ^ (6 * j) * law q (E n) ≤ law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j
      → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
            2 |
          (t' i = 0 ∧ b 1 = z 1 + R' ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 1 ∧ b 0 = z 0 + R' ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i) ∨
          (t' i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    intro n
    -- the empty case
    by_cases hne : ∃ (ω₀ : Config (LatticeSite 2)) (a₀ b₀ : Fin j → LatticeSite 2)
        (γ₀ : ∀ i, (zdGraph 2).Walk (a₀ i) (b₀ i)),
        (∀ i, b₀ i ∈ {b : LatticeSite 2 | (t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
          (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
          (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)}) ∧
        ∀ i, b₀ i ∈ {b : LatticeSite 2 | (t i = 0 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W +
            1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 1 ∧
            (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N
            + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨
          (t i = 2 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
              : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 3 ∧ (α i + (((n i : Fin (N + 1)) :
              ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
              W)}
    swap
    · refine le_trans (le_of_eq ?_) zero_le
      refine mul_eq_zero_of_right _ ?_
      convert measure_empty (μ := law q)
      ext ω
      simp only [hE, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨a, b, γ, -, -, -, -, h₅, h₆, -⟩
      exact hne ⟨ω, a, b, γ, h₅, h₆⟩
    obtain ⟨ω₀, a₀, b₀, γ₀, hW₀, hB₀⟩ := hne
    -- the bins start inside the windows
    have hx : ∀ i, α i ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ∧ (α i + (((n i : Fin
        (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ β i := by
      intro i
      have h₁ := hW₀ i
      have h₂ := hB₀ i
      have h₀ : (0 : ℤ) ≤ (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1) := by positivity
      simp only [mem_ofPred_eq] at h₁ h₂
      rcases h₁ with ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ | ⟨ht, -, h₁, h₁'⟩ <;>
        rcases h₂ with ⟨ht', h₂, h₂'⟩ | ⟨ht', h₂, h₂'⟩ | ⟨ht', h₂, h₂'⟩ | ⟨ht', h₂, h₂'⟩ <;>
        exact ⟨by omega, by omega⟩
    have hm := fun i => exists_corridor_move (col := σ i) (z := z) (r := r) (R := R) (R' := R')
      (M := M) (K := K) (M' := M') (K' := K') (W := W) (D := D) (S := S) (κ := A) hCB hM hWK hKM
      hW hM' hWM' hS hh hhR hκ₁ hκ₂ hR'L (hd i) (hwin i) (hx i) (hout i)
      {b : LatticeSite 2 | ((t i = 0 ∧ b 1 = z 1 + R ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 1 ∧ b 0 = z 0 + R ∧ α i ≤ b 1 ∧ b 1 ≤ β i) ∨
        (t i = 2 ∧ b 1 = z 1 - R - cond (σ i) 0 1 ∧ α i ≤ b 0 ∧ b 0 ≤ β i) ∨
        (t i = 3 ∧ b 0 = z 0 - R - cond (σ i) 0 1 ∧ α i ≤ b 1 ∧ b 1 ≤ β i)) ∧
        ((t i = 0 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i
            : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 1 ∧ (α i + (((n i : Fin (N + 1)) :
            ℕ) : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) +
            W) ∨
        (t i = 2 ∧ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) ≤ b 0 ∧ b 0 ≤ (α i + (((n i :
            Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W) ∨ (t i = 3 ∧ (α i + (((n i : Fin (N + 1)) : ℕ)
            : ℤ) * (W + 1)) ≤ b 1 ∧ b 1 ≤ (α i + (((n i : Fin (N + 1)) : ℕ) : ℤ) * (W + 1)) + W))}
            (fun b hb => hb)
    choose gl gh hspec hcor using hm
    have hG : ∀ i k, i ≠ k → Disjoint (Icc (gl i) (gh i)) (Icc (gl k) (gh k)) := by
      intro i k hik
      refine disjoint_Icc_of_lt ?_
      have hR : (M : ℤ) + K' + 1 < R := by
        have := hwin i
        have := hx i
        omega
      exact disjoint_regions_of_moves (z₀ := z 0) (z₁ := z 1) (R := R) (R' := R') (h := h)
        (M := M) (M' := M') (K' := K') (W := W) (D := D) (S := S)
        ⟨by positivity, by positivity, by positivity, by positivity, by positivity⟩
        ⟨(hx i).1.trans (hx i).2, (hx k).1.trans (hx k).2⟩ (by exact_mod_cast hS) hR hh hhR
        (hgap i k hik) (hccw i k hik) (hccw k i (Ne.symm hik)) (hspec i) (hspec k)
    refine le_trans (mul_le_mul' le_rfl (measure_mono fun ω hω => ?_))
      ((pow_mul_law_le_law_of_regions (q := q) (c := c) (κ := A) (σ := σ) (z := z) (r := r)
        (R := R) (s := s) (M := M) (K := K) (R' := R') (M' := M') (K' := K') hσ hKM hM hrM
        (by omega) hs J _ _ (fun i => Icc (gl i) (gh i)) hG hcor).trans (measure_mono ?_))
    · obtain ⟨a, b, γ, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hω
      exact ⟨a, b, γ, h₁, h₂, h₃, h₄, fun i => ⟨h₅ i, h₆ i⟩, h₇⟩
    · rintro ω ⟨a, b', γ', hγ', hd', ho', hJ', hB'⟩
      obtain ⟨hs₁, hs₂⟩ := le_abs_landingPos_sub_of_windows hγ' (by omega) hg' t' α' β'
        (fun i => (hB' i).1) hcor' hgap'
      refine ⟨a, b', γ', hγ', hd', ho', ⟨fun i k hik => ?_, fun i m => ?_, fun i => (hB' i).2⟩,
        fun i => (hB' i).1, hJ'⟩
      · rw [← Int.cast_abs]
        exact_mod_cast hs₁ i k hik
      · rw [← Int.cast_abs]
        exact_mod_cast hs₂ i m
  refine (mul_le_mul' le_rfl hcover).trans ?_
  rw [Finset.mul_sum]
  calc ∑ n, c A ^ (6 * j) / ((((N + 1) ^ j : ℕ)) : ℝ≥0∞) * law q (E n)
      ≤ ∑ _n : Fin j → Fin (N + 1), law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j →
          LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R') (z + R') (σ i) (γ i))
          (landingPos (z - R') (z + R') (σ k) (γ k)) (landingPos (z - R') (z + R') (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R' ((2 * g' - 1 : ℤ) : ℝ) M' K' γ ∧ (∀ i, b i ∈ {b : LatticeSite
            2 |
          (t' i = 0 ∧ b 1 = z 1 + R' ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 1 ∧ b 0 = z 0 + R' ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i) ∨
          (t' i = 2 ∧ b 1 = z 1 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 0 ∧ b 0 ≤ β' i) ∨
          (t' i = 3 ∧ b 0 = z 0 - R' - cond (σ i) 0 1 ∧ α' i ≤ b 1 ∧ b 1 ≤ β' i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} * ((((N + 1) ^ j : ℕ) : ℝ≥0∞))⁻¹ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul_left (hβ n) _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hX0 hXt, mul_one]

end Stages

/-! ### Chains of stages -/

section Chains

variable {j : ℕ}

/-- **Geometric growth along a chain** in `ℝ≥0∞`: if `c u k ≤ u (k + 1)` for `k < n`, then
`c ^ n u 0 ≤ u n` (`geom_le` for `ℝ≥0∞`). -/
theorem pow_mul_le_of_forall_mul_le {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (n : ℕ)
    (h : ∀ k < n, c * u k ≤ u (k + 1)) : c ^ n * u 0 ≤ u n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc c ^ (n + 1) * u 0 = c * (c ^ n * u 0) := by rw [pow_succ', mul_assoc]
      _ ≤ c * u n := mul_le_mul' le_rfl (ih fun k hk => h k (by omega))
      _ ≤ u (n + 1) := h n (by omega)

/-- **A chain of stages of moves** (the rotation into fixed windows, given its plan). For a colour
sequence `σ` without packs, ratios `A`, `N` and a number of stages `n` there is `c₀ > 0` such that
for every law with crossing bounds `c` up to scale `L`: separated arms with fences `(M, K)` ending
in windows `(t 0, [α 0, β 0])` on the sides of `B_{ρ 0}(z)` are carried, through `n` stages of moves
(`exists_pos_le_law_windows_of_moves`, stage `k` from `ρ k` to `ρ (k + 1)` at the level `hl k`, with
the moves `τ k`, `d k`), to separated arms with the **same** fences `(M, K)` ending in the windows
`(t n, [α n, β n])` of `B_{ρ n}(z)`, separated at scale `2S - 1`:
`c₀ P(windows at ρ 0) ≤ P(windows at ρ n)`. The windows of every stage are at least `S` from the
corners and from each other on one side, a turning arm is the last of its side in counterclockwise
order, and each stage's target windows are the next stage's windows. The constant depends only on
`σ`, `c`, `A`, `N`, `n`. -/
theorem exists_pos_le_law_windows_of_stages (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r W M K D S : ℕ) (ρ : ℕ → ℕ) (hl : ℕ → ℤ)
      (s : ℝ) (J : Fin j → Set ℤ) (t : ℕ → Fin j → Fin 4) (τ : ℕ → Fin j → Bool)
      (α β d : ℕ → Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → W + 2 * D + 2 * M + 2 * K + 3 ≤ S →
      W + 2 * K ≤ A * (M - 1) → 4 * (M : ℝ) ≤ s → r + M + 1 < ρ 0 →
      (∀ k < n, (ρ k : ℤ) + M + 1 ≤ hl k ∧ hl k + W + M ≤ ρ (k + 1) ∧
        2 * ρ (k + 1) + 2 ≤ A * W ∧ (ρ (k + 1) : ℕ∞) ≤ L) →
      (∀ k < n, ∀ i, -(D : ℤ) ≤ d k i ∧ d k i ≤ D) →
      (∀ k < n, ∀ i, β k i - α k i + 1 ≤ N * ((W : ℤ) + 1)) →
      (∀ k ≤ n, ∀ i, (if t k i = 0 ∨ t k i = 2 then z 0 else z 1) - ρ k + S ≤ α k i ∧
        β k i + S ≤ (if t k i = 0 ∨ t k i = 2 then z 0 else z 1) + ρ k) →
      (∀ k ≤ n, ∀ i l, i ≠ l → t k i = t k l → β k i + S ≤ α k l ∨ β k l + S ≤ α k i) →
      (∀ k < n, ∀ i l, i ≠ l → τ k i = true → t k l = t k i →
        (t k i = 0 ∨ t k i = 3 → β k i + S ≤ α k l) ∧ (t k i = 1 ∨ t k i = 2 → β k l + S ≤ α k i)) →
      (∀ k < n, ∀ i, (τ k i = false ∧ t (k + 1) i = t k i ∧ α (k + 1) i = α k i + d k i ∧
          β (k + 1) i = β k i + d k i + W) ∨
        (τ k i = true ∧ ((t k i = 1 ∧ t (k + 1) i = 0 ∧ α (k + 1) i = z 0 + hl k ∧
            β (k + 1) i = z 0 + hl k + W) ∨
          (t k i = 0 ∧ t (k + 1) i = 3 ∧ α (k + 1) i = z 1 + hl k ∧
            β (k + 1) i = z 1 + hl k + W) ∨
          (t k i = 3 ∧ t (k + 1) i = 2 ∧ α (k + 1) i = z 0 - hl k - W ∧ β (k + 1) i = z 0 - hl k) ∨
          (t k i = 2 ∧ t (k + 1) i = 1 ∧ α (k + 1) i = z 1 - hl k - W ∧
            β (k + 1) i = z 1 - hl k)))) →
      c₀ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ 0)) (z + (ρ 0)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ i) (γ i))
          (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ k) (γ k)) (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ 0) s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t 0 i = 0 ∧ b 1 = z 1 + (ρ 0) ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 1 ∧ b 0 = z 0 + (ρ 0) ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i) ∨
          (t 0 i = 2 ∧ b 1 = z 1 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 3 ∧ b 0 = z 0 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ n)) (z + (ρ n)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ n)) (z + (ρ n)) (σ i) (γ i))
          (landingPos (z - (ρ n)) (z + (ρ n)) (σ k) (γ k)) (landingPos (z - (ρ n)) (z + (ρ n)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ n) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (t n i = 0 ∧ b 1 = z 1 + (ρ n) ∧ α n i ≤ b 0 ∧ b 0 ≤ β n i) ∨
          (t n i = 1 ∧ b 0 = z 0 + (ρ n) ∧ α n i ≤ b 1 ∧ b 1 ≤ β n i) ∨
          (t n i = 2 ∧ b 1 = z 1 - (ρ n) - cond (σ i) 0 1 ∧ α n i ≤ b 0 ∧ b 0 ≤ β n i) ∨
          (t n i = 3 ∧ b 0 = z 0 - (ρ n) - cond (σ i) 0 1 ∧ α n i ≤ b 1 ∧ b 1 ≤ β n i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
  obtain ⟨c₁, hc₁, hstage⟩ := exists_pos_le_law_windows_of_moves σ hσ c A N
  refine ⟨c₁ ^ n, ENNReal.pow_pos hc₁ n, ?_⟩
  intro q L hCB z r W M K D S ρ hl s J t τ α β d hW hWK hWKM hS hAM hs hρ0 hρ hd hN hwin hgap
    hccw hout
  have hS1 : (1 : ℤ) ≤ S := by omega
  have hsS : 4 * (M : ℝ) ≤ ((2 * (S : ℤ) - 1 : ℤ) : ℝ) := by
    have : (4 * M : ℤ) ≤ 2 * (S : ℤ) - 1 := by omega
    exact_mod_cast this
  have hmono : ∀ k ≤ n, ρ 0 ≤ ρ k := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      obtain ⟨h₁, h₂, -, -⟩ := hρ k hk
      have := ih (by omega)
      omega
  -- the windows give the separation at scale `2S - 1` at the start
  have h₀ : law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ 0)) (z + (ρ 0)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ i) (γ i))
          (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ k) (γ k)) (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ 0) s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
          (t 0 i = 0 ∧ b 1 = z 1 + (ρ 0) ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 1 ∧ b 0 = z 0 + (ρ 0) ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i) ∨
          (t 0 i = 2 ∧ b 1 = z 1 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 3 ∧ b 0 = z 0 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤ law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j
            → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ 0)) (z + (ρ 0)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ i) (γ i))
          (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ k) (γ k)) (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ 0) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (t 0 i = 0 ∧ b 1 = z 1 + (ρ 0) ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 1 ∧ b 0 = z 0 + (ρ 0) ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i) ∨
          (t 0 i = 2 ∧ b 1 = z 1 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 3 ∧ b 0 = z 0 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    refine measure_mono ?_
    rintro ω ⟨a, b, γ, hγ, hd', ho, hsep, hw, hJ⟩
    obtain ⟨hs₁, hs₂⟩ := le_abs_landingPos_sub_of_windows hγ (by omega) hS1 (t 0) (α 0) (β 0) hw
      (hwin 0 (Nat.zero_le _)) (hgap 0 (Nat.zero_le _))
    refine ⟨a, b, γ, hγ, hd', ho, ⟨fun i k hik => ?_, fun i m => ?_, hsep.2.2⟩, hw, hJ⟩
    · rw [← Int.cast_abs]
      exact_mod_cast hs₁ i k hik
    · rw [← Int.cast_abs]
      exact_mod_cast hs₂ i m
  -- one stage
  have hstep : ∀ m < n, c₁ * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ m)) (z + (ρ m)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ m)) (z + (ρ m)) (σ i) (γ i))
          (landingPos (z - (ρ m)) (z + (ρ m)) (σ k) (γ k)) (landingPos (z - (ρ m)) (z + (ρ m)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ m) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (t m i = 0 ∧ b 1 = z 1 + (ρ m) ∧ α m i ≤ b 0 ∧ b 0 ≤ β m i) ∨
          (t m i = 1 ∧ b 0 = z 0 + (ρ m) ∧ α m i ≤ b 1 ∧ b 1 ≤ β m i) ∨
          (t m i = 2 ∧ b 1 = z 1 - (ρ m) - cond (σ i) 0 1 ∧ α m i ≤ b 0 ∧ b 0 ≤ β m i) ∨
          (t m i = 3 ∧ b 0 = z 0 - (ρ m) - cond (σ i) 0 1 ∧ α m i ≤ b 1 ∧ b 1 ≤ β m i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤ law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j
            → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ (m + 1))) (z + (ρ (m + 1))) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ (m + 1))) (z + (ρ (m + 1))) (σ i) (γ i))
          (landingPos (z - (ρ (m + 1))) (z + (ρ (m + 1))) (σ k) (γ k)) (landingPos (z - (ρ (m +
              1))) (z + (ρ (m + 1))) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ (m + 1)) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (t (m + 1) i = 0 ∧ b 1 = z 1 + (ρ (m + 1)) ∧ α (m + 1) i ≤ b 0 ∧ b 0 ≤ β (m + 1) i) ∨
          (t (m + 1) i = 1 ∧ b 0 = z 0 + (ρ (m + 1)) ∧ α (m + 1) i ≤ b 1 ∧ b 1 ≤ β (m + 1) i) ∨
          (t (m + 1) i = 2 ∧ b 1 = z 1 - (ρ (m + 1)) - cond (σ i) 0 1 ∧ α (m + 1) i ≤ b 0 ∧ b 0 ≤
              β (m + 1) i) ∨
          (t (m + 1) i = 3 ∧ b 0 = z 0 - (ρ (m + 1)) - cond (σ i) 0 1 ∧ α (m + 1) i ≤ b 1 ∧ b 1 ≤
              β (m + 1) i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := by
    intro k hk
    obtain ⟨hρ₁, hρ₂, hρ₃, hρ₄⟩ := hρ k hk
    have hr : r + M + 1 < ρ k := hρ0.trans_le (hmono k hk.le)
    exact hstage q L hCB z r (ρ k) (ρ (k + 1)) W M K M K D S (hl k) _ S J (t k) (t (k + 1))
      (τ k) (α k) (β k) (d k) (α (k + 1)) (β (k + 1)) hW hWK (by omega) (by omega) hWKM hS hsS hr
      hρ₁ hρ₂ hρ₃ hAM hρ₄ (hd k hk) (hN k hk) (hwin k hk.le) (hgap k hk.le) (hccw k hk) (hout k hk)
      hS1 (hwin (k + 1) hk) (hgap (k + 1) hk)
  calc c₁ ^ n * law q _ ≤ c₁ ^ n * law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j →
      LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ 0)) (z + (ρ 0)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ i) (γ i))
          (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ k) (γ k)) (landingPos (z - (ρ 0)) (z + (ρ 0)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ 0) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (t 0 i = 0 ∧ b 1 = z 1 + (ρ 0) ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 1 ∧ b 0 = z 0 + (ρ 0) ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i) ∨
          (t 0 i = 2 ∧ b 1 = z 1 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 0 ∧ b 0 ≤ β 0 i) ∨
          (t 0 i = 3 ∧ b 0 = z 0 - (ρ 0) - cond (σ i) 0 1 ∧ α 0 i ≤ b 1 ∧ b 1 ≤ β 0 i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} := mul_le_mul' le_rfl h₀
    _ ≤ _ := pow_mul_le_of_forall_mul_le (u := fun m => law q {ω : Config (LatticeSite 2) | ∃ (a b
        : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (ρ m)) (z + (ρ m)) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - (ρ m)) (z + (ρ m)) (σ i) (γ i))
          (landingPos (z - (ρ m)) (z + (ρ m)) (σ k) (γ k)) (landingPos (z - (ρ m)) (z + (ρ m)) (σ
              l) (γ l))) ∧
        ArmsOuterSeparated ω σ z (ρ m) ((2 * (S : ℤ) - 1 : ℤ) : ℝ) M K γ ∧ (∀ i, b i ∈ {b :
            LatticeSite 2 |
          (t m i = 0 ∧ b 1 = z 1 + (ρ m) ∧ α m i ≤ b 0 ∧ b 0 ≤ β m i) ∨
          (t m i = 1 ∧ b 0 = z 0 + (ρ m) ∧ α m i ≤ b 1 ∧ b 1 ≤ β m i) ∨
          (t m i = 2 ∧ b 1 = z 1 - (ρ m) - cond (σ i) 0 1 ∧ α m i ≤ b 0 ∧ b 0 ≤ β m i) ∨
          (t m i = 3 ∧ b 0 = z 0 - (ρ m) - cond (σ i) 0 1 ∧ α m i ≤ b 1 ∧ b 1 ≤ β m i)}) ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i}) n hstep

/-- **Covering the separated event by windows of bins.** Separated arms at the outer boundary of
`B_R(z)` (separation `s ≥ 4M`) end in bins of width `W` on the sides: the separated event is
covered by the `(4 (2A + 1)) ^ j` events in which arm `i` ends in the window of the bin `p i`
(a side and an index), `R ≤ A W`; the first stage of a chain (`exists_pos_le_law_windows_of_stages`)
starts from one of these. -/
theorem law_le_sum_law_windows_of_separated (q : Sym2 (LatticeSite 2) → unitInterval)
    {σ : Fin j → Bool} {z : LatticeSite 2} {r R W M K A : ℕ} {s : ℝ} (hrR : r < R) (hM : 1 ≤ M)
    (hW : 1 ≤ W) (hRA : R ≤ A * W) (hs : 4 * (M : ℝ) ≤ s) (J : Fin j → Set ℤ) :
    law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      ∑ p : Fin j → Fin 4 × Fin (2 * A + 1), law q {ω : Config (LatticeSite 2) | ∃ (a b : Fin j →
          LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (∀ i k l, i < k → k < l → sbtw (landingPos (z - R) (z + R) (σ i) (γ i))
          (landingPos (z - R) (z + R) (σ k) (γ k)) (landingPos (z - R) (z + R) (σ l) (γ l))) ∧
        ArmsOuterSeparated ω σ z R s M K γ ∧ (∀ i, b i ∈ {b : LatticeSite 2 |
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
  rintro ω ⟨a, b, γ, hγ, hd, ho, hsep, hJ⟩
  have hcor := (hsep.le_abs_landingPos_sub (S := 4 * M) (by push_cast; linarith)).2
  have hbin := fun i => (hγ i).exists_mem_bin hrR hM hW hRA (fun m => hcor i m)
  choose t n hn hb using hbin
  rw [mem_iUnion]
  refine ⟨fun i => (t i, ⟨n i, hn i⟩), a, b, γ, hγ, hd, ho, hsep, fun i => ?_, hJ⟩
  rcases hb i with ⟨h₀, h₁, h₂, h₃, -⟩ | ⟨h₀, h₁, h₂, h₃, -⟩ | ⟨h₀, h₁, h₂, h₃, -⟩ |
      ⟨h₀, h₁, h₂, h₃, -⟩
  · exact Or.inl ⟨h₀, h₁, h₂, h₃⟩
  · exact Or.inr (Or.inl ⟨h₀, h₁, h₂, h₃⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h₀, h₁, h₂, h₃⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₀, h₁, h₂, h₃⟩))

end Chains

end PercLib.Models.Planar
