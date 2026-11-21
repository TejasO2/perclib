/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New definitions. Reference: T. Hutchcroft, *Critical cluster volumes in hierarchical
percolation*, arXiv:2211.05686 (the exact radial kernel and its block layers).
-/
module

public import PercLib.Models.HierarchicalGeometry
public import PercLib.Percolation.Bond.Basic

/-! # Block layers of the hierarchical lattice (definitions)

The lattice is `V = ℕ →₀ A` for an abelian group `A` (for the hierarchical lattice,
`A = Fin d → ZMod L`); the level of `z` is `h z = z.support.sup Nat.succ`. Two distinct
vertices first share a block at level `h(y - x)`.

* `pairLevel e`: the level `h(x, y) = h(y - x)` of the pair `e = s(x, y)`.
* `block n x`: the block of level `n` containing `x`, `{y | h(y - x) ≤ n}`.
* `IsCopy i`: the index `i = (m, e)` is a copy of a genuine pair `e` in its common block of
  level `m`, that is `e` is not a loop and `h(e) ≤ m`. Copies of `e` correspond to the blocks
  containing both endpoints, one per level `m ≥ h(e)`.
* `layerWeight L s i`: the weight `L^{-sm}` of a copy `i = (m, e)` (`0` for other indices), and
  `layerProfile L s β i = 1 - exp(-β L^{-sm})` the open probability of its layer edge.
* `openCopies L s β T`: the copies whose clock `T i` rings by the layer time `β L^{-sm}`.
* `fullConfig ξ`, `blockConfig n x ξ`, `ancestorConfig n x ξ`: the pairs with some open copy;
  with an open copy at a level `≤ n` inside `block n x` (the union `η_B` of the layers of the
  blocks inside `B = block n x`); with an open copy at a level `> n` inside `block n x`.
* `exactKernel L s`, `truncatedKernel L s n x`, `ancestorKernel L s n x`: the kernels
  `J_∞(x,y) = L^s/(L^s - 1) ‖x - y‖^{-s}` with `‖x - y‖ = L^{h(x,y)}`,
  `J_n(x,y) = ∑_{m=h(x,y)}^n L^{-sm}` on pairs of `block n x`, and the constant
  `L^{-sn}/(L^s - 1)` on pairs of `block n x`.
-/

@[expose] public section
noncomputable section

open scoped NNReal

namespace PercLib.Models.HierarchicalLayers

open PercLib.Percolation.Bond

variable {A : Type*} [AddCommGroup A]

/-- The level `h(x, y) = h(y - x)` of a pair. -/
def pairLevel : Sym2 (ℕ →₀ A) → ℕ :=
  Sym2.lift ⟨fun x y => (y - x).support.sup Nat.succ, fun x y => level_sub_comm x y⟩

@[simp] theorem pairLevel_mk (x y : ℕ →₀ A) :
    pairLevel s(x, y) = (y - x).support.sup Nat.succ := rfl

/-- The block of level `n` containing `x`. -/
def block (n : ℕ) (x : ℕ →₀ A) : Set (ℕ →₀ A) := {y | (y - x).support.sup Nat.succ ≤ n}

@[simp] theorem mem_block {n : ℕ} {x y : ℕ →₀ A} :
    y ∈ block n x ↔ (y - x).support.sup Nat.succ ≤ n := Iff.rfl

theorem mem_block_self (n : ℕ) (x : ℕ →₀ A) : x ∈ block n x := by simp

theorem block_mono {n m : ℕ} (h : n ≤ m) (x : ℕ →₀ A) : block n x ⊆ block m x :=
  fun _ hy => le_trans hy h

/-- `(m, e)` is a copy of the genuine pair `e` in its common block of level `m`. -/
def IsCopy (i : ℕ × Sym2 (ℕ →₀ A)) : Prop := ¬ i.2.IsDiag ∧ pairLevel i.2 ≤ i.1

theorem isCopy_iff (i : ℕ × Sym2 (ℕ →₀ A)) : IsCopy i ↔ ¬ i.2.IsDiag ∧ pairLevel i.2 ≤ i.1 :=
  Iff.rfl

open Classical in
/-- The weight `L^{-sm}` of a copy `(m, e)`, and `0` for other indices. -/
def layerWeight (L s : ℝ) (i : ℕ × Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if IsCopy i then (L ^ (-(s * i.1))).toNNReal else 0

theorem layerWeight_of_isCopy {L s : ℝ} {i : ℕ × Sym2 (ℕ →₀ A)} (hi : IsCopy i) :
    layerWeight L s i = (L ^ (-(s * i.1))).toNNReal := by
  classical
  simp [layerWeight, hi]

theorem layerWeight_of_not_isCopy {L s : ℝ} {i : ℕ × Sym2 (ℕ →₀ A)} (hi : ¬ IsCopy i) :
    layerWeight L s i = 0 := by
  classical
  simp [layerWeight, hi]

/-- The open probability `1 - exp(-β L^{-sm})` of the layer edge of a copy `(m, e)`. -/
def layerProfile (L s : ℝ) (β : ℝ≥0) (i : ℕ × Sym2 (ℕ →₀ A)) : unitInterval :=
  ⟨1 - Real.exp (-(β : ℝ) * layerWeight L s i), by
    constructor
    · apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr β.coe_nonneg) (layerWeight L s i).2
    · exact sub_le_self _ (Real.exp_pos _).le⟩

@[simp] theorem coe_layerProfile (L s : ℝ) (β : ℝ≥0) (i : ℕ × Sym2 (ℕ →₀ A)) :
    (layerProfile L s β i : ℝ) = 1 - Real.exp (-(β : ℝ) * layerWeight L s i) := rfl

/-- The copies whose rate-one clocks ring by the layer times `β L^{-sm}`. -/
def openCopies (L s β : ℝ) (T : ℕ × Sym2 (ℕ →₀ A) → ℝ) : Set (ℕ × Sym2 (ℕ →₀ A)) :=
  {i | i ∈ {i | IsCopy i} ∧ T i ≤ β * L ^ (-(s * i.1))}

@[simp] theorem mem_openCopies {L s β : ℝ} {T : ℕ × Sym2 (ℕ →₀ A) → ℝ}
    {i : ℕ × Sym2 (ℕ →₀ A)} :
    i ∈ openCopies L s β T ↔ IsCopy i ∧ T i ≤ β * L ^ (-(s * i.1)) := Iff.rfl

/-- The union of all layers: the pairs with some open copy. -/
def fullConfig (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) : Config (ℕ →₀ A) := {e | ∃ m, (m, e) ∈ ξ}

@[simp] theorem mem_fullConfig {ξ : Set (ℕ × Sym2 (ℕ →₀ A))} {e : Sym2 (ℕ →₀ A)} :
    e ∈ fullConfig ξ ↔ ∃ m, (m, e) ∈ ξ := Iff.rfl

/-- The union `η_B` of the layers of the blocks inside `B = block n x`: the pairs of `B` with an
open copy at a level `≤ n`. -/
def blockConfig (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) : Config (ℕ →₀ A) :=
  {e | ∃ m ≤ n, (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x}

@[simp] theorem mem_blockConfig {n : ℕ} {x : ℕ →₀ A} {ξ : Set (ℕ × Sym2 (ℕ →₀ A))}
    {e : Sym2 (ℕ →₀ A)} :
    e ∈ blockConfig n x ξ ↔ ∃ m ≤ n, (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x := Iff.rfl

/-- The layers of the strict ancestors of `B = block n x`, seen on the pairs of `B`. -/
def ancestorConfig (n : ℕ) (x : ℕ →₀ A) (ξ : Set (ℕ × Sym2 (ℕ →₀ A))) : Config (ℕ →₀ A) :=
  {e | ∃ m, n < m ∧ (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x}

@[simp] theorem mem_ancestorConfig {n : ℕ} {x : ℕ →₀ A} {ξ : Set (ℕ × Sym2 (ℕ →₀ A))}
    {e : Sym2 (ℕ →₀ A)} :
    e ∈ ancestorConfig n x ξ ↔ ∃ m, n < m ∧ (m, e) ∈ ξ ∧ ∀ v ∈ e, v ∈ block n x := Iff.rfl

open Classical in
/-- The exact radial kernel `J_∞(x,y) = L^s/(L^s - 1) (L^{h(x,y)})^{-s}`, `0` on loops. -/
def exactKernel (L s : ℝ) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if e.IsDiag then 0 else (L ^ s / (L ^ s - 1) * ((L ^ pairLevel e) ^ (-s))).toNNReal

theorem exactKernel_of_not_isDiag {L s : ℝ} {e : Sym2 (ℕ →₀ A)} (he : ¬ e.IsDiag) :
    exactKernel L s e = (L ^ s / (L ^ s - 1) * ((L ^ pairLevel e) ^ (-s))).toNNReal := by
  classical
  simp [exactKernel, he]

@[simp] theorem exactKernel_of_isDiag {L s : ℝ} {e : Sym2 (ℕ →₀ A)} (he : e.IsDiag) :
    exactKernel L s e = 0 := by
  classical
  simp [exactKernel, he]

open Classical in
/-- The truncated kernel `J_n(x,y) = ∑_{m=h(x,y)}^n L^{-sm}` on the pairs of `block n x`,
`0` elsewhere. -/
def truncatedKernel (L s : ℝ) (n : ℕ) (x : ℕ →₀ A) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x then
    (∑ m ∈ Finset.Icc (pairLevel e) n, L ^ (-(s * m))).toNNReal
  else 0

theorem truncatedKernel_of_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x) :
    truncatedKernel L s n x e = (∑ m ∈ Finset.Icc (pairLevel e) n, L ^ (-(s * m))).toNNReal := by
  classical
  rw [truncatedKernel, ite_eq_left_iff.mpr fun h => absurd he h]

theorem truncatedKernel_of_not_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ (¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x)) : truncatedKernel L s n x e = 0 := by
  classical
  rw [truncatedKernel, ite_eq_right_iff.mpr fun h => absurd h he]

open Classical in
/-- The kernel of the ancestor layers on `block n x`: `L^{-sn}/(L^s - 1)` on its pairs. -/
def ancestorKernel (L s : ℝ) (n : ℕ) (x : ℕ →₀ A) (e : Sym2 (ℕ →₀ A)) : ℝ≥0 :=
  if ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x then (L ^ (-(s * n)) / (L ^ s - 1)).toNNReal else 0

theorem ancestorKernel_of_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x) :
    ancestorKernel L s n x e = (L ^ (-(s * n)) / (L ^ s - 1)).toNNReal := by
  classical
  rw [ancestorKernel, ite_eq_left_iff.mpr fun h => absurd he h]

theorem ancestorKernel_of_not_mem {L s : ℝ} {n : ℕ} {x : ℕ →₀ A} {e : Sym2 (ℕ →₀ A)}
    (he : ¬ (¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ block n x)) : ancestorKernel L s n x e = 0 := by
  classical
  rw [ancestorKernel, ite_eq_right_iff.mpr fun h => absurd h he]

end PercLib.Models.HierarchicalLayers
