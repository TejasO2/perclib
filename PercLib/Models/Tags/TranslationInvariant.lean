/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrapper for the row sums of translation-invariant kernels
(displacement-kernels article). All mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.TranslationInvariant

/-!
# Row sums of translation-invariant kernels: statement form

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `rowSum_of_translationInvariant_offDiag`
-/

@[expose] public section
noncomputable section
open scoped ENNReal NNReal

namespace PercLib.Models

variable {G : Type*} [AddGroup G]

open Classical in
/-- If `J(x,y) = k(y - x)` for distinct `x, y` (the diagonal is arbitrary), every
off-diagonal row of `J` equals `∑_{z ≠ 0} k(z)`, which is at most `∑_z k(z)`. -/
@[tag "R01V"]
theorem rowSum_of_translationInvariant_offDiag (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, x ≠ y → J s(x,y) = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) =
        (∑' z, if z = 0 then 0 else (k z : ℝ≥0∞)) ∧
      (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ ∑' z, (k z : ℝ≥0∞) :=
  ⟨rowSum_eq_of_translationInvariant_of_ne J k hJ v,
    rowSum_le_tsum_of_translationInvariant_of_ne J k hJ v⟩

end PercLib.Models
