# The square-root trick: advice for the wiki

Advice for the wiki agent on package P9 of the RSW plan
(`PercLib/Probability/SquareRootTrick.lean`). **The result is general, not planar.** It holds for
the configuration law `prodBernoulli q` on any index type `ι`, with any profile `q`, and for events
indexed by a finite set of any type; nothing in the file mentions `ℤ²`, crossings or arms, and it
sits in `Probability/`, not in `Models/Planar/`. Everything is proved with only `propext`,
`Classical.choice` and `Quot.sound`. No tags and no definitions were added.

## Conventions

`P` is `prodBernoulli q`. The real statements use `(prodBernoulli q).real`; the `ℝ≥0∞` ones use
`prodBernoulli q`. The events are `A a` for `a` in a `Finset` `s`, so there are `k = s.card` of
them; their union is `⋃ a ∈ s, A a`. "Increasing" is `IsUpperSet` (in the inclusion order on
`Set ι`) and every event is assumed measurable. The `k`-th root is the real power
`x ^ (s.card : ℝ)⁻¹`, and the maximum of the probabilities is `s.sup' hs (fun a => P.real (A a))`,
with `hs : s.Nonempty`.

## Statements as proved

- **The square-root trick** (`prodBernoulli_one_sub_rpow_le_sup'`): for a nonempty finite family
  of increasing measurable events,
  `1 - (1 - P(⋃ A a))^(1/k) ≤ max_{a ∈ s} P(A a)`.
  Existential form (`exists_one_sub_rpow_le_prodBernoulli_real`): some `b ∈ s` has
  `P(A b) ≥ 1 - (1 - P(⋃ A a))^(1/k)`.
- **Equal probabilities.** If every `P(A a) = p`, then `(1 - p)^k ≤ 1 - P(⋃ A a)`
  (`prodBernoulli_one_sub_pow_le_of_forall_eq`; no root, and `s` may be empty), and, for `s`
  nonempty, `1 - (1 - P(⋃ A a))^(1/k) ≤ p` (`prodBernoulli_one_sub_rpow_le_of_forall_eq`). This is
  the form used after a symmetry argument: if a symmetry of the law permutes the events and their
  union has probability at least `1 - ε`, each has probability at least `1 - ε^(1/k)`.
- **Two events** (increasing, measurable `A`, `B`):
  `(1 - P(A))(1 - P(B)) ≤ 1 - P(A ∪ B)` (`prodBernoulli_one_sub_mul_one_sub_le_one_sub_union`),
  `1 - √(1 - P(A ∪ B)) ≤ max(P(A), P(B))` (`prodBernoulli_one_sub_sqrt_le_max`, written with
  `Real.sqrt`), and, when `P(A) = P(B)`, `1 - √(1 - P(A ∪ B)) ≤ P(A)`
  (`prodBernoulli_one_sub_sqrt_le_of_eq`; the hypothesis is the real equality, which
  `congrArg ENNReal.toReal h` supplies from an `ℝ≥0∞` equality of laws).
- **The product bound** (`prodBernoulli_prod_one_sub_le_one_sub_biUnion` in `ℝ≥0∞`,
  `prodBernoulli_real_prod_one_sub_le_one_sub_biUnion` in `ℝ`):
  `∏_{a ∈ s} (1 - P(A a)) ≤ 1 - P(⋃ A a)` for increasing measurable events, any finite `s`.
- **Harris for finitely many decreasing events** (`prodBernoulli_prod_le_biInter_of_isLowerSet`,
  real form `prodBernoulli_real_prod_le_biInter_of_isLowerSet`):
  `∏_{a ∈ s} P(A a) ≤ P(⋂ A a)` for decreasing measurable events. This is the decreasing
  companion of `prodBernoulli_prod_le_biInter` (tag 22S9, increasing events), which PercLib did
  not have.
- **The real-number step** (`Finset.one_sub_rpow_le_sup'_of_prod_one_sub_le`): for any reals
  `x a ≤ 1` (`a ∈ s`, `s` nonempty) and `u` with `∏ (1 - x a) ≤ 1 - u`,
  `1 - (1 - u)^(1/k) ≤ max_a x a`. It knows nothing about probability; any measure satisfying
  the product bound gets the trick from it.

## Proof the Lean follows

The complements `A aᶜ` are decreasing, so Harris for decreasing events
(`prodBernoulli_harris_of_isLowerSet`, `HarrisDecreasing.lean`), iterated by induction on `s`,
gives `1 - P(⋃ A a) = P(⋂ A aᶜ) ≥ ∏ P(A aᶜ) = ∏ (1 - P(A a))`. With `m = max_a P(A a) ≤ 1`, each
factor is at least `1 - m ≥ 0`, so `(1 - m)^k ≤ 1 - P(⋃ A a)`; taking real `k`-th roots
(`Real.rpow_le_rpow`, `Real.pow_rpow_inv_natCast`) gives `1 - m ≤ (1 - P(⋃ A a))^(1/k)`. For two
events the root is `Real.sqrt` (`Real.sqrt_le_sqrt`, `Real.sqrt_sq`).

## Where it is used

The RSW route of the plan does not use it (plan §4: "not needed on this route"). The plan lists it
for the other RSW routes and for later arm-event work (quasi-multiplicativity and bounds of the
`ρ < 1/2` kind). If a wiki article states the trick as an assertion, these are the declarations to
tag: the general form `prodBernoulli_one_sub_rpow_le_sup'` (or its existential form), with the
equal-probability and two-event forms as corollaries. As a tag correspondence it belongs to a
general probability article (next to Harris, X5SS and 22S9), not to a planar one.

## Search

PercLib: `prodBernoulli_prod_le_biInter` (22S9, `OpenEventHarris.lean`) covers increasing events
only; the two-event decreasing and mixed forms are in `HarrisDecreasing.lean`; there was no
finite-product decreasing form and no square-root trick. Mathlib: Harris appears only as the
counting Harris–Kleitman inequality for finite set families
(`Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean`), not for product measures, and there is no
square-root trick. The real powers, `Finset.sup'`, `Finset.prod_le_prod₀`,
`probReal_compl_eq_one_sub` and `measureReal_le_one` are mathlib's.

## Sources

The plan cites V. Tassion, *Crossing probabilities for Voronoi percolation*, Ann. Probab. 44
(2016), arXiv:1410.6773v2, Proposition 4.1 (square-root trick), p. 11; that text was not re-read
for this package. The argument is the standard one-line consequence of Harris's inequality and
needs nothing from that paper.
