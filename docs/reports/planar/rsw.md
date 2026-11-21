# RSW on ℤ²: advice for the wiki

Advice for the wiki agent on package P4 of the RSW plan (`PercLib/Models/Planar/RSW.lean`).
This is Step 5 of the wiki's proof of WD31 (`critical-exponents`, §"The square-lattice crossing
input") and Corollary 7 of Bollobás–Riordan. Everything is proved with only `propext`,
`Classical.choice` and `Quot.sound`; no tags were added.

## Statements as proved

Conventions as in `duality.md`, `gluing.md` and `rsw-key-step.md`: boxes are `Set.Icc lo hi` on
`Fin 2 → ℤ`, `crossing 0` is left-right and `crossing 1` bottom-top. "At `1/2`" means the
hypothesis `∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2`: every edge of `ℤ²` is open with
probability `1/2`, and the profile off the edges is arbitrary (crossings read only the edges of
`ℤ²`). This is the convention of `law_crossing_zero_eq_half`. All probabilities are in `ℝ≥0∞`.

- **RSW, the crossing conjunct of WD31** (`exists_pos_le_law_crossing_zero`): for each integer
  `k ≥ 2` there is `c > 0` such that for every `q` at `1/2` and every integer `n ≥ 1`,
  `P([0, 2kn] × [0, 2n] has an open left-right crossing) ≥ c`. The quantifiers are in the wiki's
  order: `c` is chosen after `k` and before `q` and `n`. The hypothesis `2 ≤ k` is kept because
  the wiki states it; the proof does not use it.
- **Doubling, at `1/2`** (`law_crossing_zero_sq_le`): for `1 ≤ n ≤ m`, with
  `g(w) = P(H([0, w] × [0, 2n]))`, `g(m)² ≤ 2⁵ · g(2m - n)`. This is the displayed inequality
  `g(2m - n) ≥ g(m)²/2⁵` of Step 5.
- **Doubling, for every profile constant on the edges** (`law_crossing_zero_sq_mul_pow_three_le`):
  if every edge of `ℤ²` is open with the same probability `p`, then for `1 ≤ n ≤ m`,
  `P(H([0, m] × [0, 2n]))² · P(H(S))³ ≤ 4 · P(H([0, 2m - n] × [0, 2n]))`, with `S = [0, n]²`.
  The `1/2` form follows from `P(H(S)) ≥ 1/2`. The wiki can quote this form if it ever needs
  RSW-type doubling away from `1/2`; the wiki's text only needs the `1/2` form.
- **Iteration** (`le_law_crossing_zero_two_pow_add_one_mul`): at `1/2`, for every `n ≥ 1` and
  `j`, `g((2^j + 1) n) ≥ 2⁵ · 2^(-6 · 2^j)`, which is the wiki's `g(w_j) ≥ 2^(5 - 6 · 2^j)`.
- **Any position, either direction, every aspect ratio** (`exists_pos_le_law_crossing`): for
  each `k` there is `c > 0` such that for every `q` at `1/2`, every corner `lo ∈ ℤ²` and every
  `n ≥ 1`, the box `lo + [0, kn] × [0, n]` has an open left-right crossing and the box
  `lo + [0, n] × [0, kn]` an open bottom-top crossing, each with probability at least `c`. This
  covers the wiki's remark "Translations and quarter-turns give the corresponding statements in
  other positions and orientations", and more: the height `n` may be odd, and `k` may be `0`
  or `1`.
- Two auxiliary bounds at `1/2`:
  - `one_half_le_law_crossing_zero`: a box `[lo, hi]` with `hi₀ - lo₀ ≤ hi₁ - lo₁ + 1`, so at
    most one wider than tall, is crossed from left to right with probability at least `1/2`.
    This is the wiki's Step 3 applied to squares (`[0, n]²` and `[0, 2n]²`).
  - `inv_two_pow_le_law_crossing_zero`: the row `[0, k] × [0, 0]` is crossed with probability
    at least `2^(-k)`, the probability that its `k` edges are open. It is the bound
    "`2^(-7)`, the probability that a straight path of seven edges is open" of Step 6, and P5
    will use it there.

## Proof the Lean follows

The doubling and the iteration are Step 5 as written, with these differences.

1. *Gluing.* On `E₁ ∩ E₂ ∩ E₃` the Lean applies the gluing lemma of `Gluing.lean`
   (`inter_edgeSet_mem_localConn_of_crossings`, the connection form of Step 1) in `S` twice: once
   to `H(S)` and the vertical crossing of `E₁`, once to `H(S)` and the reflected vertical
   crossing of `E₂`. It then chains the five connections with `localConn_trans`. In the library a
   crossing of a box is a connection inside the box between a vertex on each of the two sides,
   so no path has to be cut at its last vertex with `x = n - m`. The crossing obtained is of
   `[n - m, m] × [0, 2n]`, and translation by `m - n` gives `[0, 2m - n] × [0, 2n]`.
2. *Harris* is the two-event inequality `prodBernoulli_harris` (tag X5SS) used twice, for
   `E₁ ∩ E₂` and then `E₃`. The proof-use record of WD31 lists X5SS. `E₁` is the event of the key
   step written out (`rsw-key-step.md`); its measurability and monotonicity are proved inside the
   doubling proof. `E₂` is the preimage of `E₁` under the reflection `x ↦ n - x`, and
   `P(E₂) = P(E₁)` by `law_preimage_image_sym2Map_eq`.
3. *`P(V(S)) = P(H(S))`* comes from the coordinate swap (`law_crossing_one_eq_law_crossing_zero`,
   `crossing-symmetry.md`), at any constant `p`.
4. *Constants.* The Lean proves `g(w_j) ≥ 2⁵ · 2^(-6 · 2^j)` by induction on `j`. The induction
   is equivalent to the wiki's `a_{j+1} + 5 ≤ 2(a_j + 5)` but avoids logarithms. For T1 it
   takes `j = k + 1`, not the least `j_k` with `2^{j_k} + 1 ≥ 2k`. Since `k < 2^k`,
   `2^{k+1} + 1 ≥ 2k`. So the Lean's constant is `2^(5 - 6 · 2^{k+1})`, smaller than the wiki's
   `c_k`. The statement only asserts that some `c_k > 0` exists, so the wiki's `c_k` is still
   correct; the Lean does not prove that particular value.
5. *Any position.* Translation (`law_crossing_add`) and the swap reduce to the left-right
   crossing of `[0, kn] × [0, n]`. For `n ≥ 2` it contains a crossing of
   `[0, (2^{k+2} + 1) n'] × [0, 2n']` with `n' = ⌊n/2⌋ ≥ 1`, by the inclusion for narrower and
   taller boxes (`crossing_zero_subset_crossing_zero`), since `2n' ≤ n` and `kn ≤ 3kn' ≤
   (2^{k+2} + 1) n'`. For `n = 1` the bottom row bound gives `2^(-k)`. The constant is the
   minimum of the two.

## Sources

B. Bollobás and O. Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math.
Soc. 38 (2006), 470–484, arXiv math/0410359v3, Corollary 7, p. 8. Their Corollary 7 is stated
for `2ρn × 2n` boxes; the Lean, like the wiki, uses the integer widths `2kn` and the widths
`(2^j + 1) n` of the iteration.
