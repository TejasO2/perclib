# Two- and three-point bounds at 1/2 on ℤ²: advice for the wiki

Advice for the wiki agent on package P8 of the RSW plan
(`PercLib/Models/Planar/Arms/TwoPoint.lean` and `PercLib/Models/Planar/Arms/ThreePoint.lean`).
The first file proves Y8K3 (`critical-exponents`, §"One arm at each endpoint"): the two-point
function is comparable to the square of the one-arm probability, with the exponent consequences
that Y8K3 lists. The second proves the lower two-scale bound of K8A1 (`critical-exponents`,
§"Three points at two scales"). **The upper half of K8A1 is not proved**: it needs the
three-point product inequality of tag 87RB, which PercLib does not have. K8A1 should not be
tagged until 87RB exists. Everything is proved with only `propext`, `Classical.choice` and
`Quot.sound`. No tags or definitions were added.

## Conventions

These are as in `arm-events.md`, `separator.md` and `one-arm.md`:

- "At `1/2`" is the hypothesis `∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2`.
- "No other pair is ever open" is `∀ e ∉ (zdGraph 2).edgeSet, q e = 0`, the convention of
  `Percolation/Bond/Host.lean` (BP7B). The plan calls it `NN0`.
- The wiki's `A(r)` is `(law q).real (armEvent 0 r)` (real) or `law q (armEvent 0 r)` (`ℝ≥0∞`).
- `τ_{p_c}(0, x)` is the library's `tau q 0 x = law q (conn 0 x)`, a value in `ℝ≥0∞`, used as
  `(tau q 0 x).toReal`. It counts every open pair, which is why the upper bounds need the second
  hypothesis.
- `‖x‖∞` is written `max (x 0).natAbs (x 1).natAbs`, a natural number, so that it can be an arm
  radius.
- `‖x - y‖∞` is written `max (x 0 - y 0).natAbs (x 1 - y 1).natAbs`.
- In the exponent statements the denominator is `Real.log ‖x‖`. Here `‖x‖` is mathlib's norm on
  `Fin 2 → ℤ`, which is the sup norm (`EisensteinSeries.norm_eq_max_natAbs`).
- "`x → ∞` over all vertices" is the filter `Filter.cofinite` on `LatticeSite 2`. On `ℤ²` it
  equals `‖x‖ → ∞`, since bounded sets are finite.
- The wiki's `t(a, b, c)` ("`a`, `b`, `c` lie in one open cluster") is
  `law q (conn a b ∩ conn a c)`. This is the library's way of writing three-point events
  (`TreeGraph/BranchPoint.lean`).
- `fourStrip z n` is the four-strip event of `arm-events.md`, the wiki's circuit `C_n` around
  `z`.

## Statements as proved

### Y8K3 (`TwoPoint.lean`)

- **T6, the comparison** (`exists_tau_comparable_armEvent_sq`). This is the plan's statement
  word for word, with `supNat x` written as `max (x 0).natAbs (x 1).natAbs`. There are real
  constants `0 < c ≤ C` such that, for every `q` at `1/2` with no other pair open and every
  `x ≠ 0`,

  `c · A(‖x‖∞)² ≤ τ(0, x)` and `τ(0, x) ≤ C · A(‖x‖∞)²`.

  The constants are chosen before `q` and `x`. This is Y8K3's display. The wiki has `p_c`;
  here it is `1/2` directly, which is `p_c(ℤ²)` by T3 (`critical-probability.md`).
- **Lower half alone** (`exists_pos_mul_law_armEvent_sq_le_tau`). There is `c > 0` with
  `c A(‖x‖∞)² ≤ τ(0, x)` for every `x ≠ 0` and every `q` at `1/2`, whatever the profile off the
  edges. More open pairs only help.
- **Upper half alone** (`exists_tau_le_mul_law_armEvent_sq`). There is `C > 0` with
  `τ(0, x) ≤ C A(‖x‖∞)²`, for every `q` at `1/2` with no other pair open.
- **Logarithmic exponents** (`tendsto_neg_log_law_armEvent_div_log_iff`). For every `q` at
  `1/2` with no other pair open and every real `L`, the following are equivalent:
  - `-log A(r) / log r → L` as `r → ∞` in `ℕ`;
  - `-log τ(0, x) / log ‖x‖ → 2L` as `x → ∞` over all vertices.

  In BLNL's conventions (`d = 2`), `1/ρ = L` and `η = d - 2 + η = 2L`, so this is Y8K3's
  "they then satisfy `η = 2/ρ`".
- **Existence** (`exists_tendsto_neg_log_law_armEvent_div_log_iff`). The one-arm logarithmic
  limit exists if and only if the two-point logarithmic limit exists over all vertices. This is
  Y8K3's "the logarithmic one-arm exponent exists if and only if the logarithmic two-point
  exponent exists as a limit over all vertices tending to infinity".
- **The limits are positive and finite**
  (`exists_pos_le_of_tendsto_neg_log_law_armEvent_div_log`). There are `0 < a` and `b` such that
  every limit `L` of `-log A(r) / log r` satisfies `a ≤ L ≤ b`, for every `q` at `1/2`. These
  are the exponents of XB1U's polynomial bounds. This is Y8K3's remark that "the polynomial
  bounds in XB1U make either limit, if it exists, positive and finite". It is the condition
  BLNL puts on `ρ`.
- **Power laws** (`exists_armEvent_rpow_bounds_iff_exists_tau_rpow_bounds`). For every `q` at
  `1/2` with no other pair open and **every real `s`** (the wiki says `s > 0`; the proof needs
  nothing), the following are equivalent:
  - `∃ c, C > 0` with `c r^{-s} ≤ A(r) ≤ C r^{-s}` for all integers `r ≥ 1`;
  - `∃ c, C > 0` with `c ‖x‖^{-2s} ≤ τ(0, x) ≤ C ‖x‖^{-2s}` for all `x ≠ 0`.

  This is Y8K3's "`A(r) ≍ r^{-s}` is equivalent to `τ_{p_c}(0, x) ≍ ‖x‖^{-2s}`, uniformly in
  `x ≠ 0`".

### Building blocks (`TwoPoint.lean`)

- `tau_le_law_armEvent_sq` (`ℤ^d`, `ℝ≥0∞`). Take a profile constant `p` on the edges and `0`
  off them. If `2m < |x i|` for some coordinate `i`, then `τ(0, x) ≤ A(m)²`. This is the wiki's
  `τ ≤ A(m)²`.
- `law_armEvent_sq_mul_law_fourStrip_le_tau` (`ℝ≥0∞`). Take a profile constant on the edges,
  any profile off them. If `‖x‖∞ ≤ 2n` and `6n ≤ R`, then `A(R)² · P(fourStrip 0 n) ≤ τ(0, x)`.
  The wiki's lower bound is the case `n = r`, `R = 8r`.
- `inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent` (deterministic). On
  `fourStrip z n`, two points of `B_{2n}(z)` with arms of radii at least `6n` are joined by an
  open path inside `B_{4n}(z)`. This is the wiki's "both arms therefore meet the same open
  circuit". `ThreePoint.lean` uses it too.
- `mem_armEvent_inter_armEvent_of_mem_conn` (deterministic, `ℤ^d`). If `x ↔ y` by open edges and
  `y ∉ x + [-(m - 1), m - 1]^d`, then both `x` and `y` have arms of radius `m`. This is the
  wiki's "a connection from zero to `x` forces an arm inside each of `B_m(0)` and `B_m(x)`".
- `law_armEvent_add`, `law_armEvent_eq_law_armEvent_zero` (`ℤ^d`, profile constant on the
  edges). Translation invariance of the one-arm probability: `A` at `x` equals `A` at `0`.
- `exists_pos_mul_law_armEvent_le_eight_mul`. There is `c > 0` with `c A(r) ≤ A(8r)` for every
  `r` and every `q` at `1/2`. This is three of XB1U's doublings, with the constant cubed.

### K8A1, lower half (`ThreePoint.lean`)

- **T7** (`exists_le_law_conn_inter_conn`). There is `c₃ > 0` such that, for every `q` at
  `1/2`, all points `a ≠ b` and `c` with `s = ‖a - b‖∞ ≤ R = ‖a - c‖∞`,

  `c₃ · A(s) · A(R)² ≤ P(a ↔ b, a ↔ c)`.

  The constant comes before `q` and the points. K8A1's hypotheses (distinct points, `s` the
  smallest and `R` the largest pair distance) imply `a ≠ b` and `s ≤ R`, so this is the lower
  two-scale bound of K8A1. It needs no hypothesis off the edges. The case `s = R` is included,
  as the wiki says.
- `law_armEvent_mul_law_fourStrip_le_law_conn_inter_conn` (`ℝ≥0∞`). Take a profile constant on
  the edges, with `‖a - b‖∞ ≤ 2n`, `‖a - c‖∞ ≤ 2N` and `n ≤ N`. Then
  `A(8n) A(8N)² P(fourStrip a n) P(fourStrip a N) ≤ P(a ↔ b, a ↔ c)`.

## Proof the Lean follows

1. *Two-point, upper bound.* This follows the wiki, for `r = ‖x‖∞ ≥ 3` and `m = ⌊r/3⌋ ≥ 1`.
   - A connection from `0` to `x` reaches `x`, which lies outside `B_{m - 1}(0)`. So it gives an
     arm of radius `m` at `0` (`mem_armEvent_of_mem_conn`). Reversed, it gives one at `x`.
   - `τ` counts all pairs. The second hypothesis makes `ω ⊆ L` almost surely
     (`ae_config_subset_host`), so the inclusion holds almost surely (`measure_mono_ae`).
   - `B_m(0)` and `B_m(x)` are disjoint because `2m < r`. Each arm event is determined by the
     pairs inside its box (`mem_armEvent_iff_of_inter_eq`). So the two events are independent
     (`law_inter_of_determined_internalPairs`).
   - Translation (`law_armEvent_eq_law_armEvent_zero`) gives `τ ≤ A(m)²`.
   - As in the wiki, `r ≤ 5m < 8m`, so `A(r) ≥ A(8m) ≥ c³ A(m)`. Hence `τ ≤ c^{-6} A(r)²`.
   - For `r ≤ 2` the wiki uses `τ ≤ 1` and `A(2) > 0`. The Lean makes this uniform in the
     profile: `A(r) ≥ A(2) ≥ 1/4` (straight arm, `inv_two_pow_le_law_armEvent`), so
     `τ ≤ 1 ≤ 16 A(r)²`.
   - The constant is `C = max(c^{-6}, 16)`, with `c` the doubling constant.
2. *Two-point, lower bound.* This also follows the wiki.
   - Take `fourStrip 0 r`, an arm of radius `8r` at `0` and one at `x`.
   - Both points lie in `B_{2r}`.
   - The arm at `0` leaves `B_{4r - 1}`. So does the arm at `x`, since its end is at distance at
     least `8r - r = 7r` from `0`.
   - Circuit gluing in its escape form (`inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn`,
     `separator.md`) joins them.
   - Harris's inequality twice (X5SS), T4 (`c₀`) and three doublings give
     `τ ≥ c₀ A(8r)² ≥ c₀ c⁶ A(r)²`.
   - The constant is `min(c₀, 1) · c⁶`. The `min` keeps it finite after `toReal`.
   - The comparison takes `min` of the two lower constants, so that `c ≤ C`.
3. *Exponents.* This is the wiki's argument with the error term made explicit.
   - From the comparison, `|log τ(0, x) - 2 log A(‖x‖∞)| ≤ K = |log c| + |log C|` for `x ≠ 0`.
     `A > 0` by the straight arm.
   - Hence `|G(x) - 2F(‖x‖∞)| ≤ K / log ‖x‖∞`, where:
     - `G(x) = -log τ(0, x) / log ‖x‖`;
     - `F(r) = -log A(r) / log r`;
     - `‖x‖ = ‖x‖∞`.
   - One direction: along the cofinite filter `‖x‖∞ → ∞` (`tendsto_norm_cocompact_atTop`,
     `cocompact_eq_cofinite`), so `F → L` gives `G → 2L`.
   - Other direction: along `x = (r, 0)`, an injective sequence, so it tends to infinity in the
     cofinite filter. There `G → 2L` gives `F → L`.
   - Positivity: `c R^{-b} ≤ A(R) ≤ C R^{-a}` (`exists_armEvent_polynomial_bounds`) gives
     `a - log C / log R ≤ F(R) ≤ b - log c / log R`.
   - Power laws: substitute the comparison, using `(r^{-s})² = r^{-2s}`. For the converse, take
     square roots at `x = (r, 0)`.
4. *Three-point lower bound.* This follows the wiki.
   - The arms have radii `8R` at `a`, `8s` at `b` and `8R` at `c`.
   - The circuits are `fourStrip a s` and `fourStrip a R`, i.e. the annuli
     `2s ≤ ‖· - a‖∞ ≤ 4s` and `2R ≤ ‖· - a‖∞ ≤ 4R`.
   - The first joins `a` to `b` (both points in `B_{2s}(a)`, radii `8R, 8s ≥ 6s`). The second
     joins `a` to `c` (both points in `B_{2R}(a)`, radii `8R ≥ 6R`).
   - Harris's inequality four times, T4 twice and three doublings at each arm scale give
     `t ≥ c₀² A(8s) A(8R)² ≥ c₀² c⁹ A(s) A(R)²`, the wiki's constant.
   - When `s = R` the two circuit events are the same event, and Harris still applies.

## Statement choices compared with the plan and the wiki

- **T6** is the plan's statement exactly (§2.7). Its hypotheses are SOURCE: `1/2 = p_c`,
  nearest-neighbour with no other pair open, and `x ≠ 0`.
- **The exponent clauses** are four theorems, since Y8K3 states them in words.
  - Existence and the relation `η = 2/ρ` are one iff, for each `L`, plus the existence
    corollary.
  - Positivity is the theorem `a ≤ L ≤ b`.
  - The power-law clause is stated for every real `s`. This is more general than the wiki's
    `s > 0` and costs nothing; for `s < 0` both sides are false.
  - The denominators are `log r` and `log ‖x‖`, the BLNL normalisation. At `r = 1` or
    `‖x‖ = 1` the quotient is `0` (division by zero), which does not affect limits.
  - For tagging Y8K3, the display is `exists_tau_comparable_armEvent_sq`. Whether the tag also
    restates the exponent clauses as conjuncts is the wiki's choice.
- **T7.** The plan only names it (`exists_le_law_threePoint ... c₃ A(s) A(R)² ≤ P(...)`). The
  Lean name is `exists_le_law_conn_inter_conn`. Its hypotheses are weaker than K8A1's: only
  `a ≠ b` and `‖a - b‖∞ ≤ ‖a - c‖∞`, with no hypothesis off the edges. So the stated bound is
  stronger. The relabelling convention of K8A1 is not needed: the proof uses only that `s` is
  the distance from `a` to `b` and `R` the distance from `a` to `c`, with `s ≤ R`.
- **Not proved: K8A1's ratio bounds.** The lower bound `0 < c₄ ≤ t / √(τ(a,b) τ(a,c) τ(b,c))`
  does not need 87RB. It follows from T7, the upper half of T6 and `A(R) ≤ A(‖b - c‖∞) ≤
  c^{-1} A(R)`. It does need translation invariance of `τ` on `ℤ²`
  (`τ(a, b) = τ(0, b - a)`), which PercLib does not have as a lemma. It was outside this
  package's target and is a possible follow-up. The upper ratio bound `2√2` and the upper
  two-scale bound need 87RB.
- **K8A1 upper half: open.** There is no `@[tag "87RB"]` in PercLib (plan §3.3). Do not tag
  K8A1, and do not tag UQ4B, which depends on K8A1. The lower half is available for a future
  K8A1 proof as `exists_le_law_conn_inter_conn`.

## Search

- **Mathlib.** The sup norm of `Fin 2 → ℤ` is `EisensteinSeries.norm_eq_max_natAbs`
  (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Summable.lean`). It is imported, not
  copied; a local copy written first was removed. Other mathlib lemmas used:
  - limits along the cofinite filter: `tendsto_norm_cocompact_atTop`, `cocompact_eq_cofinite`,
    `Function.Injective.tendsto_cofinite`, `Nat.cofinite_eq_atTop`,
    `tendsto_natCast_atTop_iff`;
  - squeezing: `squeeze_zero_norm'`, `Filter.Tendsto.div_atTop`, `Real.tendsto_log_atTop`,
    `le_of_tendsto_of_tendsto`;
  - logarithms and powers: `Real.log_le_log`, `Real.log_mul`, `Real.log_pow`,
    `Real.log_rpow`, `Real.rpow_mul_natCast`, `Real.sq_sqrt`, `pow_le_pow_iff_left₀`.
- **PercLib.** No two-point or three-point bound on `ℤ²` existed. No law-level translation of
  `armEvent` existed: `Arms/Defs.lean` has the configuration level only, so
  `law_armEvent_add` adds it from `law_preimage_image_sym2Map_eq` (`SelfDuality.lean`), as
  `law_crossing_add` does for crossings. Translation invariance of `tau` on `ℤ^d` is not in
  PercLib either: only hypotheses `hinv` in `CorrelationLength.lean` and a hierarchical-lattice
  lemma. `conn x y ∩ conn x z` is the existing three-point convention.
- **Reused:**
  - circuit gluing and T4 (`separator.md`);
  - the doubling and polynomial bounds (`one-arm.md`);
  - the stopping lemma, determination and translation of `armEvent` (`arm-events.md`);
  - `ae_config_subset_host` (`Bond/Host.lean`);
  - the independence lemmas of `Bond/DomainIndependence.lean`;
  - Harris (`prodBernoulli_harris`, X5SS).

## Sources

The proofs are the wiki's proofs of Y8K3 and of the lower half of K8A1, with the changes listed
above. The circuit and arm inputs are as in `separator.md` and `one-arm.md`. H. Duminil-Copin,
*Introduction to Bernoulli percolation*, lecture notes, 7 October 2018, Section 4, Corollary 4.7,
pp. 23–24 (located by the plan; not re-read for this package). Gladkov's discussion that K8A1
refers to (arXiv:2408.08457v1, §6.3) was not read for this package.
