# One-arm bounds at 1/2 on ℤ²: advice for the wiki

Advice for the wiki agent on package P7 of the RSW plan
(`PercLib/Models/Planar/Arms/OneArm.lean`). This is XB1U (`critical-exponents`,
§"Extending an arm and blocking it"): the doubling bound `A(2r) ≥ cA(r)`, the two polynomial
scale bounds `c(R/r)^{-b}A(r) ≤ A(R) ≤ C(R/r)^{-a}A(r)`, and the "in particular" clauses
(`A(r)` between two positive powers of `r`, `A(r) → 0`). Everything is proved with only
`propext`, `Classical.choice` and `Quot.sound`; no tags and no definitions were added.

## Conventions

As in `arm-events.md` and `separator.md`: boxes are `Set.Icc lo hi` on `Fin 2 → ℤ`,
`(r : LatticeSite 2)` is the constant vector `r`, so `Icc (0 - r) (0 + r)` is `B_r = [-r, r]²`,
and only the open nearest-neighbour edges `ω ∩ (zdGraph 2).edgeSet` are read. "At `1/2`" is the
hypothesis `∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2`: every edge of `ℤ²` is open with
probability `1/2`, and the profile off the edges is arbitrary. The wiki's
`A(r) = P_{1/2}(0 ↔ ∂B_r)` is `(law q).real (armEvent 0 r)` in the real statements and
`law q (armEvent 0 r)` (in `ℝ≥0∞`) in the others. `armEvent 0 r` is the arm stopped on first
reaching the boundary, an event on the edges inside `B_r`; its bridge to the unrestricted event
`0 ↔ ∂B_r` is `mem_armEvent_iff_exists_conn` (`arm-events.md`). `(R / r : ℝ) ^ (-b)` is the real
power `Real.rpow`. `fourStrip 0 n` is the four-strip event of `arm-events.md` (the wiki's circuit
`C_n`). The blocking event at scale `s` is the one of `critical-probability.md`: none of the
strips `[-3s, 3s] × [s, 3s]`, `[-3s, 3s] × [-3s, -s]`, `[s, 3s] × [-3s, 3s]`,
`[-3s, -s] × [-3s, 3s]` has an open crossing in its short direction.

## Statements as proved

- **T5, one-arm bounds** (`exists_armEvent_bounds`, the plan's statement): there are real
  constants `c, C, a, b > 0` such that for every `q` at `1/2` and all integers `1 ≤ r ≤ R`,
  `c · A(r) ≤ A(2r)`, `c · (R/r)^{-b} · A(r) ≤ A(R)` and `A(R) ≤ C · (R/r)^{-a} · A(r)`. The four
  constants are chosen before `q`, `r` and `R`, and the same `c` serves the doubling and the
  lower bound, as in the wiki. This is XB1U's displayed statement word for word.
- **The limit** (`tendsto_law_armEvent_zero`): for every `q` at `1/2`, `A(r) → 0` as `r → ∞`
  (stated in `ℝ≥0∞`, `Filter.Tendsto (fun r : ℕ => law q (armEvent 0 r)) atTop (𝓝 0)`). This is
  XB1U's "tends to zero".
- **Polynomial bounds** (`exists_armEvent_polynomial_bounds`): there are `c, C, a, b > 0` such
  that for every `q` at `1/2` and every integer `R ≥ 1`, `c R^{-b} ≤ A(R) ≤ C R^{-a}`. This is
  XB1U's "`A(r)` lies between two positive polynomial bounds"; it is T5 at `r = 1`, with
  `A(1) ≥ 1/2` and `A(1) ≤ 1`.
- **Doubling** (`exists_pos_mul_law_armEvent_le`, in `ℝ≥0∞`): there is `c ∈ (0, 1)` such that for
  every `q` at `1/2` and every `r ∈ ℕ` (including `r = 0`), `c · A(r) ≤ A(2r)`. The wiki's
  `A(2r) ≥ cA(r)` with `c ∈ (0, 1)`.
- **Blocking at many scales** (`exists_law_armEvent_le_pow_mul`, in `ℝ≥0∞`): there is
  `ρ ∈ (0, 1)` such that for every `q` at `1/2`, all `r ≤ R` and every `N` with
  `3 (r + 1) 4^j ≤ R` for all `j < N`, `A(R) ≤ ρ^N A(r)`. The wiki's
  `A(R) ≤ A(r)(1 - c_0)^N`, with other scales (below).
- **Extending an arm** (`mem_armEvent_of_mem_fourStrip_of_mem_crossing`, deterministic): if
  `4n ≤ r`, `4n ≤ m` and `R ≤ m`, every configuration with an arm of radius `r`, the four-strip
  event `fourStrip 0 n` and a left-right crossing of `[0, m] × [-n, n]` has an arm of radius
  `R`. The wiki's "these three increasing events imply `0 ↔ ∂B_{2r}`" (`m = 30n`, `R = 2r`).
- **Blocking an arm** (`notMem_armEvent_of_notMem_crossing`, deterministic): on the blocking
  event at scale `s`, the origin has no arm of any radius `R ≥ 3s`. The wiki's "such a circuit
  blocks every primal arm from zero".
- **A straight arm** (`inv_two_pow_le_law_armEvent`): at `1/2`, `A(r) ≥ 2^{-r}` for every `r`
  (the segment from the origin to `(r, 0)` open).

## Proof the Lean follows

1. *Doubling, `r ≥ 8`.* As the wiki: `n = ⌊r/8⌋ ≥ 1`; the arm of radius `r`, `fourStrip 0 n`
   and a left-right crossing of `[0, 30n] × [-n, n]` give an arm of radius `2r`. The arm leaves
   `B_{4n - 1}` since `r ≥ 8n`; the crossing starts at `x = 0`, `|y| ≤ n`, inside `B_{2n}`, and
   ends at `x = 30n ≥ 4n`; circuit gluing in its escape form
   (`inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn`, `separator.md`) joins the
   origin to the start of the crossing, and the end of the crossing lies outside `B_{2r - 1}`
   since `2r ≤ 16n + 14 ≤ 30n`; stopping on first reaching the boundary
   (`mem_armEvent_of_mem_conn`) gives the arm of radius `2r`. Harris's inequality (X5SS) twice,
   T4 (`exists_pos_le_law_fourStrip`, `c₀`) and RSW in any position (`exists_pos_le_law_crossing
   15` at height `2n`, the box `[0, 30n] × [-n, n]` being `15 · 2n × 2n`, `c₁₅`) give
   `A(2r) ≥ c₀ c₁₅ A(r)`.
2. *Doubling, `r < 8`.* The wiki: the finitely many ratios `A(2r)/A(r)` are positive. The Lean
   gives a bound uniform in the profile: `A(2r) ≥ 2^{-2r} ≥ 2^{-16} ≥ 2^{-16} A(r)`, by the
   straight arm. The constant is `c = min(c₀ c₁₅, 2^{-16}) ∈ (0, 1)`.
3. *Lower bound.* As the wiki: with `k` the least integer such that `R ≤ 2^k r` (that is
   `k = ⌈log₂(R/r)⌉`, found with `Nat.find`), `A(R) ≥ A(2^k r) ≥ c^k A(r)`. Minimality gives
   `2^k r < 2R`, so with `b = -log₂ c` (`c = 2^{-b}`),
   `c^k = (2^k)^{-b} ≥ (2R/r)^{-b} = c (R/r)^{-b}`.
4. *Upper bound.* The wiki blocks arms with closed dual circuits around `(1/2, 1/2)` in the
   annuli between radii `2n - 1` and `4n + 1`, at the scales `n_j = 2r 8^j`, for `R ≥ 16r`. The
   Lean uses the primal blocking event of WD31 Step 6 (`critical-probability.md`): four strips
   around the annulus `s ≤ ‖·‖∞ ≤ 3s` with no open crossing in their short direction. By
   vertical duality this is the event that the four dual strips are crossed in their long
   direction by closed dual paths, i.e. the wiki's closed dual circuit, which is never
   extracted. Blocking (`notMem_localConn_of_notMem_crossing`) excludes every arm of radius
   `R ≥ 3s`. Scales: `s_j = (r + 1) 4^j` for `j < N`, `N` the least integer with
   `R < 3 (r + 1) 4^N` (so `3 s_j ≤ R` for `j < N`). The arm of radius `r` is determined by the
   pairs inside `B_r` (`mem_armEvent_iff_of_inter_eq`), each blocking event by the pairs inside
   its annulus (`mem_crossing_iff_of_inter_eq`); the annuli are disjoint from `B_r`
   (`s_0 = r + 1 > r`) and from each other (`3 s_j < s_{j+1}`). Independence
   (`law_inter_of_determined_internalPairs` for the box against the union of the annuli, then
   `law_biInter_of_determined_internalPairs` across the annuli) and the blocking probability
   (`exists_pos_le_law_blocking`, `c_b`) give `A(R) ≤ ρ^N A(r)` with `ρ = 1 - min(c_b, 1/2)`.
   With `a = -log₄ ρ` (`ρ = 4^{-a}`) and `4^N > R/(3(r + 1)) ≥ R/(6r)`,
   `ρ^N = (4^N)^{-a} ≤ (R/(6r))^{-a} = 6^a (R/r)^{-a}`, so `C = 6^a`. The case `N = 0`
   (`R < 3(r + 1)`) is included: then `A(R) ≤ A(r)` and `C (R/r)^{-a} > 1`. So there is no
   separate case `r ≤ R < 16r` as in the wiki.
5. *In particular.* `A(R) → 0`: `A` is decreasing and `A(3 · 4^N) ≤ ρ^N A(0) = ρ^N`, so its
   infimum is `0` (`tendsto_atTop_iInf`). The polynomial bounds are T5 at `r = 1`. XB1U's last
   sentence, "there is almost surely no infinite open cluster at `p_c`", is already proved
   without arm events, by blocking directly (`law_cluster_infinite_eq_zero_of_half`,
   `law_exists_cluster_infinite_eq_zero_of_half`, `critical-probability.md`).

## Statement choices compared with the plan

`exists_armEvent_bounds` and `tendsto_law_armEvent_zero` are the plan's statements (§2.7), with
`NN q` written out as `∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2`. The plan's §3.2 lists the
"in particular" clauses as `tendsto_law_armEvent_zero`, the lower polynomial bound at `r = 1`,
and T2; the polynomial bounds at `r = 1` (both sides) are the added corollary
`exists_armEvent_polynomial_bounds`. Constants are quantified before the profile, as the plan
requires; the wiki has one measure, so this is stronger. `c < 1` is not part of T5 (the wiki
uses `c ∈ (0, 1)` only inside the proof); the `ℝ≥0∞` doubling lemma states it. The upper bound
uses the primal blocking event and the scales `(r + 1) 4^j` instead of the wiki's dual circuits
at the scales `2r 8^j` (item 4); the constants `a` and `C` differ accordingly, the statement does
not. For tagging XB1U, the displayed bounds are `exists_armEvent_bounds`; whether the tag also
restates the limit and the polynomial bounds as conjuncts is the wiki agent's call (plan §3.2).

## Search

PercLib: no one-arm bound existed; `armEvent` is used only in `Arms/Defs.lean` and
`Arms/Separator.lean`. The doubling reuses circuit gluing and T4 (`separator.md`), RSW in any
position (`rsw.md`), the straight-row bound `inv_two_pow_le_law_crossing_zero` (`rsw.md`) and
Harris (`prodBernoulli_harris`, X5SS); the upper bound reuses the blocking lemma and probability
and the crossing determination lemma (`critical-probability.md`), `mem_armEvent_iff_of_inter_eq`
and `armEvent_anti` (`arm-events.md`), and the independence lemmas of
`Percolation/Bond/DomainIndependence.lean`. Mathlib: the real-power and logarithm facts are
mathlib's (`Real.rpow_logb`, `Real.logb_neg`, `Real.rpow_le_rpow_of_nonpos`, `Real.mul_rpow`,
`Real.div_rpow`, `Real.rpow_neg`, `Real.rpow_natCast_mul`, `Real.rpow_mul_natCast`), the limit
uses `tendsto_atTop_iInf` and `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`, and the integer
choices `Nat.find`. Every new declaration mentions arm events or crossings; no general lemma was
added.

## Sources

The proof is the wiki's XB1U proof, with the upper bound's dual circuits replaced by the
blocking event of WD31 Step 6 (Bollobás–Riordan, Theorem 8, as in `critical-probability.md`).
The plan locates the one-arm bounds in H. Duminil-Copin, *Introduction to Bernoulli
percolation*, lecture notes, 7 October 2018, Corollary 4.7, pp. 23–24; that text was not re-read
for this package. B. Bollobás and O. Riordan, *A short proof of the Harris–Kesten theorem*,
Bull. London Math. Soc. 38 (2006), 470–484, arXiv math/0410359v3.
