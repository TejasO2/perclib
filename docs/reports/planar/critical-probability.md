# Harris's theorem and p_c(ℤ²) = 1/2: advice for the wiki

Advice for the wiki agent on package P5 of the RSW plan
(`PercLib/Models/Planar/CriticalProbability.lean`). This is Step 6 of the wiki's proof of WD31
(`critical-exponents`, §"The square-lattice crossing input"), Theorem 8 of Bollobás–Riordan,
and, with Kesten's bound (`kesten-bound.md`, which is Step 7), the threshold conjunct
"`p_c = 1/2`" of WD31. Everything is proved with only `propext`, `Classical.choice` and
`Quot.sound`; no tags were added.

## Statements as proved

Conventions as in `duality.md`, `crossing-symmetry.md` and `rsw.md`: boxes are `Set.Icc lo hi`
on `Fin 2 → ℤ`, `crossing 0` is left-right and `crossing 1` bottom-top. "At `1/2`" means the
hypothesis `∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2`: every edge of `ℤ²` is open with
probability `1/2`, and the profile off the edges is arbitrary. At `1/2` the events read only
`ω ∩ (zdGraph 2).edgeSet`, so clusters are written `cluster (ω ∩ (zdGraph 2).edgeSet) x`. In
the intensity form the kernel is `J = (zdGraph 2).edgeSet.indicator 1`, an edge is open with
probability `1 - e^{-β}`, and edge probability `1/2` is `β = log 2` (as in `kesten-bound.md`).
All probabilities are in `ℝ≥0∞`. Write `‖v‖∞ = max(|v₀|, |v₁|)`.

- **Blocking** (`notMem_localConn_of_notMem_crossing`): for `s ∈ ℕ` and every configuration `ω`,
  if none of the four strips `[-3s, 3s] × [s, 3s]` (top), `[-3s, 3s] × [-3s, -s]` (bottom),
  `[s, 3s] × [-3s, 3s]` (right), `[-3s, -s] × [-3s, 3s]` (left) has an open crossing in its
  short direction, then no open path, inside any vertex set `S`, joins a vertex `a` with
  `‖a‖∞ ≤ s` to a vertex `v` with `‖v‖∞ ≥ 3s`. Purely deterministic.
- **Blocking, cluster form** (`cluster_subset_Icc_of_notMem_crossing`): under the same four
  hypotheses, the open cluster of every vertex `a` with `‖a‖∞ ≤ s` lies in `[1 - 3s, 3s - 1]²`.
- **Blocking probability** (`exists_pos_le_law_blocking`): there is `c > 0` such that for every
  `q` at `1/2` and every integer `s ≥ 1`, the intersection of the four strip events "no open
  crossing in the short direction" has probability at least `c`. This is the wiki's
  `P_{1/2}(E_s) ≥ c_*` for all `s ≥ 1`, with `E_s` written as in the next section.
- **Harris's theorem, `θ(1/2) = 0`** (`law_cluster_infinite_eq_zero_of_half`): for every `q` at
  `1/2` and every vertex `x`, `P((cluster of x).Infinite) = 0`. The origin case is
  `law_cluster_infinite_zero_eq_zero_of_half`.
- **Global form** (`law_exists_cluster_infinite_eq_zero_of_half`): at `1/2`, almost surely no
  cluster is infinite. This is the "almost surely no infinite open cluster at `p_c`" that XB1U
  repeats.
- **Intensity form** (`law_cluster_infinite_intensityProfile_eq_zero`,
  `law_exists_cluster_infinite_intensityProfile_eq_zero`): for every `β ≤ log 2`, at intensity
  `β` the cluster of every vertex is almost surely finite, and almost surely no cluster is
  infinite. This is the wiki's "`θ(p) = 0` for every `p ≤ 1/2`".
- **`p_c(ℤ²) = 1/2`, the threshold conjunct of WD31**
  (`rootCriticalIntensity_indicator_edgeSet_eq_log_two`, for every vertex `x`;
  `globalCriticalIntensity_indicator_edgeSet_eq_log_two`): the root and the global critical
  intensities of `J` both equal `ENNReal.ofReal (log 2)`. With `p = 1 - e^{-β}`, this is
  `p_c = 1/2`. A tag file for WD31 should say so in its docstring (U5MC: intensity
  parametrisations need their own convention); the two conjuncts of WD31 are then
  `rootCriticalIntensity_indicator_edgeSet_eq_log_two` and `exists_pos_le_law_crossing_zero`
  (`rsw.md`).
- Two auxiliary lemmas:
  - `law_compl_crossing_zero_eq`: at `1/2`, a box `[lo, hi]` has no open left-right crossing with
    the probability that `[0, hi₁ - lo₁ + 1] × [0, hi₀ - lo₀ - 1]` has an open left-right
    crossing. It is the horizontal companion of `law_compl_crossing_one_eq`
    (`crossing-symmetry.md`).
  - `mem_crossing_iff_of_inter_eq`: a crossing of a box is determined by the open pairs with
    both endpoints in any region containing the box.
- Walk helpers, no wiki counterpart needed: `exists_mem_localConn_of_walk` (an open walk from
  level `≤ s` to level `≥ t` of a function that changes by at most one per step contains a
  connection between the two levels that stays between them) and `max_abs_le_add_one_of_adj`
  (one open edge changes `‖·‖∞` by at most one).

## Proof the Lean follows

Step 6 as written, with these differences.

1. *The strip events.* The wiki's `E_s` asks for dual-open crossings of `D_s` and its three
   quarter-turns in the long direction. The Lean states the same events in primal form: by
   vertical duality (Step 2), `D_s` has a dual-open left-right crossing exactly when the primal
   strip `[-3s, 3s] × [s, 3s]` has no open bottom-top crossing, since `D_s` is its box `R^v`.
   So `E_s` is the intersection of four complements of short-direction crossings. No duality is
   needed in the blocking argument itself.
2. *Blocking without rotating.* The wiki rotates the configuration so that the first vertex `v`
   with `‖v‖∞ ≥ 3s` has `v_y = 3s`. The Lean splits instead into four cases by which coordinate
   of `v` equals `±3s`. It takes the first passage to sup norm `3s` along the path, and then a
   segment between the levels `s` and `3s` of that coordinate (the discrete intermediate value
   theorem `SimpleGraph.Walk.exists_walk_mem_Icc` of `crossing-symmetry.md`). The segment lies in
   one strip and crosses it in its short direction, which contradicts the hypothesis directly.
   The wiki then applies Step 1 to this segment and the dual crossing of `D_s`; with the primal
   form of item 1 that step is not needed.
3. *Lower bound for one strip.* Each complement has the probability of an open left-right
   crossing of `[0, 6s + 1] × [0, 2s - 1]` (the translate by `(1/2, 1/2)` of the wiki, done by
   `law_compl_crossing_one_eq` for the top and bottom strips and its horizontal companion for the
   left and right strips). The Lean bounds it for **every** `s ≥ 1` at once: RSW in any position
   (`exists_pos_le_law_crossing 7`, `rsw.md`) bounds the crossing of `[0, 7(2s - 1)] × [0, 2s - 1]`,
   which contains a crossing of `[0, 6s + 1] × [0, 2s - 1]` since `6s + 1 ≤ 7(2s - 1)` for
   `s ≥ 1`. So there is no separate case `s = 1` with the bound `2^(-7)`, and no `n' = s - 1`.
   The wiki's argument is still correct; the Lean's constant is `c^4`, with `c` the constant of
   `exists_pos_le_law_crossing 7`, instead of `min(2^(-7), c₇)^4`.
4. *Harris* is the two-event inequality for decreasing events
   (`prodBernoulli_harris_of_isLowerSet`, from X5SS applied to complements) used three times.
   The wiki says "increasing in the closed indicators", which is the same thing.
5. *Independence.* The scales are `s_j = 4^j`, as in the wiki. The blocking event at scale `s`
   is determined by the pairs with both endpoints in the annulus `s ≤ ‖·‖∞ ≤ 3s`
   (`mem_crossing_iff_of_inter_eq`), and these annuli are disjoint for `s = 4^j` since
   `3 · 4^j < 4^{j+1}`. The wiki phrases the disjointness by midpoints of crossed edges; the Lean
   uses the vertex annuli. Independence is `law_biInter_of_determined_internalPairs`
   (`Percolation/Bond/DomainIndependence.lean`).
6. *Conclusion.* An infinite cluster of the origin is not contained in the finite box
   `[1 - 3s, 3s - 1]²`, so it defeats every blocking event. Hence
   `θ(1/2) ≤ ∏_{j<J} (1 - P(E_{4^j})) ≤ (1 - c^4)^J` for every `J`, and `θ(1/2) = 0`. Translation
   invariance at `1/2` gives every vertex, and a countable union the global form.
7. *Monotonicity in `p`.* The wiki uses the standard coupling. The Lean uses
   `law_intensityProfile_mono` (increasing events are monotone in the intensity), and that at
   intensity `log 2` almost surely only edges of `ℤ²` are open (`ae_config_subset_host`), so the
   cluster at intensity `log 2` is the cluster of `ω ∩ (zdGraph 2).edgeSet` at `1/2`.
8. *`p_c = 1/2`.* `log 2 ≤ β_c` because every intensity with positive percolation probability
   exceeds `log 2` by item 7; `β_c ≤ log 2` is Kesten's bound (Step 7, `kesten-bound.md`). The
   global threshold equals the root one by transitivity
   (`rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive`).

## Sources

B. Bollobás and O. Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math.
Soc. 38 (2006), 470–484, arXiv math/0410359v3, Theorem 8, p. 9. They use annuli between
`4^k` and `3 · 4^k` and four crossings of rectangles forming a circuit; the Lean, like the
wiki, uses the four strips directly and never builds a circuit. For the upper bound
`p_c ≤ 1/2` they use the Friedgut–Kalai sharp-threshold theorem (their Theorem 10); the
library, like the wiki, uses sharpness (`kesten-bound.md`). H. Kesten, *The critical
probability of bond percolation on the square lattice equals 1/2*, Comm. Math. Phys. 74 (1980),
41–59.
