# Kesten's incipient infinite cluster, part 2 (the limits, the law and uniqueness): advice for the wiki

Advice for the wiki agent on package F4 of the arms plan
(`PercLib/Models/Planar/Arms/IncipientCluster.lean`, after F3's part). It finishes wiki FM8D
(`size-biased-laws`, "The planar lattice construction"). F3 proved the uniform Cauchy property of
`P(A | z ↔ ∂B_n(z))` (see `incipient-cluster-a.md`). F4 adds the two limits, the law `ν`, and
uniqueness of the infinite cluster under `ν`. It ends with the arms plan's §4.1 statement
`exists_incipientInfiniteCluster`, in FM8D's required form.

The theorem is **not tagged**; tagging FM8D is package TgF (`Models/Tags/Planar.lean`, interface).
The package is proof-only: 20 theorems, no definition, instance, notation or tag, no `sorry` and no
`…Input`. Everything uses only `propext`, `Classical.choice` and `Quot.sound` (gate axiom audit).
Nothing in FM8D is "proved modulo" a cited result.

## Conventions

As in `incipient-cluster-a.md`. `P_β = law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β)`:
each edge of `ℤ²` is open with probability `p = 1 - e^{-β}` and every other pair is closed;
`β = log 2` is `p_c = 1/2` (T3, `rootCriticalIntensity_indicator_edgeSet_eq_log_two`). Conditional
probabilities use mathlib's notation `μ[A | B] = ProbabilityTheory.cond μ B A`, available after
`open scoped ProbabilityTheory`. A *cylinder event* is an `A` with `∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A` for a
finite set `F` of pairs. `K_x` is the open cluster `cluster (ω ∩ (zdGraph 2).edgeSet) x`. A profile
*at least `1/2`* means `∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e`, with nothing assumed off the
edges (D-2).

## The final statement

```lean
theorem exists_incipientInfiniteCluster :
    ∃ ν : Measure (Config (LatticeSite 2)), IsProbabilityMeasure ν ∧
      (∀ (F : Finset (Sym2 (LatticeSite 2))) (A : Set (Config (LatticeSite 2))),
        (∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) →
        Tendsto (fun r : ℕ => (law (intensityProfile ((zdGraph 2).edgeSet.indicator 1)
            ⟨Real.log 2, (Real.log_pos one_lt_two).le⟩))[|armEvent 0 (r + 1)] A)
          atTop (𝓝 (ν A)) ∧
        Tendsto (fun β : ℝ≥0 => (law (intensityProfile ((zdGraph 2).edgeSet.indicator 1)
            β))[|{ω | (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite}] A)
          (𝓝[>] ⟨Real.log 2, (Real.log_pos one_lt_two).le⟩) (𝓝 (ν A))) ∧
      ν {ω | (cluster (ω ∩ (zdGraph 2).edgeSet) 0).Infinite ∧
        ∀ x, (cluster (ω ∩ (zdGraph 2).edgeSet) x).Infinite →
          cluster (ω ∩ (zdGraph 2).edgeSet) x = cluster (ω ∩ (zdGraph 2).edgeSet) 0} = 1
```

This is the plan's §4.1 text with its placeholders filled: `J = (zdGraph 2).edgeSet.indicator 1`,
`L = (zdGraph 2).edgeSet`, and `log2 = ⟨Real.log 2, (Real.log_pos one_lt_two).le⟩`, written inline
as the plan says. The binder table is the plan's and is unchanged:

| binder | class | note |
|---|---|---|
| `ν`, `IsProbabilityMeasure ν` | SOURCE | "define a probability law" |
| `F`, `A`, `∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A` | SOURCE | "every cylinder event"; measurability is not assumed (it follows, `measurableSet_of_determined_finset`) |
| `law (intensityProfile J ⟨log 2, _⟩)` | SOURCE + TYPING | `P_{p_c}`, `p_c = 1/2` (T3); `0` off the edges is the bond-interface convention |
| `armEvent 0 (r + 1)` | SOURCE | `{0 ↔ Q_r^c}`, `Q_r = [-r, r]²`, by `mem_armEvent_iff_exists_notMem_conn` |
| `r → ∞` in `ℕ` | SOURCE | |
| `β ↓ log 2` (`𝓝[>]`) | SOURCE | `p ↓ p_c`; `p = 1 - e^{-β}` is an increasing homeomorphism, so this is a reparametrisation |
| `ProbabilityTheory.cond` | TYPING | `P(A ∩ B)/P(B)` |
| the uniqueness set | SOURCE | "exactly one infinite open cluster, and it contains 0" |

No EXCESS. Notes for the binder review:
- `𝓝[>] ⟨Real.log 2, _⟩` is a filter on `ℝ≥0`. Values of `β ≤ log 2` play no role; there
  `P_β(|K_0| = ∞) = 0` and mathlib's `cond` is the zero measure.
- The point `⟨Real.log 2, _⟩` elaborates with type `{r // 0 ≤ r}`, which is `ℝ≥0` up to unfolding.
  In proofs, `rw` with a lemma about `𝓝[s] a` can fail on it ("not type-correct under the
  `implicit` transparency"); applying the lemma with `refine` (`.1`, `.2`) works. KestenBound uses
  `(Real.log 2).toNNReal` for the same point; the two are equal but not syntactically. If the tag
  file prefers `(Real.log 2).toNNReal`, the change of point is one `Real.toNNReal_of_nonneg` (or
  `Subtype.ext`) step.
- The `p` form (`fun e => if e ∈ L then p else 0`, `p ↓ 1/2`) is a change of variables and is not
  proved here.

## Statements as proved

**General lemmas** (no percolation):
- `Probability.mem_inter_iff_inter_union_mem_of_determined`: if `A` is determined by `F` and `B`
  by `G`, then `A ∩ B` is determined by `F ∪ G`.
- `Probability.continuous_prodBernoulli_of_determined`: the probability of a cylinder event is
  continuous in the profile, for the product topology. It restates `continuous_prodBernoulli_cylinder`
  (`Probability/FiniteContinuity.lean`) in the `ω ∩ F` form.
- `Bond.mem_iff_inter_sym2_mem_of_determined`: an event of the pairs with both ends in a finite
  set `T` is determined by the finite set `T.sym2`.

**Arm events and the infinite cluster** (any dimension `d` unless stated):
- `mem_armEvent_iff_inter_sym2_mem`: `armEvent z n` is determined by
  `(Finset.Icc (z - n) (z + n)).sym2`.
- **`setOf_cluster_infinite_eq_iInter_armEvent`**:
  `{ω | (cluster (ω ∩ (zdGraph d).edgeSet) x).Infinite} = ⋂ r : ℕ, armEvent x (r + 1)`. An infinite
  cluster leaves every finite box. A finite cluster is bounded for the sup metric, so it lies in
  some box (`closedBall_eq_Icc`). Corollary: `measurableSet_setOf_cluster_inter_edgeSet_infinite`.
- **`tendsto_cond_armEvent_cond_setOf_cluster_infinite`**: for **every** profile with
  `P(|K_z| = ∞) ≠ 0` and every measurable `A`, `P(A | z ↔ ∂B_n(z)) → P(A | |K_z| = ∞)`. This is
  continuity from above along the decreasing arm events.

**Intensities** (`ℤ²`):
- `half_le_intensityProfile_indicator_edgeSet`: for `Real.log 2 ≤ β`, every edge is open with
  probability at least `1/2`. Proof: monotonicity in `β` and the value `1/2` at `log 2`.
- `law_setOf_cluster_inter_edgeSet_infinite_pos`: for `Real.log 2 < β`,
  `0 < P_β(|K_x| = ∞)` with the cluster read in `ω ∩ (zdGraph 2).edgeSet`. KestenBound's version
  reads it in `ω`; the two events are almost surely equal (`ae_config_subset_host`).
- `continuousOn_toReal_cond_armEvent`: for a continuous family of profiles `q : X → …` that are
  at least `1/2` on a set `s`, the map `x ↦ P_{q x}(A | z ↔ ∂B_n(z))` is continuous on `s` for every
  cylinder `A`.

**The first limit and the law:**
- **`exists_tendsto_cond_armEvent`**: for every profile at least `1/2`, every centre `z` and every
  cylinder `A`, `P(A | z ↔ ∂B_n(z))` converges in `ℝ≥0∞`. The proof turns F3's Cauchy property into
  convergence in `ℝ` by completeness.
- **`exists_abs_toReal_cond_armEvent_sub_toReal_le`** (the first limit is uniform). For every `z`,
  finite `F` and `ε > 0` there is `n₀` with the following property. For every profile at least
  `1/2`, every `A` determined by `F`, every limit `l` of `P(A | z ↔ ∂B_n(z))` and every
  `n ≥ n₀`, `|P(A | z ↔ ∂B_n(z)) - l| ≤ ε`.
- **`exists_measure_tendsto_cond_armEvent`**: for every profile at least `1/2` and every centre
  `z`, there is a probability law `ν` with `P(A | z ↔ ∂B_n(z)) → ν(A)` for every cylinder `A`. It
  follows from F2's `exists_measure_of_tendsto_cylinder` with `μ n = (law q)[|armEvent z n]`.

**Continuity and the second limit:**
- **`continuousOn_toReal_of_tendsto_cond_armEvent`**: for a continuous family of profiles that are
  at least `1/2` on `s`, any family `l x` of limits of `P_{q x}(A | z ↔ ∂B_n(z))` (for `x ∈ s`) is
  continuous on `s`. It is a uniform limit of continuous functions (mathlib's
  `TendstoUniformlyOn.continuousOn`). With `continuous_intensityProfile_pi` this gives continuity
  of `β ↦ ν_β(A)` on `β ≥ log 2`.
- **`tendsto_cond_setOf_cluster_infinite_nhdsGT`**: for every centre `z` and cylinder `A`, if
  `P_{log 2}(A | z ↔ ∂B_n(z)) → l`, then `P_β(A | |K_z| = ∞) → l` as `β ↓ log 2`.

**Uniqueness under `ν`:**
- **`cluster_eq_of_mem_fourStrip`**: on `fourStrip z n`, two vertices of `B_{2n}(z)` with infinite
  clusters have the same cluster.
- `measure_armEvent_eq_one_of_tendsto`: if `ν` is a limit of `P(· | z ↔ ∂B_n(z))` on cylinder
  events (profile at least `1/2`), then `ν(armEvent z r) = 1` for every `r`.
- **`ae_exists_mem_fourStrip_of_tendsto`**: under such a `ν`, almost surely, for every `K` there is
  `j ≥ K` with `fourStrip z (3 ^ j)`.
- **`measure_setOf_cluster_infinite_forall_eq_eq_one`**: under such a `ν` (a probability measure),
  the uniqueness set has `ν`-probability one. This holds for every profile at least `1/2` and every
  centre.

## Proof the Lean follows

1. *First limit.* F3's `exists_abs_toReal_cond_armEvent_sub_le` gives Cauchy sequences in `ℝ`
   (`Metric.cauchySeq_iff'`), and `cauchySeq_tendsto_of_complete` gives the limit. Every `cond`
   value is at most `1`, so it is finite and the limit transfers to `ℝ≥0∞`. Letting `m → ∞` in
   F3's bound `|f_n - f_m| ≤ ε` gives the uniform rate, with `n₀` depending only on `F` and `ε`.
2. *The law.* The conditional laws are probability measures (`law_armEvent_pos`,
   `cond_isProbabilityMeasure`). F2's Prokhorov-based theorem turns the convergent cylinder
   probabilities into a law `ν`.
3. *Continuity.* Both `P_q(A ∩ armEvent z n)` and `P_q(armEvent z n)` are cylinder probabilities,
   since `A ∩ armEvent z n` is determined by `F ∪ (B_n)^{sym2}`. So they are continuous in the
   profile. The denominator is positive for profiles at least `1/2`. The uniform first limit then
   makes the limit continuous.
4. *Second limit.* For `β > log 2`, `P_β(|K_z| = ∞) > 0` (KestenBound, via
   `ae_config_subset_host`). With `{|K_z| = ∞} = ⋂_r armEvent z (r + 1)`, continuity from above
   gives `lim_n P_β(A | z ↔ ∂B_n) = P_β(A | |K_z| = ∞)`. Take the family of limits equal to `l`
   at `log 2` and to `P_β(A | |K_z| = ∞)` above it. It is continuous on `[log 2, ∞)`; restricting
   continuity at `log 2` to `𝓝[>] log 2` gives the limit.
5. *Uniqueness.*
   - Each arm event is a cylinder event, and `P(armEvent z r | armEvent z n) = 1` for `n ≥ r`.
     So `ν(armEvent z r) = 1`, and `ν(|K_z| = ∞) = 1` by step 4's set identity.
   - Take the scales `3^j` for `K ≤ j < K + M` (so `2 · 3^j < 3^{j'}`). The event "no four-strip
     event at these scales" is a cylinder event, determined by the box of radius `4 · 3^{K+M}`.
     F1's `exists_law_inter_biInter_compl_fourStrip_le` with `E = armEvent z n` bounds its
     conditional probability by `(1 - c₀)^M`. This passes to `ν`, and `M → ∞` gives `ν`-a.s. a
     four-strip event at some scale `3^j`, `j ≥ K`.
   - Given `x`, take `K = |x₀ - z₀| + |x₁ - z₁|`. Then `x, z ∈ B_{2·3^j}(z)`, because `j < 3^j`.
     An infinite cluster has a point outside `B_{4·3^j - 1}(z)`. F1's annulus gluing
     (`inter_edgeSet_mem_localConn_union_of_mem_fourStrip`, with `W = W' = univ`) joins `x` to `z`.

## Statement choices compared with the plan

- **Generality.** Every lemma before the final theorem holds for every profile at least `1/2` on
  the edges and every centre `z`. FM8D needs `β = log 2`, `z = 0`. In particular, for every
  `β ≥ log 2` the limit `ν_β` exists and has a unique infinite cluster, and for `β > log 2` it
  agrees with `P_β(· | |K_z| = ∞)` on cylinder events. The identity of the infinite cluster with
  the arm events, and the conditioning limit, hold in every dimension and for every profile.
- **Continuity** (plan §4.2 step 6) is proved for the limit along any continuous family of
  profiles, not only `β ↦ intensityProfile J β`.
- **The scales** for uniqueness are `3^j` (separated, since `2 · 3^j < 3^{j+1}`), a concrete
  choice of the plan's `n_K, …, n_{K+M}`.
- **Indices.** Lemmas use `armEvent z n` for all `n`; the final statement's `armEvent 0 (r + 1)`
  is `tendsto_add_atTop_iff_nat 1`.

## Notes for the tag file (TgF)

- Tag `exists_incipientInfiniteCluster` as FM8D after the binder review above. `check_d35.py`
  check (i) wants the proving theorem to carry the tag as well (as in the J98J and W498 repairs on
  `main`), so TgF adds `@[tag "FM8D"]` in the area file together with the `Tags/` restatement.
- FM8D's sketch also says "`ν` lives on subsets of `L`". That is not stated. It is a short
  corollary if wanted: for `e ∉ L`, `P_{log 2}(e ∈ ω) = 0` (`ae_config_subset_host`), so `ν(e ∈ ω) = 0`.
- Useful companions, already proved: `exists_measure_tendsto_cond_armEvent` (the IIC law at every
  `β ≥ log 2`), `tendsto_cond_armEvent_cond_setOf_cluster_infinite`, and
  `setOf_cluster_infinite_eq_iInter_armEvent` (this links FM8D's `|K_0| = ∞` with the one-arm event
  of XB1U).

## Search

- **Mathlib.** No Kolmogorov extension (F2's search stands). Used: `Metric.cauchySeq_iff'`,
  `cauchySeq_tendsto_of_complete`, `ENNReal.tendsto_toReal_iff`, `ENNReal.tendsto_ofReal`,
  `tendsto_measure_iInter_atTop`, `ProbabilityTheory.cond_apply`, `cond_isProbabilityMeasure`,
  `IsZeroOrProbabilityMeasure` (`prob_le_one` for every `cond`), `ENNReal.Tendsto.mul`,
  `tendsto_inv_iff`, `Metric.tendstoUniformlyOn_iff`, `TendstoUniformlyOn.continuousOn`,
  `ContinuousOn.div`, `ENNReal.continuousOn_toReal`, `Set.Infinite.exists_notMem_finite`,
  `Set.Finite.isBounded`, `Metric.isBounded_iff_subset_closedBall`, `Finset.mem_sym2_iff`,
  `ae_all_iff`, `ae_iff`, `ae_eq_univ`, `ae_mem_iff_measure_eq`,
  `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`, `ENNReal.sub_lt_self`, `Nat.lt_pow_self`.
- **PercLib, reused.** `continuous_prodBernoulli_cylinder` (`Probability/FiniteContinuity.lean`),
  `continuous_intensityProfile_pi` (`Bond/FiniteSetCriterion.lean`), `intensityProfile_mono`,
  `intensityProfile_indicator_edgeSet_log_two` and
  `law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt` (KestenBound), `ae_config_subset_host`
  (`Bond/Host.lean`), `cluster_eq_of_mem_conn` (`Bond/RootIndependence.lean`), `localConn_univ`,
  `localConn_subset_conn`, `closedBall_eq_Icc`, `mem_armEvent_iff_exists_notMem_conn`,
  `mem_armEvent_iff_of_inter_eq`, `armEvent_anti`, `mem_fourStrip_iff_of_inter_eq`. Also F1's
  `exists_law_inter_biInter_compl_fourStrip_le` and
  `inter_edgeSet_mem_localConn_union_of_mem_fourStrip`; F2's `exists_measure_of_tendsto_cylinder`
  and `measurableSet_of_determined_finset`; F3's `exists_abs_toReal_cond_armEvent_sub_le`,
  `law_armEvent_pos` and `toReal_cond_armEvent`.
- **Not found, hence written.** There was no intersection rule for cylinder events in the
  `ω ∩ F` form. `DeterminedIndependence.lean` has `determined_biInter` for sets of coordinates.
  There was no "events of the pairs inside a finite set are cylinder events" lemma, no identity
  between the infinite cluster and the arm events, and no continuity of cylinder probabilities in
  the `ω ∩ F` form.

## Sources

H. Kesten, *The incipient infinite cluster in two-dimensional percolation*, Probab. Theory Related
Fields 73 (1986), Theorem 3: the statement. D. Basu and A. Sapozhnikov, *Kesten's incipient
infinite cluster and quasi-multiplicativity of crossing probabilities*, Electron. Commun. Probab.
22 (2017), arXiv:1603.06884v2, Section 2: the route, as in part 1. The limit and uniqueness
arguments follow the arms plan §4.2 step 6. Kesten's paper was not consulted for this package.
