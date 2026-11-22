# Ratio contraction and limit laws from cylinder probabilities: advice for the wiki

Advice for the wiki agent on package F2 of the arms plan
(`PercLib/Probability/RatioContraction.lean`, `PercLib/Probability/CylinderLimit.lean`).
**These are general probability lemmas, outside the planar area.** Nothing in either file
mentions `ℤ²`, crossings, arms or even percolation. The index types, measures, matrices and
filters are arbitrary; the index type is countable for the limit law. Both files sit in
`Probability/`, not in `Models/Planar/`. Tom should know about them: they touch the shared
probability layer, and the limit-law theorem is a small piece of Kolmogorov-extension territory
that mathlib does not have yet.

Both files are proof-only: no definition, instance, notation or tag. `#print axioms` on the main
theorems shows only `propext`, `Classical.choice` and `Quot.sound`, and the gate's axiom audit
checks every constant.

They supply step 4 (contraction), step 5 (inclusion–exclusion) and the existence of the law `ν`
in step 6 of the arms plan's proof of Kesten's incipient infinite cluster (§4.2, wiki FM8D, by
the Basu–Sapozhnikov route). F3 and F4 (`Arms/IncipientCluster.lean`) will use them.

## Conventions

A *cylinder event* on a finite set `F : Finset ι` is an `A : Set (Set ι)` with
`∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A`, the arms plan's form. The *all-open event* of `S` is
`{ω | (S : Set ι) ⊆ ω}`. Real probabilities are `μ.real`, `ℝ≥0∞` ones `μ`.

In `RatioContraction.lean` the matrices are `M : ∀ k, ι k → ι (k + 1) → ℝ` with every `ι k` a
`Fintype`. The iterated products are not defined. They are written through recursion
hypotheses:
- forward: `hf : ∀ k b, f (k + 1) b = ∑ a, f k a * M k a b` (row vectors pushed forward);
- backward: `hw : ∀ k < s, ∀ a, w k a = ∑ b, M k a b * w (k + 1) b` (columns pulled back).

So `f s = f 0 M_0 ⋯ M_{s-1}` and `w 0 = M_0 ⋯ M_{s-1} w s`. The ratio is written inline as a
quotient of sums, `(∑ b, f s b * γ b) / (∑ b, g s b * γ b)`. The cross-ratio bound is
`hM : ∀ k a a' b b', M k a b * M k a' b' ≤ κ ^ 2 * (M k a b' * M k a' b)`.

## Statements as proved

### `RatioContraction.lean`

- **The ratio bound** (`abs_ratio_sub_ratio_le_of_crossRatio`): under `hM`, with `f`, `g` pushed
  forward from `0 ≤ f 0 ≤ g 0`, and two nonnegative weights `γ`, `γ'` on `ι s` with positive
  denominators,
  `|⟨f_s, γ⟩/⟨g_s, γ⟩ - ⟨f_s, γ'⟩/⟨g_s, γ'⟩| ≤ ((κ² - 1)/(κ² + 1))^s`.
  The form with the plan's factor is `abs_ratio_sub_ratio_le_one_sub_inv_sq_pow_of_crossRatio`
  (`1 ≤ κ`, bound `(1 - κ⁻¹ ^ 2) ^ s`), via `div_le_one_sub_inv_sq`.
- **Backward orientation** (`abs_ratio_sub_ratio_le_of_crossRatio_of_backward`), the plan's
  `⟨u', M_1 ⋯ M_{s-1} γ⟩ / ⟨u'', M_1 ⋯ M_{s-1} γ⟩`: for `0 ≤ u' ≤ u''` on `ι 0` and two
  backward recursions `w`, `w'` from nonnegative `w s`, `w' s`, with positive denominators,
  `|⟨u', w_0⟩/⟨u'', w_0⟩ - ⟨u', w'_0⟩/⟨u'', w'_0⟩| ≤ ((κ² - 1)/(κ² + 1))^s`.
  It rests on `sum_mul_eq_sum_mul_of_forall_lt` (`⟨h_0, w_0⟩ = ⟨h_k, w_k⟩` for `k ≤ s`).
- **General form** (`abs_div_sub_div_le_of_crossRatio`): start from any pairwise bound
  `f 0 a * g 0 a' - f 0 a' * g 0 a ≤ δ * (g 0 a * g 0 a')`. This is the division-free form of
  "`f_0/g_0` oscillates by at most `δ`", and holds with `δ = 1` when `0 ≤ f_0 ≤ g_0`. The ratio
  bound is then `δ ((κ² - 1)/(κ² + 1))^s`. No sign condition on `M`, `f` or `g`. Only the final
  weights `γ`, `γ'` must be nonnegative.
- Building blocks: `sum_mul_sum_sub_sum_mul_sum_eq` (Lagrange-type identity),
  `sum_mul_sum_sub_sum_mul_sum_le` (averaging against nonnegative weights),
  `sum_mul_sum_sub_sum_mul_sum_le_of_crossRatio` (one step, any `Finset`),
  `mul_sub_mul_le_pow_of_crossRatio` (`s` steps).

### `CylinderLimit.lean`

- **Inclusion–exclusion for cylinder events** (`indicator_eq_sum_subset_of_determined`, values
  in any commutative ring): for `A` determined by `F`,
  `1_A(ω) = ∑_{S ⊆ F} c_A(S) 1{S ⊆ ω}` with `c_A(S) = ∑_{T ⊆ S} (-1)^{|S| - |T|} 1_A(T)`.
  Finite-measure form `measureReal_eq_sum_subset_of_determined`:
  `μ.real A = ∑_{S ⊆ F} c_A(S) μ.real {S ⊆ ω}`. Limit form
  `tendsto_measureReal_of_determined`: if `(μ a).real {S ⊆ ω} → x S` along a filter for every
  `S ⊆ F`, then `(μ a).real A → ∑ c_A(S) x S`. The coefficients do not depend on the measure, so
  uniform estimates for the all-open events pass to `A` with the factor `∑_S |c_A(S)|`.
- **Cylinder events are measurable** (`measurableSet_of_determined_finset`), for any `ι`. PercLib
  had this only for bond configurations (`Bond.measurableSet_of_determined_finite`,
  `Models.measurableSet_of_determined`, both on `Set (Sym2 V)`).
- **Möbius inversion on the subsets of a finite set** (namespace `Finset`):
  `sum_powerset_filter_subset_neg_one_pow` (`∑_{T ⊆ S ⊆ U} (-1)^{|S| - |T|} = [T = U]`) and
  `moebius_inversion_powerset`.
- **A law from convergent cylinder probabilities** (`exists_measure_of_tendsto_cylinder`): for
  countable `ι`, probability laws `μ : α → Measure (Set ι)` along a filter `L` with `[L.NeBot]`,
  if every cylinder event's probability converges in `ℝ≥0∞`, then some probability law `ν` on
  `Set ι` satisfies `Tendsto (fun a => μ a A) L (𝓝 (ν A))` for every cylinder event `A`. This
  is the plan's statement with `ℕ`, `atTop` generalised to any nontrivial filter. The limit along
  `β ↓ log 2` (`𝓝[>] log2`) is covered too.
- **From the all-open events alone** (`exists_measure_of_tendsto_subset`): it suffices that
  `μ a {ω | ↑F ⊆ ω}` converges for every finite `F`.
- The law `ν` is unique: two probability laws with the same all-open probabilities are equal
  (`measure_ext_of_finset_subset`, `Superposition.lean`), and limits are unique.

## Deviations from the plan's §4.3 sketch

- The plan's `abs_ratio_sub_ratio_le_of_crossRatio` had `ℝ≥0` entries, `hκ : 1 ≤ κ`, an
  unspecified `hpos` and bound `(1 - κ⁻¹ ^ 2) ^ (s - 1)`. The proved forms are stronger:
  - real entries, with no sign condition on `M` (only `hM`);
  - no condition on `κ` except in the `1 - κ⁻²` corollary;
  - factor `(κ² - 1)/(κ² + 1) ≤ 1 - κ⁻²`;
  - exponent `s` for the `s` matrices `M_0, …, M_{s-1}`. The plan counted `M_1, …, M_{s-1}`,
    which is `s - 1` matrices, so its exponent `s - 1` is the same count.
  - `hpos` is just positivity of the two denominators; positive entries are not needed.
- The plan suggested Hopf's theorem or a backward-kernel Dobrushin argument. The Lean uses a
  shorter division-free argument (below); no kernels or total-variation distances appear.
- The limit law is built by compactness (the plan's "fallback", Prokhorov), not by
  `projectiveFamilyContent` + `IsCompactSystem` (the plan's recommendation). The fallback was
  shorter because mathlib already has `CompactSpace (ProbabilityMeasure E)` for compact `E` and
  the portmanteau theorem for clopen sets. Nothing was assumed: no `…Input`, no axiom.

## Proofs the Lean follows

**Contraction.** Write `D(a, a') = f(a) g(a') - f(a') g(a)` (antisymmetric). Suppose
`D ≤ δ g(a) g(a')` and fix columns `x = M(·, b)`, `y = M(·, b')`. Then
`f M(b) g M(b') - f M(b') g M(b) = S := ∑_{a, a'} x(a) y(a') D(a, a')`. The weights
`c(a, a') = κ² x(a) y(a') - x(a') y(a)` are `≥ 0` by the cross-ratio bound. Antisymmetry gives
`∑ c D = (κ² + 1) S`, and `∑ c g(a) g(a') = (κ² - 1) g M(b) g M(b')`. So
`(κ² + 1) S ≤ δ (κ² - 1) g M(b) g M(b')`, the same bound with `δ (κ² - 1)/(κ² + 1)`. After `s`
steps, average against `γ(b) γ'(b') ≥ 0` (Lagrange identity again) and divide by the two
denominators. For comparison, Birkhoff's sharp coefficient is `(κ - 1)/(κ + 1)`; any factor
`< 1` suffices for F3.

**Inclusion–exclusion.** Fix `ω` and put `U = F ∩ ω`. Then `1_A(ω) = 1_A(U)` and
`1{S ⊆ ω} = [S ⊆ U]` for `S ⊆ F`. Swapping the sums leaves `∑_{T ⊆ U} 1_A(T) ∑_{T ⊆ S ⊆ U}
(-1)^{|S| - |T|}`. The inner sum is `[T = U]`, by `S ↦ S \ T` and mathlib's
`Finset.sum_powerset_neg_one_pow_card`. Integrate for the measure form.

**Limit law.** Transport `μ_a` to `ι → Bool` by `ω ↦ (i ↦ decide (i ∈ ω))`. For countable `ι`
this space is compact, Hausdorff and Borel (`Pi.borelSpace`), so
`ProbabilityMeasure (ι → Bool)` is compact (`Prokhorov.lean`). Take a cluster point of the
transported laws along `L` (`exists_clusterPt_of_compactSpace`). A cylinder event pulls back to
a set that depends on the coordinates in `F` only, hence is clopen. Its probability is
continuous in the law (`ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto`; the
`HasOuterApproxClosed` instance comes from pseudo-metrizability). So the cluster point gives it
the limit value (uniqueness of limits in `ℝ≥0∞`). Push back by `x ↦ {i | x i = true}`.

## How F3 and F4 should call them

- F3, contraction: build the transfer matrices `M_β(U, R; U', R')` over the finite sets of
  admissible boundary data and prove the cross-ratio bound `hM` from B–S (2.7) (F1's
  `exists_law_setOf_localConn_comparable` gives `κ = c⁻¹`). Then call
  `abs_ratio_sub_ratio_le_of_crossRatio_of_backward`, or the forward form if the decomposition
  produces forward vectors. Different outer radii `n`, `n'` give different `γ`, `γ'`. If index
  sets with zero weight are awkward, keep them: zeros are allowed.
- F3, general cylinders: prove the Cauchy property for the all-open events `{S ⊆ ω}` (they are
  increasing). `measureReal_eq_sum_subset_of_determined` then gives it for every cylinder event,
  with constant `∑_S |c_A(S)| ≤ 3^{|F|}`.
- F4, the law: apply `exists_measure_of_tendsto_subset` (or `exists_measure_of_tendsto_cylinder`)
  to `μ r = (law (intensityProfile J log2))[|armEvent 0 (r + 1)]`, `L = atTop`, on
  `ι = Sym2 (LatticeSite 2)` (countable). `Config V` is `Set (Sym2 V)`, so no transport is
  needed. The conditional laws need `IsProbabilityMeasure`, from `ProbabilityTheory.cond_isProbabilityMeasure`
  and positivity of the arm probability.

If a wiki article ever states a Kolmogorov-type extension for `{0,1}`-valued fields, or
inclusion–exclusion for cylinder events, these are the declarations to tag. They belong to a
general probability article, not a planar one.

## Search

What was searched, in mathlib (pinned revision) and PercLib, before writing:

- **Kolmogorov extension / projective limits.**
  - `Mathlib/MeasureTheory/Constructions/Projective.lean` (`IsProjectiveMeasureFamily`,
    `IsProjectiveLimit`, uniqueness only).
  - `ProjectiveFamilyContent.lean` (the additive content on cylinders, no σ-additivity in
    general), `ClosedCompactCylinders.lean`, `Mathlib/Topology/Compactness/CompactSystem.lean`.
  - `Mathlib/Probability/ProductMeasure.lean`: `Measure.infinitePi`, products of measures only,
    whose σ-subadditivity goes through Ionescu–Tulcea, not compact systems.
  - `Mathlib/Probability/Kernel/IonescuTulcea/*` (ℕ-indexed kernel trajectories).
  - `Mathlib/Probability/Process/FiniteDimensionalLaws.lean` (equality of laws from
    finite-dimensional laws).
  - `Process/Kolmogorov.lean`: the Kolmogorov–Chentsov condition, not extension.
  - `Mathlib/Probability/BrownianMotion/GaussianProjectiveFamily.lean`, whose docstring wants
    Kolmogorov's extension theorem but does not prove it.

  **No general Kolmogorov extension theorem exists in the pinned mathlib.**
- **Compactness / weak convergence.** `Mathlib/MeasureTheory/Measure/Prokhorov.lean`
  (`CompactSpace (ProbabilityMeasure E)`, used), `Portmanteau.lean` (clopen form, used),
  `HasOuterApproxClosed.lean` (instance for pseudo-metrizable spaces, used), `LevyProkhorovMetric`.
- **Inclusion–exclusion / Möbius.**
  - `Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean` (unions of finsets).
  - `measureReal_biUnion_eq_sum_powerset` and `integral_biUnion_eq_sum_powerset`
    (`Integral/Bochner/Set.lean`, unions of sets).
  - `Combinatorics/Enumerative/IncidenceAlgebra.lean` (`moebius_inversion_top/bot` for locally
    finite orders, without the explicit Möbius function of `Finset α`).
  - `Finset.sum_powerset_neg_one_pow_card` (`Data/Nat/Choose/Sum.lean`, used).

  None gives the cylinder form, so the Boolean Möbius inversion was written (two short lemmas in
  namespace `Finset`).
- **Contraction.** No Hopf, Birkhoff, Hilbert projective metric or Dobrushin coefficient in
  mathlib or PercLib (searched those words).
- **PercLib.** `Characterization.lean` / `Superposition.lean` (all-open events determine a law:
  `measure_ext_of_finset_subset`; their measurability `measurableSet_setOf_finset_coe_subset`,
  used). `Mixing.lean` (`measurableSet_finset_cylinder`, cylinder events as preimages; the proof
  pattern was followed). `Bond.measurableSet_of_determined_finite` and
  `Models.measurableSet_of_determined` (bond-configuration special cases of the new
  measurability lemma; they could be derived from it). `FiniteContinuity.lean` (continuity in
  the profile, a different statement). Nothing on ratio contraction or cylinder
  inclusion–exclusion.

## Sources

J. Basu and A. Sapozhnikov, *Kesten's incipient infinite cluster and quasi-multiplicativity of
crossing probabilities*, Electron. Commun. Probab. 22 (2017), paper 26, arXiv:1603.06884v2, §2:
the cross-ratio bound (2.7) and the contraction step after it, done there with Hopf's theorem.
The paper was not re-read for this package. The plan's summary (§4.2 step 4) fixes what is
needed, and the Lean proof is self-contained.
