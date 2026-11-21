# Interface changes

Changes to shared definitions and public names that can break other branches are announced
here before they merge (decision D-37, item h), with the migration recipe. Renames keep a
deprecated alias for one release where that is possible.

## Announced, not yet merged

None.

## Merged

### New definitions, round 14 batch (additive; no existing name changed)

- `p-a-GPDF` (audited APPROVE, `audit-p-a-GPDF`): `ballExitRate`, `boundaryThreshold`, `maxBoundaryThreshold`,
  `boundaryScaleIndex`, `boundaryLength` in new `PercLib/Models/HierarchicalBoundaryScales/Defs.lean`.
- `p-b-CUE4` (audited APPROVE, `audit-p-b-CUE4`): `mobiusCoeff`, `HasNonnegMobiusCoeffs` in new
  `PercLib/Combinatorics/BooleanCoefficients/Defs.lean`; `HasMassTransport` in new
  `PercLib/Probability/MassTransport/Defs.lean`; `poissonTail` in new `PercLib/Probability/PoissonTail/Defs.lean`.
- Announced 21 November 2026 (round 14), merged in the batch on top of `e0ae3ec`.

### Size-biased law (`sizeBiased`)

- **What:** a new definition `PercLib.Probability.sizeBiased` in the new file
  `PercLib/Probability/SizeBias/Defs.lean`: the size-biased law of a nonnegative random
  variable as a `withDensity` measure, with its API; `PercLib/Probability/SizeBias.lean` now
  uses it. Tags 6L9Z, IDIL (`work/p-b-6L9Z`, audit `audit-p-b-6L9Z` APPROVE).
- **Breaks:** nothing; existing statements keep their names (additive change).
- **Merged:** 21 November 2026, round-12 batch gated at `4312804` (merge of `work/p-b-6L9Z-doc`).

### Long-range norm structure (`ModelNorm`)

- **What:** a new structure `ModelNorm E` extending `Seminorm ℝ E` with definiteness
  (`PercLib/Analysis/ModelNorm/Defs.lean`). The long-range and dispersion lemmas that carried
  the hypothesis `∀ v, N v = 0 → v = 0` take `N : ModelNorm (Fin d → ℝ)` instead and lose
  that hypothesis; the kernel and Lévy definitions keep taking a `Seminorm` and accept a
  `ModelNorm` through the coercion. Four tagged statements change spelling (PVA8, MQNP,
  LF50, 6YYS).
- **Deleted when unused:** `normSeminorm_eq_zero`, `euclidean_seminorm_eq_zero`
  (replaced by `ModelNorm.ofNorm` and the Euclidean `ModelNorm.comp`).
- **Recipe:** replace a seminorm `N` together with its definiteness proof by a `ModelNorm`
  (`ModelNorm.ofNorm E` for the norm of a normed space); drop the definiteness argument at
  call sites.
- **Renames** (merged with `work/mig-model-norm` at `d1295a4`; no deprecated aliases were
  kept, since no outside branch used the old names):

  | Old name | New name |
  |---|---|
  | `seminorm_intCast_pos` | `ModelNorm.intCast_comp_pos` |
  | `norm_sub_pos` | `ModelNorm.intCast_comp_sub_pos` |
  | `LongRange.exists_pos_mul_norm_le` | `ModelNorm.exists_pos_mul_norm_le` (deleted, use this) |
  | `normSeminorm_eq_zero`, `euclidean_seminorm_eq_zero` | `ModelNorm.ofNorm`, Euclidean `ModelNorm.comp` |

### Connection probability under a general measure (`connProb`)

- **What:** a new definition in `PercLib/Percolation/Bond/Basic.lean`,
  `connProb (μ : Measure (Config V)) (x y : V) : ℝ≥0∞ := μ (conn x y)`, with
  `connProb_def` and the simp lemma `connProb_law : connProb (law q) x y = tau q x y`.
  Results in `Bond/{Transport,ConnectionKernel,TriangleDecay,ClusterCount,ClusterMoments}.lean`
  and `Bond/Tightness/Hyperscaling.lean` that never used independence are restated for an
  arbitrary measure `μ` on configurations (`law q` becomes `μ`, `tau q` becomes `connProb μ`,
  with `[IsProbabilityMeasure μ]` where needed). One tagged statement changes spelling (Q0D1).
- **Renames** (from the diff of the merged branch against its base `cfef666`; no deprecated
  aliases were kept):

  | Old name | New name |
  |---|---|
  | `tau_ne_top` | `connProb_ne_top` |
  | `tendsto_tau_cofinite` | `tendsto_connProb_cofinite` |
  | `tendsto_tau_sq_cofinite` | `tendsto_connProb_sq_cofinite` |
  | `posSemidef_tau` | `posSemidef_connProb` |
  | `sum_tau_cauchySchwarz` | `sum_connProb_cauchySchwarz` |
  | `sum_finset_mul_tau_nonneg` | `sum_finset_mul_connProb_nonneg` |
  | `sum_mul_tau_nonneg` | `sum_mul_connProb_nonneg` |
  | `sum_mul_tau_eq_integral` | `sum_mul_connProb_eq_integral` |
  | `sum_mul_tau_eq_integral_indicator` | `sum_mul_connProb_eq_integral_indicator` |
  | `triangle_eq_tsum_tau_mul` | `triangle_eq_tsum_connProb_mul` |
  | `tsum_tau_sq_le_triangle` | `tsum_connProb_sq_le_triangle` |

  Deleted with no replacement of the same name: `integrable_of_fintype`
  (`Bond/ClusterCount.lean`). New API: `connProb_comm`, `connProb_le_one`, `connProb_mono`,
  `connProb_self`, `connProb_zero`, `connProb_map_image_sym2Map`.
- **Merged:** 21 November 2026, integration branch merge `605bc7d` (gated in batch `df5d0fd`).
- **Recipe:** to use a generalised lemma at the independent law, apply it with `μ := law q`
  and rewrite with `connProb_law`.

Earlier respellings (the `localConn`/`localCluster`/`boundaryFlux`/`IsCut` fold, the header
and linter migrations) predate this file; see `git log` of the integration branch.
