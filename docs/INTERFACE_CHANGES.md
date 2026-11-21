# Interface changes

Changes to shared definitions and public names that can break other branches are announced
here before they merge (decision D-37, item h), with the migration recipe. Renames keep a
deprecated alias for one release where that is possible.

## Announced, not yet merged

### Connection probability under a general measure (`connProb`)

- **What:** a new definition in `PercLib/Percolation/Bond/Basic.lean`,
  `connProb (μ : Measure (Config V)) (x y : V) : ℝ≥0∞ := μ (conn x y)`, with
  `connProb_def` and the simp lemma `connProb_law : connProb (law q) x y = tau q x y`.
  Results in `Bond/{Transport,ConnectionKernel,TriangleDecay,ClusterCount,ClusterMoments}.lean`
  and `Bond/Tightness/Hyperscaling.lean` that never used independence are restated for an
  arbitrary measure `μ` on configurations (`law q` becomes `μ`, `tau q` becomes `connProb μ`,
  with `[IsProbabilityMeasure μ]` where needed). One tagged statement changes spelling (Q0D1).
- **Renames:** `tendsto_tau_cofinite` → `tendsto_connProb_cofinite`,
  `tendsto_tau_sq_cofinite` → `tendsto_connProb_sq_cofinite`; the full table is added here
  when the change merges.
- **Recipe:** to use a generalised lemma at the independent law, apply it with `μ := law q`
  and rewrite with `connProb_law`.

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

## Merged

Earlier respellings (the `localConn`/`localCluster`/`boundaryFlux`/`IsCut` fold, the header
and linter migrations) predate this file; see `git log` of the integration branch.
