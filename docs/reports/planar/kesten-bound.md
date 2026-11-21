# Kesten's bound p_c(ℤ²) ≤ 1/2: advice for the wiki

Advice for the wiki agent on the second planar package: nearest-neighbour bond percolation on
`ℤ²` has critical edge probability at most `1/2`, and percolates for every edge probability
above `1/2`. Everything below is proved in Lean with only `propext`, `Classical.choice` and
`Quot.sound`; no `…Input` is used. No `@[tag]` attribute has been added: the declarations
listed here are what the wiki agent's tagged statements should point at.

Lean file: `PercLib/Models/Planar/KestenBound.lean`. It builds on the duality package
(`docs/reports/planar/duality.md`) and on the sharpness theorems of
`PercLib/Percolation/Bond/Sharpness.lean`.

## Conventions

- The library parametrises bond percolation by an intensity: with a kernel
  `J : Sym2 V → ℝ≥0`, the edge `e` is open with probability `1 - e^{-β J(e)}`
  (`intensityProfile J β`). Thresholds are intensities in `ℝ≥0∞`
  (`rootCriticalIntensity J x`, `globalCriticalIntensity J`).
- Nearest-neighbour percolation on `ℤ²` is the kernel `J = (zdGraph 2).edgeSet.indicator 1`
  (one on the edges of `ℤ²`, zero on all other pairs), written inline; no new definition was
  added. An edge is then open with probability `p = 1 - e^{-β}`, so `p = 1/2` is `β = log 2`,
  and `p > 1/2` is `β > log 2`. The bound `β_c ≤ log 2` is the statement `p_c(ℤ²) ≤ 1/2`.

## Statements as proved

**1. Infinite susceptibility at the self-dual point**
(`chi_intensityProfile_indicator_edgeSet_log_two_eq_top`). At intensity `log 2` the expected
size of the open cluster of every vertex is infinite:

```lean
theorem chi_intensityProfile_indicator_edgeSet_log_two_eq_top (x : LatticeSite 2) :
    chi (intensityProfile ((zdGraph 2).edgeSet.indicator 1) (Real.log 2).toNNReal) x = ⊤
```

**2. Kesten's bound** (`rootCriticalIntensity_indicator_edgeSet_le_log_two` and
`globalCriticalIntensity_indicator_edgeSet_le_log_two`):

```lean
theorem rootCriticalIntensity_indicator_edgeSet_le_log_two (x : LatticeSite 2) :
    rootCriticalIntensity ((zdGraph 2).edgeSet.indicator 1) x ≤ ENNReal.ofReal (Real.log 2)

theorem globalCriticalIntensity_indicator_edgeSet_le_log_two :
    globalCriticalIntensity ((zdGraph 2).edgeSet.indicator (1 : Sym2 (LatticeSite 2) → ℝ≥0)) ≤
      ENNReal.ofReal (Real.log 2)
```

**3. Percolation above one half** (`one_sub_div_le_law_cluster_infinite_indicator_edgeSet` and
`law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt`). For every intensity `β > log 2`,
that is every edge probability `p > 1/2`, the cluster of every vertex is infinite with
probability at least `1 - log 2 / β`, in particular with positive probability:

```lean
theorem one_sub_div_le_law_cluster_infinite_indicator_edgeSet {β : ℝ≥0}
    (hβ : Real.log 2 < β) (x : LatticeSite 2) :
    1 - ENNReal.ofReal (Real.log 2) / β ≤
      law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β) {ω | (cluster ω x).Infinite}

theorem law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt {β : ℝ≥0}
    (hβ : Real.log 2 < β) (x : LatticeSite 2) :
    0 < law (intensityProfile ((zdGraph 2).edgeSet.indicator 1) β) {ω | (cluster ω x).Infinite}
```

The quantitative bound is the mean-field lower bound of sharpness with `β_c` replaced by its
upper bound `log 2`. In edge-probability terms it reads
`θ(p) ≥ 1 - log 2 / log(1/(1 - p))`.

The matching lower bound `p_c(ℤ²) ≥ 1/2` (Harris's theorem) is **not** proved here; it needs
`θ(1/2) = 0`, for instance by Zhang's argument, which uses uniqueness of the infinite cluster.
So the wiki assertion "p_c(ℤ²) = 1/2" is half proved: the `≤` direction is this package.

**Supporting results**, each usable on its own:

- `indicator_edgeSet_transitive`, `summable_indicator_edgeSet`: the nearest-neighbour kernel
  of `ℤ²` satisfies the hypotheses of the sharpness theorems (transitive under translations;
  finite rows).
- `intensityProfile_indicator_edgeSet_log_two`: at `β = log 2` every edge is open with
  probability `1/2`.
- `tau_intensityProfile_indicator_edgeSet_add_add`: translation invariance of the two-point
  function.
- `law_crossing_zero_le_sum_tau`: the probability of a left-right crossing of
  `[0, n + 1] × [0, n]` is at most the sum of `τ(a, b)` over `a` on the left side and `b` on
  the right side (any profile).
- `half_le_mul_sum_tau_log_two`: at `β = log 2`,
  `(n + 1) · Σ_{|k| ≤ n} τ(0, (n + 1, k)) ≥ 1/2` for every `n`.

## Sources and locators

- H. Kesten, "The critical probability of bond percolation on the square lattice equals 1/2",
  *Comm. Math. Phys.* **74** (1980), 41–59, DOI 10.1007/BF01197577. The original proof of
  `p_c ≤ 1/2` (with Harris 1960, `p_c = 1/2`). The Lean does not follow this paper's proof.
- H. Duminil-Copin and V. Tassion, "A new proof of the sharpness of the phase transition for
  Bernoulli percolation on ℤ^d", *L'Enseignement Math.* **62** (2016), 199–206 (arXiv
  1502.03051). Theorem 1.1 is sharpness (exponential decay below `p_c`, mean-field lower bound
  above it); Remark 6 of the arXiv version notes that it gives `p_c ≤ 1/2` on `ℤ²`. This is the
  modern route formalised here. The general version is H. Duminil-Copin and V. Tassion, "A new
  proof of the sharpness of the phase transition for Bernoulli percolation and the Ising
  model", *Comm. Math. Phys.* **343** (2016), 725–745 (arXiv 1502.03050).
- G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.3 "The Critical Probability
  Equals ½" (pp. 287–294; section title and pages checked against the printed contents). The
  remark of Duminil-Copin and Tassion cites Zhang's argument for the lower bound as Lemma 11.12
  of this book; that lemma number was not checked against the text.
- B. Bollobás and O. Riordan, *Percolation*, Cambridge University Press, 2006, Chapter 3
  "Bond percolation on Z² – the Harris–Kesten Theorem" (p. 50), §3.4 "Kesten's Theorem"
  (p. 67), and §5.2 "The Harris–Kesten Theorem revisited" (p. 124); titles and pages checked
  against the printed contents only.

The library's sharpness theorem is in the intensity form, with the susceptibility in place of
the one-arm probability: below `β_c` the susceptibility is finite
(`chi_lt_top_of_lt_rootCriticalIntensity`). Infinite susceptibility at `log 2` is therefore
the input used, not the slow decay of the one-arm probability as in Remark 6.

## Proof outline (as in the Lean)

1. **Crossings at one half.** By the duality package, the box `[0, n + 1] × [0, n]` has an
   open left-right crossing with probability exactly `1/2` when every edge is open with
   probability `1/2` (`law_crossing_zero_eq_half`).
2. **Union bound.** A left-right crossing joins some `(0, i)` to some `(n + 1, j)`,
   `0 ≤ i, j ≤ n`, so `1/2 ≤ Σ_{i, j} τ((0, i), (n + 1, j))`.
3. **Translation invariance.** `τ((0, i), (n + 1, j)) = τ(0, (n + 1, j - i))`, and
   `j - i` ranges over `[-n, n]`, so
   `1/2 ≤ (n + 1) · Σ_{|k| ≤ n} τ(0, (n + 1, k))`.
4. **Harmonic series.** The points `(n + 1, k)`, `|k| ≤ n`, are distinct for distinct `n`, so
   `χ(0) = Σ_y τ(0, y) ≥ Σ_{n < N} 1/(2(n + 1))` for every `N`, and `χ(0) = ∞`.
5. **Sharpness.** The kernel is transitive with finite rows, so `χ < ∞` at every intensity
   below `β_c`. Since `χ = ∞` at `log 2`, `β_c ≤ log 2`. The global threshold equals the root
   threshold by transitivity.
6. **Percolation above `log 2`.** The mean-field bound of sharpness,
   `P_β(|K_x| = ∞) ≥ 1 - β_c / β` for `β > β_c`, with `β_c ≤ log 2`, gives
   `P_β(|K_x| = ∞) ≥ 1 - log 2 / β > 0`.

## Declarations by role

| Role | Declaration |
|---|---|
| χ = ∞ at `p = 1/2` | `chi_intensityProfile_indicator_edgeSet_log_two_eq_top` |
| `p_c(ℤ²) ≤ 1/2`, root threshold | `rootCriticalIntensity_indicator_edgeSet_le_log_two` |
| `p_c(ℤ²) ≤ 1/2`, global threshold | `globalCriticalIntensity_indicator_edgeSet_le_log_two` |
| `θ(p) ≥ 1 - log 2/β` for `β > log 2` | `one_sub_div_le_law_cluster_infinite_indicator_edgeSet` |
| Percolation for `p > 1/2` | `law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt` |
| Kernel transitive, finite rows | `indicator_edgeSet_transitive`, `summable_indicator_edgeSet` |
| Union bound for a crossing | `law_crossing_zero_le_sum_tau` |
| Column sums at `1/2` | `half_le_mul_sum_tau_log_two` |

All declarations are in namespace `PercLib.Models.Planar`.

## Suggestions for the tagged statements

- Tag `p_c(ℤ²) ≤ 1/2` against `rootCriticalIntensity_indicator_edgeSet_le_log_two` (and the
  global form if the wiki states it), with a sentence translating intensity to edge
  probability (`p = 1 - e^{-β}`).
- Tag "percolation occurs for every `p > 1/2`" against
  `law_cluster_infinite_indicator_edgeSet_pos_of_log_two_lt`.
- Keep the equality `p_c(ℤ²) = 1/2` untagged or `stated` until `θ(1/2) = 0` is proved.
