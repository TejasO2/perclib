# Bounds on crossing and multi-arm events on ℤ²: advice for the wiki

Advice for the wiki agent on package A1b of the arms plan, the second half of package A1 (the
first half is in `multi-arm-basics.md`). It adds two files:

* `PercLib/Probability/LocallyMonotone.lean` (344 lines, 12 theorems). It is general, not
  planar: any index type, any profile.
* `PercLib/Models/Planar/Arms/MultiArmBounds.lean` (760 lines, 27 theorems).

Both files are proof-only: no definition, no tag, no `…Input`. `Arms/Defs.lean` and
`Planar/Defs.lean` are unchanged. Everything uses only `propext`, `Classical.choice` and
`Quot.sound`.

Three of the four remaining A1 items are done, in the order A2 needs them:

* item 9, Nolin's Lemma 13 (FKG for locally monotone events);
* item 8, the tail of the number of disjoint crossings (Nolin's Lemma 15, first step);
* item 6, the a priori upper bound for multi-arm events, for both colours (Nolin's
  Proposition 14, upper half).

Item 7 (colour inversion at `1/2`) was done afterwards (A1c, `colour-inversion.md`); the
optional item 4 is not done; see "Not done here".

Numbering: these are the numbers of the published version (EJP 13, 2008). The arXiv version
0711.4948v1 numbers them one lower: Lemma 13 is its Lemma 12, Proposition 14 its
Proposition 13, Lemma 15 its Lemma 14.

## Conventions

As in `multi-arm-basics.md`: points of `ℤ²` are `![x, y]`, boxes are `Set.Icc lo hi`,
`B_r(z) = Icc (z - r) (z + r)`, the face `f` is the unit square with lower-left corner `f`,
`π_σ(r, R)` is the probability of `multiArmEvent σ z r R`. `law q` is by definition
`prodBernoulli q`, so the general lemmas below apply to it directly.

## Statements as proved

### FKG for locally monotone events (Nolin, Lemma 13)

`prodBernoulli_mul_mul_le_inter_of_determined`, for any index type `ι` and profile `p`. Let
`S`, `Sinc`, `Sdec` be pairwise disjoint sets of coordinates. Let `Ainc`, `Binc` be increasing,
`Adec`, `Bdec` decreasing, all measurable, with:

* `Ainc` determined by `S ∪ Sinc`, `Adec` by `S ∪ Sdec`;
* `Binc` determined by `Sinc`, `Bdec` by `Sdec`.

Then

```lean
prodBernoulli p (Ainc ∩ Adec) * prodBernoulli p Binc * prodBernoulli p Bdec ≤
  prodBernoulli p (Ainc ∩ Adec ∩ (Binc ∩ Bdec))
```

"Determined by `P`" is the library's form `∀ ω ω', ω ∩ P = ω' ∩ P → (ω ∈ A ↔ ω' ∈ A)`, as in
`prodBernoulli_inter_of_determined`.

### Splicing (a tool, also usable elsewhere)

`prodBernoulli_prod_map_splice`: for two independent configurations with law
`prodBernoulli p`, the configuration `(ω₁ ∩ S) ∪ (ω₂ \ S)` again has law `prodBernoulli p`, for
any set `S`. `prodBernoulli_eq_lintegral_splice` is the resulting conditioning formula:
`P(E) = ∫ P({y | (x ∩ S) ∪ (y \ S) ∈ E}) dP(x)` for measurable `E`.

### BK powers

* `prodBernoulli_foldl_replicate_le_pow`: for an increasing `C` on a countable index set,
  `P((List.replicate h C).foldl disjointOccurrence univ) ≤ P(C)^h`. `C` need not be measurable.
* `prodBernoulli_foldl_replicate_le_pow_of_isLowerSet`: the same for a measurable decreasing
  `D`.
* `preimage_compl_disjointOccurrence`, `preimage_compl_foldl_disjointOccurrence`: disjoint
  occurrence commutes with complementing configurations.

### Tail of the number of disjoint crossings (Nolin, Lemma 15, first step)

Assume `h : CrossingBounds q L c`, `1 ≤ n` and `n ≤ L`. Four shapes, two colours:

| Theorem | Event | Bound |
|---|---|---|
| `law_crossing_one_le_one_sub` | open bottom-top crossing of `[lo, lo + (k n, n + 1)]` | `1 - c (k + 1)` |
| `law_crossing_zero_le_one_sub` | open left-right crossing of `[lo, lo + (n + 1, k n)]` | `1 - c (k + 1)` |
| `law_dualConfig_crossing_one_le_one_sub` | dual bottom-top crossing of the box of faces `[lo, lo + (k n, n + 1)]` | `1 - c (k + 1)` |
| `law_dualConfig_crossing_zero_le_one_sub` | dual left-right crossing of the box of faces `[lo, lo + (n + 1, k n)]` | `1 - c (k + 1)` |

The `law_foldl_…_le_pow` versions bound `m` disjoint occurrences of the same events,
`(List.replicate m E).foldl disjointOccurrence univ`, by `(1 - c (k + 1))^m`.

To get these events from walks:

* `mem_foldl_crossing_of_walks` (any `ℤ^d`): `h` walks along open edges, each inside the box
  from its face `{v i = lo i}` to its face `{v i = hi i}`, with pairwise disjoint edge lists,
  give `ω ∈ (List.replicate h (crossing i lo hi)).foldl disjointOccurrence univ`.
* `mem_foldl_dualConfig_crossing_of_walks`: the same for walks of faces along edges of
  `dualConfig ω`; the result is the event for `dualConfig ⁻¹' crossing i lo hi`.

Disjoint edge sets are the weakest disjointness. Vertex-disjoint open arms and face-disjoint
dual arms (`ArmsDisjoint`) have disjoint edge sets.

### A priori upper bound (Nolin, Proposition 14, upper half)

```lean
theorem exists_law_multiArmEvent_le_rpow {j : ℕ} (σ : Fin j → Bool) {col : Bool}
    (hσ : ∃ i, σ i = col) (c : ℕ → ℝ≥0∞) :
    ∃ C a : ℝ, 0 < a ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), (R : ℕ∞) ≤ L →
        (law q).real (multiArmEvent σ z r R) ≤ C * ((r + 1 : ℝ) / (R + 1)) ^ a
```

With `col = true` it is the plan's statement; with `col = false` it is the dual version. The
constants depend only on `c`, so they do not depend on `q`, `L`, `z`, `r` or `R`. The proof gives
`C = 6^a` and `4^(-a) = 1 - min (c 7 ^ 4) (1/2)`.

The quantitative form behind it is `law_multiArmEvent_zero_le_one_sub_pow`: at the origin,
`π_σ(r, R) ≤ (1 - c 7 ^ 4)^N` when the `N` scales `(r + 2) 4^i`, `i < N`, are all at most
`R / 3`, and `R ≤ L`.

Tools used by this proof, also usable elsewhere:

* `CrossingBounds.le_law_crossing_zero_of_le` and its three companions (`…_one_of_le`,
  `…_dualConfig_…`): a box at most `k m` long and at least `m` wide is crossed in its long
  direction with probability at least `c k`.
* `notMem_multiArmEvent_of_notMem_crossing`: an open arm from `B_r(0)` to `∂B_R(0)` crosses one
  of the four strips around `t ≤ ‖·‖∞ ≤ 3t` in its short direction (`r ≤ t`, `3t ≤ R`).
* `notMem_multiArmEvent_of_mem_crossing`: an open circuit made of four long crossings of boxes
  around `t ≤ ‖·‖∞ ≤ 3t + 1` blocks every dual arm (`r < t`, `3t ≤ R`).
* `law_le_one_sub_pow_of_blocking`: blocking events of probability at least `β` at `N` scales,
  determined by edges inside pairwise disjoint sets, give `(1 - β)^N`.
* `law_translate_apply`: the law of the profile `e ↦ q (e + a)` is the law of `q` seen from
  `a`.

## Proofs the Lean follows

**Lemma 13.** This is Nolin's proof: condition on the coordinates in `S`. In Lean the
conditioning is the splicing identity. Take `x` for the configuration on `S`. Then:

* the section of `Ainc` at `x` is increasing and determined by `Sinc`, and the section of
  `Adec` is decreasing and determined by `Sdec`;
* `Binc` and `Bdec` equal their sections.

Independence of events determined by the disjoint sets `Sinc` and `Sdec`, and Harris in each,
give the inequality for every `x`. Integrating over `x` with `lintegral_mul_const'` finishes.
The splicing identity is checked on the events `{F ⊆ ω}`, `F` finite, which generate the
σ-algebra (`measure_ext_of_finset_subset`).

**BK powers.** `countable_profile_bk_foldl` with all events equal to `C`. For a decreasing
`D`, the complement of a configuration of law `prodBernoulli p` has law
`prodBernoulli (1 - p)`, under which the complement-preimage of `D` is increasing. Disjoint
occurrence commutes with complementing, because fixing coordinates of `ω` or of `ωᶜ` is the same
thing. `Measure.le_map_apply` avoids any measurability condition on the iterated event.

**Crossing tail.** By box duality (`compl_crossing_one_eq_preimage_dualConfig`,
`crossing_zero_eq_compl_preimage_dualConfig`, `mem_crossing_zero_iff_dualConfig_notMem_crossing_one`,
`mem_crossing_one_iff_dualConfig_notMem_crossing_zero`), the complement of a short crossing of
a box of size `k n × (n + 1)` contains a long crossing of the other colour of a box of size
`(k n + 1) × n`. That box is shorter than a `(k + 1) n × n` box, so it is crossed with probability
at least `c (k + 1)` (`crossing_zero_subset_crossing_zero`). The shapes `k n × (n + 1)` are chosen
so that the comparison box has exactly the height `n` that `CrossingBounds` needs; other shapes
follow by monotonicity in the box. The tail is BK. A walk with open edges inside the box from side
to side is a certificate for the crossing event (its edge set forces it), so `h` walks with
disjoint edge sets are `h` disjoint certificates (`mem_foldl_replicate_disjointOccurrence` from
`Tightness/BKStep.lean`). For dual walks the certificates are the closed edges of `ℤ²` that they
cross.

**A priori bound.** This is P7's multi-scale blocking, run under `CrossingBounds` and for both
colours.

* *Open arms.* The blocking event at scale `t` is "none of the four strips of
  `notMem_localConn_of_notMem_crossing` is crossed in its short direction". Each complement is a
  dual long crossing of a box of faces of size `(6t + 1) × (2t - 1)`. Such a box is shorter than
  `7 m × m` with `m = 2t - 1`, so it has probability at least `c 7`. By Harris for decreasing
  events the four together have probability at least `c 7 ^ 4`.
* *Dual arms.* The blocking event is four open long crossings of boxes of size
  `(6t + 1) × (2t - 1)`, forming a circuit, by Harris for increasing events. Box duality turns
  them into "no dual short crossing of the four strips of faces". Then
  `notMem_localConn_of_notMem_crossing`, applied to `dualConfig ω`, blocks the dual arm.

All eight boxes lie in the annulus `t ≤ ‖v‖∞ ≤ 3t + 1`. The scales `(r + 2) 4^i` keep these
annuli pairwise disjoint, so the blocking events are independent
(`law_biInter_of_determined_internalPairs`). The `+ 2` makes every scale at least `2`, so
that `3t + 1 < 4t`. The number `N` of scales with `3 s ≤ R` satisfies
`R + 1 ≤ 3 (r + 2) 4^N ≤ 6 (r + 1) 4^N`, which turns `(1 - β)^N` into `6^a ((r + 1)/(R + 1))^a`.
A general centre `z` is reduced to the origin with `CrossingBounds.translate`,
`law_translate_apply` and `image_add_mem_multiArmEvent_iff`.

The handoff suggested comparing a single arm with P7's `armEvent`; that does not work for
`r > 0`. `armEvent` starts at the centre, while an arm of `multiArmEvent` starts anywhere in
`B_r(z)`. The blocking lemma `notMem_localConn_of_notMem_crossing` already takes a general
start, so it is used directly.

## Statement choices compared with the plan

1. **Lemma 13** is stated multiplicatively, with no division by `P(Ainc ∩ Adec)`. This is
   Nolin's conditional form once multiplied out, and it holds also when `P(Ainc ∩ Adec) = 0`.
   Nolin's sets are finite. Here they are arbitrary, so measurability of the four events is
   assumed. Finite sets make every determined event measurable.
   The theorem has fifteen hypotheses: three disjointness, four monotonicity, four
   determination and four measurability conditions. The docstring records why. A structure
   would need an interface package.
2. **The a priori bound** is stated for every colour `col`, with `∃ i, σ i = col`. The plan's
   statement (`col = true`) and its dual version are the two cases. The plan's hypothesis
   `r ≤ R` is dropped because the proof does not use it: for `R < 3 (r + 2)` there is no scale
   and the right-hand side is at least `1`. Both changes make the theorem stronger.
3. **The crossing tail** is stated for events, as iterated disjoint occurrence. Two bridges
   take families of walks to these events. This leaves A2 free to choose its domain. The
   plan's strip `[0, 4N] × [0, N]` with vertical crossings is the shape `k = 4`, `n + 1 = N`,
   up to the monotonicity of crossings in the box.
4. **General lemmas** go to `PercLib/Probability/LocallyMonotone.lean`, not to the planar file:
   splicing, Lemma 13, the commutation with complements and both BK powers mention no
   percolation. This follows rule 5.

## Not done here

* **Item 7, colour inversion at `1/2`**: done afterwards (A1c) in
  `Arms/ColourInversion.lean`, `law_multiArmEvent_comp_not_le`, by the route checked on paper in
  `multi-arm-basics.md`; see `colour-inversion.md`.
* **Item 4** (optional): nonemptiness of the I2b example sequences for every `R ≥ 1`.

## What A2 has from A1 and A1b

From A1 (`multi-arm-basics.md`):

* `exists_crossingBounds_half`;
* order invariance `sbtw_innerPos_iff_sbtw_landingPos`;
* the cuts and doubled arms;
* monotonicity in the radii;
* the upper half of quasi-multiplicativity.

From A1b:

* the crossing tail `law_foldl_…_le_pow` with the bridges `mem_foldl_crossing_of_walks` and
  `mem_foldl_dualConfig_crossing_of_walks` (Nolin's step (a));
* Lemma 13, for gluing in A3;
* the a priori bound, for A3 and U2;
* the blocking tools.

A2 still has to state relative duality (`quad-duality-c.md`, §"Relative duality").

## Search

* **mathlib**:
  * used: `Measure.prod_apply`, `Measure.prod_prod`, `lintegral_mul_const'`,
    `Measure.le_map_apply`, `Finset.prod_filter_mul_prod_filter_not`, `prob_compl_eq_one_sub`
    and the `Real.logb` and `Real.rpow` lemmas;
  * not found: no FKG for events of mixed monotonicity, and no splicing of product measures on
    `Set ι`.
* **PercLib**:
  * no splicing lemma existed. These were checked:
    * `Superposition.lean` (intersections and unions of independent configurations);
    * `FiniteEnergy/Insertion.lean` (`prodBernoulli_map_overwrite`, a fixed assignment on a
      block);
    * `SplitCoordinate.lean` (one coordinate);
    * `Harris.lean` (`integral_integral_piecewise`, for finite sets on `infinitePi`).
  * no law-translation lemma existed outside the proof of `CrossingBounds.translate`, so
    `law_translate_apply` states it.
  * reused:
    * `countable_profile_bk_foldl`, `prodBernoulli_harris`, `prodBernoulli_harris_of_isLowerSet`;
    * `prodBernoulli_inter_of_determined`, `prodBernoulli_map_compl`,
      `measure_ext_of_finset_subset`;
    * `mem_foldl_replicate_disjointOccurrence` (`Tightness/BKStep.lean`), `mem_localConn_of_walk`;
    * the four box dualities, `crossing_zero_subset_crossing_zero` and
      `crossing_one_subset_crossing_one`;
    * `notMem_localConn_of_notMem_crossing`, `mem_crossing_iff_of_inter_eq`,
      `law_biInter_of_determined_internalPairs`;
    * `CrossingBounds.translate`, `image_add_mem_multiArmEvent_iff`.

## Sources

P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
no. 55:

* Lemma 13, FKG for locally monotone events, p. 1577;
* Proposition 14, a priori bounds, p. 1578; the upper half is sketched there as "concentric
  annuli";
* Lemma 15, first step of the proof, p. 1579.

The statements were checked against arXiv 0711.4948v1 (Lemma 12, Proposition 13, Lemma 14
there).
