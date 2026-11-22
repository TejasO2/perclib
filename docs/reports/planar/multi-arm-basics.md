# Basic facts about multi-arm events on ℤ²: advice for the wiki

Advice for the wiki agent on package A1 of the arms plan, the first package of the stage on arm
separation and quasi-multiplicativity (Nolin 2008, §4). It is proved in the new file
`PercLib/Models/Planar/Arms/MultiArmBasics.lean` (901 lines, 33 theorems). The file is
proof-only: it adds no definition and no tag, and `Arms/Defs.lean` is unchanged. Everything uses
only `propext`, `Classical.choice` and `Quot.sound`, and no `…Input` is used.

Four of the plan's items are done:

* crossing bounds at `1/2`;
* order invariance for arms of both colours;
* monotonicity in the radii;
* the upper half of quasi-multiplicativity.

The other four items are not done and are recorded as A1b (see "Not done here"):

* the a priori upper bound;
* colour inversion;
* the tail of the number of disjoint crossings;
* Nolin's Lemma 13.

No wiki assertion is attached yet. These results are tools for arm separation (A2),
quasi-multiplicativity (A3) and the universal exponents (U1, U2).

## Conventions

As in `arms-interface-a.md` and `arms-interface-b.md`:

* A point of `ℤ²` is `![x, y]`, boxes are `Set.Icc lo hi`, and `B_r(z) = Icc (z - r) (z + r)`.
* A face `f` is the unit square with lower-left corner `f`.
* `multiArmEvent σ z r R` is the event `A_σ(r, R)` at `z`. Write `π_σ(r, R)` for its probability.
* Three integers are in counterclockwise order when `sbtw a b c`, for mathlib's `CircularOrder ℤ`.
* The **doubled lattice** is the lattice in which positions are measured (`innerPos`,
  `landingPos`). There a point `v` becomes `2v`, a face `f` its centre `2f + (1, 1)`, and an edge
  its midpoint, which is the sum of its ends.

## Statements as proved

**Crossing bounds at one half** (`exists_crossingBounds_half`):

```lean
theorem exists_crossingBounds_half :
    ∃ c : ℕ → ℝ≥0∞, ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) → CrossingBounds q ⊤ c
```

One sequence `c` works for every law with all edges of `ℤ²` open with probability `1/2`, at
every scale. A compiled `example` gives the witness for the constant profile `1/2`.

**Order invariance for both colours** (`sbtw_innerPos_iff_sbtw_landingPos`). Suppose `B_r(z)`
lies in the interior of `Icc lo hi`, and `γ` is a disjoint family of arms of colours `σ` from
`B_r(z)` to the boundary of `Icc lo hi`. Then for all `i, k, l`:

```lean
sbtw (innerPos z r (σ i) (γ i)) (innerPos z r (σ k) (γ k)) (innerPos z r (σ l) (γ l)) ↔
  sbtw (landingPos lo hi (σ i) (γ i)) (landingPos lo hi (σ k) (γ k))
    (landingPos lo hi (σ l) (γ l))
```

In words, three arms leave the inner box in counterclockwise order exactly when they land in
counterclockwise order. Open and dual arms may be mixed in any way.

**Monotonicity in the radii**:

* `multiArmEvent_subset_of_le`: `A_σ(r, R) ⊆ A_σ(r', R')` when `r ≤ r' < R' ≤ R`.
* Two forms with windows. They hold for any outer box `Icc lo hi`, not only centred ones.
  * `multiArmEventTo_subset_of_le` enlarges the inner radius. It keeps the landing windows `I`,
    with the inner windows equal to `univ`. It needs `B_{r'}(z)` in the interior of `Icc lo hi`.
  * `multiArmEventTo_subset_of_le_of_le` shrinks the outer box to `Icc lo' hi'`. It keeps the
    inner windows `J`, with the landing windows equal to `univ`. It needs `lo ≤ lo'`, `hi' ≤ hi`,
    and `B_r(z)` in the interior of `Icc lo' hi'`.

**Upper half of quasi-multiplicativity** (`law_multiArmEvent_le_mul`). For every profile `q`,
all colours `σ`, every centre `z` and `r₁ < r₂ < r₃`:

```lean
law q (multiArmEvent σ z r₁ r₃) ≤
  law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃)
```

So `π_σ(r₁, r₃) ≤ π_σ(r₁, r₂) π_σ(r₂, r₃)`, with no gap between the two annuli. The law is
any product law; no crossing bound is used.

**Tools**, also usable elsewhere:

* `IsOpenArm.exists_double`, `IsDualArm.exists_double` and `IsArm.exists_double` give the
  doubled arms. `IsArm.double_disjoint` says that the doubled arms of a disjoint family are
  disjoint.
* `exists_walk_double`, `exists_walk_double_tail` and `exists_walk_double_dropLast` give the
  doubled walk of any walk of `ℤ²`, translated by any `c`. The second drops the first vertex and
  the third drops the last vertex.
* `IsArm.exists_append_eq_of_le` cuts an arm at a larger inner box: it starts the arm at its last
  vertex, or face, touching the larger box. `IsArm.exists_append_eq_of_le_of_le` cuts it at a
  smaller outer box: it stops the arm at its first exit. `landingPos_append` and
  `innerPos_append` say that these cuts keep the landing and inner positions.
* `ArmsDisjoint.mono`: pieces of a disjoint family are disjoint.
* For walks of any graph (`SimpleGraph.Walk`):
  * `IsCrossing.exists_append_eq_isCrossing` stops a crossing at its first vertex outside a
    smaller set.
  * `IsCrossing.exists_append_eq_isCrossing_of_subset` starts a crossing at its last vertex in a
    larger set.
  * `exists_append_eq_of_notMem` and `exists_append_eq_of_exists_mem` split a walk at its first
    exit and at its last visit.
  * `snd_append_of_not_nil`, `penultimate_append_of_not_nil` and
    `snd_eq_of_mem_darts_of_fst_eq` are small facts about the second and last-but-one vertices.
* Coordinates and midpoints:
  * `mem_Icc_innerBox_iff`, `mem_boxBoundary_innerBox_iff`, `mem_Icc_two_nsmul_iff`,
    `mem_boxBoundary_two_nsmul_iff` and `add_one_le_of_Icc_subset` are forms ready for `omega`.
  * `eq_and_eq_or_of_add_eq`: two edges with the same midpoint are equal.
  * `dualEdge_eq_of_add_eq`: an edge and a dual edge with the same doubled midpoint cross.

## Proofs the Lean follows

**Crossing bounds.** For the open half, RSW in any position and either direction
(`exists_pos_le_law_crossing`) is exactly the field `le_law_crossing`. For the dual half, the
dual crossing event is `dualConfig ⁻¹' crossing i lo hi`. Self-duality
(`law_preimage_dualConfig_eq`, for events that read only edges of `ℤ²`) gives it the probability
of `crossing i lo hi`. So **no half-lattice shift is needed**, contrary to the handoff's
suggestion: `CrossingBounds` states dual crossings of boxes of faces, and those are crossings of
the same boxes for the dual configuration.

**Doubled arms.**

* An open arm `v₀, …, v_m` becomes `v₀ + v₁, 2v₁, v₁ + v₂, …, 2v_m`. The doubled walk is cut
  after its first step. In I2b's convention open arms may share their first vertex, so they
  must be cut there.
* A dual arm `f₀, …, f_m` becomes `2f₀ + 1, f₀ + f₁ + 1, …, 2f_{m-1} + 1, f_{m-1} + f_m + 1`. The
  doubled walk is cut before its last face.

Consecutive points differ by a unit vector, so these are walks of `ℤ²`. The coordinate facts
are:

* the start lies on the boundary of `I = 2z + [-(2r + 1), 2r + 1]²`;
* the walk meets `I` nowhere else;
* the walk lies in `O = Icc (2 lo) (2 hi)`;
* the end lies on the boundary of `O`.

These follow from the arm conditions (`IsCrossing`) and are checked with `omega`. One extra fact
is needed for open arms. A midpoint `v + v'` with `v` the start lies in `I` only for the first
edge. This is because the tail of an open arm never returns to `B_r(z)`
(`snd_eq_of_mem_darts_of_fst_eq`).

**Disjointness of doubled arms.** There are three pairs of colours.

* **Two open arms.** A doubled vertex `2w` comes from the tail, which avoids the other arm. Two
  equal midpoints come from the same edge (`eq_and_eq_or_of_add_eq`). The end of that edge lies
  in the tail of the first arm and on the second arm.
* **Two dual arms.** They share no face. Equal midpoints come from the same dual edge.
* **An open arm and a dual arm.** `2w` is even–even, `2f + 1` is odd–odd, and midpoints have
  mixed parity. So the only possible coincidence is between an edge midpoint `u + u'` and a dual
  edge midpoint `f + f' + 1`. Then the dual edge crosses the edge (`dualEdge_eq_of_add_eq`). But
  the edge is open in `ω` and the dual edge is open in `dualConfig ω`, which is impossible.

**Order invariance** then is `cyclicallyOrdered_end_iff_of_pairwise_disjoint` (PT2b), applied to
the doubled family with inner box `I` and outer box `O`. The positions of the starts and ends of
the doubled walks are by definition `innerPos` and `landingPos`.

**Monotonicity.**

* **Inner radius.** Each arm starts again at its last vertex in `B_{r'}(z)` (open), or its last
  face in `Icc (z - r' - 1) (z + r')` (dual). The end and the last step do not change, so the
  landing positions do not change either.
* **Outer box.** Each arm stops at its first vertex outside `Icc (lo' + 1) (hi' - 1)` (open), or
  its first face outside `Icc lo' (hi' - 1)` (dual). The start and the first step do not change,
  so the inner positions do not change. Order invariance for the old family and for the new
  family then transfers the counterclockwise order of the landing positions. The first-hit form
  of PT2b is not needed: I2b's arms already stop at their first exit.

Pieces of a disjoint family stay disjoint (`ArmsDisjoint.mono`), because their supports and tails
are contained in the old ones.

**Quasi-multiplicativity, upper half.** `A_σ(r₁, r₃)` is contained in `A_σ(r₁, r₂)` and in
`A_σ(r₂, r₃)`, by monotonicity. I2b's sharp determination (`mem_multiArmEventTo_iff_of_agree`)
says which edges each event reads:

* `A_σ(r₁, r₂)` reads only edges with both ends in `B_{r₂}(z)`;
* `A_σ(r₂, r₃)` reads only edges with an end outside `B_{r₂}(z)`.

These two sets of edges are disjoint, so the events are independent
(`prodBernoulli_inter_of_determined`).

## Statement choices compared with the plan

1. **`r' < R'` in the monotonicity**, where the plan had `r' ≤ R'`. The plan's statement is
   false at `r' = R'`. Take `σ` to be twelve open arms, `z = 0` and `r = r' = R' = 1`, `R = 3`.
   * `A_σ(1, 3)` contains the configuration with every edge open. There are twelve straight arms,
     one along each of the twelve edges leaving `B_1`, landing at twelve distinct points of
     `∂B_3` in counterclockwise order.
   * `A_σ(1, 1)` is empty. An arm from `B_1` to the boundary of `B_1` has no step (`IsCrossing`
     with `S = Icc (z - 1) (z + 1)` and `T` its interior). So twelve arms would need twelve
     distinct positions in counterclockwise order among the eight points of `∂B_1`.

   For `r' = R'` the event no longer depends on the configuration. Nolin's annuli always have
   inner radius below outer radius, so the strict inequality is the faithful reading.
2. **`r₁ < r₂ < r₃` and no gap in quasi-multiplicativity**, where the plan had `r₁ ≤ r₂`,
   `r₂ + 1 ≤ r₃` and the second event `A_σ(r₂ + 1, r₃)`. The plan's form is false at `r₁ = r₂`,
   by the same example: the right-hand side is `π_σ(1, 1) π_σ(2, 3) = 0`, while `π_σ(1, 3) > 0`
   at `1/2`. When `r₂ + 1 < r₃`, the form proved here implies the plan's form, because
   `A_σ(r₂, r₃) ⊆ A_σ(r₂ + 1, r₃)` by monotonicity. The gap is unnecessary, because of I2b's sharp
   determination.
3. **The order-invariance re-export** is stated with `sbtw` and arm families (`IsArm`,
   `ArmsDisjoint`), not with the eighteen hypotheses of the PT2b form. The plan's "first-hit
   form" for arms cut at an intermediate box is obtained by cutting the arms
   (`IsArm.exists_append_eq_of_le_of_le`) and applying the same theorem to the cut family.
4. The doubled walks are **existence statements** whose supports are described pointwise. A
   walk-valued `def` would have needed an interface package.

## Not done here (A1b)

These are left for a package A1b, or for A2 where A2 needs them.

* **Nonemptiness for every `R ≥ 1`** (optional, plan item 4). Straight arms of length `R` for the
  sequences of the I2b examples; only `R = 1` is compiled.
* **A priori upper bound** (Nolin Prop. 14, upper half), `exists_law_multiArmEvent_le_rpow`. The
  event is contained in "an open (or dual) path crosses the annulus". Run P7's multi-scale
  blocking (`exists_law_armEvent_le_pow_mul`) at centre `z` from `B_r(z)`, with these changes:
  * the blocking event at scale `t` has probability at least a product of four dual long
    crossings (`CrossingBounds.le_law_dualConfig_crossing_*`, Harris for decreasing events);
  * this replaces RSW at `1/2`, and the scales are limited by `L`.

  `notMem_localConn_of_notMem_crossing` already takes a general start `a`.
* **Colour inversion at `1/2`**: `π_σ(r, R) ≤ π_{¬σ}(r + 1, R - 1)` for `r + 2 < R`. A route
  checked on paper:
  * `ω ∈ A_σ(z, r, R)` gives `dualConfig ω ∈ A_{¬σ}(z, r + 1, R - 1)`.
  * An open arm of `ω` is cut at its last visit of `Icc (z - r - 1) (z + r + 2)` and at its first
    exit from `Icc (z - R + 2) (z + R - 1)`, then translated by `-(1, 1)`. This gives a dual arm
    of `dualConfig ω` (`isDualArm_dualConfig_iff`).
  * A dual arm of `ω` is cut at its last face in `Icc (z - r - 1) (z + r + 1)` and at its first
    face outside `Icc (z - R + 2) (z + R - 2)`. This gives an open arm of `dualConfig ω`
    (`isOpenArm_dualConfig_iff`).
  * The new family is disjoint. The second vertex of an open arm always lies in
    `Icc (z - r - 1) (z + r + 2)`, so the cut open arms lie in their tails.
  * In the doubled lattice of `ω`, the new landing positions are the positions on the box
    `Icc (2(z - R') + 1) (2(z + R') + 1)` (with `R' = R - 1`) of the first exits of the old
    doubled arms from its interior. So the order comes from one more lemma: order invariance for
    walks whose supports lie in the doubled arms of a family, ending at their first exit from an
    intermediate doubled box. This is `cyclicallyOrdered_end_iff_of_pairwise_disjoint` with the
    disjointness of `IsArm.double_disjoint`.
  * The probability bound is then self-duality (`law_preimage_dualConfig_eq`, with
    `mem_multiArmEventTo_iff_of_agree` for the determination by edges of `ℤ²`).
* **Tail of the number of disjoint crossings** (Nolin Lemma 15(a)): BK for increasing events
  (`countable_profile_bk`); for dual crossings, pass to the complement.
* **Nolin Lemma 13** (FKG for locally monotone events): `prodBernoulli_harris` plus conditioning
  on the region of the other monotonicity.

The last two are used by arm separation (A2). Their statements should be fixed with A2's
exploration in view.

## Search

* **mathlib.**
  * Walks: `takeUntil`/`dropUntil` split at a vertex, not at a set. Nothing splits a walk at a
    first exit from a set or a last visit to a set, so the two inductive lemmas are new.
  * Mathlib has `snd_reverse`, `penultimate_reverse`, `snd_cons`, `penultimate_cons_of_not_nil`,
    `getVert_append`, `support_append_eq_support_dropLast_append`, `tail_support_append`,
    `darts_reverse`, `map_fst_darts`, `map_snd_darts`, `dart_fst_mem_support_of_mem_darts` and
    `dart_snd_mem_support_of_mem_darts`, all used. It has no `snd_append` and no
    `penultimate_append` (both added here as `snd_append_of_not_nil`,
    `penultimate_append_of_not_nil`).
  * Independence: none needed beyond PercLib's.
* **PercLib.** Several lemmas are reused:
  * `exists_append_eq_of_mem` (PT2b) gives a first hit, but without "the hit vertex appears only
    at the end". The first-exit lemma here gives "all vertices before the last are in `T`".
  * Also reused: `cyclicallyOrdered_end_iff_of_pairwise_disjoint`, `exists_pos_le_law_crossing`,
    `law_preimage_dualConfig_eq`, `prodBernoulli_inter_of_determined` and all of I2b's arm API.

  No doubled-lattice construction existed. PT2b's note planned it for here.

## Sources

P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
no. 55, §3.1 (crossing bounds, p. 1570) and §4.1–4.2 (arm events, quasi-multiplicativity,
pp. 1572–1576). The proofs here derive these facts from PercLib's order invariance and
determination lemmas. They do not follow the text.
