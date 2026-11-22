# Arm events and the four-strip event: advice for the wiki

Advice for the wiki agent on package I1 of the RSW plan, the **interface** package of the arm
stage: two definitions, `armEvent` and `fourStrip`, with their API, in
`PercLib/Models/Planar/Arms/Defs.lean`. Nothing here proves an assertion of the wiki: the one-arm
bounds (XB1U), the two-point comparison (Y8K3) and the lower half of the three-point bound
(K8A1) come in the proof packages P6–P8, which state their events with these two definitions.
Every declaration uses only `propext`, `Classical.choice` and `Quot.sound`; no `…Input` is used
and no `@[tag]` was added.

The file imports only `PercLib/Models/Planar/Defs.lean` and files already on `main`, not the
planar proof files, so it can go into the planar definitions pull request on its own. The
arm-stage files go in the folder `PercLib/Models/Planar/Arms/`: `Defs.lean` (this package),
then `Separator.lean` (P6), `OneArm.lean` (P7), `TwoPoint.lean` and `ThreePoint.lean` (P8).

## Conventions

As in `duality.md`: the lattice is `zdGraph d = SimpleGraph.hasse (Fin d → ℤ)`, a configuration
is a `Set (Sym2 (LatticeSite d))` with law `law q = prodBernoulli q`, boxes are `Set.Icc lo hi`
for the product order, and `crossing 0` / `crossing 1` are left-right / bottom-top crossings
inside a box of `ℤ²`. For `r : ℕ`, `(r : LatticeSite d)` is the constant vector `r`, so
`Set.Icc (x - r) (x + r)` is the box `x + [-r, r]^d`. Both events read only the
nearest-neighbour pairs `ω ∩ (zdGraph d).edgeSet`, so the profile `q` off the edges is
arbitrary for them.

## The definitions

**One-arm event** (`armEvent`, any dimension `d`):

```lean
def armEvent (x : LatticeSite d) (r : ℕ) : Set (Config (LatticeSite d)) :=
  {ω | ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
    ω ∩ (zdGraph d).edgeSet ∈ localConn (Icc (x - r) (x + r)) x v}
```

In words: the centre `x` of the box `B_r(x) = x + [-r, r]^d` is joined to a point `v` of the
boundary of the box (a point of the box with some coordinate at distance exactly `r` from `x`,
that is `‖v - x‖∞ = r`) by a path of open nearest-neighbour edges all of whose vertices lie in
the box. It is an event on the edges inside the box. For `r = 0` it is every configuration
(`armEvent_zero`, in dimension `d ≥ 1`); in dimension `0` the box has no boundary and the event
is empty.

**Four-strip event** (`fourStrip`, on `ℤ²`):

```lean
def fourStrip (z : LatticeSite 2) (n : ℕ) : Set (Config (LatticeSite 2)) :=
  crossing 0 (z + ![-4 * (n : ℤ), 2 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∩
  crossing 0 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), -2 * n]) ∩
  crossing 1 (z + ![2 * (n : ℤ), -4 * n]) (z + ![4 * (n : ℤ), 4 * n]) ∩
  crossing 1 (z + ![-4 * (n : ℤ), -4 * n]) (z + ![-2 * (n : ℤ), 4 * n])
```

In words, all translated by `z`: a left-right open crossing of the top strip
`[-4n, 4n] × [2n, 4n]` and of the bottom strip `[-4n, 4n] × [-4n, -2n]`, and a bottom-top open
crossing of the right strip `[2n, 4n] × [-4n, 4n]` and of the left strip
`[-4n, -2n] × [-4n, 4n]`. All four strips lie in the annulus `2n ≤ ‖v - z‖∞ ≤ 4n`.

## How they match the wiki

**π(r) of BLNL** (`critical-exponents`, "Euclidean one-arm and two-point exponent
conventions"). BLNL sets `Λ_r = [-r, r]^d ∩ ℤ^d`, `∂Λ_r = {x : ‖x‖∞ = r}` and
`π(r) = P_{p_c}(o ↔ ∂Λ_r)` for nearest-neighbour percolation. In Lean this is
`law q (armEvent 0 r)` (or `(law q).real (armEvent 0 r)`), with `q` equal to `p_c` on the edges
of `ℤ^d`:

- `Λ_r` is `Set.Icc (0 - r) (0 + r)`; the bridge `Site.closedBall_eq_Icc` identifies the box
  `Set.Icc (x - r) (x + r)` with `Metric.closedBall x r` for the sup metric of `Fin d → ℤ`, if a
  tagged statement prefers mathlib's ball.
- The wiki's `o ↔ ∂Λ_r` uses open paths that may leave the box. The definition confines the path
  to the box, and `mem_armEvent_iff_exists_conn` shows the two agree for every configuration:

  ```lean
  theorem mem_armEvent_iff_exists_conn {x : LatticeSite d} {r : ℕ} {ω : Config (LatticeSite d)} :
      ω ∈ armEvent x r ↔ ∃ v ∈ Icc (x - r) (x + r), (∃ i, v i = x i - r ∨ v i = x i + r) ∧
        ω ∩ (zdGraph d).edgeSet ∈ conn x v
  ```

  For a configuration of nearest-neighbour edges (`ω ⊆ (zdGraph d).edgeSet`),
  `mem_armEvent_iff_exists_conn_of_subset` drops the `∩ (zdGraph d).edgeSet`. The proof stops
  the path on first reaching the boundary (`mem_armEvent_of_mem_conn`, from the library's
  `exists_first_exit`).
- BLNL's remark on long-range models: `armEvent` reads only nearest-neighbour edges, so it is
  the nearest-neighbour arm event. A long-range model needs its own spatial arm event, as the
  wiki says; `armEvent` is not that event.
- BLNL takes `r` a positive integer; `armEvent x 0` is defined and is everything in `d ≥ 1`.

**A(r) of XB1U** (`critical-exponents`, "Extending an arm and blocking it"). XB1U writes
`B_r(x) = x + [-r, r]² ∩ ℤ²`, `A(r) = P_{1/2}(0 ↔ ∂B_r)` and adds that the arm can be stopped
on first reaching the boundary, so `A(r)` is an event on the edges inside `B_r`. That is
`armEvent 0 r` on `ℤ²` read at `1/2`, and the sentence about stopping is exactly
`mem_armEvent_iff_exists_conn`. The planned form of XB1U (plan, section 2.7) uses
`(law q).real (armEvent 0 r)` with `q` equal to `1/2` on the edges of `ℤ²`; `p_c = 1/2` is the
P5 result `rootCriticalIntensity_indicator_edgeSet_eq_log_two` (see `critical-probability.md`).

**The circuit of XB1U's proof.** XB1U's proof asks for horizontal crossings of
`[-4n, 4n] × [2n, 4n]` and `[-4n, 4n] × [-4n, -2n]` and vertical crossings of
`[2n, 4n] × [-4n, 4n]` and `[-4n, -2n] × [-4n, 4n]`: these are the four crossings of
`fourStrip 0 n`, with the same strips (the inner line `‖·‖∞ = 2n` included). The wiki then
extracts a simple open circuit in `B_{4n} ∖ B_{2n-1}`; the Lean never extracts it. P6 will prove
that on `fourStrip z n` every open arm crossing the annulus is joined to the four crossings
inside `B_{4n}(z)` (circuit gluing), and that `fourStrip z n` has probability at least a
constant `c₀ > 0` at `1/2` (the wiki's "constant `c₀`, independent of `n`, for the event
`C_n`"). The note for P6 will say how those statements read. For FAT3 (`multipoint-trees`), the
plan's advice stands: restating its circuit hypothesis with `fourStrip`, or with "an open
connected set in the annulus meeting every path across it", would let the planar packages
discharge it.

## API, by role

One-arm event (namespace `PercLib.Models.Planar`):

| Role | Declaration |
|---|---|
| membership | `mem_armEvent_iff` |
| reads only nearest-neighbour edges (simp) | `inter_edgeSet_mem_armEvent_iff` |
| increasing event | `armEvent_mono`, `isUpperSet_armEvent` |
| measurable | `measurableSet_armEvent` |
| trivial case `r = 0` | `mem_armEvent_zero` (given a coordinate `i`), `armEvent_zero` (simp, `[NeZero d]`) |
| decreasing in the radius | `armEvent_anti : Antitone (armEvent x)` |
| stopping at the first boundary hit | `mem_armEvent_of_mem_conn` |
| bridge to `x ↔ ∂B_r(x)` | `mem_armEvent_iff_exists_conn`, `mem_armEvent_iff_exists_conn_of_subset` |
| escape form | `mem_armEvent_iff_exists_notMem_conn`: an open path to some `y ∉ Icc (x - r + 1) (x + r - 1)` |
| determined by the pairs inside the box | `mem_armEvent_iff_of_inter_eq` (any `T ⊇` box) |
| translation | `image_add_mem_armEvent_iff`, `preimage_image_add_armEvent` |
| non-vacuity | `empty_notMem_armEvent` (`1 ≤ r`), `univ_mem_armEvent` (`[NeZero d]`) |

Four-strip event:

| Role | Declaration |
|---|---|
| membership | `mem_fourStrip_iff` (the four crossings) |
| reads only nearest-neighbour edges (simp) | `inter_edgeSet_mem_fourStrip_iff` |
| increasing event | `fourStrip_mono`, `isUpperSet_fourStrip` |
| measurable | `measurableSet_fourStrip` |
| determined by the pairs inside the annulus | `mem_fourStrip_iff_of_inter_eq` (any `T` containing `2n ≤ ‖v - z‖∞ ≤ 4n`, written with coordinate inequalities) |
| translation | `image_add_mem_fourStrip_iff` |
| non-vacuity | `univ_mem_fourStrip` |

General helpers in the same file: `Bond.inter_mem_localConn_iff_of_inter_eq` (a connection
inside `S` is determined by the pairs inside any `T ⊇ S`),
`image_add_inter_edgeSet_mem_localConn_iff` (translations carry connections inside a set),
`edgeSet_mem_localConn_Icc` (any two points of a box of `ℤ^d` are joined by nearest-neighbour
edges inside it), `Site.closedBall_eq_Icc`, `Site.apply_le_apply_add_one_of_adj`.

The determination lemmas have the shape the independence lemmas of
`PercLib/Percolation/Bond/DomainIndependence.lean` take
(`law_inter_of_determined_internalPairs`, `law_biInter_of_determined_internalPairs`); P7 will use
them for the arm inside `B_r` and the four-strip events in disjoint annuli.

Compiled `example`s (D-5): `∅ ∉ armEvent 0 1` and `univ ∈ armEvent 0 1` in `ℤ²`;
`univ ∈ fourStrip z 1` and `∅ ∉ fourStrip z 1` for every `z`.

## Choices, compared with the plan

- File: `PercLib/Models/Planar/Arms/Defs.lean`, not `Planar/Defs.lean` (the user's choice; the
  plan allowed a later move).
- `armEvent` stays on `ℤ^d` (the generality is free and BLNL is on `ℤ^d`); `fourStrip` is on
  `ℤ²`.
- Radius monotonicity is `armEvent_anti` (`Antitone`, as `dualConfig_anti`), not
  `armEvent_mono_radius`; `armEvent_mono` is monotonicity in the configuration.
- The bridges are stated for every `ω`, through `ω ∩ (zdGraph d).edgeSet`; the plan's
  "for `ω ⊆ L`" form is `mem_armEvent_iff_exists_conn_of_subset`.
- The escape form uses the box `Icc (x - r + 1) (x + r - 1)` (the box of radius `r - 1` when
  `r ≥ 1`, empty when `r = 0`), so it holds for every `r` instead of only `r ≥ 1`.
- Translation is stated for configurations. The law-level form (the arm probability does not
  depend on `x` when `q` is translation invariant on edges) needs the law symmetry
  `law_preimage_image_sym2Map_eq` of `SelfDuality.lean`, a proof file, and is left to the proof
  packages; `preimage_image_add_armEvent` is the form that lemma takes.
- `armEvent_zero` needs `[NeZero d]`, since in dimension `0` the event is empty.

## Search before defining

PercLib (this branch and Tom's current `main`): no arm event on `ℤ^d`, no four-strip or
annulus event, no sup-norm sphere notion (searched `arm`, `strip`, `annul`, `sphere`, `boundary`,
`escape`, `box` among definitions; `BinaryTreeArm.lean` is about trees). Escape events are
written inline as `⋃ y ∈ Fᶜ, conn x y` (`OpenEventHarris.lean`), without the restriction to the
box. Mathlib has no percolation arm events; for the ball bridge it has `closedBall_pi`,
`Int.closedBall_eq_Icc` and `Set.pi_univ_Icc`, which the proof uses. Library lemmas reused:
`exists_first_exit` (`Bond/FirstExit.lean`), `localConn_of_image` (`Bond/FiniteSetCriterion.lean`),
`localConn_iff_of_agree` (`Bond/LocalConnectivity.lean`), `image_sym2Map_symm_image`
(`Bond/Transport.lean`), `zdGraph_adj_iff_exists`, `zdGraph_adj_iff_of_sub`,
`zdGraph_adj_iff_eq_update` (`Models/Lattice.lean`), and `crossing` with its API from
`Planar/Defs.lean`.
