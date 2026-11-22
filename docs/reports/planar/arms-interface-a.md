# Box boundaries, perimeter positions and crossing bounds: advice for the wiki

Advice for the wiki agent on package I2a of the arms plan, the first **interface** package of
the arms stage: three definitions, `boxBoundary`, `perimeterPos` and `CrossingBounds`, with their
API, added to `PercLib/Models/Planar/Arms/Defs.lean` (the file of I1's `armEvent` and
`fourStrip`). Nothing here proves an assertion of the wiki. The definitions are the vocabulary of
the later arm packages: quad duality and interlacing, the multi-arm events, arm separation and
quasi-multiplicativity. Every declaration uses only `propext`, `Classical.choice` and
`Quot.sound`; no `…Input` is used and no `@[tag]` was added.

The file still imports only `PercLib/Models/Planar/Defs.lean` and files already on `main`, not
the planar proof files, so it can go into the planar definitions pull request together with
`Planar/Defs.lean`.

## Conventions

As in `arm-events.md`: the lattice is `zdGraph d = SimpleGraph.hasse (Fin d → ℤ)`, a
configuration is a `Set (Sym2 (LatticeSite d))` with law `law q = prodBernoulli q`, boxes are
`Set.Icc lo hi` for the product order, and `crossing 0` / `crossing 1` are left-right /
bottom-top crossings inside a box of `ℤ²`. For `r : ℕ`, `(r : LatticeSite d)` is the constant
vector `r`. A dual vertex `f` of `ℤ²` stands for the unit face with lower-left corner `f`, and
`dualConfig ω` opens the dual edge crossing each closed edge of `ω` (see `duality.md`).

## The definitions

**Boundary of a box** (`boxBoundary`, any dimension `d`):

```lean
def boxBoundary (lo hi : LatticeSite d) : Set (LatticeSite d) :=
  {v | v ∈ Icc lo hi ∧ ∃ i, v i = lo i ∨ v i = hi i}
```

In words: the points of the box with some coordinate at an end of its range. In dimension `0` it
is empty; for a one-point box it is the point (`boxBoundary_self`, `d ≥ 1`).

**Perimeter position** (`perimeterPos`, on `ℤ²`):

```lean
def perimeterPos (lo hi v : LatticeSite 2) : ℤ :=
  if v 1 = lo 1 then v 0 - lo 0
  else if v 0 = hi 0 then (hi 0 - lo 0) + (v 1 - lo 1)
  else if v 1 = hi 1 then (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 0 - v 0)
  else 2 * (hi 0 - lo 0) + (hi 1 - lo 1) + (hi 1 - v 1)
```

In words: for a point `v` of the boundary of the box, its distance from the lower-left corner
`lo` along the boundary, counterclockwise. The bottom side, both corners included, has positions
`0` to `w = hi₀ - lo₀`; the right side above the lower-right corner has `w + 1` to `w + h`
(`h = hi₁ - lo₁`); the top side left of the upper-right corner has `w + h + 1` to `2w + h`; the
left side strictly between its corners has `2w + h + 1` to `2w + 2h - 1`. Each corner other than
`lo` belongs to the side that ends at it. Off the boundary the value has no meaning. On the unit
square the corners `(0,0), (1,0), (1,1), (0,1)` have positions `0, 1, 2, 3` (a compiled
`example`). The counterclockwise cyclic order of boundary points is the cyclic order of their
positions, which is mathlib's `CircularOrder ℤ` (`Int.sbtw_iff`); no new order is defined.

**Crossing bounds** (`CrossingBounds`, on `ℤ²`):

```lean
structure CrossingBounds (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞) (c : ℕ → ℝ≥0∞) :
    Prop where
  pos : ∀ k, 0 < c k
  le_law_crossing : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n → (n : ℕ∞) ≤ L →
    c k ≤ law q (crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]))
  le_law_dualConfig_crossing : ∀ (k : ℕ) (i : Fin 2) (lo : LatticeSite 2) (n : ℕ), 1 ≤ n →
    (n : ℕ∞) ≤ L →
    c k ≤ law q (dualConfig ⁻¹'
      crossing i lo (lo + if i = 0 then ![(k : ℤ) * n, n] else ![(n : ℤ), k * n]))
```

In words: under `law q`, for every aspect ratio `k`, every box of size `k n × n` with
`1 ≤ n ≤ L`, in either orientation and at any position, is crossed in its long direction with
probability at least `c k > 0`, both by open edges and by dual-open edges. Direction `i = 0` is
the box `[lo, lo + (kn, n)]` crossed left to right, `i = 1` the box `[lo, lo + (n, kn)]` crossed
bottom to top; for the dual crossing the box is a box of faces. `L : ℕ∞`, so `L = ⊤` means every
scale. Because positions are quantified, the profile `q` need not be translation invariant.

## How they match the wiki and the sources

**`∂Λ_r` of BLNL** (`critical-exponents`, "Euclidean one-arm and two-point exponent
conventions"). BLNL writes `∂Λ_r = {x : ‖x‖∞ = r}`. In Lean this is
`boxBoundary (0 - r) (0 + r)`, and `boxBoundary_sub_add_eq_sphere` states, for any centre `x` and
`d ≥ 1`,

```lean
theorem boxBoundary_sub_add_eq_sphere [NeZero d] (x : LatticeSite d) (r : ℕ) :
    boxBoundary (x - r : LatticeSite d) (x + r) = Metric.sphere x r
```

with the sup metric of `Fin d → ℤ`, the companion of I1's `Site.closedBall_eq_Icc`. The one-arm
event of I1 reaches exactly this boundary: `mem_armEvent_iff_exists_mem_boxBoundary` restates
`armEvent x r` as "`x` is joined to a point of `boxBoundary (x - r) (x + r)` inside the box", and
`mem_armEvent_iff_exists_mem_boxBoundary_conn` as "… by an open path confined to no box". These
are bridges, not a redefinition: `armEvent` is unchanged, and `mem_boxBoundary_sub_add_iff` turns
its coordinate condition `v i = x i - r ∨ v i = x i + r` into `boxBoundary` membership.

**Crossing bounds** (Nolin 2008, Section 3.1, as located by the arms plan; the plan's §1.4).
Nolin proves arm separation and quasi-multiplicativity for every law whose crossing
probabilities of both colours in `k n × n` boxes are bounded below uniformly up to the
characteristic length. `CrossingBounds q L c` is that hypothesis, with `L` the scale up to which
it holds. At `1/2` it holds with `L = ⊤` by RSW; that witness needs the RSW proofs and will be a
theorem of a later proof package (planned name `exists_crossingBounds_half`), not part of this
interface file. No wiki assertion uses `CrossingBounds` yet; if a tagged statement of the arm
stage takes it as a hypothesis, the binder table should class each field as SOURCE (Nolin's
standing assumption) and the auditor should check that the tagged statement also has a
non-vacuity witness at `1/2`.

**Perimeter positions** are not a wiki notion. They give the counterclockwise order of arm
endpoints on a box, which the planned multi-arm events use to say that arms land in
counterclockwise order.

## API, by role

Boundary of a box (namespace `PercLib.Models.Planar`, any `d` unless noted):

| Role | Declaration |
|---|---|
| membership | `mem_boxBoundary_iff`; on `ℤ²`, coordinate by coordinate, `mem_boxBoundary_two_iff` |
| inside the box | `boxBoundary_subset_Icc` |
| box minus the box one step inside it | `boxBoundary_eq_Icc_diff_Icc` (`Icc lo hi \ Icc (lo + 1) (hi - 1)`) |
| trivial case (simp, `[NeZero d]`) | `boxBoundary_self` (`= {v}`) |
| corners on the boundary (`[NeZero d]`) | `left_mem_boxBoundary`, `right_mem_boxBoundary` (`lo ≤ hi`) |
| translation | `add_mem_boxBoundary_add_iff` (simp), `image_add_const_boxBoundary` |
| quarter turn (`ℤ²`, simp) | `rotate_mem_boxBoundary_iff`: `(x, y) ↦ (-y, x)` maps the boundary of `Icc lo hi` onto that of `[-hi₁, -lo₁] × [lo₀, hi₀]` |
| bridge to the one-arm event | `mem_boxBoundary_sub_add_iff`, `mem_armEvent_iff_exists_mem_boxBoundary`, `mem_armEvent_iff_exists_mem_boxBoundary_conn` |
| bridge to the sup-metric sphere (`[NeZero d]`) | `boxBoundary_sub_add_eq_sphere` |

Perimeter positions (`ℤ²`):

| Role | Declaration |
|---|---|
| values on each side | `perimeterPos_of_bottom`, `perimeterPos_of_right`, `perimeterPos_of_top`, `perimeterPos_of_left` (hypotheses are the `if` conditions) |
| lower-left corner (simp) | `perimeterPos_self : perimeterPos lo hi lo = 0` |
| nonnegative | `perimeterPos_nonneg` (any point of the box) |
| bound by the perimeter | `perimeterPos_lt` (`lo ≠ hi`, any point of the box) |
| injective on the boundary | `perimeterPos_injOn` (no hypothesis: also for segments and points) |
| translation (simp) | `perimeterPos_add` |
| quarter turn | `perimeterPos_rotate` (`lo₀ < hi₀`, `lo₁ < hi₁`): the position in the turned box is `(perimeterPos lo hi v + (hi₁ - lo₁)) % (2(hi₀ - lo₀) + 2(hi₁ - lo₁))` |

Crossing bounds:

| Role | Declaration |
|---|---|
| fields | `pos`, `le_law_crossing`, `le_law_dualConfig_crossing` |
| the four orientations without the `if` | `CrossingBounds.le_law_crossing_zero`, `le_law_crossing_one`, `le_law_dualConfig_crossing_zero`, `le_law_dualConfig_crossing_one` |
| monotonicity (smaller `L`, smaller positive `c`) | `CrossingBounds.mono` |
| translation | `CrossingBounds.translate`: bounds for `q` give bounds for `e ↦ q (e + a)` |
| trivial case | `crossingBounds_zero` (`L = 0`, any positive `c`) |

General helpers added to the same file: `image_add_mem_crossing_iff` (any `d`: translating the
configuration and the box carries crossings), and `dualConfig_image_add` (the dual configuration
commutes with translations). `image_add_mem_crossing_iff` was a local `have` inside I1's
`image_add_mem_fourStrip_iff`, which now uses the lemma; its statement is unchanged.

Compiled `example`s (D-5 and sanity): the corner `(0, 2)` of `[0, 2]²` is on its boundary and
the centre `(1, 1)` is not; the positions `0, 1, 2, 3` around the unit square; and
`CrossingBounds q 0 (fun _ => 1)` for every `q` (the trivial witness).

## Choices, compared with the plan

- Field names: the plan's `open_le` and `dual_le` are `le_law_crossing` and
  `le_law_dualConfig_crossing` (names describe the conclusion). The dual event is spelt
  `dualConfig ⁻¹' crossing …` (the library's spelling elsewhere) instead of the plan's
  `{ω | dualConfig ω ∈ crossing …}`; the two are the same set by definition.
- Injectivity of `perimeterPos` on the boundary needs no hypothesis (the plan asked for
  `lo < hi`). The perimeter bound needs only `lo ≠ hi` and holds on the whole box, not only on
  its boundary. Nonnegativity holds on the whole box.
- The quarter-turn lemma is stated with the turn written out, `![-v 1, v 0]`, as P1 wrote its
  swap and reflections; no rotation map is defined. It needs positive width and height: on a
  segment the positions run along it once, and a quarter turn reverses them.
- `CrossingBounds.translate` is at the law level. It uses `prodBernoulli_map_image_sym2`
  (`Probability/Transport/Reindexing.lean`, on `main`) and `map_image_sym2Map_apply`
  (`Bond/Transport.lean`), so it needs no planar proof file.
- Added beyond the plan: the sphere bridge, `boxBoundary_eq_Icc_diff_Icc`, the corner lemmas,
  `mem_boxBoundary_two_iff`, `rotate_mem_boxBoundary_iff`, the four orientation accessors, and
  the two translation helpers.
- Only the trivial `L = 0` witness of `CrossingBounds` is here, as planned.
- At pull-request preparation, `image_add_mem_crossing_iff` and `dualConfig_image_add` could move
  to `Planar/Defs.lean`, next to `crossing` and `dualConfig`. `SelfDuality.lean`'s
  `image_mem_crossing_iff` (any automorphism, a proof file) has the translation case as a special
  case. It needs a graph isomorphism, and this file may not import it.

## Search before defining

PercLib (this branch): no box boundary, sphere, perimeter, cyclic-order or crossing-bounds notion
(searched `boundary`, `perimeter`, `sphere`, `cyclic`, `circular`, `CrossingBound` among
definitions; the hits `boundarySusceptibility` and `boundaryFlux` are unrelated). No translation
lemma for `dualConfig` (only `dualConfig_image_swap` in `CrossingSymmetry.lean`) and no
stand-alone translation lemma for `crossing` (only the general `image_mem_crossing_iff` in
`SelfDuality.lean`, a proof file). Mathlib: `Cube.boundary` (`Topology/Homotopy/HomotopyGroup.lean`)
is the same idea for the real unit cube `I^N`, not lattice boxes; `Polygon.boundary` and manifold
boundaries are unrelated; there is no lattice box boundary. Mathlib's circular orders
(`Order/Circular.lean`, `CircularOrder ℤ` in `Order/Circular/ZMod.lean`) order integers, so
`perimeterPos` composes with them and does not duplicate them. Mathlib lemmas used: `sphere_pi`
(sup-metric spheres of products), `Int.dist_eq`, `abs_eq`, `Int.cast_injective`,
`Int.emod_eq_of_lt`, `Int.add_emod_right`, `Equiv.addRight_symm`, `Sym2.map.injective`. Library lemmas
reused: `prodBernoulli_map_image_sym2`, `map_image_sym2Map_apply`, `dualEdge_map_add`,
`map_add_mem_edgeSet`, `mem_dualConfig_iff'`, `mem_Icc_two_iff`, and I1's
`Site.closedBall_eq_Icc` and `image_add_inter_edgeSet_mem_localConn_iff`.
