# Arms, multi-arm events and landing data: advice for the wiki

Advice for the wiki agent on package I2b of the arms plan. I2b is the second **interface**
package of the arms stage. It adds to `PercLib/Models/Planar/Arms/Defs.lean` the arm events that
arm separation, quasi-multiplicativity and the universal arm exponents are stated with:

* open and dual arms;
* disjoint families of arms;
* positions of arms on a boundary;
* the multi-arm events, in the plane and in the half-plane;
* landing data.

Each comes with its API and compiled non-vacuity examples. Nothing here proves an assertion of
the wiki. Every declaration uses only `propext`, `Classical.choice` and `Quot.sound`. No
`…Input` is used and no `@[tag]` was added.

The file still imports only `PercLib/Models/Planar/Defs.lean`, files already on `main`, and
mathlib. The one new import is `Mathlib.Order.Circular.ZMod`, for the circular order of `ℤ`. So
the file can go into a planar definitions pull request. Three small lemmas about faces moved here
unchanged from the proof file `Arms/QuadDuality.lean` (see "Choices").

## Conventions

As in `arms-interface-a.md` and the quad-duality notes:

* A point of `ℤ²` is `![x, y]`, boxes are `Set.Icc lo hi`, and `(r : LatticeSite 2)` is the
  constant vector `r`. So `B_r(z) = Icc (z - r) (z + r)`, and `Icc (lo + 1) (hi - 1)` is the
  interior of the box `Icc lo hi`.
* A **face** is a dual vertex: `f` stands for the unit square with lower-left corner `f`. The
  faces inside `Icc lo hi` form `Icc lo (hi - 1)`. The faces touching `B_r(z)` (with a corner in
  it) form `Icc (z - r - 1) (z + r)`.
* `dualConfig ω` opens the dual edge across each closed edge of `ω`.
* `perimeterPos lo hi v` is I2a's counterclockwise position on the boundary of `Icc lo hi`.
* Three integers are in **counterclockwise order** when `sbtw a b c`. This is mathlib's strict
  cyclic betweenness for the instance `CircularOrder ℤ` in `Mathlib.Order.Circular.ZMod`. By
  definition (`Int.sbtw_iff`, proved by `rfl`) it is the disjunction
  `a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b` that the order-invariance theorems of PT2b
  write out.

## The definitions

**Crossing walks** (`SimpleGraph.Walk.IsCrossing`, for any graph):

```lean
structure IsCrossing (S T : Set V) {u v : V} (p : G.Walk u v) : Prop where
  start_mem : u ∈ S
  notMem_of_mem_tail : ∀ w ∈ p.support.tail, w ∉ S
  end_notMem : v ∉ T
  mem_of_mem_dropLast : ∀ w ∈ p.support.dropLast, w ∈ T
```

In words: the walk starts in `S` and never returns to `S`. It stays in `T` up to its last
vertex, which is outside `T`. For a box `S` inside a box `T`, this is a crossing of the annulus
between them that stops when it first leaves `T`.

**Open arms** (`IsOpenArm ω z r lo hi γ`, for a walk `γ` of `ℤ²`):

```lean
structure IsOpenArm (ω) (z) (r : ℕ) (lo hi) {a b} (γ : (zdGraph 2).Walk a b) : Prop where
  isCrossing : γ.IsCrossing (Icc (z - r) (z + r)) (Icc (lo + 1) (hi - 1))
  mem_of_mem_edges : ∀ e ∈ γ.edges, e ∈ ω
```

In words: a path of open edges that starts in `B_r(z)` and leaves it at its first step. It stays
in the interior of the outer box `Icc lo hi` until its last vertex, so its last vertex is its
first point on the boundary of the outer box. When `B_r(z)` lies in the interior of the outer box:

* the arm starts on the boundary of `B_r(z)`;
* it lies in `Icc lo hi`;
* it meets `B_r(z)` only at its start and the outer boundary only at its end.

These are the hypotheses of the order-invariance theorems (`IsOpenArm.start_mem_boxBoundary`,
`mem_Icc`, `eq_start_of_mem`, `end_mem_boxBoundary`, `eq_end_of_mem_boxBoundary`). For `r = 0`
the box `B_0(z)` is the vertex `z`.

**Dual arms** (`IsDualArm ω z r lo hi γ`, for a walk `γ` of faces):

```lean
structure IsDualArm (ω) (z) (r : ℕ) (lo hi) {f g} (γ : (zdGraph 2).Walk f g) : Prop where
  isCrossing : γ.IsCrossing (Icc (z - r - 1) (z + r)) (Icc lo (hi - 1))
  mem_of_mem_edges : ∀ e ∈ γ.edges, e ∈ dualConfig ω
```

In words: a path of faces along dual-open dual edges. It starts at a face touching `B_r(z)` and
never touches `B_r(z)` again. It runs through faces of the outer box up to its last face, which
lies just outside the box. Its last dual edge crosses an edge of the boundary of `Icc lo hi`.
Every dual edge it uses crosses a closed edge with both ends in `Icc lo hi` and no end in
`B_r(z)` (`IsDualArm.exists_mem_edgeSet_of_mem_edges`). For `r = 0` the first face is one of the
four faces at `z`.

**Arms of a colour.** `IsArm ω c z r lo hi γ` is `IsOpenArm` for `c = true` and `IsDualArm` for
`c = false` (`cond`, with simp lemmas `isArm_true`, `isArm_false`).

**Disjoint families** (`ArmsDisjoint σ γ`, for `γ : ∀ i : Fin j, (zdGraph 2).Walk (a i) (b i)`):

```lean
def ArmsDisjoint (σ : Fin j → Bool) (γ) : Prop :=
  (∀ i k, i ≠ k → σ i = true → σ k = true → ∀ v ∈ (γ i).support.tail, v ∉ (γ k).support) ∧
    ∀ i k, i ≠ k → σ i = false → σ k = false → ∀ v ∈ (γ i).support, v ∉ (γ k).support
```

In words: two open arms share no vertex, except possibly their first one. Two dual arms share no
face. An open arm and a dual arm of one configuration never cross, so nothing is required of
them.

**Positions** (`innerPos`, `landingPos`). Positions live on the **doubled lattice**:

* a point `v` becomes `2v`;
* a face `f` becomes its centre `2f + (1, 1)`;
* an edge becomes its midpoint, the sum of its ends.

```lean
def innerPos (z) (r : ℕ) (c : Bool) {a b} (γ) : ℤ :=
  perimeterPos (2 • z - ((2 * r + 1 : ℕ) : LatticeSite 2))
    (2 • z + ((2 * r + 1 : ℕ) : LatticeSite 2)) (cond c (a + γ.snd) (2 • a + 1))
def landingPos (lo hi) (c : Bool) {a b} (γ) : ℤ :=
  perimeterPos (2 • lo) (2 • hi) (cond c (2 • b) (γ.penultimate + b + 1))
```

In words:

* **Inner position.** This is a position on the boundary of the doubled box
  `2z + [-(2r + 1), 2r + 1]²`, of perimeter `16r + 8`. That box sits halfway between `B_r(z)`
  and the faces around it. For an open arm the position is that of the midpoint of its first
  edge; for a dual arm, that of the centre of its first face.
* **Landing position.** This is a position on the boundary of `Icc (2 lo) (2 hi)`. For an open
  arm it is that of twice its last vertex: `landingPos_true` gives `2 · perimeterPos lo hi b`.
  For a dual arm it is that of the midpoint of the boundary edge crossed by its last dual edge,
  which is the sum of its last two faces plus `(1, 1)`. If that edge runs from `x` to the next
  point counterclockwise, the position is `2 · perimeterPos lo hi x + 1`.

So the arms of both colours land on one cycle. For a centred outer box `B_R(z)` its perimeter is
`16R`.

**Multi-arm events.**

```lean
def multiArmEventTo (σ : Fin j → Bool) (z) (r : ℕ) (lo hi) (J I : Fin j → Set ℤ) :
    Set (Config (LatticeSite 2)) :=
  {ω | ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, IsArm ω (σ i) z r lo hi (γ i)) ∧ ArmsDisjoint σ γ ∧
    (∀ i, innerPos z r (σ i) (γ i) ∈ J i ∧ landingPos lo hi (σ i) (γ i) ∈ I i) ∧
    ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i))
      (landingPos lo hi (σ k) (γ k)) (landingPos lo hi (σ l) (γ l))}
abbrev multiArmEventIn σ z r R J I := multiArmEventTo σ z r (z - R) (z + R) J I
abbrev multiArmEvent σ z r R := multiArmEventIn σ z r R (fun _ => univ) (fun _ => univ)
```

In words: a disjoint family of `j` arms from `B_r(z)` to the boundary of `Icc lo hi`, where:

* arm `i` is open if `σ i` and dual otherwise;
* its inner position lies in the window `J i` and its landing position in the window `I i`;
* the arms land in counterclockwise order.

`multiArmEvent σ z r R` is the event `A_σ(r, R)` of the sources, centred at `z`.

The half-plane events `halfArmEventTo`, `halfArmEventIn` and `halfArmEvent` have the same
arguments and two changes. Every arm stays in `{v | z 1 ≤ v 1}`: the vertices of an open arm and
the lower-left corners of the faces of a dual arm. The landing positions increase with `i`
(`StrictMono`). When the outer box reaches below the line (`lo 1 < z 1`, as for `B_R(z)` with
`R ≥ 1`), the part of its boundary in the half-plane runs counterclockwise from its right end to
its left end. So the arms are ordered from the right.

**Landing data.**

```lean
structure IsLanding (η : ℚ) (θ : Fin j → ℚ) : Prop where
  pos : 0 < η
  nonneg : ∀ i, 0 ≤ θ i
  add_le_one : ∀ i, θ i + η ≤ 1
  add_two_mul_le : ∀ i k, i < k → θ i + 2 * η ≤ θ k
  add_two_mul_le_add_one : ∀ i k, θ i + 2 * η ≤ θ k + 1
def window (P : ℕ) (θ : Fin j → ℚ) (η : ℚ) (i : Fin j) : Set ℤ :=
  {p | θ i * P ≤ p ∧ (p : ℚ) ≤ (θ i + η) * P}
```

In words: landing data are `j` windows `[θ i, θ i + η]` of the circle `[0, 1)`, measured in
fractions of a turn. They lie inside `[0, 1]`, in counterclockwise order, with a gap of at least
`η` between consecutive windows and between the last and the first around the circle.
`window P θ η i` is the set of positions of a cycle of perimeter `P` in window `i`. Landing
windows on `B_R(z)` are `window (16 * R) θ η`; inner windows on `B_r(z)` are
`window (16 * r + 8) θ' η`.

## How they match the wiki and the sources

**Arm events** (Nolin 2008, §4.1, p. 1572; half-plane arm events §4.6, p. 1586). In Nolin,
`A_{j,σ}(n, N)` is the event that `j` disjoint arms of colours `σ`, in counterclockwise order,
cross the annulus between `B_n` and `B_N`. On the square lattice the arms are open paths of `ℤ²`
and closed paths of the dual lattice. `multiArmEvent σ z r R` is that event at `z`. The sources do
not fix how arms meet the two boundaries; the choices made here are listed below. They change
each event only by a bounded amount, which the comparison results absorb. No wiki assertion uses
the events yet. If a tagged statement of the arms stage does, the binder table should class:

* `σ`, `r`, `R` (and `z`) as SOURCE;
* the windows `J`, `I` as SOURCE for the statements with landing areas (Nolin's Theorem 11,
  p. 1576);
* `lo`, `hi` as SOURCE only for the non-centred forms (Nolin's Lemma 25, p. 1592).

**Landing sequences** (Nolin §4.2–4.3, pp. 1573–1576: landing areas, used by Theorem 11 and
Remark 10). `IsLanding η θ` is the separated form with windows of length exactly `η`. Nolin's
landing sequences, with intervals of length at least `η`, contain such windows. Monotonicity in
the windows (`multiArmEventTo_mono`) transfers lower bounds.

**The one-arm event.** `multiArmEvent_true_eq_armEvent` states
`multiArmEvent ![true] z 0 R = armEvent z R`. So I1's one-arm event, and every result about it
(the one-arm bounds of P7, the incipient infinite cluster of F1–F4), is the case of one open arm
from the centre.

## API, by role

Arms (namespace `PercLib.Models.Planar`, the crossing predicate in `SimpleGraph.Walk`):

| Role | Declaration |
|---|---|
| crossing walks | `isCrossing_nil_iff` (simp), `IsCrossing.not_nil`, `snd_notMem`, `penultimate_mem`, `eq_start_of_mem`, `eq_end_of_notMem`, `isCrossing_map_iff` (images by an injective homomorphism) |
| unfolding | `isOpenArm_iff`, `isDualArm_iff`, `isArm_true`, `isArm_false` (simp) |
| open arm facts | `IsOpenArm.not_nil`, `start_mem_boxBoundary`, `end_mem_boxBoundary`, `mem_Icc`, `eq_start_of_mem`, `eq_end_of_mem_boxBoundary`, `exists_notMem_of_mem_edges` |
| dual arm facts | `IsDualArm.not_nil`, `start_mem_boxBoundary` (a face of `∂Icc (z - r - 1) (z + r)`), `end_mem_boxBoundary` (a face of `∂Icc (lo - 1) hi`), `mem_Icc`, `eq_start_of_mem`, `eq_end_of_notMem`, `exists_mem_edgeSet_of_mem_edges` (crosses closed edges of the box) |
| determination | `IsOpenArm.of_agree`, `IsDualArm.of_agree`, `IsArm.of_agree` |
| translation | `IsArm.map_add`, `ArmsDisjoint.map`, `innerPos_map_add`, `landingPos_map_add` |
| one step (trivial case) | `isOpenArm_toWalk_iff`, `isDualArm_toWalk_iff`, `armsDisjoint_of_subsingleton` |
| positions | `innerPos_true`, `innerPos_false`, `landingPos_true`, `landingPos_false` (simp), `perimeterPos_two_smul` |
| colour inversion | `dualConfig_dualConfig`, `isOpenArm_dualConfig_iff`, `isDualArm_dualConfig_iff` |

Events (the half-plane versions have the same names with `halfArmEvent…`):

| Role | Declaration |
|---|---|
| membership | `mem_multiArmEventTo_iff`, `mem_multiArmEvent_iff` (without windows), `mem_halfArmEventTo_iff`, `mem_halfArmEvent_iff` |
| monotonicity in the windows | `multiArmEventTo_mono`, `multiArmEventIn_subset_multiArmEvent`, `halfArmEventTo_mono`, `halfArmEventIn_subset_halfArmEvent` |
| half-plane arms are arms | `halfArmEventTo_subset_multiArmEventTo` |
| measurability | `measurableSet_setOf_isArm`, `measurableSet_multiArmEventTo`, `measurableSet_multiArmEvent`, `measurableSet_halfArmEventTo`, `measurableSet_halfArmEvent` |
| determination by the annulus | `mem_multiArmEventTo_iff_of_agree` (edges of `Icc lo hi` with an end outside `B_r(z)`), `mem_multiArmEventTo_iff_of_inter_eq` (pairs inside any `T ⊇ Icc lo hi \ Icc (z - r + 1) (z + r - 1)`), `mem_annulus_of_mem_edgeSet`, `mem_halfArmEventTo_iff_of_agree` |
| translation | `image_add_mem_multiArmEventTo_iff`, `image_add_mem_multiArmEvent_iff`, `image_add_mem_halfArmEventTo_iff` (and the one-direction forms), `image_add_neg_image_add` |
| trivial configurations | `empty_notMem_multiArmEventTo` (some arm open), `univ_notMem_multiArmEventTo` (some arm dual) |
| one-arm bridge | `multiArmEvent_true_eq_armEvent` |

Landing data:

| Role | Declaration |
|---|---|
| membership | `mem_window_iff` |
| monotonicity in the length | `window_mono` |
| range | `IsLanding.mem_Icc_of_mem_window` (`[0, P]`) |
| disjointness | `IsLanding.disjoint_window` (`P > 0`) |
| nonempty | `nonempty_window` (`1 ≤ η P`) |
| existence | `isLanding_div`: windows `[i/j, i/j + 1/(4j)]` for every `j ≥ 1` |

General helpers: `mem_boxBoundary_of_adj` (a point of a box with a neighbour outside it is on the
boundary; any dimension) and `mem_Icc_of_adj_of_mem_Icc_sub_one`. The faces lemmas
`mem_Icc_of_mem_Icc_sub_one`, `mem_Icc_sub_one_of_mem_Icc` and `mem_Icc_of_mem_dualEdge` moved
from `QuadDuality.lean`. `Icc_sub_one_subset_iff`: `B_r(z)` is in the interior of `Icc lo hi`
exactly when the faces touching it are faces of the box.

Compiled `example`s (D-5), all from the vertex `0` at radius `1`:

* five arms open, dual, open, open, dual (the five-arm sequence);
* four alternating arms;
* the half-plane sequences open, dual and open, dual, open;
* one open arm with every edge open (from the bridge) and none with every edge closed;
* one dual arm with every edge closed and none with every edge open;
* landing data for five arms (`η = 1/20`) and a nonempty window of perimeter `80`.

## Choices, with reasons

1. **Which dual arms.** Note 5 of PT2. Dual arms cross only edges with both ends in the outer box,
   and stop at the first face outside it. Quad duality and the mixed interlacing lemma hold for
   exactly these dual paths; with all dual edges allowed, "not both" fails (PT1's
   counterexample). `IsDualArm.exists_mem_edgeSet_of_mem_edges` makes a dual arm a path for
   PT1's restricted dual configuration. The pivotal-edge arms of PT2
   (`exists_arms_of_pivotal`) use `Duality.lean`'s dual box instead. Restating them as arms needs
   a bridge, to be proved where they are used (A1 or N2).
2. **Open arms stop at their first exit.** The plan let an open arm end at any last vertex on the
   outer boundary. Here it ends at its first point on it. This is the same convention as for dual
   arms, for which it is forced, and it makes the landing point canonical. Without windows the two
   conventions should give the same event, by cutting a family at its first hits and order
   invariance; that is a theorem for A1, not proved here.
   PT2b's theorems cover both forms (`cyclicallyOrdered_end_iff`, `cyclicallyOrdered_firstHit_iff`).
3. **Leaving `B_r(z)`.** Note 1. An arm never returns to `B_r(z)` after its first vertex; the
   tail of its support avoids it. The start is on `∂B_r(z)` as soon as the arm has a step
   (`start_mem_boxBoundary`). Not returning, rather than "meets `B_r` only at the start", also
   rules out revisits of the start, which the doubled walks below need.
4. **Inner radius `0`.** Note 4. Open arms all start at `z`. Dual arms start at the four faces at
   `z`, because they start at a face *touching* `B_r(z)`. Starting inside `B_r(z)` would leave no
   dual arm at `r = 0`. Open arms may share their first vertex for every `r` (at most two share a
   corner of `B_r(z)` when `r ≥ 1`). Their tails are disjoint, and that is what order invariance
   needs once positions use the first step (item 5).
5. **Positions on the doubled lattice.** Notes 2 and 6. Landing: `2 · pos b` for an open arm and
   `2 · pos x + 1` for a dual arm, as planned. Inner: the box of radius `2r + 1` around `2z`,
   which every arm crosses at its first step. There the doubled open arm, cut after its first
   step, and the doubled dual arm both start on the boundary, meet the box nowhere else, and are
   disjoint. So mixed-colour order invariance is PT2b's theorem on the doubled lattice:
   * inner box of half-width `2r + 1`, which is positive also for `r = 0`;
   * outer box `Icc (2 lo) (2 hi)`;
   * condition `lo + 1 ≤ z - r` and `z + r + 1 ≤ hi`.

   The walk-doubling lemma is left to A1.
6. **Order by triples, with `sbtw`.** Note 3. The plan's rotation form
   `∃ k, StrictMono (pos ∘ finRotate j ^ k)` would need a combinatorial bridge to the triple
   form of order invariance. Defining the order by triples needs none: A1 re-exports
   `cyclicallyOrdered_end_iff_of_pairwise_disjoint` with `Int.sbtw_iff`. "Three positions in
   counterclockwise order" (note 7) is mathlib's `sbtw`. Correction to PT2b's note: mathlib has
   the instance `CircularOrder ℤ`, in `Mathlib.Order.Circular.ZMod`, which `Interlacing.lean`
   does not import. So nothing new was defined for it.
7. **Bundling.** Note 8. The four crossing conditions are one structure, `IsCrossing`. An arm is
   that plus open edges, `IsOpenArm`/`IsDualArm`, dispatched by colour by `IsArm`. A family is
   `∀ i, IsArm …` plus `ArmsDisjoint σ γ`. So the twenty hypotheses of the three-arm order
   theorem become three: the arms, their disjointness, and `B_r(z) ⊆ Icc (lo + 1) (hi - 1)`.
8. **Rule-4 candidates not defined here.** Note 7 lists these candidates:
   * the face on the left of a step;
   * the dual arc;
   * the arc-crossing event;
   * the restricted dual configuration;
   * interlacing of position pairs.

   They belong to the quad-duality and interlacing statements, not to the arm events. Defining
   them would mean rewriting the proof files of PT1/PT2. Defer them to a small interface package
   if relative duality (A2) states something with them.
9. **Determination is sharper than the plan's.** The events read only edges of the outer box with
   an end outside `B_r(z)`: open arms leave `B_r(z)` at their first step, and dual arms touch it
   only with their first face. So `multiArmEvent σ z r₁ r₂` (edges inside `B_{r₂}`) and
   `multiArmEvent σ z r₂ r₃` (edges with an end outside `B_{r₂}`) depend on disjoint edges.
   A1's upper half of quasi-multiplicativity can use `r₂` for both, where the plan had `r₂ + 1`.
10. **Colour inversion.** The configuration-level identity is exact:
    `dualConfig (dualConfig ω) = Sym2.map (· - 1) '' (ω ∩ edges)`. At the arm level,
    `isDualArm_dualConfig_iff` turns the dual arms of the dual configuration into open walks of
    `ω`, translated by `(1, 1)`, between boxes moved by half a lattice step. At the event level
    no equality with the same `z`, `r`, `R` is possible: the dual of a box of radius `r` has
    radius `r ± 1/2`. The comparison `π_σ ≍ π_{not ∘ σ}` needs monotonicity in the radii, which
    uses order invariance, so it belongs to A1.
11. **Windows** take the perimeter `P` of the cycle. Inner and landing positions live on cycles
    of different lengths (`16r + 8`, `16R`). The plan's `window R θ η` is `window (16 * R) θ η`.
12. **Moved lemmas.** `mem_Icc_of_mem_Icc_sub_one`, `mem_Icc_sub_one_of_mem_Icc` and
    `mem_Icc_of_mem_dualEdge` moved unchanged from `QuadDuality.lean`; the dual-arm API needs
    them, and this file may not import a proof file. The proof pull request of PT1–PT2 then needs
    this interface file first. At PR preparation they could go to `Planar/Defs.lean`, next to
    `dualEdge`. Similarly, `CrossingSymmetry.lean`'s `mem_localConn_iff_exists_walk` (used inline
    here through mathlib's `Walk.transfer` and `Walk.induce`) could move to `Bond/Basic.lean`.
    F3's `mem_boxBoundary_of_adj_of_notMem` is a special case of `mem_boxBoundary_of_adj`.

**Not done here**, left to A1:

* nonemptiness for every `R ≥ 1`, by straight arms (only `R = 1` is compiled);
* monotonicity in the radii;
* the walk-doubling lemma and mixed-colour order invariance;
* the event-level colour inversion;
* a bridge for the pivotal-edge arms.

## Search before defining

PercLib (this branch): no arm, crossing-walk, landing or window notion. The only arm definition is
I1's one-arm `armEvent`; a search of all `def`/`structure` names for `arm`, `cross`, `landing`,
`window`, `disjoint` found only `crossing` (box crossings) and the BK notions of
`DisjointOccurrence.lean`. There is no translation lemma for walks (translations are built from
`zdGraph_adj_iff_of_sub`, as in `exists_zdGraph_iso_add`).

Mathlib:

* Walk predicates `IsTrail`, `IsPath`, `IsCircuit`, `IsCycle`, `IsChordless`, `IsSubwalk`; none
  says that a walk crosses from one set out of another.
* Circular orders: `CircularOrder ℤ` with `Int.sbtw_iff` (used).
* No landing sequences or windows.

Mathlib lemmas used:

* walks: `Walk.support_injective` (countability of walks, for measurability),
  `Walk.map_fst_darts`, `Walk.map_snd_darts`, `snd_mem_tail_support`,
  `penultimate_mem_dropLast_support`, `adj_snd`, `adj_penultimate`, `mk_start_snd_mem_edges`,
  `Walk.induce`, `Walk.transfer`, `bypass_isPath`, `Adj.support_toWalk`, `Adj.edges_toWalk`,
  `tail_support_append`, `dropLast_support_concat`;
* measurability: `Measurable.exists`, `Measurable.forall`, `measurableSet_setOfPred`;
* sets: `Set.image_add_const_Icc`.

Library lemmas reused: `exists_first_exit` (`Bond/FirstExit.lean`), `dualConfig_image_add`,
`mem_dualConfig_iff`, `mem_dualConfig_iff'`, `dualEdge_dualEdge`,
`map_add_one_dualEdge_dualEdge`, `measurable_dualConfig`, `perimeterPos_add`,
`boxBoundary_eq_Icc_diff_Icc`, `mem_armEvent_iff_exists_mem_boxBoundary`.
