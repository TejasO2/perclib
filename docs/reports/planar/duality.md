# Planar duality on the square lattice: advice for the wiki

Advice for the wiki agent on the first planar package: bond percolation on `ℤ²`, the dual
lattice, the duality of crossings of a box, and the crossing probability `1/2` at the
self-dual point. Everything below is proved in Lean with only `propext`, `Classical.choice` and
`Quot.sound`; no `…Input` is used. No `@[tag]` attribute has been added: the wiki agent writes
the tagged statements, and the declarations listed here are what they should point at.

Lean files: `PercLib/Models/Planar/Defs.lean` (definitions and their API),
`PercLib/Models/Planar/Duality.lean` (the deterministic duality lemma),
`PercLib/Models/Planar/SelfDuality.lean` (the probability one half).

## Conventions

- The square lattice is `zdGraph 2 = SimpleGraph.hasse (Fin 2 → ℤ)`; a point is `![x, y]`.
  Coordinate `0` is horizontal, coordinate `1` vertical.
- A configuration is a `Set (Sym2 (LatticeSite 2))` (the bond interface of D-2), with law
  `law q = prodBernoulli q`. Only nearest-neighbour pairs are used by the events below, so the
  profile `q` off the edges of `ℤ²` is arbitrary.
- **Dual lattice.** The dual vertex `f = ![a, b]` is the unit face with lower-left corner
  `(a, b)`, i.e. the point `(a + 1/2, b + 1/2)`. The dual lattice is therefore another copy of
  `zdGraph 2`, and dual edges are edges of `zdGraph 2`.
- **Dual edge** (`dualEdge`): the quarter turn of an edge about its midpoint. Concretely
  `{(x, y), (x + 1, y)} ↦ {(x, y - 1), (x, y)}` and `{(x, y), (x, y + 1)} ↦ {(x - 1, y), (x, y)}`.
- **Dual configuration** (`dualConfig ω`): a dual edge is open iff the edge it crosses is
  closed in `ω`.
- **Box** `Set.Icc lo hi = [lo₀, hi₀] × [lo₁, hi₁]` (product order on `Fin 2 → ℤ`).
- **Crossing** (`crossing i lo hi`, any dimension `d`): some vertex of the box with `i`-th
  coordinate `lo i` is joined to some vertex of the box with `i`-th coordinate `hi i` by a
  path of open nearest-neighbour edges whose vertices all lie in the box. `crossing 0` is a
  left-right crossing, `crossing 1` a bottom-top crossing.

## Statements as proved

**1. Planar duality of crossings** (`mem_crossing_zero_iff_dualConfig_notMem_crossing_one`).
For `lo ≤ hi` and every configuration `ω`, the box `R = [lo₀, hi₀] × [lo₁, hi₁]` has an open
left-right crossing if and only if the dual box `R* = [lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]` has no
bottom-top crossing in the dual configuration. In Lean:

```lean
theorem mem_crossing_zero_iff_dualConfig_notMem_crossing_one {lo hi : LatticeSite 2}
    (hle : lo ≤ hi) (ω : Config (LatticeSite 2)) :
    ω ∈ crossing 0 lo hi ↔ dualConfig ω ∉ crossing 1 ![lo 0, lo 1 - 1] ![hi 0 - 1, hi 1]
```

The two halves are separate theorems:

- *not both*, `notMem_crossing_one_dualConfig_of_mem_crossing_zero` (no hypothesis on
  `lo`, `hi`);
- *at least one*, `mem_crossing_one_dualConfig_of_notMem_crossing_zero` (needs `lo ≤ hi`).

The event form is `crossing_zero_eq_compl_preimage_dualConfig`. The statement holds for every
box shape, not only `(n + 1) × n`. The hypothesis `lo ≤ hi` is needed: for an empty box both
events fail. For a box of width zero (`lo₀ = hi₀`) the left-right crossing is trivial and the
dual box is empty, consistent with the statement.

Wiki assertion this supports: "for any rectangle, exactly one of: an open left-right crossing,
or a closed (dual-open) top-bottom crossing of the matching dual rectangle".

**2. Crossing probability one half** (`law_crossing_zero_eq_half`). If every edge of `ℤ²` is
open with probability `1/2`, then for every `lo` and `n` the box
`[lo₀, lo₀ + n + 1] × [lo₁, lo₁ + n]` (side lengths `n + 1` by `n`) has an open left-right
crossing with probability exactly `1/2`:

```lean
theorem law_crossing_zero_eq_half (lo : LatticeSite 2) (n : ℕ)
    {q : Sym2 (LatticeSite 2) → unitInterval}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) :
    law q (crossing 0 lo (lo + ![(n : ℤ) + 1, n])) = 1 / 2
```

The hypothesis constrains `q` only on the edges of `ℤ²`, so the statement covers both the
nearest-neighbour model (`q = 1/2` on edges, `0` elsewhere) and the homogeneous profile. A
compiled example checks it for the constant profile `1/2`.

**Supporting results** worth a mention, each usable on its own:

- `law_preimage_dualConfig_eq`: at `q = 1/2` on the edges of `ℤ²`, any event depending only
  on those edges has the same probability for `dualConfig ω` as for `ω` (self-duality of the
  law).
- `image_mem_crossing_iff`: crossings are carried along an automorphism of `ℤ^d` that maps a
  box onto a box and the faces in direction `i` onto the faces in direction `j`.
- `law_preimage_image_sym2Map_eq`: for any graph `G`, an automorphism preserving the profile
  on the edges of `G` preserves the probability of every event depending only on those edges.
- `univ_mem_crossing_zero`: with every edge open, every nonempty box is crossed (obtained from
  the duality, not by building a path).
- `dualEdgeEquiv`, `dualEdge_mem_dualConfig_iff`, `dualEdge_dualEdge` (taking the dual twice
  translates by `(-1, -1)`).

## Sources and locators

Only the section titles and page numbers below were checked, against the printed tables of
contents of both books. The bodies of the sections were not available, so the lemma numbers
are not given and the placement of each statement within a section is unconfirmed. Before
tagging, the wiki agent should confirm the exact lemma or theorem number in the text.

- G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer, 1999. Chapter 11
  "Bond Percolation in Two Dimensions" (p. 281); §11.2 "Planar Duality" (pp. 283–286) is the
  expected locator for the dual lattice and the duality of crossings; §11.3 "The Critical
  Probability Equals ½" (pp. 287–294) is the expected locator for the crossing probability
  one half of the `(n + 1) × n` rectangle.
- B. Bollobás and O. Riordan, *Percolation*, Cambridge University Press, 2006. Chapter 3
  "Bond percolation on Z² – the Harris–Kesten Theorem" (starts p. 50; §3.1, on the
  Russo–Seymour–Welsh method, starts p. 57), whose opening pages are the expected locator for
  planar duality and the self-dual rectangle; §5.4 "Bond percolation on a lattice and its
  dual" (p. 136) for the general planar-lattice version.

The textbook proofs of "at least one" follow the boundary of the cluster of the left side,
which needs a discrete Jordan-curve argument. The Lean proof below avoids it; the wiki may
present either, but should say which one the Lean follows.

## Proof outline (as in the Lean)

*Not both* (`notMem_crossing_one_dualConfig_of_mem_crossing_zero`). Fix a dual-open path `σ`
from the bottom row `lo₁ - 1` to the top row `hi₁` of `R*`. For a vertex `v = (x, y)` let `N(v)`
be the number, modulo two, of steps of `σ` that cross the horizontal half-line to the left of
`v`, i.e. dual steps between `(x', y - 1)` and `(x', y)` with `x' < x`.

1. On the left side `x = lo₀`, `N = 0`, because `σ` stays in `R*`, where `x' ≥ lo₀`.
2. On the right side `x = hi₀`, `N` counts every crossing of the line between rows `y - 1`
   and `y`; `σ` starts below it and ends above it, so `N = 1`.
3. Across an open horizontal edge `{(x, y), (x + 1, y)}`, `N` changes by the number of uses
   of its dual edge, which is `0` because a dual-open edge crosses only closed edges.
4. Across an open vertical edge `{(x, y), (x, y + 1)}` inside `R`, `N(x, y) + N(x, y + 1)` is
   the number of times `σ` enters or leaves the half-row of faces `{(x', y) : x' < x}`, minus
   the uses of the dual of that edge (none). A walk whose ends lie outside a set enters and
   leaves it an even number of times, so the two values agree.

So `N` is constant along an open path, and no open path joins the two sides.

*At least one* (`mem_crossing_one_dualConfig_of_notMem_crossing_zero`). A *corner* is a pair
(vertex `v`, face `f`) with `v` a corner of `f`; it is encoded by the point `s = v + f` of `ℤ²`
(`cornerVertex`, `cornerFace`). Each corner lies on one horizontal and one vertical edge of
its face (`cornerHEdge`, `cornerVEdge`). The involution `hPartner ω` sends a corner to the
corner of the same face at the other end of its horizontal edge if that edge is open, and to
the corner at the same vertex across that edge if it is closed; `vPartner ω` does the same
with the vertical edge. This is the loop representation: one step of a partner map moves the
vertex along an open edge or the face along a dual-open edge, never both.

1. The corners with vertex in `R` and face in `R*` form the box
   `K = [2lo₀, 2hi₀ - 1] × [2lo₁ - 1, 2hi₁]` of corner coordinates.
2. Wire the boundary: make the vertical edges of the left and right sides of `R` open and
   the vertical edges leaving `R` downwards and upwards closed. Then `hPartner` maps `K` to
   itself, and `vPartner` maps every corner of `K` into `K` except the four extreme corners.
3. Suppose neither crossing exists. Let `S` be the corners of `K` whose vertex is joined to
   the left side of `R` by an open path in `R`, and whose face is joined to the bottom row of
   `R*` by a dual-open path in `R*`. One step of a partner map stays in `S` (a wired step on
   the right side or top would produce a crossing). The bottom-left extreme corner is in `S`;
   the other three are not, again because each would give a crossing.
4. `hPartner` pairs off the elements of `S`, so `|S|` is even; `vPartner` pairs off the
   elements of `S` other than the bottom-left extreme corner, so `|S| - 1` is even. This is a
   contradiction.

*Probability one half* (`law_crossing_zero_eq_half`). Write `x` for the crossing probability.
By duality `x = 1 - P(dual crossing of R*)`. At `1/2` the dual configuration restricted to the
edges of `ℤ²` has the law of the configuration (the dual map is a bijection of the edges and
`1 - 1/2 = 1/2`), so `P(dual crossing of R*) = P(bottom-top crossing of R*)`. Exchanging the
coordinates and translating maps `R*`, a box of side lengths `n` by `n + 1`, onto `R` and its
bottom-top crossing onto the left-right crossing of `R`, and preserves the law. Hence
`x = 1 - x`.

## Declarations by role

| Role | Declaration | File |
|---|---|---|
| Definition: crossing of a box in `ℤ^d` | `PercLib.Models.Planar.crossing` | `Defs.lean` |
| Definition: dual edge | `PercLib.Models.Planar.dualEdge` | `Defs.lean` |
| Definition: edge–dual-edge bijection | `PercLib.Models.Planar.dualEdgeEquiv` | `Defs.lean` |
| Definition: dual configuration | `PercLib.Models.Planar.dualConfig` | `Defs.lean` |
| Definitions: corner lattice (loop representation) | `cornerVertex`, `cornerFace`, `cornerHEdge`, `cornerVEdge`, `hPartner`, `vPartner` | `Defs.lean` |
| Dual edge open iff crossed edge closed | `dualEdge_mem_dualConfig_iff` | `Defs.lean` |
| Edges of `ℤ²` | `mem_edgeSet_zdGraph_two_iff`, `zdGraph_two_adj_iff` | `Defs.lean` |
| Duality of crossings (exactly one) | `mem_crossing_zero_iff_dualConfig_notMem_crossing_one` | `Duality.lean` |
| Duality, not both | `notMem_crossing_one_dualConfig_of_mem_crossing_zero` | `Duality.lean` |
| Duality, at least one | `mem_crossing_one_dualConfig_of_notMem_crossing_zero` | `Duality.lean` |
| Duality, as events | `crossing_zero_eq_compl_preimage_dualConfig` | `Duality.lean` |
| Self-duality of the law at `1/2` | `law_preimage_dualConfig_eq` | `SelfDuality.lean` |
| Crossing probability `1/2` | `law_crossing_zero_eq_half` | `SelfDuality.lean` |

All declarations are in namespace `PercLib.Models.Planar` except the general lemmas
`SimpleGraph.Walk.sum_map_darts_sub`, `PercLib.Probability.prodBernoulli_eq_of_eqOn` and the
`PercLib.Percolation.Bond` lemmas `mem_localConn_of_mem_localConn_of_mem`,
`image_mem_localConn_iff`, `image_sym2Map_edgeSet`, `law_preimage_image_sym2Map_eq`.

## Suggestions for the tagged statements

- Tag the duality iff and the probability one half as two assertions; tag the two halves of
  the duality separately if the wiki states them separately.
- State the rectangle as in the sources (side lengths `n + 1` and `n`); the Lean box
  `[lo₀, lo₀ + n + 1] × [lo₁, lo₁ + n]` has those side lengths.
- The tagged probability statement can keep the hypothesis "`q = 1/2` on the edges of
  `ℤ²`"; it is not an excess binder, since the source's `p = 1/2` is that hypothesis on the
  nearest-neighbour model.
