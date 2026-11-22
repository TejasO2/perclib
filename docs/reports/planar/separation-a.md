# Local separation, part A2a-1: relative duality and the greedy exploration

Advice for the wiki agent and for the next session on package A2 of the arms plan (Nolin's local
separation lemma, EJP 2008, Lemma 15, p. 1579). A2 is **not finished**. This part proves the
exploration that the lemma conditions on, in the new file
`PercLib/Models/Planar/Arms/Separation.lean` (712 lines, 20 theorems, imports
`Arms/ColourInversion.lean`). The file is proof-only: no definition, no tag, no `…Input`;
`Arms/Defs.lean` and `Planar/Defs.lean` are unchanged. Everything uses only `propext`,
`Classical.choice` and `Quot.sound`.

What is done: relative duality for any box, the explored dual cluster of the left column for any
configuration, the greedy exploration of crossings for any configuration (existence, uniqueness,
growth, determination, disjointness, maximality), step (a) of the lemma (the exploration finds
few crossings), and the surgery for a crossing that has its own cluster. What is left: the dual
exploration's conventions, the protection events and their conditional probability (A2b), the
surgery for packs of same-colour crossings in one cluster, and the final statement. The design
for all of it, and one correction to the source's rerouting step, are below.

## Conventions

As in `multi-arm-basics.md`: points of `ℤ²` are `![x, y]`, boxes are `Set.Icc lo hi`, the face
`f` is the unit square with lower-left corner `f`, `dualConfig ω` is the set of dual-open dual
edges. For a box `Icc lo hi` of height at least one (`lo 1 < hi 1`):

* the **dual box** is `T = Icc ![lo 0 - 1, lo 1] ![hi 0, hi 1 - 1]` (the faces met by a left-right
  dual path blocking bottom-top crossings, as in `mem_crossing_one_iff_dualConfig_notMem_crossing_zero`);
  its **left column** is `x = lo 0 - 1`, its **right column** `x = hi 0`, its bottom-left face is
  `a₀ = ![lo 0 - 1, lo 1]`;
* the **wired dual configuration** of `ζ` is
  `ζ' = dualConfig ζ ∩ {s | ∀ v ∈ s, v ∈ T} ∪ W`, where `W` joins consecutive faces of the left
  column; the **explored cluster** of `ζ` is `cluster ζ' a₀`. Statements carry `ζ'` through a
  hypothesis `hζ' : ζ' = …` (no definition);
* the **exploration** of a configuration `G` with choice rule `Γ` (a crossing `Γ A` from `c A` to
  `d A` for each finite set of faces `A`) up to step `u` is a sequence `A : ℕ → Finset` with

  ```lean
  ∀ v ≤ u, cluster (dualConfig (G \ {e | ∃ x ∈ e, ∃ w < v, x ∈ (Γ (A w)).support}) ∩
      {s | ∀ x ∈ s, x ∈ T} ∪ W) a₀ = ↑(A v)
  ```

  `A v` is **admissible** when it avoids the right column (`∀ f ∈ A v, f 0 ≠ hi 0`); then
  `Γ (A v)` is the `(v + 1)`-th greedy crossing.

## Statements as proved

**Relative duality** (`mem_crossing_one_of_leftColumn`): for `lo ≤ hi`, a set `D₀` of faces
containing the left column of `T` and avoiding its right column,

```lean
{e | e ∈ (zdGraph 2).edgeSet ∧ (∀ f ∈ dualEdge e, f ∈ T) ∧
    (∃ f ∈ dualEdge e, f ∈ D₀) ∧ ∃ f ∈ dualEdge e, f ∉ D₀} ∈ crossing 1 lo hi
```

The explored set is a wired boundary arc: the edges separating it from the rest of `T` carry a
bottom-top crossing. This generalises `RSWKeyStep.mem_crossing_one_boundary` (square `[0, n]²`,
`lo = 0`) to every box.

**The explored cluster** (hypotheses `h1 : lo 1 < hi 1`, `hle`, `hζ'`):

| Theorem | Statement |
|---|---|
| `forall_mem_Icc_of_mem_wired` | every pair of `ζ'` is an edge with both ends in `T` |
| `exists_walk_of_mem_exploredCluster` | each face of the cluster is joined to `a₀` by a walk in the cluster along `ζ'` |
| `exploredCluster_subset` | the cluster lies in `T` |
| `mem_exploredCluster_of_leftColumn` | the left column lies in the cluster |
| `mem_of_mem_exploredCluster_of_notMem` | an edge with duals in `T`, one in the cluster and one not, is open in `ζ` |
| `forall_mem_exploredCluster_ne_of_mem_crossing` | `ζ ∈ crossing 1 lo hi` ⇒ the cluster avoids the right column |
| `mem_crossing_one_iff_forall_mem_exploredCluster_ne` | `ζ ∈ crossing 1 lo hi ↔` the cluster avoids the right column |
| `exploredCluster_anti` | `ζ₁ ⊆ ζ₂` ⇒ cluster of `ζ₂` ⊆ cluster of `ζ₁` |
| `exploredCluster_eq_iff_of_agree` | for a finite `D₀ ∋ a₀`, `cluster = D₀` depends only on the edges whose duals meet `D₀` |
| `measurable_wired` | `ζ ↦ ζ'` is measurable |

**The greedy exploration** (any `G`, any `Γ`):

| Theorem | Statement |
|---|---|
| `exists_crossing_choice` | a choice rule exists: for each `A` containing the left column and avoiding the right column, `Γ A` runs in the box from the bottom row to the top row along edges separating `A` from the rest of `T` |
| `exists_exploration` | every `G` has an exploration up to every step |
| `exploration_unique` | two explorations of `G` agree up to the common step |
| `exploration_mono` | `v ≤ w ≤ u` ⇒ `A v ⊆ A w` |
| `exploration_iff_of_agree` | for increasing `A` with `a₀ ∈ A v`, being the exploration of `G` up to `u` depends only on the edges whose duals meet `A u` |
| `forall_mem_of_exploration` | if `A v` is admissible, the edges of `Γ (A v)` are open in `G` and its vertices avoid every `Γ (A w)`, `w < v` |
| `exists_mem_support_of_exploration` | if `A u` meets the right column, every bottom-top crossing open in `G` meets some `Γ (A w)`, `w < u` (maximality) |
| `exists_walk_reroute_of_exploration` | under the same hypothesis, every open crossing from `a` has a walk from `a` to `d (A w)` for an admissible `A w`, `w < u`, inside the crossing and `Γ (A w)`, open in `G` |

**Step (a)** (`law_exploration_le_pow`): under `CrossingBounds q L c`, in the box
`Icc lo (lo + ![k n, n + 1])` with `1 ≤ n ≤ L`, the event "the exploration of `ω` up to step `u` has
all `A v` admissible" has probability at most `(1 - c (k + 1))^(u + 1)`.

## Proofs the Lean follows

* Relative duality: box duality (`mem_crossing_one_iff_dualConfig_notMem_crossing_zero`) for the
  configuration `B` of separating edges. A dual left-right crossing of `T` in `dualConfig B` starts
  in `D₀` (left column) and ends outside (right column); its boundary dart crosses an edge of `B`,
  which is then closed in `B`: contradiction. Same argument as `mem_crossing_one_boundary`.
* The explored cluster: the internal `have`s of `RSWKeyStep.law_crossing_zero_mul_law_crossing_one_le`
  (`hDSv`, `hDleft`, `hDbdry`, `hDright`, `hindep`) made into lemmas for a general box and a
  general configuration. Determination is `cluster_eq_finset_determined` plus the equality of the
  wired configurations on the pairs meeting `D₀`.
* The exploration: no recursive definition. A sequence `A` is tested against the condition above;
  existence is induction on `u` (extend by `if v ≤ u then A v else …`); uniqueness is strong
  induction (the removed edge sets agree once the earlier sets agree); growth is
  `exploredCluster_anti` (more edges removed); determination is `exploredCluster_eq_iff_of_agree`
  at each step, with `A v ⊆ A u`. Disjointness: the edges of `Γ (A v)` separate `A v` from the
  rest, so they are open in `G` minus the removed edges, hence avoid the earlier crossings' vertices
  (`mem_support_iff_exists_mem_edges_of_not_nil`). Maximality: a crossing avoiding all chosen
  crossings is a crossing of the last configuration, so its explored cluster avoids the right
  column. Rerouting: take the first step `u₀` (`Nat.find`) whose cluster meets the right column;
  all earlier steps are admissible; follow the crossing to a common vertex, then the chosen
  crossing (`takeUntil`, `dropUntil`).
* Step (a): the `u + 1` chosen crossings are disjoint open crossings, so A1b's
  `mem_foldl_crossing_of_walks` and `law_foldl_crossing_one_le_pow` apply.

## Design for the rest of A2

### Target statement (inline, for the record)

Plan §2.3's `exists_law_separable_ge`, with `Separable` written out (rule 4: no definition).
Strip `Q = Icc 0 ![4N, N]` (or any `Icc lo (lo + ![4N, N])`), crossings from bottom to top:

```lean
theorem exists_law_separable_ge (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ q L, CrossingBounds q L c → ∀ N : ℕ, (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, γ i crosses Q in colour σ i) → (γ pairwise disjoint) →
          ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
            (∀ i, γ' i crosses Q in colour σ i) ∧ (γ' pairwise disjoint) ∧
            (positions of b' pairwise ≥ 4 √η N apart, and ≥ 4 √η N from both top corners) ∧
            (∀ i, fence of colour σ i at b' i)}
```

* Open crossing: `a 1 = 0`, `b 1 = N`, support in `Q`, edges in `ω`. Dual crossing: a walk of
  faces from row `-1` to row `N`, intermediate faces in `Icc 0 ![4N - 1, N - 1]`, each dual edge
  crossing an edge of `Q` (PT1 / I2b convention), dual edges in `dualConfig ω`.
* Positions are doubled (`2 (b 0)` open, `2 (b 0) + 1` dual), so `2√η N` becomes `4√η N`.
* Disjoint: open–open vertex-disjoint, dual–dual face-disjoint, open–dual nothing.
* Fence (Nolin (4.5)): the box `Icc ![x - ⌊ηN⌋, N] ![x + ⌊ηN⌋, N + ⌊√ηN⌋]` above the landing
  point `b' i = (x, N)` is crossed left-right in colour `σ i`, and that crossing is joined to
  `b' i` in colour `σ i` inside `B_{⌊√ηN⌋}(b' i)`; dual version on faces.
* "Same bottom parts" in the plan is read as Nolin's Definition 7: **same starting points**
  (`γ' i` starts at `a i`). Same order then follows from disjointness.
* For small `N` (`16 η N < 1`) the event is everything (take `γ' = γ`; positions differ by
  parity or disjointness; fences degenerate), so nothing is lost by the floors.

### Explore each colour separately

Nolin takes the lowest crossing of either colour, then the lowest disjoint one, and so on. Mixed
colours are not needed. Run the exploration of this file twice:

* **open**: `G = ω`, box `Q`;
* **dual**: `G = dualConfig ω ∩ dualEdge '' {e ∈ edgeSet | ∀ x ∈ e, x ∈ Q}` (dual edges crossing
  edges of `Q` only), box of faces `Icc ![0, -1] ![4N - 1, N]`. Its explored clusters are sets of
  vertices shifted by `(-1, -1)` (`dualEdge_dualEdge`); nothing new is needed.

Each greedy tip `z` (top end of a chosen crossing `γ`) is then **protected from the right in both
colours**: in the fresh region (edges whose duals miss the explored set), a path of each colour
from (or, for the other colour, from next to) `γ`, around `z` at distance between `ρ = 2√ηN` and
`η^{1/4} N`, to the top side right of `z`. A crossing of either colour that is disjoint from `γ`
and lands within `ρ` to the right of `z` meets the cross-cut "`γ` up to the start of the path, then
the path" of the other colour (interlacing in `Q`, with the doubled lattice for mixed colours),
which is impossible. Hence **all tips of both explorations are pairwise `ρ`-separated**: tips
`z₁ < z₂` closer than `ρ` would belong to disjoint crossings `γ₁, γ₂` (different colours, or two
crossings of the same exploration), and `γ₂` would land within `ρ` to the right of `z₁`, which
the protection of `z₁` excludes. The blocking argument is deterministic and does not need
freshness. Corners: both colours protected at the two top corners.
Fences: a path of `γ`'s colour around `z` at distance between `2ηN` and `√ηN/2`, passing above
`Q` from right to left; its part above `Q` crosses the fence box.

### Conditional probability (A2b)

For a fixed admissible exploration sequence `A` up to step `v`, the event "exploration of `ω` is
`A`" is determined by the edges whose duals meet `A v` (`exploration_iff_of_agree`), and the
protection event of the tip of `Γ (A v)` uses only the other edges: independent
(`prodBernoulli_inter_of_determined`). Events for different sequences are disjoint
(`exploration_unique`); restrict to `A w ⊆ T` so there are finitely many. So

`P(some tip of step ≤ T not protected) ≤ 2 T · max_A P(protection of Γ (A v) fails)`,

and `P(≥ T crossings) ≤ 2 (1 - c 5)^T` (`law_exploration_le_pow` for each colour). Choose `T`, then
`η`.

**Fresh protection has probability at least that of a standard event**, for every fixed `A`
(the `exists_walk_unexplored` pattern of `RSWKeyStep.lean`): for every `ω` with a circuit of colour
`X` in the annulus around `z`, cut the circuit at a point above `z` and follow it clockwise to its
first vertex on `Γ (A v)` (colour of `γ`) or next to it (other colour); everything before is in
the fresh region, because reaching an explored vertex first would cross `Γ (A v)` (separation
lemma `exists_mem_support_of_dualConfig_mem_localConn` with `τ = Γ (A v)` extended upwards from
`z`; the dual paths inside `A v` cross no edge of `Γ (A v)`). The circuit events in disjoint
annuli are independent with probability `≥ c'` each (`CrossingBounds`, Harris), so failure at
`K ≍ log(1/η)` scales has probability `≤ (1 - c')^K`, a power of `η`. The circuits must use
**dyadic annuli between `2√ηN` and `η^{1/4} N`** (both colours) and between `2ηN` and `√ηN/2`
(fence), and quarter-annuli at the corners.

### Surgery

* **A crossing alone in its cluster** (every family whose consecutive members are in different
  clusters of `Q`, e.g. alternating colours): every crossing meets a chosen crossing of its colour
  (`exists_mem_support_of_exploration`) and is rerouted inside its cluster to that tip
  (`exists_walk_reroute_of_exploration`; dual version through the dual exploration). Different
  members lie in different clusters (a member between two same-colour members separates them:
  primal–primal or mixed interlacing), so the new family is disjoint, keeps the starts and lands
  at separated, fenced tips. This is done up to the bookkeeping of the statement.
* **Packs** (two or more consecutive same-colour members in one cluster, `OO` in `OCOOC`): the
  members must be sent to distinct tips of the same exploration by disjoint walks. This is a
  linkage statement (planar Menger type: `m` disjoint crossings from given starts to `m` of the
  greedy tips). **Open.** Mathlib has no Menger theorem. Two routes: (i) prove that greedy
  crossings are leftmost (every crossing avoiding `Γ (A 0), …, Γ (A (v - 1))` lies weakly right of
  `Γ (A v)`, via `A v` and interlacing) and use the first-hit rule below with an inductive
  uncrossing argument; (ii) prove that the greedy family is a maximum disjoint family and derive
  the linkage from the same exchange argument.

## Correction to the source's rerouting step

The subagent's paraphrase of Nolin's step (f) (arXiv v1, Lemma 14; journal Lemma 15, not
re-read): crossing `c'_k` of the given family is matched to the lowest greedy crossing `c_{v_k}` it
meets (`v_1 < v_2 < …`), and the piece of `c'_k` after its **last** intersection with `c_{v_k}` is
replaced by the end of `c_{v_k}`. With leftmost greedy crossings this can produce intersecting
crossings. Sketch, strip `[0, 3] × [0, 1]` with greedy crossings the vertical lines `x = 0` and
`x = 2`:

* `c'_k`: from `(0.5, 0)` up to `(0.5, 0.2)`, left to `(0, 0.2)`; then through the gap to
  `(2, 0.7)`; back to `(0, 0.8)`; then to `(1, 1)`;
* `c'_l`: from `(3, 0)` to `(2, 0.5)`, then to `(2.5, 1)`;
* no other open edges in the gap `0 < x < 2`.

Every route from `x = 2` into the gap ends on `x = 0`, so `x = 2` is the leftmost crossing avoiding
`x = 0`, and `c'_k`, `c'_l` are disjoint. Here `v_k` is the index of `x = 0` and `v_l` the index of
`x = 2`. The rule gives `c''_k = c'_k` up to `(0, 0.8)`, then `x = 0`, and `c''_l = c'_l` up to
`(2, 0.5)`, then `x = 2`. Both pass through `(2, 0.7)`. Cutting `c'_k` at its **first**
intersection with `c_{v_k}`, at `(0, 0.2)`, gives disjoint crossings here. That the first-hit rule
works in general is not proved: the argument for `v_l = v_k + 1` uses the leftmost property, and
intermediate greedy crossings are not handled. The cluster argument above avoids the issue for
families without packs. This is a gap in the proof route, not in the statement. Nothing was
narrowed.

## Statement choices compared with the plan

* Plan §2.3 explores "alternately the dual cluster of the left side … then the open cluster of its
  boundary crossing". Here each colour gets its own greedy exploration in its own configuration,
  with the earlier crossings' vertices removed. That is simpler (one generic theory, applied
  twice), and mixed colours only enter through interlacing.
* The exploration is stated for any configuration and any box, not the strip: rule 5.
* Step (a) is stated for the exploration itself (A1b's tail is about disjoint occurrence), in the
  box `Icc lo (lo + ![k n, n + 1])` of A1b; the strip `[0, 4N] × [0, N]` is `k = 4`, `n = N - 1`.

## Not done here

1. Dual exploration: the conventions above (restricted dual configuration, box of faces) and a
   dual version of `law_exploration_le_pow` (`law_foldl_dualConfig_crossing_one_le_pow`).
2. Protection: the geometric extraction lemma (circuit ⇒ fresh barrier, both colours; corners;
   fence), the blocking lemma (barrier ⇒ no crossing lands nearby), the circuit probabilities in
   annuli and half-annuli from `CrossingBounds`, and the assembly over exploration sequences (A2b).
3. Surgery for packs (open, see above) and the final statement `exists_law_separable_ge`.
4. Wiki edits are on hold; nothing is tagged.

## Search

* PercLib: `mem_crossing_one_boundary`, `exists_walk_unexplored` and the internals of
  `law_crossing_zero_mul_law_crossing_one_le` (`RSWKeyStep.lean`) are the square special case; no
  general explored-cluster or greedy-crossing lemma existed. `cluster_eq_finset_determined`,
  `measurableSet_cluster_eq_finset` (`Bond/ClusterLaw.lean`) are used as they are.
* Mathlib: `SimpleGraph.Walk.exists_boundary_dart`, `mem_support_iff_exists_mem_edges_of_not_nil`,
  `takeUntil`/`dropUntil` API. No Menger theorem (`grep -ri menger` finds nothing in the pinned
  Mathlib), so the pack surgery needs its own argument.

## Sources

* P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
  no. 55, §4.2 (Definitions of well-separateness, fences, (4.3)–(4.5)), §4.4, Lemma 15 (p. 1579).
  Read this session through arXiv:0711.4948v1 (HTML), where it is Lemma 14 and the separation
  theorem is Theorem 10; journal page numbers from the plan, not re-checked.
* B. Bollobás, O. Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math. Soc.
  38 (2006), proof of Lemma 6 (exploration of the dual cluster of a side; the template in
  `RSWKeyStep.lean`).
