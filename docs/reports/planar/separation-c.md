# Local separation, part A2c-1: protection of the greedy tips and fences

Advice for the wiki agent and for the next session on package A2 of the arms plan (Nolin's local
separation lemma, EJP 2008, Lemma 15). **A2 is still not finished.** This part proves the
deterministic protection of the greedy tips (separation from other tips of both colours, from the
top corners, and the fence) and the probability bounds for the protection events. What is left
(A2c-2) is bookkeeping: determination and measurability of the protection events, the sum over
exploration sequences, the dual instance, the final statement and its assembly. **Two statement
problems were found** in the draft target of `separation-a.md`; they are recorded below with a
counterexample and a proposed faithful statement. The user should confirm the statement before
A2c-2 proves it.

New files, both proof-only (no definition, no tag, no `…Input`; `Arms/Defs.lean` and
`Planar/Defs.lean` unchanged); everything uses only `propext`, `Classical.choice`, `Quot.sound`:

* `PercLib/Models/Planar/Arms/SeparationProtection.lean` (828 lines, 20 theorems);
* `PercLib/Models/Planar/Arms/SeparationFence.lean` (423 lines, 4 theorems).

## Design change: absence events in the fresh part

`separation-b.md` planned to extract fresh barrier paths from circuits ("follow the circuit
clockwise until it reaches the greedy crossing") and then block with them. For separation this
is not needed. Let `E` be the set of edges with a dual face in the explored set `A v` (the edges
the exploration up to step `v` has looked at); `{exploration = A}` is determined by `E`.

* **Same colour.** The event "the fresh part `(G \ E) ∩ box` crosses none of the three in-box
  strips of the annulus `s ≤ ‖· - z‖∞ ≤ 3s` around the tip `z` in their short directions" is
  determined by edges outside `E`, contains the dual circuit event of `G` (monotonicity), and
  blocks every later greedy crossing from landing within `s` right of `z`
  (`lt_sub_of_exploration`). Later greedy crossings are fresh (`not_le_of_mem_support_of_exploration`),
  so they would cross a strip of the fresh part. The fourth strip lies above the box.
* **Other colour.** The same with the fresh part of the dual configuration,
  `dualConfig (G ∪ E) ∩ (dual box)`: walks of faces crossing only closed edges of `G` and landing
  at or right of a tip are fresh (`notMem_of_localConn_of_exploration`), so they are blocked
  (`false_of_localConn_of_exploration`).
* **Corners**: the same strips for `G ∩ box` itself (`false_of_le_add_corner_right`, `_left`); no
  freshness is needed there.

All three reduce to `CriticalProbability.notMem_localConn_of_notMem_crossing`, translated to any
centre (`notMem_localConn_of_notMem_crossing_add`). The probability lower bounds come from the
circuit events at any centre (`pow_le_law_compl_crossing_inter_add`,
`pow_le_law_dualConfig_notMem_crossing_add`, `pow_le_law_crossing_inter_add`, all `c 7 ^ 4`, by
`CrossingBounds.translate` and `law_translate_apply`), and the conditioning step is
`law_inter_biInter_compl_le`: an event determined by the explored pairs, intersected with the
failure of `J` protection events determined by pairwise disjoint sets of unexplored pairs, has
probability at most `P(X) (1 - β)^J`.

Path extraction is needed only for the **fence**, and there the event is again monotone: "`G ∪ E`
crosses the four boxes of an annulus around `z` in their long directions" (explored edges count
as open) contains the open circuit event and is determined by edges outside `E`. The
deterministic step (`exists_fence_of_exploration`) follows the circuit clockwise: top crossing
from its left end to the top right corner square, down the right crossing, along the bottom
crossing, up the left crossing to the top row. When the annulus fits horizontally in the box, this
walk enters the box only from above and right of `z` (the top crossing lies above the box, the
bottom one inside it, the left one is followed only up to the top row), and its last piece in the
box runs from the top row right of `z` to the top row left of `z`, so by top separation it meets
the crossing `γ`. Cut it at its first vertex on `γ` or at an explored face; top separation again
puts that vertex on `γ`, and every edge before it has an end without explored face, so it is not
in `E`, hence open in `G`.

## Statements proved

`SeparationProtection.lean` (line numbers at `1556771`):

| Theorem (line) | Statement |
|---|---|
| `SimpleGraph.Walk.exists_isPath_clean` (78) | a walk from `P` to `Q` contains a path meeting `P` only at its start and `Q` only at its end |
| `notMem_crossing_of_forall` (134) | no crossing of a box by a configuration whose edges have their ends outside its range |
| `not_localConn_top` (150) | **top separation, dual form**: a clean bottom-top `τ` ending at `d`; no dual path crossing no edge of `τ` joins the left column of the dual box to a top-row face at or right of `d` |
| `exists_mem_support_of_lt_top` (201) | **top separation, primal form**: a walk from the top row strictly right of `d` to a vertex with a face joined to the left column without crossing `τ` meets `τ` |
| `notMem_localConn_of_notMem_crossing_add` (238) | blocking by the four strips of an annulus at any centre |
| `false_of_le_add_corner_right` (268), `_left` (306) | no crossing of `G` lands within `s` of a top corner if two strips at the corner are uncrossed by `G ∩ box` |
| `exists_crossing_choice_clean` (348) | a choice rule whose crossings are paths meeting the bottom row only at the start and the top row only at the end (the old `hΓ` is its first conjunct) |
| `localConn_of_mem_exploration` (399) | every face of `A v` reaches the left column without crossing any walk open after the removals of step `v` |
| `lt_of_exploration` (436) | the greedy tips increase from left to right |
| `not_le_of_mem_support_of_exploration` (481) | later greedy crossings have no vertex at a face of `A v` (fresh) |
| `notMem_of_localConn_of_exploration` (524) | a face joined, without crossing `Γ (A v)`, to a top-row face at or right of the tip is not in `A v` |
| `lt_sub_of_exploration` (560) | **same-colour blocking** (fresh `G`) |
| `false_of_localConn_of_exploration` (623) | **blocking of the other colour** (fresh dual configuration) |
| `preimage_image_add_crossing` (700) | translation of crossing events |
| `pow_le_law_compl_crossing_inter_add` (717), `pow_le_law_dualConfig_notMem_crossing` (731), `_add` (759), `pow_le_law_crossing_inter_add` (781) | circuit events at any centre, `≥ c 7 ^ 4` |
| `law_inter_biInter_compl_le` (797) | conditioning on an event of the explored pairs, `≤ P(X) (1 - β)^J` |

`SeparationFence.lean`:

| Theorem (line) | Statement |
|---|---|
| `exists_walk_of_mem_support_of_mem_support` (62) | a walk between two vertices of a walk, inside it |
| `exists_mem_support_of_mem_Icc_of_mem_Icc` (82) | two walks crossing a rectangle in the two directions meet |
| `exists_walk_entry_of_above` (114) | the last entry of a walk into a lower half-plane, from directly above |
| `exists_fence_of_exploration` (166) | **the fence**: if `G ∪ E` crosses the four boxes of the annulus `t ≤ ‖· - z‖∞ ≤ 3t + 1` (fitting horizontally in the box) in their long directions, every clean crossing landing at `z` and open after the removals of step `v` has a vertex joined, inside the ball of radius `3t + 1`, by edges of `G`, to the left end of a left-right crossing of the top box by edges of `G` |

The fence lemma is stated for any top-row point `z`, not only the tip, and needs no choice rule:
only the exploration `hA`.

## Statement problems in the draft target (`separation-a.md`)

### 1. The fence clause is stronger than Nolin's (4.5)

Nolin's Definition 6, condition (4.5) (arXiv v1, read this session through the HTML version):
the free space `r_i` (in our orientation the box `[x - ηN, x + ηN] × [N, N + √ηN]` above the
landing point) is crossed by `c̃_i` (here left to right, across its short side), and
**"`c_i ↝ c̃_i` inside `S̊_{√η M}(z_i)`"**: the *arm* `c_i` is joined to `c̃_i` inside the open ball.
The draft wrote "that crossing is joined to `b' i` in colour `σ i` inside `B_{⌊√ηN⌋}(b' i)`": the
*endpoint*. That is stronger, and neither Nolin's argument nor ours gives it. The fresh path meets
the rerouted crossing at some vertex `x` inside the ball, but the crossing can leave the ball after
`x` and come back to its end (a "finger" of the explored cluster's boundary near the tip). Ruling
fingers out would need a half-plane multi-arm bound at the tip (five arms; not available before
U1), which the source does not use. This is not a counterexample to the draft clause, only to its
provability by the source's route. **Proposed reading (faithful to (4.5))**: the fence clause says
that some vertex of `γ' i` is joined to the left end of a left-right crossing of the fence box
inside the ball. That is what `exists_fence_of_exploration` gives (with the top box of the annulus
in place of the fence box; the fence box is narrower and at least as tall when
`⌊ηN⌋ ≤ 3t` and `3t + 1 ≤ ⌊√ηN⌋`, so `crossing_zero_subset_crossing_zero`'s argument restricts it).
For A3's gluing (Nolin Prop. 12) the arm-connected form is what is used: a corridor path entering
the free space must cross `c̃_i`, which is joined to the arm.

### 2. The draft is false for small `N`: a counterexample

The draft quantifies `∀ N, (N : ℕ∞) ≤ L`. Take `N = 1`, so `Q = [0, 4] × [0, 1]` (13 edges), the
law `q ≡ 1/2` with the bounds `c` of `exists_crossingBounds_half` (crossing bounds at every scale,
`L = ⊤`), and any `δ < 2^{-13}`. With probability `2^{-13}` the only open edge of `Q` is the
vertical edge from `(0, 0)` to `(0, 1)`. The family consisting of this one open crossing must be
rerouted to an open crossing of `Q` from `(0, 0)`, which can only end at `(0, 1)`, at doubled
position `0`, at distance `0 < 4√η · 1` from the corner. So for every `η > 0` the event fails with
probability at least `2^{-13} > δ`. (Separation between distinct tips and the fences are harmless
for small `N`: `4√ηN ≤ 1` and `⌊ηN⌋ = ⌊√ηN⌋ = 0` make them automatic. Only the corners fail.)
Nolin's (4.11) has the same quantifier ("any `N ≤ L(p)`") and the same problem on a lattice;
his proof protects the corners by circuits at scales between powers of `η` times `N`, which are
empty for small `N`. **Proposed faithful statement**: add `∃ N₀ : ℕ` after `η`, and `N₀ ≤ N`
(with `N₀` depending only on `δ` and `c`). A3 applies the lemma at dyadic scales `2^k`; the
finitely many small scales go into its constants.

### Proposed statement for A2c-2 (please confirm)

```lean
theorem exists_law_separable_ge (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ N : ℕ, N₀ ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
          (∀ i, γ i crosses Q in colour σ i) → (γ pairwise disjoint) →
          ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
            (∀ i, γ' i crosses Q in colour σ i) ∧ (γ' pairwise disjoint) ∧
            (doubled positions of b' pairwise ≥ 4 √η N apart and ≥ 4 √η N from 0 and 8N) ∧
            (∀ i, ∃ x ∈ (γ' i).support, ∃ l r, l 0 = b' i 0 - ⌊ηN⌋ ∧ r 0 = b' i 0 + ⌊ηN⌋ ∧
              (colour σ i) ∈ localConn (fence box) l r ∧
              (colour σ i) ∈ localConn (ball of radius ⌊√ηN⌋ around b' i) x l)}
```

Crossings as in `separation-a.md` (open: rows `0` to `N`, support in `Q`; dual: faces from row `-1`
to row `N`, faces in `Icc ![0, -1] ![4N - 1, N]`, dual edges in `dualConfig ω` crossing edges of
`Q`); positions doubled (`2 x` open, `2 x + 1` dual); disjoint: open–open vertex-disjoint,
dual–dual face-disjoint. The dual fence box is the box of faces `[x - ⌊ηN⌋, x + ⌊ηN⌋] × [N, N + ⌊√ηN⌋]`
above the landing face `(x, N)`.

## What A2c-2 has to do

1. **Determination and measurability** of: `{exploration of G up to v = A}` (determined by the
   finite set `{e ∈ edgeSet | ∃ f ∈ dualEdge e, f ∈ A v}`, by `exploration_iff_of_agree`;
   measurable by `measurableSet_of_determined_finite` in `Percolation/Bond/CrossEdge.lean`) and of
   the three protection events at a scale (determined by the edges outside `E` with both ends in
   the annulus; `mem_crossing_iff_of_inter_eq` in `CriticalProbability.lean`). Disjoint annuli at
   scales `s₀ 4^j` (`pairwiseDisjoint_blockingAnnulus` pattern).
2. **Sum over exploration sequences**: the candidates restricted to `[0, v]` are functions
   `Fin (v + 1) → (subsets of the dual box)`, a finite type; the events `{exploration = A}` are
   pairwise disjoint (`exploration_unique`), so `Σ_A P(X_A ∩ fail_A) ≤ (1 - β)^J Σ_A P(X_A) ≤ (1 - β)^J`.
3. **Strip shape** (item 8 of `separation-b.md`): run the exploration in `Q = Icc 0 ![4N, N]`
   itself; its chosen crossings are disjoint crossings of the wider box
   `Icc 0 ![5 (N - 1), N]` (`N ≥ 5`), so `mem_foldl_crossing_of_walks` and
   `law_foldl_crossing_one_le_pow` (`k = 5`, `n = N - 1`) bound step (a). Same for the dual box.
4. **The dual instance: use `G = dualConfig ω`, not `dualConfig ω ∩ S`.** With `S` (dual edges
   crossing edges of `Q`) the dual configuration is empty above the strip and no dual fence exists.
   Clean greedy dual crossings in the face box `Icc ![0, -1] ![4N - 1, N]` use only dual edges
   crossing edges of `Q` anyway (row `-1` only at the start, row `N` only at the end), and members
   of the family are crossings of `dualConfig ω`. `law_exploration_dualConfig_le_pow` applies with
   `S = univ`. Lower bounds in face coordinates: same colour `pow_le_law_dualConfig_notMem_crossing_add`;
   other colour via `dualConfig_dualConfig` (the dual of the dual is the shifted configuration) and
   `pow_le_law_compl_crossing_inter_add`; fence via box duality (four dual long crossings = four
   open short crossings absent) and `pow_le_law_compl_crossing_inter_add`.
5. **Scales**: separation `s ∈ [2√ηN, η^{1/4} N]` dyadic (blocking range `s`, doubled `2s ≥ 4√ηN`);
   fence `t` with `⌊ηN⌋ ≤ 3t` and `3t + 1 ≤ ⌊√ηN⌋`; corners `s ∈ [2√ηN, η^{1/4} N]`, which also
   keeps every tip at least `√ηN + 1` from the corners so the fence annulus fits horizontally.
   Each range has `≍ log (1/η)` dyadic scales. Union bound:
   `2 (1 - c 6)^(T + 1) + 2 (T + 1) · 3 (1 - c 7 ^ 4)^J + 4 (1 - c 7 ^ 4)^J`; choose `T`, then `η`, then
   `N₀` so that every range is non-empty and `N ≥ 5`.
6. **Surgery output**: the fence lemma needs each rerouted crossing to be clean at the top and
   open after the removals of its step (vertices off the chosen crossings of smaller index).
   `exists_reroute_of_exploration` does not state the second property; it holds by construction
   (`exists_reroute_aux`: each prefix meets no chosen crossing of smaller index before its cut).
   Add that conjunct to `exists_reroute_of_exploration` (a strengthening of a proved, untagged
   statement). Clean the given family first: cut each member at its first top-row vertex (first
   top-row face for dual members); starts are unchanged and disjointness is kept.
7. **Assembly**: on the good event, apply the surgery once per colour, then `lt_sub_of_exploration`
   (same colour), `false_of_localConn_of_exploration` in both explorations (mixed pairs: the dual
   greedy crossing without its first and last face is a walk of the dual box of the open
   exploration; the open crossing shifted by `(-1, -1)` is a walk of the dual box of the dual
   exploration), the corner lemmas, and `exists_fence_of_exploration`.

## Search

* PercLib: `CriticalProbability.notMem_localConn_of_notMem_crossing`, `mem_crossing_iff_of_inter_eq`;
  `MultiArmBounds.pow_le_law_compl_crossing_inter`, `pow_le_law_crossing_inter`,
  `law_le_one_sub_pow_of_blocking`, `law_translate_apply`; `CrossingBounds.translate`;
  `Defs.image_add_mem_crossing_iff`, `image_add_inter_edgeSet_mem_localConn_iff`,
  `dualConfig_image_add`; `Gluing.exists_mem_support_of_dualConfig_mem_localConn`,
  `exists_mem_support_of_crossing_walks`; `CrossingSymmetry.exists_walk_mem_Icc`;
  `DeterminedIndependence.prodBernoulli_inter_of_determined`, `prodBernoulli_biInter_of_determined`,
  `determined_biInter`; `CrossEdge.measurableSet_of_determined_finite` (for A2c-2). No existing
  lemma for top separation, cleaning a walk at both ends, a sub-walk between two support vertices,
  or the last entry from above; they were added.
* Mathlib: `Walk.bypass_isPath`, `IsPath.of_append_left`, `IsPath.reverse`, `takeUntil`/`dropUntil`
  API, `Finset.prod_le_prod`, `prob_compl_eq_one_sub`.

## Lessons

* A tactic block inside parentheses that spans lines (`(by simp only [a,\n b]; omega)`) does not
  parse when the continuation line is indented less than the tactic: write `?_` and prove it in a
  bullet.
* `simp only [...] at h₁ h₂\n    h₃` does not parse either: split the `at` list.
* In `z + ![3 * s, -s]` with `s : ℕ` the vector elaborates over `ℕ` (heterogeneous `+`): write
  `![3 * (s : ℤ), -s]`.
* Under `--wfail`, `simp only` arguments must all be used: `Matrix.cons_val_one` is unused on
  goals about coordinate `0`.
* `Finset.prod_le_prod'` is deprecated; `Finset.prod_le_prod` takes one argument here.
* The module builds in 7–10 s per iteration; every lemma compiled after one or two rounds.

## Sources

* P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
  no. 55, §4.2 (Definitions 6–8, (4.3)–(4.5)), §4.4, Lemma 15. Read this session:
  arXiv:0711.4948v1 through its HTML rendering (Lemma 14 there; the PDF did not decode), via a
  subagent.
