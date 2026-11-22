# Local separation, part A2b: the rerouting surgery, packs included

Advice for the wiki agent and for the next session on package A2 of the arms plan (Nolin's local
separation lemma, EJP 2008, Lemma 15). A2 is **still not finished**, but the open point of A2a-1
is closed: the surgery that reroutes a family of disjoint crossings to greedy tips is proved for
every family, including packs of same-colour crossings in one cluster. What is left is the
protection of the greedy tips, the assembly over exploration sequences, and the final statement
(called A2c below).

This part adds the new file `PercLib/Models/Planar/Arms/SeparationSurgery.lean` (876 lines,
13 theorems) and one theorem to `Arms/Separation.lean`. Both are proof-only: no definition, no
tag, no `…Input`; `Arms/Defs.lean` and `Planar/Defs.lean` are unchanged. Everything uses only
`propext`, `Classical.choice` and `Quot.sound`.

## What the source says (checked this session)

Read: arXiv:0711.4948v1, the PDF, pages 23-26 (printed page numbers). There the lemma is
Lemma 14; in the journal it is Lemma 15 (p. 1579 per the plan's locators; the journal PDF was not
re-read). The proof has no numbered steps; the "step (f)" of `separation-a.md` was a label of the
earlier paraphrase, not of the paper.

* **Domain** (p. 23, Figure 7): a U-shaped `N x 4N` region `U_N^{1,ext}`; crossings join two
  marked parts of its boundary. "Lowest" means closest to the bottom side, and `z_u` is the end on
  the right side. The model is site percolation on the triangular lattice.
* **Few crossings** (p. 23, (4.12)): RSW plus BK.
* **Corners and greedy crossings** (p. 24). The corners `Z±` are protected by circuits of both
  colours in dyadic annuli. As printed, the annulus ranges have their exponents reversed: a range
  like `eta^{3/8} <= 2^{l-1} < 2^l <= sqrt(eta)` is empty for `eta < 1`. The greedy family is
  defined there too: `c_1` is the lowest monochromatic crossing **of either colour**, and `c_u`
  the lowest one disjoint from `c_1, …, c_{u-1}`.
* **Conditioning** (p. 24): on the first `u` crossings, the sites above `c_u` are unexplored. Each
  `z_u` is "protected from above" by a circuit of the opposite colour, a circuit of the same colour,
  and a third circuit that gives a small extension (the fence).
* **Rerouting** (pp. 25-26). The family `c'_1, …, c'_{t'}` is ordered. `c'_1` meets some `c_v`
  by maximality; let `c_{v_1}` be the lowest one it meets. The piece of `c'_1` after its **last**
  intersection with `c_{v_1}` is replaced by the matching piece of `c_{v_1}`, up to its end. For
  `c'_2`, the lowest crossing `c_{v_2}` it meets has `v_2 > v_1`. The paper's reason is a short
  phrase that names `c_1` where `c'_1` is presumably meant. Then the paper says "the same
  reasoning applies".
* The paper gives **no argument that the rerouted crossings are disjoint**. It does not treat
  consecutive same-colour crossings (packs) separately, and it uses no cluster or Menger-type
  argument. Its matching by least index, with `v_1 < v_2 < …`, is meant to cover packs like any
  other family.

## The source's rule fails, and so does the first-intersection variant

Coordinates below follow the library's convention: crossings run from bottom to top, and
"lowest" becomes "leftmost".

1. **Last intersection** (the rule as written). The counterexample of `separation-a.md` is
   correct against the paper's own wording: in the strip `[0, 3] x [0, 1]`, take the greedy
   crossings `x = 0` and `x = 2`. Then
   `c'_k = (0.5, 0) → (0.5, 0.2) → (0, 0.2) → (2, 0.7) → (0, 0.8) → (1, 1)` and
   `c'_l = (3, 0) → (2, 0.5) → (2.5, 1)` are disjoint, but their rerouted versions both pass
   through `(2, 0.7)`.
2. **First intersection with the same matching** (the fix suggested in `separation-a.md`) also
   fails. Strip `[0, 6] x [0, 1]`, greedy crossings `x = 0, 2, 4` (each is the leftmost crossing
   avoiding the earlier ones: all other open edges in the gaps are dead ends once the earlier
   crossings' vertices are removed).
   * `c'_l = (5, 0) → (4, 0.2) → (5, 1)` meets only `x = 4`, first at `(4, 0.2)`.
   * `c'_k = (4.5, 0) → (4, 0.1) → (2, 0.3) → (4, 0.6) → (4.5, 0.65) → (4, 0.7) → (2, 0.8)
     → (0, 0.85) → (1, 1)` stays left of `c'_l`. Its least-index greedy crossing is `x = 0`, first
     met at `(0, 0.85)`.
   * Before that point, `c'_k` passes through `(4, 0.6)` on `x = 4`, above `(4, 0.2)`. So the two
     rerouted crossings meet at `(4, 0.6)`.

   Here a disjoint rerouting exists: cut `c'_k` at `(2, 0.3)` and send it up `x = 2`. The matching
   by least index is the problem, not the lemma.

Neither failure is a problem with the statement: Lemma 15 is true and is not narrowed.

## The rule proved here (right to left)

Order the members of one colour by their starting points on the bottom row. Let `W` be the number
of greedy crossings. Treat the members from right to left. The rightmost member is cut at its
first vertex on any greedy crossing; say that crossing has index `w`. The next member to the left
is cut at its first vertex on a greedy crossing of index `< w`, and so on. Each member keeps its
part before the cut and then follows the greedy crossing it reached to its top end.

Why it works. Every claim comes from one tool, the separation lemma of `Gluing.lean`, applied in
the box **extended by one row below the bottom row**: a bottom-top walk `τ` separates the points of
the bottom row on its right from every face that is joined to the left column without crossing
`τ`. Two kinds of faces are used.

* **The faces of the explored cluster at a vertex of a chosen crossing.** Its dual paths cross
  only edges that are closed after the removals, or wire the left column outside the box, so they
  cross no walk that is open after the removals.
* **The face below a bottom-row point left of `τ`.** Its path runs along the extra row and
  crosses only the edge below the start of `τ`.

The three claims, for members `k` left of `r`:

* **Existence.** `k` meets a greedy crossing of index `< w_r`. Otherwise `τ = c'_k` is open
  after the removals, and the cut prefix of `c'_r` reaches an explored face from the right without
  meeting it.
* **Neighbours.** The prefix of the left neighbour `r'` avoids the greedy part of `r`. Otherwise,
  with `p` the common vertex, `τ = c'_{r'}[..p] ++ g_{w_r}[p..]` is open after the removals, and
  the prefix of `r` reaches the explored face at its cut from the right without meeting it. This
  uses that the greedy part is a path, so the cut of `r` is not on `g_{w_r}[p..]`.
* **Far members.** A member left of `r'` avoids all of `r`. The new walk of `r'` runs from bottom
  to top and separates the two (the second kind of face).

Packs need nothing special: same-colour members of one cluster are handled like any others. Open
and dual members never conflict (an open path and a dual path never share a vertex or a face), so
the surgery runs once per colour: on `G = ω` in the strip, and on `G = dualConfig ω ∩ S` in the box
of faces.

## Statements proved

`SeparationSurgery.lean`:

| Theorem | Statement |
|---|---|
| `SimpleGraph.Walk.start_notMem_support_dropUntil` | in a path, the start is not after any other vertex |
| `SimpleGraph.Walk.mem_dropLast_support_of_ne` | a vertex other than the end is in `support.dropLast` |
| `exists_walk_row` | a walk along a row between two points, with its vertices and edges |
| `exists_mem_support_of_dualConfig_mem_localConn_below` | separation in the box extended by one row below |
| `exists_mem_support_of_lt_of_localConn` | the same, for a face joined to the left column of the dual box without crossing `τ` |
| `exists_mem_support_of_lt_of_lt` | a walk between two bottom-row points on either side of the start of `τ` meets `τ` |
| `notMem_support_of_lt_of_lt` | a bottom-top walk separates the walks starting on its two sides |
| `mem_leftColumn_of_exploration` | the explored clusters contain the left column |
| `exists_localConn_of_mem_support_of_exploration` | the explored faces at a vertex of `Γ (A v)` reach the left column without crossing any walk open after the removals |
| `exists_mem_support_of_lt_of_exploration` | existence (above) |
| `notMem_support_of_lt_of_exploration` | neighbours (above) |
| `exists_reroute_aux` | the induction from the right, with the bound `W` |
| **`exists_reroute_of_exploration`** | once the explored cluster reaches the right column, every finite family `S` of pairwise disjoint bottom-top crossings open in `G` is rerouted to walks from the same starts to the tips `d (A (w i))` of admissible chosen crossings, inside the members and the chosen crossings, open in `G`, pairwise disjoint, with `w` increasing from left to right (so distinct) |

`Separation.lean`: `law_exploration_dualConfig_le_pow`, step (a) for the exploration of
`dualConfig ω ∩ S` in the box of faces of width `k n` and height `n + 1`.

The rerouted family is returned as `γ' : ∀ i, Σ y, (zdGraph 2).Walk (a i) y` with
`(γ' i).1 = d (A (w i))` for `i ∈ S`. The `Σ` avoids a walk type depending on `w`.

## Design for the rest of A2 (A2c)

The target statement is unchanged (`separation-a.md`, "Target statement"). Members of the given
family of colour `X` go through `exists_reroute_of_exploration` for the exploration of colour `X`,
so the new family lands at greedy tips. It remains to show that, with probability `≥ 1 - δ`, all
greedy tips of both explorations are pairwise separated, are far from the top corners, and carry
fences.

1. **Clean greedy crossings.** Add a choice rule whose crossings visit the top row only at their
   end. Cut the walks of `exists_crossing_choice` at their first top-row vertex
   (`exists_append_eq_of_notMem`); a sub-walk still runs along separating edges. The exploration
   theory is generic in `Γ`, so nothing else changes.
2. **Top separation lemma.** The mirror of `exists_mem_support_of_lt_of_localConn`, with one row
   added above: a bottom-top walk `τ` ending at `d`, and a walk from a top-row point `s` with
   `s 0 > d 0` to a vertex with a face joined to the left column without crossing `τ`, meet.
   About 120 lines, the same proof as the bottom version.
3. **Same-colour blocking.** Let `γ_v = Γ (A v)` be admissible, and let `π` be a walk of faces
   crossing no edge of `G`. It starts at a face at a vertex of `γ_v` and reaches the top face row
   of the dual box at `f₁`. Then every clean walk open in `G_v`, disjoint from `γ_v`, from the
   bottom row to the top row, lands at `x ≥ f₁ 0 + 1`. The proof is the top lemma with
   `σ = nil`. The face path is the explored faces at that vertex
   (`exists_localConn_of_mem_support_of_exploration`), then the faces around the vertex, then `π`.
   It crosses no edge of the clean walk. Later greedy crossings are such walks, so tips of one
   exploration are ordered and separated by the barriers.
4. **Mixed blocking.** An open barrier from a vertex of an open greedy crossing `γ` to the top row
   at `w > z + ρ` blocks every dual crossing from landing strictly between `z` and `w`. The dual
   crossing would cross `γ` or `γ[..x] ++ barrier`, by mixed interlacing
   (`dualConfig_inter_notMem_localConn_of_interlaced`, `exists_mem_support_of_interlaced_dual`).
   No freshness is needed. The same holds with the colours exchanged. Positions are doubled.
5. **Fresh barriers from circuits (extraction).** Fix an admissible sequence `A`. A circuit of
   colour `Y` in the annulus `A(z; r, 2r)` around the tip `z` (the full annulus in `ℤ²`; `z` is on
   the top row) gives a fresh barrier. Follow the circuit clockwise from its topmost crossing of
   the vertical line through `z` until it first reaches `γ_v`: a vertex of it for `Y = X`, a face
   at one of its vertices for `Y ≠ X`. Every edge of that piece has no dual face in `A v`: the
   piece starts outside the strip and reaches `γ_v` from the right. The proof is the top lemma
   in the box extended upwards, with the piece as `σ`. The event "a fresh barrier exists" is
   determined by fresh edges, so it is independent of `{exploration = A}`
   (`exploration_iff_of_agree`, `prodBernoulli_inter_of_determined`). Since the extraction holds
   for every `ω`, its probability is at least that of the circuit event.
6. **Fences.** The target fence box `[z - ⌊ηN⌋, z + ⌊ηN⌋] x [N, N + ⌊√ηN⌋]` lies above the strip,
   in edges no exploration reads. A same-colour circuit in an annulus around `z` with radii
   between `2ηN` and `√ηN / 2` crosses the fence box left to right, because the box's bottom side
   is inside the circuit and its top side outside. Its clockwise piece down to the last stretch of
   `γ_v` inside `B(z, r₂ + 1)` gives the connection to `z` inside `B_{⌊√ηN⌋}(z)`; that piece is
   fresh, as in item 5.
7. **Probabilities.** Use circuits in dyadic annuli, from `CrossingBounds` and Harris (A1b's
   `pow_le_law_crossing_inter`, which gives `c 7 ^ 4`); events in disjoint annuli are independent.
   * Barriers of both colours at scales `2√ηN … η^{1/4}N`, fences at scales `2ηN … √ηN / 2`, and
     circuits of both colours around the two top corners (no freshness needed there). Each gives
     failure `≤ (1 - c')^K` with `K ≍ log(1/η)`.
   * Sum over exploration sequences with `A w ⊆ T` (finitely many, disjoint by
     `exploration_unique`), over steps `v ≤ T` and over both colours, plus
     `P(> T crossings) ≤ 2 (1 - c 6)^T`. Choose `T`, then `η`.
8. **Strip shape.** `law_exploration_le_pow` is stated for the box `Icc lo (lo + ![k n, n + 1])`.
   Either state Lemma 15 for that box, or add the variant "exploration in a narrower box of the
   same height inside it" (the chosen crossings are crossings of the wider box). The strip
   `[0, 4N] x [0, N]` sits in the box with `k = 5`, `n = N - 1`, `N ≥ 5`.

## Search

* PercLib: `Gluing.exists_mem_support_of_dualConfig_mem_localConn` is the only planar tool used.
  `RSWKeyStep.exists_walk_of_mem_localConn`, `mem_localConn_of_walk`, `face_of_mem_dualEdge`,
  `exists_ne_of_mem_edges`; A1's `exists_append_eq_of_notMem`; A1b's
  `dualEdge_map_add_one_dualEdge`. `IncipientCluster.localConn_mono_of_forall_mem` exists but is
  not imported here, so a walk argument is used instead (not a copy). No straight-walk lemma with
  given ends existed, so `exists_walk_row` was added.
* Mathlib: `Walk.endpoint_notMem_support_takeUntil` (the end version of the new
  `start_notMem_support_dropUntil`), `bypass_isPath`, `support_bypass_subset_support`,
  `edges_bypass_subset_edges`, `take_spec`, `List.nodup_append`, `Finset.induction_on_max_value`,
  `Finset.exists_max_image`. Still no Menger theorem; none is needed.

## Lessons

* Avoid `simp` on goals with `Function.update` under `Sigma` projections: it makes partial or no
  progress. State the `update_self` and `update_of_ne` facts as named equalities, then `rw`.
* `simp only [Matrix.cons_val_zero, Matrix.cons_val_one]` can leave `True ∧ …`, which `omega`
  rejects; add `true_and`. Unused simp arguments fail `--wfail`.
* `Int.le_induction` is not in the pinned Mathlib; induct on a natural number `b - a = n`
  instead.
* `dif_pos` is deprecated in favour of `dite_eq_left`; `Set.mem_setOf_eq` in favour of
  `mem_ofPred_eq`.
* The module builds in about 20 s per iteration. The two geometric lemmas and the induction
  compiled after one or two rounds of fixes.

## Sources

* P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
  no. 55, Section 4.4, Lemma 15. Read this session: arXiv:0711.4948v1 (PDF), Lemma 14, pp. 23-26.
* B. Bollobás, O. Riordan, *A short proof of the Harris-Kesten theorem*, Bull. London Math. Soc.
  38 (2006), proof of Lemma 6 (the exploration template).
