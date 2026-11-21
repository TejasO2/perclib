# The RSW key step on ℤ²: advice for the wiki

Advice for the wiki agent on package P3 of the RSW plan
(`PercLib/Models/Planar/RSWKeyStep.lean`). This is Step 4 of the wiki's proof of WD31
(`critical-exponents`, §"The square-lattice crossing input") and Lemma 6 of Bollobás–Riordan.
Everything is proved with only `propext`, `Classical.choice` and `Quot.sound`; no tags were
added.

## Statements as proved

Conventions as in `duality.md` and `gluing.md`: boxes are `Set.Icc lo hi` on `Fin 2 → ℤ`,
`crossing 0` is left-right, `crossing 1` bottom-top, and the dual vertex `f` is the face with
lower-left corner `f`. So the wiki's dual box `S^v = [-½, n + ½] × [½, n - ½]` is
`Sv = [-1, n] × [0, n - 1]` in the Lean.

- **Key step** (`law_crossing_zero_mul_law_crossing_one_le`): let `q` be a profile constant,
  equal to `p`, on the edges of `ℤ²`, let `1 ≤ n ≤ m`, `S = [0, n]²` and
  `R = [0, m] × [0, 2n]`. Then

  `P(H(R)) · P(V(S)) ≤ 2 · P(X(R))`,

  where `X(R)` is the event that some vertex `c` of `S` is joined by open edges inside `S` to a
  vertex on the bottom of `S` and to a vertex on the top of `S`, and by open edges inside `R` to
  a vertex on the right side of `R`. The inequality is in `ℝ≥0∞`; it is the wiki's
  `P_p(X(R)) ≥ ½ P_p(H(R)) P_p(V(S))`.

  The wiki states `X(R)` with an open bottom-top path `P₁` of `S` and an open path `P₂` of `R`
  from a vertex of `P₁` to the right side. The two forms are the same event. Any vertex of `P₁`
  where `P₂` starts serves as `c`. Conversely, the walk from the bottom through `c` to the top
  contains a bottom-top path `P₁` of `S` that starts at the same bottom vertex (it need not pass
  through `c`); the walk from the right side of `R` to `c` and on to that bottom vertex ends on
  `P₁`, and cut at its first vertex on `P₁` it gives `P₂`. No definition of `X(R)` was
  introduced; the event is written out in the statement.
- **The boundary of a dual set crossing the dual box** (`mem_crossing_one_boundary`): if a set
  `D₀` of faces contains the left column of `Sv` and no face in its right column, then the edges
  of `ℤ²` whose duals lie in `Sv` and have exactly one end in `D₀` contain a bottom-top crossing
  of `[0, n]²`. This is the wiki's "deterministic configuration" paragraph of Step 4.
- **Separation in the key step** (`exists_walk_unexplored`): if `D₀ ⊆ Sv` is joined to the left
  column by walks inside `D₀`, `γ` is a bottom-top walk of `[0, n]²` each of whose edges has a dual
  end outside `D₀`, and `ρ` is the reflection in `y = n`, then every left-right crossing of `R`
  in `ω` gives, in `ω` or in `ρω`, a walk inside `R` from the right side of `R` to a vertex of
  `γ` whose edges are open and *unexplored*: neither their duals nor the duals of their
  reflections meet `D₀`. This is the wiki's `H(R) ⊆ F ∪ F'`.

General lemmas added: `SimpleGraph.Walk.exists_walk_first_mem` (a walk that visits a set has an
initial segment ending at its first visit), `exists_walk_of_mem_localConn` and
`mem_localConn_of_walk` (a connection inside `S` is a walk of `ℤ^d` in `S` with open edges),
`exists_ne_of_mem_edges`, `face_of_mem_dualEdge`, `exists_mem_le_of_dualEdge`,
`exists_dualEdge_eq`.

## Proof the Lean follows

The structure is the wiki's Step 4: condition on the dual cluster of the left side of `S^v`,
choose a crossing `γ₀` inside the boundary of each admissible value, glue it to its reflection,
and use independence and the reflection symmetry. The differences are these.

1. *The dual cluster.* `D(ω)` is the cluster of the face `(-1, 0)` in the configuration made of
   the dual-open edges with both ends in `Sv` together with the dual edges of the left column of
   `Sv`, which are declared open. This is the wiki's `D` (the set of faces joined to the left
   side inside `S^v`, the left side included).
2. *Determination.* `{D = D₀}` is determined by the edges of `ℤ²` whose duals have an end in
   `D₀` (`cluster_eq_finset_determined`). The wired left-column edges are the same in every
   configuration, so they need not be excluded as in the wiki.
3. *Admissible values.* The Lean sums over the finite sets `D₀ ⊆ Sv` with no face in the right
   column that are values of `D`. Every such set contains the left column and is joined to it
   inside itself, which the separation step uses. Other sets give empty events, so the union is
   the wiki's.
4. *Separation without the parity function.* The wiki proves `H(R) ⊆ F ∪ F'` with the parity
   function `N` (facts F5–F7). The Lean uses the separation lemma of `Gluing.lean` instead
   (see `gluing.md`). Follow the left-right crossing backwards from the right side of `R` to its
   first vertex `k` that lies on `τ₀` (the bottom-top walk `γ₀` glued to `ργ₀`) or is an endpoint
   of an explored edge or of the reflection of one. If `k` were an endpoint of an explored edge,
   the dual walk inside `D₀` from the left column to a face at `k` crosses no edge of `τ₀`: not
   `γ₀`, whose edges have exactly one dual end in `D₀`, and not `ργ₀`, which lies in `y ≥ n`
   where no dual edge of `Sv` crosses. Then the separation lemma makes the crossing meet `τ₀`
   before `k`, a contradiction. The reflected case is the same after applying `ρ`.
5. *The fresh event.* `F` is defined through the unexplored edges, those `e` such that neither
   the dual of `e` nor the dual of `ρe` meets `D₀`, in place of the wiki's set `Ω`:
   `F = {some vertex on the right side of R is joined inside R to a vertex of γ₀ by open
   unexplored edges}`. It is independent of `{D = D₀}`
   (`prodBernoulli_inter_of_determined`), and `F' = ρ⁻¹F` has the same probability
   (`law_preimage_image_sym2Map_eq`).
6. *Paths and walks.* `γ₀` and the connecting paths are walks; `γ₀` is chosen with
   `Classical.choose` as a function of `D₀`, and runs from the bottom of `S` to its top.

The assembly is the wiki's last display: `V(S)` is the disjoint union of the events
`{D = D₀}` (by vertical duality, `crossing-symmetry.md`), `{D = D₀} ∩ F ⊆ X(R)`, and
`measure_biUnion_finset` gives the sum.

## Sources

B. Bollobás and O. Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math.
Soc. 38 (2006), 470–484, arXiv math/0410359v3, Lemma 6, p. 7. Their proof conditions on the
leftmost vertical crossing of `[0, n]²`; the Lean, like the wiki, conditions on the dual
cluster of the left side instead.
