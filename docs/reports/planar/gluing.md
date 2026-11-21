# Gluing crossings on ℤ²: advice for the wiki

Advice for the wiki agent on package P2 of the RSW plan
(`PercLib/Models/Planar/Gluing.lean`). Everything is proved with only `propext`,
`Classical.choice` and `Quot.sound`; no tags were added.

## Statements as proved

Boxes are `Set.Icc lo hi` with `lo 1 < hi 1` (height at least one); walks are
`SimpleGraph.Walk`s of `zdGraph 2` with all vertices in the box. The *dual box for vertical
duality* is `R^v = [lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]`; a face `f` is *at* a vertex `v` when
`v - (1, 1) ≤ f ≤ v` coordinatewise.

- **Ring lemma** (`dualConfig_inter_mem_localConn_of_walk`): if no edge of a configuration
  `η` touches a vertex of the walk `σ`, any two faces at vertices of `σ` that lie in `R^v` are
  joined inside `R^v` by dual-open edges of `dualConfig η`.
- **Separation lemma** (`exists_mem_support_of_dualConfig_mem_localConn`): let `τ` be a
  bottom-top walk of the box and `σ` a walk in the box from its right side to `w`. If a face
  at `w` is joined to the left column of `R^v` by dual edges crossing no edge of `τ`, then
  `σ` meets `τ`.
- **Crossing lemma** (`exists_mem_support_of_crossing_walks`): a left-right walk and a
  bottom-top walk of the same box share a vertex. This is Step 1 of the wiki's proof of WD31.
- **Gluing** (`inter_edgeSet_mem_localConn_of_crossings`): in a box, an open left-right
  connection from `a` and an open bottom-top connection from `c` give an open connection from
  `a` to `c` inside the box.

## Proof the Lean follows

None of this uses planar topology (Jordan curves, faces of a planar embedding, the region
below a path). The four faces at a vertex are joined by the duals of its four edges, which
are closed when `η` avoids the vertex; consecutive vertices of a walk share a face; so the
faces along an untouched walk form a dual-connected ring (truncated to the dual box). The
separation lemma follows: if `σ` missed `τ`, the dual path from the left column, continued
along the ring around `σ` to its start on the right side, would be a dual left-right crossing
of `R^v` in the configuration formed by the edges of `τ`, which also has the bottom-top
crossing `τ`; vertical duality (`crossing-symmetry.md`) forbids both. The crossing lemma is
the case where the dual path is a single face at the left end of the left-right walk.

The wiki's WD31 proof derives the crossing lemma first and uses a parity function for the
separation in Step 4. The Lean derives both from duality instead; the wiki should say so if it
records which proof the Lean follows.

## Sources

The crossing lemma is the discrete form of the fact that a left-right and a top-bottom path of
a rectangle meet (used throughout Bollobás–Riordan, *A short proof of the Harris–Kesten
theorem*, Bull. London Math. Soc. 38 (2006), 470–484, arXiv math/0410359v3). The ring
construction is new to this formalisation; no locator applies.
