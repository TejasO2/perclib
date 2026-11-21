# Crossing symmetries and vertical duality: advice for the wiki

Advice for the wiki agent on package P1 of the RSW plan
(`PercLib/Models/Planar/CrossingSymmetry.lean`). These are tools, not wiki assertions of their
own; most wiki articles use them silently ("by symmetry", "by duality"). Everything is proved
with only `propext`, `Classical.choice` and `Quot.sound`; no tags were added.

## Statements as proved

Conventions as in `duality.md`: boxes are `Set.Icc lo hi` on `Fin 2 → ℤ`, `crossing 0` is
left-right, `crossing 1` bottom-top, the dual vertex `f` is the face with lower-left corner `f`.

- **Vertical duality** (`mem_crossing_one_iff_dualConfig_notMem_crossing_zero`): for
  `lo ≤ hi`, the box `[lo₀, hi₀] × [lo₁, hi₁]` has an open bottom-top crossing iff the dual box
  `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` has no dual-open left-right crossing. Event form:
  `compl_crossing_one_eq_preimage_dualConfig`. Proved by transporting the horizontal duality
  of `Duality.lean` along the coordinate swap, which commutes with taking duals
  (`dualConfig_image_swap`).
- **Sub-crossings** (`crossing_zero_subset_crossing_zero`,
  `crossing_one_subset_crossing_one`): a crossing of a box contains a crossing of every box
  that is narrower in the crossing direction and at least as wide in the other. Proved by a
  discrete intermediate value theorem along walks
  (`SimpleGraph.Walk.exists_walk_mem_Icc`, general graphs).
- **Symmetries of crossing probabilities**, for any profile constant on the edges of `ℤ²`
  (or `ℤ^d` for the general lemmas):
  translation (`law_crossing_add`), coordinate swap (`law_crossing_one_eq_law_crossing_zero`),
  reflections in vertical and horizontal lines (`law_crossing_reflect_zero`,
  `law_crossing_reflect_one`), and any automorphism mapping boxes to boxes
  (`law_crossing_eq_of_iso`, `law_crossing_eq_of_iso_of_rev`).
- **Complement of a vertical crossing at `1/2`** (`law_compl_crossing_one_eq`): if every edge
  of `ℤ²` is open with probability `1/2` and `lo ≤ hi`, then
  `P(no bottom-top crossing of [lo₀, hi₀] × [lo₁, hi₁]) =
  P(left-right crossing of [0, hi₀ - lo₀ + 1] × [0, hi₁ - lo₁ - 1])`.

General lemmas: `mem_localConn_iff_exists_walk` (a connection inside `S` is a walk of open
edges with all vertices in `S`), `SimpleGraph.Walk.exists_walk_eq_of_le` (first passage to a
level), automorphisms `exists_iso_swap`, `exists_iso_reflect_zero`, `exists_iso_reflect_one`.

## Sources

Standard; no specific locator is needed. Vertical duality is the rotated form of planar
duality (Grimmett 1999, §11.2). The symmetry and sub-crossing facts are used without comment
in Bollobás–Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math. Soc. 38
(2006), 470–484 (arXiv math/0410359v3), §2 onwards.
