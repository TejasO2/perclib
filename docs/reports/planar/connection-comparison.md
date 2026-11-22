# Connection comparison across annuli of ℤ²: advice for the wiki

Advice for the wiki agent on package F1 of the arms-stage plan
(`PercLib/Models/Planar/Arms/ConnectionComparison.lean`). These are the two inputs of Basu and
Sapozhnikov's construction of Kesten's incipient infinite cluster, which the plan follows for
FM8D (`size-biased-laws`, §"The planar lattice construction"): (A1), uniqueness of the open
crossing cluster of an annulus, and (A2), the comparison of connection probabilities across an
annulus. Both are proved on `ℤ²` for **every profile that opens each edge with probability at
least `1/2`**, with constants that do not depend on the profile, so they hold uniformly in
`p ∈ [1/2, 1)` (that is, `β ≥ log 2`), as the two limits of FM8D need. The package also proves
circuit gluing in annulus form. Everything uses only `propext`, `Classical.choice` and
`Quot.sound`; no tags and no definitions were added (proof-only, 19 theorems).

## Conventions

As in `arm-events.md` and `separator.md`: boxes are `Set.Icc lo hi` on `Fin 2 → ℤ`,
`(r : LatticeSite 2)` is the constant vector `r`, so `Icc (z - r) (z + r)` is
`B_r(z) = z + [-r, r]²`, and `B_{r-1}(z)` is written `Icc (z - r + 1) (z + r - 1)` (empty for
`r = 0`). `∂B_r(z)` is `boxBoundary (z - r) (z + r)` (`arms-interface-a.md`). Only the open
nearest-neighbour edges `ω ∩ (zdGraph 2).edgeSet` are read. "`X ↔ Y` in `Z`" is the event
`{ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ (zdGraph 2).edgeSet ∈ localConn Z x y}`: an open path all of whose
vertices lie in `Z`. "Profile at least `1/2`" is the hypothesis
`∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e`; nothing is assumed off the edges. Probabilities
are in `ℝ≥0∞`. The **circuit event of the annulus `a ≤ ‖v - z‖∞ ≤ b`** is the intersection of the
four long-direction crossings of its strips: left-right crossings of `z + [-b, b] × [a, b]` and
`z + [-b, b] × [-b, -a]`, bottom-top crossings of `z + [a, b] × [-b, b]` and
`z + [-b, -a] × [-b, b]`. For `a = 2n`, `b = 4n` it is `fourStrip z n`.

## Statements as proved

**Circuit gluing in annulus form.**

- `inter_edgeSet_mem_localConn_of_mem_annulus_crossings`: for `a < b`, on the circuit event of the
  annulus `a ≤ ‖v - z‖∞ ≤ b`, if `x, x' ∈ B_a(z)`, `y, y' ∉ B_{b-1}(z)`, `x ↔ y` in `W` and
  `x' ↔ y'` in `W'`, then `x ↔ x'` in `W ∪ W' ∪ (B_b(z) \ B_{a-1}(z))`. The sets `W`, `W'` are
  arbitrary; the joining path uses only the annulus and the two paths. This is the plan's
  "annulus form" (§4.2, dependency note for P6), for every pair of radii.
- `inter_edgeSet_mem_localConn_union_of_mem_fourStrip`: the same on `fourStrip z n`, with
  `x, x' ∈ B_{2n}(z)`, `y, y' ∉ B_{4n-1}(z)` and the annulus `B_{4n}(z) \ B_{2n-1}(z)`; no
  `n ≥ 1` (for `n = 0` both points are the centre).

**(A2), Basu–Sapozhnikov (1.2) on `ℤ²`.**

- Lower bound, `exists_pos_mul_le_law_setOf_localConn`: there is `c > 0` such that for every
  profile at least `1/2`, every centre `z`, every `m ≥ 1`, every `Z ⊇ B_{4m}(z) \ B_{m-1}(z)`,
  every `X ⊆ B_m(z)` and every `Y` with no point in `B_{4m}(z)`,
  `c · P(X ↔ ∂B_{2m}(z) in Z) · P(Y ↔ ∂B_{2m}(z) in Z) ≤ P(X ↔ Y in Z)`.
- Upper bound with the same factors, `law_setOf_localConn_le_mul`: for **every** profile, every
  `r`, every `X ⊆ B_r(z)`, every `Y` with no point in `B_r(z)` and every `Z`,
  `P(X ↔ Y in Z) ≤ P(X ↔ ∂B_r(z) in Z) · P(Y ↔ ∂B_r(z) in Z)`.
- Upper bound in the plan's form, `law_setOf_localConn_le_mul_inside_outside`: same hypotheses,
  `P(X ↔ Y in Z) ≤ P(X ↔ ∂B_r(z) in Z ∩ B_r(z)) · P(∂B_{r+1}(z) ↔ Y in Z \ B_r(z))`.
- Both directions, `exists_law_setOf_localConn_comparable`: under the hypotheses of the lower bound,
  `c · f · g ≤ P(X ↔ Y in Z) ≤ f · g` with `f = P(X ↔ ∂B_{2m}(z) in Z)`,
  `g = P(Y ↔ ∂B_{2m}(z) in Z)`.

**(A1), Basu–Sapozhnikov (1.3)–(1.4) on `ℤ²`.**

- `exists_law_inter_setOf_crossing_clusters_le`: there is `c₀ > 0` such that for every profile at
  least `1/2`, every measurable increasing event `E`, every centre `z` and all `N ≥ 1`, `k` and
  `M ≥ 4^k N`, the probability that `E` holds and the annulus `A = B_M(z) \ B_{N-1}(z)` has two
  distinct open crossing clusters is at most `(1 - c₀)^k · P(E)`. "Two distinct crossing
  clusters" is spelled out: points `a, a' ∈ ∂B_N(z)` and `b, b' ∈ ∂B_M(z)` with `a ↔ b` and
  `a' ↔ b'` in `A` but not `a ↔ a'` in `A`. With `E` the whole space this is (1.3).
- `exists_cond_setOf_crossing_clusters_le`: the conditional form (1.4): given
  `∂B_N(z) ↔ ∂B_M(z)` in `A` (`ProbabilityTheory.cond`), two distinct crossing clusters have
  probability at most `(1 - c₀)^k`. This is Basu–Sapozhnikov's `ε_i` bound with
  `N_{i+1} = 4^{k_i} N_i`.
- Building block, `exists_law_inter_biInter_compl_fourStrip_le`: for every profile at least `1/2`,
  every measurable increasing `E`, every finite index set `s` and scales `n j ≥ 1` with
  `2 n_j < n_{j'}` for `j < j'`, `P(E ∩ ⋂_{j ∈ s} (fourStrip z (n j))ᶜ) ≤ (1 - c₀)^{#s} P(E)`.

**General tools added on the way** (none mentions anything new to the wiki):
`exists_law_le_of_half_le` (a profile at least `1/2` dominates, on increasing events, a profile
equal to `1/2` on the edges), `exists_pos_le_law_crossing_of_half_le` and
`exists_pos_le_law_fourStrip_of_half_le` (RSW in any position and T4 for profiles at least
`1/2`), `exists_pos_le_law_annulus_crossings` (circuit event of `a ≤ ‖v - z‖∞ ≤ 2a`, any `a ≥ 1`,
probability at least `c`), `exists_mem_boxBoundary_mem_localConn_inter` /
`exists_mem_boxBoundary_mem_localConn_diff` (an open path inside `U` stopped at its first
visit to `∂B_r(z)`, from inside or from outside), `exists_mem_support_of_walks_of_rows_of_cols`
(two open walks crossing a box in perpendicular directions, each staying in the box's rows,
respectively columns, meet), `measurableSet_setOf_exists_inter_mem_localConn` and
`isUpperSet_setOf_exists_inter_mem_localConn` (set-to-set connections, `Bond` namespace).

## Proof the Lean follows

1. *Circuit gluing.* Adjacent strip crossings meet in a corner square: in the square
   `z + [a, b]²` the top crossing has a left-right segment and the right crossing a bottom-top
   segment (discrete intermediate value theorem along a walk), and these meet by the crossing
   lemma of `gluing.md` (`exists_mem_support_of_crossing_walks`). Three corners join the four
   crossings, and every vertex of them is joined to the start of the top crossing inside the
   annulus. A path from `B_a(z)` to outside `B_{b-1}(z)`, stopped at its first visit to
   `∂B_b(z)`, stays in `B_b(z)`; according to the side it reaches, a segment of it crosses that
   side's strip in the short direction and meets the strip's crossing (same lemma). This differs
   from `separator.md`, which glues the four crossings as crossings of the whole box `B_{4n}(z)`
   and so only joins inside `B_{4n}(z)`; the corner squares keep every connection in the
   annulus.
2. *(A2), lower bound.* Five increasing events: the two arms, the circuit event of the annulus
   `[m, 2m]`, that of `[2m, 4m]`, and a left-right crossing of the rectangle `z + [m, 4m] × [0, m]`.
   The rectangle crossing starts in `B_m(z)` and ends outside `B_{4m-1}(z)`, so it is a path
   crossing both annuli. Circuit gluing in `[m, 2m]` joins `x ∈ X` (its arm reaches `∂B_{2m}`) to
   the start of the rectangle crossing; circuit gluing in `[2m, 4m]` joins the end of the arm
   from `Y` (a point of `∂B_{2m}`) to the same point; all inside `Z`, because the annuli and the
   rectangle lie in `B_{4m}(z) \ B_{m-1}(z) ⊆ Z`. Harris's inequality (X5SS) four times gives
   `P(X ↔ Y in Z) ≥ c_C² c_R · f · g`, where `c_C = c₄⁴` bounds each circuit event (four `4a × a`
   boxes, RSW with `k = 4`) and `c_R` the rectangle (`3m × m`, RSW with `k = 3`). For profiles
   above `1/2` all five events are increasing, so each bound passes from the profile equal to
   `1/2` on the edges by the monotone coupling (`prodBernoulli_mono_event`). The plan's
   "radius shift with one RSW extension step" is not needed: the inner circuit is placed in
   `[m, 2m]` directly (for odd `m` that annulus is not a four-strip annulus, hence general radii
   in item 1).
3. *(A2), upper bounds.* A path from `x ∈ X` to `y ∈ Y` inside `Z`, stopped at its first visit to
   `∂B_r(z)`, gives `X ↔ ∂B_r` in `Z ∩ B_r`, which reads only the pairs inside `B_r(z)`. Run from
   `y`, the path up to its first visit to `B_r(z)` uses only pairs not inside `B_r(z)` (two
   consecutive vertices cannot both be that first visit). The two families of pairs are
   disjoint, so the events are independent (`prodBernoulli_inter_of_determined`); enlarging
   each to `X ↔ ∂B_r in Z` and `Y ↔ ∂B_r in Z` gives the same-factor bound. For the plan's form,
   the path from `y` stopped at its first visit to `∂B_{r+1}(z)` stays outside `B_r(z)`, and
   independence of the pairs inside `B_r(z)` and inside its complement
   (`law_inter_of_determined_internalPairs`) concludes.
4. *(A1).* The annulus `B_M \ B_{N-1}` contains the `k` four-strip annuli
   `2 · 4^j N ≤ ‖v - z‖∞ ≤ 4^{j+1} N`, `j < k`, which are disjoint. If one of their four-strip
   events holds, circuit gluing in annulus form (with `W = W' = A`) joins any two crossings of `A`
   inside `A`; so two distinct crossing clusters force all `k` events to fail. That event is
   decreasing, hence negatively correlated with the increasing `E`
   (`prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet`); the `k` events are independent
   (`law_biInter_of_determined_internalPairs`, determination by `mem_fourStrip_iff_of_inter_eq`)
   and each fails with probability at most `1 - c₀` (T4 for profiles above `1/2`).

## Statement choices compared with the plan

The plan states F1 in prose (§4.2 steps 1–2, §7, §9); no Lean signature was drafted. Each
choice below makes a theorem stronger than the plan's wording or the source's.

- (A2): Basu–Sapozhnikov require `Z` finite and connected, `X ⊆ Z ∩ B(m)` and `Y ⊆ Z \ B(4m)`;
  the Lean asks only `Z ⊇ B_{4m} \ B_{m-1}`, `X ⊆ B_m`, `Y` outside `B_{4m}`. Their balls are
  graph-metric balls of a general graph; on `ℤ²` the plan uses sup-norm boxes, as their §3 does
  for slabs. `p ∈ [p_c, p_c + δ]` becomes every profile at least `1/2` on the edges, with one
  constant.
- (A2), upper bound: the plan's form (with `∂B_{2m+1}` and `Z \ B_{2m}`) is proved at every
  radius `r`, and so is the bound with the same factors as the lower bound. The same-factor
  form is what Basu–Sapozhnikov's cross-ratio bound (2.7) needs: with
  `c f g ≤ P ≤ f g`, the ratio `M(1,1')M(2,2') / (M(1,2')M(2,1'))` is at most `c⁻²`, i.e.
  `κ = c⁻¹` as they state. With the plan's form alone the second factors differ
  (`P(∂B_{r+1} ↔ Y in Z \ B_r) ≥ P(Y ↔ ∂B_r in Z)`), and an extra comparison would be needed.
- (A1): the bound holds jointly with any measurable increasing event `E`, not only after
  conditioning on the crossing event; `M ≥ 4^k N` instead of `M = 4^k N`. The conditional form is
  the instance `E = {∂B_N ↔ ∂B_M in A}`. Basu–Sapozhnikov's (A1) is uniqueness of the infinite
  cluster, with (1.3)–(1.4) as equivalent forms; on `ℤ²` the quantitative form is proved
  directly, with the rate `(1 - c₀)^k`.
- Circuit gluing in annulus form is stated for every `a < b`, not only for four-strip annuli,
  because (A2) needs the annulus `[m, 2m]` for odd `m`.

## Where it is used

F3 (Basu–Sapozhnikov (2.2)–(2.7)): `ε_i ≤ (1 - c₀)^{k_i}` is
`exists_cond_setOf_crossing_clusters_le` (or the unconditional form with
`E = {∂B_{N_i} ↔ ∂B_{N_{i+1}}}`); (2.2) uses the lower bound of (A2) twice; (2.7) uses
`exists_law_setOf_localConn_comparable`. In their (2.7) the set `R` lies on `S(N_{i+1} + 1)`,
outside `B(N_{i+1})`; on `ℤ²` take `m = N_{i+1} + 1`, so that `R ⊆ B_m` and the explored set
`U ⊆ B_{N_{i+1}} = B_{m-1}` stays out of the annulus `B_{4m} \ B_{m-1}`. F4 (uniqueness under
`ν`): `exists_law_inter_biInter_compl_fourStrip_le` with `E = armEvent 0 (r + 1)` and scales
`n_K, …, n_{K+M}`, then `inter_edgeSet_mem_localConn_union_of_mem_fourStrip`.

## Search

PercLib: `localConn` and `conn` are point-to-point and `crossing` is between faces of a box; no
set-to-set connection notion, so the event is written out in each statement (a definition, and
one for the circuit event of a general annulus, which generalises `fourStrip`, could be proposed
in a later interface package if F3 repeats them). No comparison of a profile at least `1/2`
with the profile `1/2`: the monotone coupling `prodBernoulli_mono_event`
(`Probability/Coupling/Monotone.lean`) does it in three lines. Circuit gluing existed only in box
form (`separator.md`). The stopping lemmas `exists_first_exit` (`Bond/FirstExit.lean`) and
`exists_boundary_mem_localConn_of_mem_conn` (`separator.md`) take unconfined connections, so the
two first-passage lemmas inside a set were added (from `SimpleGraph.Walk.exists_walk_eq_of_le`,
`crossing-symmetry.md`); the first visit to a set is `SimpleGraph.Walk.exists_walk_first_mem`
(`RSWKeyStep.lean`). Mathlib: `SimpleGraph.Walk.transfer`, `takeUntil`,
`fst_mem_support_of_mem_edges`, `ProbabilityTheory.cond_apply`, `Finset.prod_le_pow_card`,
`isLowerSet_iInter₂`. Reused library lemmas: `exists_mem_support_of_crossing_walks`
(`Gluing.lean`), `exists_pos_le_law_crossing` (`RSW.lean`), `exists_pos_le_law_fourStrip`,
`mem_fourStrip_iff_of_inter_eq`, `inter_mem_localConn_iff_of_inter_eq`, `mem_boxBoundary_two_iff`
(`Arms/`), `prodBernoulli_harris` (X5SS), `prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet`,
`prodBernoulli_inter_of_determined`, `law_inter_of_determined_internalPairs`,
`law_biInter_of_determined_internalPairs`.

## Sources

D. Basu and A. Sapozhnikov, *Kesten's incipient infinite cluster and quasi-multiplicativity of
crossing probabilities*, Electron. Commun. Probab. 22 (2017), doi:10.1214/17-ECP56,
arXiv:1603.06884v2. Read in the arXiv HTML rendering: §1, assumptions (A1) and (A2), (1.2),
the equivalent forms (1.3)–(1.4) of (A1), Theorem 1.1; §2, the scales `N_i`, the events `F_i`,
`ε_i`, (2.2), the sets `C_i, D_i` (2.3), the transfer matrices and the cross-ratio bound (2.7);
§3, Lemma 3.2 and (3.1) (the slab version with annuli `An(m, 3m)`). Their (3.2) and the rest of
§3 were not read reliably, and journal page numbers were not checked. No wiki tag corresponds to
(A1) or (A2); they are steps of the proof of FM8D, which the wiki attributes to Kesten (1986,
Theorem 3) and Basu–Sapozhnikov (2017). The circuit construction is that of XB1U's proof
(`separator.md`).
