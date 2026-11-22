# Kesten's incipient infinite cluster, part 1 (the Basu–Sapozhnikov decomposition): advice for the wiki

Advice for the wiki agent on package F3 of the arms plan
(`PercLib/Models/Planar/Arms/IncipientCluster.lean`). It proves the first half of wiki FM8D
(`size-biased-laws`, "The planar lattice construction") by the route the wiki's proof sketch cites:
Basu and Sapozhnikov's Section 2, on `ℤ²`. The package gives the decomposition along a chain of
cuts, the estimates (2.2)–(2.7), and the **uniform Cauchy property** (2.1), (2.8): for every
cylinder event `A`, `P(A | z ↔ ∂B_n(z))` is Cauchy in `n`, uniformly over every profile that opens
each edge with probability at least `1/2`. That class contains the critical and supercritical
intensities `β ≥ log 2` (`p = 1 - e^{-β}` on the edges, `0` off them).

F4 continues the same file with the two limits, the law `ν` and uniqueness of the infinite cluster
under `ν`. Until then FM8D stays untagged. The file is proof-only: no definition, instance,
notation or tag (35 theorems). Everything uses only `propext`, `Classical.choice` and
`Quot.sound` (gate axiom audit).

## Conventions

As in `connection-comparison.md`. Boxes are `B_r(z) = Icc (z - r) (z + r)` on `Fin 2 → ℤ`, and
`B_{r-1}(z)` is written `Icc (z - r + 1) (z + r - 1)`. The sphere `∂B_r(z)` is
`boxBoundary (z - r) (z + r)`. Only the open edges `ω ∩ (zdGraph 2).edgeSet` are read.
"`X ↔ Y` inside `Z`" means an open path all of whose vertices lie in `Z`. The arm event
`z ↔ ∂B_n(z)` is `armEvent z n`; FM8D's `0 ↔ Q_r^c` is `armEvent 0 (r + 1)`. Conditional
probabilities are `ProbabilityTheory.cond (law q) (armEvent z n) A`, read through `.toReal`. A
profile *at least `1/2`* means `∀ e ∈ (zdGraph 2).edgeSet, (1 / 2 : ℝ) ≤ q e`, with nothing
assumed off the edges.

**Cuts.** A cut has radii `a < c < b` around `z`, and its annulus is `B_b \ B_{a-1}`.
- Its *cluster* `W` is the set of vertices joined to the middle sphere `∂B_c` inside the annulus.
- Its *inner port* `Y` is the set of points of `B_{a-1}` with an open edge to `W`.
- Its *outer port* `R` is the set of points outside `B_b` with an open edge to `W`.
- It is *linked* when every crossing of the inner half `B_c \ B_{a-1}` is joined inside the
  annulus to every crossing of the outer half `B_b \ B_{c-1}` (stated with the endpoints on
  `∂B_a`, `∂B_c`, `∂B_b`).

In the lemmas, `W`, `Y`, `R` are functions of the configuration, given by these descriptions as
hypotheses `hW`, `hY`, `hR`; the link event is a set `G` with hypothesis `hG`. These sets are
written out because the package may not add definitions; see "Possible definitions" below.

## Statements as proved

**General lemmas** (no percolation):
- `SimpleGraph.Walk.exists_adj_walk_forall_not`: a walk from outside a set `P` into `P` has an
  initial segment avoiding `P` that ends next to a vertex of `P` on the walk.
- `Bond.mem_localConn_inter_of_closed`, `Bond.localConn_iff_of_closed`: if no open pair joins `W`
  to `S \ W`, connections inside `S` from `W` run inside `S ∩ W`. They are therefore determined by
  the pairs meeting `W`.
- `Bond.setOf_exists_mem_localConn_eq_of_agree`: the cluster of a set `T ⊆ A` inside `A` is the
  same for any configuration that agrees on the pairs meeting it. This is the localised form of
  `cluster_eq_finset_determined`.
- Small helpers: `Bond.mem_localConn_of_mem`, `Bond.localConn_mono_of_forall_mem`,
  `Bond.exists_mem_localConn_of_mem`, `Bond.inter_eq_inter_of_inter_eq_of_subset`.
- `Probability.mul_le_inv_sq_mul_of_le_mul`: a rank-one sandwich
  `c f(a) g(b) ≤ M(a, b) ≤ f(a) g(b)` gives the cross-ratio bound `M M' ≤ c⁻² M'' M'''`.
  `Probability.toReal_mul_le_inv_sq_mul_of_le_mul` is the `ℝ≥0∞` version, with a factor `B(b)`
  and the sandwich needed only where `B(b) ≠ 0`.
- `Probability.abs_div_sub_div_le_two_mul`: if `(1 - δ) A ≤ P ≤ A`, `(1 - δ) B ≤ Q ≤ B`,
  `0 ≤ A ≤ B`, `B > 0` and `0 ≤ δ ≤ 1/2`, then `|A/B - P/Q| ≤ 2δ`.

**One cut** (Basu–Sapozhnikov (2.3)):
- Path surgery. `exists_mem_localConn_cut_inner`: a path from `B_{a-1}` to outside `B_c`, up to its
  first visit to `W`, ends at a point of `Y` and avoids `W`. `exists_mem_localConn_cut_outer`: the
  part after its last visit to `W ∪ B_c` starts at a point of `R`. `mem_localConn_of_cut`: on the
  link event, paths into `Y` and out of `R` are glued through `W`.
- Determination. `cut_eq_of_agree` (the cluster and both ports) and `link_iff_of_agree` (the link
  event) are determined by the pairs meeting `W`. `link_iff_of_inter_eq`: the link event is also
  determined by the edges inside the annulus. `measurableSet_setOf_link`.
- `measurableSet_inter_and_law_inter_eq_mul_of_cut` gives independence across a cut. Fix a cut
  value `(W₀, Y₀, R₀)` and take three events:
  1. `E` together with `P ↔ Y₀` inside `(B_c ∩ D) \ W₀`;
  2. the cut event `{W = W₀, Y = Y₀, R = R₀}` with the link event;
  3. `R₀ ↔ ∂B_n` inside `(B_n ∩ D) \ (W₀ ∪ B_c)` together with `H`.

  They are determined by disjoint sets of pairs, so the probability of their intersection is the
  product.
- **`law_inter_eq_sum_of_cut`** (the decomposition, (2.3)). Hypotheses: sources `P ⊆ B_{a-1}`, a
  region `D` containing the annulus, an event `E` of the pairs inside `B_{a-1} ∩ D` and off the
  edges, an event `H` of the edges outside `B_b`, and `n > b`. Then
  `P(E, P ↔ ∂B_n inside B_n ∩ D, linked, H)` is the sum over cut values of the three-factor
  products above. Any finite set of values containing the value of every configuration may be
  summed over.

**The chain** (Basu–Sapozhnikov (2.5), (2.6)):
- Two specialisations of the decomposition. `law_inter_eq_sum_of_cut_of_prev` is the step from one
  cut to the next: the sources are the previous outer port, and the region avoids the previous
  cluster and `B_{c_k}`. `law_inter_armEvent_eq_sum_of_cut` is the start: the source is `z` and the
  connection is `armEvent z n`.
- **`exists_chain_of_cuts`.** There is `κ ≥ 1` with the following property. Take a profile at
  least `1/2`, cuts with `1 ≤ a 0`, `a k < c k < b k` and `4 (b k + 1) + 2 ≤ a (k + 1)`, a number
  `S`, and a measurable `E` of the pairs inside `B_{a 0 - 1}` and off the edges. Then there are:
  - finite sets `T k` of cut values;
  - matrices `M k : T k → T (k+1) → ℝ` with `M x y · M x' y' ≤ κ² M x y' · M x' y`;
  - weights `0 ≤ u' ≤ u''`.

  For every `n > b S` a backward chain `w` (with `w k = M k w (k + 1)` for `k < S` and
  `w S ≥ 0`) gives `⟨u', w 0⟩ = P(E, z ↔ ∂B_n, cuts 0..S linked)` and
  `⟨u'', w 0⟩ = P(z ↔ ∂B_n, cuts 0..S linked)`. The matrices and weights do not depend on `n`.
  Explicitly:
  - `M k x y = P(R_x ↔ Y_y inside (B_{c_{k+1}} \ (W_x ∪ B_{c_k})) \ W_y) · P(cut k+1 has value y, linked)`;
  - `u'(x) = P(E, z ↔ Y_x inside B_{c_0} \ W_x) · P(cut 0 has value x, linked)`;
  - `w k x = P(R_x ↔ ∂B_n inside B_n \ (W_x ∪ B_{c_k}), cuts k+1..S linked)`.

**(2.7).**
- `exists_law_localConn_comparable_of_cut`: there is `c ∈ (0, 1]` such that, for `m ≥ 1`,
  `4m < a ≤ c'`, `U ⊆ B_{m-1}`, `R ⊆ B_m`, `X` outside `B_{a-1}` and `Y` outside `B_{4m}`,
  `c f g ≤ P(R ↔ Y inside (B_{c'} \ U) \ X) ≤ f g`. Here
  `f = P(R ↔ ∂B_{2m} inside B_{2m} \ U)` and `g = P(Y ↔ ∂B_{2m} inside (B_{c'} \ B_{2m-1}) \ X)`.
  So `f` depends only on the inner data `(U, R)` and `g` only on the outer data `(X, Y)`.
- `exists_crossRatio_of_cuts`: the resulting cross-ratio bound for the matrices of two
  consecutive cuts, with `κ = c⁻¹`.

**(2.2), (2.4).**
- `mem_setOf_crossing_clusters_of_mem_armEvent`: on `z ↔ ∂B_n` with `n > b`, an unlinked cut has
  two distinct open crossing clusters in one half of its annulus (in F1's form).
- `exists_law_inter_armEvent_inter_not_link_le`: for every measurable increasing `E` and
  `4^K a ≤ c`, `4^K c ≤ b`, `P(E, z ↔ ∂B_n, cut not linked) ≤ 2 (1 - c₀)^K P(E, z ↔ ∂B_n)`.
- `exists_law_inter_armEvent_le_add_of_cuts`: summed over cuts `0..S`,
  `P(E, z ↔ ∂B_n) ≤ P(E, z ↔ ∂B_n, all linked) + (S + 1) · 2 (1 - c₀)^K · P(E, z ↔ ∂B_n)`.

**The Cauchy property** (Basu–Sapozhnikov (2.1), (2.8)):
- **`exists_abs_toReal_cond_armEvent_sub_le_of_isUpperSet`.** For every `z`, `N` and `ε > 0`
  there is `n₀` such that every profile at least `1/2`, every measurable increasing `E` of the
  edges inside `B_N(z)` and the pairs off the edges, and all `m, n ≥ n₀` satisfy
  `|P(E | z ↔ ∂B_m) - P(E | z ↔ ∂B_n)| ≤ ε`.
- **`exists_abs_toReal_cond_armEvent_sub_le`** (the plan's step 5). For every `z`, every finite set
  `F` of pairs and every `ε > 0` there is `n₀` such that every profile at least `1/2`, every event
  `A` with `∀ ω, ω ∈ A ↔ ω ∩ F ∈ A`, and all `m, n ≥ n₀` satisfy
  `|P(A | z ↔ ∂B_m) - P(A | z ↔ ∂B_n)| ≤ ε`.
- Helpers: `law_armEvent_pos` (`z ↔ ∂B_n` has positive probability for a profile at least `1/2`),
  `toReal_cond_armEvent` (conditional probability as a ratio of reals),
  `exists_forall_mem_Icc_of_finset` (a finite set of pairs lies in a box).

## Proof the Lean follows

1. *Cuts as random sets.* `W` is closed under open pairs inside the annulus. Consider an open path
   from `z` (or from a previous outer port) to `∂B_n`.
   - At its first visit to `W` it arrives from a point of `B_{a-1}`, a point of `Y`. Before that
     point it has not reached `∂B_c ⊆ W`.
   - After its last visit to `W ∪ B_c` it leaves to a point outside `B_b`, a point of `R`.

   Conversely, on the link event every point of `W` next to `Y` lies on a crossing of the inner
   half, and every point next to `R` on a crossing of the outer half. The two crossings are
   joined. This is Basu–Sapozhnikov's uniqueness of the crossing cluster in a form with no
   planar topology.
2. *Independence.* Three sets of pairs carry the three factors:
   - all non-edges, and the edges inside `(B_c ∩ D) \ W₀`;
   - the edges meeting `W₀`;
   - the edges with no endpoint in `W₀ ∪ B_c`.

   They are disjoint, and `prodBernoulli_inter_of_determined` applies twice. The cut event is
   measurable because it is determined by the finitely many pairs inside `B_{b+1}`
   (`measurableSet_of_determined_finset`, F2).
3. *The chain.* The decomposition at cut `k + 1`, with the previous cut's cluster and `B_{c_k}`
   removed from the region, is exactly `w k = M k w (k + 1)`. The later link events are determined
   by edges outside `B_{b_{k+1}}`. Summing over `T k` (all triples of subsets of the relevant
   boxes) is allowed because unrealised values contribute `0`.
4. *Cross ratio.* With `m = b_k + 1`, the middle factor `M` is F1's (A2) quantity for
   `X = R_x ⊆ B_m`, `Y = Y_y` (outside `B_{4m}` because `4(b_k + 1) + 2 ≤ a_{k+1}`), and
   `Z = (B_{c_{k+1}} \ (W_x ∪ B_{c_k})) \ W_y`. Stopping at the first visit to `∂B_{2m}` shows that
   F1's two factors depend only on `x` and only on `y`. The second factor of `M` only multiplies
   the outer function, so the rank-one sandwich gives `κ = c⁻¹`. When the cut value `y` has
   probability `0` both sides vanish.
5. *Errors.* An unlinked cut on the arm event has two crossing clusters in one half. Indeed, the
   arm gives a crossing of the whole annulus, which splits at `∂B_c`, and uniqueness in both halves
   would link everything. F1's (A1) with the increasing event `E ∩ {z ↔ ∂B_n}` bounds this by
   `(1 - c₀)^K` times `P(E, z ↔ ∂B_n)`. No division by `P(E)` is needed, unlike
   Basu–Sapozhnikov's (2.4).
6. *Cauchy.* Choose `S` with `θ^S ≤ ε/2`, where `θ = (κ² - 1)/(κ² + 1)`. Choose `K` with
   `δ = 2(S + 1)(1 - c₀)^K ≤ min(1/2, ε/8)`. The radii are `a 0 = N + 2`, `c k = 4^K a k + 1`,
   `b k = 4^K c k + 1` and `a (k + 1) = 4 (b k + 1) + 2`, with `n₀ = b S + 1`; none of them depends
   on the profile. F2's backward ratio contraction gives
   `|⟨u', w_m⟩/⟨u'', w_m⟩ - ⟨u', w_n⟩/⟨u'', w_n⟩| ≤ θ^S`. Each ratio is within `2δ` of
   `P(E | z ↔ ∂B_·)`, so the distance is at most `4δ + θ^S ≤ ε`. For a general cylinder event, F2's
   inclusion–exclusion (`measureReal_eq_sum_subset_of_determined`, applied to the conditional
   measure) writes `P(A | ·)` as `Σ_{S ⊆ F} c_S P(S ⊆ ω | ·)` with `|c_S| ≤ 2^{|F|}`. The
   all-open events are increasing, so `ε / 4^{|F|}` for them gives `ε` for `A`.

## Statement choices compared with the plan

The plan states F3 in prose (§4.2 steps 3–5). Each choice below is at least as strong as the plan
and the source.
- **Uniformity.** Every profile at least `1/2` on the edges, not `p ∈ [p_c, p_c + δ]` or
  `β ≥ log 2`. The `β` form is an instance (`p = 1 - e^{-β} ≥ 1/2`). Every centre `z`; FM8D needs
  `z = 0`.
- **The cut.** Basu–Sapozhnikov use `C_i` (the cluster of `B(N_i)` in `B(N_{i+1})`) and, inside
  (2.7), an inward cluster `X_j`. As written, their matrix `M` is a sum over `X_j` of products whose
  factors are not independent: the event `{C_j = U'}` with `C_j ⊇ B(N_j)` reads the pairs of the
  middle region.
  Here one cut carries both ports at once (the cluster of the middle sphere), so every factor is
  determined by disjoint pairs and (2.7) needs no inner sum.
- **The good event.** The link event (any inner crossing joined to any outer crossing) replaces
  "unique crossing cluster" `F_i`. It is what the gluing needs, it is determined by the pairs
  meeting `W`, and on the arm event its failure implies two crossing clusters in a half annulus,
  so F1's (A1) applies.
- **Errors.** They are bounded relative to `P(E, z ↔ ∂B_n)` directly (F1's (A1) holds jointly with
  any increasing event). There is no `C* = (c*² P_{p_c}(E))⁻¹`, and the error is summed over the
  cuts instead of being multiplied as `e^{±ε}`.
- **The contraction exponent** is `S` for `S` matrices (F2), with factor `(κ² - 1)/(κ² + 1)`; the
  source has `((κ - 1)/(κ + 1))^{s-1}` with `κ_BS = c⁻¹`.
- **Cylinder events** are handled for every event determined by a finite set of pairs, including
  pairs that are not edges.

## Where F4 picks up

F4 continues `Arms/IncipientCluster.lean` (plan §4.2 step 6 and the uniqueness paragraph):
1. *First limit.* For each `β ≥ log 2` (or each profile at least `1/2`), the real sequence
   `r ↦ P(A | armEvent 0 (r + 1))` is Cauchy by `exists_abs_toReal_cond_armEvent_sub_le` with
   `z = 0`, hence convergent. The convergence is uniform in `β`, because `n₀` depends only on
   `F` and `ε`.
2. *Continuity in β.* `β ↦ P_β(A | armEvent 0 n)` is continuous: the cylinder probabilities are
   polynomials in `p`, and the arm event is a cylinder event. A uniform limit of continuous
   functions is continuous.
3. *Second limit.* For `β > log 2`, `P_β(|K_0| = ∞) > 0` and `{|K_0| = ∞} = ⋂_r armEvent 0 r`.
   Continuity from above gives `P_β(A | |K_0| = ∞) = lim_r P_β(A | armEvent 0 r)`. Continuity at
   `log 2` then gives the `𝓝[>] log 2` limit.
4. *The law `ν`.* F2's `exists_measure_of_tendsto_cylinder` (or `exists_measure_of_tendsto_subset`)
   on `ι = Sym2 (LatticeSite 2)` with `μ r = cond (law q) (armEvent 0 (r + 1))`. These are
   probability measures by `ProbabilityTheory.cond_isProbabilityMeasure` and `law_armEvent_pos`.
5. *Uniqueness under `ν`.* Use F1's `exists_law_inter_biInter_compl_fourStrip_le` with
   `E = armEvent 0 (r + 1)` and `inter_edgeSet_mem_localConn_union_of_mem_fourStrip`, as in the
   plan.

## Possible definitions (interface, for later)

The cut sets, the link event and the set-to-set connection `{ω | ∃ x ∈ X, ∃ y ∈ Y, ω ∩ L ∈
localConn Z x y}` are each written out many times. A small interface package could define them:
a set-to-set `localConn`, an annulus `B_b \ B_{a-1}`, and the cluster of a set inside a region.
The statements here would then shorten considerably. Not done (proof-only package).

## Search

- **PercLib.** `cluster_eq_finset_determined` and `law_cluster_eq_inter` (`Bond/ClusterLaw.lean`)
  cover the cluster of a vertex in the whole graph. `localConn_iff_of_agree`
  (`Bond/LocalConnectivity.lean`) needs agreement on all internal pairs. There was nothing for
  connections from a set closed under open pairs, or for the cluster of a set inside a region,
  hence the two `Bond` lemmas above. `exists_walk_first_mem` (`RSWKeyStep.lean`) gives a first
  visit but not the step before it, hence `exists_adj_walk_forall_not`.
- **Reused, F1:** `exists_mem_boxBoundary_mem_localConn_inter`, `_diff`,
  `exists_law_setOf_localConn_comparable`, `exists_law_inter_setOf_crossing_clusters_le`,
  `exists_law_le_of_half_le`, `measurableSet_setOf_exists_inter_mem_localConn`.
- **Reused, F2:** `abs_ratio_sub_ratio_le_of_crossRatio_of_backward`,
  `measureReal_eq_sum_subset_of_determined`, `measurableSet_of_determined_finset`.
- **Reused, P7/P8:** `inv_two_pow_le_law_armEvent`, `law_armEvent_eq_law_armEvent_zero`.
- **Reused, other:** `prodBernoulli_inter_of_determined`, `inter_mem_localConn_iff_of_inter_eq`,
  `mem_localConn_iff_exists_walk`.
- **Mathlib.** No rank-one-sandwich-to-cross-ratio lemma (F2 takes the cross ratio as a
  hypothesis). Used: `measure_le_inter_add_sdiff`, `measure_biUnion_finset(_le)`,
  `ProbabilityTheory.cond_apply`, `cond_isProbabilityMeasure`, `exists_pow_lt_of_lt_one`,
  `Finset.abs_sum_le_sum_abs`, `Finset.mem_sym2_iff`, `Sym2.mem_iff_exists`.

## Sources

D. Basu and A. Sapozhnikov, *Kesten's incipient infinite cluster and quasi-multiplicativity of
crossing probabilities*, Electron. Commun. Probab. 22 (2017), arXiv:1603.06884v2, read in the
arXiv HTML rendering. The parts used are Section 1, Theorem 1.1, and Section 2: the scales, the
events `F_i`, `ε_i`, the estimates (2.2)–(2.8), the sets `C_i`, `D_i`, `X_j`, `Y_j`, and
Remark 2.1. Equation numbers are the arXiv ones, and journal page numbers were not checked. The
paper's (2.2) and (2.7) assert product bounds without derivation; the Lean proves its own forms,
described above. The wiki attributes FM8D to Kesten (1986, Theorem 3) and Basu–Sapozhnikov (2017).
