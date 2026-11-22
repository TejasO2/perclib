# Open circuits in annuli of ℤ²: advice for the wiki

Advice for the wiki agent on package P6 of the RSW plan
(`PercLib/Models/Planar/Arms/Separator.lean`). This is the first paragraph of the proof of XB1U
(`critical-exponents`, §"Extending an arm and blocking it"): the circuit `C_n` built from four
strip crossings, the fact that arms crossing the annulus meet it, and its probability bound
`c₀`. The same circuit is used in the lower bound of Y8K3 and in K8A1. Everything is proved
with only `propext`, `Classical.choice` and `Quot.sound`; no tags and no definitions were added.

## Conventions

As in `arm-events.md`: boxes are `Set.Icc lo hi` on `Fin 2 → ℤ`, `(r : LatticeSite 2)` is the
constant vector `r`, so `Icc (z - r) (z + r)` is `B_r(z) = z + [-r, r]²`, and only the open
nearest-neighbour edges `ω ∩ (zdGraph 2).edgeSet` are read. "Joined inside `S`" is
`ω ∩ (zdGraph 2).edgeSet ∈ localConn S a b` (an open path all of whose vertices lie in `S`);
"joined" with no set is `conn a b` (confined to no box). "At `1/2`" is the hypothesis
`∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2`. Probabilities are in `ℝ≥0∞`. `fourStrip z n` is
the event of `arm-events.md`: left-right crossings of the top and bottom strips
`z + [-4n, 4n] × [2n, 4n]` and `z + [-4n, 4n] × [-4n, -2n]`, bottom-top crossings of the right
and left strips `z + [2n, 4n] × [-4n, 4n]` and `z + [-4n, -2n] × [-4n, 4n]`, exactly the four
crossings the wiki requires.

## Statements as proved

- **Circuit gluing** (`inter_edgeSet_mem_localConn_of_mem_fourStrip`): for every configuration
  `ω ∈ fourStrip z n`, every `n ∈ ℕ`, every `a, a'` in the inner box `B_{2n}(z)` and every
  `b, b'` on the boundary of `B_{4n}(z)` (some coordinate `b i = z i ± 4n`), if `a` is joined to
  `b` and `a'` to `b'` inside `B_{4n}(z)`, then `a` is joined to `a'` inside `B_{4n}(z)`. This
  is the wiki's "the original arm exits `B_{4n}` and hence meets the circuit", for two arms at
  once: both meet `C_n`, so they are connected.
- **Circuit gluing, escape form** (`inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_conn`):
  the same conclusion when `a` is joined (in no box) to some `y` outside `B_{4n - 1}(z)` and `a'`
  to some `y'` outside `B_{4n - 1}(z)`. This is the form the three proofs use: in XB1U the arm
  `0 ↔ ∂B_r` with `r ≥ 8n` and the horizontal crossing of `[0, 30n] × [-n, n]` (it starts at
  `x = 0`, `|y| ≤ n`, inside `B_{2n}`, and reaches `x = 30n ≥ 4n`); in Y8K3 the arms of length
  `8r` from `0` and from `x` (`‖x‖∞ = r ≤ 2r`, and the second arm reaches distance `≥ 7r ≥ 4r`);
  in K8A1 the arms from `a`, `b` and `a`, `c` at the two scales.
- **T4, circuits with probability bounded below** (`exists_pos_le_law_fourStrip`): there is
  `c₀ > 0` such that for every `q` at `1/2`, every centre `z` and every integer `n ≥ 1`,
  `c₀ ≤ P(fourStrip z n)`. This is the wiki's "a constant `c₀ ∈ (0, 1)`, independent of `n`, for
  the event `C_n`", with `C_n` replaced by the four-strip event (see item 1 below). `c₀ < 1` is
  not stated; any smaller positive constant also works, so it costs nothing downstream.
- **Stopping at the boundary of a box centred anywhere**
  (`exists_boundary_mem_localConn_of_mem_conn`, on `ℤ^d`): if `x` lies in
  `c + [-(r - 1), r - 1]^d` and is joined to a point outside it, then `x` is joined inside
  `c + [-r, r]^d` to a point on the boundary of that box. It is `mem_armEvent_of_mem_conn`
  (`arm-events.md`) for a box whose centre `c` need not be the start of the path; it turns the
  escape form into the first form.

## Proof the Lean follows

The wiki's construction, with the circuit never extracted (the plan's choice, §2.6 and §3.4).

1. *Adjacent crossings meet.* The wiki: their portions in the common corner square cross it in
   perpendicular directions. The Lean uses a simpler observation: a left-right crossing of the
   top (or bottom) strip is also a left-right crossing of the whole box `B_{4n}(z)`, and a
   bottom-top crossing of the right (or left) strip a bottom-top crossing of `B_{4n}(z)`. The
   gluing lemma of `gluing.md` (`inter_edgeSet_mem_localConn_of_crossings`) in `B_{4n}(z)` then
   joins top to right, top to left and bottom to right inside `B_{4n}(z)`. No corner square and
   no sub-crossing is needed.
2. *No simple circuit.* The wiki follows the four crossings around the square, then deletes
   loops to get a simple circuit in `B_{4n} \ B_{2n-1}`. The Lean uses only what the later
   proofs need from the circuit: every arm crossing the annulus meets it. Item 3 proves that
   directly from the four crossings.
3. *An arm meets the crossings.* Let an open path inside `B_{4n}(z)` run from `a ∈ B_{2n}(z)` to
   a point `b` of, say, the top side (`b₁ = z₁ + 4n`). Along it, the second coordinate goes from
   at most `z₁ + 2n` to `z₁ + 4n`, so a segment of the path runs from height `z₁ + 2n` to height
   `z₁ + 4n` and stays between them (`SimpleGraph.Walk.exists_walk_mem_Icc`, `crossing-symmetry.md`).
   That segment is a bottom-top crossing of the top strip; the gluing lemma in the top strip
   joins it to the strip's left-right crossing. The other three sides are the same with the
   coordinate or its sign changed (four cases, no rotation of the configuration), and item 1
   joins every crossing to the left-right crossing of the top strip. So both arms are joined to
   that crossing, hence to each other, inside `B_{4n}(z)`.
4. *Inner radius.* Because the strips contain their inner sides (`|·| = 2n`), item 3 works for
   arms starting anywhere in `B_{2n}(z)`, one more than the wiki's `B_{2n-1}`. For `n = 0` both
   points are the centre and the statement is trivial, so circuit gluing has no hypothesis
   `n ≥ 1`. The wiki's uses (`B_n`, `x` with `‖x‖∞ = r` inside the circuit of scale `r`, the
   marks inside `B_{2s-1}(a)`) are all covered.
5. *Probability.* Each strip is an `8n × 2n` box crossed in its long direction. RSW in any
   position (`exists_pos_le_law_crossing 4` at height `2n`, `rsw.md`) bounds each by the same
   `c`; Harris's inequality (X5SS, `prodBernoulli_harris`) for the four increasing crossings,
   applied three times, gives `c₀ = c⁴`. In the wiki's notation `c₀ = c₄⁴`.

## Statement choices compared with the plan

The plan's draft (§2.6) had `1 ≤ n`, an inner box of radius `2n - 1`, and `b ∈ boxSphere z (4n)`.
The proved statement drops `1 ≤ n`, uses radius `2n`, and asks of `b` only the boundary
condition `∃ i, b i = z i - 4n ∨ b i = z i + 4n` (membership in the box follows from the path).
Each change makes the theorem stronger. The boundary condition is written exactly as in
`armEvent`, so an arm `ω ∈ armEvent z (4n)` supplies `b` and its path directly. T4 is the plan's
statement.

## Search

PercLib: no circuit or separator lemma besides the blocking lemma of `critical-probability.md`
(the dual counterpart, used for the upper bound of XB1U); `mem_armEvent_of_mem_conn` is the
stopping lemma for boxes centred at the start of the path only, so the general-centre version
was added. Mathlib has no percolation notions; the walk tools are those of
`crossing-symmetry.md` (`exists_walk_mem_Icc`) and mathlib's `SimpleGraph.Walk.takeUntil`.
Library lemmas reused: `inter_edgeSet_mem_localConn_of_crossings` (`Gluing.lean`),
`exists_pos_le_law_crossing` (`RSW.lean`), `prodBernoulli_harris` (`Probability/Harris.lean`),
`exists_first_exit` (`Bond/FirstExit.lean`), `mem_fourStrip_iff`, `apply_le_apply_add_one_of_adj`
(`Arms/Defs.lean`), `coord_le_add_one_of_adj`, `mem_localConn_iff_exists_walk`
(`CrossingSymmetry.lean`).

## Sources

The construction is the one of the wiki's XB1U proof (four strips, Harris). The plan locates
the one-arm bounds in H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes,
7 October 2018, Corollary 4.7, pp. 23–24; that text was not re-read for this package. B. Bollobás
and O. Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math. Soc. 38 (2006),
470–484, arXiv math/0410359v3, Theorem 8, p. 9, form circuits from four rectangle crossings in
annuli (as recorded in `critical-probability.md`).
