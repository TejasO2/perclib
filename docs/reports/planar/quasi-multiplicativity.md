# Separation of arms and quasi-multiplicativity: package A3, first part (A3a)

Advice note for package A3 of the arms plan (`docs/reports/planar/arms-plan.md` on branch
`claude/planar-arms-plan-0a97fc`, §2.4, §1.4 and §9 row A3). Source: P. Nolin, *Near-critical
percolation in two dimensions*, EJP 13 (2008), §§4.4–4.6, read through arXiv:0711.4948v1, where the
numbering is one lower in places (journal Theorem 11 = arXiv Theorem 10, journal Lemma 13 = arXiv
Lemma 12, journal Lemma 15 = arXiv Lemma 14, journal Propositions 16, 17 = arXiv Propositions 15,
16; the gluing of the plan's "Proposition 12" is arXiv Proposition 11, items 1–3).

**Status: A3 is not finished.** This session proved the foundations listed below (A3a), checked
every plan statement at small scales, and found two problems in the route that need decisions
before the main theorems can be proved. Nothing in `Arms/Defs.lean` or `Planar/Defs.lean` was
changed. Local commits only, nothing pushed.

## 1. What is proved (A3a)

New file `PercLib/Models/Planar/Arms/QuasiMultiplicativity.lean`, proof-only (no definition, no
tag, no `…Input`), imported from `PercLib.lean`.

**Symmetries of crossing bounds** (the helper the task asked for):

```lean
theorem law_comp_sym2Map_apply {V : Type*} (q : Sym2 V → unitInterval) (g : V ≃ V)
    (A : Set (Config V)) :
    law (fun e => q (Sym2.map g e)) A = law q ((fun ω => Sym2.map g.symm '' ω) ⁻¹' A)

theorem dualConfig_image_reflect (b : ℤ) (ω : Config (LatticeSite 2)) :
    dualConfig (Sym2.map (fun v : LatticeSite 2 => ![v 0, b - v 1]) '' ω) =
      Sym2.map (fun v : LatticeSite 2 => ![v 0, b - 1 - v 1]) '' dualConfig ω

theorem CrossingBounds.swap (h : CrossingBounds q L c) :
    CrossingBounds (fun e => q (Sym2.map (fun v : LatticeSite 2 => ![v 1, v 0]) e)) L c

theorem CrossingBounds.reflect (h : CrossingBounds q L c) :
    CrossingBounds (fun e => q (Sym2.map (fun v : LatticeSite 2 => ![v 0, 0 - v 1]) e)) L c
```

The swap maps a box crossed in direction `0` onto a box of the same size crossed in direction `1`
and commutes with duality (`dualConfig_image_swap`, `CrossingSymmetry.lean`); the reflection keeps
the direction, exchanges the two faces of a vertical crossing, and moves faces by one
(`dualConfig_image_reflect`). With `CrossingBounds.translate` these generate all symmetries of
`ℤ²`. Use: to apply Lemma 15 (`exists_law_separable_ge`, stated for `[0, 4N] × [0, N]` crossed
bottom to top) on another side of an annulus, apply it to the law `q ∘ Sym2.map g` (crossing
bounds by `swap`/`reflect`/`translate`) and rewrite with `law_comp_sym2Map_apply`: the good event
is then the set of `ω` whose image `Sym2.map g.symm '' ω` is in Lemma 15's event. The predicate has
to be read back in the original coordinates at the point of use (walks mapped by the graph
isomorphism, `dualConfig` by the three equivariance lemmas, positions by `perimeterPos_add`,
`perimeterPos_rotate`).

**Arms in corridors and the a priori lower bound at one scale:**

```lean
theorem exists_isCrossing_of_mem_crossing_one {ζ : Config (LatticeSite 2)}
    {lo hi : LatticeSite 2} {S T : Set (LatticeSite 2)} (h : ζ ∈ crossing 1 lo hi)
    (hS : ∀ v ∈ Icc lo hi, v 1 = lo 1 → v ∈ S) (hT : ∀ v ∈ Icc lo hi, v 1 = hi 1 → v ∉ T) :
    ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), γ.IsCrossing S T ∧
      (∀ e ∈ γ.edges, e ∈ ζ) ∧ ∀ v ∈ γ.support, v ∈ Icc lo hi

theorem exists_isArm_of_mem_corridor {ω : Config (LatticeSite 2)} {z : LatticeSite 2} {r R : ℕ}
    {x w : ℤ} (col : Bool) (hx : z 0 - r ≤ x) (hxw : x + w ≤ z 0 + r) (hrR : r < R)
    (h : ω ∈ cond col (crossing 1 ![x, z 1 + r] ![x + w, z 1 + R])
      (dualConfig ⁻¹' crossing 1 ![x, z 1 + r] ![x + w, z 1 + R])) :
    ∃ (a b : LatticeSite 2) (γ : (zdGraph 2).Walk a b), IsArm ω col z r (z - R) (z + R) γ ∧
      (∀ v ∈ γ.support, x ≤ v 0 ∧ v 0 ≤ x + w ∧ z 1 + r ≤ v 1) ∧
      8 * (R : ℤ) + 2 * (z 0 + R - x - w) - 1 ≤ landingPos (z - R) (z + R) col γ ∧
      landingPos (z - R) (z + R) col γ ≤ 8 * (R : ℤ) + 2 * (z 0 + R - x)

theorem dualConfig_inter_eq_of_inter_eq {lo hi : LatticeSite 2} {ω ω' : Config (LatticeSite 2)}
    (h : ω ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)} = ω' ∩ {e | ∀ v ∈ e, v ∈ Icc lo (hi + 1)}) :
    dualConfig ω ∩ {f | ∀ g ∈ f, g ∈ Icc lo hi} = dualConfig ω' ∩ {f | ∀ g ∈ f, g ∈ Icc lo hi}

theorem exists_pos_le_law_multiArmEvent_inter_halfArmEvent {j : ℕ} (σ : Fin j → Bool)
    (c : ℕ → ℝ≥0∞) (K : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), 4 * j ≤ r → r < R → R ≤ K * r →
        (R : ℕ∞) ≤ L → c₀ ≤ law q (multiArmEvent σ z r R ∩ halfArmEvent σ z r R)
```

with corollaries `exists_pos_le_law_multiArmEvent` and `exists_pos_le_law_halfArmEvent` (the same
statement for each event alone). Construction: `j` vertical corridors of width `w = ⌊r / 2j⌋` on the
top side of `B_r(z)`, gaps of width `w`, arm `i` in the corridor at columns
`[z₀ + r - (2i + 2)w, z₀ + r - (2i + 1)w]` (right to left, so landing positions increase with `i`);
`c₀ = c (4jK) ^ j`; independence by `prodBernoulli_iInter_fin_of_determined` with the edge sets of
the corridors enlarged by one (a dual crossing of a box of faces reads the edges of the box enlarged
by one). This is Nolin's a priori lower bound (arXiv Prop. 13) for one annulus of bounded aspect
ratio, and the case `n₂ ≤ 8 n₁` of quasi-multiplicativity will use it.

## 2. The plan statements at small scales

Every plan statement of §2.4 was checked for small scales. Four of them fail there. The fixes below
only exclude small or degenerate scales, the same kind as the approved `N₀` of Lemma 15. **None of
the corrected forms is proved yet; all are pending the user's approval.**

### 2.1 Theorem 11 (separation, landing form): false for small `r`

Plan (with the real `window`; perimeter `16 r + 8` inside, `16 R` outside, as the docstring of
`window` says):

```lean
∃ C, C ≠ ⊤ ∧ ∀ q L, CrossingBounds q L c → ∀ z (r R : ℕ), 2 * r ≤ R → (R : ℕ∞) ≤ L →
  law q (multiArmEvent σ z r R) ≤
    C * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ' η) (window (16 * R) θ η))
```

**Counterexample.** `j = 1`, `σ = ![true]`, `η = 1/100`, `θ = θ' = ![3/10]` (landing data:
`3/10 + 1/100 ≤ 1`, `2η ≤ 1`). At `r = 0` the inner window is
`{p ∈ ℤ | 8 · 3/10 ≤ p ≤ 8 · 31/100} = {p | 2.4 ≤ p ≤ 2.48} = ∅`, so the right side is `0`. At
`q ≡ 1/2` with `c` from `exists_crossingBounds_half` and `L = ⊤`, the left side is the probability of
an open arm from `z` to distance `R`, positive. So no `C` works, for every `R`. The same happens for
every `r` with `(16 r + 8) η < 1`, and windows shorter than `2` may contain only positions of the
wrong parity (open arms have odd inner positions and even landing positions, dual arms the
opposite). Even with nonempty windows, a law with crossing bounds may forbid single edges (see
2.2), so small windows can be emptied by the law.

**Fix (pending approval):** `∃ C, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ q L, … → ∀ z r R, r₀ ≤ r → 2 * r ≤ R → …`,
with `r₀` chosen after `σ, η, θ, θ', c`, before `q, L, z, r, R`.

### 2.2 Quasi-multiplicativity, lower half: false for small `r₁`

Plan: `∀ z r₁ r₂ r₃, r₁ ≤ r₂ → r₂ ≤ r₃ → (r₃ : ℕ∞) ≤ L → upper ∧ lower`, lower =
`law (A r₁ r₂) * law (A r₂ r₃) ≤ C * law (A r₁ r₃)`.

**Counterexample.** Crossing bounds do not bound single edges away from `0`: the profile `q`
equal to `1/2` except on the three edges of `v = z + (1, 0)` other than `{z, v}`, where it is `0`,
has crossing bounds at every scale with some `c > 0`. (Open left-right crossings of a `kn × n`
box: for `n ≥ 9` the bottom or the top sub-box of the full width and height `⌊n/4⌋` avoids the three
rows around `v`, and its crossing, which reads no closed edge, has probability at least the RSW
bound at `1/2` for aspect ratio `6k`; for `n < 9` a straight path along a row other than `v`'s uses
none of the three edges and is open with probability at least `2^{-8k}`. Bottom-top crossings the
same with columns. Dual crossings: `q ≤ 1/2` everywhere and dual crossings are decreasing.) Take `σ` = four open arms. Then `A(z, 0, R) = ∅` almost surely for
`R ≥ 2` (the arm through `v` cannot continue), `law (A z 0 1) = 1/16` (the four edges at `z`), and
`law (A z 1 R) > 0` (straight arms from `z - (1,0)`, `z ± (0,1)` and `z + (1,1)` avoid `v`). So
`law (A 0 1) * law (A 1 R) > 0 = C * law (A 0 R)` for `r₁ = 0, r₂ = 1, r₃ = R ≥ 2`.

**Upper half at equal radii** (already in `MultiArmBasics.lean`'s implementation notes): with twelve
open arms, `A(1, 1) = ∅` and `A(1, 3) ∋ univ`, so the upper half fails at `r₁ = r₂ = 1`.

**Fix (pending approval):** `∃ C, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ q L, … → ∀ z r₁ r₂ r₃, r₀ ≤ r₁ → r₁ ≤ r₂ →
r₂ ≤ r₃ → (r₃ : ℕ∞) ≤ L → upper ∧ lower`. With `r₀ ≥ j` both halves survive equal radii: for
`r ≥ j`, `A(r, r) = univ` (arms of length zero at consecutive positions down the left side of
`B_r(z)`: open arms at its vertices, positions `12r + 2(z₁ + r - y)`; dual arms at the faces just
left of it, positions `12r + 2(z₁ + r - y) - 1`, read through the last case of `perimeterPos`). The
upper half for `r₁ < r₂ < r₃` is A1's `law_multiArmEvent_le_mul` (with `C = 1`, every law).

### 2.3 Extendability: false for small `R`; second conjunct in the trivial direction

Plan: `law (A r R) ≤ C * law (A r (2R)) ∧ law (A r R) ≤ C * law (A (2r) R)`.

* **First conjunct, counterexample:** the profile of 2.2 with four open arms gives
  `law (A z 0 1) = 1/16 > 0 = law (A z 0 2)`. **Fix (pending approval):** `∃ r₀`, `r₀ ≤ r` (or
  `r₀ ≤ R`).
* **Second conjunct:** `A(r, R) ⊆ A(2r, R)` for `2r < R` (`multiArmEvent_subset_of_le`), so it holds
  with `C = 1`; it is the trivial direction. Nolin's Prop. 16 (arXiv Prop. 15) has
  `P(A(n/2, N)) ≍ P(A(n, N))`, whose content is `law (A (2r) R) ≤ C * law (A r R)`. **Proposed:**
  state this direction (with `r₀ ≤ r`), keep the plan's as a remark. Pending approval.

### 2.4 The other statements

* **A priori lower bound** (Nolin arXiv Prop. 13): needs `r₀ ≤ r` for the same reason as 2.2 (and
  for `j ≥ 7` arms from a point Nolin's own statement is false: `A(0, N) = ∅`). The one-scale form
  proved here has `4j ≤ r`.
* **Half-plane and non-centred versions** inherit the same `r₀`.

## 3. Two problems in the route (decisions needed)

### 3.1 Other arms in the separation strip: fine for colour sequences without packs

Lemma 15 reroutes every family of disjoint crossings of a strip. Applied near the top side of
`B_R(z)` to the final crossings of the arms landing there, it ignores the rest of the arms: the
arms landing on other sides, and the excursions (arches over the bottom row of the strip) of the
initial parts of all arms. A rerouted crossing can meet those. Nolin's U-shaped domains do not
remove this either.

For a colour sequence **without packs** (no two cyclically consecutive arms of the same colour), this
is harmless. An open rerouted crossing of arm `i` cannot meet another open arm `k`: in the cyclic
order there is a dual arm between `i` and `k` on each side, and an open walk joining arm `i` to arm
`k` inside the annulus would give an open arm whose order against those two dual arms contradicts
order invariance (`sbtw_innerPos_iff_sbtw_landingPos`, A1). It may meet the initial part of arm `i`
itself; then shortcut. The same argument confines the fence connection (Nolin (4.5), inside the
ball of radius `√η N` around the tip, which reaches no other tip). So for pack-free sequences the
four sides can be separated one after the other with Lemma 15 transported by `CrossingBounds.swap`,
`.reflect`, `.translate` (each side's good event is for the original configuration; separation
between tips of adjacent sides follows from the corner clause).

### 3.2 Packs: a gap in the gluing and in the separation step

For a **pack** (consecutive arms of one colour, e.g. `OO` in `OCOOC`, or any monochromatic `σ` with
`j ≥ 2`) nothing stops a rerouted crossing, or a fence connection, from meeting an arch of a
pack-mate. Then the obvious surgeries fail. Example: open pack arms `c₁` (left) and `c₂` (right) with
tips `b'₁`, `b'₂`; `c₂` enters the ball around `b'₁` below the top row; the fence connection of
`c₁` leaves `c₁`, meets `c₂` at `y`, then reaches the fence of `b'₁` without meeting any arm. Then `y`
is a cut vertex of the union of `c₁, c₂`, both connections and both fences between the two
starts and the two fences, and no two disjoint glued arms exist in that union. Nolin's gluing
("straightforward", arXiv Prop. 11 items 1–2) and his separation step do not address this. The
literature treats monochromatic arm events separately (Beffara–Nolin, Ann. Probab. 2011); I have not
checked how they handle this point.

**Options (the user's call; they change what A3 can state):**

* **(A) Restrict A3 to pack-free `σ` and `j = 1`.** Covers `O`, `OC`, `OCOC` (Stage 3 uses `j ∈ {1, 4}`)
  and the half-plane sequences `OC`, `OCO` (linear order: pack-free). It does **not** cover `OCOOC`,
  which U2 needs for the five-arm upper bound. Statement change (restriction of `σ`); plan risk 3
  anticipated it.
* **(B) Planar Menger for packs.** `m` disjoint same-colour arms in a sector between two arms of
  the other colour exist iff no dual cross-cut of the sector meets fewer than `m` arms' worth of
  edges; with it, any union of the rerouted pieces that is not cut by fewer than `m` vertices
  contains `m` disjoint arms. A2's greedy exploration already gives Menger for boxes (rerouting to
  greedy tips, `exists_reroute_of_exploration`, shows the greedy family is maximum); a sector is not
  a box. New planar package, size unknown (probably like PT2).
* **(C) A separation lemma with obstacles.** Re-prove Lemma 15's deterministic part so that the
  reroute avoids given walks of the same colour touching only the bottom row (arches). The
  probability side is unchanged; the surgery (`separable_of_forall`) needs a new invariant. Also new
  work in A2's files.

(A) first, then (B) or (C) for `OCOOC`, is the cheapest path to Stage 3; U2 needs (B) or (C).

### 3.3 Smaller design points

* **The separated event in statements.** Theorem 11's iteration needs "arms to `∂B_R` with tips
  separated at scale `η` and fences" in several intermediate statements. Rule 4 forbids a `def` in
  a proof file, so it must be written inline each time (about fifteen lines), or added to
  `Arms/Defs.lean` in a small interface package once PR #12 is settled (plan §8.4 allows it).
  The user's call.
* **Conditioning on the separated event.** The gluing conditions on a non-monotone event. A1b's
  Nolin Lemma 13 (`prodBernoulli_mul_mul_le_inter_of_determined`) needs `Ainc` increasing and `Adec`
  decreasing globally. What the gluing has is an event whose sections, at fixed edges inside the
  box, are increasing in the open-corridor edges and decreasing in the dual-corridor edges: a
  union of such products is an upper set for the order that reverses the dual-corridor
  coordinates, so Harris applies after complementing those coordinates. A general lemma "Harris
  for a mixed order" (`Probability/`, not planar) does this; I found none in PercLib.
* **Corridors from separated tips to landing windows.** The tips are anywhere on `∂B_R` (in
  `O(1/η)` bins); the windows are fixed. Routing `j` disjoint corridors from bins to windows with the
  cyclic order kept needs turning corridors (radial, then along nested rings, then radial). Plan
  this geometry before coding; the straight corridors of A3a are the base case.

## 4. Errata in the source (Nolin, arXiv v1 §4)

Found while reading §4 for this package (arXiv numbering):

* **No minimal radius in Theorem 10 and Proposition 13**: both need `n ≥ n₀(j)` (for `j ≥ 7` arms
  from a point the event is empty, so Prop. 13's lower bound fails); our 2.1, 2.2.
* **Proposition 11, item 3** (choosing landing sequences by covering): the constant should be
  raised to the power `j`, one factor per arm and per boundary.
* **Proposition 11, item 2 vs Proposition 16**: the statement asks `n₂ ≥ 4 n₁`, the proof of
  Prop. 16 "may assume `n₂ ≥ 8 n₁`"; the remaining range follows from the one-scale lower bound
  (proved here in the form `4j ≤ r < R ≤ K r`).
* **Proposition 16, upper bound**: the annuli `S_{n₁,n₂}` and `S_{n₂,n₃}` share `∂S_{n₂}`; A1 handled
  it with "arms leave `B_r` at the first step", and the degenerate case `n₁ = n₂` fails (2.2).
* **Proposition 15**: `P(A(n/2, N)) ≍ P(A(n, N))` needs `n/2 ≥ n₀(j)`.
* **Packs**: §3.2 above.
* **Half-plane (§4.6) and non-centred boxes ((4.20))**: asserted without proof.

## 5. What remains: A3b and later

In order, once the decisions of §2 and §3 are made:

1. **Lemma 15 on the four sides of an annulus** at any centre: transport with `translate`, `swap`,
   `reflect` and `law_comp_sym2Map_apply`; read the event back (walks by `SimpleGraph.Walk.map`,
   duals by `dualConfig_image_add`, `dualConfig_image_swap`, `dualConfig_image_reflect`).
2. **Barrier lemma** (pack-free): a walk of one colour joining two arms of that colour of a disjoint
   family is impossible when arms of the other colour separate them (from
   `sbtw_innerPos_iff_sbtw_landingPos`).
3. **Outer separation step**: `A(r, R) ∩ (good events of the four sides at scale R/2) ⊆` the
   separated event at `∂B_R`; with independence of the outer annulus,
   `law (A r R) ≤ law (separated) + 4δ · law (A r (R/2))`.
4. **Harris for a mixed order** (`Probability/`, general).
5. **Gluing**: separated with fences at `∂B_R` ⇒ landing in fixed windows at `∂B_{2R}`, probability
   at least `c(η)` times; corridors from bins to windows.
6. **Theorem 11** (outer, then inner by the same steps with internal strips), **extendability**,
   **quasi-multiplicativity** (lower half by separation at both ends and gluing in `B_{r₂} \ B_{r₂/4}`;
   `r₂ ≤ 8 r₁` by the one-scale bound), **a priori lower bound** (one-scale bound plus gluing
   at dyadic scales).
7. **Half-plane versions** (linear order: no packs among `OC`, `OCO`; strips only on the top side and
   the two half-sides) and **non-centred outer boxes** (`multiArmEventTo`, `B_{N/τ} ⊆ box ⊆ B_N`).

Rough size: items 1–3 one session, 4–5 one session, 6 one session, 7 half a session, plus (B) or (C)
for packs.

## 6. Notes for U1 and U2

* **U1** (`Arms/HalfPlaneExponents.lean`, two and three half-plane arms) does **not** depend on A3
  (plan §9: A1, PT2), and its sequences `OC`, `OCO` are pack-free. It can go ahead now. Useful here:
  `exists_pos_le_law_halfArmEvent` (one-scale half-plane lower bound, uniformly under crossing
  bounds) and `exists_isArm_of_mem_corridor` (arms from corridor crossings, with landing positions).
* **U2** (five arms, `OCOOC`) needs Theorem 11 for a sequence with a pack: blocked on §3.2.

## 7. Search

* PercLib: `exists_iso_swap`, `exists_iso_reflect_one`, `image_swap_Icc`, `image_mem_crossing_iff`,
  `image_mem_crossing_iff_of_rev`, `dualConfig_image_swap`, `dualEdge_map_swap`, `dualConfig_image_add`,
  `CrossingBounds.translate`, `law_translate_apply` (`MultiArmBounds.lean`: the translation case of
  `law_comp_sym2Map_apply`, which generalises it to any bijection), `law_preimage_image_sym2Map_eq`,
  `prodBernoulli_map_image_sym2`, `map_image_sym2Map_apply`, `prodBernoulli_iInter_fin_of_determined`,
  `mem_crossing_iff_of_inter_eq`, `CrossingBounds.le_law_crossing_one_of_le` and its dual,
  `exists_append_eq_of_notMem`, `exists_append_eq_of_exists_mem`, `mem_localConn_iff_exists_walk`,
  `mem_Icc_of_mem_dualEdge`, `dualEdge_map_add_one_dualEdge`, `Int.sbtw_iff`. Not found (added):
  crossing bounds under rotations or reflections, determination of dual crossings of a box of faces,
  extraction of a crossing walk (`IsCrossing`) from a box crossing. Not found (needed later): Harris
  for a mixed order.
* Mathlib: `Nat.lt_mul_div_succ`, `Nat.div_mul_le_self`, `Nat.le_div_iff_mul_le`,
  `Finset.prod_le_prod`, `Finset.prod_const`, `ENNReal.pow_pos`, `Sym2.out_fst_mem`,
  `SimpleGraph.Walk.transfer`, `SimpleGraph.Walk.adj_penultimate`,
  `SimpleGraph.Walk.penultimate_mem_dropLast_support`.

## 8. Lessons

* `lake env lean` does not run mathlib's style linters; `lake build --wfail` does (line length,
  counted in characters).
* `have h := hgB.2 i` for `hgB : g ∈ Icc lo hi` gives an inequality whose `≤` instance comes from
  the `Pi` order, which `omega` does not read; annotate: `have h : g i ≤ hi i := hgB.2 i`.
* `Set.mem_setOf_eq` is deprecated in this mathlib (`Set.mem_ofPred_eq`); `Finset.prod_le_prod'` too
  (`Finset.prod_le_prod`, one explicit argument for ordered monoids).
* `landingPos_true` and `landingPos_false` are `simp`/`rfl` forms that already apply
  `perimeterPos_two_smul`; rewrite with `perimeterPos_of_top` directly.
