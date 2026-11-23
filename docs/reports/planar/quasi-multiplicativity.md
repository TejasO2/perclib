# Separation of arms and quasi-multiplicativity: package A3, first part (A3a)

Advice note for package A3 of the arms plan (`docs/reports/planar/arms-plan.md` on branch
`claude/planar-arms-plan-0a97fc`, §2.4, §1.4 and §9 row A3). Source: P. Nolin, *Near-critical
percolation in two dimensions*, EJP 13 (2008), §§4.4–4.6, read through arXiv:0711.4948v1, where the
numbering is one lower in places (journal Theorem 11 = arXiv Theorem 10, journal Lemma 13 = arXiv
Lemma 12, journal Lemma 15 = arXiv Lemma 14, journal Propositions 16, 17 = arXiv Propositions 15,
16; the gluing of the plan's "Proposition 12" is arXiv Proposition 11, items 1–3).

**Status: A3 is not finished.** The A3a session proved the foundations listed below, checked
every plan statement at small scales, and found two problems in the route. The user's decisions on
them are recorded in "Decisions (user, 2026-11-22)" below. On 2026-11-23 the user resumed A3 for
colour sequences without packs ("Decisions (user, 2026-11-23)"). The A3b-1 session (§9) proved item 2
of §5 (sectors and the barrier) and found that items 1 and 3 cannot use Lemma 15 as stated: its
strip does not fit the arms of an annulus by half a lattice unit. A fix is proposed in §9.3 and needs
the user's word. Nothing in `Arms/Defs.lean` or `Planar/Defs.lean` was changed. Local commits only,
nothing pushed.

## Decisions (user, 2026-11-22)

1. **Small radii (§2): approved** ("Approve both"). Theorem 11, quasi-multiplicativity,
   extendability and the a priori lower bound get `∃ r₀ : ℕ`, chosen after `σ`, the landing data and
   `c`, before `q`, `L`, `z` and the radii, with `r₀ ≤ r` (`r₀ ≤ r₁` for quasi-multiplicativity).
   Extendability is stated in Nolin's direction: `law (A (2r) R) ≤ C * law (A r R)` with `r₀ ≤ r`
   (together with the outer half `law (A r R) ≤ C * law (A r (2R))`).
2. **Packs (§3.2): "Stop A3 for now".** A3 stays at A3a until the user has looked at the pack gap.
   A3b and the routes (A), (B), (C) are not started. U2 (`OCOOC`) is blocked on this.
3. **Separated event (§3.3): inline.** No new definition; the event is written out in the statements
   that need it when A3b resumes.

## Decisions (user, 2026-11-23)

1. **A3 resumes, without packs: "Yes, A3b then U1b".** Route (A) of §3.2: Theorem 11,
   quasi-multiplicativity and extendability carry the hypothesis
   `hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)` (no two cyclically consecutive arms of the same colour;
   the disjunct `j ≤ 1` is needed because for `j = 1` the second one fails). A separate read-only
   analysis checked that the barrier argument of §3.1 is sound for such sequences; a route for packs
   (a "first-pivot" rerouting) was proposed there and is **not** approved. The user was told that this
   delays only the five-arm upper bound of U2; U1, Stage 3 and the lower bounds of U2 use sequences
   without packs.
2. **Order of packages:** A3b-1 (items 1–3 of §5), A3b-2 (items 4–5), A3b-3 (item 6), A3b-4 (item 7),
   then U1b with the plan's colours `![true, false, true]`. One package per session.

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
only exclude small or degenerate scales, the same kind as the approved `N₀` of Lemma 15. **The
fixes are approved by the user (2026-11-22, decision 1); none of the corrected forms is proved
yet** (A3 is paused).

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

**Fix (approved):** `∃ C, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ q L, … → ∀ z r R, r₀ ≤ r → 2 * r ≤ R → …`,
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

**Fix (approved):** `∃ C, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ q L, … → ∀ z r₁ r₂ r₃, r₀ ≤ r₁ → r₁ ≤ r₂ →
r₂ ≤ r₃ → (r₃ : ℕ∞) ≤ L → upper ∧ lower`. With `r₀ ≥ j` both halves survive equal radii: for
`r ≥ j`, `A(r, r) = univ` (arms of length zero at consecutive positions down the left side of
`B_r(z)`: open arms at its vertices, positions `12r + 2(z₁ + r - y)`; dual arms at the faces just
left of it, positions `12r + 2(z₁ + r - y) - 1`, read through the last case of `perimeterPos`). The
upper half for `r₁ < r₂ < r₃` is A1's `law_multiArmEvent_le_mul` (with `C = 1`, every law).

### 2.3 Extendability: false for small `R`; second conjunct in the trivial direction

Plan: `law (A r R) ≤ C * law (A r (2R)) ∧ law (A r R) ≤ C * law (A (2r) R)`.

* **First conjunct, counterexample:** the profile of 2.2 with four open arms gives
  `law (A z 0 1) = 1/16 > 0 = law (A z 0 2)`. **Fix (approved):** `∃ r₀`, `r₀ ≤ r`.
* **Second conjunct:** `A(r, R) ⊆ A(2r, R)` for `2r < R` (`multiArmEvent_subset_of_le`), so it holds
  with `C = 1`; it is the trivial direction. Nolin's Prop. 16 (arXiv Prop. 15) has
  `P(A(n/2, N)) ≍ P(A(n, N))`, whose content is `law (A (2r) R) ≤ C * law (A r R)`. **Approved:**
  this direction is stated (with `r₀ ≤ r`); the plan's form is a remark.

### 2.4 The other statements

* **A priori lower bound** (Nolin arXiv Prop. 13): needs `r₀ ≤ r` for the same reason as 2.2 (and
  for `j ≥ 7` arms from a point Nolin's own statement is false: `A(0, N) = ∅`). The one-scale form
  proved here has `4j ≤ r`.
* **Half-plane and non-centred versions** inherit the same `r₀`.

## 3. Two problems in the route (decided: A3 paused, separated event inline)

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

In order (A3 resumed on 2026-11-23 without packs; after A3b-1, item 2 is done and items 1 and 3
wait for the fix of §9.3):

1. **Lemma 15 on the four sides of an annulus** at any centre: transport with `translate`, `swap`,
   `reflect` and `law_comp_sym2Map_apply`; read the event back (walks by `SimpleGraph.Walk.map`,
   duals by `dualConfig_image_add`, `dualConfig_image_swap`, `dualConfig_image_reflect`).
2. **Barrier lemma** (pack-free): a walk of one colour joining two arms of that colour of a disjoint
   family is impossible when arms of the other colour separate them (from
   `sbtw_innerPos_iff_sbtw_landingPos`). **Done in A3b-1** (§9.1), in a stronger form: every family of arms
   with the old inner positions is disjoint and in the old order.
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

## 9. A3b-1 (2026-11-23): sectors proved; Lemma 15's strip does not fit the arms

Package A3b-1 was to do items 1–3 of §5 for colour sequences without packs. **Item 2 is done**, in a
stronger form than planned. **Items 1 and 3 are not done**: the strip of Lemma 15
(`exists_law_separable_ge`) does not fit the arms of an annulus, on any side and for any choice of
the strip, by half a lattice unit. This is one of the stop conditions of the package, so the session
stopped there; a fix is proposed in §9.3. Proof-only: no definition, no tag, no `…Input`, no change
to either `Defs.lean`.

### 9.1 What is proved

New file `PercLib/Models/Planar/Arms/Sectors.lean` (imports `MultiArmBasics.lean` only), 7
theorems. Under the section hypotheses `hB : Icc (z - r) (z + r) ⊆ Icc (lo + 1) (hi - 1)`,
`hγ : ∀ i, IsArm ω (σ i) z r lo hi (γ i)`, `hd : ArmsDisjoint σ γ` and, where needed, the landing order
`ho : ∀ i k l, i < k → k < l → sbtw (landingPos lo hi (σ i) (γ i)) (landingPos … k) (landingPos … l)`
(the data of a member of `multiArmEventTo`):

```lean
/-- The barrier. -/
theorem ArmsDisjoint.of_innerPos_eq (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (hB) (hγ) (hd) (ho)
    {a' b' : Fin j → LatticeSite 2} {γ' : ∀ i, (zdGraph 2).Walk (a' i) (b' i)}
    (hγ' : ∀ i, IsArm ω (σ i) z r lo hi (γ' i))
    (hin : ∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) : ArmsDisjoint σ γ'

/-- The order (same hypotheses). -/
theorem sbtw_landingPos_of_innerPos_eq … (i k l : Fin j) (hik : i < k) (hkl : k < l) :
    sbtw (landingPos lo hi (σ i) (γ' i)) (landingPos lo hi (σ k) (γ' k))
      (landingPos lo hi (σ l) (γ' l))

/-- Sectors: two arms of one colour with the same inner position lie on the same side of any two
arms `k ≠ l` of the other colour of a disjoint family. -/
theorem sbtw_landingPos_iff_of_innerPos_eq (hB) (hγ) (hd) {k l : Fin j} (hkl : k ≠ l)
    (hσkl : σ k = σ l) {c : Bool} (hc : c ≠ σ k) (h₁ : IsArm ω c z r lo hi W₁)
    (h₂ : IsArm ω c z r lo hi W₂) (hin : innerPos z r c W₁ = innerPos z r c W₂) :
    sbtw (landingPos lo hi c W₁) (landingPos … (γ k)) (landingPos … (γ l)) ↔
      sbtw (landingPos lo hi c W₂) (landingPos … (γ k)) (landingPos … (γ l))
```

and the helpers `sbtw_apply_finRotate_apply` (any `CircularOrder`: if `f : Fin n → α` takes
increasing triples to triples in strict cyclic order, then `f x`, `f (finRotate n x)`, `f w` are in
strict cyclic order for every other `w`), `SimpleGraph.Walk.IsCrossing.append_of_append` and
`IsArm.append_of_append` (if `q.append s` and `q'.append s'` are crossings, resp. arms of one colour,
so is `q.append s'`), `IsDualArm.penultimate_eq` (two dual arms ending at the same face end with the
same dual edge: the last face is adjacent to exactly one face of the box).

**Proof of the barrier.** Suppose arms `γ' i`, `γ' i'` of one colour, `i ≠ i'`, share a vertex `v`
(after the first vertex of `γ' i`, for open arms) or a face. Joining `γ' i` up to `v` to `γ' i'` from
`v` gives an arm `W` (`IsArm.append_of_append`) with the inner position of `γ i` and the landing
position of `γ' i'` (if the dual arms share only their last face, `W = γ' i` works by
`IsDualArm.penultimate_eq`). Take `k = i + 1`, `l = i' + 1` (indices mod `j`): both have the other
colour (no packs), `k ≠ l`, and the original landing positions satisfy `sbtw (L i) (L k) (L l)` and
`¬ sbtw (L i') (L k) (L l)` (`sbtw_apply_finRotate_apply` twice and `sbtw_asymm`). The sector lemma
moves the first to `W`, the second to `γ' i'`; since `W` and `γ' i'` land at the same position, this
is a contradiction. The sector lemma is order invariance (`sbtw_innerPos_iff_sbtw_landingPos`, A1)
for the two three-arm families `W, γ k, γ l` and `γ i, γ k, γ l` (built with nested `Fin.cases`).

**Consequence for item 3.** After rerouting, nothing about the new family needs checking except
that each new walk is an arm to the same box with the old inner position: disjointness (also across
the four sides and in the overlaps of the strips at the corners) and the counterclockwise order of
the new tips follow. This replaces the case analysis of the barrier in the plan.

### 9.2 Items 1 and 3: the strip of Lemma 15 does not fit the arms of an annulus

The step of §5 item 3 applies Lemma 15 to the final crossing of each arm in a strip along the side
where it lands, and puts the rerouted crossing in place of it. For the new walk to be an arm to the
boundary of `B_R(z)`, two things are needed: **input**, the final crossings must be crossings of the
strip in Lemma 15's sense; **output**, the rerouted crossings must stay off `∂B_R(z)` before their
ends (open), resp. inside the faces of `B_R(z)` before their ends (dual). Take the top side.

* Arms of `B_R(z)`: an open arm lies in the vertex columns `[z₀ - R + 1, z₀ + R - 1]` before its last
  vertex; a dual arm lies in the face columns `[z₀ - R, z₀ + R - 1]` (faces spanning
  `x ∈ [z₀ - R, z₀ + R]`). The two colours have different horizontal extents.
* Lemma 15 in `Q = [lo₀, hi₀] × [lo₁, hi₁]`: open crossings in the vertex columns `[lo₀, hi₀]`, dual
  crossings in the face columns `[lo₀, hi₀ - 1]`, spanning `x ∈ [lo₀, hi₀]`: the same extent for both.
* Input for dual arms needs `lo₀ ≤ z₀ - R` and `hi₀ ≥ z₀ + R`; output for open arms needs
  `z₀ - R + 1 ≤ lo₀` and `hi₀ ≤ z₀ + R - 1`. No `Q` does both. (Vertically the two fit: both colours
  of Lemma 15 finish at the row `hi₁ = z₁ + R`, as the arms do.)

**Counterexample for the strip one column inside** (`Q = [z₀ - R + 1, z₀ + R - 1] × [z₁ + R - N,
z₁ + R]`, the choice of the pack analysis): a dual arm that runs up the column of faces
`z₀ + R - 1` along the right side of `B_R(z)` from below the strip to the face row `z₁ + R - 2`, then
left along that row to the column `z₀`, then up through the top side. It is a dual arm of `B_R(z)`
landing in the middle of the top side, but no piece of it is a bottom-top crossing of the box of
faces `[z₀ - R + 1, z₀ + R - 2] × [z₁ + R - N - 1, z₁ + R]`; it does not land on the right side either,
so no strip handles it. The faces missed are a column of length `N ≈ R/2` at each end of the strip,
not "`O(1)` columns at the corners", and corner protection does not remove them.

**Counterexample for the full-width strip** (`Q = [z₀ - R, z₀ + R] × …`): every input fits, but the
first greedy open crossing of `Q` may run up the column `z₀ - R`, which is the left side of `B_R(z)`.
A member rerouted to its tip touches `∂B_R(z)` before its end, so the new walk is not an arm to
`∂B_R(z)` (cutting it there loses the separation and the fence, which belong to its end), and
Lemma 15's statement gives no control over this.

**Also:** Lemma 15's statement lets the new crossings visit the top row before their ends. Its proof
does not (`exists_reroute_fence_of_exploration` cuts each member at its first top-row vertex, and the
greedy crossings meet the top row only at their tips), but the clause is not in the statement, and
without it a new walk can touch `∂B_R(z)` early at the top as well.

**Things that do not help.** Lemma 15 for `dualConfig ω` on the lattice of faces fits horizontally
but not vertically (the open arms would have to reach the row `z₁ + R + 1`). One strip per colour
(narrow for open, full-width for dual) loses the separation between tips of different colours, which
the gluing needs (adjacent open and dual tips must be far apart for their corridors); fences alone do
not give it. Cutting the arms at a smaller box (`B_{R-1}`) has the same mismatch one unit further in.
On the triangular lattice (site percolation, Nolin's setting) both colours live on the same sites,
which is why the source does not meet this.

### 9.3 Proposed fix: Lemma 15 in the arm box (package "A3b-0", proof-only, needs the user's word)

A new theorem beside `exists_law_separable_ge` (which stays as it is): the strip with the **open box
one column narrower on each side than the box of faces**, `[1, 4N + 1] × [0, N]` for open crossings and
faces `[0, 4N + 1] × [-1, N]` crossing edges of `[0, 4N + 2] × [0, N]` for dual ones, with one more
conclusion: **the new crossings meet the top row only at their ends**. For the top side of `B_R(z)`
with `R = 2N + 1` this is exactly the arm geometry (open `[z₀ - R + 1, z₀ + R - 1]`, faces
`[z₀ - R, z₀ + R - 1]`); other sides by `CrossingBounds.swap`, `.reflect`, `.translate`. Then every
arm landing on a side has its final crossing in that side's strip, every rerouted crossing extends to
an arm, and no corner protection of `B_R(z)` is needed.

Proof: A2 re-instantiated, with the open exploration in the narrow box and the dual exploration in
the wide box of faces. Checked in the code: the core of the mixed-colour separation,
`false_of_localConn_of_exploration` (`SeparationProtection.lean`), already asks the dual walk to lie in
the faces `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]` of the open box `[lo, hi]`, which for the narrow box are
exactly the wide face columns. What changes: the region hypothesis of
`add_lt_of_exploration_of_dualConfig` (`[lo₀ - 1, hi₀]` in place of `[lo₀, hi₀ - 1]`), the box relation
`hlo₂`, `hhi₂` of `separable_of_forall` and the corner bounds of its conclusion, the dual edges' box
in `mem_image_dualEdge_of_mem_edges`, and the probability side of `exists_law_separable_ge` with the
boxes moved (the open box is narrower, so the step-(a) bound in a narrower box still applies). The
top-row clause needs one more conjunct in `exists_reroute_fence_of_exploration` (its proof already
has it) and in `separable_of_forall`. Estimate: one session. Odd outer radius `R = 2N + 1`: Theorem 11
iterates over scales and can use `multiArmEvent_subset_of_le` to move between `R` and `R - 1`.

**Then item 3** (A3b-1 resumed) is: the four transported strips; for each arm its final crossing in
the strip of its side; the new walk = the arm up to the start of that crossing, then the rerouted
crossing; this is an arm with the old inner position (`innerPos_append`, the strip lies outside
`B_r(z)` once `r + 1 < R - N`); then `ArmsDisjoint.of_innerPos_eq` and `sbtw_landingPos_of_innerPos_eq`;
independence of the strips' good events (edges outside `B_{R-N-2}(z)` and the fence boxes) from
`multiArmEvent σ z r R'` for `R' ≤ R - N - 3`. Draft statement, with the separated event inline:

```lean
theorem exists_law_multiArmEvent_inter_not_separated_le {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ q L, CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N : ℕ),
      N₀ ≤ N → r + 3 ≤ N → ((2 * N + 1 : ℕ) : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r (2 * N + 1) ∩ {ω | ¬ ∃ (a b : Fin j → LatticeSite 2)
          (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, IsArm ω (σ i) z r (z - (2 * N + 1 : ℕ)) (z + (2 * N + 1 : ℕ)) (γ i)) ∧
        ArmsDisjoint σ γ ∧ (∀ i k l, i < k → k < l → sbtw …) ∧
        -- tips at doubled cyclic distance ≥ 4 √η N from each other and from the four corners
        … ∧
        -- a fence of colour σ i outside B_R(z) next to each tip, joined to the arm near the tip
        …}) ≤ δ * law q (multiArmEvent σ z r (N - 2))
```

Here `R = 2N + 1` and `N - 2 = R - N - 3`; the exact constants are for that session. The fence clause
has to be written once per side (four cases, in the coordinates of that side) or
uniformly with a box around the tip and the perimeter position; I recommend the four cases, read off
Lemma 15 through the three symmetries, since item 5 needs them in that form anyway.

### 9.4 For A3b-2 (gluing)

* The barrier works in one box. The gluing's fence connections (from a vertex `x` of the arm to the
  fence, inside the ball of radius `⌊√η N⌋` around the tip) can leave `B_R(z)` and come back. To show
  that such a connection of arm `i` meets no other arm `k` of its colour: if it did, at `y`, take the
  last entry point `e ∈ ∂B_R(z)` of the connection before `y`; then `γ k` up to `y`, followed by the
  connection backwards from `y` to `e`, is an arm with the inner position of `γ k` landing at `e`,
  within `2⌊√η N⌋` of the tip of `i`; by `sbtw_landingPos_iff_of_innerPos_eq` it lands in the sector
  of `k`, but the neighbours of `i` land at least `4 √η N` away from its tip, so `e` is in the sector of
  `i`: contradiction. (When the connection does not leave `B_R(z)`, `ArmsDisjoint.of_innerPos_eq` applies
  directly.)
* Still needed, as recorded in §3.3: Harris for a mixed order (`Probability/`, general) and the
  corridors from bins to windows.

### 9.5 Search

* Mathlib: `sbtw_cyclic_left`, `sbtw_cyclic_right`, `sbtw_asymm`, `Int.sbtw_iff` (and the instance
  `CircularOrder ℤ` in `Order/Circular/ZMod.lean`), `finRotate_of_lt`, `finRotate_last`,
  `Fin.val_lt_last`, `Fin.pos_iff_ne_zero`, `SimpleGraph.Walk.take_spec`, `tail_support_append`,
  `support_append_eq_support_dropLast_append`, `List.dropLast_append_of_ne_nil`,
  `SimpleGraph.Walk.adj_penultimate`, `SimpleGraph.Walk.Nil.eq`. Searched and not found: a lemma on
  the successor in a cyclically ordered `Fin n`-family (no file of mathlib mentions both `sbtw` and
  `finRotate`), a join of two walks at a common vertex that keeps a crossing property.
* PercLib: `sbtw_innerPos_iff_sbtw_landingPos`, `innerPos_append`, `landingPos_append`,
  `IsArm.not_nil`, `armsDisjoint_of_subsingleton`, `IsCrossing.eq_end_of_notMem`,
  `IsCrossing.penultimate_mem`, `zdGraph_two_adj_iff`, `mem_Icc_two_iff`; the in-proof joins
  `(q.takeUntil …).append (r.dropUntil …)` of `Separation.lean` and `SeparationSurgery.lean` are not
  lemmas. For §9.2–§9.3: `exists_law_separable_ge`, `separable_of_forall`,
  `exists_reroute_fence_of_exploration`, `add_lt_of_exploration_of_dualConfig`,
  `add_lt_of_exploration_dualConfig`, `false_of_localConn_of_exploration`.

### 9.6 Lessons

* Section variables `lo hi` (box corners) clash with hypotheses named `hi : σ i = true`: the error is
  an application type mismatch in `IsOpenArm ω z r lo hi`. Name colour hypotheses `hσi`.
* A three-arm family for order invariance: nested `@Fin.cases` with explicit motives
  (`fun t => (zdGraph 2).Walk (A t) (B t)`, then `A t.succ`, `A t.succ.succ`, last level
  `fun t => t.elim0`); after `fin_cases t` the goals close with `exact` by definitional unfolding, and
  `ArmsDisjoint` of the triple by `fin_cases t <;> fin_cases u` (nine goals).
* Split an arm at a vertex with `rw [← SimpleGraph.Walk.take_spec (γ i) hv] at h`; to rewrite only
  one side of a goal, `conv_rhs => rw [← SimpleGraph.Walk.take_spec …]`.
