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
strip does not fit the arms of an annulus by half a lattice unit. A fix was proposed in §9.3; the
A3b-0 session (§10) proved it: Lemma 15 in the arm box, `exists_law_separable_ge_arm`, with the new
crossings meeting the top row only at their ends (`exists_law_separable_ge` unchanged). The resumed
A3b-1 session (§11) did items 1 and 3 of §5: Lemma 15 on the four sides of `B_R(z)` at any centre
(`exists_law_separable_ge_sides`) and the outer separation step for colour sequences without packs
(`exists_separating_event`, `exists_law_multiArmEvent_inter_not_separated_le`). On the user's
decision of 2026-11-23 ("Yes, new Defs file") the separated event of the outer step became a
definition, `outerSeparatedArmEvent`, in the new interface module `Arms/Separation/Defs.lean` (§12);
the outer step is restated with it, with definitionally equal statements. The A3b-2 session (§13)
proved item 4 (Harris for a mixed order, general) and the corridor-independent half of item 5
(conditioning on the separated event, the fence-connection argument, the gluing of continuations);
the corridors, bins and the gluing statement remain (A3b-2b, §13.5). The A3b-2b session (§14) proved
the gluing statement with straight corridors (`exists_pos_le_law_multiArmEventIn_of_separated`) on
top of a gluing lemma for arbitrary corridor events (`law_mul_prod_le_law_of_corridors`); landing in
fixed windows (staged rotation) and fences at `∂B_{R'}` are designed in §14.4 and not proved
(A3b-2c). The A3b-2c session (§15) proved fences at `∂B_{R'}` (caps) for corridors that move each arm
along its side (jogs), the first gluing with fences at the new boundary for straight corridors
(`exists_pos_le_law_separated_of_separated`) and the window-to-window step
(`exists_pos_le_law_windows_of_windows`, constant independent of the separation scale); the rotation
into fixed windows (corridors turning round the corners and a motion plan) and the two-sided gluing
are designed in §15.4 and not proved (A3b-2d). Nothing in `Arms/Defs.lean` or `Planar/Defs.lean` was
changed. Local commits only, nothing pushed.

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

In order (A3 resumed on 2026-11-23 without packs; after A3b-1, item 2 is done; after A3b-0 (§10)
the arm-box form of Lemma 15 is proved; after the resumed A3b-1 (§11), items 1 and 3 are done, with
an inner radius `N` in place of `R/2` in item 3):

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

## 10. A3b-0 (2026-11-23): Lemma 15 in the arm box

The fix of §9.3, run as a proof-only helper package with the coordinator's approval. **Done:** the
arm-box form of Lemma 15, `exists_law_separable_ge_arm`, with the extra conclusion that the new
crossings meet the top row only at their ends; `exists_law_separable_ge` keeps its statement and
docstring byte for byte and is now read off the same general theorem. **Not done:** item 1 of §5
(the transport to the four sides of `B_R(z)` at any centre); it is left to the resumed A3b-1 (§10.5).
No definition, no tag, no `…Input`; `Planar/Defs.lean` and `Arms/Defs.lean` unchanged. Lean commit
`d6c9df7` (`SeparationLemma.lean`, `SeparationSurgery.lean`); `#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`. Gate: `scripts/gate.sh main` **passed on `d6c9df7`** (axiom audit 9847
constants; the expected interface NOTICE from `Arms/Defs.lean`, no other notice; 4.8 min). This
note's commit changes only `docs/`.

### 10.1 The statement proved

`PercLib/Models/Planar/Arms/SeparationLemma.lean`, after `exists_law_separable_ge`:

```lean
theorem exists_law_separable_ge_arm (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ N : ℕ, N₀ ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = 0 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![1, 0] : LatticeSite 2) ![4 * (N : ℤ) + 1, N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = -1 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![0, -1] : LatticeSite 2) ![4 * (N : ℤ) + 1, N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ) + 2, N]})) →
        (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
        ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i) (… the same two clauses for b', γ' …)) ∧
          (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ' i).support, x ∉ (γ' j).support) ∧
          (∀ i, ∀ x ∈ (γ' i).support.dropLast, x 1 ≠ N) ∧          -- top row only at the end
          (∀ i j, i ≠ j → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' j 0 + cond (σ j) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ 8 * N + 4 - ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,   -- the fence, as in Lemma 15
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, N] ![b' i 0 + ⌊η * N⌋₊, N + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}
```

Same quantifier shape as `exists_law_separable_ge` (`η` and `N₀` before the law, `N₀ ≤ N ≤ L`),
same constants (`η = 1/D²`, `N₀ = D²`, `D = 16 · 8^J`). The top-row clause is stated with
`support.dropLast`, so the end is not visited twice either; this is what `IsCrossing` asks of an
arm. The corners are measured from the ends `0` and `8N + 4` of the doubled top side of the arm box
(the proof gives at least that from the open box's ends as well).

Both forms are instances of `exists_law_separable_ge_aux`: the same statement for the open box
`Icc lo hi`, `hi = ![lo 0 + 4N, lo 1 + N]`, the box of faces `lo₂ = ![lo 0 - k, lo 1 - 1]`,
`hi₂ = ![hi 0 - 1 + k, hi 1]`, crossed edges in `Icc elo ehi` with `elo = ![lo 0 - k, lo 1]`,
`ehi = ![hi 0 + k, hi 1]`, `0 ≤ k ≤ 1`, corners from `2 elo₀` and `2 ehi₀`, plus the top-row clause.
The boxes are variables with defining equations (eleven hypotheses, reason in the docstring), so
that each instance is read off by definitional unfolding (`![a, b] 1` is `b`, `(0 : LatticeSite 2) 1`
is `0`) and only the corner clause needs a cast rewrite. `k = 0`, `lo = 0` gives
`exists_law_separable_ge`; `k = 1`, `lo = ![1, 0]` gives `exists_law_separable_ge_arm`.

### 10.2 The coordinates, checked against `IsOpenArm` / `IsDualArm`

§9.3's coordinates are right; nothing had to be corrected. Take `R = 2N + 1` and
`z = (2N + 1, -N - 1)`, so `Icc (z - R) (z + R) = [0, 4N + 2] × [-3N - 2, N]` and its top side is the
row `N`.

| | arm of `B_R(z)` (`Arms/Defs.lean`) | strip of `exists_law_separable_ge_arm` |
|---|---|---|
| open, before the last vertex | `Icc (lo + 1) (hi - 1) = [1, 4N + 1] × [-3N - 1, N - 1]` | `[1, 4N + 1] × [0, N]`, row `N` only at the end |
| open, last vertex on the top side | `(x, N)`, `1 ≤ x ≤ 4N + 1` (one step from the interior) | `b' i = (x, N)`, `x ∈ [1, 4N + 1]` |
| dual, faces before the last | `Icc lo (hi - 1) = [0, 4N + 1] × [-3N - 2, N - 1]` | `[0, 4N + 1] × [-1, N]`, row `N` only at the end |
| dual, last face on the top side | `(x, N)`, `0 ≤ x ≤ 4N + 1` | `b' i = (x, N)`, `x ∈ [0, 4N + 1]` |
| dual edges | cross edges with both ends in `Icc lo hi` | cross edges of `[0, 4N + 2] × [0, N]` |
| doubled top-side column (`landingPos`) | open `2x` (from `2 • b`), dual `2x + 1` (from `penultimate + b + 1 = (2x + 1, 2N)`) | `2 b' i 0 + cond (σ i) 0 1` |
| ends of the doubled top side | `2 (z₀ - R) = 0`, `2 (z₀ + R) = 8N + 4` | `0`, `8N + 4` |

**Input.** The final crossing of an open arm landing on the top side (its part after its last
visit to the row `0`) starts on the row `0`, stays in the rows `1 … N - 1` and the columns
`1 … 4N + 1`, and ends at `(x, N)`: a crossing of the open strip. The final crossing of a dual arm
landing there (after its last visit to the face row `-1`) is a walk of faces of `[0, 4N + 1] × [-1, N]`
meeting the row `-1` only at its start and the row `N` only at its end, so by
`mem_image_dualEdge_of_mem_edges` (with its box `[0, 4N + 2] × [0, N]`) its dual edges cross edges of
`[0, 4N + 2] × [0, N]`. Both need the arm to reach the strip's bottom row, which holds when
`B_r(z)` (rows `≤ -N - 1 + r`) lies below it.

**Output.** A rerouted open crossing lies in `[1, 4N + 1] × [0, N - 1]` before its end, inside the
interior of the arm box; a rerouted dual crossing lies in the faces `[0, 4N + 1] × [-1, N - 1]`
before its end, inside the faces of the arm box; its last face `(x, N)` is outside. So the arm up to
the start of its final crossing, followed by the rerouted crossing, is again an arm of `B_R(z)` with
the old inner position, as soon as the strip does not touch `B_r(z)` (open: `r ≤ N`; faces touching
`B_r(z)`: rows `≤ -N - 1 + r < -1` needs `r < N`). This is exactly what `ArmsDisjoint.of_innerPos_eq`
and `sbtw_landingPos_of_innerPos_eq` (§9.1) take.

### 10.3 What changed in A2's lemmas (all plain generalisations; every caller adapted)

* `exists_reroute_of_exploration` (`SeparationSurgery.lean`): one more conjunct, last: every vertex
  of a new walk before its last entry is a vertex of the member before its last entry, or a vertex
  of the chosen crossing other than its tip. Proof: the new walk is `P.append R` with `P`, `R` paths
  (`exists_reroute_aux`), `support_append_eq_support_dropLast_append`, and a path's end is not in
  `support.dropLast` (`dropLast_support_concat`, `List.nodup_append`).
* `exists_reroute_fence_of_exploration`: one more conjunct, before the fence:
  `∀ i ∈ S, ∀ x ∈ (γ' i).2.support.dropLast, x 1 ≠ hi 1` (members are first cut at their first
  top-row vertex, chosen crossings meet the top row only at their tips).
* `add_lt_of_exploration_of_dualConfig`: the dual path may lie in the faces
  `[lo₀ - 1, hi₀] × [lo₁ - 1, hi₁]` (was `[lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]`): a weaker hypothesis. After
  trimming the two end rows the path lies in `[lo₀ - 1, hi₀] × [lo₁, hi₁ - 1]`, which is what
  `false_of_localConn_of_exploration` already accepted.
* `separable_of_forall`: new `{k : ℤ} (hk : 0 ≤ k) (hk1 : k ≤ 1)`, box relation
  `hlo₂ : lo₂ = ![lo 0 - k, lo 1 - 1]`, `hhi₂ : hi₂ = ![hi 0 - 1 + k, hi 1]` (was `k = 0`); crossed
  edges in `Icc ![lo 0 - k, lo 1] ![hi 0 + k, hi 1]` (was `Icc lo hi`); corners from `2 (lo₀ - k)` and
  `2 (hi₀ + k)` (was `2 lo₀`, `2 hi₀`); one more conjunct (top row only at the ends), before the fence.
  The other-colour protection of a dual tip (`add_lt_of_exploration_dualConfig`) already accepted open
  walks in `[lo₂₀, hi₂₀ + 1] × [lo₂₁ + 1, hi₂₁] ⊇ Icc lo hi`; the corner and same-colour lemmas are
  per box and unchanged.
* `exists_law_separable_ge`: proof replaced by the instance `k = 0` of the new
  `exists_law_separable_ge_aux` (the old proof, with the boxes as variables); statement unchanged.
* Unchanged: `mem_image_dualEdge_of_mem_edges` (already general in its box; called with
  `![lo 0 - k, lo 1]`, `![hi 0 + k, hi 1]`), `false_of_localConn_of_exploration`, `exists_walk_trim`,
  `lt_tip_of_corner`, `lt_abs_sub_of_exploration`, `exists_fence_of_le`, all of `SeparationEvents.lean`
  (the step-(a) bounds `law_exploration_le_pow_of_le` / `…_dualConfig_…` take the open box with
  `n = N - 1` and the box of faces with `n = N`, width at most `5n` for `N ≥ 5`).

Callers: the changed lemmas are used only inside `SeparationLemma.lean`; `QuasiMultiplicativity.lean`
mentions `exists_law_separable_ge` only in its module docstring.

### 10.4 Search

* Mathlib: `SimpleGraph.Walk.support_append_eq_support_dropLast_append`,
  `SimpleGraph.Walk.dropLast_support_concat`, `SimpleGraph.Walk.support_ne_nil`,
  `SimpleGraph.Walk.support_copy`, `List.dropLast_append_of_ne_nil`, `List.nodup_append`,
  `SimpleGraph.Walk.IsPath.support_nodup`. Searched and not found: "the end of a path is not in
  `support.dropLast`" (two lines inline).
* PercLib: the A2 lemmas above, `eq_vec_two_iff`, `mem_Icc_two_iff`; for §10.5:
  `measurableSet_of_determined_finite` (`Percolation/Bond/CrossEdge.lean:66`),
  `measurableSet_of_determined_finset` (`Probability/CylinderLimit.lean:137`),
  `dualConfig_image_add` (`Arms/Defs.lean`), `dualConfig_image_swap` (`CrossingSymmetry.lean`),
  `dualConfig_image_reflect`, `law_comp_sym2Map_apply`, `CrossingBounds.swap`, `CrossingBounds.reflect`
  (`QuasiMultiplicativity.lean`), `innerPos_append` (`MultiArmBasics.lean`).

### 10.5 For the resumed A3b-1 (items 1 and 3 of §5)

1. **Item 1, the transport (not done here).** Top side of `B_R(z)`, `R = 2N + 1`, any `z`: translate
   `exists_law_separable_ge_arm` by `z - (2N + 1, -N - 1)` (`dualConfig_image_add`, translation
   invariance of `CrossingBounds`). The other three sides by quarter turns (`CrossingBounds.swap` and
   `.reflect`, `dualConfig_image_swap`, `dualConfig_image_reflect`, `law_comp_sym2Map_apply`); faces are
   labelled by their lower-left corners, so a reflection moves faces by one unit
   (`dualConfig_image_reflect`). Write the four results in their own coordinates (recommended in §9.3):
   for example the strip of the right side should be `[z₀ + R - N, z₀ + R] × [z₁ - R + 1, z₁ + R - 1]`
   for open crossings (left to right) and the faces `[z₀ + R - N - 1, z₀ + R] × [z₁ - R, z₁ + R - 1]`
   (not yet checked in Lean).
2. **Measurability of the strip event.** The theorem bounds `law q S` from below for the
   set-builder `S`; the outer step needs `S` (or its complement) measurable and independent of
   `multiArmEvent σ z r R'`. `S` depends on `ω` only through edges with both ends in
   `[-M, 4N + 2 + M] × [0, N + M]`, `M = ⌊√η N⌋ < N` (open walks in the open box, dual edges crossing
   edges of `[0, 4N + 2] × [0, N]`, fence connections in the boxes and balls at the row `N`). Prove
   `ω ∩ W = ω' ∩ W → (ω ∈ S ↔ ω' ∈ S)` and use `measurableSet_of_determined_finite`. In the arm box,
   `B_{R'}(z)` has rows `≤ -N - 1 + R'`, below the row `0` for `R' ≤ N`: independence by disjoint edge
   sets. (The proof's bad set is measurable, but the statement does not expose it; the old
   `exists_law_separable_ge` has the same shape.)
3. **Item 3** as in §9.3, with the inputs of §10.2: for `r < N`, the final crossing of each arm in the
   strip of its side is a crossing of that strip; the rerouted crossing extends the arm's beginning
   to an arm with the old inner position (`innerPos_append`, top-row clause); then
   `ArmsDisjoint.of_innerPos_eq` and `sbtw_landingPos_of_innerPos_eq`. Tips on one side are
   `4 √η N` apart and `4 √η N` from that side's corners, so tips on different sides are at least
   `8 √η N` apart in landing positions. The draft statement of §9.3
   (`exists_law_multiArmEvent_inter_not_separated_le`, `r + 3 ≤ N`, inner radius `N - 2`) fits these
   coordinates.

### 10.6 Lessons

* The whole package compiled at the first build of each module (`SeparationSurgery` 7 s; the chain
  `SeparationProtection` → `SeparationLemma` 25 s).
* A general probability theorem with its boxes as universally quantified variables plus defining
  equations (`hi = ![…]`, `lo₂ = ![…]`, …) gives instances by plain application: the event of the
  instance matches by definitional unfolding (`![a, b] 1 ≡ b`, `(0 : LatticeSite 2) 1 ≡ 0`), and the
  equations close with `eq_vec_two_iff.2 ⟨by simp, by simp⟩` (`ring` after
  `simp only [Matrix.cons_val_zero]` for `4N + 1 = 1 + 4N`). `subst` the equations of boxes that
  appear only as `Icc elo ehi`; keep the others as variables with coordinate facts for `omega`.
* The new walk of the surgery is `((P i).2.2.append ((R i).2.2.copy …)).copy …`: unfold `γ'` with
  `rw [hγ']; dsimp only; rw [dite_eq_left hi, support_copy, support_append_eq_support_dropLast_append,
  support_copy, List.dropLast_append_of_ne_nil (support_ne_nil _)]`.

## 11. A3b-1 resumed (2026-11-23): Lemma 15 on the four sides; the outer separation step

Items 1 and 3 of §5, on top of A3b-0 (§10). **Both are done.** Proof-only: no definition, no tag, no
`…Input`; `Planar/Defs.lean` and `Arms/Defs.lean` unchanged. Two new modules, imported from
`PercLib.lean`: `Arms/SeparationSides.lean` (item 1, 8 theorems) and `Arms/OuterSeparation.lean`
(item 3, 22 theorems); one helper strengthened in `Arms/SeparationLemma.lean` (§11.3). Lean commit
`a2df0f1`; `#print axioms` of the main results: `propext`, `Classical.choice`, `Quot.sound`. Gate:
`scripts/gate.sh main` **passed on `a2df0f1`** (axiom audit 10135 constants; the expected interface
NOTICE from `Arms/Defs.lean`, no other notice; about 5 min). This note's commit changes only `docs/`.

### 11.1 Item 1: Lemma 15 on the four sides of `B_R(z)`

`SeparationSides.lean`. `R = 2N + 1`, any centre `z`, `M = ⌊√η N⌋`, `K = ⌊η N⌋`.

* `exists_law_separable_ge_top`: `∃ η, 0 < η ∧ η ≤ 1 ∧ ∃ N₀, ∀ q L, CrossingBounds q L c → ∀ z N R,
  R = 2N + 1 → N₀ ≤ N → N ≤ L → 1 - δ ≤ law q {ω | …}`, the event of `exists_law_separable_ge_arm`
  moved to the top side of `B_R(z)` (it is the `k = 1` instance of `exists_law_separable_ge_aux` at
  `lo = (z₀ - R + 1, z₁ + R - N)`, so no translation is needed), for **families indexed by any finite
  type** (`∀ (ι : Type) [Finite ι]`, reindexed from `Fin m` inside the proof), so that it applies to
  the subfamily of arms landing on one side.
* `mem_separable_top_of_inter_eq`: if `M ≤ N` and `ω`, `ω'` agree on the edges with both ends in
  `[z₀ - R - M - K, z₀ + R + M + K] × [z₁ + R - N, z₁ + R + M + 1]`, then `ω` is in the top-side event
  iff `ω'` is (stated as an implication; used both ways).
* `separable_right_of_top`, `separable_bottom_of_top`, `separable_left_of_top`: if the configuration
  moved by the swap `(x, y) ↦ (y, x)`, the reflection `(x, y) ↦ (x, -y)`, resp. the quarter turn
  `(x, y) ↦ (y, -x)` has the top-side property at the moved centre `zf` (given by its coordinates,
  `hzf0`, `hzf1`), then the configuration has the side property, written in the coordinates of the
  side. Open crossings are moved by the map, dual crossings by the map of faces (the same for the
  swap; `(x, y) ↦ (x, -1 - y)` and `(x, y) ↦ (y, -1 - x)` for the other two, from
  `dualConfig_image_reflect`).
* `exists_law_separable_ge_sides`: one `η`, one `N₀` for the four sides: `1 - δ ≤ law q E_top ∧
  1 - δ ≤ law q E_right ∧ 1 - δ ≤ law q E_bottom ∧ 1 - δ ≤ law q E_left` (laws through
  `CrossingBounds.swap`, `.reflect`, `.swap.reflect` and `law_comp_sym2Map_apply`).
* helpers `image_sym2Map_inter_edgeSet`, `inter_edgeSet_mem_localConn_of_image` (connections through
  an automorphism of `ℤ²`, a wrapper of `localConn_of_image`).

The four events in their own coordinates (open crossings / dual crossings of faces / crossed edges;
`d` is the doubled coordinate of the end along the side, `cond c 0 1` the dual half-step):

| side | open strip | faces | crossed edges in | end | `d` | corners | fence box (`b'` the end) |
|---|---|---|---|---|---|---|---|
| top | `[z₀-R+1, z₀+R-1] × [z₁+R-N, z₁+R]` | `[z₀-R, z₀+R-1] × [z₁+R-N-1, z₁+R]` | `[z₀-R, z₀+R] × [z₁+R-N, z₁+R]` | row `z₁+R` | `2b'₀+[dual]` | `2(z₀∓R)` | `[b'₀-K, b'₀+K] × [z₁+R, z₁+R+M]`, left to right |
| right | `[z₀+R-N, z₀+R] × [z₁-R+1, z₁+R-1]` | `[z₀+R-N-1, z₀+R] × [z₁-R, z₁+R-1]` | `[z₀+R-N, z₀+R] × [z₁-R, z₁+R]` | column `z₀+R` | `2b'₁+[dual]` | `2(z₁∓R)` | `[b'₀, b'₀+M] × [b'₁-K, b'₁+K]`, bottom to top |
| bottom | `[z₀-R+1, z₀+R-1] × [z₁-R, z₁-R+N]` | `[z₀-R, z₀+R-1] × [z₁-R-1, z₁-R+N]` | `[z₀-R, z₀+R] × [z₁-R, z₁-R+N]` | row `z₁-R` (open), `z₁-R-1` (dual) | `2b'₀+[dual]` | `2(z₀∓R)` | `[b'₀-K, b'₀+K] × [b'₁-M, b'₁]`, left to right |
| left | `[z₀-R, z₀-R+N] × [z₁-R+1, z₁+R-1]` | `[z₀-R-1, z₀-R+N] × [z₁-R, z₁+R-1]` | `[z₀-R, z₀-R+N] × [z₁-R, z₁+R]` | column `z₀-R` (open), `z₀-R-1` (dual) | `2b'₁+[dual]` | `2(z₁∓R)` | `[b'₀-M, b'₀] × [b'₁-K, b'₁+K]`, bottom to top |

Starts: the inner row (column) of the strip: `z₁+R-N` / `z₁+R-N-1` (top, open / dual), `z₀+R-N` /
`z₀+R-N-1` (right), `z₁-R+N` (bottom, both colours), `z₀-R+N` (left, both colours). The new crossings
meet the outer row (column) only at their ends: `x 1 ≠ z₁ + R` (top, as in Lemma 15), `x 0 ≠ b' i 0`
(right, left), `x 1 ≠ b' i 1` (bottom). The ball of the fence is `Icc (b' - M) (b' + M)` on every side.

### 11.2 Item 3: the outer separation step

`OuterSeparation.lean`. Two forms, both for `σ` with `hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)`
and `0 < δ`:

```lean
theorem exists_separating_event … :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ q L, CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ),
      R = 2 * N + 1 → N₀ ≤ N → (N : ℕ∞) ≤ L → ∃ G : Set (Config (LatticeSite 2)), MeasurableSet G ∧
        (∀ ω ω', ω ∩ {e | ∀ v ∈ e, v ∈ Icc (z - 2R) (z + 2R) \ Icc (z - N) (z + N)} = ω' ∩ {…} →
          (ω ∈ G ↔ ω' ∈ G)) ∧
        1 - δ ≤ law q G ∧ ∀ r < N, ∀ ω ∈ multiArmEvent σ z r R ∩ G, SEPARATED(ω)

theorem exists_law_multiArmEvent_inter_not_separated_le … :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ q L, CrossingBounds q L c → ∀ (z : LatticeSite 2) (r N R : ℕ),
      R = 2 * N + 1 → N₀ ≤ N → r < N → (N : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R ∩ {ω | ¬ SEPARATED(ω)}) ≤ δ * law q (multiArmEvent σ z r N)
```

with `SEPARATED(ω)` written inline (`L i` short for `landingPos (z - R) (z + R) (σ i) (γ i)`):

```lean
∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
  (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
  (∀ i k l, i < k → k < l → sbtw (L i) (L k) (L l)) ∧
  (∀ i k, i ≠ k → 4 * √η * N ≤ |L i - L k|) ∧
  (∀ i (m : ℕ), 4 * √η * N ≤ |L i - 4 * m * R|) ∧
  ∀ i, ∃ x ∈ (γ i).support, ∃ l r',
    G_i ∩ E ∈ localConn (Icc (b i - M) (b i + M)) x l ∧
    ((b i 1 = z 1 + R ∧ l 0 = b i 0 - K ∧ r' 0 = b i 0 + K ∧
        G_i ∩ E ∈ localConn (Icc ![b i 0 - K, b i 1] ![b i 0 + K, b i 1 + M]) l r') ∨
     (b i 0 = z 0 + R ∧ l 1 = b i 1 - K ∧ r' 1 = b i 1 + K ∧
        G_i ∩ E ∈ localConn (Icc ![b i 0, b i 1 - K] ![b i 0 + M, b i 1 + K]) l r') ∨
     (b i 1 = z 1 - R - cond (σ i) 0 1 ∧ l 0 = b i 0 - K ∧ r' 0 = b i 0 + K ∧
        G_i ∩ E ∈ localConn (Icc ![b i 0 - K, b i 1 - M] ![b i 0 + K, b i 1]) l r') ∨
     (b i 0 = z 0 - R - cond (σ i) 0 1 ∧ l 1 = b i 1 - K ∧ r' 1 = b i 1 + K ∧
        G_i ∩ E ∈ localConn (Icc ![b i 0 - M, b i 1 - K] ![b i 0, b i 1 + K]) l r'))
```

(`G_i = cond (σ i) ω (dualConfig ω)`, `E` the edges of `ℤ²`, real casts as in the file). `G` is the
intersection of the four side events, moved to the frames (top event of `exists_law_separable_ge_top`
at `z`, at `(z₁, z₀)` for the swapped configuration, at `(z₀, -z₁)` for the reflected one, at
`(z₁, -z₀)` for the turned one). Proof of the inclusion: on each side, `IsArm.exists_append_eq_*` cuts
every arm landing there at its last vertex (face) on the inner row of the strip; the final pieces are
crossings of the strip in the sense of the side event; the side event reroutes them;
`IsArm.append_right` glues each first piece to its rerouted crossing (an arm with the old start and
first step, so the old inner position by `innerPos_append`); `IsArm.landingPos_eq_of_*` turns the
doubled end coordinates into landing positions (top `8R + 2(z₀+R) - d`, right `4R + d - 2(z₁-R)`,
bottom `d - 2(z₀-R)`, left `12R + 2(z₁+R) - d`), so the side's separation and corner bounds give
landing positions `4 √η N` apart inside `[4nR + 4 √η N, 4(n+1)R - 4 √η N]` for the side index `n`;
arms on different sides are then `≥ 8 √η N` apart. Every arm lands on exactly one side
(`IsArm.end_mem_sides`). Disjointness and order: `ArmsDisjoint.of_innerPos_eq`,
`sbtw_landingPos_of_innerPos_eq` (A3b-1's barrier), applied once to the whole new family, so the
overlaps of the strips at the corners and the arms of the other sides need no separate argument, as
§9.1 predicted. Probability: `G` depends only on edges with both ends in `B_{2R}(z) \ B_N(z)` (each
frame box lies there since `M, K ≤ N`), `multiArmEvent σ z r N` only on edges inside `B_N(z)`
(`mem_multiArmEventTo_iff_of_inter_eq`), so `prodBernoulli_inter_of_determined` applies; and
`multiArmEvent σ z r R ⊆ multiArmEvent σ z r N` for `r < N` (`multiArmEvent_subset_of_le`).

**The independence of §9.3 holds as set up** (stop condition not triggered), with a larger inner box:
inner radius `N` instead of `N - 2`.

### 11.3 Deviations

1. **Inner radius `N`, hypothesis `r < N`** (draft of §9.3: `N - 2` and `r + 3 ≤ N`). Both are weaker
   hypotheses / a stronger bound: the strips start at the row `z₁ + N + 1` (faces `z₁ + N`) and the
   fence balls stay above it once `⌊√η N⌋ ≤ N`.
2. **`δ`, not `4δ`**: Lemma 15 is applied with `δ / 4`.
3. **`η ≤ 1` is exposed** in both statements and in `exists_law_separable_ge_top`/`_sides`; for it,
   `exists_law_separable_ge_aux` (the A3b-0 helper) now also returns `η ≤ 1` (its `η = 1/D²`). The
   statements of `exists_law_separable_ge` (the approved Lemma 15) and `exists_law_separable_ge_arm`
   are unchanged; their proofs drop the new conjunct. Without `η ≤ 1` the fence balls
   (`⌊√η N⌋` around the ends) could reach into `B_N(z)` and the independence would fail.
4. **Event form added** (`exists_separating_event`): the inclusion `A(r, R) ∩ G ⊆ SEPARATED` with
   `G` determined by the annulus `B_{2R}(z) \ B_N(z)` and independent of `r`. The probability bound is
   its corollary. A3b-3 will need the event form (§11.4).
5. **Families of crossings indexed by any finite type** in item 1 (Lemma 15 itself has `Fin m`).
6. **Corners stated for all `m : ℕ`** (`|L i - 4mR| ≥ 4 √η N`) and separation with the linear `|·|`;
   together they give the cyclic separation (all positions lie in `[4 √η N, 16R - 4 √η N]`).
7. The transports use **linear maps at moved centres** (swap, reflection, quarter turn) rather than
   translations plus rotations about `z`: the top-side event is already available at any centre.

### 11.4 How A3b-2 and A3b-3 use it

* **§9.4's fence connection (A3b-2, item 5).** It needs, for each arm `i` with end `b i`: a vertex
  `x` of the arm joined to the fence's first end `l` inside `Icc (b i - M) (b i + M)` (given), the
  fence itself as a crossing of the box on the side of `b i` (given, with the side equation), and that
  a point `e` of `∂B_R(z)` within sup-distance `M` of `b i` lands strictly between the neighbours of
  `i`. Given: neighbours land at least `4 √η N` from `L i` (separation) and `L i` is at least
  `4 √η N` from every corner, i.e. `2 √η N` in perimeter units, so `e` is on the same side as `b i`
  (`M ≤ √η N < 2 √η N`) and lands within `2M + 1` (doubled) of `L i`, strictly less than `4 √η N`
  once `√η N > 1/2`. **A3b-2 should take `N₀' = max N₀ ⌈1/√η⌉ + 1`** (the statements hold for all
  `N ≥ N₀`); `N₀` is not exposed as `≥ 1/η`. The rest of §9.4 is as written there: the connection
  can leave `B_R(z)`; the sector lemma `sbtw_landingPos_iff_of_innerPos_eq` applies to `γ k` followed
  by the connection back to its last entry point.
* **Corridors (A3b-2, item 5).** The fence of an end on the top side is a left-right crossing of
  `[b₀ - K, b₀ + K] × [z₁ + R, z₁ + R + M]`; a corridor of width `< 2K` going up from `b` and longer
  than `M` is crossed by it (the top case; the other sides by the side's box). The ends are
  `≥ 8 √η N` apart in landing positions across sides and `≥ 4 √η N` on a side, so the corridors of
  width `2K ≤ 2 η N ≤ 2 √η N` fit. Conditioning: `SEPARATED` is not monotone; "Harris for a mixed
  order" (item 4) is still needed for the gluing, as recorded in §3.3.
* **Theorem 11 (A3b-3, item 6), outer half.** The event form is what the scale iteration needs:
  `G_k` at scales `R_k = 2N_k + 1` are determined by the annuli `B_{2R_k}(z) \ B_{N_k}(z)`, which are
  pairwise disjoint when `N_k ≥ 4 N_{k+1} + 3` (e.g. `N_{k+1} = ⌊N_k / 8⌋`), so the events
  `G_k` (and the arm event inside the smallest box) are jointly independent
  (`prodBernoulli_biInter_of_determined`). The usual argument (the arms are separated at the first
  good scale from outside; failing at `k` scales costs `δ^k`; extending separated arms outwards by
  the gluing costs a factor per scale) is A3b-3's; the inner half needs strips near `∂B_r(z)`
  (arms crossing outwards), a different geometry, which the read-back lemmas of item 1 can transport
  once the inner strip event is stated (one side, then the three symmetries).

### 11.5 Proposal: a definition for the separated event

`SEPARATED` is about 40 lines. It is written twice in `OuterSeparation.lean` (once with the arms as
an existential, once negated inside the set-builder) and its fence clause once more inside the proof
(`hnew`). A3b-2 (input of the gluing) and A3b-3 (Theorem 11: outer and inner separation, the scale
iteration) will restate it in at least four more statements, with the inner variant (fences inside the
annulus) beside it. **Proposal (the user's call; not done):** a definition, e.g.
`separatedArmEvent σ z r R η N : Set (Config (LatticeSite 2))` with its API (membership lemma,
monotonicity in `η`… only where true, measurability), in `Arms/Defs.lean` through a small interface
PR. The user decided "inline" on 2026-11-22; this package kept it inline. **Done on the user's word
of 2026-11-23, in a new file instead of `Arms/Defs.lean`: §12.**

### 11.6 Errata and observations

* No new errata in the source. The draft constants of §9.3 were conservative (inner radius
  `N - 2`, `r + 3 ≤ N`); `N` and `r < N` suffice.
* Lemma 15 as stated has no upper bound on `η`; for the independence one needs `⌊√η N⌋ ≤ N`, hence
  §11.3 item 3.

### 11.7 Search

* Mathlib: `Set.Finite.prod`, `Set.Finite.image`, `Set.Finite.subset`, `Set.sym2` and
  `Set.mem_sym2_iff_subset` (no finiteness lemma for `Set.sym2` found; added
  `finite_setOf_forall_mem`), `Sym2.mem_map`, `Sym2.map_map`, `Sym2.out_fst_mem`,
  `Finite.exists_equiv_fin`, `Equiv.symm_apply_apply`, `RelIso.apply_symm_apply`,
  `RelIso.symm_comp_self`, `RelIso.self_comp_symm`, `prob_compl_eq_one_sub`, `Nat.floor_le_of_le`,
  `Real.sqrt_le_one`, `ENNReal.mul_div_le`, `SimpleGraph.Walk.mem_support_iff`,
  `end_mem_tail_support`, `adj_snd`, `adj_penultimate`, `support_map`, `edges_map`, `support_copy`,
  `edges_copy`, `mem_support_append_iff`, `List.map_dropLast`, `List.dropLast_subset`,
  `dite_eq_left`, `ite_eq_left`, `ite_eq_right`.
* PercLib: `exists_law_separable_ge_aux`, `exists_law_separable_ge_arm`, `dualConfig_image_swap`,
  `dualConfig_image_reflect`, `dualEdge_map_swap`, `dualEdge_map_reflect`, `map_swap_mem_edgeSet_iff`,
  `map_reflect_mem_edgeSet_iff`, `map_swap_map_swap`, `map_reflect_map_reflect`, `exists_iso_swap`,
  `exists_iso_reflect_one`, `CrossingBounds.swap`, `CrossingBounds.reflect`, `law_comp_sym2Map_apply`,
  `localConn_of_image`, `mem_image_sym2Map_iff`, `image_sym2Map_refl`,
  `inter_mem_localConn_iff_of_inter_eq`, `dualConfig_inter_eq_of_inter_eq`,
  `mem_image_dualEdge_of_mem_edges` (bottom-top only; generalised to every orientation as
  `mem_image_dualEdge_of_forall_mem_edges`), `le_of_mem_map_add_one_dualEdge`, `exists_ne_of_mem_edges`,
  `IsCrossing.exists_append_eq_isCrossing_of_subset`, `IsCrossing.append_of_append` (needs the second
  crossing to start in `S`; added `IsCrossing.append_right`), `innerPos_append`, `landingPos_true`,
  `landingPos_false`, `IsArm.not_nil`, `ArmsDisjoint.of_innerPos_eq`, `sbtw_landingPos_of_innerPos_eq`,
  `mem_multiArmEventTo_iff_of_inter_eq`, `multiArmEvent_subset_of_le`,
  `prodBernoulli_inter_of_determined`, `measurableSet_of_determined_finite`. Not found (added):
  Lemma 15 on the other sides, determination of its event, connections through automorphisms of `ℤ²`,
  finiteness of the pairs inside a finite set, determination through a bijection, replacing the end of
  a crossing or of an arm, landing positions side by side, the side of the landing.

### 11.8 Lessons

* `Sym2.mk` is curried in this mathlib: `fun p : V × V => Sym2.mk p` is ill-typed and showed up only as
  a confusing `Set.Finite ?m` mismatch; write `s(p.1, p.2)`.
* `cases σ i` fails (motive not type correct) as soon as a hypothesis or the goal contains a walk whose
  type depends on `σ i` (walks mapped by a colour-dependent map); prove `cond c A B → c = true → A`
  and `(c = true → A) → (c = false → B) → cond c A B` locally and use them instead.
* `first | (exfalso; omega) | exact …` works; an alternative `exact absurd h (by norm_num)` does not
  (the nested `by` is elaborated after `first` commits, leaving "unsolved goals").
* Give `(z := z) (zf := …)` explicitly when equations proved by `rfl` could unify the wrong variables.
* Deprecated here: `dif_pos` (use `dite_eq_left`), `mem_diff`, `diff_subset` (`mem_sdiff`,
  `sdiff_subset`), `cond_true`, `cond_false` (`Bool.cond_true`, `Bool.cond_false`).
* The large set-builder events were generated from one template, so the four sides, the determination
  lemma and the side steps match by definitional unfolding (`![a, b] 1 ≡ b`, `let` bodies). Module
  builds: `SeparationSides` about 10 s, `OuterSeparation` about 15 s.

## 12. The separated event (definition)

On the user's decision of 2026-11-23 ("Yes, new Defs file"), the separated event of the outer step
(§11.2's inline `SEPARATED`) is now a definition, in the new module
`PercLib/Models/Planar/Arms/Separation/Defs.lean` (596 lines: 3 definitions, 16 theorems, 2
examples), which imports only `Arms/Defs.lean`. `Arms/Defs.lean` and `Planar/Defs.lean` (open
interface PRs #11 and #12) are unchanged. Commits:

* `2332e20` **move** (no new mathematics): `dualConfig_inter_eq_of_inter_eq` moves from
  `Arms/QuasiMultiplicativity.lean` (A3a, proof file) to the new module, which needs it for the
  determination lemma; same name and statement; its proof uses `dualEdgeEquiv.right_inv` instead of
  `dualEdge_map_add_one_dualEdge` (a proof file); `QuasiMultiplicativity.lean` imports the new module.
* `4b8801a` **interface**: the three definitions and their API (below), two non-vacuity examples.
* `d125d04` **proof-only**: `OuterSeparation.lean` restated with the definitions (below).
* this note's commit (docs only).

Gate: `scripts/gate.sh main` **passed on `d125d04`** (axiom audit 10199 constants; the expected
interface NOTICE, no other notice; 5.8 min). This note's commit changes only `docs/`.

### 12.1 Design

Three levels, so that a single arm's fence, a family's separation and the event can each be named
in later statements:

```lean
def HasOuterFence (ω : Config (LatticeSite 2)) (c : Bool) (z : LatticeSite 2) (R M K : ℕ)
    {a b : LatticeSite 2} (γ : (zdGraph 2).Walk a b) : Prop :=
  ∃ x ∈ γ.support, ∃ u v : LatticeSite 2,
    cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
      (Icc (b - (M : LatticeSite 2)) (b + (M : LatticeSite 2))) x u ∧
    ((b 1 = z 1 + R ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
        cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
          (Icc ![b 0 - K, b 1] ![b 0 + K, b 1 + M]) u v) ∨
      (b 0 = z 0 + R ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧ … (Icc ![b 0, b 1 - K] ![b 0 + M, b 1 + K]) u v) ∨
      (b 1 = z 1 - R - cond c 0 1 ∧ u 0 = b 0 - K ∧ v 0 = b 0 + K ∧
        … (Icc ![b 0 - K, b 1 - M] ![b 0 + K, b 1]) u v) ∨
      (b 0 = z 0 - R - cond c 0 1 ∧ u 1 = b 1 - K ∧ v 1 = b 1 + K ∧
        … (Icc ![b 0 - M, b 1 - K] ![b 0, b 1 + K]) u v))

def ArmsOuterSeparated (ω : Config (LatticeSite 2)) {j : ℕ} (σ : Fin j → Bool)
    (z : LatticeSite 2) (R : ℕ) (s : ℝ) (M K : ℕ) {a b : Fin j → LatticeSite 2}
    (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)) : Prop :=
  (∀ i k, i ≠ k → s ≤ |((landingPos (z - R) (z + R) (σ i) (γ i) -
      landingPos (z - R) (z + R) (σ k) (γ k) : ℤ) : ℝ)|) ∧
    (∀ i (m : ℕ), s ≤ |((landingPos (z - R) (z + R) (σ i) (γ i) - 4 * m * R : ℤ) : ℝ)|) ∧
    ∀ i, HasOuterFence ω (σ i) z R M K (γ i)

def outerSeparatedArmEvent {j : ℕ} (σ : Fin j → Bool) (z : LatticeSite 2) (r R : ℕ) (s : ℝ)
    (M K : ℕ) : Set (Config (LatticeSite 2)) :=
  {ω | ∃ (a b : Fin j → LatticeSite 2) (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
    (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
    (∀ i k l, i < k → k < l → sbtw (landingPos …) (landingPos …) (landingPos …)) ∧
    ArmsOuterSeparated ω σ z R s M K γ}
```

(`…` in the fence: the same `cond c ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn` as in the
first case.)

* **Parameters `s : ℝ`, `M K : ℕ`, not `η` and `N`.** Nolin's outer step uses `s = 4 √η N`,
  `M = ⌊√η N⌋`, `K = ⌊η N⌋` (`R = 2N + 1`). Taking the derived quantities keeps square roots and
  integer parts out of the definition, gives monotonicity in `s` and `M`, and lets the same notion
  serve other scales (the gluing may want other fence sizes; Theorem 11's scale iteration uses
  several `N`). `s` is real because Nolin's separation is real; positions are integers cast to `ℝ`.
* **Equal to the inline event by `Iff.rfl`.** At `s = 4 * Real.sqrt η * N`,
  `M = ⌊Real.sqrt η * N⌋₊`, `K = ⌊η * N⌋₊`, the event unfolds to exactly §11.2's `SEPARATED` (same
  conjunctions, same casts, same bound structure). Checked with a standalone file (`lake env lean`)
  whose `example : (inline SEPARATED, copied from the statement) ↔ ω ∈ outerSeparatedArmEvent … :=
  Iff.rfl` elaborates. `mem_outerSeparatedArmEvent_iff` is the same equality, written out, as an API
  lemma.
* **The outer step, restated** (`d125d04`): `exists_separating_event` concludes
  `∀ r < N, ∀ ω ∈ multiArmEvent σ z r R ∩ G, ω ∈ outerSeparatedArmEvent σ z r R (4 * Real.sqrt η * N)
  ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊`, and `exists_law_multiArmEvent_inter_not_separated_le` bounds
  `law q (multiArmEvent σ z r R \ outerSeparatedArmEvent σ z r R (4 * Real.sqrt η * N) ⌊Real.sqrt η * N⌋₊ ⌊η * N⌋₊)`.
  Hypotheses and quantifiers unchanged. A second standalone file proves each **old** statement text,
  copied from the file before the refactor, by the **new** theorem applied to its arguments: the
  statements are definitionally equal, nothing weakened. Inside the proof, the step `hnew` now states
  each new arm's fence with `HasOuterFence`. The file shrank from 2087 to 2009 lines.
* **The fence is a connection inside its box between its two ends**, not a crossing in the strict
  sense (it may meet the end columns elsewhere), exactly as the inline clause had it; that is what the
  gluing uses (§11.4).
* **Centred boxes only.** The corner clause `4 m R` assumes the square box `B_R(z)`; non-centred outer
  boxes (§5 item 7) would need the corners of `Icc lo hi`, which have no uniform formula. Nolin's
  separated events are centred.

### 12.2 API (all in `Arms/Separation/Defs.lean`)

* Membership: `mem_outerSeparatedArmEvent_iff` (`Iff.rfl`, written out in full).
* `outerSeparatedArmEvent_subset_multiArmEvent`: separated arms are arms.
* Monotonicity, only where true: `HasOuterFence.mono` (depth `M ≤ M'`: the fence box and the box
  about the end only grow), `ArmsOuterSeparated.mono` and `outerSeparatedArmEvent_mono` (`s' ≤ s`,
  `M ≤ M'`). **Not monotone in `K`**: the fence must run exactly between the columns `b₀ ∓ K` (top
  side), and the first end of a fence of a wider box need not be joined to the arm inside the box of
  radius `M` about `b`.
* Trivial case: `outerSeparatedArmEvent_fin_zero` (`@[simp]`, `j = 0`: the event is `univ`).
* Measurability: `measurableSet_setOf_hasOuterFence`, `measurableSet_outerSeparatedArmEvent`
  (countable unions over walks, `measurableSet_localConn`, `measurable_dualConfig`).
* Determination: `cond_inter_edgeSet_mem_localConn_iff_of_inter_eq` (a connection of colour `c` inside
  `Icc lo hi` is determined by the pairs in any `T ⊇ Icc lo (hi + 1)`), `hasOuterFence_iff_of_inter_eq`
  (a fence at `b` is determined by `T ⊇ Icc (b - (M + K)) (b + (M + K + 1))`),
  `mem_outerSeparatedArmEvent_iff_of_inter_eq` (for `r < R`, the event is determined by
  `T ⊇ B_{R + M + K + 1}(z)`; for `r ≥ R` arms of length zero can sit anywhere in `B_r(z)`), with the
  helper `IsArm.end_mem_Icc` (an arm from a box inside the interior of `Icc lo hi` ends in
  `Icc (lo - 1) hi`) and the moved `dualConfig_inter_eq_of_inter_eq`.
* Translation: `HasOuterFence.map_add`, `image_add_mem_outerSeparatedArmEvent`,
  `image_add_mem_outerSeparatedArmEvent_iff` (`Sym2.map (· + c) '' ω` at `z + c` iff `ω` at `z`).
* Non-vacuity (two `example`s): with every edge open, the open arm from `0` to `(1, 0)` is separated
  for `s = 2`, `M = K = 1` (landing position `6`, corners `4`, `8`; fence from `(1, -1)` to `(1, 1)` in
  `[1, 2] × [-1, 1]`); the empty configuration is not in that event.

Not included (not needed now, and each would be a guess): colour inversion, rotations, an `_of_agree`
form (the `_of_inter_eq` form is what `prodBernoulli_inter_of_determined` takes).

### 12.3 How A3b-2 and A3b-3 use it

* **A3b-2 (gluing, §5 items 4–5).** The input is `ω ∈ outerSeparatedArmEvent σ z r R (4√ηN) M K` with
  `M = ⌊√η N⌋₊`, `K = ⌊η N⌋₊`, i.e. arms `γ` with `ArmsOuterSeparated ω σ z R (4√ηN) M K γ`; per-arm
  lemmas (the fence connection of §9.4, the corridor crossing of §11.4) take `HasOuterFence ω c z R M K γ`
  as a hypothesis instead of the 20-line clause. Measurability and determination by
  `B_{R + M + K + 1}(z)` are available for the conditioning; "Harris for a mixed order" is still to be
  proved in `Probability/` (§3.3).
* **A3b-3 (Theorem 11).** The scale iteration uses `exists_separating_event` at scales `N_k` (event
  form, §11.4) with `outerSeparatedArmEvent` at each scale; `outerSeparatedArmEvent_mono` compares
  separations. Separation at both ends of one family is
  `∃ a b γ, arms ∧ ArmsDisjoint σ γ ∧ order ∧ ArmsOuterSeparated ω σ z R s M K γ ∧ ArmsInnerSeparated …`
  once the inner predicate exists (§12.4); about five lines, so it can be stated inline or added as a
  definition beside the others.

### 12.4 The inner variant: intended shape, not defined

The inner variant (arms separated at `∂B_r(z)`, fences inside `B_r(z)` at the first vertex or face
`a` of each arm, separation of `innerPos`) is **not defined in this package**. Its intended shape, the
mirror of the outer one:

```lean
HasInnerFence ω c z r M K γ :=   -- γ : Walk a b
  ∃ x ∈ γ.support, ∃ u v, G ∩ E ∈ localConn (Icc (a - M) (a + M)) x u ∧
    ((a 1 = z 1 + r ∧ u 0 = a 0 - K ∧ v 0 = a 0 + K ∧ G ∩ E ∈ localConn (Icc ![a 0 - K, a 1 - M] ![a 0 + K, a 1]) u v) ∨
     (a 0 = z 0 + r ∧ u 1 = a 1 - K ∧ v 1 = a 1 + K ∧ … (Icc ![a 0 - M, a 1 - K] ![a 0, a 1 + K]) u v) ∨
     (a 1 = z 1 - r - cond c 0 1 ∧ u 0 = a 0 - K ∧ v 0 = a 0 + K ∧ … (Icc ![a 0 - K, a 1] ![a 0 + K, a 1 + M]) u v) ∨
     (a 0 = z 0 - r - cond c 0 1 ∧ u 1 = a 1 - K ∧ v 1 = a 1 + K ∧ … (Icc ![a 0, a 1 - K] ![a 0 + M, a 1 + K]) u v))
ArmsInnerSeparated ω σ z r s M K γ :=
  (∀ i k, i ≠ k → s ≤ |innerPos z r (σ i) (γ i) - innerPos z r (σ k) (γ k)|) ∧
  (∀ i (m : ℕ), s ≤ |innerPos z r (σ i) (γ i) - m * (4 * r + 2)|) ∧ ∀ i, HasInnerFence ω (σ i) z r M K (γ i)
```

(`G = cond c ω (dualConfig ω)`, `E` the edges of `ℤ²`; `innerPos` lives on the doubled box
`2z ± (2r + 1)`, of perimeter `16 r + 8` with corners at the multiples of `4 r + 2`.) **Why not now:**
a half-unit choice that only A3b-3's inner strip lemma can settle. A dual arm starts at a face *outside*
`B_r(z)` touching it (top side: face row `z₁ + r`), while reflecting Lemma 15's arm box through the top
side of `B_r(z)` (vertex rows `y ↦ 2(z₁ + r) - y`, hence face rows `f₁ ↦ 2(z₁ + r) - 1 - f₁`) puts the end face of a
rerouted dual crossing one row *inside* (`z₁ + r - 1`). Either the dual fence box is anchored one row
in, or the reversed crossing is extended by one face; this is the kind of half-unit mismatch that
blocked A3b-1 (§9.2). The three-level design makes the inner predicates an **addition** beside the
outer ones (a small additive interface change in the same file, nothing outer changes); defining them
now would fix the half-unit before it is proved. Design question for the user (§12.5).

### 12.5 For the interface PR

To be stacked after #12 (it imports only `Arms/Defs.lean`); it would contain
`PercLib/Models/Planar/Arms/Separation/Defs.lean` and its line in `PercLib.lean`. The deletion of
`dualConfig_inter_eq_of_inter_eq` from `QuasiMultiplicativity.lean` (`2332e20`) belongs to that proof
file's own PR, since `QuasiMultiplicativity.lean` is not upstream. Declarations: the definitions
`HasOuterFence`, `ArmsOuterSeparated`, `outerSeparatedArmEvent`; the theorems
`dualConfig_inter_eq_of_inter_eq`, `cond_inter_edgeSet_mem_localConn_iff_of_inter_eq`,
`IsArm.end_mem_Icc`, `mem_outerSeparatedArmEvent_iff`, `outerSeparatedArmEvent_subset_multiArmEvent`,
`outerSeparatedArmEvent_fin_zero`, `HasOuterFence.mono`, `ArmsOuterSeparated.mono`,
`outerSeparatedArmEvent_mono`, `measurableSet_setOf_hasOuterFence`,
`measurableSet_outerSeparatedArmEvent`, `hasOuterFence_iff_of_inter_eq`,
`mem_outerSeparatedArmEvent_iff_of_inter_eq`, `HasOuterFence.map_add`,
`image_add_mem_outerSeparatedArmEvent`, `image_add_mem_outerSeparatedArmEvent_iff`; two examples. No
tag, no `…Input`. Questions a reviewer will ask:

1. Right notion? A fence is a connection between the two ends inside its box, not a strict crossing;
   separation is real (`s : ℝ`) on integer positions; corners only for the centred box.
2. Duplicates? None found (search below); the inline event of `OuterSeparation.lean` is replaced.
3. Placement of three general lemmas: `dualConfig_inter_eq_of_inter_eq` belongs in `Planar/Defs.lean`,
   `IsArm.end_mem_Icc` and `cond_inter_edgeSet_mem_localConn_iff_of_inter_eq` in `Arms/Defs.lean`; both
   files are frozen under #11/#12, so they sit here and can move after those merge.
4. Names: `HasOuterFence`, `ArmsOuterSeparated`, `outerSeparatedArmEvent` (outer, leaving room for the
   inner and two-sided versions); `outerSeparatedArmEvent_fin_zero` for the case `j = 0`.
5. Missing API: no monotonicity in `K` (false), no `_of_agree` form, no colour inversion or rotation.

### 12.6 Search

* PercLib, for an existing notion: `rg -i "separated|fence"` over `PercLib/`: only the inline event and
  the per-side lemmas of `OuterSeparation.lean`, and Lemma 15's strip events (`SeparationLemma.lean`,
  `SeparationSides.lean`, a different, per-strip notion). No definition to reuse.
* PercLib, API used: `inter_mem_localConn_iff_of_inter_eq`, `localConn_mono_set`,
  `measurableSet_localConn`, `measurable_dualConfig`, `measurableSet_setOf_isArm`, `IsArm.of_agree`,
  `IsArm.map_add`, `landingPos_map_add`, `ArmsDisjoint.map`, `armsDisjoint_of_subsingleton`,
  `image_add_neg_image_add`, `image_add_inter_edgeSet_mem_localConn_iff`, `dualConfig_image_add`,
  `IsOpenArm.end_mem_boxBoundary`, `IsDualArm.end_mem_boxBoundary`, `IsOpenArm.not_nil`,
  `IsDualArm.not_nil`, `boxBoundary_subset_Icc`, `edgeSet_mem_localConn_Icc`, `isOpenArm_toWalk_iff`,
  `landingPos_true`, `perimeterPos_of_right`, `empty_notMem_multiArmEventTo`, `mem_multiArmEvent_iff`,
  `mem_Icc_two_iff`, `mem_Icc_of_mem_dualEdge`, `mem_dualConfig_iff`, `dualEdgeEquiv`. Found in proof
  files and not imported (so that the module needs no proof file): `dualConfig_inter_eq_of_inter_eq`
  (moved), `dualEdge_map_add_one_dualEdge` (replaced by `dualEdgeEquiv.right_inv`),
  `Icc_subset_Icc_add_one_sub_one`, `IsArm.end_mem_sides`, `IsArm.penultimate_mem` (two-line facts,
  proved inline). `measurableSet_of_determined_finite` (`CrossEdge.lean`) not needed.
* Mathlib: `Set.image_add_right`, `Set.Icc_subset_Icc`, `Set.Icc_subset_Icc_left`,
  `Fin.forall_fin_two`, `Fin.elim0`, `Measurable.exists`, `Measurable.forall`, `Measurable.and`,
  `Measurable.or`, `measurableSet_setOfPred`, `SimpleGraph.Walk.support_injective`,
  `SimpleGraph.Walk.support_map`, `SimpleGraph.Walk.end_mem_support`, `List.mem_map_of_mem`, `le_abs`,
  `Bool.cond_true`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`.

### 12.7 Lessons

* `awk 'length > 100'` counts bytes on macOS; Unicode-heavy Lean lines look too long. Count characters
  (Python) or trust the `longLine` linter.
* `Matrix.cons_val_one` turns `![a, b] 1` into `![b] 0`; add `Matrix.cons_val_zero`.
* `fun_prop` does not see through `cond true ω (dualConfig ω)` after `cases c`; give the function
  explicitly (`(by fun_prop : Measurable fun ω => ω ∩ E)`), `exact` accepts it up to defeq.
* `simp` rewrites `![1, 0] - ↑1` by `Matrix.cons_sub` into `vecHead`/`vecTail` of the constant vector;
  add `Matrix.vecHead`, `Matrix.vecTail` to the simp set.
* Anonymous constructors and `rcases` see through `Set` membership and through `Prop` definitions, so
  the old proofs closed the new statements unchanged (only `hnew` was shortened).
* Statement equivalence is cheap to check: a standalone file importing the module, with the old
  statement text and the new theorem as its proof, `lake env lean` (about 1.5–2 min, mostly loading).
* The new module's builds: about 15 s; the move rebuilt `QuasiMultiplicativity`, `SeparationSides`,
  `HalfPlaneExponents`, `OuterSeparation` in 87 s.

## 13. A3b-2 (2026-11-23): Harris for a mixed order; the gluing, first part

Package A3b-2 = items 4 and 5 of §5. **Item 4 is done. Item 5 is half done**: everything in the gluing
that does not depend on the shape of the corridors is proved (conditioning on the separated event,
the fence-connection argument of §9.4, the gluing of continuations into arms of a larger box); the
corridors themselves, the bins for the ends and the probability assembly (the gluing *statement*,
§13.5) are not. Proof-only, no new definition, no `Defs.lean` touched. Commits:

* `8aef63a` **Probability/MixedHarris** (general, not planar; new module, 213 lines, 7 theorems).
* `b31db79` **Arms/OuterGluing** (planar, proof-only; new module, 862 lines, 22 theorems).
* this note's commit (docs only).

Gate: passed on `b31db79` (§13.8).

### 13.1 Item 4: Harris for a mixed order (`PercLib/Probability/MixedHarris.lean`)

Arbitrary index type `ι`, arbitrary profile `p`, an arbitrary set `D` of coordinates; "upper for the
mixed order" is the hypothesis `∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A` (increasing
off `D`, decreasing on `D`).

```lean
theorem prodBernoulli_map_symmDiff (p : ι → unitInterval) (D : Set ι) [DecidablePred (· ∈ D)] :
    (prodBernoulli p).map (· ∆ D) =
      prodBernoulli (fun i => if i ∈ D then unitInterval.symm (p i) else p i)

theorem prodBernoulli_harris_of_mixed (p : ι → unitInterval) (D : Set ι) {A B : Set (Set ι)}
    (hA : upper for the mixed order) (hB : …) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    prodBernoulli p A * prodBernoulli p B ≤ prodBernoulli p (A ∩ B)

theorem prodBernoulli_prod_le_biInter_of_mixed (p) (D) (s : Finset κ) {A : κ → Set (Set ι)}
    (hA : ∀ k ∈ s, upper for the mixed order) (hAm : ∀ k ∈ s, MeasurableSet (A k)) :
    ∏ k ∈ s, prodBernoulli p (A k) ≤ prodBernoulli p (⋂ k ∈ s, A k)

/-- conditional form -/
theorem prodBernoulli_mul_le_inter_of_mixed_of_determined (p : ι → unitInterval)
    {T D : Set ι} {A B : Set (Set ι)}
    (hA : ∀ ω ω', ω \ T = ω' \ T → ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ A → ω' ∈ A)
    (hB : ∀ ω ω', ω \ D ⊆ ω' \ D → ω' ∩ D ⊆ ω ∩ D → ω ∈ B → ω' ∈ B)
    (hBT : ∀ ω ω', ω ∩ T = ω' ∩ T → (ω ∈ B ↔ ω' ∈ B))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    prodBernoulli p A * prodBernoulli p B ≤ prodBernoulli p (A ∩ B)
```

plus `prodBernoulli_eq_map_symmDiff`, `isUpperSet_preimage_symmDiff`, `mixed_inter`. Proof: flipping
the coordinates of `D` (`ω ↦ ω ∆ D`) maps the law to the law with the profile flipped on `D`
(`Measure.infinitePi_map_pi`, as in `prodBernoulli_map_compl`) and turns the mixed order into
inclusion, so `prodBernoulli_harris` applies; the conditional form conditions on the coordinates
outside `T` by splicing (`prodBernoulli_eq_lintegral_splice`, `LocallyMonotone.lean`) and applies
the mixed form to the sections. **It generalises Nolin's Lemma 13**
(`prodBernoulli_mul_mul_le_inter_of_determined`): there `A = Ainc ∩ Adec` with determination
hypotheses; here `A` is any event whose sections at fixed coordinates outside `T` are upper for the
mixed order, which is what the separated event satisfies (it is a union over witnesses, not an
intersection of an increasing and a decreasing event). No percolation-facing corollary was needed:
the planar file applies the conditional form with `T` = the pairs read by the corridors and
`D` = those read by the dual corridors (a dual crossing is decreasing in `ω`, `dualConfig_anti`).

### 13.2 Item 5, first part (`PercLib/Models/Planar/Arms/OuterGluing.lean`)

**Conditioning on the separated event.** With `E_B` the separated event whose arms end in given sets
`B i` (written out as a set-builder: arms, `ArmsDisjoint`, order, `ArmsOuterSeparated ω σ z R s M K γ`,
`∀ i, b i ∈ B i`):

```lean
theorem law_mul_le_law_inter_of_mixed (q) (hKM : K ≤ M) {B : Fin j → Set (LatticeSite 2)}
    {T D : Set (Sym2 (LatticeSite 2))}
    (hT : ∀ e ∈ T, ∀ v ∈ e, v ∉ Icc (z - R + 1) (z + R - 1))
    (hTB : ∀ i, ∀ b ∈ B i, ∀ e ∈ T, (∀ v ∈ e, v ∈ Icc (b - M) (b + (M + 1))) →
      (e ∈ D ↔ σ i = false))
    {C} (hCm : MeasurableSet C) (hC : C upper for the mixed order of D)
    (hCT : C determined by T) :
    law q E_B * law q C ≤ law q (E_B ∩ C)
```

from `mem_of_mixed_of_forall_mem` (the same witness serves for `ω'`: open arms use only edges with an
end in the interior, which are not in `T`; a dual arm crosses such edges except at its last dual edge,
whose edge has its ends in `Icc b (b + 1)` and so lies in `D` when it lies in `T`
(`IsDualArm.exists_mem_or_forall_mem_Icc`); fences are determined by the box of radius `M + 1` and grow
in their colour, `HasOuterFence.of_cond_subset`) and `measurableSet_setOf_separated_forall_mem`.

**The fence-connection argument (§9.4), as proved.** `notMem_support_of_mem_Icc`: for a pack-free
ordered disjoint family with integer separation `2M < |L i - L k|`, `2M < |L i - 4mR|` and
`r + M + 1 < R`, a walk `P` of the colour of arm `i`, from a vertex (face) `x` of arm `i` in
`Icc (b i - M) (b i + M)`, whose points in `Icc (z - R - 1) (z + R)` lie in `Icc (b i - M) (b i + M)`,
misses every other arm `k` of that colour. Proof as in §9.4, with one simplification: the walk
`γ k` up to the meeting point `v`, then `P` backwards to `x`, then `γ i` from `x` to its end, is cut at
its first exit from the interior of `B_R(z)`; the exit point is `v` (if it lies on the part of `γ k`),
a point of `P` in `Icc (z - R - 1) (z + R)`, or `b i`, so in all cases within `M` of `b i`; the cut walk
is an arm with the inner position of `γ k` (`innerPos_append`) landing within `2M` of `L i`
(`abs_landingPos_sub_le`, which needs `M < R` and the corner bound), and
`false_of_innerPos_eq_of_abs_lt` (the sector lemma with the next arms after `i` and after `k`)
gives the contradiction. "Last entry point" (§9.4) is not needed.

**The gluing, for continuations of any shape.**

```lean
theorem exists_isArm_of_glue (hσ) {M R' : ℕ} (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R')
    (hγ : arms to ∂B_R(z)) (hd) (ho) (hsep : 2M < |L i - L k|) (hcor : 2M < |L i - 4mR|)
    (P : ∀ i, (zdGraph 2).Walk (x i) (y i)) (hx : ∀ i, x i ∈ (γ i).support)
    (hxM : ∀ i, x i ∈ Icc (b i - M) (b i + M))
    (hP : ∀ i, ∀ e ∈ (P i).edges, e ∈ cond (σ i) ω (dualConfig ω))
    (hloc : ∀ i, ∀ v ∈ (P i).support, v ∈ Icc (z - R - 1) (z + R) → v ∈ Icc (b i - M) (b i + M))
    (hy : ∀ i, y i ∉ cond (σ i) (Icc (z - R' + 1) (z + R' - 1)) (Icc (z - R') (z + R' - 1)))
    (hdisj : ∀ i k, i ≠ k → σ i = σ k → ∀ v ∈ (P i).support, v ∉ (P k).support) :
    ∃ b' γ', (∀ i, IsArm ω (σ i) z r (z - R') (z + R') (γ' i)) ∧ ArmsDisjoint σ γ' ∧ order ∧
      (∀ i, innerPos z r (σ i) (γ' i) = innerPos z r (σ i) (γ i)) ∧ ∀ i, b' i ∈ (P i).support
```

(`γ' i` = `γ i` up to `x i`, then `P i`, cut at the first exit from the interior of `B_{R'}(z)`; order
by order invariance at both boxes.) Also: `two_mul_le_abs_landingPos_sub` (pack-free: two arms of one
colour land at least `2S` apart when any two land at least `S` apart: an arm of the other colour lies
between them on each arc), `IsArm.landingPos_cases`, `isArm_iff_cond`, `IsArm.mem_Icc_of_mem_support`,
the sharp fence determination `hasOuterFence_iff_of_inter_eq_of_le` (`K ≤ M`, box of radius `M + 1`),
two walk helpers (`IsCrossing.eq_of_mem_support_left`, `mem_support_tail_append_of_mem_right`).

### 13.3 Deviations and decisions (mine, recorded per the standing instruction)

1. **Item 5 split.** The gluing statement (§13.5) is not proved; this package proves its
   shape-independent core. Reason: size. The remaining part is coordinates (bins, four sides, two
   colours, corridor probabilities), no new mathematics, except the rotation to fixed windows (§13.4).
2. **Fence determination sharpened** to the box `Icc (b - M) (b + (M + 1))` for `K ≤ M`
   (`hasOuterFence_iff_of_inter_eq` has radius `M + K + 1`): with tips `2M` apart and `K` comparable to
   `M`, the old box would contain the neighbouring corridors. `K ≤ M` holds in the outer step
   (`⌊ηN⌋ ≤ ⌊√ηN⌋` for `η ≤ 1`).
3. **Integer separation hypotheses** (`2M < |L i - L k|`, `2M < |L i - 4mR|`) in the deterministic
   lemmas; `ArmsOuterSeparated` with `2M < s` gives them (positions are integers).
4. Hypotheses `r + M + 1 < R` (the fence boxes miss `B_r(z)`) and `R + 2 ≤ R'`.
5. No definition. The separated event with ends in bins is a set-builder inside the statements.

### 13.4 Errata and observations

* **Off by one in the separation.** With `s = 4√ηN` and `M = ⌊√ηN⌋`, two *adjacent* arms (different
  colours) can end exactly `2M` apart on a side, so their fence boxes `Icc (b ± M)` can share a column.
  Only the boxes of arms of one colour must be disjoint, and those arms are at least `2s ≥ 8M` apart
  (`two_mul_le_abs_landingPos_sub`): pack-freeness is used a second time here, not only in the barrier.
* **The rotation.** Theorem 11's windows are fixed while the ends of the separated arms are anywhere
  on `∂B_R(z)` (in cyclic order). Straight radial corridors keep each arm near the radial projection of
  its end; reaching fixed windows needs corridors that turn round the annulus. The "radial, ring at
  level `h_i`, radial" design with nested levels **fails for large rotations**: two arms at angles
  `0, 1/2` (turns) going to windows at `0.9, 1.4` (both rotate by `0.9`) force `h₁ < h₀` (arc `0`
  passes over the start of arm `1`) and `h₀ < h₁` (arc `1` passes over the start of arm `0` one turn
  later). Proposed: rotate in stages, each moving every arm by less than half the smallest gap
  (linear interpolation of the lifted angles of ends and windows, both increasing along the cyclic
  order with span `< 1`; `O(1/η)` stages), all arcs at one level per stage; each stage is the straight
  gluing plus one ring arc. Alternatively (Nolin's own route) Theorem 11 is proved by extending arms
  that already land in windows, scale by scale, and only the first step needs any rotation (§13.6).

### 13.5 What remains of item 5 (package "A3b-2b")

The gluing statement, straight corridors first:

```lean
theorem exists_pos_le_law_multiArmEvent_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q L, CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K : ℕ)
      (s : ℝ), 1 ≤ W → W ≤ K → K ≤ M → W + 3 ≤ M → 4 * M ≤ s → r + M + 1 < R → R + 2 ≤ R' →
      R' ≤ D * R → R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q (outerSeparatedArmEvent σ z r R s M K) ≤ law q (multiArmEvent σ z r R')
```

(Nolin's outer step gives `s = 4√ηN`, `M = ⌊√ηN⌋`, `K = ⌊ηN⌋`, `R = 2N + 1`; take
`W = min K ⌊M/4⌋`, `A ≍ 1/η`, `N ≥ N₀'(η)`.) Design, checked on paper in this session:

* **Bins.** Side `t ∈ Fin 4` of the end and index `n` with the coordinate along the side in
  `[base + nW, base + nW + W - 1]` (`base = z₀ - R` for top/bottom, `z₁ - R` for left/right); at most
  `4 (2R/W + 3)` bins per arm. `P(sep) ≤ Σ_β P(E_β)` over bin configurations `β`; for each `β` with
  `E_β ≠ ∅` a witness gives the geometry below.
* **Corridor of a bin** = the bin's columns (rows) times the band between the boxes: top
  `[base + nW, base + nW + W - 1] × [z₁ + R, z₁ + R']`, right `[z₀ + R, z₀ + R'] × […]`, bottom
  `[…] × [z₁ - R' - 1, z₁ - R - [dual]]`, left `[z₀ - R' - 1, z₀ - R - [dual]] × […]`; event: a crossing
  of colour `σ i` between the two long sides (`crossing 1` / `crossing 0`, `dualConfig ⁻¹'` for dual
  arms). Read regions: the box (open) or the box enlarged by one at its upper corner (dual); they have
  no end in the interior of `B_R(z)` (`hT`), are pairwise disjoint and avoid the boxes of radius `M + 1`
  about the ends in other bins (`hTB`): ends of different arms are `≥ 2M` apart along a side
  (`s ≥ 4M`), corridors are `W` wide, `W + 3 ≤ M`; ends are `> M` from the corners, so corridors of
  different sides lie in disjoint quadrant strips.
* **Hook.** The fence of a top end `b` crosses `[b₀ - K, b₀ + K] × [b₁, b₁ + M]` from left to right; the
  corridor's crossing walk, cut at its first visit to row `b₁ + M`, crosses the same box from bottom to
  top inside the bin's columns `⊆ [b₀ - K, b₀ + K]` (`W ≤ K`); `exists_mem_support_of_crossing_walks`
  (`Gluing.lean`, needs `1 ≤ M`) gives a common vertex (face) `p`. Continuation
  `P i = (connection x → u) ++ (fence u → p) ++ (corridor walk p → far end)`; `hloc` holds since the
  corridor meets `Icc (z - R - 1) (z + R)` only in its near row, inside the fence's columns; `hdisj`
  from the disjoint read regions and the disjoint boxes of same-colour ends (`2s ≥ 8M` apart).
  Other sides: same lemma with the walks' roles swapped (left/right) or reversed (bottom/left).
* **Probability.** Corridor crossings: `CrossingBounds.le_law_crossing_one_of_le` and the three others
  (`MultiArmBounds.lean`) with aspect `⌈(R' - R)/W⌉ ≤ D A`, so `P(C_β) ≥ c(DA)^j` by independence
  (`prodBernoulli_iInter_fin_of_determined`, disjoint read regions); `law_mul_le_law_inter_of_mixed`;
  `E_β ∩ C_β ⊆ multiArmEvent σ z r R'` by `exists_isArm_of_glue`; so
  `c(DA)^j · P(sep) ≤ #bins^j · P(A(r, R'))`.
* **Windows** (for Theorem 11): the staged rotation of §13.4, or the landing information
  `b' i ∈ (P i).support` of `exists_isArm_of_glue` with corridors ending in the windows.

Rough size: 1000–1500 lines, one session for the straight statement, a second for windows.

### 13.6 How A3b-3 uses items 4 and 5

* **Extendability, outer half** (`law (A r R) ≤ C law (A r (2R))`): outer step at scale `R`
  (`exists_law_multiArmEvent_inter_not_separated_le`: `P(A(r,R)) ≤ P(sep_R) + δ P(A(r,N))`) and the
  straight gluing `P(sep_R) ≤ C(η) P(A(r, R'))`; the remaining `δ`-term is handled by the scale
  iteration below.
* **Theorem 11, outer half, by scale iteration** (§11.4): `G_k` at scales `R_k` with disjoint annuli;
  "first good scale from outside" costs `δ^k`; then extend the separated arms from `R_k` to `R`. For the
  constants to close (`δ` is chosen after the per-scale cost), the per-scale extension must not depend
  on `η`: glue once (cost `c(η)`) into arms that land in fixed windows *with fences* at the next scale,
  then extend window-to-window at a cost depending only on the landing data. So A3b-3 will want the
  gluing with **fences at `∂B_{R'}`** in its output: add to the corridor event a fence event at the far
  end (a crossing of `[c - W - K', c + W + K'] × [z₁ + R' + 1, z₁ + R' + M']` beyond the corridor, a
  crossing just inside, `[c - W - 1, c + W + 1] × [z₁ + R' - M', z₁ + R' - 1]`, and a short crossing
  joining them along the corridor), giving `HasOuterFence` at the new end with `K_new = K'`,
  `M_new = M' + 2W + K'`. Planned for A3b-2b or early in A3b-3.
* **Quasi-multiplicativity, lower half**: separation at both ends (outer step for the inner event,
  inner step — the inner predicates of §12.4 — for the outer event), Theorem 11 to put both into the
  same windows, gluing in `B_{r₂} \ B_{r₂/4}` (corridors from window `i` to window `i`), and the
  one-scale bound when `r₂ ≤ 8 r₁`. Conditioning on two separated events at once: the conditional
  Harris form applies to their intersection (both sections are upper for the mixed order off the
  corridors).
* **A priori lower bound**: the one-scale bound and the gluing at dyadic scales.

### 13.7 Search

* Mathlib: `Combinatorics/SetFamily/HarrisKleitman.lean` and `FourFunctions.lean` (finite set
  families / finite distributive lattices, counting measure; no product measure, no mixed order),
  `Measure.infinitePi_map_pi`, `map_bernoulliMeasure`, `Measurable.symmDiff`, `Measurable.of_eval`,
  `lintegral_mul_const'`, `Int.sbtw_iff`, `sbtw_asymm`, `sbtw_cyclic_left`, `abs_cases`, `lt_abs`,
  `abs_le`, walk API (`take_spec`, `tail_support_append`, `support_append_eq_support_dropLast_append`,
  `mem_support_append_iff`, `edges_append`, `edges_reverse`, `support_reverse`, `getLast_support`,
  `end_mem_tail_support`, `mem_support_iff`, `dart_snd_mem_support_of_mem_darts`).
* PercLib, reused: `prodBernoulli_harris`, `prodBernoulli_map_compl` (full flip; the partial flip is
  new), `bernoulliMeasure_swap`, `prodBernoulli_eq_lintegral_splice`, `splice_preimage_eq_of_disjoint`,
  `measurable_splice_right`, `prodBernoulli_mul_mul_le_inter_of_determined` (Lemma 13; generalised, not
  duplicated), `localConn_mono`, `dualConfig_anti`, `hasOuterFence_iff_of_inter_eq`,
  `cond_inter_edgeSet_mem_localConn_iff_of_inter_eq`, `measurableSet_setOf_isArm`,
  `measurableSet_setOf_hasOuterFence`, `IsArm.end_mem_Icc`, `IsArm.landingPos_eq_of_top/right/bottom/
  left`, `IsArm.end_mem_sides`, `IsArm.penultimate_mem`, `Icc_subset_Icc_add_one_sub_one`,
  `sbtw_landingPos_iff_of_innerPos_eq`, `sbtw_apply_finRotate_apply`,
  `sbtw_innerPos_iff_sbtw_landingPos`, `innerPos_append`, `exists_append_eq_of_notMem`,
  `armsDisjoint_of_subsingleton`, `IsOpenArm/IsDualArm.mem_Icc`, `exists_mem_edgeSet_of_mem_edges`,
  `mem_Icc_of_mem_dualEdge`. Not found (added): Harris for a mixed order and its conditional form, the
  flip of a set of coordinates, the monotonicity of fences in their colour, the sharp fence
  determination, the sector bound beyond the boundary, the gluing of continuations. `ArmsDisjoint.of_innerPos_eq`
  contains a `key` step close to `false_of_innerPos_eq_of_abs_lt` but it is internal to that proof.

### 13.8 Gate and lessons

Gate: `scripts/gate.sh main` **passed on `b31db79`** (axiom audit 10319 constants, only `propext`,
`Classical.choice`, `Quot.sound`; the expected interface NOTICE from `Arms/Defs.lean`, no other notice;
about 8 min). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on b31db79739d8c42c00b24274f488258daf44cd16
```

This note's commit changes only `docs/`.

Lessons:
* `lake build … | tail -1 && git commit …` commits even when the build fails (the pipeline's status is
  `tail`'s); check for `Build completed` first. (Happened once here; the commit was amended locally
  before anything else.)
* `rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩` drops the sign facts; `omega` then reports counterexamples
  from impossible branches. Keep both conjuncts.
* `namespace SimpleGraph.Walk` inside `namespace PercLib.Models.Planar` nests; state general walk
  lemmas as `theorem _root_.SimpleGraph.Walk.…` with `open SimpleGraph.Walk` in a section.
* The ascription `(r : LatticeSite 2)` in `Icc (z - r) (z + r)` is unnecessary (same term); dropping it
  fixed most long lines.
* Comparing landing positions near a side needs `IsArm.penultimate_mem`: without it `omega` considers
  the diagonal corner faces, which no dual arm can end at.
* Builds: `MixedHarris` 7 s, `OuterGluing` about 15 s.

## 14. A3b-2b (2026-11-24): the gluing statement, straight corridors

Package A3b-2b = the rest of item 5 of §5 as designed in §13.5. **The gluing statement is proved for
straight corridors**, with inner windows carried along, on top of a gluing lemma for *arbitrary*
corridor events that later corridor shapes reuse. **Not proved:** landing in prescribed windows
(staged rotation) and fences at `∂B_{R'}` (§14.4 gives the design; package "A3b-2c"). Proof-only,
no definition, no `Defs.lean` touched. Commits:

* `d9837d7` **Arms/CorridorGluing** (new module, 1870 lines, 43 theorems) and a proof-only refactor
  of `Arms/OuterGluing.lean` (`mem_of_mixed_of_forall_mem` split into the per-family lemma
  `separated_of_mixed_of_forall_mem`; the old statement is unchanged and is now a corollary).
* this note's commit (docs only).

Gate: §14.8.

### 14.1 The statements proved

**The gluing statement** (inner windows `J`; the plain form follows with `J = univ`):

```lean
theorem exists_pos_le_law_multiArmEventIn_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R R' W M K : ℕ) (s : ℝ)
      (J : Fin j → Set ℤ), 1 ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → 4 * (M : ℝ) ≤ s →
      r + M + 1 < R → R + M ≤ R' → R' ≤ D * R → R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q {ω | ∃ a b γ, (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
        (counterclockwise order at ∂B_R(z)) ∧ ArmsOuterSeparated ω σ z R s M K γ ∧
        ∀ i, innerPos z r (σ i) (γ i) ∈ J i} ≤
      law q (multiArmEventIn σ z r R' J fun _ => univ)

theorem exists_pos_le_law_multiArmEvent_of_separated … :   -- same hypotheses, no J
      c₀ * law q (outerSeparatedArmEvent σ z r R s M K) ≤ law q (multiArmEvent σ z r R')
```

with `c₀ = c (D A) ^ j / (4 (2A + 1)) ^ j` (and `c₀ = 1` when `c (D A) = 0`, a vacuous case).

**The gluing through given corridors** (the reusable core):

```lean
theorem law_mul_prod_le_law_of_corridors (q) (hσ) {R'} (hKM : K ≤ M) (hM : 1 ≤ M)
    (hrM : r + M + 1 < R) (hRR' : R + 2 ≤ R') (hs : 4 * (M : ℝ) ≤ s)
    (B : Fin j → Set (LatticeSite 2)) (J : Fin j → Set ℤ) (C : Fin j → Set (Config _))
    (T : Fin j → Set (Sym2 _)) (Q : Fin j → Set (LatticeSite 2))
    (Φ : Fin j → Config _ → LatticeSite 2 → Prop)
    (hCm : C i measurable) (hCT : C i determined by T i)
    (hCmono : cond (σ i) ω ω' ⊆ cond (σ i) ω' ω → ω ∈ C i → ω' ∈ C i)   -- monotone in the colour
    (hTT : open and dual corridors read disjoint pairs)
    (hT : no corridor reads a pair with an end in the interior of B_R(z))
    (hTB : σ i ≠ σ k → b ∈ B i → no pair of T k lies in Icc (b - M) (b + (M + 1)))
    (hQloc : b ∈ B i → Q i ∩ Icc (z - R - 1) (z + R) ⊆ Icc (b - M) (b + M))
    (hQdisj : for every separated family with ends in the bins, the regions
       Icc (b i - M) (b i + M) ∪ Q i of two arms of one colour are disjoint)
    (hhook : ω ∈ C i → γ an arm of colour σ i ending at b ∈ B i with an outer fence →
       ∃ x y (P : Walk x y), x ∈ γ.support, x within M of b, P of colour σ i,
       P.support ⊆ Icc (b - M) (b + M) ∪ Q i, y outside the interior of B_{R'}(z),
       Φ i ω v for every point v of P outside that interior) :
    law q (separated, ends in B, inner positions in J) * ∏ i, law q (C i) ≤
      law q {ω | ∃ a b' γ', arms to ∂B_{R'}(z), disjoint, ordered, inner positions in J,
        ∀ i, Φ i ω (b' i)}
```

Its proof: `D` = the pairs read by dual corridors; each `C i` is upper for the mixed order of `D`
(`mixed_of_determined_of_increasing/decreasing`), so Harris for the mixed order gives
`∏ P(C i) ≤ P(⋂ C i)`; the conditional form (`law_mul_le_law_inter_of_mixed_of_innerPos`, the inner-window
version of A3b-2's conditioning) gives `P(E) P(⋂ C i) ≤ P(E ∩ ⋂ C i)`; on `E ∩ ⋂ C i` the hooks give
the continuations and `exists_isArm_of_glue` the new arms, whose ends lie on the continuations and
outside the interior, hence satisfy `Φ`. Everything about the shape of the corridors is in the
hypotheses; `Φ` is where landing windows and fences at the new boundary will enter (§14.4).

**Straight corridors.** A side of `B_R(z)` is described by a four-case disjunction `hside` (top, right,
bottom, left): the bin `B` is the set of ends on that side with coordinate along the side in
`[x, x + W]`, at least `2M` from the corners (dual arms on the bottom and left sides one row/column
further out, `cond col 0 1`), and the corridor is `Icc lo hi`, of width `W`, from the bin straight
out to `∂B_{R'}(z)`, crossed in direction `dir` in the configuration of the colour of the arm. Proved:

* `exists_walk_of_corridor_top/right/bottom/left` and `exists_walk_of_side`: the hook. The fence of
  an arm ending at `b` (length `2K ≥ 2W`, depth `M`) and the corridor's crossing walk meet by
  `exists_mem_support_of_mem_Icc_of_mem_Icc` (`SeparationFence.lean`: a walk in rows `[y₀, y₁]` from
  a column `≤ x₀` to a column `≥ x₁` meets a walk in columns `[x₀, x₁]` from a row `≤ y₀` to a row
  `≥ y₁`); no cutting of walks is needed. Bottom and left sides use the reversed crossing.
* `CrossingBounds.le_law_of_side`: `c κ ≤ P(corridor)` for `R' ≤ κ W`, from A1b's
  `le_law_crossing_*_of_le` (`le_law_preimage_cond_crossing_one/zero`, either colour).
* `measurableSet_preimage_cond_crossing`, `preimage_cond_crossing_iff_of_inter_eq` (determined by
  `Icc lo (hi + cond col 0 1)`), `cond_mem_crossing_of_cond_subset`.
* `sideP_of_side`, `IsArm.sideL_of_side` (end coordinates and landing position of an arm ending in
  a bin, as integer facts), `notMem_Icc_of_side`, `mem_Icc_of_side`.
* The integer geometry, split by sides (each a separate declaration, §14.7):
  `false_of_corridor_of_corridor` (open and dual corridors read disjoint pairs),
  `false_of_box_of_corridor` (+ `_top/_right/_bottom/_left`: corridors avoid the end boxes of the
  other colour), `false_of_region_of_region` (+ four sides: regions of one colour are disjoint).
* `pow_mul_law_le_law_multiArmEventIn_of_sides`: the gluing for fixed bins
  (`c κ ^ j · P(E_bins) ≤ P(multiArmEventIn σ z r R' J univ)`); it uses a witness of `E_bins` for
  the conditions on fixed sets (`hTT`, `hTB`: if `E_bins = ∅` there is nothing to prove) and the
  witness of `ω` itself for `hQdisj`.
* `exists_lt_le_le`, `IsArm.exists_mem_bin` (every end of a separated arm lies in one of `2A + 1`
  bins of width `W` on its side), `side_of_bin` (the bin and its corridor satisfy `hside`), and the
  union bound over the `(4 (2A + 1)) ^ j` bin configurations.

**Arms of one colour and the corners** (`exists_lt_lt_of_eq`, `le_or_le_of_lt_of_lt`,
`le_or_le_of_lt`): without packs, between two arms of one colour there is an arm of the other colour
on each arc; so two arms of one colour landing on both sides of a corner `C` are not both within
`2S` of `C`. This is the third use of pack-freeness (after the barrier and
`two_mul_le_abs_landingPos_sub`), see §14.3.

### 14.2 Decisions (mine, per the standing instruction)

1. **Hypotheses.** `1 ≤ W ≤ K ≤ M`, `2W + 2 ≤ M`, `4M ≤ s`, `r + M + 1 < R`, `R + M ≤ R' ≤ D R`,
   `R ≤ A W`, `R' ≤ L`. Deviations from the draft of §13.5: `W + 3 ≤ M` is replaced by
   `2W + 2 ≤ M` (the draft's condition is too weak, §14.3) and `R + 2 ≤ R'` by `R + M ≤ R'` (the
   corridor must reach the depth `M` of the fence for the hook). For Nolin's parameters
   (`s = 4√ηN`, `M = ⌊√ηN⌋`, `K = ⌊ηN⌋`, `R = 2N + 1`) take `W = min K ⌊(M - 2) / 2⌋`, which is
   `≥ 1` once `ηN ≥ 1` and `√ηN ≥ 4`, and `A ≍ 1/η` (`R ≤ A W`).
2. **Constants.** Aspect ratio `κ = D A` (`R' ≤ D R ≤ D A W`), `2A + 1` bins per side,
   `c₀ = c (D A) ^ j / (4 (2A + 1)) ^ j`. `c₀` is chosen before `q`, `L`, `z` and the radii.
3. **Inner windows `J` are carried** (the conditioning keeps the witness, `exists_isArm_of_glue` keeps
   the inner positions). Theorem 11's inner half needs to extend arms outwards without losing their
   inner windows.
4. **Bins** are given by a side and an interval of `W + 1` coordinates (step `W + 1`), with the
   corner distance `2M` built in; the colour shifts the bottom and left sides. Corridors have width
   `W` (`W + 1` columns) so the fence of length `2K ≥ 2W` always covers them.
5. **Read sets** `Icc lo (hi + cond col 0 1)`: the box for an open corridor, the box enlarged by one at
   its upper corner for a dual one (`cond_inter_edgeSet_mem_localConn_iff_of_inter_eq`). For the open
   bottom/left corridors the enlarged box would reach into the interior of `B_R(z)`.
6. **Generality.** The gluing lemma takes arbitrary corridor events, regions and an arbitrary end
   property `Φ`, so the remaining corridor shapes (§14.4) only have to supply events, hooks and
   geometry. The mixed-order lemmas for determined monotone events
   (`mixed_of_determined_of_increasing/decreasing`) are general (any index type) but live in the planar
   file; they can move to `Probability/MixedHarris.lean` in a later proof-only commit.
7. **No definition.** Bins, corridors and the separated event with ends in bins are written out
   (set-builders and the `hside` disjunction).

### 14.3 Errata and observations

* **The draft's `W + 3 ≤ M` is not enough for this proof.** Two adjacent arms (different colours)
  on one side can end `2M` apart in lattice units (landing positions `4M` apart, one of them dual).
  The box of radius `M + 1` about a point `b` of the first bin (`b` up to `W` from the first end) and
  the read set of the second corridor (up to `W` from the second end, one more column for a dual
  corridor) are disjoint, as the conditioning needs (`hTB`), only if `2M - 2W > M + 1`, i.e.
  `M ≥ 2W + 2`. Example with `W = 4`, `M = 7` (so `W + 3 ≤ M`): top side, open arm ending at
  column `0` with bin `[0, 4]`, dual arm ending at column `14` with bin `[10, 14]` (landing positions
  `29 ≥ 4M` apart); the box about `b = 4` covers columns `[-4, 12]`, the dual corridor reads columns
  `[10, 15]`. The statement itself is not affected; only the margin between bins and boxes.
* **Arms of one colour at a corner (`s = 4M` exactly).** `two_mul_le_abs_landingPos_sub` gives two
  arms of one colour `8M` apart in landing positions; near a common corner this allows both to be
  exactly `2M` (lattice) from the corner, and then the boxes of radius `M` about their ends share the
  corner point `(z₀ + R - M, z₁ + R - M)`. The configuration is impossible: the arm of the other
  colour between them (on the arc through the corner) must be `4M` from both and from the corner.
  `le_or_le_of_lt_of_lt` makes this precise: one of the two is `8M` (doubled) from the corner. With
  `4M < s` the simpler argument would do, but the outer step gives `s = 4√ηN ≥ 4⌊√ηN⌋` with equality
  possible.
* **Corner faces need `M ≥ 1`**: an end of a separated arm is at least `2M` from the corners, but a
  dual arm may end at the corner face (`b₀ = z₀ - R - 1` on the top side) when `M = 0`.
* **Ends of separated arms determine their side**: they are at least `2M ≥ 2` from the corners, so
  exactly one clause of `HasOuterFence` and of `IsArm.landingPos_cases` applies.

### 14.4 What remains of item 5 (package "A3b-2c"): windows and fences at `∂B_{R'}`

Both are instances of `law_mul_prod_le_law_of_corridors` with new corridor events and a new `Φ`; the
conditioning, the gluing of continuations and the union bound over bins are done.

**(a) Landing in fixed windows.** `Φ i ω v := v` lies where an arm ending at `v` lands in
`window (16 R') θ η i`. For an open arm the landing position is `2 · perimeterPos (z - R') (z + R') v`;
for a dual arm it is determined by `v` and its side up to the neighbouring face, so the corridor must
end at least one unit inside the window (`IsArm.landingPos_cases` at `R'`). The corridors turn:

* **Junctions.** An L-shaped junction of a vertical rectangle `[x₀, x₁] × [y, Y]` and a horizontal
  rectangle `[X, X'] × [y₀, y₁]` with `[y₀, y₁] ⊆ [y, Y]`, `[x₀, x₁] ⊆ [X, X']` is
  `exists_mem_support_of_mem_Icc_of_mem_Icc` again (the vertical crossing's walk is a "bottom-top" walk
  of the junction square, the horizontal one a "left-right" walk); a chain of walks with consecutive
  common vertices gives one walk (`exists_walk_of_mem_support_of_mem_support` repeatedly). Turning
  corridors are chains of rectangles alternating in direction; the corridor event is the intersection
  of their crossings (all of one colour, so Harris inside a corridor is the mixed Harris already used).
* **Staged rotation** (§13.4): lift the landing positions of the bins and the window centres to
  increasing sequences with span `< 1` turn; stage `k` of `S` moves every arm by
  `(θ_i - α_i)/S`, less than half the smallest gap, inside the annulus band `[ρ_{k-1}, ρ_k]`:
  radial leg, arc along the middle of the band (at most one corner, since a move is shorter than a
  side), radial leg. Arcs of one stage are disjoint because each stays within half a gap of its
  start. `S` and the band widths depend on `j`, `A` (the bin gap) and `θ`, `η`; the probability is
  `c(κ')^{(number of rectangles)}` per arm.
* **Scaling corridors** for window-to-window steps (`R → 2R`, same `θ`): on one side, vertical leg,
  horizontal leg from column `t` to column `2t` (relative to `z₀`), vertical leg; arms farther from the
  middle of the side turn at lower levels (nested levels by `|t|`). No corner is passed when the windows
  are `≥ ηR` from the corners. This is the case A3b-3 iterates; it needs no rotation.
* **Geometry** as here: one four-case description per rectangle and integer lemmas split by sides; the
  cross-arm conditions for a stage involve only arms whose arcs lie on adjacent sides.

**(b) Fences at `∂B_{R'}`** (§13.6, checked on paper in this session for the top side). Corridor of a
bin ending at columns `[x, x + W]`:
`V` = bottom-top crossing of `[x, x + W] × [z₁ + R, z₁ + R' - 1]` (stays inside `B_{R'}`),
`Hc` = left-right crossing of `[x, x + W] × [z₁ + R' - M', z₁ + R' - 1]` (connector),
`U` = bottom-top crossing of `[x, x + W] × [z₁ + R' - M', z₁ + R' + M']` (cap),
`H` = left-right crossing of `[x - K', x + W + K'] × [z₁ + R' + 1, z₁ + R' + M']` (new fence).
`V`, `U` both cross `Hc`'s box bottom to top inside its columns, so `V ∪ Hc ∪ U` is connected; the
continuation is `P = (old hook) ++ V ++ Hc ++ U` up to `U`'s first point on the row `z₁ + R'`, which is
the new end `b'` (every earlier point of `P` is inside `B_{R'}`). `Φ i ω b'` := there are `u, v` with a
connection `b' → u` inside `Icc (b' - M') (b' + M')` (along `U` from `b'` to its meeting point with
`H`, then along `H`) and a fence `u → v` in `[b'₀ - K', b'₀ + K'] × [b'₁, b'₁ + M']`: the sub-walk of
`H` between its last visit to column `b'₀ - K'` and its first visit to column `b'₀ + K'`
(`SimpleGraph.Walk.exists_walk_mem_Icc`). Hence `HasOuterFence ω (σ i) z R' M' K' (γ' i)` with
`x := b'`, for `W ≤ K' ≤ M'`. Together with landing windows of size `η R'` at least `η R'` apart and
from the corners this is `outerSeparatedArmEvent σ z r R' s' M' K'` with `s' ≍ η R'`, `M', K' ≍ η R'`
small enough that neighbouring caps and fences miss each other (`4M' ≤ s'` again).

### 14.5 How A3b-3 consumes the statements

* **Theorem 11, outer half** (scale iteration of §11.4/§13.6): needs (G1) the first gluing
  `c(η) P(sep_η at R) ≤ P(arms at 2R in windows θ with fences)` — rotation (a) + fences (b) — and (G2)
  the window-to-window step `c₀(θ) P(windows θ with fences at R) ≤ P(windows θ with fences at 2R)` —
  scaling corridors (a) + fences (b), cost independent of `η`, so `δ` can be chosen after `c₀(θ)`.
  Both are `law_mul_prod_le_law_of_corridors` with the corridors of §14.4 and the bins of this package
  (G2's input is separated with `s ≍ ηR`, so its bins are those of `IsArm.exists_mem_bin` with
  `A ≍ 1/η_θ`). The straight statement proved here is the special case without windows and fences;
  it also gives directly `P(sep at R) ≤ c₀⁻¹ P(A(r, R'))` for every `R' ∈ [R + M, D R]`.
* **Inner half of Theorem 11**: the outer gluing keeps inner positions (`J`), so arms first put into
  inner windows (inner separation and an inner gluing, which needs the inner predicates of §12.4 and
  mirrored hooks) are then extended outwards with `J = window (16 r + 8) θ' η`.
* **Extendability** `π(r, R) ≤ C π(r, 2R)`: Theorem 11 (arms in windows with fences at `R`) and one
  window-to-window gluing (G2). `π(2r, R) ≤ C π(r, R)`: the inner analogue.
* **Quasi-multiplicativity, lower half**: Theorem 11 at both ends of `r₂`, then corridors from window
  `i` of the inner family to window `i` of the outer family in `B_{r₂} \ B_{r₂/4}` (scaling corridors);
  the conditioning on two separated events uses the conditional mixed Harris on their intersection
  (both sections are upper for the mixed order off the corridors), so the gluing lemma needs a
  two-sided variant (inner fences of the outer family as a second hook) — about the size of
  `law_mul_prod_le_law_of_corridors`.
* **A priori lower bound** `π(r, R) ≥ c (r/R)^C`: the one-scale bound (A3a) at scale `r`, then (G2)
  at the `log₂(R/r)` dyadic scales: `c₀(θ)^{log₂(R/r)} = (r/R)^{log₂(1/c₀)}`.

### 14.6 Search

* Mathlib: `Int.ediv_mul_le`, `Int.lt_ediv_add_one_mul_self`, `Int.ediv_lt_of_lt_mul`,
  `Int.ediv_nonneg`, `Int.toNat_of_nonneg`, `add_one_mul`, `Finset.pow_card_le_prod`,
  `measure_iUnion_fintype_le`, `Finset.sum_le_sum`, `Finset.sum_const`, `Fintype.card_fun`,
  `Fintype.card_prod`, `ENNReal.div_pos`, `ENNReal.inv_mul_cancel`, `mul_le_mul_left` (the former
  `mul_le_mul_right'`), `mul_le_mul'`, `mul_right_comm`, `Sym2.out_fst_mem`, `Bool.eq_false_or_eq_true`,
  `Int.sbtw_iff`, `le_abs`, `Int.cast_abs`.
* PercLib, reused: `exists_mem_support_of_mem_Icc_of_mem_Icc` and
  `exists_walk_of_mem_support_of_mem_support` (`SeparationFence.lean`), `exists_walk_of_mem_localConn`
  (`RSWKeyStep.lean`), `mem_crossing_iff_of_inter_eq` (`CriticalProbability.lean`),
  `dualConfig_inter_eq_of_inter_eq`, `measurableSet_crossing`, `measurable_dualConfig`, `crossing_mono`,
  `dualConfig_anti`, `CrossingBounds.le_law_crossing_*_of_le` (`MultiArmBounds.lean`),
  `prodBernoulli_prod_le_biInter_of_mixed`, `prodBernoulli_mul_le_inter_of_mixed_of_determined`,
  `measurableSet_setOf_hasOuterFence`, `measurableSet_setOf_isArm`, `IsArm.landingPos_cases`,
  `IsArm.end_mem_Icc`, `Icc_subset_Icc_add_one_sub_one`, `two_mul_le_abs_landingPos_sub`,
  `exists_isArm_of_glue`, `isArm_iff_cond`, `sbtw_apply_finRotate_apply`.
* Not found (added): the gluing through given corridor events, the mixed order for determined monotone
  events, crossings of either colour as one event (`(fun ω => cond col ω (dualConfig ω)) ⁻¹' crossing`),
  the corner lemma for arms of one colour, bins, the hooks.

### 14.7 Lessons

* **Heartbeats are per declaration** and `maxHeartbeats` cannot be raised (forbidden option): a proof
  with about twelve `omega` calls on four-case disjunctions of ten-fact conjunctions exhausts 200000.
  Split by side into sublemmas; the dispatcher discharges mismatched cases after `clear`ing the big
  hypotheses. State the side data over `ℤ` so that `omega` sees only linear facts.
* `set` local definitions are unfolded during `omega`'s atom collection (timeouts at `whnf`/`isDefEq`);
  `obtain ⟨x, hx⟩ : ∃ x, x = … := ⟨_, rfl⟩` keeps them opaque. (For a family of set-builders indexed
  by bin configurations `obtain` left metavariables; `set` was fine there, no `omega` involved.)
* `omega` with a goal that is a disjunction of long conjunctions negates it into a product of
  disjunctions; give each disjunct the shape `(facts) ∧ (landing formula)` and pick it with
  `exact Or.inl ⟨h₁, h₂⟩` after matching the cases.
* `simp only [Matrix.cons_val_zero, Matrix.cons_val_one]` turns `x = x` into `True`: use `trivial`.
* `n < 2 * A + 1 ∧ (P ∨ Q)` needs the parentheses; `zero_le` has no explicit argument here;
  `mul_le_mul_right` is ambiguous in context, `mul_le_mul' le_rfl h` is not.
* The four-sided statements were generated from Python templates with a line wrapper; the wrapper must
  not split a `simp … at h₁ h₂` location list (parse error), and docstrings were reflowed separately.
* Build: `CorridorGluing` about 16 s.

### 14.8 Gate

`scripts/gate.sh main` **passed on `d9837d7`** (axiom audit 10570 constants, only `propext`,
`Classical.choice`, `Quot.sound`; the expected interface NOTICE from `Arms/Defs.lean`, no other
notice; about 5 min). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on d9837d77768099b4eaa5131d815432ccfb7cff60
```

This note's commit changes only `docs/`.

## 15. A3b-2c (2026-11-24): jogs with caps, fences at the new boundary, window-to-window steps

Package A3b-2c = the rest of item 5 of §5 as designed in §14.4. **Proved:** fences at `∂B_{R'}`
(the caps `H_c`, `U`, `H_f` of §14.4(b)) for corridors that move each arm along its side by a given
shift (jogs), on all four sides and both colours; on top of them **the first gluing with fences at
the new boundary for straight corridors** (output `outerSeparatedArmEvent` at `R'` with new, much
smaller fences) and **the window-to-window step** (arms in windows on the sides of `B_R` to arms in
shifted windows on the same sides of `B_{R'}`, separation read off the windows, constant independent
of the separation scale of the first gluing). **Not proved:** the rotation into fixed windows (the
first gluing *into windows*, §14.4(a) "staged rotation"), which needs corridors turning round the
corners of the annulus and a motion plan; and the two-sided gluing for the lower half of
quasi-multiplicativity. Both are designed in §15.4. Proof-only, no definition, no `Defs.lean`
touched. Commits:

* `3f79aee` **Arms/JogCorridors** (new module, 2630 lines) and **Arms/CapGluing** (new module, first
  part): jogs with caps on the four sides, corridor events of six crossings, the gluing inside
  straight boxes, jogs with caps for fixed bins.
* `f1a09be` **Arms/CapGluing**: the first gluing with fences at `∂B_{R'}` (straight).
* `d1b2f16` **Arms/CapGluing**: the window-to-window step (module now 1444 lines).
* `e15749d` **Arms/CapGluing**: a hypothesis renamed (`hκdef` → `hκeq`, §15.8).
* this note's commit (docs only).

Gate: §15.8.

### 15.1 The statements proved

**Jogs with caps** (`JogCorridors.lean`). On the top side (the other three sides are the same
statement reflected or with the coordinates exchanged, `δ = cond col 0 1` shifting the rows (columns)
of a dual arm on the bottom (left) side): an arm `γ` of colour `col` ending at `b` on the top side of
`B_R(z)` in the bin columns `[x, x + W]`, at least `2M` from the corners, with an outer fence `(M, K)`,
`W ≤ K ≤ M`; the six boxes

```
V₁  = [x + K', x + W - K'] × [z₁ + R, z₁ + h + W₀]        (bottom-top; W₀ = W - 2K')
H   = [xl + K', xr + W - K'] × [z₁ + h, z₁ + h + W₀]      (left-right; xl ≤ x, x + d ≤ xr …)
V₂  = [x + d + K', x + d + W - K'] × [z₁ + h, z₁ + R' - 1]
H_c = [x + d + K', x + d + W - K'] × [z₁ + R' - M', z₁ + R' - 1]
U   = [x + d + K', x + d + W - K'] × [z₁ + R' - M', z₁ + R' + M']
H_f = [x + d, x + d + W] × [z₁ + R' + 1, z₁ + R' + M']
```

crossed in the configuration of the colour of the arm give (`exists_walk_of_jog_top`) a walk of that
colour from a vertex (face) of `γ` within `M` of `b`, through the box of radius `M` about `b`, `V₁`
and the region `[xl, xr + W] × [z₁ + h, z₁ + R' + M']`, to the **first point `y` outside the interior
of `B_{R'}(z)`**; `y` lies on the top side, `x + d + K' ≤ y₀ ≤ x + d + W - K'`, every other point of
the walk is inside, and `HasOuterFence ω col z R' M' K' (nil y)` (a fence of length `2K'` and depth
`M'` at `y`), for `2K' + 1 ≤ W`, `2 ≤ M'`, `W ≤ M' + K'`, `R + M ≤ h`, `h + W₀ + M' ≤ R'`. It is the
leg `exists_walk_leg_top` (old fence → `V₁` → `H` → `V₂`) followed by the cap `exists_walk_cap_top`
(`V₂` → `H_c` → `U`, cut at the first exit; the part of `U` after `y` meets `H_f`, and the sub-walk of
`H_f` between columns `y₀ ∓ K'` is the new fence, `exists_mem_localConn_of_walk_zero`). The cap takes
its three boxes as variables with coordinate equations, so it is reusable by other legs (turns).

**One arm's corridor** (`exists_corridor_jog`, any side through a four-case description `hjog`):
the six crossings form an event `C` that is measurable, determined by the pairs inside
`Icc lo (hi + cond col 0 1)` of the straight box `Icc lo hi` from the fat bin (`[x, x + W₀ + 2D]`
along the side) out to distance `R' + M'`, monotone in the colour, with `c κ ^ 6 ≤ P(C)` under the
aspect bounds `R' + M' - R ≤ κ (W₀ - 2K')`, `2D + W₀ - 2K' ≤ κ (W₀ - 2K')`, `W₀ ≤ κ (M' - 1)`; the
bin is `[x + D, x + D + W₀]`, the shift `|d| ≤ D`, the target `[x + D + d + K', x + D + d + W₀ - K']`
on the same side of `B_{R'}`.

**The gluing inside straight boxes** (`law_mul_prod_le_law_of_sides`, `CapGluing.lean`):
`law_mul_prod_le_law_of_corridors` when every corridor reads only pairs inside a straight box of
width `W` from its bin out to distance `R''` and its region lies in that box; the geometric
hypotheses of the corridor gluing (`hTT`, `hTB`, `hQdisj`, `hT`) are discharged by A3b-2b's integer
lemmas used with a **margin `S ≥ M` in place of `M`** (separation `s ≥ 4S`, `2W + 2 ≤ S`, bins `2S`
from the corners): wide boxes need well separated arms, not deep fences.

**Jogs with caps for fixed bins** (`pow_mul_law_le_law_of_jogs`): `c κ ^ (6j) · P(separated at R
with ends in the bins B, inner positions in J) ≤ P(arms to ∂B_{R'}(z), disjoint, ordered, inner
positions in J, ends in the targets B' with outer fences (M', K'))`.

**The first gluing with fences at `∂B_{R'}`** (straight corridors, `D = d = 0`):

```lean
theorem exists_pos_le_law_separated_of_separated {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A D : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q L, CrossingBounds q L c → ∀ z (r R R' W M K M' K' : ℕ) (s : ℝ) J,
      1 ≤ K' → 4 * K' ≤ W → W ≤ K → K ≤ M → 2 * W + 2 ≤ M → W ≤ M' →
      4 * (M : ℝ) ≤ s → r + M + 1 < R → R + M + 1 + W + M' ≤ R' → R' + M' ≤ D * R →
      R ≤ A * W → (R' : ℕ∞) ≤ L →
      c₀ * law q {separated at R, scale s, fences (M, K), inner positions in J} ≤
        law q {separated at R', scale s - 4W, fences (M', K'), inner positions in J}
```

and `exists_pos_le_law_outerSeparatedArmEvent_of_separated` (`J = univ`, with
`outerSeparatedArmEvent`). `c₀ = c κ ^ (6j) / (4 (2A + 1)) ^ j`, `κ = 2DA + 2`. The separation at
`R'` is inherited from a separated family ending in the same bins (`IsArm.shift_of_jog`: the landing
position moves by the growth `(4t + 2)(R' - R)` of the perimeter up to the side `t`, up to `2W`;
sides are ordered as the positions, so distances drop by at most `4W`,
`abs_sub_sub_le_abs_of_shift`, and the distance to the corners by at most `2W`,
`sub_le_abs_sub_of_shift`).

**The window-to-window step**:

```lean
theorem exists_pos_le_law_windows_of_windows {j : ℕ} (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q L, CrossingBounds q L c →
      ∀ z (r R R' W M K M' K' D S : ℕ) (s : ℝ) (g' : ℤ) J (t : Fin j → Fin 4) (α β d : Fin j → ℤ),
      1 ≤ K' → 4 * K' ≤ W → W ≤ K → K ≤ M → M ≤ S → 2 * (W + 2 * D) + 2 ≤ S → W ≤ M' →
      4 * (S : ℝ) ≤ s → r + M + 1 < R → R + M + 1 + W + M' ≤ R' → R' + M' ≤ R + A * W →
      D ≤ A * W → (R' : ℕ∞) ≤ L → (∀ i, -D ≤ d i ∧ d i ≤ D) →
      (∀ i, β i - α i + 1 ≤ N * (W + 1)) →                       -- N bins per window
      (∀ i, windows [α i, β i] at least 2S from the corners of B_R(z) on the side t i) →
      1 ≤ g' →
      (∀ i, windows [α i + d i, β i + d i + W] at least g' from the corners of B_{R'}(z)) →
      (∀ i k, i ≠ k → t i = t k → these windows at least g' apart) →
      c₀ * law q {separated at R, scale s, fences (M, K), b i ∈ window [α i, β i] on side t i, J} ≤
        law q {separated at R', scale 2g' - 1, fences (M', K'),
          b i ∈ window [α i + d i, β i + d i + W] on side t i, J}
```

(window on side `t`: `t = 0`: `b₁ = z₁ + R`, `α ≤ b₀ ≤ β`; `t = 1`: `b₀ = z₀ + R`, `α ≤ b₁ ≤ β`;
`t = 2`: `b₁ = z₁ - R - δ`, `α ≤ b₀ ≤ β`; `t = 3`: `b₀ = z₀ - R - δ`, `α ≤ b₁ ≤ β`.)
`c₀ = c κ ^ (6j) / (N + 1) ^ j`, `κ = 4A + 2`: **it depends only on `σ`, `c`, `A`, `N`**. The
separation `2g' - 1` at `R'` is read off the windows (`le_abs_landingPos_sub_of_windows`: arms ending
in windows at least `g` from the corners and, on one side, `g` apart, land `2g - 1` apart and from
the corners), so iterating the step does not erode it.

### 15.2 Decisions (mine, per the standing instruction)

1. **Caps as in §14.4(b), cut inside the hook.** The continuation is cut at its first exit from the
   interior of `B_{R'}(z)` by the hook itself, so the end property of
   `law_mul_prod_le_law_of_corridors` (`Φ`) has to hold at one point only; the fence at that point is
   `HasOuterFence … (SimpleGraph.Walk.nil : Walk y y)` (`HasOuterFence.of_nil` transfers it to any walk
   ending at `y`). **No new definition.** A single crossing of `[x, x + W] × [z₁ + R, z₁ + R' + M']`
   instead of `V₂, H_c, U` does not work: after first reaching the row `z₁ + R'` the walk may return
   below `z₁ + R' - M'`, so the connection from `y` to the fence would leave the box of radius `M'`.
2. **Window-to-window by small jogs, not nested scaling corridors.** §14.4(a)'s scaling corridors
   (`t ↦ 2t` with levels nested by `|t|`) conflict near the corners: the L-shaped approximations of
   rays from `z` through two ends on adjacent sides near a common corner cross. Instead one step moves
   every arm by a fixed shift `|d i| ≤ D` along its side, with one level `h` for all arms, and every
   corridor stays in a straight box of width `W + 2D` above its bin: the geometry is A3b-2b's, used
   with a separation margin `S ≥ M` (decision 3). A doubling `ρ → 2ρ` is `O(1/ε)` such steps with
   `R' - R ≍ ε ρ`; A3b-3 composes them (§15.5). No corner is passed: windows stay on their sides.
3. **Separation margin `S` separate from the fence depth `M`** in the gluing inside straight boxes
   (and in the bins and windows): the integer lemmas of A3b-2b are instantiated with `S`; boxes of
   radius `M + 1` about the ends lie in those of radius `S + 1`.
4. **Output separation.** The first gluing inherits `s - 4W` from a separated family in the same bins
   (the arms only move by `≤ W` along their sides); the window step reads `2g' - 1` off the windows.
   The first gluing outputs fences `(M', K')` with `M' ≥ W`, `4K' ≤ W` freely chosen: with Nolin's
   `M = ⌊√ηN⌋`, `W ≍ ηN` the output has separation `≈ 4√ηN` and fences `≍ ηN`, i.e. **room**
   (`s' ≫ M'`), which later steps need (the input of the first gluing has `s = 4M` exactly).
5. **Constants.** First gluing: `κ = 2DA + 2` (all six aspect ratios), `c₀ = c κ ^ (6j) / (4(2A+1))^j`.
   Window step: `κ = 4A + 2`, `c₀ = c κ ^ (6j) / (N + 1)^j` (`N + 1` keeps `c₀` finite for `N = 0`).
   Both chosen before `q`, `L`, `z` and the radii.
6. **Level `h ≥ R + M + 1`** (the legs' horizontal piece misses `Icc (z - R - 1) (z + R)`: on the
   bottom side with `M = 1` the level `R + M` would touch the row `z₁ - R - 1`).
7. **Interiors for either colour** through `mem_cond_interior_iff` (open: `Icc (z - R' + 1) (z + R' - 1)`,
   dual: `Icc (z - R') (z + R' - 1)`); the bottom and left caps work in the dual interior.
8. **Windows** are coordinate intervals `[α, β]` on a side `t`, not `window (16R) θ η`: the
   corridors are built from side coordinates; the translation to landing data is A3b-3's (§15.5).
9. Right and left statements are generated from the top and bottom ones by exchanging the
   coordinates (`exists_mem_support_of_mem_Icc_of_mem_Icc_swap`, `exists_mem_localConn_of_walk_one`,
   whose argument names are the exchanged ones). The optional move of A3b-2b's mixed-order lemmas to
   `Probability/MixedHarris.lean` was not done.

### 15.3 Errata and observations

* **Two-arm separation after a shift is false at the corners**: two positions both equal to a
  corner `4tR`, read on the two adjacent sides, move by different amounts. The lemmas use positions
  strictly inside the sides, which holds since ends are `≥ 2S` from the corners.
* The shift of a landing position under a straight move from `R` to `R'` is `(4t + 2)(R' - R)` for
  the side `t` (bottom `0`, right `1`, top `2`, left `3`): positions on later sides move more, so
  distances between arms on different sides only grow.
* The jog's bins must start inside their windows (`α ≤ x + D`) for the target window
  `[α + d, β + d + W]`; a bin straddling `α` would need `[α + d - W, …]`.
* No statement of the plan or of §14 had to change; no hypothesis beyond `hσ` was needed.

### 15.4 What remains of item 5: the rotation (first gluing into windows) and the two-sided gluing

**(a) The first gluing into fixed windows** (§14.5 (G1)): from `separated at R` (scale `s`, after
`exists_pos_le_law_separated_of_separated`: room `s ≫ M'`) to arms ending in prescribed windows
`θ̃` (on the sides, away from the corners) at some `R'' ≤ D(η) R`, cost `c(η, θ̃)`. Design:

* **Turns.** For an arm near the top-right corner moving clockwise: `V₁` up from its bin to the level
  `h`, then `H = [x + K', R' - 1] × [h, h + W₀]` right through the corner square, then the right-side
  cap (`exists_walk_cap_right` with rows `[h, h + W₀]`): the new end is on the right side of
  `B_{R'}`, `R' - h - W₀` below its corner. Eight variants (four corners, two directions) from one by
  reflections; the cap lemmas are already general (boxes as variables).
* **Sectors.** With room, give each arm a sector (a box: the straight box for a jog; for a turn
  `[x - M, R' + M' + 1] × [R - M, h + W₀ + K' + 1]` at the top-right corner), containing its old end
  box, its corridor and its read set; if the sectors are pairwise disjoint, `hTT`, `hTB`, `hQdisj`
  follow without the corner lemma of A3b-2b. New generic lemma `law_mul_prod_le_law_of_sectors`
  (about 150 lines, from `law_mul_prod_le_law_of_corridors`).
* **Motion plan.** Lift the fractional positions of the arms (`φ i`) and of the targets (`ψ i`) to
  increasing sequences with a common offset; interpolate linearly in `S = O(1/(gap))` steps, each
  moving every arm by less than a quarter of the smallest gap (gaps stay `≥ min(start, target)`);
  each step is a window step in which an arm whose move passes a corner turns instead of jogging
  (at most one arm per corner per step). The plan is integer arithmetic on side coordinates at the
  radii `R_k = R + k Δ`; the invariant per step is "ends in windows of width `W` around the planned
  positions, sectors disjoint".
* **Size**: turns 4 × 150 lines (generated), sectors lemma 150, planning and invariants 500–800. One
  session (package "A3b-2d"), or the first part of A3b-3.

**(b) The two-sided gluing** (§14.5, lower half of quasi-multiplicativity): an inner family (arms
from `B_{r₁}` to `∂B_{ρ}`, outer fences, ends in windows `θ̃`) and an outer family (arms from `∂B_{ρ'}`
to `∂B_{r₃}`, `ρ' > ρ`, **inner** fences, starts in the same windows) are joined by straight corridors
(jogs with `d = 0` between the two window sets, no cap) to arms from `B_{r₁}` to `∂B_{r₃}`. Needs:
the inner predicates `HasInnerFence`/`ArmsInnerSeparated` of §12.4 (an additive definition in
`Arms/Separation/Defs.lean`, its own interface commit; the half-unit at `∂B_r` is fixed by the inner
strip lemma, §12.4); a hook into an inner fence (mirror of the leg, walking inwards from `∂B_{ρ'}`);
a gluing-of-continuations lemma for two families (`exists_isArm_of_glue` with the outer family's arm
appended after the corridor; order invariance at both boxes); the conditioning on both separated
events (the conditional mixed Harris applies to their intersection: both sections are upper for the
mixed order off the corridors). Size: about `law_mul_prod_le_law_of_corridors` + four inner hooks.

### 15.5 How A3b-3 uses the statements

* **Theorem 11, outer half.** With `u(ρ) = P(A(r, ρ))` and `v(ρ) = P(arms in windows θ̃ at ρ with
  fences (M(ρ), K(ρ)), separated)`: `u(R) ≤ u(ρ₁)` for `ρ₁ ≤ R`; at `ρ = 2N + 1`,
  `u(ρ) ≤ P(sep_η(ρ)) + δ u(N)` (`exists_law_multiArmEvent_inter_not_separated_le`);
  `P(sep_η(ρ)) ≤ C_η P(sep at ρ', small fences)` (`exists_pos_le_law_separated_of_separated`);
  `≤ C'_η v(ρ'')` (§15.4(a), to be proved); `v(ρ'') ≤ C_θ^{k} v(R)` by `k = O(log(R/ρ''))` doublings of
  window steps (`exists_pos_le_law_windows_of_windows`, constant independent of `η`); choose `δ` after
  `C_θ`. Base: `v(ρ) ≥ c` at scales `ρ ≍ r` from the one-scale bound (A3a) and the first gluing.
* **Parameters for the window steps at scale `ρ`** (all proportional to `ρ`, fixed by `θ̃`): windows
  `α i = z_side + ⌈a_i ρ⌉`, `β i = z_side + ⌊b_i ρ⌋` with `-1 < a_i < b_i < 1` from `θ̃`; bin width
  `W = ⌊μρ⌋`, fences `M = M' = ⌊μ'ρ⌋ ≥ W`, `K = W`, `K' = ⌊W/4⌋`; margin `S ≍` (gap of `θ̃`)`·ρ/8`,
  `s = 4S`; step `R' - R = ⌈ερ⌉` with shift `d i ≈ (a_i + b_i)/2 · (R' - R)` and
  `D = max |d i| ≤ ερ`; then `2(W + 2D) + 2 ≤ S` needs `μ + 2ε` small against the gap, and
  `R + M + 1 + W + M' ≤ R'` needs `ε ≥ 2μ' + μ`: choose `μ, μ' ≪ ε ≪ gap`. The windows at `R'` must
  contain `[α + d, β + d + W]`: widen the target windows by `W` per step and shrink them back by
  starting each doubling inside the core windows (the drift per doubling is `O(μ/ε)` of a window).
  `N = ⌈(b - a)/μ⌉ + 1`.
* **Windows and landing data.** A side window `[α, β]` on side `t` at `ρ` is a set of landing
  positions (top: `8ρ + 2(z₀ + ρ) - 2b₀ - δ`, …); choose core windows `θ̃` inside the windows of `θ`
  and away from the corners (each window of `IsLanding η θ` contains a sub-window of length `η/3` at
  distance `≥ η/3` from the corners when `η ≤ 1/4`); then `multiArmEventIn … (window (16R) θ η)`
  contains the window event at `R` (`multiArmEventTo_mono`).
* **Extendability, quasi-multiplicativity, a priori bound**: as in §14.5, with the window step in
  place of (G2) and §15.4(b) for the two-sided gluing.

### 15.6 Search

* PercLib, reused: `exists_mem_support_of_mem_Icc_of_mem_Icc`, `exists_walk_of_mem_support_of_mem_support`
  (`SeparationFence.lean`); `exists_walk_of_mem_localConn`, `mem_localConn_of_walk` (`RSWKeyStep.lean`);
  `SimpleGraph.Walk.exists_walk_mem_Icc`, `coord_le_add_one_of_adj` (`CrossingSymmetry.lean`);
  `mem_localConn_iff_exists_walk`; `SimpleGraph.Walk.exists_append_eq_of_notMem` (`MultiArmBasics.lean`);
  `apply_le_apply_add_one_of_adj`; `IsArm.landingPos_eq_of_top/right/bottom/left`
  (`OuterSeparation.lean`); `IsArm.exists_mem_bin`, `IsArm.sideL_of_side`, `sideP_of_side`,
  `false_of_corridor_of_corridor`, `false_of_box_of_corridor`, `false_of_region_of_region`,
  `measurableSet_preimage_cond_crossing`, `preimage_cond_crossing_iff_of_inter_eq`,
  `cond_mem_crossing_of_cond_subset`, `CrossingBounds.le_law_preimage_cond_crossing_one/zero`,
  `law_mul_prod_le_law_of_corridors`, `cond_zero_one_apply`, `ArmsOuterSeparated.le_abs_landingPos_sub`,
  `two_mul_le_abs_landingPos_sub`, `le_or_le_of_lt_of_lt`, `le_or_le_of_lt` (`CorridorGluing.lean`);
  `prodBernoulli_prod_le_biInter_of_mixed` (`MixedHarris.lean`, with `D = ∅` or `univ` for Harris
  inside one corridor).
* Mathlib: `SimpleGraph.Walk.penultimate_mem_dropLast_support`, `SimpleGraph.Walk.adj_penultimate`,
  `SimpleGraph.Walk.getLast_support`, `List.dropLast_append_getLast`, `SimpleGraph.Walk.support_transfer`,
  `Finset.pow_card_le_prod`, `Finset.prod_le_prod`, `Finset.prod_const`, `Int.ceil_le`,
  `Int.le_ceil`, `Int.cast_abs`, `abs_of_nonneg`, `abs_of_nonpos`, `neg_le_abs`, `le_abs_self`,
  `mul_le_mul_of_nonneg_right`, `le_mul_of_one_le_left`, `Int.ediv_lt_of_lt_mul`.
* Not found (added): the joining of walks through a common vertex with support control
  (`exists_walk_join`), the fence inside a crossing (`exists_mem_localConn_of_walk_zero/one`), the
  coordinate-exchanged crossing lemma, multi-crossing corridor events and Harris inside one corridor,
  the colour-aware interior, jogs and caps, the gluing inside straight boxes with a margin, landing
  positions after a jog, separation from side windows.

### 15.7 Lessons

* **Split hooks into leg and cap.** One declaration with six crossings, the cut and the new fence
  exceeded the heartbeat budget; leg (three crossings) and cap (three crossings, cut, fence) compile
  in seconds each.
* **Generate three sides from one.** The right side is the top side with the coordinates exchanged:
  a script swapping `v 0 ↔ v 1`, two-element vectors `![a, b] ↔ ![b, a]`, `crossing 0 ↔ crossing 1`
  and the crossing-bound lemma names, with `cond col 0 1` and Fin-6 indices protected
  (`hω (0 : Fin 6)`). It only works if the source avoids order-dependent steps: `simpa using` on
  coordinate conjunctions breaks (use `simp only … at this; omega`), and so do simp lemma sets
  chosen per coordinate (recompute after the swap).
* **Boxes as variables with equations** (`hlc : lc 0 = c₀ ∧ lc 1 = …`) let legs pass their own
  vectors to the cap without `convert`; implicit section variables used only in such equations must be
  passed by name (`(K' := K')`), or a `ring` goal is left with a metavariable.
* `set` for `Fin 6`-indexed vectors plus `simp [hlo, hhi]` and `nlinarith` timed out; explicit
  vectors, `change` per `fin_cases` branch and pre-linearised aspect bounds (`rw [hw'] at hκV` with
  `W₀ - 2K' = w`) are cheap.
* `simp_all` in a large context times out; a case split on the colours with `rfl` closes the same
  goals.
* `lake env lean` on a scratch file uses `autoImplicit` default (true): a hypothesis mentioning a
  variable bound later silently gets an auto-bound copy (`Wc✝`); the real build (`autoImplicit =
  false`) would reject it. Bind variables before use.
* **The proof-only classifier tokenizes ASCII only**: `hκdef` reads as `def` and makes the change an
  interface change. Avoid identifiers whose ASCII pieces are keywords (`def`, `instance`, …); check
  with the `FORBIDDEN` set of `scripts/check_proof_pr.py` before the gate.
* Builds: `JogCorridors` 28 s, `CapGluing` 11 s; gate about 9 min.

### 15.8 Gate

`scripts/gate.sh main` **passed on `e15749d`** (axiom audit 11322 constants, only `propext`,
`Classical.choice`, `Quot.sound`; the expected interface NOTICE from `Arms/Defs.lean`, no other
notice). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on e15749d8631dab5f138dc1a10bff92b39d3e2480
```

A first run on `d1b2f16` also passed, but its NOTICE named `CapGluing.lean` (token `def`): the
classifier of `scripts/check_proof_pr.py` splits identifiers at non-ASCII letters, so the hypothesis
name `hκdef` produced `def`. `e15749d` renames it (`hκeq`); no statement changed. This note's commit
changes only `docs/`.
