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
are designed in §15.4 and not proved (A3b-2d). The A3b-2d session (§16) proved corridors that turn
round the four corners, jogs whose new fence may be as large as the old one, the gluing over disjoint
regions, the stage of moves between windows (jogs and turns, `exists_pos_le_law_windows_of_moves`) and
chains of stages with constant fences (`exists_pos_le_law_windows_of_stages`); it added the inner
fence predicates as an interface commit in `Arms/Separation/Defs.lean`. The motion plan (the stage
data from start bins to prescribed windows, package A3b-2e) and the two-sided gluing are designed in
§16.5–§16.6 and not proved; §16.4 records that A3b-2c's window step cannot be iterated (fixed by the
wide caps). The A3b-2e session (§17) proved the motion plan and the first gluing into prescribed
windows (`exists_pos_le_law_target_windows`, and from the outer step's separated event
`exists_pos_le_law_target_windows_of_separated`), with a last stage that changes the fences in the
room of the target windows; the two-sided gluing was not started (design refined in §17.6). The
A3b-2f session (§18) proved the two-sided gluing (`exists_pos_le_law_two_sided`: arms separated at
the outer boundary of `B_R(z)` and arms separated at the inner boundary of `B_{R'}(z)`, with windows
aligned with one straight corridor per arm, glue into arms of `(r, R₃)` at the cost `c A ^ j`) and
the lower half of quasi-multiplicativity modulo the two separation steps
(`exists_pos_mul_le_of_separated_of_separated`); item 5 of §5 is complete. The A3b-3 session (§19)
proved Theorem 11's outer half (landing in the windows of landing data, and a separated form with
parameters proportional to the radius), extendability of the outer radius, the upper half of
quasi-multiplicativity for all ordered radii and the a priori lower bound; Theorem 11's inner half,
the lower half of quasi-multiplicativity and extendability inwards need an inner separation step,
designed in §19.6 and not proved. The A3b-3b session (§20) proved the inner separation step
(`exists_inner_separating_event`, `exists_law_multiArmEvent_diff_innerSeparated_le`) by corner exclusion
through the one-arm bound, Lemma 15 in thin strips and Lemma 15 for the dual configuration; Theorem 11's
inner half, the lower half of quasi-multiplicativity and extendability inwards remain (§20.5). The A3b-3c
session (§21) found that the inner step's families do not fit the two-sided gluing as stated (neighbouring
starts too close for regions disjoint across colours; starts too close to the corners; `η` not known to be
small) and repaired all three (`exists_pos_le_law_two_sided_of_colour`; the inner step's corner events and
`η ≤ 1/256` stated); it proved the core step of the lower half (`exists_pos_mul_le_law_of_plan_two_sided`)
and the reindexing by rotations; the binning, the arithmetic and the induction of the lower half, extendability
inwards and Theorem 11's inner half remain, redesigned in §21.2 and §21.6 (order: lower half, inwards
extendability, then the inner half at bounded ratio). The A3b-3d session (§22) proved the lower half of
quasi-multiplicativity (`exists_law_multiArmEvent_mul_law_multiArmEvent_le`) and extendability of the
inner radius (`exists_law_multiArmEvent_le_law_multiArmEvent_of_le_two_mul`) by the route of §21.2, with
step S, the far inner family and its bins, and extendability of the outer radius at bounded ratio below
`L`; Theorem 11's inner half remains (package A3b-3e, §21.6). Nothing in `Arms/Defs.lean` or
`Planar/Defs.lean` was changed. Local commits only, nothing pushed.

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

## 16. A3b-2d (2026-11-24): corner turns, wide caps, stages of moves between windows; inner fences

Package A3b-2d = the rest of item 5 of §5 as designed in §15.4: (a) the first gluing into fixed
windows (the rotation) and (b) the two-sided gluing. **Proved for (a):** corridors that turn round
the four corners, jogs whose new fence may be as large as the old one (wide caps), the gluing over
pairwise disjoint regions, **the stage of moves between windows** (every arm jogs along its side
or turns round the next corner, constant independent of the separation scale) and **chains of
stages** with constant fences. **Not proved for (a):** the motion plan, i.e. the existence, for given
start bins and prescribed target windows, of the stage data the chain theorem takes; it is pure
integer combinatorics, designed in §16.5 (package "A3b-2e"). **For (b):** the inner fence
predicates are added as an interface-only commit; the two-sided gluing itself is designed in §16.6,
not proved. One erratum to §15.5 (the window step of A3b-2c cannot be iterated) is fixed by the wide
caps (§16.4). Commits:

* `b069f97` **Arms/TurnCorridors** (new module, 1905 lines, 24 theorems; proof-only).
* `3d5707e` **Arms/RotationGluing** (new module): gluing over regions, region disjointness, one move,
  the stage of moves (proof-only).
* `f04a0ba` **Arms/RotationGluing**: chains of stages, covering by bin windows (module now 1530
  lines, 19 theorems; proof-only).
* `4aba31b` **Arms/Separation/Defs** (**interface**, additive): `HasInnerFence`,
  `ArmsInnerSeparated`, `innerSeparatedArmEvent` and their API (+462 lines; nothing outer changes).
* this note's commit (docs only).

Gate: §16.10.

### 16.1 The statements proved (a)

**Legs of two crossings** (`exists_walk_leg2_top/bottom/right/left`): a fenced arm ending in the
bin `[x, x + W]` on a side of `B_R(z)` (`W ≤ K ≤ M`) is continued on the crossings of `V₁` (out of
the side, `[x, x + W] × [z₁ + R, z₁ + h + W]` on the top side) and of a band `H` at the level `h`
(`[xl, xr] × [z₁ + h, z₁ + h + W]`, any `xl ≤ x`, `x + W ≤ xr`) by a walk of its colour through the box
of radius `M` about its end and `V₁` to a vertex of the crossing walk of `H`, whose walk is returned.

**Turns** (`exists_walk_turn_right_top`, `exists_walk_turn_top_left`, `exists_walk_turn_left_bottom`,
`exists_walk_turn_bottom_right`; the four counterclockwise ones): a leg whose band runs to the far
boundary of `B_{R'}(z)`, followed by the cap of the *next* side (A3b-2c's `exists_walk_cap_*`, whose
fence size `K'` is free) on the band. From the right side to the top side: `H₁ = [z₀ + R, z₀ + h + W]
× [y, y + W]`, band `V = [z₀ + h, z₀ + h + W] × [y, z₁ + R' - 1]`, top cap on the columns
`[z₀ + h, z₀ + h + W]`; the new end is the first exit from the interior of `B_{R'}(z)`, on the top side
in those columns, with a fence `(M', K')`, for `R + M + 1 ≤ h`, `h + W + M' ≤ R'`, `W + K' ≤ M'`.
The other three are the same at their corners (from the top side to the left side the band is
`[z₀ - R' + 1 - δ, x + W] × [z₁ + h, z₁ + h + W]`; `δ = cond col 0 1` appears only in rows (columns)
that touch the old side or the new side).

**Jogs with wide caps** (`exists_walk_jogCap_top` and the three other sides): A3b-2c's jog with the
inset of the bands set to `0` and the cap's fence box `[x + d - K', x + d + W + K']` decoupled from the
corridor: the new fence may be as long as `M' - W` (in A3b-2c it was at most `(W - 1)/2`).

**Corridor events** (`exists_corridor_of_boxes`, eight instances `exists_corridor_jogCap_*`,
`exists_corridor_turn_*`): six crossings (a turn has five; the first is counted twice) form an event
that is measurable, determined by its boxes, monotone in the colour and of probability at least
`c κ ^ 6` under `2R' + 2 ≤ κW`, `W + 2K' ≤ κ(M' - 1)`; the event, its read pairs, the region of the
continuation and the boxes of radius `M + 1` about the possible ends lie in a given rectangle
`Icc gl gh`.

**Gluing over disjoint regions** (`law_mul_prod_le_law_of_regions`): `law_mul_prod_le_law_of_corridors`
when each corridor's pairs, its continuation region and the boxes about its possible ends lie in a
region `G i`, the `G i` pairwise disjoint; the conditions on other-colour corridors and same-colour
regions then hold automatically. For fixed bins: `pow_mul_law_le_law_of_regions`
(`c κ ^ (6j) P(separated, ends in B) ≤ P(arms to ∂B_{R'}, ends in B' with fences (M', K'))`).

**Regions and one move.** `disjoint_regions_of_moves` (64 cases, eight sublemmas, `omega`): the
rectangles of two moves are disjoint when the windows are `S` from the corners and `S` apart on one
side, a turning arm is the last of its side in counterclockwise order, and
`S ≥ W + 2D + 2M + 2K' + 3`. `exists_corridor_move`: the corridor of one move (four jogs, four
turns) in its rectangle, from the window `[α, β]`, the bin start `x ∈ [α, β]` and the move.

**The stage of moves between windows** (`exists_pos_le_law_windows_of_moves`):

```lean
theorem exists_pos_le_law_windows_of_moves (σ) (hσ) (c : ℕ → ℝ≥0∞) (A N : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q L, CrossingBounds q L c → ∀ z r R R' W M K M' K' D S (h : ℤ) s
      (g' : ℤ) J (t t' : Fin j → Fin 4) (τ : Fin j → Bool) (α β d α' β' : Fin j → ℤ),
      1 ≤ W → W ≤ K → K ≤ M → 2 ≤ M' → W + K' ≤ M' → W + 2D + 2M + 2K' + 3 ≤ S →
      4M ≤ s → r + M + 1 < R → R + M + 1 ≤ h → h + W + M' ≤ R' →
      2R' + 2 ≤ A W → W + 2K' ≤ A (M' - 1) → R' ≤ L → |d i| ≤ D →
      (windows [α i, β i] of N bins of width W) → (windows S from the corners of B_R) →
      (windows on one side S apart) → (a turning arm is the last of its side counterclockwise) →
      (target: τ i = false: t' i = t i, [α i + d i, β i + d i + W];
               τ i = true: next side counterclockwise, [z₀ + h, z₀ + h + W] from the right side,
               [z₁ + h, z₁ + h + W] from the top, [z₀ - h - W, z₀ - h] from the left,
               [z₁ - h - W, z₁ - h] from the bottom) →
      1 ≤ g' → (targets g' from the corners of B_{R'}) → (targets on one side g' apart) →
      c₀ * P(separated at R (s, M, K), ends in the windows (t, α, β), inner positions in J) ≤
        P(separated at R' (2g' - 1, M', K'), ends in the windows (t', α', β'), J)
```

(windows as in `exists_pos_le_law_windows_of_windows`: side `0` top, `1` right, `2` bottom, `3` left,
coordinate along the side). `c₀ = c A ^ (6j) / (N + 1) ^ j`: **depends only on `σ`, `c`, `A`, `N`**.
With `τ ≡ false` this is the window-to-window step with output fences of any size; with `M' = M`,
`K' = K` (`W + K ≤ M`) it can be iterated with the same fences.

**Chains of stages** (`exists_pos_le_law_windows_of_stages`): `n` stages from radii `ρ k` to
`ρ (k + 1)` at levels `hl k`, stage data `t k`, `α k`, `β k`, `τ k`, `d k` (the targets of stage `k`
are the windows of stage `k + 1`), fences `(M, K)` throughout, `g' = S` at every stage:

```lean
    c₀ * P(separated at ρ 0 (s, M, K), ends in the windows of stage 0, J) ≤
      P(separated at ρ n (2S - 1, M, K), ends in the windows of stage n, J)
```

with `c₀ = c₀(stage) ^ n`, under the stage hypotheses for every `k < n` (windows `S` from the corners
and apart for every `k ≤ n`), `W + K ≤ M`, `W + 2D + 2M + 2K + 3 ≤ S`, `W + 2K ≤ A(M - 1)`,
`r + M + 1 < ρ 0`, `ρ k + M + 1 ≤ hl k`, `hl k + W + M ≤ ρ (k + 1)`, `2ρ(k + 1) + 2 ≤ A W`.
Helper `pow_mul_le_of_forall_mul_le` (`geom_le` in `ℝ≥0∞`).

**Covering by bins** (`law_le_sum_law_windows_of_separated`): `P(separated at R, s ≥ 4M) ≤
Σ_p P(separated, arm i ends in the bin window p i)` over the `(4(2A + 1))^j` choices of a side and a
bin of width `W` per arm (`R ≤ AW`); a chain starts from one of these.

### 16.2 The inner fences (interface, `Arms/Separation/Defs.lean`, commit `4aba31b`)

```lean
def HasInnerFence (ω) (c : Bool) (z) (r M K : ℕ) {a b} (γ : Walk a b) : Prop :=
  ∃ x ∈ γ.support, ∃ u v, G ∩ E ∈ localConn (Icc (a - M) (a + M)) x u ∧
    ((a 1 = z 1 + r ∧ u 0 = a 0 - K ∧ v 0 = a 0 + K ∧ G ∩ E ∈ localConn (Icc ![a 0 - K, a 1 - M] ![a 0 + K, a 1]) u v) ∨
     (a 0 = z 0 + r ∧ u 1 = a 1 - K ∧ v 1 = a 1 + K ∧ … (Icc ![a 0 - M, a 1 - K] ![a 0, a 1 + K]) u v) ∨
     (a 1 = z 1 - r - cond c 0 1 ∧ … (Icc ![a 0 - K, a 1] ![a 0 + K, a 1 + M]) u v) ∨
     (a 0 = z 0 - r - cond c 0 1 ∧ … (Icc ![a 0, a 1 - K] ![a 0 + M, a 1 + K]) u v))
def ArmsInnerSeparated (ω) (σ) (z) (r : ℕ) (s : ℝ) (M K : ℕ) (γ) : Prop :=
  (∀ i k, i ≠ k → s ≤ |innerPos z r (σ i) (γ i) - innerPos z r (σ k) (γ k)|) ∧
  (∀ i (m : ℕ), s ≤ |innerPos z r (σ i) (γ i) - m (4r + 2)|) ∧ ∀ i, HasInnerFence ω (σ i) z r M K (γ i)
def innerSeparatedArmEvent (σ) (z) (r R : ℕ) (s : ℝ) (M K : ℕ) :=
  {ω | ∃ a b γ, arms from B_r(z) to ∂B_R(z) ∧ ArmsDisjoint σ γ ∧ order ∧ ArmsInnerSeparated ω σ z r s M K γ}
```

(`G = cond c ω (dualConfig ω)`, `E` the edges.) This is §12.4's intended shape. API, mirroring the
outer one: `mem_innerSeparatedArmEvent_iff` (`Iff.rfl`), `innerSeparatedArmEvent_subset_multiArmEvent`,
`HasInnerFence.mono`, `ArmsInnerSeparated.mono`, `innerSeparatedArmEvent_mono` (antitone in `s`,
monotone in `M`, not in `K`), `innerSeparatedArmEvent_fin_zero`, `measurableSet_setOf_hasInnerFence`,
`measurableSet_innerSeparatedArmEvent`, `hasInnerFence_iff_of_inter_eq` (box
`Icc (a - (M + K)) (a + (M + K + 1))`), `mem_innerSeparatedArmEvent_iff_of_inter_eq` (`r < R`, box
`B_{R + M + K + 1}(z)`), `HasInnerFence.map_add`, `image_add_mem_innerSeparatedArmEvent(_iff)`
(with `innerPos_map_add`), the helper `IsArm.start_mem_Icc` (an arm from `B_r(z)` starts in
`Icc (z - r - 1) (z + r)`), and an `example`: with every edge open, the open arm `(1, 0) → (2, 0)`
from `B_1(0)` to `∂B_2(0)` has inner position `9` (corners `6`, `12`) and the inner fence
`(1, -1) → (1, 1)` in `[0, 1] × [-1, 1]`, so it lies in `innerSeparatedArmEvent ![true] 0 1 2 2 1 1`.

**The half-unit (§12.4) is settled as follows:** the dual inner fence box is anchored at the first
face `a` and contains its row (column), which lies just outside `B_r(z)`, and the `M` rows inside.
A fence one row further in (the other form §12.4 anticipated from reflecting Lemma 15's arm box) is
also a fence in this sense (a connection in a sub-box is a connection in the box), so the definition
fits both forms an inner separation step may produce; it does not fix a half-unit that a proof could
contradict.

For the interface PR (stacked after the outer one, §12.5): the three definitions and the 14 API
theorems above, one `example`; no tag, no `…Input`. A reviewer's questions: right notion (mirror of
the outer, fence box inside `B_r`); duplicates (none; `rg -i "innerfence|innerSeparated"` empty
before); the corner formula `m (4r + 2)` (the doubled inner box has side `4r + 2`, `innerPos`'s
docstring); arms separated at both ends are written inline (`ArmsOuterSeparated … ∧
ArmsInnerSeparated …`), as §12.3 proposed.

### 16.3 Decisions (mine, per the standing instruction)

1. **Wide caps.** The output fence of a stage is decoupled from the corridor width (`W + K' ≤ M'`
   instead of `4K' ≤ W`), so a stage can output the fences it was given (`M' = M`, `K' = K`); this
   is what makes stages iterable (erratum, §16.4).
2. **Counterclockwise turns only, from anywhere on the side.** A turn is taken by the last arm of its
   side in counterclockwise order, from wherever its window is; it lands on the next side near its
   start corner (`[z₀ + h, z₀ + h + W]` etc.). Arms never need to approach a corner by jogs (they
   cannot: corners recede faster than jogs move, §16.4). One turn per side per stage.
3. **Regions are rectangles,** one formula for each side and kind of move (in
   `disjoint_regions_of_moves`, together with the window bounds); disjointness from one-dimensional
   conditions on the windows: `S` from the corners, `S` apart, the turning arm last;
   `S ≥ W + 2D + 2M + 2K' + 3`. The gluing over regions replaces A3b-2b's corner lemma (`hQdisj` and
   `hTB` follow from disjointness), at the price of needing room (`s ≫ M`), which the straight first
   gluing provides.
4. **One level `h` per stage** for all arms; jogs use the band `[x - D, x + D + W]` (`xl = x - D`,
   `xr = x + D`); turns use the same `h`. Typical: `h = R + M + 1`, `R' ≥ h + W + M'`; a turn's landing
   is `R' - h - W` from the new corner, so the next stage needs `R' - R ≥ S + M + W + 1`.
5. **Constants.** `κ = A` with `2R' + 2 ≤ AW` and `W + 2K' ≤ A(M' - 1)` (all box aspect ratios);
   `c₀ = c A ^ (6j) / (N + 1) ^ j` per stage, `c₀ ^ n` for a chain of `n` stages. Chosen before `q`,
   `L`, `z` and the radii.
6. **Windows and bins** as in A3b-2c: a jog's target widens by `W` (`[α + d, β + d + W]`); a turn's
   target has width `W` whatever the source window (it is fixed by `h`). The chain uses `g' = S` at
   every stage (separation `2S - 1`, read off the windows).
7. **The plan is data.** The chain theorem takes the stage data as functions of the stage index and
   checks every stage's hypotheses; producing the data (the motion plan) is separate (§16.5).
8. **Turn events have five crossings, the first counted twice,** so every move's event is indexed by
   `Fin 6` and has the bound `c κ ^ 6`.
9. **No new definition** in the proof modules; the stage statement is written out (as A3b-2c's
   window step). The inner fences are definitions (interface commit), as the task required.
10. `geom_le` exists only for `ℝ`; its `ℝ≥0∞` form `pow_mul_le_of_forall_mul_le` is proved locally
    (seven lines) rather than added to a general file.

### 16.4 Errata and observations

* **A3b-2c's window step cannot be iterated as §15.5 says.** Its hypotheses `4K' ≤ W ≤ K` force the
  output fence `K'` to be at most a quarter of the input `K`; iterating `n` steps shrinks `K` by
  `4^n`, so after `O(log(R/ρ)/ε)` steps (§15.5) the fences vanish and the aspect ratios blow up. The
  cause is the cap's fence box tied to the corridor (`[x + d, x + d + W]`). Fix: wide caps (§16.3.1);
  `exists_pos_le_law_windows_of_moves` with `τ ≡ false` and `M' = M`, `K' = K` is the iterable
  window step. §15.5's parameter list ("`K = W`, `K' = ⌊W/4⌋`") should read `K' = K`, `W + K ≤ M`.
* **Corners recede faster than jogs move.** A stage grows the radius by `R' - R ≥ M + W + M' + 1`
  while a jog moves an arm by `|d| ≤ D < S/2`; with `S > 2M` an arm's distance to the next corner grows
  at every stage. So §15.4's "turn when near the corner" never happens; turns are taken from anywhere
  on the side by the last arm of the side (decision 2).
* **A turn's landing must clear the new corner by `S`** (it is the next stage's window): the stage
  needs `h + W + S ≤ R'`, i.e. `R' - R ≥ S + M + W + 1`. Not a hypothesis of the stage lemma (its
  output windows are checked by `hcor'`), but every plan needs it.
* **Two turning arms on one side are excluded by the "last of its side" condition only if windows are
  nonempty** (`α ≤ β`): `disjoint_regions_of_moves` takes `α ≤ β` for both arms; the stage proof gets
  it from the bin start `x ∈ [α, β]` of a nonempty bin event.
* No plan statement of §2 or §14–§15 had to change; no hypothesis beyond `hσ` was needed.

### 16.5 What remains of (a): the motion plan (package "A3b-2e", no probability)

**Statement to prove** (pure integer combinatorics): for `j` arms whose start windows are bins of
width `W` on the sides `t⁰ i` of `B_{ρ₀}(z)` (from `law_le_sum_law_windows_of_separated`), in
counterclockwise order of `i`, at least `S₀ ≫ S` from the corners and from each other, and target
windows `(t^T i, [a i, b i])` on `B_{ρ_F}(z)` in the same cyclic order, of width at least `w_F`, at
least `S_T` from the corners and apart, there are `n ≤ n₀(j, ρ₀/W, …)` and stage data `ρ k`,
`hl k`, `t k`, `α k`, `β k`, `τ k`, `d k` satisfying every hypothesis of
`exists_pos_le_law_windows_of_stages`, with stage `0` = the start bins and the windows of stage `n`
inside the target windows (then `multiArmEventTo_mono`-style monotonicity of the window event gives
the target event). All parameters are proportional to `ρ₀` with constants from `η`, `j` and the
target data, so the chain constant `c₀ ^ n` depends only on those.

**Design.**
1. *Lifted sides.* Number the sides counterclockwise `0` bottom, `1` right, `2` top, `3` left (the
   stage lemma's `t` is a relabelling). Lift start and target sides to integers `λ⁰ i ≤ λ^T i`,
   nondecreasing along `i` with `λ (j - 1) ≤ λ 0 + 4`, `λ^T i - λ⁰ i ≤ 7` (choose the lift of the
   targets with `min (λ^T - λ⁰) ∈ [0, 4)`; the targets' lifted positions minus the starts' lie in an
   interval of length less than one turn, so the maximum is below `8`).
2. *Turn rounds* (at most `8j` stages). In each stage, on each side the last arm in counterclockwise
   order turns iff its lifted side is below its target; all other arms go straight (`d = 0`). Invariant:
   `λ` stays nondecreasing along `i` with the wrap condition, `λ ≤ λ^T`, so on one side the remaining
   turns `λ^T - λ` increase counterclockwise and the last arm has the most; `Σ (λ^T - λ)` drops by at
   least one per stage while positive. Geometry: a turn at stage `k` lands at the side coordinate
   `±(ρ_k + M + 1)` (level `hl k = ρ_k + M + 1`), farther out than every arm already on that side, so
   with `ρ_{k+1} - ρ_k = Δ ≥ 2S + (widths) + M + W + 1` every window stays `S` from the corners and
   from the others; windows widen by `W` per stage.
3. *Spreading* (`S₁` stages). On each side, interpolate linearly from the positions after the turn
   rounds to the target positions: `α_i(k) = u_i + ⌊k (v_i - u_i) / S₁⌋`; gaps stay at least
   `min(start gap, target gap) - 1`, corner margins too (the radius grows linearly in `k`, so margins
   interpolate), moves are at most `⌈2ρ_F / S₁⌉ ≤ D`. Floors with a variable denominator: state the
   bounds `S₁ ⌊x/S₁⌋ ≤ x < S₁ ⌊x/S₁⌋ + S₁` as hypotheses and close with `nlinarith`.
4. *Parameters.* `W ≪ M ≍ K ≪ D ≪ S ≪ Δ`, all `≍ ρ₀` with ratios from `η`, `j`, `θ̃`; the radius grows
   by `(8j + S₁) Δ`, so `ρ_F ≤ C(η, j, θ̃) ρ₀` (the first gluing's `R ≤ D(η) R` budget).
5. *Assembly.* `c₀(η) P(sep at ρ₀, s) ≤ Σ_p P(bin windows p) ≤ #p · c₀(stage)^{-n} P(target windows)`.

Size estimate: 1000–1500 lines (the lift bookkeeping and the interpolation), one session.

### 16.6 (b) The two-sided gluing: design (not proved)

**Statement** (the form the lower half of quasi-multiplicativity uses, after both families have
been put into aligned windows by Theorem 11 and window steps): for windows `(t i, [α i, β i])` at
`R` (outer boundary of the inner family) and the *same* side coordinates at `R' = R + Δ` (inner
boundary of the outer family, `[α i, β i + W]` say),

```lean
c₀ * P(arms B_{r₁} → ∂B_R, outer-separated (s, M, K), ends in the windows (t, α, β))
   * P(arms B_{R'} → ∂B_{r₃}, inner-separated (s', M', K'), starts in the windows (t, α', β'))
  ≤ P(multiArmEvent σ z r₁ r₃)          (inner windows of the first family carried, `J`)
```

with `c₀ = c(κ)^{3j}/(N+1)^{2j}`, `κ` from `Δ / W`, for `R + M + K + 1 < R' - M' - K' - 2`
(independence) and the corner/gap conditions of the windows.

**Proof plan and pieces.**
1. *Independence.* The first event is determined by `B_{R + M + K + 1}(z)`
   (`mem_outerSeparatedArmEvent_iff_of_inter_eq` with bins); the second by the pairs with an end
   outside `B_{R' - M' - K' - 2}(z)`: a new determination lemma for `innerSeparatedArmEvent` (arms
   from `B_{R'}` use edges with an end outside `B_{R'}`; inner fences lie within `M' + K' + 1` of
   the starts). Then `prodBernoulli` independence (`prodBernoulli_iInter_fin_of_determined` pattern)
   gives `P(E_in) P(E_out) = P(E_in ∩ E_out)`.
2. *Straight two-sided corridors.* For arm `i` on the top side: one bottom-top crossing
   `V = [x, x + W] × [z₁ + R, z₁ + R']` of the colour of the arm. It meets the outer fence of the inner
   arm (horizontal, in `[b₀ - K, b₀ + K] × [R, R + M]`, `W ≤ K`) and the inner fence of the outer arm
   (horizontal, in `[a₀ - K', a₀ + K'] × [R' - M', R']`, `W ≤ K'`) by
   `exists_mem_support_of_mem_Icc_of_mem_Icc`, giving `x ∈ γ_in → fence → V → fence → y ∈ γ_out`.
   Four sides (right/left by the coordinate swap). Corridor probability `c(κ)` per arm.
3. *Conditioning on both families.* The sections of `E_in ∩ E_out` at fixed coordinates off the
   corridors are upper for the mixed order: for `E_in` this is `separated_of_mixed_of_forall_mem`
   (corridors miss the interior of `B_R` and the other-colour fence boxes at `R`); for `E_out` the
   mirror (`separated_of_mixed` at the inner boundary: corridors miss the exterior of `B_{R'}` except
   near the starts, and the other-colour inner fence boxes). Then
   `prodBernoulli_mul_le_inter_of_mixed_of_determined` with `A = E_in ∩ E_out`.
4. *The barrier at the inner boundary* (mirror of `notMem_support_of_mem_Icc`): a walk of the colour
   of outer arm `i`, from a vertex of it near its start, whose points outside `B_{R'}` lie near the
   start, misses every other outer arm of that colour (pack-free; same proof with `innerPos` and the
   sector lemma `sbtw_innerPos_iff_sbtw_landingPos`).
5. *Gluing.* `exists_isArm_of_glue` with the continuation `P_i ++ (tail of γ_out i)` (ending at
   `∂B_{r₃}`); `hdisj` from disjoint regions (corridors), the outer family's disjointness, and step 4;
   order by order invariance at both boxes.
6. *Bins.* Union over the bins of both families (`(N + 1)^{2j}` configurations), as in the window
   step.

Reuses: `law_mul_le_law_inter_of_mixed_of_innerPos` (conditioning, generalised to two events),
`exists_isArm_of_glue`, `exists_mem_support_of_mem_Icc_of_mem_Icc(_swap)`, `exists_walk_join`,
`le_abs_landingPos_sub_of_windows`, the corridor event tools of `JogCorridors.lean` and
`TurnCorridors.lean`, the new inner fence API. Size: about `law_mul_prod_le_law_of_corridors` plus
four hooks plus the inner barrier, 1200–1500 lines, one session (after A3b-2e, or in parallel: it
needs no plan).

### 16.7 How A3b-3 uses the statements

* **Window steps that iterate.** `exists_pos_le_law_windows_of_stages` with `τ ≡ false` (or
  `exists_pos_le_law_windows_of_moves` with `τ ≡ false`, `M' = M`, `K' = K`): fences constant, constant
  `c₀(σ, c, A, N)` per step, independent of `η` when windows and fences are proportional to the radius.
  This replaces A3b-2c's `exists_pos_le_law_windows_of_windows` in §15.5's iteration (erratum §16.4).
* **Theorem 11, outer half** (§15.5 with this package): outer step (`exists_law_multiArmEvent_inter_not_separated_le`)
  → straight first gluing with fences (`exists_pos_le_law_separated_of_separated`, room `s' ≫ M'`)
  → covering by bins (`law_le_sum_law_windows_of_separated`) → the plan of §16.5 (A3b-2e) and the chain
  (`exists_pos_le_law_windows_of_stages`) into the core windows `θ̃` at `ρ'' ≤ C(η) ρ` → iterable window
  steps (chain with `τ ≡ false`) to `R`; choose `δ` after the window-step constant.
* **Quasi-multiplicativity, lower half**: §16.6 after aligning both families' windows by window steps.
* **Inner half of Theorem 11**: the inner separation step will produce `innerSeparatedArmEvent`
  (fence box as in §16.2); the inner gluing is the mirror of this package (turns and jogs inward), or
  reduced to the outer one by the two-sided gluing.

### 16.8 Search

* PercLib, reused: `exists_walk_cap_top/right/bottom/left`, `exists_walk_join`,
  `exists_mem_support_of_mem_Icc_of_mem_Icc(_swap)`, `exists_walk_of_mem_localConn`,
  `measurableSet_setOf_forall_cond_crossing`, `forall_cond_crossing_iff_of_inter_eq`,
  `prod_law_le_law_setOf_forall_cond_crossing`, `cond_mem_crossing_of_cond_subset`,
  `CrossingBounds.le_law_preimage_cond_crossing_one/zero`, `mem_cond_interior_iff`,
  `law_mul_prod_le_law_of_corridors`, `HasOuterFence.of_nil`, `exists_lt_mem_bin`,
  `IsArm.exists_mem_bin`, `ArmsOuterSeparated.le_abs_landingPos_sub`, `le_abs_landingPos_sub_of_windows`,
  `cond_zero_one_apply`; for the interface: the whole outer API as a template, `innerPos_map_add`,
  `isOpenArm_toWalk_iff`, `perimeterPos_of_right`, `edgeSet_mem_localConn_Icc`.
* Mathlib: `geom_le` (for `ℝ` only; the `ℝ≥0∞` form proved locally), `Finset.pow_card_le_prod`,
  `measure_iUnion_fintype_le`, `ENNReal.pow_pos`, `ite_eq_left_of_eq_true`,
  `ite_eq_right_of_eq_false` (the `ite_cond_eq_true/false` names are deprecated), `eq_true`, `eq_false`,
  `Sym2.out_fst_mem`, `Set.disjoint_left`, `Icc_subset_Icc`.
* Not found (added): turns at corners, wide caps, corridor events from boxes in a region, gluing over
  disjoint regions, region disjointness of moves, the stage of moves, chains of stages, the covering by
  bin windows, inner fences.

### 16.9 Lessons

* **`omega` reasons about `Fin 4` equalities** (`t i = 0`, `t i = 1` contradict); the
  `first | omega | absurd …` fallback was flagged as unreachable.
* **`rcases … with rfl` on `t' = t`** eliminates `t` (the right-hand variable); use a named
  hypothesis and `subst t'` to keep `t`.
* Event texts with a bound `k` (`∀ i k l, i < k → …`) capture a stage index named `k` substituted into
  them: name stage indices `m` in such places; radii `ρ k` need parentheses inside applications.
* **Generated 64-case disjointness**: eight sublemmas (one per case of the first arm), each `rcases`
  on the second arm and one `omega`, with only the needed same-side facts introduced per case; unused
  hypotheses named `_h…` (the linter flags hypotheses that `omega` happened not to use).
* Boxes as variables with equations (`obtain ⟨gl, hgl₀, hgl₁⟩ : ∃ gl, gl 0 = … ∧ gl 1 = … :=
  ⟨![_, _], rfl, rfl⟩`) again kept every region fact `omega`-ready.
* `CrossingBounds.le_law_box_one/zero` (corners as four integers) let the probability facts of a
  `Fin 6` event be passed by `fin_cases` and `exact` without `change`.
* Builds: `TurnCorridors` 18 s, `RotationGluing` 9 s, the interface change rebuilt the dependents of
  `Arms/Separation/Defs.lean` in a few minutes.

### 16.10 Gate

`scripts/gate.sh main` **passed on `4aba31b`** (axiom audit 12144 constants, only `propext`,
`Classical.choice`, `Quot.sound`; the interface NOTICE, expected: the classifier names the first
interface file, `Arms/Defs.lean`; `Arms/Separation/Defs.lean` changed too, by the additive interface
commit `4aba31b`; no other notice). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 4aba31b4c1fc6dd4da6e40a50622e8f3235750de
```

The gate ran after a full `lake build --wfail` of the same tree (4020 jobs, which rebuilt the
dependents of `Arms/Separation/Defs.lean`). This note's commit changes only `docs/`.

## 17. A3b-2e (2026-11-24): the motion plan; the first gluing into prescribed windows

Package A3b-2e = (a) the motion plan of §16.5 and (b) the two-sided gluing of §16.6. **Proved
(a):** separated arms are carried into prescribed windows at a larger radius, in their
counterclockwise order, with fences of any size at the end. The plan has rounds of turns, then
linear spreading along the sides, then one last stage that changes the fences. The first gluing
into windows, starting from the outer step's separated event, is assembled with a constant
depending only on `σ`, `c` and two ratios. **Not started (b):** §17.6 refines the design.
Commits:

* `194d39c` **Arms/MotionPlan** (new module, proof-only): counterclockwise window coordinates, the
  stage lemma in them, one round of turns, the start of the plan, the two phases, the plan and
  the composite with the straight first gluing.
* `1df9316` **Arms/MotionPlan** (proof-only): the fence change moved from the first stage of the
  spreading to a separate last stage (§17.3, first item); the plan for fixed bins split off.
* this note's commit (docs only).

Gate: §17.9.

### 17.1 The statements proved (`PercLib/Models/Planar/Arms/MotionPlan.lean`, 1675 lines, 22 theorems)

**Counterclockwise coordinates.** A window on side `t` (`0` top, `1` right, `2` bottom, `3` left) is
`[u, v]` with `u, v` the coordinate along the side minus that of `z` on the right and bottom sides,
its negative on the top and left sides. `exists_side_window` and `exists_ccw_window` translate to
and from the windows `[α, β]` of the stage lemmas (same ends of arms). `side_center_eq` gives the
translation with the centre `if t = 0 ∨ t = 2 then z 0 else z 1` of the stage lemmas.
`mem_side_window_of_le` and `mem_ccw_window_of_le` state monotonicity. In these coordinates
counterclockwise order on a side is increasing order, the last arm of a side is the one with the
largest coordinates, and a turn always lands in `[-h - W, -h]` on the next side.

**The stage in counterclockwise coordinates** (`exists_pos_le_law_ccw_of_moves`): the statement of
`exists_pos_le_law_windows_of_moves`, with windows `[u, v]` and new windows `[u', v']` that only
need to *contain* the image: `[u + e - W, v + e + W]` for a jog by `e`, or `[-h - W, -h]` for a
turn. Same constant `c A^(6j)/(N+1)^j`.

**One round of turns** (`exists_turn_step`, pure combinatorics, `Fin (m + 1)`). State: lifted sides
`lam i` (sides counted counterclockwise from the bottom side, `lam i + t i ≡ 2 (mod 4)`), windows
`[u i, v i]`. The invariant:
* (L1) lexicographic order of `(lam, u)` along the index with gaps `G`;
* (L2) wrap: `lam (last) < lam 0 + 4`, or equality with `v (last) + G ≤ u 0`;
* (L3) windows `G` from the corners;
* `lam ≤ lamT`, with `lamT` nondecreasing and `lamT (last) ≤ lamT 0 + 4`.

Rule: arm `i` turns iff `lam i < lamT i`, `lam i < lam l` for every `l > i`, and
`lam i < lam 0 + 4`. Such an arm is the last of its side. The invariant holds again at the next
radius with gaps `G - 2W`, and `Σ (lamT - lam)` drops while positive. When some arm has turns
left, take the largest such index; if it is not last, the last arm of the first block turns.
`gap_of_lex` turns (L1)–(L2) into the gap hypothesis of the stage lemma.

**The start** (`lift_add_le_of_sbtw`, `IsArm.exists_landingPos_eq_of_window`,
`exists_lift_of_separated`). Lifting by `16R` every landing position below that of arm `0` turns
the cyclic order `sbtw` into an increasing order with gaps `s`. Each landing position is
`4Rc + x` with `c` the counterclockwise side and `x ∈ [2u + 2R - 1, 2v + 2R + 1] ∩ [s, 4R - s]`.
For separated arms (separation `≥ 2G + 4W + 2`) ending in bins of width `W`, this gives lifted sides
`lam ∈ [0, 7]` satisfying the invariant with gaps `G`.

**Phase 1** (`exists_pos_le_law_turns`): `n₁` rounds of turns. The radius grows by at least
`G + M + W + 1` per round, the fences `(M, K)` are kept. Starting with at most `n₁` turns in all,
every arm ends on the side of `lamT`, in lexicographic order with gaps `G - 2n₁W` and widths at
most `(2n₁ + 1)W`. Constant `c₁ ^ n₁`.

**Phase 2** (`exists_pos_le_law_spread`): `n` stages of linear spreading. The radius grows by `Δ ≥
2M + W + 1` per stage. Arm `i` jogs by the same `e i = ⌊(uT i + n + nW - u i)/n⌋` at every stage
(`|e i| ≤ D` from `2(ρ₀ + nΔ) + 2n + nW ≤ nD`). Positions, gaps and corner margins are then linear
in the stage index, and `le_add_mul_of_le_of_le` checks them at the two ends. The arms end in
`[uT i, uT i + n + w + 2nW]`. The fences `(M, K)` are kept. Constant `c₂ ^ n`.

**The last stage** (`exists_pos_le_law_fences_of_windows`): one straight stage (`τ ≡ false`,
`e ≡ 0`) from `R' - (M + M' + W + 1)` to `R'`. Arms inside `[uT + W, vT - W]` end in the targets
`[uT, vT]` with the new fences `(M', K')`, separated at scale `2Q - 1`. The room needed is
`Q ≥ 2M + 2K' + W + 3`, which the targets provide (gaps `Q`, corners `Q + M + M' + W + 1`).

**The plan** (`exists_pos_le_law_target_windows_of_bins` for fixed bins, then the covering
`law_le_sum_law_windows_of_separated`):

```lean
theorem exists_pos_le_law_target_windows (σ) (hσ) (c) (A n : ℕ) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q L, CrossingBounds q L c → ∀ z r R R' W M K M' K' D S G Q B s J
      (tT : Fin j → Fin 4) (lamT αT βT : Fin j → ℤ),
      1 ≤ W → W ≤ K → W + K ≤ M → 2 ≤ M' → W + K' ≤ M' →
      W + 2K ≤ A (M - 1) → W + 2K' ≤ A (M' - 1) →
      W + 2D + 2M + 2K + 3 ≤ S → S + 2 (12 j) W ≤ G → W + 2M + 2K' + 3 ≤ Q →
      2G + 4W + 2 ≤ s → r + M + 1 < R →
      R + 12 j (G + M + W + 1) + n (2M + W + 1) + (M + M' + W + 1) ≤ R' →
      2R' + 2 ≤ A W → R' ≤ L → 2R' + 2n + nW ≤ n D → n + (24 j + 2n + 3) W ≤ B →
      (∀ i, 0 ≤ lamT i ≤ 3 ∧ lamT i + tT i ≡ 2 (mod 4)) → Monotone lamT →
      (target windows at least S + Q + M + M' + W + 1 from the corners of B_{R'}) →
      (∀ i, αT i + B ≤ βT i) →
      (∀ i < l, tT i = tT l → counterclockwise order on the side with gap S + Q) →
      c₀ * P(separated at R (s, M, K), inner positions in J) ≤
        P(separated at R' (2Q - 1, M', K'), ends in the windows (tT, αT, βT), J)
```

`c₀ = c₁^(12j) c₂^n c₃ / (4(2A + 1))^j` with the stage constant at `N = 24j + 2n + 1`. It depends
only on `σ`, `c`, `A`, `n`. Non-vacuity, checked by hand: `j = 1`, `n = 100`, `W = K = 1`,
`M = M' = 2`, `K' = 1`, `Q = 10`, `D = 203`, `S = 416`, `G = 440`, `s = 886`, `R = 1000`,
`R' = 10000`, `A = 20002`, `B = 327` and one window 432 from the corners satisfy every hypothesis.

**The first gluing into prescribed windows** (`exists_pos_le_law_target_windows_of_separated`). The
input is separated arms with `4M ≤ s` only, which is the output of the outer separation step. A
straight first gluing (`exists_pos_le_law_separated_of_separated` with corridors `4W`, new fences
`(4W, W)` at `R + M + 1 + 8W`, ratios `A` and `A + 4`) makes room; the plan does the rest.
Hypotheses as above with `4W ≤ K`, `8W + 2 ≤ M`, `2G + 20W + 2 ≤ s`, `W + 2D + 10W + 3 ≤ S`,
`9W + 2K' + 3 ≤ Q` and the budget
`R + M + 1 + 8W + 12j(G + 5W + 1) + n(9W + 1) + (M' + 5W + 1) ≤ R'`.

Generic helpers: `le_add_mul_of_le_of_le` (a linear function above a bound at both ends of an
interval), `exists_pow_mul_le_of_forall_exists` (iterating a step under an invariant in `ℝ≥0∞`),
`mul_measure_le_of_nonempty`, `turn_side_rel`, `val_sub_one_fin_four`.

### 17.2 Decisions (mine, per the standing instruction)

1. **The plan is built one stage at a time under an invariant, not as data.** Rule 4 allows
   definitions only in `Basic`/`Defs` files, so a recursively defined plan cannot be written in the
   proof module. Each phase iterates the stage lemma with `exists_pow_mul_le_of_forall_exists`.
   The chain theorem `exists_pos_le_law_windows_of_stages` is not used; this is equivalent, and
   the per-stage room and fences can vary.
2. **Counterclockwise coordinates, moves in containment form.** In the state, windows widen by `W` at
   both ends per jog (the exact image widens at one end), so the invariants have no case split by
   side. The four-side case analysis happens once, in `exists_pos_le_law_ccw_of_moves`.
3. **The turning rule and the lifts.** Start lifts come from the landing positions
   (`lam ∈ [0, 7]`); target lifts are `lamT + 8 ∈ [8, 11]`. Each arm needs at most 11 turns, so
   there are `n₁ = 12j` rounds, idle once every arm is done. The fixed number keeps the constant
   uniform. Every arm makes at least one turn (a full extra turn round the box is allowed); this
   is harmless.
4. **Targets** are given in the stage format `(tT, αT, βT)` at `R'` together with `lamT ∈ [0, 3]`
   nondecreasing, with no wrap. For Theorem 11's landing data, `IsLanding` windows increase with the
   index from the bottom-left corner, so `lamT i = ⌊4 θ̃ i⌋`.
5. **Radius increments.** Phase 1 uses `G + M + W + 1` per round, so a turn's landing clears the
   new corner by the current gap bound. Phase 2 uses `2M + W + 1`, which is small, so jogs outrun
   the receding corners (§17.3) and targets near corners are reachable. The last stage uses
   `M + M' + W + 1`. Phase 1's last round absorbs the remainder of the radius budget.
6. **Constant moves in phase 2** (`e i` fixed per arm): everything is linear in the stage index,
   so floors appear only once, in `e i`.
7. **Fences change only in the last stage** (taken after the first commit; §17.3). The plan's
   fences `(M, K)` stay below the plan's room `S` (of order the separation scale). The output
   fences `(M', K')` only need the targets' room `Q`.
8. **Output separation `2Q - 1`**, read off the target windows.
9. **Composite with the straight first gluing:** corridors `4W`, fences `(4W, W)`, radius
   `R + M + 1 + 8W` (all fixed multiples of the plan unit `W`), ratios `A`, `A + 4`.
10. **No threshold on radii:** all hypotheses are linear; small radii make them unsatisfiable,
    not false.
11. **No new definition.** Events are written out as in A3b-2b–2d. A Python template generated
    them.

### 17.3 Errata and observations

* **§16.5 with one room `S` throughout cannot give fences independent of the separation scale.**
  The stage lemma needs `S ≥ 2M + 2K' + …` at the stage that outputs `K'`. If the fences change at
  the first spreading stage, `K' ≲ S ≲ s`, the separation of the outer step (`≍ √η R`). A3b-3's
  window steps then need fences `≍ μR` with `μ` independent of `η` (their constant depends on
  `R/W` and `W ≤ K`). Fix: a separate last stage in the room of the targets (Decision 7). The
  first commit `194d39c` had the weaker form; `1df9316` replaced it.
* **Turns land before the arms of the next side**, not "farther out than every arm on the side"
  (§16.5): in counterclockwise coordinates the turning arm lands at the start of the next side.
  The lexicographic invariant accounts for this.
* **§16.5's wrap condition `λ (j - 1) ≤ λ 0 + 4` needs the equality case refined.** Two arms can
  share a side with lifts four apart, the last arm before the first. That is (L2).
* **Jogs can outrun the corners in phase 2.** §16.4's "corners recede faster than jogs move"
  concerns stages with turns (`R' - R > S`). Without turns the increment is `2M + W + 1 ≪ S`, so the
  speed `D/Δ` can be large.
* No plan statement of §2 or §14–§16 had to change. No hypothesis beyond `hσ` was needed.

### 17.4 How A3b-3 uses the statements

* **Theorem 11, outer half**, at the scale `ρ = 2N + 1` of the outer step:
  * The outer step gives the separated event (`s = 4√ηN`, `M = ⌊√ηN⌋`, `K = ⌊ηN⌋`).
  * Apply `exists_pos_le_law_target_windows_of_separated` with
    * `W = ⌊η² N / C₁⌋`, `D = ⌊√η N / 16⌋`, `S = 11W + 2D + 3`, `G = S + 24jW`;
    * `n = ⌈C₂ / √η⌉`, so that `2R' + 2n + nW ≤ nD`, and `B = n + (24j + 2n + 3)W`;
    * `R'` in `[ρ + C₃ j √η N, C₄ ρ]`.
  * The targets are A3b-3's core windows `θ̃` at `R'`, with gaps and margins `≍ ϑR'`, and fences
    `M' ≍ μR'`, `K' ≍ μR'/2` with `μ ≪ ϑ`; then `Q = W + 8W + 2K' + 3`.
  * All hypotheses hold for `N ≥ N₀(η, ϑ, μ, j)`.
  * The output is the input of the window steps: the chain `exists_pos_le_law_windows_of_stages`
    with `τ ≡ false`, fences `(M', K')`, room `≍ ϑR`. Its constant does not depend on `η`.
  * The constant `c₀(σ, c, A, n)` depends on `η` through `A ≍ 1/η²` and `n ≍ 1/√η` only. This is
    the "first gluing" constant `C_η` of §15.5; choose `δ` after the window-step constant and `η`
    after `δ`.
* **Re-aligning windows** for quasi-multiplicativity: the plan (or `exists_pos_le_law_spread`
    alone, for windows already on the right sides) moves a family between any two window
    configurations in the same counterclockwise order.
* **Inner half:** the mirror statements (turns and jogs inward) are not proved. Alternatively,
  the inner half reduces to the outer one through the two-sided gluing (§17.6).

### 17.5 What remains

* (b) the two-sided gluing (§17.6), then A3b-3 (Theorem 11 with §17.4, extendability,
  quasi-multiplicativity, the a priori lower bound).

### 17.6 (b) The two-sided gluing: refined design (not started)

**Target statement** (the form used for `π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)`, after both families
have been put into aligned windows by Theorem 11 and the plan):

```lean
theorem exists_pos_le_law_of_two_sided (σ) (hσ) (c) (A N : ℕ) :
    ∃ c₀ > 0, ∀ q L, CrossingBounds q L c → ∀ z r₁ R R' r₃ W M K M' K' s s' J (t : Fin j → Fin 4)
      (u v : Fin j → ℤ),
      (inner family: windows [u, v] on the sides t of B_R, S from the corners and apart) →
      (outer family: starts in the same windows on the sides of B_{R'}) →
      W ≤ K → W ≤ K' → R + M + 1 ≤ R' - M' - 1 → R' ≤ A W → ... →
      c₀ * P(separated at R (s, M, K), ends in (t, u, v), J) *
          P(innerSeparatedArmEvent at R' (s', M', K'), starts in (t, u, v), arms to ∂B_{r₃}) ≤
        P(multiArmEventIn σ z r₁ r₃ J univ)
```

**Pieces, in order, with what exists:**

1. *Independence.* The inner event is determined by the pairs in `B_{R + M + K + 1}`
   (`mem_outerSeparatedArmEvent_iff_of_inter_eq`). New: `mem_innerSeparatedArmEvent_iff_of_inter_eq_out`,
   which says the outer event is determined by pairs with both ends outside `B_{R' - M' - K' - 2}`.
   Arms from `B_{R'}` use only edges with an end outside the interior after the first step, and the
   inner fences lie within `M' + K' + 1` of the starts. Then use product independence (the pattern of
   `prodBernoulli_iInter_fin_of_determined`, for two events). About 250 lines; the half-units are
   those of §16.2.
2. *Straight two-sided corridors.* On the top side, one bottom-top crossing of
   `[x, x + W] × [z₁ + R, z₁ + R']` in the arm's colour:
   * it meets the outer fence (horizontal in `[b₀ - K, b₀ + K] × [R, R + M]`) and the inner fence
     (horizontal in `[a₀ - K', a₀ + K'] × [R' - M', R']`), by
     `exists_mem_support_of_mem_Icc_of_mem_Icc`, as the legs `exists_walk_leg2_*` do;
   * four sides by the coordinate-swap template; event bound `c κ` with `κ` from `(R' - R)/W`.
   About 400 lines (four hooks and the corridor events).
3. *Conditioning on both families.* Generalise `law_mul_le_law_inter_of_mixed` to an event
   `A₁ ∩ A₂`:
   * `separated_of_mixed_of_forall_mem` handles `A₁`;
   * the mirror at the inner boundary (new, `innerSeparated_of_mixed_of_forall_mem`: corridors miss
     the exterior of `B_{R'}` except near the starts, and the other-colour inner fence boxes)
     handles `A₂`;
   * then apply `prodBernoulli_mul_le_inter_of_mixed_of_determined`.
   About 300 lines.
4. *Inner barrier.* The mirror of `notMem_support_of_mem_Icc`: a walk of the colour of outer arm
   `i`, from a vertex near its start, whose points inside `B_{R'}` lie near that start, misses the
   other outer arms of that colour (pack-free). Use `ArmsDisjoint.of_innerPos_eq` and
   `sbtw_innerPos_iff_sbtw_landingPos` on the outer family. About 200 lines.
5. *Gluing.* Apply `exists_isArm_of_glue` with the continuation fence → corridor → fence → tail of
   the outer arm, ending on `∂B_{r₃}`:
   * corridor regions are disjoint by the window gaps;
   * the outer arms are disjoint by the outer family's `ArmsDisjoint`;
   * a corridor misses the other outer arms by step 4;
   * the order follows from order invariance at both boxes (`sbtw_landingPos_of_innerPos_eq`).
   About 300 lines.
6. *Bins.* Take the union over the `(N + 1)^(2j)` bin pairs of the two families, as in the window
   step.

Size 1300–1600 lines; one session. It needs no part of (a) beyond the window conventions; the
plan (a) aligns the windows of the two families before it.

### 17.7 Search

* PercLib, reused:
  * stages, gluing and bins: `exists_pos_le_law_windows_of_moves`,
    `law_le_sum_law_windows_of_separated`, `exists_pos_le_law_separated_of_separated`;
  * separation: `ArmsOuterSeparated.le_abs_landingPos_sub`, `ArmsOuterSeparated.mono`;
  * landing positions: `IsArm.landingPos_eq_of_top/right/bottom/left`, `IsArm.end_mem_Icc`,
    `Icc_subset_Icc_add_one_sub_one`, `mem_Icc_two_iff`.
* Mathlib:
  * integer division: `Int.mul_ediv_self_le`, `Int.lt_ediv_add_one_mul_self`, `Int.sbtw_iff`;
  * sums and maxima: `Finset.max'`, `Finset.le_max'`, `Finset.sum_lt_sum`,
    `Finset.sum_eq_zero_iff_of_nonneg`;
  * measures and `ℝ≥0∞`: `MeasureTheory.measure_mono`, `measure_iUnion_fintype_le`,
    `ENNReal.mul_inv_cancel`, `ENNReal.pow_pos`;
  * order: `le_of_mul_le_mul_left`, `ite_eq_left`/`ite_eq_right`.
* Not found (added): counterclockwise window coordinates, rounds of turns, lifting a cyclic order of
  integers, linear spreading, the motion plan, the generic iteration lemma in `ℝ≥0∞` (mathlib's
  `geom_le` is for `ℝ` and a fixed sequence, not an existential state).

### 17.8 Lessons

* **`(z - (R' - E))` elaborates with the cast distributed** (`z - (↑R' - ↑E)`), which is not the
  stage lemmas' `z - ↑(R' - E)`. Ascribe `(R' - E : ℕ)` in event texts. The same holds for
  `(ρ₀ + n * Δ : ℕ)`, or `rw [Nat.sub_add_cancel]` cannot fire.
* **omega treats products as atoms, but not the same atom across casts.** `↑(2 * n₁) * ↑W`,
  `2 * ↑n₁ * ↑W` and `↑(2 * n₁ * W)` are different atoms. State the linking equalities
  (`push_cast; ring`) and nonnegativity (`positivity`) explicitly.
* **`?_` holes inside `obtain … := f ?_ ?_` do not become goals reliably.** Pass `(by …)` blocks
  instead.
* **Per-declaration heartbeats:** the assembled plan exceeded them once the last stage was inlined;
  splitting it into the fixed-bins lemma, the last-stage lemma and a thin covering proof fixed it.
  `nlinarith` in big contexts timed out; `linarith` with explicit product facts did not.
* **Superscript `⁰` is not an identifier character** (`t⁰` is a parse error).
* A stage index named `k` is captured by event texts binding `k` (A3b-2d's lesson again): name it
  `kk` in the event family.
* `lake env lean` on the module took 3–20 s here; `lake build --wfail` 12–14 s.

### 17.9 Gate

`scripts/gate.sh main` **passed on `1df9316`** (axiom audit 12421 constants, only `propext`,
`Classical.choice`, `Quot.sound`; the interface NOTICE, expected: the classifier names the first
interface file on this branch, `Arms/Defs.lean`; no other notice). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 1df931682e460586ce02025c5a7d513f5960b458
```

This note's commit changes only `docs/`.

## 18. A3b-2f (2026-11-24): the two-sided gluing

Package A3b-2f = (b) of §16.6/§17.6, the last piece of item 5 of §5. **Proved:** arms separated at
the outer boundary of `B_R(z)` and arms separated at the inner boundary of `B_{R'}(z)` (to the
boundary of `B_{R₃}(z)`), whose windows are aligned with one straight corridor per arm, glue into
`j` arms from `B_r(z)` to the boundary of `B_{R₃}(z)` at the cost `c A ^ j`; and the lower half of
quasi-multiplicativity follows from the two separation steps, taken as plain inequalities.
Commits:

* `9118d28` **Arms/InnerGluing** (new module, proof-only): the facts about the inner family that the
  gluing needs (conditioning, determination from outside, independence of the two families, inner
  positions, sectors read at the inner boundary, the barrier at the inner boundary), and in the new
  module **Arms/TwoSidedGluing**: corridors read only the pairs they need, joining two fences
  through a corridor, the straight two-sided hooks on the four sides, and the two-sided gluing
  through given corridors in disjoint regions.
* `717d8b3` **Arms/TwoSidedGluing** (proof-only): straight two-sided corridors from windows (data,
  geometry, disjoint regions, crossing bound, hook on any side), the two-sided gluing
  `exists_pos_le_law_two_sided` and the conditional corollary.
* this note's commit (docs only).

Gate: §18.9. Sizes: `InnerGluing.lean` 860 lines, 19 theorems; `TwoSidedGluing.lean` 1445 lines,
16 theorems.

### 18.1 The statements proved: the inner family (`Arms/InnerGluing.lean`)

* **Fences.** `HasInnerFence.of_cond_subset` (a fence survives when its colour grows),
  `HasInnerFence.side` (the four sides of the start), `hasInnerFence_iff_of_inter_eq_of_le` (for
  `K ≤ M` the fence is determined by `Icc (a - M) (a + (M + 1))`, `a` the start).
* **Pairs near the inner box.** `IsOpenArm.mem_Icc_of_mem_edges_of_mem`: an edge of an open arm from
  `B_r(z)` with an end in `B_r(z)` has both ends in `Icc (a - 1) (a + 1)` (it is the first edge). For
  dual arms the existing `IsDualArm.exists_mem_edgeSet_of_mem_edges` already says that every crossed
  edge has both ends outside `B_r(z)`.
* **Conditioning** (`innerSeparated_of_mixed_of_forall_mem`, mirror of
  `separated_of_mixed_of_forall_mem`): with `K ≤ M`, `1 ≤ M`, every corridor pair having an end in
  `B_r(z)`, and the corridor pairs inside the box of radius `M + 1` about a possible start `a ∈ B i`
  lying in `D` exactly when arm `i` is dual, a family of arms separated at the inner boundary with
  starts in `B i` stays such a family under the mixed order off the corridors.
  `measurableSet_setOf_innerSeparated_forall_mem`.
* **Determination and independence.** `outerSeparated_of_inter_eq` (the outer family, per family,
  determined by `B_{R + M + K + 1}(z)`), `innerSeparated_of_inter_eq_compl` (the inner family is
  determined by the pairs with both ends outside `B_ρ(z)` when `ρ + M + K + 1 < r`: the arms read
  only pairs with an end outside `B_r(z)`, the fences lie in boxes of radius `M + K + 1` about the
  starts, which lie on the sides), and
  ```lean
  theorem law_inter_eq_mul_of_separated (q) (hrR : r < R)
      (hRR' : R + M + K + 1 + M' + K' + 1 < R') (B B' J) :
      law q (E_out-sep(r, R, s, M, K; ends in B, inner positions in J) ∩
        E_in-sep(R' → ∂Icc lo hi, s', M', K'; starts in B')) =
      law q (first) * law q (second)
  ```
* **Positions at the inner boundary.** `IsArm.snd_mem` (first step), `IsArm.innerPos_cases`: the
  inner position is `10r + 5 + 2z₀ - (2a₀ + [dual])` (top), `6r + 3 + (2a₁ + [dual]) - 2z₁` (right),
  `(2a₀ + [dual]) - 2z₀ + 2r + 1` (bottom), `14r + 7 + 2z₁ - (2a₁ + [dual])` (left);
  `abs_innerPos_sub_le`: arms of one colour starting within `M` of each other have inner positions
  within `2M` when the second is more than `2M + 1` from every doubled corner `m (4r + 2)`.
* **Sectors read at the inner boundary.** `sbtw_innerPos_iff_sbtw_landingPos_of_isArm` (order
  invariance for one more arm of the other colour), `sbtw_innerPos_iff_of_landingPos_eq` (two arms
  with the same landing position start on the same side of two arms of the family), and
  `false_of_landingPos_eq_of_abs_lt` (an arm landing where `γ k` lands cannot start closer to `γ i`,
  of the same colour, than every arm of the other colour).
* **The barrier at the inner boundary** (`notMem_support_of_subset_Icc_start`, mirror of
  `notMem_support_of_mem_Icc`): for a disjoint family of arms from `B_r(z)` to `∂B_{R₃}(z)` in
  counterclockwise order, without packs, with inner positions more than `2M` apart and more than
  `2M + 1` from the corners, `r + M + 1 < R₃`, a walk of the colour of arm `i` from a vertex (face)
  of arm `i`, all of whose points lie within `M` of the start of arm `i`, meets no other arm of that
  colour. Proof: the walk "arm `i` to the walk, the walk, arm `k` from the meeting point", cut at its
  last visit to the start box (`exists_append_eq_of_exists_mem`), is an arm landing where `γ k`
  lands with inner position within `2M` of `γ i`'s. Walk helpers
  `SimpleGraph.Walk.mem_support_dropLast_append(_of_right)`, `Icc_sub_add_subset_cond_Icc`.

### 18.2 The statements proved: the gluing (`Arms/TwoSidedGluing.lean`)

* **Corridors read only the pairs they need.** `mem_Icc_of_map_dualEdge`: the edge crossed by a dual
  edge between two faces of `Icc lo hi` has both ends in `Icc lo (hi + 1)`, an end in `Icc lo hi` and
  an end in `Icc (lo + 1) (hi + 1)`. `cond_mem_crossing_iff_of_agree`: a crossing of either colour is
  determined by the pairs with these three properties (for the open colour: the pairs inside the
  box).
* **Hooks.** `exists_walks_of_fences` (side-independent: a connection to an outer fence, the fence, a
  corridor walk meeting it, an inner fence meeting the corridor walk, and the connection from the
  inner fence to the second arm give a walk `P₁` through the box of radius `M` about `b` and the
  corridor, followed by `P₂` inside the box of radius `M'` about `a'`);
  `exists_walks_two_sided_top/right/bottom/left` (the straight corridor `[x, x + W] × [z₁ + R, z₁ + R']`
  on the top side and its three images, ends and starts not at a corner, both fences spanning the
  columns of the corridor: `b₀ - K ≤ x`, `x + W ≤ b₀ + K`, the same with `a'`, `K'`);
  `exists_walks_two_sided` (any side, from windows).
* **The two-sided gluing through given corridors.**
  ```lean
  theorem law_mul_mul_prod_le_law_of_two_sided (q) (hσ)
      (hKM : K ≤ M) (hM : 1 ≤ M) (hK'M' : K' ≤ M') (hM' : 1 ≤ M')
      (hrM : r + M + 1 < R) (hRR' : R + M + K + 1 + M' + K' + 1 < R') (hR'R₃ : R' + M' + 1 < R₃)
      (hs : 2M + 1 ≤ s) (hs' : 2M' + 2 ≤ s') (B B' J C T Q G) (hCm hCT hCmono)
      (hT : corridor pairs miss the interior of B_R) (hT' : each has an end in B_{R'})
      (hTG hBG hB'G hQG : pairs, boxes about B (radius M + 1), about B' (radius M' + 1), Q in G i)
      (hG : regions pairwise disjoint) (hQloc) (hQin : Q i ⊆ start box of B_{R'} of colour σ i)
      (hB'loc : boxes of radius M' about B' miss Icc (z - R - 1) (z + R)) (hhook) :
      law q (outer-separated at R, ends in B, inner positions in J) *
        law q (inner-separated at R' to ∂B_{R₃}, starts in B') * ∏ i, law q (C i) ≤
      law q (multiArmEventIn σ z r R₃ J fun _ => univ)
  ```
  Proof: Harris for the corridors (`prodBernoulli_prod_le_biInter_of_mixed`), independence
  (`law_inter_eq_mul_of_separated`), conditioning on the intersection of the two families
  (`prodBernoulli_mul_le_inter_of_mixed_of_determined` with `separated_of_mixed_of_forall_mem` and
  `innerSeparated_of_mixed_of_forall_mem`), then `exists_isArm_of_glue` with the continuation
  `P₁ ++ P₂ ++ (second arm from the junction)`. Disjointness of the continuations of two arms of one
  colour: regions (`P₁`, `P₂` lie in `G i`); `P₁` meets an arm `δ k` of the second family only in the
  start box, hence only at its start `a' k ∈ G k`; `P₂` misses `δ k` by the inner barrier; two arms
  of the second family are disjoint, and two open ones cannot share their first vertex since
  `a' i ∈ G i`, `a' k ∈ G k`.
* **Straight corridors from windows.** `exists_two_sided_side` (direction, box
  `Icc lo hi`, region `Icc gl gh` per side; top: box `[x, x + W] × [z₁ + R, z₁ + R']`, region
  `[x - S, x + W + S] × [z₁ + R - M - 1, z₁ + R' + M' + 1]`), `two_sided_side_facts` (all geometric
  hypotheses of the gluing for one corridor), `disjoint_two_sided_regions`,
  `CrossingBounds.le_law_two_sided_side` (`c A` when `R' ≤ R + A W`).
* **The two-sided gluing** (the statement A3b-3 uses):
  ```lean
  theorem exists_pos_le_law_two_sided (σ) (hσ) (c) (A : ℕ) :
      ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ ∀ q L, CrossingBounds q L c → ∀ z r R R' R₃ W M K M' K' S s s' J
        (t : Fin j → Fin 4) (x α β α' β' : Fin j → ℤ),
        1 ≤ W → W ≤ K → K ≤ M → W ≤ K' → K' ≤ M' → M + K + M' + K' + 2 ≤ S →
        2M + 1 ≤ s → 2M' + 2 ≤ s' →
        r + M + 1 < R → R + M + K + 1 + M' + K' + 1 < R' → R' + M' + 1 < R₃ →
        R' ≤ R + A W → W ≤ L →
        (∀ i, β i ≤ x i + K ∧ x i + W ≤ α i + K ∧ β' i ≤ x i + K' ∧ x i + W ≤ α' i + K') →
        (∀ i, corridor [x i, x i + W] at least 2S from the corners of B_R on side t i) →
        (∀ i ≠ k, t i = t k → x i + W + 2S < x k ∨ x k + W + 2S < x i) →
        c₀ * law q (outer-separated at R (s, M, K), ends in (t, α, β), inner positions in J) *
          law q (inner-separated at R' (s', M', K') to ∂B_{R₃}, starts in (t, α', β')) ≤
        law q (multiArmEventIn σ z r R₃ J fun _ => univ)
  ```
  with `c₀ = c A ^ j`. Windows in the format of `exists_pos_le_law_windows_of_moves` (ends at `R`:
  `b₁ = z₁ + R`, `b₀ = z₀ + R`, `b₁ = z₁ - R - [dual]`, `b₀ = z₀ - R - [dual]`; starts at `R'`: the
  same with `R'`, which are the sides of `HasInnerFence`). Non-vacuity, by hand: `j = 1`, `W = K = M
  = K' = M' = 1`, `S = 6`, `s = 3`, `s' = 4`, `r = 0`, `R = 20`, `R' = 27`, `R₃ = 30`, `A = 7`,
  `t = 0`, `x = α = β = α' = β' = z₀` satisfy every hypothesis.
* **The lower half of quasi-multiplicativity modulo separation**:
  ```lean
  theorem exists_pos_mul_le_of_separated_of_separated (σ) (hσ) (c) (A) :
      ∃ c₀ > 0, ∀ q L hCB z r₁ r₂ r₃ R R' W M K M' K' S s s' t x α β α' β' (C₁ C₂ : ℝ≥0∞),
        (the hypotheses above with r := r₁, R₃ := r₃) →
        law q (A(r₁, r₂)) ≤ C₁ * law q (outer-separated at R, ends in (t, α, β)) →
        law q (A(r₂, r₃)) ≤ C₂ * law q (inner-separated at R', starts in (t, α', β')) →
        c₀ * (law q (A(r₁, r₂)) * law q (A(r₂, r₃))) ≤ C₁ * C₂ * law q (A(r₁, r₃))
  ```
  The two separation steps are plain inequalities, not a `…Input` structure (Theorem 11 is A3b-3's).

### 18.3 Decisions (mine, per the standing instruction)

1. **Aligned windows and straight corridors, no bins and no jogs** (deviation from §17.6, step 6).
   The windows of both families on side `t i` must lie inside the fences' reach of one corridor
   `[x i, x i + W]` (`β ≤ x + K`, `x + W ≤ α + K`, and with `K'`). Then one crossing per arm suffices
   and the constant is `c A ^ j`, independent of the window widths. §17.6's bins would need jogs
   (the two families' bins differ) and a factor `(N + 1)^{2j}`; the alignment is cheaper to obtain
   beforehand: the motion plan puts the first family into any prescribed windows, and binning the
   second family's windows to width `≤ 2K' - W` costs `(N + 1)^j` once (§18.4). Same strength for
   A3b-3's purpose.
2. **The inner barrier needs only the walk near the start**: hypothesis "all points of the walk within
   `M'` of the start" (stronger than §17.6's "points inside `B_{R'}` near the start", and all the
   gluing needs: the hook's last piece lies in that box). The corridor part of the continuation meets
   the second family only at its starts, by the start box (no barrier needed there).
3. **Separation hypotheses** `s ≥ 2M + 1` (first family; `exists_isArm_of_glue` needs `> 2M` in
   integers; regions replace the `4M` used before) and `s' ≥ 2M' + 2` (second family; the inner
   barrier needs `> 2M'` apart and `> 2M' + 1` from the corners).
4. **Independence threshold** `R + M + K + 1 + M' + K' + 1 < R'`: the first event lives in
   `B_{R + M + K + 1}(z)`, the second outside `B_ρ(z)` for `ρ + M' + K' + 1 < R'`.
5. **Corridor read sets.** The corridor events are taken determined by the pairs they read, not by
   all pairs of the enlarged box (see §18.5, first item); `T i` = pairs in `Icc lo (hi + δ)` with an
   end in `Icc lo hi` and an end in `Icc (lo + δ) (hi + δ)`.
6. **Mirror conditioning hypothesis**: every corridor pair has an end in `B_{R'}(z)` (then the arms of
   the second family beyond their first step never see the corridors).
7. **Hooks return two walks** (`P₁` through the outer box and the corridor, `P₂` inside the inner
   box), so that the barrier applies to `P₂` alone.
8. **Output** `multiArmEventIn σ z r R₃ J univ`: the inner windows `J` of the first family are carried
   (as in all earlier gluing statements); the landing windows of the second family are not.
9. **The corollary** takes `C₁`, `C₂` and the separated events with `J = univ`; the radii `R ≤ r₂ ≤ R'`
   are not constrained by it (the hypotheses carry them).
10. **Module split**: `InnerGluing.lean` (facts about the inner family, mirrors of `OuterGluing.lean`)
    and `TwoSidedGluing.lean` (corridors, hooks, gluing). No definition; neither `Defs` file touched.
11. **Corner of the inner box**: `innerPos_cases` classifies the dual arm starting at the lower-left
    corner face and stepping left as "bottom" (its position is `0`, not `16r + 8`).

### 18.4 How A3b-3 uses the statements (quasi-multiplicativity, lower half)

Given `r₁ < r₂ < r₃` with large ratios (small ratios by the one-scale bound, §2.2's `∃ r₀`):

1. **First family.** `A(r₁, r₂) ⊆ A(r₁, R₀)` for `R₀ ≈ r₂/8`; Theorem 11's outer half at `R₀` and the
   motion plan (`exists_pos_le_law_target_windows_of_separated`, §17.4) give
   `P(A(r₁, r₂)) ≤ C₁ P(outer-separated at R, ends in prescribed windows (t, α, β), fences (M, K))`
   at some `R ≤ r₂`, with `K ≍ μR` and window width `B ≪ K` (the plan's target width).
2. **Second family.** `A(r₂, r₃) ⊆ A(R', r₃)` for `R' ≈ 2 r₂`; Theorem 11's inner half (to be proved in
   A3b-3, giving `innerSeparatedArmEvent` with starts in windows `θ'` at `R'`) and binning the start
   windows into windows of width `≤ 2K' - W` (`law_le_sum_law_windows_of_separated`-style union, factor
   `(N + 1)^j`, take the largest term) give `P(A(r₂, r₃)) ≤ C₂ P(inner-separated at R', starts in
   (t, α', β'))`.
3. **Alignment.** Choose the plan's targets in step 1 as the bins of step 2 read at `R`
   (`α i, β i` inside `[x i + W - K, x i + K]`, same sides `t i`), `R' - R ≤ A W` with
   `W ≤ min(K, K')`, `S ≥ M + K + M' + K' + 2` and the corridors `2S` from the corners (Theorem 11's
   windows are `≍ ϑR` from the corners, `ϑ ≫ μ`).
4. **Gluing.** `exists_pos_mul_le_of_separated_of_separated` gives
   `c A^j P(A(r₁, r₂)) P(A(r₂, r₃)) ≤ C₁ C₂ P(A(r₁, r₃))`.

The constant depends on `η` (through Theorem 11 and the plan), which is fixed once `σ` and `c` are;
this is allowed for quasi-multiplicativity. The two-sided gluing itself does not depend on `η`.

### 18.5 Errata and observations

* **§17.6 step 3 ("corridors miss the exterior of `B_{R'}` except near the starts") is false for the
  naive read set of a dual corridor.** A dual crossing of the faces `[x, x + W] × [z₁ + R, z₁ + R']`
  is determined by the edges with both ends in `[x, x + W + 1] × [z₁ + R, z₁ + R' + 1]`, which
  include horizontal edges of the row `z₁ + R' + 1`, outside `B_{R'}(z)`, possibly used by an *open*
  arm of the second family (of another index, beyond its first step); the mixed order could close
  them. Fixed by `cond_mem_crossing_iff_of_agree`: the dual crossing reads only edges crossed by dual
  edges between its faces, each with an end in the face box and one in the box shifted by `(1, 1)`,
  hence one in `B_{R'}(z)` on all four sides.
* **Inner positions live on a cycle.** The dual arm starting at the lower-left corner face of the
  ring and stepping left has `innerPos = 0` (`perimeterPos` at the lower-left corner), not the
  left-side formula's `16r + 8`; harmless with the corner separation, but the four-case formula must
  classify it on the bottom side.
* **Two open arms of the second family may share their first vertex only at a corner**; the proof
  avoids the question through the regions (`a' i ∈ G i`).
* **No bins are needed** once the windows are aligned (Decision 1); no plan statement of §2 or
  §14–§17 had to change; no hypothesis beyond `hσ` and the approved small radii was needed.

### 18.6 What remains

* A3b-3: Theorem 11 (outer half assembled from §17.4; the inner half — the inner separation step and
  the inward motion, or a reduction), extendability, quasi-multiplicativity (both halves, the lower
  one by §18.4), the a priori lower bound. Item 5 of §5 is complete.
* A3b-4: half-plane versions and non-centred outer boxes (item 7).

### 18.7 Search

* PercLib, reused: `exists_isArm_of_glue`, `separated_of_mixed_of_forall_mem`,
  `prodBernoulli_mul_le_inter_of_mixed_of_determined`, `prodBernoulli_prod_le_biInter_of_mixed`,
  `prodBernoulli_inter_of_determined`, `mixed_of_determined_of_increasing/decreasing`,
  `measurableSet_setOf_separated_forall_mem_innerPos`, `hasOuterFence_iff_of_inter_eq`,
  `hasInnerFence_iff_of_inter_eq`, `IsArm.of_agree`, `IsDualArm.exists_mem_edgeSet_of_mem_edges`,
  `sbtw_innerPos_iff_sbtw_landingPos`, `sbtw_apply_finRotate_apply`, `sbtw_iff_of_abs_sub_lt`,
  `exists_append_eq_of_exists_mem`, `IsCrossing.eq_of_mem_support_left`, `landingPos_append`,
  `exists_mem_support_of_mem_Icc_of_mem_Icc(_swap)`, `exists_walk_join`,
  `exists_walk_of_mem_support_of_mem_support`, `exists_walk_of_mem_localConn`,
  `mem_Icc_of_mem_dualEdge`, `dualEdgeEquiv`, `mem_crossing_iff_of_inter_eq`,
  `measurableSet_preimage_cond_crossing`, `cond_mem_crossing_of_cond_subset`,
  `CrossingBounds.le_law_box_one/zero`, `disjoint_Icc_of_lt`, `Icc_sub_add_subset_Icc_sub_add_succ`,
  `cond_Icc_subset_cond_Icc`, `isArm_iff_cond`.
* Mathlib: `SimpleGraph.Walk.map_snd_darts`, `cons_tail_support`, `snd_mem_tail_support`,
  `adj_snd`, `support_append_eq_support_dropLast_append`, `List.dropLast_append_of_ne_nil`,
  `List.mem_of_mem_dropLast`, `Sym2.mem_iff`, `ite_eq_left`/`ite_eq_right`, `Finset.prod_le_prod`,
  `ENNReal.pow_pos`.
* Not found (added): the inner-family conditioning, determination from outside and independence of
  the two families, inner positions on the sides, sectors read at the inner boundary, the inner
  barrier, read-set determination of dual crossings, the two-sided gluing.

### 18.8 Lessons

* **`obtain … := h (by decide)` inside `first` does not fail when `decide` fails**: the elaboration
  error is logged and recovered, so `first` keeps the first branch. Use `exact absurd ht (by decide)`
  under `try`, which fails properly.
* **The unused-simp-argument linter aggregates over all runs of one syntax occurrence**: in a uniform
  tactic applied to many goals (`all_goals first | …`), give each `simp only` exactly the union of
  what its runs use.
* `rw [if_pos h, if_pos h]` fails (the first rewrite rewrites both occurrences); `if_pos`/`if_neg`
  are deprecated (`ite_eq_left`/`ite_eq_right`); `Finset.prod_le_prod'` is deprecated
  (`Finset.prod_le_prod`); `mul_le_mul_left'` is not available (`mul_le_mul' le_rfl h`).
* `simp` with `nsmul_eq_mul` turns `(2 • a) 0` into `(2 * a) 0`: add `Pi.mul_apply`, `Pi.ofNat_apply`.
* A `calc` with `law q _` placeholders followed by `ring` fails when the placeholders elaborate to
  terms that differ up to beta (`(fun _ => univ) i` vs `univ`); ascribe the glued inequality's type
  first.
* `lake env lean` on each new module took 4–10 s, `lake build --wfail` 5–12 s.

### 18.9 Gate

`scripts/gate.sh main` **passed on `717d8b3`** (axiom audit 12752 constants, only `propext`,
`Classical.choice`, `Quot.sound`; the interface NOTICE, expected: the classifier names the first
interface file on this branch, `Arms/Defs.lean`; no other notice). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 717d8b354469d738d37cf45ab17af0eab2e19d8a
```

This note's commit changes only `docs/`.


## 19. A3b-3 (2026-11-24): Theorem 11, outer half; extendability outwards; upper half; a priori lower bound

Package A3b-3 = item 6 of §5. **Proved**, for colour sequences without packs
(`hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)`) and uniformly under `CrossingBounds q L c`, with all
constants chosen before `q`, `L`, `z` and the radii and small radii handled by `∃ r₀`:

* **Theorem 11, outer half** (arms landing in the windows of landing data at `∂B_R`), and its
  separated form (separation and fences proportional to `R`);
* **extendability of the outer radius**, `π(r, R) ≤ C π(r, 2R)`;
* **the upper half of quasi-multiplicativity** for all `j ≤ r₁ ≤ r₂ ≤ r₃` (`C = 1`, every law);
* **the a priori lower bound** `π(r, R) ≥ c (r / R)^α`.

**Not proved: the inner half of Theorem 11, the lower half of quasi-multiplicativity and
extendability inwards** (`π(2r, R) ≤ C π(r, R)`). All three need an inner separation step (Lemma 15
at the inner boundary), which does not exist and is a new geometric development (§19.6). Commits
(all proof-only, one new module `Arms/OuterArmSeparation.lean`, 1534 lines, 22 theorems; neither
`Defs` file touched; no `@[tag]`):

* `e38c2c7` **Theorem 11, outer half** (separated form and landing form), the window step, the
  gluing step, target windows, extendability outwards.
* `98a1c10` the arm event across an empty annulus; upper half of quasi-multiplicativity for all
  ordered radii.
* `696c78c` the a priori lower bound.
* this note's commit (docs only).

Gate: §19.9.

### 19.1 The statements proved (`PercLib/Models/Planar/Arms/OuterArmSeparation.lean`)

**Theorem 11, outer half** (plan §2.4 `exists_law_multiArmEvent_le_law_multiArmEventIn` with the
inner windows `univ`; the approved `∃ r₀` of decision 1 of 2026-11-22):

```lean
theorem exists_law_multiArmEvent_le_law_multiArmEventIn_window (σ) (hσ) {η : ℚ} {θ : Fin j → ℚ}
    (hθ : IsLanding η θ) (c) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ q L, CrossingBounds q L c → ∀ z (r R : ℕ), r₀ ≤ r → 2 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤
        C * law q (multiArmEventIn σ z r R (fun _ => univ) (window (16 * R) θ η))
```

**The separated form** (the input of every later gluing): for `n ≥ 1000 (j + 1)²`, with
`u = ⌊R / n²⌋` and `Q = (64 n + 24 j + 24) u`,

```lean
theorem exists_law_multiArmEvent_le_law_outerSeparated (σ) (hσ) (c) {n} (hn : 1000 * (j + 1) * (j + 1) ≤ n) :
    ∃ C ≠ ⊤, ∃ r₀, ∀ q L, CrossingBounds q L c → ∀ z r R, r₀ ≤ r → 7 * r ≤ R → (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤
        C * law q (outerSeparatedArmEvent σ z r R (2 Q - 1) (2 u) u)
```

**Extendability outwards** (plan §2.4 `exists_extendability`, first conjunct):

```lean
theorem exists_law_multiArmEvent_le_law_multiArmEvent_two_mul (σ) (hσ) (c) :
    ∃ C ≠ ⊤, ∃ r₀, ∀ q L, CrossingBounds q L c → ∀ z r R, r₀ ≤ r → r ≤ R → ((2 * R : ℕ) : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤ C * law q (multiArmEvent σ z r (2 * R))
```

**Upper half of quasi-multiplicativity** (plan §2.4 `exists_quasiMultiplicativity`, first conjunct,
with `C = 1` and `r₀ = j`, no crossing bounds needed):

```lean
theorem multiArmEvent_self_eq_univ (σ) (z) (hjr : j ≤ r) : multiArmEvent σ z r r = univ
theorem law_multiArmEvent_le_mul_of_le (q) (σ) (z) (hj : j ≤ r₁) (h₁ : r₁ ≤ r₂) (h₂ : r₂ ≤ r₃) :
    law q (multiArmEvent σ z r₁ r₃) ≤ law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃)
```

`multiArmEvent_self_eq_univ` uses arms of length zero at the heights `z₁ + r - 1 - i` down the left
side (open arms at the vertices `(z₀ - r, y)`, dual arms at the faces `(z₀ - r - 1, y)`), with
landing positions `12 r + 2 (z₁ + r - y) - [dual]`, increasing in `i` (§2.2's remark, now proved).

**The a priori lower bound** (Nolin Prop. 14, lower half; §5 item 6):

```lean
theorem exists_le_law_multiArmEvent_rpow (σ) (hσ) (c) :
    ∃ c₀ α : ℝ, 0 < c₀ ∧ 0 < α ∧ ∃ r₀, ∀ q L, CrossingBounds q L c → ∀ z r R, r₀ ≤ r → r ≤ R →
      (R : ℕ∞) ≤ L → c₀ * ((r : ℝ) / R) ^ α ≤ (law q).real (multiArmEvent σ z r R)
```

The same form as A1's upper bound `exists_law_multiArmEvent_le_rpow` (real-valued law, `rpow`).

**The steps** (statements in full in the file):

* `exists_pos_le_law_window_step` (**the window step**): `c_W P(separated at N, parameters at N) ≤
  P(separated at R, parameters at R, ends in prescribed windows)` for `n³ ≤ N`, `2N ≤ R ≤ 8N`,
  `2r + 2 ≤ N`, windows whose margins, gaps and lengths are at least `Y = (96 n + 24 j + 38) ⌊R / n²⌋`.
  It is `exists_pos_le_law_target_windows` with `A = 32 n² + 2`, plan `n`, bin width `u`, jog bound
  `2 ⌊R / n⌋ + u + 4`, input fences `(2u, u)`, output fences `(2u', u')`, room `Q`. `c_W` depends on
  `σ`, `c`, `n` only, **not on the separation scale `ε`**.
* `exists_pos_le_law_window_step_landing`: the same into the windows of landing data
  (`n = 1000 (j + 1)² (Λ + 1)`).
* `exists_pos_le_law_glue_step` (**the gluing step**): `c_G P(outerSeparatedArmEvent σ z r (2N + 1)
  (4 √ε N) ⌊√ε N⌋ ⌊ε N⌋) ≤ P(separated at R, parameters at R, ends in windows)` for `N ≥ N₁`,
  `r < N`, `4N + 2 ≤ R ≤ 8N + 4`; it is `exists_pos_le_law_target_windows_of_separated` with
  `E = ⌈1 / √ε⌉`, plan `n_g = 32 E n`, bin width `⌊N / P⌋` for an integer `P` built from `E`, `n`, `j`,
  `A = 40 P`. `c_G` depends on `ε`.
* `exists_pos_le_law_outerSeparated` (**the one-scale bound for the separated event**): `c₁ ≤
  P(separated at R)` for `7r ≤ R ≤ 48r` (A3a's one-scale bound at `ρ = 2⌊R/6⌋ + 1`, the outer step with
  `δ = c₀ / 2`, the gluing step).
* `div_le_floor_sqrt_mul`: the real scales of the outer step in integers (`⌊N / E⌋ ≤ ⌊√ε N⌋ ≤ N`,
  `⌊N / E²⌋ ≤ ⌊ε N⌋ ≤ ⌊√ε N⌋`).
* Arithmetic: `window_step_bounds`, `glue_bounds_one/sep/budget/corner/width` (all hypotheses of the
  two motion-plan statements, in integers).
* Windows: `exists_windows_of_ccw` (counterclockwise windows to the plan's format, same ends),
  `exists_bottom_windows` (`j` windows of length `Y` on the bottom side, `2Y` apart, `Y` from the
  corners), `IsLanding.exists_core` (core windows `[a i, a i + μ]` of the circle inside the windows of
  the landing data, inside one side with margin `μ`, `μ = min(η, 1/8) / 8`), `IsLanding.exists_windows`
  (for `R ≥ Λ (Y + 4)`: windows in the plan's format with margins, gaps, lengths `≥ Y`, such that an arm
  ending in window `i`, landing `≥ 4` from the corners, has `landingPos ∈ window (16 R) θ η i`).
* `isArm_nil_left`.

### 19.2 The proof of the outer half (Nolin's induction on scales)

`a(R) = π(r, R)`, `b(R) = P(separated at R with the proportional parameters)`. For `R ≥ 42r + 42`,
`N = ⌊R / 6⌋`, `ρ = 2N + 1`:

* `a(R) ≤ a(ρ)` (monotonicity);
* `a(ρ) ≤ P(sep_ε(ρ)) + δ a(N)` (outer step, probability form);
* `P(sep_ε(ρ)) ≤ c_G⁻¹ b(R)` (gluing step into bottom windows at `R`, then drop the windows);
* `a(N) ≤ C b(N)` (induction) and `b(N) ≤ c_W⁻¹ b(R)` (window step `N → R`, bottom windows).

With `δ = min(c_W, 1) / 2` and `C = 2 (min(c_G, 1)⁻¹ + c₁⁻¹)`: `a(R) ≤ (C / 2 + C / 2) b(R)`. For
`7r ≤ R < 42r + 42`, `a(R) ≤ 1 ≤ c₁⁻¹ b(R)`. Order of constants: `n`, `c_W`, `δ`, `(ε, N₀)`, `(c_G, N₁)`,
`c₁` (with its own `δ`), `C`, then `r₀ ≥ n³, N₀, N₁, r_B + 7`. Landing form: for `R ≥ 28r + 4`,
`a(R) ≤ a(⌊R/4⌋) ≤ C b(⌊R/4⌋) ≤ C c_W⁻¹ P(landing in θ at R)`; for `2r ≤ R < 28r + 4`, the event
is bounded below through the smaller inner box `B_{⌊R/32⌋}` (`multiArmEventTo_subset_of_le`), the
one-scale bound and one window step. A priori bound: `b(2N) ≥ min(c_W, 1/2) b(N)`, so
`b(R) ≥ c₁ (7r / R)^α` with `α = log_{1/2} min(c_W, 1/2)` by induction on `R`.

### 19.3 Decisions (mine, per the standing instruction)

1. **The separated event at every scale has parameters proportional to the radius** in one integer
   unit `u = ⌊R / n²⌋` (fences `(2u, u)`, separation `2Q - 1`, `Q = (64 n + 24 j + 24) u`), with one
   integer `n ≥ 1000 (j + 1)²`. §15.5's real fractions `μ, μ', ϑ` became integers; every hypothesis of
   the plan is then linear in `u`, `u'` with integer coefficients.
2. **Induction on the radius** (`Nat.strong_induction_on`, step `R → ⌊R / 6⌋`) instead of the sum over
   the last good dyadic scale; equivalent, and it uses each step lemma once per level.
3. **Every window step is the full motion plan** (`exists_pos_le_law_target_windows`), with any
   target windows. Intermediate steps target `j` windows on the bottom side
   (`exists_bottom_windows`), which are then dropped: the induction runs on the separated event without
   windows, and the windows of the landing data are reached in one last step. No "core windows" at
   every radius, no re-binning between steps (§15.5's widening/shrinking is not needed).
4. **Core windows of landing data**: two cases by the half of the side containing the midpoint of the
   (shortened) window; margin and length `μ = min(η, 1/8) / 8` of a turn (`IsLanding.exists_core`).
5. **Small ratios**: lower bounds come from a smaller inner box (`T_r(R) ⊇ T_{⌊R/32⌋}(R)`), so the
   one-scale bound for the separated event is needed only for `7r ≤ R ≤ 48r`.
6. **Constants normalised by `min(·, 1)`** (and `min(c_W, 1/2)` for the exponent), so that inverses
   are finite and `α > 0`.
7. **Extendability outwards for `r ≤ R`** (the plan elides the hypotheses); `2R ≤ L`.
8. **The a priori lower bound from the window steps alone**: no quasi-multiplicativity needed. The
   plan's order put it after the lower half; it only needs the outer machinery.
9. **The upper half without `CrossingBounds`**: `C = 1`, `r₀ = j`, every product law.
10. **No new definition**; the separated event of the outer half is `outerSeparatedArmEvent` with
    explicit parameters; window events are written out as in A3b-2b–2f.
11. **The outer step was not changed** (no `J`): Theorem 11's inner windows need the inner half anyway
    (§19.6).

### 19.4 Errata and observations

* **§15.5's window steps with constant independent of `η` hold as designed**, with the motion plan in
  place of A3b-2c's window step; the plan's `B ≥ n + (24 j + 2n + 3) W` (drift) forces target windows
  much longer than the plan's unit, `≍ n W`.
* **For the two-sided gluing (§18.4, step 3)** the first family's windows must be narrower than its
  fences (`β - α ≤ 2K - W`). With the window step's output fences `(2u', u')` and windows of length
  `≥ Y ≍ n u'` this fails: the alignment needs a last stage with large fences, `K' ≥ Y`
  (`exists_pos_le_law_fences_of_windows`, or the plan with `K' ≍ Y`, `M' = 2K'`; the plan allows any
  `K'` with `W + K' ≤ M'` and room `Q ≥ W + 2M + 2K' + 3`). Not done here.
* `π(r, r) = 1` for `j ≤ r` (§2.2's remark, now a theorem); the QM statements with equal radii need no
  extra care.
* No plan statement had to change; no hypothesis beyond `hσ` and the approved `∃ r₀` was needed.

### 19.5 How later packages use the statements

* **U1b / U2a (exponents)**: `exists_le_law_multiArmEvent_rpow` (polynomial lower bounds),
  `exists_law_multiArmEvent_le_law_multiArmEvent_two_mul` (doubling the outer radius),
  `law_multiArmEvent_le_mul_of_le`.
* **QM lower half (§18.4)**: step 1 is now `exists_law_multiArmEvent_le_law_outerSeparated` at
  `R₀ ≈ r₂ / 8` followed by one motion plan into the first family's target windows (with large final
  fences, §19.4); step 2 needs the inner half.
* **A3b-4 (half-plane, non-centred boxes)**: the same assembly with the half-plane strip events; the
  arithmetic lemmas and the induction carry over.

### 19.6 What remains, with a design

**The inner separation step** (Lemma 15 at the inner boundary): on an event `G` of probability
`≥ 1 - δ`, determined by an annulus `B_{c N}(z) \ B_N(z)`, every family of arms from `B_N(z)` to
`∂B_R(z)` (`R ≥ 4N`) can be rerouted near `∂B_N` into a family with the same landing positions (or
at least the same order), separated at the inner boundary with inner fences
(`innerSeparatedArmEvent` at scale `√ε N`).

**Why the outer step does not mirror.** In the outer step the final piece of an arm (after its last
visit to the inner row of the strip of the side where it lands) stays above that row *and inside
`B_R`*, hence in the strip. At the inner boundary the initial piece (from the start to its first
visit to the outer row of the strip of its side) stays below that row but may go *around* `B_N`
(below its top row, beside it): it need not lie in any strip. The "first exit from `B_{2N+1}`" cut
just reproduces the outer step at `∂B_{2N+1}`. Nolin's U-shaped domains (`U^{int}`) are where this is
handled; §3.1 noted they do not remove the interaction with other arms either.

**Proposed routes (a design session first):**

* (I1) **Lemma 15 for a U-shaped domain**: the region `{v : v₁ ≤ z₁ + N + D} \ B_N^∘` around one side,
  crossed from `∂B_N` to the row `z₁ + N + D`; re-prove the exploration of A2 (`Separation.lean`,
  `SeparationSurgery.lean`, `SeparationProtection.lean`, `SeparationEvents.lean`) for this domain. The
  probability side (protection events from fresh pairs) is local and should carry over; the surgery
  needs the U-shape's two arms. Large (A2 was about 4000 lines).
* (I2) **Corner exclusion**: separate only the arms starting in the middle parts of the sides
  (strips over `[z₀ - N + D, z₀ + N - D]`), and show that with probability `≥ 1 - δ` no arm starts
  within `D` of a corner *and* turns the corner (a four-arm-type event in a small box at the corner,
  bounded by the a priori upper bound of A1b: probability `≤ C (D / N)^a`, summed over `O(1)`
  corners). Then every remaining initial piece is a crossing of one strip, and Lemma 15 (reflected,
  `exists_law_separable_ge_aux` at `k = 1`) applies side by side. This looks cheapest; the corner
  estimate must be checked against the arms of the other sides crossing the corner squares.
* (I3) A literature proof with both ends (Damron–Sapozhnikov–Vágvölgyi 2011, separation lemma for
  arms at both ends) — not read; worth checking before (I1).

**Then, Theorem 11 inner half by the reduction through the two-sided gluing** (route (b) of the
mandate; **chosen, reason**: it needs no inward motion plan, which would mirror A3b-2c–2e, about
5000 lines): with `a'(ρ) = π(ρ, R)`, the inner step gives `a'(ρ) ≤ P(inner-sep at ρ) + δ a'(2ρ + 1)`;
bin the starts of the inner-separated family (factor `(N + 1)^j`), and glue it
(`exists_pos_le_law_two_sided`) to a first family from `B_r(z)` with inner positions in the windows
`θ'` and outer ends in windows aligned with the bins, at radius `ρ / 16`; that family has probability
`≥ c c_W^k` for `ρ / r ≍ 2^k` by the window steps of §19.1 carrying `J` (the motion plan carries
`J`; the outer step needs `J`: one line, the rerouted arms keep their inner positions, `hin` in
`exists_separating_event`), plus a one-scale bound with inner windows `θ'` (A3a's corridors from the
windows of `θ'`, on four sides). The sum over levels converges when `δ < c_W`. The full Theorem 11
then follows from the inner half (with outer windows) and the outer half carrying `J = window θ'`.

**QM lower half** by §18.4 with §19.4's large final fences; **extendability inwards** then follows
from the lower half and the one-scale bound: `π(r, 2r) π(2r, R) ≤ C π(r, R)`.

### 19.7 Search

* PercLib, reused: `exists_pos_le_law_target_windows`, `exists_pos_le_law_target_windows_of_separated`,
  `exists_law_multiArmEvent_inter_not_separated_le`, `exists_pos_le_law_multiArmEvent`,
  `multiArmEvent_subset_of_le`, `multiArmEventTo_subset_of_le`, `law_multiArmEvent_le_mul`,
  `outerSeparatedArmEvent_subset_multiArmEvent`, `exists_side_window`, `side_center_eq`,
  `IsArm.exists_landingPos_eq_of_window`, `Icc_subset_Icc_add_one_sub_one`, `isCrossing_nil_iff`,
  `mem_Icc_two_iff`, `mem_multiArmEvent_iff`, `landingPos_true/false`, `perimeterPos`.
* Mathlib: `Nat.lt_div_mul_add`, `Nat.div_mul_le_self`, `Nat.le_div_iff_mul_le`,
  `Nat.lt_of_mul_lt_mul_left`, `Nat.le_of_mul_le_mul_left`, `Nat.floor_le_floor`, `Nat.le_floor`,
  `Nat.cast_div_le`, `Int.le_ceil`, `Int.ceil_lt_add_one`, `Int.floor_le`, `Int.lt_floor_add_one`,
  `Real.logb_pos_of_base_lt_one`, `Real.rpow_logb`, `Real.mul_rpow`, `Real.rpow_le_one`,
  `ENNReal.inv_mul_cancel`, `ENNReal.add_halves`, `ENNReal.add_le_add_iff_right`, `Int.sbtw_iff`,
  `Nat.strong_induction_on`, `SimpleGraph.Walk.penultimate_nil`.
* Not found (added): the scale iteration of Theorem 11, windows inside landing data, `π(r, r) = 1`,
  the a priori lower bound for multi-arm events.

### 19.8 Lessons

* `linarith` over `ℕ` adds nonnegativity only for atoms, not for products: give `Nat.zero_le (x * y)`
  for every monomial that must be dropped.
* `nlinarith` in a large context times out; `linarith` with explicit product facts
  (`Nat.mul_le_mul_left/right`, `Nat.le_mul_of_pos_left/right`) and `ring` identities works. Test the
  arithmetic in a scratch file importing only Mathlib (about 15 s per run).
* The per-declaration heartbeat budget is shared by all `linarith` calls of one proof: split the
  arithmetic into several lemmas (`glue_bounds_*`).
* `h ▸ e` with a large `e` hit the recursion limit; `rw` worked.
* `rw [← hsq]` with `hsq : √ε * √ε = ε` also rewrites the `ε` under `√`.
* `Nat.le_of_mul_le_mul_left` names its multiplier `c`.
* `exact_mod_cast` from an `ℤ` subtraction to its real cast produced `Int.subNatNat`; go through
  `Int.cast_natCast` and `Int.cast_le`.
* The induction compiled at the first attempt once every step was an opaque lemma with its events
  named (`obtain ⟨S, hS⟩ : ∃ S, S = …`).

### 19.9 Gate

`scripts/gate.sh main` **passed on `696c78c`** (axiom audit 12925 constants, only `propext`,
`Classical.choice`, `Quot.sound`; 416 modules in the import closure; the interface NOTICE, expected:
the classifier names the first interface file on this branch, `Arms/Defs.lean`; no other notice).
Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 696c78cb16d0f2e2b1f2ed10c90b7ac0d351b5a3
```

This note's commit changes only `docs/`.

## 20. A3b-3b (2026-11-24): the inner separation step

Package A3b-3b = the rest of item 6 of §5, as set out in §19.6: (1) the inner separation step,
(2) Theorem 11's inner half, (3) the lower half of quasi-multiplicativity, (4) extendability inwards.
**Done: (1), in event form and in probability form.** (2)–(4) are not started; they are the next
package (§20.5). Proof-only; neither `Defs` file touched; no `@[tag]`, no `…Input`, no new
definition. Commits:

* `6682f36` **Arms/SeparationLemma, Arms/InnerSeparationSides, Arms/InnerSeparation** (part 1):
  Lemma 15 in strips of any width (`exists_law_separable_ge_aux_wide`; the old auxiliary statement is
  its `w = 4` instance, byte for byte), the strip event at any position and its determination by a
  finite box, the dual configuration as a measurable bijection of configurations with the same
  crossing bounds, Lemma 15 read through a frame of the dual lattice, and the frame reroute.
* `4d7b581` **Arms/InnerSeparation** (part 2): the four sides, the four frames, corner exclusion,
  the deterministic inner step, `exists_inner_separating_event`,
  `exists_law_multiArmEvent_diff_innerSeparated_le`.
* this note's commit (docs only).

Sizes: `InnerSeparationSides.lean` 724 lines, `InnerSeparation.lean` 2092 lines. Gate: §20.8.

### 20.1 Step 0: the route (decided on paper before any Lean)

**(I3) was checked first.** Damron–Sapozhnikov–Vágvölgyi (arXiv 0806.2425, Ann. Probab. 37 (2009)),
§6, Lemma 6.2 (arm separation with arms constrained to the sides of the inner and the outer annuli,
both ends) give no proof: they cite Kesten (1987, Lemma 4) and Nolin (Theorem 11) and say the same
proof is valid. So (I3) offers nothing for the inner boundary on `ℤ²`.

**The coordinator's concern about (I2) is right as (I2) was stated in §19.6, and it is avoided by a
different corner estimate.** §19.6 proposed to exclude, near each corner, "an arm that starts within
`D` of a corner and turns it". The concern: an arm starting at distance `d` from a corner turns it
within a strip of depth `D` at the cost of a `d × D` crossing, small only for `d ≫ D`, so (I2) seemed to
need two scales (long thin crossings along the sides, and a separate treatment near the corners).
**One estimate suffices:** an arm that turns a corner of `B_ρ(z)` within depth `N` of the strip passes
within `N` of the corner, and continues to `∂B_R(z)`, far away. So it contains a **one-arm event of
its colour from `B_N(κ)` to `∂B_ρ(κ)`** at that corner `κ`. By A1b's a priori upper bound (for
`![true]` and `![false]`) this has probability `≤ C ((N + 1)/(ρ + 1))^a`, small when `ρ/N` is large,
whatever the starting points. Excluding these eight events (four corners, two colours) excludes every
arm from the corner zones: no arm starts near a corner, and no initial piece turns one. The price is
that the strips must be **long and thin** (depth `N ≪` side `2ρ`), whereas Lemma 15 (A2) is for the
strip `4N × N`.

**Lemma 15 in thin strips is cheap.** A2's proof of `exists_law_separable_ge_aux` depends on the width
only through the bound on the number of greedy crossings, `law_exploration_le_pow_of_le h k`, which is
already parametric in the aspect ratio `k` (bound `(1 - c (k + 1))^(u + 1)`); the protection events are
per crossing tip and the deterministic part `separable_of_forall` takes any box. Replacing `h 5` by
`h (w + 1)` and asking `N ≥ w + 1` gives the lemma for width `wN` (`exists_law_separable_ge_aux_wide`).

**The half-unit at the inner boundary.** Reflecting Lemma 15 through a side of `B_ρ(z)` (crossings
running *towards* the inner box) fits open crossings but puts dual crossings one face row inside: any
reflection of `ℤ²` moves faces by one row against vertices (`dualConfig_image_reflect`), so no image of
Lemma 15 under a symmetry of `ℤ²` fits both colours (the §12.4 warning; checked: a reversed reflected
dual crossing may run along the touching layer of faces, and cutting it there loses the fence). **Lemma
15 applied to the dual configuration fits exactly:** with the faces as the vertices of a copy of `ℤ²`,
Lemma 15's open crossings are our dual walks and its dual crossings are our open walks moved by
`(-1, -1)` (`dualConfig_dualConfig`). On the bottom side of `B_ρ(z)`, unreflected, with the strip
`lo = (z₀ - ρ - 1, z₁ - ρ - 1 - N)`, `hi = (z₀ + ρ, z₁ - ρ - 1)` (`k = 0`, width `2ρ + 1 = wN`), the new
dual walks end on the face row `z₁ - ρ - 1` (the faces touching `B_ρ(z)`) and the new open walks on the
row `z₁ - ρ`, both visiting it only at their ends; the fences are exactly the boxes of
`HasInnerFence` (depth `M`, no extra row); the doubled strip columns are the inner positions up to a
constant, and the strip's ends are the corners `0`, `4ρ + 2`. The other sides by frames: top by the
reflection `(x, y) ↦ (x, -y)` of faces (vertices `(x - 1, -y)`), left by the swap (vertices
`(y - 1, x - 1)`), right by the quarter turn `(x, y) ↦ (y, -x)` (vertices `(y - 1, -x)`).

**Conclusion: (I2) with corner exclusion by the one-arm bound, thin strips, Lemma 15 in the dual
lattice.** No hypothesis beyond `hσ` and the small-radius threshold is needed; (I1) (a U-shaped
Lemma 15, about 4000 lines) is avoided.

### 20.2 The statements proved

`Arms/InnerSeparationSides.lean`:

* `exists_law_separable_ge_strip` (`c`, `w ≥ 1`, `δ > 0`): `∃ η ∈ (0, 1], ∃ N₀, ∀ q L, CrossingBounds q L c →
  ∀ lo hi N, hi₀ = lo₀ + wN → hi₁ = lo₁ + N → N₀ ≤ N ≤ L → 1 - δ ≤ law q {Lemma 15 in Icc lo hi, faces
  [lo₀, hi₀ - 1] × [lo₁ - 1, hi₁], families over any finite type}` (the `k = 0` instance at any
  position).
* `mem_separable_strip_of_inter_eq`: that event is determined by the pairs in
  `[lo₀ - M - K - 1, hi₀ + M + K + 1] × [lo₁ - 1, hi₁ + M + 1]` when `lo₁ + M ≤ hi₁`.
* `exists_equiv_dualEdge`, **`exists_measurableEquiv_dualConfig`**: a measurable bijection `Φ` of
  configurations (complement, then every edge relabelled by its dual edge) with `Φ ω ∩ E = dualConfig ω`;
  its pairs in `Icc A B` are determined by the pairs of `ω` in `Icc A (B + 1)`; `(law q).map Φ = law q'`
  with `CrossingBounds q L c → CrossingBounds q' L c`.
* `separable_of_frame`: for `Y` with `Y ∩ E = F false '' dualConfig ω` and
  `dualConfig Y = F true '' (ω ∩ E)`, Lemma 15 for `Y` in `Icc lo hi` reroutes families of walks of `ω`
  whose `F`-images are strip crossings; the conclusions are read through `F` (fence boxes as preimages).

`Arms/InnerSeparation.lean`:

* `IsArm.append_left` (replacing the start of an arm), `exists_append_eq_far` (first visit to the far
  row of a frame; the corner hypothesis concerns only the two columns next to the strip),
  `ArmsDisjoint.of_landingPos_eq` (**the barrier for new starts**: arms with the old landing positions of
  a disjoint ordered pack-free family are disjoint; one application of the sector lemma
  `sbtw_landingPos_iff_of_innerPos_eq`).
* `exists_reroute_of_frame`: the cut, Lemma 15 in the frame, and the new arms (reversed new crossing
  followed by the old arm after its first visit to the far row), with the old landing positions.
* `exists_reroute_inner_bottom`, `_right`, `_top`, `_left`: for arms starting on that side, new arms
  with inner positions `4 √η N` apart and inside the side's interval `[m(4ρ + 2) + 4√ηN,
  (m + 1)(4ρ + 2) - 4√ηN]` (`m = 0, 1, 2, 3` for bottom, right, top, left), and `HasInnerFence ω (σ i) z ρ
  ⌊√η N⌋ ⌊η N⌋`. Needs `1 ≤ N`, `1 ≤ ρ`, `ρ + N + 2 ≤ R`, `1 ≤ √η N` and no arm within `N` of a corner.
* `frame_relations`, `law_frame_apply`, `exists_frame_bottom/top/left/right`.
* `mem_multiArmEvent_one_of_walk`: a walk of colour `c` visiting `B_n(κ)` (faces touching it) and ending
  outside `B_P(κ)`'s interior gives `ω ∈ multiArmEvent ![c] κ n P`.
* `mem_innerSeparatedArmEvent_of_frames`: the deterministic inner step.
* **`exists_inner_separating_event`** (plan item: §5 item 6, inner separation step; §19.6):

```lean
theorem exists_inner_separating_event (σ) (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c) {δ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ w N₀ : ℕ, 7 ≤ w ∧ ∀ q L, CrossingBounds q L c → ∀ z (N ρ : ℕ),
      2 * ρ + 1 = w * N → N₀ ≤ N → (ρ : ℕ∞) ≤ L → ∃ G, MeasurableSet G ∧
        (G determined by the pairs inside B_{2ρ}(z)) ∧ 1 - δ ≤ law q G ∧
        ∀ R, 2 * ρ + 1 ≤ R → ∀ ω ∈ multiArmEvent σ z ρ R ∩ G,
          ω ∈ innerSeparatedArmEvent σ z ρ R (4 * √η * N) ⌊√η * N⌋₊ ⌊η * N⌋₊
```

* **`exists_law_multiArmEvent_diff_innerSeparated_le`** (probability form, same constants,
  `2ρ + 2 ≤ R`): `law q (A(ρ, R) \ innerSeparatedArmEvent …) ≤ δ * law q (A(2ρ + 1, R))`.

The rerouted family keeps the **landing positions** (not only the order): the new arms are the old
arms after their first visit to the far row of the strip.

### 20.3 Decisions (mine, per the standing instruction)

1. **Route (I2) with the one-arm corner estimate** (§20.1), not the two-scale crossing scheme.
2. **Lemma 15 generalised in place to any width** (`exists_law_separable_ge_aux_wide`); the old
   auxiliary statement is kept as its `w = 4` corollary, so no caller changed.
3. **Lemma 15 for the dual configuration**, through a measurable bijection `Φ` of configurations rather
   than the push-forward by `dualConfig` (which is not injective): laws of arbitrary events transport by
   `MeasurableEquiv.map_apply`, so no measurability of Lemma 15's event is needed for its probability.
4. **One generic reroute through a frame**, four side instances generated from one template (frame
   coordinates `F c v` given by two equations; strip box by two equations), instead of four read-back
   lemmas of the side events.
5. **Inner radius `ρ` with `2ρ + 1 = wN`**, `w` odd `≥ 7` chosen from `δ` and the one-arm constants;
   strip depth `N`; corner zones of radius `N`, one-arm events to radius `ρ` (inside `B_{2ρ}(z)`).
   Constants: `w` from `δ` and `c`, then `(η, N₁)` from Lemma 15 with `δ/8`, `N₀ = N₁ + ⌈1/η⌉ + 3`
   (so `√η N ≥ 1`).
6. **Budget** `δ' = min(δ, 1) = 16x`: eight corner events of probability `≤ x`, four side events failing
   with probability `≤ 2x`.
7. **Separation parameters** `s = 4√ηN`, `M = ⌊√ηN⌋`, `K = ⌊ηN⌋` (as in the outer step); `s ≥ 2M + 2`, as
   the two-sided gluing asks, once `√ηN ≥ 1`.
8. **Probability form against `A(2ρ + 1, R)`** (determined outside `B_{2ρ}(z)`), for `2ρ + 2 ≤ R`.
9. **No new definition**; the strip events appear as hypotheses written out (generated text).

### 20.4 Errata and observations

* §19.6's (I2) corner estimate ("a four-arm-type event in a small box at the corner") is not what is
  needed: a one-arm event suffices and is simpler (§20.1); and the coordinator's objection to the
  version "arms that start near a corner and turn it" holds — that event is not small.
* §12.4's half-unit warning is confirmed: no lattice symmetry fits Lemma 15 to the inner boundary for
  both colours; the dual lattice does.
* `HasInnerFence` as defined in §16.2 fits exactly the fences produced (no row added); the definition
  needed no change.
* An arm may run far beside a strip after its initial piece; the cut lemma's corner hypothesis must
  concern only the exit step (the two columns next to the strip), not all points of the arm.
* No plan statement had to change; no hypothesis beyond `hσ` and the approved small-radius threshold.

### 20.5 What remains (package "A3b-3c"), with a design

**Theorem 11, inner half.** The inner step gives, for `a'(ρ) = π(ρ, R)` (fixed `R`),
`a'(ρ) ≤ P(inner-sep at ρ) + δ a'(2ρ + 1)`. To close the induction one needs that extending inner-separated
arms inwards costs at most a constant per scale, i.e. an *inward* window step, which the outer machinery
does not provide; §19.6's reduction avoids it: glue the inner-separated family at `ρ` (starts binned into
windows of width `≤ 2K' - W`, factor `(ρ/K')^j`, a constant of `η`) to a first family from `B_r(z)` with
inner positions in `θ'` and outer ends aligned with the bins (`exists_pos_le_law_two_sided`), the first
family coming from the outer machinery with the inner windows `J = window θ'` carried (the motion plan
carries `J`; the outer step needs `J` added: one line, `hin` of `exists_separating_event`), with large
final fences (§19.4). Design to be fixed in that package: the target statement is the landing-window
form `π(r, R) ≤ C P(A(r, R) with inner positions in window (16 r + 8) θ' η)`, the induction runs over
the inner separation radius `ρ` between `r` and `R`, and the levels sum when `δ < c_W`.

**Lower half of quasi-multiplicativity** by §18.4 with §19.4's large final fences, using the inner step's
separated family at `R' ≈ 2 r₂` directly for step 2 once Theorem 11's inner half (separated form) holds.

**Extendability inwards** `π(2r, R) ≤ C π(r, R)` from the lower half and the one-scale bound
(`π(r, 2r) π(2r, R) ≤ C π(r, R)`, `π(r, 2r) ≥ c`).

Estimated size: one large session (1500–2500 lines).

### 20.6 Search

* PercLib, reused: `law_exploration_le_pow_of_le` (already parametric in the aspect ratio),
  `exists_law_separable_ge_aux` (generalised), `mem_separable_top_of_inter_eq` (adapted),
  `separable_bottom_of_top` (pattern), `exists_law_multiArmEvent_le_rpow` (one-arm bound, both colours),
  `prodBernoulli_map_compl`, `prodBernoulli_map_image_equiv`, `measurable_image_equiv`,
  `law_comp_sym2Map_apply`, `CrossingBounds.swap/.reflect`, `dualConfig_dualConfig`,
  `dualConfig_image_reflect`, `dualConfig_image_swap`, `dualEdgeEquiv`, `dualEdge_map_add`,
  `map_add_one_dualEdge_dualEdge`, `inter_edgeSet_mem_crossing_iff`, `dualConfig_inter_edgeSet`,
  `image_add_mem_crossing_iff`, `inter_edgeSet_mem_localConn_of_image`, `image_sym2Map_inter_edgeSet`,
  `image_sym2Map_mem_iff_of_inter_eq`, `mem_image_dualEdge_of_forall_mem_edges`,
  `exists_append_eq_of_notMem`, `exists_append_eq_of_exists_mem`, `isArm_iff_cond`,
  `IsArm.innerPos_cases`, `IsArm.append_of_append`, `IsDualArm.penultimate_eq`,
  `sbtw_landingPos_iff_of_innerPos_eq`, `sbtw_apply_finRotate_apply`, `landingPos_append`,
  `innerPos_append`, `mem_multiArmEventTo_iff_of_inter_eq`, `measurableSet_multiArmEvent`,
  `measurableSet_of_determined_finite`, `finite_setOf_forall_mem`, `prodBernoulli_inter_of_determined`,
  `multiArmEvent_subset_of_le`, `localConn_mono_set`.
* Mathlib: `Equiv.Perm.subtypeCongr`, `MeasurableEquiv.map_apply`, `measurable_compl`, `Measure.map_map`,
  `tendsto_rpow_neg_atTop`, `tendsto_natCast_atTop_atTop`, `Real.div_rpow`, `Real.rpow_neg`,
  `Real.rpow_le_rpow`, `ofReal_measureReal`, `measure_iUnion_fintype_le`, `ENNReal.mul_div_cancel`,
  `prob_compl_eq_one_sub`, `Set.image_congr`, `Sym2.map_map`, `Sym2.map_comp`, `Set.image_comp`.
* Literature: Damron–Sapozhnikov–Vágvölgyi §6 (no inner-boundary argument, §20.1).
* Not found (added): Lemma 15 in thin strips, the dual configuration as a measurable bijection, the
  inner separation step.

### 20.7 Lessons

* Text-generated side lemmas: write the proof once with the frame coordinates as hypotheses
  (`F c v 0 = …`, `F c v 1 = …`) and close every coordinate goal by `simp only [hF0, hF1, …]; omega`; the
  same script then compiles for all four sides.
* `rw [hF0]` with `hF0 : ∀ c v, F c v 0 = …` rewrites all instances of the first match at once; use
  `simp only [hF0]`.
* `if` conditions rewritten by `simp only [h]` with `h : a = b` lose the shape a negated hypothesis
  about the same condition needs; split the simp calls.
* `(F true).toHom v` and `F true v` are different atoms for `omega`; state `∀ v, (F true).toHom v =
  F true v := fun _ => rfl` and rewrite.
* `Set.mem_setOf_eq`, `if_pos`, `dif_pos`, `cond_true` are deprecated here: `Set.mem_ofPred_eq`,
  `↓reduceIte`, `Bool.cond_true`, `dite_eq_left_of_eq_true`.
* The `show` linter rejects `show` for goals that are not intermediate states; use `change`.

### 20.8 Gate

`scripts/gate.sh main` **passed on `4d7b581`** (full rebuild of the dependants of `SeparationLemma`,
4026 jobs; axiom audit 13136 constants, only `propext`, `Classical.choice`, `Quot.sound`; 418 modules in
the import closure; the interface NOTICE, expected: the classifier names the first interface file on
this branch, `Arms/Defs.lean`; no other notice). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 4d7b5811cacdf6826bfd2843e49c2164ff352cf3
```

A first run on the same commit failed in the build step on an unreadable `.olean` of aesop ("invalid
header"): macOS had evicted files of the worktree (iCloud "Optimize Mac Storage", disk 92% full;
4076 files under `.lake` marked `dataless`). Reading the files restores them (about one second each);
the second run passed. This note's commit changes only `docs/`.

## 21. A3b-3c (2026-11-24): the inner family meets the two-sided gluing; the core of the lower half

Package A3b-3c = the rest of item 6 of §5 as designed in §20.5: (1) Theorem 11's inner half, (2) the
lower half of quasi-multiplicativity, (3) extendability inwards. **Not finished.** Before any Lean, the
route of §20.5 was checked against the statements it composes, and two of its steps do not fit (§21.1);
both were repaired. The package then built the pieces of (2) that do not depend on the arithmetic of the
scales: the inner step with small `η` and its corner events, the two-sided gluing in a form that the
inner step's families satisfy, the reindexing of families by rotations, and the core composite step
(motion plan into aligned windows, then the gluing). What remains of (2) is the binning of the inner
family, the arithmetic and the induction (§21.6); (3) follows from (2) in a few lines; (1) needs (2), (3)
and a one-scale bound with inner windows (§21.6). Proof-only; neither `Defs` file touched; no `@[tag]`,
no `…Input`, no new definition. Commits:

* `02b1797` **Arms/SeparationLemma, Arms/InnerSeparationSides, Arms/InnerSeparation**: `η ≤ 1/256` in
  Lemma 15 and the inner step (statement strengthening; Lemma 15's `η` is `(1/(16·8^J))²`); the inner
  step's statement records that `G` excludes the eight corner one-arm events.
* `c23e8be` **Arms/InnerFamilyGluing** (new module): rotations of the indices; the two-sided gluing with
  regions disjoint by colour.
* `cd1daf1`, `2b5dbc4` **Arms/LowerQuasiMultiplicativity** (new module): the motion plan into aligned
  windows followed by the gluing; choosing the first arm.
* this note's commit (docs only).

Gate: §21.8.

### 21.1 Errata to §20.5 (found on paper, before any Lean)

1. **The inner step's family does not fit `exists_pos_le_law_two_sided`.** That lemma asks the regions
   `G i` of *all* pairs of arms to be disjoint, each `G i` containing the box of radius `M' + 1` about the
   start of arm `i`, with gaps `> W + 2S`, `S ≥ M + K + M' + K' + 2`. The inner step gives inner positions
   `4√ηN` apart, i.e. starts `2√ηN ≈ 2M'` apart (`M' = ⌊√ηN⌋`): the boxes of radius `M' + 1` about two
   neighbouring starts may overlap. Counterexample to the hypotheses: two arms of different colours on
   the bottom side with inner positions `P` and `P + ⌈4√ηN⌉`; any corridors aligned with them are at most
   `2M' + 2K'` apart, less than `W + 2S`. In the proof of `law_mul_mul_prod_le_law_of_two_sided`, the
   disjointness of regions of arms of *different* colours is used only through `hreg` (a pair read by a
   corridor lies in no other arm's region): for the mixed order and for the conditioning sets. That needs
   only (a) the corridors read different pairs, (b) no corridor reads a pair inside the box about an end
   or a start of an arm of the other colour. Arms of one colour are at least `2 · 4√ηN` apart (pack-free,
   `exists_lt_lt_of_eq`), enough for disjoint regions. Fixed by `exists_pos_le_law_two_sided_of_colour`.
2. **Corners.** Straight corridors from `∂B_R` to `∂B_ρ` must stand `2S ≈ 2M'` inside the corners of
   `B_R`, and `ρ - R ≥ S`; so the starts must be about `3M'` from the corners of `B_ρ`, but the inner step
   only guarantees `2√ηN`. Fixed without new probability: `G` already excludes, at each corner `κ` of
   `B_ρ`, the one-arm events of both colours from `B_N(κ)` to `∂B_ρ(κ)`; any arm of any family (the
   rerouted ones too) then starts at least `N` from the corners. The statement of
   `exists_inner_separating_event` now records this conjunct.
3. **`K' ≪ M'` needs `η` small**, which the statements did not say (`η ≤ 1`; with `η = 1`, `M' = K' = N`
   and no gluing fits). Lemma 15's proof takes `η = (1/(16·8^J))² ≤ 1/256`; the three statements now say
   so (`√η ≤ 1/16`, `16 K' ≤ M'`).
4. **The motion plan needs linearly ordered targets** (`lamT` monotone from the lower-left corner) but
   the inner family is only cyclically ordered: its indices are rotated (σ ∘ finRotate^k, pack-free again)
   so that the arm of smallest inner position comes first.

No plan statement is false; no hypothesis beyond `hσ` and the approved small radii is needed.

### 21.2 The route for (2), (3), (1) (decided here; replaces §20.5's order)

**(2) by an induction on `r₂` downward, without Theorem 11's inner half.** For `r₁ ≤ r₂ ≤ r₃`, put
`Φ(r₂) = π(r₁, r₂) π(r₂, r₃)`. Take a valid inner radius `ρ` (`2ρ + 1 = wN`) in `[X, X + w]`,
`X = max(2r₂, K₀ r₁)`. Then `π(r₂, r₃) ≤ π(ρ, r₃) ≤ P(E_far(ρ)) + δ π(2ρ + 1, r₃)` (inner step, probability
form, with `E_far` the inner-separated event with corner distances `≥ 2N + 1`), and
* **step S:** `π(r₁, ⌊ρ/5⌋) · P(E_far(ρ)) ≤ C_S π(r₁, r₃)`: Theorem 11's outer half (separated form) at
  `R₀ = ⌊ρ/5⌋`, then for each bin assignment of the starts of `E_far` (constant number of bins), the motion
  plan into windows aligned with the bins and the gluing with regions disjoint by colour;
* `π(r₁, r₂) ≤ C π(r₁, R')` for `R' ≤ K r₂` (outward extendability at bounded ratio; from the window step,
  which accepts any `R' ∈ [2N, 8N]`, so that `R' ≤ L` suffices).
Hence `Φ(r₂) ≤ C₆ π(r₁, r₃) + δ C₅ Φ(2ρ + 1)`; with `δ = 1/(2C₅)` (chosen before `η`, `w`) the induction
closes; the base (`2ρ + 2 > r₃`) is bounded-ratio extendability. Small `r₂/r₁` are covered by `X ≥ K₀ r₁`
(the one-scale bound for `π(r₁, ·)` at bounded ratio).

**(3) from (2):** `π(r, r') π(r', R) ≤ C π(r, R)` and `π(r, r') ≥ c` for `r ≤ r' ≤ 2r`.

**(1) from (2), (3) and a one-scale bound with inner windows** (not the induction of §20.5): with the
same step S carrying the inner windows `J` (the plan and the gluing carry `J`),
`P(A_J(r, R)) ≥ c P(E_far(ρ)) ≥ c (π(ρ, R) - δ π(2ρ + 1, R)) ≥ (c/2) π(r, R)` for `ρ ≍ r`, using (3) for
`π(2ρ + 1, R) ≤ C π(ρ, R)` and `π(ρ, R) ≥ π(r, R)`. The first family at bounded ratio with inner positions
in `window (16r + 8) θ' η` needs: a one-scale bound with inner windows (straight corridors from the windows
of `θ'` on the four sides; A3a's corridors are on the top side only), the outer step with `J`
(`exists_separating_event` keeps inner positions, `hin`), and the gluing step with `J`. §20.5's induction
over `ρ` would need the same base plus `J`-versions of the window step and of the induction; this route
needs neither.

### 21.3 The statements proved

`Arms/InnerSeparation.lean` (changed statements, proofs adapted; callers unchanged in meaning):

* `exists_law_separable_ge_aux_wide`, `exists_law_separable_ge_strip`: `0 < η ≤ 1/256`.
* `exists_inner_separating_event`: `0 < η ≤ 1/256`, and the new conjunct
  `∀ ω ∈ G, ∀ col κ, (κ₀ = z₀ ± ρ) → (κ₁ = z₁ ± ρ) → ω ∉ multiArmEvent ![col] κ N ρ`.
* helpers `notMem_multiArmEvent_corner_of_notMem`, `one_sub_le_measure_compl_inter` (split out of the
  inner step's proof for the per-declaration heartbeat budget).

`Arms/InnerFamilyGluing.lean`:

* rotations: `val_finRotate_succ`, `sbtw_comp_finRotate`, `sbtw_of_comp_finRotate`,
  `sbtw_comp_finRotate_pow`, `sbtw_of_comp_finRotate_pow`, `comp_finRotate_pow_of_noPack`,
  `ArmsDisjoint.comp_perm`, `ArmsDisjoint.of_comp_perm`, `multiArmEventTo_subset_comp_finRotate_pow`,
  `multiArmEventTo_comp_finRotate_pow_subset`;
* corridor geometry: `mem_Icc_add_one_of_mem_Icc_add_cond`, `disjoint_two_sided_boxes` (read sets of two
  corridors), `disjoint_two_sided_box_of_window` (a corridor misses the box of radius `Mb + 1` about a
  point of another arm's window, at any radius `ρ' ≥ R`);
* **`law_mul_mul_prod_le_law_of_two_sided_of_colour`**: as `law_mul_mul_prod_le_law_of_two_sided` with
  `hG` only for arms of one colour, plus `hTT` (read sets pairwise disjoint), `hTBx`, `hTB'x` (no read pair
  inside the box about an end/start of an arm of the other colour); `hTG` dropped (no longer needed);
* **`exists_pos_le_law_two_sided_of_colour`**: as `exists_pos_le_law_two_sided` (constant `c A ^ j`) with
  the gap hypothesis split: `x i + W + 2S < x k` (or the reverse) for arms of one colour on one side, and
  `x i + W + (M + K + M' + K' + 2) < x k` (or the reverse) for any two arms on one side.

`Arms/LowerQuasiMultiplicativity.lean`:

* `finRotate_pow_val_apply_zero`, **`exists_strictMono_comp_finRotate_pow`** (positions in strict cyclic
  order, pairwise distinct ⇒ some rotation makes them increasing);
* **`exists_pos_mul_le_law_of_plan_two_sided`** (step S's core, abstract parameters):
  `c₀ · P(separated at ∂B_{R₀}, fences (2u, u), inner positions in J) · P(separated at the inner boundary of
  B_ρ, fences (m', k'), starts in [x i, x i + bw] on sides t i) ≤ P(A_J(r, R₃))`, for targets in the plan's
  linear order (`lamT`), with the hypotheses of `exists_pos_le_law_target_windows` (unit `u`, jog bound `D`,
  rooms `Sp`, `Gp`, `Q`, target width `B`, output fences `(M₁, K₁)`) and of
  `exists_pos_le_law_two_sided_of_colour` (corridors `[x i, x i + W]`, `S`, `ρ ≤ R + At W`) passed through.

### 21.4 Decisions (mine, per the standing instruction)

1. **Order (2) → (3) → (1)** instead of (1) → (2) → (3) (§21.2): (2) does not need (1); (1) then needs only
   a bounded-ratio first family.
2. **Repair the gluing, not the inner step**: a variant of the two-sided gluing with regions disjoint by
   colour (the old lemma unchanged), rather than an inward straight gluing that would shrink the inner
   fences (a mirror of `CapGluing`, ~1500 lines).
3. **Statement strengthenings in place** (`η ≤ 1/256`, the corner conjunct): equivalent or stronger, all
   callers adapted in the same commit; the alternative (duplicate lemmas) would copy ~400 lines.
4. **Rotation of indices** for the plan's linear order (reindexing lemmas for any power of `finRotate`).
5. **Step S with abstract parameters** (hypotheses passed through; the reason for their number is stated in
   its docstring); the arithmetic goes in separate lemmas (heartbeats).
6. Bin width `bw = k' - u`, first-family unit `u = ⌊R₀/n²⌋`, `R₀ = ⌊ρ/5⌋`, corridor width `W = u`,
   `K₁ = (2n + 24j + 5)u`, `M₁ = 2K₁`, `B = (2n + 24j + 4)u`, `Q = 2K₁ + 5u + 3`, `S = M₁ + K₁ + m' + k' + 2`,
   `R = ρ - (S + 1)`, `n = 1000 (j+1)² (w+1) E`, `E = ⌈1/√η⌉` (planned for §21.6; not yet in Lean).

### 21.5 Search

* PercLib, reused: `exists_pos_le_law_target_windows`, `law_mul_mul_prod_le_law_of_two_sided` (copied and
  patched), `exists_pos_le_law_two_sided` (copied and patched), `exists_two_sided_side`,
  `two_sided_side_facts`, `disjoint_two_sided_regions`, `CrossingBounds.le_law_two_sided_side`,
  `exists_walks_two_sided`, `disjoint_Icc_of_lt`, `exists_lt_lt_of_eq`, `sbtw_apply_finRotate_apply`,
  `Int.sbtw_iff`, `mem_multiArmEvent_one_of_walk`.
* Mathlib: `finRotate_last`, `coe_finRotate_of_ne_last`, `finCycle_eq_finRotate_iterate`, `finCycle_apply`,
  `Equiv.Perm.coe_pow`, `Equiv.Perm.mul_apply`, `pow_succ`, `pow_succ'`, `sbtw_cyclic_left`,
  `sbtw_cyclic_right`, `Finset.exists_min_image`, `Equiv.apply_symm_apply`, `Equiv.symm_apply_apply`,
  `pow_le_pow_left₀`, `one_div_le_one_div_of_le`.
* Not found (added): rotation invariance of the arm events, the two-sided gluing with regions disjoint by
  colour.

### 21.6 What remains (packages "A3b-3d" and "A3b-3e"), with a design

**A3b-3d: (2) and (3).** In `Arms/LowerQuasiMultiplicativity.lean`:
1. *Bins and the far family.* `E_far(ρ, r₃)` := inner-separated at `ρ` to `∂B_{r₃}` with parameters
   `(4√ηN, m', k')` and `∀ i m, 2N + 1 ≤ |innerPos − m(4ρ + 2)|`; from the inner step's corner conjunct,
   `P(A(ρ, r₃) \ E_far) ≤ δ P(A(2ρ + 1, r₃))` (copy of `exists_law_multiArmEvent_diff_innerSeparated_le`;
   the far property from `mem_multiArmEvent_one_of_walk` applied to the new arms, start in a corner zone ⇒
   one-arm event). Bins on side `t`: `x(t, g) = Z_t − ρ − 1 + g(bw + 1)`, `g < NB = 2wE² + 4`;
   `P(E_far) ≤ Σ_p P(E_far(p))` (`measure_iUnion_fintype_le`).
2. *Per bin assignment* (`mul_measure_le_of_nonempty`): from a witness, inner positions in cyclic order
   (`sbtw_innerPos_iff_sbtw_landingPos`), rotation by `exists_strictMono_comp_finRotate_pow`, then
   `lamT = ⌊P/(4ρ + 2)⌋` monotone, same-side gaps `|Δc| ≥ 2m'` (any) and `≥ 4m'` (one colour, via
   `exists_lt_lt_of_eq`), corners `c ∈ [Z − ρ + N, Z + ρ − N]` (from the far property via
   `IsArm.innerPos_cases`). Reindex both families and the output (`InnerFamilyGluing` rotation lemmas) and
   apply `exists_pos_mul_le_law_of_plan_two_sided` for `σ ∘ finRotate^k` (constants: max over `k : Fin j`).
3. *Arithmetic* (separate lemmas, `linarith` with explicit products, as `window_step_bounds`): with the
   choices of §21.4 item 6 and `⌊N/E⌋ ≤ m' ≤ N/16`, `16k' ≤ m'`, `⌊N/E²⌋ ≤ k'`, `10n²u ≤ wN`
   (`div_le_floor_sqrt_mul` gives the first and third), every plan/gluing quantity is `≤ T = 80nu ≤ (m'+1)/125`,
   which gives the gaps, corners and `ρ − R = S + 1 ≤ At·u` for a constant `At` of `n` (for example
   `At = 3(2n + 24j + 5) + 3 + 20n²`; to be checked).
4. *Bounded-ratio extendability*: `π(r, N) ≤ C π(r, R')` for `r₀ ≤ r ≤ N ≤ R' ≤ 8N`, `R' ≤ L` (window step
   from `⌊R'/2⌋`; small ratios by the one-scale bound), then any bounded ratio by iteration.
5. *The induction* (strong induction on `r₃ − r₂`) and the statement
   `∃ C ≠ ⊤, ∃ r₀, ∀ q L, CrossingBounds q L c → ∀ z r₁ r₂ r₃, r₀ ≤ r₁ → r₁ ≤ r₂ → r₂ ≤ r₃ → r₃ ≤ L →
   π(r₁, r₂) π(r₂, r₃) ≤ C π(r₁, r₃)`; constants in the order `C_ext`, `C₅`, `δ = (2C₅)⁻¹`, `(η, w, N₀)`,
   `n`, `C_S`, `C`, `r₀`.
6. (3): `∃ C r₀, r₀ ≤ r ≤ r' ≤ 2r, r' ≤ R ≤ L → π(r', R) ≤ C π(r, R)` from (2) and
   `exists_pos_le_law_multiArmEvent` (`r' = r` trivial).
Estimated 1000–1300 lines.

**A3b-3e: (1).** One-scale bound with inner windows (four straight corridors families, side versions of
`exists_isArm_of_mem_corridor` by the frame template of A3b-3b), the outer step with `J` (variant of
`exists_separating_event` keeping `innerPos ∈ J`: the rerouted arms keep their inner positions, `hin`),
the gluing step with `J` (the plan carries `J`), step S with `J` (already carried by
`exists_pos_mul_le_law_of_plan_two_sided`), then `P(A_J(r, R)) ≥ (c/2) π(r, R)` as in §21.2. Estimated
800–1200 lines.

### 21.7 Lessons

* A statement change in `SeparationLemma.lean` rebuilds ~600 dependants (full build ~6 min here).
* Adding one conjunct to a proof at the edge of the heartbeat budget broke it twice: split self-contained
  blocks into lemmas (`notMem_multiArmEvent_corner_of_notMem`, `one_sub_le_measure_compl_inter`).
* A bound variable `b` of a set-builder (`∃ a b γ`) silently captures an outer `b : ℕ` in `x i + b`: name
  window widths `bw`.
* Dependent reindexing (`γ (e.symm (e i))` vs `γ i`): rewrite through
  `∀ x y, x = y → f (γ x) = f (γ y)` (`rintro x y rfl; rfl`) and `change`, not `rw` on `γ`.
* `rw [h]` with `h : P (rot^k 0) = …` fails on a `fun`-applied goal: `change` the goal to its beta form first.
* The proof of the two-sided gluing could be patched textually (Python) for the variant: 6 occurrences of the
  region lemma, `hreg` and the two conditioning sets.

### 21.8 Gate

`scripts/gate.sh main` **passed on `2b5dbc4`** (full rebuild of the dependants of `SeparationLemma`; axiom audit
13245 constants, only `propext`, `Classical.choice`, `Quot.sound`; 420 modules in the import closure; the
interface NOTICE, expected: the classifier names the first interface file on this branch, `Arms/Defs.lean`;
no other notice). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 2b5dbc46a18fb6ae829a30165673642668d8eaf6
```

This note's commit changes only `docs/`.

## 22. A3b-3d (2026-11-24): the lower half of quasi-multiplicativity; extendability inwards

Package A3b-3d = items (2) and (3) of §21.2, by the design of §21.6 ("A3b-3d", items 1–6) with the
scales of §21.4 item 6. **Done.** Proof-only; neither `Defs` file touched; no `@[tag]`, no `…Input`, no
new definition. Commits:

* `b68e897` **Arms/InnerFarFamily** (new), **Arms/LowerQuasiMultiplicativity**, **Arms/InnerSeparation**:
  the far inner family (probability form), bins, side data and integer facts of starts in bins; step S
  for one bin assignment; the inner step states that `w` is odd; the rotation of
  `exists_strictMono_comp_finRotate_pow` is at most `j`.
* `b57a34e` **Arms/LowerQuasiMultiplicativity**: step S and the arithmetic of its scales;
  `exists_bin_assignment`.
* `6aacc55`, `61d57b7` **Arms/Extendability** (new): extendability of the outer radius at bounded ratio,
  the induction (lower half of quasi-multiplicativity), extendability of the inner radius.
* this note's commit (docs only).

Sizes: `InnerFarFamily.lean` 460 lines, `LowerQuasiMultiplicativity.lean` 843 (was 170),
`Extendability.lean` 320. Gate: §22.7.

### 22.1 The statements proved, by plan item of §21.6

All for a colour sequence without packs (`hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)`), uniformly under
`CrossingBounds q L c`, with every constant (and the threshold `r₀`) chosen before `q`, `L`, `z` and the
radii.

**Item 1 (bins and the far family)**, `Arms/InnerFarFamily.lean`:

* `far_of_notMem_corner`, **`far_of_isArm`**: a start in none of the four corner zones of radius `N`
  (both colours, the inner step's corner events) has a coordinate at least `N + 1` from both ends of its
  range: `(z₀ - ρ + N + 1 ≤ a₀ ∧ a₀ + N + 1 ≤ z₀ + ρ) ∨ (same for the second coordinate)`.
* **`exists_law_multiArmEvent_diff_far_le`**: as `exists_law_multiArmEvent_diff_innerSeparated_le`, with
  the event `E_far(ρ, R)` = a family separated at the inner boundary (`4√ηN`, `⌊√ηN⌋`, `⌊ηN⌋`) whose
  starts all have the far property: `P(A(ρ, R) \ E_far) ≤ δ P(A(2ρ + 1, R))` for `2ρ + 1 = wN`, `N₀ ≤ N`,
  `2ρ + 2 ≤ R`, `ρ ≤ L`; it also exports `7 ≤ w`, `w` odd, `0 < η ≤ 1/256`.
* `exists_bin`, `exists_mem_bin`, **`exists_bin_assignment`**: every family has an assignment
  `p : Fin j → Fin 4 × Fin NB` of a side and a bin `[X(t, g), X(t, g) + k]`,
  `X(t, g) = Z_t - ρ - 1 + g (k + 1)`, once `NB (k + 1) > 2ρ + 1`.

**Item 2 (per bin assignment)**:

* `exists_side_data` (coordinate `y` along the side and the side's inner-position formula of a far start in
  a bin), `side_facts_single` (margins `V`, `2S` from the ends of the sides of `B_R(z)`, side index
  `(6 - t) % 4`), `side_facts_pair` (side order and gaps from `P₁ + D ≤ P₂`), `le_abs_sub_of_eq_colour`
  (one colour: twice the separation), `floor_sqrt_mul_bounds` (`⌊N/E⌋ ≤ m`, `16 m ≤ N`, `⌊N/E²⌋ ≤ k`,
  `16 k ≤ m`, `4m ≤ 4√ηN`, `2m + 2 ≤ 4√ηN`).
* `outerSeparatedArmEvent_subset_comp_finRotate_pow` (reindexing the first family).
* **`exists_pos_mul_le_law_of_far_bins`** (`Arms/LowerQuasiMultiplicativity.lean`): `c₀ P(outer-separated
  at R₀, fences (2u, u)) P(far family with starts in the windows [x i, x i + k'] of the sides t i) ≤
  π(r, R₃)`, for any `t`, `x`; a witness fixes the cyclic order, a rotation (one of `j + 1`, constant = the
  least of their constants) makes it linear, and the core step `exists_pos_mul_le_law_of_plan_two_sided`
  applies with corridor width `u`, `bw = k'`, `S = M₁ + K₁ + m' + k' + 2`, `R + S + 1 = ρ`. Hypotheses
  passed through (the reason for their number), plus seven inequalities for the bins.

**Item 3 (arithmetic)**: `step_scales`, `step_scales_outer`, `step_products`, `step_bound_S`,
`step_bounds_core`, `step_bounds_budget`, `step_bounds_bins`; and **step S**,
**`exists_law_mul_law_far_le`** (`0 < η ≤ 1/256`, `7 ≤ w`): `∃ C ≠ ⊤, ∃ r₀, … 2ρ + 1 = wN → r₀ ≤ r →
40 r ≤ ρ → 2ρ + 2 ≤ R₃ → R₃ ≤ L → π(r, ⌊ρ/5⌋) P(E_far(ρ, R₃)) ≤ C π(r, R₃)`.

**Item 4 (bounded-ratio extendability)**, `Arms/Extendability.lean`:
`exists_law_multiArmEvent_le_law_multiArmEvent_of_le_eight_mul` (`1 ≤ C`, `r₀ ≤ r ≤ R ≤ R' ≤ 8R`,
`R' ≤ L`) and **`exists_law_multiArmEvent_le_law_multiArmEvent_of_le_pow_mul`** (`R' ≤ 8^k R`).

**Item 5 (the induction)**: **`exists_law_multiArmEvent_mul_law_multiArmEvent_le`**:

```lean
theorem exists_law_multiArmEvent_mul_law_multiArmEvent_le (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r₁ r₂ r₃ : ℕ), r₀ ≤ r₁ → r₁ ≤ r₂ →
      r₂ ≤ r₃ → (r₃ : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r₁ r₂) * law q (multiArmEvent σ z r₂ r₃) ≤
        C * law q (multiArmEvent σ z r₁ r₃)
```

(the target statement of the mandate, unchanged). Helpers `measure_le_add_of_diff_le`,
`mul_le_of_induction_step`.

**Item 6 (extendability inwards)**: **`exists_law_multiArmEvent_le_law_multiArmEvent_of_le_two_mul`**:
`∃ C ≠ ⊤, ∃ r₀, … r₀ ≤ r → r ≤ r' → r' ≤ 2r → r' ≤ R → R ≤ L → π(r', R) ≤ C π(r, R)`; and Nolin's form
`exists_law_multiArmEvent_two_mul_le_law_multiArmEvent` (`2r ≤ R ≤ L`, `π(2r, R) ≤ C π(r, R)`).

### 22.2 The proof of the lower half

Fix `r₁`, `r₃` and induct on `r₃ - r₂`. With `X = max(2r₂, 40r₁)`, `w = 2a + 1`, `mX = ⌊X/w⌋`,
`N = 2mX + 3` and `ρ = w·mX + w + a`, one has `2ρ + 1 = wN` and `X < ρ ≤ X + 2w`; `N ≥ N₀` from
`r₁ ≥ wN₀`. If `r₃ < 2ρ + 2`, then `r₃ ≤ 81 r₂`, and `Φ(r₂) ≤ π(r₁, r₂) ≤ C_b π(r₁, r₃)`. Otherwise
`π(r₂, r₃) ≤ π(ρ, r₃) ≤ P(E_far) + δ π(2ρ + 1, r₃)`; `π(r₁, r₂) ≤ C_b π(r₁, ⌊ρ/5⌋)` (monotonicity if
`⌊ρ/5⌋ ≤ r₂`, bounded-ratio extendability otherwise, ratio `≤ 9`) and `π(r₁, r₂) ≤ C_b π(r₁, 2ρ + 1)`
(ratio `≤ 81`); step S and the induction hypothesis at `2ρ + 1` give
`Φ(r₂) ≤ C_b C_S π(r₁, r₃) + δ C_b C π(r₁, r₃) ≤ C π(r₁, r₃)` with `δ C_b = 1/2`, `C = 2 C_b C_S + C_b`.
Step S: Theorem 11's outer half (separated form) at `R₀ = ⌊ρ/5⌋ ≥ 8 r₁`; `E_far ⊆ ⋃_p E_far(p)` over
the `(4NB)^j` bin assignments; for each, `exists_pos_mul_le_law_of_far_bins`.

### 22.3 Decisions (mine, per the standing instruction)

1. **The far property on the start coordinates** (at least `N + 1` from both ends of the side) instead of
   §21.6's `2N + 1 ≤ |innerPos − m(4ρ + 2)|`: it is what the corner events give directly
   (`mem_multiArmEvent_one_of_walk` at the start), and what the margins need; equivalent up to constants.
2. **`w` odd exported** by `exists_inner_separating_event` and `exists_law_multiArmEvent_diff_innerSeparated_le`
   (statement strengthening in place; the width was `2(w₁ + w₂ + 4) + 1` already): without it
   `2ρ + 1 = wN` may have no solution and the induction could not choose `ρ`.
3. **The rotation is at most `j`** in `exists_strictMono_comp_finRotate_pow` (strengthened in place, no
   caller): the per-bin constant is the least of the `j + 1` rotated core constants.
4. **Bins**: width `k + 1` with `bw = k' = k = ⌊ηN⌋` (not `k' - u`: the core needs only `bw ≤ k'`),
   `NB = wE²` (not `2wE² + 4`: `N < E²(k + 1)` already gives `2ρ + 1 < NB(k + 1)`), `E = ⌈1/√η⌉`.
5. **Scales** as §21.4 item 6 with `bw = k`, `Ap = 32n² + 2`, `At = 4n² + 6n + 72j + 15` (checked:
   `S + 1 ≤ At·u`), `R₀ = ⌊ρ/5⌋`, `Rn = ⌊R/n⌋`, `D = 2Rn + u + 4`, `Sp = 7u + 2D + 3`, `Gp = Sp + 24ju`,
   `Q = 2K₁ + 5u + 3`; step S asks `40 r ≤ ρ` and `r₀ = max(r₁, n³ + wE² + 1)` (so `ρ ≥ 5n³`, `N ≥ E²`).
   The arithmetic is seven lemmas (per-declaration heartbeats), linear in the atoms `n u`, `j u`, `j² u`,
   `j Rn`, `n Rn`, `n² u` with the product facts given explicitly.
6. **Bounded-ratio extendability via the window step from `⌈R'/8⌉`** (only `R' ≤ L`), iterated to `8^k`;
   one constant `C_b` (ratio `8³`) for both extensions in the induction.
7. **The induction's inner radius** `ρ ∈ (X, X + 2w]` from `mX = ⌊X/w⌋` (no search over `N`).
8. **Module split**: `InnerFarFamily` (item 1 and the integer facts), `LowerQuasiMultiplicativity` (items
   2–3), `Extendability` (items 4–6).
9. **No definition**; the far event is written out in the three statements that use it.

### 22.4 Errata and observations

* §21.6 item 1's bin count `2wE² + 4` and width `k' - u` are not needed (decision 4); no statement changed.
* The inner step did not export that `w` is odd (decision 2); a statement of the form
  `∀ N ρ, 2ρ + 1 = wN → …` with an even `w` would be vacuous, so the export is needed by any caller that
  must produce a `ρ`.
* The design's `Φ(r₂) ≤ C₆ π(r₁, r₃) + δ C₅ Φ(2ρ + 1)` holds with `C₅ = C_b` (ratio `≤ 81`) and
  `C₆ = C_b C_S`; `⌊ρ/5⌋` may lie below or above `r₂` (both handled).
* No plan statement is false; no hypothesis beyond `hσ` and the approved small radii was needed.

### 22.5 Search

* PercLib, reused: `exists_pos_mul_le_law_of_plan_two_sided`, `exists_strictMono_comp_finRotate_pow`,
  `comp_finRotate_pow_of_noPack`, `sbtw_comp_finRotate_pow`, `ArmsDisjoint.comp_perm`,
  `multiArmEventTo_comp_finRotate_pow_subset`, `exists_inner_separating_event`,
  `mem_multiArmEvent_one_of_walk`, `isArm_iff_cond`, `IsArm.innerPos_cases`,
  `sbtw_innerPos_iff_sbtw_landingPos`, `exists_lt_lt_of_eq`, `div_le_floor_sqrt_mul`,
  `exists_law_multiArmEvent_le_law_outerSeparated`, `exists_pos_le_law_window_step`,
  `exists_bottom_windows`, `exists_pos_le_law_multiArmEvent`, `multiArmEvent_subset_of_le`,
  `mul_measure_le_of_nonempty` (MotionPlan; a duplicate was written and removed),
  `prodBernoulli_inter_of_determined`.
* Mathlib: `measure_le_inter_add_sdiff`, `measure_union_le`, `measure_iUnion_fintype_le`,
  `Finset.exists_min_image`, `Finset.mul_sum`, `Fintype.card_fun`, `Fintype.card_prod`,
  `Nat.lt_div_mul_add`, `Nat.div_mul_le_self`, `Nat.le_div_iff_mul_le`, `Nat.div_lt_iff_lt_mul`,
  `Nat.lt_of_mul_lt_mul_left`, `Nat.le_of_mul_le_mul_left`, `Int.toNat_of_nonneg`, `ite_eq_left`,
  `ite_eq_right`, `ENNReal.inv_two_add_inv_two`, `ENNReal.mul_inv`, `Nat.strong_induction_on`,
  `one_le_pow₀`.
* Not found (added): the far inner family, bins of arm starts, step S, bounded-ratio extendability with
  only the larger radius below `L`, the lower half of quasi-multiplicativity, extendability inwards.

### 22.6 Lessons

* `omega` on a goal that is a disjunction of four conjunctions, in a large context, ran for more than ten
  minutes of wall-clock without a heartbeat error (the build had to be stopped); choose the disjunct
  explicitly and keep such steps in small lemmas (`exists_bin_assignment`).
* `gcongr` on `μ {ω | ∃ a b γ, …} ≤ μ {ω | ∃ a b γ, …}` descends into the set-builder with the same
  witnesses; for reindexed families use `mul_le_mul'` and `measure_mono` with the goals left explicit.
* `if_pos`/`if_neg` are deprecated (`ite_eq_left`/`ite_eq_right`); `Set.diff_union_self`,
  `measure_le_inter_add_diff` are deprecated (`sdiff` names).
* Linear arithmetic over `ℕ` with the scale definitions as equations (not `subst`) and products as atoms
  (`n * u`, `j * u`, …) stays within the heartbeat budget; the unused-variables linter then names the
  hypotheses the arithmetic did not need.
* `rw [mul_assoc, Finset.mul_sum]`, not `rw [Finset.mul_sum, mul_assoc]`, for `(C * a) * ∑ = C * ∑ a * f`.

### 22.7 Gate

`scripts/gate.sh main` **passed on `61d57b7`** (axiom audit 13480 constants, only `propext`,
`Classical.choice`, `Quot.sound`; 422 modules in the import closure; the interface NOTICE, expected: the
classifier names the first interface file on this branch, `Arms/Defs.lean`; no other notice). A first run on
`6aacc55` was stopped after its build step to replace a hand proof by mathlib's `measure_le_inter_add_sdiff`
(`61d57b7`). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on 61d57b799e4bf06bc0ecf56ec00ee804afa19e7f
```

This note's commit changes only `docs/`.

## 23. A3b-3e (2026-11-24): Theorem 11, inner half; Theorem 11 at both ends for large ratios

Package A3b-3e = item (1) of §21.2, by the design of §21.6 ("A3b-3e"). **Done**, and item 6 of §5
(Theorem 11) is complete except for windows at **both** ends at aspect ratios `2 ≤ R / r < 32` (design
in §23.6). Proof-only; neither `Defs` file touched; no `@[tag]`, no `…Input`, no new definition.
Commits:

* `a45b2cc` **Arms/InnerWindows** (new): straight corridors on the four sides in counterclockwise
  coordinates; the one-scale bound with inner windows.
* `935953c` **Arms/OuterSeparation, Arms/OuterArmSeparation, Arms/InnerWindows,
  Arms/LowerQuasiMultiplicativity**: the outer step, the window step, the gluing step and step S keep
  inner windows `J`; separated arms from inner windows at one scale.
* `ce6bd27` **Arms/InnerArmSeparation** (new): Theorem 11's inner half; the separated form at the
  inner end; extendability of the inner radius at bounded ratio.
* `ca935e6` **Arms/OuterArmSeparation, Arms/InnerArmSeparation**: the window step into landing windows
  keeps `J`; the separated form of the outer half with inner windows; Theorem 11 with windows at both
  ends for `32 r ≤ R`.
* this note's commit (docs only).

Sizes: `InnerWindows.lean` 582 lines, `InnerArmSeparation.lean` 465 lines. Gate: §23.8.

### 23.1 The statements proved, by plan item of §21.6 ("A3b-3e")

All for a colour sequence without packs (`hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)`), uniformly
under `CrossingBounds q L c`, with every constant (and the threshold `r₀`) chosen before `q`, `L`,
`z` and the radii. Inner windows are `window (16 r + 8) θ η` (the cycle of inner positions has
perimeter `16 r + 8`).

**Item 1 (one-scale bound with inner windows on all four sides)**, `Arms/InnerWindows.lean`:

* `exists_isCrossing_of_mem_crossing`: a crossing of a box in direction `d`, in either orientation
  (`S` on the side `lo d` and `T` exited on `hi d`, or the reverse), contains a crossing walk inside
  the box (generalises A3a's `exists_isCrossing_of_mem_crossing_one`).
* `exists_ccw_corridor` (the box of a straight corridor on the side `m` — `0` bottom, `1` right,
  `2` top, `3` left — at counterclockwise coordinates `[Y, Y + W]`, faces for the dual colour, as in
  `exists_two_sided_side`), **`exists_isArm_of_mem_ccw_corridor`** (the side version of A3a's
  `exists_isArm_of_mem_corridor`, all four sides and both colours in one statement: an arm inside the
  box with `innerPos ∈ [m(4r + 2) + 2Y, m(4r + 2) + 2(Y + W) + 2]` and
  `landingPos ∈ [4mR + 2(Y + R - r) - 1, 4mR + 2(Y + W + R - r) + 1]`, for `1 ≤ Y`, `Y + W + 1 ≤ 2r`),
  `CrossingBounds.le_law_ccw_corridor`, `disjoint_ccw_corridors` (read sets `Icc lo (hi + 1)`).
* `ccw_core_bounds`, `ccw_core_gap`: the corridor `Y = ⌈(a - m/4)(16r + 8)/2⌉`, `W = ⌊r / n⌋`
  (`n μ ≥ 1`) inside the core window `[a, a + μ]` of `IsLanding.exists_core` has margins `≥ 2`, its
  inner positions in the window of the landing data, and corridors of one side are more than `W + 1`
  apart.
* **`exists_pos_le_law_multiArmEventIn_window_inner`**: `∃ c₀ > 0, ∃ r₀, … r₀ ≤ r → r < R → R ≤ K r →
  R ≤ L → c₀ ≤ P(multiArmEventIn σ z r R (window (16 r + 8) θ η) univ)` (`c₀ = c(2Kn)^j`, `r₀ = 16n`;
  no pack-freeness needed).
* **`exists_pos_le_law_outerSeparated_inner`**: as `exists_pos_le_law_outerSeparated` (`7r ≤ R ≤ 48r`)
  with the inner positions in `window (16 r + 8) θ η`.

**Item 2 (the outer step and the gluing step with `J`)**:

* `exists_separating_event` **strengthened in place**: for every `r < N` and **all windows `J`**,
  `A_J(r, R) ∩ G ⊆ {separated arms with the same parameters and inner positions in J}` (the rerouted
  arms keep their inner positions, `hin`); the old conclusion is its `J = univ` instance.
  `exists_law_multiArmEventIn_diff_separated_le` (new, the probability form with `J`);
  `exists_law_multiArmEvent_inter_not_separated_le` is now derived from it (statement unchanged).
* `exists_pos_le_law_glue_step_inner`, `exists_pos_le_law_window_step_inner`,
  `exists_pos_le_law_window_step_landing_inner` (new; the old three are their `J = univ` corollaries,
  statements unchanged). The gluing step with `J` takes the radius `ρ` with `ρ = 2N + 1`.

**Item 3 (step S with `J`)**, `Arms/LowerQuasiMultiplicativity.lean`:

* `exists_pos_mul_le_law_of_far_bins` **strengthened in place**: windows `J` for the first family,
  output `multiArmEventIn σ z r R₃ J univ` (the rotation reindexes `J`;
  `setOf_outerSeparated_subset_comp_finRotate_pow` replaces `outerSeparatedArmEvent_subset_comp_finRotate_pow`).
* **`exists_law_mul_law_far_le_inner`**: `∃ C < ⊤, ∃ n ≥ 1000(j + 1)², ∃ r₀, … 2ρ + 1 = wN → R₀ = ⌊ρ/5⌋ →
  r₀ ≤ r → 40r ≤ ρ → 2ρ + 2 ≤ R₃ ≤ L → P(first family at R₀, separated with (2Q - 1, 2u, u),
  u = ⌊R₀/n²⌋, inner positions in J) · P(far inner family at ρ) ≤ C P(A_J(r, R₃))`;
  `exists_law_mul_law_far_le` (statement unchanged) is its corollary with Theorem 11's outer half.

**Item 4 (Theorem 11, inner half)**, `Arms/InnerArmSeparation.lean`:

* `le_two_mul_of_le_add_inv_two_mul` (`x ≤ F + x/2`, `x < ⊤` ⇒ `x ≤ 2F`);
  `exists_law_multiArmEvent_le_law_multiArmEvent_of_le_mul` (extendability inwards at any bounded
  ratio `K`, `1 ≤ C`).
* **`exists_law_multiArmEvent_le_law_multiArmEventIn_window_inner`**:

```lean
theorem exists_law_multiArmEvent_le_law_multiArmEventIn_window_inner (σ : Fin j → Bool)
    (hσ : j ≤ 1 ∨ ∀ i, σ i ≠ σ (finRotate j i)) {η : ℚ} {θ : Fin j → ℚ} (hθ : IsLanding η θ)
    (c : ℕ → ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ r₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (r R : ℕ), r₀ ≤ r → 2 * r ≤ R →
      (R : ℕ∞) ≤ L →
      law q (multiArmEvent σ z r R) ≤
        C * law q (multiArmEventIn σ z r R (window (16 * r + 8) θ η) fun _ => univ)
```

  (the mandate's `P(A_J(r, R)) ≥ (c/2) π(r, R)`, with `C = 2 min(c₁, 1)⁻¹ C_S + c₂⁻¹`).
* **The separated form at the inner end**, `exists_law_multiArmEvent_le_law_innerSeparated`:
  `∃ 0 < η ≤ 1, ∃ w N₀, 7 ≤ w, w odd, … 2ρ + 1 = wN → N₀ ≤ N → 2ρ + 2 ≤ R ≤ L →
  π(ρ, R) ≤ 2 P(innerSeparatedArmEvent σ z ρ R (4√ηN) ⌊√ηN⌋ ⌊ηN⌋)` — at the radii of the inner step
  (they are `≍` every radius up to the factor `w`; with extendability inwards this is the separated
  form at every inner radius up to a constant and a bounded change of radius).

**Theorem 11 at both ends** (the mandate's last item):

* `exists_law_multiArmEvent_le_law_outerSeparated_inner` (the separated form of the outer half with
  inner windows): `π(r, R) ≤ C P(separated at ∂B_R, (2Q - 1, 2u, u), inner positions in
  window (16 r + 8) θ η)` for `r₀ ≤ r`, `7r ≤ R ≤ L` — separation at the outer end and windows at
  the inner end.
* **`exists_law_multiArmEvent_le_law_multiArmEventIn_windows`**: `π(r, R) ≤ C P(multiArmEventIn σ z r R
  (window (16 r + 8) θ' η) (window (16 R) θ η))` for `r₀ ≤ r`, **`32 r ≤ R`**, `R ≤ L` (plan §2.4's
  `exists_law_multiArmEvent_le_law_multiArmEventIn` at large ratio; `2r ≤ R < 32r` open, §23.6).

### 23.2 The proofs

**Inner half.** With `ρ ∈ (40r, 40r + 2w]`, `2ρ + 1 = wN` (as in §22.2): if `R < 2ρ + 2` then
`R ≤ 81 r` and the one-scale bound with inner windows gives `π ≤ 1 ≤ c₂⁻¹ P(A_J)`. Otherwise
`π(r, R) ≤ π(ρ, R) ≤ P(E_far) + δ π(2ρ + 1, R)` and `π(2ρ + 1, R) ≤ C_b π(r, R)` (QM lower half and
the one-scale bound, ratio `≤ 90`), so `π(r, R) ≤ 2 P(E_far)` with `δ C_b = 1/2`; then
`min(c₁,1) P(E_far) ≤ P(sep_J at ⌊ρ/5⌋) P(E_far) ≤ C_S P(A_J(r, R))` (one-scale separated bound with
inner windows, `8r ≤ ⌊ρ/5⌋ ≤ 48r`; step S with `J`). No induction over scales.

**Separated form of the outer half with inner windows.** Nolin's induction (§19.2) with `J` carried
by the outer step, the gluing step and the window step; the outer step's error term `δ π(r, N)`
has no `J`, so the left side is `π(r, R)` and the induction passes through the inner half:
`π(r, R) ≤ π(r, ρ) ≤ C_in P(A_J(r, ρ)) ≤ C_in (P(S_J(ρ)) + δ π(r, N))` with
`π(r, N) ≤ C b_J(N) ≤ C c_W⁻¹ b_J(R)`; `δ = (2 C_in c_W⁻¹)⁻¹`, so `C = 2(C_in c_G⁻¹ + c₁⁻¹)`.

**Both ends.** `π(r, R) ≤ π(r, ⌊R/4⌋) ≤ C₁ b_J(⌊R/4⌋) ≤ C₁ c_L⁻¹ P(A_{J,I}(r, R))` (window step with
`J` into the landing windows, `n` of the landing data).

### 23.3 Decisions (mine, per the standing instruction)

1. **Corridors in counterclockwise coordinates** `(m, Y)` (side of the cycle of inner positions,
   distance from the corner where the side begins), one statement for the four sides and both colours
   (case split inside, `omega`), instead of four generated side lemmas: the corridor lemma needs no
   frame, only coordinates; the boxes are those of `exists_two_sided_side` re-indexed.
2. **Variants with `J` as the primary statements, the old names as corollaries** (`_inner` suffix) for
   the gluing step and the two window steps; **in-place strengthening** for `exists_separating_event`
   (one caller) and `exists_pos_mul_le_law_of_far_bins` (one caller). No statement weakened; every
   existing caller unchanged in meaning.
3. **Step S with `J` exposes `n`** (`∃ n ≥ 1000(j + 1)²`) and takes the first family's separated event
   itself, not `π(r, R₀)`: the inner half supplies that event's lower bound at one scale; the old step
   S uses Theorem 11's outer half.
4. **Extendability inwards by quasi-multiplicativity and the one-scale bound** at ratio `≤ 90`
   (`exists_law_multiArmEvent_le_law_multiArmEvent_of_le_mul`), one step instead of iterating the
   ratio-2 statement.
5. **Inner radius** `ρ = w⌊40r/w⌋ + w + (w - 1)/2` (as §22.3 item 7 with `X = 40 r`).
6. **The separated form at the inner end at the radii of the inner step** (`2ρ + 1 = wN`), constant 2.
7. **Both ends for `32 r ≤ R` only** (§23.6 for smaller ratios).
8. **Normalised constants** `min(·, 1)`, `max(·, 1)` as before; no definition.

### 23.4 Errata and observations

* §21.2's "inner half at bounded ratio" needs no induction: a single inner step at `ρ ≍ r` plus
  extendability inwards suffices, as designed; confirmed.
* The outer half's separated form **with** inner windows cannot be proved by the outer induction alone:
  the outer step's error term is `δ π(r, N)` without windows, so the induction needs the inner half.
  The order is therefore inner half → outer half with `J` → both ends.
* **Both ends at small ratios do not follow from the outer half and the gluing**: the window step
  needs separated arms at a radius `N ≥ 7r` with `2N ≤ R`, i.e. `R ≥ 14r`; the outer half avoided
  this by shrinking the inner box (`B_{⌊R/32⌋}`), which windows at the inner end forbid.
* No plan statement is false; no hypothesis beyond `hσ` and the approved small radii was needed.
* **Environment.** During the last builds macOS evicted up to ~38600 files of the worktree
  (`.hash`, `.trace`, `.olean`, `.ilean`, the IR files, Mathlib sources). Lake then blocks at ~0 % CPU
  on a read, or fails with `time expired (error code: 60, connection timed out)` and reports
  `Running Mathlib.…` / `bad import` for modules whose files it could not read (no Lean error). The
  re-materialisation line with `xargs -P 32` restored ~10 files/s (8 readers: ~0.3 files/s); the
  `.olean`, `.trace` and `.lean` files first, then the rest. A waiter `until ! pgrep -f '<pattern>'`
  must not contain its own pattern in its command line (it waits on itself).

### 23.5 Search

* PercLib, reused: `exists_two_sided_side` (box format), `cond_mem_crossing_iff_of_agree`,
  `mem_Icc_add_one_of_mem_Icc_add_cond`, `measurableSet_preimage_cond_crossing`,
  `CrossingBounds.le_law_box_one/zero`, `disjoint_Icc_of_lt`, `isArm_iff_cond`,
  `IsArm.innerPos_cases`, `IsArm.landingPos_eq_of_top/right/bottom/left`,
  `Icc_subset_Icc_add_one_sub_one`, `IsLanding.exists_core`, `IsLanding.exists_windows`,
  `exists_bottom_windows`, `prodBernoulli_iInter_fin_of_determined`, `localConn_comm`,
  `mem_localConn_iff_exists_walk`, `exists_append_eq_of_notMem`, `exists_append_eq_of_exists_mem`,
  `multiArmEventIn_subset_multiArmEvent`, `multiArmEventTo_comp_finRotate_pow_subset`,
  `exists_law_multiArmEvent_diff_far_le`, `exists_law_multiArmEvent_diff_innerSeparated_le`,
  `exists_law_multiArmEvent_mul_law_multiArmEvent_le`, `exists_pos_le_law_multiArmEvent`,
  `measure_le_add_of_diff_le`.
* Mathlib: `Int.le_ceil`, `Int.ceil_lt_add_one`, `Nat.le_ceil`, `Nat.one_le_ceil_iff`,
  `Nat.div_mul_le_self`, `Nat.lt_div_mul_add`, `Nat.le_div_iff_mul_le`, `le_mul_of_one_le_right`,
  `mul_le_mul_of_nonneg_left/right`, `Int.sbtw_iff`, `ENNReal.add_le_add_iff_right`,
  `ENNReal.inv_two_add_inv_two`, `ENNReal.mul_inv`, `Finset.prod_le_prod`.
* Not found (added): crossing walks in either orientation, straight corridors on every side with
  inner positions, the one-scale bound with inner windows, the inner half of Theorem 11.

### 23.6 What remains of item 6, with a design: both ends at ratios `2 ≤ R / r < 32`

Needed: `c ≤ P(A_{J,I}(r, R))` for `2r ≤ R ≤ 32r` (then `π ≤ 1 ≤ c⁻¹ P`). A deterministic family of
`j` disjoint corridors in the annulus from the core windows of `θ'` on `∂B_r` to those of `θ` on
`∂B_R`, preserving the cyclic order, each a chain of `O(j)` rectangles of aspect ratio `O(1/μ)`.
Construction: (a) radial legs from the inner core windows to the ring `r + (R - r)/4`
(`exists_isArm_of_mem_ccw_corridor`'s boxes); (b) a **one-scale motion plan** in the ring
`[r + (R - r)/4, r + 3(R - r)/4]`: rotate all arms counterclockwise by the lifted differences of
`exists_lift_of_separated` (§17.1), in `≤ 8j` turn rounds at nested levels `h_k` (level spacing
`(R - r)/(32 j)`), as `exists_turn_step` does with radius growth replaced by level steps inside the
fixed ring; (c) radial legs to the outer core windows. Probability `≥ (c κ)^{O(j²)}` by
`law_mul_prod_le_law_of_regions` (independent corridors). Estimated 800–1200 lines (the turn corridors
of `TurnCorridors.lean` are reusable; the motion plan's combinatorics `exists_turn_step` is reusable
with a different radius bookkeeping). Then `exists_law_multiArmEvent_le_law_multiArmEventIn_windows`
holds for `2r ≤ R`.

### 23.7 Design for A3b-4 (half-plane OC/OCO separation; non-centred boxes)

**Targets** (plan §2.4 "half-plane versions"; `half-plane-exponents.md` §7 for U1b):
`π⁺_σ(r, R) ≤ C P⁺(arms landing in windows)` for `σ ∈ {OC, OCO}` (`halfArmEventTo`, linear order),
quasi-multiplicativity and extendability for `π⁺`, and the non-centred outer box version
`multiArmEventTo σ z r lo hi` with `B_{N/τ}(z) ⊆ Icc lo hi ⊆ B_N(z)`.

1. **Half-plane outer step.** The half-annulus boundary has three sides (top, the right half-side,
   the left half-side); arms land on them in linear order. Reuse `exists_law_separable_ge_top` on the
   top side and its reflections (`separable_right_of_top`, `separable_left_of_top`) on the half-sides
   cut at the line `y = z₁` (strip events at any position, `mem_separable_strip_of_inter_eq`). The
   bottom side is the boundary line: no arm lands there (`halfArmEventTo` keeps arms in
   `{v | z₁ ≤ v₁}`), so the corner exclusion of A3b-3b is needed only at the two corners on the line,
   by the one-arm bound (§20.1) in the half-plane (`exists_law_multiArmEvent_le_rpow` restricted, or a
   half-plane one-arm bound from `exists_halfArmEvent_two_bounds`' proof).
   Pack-freeness: `OC`, `OCO` have no two consecutive arms of one colour in the linear order, which is
   all the barrier needs (the cyclic condition `σ (j-1) ≠ σ 0` is not needed: the line separates the
   first and last arms).
2. **Half-plane gluing.** The motion plan in the half-annulus: lifted positions without wrap
   (linear order), turns only at the two upper corners; `exists_pos_le_law_target_windows` restricted
   to `tT ∈ {top, right, left}` and windows above the line by margin `S`. Corridors stay in the upper
   half-plane when the windows are `≥ S` above the line.
3. **Half-plane Theorem 11 / QM / extendability**: the induction of §19.2 verbatim; the inner half by
   §23.2 with half-plane corridors (`exists_pos_le_law_halfArmEvent`'s corridors already land in
   order) and the inner step on three sides (the bottom side is the line).
4. **Non-centred boxes.** `multiArmEventTo σ z r lo hi` with `B_{N/τ}(z) ⊆ Icc lo hi ⊆ B_N(z)`: compare
   with `B_{N/τ}` and `B_N` by monotonicity (`multiArmEventTo_subset_of_le_of_le`) in one direction,
   and in the other glue from separated arms at `∂B_{N/(2τ)}` into the four sides of `Icc lo hi`
   (the motion plan's window step with the target box `Icc lo hi` instead of `B_R`: the side
   coordinates of `exists_side_window` take `lo`, `hi` in place of `z ± R`; corners of `Icc lo hi`
   replace `4mR`). Simplest statement: `π(r, N) ≤ C P(multiArmEventTo σ z r lo hi univ univ)` and the
   converse inclusion bound, both for `τ` fixed.
5. **Order:** (1)–(3) for `OC`, `OCO` first (U1b needs the three-arm half-plane upper bound with
   separation, `half-plane-exponents.md` §4.3 option (2)); (4) when U2/Stage 3 need it.

### 23.8 Gate

`scripts/gate.sh main` **passed on `ca935e6`** (axiom audit 13626 constants, only `propext`,
`Classical.choice`, `Quot.sound`; 424 modules in the import closure; the interface NOTICE, expected:
the classifier names the first interface file on this branch, `Arms/Defs.lean`; no other notice). A
first gate passed on `ce6bd27` (13597 constants), before the two-ended form. Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against ae4eb08e45a1: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on ca935e6f8afa180546e538b86febf5518fd41fbf
```

This note's commit changes only `docs/`.

## 24. A3b-4 (2026-11-27): the half-plane outer separation step; design for the rest

Package A3b-4 = §23.7 (half-plane separation for `OC`, `OCO`; non-centred boxes). **Done: item 1,
the half-plane outer step, in event form and probability form, for every colour sequence with no
two consecutive arms of one colour in the linear order** (so `OC`, `OCO` and more). **Not done:
items 2–4** (§24.6 has the design and the order). Proof-only; `Planar/Defs.lean`, `Arms/Defs.lean`
and `Arms/Separation/Defs.lean` untouched; no `@[tag]`, no `…Input`, no new definition (the separated
half-plane event is written inline). Commits:

* `6d98681` **Arms/HalfSeparationSides, Arms/HalfOuterSeparation** (new) and in-place
  generalisations in `Arms/SeparationLemma`, `Arms/OuterSeparation`, `Arms/InnerSeparationSides`.
* `f8cbf3f` **Arms/HalfOuterSeparation**: rename of one hypothesis (`hηdef`; the gate's classifier
  reads `def` after a Greek letter as a keyword and called the file an interface change).
* this note's commit (docs only).

Sizes: `HalfSeparationSides.lean` 1095 lines, `HalfOuterSeparation.lean` 1742 lines. Gate: §24.8.

### 24.1 The statements proved, by plan item

All uniformly under `CrossingBounds q L c`, constants (`η`, `N₀`) chosen before `q`, `L`, `z` and
the radii. The colour hypothesis is the **linear** pack-freeness
`hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k` (the first and the last arm may have one
colour, as in `OCO`).

**Item 1 (§23.7 (1), the half-plane outer step)**:

* `exists_law_separable_ge_top_half` (`HalfSeparationSides`): Lemma 15 for the strip of a
  half-side read on a top row: open crossings in `[A, B] × [T - N, T]`, dual crossings in the faces
  `[A, B] × [T - N - 1, T]` whose dual edges cross edges of `[A, B + 1] × [T - N, T]`, `B = A + 2N`
  (width `2`); separation `4√η N` of the ends from each other and from `2A` (the line) and
  `2(B + 1)` (the corner); fences as in Lemma 15. Stated as `∃ J₀, ∀ J ≥ J₀, η = (1/(16·8^J))² → …`.
* `exists_law_separable_ge_top_of_le`: the top side of `B_R(z)` (Lemma 15 of
  `exists_law_separable_ge_top`) in the same `∀ J ≥ J₀` form, so that the top side and the
  half-sides share one `η` (fences must have one `K = ⌊ηN⌋`, `HasOuterFence` is not monotone in `K`).
* `mem_separable_top_half_of_inter_eq` (determination by `[A - M - K, B + 1 + M + K] × [T - N, T + M + 1]`),
  `separable_right_half_of_top` (swap), `separable_left_half_of_top` (quarter turn, `T = -X`).
* `IsArm.exists_append_eq_right_half`, `…_left_half` (final crossings of half-plane arms lie in the
  half-side strips; derived from the full-side lemmas and the half-plane condition),
  `exists_reroute_right_half`, `exists_reroute_left_half` (new landing positions in
  `[6R + s, 8R - s]`, resp. `[12R + s, 14R - s]`, the new arms in the half-plane).
* The virtual arm and the barrier: `exists_walk_column`, `IsArm.of_agree_of_le`,
  `IsArm.landingPos_mem_Icc_of_half` (half-plane arms land in `[6R, 14R]`), `exists_isArm_virtual`
  (in the configuration equal to `ω` on the edges above the line, with the column below `B_r(z)`
  open for an open virtual arm, a straight arm down to the bottom side, landing at `2R + [dual]`,
  inner position `2r + 1 + [dual]`), `sbtw_innerPos_iff_sbtw_landingPos_three`, `ArmsDisjoint.pair`,
  **`armsDisjoint_and_strictMono_of_innerPos_eq_half`** (a family of half-plane arms with the colours
  and inner positions of a disjoint, increasingly landing family is disjoint and lands increasingly).
* `halfArmEventIn_subset_halfArmEventIn_of_le` (monotonicity of the half-plane event in the outer
  radius, `r < N ≤ R`, windows `J` kept).
* **`exists_half_separating_event`** (event form):

```lean
theorem exists_half_separating_event {j : ℕ} (σ : Fin j → Bool)
    (hσ : ∀ i k : Fin j, i.val + 1 = k.val → σ i ≠ σ k) (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ (z : LatticeSite 2) (N R : ℕ), R = 2 * N + 1 → N₀ ≤ N →
      (N : ℕ∞) ≤ L → ∃ G : Set (Config (LatticeSite 2)), MeasurableSet G ∧
        (G determined by the edges of B_{2R}(z) \ B_N(z)) ∧ 1 - δ ≤ law q G ∧
        ∀ r < N, ∀ (J : Fin j → Set ℤ), ∀ ω ∈ halfArmEventIn σ z r R J (fun _ => univ) ∩ G,
          ∃ a b γ, (∀ i, IsArm ω (σ i) z r (z - R) (z + R) (γ i)) ∧ ArmsDisjoint σ γ ∧
            (∀ i, ∀ v ∈ (γ i).support, z 1 ≤ v 1) ∧
            (StrictMono fun i => landingPos (z - R) (z + R) (σ i) (γ i)) ∧
            ArmsOuterSeparated ω σ z R (4 * √η * N) ⌊√η * N⌋₊ ⌊η * N⌋₊ γ ∧
            (∀ i, 6R + 4√η N ≤ landingPos … (γ i) ∧ landingPos … (γ i) + 4√η N ≤ 14R) ∧
            ∀ i, innerPos z r (σ i) (γ i) ∈ J i
```

* **`exists_law_halfArmEventIn_diff_separated_le`** (probability form): for `R = 2N + 1`,
  `N₀ ≤ N ≤ L`, `r < N`, all `J`:
  `P(A⁺_J(r, R) \ {separated half-plane family as above}) ≤ δ · P(A⁺(r, N))`.

**Items 2–4: not done** (§24.6).

### 24.2 The proof

* **Strips cut at the line.** An open arm of the half-plane lies in the rows `[z₁, z₁ + R - 1]`
  before its end, a dual arm in the face rows `[z₁, z₁ + R - 1]`. Read through the swap (right) or
  the quarter turn (left) as a top strip, the open and the face columns coincide at the line and the
  face columns reach one further at the corner: Lemma 15 with `k = 0` at one end and `k' = 1` at the
  other. A strip ending at the line fits the arms exactly, so **no corner exclusion is needed** at
  the two points of the line (§23.7 (1) proposed one; it is not needed, see §24.4). With
  `R = 2N + 1` the half-side strip has length `2N` and depth `N` (width `2`), the top strip length
  `4N` (width `4`).
* **One `η`.** Lemma 15's proof picks a number of scales `J` from `δ` and the width; every larger `J`
  works with `η = (1/(16·8^J))²`. `exists_law_separable_ge_aux_wide_of_le` states this; the top and
  half-side events then use `J = max J₁ J₂`.
* **Rerouting.** Top: `exists_reroute_top` (now also saying that the new arm lies in the old arm and
  the strip, above `z₁ + R - N - 1`, hence in the half-plane). Half-sides: as on the full sides, with
  the half-side events.
* **Barrier (linear).** Two arms `i < i'` of one colour are separated by two arms of the other
  colour: their right neighbours `i + 1`, `i' + 1` if `i' + 1 < j`; else `i - 1`, `i + 1` if `i > 0`;
  else (`i` first, `i'` last) the arm `1` and a **virtual arm** below the line of the colour opposite
  to arm `0`. The virtual arm lives in the configuration `ω↓` equal to `ω` on the edges with both
  ends at height `≥ z₁` (all half-plane arms of `ω` are arms of `ω↓`, `IsArm.of_agree_of_le`) and
  lands at `2R` or `2R + 1`, below all half-plane landing positions (`≥ 6R`). The sector argument
  of `ArmsDisjoint.of_innerPos_eq` then runs through `sbtw_innerPos_iff_sbtw_landingPos_three`
  (order invariance for three arms given one by one). The increasing order of the new family follows
  from the cyclic order of `(γ'_i, γ'_k, V)` and `V` landing lowest.
* **Probability form.** `G` is the intersection of the top event at `z` and the two half-side events
  in their frames (probability `≥ 1 - δ/3` each), determined by `B_{2R}(z) \ B_N(z)`; the half-plane
  event at radius `N` is determined by the edges in `B_N(z)` (`mem_halfArmEventTo_iff_of_agree`) and
  contains `A⁺_J(r, R)` (`halfArmEventIn_subset_halfArmEventIn_of_le`); independence as in the plane.

### 24.3 Decisions (mine, per the standing instruction)

1. **Linear pack-freeness** `σ i ≠ σ (i + 1)` as the hypothesis, for every `j` (covers `OC`, `OCO`;
   no specialisation needed).
2. **Strips ending at the line, `k = 0`, `k' = 1`** (generalising Lemma 15 in place to two end
   parameters; the old statements are the instances `k = k'`), instead of corner exclusion.
3. **Uniform `η`** by restating Lemma 15 for all `J ≥ J₀` (`exists_law_separable_ge_aux_wide_of_le`),
   the old `exists_law_separable_ge_aux_wide` its `J = J₀` corollary; new `exists_law_separable_ge_top_of_le`
   beside the old top lemma (unchanged).
4. **Virtual arm** in a modified configuration to reuse the cyclic order invariance, instead of a
   new topological lemma for the half-plane.
5. **In-place strengthening of `exists_reroute_top`** (one more conjunct: where the new arm lies);
   its only caller adapted.
6. **The separated half-plane event inline**: `ArmsOuterSeparated` (with the same `s`, `M`, `K` as
   the plane) together with the half-plane condition, `StrictMono` of the landing positions and the
   separation `[6R + s, 14R - s]` from the line. No new definition.
7. Half-side event parameters: `A = z₁`, `B = z₁ + R - 1` (the expression `z₁ + R - 1 + 1` appears
   for the corner and is kept syntactically, so that the frame events and the reroute lemmas match).
8. Probability split `δ/3` per side; `N₀ = (16·8^J)² + 4`.

### 24.4 Errata and observations

* **§23.7 (1): the corner exclusion at the line is not needed.** With the half-side strip ending at
  the line (face columns starting with the open columns there), every final crossing of an arm
  landing on a half-side lies in the strip, and Lemma 15 keeps the new ends `4√ηN` away from the
  line. The half-plane one-arm bound is not used.
* §23.7 (1) did not mention that the half-side strips have a different width (`2`) from the top
  strip (`4`), so the plain `∃ η` form of Lemma 15 gives two different `η`; fixed by the `∀ J ≥ J₀`
  form (decision 3).
* The cyclic condition `σ (j-1) ≠ σ 0` is indeed not needed: the virtual arm below the line plays
  the role of the missing separator (confirmed in Lean, `armsDisjoint_and_strictMono_of_innerPos_eq_half`).
* No plan statement is false; nothing beyond `hσ` (linear) was needed; no small-radius threshold is
  needed for item 1 (only `N₀ ≤ N`, as in the plane).

### 24.5 Search

* PercLib, reused: `exists_law_separable_ge_aux_wide` (generalised), `separable_of_forall`
  (generalised), `exists_law_separable_ge_top`, `mem_separable_top_of_inter_eq`,
  `separable_right_of_top` / `separable_left_of_top` (adapted into the half versions),
  `IsArm.exists_append_eq_right/left`, `exists_reroute_top/right/left`, `IsArm.penultimate_mem`,
  `IsArm.end_mem_sides`, `IsArm.landingPos_eq_of_top/right/bottom/left`,
  `Icc_subset_Icc_add_one_sub_one`, `sbtw_innerPos_iff_sbtw_landingPos`, `IsArm.append_of_append`,
  `IsDualArm.penultimate_eq`, `innerPos_append`, `landingPos_append`, `ArmsDisjoint.mono`,
  `IsArm.exists_append_eq_of_le_of_le`, `mem_halfArmEventTo_iff_of_agree`,
  `measurableSet_halfArmEvent`, `halfArmEventIn_subset_halfArmEvent`, `image_sym2Map_mem_iff_of_inter_eq`,
  `finite_setOf_forall_mem`, `measurableSet_of_determined_finite`, `law_comp_sym2Map_apply`,
  `CrossingBounds.swap/.reflect`, `exists_iso_swap`, `exists_iso_reflect_one`,
  `prodBernoulli_inter_of_determined`, `mem_Icc_of_mem_dualEdge`, `mem_dualConfig_iff`,
  `dualEdgeEquiv`, `map_add_mem_edgeSet`, `dualEdge_mem_edgeSet`, `exists_walk_row` (pattern).
* Mathlib: `SimpleGraph.Walk.mem_support_of_mem_edges`, `snd_mem_tail_support`, `adj_snd`,
  `take_spec`, `support_takeUntil_subset_support`, `support_dropUntil_subset_support`,
  `List.dropLast_cons_of_ne_nil`, `Sym2.mem_iff_exists`, `Int.sbtw_iff`, `Fin.cases`.
* Not found (added): Lemma 15 with different ends; Lemma 15 for all scale parameters from some on;
  half-side transports; a column walk (only the row walk existed); order invariance for three arms
  given one by one; the barrier, the outer step and outer-radius monotonicity in the half-plane.

### 24.6 What remains, with a design and an order

The full-plane outer half took A3b-2…A3b-3 (gluing, motion plan, window steps, induction); the
inner half A3b-3b…A3b-3e. The half-plane versions reuse most geometry but need their own statements.
Proposed packages (each one session; estimates in Lean lines):

* **A3b-4b: half-plane gluing (§23.7 (2)), ~1500–2500.** From the separated half-plane event at
  `∂B_N` (24.1) to landing in prescribed windows at `∂B_{R'}`, `R' ≍ N`, with fences: the motion plan
  in linear order (no wrap; `exists_lift_of_separated` is not needed, the positions are already
  linear), turns only at the two upper corners, windows `≥ S` above the line. Reuse
  `exists_pos_le_law_windows_of_stages` / `exists_turn_step` (TurnCorridors, RotationGluing) with the
  bottom side excluded; the corridors stay above the line when the windows and the separated ends
  are `≥ S` above it (the separated ends are `≥ 2√ηN` above the line in rows, 24.1). Half-plane
  windows: `window (16R) θ η` with `θ` in `[3/8 + η, 7/8 - 2η]` (positions in `(6R, 14R)`), i.e.
  `IsLanding η θ` plus the margins; an `example` that such data exist.
* **A3b-4c: half-plane Theorem 11, outer half, + QM upper half + extendability outwards
  (§23.7 (3) first half), ~800–1200.** Nolin's induction (§19.2) verbatim with 24.1's outer step,
  A3b-4b's gluing and window steps; the a priori lower bound `c₀ (r/R)^α ≤ π⁺` from the window steps.
* **A3b-4d…f: the inner half for `π⁺`** (needed by U1b, see below), by §23.2: half-plane inner step
  (Lemma 15 at the inner boundary on the **upper half of `∂B_ρ(z)`**: top side and two half-sides of
  `B_ρ(z)`, with the dual-configuration trick of A3b-3b and the line handled as here: strips ending
  at the line, no corner exclusion at the line, the one-arm corner exclusion of §20.1 at the two
  upper corners only), half-plane two-sided gluing and step S, QM lower half by the induction of
  §21.2, extendability inwards, then `π⁺(r, R) ≤ C P(A⁺_J(r, R))`. Estimate 3 sessions.
* **Item 4 (non-centred boxes): not needed by U2a** (`planar-pack-analysis.md` §4.2: U2a is an RSW
  construction without separation; non-centred boxes enter only Stage 3's comparison of four-arm
  probabilities across centres). Design unchanged from §23.7 (4): monotonicity one way, the window
  step with target box `Icc lo hi` the other way (the side coordinates of `exists_side_window` take
  `lo`, `hi` in place of `z ± R`; corners of `Icc lo hi` in place of `4mR`). Do it when Stage 3 starts.

### 24.7 For U1b (three arms `OCO` in the half-plane, upper bound, option (2) of `half-plane-exponents.md` §4.3)

* **What U1b needs.** Werner's count works once the open arms of `x` stay off the line `y = x₁`
  outside a fixed box `B_k(x)` (then the dual cluster of `x`'s upper face, cut to `B_{3n}(0)`, has its
  lowest faces only near `x`, the map `x ↦ cluster` has bounded multiplicity, and the BK count of
  dual clusters crossing `B_{3n} \ B_n` — as in U1's two-arm proof, `sum_law_le_sum_pow_of_forall_mem_foldl`,
  `mem_foldl_of_pairwise_notMem_localConn` — gives `Σ_x P(strict arms at x) ≤ C`). Strictness is
  obtained by moving the half-plane event up: for `y = x + (k + 1)e₂`, arms of `A⁺_y(k, R)` lie in
  `{height ≥ x₁ + k + 1}`; joining them to `x` inside `B_k(y)` needs their starts in **inner windows**
  on the upper half of `∂B_k(y)` (finite energy at `q = 1/2` then gives a fixed local configuration
  of probability `≥ 2^{-O(k²)}`). So U1b needs **the half-plane inner half of Theorem 11 at a fixed
  inner radius `k = r₀`, uniformly in `R`**:
  `π⁺_{OCO}(k, R) ≤ C · P(halfArmEventIn ![true, false, true] y k R (window (16k + 8) θ' η) univ)`
  for half-plane inner landing data `θ'` (positions in `(6k + 3, 14k + 7)`), plus translation
  (`law_halfArmEvent_eq_law_halfArmEvent_zero`) and inner monotonicity `π⁺(0, R) ≤ π⁺(k, R)` (the
  half-plane analogue of `multiArmEvent_subset_of_le` for the inner radius; same virtual-arm proof as
  `halfArmEventIn_subset_halfArmEventIn_of_le`).
* **Not provided by this package.** 24.1 is the outer step only; the inner half is A3b-4d…f (24.6).
  **U1b's upper bound is therefore not reachable directly after this package**; its lower bound is
  (the RSW construction of `half-plane-exponents.md` §4.2). Options for the coordinator/user:
  (a) run A3b-4b…f first (about 5 sessions), then U1b; (b) U1b's lower bound now, upper bound after
  A3b-4f; (c) option (1)/(3) of `half-plane-exponents.md` §4.3 (`![false, true, false]`, no separation).
* A fixed-scale shortcut (routing the arms of `A⁺_y(k, R)` from **arbitrary** starts on `∂B_k(y)` to
  `x` by an exhaustive finite construction, avoiding inner windows) was considered and rejected:
  starts may be adjacent or at corners, and the local surgery interferes with the event at `y`.

### 24.8 Gate and lessons

Gate: `scripts/gate.sh 7d084c2` (the Tom's-main commit merged into this branch) **passed on
`f8cbf3f`** (axiom audit 17393 constants, only `propext`, `Classical.choice`, `Quot.sound`; 622
modules in the import closure; the interface NOTICE, expected: the classifier names this branch's
pending interface file `Arms/Separation/Defs.lean`). A first run passed on `6d98681` with the NOTICE
naming `HalfOuterSeparation.lean` for the token `def` in `hηdef` (fixed in `f8cbf3f`). Final lines:

```
D-35 checks passed (tagged statements, headers of new files).
INTERFACE change against 7d084c206b9a: Proof PR touches an interface/non-Lean file: PercLib/Models/Planar/Arms/Separation/Defs.lean
NOTICE: interface change; an auditor must approve before merge.
== gate passed on f8cbf3f98436416635a583d9d9e7d9e5835d0f42
```

This note's commit changes only `docs/`.

Lessons:

* **Text transformation of existing proofs** (python substitution of coordinates, then compile) gave
  the half-side transports (~900 lines) at the first compile: the transport proofs are pure
  coordinate chases (`omega` after `simp` of `![…]` entries), so replacing the coordinates of the
  frame and of the side by variables works unchanged.
* The classifier splits identifiers at non-ASCII letters: `hηdef` reads as the keyword `def`. Check
  new files with `check_paths_and_source` from `scripts/check_proof_pr.py` before the gate.
* `\b` does not work in BSD `sed`; the substitution silently did nothing. Check with `grep` after
  each substitution.
* The shell's working directory can reset to the main checkout between commands; always `cd` to the
  worktree explicitly.
* `nlinarith` stopped finding the product of two hypotheses once the context grew; give the product
  (`mul_le_mul_of_nonneg_right`) and use `linarith`.
* `tauto` failed on goals with `sbtw` on `ℤ` (it unfolds to a disjunction of conjunctions); prove the
  propositional step by hand.
* After `nsmul_eq_mul` fires on a function (`2 • z = 2 * z`), the coordinates need `Pi.mul_apply`
  and `Pi.ofNat_apply`.
