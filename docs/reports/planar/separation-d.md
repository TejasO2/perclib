# Local separation, part A2c-2: Nolin's Lemma 15 is proved

Advice for the wiki agent and for the next session on package A2 of the arms plan (Nolin's local
separation lemma, EJP 2008, Lemma 15). **A2 is finished**: `exists_law_separable_ge` is proved, in
the form the user approved on 2026-11-22 ("Yes, both corrections", `separation-c.md`,
§"Proposed statement for A2c-2"). Nothing else in the statement was changed.

New files, both proof-only (no definition, no tag, no `…Input`; `Arms/Defs.lean` and
`Planar/Defs.lean` unchanged); `#print axioms exists_law_separable_ge` gives `propext`,
`Classical.choice`, `Quot.sound`:

* `PercLib/Models/Planar/Arms/SeparationEvents.lean` (1630 lines, 43 theorems): the probability
  side (conditioning on the exploration by summing over explorations, the protection events, their
  bounds, and the inclusions that turn them into the hypotheses of the blocking and fence lemmas).
* `PercLib/Models/Planar/Arms/SeparationLemma.lean` (1324 lines, 11 theorems): the deterministic
  assembly and the final theorem.

`Arms/SeparationSurgery.lean` was strengthened (proof-only; untagged statements): three conjuncts
added to `exists_reroute_of_exploration` (each rerouted walk is open after the removals of its
step; its vertices lie on its greedy crossing or on the member before the member's last vertex;
its edges are edges of the member or of the greedy crossing), and the matching invariants in
`exists_reroute_aux`.

## The statement as proved

`SeparationLemma.lean:1040`:

```lean
theorem exists_law_separable_ge (c : ℕ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ (q : Sym2 (LatticeSite 2) → unitInterval) (L : ℕ∞),
      CrossingBounds q L c → ∀ N : ℕ, N₀ ≤ N → (N : ℕ∞) ≤ L →
      1 - δ ≤ law q {ω | ∀ (m : ℕ) (σ : Fin m → Bool) (a b : Fin m → LatticeSite 2)
        (γ : ∀ i, (zdGraph 2).Walk (a i) (b i)),
        (∀ i, cond (σ i)
          (a i 1 = 0 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ), N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ ω)
          (a i 1 = -1 ∧ b i 1 = N ∧
            (∀ x ∈ (γ i).support, x ∈ Icc (![0, -1] : LatticeSite 2) ![4 * (N : ℤ) - 1, N]) ∧
            ∀ e ∈ (γ i).edges, e ∈ dualConfig ω ∩ dualEdge '' {e | e ∈ (zdGraph 2).edgeSet ∧
              ∀ x ∈ e, x ∈ Icc (0 : LatticeSite 2) ![4 * (N : ℤ), N]})) →
        (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ i).support, x ∉ (γ j).support) →
        ∃ (b' : Fin m → LatticeSite 2) (γ' : ∀ i, (zdGraph 2).Walk (a i) (b' i)),
          (∀ i, cond (σ i) (… the same crossing conditions for γ' i, b' i …)) ∧
          (∀ i j, i ≠ j → σ i = σ j → ∀ x ∈ (γ' i).support, x ∉ (γ' j).support) ∧
          (∀ i j, i ≠ j → 4 * Real.sqrt η * N ≤
            |((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) - ((2 * b' j 0 + cond (σ j) 0 1 : ℤ) : ℝ)|) ∧
          (∀ i, 4 * Real.sqrt η * N ≤ ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ) ∧
            4 * Real.sqrt η * N ≤ 8 * N - ((2 * b' i 0 + cond (σ i) 0 1 : ℤ) : ℝ)) ∧
          ∀ i, ∃ x ∈ (γ' i).support, ∃ l r : LatticeSite 2,
            l 0 = b' i 0 - ⌊η * N⌋₊ ∧ r 0 = b' i 0 + ⌊η * N⌋₊ ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc ![b' i 0 - ⌊η * N⌋₊, N] ![b' i 0 + ⌊η * N⌋₊, N + ⌊Real.sqrt η * N⌋₊]) l r ∧
            cond (σ i) ω (dualConfig ω) ∩ (zdGraph 2).edgeSet ∈ localConn
              (Icc (b' i - (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))
                (b' i + (⌊Real.sqrt η * N⌋₊ : LatticeSite 2))) x l}
```

Conventions, as fixed in `separation-a.md` and `separation-c.md`: `Q = [0, 4N] × [0, N]`; an open
crossing is a walk of `ℤ²` in `Q` from row `0` to row `N` along open edges; a dual crossing is a
walk of faces of `[0, 4N - 1] × [-1, N]` from row `-1` to row `N` along dual-open dual edges that
cross edges of `Q` (the PT1 form `dualConfig ω ∩ dualEdge '' {edges of Q}`); disjointness is only
between crossings of the same colour (vertices for open, faces for dual); positions are doubled
(`2x` open, `2x + 1` dual). The floors are `Nat.floor` (`⌊·⌋₊`), equal to the integer floors since
`η N ≥ 0`. "Same bottom parts" is read as Nolin's Definition 7: the same starting points.

Binder check (for a reviewer): `c`, `δ`, `hδ`, `q`, `L`, `CrossingBounds q L c`, `N ≤ L` are the
source's data (crossing bounds stand for "below the characteristic length"); `η` and `N₀` are
chosen after `δ` and `c` only, before `q`, `L`, `N`; `N₀ ≤ N` is the approved correction 2. No
excess binder.

## The two approved corrections and why

1. **The fence clause is Nolin's (4.5).** The draft asked for the fence crossing to be joined to the
   end `b' i` inside the ball. Nolin's condition (4.5) joins the *arm* to the fence crossing inside
   the ball ("`c_i ↝ c̃_i` inside `S̊_{√ηM}(z_i)`"). The proof (Nolin's, and ours) produces a vertex of
   the rerouted crossing joined to the fence; the crossing can leave the ball after that vertex and
   come back to its end. Joining the end would need a half-plane five-arm bound, which the source
   does not use. The proved clause is the arm-joined one: some `x ∈ (γ' i).support`.
2. **`∃ N₀` and `N₀ ≤ N`.** The draft (like Nolin's (4.11), "any `N ≤ L(p)`") quantified over every
   `N`. It is false for small `N`: at `N = 1`, `q ≡ 1/2`, `δ < 2^{-13}`, with probability `2^{-13}`
   the only open edge of `Q` is `(0, 0)–(0, 1)`, and the one-member family consisting of it cannot
   be moved off the corner (counterexample in `separation-c.md`). Here `N₀ = D²` with
   `D = 16 · 8^J`, depending only on `δ` and `c`.

## Errata in the source found during A2

* **The rerouting rule** (arXiv v1, Lemma 14, pp. 25-26; journal Lemma 15). Matching each crossing
  to the least-index greedy crossing it meets and cutting at the *last* intersection can produce
  intersecting crossings; cutting at the *first* intersection with the same matching fails too.
  Counterexamples in `separation-a.md` and `separation-b.md`. The rule proved works from right to
  left (`exists_reroute_of_exploration`), packs included. Lemma 15 itself is unaffected.
* **Reversed exponents in the corner annuli** (arXiv v1, p. 24): a range like
  `η^{3/8} ≤ 2^{l-1} < 2^l ≤ √η` is empty for `η < 1`. Here the corner scales are
  `2 (⌊√η N⌋ + 1) 8^j`, `j < J`, which are between `2 √η N` and `N / 32`.
* **The small-`N` quantifier in (4.11)**: see correction 2.

## How the proof goes (items 1–7 of `separation-c.md`)

* **Explorations.** One greedy exploration per colour with the clean choice rule: of `ω` in `Q`,
  and of `dualConfig ω` (not restricted) in the box of faces `[0, 4N - 1] × [-1, N]`.
* **Sum over explorations** (`law_exploration_forall_notMem_le`, `SeparationEvents.lean:250`). For
  each finite sequence `B : Fin (v + 1) → Finset`, the event "the exploration of `g ω` up to step
  `v` is `B`" is measurable (`measurableSet_exploration`), determined by the pairs meeting `B v`
  (`exploration_iff_of_inter_eq`, any `g` with that determination, here `id` and `dualConfig`),
  and these events are disjoint (`exploration_unique`). With `law_inter_biInter_compl_le` on each
  and `measure_iUnion_inter_le`, protection at `J` disjoint scales fails with probability at most
  `(1 - c 7 ^ 4)^J`, for every step `v`.
* **Events built from fresh pairs.** Instead of proving that the absence events of A2c-1 are
  determined by the unexplored pairs, the protection event at scale `s` around a centre is defined
  from `Q = (pairs in the annulus s - 2 ≤ ‖·‖∞ ≤ 3s + 2) \ P`, with `P` the pairs the exploration
  has read, in one of four forms: `ω ∩ Q` crosses none of three strips; `dualConfig (ω ∪ Qᶜ)`
  crosses none of three strips; `ω ∪ Qᶜ` crosses four boxes; `dualConfig (ω ∩ Q)` crosses four
  boxes of faces. Each is determined by `Q` by construction and contains a circuit event
  (`pow_le_law_…_add`, `c 7 ^ 4`, the dual fence by box duality at `z + (1, 1)`). Eight inclusion
  lemmas (`notMem_crossing_sdiff_of_inter`, …, `SeparationEvents.lean:1151–1569`) turn each event
  into the hypotheses of `lt_sub_of_exploration`, `false_of_localConn_of_exploration`,
  `exists_fence_of_exploration` and the corner lemmas. For the dual exploration the read pairs are
  the edges crossed by the read dual edges (`map_add_one_dualEdge_injOn`), and its other-colour
  protection is read on `ω` moved by `(1, 1)` (`image_dualConfig_union_inter_subset`).
* **Strip shape.** Step (a) in a box narrower than the boxes of the crossing bounds
  (`law_exploration_le_pow_of_le`, `law_exploration_dualConfig_le_pow_of_le`): `Q` sits in the box
  of width `5 (N - 1)` and height `N`, the box of faces in width `5N`, height `N + 1`; both give
  `(1 - c 6)^(T + 1)`.
* **Mixed colours.** An open tip `z` and a dual tip `f` with `z₀ ≤ f₀` are separated by the open
  tip's protection against the other colour applied to the dual greedy crossing of `f`, trimmed of
  its first and last face (`exists_walk_trim`, `add_lt_of_exploration_of_dualConfig`); with
  `f₀ < z₀`, by the dual tip's protection applied to the open greedy crossing of `z` moved by
  `(-1, -1)` (`add_lt_of_exploration_dualConfig`). Doubled distance `> 2s + 1`.
* **Surgery and fences.** Members are first cut at their first top-row vertex; then
  `exists_reroute_of_exploration`, and `exists_fence_of_exploration` on each rerouted walk (now
  clean at the top and open after the removals); `exists_fence_of_le` shrinks the fence to the box
  `[x - K, x + K] × [N, N + M]` and the ball of radius `M` (`exists_reroute_fence_of_exploration`).
* **Constants** (`scale_bounds`, `exists_law_separable_ge`). `T` with `(1 - c 6)^(T+1) ≤ δ/4`;
  `J` with `(1 - c 7^4)^J ≤ (δ/2) / (6 (T + 1) + 4)`; `D = 16 · 8^J`, `η = 1/D²`, `N₀ = D²`;
  `M = ⌊N/D⌋ = ⌊√η N⌋`, `K = ⌊N/D²⌋ = ⌊η N⌋`; separation and corner scales `2 (M + 1) 8^j`, fence
  scales `(K + 1) 8^j`, `j < J`. Union bound: two step-(a) events, `6 (T + 1)` protection families
  (three per colour per step), four corners: total `≤ δ`.
* **Deterministic part** (`separable_of_forall`, `SeparationLemma.lean:586`): given the good
  event, generic in the box `Icc lo hi` with the box of faces `[lo₀, hi₀ - 1] × [lo₁ - 1, hi₁]`.

## For A3

* A3 applies `exists_law_separable_ge` at dyadic scales; the scales `N < N₀` go into its
  constants (correction 2).
* The lemma is stated for the strip at the origin, crossed from bottom to top. Other positions:
  `CrossingBounds.translate`. Other sides of an annulus: no rotation or reflection of
  `CrossingBounds` exists yet; either add `CrossingBounds.rotate` (the rotated law has crossing
  bounds with the same `c`, both colours) or run the proof for the other orientations. The proof
  is generic in the box for everything deterministic (`separable_of_forall`), so a rotated statement
  only needs the probability side.
* The fence is arm-joined (Nolin (4.5)): a corridor path entering the fence box must cross the
  fence crossing, which is joined to the arm inside the ball. That is what Prop. 12 (gluing) uses.

## Search

* PercLib: `exploration_unique`, `exploration_iff_of_agree`, `law_inter_biInter_compl_le`,
  `measurableSet_cluster_eq_finset`, `mem_crossing_iff_of_inter_eq`, the box dualities
  `mem_crossing_one_iff_dualConfig_notMem_crossing_zero` and `mem_crossing_zero_iff_…`,
  `dualConfig_dualConfig`, `dualEdge_map_add_one_dualEdge`, `face_of_mem_dualEdge`,
  `image_add_mem_crossing_iff`, `exists_walk_mem_Icc` (generic graph, used in the open graph),
  `mem_localConn_iff_exists_walk`, `exists_zdGraph_iso_add`-style translation homomorphism (as in
  `ColourInversion.lean`). No existing lemma for summing over a countable partition, for
  determination of the exploration of `dualConfig ω`, or for trimming a clean crossing.
* Mathlib: `measure_iUnion_le`, `measure_iUnion`, `ENNReal.tsum_mul_right`,
  `measure_biUnion_finset_le`, `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`,
  `Nat.floor_div_eq_div`, `Nat.lt_floor_add_one`, `Real.sqrt_sq`, `ENNReal.add_halves`,
  `ENNReal.mul_div_le`, `List.dropLast_append_of_ne_nil`.

## Lessons

* Higher-order unification of an event family `K : Finset → ℕ → Set Config` from a goal times out
  (200000 heartbeats in `whnf`): pass `K` and `Q` explicitly, with `set` for the shared part and
  `exact key` against the expanded goal.
* `Pairwise (Disjoint on X)` needs `open Function`; write `Function.onFun Disjoint X`.
* `cond_true`, `cond_false` are deprecated (`Bool.cond_true`); `Set.diff_empty` is deprecated
  (`sdiff_empty`); `show` that changes the goal is flagged by the linter: use `change`.
* `simp` before `omega` pushes casts `↑(a * 8 ^ j)` to `↑a * 8 ^ j` in the goal but not in a
  hypothesis about the natural number, and `omega` then sees two atoms: use `simp only` with the
  vector lemmas.
* A bad event whose law is bounded by a lemma need not be written out: build
  `law q (B₁ ∪ (B₂ ∪ …)) ≤ …` with `measure_union_le_add_of_le` from the lemmas, then
  `one_sub_le_measure_of_forall_notMem`, and prove membership outside by
  `by_contra; exact hB ⟨A, hA, fun j hj hK => …⟩`.
* Modules build in 8–16 s per iteration; most lemmas compiled after one or two rounds.

## Sources

* P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008), paper
  no. 55, §4.2 (Definitions 6–8, (4.3)–(4.5)), §4.4, Lemma 15, (4.11). Read in earlier sessions
  through arXiv:0711.4948v1 (Lemma 14 there).
