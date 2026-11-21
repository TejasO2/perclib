/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, using mathlib's `SimpleGraph`, lists and finite sets. Mathematical reference: the
probabilistic depth-first search of I. Gladkov and I. Pak, *Exploring mazes at random*; the pivot
involution argument is the one written out in the PercLib wiki article on adaptive three-point
bounds. No source text or code is copied.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.Logic.Relation

/-! # The pivot involution of a randomised depth-first search

A recursive depth-first search on a finite graph is encoded by an *order function*
`σ : V → V → List V`: on entering `u` from its parent `p`, the search examines the vertices of
`σ u p` in this order, and descends immediately into each vertex not yet visited.
`DFS.visit σ n p u S` is the list of discoveries `(child, parent)`, in discovery order, made by the
call at `u` (entered from `p`) when the vertices of `S` are already visited, with recursion depth
at most `n`.

## Main results

* `PercLib.DFS.visit_congr`: two runs agree as long as they examine the same vertices with the
  same visited status.
* `PercLib.DFS.visit_closure`: a run with enough fuel visits every neighbour of every vertex it
  discovers.
* `PercLib.DFS.visit_swap_decomposition`: reversing the child order at a vertex with two children
  exchanges the two child blocks of the discovery list and changes nothing else.
-/

@[expose] public section

namespace PercLib
namespace DFS

variable {V : Type*} [DecidableEq V]

/-- The loop of the search at `u` over the candidate list, from the discoveries `L` so far;
`S` is the visited set at entry and `rec` the recursive call. -/
def visitList (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V) :
    List V → List (V × V) → List (V × V)
  | [], L => L
  | w :: ws, L => visitList rec u S ws
      (if w ∈ S ∨ w ∈ L.map Prod.fst then L
        else L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)))

/-- The discoveries `(child, parent)` of the recursive search at `u`, entered from `p`, with the
vertices of `S` already visited and recursion depth at most `n`. -/
def visit (σ : V → V → List V) : ℕ → V → V → Finset V → List (V × V)
  | 0, _, _, _ => []
  | n + 1, p, u, S => visitList (visit σ n) u S (σ u p) []

@[simp] theorem visitList_nil (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V)
    (L : List (V × V)) : visitList rec u S [] L = L := rfl

theorem visitList_cons (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V) (w : V)
    (ws : List V) (L : List (V × V)) :
    visitList rec u S (w :: ws) L = visitList rec u S ws
      (if w ∈ S ∨ w ∈ L.map Prod.fst then L
        else L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset))) := rfl

@[simp] theorem visit_zero (σ : V → V → List V) (p u : V) (S : Finset V) :
    visit σ 0 p u S = [] := rfl

theorem visit_succ (σ : V → V → List V) (n : ℕ) (p u : V) (S : Finset V) :
    visit σ (n + 1) p u S = visitList (visit σ n) u S (σ u p) [] := rfl

theorem exists_visitList_eq_append (rec : V → V → Finset V → List (V × V)) (u : V)
    (S : Finset V) : ∀ (ws : List V) (L : List (V × V)), ∃ M, visitList rec u S ws L = L ++ M
  | [], L => ⟨[], by simp⟩
  | w :: ws, L => by
    obtain ⟨M, hM⟩ := exists_visitList_eq_append rec u S ws
      (if w ∈ S ∨ w ∈ L.map Prod.fst then L
        else L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)))
    rw [visitList_cons, hM]
    split_ifs
    · exact ⟨M, rfl⟩
    · exact ⟨(w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)) ++ M, by simp⟩

/-- Induction along the loop: a property of the discovery list preserved by every new block. -/
theorem visitList_induction (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V)
    (Q : List (V × V) → Prop) (ws : List V)
    (hstep : ∀ L w, w ∈ ws → Q L → w ∉ S → w ∉ L.map Prod.fst →
      Q (L ++ (w, u) :: rec u w (insert w (S ∪ (L.map Prod.fst).toFinset)))) :
    ∀ L, Q L → Q (visitList rec u S ws L) := by
  induction ws with
  | nil => intro L h; exact h
  | cons w ws ih =>
    intro L hL
    rw [visitList_cons]
    apply ih (fun L w' hw' => hstep L w' (List.mem_cons_of_mem _ hw'))
    split_ifs with h
    · exact hL
    · simp only [not_or] at h
      exact hstep L w List.mem_cons_self hL h.1 h.2

theorem mem_or_mem_visitList (rec : V → V → Finset V → List (V × V)) (u : V) (S : Finset V) :
    ∀ (ws : List V) (L : List (V × V)) (w : V), w ∈ ws →
      w ∈ S ∨ w ∈ (visitList rec u S ws L).map Prod.fst
  | [], _, _, h => absurd h List.not_mem_nil
  | w :: ws, L, w', h => by
    rw [visitList_cons]
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨M, hM⟩ := exists_visitList_eq_append rec u S ws
        (if w' ∈ S ∨ w' ∈ L.map Prod.fst then L
          else L ++ (w', u) :: rec u w' (insert w' (S ∪ (L.map Prod.fst).toFinset)))
      rw [hM]
      split_ifs with hc
      · rcases hc with hc | hc
        · exact Or.inl hc
        · exact Or.inr (by simp only [List.map_append, List.mem_append]; exact Or.inl hc)
      · exact Or.inr (by simp)
    · exact mem_or_mem_visitList rec u S ws _ w' h

/-- Basic shape of a run: discovered vertices are new and distinct, every parent is the start
vertex or discovered earlier. -/
theorem visit_wf (σ : V → V → List V) : ∀ (n : ℕ) (p u : V) (S : Finset V), u ∈ S →
    ((visit σ n p u S).map Prod.fst).Nodup ∧ (∀ e ∈ visit σ n p u S, e.1 ∉ S) ∧
    (∀ e ∈ visit σ n p u S, e.2 = u ∨ e.2 ∈ (visit σ n p u S).map Prod.fst) ∧
    (visit σ n p u S).Pairwise (fun e f => e.2 ≠ f.1)
  | 0, p, u, S, _ => by simp
  | n + 1, p, u, S, hu => by
    rw [visit_succ]
    apply visitList_induction _ u S (fun L => (L.map Prod.fst).Nodup ∧ (∀ e ∈ L, e.1 ∉ S) ∧
      (∀ e ∈ L, e.2 = u ∨ e.2 ∈ L.map Prod.fst) ∧ L.Pairwise (fun e f => e.2 ≠ f.1)) _ _ _
      (by simp)
    intro L w _ ⟨h1, h2, h3, h4⟩ hwS hwL
    obtain ⟨k1, k2, k3, k4⟩ := visit_wf σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
      (Finset.mem_insert_self _ _)
    set D := visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
    have k2' : ∀ e ∈ D, e.1 ≠ w ∧ e.1 ∉ S ∧ e.1 ∉ L.map Prod.fst := by
      intro e he
      have := k2 e he
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, not_or] at this
      exact this
    have huw : u ≠ w := fun h => hwS (h ▸ hu)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons]
      refine List.nodup_append.2 ⟨h1, List.nodup_cons.2 ⟨?_, k1⟩, ?_⟩
      · intro hw
        obtain ⟨e, he, hew⟩ := List.mem_map.1 hw
        exact (k2' e he).1 hew
      · intro a ha b hb hab
        subst hab
        rcases List.mem_cons.1 hb with hb | hb
        · exact hwL (hb ▸ ha)
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
          exact (k2' e he).2.2 ha
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact h2 e he
      · rcases List.mem_cons.1 he with rfl | he
        · exact hwS
        · exact (k2' e he).2.1
    · intro e he
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      rcases List.mem_append.1 he with he | he
      · rcases h3 e he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.1 he with rfl | he
        · exact Or.inl rfl
        · rcases k3 e he with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
    · refine List.pairwise_append.2 ⟨h4, List.pairwise_cons.2 ⟨?_, k4⟩, ?_⟩
      · intro f hf h
        exact (k2' f hf).2.1 (h ▸ hu)
      · intro e he f hf h
        have hpar : e.2 ∈ S ∨ e.2 ∈ L.map Prod.fst := by
          rcases h3 e he with h' | h'
          · exact Or.inl (h' ▸ hu)
          · exact Or.inr h'
        rcases List.mem_cons.1 hf with rfl | hf
        · rcases hpar with h' | h' <;> simp_all
        · rcases hpar with h' | h'
          · exact (k2' f hf).2.1 (h ▸ h')
          · exact (k2' f hf).2.2 (h ▸ h')

/-- Every discovery is along an edge, when the order function lists only neighbours. -/
theorem visit_adj {G : SimpleGraph V} {σ : V → V → List V}
    (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w) : ∀ (n : ℕ) (p u : V) (S : Finset V),
    ∀ e ∈ visit σ n p u S, G.Adj e.2 e.1
  | 0, _, _, _ => by simp
  | n + 1, p, u, S => by
    rw [visit_succ]
    apply visitList_induction _ u S (fun L => ∀ e ∈ L, G.Adj e.2 e.1) _ _ _ (by simp)
    intro L w hw hL _ _ e he
    rcases List.mem_append.1 he with he | he
    · exact hL e he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hσ' _ _ _ hw
      · exact visit_adj hσ' n u w _ e he

/-- A child discovered directly from the start vertex is one of its candidates. -/
theorem mem_of_mem_visit (σ : V → V → List V) (n : ℕ) (p u x : V) (S : Finset V) (hu : u ∈ S)
    (h : (x, u) ∈ visit σ n p u S) : x ∈ σ u p := by
  cases n with
  | zero => simp at h
  | succ n =>
    rw [visit_succ] at h
    revert h x
    apply visitList_induction _ u S (fun L => ∀ x, (x, u) ∈ L → x ∈ σ u p) _ _ _ (by simp)
    intro L w hw hL hwS _ x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL x hx
    · rcases List.mem_cons.1 hx with h | hx
      · cases h; exact hw
      · obtain ⟨-, k2, k3, -⟩ := visit_wf σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
          (Finset.mem_insert_self _ _)
        rcases k3 _ hx with h | h
        · exact absurd (h ▸ hu) hwS
        · obtain ⟨e, he, hee⟩ := List.mem_map.1 h
          exact absurd (by simp [hu]) (hee ▸ k2 e he)

/-- **Lockstep.** Two runs coincide when, at every vertex the first run enters, the order
functions agree and the examined vertices have the same visited status. -/
theorem visit_congr {σ σ' : V → V → List V} : ∀ (n : ℕ) (p u : V) (S₁ S₂ : Finset V),
    (∀ z, (z = u ∨ z ∈ (visit σ n p u S₁).map Prod.fst) →
      (∀ q, σ' z q = σ z q) ∧ ∀ q, ∀ w ∈ σ z q, (w ∈ S₂ ↔ w ∈ S₁)) →
    visit σ' n p u S₂ = visit σ n p u S₁
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, u, S₁, S₂, h => by
    rw [visit_succ, visit_succ, (h u (Or.inl rfl)).1 p]
    have key : ∀ (ws : List V) (L : List (V × V)), (∀ w ∈ ws, (w ∈ S₂ ↔ w ∈ S₁)) →
        (∀ z ∈ (visitList (visit σ n) u S₁ ws L).map Prod.fst,
          (∀ q, σ' z q = σ z q) ∧ ∀ q, ∀ w ∈ σ z q, (w ∈ S₂ ↔ w ∈ S₁)) →
        visitList (visit σ' n) u S₂ ws L = visitList (visit σ n) u S₁ ws L := by
      intro ws
      induction ws with
      | nil => intro L _ _; rfl
      | cons w ws ih =>
        intro L hws hz
        rw [visitList_cons, visitList_cons]
        have hw := hws w List.mem_cons_self
        have hws' : ∀ w' ∈ ws, (w' ∈ S₂ ↔ w' ∈ S₁) :=
          fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')
        by_cases hc : w ∈ S₁ ∨ w ∈ L.map Prod.fst
        · have hc' : w ∈ S₂ ∨ w ∈ L.map Prod.fst := by rwa [hw]
          simp only [hc, hc', ↓reduceIte]
          rw [visitList_cons] at hz
          simp only [hc, ↓reduceIte] at hz
          exact ih L hws' hz
        · have hc' : ¬ (w ∈ S₂ ∨ w ∈ L.map Prod.fst) := by rwa [hw]
          simp only [hc, hc', ↓reduceIte]
          rw [visitList_cons] at hz
          simp only [hc, ↓reduceIte] at hz
          obtain ⟨M, hM⟩ := exists_visitList_eq_append (visit σ n) u S₁ ws
            (L ++ (w, u) :: visit σ n u w (insert w (S₁ ∪ (L.map Prod.fst).toFinset)))
          have hrec : visit σ' n u w (insert w (S₂ ∪ (L.map Prod.fst).toFinset)) =
              visit σ n u w (insert w (S₁ ∪ (L.map Prod.fst).toFinset)) := by
            apply visit_congr n u w
            intro z hz2
            have hzmem : z ∈ (visitList (visit σ n) u S₁ ws
                (L ++ (w, u) :: visit σ n u w (insert w (S₁ ∪ (L.map Prod.fst).toFinset)))).map
                  Prod.fst := by
              rw [hM]
              simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
              tauto
            obtain ⟨h1, h2⟩ := hz z hzmem
            refine ⟨h1, fun q w' hw' => ?_⟩
            simp only [Finset.mem_insert, Finset.mem_union, h2 q w' hw']
          rw [hrec]
          exact ih _ hws' hz
    exact key _ [] (fun w hw => (h u (Or.inl rfl)).2 p w hw) (fun z hz => h z (Or.inr hz))

variable [Fintype V]

theorem card_compl_insert_lt {S T : Finset V} {w : V} {n : ℕ} (hw : w ∉ S)
    (hn : Sᶜ.card < n + 1) : (insert w (S ∪ T))ᶜ.card < n := by
  have : (insert w (S ∪ T))ᶜ ⊂ Sᶜ := by
    refine Finset.ssubset_iff_of_subset (Finset.compl_subset_compl.2 ?_) |>.2 ⟨w, ?_, ?_⟩
    · intro a ha; simp [ha]
    · simpa using hw
    · simp
  have := Finset.card_lt_card this
  omega

/-- **Closure.** A run with enough fuel, from an order function listing all neighbours except the
parent, leaves no unvisited neighbour of the start vertex or of any discovered vertex. -/
theorem visit_closure {G : SimpleGraph V} {σ : V → V → List V}
    (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p) : ∀ (n : ℕ) (p u : V) (S : Finset V),
    u ∈ S → p ∈ S → Sᶜ.card < n →
    ∀ z, (z = u ∨ z ∈ (visit σ n p u S).map Prod.fst) → ∀ w, G.Adj z w →
      w ∈ S ∨ w ∈ (visit σ n p u S).map Prod.fst
  | 0, _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, u, S, hu, hp, hn => by
    rw [visit_succ]
    have hQ := visitList_induction (visit σ n) u S
      (fun L => ∀ z ∈ L.map Prod.fst, ∀ w, G.Adj z w → w ∈ S ∨ w ∈ L.map Prod.fst) (σ u p)
      (by
        intro L w _ hL hwS _ z hz w' hzw'
        have IH := visit_closure hσ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
          (Finset.mem_insert_self _ _) (by simp [hu]) (card_compl_insert_lt hwS hn)
        simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with hz | hz
        · rcases hL z hz w' hzw' with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases IH z hz w' hzw' with h | h
          · simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at h
            tauto
          · tauto) [] (by simp)
    intro z hz w hzw
    rcases hz with rfl | hz
    · by_cases hwp : w = p
      · exact Or.inl (hwp ▸ hp)
      · exact mem_or_mem_visitList _ z S _ [] w (hσ _ _ _ hzw hwp)
    · exact hQ z hz w hzw

omit [DecidableEq V] [Fintype V] in
theorem eq_pair_or_eq_pair_of_length_le_two {l : List V} {x y : V} (hl : l.length ≤ 2)
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) : l = [x, y] ∨ l = [y, x] := by
  match l, hl, hx, hy with
  | [], _, hx, _ => simp at hx
  | [a], _, hx, hy =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  | [a, b], _, hx, hy =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
  | _ :: _ :: _ :: _, hl, _, _ => simp at hl

variable {G : SimpleGraph V}

/-- **The pivot at one vertex.** If the search at `v` examines `[x, y]` and discovers both, then
examining `[y, x]` instead exchanges the two child blocks; each block has no unvisited
neighbour once it is finished. -/
theorem visit_swap_at {σ σ' : V → V → List V}
    (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p) (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w)
    {v : V} (hv : ∀ z, z ≠ v → ∀ q, σ' z q = σ z q)
    {n : ℕ} {p x y : V} {S : Finset V} (hxy : x ≠ y) (hvS : v ∈ S)
    (hn : Sᶜ.card < n + 1) (hσv : σ v p = [x, y]) (hσ'v : σ' v p = [y, x])
    (hx : (x, v) ∈ visit σ (n + 1) p v S) (hy : (y, v) ∈ visit σ (n + 1) p v S) :
    ∃ t₁ t₂ : List (V × V), visit σ (n + 1) p v S = (x, v) :: t₁ ++ (y, v) :: t₂ ∧
      visit σ' (n + 1) p v S = (y, v) :: t₂ ++ (x, v) :: t₁ ∧
      (∀ c ∈ ((x, v) :: t₁).map Prod.fst, ∀ a, G.Adj c a →
        a ∈ S ∨ a ∈ ((x, v) :: t₁).map Prod.fst) ∧
      (∀ c ∈ ((y, v) :: t₂).map Prod.fst, ∀ a, G.Adj c a →
        a ∈ S ∨ a ∈ ((x, v) :: t₁ ++ (y, v) :: t₂).map Prod.fst) := by
  have hxS : x ∉ S := (visit_wf σ (n + 1) p v S hvS).2.1 _ hx
  have hyS : y ∉ S := (visit_wf σ (n + 1) p v S hvS).2.1 _ hy
  have hxv : x ≠ v := fun h => hxS (h ▸ hvS)
  have hyv : y ≠ v := fun h => hyS (h ▸ hvS)
  set Dx := visit σ n v x (insert x S) with hDx
  obtain ⟨-, kx2, kx3, -⟩ := visit_wf σ n v x (insert x S) (Finset.mem_insert_self _ _)
  have kxc := visit_closure hσ n v x (insert x S) (Finset.mem_insert_self _ _)
    (by simp [hvS]) (by simpa using card_compl_insert_lt (T := ∅) hxS hn)
  have hD : visit σ (n + 1) p v S =
      if y ∈ S ∨ y ∈ ((x, v) :: Dx).map Prod.fst then (x, v) :: Dx
      else (x, v) :: Dx ++ (y, v) :: visit σ n v y
        (insert y (S ∪ (((x, v) :: Dx).map Prod.fst).toFinset)) := by
    rw [visit_succ, hσv, visitList_cons, visitList_cons]
    simp only [visitList_nil, hxS, List.map_nil, List.not_mem_nil, or_false, ↓reduceIte,
      List.nil_append, List.toFinset_nil, Finset.union_empty, hDx]
  have hc : ¬ (y ∈ S ∨ y ∈ ((x, v) :: Dx).map Prod.fst) := by
    intro hc
    rw [hD] at hy
    simp only [hc, ↓reduceIte] at hy
    rcases List.mem_cons.1 hy with h | h
    · exact hxy (Prod.mk.inj h).1.symm
    · rcases kx3 _ h with h' | h'
      · exact hxv h'.symm
      · obtain ⟨e, he, hee⟩ := List.mem_map.1 h'
        exact kx2 e he (by simp [hee, hvS])
  simp only [hc, ↓reduceIte] at hD
  set Sy := insert y (S ∪ (((x, v) :: Dx).map Prod.fst).toFinset) with hSy
  set Dy := visit σ n v y Sy with hDy
  have hySy : y ∈ Sy := Finset.mem_insert_self _ _
  obtain ⟨-, ky2, -, -⟩ := visit_wf σ n v y Sy hySy
  have kyc := visit_closure hσ n v y Sy hySy (by simp [hSy, hvS])
    (card_compl_insert_lt hyS hn)
  simp only [List.map_cons, List.mem_cons, not_or] at hc
  have hDy' : visit σ' n v y (insert y S) = Dy := by
    apply visit_congr
    intro z hz
    have hzv : z ≠ v := by
      rcases hz with rfl | hz
      · exact hyv
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
        intro h; exact ky2 e he (by simp [hSy, h, hvS])
    refine ⟨hv z hzv, fun q w hw => ?_⟩
    have hzw : G.Adj w z := (hσ' _ _ _ hw).symm
    constructor
    · intro h; simp only [hSy, Finset.mem_insert, Finset.mem_union] at h ⊢; tauto
    · intro h
      simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
        List.mem_cons] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have := kxc w (Or.inl h) z hzw
        rcases hz with rfl | hz
        · simp only [Finset.mem_insert] at this; tauto
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
          apply ky2 e he
          simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
            List.mem_cons] at this ⊢
          tauto
      · exfalso
        have := kxc w (Or.inr h) z hzw
        rcases hz with rfl | hz
        · simp only [Finset.mem_insert] at this; tauto
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
          apply ky2 e he
          simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
            List.mem_cons] at this ⊢
          tauto
  have hxDy : x ∉ Dy.map Prod.fst := by
    intro h
    obtain ⟨e, he, hee⟩ := List.mem_map.1 h
    exact ky2 e he (by simp [hSy, hee])
  have hDx' : visit σ' n v x (insert x (S ∪ (y :: Dy.map Prod.fst).toFinset)) = Dx := by
    apply visit_congr
    intro z hz
    have hzv : z ≠ v := by
      rcases hz with rfl | hz
      · exact hxv
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
        intro h; exact kx2 e he (by simp [h, hvS])
    refine ⟨hv z hzv, fun q w hw => ?_⟩
    have hzw : G.Adj z w := hσ' _ _ _ hw
    rcases kxc z hz w hzw with h | h
    · simp only [Finset.mem_insert, Finset.mem_union] at h ⊢; tauto
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      have h1 := kx2 e he
      have h2 : e.1 ∉ Dy.map Prod.fst := by
        intro h'
        obtain ⟨f, hf, hfe⟩ := List.mem_map.1 h'
        apply ky2 f hf
        rw [hSy, hfe]
        simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_cons,
          List.mem_cons]
        exact Or.inr (Or.inr (Or.inr h))
      have h3 : e.1 ≠ y := fun h' => hc.2.2 (h' ▸ h)
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
        List.mem_cons] at h1 ⊢
      tauto
  refine ⟨Dx, Dy, hD, ?_, ?_, ?_⟩
  · rw [visit_succ, hσ'v, visitList_cons, visitList_cons]
    simp only [visitList_nil, hyS, List.map_nil, List.not_mem_nil, or_false, ↓reduceIte,
      List.nil_append, List.toFinset_nil, Finset.union_empty, hDy', List.map_cons,
      List.mem_cons, hxS, hxy, hxDy, hDx']
  · intro c hc' a hca
    rcases kxc c (by simpa using hc') a hca with h | h
    · simp only [Finset.mem_insert] at h
      simp only [List.map_cons, List.mem_cons]; tauto
    · simp only [List.map_cons, List.mem_cons]; tauto
  · intro c hc' a hca
    rcases kyc c (by simpa using hc') a hca with h | h
    · simp only [hSy, Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at h
      simp only [List.map_cons, List.map_append, List.mem_append, List.mem_cons] at h ⊢; tauto
    · simp only [List.map_cons, List.map_append, List.mem_append, List.mem_cons]; tauto

omit [DecidableEq V] [Fintype V] in
theorem not_mem_map_fst_of_nodup {P Q : List (V × V)} {a : V}
    (h : ((P ++ Q).map Prod.fst).Nodup) (ha : a ∈ P.map Prod.fst) : a ∉ Q.map Prod.fst := by
  rw [List.map_append, List.nodup_append] at h
  exact fun hb => h.2.2 a ha a hb rfl

omit [Fintype V] in
theorem mem_of_mem_insert_or {S : Finset V} {L A : List (V × V)} {w u z : V}
    (h : z ∈ insert w (S ∪ (L.map Prod.fst).toFinset) ∨ z ∈ A.map Prod.fst) :
    z ∈ S ∨ z ∈ (L ++ (w, u) :: A).map Prod.fst := by
  simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.map_append,
    List.map_cons, List.mem_append, List.mem_cons] at h ⊢
  tauto

/-- In a run `F` whose block of `w` contains `v`, every pair of `F` with parent `v` lies in that
block. -/
theorem mem_block_of_mem {σ : V → V → List V} (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p)
    {n : ℕ} {u v : V} {S : Finset V} (hu : u ∈ S) (hn : Sᶜ.card < n + 1) (huv : u ≠ v)
    {F : List (V × V)} (F1 : (F.map Prod.fst).Nodup) (F2 : ∀ e ∈ F, e.1 ∉ S)
    (F4 : F.Pairwise (fun e f => e.2 ≠ f.1)) (Fadj : ∀ e ∈ F, G.Adj e.2 e.1)
    (L M : List (V × V)) (w : V) (hwS : w ∉ S)
    (hFe : F = L ++ (w, u) :: visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) ++ M)
    (hvD : v = w ∨ v ∈ (visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))).map Prod.fst)
    (t : V) (ht : (t, v) ∈ F) :
    (t, v) ∈ visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) := by
  set D := visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) with hD
  have hFe' := hFe
  rw [hFe] at ht
  simp only [List.mem_append, List.mem_cons] at ht
  rcases ht with (ht | ht | ht) | ht
  · exfalso
    rw [hFe, List.append_assoc] at F4
    have := (List.pairwise_append.1 F4).2.2 _ ht
    rcases hvD with hvw | hvD
    · exact this (w, u) (by simp) hvw
    · obtain ⟨e, he, hev⟩ := List.mem_map.1 hvD
      exact this e (by simp [he]) hev.symm
  · exact absurd (Prod.mk.inj ht).2 huv.symm
  · exact ht
  · exfalso
    have hadj : G.Adj v t := Fadj (t, v) (by rw [hFe]; exact List.mem_append_right _ ht)
    have hcl := visit_closure hσ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
      (Finset.mem_insert_self _ _) (by simp [hu]) (card_compl_insert_lt hwS hn) v hvD t hadj
    have htM : t ∈ M.map Prod.fst := List.mem_map.2 ⟨_, ht, rfl⟩
    have hF1 := F1
    rw [hFe] at hF1
    rcases hcl with h | h
    · simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at h
      rcases h with h | h | h
      · exact not_mem_map_fst_of_nodup hF1 (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto) htM
      · exact F2 (t, v) (by rw [hFe]; exact List.mem_append_right _ ht) h
      · exact not_mem_map_fst_of_nodup hF1 (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto) htM
    · exact not_mem_map_fst_of_nodup hF1 (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto) htM

/-- **Pivot decomposition.** Let `σ'` agree with `σ` except at `v`, where it reverses every
candidate list of length two. If a run discovers `x ≠ y` both as children of `v` (with `v` not the
start vertex), then the two runs are `L₁ ++ M₁ ++ M₂ ++ L₂` and `L₁ ++ M₂ ++ M₁ ++ L₂`, where
`M₁, M₂` are the blocks of `x` and `y`, each closed under adjacency once finished. -/
theorem visit_swap_decomposition {σ σ' : V → V → List V}
    (hσ : ∀ u p w, G.Adj u w → w ≠ p → w ∈ σ u p) (hσ' : ∀ u p w, w ∈ σ u p → G.Adj u w)
    {v x y : V} (hxy : x ≠ y) (hv : ∀ z, z ≠ v → ∀ q, σ' z q = σ z q)
    (hlen : ∀ q, G.Adj q v → (σ v q).length ≤ 2)
    (hrev : ∀ q, G.Adj q v → 2 ≤ (σ v q).length → σ' v q = (σ v q).reverse) :
    ∀ (n : ℕ) (p u : V) (S : Finset V), u ∈ S → p ∈ S → Sᶜ.card < n → u ≠ v →
    (x, v) ∈ visit σ n p u S → (y, v) ∈ visit σ n p u S →
    ∃ L₁ M₁ M₂ L₂ : List (V × V), ∃ a₁ a₂ : V, ((a₁ = x ∧ a₂ = y) ∨ (a₁ = y ∧ a₂ = x)) ∧
      M₁.head? = some (a₁, v) ∧ M₂.head? = some (a₂, v) ∧
      visit σ n p u S = L₁ ++ M₁ ++ M₂ ++ L₂ ∧ visit σ' n p u S = L₁ ++ M₂ ++ M₁ ++ L₂ ∧
      (∀ c ∈ M₁.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁).map Prod.fst) ∧
      (∀ c ∈ M₂.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁ ++ M₂).map Prod.fst)
  | 0, _, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, u, S, hu, hp, hn, huv, hx, hy => by
    obtain ⟨F1, F2, F3, F4⟩ := visit_wf σ (n + 1) p u S hu
    have Fadj := visit_adj hσ' (n + 1) p u S
    rw [visit_succ] at hx hy F1 F2 F3 F4 Fadj ⊢
    rw [visit_succ, hv u huv p]
    set F := visitList (visit σ n) u S (σ u p) [] with hF
    let Dec : List (V × V) → List (V × V) → Prop := fun L L' =>
      ∃ L₁ M₁ M₂ L₂ : List (V × V), ∃ a₁ a₂ : V, ((a₁ = x ∧ a₂ = y) ∨ (a₁ = y ∧ a₂ = x)) ∧
      M₁.head? = some (a₁, v) ∧ M₂.head? = some (a₂, v) ∧
      L = L₁ ++ M₁ ++ M₂ ++ L₂ ∧ L' = L₁ ++ M₂ ++ M₁ ++ L₂ ∧
      (∀ c ∈ M₁.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁).map Prod.fst) ∧
      (∀ c ∈ M₂.map Prod.fst, ∀ a, G.Adj c a → a ∈ S ∨ a ∈ (L₁ ++ M₁ ++ M₂).map Prod.fst)
    have inBlock := fun L M w hwS (_ : w ∉ L.map Prod.fst) hFe hvD t ht =>
      mem_block_of_mem hσ hu hn huv F1 F2 F4 Fadj L M w hwS hFe hvD t ht
    have key : ∀ (ws : List V), (∀ w ∈ ws, w ∈ σ u p) → ∀ (L L' : List (V × V)),
        visitList (visit σ n) u S ws L = F →
        ((L' = L ∧ v ∉ L.map Prod.fst) ∨ Dec L L') →
        ((visitList (visit σ' n) u S ws L' = visitList (visit σ n) u S ws L ∧
          v ∉ (visitList (visit σ n) u S ws L).map Prod.fst) ∨
          Dec (visitList (visit σ n) u S ws L) (visitList (visit σ' n) u S ws L')) := by
      intro ws
      induction ws with
      | nil => intro _ L L' _ h; exact h
      | cons w ws ih =>
        intro hws L L' hfin hR
        rw [visitList_cons] at hfin ⊢
        rw [visitList_cons]
        apply ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) _ _ hfin
        obtain ⟨M, hM⟩ := exists_visitList_eq_append (visit σ n) u S ws
          (if w ∈ S ∨ w ∈ L.map Prod.fst then L
            else L ++ (w, u) :: visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)))
        rw [hfin] at hM
        rcases hR with ⟨hLL, hvL⟩ | ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, hL, hL', hc₁, hc₂⟩
        · rw [hLL]
          by_cases hc : w ∈ S ∨ w ∈ L.map Prod.fst
          · simp only [hc, ↓reduceIte]
            exact Or.inl ⟨by simp, hvL⟩
          · simp only [hc, ↓reduceIte] at hM ⊢
            simp only [not_or] at hc
            set Sw := insert w (S ∪ (L.map Prod.fst).toFinset) with hSw
            set D := visit σ n u w Sw with hD
            have hwSw : w ∈ Sw := Finset.mem_insert_self _ _
            have huSw : u ∈ Sw := by simp [hSw, hu]
            obtain ⟨-, kd2, -, -⟩ := visit_wf σ n u w Sw hwSw
            have hFe : F = L ++ (w, u) :: D ++ M := by rw [hM]
            by_cases hvw : v = w
            · -- the block of `v` itself
              have hxD := inBlock L M w hc.1 hc.2 hFe (Or.inl hvw) x hx
              have hyD := inBlock L M w hc.1 hc.2 hFe (Or.inl hvw) y hy
              subst hvw
              cases n with
              | zero => simp at hxD
              | succ m =>
                have huv' : G.Adj u v := hσ' u p v (hws v List.mem_cons_self)
                have hxσ := mem_of_mem_visit σ (m + 1) u v x Sw hwSw hxD
                have hyσ := mem_of_mem_visit σ (m + 1) u v y Sw hwSw hyD
                have hfuel : Swᶜ.card < m + 1 := card_compl_insert_lt hc.1 hn
                have hcl : ∀ (a b : V) (t₁ t₂ : List (V × V)),
                    (∀ c ∈ ((a, v) :: t₁).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ Sw ∨ z ∈ ((a, v) :: t₁).map Prod.fst) →
                    (∀ c ∈ ((b, v) :: t₂).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ Sw ∨ z ∈ ((a, v) :: t₁ ++ (b, v) :: t₂).map Prod.fst) →
                    (∀ c ∈ ((a, v) :: t₁).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ S ∨ z ∈ ((L ++ [(v, u)]) ++ (a, v) :: t₁).map Prod.fst) ∧
                    (∀ c ∈ ((b, v) :: t₂).map Prod.fst, ∀ z, G.Adj c z →
                      z ∈ S ∨ z ∈ ((L ++ [(v, u)]) ++ (a, v) :: t₁ ++ (b, v) :: t₂).map
                        Prod.fst) := by
                  intro a b t₁ t₂ h₁ h₂
                  refine ⟨fun c hc z hz => ?_, fun c hc z hz => ?_⟩
                  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
                      mem_of_mem_insert_or (u := u) (h₁ c hc z hz)
                  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
                      mem_of_mem_insert_or (u := u) (h₂ c hc z hz)
                rcases eq_pair_or_eq_pair_of_length_le_two (hlen u huv') hxσ hyσ hxy
                  with h | h
                · have h' : σ' v u = [y, x] := by rw [hrev u huv' (by simp [h]), h]; rfl
                  obtain ⟨t₁, t₂, e₁, e₂, c₁, c₂⟩ :=
                    visit_swap_at hσ hσ' hv hxy hwSw hfuel h h' hxD hyD
                  obtain ⟨d₁, d₂⟩ := hcl x y t₁ t₂ c₁ c₂
                  refine Or.inr ⟨L ++ [(v, u)], (x, v) :: t₁, (y, v) :: t₂, [], x, y,
                    Or.inl ⟨rfl, rfl⟩, rfl, rfl, ?_, ?_, d₁, d₂⟩
                  · rw [hD, e₁]; simp
                  · rw [e₂]; simp
                · have h' : σ' v u = [x, y] := by rw [hrev u huv' (by simp [h]), h]; rfl
                  obtain ⟨t₁, t₂, e₁, e₂, c₁, c₂⟩ :=
                    visit_swap_at hσ hσ' hv hxy.symm hwSw hfuel h h' hyD hxD
                  obtain ⟨d₁, d₂⟩ := hcl y x t₁ t₂ c₁ c₂
                  refine Or.inr ⟨L ++ [(v, u)], (y, v) :: t₁, (x, v) :: t₂, [], y, x,
                    Or.inr ⟨rfl, rfl⟩, rfl, rfl, ?_, ?_, d₁, d₂⟩
                  · rw [hD, e₁]; simp
                  · rw [e₂]; simp
            · by_cases hvD : v ∈ D.map Prod.fst
              · have hxD := inBlock L M w hc.1 hc.2 hFe (Or.inr hvD) x hx
                have hyD := inBlock L M w hc.1 hc.2 hFe (Or.inr hvD) y hy
                obtain ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, e₁, e₂, c₁, c₂⟩ :=
                  visit_swap_decomposition hσ hσ' hxy hv hlen hrev n u w Sw hwSw huSw
                    (card_compl_insert_lt hc.1 hn) (Ne.symm hvw) hxD hyD
                refine Or.inr ⟨L ++ (w, u) :: L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, ?_, ?_, ?_, ?_⟩
                · rw [hD, e₁]; simp
                · rw [e₂]; simp
                · intro c hc z hz
                  simpa only [List.append_assoc, List.cons_append] using
                    mem_of_mem_insert_or (u := u) (c₁ c hc z hz)
                · intro c hc z hz
                  simpa only [List.append_assoc, List.cons_append] using
                    mem_of_mem_insert_or (u := u) (c₂ c hc z hz)
              · have hDD : visit σ' n u w Sw = D := by
                  apply visit_congr
                  intro z hz
                  refine ⟨hv z ?_, fun _ _ _ => Iff.rfl⟩
                  rcases hz with rfl | hz
                  · exact Ne.symm hvw
                  · exact fun h => hvD (h ▸ hz)
                rw [hDD]
                refine Or.inl ⟨rfl, ?_⟩
                simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
                tauto
        · -- the pivot has already happened
          have hvs : ∀ a, a ∈ L'.map Prod.fst ↔ a ∈ L.map Prod.fst := by
            intro a; rw [hL, hL']
            simp only [List.map_append, List.mem_append]; tauto
          have hvL : v ∈ L.map Prod.fst := by
            have ha₁ : (a₁, v) ∈ L := by
              rw [hL]; cases M₁ with
              | nil => simp at hM₁
              | cons m M₁ => simp only [List.head?_cons, Option.some.injEq] at hM₁; simp [hM₁]
            have hFL : ∃ X, F = L ++ X := by
              split_ifs at hM
              · exact ⟨M, hM⟩
              · exact ⟨_, by rw [hM, List.append_assoc]⟩
            obtain ⟨X, hX⟩ := hFL
            rcases F3 (a₁, v) (by rw [hX]; exact List.mem_append_left _ ha₁) with h | h
            · exact absurd h huv.symm
            · rw [hX] at h F4
              simp only [List.map_append, List.mem_append] at h
              rcases h with h | h
              · exact h
              · exfalso
                obtain ⟨e, he, hev⟩ := List.mem_map.1 h
                exact (List.pairwise_append.1 F4).2.2 _ ha₁ e he hev.symm
          have hc' : (w ∈ S ∨ w ∈ L'.map Prod.fst) ↔ (w ∈ S ∨ w ∈ L.map Prod.fst) := by
            rw [hvs]
          by_cases hc : w ∈ S ∨ w ∈ L.map Prod.fst
          · simp only [hc, hc'.2 hc, ↓reduceIte]
            exact Or.inr ⟨L₁, M₁, M₂, L₂, a₁, a₂, ha, hM₁, hM₂, hL, hL', hc₁, hc₂⟩
          · have hcn : ¬ (w ∈ S ∨ w ∈ L'.map Prod.fst) := fun h => hc (hc'.1 h)
            simp only [hc, hcn, ↓reduceIte]
            simp only [not_or] at hc
            have hSS : insert w (S ∪ (L'.map Prod.fst).toFinset) =
                insert w (S ∪ (L.map Prod.fst).toFinset) := by
              ext a; simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, hvs]
            have hwv : w ≠ v := fun h => hc.2 (h ▸ hvL)
            obtain ⟨-, kd2, -, -⟩ := visit_wf σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset))
              (Finset.mem_insert_self _ _)
            have hDD : visit σ' n u w (insert w (S ∪ (L'.map Prod.fst).toFinset)) =
                visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)) := by
              rw [hSS]
              apply visit_congr
              intro z hz
              refine ⟨hv z ?_, fun _ _ _ => Iff.rfl⟩
              rcases hz with rfl | hz
              · exact hwv
              · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
                intro h; exact kd2 e he (by simp [h, hvL])
            rw [hDD]
            refine Or.inr ⟨L₁, M₁, M₂, L₂ ++ (w, u) ::
              visit σ n u w (insert w (S ∪ (L.map Prod.fst).toFinset)), a₁, a₂, ha, hM₁, hM₂,
              ?_, ?_, hc₁, hc₂⟩
            · rw [hL]; simp
            · rw [hL']; simp
    rcases key (σ u p) (fun _ h => h) [] [] rfl (Or.inl ⟨rfl, by simp⟩) with ⟨-, hvF⟩ | h
    · exfalso
      rcases F3 (x, v) hx with h | h
      · exact huv h.symm
      · exact hvF h
    · exact h

end DFS
end PercLib
