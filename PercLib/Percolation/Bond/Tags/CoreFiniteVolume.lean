/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Correspondence wrappers for internal events of disjoint domains, exhaustion by induced
domains, and the local Harris corollary.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.DomainIndependence
public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.HarrisLocal

@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Measurable events determined by the internal pairs of pairwise disjoint domains are
mutually independent (the empty family included), and in particular internal connection
events of two disjoint countable domains factor. -/
@[tag "RDX7"]
theorem law_iInter_internal_events_and_localConn (q : Sym2 V → unitInterval) :
    (∀ (m : ℕ) (S : Fin m → Set V), Pairwise (Disjoint on S) →
      ∀ A : Fin m → Set (Config V), (∀ k, MeasurableSet (A k)) →
      (∀ k, ∀ ω ω' : Config V,
        ω ∩ {e | ∀ v ∈ e, v ∈ S k} = ω' ∩ {e | ∀ v ∈ e, v ∈ S k} → (ω ∈ A k ↔ ω' ∈ A k)) →
      law q (⋂ k, A k) = ∏ k, law q (A k)) ∧
    (∀ (S T : Set V) [Countable S] [Countable T], Disjoint S T → ∀ (x y : S) (u v : T),
      law q {ω | ((openGraph ω).induce S).Reachable x y ∧
          ((openGraph ω).induce T).Reachable u v} =
        law q {ω | ((openGraph ω).induce S).Reachable x y} *
          law q {ω | ((openGraph ω).induce T).Reachable u v}) := by
  refine ⟨fun m S hS A hAm hA => ?_, fun S T _ _ hST x y u v =>
    law_localConn_inter_eq_mul q hST x y u v⟩
  have h := law_biInter_of_determined_internalPairs q (Finset.univ : Finset (Fin m))
    (S := S) (by rw [Finset.coe_univ]; exact hS.set_pairwise _) (A := A)
    (fun k _ => hAm k) hA
  simpa only [Finset.mem_univ, iInter_true] using h

/-- Along an increasing sequence of domains covering `V`, the internal clusters increase to
the cluster with volume the supremum; on countable `V` the susceptibility is the supremum of
the internal expected volumes; escape probabilities are the suprema of internal escape
probabilities. -/
@[tag "6QN7"]
theorem induced_domains_recover_cluster (q : Sym2 V → unitInterval) {S : ℕ → Set V}
    (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (x : V) :
    (∀ ω : Config V, Monotone fun n => {y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}) ∧
    (∀ ω : Config V, (⋃ n, {y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}) = cluster ω x) ∧
    (∀ ω : Config V, (cluster ω x).encard = ⨆ n, ({y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard) ∧
    (Countable V → chi q x = ⨆ n, ∫⁻ ω, (({y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard : ℝ≥0∞)
        ∂law q) ∧
    (∀ F : Set V, law q (⋃ y ∈ Fᶜ, conn x y) = ⨆ n, law q {ω | ∃ y ∉ F,
      y ∈ {y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
        ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}}) :=
  ⟨fun ω => monotone_induce_cluster hS ω x, fun ω => iUnion_induce_cluster hS hcover ω x,
    fun ω => encard_cluster_eq_iSup_induce hS hcover ω x,
    fun _ => chi_eq_iSup_lintegral_induce q hS hcover x,
    fun F => escape_eq_iSup_induce q hS hcover x F⟩

/-- Harris's inequality for a connection and an escape event inside a domain `S`, and its
full-graph form. -/
@[tag "EWMP"]
theorem harris_connection_escape_local [Countable V] (q : Sym2 V → unitInterval)
    (S : Set V) (F : Set V) :
    (∀ x y : S,
      law q {ω | ((openGraph ω).induce S).Reachable x y} *
          law q {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable y w} ≤
        law q {ω : Config V | ∃ w : S, (w : V) ∉ F ∧ ((openGraph ω).induce S).Reachable x w}) ∧
    (∀ x y : V, tau q x y * law q (⋃ w ∈ Fᶜ, conn y w) ≤ law q (⋃ w ∈ Fᶜ, conn x w)) :=
  ⟨fun x y => law_localConn_mul_localEscape_le q S x y F,
    fun x y => tau_mul_law_escape_le q x y F⟩

end PercLib.Percolation.Bond
