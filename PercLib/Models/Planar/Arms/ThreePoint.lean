/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied.
Mathematical reference: H. Duminil-Copin, Introduction to Bernoulli percolation, lecture notes,
7 October 2018, Section 4, Corollary 4.7 (circuits in annuli and the one-arm bounds, pp. 23-24).
The three-point construction follows the proof in the PercLib wiki article critical-exponents,
section "Three points at two scales".
-/
module

public import PercLib.Models.Planar.Arms.TwoPoint

/-!
# A lower bound for the three-point function at the self-dual point of `ℤ²`

At the self-dual point, where every nearest-neighbour edge of `ℤ²` is open with probability
`1/2`, the probability `t(a, b, c)` that three points lie in one open cluster, the event
`conn a b ∩ conn a c`, is bounded below at two scales (the lower half of wiki tag K8A1, "Three
points at two scales"): there is `c₃ > 0` such that, with `s = ‖a - b‖∞` and `R = ‖a - c‖∞`,
`c₃ π(s) π(R)² ≤ t(a, b, c)` whenever `a ≠ b` and `s ≤ R`. Here `π(r)` is the probability of
`armEvent 0 r` of `Arms/Defs.lean`, and `‖a - b‖∞` is written
`max (a 0 - b 0).natAbs (a 1 - b 1).natAbs`.

* **The construction** (`law_armEvent_mul_law_fourStrip_le_law_conn_inter_conn`). Arms of radius
  `8s` at `b` and `8R` at `a` and at `c`, and the four-strip events of the annuli
  `2s ≤ ‖· - a‖∞ ≤ 4s` and `2R ≤ ‖· - a‖∞ ≤ 4R`. The first four-strip event joins `a` to `b`
  and the second joins `a` to `c` (`inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent`,
  `Arms/TwoPoint.lean`). The five events are increasing, so Harris's inequality
  (`prodBernoulli_harris`, tag X5SS) bounds `t(a, b, c)` below by the product of their
  probabilities; the arms at `a`, `b`, `c` have the probabilities of arms at the origin
  (`law_armEvent_eq_law_armEvent_zero`).
* **The bound** (`exists_le_law_conn_inter_conn`). The circuit bound
  (`exists_pos_le_law_fourStrip`, `c₀`) and three doublings at each arm scale
  (`exists_pos_mul_law_armEvent_le_eight_mul`: `π(8r) ≥ c³ π(r)`, with `c` the doubling constant
  of XB1U) give `t(a, b, c) ≥ c₀² π(8s) π(8R)² ≥ c₀² c⁹ π(s) π(R)²`.

In K8A1 the three points are distinct and labelled so that `s` is the smallest and `R` the
largest pair distance; then `a ≠ b` and `s ≤ R`, so `exists_le_law_conn_inter_conn` is the lower
two-scale bound of K8A1. The case `s = R` needs nothing special. The upper bound of K8A1 rests on
the three-point product inequality of tag 87RB, which this library does not prove.

## Main results

* `PercLib.Models.Planar.exists_le_law_conn_inter_conn`
* `PercLib.Models.Planar.law_armEvent_mul_law_fourStrip_le_law_conn_inter_conn`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond PercLib.Models.Site PercLib.Probability
open scoped ENNReal

namespace PercLib.Models.Planar

/-- **Three points joined through two circuits.** If the profile is constant on the edges of
`ℤ²`, `‖a - b‖∞ ≤ 2n`, `‖a - c‖∞ ≤ 2N` and `n ≤ N`, then the probability that `a`, `b`, `c` lie
in one open cluster is at least `π(8n) π(8N)² P(fourStrip a n) P(fourStrip a N)`: arms of radius
`8n` at `b` and `8N` at `a` and `c`, and the two four-strip events around `a`, join the three
points, and Harris's inequality applies to these five increasing events. -/
theorem law_armEvent_mul_law_fourStrip_le_law_conn_inter_conn
    {q : Sym2 (LatticeSite 2) → unitInterval} {p : ℝ}
    (hq : ∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = p) {a b c : LatticeSite 2} {n N : ℕ}
    (hb : max (a 0 - b 0).natAbs (a 1 - b 1).natAbs ≤ 2 * n)
    (hc : max (a 0 - c 0).natAbs (a 1 - c 1).natAbs ≤ 2 * N) (hnN : n ≤ N) :
    law q (armEvent 0 (8 * n)) * law q (armEvent 0 (8 * N)) ^ 2 * law q (fourStrip a n) *
        law q (fourStrip a N) ≤ law q (conn a b ∩ conn a c) := by
  -- the box memberships for the two circuits
  have hbox : ∀ (v : LatticeSite 2) (k : ℕ), max (a 0 - v 0).natAbs (a 1 - v 1).natAbs ≤ 2 * k →
      v ∈ Icc (a - ((2 * k : ℕ) : LatticeSite 2)) (a + ((2 * k : ℕ) : LatticeSite 2)) := by
    intro v k hv
    rw [mem_Icc_two_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
    omega
  have haa : ∀ k : ℕ, max (a 0 - a 0).natAbs (a 1 - a 1).natAbs ≤ 2 * k := fun k => by
    simp
  set A₁ := armEvent b (8 * n) with hA₁
  set A₂ := armEvent a (8 * N) with hA₂
  set A₃ := armEvent c (8 * N) with hA₃
  set A₄ := fourStrip a n with hA₄
  set A₅ := fourStrip a N with hA₅
  have hsub : A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ ⊆ conn a b ∩ conn a c := by
    rintro ω ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩
    refine ⟨conn_mono inter_subset_left (localConn_subset_conn _ _ _
      (inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent h₄ (hbox a n (haa n))
        (hbox b n hb) (by omega) (by omega) h₂ h₁)), conn_mono inter_subset_left
      (localConn_subset_conn _ _ _ (inter_edgeSet_mem_localConn_of_mem_fourStrip_of_mem_armEvent
        h₅ (hbox a N (haa N)) (hbox c N hc) (by omega) (by omega) h₂ h₃))⟩
  have hu₁ : IsUpperSet A₁ := isUpperSet_armEvent _ _
  have hu₂ : IsUpperSet A₂ := isUpperSet_armEvent _ _
  have hu₃ : IsUpperSet A₃ := isUpperSet_armEvent _ _
  have hu₄ : IsUpperSet A₄ := isUpperSet_fourStrip _ _
  have hu₅ : IsUpperSet A₅ := isUpperSet_fourStrip _ _
  have hm₁ : MeasurableSet A₁ := measurableSet_armEvent _ _
  have hm₂ : MeasurableSet A₂ := measurableSet_armEvent _ _
  have hm₃ : MeasurableSet A₃ := measurableSet_armEvent _ _
  have hm₄ : MeasurableSet A₄ := measurableSet_fourStrip _ _
  have hm₅ : MeasurableSet A₅ := measurableSet_fourStrip _ _
  calc law q (armEvent 0 (8 * n)) * law q (armEvent 0 (8 * N)) ^ 2 * law q A₄ * law q A₅
      = law q A₁ * law q A₂ * law q A₃ * law q A₄ * law q A₅ := by
        rw [hA₁, hA₂, hA₃, law_armEvent_eq_law_armEvent_zero hq b,
          law_armEvent_eq_law_armEvent_zero hq a, law_armEvent_eq_law_armEvent_zero hq c]
        ring
    _ ≤ law q (A₁ ∩ A₂) * law q A₃ * law q A₄ * law q A₅ := by
        gcongr
        exact prodBernoulli_harris q hu₁ hu₂ hm₁ hm₂
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃) * law q A₄ * law q A₅ := by
        gcongr
        exact prodBernoulli_harris q (hu₁.inter hu₂) hu₃ (hm₁.inter hm₂) hm₃
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃ ∩ A₄) * law q A₅ := by
        gcongr
        exact prodBernoulli_harris q ((hu₁.inter hu₂).inter hu₃) hu₄
          ((hm₁.inter hm₂).inter hm₃) hm₄
    _ ≤ law q (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅) :=
        prodBernoulli_harris q (((hu₁.inter hu₂).inter hu₃).inter hu₄) hu₅
          (((hm₁.inter hm₂).inter hm₃).inter hm₄) hm₅
    _ ≤ law q (conn a b ∩ conn a c) := measure_mono hsub

/-- **T7: the three-point lower bound** (the lower half of tag K8A1). At the self-dual point of
`ℤ²` there is `c₃ > 0` such that, for all points `a ≠ b` and `c` with `s = ‖a - b‖∞` at most
`R = ‖a - c‖∞`, the probability that `a`, `b`, `c` lie in one open cluster is at least
`c₃ π(s) π(R)²`, whatever the profile off the edges of `ℤ²`. -/
theorem exists_le_law_conn_inter_conn :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ q : Sym2 (LatticeSite 2) → unitInterval,
      (∀ e ∈ (zdGraph 2).edgeSet, (q e : ℝ) = 1 / 2) →
      ∀ a b c : LatticeSite 2, a ≠ b →
        max (a 0 - b 0).natAbs (a 1 - b 1).natAbs ≤ max (a 0 - c 0).natAbs (a 1 - c 1).natAbs →
        c₃ * (law q).real (armEvent 0 (max (a 0 - b 0).natAbs (a 1 - b 1).natAbs)) *
            (law q).real (armEvent 0 (max (a 0 - c 0).natAbs (a 1 - c 1).natAbs)) ^ 2 ≤
          (law q).real (conn a b ∩ conn a c) := by
  obtain ⟨c₀, hc₀, hc₀q⟩ := exists_pos_le_law_fourStrip
  obtain ⟨κ, hκ, hκq⟩ := exists_pos_mul_law_armEvent_le_eight_mul
  have hc₀' : min c₀ 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set c₁ := (min c₀ 1).toReal with hc₁_def
  have hc₁ : 0 < c₁ := ENNReal.toReal_pos (lt_min hc₀ one_pos).ne' hc₀'
  refine ⟨c₁ ^ 2 * κ ^ 3, by positivity, fun q hq a b c hab hsR => ?_⟩
  set s := max (a 0 - b 0).natAbs (a 1 - b 1).natAbs with hs
  set R := max (a 0 - c 0).natAbs (a 1 - c 1).natAbs with hR
  have hs1 : 1 ≤ s := by
    by_contra h
    exact hab (funext (Fin.forall_fin_two.2 ⟨by omega, by omega⟩))
  have hR1 : 1 ≤ R := hs1.trans hsR
  have hE : law q (armEvent 0 (8 * s)) * law q (armEvent 0 (8 * R)) ^ 2 * min c₀ 1 * min c₀ 1 ≤
      law q (conn a b ∩ conn a c) :=
    (mul_le_mul' (mul_le_mul' le_rfl ((min_le_left _ _).trans (hc₀q q hq a s hs1)))
      ((min_le_left _ _).trans (hc₀q q hq a R hR1))).trans
      (law_armEvent_mul_law_fourStrip_le_law_conn_inter_conn hq (n := s) (N := R)
        (by omega) (by omega) hsR)
  have hE' : (law q).real (armEvent 0 (8 * s)) * (law q).real (armEvent 0 (8 * R)) ^ 2 * c₁ * c₁ ≤
      (law q).real (conn a b ∩ conn a c) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hE
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at h
    exact h
  calc c₁ ^ 2 * κ ^ 3 * (law q).real (armEvent 0 s) * (law q).real (armEvent 0 R) ^ 2 =
        c₁ * c₁ * (κ * (law q).real (armEvent 0 s)) * (κ * (law q).real (armEvent 0 R)) ^ 2 := by
        ring
    _ ≤ c₁ * c₁ * (law q).real (armEvent 0 (8 * s)) * (law q).real (armEvent 0 (8 * R)) ^ 2 := by
        gcongr
        · exact hκq q hq s
        · exact hκq q hq R
    _ = (law q).real (armEvent 0 (8 * s)) * (law q).real (armEvent 0 (8 * R)) ^ 2 * c₁ * c₁ := by
        ring
    _ ≤ (law q).real (conn a b ∩ conn a c) := hE'

end PercLib.Models.Planar
