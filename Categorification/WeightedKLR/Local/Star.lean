/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GallerySpan.Bridge
import Categorification.WeightedKLR.Segment.Perturb

/-!
# Chambers incident to a configuration

The local-chamber argument for Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19, roadmap A, uses the closed chambers containing a
configuration. We express incidence by weak affine inequalities, so that no
topological completeness assumption on the position field is needed. These are
supporting geometric lemmas for the local-chart argument, not statements printed
in the source.
-/

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

namespace FullChamber

/-- The closed chamber contains the configuration, expressed by weak inequalities. -/
def Incident (C : FullChamber Γ ν) (p : Strand ν → 𝕜) : Prop :=
  ∀ h : Hyp Γ ν, if C.1 h then 0 ≤ h.val p else h.val p ≤ 0

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem incident_of_signs {C : FullChamber Γ ν} {p : Strand ν → 𝕜}
    (hC : fullSigns p = C.1) : C.Incident p := by
  intro h
  rw [← hC]
  simp only [fullSigns, decide_eq_true_eq]
  split_ifs with hpos
  · exact hpos.le
  · exact le_of_not_gt hpos

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Away from a hyperplane, incidence determines its chamber sign. -/
theorem Incident.sign_eq {C : FullChamber Γ ν} {p : Strand ν → 𝕜}
    (hp : C.Incident p) (h : Hyp Γ ν) (hne : h.val p ≠ 0) :
    C.1 h = decide (0 < h.val p) := by
  have hh := hp h
  cases hs : C.1 h <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hh ⊢
  · exact (decide_eq_false (not_lt_of_ge hh)).symm
  · exact (decide_eq_true (lt_of_le_of_ne hh (Ne.symm hne))).symm

omit [DecidableEq I] in
/-- Closed chambers are convex over the ordered position field. -/
theorem Incident.segPt {C : FullChamber Γ ν} {p q : Strand ν → 𝕜}
    (hp : C.Incident p) (hq : C.Incident q) {t : 𝕜} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    C.Incident (Segment.segPt p q t) := by
  intro h
  have he := Segment.apply_segPt (f := hypAff (Γ := Γ)) h p q t
  change h.val (Segment.segPt p q t) = h.val p + t * (h.val q - h.val p) at he
  have hp' := hp h
  have hq' := hq h
  cases hs : C.1 h <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hp' hq' ⊢
  · rw [he]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 hp'),
      mul_nonneg ht0 (neg_nonneg.2 hq')]
  · rw [he]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) hp', mul_nonneg ht0 hq']

omit [DecidableEq I] in
/-- Moving from a closed-chamber point toward an interior point immediately enters
that chamber. -/
theorem Incident.generic_segPt {C : FullChamber Γ ν} {p q : Strand ν → 𝕜}
    (hp : C.Incident p) (hq : IsGeneric Γ q) (hC : fullSigns q = C.1)
    {t : 𝕜} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    IsGeneric Γ (Segment.segPt p q t) ∧ fullSigns (Segment.segPt p q t) = C.1 := by
  have hs : ∀ h : Hyp Γ ν, if C.1 h then 0 < h.val (Segment.segPt p q t)
      else h.val (Segment.segPt p q t) < 0 := by
    intro h
    have he := Segment.apply_segPt (f := hypAff (Γ := Γ)) h p q t
    change h.val (Segment.segPt p q t) = h.val p + t * (h.val q - h.val p) at he
    have hp' := hp h
    have hq' := congrFun hC h
    simp only [fullSigns] at hq'
    cases hc : C.1 h <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at hp' hq' ⊢
    · have hqneg : h.val q < 0 := lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false hq')) (hq h)
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 hp'),
        mul_pos ht0 (neg_pos.2 hqneg)]
    · have hqpos : 0 < h.val q := of_decide_eq_true hq'
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) hp', mul_pos ht0 hqpos]
  constructor
  · intro h
    have hh := hs h
    cases hc : C.1 h <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at hh
    · exact hh.ne
    · exact hh.ne'
  · funext h
    have hh := hs h
    cases hc : C.1 h <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at hh ⊢
    · exact decide_eq_false (not_lt_of_ge hh.le)
    · exact decide_eq_true hh

end FullChamber

end Categorification.WeightedKLR
