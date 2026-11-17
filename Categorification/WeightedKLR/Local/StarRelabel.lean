/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Geometry.SupportMinimum
import Categorification.WeightedKLR.RedStrands.ViolatingComparison

/-!
# Relabelling incident chambers

Supporting geometry for the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19,
roadmap A. Incidence with a closed chamber is equivariant under colour-preserving
strand permutations. A chamber and an incident configuration can therefore be
relabelled together to make the chamber rank ordered. These supporting lemmas
are not statements printed in the source.
-/

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

namespace FullChamber

omit [DecidableEq I] in
/-- Relabelling a closed chamber and a configuration preserves incidence. -/
theorem Incident.smul {C : FullChamber Γ ν} {p : Strand ν → 𝕜}
    (hp : C.Incident p) (g : ColPerm ν) : (g • C).Incident (act g p) := by
  intro h
  have hh := hp (h.comap g)
  change (if signMap g C.1 h then 0 ≤ h.val (act g p) else h.val (act g p) ≤ 0)
  rw [Hyp.val_act]
  simp only [signMap]
  by_cases hr : h.reverses g = true <;> by_cases hc : C.1 (h.comap g) = true <;>
    simp_all

omit [DecidableEq I] in
/-- Incidence is equivariant under strand relabelling. -/
theorem incident_smul_iff (g : ColPerm ν) (C : FullChamber Γ ν)
    (p : Strand ν → 𝕜) : (g • C).Incident (act g p) ↔ C.Incident p := by
  constructor
  · intro hp
    have hi := hp.smul g⁻¹
    simpa only [inv_smul_smul, ← act_mul, inv_mul_cancel, act_one] using hi
  · exact fun hp => hp.smul g

omit [DecidableEq I] in
/-- The same relabelling makes a chamber rank ordered and transports an incident
configuration into its closed chamber. -/
theorem exists_smul_rankOrdered_incident (C : FullChamber Γ ν) (p : Strand ν → 𝕜)
    (hp : C.Incident p) :
    ∃ g : ColPerm ν, (g • C).IsRankOrdered ∧ (g • C).Incident (act g p) := by
  obtain ⟨q, hq, hC⟩ := C.property
  obtain ⟨g, hg⟩ := exists_act_rankOrdered hq
  refine ⟨g, ?_, hp.smul g⟩
  intro d
  change signMap g C.1 (.inr d) = true
  rw [← hC, ← fullSigns_act hq]
  exact decide_eq_true (hg d)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- An incident configuration has weakly increasing coordinates of each colour
when the chamber is rank ordered. -/
theorem Incident.diag_nonneg {C : FullChamber Γ ν} {p : Strand ν → 𝕜}
    (hp : C.Incident p) (hC : C.IsRankOrdered) (d : Diag ν) : 0 ≤ d.val p := by
  have hh := hp (.inr d)
  simpa only [hC d, ite_true, Hyp.val_inr] using hh

end FullChamber

open Categorification.WeightedKLR.Geometry

omit [DecidableEq I] in
/-- The minimum-norm property on a permutation-invariant support is preserved by
the same permutation. -/
theorem support_squaredNorm_minimum_smul (S : Set (FullChamber Γ ν))
    (hS : ∀ g : ColPerm ν, ∀ C ∈ S, g • C ∈ S) {p : Strand ν → 𝕜}
    (hmin : ∀ C ∈ S, ∀ x : Strand ν → 𝕜, C.Incident x → squaredNorm p ≤ squaredNorm x)
    (g : ColPerm ν) :
    ∀ C ∈ S, ∀ x : Strand ν → 𝕜, C.Incident x →
      squaredNorm (act g p) ≤ squaredNorm x := by
  intro C hC x hx
  have hi := hmin (g⁻¹ • C) (hS g⁻¹ C hC) (act g⁻¹ x) (hx.smul g⁻¹)
  simpa only [squaredNorm_act] using hi

/-- A nonempty permutation-invariant support has a minimum-norm configuration
incident to a rank-ordered supported chamber. -/
theorem exists_rankOrdered_support_squaredNorm_minimum (S : Set (FullChamber Γ ν))
    (hne : S.Nonempty) (hS : ∀ g : ColPerm ν, ∀ C ∈ S, g • C ∈ S) :
    ∃ p : Strand ν → 𝕜, ∃ C ∈ S, C.IsRankOrdered ∧ C.Incident p ∧
      ∀ D ∈ S, ∀ x : Strand ν → 𝕜, D.Incident x → squaredNorm p ≤ squaredNorm x := by
  obtain ⟨p, C, hC, hp, hmin⟩ := exists_support_squaredNorm_minimum S hne
  obtain ⟨g, hg, hp'⟩ := C.exists_smul_rankOrdered_incident p hp
  exact ⟨act g p, g • C, hS g C hC, hg, hp', support_squaredNorm_minimum_smul S hS hmin g⟩

end Categorification.WeightedKLR
