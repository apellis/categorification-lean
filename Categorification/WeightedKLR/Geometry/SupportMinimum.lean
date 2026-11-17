/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Geometry.PolyhedronMinimum
import Categorification.WeightedKLR.Local.Star

/-!
# Minimum configurations on a chamber support

Supporting geometry for the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19,
roadmap A. These are supporting lemmas rather than statements printed in the source.
A nonempty collection of closed chambers has a point of minimum squared coordinate norm.
The norm is invariant under strand relabelling, and its strict midpoint inequality makes
such a minimum unique within each closed chamber. All results hold over any ordered field.
-/

namespace Categorification.WeightedKLR.Geometry

variable {K ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Permuting the coordinates preserves squared norm. -/
lemma squaredNorm_comp_equiv (e : ι ≃ ι) (x : ι → K) :
    squaredNorm (x ∘ e) = squaredNorm x := by
  exact e.sum_comp (fun i => x i ^ 2)

lemma squaredNorm_eq_zero_iff {x : ι → K} : squaredNorm x = 0 ↔ x = 0 := by
  simpa only [squaredNorm, pow_two, dotProduct] using (dotProduct_self_eq_zero (v := x))

lemma squaredNorm_pos {x : ι → K} (hx : x ≠ 0) : 0 < squaredNorm x :=
  lt_of_le_of_ne (squaredNorm_nonneg x) (Ne.symm fun h => hx (squaredNorm_eq_zero_iff.1 h))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The exact quadratic identity for a point on a segment. -/
lemma squaredNorm_combo (p q : ι → K) (t : K) :
    squaredNorm ((1 - t) • p + t • q) =
      (1 - t) * squaredNorm p + t * squaredNorm q -
        t * (1 - t) * squaredNorm (p - q) := by
  unfold squaredNorm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Distinct vectors of equal squared norm have a midpoint of smaller squared norm. -/
lemma squaredNorm_midpoint_lt {p q : ι → K} (hpq : p ≠ q)
    (hnorm : squaredNorm p = squaredNorm q) :
    squaredNorm (Segment.segPt p q (1 / 2 : K)) < squaredNorm p := by
  have hpos : 0 < squaredNorm (p - q) := squaredNorm_pos (sub_ne_zero.2 hpq)
  have hcombo : Segment.segPt p q (1 / 2 : K) =
      (1 - (1 / 2 : K)) • p + (1 / 2 : K) • q := by
    unfold Segment.segPt
    module
  rw [hcombo, squaredNorm_combo]
  rw [hnorm]
  nlinarith

end Categorification.WeightedKLR.Geometry

namespace Categorification.WeightedKLR

open Categorification.WeightedKLR.Geometry

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Strand relabelling preserves squared coordinate norm. -/
lemma squaredNorm_act (g : ColPerm ν) (p : Strand ν → 𝕜) :
    squaredNorm (act g p) = squaredNorm p :=
  squaredNorm_comp_equiv g.1.symm p

namespace FullChamber

/-- The closed chamber has a minimum-norm point over any ordered field. -/
theorem exists_incident_squaredNorm_minimum (C : FullChamber Γ ν) :
    ∃ p : Strand ν → 𝕜, C.Incident p ∧
      ∀ x : Strand ν → 𝕜, C.Incident x → squaredNorm p ≤ squaredNorm x := by
  classical
  let ℓ : Hyp Γ ν → (Strand ν → 𝕜) →ₗ[𝕜] 𝕜 := fun h =>
    if C.1 h then -(hypAff h).linear else (hypAff h).linear
  let b : Hyp Γ ν → 𝕜 := fun h => if C.1 h then -h.cst else h.cst
  have hiff (x : Strand ν → 𝕜) : C.Incident x ↔ ∀ h, ℓ h x ≤ b h := by
    constructor
    · intro hx h
      have hh := hx h
      rw [Hyp.val_eq] at hh
      dsimp only [ℓ, b]
      split_ifs with hc
      · simp only [hc, ite_true] at hh
        simp only [LinearMap.neg_apply, hypAff_linear_apply]
        linarith
      · simp only [hc, Bool.false_eq_true, ite_false] at hh
        rw [hypAff_linear_apply]
        linarith
    · intro hx h
      have hh := hx h
      rw [Hyp.val_eq]
      dsimp only [ℓ, b] at hh
      split_ifs with hc
      · simp only [hc, ite_true, LinearMap.neg_apply, hypAff_linear_apply] at hh
        linarith
      · simp only [hc, Bool.false_eq_true, ite_false, hypAff_linear_apply] at hh
        linarith
  obtain ⟨y, _, hy⟩ := C.property
  have hy' : C.Incident y := incident_of_signs hy
  obtain ⟨p, hp, hmin⟩ := exists_squaredNorm_minimum ℓ b ⟨y, (hiff y).1 hy'⟩
  exact ⟨p, (hiff p).2 hp, fun x hx => hmin x ((hiff x).1 hx)⟩

omit [DecidableEq I] in
/-- Equal-norm incident points coincide if one minimizes squared norm on the chamber. -/
theorem Incident.eq_of_squaredNorm_eq_of_minimum {C : FullChamber Γ ν}
    {p q : Strand ν → 𝕜} (hp : C.Incident p) (hq : C.Incident q)
    (hnorm : squaredNorm p = squaredNorm q)
    (hmin : ∀ x : Strand ν → 𝕜, C.Incident x → squaredNorm p ≤ squaredNorm x) : p = q := by
  by_contra hpq
  have hmid := hp.segPt hq (t := (1 / 2 : 𝕜)) (by positivity) (by norm_num)
  exact (not_lt_of_ge (hmin _ hmid)) (squaredNorm_midpoint_lt hpq hnorm)

omit [DecidableEq I] in
/-- The point of minimum squared norm in a closed chamber is unique. -/
theorem Incident.eq_of_squaredNorm_minimum {C : FullChamber Γ ν}
    {p q : Strand ν → 𝕜} (hp : C.Incident p) (hq : C.Incident q)
    (hpmin : ∀ x : Strand ν → 𝕜, C.Incident x → squaredNorm p ≤ squaredNorm x)
    (hqmin : ∀ x : Strand ν → 𝕜, C.Incident x → squaredNorm q ≤ squaredNorm x) : p = q :=
  hp.eq_of_squaredNorm_eq_of_minimum hq (le_antisymm (hpmin q hq) (hqmin p hp)) hpmin

end FullChamber

/-- A nonempty support of chambers has a minimum-norm incident configuration. Finiteness of
chambers reduces this to the minimum on each closed chamber. -/
theorem exists_support_squaredNorm_minimum (S : Set (FullChamber Γ ν)) (hS : S.Nonempty) :
    ∃ p : Strand ν → 𝕜, ∃ C ∈ S, C.Incident p ∧
      ∀ D ∈ S, ∀ x : Strand ν → 𝕜, D.Incident x → squaredNorm p ≤ squaredNorm x := by
  classical
  choose p hp hmin using (fun C : FullChamber Γ ν => C.exists_incident_squaredNorm_minimum)
  let support : Finset (FullChamber Γ ν) := Finset.univ.filter fun C => C ∈ S
  have hs : support.Nonempty := by
    obtain ⟨C, hC⟩ := hS
    exact ⟨C, Finset.mem_filter.2 ⟨Finset.mem_univ _, hC⟩⟩
  obtain ⟨C, hC, hleast⟩ := support.exists_min_image (fun C => squaredNorm (p C)) hs
  refine ⟨p C, C, (Finset.mem_filter.1 hC).2, hp C, ?_⟩
  intro D hD x hx
  exact (hleast D (Finset.mem_filter.2 ⟨Finset.mem_univ _, hD⟩)).trans (hmin D x hx)

end Categorification.WeightedKLR
