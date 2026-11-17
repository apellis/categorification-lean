/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ScalarK0
import Categorification.KLR.CyclotomicAbsentColour
import Categorification.KLR.CyclotomicGrading

/-!
# The first lowering of the cyclotomic highest weight

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§3.4, Proposition 3.21, and Kang–Kashiwara, arXiv:1102.4677v4, Theorem 6.2:
at weight `Λ - αᵢ` with `Λᵢ > 0` the regular projective freely generates graded
projective `K₀`. The one-strand algebra is `k[X]/(X^Λᵢ)`, whose only idempotents
are zero and one. Every indecomposable graded projective is therefore a shift of
its regular module.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded Polynomial

variable {k : Type*} [Field k]

private theorem rootPower_idempotent {n : ℕ} (hn : n ≠ 0)
    {z : AdjoinRoot (X ^ n : k[X])} (hz : IsIdempotentElem z) : z = 0 ∨ z = 1 := by
  let ε := AdjoinRoot.lift (f := (X ^ n : k[X])) (RingHom.id k) (0 : k)
    (by simp [hn])
  have nil_ker : ∀ w, ε w = 0 → IsNilpotent w := by
    intro w hw
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective w
    have hp : p.coeff 0 = 0 := by
      simpa [ε, AdjoinRoot.lift_mk, Polynomial.coeff_zero_eq_eval_zero] using hw
    obtain ⟨t, rfl⟩ := X_dvd_iff.mpr hp
    refine ⟨n, ?_⟩
    rw [map_mul, mul_pow, ← map_pow, AdjoinRoot.mk_self, zero_mul]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (hz.map ε)) with h | h
  · exact Or.inl (hz.eq_zero_of_isNilpotent (nil_ker z h))
  · exact Or.inr (sub_eq_zero.mp (hz.one_sub.eq_zero_of_isNilpotent
      (nil_ker (1 - z) (by rw [map_sub, map_one, h, sub_self])))).symm

variable {I : Type*} [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I)

local notation "aΛ" => (fun j => (X : k[X]) ^ Λ j)
local notation "S" => CycKLR k Q aΛ (Singleton.singleton i : Multiset I)

/-- With zero cyclotomic multiplicity the first lowering block vanishes
(Webster, arXiv:1309.3796v2, Definition 3.3 and Proposition 3.21). -/
theorem singleK0_eq_zero (hi : Λ i = 0) (x : K0 (grade G Λ {i})) : x = 0 := by
  let e := cyclotomicSingleFinEquiv Q i aΛ (monic_X_pow _)
  have hdeg : (aΛ i).natDegree = 0 := by simp [hi]
  let : IsEmpty (Fin (aΛ i).natDegree) := ⟨fun d => by have := d.isLt; omega⟩
  let : Subsingleton S := e.symm.injective.subsingleton
  induction x using K0.induction_on with
  | of P =>
    let := Module.subsingleton S P.carrier
    exact K0.of_eq_zero_of_subsingleton P
  | zero => rfl
  | add _ _ hx hy => simp [hx, hy]
  | neg _ hx => simp [hx]

private theorem regular_isIndec_single (hi : 0 < Λ i) :
    (GProj.regular (grade G Λ {i})).IsIndec S := by
  let e := cyclotomicSingleEquiv Q i aΛ
  let ε := AdjoinRoot.lift (f := (X ^ Λ i : k[X])) (RingHom.id k) (0 : k)
    (by simp [hi.ne'])
  let : Nontrivial S := (ε.comp e.toRingHom).domain_nontrivial
  refine ⟨inferInstanceAs (Nontrivial S), ?_⟩
  change ∀ f : Module.End S S, f ∈ endZero S (grade G Λ {i}) → IsIdempotentElem f → f = 0 ∨ f = 1
  intro f _ hf
  have he := rootPower_idempotent hi.ne'
    (((LinearMap.isIdempotentElem_map_one_iff (f := f)).2 hf).map e)
  have h : f (1 : S) = 0 ∨ f (1 : S) = 1 :=
    he.imp (fun h => e.injective (h.trans (map_zero e).symm))
      (fun h => e.injective (h.trans (map_one e).symm))
  have hf_apply (a : S) : f a = a • f (1 : S) := by rw [← f.map_smul]; simp
  rcases h with h | h
  · exact Or.inl (LinearMap.ext fun a => by simp [hf_apply a, h])
  · exact Or.inr (LinearMap.ext fun a => by simp [hf_apply a, h])

/-- The projective Grothendieck group of the first lowering block of Webster's
Proposition 3.21 (arXiv:1309.3796v2) is free of rank one when `Λᵢ > 0`. -/
def singleK0Equiv (hi : 0 < Λ i) :
    K0 (grade G Λ {i}) ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ := by
  let e := cyclotomicSingleFinEquiv Q i aΛ (monic_X_pow _)
  letI : FiniteDimensional k S := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  letI := HasGdim.of_finiteDimensional (grade G Λ {i})
  exact regularK0Equiv _ (regular_isIndec_single G Λ i hi)

@[simp] theorem singleK0Equiv_regular (hi : 0 < Λ i) :
    singleK0Equiv G Λ i hi (K0.of (GProj.regular (grade G Λ {i}))) = 1 := by
  apply (singleK0Equiv G Λ i hi).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (one_smul (LaurentPolynomial ℤ) (K0.of (GProj.regular (grade G Λ {i})))).symm

end Categorification.KLR.CycKLR
