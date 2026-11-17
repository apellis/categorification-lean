/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedInduction
import Categorification.Algebra.Graded.IdempotentLift

/-!
# Graded extension of scalars on projective Grothendieck groups

In the projective generation arguments of Webster, arXiv:1309.3796v2,
Proposition 3.21 and Lemma 4.37, extension of scalars takes the left ideal
of a homogeneous idempotent to the left ideal of its image.
-/

noncomputable section
namespace Categorification.Graded

open MulOpposite

universe u

variable {k : Type*} {A C : Type u} [CommRing k] [Ring A] [Algebra k A] [Ring C] [Algebra k C]
  (𝒜 : ℤ → Submodule k A) (ℬ : ℤ → Submodule k C) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (π : A →ₐ[k] C) (hπ : PreservesGrading 𝒜 ℬ π.toLinearMap)

variable [Module Aᵐᵒᵖ C] [SMulCommClass C Aᵐᵒᵖ C] [IsScalarTower k Aᵐᵒᵖ C]
  (hact : ∀ (a : A) (c : C), op a • c = c * π a)

/-- Extension of a graded projective along a degree-preserving algebra map. -/
def extensionProj (P : GProj 𝒜) : GProj ℬ where
  carrier := BalancedTensor k C A C P.carrier
  grading := balancedGrading C A ℬ P.grading
  decomposition := balancedDecomposition 𝒜 fun _ _ _ _ hm ha =>
    (hact _ _).symm ▸ SetLike.GradedMul.mul_mem (A := ℬ) hm (hπ ha)
  gradedSMul := gradedSMul_balanced ℬ
  finite := BalancedTensor.finite
  projective := BalancedTensor.projective

private def quotientCongr {P P' : GProj 𝒜} (e : P.Iso P') :
    (extensionProj 𝒜 ℬ π hπ hact P).Iso (extensionProj 𝒜 ℬ π hπ hact P') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight e.toLinearEquiv)
    (fun _ _ hy => mapRight_mem_balancedGrading (ℳ := ℬ) e.preservesGrading hy)

private def quotientProd (P P' : GProj 𝒜) :
    (extensionProj 𝒜 ℬ π hπ hact (P.prod P')).Iso
      ((extensionProj 𝒜 ℬ π hπ hact P).prod (extensionProj 𝒜 ℬ π hπ hact P')) :=
  GradedEquiv.ofPreserves (BalancedTensor.prodRight k C A C P.carrier P'.carrier)
    (fun _ _ hy => ⟨mapRight_mem_balancedGrading (ℳ := ℬ)
      (g := LinearMap.fst A P.carrier P'.carrier)
      (𝒩 := Graded.prod P.grading P'.grading) (𝒩' := P.grading) (fun _ _ hx => hx.1) hy,
      mapRight_mem_balancedGrading (ℳ := ℬ)
      (g := LinearMap.snd A P.carrier P'.carrier)
      (𝒩 := Graded.prod P.grading P'.grading) (𝒩' := P'.grading) (fun _ _ hx => hx.2) hy⟩)

private def quotientShift (P : GProj 𝒜) (a : ℤ) :
    (extensionProj 𝒜 ℬ π hπ hact (P.shift a)).Iso ((extensionProj 𝒜 ℬ π hπ hact P).shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (P.shiftLinearEquiv a))
    (fun d y hy => by
      have h := mapRight_mem_balancedGrading (B := C) (ℳ := ℬ)
        (P.shiftLinearEquiv_preservesGrading a) (y := y) hy
      rwa [balancedGrading_shift_right] at h)

private def quotientAdd : K0 𝒜 →+ K0 ℬ :=
  K0.lift (fun P => K0.of (extensionProj 𝒜 ℬ π hπ hact P))
    (fun _ _ e => K0.of_eq_of_iso (quotientCongr 𝒜 ℬ π hπ hact e))
    (fun P P' => (K0.of_eq_of_iso (quotientProd 𝒜 ℬ π hπ hact P P')).trans (K0.of_prod ..))

/-- Extension of scalars along a degree-preserving algebra map on graded projective classes
(Webster, arXiv:1309.3796v2, proof of Proposition 3.21). -/
def extensionK0 : K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 ℬ where
  __ := quotientAdd 𝒜 ℬ π hπ hact
  map_smul' := K0.map_smul_of_shift (quotientAdd 𝒜 ℬ π hπ hact) fun a x => by
    induction x using K0.induction_on with
    | of P =>
      simp only [K0.shiftHom_of, quotientAdd, K0.lift_of]
      exact K0.of_eq_of_iso (quotientShift 𝒜 ℬ π hπ hact P a)
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | neg x hx => simp only [map_neg, hx]

@[simp] theorem extensionK0_of (P : GProj 𝒜) :
    extensionK0 𝒜 ℬ π hπ hact (K0.of P) = K0.of (extensionProj 𝒜 ℬ π hπ hact P) := by
  change quotientAdd 𝒜 ℬ π hπ hact (K0.of P) = _
  exact K0.lift_of _ _ _ _

private def mulTensor (e : A) : BalancedTensor k C A C (leftIdeal e) →ₗ[C] C :=
  (BalancedTensor.rid k C A C).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

include hact in
private theorem mulTensor_tmul (e : A) (b : C) (x : leftIdeal e) :
    mulTensor (k := k) (C := C) e (BalancedTensor.tmul b x) = b * π x.val := hact x.val b

private def principalEquiv {e : A} (he : IsIdempotentElem e) :
    BalancedTensor k C A C (leftIdeal e) ≃ₗ[C] leftIdeal (π e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (mulTensor (k := k) (C := C) e).codRestrict (leftIdeal (π e)) fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b x =>
      rw [mulTensor_tmul π hact]
      change (b * π x.val) * π e = b * π x.val
      rw [mul_assoc, ← map_mul, mem_leftIdeal.mp x.2]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  let g : leftIdeal (π e) →ₗ[C] BalancedTensor k C A C (leftIdeal e) :=
    { toFun := fun b => BalancedTensor.tmul b.val p
      map_add' := fun x y => BalancedTensor.add_tmul x.val y.val p
      map_smul' := fun c x => BalancedTensor.smul_tmul' c x.val p }
  apply LinearEquiv.ofLinearMap f g
  · ext x
    change mulTensor (k := k) (C := C) e (BalancedTensor.tmul x.val p) = x.val
    rw [mulTensor_tmul π hact]
    exact x.property
  · apply BalancedTensor.extB
    intro b x
    change BalancedTensor.tmul (mulTensor (k := k) (C := C) e (BalancedTensor.tmul b x)) p = _
    rw [mulTensor_tmul π hact, ← hact]
    rw [BalancedTensor.op_smul_tmul]
    exact congrArg (BalancedTensor.tmul b) (Subtype.ext (mem_leftIdeal.mp x.property))

/-- Extension of scalars takes `A e` to `C π(e)` with its inherited grading
(Webster, proof of Proposition 3.21). -/
theorem extensionK0_ofIdempotent {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    extensionK0 𝒜 ℬ π hπ hact (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := ℬ) (π e) (he.map (π))
        (hπ he0)) := by
  rw [extensionK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (principalEquiv π hact he) ?_
  intro d y hy
  change mulTensor (k := k) (C := C) e y ∈ ℬ d
  apply balancedGrading_map_mem ℬ ((mulTensor (k := k) (C := C) e).restrictScalars k) _ hy
  intro i j b a hb ha
  rw [LinearMap.restrictScalars_apply, mulTensor_tmul π hact]
  exact SetLike.GradedMul.mul_mem (A := ℬ) hb (hπ ha)

section Surjectivity

variable {k' : Type*} [Field k'] {R S : Type u} [Ring R] [Ring S] [Algebra k' R] [Algebra k' S]
  (𝓡 : ℤ → Submodule k' R) (𝓢 : ℤ → Submodule k' S) [GradedAlgebra 𝓡] [GradedAlgebra 𝓢]
  (φ : R →ₐ[k'] S) (hφ : PreservesGrading 𝓡 𝓢 φ.toLinearMap)
  [Module Rᵐᵒᵖ S] [SMulCommClass S Rᵐᵒᵖ S] [IsScalarTower k' Rᵐᵒᵖ S]
  (hmul : ∀ (a : R) (s : S), op a • s = s * φ a)

/-- A graded algebra quotient induces a surjection on projective classes if
the source is locally finite and bounded below. -/
theorem extensionK0_surjective [HasGdim 𝓡] (hs : Function.Surjective φ) :
    Function.Surjective (extensionK0 𝓡 𝓢 φ hφ hmul) := by
  let := hasGdim_of_surjective 𝓡 𝓢 φ hφ hs
  apply LinearMap.range_eq_top.mp
  rw [eq_top_iff, ← K0.span_indec 𝓢]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  obtain ⟨e, he, he0, j, ⟨u⟩⟩ := b.isIndec_rep.exists_iso_ofIdempotent
  obtain ⟨p, hp, hp0, rfl⟩ := exists_graded_idempotent_preimage 𝓡 𝓢 φ hφ hs he he0
  refine ⟨(LaurentPolynomial.T j : LaurentPolynomial ℤ) • K0.of (GProj.ofIdempotent p hp hp0), ?_⟩
  rw [map_smul, extensionK0_ofIdempotent, K0.T_smul_of]
  exact (K0.of_eq_of_iso u).symm

end Surjectivity

end Categorification.Graded
