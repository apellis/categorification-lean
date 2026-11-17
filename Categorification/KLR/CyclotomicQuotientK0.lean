/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedInduction
import Categorification.KLR.CyclotomicProjectiveLift
import Categorification.KLR.K0Algebra

/-!
# Extension to the cyclotomic quotient on projective K₀

Webster, arXiv:1309.3796v2, §3.4, proof of Proposition 3.21. Tensoring an
affine graded projective with the monomial cyclotomic quotient takes a principal
projective to the left ideal of the projected idempotent. Over a field,
lifting a degree-zero idempotent gives a preimage for every shifted
indecomposable projective class. Hence extension is onto in each weight and
on their direct sum.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open Categorification.Graded MulOpposite

section Algebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (ν : Multiset I)

local notation "Aff" => KLRAlgebra k Q ν
local notation "C" => CycKLR k Q (fun i => Polynomial.X ^ Λ i) ν
local notation "π" => mk k Q (fun i => Polynomial.X ^ Λ i) ν
local notation "srcGr" => G.grade ν
local notation "dstGr" => grade G Λ ν

local instance : Module Affᵐᵒᵖ C := Module.compHom C (π).toRingHom.op

local instance : SMulCommClass C Affᵐᵒᵖ C where
  smul_comm b r x := (mul_assoc b x (π r.unop)).symm

local instance : IsScalarTower k Affᵐᵒᵖ C where
  smul_assoc c r x := by
    change x * π (c • r.unop) = c • (x * π r.unop)
    rw [map_smul, mul_smul_comm]

/-- The graded cyclotomic projective obtained as `C ⊗_A P` via the quotient map. -/
def quotientProj (P : GProj srcGr) : GProj dstGr where
  carrier := BalancedTensor k C Aff C P.carrier
  grading := balancedGrading C Aff dstGr P.grading
  decomposition := balancedDecomposition srcGr fun _ _ _ _ hm ha =>
    SetLike.GradedMul.mul_mem (A := dstGr) hm (Graded.mem_map_of_mem _ (π).toLinearMap ha)
  gradedSMul := gradedSMul_balanced dstGr
  finite := BalancedTensor.finite
  projective := BalancedTensor.projective

private def quotientCongr {P P' : GProj srcGr} (e : P.Iso P') :
    (quotientProj G Λ ν P).Iso (quotientProj G Λ ν P') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight e.toLinearEquiv)
    (fun _ _ hy => mapRight_mem_balancedGrading (ℳ := dstGr) e.preservesGrading hy)

private def quotientProd (P P' : GProj srcGr) :
    (quotientProj G Λ ν (P.prod P')).Iso
      ((quotientProj G Λ ν P).prod (quotientProj G Λ ν P')) :=
  GradedEquiv.ofPreserves (BalancedTensor.prodRight k C Aff C P.carrier P'.carrier)
    (fun _ _ hy => ⟨mapRight_mem_balancedGrading (ℳ := dstGr)
      (g := LinearMap.fst Aff P.carrier P'.carrier)
      (𝒩 := Graded.prod P.grading P'.grading) (𝒩' := P.grading) (fun _ _ hx => hx.1) hy,
      mapRight_mem_balancedGrading (ℳ := dstGr)
      (g := LinearMap.snd Aff P.carrier P'.carrier)
      (𝒩 := Graded.prod P.grading P'.grading) (𝒩' := P'.grading) (fun _ _ hx => hx.2) hy⟩)

private def quotientShift (P : GProj srcGr) (a : ℤ) :
    (quotientProj G Λ ν (P.shift a)).Iso ((quotientProj G Λ ν P).shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (P.shiftLinearEquiv a))
    (fun d y hy => by
      have h := mapRight_mem_balancedGrading (B := C) (ℳ := dstGr)
        (P.shiftLinearEquiv_preservesGrading a) (y := y) hy
      rwa [balancedGrading_shift_right] at h)

private def quotientAdd : K0 srcGr →+ K0 dstGr :=
  K0.lift (fun P => K0.of (quotientProj G Λ ν P))
    (fun _ _ e => K0.of_eq_of_iso (quotientCongr G Λ ν e))
    (fun P P' => (K0.of_eq_of_iso (quotientProd G Λ ν P P')).trans (K0.of_prod ..))

/-- Extension of scalars along the cyclotomic quotient on graded projective classes
(Webster, arXiv:1309.3796v2, proof of Proposition 3.21). -/
def quotientK0 : K0 srcGr →ₗ[LaurentPolynomial ℤ] K0 dstGr where
  __ := quotientAdd G Λ ν
  map_smul' := K0.map_smul_of_shift (quotientAdd G Λ ν) fun a x => by
    induction x using K0.induction_on with
    | of P =>
      simp only [K0.shiftHom_of, quotientAdd, K0.lift_of]
      exact K0.of_eq_of_iso (quotientShift G Λ ν P a)
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | neg x hx => simp only [map_neg, hx]

@[simp] theorem quotientK0_of (P : GProj srcGr) :
    quotientK0 G Λ ν (K0.of P) = K0.of (quotientProj G Λ ν P) := by
  change quotientAdd G Λ ν (K0.of P) = _
  exact K0.lift_of _ _ _ _

private def mulTensor (e : Aff) : BalancedTensor k C Aff C (leftIdeal e) →ₗ[C] C :=
  (BalancedTensor.rid k C Aff C).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem mulTensor_tmul (e : Aff) (b : C) (x : leftIdeal e) :
    mulTensor Λ ν e (BalancedTensor.tmul b x) = b * π x.val := rfl

private def principalEquiv {e : Aff} (he : IsIdempotentElem e) :
    BalancedTensor k C Aff C (leftIdeal e) ≃ₗ[C] leftIdeal (π e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (mulTensor Λ ν e).codRestrict (leftIdeal (π e)) fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b x =>
      change (b * π x.val) * π e = b * π x.val
      rw [mul_assoc, ← map_mul, mem_leftIdeal.mp x.2]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  let g : leftIdeal (π e) →ₗ[C] BalancedTensor k C Aff C (leftIdeal e) :=
    { toFun := fun b => BalancedTensor.tmul b.val p
      map_add' := fun x y => BalancedTensor.add_tmul x.val y.val p
      map_smul' := fun c x => BalancedTensor.smul_tmul' c x.val p }
  apply LinearEquiv.ofLinearMap f g
  · ext x
    exact x.property
  · apply BalancedTensor.extB
    intro b x
    change BalancedTensor.tmul (op x.val • b) p = BalancedTensor.tmul b x
    rw [BalancedTensor.op_smul_tmul]
    exact congrArg (BalancedTensor.tmul b) (Subtype.ext (mem_leftIdeal.mp x.property))

/-- Extension of scalars takes `A e` to `C π(e)` with its inherited grading
(Webster, proof of Proposition 3.21). -/
theorem quotientK0_ofIdempotent {e : Aff} (he : IsIdempotentElem e) (he0 : e ∈ srcGr 0) :
    quotientK0 G Λ ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dstGr) (π e) (he.map (π))
        (Graded.mem_map_of_mem _ (π).toLinearMap he0)) := by
  rw [quotientK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (principalEquiv Λ ν he) ?_
  intro d y hy
  change mulTensor Λ ν e y ∈ dstGr d
  apply balancedGrading_map_mem dstGr ((mulTensor Λ ν e).restrictScalars k) _ hy
  intro i j b a hb ha
  rw [LinearMap.restrictScalars_apply, mulTensor_tmul]
  exact SetLike.GradedMul.mul_mem (A := dstGr) hb (Graded.mem_map_of_mem _ (π).toLinearMap ha)

/-- Extension of scalars on the direct sum of all root contents (Webster, §3.4,
proof of Proposition 3.21). -/
def totalQuotientK0 : G.K0R →ₗ[LaurentPolynomial ℤ] projectiveK0 G Λ :=
  DirectSum.lmap (quotientK0 G Λ)

@[simp] theorem totalQuotientK0_lof (x : K0 srcGr) :
    totalQuotientK0 G Λ (DirectSum.lof (LaurentPolynomial ℤ) _ G.K0fam ν x) =
      DirectSum.lof (LaurentPolynomial ℤ) _ (fun β => K0 (grade G Λ β)) ν (quotientK0 G Λ ν x) :=
  DirectSum.lmap_lof ..

end Algebra

section Field

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (ν : Multiset I)

/-- The affine-to-cyclotomic map is onto in each weight (Webster, proof of
Proposition 3.21). Symmetry and positive dot degrees ensure that the
degree-zero affine algebra is finite dimensional. -/
theorem quotientK0_surjective (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) :
    Function.Surjective (quotientK0 G Λ ν) := by
  let := G.hasGdim_grade' (ν := ν) hsym hX
  let : HasGdim (grade G Λ ν) :=
    { finiteDimensional := fun n => inferInstanceAs (Module.Finite k ((G.grade ν n).map _))
      bddBelow := by
        obtain ⟨L, hL⟩ := HasGdim.bddBelow (ℳ := G.grade ν)
        refine ⟨L, fun n hn => hL ?_⟩
        intro h
        apply hn
        change (G.grade ν n).map _ = ⊥
        rw [h, Submodule.map_bot] }
  apply LinearMap.range_eq_top.mp
  rw [eq_top_iff, ← K0.span_indec (grade G Λ ν)]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  obtain ⟨e, he, he0, j, ⟨u⟩⟩ := exists_iso_of_affineIdempotent G Λ ν hsym hX b.rep b.isIndec_rep
  refine ⟨(LaurentPolynomial.T j : LaurentPolynomial ℤ) • K0.of (GProj.ofIdempotent e he he0), ?_⟩
  rw [map_smul, quotientK0_ofIdempotent, K0.T_smul_of]
  exact (K0.of_eq_of_iso u).symm

/-- The affine graded projective Grothendieck group surjects onto the direct sum
of cyclotomic weight groups (Webster, Proposition 3.21, generation step). -/
theorem totalQuotientK0_surjective (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) :
    Function.Surjective (totalQuotientK0 G Λ) :=
  (DirectSum.lmap_surjective _).mpr fun γ => quotientK0_surjective G Λ γ hsym hX

end Field

end Categorification.KLR.CycKLR
