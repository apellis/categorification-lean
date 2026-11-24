/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoUnknotHomology
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases

/-!
# The polynomial presentation of the label-two middle algebra

This identifies both quotient rings in the middle term of the label-two
unknot calculation of Webster, arXiv:1309.3796v2, §8.2, printed page 81.
The first equivalence takes the two polynomial variables to the two
iterated dual-number generators. The second identifies the quotient by
their sum with the single dual-number algebra.
-/

namespace Categorification.Webster.LabelTwo

open TrivSqZeroExt
open scoped DualNumber

noncomputable section

variable (k : Type*) [CommRing k]

local notation "P" => MvPolynomial (Fin 2) k

/-- The two-square ideal in the polynomial presentation of the middle term. -/
def squareIdeal : Ideal P :=
  Ideal.span (Set.range fun i : Fin 2 => (MvPolynomial.X i : P)^2)

abbrev SquareQuotient := P ⧸ squareIdeal k

abbrev squareQuotientVariable (i : Fin 2) : SquareQuotient k :=
  Ideal.Quotient.mkₐ k (squareIdeal k) (MvPolynomial.X i)

private theorem quotX_mul_self (i : Fin 2) : squareQuotientVariable k i * squareQuotientVariable k i=0 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← pow_two]
  exact Ideal.subset_span ⟨i,rfl⟩

private theorem y₁_mul_self : (y₁ : Middle k)*y₁=0 := by
  change inl ε * inl ε = (0 : Middle k)
  rw [inl_mul_inl (R := DualNumber k) (M := DualNumber k) ε ε,DualNumber.eps_mul_eps,inl_zero]

private theorem y₂_mul_self : (y₂ : Middle k)*y₂=0 :=
  DualNumber.eps_mul_eps

private def y (i : Fin 2) : Middle k := if i=0 then y₁ else y₂

private theorem y_sq (i : Fin 2) : y k i ^ 2=0 := by
  by_cases h : i=0
  · rw [y,ite_eq_left h,pow_two,y₁_mul_self]
  · rw [y,ite_eq_right h,pow_two,y₂_mul_self]

private theorem eval_kills_squareIdeal (p : P) (hp : p ∈ squareIdeal k) :
    MvPolynomial.aeval (y k) p=0 := by
  have le : squareIdeal k ≤ RingHom.ker (MvPolynomial.aeval (y k)).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change MvPolynomial.aeval (y k) ((MvPolynomial.X i)^2)=0
    rw [map_pow,MvPolynomial.aeval_X,y_sq]
  exact le hp

private def toMiddle : SquareQuotient k →ₐ[k] Middle k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (y k)) (eval_kills_squareIdeal k)

private theorem toMiddle_quotX (i : Fin 2) : toMiddle k (squareQuotientVariable k i) = y k i := by
  change Ideal.Quotient.lift (squareIdeal k)
    (MvPolynomial.aeval (y k) : P →ₐ[k] Middle k).toRingHom
    (eval_kills_squareIdeal k) (Ideal.Quotient.mk (squareIdeal k) (MvPolynomial.X i)) = _
  rw [Ideal.Quotient.lift_mk]
  exact MvPolynomial.aeval_X _ _

private def fromFirst : DualNumber k →ₐ[k] SquareQuotient k :=
  DualNumber.lift ⟨(Algebra.ofId k _,squareQuotientVariable k 0),quotX_mul_self k 0,fun _ => Commute.all _ _⟩

private def fromMiddle : Middle k →ₐ[k] SquareQuotient k :=
  DualNumber.lift ⟨(fromFirst k,squareQuotientVariable k 1),quotX_mul_self k 1,fun _ => Commute.all _ _⟩

private theorem fromMiddle_y₁ : fromMiddle k y₁=squareQuotientVariable k 0 := by
  simp [fromMiddle,fromFirst,y₁]

private theorem fromMiddle_y₂ : fromMiddle k y₂=squareQuotientVariable k 1 := by
  simp [fromMiddle,y₂]

private theorem fromMiddle_comp_toMiddle :
    (fromMiddle k).comp (toMiddle k) = AlgHom.id _ _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fromMiddle k (toMiddle k (squareQuotientVariable k i)) = squareQuotientVariable k i
  rw [toMiddle_quotX]
  fin_cases i
  · exact fromMiddle_y₁ k
  · exact fromMiddle_y₂ k

private theorem middle_algHom_ext {R : Type*} [CommRing R] [Algebra k R]
    {f g : Middle k →ₐ[k] R}
    (h₁ : f y₁ = g y₁) (h₂ : f y₂ = g y₂) : f=g := by
  have hinl : f.comp (inlAlgHom k (DualNumber k) (DualNumber k)) =
      g.comp (inlAlgHom k (DualNumber k) (DualNumber k)) := by
    apply DualNumber.algHom_ext
    exact h₁
  apply DualNumber.algHom_ext' hinl
  ext x
  change f (x • (ε : Middle k)) = g (x • (ε : Middle k))
  rw [← inl_mul_eq_smul x (ε : Middle k)]
  change f (inl x * y₂) = g (inl x * y₂)
  rw [map_mul,map_mul,h₂]
  exact congrArg (· * g y₂) (DFunLike.congr_fun hinl x)

private theorem toMiddle_comp_fromMiddle :
    (toMiddle k).comp (fromMiddle k) = AlgHom.id _ _ := by
  apply middle_algHom_ext k (R := Middle k)
    (f := (toMiddle k).comp (fromMiddle k)) (g := AlgHom.id k _)
  · change toMiddle k (fromMiddle k y₁)=y₁
    rw [fromMiddle_y₁,toMiddle_quotX]
    rfl
  · change toMiddle k (fromMiddle k y₂)=y₂
    rw [fromMiddle_y₂,toMiddle_quotX]
    rfl

/-- The algebra `k[y₁,y₂]/(y₁²,y₂²)` in iterated dual number coordinates. -/
def middlePolynomialEquiv : SquareQuotient k ≃ₐ[k] Middle k :=
  AlgEquiv.ofAlgHom (toMiddle k) (fromMiddle k)
    (toMiddle_comp_fromMiddle k) (fromMiddle_comp_toMiddle k)

@[simp] theorem middlePolynomialEquiv_variable_zero :
    middlePolynomialEquiv k (squareQuotientVariable k 0) = y₁ :=
  toMiddle_quotX k 0

@[simp] theorem middlePolynomialEquiv_variable_one :
    middlePolynomialEquiv k (squareQuotientVariable k 1) = y₂ :=
  toMiddle_quotX k 1

attribute [local instance] quotientAlgebra quotientModule

/-- The plus relation generates the augmentation ideal. -/
def sumIdeal : Ideal (Middle k) := Ideal.span ({(y₁ : Middle k)+y₂} : Set (Middle k))

instance sumIdeal_isTwoSided : (sumIdeal k).IsTwoSided :=
  ⟨fun a h => mul_comm a _ ▸ (sumIdeal k).smul_mem a h⟩

/-- The augmentation kills exactly the principal ideal of the sum differential. -/
theorem ker_specialize_eq_span :
    RingHom.ker (specialize (k := k)).toRingHom = sumIdeal k := by
  ext x
  have hker : x ∈ (augmentation (k := k)).ker ↔ x ∈ (plus (k := k)).range := by
    rw [ker_augmentation]
  change x ∈ (augmentation (k := k)).ker ↔ x ∈ sumIdeal k
  have hspan : x ∈ sumIdeal k ↔ ((y₁ : Middle k)+y₂) ∣ x :=
    Ideal.mem_span_singleton (α := Middle k)
  rw [hker,hspan]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩

/-- The quotient by the sum relation is the dual numbers as a ring. -/
noncomputable def specializedQuotientEquiv :
    (Middle k ⧸ sumIdeal k) ≃+* DualNumber k :=
  (Ideal.quotEquivOfEq (R := Middle k) (I := sumIdeal k) (ker_specialize_eq_span k).symm).trans
    ((specialize (k := k)).toRingHom.quotientKerEquivOfSurjective
      (augmentation_surjective (k := k)))

@[simp] theorem specializedQuotientEquiv_mk (x : Middle k) :
    specializedQuotientEquiv k (Ideal.Quotient.mk (sumIdeal k) x) = specialize x :=
  rfl

end

end Categorification.Webster.LabelTwo
