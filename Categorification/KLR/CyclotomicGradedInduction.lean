/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentModule
import Categorification.KLR.CyclotomicGrothendieck
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.Induction

/-!
# Graded cyclotomic induction on projectives

Webster, arXiv:1309.3796v2, Definition 3.15, and Kang–Kashiwara,
arXiv:1102.4677v4, §4.2 and §6. Adjoining a final black strand gives a
degree-preserving nonunital map on the cyclotomic quotient. Its one-sided
corner defines unshifted induction on graded projectives and a Laurent-linear
lowering operator on the projective Grothendieck group.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded MulOpposite
open scoped TensorProduct

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ (Si + β)
local notation "Mc" => IndCorner Q i aΛ β
local notation "srcGr" => grade G Λ β
local notation "dstGr" => grade G Λ (Si + β)

/-- The last-strand map on the cyclotomic quotient preserves degrees. -/
theorem cyclotomicLast_mem_grade {d : ℤ} {z : Rl} (hz : z ∈ srcGr d) :
    cyclotomicLast Q i aΛ β z ∈ dstGr d := by
  obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hz
  rw [AlgHom.toLinearMap_apply, cyclotomicLast_mk]
  apply Graded.mem_map_of_mem
  rw [cL_eq_cast]
  apply G.castKLR_mem_grade
  simpa only [add_zero] using G.concat_tmul_mem_grade hr
    (show (1 : KLRAlgebra k Q Si) ∈ G.grade Si 0 from SetLike.GradedOne.one_mem)

private def cornerProjective : GProj dstGr :=
  GProj.ofIdempotent (lastIdem Q i aΛ β) (lastIdem_mul Q i aΛ β)
    (cyclotomicLast_mem_grade G Λ i β SetLike.GradedOne.one_mem)

local notation "corGr" => Graded.submodule dstGr (lIdeal (lastIdem Q i aΛ β))

/-- The left-module form of cyclotomic induction in Webster's Definition 3.15:
the existing `Ind` module with its balanced tensor grading. -/
def gradedIndProj (P : GProj srcGr) : GProj dstGr := by
  letI : Module.Finite Su Mc := (cornerProjective G Λ i β).finite
  letI : Module.Projective Su Mc := (cornerProjective G Λ i β).projective
  letI : DirectSum.Decomposition corGr := (cornerProjective G Λ i β).decomposition
  refine
    { carrier := Ind Q i aΛ β P.carrier
      grading := balancedGrading Su Rl corGr P.grading
      decomposition := balancedDecomposition srcGr ?_
      gradedSMul := gradedSMul_balanced dstGr
      finite := BalancedTensor.finite
      projective := BalancedTensor.projective }
  intro d l m a hm ha
  exact SetLike.GradedMul.mul_mem (A := dstGr) hm (cyclotomicLast_mem_grade G Λ i β ha)

private def indCongr {P P' : GProj srcGr} (e : P.Iso P') :
    (gradedIndProj G Λ i β P).Iso (gradedIndProj G Λ i β P') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight e.toLinearEquiv)
    (fun _ _ hy => mapRight_mem_balancedGrading (ℳ := corGr) e.preservesGrading hy)

private def indProd (P P' : GProj srcGr) :
    (gradedIndProj G Λ i β (P.prod P')).Iso
      ((gradedIndProj G Λ i β P).prod (gradedIndProj G Λ i β P')) :=
  GradedEquiv.ofPreserves (BalancedTensor.prodRight k Su Rl Mc P.carrier P'.carrier)
    (fun _ _ hy => ⟨mapRight_mem_balancedGrading (ℳ := corGr)
      (g := LinearMap.fst Rl P.carrier P'.carrier)
      (𝒩 := Graded.prod P.grading P'.grading) (𝒩' := P.grading) (fun _ _ hx => hx.1) hy,
      mapRight_mem_balancedGrading (ℳ := corGr)
      (g := LinearMap.snd Rl P.carrier P'.carrier)
      (𝒩 := Graded.prod P.grading P'.grading) (𝒩' := P'.grading) (fun _ _ hx => hx.2) hy⟩)

private def indShift (P : GProj srcGr) (a : ℤ) :
    (gradedIndProj G Λ i β (P.shift a)).Iso ((gradedIndProj G Λ i β P).shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (P.shiftLinearEquiv a))
    (fun d y hy => by
      have h := mapRight_mem_balancedGrading (B := Su) (ℳ := corGr)
        (P.shiftLinearEquiv_preservesGrading a) (y := y) hy
      rwa [balancedGrading_shift_right] at h)

private def indAdd : K0 srcGr →+ K0 dstGr :=
  K0.lift (fun P => K0.of (gradedIndProj G Λ i β P))
    (fun _ _ e => K0.of_eq_of_iso (indCongr G Λ i β e))
    (fun P P' => (K0.of_eq_of_iso (indProd G Λ i β P P')).trans (K0.of_prod ..))

/-- The lowering operator `[Fᵢ]` induced by the one-sided cyclotomic corner with
its graded induction action (Webster, arXiv:1309.3796v2, Definition 3.15). -/
def indK0 : K0 srcGr →ₗ[LaurentPolynomial ℤ] K0 dstGr where
  __ := indAdd G Λ i β
  map_smul' := K0.map_smul_of_shift (indAdd G Λ i β) fun a x => by
    induction x using K0.induction_on with
    | of P =>
      simp only [K0.shiftHom_of, indAdd, K0.lift_of]
      exact K0.of_eq_of_iso (indShift G Λ i β P a)
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | neg x hx => simp only [map_neg, hx]

@[simp] theorem indK0_of (P : GProj srcGr) :
    indK0 G Λ i β (K0.of P) = K0.of (gradedIndProj G Λ i β P) := by
  change indAdd G Λ i β (K0.of P) = _
  exact K0.lift_of _ _ _ _

/-- Induction carries the regular projective of the smaller weight to the
last-colour principal projective in the larger block. -/
theorem indK0_regular :
    indK0 G Λ i β (K0.of (GProj.regular srcGr)) =
      K0.of (GProj.ofIdempotent (lastIdem Q i aΛ β) (lastIdem_mul Q i aΛ β)
        (cyclotomicLast_mem_grade G Λ i β SetLike.GradedOne.one_mem)) := by
  rw [indK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (BalancedTensor.rid k Su Rl Mc) ?_
  intro d y hy
  apply balancedGrading_map_mem (ℳ := corGr) (𝒩 := srcGr) corGr
    ((BalancedTensor.rid k Su Rl Mc).toLinearMap.restrictScalars k) _ hy
  intro d l m a hm ha
  exact SetLike.GradedMul.mul_mem (A := dstGr) hm (cyclotomicLast_mem_grade G Λ i β ha)

/-- The first lowering of the vacuum class is the regular projective in the
one-black-strand block (Webster, Definition 3.15 and Proposition 3.21). -/
theorem indK0_vacuum :
    indK0 G Λ i 0 (K0.of (GProj.regular (grade G Λ 0))) =
      K0.of (GProj.regular (grade G Λ (Si + 0))) := by
  rw [indK0_regular]
  have he : lastIdem Q i aΛ 0 = 1 := by
    rw [lastIdem, cyclotomicLast_one, cL_zero_one, map_one]
  exact (K0.of_ofIdempotent_congr he _ IsIdempotentElem.one _ SetLike.GradedOne.one_mem).trans
    (K0.of_eq_of_iso GProj.ofIdempotentOneIso)

local notation "LP" => LaurentPolynomial ℤ

/-- The unshifted lowering operator on the sum of all cyclotomic projective
weight groups (Kang–Kashiwara, arXiv:1102.4677v4, §6). -/
def lower : projectiveK0 G Λ →ₗ[LP] projectiveK0 G Λ :=
  DirectSum.toModule LP _ _ fun ν =>
    DirectSum.lof LP _ _ (Si + ν) ∘ₗ indK0 G Λ i ν

@[simp] theorem lower_lof (ν : Multiset I) (x : K0 (grade G Λ ν)) :
    lower G Λ i (DirectSum.lof LP _ _ ν x) = DirectSum.lof LP _ _ (Si + ν) (indK0 G Λ i ν x) :=
  DirectSum.toModule_lof ..

end Categorification.KLR.CycKLR
