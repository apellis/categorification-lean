/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Restriction
import Categorification.TwoRep.CyclotomicRouqAdjunction

/-!
# Comparison of the two descriptions of cyclotomic induction

Kang–Kashiwara (arXiv:1102.4677v4, §4.2) define `F_i^Λ N = R^Λ(β + α_i) e(β, i) ⊗_{R^Λ(β)} N`
and `E_i^Λ M = e(β, i) M`. The library has two models of these functors:

* `KLRAlgebra.AbsentColour.inductionFunctor` and `restrictionFunctor`, where the tensor product
  is balanced over the ground ring `k`;
* `CyclotomicAction.ind` and `res`, induction and restriction along the last-strand inclusion
  `lastEmb` (`Categorification.InductionAlong`), where it is balanced over `ℤ`.

This file identifies them: `indIso` and `resIso` are the identity on generators `z ⊗ n` and on
elements of `e(β, i) M`. Under these isomorphisms the units and counits of the two
induction–restriction adjunctions, the dots and the same-colour crossings `-ψ` agree
(`unit_compat`, `counit_compat`, `dot_compat`, `cross_compat`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory MulOpposite
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k) (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "ιL" => lastEmb Q a i (rfl : Si + β = Si + β)

namespace Comparison

variable (N : ModuleCat.{max (max u v) w} (CycKLR k Q a β))

/-- The two corners agree: both are the left ideal of `e(β, i)`. -/
def cornerTo (z : InductionAlong.Corner ιL) : KLRAlgebra.AbsentColour.IndCorner Q i a β :=
  ⟨z.1, z.2⟩

/-- The comparison map on generators `z ⊗ n ↦ z ⊗ n`. -/
def toOld : InductionAlong.Ind N ιL →ₗ[CycKLR k Q a (Si + β)]
    KLRAlgebra.AbsentColour.Ind Q i a β N :=
  InductionAlong.Ind.lift (fun z n => BalancedTensor.tmul (cornerTo Q a i β z) n)
    (fun _ _ n => BalancedTensor.add_tmul _ _ n)
    (fun _ n n' => BalancedTensor.tmul_add _ n n')
    (fun z r n => BalancedTensor.op_smul_tmul (cornerTo Q a i β z) r n)
    (fun s z n => (BalancedTensor.smul_tmul' s (cornerTo Q a i β z) n).symm)

@[simp] theorem toOld_tmul (z : InductionAlong.Corner ιL) (n : N) :
    toOld Q a i β N (InductionAlong.Ind.tmul z n) =
      BalancedTensor.tmul (cornerTo Q a i β z) n := rfl

/-- The inverse comparison. -/
def fromOld : KLRAlgebra.AbsentColour.Ind Q i a β N →ₗ[CycKLR k Q a (Si + β)]
    ((ind Q a i (rfl : Si + β = Si + β)).obj N) :=
  BalancedTensor.liftB
    (LinearMap.mk₂ k (fun (z : KLRAlgebra.AbsentColour.IndCorner Q i a β) (n : N) =>
      (InductionAlong.Ind.tmul ⟨z.1, z.2⟩ n :
        (ind Q a i (rfl : Si + β = Si + β)).obj N))
      (fun z z' n => InductionAlong.Ind.add_tmul _ _ n)
      (fun c z n => by
        change _ = (algebraMap k (CycKLR k Q a (Si + β)) c •
          (InductionAlong.Ind.tmul ⟨z.1, z.2⟩ n : InductionAlong.Ind N ιL))
        rw [InductionAlong.Ind.smul_tmul]
        congr 1)
      (fun z n n' => InductionAlong.Ind.tmul_add _ n n')
      (fun c z n => by
        change InductionAlong.Ind.tmul _ (algebraMap k (CycKLR k Q a β) c • n) =
          (algebraMap k (CycKLR k Q a (Si + β)) c •
            (InductionAlong.Ind.tmul ⟨z.1, z.2⟩ n : InductionAlong.Ind N ιL))
        rw [← InductionAlong.Ind.op_smul_tmul, InductionAlong.Ind.smul_tmul]
        congr 1
        refine Subtype.ext ?_
        change z.1 * KLRAlgebra.AbsentColour.cyclotomicLast Q i a β
          (algebraMap k (CycKLR k Q a β) c) = algebraMap k (CycKLR k Q a (Si + β)) c * z.1
        have hz : z.1 * KLRAlgebra.AbsentColour.cyclotomicLast Q i a β 1 = z.1 := z.2
        rw [Algebra.algebraMap_eq_smul_one, map_smul, mul_smul_comm, hz, ← Algebra.smul_def]))
    (fun z r n => InductionAlong.Ind.op_smul_tmul (φ := ιL) ⟨z.1, z.2⟩ r n)
    (fun s z n => (InductionAlong.Ind.smul_tmul (φ := ιL) s ⟨z.1, z.2⟩ n).symm)

/-- The comparison of the two induced modules. -/
def equiv : InductionAlong.Ind N ιL ≃ₗ[CycKLR k Q a (Si + β)]
    KLRAlgebra.AbsentColour.Ind Q i a β N :=
  LinearEquiv.ofLinearMap (toOld Q a i β N) (fromOld Q a i β N)
    (BalancedTensor.extB fun _ _ => rfl) (InductionAlong.Ind.ext fun _ _ => rfl)

variable (M : ModuleCat.{max (max u v) w} (CycKLR k Q a ({i} + β)))

/-- The comparison of the two restricted modules: both are `e(β, i) M`. -/
def resEquiv : InductionAlong.Res ιL M ≃ₗ[CycKLR k Q a β]
    KLRAlgebra.AbsentColour.Res Q i a β M where
  toFun m := ⟨m.val, m.prop⟩
  invFun m := InductionAlong.Res.mk m.1 m.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Comparison

open Comparison KLRAlgebra.AbsentColour

/-- **Cyclotomic induction along `lastEmb` is the cyclotomic induction functor.** -/
def indIso : ind.{u, v, w} Q a i (rfl : Si + β = Si + β) ≅ inductionFunctor.{u, v, w} Q i a β :=
  NatIso.ofComponents (fun N => (equiv Q a i β N).toModuleIso)
    (fun _ => ModuleCat.hom_ext (InductionAlong.Ind.ext fun _ _ => rfl))

/-- **Cyclotomic restriction along `lastEmb` is the cyclotomic restriction functor.** -/
def resIso : res.{u, v, w} Q a i (rfl : Si + β = Si + β) ≅
    restrictionFunctor.{u, v, w} Q i a β :=
  NatIso.ofComponents (fun M => (resEquiv Q a i β M).toModuleIso)
    (fun _ => rfl)

open TwoRep in
/-- `indIso` as a 2-isomorphism of `TwoRep.AdditiveCat`. -/
def indIsoA : indA.{u, v, w} Q a i (rfl : Si + β = Si + β) ≅ ConcreteAdjunction.ind Q i a β :=
  ObjectProperty.isoMk _ (indIso Q a i β)

open TwoRep in
/-- `resIso` as a 2-isomorphism of `TwoRep.AdditiveCat`. -/
def resIsoA : resA.{u, v, w} Q a i (rfl : Si + β = Si + β) ≅ ConcreteAdjunction.res Q i a β :=
  ObjectProperty.isoMk _ (resIso Q a i β)

open Bicategory TwoRep

theorem unit_compat_nat : (indResAdj.{u, v, w} Q a i (rfl : Si + β = Si + β)).unit ≫
    Functor.whiskerRight (indIso Q a i β).hom (res Q a i rfl) ≫
      Functor.whiskerLeft (inductionFunctor Q i a β) (resIso Q a i β).hom =
    (cyclotomicAdjunction Q i a β).unit := by
  ext N n
  rfl

theorem counit_compat_nat : (Functor.whiskerRight (resIso.{u, v, w} Q a i β).hom
    (ind Q a i (rfl : Si + β = Si + β)) ≫
      Functor.whiskerLeft (restrictionFunctor Q i a β) (indIso Q a i β).hom) ≫
      (cyclotomicAdjunction Q i a β).counit = (indResAdj Q a i rfl).counit := by
  ext M : 2
  exact ModuleCat.hom_ext (InductionAlong.Ind.ext fun _ _ => rfl)

theorem dot_compat_nat : dot.{u, v, w} Q a i (rfl : Si + β = Si + β) ≫ (indIso Q a i β).hom =
    (indIso Q a i β).hom ≫ InductionCalculus.dotNat Q i a β := by
  ext N : 2
  exact ModuleCat.hom_ext (InductionAlong.Ind.ext fun _ _ => rfl)

theorem cross_compat_nat : sameCross.{u, v, w} Q a i (rfl : Si + β = Si + β)
      (rfl : Si + (Si + β) = Si + (Si + β)) ≫
      (Functor.whiskerRight (indIso Q a i β).hom (ind Q a i rfl) ≫
        Functor.whiskerLeft (inductionFunctor Q i a β) (indIso Q a i (Si + β)).hom) =
    (Functor.whiskerRight (indIso Q a i β).hom (ind Q a i rfl) ≫
        Functor.whiskerLeft (inductionFunctor Q i a β) (indIso Q a i (Si + β)).hom) ≫
      InductionCalculus.crossingNat Q i a β := by
  rw [sameCross, Preadditive.neg_comp]
  ext N : 2
  refine ModuleCat.hom_ext (InductionAlong.Ind.ext₂ fun z w n => ?_)
  simp only [NatTrans.app_neg, ModuleCat.hom_neg]
  set X : KLRAlgebra.AbsentColour.Ind Q i a (Si + β) (KLRAlgebra.AbsentColour.Ind Q i a β N) :=
    BalancedTensor.tmul (indGenerator Q i a (Si + β))
      (BalancedTensor.tmul (indGenerator Q i a β) n) with hX
  have hD : InductionCalculus.doubleIdem Q i a β • X = X := by
    rw [hX, BalancedTensor.smul_tmul']
    have h1 : InductionCalculus.doubleIdem Q i a β • indGenerator Q i a (Si + β) =
        op (cyclotomicLast Q i a β 1) • indGenerator Q i a (Si + β) :=
      Subtype.ext (by
        change cyclotomicLast Q i a (Si + β) (cyclotomicLast Q i a β 1) *
            cyclotomicLast Q i a (Si + β) 1 =
          cyclotomicLast Q i a (Si + β) 1 * cyclotomicLast Q i a (Si + β)
            (cyclotomicLast Q i a β 1)
        rw [← map_mul, ← map_mul, mul_one, one_mul])
    rw [h1, BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul']
    congr 2
    exact Subtype.ext (lastIdem_mul Q i a β)
  change -(BalancedTensor.tmul (⟨z.1 * lastEmb Q a i rfl w.1 *
      crossElt Q a (γ := β) (δ := Si + (Si + β)), _⟩ : IndCorner Q i a (Si + β))
        (BalancedTensor.tmul (indGenerator Q i a β) n)) =
    InductionCalculus.crossing Q i a β N
      (BalancedTensor.tmul ⟨z.1, z.2⟩ (BalancedTensor.tmul ⟨w.1, w.2⟩ n))
  rw [InductionCalculus.crossing, InductionCalculus.doubleEnd_tmul]
  have gen (c : IndCorner Q i a (Si + β)) :
      (BalancedTensor.tmul c (BalancedTensor.tmul (indGenerator Q i a β) n) :
        KLRAlgebra.AbsentColour.Ind Q i a (Si + β) (KLRAlgebra.AbsentColour.Ind Q i a β N)) =
        c.1 • X :=
    InductionCalculus.tmul_generator Q i a (Si + β) _ c _
  refine (congrArg Neg.neg (gen _)).trans (Eq.trans ?_ (gen _).symm)
  have hc : (z.1 * (cyclotomicLast Q i a (Si + β) w.1 *
      InductionCalculus.crossingElement Q i a β)) =
      -(z.1 * lastEmb Q a i rfl w.1 * crossElt Q a (γ := β) (δ := Si + (Si + β))) *
        InductionCalculus.doubleIdem Q i a β := by
    simp only [InductionCalculus.crossingElement, mul_neg, neg_mul, mul_assoc]
    rfl
  change -((z.1 * lastEmb Q a i rfl w.1 * crossElt Q a (γ := β) (δ := Si + (Si + β))) • X) =
    (z.1 * (cyclotomicLast Q i a (Si + β) w.1 * InductionCalculus.crossingElement Q i a β)) • X
  rw [hc, mul_smul _ (InductionCalculus.doubleIdem Q i a β), hD, neg_smul]

theorem unit_compat : (adjA.{u, v, w} Q a i (rfl : Si + β = Si + β)).unit ≫
    ((indIsoA Q a i β).hom ▷ resA Q a i rfl ≫ ConcreteAdjunction.ind Q i a β ◁
      (resIsoA Q a i β).hom) = (ConcreteAdjunction.adj Q i a β).unit :=
  ObjectProperty.hom_ext _ (unit_compat_nat Q a i β)

theorem counit_compat : ((resIsoA.{u, v, w} Q a i β).hom ▷ indA Q a i rfl ≫
    ConcreteAdjunction.res Q i a β ◁ (indIsoA Q a i β).hom) ≫
      (ConcreteAdjunction.adj Q i a β).counit = (adjA Q a i rfl).counit :=
  ObjectProperty.hom_ext _ (counit_compat_nat Q a i β)

theorem dot_compat : dotA.{u, v, w} Q a i (rfl : Si + β = Si + β) ≫ (indIsoA Q a i β).hom =
    (indIsoA Q a i β).hom ≫ ConcreteAdjunction.dot Q i a β :=
  ObjectProperty.hom_ext _ (dot_compat_nat Q a i β)

theorem cross_compat : sameCrossA.{u, v, w} Q a i (rfl : Si + β = Si + β)
      (rfl : Si + (Si + β) = Si + (Si + β)) ≫
      ((indIsoA Q a i β).hom ▷ indA Q a i rfl ≫
        ConcreteAdjunction.ind Q i a β ◁ (indIsoA Q a i (Si + β)).hom) =
    ((indIsoA Q a i β).hom ▷ indA Q a i rfl ≫
        ConcreteAdjunction.ind Q i a β ◁ (indIsoA Q a i (Si + β)).hom) ≫
      ConcreteAdjunction.crossing Q i a β :=
  ObjectProperty.hom_ext _ (cross_compat_nat Q a i β)

end

end Categorification.KLR.CyclotomicAction
