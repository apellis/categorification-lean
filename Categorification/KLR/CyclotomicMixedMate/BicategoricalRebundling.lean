/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.Bundled
import Categorification.TwoRep.CyclotomicRouqAdjunction

/-!
# BicategoricalRebundling

Canonical scalar rebundling for double cyclotomic induction. The crossing uses
the original signed crossing and the inverse upper weight transport.
-/

noncomputable section
open CategoryTheory
namespace Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
open MixedMate Categorification.TwoRep
open scoped ModuleCat.Algebra
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)

abbrev doubleFunctor : ModuleCat.{max u v w} (CycKLR k Q a γ) ⥤
    ModuleCat.{max u v w} (CycKLR k Q a ({i} + ({j} + γ))) :=
  inductionFunctor Q j a γ ⋙ inductionFunctor Q i a ({j} + γ)

/-- Canonical scalar rebundling of actual double induction. -/
def doubleEquiv (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    (doubleFunctor Q a γ i j).obj N ≃ₗ[
      CycKLR k Q a ({i} + ({j} + γ))] Ind Q i a ({j} + γ) (Ind Q j a γ N) :=
  BalancedTensor.congrRight
    (N := (inductionFunctor Q j a γ).obj N) (N' := Ind Q j a γ N)
    (LinearEquiv.refl (CycKLR k Q a ({j} + γ)) _)

def doubleInverse (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    ModuleCat.of (CycKLR k Q a ({i} + ({j} + γ)))
      (Ind Q i a ({j} + γ) (Ind Q j a γ N)) ⟶ (doubleFunctor Q a γ i j).obj N :=
  ModuleCat.ofHom (doubleEquiv Q a γ i j N).symm.toLinearMap

/-- Canonical target rebundling transported through the actual upper scalar functor. -/
def targetRebundle (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    crossingTarget Q a γ i j N ⟶
      (upperTransport Q a γ i j).obj ((doubleFunctor Q a γ j i).obj N) :=
  (upperTransport Q a γ i j).map (doubleInverse Q a γ j i N)

theorem doubleEquiv_natural {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)}
    (f : N ⟶ N') :
    (doubleEquiv Q a γ i j N').toLinearMap.comp ((doubleFunctor Q a γ i j).map f).hom =
      (doubleMap Q a γ i j N f.hom).comp (doubleEquiv Q a γ i j N).toLinearMap := by
  apply BalancedTensor.extB
  intro z m
  rfl

theorem doubleInverse_natural {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)}
    (f : N ⟶ N') :
    ((doubleFunctor Q a γ i j).map f).hom.comp (doubleEquiv Q a γ i j N).symm.toLinearMap =
      (doubleEquiv Q a γ i j N').symm.toLinearMap.comp (doubleMap Q a γ i j N f.hom) := by
  apply BalancedTensor.extB
  intro z m
  rfl

/-- The original crossingLinear, rebundled only by canonical scalar identities. -/
def crossingApp (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    (doubleFunctor Q a γ i j).obj N ⟶
      (upperTransport Q a γ i j).obj ((doubleFunctor Q a γ j i).obj N) :=
  ModuleCat.ofHom (X := (doubleFunctor Q a γ i j).obj N)
      (Y := crossingTarget Q a γ i j N)
      ((crossingLinear Q a γ i j N).comp (doubleEquiv Q a γ i j N).toLinearMap) ≫
    targetRebundle Q a γ i j N


end Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
