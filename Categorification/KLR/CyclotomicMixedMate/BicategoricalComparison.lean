/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.AdditiveMateFormula

/-!
# BicategoricalComparison

Comparison of the actual four-object bicategorical mate with the ordinary
cyclotomic Hom-equivalence, retaining the canonical source scalar rebundling.
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
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)

def actualMateNat : MixedNatIso.sourceFunctor.{u,v,w} Q a γ i j ⟶
    MixedNatIso.targetFunctor Q a γ i j := (actualMate Q a γ i j).hom

theorem actualMateNat_app (M : ModuleCat.{max u v w} C) :
    ((actualMateNat Q a γ i j).app M).hom =
      (mate Q a γ i j M).comp (MixedNatIso.sourceEquiv Q a γ i j M).toLinearMap := by
  have h := PrivateAdditiveMate.mate_app_homEquiv
    (L := ConcreteAdjunction.ind Q i a γ) (R := ConcreteAdjunction.res Q i a γ)
    (L' := ConcreteAdjunction.ind Q i a ({j} + γ))
    (R' := ConcreteAdjunction.res Q i a ({j} + γ))
    (G := ConcreteAdjunction.ind Q j a γ) (H := upperInd Q a γ i j)
    (AdditiveCat.toAdjunction (ConcreteAdjunction.adj Q i a γ))
    (AdditiveCat.toAdjunction (ConcreteAdjunction.adj Q i a ({j} + γ)))
    (crossingCell Q a γ i j) M
  apply BalancedTensor.extB
  intro y m
  apply Subtype.ext
  have he := congrArg (fun f : (MixedNatIso.sourceFunctor Q a γ i j).obj M ⟶
      (MixedNatIso.targetFunctor Q a γ i j).obj M =>
      (f.hom (BalancedTensor.tmul y m)).1) h
  exact he

end Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
