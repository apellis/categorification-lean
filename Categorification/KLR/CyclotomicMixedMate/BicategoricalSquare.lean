/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.BicategoricalCrossing

/-!
# BicategoricalSquare

The original four-object cyclotomic square and its actual bicategorical mate.
The upper edge includes the inverse weight algebra transport.
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

instance upperTransport_additive : (upperTransport.{u,v,w} Q a γ i j).Additive where
  map_add := by intros; rfl

/-- Upper edge uses the actual inverse weight algebra equivalence. -/
def upperInd : ConcreteAdjunction.moduleCategory.{u,v,w} Q a ({i} + γ) ⟶
    ConcreteAdjunction.moduleCategory.{u,v,w} Q a ({i} + ({j} + γ)) :=
  @AdditiveFunctor.of _ _ _ _ _ _
    (inductionFunctor.{u,v,w} Q j a ({i} + γ) ⋙ upperTransport Q a γ i j)
    (inferInstanceAs ((inductionFunctor.{u,v,w} Q j a ({i} + γ) ⋙
      upperTransport Q a γ i j).Additive))

/-- Four-object square, with the genuine signed crossing, not an inverse mate. -/
def crossingCell : ConcreteAdjunction.ind.{u,v,w} Q j a γ ≫
    ConcreteAdjunction.ind Q i a ({j} + γ) ⟶
      ConcreteAdjunction.ind Q i a γ ≫ upperInd Q a γ i j :=
  ObjectProperty.homMk (crossingNat Q a γ i j)

/-- The actual bicategorical mate of the two original induction adjunctions. -/
def actualMate : ConcreteAdjunction.res.{u,v,w} Q i a γ ≫
    ConcreteAdjunction.ind Q j a γ ⟶
      upperInd Q a γ i j ≫ ConcreteAdjunction.res Q i a ({j} + γ) :=
  Bicategory.mateEquiv (ConcreteAdjunction.adj Q i a γ)
    (ConcreteAdjunction.adj Q i a ({j} + γ)) (crossingCell Q a γ i j)

end Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
