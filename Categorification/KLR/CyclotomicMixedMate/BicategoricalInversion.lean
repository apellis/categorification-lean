/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.BicategoricalComparison

/-!
# BicategoricalInversion

Invertibility of the actual four-object cyclotomic bicategorical mate on
input {i} + γ for distinct colours. Comparison holds over any commutative ring;
inversion assumes a domain, nonzero PBW factorization and KLRSymm.
This does not construct a global RouqFamily, all-multiset mixed inversion,
graded action, or nondegeneracy theorem.
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

/-- Equality of the actual bicategorical mate and the accepted original natural mate. -/
theorem actualMate_hom :
    actualMateNat.{u,v,w} Q a γ i j = MixedNatIso.originalMate Q a γ i j := by
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  have h₁ := actualMateNat_app Q a γ i j M
  have h₂ := MixedNatIso.originalMate_app Q a γ i j M
  exact h₁.trans h₂.symm

/-- The actual component is the original upper Hom equivalence after scalar rebundling. -/
theorem actualMate_app_homToRes (M : ModuleCat.{max u v w} C) :
    (((actualMateNat Q a γ i j).app M).hom).comp
        (MixedNatIso.sourceEquiv Q a γ i j M).symm.toLinearMap =
      homToRes Q i a ({j} + γ)
        ((liftedCounit Q a γ i j M).comp
          (crossingLinear Q a γ i j (Res Q i a γ M))) := by
  rw [actualMate_hom]
  exact MixedNatIso.originalMate_app_homToRes Q a γ i j M

variable (hij : i ≠ j) (hsym : KLRSymm Q)

/-- The accepted inverse on the original four-object square. -/
def actualMateIso : ConcreteAdjunction.res.{u,v,w} Q i a γ ≫
    ConcreteAdjunction.ind Q j a γ ≅
      upperInd Q a γ i j ≫ ConcreteAdjunction.res Q i a ({j} + γ) :=
  ObjectProperty.isoMk _ (MixedNatIso.mixedNatIso Q a γ i j hij hsym)

theorem actualMateIso_hom :
    (actualMateIso.{u,v,w} Q a γ i j hij hsym).hom = actualMate Q a γ i j := by
  apply ObjectProperty.hom_ext
  exact (actualMate_hom Q a γ i j).symm

include hij hsym in
/-- Invertibility of the actual mate, not of a substituted crossing or replacement model. -/
theorem actualMate_isIso : IsIso (actualMate.{u,v,w} Q a γ i j) := by
  rw [← actualMateIso_hom Q a γ i j hij hsym]
  infer_instance

theorem actualMate_forward_inverse :
    actualMate.{u,v,w} Q a γ i j ≫ (actualMateIso Q a γ i j hij hsym).inv = 𝟙 _ := by
  rw [← actualMateIso_hom Q a γ i j hij hsym]
  exact (actualMateIso Q a γ i j hij hsym).hom_inv_id

theorem actualMate_inverse_forward :
    (actualMateIso.{u,v,w} Q a γ i j hij hsym).inv ≫ actualMate Q a γ i j = 𝟙 _ := by
  rw [← actualMateIso_hom Q a γ i j hij hsym]
  exact (actualMateIso Q a γ i j hij hsym).inv_hom_id

end Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
