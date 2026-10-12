/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.BicategoricalNaturality

/-!
# BicategoricalCrossing

The original signed crossing as a natural transformation between the actual
double induction functors, with canonical scalar rebundling.
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

def sourceRebundle (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    (doubleFunctor Q a γ i j).obj N ⟶ rawDouble Q a γ i j N :=
  ModuleCat.ofHom (doubleEquiv Q a γ i j N).toLinearMap

theorem sourceRebundle_natural {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)}
    (f : N ⟶ N') :
    (doubleFunctor Q a γ i j).map f ≫ sourceRebundle Q a γ i j N' =
      sourceRebundle Q a γ i j N ≫ rawMap Q a γ i j f := by
  apply ModuleCat.hom_ext
  exact doubleEquiv_natural Q a γ i j f

theorem pasteSquare {C : Type*} [Category C] {A B D E F G : C}
    (p : A ⟶ B) (q : D ⟶ E) (r : F ⟶ G)
    (s : A ⟶ D) (t : B ⟶ E) (x : D ⟶ F) (y : E ⟶ G)
    (h : p ≫ t = s ≫ q) (h' : q ≫ y = x ≫ r) :
    p ≫ (t ≫ y) = (s ≫ x) ≫ r := by
  rw [← Category.assoc, h, Category.assoc, h', Category.assoc]

def IsNatural {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (app : ∀ X, F.obj X ⟶ G.obj X) : Prop :=
  ∀ {X Y} (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

theorem rebundledCrossing_natural :
    IsNatural (doubleFunctor.{u,v,w} Q a γ i j)
      (doubleFunctor Q a γ j i ⋙ upperTransport Q a γ i j) (crossingApp Q a γ i j) := by
  intro N N' f
  have ht := targetRebundle_natural Q a γ i j f
  have hc := pasteSquare _ _ _ _ _ _ _ (rawCrossing_natural Q a γ i j f) ht
  have hs := pasteSquare _ _ _ _ _ _ _ (sourceRebundle_natural Q a γ i j f) hc
  exact hs

def crossingNat :
    inductionFunctor.{u,v,w} Q j a γ ⋙ inductionFunctor Q i a ({j} + γ) ⟶
      inductionFunctor Q i a γ ⋙ (inductionFunctor Q j a ({i} + γ) ⋙
        upperTransport Q a γ i j) where
  app := crossingApp Q a γ i j
  naturality {_ _} f := rebundledCrossing_natural Q a γ i j f

end Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
