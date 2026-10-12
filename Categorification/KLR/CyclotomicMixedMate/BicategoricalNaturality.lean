/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.BicategoricalRebundling

/-!
# BicategoricalNaturality

Naturality of the original crossing and of the target scalar rebundling on
arbitrary modules. These squares supply the four-object bicategorical crossing.
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

abbrev rawDouble (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :=
  ModuleCat.of (CycKLR k Q a ({i} + ({j} + γ)))
    (Ind Q i a ({j} + γ) (Ind Q j a γ N))

def rawMap {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)} (f : N ⟶ N') :
    rawDouble Q a γ i j N ⟶ rawDouble Q a γ i j N' :=
  ModuleCat.ofHom (doubleMap Q a γ i j N f.hom)

theorem inverse_natural_cat {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)}
    (f : N ⟶ N') :
    rawMap Q a γ i j f ≫ doubleInverse Q a γ i j N' =
      doubleInverse Q a γ i j N ≫ (doubleFunctor Q a γ i j).map f := by
  apply ModuleCat.hom_ext
  exact (doubleInverse_natural Q a γ i j f).symm

def targetMap {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)} (f : N ⟶ N') :
    crossingTarget Q a γ i j N ⟶ crossingTarget Q a γ i j N' :=
  (upperTransport Q a γ i j).map (rawMap Q a γ j i f)

def bundledTargetMap {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)} (f : N ⟶ N') :
    (upperTransport Q a γ i j).obj ((doubleFunctor Q a γ j i).obj N) ⟶
      (upperTransport Q a γ i j).obj ((doubleFunctor Q a γ j i).obj N') :=
  (upperTransport Q a γ i j).map ((doubleFunctor Q a γ j i).map f)

theorem mapSquare {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} (p : W ⟶ X) (q : X ⟶ Z) (r : W ⟶ Y) (s : Y ⟶ Z)
    (h : p ≫ q = r ≫ s) : F.map p ≫ F.map q = F.map r ≫ F.map s := by
  rw [← F.map_comp, ← F.map_comp, h]

def MappedSquare {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} (p : W ⟶ X) (q : X ⟶ Z) (r : W ⟶ Y) (s : Y ⟶ Z) : Prop :=
  F.map p ≫ F.map q = F.map r ≫ F.map s

theorem targetRebundle_natural {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)}
    (f : N ⟶ N') :
    MappedSquare (upperTransport Q a γ i j)
      (rawMap Q a γ j i f) (doubleInverse Q a γ j i N')
      (doubleInverse Q a γ j i N) ((doubleFunctor Q a γ j i).map f) :=
  mapSquare (upperTransport Q a γ i j)
    (rawMap Q a γ j i f) (doubleInverse Q a γ j i N')
    (doubleInverse Q a γ j i N) ((doubleFunctor Q a γ j i).map f)
    (inverse_natural_cat Q a γ j i f)

def rawCrossing (N : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    rawDouble Q a γ i j N ⟶ crossingTarget Q a γ i j N :=
  ModuleCat.ofHom (X := rawDouble Q a γ i j N) (Y := crossingTarget Q a γ i j N)
    (crossingLinear Q a γ i j N)

theorem rawCrossing_natural {N N' : ModuleCat.{max u v w} (CycKLR k Q a γ)}
    (f : N ⟶ N') :
    rawMap Q a γ i j f ≫ rawCrossing Q a γ i j N' =
      rawCrossing Q a γ i j N ≫ targetMap Q a γ i j f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact (LinearMap.congr_fun (crossing_natural Q a γ i j N N' f.hom) t).symm

end Categorification.KLR.KLRAlgebra.AbsentColour.BicategoricalMixedMate
