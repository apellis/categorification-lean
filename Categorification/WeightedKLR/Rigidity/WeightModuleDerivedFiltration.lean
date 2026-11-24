/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorDerived
import Categorification.WeightedKLR.Rigidity.WeightModuleFiltration

/-!
# Derived tensor on a finite filtration of weight modules

This is the passage from layerwise vanishing to vanishing for the filtered
input in Webster, arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG MulOpposite
open scoped DG.DegreeZero

universe u v

variable {A B P : Type u} [Ring A] [Ring B]
  [InternalGrading A] [InternalGrading B] [BigradedDGRing A] [BigradedDGRing B]
  [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hr : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

/-- For the derived diagram tensor, cohomology vanishing at a specified weight and degree
passes from the layers of a finite filtration to the filtered module. -/
theorem WeightModuleFiltration.diagramWeightDerivedTensor_cohomology_isZero
    {ι : Type*} {L : ι → CatModule.{u} (WeightCategory B)}
    {layers : List ι} {M : CatModule.{u} (WeightCategory B)}
    (h : WeightModuleFiltration L layers M) (X : WeightCategory A) (n : ℤ)
    (hL : ∀ i ∈ layers, IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj (CatModule.DerivedCategory.Q.obj (L i))))) :
    IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj (CatModule.DerivedCategory.Q.obj M))) := by
  let F := diagramWeightDerivedTensor G hl hr ⋙ CatModule.DerivedCategory.cohomologyFunctor X n
  let Q : ObjectProperty (CatModule.DerivedCategory.{v,u} (WeightCategory B)) :=
    fun Z => IsZero (F.obj Z)
  let _ : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e he => IsZero.of_iso he (F.mapIso e).symm⟩
  exact diagramWeightDerivedTensor_cohomology_isZero_of_extensions G hl hr X n
    Q (fun _ hz => hz) _ (h.extensionProductIter Q (fun _ hz => F.map_isZero hz) hL)

end Categorification
