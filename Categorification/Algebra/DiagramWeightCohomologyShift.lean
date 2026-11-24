/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import DG.Derived.DimensionShift

/-!
# Dimension shifting at a weight

At a fixed weight, the cohomology sequence of a distinguished triangle
identifies the connecting map with an isomorphism or a kernel whenever
the relevant middle cohomology vanishes.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits Pretriangulated DG

universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  [CatModule.HasDerivedCategory.{z,w} C]

variable (X : C)

local instance : (CatModule.DerivedCategory.cohomologyFunctor X 0).ShiftSequence ℤ := by
  let : (CatModule.HomotopyCategory.cohomologyFunctor.{w} X 0).ShiftSequence ℤ := by
    change (CatModule.HomotopyCategory.eval.{w} X ⋙
      _root_.HomotopyCategory.homologyFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (CatModule.DerivedCategory.cohomologyFunctorFactorsh X 0) ℤ
    (CatModule.DerivedCategory.cohomologyFunctor X)
    (CatModule.DerivedCategory.cohomologyFunctorFactorsh X)

variable (T : Triangle (CatModule.DerivedCategory.{z,w} C))
  (hT : T ∈ distTriang _)

/-- With vanishing middle cohomology in two successive degrees, the connecting
map at a fixed weight is an isomorphism. -/
def weightCohomologyShiftIso (n : ℤ)
    (h₀ : IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj T.obj₂))
    (h₁ : IsZero ((CatModule.DerivedCategory.cohomologyFunctor X (n+1)).obj T.obj₂)) :
    (CatModule.DerivedCategory.cohomologyFunctor X n).obj T.obj₃ ≅
      (CatModule.DerivedCategory.cohomologyFunctor X (n+1)).obj T.obj₁ := by
  let F := CatModule.DerivedCategory.cohomologyFunctor X 0
  let δ := F.homologySequenceδ T n (n+1) rfl
  have : Mono δ := (F.homologySequence_exact₃ T hT n (n+1) rfl).mono_g_iff.mpr
    (h₀.eq_of_src _ _)
  have : Epi δ := (F.homologySequence_exact₁ T hT n (n+1) rfl).epi_f_iff.mpr
    (h₁.eq_of_tgt _ _)
  letI : IsIso δ := isIso_of_mono_of_epi δ
  exact (asIso δ : (F.shift n).obj T.obj₃ ≅ (F.shift (n+1)).obj T.obj₁)

/-- If the middle cohomology vanishes in this degree, the connecting map
identifies the third term's cohomology with the kernel of the next map. -/
def weightCohomologyShiftKernelIso (n : ℤ)
    (h₀ : IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj T.obj₂)) :
    (CatModule.DerivedCategory.cohomologyFunctor X n).obj T.obj₃ ≅
      kernel ((CatModule.DerivedCategory.cohomologyFunctor X (n+1)).map T.mor₁) := by
  let F := CatModule.DerivedCategory.cohomologyFunctor X 0
  let δ := F.homologySequenceδ T n (n+1) rfl
  have : Mono δ := (F.homologySequence_exact₃ T hT n (n+1) rfl).mono_g_iff.mpr
    (h₀.eq_of_src _ _)
  let h := (F.homologySequence_exact₁ T hT n (n+1) rfl).fIsKernel
  exact IsLimit.conePointUniqueUpToIso h (limit.isLimit _)

end Categorification
