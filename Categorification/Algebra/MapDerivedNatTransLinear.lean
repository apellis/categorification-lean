/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedNatTrans
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.Algebra.Algebra.Hom

/-!
# Linearity of passing to derived categories on natural transformations

For exact functors between `R`-linear abelian categories, `NatTrans.mapDerivedCategory` is
`R`-linear (`NatTrans.mapDerivedCategory_smul`). For a composite `F ⋙ G` of exact functors,
conjugation by `Functor.mapDerivedCategoryCompIso` after passing to derived categories is a map
of `R`-algebras `End (F ⋙ G) →ₐ[R] End (F.mapDerivedCategory ⋙ G.mapDerivedCategory)`
(`NatTrans.derivedCompAlgHom`). It transfers polynomial relations between 2-morphisms, such as
the quadratic KLR relation, from module categories to derived categories.
-/

noncomputable section

namespace CategoryTheory

open Category Limits

universe w₁ w₂ w₃

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  (R : Type*) [CommRing R] [Linear R C₁] [Linear R C₂] [Linear R C₃]

namespace NatTrans

section Smul

variable {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [Linear R C₁] in
theorem mapHomologicalComplex_smul_app (r : R) (σ : F ⟶ G) (X : CochainComplex C₁ ℤ) :
    (mapHomologicalComplex (r • σ) (ComplexShape.up ℤ)).app X =
      r • (mapHomologicalComplex σ (ComplexShape.up ℤ)).app X := by
  ext n
  simp

omit [Linear R C₁] in
/-- **`mapDerivedCategory` is `R`-linear.** -/
@[simp]
theorem mapDerivedCategory_smul (r : R) (σ : F ⟶ G) :
    (r • σ).mapDerivedCategory = r • σ.mapDerivedCategory :=
  derivedCategory_ext fun X => by
    simp [mapDerivedCategory_app_Q_obj, mapHomologicalComplex_smul_app, Functor.map_smul]

end Smul

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **Endomorphisms of a composite on derived categories**: `α ↦ c ≫ α.mapDerivedCategory ≫ c⁻¹`
for `c = mapDerivedCategoryCompIso F G`, a map of `R`-algebras. -/
def derivedCompAlgHom :
    End (F ⋙ G) →ₐ[R] End (F.mapDerivedCategory ⋙ G.mapDerivedCategory) where
  toFun α := (Functor.mapDerivedCategoryCompIso F G).hom ≫ α.mapDerivedCategory ≫
    (Functor.mapDerivedCategoryCompIso F G).inv
  map_one' := by
    change _ ≫ (𝟙 (F ⋙ G) : F ⋙ G ⟶ F ⋙ G).mapDerivedCategory ≫ _ = 𝟙 _
    rw [mapDerivedCategory_id, id_comp, Iso.hom_inv_id]
  map_mul' α β := by
    change _ ≫ (β ≫ α).mapDerivedCategory ≫ _ = (_ ≫ β.mapDerivedCategory ≫ _) ≫
      (_ ≫ α.mapDerivedCategory ≫ _)
    rw [mapDerivedCategory_comp]
    simp only [assoc, Iso.inv_hom_id_assoc]
  map_zero' := by
    change _ ≫ (0 : F ⋙ G ⟶ F ⋙ G).mapDerivedCategory ≫ _ = 0
    rw [mapDerivedCategory_zero, zero_comp, comp_zero]
  map_add' α β := by
    change _ ≫ (α + β).mapDerivedCategory ≫ _ = (_ ≫ α.mapDerivedCategory ≫ _) +
      (_ ≫ β.mapDerivedCategory ≫ _)
    rw [mapDerivedCategory_add, Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    change _ ≫ (r • (𝟙 (F ⋙ G) : F ⋙ G ⟶ F ⋙ G)).mapDerivedCategory ≫ _ =
      r • 𝟙 (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    rw [mapDerivedCategory_smul, mapDerivedCategory_id, Linear.smul_comp, Linear.comp_smul,
      id_comp, Iso.hom_inv_id]

omit [Linear R C₁] [Linear R C₂] in
theorem derivedCompAlgHom_apply (α : End (F ⋙ G)) :
    derivedCompAlgHom R F G α = (Functor.mapDerivedCategoryCompIso F G).hom ≫
      α.mapDerivedCategory ≫ (Functor.mapDerivedCategoryCompIso F G).inv :=
  rfl

end NatTrans

end CategoryTheory
