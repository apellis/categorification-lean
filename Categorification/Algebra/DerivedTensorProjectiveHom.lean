/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DegreeZeroHeart
import Categorification.Algebra.ProjectiveKProjective
import Categorification.Algebra.DerivedTensorHomology
import Categorification.Algebra.DerivedTensorDegreeZero

set_option backward.isDefEq.respectTransparency false

/-!
# The derived tensor on morphisms between projective modules

For a `(A, B)`-bimodule `M` and projective `B`-modules `X`, `Y` in degree `0`, the derived
tensor `M ⊗ᴸ_B -` is the ordinary tensor `M ⊗_B -` on objects (`projectiveTensorIso`) and on
morphisms (`projectiveTensorIso_naturality`). Since modules sit fully faithfully in the
derived category (`degreeZeroModuleFunctor_comp_Q_full`), the derived tensor is bijective on
`Hom(X, Y)` exactly when `f ↦ id ⊗ f : Hom_B(X, Y) → Hom_A(M ⊗_B X, M ⊗_B Y)` is
(`derivedTensor_map_bijective_iff`).

This is used for Webster, arXiv:1309.3796v3, Theorem 6.15: the braiding functor is bijective on
morphisms between projectives in degree `0`.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG
open scoped DG.DegreeZero

variable {A B : Type} [Ring A] [Ring B] (M : Type) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

/-- The ordinary tensor `M ⊗_B X` of modules in degree `0`. -/
abbrev TensorInDegreeZero (X : ModuleCat.{0} B) : Type :=
  TensorProductOver B (InDegreeZero M) (InDegreeZero X)

/-- `M ⊗_B X` of modules in degree `0` is in degree `0`. -/
def placedTensorIso (X : ModuleCat.{0} B) :
    (DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M)).obj
        ((degreeZeroModuleFunctor B).obj X) ≅
      (degreeZeroModuleFunctor A).obj (ModuleCat.of A (TensorInDegreeZero M X)) := by
  let e : TensorInDegreeZero M X ≃ᵈᵍ[A] InDegreeZero (TensorInDegreeZero M X) :=
    DGModuleEquiv.ofDegreeZero (LinearEquiv.refl A _)
      (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
      TensorProductOver.d_inDegreeZero InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _)
  exact DGModuleCat.isoOfDGModuleEquiv e

/-- The map `id ⊗ f : M ⊗_B X → M ⊗_B Y`, linear over `A`. -/
def tensorInDegreeZeroMap {X Y : ModuleCat.{0} B} (f : X →ₗ[B] Y) :
    TensorInDegreeZero M X →ₗ[A] TensorInDegreeZero M Y where
  toFun := TensorProductOver.map LinearMap.id (f : InDegreeZero X →ₗ[B] InDegreeZero Y)
  map_add' := map_add _
  map_smul' a z := by
    induction z using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul m x => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp]
theorem tensorInDegreeZeroMap_tmul {X Y : ModuleCat.{0} B} (f : X →ₗ[B] Y) (m : InDegreeZero M)
    (x : InDegreeZero X) :
    tensorInDegreeZeroMap (A := A) M f (TensorProductOver.tmul B m x) =
      TensorProductOver.tmul B m (show InDegreeZero Y from f x) := rfl

variable [HasDerivedCategory.{0, 0} A] [HasDerivedCategory.{0, 0} B]

/-- On a projective module in degree `0`, `M ⊗ᴸ_B X ≅ M ⊗_B X`. -/
def projectiveTensorIso (X : ModuleCat.{0} B) [Module.Projective B X] :
    (derivedTensor.{0} A B M).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor B).obj X)) ≅
      DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor A).obj
        (ModuleCat.of A (TensorInDegreeZero M X))) :=
  derivedTensorObjIso (A := A) (B := B) (M := M) (P := (degreeZeroModuleFunctor B).obj X)
    (show IsKProjective B (InDegreeZero X) from InDegreeZero.isKProjective) ≪≫
    DG.DerivedCategory.Q.mapIso (placedTensorIso M X)

/-- **The derived tensor on morphisms between projectives is the ordinary tensor.** -/
theorem projectiveTensorIso_naturality {X Y : ModuleCat.{0} B} [Module.Projective B X]
    [Module.Projective B Y] (f : X →ₗ[B] Y) :
    (derivedTensor.{0} A B M).map (DG.DerivedCategory.Q.map
        ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom f))) ≫
        (projectiveTensorIso M Y).hom =
      (projectiveTensorIso M X).hom ≫ DG.DerivedCategory.Q.map ((degreeZeroModuleFunctor A).map
        (ModuleCat.ofHom (tensorInDegreeZeroMap M f))) := by
  have sq : (DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M)).map
        ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom f)) ≫ (placedTensorIso M Y).hom =
      (placedTensorIso M X).hom ≫ (degreeZeroModuleFunctor A).map
        (ModuleCat.ofHom (tensorInDegreeZeroMap M f)) :=
    DGModuleCat.tensor_hom_ext fun _ _ => rfl
  have hX : IsKProjective B ((degreeZeroModuleFunctor B).obj X) :=
    show IsKProjective B (InDegreeZero X) from InDegreeZero.isKProjective
  have hY : IsKProjective B ((degreeZeroModuleFunctor B).obj Y) :=
    show IsKProjective B (InDegreeZero Y) from InDegreeZero.isKProjective
  have h := derivedTensorObjIso_naturality (A := A) (M := M)
    ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom f)) hX hY
  change _ ≫ (derivedTensorObjIso hY).hom ≫ DG.DerivedCategory.Q.map _ =
    ((derivedTensorObjIso hX).hom ≫ DG.DerivedCategory.Q.map _) ≫ DG.DerivedCategory.Q.map _
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, sq, Functor.map_comp,
    Category.assoc]

omit [HasDerivedCategory.{0, 0} A] [HasDerivedCategory.{0, 0} B] in
theorem ofHom_bijective {R : Type} [Ring R] (X Y : ModuleCat.{0} R) :
    Function.Bijective (fun f : X →ₗ[R] Y => ModuleCat.ofHom f) :=
  ⟨fun f g h => by simpa using congrArg ModuleCat.Hom.hom h, fun g => ⟨g.hom, rfl⟩⟩

/-- **The derived tensor is bijective on morphisms between projectives in degree `0` exactly
when the ordinary tensor is.** -/
theorem derivedTensor_map_bijective_iff (X Y : ModuleCat.{0} B) [Module.Projective B X]
    [Module.Projective B Y] :
    Function.Bijective ((derivedTensor.{0} A B M).map :
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor B).obj X) ⟶
          DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor B).obj Y)) → _) ↔
      Function.Bijective (tensorInDegreeZeroMap (A := A) M (X := X) (Y := Y)) := by
  let hB := Functor.FullyFaithful.ofFullyFaithful (degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q)
  let hA := Functor.FullyFaithful.ofFullyFaithful (degreeZeroModuleFunctor A ⋙ DG.DerivedCategory.Q)
  let eX := projectiveTensorIso (A := A) M X
  let eY := projectiveTensorIso (A := A) M Y
  -- `F.map (Q f) = eX ≫ Q (id ⊗ f) ≫ eY⁻¹`.
  have key : ∀ f : X →ₗ[B] Y,
      (derivedTensor.{0} A B M).map ((degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q).map
        (ModuleCat.ofHom f)) =
        eX.hom ≫ (degreeZeroModuleFunctor A ⋙ DG.DerivedCategory.Q).map
          (ModuleCat.ofHom (tensorInDegreeZeroMap M f)) ≫ eY.inv := by
    intro f
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact projectiveTensorIso_naturality (A := A) M f
  let conj : (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor A).obj
        (ModuleCat.of A (TensorInDegreeZero M X))) ⟶
      DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor A).obj
        (ModuleCat.of A (TensorInDegreeZero M Y)))) ≃ _ :=
    ((Iso.homCongr eX eY).symm)
  have hfac : (derivedTensor.{0} A B M).map ∘ (fun f : X →ₗ[B] Y =>
      (degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q).map (ModuleCat.ofHom f)) =
      conj ∘ (fun g => (degreeZeroModuleFunctor A ⋙ DG.DerivedCategory.Q).map
        (ModuleCat.ofHom g)) ∘ tensorInDegreeZeroMap (A := A) M (X := X) (Y := Y) := by
    funext f
    simp only [Function.comp_apply, key, conj, Iso.homCongr_symm, Iso.homCongr_apply,
      Iso.symm_inv, Iso.symm_hom]
  have hBbij : Function.Bijective (fun f : X →ₗ[B] Y =>
      (degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q).map (ModuleCat.ofHom f)) :=
    (hB.map_bijective _ _).comp (ofHom_bijective X Y)
  have hAbij : Function.Bijective (fun g : TensorInDegreeZero M X →ₗ[A] TensorInDegreeZero M Y =>
      (degreeZeroModuleFunctor A ⋙ DG.DerivedCategory.Q).map (ModuleCat.ofHom g)) :=
    (hA.map_bijective _ _).comp (ofHom_bijective (ModuleCat.of A (TensorInDegreeZero M X))
      (ModuleCat.of A (TensorInDegreeZero M Y)))
  constructor
  · intro h
    have h2 : Function.Bijective (conj ∘ (fun g => (degreeZeroModuleFunctor A ⋙
        DG.DerivedCategory.Q).map (ModuleCat.ofHom g)) ∘
        tensorInDegreeZeroMap (A := A) M (X := X) (Y := Y)) :=
      hfac ▸ h.comp hBbij
    exact (Function.Bijective.of_comp_iff' (conj.bijective.comp hAbij) _).1
      (by simpa only [Function.comp_assoc] using h2)
  · intro h
    have h2 := (conj.bijective.comp (hAbij.comp h))
    exact (Function.Bijective.of_comp_iff _ hBbij).1 (by rw [hfac]; exact h2)

end Categorification
