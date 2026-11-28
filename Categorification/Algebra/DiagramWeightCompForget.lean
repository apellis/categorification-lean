/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightDerivedComp
import Categorification.Algebra.DiagramWeightForgetTensor
import Categorification.Algebra.WeightForgetQuasiIso
import Categorification.Algebra.WeightSumRepresentable
import Categorification.Algebra.DerivedTensorCompComparison

set_option backward.isDefEq.respectTransparency false

/-!
# The graded Tor condition from the ungraded one

For diagram coefficients `D_M` over `(C_A, C_B)` and `D_N` over `(C_B, C_C)` whose weight pieces
decompose `M` and `N`, if the higher `Tor^B(M, N)` vanish, then the resolution map of every row
`D_N(-, Z)` stays invertible after `D_M ⊗ -`
(`isIso_diagramWeightTensor_map_counit_of_torVanishing`): a K-projective resolution of the row
forgets to a K-projective resolution of `N`, and forgetting the weights reflects
quasi-isomorphisms. This is the hypothesis of the composite of graded derived tensors
(`diagramWeightDerivedTensorCompIso`), used for Webster, arXiv:1309.3796v3, Lemma 6.12 for the
graded braiding functors.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits DG MulOpposite
open scoped DG.DegreeZero

universe u

section Resolution

variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  (G : ℤ → AddSubgroup M)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)]

/-- The resolution map of `N` stays invertible after the tensor with a diagram coefficient `D`
when some K-projective resolution `K ⟶ N` stays a quasi-isomorphism after `D ⊗ -`. -/
theorem isIso_diagramWeightTensor_map_counit_of_resolution
    {N K : CatModule.{u} (WeightCategory B)} (f : K ⟶ N) (hK : CatModule.IsKProjective K)
    (hf : CatModule.IsQuasiIso f)
    (ht : CatModule.IsQuasiIso ((diagramWeightBimodule G hgL hgR).tensorMap f)) :
    IsIso ((diagramWeightTensorHomotopy G hgL hgR ⋙ CatModule.DerivedCategory.Qh).map
      ((CatModuleResolution.resolutionAdjunction.{u, u} (WeightCategory B)).counit.app
        ((CatModule.HomotopyCategory.quotient.{u} (WeightCategory B)).obj N))) := by
  let qB := CatModule.HomotopyCategory.quotient.{u} (WeightCategory B)
  let F := diagramWeightTensorHomotopy G hgL hgR ⋙ CatModule.DerivedCategory.Qh
  let ε := (CatModuleResolution.resolutionAdjunction.{u, u} (WeightCategory B)).counit
  have hε : IsIso (ε.app (qB.obj K)) :=
    CatModuleResolution.isIso_resolutionAdjunction_counit_app
      ((CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff K).mpr hK)
  have hQ : IsIso (CatModule.DerivedCategory.Qh.map (qB.map f)) :=
    (CatModule.DerivedCategory.isIso_Q_map_iff f).mpr hf
  have hFf : IsIso (F.map (qB.map f)) := by
    have e := Functor.isoWhiskerRight (diagramWeightTensorHomotopyFactors G hgL hgR)
      CatModule.DerivedCategory.Qh
    have h₀ : IsIso (CatModule.DerivedCategory.Q.map
        ((diagramWeightBimodule G hgL hgR).tensorMap f)) :=
      (CatModule.DerivedCategory.isIso_Q_map_iff _).mpr ht
    exact (NatIso.isIso_map_iff e f).mpr h₀
  have hn := ε.naturality (qB.map f)
  rw [Functor.id_map] at hn
  have : IsIso ((CatModule.DerivedCategory.Qh ⋙
      CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory B)).map (qB.map f)) :=
    inferInstanceAs (IsIso ((CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory B)).map
      (CatModule.DerivedCategory.Qh.map (qB.map f))))
  have h : IsIso (F.map ((CatModule.DerivedCategory.Qh ⋙
      CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory B)).map (qB.map f)) ≫
      F.map (ε.app (qB.obj N))) := by
    rw [← F.map_comp, hn, F.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map ((CatModule.DerivedCategory.Qh ⋙
    CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory B)).map (qB.map f))) _

end Resolution

variable {A B C M N : Type u} [Ring A] [Ring B] [Ring C]
  [InternalGrading A] [InternalGrading B] [InternalGrading C]
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N)
  [DirectSum.Decomposition G] [DirectSum.Decomposition H]
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)]
  [DG.HasDerivedCategory.{u,u} A] [DG.HasDerivedCategory.{u,u} B]

set_option hygiene false in
local notation "D₁" => diagramWeightBimodule G hgL hgR
set_option hygiene false in
local notation "D₂" => diagramWeightBimodule H hhL hhR

/-- Forgetting the weights of a row `D_N(-, Z)` gives `N`. -/
def diagramWeightForgetLeftIso (Z : WeightCategory C) :
    (CatModule.weightForget B).obj ((D₂).left Z) ≅ DGModuleCat.of B (InDegreeZero N) :=
  let e₀ : CatModule.representableW.{u} (WeightCategory C) Z ≅ CatModule.representable Z :=
    CatModule.isoMk (fun _ => AddEquiv.ulift) Iff.rfl (fun _ => rfl) (fun _ _ => rfl)
  (CatModule.weightForget B).mapIso ((diagramWeightTensorRepresentableIso H hhL hhR Z).symm ≪≫
      (CatBimodule.tensorFunctor.{u, u} (D₂)).mapIso e₀.symm) ≪≫
    (diagramWeightForgetTensorIso H hhL hhR).app _ ≪≫
    (DGModuleCat.tensorFunctor B (InDegreeZero N)).mapIso
      (CatModule.weightForgetRepresentableIso (A := C) Z.as) ≪≫
    tensorRegularCoefficientIso B C N

/-- **The graded Tor condition from the ungraded one**: if `Tor^B_{>0}(M, N) = 0`, the
resolution map of each row `D_N(-, Z)` stays invertible after `D_M ⊗ -`. -/
theorem isIso_diagramWeightTensor_map_counit_of_torVanishing (Z : WeightCategory C)
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((DG.DerivedCategory.homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{u} A B M).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of B (InDegreeZero N)))))) :
    IsIso ((diagramWeightTensorHomotopy G hgL hgR ⋙ CatModule.DerivedCategory.Qh).map
      ((CatModuleResolution.resolutionAdjunction.{u, u} (WeightCategory B)).counit.app
        ((CatModule.HomotopyCategory.quotient.{u} (WeightCategory B)).obj ((D₂).left Z)))) := by
  obtain ⟨K, f, hK, hf, -⟩ := CatModule.exists_kProjective_resolution ((D₂).left Z)
  apply isIso_diagramWeightTensor_map_counit_of_resolution G hgL hgR f hK hf
  apply CatModule.IsQuasiIso.of_weightSumMap
  change ((CatModule.weightForget A).map ((D₁).tensorMap f)).hom.IsQuasiIso
  rw [← DG.DerivedCategory.isIso_Q_map_iff]
  let S := (CatModule.weightForget B).obj ((D₂).left Z)
  let g := (CatModule.weightForget B).map f
  have hg : IsIso (DG.DerivedCategory.Q.map g) :=
    (DG.DerivedCategory.isIso_Q_map_iff g).mpr (CatModule.IsQuasiIso.weightSumMap hf)
  have hP : IsKProjective.{u} B ((CatModule.weightForget B).obj K) := hK.weightSum
  -- the resolution map of `N` tensored with `M` is invertible
  have h₀ := isIso_derivedTensorResolutionMap.{u} (A := A) M N hv
  have h₀' : IsIso ((DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M) ⋙
      DG.DerivedCategory.Qh).map ((resolutionAdjunction.{u} B).counit.app
        ((DG.HomotopyCategory.quotient B).obj (DGModuleCat.of B (InDegreeZero N))))) := by
    unfold derivedTensorResolutionMap at h₀
    exact IsIso.of_isIso_comp_right (DG.DerivedCategory.Qh.map
      ((DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M)).map
        ((resolutionAdjunction.{u} B).counit.app
          ((DG.HomotopyCategory.quotient B).obj (DGModuleCat.of B (InDegreeZero N))))))
      (DG.DerivedCategory.Qh.map ((DG.HomotopyCategory.tensorFunctorQuotientIso A
        (InDegreeZero M)).hom.app (DGModuleCat.of B (InDegreeZero N))))
  have h₁ := isIso_map_counit_of_iso
    ((DG.HomotopyCategory.quotient B).mapIso (diagramWeightForgetLeftIso H hhL hhR Z)) h₀'
  have hres : IsIso (derivedTensorResolutionMap.{u} (A := A) M S) := by
    unfold derivedTensorResolutionMap
    have : IsIso (DG.DerivedCategory.Qh.map
        ((DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M)).map
          ((resolutionAdjunction.{u} B).counit.app ((DG.HomotopyCategory.quotient B).obj S)))) :=
      h₁
    infer_instance
  have h := derivedTensorObjIso_hom_comp (A := A) (M := M) hP g
  have h₂ : IsIso ((derivedTensorObjIso (A := A) (M := M) hP).hom ≫
      DG.DerivedCategory.Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map g)) := by
    rw [h]
    infer_instance
  have h₃ : IsIso (DG.DerivedCategory.Q.map
      ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map g)) :=
    IsIso.of_isIso_comp_left (derivedTensorObjIso (A := A) (M := M) hP).hom _
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight (diagramWeightForgetTensorIso G hgL hgR)
    DG.DerivedCategory.Q) f).mpr h₃

end Categorification
