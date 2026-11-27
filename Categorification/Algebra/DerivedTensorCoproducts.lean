/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorTriangulated
import DG.Homotopy.Products
import DG.Homotopy.Coproducts
import DG.Derived.Coproducts

set_option backward.isDefEq.respectTransparency false

/-!
# Derived tensor products preserve coproducts

The balanced tensor product `M ⊗_B -` of dg modules commutes with direct sums
(`Categorification.tensorDirectSumEquiv`), so it preserves coproducts on dg modules and on
homotopy categories. The K-projective objects of the homotopy category are closed under
coproducts, being a left orthogonal. Hence the derived tensor product `M ⊗ᴸ_B -`, computed on
K-projective resolutions, preserves coproducts (`Categorification.derivedTensor_preservesCoproducts`),
and so does `- ⊗ᴸ_C N` on right modules.

This is used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 6.12, where the functors `𝔅_w = - ⊗ᴸ B_w` of Definition 6.6 are compared
on the whole derived category through its compact generator.
-/

open CategoryTheory Limits DG DirectSum

universe w' u

noncomputable section

namespace Categorification

/-! ### Left orthogonals are closed under colimits -/

instance leftOrthogonal_isClosedUnderColimitsOfShape {C : Type*} [Category C] [HasZeroMorphisms C]
    (P : ObjectProperty C) (J : Type*) [Category J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩ Y f hY
    exact p.isColimit.hom_ext fun j => by
      rw [Limits.comp_zero]
      exact p.prop_diag_obj j _ hY

/-! ### Tensor products and direct sums -/

section DirectSum

variable (A : Type u) {B : Type u} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type u) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]
  {J : Type u} [DecidableEq J] (F : J → Type u) [∀ j, AddCommGroup (F j)]
  [∀ j, DGAddCommGroup (F j)] [∀ j, Module B (F j)] [∀ j, DGModule B (F j)]

open TensorProductOver

/-- The comparison `⨁ⱼ (M ⊗_B Fⱼ) → M ⊗_B ⨁ⱼ Fⱼ`. -/
def tensorDirectSumHom :
    (⨁ j, TensorProductOver B M (F j)) →ᵈᵍ[A] TensorProductOver B M (⨁ j, F j) :=
  DGModuleHom.toModule fun j => DGModuleHom.lTensor A M (DGModuleHom.lof B F j)

theorem tensorDirectSumHom_of (j : J) (m : M) (y : F j) :
    tensorDirectSumHom A M F (DirectSum.of _ j (tmul B m y)) =
      tmul B m (DirectSum.of F j y) :=
  DGModuleHom.toModule_lof _ j _

/-- The inverse comparison, as an additive map: `m ⊗ (yⱼ)ⱼ ↦ (m ⊗ yⱼ)ⱼ`. -/
def tensorDirectSumInv :
    TensorProductOver B M (⨁ j, F j) →+ ⨁ j, TensorProductOver B M (F j) :=
  lift (AddMonoidHom.mk' (fun m => DirectSum.toAddMonoid fun j =>
      (DirectSum.of (fun j => TensorProductOver B M (F j)) j).comp (tmulAddHom B M (F j) m))
      fun m m' => DirectSum.addHom_ext fun j y => by
        simp)
    fun b m x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of j y =>
        simp only [AddMonoidHom.mk'_apply, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
        rw [show b • DirectSum.of F j y = DirectSum.of F j (b • y) from
          (DirectSum.lof_eq_of B J F j y ▸ (DirectSum.lof B J F j).map_smul b y).symm.trans
            (DirectSum.lof_eq_of B J F j _), DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
          TensorProductOver.tmulAddHom_apply, TensorProductOver.tmulAddHom_apply, op_smul_tmul]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]

omit [DGAddCommGroup B] [DGAddCommGroup M] [∀ j, DGAddCommGroup (F j)]
  [∀ j, DGModule B (F j)] in
theorem tensorDirectSumInv_tmul_of (j : J) (m : M) (y : F j) :
    tensorDirectSumInv M F (tmul B m (DirectSum.of F j y)) =
      DirectSum.of (fun j => TensorProductOver B M (F j)) j (tmul B m y) := by
  simp [tensorDirectSumInv]

theorem tensorDirectSumInv_hom (x : ⨁ j, TensorProductOver B M (F j)) :
    tensorDirectSumInv M F (tensorDirectSumHom A M F x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | tmul m y => rw [tensorDirectSumHom_of, tensorDirectSumInv_tmul_of]
    | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tensorDirectSumHom_inv (x : TensorProductOver B M (⨁ j, F j)) :
    tensorDirectSumHom A M F (tensorDirectSumInv M F x) = x := by
  induction x using TensorProductOver.induction_on with
  | zero => simp
  | tmul m x =>
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y => rw [tensorDirectSumInv_tmul_of, tensorDirectSumHom_of]
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Tensor products commute with direct sums**: `⨁ⱼ (M ⊗_B Fⱼ) ≅ M ⊗_B ⨁ⱼ Fⱼ` as dg
modules. -/
def tensorDirectSumEquiv :
    (⨁ j, TensorProductOver B M (F j)) ≃ᵈᵍ[A] TensorProductOver B M (⨁ j, F j) where
  __ := (tensorDirectSumHom A M F).toLinearMap
  invFun := tensorDirectSumInv M F
  left_inv := tensorDirectSumInv_hom A M F
  right_inv := tensorDirectSumHom_inv A M F
  map_mem' := (tensorDirectSumHom A M F).map_mem
  map_d' := (tensorDirectSumHom A M F).map_d

end DirectSum

/-! ### Preservation of coproducts -/

section Preservation

variable (A : Type u) {B : Type u} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type u) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- `M ⊗_B -` on dg modules preserves coproducts. -/
instance tensorFunctor_preservesCoproducts (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (DGModuleCat.tensorFunctor A M (B := B)) where
  preservesColimit {K} := by
    classical
    let F : J → DGModuleCat.{u} B := K.obj ∘ Discrete.mk
    suffices h : PreservesColimit (Discrete.functor F) (DGModuleCat.tensorFunctor A M (B := B)) from
      preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm
    refine preservesColimit_of_preserves_colimit_cocone
      (DGModuleCat.coproductCoconeIsColimit.{u, u} F)
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_)
    refine IsColimit.ofIsoColimit
      (DGModuleCat.coproductCoconeIsColimit.{u, u}
        fun j => (DGModuleCat.tensorFunctor A M (B := B)).obj (F j))
      (Cofan.ext (DGModuleCat.isoOfDGModuleEquiv
        (tensorDirectSumEquiv A M (fun j => (F j : Type u)))) fun j => ?_)
    refine DGModuleCat.hom_ext (DGModuleHom.ext fun x => ?_)
    induction x using TensorProductOver.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul m y =>
      exact tensorDirectSumHom_of A M (fun j => (F j : Type u)) j m y
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `M ⊗_B -` on homotopy categories preserves coproducts. -/
instance homotopyTensorFunctor_preservesCoproducts (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (DG.HomotopyCategory.tensorFunctor A M (B := B)) where
  preservesColimit {K} := by
    classical
    let G : J → DGModuleCat.{u} B := fun j => (K.obj ⟨j⟩).as
    let e : K ≅ Discrete.functor G ⋙ DG.HomotopyCategory.quotient B :=
      Discrete.natIso fun _ => Iso.refl _
    suffices h : PreservesColimit (Discrete.functor G ⋙ DG.HomotopyCategory.quotient B)
        (DG.HomotopyCategory.tensorFunctor A M (B := B)) from
      preservesColimit_of_iso_diagram _ e.symm
    have hc := DGModuleCat.coproductCoconeIsColimit.{u, u} G
    have : PreservesColimit (Discrete.functor G)
        (DG.HomotopyCategory.quotient B ⋙ DG.HomotopyCategory.tensorFunctor A M (B := B)) :=
      preservesColimit_of_natIso _ (DG.HomotopyCategory.tensorFunctorQuotientIso A M).symm
    refine preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (DG.HomotopyCategory.quotient B) hc) ?_
    exact isColimitOfPreserves
      (DG.HomotopyCategory.quotient B ⋙ DG.HomotopyCategory.tensorFunctor A M (B := B)) hc

end Preservation

section Derived

open DG.DerivedCategory
open scoped DG.DegreeZero

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

instance subcategoryKProjective_ι_preservesCoproducts {B : Type u} [Ring B] [DGAddCommGroup B]
    [DGRing B] (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (DG.HomotopyCategory.subcategoryKProjective.{u} B).ι :=
  inferInstance

/-- **The derived tensor product `M ⊗ᴸ_B -` preserves coproducts.** -/
instance derivedTensor_preservesCoproducts [HasDerivedCategory.{w', u} A]
    [HasDerivedCategory.{w', u} B] (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (derivedTensor.{w'} A B M) := by
  unfold derivedTensor
  infer_instance

variable (C C' N : Type u) [Ring C] [Ring C'] [AddCommGroup N] [Module C N] [Module C'ᵐᵒᵖ N]
  [SMulCommClass C C'ᵐᵒᵖ N] [HasDerivedCategory.{w', u} Cᵐᵒᵖ] [HasDerivedCategory.{w', u} C'ᵐᵒᵖ]

/-- **The derived tensor product `- ⊗ᴸ_C N` on right modules preserves coproducts.** -/
instance derivedRightTensor_preservesCoproducts (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (derivedRightTensor.{w'} C C' N) := by
  unfold derivedRightTensor
  infer_instance

end Derived

end Categorification
