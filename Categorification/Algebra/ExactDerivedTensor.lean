/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ProjectiveFlat

set_option backward.isDefEq.respectTransparency false

/-!
# Derived tensor products with bimodules that are projective over the source

For rings `A`, `B` (dg rings in degree `0`) and an `(A, B)`-bimodule `M` that is projective as
a right `B`-module, `M ⊗_B -` preserves quasi-isomorphisms
(`Categorification.InDegreeZero.isQuasiIso_lTensor`), so the derived tensor product
`M ⊗ᴸ_B -` is computed by the ordinary tensor product on every dg module, not only on
K-projective ones.

This is how B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Proposition 6.7, treats the functors `𝔈_i`, `𝔉_i`: they are
tensor products with bimodules that are projective on both sides, so they are exact and need
no resolution.

## Main results

* `Categorification.tensorFunctor_map_mem_quasiIso`: `M ⊗_B -` preserves quasi-isomorphisms
  of the homotopy category.
* `Categorification.QhCompDerivedTensorIso`: `Qh ⋙ (M ⊗ᴸ_B -) ≅ (M ⊗_B -) ⋙ Qh`.
* `Categorification.QCompDerivedTensorIso`: `Q ⋙ (M ⊗ᴸ_B -) ≅ (M ⊗_B -) ⋙ Q`.
-/

open CategoryTheory DG DG.DegreeZero DG.DerivedCategory

universe w u

noncomputable section

namespace Categorification

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M]

variable {A B} in
/-- For `M` projective as a right `B`-module, `M ⊗_B -` preserves quasi-isomorphisms of the
homotopy category. -/
theorem tensorFunctor_map_mem_quasiIso {X Y : DG.HomotopyCategory.{u} B} {f : X ⟶ Y}
    (hf : DG.HomotopyCategory.quasiIso B f) :
    DG.HomotopyCategory.quasiIso A
      ((DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)).map f) := by
  obtain ⟨X, rfl⟩ := DG.HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y, rfl⟩ := DG.HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨f, rfl⟩ := (DG.HomotopyCategory.quotient B).map_surjective f
  rw [DG.HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoOfNatIso
    (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)) (Arrow.mk f))).mpr ?_
  exact (DG.HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
    (InDegreeZero.isQuasiIso_lTensor (A := A) hf)

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

/-- The functor `D(B) ⥤ D(A)` induced by `M ⊗_B -` on homotopy categories, for `M` projective
as a right `B`-module. -/
def exactDerivedTensor : DerivedCategory.{w, u} B ⥤ DerivedCategory.{w, u} A :=
  Localization.lift (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh)
    (fun _ _ _ hf => Localization.inverts Qh (DG.HomotopyCategory.quasiIso A) _
      (tensorFunctor_map_mem_quasiIso M hf))
    Qh

instance exactDerivedTensorLifting :
    Localization.Lifting Qh (DG.HomotopyCategory.quasiIso B)
      (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh)
      (exactDerivedTensor.{w} A B M) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qh))

/-- For `M` projective as a right `B`-module, the derived tensor product `M ⊗ᴸ_B -` (computed
on K-projective resolutions) is the functor induced by `M ⊗_B -`. -/
def derivedTensorIsoExact :
    derivedTensor.{w} A B M ≅ exactDerivedTensor.{w} A B M :=
  let EB := kProjectiveEquivalence.{w} B
  let ιB := (DG.HomotopyCategory.subcategoryKProjective B).ι
  let L := exactDerivedTensor.{w} A B M
  (Functor.isoWhiskerLeft (EB.inverse ⋙ ιB)
      (Localization.Lifting.iso Qh (DG.HomotopyCategory.quasiIso B) _ L).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫ EB.counitIso) L ≪≫
    Functor.leftUnitor L :
      (EB.inverse ⋙ ιB) ⋙ DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh ≅ L)

/-- **`M ⊗ᴸ_B -` is computed by `M ⊗_B -` on the homotopy category** when `M` is projective as
a right `B`-module. -/
def QhCompDerivedTensorIso :
    Qh ⋙ derivedTensor.{w} A B M ≅
      DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh :=
  Functor.isoWhiskerLeft Qh (derivedTensorIsoExact A B M) ≪≫
    Localization.Lifting.iso Qh (DG.HomotopyCategory.quasiIso B) _ _

/-- **`M ⊗ᴸ_B -` is computed by `M ⊗_B -` on every dg module** when `M` is projective as a
right `B`-module (no resolution is needed). -/
def QCompDerivedTensorIso :
    DG.DerivedCategory.Q ⋙ derivedTensor.{w} A B M ≅
      DGModuleCat.tensorFunctor A (InDegreeZero M) ⋙ DG.DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (QhCompDerivedTensorIso A B M) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)) _ ≪≫
    Functor.associator _ _ _

end Categorification
