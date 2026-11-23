/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensor
import DG.Homotopy.ExternalTensorKProjective

set_option backward.isDefEq.respectTransparency false

/-!
# Composition of derived tensor products

For dg rings `A`, `B`, `C`, a dg `(A, B)`-bimodule `M` and a dg `(B, C)`-bimodule `N`, the
derived tensor products `M ⊗ᴸ_B - : D(B) ⥤ D(A)` and `N ⊗ᴸ_C - : D(C) ⥤ D(B)`, computed on
K-projective resolutions, compose to `(M ⊗_B N) ⊗ᴸ_C -` when `N` is K-projective over `B`: then
`N ⊗_C -` sends K-projective resolutions to K-projective modules, so no second resolution is
needed.

This is how the functors `𝔈_i`, `𝔉_i` of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, are composed with the braiding functors `𝔅_w` (Definition 6.6) in the
proof of Proposition 6.7: their bimodules are projective over the target ring, and projective
modules in degree `0` are K-projective (`Categorification.InDegreeZero.isKProjective`).

## Main definitions and results

* `Categorification.dgDerivedTensor A B X`: the derived tensor product `X ⊗ᴸ_B -` with a dg
  `(A, B)`-bimodule `X`; `derivedTensor A B M` is the case `X = InDegreeZero M`.
* `Categorification.tensorFunctor_obj_mem_subcategoryKProjective`: `N ⊗_C -` preserves
  K-projective objects of the homotopy category when `N` is K-projective over `B`.
* `Categorification.dgDerivedTensorCompIso`:
  `N ⊗ᴸ_C - ⋙ M ⊗ᴸ_B - ≅ (M ⊗_B N) ⊗ᴸ_C -` for `N` K-projective over `B`.
-/

open CategoryTheory DG DG.DerivedCategory

universe w u

noncomputable section

namespace Categorification

section Defs

variable (A B : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (X : Type u) [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

/-- **The derived tensor product** `X ⊗ᴸ_B - : D(B) ⥤ D(A)` with a dg `(A, B)`-bimodule `X`,
computed on K-projective resolutions. -/
def dgDerivedTensor : DerivedCategory.{w, u} B ⥤ DerivedCategory.{w, u} A :=
  (kProjectiveEquivalence.{w} B).inverse ⋙ (DG.HomotopyCategory.subcategoryKProjective B).ι ⋙
    DG.HomotopyCategory.tensorFunctor A X ⋙ DG.DerivedCategory.Qh

end Defs

open DG.DegreeZero in
theorem derivedTensor_eq_dgDerivedTensor (A B : Type u) [Ring A] [Ring B] (M : Type u)
    [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
    [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B] :
    derivedTensor.{w} A B M = dgDerivedTensor.{w} A B (InDegreeZero M) := rfl

variable {A B C : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [Ring C] [DGAddCommGroup C] [DGRing C]
  (M : Type u) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]
  (N : Type u) [AddCommGroup N] [DGAddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N]
  [DGBimodule B C N]

variable {N} in
/-- `N ⊗_C -` sends K-projective objects of the homotopy category to K-projective objects when
`N` is K-projective over `B`. -/
theorem tensorFunctor_obj_mem_subcategoryKProjective (hN : IsKProjective.{u} B N)
    {Y : DG.HomotopyCategory.{u} C} (hY : DG.HomotopyCategory.subcategoryKProjective C Y) :
    DG.HomotopyCategory.subcategoryKProjective B
      ((DG.HomotopyCategory.tensorFunctor B N).obj Y) := by
  obtain ⟨P, rfl⟩ := DG.HomotopyCategory.quotient_obj_surjective Y
  rw [DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff] at hY
  exact (DG.HomotopyCategory.subcategoryKProjective B).prop_of_iso
    ((DG.HomotopyCategory.tensorFunctorQuotientIso B N).app P).symm
    ((DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff _).mpr
      (hN.tensorProductOver hY))

variable {N} in
/-- `N ⊗_C -` on K-projective objects, for `N` K-projective over `B`. -/
def kProjectiveTensor (hN : IsKProjective.{u} B N) : KProjective C ⥤ KProjective B :=
  (DG.HomotopyCategory.subcategoryKProjective B).lift
    ((DG.HomotopyCategory.subcategoryKProjective C).ι ⋙ DG.HomotopyCategory.tensorFunctor B N)
    fun Y => tensorFunctor_obj_mem_subcategoryKProjective hN Y.property

open TensorProductOver.RightAction in
/-- `M ⊗_B (N ⊗_C -) ≅ (M ⊗_B N) ⊗_C -` on homotopy categories. -/
def homotopyTensorFunctorCompIso :
    DG.HomotopyCategory.tensorFunctor (B := C) B N ⋙
        DG.HomotopyCategory.tensorFunctor (B := B) A M ≅
      DG.HomotopyCategory.tensorFunctor (B := C) A (TensorProductOver B M N) :=
  DG.HomotopyCategory.liftFunctorCompIso _ _
      (DG.HomotopyCategory.tensorFunctor_homotopic (B := C) B N)
      (DG.HomotopyCategory.tensorFunctor_homotopic (B := B) A M) ≪≫
    DG.HomotopyCategory.liftNatIso _ (DG.HomotopyCategory.tensorFunctor_homotopic (B := C) A _)
      (DGModuleCat.tensorFunctorCompIso (A := B) (B := C) (C := A) N M)

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [HasDerivedCategory.{w, u} C]

variable {N} in
open TensorProductOver.RightAction in
/-- **Derived tensor products compose**: for `N` K-projective over `B`,
`M ⊗ᴸ_B (N ⊗ᴸ_C -) ≅ (M ⊗_B N) ⊗ᴸ_C -`. -/
def dgDerivedTensorCompIso (hN : IsKProjective.{u} B N) :
    dgDerivedTensor.{w} B C N ⋙ dgDerivedTensor.{w} A B M ≅
      dgDerivedTensor.{w} A C (TensorProductOver B M N) :=
  let L := kProjectiveTensor hN
  let EB := kProjectiveEquivalence.{w} B
  let EC := kProjectiveEquivalence.{w} C
  let ιB := (DG.HomotopyCategory.subcategoryKProjective B).ι
  let ιC := (DG.HomotopyCategory.subcategoryKProjective C).ι
  let TN := DG.HomotopyCategory.tensorFunctor (B := C) B N
  let TM := DG.HomotopyCategory.tensorFunctor (B := B) A M
  let TMN := DG.HomotopyCategory.tensorFunctor (B := C) A (TensorProductOver B M N)
  let Q := DG.DerivedCategory.Qh.{w, u} (A := A)
  let QB := DG.DerivedCategory.Qh.{w, u} (A := B)
  let e₁ : (ιC ⋙ TN ⋙ QB) ⋙ EB.inverse ≅ L :=
    (Functor.isoWhiskerLeft L EB.unitIso.symm ≪≫ Functor.rightUnitor L :
      (L ⋙ EB.functor) ⋙ EB.inverse ≅ L)
  let e₂ : L ⋙ ιB ⋙ TM ⋙ Q ≅ ιC ⋙ TMN ⋙ Q :=
    (Functor.isoWhiskerLeft ιC
      (Functor.isoWhiskerRight (homotopyTensorFunctorCompIso M N) Q) :
        ιC ⋙ (TN ⋙ TM) ⋙ Q ≅ ιC ⋙ TMN ⋙ Q)
  let α : (ιC ⋙ TN ⋙ QB) ⋙ EB.inverse ⋙ ιB ⋙ TM ⋙ Q ≅ ιC ⋙ TMN ⋙ Q :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ (ιB ⋙ TM ⋙ Q) ≪≫ e₂
  (Functor.isoWhiskerLeft EC.inverse α : EC.inverse ⋙ (ιC ⋙ TN ⋙ QB) ⋙ EB.inverse ⋙ ιB ⋙ TM ⋙ Q
    ≅ EC.inverse ⋙ ιC ⋙ TMN ⋙ Q)

end Categorification
