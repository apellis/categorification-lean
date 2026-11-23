/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Derived.ExternalTensor
import DG.Homotopy.BimoduleTensor
import DG.Homotopy.Comparison

set_option backward.isDefEq.respectTransparency false

/-!
# Derived tensor products with an ordinary bimodule

For rings `A`, `B` and an `(A, B)`-bimodule `M` (a left `A`-module with a commuting left
`Bᵐᵒᵖ`-action), the derived functor `M ⊗ᴸ_B - : D(B) ⥤ D(A)` of `N ↦ M ⊗_B N`. The rings are
dg rings concentrated in degree `0` (the scoped instances of `DG.DegreeZero`) and `D(-)` is the
derived category of dg modules of `dg-lean`; `M` itself is not assumed flat or K-projective:
the functor is computed on K-projective resolutions of the argument.

This is the construction underlying B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, Definition 6.6 (the functors `𝔅_w = - ⊗ᴸ B_w`).

## Main definitions and results

* `Categorification.InDegreeZero M`: an ordinary module `M` regarded as a dg module concentrated
  in degree `0`, with its dg bimodule structure.
* `Categorification.derivedTensor A B M`: the derived tensor product `M ⊗ᴸ_B -`.
* `Categorification.derivedTensorObjIso`: on a K-projective dg module `P`,
  `M ⊗ᴸ_B Q P ≅ Q (M ⊗_B P)`.
-/

open CategoryTheory DG

universe w u

noncomputable section

namespace Categorification

/-- An ordinary module, regarded as a dg module concentrated in degree `0`. -/
def InDegreeZero (M : Type*) : Type _ := M

namespace InDegreeZero

variable (M : Type*) [AddCommGroup M]

instance : AddCommGroup (InDegreeZero M) := inferInstanceAs (AddCommGroup M)

instance {R : Type*} [Ring R] [Module R M] : Module R (InDegreeZero M) :=
  inferInstanceAs (Module R M)

instance {R S : Type*} [Ring R] [Ring S] [Module R M] [Module S M] [SMulCommClass R S M] :
    SMulCommClass R S (InDegreeZero M) :=
  inferInstanceAs (SMulCommClass R S M)

instance : DGAddCommGroup (InDegreeZero M) := DGAddCommGroup.degreeZero M

/-- The identification of `InDegreeZero M` with `M`. -/
def equiv : InDegreeZero M ≃+ M := AddEquiv.refl _

theorem mem_grading_iff {n : ℤ} {m : InDegreeZero M} :
    m ∈ grading n ↔ n = 0 ∨ m = 0 :=
  mem_degreeZeroGrading_iff M

theorem d_apply (m : InDegreeZero M) : d m = 0 := rfl

open DG.DegreeZero

variable {M}

theorem ring_mem_grading_iff {R : Type*} [Ring R] {n : ℤ} {r : R} :
    r ∈ grading n ↔ n = 0 ∨ r = 0 :=
  mem_degreeZeroGrading_iff R

theorem ring_d_apply {R : Type*} [Ring R] (r : R) : d r = 0 := rfl

instance {A : Type*} [Ring A] [Module A M] : DGModule A (InDegreeZero M) where
  smul_mem {i j a m} ha hm := by
    rw [ring_mem_grading_iff] at ha
    rw [mem_grading_iff] at hm ⊢
    rcases ha with rfl | rfl
    · rcases hm with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (smul_zero _)
    · exact Or.inr (zero_smul _ _)
  d_smul' {n a} _ m := by
    rw [d_apply, d_apply, ring_d_apply, zero_smul, smul_zero, smul_zero, add_zero]

instance {B : Type*} [Ring B] [Module Bᵐᵒᵖ M] : DGRightModule B (InDegreeZero M) where
  op_smul_mem' {i j b m} hb hm := by
    rw [ring_mem_grading_iff] at hb
    rw [mem_grading_iff] at hm ⊢
    rcases hb with rfl | rfl
    · rcases hm with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (smul_zero _)
    · exact Or.inr (by rw [MulOpposite.op_zero, zero_smul])
  d_op_smul' {j m} _ b := by
    rw [d_apply, d_apply, ring_d_apply, MulOpposite.op_zero, zero_smul, smul_zero, smul_zero,
      add_zero]

instance {A B : Type*} [Ring A] [Ring B] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] :
    DGBimodule A B (InDegreeZero M) :=
  DGBimodule.mk'

end InDegreeZero

open DG.DegreeZero DerivedCategory

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

/-- **The derived tensor product** `M ⊗ᴸ_B - : D(B) ⥤ D(A)` with an ordinary
`(A, B)`-bimodule `M`, computed on K-projective resolutions. -/
def derivedTensor : DerivedCategory.{w, u} B ⥤ DerivedCategory.{w, u} A :=
  (kProjectiveEquivalence.{w} B).inverse ⋙ (DG.HomotopyCategory.subcategoryKProjective B).ι ⋙
    DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ DG.DerivedCategory.Qh

variable {A B M} in
/-- On a K-projective dg module `P`, `M ⊗ᴸ_B Q P ≅ Q (M ⊗_B P)`. -/
def derivedTensorObjIso {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) :
    (derivedTensor.{w} A B M).obj (DG.DerivedCategory.Q.obj P) ≅
      DG.DerivedCategory.Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj P) :=
  let X : KProjective B := ⟨(DG.HomotopyCategory.quotient B).obj P,
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  DG.DerivedCategory.Qh.mapIso ((DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)).mapIso
      ((DG.HomotopyCategory.subcategoryKProjective B).ι.mapIso
        ((kProjectiveEquivalence.{w} B).unitIso.app X).symm) ≪≫
    (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).app P)

/-- An `(C, C')`-bimodule `M` (left `C`, right `C'`), regarded as a
`(C'ᵐᵒᵖ, Cᵐᵒᵖ)`-bimodule, so that tensoring right `C`-modules with `M` becomes a tensor product
of left modules. -/
def OpBimodule (_C : Type*) (M : Type*) : Type _ := M

namespace OpBimodule

variable (C : Type*) [Ring C] (M : Type*) [AddCommGroup M] [Module C M]

instance : AddCommGroup (OpBimodule C M) := inferInstanceAs (AddCommGroup M)

instance {R : Type*} [Ring R] [Module R M] : Module R (OpBimodule C M) :=
  inferInstanceAs (Module R M)

/-- The left action of `C` on `M`, as a right action of `Cᵐᵒᵖ`. -/
instance instModuleOpOp : Module Cᵐᵒᵖᵐᵒᵖ (OpBimodule C M) :=
  Module.compHom M (RingEquiv.opOp C).symm.toRingHom

theorem op_op_smul (c : C) (m : OpBimodule C M) :
    (MulOpposite.op (MulOpposite.op c) • m : OpBimodule C M) = (c • (m : M) : M) := rfl

instance {R : Type*} [Ring R] [Module R M] [SMulCommClass C R M] :
    SMulCommClass R Cᵐᵒᵖᵐᵒᵖ (OpBimodule C M) where
  smul_comm r c m := (smul_comm (α := M) c.unop.unop r m).symm

end OpBimodule

variable (C C' : Type u) [Ring C] [Ring C'] (N : Type u) [AddCommGroup N] [Module C N]
  [Module C'ᵐᵒᵖ N] [SMulCommClass C C'ᵐᵒᵖ N]
  [HasDerivedCategory.{w, u} Cᵐᵒᵖ] [HasDerivedCategory.{w, u} C'ᵐᵒᵖ]

/-- **The derived tensor product on right modules** `- ⊗ᴸ_C N : D(Cᵐᵒᵖ) ⥤ D(C'ᵐᵒᵖ)` with an
ordinary `(C, C')`-bimodule `N`. Right `C`-modules are left `Cᵐᵒᵖ`-modules, and `X ⊗_C N` is
computed as `N ⊗_{Cᵐᵒᵖ} X`. This is the form of Webster's functors `𝔅_w = - ⊗ᴸ B_w`
(arXiv:1309.3796v2, Definition 6.6), which act on right modules. -/
def derivedRightTensor : DerivedCategory.{w, u} Cᵐᵒᵖ ⥤ DerivedCategory.{w, u} C'ᵐᵒᵖ :=
  derivedTensor.{w} C'ᵐᵒᵖ Cᵐᵒᵖ (OpBimodule C N)

end Categorification
