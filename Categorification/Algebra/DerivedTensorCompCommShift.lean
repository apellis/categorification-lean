/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExactDerivedTensor
import Categorification.Algebra.DerivedTensorTriangulated
import Categorification.Algebra.ResolutionAdjunction
import Categorification.Algebra.DerivedTensorCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# The composite of exact derived tensor products commutes with the shift

For rings `A`, `B`, `C` (dg rings in degree `0`), an `(A, B)`-bimodule `M` projective as a right
`B`-module and a `(B, C)`-bimodule `N`, the isomorphisms computing `M ⊗ᴸ_B -` by `M ⊗_B -`
(`QhCompDerivedTensorIso`, `QCompDerivedTensorIso`) and the composition isomorphism
`M ⊗ᴸ_B (N ⊗ᴸ_C -) ≅ (M ⊗_B N) ⊗ᴸ_C -` (`derivedTensorCompIsoOfProjective`) commute with the
homological shift, for the shift structures of the derived tensor functors. The first is the
resolution map tensored with `M` (`QhCompDerivedTensorIso_hom_eq`).

Consequently, an endomorphism of `(N ⊗ᴸ_C -) ⋙ (M ⊗ᴸ_B -)` that is induced on dg modules by an
endomorphism of `(N ⊗_C -) ⋙ (M ⊗_B -)` commuting with the shift commutes with the shift
(`derivedTensorTwo_commShift_of_QComp`). This is the input for the shift compatibility of the
crossing on `𝔈_i²` in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21.

## Main results

* `natTransCommShift_of_whiskerLeft_essSurj` (generic).
* `QhCompDerivedTensorIso_commShift`, `QCompDerivedTensorIso_commShift`.
* `tensorFunctorCompIso_inDegreeZero_commShift`,
  `homotopyTensorFunctorCompIso_inDegreeZero_commShift`, `tensorCoeffNat_degreeZero_commShift`.
* `derivedTensorCompIsoOfProjective_commShift`.
* `QCompDerivedTensorTwoIso`, `derivedTensorTwo_commShift_of_QComp`.
-/

open CategoryTheory DG DG.DegreeZero DG.DerivedCategory

universe w u

noncomputable section

namespace Categorification

section Generic

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]

/-- A natural transformation commutes with the shift as soon as its whiskering by an
essentially surjective functor commuting with the shift does. -/
theorem natTransCommShift_of_whiskerLeft_essSurj (H : C ⥤ D) [H.CommShift ℤ] [H.EssSurj]
    {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift (Functor.whiskerLeft H τ) ℤ] : NatTrans.CommShift τ ℤ where
  shift_comm n := by
    have key : ∀ X, ((F.commShiftIso n).hom ≫ Functor.whiskerRight τ _).app (H.obj X) =
        (Functor.whiskerLeft _ τ ≫ (G.commShiftIso n).hom).app (H.obj X) := by
      intro X
      have e := NatTrans.shift_app_comm (Functor.whiskerLeft H τ) n X
      simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
        Functor.comp_obj, Category.assoc] at e
      let h : H.obj ((shiftFunctor C n).obj X) ⟶
          (shiftFunctor D n).obj (H.obj X) := (H.commShiftIso n).hom.app X
      have hnat := τ.naturality h
      change F.map h ≫ τ.app ((shiftFunctor D n).obj (H.obj X)) =
        τ.app (H.obj ((shiftFunctor C n).obj X)) ≫ G.map h at hnat
      rw [← Category.assoc (τ.app _) (G.map h), ← hnat, Category.assoc] at e
      exact (cancel_epi (F.map h)).mp e
    ext Y
    let e := H.objObjPreimageIso Y
    have n₁ := ((F.commShiftIso n).hom ≫ Functor.whiskerRight τ _).naturality e.hom
    have n₂ := (Functor.whiskerLeft _ τ ≫ (G.commShiftIso n).hom).naturality e.hom
    rw [← cancel_epi ((shiftFunctor D n ⋙ F).map e.hom), n₁, n₂, key]

end Generic

section DGLevel

open TensorProductOver.RightAction

variable {A B C : Type u} [Ring A] [Ring B] [Ring C]

variable (M N : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]

/-- The balanced tensor product of two bimodules concentrated in degree `0` is concentrated in
degree `0`. -/
theorem tensorProductOver_inDegreeZero_mem_grading_zero
    (x : TensorProductOver B (InDegreeZero M) (InDegreeZero N)) : x ∈ grading 0 := by
  induction x using TensorProductOver.induction_on with
  | zero => exact (grading 0).zero_mem
  | tmul m n =>
    simpa using TensorProductOver.tmul_mem_grading
      ((InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inl rfl) : m ∈ grading 0)
      ((InDegreeZero.mem_grading_iff (M := N)).mpr (Or.inl rfl) : n ∈ grading 0)
  | add x y hx hy => exact (grading 0).add_mem hx hy

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

instance tensorProductOver_inDegreeZero_fact :
    Fact (∀ x : TensorProductOver B (InDegreeZero M) (InDegreeZero N), x ∈ grading 0) :=
  ⟨tensorProductOver_inDegreeZero_mem_grading_zero M N⟩

/-- **Associativity of the dg tensor product commutes with the shift**, for bimodules
concentrated in degree `0`. -/
instance tensorFunctorCompIso_inDegreeZero_commShift :
    NatTrans.CommShift (DGModuleCat.tensorFunctorCompIso (A := B) (B := C) (C := A)
      (InDegreeZero N) (InDegreeZero M)).hom ℤ where
  shift_comm n := by
    ext X : 2
    exact DGModuleCat.tensor_hom_ext₂ _ _ fun _ _ _ => rfl

/-- **The coefficient map of a dg bimodule map commutes with the shift**, for dg bimodules
concentrated in degree `0`. -/
instance tensorCoeffNat_degreeZero_commShift {X X' : Type u} [AddCommGroup X]
    [DGAddCommGroup X] [Module A X] [Module Cᵐᵒᵖ X] [DGBimodule A C X]
    [Fact (∀ m : X, m ∈ grading 0)] [AddCommGroup X'] [DGAddCommGroup X'] [Module A X']
    [Module Cᵐᵒᵖ X'] [DGBimodule A C X'] [Fact (∀ m : X', m ∈ grading 0)]
    (f : X →ᵈᵍ[A] X') (hf : ∀ (c : C) (m : X), f (MulOpposite.op c • m) = MulOpposite.op c • f m) :
    NatTrans.CommShift (tensorCoeffNat f hf) ℤ where
  shift_comm n := by
    ext Y : 2
    exact DGModuleCat.tensor_hom_ext (A := A) (M := X)
      (N := DGModuleCat.of C (Shift n Y)) fun _ _ => rfl

theorem whiskerLeft_quotient_homotopyTensorFunctorCompIso :
    Functor.whiskerLeft (DG.HomotopyCategory.quotient C)
        (homotopyTensorFunctorCompIso (A := A) (B := B) (C := C) (InDegreeZero M)
          (InDegreeZero N)).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (DG.HomotopyCategory.tensorFunctorQuotientIso B (InDegreeZero N)).hom
          (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (DGModuleCat.tensorFunctor B (InDegreeZero N))
          (DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (DGModuleCat.tensorFunctorCompIso (A := B) (B := C) (C := A)
          (InDegreeZero N) (InDegreeZero M)).hom (DG.HomotopyCategory.quotient A) ≫
        (DG.HomotopyCategory.tensorFunctorQuotientIso A
          (TensorProductOver B (InDegreeZero M) (InDegreeZero N))).inv := by
  ext X
  simp [homotopyTensorFunctorCompIso, DG.HomotopyCategory.liftFunctorCompIso,
    DG.HomotopyCategory.liftNatIso, DG.HomotopyCategory.tensorFunctorQuotientIso,
    DG.HomotopyCategory.liftFunctorQuotientIso]
  erw [Quotient.natTransLift_app, Quotient.natTransLift_app]
  simp only [DG.HomotopyCategory.tensorFunctor]
  rfl

/-- **`M ⊗_B (N ⊗_C -) ≅ (M ⊗_B N) ⊗_C -` on homotopy categories commutes with the shift**, for
bimodules concentrated in degree `0`. -/
instance homotopyTensorFunctorCompIso_inDegreeZero_commShift :
    NatTrans.CommShift (homotopyTensorFunctorCompIso (A := A) (B := B) (C := C) (InDegreeZero M)
      (InDegreeZero N)).hom ℤ := by
  have : NatTrans.CommShift (Functor.whiskerLeft (DG.HomotopyCategory.quotient C)
      (homotopyTensorFunctorCompIso (A := A) (B := B) (C := C) (InDegreeZero M)
        (InDegreeZero N)).hom) ℤ := by
    rw [whiskerLeft_quotient_homotopyTensorFunctorCompIso]
    infer_instance
  exact natTransCommShift_of_whiskerLeft_essSurj (DG.HomotopyCategory.quotient C) _

end DGLevel

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

theorem QhCompDerivedTensorIso_hom_eq :
    (QhCompDerivedTensorIso.{w} A B M).hom =
      Functor.whiskerLeft Qh (Functor.associator (kProjectiveEquivalence.{w} B).inverse
          (DG.HomotopyCategory.subcategoryKProjective B).ι
          (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh)).inv ≫
        (Functor.associator Qh (resolutionFunctor.{w} B)
          (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh)).inv ≫
        Functor.whiskerRight (resolutionAdjunction.{w} B).counit
          (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh) ≫
        (Functor.leftUnitor _).hom := by
  ext Y
  have h := (Localization.Lifting.iso Qh (DG.HomotopyCategory.quasiIso B)
    (DG.HomotopyCategory.tensorFunctor A (InDegreeZero M) ⋙ Qh)
    (exactDerivedTensor.{w} A B M)).hom.naturality ((resolutionAdjunction.{w} B).counit.app Y)
  simp only [Functor.comp_map, Functor.id_obj] at h
  rw [Qh_map_resolutionAdjunction_counit_app] at h
  simp only [QhCompDerivedTensorIso, derivedTensorIsoExact, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id, Category.assoc]
  rw [h]
  erw [Iso.inv_hom_id_app_assoc]
  exact (Category.id_comp _).symm

instance QhCompDerivedTensorIso_commShift :
    NatTrans.CommShift (QhCompDerivedTensorIso.{w} A B M).hom ℤ := by
  rw [QhCompDerivedTensorIso_hom_eq]
  infer_instance

instance QCompDerivedTensorIso_commShift :
    NatTrans.CommShift (QCompDerivedTensorIso.{w} A B M).hom ℤ := by
  simp only [QCompDerivedTensorIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

section Comp

open TensorProductOver.RightAction

variable {A B} {C : Type u} [Ring C] (N : Type u) [AddCommGroup N] [Module B N]
  [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N] [HasDerivedCategory.{w, u} C]

instance dgDerivedTensor_tensorProductOver_commShift :
    (dgDerivedTensor.{w} A C
      (TensorProductOver B (InDegreeZero M) (InDegreeZero N))).CommShift ℤ := by
  unfold dgDerivedTensor
  infer_instance

/-- **`M ⊗ᴸ_B (N ⊗ᴸ_C -) ≅ (M ⊗_B N) ⊗ᴸ_C -` commutes with the shift**, for `M` projective as a
right `B`-module. -/
instance derivedTensorCompIsoOfProjective_commShift :
    NatTrans.CommShift (derivedTensorCompIsoOfProjective.{w} (A := A) (B := B) (C := C) M N).hom
      ℤ := by
  simp only [derivedTensorCompIsoOfProjective, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

end Comp

section TwoStep

variable {A B} {C : Type u} [Ring C] (N : Type u) [AddCommGroup N] [Module B N]
  [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N] [Module.Projective Cᵐᵒᵖ N]
  [HasDerivedCategory.{w, u} C]

/-- `Q ⋙ (N ⊗ᴸ_C -) ⋙ (M ⊗ᴸ_B -) ≅ ((N ⊗_C -) ⋙ (M ⊗_B -)) ⋙ Q`, for `M`, `N` projective as
right modules: two copies of `QCompDerivedTensorIso`. -/
def QCompDerivedTensorTwoIso :
    DG.DerivedCategory.Q ⋙ derivedTensor.{w} B C N ⋙ derivedTensor.{w} A B M ≅
      (DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M)) ⋙ DG.DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompDerivedTensorIso.{w} B C N) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (QCompDerivedTensorIso.{w} A B M) ≪≫ (Functor.associator _ _ _).symm

instance QCompDerivedTensorTwoIso_commShift :
    NatTrans.CommShift (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ℤ := by
  simp only [QCompDerivedTensorTwoIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

/-- **Reduction of shift compatibility to dg modules.** An endomorphism `α` of
`(N ⊗ᴸ_C -) ⋙ (M ⊗ᴸ_B -)` commutes with the shift as soon as, on dg modules and through
`QCompDerivedTensorTwoIso`, it is induced by an endomorphism `θ` of
`(N ⊗_C -) ⋙ (M ⊗_B -)` that commutes with the shift. -/
theorem derivedTensorTwo_commShift_of_QComp
    (α : derivedTensor.{w} B C N ⋙ derivedTensor.{w} A B M ⟶
      derivedTensor.{w} B C N ⋙ derivedTensor.{w} A B M)
    (θ : DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙
        DGModuleCat.tensorFunctor A (InDegreeZero M) ⟶
      DGModuleCat.tensorFunctor B (InDegreeZero N) ⋙ DGModuleCat.tensorFunctor A (InDegreeZero M))
    [NatTrans.CommShift θ ℤ]
    (h : Functor.whiskerLeft DG.DerivedCategory.Q α ≫
        (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom =
      (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ≫
        Functor.whiskerRight θ DG.DerivedCategory.Q) :
    NatTrans.CommShift α ℤ := by
  have : NatTrans.CommShift (Functor.whiskerLeft DG.DerivedCategory.Q α) ℤ := by
    have h' : Functor.whiskerLeft DG.DerivedCategory.Q α =
        (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).hom ≫
          Functor.whiskerRight θ DG.DerivedCategory.Q ≫
            (QCompDerivedTensorTwoIso.{w} (A := A) (B := B) (C := C) M N).inv := by
      rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
    rw [h']
    infer_instance
  have := Localization.essSurj (DG.DerivedCategory.Q (A := C)) (DGModuleCat.quasiIso C)
  exact natTransCommShift_of_whiskerLeft_essSurj DG.DerivedCategory.Q α

end TwoStep

end Categorification
