/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DGBimoduleTensorShift
import Categorification.Algebra.DerivedTensorComp
import Categorification.Algebra.DerivedTensorCoefficient
import Categorification.Algebra.DerivedTensorCoproducts
import Categorification.Algebra.CompactGeneratorIsIso
import Categorification.Algebra.DerivedTensorCompCommShift
import Categorification.Algebra.DerivedTensorCompComparison
import DG.Derived.Perfect

set_option backward.isDefEq.respectTransparency false

/-!
# Quasi-isomorphism invariance of derived tensor products in the bimodule

Let `A`, `B` be rings concentrated in degree `0` and `X` a dg `(A, B)`-bimodule in arbitrary
degrees. The derived tensor product `X ⊗ᴸ_B - : D(B) ⥤ D(A)` (`dgDerivedTensor`) is a
triangulated functor (`dgDerivedTensor_isTriangulated_sign`, with the Koszul-sign shift
structure `dgDerivedTensorSignCommShift`) and preserves coproducts.

A morphism of dg bimodules `f : X → X'` induces a natural transformation
`X ⊗ᴸ_B - ⟶ X' ⊗ᴸ_B -` (`dgDerivedTensorCoeffMap`) compatible with the shifts. At the regular
module it is `f` itself (`dgDerivedTensorCoeffMap_app_regular`). Since `B` compactly generates
`D(B)`, **if `f` is a quasi-isomorphism then `X ⊗ᴸ_B - ≅ X' ⊗ᴸ_B -`**
(`isIso_dgDerivedTensorCoeffMap`, `dgDerivedTensorIsoOfQuasiIso`). This is the standard fact
that the derived tensor product depends on the bimodule only up to quasi-isomorphism.

It is used for the bimodule form of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, proof of Proposition 7.22, where the bimodule of `S` is replaced by
its truncation and then by its cohomology. The results are generic dg algebra.
-/

open CategoryTheory Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

universe u

noncomputable section

namespace Categorification

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

section DGLevel

open TensorProductOver

variable {A B : Type u} [Ring A] [Ring B]
  {X X' : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] [AddCommGroup X'] [DGAddCommGroup X'] [Module A X'] [Module Bᵐᵒᵖ X']
  [DGBimodule A B X']

omit [Module Bᵐᵒᵖ X] [DGBimodule A B X] [Module Bᵐᵒᵖ X'] [DGBimodule A B X'] in
theorem signTwist_comm_dgModuleHom (f : X →ᵈᵍ[A] X') (j : ℤ) (m : X) :
    f (signTwist X j m) = signTwist X' j (f m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_homogeneous m =>
    rw [signTwist_of_mem j m.2, signTwist_of_mem j (f.map_mem m.2), Units.smul_def, map_zsmul,
      Units.smul_def]
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add, map_add]

/-- **The coefficient map of a dg bimodule map commutes with the shift**, for dg bimodules in
arbitrary degrees and the Koszul-sign shift structures. -/
theorem tensorCoeffNat_signCommShift (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) :
    NatTrans.CommShift (tensorCoeffNat f hf) ℤ where
  shift_comm n := by
    ext Y : 2
    exact DGModuleCat.tensor_hom_ext (A := A) (M := X)
      (N := DGModuleCat.of B (Shift n Y)) fun m y =>
        (congrArg (fun m' : X' =>
          (Shift.mk n (tmul B m' (Shift.unmk n (show Shift n Y from y))) :
            Shift n (TensorProductOver B X' Y)))
          (signTwist_comm_dgModuleHom f n m) : _)

end DGLevel

section Homotopy

variable {A B : Type u} [Ring A] [Ring B]
  {X X' : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] [AddCommGroup X'] [DGAddCommGroup X'] [Module A X'] [Module Bᵐᵒᵖ X']
  [DGBimodule A B X']

/-- **The coefficient map on homotopy categories commutes with the shift.** -/
theorem homotopyTensorCoeffNat_signCommShift (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) :
    NatTrans.CommShift (homotopyTensorCoeffNat f hf) ℤ := by
  have := homotopyTensorFunctorQuotientIso_signCommShift B X A
  have := homotopyTensorFunctorQuotientIso_signCommShift B X' A
  have := tensorCoeffNat_signCommShift f hf
  have he : Functor.whiskerLeft (DG.HomotopyCategory.quotient B) (homotopyTensorCoeffNat f hf) =
      (DG.HomotopyCategory.tensorFunctorQuotientIso A X).hom ≫
        Functor.whiskerRight (tensorCoeffNat f hf) (DG.HomotopyCategory.quotient A) ≫
        (DG.HomotopyCategory.tensorFunctorQuotientIso A X').inv := rfl
  have : NatTrans.CommShift
      (Functor.whiskerLeft (DG.HomotopyCategory.quotient B) (homotopyTensorCoeffNat f hf)) ℤ := by
    rw [he]
    infer_instance
  exact natTransCommShift_of_whiskerLeft_essSurj (DG.HomotopyCategory.quotient B) _

end Homotopy

section Derived

variable (A B : Type u) [Ring A] [Ring B]
  (X : Type u) [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]

noncomputable local instance kProjectiveInverse_signCommShift :
    (kProjectiveEquivalence.{u} B).inverse.CommShift ℤ := by
  letI : (kProjectiveEquivalence.{u} B).functor.CommShift ℤ :=
    inferInstanceAs ((kProjectiveFunctor.{u} B).CommShift ℤ)
  exact (kProjectiveEquivalence.{u} B).commShiftInverse ℤ

local instance kProjectiveInverse_isTriangulated_sign :
    (kProjectiveEquivalence.{u} B).inverse.IsTriangulated := by
  let : (kProjectiveEquivalence.{u} B).functor.CommShift ℤ :=
    inferInstanceAs ((kProjectiveFunctor.{u} B).CommShift ℤ)
  let : (kProjectiveEquivalence.{u} B).functor.IsTriangulated :=
    inferInstanceAs ((kProjectiveFunctor.{u} B).IsTriangulated)
  let : (kProjectiveEquivalence.{u} B).CommShift ℤ :=
    (kProjectiveEquivalence.{u} B).commShift_of_functor ℤ
  let : (kProjectiveEquivalence.{u} B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  infer_instance

/-- **`X ⊗ᴸ_B -` commutes with the shift**, for a dg bimodule `X` in arbitrary degrees. -/
@[instance_reducible]
def dgDerivedTensorSignCommShift : (dgDerivedTensor.{u} A B X).CommShift ℤ := by
  unfold dgDerivedTensor
  infer_instance

attribute [local instance] dgDerivedTensorSignCommShift

/-- **`X ⊗ᴸ_B -` is triangulated**, for a dg bimodule `X` in arbitrary degrees. -/
theorem dgDerivedTensor_isTriangulated_sign : (dgDerivedTensor.{u} A B X).IsTriangulated := by
  have := homotopyTensorFunctor_isTriangulated_sign B X A
  unfold dgDerivedTensor
  infer_instance

/-- `X ⊗ᴸ_B -` preserves coproducts. -/
instance dgDerivedTensor_preservesCoproducts (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (dgDerivedTensor.{u} A B X) := by
  unfold dgDerivedTensor
  infer_instance

variable {A B X} in
/-- On a K-projective dg module `P`, `X ⊗ᴸ_B Q P ≅ Q (X ⊗_B P)`. -/
def dgDerivedTensorObjIso {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) :
    (dgDerivedTensor.{u} A B X).obj (Q.obj P) ≅
      Q.obj ((DGModuleCat.tensorFunctor A X).obj P) :=
  let V : KProjective B := ⟨(DG.HomotopyCategory.quotient B).obj P,
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  Qh.mapIso ((DG.HomotopyCategory.tensorFunctor A X).mapIso
      ((DG.HomotopyCategory.subcategoryKProjective B).ι.mapIso
        ((kProjectiveEquivalence.{u} B).unitIso.app V).symm) ≪≫
    (DG.HomotopyCategory.tensorFunctorQuotientIso A X).app P)

variable {X} {X' : Type u} [AddCommGroup X'] [DGAddCommGroup X'] [Module A X'] [Module Bᵐᵒᵖ X']
  [DGBimodule A B X']

/-- **The natural transformation `X ⊗ᴸ_B - ⟶ X' ⊗ᴸ_B -` of a dg bimodule map** `f : X → X'`. -/
def dgDerivedTensorCoeffMap (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) :
    dgDerivedTensor.{u} A B X ⟶ dgDerivedTensor.{u} A B X' :=
  Functor.whiskerLeft (kProjectiveEquivalence.{u} B).inverse
    (Functor.whiskerLeft (DG.HomotopyCategory.subcategoryKProjective B).ι
      (Functor.whiskerRight (homotopyTensorCoeffNat f hf) (Qh (A := A))))

/-- The coefficient map commutes with the shift. -/
theorem dgDerivedTensorCoeffMap_commShift (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) :
    NatTrans.CommShift (dgDerivedTensorCoeffMap A B f hf) ℤ := by
  have hα := homotopyTensorCoeffNat_signCommShift f hf
  have hβ : NatTrans.CommShift (Functor.whiskerRight (homotopyTensorCoeffNat f hf) (Qh (A := A)))
      ℤ := NatTrans.CommShift.whiskerRight _ _ ℤ
  have hγ : NatTrans.CommShift (Functor.whiskerLeft
      (DG.HomotopyCategory.subcategoryKProjective B).ι
      (Functor.whiskerRight (homotopyTensorCoeffNat f hf) (Qh (A := A)))) ℤ :=
    NatTrans.CommShift.whiskerLeft (F₁ := (DG.HomotopyCategory.subcategoryKProjective B).ι) _ _ _ ℤ
  exact NatTrans.CommShift.whiskerLeft (F₁ := (kProjectiveEquivalence.{u} B).inverse) _ _ _ ℤ

/-- On a K-projective representative, the derived coefficient map is the dg tensor map. -/
theorem dgDerivedTensorObjIso_coeff_naturality (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m)
    {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) :
    (dgDerivedTensorCoeffMap A B f hf).app (Q.obj P) ≫ (dgDerivedTensorObjIso (X := X') hP).hom =
      (dgDerivedTensorObjIso (X := X) hP).hom ≫ Q.map ((tensorCoeffNat f hf).app P) := by
  let E := kProjectiveEquivalence.{u} B
  let ι := (DG.HomotopyCategory.subcategoryKProjective B).ι
  let V : KProjective B := ⟨(DG.HomotopyCategory.quotient B).obj P,
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  let r : ι.obj (E.inverse.obj (Q.obj P)) ⟶
      (DG.HomotopyCategory.quotient B).obj P := ι.map (E.unitIso.inv.app V)
  let T := DG.HomotopyCategory.tensorFunctor (B := B) A X
  let T' := DG.HomotopyCategory.tensorFunctor (B := B) A X'
  let η := tensorCoeffNat f hf
  let α := homotopyTensorCoeffNat f hf
  let e := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A X
  let e' := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A X'
  have h := α.naturality r
  have hα : α.app ((DG.HomotopyCategory.quotient B).obj P) ≫ e'.hom.app P =
      e.hom.app P ≫ (DG.HomotopyCategory.quotient A).map (η.app P) := by
    change (e.hom.app P ≫ (DG.HomotopyCategory.quotient A).map (η.app P) ≫ e'.inv.app P) ≫
      e'.hom.app P = _
    simp
  simp only [dgDerivedTensorObjIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    Iso.symm_hom]
  change Qh.map (α.app (ι.obj (E.inverse.obj (Q.obj P)))) ≫
      (Qh.map (T'.map r) ≫ Qh.map (e'.hom.app P)) =
    (Qh.map (T.map r) ≫ Qh.map (e.hom.app P)) ≫
      Qh.map ((DG.HomotopyCategory.quotient A).map (η.app P))
  simp only [← Functor.map_comp, Category.assoc]
  rw [← Category.assoc (α.app _) (T'.map r), ← h, Category.assoc, hα]

end Derived

section Regular

variable {A B : Type u} [Ring A] [Ring B]
  (X : Type u) [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X]

/-- The right unit isomorphism `X ⊗_B B ≅ X` of a dg bimodule, in `DGModuleCat A`. -/
def tensorRegularDGIso :
    (DGModuleCat.tensorFunctor A X).obj (DGModuleCat.of B B) ≅ DGModuleCat.of A X := by
  let e := TensorProductOver.rid B X
  have h (a : A) (z : TensorProductOver B X B) : e (a • z) = a • e z := by
    induction z using TensorProductOver.induction_on with
    | zero => simp
    | tmul m b =>
      change e (TensorProductOver.tmul B (a • m) b) = a • e (TensorProductOver.tmul B m b)
      simpa only [e, TensorProductOver.rid_tmul] using (smul_comm a (op b) m).symm
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  exact DGModuleCat.isoOfDGModuleEquiv
    { toLinearEquiv := { e.toAddEquiv with map_smul' := h }
      map_mem' := fun hz => e.map_mem hz
      map_d' := e.map_d }

variable {X} {X' : Type u} [AddCommGroup X'] [DGAddCommGroup X'] [Module A X'] [Module Bᵐᵒᵖ X']
  [DGBimodule A B X']

theorem tensorCoeffNat_app_regular (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) :
    (tensorCoeffNat f hf).app (DGModuleCat.of B B) ≫ (tensorRegularDGIso X').hom =
      (tensorRegularDGIso X).hom ≫ DGModuleCat.ofHom f :=
  DGModuleCat.tensor_hom_ext (A := A) (M := X) fun m b => (hf b m).symm

end Regular

section QuasiIso

variable {A B : Type u} [Ring A] [Ring B] [HasDerivedCategory.{u, u} A]
  [HasDerivedCategory.{u, u} B]
  {X X' : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] [AddCommGroup X'] [DGAddCommGroup X'] [Module A X'] [Module Bᵐᵒᵖ X']
  [DGBimodule A B X']

attribute [local instance] dgDerivedTensorSignCommShift

/-- The coefficient map at the regular module is invertible iff `f` is a quasi-isomorphism. -/
theorem isIso_dgDerivedTensorCoeffMap_app_regular_iff (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) :
    IsIso ((dgDerivedTensorCoeffMap A B f hf).app (Q.obj (DGModuleCat.of B B))) ↔
      f.IsQuasiIso := by
  have hP : IsKProjective.{u} B (DGModuleCat.of B B) := isKProjective_self.{u} (A := B)
  have h₁ := dgDerivedTensorObjIso_coeff_naturality A B f hf hP
  have h₂ : Q.map ((tensorCoeffNat f hf).app (DGModuleCat.of B B)) =
      Q.map (tensorRegularDGIso X).hom ≫ Q.map (DGModuleCat.ofHom f) ≫
        Q.map (tensorRegularDGIso X').inv := by
    rw [← Q.map_comp, ← Q.map_comp, ← Category.assoc, ← tensorCoeffNat_app_regular,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Iff.trans ?_ (isIso_Q_map_iff (DGModuleCat.ofHom f))
  have e : (dgDerivedTensorCoeffMap A B f hf).app (Q.obj (DGModuleCat.of B B)) =
      ((dgDerivedTensorObjIso (X := X) hP).hom ≫ Q.map (tensorRegularDGIso X).hom) ≫
        Q.map (DGModuleCat.ofHom f) ≫
          (Q.map (tensorRegularDGIso X').inv ≫ (dgDerivedTensorObjIso (X := X') hP).inv) := by
    rw [← cancel_mono (dgDerivedTensorObjIso (X := X') hP).hom, h₁, h₂]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [e]
  constructor
  · intro h
    have : IsIso (Q.map (DGModuleCat.ofHom f) ≫
        (Q.map (tensorRegularDGIso X').inv ≫ (dgDerivedTensorObjIso (X := X') hP).inv)) :=
      IsIso.of_isIso_comp_left
        ((dgDerivedTensorObjIso (X := X) hP).hom ≫ Q.map (tensorRegularDGIso X).hom) _
    exact IsIso.of_isIso_comp_right _
      (Q.map (tensorRegularDGIso X').inv ≫ (dgDerivedTensorObjIso (X := X') hP).inv)
  · intro h
    infer_instance

/-- **Derived tensor products with quasi-isomorphic bimodules are isomorphic**: for a
quasi-isomorphism of dg bimodules `f : X → X'`, the induced `X ⊗ᴸ_B - ⟶ X' ⊗ᴸ_B -` is an
isomorphism. The regular module `B` compactly generates `D(B)`. -/
theorem isIso_dgDerivedTensorCoeffMap (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) (hq : f.IsQuasiIso) :
    IsIso (dgDerivedTensorCoeffMap A B f hf) := by
  have := dgDerivedTensorCoeffMap_commShift A B f hf
  have := dgDerivedTensor_isTriangulated_sign A B X
  have := dgDerivedTensor_isTriangulated_sign A B X'
  have := preservesColimitsOfShape_discrete_nat.{u} (dgDerivedTensor.{u} A B X)
  have := preservesColimitsOfShape_discrete_nat.{u} (dgDerivedTensor.{u} A B X')
  exact isIso_of_compactlyGenerates _ (compactlyGenerates (A := B))
    fun _ => (isIso_dgDerivedTensorCoeffMap_app_regular_iff f hf).mpr hq

/-- **`X ⊗ᴸ_B - ≅ X' ⊗ᴸ_B -` for a quasi-isomorphism of dg bimodules** `f : X → X'`. -/
def dgDerivedTensorIsoOfQuasiIso (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) (hq : f.IsQuasiIso) :
    dgDerivedTensor.{u} A B X ≅ dgDerivedTensor.{u} A B X' :=
  have := isIso_dgDerivedTensorCoeffMap f hf hq
  asIso (dgDerivedTensorCoeffMap A B f hf)

@[simp]
theorem dgDerivedTensorIsoOfQuasiIso_hom (f : X →ᵈᵍ[A] X')
    (hf : ∀ (b : B) (m : X), f (op b • m) = op b • f m) (hq : f.IsQuasiIso) :
    (dgDerivedTensorIsoOfQuasiIso f hf hq).hom = dgDerivedTensorCoeffMap A B f hf := rfl

end QuasiIso

end Categorification
