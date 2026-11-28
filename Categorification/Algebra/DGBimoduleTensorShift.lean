/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Module.TensorProductOverProd
import DG.Module.Regrade
import DG.Homotopy.BimoduleTensor
import DG.Homotopy.Comparison
import DG.Homotopy.ConeCochain

set_option backward.isDefEq.respectTransparency false

/-!
# Tensoring with a dg bimodule commutes with shifts and cones

Let `A`, `B` be rings concentrated in degree `0` and `X` a dg `(A, B)`-bimodule, in arbitrary
degrees. The balanced tensor product `X ⊗_B -` commutes with the cochain shift by the Koszul sign
rule:
`X ⊗_B N⟦j⟧ ≅ (X ⊗_B N)⟦j⟧`, `x ⊗ n ↦ (-1)^{j |x|} (x ⊗ n)`
(`Categorification.tensorSignShiftEquiv`), and with mapping cones,
`X ⊗_B Cone(g) ≅ Cone(X ⊗_B g)` (`Categorification.tensorSignConeEquiv`). For `X` concentrated
in degree `0` the sign is trivial, and these are dg-lean's `DG.tensorShiftEquiv`,
`DG.tensorConeEquiv`.

This is the standard sign convention for tensor products of complexes. It is used to show
that `X ⊗ᴸ_B -` is a triangulated functor for a complex of bimodules `X`, as needed for the
bimodule form of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 7.22.

The results are generic dg algebra (they belong with dg-lean's
`DG/Homotopy/OrdinaryBimoduleTensorTriangulated.lean`).
-/

open CategoryTheory
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

open DG DG.TensorProductOver

universe u

variable {B : Type u} [Ring B] {M N : Type u} [AddCommGroup M] [DGAddCommGroup M]
  [Module Bᵐᵒᵖ M] [DGRightModule B M] [AddCommGroup N] [DGAddCommGroup N] [Module B N]
  [DGModule B N]

omit [DGAddCommGroup N] [DGModule B N] in
theorem shift_unmk_smul_of_degreeZero (j : ℤ) (b : B) (x : Shift j N) :
    Shift.unmk j (b • x) = b • Shift.unmk j x := by
  rw [Shift.unmk_smul (i := 0) (DegreeZero.mem_grading_iff.mpr (Or.inl rfl))]
  rw [mul_zero, koszulSign_zero, one_smul]

omit [DGAddCommGroup N] [Module B N] [DGModule B N] in
theorem signTwist_op_smul_of_degreeZero (j : ℤ) (b : B) (m : M) :
    signTwist M j (MulOpposite.op b • m) = MulOpposite.op b • signTwist M j m := by
  rw [signTwist_op_smul_of_mem j (DegreeZero.mem_grading_iff.mpr (Or.inl rfl)) m, mul_zero,
    koszulSign_zero, one_smul]

omit [Module Bᵐᵒᵖ M] [DGRightModule B M] [AddCommGroup N] [DGAddCommGroup N] [Module B N]
  [DGModule B N] in
theorem signTwist_zero_apply (m : M) : signTwist M 0 m = m := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_homogeneous m => rw [signTwist_of_mem 0 m.2, zero_mul, koszulSign_zero, one_smul]
  | h_add m m' hm hm' => rw [map_add, hm, hm']

omit [Module Bᵐᵒᵖ M] [DGRightModule B M] [AddCommGroup N] [DGAddCommGroup N] [Module B N]
  [DGModule B N] in
theorem signTwist_add_apply (a b : ℤ) (m : M) :
    signTwist M (a + b) m = signTwist M b (signTwist M a m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_homogeneous m =>
    rw [signTwist_of_mem _ m.2, signTwist_of_mem a m.2, map_units_zsmul, signTwist_of_mem b m.2,
      smul_smul, add_mul, koszulSign_add]
  | h_add m m' hm hm' => rw [map_add, hm, hm', map_add, map_add]

omit [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] in
theorem signTwist_mem_grading (j : ℤ) {k : ℤ} {m : M} (hm : m ∈ grading k) :
    signTwist M j m ∈ grading k :=
  signTwist_mem j hm

/-- The balanced bi-additive map `(x, n) ↦ (-1)^{j |x|} (x ⊗ n)`, into the shift. -/
def tensorSignShiftBil (j : ℤ) : M →+ Shift j N →+ Shift j (TensorProductOver B M N) :=
  (((TensorProductOver.tmulAddHom B M N).comp (signTwist M j)).compr₂
    (Shift.mk j (M := TensorProductOver B M N)).toAddMonoidHom).compl₂
    (Shift.unmk j (M := N)).toAddMonoidHom

omit [DGAddCommGroup N] [DGModule B N] in
theorem tensorSignShiftBil_balanced (j : ℤ) (b : B) (m : M) (x : Shift j N) :
    tensorSignShiftBil (B := B) j (MulOpposite.op b • m) x =
      tensorSignShiftBil (B := B) j m (b • x) := by
  change Shift.mk j (tmul B (signTwist M j (MulOpposite.op b • m)) (Shift.unmk j x)) =
    Shift.mk j (tmul B (signTwist M j m) (Shift.unmk j (b • x)))
  rw [signTwist_op_smul_of_degreeZero, shift_unmk_smul_of_degreeZero, op_smul_tmul]

/-- The comparison `X ⊗_B N⟦j⟧ → (X ⊗_B N)⟦j⟧`, `x ⊗ n ↦ (-1)^{j |x|} (x ⊗ n)`. -/
def tensorSignShiftTo (j : ℤ) :
    TensorProductOver B M (Shift j N) →+ Shift j (TensorProductOver B M N) :=
  lift (tensorSignShiftBil (B := B) j) (tensorSignShiftBil_balanced j)

omit [DGAddCommGroup N] [DGModule B N] in
@[simp]
theorem tensorSignShiftTo_tmul (j : ℤ) (m : M) (x : Shift j N) :
    tensorSignShiftTo j (tmul B m x) =
      Shift.mk j (tmul B (signTwist M j m) (Shift.unmk j x)) := rfl

/-- The inverse comparison, `x ⊗ n ↦ (-1)^{j |x|} (x ⊗ n)`. -/
def tensorSignShiftFrom (j : ℤ) :
    Shift j (TensorProductOver B M N) →+ TensorProductOver B M (Shift j N) :=
  (lift (((TensorProductOver.tmulAddHom B M (Shift j N)).comp (signTwist M j)).compl₂
      (Shift.mk j (M := N)).toAddMonoidHom) (fun b m x => by
    change tmul B (signTwist M j (MulOpposite.op b • m)) (Shift.mk j x) =
      tmul B (signTwist M j m) (Shift.mk j (b • x))
    rw [signTwist_op_smul_of_degreeZero, op_smul_tmul]
    congr 1
    apply (Shift.unmk j).injective
    rw [shift_unmk_smul_of_degreeZero, Shift.unmk_mk, Shift.unmk_mk])).comp
    (Shift.unmk j).toAddMonoidHom

omit [DGAddCommGroup N] [DGModule B N] in
theorem tensorSignShiftFrom_mk_tmul (j : ℤ) (m : M) (n : N) :
    tensorSignShiftFrom j (Shift.mk j (tmul B m n)) =
      tmul B (signTwist M j m) (Shift.mk j n) := rfl

/-- Tensoring with a dg bimodule commutes with the shift on underlying groups. -/
def tensorSignShiftAddEquiv (j : ℤ) :
    TensorProductOver B M (Shift j N) ≃+ Shift j (TensorProductOver B M N) := by
  refine { tensorSignShiftTo j with
    invFun := tensorSignShiftFrom j
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    change tensorSignShiftFrom j (tensorSignShiftTo j x) = x
    have h : (tensorSignShiftFrom j).comp (tensorSignShiftTo j) =
        AddMonoidHom.id (TensorProductOver B M (Shift j N)) := by
      apply addHom_ext
      intro m x
      change tmul B (signTwist M j (signTwist M j m)) (Shift.mk j (Shift.unmk j x)) = tmul B m x
      rw [signTwist_signTwist, Shift.mk_unmk]
    exact DFunLike.congr_fun h x
  · have h : ((tensorSignShiftTo (B := B) (M := M) (N := N) j).comp
          (tensorSignShiftFrom j)).comp (Shift.mk j).toAddMonoidHom =
        (Shift.mk j).toAddMonoidHom := by
      apply addHom_ext
      intro m x
      change Shift.mk j (tmul B (signTwist M j (signTwist M j m)) (Shift.unmk j (Shift.mk j x))) =
        Shift.mk j (tmul B m x)
      rw [signTwist_signTwist, Shift.unmk_mk]
    intro y
    obtain ⟨x, rfl⟩ := (Shift.mk j).surjective y
    change tensorSignShiftTo j (tensorSignShiftFrom j (Shift.mk j x)) = Shift.mk j x
    exact DFunLike.congr_fun h x

omit [Module Bᵐᵒᵖ M] [DGRightModule B M] [AddCommGroup N] [DGAddCommGroup N] [Module B N]
  [DGModule B N] in
theorem signTwist_smul_of_degreeZero {A : Type u} [Ring A] [Module A M] [DGModule A M] (j : ℤ)
    (a : A) (m : M) :
    signTwist M j (a • m) = a • signTwist M j m := by
  rw [signTwist_smul_of_mem j (DegreeZero.mem_grading_iff.mpr (Or.inl rfl)) m, mul_zero,
    koszulSign_zero, one_smul]

end Categorification

namespace Categorification

open DG DG.TensorProductOver

universe u

variable {B : Type u} [Ring B] {M N : Type u} [AddCommGroup M] [DGAddCommGroup M]
  [Module Bᵐᵒᵖ M] [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  {A : Type u} [Ring A] [Module A M] [DGBimodule A B M]

/-- **Tensoring with a dg bimodule commutes with the shift**:
`X ⊗_B N⟦j⟧ ≅ (X ⊗_B N)⟦j⟧`, `x ⊗ n ↦ (-1)^{j |x|} (x ⊗ n)`. -/
def tensorSignShiftEquiv (j : ℤ) :
    TensorProductOver B M (Shift j N) ≃ᵈᵍ[A] Shift j (TensorProductOver B M N) where
  __ := tensorSignShiftAddEquiv j
  map_smul' a y := by
    change tensorSignShiftTo j (a • y) = a • tensorSignShiftTo j y
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m x =>
      apply (Shift.unmk j).injective
      rw [TensorProductOver.smul_tmul, tensorSignShiftTo_tmul, tensorSignShiftTo_tmul,
        shift_unmk_smul_of_degreeZero, Shift.unmk_mk, Shift.unmk_mk,
        TensorProductOver.smul_tmul, signTwist_smul_of_degreeZero]
  map_mem' := by
    intro k y hy
    change tensorSignShiftTo j y ∈ grading k
    refine lift_mem _ (tensorSignShiftBil_balanced (B := B) j) ?_ hy
    intro i l m x hm hx
    change Shift.mk j (tmul B (signTwist M j m) (Shift.unmk j x)) ∈ grading (i + l)
    rw [Shift.mem_grading_iff, add_assoc]
    exact TensorProductOver.tmul_mem_grading (signTwist_mem j hm) (Shift.unmk_mem_grading hx)
  map_d' y := by
    change tensorSignShiftTo j (d y) = d (tensorSignShiftTo j y)
    refine lift_d _ (tensorSignShiftBil_balanced (B := B) j) ?_ y
    intro i m hm x
    change d (Shift.mk j (tmul B (signTwist M j m) (Shift.unmk j x))) =
      Shift.mk j (tmul B (signTwist M j (d m)) (Shift.unmk j x)) +
        koszulSign i • Shift.mk j (tmul B (signTwist M j m) (Shift.unmk j (d x)))
    rw [Shift.d_mk, TensorProductOver.d_tmul_of_mem (signTwist_mem j hm), d_signTwist,
      Shift.unmk_d, units_smul_tmul, tmul_units_smul, smul_add, smul_smul, Int.units_mul_self,
      one_smul, Shift.mk_add, smul_comm (koszulSign j) (koszulSign i), Shift.mk_units_smul]

@[simp]
theorem tensorSignShiftEquiv_tmul (j : ℤ) (m : M) (x : Shift j N) :
    tensorSignShiftEquiv (A := A) j (tmul B m x) =
      Shift.mk j (tmul B (signTwist M j m) (Shift.unmk j x)) := rfl


section Cone

variable {N' : Type u} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']
  (g : N →ᵈᵍ[B] N')

/-- Comparison of the cone carriers under tensoring by a dg bimodule. -/
def tensorSignConeAddEquiv :
    TensorProductOver B M (Cone g) ≃+ Cone (DGModuleHom.lTensor A M g) :=
  prodRightAddEquiv.trans (AddEquiv.prodCongr (tensorSignShiftAddEquiv 1) (AddEquiv.refl _))

theorem tensorSignConeAddEquiv_tmul (m : M) (x : Cone g) :
    tensorSignConeAddEquiv (A := A) g (tmul B m x) =
      ((tensorSignShiftAddEquiv 1 (tmul B m x.1), tmul B m x.2) :
        Cone (DGModuleHom.lTensor A M g)) := rfl

/-- **Tensoring with a dg bimodule commutes with mapping cones**:
`X ⊗_B Cone(g) ≅ Cone(X ⊗_B g)`, with the Koszul sign of `tensorSignShiftEquiv` on `N⟦1⟧`. -/
def tensorSignConeEquiv :
    TensorProductOver B M (Cone g) ≃ᵈᵍ[A] Cone (DGModuleHom.lTensor A M g) where
  __ := tensorSignConeAddEquiv g
  map_smul' a y := by
    change tensorSignConeAddEquiv g (a • y) = a • tensorSignConeAddEquiv g y
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m x =>
      rw [TensorProductOver.smul_tmul, tensorSignConeAddEquiv_tmul, tensorSignConeAddEquiv_tmul]
      refine Prod.ext ?_ ?_
      · change tensorSignShiftEquiv (A := A) 1 (tmul B (a • m) x.1) =
          a • tensorSignShiftEquiv (A := A) 1 (tmul B m x.1)
        rw [← TensorProductOver.smul_tmul, map_smul]
      · exact (TensorProductOver.smul_tmul a m x.2).symm
  map_mem' {k y} hy := by
    change tensorSignConeAddEquiv g y ∈ grading k
    obtain ⟨x, hx, rfl⟩ := hy
    have h := DG.map_mem_grading_of_tmul
      ((tensorSignConeAddEquiv (A := A) g).toAddMonoidHom.comp (TensorProductOver.mk B _ _)) 0
      (fun {i j m p} hm hp => by
        change tensorSignConeAddEquiv (A := A) g (tmul B m p) ∈ grading (i + j + 0)
        rw [add_zero, tensorSignConeAddEquiv_tmul]
        refine Cone.mem_grading_iff.mpr ⟨?_, ?_⟩
        · exact (tensorSignShiftEquiv (A := A) 1).map_mem
            (TensorProductOver.tmul_mem_grading hm (Cone.mem_grading_iff.mp hp).1)
        · exact TensorProductOver.tmul_mem_grading hm (Cone.mem_grading_iff.mp hp).2) hx
    rwa [add_zero] at h
  map_d' y := by
    change tensorSignConeAddEquiv g (d y) = d (tensorSignConeAddEquiv g y)
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m p =>
      induction m using DG.induction_on with
      | h_zero => simp
      | h_add m m' hm hm' =>
        rw [add_tmul, d_add, map_add, map_add, hm, hm', map_add]
      | @h_homogeneous i m =>
        have hm : (m : M) ∈ grading i := m.2
        rw [TensorProductOver.d_tmul_of_mem hm, map_add, Units.smul_def, map_zsmul,
          ← Units.smul_def, tensorSignConeAddEquiv_tmul, tensorSignConeAddEquiv_tmul,
          tensorSignConeAddEquiv_tmul]
        refine Prod.ext ?_ ?_
        · change tensorSignShiftEquiv (A := A) 1 (tmul B (d (m : M)) p.1) +
              koszulSign i • tensorSignShiftEquiv (A := A) 1 (tmul B (m : M) (d p.1)) =
            d (tensorSignShiftEquiv (A := A) 1 (tmul B (m : M) p.1))
          rw [← DGModuleEquiv.map_d, TensorProductOver.d_tmul_of_mem hm, map_add]
          simp only [Units.smul_def, map_zsmul]
        · change tmul B (d (m : M)) p.2 +
              koszulSign i • tmul B (m : M) (g (Shift.unmk 1 p.1) + d p.2) =
            DGModuleHom.lTensor A M g
              (Shift.unmk 1 (tensorSignShiftEquiv (A := A) 1 (tmul B (m : M) p.1))) +
              d (tmul B (m : M) p.2)
          rw [tensorSignShiftEquiv_tmul, Shift.unmk_mk, signTwist_of_mem 1 hm, one_mul,
            units_smul_tmul, TensorProductOver.d_tmul_of_mem hm, tmul_add]
          simp only [Units.smul_def, map_zsmul, DGModuleHom.lTensor_tmul, smul_add]
          abel

end Cone


section Functor

open CategoryTheory.Pretriangulated

variable (A B M)

/-- The shift comparison `X ⊗_B N⟦n⟧ ≅ (X ⊗_B N)⟦n⟧` in `DGModuleCat A`. -/
def tensorSignShiftIso (n : ℤ) (X : DGModuleCat.{u} B) :
    (shiftFunctor (DGModuleCat.{u} B) n ⋙ DGModuleCat.tensorFunctor A M).obj X ≅
      (DGModuleCat.tensorFunctor A M ⋙ shiftFunctor (DGModuleCat.{u} A) n).obj X :=
  DGModuleCat.isoOfDGModuleEquiv
    (M := DGModuleCat.of A (TensorProductOver B M (Shift n X)))
    (N := DGModuleCat.of A (Shift n (TensorProductOver B M X)))
    (tensorSignShiftEquiv (A := A) n)

/-- **`X ⊗_B -` commutes with the shift** on dg modules, for a dg bimodule `X` in arbitrary
degrees, by the Koszul sign rule (`tensorSignShiftEquiv`). For `X` in degree `0` this agrees
with dg-lean's `DG.ordinaryTensorFunctor_commShift`; it is not an instance, to avoid a second
shift structure on that functor. -/
@[instance_reducible]
def tensorFunctorSignCommShift : (DGModuleCat.tensorFunctor A M (B := B)).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (tensorSignShiftIso B M A n) fun {X Y} h =>
    DGModuleCat.tensor_hom_ext (A := A) (M := M)
      (N := DGModuleCat.of B (Shift n X)) fun _ _ => rfl
  commShiftIso_zero := by
    ext X : 3
    rw [Functor.CommShift.isoZero_hom_app]
    exact DGModuleCat.tensor_hom_ext (A := A) (M := M)
      (N := DGModuleCat.of B (Shift 0 X)) fun m x =>
        (congrArg (fun m' : M => (Shift.mk 0 (tmul B m' (Shift.unmk 0 (show Shift 0 X from x))) :
          Shift 0 (TensorProductOver B M X))) (signTwist_zero_apply m) : _)
  commShiftIso_add a b := by
    ext X : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    exact DGModuleCat.tensor_hom_ext (A := A) (M := M)
      (N := DGModuleCat.of B (Shift (a + b) X)) fun m x =>
        (congrArg (fun m' : M =>
          (Shift.mk (a + b) (tmul B m' (Shift.unmk (a + b) (show Shift (a + b) X from x))) :
            Shift (a + b) (TensorProductOver B M X)))
          (show signTwist M (a + b) m = signTwist M a (signTwist M b m) by
            rw [add_comm a b]; exact signTwist_add_apply b a m) : _)

attribute [local instance] tensorFunctorSignCommShift

/-- `X ⊗_B -` sends the standard cone triangle to the standard cone triangle. -/
def tensorSignMapTriangleIso {X Y : DGModuleCat.{u} B} (f : X ⟶ Y) :
    (DGModuleCat.tensorFunctor A M (B := B)).mapTriangle.obj (Cone.triangle f) ≅
      Cone.triangle ((DGModuleCat.tensorFunctor A M (B := B)).map f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (DGModuleCat.isoOfDGModuleEquiv (tensorSignConeEquiv f.hom))
    (by simp)
    (by
      apply DGModuleCat.tensor_hom_ext
      intro m y
      refine Prod.ext ?_ rfl
      exact (show Shift.mk 1 (tmul B (signTwist M 1 m) (Shift.unmk 1 (0 : Shift 1 X))) = 0 by
        simp : _))
    (by
      apply DGModuleCat.tensor_hom_ext
      intro m x
      exact (show Shift.mk 1 (tmul B (signTwist M 1 m) (-(Shift.unmk 1 x.1))) =
          -Shift.mk 1 (tmul B (signTwist M 1 m) (Shift.unmk 1 x.1)) by
        rw [tmul_neg, Shift.mk_neg] : _))

theorem quotient_tensorFunctor_map_eq (X Y : DGModuleCat.{u} B) (f g : X ⟶ Y)
    (h : DGModuleCat.homotopic B f g) :
    (DGModuleCat.tensorFunctor A M (B := B) ⋙ DG.HomotopyCategory.quotient A).map f =
      (DGModuleCat.tensorFunctor A M (B := B) ⋙ DG.HomotopyCategory.quotient A).map g :=
  (DG.HomotopyCategory.quotient_map_eq_iff _ _).mpr
    (DG.HomotopyCategory.tensorFunctor_homotopic A M f g h)

/-- `X ⊗_B -` on homotopy categories commutes with the shift, for a dg bimodule `X` in arbitrary
degrees. -/
@[instance_reducible]
def homotopyTensorFunctorSignCommShift :
    (DG.HomotopyCategory.tensorFunctor A M (B := B)).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift
    (DGModuleCat.tensorFunctor A M (B := B) ⋙ DG.HomotopyCategory.quotient A)
    (DGModuleCat.homotopic.{u} B) ℤ (quotient_tensorFunctor_map_eq B M A)

attribute [local instance] homotopyTensorFunctorSignCommShift

theorem homotopyTensorFunctorQuotientIso_signCommShift :
    NatTrans.CommShift (DG.HomotopyCategory.tensorFunctorQuotientIso A M (B := B)).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility
    (DGModuleCat.tensorFunctor A M (B := B) ⋙ DG.HomotopyCategory.quotient A)
    (DGModuleCat.homotopic.{u} B) ℤ (quotient_tensorFunctor_map_eq B M A)

/-- **`X ⊗_B -` on homotopy categories is triangulated**, for a dg bimodule `X` in arbitrary
degrees, with the shift structure `homotopyTensorFunctorSignCommShift`. -/
theorem homotopyTensorFunctor_isTriangulated_sign :
    (DG.HomotopyCategory.tensorFunctor A M (B := B)).IsTriangulated where
  map_distinguished := by
    have := homotopyTensorFunctorQuotientIso_signCommShift B M A
    rintro T ⟨X, Y, f, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(DG.HomotopyCategory.tensorFunctor A M (B := B)).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
      (Functor.mapTriangleIso
        (DG.HomotopyCategory.tensorFunctorQuotientIso A M)).app _ ≪≫
      (Functor.mapTriangleCompIso _ _).app _ ≪≫
      (DG.HomotopyCategory.quotient A).mapTriangle.mapIso (tensorSignMapTriangleIso B M A f)⟩⟩

end Functor

end Categorification
