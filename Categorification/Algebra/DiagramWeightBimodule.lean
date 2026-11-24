/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ProjectiveKProjective
import Categorification.Algebra.DiagramBigrading
import DG.Category.Derived.Tensor
import DG.Bigraded.Derived

/-!
# Diagram coefficients as graded dg bimodules

A homogeneous coefficient bimodule defines a dg bimodule between the weight
categories of its two rings. Its derived tensor uses a K-projective
representative of the input. The construction supplies the derived tensor
for coefficients as in Webster, arXiv:1309.3796v2, Definitions 6.6 and 7.4.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v
variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M]

variable (G : ℤ → AddSubgroup M)
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))

local notation "P" => fun (X : WeightCategory A) (Y : WeightCategory B) => InDegreeZero (G (WeightCategory.as X - WeightCategory.as Y))

private def weightLeft {X X' : WeightCategory A} {Y : WeightCategory B} :
    (X ⟶ X') →+ P X Y →+ P X' Y where
  toFun f :=
    { toFun := fun x => ⟨f.val • x.val, by
        have h := hl f.property x.property
        rwa [show (X'.as - X.as) + (X.as - Y.as) = X'.as - Y.as by omega] at h⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun x y => Subtype.ext (smul_add _ _ _) }
  map_zero' := AddMonoidHom.ext fun x => Subtype.ext (zero_smul _ _)
  map_add' f g := AddMonoidHom.ext fun x => Subtype.ext (add_smul _ _ _)

private def weightRight {X : WeightCategory A} {Y Y' : WeightCategory B} :
    (Y ⟶ Y') →+ P X Y' →+ P X Y where
  toFun g :=
    { toFun := fun x => ⟨op g.val • x.val, by
        have h := hr g.property x.property
        rwa [show (X.as - Y'.as) + (Y'.as - Y.as) = X.as - Y.as by omega] at h⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun x y => Subtype.ext (smul_add _ _ _) }
  map_zero' := AddMonoidHom.ext fun x => Subtype.ext (zero_smul _ _)
  map_add' f g := AddMonoidHom.ext fun x => Subtype.ext (by
    change op (f.val + g.val) • x.val = op f.val • x.val + op g.val • x.val
    exact (congrArg (fun b : Bᵐᵒᵖ => b • (show M from x.val)) (op_add f.val g.val)).trans
      (add_smul _ _ _))

/-- The bimodule between the two weight categories has component
at weights X and Y equal to the X−Y part of the coefficient. -/
def diagramWeightBimodule : CatBimodule (WeightCategory A) (WeightCategory B) where
  obj := P
  lact := weightLeft G hl
  ract := weightRight G hr
  lact_mem' {X X' Y i j f x} hf hx := by
    rcases (InDegreeZero.ring_mem_grading_iff (R := A)).mp (WeightCategory.mem_grading_iff.mp hf)
      with rfl | hf
    · rcases (InDegreeZero.mem_grading_iff (M := G (WeightCategory.as X - WeightCategory.as Y))).mp hx with rfl | rfl
      · exact InDegreeZero.mem_grading_zero _
      · rw [map_zero]
        exact zero_mem _
    · have h : f = 0 := WeightCategory.hom_ext hf
      rw [h, map_zero, AddMonoidHom.zero_apply]
      exact zero_mem _
  lact_id' _ _ x := Subtype.ext (one_smul A x.val)
  lact_comp' f g x := Subtype.ext (mul_smul g.val f.val x.val)
  d_lact' {X X' Y i f} _ x := by
    have hf : d f = 0 := WeightCategory.hom_ext (InDegreeZero.ring_d_apply f.val)
    simp only [InDegreeZero.d_apply, hf, map_zero, AddMonoidHom.zero_apply, smul_zero, zero_add]
  ract_mem' {X Y Y' i j g x} hg hx := by
    rcases (InDegreeZero.ring_mem_grading_iff (R := B)).mp (WeightCategory.mem_grading_iff.mp hg)
      with rfl | hg
    · rcases (InDegreeZero.mem_grading_iff (M := G (X.as-Y'.as))).mp hx with rfl | rfl
      · exact InDegreeZero.mem_grading_zero _
      · rw [map_zero]
        exact zero_mem _
    · have h : g = 0 := WeightCategory.hom_ext hg
      rw [h, map_zero, AddMonoidHom.zero_apply]
      exact zero_mem _
  ract_id' _ _ x := Subtype.ext (one_smul Bᵐᵒᵖ x.val)
  ract_comp' f g x := Subtype.ext (mul_smul (op f.val) (op g.val) x.val)
  d_ract' {X Y Y' j x} _ g := by
    have hg : d g = 0 := WeightCategory.hom_ext (InDegreeZero.ring_d_apply g.val)
    simp only [InDegreeZero.d_apply, hg, map_zero, AddMonoidHom.zero_apply, smul_zero, zero_add]
  lact_ract' f g x := Subtype.ext (smul_comm f.val (op g.val) x.val)

section Derived

variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

local notation "D" => diagramWeightBimodule G hl hr

/-- Tensoring with the graded coefficient preserves chain homotopies. -/
def diagramWeightTensorHomotopy :
    CatModule.HomotopyCategory.{u} (WeightCategory B) ⥤
      CatModule.HomotopyCategory.{u} (WeightCategory A) :=
  CategoryTheory.Quotient.lift _ ((D).tensorFunctor ⋙ CatModule.HomotopyCategory.quotient _)
    (fun _ _ _ _ h => CatModule.HomotopyCategory.eq_of_homotopy _ _
      ((D).homotopic_tensorMap h).some)

/-- Derived tensor with a graded diagram coefficient, computed on
K-projective representatives of the input. -/
def diagramWeightDerivedTensor :
    CatModule.DerivedCategory.{v,u} (WeightCategory B) ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory A) :=
  (CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)).inverse ⋙
    (CatModule.HomotopyCategory.subcategoryKProjective (WeightCategory B)).ι ⋙
    diagramWeightTensorHomotopy G hl hr ⋙ CatModule.DerivedCategory.Qh

/-- The derived tensor evaluates on a K-projective input by tensoring its dg model. -/
def diagramWeightDerivedTensorObjIso {X : CatModule.{u} (WeightCategory B)}
    (hX : CatModule.IsKProjective X) :
    (diagramWeightDerivedTensor G hl hr).obj (CatModule.DerivedCategory.Q.obj X) ≅
      CatModule.DerivedCategory.Q.obj ((D).tensorFunctor.obj X) := by
  let H := CatModule.HomotopyCategory.subcategoryKProjective.{u} (WeightCategory B)
  let p : H.FullSubcategory := ⟨(CatModule.HomotopyCategory.quotient _).obj X,
    (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff X).mpr hX⟩
  let E := CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory B)
  exact (diagramWeightTensorHomotopy G hl hr ⋙ CatModule.DerivedCategory.Qh).mapIso
    (H.ι.mapIso (E.unitIso.symm.app p))

/-- A resolution whose augmentation stays a quasi-isomorphism after tensoring
computes the derived tensor by the ordinary tensor of the input. -/
def diagramWeightDerivedTensorObjIsoOfResolution
    {K N : CatModule.{u} (WeightCategory B)} (f : K ⟶ N)
    (hK : CatModule.IsKProjective K) (hf : CatModule.IsQuasiIso f)
    (hTensor : CatModule.IsQuasiIso ((D).tensorMap f)) :
    (diagramWeightDerivedTensor G hl hr).obj (CatModule.DerivedCategory.Q.obj N) ≅
      CatModule.DerivedCategory.Q.obj ((D).tensorFunctor.obj N) := by
  let Q₁ : CatModule.{u} (WeightCategory A) ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory A) := CatModule.DerivedCategory.Q
  let Q₂ : CatModule.{u} (WeightCategory B) ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory B) := CatModule.DerivedCategory.Q
  letI : IsIso (Q₂.map f) := (CatModule.DerivedCategory.isIso_Q_map_iff f).mpr hf
  let t := Q₁.map ((D).tensorMap f)
  have ht : IsIso t :=
    (CatModule.DerivedCategory.isIso_Q_map_iff ((D).tensorMap f)).mpr hTensor
  exact ((diagramWeightDerivedTensor G hl hr).mapIso (asIso (Q₂.map f))).symm ≪≫
    diagramWeightDerivedTensorObjIso G hl hr hK ≪≫
    @asIso _ _ _ _ t ht

/-- Derived Hom with the graded coefficient, when its left modules are K-projective. -/
def diagramWeightDerivedHom (h : ∀ Y, CatModule.IsKProjective ((D).left Y)) :
    CatModule.DerivedCategory.{v,u} (WeightCategory A) ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory B) :=
  CatModule.DerivedCategory.rhom D h

end Derived

end Categorification
