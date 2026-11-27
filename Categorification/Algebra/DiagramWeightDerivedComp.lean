/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorComp
import Categorification.Algebra.DiagramWeightTensorDerived
import Categorification.Algebra.CatModuleResolutionAdjunction
import Categorification.Algebra.DiagramWeightEquivalence
import Categorification.Algebra.CompactGeneratorIsIso

set_option backward.isDefEq.respectTransparency false

/-!
# Composites of derived tensors with diagram coefficients

A balanced homogeneous product `β : M × N → P` of three diagram coefficients induces a
comparison of the derived tensors over the weight categories,
`D_M ⊗ᴸ (D_N ⊗ᴸ -) ⟶ D_P ⊗ᴸ -`: the resolution map of `D_N ⊗ p(-)` followed by the product
`D_M ⊗ (D_N ⊗ -) ⟶ D_P ⊗ -`. This is the comparison behind the composites of the graded
braiding functors (Webster, arXiv:1309.3796v3, Lemma 6.12).
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe w'' w' v' u' u

private theorem commShift_of_whiskerLeft_obj_surjective
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (H : C ⥤ D) [H.CommShift ℤ] {F G : D ⥤ E}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift (Functor.whiskerLeft H τ) ℤ]
    (hH : Function.Surjective H.obj) : NatTrans.CommShift τ ℤ where
  shift_comm n := by
    ext Y
    obtain ⟨X,rfl⟩ := hH Y
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

namespace CatModuleResolution

variable {C₀ : Type u'} [Category.{v'} C₀] [Preadditive C₀] [∀ X Y : C₀, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C₀] [CatModule.HasDerivedCategory.{w'', max u' v' w'} C₀]

/-- A morphism between K-projective objects of the homotopy category which becomes invertible in
the derived category is invertible. -/
theorem isIso_of_isIso_Qh_map {Y Y' : CatModule.HomotopyCategory.{max u' v' w'} C₀}
    (hY : CatModule.HomotopyCategory.subcategoryKProjective C₀ Y)
    (hY' : CatModule.HomotopyCategory.subcategoryKProjective C₀ Y') (f : Y ⟶ Y')
    [IsIso (CatModule.DerivedCategory.Qh.map f)] : IsIso f := by
  have b : ∀ {T : CatModule.HomotopyCategory.{max u' v' w'} C₀}
      (_ : CatModule.HomotopyCategory.subcategoryKProjective C₀ T)
      (Z : CatModule.HomotopyCategory.{max u' v' w'} C₀),
      Function.Bijective (CatModule.DerivedCategory.Qh.map : (T ⟶ Z) → _) :=
    fun hT Z => ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated hT
      CatModule.DerivedCategory.Qh Z
  obtain ⟨g, hg⟩ := (b hY' Y).2 (inv (CatModule.DerivedCategory.Qh.map f))
  refine ⟨g, (b hY Y).1 ?_, (b hY' Y').1 ?_⟩ <;> simp [hg]

/-- The resolution map of a K-projective object is invertible. -/
theorem isIso_resolutionAdjunction_counit_app {Y : CatModule.HomotopyCategory.{max u' v' w'} C₀}
    (hY : CatModule.HomotopyCategory.subcategoryKProjective C₀ Y) :
    IsIso ((resolutionAdjunction.{w'', w'} C₀).counit.app Y) :=
  isIso_of_isIso_Qh_map
    ((CatModule.DerivedCategory.kProjectiveEquivalence.{w'', max u' v' w'} C₀).inverse.obj _).property hY _

/-- A functor inverts the resolution map of `Y` if it inverts that of an isomorphic `Y'`. -/
theorem isIso_map_resolutionAdjunction_counit_app_of_iso {D : Type*} [Category D]
    (F : CatModule.HomotopyCategory.{max u' v' w'} C₀ ⥤ D) {Y Y' : CatModule.HomotopyCategory.{max u' v' w'} C₀}
    (e : Y ≅ Y') (h : IsIso (F.map ((resolutionAdjunction.{w'', w'} C₀).counit.app Y'))) :
    IsIso (F.map ((resolutionAdjunction.{w'', w'} C₀).counit.app Y)) := by
  have hn := (resolutionAdjunction.{w'', w'} C₀).counit.naturality e.hom
  have : (resolutionAdjunction.{w'', w'} C₀).counit.app Y =
      (CatModule.DerivedCategory.Qh ⋙ resolutionFunctor.{w'', w'} C₀).map e.hom ≫
        (resolutionAdjunction.{w'', w'} C₀).counit.app Y' ≫ e.inv := by
    rw [← Category.assoc, hn, Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, F.map_comp, F.map_comp]
  infer_instance

end CatModuleResolution

variable {A B C M N P : Type u} [Ring A] [Ring B] [Ring C]
  [InternalGrading A] [InternalGrading B] [InternalGrading C]
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  [Module A P] [Module Cᵐᵒᵖ P] [SMulCommClass A Cᵐᵒᵖ P]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N) (L : ℤ → AddSubgroup P)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  (hPL : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ L j → a • x ∈ L (i + j))
  (hPR : ∀ {i j : ℤ} {c : C} {x : P}, c ∈ wgrading i → x ∈ L j → op c • x ∈ L (j + i))
  (β : M →+ N →+ P)
  (hw : ∀ {i j : ℤ} {x : M} {y : N}, x ∈ G i → y ∈ H j → β x y ∈ L (i + j))
  (hb : ∀ (b : B) (x : M) (y : N), β (op b • x) y = β x (b • y))
  (hβL : ∀ (a : A) (x : M) (y : N), β (a • x) y = a • β x y)
  (hβR : ∀ (c : C) (x : M) (y : N), β x (op c • y) = op c • β x y)

set_option hygiene false in
local notation "D₁" => diagramWeightBimodule G hgL hgR
set_option hygiene false in
local notation "D₂" => diagramWeightBimodule H hhL hhR
set_option hygiene false in
local notation "D₃" => diagramWeightBimodule L hPL hPR
set_option hygiene false in
local notation "μ" => diagramWeightTensorCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR
set_option hygiene false in
local notation "qA" => CatModule.HomotopyCategory.quotient.{u} (WeightCategory A)
set_option hygiene false in
local notation "qB" => CatModule.HomotopyCategory.quotient.{u} (WeightCategory B)
set_option hygiene false in
local notation "qC" => CatModule.HomotopyCategory.quotient.{u} (WeightCategory C)

/-- On a representable module the comparison is the coend product, up to the identifications
`D ⊗ C(Z, -) ≅ D(-, Z)`. -/
theorem diagramWeightTensorCompNatTrans_app_representable (Z : WeightCategory C) :
    (μ).app (CatModule.representable Z) ≫ (diagramWeightTensorRepresentableIso L hPL hPR Z).hom =
      (D₁).tensorMap (diagramWeightTensorRepresentableIso H hhL hhR Z).hom ≫
        diagramWeightCoendProductHom G H L hgL hgR hhL hhR β hw hb Z hPL hPR hβL := by
  apply diagramWeightTensorComp_hom_ext
  intro X Y x Z' y f
  have h₁ := diagramWeightTensorCompHom_app_tmul G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR
    (CatModule.representable Z) X Y x Z' y f
  have h₂ := CatBimodule.tensorMap_tmul (D₁) (diagramWeightTensorRepresentableIso H hhL hhR Z).hom
    X Y x (CatTensorProduct.tmul (N := (D₂).right Y) (M := CatModule.representable Z) Z' y f)
  refine (congrArg ((diagramWeightTensorRepresentableIso L hPL hPR Z).hom.app X) h₁).trans
    (Eq.trans ?_ (congrArg ((diagramWeightCoendProductHom G H L hgL hgR hhL hhR β hw hb Z hPL hPR
      hβL).app X) h₂).symm)
  apply Subtype.ext
  change (CatTensorProduct.rid ((D₃).right X) Z
      (CatTensorProduct.tmul Z' (diagramWeightMul G H L hgL hgR hhL hhR hPL hPR β hw x y) f)).val =
    (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z
      (CatTensorProduct.tmul Y x (CatTensorProduct.rid ((D₂).right Y) Z
        (CatTensorProduct.tmul Z' y f)))).val
  rw [CatTensorProduct.rid_tmul, CatTensorProduct.rid_tmul, diagramWeightCoendProduct_tmul,
    CatBimodule.right_ract, CatBimodule.right_ract]
  exact (hβR f.val x.val y.val).symm

/-- With bijective coend products, the comparison is invertible on a representable module. -/
theorem isIso_diagramWeightTensorCompNatTrans_app_representable (Z : WeightCategory C)
    (hbij : ∀ X, Function.Bijective (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z)) :
    IsIso ((μ).app (CatModule.representable Z)) := by
  have hp : IsIso (diagramWeightCoendProductHom G H L hgL hgR hhL hhR β hw hb Z hPL hPR hβL) :=
    CatModule.isIso_of_bijective _ hbij
  have ht : IsIso ((D₁).tensorMap (diagramWeightTensorRepresentableIso H hhL hhR Z).hom) :=
    inferInstanceAs (IsIso ((CatBimodule.tensorFunctor.{u, u} (D₁)).map
      (diagramWeightTensorRepresentableIso H hhL hhR Z).hom))
  have h := diagramWeightTensorCompNatTrans_app_representable G H L hgL hgR hhL hhR hPL hPR β hw
    hb hβL hβR Z
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

section Homotopy

variable [CatModule.HasDerivedCategory.{u,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory C)]

set_option hygiene false in
local notation "Th₁" => diagramWeightTensorHomotopy G hgL hgR
set_option hygiene false in
local notation "Th₂" => diagramWeightTensorHomotopy H hhL hhR
set_option hygiene false in
local notation "Th₃" => diagramWeightTensorHomotopy L hPL hPR

/-- The comparison on dg modules, written through the quotient to the homotopy category. -/
def diagramWeightTensorCompQuotientNatTrans :
    qC ⋙ (Th₂ ⋙ Th₁) ⟶ qC ⋙ Th₃ :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (diagramWeightTensorHomotopyFactors H hhL hhR).hom Th₁ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (CatBimodule.tensorFunctor.{u, u} (D₂))
      (diagramWeightTensorHomotopyFactors G hgL hgR).hom ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight μ qA ≫
    (diagramWeightTensorHomotopyFactors L hPL hPR).inv

/-- **The comparison of homotopy-category tensors** `D_M ⊗ (D_N ⊗ -) ⟶ D_P ⊗ -`. -/
def diagramWeightTensorHomotopyCompNatTrans : Th₂ ⋙ Th₁ ⟶ Th₃ :=
  CategoryTheory.Quotient.natTransLift _
    (diagramWeightTensorCompQuotientNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR)

instance diagramWeightTensorHomotopyCompNatTrans_commShift :
    NatTrans.CommShift
      (diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR) ℤ := by
  have he : Functor.whiskerLeft qC
      (diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR) =
      diagramWeightTensorCompQuotientNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR :=
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft qC
      (diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR))
      ℤ := by
    rw [he]
    unfold diagramWeightTensorCompQuotientNatTrans
    infer_instance
  exact commShift_of_whiskerLeft_obj_surjective qC _ (fun ⟨X⟩ => ⟨X, rfl⟩)

end Homotopy

section Derived

variable [CatModule.HasDerivedCategory.{u,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory C)]

set_option hygiene false in
local notation "Th₁" => diagramWeightTensorHomotopy G hgL hgR
set_option hygiene false in
local notation "Th₂" => diagramWeightTensorHomotopy H hhL hhR
set_option hygiene false in
local notation "Th₃" => diagramWeightTensorHomotopy L hPL hPR
set_option hygiene false in
local notation "resB" => CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory B)
set_option hygiene false in
local notation "resC" => CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory C)
set_option hygiene false in
local notation "QhA" => (CatModule.DerivedCategory.Qh :
  CatModule.HomotopyCategory.{u} (WeightCategory A) ⥤ _)
set_option hygiene false in
local notation "QhB" => (CatModule.DerivedCategory.Qh :
  CatModule.HomotopyCategory.{u} (WeightCategory B) ⥤ _)

/-- The composite `D_M ⊗ᴸ (D_N ⊗ᴸ -)`, written as `D_M ⊗ p(D_N ⊗ p(-))`. -/
abbrev diagramWeightDerivedCompSource :
    CatModule.DerivedCategory.{u,u} (WeightCategory C) ⥤
      CatModule.DerivedCategory.{u,u} (WeightCategory A) :=
  (resC ⋙ Th₂) ⋙ (QhB ⋙ resB) ⋙ (Th₁ ⋙ QhA)

/-- The functor `D_M ⊗ (D_N ⊗ p(-))`. -/
abbrev diagramWeightDerivedCompMiddle :
    CatModule.DerivedCategory.{u,u} (WeightCategory C) ⥤
      CatModule.DerivedCategory.{u,u} (WeightCategory A) :=
  (resC ⋙ Th₂) ⋙ 𝟭 _ ⋙ (Th₁ ⋙ QhA)

/-- **The comparison** `D_M ⊗ᴸ (D_N ⊗ᴸ -) ⟶ D_P ⊗ᴸ -`: the resolution map of `D_N ⊗ p(-)`
followed by the product `D_M ⊗ (D_N ⊗ -) ⟶ D_P ⊗ -`. -/
def diagramWeightDerivedCompNatTrans :
    diagramWeightDerivedCompSource G H hgL hgR hhL hhR ⟶ resC ⋙ (Th₃ ⋙ QhA) :=
  (Functor.whiskerLeft (resC ⋙ Th₂)
      (Functor.whiskerRight (CatModuleResolution.resolutionAdjunction.{u, u}
        (WeightCategory B)).counit (Th₁ ⋙ QhA)) :
      diagramWeightDerivedCompSource G H hgL hgR hhL hhR ⟶
        diagramWeightDerivedCompMiddle G H hgL hgR hhL hhR) ≫
    Functor.whiskerLeft (resC ⋙ Th₂) (Functor.leftUnitor (Th₁ ⋙ QhA)).hom ≫
    (Functor.associator resC Th₂ (Th₁ ⋙ QhA)).hom ≫
    Functor.whiskerLeft resC (Functor.associator Th₂ Th₁ QhA).inv ≫
    Functor.whiskerLeft resC (Functor.whiskerRight
      (diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR) QhA)

instance diagramWeightDerivedCompNatTrans_commShift :
    NatTrans.CommShift
      (diagramWeightDerivedCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR) ℤ := by
  unfold diagramWeightDerivedCompNatTrans
  have h₁ : NatTrans.CommShift (CatModuleResolution.resolutionAdjunction.{u, u}
      (WeightCategory B)).counit ℤ := inferInstance
  have h₂ : NatTrans.CommShift (Functor.whiskerRight (CatModuleResolution.resolutionAdjunction.{u, u}
      (WeightCategory B)).counit (Th₁ ⋙ QhA)) ℤ := inferInstance
  have h₃ : NatTrans.CommShift (Functor.whiskerRight
      (diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR)
      QhA) ℤ := inferInstance
  have h₄ : NatTrans.CommShift (Functor.whiskerLeft (resC ⋙ Th₂)
      (Functor.whiskerRight (CatModuleResolution.resolutionAdjunction.{u, u}
      (WeightCategory B)).counit (Th₁ ⋙ QhA))) ℤ := inferInstance
  have h₅ : NatTrans.CommShift (Functor.whiskerLeft resC (Functor.whiskerRight
      (diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR)
      QhA)) ℤ := inferInstance
  infer_instance

instance diagramWeightDerivedCompSource_isTriangulated :
    (diagramWeightDerivedCompSource G H hgL hgR hhL hhR).IsTriangulated := by
  have : (resC ⋙ Th₂).IsTriangulated := inferInstance
  have : (QhB ⋙ resB).IsTriangulated := inferInstance
  have : (Th₁ ⋙ QhA).IsTriangulated := inferInstance
  infer_instance

section Coproducts

variable [DirectSum.Decomposition G] [DirectSum.Decomposition H] [DirectSum.Decomposition L]
  [DG.HasDerivedCategory.{u,u} A] [DG.HasDerivedCategory.{u,u} B]
  [DG.HasDerivedCategory.{u,u} C]

instance diagramWeightDerivedCompSource_preservesCoproducts (J : Type u) :
    Limits.PreservesColimitsOfShape (Discrete J)
      (diagramWeightDerivedCompSource G H hgL hgR hhL hhR) := by
  have := preservesColimitsOfShape_diagramWeightDerivedTensor.{u, u} G hgL hgR J
  have := preservesColimitsOfShape_diagramWeightDerivedTensor.{u, u} H hhL hhR J
  exact inferInstanceAs (Limits.PreservesColimitsOfShape (Discrete J)
    (diagramWeightDerivedTensor.{u, u} H hhL hhR ⋙ diagramWeightDerivedTensor.{u, u} G hgL hgR))

end Coproducts

end Derived
section Generators

variable [CatModule.HasDerivedCategory.{u,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory C)]

set_option hygiene false in
local notation "Th₁" => diagramWeightTensorHomotopy G hgL hgR
set_option hygiene false in
local notation "Th₂" => diagramWeightTensorHomotopy H hhL hhR
set_option hygiene false in
local notation "QhA" => (CatModule.DerivedCategory.Qh :
  CatModule.HomotopyCategory.{u} (WeightCategory A) ⥤ _)
set_option hygiene false in
local notation "εB" => (CatModuleResolution.resolutionAdjunction.{u, u} (WeightCategory B)).counit
set_option hygiene false in
local notation "εC" => (CatModuleResolution.resolutionAdjunction.{u, u} (WeightCategory C)).counit
set_option hygiene false in
local notation "μ̄" =>
  diagramWeightTensorHomotopyCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR

/-- **The comparison is invertible on the representable generators** when the coend products
are bijective and `D_M ⊗ᴸ D_N(-, Z) ≅ D_M ⊗ D_N(-, Z)` (the vanishing of the higher `Tor`). -/
theorem isIso_diagramWeightDerivedCompNatTrans_app_representableW (Z : WeightCategory C)
    (hbij : ∀ X, Function.Bijective (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z))
    (hv : IsIso ((Th₁ ⋙ QhA).map ((εB).app ((qB).obj ((D₂).left Z))))) :
    IsIso ((diagramWeightDerivedCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR).app
      (CatModule.DerivedCategory.Q.obj (CatModule.representableW.{u} (WeightCategory C) Z))) := by
  let P := CatModule.representableW.{u} (WeightCategory C) Z
  let e₀ : P ≅ CatModule.representable Z :=
    CatModule.isoMk (fun _ => AddEquiv.ulift) Iff.rfl (fun _ => rfl) (fun _ _ => rfl)
  have hK : CatModule.HomotopyCategory.subcategoryKProjective _ ((qC).obj P) :=
    ObjectProperty.prop_of_iso _ ((qC).mapIso e₀).symm
      ((CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff _).mpr
        (CatModule.isKProjective_representable Z))
  have hε : IsIso ((εC).app ((qC).obj P)) :=
    CatModuleResolution.isIso_resolutionAdjunction_counit_app hK
  have hμ : IsIso ((μ).app P) := (NatTrans.isIso_app_iff_of_iso (μ) e₀).mpr
    (isIso_diagramWeightTensorCompNatTrans_app_representable G H L hgL hgR hhL hhR hPL hPR β hw hb
      hβL hβR Z hbij)
  have h₂ : IsIso ((μ̄).app ((qC).obj P)) := by
    change IsIso ((diagramWeightTensorCompQuotientNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb
      hβL hβR).app P)
    simp only [diagramWeightTensorCompQuotientNatTrans, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.id_comp]
    infer_instance
  have h₂' : IsIso ((μ̄).app ((CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory C)).obj
      (CatModule.DerivedCategory.Q.obj P))) :=
    (NatTrans.isIso_app_iff_of_iso (μ̄) (asIso ((εC).app ((qC).obj P)))).mpr h₂
  have h₁ : IsIso ((Th₁ ⋙ QhA).map ((εB).app ((Th₂).obj
      ((CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory C)).obj
        (CatModule.DerivedCategory.Q.obj P))))) :=
    CatModuleResolution.isIso_map_resolutionAdjunction_counit_app_of_iso (Th₁ ⋙ QhA)
      ((Th₂).mapIso (asIso ((εC).app ((qC).obj P))) ≪≫
        (diagramWeightTensorHomotopyFactors H hhL hhR).app P ≪≫
        (qB).mapIso ((CatBimodule.tensorFunctor.{u, u} (D₂)).mapIso e₀ ≪≫
          diagramWeightTensorRepresentableIso H hhL hhR Z)) hv
  simp only [diagramWeightDerivedCompNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.id _) ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.id _) ?_
  exact Functor.map_isIso _ _

section Coproducts

variable [DirectSum.Decomposition G] [DirectSum.Decomposition H] [DirectSum.Decomposition L]
  [DG.HasDerivedCategory.{u,u} A] [DG.HasDerivedCategory.{u,u} B]
  [DG.HasDerivedCategory.{u,u} C]

set_option hygiene false in
local notation "Th₃" => diagramWeightTensorHomotopy L hPL hPR
set_option hygiene false in
local notation "resC" => CatModuleResolution.resolutionFunctor.{u, u} (WeightCategory C)

/-- **The comparison `D_M ⊗ᴸ (D_N ⊗ᴸ -) ⟶ D_P ⊗ᴸ -` is invertible** when the coend products
`D_M ⊗ D_N(-, Z) ⟶ D_P(-, Z)` are bijective and `D_M ⊗ᴸ D_N(-, Z) ≅ D_M ⊗ D_N(-, Z)`. -/
theorem isIso_diagramWeightDerivedCompNatTrans
    (hbij : ∀ X Z, Function.Bijective
      (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z))
    (hv : ∀ Z : WeightCategory C,
      IsIso ((Th₁ ⋙ QhA).map ((εB).app ((qB).obj ((D₂).left Z))))) :
    IsIso (diagramWeightDerivedCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR) := by
  have : ∀ J : Type u, Limits.PreservesColimitsOfShape (Discrete J) (resC ⋙ (Th₃ ⋙ QhA)) :=
    fun J => preservesColimitsOfShape_diagramWeightDerivedTensor.{u, u} L hPL hPR J
  have : (resC ⋙ (Th₃ ⋙ QhA)).IsTriangulated := inferInstance
  have := Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℕ)))
    (diagramWeightDerivedCompSource G H hgL hgR hhL hhR)
  have := Limits.preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℕ))) (resC ⋙ (Th₃ ⋙ QhA))
  exact isIso_of_compactlyGenerates _
    (CatModule.DerivedCategory.compactlyGenerates.{u, u, 0} (C := WeightCategory C))
    fun Z => isIso_diagramWeightDerivedCompNatTrans_app_representableW G H L hgL hgR hhL hhR
      hPL hPR β hw hb hβL hβR Z (fun X => hbij X Z) (hv Z)

/-- **Composites of graded derived tensors** (the mechanism of Webster, arXiv:1309.3796v3,
Lemma 6.12, for graded coefficients): if the coend products `D_M ⊗ D_N(-, Z) ⟶ D_P(-, Z)` are
bijective and the higher `Tor` of `D_M` against each `D_N(-, Z)` vanish, then
`D_M ⊗ᴸ (D_N ⊗ᴸ -) ≅ D_P ⊗ᴸ -`. -/
def diagramWeightDerivedTensorCompIso
    (hbij : ∀ X Z, Function.Bijective
      (diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb X Z))
    (hv : ∀ Z : WeightCategory C,
      IsIso ((Th₁ ⋙ QhA).map ((εB).app ((qB).obj ((D₂).left Z))))) :
    diagramWeightDerivedTensor.{u, u} H hhL hhR ⋙ diagramWeightDerivedTensor.{u, u} G hgL hgR ≅
      diagramWeightDerivedTensor.{u, u} L hPL hPR :=
  have := isIso_diagramWeightDerivedCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR
    hbij hv
  asIso (diagramWeightDerivedCompNatTrans G H L hgL hgR hhL hhR hPL hPR β hw hb hβL hβR)

end Coproducts

end Generators

end Categorification
