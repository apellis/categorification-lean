/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import Categorification.Algebra.ModuleFiltration
import DG.Category.Abelian
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Loading support for the graded derived tensor

The balancing relation proves the vanishing step of Webster,
arXiv:1309.3796v2, Lemma 6.11 for a supplied K-projective model with
support on loadings annihilating the coefficient.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG DGOpposite MulOpposite
open scoped DG.DegreeZero CatModule

universe u v

variable {A B P : Type u} [Ring A] [Ring B]
  [InternalGrading A] [InternalGrading B] [BigradedDGRing A] [BigradedDGRing B]
  [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hr : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ G j → MulOpposite.op b • x ∈ G (j + i))

local notation "D" => diagramWeightBimodule G hl hr

/-- If a degree of a resolution is generated at each weight by loading images,
and those loadings kill the coefficient at an output weight, the corresponding
degree of the ordinary tensor is zero at that weight. -/
theorem diagramWeightTensor_grading_subsingleton_of_loading_support
    {K : CatModule.{u} (WeightCategory B)} (X : WeightCategory A) (n : ℤ)
    {ι : WeightCategory B → Type*} (e : ∀ Z, ι Z → (Z ⟶ Z))
    (hspan : ∀ Z (m : K.obj Z), m ∈ DG.grading n →
      m ∈ AddSubgroup.closure {x | ∃ i : ι Z, ∃ y : K.obj Z, x = K.act (e Z i) y})
    (hkill : ∀ Z (i : ι Z) (p : (D).obj X Z), (D).ract (e Z i) p = 0) :
    Subsingleton (DG.grading (M := ((D).tensorObj K).obj X) n) := by
  suffices hz : ∀ x : ((D).tensorObj K).obj X, x ∈ DG.grading n → x = 0 from
    ⟨fun x y => Subtype.ext ((hz x x.property).trans (hz y y.property).symm)⟩
  intro x hx
  refine CatTensorProduct.induction_on_mem_grading (P := fun y => y = 0) rfl ?_
    (fun _ _ ha hb => by rw [ha, hb, add_zero])
    (fun _ ha => by rw [ha, neg_zero]) hx
  intro Z i j p m hp hm hij
  have hi : i = 0 ∨ p = 0 := (InDegreeZero.mem_grading_iff (M := G (X.as - Z.as))).mp hp
  rcases hi with rfl | rfl
  · have hj : j = n := by simpa using hij
    subst j
    let t := CatTensorProduct.tmulAddHom ((D).right X) K Z p
    have hle : AddSubgroup.closure {x | ∃ i : ι Z, ∃ y : K.obj Z, x = K.act (e Z i) y} ≤
        t.ker := (AddSubgroup.closure_le _).mpr (by
      rintro _ ⟨s, z, rfl⟩
      change CatTensorProduct.tmul (N := (D).right X) Z p (e Z s • z) = 0
      calc
        _ = CatTensorProduct.tmul Z (((D).right X).ract (e Z s) p) z :=
          (CatTensorProduct.ract_tmul (e Z s) p z).symm
        _ = 0 := by rw [CatBimodule.right_ract, hkill, CatTensorProduct.zero_tmul])
    exact hle (hspan Z m hm)
  · exact CatTensorProduct.zero_tmul _ _

variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

/-- Webster, arXiv:1309.3796v2, Lemma 6.11. Loading support of a given
K-projective model and annihilation on the coefficient imply vanishing at the
specified weight and cohomological degree. -/
theorem diagramWeightDerivedTensor_cohomology_isZero_of_loading_support
    {K M : CatModule.{u} (WeightCategory B)} (q : K ⟶ M)
    (hK : CatModule.IsKProjective K) (hq : CatModule.IsQuasiIso q)
    (X : WeightCategory A) (n : ℤ)
    {ι : WeightCategory B → Type*} (e : ∀ Z, ι Z → (Z ⟶ Z))
    (hspan : ∀ Z (m : K.obj Z), m ∈ DG.grading n →
      m ∈ AddSubgroup.closure {x | ∃ i : ι Z, ∃ y : K.obj Z, x = K.act (e Z i) y})
    (hkill : ∀ Z (i : ι Z) (p : (D).obj X Z), (D).ract (e Z i) p = 0) :
    IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj (CatModule.DerivedCategory.Q.obj M))) := by
  let C := CatModule.DerivedCategory.cohomologyFunctor X n
  let F := diagramWeightDerivedTensor G hl hr
  let Q := CatModule.DerivedCategory.Q (C := WeightCategory B)
  let _ : IsIso (Q.map q) := (CatModule.DerivedCategory.isIso_Q_map_iff q).mpr hq
  let M' := (D).tensorObj K
  refine IsZero.of_iso ?_ (C.mapIso (F.mapIso (asIso (Q.map q)).symm ≪≫
    diagramWeightDerivedTensorObjIso G hl hr hK))
  refine IsZero.of_iso ?_ ((CatModule.DerivedCategory.cohomologyFunctorFactorsh X n).app
    ((CatModule.HomotopyCategory.quotient _).obj M'))
  let H := _root_.HomotopyCategory.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n
  refine IsZero.of_iso ?_ (H.mapIso ((CatModule.HomotopyCategory.evalFactors X).app M'))
  refine IsZero.of_iso ?_
    ((_root_.HomotopyCategory.homologyFunctorFactors AddCommGrpCat (ComplexShape.up ℤ) n).app
      ((CatModule.evalComplex X).obj M'))
  apply ShortComplex.isZero_homology_of_isZero_X₂
  apply AddCommGrpCat.isZero_of_iff_subsingleton.mpr
  exact diagramWeightTensor_grading_subsingleton_of_loading_support G hl hr X n e hspan hkill

/-- In the loading-support criterion, one may test annihilation on the ordinary
filtration layers of the coefficient. Idempotence promotes layerwise annihilation
to annihilation of the coefficient before restricting to any weight. -/
theorem diagramWeightDerivedTensor_cohomology_isZero_of_filtered_loading_support
    {K M : CatModule.{u} (WeightCategory B)} (q : K ⟶ M)
    (hK : CatModule.IsKProjective K) (hq : CatModule.IsQuasiIso q)
    (X : WeightCategory A) (n : ℤ)
    {ι : WeightCategory B → Type*} (e : ∀ Z, ι Z → (Z ⟶ Z))
    (he : ∀ Z (i : ι Z), IsIdempotentElem (MulOpposite.op (e Z i).val))
    (hspan : ∀ Z (m : K.obj Z), m ∈ DG.grading n →
      m ∈ AddSubgroup.closure {x | ∃ i : ι Z, ∃ y : K.obj Z, x = K.act (e Z i) y})
    {η : Type*} {L : η → ModuleCat.{u} Bᵐᵒᵖ} {layers : List η}
    (hF : ModuleFiltration.HasFiltration L layers (ModuleCat.of Bᵐᵒᵖ P))
    (hkill : ∀ Z (i : ι Z) c, c ∈ layers → ∀ z : L c, MulOpposite.op (e Z i).val • z = 0) :
    IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj (CatModule.DerivedCategory.Q.obj M))) :=
  diagramWeightDerivedTensor_cohomology_isZero_of_loading_support G hl hr q hK hq X n e hspan
    (fun Z i p => Subtype.ext (hF.idempotent_smul_eq_zero _ (he Z i) (hkill Z i) p.val))

end Categorification
