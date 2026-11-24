/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorRegular
import Categorification.WeightedKLR.Rigidity.DerivedCupHom

/-!
# The derived Hom cup on the ground field

Webster, arXiv:1309.3796v2, Definition 7.4. For the regular scalar input
the dg Hom complex is concentrated in degree zero, where its opposite
algebra action is precomposition on the ordinary dual. Thus the ungraded
derived Hom and dual-tensor cup models agree on that input.
-/

noncomputable section

namespace Categorification.InDegreeZero

open CategoryTheory DG
open scoped DG.DegreeZero

universe u
variable (k : Type u) [Field k] (L V : Type u)
  [AddCommGroup L] [Module k L] [AddCommGroup V] [Module k V]

local notation "L₀" => DGModuleCat.toCatModuleObj (DGModuleCat.of k (InDegreeZero L))
local notation "V₀" => DGModuleCat.toCatModuleObj (DGModuleCat.of k (InDegreeZero V))
local notation "star" => SingleObj.star k

private def cochainLinear (z : CatModule.Cochain L₀ V₀ 0) : L →ₗ[k] V where
  toFun x := z.app star x
  map_add' x y := map_add (z.app star) x y
  map_smul' c x := by
    have hc : (c : star ⟶ star) ∈ grading 0 :=
      (InDegreeZero.ring_mem_grading_iff (R := k)).mpr (Or.inl rfl)
    have h := z.map_smul (Y := star) hc (show (L₀).obj star from x)
    rw [mul_zero, koszulSign_zero, one_smul] at h
    exact h

private def linearCochain (f : L →ₗ[k] V) : CatModule.Cochain L₀ V₀ 0 where
  app _ := f.toAddMonoidHom
  map_mem' {X n x} hx := by
    change (show InDegreeZero V from f (show L from x)) ∈ grading (M := InDegreeZero V) (n + 0)
    rw [add_zero]
    have hx' := (InDegreeZero.mem_grading_iff (M := L)).mp hx
    apply (InDegreeZero.mem_grading_iff (M := V)).mpr
    rcases hx' with hn | hx'
    · exact Or.inl hn
    · right
      change (show L from x) = 0 at hx'
      change f (show L from x) = 0
      rw [hx', map_zero]
  map_smul' {X Y i c} hc x := by
    rw [zero_mul, koszulSign_zero, one_smul]
    exact map_smul f (show k from c) (show L from x)

private def scalarHomDegreeZeroEquiv : CatModule.Cochain L₀ V₀ 0 ≃+ (L →ₗ[k] V) where
  toFun := cochainLinear k L V
  invFun := linearCochain k L V
  left_inv z := by
    ext X x
    cases X
    rfl
  right_inv f := rfl
  map_add' x y := rfl

private theorem scalarHom_subsingleton_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (CatModule.Cochain L₀ V₀ n) := by
  refine ⟨fun a b => ?_⟩
  have hz (z : CatModule.Cochain L₀ V₀ n) (X : SingleObj k) (x : (L₀).obj X) :
      z.app X x = 0 := by
    have hx : x ∈ grading 0 := (InDegreeZero.mem_grading_iff (M := L)).mpr (Or.inl rfl)
    have hz := z.map_mem hx
    rw [zero_add] at hz
    exact ((InDegreeZero.mem_grading_iff (M := V)).mp hz).resolve_left hn
  exact CatModule.Cochain.ext fun X x => (hz a X x).trans (hz b X x).symm

open scoped DirectSum

private def extractDegreeZero (n : ℤ) : CatModule.Cochain L₀ V₀ n →+ (L →ₗ[k] V) :=
  if h : n = 0 then h.symm ▸ (scalarHomDegreeZeroEquiv k L V).toAddMonoidHom else 0

/-- The Hom complex of two degree-zero scalar modules is supported in degree zero,
where it is the ordinary scalar Hom module. -/
private def scalarHomComplexEquiv : CatModule.HOM L₀ V₀ ≃+ (L →ₗ[k] V) := by
  let f := DirectSum.toAddMonoid (extractDegreeZero k L V)
  let g := (DirectSum.of (fun n => CatModule.Cochain L₀ V₀ n) 0).comp
    (scalarHomDegreeZeroEquiv k L V).symm.toAddMonoidHom
  refine { toFun := f, invFun := g, map_add' := map_add f, left_inv := ?_, right_inv := ?_ }
  · intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of n z =>
      by_cases hn : n = 0
      · subst n
        simp [f, g, extractDegreeZero]
      · have := scalarHom_subsingleton_of_ne_zero k L V hn
        rw [Subsingleton.elim z 0, map_zero, map_zero, map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro z
    simp [f, g, extractDegreeZero]

private theorem scalarHomComplexEquiv_symm_apply (f : L →ₗ[k] V) :
    (scalarHomComplexEquiv k L V).symm f =
      DirectSum.of (fun n => CatModule.Cochain L₀ V₀ n) 0 (linearCochain k L V f) :=
  rfl

end Categorification.InDegreeZero

namespace Categorification.Stendhal.Coevaluation

open CategoryTheory DG MulOpposite InDegreeZero
open scoped DG.DegreeZero DirectSum

universe u v
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  (L : Type u) [AddCommGroup L] [Module k L] [Module A L] [IsScalarTower k A L]

private instance : SMulCommClass A k L where
  smul_comm a c x := smul_algebra_smul_comm c a x

local notation "M₀" => InDegreeZero (OpBimodule A L)
local notation "B₀" => DGBimodule.catBimodule k Aᵐᵒᵖ M₀
local notation "X₀" => DGModuleCat.of k (InDegreeZero k)
local notation "N₀" => DGModuleCat.toCatModuleObj X₀
local notation "W" => CatBimodule.homObj B₀ N₀
local notation "S" => SingleObj.star Aᵐᵒᵖ
local notation "C" => InDegreeZero (CupCoefficient k L)

set_option backward.isDefEq.respectTransparency false in
/-- The dg Hom cup coefficient on the scalar regular module is the
ordinary dual, with its opposite algebra action. -/
private def scalarHomCupCoefficientIso : DGModuleCat.of Aᵐᵒᵖ C ≅ CatModule.toDGModuleCatObj W := by
  let e : C ≃+ (W).obj S := (scalarHomComplexEquiv k (OpBimodule A L) k).symm
  have equiv_apply (f : C) : e f = DirectSum.of _ 0
      (linearCochain k (OpBimodule A L) k
        (show OpBimodule A L →ₗ[k] k from f)) :=
    scalarHomComplexEquiv_symm_apply k (OpBimodule A L) k _
  have smul_eq (a : Aᵐᵒᵖ) (f : C) : e (a • f) = (W).act (X := S) (Y := S) a (e f) := by
    have ha : (a : S ⟶ S) ∈ grading 0 :=
      (InDegreeZero.ring_mem_grading_iff (R := Aᵐᵒᵖ)).mpr (Or.inl rfl)
    let c := linearCochain k (OpBimodule A L) k (show OpBimodule A L →ₗ[k] k from f)
    let r := (B₀).ractCochain (Y := S) (Y' := S) a ha
    have hact := CatBimodule.homAct_of_mem (B := B₀) (N := N₀) (Y := S) (Y' := S) ha
      (DirectSum.of _ 0 c)
    symm
    calc
      (W).act (X := S) (Y := S) a (e f) =
          CatModule.HOM.precompCochain r (DirectSum.of _ 0 c) := hact
      _ = DirectSum.of _ (0 + 0) (c.comp r rfl) := by
        simpa only [zero_mul, koszulSign_zero, one_smul] using
          CatModule.HOM.precompCochain_of r 0 c
      _ = e (a • f) := by
        exact CatModule.HOM.of_congr (by simp) (fun star x => by
          have hx : x ∈ grading 0 :=
            (InDegreeZero.mem_grading_iff (M := OpBimodule A L)).mpr (Or.inl rfl)
          rw [CatModule.Cochain.comp_apply]
          change c.app star (((B₀).ractCochain (Y := S) (Y' := S) a ha).app star x) = _
          rw [CatBimodule.ractCochain_app_of_mem (B := B₀) (Y := S) (Y' := S) ha hx,
            zero_mul, koszulSign_zero, one_smul, DGBimodule.catBimodule_ract]
          rfl)
  have mem (n : ℤ) (f : C) (hf : f ∈ grading n) : e f ∈ grading n := by
    rcases (InDegreeZero.mem_grading_iff (M := CupCoefficient k L)).mp hf with rfl | h
    · rw [equiv_apply, CatModule.HOM.grading_eq]
      exact of_mem_summand _ _
    · rw [h, map_zero]
      exact zero_mem _
  have diff (f : C) : e (d f) = d (e f) := by
    rw [InDegreeZero.d_apply, map_zero]
    have h := scalarHom_subsingleton_of_ne_zero k (OpBimodule A L) k (n := 1) (by decide)
    have hd : d (e f) ∈ grading (1 : ℤ) := by
      simpa only [zero_add] using d_mem (mem 0 f (InDegreeZero.mem_grading_zero f))
    change d (e f) ∈ DG.summand (fun n => CatModule.Cochain _ _ n) 1 at hd
    obtain ⟨z, hz⟩ := hd
    rw [h.elim z 0, map_zero] at hz
    exact hz
  exact DGModuleCat.isoOfDGModuleEquiv {
    toLinearEquiv := { e with map_smul' := smul_eq }
    map_mem' := fun hf => mem _ _ hf
    map_d' := diff }

variable [CatModule.HasDerivedCategory.{v,u} (SingleObj k)]
  [CatModule.HasDerivedCategory.{v,u} (SingleObj Aᵐᵒᵖ)]
  [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ]

/-- The unshifted derived Hom cup on the scalar regular object is the dual coefficient. -/
def cupRHomRegularIso :
    (cupRHomFunctor k A L).obj (DG.DerivedCategory.Q.obj X₀) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of Aᵐᵒᵖ C) :=
  cupRHomObjIso k A L X₀ ≪≫
    (CatModule.DerivedCategory.QhCompToDGDerivedCategoryIso Aᵐᵒᵖ).app
      ((CatModule.HomotopyCategory.quotient (SingleObj Aᵐᵒᵖ)).obj W) ≪≫
    DG.DerivedCategory.Qh.mapIso
      ((CatModule.HomotopyCategory.toDGHomotopyCategoryFactors Aᵐᵒᵖ).app W) ≪≫
    DG.DerivedCategory.Q.mapIso (scalarHomCupCoefficientIso k A L).symm

/-- The derived Hom and dual-tensor cup models agree on the regular scalar input. -/
def cupRHomTensorRegularIso :
    (cupRHomFunctor k A L).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of k k)) ≅
      (cupFunctor k A L).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of k k)) :=
  cupRHomRegularIso k A L ≪≫
    (derivedTensorRegularCoefficientIso Aᵐᵒᵖ k (CupCoefficient k L)).symm


end Categorification.Stendhal.Coevaluation
