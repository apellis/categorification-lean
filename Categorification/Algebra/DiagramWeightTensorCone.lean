/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightTensorShift
import DG.Category.Homotopy.Triangulated

/-!
# Mapping cones of diagram weight tensors

The additive split into the two cone summands preserves the differential
and the dg module action. The comparison identifies the standard triangle
and gives a triangulated functor on homotopy categories.
-/

noncomputable section
namespace Categorification

open CategoryTheory Pretriangulated DG DGOpposite
open scoped CatModule

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (P : CatModule.{w} (DGOpposite C)) {L M : CatModule.{w} C} (f : L ⟶ M)

private abbrev coneFst (X : C) : (CatModule.cone f).obj X →+ (CatModule.shift 1 L).obj X :=
  AddMonoidHom.fst _ _

private abbrev coneSnd (X : C) : (CatModule.cone f).obj X →+ M.obj X :=
  AddMonoidHom.snd _ _

private def tensorConeFstFamily (X : C) :
    P.obj (op X) →+ (CatModule.cone f).obj X →+
      CatTensorProduct P (CatModule.shift 1 L) :=
  (CatTensorProduct.tmulAddHom P (CatModule.shift 1 L) X).compl₂ (coneFst f X)

private def tensorConeSndFamily (X : C) :
    P.obj (op X) →+ (CatModule.cone f).obj X →+ CatTensorProduct P M :=
  (CatTensorProduct.tmulAddHom P M X).compl₂ (coneSnd f X)

private theorem tensorConeFstFamily_balanced : CatTensorProduct.Balanced (tensorConeFstFamily P f) := by
  intro X Y a p m
  exact CatTensorProduct.ract_tmul (N := P) (M := CatModule.shift 1 L) a p (coneFst f X m)

private theorem tensorConeSndFamily_balanced : CatTensorProduct.Balanced (tensorConeSndFamily P f) := by
  intro X Y a p m
  exact CatTensorProduct.ract_tmul (N := P) (M := M) a p (coneSnd f X m)

/-- Before shifting the first component, the cone tensor splits into its two summands as a group. -/
def tensorConeSplitHom : CatTensorProduct P (CatModule.cone f) →+
    CatTensorProduct P (CatModule.shift 1 L) × CatTensorProduct P M :=
  (CatTensorProduct.lift _ (tensorConeFstFamily_balanced P f)).prod
    (CatTensorProduct.lift _ (tensorConeSndFamily_balanced P f))

theorem tensorConeSplitHom_tmul (X : C) (p : P.obj (op X)) (z : (CatModule.cone f).obj X) :
    tensorConeSplitHom P f (CatTensorProduct.tmul X p z) =
      (CatTensorProduct.tmul (N := P) (M := CatModule.shift 1 L) X p (coneFst f X z),
       CatTensorProduct.tmul (N := P) (M := M) X p (coneSnd f X z)) :=
  Prod.ext (CatTensorProduct.lift_tmul _ (tensorConeFstFamily_balanced P f) X p z)
    (CatTensorProduct.lift_tmul _ (tensorConeSndFamily_balanced P f) X p z)

private abbrev coneInl (X : C) : (CatModule.shift 1 L).obj X →+ (CatModule.cone f).obj X :=
  AddMonoidHom.inl _ _

private abbrev coneInr (X : C) : M.obj X →+ (CatModule.cone f).obj X :=
  AddMonoidHom.inr _ _

private def tensorConeInlFamily (X : C) :
    P.obj (op X) →+ (CatModule.shift 1 L).obj X →+ CatTensorProduct P (CatModule.cone f) :=
  (CatTensorProduct.tmulAddHom P (CatModule.cone f) X).compl₂ (coneInl f X)

private def tensorConeInrFamily (X : C) :
    P.obj (op X) →+ M.obj X →+ CatTensorProduct P (CatModule.cone f) :=
  (CatTensorProduct.tmulAddHom P (CatModule.cone f) X).compl₂ (coneInr f X)

private theorem tensorConeInlFamily_balanced : CatTensorProduct.Balanced (tensorConeInlFamily P f) := by
  intro X Y a p m
  have hh := CatTensorProduct.ract_tmul (N := P) (M := CatModule.cone f) a p (coneInl f X m)
  have h : a • coneInl f X m = coneInl f Y (a • m) := Prod.ext rfl (map_zero (M.act a))
  exact hh.trans (congrArg (CatTensorProduct.tmul (N := P) (M := CatModule.cone f) Y p) h)

private theorem tensorConeInrFamily_balanced : CatTensorProduct.Balanced (tensorConeInrFamily P f) := by
  intro X Y a p m
  have hh := CatTensorProduct.ract_tmul (N := P) (M := CatModule.cone f) a p (coneInr f X m)
  have h : a • coneInr f X m = coneInr f Y (a • m) := Prod.ext (map_zero ((CatModule.shift 1 L).act a)) rfl
  exact hh.trans (congrArg (CatTensorProduct.tmul (N := P) (M := CatModule.cone f) Y p) h)

private def tensorConeInlHom := CatTensorProduct.lift _ (tensorConeInlFamily_balanced P f)
private def tensorConeInrHom := CatTensorProduct.lift _ (tensorConeInrFamily_balanced P f)

private theorem tensorConeInlHom_tmul (X : C) (p : P.obj (op X)) (m : (CatModule.shift 1 L).obj X) :
    tensorConeInlHom P f (CatTensorProduct.tmul X p m) =
      CatTensorProduct.tmul (N := P) X p (coneInl f X m) :=
  CatTensorProduct.lift_tmul _ (tensorConeInlFamily_balanced P f) X p m

private theorem tensorConeInrHom_tmul (X : C) (p : P.obj (op X)) (m : M.obj X) :
    tensorConeInrHom P f (CatTensorProduct.tmul X p m) =
      CatTensorProduct.tmul (N := P) X p (coneInr f X m) :=
  CatTensorProduct.lift_tmul _ (tensorConeInrFamily_balanced P f) X p m

/-- Join the two underlying summands of a tensor with a mapping cone. -/
def tensorConeJoinHom : CatTensorProduct P (CatModule.shift 1 L) × CatTensorProduct P M →+
    CatTensorProduct P (CatModule.cone f) :=
  (tensorConeInlHom P f).coprod (tensorConeInrHom P f)

/-- Tensoring the underlying cone separates its two additive summands. -/
def tensorConeSplitAddEquiv : CatTensorProduct P (CatModule.cone f) ≃+
    CatTensorProduct P (CatModule.shift 1 L) × CatTensorProduct P M := by
  let s := tensorConeSplitHom P f
  let j := tensorConeJoinHom P f
  let l := tensorConeInlHom P f
  let r := tensorConeInrHom P f
  have h₁ : s.comp l = AddMonoidHom.inl _ _ := by
    apply CatTensorProduct.addHom_ext
    intro X p x
    change s (l (CatTensorProduct.tmul X p x)) = (CatTensorProduct.tmul X p x, 0)
    rw [tensorConeInlHom_tmul, tensorConeSplitHom_tmul]
    exact Prod.ext rfl (CatTensorProduct.tmul_zero X p)
  have h₂ : s.comp r = AddMonoidHom.inr _ _ := by
    apply CatTensorProduct.addHom_ext
    intro X p x
    change s (r (CatTensorProduct.tmul X p x)) = (0, CatTensorProduct.tmul X p x)
    rw [tensorConeInrHom_tmul, tensorConeSplitHom_tmul]
    exact Prod.ext (CatTensorProduct.tmul_zero X p) rfl
  have hL : j.comp s = AddMonoidHom.id _ := by
    apply CatTensorProduct.addHom_ext
    intro X p z
    change j (s (CatTensorProduct.tmul X p z)) = CatTensorProduct.tmul X p z
    rw [tensorConeSplitHom_tmul]
    change l (CatTensorProduct.tmul X p (coneFst f X z)) +
      r (CatTensorProduct.tmul X p (coneSnd f X z)) = _
    rw [tensorConeInlHom_tmul, tensorConeInrHom_tmul, ← CatTensorProduct.tmul_add]
    exact congrArg (CatTensorProduct.tmul X p) (Prod.ext (add_zero _) (zero_add _))
  have hR (v : CatTensorProduct P (CatModule.shift 1 L) × CatTensorProduct P M) : s (j v) = v := by
    have hl : s (l v.1) = (v.1, 0) := DFunLike.congr_fun h₁ v.1
    have hr : s (r v.2) = (0, v.2) := DFunLike.congr_fun h₂ v.2
    change s (l v.1 + r v.2) = v
    rw [map_add, hl, hr]
    exact Prod.ext (add_zero _) (zero_add _)
  exact
    { toFun := s
      invFun := j
      map_add' := s.map_add
      left_inv := fun x => DFunLike.congr_fun hL x
      right_inv := hR }

section DiagramCone

open scoped DG.DegreeZero

variable {A B T : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup T] [Module A T] [Module Bᵐᵒᵖ T]
  [SMulCommClass A Bᵐᵒᵖ T]
  (G : ℤ → AddSubgroup T)
  (hl : ∀ {i j : ℤ} {a : A} {x : T}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : T},
    b ∈ wgrading i → x ∈ G j → MulOpposite.op b • x ∈ G (j+i))
  {U V : CatModule.{u} (WeightCategory B)} (h : U ⟶ V)

local notation "D" => diagramWeightBimodule G hl hr

private theorem diagramCone_twist_eq {X Y : WeightCategory B} (a : X ⟶ Y) :
    CatModule.twist 1 a = a := by
  have h₀ : a ∈ DG.grading (0 : ℤ) :=
    WeightCategory.mem_grading_iff.mpr (InDegreeZero.ring_mem_grading_zero a.val)
  rw [CatModule.twist_of_mem h₀, mul_zero, koszulSign_zero, one_smul]

/-- The two additive summands of a diagram tensor of a mapping cone. -/
def diagramWeightTensorConeAddEquiv (X : WeightCategory A) :
    CatTensorProduct ((D).right X) (CatModule.cone h) ≃+
      (CatModule.cone ((D).tensorMap h)).obj X :=
  (tensorConeSplitAddEquiv ((D).right X) h).trans
    (AddEquiv.prodCongr (weightTensorShiftAddEquiv 1 ((D).right X) U diagramCone_twist_eq)
      (AddEquiv.refl _))

theorem diagramWeightTensorConeAddEquiv_tmul (X : WeightCategory A) (Y : WeightCategory B)
    (x : (D).obj X Y) (p : (CatModule.cone h).obj Y) :
    diagramWeightTensorConeAddEquiv G hl hr h X (CatTensorProduct.tmul (N := (D).right X) Y x p) =
      (Shift.mk 1 (M := ((D).tensorObj U).obj X)
        (CatTensorProduct.tmul (N := (D).right X) (M := U) Y x (Shift.unmk 1 (M := U.obj Y) p.1)),
        CatTensorProduct.tmul (N := (D).right X) (M := V) Y x p.2) := by
  have e := tensorConeSplitHom_tmul ((D).right X) h Y x p
  exact (congrArg (AddEquiv.prodCongr
    (weightTensorShiftAddEquiv 1 ((D).right X) U diagramCone_twist_eq) (AddEquiv.refl _)) e).trans
      (Prod.ext (weightTensorShiftHom_tmul 1 ((D).right X) U diagramCone_twist_eq Y x p.1) rfl)

private theorem diagramWeightTensorConeAddEquiv_mem (X : WeightCategory A)
    {n : ℤ} {x : CatTensorProduct ((D).right X) (CatModule.cone h)} (hx : x ∈ DG.grading n) :
    diagramWeightTensorConeAddEquiv G hl hr h X x ∈ DG.grading n := by
  let e := diagramWeightTensorConeAddEquiv G hl hr h X
  refine CatTensorProduct.induction_on_mem_grading
    (P := fun x => e x ∈ DG.grading n) ?_ ?_ ?_ ?_ hx
  · rw [map_zero]
    exact zero_mem _
  · intro Y a b z p hz hp hab
    rw [diagramWeightTensorConeAddEquiv_tmul G hl hr h X Y z p]
    obtain ⟨hp₁, hp₂⟩ := (CatModule.cone.mem_grading_iff (f := h)).mp hp
    have hpu : Shift.unmk 1 (M := U.obj Y) p.1 ∈ DG.grading (b+1) :=
      CatModule.shift.unmk_mem_grading (M := U) (n := 1) hp₁
    have h₁ := CatTensorProduct.tmul_mem_grading (N := (D).right X) (M := U) hz hpu
    have h₂ := CatTensorProduct.tmul_mem_grading (N := (D).right X) (M := V) hz hp₂
    have hs := Shift.mk_mem_grading (n := 1) h₁
    rw [← add_assoc, add_sub_cancel_right, hab] at hs
    exact Prod.mem_grading.mpr ⟨hs, hab ▸ h₂⟩
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro x hx
    rw [map_neg]
    exact neg_mem hx

private theorem diagramWeightTensorConeAddEquiv_d (X : WeightCategory A)
    (x : CatTensorProduct ((D).right X) (CatModule.cone h)) :
    diagramWeightTensorConeAddEquiv G hl hr h X (d x) =
      d (diagramWeightTensorConeAddEquiv G hl hr h X x) := by
  induction x using CatTensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
  | tmul Y z p =>
    have hz : z ∈ DG.grading (0 : ℤ) := InDegreeZero.mem_grading_zero _
    have hd : d z = 0 := InDegreeZero.d_apply (G (X.as - Y.as)) z
    have hdp := CatTensorProduct.d_tmul_of_mem (N := (D).right X) (M := CatModule.cone h) Y hz p
    rw [hd, CatTensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul] at hdp
    rw [hdp, diagramWeightTensorConeAddEquiv_tmul G hl hr h X Y z (d p),
      diagramWeightTensorConeAddEquiv_tmul G hl hr h X Y z p]
    let m := Shift.unmk 1 (M := U.obj Y) p.1
    let tm := CatTensorProduct.tmulAddHom ((D).right X) U Y z
    let s := Shift.mk 1 (M := ((D).tensorObj U).obj X)
    have em : d (tm m) = tm (d m) :=
      (CatTensorProduct.d_tmul_of_mem (N := (D).right X) (M := U) Y hz m).trans (by
        rw [hd, CatTensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul]
        rfl)
    apply Prod.ext
    · change s (tm (Shift.unmk 1 (M := U.obj Y) (d p).1)) = d (s (tm m))
      have hg : Shift.unmk 1 (M := U.obj Y) (d p).1 = koszulSign (1 : ℤ) • d m :=
        CatModule.shift.unmk_d p.1
      exact (congrArg (fun m₀ => s (tm m₀)) hg).trans
        ((congrArg s (map_units_zsmul tm (koszulSign (1 : ℤ)) (d m))).trans
          ((congrArg (fun y => s (koszulSign (1 : ℤ) • y)) em.symm).trans (Shift.d_mk (tm m)).symm))
    · let z₀ : CatTensorProduct ((D).right X) V := ((D).tensorMap h).app X (tm m)
      change CatTensorProduct.tmul (N := (D).right X) (M := V) Y z (d p).2 =
        z₀ + d (CatTensorProduct.tmul (N := (D).right X) (M := V) Y z p.2)
      have hp : (d p).2 = h.app Y m + d p.2 := rfl
      have hp₂ := CatTensorProduct.d_tmul_of_mem (N := (D).right X) (M := V) Y hz p.2
      rw [hd, CatTensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul] at hp₂
      exact (congrArg (CatTensorProduct.tmul (N := (D).right X) (M := V) Y z) hp).trans
        ((CatTensorProduct.tmul_add (N := (D).right X) (M := V) Y z (h.app Y m) (d p.2)).trans
          (congrArg₂ (· + ·) (CatBimodule.tensorMap_tmul (D) h X Y z m).symm hp₂.symm))

/-- The value of a diagram tensor on a mapping cone is the cone of the tensor map. -/
def diagramWeightTensorConeDGEquiv (X : WeightCategory A) :
    DGAddEquiv (CatTensorProduct ((D).right X) (CatModule.cone h)) ((CatModule.cone ((D).tensorMap h)).obj X) where
  toAddEquiv := diagramWeightTensorConeAddEquiv G hl hr h X
  map_mem' := fun hx => diagramWeightTensorConeAddEquiv_mem G hl hr h X hx
  map_d' := diagramWeightTensorConeAddEquiv_d G hl hr h X

/-- Tensoring a diagram coefficient sends a mapping cone to the cone of the tensor map. -/
def diagramWeightTensorConeIso :
    (D).tensorObj (CatModule.cone h) ≅ CatModule.cone ((D).tensorMap h) := by
  let e (X : WeightCategory A) := diagramWeightTensorConeDGEquiv G hl hr h X
  refine CatModule.isoMk (fun X => (e X).toAddEquiv) ?_ ?_ ?_
  · intro X n x
    exact ⟨fun hx => (e X).symm_apply_apply x ▸ (e X).symm.map_mem hx,
      fun hx => (e X).map_mem hx⟩
  · intro X x
    exact (e X).map_d x
  · intro X X' a x
    let l := (D).tensorAct (CatModule.cone h) a
    let r := (CatModule.cone ((D).tensorMap h)).act a
    have hm : (e X').toAddEquiv.toAddMonoidHom.comp l =
        r.comp (e X).toAddEquiv.toAddMonoidHom := by
      apply CatTensorProduct.addHom_ext
      intro Y p z
      have ht := CatBimodule.tensorAct_tmul (B := D) (CatModule.cone h) a Y p z
      refine (congrArg (e X') ht).trans ?_
      change diagramWeightTensorConeAddEquiv G hl hr h X'
          (CatTensorProduct.tmul (N := (D).right X') Y ((D).lact a p) z) =
        r (diagramWeightTensorConeAddEquiv G hl hr h X (CatTensorProduct.tmul (N := (D).right X) Y p z))
      rw [diagramWeightTensorConeAddEquiv_tmul G hl hr h X' Y ((D).lact a p) z,
        diagramWeightTensorConeAddEquiv_tmul G hl hr h X Y p z]
      apply Prod.ext
      · let tm := CatTensorProduct.tmul (N := (D).right X) (M := U) Y p
          (Shift.unmk 1 (M := U.obj Y) z.1)
        have ht' := CatBimodule.tensorAct_tmul (B := D) U a Y p (Shift.unmk 1 (M := U.obj Y) z.1)
        have htw := diagramCone_twist_eq a
        change _ = Shift.mk 1 (M := ((D).tensorObj U).obj X') ((D).tensorAct U
          (CatModule.twist 1 a) tm)
        refine (congrArg (Shift.mk 1 (M := ((D).tensorObj U).obj X')) ht'.symm).trans ?_
        exact congrArg (fun b => Shift.mk 1 (M := ((D).tensorObj U).obj X') ((D).tensorAct U b tm)) htw.symm
      · exact (CatBimodule.tensorAct_tmul (B := D) V a Y p z.2).symm
    exact DFunLike.congr_fun hm x

private theorem diagramWeightTensorConeIso_hom_tmul (X : WeightCategory A) (Y : WeightCategory B)
    (x : (D).obj X Y) (p : (CatModule.cone h).obj Y) :
    (diagramWeightTensorConeIso G hl hr h).hom.app X (CatTensorProduct.tmul (N := (D).right X) Y x p) =
      (Shift.mk 1 (M := ((D).tensorObj U).obj X)
        (CatTensorProduct.tmul (N := (D).right X) (M := U) Y x (Shift.unmk 1 (M := U.obj Y) p.1)),
        CatTensorProduct.tmul (N := (D).right X) (M := V) Y x p.2) :=
  diagramWeightTensorConeAddEquiv_tmul G hl hr h X Y x p

theorem diagramWeightTensorConeIso_hom_inr :
    (D).tensorMap (CatModule.cone.inr h) ≫ (diagramWeightTensorConeIso G hl hr h).hom =
      CatModule.cone.inr ((D).tensorMap h) := by
  apply CatModule.Hom.ext
  intro X x
  let l := ((D).tensorMap (CatModule.cone.inr h)).app X
  let e := (diagramWeightTensorConeIso G hl hr h).hom.app X
  let b := (CatModule.cone.inr ((D).tensorMap h)).app X
  have he : e.comp l = b := by
    apply CatTensorProduct.addHom_ext
    intro Y z y
    have hz := CatBimodule.tensorMap_tmul (D) (CatModule.cone.inr h) X Y z y
    refine (congrArg e hz).trans ?_
    refine (diagramWeightTensorConeIso_hom_tmul G hl hr h X Y z ((CatModule.cone.inr h).app Y y)).trans ?_
    apply Prod.ext
    · change Shift.mk 1 (M := ((D).tensorObj U).obj X)
        (CatTensorProduct.tmul (N := (D).right X) (M := U) Y z (Shift.unmk 1 (M := U.obj Y) 0)) = 0
      rw [map_zero, CatTensorProduct.tmul_zero]
      exact map_zero (Shift.mk 1 (M := ((D).tensorObj U).obj X))
    · rfl
  exact DFunLike.congr_fun he x

theorem diagramWeightTensorConeIso_hom_fstHom :
    (D).tensorMap (CatModule.cone.fstHom h) ≫
      (diagramWeightTensorShiftNatIso G hl hr 1).hom.app U =
        (diagramWeightTensorConeIso G hl hr h).hom ≫ CatModule.cone.fstHom ((D).tensorMap h) := by
  apply CatModule.Hom.ext
  intro X x
  let l := ((D).tensorMap (CatModule.cone.fstHom h)).app X
  let e := (diagramWeightTensorConeIso G hl hr h).hom.app X
  let b := (CatModule.cone.fstHom ((D).tensorMap h)).app X
  let s := ((diagramWeightTensorShiftNatIso G hl hr 1).hom.app U).app X
  have he : s.comp l = b.comp e := by
    apply CatTensorProduct.addHom_ext
    intro Y z y
    have hz := CatBimodule.tensorMap_tmul (D) (CatModule.cone.fstHom h) X Y z y
    exact (congrArg s hz).trans
      ((diagramWeightTensorShiftNatIso_hom_tmul G hl hr 1 U X Y z y.1).trans
        (congrArg b (diagramWeightTensorConeIso_hom_tmul G hl hr h X Y z y)).symm)
  exact DFunLike.congr_fun he x

/-- The graded tensor sends a standard cone triangle to the triangle of the tensor map. -/
def diagramWeightTensorTriangleIso :
    (D).tensorFunctor.mapTriangle.obj (CatModule.cone.triangle h) ≅
      CatModule.cone.triangle ((D).tensorMap h) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (diagramWeightTensorConeIso G hl hr h)
    (by
      change (D).tensorMap h ≫ 𝟙 _ = 𝟙 _ ≫ (D).tensorMap h
      rw [Category.comp_id, Category.id_comp])
    (by
      change (D).tensorMap (CatModule.cone.inr h) ≫ (diagramWeightTensorConeIso G hl hr h).hom =
        𝟙 _ ≫ CatModule.cone.inr ((D).tensorMap h)
      rw [Category.id_comp, diagramWeightTensorConeIso_hom_inr])
    (by
      change ((D).tensorMap (-CatModule.cone.fstHom h) ≫
          (diagramWeightTensorShiftNatIso G hl hr 1).hom.app U) ≫
            (shiftFunctor (CatModule.{u} (WeightCategory A)) (1 : ℤ)).map (𝟙 _) =
          (diagramWeightTensorConeIso G hl hr h).hom ≫ (-CatModule.cone.fstHom ((D).tensorMap h))
      rw [(shiftFunctor (CatModule.{u} (WeightCategory A)) (1 : ℤ)).map_id]
      let l := (D).tensorMap (CatModule.cone.fstHom h)
      let r := (diagramWeightTensorShiftNatIso G hl hr 1).hom.app U
      let e := (diagramWeightTensorConeIso G hl hr h).hom
      let p := CatModule.cone.fstHom ((D).tensorMap h)
      have hn : (D).tensorMap (-CatModule.cone.fstHom h) = -l :=
        (D).tensorFunctor.map_neg (f := CatModule.cone.fstHom h)
      have hf : l ≫ r = e ≫ p := diagramWeightTensorConeIso_hom_fstHom G hl hr h
      exact (Category.comp_id _).trans ((congrArg (fun q => q ≫ r) hn).trans
        ((Preadditive.neg_comp l r).trans ((congrArg Neg.neg hf).trans
          (Preadditive.comp_neg e p).symm))))


/-- Tensoring in the homotopy category preserves the standard cone triangle. -/
def diagramWeightTensorTrianglehIso :
    (diagramWeightTensorHomotopy G hl hr).mapTriangle.obj (CatModule.cone.triangleh h) ≅
      CatModule.cone.triangleh ((D).tensorMap h) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (diagramWeightTensorHomotopyFactors G hl hr)).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (CatModule.HomotopyCategory.quotient (WeightCategory A)).mapTriangle.mapIso
      (diagramWeightTensorTriangleIso G hl hr h)

instance diagramWeightTensorHomotopy_isTriangulated :
    (diagramWeightTensorHomotopy G hl hr).IsTriangulated where
  map_distinguished := by
    rintro T ⟨L, M, f, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(diagramWeightTensorHomotopy G hl hr).mapTriangle.mapIso e ≪≫
      diagramWeightTensorTrianglehIso G hl hr f⟩⟩

end DiagramCone

end Categorification
