/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndCorner
import Categorification.Algebra.InductionAlongRes

/-!
# Morphisms out of the image of a sum as a restriction

In the setting of `MatEndCorner` (an additive functor `F : C ⥤ D`, finite families `X`, `Y` and
an injective `e` with `F (X i) = Y (e i)`), the image `F (⊕ X)` of the sum of `X` is the summand
of `⊕ Y` cut out by the idempotent `φ(1)` of the matrix map `φ` of `F`. Hence for every object
`M` of the idempotent completion, `Hom(F (⊕ X), M)` is the restriction along `φ` of the right
`MatEnd Y`-module `Hom(⊕ Y, M)` (`resEquivKaroubi`), semilinearly for `MatEnd X`
(`resEquivKaroubi_smul`).

This is the module-side form of the right adjoint of `F`, used for the action of `Eᵢ` in
Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6, after
Theorem 4.31.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe w v

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))

/-- The inclusion of the columns in the image of `e`. -/
def sectRect (i : ι) (a : κ) : F.obj (X i) ⟶ Y a :=
  eqToHom (h i) ≫ mapEmb F h 1 (e i) a

/-- The section `F (⊕ X) → ⊕ Y` of the corner generator `φ(1)`. -/
def karoubiSect :
    (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)) ⟶
      (toKaroubi _).obj (familySum Y) :=
  ⟨toFamilyHom (fun i => F.obj (X i)) Y (sectRect F h), by
    change F.mapMat_.map (𝟙 (familySum X)) ≫ toFamilyHom (fun i => F.obj (X i)) Y
      (sectRect F h) ≫ 𝟙 (familySum Y) = _
    rw [F.mapMat_.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _)⟩

/-- The corner generator `φ(1)` as a morphism `⊕ Y → F (⊕ X)`. -/
abbrev karoubiGen :
    (toKaroubi _).obj (familySum Y) ⟶
      (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)) :=
  karoubiCorner F he h (unitGen (mapEmbOp F he h))

include he in
theorem mapEmb_one_mul_one (a b : κ) :
    ∑ c, mapEmb F h 1 a c ≫ mapEmb F h 1 c b = mapEmb F h 1 a b := by
  have := congrFun (congrFun (mapEmb_mul F he h (1 : MatEnd X) 1) a) b
  rw [one_mul, mul_apply] at this
  exact this.symm

theorem karoubiSect_gen : karoubiSect F h ≫ karoubiGen F he h = 𝟙 _ := by
  apply Karoubi.hom_ext
  change toFamilyHom (fun i => F.obj (X i)) Y (sectRect F h) ≫
      toFamilyHom Y (fun i => F.obj (X i)) (cornerEquiv F he h (unitGen (mapEmbOp F he h))) =
    F.mapMat_.map (𝟙 (familySum X))
  rw [F.mapMat_.map_id]
  change _ = 𝟙 (familySum fun i => F.obj (X i))
  rw [toFamilyHom_comp, show (𝟙 (familySum fun i => F.obj (X i))) =
      toFamilyHom (fun i => F.obj (X i)) (fun i => F.obj (X i)) (1 : MatEnd fun i => F.obj (X i))
      from (map_one (familyMatrixEquiv fun i => F.obj (X i))).symm]
  congr 1
  funext i j
  simp only [sectRect, cornerEquiv_apply, unitGen, mapEmbOp_apply, unop_one, Category.assoc]
  rw [← Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← Preadditive.sum_comp]
  rw [mapEmb_one_mul_one F he h, mapEmb_apply_emb F he h]
  by_cases hij : i = j
  · subst hij
    simp [conjF]
  · rw [one_apply_of_ne hij, one_apply_of_ne hij, conjF_zero]
    simp

theorem karoubiGen_sect :
    karoubiGen F he h ≫ karoubiSect F h =
      (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop := by
  apply Karoubi.hom_ext
  change toFamilyHom Y (fun i => F.obj (X i)) (cornerEquiv F he h (unitGen (mapEmbOp F he h))) ≫
      toFamilyHom (fun i => F.obj (X i)) Y (sectRect F h) =
    toFamilyHom Y Y (mapEmb F h 1)
  rw [toFamilyHom_comp]
  congr 1
  funext a b
  simp only [sectRect, cornerEquiv_apply, unitGen, mapEmbOp_apply, unop_one, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← mapEmb_one_mul_one F he h a b]
  refine (sum_emb he (fun c => mapEmb F h 1 a c ≫ mapEmb F h 1 c b) fun c hc => ?_).symm
  change mapEmb F h 1 a c ≫ _ = 0
  rw [mapEmb_apply_of_right F h hc, Limits.zero_comp]

theorem karoubiMatrixOpY_gen :
    (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop ≫ karoubiGen F he h = karoubiGen F he h := by
  rw [← karoubiCorner_smul]
  congr 1
  exact Subtype.ext (unit_mul_unit (mapEmbOp F he h))

theorem karoubiGen_map (m : (MatEnd X)ᵐᵒᵖ) :
    karoubiGen F he h ≫ (mapKaroubi F.mapMat_).map (karoubiMatrixOp X m).unop =
      (karoubiMatrixOpY Y (mapEmbOp F he h m)).unop ≫ karoubiGen F he h := by
  rw [← karoubiCorner_op_smul, ← karoubiCorner_smul]
  congr 1
  apply Subtype.ext
  change mapEmbOp F he h 1 * mapEmbOp F he h m = mapEmbOp F he h m * mapEmbOp F he h 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

theorem karoubiSect_matrixOpY (m : (MatEnd X)ᵐᵒᵖ) :
    karoubiSect F h ≫ (karoubiMatrixOpY Y (mapEmbOp F he h m)).unop =
      (mapKaroubi F.mapMat_).map (karoubiMatrixOp X m).unop ≫ karoubiSect F h := by
  have hm : (karoubiMatrixOpY Y (mapEmbOp F he h m)).unop =
      (karoubiMatrixOpY Y (mapEmbOp F he h m)).unop ≫
        (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop := by
    rw [← End.mul_def, ← unop_mul, ← map_mul, ← map_mul, mul_one]
  rw [hm, ← karoubiGen_sect F he h, ← Category.assoc _ (karoubiGen F he h),
    ← karoubiGen_map F he h m]
  simp only [Category.assoc]
  rw [← Category.assoc (karoubiSect F h), karoubiSect_gen, Category.id_comp]

variable (M : Karoubi (Mat_ D))

/-- **Morphisms out of `F (⊕ X)` as a restriction along the matrix map**: `Hom(F (⊕ X), M)` is
the `φ(1)`-fixed part of `Hom(⊕ Y, M)`, by precomposition with the section and the generator. -/
def resEquivKaroubi :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) M
    Res (mapEmbOp F he h) ((toKaroubi _).obj (familySum Y) ⟶ M) ≃+
      ((mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)) ⟶ M) :=
  letI := HomTensor.homModule _ (karoubiMatrixOpY Y) M
  { toFun := fun g => karoubiSect F h ≫ g.val
    invFun := fun f => Res.mk (karoubiGen F he h ≫ f) (by
      change (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop ≫ karoubiGen F he h ≫ f = _
      rw [← Category.assoc, karoubiMatrixOpY_gen])
    left_inv := fun g => Res.ext (by
      change karoubiGen F he h ≫ karoubiSect F h ≫ g.val = g.val
      rw [← Category.assoc, karoubiGen_sect]
      exact g.prop)
    right_inv := fun f => by
      change karoubiSect F h ≫ karoubiGen F he h ≫ f = f
      rw [← Category.assoc, karoubiSect_gen, Category.id_comp]
    map_add' := fun g g' => Preadditive.comp_add _ _ _ _ _ _ }

theorem resEquivKaroubi_apply :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) M
    ∀ g : Res (mapEmbOp F he h) ((toKaroubi _).obj (familySum Y) ⟶ M),
      resEquivKaroubi F he h M g = karoubiSect F h ≫ g.val :=
  fun _ => rfl

theorem resEquivKaroubi_symm_apply
    (f : (mapKaroubi F.mapMat_).obj ((toKaroubi _).obj (familySum X)) ⟶ M) :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) M
    ((resEquivKaroubi F he h M).symm f).val = karoubiGen F he h ≫ f :=
  rfl

/-- The restriction comparison is semilinear: the action of `MatEnd X` on the restriction is
precomposition with its image under `F`. -/
theorem resEquivKaroubi_smul :
    letI := HomTensor.homModule _ (karoubiMatrixOpY Y) M
    ∀ (m : (MatEnd X)ᵐᵒᵖ) (g : Res (mapEmbOp F he h) ((toKaroubi _).obj (familySum Y) ⟶ M)),
      resEquivKaroubi F he h M (m • g) =
        (mapKaroubi F.mapMat_).map (karoubiMatrixOp X m).unop ≫ resEquivKaroubi F he h M g := by
  let _ := HomTensor.homModule _ (karoubiMatrixOpY Y) M
  intro m g
  change karoubiSect F h ≫ ((karoubiMatrixOpY Y (mapEmbOp F he h m)).unop ≫ g.val) = _
  rw [← Category.assoc, karoubiSect_matrixOpY, Category.assoc]
  rfl

end MatEnd

end Categorification.KLR.Diagram
