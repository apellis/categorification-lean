/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleDot
import Categorification.TwoRep.CompletionPseudofunctor

/-!
# Natural endomorphisms of a functor as intertwining matrices

In the setting of `MatEndCorner` (an additive functor `F : C ⥤ D`, finite families `X`, `Y` and
an injective `e` with `F (X i) = Y (e i)`), a natural endomorphism `α₀ : F ⟶ F` gives the
diagonal matrix `natEmb α₀` of `MatEnd Y` with entry `α₀ (X i)` at `(e i, e i)`. It intertwines
the matrix map of `F` with itself (`MatEnd.intertwines_natEmb`), and right multiplication by it
on the corner generator is the completed natural transformation `completionMap₂ α₀`
(`MatEnd.karoubiCorner_cornerMul_natEmb`). This is the hypothesis of
`MatEnd.indModuleEquiv_natMap` and its variants, so the dots of Webster's induction functors on
modules over `T^λ` (arXiv:1309.3796v3, §4.6) are the completed dots of the black action.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))

/-- The component of `α₀` at `X i`, transported to `Y (e i)`. -/
def natEntry (α₀ : F ⟶ F) (i : ι) : Y (e i) ⟶ Y (e i) :=
  eqToHom (h i).symm ≫ α₀.app (X i) ≫ eqToHom (h i)

/-- The diagonal matrix of a natural endomorphism `α₀` of `F`, supported on the image of `e`. -/
def natEmb (α₀ : F ⟶ F) : MatEnd Y :=
  ∑ i, single (e i) (e i) (natEntry F h α₀ i)

variable (α₀ : F ⟶ F)

omit [Preadditive C] [DecidableEq ι] in
include he in
theorem natEmb_apply_emb (i : ι) : natEmb F h α₀ (e i) (e i) = natEntry F h α₀ i := by
  rw [natEmb, sum_apply, Finset.sum_eq_single i, single_apply_self]
  · intro l _ hl
    exact single_apply_of_ne _ (fun h' => hl (he h'.1.symm))
  · simp

omit [Preadditive C] [DecidableEq ι] in
theorem natEmb_apply_of_ne {c d : κ} (hcd : c ≠ d) : natEmb F h α₀ c d = 0 := by
  rw [natEmb, sum_apply]
  exact Finset.sum_eq_zero fun l _ => single_apply_of_ne _ (fun h' => hcd (h'.1.trans h'.2.symm))

omit [Preadditive C] [DecidableEq ι] in
theorem natEmb_apply_of_not {d : κ} (hd : ∀ i, e i ≠ d) : natEmb F h α₀ d d = 0 := by
  rw [natEmb, sum_apply]
  exact Finset.sum_eq_zero fun l _ => single_apply_of_ne _ (fun h' => hd l h'.1.symm)

omit [Preadditive C] [DecidableEq ι] in
theorem natEmb_mul_apply (M : MatEnd Y) (a d : κ) :
    (natEmb F h α₀ * M) a d = M a d ≫ natEmb F h α₀ d d := by
  rw [mul_apply, Finset.sum_eq_single d]
  · intro c _ hc
    rw [natEmb_apply_of_ne F h α₀ hc, Limits.comp_zero]
  · simp

omit [Preadditive C] [DecidableEq ι] in
theorem mul_natEmb_apply (M : MatEnd Y) (a d : κ) :
    (M * natEmb F h α₀) a d = natEmb F h α₀ a a ≫ M a d := by
  rw [mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rw [natEmb_apply_of_ne F h α₀ (Ne.symm hc), Limits.zero_comp]
  · simp

omit [Preadditive C] [Preadditive D] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [DecidableEq ι] in
theorem conjF_natEntry {i j : ι} (f : X i ⟶ X j) :
    conjF F h f ≫ natEntry F h α₀ j = natEntry F h α₀ i ≫ conjF F h f := by
  simp only [conjF, natEntry, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, α₀.naturality_assoc]

omit [Preadditive C] [DecidableEq ι] in
include he in
/-- `natEmb α₀` commutes with the image of the matrix map. -/
theorem natEmb_mul_mapEmb (f : MatEnd X) :
    natEmb F h α₀ * mapEmb F h f = mapEmb F h f * natEmb F h α₀ := by
  funext a d
  rw [natEmb_mul_apply, mul_natEmb_apply]
  by_cases ha : ∃ i, e i = a
  · obtain ⟨i, rfl⟩ := ha
    by_cases hd : ∃ j, e j = d
    · obtain ⟨j, rfl⟩ := hd
      rw [mapEmb_apply_emb F he h, natEmb_apply_emb F he h, natEmb_apply_emb F he h,
        conjF_natEntry]
    · push Not at hd
      rw [natEmb_apply_of_not F h α₀ hd, mapEmb_apply_of_right F h hd, Limits.comp_zero,
        Limits.comp_zero]
  · push Not at ha
    rw [natEmb_apply_of_not F h α₀ ha, mapEmb_apply_of_left F h ha, Limits.zero_comp,
      Limits.zero_comp]

variable [F.Additive]

/-- **`natEmb α₀` intertwines the matrix map of `F` with itself.** -/
theorem intertwines_natEmb :
    Intertwines (mapEmbOp F he h) (mapEmbOp F he h) (op (natEmb F h α₀)) := fun f =>
  unop_injective (by
    change natEmb F h α₀ * mapEmb F h f.unop = mapEmb F h f.unop * natEmb F h α₀
    exact natEmb_mul_mapEmb F he h α₀ f.unop)

omit [DecidableEq κ] in
theorem matNatTrans_familySum :
    ((matNatTrans α₀).app (familySum X) ≫ F.mapMat_.map (𝟙 (familySum X)) :
      familySum (fun i => F.obj (X i)) ⟶ familySum (fun i => F.obj (X i))) =
      toFamilyHom (fun i => F.obj (X i)) (fun i => F.obj (X i))
        (fun i j => F.map ((1 : MatEnd X) i j) ≫ α₀.app (X j)) := by
  rw [F.mapMat_.map_id]
  refine (Category.comp_id _).trans ?_
  funext (a : Fin (Fintype.card ι)) (b : Fin (Fintype.card ι))
  change F.map ((𝟙 (familySum X) : familySum X ⟶ familySum X) a b) ≫
      α₀.app (X ((Fintype.equivFin ι).symm b)) =
    F.map ((1 : MatEnd X) ((Fintype.equivFin ι).symm a) ((Fintype.equivFin ι).symm b)) ≫
      α₀.app (X ((Fintype.equivFin ι).symm b))
  congr 2
  exact (congrFun (congrFun (map_one (familyMatrixEquiv X)) a) b).symm

/-- **Right multiplication by `natEmb α₀` on the corner generator is `completionMap₂ α₀`.** This
is the hypothesis `hα` of `MatEnd.indModuleEquiv_natMap`. -/
theorem karoubiCorner_cornerMul_natEmb :
    karoubiCorner F he h (cornerMul (intertwines_natEmb F he h α₀) (unitGen (mapEmbOp F he h))) =
      karoubiGen F he h ≫ (completionMap₂ α₀).app ((toKaroubi _).obj (familySum X)) := by
  apply Karoubi.hom_ext
  change toFamilyHom Y _ (cornerEquiv F he h (cornerMul (intertwines_natEmb F he h α₀)
      (unitGen (mapEmbOp F he h)))) =
    toFamilyHom Y _ (cornerEquiv F he h (unitGen (mapEmbOp F he h))) ≫
      ((matNatTrans α₀).app (familySum X) ≫ F.mapMat_.map (𝟙 (familySum X)) :
        familySum (fun i => F.obj (X i)) ⟶ familySum (fun i => F.obj (X i)))
  rw [matNatTrans_familySum, toFamilyHom_comp]
  congr 1
  funext a j
  rw [cornerEquiv_apply, Finset.sum_eq_single j]
  · change (natEmb F h α₀ * mapEmb F h 1) a (e j) ≫ _ = _
    rw [natEmb_mul_apply, natEmb_apply_emb F he h, cornerEquiv_apply, one_apply_self,
      F.map_id, Category.id_comp]
    simp only [natEntry, unitGen, mapEmbOp_apply, unop_one, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
  · intro l _ hl
    rw [one_apply_of_ne hl, F.map_zero, Limits.zero_comp, Limits.comp_zero]
  · simp

end MatEnd

end Categorification.KLR.Diagram
