/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Natural transformations of double and triple inductions given by elements

For nonunital ring maps `φ : A → B`, `φ' : B → C`, `φ'' : C → D`, the composite functors
`Ind_φ ⋙ Ind_φ'` and `Ind_φ ⋙ (Ind_φ' ⋙ Ind_φ'')` are identified with induction along the
composite maps (`compIso`, `tripleIso`). A natural transformation between two such composites
*is represented by* an intertwining element `x` of the last ring when, under these
identifications, it is the element transformation `natTrans` of `x` (`Rep2`, `Rep3`).

Being represented is preserved by composition (product of elements), subtraction, whiskering
on either side (the element itself, or its image under the outer map) and the associator.
Two represented transformations are equal as soon as their elements agree after left
multiplication by the unit of the source (`Rep2.eq`, `Rep3.eq`). This reduces the KLR
relations between whiskered dots and crossings of induction functors (Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6; Kang–Kashiwara, arXiv:1102.4677v4, §4.2) to identities in one ring.
-/

namespace Categorification.InductionAlong

open CategoryTheory

universe u w

noncomputable section

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D]

/-- Induction along three maps, right bracketed, is induction along the composite. -/
def tripleIso (φ : A →ₙ+* B) (φ' : B →ₙ+* C) (φ'' : C →ₙ+* D) :
    functor.{u, w} φ ⋙ (functor.{u, w} φ' ⋙ functor.{u, w} φ'') ≅ functor ((φ''.comp φ').comp φ) :=
  Functor.isoWhiskerLeft (functor.{u, w} φ) (compIso.{u, w} φ' φ'') ≪≫ compIso φ (φ''.comp φ')

theorem tripleIso_hom (φ : A →ₙ+* B) (φ' : B →ₙ+* C) (φ'' : C →ₙ+* D) :
    (tripleIso.{u, w} φ φ' φ'').hom =
      Functor.whiskerLeft (functor.{u, w} φ) (compIso.{u, w} φ' φ'').hom ≫
        (compIso.{u, w} φ (φ''.comp φ')).hom :=
  rfl

/-- The associator, read through `compIso` and `tripleIso`. -/
theorem associator_tripleIso (φ : A →ₙ+* B) (φ' : B →ₙ+* C) (φ'' : C →ₙ+* D) :
    (Functor.associator (functor.{u, w} φ) (functor.{u, w} φ') (functor.{u, w} φ'')).hom ≫
        (tripleIso.{u, w} φ φ' φ'').hom =
      Functor.whiskerRight (compIso.{u, w} φ φ').hom (functor.{u, w} φ'') ≫
        (compIso (φ'.comp φ) φ'').hom := by
  rw [tripleIso_hom, compIso_assoc]

section Rep2

variable {B' B'' : Type u} [Ring B'] [Ring B'']

/-- `α` is represented by the element `x`. -/
def Rep2 {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C}
    (α : functor.{u, w} φ ⋙ functor.{u, w} φ' ⟶ functor.{u, w} ψ ⋙ functor.{u, w} ψ') {x : C}
    (hx : Intertwines (φ'.comp φ) (ψ'.comp ψ) x) : Prop :=
  α ≫ (compIso.{u, w} ψ ψ').hom = (compIso.{u, w} φ φ').hom ≫ natTrans hx

theorem Rep2.eq {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C}
    {α β : functor.{u, w} φ ⋙ functor.{u, w} φ' ⟶ functor.{u, w} ψ ⋙ functor.{u, w} ψ'} {x y : C}
    {hx : Intertwines (φ'.comp φ) (ψ'.comp ψ) x} {hy : Intertwines (φ'.comp φ) (ψ'.comp ψ) y}
    (hα : Rep2 α hx) (hβ : Rep2 β hy) (h : φ' (φ 1) * x = φ' (φ 1) * y) : α = β := by
  rw [← Iso.cancel_iso_hom_right α β (compIso.{u, w} ψ ψ'), hα, hβ,
    natTrans_eq_of_unit_mul hx hy h]

theorem Rep2.comp {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C}
    {χ : A →ₙ+* B''} {χ' : B'' →ₙ+* C}
    {α : functor.{u, w} φ ⋙ functor.{u, w} φ' ⟶
      functor.{u, w} ψ ⋙ functor.{u, w} ψ'}
    {β : functor.{u, w} ψ ⋙ functor.{u, w} ψ' ⟶ functor.{u, w} χ ⋙ functor.{u, w} χ'}
    {x y : C}
    {hx : Intertwines (φ'.comp φ) (ψ'.comp ψ) x} {hy : Intertwines (ψ'.comp ψ) (χ'.comp χ) y}
    (hα : Rep2 α hx) (hβ : Rep2 β hy) : Rep2 (α ≫ β) (hx.mul hy) := by
  rw [Rep2, Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, natTrans_comp]

theorem Rep2.sub {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C}
    {α β : functor.{u, w} φ ⋙ functor.{u, w} φ' ⟶ functor.{u, w} ψ ⋙ functor.{u, w} ψ'} {x y : C}
    {hx : Intertwines (φ'.comp φ) (ψ'.comp ψ) x} {hy : Intertwines (φ'.comp φ) (ψ'.comp ψ) y}
    (hα : Rep2 α hx) (hβ : Rep2 β hy) : Rep2 (α - β) (hx.sub hy) := by
  rw [Rep2, Preadditive.sub_comp, hα, hβ, natTrans_sub, Preadditive.comp_sub]

/-- An element transformation of the outer induction. -/
theorem Rep2.whiskerLeft (φ : A →ₙ+* B) {φ' ψ' : B →ₙ+* C} {x : C}
    (hx : Intertwines φ' ψ' x) :
    Rep2 (Functor.whiskerLeft (functor.{u, w} φ) (natTrans hx)) (hx.comp φ) :=
  whiskerLeft_natTrans φ φ' hx

/-- An element transformation of the inner induction, followed by the outer one. -/
theorem Rep2.whiskerRight {φ ψ : A →ₙ+* B} (φ' : B →ₙ+* C) {y : B}
    (hy : Intertwines φ ψ y) :
    Rep2 (Functor.whiskerRight (natTrans.{u, w} hy) (functor.{u, w} φ')) (hy.map φ') :=
  whiskerRight_natTrans φ φ' hy

end Rep2

section Rep3

variable {B' B'' C' C'' : Type u} [Ring B'] [Ring B''] [Ring C'] [Ring C'']

/-- `α` is represented by the element `x`. -/
def Rep3 {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {φ'' : C →ₙ+* D}
    {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C'} {ψ'' : C' →ₙ+* D}
    (α : functor.{u, w} φ ⋙ (functor.{u, w} φ' ⋙ functor.{u, w} φ'') ⟶
      functor.{u, w} ψ ⋙ (functor.{u, w} ψ' ⋙ functor.{u, w} ψ'')) {x : D}
    (hx : Intertwines ((φ''.comp φ').comp φ) ((ψ''.comp ψ').comp ψ) x) : Prop :=
  α ≫ (tripleIso.{u, w} ψ ψ' ψ'').hom = (tripleIso.{u, w} φ φ' φ'').hom ≫ natTrans hx

theorem Rep3.eq {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {φ'' : C →ₙ+* D}
    {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C'} {ψ'' : C' →ₙ+* D}
    {α β : functor.{u, w} φ ⋙ (functor.{u, w} φ' ⋙ functor.{u, w} φ'') ⟶
      functor.{u, w} ψ ⋙ (functor.{u, w} ψ' ⋙ functor.{u, w} ψ'')} {x y : D}
    {hx : Intertwines ((φ''.comp φ').comp φ) ((ψ''.comp ψ').comp ψ) x}
    {hy : Intertwines ((φ''.comp φ').comp φ) ((ψ''.comp ψ').comp ψ) y}
    (hα : Rep3 α hx) (hβ : Rep3 β hy) (h : φ'' (φ' (φ 1)) * x = φ'' (φ' (φ 1)) * y) :
    α = β := by
  rw [← Iso.cancel_iso_hom_right α β (tripleIso.{u, w} ψ ψ' ψ''), hα, hβ,
    natTrans_eq_of_unit_mul hx hy h]

theorem Rep3.comp {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {φ'' : C →ₙ+* D}
    {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C'} {ψ'' : C' →ₙ+* D}
    {χ : A →ₙ+* B''} {χ' : B'' →ₙ+* C''} {χ'' : C'' →ₙ+* D}
    {α : functor.{u, w} φ ⋙ (functor.{u, w} φ' ⋙ functor.{u, w} φ'') ⟶
      functor.{u, w} ψ ⋙ (functor.{u, w} ψ' ⋙ functor.{u, w} ψ'')}
    {β : functor.{u, w} ψ ⋙ (functor.{u, w} ψ' ⋙ functor.{u, w} ψ'') ⟶
      functor.{u, w} χ ⋙ (functor.{u, w} χ' ⋙ functor.{u, w} χ'')} {x y : D}
    {hx : Intertwines ((φ''.comp φ').comp φ) ((ψ''.comp ψ').comp ψ) x}
    {hy : Intertwines ((ψ''.comp ψ').comp ψ) ((χ''.comp χ').comp χ) y}
    (hα : Rep3 α hx) (hβ : Rep3 β hy) : Rep3 (α ≫ β) (hx.mul hy) := by
  rw [Rep3, Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, natTrans_comp]

theorem Rep3.sub {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {φ'' : C →ₙ+* D}
    {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C'} {ψ'' : C' →ₙ+* D}
    {α β : functor.{u, w} φ ⋙ (functor.{u, w} φ' ⋙ functor.{u, w} φ'') ⟶
      functor.{u, w} ψ ⋙ (functor.{u, w} ψ' ⋙ functor.{u, w} ψ'')} {x y : D}
    {hx : Intertwines ((φ''.comp φ').comp φ) ((ψ''.comp ψ').comp ψ) x}
    {hy : Intertwines ((φ''.comp φ').comp φ) ((ψ''.comp ψ').comp ψ) y}
    (hα : Rep3 α hx) (hβ : Rep3 β hy) : Rep3 (α - β) (hx.sub hy) := by
  rw [Rep3, Preadditive.sub_comp, hα, hβ, natTrans_sub, Preadditive.comp_sub]

/-- Whiskering a represented transformation of the two outer inductions on the left. -/
theorem Rep3.whiskerLeft (φ : A →ₙ+* B) {φ' : B →ₙ+* C} {φ'' : C →ₙ+* D}
    {ψ' : B →ₙ+* C'} {ψ'' : C' →ₙ+* D}
    {α : functor.{u, w} φ' ⋙ functor.{u, w} φ'' ⟶ functor.{u, w} ψ' ⋙ functor.{u, w} ψ''} {x : D}
    {hx : Intertwines (φ''.comp φ') (ψ''.comp ψ') x} (hα : Rep2 α hx) :
    Rep3 (Functor.whiskerLeft (functor.{u, w} φ) α) (hx.comp φ) := by
  rw [Rep3, tripleIso_hom, tripleIso_hom, ← Category.assoc, ← Functor.whiskerLeft_comp, hα,
    Functor.whiskerLeft_comp, Category.assoc, whiskerLeft_natTrans, ← Category.assoc]

/-- Whiskering a represented transformation of the two inner inductions on the right, read
through the associator. -/
theorem Rep3.whiskerRight {φ : A →ₙ+* B} {φ' : B →ₙ+* C} {ψ : A →ₙ+* B'} {ψ' : B' →ₙ+* C}
    (φ'' : C →ₙ+* D) {α : functor.{u, w} φ ⋙ functor.{u, w} φ' ⟶
      functor.{u, w} ψ ⋙ functor.{u, w} ψ'} {y : C}
    {hy : Intertwines (φ'.comp φ) (ψ'.comp ψ) y} (hα : Rep2 α hy) :
    Rep3 ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α (functor.{u, w} φ'') ≫
      (Functor.associator _ _ _).hom)
      (show Intertwines ((φ''.comp φ').comp φ) ((φ''.comp ψ').comp ψ) (φ'' y) from hy.map φ'') := by
  have hφ : (tripleIso.{u, w} φ φ' φ'').hom = (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (compIso.{u, w} φ φ').hom (functor.{u, w} φ'') ≫
        (compIso (φ'.comp φ) φ'').hom := by
    rw [← associator_tripleIso, Iso.inv_hom_id_assoc]
  rw [Rep3, hφ, Category.assoc, Category.assoc, associator_tripleIso,
    ← Functor.whiskerRight_comp_assoc, hα, Functor.whiskerRight_comp_assoc,
    whiskerRight_natTrans]
  simp only [Category.assoc]

/-- An element transformation of the innermost induction, followed by the two outer ones. -/
theorem Rep3.whiskerRight₂ {φ ψ : A →ₙ+* B} (φ' : B →ₙ+* C) (φ'' : C →ₙ+* D) {y : B}
    (hy : Intertwines φ ψ y) :
    Rep3 (Functor.whiskerRight (natTrans.{u, w} hy) (functor.{u, w} φ' ⋙ functor.{u, w} φ''))
      (hy.map (φ''.comp φ')) := by
  rw [Rep3, tripleIso_hom, tripleIso_hom, ← Category.assoc,
    ← Functor.whiskerLeft_comp_whiskerRight, Category.assoc, whiskerRight_natTrans,
    Category.assoc]

end Rep3

end

end Categorification.InductionAlong
