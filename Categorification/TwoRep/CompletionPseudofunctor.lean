/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Karoubi
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Category.Cat

/-!
# Additive idempotent completion of a strict action

The additive idempotent completion `Karoubi (Mat_ A)` of a preadditive category is functorial
in additive functors and natural transformations, and strictly so: the completion of a
composite functor is the composite of the completions. Hence a strict pseudofunctor into `Cat`
whose values are preadditive and whose 1-cells act by additive functors induces a strict
pseudofunctor on the completions. This is the passage from an action on a category to the
action on its category of (graded) projective modules, used for Webster, arXiv:1309.3796v3,
§4.6, Theorem 4.31.
-/

noncomputable section

namespace Categorification

open CategoryTheory Idempotents

section Completion

universe v u₁ u₂ u₃

variable {A : Type u₁} [Category.{v} A] [Preadditive A] {B : Type u₂} [Category.{v} B]
  [Preadditive B] {C : Type u₃} [Category.{v} C] [Preadditive C]

/-- The functor induced by an additive functor on additive idempotent completions. -/
def completionMap (F : A ⥤ B) [F.Additive] : Karoubi (Mat_ A) ⥤ Karoubi (Mat_ B) :=
  mapKaroubi F.mapMat_

theorem completionMap_comp (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] :
    completionMap (F ⋙ G) = completionMap F ⋙ completionMap G :=
  rfl

theorem completionMap_id : completionMap (𝟭 A) = 𝟭 (Karoubi (Mat_ A)) :=
  rfl

/-- The diagonal matrix of a natural transformation between additive functors: its entry at
`(i, j)` is `F` applied to the `(i, j)` entry of the identity matrix, followed by `α`. -/
def matNatTrans {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.mapMat_ ⟶ G.mapMat_ where
  app M i j := F.map ((𝟙 M : M ⟶ M) i j) ≫ α.app (M.X j)
  naturality {M N} f := by
    ext i k
    revert i k
    intro (i : M.ι) (k : N.ι)
    change ∑ j : N.ι, F.map (f i j) ≫ (F.map ((𝟙 N : N ⟶ N) j k) ≫ α.app (N.X k)) =
      ∑ j : M.ι, (F.map ((𝟙 M : M ⟶ M) i j) ≫ α.app (M.X j)) ≫ G.map (f j k)
    simp only [Category.assoc, ← α.naturality, ← F.map_comp_assoc, ← Preadditive.sum_comp,
      ← F.map_sum]
    rw [← Mat_.comp_apply, ← Mat_.comp_apply, Category.comp_id, Category.id_comp]

theorem matNatTrans_app_apply {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    (M : Mat_ A) (i j : M.ι) :
    (matNatTrans α).app M i j = F.map ((𝟙 M : M ⟶ M) i j) ≫ α.app (M.X j) :=
  rfl

@[simp] theorem matNatTrans_app_self {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    (M : Mat_ A) (i : M.ι) : (matNatTrans α).app M i i = α.app (M.X i) := by
  rw [matNatTrans_app_apply, Mat_.id_apply_self, F.map_id, Category.id_comp]

@[simp] theorem matNatTrans_app_of_ne {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    (M : Mat_ A) {i j : M.ι} (h : i ≠ j) : (matNatTrans α).app M i j = 0 := by
  rw [matNatTrans_app_apply, Mat_.id_apply_of_ne _ _ _ h, F.map_zero, Limits.zero_comp]
  rfl

theorem map_id_apply (F : A ⥤ B) [F.Additive] (M : Mat_ A) (i j : M.ι) :
    F.map ((𝟙 M : M ⟶ M) i j) = (𝟙 (F.mapMat_.obj M) : F.mapMat_.obj M ⟶ _) i j :=
  congr_fun (congr_fun (F.mapMat_.map_id M) i) j

theorem matNatTrans_id (F : A ⥤ B) [F.Additive] : matNatTrans (𝟙 F) = 𝟙 F.mapMat_ := by
  ext M i j
  revert i j
  intro (i : M.ι) (j : M.ι)
  change F.map ((𝟙 M : M ⟶ M) i j) ≫ 𝟙 _ = _
  rw [Category.comp_id, map_id_apply]
  rfl

theorem matNatTrans_comp {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) :
    matNatTrans (α ≫ β) = matNatTrans α ≫ matNatTrans β := by
  ext M i k
  revert i k
  intro (i : M.ι) (k : M.ι)
  change F.map ((𝟙 M : M ⟶ M) i k) ≫ (α.app (M.X k) ≫ β.app (M.X k)) =
    ∑ j : M.ι, (F.map ((𝟙 M : M ⟶ M) i j) ≫ α.app (M.X j)) ≫
      (G.map ((𝟙 M : M ⟶ M) j k) ≫ β.app (M.X k))
  simp only [Category.assoc, ← α.naturality_assoc, ← F.map_comp_assoc,
    ← Preadditive.sum_comp, ← F.map_sum]
  rw [← Mat_.comp_apply, Category.comp_id]

/-- The natural transformation induced on additive idempotent completions. -/
def completionMap₂ {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    completionMap F ⟶ completionMap G where
  app P := ⟨(matNatTrans α).app P.X ≫ G.mapMat_.map P.p, by
    change F.mapMat_.map P.p ≫ ((matNatTrans α).app P.X ≫ G.mapMat_.map P.p) ≫
      G.mapMat_.map P.p = _
    rw [Category.assoc, ← G.mapMat_.map_comp, P.idem, ← Category.assoc,
      (matNatTrans α).naturality, Category.assoc, ← G.mapMat_.map_comp, P.idem]
    rfl⟩
  naturality {P Q} f := by
    apply Karoubi.hom_ext
    change F.mapMat_.map f.f ≫ ((matNatTrans α).app Q.X ≫ G.mapMat_.map Q.p) =
      ((matNatTrans α).app P.X ≫ G.mapMat_.map P.p) ≫ G.mapMat_.map f.f
    rw [← Category.assoc, (matNatTrans α).naturality, Category.assoc, Category.assoc,
      ← G.mapMat_.map_comp, ← G.mapMat_.map_comp, Karoubi.comp_p, Karoubi.p_comp]

@[simp] theorem completionMap₂_app_f {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    (P : Karoubi (Mat_ A)) :
    ((completionMap₂ α).app P).f = (matNatTrans α).app P.X ≫ G.mapMat_.map P.p :=
  rfl

theorem completionMap₂_id (F : A ⥤ B) [F.Additive] :
    completionMap₂ (𝟙 F) = 𝟙 (completionMap F) := by
  refine NatTrans.ext (funext fun P => Karoubi.hom_ext _ _ ?_)
  rw [completionMap₂_app_f, matNatTrans_id, NatTrans.id_app, Category.id_comp]
  rfl

theorem completionMap₂_comp {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) :
    completionMap₂ (α ≫ β) = completionMap₂ α ≫ completionMap₂ β := by
  refine NatTrans.ext (funext fun P => Karoubi.hom_ext _ _ ?_)
  change (matNatTrans (α ≫ β)).app P.X ≫ H.mapMat_.map P.p =
    ((matNatTrans α).app P.X ≫ G.mapMat_.map P.p) ≫
      ((matNatTrans β).app P.X ≫ H.mapMat_.map P.p)
  rw [matNatTrans_comp, NatTrans.comp_app, Category.assoc, Category.assoc,
    ← Category.assoc (G.mapMat_.map P.p), (matNatTrans β).naturality, Category.assoc,
    ← H.mapMat_.map_comp, P.idem]

theorem completionMap₂_eqToHom {F G : A ⥤ B} [F.Additive] [G.Additive] (h : F = G) :
    completionMap₂ (eqToHom h) = eqToHom (by subst h; rfl) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, completionMap₂_id]

theorem completionMap₂_whiskerLeft (F : A ⥤ B) [F.Additive] {G G' : B ⥤ C} [G.Additive]
    [G'.Additive] (β : G ⟶ G') :
    completionMap₂ (Functor.whiskerLeft F β) =
      Functor.whiskerLeft (completionMap F) (completionMap₂ β) := by
  refine NatTrans.ext (funext fun P => Karoubi.hom_ext _ _ ?_)
  change (matNatTrans (Functor.whiskerLeft F β)).app P.X ≫ (F ⋙ G').mapMat_.map P.p =
    (matNatTrans β).app (F.mapMat_.obj P.X) ≫ G'.mapMat_.map (F.mapMat_.map P.p)
  congr 1
  ext i j
  revert i j
  intro (i : P.X.ι) (j : P.X.ι)
  change G.map (F.map ((𝟙 P.X : P.X ⟶ P.X) i j)) ≫ β.app (F.obj (P.X.X j)) =
    G.map ((𝟙 (F.mapMat_.obj P.X) : F.mapMat_.obj P.X ⟶ _) i j) ≫ β.app (F.obj (P.X.X j))
  rw [map_id_apply]
  rfl

theorem completionMap₂_whiskerRight {F F' : A ⥤ B} [F.Additive] [F'.Additive] (α : F ⟶ F')
    (G : B ⥤ C) [G.Additive] :
    completionMap₂ (Functor.whiskerRight α G) =
      Functor.whiskerRight (completionMap₂ α) (completionMap G) := by
  refine NatTrans.ext (funext fun P => Karoubi.hom_ext _ _ ?_)
  change (matNatTrans (Functor.whiskerRight α G)).app P.X ≫ (F' ⋙ G).mapMat_.map P.p =
    G.mapMat_.map ((matNatTrans α).app P.X ≫ F'.mapMat_.map P.p)
  rw [G.mapMat_.map_comp]
  congr 1
  ext i j
  revert i j
  intro (i : P.X.ι) (j : P.X.ι)
  exact (G.map_comp _ _).symm

theorem completionMap_congr {F G : A ⥤ B} [F.Additive] [G.Additive] (h : F = G) :
    completionMap F = completionMap G := by
  subst h; rfl

theorem completionMap₂_congr {F G : A ⥤ B} [F.Additive] [G.Additive] {α β : F ⟶ G}
    (h : α = β) : completionMap₂ α = completionMap₂ β := by
  rw [h]

end Completion

section Pseudofunctor

universe w₁ w₂ w₃ v u

variable {𝔅 : Type w₁} [Bicategory.{w₂, w₃} 𝔅] [Bicategory.Strict 𝔅]
  (F : StrictPseudofunctor 𝔅 Cat.{v, u})
  [hpre : ∀ a, Preadditive (F.obj a)]
  [hadd : ∀ (a b : 𝔅) (f : a ⟶ b), (F.map f).toFunctor.Additive]

open Bicategory

instance Cat.id_toFunctor_additive (D : Cat.{v, u}) [Preadditive D] :
    (𝟙 D : D ⟶ D).toFunctor.Additive :=
  inferInstanceAs (𝟭 D).Additive

instance Cat.comp_toFunctor_additive {D E G : Cat.{v, u}} [Preadditive D] [Preadditive E]
    [Preadditive G] (S : D ⟶ E) (T : E ⟶ G) [S.toFunctor.Additive] [T.toFunctor.Additive] :
    (S ≫ T).toFunctor.Additive :=
  inferInstanceAs (S.toFunctor ⋙ T.toFunctor).Additive

/-- The additive idempotent completion of a strict pseudofunctor into `Cat` whose values are
preadditive and whose 1-cells act by additive functors: it sends an object `a` to
`Karoubi (Mat_ (F a))`. -/
def StrictPseudofunctor.completion : StrictPseudofunctor 𝔅 Cat.{v, max 1 u v} :=
  StrictPseudofunctor.mk''
    { obj := fun a => Cat.of (Karoubi (Mat_ (F.obj a)))
      map := fun {a b} f => (completionMap (F.map f).toFunctor).toCatHom
      map₂ := fun {_ _ f g} η => (completionMap₂ (F.map₂ η).toNatTrans).toCatHom₂
      map₂_id := fun f => by
        ext1
        simp only [NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_id]
        rw [completionMap₂_congr (congrArg Cat.Hom₂.toNatTrans (F.map₂_id f)),
          Cat.Hom.toNatTrans_id, completionMap₂_id]
        rfl
      map₂_comp := fun {_ _ f g h} η θ => by
        ext1
        simp only [NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_comp]
        rw [completionMap₂_congr (congrArg Cat.Hom₂.toNatTrans (F.map₂_comp η θ)),
          Cat.Hom.toNatTrans_comp, completionMap₂_comp]
      map_id := fun a => by
        apply Cat.ext
        change completionMap (F.map (𝟙 a)).toFunctor = 𝟭 _
        rw [completionMap_congr (congrArg Cat.Hom.toFunctor (F.map_id a))]
        rfl
      map_comp := fun {a b c} f g => by
        apply Cat.ext
        change completionMap (F.map (f ≫ g)).toFunctor =
          completionMap (F.map f).toFunctor ⋙ completionMap (F.map g).toFunctor
        rw [completionMap_congr (congrArg Cat.Hom.toFunctor (F.map_comp f g))]
        rfl
      map₂_whisker_left := fun {a b c} f {g g'} η => by
        ext1
        have hF := congrArg Cat.Hom₂.toNatTrans (F.map₂_whisker_left f η)
        rw [F.mapComp_eq_eqToIso, F.mapComp_eq_eqToIso] at hF
        simp only [eqToIso.hom, eqToIso.inv, Cat.Hom.toNatTrans_comp,
          Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans] at hF
        simp only [NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_comp,
          Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans]
        rw [completionMap₂_congr hF, completionMap₂_comp, completionMap₂_comp,
          completionMap₂_eqToHom, completionMap₂_eqToHom, completionMap₂_whiskerLeft]
        rfl
      map₂_whisker_right := fun {a b c} {f f'} η g => by
        ext1
        have hF := congrArg Cat.Hom₂.toNatTrans (F.map₂_whisker_right η g)
        rw [F.mapComp_eq_eqToIso, F.mapComp_eq_eqToIso] at hF
        simp only [eqToIso.hom, eqToIso.inv, Cat.Hom.toNatTrans_comp,
          Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans] at hF
        simp only [NatTrans.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_comp,
          Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans]
        rw [completionMap₂_congr hF, completionMap₂_comp, completionMap₂_comp,
          completionMap₂_eqToHom, completionMap₂_eqToHom, completionMap₂_whiskerRight]
        rfl }

end Pseudofunctor

end Categorification

end
