/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.RescaleBasic
import Categorification.Diagrams.RevBicat
import StringDiagrams.Bicategory

/-!
# Rescaling as a strict 2-functor between presented bicategories

For presentations `P`, `P'` of the same even signature and a rescaling of the generators whose
rescaled relations of `P` hold in `P'` (`Categorification.KL3.Diagram.CL.Rescale`), the rescaling
functor `P.Presented ⥤ P'.Presented` is the identity on objects and commutes with whiskering
(`Rescale.functor_whisk`). It is therefore a strict 2-functor between the presented bicategories,
the identity on objects and 1-morphisms (`Rescale.pseudofunctor`; stated for `RevBicat`, the
orientation used for interpretations, see `Categorification.Diagrams.BicatInterpPseudo`): its
composition and unit constraints are identities.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL.Rescale

open CategoryTheory Bicategory StringDiagrams

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} [S.IsEven] {k : Type w} [CommRing k] {χ : S.Gen → kˣ}
  {P P' : Presentation.{w, v} S k} (h : ∀ i, P'.lin (scL χ (P.rel i)) = 0)

/-- A 1-morphism of `P.Bicat` as a 1-morphism of `P'.Bicat` (the same word). -/
def homMap {l m : P.Bicat} (x : Presentation.Bicat.Hom l m) :
    Presentation.Bicat.Hom (P := P') ⟨l.region⟩ ⟨m.region⟩ :=
  ⟨x.obj, x.start_eq, x.wf, x.endR_eq⟩

omit [S.IsEven] in
@[simp] theorem homMap_obj {l m : P.Bicat} (x : Presentation.Bicat.Hom l m) :
    (homMap (P' := P') x).obj = x.obj := rfl

omit [S.IsEven] in
theorem functor_eqToHom {a b : Obj S} (e : a = b) :
    (functor χ h).map (eqToHom (congrArg P.obj e)) = eqToHom (congrArg P'.obj e) := by
  subst e; simp

omit [S.IsEven] in
theorem functor_wRAt {r : S.Region} {a a' : Obj S} (f : P.obj a ⟶ P.obj a') (b : Obj S)
    (ha : a.start = r) (ha' : a'.start = r) :
    (functor χ h).map (P.wRAt r f b ha ha') = P'.wRAt r ((functor χ h).map f) b ha ha' := by
  simp only [Presentation.wRAt, Functor.map_comp, functor_whisk]
  rw [eqToHom_map, eqToHom_map]
  rfl

omit [S.IsEven] in
theorem functor_wL (a : Obj S) {b b' : Obj S} (g : P.obj b ⟶ P.obj b') :
    (functor χ h).map (P.wL a g) = P'.wL a ((functor χ h).map g) := by
  simp only [Presentation.wL, Functor.map_comp, functor_whisk]
  rw [eqToHom_map, eqToHom_map]
  rfl

/-- **Rescaling as a strict 2-functor** `P.Bicat → P'.Bicat` (read in `RevBicat`): the identity on
objects and 1-morphisms, the rescaling functor on 2-morphisms. -/
def pseudofunctor : Pseudofunctor (RevBicat P.Bicat) (RevBicat P'.Bicat) where
  obj a := ⟨⟨a.as.region⟩⟩
  map {a b} x := homMap (x : Presentation.Bicat.Hom b.as a.as)
  map₂ η := (functor χ h).map η
  map₂_id x := (functor χ h).map_id (P.obj (x : Presentation.Bicat.Hom _ _).obj)
  map₂_comp η θ := (functor χ h).map_comp (X := P.obj (Presentation.Bicat.Hom.obj _))
    (Y := P.obj (Presentation.Bicat.Hom.obj _)) (Z := P.obj (Presentation.Bicat.Hom.obj _)) η θ
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂_whisker_left f g g' η := by
    refine (functor_wRAt h _ _ _ _).trans ?_
    erw [Category.id_comp, Category.comp_id]
    rfl
  map₂_whisker_right η h' := by
    refine (functor_wL h _ _).trans ?_
    erw [Category.id_comp, Category.comp_id]
    rfl
  map₂_associator f g h' := by
    refine (functor_eqToHom h (Obj.tensor_assoc (Presentation.Bicat.Hom.obj h')
      (Presentation.Bicat.Hom.obj g) (Presentation.Bicat.Hom.obj f)).symm).trans ?_
    erw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.id_comp, Category.comp_id,
      Category.comp_id]
    rfl
  map₂_left_unitor {a _} f := by
    refine (functor_eqToHom h (Obj.tensor_nil (Presentation.Bicat.Hom.obj f) a.as.region)).trans ?_
    erw [id_whiskerRight, Category.id_comp, Category.id_comp]
    rfl
  map₂_right_unitor f := by
    refine (functor_eqToHom h (Obj.nil_tensor (Presentation.Bicat.Hom.start_eq f))).trans ?_
    erw [whiskerLeft_id, Category.id_comp, Category.id_comp]
    rfl

@[simp] theorem pseudofunctor_map₂ {a b : RevBicat P.Bicat} {x y : a ⟶ b} (η : x ⟶ y) :
    (pseudofunctor h).map₂ η = (functor χ h).map η := rfl

end Categorification.KL3.Diagram.CL.Rescale
