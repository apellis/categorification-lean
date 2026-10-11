/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissibleHorizontal
import StringDiagrams.Whisker

/-!
# Admissible descent to the original quotient

`admissiblePresentedInterp` is a linear functor on the full subcategory of
`P.Presented` with prescribed admissible outer regions. Its morphisms are those
of the original quotient, not a newly generated relation. Well-definedness uses
`admissibleMap_ideal`, and horizontal compatibility holds for all quotient
morphisms. No zero objects or values at inadmissible objects are introduced.
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams
universe w₁ w₂ u₀ u₁ u₂ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C}
variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]
variable (G : GenImg M) (P : Presentation S k)
  (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
    (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
  (heven : ∀ g, S.odd g = false)

/-- The admissible full subcategory of the original presented category. -/
abbrev PresentedAdmissible (s t : S.Region) :=
  ObjectProperty.FullSubcategory (fun a : P.Presented => Cond s t (show Obj S from a.as))

/-- Evaluation of an actual quotient morphism on an admissible component. -/
def admissibleQuotientMap {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (f : P.obj a ⟶ P.obj b) :
    M.word s a.word t ha.1 ha.2.1 ⟶ M.word s b.word t hb.1 hb.2.1 :=
  Quot.liftOn f (admissibleMap G ha hb) fun f g h => by
    apply sub_eq_zero.mp
    erw [← map_sub]
    exact admissibleMap_ideal G P hrel heven ha hb (f - g)
      ((HomRel.compClosure_iff_self P.homRel f g).mp h)

/-- Evaluation on a representative is the unchanged admissible map. -/
@[simp] theorem admissibleQuotientMap_lin {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (f : LinDiagram k a b) :
    admissibleQuotientMap G P hrel heven ha hb (P.lin f) = admissibleMap G ha hb f := rfl

/-- Descent to the actual quotient, restricted only on objects. -/
def admissiblePresentedInterp (s t : S.Region) :
    PresentedAdmissible P s t ⥤ (M.obj t ⟶ M.obj s) where
  obj a := M.word s (Obj.word a.obj.as) t a.property.1 a.property.2.1
  map {a b} f := admissibleQuotientMap G P hrel heven a.property b.property f.hom
  map_id a := by
    change admissibleMap G a.property a.property (LinDiagram.of (𝟙 (show Obj S from a.obj.as))) = _
    rw [admissibleMap_of]
    exact (admissibleInterp G s t).map_id ⟨a.obj.as, a.property⟩
  map_comp {a b c} f g := by
    obtain ⟨f', hf⟩ := (CategoryTheory.Quotient.functor P.homRel).map_surjective f.hom
    obtain ⟨g', hg⟩ := (CategoryTheory.Quotient.functor P.homRel).map_surjective g.hom
    change admissibleQuotientMap G P hrel heven a.property c.property (f.hom ≫ g.hom) = _
    rw [← hf, ← hg]
    exact admissibleMap_comp G a.property b.property c.property f' g'

instance admissiblePresentedInterp_additive (s t : S.Region) :
    (admissiblePresentedInterp G P hrel heven s t).Additive where
  map_add := by
    intro a b f g
    change admissibleQuotientMap G P hrel heven a.property b.property (f.hom + g.hom) =
      admissibleQuotientMap G P hrel heven a.property b.property f.hom +
        admissibleQuotientMap G P hrel heven a.property b.property g.hom
    obtain ⟨f', hf⟩ := (CategoryTheory.Quotient.functor P.homRel).map_surjective f.hom
    obtain ⟨g', hg⟩ := (CategoryTheory.Quotient.functor P.homRel).map_surjective g.hom
    rw [← hf, ← hg, ← Functor.map_add]
    exact (admissibleMap G a.property b.property).map_add f' g'

instance admissiblePresentedInterp_linear (s t : S.Region) :
    (admissiblePresentedInterp G P hrel heven s t).Linear k where
  map_smul := by
    intro a b f r
    change admissibleQuotientMap G P hrel heven a.property b.property (r • f.hom) =
      r • admissibleQuotientMap G P hrel heven a.property b.property f.hom
    obtain ⟨f', hf⟩ := (CategoryTheory.Quotient.functor P.homRel).map_surjective f.hom
    rw [← hf]
    change admissibleMap G a.property b.property (r • f') = _
    exact (admissibleMap G a.property b.property).map_smul r f'

/-- Identity law on the original quotient. -/
@[simp] theorem admissibleQuotientMap_id {s t : S.Region} {a : Obj S} (ha : Cond s t a) :
    admissibleQuotientMap G P hrel heven ha ha (𝟙 (P.obj a)) = 𝟙 _ :=
  (admissiblePresentedInterp G P hrel heven s t).map_id ⟨P.obj a, ha⟩

/-- Composition law on the original quotient. -/
@[simp] theorem admissibleQuotientMap_comp {s t : S.Region} {a b c : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (hc : Cond s t c)
    (f : P.obj a ⟶ P.obj b) (g : P.obj b ⟶ P.obj c) :
    admissibleQuotientMap G P hrel heven ha hc (f ≫ g) =
      admissibleQuotientMap G P hrel heven ha hb f ≫
        admissibleQuotientMap G P hrel heven hb hc g :=
  (admissiblePresentedInterp G P hrel heven s t).map_comp
    (ObjectProperty.homMk (X := ⟨P.obj a, ha⟩) (Y := ⟨P.obj b, hb⟩) f)
    (ObjectProperty.homMk (X := ⟨P.obj b, hb⟩) (Y := ⟨P.obj c, hc⟩) g)

/-- Equality transport is the image of the corresponding free coherence morphism. -/
theorem admissibleQuotientMap_eqToHom {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (e : a = b) :
    admissibleQuotientMap G P hrel heven ha hb (eqToHom (congrArg P.obj e)) =
      M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word e) ha.1 ha.2.1 hb.1 hb.2.1)) := by
  subst b
  rw [eqToHom_refl, admissibleQuotientMap_id, eqToHom_refl, PrelaxFunctor.map₂_id]

/-- Horizontal coherence survives the original quotient, for every quotient morphism. -/
theorem admissibleQuotientMap_whisk (s t : S.Region) {a b u : Obj S}
    {v : List S.Colour} (ha : Cond s t a) (hb : Cond s t b)
    (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s) (hvv : S.ok t v)
    (hw : a.WhiskerOK u v) (f : P.obj a ⟶ P.obj b) :
    admissibleQuotientMap G P hrel heven (ha.whisker hu hue hvv) (hb.whisker hu hue hvv)
      (P.whisk f u v) =
    M.lift.map₂ (splitW hu hue hvv a ha).hom ≫
      midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue)
        (admissibleQuotientMap G P hrel heven ha hb f) ≫
          M.lift.map₂ (splitW hu hue hvv b hb).inv := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [P.whisk_lin, LinDiagram.whisk_of_ok _ hw, admissibleQuotientMap_lin,
    admissibleQuotientMap_lin]
  exact admissibleMap_whisker G ha hb hu hue hvv hw f

/-- Coherent form of quotient whiskering with arbitrary free coherence maps. -/
theorem admissibleQuotientMap_whisk_coherent {a b : Obj S} (f : P.obj a ⟶ P.obj b)
    {s t s' t' : S.Region} (ha : Cond s t a) (hb : Cond s t b)
    {u : Obj S} {v : List S.Colour} (hs' : u.start = s')
    (hu : S.ok s' u.word) (hue : S.endR s' u.word = s) (hvv : S.ok t v)
    (ht' : S.endR t v = t') (hwa : Cond s' t' (a.whisker u v))
    (hwb : Cond s' t' (b.whisker u v))
    (φ : fw s' (a.whisker u v).word t' hwa.1 hwa.2.1 ⟶
      fw t v t' hvv ht' ≫ (fw s a.word t ha.1 ha.2.1 ≫ fw s' u.word s hu hue))
    (ψ : fw t v t' hvv ht' ≫ (fw s b.word t hb.1 hb.2.1 ≫ fw s' u.word s hu hue) ⟶
      fw s' (b.whisker u v).word t' hwb.1 hwb.2.1) :
    admissibleQuotientMap G P hrel heven hwa hwb (P.whisk f u v) =
      M.lift.map₂ φ ≫ M.lift.map (fw t v t' hvv ht') ◁
        (admissibleQuotientMap G P hrel heven ha hb f ▷ M.lift.map (fw s' u.word s hu hue)) ≫
          M.lift.map₂ ψ := by
  subst hs'
  subst ht'
  have hw : a.WhiskerOK u v := ⟨hu, hue.trans ha.2.2.symm,
    by change S.ok (S.endR a.start a.word) v; rw [ha.2.2, ha.2.1]; exact hvv⟩
  rw [admissibleQuotientMap_whisk G P hrel heven s t ha hb hu hue hvv hw,
    lift_map₂_eq M (splitW hu hue hvv a ha).hom φ,
    lift_map₂_eq M (splitW hu hue hvv b hb).inv ψ]
  rfl

end Categorification.Diagrams.BicatInterp