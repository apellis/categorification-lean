/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.LayerMap.Local
import StringDiagrams.Generation
import StringDiagrams.Monoidal

/-!
# Composites of functors given by images of generators

Two functors of a presented category given by images of generators (`LocalMap.liftGen`)
compose to a functor isomorphic to the identity, with `eqToHom` components, as soon as the
composite relabelling of regions and strands is the identity and the composite image of every
generator is that generator (`isoIdOfLiftGenComp`). This is the mechanism behind the inverse of
the weight shift of `U′` (Webster arXiv:1309.3796v2, Proposition 3.30).

* `FixedBy`, `fixedBy_of_layers`, `isoIdOfLayers`: a linear endofunctor fixing every layer is
  isomorphic to the identity.
* `fixedBy_liftGen_comp_layer`: the layer condition for a composite of two `liftGen` functors.
-/


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams Presentation
universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R] {P : Presentation.{w, v} S R}

/-- `K` fixes `f`, up to the given identifications `K (P.obj a) = P.obj a` of objects. -/
def FixedBy (K : P.Presented ⥤ P.Presented) (hK : ∀ a, K.obj (P.obj a) = P.obj a)
    {a b : Obj S} (f : P.obj a ⟶ P.obj b) : Prop :=
  K.map f ≫ eqToHom (hK b) = eqToHom (hK a) ≫ f

/-- A linear endofunctor fixing every layer fixes every morphism. -/
theorem fixedBy_of_layers (K : P.Presented ⥤ P.Presented) [K.Additive] [K.Linear R]
    (hK : ∀ a, K.obj (P.obj a) = P.obj a)
    (hlayer : ∀ (L : Layer S) (hv : L.Valid), FixedBy K hK (P.diag (Diagram.ofLayer L hv)))
    {a b : Obj S} (f : P.obj a ⟶ P.obj b) : FixedBy K hK f := by
  induction f using P.hom_induction_layers with
  | nil h =>
    rename_i a b
    subst h
    simp [FixedBy]
  | layer L hv => exact hlayer L hv
  | comp f g hf hg =>
    unfold FixedBy at *
    rw [K.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
  | zero => simp [FixedBy]
  | add f g hf hg =>
    unfold FixedBy at *
    rw [K.map_add, Preadditive.add_comp, hf, hg, Preadditive.comp_add]
  | smul r f hf =>
    unfold FixedBy at *
    rw [K.map_smul, Linear.smul_comp, hf, Linear.comp_smul]

/-- A linear endofunctor of a presented category fixing every layer, up to identifications of
objects, is isomorphic to the identity, with `eqToHom` components. -/
def isoIdOfLayers (K : P.Presented ⥤ P.Presented) [K.Additive] [K.Linear R]
    (hK : ∀ a, K.obj (P.obj a) = P.obj a)
    (hlayer : ∀ (L : Layer S) (hv : L.Valid), FixedBy K hK (P.diag (Diagram.ofLayer L hv))) :
    K ≅ 𝟭 P.Presented :=
  NatIso.ofComponents (fun X => eqToIso (hK X.as))
    (fun {X Y} f => fixedBy_of_layers K hK hlayer (a := X.as) (b := Y.as) f)

/-- Whiskering commutes with retyping along equalities of objects. -/
theorem whisk_eqToHom_conj {a a' b b' : Obj S} (ha : a' = a) (hb : b' = b) (f : P.obj a ⟶ P.obj b)
    {u u' : Obj S} {v v' : List S.Colour} (hu : u' = u) (hv : v' = v) :
    P.whisk (eqToHom (congrArg P.obj ha) ≫ f ≫ eqToHom (congrArg P.obj hb.symm)) u' v' =
      eqToHom (by rw [ha, hu, hv]) ≫ P.whisk f u v ≫ eqToHom (by rw [hb, hu, hv]) := by
  subst ha hb hu hv
  simp

/-- The single layer consisting of the generator `g` alone. -/
def bareLayer (g : S.Gen) : Layer S := ⟨S.left g, [], g, []⟩

/-- The bare layer of the generator of a valid layer is valid. -/
theorem bareLayer_valid {L : Layer S} (hv : L.Valid) : (bareLayer L.gen).Valid where
  left_ok := Signature.ok_nil _
  left_end := rfl
  dom_ok := hv.dom_ok
  dom_end := hv.dom_end
  cod_ok := hv.cod_ok
  cod_end := hv.cod_end
  right_ok := Signature.ok_nil _

section LiftGen

variable (κ κ' : ColourMap S S)
  (img : (g : S.Gen) → (P.obj (LocalMap.genDom κ g) ⟶ P.obj (LocalMap.genCod κ g)))
  (himg : ∀ g, img g ∈ P.homDeg (Presentation.parityDeg S) (LocalMap.genDom κ g)
    (LocalMap.genCod κ g) (Presentation.parityDeg S g))
  (hrel : ∀ r, (freeLift R (LocalMap.ofGen κ img).functor).map (P.rel r) = 0)
  (img' : (g : S.Gen) → (P.obj (LocalMap.genDom κ' g) ⟶ P.obj (LocalMap.genCod κ' g)))
  (himg' : ∀ g, img' g ∈ P.homDeg (Presentation.parityDeg S) (LocalMap.genDom κ' g)
    (LocalMap.genCod κ' g) (Presentation.parityDeg S g))
  (hrel' : ∀ r, (freeLift R (LocalMap.ofGen κ' img').functor).map (P.rel r) = 0)
  (hobj : ∀ a, κ'.obj (κ.obj a) = a)

  (hword : ∀ w, κ'.word (κ.word w) = w)

include hobj in
/-- The composite relabelling of the source of a generator. -/
theorem genDom_comp (g : S.Gen) : κ'.obj (LocalMap.genDom κ g) = (bareLayer g).dom := by
  rw [LocalMap.genDom, hobj]
  simp [bareLayer, Layer.dom]

include hobj in
/-- The composite relabelling of the target of a generator. -/
theorem genCod_comp (g : S.Gen) : κ'.obj (LocalMap.genCod κ g) = (bareLayer g).cod := by
  rw [LocalMap.genCod, hobj]
  simp [bareLayer, Layer.cod]

include hword in
/-- The composite of two functors given by images of generators fixes every layer, when the
composite relabelling is the identity and the composite image of each generator is the
generator itself. -/
theorem fixedBy_liftGen_comp_layer
    (hne : ∀ g, (bareLayer g).Valid → Nonempty (LocalMap.genDom κ g ⟶ LocalMap.genCod κ g))
    (hgen : ∀ g (hb : (bareLayer g).Valid),
      (LocalMap.liftGen κ' img' P himg' hrel').map (img g) =
        eqToHom (congrArg P.obj (genDom_comp κ κ' hobj g)) ≫
          P.diag (Diagram.ofLayer (bareLayer g) hb) ≫
            eqToHom (congrArg P.obj (genCod_comp κ κ' hobj g).symm))
    (L : Layer S) (hv : L.Valid) :
    FixedBy (LocalMap.liftGen κ img P himg hrel ⋙ LocalMap.liftGen κ' img' P himg' hrel')
      (fun a => congrArg P.obj (hobj a)) (P.diag (Diagram.ofLayer L hv)) := by
  have hb := bareLayer_valid hv
  have hw : (bareLayer L.gen).dom.WhiskerOK ⟨L.start, L.left⟩ L.right :=
    ⟨hv.left_ok, hv.left_end, by
      show S.ok (S.endR (S.left L.gen) ([] ++ S.dom L.gen ++ [])) L.right
      simp only [List.nil_append, List.append_nil, hv.dom_end]
      exact hv.right_ok⟩
  have e1 : (κ'.obj (LocalMap.genDom κ L.gen)).whisker (κ'.obj (κ.obj ⟨L.start, L.left⟩))
      (κ'.word (κ.word L.right)) = L.dom := by
    rw [genDom_comp κ κ' hobj, hobj, hword]
    simp [bareLayer, Layer.dom, Obj.whisker]
  have e2 : (κ'.obj (LocalMap.genCod κ L.gen)).whisker (κ'.obj (κ.obj ⟨L.start, L.left⟩))
      (κ'.word (κ.word L.right)) = L.cod := by
    rw [genCod_comp κ κ' hobj, hobj, hword]
    simp [bareLayer, Layer.cod, Obj.whisker]
  have hW : P.whisk (a := κ'.obj (LocalMap.genDom κ L.gen))
      (b := κ'.obj (LocalMap.genCod κ L.gen))
      ((LocalMap.liftGen κ' img' P himg' hrel').map (img L.gen))
      (κ'.obj (κ.obj ⟨L.start, L.left⟩)) (κ'.word (κ.word L.right)) =
      eqToHom (congrArg P.obj e1) ≫ P.diag (Diagram.ofLayer L hv) ≫
        eqToHom (congrArg P.obj e2.symm) := by
    rw [hgen L.gen hb, whisk_eqToHom_conj (genDom_comp κ κ' hobj L.gen)
      (genCod_comp κ κ' hobj L.gen) _ (hobj ⟨L.start, L.left⟩) (hword L.right),
      whisk_diag _ _ _ _ hw,
      P.diag_eq_of_layers_eq' (Diagram.whisker _ _ _ hw) (Diagram.ofLayer L hv)
        (by simp [bareLayer, Layer.dom, Obj.whisker]) (by simp [bareLayer, Layer.cod, Obj.whisker])
        (by simp [bareLayer, Layer.whisker])]
    simp
  unfold FixedBy
  rw [Functor.comp_map, LocalMap.liftGen_layer, Functor.map_comp, Functor.map_comp, eqToHom_map,
    eqToHom_map, LocalMap.liftGen_whisk κ' img' himg' hrel' (img L.gen)
      (LocalMap.genDom_whiskerOK κ hv) (hne L.gen hb), hW]
  simp

include hword in
/-- **Composites of functors given by images of generators.** If the composite relabelling is
the identity and the composite image of every generator is that generator, the composite of the
two functors is isomorphic to the identity, with `eqToHom` components. -/
def isoIdOfLiftGenComp
    (hne : ∀ g, (bareLayer g).Valid → Nonempty (LocalMap.genDom κ g ⟶ LocalMap.genCod κ g))
    (hgen : ∀ g (hb : (bareLayer g).Valid),
      (LocalMap.liftGen κ' img' P himg' hrel').map (img g) =
        eqToHom (congrArg P.obj (genDom_comp κ κ' hobj g)) ≫
          P.diag (Diagram.ofLayer (bareLayer g) hb) ≫
            eqToHom (congrArg P.obj (genCod_comp κ κ' hobj g).symm)) :
    LocalMap.liftGen κ img P himg hrel ⋙ LocalMap.liftGen κ' img' P himg' hrel' ≅
      𝟭 P.Presented :=
  isoIdOfLayers _ (fun a => congrArg P.obj (hobj a))
    (fixedBy_liftGen_comp_layer κ κ' img himg hrel img' himg' hrel' hobj hword hne hgen)

theorem isoIdOfLiftGenComp_hom_app (hne hgen) (a : Obj S) :
    (isoIdOfLiftGenComp κ κ' img himg hrel img' himg' hrel' hobj hword hne hgen).hom.app
      (P.obj a) = eqToHom (congrArg P.obj (hobj a)) := rfl

end LiftGen

end Categorification.KL3.Diagram
