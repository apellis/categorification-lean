/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissible
import Categorification.Diagrams.BicatInterpPull

/-!
# Pulling back admissible interpretations

The admissible interpretation (`admissibleInterp`, `admissibleMap`) of the pullback
`G'.pull φ` of generator images along a map of signatures `φ` is the admissible
interpretation of the relabelled diagrams for `G'`, up to the identifications of the
images of the boundary words (`admissibleMap_pull`). Unlike `freeLift_pull`, this needs
no zero objects in the target Hom categories, so it applies to `TwoRep.LinearCat`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ u₀ u₁ u₂ u₀' u₁' u₂' v₂

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}}
  {C : Type w₁} [Bicategory.{w₂, v₂} C] {M' : Model S' C} (φ : SigMap S S') (G' : GenImg M')

/-- The image of an admissible word for the pullback is the image of its relabelling. -/
theorem word_pull {s t : S.Region} {a : Obj S} (h : Cond s t a)
    (h' : Cond (φ.region s) (φ.region t) (φ.obj a)) :
    (M'.pull φ.toColourMap).word s a.word t h.1 h.2.1 =
      M'.word (φ.region s) (φ.obj a).word (φ.region t) h'.1 h'.2.1 :=
  pull_word' M' φ.toColourMap s a.word t _ _ _ (φ.word_eq _) _ _

/-- **The image of a layer for the pullback**, on admissible words. -/
theorem coreC_pull {s t : S.Region} {L : Layer S} (hv : L.Valid) (h : Cond s t L.dom)
    (h' : Cond (φ.region s) (φ.region t) (φ.layer L).dom) :
    coreC (G'.pull φ) hv h =
      eqToHom (word_pull φ h (Cond.map φ h)) ≫
        eqToHom (admissibleWord_eq (M := M') (φ.toLayerMap.dom_eq hv).symm
          (Cond.map φ h) h') ≫
        coreC G' (φ.layer_valid hv) h' ≫
        eqToHom (admissibleWord_eq (M := M') (φ.toLayerMap.cod_eq hv)
          (h'.cod (φ.layer_valid hv)) (Cond.map φ (h.cod hv))) ≫
        eqToHom (word_pull φ (h.cod hv) (Cond.map φ (h.cod hv))).symm := by
  rw [coreC_eq, coreC_eq, core_pull φ G' hv,
    core_regions G' (φ.layer_valid hv) (φ.region s) (S'.left (φ.layer L).gen)
      (S'.right (φ.layer L).gen) (φ.region (S.left L.gen)) (φ.region (S.right L.gen))]
  · simp only [eqToHom_trans_assoc, eqToHom_trans]
  · exact (φ.endR_map _ _).trans (congrArg φ.region (h.left_end hv))
  · exact φ.left _
  · exact φ.right _
  · exact (φ.endR_map _ _).trans (congrArg φ.region (h.right_end hv))

omit φ G' in
/-- Changing the source of an admissible chain along an equality. -/
theorem admissibleChain_src {M : Model S C} (G : GenImg M) {s t : S.Region} {a a' b : Obj S}
    (e : a = a') {ls : List (Layer S)} (h : Chain a ls b) (h' : Chain a' ls b)
    (ha : Cond s t a) (ha' : Cond s t a') (hb : Cond s t b) :
    admissibleChain G a ls b h ha hb =
      eqToHom (admissibleWord_eq e ha ha') ≫ admissibleChain G a' ls b h' ha' hb := by
  subst e
  simp

/-- **The images of admissible chains for the pullback** are the images of the relabelled
chains. -/
theorem admissibleChain_pull {s t : S.Region} : ∀ (ls : List (Layer S)) (a b : Obj S)
    (hc : Chain a ls b) (ha : Cond s t a) (hb : Cond s t b),
    admissibleChain (G'.pull φ) a ls b hc ha hb =
      eqToHom (word_pull φ ha (Cond.map φ ha)) ≫
        admissibleChain G' (φ.obj a) (ls.map φ.layer) (φ.obj b) (φ.toLayerMap.chain hc)
          (Cond.map φ ha) (Cond.map φ hb) ≫
        eqToHom (word_pull φ hb (Cond.map φ hb)).symm
  | [], a, b, hc, ha, hb => by
    obtain rfl : a = b := hc
    simp [admissibleChain]
  | L :: ls, a, b, hc, ha, hb => by
    obtain ⟨hv, rfl, hc'⟩ := hc
    have h' : Cond (φ.region s) (φ.region t) (φ.layer L).dom :=
      (φ.toLayerMap.dom_eq hv).symm ▸ Cond.map φ ha
    simp only [List.map_cons, admissibleChain]
    rw [coreC_pull φ G' hv _ h', admissibleChain_pull ls L.cod b hc' _ hb]
    simp only [eqToHom_refl, Category.id_comp, Category.assoc, eqToHom_trans_assoc]
    erw [admissibleChain_src G' (φ.toLayerMap.cod_eq hv) (h' := φ.toLayerMap.chain hc')
      (ha' := Cond.map φ (ha.cod hv))]
    simp only [Category.assoc]
    rfl

/-- **The admissible interpretation of the pullback** of a diagram is that of its relabelling. -/
theorem admissibleInterp_pull {s t : S.Region} {a b : Obj S} (d : a ⟶ b) (ha : Cond s t a)
    (hb : Cond s t b) :
    (admissibleInterp (G'.pull φ) s t).map
        (ObjectProperty.homMk (X := ⟨a, ha⟩) (Y := ⟨b, hb⟩) d) =
      eqToHom (word_pull φ ha (Cond.map φ ha)) ≫
        (admissibleInterp G' (φ.region s) (φ.region t)).map
          (ObjectProperty.homMk (X := ⟨φ.obj a, Cond.map φ ha⟩)
            (Y := ⟨φ.obj b, Cond.map φ hb⟩) (φ.toLayerMap.map d)) ≫
        eqToHom (word_pull φ hb (Cond.map φ hb)).symm :=
  admissibleChain_pull φ G' _ a b _ ha hb

section Linear

variable {R : Type*} [CommRing R] [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]

/-- **The linear admissible interpretation of the pullback**: the image of a relabelled linear
combination of diagrams is the image of the original one for the pullback, transported along
the identifications of the boundary words. -/
theorem admissibleMap_pull {s t : S.Region} {a b : Obj S} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram R a b) :
    admissibleMap G' (Cond.map φ ha) (Cond.map φ hb) (φ.toLayerMap.lin f) =
      eqToHom (word_pull φ ha (Cond.map φ ha)).symm ≫ admissibleMap (G'.pull φ) ha hb f ≫
        eqToHom (word_pull φ hb (Cond.map φ hb)) := by
  induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := R)) with
  | zero =>
    change admissibleMap G' _ _ (Finsupp.mapDomain _ 0) = _
    rw [Finsupp.mapDomain_zero, map_zero, map_zero]
    simp
  | add f g hf hg =>
    erw [LayerMap.lin_add, map_add, hf, hg, map_add]
    simp
  | single d r =>
    change admissibleMap G' _ _ (Finsupp.mapDomain _ (Finsupp.single d r)) = _
    rw [Finsupp.mapDomain_single]
    dsimp only [admissibleMap]
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
    rw [admissibleInterp_pull φ G' d ha hb]
    simp

/-- A linear combination killed by the admissible interpretation of the pullback has its
relabelling killed by the original admissible interpretation. -/
theorem admissibleMap_pull_eq_zero {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (f : LinDiagram R a b) (hf : admissibleMap (G'.pull φ) ha hb f = 0) :
    admissibleMap G' (Cond.map φ ha) (Cond.map φ hb) (φ.toLayerMap.lin f) = 0 := by
  rw [admissibleMap_pull φ G' ha hb f, hf]
  simp

end Linear

end Categorification.Diagrams.BicatInterp
