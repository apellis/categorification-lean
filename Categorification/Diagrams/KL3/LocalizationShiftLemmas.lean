/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Biadjunction.Zigzag
import StringDiagrams.LayerMap.Local

/-!
# Generic lemmas on whiskering and on functors given by images of generators

Supporting lemmas for the weight shifts of the localization `U′` (Webster,
arXiv:1309.3796v2, Proposition 3.30; `Categorification.Diagrams.KL3.LocalizationShift`).

* `Presentation.whisk_nil_nil`: whiskering by the empty words on both sides is the identity,
  up to the identifications of the boundaries.
* `LocalMap.functor_map_single`: the image of a one-layer diagram under the functor of a local
  map given by images of generators, when the layer has no strands on either side.
* `functor_map_eq_of_layer'`, `freeLift_map_eq_of_layer'`: two functors out of the free
  2-category that agree on layers (up to identifications of the boundaries of well-formed
  objects) agree on all diagrams and on all linear combinations of diagrams.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

namespace Presentation

variable (Q : Presentation.{w, v} S R)

theorem whisker_nil_nil_obj (a : Obj S) (r : S.Region) (ha : a.start = r) :
    a.whisker (Obj.nil r) [] = a :=
  Obj.ext ha.symm (by simp [Obj.whisker])

theorem whisker_nil_nil_obj' (a u : Obj S) (v : List S.Colour) (hu : u.word = []) (hv : v = [])
    (ha : a.start = u.start) : a.whisker u v = a :=
  Obj.ext ha.symm (by simp [Obj.whisker, hu, hv])

/-- Whiskering by the empty words is the identity, up to the identifications of the
boundaries. -/
theorem whisk_nil_nil {a b : Obj S} (f : Q.obj a ⟶ Q.obj b) (r : S.Region) (ha : a.start = r)
    (hb : b.start = r) :
    Q.whisk f (Obj.nil r) [] =
      eqToHom (congrArg Q.obj (whisker_nil_nil_obj a r ha)) ≫ f ≫
        eqToHom (congrArg Q.obj (whisker_nil_nil_obj b r hb)).symm := by
  subst ha
  obtain ⟨g, rfl⟩ := Q.lin_surjective f
  have hw : a.WhiskerOK (Obj.nil a.start) [] := ⟨trivial, rfl, trivial⟩
  have ha' : a = a.whisker (Obj.nil a.start) [] := (whisker_nil_nil_obj a _ rfl).symm
  have hb' : b = b.whisker (Obj.nil a.start) [] := (whisker_nil_nil_obj b _ hb).symm
  have e : LinDiagram.whisker g (Obj.nil a.start) [] hw = LinDiagram.cast g ha' hb' := by
    unfold LinDiagram.whisker LinDiagram.cast
    congr 1
    funext d'
    exact Diagram.whisker_nil_start_eq_cast d' hw ha' hb'
  rw [whisk_lin, LinDiagram.whisk_of_ok _ hw, e, lin_cast]

/-- Whiskering by words without strands is the identity, up to the identifications of the
boundaries. -/
theorem whisk_empty {a b : Obj S} (f : Q.obj a ⟶ Q.obj b) (u : Obj S) (v : List S.Colour)
    (hu : u.word = []) (hv : v = []) (ha : a.start = u.start) (hb : b.start = u.start)
    (e₁ : a.whisker u v = a) (e₂ : b.whisker u v = b) :
    Q.whisk f u v = eqToHom (congrArg Q.obj e₁) ≫ f ≫ eqToHom (congrArg Q.obj e₂).symm := by
  obtain ⟨r, w⟩ := u
  dsimp only at hu ha hb
  subst hu hv
  exact whisk_nil_nil Q f r ha hb

end Presentation

namespace LocalMap

variable {S' : Signature.{u₀, u₁, u₂}} {Q : Presentation.{w, v} S' R} (κ : ColourMap S S')
  (img : (g : S.Gen) → (Q.obj (genDom κ g) ⟶ Q.obj (genCod κ g)))

/-- The image of a one-layer diagram whose layer has no strands on either side: the image of
its generator, up to the identifications of the boundaries. -/
theorem functor_map_single {a b : Obj S} (L : Layer S) (h : Chain a [L] b) (hl : L.left = [])
    (hr : L.right = []) (e₁ : κ.obj a = genDom κ L.gen) (e₂ : κ.obj b = genCod κ L.gen) :
    (ofGen κ img).functor.map (Diagram.mk [L] h) =
      eqToHom (congrArg Q.obj e₁) ≫ img L.gen ≫ eqToHom (congrArg Q.obj e₂).symm := by
  obtain ⟨s, l, g, r⟩ := L
  dsimp only at hl hr
  subst hl hr
  have hv := h.1
  have hs : κ.region s = κ.region (S.left g) := congrArg κ.region hv.left_end
  refine ((ofGen κ img).toInterpretation.functor_map_mk_cons _ _ h).trans ?_
  rw [Interpretation.functor_map_mk_nil, toInterpretation_layer, ofGen_layer,
    Q.whisk_empty _ _ _ (κ.word_nil) (κ.word_nil) hs.symm hs.symm
      (Presentation.whisker_nil_nil_obj' _ _ _ κ.word_nil κ.word_nil hs.symm)
      (Presentation.whisker_nil_nil_obj' _ _ _ κ.word_nil κ.word_nil hs.symm)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- The image of a layer whose generator is sent to a diagram, up to the identifications of the
boundaries: it is the diagram whose layers are those of the image whiskered by the relabelled
strands on either side. -/
theorem ofGen_layer_eq_diag (L : Layer S) (hv : L.Valid) {c d : Obj S'} (D₀ : c ⟶ d)
    (h₁ : genDom κ L.gen = c) (h₂ : genCod κ L.gen = d)
    (himg : img L.gen = eqToHom (congrArg Q.obj h₁) ≫ Q.diag D₀ ≫ eqToHom (congrArg Q.obj h₂).symm)
    (D : κ.obj L.dom ⟶ κ.obj L.cod)
    (hD : Diagram.layers D =
      (Diagram.layers D₀).map (·.whisker (κ.obj ⟨L.start, L.left⟩) (κ.word L.right))) :
    (ofGen κ img).layer L hv = Q.diag D := by
  subst h₁ h₂
  rw [ofGen_layer, himg]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Q.whisk_diag _ _ _ (genDom_whiskerOK κ hv),
    Q.diag_eq_of_layers_eq' (Diagram.whisker D₀ _ _ (genDom_whiskerOK κ hv)) D
      (whisker_genDom κ L) (whisker_genCod κ L) hD.symm]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- The image of a layer whose generator is sent to a one-layer diagram: the one-layer diagram
of the whiskered layer. -/
theorem ofGen_layer_eq_single (L : Layer S) (hv : L.Valid) {c d : Obj S'} (D₀ : c ⟶ d)
    (h₁ : genDom κ L.gen = c) (h₂ : genCod κ L.gen = d)
    (himg : img L.gen = eqToHom (congrArg Q.obj h₁) ≫ Q.diag D₀ ≫ eqToHom (congrArg Q.obj h₂).symm)
    (L' : Layer S')
    (hL : (Diagram.layers D₀).map (·.whisker (κ.obj ⟨L.start, L.left⟩) (κ.word L.right)) = [L']) :
    ∃ (hv' : L'.Valid) (e₁ : L'.dom = κ.obj L.dom) (e₂ : L'.cod = κ.obj L.cod),
      (ofGen κ img).layer L hv = Q.diag (Diagram.layer L' hv' e₁ e₂) := by
  subst h₁ h₂
  have hch := Diagram.chain (Diagram.whisker D₀ _ _ (genDom_whiskerOK κ hv))
  rw [Diagram.layers_whisker, hL, whisker_genDom, whisker_genCod] at hch
  obtain ⟨hv', e₁, e₂⟩ := hch
  exact ⟨hv', e₁, e₂, ofGen_layer_eq_diag κ img L hv D₀ rfl rfl himg _ (by rw [hL]; rfl)⟩

end LocalMap

namespace LocalMap

variable {S' : Signature.{u₀, u₁, u₂}} {Q : Presentation.{w, v} S' R}

/-- A local map that sends each layer of a list to the diagram of one layer (given by a function
`σ` on layers) sends the diagram with these layers to the diagram with the image layers. -/
theorem functor_map_mk_eq_diag (φ : LocalMap S Q) (σ : Layer S → Layer S') :
    ∀ (ls : List (Layer S))
      (_ : ∀ L ∈ ls, ∀ (hv : L.Valid), ∃ (hv' : (σ L).Valid) (e₁ : (σ L).dom = φ.obj L.dom)
        (e₂ : (σ L).cod = φ.obj L.cod), φ.layer L hv = Q.diag (Diagram.layer (σ L) hv' e₁ e₂))
      {a b : Obj S} (hc : Chain a ls b) (hc' : Chain (φ.obj a) (ls.map σ) (φ.obj b)),
      φ.functor.map (Diagram.mk ls hc) = Q.diag (Diagram.mk (ls.map σ) hc')
  | [], _, a, b, hc, hc' => by
    cases hc
    rw [show Diagram.mk [] (rfl : Chain a [] a) = 𝟙 a from rfl, CategoryTheory.Functor.map_id,
      show Diagram.mk (([] : List (Layer S)).map σ) hc' = 𝟙 _ from rfl, Q.diag_id]
    rfl
  | L :: ls, hσ, a, b, hc, hc' => by
    obtain ⟨hv, rfl, hc₂⟩ := hc
    obtain ⟨hv', e₁, e₂, hL⟩ := hσ L List.mem_cons_self hv
    have hc₂' : Chain (φ.obj L.cod) (ls.map σ) (φ.obj b) := by
      have := hc'.2.2
      rwa [e₂] at this
    have ih := functor_map_mk_eq_diag φ σ ls (fun L' h => hσ L' (List.mem_cons_of_mem _ h)) hc₂ hc₂'
    refine (φ.toInterpretation.functor_map_mk_cons _ _ ⟨hv, rfl, hc₂⟩).trans ?_
    have e : Diagram.mk ((L :: ls).map σ) hc' = Diagram.layer (σ L) hv' e₁ e₂ ≫
        Diagram.mk (ls.map σ) hc₂' := Diagram.ext rfl
    rw [e, Q.diag_comp, ← hL, ← ih]
    simp only [eqToHom_refl, Category.id_comp]
    rfl

end LocalMap

end StringDiagrams
