/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterp
import StringDiagrams.LayerMap.Generators
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Pulling a model back along a map of signatures

For a map of signatures `φ : S → S'` (`StringDiagrams.SigMap`) and a model `M'` of `S'` in a
bicategory `C` with generator images `G'` (`Categorification.Diagrams.BicatInterp`), the
*pullback* `M'.pull φ` is the model of `S` sending a region `x` to `M'.obj (φ x)` and a strand `c`
to the image of `φ c`, and `G'.pull φ` sends a generator `g` to the image of `φ g`. The
interpretation of a diagram `d` of `S` for the pullback is the interpretation of its relabelling
`φ d` for `M'`, up to the identifications of the images of the boundary words (`interp_pull`).

This is used to restrict the model of `U(g)` given by a `Q`-strong 2-representation to an
`α_i`-string, where it becomes the `sl₂` model (`Categorification.TwoRep.ModelSl2`).

## Main definitions and results

* `rqMap`, `fbMap`: the induced prefunctor of region quivers and pseudofunctor of free
  bicategories;
* `Model.pull`, `GenImg.pull`;
* `pull_lift_map`, `pull_lift_map₂`: the pseudofunctor of the pullback is the composite of `fbMap`
  and the pseudofunctor of `M'`;
* `fbMap_fw`: `fbMap` sends the free 1-morphism of a word to that of the relabelled word;
* `interp_pull`: the comparison of interpretations.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ u₀ u₁ u₂ u₀' u₁' u₂' v₂

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}}

/-! ## Free bicategories -/

/-- The prefunctor from the quiver of regions of `S` to the free bicategory of `S'` induced by a
relabelling of regions and strands. -/
def rqMap (κ : ColourMap S S') : Prefunctor (RQ S) (FB S') where
  obj := κ.region
  map {_ _} c := FreeBicategory.Hom.of
    (show rq (κ.region _) ⟶ rq (κ.region _) from
      ⟨κ.colour c.1, by rw [κ.colourTgt, c.2.1], by rw [κ.colourSrc, c.2.2]⟩)

/-- The pseudofunctor of free bicategories induced by a relabelling. -/
abbrev fbMap (κ : ColourMap S S') : FB S ⥤ᵖ FB S' := FreeBicategory.lift (rqMap κ)

theorem fw_comp_of_congr {p q : S'.Region} (e : p = q) (w : List S'.Colour) (t s : S'.Region)
    (c : S'.Colour) (h₁ : S'.ok p w) (e₁ : S'.endR p w = t) (h₂ : S'.ok q w)
    (e₂ : S'.endR q w = t) (k₁ : S'.colourTgt c = p) (k₂ : S'.colourSrc c = s)
    (k₁' : S'.colourTgt c = q) (k₂' : S'.colourSrc c = s) :
    fw p w t h₁ e₁ ≫ FreeBicategory.Hom.of (show rq p ⟶ rq s from ⟨c, k₁, k₂⟩) =
      fw q w t h₂ e₂ ≫ FreeBicategory.Hom.of (show rq q ⟶ rq s from ⟨c, k₁', k₂'⟩) := by
  subst e; rfl

theorem ok_map' (κ : ColourMap S S') {r : S.Region} {w : List S.Colour} (h : S.ok r w) :
    S'.ok (κ.region r) (w.map κ.colour) := by
  rw [← κ.word_eq]; exact κ.ok_map h

theorem endR_map' (κ : ColourMap S S') (r : S.Region) (w : List S.Colour) :
    S'.endR (κ.region r) (w.map κ.colour) = κ.region (S.endR r w) := by
  rw [← κ.word_eq]; exact κ.endR_map r w

theorem fbMap_comp (κ : ColourMap S S') {a b c : FB S} (f : a ⟶ b) (g : b ⟶ c) :
    (fbMap κ).map (f ≫ g) = (fbMap κ).map f ≫ (fbMap κ).map g := rfl

/-- **`fbMap` on words**: the free 1-morphism of a word goes to that of the relabelled word. -/
theorem fbMap_fw (κ : ColourMap S S') : ∀ (w : List S.Colour) (s t : S.Region) (h : S.ok s w)
    (e : S.endR s w = t) (h' : S'.ok (κ.region s) (w.map κ.colour))
    (e' : S'.endR (κ.region s) (w.map κ.colour) = κ.region t),
    (fbMap κ).map (fw s w t h e) = fw (κ.region s) (w.map κ.colour) (κ.region t) h' e'
  | [], s, t, h, e, h', e' => by subst e; rfl
  | [c], s, t, h, e, h', e' => rfl
  | c :: c' :: w, s, t, h, e, h', e' => by
    have hr : fw (κ.region s) ((c :: c' :: w).map κ.colour) (κ.region t) h' e' =
        fw (S'.colourTgt (κ.colour c)) (κ.colour c' :: w.map κ.colour) (κ.region t) h'.2 e' ≫
          FreeBicategory.Hom.of ⟨κ.colour c, rfl, h'.1⟩ := rfl
    rw [fw_cons₂, hr]
    change (fbMap κ).map (fw (S.colourTgt c) (c' :: w) t h.2 e) ≫ _ = _
    rw [fbMap_fw κ (c' :: w) (S.colourTgt c) t h.2 e (ok_map' κ h.2)
      ((endR_map' κ _ _).trans (congrArg κ.region e))]
    refine fw_comp_of_congr (κ.colourTgt c).symm _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals first
      | exact κ.colourTgt c
      | rfl
      | exact h'.1


/-! ## The pullback of a model -/

section Pull

variable {C : Type w₁} [Bicategory.{w₂, v₂} C]

/-- **The pullback of a model** along a relabelling: the region `x` goes to `M'.obj (κ x)` and the
strand `c` to the image of `κ c`. -/
def Model.pull (M' : Model S' C) (κ : ColourMap S S') : Model S C where
  obj x := M'.obj (κ.region x)
  strandAt c x y hx hy := M'.strandAt (κ.colour c) (κ.region x) (κ.region y)
    (by rw [κ.colourTgt, hx]) (by rw [κ.colourSrc, hy])

variable (M' : Model S' C) (κ : ColourMap S S')

/-- The pseudofunctor of the pullback on 1-morphisms: `fbMap` followed by that of `M'`. -/
theorem pull_lift_map {a b : FB S} (f : a ⟶ b) :
    (M'.pull κ).lift.map f = M'.lift.map ((fbMap κ).map f) := by
  induction f with
  | of f => rfl
  | id a => rfl
  | comp f g ihf ihg =>
    exact congrArg₂ (· ≫ ·) ihf ihg

omit [Bicategory C] in
theorem eqToHom_conj_assoc {D : Type*} [Category D] {X X' Y Y' Z Z' : D} (p : X = X')
    (q : Y = Y') (r : Z = Z') (f : X' ⟶ Y') (g : Y' ⟶ Z') (fg : X' ⟶ Z') (hfg : f ≫ g = fg) :
    (eqToHom p ≫ f ≫ eqToHom q.symm) ≫ (eqToHom q ≫ g ≫ eqToHom r.symm) =
      eqToHom p ≫ fg ≫ eqToHom r.symm := by
  subst p q r hfg; simp

omit [Bicategory C] in
theorem id_conj {D : Type*} [Category D] {X X' : D} (e : X = X') (w : X' ⟶ X')
    (hw : 𝟙 X' = w) : 𝟙 X = eqToHom e ≫ w ≫ eqToHom e.symm := by
  subst e hw; simp

theorem whiskerLeft_conj {a b c : C} {f f' : a ⟶ b} {g g' h h' : b ⟶ c} (ef : f = f')
    (eg : g = g') (eh : h = h') (η : g' ⟶ h') (θ : f' ≫ g' ⟶ f' ≫ h') (hθ : f' ◁ η = θ) :
    f ◁ (eqToHom eg ≫ η ≫ eqToHom eh.symm) =
      eqToHom (by rw [ef, eg]) ≫ θ ≫ eqToHom (by rw [ef, eh]) := by
  subst ef eg eh hθ; simp

theorem whiskerRight_conj {a b c : C} {f f' g g' : a ⟶ b} {h h' : b ⟶ c} (ef : f = f')
    (eg : g = g') (eh : h = h') (η : f' ⟶ g') (θ : f' ≫ h' ⟶ g' ≫ h') (hθ : η ▷ h' = θ) :
    (eqToHom ef ≫ η ≫ eqToHom eg.symm) ▷ h =
      eqToHom (by rw [ef, eh]) ≫ θ ≫ eqToHom (by rw [eg, eh]) := by
  subst ef eg eh hθ; simp

theorem associator_conj {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).hom = eqToHom (by rw [ef, eg, eh]) ≫ (α_ f' g' h').hom ≫
      eqToHom (by rw [ef, eg, eh]) := by
  subst ef eg eh; simp

theorem associator_inv_conj {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).inv = eqToHom (by rw [ef, eg, eh]) ≫ (α_ f' g' h').inv ≫
      eqToHom (by rw [ef, eg, eh]) := by
  subst ef eg eh; simp

theorem leftUnitor_conj {a b : C} {f f' : a ⟶ b} (ef : f = f') :
    (λ_ f).hom = eqToHom (by rw [ef]) ≫ (λ_ f').hom ≫ eqToHom ef.symm := by
  subst ef; simp

theorem leftUnitor_inv_conj {a b : C} {f f' : a ⟶ b} (ef : f = f') :
    (λ_ f).inv = eqToHom ef ≫ (λ_ f').inv ≫ eqToHom (by rw [ef]) := by
  subst ef; simp

theorem rightUnitor_conj {a b : C} {f f' : a ⟶ b} (ef : f = f') :
    (ρ_ f).hom = eqToHom (by rw [ef]) ≫ (ρ_ f').hom ≫ eqToHom ef.symm := by
  subst ef; simp

theorem rightUnitor_inv_conj {a b : C} {f f' : a ⟶ b} (ef : f = f') :
    (ρ_ f).inv = eqToHom ef ≫ (ρ_ f').inv ≫ eqToHom (by rw [ef]) := by
  subst ef; simp

/-- The pseudofunctor of the pullback on 2-morphisms: `fbMap` followed by that of `M'`, up to
the identifications `pull_lift_map`. -/
theorem pull_lift_map₂ {a b : FB S} {f g : a ⟶ b} (η : f ⟶ g) :
    (M'.pull κ).lift.map₂ η = eqToHom (pull_lift_map M' κ f) ≫
      M'.lift.map₂ ((fbMap κ).map₂ η) ≫ eqToHom (pull_lift_map M' κ g).symm := by
  induction η using Quot.ind with
  | mk η =>
  induction η with
  | id f =>
    exact id_conj (pull_lift_map M' κ f) _ (PrelaxFunctor.map₂_id _ _).symm
  | vcomp η θ ihη ihθ =>
    show (M'.pull κ).lift.map₂ (Quot.mk _ η) ≫ (M'.pull κ).lift.map₂ (Quot.mk _ θ) = _
    rw [ihη, ihθ]
    exact eqToHom_conj_assoc (pull_lift_map M' κ _) (pull_lift_map M' κ _) (pull_lift_map M' κ _)
      _ _ _ (PrelaxFunctor.map₂_comp _ _ _).symm
  | whisker_left f η ih =>
    show (M'.pull κ).lift.map f ◁ (M'.pull κ).lift.map₂ (Quot.mk _ η) = _
    rw [ih]
    exact whiskerLeft_conj (pull_lift_map M' κ f) (pull_lift_map M' κ _) (pull_lift_map M' κ _)
      _ _ (lift_map₂_whiskerLeft _ _ _).symm
  | whisker_right h η ih =>
    show (M'.pull κ).lift.map₂ (Quot.mk _ η) ▷ (M'.pull κ).lift.map h = _
    rw [ih]
    exact whiskerRight_conj (pull_lift_map M' κ _) (pull_lift_map M' κ _) (pull_lift_map M' κ h)
      _ _ (lift_map₂_whiskerRight _ _ _).symm
  | associator f g h =>
    exact associator_conj (pull_lift_map M' κ f) (pull_lift_map M' κ g) (pull_lift_map M' κ h)
  | associator_inv f g h =>
    exact associator_inv_conj (pull_lift_map M' κ f) (pull_lift_map M' κ g)
      (pull_lift_map M' κ h)
  | right_unitor f => exact rightUnitor_conj (pull_lift_map M' κ f)
  | right_unitor_inv f => exact rightUnitor_inv_conj (pull_lift_map M' κ f)
  | left_unitor f => exact leftUnitor_conj (pull_lift_map M' κ f)
  | left_unitor_inv f => exact leftUnitor_inv_conj (pull_lift_map M' κ f)

end Pull


/-! ## Words and generator images -/

section GenPull

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] (M' : Model S' C) (κ : ColourMap S S')

/-- The image of a word for the pullback is the image of the relabelled word. -/
theorem pull_word (s : S.Region) (w : List S.Colour) (t : S.Region) (h : S.ok s w)
    (e : S.endR s w = t) (h' : S'.ok (κ.region s) (w.map κ.colour))
    (e' : S'.endR (κ.region s) (w.map κ.colour) = κ.region t) :
    (M'.pull κ).lift.map (fw s w t h e) =
      M'.lift.map (fw (κ.region s) (w.map κ.colour) (κ.region t) h' e') :=
  (pull_lift_map M' κ _).trans (congrArg M'.lift.map (fbMap_fw κ w s t h e h' e'))

theorem pull_word' (s : S.Region) (w : List S.Colour) (t : S.Region) (h : S.ok s w)
    (e : S.endR s w = t) (w' : List S'.Colour) (hw : w' = w.map κ.colour)
    (h' : S'.ok (κ.region s) w') (e' : S'.endR (κ.region s) w' = κ.region t) :
    (M'.pull κ).lift.map (fw s w t h e) =
      M'.lift.map (fw (κ.region s) w' (κ.region t) h' e') := by
  subst hw; exact pull_word M' κ s w t h e h' e'

variable {M'} (φ : SigMap S S') (G' : GenImg M')

theorem sigMap_dom_map (g : S.Gen) : S'.dom (φ.gen g) = (S.dom g).map φ.colour := by
  rw [φ.dom, φ.word_eq]

theorem sigMap_cod_map (g : S.Gen) : S'.cod (φ.gen g) = (S.cod g).map φ.colour := by
  rw [φ.cod, φ.word_eq]

/-- **The pullback of generator images**: the image of `g` is the image of `φ g`, between the
images of the boundary words (identified by `pull_word`). -/
def GenImg.pull : GenImg (M'.pull φ.toColourMap) where
  gen g a b ha hb hd hde hc hce :=
    eqToHom (pull_word' M' φ.toColourMap a (S.dom g) b hd hde _ (sigMap_dom_map φ g)
        (by rw [sigMap_dom_map]; exact ok_map' _ hd)
        (by rw [sigMap_dom_map, endR_map', hde])) ≫
      G'.gen (φ.gen g) (φ.region a) (φ.region b) (by rw [φ.left, ha]) (by rw [φ.right, hb])
        (by rw [sigMap_dom_map]; exact ok_map' _ hd) (by rw [sigMap_dom_map, endR_map', hde])
        (by rw [sigMap_cod_map]; exact ok_map' _ hc) (by rw [sigMap_cod_map, endR_map', hce]) ≫
      eqToHom (pull_word' M' φ.toColourMap a (S.cod g) b hc hce _ (sigMap_cod_map φ g)
        (by rw [sigMap_cod_map]; exact ok_map' _ hc)
        (by rw [sigMap_cod_map, endR_map', hce])).symm

end GenPull


/-! ## Images of layers -/

section CorePull

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] {M' : Model S' C} (φ : SigMap S S')
  (G' : GenImg M')

theorem fbMap_fw' (κ : ColourMap S S') (w : List S.Colour) (s t : S.Region) (h : S.ok s w)
    (e : S.endR s w = t) (w' : List S'.Colour) (hw : w' = w.map κ.colour)
    (h' : S'.ok (κ.region s) w') (e' : S'.endR (κ.region s) w' = κ.region t) :
    (fbMap κ).map (fw s w t h e) = fw (κ.region s) w' (κ.region t) h' e' := by
  subst hw; exact fbMap_fw κ w s t h e h' e'

theorem whisker_mid_conj {a b c d : C} {P P' : a ⟶ b} {Q Q' : c ⟶ d} {X X' Y Y' : b ⟶ c}
    (ep : P = P') (eq : Q = Q') (ex : X = X') (ey : Y = Y') (g : X' ⟶ Y') :
    P ◁ ((eqToHom ex ≫ g ≫ eqToHom ey.symm) ▷ Q) =
      eqToHom (by rw [ep, ex, eq]) ≫ P' ◁ (g ▷ Q') ≫ eqToHom (by rw [ep, ey, eq]) := by
  subst ep eq ex ey; simp

omit φ G' in
/-- The normal form of the image of a layer for the pullback, abstractly. -/
theorem key_pull {a b c d : FB S'} {F₀ F₁ F₂ F₃ G₀ G₃ : a ⟶ b} {P : a ⟶ c} {X Y : c ⟶ d}
    {Q : d ⟶ b} {U₀ U₃ : M'.lift.obj a ⟶ M'.lift.obj b}
    {P₀ : M'.lift.obj a ⟶ M'.lift.obj c} {X₀ Y₀ : M'.lift.obj c ⟶ M'.lift.obj d}
    {Q₀ : M'.lift.obj d ⟶ M'.lift.obj b}
    (A : F₀ ⟶ F₁) (B : F₂ ⟶ F₃) (A' : G₀ ⟶ P ≫ (X ≫ Q)) (B' : P ≫ (Y ≫ Q) ⟶ G₃)
    (g : M'.lift.map X ⟶ M'.lift.map Y)
    (hF₀ : F₀ = G₀) (hF₃ : F₃ = G₃) (hF₁ : F₁ = P ≫ (X ≫ Q)) (hF₂ : F₂ = P ≫ (Y ≫ Q))
    (ep : P₀ = M'.lift.map P) (eq : Q₀ = M'.lift.map Q)
    (ex : X₀ = M'.lift.map X) (ey' : M'.lift.map Y = Y₀)
    (e₀ : U₀ = M'.lift.map F₀) (e₁' : M'.lift.map F₁ = P₀ ≫ (X₀ ≫ Q₀))
    (e₂ : P₀ ≫ (Y₀ ≫ Q₀) = M'.lift.map F₂) (e₃' : M'.lift.map F₃ = U₃)
    (w₀ : U₀ = M'.lift.map G₀) (w₃' : M'.lift.map G₃ = U₃) :
    (eqToHom e₀ ≫ M'.lift.map₂ A ≫ eqToHom e₁') ≫
        (P₀ ◁ ((eqToHom ex ≫ g ≫ eqToHom ey') ▷ Q₀) ≫
          (eqToHom e₂ ≫ M'.lift.map₂ B ≫ eqToHom e₃')) =
      eqToHom w₀ ≫ (M'.lift.map₂ A' ≫ midK M' P Q g ≫ M'.lift.map₂ B') ≫ eqToHom w₃' := by
  subst hF₀ hF₃ hF₁ hF₂ ep eq ex ey' e₀ e₃'
  have hk₁ : eqToHom e₁' = 𝟙 _ := rfl
  have hk₂ : eqToHom e₂ = 𝟙 _ := rfl
  rw [hk₁, hk₂]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Category.id_comp, Category.comp_id]
  exact lift_conj_eq M' A A' (midK M' P Q g) B B'

theorem sigMap_word_dom (L : Layer S) :
    (φ.word L.left ++ S'.dom (φ.gen L.gen)) ++ φ.word L.right =
      ((L.left ++ S.dom L.gen) ++ L.right).map φ.colour := by
  rw [sigMap_dom_map, φ.word_eq, φ.word_eq]; simp

theorem sigMap_word_cod (L : Layer S) :
    (φ.word L.left ++ S'.cod (φ.gen L.gen)) ++ φ.word L.right =
      ((L.left ++ S.cod L.gen) ++ L.right).map φ.colour := by
  rw [sigMap_cod_map, φ.word_eq, φ.word_eq]; simp

/-- **The image of a layer for the pullback** is the image of the relabelled layer for `M'`,
between the identified images of the boundary words. -/
theorem core_pull {L : Layer S} (hv : L.Valid) (s m n t : S.Region) (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n)
    (ht : S.endR n L.right = t) :
    core (G'.pull φ) hv s m n t hl hm ha hb ht =
      eqToHom (pull_word' M' φ.toColourMap s _ t _ _ _ (sigMap_word_dom φ L) _ _) ≫
        core G' (φ.layer_valid hv) (φ.region s) (φ.region m) (φ.region n) (φ.region t)
          (φ.ok_map hl) ((φ.endR_map _ _).trans (congrArg φ.region hm))
          ((φ.left _).trans (congrArg φ.region ha)) ((φ.right _).trans (congrArg φ.region hb))
          ((φ.endR_map _ _).trans (congrArg φ.region ht)) ≫
        eqToHom (pull_word' M' φ.toColourMap s _ t _ _ _ (sigMap_word_cod φ L) _ _).symm := by
  unfold core
  rw [pull_lift_map₂, pull_lift_map₂]
  unfold midK
  dsimp only [GenImg.pull]
  have hm' : S'.endR (φ.region s) (φ.layer L).left = φ.region m :=
    (φ.endR_map _ _).trans (congrArg φ.region hm)
  have ha' : S'.left (φ.layer L).gen = φ.region m := (φ.left _).trans (congrArg φ.region ha)
  have hb' : S'.right (φ.layer L).gen = φ.region n := (φ.right _).trans (congrArg φ.region hb)
  have ht' : S'.endR (φ.region n) (φ.layer L).right = φ.region t :=
    (φ.endR_map _ _).trans (congrArg φ.region ht)
  have hv' := φ.layer_valid hv
  exact key_pull
    ((fbMap φ.toColourMap).map₂ (layerSplit L s m n t hl hm (S.dom L.gen)
      (Valid.ok_dom_of hv ha) (Valid.dom_end_of hv ha hb) (Valid.right_ok_of hv hb) ht).hom)
    ((fbMap φ.toColourMap).map₂ (layerSplit L s m n t hl hm (S.cod L.gen)
      (Valid.ok_cod_of hv ha) (Valid.cod_end_of hv ha hb) (Valid.right_ok_of hv hb) ht).inv)
    (layerSplit (φ.layer L) (φ.region s) (φ.region m) (φ.region n) (φ.region t) (φ.ok_map hl) hm'
      (S'.dom (φ.layer L).gen) (Valid.ok_dom_of hv' ha') (Valid.dom_end_of hv' ha' hb')
      (Valid.right_ok_of hv' hb') ht').hom
    (layerSplit (φ.layer L) (φ.region s) (φ.region m) (φ.region n) (φ.region t) (φ.ok_map hl) hm'
      (S'.cod (φ.layer L).gen) (Valid.ok_cod_of hv' ha') (Valid.cod_end_of hv' ha' hb')
      (Valid.right_ok_of hv' hb') ht').inv _
    (fbMap_fw' φ.toColourMap _ _ _ _ _ _ (sigMap_word_dom φ L) _ _)
    (fbMap_fw' φ.toColourMap _ _ _ _ _ _ (sigMap_word_cod φ L) _ _)
    (by
      rw [fbMap_comp, fbMap_comp, fbMap_fw' φ.toColourMap _ _ _ _ _ _ (φ.word_eq _) _ _,
        fbMap_fw' φ.toColourMap _ _ _ _ _ _ (sigMap_dom_map φ L.gen) _ _,
        fbMap_fw' φ.toColourMap _ _ _ _ _ _ (φ.word_eq _) _ _]
      rfl)
    (by
      rw [fbMap_comp, fbMap_comp, fbMap_fw' φ.toColourMap _ _ _ _ _ _ (φ.word_eq _) _ _,
        fbMap_fw' φ.toColourMap _ _ _ _ _ _ (sigMap_cod_map φ L.gen) _ _,
        fbMap_fw' φ.toColourMap _ _ _ _ _ _ (φ.word_eq _) _ _]
      rfl)
    (pull_word' M' φ.toColourMap n L.right t _ _ _ (φ.word_eq _) _ _)
    (pull_word' M' φ.toColourMap s L.left m _ _ _ (φ.word_eq _) _ _) _ _ _ _ _ _ _ _

end CorePull


/-! ## The interpretation of the pullback -/

section InterpPull

open CategoryTheory.Limits

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] [∀ a b : C, HasZeroObject (a ⟶ b)]
  [∀ a b : C, Preadditive (a ⟶ b)] {M' : Model S' C} (φ : SigMap S S') (G' : GenImg M')

omit [Bicategory C] [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)] in
theorem conj_shuffle {D : Type*} [Category D] {A B Z₁ Z₂ W₁ W₂ V₁ V₂ : D} (x : Z₁ ⟶ Z₂)
    (p₁ : A = W₁) (p₂ : W₁ = Z₁) (p₃ : Z₂ = W₂) (p₄ : W₂ = B) (q₁ : A = V₁) (q₂ : V₁ = Z₁)
    (q₃ : Z₂ = V₂) (q₄ : V₂ = B) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ x ≫ eqToHom p₃) ≫ eqToHom p₄ =
      eqToHom q₁ ≫ (eqToHom q₂ ≫ x ≫ eqToHom q₃) ≫ eqToHom q₄ := by
  subst p₁ p₂ p₃ p₄ q₂ q₃; simp

omit [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)] in
/-- Admissibility is preserved by a map of signatures. -/
theorem Cond.map {s t : S.Region} {a : Obj S} (h : Cond s t a) :
    Cond (φ.region s) (φ.region t) (φ.obj a) :=
  ⟨φ.ok_map h.1, (φ.endR_map _ _).trans (congrArg φ.region h.2.1),
    congrArg φ.region h.2.2⟩

omit [∀ a b : C, Preadditive (a ⟶ b)] in
/-- The image of an admissible object for the pullback is the image of its relabelling. -/
theorem objI_pull {s t : S.Region} {a : Obj S} {b : Obj S'} (h : Cond s t a)
    (hb : b = φ.obj a) (h' : Cond (φ.region s) (φ.region t) b) :
    objI (M'.pull φ.toColourMap) s t a = objI M' (φ.region s) (φ.region t) b := by
  subst hb
  rw [objI_pos _ _ h, objI_pos _ _ h']
  exact pull_word' M' φ.toColourMap s a.word t _ _ _ (φ.word_eq _) _ _

/-- **The image of a layer for the pullback** is the image of the relabelled layer. -/
theorem layerI_pull {s t : S.Region} {L : Layer S} (hv : L.Valid) (h : Cond s t L.dom) :
    layerI (G'.pull φ) s t L hv =
      eqToHom (objI_pull φ h (φ.toLayerMap.dom_eq hv)
          ((φ.toLayerMap.dom_eq hv).symm ▸ Cond.map φ h)) ≫
        layerI G' (φ.region s) (φ.region t) (φ.layer L) (φ.layer_valid hv) ≫
        eqToHom (objI_pull φ (h.cod hv) (φ.toLayerMap.cod_eq hv)
          ((φ.toLayerMap.cod_eq hv).symm ▸ Cond.map φ (h.cod hv))).symm := by
  have h' : Cond (φ.region s) (φ.region t) (φ.layer L).dom :=
    (φ.toLayerMap.dom_eq hv).symm ▸ Cond.map φ h
  rw [layerI_pos _ _ _ hv h, layerI_pos _ _ _ (φ.layer_valid hv) h', coreC_eq, coreC_eq,
    core_pull φ G' hv, core_regions G' (φ.layer_valid hv) _ _ _ (φ.region (S.left L.gen))
      (φ.region (S.right L.gen))]
  exact conj_shuffle (D := (M'.lift.obj (fo (φ.region t)) ⟶ M'.lift.obj (fo (φ.region s))))
    _ _ _ _ _ _ _ _ _

omit [∀ a b : C, Preadditive (a ⟶ b)] in
theorem mapChain_congr {D : Type*} [Category D] (I : Interpretation S' D) {a a' b : Obj S'}
    (e : a = a') (ls : List (Layer S')) (h : Chain a ls b) (h' : Chain a' ls b) :
    I.mapChain a ls b h = eqToHom (congrArg I.obj e) ≫ I.mapChain a' ls b h' := by
  subst e; simp

omit [Bicategory C] [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)] in
theorem id_shuffle {D : Type*} [Category D] {X Y : D} (e : X = Y) (e' : Y = X) :
    𝟙 X = eqToHom e ≫ 𝟙 Y ≫ eqToHom e' := by
  subst e; simp

omit [Bicategory C] [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)] in
theorem chain_shuffle {D : Type*} [Category D] {A B V₀ W₀ Xs Xt Z Y₁ Yt : D} (x : Xs ⟶ Xt)
    (y : Y₁ ⟶ Yt) (y' : Xt ⟶ Yt) (p₀ : A = W₀) (p₁ : W₀ = Xs) (p₂ : Xt = Z) (p₃ : Z = Y₁)
    (p₄ : Yt = B) (q₀ : A = V₀) (q₁ : V₀ = Xs) (q₂ : Yt = B) (r : Xt = Y₁)
    (hy : y' = eqToHom r ≫ y) :
    eqToHom p₀ ≫ (eqToHom p₁ ≫ x ≫ eqToHom p₂) ≫ eqToHom p₃ ≫ y ≫ eqToHom p₄ =
      eqToHom q₀ ≫ (eqToHom q₁ ≫ x ≫ y') ≫ eqToHom q₂ := by
  subst hy p₀ p₁ q₀ p₂ p₃ p₄; simp

/-- **The images of chains of layers for the pullback** are the images of the relabelled chains. -/
theorem mapChain_pull {s t : S.Region} : ∀ (ls : List (Layer S)) (a b : Obj S) (hc : Chain a ls b)
    (ha : Cond s t a),
    (interp (G'.pull φ) s t).mapChain a ls b hc =
      eqToHom (objI_pull φ ha rfl (Cond.map φ ha)) ≫
        (interp G' (φ.region s) (φ.region t)).mapChain (φ.obj a) (ls.map φ.layer) (φ.obj b)
          (φ.toLayerMap.chain hc) ≫
        eqToHom (objI_pull φ (ha.chain hc) rfl (Cond.map φ (ha.chain hc))).symm
  | [], a, b, hc, ha => by
    obtain rfl : a = b := hc
    exact id_shuffle (D := M'.lift.obj (fo (φ.region t)) ⟶ M'.lift.obj (fo (φ.region s))) _ _
  | L :: ls, a, b, hc, ha => by
    obtain ⟨hv, rfl, hc'⟩ := hc
    simp only [List.map_cons, Interpretation.mapChain]
    rw [layerI_pull φ G' hv ha, mapChain_pull ls L.cod b hc' (ha.cod hv)]
    exact chain_shuffle (D := M'.lift.obj (fo (φ.region t)) ⟶ M'.lift.obj (fo (φ.region s)))
      _ _ _ _ _ _ _ _ _ _ _ _ (mapChain_congr _ (φ.toLayerMap.cod_eq hv) _ _ _)


/-- **The interpretation of the pullback** (`interp_pull`): the image of a diagram `d` of `S` with
admissible source is the image of its relabelling `φ d`, between the identified images of the
boundary words. -/
theorem interp_pull {s t : S.Region} {a b : Obj S} (d : a ⟶ b) (ha : Cond s t a) :
    (interp (G'.pull φ) s t).functor.map d =
      eqToHom (objI_pull φ ha rfl (Cond.map φ ha)) ≫
        (interp G' (φ.region s) (φ.region t)).functor.map (φ.toLayerMap.map d) ≫
        eqToHom (objI_pull φ (ha.chain (Diagram.chain d)) rfl
          (Cond.map φ (ha.chain (Diagram.chain d)))).symm :=
  mapChain_pull φ G' _ a b _ ha

variable {R : Type*} [CommRing R] [∀ a b : C, Linear R (a ⟶ b)]

omit [Bicategory C] [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear R (a ⟶ b)] in
theorem cancel_conj {D : Type*} [Category D] {X X' Y Y' : D} (e : X = X') (e' : Y = Y')
    (x : X' ⟶ Y') (p : X' = X) (q : Y' = Y) :
    x = eqToHom p ≫ (eqToHom e ≫ x ≫ eqToHom q) ≫ eqToHom e' := by
  subst e e'; simp

/-- Conjugation by transports, as a linear map. -/
def conjLin {D : Type*} [Category D] [Preadditive D] [Linear R D] {X X' Y Y' : D} (e : X = X')
    (e' : Y = Y') : (X ⟶ Y) →ₗ[R] (X' ⟶ Y') where
  toFun x := eqToHom e.symm ≫ x ≫ eqToHom e'
  map_add' x y := by simp
  map_smul' r x := by simp

/-- **The linear extension of the interpretation of the pullback**: the image of a linear
combination `f` of diagrams of `S` (with admissible boundaries) under the interpretation of the
pullback, transported, is the image of its relabelling for `M'`. In particular the relabelling of
a linear combination killed by the pullback is killed by `M'`. -/
theorem freeLift_pull {s t : S.Region} {a b : Obj S} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram R a b) :
    (freeLift R (interp G' (φ.region s) (φ.region t)).functor).map (φ.toLayerMap.lin f) =
      conjLin (R := R) (D := M'.lift.obj (fo (φ.region t)) ⟶ M'.lift.obj (fo (φ.region s)))
        (objI_pull φ ha rfl (Cond.map φ ha)) (objI_pull φ hb rfl (Cond.map φ hb))
        ((freeLift R (interp (G'.pull φ) s t).functor).map f) := by
  refine freeLift_map_mapDomain (F := (interp (G'.pull φ) s t).functor)
    (G := (interp G' (φ.region s) (φ.region t)).functor) φ.toLayerMap.map _ (fun d => ?_) f
  rw [interp_pull φ G' d ha]
  exact cancel_conj (D := M'.lift.obj (fo (φ.region t)) ⟶ M'.lift.obj (fo (φ.region s))) _ _ _ _ _

theorem freeLift_pull_eq_zero {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (f : LinDiagram R a b)
    (hf : (freeLift R (interp (G'.pull φ) s t).functor).map f = 0) :
    (freeLift R (interp G' (φ.region s) (φ.region t)).functor).map (φ.toLayerMap.lin f) = 0 := by
  rw [freeLift_pull φ G' ha hb f]
  simp only [conjLin, LinearMap.coe_mk, AddHom.coe_mk]
  erw [hf, Limits.zero_comp, Limits.comp_zero]
  rfl

end InterpPull


/-! ## Models with equal strands -/

section Congr

open CategoryTheory.Limits

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] [∀ a b : C, HasZeroObject (a ⟶ b)]
  [∀ a b : C, Preadditive (a ⟶ b)] {R : Type*} [CommRing R] [∀ a b : C, Linear R (a ⟶ b)]

/-- **Models with equal strand images and generator images agreeing up to the identifications of
the strands** kill the same linear combinations of diagrams. -/
theorem freeLift_eq_zero_of_strand_eq (obj : S.Region → C)
    {st₁ st₂ : (c : S.Colour) → (x y : S.Region) → S.colourTgt c = x → S.colourSrc c = y →
      (obj x ⟶ obj y)} (h : st₁ = st₂)
    (G₁ : GenImg (⟨obj, st₁⟩ : Model S C)) (G₂ : GenImg (⟨obj, st₂⟩ : Model S C))
    (hG : ∀ g a b ha hb hd hde hc hce, G₁.gen g a b ha hb hd hde hc hce =
      eqToHom (by subst h; rfl) ≫ G₂.gen g a b ha hb hd hde hc hce ≫ eqToHom (by subst h; rfl))
    (s t : S.Region) {a b : Obj S} (f : LinDiagram R a b)
    (hf : (freeLift R (interp G₂ s t).functor).map f = 0) :
    (freeLift R (interp G₁ s t).functor).map f = 0 := by
  subst h
  obtain rfl : G₁ = G₂ := by
    cases G₁; cases G₂
    congr
    funext g a b ha hb hd hde hc hce
    simpa using hG g a b ha hb hd hde hc hce
  exact hf

end Congr

end Categorification.Diagrams.BicatInterp
