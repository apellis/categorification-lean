/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissible
import Categorification.Diagrams.BicatInterpPull
import Categorification.Diagrams.BicatInterpAdmissiblePull
import Categorification.Diagrams.RevBicat
import StringDiagrams.LayerMap.Generators

/-!
# Pulling a model back along a reflection in a vertical axis

For a reflection `φ : S → S'` in a vertical axis (`StringDiagrams.SigMirror`), a model `M'` of
`S'` in the 1-cell dual `RevBicat C` of a bicategory `C` gives a model `M'.mirror φ` of `S` in
`C` itself: the region `x` goes to the image of `φ x`, and a strand `c` to the image of `φ c`.
A word of `S` and its reflection have images that are 1-morphisms of `C` between the same
objects; they differ only in the bracketing of composites, and are identified by the images of
free 2-isomorphisms (`mirrorWordIso`). Generator images of `M'` pull back to generator images
of `M'.mirror φ` (`GenImg.mirror`), and the admissible interpretation of the pullback of a
diagram is the admissible interpretation of the reflected diagram, conjugated by these
identifications (`admissibleMap_mirror`).

This transfers relations proved for a model of the Khovanov–Lauda signature to the
reflected black part of the double Stendhal signature of Webster, arXiv:1309.3796v3, §4.5
(Theorem 4.25), whose words are read with the opposite horizontal orientation.

## Main definitions and results

* `rqMirror`, `fbMirror`: the pseudofunctor `FB S ⥤ᵖ RevBicat (FB S')` of free bicategories;
* `Model.mirror`, `mirror_lift_map`, `mirror_lift_map₂`;
* `mirrorFwIso`, `mirrorWordIso`: the identification of the image of a word with that of its
  reflection;
* `GenImg.mirror`, `midK_mirror`, `core_mirror`, `coreC_mirror`, `admissibleChain_mirror`,
  `admissibleMap_mirror`, `admissibleMap_mirror_eq_zero`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ u₀ u₁ u₂ u₀' u₁' u₂' v₂

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}}

/-! ## Free bicategories -/

section Free

variable (κ : MirrorColourMap S S')

/-- The prefunctor from the quiver of regions of `S` to the 1-cell dual of the free bicategory
of `S'` induced by a reflection: a strand from `x` (on its right) to `y` (on its left) goes to
its reflection, from `κ y` to `κ x`. -/
def rqMirror : Prefunctor (RQ S) (RevBicat (FB S')) where
  obj x := ⟨κ.region x⟩
  map {x y} c := RevBicat.of (B := FB S') (FreeBicategory.Hom.of
    (show rq (κ.region y) ⟶ rq (κ.region x) from
      ⟨κ.colour c.1, by rw [κ.colourTgt, c.2.2], by rw [κ.colourSrc, c.2.1]⟩))

/-- The pseudofunctor of free bicategories induced by a reflection. -/
abbrev fbMirror : FB S ⥤ᵖ RevBicat (FB S') := FreeBicategory.lift (rqMirror κ)

/-- The image under `fbMirror` of a free 1-morphism, as a 1-morphism of `FB S'`. -/
abbrev fbMirrorMap {a b : FB S} (f : a ⟶ b) :
    (fo (κ.region b) : FB S') ⟶ fo (κ.region a) :=
  (fbMirror κ).map f

theorem fbMirrorMap_comp {a b c : FB S} (f : a ⟶ b) (g : b ⟶ c) :
    fbMirrorMap κ (f ≫ g) = fbMirrorMap κ g ≫ fbMirrorMap κ f := rfl

end Free

/-! ## The pullback of a model along a reflection -/

section Model

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] (κ : MirrorColourMap S S')

/-- **The pullback of a model along a reflection**: a model of `S'` in `RevBicat C` gives a
model of `S` in `C`, sending the region `x` to the image of `κ x` and the strand `c` to the
image of `κ c`. -/
def Model.mirror (M' : Model S' (RevBicat C)) : Model S C where
  obj x := (M'.obj (κ.region x)).as
  strandAt c x y hx hy := M'.strandAt (κ.colour c) (κ.region y) (κ.region x)
    (by rw [κ.colourTgt, hy]) (by rw [κ.colourSrc, hx])

variable (M' : Model S' (RevBicat C))

/-- The pseudofunctor of the pullback on 1-morphisms: `fbMirror` followed by that of `M'`. -/
theorem mirror_lift_map {a b : FB S} (f : a ⟶ b) :
    (M'.mirror κ).lift.map f = M'.lift.map (fbMirrorMap κ f) := by
  induction f with
  | of f => rfl
  | id a => rfl
  | comp f g ihf ihg =>
    exact congrArg₂ (fun x y => x ≫ y) ihf ihg

/-- The pseudofunctor of the pullback on 2-morphisms: `fbMirror` followed by that of `M'`, up to
the identifications `mirror_lift_map`. -/
theorem mirror_lift_map₂ {a b : FB S} {f g : a ⟶ b} (η : f ⟶ g) :
    (M'.mirror κ).lift.map₂ η = eqToHom (mirror_lift_map κ M' f) ≫
      M'.lift.map₂ ((fbMirror κ).map₂ η) ≫ eqToHom (mirror_lift_map κ M' g).symm := by
  induction η using Quot.ind with
  | mk η =>
  induction η with
  | id f =>
    exact id_conj (mirror_lift_map κ M' f) _ (PrelaxFunctor.map₂_id _ _).symm
  | vcomp η θ ihη ihθ =>
    show (M'.mirror κ).lift.map₂ (Quot.mk _ η) ≫ (M'.mirror κ).lift.map₂ (Quot.mk _ θ) = _
    rw [ihη, ihθ]
    exact eqToHom_conj_assoc (mirror_lift_map κ M' _) (mirror_lift_map κ M' _)
      (mirror_lift_map κ M' _) _ _ _ (PrelaxFunctor.map₂_comp _ _ _).symm
  | whisker_left f η ih =>
    show (M'.mirror κ).lift.map f ◁ (M'.mirror κ).lift.map₂ (Quot.mk _ η) = _
    rw [ih]
    exact whiskerLeft_conj (mirror_lift_map κ M' f) (mirror_lift_map κ M' _)
      (mirror_lift_map κ M' _) _ _ (lift_map₂_whiskerRight _ _ _).symm
  | whisker_right h η ih =>
    show (M'.mirror κ).lift.map₂ (Quot.mk _ η) ▷ (M'.mirror κ).lift.map h = _
    rw [ih]
    exact whiskerRight_conj (mirror_lift_map κ M' _) (mirror_lift_map κ M' _)
      (mirror_lift_map κ M' h) _ _ (lift_map₂_whiskerLeft _ _ _).symm
  | associator f g h =>
    exact associator_conj (mirror_lift_map κ M' f) (mirror_lift_map κ M' g)
      (mirror_lift_map κ M' h)
  | associator_inv f g h =>
    exact associator_inv_conj (mirror_lift_map κ M' f) (mirror_lift_map κ M' g)
      (mirror_lift_map κ M' h)
  | right_unitor f => exact rightUnitor_conj (mirror_lift_map κ M' f)
  | right_unitor_inv f => exact rightUnitor_inv_conj (mirror_lift_map κ M' f)
  | left_unitor f => exact leftUnitor_conj (mirror_lift_map κ M' f)
  | left_unitor_inv f => exact leftUnitor_inv_conj (mirror_lift_map κ M' f)

end Model

/-! ## Words -/

section Words

variable (κ : MirrorColourMap S S')

theorem mirror_ok {s t : S.Region} {w : List S.Colour} (h : S.ok s w) (e : S.endR s w = t) :
    S'.ok (κ.region t) (κ.word w) := by
  have := (κ.ok_word h).1; rwa [e] at this

theorem mirror_endR {s t : S.Region} {w : List S.Colour} (h : S.ok s w) (e : S.endR s w = t) :
    S'.endR (κ.region t) (κ.word w) = κ.region s := by
  have := (κ.ok_word h).2; rwa [e] at this

/-- **The free 1-morphism of a reflected word**: the image under `fbMirror` of the free
1-morphism of a word is isomorphic to the free 1-morphism of its reflection (the two differ in
the bracketing of composites). -/
def mirrorFwIso : (w : List S.Colour) → (s t : S.Region) → (h : S.ok s w) →
    (e : S.endR s w = t) → (h' : S'.ok (κ.region t) (κ.word w)) →
    (e' : S'.endR (κ.region t) (κ.word w) = κ.region s) →
    (fbMirrorMap κ (fw s w t h e) ≅ fw (κ.region t) (κ.word w) (κ.region s) h' e')
  | [], s, t, h, e, h', e' => by subst e; exact Iso.refl _
  | [c], s, t, h, e, h', e' => Iso.refl _
  | c :: c' :: w, s, t, h, e, h', e' =>
    @whiskerLeftIso (FB S') _ _ _ _
        (fbMirrorMap κ (show fo (S.colourTgt c) ⟶ fo s from FreeBicategory.Hom.of ⟨c, rfl, h.1⟩))
        _ _ (mirrorFwIso (c' :: w) (S.colourTgt c) t h.2 e (mirror_ok κ h.2 e)
        (mirror_endR κ h.2 e)) ≪≫
      (splitIso (κ.region t) (κ.word (c' :: w)) [κ.colour c] (κ.region (S.colourTgt c))
        (κ.region s) (mirror_ok κ h.2 e) (mirror_endR κ h.2 e)
        ⟨κ.colourSrc c, trivial⟩ (by
          change S'.colourTgt (κ.colour c) = κ.region s
          rw [κ.colourTgt, h.1])).symm ≪≫
      eqToIso (fw_eq (κ.word_cons c (c' :: w)).symm _ _ h' e')

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] (M' : Model S' (RevBicat C))

/-- **The image of a reflected word**: the image of a word for the pullback along a reflection
is identified with the image of the reflected word, by the image of a free 2-isomorphism. -/
def mirrorWordIso (w : List S.Colour) (s t : S.Region) (h : S.ok s w) (e : S.endR s w = t)
    (h' : S'.ok (κ.region t) (κ.word w)) (e' : S'.endR (κ.region t) (κ.word w) = κ.region s) :
    (M'.mirror κ).word s w t h e ≅ M'.word (κ.region t) (κ.word w) (κ.region s) h' e' :=
  eqToIso (mirror_lift_map κ M' _) ≪≫ M'.lift.map₂Iso (mirrorFwIso κ w s t h e h' e')

end Words

/-! ## Generator images -/

section GenMirror

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] {M' : Model S' (RevBicat C)}
  (φ : SigMirror S S') (G' : GenImg M')

theorem sigMirror_ok_dom {g : S.Gen} {a b : S.Region} (hd : S.ok a (S.dom g))
    (hde : S.endR a (S.dom g) = b) : S'.ok (φ.region b) (S'.dom (φ.gen g)) := by
  rw [φ.dom']; exact mirror_ok φ.toMirrorColourMap hd hde

theorem sigMirror_endR_dom {g : S.Gen} {a b : S.Region} (hd : S.ok a (S.dom g))
    (hde : S.endR a (S.dom g) = b) : S'.endR (φ.region b) (S'.dom (φ.gen g)) = φ.region a := by
  rw [φ.dom']; exact mirror_endR φ.toMirrorColourMap hd hde

theorem sigMirror_ok_cod {g : S.Gen} {a b : S.Region} (hc : S.ok a (S.cod g))
    (hce : S.endR a (S.cod g) = b) : S'.ok (φ.region b) (S'.cod (φ.gen g)) := by
  rw [φ.cod']; exact mirror_ok φ.toMirrorColourMap hc hce

theorem sigMirror_endR_cod {g : S.Gen} {a b : S.Region} (hc : S.ok a (S.cod g))
    (hce : S.endR a (S.cod g) = b) : S'.endR (φ.region b) (S'.cod (φ.gen g)) = φ.region a := by
  rw [φ.cod']; exact mirror_endR φ.toMirrorColourMap hc hce

/-- **The pullback of generator images along a reflection**: the image of `g` is the image of
`φ g`, between the images of the reflected boundary words, identified with the images of the
boundary words by `mirrorWordIso`. -/
def GenImg.mirror : GenImg (M'.mirror φ.toMirrorColourMap) where
  gen g a b ha hb hd hde hc hce :=
    (mirrorWordIso φ.toMirrorColourMap M' (S.dom g) a b hd hde
        (mirror_ok _ hd hde) (mirror_endR _ hd hde)).hom ≫
      eqToHom (congrArg M'.lift.map (fw_eq (φ.dom' g).symm _ _
        (sigMirror_ok_dom φ hd hde) (sigMirror_endR_dom φ hd hde))) ≫
      G'.gen (φ.gen g) (φ.region b) (φ.region a) (by rw [φ.left, hb]) (by rw [φ.right, ha])
        (sigMirror_ok_dom φ hd hde) (sigMirror_endR_dom φ hd hde)
        (sigMirror_ok_cod φ hc hce) (sigMirror_endR_cod φ hc hce) ≫
      eqToHom (congrArg M'.lift.map (fw_eq (φ.cod' g) _ _
        (mirror_ok _ hc hce) (mirror_endR _ hc hce))) ≫
      (mirrorWordIso φ.toMirrorColourMap M' (S.cod g) a b hc hce
        (mirror_ok _ hc hce) (mirror_endR _ hc hce)).inv

end GenMirror

/-! ## Whiskered generator images -/

section MidMirror

variable {C : Type w₁} [Bicategory.{w₂, v₂} C]

theorem mirror_mid_aux {o₀ o₁ o₂ o₃ : C} {A A' : o₀ ⟶ o₁} {X X' Y Y' : o₁ ⟶ o₂}
    {B B' : o₂ ⟶ o₃} (eA : A = A') (eB : B = B') (eX : X = X') (eY : Y = Y') (k : X ⟶ Y) :
    A ◁ (k ▷ B) = eqToHom (by rw [eA, eX, eB]) ≫ (α_ A' X' B').inv ≫
      (A' ◁ (eqToHom eX.symm ≫ k ≫ eqToHom eY)) ▷ B' ≫ (α_ A' Y' B').hom ≫
        eqToHom (by rw [eA, eY, eB]) := by
  subst eA eB eX eY
  simp [whisker_assoc]

variable (κ : MirrorColourMap S S') (M' : Model S' (RevBicat C))

/-- **A whiskered 2-morphism for the pullback along a reflection** is the whiskered
2-morphism for `M'` with the whiskering 1-morphisms exchanged, up to an associator. -/
theorem midK_mirror {a b c d : FB S} (p : a ⟶ b) (q : c ⟶ d) {x y : b ⟶ c}
    (k : (M'.mirror κ).lift.map x ⟶ (M'.mirror κ).lift.map y) :
    midK (M'.mirror κ) p q k =
      eqToHom (mirror_lift_map κ M' (p ≫ (x ≫ q))) ≫
        M'.lift.map₂ (α_ (fbMirrorMap κ q) (fbMirrorMap κ x) (fbMirrorMap κ p)).hom ≫
        midK M' (fbMirrorMap κ q) (fbMirrorMap κ p)
          (eqToHom (mirror_lift_map κ M' x).symm ≫ k ≫ eqToHom (mirror_lift_map κ M' y)) ≫
        M'.lift.map₂ (α_ (fbMirrorMap κ q) (fbMirrorMap κ y) (fbMirrorMap κ p)).inv ≫
        eqToHom (mirror_lift_map κ M' (p ≫ (y ≫ q))).symm := by
  unfold midK
  exact (mirror_mid_aux (mirror_lift_map κ M' p) (mirror_lift_map κ M' q)
    (mirror_lift_map κ M' x) (mirror_lift_map κ M' y) k).trans rfl

end MidMirror

/-! ## Layers -/

section CoreMirror

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] {M' : Model S' (RevBicat C)}
  (φ : SigMirror S S') (G' : GenImg M')

theorem sigMirror_word_dom (L : Layer S) :
    φ.word ((L.left ++ S.dom L.gen) ++ L.right) =
      (φ.word L.right ++ S'.dom (φ.gen L.gen)) ++ φ.word L.left := by
  simp [MirrorColourMap.word_append, φ.dom', List.append_assoc]

theorem sigMirror_word_cod (L : Layer S) :
    φ.word ((L.left ++ S.cod L.gen) ++ L.right) =
      (φ.word L.right ++ S'.cod (φ.gen L.gen)) ++ φ.word L.left := by
  simp [MirrorColourMap.word_append, φ.cod', List.append_assoc]

omit [Bicategory C] in
theorem layer_ok_dom {L : Layer S} (hv : L.Valid) {s m n : S.Region} (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n) :
    S.ok s ((L.left ++ S.dom L.gen) ++ L.right) :=
  ok_append_of (ok_append_of hl hm (Valid.ok_dom_of hv ha))
    (endR_append_of hm (Valid.dom_end_of hv ha hb)) (Valid.right_ok_of hv hb)

omit [Bicategory C] in
theorem layer_endR_dom {L : Layer S} (hv : L.Valid) {s m n t : S.Region}
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n)
    (ht : S.endR n L.right = t) : S.endR s ((L.left ++ S.dom L.gen) ++ L.right) = t :=
  endR_append_of (endR_append_of hm (Valid.dom_end_of hv ha hb)) ht

omit [Bicategory C] in
theorem layer_ok_cod {L : Layer S} (hv : L.Valid) {s m n : S.Region} (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n) :
    S.ok s ((L.left ++ S.cod L.gen) ++ L.right) :=
  ok_append_of (ok_append_of hl hm (Valid.ok_cod_of hv ha))
    (endR_append_of hm (Valid.cod_end_of hv ha hb)) (Valid.right_ok_of hv hb)

omit [Bicategory C] in
theorem layer_endR_cod {L : Layer S} (hv : L.Valid) {s m n t : S.Region}
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n)
    (ht : S.endR n L.right = t) : S.endR s ((L.left ++ S.cod L.gen) ++ L.right) = t :=
  endR_append_of (endR_append_of hm (Valid.cod_end_of hv ha hb)) ht

omit φ G' in
/-- The normal form of the image of a layer for the pullback along a reflection, abstractly. -/
theorem key_mirror {a b c d : FB S'} {P P' : c ⟶ d} {Q Q' : b ⟶ a} {x y x₀ y₀ : d ⟶ b}
    {F₀ F₃ : c ⟶ a} {U₀ U₃ : M'.lift.obj c ⟶ M'.lift.obj a} (σ : P ≅ P') (τ : Q ≅ Q')
    (g : M'.lift.map x ⟶ M'.lift.map y) (a₀ : x₀ ⟶ x) (b₀ : y ⟶ y₀)
    (A : F₀ ⟶ P ≫ (x₀ ≫ Q)) (B : P ≫ (y₀ ≫ Q) ⟶ F₃) (A' : F₀ ⟶ P' ≫ (x ≫ Q'))
    (B' : P' ≫ (y ≫ Q') ⟶ F₃) (e₀ : U₀ = M'.lift.map F₀) (e₃ : M'.lift.map F₃ = U₃) :
    eqToHom e₀ ≫ M'.lift.map₂ A ≫ midK M' P Q (M'.lift.map₂ a₀ ≫ g ≫ M'.lift.map₂ b₀) ≫
        M'.lift.map₂ B ≫ eqToHom e₃ =
      eqToHom e₀ ≫ M'.lift.map₂ A' ≫ midK M' P' Q' g ≫ M'.lift.map₂ B' ≫ eqToHom e₃ := by
  rw [mid_comp, mid_conj M' σ τ g]
  have := lift_conj_eq M' (A ≫ P ◁ (a₀ ▷ Q) ≫ (σ.hom ▷ (x ≫ Q) ≫ P' ◁ x ◁ τ.hom)) A'
    (midK M' P' Q' g) ((P' ◁ y ◁ τ.inv ≫ σ.inv ▷ (y ≫ Q)) ≫ P ◁ (b₀ ▷ Q) ≫ B) B'
  simp only [PrelaxFunctor.map₂_comp, Category.assoc] at this
  simp only [PrelaxFunctor.map₂_comp, Category.assoc, reassoc_of% this]

omit φ G' in
/-- The image of a layer for the pullback along a reflection, with the transports of
`mirror_lift_map` and of equal free 1-morphisms, abstractly. -/
theorem key_mirror' {a b c d : FB S'} {P P' : c ⟶ d} {Q Q' : b ⟶ a}
    {x₀ x₁ xg yg y₁ y₀ : d ⟶ b} {T₀ V₀ V₀' F₁ F₂ V₃' V₃ T₃ : c ⟶ a}
    {U₀ U₃ Z₁ Z₂ : M'.lift.obj c ⟶ M'.lift.obj a} {X₀ Y₀ : M'.lift.obj d ⟶ M'.lift.obj b}
    (σ : P ≅ P') (τ : Q ≅ Q') (g : M'.lift.map xg ⟶ M'.lift.map yg)
    (σd : x₀ ⟶ x₁) (σc : y₁ ⟶ y₀) (S₁ : T₀ ⟶ F₁) (α₁ : F₁ ⟶ P ≫ (x₀ ≫ Q))
    (α₂ : P ≫ (y₀ ≫ Q) ⟶ F₂) (S₂ : F₂ ⟶ T₃) (τd : T₀ ⟶ V₀) (A' : V₀' ⟶ P' ≫ (xg ≫ Q'))
    (B' : P' ≫ (yg ≫ Q') ⟶ V₃') (τc : V₃ ⟶ T₃)
    (hx : x₁ = xg) (hy : yg = y₁) (hV₀ : V₀ = V₀') (hV₃ : V₃' = V₃)
    (p₁ : U₀ = M'.lift.map T₀) (p₂ : M'.lift.map F₁ = Z₁) (p₃ : Z₁ = M'.lift.map F₁)
    (p₄ : M'.lift.map x₀ = X₀) (p₅ : X₀ = M'.lift.map x₀)
    (p₆ : M'.lift.map x₁ = M'.lift.map xg) (p₇ : M'.lift.map yg = M'.lift.map y₁)
    (p₈ : M'.lift.map y₀ = Y₀) (p₉ : Y₀ = M'.lift.map y₀)
    (p₁₀ : M'.lift.map F₂ = Z₂) (p₁₁ : Z₂ = M'.lift.map F₂) (p₁₂ : M'.lift.map T₃ = U₃)
    (q₂ : M'.lift.map V₀ = M'.lift.map V₀') (q₃ : M'.lift.map V₃' = M'.lift.map V₃) :
    eqToHom p₁ ≫ M'.lift.map₂ S₁ ≫ eqToHom p₂ ≫ eqToHom p₃ ≫ M'.lift.map₂ α₁ ≫
        midK M' P Q (eqToHom p₄ ≫ eqToHom p₅ ≫ M'.lift.map₂ σd ≫ eqToHom p₆ ≫ g ≫
          eqToHom p₇ ≫ M'.lift.map₂ σc ≫ eqToHom p₈ ≫ eqToHom p₉) ≫
        M'.lift.map₂ α₂ ≫ eqToHom p₁₀ ≫ eqToHom p₁₁ ≫ M'.lift.map₂ S₂ ≫ eqToHom p₁₂ =
      eqToHom p₁ ≫ M'.lift.map₂ τd ≫ eqToHom q₂ ≫ M'.lift.map₂ A' ≫ midK M' P' Q' g ≫
        M'.lift.map₂ B' ≫ eqToHom q₃ ≫ M'.lift.map₂ τc ≫ eqToHom p₁₂ := by
  subst hx hy hV₀ hV₃ p₂ p₄ p₈ p₁₀
  have := key_mirror σ τ g σd σc (S₁ ≫ α₁) (α₂ ≫ S₂) (τd ≫ A') (B' ≫ τc) p₁ p₁₂
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, eqToHom_trans_assoc,
    PrelaxFunctor.map₂_comp, Category.assoc] using this

/-- **The image of a layer for the pullback along a reflection** is the image of the reflected
layer for `M'`, between the identified images of the boundary words. -/
theorem core_mirror {L : Layer S} (hv : L.Valid) (s m n t : S.Region) (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n)
    (ht : S.endR n L.right = t) :
    core (G'.mirror φ) hv s m n t hl hm ha hb ht =
      (mirrorWordIso φ.toMirrorColourMap M' _ s t
          (layer_ok_dom hv hl hm ha hb) (layer_endR_dom hv hm ha hb ht)
          (mirror_ok _ (layer_ok_dom hv hl hm ha hb) (layer_endR_dom hv hm ha hb ht))
          (mirror_endR _ (layer_ok_dom hv hl hm ha hb) (layer_endR_dom hv hm ha hb ht))).hom ≫
        eqToHom (by exact congrArg M'.lift.map (fw_eq (sigMirror_word_dom φ L) _ _ _ _)) ≫
        core G' (φ.layer_valid hv) (φ.region t) (φ.region n) (φ.region m) (φ.region s)
          (mirror_ok _ (Valid.right_ok_of hv hb) ht) (mirror_endR _ (Valid.right_ok_of hv hb) ht)
          ((φ.left _).trans (congrArg φ.region hb)) ((φ.right _).trans (congrArg φ.region ha))
          (mirror_endR _ hl hm) ≫
        eqToHom (by exact congrArg M'.lift.map (fw_eq (sigMirror_word_cod φ L).symm _ _ _ _)) ≫
        (mirrorWordIso φ.toMirrorColourMap M' _ s t
          (layer_ok_cod hv hl hm ha hb) (layer_endR_cod hv hm ha hb ht)
          (mirror_ok _ (layer_ok_cod hv hl hm ha hb) (layer_endR_cod hv hm ha hb ht))
          (mirror_endR _ (layer_ok_cod hv hl hm ha hb) (layer_endR_cod hv hm ha hb ht))).inv := by
  unfold core
  rw [mirror_lift_map₂, mirror_lift_map₂, midK_mirror]
  dsimp only [GenImg.mirror, mirrorWordIso]
  simp only [Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc,
    PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂Iso_inv]
  exact key_mirror'
    (mirrorFwIso φ.toMirrorColourMap L.left s m hl hm _ _)
    (mirrorFwIso φ.toMirrorColourMap L.right n t _ ht _ _) _ _ _ _ _ _ _ _ _ _ _
    (fw_eq (φ.dom' L.gen).symm _ _ _ _) (fw_eq (φ.cod' L.gen) _ _ _ _)
    (fw_eq (sigMirror_word_dom φ L) _ _ _ _) (fw_eq (sigMirror_word_cod φ L).symm _ _ _ _)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _

end CoreMirror

/-! ## Admissible interpretations -/

section AdmissibleMirror

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] {M' : Model S' (RevBicat C)}
  (φ : SigMirror S S') (G' : GenImg M')

/-- Admissibility is carried to the reflection, with the outer regions exchanged. -/
theorem Cond.mirror {s t : S.Region} {a : Obj S} (h : Cond s t a) :
    Cond (φ.region t) (φ.region s) (φ.obj a) :=
  ⟨mirror_ok _ h.1 h.2.1, mirror_endR _ h.1 h.2.1, by
    show φ.region (S.endR a.start a.word) = φ.region t
    rw [h.2.2, h.2.1]⟩

omit G' in
/-- The image of an admissible word for the pullback along a reflection is isomorphic to the
image of its reflection. -/
def condMirrorIso {s t : S.Region} {a : Obj S} (h : Cond s t a) :
    (M'.mirror φ.toMirrorColourMap).word s a.word t h.1 h.2.1 ≅
      M'.word (φ.region t) (φ.obj a).word (φ.region s) (Cond.mirror φ h).1
        (Cond.mirror φ h).2.1 :=
  mirrorWordIso φ.toMirrorColourMap M' a.word s t h.1 h.2.1 _ _

omit G' in
theorem condMirrorIso_eqToHom {s t : S.Region} {a a' : Obj S} (e : a = a') (h : Cond s t a)
    (h' : Cond s t a') :
    (condMirrorIso φ h).hom ≫
        eqToHom (admissibleWord_eq (M := M') (congrArg φ.obj e) (Cond.mirror φ h)
          (Cond.mirror φ h')) =
      eqToHom (admissibleWord_eq (M := M'.mirror φ.toMirrorColourMap) e h h') ≫
        (condMirrorIso φ h').hom := by
  subst e; simp

/-- **The image of a layer for the pullback along a reflection**, on admissible words. -/
theorem coreC_mirror {s t : S.Region} {L : Layer S} (hv : L.Valid) (h : Cond s t L.dom)
    (h' : Cond (φ.region t) (φ.region s) (φ.layer L).dom) :
    coreC (G'.mirror φ) hv h =
      (condMirrorIso φ h).hom ≫
        eqToHom (admissibleWord_eq (M := M') (φ.toLayerMap.dom_eq hv).symm
          (Cond.mirror φ h) h') ≫
        coreC G' (φ.layer_valid hv) h' ≫
        eqToHom (admissibleWord_eq (M := M') (φ.toLayerMap.cod_eq hv)
          (h'.cod (φ.layer_valid hv)) (Cond.mirror φ (h.cod hv))) ≫
        (condMirrorIso φ (h.cod hv)).inv := by
  rw [coreC_eq, coreC_eq, core_mirror φ G' hv,
    core_regions G' (φ.layer_valid hv) (φ.region t) (S'.left (φ.layer L).gen)
      (S'.right (φ.layer L).gen) (φ.region (S.right L.gen)) (φ.region (S.left L.gen))]
  rfl

/-- **The images of admissible chains for the pullback along a reflection** are the images of
the reflected chains, between the identified images of the boundary words. -/
theorem admissibleChain_mirror {s t : S.Region} : ∀ (ls : List (Layer S)) (a b : Obj S)
    (hc : Chain a ls b) (ha : Cond s t a) (hb : Cond s t b),
    admissibleChain (G'.mirror φ) a ls b hc ha hb =
      (condMirrorIso φ ha).hom ≫
        admissibleChain G' (φ.obj a) (ls.map φ.layer) (φ.obj b) (φ.toLayerMap.chain hc)
          (Cond.mirror φ ha) (Cond.mirror φ hb) ≫
        (condMirrorIso φ hb).inv
  | [], a, b, hc, ha, hb => by
    obtain rfl : a = b := hc
    simp [admissibleChain]
  | L :: ls, a, b, hc, ha, hb => by
    obtain ⟨hv, rfl, hc'⟩ := hc
    have h' : Cond (φ.region t) (φ.region s) (φ.layer L).dom :=
      (φ.toLayerMap.dom_eq hv).symm ▸ Cond.mirror φ ha
    simp only [List.map_cons, admissibleChain]
    rw [coreC_mirror φ G' hv _ h', admissibleChain_mirror ls L.cod b hc' _ hb]
    simp only [eqToHom_refl, Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
    erw [admissibleChain_src G' (φ.toLayerMap.cod_eq hv) (h' := φ.toLayerMap.chain hc')
      (ha' := Cond.mirror φ (ha.cod hv))]
    simp only [Category.assoc]
    rfl

/-- **The admissible interpretation of the pullback along a reflection** of a diagram is that of
its reflection. -/
theorem admissibleInterp_mirror {s t : S.Region} {a b : Obj S} (d : a ⟶ b) (ha : Cond s t a)
    (hb : Cond s t b) :
    (admissibleInterp (G'.mirror φ) s t).map
        (ObjectProperty.homMk (X := ⟨a, ha⟩) (Y := ⟨b, hb⟩) d) =
      (condMirrorIso φ ha).hom ≫
        (admissibleInterp G' (φ.region t) (φ.region s)).map
          (ObjectProperty.homMk (X := ⟨φ.obj a, Cond.mirror φ ha⟩)
            (Y := ⟨φ.obj b, Cond.mirror φ hb⟩) (φ.toLayerMap.map d)) ≫
        (condMirrorIso φ hb).inv :=
  admissibleChain_mirror φ G' _ a b _ ha hb

end AdmissibleMirror

/-! ## Linear admissible interpretations -/

section LinearMirror

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] {R : Type*} [CommRing R]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]

instance revBicatPreadditive (a b : RevBicat C) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (b.as ⟶ a.as))

instance revBicatLinear (a b : RevBicat C) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (b.as ⟶ a.as))

variable {M' : Model S' (RevBicat C)} (φ : SigMirror S S') (G' : GenImg M')

/-- **The linear admissible interpretation of the pullback along a reflection**: the image of
a reflected linear combination of diagrams is the image of the original one for the pullback,
conjugated by the identifications of the boundary words. -/
theorem admissibleMap_mirror {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (f : LinDiagram R a b) :
    admissibleMap G' (Cond.mirror φ ha) (Cond.mirror φ hb) (φ.toLayerMap.lin f) =
      (condMirrorIso φ ha).inv ≫ admissibleMap (G'.mirror φ) ha hb f ≫
        (condMirrorIso φ hb).hom := by
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
    rw [admissibleInterp_mirror φ G' d ha hb]
    simp

/-- A linear combination killed by the admissible interpretation of the pullback along a
reflection has its reflection killed by the original admissible interpretation. -/
theorem admissibleMap_mirror_eq_zero {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (f : LinDiagram R a b) (hf : admissibleMap (G'.mirror φ) ha hb f = 0) :
    admissibleMap G' (Cond.mirror φ ha) (Cond.mirror φ hb) (φ.toLayerMap.lin f) = 0 := by
  rw [admissibleMap_mirror φ G' ha hb f, hf]
  simp

end LinearMirror

end Categorification.Diagrams.BicatInterp
