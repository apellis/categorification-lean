/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpPull
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Pushing a model forward along a strict pseudofunctor

For a model `M'` of a signature `S` in a bicategory `C'` with generator images `G'`
(`Categorification.Diagrams.BicatInterp`) and a strict pseudofunctor `Φ : C' → C`, the
*pushforward* `M'.push Φ` is the model of `S` in `C` sending a region `x` to `Φ (M'.obj x)` and a
strand to the image under `Φ` of its image, and `G'.push Φ` sends a generator to the image under
`Φ` of its image. The interpretation of a diagram for the pushforward is the image under `Φ` of
its interpretation for `M'`, up to the identifications of the images of the boundary words
(`interp_push`); hence a linear combination of diagrams killed by `M'` is killed by its
pushforward when `Φ` is linear on 2-morphisms (`freeLift_push_eq_zero`).

This is used to compare the `sl₂` model of a strong 2-representation on a bicategory with a
rescaled grading (`Categorification.TwoRep.Regrade`) with the model of a `Q`-strong
2-representation along an `α_i`-string when `(α_i, α_i) ≠ 2`.

## Main definitions and results

* `StrictPseudofunctor` normal forms: `sp_map₂_whiskerLeft`, `sp_map₂_whiskerRight`,
  `sp_map₂_associator_hom`, … (structural 2-morphisms go to structural 2-morphisms up to the
  equalities `map_comp`, `map_id`);
* `Model.push`, `GenImg.push`, `push_lift_map`, `push_lift_map₂`;
* `core_push`, `layerI_push`, `mapChain_push`, `interp_push`, `freeLift_push_eq_zero`.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ w₃ w₄ u₀ u₁ u₂ v₂ v₃

/-! ## Strict pseudofunctors on structural 2-morphisms -/

section Strict

variable {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁} [Bicategory.{w₂, v₂} C]
  (Φ : StrictPseudofunctor C' C)

theorem sp_map₂_whiskerLeft {a b c : C'} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    Φ.map₂ (f ◁ η) =
      eqToHom (Φ.map_comp f g) ≫ Φ.map f ◁ Φ.map₂ η ≫ eqToHom (Φ.map_comp f h).symm := by
  rw [Φ.map₂_whisker_left, Φ.mapComp_eq_eqToIso, Φ.mapComp_eq_eqToIso]
  simp

theorem sp_map₂_whiskerRight {a b c : C'} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    Φ.map₂ (η ▷ h) =
      eqToHom (Φ.map_comp f h) ≫ Φ.map₂ η ▷ Φ.map h ≫ eqToHom (Φ.map_comp g h).symm := by
  rw [Φ.map₂_whisker_right, Φ.mapComp_eq_eqToIso, Φ.mapComp_eq_eqToIso]
  simp

theorem sp_map₂_associator_hom {a b c d : C'} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    Φ.map₂ (α_ f g h).hom =
      eqToHom (by rw [Φ.map_comp, Φ.map_comp]) ≫ (α_ (Φ.map f) (Φ.map g) (Φ.map h)).hom ≫
        eqToHom (by rw [Φ.map_comp, Φ.map_comp]) := by
  rw [Φ.map₂_associator]
  simp [Φ.mapComp_eq_eqToIso, eqToHom_whiskerRight, whiskerLeft_eqToHom]

theorem sp_map₂_associator_inv {a b c d : C'} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    Φ.map₂ (α_ f g h).inv =
      eqToHom (by rw [Φ.map_comp, Φ.map_comp]) ≫ (α_ (Φ.map f) (Φ.map g) (Φ.map h)).inv ≫
        eqToHom (by rw [Φ.map_comp, Φ.map_comp]) := by
  rw [← cancel_epi (Φ.map₂ (α_ f g h).hom), ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
    PrelaxFunctor.map₂_id, sp_map₂_associator_hom]
  simp

theorem sp_map₂_leftUnitor_hom {a b : C'} (f : a ⟶ b) :
    Φ.map₂ (λ_ f).hom = eqToHom (by rw [Φ.map_comp, Φ.map_id]) ≫ (λ_ (Φ.map f)).hom := by
  rw [Φ.map₂_left_unitor]
  simp [Φ.mapComp_eq_eqToIso, Φ.mapId_eq_eqToIso, eqToHom_whiskerRight]

theorem sp_map₂_leftUnitor_inv {a b : C'} (f : a ⟶ b) :
    Φ.map₂ (λ_ f).inv = (λ_ (Φ.map f)).inv ≫ eqToHom (by rw [Φ.map_comp, Φ.map_id]) := by
  rw [← cancel_epi (Φ.map₂ (λ_ f).hom), ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
    PrelaxFunctor.map₂_id, sp_map₂_leftUnitor_hom]
  simp

theorem sp_map₂_rightUnitor_hom {a b : C'} (f : a ⟶ b) :
    Φ.map₂ (ρ_ f).hom = eqToHom (by rw [Φ.map_comp, Φ.map_id]) ≫ (ρ_ (Φ.map f)).hom := by
  rw [Φ.map₂_right_unitor]
  simp [Φ.mapComp_eq_eqToIso, Φ.mapId_eq_eqToIso, whiskerLeft_eqToHom]

theorem sp_map₂_rightUnitor_inv {a b : C'} (f : a ⟶ b) :
    Φ.map₂ (ρ_ f).inv = (ρ_ (Φ.map f)).inv ≫ eqToHom (by rw [Φ.map_comp, Φ.map_id]) := by
  rw [← cancel_epi (Φ.map₂ (ρ_ f).hom), ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
    PrelaxFunctor.map₂_id, sp_map₂_rightUnitor_hom]
  simp

theorem sp_map₂_eqToHom {a b : C'} {f g : a ⟶ b} (h : f = g) :
    Φ.map₂ (eqToHom h) = eqToHom (congrArg Φ.map h) := by
  subst h; simp

end Strict

/-! ## The pushforward of a model -/

section Push

variable {S : Signature.{u₀, u₁, u₂}} {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁}
  [Bicategory.{w₂, v₂} C] (Φ : StrictPseudofunctor C' C)

/-- **The pushforward of a model** along a strict pseudofunctor. -/
def Model.push (M' : Model S C') : Model S C where
  obj x := Φ.obj (M'.obj x)
  strandAt c x y hx hy := Φ.map (M'.strandAt c x y hx hy)

variable (M' : Model S C')

/-- The pseudofunctor of the pushforward on 1-morphisms. -/
theorem push_lift_map {a b : FB S} (f : a ⟶ b) :
    (M'.push Φ).lift.map f = Φ.map (M'.lift.map f) := by
  induction f with
  | of f => rfl
  | id a => exact (Φ.map_id _).symm
  | comp f g ihf ihg => exact (congrArg₂ (· ≫ ·) ihf ihg).trans (Φ.map_comp _ _).symm

theorem id_conj₂ {D : Type*} [Category D] {X X' : D} (e : X = X') (w : X' ⟶ X')
    (hw : 𝟙 X' = w) : 𝟙 X = eqToHom e ≫ w ≫ eqToHom e.symm := by
  subst e hw; simp

theorem whiskerLeft_conj₂ {a b c : C} {f f' : a ⟶ b} {g g' h h' : b ⟶ c} {X Y : a ⟶ c}
    (ef : f = f') (eg : g = g') (eh : h = h') (η : g' ⟶ h') (p : f ≫ g = X) (q : X = f' ≫ g')
    (r : f' ≫ h' = Y) (s : Y = f ≫ h) :
    f ◁ (eqToHom eg ≫ η ≫ eqToHom eh.symm) =
      eqToHom p ≫ (eqToHom q ≫ f' ◁ η ≫ eqToHom r) ≫ eqToHom s := by
  subst ef eg eh p r; simp

theorem whiskerRight_conj₂ {a b c : C} {f f' g g' : a ⟶ b} {h h' : b ⟶ c} {X Y : a ⟶ c}
    (ef : f = f') (eg : g = g') (eh : h = h') (η : f' ⟶ g') (p : f ≫ h = X) (q : X = f' ≫ h')
    (r : g' ≫ h' = Y) (s : Y = g ≫ h) :
    (eqToHom ef ≫ η ≫ eqToHom eg.symm) ▷ h =
      eqToHom p ≫ (eqToHom q ≫ η ▷ h' ≫ eqToHom r) ≫ eqToHom s := by
  subst ef eg eh p r; simp

theorem associator_conj₂ {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    {X Y : a ⟶ d} (ef : f = f') (eg : g = g') (eh : h = h') (p : (f ≫ g) ≫ h = X)
    (q : X = (f' ≫ g') ≫ h') (r : f' ≫ g' ≫ h' = Y) (s : Y = f ≫ g ≫ h) :
    (α_ f g h).hom = eqToHom p ≫ (eqToHom q ≫ (α_ f' g' h').hom ≫ eqToHom r) ≫ eqToHom s := by
  subst ef eg eh p r; simp

theorem associator_inv_conj₂ {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    {X Y : a ⟶ d} (ef : f = f') (eg : g = g') (eh : h = h') (p : f ≫ g ≫ h = X)
    (q : X = f' ≫ g' ≫ h') (r : (f' ≫ g') ≫ h' = Y) (s : Y = (f ≫ g) ≫ h) :
    (α_ f g h).inv = eqToHom p ≫ (eqToHom q ≫ (α_ f' g' h').inv ≫ eqToHom r) ≫ eqToHom s := by
  subst ef eg eh p r; simp

theorem leftUnitor_conj₂ {a b : C} {f f' : a ⟶ b} {X : a ⟶ b} (ef : f = f')
    (p : 𝟙 a ≫ f = X) (q : X = 𝟙 a ≫ f') :
    (λ_ f).hom = eqToHom p ≫ (eqToHom q ≫ (λ_ f').hom) ≫ eqToHom ef.symm := by
  subst ef p; simp

theorem leftUnitor_inv_conj₂ {a b : C} {f f' : a ⟶ b} {X : a ⟶ b} (ef : f = f')
    (p : 𝟙 a ≫ f' = X) (q : X = 𝟙 a ≫ f) :
    (λ_ f).inv = eqToHom ef ≫ ((λ_ f').inv ≫ eqToHom p) ≫ eqToHom q := by
  subst ef p; simp

theorem rightUnitor_conj₂ {a b : C} {f f' : a ⟶ b} {X : a ⟶ b} (ef : f = f')
    (p : f ≫ 𝟙 b = X) (q : X = f' ≫ 𝟙 b) :
    (ρ_ f).hom = eqToHom p ≫ (eqToHom q ≫ (ρ_ f').hom) ≫ eqToHom ef.symm := by
  subst ef p; simp

theorem rightUnitor_inv_conj₂ {a b : C} {f f' : a ⟶ b} {X : a ⟶ b} (ef : f = f')
    (p : f' ≫ 𝟙 b = X) (q : X = f ≫ 𝟙 b) :
    (ρ_ f).inv = eqToHom ef ≫ ((ρ_ f').inv ≫ eqToHom p) ≫ eqToHom q := by
  subst ef p; simp

/-- The pseudofunctor of the pushforward on 2-morphisms: that of `M'` followed by `Φ`, up to the
identifications `push_lift_map`. -/
theorem push_lift_map₂ {a b : FB S} {f g : a ⟶ b} (η : f ⟶ g) :
    (M'.push Φ).lift.map₂ η = eqToHom (push_lift_map Φ M' f) ≫
      Φ.map₂ (M'.lift.map₂ η) ≫ eqToHom (push_lift_map Φ M' g).symm := by
  induction η using Quot.ind with
  | mk η =>
  induction η with
  | id f =>
    exact id_conj₂ (push_lift_map Φ M' f) _ (by
      rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.id f)) = 𝟙 _ from
        PrelaxFunctor.map₂_id _ _, PrelaxFunctor.map₂_id]; rfl)
  | vcomp η θ ihη ihθ =>
    show (M'.push Φ).lift.map₂ (Quot.mk _ η) ≫ (M'.push Φ).lift.map₂ (Quot.mk _ θ) = _
    rw [ihη, ihθ]
    exact eqToHom_conj_assoc (push_lift_map Φ M' _) (push_lift_map Φ M' _)
      (push_lift_map Φ M' _) _ _ _
      ((PrelaxFunctor.map₂_comp _ _ _).symm.trans
        (congrArg Φ.map₂ (M'.lift.map₂_comp _ _).symm))
  | whisker_left f η ih =>
    show (M'.push Φ).lift.map f ◁ (M'.push Φ).lift.map₂ (Quot.mk _ η) = _
    rw [ih, show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.whisker_left f η)) =
      M'.lift.map f ◁ M'.lift.map₂ (Quot.mk _ η) from rfl]
    erw [sp_map₂_whiskerLeft]
    exact whiskerLeft_conj₂ (push_lift_map Φ M' f) (push_lift_map Φ M' _) (push_lift_map Φ M' _)
      _ _ _ _ _
  | whisker_right h η ih =>
    show (M'.push Φ).lift.map₂ (Quot.mk _ η) ▷ (M'.push Φ).lift.map h = _
    rw [ih, show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.whisker_right h η)) =
      M'.lift.map₂ (Quot.mk _ η) ▷ M'.lift.map h from rfl]
    erw [sp_map₂_whiskerRight]
    exact whiskerRight_conj₂ (push_lift_map Φ M' _) (push_lift_map Φ M' _) (push_lift_map Φ M' h)
      _ _ _ _ _
  | associator f g h =>
    show (α_ _ _ _).hom = _
    rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.associator f g h)) =
      (α_ (M'.lift.map f) (M'.lift.map g) (M'.lift.map h)).hom from rfl]
    erw [sp_map₂_associator_hom]
    exact associator_conj₂ (push_lift_map Φ M' f) (push_lift_map Φ M' g) (push_lift_map Φ M' h)
      _ _ _ _
  | associator_inv f g h =>
    show (α_ _ _ _).inv = _
    rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.associator_inv f g h)) =
      (α_ (M'.lift.map f) (M'.lift.map g) (M'.lift.map h)).inv from rfl]
    erw [sp_map₂_associator_inv]
    exact associator_inv_conj₂ (push_lift_map Φ M' f) (push_lift_map Φ M' g)
      (push_lift_map Φ M' h) _ _ _ _
  | right_unitor f =>
    show (ρ_ _).hom = _
    rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.right_unitor f)) =
      (ρ_ (M'.lift.map f)).hom from rfl]
    erw [sp_map₂_rightUnitor_hom]
    exact rightUnitor_conj₂ (push_lift_map Φ M' f) _ _
  | right_unitor_inv f =>
    show (ρ_ _).inv = _
    rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.right_unitor_inv f)) =
      (ρ_ (M'.lift.map f)).inv from rfl]
    erw [sp_map₂_rightUnitor_inv]
    exact rightUnitor_inv_conj₂ (push_lift_map Φ M' f) _ _
  | left_unitor f =>
    show (λ_ _).hom = _
    rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.left_unitor f)) =
      (λ_ (M'.lift.map f)).hom from rfl]
    erw [sp_map₂_leftUnitor_hom]
    exact leftUnitor_conj₂ (push_lift_map Φ M' f) _ _
  | left_unitor_inv f =>
    show (λ_ _).inv = _
    rw [show M'.lift.map₂ (Quot.mk _ (FreeBicategory.Hom₂.left_unitor_inv f)) =
      (λ_ (M'.lift.map f)).inv from rfl]
    erw [sp_map₂_leftUnitor_inv]
    exact leftUnitor_inv_conj₂ (push_lift_map Φ M' f) _ _

end Push

/-! ## Generator images and layers -/

section GenPush

variable {S : Signature.{u₀, u₁, u₂}} {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁}
  [Bicategory.{w₂, v₂} C] (Φ : StrictPseudofunctor C' C) {M' : Model S C'} (G' : GenImg M')

/-- **The pushforward of generator images**: the image under `Φ` of the image of a generator,
between the identified images of its boundary words. -/
def GenImg.push : GenImg (M'.push Φ) where
  gen g a b ha hb hd hde hc hce :=
    eqToHom (push_lift_map Φ M' (fw a (S.dom g) b hd hde)) ≫
      Φ.map₂ (G'.gen g a b ha hb hd hde hc hce) ≫
      eqToHom (push_lift_map Φ M' (fw a (S.cod g) b hc hce)).symm

omit G' in
/-- The normal form of the image of a layer for the pushforward, abstractly. -/
theorem key_push {x y z w : C'} {F₀ F₃ : x ⟶ w} {P : x ⟶ y} {X Y : y ⟶ z} {Q : z ⟶ w}
    {U₀ U₃ : Φ.obj x ⟶ Φ.obj w} {P₀ : Φ.obj x ⟶ Φ.obj y} {X₀ Y₀ : Φ.obj y ⟶ Φ.obj z}
    {Q₀ : Φ.obj z ⟶ Φ.obj w}
    (A : F₀ ⟶ P ≫ (X ≫ Q)) (B : P ≫ (Y ≫ Q) ⟶ F₃) (g : X ⟶ Y)
    (ep : P₀ = Φ.map P) (eq : Q₀ = Φ.map Q) (ex : X₀ = Φ.map X) (ey : Φ.map Y = Y₀)
    (e₀ : U₀ = Φ.map F₀) (e₁ : Φ.map (P ≫ (X ≫ Q)) = P₀ ≫ (X₀ ≫ Q₀))
    (e₂ : P₀ ≫ (Y₀ ≫ Q₀) = Φ.map (P ≫ (Y ≫ Q))) (e₃ : Φ.map F₃ = U₃) :
    (eqToHom e₀ ≫ Φ.map₂ A ≫ eqToHom e₁) ≫
        (P₀ ◁ ((eqToHom ex ≫ Φ.map₂ g ≫ eqToHom ey) ▷ Q₀) ≫
          (eqToHom e₂ ≫ Φ.map₂ B ≫ eqToHom e₃)) =
      eqToHom e₀ ≫ Φ.map₂ (A ≫ P ◁ (g ▷ Q) ≫ B) ≫ eqToHom e₃ := by
  subst ep eq ex ey e₀ e₃
  rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp, sp_map₂_whiskerLeft, sp_map₂_whiskerRight]
  simp [whiskerLeft_comp, whiskerLeft_eqToHom]

/-- **The image of a layer for the pushforward** is the image under `Φ` of its image for `M'`,
between the identified images of the boundary words. -/
theorem core_push {L : Layer S} (hv : L.Valid) (s m n t : S.Region) (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n)
    (ht : S.endR n L.right = t) :
    core (G'.push Φ) hv s m n t hl hm ha hb ht =
      eqToHom (push_lift_map Φ M' _) ≫ Φ.map₂ (core G' hv s m n t hl hm ha hb ht) ≫
        eqToHom (push_lift_map Φ M' _).symm := by
  unfold core
  rw [push_lift_map₂, push_lift_map₂]
  unfold midK
  dsimp only [GenImg.push]
  exact key_push Φ _ _ _ (push_lift_map Φ M' _) (push_lift_map Φ M' _) (push_lift_map Φ M' _)
    (push_lift_map Φ M' _).symm _ _ _ _

end GenPush

/-! ## The interpretation of the pushforward -/

section InterpPush

open CategoryTheory.Limits

variable {S : Signature.{u₀, u₁, u₂}} {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁}
  [Bicategory.{w₂, v₂} C] (Φ : StrictPseudofunctor C' C) {M' : Model S C'} (G' : GenImg M')
  [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C', HasZeroObject (a ⟶ b)] [∀ a b : C', Preadditive (a ⟶ b)]

omit [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C', Preadditive (a ⟶ b)] in
/-- The image of an admissible object for the pushforward is the image under `Φ` of its image. -/
theorem objI_push {s t : S.Region} {a : Obj S} (h : Cond s t a) :
    objI (M'.push Φ) s t a = Φ.map (objI M' s t a) := by
  rw [objI_pos _ _ h, objI_pos _ _ h]
  exact push_lift_map Φ M' _

omit [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C', HasZeroObject (a ⟶ b)] [∀ a b : C', Preadditive (a ⟶ b)] in
theorem conj_push₂ {a b : C'} {X Y X' Y' : a ⟶ b} {U U' V V' : Φ.obj a ⟶ Φ.obj b}
    (x : X' ⟶ Y') (p₁ : U = U') (p₂ : U' = Φ.map X') (p₃ : Φ.map Y' = V') (p₄ : V' = V)
    (q₁ : U = Φ.map X) (q₂ : X = X') (q₃ : Y' = Y) (q₄ : Φ.map Y = V) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ Φ.map₂ x ≫ eqToHom p₃) ≫ eqToHom p₄ =
      eqToHom q₁ ≫ Φ.map₂ (eqToHom q₂ ≫ x ≫ eqToHom q₃) ≫ eqToHom q₄ := by
  subst q₂ q₃ p₂ p₁ p₃ p₄
  simp

/-- **The image of a layer for the pushforward** is the image under `Φ` of its image. -/
theorem layerI_push {s t : S.Region} {L : Layer S} (hv : L.Valid) (h : Cond s t L.dom) :
    layerI (G'.push Φ) s t L hv =
      eqToHom (objI_push Φ h) ≫ Φ.map₂ (layerI G' s t L hv) ≫
        eqToHom (objI_push Φ (h.cod hv)).symm := by
  rw [layerI_pos _ _ _ hv h, layerI_pos _ _ _ hv h, coreC_eq, coreC_eq, core_push]
  exact conj_push₂ Φ _ _ _ _ _ _ _ _ _

omit [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C', HasZeroObject (a ⟶ b)] [∀ a b : C', Preadditive (a ⟶ b)] in
theorem comp_conj_push {a b : C'} {X Y Z : a ⟶ b} {U V W : Φ.obj a ⟶ Φ.obj b} (x : X ⟶ Y)
    (y : Y ⟶ Z) (p₁ : U = Φ.map X) (p₂ : Φ.map Y = V) (p₃ : V = Φ.map Y) (p₄ : Φ.map Z = W) :
    (eqToHom p₁ ≫ Φ.map₂ x ≫ eqToHom p₂) ≫ (eqToHom p₃ ≫ Φ.map₂ y ≫ eqToHom p₄) =
      eqToHom p₁ ≫ Φ.map₂ (x ≫ y) ≫ eqToHom p₄ := by
  subst p₁ p₂ p₄
  simp

omit [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C', HasZeroObject (a ⟶ b)] [∀ a b : C', Preadditive (a ⟶ b)] in
theorem eqToHom_conj_push {a b : C'} {X : a ⟶ b} {U : Φ.obj a ⟶ Φ.obj b} (r : U = U)
    (r' : X = X) (p : U = Φ.map X) (q : Φ.map X = U) :
    eqToHom r = eqToHom p ≫ Φ.map₂ (eqToHom r') ≫ eqToHom q := by
  subst p
  simp

/-- **The images of chains of layers for the pushforward** are the images under `Φ`. -/
theorem mapChain_push {s t : S.Region} : ∀ (ls : List (Layer S)) (a b : Obj S)
    (hc : Chain a ls b) (ha : Cond s t a),
    (interp (G'.push Φ) s t).mapChain a ls b hc =
      eqToHom (objI_push Φ ha) ≫ Φ.map₂ ((interp G' s t).mapChain a ls b hc) ≫
        eqToHom (objI_push Φ (ha.chain hc)).symm
  | [], a, b, hc, ha => by
    obtain rfl : a = b := hc
    exact eqToHom_conj_push Φ _ _ _ _
  | L :: ls, a, b, hc, ha => by
    obtain ⟨hv, rfl, hc'⟩ := hc
    simp only [Interpretation.mapChain, eqToHom_refl, Category.id_comp]
    rw [layerI_push Φ G' hv ha, mapChain_push ls L.cod b hc' (ha.cod hv)]
    exact comp_conj_push Φ _ _ _ _ _ _

/-- **The interpretation of the pushforward** (`interp_push`): the image of a diagram with
admissible source is the image under `Φ` of its image for `M'`, between the identified images of
the boundary words. -/
theorem interp_push {s t : S.Region} {a b : Obj S} (d : a ⟶ b) (ha : Cond s t a) :
    (interp (G'.push Φ) s t).functor.map d =
      eqToHom (objI_push Φ ha) ≫ Φ.map₂ ((interp G' s t).functor.map d) ≫
        eqToHom (objI_push Φ (ha.chain (Diagram.chain d))).symm :=
  mapChain_push Φ G' _ a b _ ha

omit [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C', HasZeroObject (a ⟶ b)] [∀ a b : C', Preadditive (a ⟶ b)] in
set_option backward.isDefEq.respectTransparency false in
/-- The linear extensions of two functors on diagrams intertwined, on each diagram, by an
`R`-linear map are intertwined by it. -/
theorem freeLift_conj {R : Type*} [CommRing R] {D D' : Type*} [Category D] [Preadditive D]
    [Linear R D] [Category D'] [Preadditive D'] [Linear R D'] {F : Obj S ⥤ D'} {G : Obj S ⥤ D}
    {a b : Obj S} (T : (F.obj a ⟶ F.obj b) →ₗ[R] (G.obj a ⟶ G.obj b))
    (h : ∀ d : a ⟶ b, G.map d = T (F.map d)) (f : LinDiagram R a b) :
    (freeLift R G).map f = T ((freeLift R F).map f) := by
  induction f using Finsupp.induction_linear with
  | zero => exact ((freeLift R G).map_zero _ _).trans (by rw [Functor.map_zero, map_zero])
  | add f g hf hg => exact ((freeLift R G).map_add).trans (by rw [hf, hg, Functor.map_add, map_add])
  | single d r => rw [freeLift_map_single, freeLift_map_single, map_smul, h]

variable {R : Type*} [CommRing R] [∀ a b : C, Linear R (a ⟶ b)] [∀ a b : C', Linear R (a ⟶ b)]
  (hadd : ∀ {a b : C'} {f g : a ⟶ b} (x y : f ⟶ g), Φ.map₂ (x + y) = Φ.map₂ x + Φ.map₂ y)
  (hsmul : ∀ {a b : C'} {f g : a ⟶ b} (r : R) (x : f ⟶ g), Φ.map₂ (r • x) = r • Φ.map₂ x)

omit [∀ a b : C, HasZeroObject (a ⟶ b)] [∀ a b : C', HasZeroObject (a ⟶ b)] in
include hadd hsmul in
/-- Conjugating the image under `Φ` by transports, as a linear map. -/
def conjΦ {a b : C'} {X Y : a ⟶ b} {U V : Φ.obj a ⟶ Φ.obj b} (p : U = Φ.map X)
    (q : Φ.map Y = V) : (X ⟶ Y) →ₗ[R] (U ⟶ V) where
  toFun x := eqToHom p ≫ Φ.map₂ x ≫ eqToHom q
  map_add' x y := by rw [hadd, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r x := by rw [hsmul, Linear.smul_comp, Linear.comp_smul]; rfl

include hadd hsmul in
/-- **The linear extension of the interpretation of the pushforward**: a linear combination of
diagrams with admissible boundaries killed by the interpretation of `M'` is killed by that of the
pushforward, for `Φ` linear on 2-morphisms. -/
theorem freeLift_push_eq_zero {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (f : LinDiagram R a b)
    (hf : (freeLift R (interp G' s t).functor).map f = 0) :
    (freeLift R (interp (G'.push Φ) s t).functor).map f = 0 := by
  have key := freeLift_conj (F := (interp G' s t).functor)
    (G := (interp (G'.push Φ) s t).functor)
    (conjΦ Φ hadd hsmul (objI_push Φ ha) (objI_push Φ hb).symm)
    (fun d => interp_push Φ G' d ha) f
  rw [key]
  exact (congrArg _ hf).trans (map_zero _)

end InterpPush


end Categorification.Diagrams.BicatInterp
