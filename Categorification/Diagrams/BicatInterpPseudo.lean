/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterp
import Categorification.Diagrams.RevBicat
import StringDiagrams.Bicategory

/-!
# The universal property of a presented 2-category

Let `P` be a presentation of an even signature `S` (so that `P.Bicat` is a strict bicategory:
regions, well-formed words, and the morphisms of the presented category). A model `M` of `S` in a
bicategory `C` with generator images `G` (`Categorification.Diagrams.BicatInterp`) whose
interpretations respect the relations of `P` for **all** outer regions gives a pseudofunctor
`RevBicat P.Bicat ⥤ᵖ C` (`presPseudofunctor`): a region `x` goes to `M.obj x`, a word to the
composite of the images of its strands, and a 2-morphism with outer regions `s`, `t` to its image
under the interpretation `P.lift` in the hom category `C(M.obj t, M.obj s)`. Its composition
constraints are the images of the canonical isomorphisms of the free bicategory splitting a word
(`splitIso`), and its compatibility with horizontal composition is the whiskering law of the
interpretation (`mapChain_whisker`), which extends to the presented category by linearity
(`lift_whisk`).

The source is `RevBicat P.Bicat` rather than `P.Bicat` because a 1-morphism of `P.Bicat` is a word
read from its left region to its right region, while its image goes from the image of the right
region to that of the left region (the convention of Khovanov–Lauda and Cautis–Lauda: `E_i 1_λ`
is a 1-morphism `λ → λ + α_i`, drawn with `λ` on the right).

## Main results

* `lift_whisk`: the image of a whiskering `u ⊗ f ⊗ v` of an arbitrary morphism of the presented
  category is the image of `f` whiskered by the images of `v` and `u`, up to images of free
  2-morphisms;
* `presPseudofunctor`, with `presPseudofunctor_map₂` (on each hom category it is the
  interpretation `P.lift`, transported to the images of words) and `presPseudofunctor_mapComp`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w w₁ w₂ u₀ u₁ u₂ v v₂

variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C] {M : Model S C}

open CategoryTheory.Limits
open scoped ZeroObject

section Ctx

variable {R : Type w} [CommRing R] [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear R]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear R]
  [∀ a b : C, Limits.HasZeroObject (a ⟶ b)] (G : GenImg M) (P : Presentation.{w, v} S R)
  (hP : ∀ s₀ t₀ : S.Region, P.Respects (interp G s₀ t₀).functor)

section Whisk

theorem whiskerLeft_add' {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ := (precomp c f).map_add

theorem add_whiskerRight' {a b c : C} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η + θ) ▷ h = η ▷ h + θ ▷ h := (postcomp a h).map_add

theorem whiskerLeft_zero'' {a b c : C} (f : a ⟶ b) (g h : b ⟶ c) :
    f ◁ (0 : g ⟶ h) = 0 := (precomp c f).map_zero g h

theorem zero_whiskerRight'' {a b c : C} (f g : a ⟶ b) (h : b ⟶ c) :
    (0 : f ⟶ g) ▷ h = 0 := (postcomp a h).map_zero f g

theorem whiskerLeft_smul' {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (r : R) (η : g ⟶ h) :
    f ◁ (r • η) = r • f ◁ η := (precomp c f).map_smul r η

theorem smul_whiskerRight' {a b c : C} {f g : a ⟶ b} (r : R) (η : f ⟶ g) (h : b ⟶ c) :
    (r • η) ▷ h = r • η ▷ h := (postcomp a h).map_smul r η

set_option backward.isDefEq.respectTransparency false in
/-- **Whiskering in the presented category**: for a morphism `f : a ⟶ b` of the presented
category with `a`, `b` admissible for the outer regions `s`, `t`, the image of `u ⊗ f ⊗ v` (for
the outer regions `u.start` and `t'`, the end of `v`) is the image of `f` whiskered by the images
of `v` and `u`, up to arbitrary images of free 2-morphisms. -/
theorem lift_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {s t s' t' : S.Region}
    (ha : Cond s t a) (hb : Cond s t b) {u : Obj S} {v : List S.Colour} (hs' : u.start = s')
    (hu : S.ok s' u.word) (hue : S.endR s' u.word = s) (hvv : S.ok t v)
    (ht' : S.endR t v = t') (hwa : Cond s' t' (a.whisker u v))
    (hwb : Cond s' t' (b.whisker u v))
    (φ : fw s' (a.whisker u v).word t' hwa.1 hwa.2.1 ⟶
      fw t v t' hvv ht' ≫ (fw s a.word t ha.1 ha.2.1 ≫ fw s' u.word s hu hue))
    (ψ : fw t v t' hvv ht' ≫ (fw s b.word t hb.1 hb.2.1 ≫ fw s' u.word s hu hue) ⟶
      fw s' (b.whisker u v).word t' hwb.1 hwb.2.1) :
    eqToHom (objI_pos s' t' hwa).symm ≫ (P.lift (hP s' t')).map (P.whisk f u v) ≫
        eqToHom (objI_pos s' t' hwb) =
      M.lift.map₂ φ ≫
        M.lift.map (fw t v t' hvv ht') ◁
          ((eqToHom (objI_pos s t ha).symm ≫ (P.lift (hP s t)).map f ≫
              eqToHom (objI_pos s t hb)) ▷ M.lift.map (fw s' u.word s hu hue)) ≫
        M.lift.map₂ ψ := by
  subst hs'
  subst ht'
  obtain ⟨g, rfl⟩ := P.lin_surjective f
  have hw : a.WhiskerOK u v := ⟨hu, hue.trans ha.2.2.symm,
    show S.ok (S.endR a.start a.word) v by rw [ha.2.2, ha.2.1]; exact hvv⟩
  rw [Presentation.whisk_lin, Presentation.lift_lin, Presentation.lift_lin,
    LinDiagram.whisk_of_ok _ hw]
  induction g using Finsupp.induction_linear with
  | zero =>
    erw [LinDiagram.whisker_zero]
    simp only [Functor.map_zero, zero_comp, comp_zero, zero_whiskerRight'', whiskerLeft_zero'']
  | add g₁ g₂ h₁ h₂ =>
    erw [LinDiagram.whisker_add]
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
    erw [Functor.map_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add, add_whiskerRight', whiskerLeft_add']
  | single d r =>
    rw [LinDiagram.whisker_single, freeLift_map_single, freeLift_map_single]
    simp only [Linear.smul_comp, Linear.comp_smul, smul_whiskerRight', whiskerLeft_smul']
    congr 1
    exact mapChain_whisker G hu hue hvv d.1 _ rfl a (a.whisker u v) b rfl d.2
      (Diagram.whisker d u v hw).2 ha hb hwa hwb φ ψ

end Whisk

/-! ## The pseudofunctor -/

section Pseudo

variable [S.IsEven]

namespace PresPseudo

variable {P}

theorem okW {l m : P.Bicat} (x : Presentation.Bicat.Hom l m) : S.ok l.region x.obj.word :=
  x.start_eq ▸ x.wf

theorem endW {l m : P.Bicat} (x : Presentation.Bicat.Hom l m) :
    S.endR l.region x.obj.word = m.region :=
  x.start_eq ▸ x.endR_eq

theorem condW {l m : P.Bicat} (x : Presentation.Bicat.Hom l m) :
    Cond l.region m.region x.obj :=
  ⟨okW x, endW x, x.start_eq⟩

/-- The free 1-morphism of the word of a 1-morphism of `RevBicat P.Bicat`. -/
abbrev fwR {a b : RevBicat P.Bicat} (x : a ⟶ b) : fo (S := S) a.as.region ⟶ fo b.as.region :=
  fw b.as.region (x : Presentation.Bicat.Hom b.as a.as).obj.word a.as.region (okW x) (endW x)

/-- The splitting of the word of a composite in `RevBicat P.Bicat`. -/
abbrev splitR {a b c : RevBicat P.Bicat} (f : a ⟶ b) (g : b ⟶ c) : fwR (f ≫ g) ≅ fwR f ≫ fwR g :=
  splitIso c.as.region (g : Presentation.Bicat.Hom c.as b.as).obj.word
    (f : Presentation.Bicat.Hom b.as a.as).obj.word b.as.region a.as.region (okW g) (endW g)
    (okW f) (endW f)

variable (M) in
/-- The image of a 1-morphism `x : a ⟶ b` of `RevBicat P.Bicat` (a word from `b` to `a`). -/
abbrev map₁ {a b : RevBicat P.Bicat} (x : a ⟶ b) :
    M.lift.obj (fo a.as.region) ⟶ M.lift.obj (fo b.as.region) :=
  M.word b.as.region (x : Presentation.Bicat.Hom b.as a.as).obj.word a.as.region (okW x)
    (endW x)

/-- The image of a 2-morphism: the interpretation with the outer regions of its boundary,
transported to the images of the words. -/
def map₂ {a b : RevBicat P.Bicat} {x y : a ⟶ b} (η : x ⟶ y) : map₁ M x ⟶ map₁ M y :=
  eqToHom (show map₁ M x = (P.lift (hP b.as.region a.as.region)).obj
        (P.obj (x : Presentation.Bicat.Hom b.as a.as).obj) from
      (objI_pos _ _ (condW (x : Presentation.Bicat.Hom b.as a.as))).symm) ≫
    (P.lift (hP b.as.region a.as.region)).map
      (η : P.obj (x : Presentation.Bicat.Hom b.as a.as).obj ⟶
        P.obj (y : Presentation.Bicat.Hom b.as a.as).obj) ≫
    eqToHom (show (P.lift (hP b.as.region a.as.region)).obj
        (P.obj (y : Presentation.Bicat.Hom b.as a.as).obj) = map₁ M y from
      objI_pos _ _ (condW (y : Presentation.Bicat.Hom b.as a.as)))

/-- The composition constraint: the image of the splitting of a concatenated word. -/
def mapComp {a b c : RevBicat P.Bicat} (f : a ⟶ b) (g : b ⟶ c) :
    map₁ M (f ≫ g) ≅ map₁ M f ≫ map₁ M g :=
  M.lift.map₂Iso (splitIso c.as.region (g : Presentation.Bicat.Hom c.as b.as).obj.word
    (f : Presentation.Bicat.Hom b.as a.as).obj.word b.as.region a.as.region (okW g) (endW g)
    (okW f) (endW f))


theorem mapComp_hom {a b c : RevBicat P.Bicat} (f : a ⟶ b) (g : b ⟶ c) :
    (mapComp (M := M) f g).hom =
      M.lift.map₂ (splitIso c.as.region (g : Presentation.Bicat.Hom c.as b.as).obj.word
        (f : Presentation.Bicat.Hom b.as a.as).obj.word b.as.region a.as.region (okW g) (endW g)
        (okW f) (endW f)).hom := rfl

theorem mapComp_inv {a b c : RevBicat P.Bicat} (f : a ⟶ b) (g : b ⟶ c) :
    (mapComp (M := M) f g).inv =
      M.lift.map₂ (splitIso c.as.region (g : Presentation.Bicat.Hom c.as b.as).obj.word
        (f : Presentation.Bicat.Hom b.as a.as).obj.word b.as.region a.as.region (okW g) (endW g)
        (okW f) (endW f)).inv := rfl

theorem map₂_id' {a b : RevBicat P.Bicat} (x : a ⟶ b) : map₂ G hP (𝟙 x) = 𝟙 (map₁ M x) := by
  have e : (P.lift (hP b.as.region a.as.region)).map (𝟙 x) = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  simp only [map₂]
  rw [e, Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem map₂_comp' {a b : RevBicat P.Bicat} {x y z : a ⟶ b} (η : x ⟶ y) (θ : y ⟶ z) :
    map₂ G hP (η ≫ θ) = map₂ G hP η ≫ map₂ G hP θ := by
  have e : (P.lift (hP b.as.region a.as.region)).map (η ≫ θ) =
      (P.lift (hP b.as.region a.as.region)).map η ≫ (P.lift (hP b.as.region a.as.region)).map θ :=
    Functor.map_comp _ _ _
  simp only [map₂, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  rw [← Category.assoc]
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem map₂_whiskerLeft {a b c : RevBicat P.Bicat} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    map₂ G hP (f ◁ η) =
      (mapComp f g).hom ≫ map₁ M f ◁ map₂ G hP η ≫ (mapComp f h).inv := by
  let F : Presentation.Bicat.Hom b.as a.as := f
  let X : Presentation.Bicat.Hom c.as b.as := g
  let Y : Presentation.Bicat.Hom c.as b.as := h
  have hwa : Cond c.as.region a.as.region (X.obj.whisker (Obj.nil c.as.region) F.obj.word) :=
    ⟨(condW (X.comp F)).1, (condW (X.comp F)).2.1, rfl⟩
  have hwb : Cond c.as.region a.as.region (Y.obj.whisker (Obj.nil c.as.region) F.obj.word) :=
    ⟨(condW (Y.comp F)).1, (condW (Y.comp F)).2.1, rfl⟩
  have key := lift_whisk G P hP (η : P.obj X.obj ⟶ P.obj Y.obj) (condW X) (condW Y)
    (u := Obj.nil c.as.region) (v := F.obj.word) rfl trivial rfl (okW F) (endW F) hwa hwb
    ((splitIso c.as.region X.obj.word F.obj.word b.as.region a.as.region (okW X) (endW X)
      (okW F) (endW F)).hom ≫ _ ◁ (ρ_ _).inv)
    (_ ◁ (ρ_ _).hom ≫ (splitIso c.as.region Y.obj.word F.obj.word b.as.region a.as.region
      (okW Y) (endW Y) (okW F) (endW F)).inv)
  calc map₂ G hP (f ◁ η)
      = eqToHom (objI_pos _ _ hwa).symm ≫ (P.lift (hP c.as.region a.as.region)).map
          (P.whisk (η : P.obj X.obj ⟶ P.obj Y.obj) (Obj.nil c.as.region) F.obj.word) ≫
          eqToHom (objI_pos _ _ hwb) := by
        simp only [map₂, RevBicat.whiskerLeft_def, Presentation.Bicat.whiskerRight_eq,
          Presentation.wRAt, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
          eqToHom_trans]
        rfl
    _ = _ := key
    _ = _ := by
        simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_rightUnitor_hom,
          lift_map₂_rightUnitor_inv, mapComp_hom, mapComp_inv, Category.assoc]
        congr 1
        rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
        congr 2
        erw [whiskerRight_id]
        simp only [Category.assoc]
        erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
        rfl


/-- A morphism of the presented category as a 2-morphism of `RevBicat P.Bicat`. -/
abbrev rev₂ {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (k : P.obj (x : Presentation.Bicat.Hom b.as a.as).obj ⟶
      P.obj (y : Presentation.Bicat.Hom b.as a.as).obj) : x ⟶ y := k

theorem map₂_eqToHom' {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (e : (x : Presentation.Bicat.Hom b.as a.as).obj = (y : Presentation.Bicat.Hom b.as a.as).obj) :
    map₂ G hP (rev₂ (eqToHom (congrArg P.obj e))) =
      M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word e) (okW x) (endW x) (okW y) (endW y))) := by
  have e' : (P.lift (hP b.as.region a.as.region)).map (eqToHom (congrArg P.obj e)) =
      eqToHom (congrArg (P.lift (hP b.as.region a.as.region)).obj (congrArg P.obj e)) :=
    eqToHom_map _ _
  simp only [map₂]
  rw [e', lift_map₂_eqToHom, eqToHom_trans, eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
theorem map₂_whiskerRight {a b c : RevBicat P.Bicat} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    map₂ G hP (η ▷ h) =
      (mapComp f h).hom ≫ map₂ G hP η ▷ map₁ M h ≫ (mapComp g h).inv := by
  let X : Presentation.Bicat.Hom b.as a.as := f
  let Y : Presentation.Bicat.Hom b.as a.as := g
  let H : Presentation.Bicat.Hom c.as b.as := h
  have hwa : Cond c.as.region a.as.region (X.obj.whisker H.obj []) :=
    ⟨by simpa using (condW (H.comp X)).1, by simpa using (condW (H.comp X)).2.1, H.start_eq⟩
  have hwb : Cond c.as.region a.as.region (Y.obj.whisker H.obj []) :=
    ⟨by simpa using (condW (H.comp Y)).1, by simpa using (condW (H.comp Y)).2.1, H.start_eq⟩
  have ex : (H.comp X).obj.word = (X.obj.whisker H.obj []).word := by simp
  have ey : (H.comp Y).obj.word = (Y.obj.whisker H.obj []).word := by simp
  have key := lift_whisk G P hP (η : P.obj X.obj ⟶ P.obj Y.obj) (condW X) (condW Y)
    (u := H.obj) (v := []) H.start_eq (okW H) (endW H) trivial rfl hwa hwb
    (eqToHom (fw_eq ex.symm hwa.1 hwa.2.1 (okW (H.comp X)) (endW (H.comp X))) ≫
      (splitIso c.as.region H.obj.word X.obj.word b.as.region a.as.region (okW H) (endW H)
        (okW X) (endW X)).hom ≫ (λ_ _).inv)
    ((λ_ _).hom ≫ (splitIso c.as.region H.obj.word Y.obj.word b.as.region a.as.region (okW H)
        (endW H) (okW Y) (endW Y)).inv ≫
      eqToHom (fw_eq ey (okW (H.comp Y)) (endW (H.comp Y)) hwb.1 hwb.2.1))
  calc map₂ G hP (η ▷ h)
      = M.lift.map₂ (eqToHom (fw_eq ex (okW (H.comp X)) (endW (H.comp X)) hwa.1 hwa.2.1)) ≫
          (eqToHom (objI_pos _ _ hwa).symm ≫ (P.lift (hP c.as.region a.as.region)).map
            (P.whisk (η : P.obj X.obj ⟶ P.obj Y.obj) H.obj []) ≫
            eqToHom (objI_pos _ _ hwb)) ≫
          M.lift.map₂ (eqToHom (fw_eq ey.symm hwb.1 hwb.2.1 (okW (H.comp Y)) (endW (H.comp Y)))) := by
        simp only [map₂, RevBicat.whiskerRight_def, Presentation.Bicat.whiskerLeft_eq,
          Presentation.wL, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
          eqToHom_trans, lift_map₂_eqToHom]
        rfl
    _ = _ := by rw [key]
    _ = _ := by
        simp only [PrelaxFunctor.map₂_comp, lift_map₂_eqToHom, lift_map₂_leftUnitor_hom,
          lift_map₂_leftUnitor_inv, mapComp_hom, mapComp_inv, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp]
        erw [id_whiskerLeft]
        simp only [Category.assoc]
        erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id]
        rfl


theorem map₂_associator' {a b c d : RevBicat P.Bicat} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    map₂ G hP (α_ f g h).hom =
      (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map₁ M h ≫
        (α_ (map₁ M f) (map₁ M g) (map₁ M h)).hom ≫ map₁ M f ◁ (mapComp g h).inv ≫
          (mapComp f (g ≫ h)).inv := by
  rw [show (α_ f g h).hom = rev₂ (x := (f ≫ g) ≫ h) (y := f ≫ (g ≫ h))
      (eqToHom (congrArg P.obj (Obj.tensor_assoc _ _ _).symm)) from rfl,
    map₂_eqToHom' G hP (Obj.tensor_assoc _ _ _).symm, lift_map₂_eq M _ ((splitR (f ≫ g) h).hom ≫ (splitR f g).hom ▷ fwR h ≫
      (α_ (fwR f) (fwR g) (fwR h)).hom ≫ fwR f ◁ (splitR g h).inv ≫ (splitR f (g ≫ h)).inv)]
  simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight,
    lift_map₂_associator_hom, mapComp_hom, mapComp_inv]
  rfl

theorem map₂_leftUnitor' {a b : RevBicat P.Bicat} (f : a ⟶ b) :
    map₂ G hP (λ_ f).hom =
      (mapComp (𝟙 a) f).hom ≫ (Iso.refl (map₁ M (𝟙 a))).hom ▷ map₁ M f ≫
        (λ_ (map₁ M f)).hom := by
  rw [show (λ_ f).hom = rev₂ (x := 𝟙 a ≫ f) (y := f)
      (eqToHom (congrArg P.obj (Obj.tensor_nil _ _))) from rfl,
    map₂_eqToHom' G hP (Obj.tensor_nil _ _),
    lift_map₂_eq M _ ((splitR (𝟙 a) f).hom ≫ (λ_ (fwR f)).hom)]
  simp only [mapComp_hom, Iso.refl_hom, id_whiskerRight]
  erw [PrelaxFunctor.map₂_comp, Category.id_comp]
  rfl

theorem map₂_rightUnitor' {a b : RevBicat P.Bicat} (f : a ⟶ b) :
    map₂ G hP (ρ_ f).hom =
      (mapComp f (𝟙 b)).hom ≫ map₁ M f ◁ (Iso.refl (map₁ M (𝟙 b))).hom ≫
        (ρ_ (map₁ M f)).hom := by
  refine (map₂_eqToHom' G hP (x := f ≫ 𝟙 b) (y := f)
    (Obj.nil_tensor (f : Presentation.Bicat.Hom b.as a.as).start_eq)).trans ?_
  rw [lift_map₂_eq M _ ((splitR f (𝟙 b)).hom ≫ (ρ_ (fwR f)).hom)]
  simp only [mapComp_hom, Iso.refl_hom, whiskerLeft_id]
  erw [PrelaxFunctor.map₂_comp, Category.id_comp]
  rfl

end PresPseudo

open PresPseudo in
/-- **The universal property of a presented 2-category**: a model whose interpretations respect
the relations of `P` for all outer regions defines a pseudofunctor out of the presented
bicategory (read with 1-morphisms from the right region to the left region). -/
def presPseudofunctor : Pseudofunctor (RevBicat P.Bicat) C where
  obj a := M.lift.obj (fo a.as.region)
  map x := map₁ M x
  map₂ η := PresPseudo.map₂ G hP η
  map₂_id x := map₂_id' G hP x
  map₂_comp η θ := map₂_comp' G hP η θ
  mapId _ := Iso.refl _
  mapComp f g := PresPseudo.mapComp f g
  map₂_whisker_left f _ _ η := map₂_whiskerLeft G hP f η
  map₂_whisker_right η h := map₂_whiskerRight G hP η h
  map₂_associator f g h := map₂_associator' G hP f g h
  map₂_left_unitor f := map₂_leftUnitor' G hP f
  map₂_right_unitor f := map₂_rightUnitor' G hP f

end Pseudo

end Ctx

end Categorification.Diagrams.BicatInterp
