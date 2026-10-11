/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissibleDescent
import Categorification.Diagrams.BicatInterpPseudo

/-!
# Zero-object-free presented pseudofunctor

The admissible quotient maps assemble to a pseudofunctor on the horizontal
reverse of the original presented bicategory. The composition constraint is the
image of `splitR`; identities, composition, both whiskerings, associators and
unitors satisfy the pseudofunctor laws. Only the zero-object-free word and free
coherence helpers of `PresPseudo` are reused, not its total interpreter.
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams PresPseudo
universe w₁ w₂ u₀ u₁ u₂ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C}
variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]
variable (G : GenImg M) {P : Presentation S k}
  (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
    (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
  [S.IsEven]
namespace AdmissiblePseudo

def map₂ {a b : RevBicat P.Bicat} {x y : a ⟶ b} (η : x ⟶ y) : map₁ M x ⟶ map₁ M y :=
  admissibleQuotientMap G P hrel Signature.IsEven.odd_eq_false (condW x) (condW y) η

theorem map₂_id' {a b : RevBicat P.Bicat} (x : a ⟶ b) : map₂ G hrel (𝟙 x) = 𝟙 (map₁ M x) :=
  admissibleQuotientMap_id G P hrel Signature.IsEven.odd_eq_false (condW x)

theorem map₂_comp' {a b : RevBicat P.Bicat} {x y z : a ⟶ b} (η : x ⟶ y) (θ : y ⟶ z) :
    map₂ G hrel (η ≫ θ) = map₂ G hrel η ≫ map₂ G hrel θ :=
  admissibleQuotientMap_comp G P hrel Signature.IsEven.odd_eq_false (condW x) (condW y) (condW z) η θ

theorem map₂_eqToHom' {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (e : (x : Presentation.Bicat.Hom b.as a.as).obj = (y : Presentation.Bicat.Hom b.as a.as).obj) :
    map₂ G hrel (rev₂ (eqToHom (congrArg P.obj e))) =
      M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word e) (okW x) (endW x) (okW y) (endW y))) :=
  admissibleQuotientMap_eqToHom G P hrel Signature.IsEven.odd_eq_false (condW x) (condW y) e

theorem map₂_whiskerLeft {a b c : RevBicat P.Bicat} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    map₂ G hrel (f ◁ η) =
      (mapComp f g).hom ≫ map₁ M f ◁ map₂ G hrel η ≫ (mapComp f h).inv := by
  let F : Presentation.Bicat.Hom b.as a.as := f
  let X : Presentation.Bicat.Hom c.as b.as := g
  let Y : Presentation.Bicat.Hom c.as b.as := h
  have hwa : Cond c.as.region a.as.region (X.obj.whisker (Obj.nil c.as.region) F.obj.word) :=
    ⟨(condW (X.comp F)).1, (condW (X.comp F)).2.1, rfl⟩
  have hwb : Cond c.as.region a.as.region (Y.obj.whisker (Obj.nil c.as.region) F.obj.word) :=
    ⟨(condW (Y.comp F)).1, (condW (Y.comp F)).2.1, rfl⟩
  have key := admissibleQuotientMap_whisk_coherent G P hrel Signature.IsEven.odd_eq_false
    (η : P.obj X.obj ⟶ P.obj Y.obj) (s' := c.as.region) (t' := a.as.region) (condW X) (condW Y)
    (u := Obj.nil c.as.region) (v := F.obj.word) rfl trivial rfl (okW F) (endW F) hwa hwb
    ((splitIso c.as.region X.obj.word F.obj.word b.as.region a.as.region (okW X) (endW X)
      (okW F) (endW F)).hom ≫ _ ◁ (ρ_ _).inv)
    (_ ◁ (ρ_ _).hom ≫ (splitIso c.as.region Y.obj.word F.obj.word b.as.region a.as.region
      (okW Y) (endW Y) (okW F) (endW F)).inv)
  have step : map₂ G hrel (f ◁ η)
      = admissibleQuotientMap G P hrel Signature.IsEven.odd_eq_false hwa hwb
          (P.whisk (η : P.obj X.obj ⟶ P.obj Y.obj) (Obj.nil c.as.region) F.obj.word) := by
        dsimp only [map₂, RevBicat.whiskerLeft_def, Presentation.Bicat.whiskerRight_eq,
          Presentation.wRAt]
        erw [admissibleQuotientMap_comp G P hrel Signature.IsEven.odd_eq_false _ hwa,
          admissibleQuotientMap_comp G P hrel Signature.IsEven.odd_eq_false hwa hwb,
          admissibleQuotientMap_eqToHom G P hrel Signature.IsEven.odd_eq_false hwb _
            (Obj.tensor_eq_whisker_nil_of_start F.obj Y.start_eq).symm,
          admissibleQuotientMap_eqToHom G P hrel Signature.IsEven.odd_eq_false _ hwa
            (Obj.tensor_eq_whisker_nil_of_start F.obj X.start_eq)]
        erw [lift_map₂_eqToHom, lift_map₂_eqToHom, eqToHom_refl, eqToHom_refl,
          Category.id_comp, Category.comp_id]
  dsimp only [F, X, Y, Obj.nil_start, Obj.nil_word] at key
  apply step.trans
  apply key.trans
  show _ = (mapComp f g).hom ≫ map₁ M f ◁ map₂ G hrel η ≫ (mapComp f h).inv
  ·
        change M.lift.map₂ ((splitR f g).hom ≫ fwR f ◁ (ρ_ (fwR g)).inv) ≫
          map₁ M f ◁ (map₂ G hrel η ▷ 𝟙 _) ≫
            M.lift.map₂ (fwR f ◁ (ρ_ (fwR h)).hom ≫ (splitR f h).inv) = _
        simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_rightUnitor_hom,
          lift_map₂_rightUnitor_inv]
        change ((mapComp f g).hom ≫ map₁ M f ◁ (ρ_ (map₁ M g)).inv) ≫
          map₁ M f ◁ (map₂ G hrel η ▷ 𝟙 _) ≫
            map₁ M f ◁ (ρ_ (map₁ M h)).hom ≫ (mapComp f h).inv = _
        rw [Category.assoc]
        congr 1
        rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
        congr 2
        erw [whiskerRight_id]
        simp only [Category.assoc]
        erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem map₂_whiskerRight {a b c : RevBicat P.Bicat} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    map₂ G hrel (η ▷ h) =
      (mapComp f h).hom ≫ map₂ G hrel η ▷ map₁ M h ≫ (mapComp g h).inv := by
  let X : Presentation.Bicat.Hom b.as a.as := f
  let Y : Presentation.Bicat.Hom b.as a.as := g
  let H : Presentation.Bicat.Hom c.as b.as := h
  have hwa : Cond c.as.region a.as.region (X.obj.whisker H.obj []) :=
    ⟨by simpa using (condW (H.comp X)).1, by simpa using (condW (H.comp X)).2.1, H.start_eq⟩
  have hwb : Cond c.as.region a.as.region (Y.obj.whisker H.obj []) :=
    ⟨by simpa using (condW (H.comp Y)).1, by simpa using (condW (H.comp Y)).2.1, H.start_eq⟩
  have ex : (H.comp X).obj.word = (X.obj.whisker H.obj []).word := by simp
  have ey : (H.comp Y).obj.word = (Y.obj.whisker H.obj []).word := by simp
  have key := admissibleQuotientMap_whisk_coherent G P hrel Signature.IsEven.odd_eq_false
    (η : P.obj X.obj ⟶ P.obj Y.obj) (s' := c.as.region) (t' := a.as.region) (condW X) (condW Y)
    (u := H.obj) (v := []) H.start_eq (okW H) (endW H) trivial rfl hwa hwb
    (eqToHom (fw_eq ex.symm hwa.1 hwa.2.1 (okW (H.comp X)) (endW (H.comp X))) ≫
      (splitIso c.as.region H.obj.word X.obj.word b.as.region a.as.region (okW H) (endW H)
        (okW X) (endW X)).hom ≫ (λ_ _).inv)
    ((λ_ _).hom ≫ (splitIso c.as.region H.obj.word Y.obj.word b.as.region a.as.region (okW H)
        (endW H) (okW Y) (endW Y)).inv ≫
      eqToHom (fw_eq ey (okW (H.comp Y)) (endW (H.comp Y)) hwb.1 hwb.2.1))
  dsimp only [X, Y, H, Signature.endR] at key
  calc map₂ G hrel (η ▷ h)
      = M.lift.map₂ (eqToHom (fw_eq ex (okW (H.comp X)) (endW (H.comp X)) hwa.1 hwa.2.1)) ≫
          admissibleQuotientMap G P hrel Signature.IsEven.odd_eq_false hwa hwb
            (P.whisk (η : P.obj X.obj ⟶ P.obj Y.obj) H.obj []) ≫
          M.lift.map₂ (eqToHom (fw_eq ey.symm hwb.1 hwb.2.1 (okW (H.comp Y)) (endW (H.comp Y)))) := by
        dsimp only [map₂, RevBicat.whiskerRight_def, Presentation.Bicat.whiskerLeft_eq,
          Presentation.wL]
        erw [admissibleQuotientMap_comp G P hrel Signature.IsEven.odd_eq_false _ hwa,
          admissibleQuotientMap_comp G P hrel Signature.IsEven.odd_eq_false hwa hwb,
          admissibleQuotientMap_eqToHom G P hrel Signature.IsEven.odd_eq_false hwb _
            (Obj.tensor_eq_whisker_nil H.obj Y.obj).symm,
          admissibleQuotientMap_eqToHom G P hrel Signature.IsEven.odd_eq_false _ hwa
            (Obj.tensor_eq_whisker_nil H.obj X.obj)]
        rfl
    _ = _ := by erw [key]
    _ = _ := by
        change M.lift.map₂ (eqToHom (fw_eq ex (okW (H.comp X)) (endW (H.comp X)) hwa.1 hwa.2.1)) ≫
          (M.lift.map₂ (eqToHom (fw_eq ex.symm hwa.1 hwa.2.1 (okW (H.comp X)) (endW (H.comp X))) ≫
            (splitR f h).hom ≫ (λ_ (fwR f ≫ fwR h)).inv) ≫
              (𝟙 _) ◁ (map₂ G hrel η ▷ map₁ M h) ≫
                M.lift.map₂ ((λ_ (fwR g ≫ fwR h)).hom ≫ (splitR g h).inv ≫
                  eqToHom (fw_eq ey (okW (H.comp Y)) (endW (H.comp Y)) hwb.1 hwb.2.1))) ≫
          M.lift.map₂ (eqToHom (fw_eq ey.symm hwb.1 hwb.2.1 (okW (H.comp Y)) (endW (H.comp Y)))) = _
        simp only [PrelaxFunctor.map₂_comp, lift_map₂_eqToHom, lift_map₂_leftUnitor_hom,
          lift_map₂_leftUnitor_inv, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp]
        erw [id_whiskerLeft]
        repeat' erw [Category.assoc]
        erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id]
        rfl

theorem map₂_associator' {a b c d : RevBicat P.Bicat} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    map₂ G hrel (α_ f g h).hom =
      (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map₁ M h ≫
        (α_ (map₁ M f) (map₁ M g) (map₁ M h)).hom ≫ map₁ M f ◁ (mapComp g h).inv ≫
          (mapComp f (g ≫ h)).inv := by
  rw [show (α_ f g h).hom = rev₂ (x := (f ≫ g) ≫ h) (y := f ≫ (g ≫ h))
      (eqToHom (congrArg P.obj (Obj.tensor_assoc _ _ _).symm)) from rfl,
    map₂_eqToHom' G hrel (Obj.tensor_assoc _ _ _).symm, lift_map₂_eq M _ ((splitR (f ≫ g) h).hom ≫ (splitR f g).hom ▷ fwR h ≫
      (α_ (fwR f) (fwR g) (fwR h)).hom ≫ fwR f ◁ (splitR g h).inv ≫ (splitR f (g ≫ h)).inv)]
  simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight,
    lift_map₂_associator_hom]
  rfl

theorem map₂_leftUnitor' {a b : RevBicat P.Bicat} (f : a ⟶ b) :
    map₂ G hrel (λ_ f).hom =
      (mapComp (𝟙 a) f).hom ≫ (Iso.refl (map₁ M (𝟙 a))).hom ▷ map₁ M f ≫
        (λ_ (map₁ M f)).hom := by
  rw [show (λ_ f).hom = rev₂ (x := 𝟙 a ≫ f) (y := f)
      (eqToHom (congrArg P.obj (Obj.tensor_nil _ _))) from rfl,
    map₂_eqToHom' G hrel (Obj.tensor_nil _ _),
    lift_map₂_eq M _ ((splitR (𝟙 a) f).hom ≫ (λ_ (fwR f)).hom)]
  simp only [Iso.refl_hom, id_whiskerRight]
  erw [PrelaxFunctor.map₂_comp, Category.id_comp]
  rfl

theorem map₂_rightUnitor' {a b : RevBicat P.Bicat} (f : a ⟶ b) :
    map₂ G hrel (ρ_ f).hom =
      (mapComp f (𝟙 b)).hom ≫ map₁ M f ◁ (Iso.refl (map₁ M (𝟙 b))).hom ≫
        (ρ_ (map₁ M f)).hom := by
  refine (map₂_eqToHom' G hrel (x := f ≫ 𝟙 b) (y := f)
    (Obj.nil_tensor (f : Presentation.Bicat.Hom b.as a.as).start_eq)).trans ?_
  rw [lift_map₂_eq M _ ((splitR f (𝟙 b)).hom ≫ (ρ_ (fwR f)).hom)]
  simp only [Iso.refl_hom, whiskerLeft_id]
  erw [PrelaxFunctor.map₂_comp, Category.id_comp]
  rfl
end AdmissiblePseudo

/-- Zero-object-free descent to the original presented bicategory. -/
def admissiblePseudofunctor : Pseudofunctor (RevBicat P.Bicat) C where
  obj a := M.lift.obj (fo a.as.region)
  map x := map₁ M x
  map₂ η := AdmissiblePseudo.map₂ G hrel η
  map₂_id x := AdmissiblePseudo.map₂_id' G hrel x
  map₂_comp η θ := AdmissiblePseudo.map₂_comp' G hrel η θ
  mapId _ := Iso.refl _
  mapComp f g := PresPseudo.mapComp f g
  map₂_whisker_left f _ _ η := AdmissiblePseudo.map₂_whiskerLeft G hrel f η
  map₂_whisker_right η h := AdmissiblePseudo.map₂_whiskerRight G hrel η h
  map₂_associator f g h := AdmissiblePseudo.map₂_associator' G hrel f g h
  map₂_left_unitor f := AdmissiblePseudo.map₂_leftUnitor' G hrel f
  map₂_right_unitor f := AdmissiblePseudo.map₂_rightUnitor' G hrel f

end Categorification.Diagrams.BicatInterp