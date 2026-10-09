/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KarBicategory

/-!
# Functoriality of the additive Karoubi envelope of a bicategory

The additive Karoubi envelope `Kar B = KarBicat (MatBicat B)` of a bicategory with preadditive hom
categories and additive whiskering (J. Brundan, A. P. Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3, §1.5 and §6; `StringDiagrams.Super.KarBicategory`) is functorial:

* `MatBicat.mapPseudofunctor F : MatBicat A ⥤ᵖ MatBicat C` for a pseudofunctor `F : A ⥤ᵖ C` which
  is additive on 2-morphisms: formal direct sums go to formal direct sums of the images, matrices of
  2-morphisms to the matrices of their images, and the composition and unit constraints are the
  diagonal matrices of those of `F`;
* `KarBicat.mapPseudofunctor F : KarBicat A ⥤ᵖ KarBicat C` for any pseudofunctor: `(f, e) ↦ (F f, F e)`,
  with the constraints of `F` composed with the idempotents.

Compositions of 1-morphisms are written in diagrammatic order.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification

open CategoryTheory Bicategory StringDiagrams StringDiagrams.Mat_

universe w v u w' v' u'


/-! ## Diagonal matrices -/

namespace DiagMat

variable {D : Type*} [Category D] [Preadditive D] {ι κ : Type} [Fintype ι] [Fintype κ]
  {X X' X'' : ι → D} {Y : κ → D}

/-- The diagonal matrix with entries `φ i`. -/
abbrev diagMat (φ : ∀ i, X i ⟶ X' i) : (⟨ι, X⟩ : Mat_ D) ⟶ ⟨ι, X'⟩ :=
  permMat (Equiv.refl ι) φ

theorem diagMat_comp_diagMat (φ : ∀ i, X i ⟶ X' i) (ψ : ∀ i, X' i ⟶ X'' i) :
    diagMat φ ≫ diagMat ψ = diagMat (fun i => φ i ≫ ψ i) :=
  (permMat_comp_permMat (Equiv.refl ι) φ (Equiv.refl ι) ψ).trans
    (permMat_congr (fun _ => rfl) _ _ fun _ => by simp)

theorem diagMat_comp_permMat (φ : ∀ i, X i ⟶ X' i) (e : ι ≃ κ) (ψ : ∀ i, X' i ⟶ Y (e i)) :
    diagMat φ ≫ permMat e ψ = permMat e (fun i => φ i ≫ ψ i) :=
  (permMat_comp_permMat (Equiv.refl ι) φ e ψ).trans
    (permMat_congr (fun _ => rfl) _ _ fun _ => by simp)

theorem permMat_comp_diagMat {Y' : κ → D} (e : ι ≃ κ) (ψ : ∀ i, X i ⟶ Y (e i))
    (χ : ∀ j, Y j ⟶ Y' j) :
    permMat e ψ ≫ diagMat χ = permMat e (fun i => ψ i ≫ χ (e i)) :=
  (permMat_comp_permMat e ψ (Equiv.refl κ) χ).trans
    (permMat_congr (fun _ => rfl) _ _ fun _ => by simp)

theorem diagMat_id : diagMat (fun i => 𝟙 (X i)) = 𝟙 (⟨ι, X⟩ : Mat_ D) :=
  permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp

end DiagMat

open DiagMat

/-! ## The additive envelope -/

namespace MatBicat

open StringDiagrams.MatBicat

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
  [PreadditiveBicategory A] {C : Type u'} [Bicategory.{w', v'} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [PreadditiveBicategory C]
  (F : Pseudofunctor A C)
  (hF : ∀ {a b : A} {f g : a ⟶ b} (η θ : f ⟶ g), F.map₂ (η + θ) = F.map₂ η + F.map₂ θ)

/-- `F.map₂` as an additive map. -/
def map₂Hom {a b : A} (f g : a ⟶ b) : (f ⟶ g) →+ (F.map f ⟶ F.map g) :=
  AddMonoidHom.mk' (fun η => F.map₂ η) (fun η θ => hF η θ)

include hF in
theorem map₂_zero' {a b : A} (f g : a ⟶ b) : F.map₂ (0 : f ⟶ g) = 0 :=
  (map₂Hom F hF f g).map_zero

include hF in
theorem map₂_sum' {a b : A} {f g : a ⟶ b} {ι : Type*} (s : Finset ι) (η : ι → (f ⟶ g)) :
    F.map₂ (∑ i ∈ s, η i) = ∑ i ∈ s, F.map₂ (η i) :=
  map_sum (map₂Hom F hF f g) η s

variable {a b c d : MatBicat A}

/-- The image of a formal direct sum. -/
abbrev mapObj (M : a ⟶ b) : (⟨F.obj a.obj⟩ : MatBicat C) ⟶ ⟨F.obj b.obj⟩ :=
  ⟨M.ι, fun i => F.map (M.X i)⟩

/-- The image of a matrix of 2-morphisms. -/
abbrev mapHom {M N : a ⟶ b} (φ : M ⟶ N) : mapObj F M ⟶ mapObj F N :=
  fun i j => F.map₂ (φ i j)

include hF in
theorem mapHom_permMat {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → (a.obj ⟶ b.obj)}
    {Y : κ → (a.obj ⟶ b.obj)} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) :
    mapHom F (M := ⟨ι, X⟩) (N := ⟨κ, Y⟩) (permMat e φ) =
      permMat (X := fun i => F.map (X i)) (Y := fun j => F.map (Y j)) e
        (fun i => F.map₂ (φ i)) := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  by_cases h : e i = j
  · subst h
    simp only [mapHom, permMat_apply_self]
  · simp only [mapHom]
    rw [permMat_apply_of_ne e φ h, permMat_apply_of_ne _ _ h, map₂_zero' F hF]

include hF in
theorem mapHom_id (M : a ⟶ b) : mapHom F (𝟙 M) = 𝟙 (mapObj F M) := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  by_cases h : i = j
  · subst h
    simp only [mapHom]
    rw [StringDiagrams.MatBicat.id_apply_self, StringDiagrams.MatBicat.id_apply_self, F.map₂_id]
  · simp only [mapHom]
    rw [StringDiagrams.MatBicat.id_apply_of_ne (mapObj F M) i j h]
    exact (congrArg F.map₂ (StringDiagrams.MatBicat.id_apply_of_ne M i j h)).trans
      (map₂_zero' F hF _ _)

include hF in
theorem mapHom_comp {M N P : a ⟶ b} (φ : M ⟶ N) (ψ : N ⟶ P) :
    mapHom F (φ ≫ ψ) = mapHom F φ ≫ mapHom F ψ := by
  apply CategoryTheory.Mat_.hom_ext
  intro i k
  simp only [mapHom, StringDiagrams.MatBicat.comp_apply, map₂_sum' F hF, F.map₂_comp]

/-- The diagonal matrix of a family of isomorphisms. -/
def diagIso {D : Type*} [Category D] [Preadditive D] {ι : Type} [Fintype ι] {X Y : ι → D}
    (φ : ∀ i, X i ≅ Y i) : (⟨ι, X⟩ : Mat_ D) ≅ ⟨ι, Y⟩ where
  hom := permMat (Equiv.refl ι) fun i => (φ i).hom
  inv := permMat (Equiv.refl ι) fun i => (φ i).inv
  hom_inv_id := (permMat_comp_permMat (Equiv.refl ι) (fun i => (φ i).hom) (Equiv.refl ι)
    (fun i => (φ i).inv)).trans (permMat_eq_id _ (fun _ => rfl) _ fun i => by simp)
  inv_hom_id := (permMat_comp_permMat (Equiv.refl ι) (fun i => (φ i).inv) (Equiv.refl ι)
    (fun i => (φ i).hom)).trans (permMat_eq_id _ (fun _ => rfl) _ fun i => by simp)

theorem diag_conj_apply {D : Type*} [Category D] [Preadditive D] {ι κ : Type} [Fintype ι]
    [Fintype κ] {X X' : ι → D} {Y Y' : κ → D} (φ : ∀ i, X i ⟶ X' i)
    (g : (⟨ι, X'⟩ : Mat_ D) ⟶ ⟨κ, Y⟩) (ψ : ∀ j, Y j ⟶ Y' j) (i : ι) (j : κ) :
    (permMat (Equiv.refl ι) φ ≫ g ≫ permMat (Equiv.refl κ) ψ) i j = φ i ≫ g i j ≫ ψ j := by
  exact (permMat_comp_apply (Equiv.refl ι) φ (g ≫ permMat (Equiv.refl κ) ψ) i j).trans
    (congrArg (φ i ≫ ·) (comp_permMat_apply (Equiv.refl κ) ψ g i j))

include hF in
theorem mapHom_whiskerLeft (M : a ⟶ b) {N N' : b ⟶ c} (η : N ⟶ N') :
    mapHom F (M ◁ η) = (diagIso fun x : M.ι × N.ι => F.mapComp (M.X x.1) (N.X x.2)).hom ≫
      mapObj F M ◁ mapHom F η ≫
        (diagIso fun x : M.ι × N'.ι => F.mapComp (M.X x.1) (N'.X x.2)).inv := by
  apply CategoryTheory.Mat_.hom_ext
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  refine Eq.trans ?_ (diag_conj_apply _ _ _ _ _).symm
  simp only [mapHom, StringDiagrams.MatBicat.whiskerLeft_eq, hcomp_apply]
  by_cases h : x₁ = y₁
  · subst h
    rw [StringDiagrams.MatBicat.id_apply_self, StringDiagrams.MatBicat.id_apply_self]
    simp only [hcomp₂, id_whiskerRight, Category.id_comp, F.map₂_whisker_left]
  · rw [StringDiagrams.MatBicat.id_apply_of_ne M x₁ y₁ h,
      StringDiagrams.MatBicat.id_apply_of_ne (mapObj F M) x₁ y₁ h, hcomp₂_zero_left,
      hcomp₂_zero_left, map₂_zero' F hF, Limits.zero_comp, Limits.comp_zero]

include hF in
theorem mapHom_whiskerRight {M M' : a ⟶ b} (η : M ⟶ M') (N : b ⟶ c) :
    mapHom F (η ▷ N) = (diagIso fun x : M.ι × N.ι => F.mapComp (M.X x.1) (N.X x.2)).hom ≫
      mapHom F η ▷ mapObj F N ≫
        (diagIso fun x : M'.ι × N.ι => F.mapComp (M'.X x.1) (N.X x.2)).inv := by
  apply CategoryTheory.Mat_.hom_ext
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  refine Eq.trans ?_ (diag_conj_apply _ _ _ _ _).symm
  simp only [mapHom, StringDiagrams.MatBicat.whiskerRight_eq, hcomp_apply]
  by_cases h : x₂ = y₂
  · subst h
    rw [StringDiagrams.MatBicat.id_apply_self, StringDiagrams.MatBicat.id_apply_self]
    simp only [hcomp₂, Bicategory.whiskerLeft_id, Category.comp_id, F.map₂_whisker_right]
  · rw [StringDiagrams.MatBicat.id_apply_of_ne N x₂ y₂ h,
      StringDiagrams.MatBicat.id_apply_of_ne (mapObj F N) x₂ y₂ h, hcomp₂_zero_right,
      hcomp₂_zero_right, map₂_zero' F hF, Limits.zero_comp, Limits.comp_zero]

theorem diag_whiskerRight {ι : Type} [Fintype ι] {X X' : ι → (a.obj ⟶ b.obj)}
    (φ : ∀ i, X i ⟶ X' i) (N : b ⟶ c) :
    (diagMat φ : (⟨ι, X⟩ : a ⟶ b) ⟶ ⟨ι, X'⟩) ▷ N =
      diagMat (X := fun x : ι × N.ι => X x.1 ≫ N.X x.2)
        (X' := fun x : ι × N.ι => X' x.1 ≫ N.X x.2) (fun x => φ x.1 ▷ N.X x.2) :=
  (permMat_whiskerRight (Equiv.refl ι) φ N).trans
    (permMat_congr (fun _ => rfl) _ _ fun _ => by rw [eqToHom_refl]; exact Category.comp_id _)

theorem diag_whiskerLeft (M : a ⟶ b) {ι : Type} [Fintype ι] {X X' : ι → (b.obj ⟶ c.obj)}
    (φ : ∀ i, X i ⟶ X' i) :
    M ◁ (diagMat φ : (⟨ι, X⟩ : b ⟶ c) ⟶ ⟨ι, X'⟩) =
      diagMat (X := fun x : M.ι × ι => M.X x.1 ≫ X x.2)
        (X' := fun x : M.ι × ι => M.X x.1 ≫ X' x.2) (fun x => M.X x.1 ◁ φ x.2) :=
  (whiskerLeft_permMat M (Equiv.refl ι) φ).trans
    (permMat_congr (fun _ => rfl) _ _ fun _ => by rw [eqToHom_refl]; exact Category.comp_id _)

include hF in
theorem mapHom_associator (M : a ⟶ b) (N : b ⟶ c) (P : c ⟶ d) :
    mapHom F (α_ M N P).hom =
      (diagIso fun x : (M.ι × N.ι) × P.ι => F.mapComp (M.X x.1.1 ≫ N.X x.1.2) (P.X x.2)).hom ≫
        (diagIso fun x : M.ι × N.ι => F.mapComp (M.X x.1) (N.X x.2)).hom ▷ mapObj F P ≫
          (α_ (mapObj F M) (mapObj F N) (mapObj F P)).hom ≫
            mapObj F M ◁ (diagIso fun x : N.ι × P.ι => F.mapComp (N.X x.1) (P.X x.2)).inv ≫
              (diagIso fun x : M.ι × (N.ι × P.ι) =>
                F.mapComp (M.X x.1) (N.X x.2.1 ≫ P.X x.2.2)).inv := by
  rw [StringDiagrams.MatBicat.associator_hom_eq, StringDiagrams.MatBicat.associator_hom_eq]
  refine (mapHom_permMat F hF _ _).trans ?_
  simp only [diagIso]
  rw [diag_whiskerRight, diag_whiskerLeft, diagMat_comp_diagMat]
  erw [permMat_comp_diagMat, diagMat_comp_permMat, diagMat_comp_permMat]
  refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
  rw [eqToHom_refl, Category.comp_id]
  exact F.map₂_associator _ _ _

include hF in
theorem mapHom_leftUnitor (M : a ⟶ b) :
    mapHom F (λ_ M).hom =
      (diagIso fun x : PUnit × M.ι => F.mapComp (𝟙 a.obj) (M.X x.2)).hom ≫
        (diagIso fun _ : PUnit => F.mapId a.obj).hom ▷ mapObj F M ≫ (λ_ (mapObj F M)).hom := by
  rw [StringDiagrams.MatBicat.leftUnitor_hom_eq, StringDiagrams.MatBicat.leftUnitor_hom_eq]
  refine (mapHom_permMat F hF _ _).trans ?_
  simp only [diagIso]
  rw [diag_whiskerRight]
  erw [diagMat_comp_permMat, diagMat_comp_permMat]
  refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
  rw [eqToHom_refl, Category.comp_id]
  exact F.map₂_left_unitor _

include hF in
theorem mapHom_rightUnitor (M : a ⟶ b) :
    mapHom F (ρ_ M).hom =
      (diagIso fun x : M.ι × PUnit => F.mapComp (M.X x.1) (𝟙 b.obj)).hom ≫
        mapObj F M ◁ (diagIso fun _ : PUnit => F.mapId b.obj).hom ≫ (ρ_ (mapObj F M)).hom := by
  rw [StringDiagrams.MatBicat.rightUnitor_hom_eq, StringDiagrams.MatBicat.rightUnitor_hom_eq]
  refine (mapHom_permMat F hF _ _).trans ?_
  simp only [diagIso]
  rw [diag_whiskerLeft]
  erw [diagMat_comp_permMat, diagMat_comp_permMat]
  refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
  rw [eqToHom_refl, Category.comp_id]
  exact F.map₂_right_unitor _

/-- **The additive envelope is functorial** for pseudofunctors additive on 2-morphisms. -/
def mapPseudofunctor : Pseudofunctor (MatBicat A) (MatBicat C) where
  obj a := ⟨F.obj a.obj⟩
  map M := mapObj F M
  map₂ φ := mapHom F φ
  map₂_id M := mapHom_id F hF M
  map₂_comp φ ψ := mapHom_comp F hF φ ψ
  mapId a := diagIso fun _ : PUnit => F.mapId a.obj
  mapComp M N := diagIso fun x : M.ι × N.ι => F.mapComp (M.X x.1) (N.X x.2)
  map₂_whisker_left M _ _ η := mapHom_whiskerLeft F hF M η
  map₂_whisker_right η N := mapHom_whiskerRight F hF η N
  map₂_associator M N P := mapHom_associator F hF M N P
  map₂_left_unitor M := mapHom_leftUnitor F hF M
  map₂_right_unitor M := mapHom_rightUnitor F hF M

@[simp] theorem mapPseudofunctor_map (M : a ⟶ b) :
    (mapPseudofunctor F hF).map M = mapObj F M := rfl

@[simp] theorem mapPseudofunctor_map₂ {M N : a ⟶ b} (φ : M ⟶ N) :
    (mapPseudofunctor F hF).map₂ φ = mapHom F φ := rfl

theorem mapPseudofunctor_map₂_add {M N : a ⟶ b} (φ ψ : M ⟶ N) :
    (mapPseudofunctor F hF).map₂ (φ + ψ) =
      (mapPseudofunctor F hF).map₂ φ + (mapPseudofunctor F hF).map₂ ψ := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  exact hF _ _

theorem mapPseudofunctor_map₂_smul {R : Type*} [CommRing R] [∀ a b : A, Linear R (a ⟶ b)]
    [∀ a b : C, Linear R (a ⟶ b)]
    (hF' : ∀ {a b : A} {f g : a ⟶ b} (r : R) (η : f ⟶ g), F.map₂ (r • η) = r • F.map₂ η)
    {M N : a ⟶ b} (r : R) (φ : M ⟶ N) :
    (mapPseudofunctor F hF).map₂ (r • φ) = r • (mapPseudofunctor F hF).map₂ φ := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  exact hF' _ _

end MatBicat

/-! ## The idempotent completion -/

namespace KarBicat

open StringDiagrams.KarBicat StringDiagrams.Karoubi

variable {A : Type u} [Bicategory.{w, v} A] {C : Type u'} [Bicategory.{w', v'} C]
  (F : Pseudofunctor A C) {a b c d : KarBicat A}

/-- The image of a 1-morphism `(f, e)`: `(F f, F e)`. -/
abbrev mapObj (P : a ⟶ b) : (⟨F.obj a.obj⟩ : KarBicat C) ⟶ ⟨F.obj b.obj⟩ :=
  ⟨F.map P.X, F.map₂ P.p, by rw [← F.map₂_comp, P.idem]⟩

/-- The image of a 2-morphism. -/
abbrev mapHom {P Q : a ⟶ b} (η : P ⟶ Q) : mapObj F P ⟶ mapObj F Q :=
  ⟨F.map₂ η.f, by simp only [← F.map₂_comp, η.comm]⟩

theorem mapComp_comm (P : a ⟶ b) (Q : b ⟶ c) :
    (mapObj F (P ≫ Q)).p ≫ (F.mapComp P.X Q.X).hom =
      (F.mapComp P.X Q.X).hom ≫ (mapObj F P ≫ mapObj F Q).p := by
  show F.map₂ (P.p ▷ Q.X ≫ P.X ◁ Q.p) ≫ _ = _ ≫ (F.map₂ P.p ▷ F.map Q.X ≫ F.map P.X ◁ F.map₂ Q.p)
  simp only [F.map₂_comp, F.map₂_whisker_left, F.map₂_whisker_right, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem mkIso_hom' {D : Type*} [Category D] {P Q : Idempotents.Karoubi D} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : (mkIso e h).hom = mkHom e.hom h := rfl

theorem mkIso_inv' {D : Type*} [Category D] {P Q : Idempotents.Karoubi D} (e : P.X ≅ Q.X)
    (h : P.p ≫ e.hom = e.hom ≫ Q.p) : (mkIso e h).inv = mkHom e.inv (comm_inv e h) := rfl

theorem mapHom_mkHom {P Q : a ⟶ b} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) :
    (mapHom F (mkHom c h)).f = F.map₂ c ≫ F.map₂ Q.p := F.map₂_comp _ _

/-- **The idempotent completion is functorial.** -/
def mapPseudofunctor : Pseudofunctor (KarBicat A) (KarBicat C) where
  obj a := ⟨F.obj a.obj⟩
  map P := mapObj F P
  map₂ η := mapHom F η
  map₂_id P := Idempotents.Karoubi.hom_ext _ _ rfl
  map₂_comp η θ := Idempotents.Karoubi.hom_ext _ _ (F.map₂_comp _ _)
  mapId a := mkIso (F.mapId a.obj) (by show F.map₂ (𝟙 _) ≫ _ = _ ≫ 𝟙 _; simp)
  mapComp P Q := mkIso (F.mapComp P.X Q.X) (mapComp_comm F P Q)
  map₂_whisker_left P Q Q' θ := Idempotents.Karoubi.hom_ext _ _ (by
    show F.map₂ (hcomp₂ P.p θ.f) = ((F.mapComp P.X Q.X).hom ≫
      hcomp₂ (F.map₂ P.p) (F.map₂ Q.p)) ≫ hcomp₂ (F.map₂ P.p) (F.map₂ θ.f) ≫
        (F.mapComp P.X Q'.X).inv ≫ F.map₂ (hcomp₂ P.p Q'.p)
    have e1 : hcomp₂ P.p θ.f = hcomp₂ P.p θ.f ≫ hcomp₂ P.p Q'.p := by
      rw [← hcomp₂_comp, P.idem, Idempotents.Karoubi.comp_p]
    have e3 : hcomp₂ (F.map₂ P.p) (F.map₂ Q.p) ≫ hcomp₂ (F.map₂ P.p) (F.map₂ θ.f) =
        hcomp₂ (F.map₂ P.p) (F.map₂ θ.f) := by
      rw [← hcomp₂_comp, ← F.map₂_comp, ← F.map₂_comp, P.idem, Idempotents.Karoubi.p_comp]
    rw [Category.assoc, ← Category.assoc (hcomp₂ (F.map₂ P.p) (F.map₂ Q.p)), e3, e1,
      F.map₂_comp]
    simp only [hcomp₂, F.map₂_comp, F.map₂_whisker_left, F.map₂_whisker_right, Category.assoc,
      Iso.inv_hom_id_assoc])
  map₂_whisker_right {_ _ _ P P'} η Q := Idempotents.Karoubi.hom_ext _ _ (by
    show F.map₂ (hcomp₂ η.f Q.p) = ((F.mapComp P.X Q.X).hom ≫
      hcomp₂ (F.map₂ P.p) (F.map₂ Q.p)) ≫ hcomp₂ (F.map₂ η.f) (F.map₂ Q.p) ≫
        (F.mapComp P'.X Q.X).inv ≫ F.map₂ (hcomp₂ P'.p Q.p)
    have e1 : hcomp₂ η.f Q.p = hcomp₂ η.f Q.p ≫ hcomp₂ P'.p Q.p := by
      rw [← hcomp₂_comp, Q.idem, Idempotents.Karoubi.comp_p]
    have e3 : hcomp₂ (F.map₂ P.p) (F.map₂ Q.p) ≫ hcomp₂ (F.map₂ η.f) (F.map₂ Q.p) =
        hcomp₂ (F.map₂ η.f) (F.map₂ Q.p) := by
      rw [← hcomp₂_comp, ← F.map₂_comp, ← F.map₂_comp, Q.idem, Idempotents.Karoubi.p_comp]
    rw [Category.assoc, ← Category.assoc (hcomp₂ (F.map₂ P.p) (F.map₂ Q.p)), e3, e1,
      F.map₂_comp]
    simp only [hcomp₂, F.map₂_comp, F.map₂_whisker_left, F.map₂_whisker_right, Category.assoc,
      Iso.inv_hom_id_assoc])
  map₂_associator P Q S := by
    rw [mkIso_hom', mkIso_hom', mkIso_inv', mkIso_inv', StringDiagrams.KarBicat.associator_hom_eq]
    erw [StringDiagrams.KarBicat.mkHom_whiskerRight, StringDiagrams.KarBicat.whiskerLeft_mkHom, StringDiagrams.Karoubi.mkHom_comp_mkHom,
      StringDiagrams.Karoubi.mkHom_comp_mkHom, StringDiagrams.Karoubi.mkHom_comp_mkHom, StringDiagrams.Karoubi.mkHom_comp_mkHom]
    refine Idempotents.Karoubi.hom_ext _ _ ?_
    erw [mapHom_mkHom, StringDiagrams.Karoubi.mkHom_f, F.map₂_associator]
    simp only [Category.assoc]
    rfl
    all_goals exact StringDiagrams.KarBicat.assoc_comm _ _ _
  map₂_left_unitor P := by
    rw [mkIso_hom', mkIso_hom', StringDiagrams.KarBicat.leftUnitor_hom_eq]
    erw [StringDiagrams.KarBicat.mkHom_whiskerRight, StringDiagrams.Karoubi.mkHom_comp_mkHom, StringDiagrams.Karoubi.mkHom_comp_mkHom]
    refine Idempotents.Karoubi.hom_ext _ _ ?_
    erw [mapHom_mkHom, StringDiagrams.Karoubi.mkHom_f, F.map₂_left_unitor]
    simp only [Category.assoc]
    rfl
    all_goals exact StringDiagrams.KarBicat.leftUnitor_comm _
  map₂_right_unitor P := by
    rw [mkIso_hom', mkIso_hom', StringDiagrams.KarBicat.rightUnitor_hom_eq]
    erw [StringDiagrams.KarBicat.whiskerLeft_mkHom, StringDiagrams.Karoubi.mkHom_comp_mkHom, StringDiagrams.Karoubi.mkHom_comp_mkHom]
    refine Idempotents.Karoubi.hom_ext _ _ ?_
    erw [mapHom_mkHom, StringDiagrams.Karoubi.mkHom_f, F.map₂_right_unitor]
    simp only [Category.assoc]
    rfl
    all_goals exact StringDiagrams.KarBicat.rightUnitor_comm _

theorem mapPseudofunctor_map₂_add [∀ a b : A, Preadditive (a ⟶ b)]
    [∀ a b : C, Preadditive (a ⟶ b)]
    (hF : ∀ {a b : A} {f g : a ⟶ b} (η θ : f ⟶ g), F.map₂ (η + θ) = F.map₂ η + F.map₂ θ)
    {P Q : a ⟶ b} (η θ : P ⟶ Q) :
    (mapPseudofunctor F).map₂ (η + θ) = (mapPseudofunctor F).map₂ η + (mapPseudofunctor F).map₂ θ :=
  Idempotents.Karoubi.hom_ext _ _ (hF η.f θ.f)

theorem mapPseudofunctor_map₂_smul {R : Type*} [CommRing R] [∀ a b : A, Preadditive (a ⟶ b)]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
    [∀ a b : C, Linear R (a ⟶ b)]
    (hF : ∀ {a b : A} {f g : a ⟶ b} (r : R) (η : f ⟶ g), F.map₂ (r • η) = r • F.map₂ η)
    {P Q : a ⟶ b} (r : R) (η : P ⟶ Q) :
    (mapPseudofunctor F).map₂ (r • η) = r • (mapPseudofunctor F).map₂ η :=
  Idempotents.Karoubi.hom_ext _ _ (hF r η.f)

end KarBicat

end Categorification
