/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ShiftCoherence
import Categorification.TwoRep.GradedHom

/-!
# The finite-sum graded-Hom bicategory

Construct the bicategory with the objects and 1-morphisms of `B` and finite sums of shifted
2-morphisms. Whiskering acts componentwise. All bicategory axioms, including interchange,
pentagon and triangle, follow from the existing shifted-whiskering coherence and the ordinary
bicategory axioms; none is introduced as a new assumption.

The hypotheses are exactly a preadditive graded bicategory and its explicit `ShiftCoherence`.
There is no boundedness or automatic-biadjointness claim. `GradedHomAdjunction` uses this actual
bicategory to construct a degree-preserving adjunction bijection. Only the construction kernel
and degree-zero/homogeneous API of the ungated `cl-sc` lead are selected here, not its
low-weight results, homogeneous-inverse calculus, or extra linearity API.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-- **The graded-Hom bicategory `K^•`** of a graded bicategory (type synonym for the objects):
the same objects and 1-morphisms, and 2-morphisms the finite sums of homogeneous 2-morphisms of
all degrees. -/
def GradedHomBicat (B : Type u) : Type u := B

namespace GradedHomBicat

open GradedHomCat

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- An object of `B` as an object of the graded-Hom bicategory. -/
abbrev of (a : B) : GradedHomBicat B := a

/-- An object of the graded-Hom bicategory as an object of `B`. -/
abbrev as (a : GradedHomBicat B) : B := a

/-! ### Whiskering of graded 2-morphisms -/

section Whisker

variable {a b c d : B}

/-- Left whiskering of graded 2-morphisms: `shWhiskerLeft` on each homogeneous component. -/
def whiskerLeftHom (f : a ⟶ b) (g h : b ⟶ c) :
    ((mk g : GradedHomCat (b ⟶ c)) ⟶ mk h) →+
      ((mk (f ≫ g) : GradedHomCat (a ⟶ c)) ⟶ mk (f ≫ h)) :=
  DirectSum.map (α := fun d : ℤ => ShiftedHom g h d)
    (β := fun d : ℤ => ShiftedHom (f ≫ g) (f ≫ h) d) fun d : ℤ =>
      AddMonoidHom.mk' (fun η : ShiftedHom g h d => shWhiskerLeft f η)
        (fun η θ => ShiftedHom.map_add η θ (precomp c f))

/-- Right whiskering of graded 2-morphisms: `shWhiskerRight` on each homogeneous component. -/
def whiskerRightHom (f g : a ⟶ b) (h : b ⟶ c) :
    ((mk f : GradedHomCat (a ⟶ b)) ⟶ mk g) →+
      ((mk (f ≫ h) : GradedHomCat (a ⟶ c)) ⟶ mk (g ≫ h)) :=
  DirectSum.map (α := fun d : ℤ => ShiftedHom f g d)
    (β := fun d : ℤ => ShiftedHom (f ≫ h) (g ≫ h) d) fun d : ℤ =>
      AddMonoidHom.mk' (fun η : ShiftedHom f g d => shWhiskerRight η h)
        (fun η θ => ShiftedHom.map_add η θ (postcomp a h))

theorem whiskerLeftHom_homOf (f : a ⟶ b) {g h : b ⟶ c} (n : ℤ) (η : ShiftedHom g h n) :
    whiskerLeftHom f g h (homOf n η) = homOf n (shWhiskerLeft f η) :=
  DirectSum.map_of _ n η

theorem whiskerRightHom_homOf {f g : a ⟶ b} (n : ℤ) (η : ShiftedHom f g n) (h : b ⟶ c) :
    whiskerRightHom f g h (homOf n η) = homOf n (shWhiskerRight η h) :=
  DirectSum.map_of _ n η

theorem whiskerLeftHom_incl (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    whiskerLeftHom f g h ((incl (b ⟶ c)).map η) = (incl (a ⟶ c)).map (f ◁ η) := by
  rw [incl_map, whiskerLeftHom_homOf, shWhiskerLeft_mk₀, incl_map]

theorem whiskerRightHom_incl {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    whiskerRightHom f g h ((incl (a ⟶ b)).map η) = (incl (a ⟶ c)).map (η ▷ h) := by
  rw [incl_map, whiskerRightHom_homOf, shWhiskerRight_mk₀, incl_map]

theorem whiskerLeftHom_id (f : a ⟶ b) (g : b ⟶ c) :
    whiskerLeftHom f g g (𝟙 (mk g)) = 𝟙 (mk (f ≫ g)) := by
  rw [GradedHomCat.id_eq, whiskerLeftHom_homOf, shWhiskerLeft_mk₀, Bicategory.whiskerLeft_id, GradedHomCat.id_eq]

theorem id_whiskerRightHom (f : a ⟶ b) (g : b ⟶ c) :
    whiskerRightHom f f g (𝟙 (mk f)) = 𝟙 (mk (f ≫ g)) := by
  rw [GradedHomCat.id_eq, whiskerRightHom_homOf, shWhiskerRight_mk₀, Bicategory.id_whiskerRight, GradedHomCat.id_eq]

theorem whiskerLeftHom_comp (f : a ⟶ b) {g h i : b ⟶ c}
    (η : (mk g : GradedHomCat (b ⟶ c)) ⟶ mk h) (θ : (mk h : GradedHomCat (b ⟶ c)) ⟶ mk i) :
    whiskerLeftHom f g i (η ≫ θ) = whiskerLeftHom f g h η ≫ whiskerLeftHom f h i θ := by
  induction η using hom_induction with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add φ ψ hφ hψ => simp only [Preadditive.add_comp, map_add, hφ, hψ]
  | homOf m η =>
    induction θ using hom_induction with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add φ ψ hφ hψ => simp only [Preadditive.comp_add, map_add, hφ, hψ]
    | homOf n θ =>
      rw [homOf_comp_homOf η θ rfl, whiskerLeftHom_homOf, whiskerLeftHom_homOf,
        whiskerLeftHom_homOf, homOf_comp_homOf _ _ rfl, shWhiskerLeft_comp]

theorem comp_whiskerRightHom {f g h : a ⟶ b} (η : (mk f : GradedHomCat (a ⟶ b)) ⟶ mk g)
    (θ : (mk g : GradedHomCat (a ⟶ b)) ⟶ mk h) (i : b ⟶ c) :
    whiskerRightHom f h i (η ≫ θ) = whiskerRightHom f g i η ≫ whiskerRightHom g h i θ := by
  induction η using hom_induction with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add φ ψ hφ hψ => simp only [Preadditive.add_comp, map_add, hφ, hψ]
  | homOf m η =>
    induction θ using hom_induction with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add φ ψ hφ hψ => simp only [Preadditive.comp_add, map_add, hφ, hψ]
    | homOf n θ =>
      rw [homOf_comp_homOf η θ rfl, whiskerRightHom_homOf, whiskerRightHom_homOf,
        whiskerRightHom_homOf, homOf_comp_homOf _ _ rfl, shWhiskerRight_comp]

theorem id_whiskerLeftHom [GradedBicategory.ShiftUnitor B] {f g : a ⟶ b}
    (η : (mk f : GradedHomCat (a ⟶ b)) ⟶ mk g) :
    whiskerLeftHom (𝟙 a) f g η =
      (incl (a ⟶ b)).map (λ_ f).hom ≫ η ≫ (incl (a ⟶ b)).map (λ_ g).inv := by
  induction η using hom_induction with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
  | homOf n η =>
    rw [whiskerLeftHom_homOf, incl_map, incl_map, homOf_comp_homOf _ _ (zero_add n),
      homOf_comp_homOf _ _ (add_zero n), shWhiskerLeft_of_id]

theorem whiskerRightHom_id [GradedBicategory.ShiftUnitor B] {f g : a ⟶ b}
    (η : (mk f : GradedHomCat (a ⟶ b)) ⟶ mk g) :
    whiskerRightHom f g (𝟙 b) η =
      (incl (a ⟶ b)).map (ρ_ f).hom ≫ η ≫ (incl (a ⟶ b)).map (ρ_ g).inv := by
  induction η using hom_induction with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
  | homOf n η =>
    rw [whiskerRightHom_homOf, incl_map, incl_map, homOf_comp_homOf _ _ (zero_add n),
      homOf_comp_homOf _ _ (add_zero n), shWhiskerRight_of_id]

theorem comp_whiskerLeftHom [GradedBicategory.ShiftAssoc B] (f : a ⟶ b) (g : b ⟶ c)
    {h h' : c ⟶ d} (η : (mk h : GradedHomCat (c ⟶ d)) ⟶ mk h') :
    whiskerLeftHom (f ≫ g) h h' η =
      (incl (a ⟶ d)).map (α_ f g h).hom ≫
        whiskerLeftHom f (g ≫ h) (g ≫ h') (whiskerLeftHom g h h' η) ≫
          (incl (a ⟶ d)).map (α_ f g h').inv := by
  induction η using hom_induction with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
  | homOf n η =>
    rw [whiskerLeftHom_homOf, whiskerLeftHom_homOf, whiskerLeftHom_homOf, incl_map, incl_map,
      homOf_comp_homOf _ _ (zero_add n), homOf_comp_homOf _ _ (add_zero n),
      shWhiskerLeft_of_comp]

theorem whiskerRightHom_comp [GradedBicategory.ShiftAssocRight B] {f f' : a ⟶ b}
    (η : (mk f : GradedHomCat (a ⟶ b)) ⟶ mk f') (g : b ⟶ c) (h : c ⟶ d) :
    whiskerRightHom f f' (g ≫ h) η =
      (incl (a ⟶ d)).map (α_ f g h).inv ≫
        whiskerRightHom (f ≫ g) (f' ≫ g) h (whiskerRightHom f f' g η) ≫
          (incl (a ⟶ d)).map (α_ f' g h).hom := by
  induction η using hom_induction with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
  | homOf n η =>
    rw [whiskerRightHom_homOf, whiskerRightHom_homOf, whiskerRightHom_homOf, incl_map, incl_map,
      homOf_comp_homOf _ _ (zero_add n), homOf_comp_homOf _ _ (add_zero n),
      shWhiskerRight_of_comp]

theorem whiskerHom_assoc [GradedBicategory.ShiftAssocMid B] (f : a ⟶ b) {g g' : b ⟶ c}
    (η : (mk g : GradedHomCat (b ⟶ c)) ⟶ mk g') (h : c ⟶ d) :
    whiskerRightHom (f ≫ g) (f ≫ g') h (whiskerLeftHom f g g' η) =
      (incl (a ⟶ d)).map (α_ f g h).hom ≫
        whiskerLeftHom f (g ≫ h) (g' ≫ h) (whiskerRightHom g g' h η) ≫
          (incl (a ⟶ d)).map (α_ f g' h).inv := by
  induction η using hom_induction with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
  | homOf n η =>
    rw [whiskerLeftHom_homOf, whiskerRightHom_homOf, whiskerRightHom_homOf,
      whiskerLeftHom_homOf, incl_map, incl_map, homOf_comp_homOf _ _ (zero_add n),
      homOf_comp_homOf _ _ (add_zero n), shWhisker_assoc]

theorem whiskerHom_exchange [GradedBicategory.ShiftInterchange B] {f g : a ⟶ b} {h i : b ⟶ c}
    (η : (mk f : GradedHomCat (a ⟶ b)) ⟶ mk g) (θ : (mk h : GradedHomCat (b ⟶ c)) ⟶ mk i) :
    whiskerLeftHom f h i θ ≫ whiskerRightHom f g i η =
      whiskerRightHom f g h η ≫ whiskerLeftHom g h i θ := by
  induction η using hom_induction with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
  | homOf m η =>
    induction θ using hom_induction with
    | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
    | add φ ψ hφ hψ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hφ, hψ]
    | homOf n θ =>
      rw [whiskerLeftHom_homOf, whiskerRightHom_homOf, whiskerRightHom_homOf,
        whiskerLeftHom_homOf, homOf_comp_homOf _ _ (add_comm m n), homOf_comp_homOf _ _ rfl,
        shWhisker_exchange η θ rfl (add_comm m n)]

theorem pentagon_aux {e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    whiskerRightHom ((f ≫ g) ≫ h) (f ≫ g ≫ h) i ((incl (a ⟶ d)).map (α_ f g h).hom) ≫
        (incl (a ⟶ e)).map (α_ f (g ≫ h) i).hom ≫
          whiskerLeftHom f ((g ≫ h) ≫ i) (g ≫ h ≫ i) ((incl (b ⟶ e)).map (α_ g h i).hom) =
      (incl (a ⟶ e)).map (α_ (f ≫ g) h i).hom ≫ (incl (a ⟶ e)).map (α_ f g (h ≫ i)).hom := by
  rw [whiskerRightHom_incl, whiskerLeftHom_incl, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, Bicategory.pentagon]

theorem triangle_aux (f : a ⟶ b) (g : b ⟶ c) :
    (incl (a ⟶ c)).map (α_ f (𝟙 b) g).hom ≫
        whiskerLeftHom f (𝟙 b ≫ g) g ((incl (b ⟶ c)).map (λ_ g).hom) =
      whiskerRightHom (f ≫ 𝟙 b) f g ((incl (a ⟶ b)).map (ρ_ f).hom) := by
  rw [whiskerLeftHom_incl, whiskerRightHom_incl, ← Functor.map_comp, Bicategory.triangle]

end Whisker

/-! ### The bicategory structure -/

variable [GradedBicategory.ShiftCoherence B]

/-- **The graded-Hom bicategory.** 1-morphisms `a ⟶ b` are the 1-morphisms of `B` (wrapped in
`GradedHomCat`), 2-morphisms are the graded 2-morphisms; whiskering is whiskering of shifted
2-morphisms and the associators and unitors are those of `B`, in degree `0`. -/
instance bicategory : Bicategory.{w, v} (GradedHomBicat B) where
  Hom a b := GradedHomCat (a.as ⟶ b.as)
  id a := GradedHomCat.mk (𝟙 a.as)
  comp f g := GradedHomCat.mk (f.as ≫ g.as)
  homCategory a b := inferInstanceAs (Category (GradedHomCat (a.as ⟶ b.as)))
  whiskerLeft f g h η := whiskerLeftHom f.as g.as h.as η
  whiskerRight {_ _ _ f g} η h := whiskerRightHom f.as g.as h.as η
  associator f g h := (incl _).mapIso (α_ f.as g.as h.as)
  leftUnitor f := (incl _).mapIso (λ_ f.as)
  rightUnitor f := (incl _).mapIso (ρ_ f.as)
  whiskerLeft_id f g := whiskerLeftHom_id f.as g.as
  whiskerLeft_comp f _ _ _ η θ := whiskerLeftHom_comp f.as η θ
  id_whiskerLeft η := id_whiskerLeftHom η
  comp_whiskerLeft f g _ _ η := comp_whiskerLeftHom f.as g.as η
  id_whiskerRight f g := id_whiskerRightHom f.as g.as
  comp_whiskerRight η θ i := comp_whiskerRightHom η θ i.as
  whiskerRight_id η := whiskerRightHom_id η
  whiskerRight_comp η g h := whiskerRightHom_comp η g.as h.as
  whisker_assoc f _ _ η h := whiskerHom_assoc f.as η h.as
  whisker_exchange η θ := whiskerHom_exchange η θ
  pentagon f g h i := pentagon_aux f.as g.as h.as i.as
  triangle f g := triangle_aux f.as g.as

instance homPreadditive (a b : GradedHomBicat B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (GradedHomCat (a.as ⟶ b.as)))

/-! ### 1-morphisms and homogeneous 2-morphisms of `B` in the graded-Hom bicategory -/

section API

variable {a b c d : B}

/-- A 1-morphism of `B` as a 1-morphism of the graded-Hom bicategory. -/
abbrev of₁ (f : a ⟶ b) : of a ⟶ of b := GradedHomCat.mk f

/-- A shifted 2-morphism `η : f ⟶ g⟦n⟧` of `B` as a (homogeneous, degree `n`) 2-morphism
`f ⟶ g` of the graded-Hom bicategory. -/
def of₂ {f g : a ⟶ b} (n : ℤ) (η : ShiftedHom f g n) : of₁ f ⟶ of₁ g := homOf n η

/-- A 2-morphism of `B` as a 2-morphism (of degree `0`) of the graded-Hom bicategory. -/
def incl₂ {f g : a ⟶ b} (η : f ⟶ g) : of₁ f ⟶ of₁ g := (incl (a ⟶ b)).map η

theorem of₁_comp (f : a ⟶ b) (g : b ⟶ c) : of₁ f ≫ of₁ g = of₁ (f ≫ g) := rfl

theorem of₁_id (a : B) : 𝟙 (of a) = of₁ (𝟙 a) := rfl

theorem incl₂_eq_of₂ {f g : a ⟶ b} (η : f ⟶ g) :
    incl₂ η = of₂ 0 (ShiftedHom.mk₀ (0 : ℤ) rfl η) := rfl

theorem of₂_comp_of₂ {f g h : a ⟶ b} {m n s : ℤ} (η : ShiftedHom f g m) (θ : ShiftedHom g h n)
    (hs : n + m = s) : of₂ m η ≫ of₂ n θ = of₂ s (η.comp θ hs) :=
  homOf_comp_homOf η θ hs

theorem whiskerLeft_of₂ (f : a ⟶ b) {g h : b ⟶ c} (n : ℤ) (η : ShiftedHom g h n) :
    of₁ f ◁ of₂ n η = of₂ n (shWhiskerLeft f η) :=
  whiskerLeftHom_homOf f n η

theorem of₂_whiskerRight {f g : a ⟶ b} (n : ℤ) (η : ShiftedHom f g n) (h : b ⟶ c) :
    of₂ n η ▷ of₁ h = of₂ n (shWhiskerRight η h) :=
  whiskerRightHom_homOf n η h

theorem whiskerLeft_incl₂ (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    of₁ f ◁ incl₂ η = incl₂ (f ◁ η) :=
  whiskerLeftHom_incl f η

theorem incl₂_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    incl₂ η ▷ of₁ h = incl₂ (η ▷ h) :=
  whiskerRightHom_incl η h

theorem incl₂_comp {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    incl₂ (η ≫ θ) = incl₂ η ≫ incl₂ θ :=
  (incl (a ⟶ b)).map_comp η θ

theorem incl₂_id (f : a ⟶ b) : incl₂ (𝟙 f) = 𝟙 (of₁ f) :=
  (incl (a ⟶ b)).map_id f

theorem incl₂_injective {f g : a ⟶ b} :
    Function.Injective (incl₂ : (f ⟶ g) → (of₁ f ⟶ of₁ g)) :=
  (incl (a ⟶ b)).map_injective

theorem of₂_injective {f g : a ⟶ b} (n : ℤ) :
    Function.Injective (of₂ n : ShiftedHom f g n → (of₁ f ⟶ of₁ g)) :=
  homOf_injective n

@[simp] theorem of₂_zero {f g : a ⟶ b} (n : ℤ) : of₂ n (0 : ShiftedHom f g n) = 0 :=
  homOf_zero n

theorem of₂_add {f g : a ⟶ b} (n : ℤ) (η θ : ShiftedHom f g n) :
    of₂ n (η + θ) = of₂ n η + of₂ n θ :=
  homOf_add n η θ

theorem of₂_sub {f g : a ⟶ b} (n : ℤ) (η θ : ShiftedHom f g n) :
    of₂ n (η - θ) = of₂ n η - of₂ n θ :=
  homOf_sub n η θ

theorem of₂_neg {f g : a ⟶ b} (n : ℤ) (η : ShiftedHom f g n) : of₂ n (-η) = -of₂ n η :=
  homOf_neg n η

theorem associator_hom_eq (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ (of₁ f) (of₁ g) (of₁ h)).hom = incl₂ (α_ f g h).hom := rfl

theorem associator_inv_eq (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ (of₁ f) (of₁ g) (of₁ h)).inv = incl₂ (α_ f g h).inv := rfl

theorem leftUnitor_hom_eq (f : a ⟶ b) : (λ_ (of₁ f)).hom = incl₂ (λ_ f).hom := rfl

theorem leftUnitor_inv_eq (f : a ⟶ b) : (λ_ (of₁ f)).inv = incl₂ (λ_ f).inv := rfl

theorem rightUnitor_hom_eq (f : a ⟶ b) : (ρ_ (of₁ f)).hom = incl₂ (ρ_ f).hom := rfl

theorem rightUnitor_inv_eq (f : a ⟶ b) : (ρ_ (of₁ f)).inv = incl₂ (ρ_ f).inv := rfl

end API

end GradedHomBicat

end Categorification.TwoRep
