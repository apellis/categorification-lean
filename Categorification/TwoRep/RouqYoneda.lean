/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.MateNat
import Categorification.TwoRep.RouqFullCL
import Categorification.KLR.Symmetries

/-!
# Rouquier's data under postcomposition

Let `B` be a bicategory whose Hom categories are `k`-linear, with additive and `k`-linear
whiskering, and fix an object `y`. Postcomposition sends an object `a` to the `k`-linear
category `y ⟶ a`, a 1-morphism `f : a ⟶ b` to the functor `- ≫ f`, and a 2-morphism `η` to
the natural transformation `- ◁ η`. This is the representable 2-functor `Hom(y, -)` into
`LinearCat k`. It is a pseudofunctor: the comparison `(- ≫ f) ≫ g ≅ - ≫ (f ≫ g)` is the
associator (`yComp`).

This file transports Rouquier's local data (`RouqLoc`; J. Brundan, *On the definition of
Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1) along it. Images of adjunctions are
adjunctions (`yAdj`). Images of mates are, componentwise, whiskered mates conjugated by
associators (`yAdj_mate_app`). So Rouquier's rightward crossing, and the dotted caps and cups,
map to their images and the explicit inverses (1.8), (1.9) map to explicit inverses
(`RouqLoc.yoneda`).

Applied in the horizontal opposite bicategory, the same construction gives precomposition
`Hom(-, w)`. These are the two factors of the external product of a lowest-weight and a
highest-weight categorification used for Webster's test representations
(B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, Lemma
`lem:g-action`).

## Main definitions

* `yObj`, `yMap`, `yMap₂`: the representable 2-functor on objects, 1-morphisms and 2-morphisms;
* `yComp`, `yConj`: the comparison isomorphism and the image of a 2-morphism between
  composites;
* `yAdj`: the image of an adjunction;
* `RouqLoc.yoneda`: the image of Rouquier's data at one weight.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u u₁

namespace Yoneda

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

instance postcomp_additive (a : B) {b c : B} (f : b ⟶ c) : (postcomp a f).Additive where
  map_add := AdditiveWhiskering.add_whiskerRight _ _ _

instance precomp_additive {a b : B} (c : B) (f : a ⟶ b) : (precomp c f).Additive where
  map_add := AdditiveWhiskering.whiskerLeft_add _ _ _

omit [∀ a b : B, Linear k (a ⟶ b)] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem whiskerLeft_sub {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η - θ) = f ◁ η - f ◁ θ :=
  map_sub (AdditiveWhiskering.whiskerLeftAddHom f g h) η θ

variable (k) (y : B)

/-- The `k`-linear category `y ⟶ a`. -/
abbrev yObj (a : B) : LinearCat.{w', w, v} k := LinearCat.of k (y ⟶ a)

/-- Postcomposition with 1-morphisms `a ⟶ b`, as a functor into the hom category of
`LinearCat k`. -/
def yFun (a b : B) : (a ⟶ b) ⥤ (yObj k y a ⟶ yObj k y b) :=
  ObjectProperty.lift _ (postcomposing y a b) fun f =>
    ⟨inferInstanceAs (postcomp y f).Additive, inferInstanceAs ((postcomp y f).Linear k)⟩

/-- Postcomposition with a 1-morphism. -/
abbrev yMap {a b : B} (f : a ⟶ b) : yObj k y a ⟶ yObj k y b := (yFun k y a b).obj f

/-- Postcomposition with a 2-morphism. -/
abbrev yMap₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : yMap k y f ⟶ yMap k y g :=
  (yFun k y a b).map η

variable {k y}

@[simp] theorem yMap_obj_obj {a b : B} (f : a ⟶ b) (X : y ⟶ a) :
    (yMap k y f).obj.obj X = X ≫ f := rfl

@[simp] theorem yMap_obj_map {a b : B} (f : a ⟶ b) {X X' : y ⟶ a} (φ : X ⟶ X') :
    (yMap k y f).obj.map φ = φ ▷ f := rfl

@[simp] theorem yMap₂_app {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (X : y ⟶ a) :
    (yMap₂ k y η).hom.app X = X ◁ η := rfl

theorem yMap₂_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    yMap₂ k y (η ≫ θ) = yMap₂ k y η ≫ yMap₂ k y θ :=
  (yFun k y a b).map_comp η θ

theorem yMap₂_id {a b : B} (f : a ⟶ b) : yMap₂ k y (𝟙 f) = 𝟙 _ :=
  (yFun k y a b).map_id f

instance homForget_additive (a b : B) :
    (LinearCat.homForget (yObj k y a) (yObj k y b)).Additive where
  map_add := rfl

instance (a b : B) : (yFun k y a b).Additive where
  map_add {_ _ η θ} := by
    apply ObjectProperty.hom_ext
    ext X
    exact AdditiveWhiskering.whiskerLeft_add X η θ

theorem yMap₂_powComp {a b : B} {f : a ⟶ b} (x : f ⟶ f) (n : ℕ) :
    yMap₂ k y (powComp x n) = powComp (yMap₂ k y x) n :=
  map_powComp (yFun k y a b) x n

variable (k y)

/-- The comparison `(- ≫ f) ≫ g ≅ - ≫ (f ≫ g)`: the associator. -/
def yComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : yMap k y f ≫ yMap k y g ≅ yMap k y (f ≫ g) :=
  ObjectProperty.isoMk _ (associatorNatIsoLeft y f g)

/-- The comparison `- ≫ 𝟙 a ≅ -`: the right unitor. -/
def yId (a : B) : yMap k y (𝟙 a) ≅ 𝟙 (yObj k y a) :=
  ObjectProperty.isoMk _ (rightUnitorNatIso y a)

variable {k y}

@[simp] theorem yComp_hom_app {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (X : y ⟶ a) :
    (yComp k y f g).hom.hom.app X = (α_ X f g).hom := rfl

@[simp] theorem yComp_inv_app {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (X : y ⟶ a) :
    (yComp k y f g).inv.hom.app X = (α_ X f g).inv := rfl

@[simp] theorem yId_hom_app (a : B) (X : y ⟶ a) : (yId k y a).hom.hom.app X = (ρ_ X).hom := rfl

@[simp] theorem yId_inv_app (a : B) (X : y ⟶ a) : (yId k y a).inv.hom.app X = (ρ_ X).inv := rfl

variable (k y)

/-- The image of a 2-morphism between composites of two 1-morphisms. -/
def yConj {a b b' c : B} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ b'} {g' : b' ⟶ c}
    (φ : f ≫ g ⟶ f' ≫ g') : yMap k y f ≫ yMap k y g ⟶ yMap k y f' ≫ yMap k y g' :=
  (yComp k y f g).hom ≫ yMap₂ k y φ ≫ (yComp k y f' g').inv

variable {k y}

@[simp] theorem yConj_app {a b b' c : B} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ b'} {g' : b' ⟶ c}
    (φ : f ≫ g ⟶ f' ≫ g') (X : y ⟶ a) :
    (yConj k y φ).hom.app X = (α_ X f g).hom ≫ X ◁ φ ≫ (α_ X f' g').inv := rfl

/-- **The image of an adjunction** under postcomposition. -/
def yAdj {a b : B} {f : a ⟶ b} {g : b ⟶ a} (A : f ⊣ g) : yMap k y f ⊣ yMap k y g :=
  LinearCat.ofAdjunction (k := k) (Adjunction.mkOfUnitCounit (F := (yMap k y f).obj)
    (G := (yMap k y g).obj)
    { unit :=
        { app X := (ρ_ X).inv ≫ X ◁ A.unit ≫ (α_ X f g).inv
          naturality X X' φ := by
            change φ ≫ (ρ_ X').inv ≫ X' ◁ A.unit ≫ (α_ X' f g).inv =
              ((ρ_ X).inv ≫ X ◁ A.unit ≫ (α_ X f g).inv) ≫ (φ ▷ f) ▷ g
            rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
              associator_inv_naturality_left, Category.assoc, Category.assoc] }
      counit :=
        { app X := (α_ X g f).hom ≫ X ◁ A.counit ≫ (ρ_ X).hom
          naturality X X' φ := by
            change (φ ▷ g) ▷ f ≫ (α_ X' g f).hom ≫ X' ◁ A.counit ≫ (ρ_ X').hom =
              ((α_ X g f).hom ≫ X ◁ A.counit ≫ (ρ_ X).hom) ≫ φ
            rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
              rightUnitor_naturality, Category.assoc, Category.assoc] }
      left_triangle := by
        ext X
        change ((ρ_ X).inv ≫ X ◁ A.unit ≫ (α_ X f g).inv) ▷ f ≫ 𝟙 _ ≫
          ((α_ (X ≫ f) g f).hom ≫ (X ≫ f) ◁ A.counit ≫ (ρ_ (X ≫ f)).hom) = 𝟙 (X ≫ f)
        calc _ = 𝟙 _ ⊗≫ X ◁ leftZigzag A.unit A.counit ⊗≫ 𝟙 _ := by
              rw [leftZigzag]; bicategory
          _ = 𝟙 (X ≫ f) := by rw [A.left_triangle]; bicategory
      right_triangle := by
        ext X
        change ((ρ_ (X ≫ g)).inv ≫ (X ≫ g) ◁ A.unit ≫ (α_ (X ≫ g) f g).inv) ≫ 𝟙 _ ≫
          ((α_ X g f).hom ≫ X ◁ A.counit ≫ (ρ_ X).hom) ▷ g = 𝟙 (X ≫ g)
        calc _ = 𝟙 _ ⊗≫ X ◁ rightZigzag A.unit A.counit ⊗≫ 𝟙 _ := by
              rw [rightZigzag]; bicategory
          _ = 𝟙 (X ≫ g) := by rw [A.right_triangle]; bicategory })

@[simp] theorem yAdj_unit_app {a b : B} {f : a ⟶ b} {g : b ⟶ a} (A : f ⊣ g) (X : y ⟶ a) :
    (yAdj (k := k) A).unit.hom.app X = (ρ_ X).inv ≫ X ◁ A.unit ≫ (α_ X f g).inv := rfl

@[simp] theorem yAdj_counit_app {a b : B} {f : a ⟶ b} {g : b ⟶ a} (A : f ⊣ g) (X : y ⟶ b) :
    (yAdj (k := k) A).counit.hom.app X = (α_ X g f).hom ≫ X ◁ A.counit ≫ (ρ_ X).hom := rfl

/-- **Mates under postcomposition**: the mate of the image of a square is, componentwise, the
whiskered mate conjugated by associators. -/
theorem yAdj_mate_app {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    {g : a ⟶ c} {h : b ⟶ d} (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (τ : g ≫ l₂ ⟶ l₁ ≫ h)
    (X : y ⟶ b) :
    (mateEquiv (yAdj (k := k) A₁) (yAdj (k := k) A₂) (g := yMap k y g) (h := yMap k y h)
      (yConj k y τ)).hom.app X =
      (α_ X r₁ g).hom ≫ X ◁ mateEquiv A₁ A₂ τ ≫ (α_ X h r₂).inv := by
  rw [LinearCat.mate_hom]
  change ((ρ_ ((X ≫ r₁) ≫ g)).inv ≫ ((X ≫ r₁) ≫ g) ◁ A₂.unit ≫
      (α_ ((X ≫ r₁) ≫ g) l₂ r₂).inv) ≫
    ((α_ (X ≫ r₁) g l₂).hom ≫ (X ≫ r₁) ◁ τ ≫ (α_ (X ≫ r₁) l₁ h).inv) ▷ r₂ ≫
    (((α_ X r₁ l₁).hom ≫ X ◁ A₁.counit ≫ (ρ_ X).hom) ▷ h) ▷ r₂ = _
  rw [mateEquiv_apply']
  bicategory

section Composites

theorem yMap₂_zero {a b : B} {f g : a ⟶ b} : yMap₂ k y (0 : f ⟶ g) = 0 :=
  (yFun k y a b).map_zero f g

theorem yMap₂_add {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) :
    yMap₂ k y (η + θ) = yMap₂ k y η + yMap₂ k y θ :=
  (yFun k y a b).map_add

theorem yMap₂_sub {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) :
    yMap₂ k y (η - θ) = yMap₂ k y η - yMap₂ k y θ :=
  (yFun k y a b).map_sub

variable (k y)

/-- The comparison `- ≫ f ≫ g ≫ h ≅ - ≫ (f ≫ (g ≫ h))` for three 1-morphisms. -/
def yComp3 {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    yMap k y f ≫ (yMap k y g ≫ yMap k y h) ≅ yMap k y (f ≫ (g ≫ h)) :=
  whiskerLeftIso (yMap k y f) (yComp k y g h) ≪≫ yComp k y f (g ≫ h)

/-- The image of a 2-morphism between composites of three 1-morphisms. -/
def yConj3 {a b c d b' c' : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {f' : a ⟶ b'}
    {g' : b' ⟶ c'} {h' : c' ⟶ d} (φ : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h')) :
    yMap k y f ≫ (yMap k y g ≫ yMap k y h) ⟶ yMap k y f' ≫ (yMap k y g' ≫ yMap k y h') :=
  (yComp3 k y f g h).hom ≫ yMap₂ k y φ ≫ (yComp3 k y f' g' h').inv

variable {k y}

@[simp] theorem yComp3_hom_app {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (X : y ⟶ a) :
    (yComp3 k y f g h).hom.hom.app X = (α_ (X ≫ f) g h).hom ≫ (α_ X f (g ≫ h)).hom := rfl

@[simp] theorem yComp3_inv_app {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (X : y ⟶ a) :
    (yComp3 k y f g h).inv.hom.app X = (α_ X f (g ≫ h)).inv ≫ (α_ (X ≫ f) g h).inv := by
  rfl

theorem yConj_comp {a b b' b'' c : B} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ b'} {g' : b' ⟶ c}
    {f'' : a ⟶ b''} {g'' : b'' ⟶ c} (φ : f ≫ g ⟶ f' ≫ g') (ψ : f' ≫ g' ⟶ f'' ≫ g'') :
    yConj k y φ ≫ yConj k y ψ = yConj k y (φ ≫ ψ) := by
  simp [yConj]

theorem yConj3_comp {a b c d b' c' b'' c'' : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    {f' : a ⟶ b'} {g' : b' ⟶ c'} {h' : c' ⟶ d} {f'' : a ⟶ b''} {g'' : b'' ⟶ c''}
    {h'' : c'' ⟶ d} (φ : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h'))
    (ψ : f' ≫ (g' ≫ h') ⟶ f'' ≫ (g'' ≫ h'')) :
    yConj3 k y φ ≫ yConj3 k y ψ = yConj3 k y (φ ≫ ψ) := by
  simp [yConj3]

theorem yConj_zero {a b b' c : B} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ b'} {g' : b' ⟶ c} :
    yConj k y (0 : f ≫ g ⟶ f' ≫ g') = 0 := by
  simp [yConj]

theorem yConj3_sub {a b c d b' c' : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {f' : a ⟶ b'}
    {g' : b' ⟶ c'} {h' : c' ⟶ d} (φ ψ : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h')) :
    yConj3 k y (φ - ψ) = yConj3 k y φ - yConj3 k y ψ := by
  simp [yConj3, Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]

/-- Right whiskering of an image is the image of the right whiskering. -/
theorem yMap₂_whiskerRight {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    yMap₂ k y η ▷ yMap k y g = yConj k y (η ▷ g) := by
  apply ObjectProperty.hom_ext
  ext X
  change (X ◁ η) ▷ g = (α_ X f g).hom ≫ X ◁ (η ▷ g) ≫ (α_ X f' g).inv
  bicategory

/-- Left whiskering by an image is the image of the left whiskering. -/
theorem yMap_whiskerLeft {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g') :
    yMap k y f ◁ yMap₂ k y θ = yConj k y (f ◁ θ) := by
  apply ObjectProperty.hom_ext
  ext X
  change (X ≫ f) ◁ θ = (α_ X f g).hom ≫ X ◁ (f ◁ θ) ≫ (α_ X f g').inv
  bicategory

theorem yMap_whiskerLeft_yConj {a b c d b' : B} (f : a ⟶ b) {g : b ⟶ c} {h : c ⟶ d}
    {g' : b ⟶ b'} {h' : b' ⟶ d} (θ : g ≫ h ⟶ g' ≫ h') :
    yMap k y f ◁ yConj k y θ = yConj3 k y (f ◁ θ) := by
  apply ObjectProperty.hom_ext
  ext X
  change (α_ (X ≫ f) g h).hom ≫ (X ≫ f) ◁ θ ≫ (α_ (X ≫ f) g' h').inv =
    ((α_ (X ≫ f) g h).hom ≫ (α_ X f (g ≫ h)).hom) ≫ X ◁ (f ◁ θ) ≫
      ((α_ X f (g' ≫ h')).inv ≫ (α_ (X ≫ f) g' h').inv)
  bicategory

theorem yConj_whiskerRight_assoc {a b c d b' : B} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ b'}
    {g' : b' ⟶ c} (φ : f ≫ g ⟶ f' ≫ g') (h : c ⟶ d) :
    (α_ (yMap k y f) (yMap k y g) (yMap k y h)).inv ≫ yConj k y φ ▷ yMap k y h ≫
      (α_ (yMap k y f') (yMap k y g') (yMap k y h)).hom =
    yConj3 k y ((α_ f g h).inv ≫ φ ▷ h ≫ (α_ f' g' h).hom) := by
  apply ObjectProperty.hom_ext
  ext X
  change 𝟙 _ ≫ ((α_ X f g).hom ≫ X ◁ φ ≫ (α_ X f' g').inv) ▷ h ≫ 𝟙 _ =
    ((α_ (X ≫ f) g h).hom ≫ (α_ X f (g ≫ h)).hom) ≫
      X ◁ ((α_ f g h).inv ≫ φ ▷ h ≫ (α_ f' g' h).hom) ≫
      ((α_ X f' (g' ≫ h)).inv ≫ (α_ (X ≫ f') g' h).inv)
  bicategory

theorem yMap_whiskerLeft_whiskerLeft {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d}
    (θ : h ⟶ h') : yMap k y f ◁ (yMap k y g ◁ yMap₂ k y θ) = yConj3 k y (f ◁ (g ◁ θ)) := by
  rw [yMap_whiskerLeft, yMap_whiskerLeft_yConj]

theorem yMap_whiskerLeft_whiskerRight {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g')
    (h : c ⟶ d) : yMap k y f ◁ (yMap₂ k y θ ▷ yMap k y h) = yConj3 k y (f ◁ (θ ▷ h)) := by
  rw [yMap₂_whiskerRight, yMap_whiskerLeft_yConj]

theorem yMap₂_whiskerRight_comp {a b c d : B} {f f' : a ⟶ b} (θ : f ⟶ f') (g : b ⟶ c)
    (h : c ⟶ d) : yMap₂ k y θ ▷ (yMap k y g ≫ yMap k y h) = yConj3 k y (θ ▷ (g ≫ h)) := by
  apply ObjectProperty.hom_ext
  ext X
  change (X ◁ θ) ▷ g ▷ h = ((α_ (X ≫ f) g h).hom ≫ (α_ X f (g ≫ h)).hom) ≫
      X ◁ (θ ▷ (g ≫ h)) ≫ ((α_ X f' (g ≫ h)).inv ≫ (α_ (X ≫ f') g h).inv)
  bicategory

end Composites

section Algebra

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]

instance (a b : B) : (yFun k y a b).Linear k where
  map_smul {_ _} η r := by
    apply ObjectProperty.hom_ext
    ext X
    exact Functor.map_smul (precomp b X) r η

theorem yMap₂_smul {a b : B} {f g : a ⟶ b} (r : k) (η : f ⟶ g) :
    yMap₂ k y (r • η) = r • yMap₂ k y η :=
  Functor.map_smul (yFun k y a b) r η

variable (k y)

/-- Conjugation by an isomorphism with an image, as an algebra homomorphism. -/
def yConjAlg {a b : B} {P : yObj k y a ⟶ yObj k y b} {p : a ⟶ b} (e : P ≅ yMap k y p) :
    End p →ₐ[k] End P where
  toFun φ := e.hom ≫ yMap₂ k y φ ≫ e.inv
  map_one' := by
    change e.hom ≫ yMap₂ k y (𝟙 p) ≫ e.inv = 𝟙 P
    rw [yMap₂_id, Category.id_comp, Iso.hom_inv_id]
  map_mul' φ ψ := by
    change e.hom ≫ yMap₂ k y (ψ ≫ φ) ≫ e.inv =
      (e.hom ≫ yMap₂ k y ψ ≫ e.inv) ≫ (e.hom ≫ yMap₂ k y φ ≫ e.inv)
    simp
  map_zero' := by
    change e.hom ≫ yMap₂ k y (0 : p ⟶ p) ≫ e.inv = 0
    rw [yMap₂_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' φ ψ := by
    change e.hom ≫ yMap₂ k y ((φ : p ⟶ p) + ψ) ≫ e.inv =
      (e.hom ≫ yMap₂ k y φ ≫ e.inv : P ⟶ P) + e.hom ≫ yMap₂ k y ψ ≫ e.inv
    rw [yMap₂_add, Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change e.hom ≫ yMap₂ k y (r • 𝟙 p) ≫ e.inv = r • 𝟙 P
    rw [yMap₂_smul, yMap₂_id, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
      Iso.hom_inv_id]

variable {k y}

theorem yConjAlg_apply {a b : B} {P : yObj k y a ⟶ yObj k y b} {p : a ⟶ b} (e : P ≅ yMap k y p)
    (φ : End p) : yConjAlg k y e φ = e.hom ≫ yMap₂ k y φ ≫ e.inv := rfl

theorem yConj_eq_alg {a b c : B} {f : a ⟶ b} {g : b ⟶ c} (φ : f ≫ g ⟶ f ≫ g) :
    yConj k y φ = yConjAlg k y (yComp k y f g) φ := rfl

theorem yConj3_eq_alg {a b c d : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    (φ : f ≫ (g ≫ h) ⟶ f ≫ (g ≫ h)) :
    yConj3 k y φ = yConjAlg k y (yComp3 k y f g h) φ := rfl

end Algebra

end Yoneda

/-! ## Rouquier's data under postcomposition -/

namespace RouqLoc

open Yoneda

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}

variable (k) (y : B)

/-- **Rouquier's data under postcomposition** with `y ⟶ -`: the images of the adjunctions, the
dots and the crossing form Rouquier's data at the same weight. -/
def yoneda (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) :
    RouqLoc (yAdj (k := k) (y := y) adj₁) (yAdj (k := k) (y := y) adj₂) (yMap₂ k y x₁)
      (yMap₂ k y x₂) (yConj k y τ) h where
  slide_left := by
    apply ObjectProperty.hom_ext
    ext X
    have hs := congrArg (fun t => (α_ X E₁ E₂).hom ≫ X ◁ t ≫ (α_ X E₁ E₂).inv) L.slide_left
    simp only [Yoneda.whiskerLeft_sub, Preadditive.sub_comp, Preadditive.comp_sub,
      Bicategory.whiskerLeft_comp, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id,
      Category.assoc] at hs
    change (X ≫ E₁) ◁ x₂ ≫ (α_ X E₁ E₂).hom ≫ X ◁ τ ≫ (α_ X E₁ E₂).inv -
      ((α_ X E₁ E₂).hom ≫ X ◁ τ ≫ (α_ X E₁ E₂).inv) ≫ (X ◁ x₁) ▷ E₂ = 𝟙 _
    rw [← hs]
    simp only [Category.assoc, associator_naturality_right_assoc,
      associator_inv_naturality_middle]
  slide_right := by
    apply ObjectProperty.hom_ext
    ext X
    have hs := congrArg (fun t => (α_ X E₁ E₂).hom ≫ X ◁ t ≫ (α_ X E₁ E₂).inv) L.slide_right
    simp only [Yoneda.whiskerLeft_sub, Preadditive.sub_comp, Preadditive.comp_sub,
      Bicategory.whiskerLeft_comp, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id,
      Category.assoc] at hs
    change ((α_ X E₁ E₂).hom ≫ X ◁ τ ≫ (α_ X E₁ E₂).inv) ≫ (X ≫ E₁) ◁ x₂ -
      (X ◁ x₁) ▷ E₂ ≫ (α_ X E₁ E₂).hom ≫ X ◁ τ ≫ (α_ X E₁ E₂).inv = 𝟙 _
    rw [← hs]
    simp only [Category.assoc, associator_inv_naturality_right,
      associator_naturality_middle_assoc]
  invPos hh := by
    refine SumInvTo.ofFullyFaithful (LinearCat.homForget _ _) (SumInvTo.ofApp fun X => ?_)
    refine ((L.invPos hh).map (precomp b X)).conj (α_ X R₁ E₁) (α_ X E₂ R₂).symm (ρ_ X)
      ?_ ?_
    · change (RightwardCrossing.sigma (yAdj adj₂).unit (yConj k y τ) (yAdj adj₁).counit).hom.app X
        = _
      rw [RouqSl2Generic.sigma_eq_mate, yAdj_mate_app, ← RouqSl2Generic.sigma_eq_mate]
      rfl
    · intro m
      change ((yMap k y R₁ ◁ powComp (yMap₂ k y x₁) m ≫ (yAdj adj₁).counit).hom.app X) = _
      rw [← yMap₂_powComp]
      change (X ≫ R₁) ◁ powComp x₁ m ≫ (α_ X R₁ E₁).hom ≫ X ◁ adj₁.counit ≫ (ρ_ X).hom =
        (α_ X R₁ E₁).hom ≫ X ◁ (R₁ ◁ powComp x₁ m ≫ adj₁.counit) ≫ (ρ_ X).hom
      simp only [Bicategory.whiskerLeft_comp, associator_naturality_right_assoc, Category.assoc]
  invNeg hh := by
    refine SumInvFrom.ofFullyFaithful (LinearCat.homForget _ _) (SumInvFrom.ofApp fun X => ?_)
    refine ((L.invNeg hh).map (precomp b X)).conj (α_ X E₂ R₂).symm (α_ X R₁ E₁) (ρ_ X).symm
      ?_ ?_
    · change (RightwardCrossing.sigma (yAdj adj₂).unit (yConj k y τ) (yAdj adj₁).counit).hom.app X
        = _
      rw [RouqSl2Generic.sigma_eq_mate, yAdj_mate_app, ← RouqSl2Generic.sigma_eq_mate]
      rfl
    · intro m
      change (((yAdj adj₂).unit ≫ powComp (yMap₂ k y x₂) m ▷ yMap k y R₂).hom.app X) = _
      rw [← yMap₂_powComp]
      change ((ρ_ X).inv ≫ X ◁ adj₂.unit ≫ (α_ X E₂ R₂).inv) ≫ (X ◁ powComp x₂ m) ▷ R₂ =
        (ρ_ X).inv ≫ X ◁ (adj₂.unit ≫ powComp x₂ m ▷ R₂) ≫ (α_ X E₂ R₂).inv
      simp only [Bicategory.whiskerLeft_comp, Category.assoc, associator_inv_naturality_middle]

end RouqLoc

/-! ## Rouquier families under postcomposition -/

namespace RouqFamily

open Yoneda QuantumGroup UDot

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}

variable (k) in
/-- **A Rouquier family under postcomposition** with `y ⟶ -`: the objects `y ⟶ S.obj x`, the
functors `- ≫ E_i`, `- ≫ F_i`, and the images of the adjunctions, dots and crossings
(Brundan, arXiv:1501.00350v1, Definition 1.1). -/
def yoneda (S : RouqFamily (B := B) RD) (y : B) :
    RouqFamily (B := LinearCat.{w', w, v} k) RD where
  obj x := yObj k y (S.obj x)
  E i _ _ h := yMap k y (S.E i h)
  F i _ _ h := yMap k y (S.F i h)
  adj i _ _ h := yAdj (S.adj i h)
  dot i _ _ h := yMap₂ k y (S.dot i h)
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := yConj k y (S.cross i j h₁ h₂ h₃ h₄)
  square i _ _ _ h₁ h₂ := by rw [yConj_comp, S.square, yConj_zero]
  braid i _ _ _ _ h₁ h₂ h₃ := by
    rw [yMap_whiskerLeft_yConj, yConj_whiskerRight_assoc, yConj3_comp, yConj3_comp,
      yConj3_comp, yConj3_comp, S.braid]
  loc i _ _ _ h₁ h₂ := (S.loc i h₁ h₂).yoneda k y

variable (S : RouqFamily (B := B) RD) (y : B)

@[simp] theorem yoneda_obj (x : X) : (S.yoneda k y).obj x = yObj k y (S.obj x) := rfl

@[simp] theorem yoneda_E (i : I) {x x' : X} (h : x + RD.iX i = x') :
    (S.yoneda k y).E i h = yMap k y (S.E i h) := rfl

@[simp] theorem yoneda_F (i : I) {x x' : X} (h : x + RD.iX i = x') :
    (S.yoneda k y).F i h = yMap k y (S.F i h) := rfl

theorem yoneda_cross (i j : I) {a b c d : X} (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d) :
    (S.yoneda k y).cross i j h₁ h₂ h₃ h₄ = yConj k y (S.cross i j h₁ h₂ h₃ h₄) := rfl

/-- Brundan's mixed inversion relation (1.7) is preserved by postcomposition: the mixed
sideways crossing of the image is, componentwise, the whiskered mixed sideways crossing
conjugated by associators. -/
theorem yoneda_mixedInversion (M : BrundanMixedInversion S) :
    BrundanMixedInversion (S.yoneda k y) := by
  intro i j hij a b c d hj hi' hi hj'
  suffices h : IsIso ((LinearCat.homForget _ _).map ((S.yoneda k y).mixedSigma i j hj hi' hi hj'))
    from isIso_of_fully_faithful (LinearCat.homForget _ _) _
  rw [LinearCat.homForget_map]
  refine (NatTrans.isIso_iff_isIso_app _).2 fun (Z : y ⟶ S.obj c) => ?_
  change IsIso ((mateEquiv (yAdj (k := k) (S.adj i hi)) (yAdj (k := k) (S.adj i hi'))
    (g := yMap k y (S.E j hj)) (h := yMap k y (S.E j hj'))
    (yConj k y (S.cross i j hj hi' hi hj'))).hom.app Z)
  rw [yAdj_mate_app]
  have hσ : IsIso (S.mixedSigma i j hj hi' hi hj') := M i j hij hj hi' hi hj'
  exact IsIso.comp_isIso' (Iso.isIso_hom (α_ Z (S.F i hi) (S.E j hj)))
    (IsIso.comp_isIso' (whiskerLeft_isIso Z (S.mixedSigma i j hj hi' hi hj'))
      (Iso.isIso_inv (α_ Z (S.E j hj') (S.F i hi'))))

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]

/-- Brundan's mixed upward KLR relations (1.2)–(1.4) are preserved by postcomposition. -/
theorem yoneda_upKLR {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q) :
    RouqUpKLR (S.yoneda k y) Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ := by
    change yConj k y _ ≫ yConj k y _ = _
    rw [yConj_comp, H.square i j hij h₁ h₂ h₃ h₄, yConj_eq_alg, KLR.ncEval_map]
    congr 1
    funext l
    fin_cases l
    · change _ = yMap k y (S.E j h₁) ◁ yMap₂ k y (S.dot i h₂)
      rw [yMap_whiskerLeft, yConj_eq_alg]
      rfl
    · change _ = yMap₂ k y (S.dot j h₁) ▷ yMap k y (S.E i h₂)
      rw [yMap₂_whiskerRight, yConj_eq_alg]
      rfl
  slide_left i j hij _ _ _ _ h₁ h₂ h₃ h₄ := by
    change yMap k y (S.E j h₁) ◁ yMap₂ k y (S.dot i h₂) ≫ yConj k y _ =
      yConj k y _ ≫ yMap₂ k y (S.dot i h₃) ▷ yMap k y (S.E j h₄)
    rw [yMap_whiskerLeft, yMap₂_whiskerRight, yConj_comp, yConj_comp,
      H.slide_left i j hij h₁ h₂ h₃ h₄]
  slide_right i j hij _ _ _ _ h₁ h₂ h₃ h₄ := by
    change yMap₂ k y (S.dot j h₁) ▷ yMap k y (S.E i h₂) ≫ yConj k y _ =
      yConj k y _ ≫ yMap k y (S.E i h₃) ◁ yMap₂ k y (S.dot j h₄)
    rw [yMap_whiskerLeft, yMap₂_whiskerRight, yConj_comp, yConj_comp,
      H.slide_right i j hij h₁ h₂ h₃ h₄]
  braid i j c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
    change yMap k y (S.E c e1) ◁ yConj k y _ ≫
        ((α_ _ _ _).inv ≫ yConj k y _ ▷ yMap k y (S.E j e5) ≫ (α_ _ _ _).hom) ≫
        yMap k y (S.E i e6) ◁ yConj k y _ =
      ((α_ _ _ _).inv ≫ yConj k y _ ▷ yMap k y (S.E i e3) ≫ (α_ _ _ _).hom) ≫
        yMap k y (S.E j e10) ◁ yConj k y _ ≫
        ((α_ _ _ _).inv ≫ yConj k y _ ▷ yMap k y (S.E c e9) ≫ (α_ _ _ _).hom)
    rw [yMap_whiskerLeft_yConj, yMap_whiskerLeft_yConj, yMap_whiskerLeft_yConj,
      yConj_whiskerRight_assoc, yConj_whiskerRight_assoc, yConj_whiskerRight_assoc,
      yConj3_comp, yConj3_comp, yConj3_comp, yConj3_comp,
      H.braid i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12]
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ := by
    change (yMap k y (S.E i h₁) ◁ yConj k y _ ≫
        ((α_ _ _ _).inv ≫ yConj k y _ ▷ yMap k y (S.E j h₅) ≫ (α_ _ _ _).hom) ≫
        yMap k y (S.E i h₁) ◁ yConj k y _) -
      (((α_ _ _ _).inv ≫ yConj k y _ ▷ yMap k y (S.E i h₃) ≫ (α_ _ _ _).hom) ≫
        yMap k y (S.E j h₆) ◁ yConj k y _ ≫
        ((α_ _ _ _).inv ≫ yConj k y _ ▷ yMap k y (S.E i h₃) ≫ (α_ _ _ _).hom)) = _
    rw [yMap_whiskerLeft_yConj, yMap_whiskerLeft_yConj, yMap_whiskerLeft_yConj,
      yConj_whiskerRight_assoc, yConj_whiskerRight_assoc, yConj_whiskerRight_assoc,
      yConj3_comp, yConj3_comp, yConj3_comp, yConj3_comp]
    erw [← yConj3_sub]
    rw [H.braidQ i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇, yConj3_eq_alg, KLR.ncEval_map]
    congr 1
    funext l
    fin_cases l
    · change _ = yMap k y (S.E i h₁) ◁ (yMap k y (S.E j h₂) ◁ yMap₂ k y (S.dot i h₃))
      rw [yMap_whiskerLeft_whiskerLeft, yConj3_eq_alg]
      rfl
    · change _ = yMap k y (S.E i h₁) ◁ (yMap₂ k y (S.dot j h₂) ▷ yMap k y (S.E i h₃))
      rw [yMap_whiskerLeft_whiskerRight, yConj3_eq_alg]
      rfl
    · change _ = yMap₂ k y (S.dot i h₁) ▷ (yMap k y (S.E j h₂) ≫ yMap k y (S.E i h₃))
      rw [yMap₂_whiskerRight_comp, yConj3_eq_alg]
      rfl

end RouqFamily

end Categorification.TwoRep
