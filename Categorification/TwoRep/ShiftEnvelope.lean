/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import StringDiagrams.Super.PiTwoCategory

/-!
# The shift envelope of a bicategory with graded 2-morphisms

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §2.1.2: in a graded additive `k`-linear 2-category
`Hom^l(A, B) = Hom(A, B⟨l⟩)`; the 2-category `U_Q(g)` (Definition 1.1, following Khovanov–Lauda)
has 1-morphisms `x⟨t⟩` for words `x` and shifts `t ∈ ℤ`, and its 2-morphisms `x⟨t⟩ → y⟨t'⟩` are the
diagrams `x → y` of degree `t' - t`.

For a bicategory `A` whose 2-morphism spaces carry a `ℤ`-grading by submodules (`GradedTwoCells`),
compatible with vertical composition and whiskering, with the associators and unitors in degree
`0`, the **shift envelope** `ShiftEnv G` has the objects of `A`, the 1-morphisms `(f, t)`
(`f` a 1-morphism of `A`, `t ∈ ℤ`), composed by `(f, t) ≫ (g, s) = (f ≫ g, t + s)`, and the
2-morphisms `(f, t) ⟶ (g, t')` the 2-morphisms `f ⟶ g` of degree `t' - t`. It is a bicategory with
preadditive, `R`-linear hom categories and additive whiskering.

A pseudofunctor `Φ : A → A'` between such bicategories which shifts degrees by an additive offset
`c` on 1-morphisms (a 2-morphism `f ⟶ g` of degree `n` goes to one of degree `n + c g - c f`; the
structure isomorphisms of `Φ` in degree `0`) induces `ShiftEnv.map Φ c : ShiftEnv G ⥤ᵖ ShiftEnv G'`,
`(f, t) ↦ (Φ f, t + c f)`.

The convention `Hom((x, t), (y, t')) = degree t' - t` is that of CL's target 2-categories
(`Hom^l(A, B) = Hom(A, B⟨l⟩)`); Khovanov–Lauda's `x{t}` (`Categorification.Diagrams.KL3.Karoubi`,
degree `t - t'`) is `(x, -t)`.
-/

noncomputable section

namespace Categorification

open CategoryTheory Bicategory

universe w v u w' v' u'

/-- A `ℤ`-grading of the 2-morphisms of a bicategory by `R`-submodules, compatible with vertical
composition and whiskering, with identities, associators and unitors in degree `0`. -/
structure GradedTwoCells (R : Type*) [CommRing R] (A : Type u) [Bicategory.{w, v} A]
    [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] where
  /-- The 2-morphisms of degree `n`. -/
  deg : ∀ {a b : A} (f g : a ⟶ b), ℤ → Submodule R (f ⟶ g)
  id_mem : ∀ {a b : A} (f : a ⟶ b), 𝟙 f ∈ deg f f 0
  comp_mem : ∀ {a b : A} {f g h : a ⟶ b} {η : f ⟶ g} {θ : g ⟶ h} {m n : ℤ},
    η ∈ deg f g m → θ ∈ deg g h n → η ≫ θ ∈ deg f h (m + n)
  whiskerLeft_mem : ∀ {a b c : A} (f : a ⟶ b) {g h : b ⟶ c} {θ : g ⟶ h} {n : ℤ},
    θ ∈ deg g h n → f ◁ θ ∈ deg (f ≫ g) (f ≫ h) n
  whiskerRight_mem : ∀ {a b c : A} {f g : a ⟶ b} {η : f ⟶ g} {n : ℤ} (h : b ⟶ c),
    η ∈ deg f g n → η ▷ h ∈ deg (f ≫ h) (g ≫ h) n
  associator_hom_mem : ∀ {a b c d : A} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    (α_ f g h).hom ∈ deg _ _ 0
  associator_inv_mem : ∀ {a b c d : A} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    (α_ f g h).inv ∈ deg _ _ 0
  leftUnitor_hom_mem : ∀ {a b : A} (f : a ⟶ b), (λ_ f).hom ∈ deg _ _ 0
  leftUnitor_inv_mem : ∀ {a b : A} (f : a ⟶ b), (λ_ f).inv ∈ deg _ _ 0
  rightUnitor_hom_mem : ∀ {a b : A} (f : a ⟶ b), (ρ_ f).hom ∈ deg _ _ 0
  rightUnitor_inv_mem : ∀ {a b : A} (f : a ⟶ b), (ρ_ f).inv ∈ deg _ _ 0

namespace GradedTwoCells

variable {R : Type*} [CommRing R] {A : Type u} [Bicategory.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] (G : GradedTwoCells R A)

theorem mem_of_eq {a b : A} {f g : a ⟶ b} {η : f ⟶ g} {m n : ℤ} (h : η ∈ G.deg f g m)
    (e : m = n) : η ∈ G.deg f g n := e ▸ h

end GradedTwoCells

/-- The shift envelope of a bicategory with graded 2-morphisms. -/
@[ext]
structure ShiftEnv {R : Type*} [CommRing R] {A : Type u} [Bicategory.{w, v} A]
    [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] (G : GradedTwoCells R A) where
  /-- The underlying object. -/
  as : A

namespace ShiftEnv

variable {R : Type*} [CommRing R] {A : Type u} [Bicategory.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] {G : GradedTwoCells R A}

/-- A 1-morphism `(f, t)` of the shift envelope. -/
@[ext]
structure Hom (a b : ShiftEnv G) where
  /-- The underlying 1-morphism. -/
  hom : a.as ⟶ b.as
  /-- The shift. -/
  sh : ℤ

instance : CategoryStruct (ShiftEnv G) where
  Hom := Hom
  id a := ⟨𝟙 a.as, 0⟩
  comp f g := ⟨f.hom ≫ g.hom, f.sh + g.sh⟩

variable {a b c d e : ShiftEnv G}

@[simp] theorem id_hom' (a : ShiftEnv G) : (𝟙 a : Hom a a).hom = 𝟙 a.as := rfl
@[simp] theorem id_sh (a : ShiftEnv G) : (𝟙 a : Hom a a).sh = 0 := rfl
@[simp] theorem comp_hom' (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g : Hom a c).hom = f.hom ≫ g.hom := rfl
@[simp] theorem comp_sh (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g : Hom a c).sh = f.sh + g.sh := rfl

/-- The 2-morphisms `(f, t) ⟶ (g, t')`: the 2-morphisms `f ⟶ g` of degree `t' - t`. -/
abbrev Hom₂ (f g : a ⟶ b) : Type _ := G.deg f.hom g.hom (g.sh - f.sh)

instance homCategory (a b : ShiftEnv G) : Category (a ⟶ b) where
  Hom f g := Hom₂ f g
  id f := ⟨𝟙 f.hom, G.mem_of_eq (G.id_mem _) (by simp)⟩
  comp η θ := ⟨η.1 ≫ θ.1, G.mem_of_eq (G.comp_mem η.2 θ.2) (by ring)⟩
  id_comp η := Subtype.ext (Category.id_comp η.1)
  comp_id η := Subtype.ext (Category.comp_id η.1)
  assoc η θ ι := Subtype.ext (Category.assoc η.1 θ.1 ι.1)

/-- The underlying 2-morphism of `A`. -/
abbrev val₂ {f g : a ⟶ b} (η : f ⟶ g) : f.hom ⟶ g.hom := (η : Hom₂ f g).1

@[ext] theorem hom₂_ext {f g : a ⟶ b} {η θ : f ⟶ g} (h : val₂ η = val₂ θ) : η = θ :=
  Subtype.ext h

@[simp] theorem val₂_id (f : a ⟶ b) : val₂ (𝟙 f) = 𝟙 f.hom := rfl
@[simp] theorem val₂_comp {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    val₂ (η ≫ θ) = val₂ η ≫ val₂ θ := rfl

/-- A 2-morphism of `A` of the right degree as a 2-morphism of the envelope. -/
abbrev mk₂ {f g : a ⟶ b} (η : f.hom ⟶ g.hom) (h : η ∈ G.deg f.hom g.hom (g.sh - f.sh)) :
    f ⟶ g := (⟨η, h⟩ : Hom₂ f g)

@[simp] theorem val₂_mk₂ {f g : a ⟶ b} (η : f.hom ⟶ g.hom)
    (h : η ∈ G.deg f.hom g.hom (g.sh - f.sh)) : val₂ (mk₂ η h) = η := rfl

/-- An isomorphism of `A` with both directions of degree `0` between 1-morphisms with equal
shifts. -/
def isoMk {f g : a ⟶ b} (e : f.hom ≅ g.hom) (hs : f.sh = g.sh) (h₁ : e.hom ∈ G.deg _ _ 0)
    (h₂ : e.inv ∈ G.deg _ _ 0) : f ≅ g where
  hom := mk₂ e.hom (G.mem_of_eq h₁ (by omega))
  inv := mk₂ e.inv (G.mem_of_eq h₂ (by omega))
  hom_inv_id := hom₂_ext (by simp)
  inv_hom_id := hom₂_ext (by simp)

@[simp] theorem isoMk_hom {f g : a ⟶ b} (e : f.hom ≅ g.hom) (hs : f.sh = g.sh)
    (h₁ : e.hom ∈ G.deg _ _ 0) (h₂ : e.inv ∈ G.deg _ _ 0) : val₂ (isoMk e hs h₁ h₂).hom = e.hom :=
  rfl

@[simp] theorem isoMk_inv {f g : a ⟶ b} (e : f.hom ≅ g.hom) (hs : f.sh = g.sh)
    (h₁ : e.hom ∈ G.deg _ _ 0) (h₂ : e.inv ∈ G.deg _ _ 0) : val₂ (isoMk e hs h₁ h₂).inv = e.inv :=
  rfl

instance bicategory : Bicategory (ShiftEnv G) where
  homCategory := homCategory
  whiskerLeft f _ _ θ := mk₂ (f.hom ◁ val₂ θ) (G.mem_of_eq (G.whiskerLeft_mem _ θ.2) (by
    simp only [comp_sh]; ring))
  whiskerRight η h := mk₂ (val₂ η ▷ h.hom) (G.mem_of_eq (G.whiskerRight_mem _ η.2) (by
    simp only [comp_sh]; ring))
  associator f g h := isoMk (α_ f.hom g.hom h.hom) (add_assoc _ _ _)
    (G.associator_hom_mem _ _ _) (G.associator_inv_mem _ _ _)
  leftUnitor f := isoMk (λ_ f.hom) (zero_add _) (G.leftUnitor_hom_mem _) (G.leftUnitor_inv_mem _)
  rightUnitor f := isoMk (ρ_ f.hom) (add_zero _) (G.rightUnitor_hom_mem _)
    (G.rightUnitor_inv_mem _)
  whiskerLeft_id f g := hom₂_ext (whiskerLeft_id _ _)
  whiskerLeft_comp f _ _ _ η θ := hom₂_ext (whiskerLeft_comp _ _ _)
  id_whiskerLeft η := hom₂_ext (id_whiskerLeft _)
  comp_whiskerLeft f g _ _ η := hom₂_ext (comp_whiskerLeft _ _ _)
  id_whiskerRight f g := hom₂_ext (id_whiskerRight _ _)
  comp_whiskerRight η θ i := hom₂_ext (comp_whiskerRight _ _ _)
  whiskerRight_id η := hom₂_ext (whiskerRight_id _)
  whiskerRight_comp η g h := hom₂_ext (whiskerRight_comp _ _ _)
  whisker_assoc f _ _ η h := hom₂_ext (whisker_assoc _ _ _)
  whisker_exchange η θ := hom₂_ext (whisker_exchange _ _)
  pentagon f g h i := hom₂_ext (pentagon _ _ _ _)
  triangle f g := hom₂_ext (triangle _ _)

@[simp] theorem val₂_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (θ : g ⟶ h) :
    val₂ (f ◁ θ) = f.hom ◁ val₂ θ := rfl
@[simp] theorem val₂_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    val₂ (η ▷ h) = val₂ η ▷ h.hom := rfl
@[simp] theorem val₂_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    val₂ (α_ f g h).hom = (α_ f.hom g.hom h.hom).hom := rfl
@[simp] theorem val₂_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    val₂ (α_ f g h).inv = (α_ f.hom g.hom h.hom).inv := rfl
@[simp] theorem val₂_leftUnitor_hom (f : a ⟶ b) : val₂ (λ_ f).hom = (λ_ f.hom).hom := rfl
@[simp] theorem val₂_leftUnitor_inv (f : a ⟶ b) : val₂ (λ_ f).inv = (λ_ f.hom).inv := rfl
@[simp] theorem val₂_rightUnitor_hom (f : a ⟶ b) : val₂ (ρ_ f).hom = (ρ_ f.hom).hom := rfl
@[simp] theorem val₂_rightUnitor_inv (f : a ⟶ b) : val₂ (ρ_ f).inv = (ρ_ f.hom).inv := rfl

/-! ### Additive and linear structure -/

instance (a b : ShiftEnv G) : Preadditive (a ⟶ b) where
  homGroup f g := inferInstanceAs (AddCommGroup (Hom₂ f g))
  add_comp _ _ _ η θ ι := hom₂_ext (Preadditive.add_comp _ _ _ (val₂ η) (val₂ θ) (val₂ ι))
  comp_add _ _ _ η θ ι := hom₂_ext (Preadditive.comp_add _ _ _ (val₂ η) (val₂ θ) (val₂ ι))

@[simp] theorem val₂_add {f g : a ⟶ b} (η θ : f ⟶ g) : val₂ (η + θ) = val₂ η + val₂ θ := rfl
@[simp] theorem val₂_zero (f g : a ⟶ b) : val₂ (0 : f ⟶ g) = 0 := rfl
@[simp] theorem val₂_neg {f g : a ⟶ b} (η : f ⟶ g) : val₂ (-η) = -val₂ η := rfl
@[simp] theorem val₂_sub {f g : a ⟶ b} (η θ : f ⟶ g) : val₂ (η - θ) = val₂ η - val₂ θ := rfl

instance (a b : ShiftEnv G) : Linear R (a ⟶ b) where
  homModule f g := inferInstanceAs (Module R (Hom₂ f g))
  smul_comp _ _ _ r η θ := hom₂_ext (Linear.smul_comp _ _ _ r (val₂ η) (val₂ θ))
  comp_smul _ _ _ η r θ := hom₂_ext (Linear.comp_smul _ _ _ (val₂ η) r (val₂ θ))

@[simp] theorem val₂_smul {f g : a ⟶ b} (r : R) (η : f ⟶ g) : val₂ (r • η) = r • val₂ η := rfl

instance [StringDiagrams.PreadditiveBicategory A] :
    StringDiagrams.PreadditiveBicategory (ShiftEnv G) where
  whiskerLeft_add f _ _ η θ :=
    hom₂_ext (StringDiagrams.PreadditiveBicategory.whiskerLeft_add f.hom (val₂ η) (val₂ θ))
  add_whiskerRight η θ h :=
    hom₂_ext (StringDiagrams.PreadditiveBicategory.add_whiskerRight (val₂ η) (val₂ θ) h.hom)

/-! ### Functoriality -/

variable {A' : Type u'} [Bicategory.{w', v'} A'] [∀ a b : A', Preadditive (a ⟶ b)]
  [∀ a b : A', Linear R (a ⟶ b)] {G' : GradedTwoCells R A'}

/-- The data making a pseudofunctor compatible with gradings, up to an additive offset `c` on
1-morphisms. -/
structure GradedPseudofunctor (G : GradedTwoCells R A) (G' : GradedTwoCells R A') where
  /-- The pseudofunctor. -/
  F : Pseudofunctor A A'
  /-- The offset of a 1-morphism. -/
  c : ∀ {a b : A}, (a ⟶ b) → ℤ
  c_id : ∀ a : A, c (𝟙 a) = 0
  c_comp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d), c (f ≫ g) = c f + c g
  map₂_mem : ∀ {a b : A} {f g : a ⟶ b} {η : f ⟶ g} {n : ℤ}, η ∈ G.deg f g n →
    F.map₂ η ∈ G'.deg (F.map f) (F.map g) (n + c g - c f)
  mapId_hom_mem : ∀ a : A, (F.mapId a).hom ∈ G'.deg _ _ 0
  mapId_inv_mem : ∀ a : A, (F.mapId a).inv ∈ G'.deg _ _ 0
  mapComp_hom_mem : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d), (F.mapComp f g).hom ∈ G'.deg _ _ 0
  mapComp_inv_mem : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d), (F.mapComp f g).inv ∈ G'.deg _ _ 0

variable (Φ : GradedPseudofunctor G G')

/-- **The induced pseudofunctor of shift envelopes**, `(f, t) ↦ (Φ f, t + c f)`. -/
def map : Pseudofunctor (ShiftEnv G) (ShiftEnv G') where
  obj a := ⟨Φ.F.obj a.as⟩
  map f := ⟨Φ.F.map f.hom, f.sh + Φ.c f.hom⟩
  map₂ η := mk₂ (Φ.F.map₂ (val₂ η)) (G'.mem_of_eq (Φ.map₂_mem η.2) (by ring))
  map₂_id f := hom₂_ext (Φ.F.map₂_id _)
  map₂_comp η θ := hom₂_ext (Φ.F.map₂_comp _ _)
  mapId a := isoMk (Φ.F.mapId a.as) (by simp [Φ.c_id]) (Φ.mapId_hom_mem _) (Φ.mapId_inv_mem _)
  mapComp f g := isoMk (Φ.F.mapComp f.hom g.hom) (by simp only [comp_sh, comp_hom', Φ.c_comp]; ring)
    (Φ.mapComp_hom_mem _ _) (Φ.mapComp_inv_mem _ _)
  map₂_whisker_left f g h η := hom₂_ext (Φ.F.map₂_whisker_left _ _)
  map₂_whisker_right η h := hom₂_ext (Φ.F.map₂_whisker_right _ _)
  map₂_associator f g h := hom₂_ext (Φ.F.map₂_associator _ _ _)
  map₂_left_unitor f := hom₂_ext (Φ.F.map₂_left_unitor _)
  map₂_right_unitor f := hom₂_ext (Φ.F.map₂_right_unitor _)

@[simp] theorem map_obj (a : ShiftEnv G) : ((map Φ).obj a).as = Φ.F.obj a.as := rfl
@[simp] theorem map_map_hom (f : a ⟶ b) : ((map Φ).map f).hom = Φ.F.map f.hom := rfl
@[simp] theorem map_map_sh (f : a ⟶ b) : ((map Φ).map f).sh = f.sh + Φ.c f.hom := rfl
@[simp] theorem val₂_map_map₂ {f g : a ⟶ b} (η : f ⟶ g) :
    val₂ ((map Φ).map₂ η) = Φ.F.map₂ (val₂ η) := rfl

end ShiftEnv

end Categorification
