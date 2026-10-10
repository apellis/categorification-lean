/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CLTwoFunctorGraded

/-!
# CL Theorem 1.1: coherence of the grading isomorphisms with composition

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §2.1.2: in a graded 2-category the shift `⟨1⟩` of the
hom categories commutes with horizontal composition, `(x⟨1⟩) y ≅ (x y)⟨1⟩ ≅ x (y⟨1⟩)`, and a graded
2-functor commutes with `⟨1⟩` compatibly with these isomorphisms and with its composition and
identity constraints. For `QStrong.twoFunctorShift : UQShift RD S₀ ⥤ᵖ B` this file proves:

* `QStrong.twoFunctorShift_mapComp_shiftLeft`, `QStrong.twoFunctorShift_mapComp_shiftRight`: the
  isomorphisms `F(x⟨1⟩) ≅ F(x)⟨1⟩` (`QStrong.shiftConstraint`) are compatible with the composition
  constraints of `F`, the isomorphisms `x⟨1⟩ y = (x y)⟨1⟩ = x (y⟨1⟩)` of `UQShift RD S₀`
  (`ShiftEnv.shiftCompLeft`, `ShiftEnv.shiftCompRight`) and the isomorphisms
  `X⟨1⟩ Y ≅ (X Y)⟨1⟩ ≅ X (Y⟨1⟩)` of `B` (`whiskerRightShiftIso`, `whiskerLeftShiftIso`);
* `QStrong.twoFunctorShift_mapId_shiftLeft`, `QStrong.twoFunctorShift_mapId_shiftRight`: the same
  for the identity constraints, i.e. with the unitors `1⟨1⟩ x ≅ x⟨1⟩ ≅ x 1⟨1⟩`.

The computations take place in the graded-Hom bicategory of `B`, where `X⟦n⟧ ≅ X` by the shift
isomorphisms `shiftIso₁` (homogeneous of degree `n`); the general statements are
`GradedHomBicat.shift_mapComp_left` and `GradedHomBicat.shift_mapComp_right`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

/-! ## Composition with a shifted 1-morphism in a shift envelope -/

namespace ShiftEnv

variable {R : Type*} [CommRing R] {A : Type u} [Bicategory.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] {G : GradedTwoCells R A}
  {a b c : ShiftEnv G}

/-- `x⟨1⟩ y = (x y)⟨1⟩` in the shift envelope (the identity 2-morphism). -/
def shiftCompLeft (f : a ⟶ b) (g : b ⟶ c) :
    (shiftHom 1 a b).obj f ≫ g ≅ (shiftHom 1 a c).obj (f ≫ g) :=
  isoMk (Iso.refl _) (by simp only [comp_sh, shiftHom_obj_sh]; ring) (G.id_mem _) (G.id_mem _)

/-- `x (y⟨1⟩) = (x y)⟨1⟩` in the shift envelope (the identity 2-morphism). -/
def shiftCompRight (f : a ⟶ b) (g : b ⟶ c) :
    f ≫ (shiftHom 1 b c).obj g ≅ (shiftHom 1 a c).obj (f ≫ g) :=
  isoMk (Iso.refl _) (by simp only [comp_sh, shiftHom_obj_sh]; ring) (G.id_mem _) (G.id_mem _)

/-- The composition constraint of a composite of induced pseudofunctors of shift envelopes. -/
theorem val₂_comp_map_mapComp_hom {A' : Type*} [Bicategory A'] [∀ a b : A', Preadditive (a ⟶ b)]
    [∀ a b : A', Linear R (a ⟶ b)] {G' : GradedTwoCells R A'} {A'' : Type*} [Bicategory A'']
    [∀ a b : A'', Preadditive (a ⟶ b)] [∀ a b : A'', Linear R (a ⟶ b)]
    {G'' : GradedTwoCells R A''} (Φ₁ : GradedPseudofunctor G G') (Φ₂ : GradedPseudofunctor G' G'')
    (f : a ⟶ b) (g : b ⟶ c) :
    val₂ (((map Φ₁).comp (map Φ₂)).mapComp f g).hom =
      Φ₂.F.map₂ (Φ₁.F.mapComp f.hom g.hom).hom ≫
        (Φ₂.F.mapComp (Φ₁.F.map f.hom) (Φ₁.F.map g.hom)).hom := rfl

/-- `1⟨1⟩ x ≅ x⟨1⟩` in the shift envelope (the left unitor). -/
def shiftIdComp (f : a ⟶ b) : (shiftHom 1 a a).obj (𝟙 a) ≫ f ≅ (shiftHom 1 a b).obj f :=
  isoMk (λ_ f.hom) (by simp only [comp_sh, shiftHom_obj_sh, id_sh]; ring)
    (G.leftUnitor_hom_mem _) (G.leftUnitor_inv_mem _)

/-- `x 1⟨1⟩ ≅ x⟨1⟩` in the shift envelope (the right unitor). -/
def shiftCompId (f : a ⟶ b) : f ≫ (shiftHom 1 b b).obj (𝟙 b) ≅ (shiftHom 1 a b).obj f :=
  isoMk (ρ_ f.hom) (by simp only [comp_sh, shiftHom_obj_sh, id_sh]; ring)
    (G.rightUnitor_hom_mem _) (G.rightUnitor_inv_mem _)

theorem shiftIdComp_hom (f : a ⟶ b) :
    (shiftIdComp f).hom = (shiftCompLeft (𝟙 a) f).hom ≫ (shiftHom 1 a b).map (λ_ f).hom :=
  hom₂_ext (Category.id_comp _).symm

theorem shiftCompId_hom (f : a ⟶ b) :
    (shiftCompId f).hom = (shiftCompRight f (𝟙 b)).hom ≫ (shiftHom 1 a b).map (ρ_ f).hom :=
  hom₂_ext (Category.id_comp _).symm

@[simp] theorem val₂_shiftCompLeft_hom (f : a ⟶ b) (g : b ⟶ c) :
    val₂ (shiftCompLeft f g).hom = 𝟙 _ := rfl

@[simp] theorem val₂_shiftCompRight_hom (f : a ⟶ b) (g : b ⟶ c) :
    val₂ (shiftCompRight f g).hom = 𝟙 _ := rfl

end ShiftEnv

/-! ## Shift isomorphisms and whiskering in the graded-Hom bicategory -/

namespace TwoRep

namespace GradedHomBicat

open GradedHomCat

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  {a b c : B}

theorem shiftIso₁_hom_whiskerRight (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    (shiftIso₁ f n).hom ▷ of₁ g =
      incl₂ (whiskerRightShiftIso f g n).hom ≫ (shiftIso₁ (f ≫ g) n).hom := by
  show whiskerRightHom _ _ g (homOf n (𝟙 (f⟦n⟧) : ShiftedHom (f⟦n⟧) f n)) = _
  rw [whiskerRightHom_homOf, homOf_eq_incl_map_comp_shiftIso]
  congr 1
  simp [shWhiskerRight, ShiftedHom.map, whiskerRightShiftIso, incl₂]
  erw [Category.id_comp]

theorem whiskerLeft_shiftIso₁_hom (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    of₁ f ◁ (shiftIso₁ g n).hom =
      incl₂ (whiskerLeftShiftIso f g n).hom ≫ (shiftIso₁ (f ≫ g) n).hom := by
  show whiskerLeftHom f _ _ (homOf n (𝟙 (g⟦n⟧) : ShiftedHom (g⟦n⟧) g n)) = _
  rw [whiskerLeftHom_homOf, homOf_eq_incl_map_comp_shiftIso]
  congr 1
  simp [shWhiskerLeft, ShiftedHom.map, whiskerLeftShiftIso, incl₂]
  erw [Category.id_comp]

/-- The shift-addition isomorphism, read in the graded-Hom bicategory. -/
theorem incl₂_shiftFunctorAdd'_hom_app (X : a ⟶ b) (t n c : ℤ) (h : t + n = c) :
    incl₂ (((shiftFunctorAdd' (a ⟶ b) t n c h).app X).hom) =
      (shiftIso₁ X c).hom ≫ (shiftIso₁ X t).inv ≫ (shiftIso₁ (X⟦t⟧) n).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, Iso.eq_comp_inv, Category.assoc]
  exact (shiftIso_hom_add X t n c h).symm

/-- The shift of a 2-morphism, read in the graded-Hom bicategory. -/
theorem incl₂_shift {X Y : a ⟶ b} (φ : X ⟶ Y) (n : ℤ) :
    incl₂ (φ⟦n⟧') = (shiftIso₁ X n).hom ≫ incl₂ φ ≫ (shiftIso₁ Y n).inv :=
  incl_map_shift φ n

theorem incl₂_whiskerRightShiftIso_hom (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    incl₂ (whiskerRightShiftIso f g n).hom =
      (shiftIso₁ f n).hom ▷ of₁ g ≫ (shiftIso₁ (f ≫ g) n).inv := by
  rw [shiftIso₁_hom_whiskerRight, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem incl₂_whiskerLeftShiftIso_hom (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) :
    incl₂ (whiskerLeftShiftIso f g n).hom =
      of₁ f ◁ (shiftIso₁ g n).hom ≫ (shiftIso₁ (f ≫ g) n).inv := by
  rw [whiskerLeft_shiftIso₁_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Coherence of a shift constraint with a composition constraint, on the left**, in the form in
which it arises for the realization of a pseudofunctor into the shift envelope: `m₁` and `m₀` are
the composition constraints at `(x⟨1⟩, y)` and `(x, y)` (both given by the same degree-`0`
2-morphism `M` conjugated by shift isomorphisms) and `e` is the image of `x⟨1⟩ y = (x y)⟨1⟩`. -/
theorem shift_mapComp_left {X : a ⟶ b} {Y : b ⟶ c} {Z : a ⟶ c} (M₁ M₀ : of₁ Z ⟶ of₁ (X ≫ Y))
    (hM : M₁ = M₀)
    {t s t' u v w : ℤ} (ht : t + 1 = t') (hv : w + 1 = v)
    (m₁ : Z⟦u⟧ ⟶ X⟦t'⟧ ≫ Y⟦s⟧)
    (hm₁ : incl₂ m₁ = (shiftIso₁ Z u).hom ≫ M₁ ≫ of₁ X ◁ (shiftIso₁ Y s).inv ≫
      (shiftIso₁ X t').inv ▷ of₁ (Y⟦s⟧))
    (m₀ : Z⟦w⟧ ⟶ X⟦t⟧ ≫ Y⟦s⟧)
    (hm₀ : incl₂ m₀ = (shiftIso₁ Z w).hom ≫ M₀ ≫ of₁ X ◁ (shiftIso₁ Y s).inv ≫
      (shiftIso₁ X t).inv ▷ of₁ (Y⟦s⟧))
    (e : Z⟦u⟧ ⟶ Z⟦v⟧) (he : incl₂ e = (shiftIso₁ Z u).hom ≫ (shiftIso₁ Z v).inv) :
    m₁ ≫ ((shiftFunctorAdd' (a ⟶ b) t 1 t' ht).app X).hom ▷ Y⟦s⟧ ≫
        (whiskerRightShiftIso (X⟦t⟧) (Y⟦s⟧) 1).hom =
      e ≫ ((shiftFunctorAdd' (a ⟶ c) w 1 v hv).app Z).hom ≫ m₀⟦(1 : ℤ)⟧' := by
  subst hM
  apply incl₂_injective
  rw [incl₂_comp, incl₂_comp, incl₂_comp, incl₂_comp, ← incl₂_whiskerRight,
    incl₂_shiftFunctorAdd'_hom_app, incl₂_shiftFunctorAdd'_hom_app,
    incl₂_whiskerRightShiftIso_hom, incl₂_shift, hm₁, hm₀, he]
  simp only [Category.assoc, comp_whiskerRight, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc]

/-- **Coherence of a shift constraint with a composition constraint, on the right** (see
`shift_mapComp_left`). -/
theorem shift_mapComp_right {X : a ⟶ b} {Y : b ⟶ c} {Z : a ⟶ c} (M₁ M₀ : of₁ Z ⟶ of₁ (X ≫ Y))
    (hM : M₁ = M₀)
    {t s s' u v w : ℤ} (hs : s + 1 = s') (hv : w + 1 = v)
    (m₁ : Z⟦u⟧ ⟶ X⟦t⟧ ≫ Y⟦s'⟧)
    (hm₁ : incl₂ m₁ = (shiftIso₁ Z u).hom ≫ M₁ ≫ of₁ X ◁ (shiftIso₁ Y s').inv ≫
      (shiftIso₁ X t).inv ▷ of₁ (Y⟦s'⟧))
    (m₀ : Z⟦w⟧ ⟶ X⟦t⟧ ≫ Y⟦s⟧)
    (hm₀ : incl₂ m₀ = (shiftIso₁ Z w).hom ≫ M₀ ≫ of₁ X ◁ (shiftIso₁ Y s).inv ≫
      (shiftIso₁ X t).inv ▷ of₁ (Y⟦s⟧))
    (e : Z⟦u⟧ ⟶ Z⟦v⟧) (he : incl₂ e = (shiftIso₁ Z u).hom ≫ (shiftIso₁ Z v).inv) :
    m₁ ≫ X⟦t⟧ ◁ ((shiftFunctorAdd' (b ⟶ c) s 1 s' hs).app Y).hom ≫
        (whiskerLeftShiftIso (X⟦t⟧) (Y⟦s⟧) 1).hom =
      e ≫ ((shiftFunctorAdd' (a ⟶ c) w 1 v hv).app Z).hom ≫ m₀⟦(1 : ℤ)⟧' := by
  subst hM
  apply incl₂_injective
  rw [incl₂_comp, incl₂_comp, incl₂_comp, incl₂_comp, ← whiskerLeft_incl₂,
    incl₂_shiftFunctorAdd'_hom_app, incl₂_shiftFunctorAdd'_hom_app,
    incl₂_whiskerLeftShiftIso_hom, incl₂_shift, hm₁, hm₀, he]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc]
  simp only [whiskerLeft_inv_hom_assoc, Iso.inv_hom_id_assoc]

end GradedHomBicat

/-! ## The composition constraints of a realization -/

namespace ShiftEnvK

open GradedHomBicat ShiftEnv

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  [GradedBicategory.IsLinear B k]
  {𝒳 : Type u₁} [Bicategory 𝒳] (Q : Pseudofunctor 𝒳 (ShEnvK k B))

/-- The composition constraint of `realize Q` is that of `Q` conjugated by the shift
isomorphisms. -/
theorem incl₂_realize_mapComp_hom {x y z : 𝒳} (f : x ⟶ y) (g : y ⟶ z) :
    incl₂ ((realize Q).mapComp f g).hom =
      (shiftIso₁ (bHom (Q.map (f ≫ g))) (Q.map (f ≫ g)).sh).hom ≫ val₂ (Q.mapComp f g).hom ≫
        of₁ (bHom (Q.map f)) ◁ (shiftIso₁ (bHom (Q.map g)) (Q.map g).sh).inv ≫
          (shiftIso₁ (bHom (Q.map f)) (Q.map f).sh).inv ▷ of₁ (realizeMap Q g) := by
  refine (congrArg val₂ (toShiftEnv_map₂_pre (k := k)
    (((realizeCopy Q).mapComp f g ≪≫ ((toShiftEnv k B).mapComp _ _).symm).hom))).trans ?_
  exact Category.comp_id _

end ShiftEnvK

/-! ## `twoFunctorShift` is a graded 2-functor -/

section Model

open GradedHomBicat ShiftEnv ShiftEnvK PresGrading
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : RootDatum C X Y}

namespace QStrong

variable (S₀ : CL.CLScalars C k) (S : QStrong B C RD k (CL.qCL S₀))
  (hrQ : ∀ i, S.rQ i = S₀.r i)

theorem shiftHOM_sh_shiftHom {a b : UQShift RD S₀} (f : a ⟶ b) :
    ((shiftHOM S₀ S hrQ).map f).sh + 1 = ((shiftHOM S₀ S hrQ).map ((shiftHom 1 a b).obj f)).sh := by
  show _ + _ + _ + 1 = _ + 1 + _ + _
  simp only [ShiftEnv.map_map_hom, shiftHom_obj_hom]
  ring

theorem incl₂_twoFunctorShift_map₂_shiftCompLeft {a b c : UQShift RD S₀} (f : a ⟶ b)
    (g : b ⟶ c) :
    incl₂ ((twoFunctorShift S₀ S hrQ).map₂ (shiftCompLeft f g).hom) =
      (shiftIso₁ (bHom ((shiftHOM S₀ S hrQ).map (f ≫ g)))
          ((shiftHOM S₀ S hrQ).map ((shiftHom 1 a b).obj f ≫ g)).sh).hom ≫
        (shiftIso₁ (bHom ((shiftHOM S₀ S hrQ).map (f ≫ g)))
          ((shiftHOM S₀ S hrQ).map ((shiftHom 1 a c).obj (f ≫ g))).sh).inv := by
  refine (incl₂_realize_map₂ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact (congrArg (· ≫ _) ((twoFunctorHOM S₀ S hrQ).map₂_id _)).trans
    (Category.id_comp _)

theorem incl₂_twoFunctorShift_map₂_shiftCompRight {a b c : UQShift RD S₀} (f : a ⟶ b)
    (g : b ⟶ c) :
    incl₂ ((twoFunctorShift S₀ S hrQ).map₂ (shiftCompRight f g).hom) =
      (shiftIso₁ (bHom ((shiftHOM S₀ S hrQ).map (f ≫ g)))
          ((shiftHOM S₀ S hrQ).map (f ≫ (shiftHom 1 b c).obj g)).sh).hom ≫
        (shiftIso₁ (bHom ((shiftHOM S₀ S hrQ).map (f ≫ g)))
          ((shiftHOM S₀ S hrQ).map ((shiftHom 1 a c).obj (f ≫ g))).sh).inv := by
  refine (incl₂_realize_map₂ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact (congrArg (· ≫ _) ((twoFunctorHOM S₀ S hrQ).map₂_id _)).trans
    (Category.id_comp _)

-- The final unification identifies the underlying 1-morphisms of `F(x⟨1⟩)` and `F(x)`.
set_option maxHeartbeats 1000000 in
/-- **`twoFunctorShift` is graded, compatibly with composition on the left**: the shift constraints
`F(x⟨1⟩) ≅ F(x)⟨1⟩` intertwine the composition constraints of `F` at `(x⟨1⟩, y)` and `(x, y)`, the
identity `x⟨1⟩ y = (x y)⟨1⟩` and `F(x)⟨1⟩ F(y) ≅ (F(x) F(y))⟨1⟩`. -/
theorem twoFunctorShift_mapComp_shiftLeft {a b c : UQShift RD S₀} (f : a ⟶ b) (g : b ⟶ c) :
    ((twoFunctorShift S₀ S hrQ).mapComp ((shiftHom 1 a b).obj f) g).hom ≫
        (shiftConstraint S₀ S hrQ f).hom ▷ (twoFunctorShift S₀ S hrQ).map g ≫
          (whiskerRightShiftIso ((twoFunctorShift S₀ S hrQ).map f)
            ((twoFunctorShift S₀ S hrQ).map g) 1).hom =
      (twoFunctorShift S₀ S hrQ).map₂ (shiftCompLeft f g).hom ≫
        (shiftConstraint S₀ S hrQ (f ≫ g)).hom ≫
          ((twoFunctorShift S₀ S hrQ).mapComp f g).hom⟦(1 : ℤ)⟧' := by
  -- Elaborating the auxiliary statement first (without the expected type) avoids identifying
  -- the underlying 1-morphisms of `F(x⟨1⟩)` and `F(x)` by unfolding.
  have key := shift_mapComp_left _ _
    ((val₂_comp_map_mapComp_hom _ _ ((shiftHom 1 a b).obj f) g).trans
      (val₂_comp_map_mapComp_hom _ _ f g).symm)
    (shiftHOM_sh_shiftHom S₀ S hrQ f) (shiftHOM_sh_shiftHom S₀ S hrQ (f ≫ g)) _
    (incl₂_realize_mapComp_hom (shiftHOM S₀ S hrQ) ((shiftHom 1 a b).obj f) g) _
    (incl₂_realize_mapComp_hom (shiftHOM S₀ S hrQ) f g) _
    (incl₂_twoFunctorShift_map₂_shiftCompLeft S₀ S hrQ f g)
  exact key

set_option maxHeartbeats 1000000 in
/-- **`twoFunctorShift` is graded, compatibly with composition on the right** (see
`twoFunctorShift_mapComp_shiftLeft`). -/
theorem twoFunctorShift_mapComp_shiftRight {a b c : UQShift RD S₀} (f : a ⟶ b) (g : b ⟶ c) :
    ((twoFunctorShift S₀ S hrQ).mapComp f ((shiftHom 1 b c).obj g)).hom ≫
        (twoFunctorShift S₀ S hrQ).map f ◁ (shiftConstraint S₀ S hrQ g).hom ≫
          (whiskerLeftShiftIso ((twoFunctorShift S₀ S hrQ).map f)
            ((twoFunctorShift S₀ S hrQ).map g) 1).hom =
      (twoFunctorShift S₀ S hrQ).map₂ (shiftCompRight f g).hom ≫
        (shiftConstraint S₀ S hrQ (f ≫ g)).hom ≫
          ((twoFunctorShift S₀ S hrQ).mapComp f g).hom⟦(1 : ℤ)⟧' := by
  have key := shift_mapComp_right _ _
    ((val₂_comp_map_mapComp_hom _ _ f ((shiftHom 1 b c).obj g)).trans
      (val₂_comp_map_mapComp_hom _ _ f g).symm)
    (shiftHOM_sh_shiftHom S₀ S hrQ g) (shiftHOM_sh_shiftHom S₀ S hrQ (f ≫ g)) _
    (incl₂_realize_mapComp_hom (shiftHOM S₀ S hrQ) f ((shiftHom 1 b c).obj g)) _
    (incl₂_realize_mapComp_hom (shiftHOM S₀ S hrQ) f g) _
    (incl₂_twoFunctorShift_map₂_shiftCompRight S₀ S hrQ f g)
  exact key

/-- **`twoFunctorShift` is graded, compatibly with the identity constraints, on the left**: under
`1⟨1⟩ x ≅ x⟨1⟩`, the shift constraint of `x` is the composite of the composition constraint at
`(1⟨1⟩, x)`, the shift constraint of `1`, the identity constraint and `1⟨1⟩ X ≅ X⟨1⟩`. -/
theorem twoFunctorShift_mapId_shiftLeft {a b : UQShift RD S₀} (f : a ⟶ b) :
    ((twoFunctorShift S₀ S hrQ).mapComp ((shiftHom 1 a a).obj (𝟙 a)) f).hom ≫
        (shiftConstraint S₀ S hrQ (𝟙 a)).hom ▷ (twoFunctorShift S₀ S hrQ).map f ≫
          ((twoFunctorShift S₀ S hrQ).mapId a).hom⟦(1 : ℤ)⟧' ▷ (twoFunctorShift S₀ S hrQ).map f ≫
            (idShiftCompIso ((twoFunctorShift S₀ S hrQ).map f) 1).hom =
      (twoFunctorShift S₀ S hrQ).map₂ (shiftIdComp f).hom ≫ (shiftConstraint S₀ S hrQ f).hom := by
  have h4 : ((twoFunctorShift S₀ S hrQ).mapId a).hom⟦(1 : ℤ)⟧' ▷ (twoFunctorShift S₀ S hrQ).map f ≫
        (whiskerRightShiftIso (𝟙 _) ((twoFunctorShift S₀ S hrQ).map f) 1).hom =
      (whiskerRightShiftIso ((twoFunctorShift S₀ S hrQ).map (𝟙 a))
          ((twoFunctorShift S₀ S hrQ).map f) 1).hom ≫
        (((twoFunctorShift S₀ S hrQ).mapId a).hom ▷ (twoFunctorShift S₀ S hrQ).map f)⟦(1 : ℤ)⟧' :=
    ((postcomp _ ((twoFunctorShift S₀ S hrQ).map f)).commShiftIso (1 : ℤ)).hom.naturality _
  rw [shiftIdComp_hom, PrelaxFunctor.map₂_comp, Category.assoc, shiftConstraint_naturality,
    Pseudofunctor.map₂_left_unitor, Functor.map_comp, Functor.map_comp,
    ← reassoc_of% (twoFunctorShift_mapComp_shiftLeft S₀ S hrQ (𝟙 a) f), ← reassoc_of% h4]
  simp only [idShiftCompIso, Iso.trans_hom, Functor.mapIso_hom]

/-- **`twoFunctorShift` is graded, compatibly with the identity constraints, on the right** (see
`twoFunctorShift_mapId_shiftLeft`). -/
theorem twoFunctorShift_mapId_shiftRight {a b : UQShift RD S₀} (f : a ⟶ b) :
    ((twoFunctorShift S₀ S hrQ).mapComp f ((shiftHom 1 b b).obj (𝟙 b))).hom ≫
        (twoFunctorShift S₀ S hrQ).map f ◁ (shiftConstraint S₀ S hrQ (𝟙 b)).hom ≫
          (twoFunctorShift S₀ S hrQ).map f ◁ ((twoFunctorShift S₀ S hrQ).mapId b).hom⟦(1 : ℤ)⟧' ≫
            (compIdShiftIso ((twoFunctorShift S₀ S hrQ).map f) 1).hom =
      (twoFunctorShift S₀ S hrQ).map₂ (shiftCompId f).hom ≫ (shiftConstraint S₀ S hrQ f).hom := by
  have h4 : (twoFunctorShift S₀ S hrQ).map f ◁ ((twoFunctorShift S₀ S hrQ).mapId b).hom⟦(1 : ℤ)⟧' ≫
        (whiskerLeftShiftIso ((twoFunctorShift S₀ S hrQ).map f) (𝟙 _) 1).hom =
      (whiskerLeftShiftIso ((twoFunctorShift S₀ S hrQ).map f)
          ((twoFunctorShift S₀ S hrQ).map (𝟙 b)) 1).hom ≫
        ((twoFunctorShift S₀ S hrQ).map f ◁ ((twoFunctorShift S₀ S hrQ).mapId b).hom)⟦(1 : ℤ)⟧' :=
    ((precomp _ ((twoFunctorShift S₀ S hrQ).map f)).commShiftIso (1 : ℤ)).hom.naturality _
  rw [shiftCompId_hom, PrelaxFunctor.map₂_comp, Category.assoc, shiftConstraint_naturality,
    Pseudofunctor.map₂_right_unitor, Functor.map_comp, Functor.map_comp,
    ← reassoc_of% (twoFunctorShift_mapComp_shiftRight S₀ S hrQ f (𝟙 b)), ← reassoc_of% h4]
  simp only [compIdShiftIso, Iso.trans_hom, Functor.mapIso_hom]

end QStrong

end Model

end TwoRep

end Categorification
