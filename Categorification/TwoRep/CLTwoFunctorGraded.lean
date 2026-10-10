/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CLTwoFunctorDot

/-!
# CL Theorem 1.1: the 2-functor `U̇_Q(g) → K` commutes with the grading shift

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §2.1.2: a graded additive `k`-linear 2-functor maps the
hom categories by additive functors that commute with the auto-equivalence `⟨1⟩`. The grading
shift of `U_Q(g)` (`x⟨t⟩ ↦ x⟨t + 1⟩`, `ShiftEnv.shiftHom`) extends to formal direct sums and to the
Karoubi completion (`QStrong.shiftDot`, entrywise). This file proves:

* `GradedHomCat.shiftIso_hom_naturality`, `GradedHomCat.shiftIso_hom_add`: the shift isomorphisms
  `X⟦n⟧ ≅ X` of the graded-Hom category are natural in `X` and additive in `n`;
* `QStrong.twoFunctorShiftShiftIso`: on each hom category, `twoFunctorShift` commutes with the shift,
  `F(x⟨t + 1⟩) ≅ F(x⟨t⟩)⟨1⟩`, naturally in 2-morphisms;
* `QStrong.twoFunctorDotShiftIso`: on each hom category, `twoFunctorDot` commutes with the shift
  of `U̇_Q(g)`, naturally (an isomorphism of functors, obtained from the previous one by the
  universal properties of the additive envelope, `MatExtGen.ext`, and of the Karoubi envelope,
  `KarMatExt.ext`; the general statement is `DotExt.extNatIso`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

/-! ## The shift on the hom categories of a shift envelope -/

namespace ShiftEnv

variable {R : Type*} [CommRing R] {A : Type u} [Bicategory.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] {G : GradedTwoCells R A}

/-- The grading shift `(f, s) ↦ (f, s + t)` on a hom category of the shift envelope. -/
def shiftHom (t : ℤ) (a b : ShiftEnv G) : (a ⟶ b) ⥤ (a ⟶ b) where
  obj f := ⟨f.hom, f.sh + t⟩
  map {f g} η := mk₂ (f := (⟨f.hom, f.sh + t⟩ : a ⟶ b)) (g := (⟨g.hom, g.sh + t⟩ : a ⟶ b))
    (val₂ (f := f) (g := g) η) (G.mem_of_eq η.2 (by simp only; ring))
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem shiftHom_obj_hom (t : ℤ) {a b : ShiftEnv G} (f : a ⟶ b) :
    ((shiftHom t a b).obj f).hom = f.hom := rfl

@[simp] theorem shiftHom_obj_sh (t : ℤ) {a b : ShiftEnv G} (f : a ⟶ b) :
    ((shiftHom t a b).obj f).sh = f.sh + t := rfl

@[simp] theorem val₂_shiftHom_map (t : ℤ) {a b : ShiftEnv G} {f g : a ⟶ b} (η : f ⟶ g) :
    val₂ ((shiftHom t a b).map η) = val₂ η := rfl

instance (t : ℤ) (a b : ShiftEnv G) : (shiftHom t a b).Additive where
  map_add := rfl

instance (t : ℤ) (a b : ShiftEnv G) : (shiftHom t a b).Linear R where
  map_smul _ _ := rfl

end ShiftEnv

/-! ## The shift isomorphisms of a graded-Hom category -/

namespace TwoRep.GradedHomCat

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- `X⟦n⟧ ≅ X` is natural in `X`. -/
theorem shiftIso_hom_naturality {X Y : C} (φ : X ⟶ Y) (n : ℤ) :
    (shiftIso X n).hom ≫ (incl C).map φ = (incl C).map (φ⟦n⟧') ≫ (shiftIso Y n).hom := by
  rw [shiftIso_hom, incl_map, homOf_comp_homOf _ _ (zero_add n), ShiftedHom.comp_mk₀,
    Category.id_comp]
  exact homOf_eq_incl_map_comp_shiftIso n (φ⟦n⟧' : X⟦n⟧ ⟶ Y⟦n⟧)

/-- `X⟦t + n⟧ ≅ X` is the composite of `X⟦t⟧⟦n⟧ ≅ X⟦t⟧ ≅ X`. -/
theorem shiftIso_hom_add (X : C) (t n c : ℤ) (h : t + n = c) :
    (shiftIso X c).hom = (incl C).map ((shiftFunctorAdd' C t n c h).hom.app X) ≫
      (shiftIso (X⟦t⟧) n).hom ≫ (shiftIso X t).hom := by
  subst h
  rw [shiftIso_hom, shiftIso_hom, shiftIso_hom, homOf_comp_homOf _ _ rfl, incl_map,
    homOf_comp_homOf _ _ (add_zero (t + n)), ShiftedHom.mk₀_comp]
  congr 1
  simp [ShiftedHom.comp]

theorem shiftIso_inv_add (X : C) (t n c : ℤ) (h : t + n = c) :
    (shiftIso X c).inv ≫ (incl C).map ((shiftFunctorAdd' C t n c h).hom.app X) =
      (shiftIso X t).inv ≫ (shiftIso (X⟦t⟧) n).inv := by
  rw [Iso.inv_comp_eq, shiftIso_hom_add X t n c h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The shift of a morphism, conjugated by the shift isomorphisms. -/
theorem incl_map_shift {X Y : C} (φ : X ⟶ Y) (n : ℤ) :
    (incl C).map (φ⟦n⟧') = (shiftIso X n).hom ≫ (incl C).map φ ≫ (shiftIso Y n).inv := by
  rw [reassoc_of% shiftIso_hom_naturality φ n, Iso.hom_inv_id, Category.comp_id]

/-- A morphism of `C` defined by conjugating a graded morphism `θ` by the shift isomorphisms, and
the same with all shifts raised by `1`, differ by the shift functor. -/
theorem shift_conj {X₁ X₂ : C} {t₁ t₂ c₁ c₂ : ℤ} (h₁ : t₁ + 1 = c₁) (h₂ : t₂ + 1 = c₂)
    (φ : X₁⟦t₁⟧ ⟶ X₂⟦t₂⟧) (φ' : X₁⟦c₁⟧ ⟶ X₂⟦c₂⟧) (θ : mk X₁ ⟶ mk X₂)
    (hφ : (incl C).map φ = (shiftIso X₁ t₁).hom ≫ θ ≫ (shiftIso X₂ t₂).inv)
    (hφ' : (incl C).map φ' = (shiftIso X₁ c₁).hom ≫ θ ≫ (shiftIso X₂ c₂).inv) :
    φ' ≫ ((shiftFunctorAdd' C t₂ 1 c₂ h₂).app X₂).hom =
      ((shiftFunctorAdd' C t₁ 1 c₁ h₁).app X₁).hom ≫ φ⟦(1 : ℤ)⟧' := by
  apply (incl C).map_injective
  rw [Functor.map_comp, Functor.map_comp, hφ', incl_map_shift, hφ, Category.assoc,
    Category.assoc, Iso.app_hom, shiftIso_inv_add X₂ t₂ 1 c₂ h₂, shiftIso_hom_add X₁ t₁ 1 c₁ h₁]
  simp only [Category.assoc]
  rfl

end TwoRep.GradedHomCat



/-! ## `twoFunctorShift` commutes with the shift -/

namespace TwoRep

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

/-- The shift constraint of `twoFunctorShift` at a 1-morphism `f = x⟨t⟩`:
`F(x⟨t + 1⟩) ≅ F(x⟨t⟩)⟨1⟩`. -/
def shiftConstraint {a b : UQShift RD S₀} (f : a ⟶ b) :
    (twoFunctorShift S₀ S hrQ).map ((shiftHom 1 a b).obj f) ≅
      ((twoFunctorShift S₀ S hrQ).map f)⟦(1 : ℤ)⟧ :=
  (shiftFunctorAdd' _ ((shiftHOM S₀ S hrQ).map f).sh 1
    ((shiftHOM S₀ S hrQ).map ((shiftHom 1 a b).obj f)).sh
    (shiftHOM_sh_shiftHom S₀ S hrQ f)).app (bHom ((shiftHOM S₀ S hrQ).map f))

-- The final unification identifies the underlying 1-morphisms of `F(x⟨1⟩)` and `F(x)`.
set_option maxHeartbeats 1000000 in
theorem shiftConstraint_naturality {a b : UQShift RD S₀} {f g : a ⟶ b} (η : f ⟶ g) :
    (twoFunctorShift S₀ S hrQ).map₂ ((shiftHom 1 a b).map η) ≫ (shiftConstraint S₀ S hrQ g).hom =
      (shiftConstraint S₀ S hrQ f).hom ≫ ((twoFunctorShift S₀ S hrQ).map₂ η)⟦(1 : ℤ)⟧' := by
  -- Elaborating the auxiliary statement first (without the expected type) is much faster.
  have key := GradedHomCat.shift_conj (shiftHOM_sh_shiftHom S₀ S hrQ f)
    (shiftHOM_sh_shiftHom S₀ S hrQ g) _ _ _ (incl₂_realize_map₂ (shiftHOM S₀ S hrQ) η)
    (incl₂_realize_map₂ (shiftHOM S₀ S hrQ) ((shiftHom 1 a b).map η))
  exact key

/-- **`twoFunctorShift` commutes with the shift** on each hom category:
`F(x⟨t + 1⟩) ≅ F(x⟨t⟩)⟨1⟩`, naturally in 2-morphisms. -/
def twoFunctorShiftShiftIso (a b : UQShift RD S₀) :
    shiftHom 1 a b ⋙ (twoFunctorShift S₀ S hrQ).mapFunctor a b ≅
      (twoFunctorShift S₀ S hrQ).mapFunctor a b ⋙ shiftFunctor _ (1 : ℤ) :=
  NatIso.ofComponents (fun f => shiftConstraint S₀ S hrQ f)
    (fun η => shiftConstraint_naturality S₀ S hrQ η)

attribute [local instance] preadditiveBicategory_of_graded

variable (RD) in
/-- The grading shift `⟨1⟩` on a hom category of `U̇_Q(g) = Kar (UQShift RD S₀)`: the shift of
`UQShift RD S₀`, applied entrywise to matrices and to idempotents. -/
def shiftDot (a b : UQDot RD S₀) :
    Idempotents.Karoubi (Mat_ (a.obj.obj ⟶ b.obj.obj)) ⥤
      Idempotents.Karoubi (Mat_ (a.obj.obj ⟶ b.obj.obj)) :=
  mapKaroubi (shiftHom 1 a.obj.obj b.obj.obj).mapMat_

instance shiftDot_additive (a b : UQDot RD S₀) : (shiftDot RD S₀ a b).Additive :=
  mapKaroubi_additive _

/-- `twoFunctorDot`, as a functor on the hom category `Karoubi (Mat_ (a ⟶ b))`. -/
abbrev dotHom (a b : UQDot RD S₀) :
    Idempotents.Karoubi (Mat_ (a.obj.obj ⟶ b.obj.obj)) ⥤
      ((twoFunctorDot S₀ S hrQ).obj a ⟶ (twoFunctorDot S₀ S hrQ).obj b) :=
  (twoFunctorDot S₀ S hrQ).mapFunctor a b

instance dotHom_additive (a b : UQDot RD S₀) : (dotHom S₀ S hrQ a b).Additive where
  map_add {_ _ η θ} := twoFunctorDot_map₂_add S₀ S hrQ η θ

/-- On the image of `UQShift RD S₀`, `twoFunctorDot` is `twoFunctorShift`. -/
def dotHomInclIso (a b : UQDot RD S₀) :
    KarMatExt.incl (a.obj.obj ⟶ b.obj.obj) ⋙ dotHom S₀ S hrQ a b ≅
      (twoFunctorShift S₀ S hrQ).mapFunctor a.obj.obj b.obj.obj := by
  -- The two types agree up to the normalization of universe levels (see `kernel_exact`).
  kernel_exact DotExt.inclNatIso (twoFunctorShift S₀ S hrQ) (twoFunctorShift_addHyp S₀ S hrQ) a b

/-- **`twoFunctorDot` commutes with the grading shift** on each hom category of `U̇_Q(g)`:
`F(X⟨1⟩) ≅ F(X)⟨1⟩`, naturally in `X` (CL §2.1.2: a graded 2-functor). -/
def twoFunctorDotShiftIso (a b : UQDot RD S₀) :
    shiftDot RD S₀ a b ⋙ dotHom S₀ S hrQ a b ≅ dotHom S₀ S hrQ a b ⋙ shiftFunctor _ (1 : ℤ) := by
  kernel_exact DotExt.extNatIso (twoFunctorShift S₀ S hrQ) (twoFunctorShift_addHyp S₀ S hrQ) a b
    (shiftHom 1 a.obj.obj b.obj.obj) (shiftFunctor _ (1 : ℤ))
    (twoFunctorShiftShiftIso S₀ S hrQ a.obj.obj b.obj.obj)

end QStrong

end Model

end TwoRep

end Categorification
