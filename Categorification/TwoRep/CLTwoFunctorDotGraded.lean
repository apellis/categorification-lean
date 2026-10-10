/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CLTwoFunctorGradedCoh
import Categorification.TwoRep.DotExtensionShift

/-!
# CL Theorem 1.1: the 2-functor `U̇_Q(g) → K` is graded

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §1.2 and §2.1.2: a 2-representation of `U̇_Q(g)` is a
graded additive `k`-linear 2-functor. In the graded 2-categories `U̇_Q(g)` and `K`, the grading
shift `⟨1⟩` of the hom categories commutes with horizontal composition on either side
(`x⟨1⟩ y ≅ (x y)⟨1⟩ ≅ x (y⟨1⟩)`), and the 2-functor commutes with `⟨1⟩` compatibly with these
isomorphisms and with its composition and identity constraints.

* `ShiftEnv.leftShift`, `ShiftEnv.rightShift`: the shift structures of a shift envelope
  (`x⟨1⟩ y = (x y)⟨1⟩ = x (y⟨1⟩)`);
* `GradedBicategory.leftShift`, `GradedBicategory.rightShift`: those of a graded bicategory
  (`X⟦1⟧ Y ≅ (X Y)⟦1⟧ ≅ X (Y⟦1⟧)`, `whiskerRightShiftIso`, `whiskerLeftShiftIso`);
* `QStrong.shiftCompatLeft`, `QStrong.shiftCompatRight`: `twoFunctorShift` commutes with them
  (`twoFunctorShift_mapComp_shiftLeft/Right`);
* `QStrong.twoFunctorDot_mapComp_shiftLeft`, `QStrong.twoFunctorDot_mapComp_shiftRight`,
  `QStrong.twoFunctorDot_mapId_shiftLeft`, `QStrong.twoFunctorDot_mapId_shiftRight`: the grading
  isomorphisms `twoFunctorDotShiftIso` of `twoFunctorDot : U̇_Q(g) ⥤ᵖ B` are coherent with its
  composition and identity constraints, where the shift of `U̇_Q(g)` commutes with composition by
  `QStrong.shiftDotCompLeft`, `QStrong.shiftDotCompRight` (the shift structures induced on the
  additive Karoubi envelope, `LeftShift.kar`, `RightShift.kar`). The proof is the general
  `LeftShiftCompat.ext`, `RightShiftCompat.ext`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

/-! ## The shift structures of a shift envelope -/

namespace ShiftEnv

variable {R : Type*} [CommRing R] {A : Type u} [Bicategory.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)] (G : GradedTwoCells R A)

/-- The left shift structure of a shift envelope: `x⟨1⟩ y = (x y)⟨1⟩`. -/
def leftShift : TwoRep.LeftShift (ShiftEnv G) where
  S a b := shiftHom 1 a b
  iso f g := shiftCompLeft f g
  iso_naturality_left _ _ := hom₂_ext ((Category.comp_id _).trans (Category.id_comp _).symm)
  iso_naturality_right := @fun _ _ _ _ _ _ _ =>
    hom₂_ext ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The right shift structure of a shift envelope: `x (y⟨1⟩) = (x y)⟨1⟩`. -/
def rightShift : TwoRep.RightShift (ShiftEnv G) where
  S a b := shiftHom 1 a b
  iso f g := shiftCompRight f g
  iso_naturality_left _ _ := hom₂_ext ((Category.comp_id _).trans (Category.id_comp _).symm)
  iso_naturality_right := @fun _ _ _ _ _ _ _ =>
    hom₂_ext ((Category.comp_id _).trans (Category.id_comp _).symm)

end ShiftEnv

namespace TwoRep

/-! ## The shift structures of a graded bicategory -/

namespace GradedBicategory

open GradedHomBicat

variable (B : Type u) [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

/-- The left shift structure of a graded bicategory: `X⟦1⟧ Y ≅ (X Y)⟦1⟧`. -/
def leftShift : LeftShift B where
  S a b := shiftFunctor (a ⟶ b) (1 : ℤ)
  iso f g := whiskerRightShiftIso f g 1
  iso_naturality_left := @fun a _ _ _ _ η g =>
    ((postcomp a g).commShiftIso (1 : ℤ)).hom.naturality η
  iso_naturality_right := @fun _ _ _ f g g' θ => by
    apply incl₂_injective
    rw [incl₂_comp, incl₂_comp, ← whiskerLeft_incl₂, incl₂_whiskerRightShiftIso_hom,
      incl₂_whiskerRightShiftIso_hom, incl₂_shift, ← whiskerLeft_incl₂]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [whisker_exchange_assoc]

/-- The right shift structure of a graded bicategory: `X (Y⟦1⟧) ≅ (X Y)⟦1⟧`. -/
def rightShift : RightShift B where
  S a b := shiftFunctor (a ⟶ b) (1 : ℤ)
  iso f g := whiskerLeftShiftIso f g 1
  iso_naturality_left := @fun _ _ _ f f' η g => by
    apply incl₂_injective
    rw [incl₂_comp, incl₂_comp, ← incl₂_whiskerRight, incl₂_whiskerLeftShiftIso_hom,
      incl₂_whiskerLeftShiftIso_hom, incl₂_shift, ← incl₂_whiskerRight]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← whisker_exchange_assoc]
  iso_naturality_right := @fun _ _ c f _ _ θ =>
    ((precomp c f).commShiftIso (1 : ℤ)).hom.naturality θ

end GradedBicategory

/-! ## `twoFunctorShift` and `twoFunctorDot` are graded -/

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

/-- `twoFunctorShift` commutes with the left shift structures
(`twoFunctorShift_mapComp_shiftLeft`). -/
def shiftCompatLeft : LeftShiftCompat (twoFunctorShift S₀ S hrQ)
    (ShiftEnv.leftShift (presGrading (CL.presCL RD k S₀) (deg RD)))
    (GradedBicategory.leftShift B) where
  φ a b := twoFunctorShiftShiftIso S₀ S hrQ a b
  coh f g := twoFunctorShift_mapComp_shiftLeft S₀ S hrQ f g

/-- `twoFunctorShift` commutes with the right shift structures
(`twoFunctorShift_mapComp_shiftRight`). -/
def shiftCompatRight : RightShiftCompat (twoFunctorShift S₀ S hrQ)
    (ShiftEnv.rightShift (presGrading (CL.presCL RD k S₀) (deg RD)))
    (GradedBicategory.rightShift B) where
  φ a b := twoFunctorShiftShiftIso S₀ S hrQ a b
  coh f g := twoFunctorShift_mapComp_shiftRight S₀ S hrQ f g

attribute [local instance] preadditiveBicategory_of_graded

variable (RD) in
/-- `X⟨1⟩ Y ≅ (X Y)⟨1⟩` in `U̇_Q(g)`: the shift structure of the shift envelope `UQShift RD S₀`,
induced on the additive Karoubi envelope (entrywise, by a diagonal matrix of identities). -/
def shiftDotCompLeft {a b c : UQDot RD S₀} (X₁ : a ⟶ b) (Y₁ : b ⟶ c) :
    (shiftDot RD S₀ a b).obj X₁ ≫ Y₁ ≅ (shiftDot RD S₀ a c).obj (X₁ ≫ Y₁) :=
  (ShiftEnv.leftShift (presGrading (CL.presCL RD k S₀) (deg RD))).kar.iso X₁ Y₁

variable (RD) in
/-- `X (Y⟨1⟩) ≅ (X Y)⟨1⟩` in `U̇_Q(g)` (see `shiftDotCompLeft`). -/
def shiftDotCompRight {a b c : UQDot RD S₀} (X₁ : a ⟶ b) (Y₁ : b ⟶ c) :
    X₁ ≫ (shiftDot RD S₀ b c).obj Y₁ ≅ (shiftDot RD S₀ a c).obj (X₁ ≫ Y₁) :=
  (ShiftEnv.rightShift (presGrading (CL.presCL RD k S₀) (deg RD))).kar.iso X₁ Y₁

/-- **CL Theorem 1.1: `twoFunctorDot` is graded, compatibly with composition on the left**: the
grading isomorphisms `F(X⟨1⟩) ≅ F(X)⟨1⟩` (`twoFunctorDotShiftIso`) intertwine the composition
constraints of `F = twoFunctorDot` at `(X⟨1⟩, Y)` and `(X, Y)`, the isomorphism
`X⟨1⟩ Y ≅ (X Y)⟨1⟩` of `U̇_Q(g)` and `F(X)⟨1⟩ F(Y) ≅ (F(X) F(Y))⟨1⟩` in `B`. -/
theorem twoFunctorDot_mapComp_shiftLeft {a b c : UQDot RD S₀} (X₁ : a ⟶ b) (Y₁ : b ⟶ c) :
    ((twoFunctorDot S₀ S hrQ).mapComp ((shiftDot RD S₀ a b).obj X₁) Y₁).hom ≫
        (twoFunctorDotShiftIso S₀ S hrQ a b).hom.app X₁ ▷ (twoFunctorDot S₀ S hrQ).map Y₁ ≫
          (whiskerRightShiftIso ((twoFunctorDot S₀ S hrQ).map X₁)
            ((twoFunctorDot S₀ S hrQ).map Y₁) 1).hom =
      (twoFunctorDot S₀ S hrQ).map₂ (shiftDotCompLeft RD S₀ X₁ Y₁).hom ≫
        (twoFunctorDotShiftIso S₀ S hrQ a c).hom.app (X₁ ≫ Y₁) ≫
          ((twoFunctorDot S₀ S hrQ).mapComp X₁ Y₁).hom⟦(1 : ℤ)⟧' := by
  kernel_exact ((shiftCompatLeft S₀ S hrQ).ext (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ)).coh X₁ Y₁

/-- **CL Theorem 1.1: `twoFunctorDot` is graded, compatibly with composition on the right** (see
`twoFunctorDot_mapComp_shiftLeft`). -/
theorem twoFunctorDot_mapComp_shiftRight {a b c : UQDot RD S₀} (X₁ : a ⟶ b) (Y₁ : b ⟶ c) :
    ((twoFunctorDot S₀ S hrQ).mapComp X₁ ((shiftDot RD S₀ b c).obj Y₁)).hom ≫
        (twoFunctorDot S₀ S hrQ).map X₁ ◁ (twoFunctorDotShiftIso S₀ S hrQ b c).hom.app Y₁ ≫
          (whiskerLeftShiftIso ((twoFunctorDot S₀ S hrQ).map X₁)
            ((twoFunctorDot S₀ S hrQ).map Y₁) 1).hom =
      (twoFunctorDot S₀ S hrQ).map₂ (shiftDotCompRight RD S₀ X₁ Y₁).hom ≫
        (twoFunctorDotShiftIso S₀ S hrQ a c).hom.app (X₁ ≫ Y₁) ≫
          ((twoFunctorDot S₀ S hrQ).mapComp X₁ Y₁).hom⟦(1 : ℤ)⟧' := by
  kernel_exact ((shiftCompatRight S₀ S hrQ).ext (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ)).coh X₁ Y₁

/-- **CL Theorem 1.1: `twoFunctorDot` is graded, compatibly with the identity constraints, on the
left**: under `1⟨1⟩ Y ≅ (1 Y)⟨1⟩ ≅ Y⟨1⟩`, the grading isomorphism of `Y` is the composite of the
composition constraint at `(1⟨1⟩, Y)`, the grading isomorphism of `1`, the identity constraint and
`1⟦1⟧ F(Y) ≅ F(Y)⟦1⟧`. -/
theorem twoFunctorDot_mapId_shiftLeft {a b : UQDot RD S₀} (Y₁ : a ⟶ b) :
    ((twoFunctorDot S₀ S hrQ).mapComp ((shiftDot RD S₀ a a).obj (𝟙 a)) Y₁).hom ≫
        (twoFunctorDotShiftIso S₀ S hrQ a a).hom.app (𝟙 a) ▷ (twoFunctorDot S₀ S hrQ).map Y₁ ≫
          ((twoFunctorDot S₀ S hrQ).mapId a).hom⟦(1 : ℤ)⟧' ▷ (twoFunctorDot S₀ S hrQ).map Y₁ ≫
            (idShiftCompIso ((twoFunctorDot S₀ S hrQ).map Y₁) 1).hom =
      (twoFunctorDot S₀ S hrQ).map₂ ((shiftDotCompLeft RD S₀ (𝟙 a) Y₁).hom ≫
        (shiftDot RD S₀ a b).map (λ_ Y₁).hom) ≫
        (twoFunctorDotShiftIso S₀ S hrQ a b).hom.app Y₁ := by
  kernel_exact ((shiftCompatLeft S₀ S hrQ).ext (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ)).mapId Y₁

/-- **CL Theorem 1.1: `twoFunctorDot` is graded, compatibly with the identity constraints, on the
right** (see `twoFunctorDot_mapId_shiftLeft`). -/
theorem twoFunctorDot_mapId_shiftRight {a b : UQDot RD S₀} (X₁ : a ⟶ b) :
    ((twoFunctorDot S₀ S hrQ).mapComp X₁ ((shiftDot RD S₀ b b).obj (𝟙 b))).hom ≫
        (twoFunctorDot S₀ S hrQ).map X₁ ◁ (twoFunctorDotShiftIso S₀ S hrQ b b).hom.app (𝟙 b) ≫
          (twoFunctorDot S₀ S hrQ).map X₁ ◁ ((twoFunctorDot S₀ S hrQ).mapId b).hom⟦(1 : ℤ)⟧' ≫
            (compIdShiftIso ((twoFunctorDot S₀ S hrQ).map X₁) 1).hom =
      (twoFunctorDot S₀ S hrQ).map₂ ((shiftDotCompRight RD S₀ X₁ (𝟙 b)).hom ≫
        (shiftDot RD S₀ a b).map (ρ_ X₁).hom) ≫
        (twoFunctorDotShiftIso S₀ S hrQ a b).hom.app X₁ := by
  kernel_exact ((shiftCompatRight S₀ S hrQ).ext (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ)).mapId X₁

end QStrong

end Model

end TwoRep

end Categorification
