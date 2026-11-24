/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Bigraded.DegreeZero
import DG.Bigraded.Derived
import DG.Category.Derived.Induction

/-!
# Graded cup and cap for a scalar character

For the one-dimensional coefficient case of Webster,
arXiv:1309.3796v2, Definition 7.4, scalar restriction and derived
induction along the character produce the cup and cap. The two shifts
are applied separately on the cup.
-/

noncomputable section

namespace Categorification.Stendhal.Coevaluation

open CategoryTheory DG

universe u v
variable {A K : Type u} [Ring A] [Ring K] [DGAddCommGroup A] [DGAddCommGroup K]
  [InternalGrading A] [InternalGrading K] [BigradedDGRing A] [BigradedDGRing K]
  [DGRing A] [DGRing K]
  (χ : A →ᵈᵍ+* K) (hχ : ∀ {j : ℤ} {a : A}, a ∈ wgrading j → χ a ∈ wgrading j)

local notation "W" => WeightCategory
local notation "F" => WeightCategory.mapFunctor χ hχ

variable [CatModule.HasDerivedCategory.{v,u} (W A)]
  [CatModule.HasDerivedCategory.{v,u} (W K)]

/-- The cup for a scalar character, before the normalization shifts.
The right action uses the character on the opposite diagram algebra. -/
def characterCup : CatModule.DerivedCategory.{v,u} (W K) ⥤ CatModule.DerivedCategory.{v,u} (W A) :=
  CatModule.DerivedCategory.restrict F

/-- The cap for the same scalar character is its derived extension of scalars. -/
def characterCap : CatModule.DerivedCategory.{v,u} (W A) ⥤ CatModule.DerivedCategory.{v,u} (W K) :=
  CatModule.DerivedCategory.induction F

/-- The character cup of Webster, arXiv:1309.3796v2, Definition 7.4
with explicit internal and cohomological normalization parameters. -/
def shiftedCharacterCup (internal cohomological : ℤ) :
    CatModule.DerivedCategory.{v,u} (W K) ⥤ CatModule.DerivedCategory.{v,u} (W A) :=
  characterCup χ hχ ⋙ CatModule.DerivedCategory.internalShift A internal ⋙
    shiftFunctor (CatModule.DerivedCategory.{v,u} (W A)) cohomological

/-- Before shifts the character cup is right adjoint to the cap using the same character. -/
def characterCapCupAdjunction : characterCap χ hχ ⊣ characterCup χ hχ :=
  CatModule.DerivedCategory.inductionAdjunction F

/-- On a scalar dg module the graded cup acts by restriction along the character. -/
def characterCupObjIso (X : CatModule.{u} (W K)) :
    (characterCup χ hχ).obj (CatModule.DerivedCategory.Q.obj X) ≅
      CatModule.DerivedCategory.Q.obj ((CatModule.precomp F).obj X) :=
  (CatModule.DerivedCategory.QCompRestrictIso F).app X

end Categorification.Stendhal.Coevaluation
