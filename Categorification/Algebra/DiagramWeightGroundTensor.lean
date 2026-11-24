/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightOrdinaryTensor
import Categorification.Algebra.BalancedTensorScalarGrading

/-!
# Ground-ring degree components of diagram weight coends

The endpoint weight coend is the total-degree component of the
ground-ring balanced tensor.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite Categorification.Graded
open scoped DG.DegreeZero

universe u

variable {k A B C M N : Type u} [CommRing k] [Ring A] [Ring B] [Ring C] [Algebra k B]
  [InternalGrading A] [InternalGrading B] [InternalGrading C]
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup M] [Module k M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [SMulCommClass k Bᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module B N] [Module Cᵐᵒᵖ N]
  [SMulCommClass B Cᵐᵒᵖ N] [IsScalarTower k B N]
  (G : ℤ → Submodule k M) (H : ℤ → Submodule k N)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m)
  (X : WeightCategory A) (Z : WeightCategory C)

local notation "G₀" => (fun i => Submodule.toAddSubgroup (G i))
local notation "H₀" => (fun i => Submodule.toAddSubgroup (H i))

local notation "D₁" => diagramWeightBimodule G₀ hgL hgR
local notation "D₂" => diagramWeightBimodule H₀ hhL hhR
local notation "Out" => CatTensorProduct (CatBimodule.right D₁ X) (CatBimodule.left D₂ Z)

private abbrev diagramWeightRange := (diagramWeightTensorToOrdinary G₀ H₀ hgL hgR hhL hhR X Z).range

/-- The endpoint weight coend is the corresponding total-degree component of
the ground-ring balanced tensor. -/
def diagramWeightTensorGroundGradeEquiv
    [dG : DirectSum.Decomposition G₀] [dH : DirectSum.Decomposition H₀] :
    Out ≃+ balancedGrading k B G H (X.as - Z.as) := by
  let e := balancedTensorIntScalarAddEquiv (N := N) hM
  have h := diagramWeightTensorOrdinary_range_eq_grade (B := B) G₀ H₀ hgL hgR hhL hhR X Z
  change diagramWeightRange G H hgL hgR hhL hhR X Z =
    (balancedGrading ℤ B (fun i => (G i).restrictScalars ℤ)
      (fun i => (H i).restrictScalars ℤ) (X.as - Z.as)).toAddSubgroup at h
  let h₁ := congrArg (AddSubgroup.map e.toAddMonoidHom) h
  let h₂ := balancedTensorIntScalarAddEquiv_map_grade hM G H (X.as - Z.as)
  exact (diagramWeightTensorOrdinaryEquivRange (B := B) G₀ H₀ hgL hgR hhL hhR X Z).trans
    ((e.addSubgroupMap _).trans (AddEquiv.addSubgroupCongr (h₁.trans h₂)))

end Categorification
