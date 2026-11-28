/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForgetDerivedCompact
import DG.Category.Derived.Compact
import DG.Derived.Perfect
import DG.Homotopy.BimoduleTensor

/-!
# Forgetting the weights of a representable module

For `C_A = DG.WeightCategory A`, the weight sum of the representable module `C_A(⟨k⟩, -)` is the
dg `A`-module `A`: the summand of weight `j` is `A⟨j - k⟩`, and summing the components identifies
`⨁ j, A⟨j - k⟩` with `A` (`DG.CatModule.weightSumRepresentableEquiv`). So forgetting the weights
sends the representable modules to compact objects of `D(A)`
(`DG.CatModule.isCompact_weightForgetDerived_representable`).

This is used for the graded braiding functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Definition 6.6 and Theorem 6.15.
-/

open CategoryTheory DirectSum

universe w₁ w₂ u

noncomputable section

namespace DG

namespace CatModule

open WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] (k : ℤ)

/-- The representable module `C_A(⟨k⟩, -)`. -/
abbrev weightRepresentable : CatModule.{u} (WeightCategory A) :=
  representableW.{u} (WeightCategory A) (⟨k⟩ : WeightCategory A)

/-- The additive equivalence `⨁ j, A⟨j - k⟩ ≃ A`, summing the components. -/
def weightSumRepresentableAddEquiv : (weightRepresentable (A := A) k).WeightSum ≃+ A :=
  (DFinsupp.mapRange.addEquiv fun j => (AddEquiv.ulift :
      ULift.{u} ((⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩) ≃+ _)).trans
    (((DirectSum.equivCongrLeft (β := fun l => wgrading (M := A) l)
      (Equiv.addRight k)).symm :
        (⨁ j : ℤ, ((⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩)) ≃+ ⨁ l : ℤ, wgrading (M := A) l).trans
      (decomposeAddEquiv (wgrading (M := A))).symm)

theorem weightSumRepresentableAddEquiv_of (j : ℤ) (y : (⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩) :
    weightSumRepresentableAddEquiv k
      (weightSumOf (weightRepresentable (A := A) k) j (ULift.up y)) = y.1 := by
  classical
  have h₁ : (DFinsupp.mapRange.addEquiv fun j => (AddEquiv.ulift :
      ULift.{u} ((⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩) ≃+ _))
        (weightSumOf (weightRepresentable (A := A) k) j (ULift.up y)) =
      DirectSum.of (fun j : ℤ => ((⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩)) j y :=
    DFinsupp.mapRange_single (hf := fun _ => rfl)
  have h₂ : (DirectSum.equivCongrLeft (β := fun l => wgrading (M := A) l)
      (Equiv.addRight k)).symm (DirectSum.of (fun j : ℤ => ((⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩)) j y) =
      DirectSum.of (fun l => wgrading (M := A) l) (j - k) y :=
    (AddEquiv.symm_apply_eq _).mpr
      (DirectSum.equivCongrLeft_of (β := fun l => wgrading (M := A) l) (Equiv.addRight k) j y).symm
  exact (congrArg (fun z => (decomposeAddEquiv (wgrading (M := A))).symm
    ((DirectSum.equivCongrLeft (β := fun l => wgrading (M := A) l) (Equiv.addRight k)).symm z))
      h₁).trans ((congrArg (decomposeAddEquiv (wgrading (M := A))).symm h₂).trans
        (decompose_symm_of (ℳ := wgrading (M := A)) (i := j - k) y))

/-- The underlying morphism of an element of the representable module. -/
abbrev weightRepresentableDown {j : ℤ} (u : (weightRepresentable (A := A) k).obj ⟨j⟩) :
    (⟨k⟩ : WeightCategory A) ⟶ ⟨j⟩ :=
  ULift.down u

theorem weightSumRepresentableAddEquiv_of' (j : ℤ) (u : (weightRepresentable (A := A) k).obj ⟨j⟩) :
    weightSumRepresentableAddEquiv k (weightSumOf (weightRepresentable (A := A) k) j u) =
      (weightRepresentableDown k u).1 :=
  weightSumRepresentableAddEquiv_of k j (weightRepresentableDown k u)

theorem weightSumRepresentableAddEquiv_smul (a : A)
    (z : (weightRepresentable (A := A) k).WeightSum) :
    weightSumRepresentableAddEquiv k (a • z) = a * weightSumRepresentableAddEquiv k z := by
  classical
  have key : ∀ (l : ℤ) (a : A), a ∈ wgrading (M := A) l → ∀ z : (weightRepresentable k).WeightSum,
      weightSumRepresentableAddEquiv k (a • z) = a * weightSumRepresentableAddEquiv k z := by
    intro l a ha z
    induction z using DirectSum.induction_on with
    | zero => rw [weightSum_smul_zero, map_zero, mul_zero]
    | of j y =>
      rw [weightSum_smul_of _ ha j y, weightSumRepresentableAddEquiv_of',
        weightSumRepresentableAddEquiv_of']
      rfl
    | add z z' hz hz' => rw [weightSum_smul_add, map_add, map_add, hz, hz', mul_add]
  induction a using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
  | zero => rw [weightSum_zero_smul, map_zero, zero_mul]
  | homogeneous a => exact key _ a a.2 z
  | add a b ha hb => rw [weightSum_add_smul, map_add, ha, hb, add_mul]

theorem weightSumRepresentableAddEquiv_d (z : (weightRepresentable (A := A) k).WeightSum) :
    weightSumRepresentableAddEquiv k (d z) = d (weightSumRepresentableAddEquiv k z) := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of j y =>
    rw [weightSum_d_of, weightSumRepresentableAddEquiv_of', weightSumRepresentableAddEquiv_of']
    rfl
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', map_add]

theorem weightSumRepresentableAddEquiv_mem {n : ℤ} {z : (weightRepresentable (A := A) k).WeightSum}
    (hz : z ∈ grading n) : weightSumRepresentableAddEquiv k z ∈ grading n := by
  classical
  rw [← DirectSum.sum_support_of z, map_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [weightSumRepresentableAddEquiv_of']
  exact hz j

/-- **The weight sum of a representable module is the free module**:
`⨁ j, A⟨j - k⟩ ≃ A` as dg `A`-modules. -/
def weightSumRepresentableEquiv : (weightRepresentable (A := A) k).WeightSum ≃ᵈᵍ[A] A where
  toFun := weightSumRepresentableAddEquiv k
  invFun := (weightSumRepresentableAddEquiv k).symm
  left_inv := (weightSumRepresentableAddEquiv k).left_inv
  right_inv := (weightSumRepresentableAddEquiv k).right_inv
  map_add' := map_add _
  map_smul' := weightSumRepresentableAddEquiv_smul k
  map_mem' := weightSumRepresentableAddEquiv_mem k
  map_d' := weightSumRepresentableAddEquiv_d k

/-- The weight sum of a representable module, as an isomorphism of dg `A`-modules. -/
def weightForgetRepresentableIso :
    (weightForget A).obj (weightRepresentable (A := A) k) ≅ DGModuleCat.of A A :=
  DGModuleCat.isoOfDGModuleEquiv (weightSumRepresentableEquiv k)

variable [CatModule.HasDerivedCategory.{w₁, u} (WeightCategory A)] [DG.HasDerivedCategory.{w₂, u} A]

/-- Forgetting the weights sends a representable module to a compact object of `D(A)`. -/
theorem isCompact_weightForgetDerived_representable :
    IsCompact.{u} ((weightForgetDerived.{w₁, w₂} A).obj
      (CatModule.DerivedCategory.Q.obj (weightRepresentable (A := A) k))) :=
  DG.DerivedCategory.isCompact_Q_self.of_iso (weightForgetDerivedQObjIso _ ≪≫
    DG.DerivedCategory.Q.mapIso (weightForgetRepresentableIso k))

end CatModule

end DG
