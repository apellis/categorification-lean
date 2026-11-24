/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoUnknotHomology
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# The projective resolution of the label-two middle quotient

Webster, arXiv:1309.3796v2, §8.2, printed page 81, proof of Proposition 8.4.
The period-two exact sequences and the augmentation form a projective
resolution by copies of the regular middle module.
-/

namespace Categorification.Webster.LabelTwo

open CategoryTheory

noncomputable section

universe u
variable {k : Type u} [CommRing k]

attribute [local instance] quotientAlgebra quotientModule

local notation "A" => Middle k
local notation "B" => DualNumber k
local notation "V" => ModuleCat.of A A
local notation "W" => ModuleCat.of A B
local notation "shape" => ComplexShape.down ℕ

private def regularDifferential (n : ℕ) : V ⟶ V :=
  if Even n then ModuleCat.ofHom (plus (k := k)) else ModuleCat.ofHom minus

private theorem plus_apply_minus_eq_zero (x : A) : plus (minus x)=0 := by
  change minus x ∈ (plus (k := k)).ker
  rw [ker_plus]
  exact ⟨x,rfl⟩

private theorem minus_apply_plus_eq_zero (x : A) : minus (plus x)=0 := by
  change plus x ∈ (minus (k := k)).ker
  rw [ker_minus]
  exact ⟨x,rfl⟩

private theorem regularDifferential_square (n : ℕ) :
    regularDifferential (k := k) (n+1) ≫ regularDifferential n = 0 := by
  by_cases hn : Even n
  · have hn' : ¬ Even (n+1) := by simp [Nat.even_add_one,hn]
    rw [regularDifferential,regularDifferential,ite_eq_right hn',ite_eq_left hn]
    exact ModuleCat.hom_ext (LinearMap.ext plus_apply_minus_eq_zero)
  · have hn' : Even (n+1) := by simp [Nat.even_add_one,hn]
    rw [regularDifferential,regularDifferential,ite_eq_left hn',ite_eq_right hn]
    exact ModuleCat.hom_ext (LinearMap.ext minus_apply_plus_eq_zero)

abbrev periodicComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun _ => V) regularDifferential regularDifferential_square

local notation "R" => periodicComplex (k := k)
local notation "aug" => ModuleCat.ofHom (augmentation (k := k))

private theorem regularAtZero :
    (R).d 1 0 = ModuleCat.ofHom (plus (k := k)) := by
  change ChainComplex.of.d (fun _ => V) regularDifferential (0+1) 0 = _
  exact (ChainComplex.of_d (fun _ : ℕ => V) regularDifferential 0).trans (by simp [regularDifferential])

private theorem regularExactAtSucc (n : ℕ) : (R).ExactAt (n+1) := by
  apply (HomologicalComplex.exactAt_iff' (R) (n+2) (n+1) n ((shape).prev_eq' rfl) ((shape).next_eq' rfl)).mpr
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change (ChainComplex.of.d (fun _ => V) regularDifferential ((n+1)+1) (n+1)).hom.range =
    (ChainComplex.of.d (fun _ => V) regularDifferential (n+1) n).hom.ker
  rw [ChainComplex.of_d,ChainComplex.of_d]
  by_cases hn : Even n
  · have hn' : ¬ Even (n+1) := by simp [Nat.even_add_one,hn]
    rw [regularDifferential,regularDifferential,ite_eq_right hn',ite_eq_left hn]
    exact (ker_plus (k := k)).symm
  · have hn' : Even (n+1) := by simp [Nat.even_add_one,hn]
    rw [regularDifferential,regularDifferential,ite_eq_left hn',ite_eq_right hn]
    exact (ker_minus (k := k)).symm

private theorem aug_square : (R).d 1 0 ≫ aug = 0 := by
  rw [regularAtZero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change plus x ∈ (augmentation (k := k)).ker
  rw [ker_augmentation]
  exact ⟨x,rfl⟩

private def regularResolutionPi : (R) ⟶ (ChainComplex.single₀ (ModuleCat A)).obj W :=
  ((R).toSingle₀Equiv W).symm ⟨aug,aug_square⟩

private theorem regularResolutionPi_zero : (regularResolutionPi (k := k)).f 0 = aug := by
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private theorem regularResolutionPi_quasiIso :
    QuasiIso (regularResolutionPi (k := k)) := by
  constructor
  intro n
  cases n with
  | succ n =>
      apply (quasiIsoAt_iff_exactAt' _
        (n+1) (ChainComplex.exactAt_succ_single_obj _ _)).mpr
      exact regularExactAtSucc n
  | zero =>
      let f := ((HomologicalComplex.shortComplexFunctor' (ModuleCat A) (shape) 1 0 0).map
        (regularResolutionPi (k := k)))
      apply (ChainComplex.quasiIsoAt₀_iff _).mpr
      change ShortComplex.QuasiIso f
      have hg : ((R).sc' 1 0 0).g = 0 := by
        change (R).d 0 0 = 0
        exact (R).shape 0 0 (by decide)
      have hf' : (((ChainComplex.single₀ (ModuleCat A)).obj W).sc' 1 0 0).f = 0 :=
        rfl
      have hg' : (((ChainComplex.single₀ (ModuleCat A)).obj W).sc' 1 0 0).g = 0 :=
        rfl
      refine (ShortComplex.quasiIso_iff_of_zeros' f hg hf' hg').mpr ⟨?_,?_⟩
      · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
        change ((R).d 1 0).hom.range = ((regularResolutionPi (k := k)).f 0).hom.ker
        rw [regularAtZero,regularResolutionPi_zero]
        exact (ker_augmentation (k := k)).symm
      · change Epi ((regularResolutionPi (k := k)).f 0)
        rw [regularResolutionPi_zero]
        change Epi (ModuleCat.ofHom (augmentation (k := k)))
        exact (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective (k := k))

/-- The periodic augmented regular complex as a Mathlib projective resolution. -/
def periodicProjectiveResolution : ProjectiveResolution W where
  complex := (R)
  projective _ := inferInstance
  π := regularResolutionPi
  quasiIso := regularResolutionPi_quasiIso

end

end Categorification.Webster.LabelTwo
