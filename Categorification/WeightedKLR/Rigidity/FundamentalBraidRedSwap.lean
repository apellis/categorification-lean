/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTargetWeightEquiv

/-!
# Simultaneous red transposition at the fundamental braid

The calculation of the double positive braid in Webster, arXiv:1309.3796v2,
§7.2 before Definition 7.12 uses the same transposition on the two
diagonal corners and on the rectangular crossing coefficient.
-/
noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra CategoryTheory DG CatModule Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded
  fundamentalBraidSourceOrderedInternal fundamentalBraidSourceOrderedBigraded
  fundamentalTargetScalarInternal fundamentalTargetScalarBigraded
local notation "ν" => ({()} : Multiset Unit)
local notation "σ" => Equiv.swap (0 : Fin 2) 1
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
local notation "V" => ViolQuotient ℚ Q wt ν
local notation "G" => violAuxiliaryGrade («ν» := ν) grading
local notation "R" => SeqRelabel.ofRedPerm (k := ℚ) (Q := Q) (Λ := wt) (Λ' := wt) («ν» := ν) σ (fun _ => rfl)
local notation "π" => violMk ℚ Q wt ν
local notation "p" κ:arg => π (redProj ℚ Q wt ν κ)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "h" κ:arg => isIdempotentElem_violMk_redProj ℚ Q wt ν κ

/-- The transposition of the two equal red labels on all diagrams. -/
def fundamentalBraidRedSwap : V ≃ₐ[ℚ] V :=
  violRedPermEquiv (k := ℚ) (Q := Q) (Λ' := wt) (Λ := wt) («ν» := ν) σ (fun _ => rfl)

local notation "S" => fundamentalBraidRedSwap

theorem fundamentalBraidRedSwap_weight {j : ℤ} (x : V) : S x ∈ G j ↔ x ∈ G j :=
  violRedPermEquiv_mem_grade_iff (Λ := wt) fundamentalBraidParameters σ x

private theorem swapAffine_twice (a : KLRAlgebra ℚ (stendhalQ Q wt) (stendhalWeight 2 ν)) :
    relabelHom R (relabelHom R a) = a := by
  induction a using klr_induction with
  | hr r => simp only [AlgHom.commutes]
  | hadd a b h₁ h₂ => simp only [map_add, h₁, h₂]
  | hmul a b h₁ h₂ => simp only [map_mul, h₁, h₂]
  | he t =>
    simp only [relabelHom_e]
    apply congrArg KLRAlgebra.e
    change Seq.redPerm σ (Seq.redPerm σ t) = t
    rw [Seq.redPerm_redPerm, Equiv.swap_mul_self, Seq.redPerm_one]
  | hx j => simp only [relabelHom_x, Fin.cast_eq_self]
  | hψ j => simp only [relabelHom_ψ]

theorem fundamentalBraidRedSwap_twice (x : V) : S (S x) = x := by
  obtain ⟨y,rfl⟩ := violMk_surjective x
  obtain ⟨z,rfl⟩ := ofKLR_surjective y
  change violRedPermEquiv σ _ (violRedPermEquiv σ _ (π _)) = _
  rw [violRedPermEquiv_violMk, violRedPermEquiv_violMk, redPermAlgEquiv,
    relabelAlgEquiv_ofKLR, relabelAlgEquiv_ofKLR, swapAffine_twice]

theorem fundamentalBraidRedSwap_source : S (p κ₀) = p κ₁ := by
  change violRedPermEquiv σ _ (π _) = _
  rw [violRedPermEquiv_violMk,redPermAlgEquiv_redProj]
  rfl

theorem fundamentalBraidRedSwap_target : S (p κ₁) = p κ₀ := by
  rw [← fundamentalBraidRedSwap_source, fundamentalBraidRedSwap_twice]

/-- The induced transposition from the source to the target corner. -/
def fundamentalBraidSourceSwap : K ≃+* U :=
  (h κ₀).cornerRingEquiv (h κ₁) (S).toRingEquiv fundamentalBraidRedSwap_source

/-- The same red transposition on the opposite diagonal corner. -/
def fundamentalBraidTargetSwap : U ≃+* K :=
  (h κ₁).cornerRingEquiv (h κ₀) (S).toRingEquiv fundamentalBraidRedSwap_target

theorem fundamentalBraidTargetSwap_eq_symm (x : U) :
    fundamentalBraidTargetSwap x = fundamentalBraidSourceSwap.symm x := by
  apply fundamentalBraidSourceSwap.injective
  rw [RingEquiv.apply_symm_apply]
  exact Subtype.ext (fundamentalBraidRedSwap_twice x.val)

theorem fundamentalBraidTargetEquiv_sourceSwap (x : K) :
    fundamentalBraidTargetEquiv (fundamentalBraidSourceSwap x) = fundamentalBraidSourceEquiv x := by
  change fundamentalBraidSourceEquiv (fundamentalBraidSourceSwap.symm (fundamentalBraidSourceSwap x)) = _
  rw [RingEquiv.symm_apply_apply]

theorem fundamentalBraidSourceEquiv_targetSwap (x : U) :
    fundamentalBraidSourceEquiv (fundamentalBraidTargetSwap x) = fundamentalBraidTargetEquiv x := by
  rw [fundamentalBraidTargetSwap_eq_symm]
  rfl

end Categorification.Stendhal.FundamentalCorner
