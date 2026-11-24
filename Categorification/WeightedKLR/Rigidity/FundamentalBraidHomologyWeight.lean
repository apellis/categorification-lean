/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidComplex
import Categorification.WeightedKLR.Rigidity.FundamentalBraidWeight

/-!
# Physical degree of the fundamental braid homology

For the fundamental type A₁ case of Webster, arXiv:1309.3796v2,
Proposition 7.11, a nonzero homology class has a homogeneous representative
in the shifted terminal loading cut precisely in physical degree three halves.
-/
noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra QuantumGroup
local notation "ν" => ({()} : Multiset Unit)
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "Cut" s:arg => violCorner ℚ Q wt ν s [1,0]
local notation "S" => fundamentalBraidCutComplex
local notation "B" => fundamentalBraidCycle
local notation "E" => braidProject (e crossedMiddle)

private theorem cycle_eq_middleClass : fundamentalBraidCycle = fundamentalBraidMiddleClass := by
  apply Subtype.ext
  simp [fundamentalBraidCycle_val,fundamentalBraidMiddleClass,ψw]

private theorem project_cycle (z : Cut terminal) (hz : (S).g z = 0) :
    ∃ a : ℚ, z.val * E = a • (B).val := by
  obtain ⟨a,y,hy⟩ := fundamentalBraidCycle_mod_boundaries z hz
  have hb := (fundamentalBraidCycle_boundary_iff ((S).f y) ((S).moduleCat_zero_apply y)).mp ⟨y,rfl⟩
  rw [hy] at hb
  change (a • (B).val - z.val) * E = 0 at hb
  rw [sub_mul,smul_mul_assoc,fundamentalBraidCycle_supported] at hb
  exact ⟨a,(sub_eq_zero.mp hb).symm⟩

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]
  (P : Matrix.Realization (UDot.A C) ℂ H)

local notation "G" => figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
  (weightPairing C P) (fun _ => braidFundamentalWeight P) terminal 1 0

private theorem projected_mem {w : ℂ} {z y : Cut terminal} (hz : z ∈ G w)
    (hy : y.val = z.val * E) : y ∈ G w := by
  let d := fun n : ℤ => (n : ℂ) + (2 - weightPairing C P (braidFundamentalWeight P) (braidFundamentalWeight P))
  let A := violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters terminal [1,0]
  change z ∈ Function.extend d A ⊥ w at hz
  change y ∈ Function.extend d A ⊥ w
  by_cases hw : ∃ n, d n = w
  · obtain ⟨n,rfl⟩ := hw
    have hd : Function.Injective d := fun _ _ h => Int.cast_injective (add_right_cancel h)
    rw [hd.extend_apply] at hz ⊢
    let D := stendhalGradingDatum wt fundamentalBraidParameters.gradingDatum (UDot.di C)
      (fun i => (fundamentalBraidParameters.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm)
    let V := violAuxiliaryGrade («ν» := ν) D
    have he : E ∈ V 0 := Graded.mem_map_of_mem _ (violMk ℚ Q wt ν).toLinearMap
      (Graded.mem_map_of_mem _ (ofKLR ℚ Q wt ν).toLinearMap (D.e_mem_grade crossedMiddle))
    change y.val ∈ V n
    rw [hy,← add_zero n]
    exact SetLike.GradedMul.mul_mem (show z.val ∈ V n from hz) he
  · rw [Function.extend_apply' _ _ _ hw] at hz ⊢
    have hzero : z = 0 := (Submodule.mem_bot ℚ).mp hz
    exact (Submodule.mem_bot ℚ).mpr (Subtype.ext (by rw [hy,hzero]; exact zero_mul _))

/-- The homogeneous representatives of nonzero degree-one homology occur
exactly in total physical weight three halves. The terminal projective term
in the source resolution contributes one to the degree of the diagram. -/
theorem fundamentalBraidHomology_weight_iff (w : ℂ) :
    (∃ z : Cut terminal, z ∈ Graded.shift G 1 w ∧ (S).g z = 0 ∧
      ¬ ∃ y : Cut middle, (S).f y = z) ↔ w = 3 / 2 := by
  constructor
  · rintro ⟨z,hw,hz,nb⟩
    obtain ⟨a,ha⟩ := project_cycle z hz
    have hp : z.val * E ≠ 0 := fun h => nb ((fundamentalBraidCycle_boundary_iff z hz).mpr h)
    have hn : a ≠ 0 := by
      rintro rfl
      exact hp (ha.trans (zero_smul _ _))
    have hm : a • fundamentalBraidMiddleClass ∈ G (w - 1) :=
      projected_mem P hw (by rw [← cycle_eq_middleClass]; exact ha.symm)
    have hh := (G (w - 1)).smul_mem a⁻¹ hm
    rw [smul_smul,inv_mul_cancel₀ hn,one_smul] at hh
    exact (fundamentalBraidMiddleClass_resolutionWeight P w).mp hh
  · rintro rfl
    refine ⟨B,?_,fundamentalBraidCycle_closed,?_⟩
    · rw [cycle_eq_middleClass]
      exact (fundamentalBraidMiddleClass_resolutionWeight P _).mpr rfl
    · intro h
      have hz := (fundamentalBraidCycle_boundary_iff _ fundamentalBraidCycle_closed).mp h
      rw [fundamentalBraidCycle_supported] at hz
      exact fundamentalBraidCycle_ne_zero hz

end Categorification.Stendhal.FundamentalCorner
