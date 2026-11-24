/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidAction
import Categorification.WeightedKLR.RedStrands.BraidedStandardGrading

/-!
# The fractional weight of the fundamental middle braid class

In Webster, arXiv:1309.3796v2, Proposition 7.11, the surviving diagram
has one red/red and one mixed crossing. Definitions 4.4 and 6.2
give degree one half for the diagram. The terminal projective in the
middle resolution has generator in degree one, giving total degree
three halves.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA MvPolynomial BraidedStendhalAlgebra QuantumGroup
local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "R" => KLRAlgebra ℚ (stendhalQ Q wt) μ

/-- The two fundamental labels with the simply laced type A₁ parameters. -/
theorem fundamentalBraidParameters : IsRouquierQ C Q where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

private theorem surviving_mem : braidProject (ψw [0,1] * e crossedMiddle) ∈
    violCorner ℚ Q wt ν terminal [1,0] := by
  have ht : wordProd (Multiset.card μ) [0,1] • crossedMiddle = terminal := by decide +kernel
  have he : (ψw [0,1] * e crossedMiddle : R) = e terminal * ψw [0,1] := by rw [ψw_mul_e,ht]
  apply mem_violCorner_iff.mpr
  constructor
  · change braidProject (e terminal) * braidProject _ = _
    rw [← map_mul,he,← mul_assoc,e_mul_self]
  · change violMk ℚ Q wt ν (ofKLR ℚ Q wt ν _) * violMk ℚ Q wt ν _ = _
    rw [← map_mul]
    apply congrArg (violMk ℚ Q wt ν)
    rw [map_mul,mul_assoc,e_mul_redProj,ite_eq_left (by decide +kernel)]
    exact (map_mul _ _ _).symm

/-- The nonzero fundamental braid class at the reversed middle loading
in the terminal projective term of Webster v2, Proposition 7.11. -/
def fundamentalBraidMiddleClass : violCorner ℚ Q wt ν terminal [1,0] :=
  ⟨braidProject (ψw [0,1] * e crossedMiddle),surviving_mem⟩

theorem fundamentalBraidMiddleClass_ne_zero : fundamentalBraidMiddleClass ≠ 0 := by
  intro h
  have hh := congrArg Subtype.val h
  exact fundamentalBraid_mixed_ne_zero.2 (by simpa [fundamentalBraidMiddleClass,ψw] using hh)

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]
  (P : Matrix.Realization (UDot.A C) ℂ H)

/-- The fundamental weight of the A₁ realization. -/
def braidFundamentalWeight : Module.Dual ℂ H := (1 / 2 : ℂ) • P.root ()

private theorem unit_degree : UDot.di C () = 1 := rfl

omit [Module.Finite ℂ H] in
theorem braidFundamentalWeight_coroot : braidFundamentalWeight P (P.coroot ()) = 1 := by
  change (1 / 2 : ℂ) * P.root () (P.coroot ()) = 1
  rw [P.root_coroot]
  change 1 / 2 * (2 : ℂ) = 1
  norm_num

/-- The red/red degree correction in Webster's Definition 6.2 uses
the norm one half of the fundamental weight. -/
theorem braidFundamentalWeight_norm :
    weightPairing C P (braidFundamentalWeight P) (braidFundamentalWeight P) = 1 / 2 := by
  calc
    _ = (1 / 2 : ℂ) * weightPairing C P (P.root ()) (braidFundamentalWeight P) := by
      exact LinearMap.BilinForm.smul_left _ _ _
    _ = _ := by rw [weightPairing_root,unit_degree,braidFundamentalWeight_coroot]; norm_num

/-- Definition 6.2 places the surviving fundamental diagram of Proposition 7.11
in degree one half of the crossed cut. -/
theorem fundamentalBraidMiddleClass_grade :
    fundamentalBraidMiddleClass ∈ figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
      (weightPairing C P) (fun _ => braidFundamentalWeight P) terminal 1 0 (1 / 2) := by
  let G := stendhalGradingDatum wt fundamentalBraidParameters.gradingDatum (UDot.di C)
    (fun i => (fundamentalBraidParameters.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm)
  have hd : G.degW [0,1] crossedMiddle = -1 := by
    change (-2 : ℤ) + (UDot.di C () * (wt 0 () : ℤ) + 0) = -1
    simp [unit_degree,wt]
  have hp := GradingDatum.ψw_mul_pol_mul_e_mem_grade G [0,1] crossedMiddle
    (p := 1) (D := 0) (isWeightedHomogeneous_one ℚ _)
  rw [map_one,mul_one,add_zero,hd] at hp
  have haux : fundamentalBraidMiddleClass ∈ violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters terminal [1,0] (-1) :=
    Graded.mem_map_of_mem _ (violMk ℚ Q wt ν).toLinearMap
      (Graded.mem_map_of_mem _ (ofKLR ℚ Q wt ν).toLinearMap hp)
  let f := fun n : ℤ => (n : ℂ) + (2 - weightPairing C P (braidFundamentalWeight P) (braidFundamentalWeight P))
  have hf : Function.Injective f := fun a b h => Int.cast_injective (add_right_cancel h)
  have he : f (-1) = (1 / 2 : ℂ) := by simp only [f,braidFundamentalWeight_norm]; norm_num
  rw [← he,figureFiveCutGrade,hf.extend_apply]
  exact haux

/-- The terminal projective in the resolution is generated at internal weight
one. Translating its crossed cut by that degree puts the surviving class
of Webster v2, Proposition 7.11, in total weight three halves, uniquely. -/
theorem fundamentalBraidMiddleClass_resolutionWeight (z : ℂ) :
    fundamentalBraidMiddleClass ∈ Graded.shift (figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
      (weightPairing C P) (fun _ => braidFundamentalWeight P) terminal 1 0) 1 z ↔ z = 3 / 2 := by
  let F := figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters (weightPairing C P)
    (fun _ => braidFundamentalWeight P) terminal 1 0
  have hF : DirectSum.IsInternal F := isInternal_figureFiveCutGrade _ _ _ _ _ _ _
  change fundamentalBraidMiddleClass ∈ F (z - 1) ↔ _
  constructor
  · intro hz
    have he : z - 1 = 1 / 2 := by
      by_contra h
      exact fundamentalBraidMiddleClass_ne_zero
        ((Submodule.disjoint_def.mp (hF.submodule_iSupIndep.pairwiseDisjoint h))
          _ hz (fundamentalBraidMiddleClass_grade P))
    linear_combination he
  · rintro rfl
    convert fundamentalBraidMiddleClass_grade P using 2
    norm_num

end Categorification.Stendhal.FundamentalCorner
