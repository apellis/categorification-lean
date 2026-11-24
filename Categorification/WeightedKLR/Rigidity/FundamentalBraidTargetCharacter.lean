/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidProjectives
import Categorification.WeightedKLR.RedStrands.BraidedRelabel

/-!
# The middle character on the reversed braid corner

For the fundamental type A₁ case of Webster, arXiv:1309.3796v2,
Proposition 7.11, the opposite order has the same pair of weights.
Relabelling the red strands identifies its middle loading with the middle
simple's projector. The diagonal component at that loading reads off the
middle character.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "ν" => ({()} : Multiset Unit)
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν)
local notation "T" => TensorProductAlgebra ℚ Q wt ν

private abbrev swapRed : Equiv.Perm (Fin 2) := Equiv.swap 0 1
private def swapCorner : K (List.finRange 2) ≃+* K [1,0] :=
  violCornerRedPermEquiv (k := ℚ) (Q := Q) (Λ' := wt) (Λ := wt) («ν» := ν) swapRed (fun _ => rfl) (List.finRange 2)

private theorem middleOrder : redWord middle = List.finRange 2 := by decide +kernel
private theorem crossedOrder : redWord crossedMiddle = [1,0] := by decide +kernel

/-- The reversed-order middle projector of the fundamental braid calculation. -/
abbrev braidTargetMiddleIdem : K [1,0] := violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) crossedOrder

private theorem swap_loading :
    swapCorner (violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) middleOrder) = braidTargetMiddleIdem := by
  apply Subtype.ext
  change violRedPermEquiv (k := ℚ) (Q := Q) (Λ := wt) (Λ' := wt) («ν» := ν) swapRed (fun _ => rfl)
    (violMk ℚ Q wt ν (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (e middle))) = _
  rw [violRedPermEquiv_violMk,redPermAlgEquiv_e]
  have h : Seq.redPerm swapRed middle = crossedMiddle := by decide +kernel
  rw [h]
  rfl

/-- Relabelling followed by the diagonal-corner equivalence, for the
target ring of the fundamental braid in Webster v2, Proposition 7.11. -/
def fundamentalBraidTargetEquiv : K [1,0] ≃+* T := swapCorner.symm.trans fundamentalBraidSourceEquiv

theorem fundamentalBraidTargetEquiv_middle : fundamentalBraidTargetEquiv braidTargetMiddleIdem = middleIdem := by
  rw [← swap_loading]
  change fundamentalBraidSourceEquiv (swapCorner.symm (swapCorner _)) = _
  rw [swapCorner.symm_apply_apply]
  refine Eq.trans ?_ (fundamentalBraidSourceEquiv_diagram (e middle))
  apply congrArg fundamentalBraidSourceEquiv
  apply Subtype.ext
  exact (congrArg (violMk ℚ Q wt ν) (cornerMk_e_val middleOrder)).symm

/-- The right target character of the fundamental middle loading is the
middle head character under relabelling (Webster v2, Proposition 7.11). -/
def fundamentalBraidTargetCharacter : K [1,0] →+* ℚ :=
  middleCharacter.toRingHom.comp fundamentalBraidTargetEquiv.toRingHom

@[simp] theorem fundamentalBraidTargetCharacter_middle : fundamentalBraidTargetCharacter braidTargetMiddleIdem = 1 := by
  change middleCharacter (fundamentalBraidTargetEquiv braidTargetMiddleIdem) = 1
  rw [fundamentalBraidTargetEquiv_middle,middleCharacter_middleIdem]

private def toAmbient : T →+ ViolQuotient ℚ Q wt ν where
  toFun x := (fundamentalBraidTargetEquiv.symm x).val
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

private theorem toAmbient_mul (a b : T) : toAmbient (a * b) = toAmbient a * toAmbient b := by
  change (fundamentalBraidTargetEquiv.symm (a * b)).val = _
  rw [map_mul]; rfl

private theorem toAmbient_middle : toAmbient middleIdem = braidProject (e crossedMiddle) := by
  change (fundamentalBraidTargetEquiv.symm middleIdem).val = _
  rw [(fundamentalBraidTargetEquiv.symm_apply_eq).mpr fundamentalBraidTargetEquiv_middle.symm]; rfl

/-- The scalar of the target middle corner is obtained by the middle
character for every diagram in the fundamental braid target order. -/
theorem fundamentalBraidTargetCorner_scalar (z : K [1,0]) :
    braidProject (e crossedMiddle) * z.val * braidProject (e crossedMiddle) =
      fundamentalBraidTargetCharacter z • braidProject (e crossedMiddle) := by
  have hq : IsIdempotentElem middleIdem := IsIdempotentElem.map
    (by simp [IsIdempotentElem,StendhalAlgebraAllOrders.e_mul_e]) project
  let x : rIdeal middleIdem := ⟨middleIdem * fundamentalBraidTargetEquiv z,by
    rw [mem_rIdeal,← mul_assoc,hq.eq]⟩
  have hm := middle_mul_middle x
  change middleIdem * fundamentalBraidTargetEquiv z * middleIdem =
    middleCharacter (middleIdem * fundamentalBraidTargetEquiv z) • middleIdem at hm
  rw [map_mul,middleCharacter_middleIdem,one_mul] at hm
  have h := congrArg toAmbient hm
  have hz : toAmbient (fundamentalBraidTargetEquiv z) = z.val := by
    change (fundamentalBraidTargetEquiv.symm (fundamentalBraidTargetEquiv z)).val = _
    rw [fundamentalBraidTargetEquiv.symm_apply_apply]
  rw [toAmbient_mul,toAmbient_mul,map_rat_smul,toAmbient_middle,hz] at h
  exact h

end Categorification.Stendhal.FundamentalCorner
