/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotRightHigherPBW
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralCornerFlag

/-!
# The intersection of the two rightmost images

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
The first central crossing is injective on its loading projective,
so its inverse on its range embeds the intersection of the two images
in that same projective over the right corner.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA MulOpposite CornerEndomorphism

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "v₂" => fixedTopFourExitCut 2
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord v₂))
local notation "A" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord v₂))
private theorem rightmost_E1_order : redWord v₁ = redWord v₂ := by decide
local notation "e₁" => orderedLoadingIdemAt Q Λ (redWord v₂) v₁ rightmost_E1_order
local notation "P₁" => rIdeal e₁
local notation "K" => blockLoadingKernel Q Λ v₂ 1 2
local notation "c" => F (ψw [2,1] * e v₁)

private theorem rightmost_c_left : F (e v₂) * c = c := by
  rw [← map_mul]
  have top : wordProd N [2,1] • v₁ = v₂ := by decide
  rw [← top, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

private theorem rightmost_E1_left (y : P₁) : F (e v₁) * y.1.1 = y.1.1 := by
  have h := y.2
  change e₁ * y.1 = y.1 at h
  exact congrArg (fun z : A => z.1) h

private theorem rightmost_c_rep_val (y : P₁) :
    (blockLoadingRep Q Λ v₂ (c * y.1.1)).1.1 = c * y.1.1 := by
  have hr : y.1.1 * E = y.1.1 := corner_mul_right _ y.1
  exact (blockLoadingRep_val Q Λ v₂ _).trans (by
    change F (e v₂) * (c * y.1.1) * E = c * y.1.1
    rw [← mul_assoc, rightmost_c_left Q Λ, mul_assoc, hr])

private def rightmost_c_element (hQ : KLRSymm Q) (y : P₁) : K :=
  ⟨blockLoadingRep Q Λ v₂ (c * y.1.1),
    (fiveSlotRightmostKernel_mem_iff_two_central_factors Q Λ hQ _).2
      ⟨y.1.1, 0, rightmost_E1_left Q Λ y, mul_zero _, corner_mul_right _ y.1, zero_mul _,
        by rw [rightmost_c_rep_val Q Λ y, mul_zero, add_zero]⟩⟩

private theorem rightmost_c_element_val (hQ : KLRSymm Q) (y : P₁) :
    (rightmost_c_element Q Λ hQ y).1.1.1 = c * y.1.1 :=
  rightmost_c_rep_val Q Λ y

private theorem rightmost_K_injective :
    Function.Injective (fun z : K => z.1.1.1) := fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

private theorem rightmost_c_element_add (hQ : KLRSymm Q) (y z : P₁) :
    rightmost_c_element Q Λ hQ (y + z) =
      rightmost_c_element Q Λ hQ y + rightmost_c_element Q Λ hQ z := by
  apply rightmost_K_injective Q Λ
  change (rightmost_c_element Q Λ hQ (y + z)).1.1.1 =
    (rightmost_c_element Q Λ hQ y).1.1.1 + (rightmost_c_element Q Λ hQ z).1.1.1
  rw [rightmost_c_element_val, rightmost_c_element_val, rightmost_c_element_val]
  exact mul_add c _ _

private theorem rightmost_c_element_smul (hQ : KLRSymm Q) (r : Aᵐᵒᵖ) (y : P₁) :
    rightmost_c_element Q Λ hQ (r • y) = r • rightmost_c_element Q Λ hQ y := by
  apply rightmost_K_injective Q Λ
  change (rightmost_c_element Q Λ hQ (r • y)).1.1.1 =
    (rightmost_c_element Q Λ hQ y).1.1.1 * r.unop.1
  rw [rightmost_c_element_val, rightmost_c_element_val]
  exact (mul_assoc c _ _).symm

/-- The first central crossing into the rightmost higher kernel. -/
def fiveSlotRightmost_firstCentralMap (hQ : KLRSymm Q) : P₁ →ₗ[Aᵐᵒᵖ] K where
  toFun := rightmost_c_element Q Λ hQ
  map_add' := rightmost_c_element_add Q Λ hQ
  map_smul' := rightmost_c_element_smul Q Λ hQ

theorem fiveSlotRightmost_firstCentralMap_val (hQ : KLRSymm Q) (y : P₁) :
    (fiveSlotRightmost_firstCentralMap Q Λ hQ y).1.1.1 = c * y.1.1 :=
  rightmost_c_element_val Q Λ hQ y

theorem fiveSlotRightmost_firstCentralMap_injective (hQ : KLRSymm Q) :
    Function.Injective (fiveSlotRightmost_firstCentralMap Q Λ hQ) := by
  apply (injective_iff_map_eq_zero _).2
  intro y hy
  apply Subtype.ext
  apply Subtype.ext
  change y.1.1 = (0 : V)
  apply FiveSlotFlag.fiveSlotRightmost_firstCrossing_cancel_on_orderCorner Q Λ hQ y.1.1
    (rightmost_E1_left Q Λ y)
  · have h : redWord v₀ = redWord v₂ := by decide
    rw [h]
    exact corner_mul_right _ y.1
  · have h := congrArg (fun z : K => z.1.1.1) hy
    exact (rightmost_c_element_val Q Λ hQ y).symm.trans h

private def crossingIntersectionPreimage {B M N₀ : Type} [Ring B]
    [AddCommGroup M] [AddCommGroup N₀] [Module B M] [Module B N₀]
    (f g : M →ₗ[B] N₀) (hf : Function.Injective f) :
    ↥(LinearMap.range f ⊓ LinearMap.range g) →ₗ[B] M :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp (Submodule.inclusion inf_le_left)

private theorem crossingIntersectionPreimage_injective {B M N₀ : Type} [Ring B]
    [AddCommGroup M] [AddCommGroup N₀] [Module B M] [Module B N₀]
    (f g : M →ₗ[B] N₀) (hf : Function.Injective f) :
    Function.Injective (crossingIntersectionPreimage f g hf) :=
  (LinearEquiv.ofInjective f hf).symm.injective.comp (Submodule.inclusion_injective inf_le_left)

section Intersection
variable (hQ : KLRSymm Q)

local notation "C" => fiveSlotRightmost_firstCentralMap Q Λ hQ
local notation "D" => fiveSlotRightmostKernel_nilHecke Q Λ

/-- The intersection of the two fixed central crossing images embeds in the
central loading projective over the same right corner. -/
def fiveSlotRightmost_centralIntersectionIntoProjective :=
  crossingIntersectionPreimage (B := Aᵐᵒᵖ) (M := ↥P₁) (N₀ := ↥K) C
    (LinearMap.comp D C) (fiveSlotRightmost_firstCentralMap_injective Q Λ hQ)

theorem fiveSlotRightmost_centralIntersectionIntoProjective_injective :
    Function.Injective (fiveSlotRightmost_centralIntersectionIntoProjective Q Λ hQ) := by
  unfold fiveSlotRightmost_centralIntersectionIntoProjective
  apply crossingIntersectionPreimage_injective

end Intersection

end Categorification.Stendhal.BraidedStendhalAlgebra
