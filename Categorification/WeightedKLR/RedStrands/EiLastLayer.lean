/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiCaseBoth
import Categorification.WeightedKLR.RedStrands.TwoPieceLastBlackRes

/-!
# Naturality of `₂Eᵢ X_M ≅ X_{M e}`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. The isomorphism `lastBlackInputEquiv` between the restriction of the two-piece
input `X_M` along the last black strand of the last factor and the input `X_{M e}` of
`ₗEᵢ M = M e` is natural in endomorphisms of `M` (`lastBlackInputEquiv_natural`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b b' : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' (Fin.last ℓ) = rightBlock b (Fin.last ℓ))
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα'' : RootNonViolated (ν := initWeight b') (blockRoot (initBlocks b')))

local notation "hinit" => initBlocks_eq_of_last h0 hr
local notation "M'" => BlockBlackRes Q Λ i (Fin.last ℓ) h0 hr hκ M
local notation "CM'" => CastBlockModule Q (Λ ∘ Fin.castSucc) hinit (InitRestrict Q Λ b' M')
local notation "hθ" => initWeight_eq_of_last h0 hr
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "XL'" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b') rfl hα''
  (InitRestrict Q Λ b' M')
local notation "inc" => lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα''
local notation "g'" => blockBlackResEnd Q Λ i (Fin.last ℓ) h0 hr hκ M

theorem lastBlackInputCast_mapRight_end
    (φ : Module.End (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b'))ᵐᵒᵖ
      (InitRestrict Q Λ b' M')) (x : XL') :
    lastBlackInputCast Q Λ i h0 hr hκ M hα' hα''
        (show FamilyCast Tfam hθ XL' from
          (BalancedTensor.mapRight φ : XL' →ₗ[Tfam (initWeight b')] XL') x) =
      BalancedTensor.mapRight (castBlockModuleMap hinit φ)
        (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' (show FamilyCast Tfam hθ XL' from x)) := by
  rw [lastBlackInputCast, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    leftStandardizationFamilyCast_symm_mapRight, leftStandardizationCast_mapRight]

theorem lastBlackIncl_comp_initRestrictEnd (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    (lastBlackIncl Q Λ i h0 hr hκ M).comp
        (castBlockModuleMap hinit (initRestrictEnd Q Λ b' (g' g))) =
      (initRestrictEnd Q Λ b g).comp (lastBlackIncl Q Λ i h0 hr hκ M) :=
  LinearMap.ext fun _ => rfl

/-- **The inclusion `X_{M e} → X_M` is natural in `M`.** -/
theorem lastBlackInputIncl_initRestrictEnd (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (x : XL') :
    inc (show FamilyCast Tfam hθ XL' from
        (BalancedTensor.mapRight (initRestrictEnd Q Λ b' (g' g)) :
          XL' →ₗ[Tfam (initWeight b')] XL') x) =
      BalancedTensor.mapRight (initRestrictEnd Q Λ b g) (inc (show FamilyCast Tfam hθ XL' from x))
      := by
  change lastBlackInclRight Q Λ i h0 hr hκ M hα' (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' _) =
    BalancedTensor.mapRight (initRestrictEnd Q Λ b g)
      (lastBlackInclRight Q Λ i h0 hr hκ M hα' (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' _))
  rw [lastBlackInputCast_mapRight_end, lastBlackInclRight, ← LinearMap.comp_apply,
    ← BalancedTensor.mapRight_comp, lastBlackIncl_comp_initRestrictEnd,
    BalancedTensor.mapRight_comp, LinearMap.comp_apply]

/-- **Naturality of `₂Eᵢ X_M ≅ X_{M e}`** in endomorphisms of `M`. -/
theorem lastBlackInputEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (x : FactorCast Q Λ (initWeight_eq_of_last h0 hr) (rfl : lastBlock b' = lastBlock b')
      (TwoPieceInput Q Λ b' M' hα'')) :
    lastBlackInputEquiv Q Λ i h0 hr hκ M hα' hα''
        (factorCastMap Q Λ (initWeight_eq_of_last h0 hr) rfl (twoPieceEnd Q Λ b' hα'' (g' g)) x) =
      Res.map (factorCastMap Q Λ rfl (lastBlock_eq_of_last i hκ) (twoPieceEnd Q Λ b hα' g))
        (lastBlackInputEquiv Q Λ i h0 hr hκ M hα' hα'' x) := by
  apply Res.ext
  rw [Res.val_map, lastBlackInputEquiv_val, lastBlackInputEquiv_val]
  change (twoPieceInputOf Q Λ b M hα') (inc (show FamilyCast Tfam hθ XL' from
    (BalancedTensor.mapRight (initRestrictEnd Q Λ b' (g' g)) : XL' →ₗ[Tfam (initWeight b')] XL')
      (show XL' from x))) = twoPieceEnd Q Λ b hα' g
        (twoPieceInputOf Q Λ b M hα' (inc (show FamilyCast Tfam hθ XL' from x)))
  rw [lastBlackInputIncl_initRestrictEnd, twoPieceEnd_of]

end StendhalAlgebra

end Categorification.Stendhal
