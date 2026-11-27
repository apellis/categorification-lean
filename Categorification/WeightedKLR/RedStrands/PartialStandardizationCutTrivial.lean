/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationLift

/-!
# Partial standardization at a cut with an empty last block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. When the
last block of a cut has no strands, the partial standardization at the cut does nothing: the
identity-shuffle inclusion `N → 𝕊(N)` is bijective (`cutStandardUnit_bijective_of_right_zero`,
`cutStandardRightZeroEquiv`), because every affine diagram of all strands is a juxtaposition
of an affine diagram of the first block with the empty diagram (`exists_concat_tmul_one`).
This is the base case of the associativity of the staged standardization at a cut.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

section Concat

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- **Every element of `R(ν + ν')` with `ν' = 0` is a juxtaposition with the empty diagram.** -/
theorem exists_concat_tmul_one {ν ν' : Multiset I} (h : ν' = 0) (z : KLRAlgebra k Q (ν + ν')) :
    ∃ b : KLRAlgebra k Q ν, concat Q ν ν' (b ⊗ₜ[k] 1) = z := by
  subst h
  refine ⟨castKLR Q (add_zero ν) z, (castKLR Q (add_zero ν)).injective ?_⟩
  exact concat_one_right (Q := Q) _

end Concat

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- With an empty last block, the identity-shuffle inclusion is surjective. -/
theorem cutStandardUnit_surjective_of_right_zero (hδ : δ = 0) :
    Function.Surjective (cutStandardUnit Q Λ θ β N) := by
  intro v
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ v
  induction y using BalancedTensor.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n', hn'⟩ := hy
    exact ⟨n + n', by rw [map_add, hn, hn', map_add]⟩
  | tmul m n =>
    obtain ⟨b, hb⟩ := exists_concat_tmul_one S hδ (m : KLRAlgebra k S (α + δ))
    refine ⟨cutInputMap Q Λ θ β (b ⊗ₜ[k] 1) • (show N from n), ?_⟩
    have hm : m = op (b ⊗ₜ[k] (1 : KLRAlgebra k S δ)) • oneConcatSubBimod := by
      apply Subtype.ext
      rw [coe_op_smul, unop_op]
      change _ = oneConcat S α δ * concat S α δ (b ⊗ₜ[k] 1)
      exact hb.symm.trans (((congrArg (· * concat S α δ (b ⊗ₜ[k] 1)) (concat_one (Q := S)
        (ν := α) (ν' := δ))).symm.trans ((concat_mul _ _).symm.trans
          (congrArg (concat S α δ) (one_mul _)))).symm)
    change Submodule.mkQ _ (BalancedTensor.tmul oneConcatSubBimod
        ((b ⊗ₜ[k] (1 : KLRAlgebra k S δ)) • (show CutInput Q Λ θ β N from n))) = _
    rw [← BalancedTensor.op_smul_tmul, ← hm]

variable (hQ : KLRSymm Q)

include hQ in
/-- **With an empty last block, partial standardization at the cut is the identity.** -/
theorem cutStandardUnit_bijective_of_right_zero (hδ : δ = 0) :
    Function.Bijective (cutStandardUnit Q Λ θ β N) :=
  ⟨cutStandardUnit_injective Q Λ θ β N hQ, cutStandardUnit_surjective_of_right_zero Q Λ θ β N hδ⟩

/-- **The partial standardization at a cut with an empty last block**, `N ≃ 𝕊(N)` along the
identity shuffle. -/
def cutStandardRightZeroEquiv (hδ : δ = 0) : N ≃ₗ[k] CutStandard Q Λ θ β N :=
  LinearEquiv.ofBijective (cutStandardUnit Q Λ θ β N)
    (cutStandardUnit_bijective_of_right_zero Q Λ θ β N hQ hδ)

theorem cutStandardRightZeroEquiv_apply (hδ : δ = 0) (n : N) :
    cutStandardRightZeroEquiv Q Λ θ β N hQ hδ n = cutStandardUnit Q Λ θ β N n := rfl

/-- The identification is compatible with the affine diagrams of the two blocks. -/
theorem cutStandardRightZeroEquiv_concat (hδ : δ = 0) (t : TensorKLR S α δ) (n : N) :
    cutStandardAction Q Λ θ β N hQ (cutAffineMap Q Λ θ β (concat S α δ t))
        (cutStandardRightZeroEquiv Q Λ θ β N hQ hδ n) =
      cutStandardRightZeroEquiv Q Λ θ β N hQ hδ (cutInputMap Q Λ θ β t • n) :=
  cutStandardAction_concat_unit Q Λ θ β N hQ t n

end Categorification.Stendhal
