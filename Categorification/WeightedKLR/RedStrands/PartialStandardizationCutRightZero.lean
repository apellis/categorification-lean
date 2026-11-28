/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorAssoc
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutTrivial

/-!
# Partial standardization at a cut with an empty last block: the action

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4, for a cut with no red strands and no
black strands in the second block. Then the identity-shuffle inclusion `N → 𝕊(N)` is
bijective (`cutStandardRightZeroEquiv`), and it intertwines the action of `t ∈ T^λ(θ)`, cast to
`T^λ(θ + 0)`, with the action of `t ⊗ 1` on `N`. This is the base case of the computation of
the standardization in stages (§7.3, proof of Lemma 7.19).

## Main results

* `Stendhal.cutPrefixProjection_right_zero`: the quotient of the first block is the affine
  quotient of all strands, when the second block is empty.
* `Stendhal.cutStandardAction_right_zero_unit`,
  `Stendhal.cutSpectStandardAction_right_zero_unit`: the action on the image of the unit,
  without and with a spectator.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-- Concatenation with the unit of an empty weight is the cast of weights. -/
theorem concat_right_zero_eq {J k : Type*} [DecidableEq J] [CommRing k]
    {P : J → J → MvPolynomial (Fin 2) k} {ν ν' : Multiset J} (h : ν' = 0)
    (b : KLRAlgebra k P ν) :
    concat P ν ν' (b ⊗ₜ 1) = castKLR P (by rw [h, add_zero]) b := by
  subst h
  conv_rhs => rw [← concat_one_right b]
  rw [castKLR_castKLR]
  rfl

variable {I k : Type*} [DecidableEq I] [CommRing k] {a : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + 0) → I →₀ ℕ) (θ : Multiset I)

local notation "S" => stendhalQ Q Λ

omit [DecidableEq I] in
/-- The second block of a cut with no red and no black strands has empty weight. -/
theorem cutRightZero_weight :
    Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight 0 (0 : Multiset I)) =
      0 := by
  simp [stendhalWeight]

omit [DecidableEq I] in
/-- Relabelling the red strands along `Fin.castAdd 0` does not change the weight. -/
theorem castAdd_zero_weight :
    stendhalWeight a θ =
      Multiset.map (Sum.map (id : I → I) (Fin.castAdd 0)) (stendhalWeight a θ) := by
  conv_lhs => rw [← Multiset.map_id (stendhalWeight a θ)]
  congr 1
  funext y
  cases y <;> rfl

/-- **With an empty second block, the quotient of the first block is the affine quotient**:
`T^λ(θ) → T^λ(θ + 0)` after the quotient of the first block is the affine quotient of the
concatenation with the unit of the empty block. -/
theorem cutPrefixProjection_right_zero (b : KLRAlgebra k S
    (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 0)) (stendhalWeight a θ))) :
    castTensorProductAlgebra Q Λ (add_zero θ).symm
        (cutPrefixProjection (a := a) (r := 0) Q Λ θ b) =
      cutAffineMap (a := a) (r := 0) Q Λ θ 0 (concat S _ _ (b ⊗ₜ 1)) := by
  rw [cutAffineMap_apply]
  simp only [cutPrefixProjection, redSubfamilyProjection, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom]
  set u := (relabelEquiv (redSubfamilyRelabel Q Λ (Fin.castAdd 0)
    (Fin.castAdd_injective a 0) θ)).symm b
  have hu : b = castKLR S (castAdd_zero_weight (I := I) (a := a) θ) u := by
    refine ((relabelEquiv (redSubfamilyRelabel Q Λ (Fin.castAdd 0)
      (Fin.castAdd_injective a 0) θ)).apply_symm_apply b).symm.trans ?_
    refine relabelEquiv_eq_castKLR (P := S) (redSubfamilyRelabel Q Λ (Fin.castAdd 0)
      (Fin.castAdd_injective a 0) θ) (castAdd_zero_weight (I := I) (a := a) θ) (fun s => ?_) u
    apply Subtype.ext; funext p
    change Sum.map (id : I → I) (Fin.castAdd 0) (s.1 _) = s.1 _
    cases s.1 _ <;> rfl
  clear_value u
  subst hu
  refine (castTensorProductAlgebra_mk Q Λ (add_zero θ).symm u).trans ?_
  refine congrArg (tensorOfKLR Q Λ (θ + 0)) ?_
  refine Eq.symm ((congrArg (castKLR S _)
    (concat_right_zero_eq (P := S) (cutRightZero_weight (a := a)) _)).trans ?_)
  exact (castKLR_castKLR _ _ _).trans (castKLR_castKLR _ _ _)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ 0) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ 0) N] (hQ : KLRSymm Q)

/-- **The action on the partial standardization with an empty second block**: on the image of
the unit, `t ∈ T^λ(θ)` acts as `t ⊗ 1` on `N`. -/
theorem cutStandardAction_right_zero_unit
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 0) θ) (n : N) :
    cutStandardAction Q Λ θ 0 N hQ (castTensorProductAlgebra Q Λ (add_zero θ).symm t)
        (cutStandardUnit Q Λ θ 0 N n) =
      cutStandardUnit Q Λ θ 0 N ((t ⊗ₜ[k] 1 : cutFactorAlgebra Q Λ θ 0) • n) := by
  obtain ⟨b, rfl⟩ := redSubfamilyProjection_surjective Q Λ (Fin.castAdd 0)
    (Fin.castAdd_injective a 0) θ t
  refine (congrArg (fun z => cutStandardAction Q Λ θ 0 N hQ z (cutStandardUnit Q Λ θ 0 N n))
    (cutPrefixProjection_right_zero Q Λ θ b)).trans ?_
  refine (cutStandardRightZeroEquiv_concat Q Λ θ 0 N hQ (cutRightZero_weight (a := a))
    (b ⊗ₜ 1) n).trans ?_
  refine congrArg (cutStandardRightZeroEquiv Q Λ θ 0 N hQ (cutRightZero_weight (a := a))) ?_
  rw [cutInputMap, Algebra.TensorProduct.map_tmul, map_one]

section Spect

variable (E : Type*) [Ring E] [Algebra k E]
  (M : Type*) [AddCommGroup M] [Module k M] [Module (cutSpectAlgebra Q Λ θ 0 E) M]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ 0 E) M]

/-- The action on the partial standardization with an empty second block and a spectator:
on the image of the unit, `t ⊗ e` acts as `(t ⊗ 1) ⊗ e`. -/
theorem cutSpectStandardAction_right_zero_unit
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 0) θ) (e : E) (n : M) :
    cutSpectStandardAction Q Λ θ 0 E M hQ
        (castTensorProductAlgebra Q Λ (add_zero θ).symm t ⊗ₜ[k] e)
        (cutStandardUnit Q Λ θ 0 (CutSpectInput Q Λ θ 0 E M) n) =
      cutStandardUnit Q Λ θ 0 (CutSpectInput Q Λ θ 0 E M)
        (cutSpectTmul Q Λ θ 0 E (t ⊗ₜ[k] 1) e • n) := by
  refine (cutStandardAction_right_zero_unit Q Λ θ (CutSpectInput Q Λ θ 0 E M) hQ t
    (cutSpectTmul Q Λ θ 0 E 1 e • n)).trans ?_
  refine congrArg (cutStandardUnit Q Λ θ 0 (CutSpectInput Q Λ θ 0 E M)) ?_
  refine (cutSpectInput_smul Q Λ θ 0 E M _ _).trans ?_
  refine (mul_smul _ _ n).symm.trans ?_
  rw [cutSpectTmul_mul, mul_one, one_mul]

end Spect

end Categorification.Stendhal
