/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksMidBotCorner
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneCorner

/-!
# The right action on the bottom corner at the outer cut of three blocks

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the intertwining
of the bottom corners).

On the partial standardization `𝕊(N)` at a cut, an affine diagram `ι(t)` of the two blocks
acts on the identity-shuffle copy `1 ⊗ n` of the input by `1 ⊗ t n`; so the identity
coordinate of `ι(t) · (1 ⊗ n)` is `t · n` (`cutStandardShuffleEquiv_affineToTensor_concat_unit`).

For three blocks `A | M | R`, let `q` be a Mackey datum of the outer cut with `q.β` the weight of
the middle block. `R(q.γ) ⊗ R(q.δ)` acts on the bottom corner `E · BlocksMid X` through
`c ↦ quadBot (1 ⊗ c)` (`botCornerModuleRight`). Read through the identity coordinate
`botCornerBlocksEquiv`, `a ⊗ b` acts by the head factor of `ι(1 ⊗ a)` composed with the action of
`t̃` on the inner input, whenever the image of `ι(1_β ⊗ b)` in the algebra `T^{MR}` of the two
inner blocks is the image of an affine diagram `ι(t̃)` of the two inner blocks
(`botCornerBlocksEquiv_smul`). The hypothesis `hb` is the identification of that image; it is
discharged for the leading data of L5 by a relabelling computation (handoff, step 2), and is
not a hypothesis of Lemma 7.19.

Webster's proof does not spell this out. Any commutative ring `k`, symmetric `Q`.

## Main results

* `Stendhal.cutStandardShuffleEquiv_affineToTensor_concat_unit`,
  `Stendhal.botCornerBlocksEquiv_smul`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Cut

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "Sh" => Shuffle (Seq.card_add' α δ)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

/-- **An affine diagram of the two blocks on the identity-shuffle copy**: the identity
coordinate of `ι(t) · (1 ⊗ n)` in `𝕊(N)` is `t · n`. -/
theorem cutStandardShuffleEquiv_affineToTensor_concat_unit (t : TensorKLR S α δ) (n : N) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ
        (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (concat S α δ t))
          (cutStandardUnit Q Λ θ β N n)) : Sh → CutInput Q Λ θ β N) shufOne =
      (t • (show CutInput Q Λ θ β N from n) : CutInput Q Λ θ β N) := by
  have h := cutStandardAction_concat_unit Q Λ θ β N hQ t n
  have h' : cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (concat S α δ t))
      (cutStandardUnit Q Λ θ β N n) =
      cutStandardUnit Q Λ θ β N (cutInputMap Q Λ θ β t • n) := h
  rw [h']
  exact (congrFun (cutStandardShuffleEquiv_unit Q Λ θ β N hQ
    (cutInputMap Q Λ θ β t • n : CutInput Q Λ θ β N)) shufOne).trans (Pi.single_eq_same _ _)

end Cut

section Blocks

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ)
  (θ β γ : Multiset I)

local notation "αi" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β)
local notation "δi" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)
local notation "cR" => Sum.map (id : I → I) (Fin.natAdd a : Fin (m + r) → Fin (a + (m + r)))
local notation "Si" => stendhalQ Q (blocksTailLabels Λ)
local notation "So" => stendhalQ Q Λ

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]
  (hQ : KLRSymm Q)

local notation "Nₒ" => CutInput Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)
local notation "Inner" => CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "CSi" => CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)

variable {ν ν' : Multiset (I ⊕ Fin (a + (m + r)))} {q : MackeyQuad ν ν'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ)))}

attribute [local instance] botCornerModuleRight

/-- **The right action on the bottom corner at the outer cut, in the identity coordinate.**
If the image of `ι(1_β ⊗ b)` in `T^{MR}(β + γ)` is the image of an affine diagram `ι(t̃)` of the
two inner blocks (`hb`), then `a ⊗ b` acts on `E · BlocksMid X` by the head factor of
`ι(1 ⊗ a)` after `t̃` on the inner input. -/
theorem botCornerBlocksEquiv_smul (hβ : q.β = (αi).map cR) (x : KLRAlgebra k So q.γ)
    (b : KLRAlgebra k So q.δ) (t : TensorKLR Si αi δi)
    (hb : cutSuffixProjection (a := a) (r := m + r) Q Λ (β + γ)
        (castAlg So q.h₄ (concat So q.β q.δ (1 ⊗ₜ b))) =
      affineToTensor (a := m) (r := r) Q (blocksTailLabels Λ) β γ (concat Si αi δi t))
    (z : botCorner So q Nₒ) :
    (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ ((x ⊗ₜ b : TensorKLR So q.γ q.δ) • z) : Inner) =
      blocksHeadEnd Q Λ θ β γ N
        (cutPrefixProjection (a := a) (r := m + r) Q Λ θ
          (castAlg So q.h₃ (concat So q.α q.γ (1 ⊗ₜ x))))
        (t • (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z : Inner)) := by
  have hz : ((z : Nₒ) : CSi) = cutStandardUnit Q (blocksTailLabels Λ) β γ
      (BlocksInner Q Λ θ β γ N) (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z : Inner) := by
    have := botCornerBlocksEquiv_symm_apply Q Λ θ β γ N hQ hβ
      (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z)
    rw [LinearEquiv.symm_apply_apply] at this
    exact this
  rw [botCornerBlocksEquiv_apply Q Λ θ β γ N hQ hβ ((x ⊗ₜ b : TensorKLR So q.γ q.δ) • z)]
  have h1 : (1 : TensorKLR So q.α q.β) = (1 : KLRAlgebra k So q.α) ⊗ₜ
      (1 : KLRAlgebra k So q.β) := rfl
  change (cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
      (blocksMidAction Q Λ θ β γ N hQ (cutInputMap Q Λ θ (β + γ)
        (quadBot q ((1 : TensorKLR So q.α q.β) ⊗ₜ (x ⊗ₜ b)))) ((z : Nₒ) : CSi)) :
      Shuffle (Seq.card_add' αi δi) → Inner) shufOne = _
  rw [h1, quadBot_tmul]
  simp only [cutInputMap, Algebra.TensorProduct.map_tmul, blocksMidAction,
    Algebra.TensorProduct.lift_tmul]
  rw [hb]
  erw [Module.End.mul_apply]
  rw [cutStandardShuffleEquiv_blocksHeadAction, hz]
  refine congrArg _ ?_
  exact cutStandardShuffleEquiv_affineToTensor_concat_unit Q (blocksTailLabels Λ) β γ
    (BlocksInner Q Λ θ β γ N) hQ t _

end Blocks

end Categorification.Stendhal
