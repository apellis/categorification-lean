/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KFlip

/-!
# The reflected coevaluation bimodule on diagrams

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof. In the reflection `K^σ` of `K^{λ⁺}_λ`
(`ReflectedCap`), a diagram of `T^{λ⁺}` acts on the left by its horizontal mirror image attached
below the cap diagram, and a diagram of `T^λ` acts on the right by its mirror image attached
above it (`mk_smul_toRefl`, `op_mk_smul_toRefl`). On the generators `e(s)`,
`ψ_p` and `x_a`, which are their own mirror images, this is attaching the generator itself.
These are the computations behind the comparison maps of Lemma 7.19 (K).

## Main results

* `tensorFlipRingEquiv_mk`: the reflection on the image of an affine diagram.
* `toRefl`: the class in `K^σ` of an element of `K̃^{λ⁺}_λ`.
* `mk_smul_toRefl`, `op_mk_smul_toRefl`: the actions on cap diagrams.
* `mk_e_smul_toRefl`, `mk_ψ_smul_toRefl`, `mk_x_smul_toRefl` and the right-hand versions
  `op_mk_e_smul_toRefl`, `op_mk_ψ_smul_toRefl`, `op_mk_x_smul_toRefl`: the actions of
  generators.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

/-- **The reflection of the image of an affine diagram** is the image of its mirror image. -/
theorem tensorFlipRingEquiv_mk {n : ℕ} {Λ' : Fin n → I →₀ ℕ} {ν' : Multiset I}
    (a : KLRAlgebra k (stendhalQ Q Λ') (stendhalWeight n ν')) :
    tensorFlipRingEquiv (Q := Q) (Λ := Λ') ν'
        (TensorProductAlgebra.mk Q Λ' ν' (topMap k Q Λ' ν' a)) =
      op (TensorProductAlgebra.mk Q Λ' ν' (topMap k Q Λ' ν' (hflip a))) :=
  congrArg op (tensorFlip_projection a)

theorem tensorFlipRingEquiv_symm_op_mk {n : ℕ} {Λ' : Fin n → I →₀ ℕ} {ν' : Multiset I}
    (a : KLRAlgebra k (stendhalQ Q Λ') (stendhalWeight n ν')) :
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ') ν').symm
        (op (TensorProductAlgebra.mk Q Λ' ν' (topMap k Q Λ' ν' a))) =
      TensorProductAlgebra.mk Q Λ' ν' (topMap k Q Λ' ν' (hflip a)) := by
  rw [RingEquiv.symm_apply_eq, tensorFlipRingEquiv_mk, hflip_hflip]

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- The class in the reflection of `K^{λ⁺}_λ` of an element of `K̃^{λ⁺}_λ`. -/
def toRefl (y : CapTilde k Q Λ Λc j hj ν ν₀ L) : ReflectedCap j hj Q Λ Λc ν ν₀ L :=
  toReflectedCap (toMidCap L y)

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem toRefl_add (y y' : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    toRefl (y + y') = toRefl y + toRefl y' :=
  toMidCap_add y y'

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem toRefl_surjective : Function.Surjective (toRefl (L := L) (Λ := Λ) (Λc := Λc) (j := j)
    (hj := hj) (ν := ν) (ν₀ := ν₀) (Q := Q)) := fun z =>
  Submodule.Quotient.mk_surjective _ z

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- **A diagram of `T^{λ⁺}` acts on the reflection** by its mirror image below the cap. -/
theorem mk_smul_toRefl
    (a : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀) (botMap k Q Λ Λc j hj ν ν₀ a) •
        toRefl y =
      toRefl ((Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ (hflip a)) : Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [toRefl, smul_toReflectedCap, tensorFlipRingEquiv_mk]
  rfl

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- **A diagram of `T^λ` acts on the reflection from the right** by its mirror image above the
cap. -/
theorem op_mk_smul_toRefl (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν a)) • toRefl y =
      toRefl ((Env.mk (topMap k Q Λ ν (hflip a)) 1 : Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [toRefl, op_smul_toReflectedCap, tensorFlipRingEquiv_symm_op_mk]
  rfl

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem mk_e_smul_toRefl (s : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e s)) • toRefl y =
      toRefl ((Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e s)) :
        Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [mk_smul_toRefl, hflip_e]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem mk_ψ_smul_toRefl (p : ℕ) (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.ψ p)) • toRefl y =
      toRefl ((Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.ψ p)) :
        Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [mk_smul_toRefl, hflip_ψ]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem mk_x_smul_toRefl (a : Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))))
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.x a)) • toRefl y =
      toRefl ((Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.x a)) :
        Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [mk_smul_toRefl, hflip_x]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem op_mk_e_smul_toRefl (s : Seq (stendhalWeight ℓ ν)) (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.e s))) • toRefl y =
      toRefl ((Env.mk (topMap k Q Λ ν (KLRAlgebra.e s)) 1 : Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [op_mk_smul_toRefl, hflip_e]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem op_mk_ψ_smul_toRefl (p : ℕ) (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.ψ p))) • toRefl y =
      toRefl ((Env.mk (topMap k Q Λ ν (KLRAlgebra.ψ p)) 1 : Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [op_mk_smul_toRefl, hflip_ψ]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem op_mk_x_smul_toRefl (a : Fin (Multiset.card (stendhalWeight ℓ ν)))
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.x a))) • toRefl y =
      toRefl ((Env.mk (topMap k Q Λ ν (KLRAlgebra.x a)) 1 : Env k Q Λ Λc j hj ν ν₀) • y) := by
  rw [op_mk_smul_toRefl, hflip_x]

end Categorification.Stendhal.CupCap
