/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KHomRep
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCapSum

/-!
# Scalars on the reflection of `K^{λ⁺}_λ`

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the inverse `Ψ` of the comparison map is
built from maps out of the reflection `K^σ` of `K^{λ⁺}_λ`, on which `T^λ` acts by
precomposition (`BalancedTensor.precompRep`). That action is an algebra map because the
scalars act on `K^σ` alike from both sides (`reflectedCap_op_algebraMap_smul`).

## Main results

* `Stendhal.CupCap.reflectedCap_op_algebraMap_smul`: the scalars act alike from both sides.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The scalars act on the reflection of `K^{λ⁺}_λ` alike from both sides.** -/
theorem reflectedCap_op_algebraMap_smul (c : k) (z : ReflectedCap j hj Q Λ Λc ν ν₀ L) :
    op (algebraMap k (TensorProductAlgebra k Q Λ ν) c) • z =
      algebraMap k (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) c • z := by
  obtain ⟨y, rfl⟩ := toRefl_surjective z
  have ha : algebraMap k (TensorProductAlgebra k Q Λ ν) c =
      TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν
        (algebraMap k (KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) c)) := by
    rw [AlgHom.commutes, AlgHom.commutes]
  have hb : algebraMap k (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) c =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀) (botMap k Q Λ Λc j hj ν ν₀
        (algebraMap k (KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
          (stendhalWeight (ℓ + 2) (ν + ν₀))) c)) := by
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [ha, hb, op_mk_smul_toRefl, mk_smul_toRefl, hflip_algebraMap, hflip_algebraMap,
    AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one c, Env.mk_smul_right]

end Categorification.Stendhal.CupCap
