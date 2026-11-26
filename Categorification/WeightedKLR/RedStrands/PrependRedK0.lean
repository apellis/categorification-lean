/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedInjective
import Categorification.Algebra.Graded.ExtensionK0Injective
import Categorification.WeightedKLR.RedStrands.BraidedStendhal

/-!
# Adding a red strand of large label on `K₀`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
proof of Proposition 4.39. Extension of scalars along `prependRed : T̃^λ_ν → T^{(λ₀, λ)}_ν`
is the functor `𝔯_N` on graded projectives. It is surjective, preserves degrees and is
injective in degree zero once `λ₀` is large, so it is an isomorphism on `K₀`.

## Main definitions

* `prependRedK0` : extension of scalars along `prependRed` on `K₀`.

## Main results

* `prependRedK0_bijective` : `K₀(T̃^λ_ν) ≅ K₀(T^{(λ₀, λ)}_ν)` once
  `⟨α_i^∨, λ₀⟩ · deg x_i` exceeds twice the lower degree bound for every black label `i`.
-/

noncomputable section

open Categorification.Graded MulOpposite

namespace Categorification.Stendhal

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "T̃" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "G₀" => restrictFirstRedGrading Q Λ G
local notation "r" => prependRed Q Λ ν

local instance : Module T̃ᵐᵒᵖ T := Module.compHom T (r).toRingHom.op
local instance : SMulCommClass T T̃ᵐᵒᵖ T where
  smul_comm b a x := (mul_assoc b x (r a.unop)).symm
local instance : IsScalarTower k T̃ᵐᵒᵖ T where
  smul_assoc c a x := by
    change x * r (c • a.unop) = c • (x * r a.unop)
    rw [map_smul, mul_smul_comm]

/-- `prependRed` preserves degrees. -/
theorem prependRed_preservesGrading :
    PreservesGrading (stendhalGrade G₀ ν) (tensorProductGrade G ν) (r).toLinearMap :=
  fun _ _ hx => prependRed_mem_grade Q Λ ν G hx

/-- **The functor `𝔯_N` on `K₀`** (Webster, arXiv:1309.3796v3, proof of Proposition 4.39):
extension of scalars along `prependRed`. -/
def prependRedK0 :
    K0 (stendhalGrade G₀ ν) →ₗ[LaurentPolynomial ℤ] K0 (tensorProductGrade G ν) :=
  extensionK0 (stendhalGrade G₀ ν) (tensorProductGrade G ν) r
    (prependRed_preservesGrading Q Λ ν G) (fun _ _ => rfl)

/-- **`𝔯_N` is an isomorphism on `K₀`** (Webster, arXiv:1309.3796v3, proof of
Proposition 4.39), over a field, for symmetric `Q` and dots of positive degree, once
`⟨α_i^∨, λ₀⟩ · deg x_i > 2c` for every black label `i`, where `T̃^λ` vanishes below degree
`-c` (such `c` exists by `exists_allOrdersGrade_eq_bot`). -/
theorem prependRedK0_bijective (hsym : KLRSymm Q) (hX : ∀ a, 0 < G.degX a) {c : ℤ}
    (hc : ∀ n < -c, allOrdersGrade G₀ ν n = ⊥)
    (hΛ : ∀ i ∈ ν, 2 * c < Λ 0 i * G.degX (.inl i)) :
    Function.Bijective (prependRedK0 Q Λ ν G) := by
  have := hasGdim_stendhalGrade G₀ ν (stendhalQ_symm Q _ hsym) (fun a => hX _)
  exact extensionK0_bijective (𝓡 := stendhalGrade G₀ ν) (𝓢 := tensorProductGrade G ν) r
    (prependRed_preservesGrading Q Λ ν G) (prependRed_surjective Q Λ ν)
    (fun z hz0 hz => prependRed_eq_zero_of_mem_zero Q Λ ν G₀ hc hΛ hz0 hz) (fun _ _ => rfl)

end Categorification.Stendhal
