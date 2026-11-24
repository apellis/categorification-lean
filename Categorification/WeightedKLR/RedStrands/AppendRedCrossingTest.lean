/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingCut
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingTransport
import Categorification.WeightedKLR.RedStrands.Projectives

/-!
# The ordinary injectivity test after appending a spectator

Webster, arXiv:1309.3796v2, Lemma 5.23 and the proof of Lemma 6.8 at (6.21).
The red induction preserves a right multiplication test, and its two cut diagrams
are the earlier idempotent and crossing with the terminal red appended.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)
variable (θ : Multiset I)

local notation "Λ₀" => Λ ∘ Fin.castSucc
local notation "ν" => (θ + 0)
local notation "μ" => stendhalWeight ℓ ν
local notation "L₀" => TensorProductAlgebra k Q Λ₀ ν
local notation "L" => TensorProductAlgebra k Q Λ ν

private theorem tensorOfKLR_idem {m : ℕ} (weights : Fin m → I →₀ ℕ)
    (s : Seq (stendhalWeight m ν)) (hs : IsRedOrdered s) :
    tensorOfKLR Q weights ν (e s) = TensorProductAlgebra.mk Q weights ν (StendhalAlgebra.e s hs) :=
  congrArg _ (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans
    (ite_eq_left hs)))

/-- An ordinary crossing test stays injective after appending a terminal red. -/
theorem eq_zero_of_mul_appendRedCrossing (hQ : KLRSymm Q)
    (s t : Seq μ) (hs : IsRedOrdered s) (ht : IsRedOrdered t)
    (j : ℕ) (hj : j + 1 < Multiset.card μ)
    (hbase : ∀ y : L₀, y * tensorOfKLR Q Λ₀ ν (e s) = y →
      y * tensorOfKLR Q Λ₀ ν (ψ j * e t) = 0 → y = 0)
    (x : L) (hx : x * tensorOfKLR Q Λ ν (e (appendRedLoading s)) = x)
    (hc : x * tensorOfKLR Q Λ ν (ψ j * e (appendRedLoading t)) = 0) : x = 0 := by
  let f := tensorOfKLR Q Λ₀ ν (e s)
  let c := tensorOfKLR Q Λ₀ ν (ψ j * e t)
  have hf : IsIdempotentElem f := by
    dsimp [f]
    rw [tensorOfKLR_idem Q θ Λ₀ s hs]
    exact isIdempotentElem_mk_e s hs
  have hfin : emptyRedHom Q Λ θ f = tensorOfKLR Q Λ ν (e (appendRedLoading s)) := by
    dsimp [f]
    rw [emptyRedHom_apply, tensorOfKLR_idem Q θ Λ₀ s hs, appendRed_mk_e,
      tensorOfKLR_idem Q θ Λ _ ((appendRedLoading_ordered_iff s).2 hs)]
  have hcin : emptyRedHom Q Λ θ c = tensorOfKLR Q Λ ν (ψ j * e (appendRedLoading t)) :=
    appendRed_tensorOfKLR_crossing Q Λ ν t ht j hj
  have hi := emptyRed_lIdeal_ind_map_injective Q Λ θ hQ (rmulLIdeal_injective hbase)
  exact eq_zero_of_mul_map (emptyRedHom Q Λ θ) hf c hi x
    (by rw [hfin]; exact hx) (by rw [hcin]; exact hc)

end Categorification.Stendhal
