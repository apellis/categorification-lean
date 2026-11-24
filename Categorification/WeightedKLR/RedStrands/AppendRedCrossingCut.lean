/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.WeightedKLR.RedStrands.BlackIdempotent

/-!
# An earlier crossing with a terminal red spectator

Webster, arXiv:1309.3796v2, Lemma 5.23 and proof of Lemma 6.8 at (6.21).
The map appending an uncrossed terminal red sends a cut at an earlier crossing
to the same crossing with the final red strand appended.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)
variable (ν : Multiset I)

local notation "Λ₀" => Λ ∘ Fin.castSucc
local notation "μ" => stendhalWeight ℓ ν
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "A₀" => StendhalAlgebraAllOrders k Q Λ₀ ν

/-- Appending an un-crossed red spectator preserves a cut at an earlier crossing. -/
theorem appendRed_tensorOfKLR_crossing (s : Seq μ) (hs : IsRedOrdered s)
    (j : ℕ) (hj : j + 1 < Multiset.card μ) :
    (appendRed Q Λ ν (tensorOfKLR Q Λ₀ ν (ψ j * e s))).1 =
      tensorOfKLR Q Λ ν (ψ j * e (appendRedLoading s)) := by
  let z := orderProjection Q Λ₀ ν
    (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν (ψ j * e s))
  change TensorProductAlgebra.mk Q Λ ν (appendRedStendhalValue Q Λ ν z) = _
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  rw [appendRedStendhalValue_val]
  have hz : z.1 = (StendhalAlgebraAllOrders.ψ j * StendhalAlgebraAllOrders.e s : A₀) := by
    change StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν (ψ j * e s) *
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν = _
    rw [map_mul, mul_assoc]
    change StendhalAlgebraAllOrders.ψ j *
      (StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν) = _
    rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ite_eq_left hs]
  rw [hz, map_mul, KLR.Corner.val_mul, appendRedAllOrders_ψ Q Λ ν j hj,
    appendRedAllOrders_e]
  have hfix : (appendRedAllOrders Q Λ ν (1 : A₀)).1 *
      StendhalAlgebraAllOrders.e (appendRedLoading s) =
      (StendhalAlgebraAllOrders.e (appendRedLoading s) : A) := by
    rw [← appendRedAllOrders_e Q Λ ν s, ← KLR.Corner.val_mul, ← map_mul, one_mul]
  rw [mul_assoc, hfix]
  change _ = StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψ j * e (appendRedLoading s)) *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  rw [map_mul, mul_assoc]
  change _ = StendhalAlgebraAllOrders.ψ j *
    (StendhalAlgebraAllOrders.e (appendRedLoading s) * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν)
  rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ite_eq_left ((appendRedLoading_ordered_iff s).2 hs)]

end Categorification.Stendhal
