/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineCover
import Categorification.WeightedKLR.RedStrands.OrderProjection

/-! # The affine KLR projection onto the ordered violating quotient -/

noncomputable section
namespace Categorification.Stendhal

open KLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "Aff" => KLRAlgebra k (affineCoverQ Q Λ) μ
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- The affine KLR cover, followed by projection to ordered red labels and
the quotient by the violating ideal. -/
def affineTensorProjection : Aff →ₐ[k] T :=
  (TensorProductAlgebra.mk Q Λ ν).comp ((orderProjection Q Λ ν).comp (affineCover Q Λ ν))

local notation "π" => affineTensorProjection (Q := Q) Λ ν

theorem affineTensorProjection_surjective : Function.Surjective π :=
  (show Function.Surjective (TensorProductAlgebra.mk Q Λ ν) from RingCon.mkₐ_surjective _).comp ((orderProjection_surjective Q Λ ν).comp
    (affineCover_surjective Q Λ ν))

end Categorification.Stendhal
