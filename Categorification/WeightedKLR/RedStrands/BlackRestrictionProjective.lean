/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverRestrictionKernel
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverTower
import Categorification.WeightedKLR.RedStrands.RestrictionProjectiveDescent
import Categorification.KLR.CyclotomicRestrictionProjective

/-!
# Projectivity of right black restriction

Webster, arXiv:1309.3796v2, §4.6, Theorem 4.31. The regular restriction
cut is a quotient of the corresponding ordinary cyclotomic cut. On
restriction the red-dot and red-order relations generate precisely the
submodule coming from the lower cover ideal.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (i : I) (ν : Multiset I) (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "T'" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "μ" => stendhalWeight ℓ ν
local notation "ci" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "B" => CycKLR k S p ((Singleton.singleton ci : Multiset _) + μ)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C

include C hQ in
/-- The right black cut of the upper regular module is projective over the
lower tensor product algebra for every black content. -/
theorem projective_blackRes_regular :
    Module.Projective T (BlackRes (Q := Q) (Λ := Λ) i ν T') := by
  let hS := isRouquierQ_cyclotomicCoverQ C Λ Q hQ
  let : Module.Projective (CycKLR k S p μ) (AbsentColour.Res S ci p μ B) :=
    CycKLR.projective_res μ ci p hS.klrSymm hS.polyInY_leading
      (show (1 : Polynomial k).Monic from Polynomial.monic_one) B
  apply projective_of_quotient_kernel (π).toRingHom (cyclotomicCoverToTensor_surjective Λ ν C)
    (cyclotomicCoverResMap (Q := Q) Λ ν C i) (cyclotomicCoverResMap_surjective Λ ν C i)
  have h := cyclotomicCoverResMap_ker_le (Q := Q) Λ ν C i hQ
  rw [← cyclotomicCoverToTensor_ker (Q := Q) Λ ν C] at h
  simpa only [idealActionSpan, TwoSidedIdeal.mem_ker] using h

include C hQ in
/-- Right black restriction preserves finite projectives, as required for
the projective action in Webster, arXiv:1309.3796v2, Theorem 4.31. -/
theorem projective_blackRes (M : Type*) [AddCommGroup M] [Module k M]
    [Module T' M] [IsScalarTower k T' M] [Module.Finite T' M] [Module.Projective T' M] :
    Module.Projective T (BlackRes (Q := Q) (Λ := Λ) i ν M) :=
  projective_blackRes_of_regular i ν M (projective_blackRes_regular i ν C hQ)

end Categorification.Stendhal
