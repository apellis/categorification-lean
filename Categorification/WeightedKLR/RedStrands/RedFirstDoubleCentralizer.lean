/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstInjective
import Categorification.Algebra.SelfDualDoubleCentralizer

set_option backward.isDefEq.respectTransparency false

/-!
# The double centralizer property of the red-first projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Corollary 5.29: the projective-injective `P⁰ = T^λ e⁰` has the double centralizer property for
the actions of `T^λ` on the left and of `e⁰ T^λ e⁰ ≅ R^{∑ λ_r}` (Proposition 5.28) on the right.
The commutant of `T^λ` on `P⁰` is `e⁰ T^λ e⁰` acting on the right; the content of the corollary
is the other half: every `e⁰ T^λ e⁰`-linear endomorphism of `P⁰` is left multiplication by a
unique element of `T^λ`.

Webster deduces this from V. Mazorchuk, C. Stroppel, J. Reine Angew. Math. 616 (2008),
Corollary 2.6, which rests on Ringel duality for standardly stratified algebras. Here the
corollary is proved from the self-duality of `P⁰` (Theorem 5.27, (3) ⇒ (1)) under the route
hypothesis `HasCornerCopresentation e⁰`: `T^λ` embeds into a sum of copies of `P⁰` with cokernel
having no nonzero submodule killed by `e⁰` (dominant dimension at least two). Uniqueness holds
unconditionally, by Lemma 5.23 (`exists_mul_redFirstIdem_ne_zero`).

## Main results

* `eq_zero_of_mul_redFirstProjective`: `T^λ` acts faithfully on `P⁰`.
* `existsUnique_eq_mul_left_redFirst`: **Corollary 5.29**, under `HasCornerCopresentation e⁰`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KL3.Diagram

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

include hR hQs in
/-- `T^λ` acts faithfully on `P⁰ = T^λ e⁰` (Webster, arXiv:1309.3796v2, Lemma 5.23): if
`z c = 0` for every `c ∈ T^λ e⁰`, then `z = 0`. -/
theorem eq_zero_of_mul_redFirstProjective {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (z : TensorProductAlgebra k QL Λ ν)
    (hz : ∀ c, c * redFirstIdem QL Λ ν = c → z * c = 0) : z = 0 := by
  have hcomp := (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem
    (k := k) QL Λ ν).complete
  rw [← mul_one z, ← hcomp, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_contra hs
  have hidem := (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem
    (k := k) QL Λ ν).idem s
  obtain ⟨c, hc, hzc⟩ := exists_mul_redFirstIdem_ne_zero hR hQs (baseCrossing_std hR hQs) Λ ν
    s.1 s.2 (z * TensorProductAlgebra.boundaryIdem QL Λ ν s)
    (by rw [mul_assoc]; exact congrArg _ hidem.eq) hs
  exact hzc (by rw [mul_assoc, hz _ (by rw [mul_assoc, hc])])

include hR hQs in
/-- **Webster, arXiv:1309.3796v2, Corollary 5.29**, under the route hypothesis
`HasCornerCopresentation e⁰` (an embedding of `T^λ` into a sum of copies of `P⁰` whose cokernel
has no nonzero submodule killed by `e⁰`): every endomorphism of `P⁰ = T^λ e⁰` commuting with the
right action of `e⁰ T^λ e⁰` is left multiplication by a unique element of `T^λ`. -/
theorem existsUnique_eq_mul_left_redFirst {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (hK : HasCornerCopresentation (redFirstIdem QL Λ ν))
    (f : TensorProductAlgebra k QL Λ ν →ₗ[k] TensorProductAlgebra k QL Λ ν)
    (hfe : ∀ x, x * redFirstIdem QL Λ ν = x → f x * redFirstIdem QL Λ ν = f x)
    (hfb : ∀ b x, x * redFirstIdem QL Λ ν = x →
      f (x * (redFirstIdem QL Λ ν * b * redFirstIdem QL Λ ν)) =
        f x * (redFirstIdem QL Λ ν * b * redFirstIdem QL Λ ν)) :
    ∃! a, ∀ x, x * redFirstIdem QL Λ ν = x → f x = a * x := by
  have : FiniteDimensional k (TensorProductAlgebra k QL Λ ν) :=
    tensorProductAlgebra_finite Λ ν hR
  obtain ⟨τ, hτ⟩ := redFirstIdem_pairing_nondegenerate hR hQs Λ ν
  obtain ⟨a, ha⟩ := exists_eq_mul_left_of_hasCornerCopresentation (τ := τ) hτ
    (finrank_leftCorner_redFirstIdem Λ ν) (isIdempotentElem_redFirstIdem QL Λ ν).eq hK
    (tensorFlipEquiv QL Λ ν) (fun x y => tensorFlip_mul x y) (fun x => tensorFlip_tensorFlip x)
    (tensorFlip_redFirstIdem QL Λ ν) f hfe hfb
  refine ⟨a, ha, fun a' ha' => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_mul_redFirstProjective hR hQs Λ ν _ fun c hc => ?_
  rw [sub_mul, ← ha' c hc, ← ha c hc, sub_self]

end Categorification.Stendhal
