/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstBaseCrossing
import Categorification.WeightedKLR.RedStrands.RedFirstTrace
import Categorification.WeightedKLR.RedStrands.TensorIdempotentPieces
import Categorification.WeightedKLR.RedStrands.AppendStrandReflection
import Categorification.Algebra.SelfDualInjective

set_option backward.isDefEq.respectTransparency false

/-!
# The red-first projective is injective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Theorem 5.27,
implication (3) ⇒ (1): the projective `P⁰ = T^λ e⁰` is self-dual, through the pairing
`(a, b) ↦ τ(a b)` built from the symmetric Frobenius trace of the red-first corner
`e⁰ T^λ e⁰ ≅ R^{∑ λ_r}` (Proposition 5.28), so `P⁰` and all its summands are injective.

The library works with the left `T^λ`-module `T^λ e⁰`; the right module `e⁰ T^λ` is its image
under the horizontal reflection `tensorFlip`, which fixes `e⁰`.

We work for Rouquier parameters `Q`, where the base
crossing of Lemma 5.23 is proved (`baseCrossing_of_rouquier`).

## Main results

* `finrank_leftCorner_redFirstIdem`: `e⁰ T^λ` and `T^λ e⁰` have the same dimension.
* `redFirstIdem_pairing_nondegenerate`: the pairing `e⁰ T^λ × T^λ e⁰ → k` is nondegenerate on
  the left.
* `injective_redFirstProjective`: **Theorem 5.27 (3) ⇒ (1)** for `P⁰` itself.
* `injective_of_isSummand_redFirstProjective`: every summand of `P⁰` is injective.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KL3.Diagram
open _root_.Module (finrank)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
  (hQs : KLRSymm Q)

local notation "QL" => Q

section Flip

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The horizontal reflection fixes `e⁰`. -/
theorem tensorFlip_redFirstIdem {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) :
    tensorFlip (redFirstIdem Q Λ ν) = redFirstIdem Q Λ ν := by
  unfold redFirstIdem redFirstStendhalIdem
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => tensorFlip_mk_e _ _

/-- The horizontal reflection as a linear involution. -/
def tensorFlipEquiv {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) :
    TensorProductAlgebra k Q Λ ν ≃ₗ[k] TensorProductAlgebra k Q Λ ν :=
  LinearEquiv.ofInvolutive tensorFlip fun z => tensorFlip_tensorFlip z

end Flip

/-- `e⁰ T^λ` and `T^λ e⁰` have the same dimension, since the horizontal reflection exchanges
them. -/
theorem finrank_leftCorner_redFirstIdem {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) :
    finrank k (leftCorner (k := k) (redFirstIdem QL Λ ν)) =
      finrank k (rightCorner (k := k) (redFirstIdem QL Λ ν)) :=
  finrank_leftCorner_eq_rightCorner (tensorFlipEquiv QL Λ ν)
    (fun x y => tensorFlip_mul x y) (fun x => tensorFlip_tensorFlip x)
    (tensorFlip_redFirstIdem QL Λ ν)

include hR hQs in
/-- **Nondegeneracy of the pairing on `P⁰`** (Webster, arXiv:1309.3796v2, proof of
Theorem 5.27): with the transported trace `τ`, every nonzero `a ∈ e⁰ T^λ` has `b ∈ T^λ e⁰`
with `τ(a b) ≠ 0`. -/
theorem redFirstIdem_pairing_nondegenerate {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) :
    ∃ τ : TensorProductAlgebra k QL Λ ν →ₗ[k] k, ∀ a, redFirstIdem QL Λ ν * a = a → a ≠ 0 →
      ∃ b, b * redFirstIdem QL Λ ν = b ∧ τ (a * b) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_redFirstTrace QL hR ν Λ
  refine ⟨τ, fun a ha ha0 => ?_⟩
  set e := redFirstIdem QL Λ ν
  have hcomp := (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem
    (k := k) QL Λ ν).complete
  obtain ⟨s, hs⟩ : ∃ s : TensorProductAlgebra.OrderedLoading (ℓ := ℓ + 1) ν,
      a * TensorProductAlgebra.boundaryIdem QL Λ ν s ≠ 0 := by
    by_contra! h
    apply ha0
    rw [← mul_one a, ← hcomp, Finset.mul_sum]
    exact Finset.sum_eq_zero fun s _ => h s
  have hidem := (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem
    (k := k) QL Λ ν).idem s
  set es := TensorProductAlgebra.boundaryIdem QL Λ ν s with hes
  obtain ⟨c, hc, hac⟩ := exists_mul_redFirstIdem_ne_zero hR hQs (baseCrossing_of_rouquier hR hQs) Λ ν
    s.1 s.2 (a * es) (by rw [mul_assoc]; exact congrArg _ hidem.eq) hs
  obtain ⟨y, hy1, hy2, hzy⟩ := hτ (a * es * c)
    (by rw [← mul_assoc, ← mul_assoc, ha]) (by rw [mul_assoc, hc]) hac
  refine ⟨es * c * y, by rw [mul_assoc, hy2], ?_⟩
  simpa only [mul_assoc] using hzy

include hR hQs in
/-- **Webster, arXiv:1309.3796v2, Theorem 5.27, (3) ⇒ (1)**, for `P⁰`: the red-first projective
`T^λ e⁰` is an injective `T^λ`-module. -/
theorem injective_redFirstProjective {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) :
    Module.Injective (TensorProductAlgebra k QL Λ ν) (lIdeal (redFirstIdem QL Λ ν)) := by
  have : FiniteDimensional k (TensorProductAlgebra k QL Λ ν) :=
    tensorProductAlgebra_finite Λ ν hR
  obtain ⟨τ, hτ⟩ := redFirstIdem_pairing_nondegenerate hR hQs Λ ν
  exact injective_lIdeal_of_pairing (τ := τ) hτ (finrank_leftCorner_redFirstIdem Λ ν)

include hR hQs in
/-- **Webster, arXiv:1309.3796v2, Theorem 5.27, (3) ⇒ (1)**: every summand of the red-first
projective `T^λ e⁰` (a module `N` with maps `N → P⁰ → N` composing to the identity) is injective.
-/
theorem injective_of_isSummand_redFirstProjective {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) {N : Type} [AddCommGroup N] [Module (TensorProductAlgebra k QL Λ ν) N]
    (i : N →ₗ[TensorProductAlgebra k QL Λ ν] lIdeal (redFirstIdem QL Λ ν))
    (r : lIdeal (redFirstIdem QL Λ ν) →ₗ[TensorProductAlgebra k QL Λ ν] N)
    (hri : ∀ x, r (i x) = x) :
    Module.Injective (TensorProductAlgebra k QL Λ ν) N :=
  (Module.Baer.of_retract i r hri
    (_root_.Module.Baer.of_injective (injective_redFirstProjective hR hQs Λ ν))).injective

end Categorification.Stendhal
