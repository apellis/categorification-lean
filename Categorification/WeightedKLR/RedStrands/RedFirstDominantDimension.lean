/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstCopresentation
import Categorification.WeightedKLR.RedStrands.RedFirstBaseCrossingCokernel
import Categorification.WeightedKLR.RedStrands.LastIndStandardCornerFaithful

set_option backward.isDefEq.respectTransparency false

/-!
# The double centralizer property of the red-first projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Corollary 5.32 (v2: Corollary 5.29). The dominant dimension of `T^λ` with respect to the
self-dual projective `P⁰ = T^λ e⁰` is at least two: `T^λ` embeds into a sum of copies of `P⁰`
with cokernel that has no nonzero submodule killed by `e⁰` (`hasCornerCopresentation_redFirstIdem`).
Hence `T^λ` is the double centralizer of `P⁰`: every endomorphism of `P⁰` commuting with the
right action of `e⁰ T^λ e⁰` is left multiplication by a unique element of `T^λ`
(`existsUnique_eq_mul_left_redFirst`).

The base crossing `c = e(s, i, λ_ℓ) G` of Lemma 5.25 (v2: Lemma 5.23) at a red-first loading `s`
has cokernel `S(₂Fᵢ N)`, which has no nonzero element killed by `e⁰ T^λ`; since `T^λ` is
finite-dimensional and `τ` pairs `e⁰ T^λ` and `T^λ e⁰` perfectly, this cokernel embeds into a
sum of copies of `P⁰` (`exactCrossPair_base_of_rouquier`). Chains of these crossings assemble into the
copresentation (`hasCornerCopresentation_redFirstIdem_of_exactBaseCrossing`).

## Main results

* `exactBaseCrossing_of_rouquier`: the base crossings at red-first loadings are exact.
* `hasCornerCopresentation_redFirstIdem`: dominant dimension at least two.
* `existsUnique_eq_mul_left_redFirst`: **Corollary 5.32** (v2: Corollary 5.29).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra KL3.Diagram

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
  (hQs : KLRSymm Q)

local notation "QL" => Q

include hR hQs in
/-- **The base crossing at a red-first loading is exact** (Webster, arXiv:1309.3796v3, proof of
Corollary 5.32): the crossing `(s, i, λ_ℓ) ⟶ (s, λ_ℓ, i)` of Lemma 5.25 has a cokernel embedding
into a sum of copies of `P⁰`. -/
theorem exactCrossPair_base_of_rouquier {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)
    (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) (hsf : IsRedFirst s) :
    ExactCrossPair QL Λ ({i} + (θ + 0)) (appendRedLoading (appendBlackLoading i (θ + 0) s))
      (appendBlackLoading i (θ + 0) (appendRedLoading s)) := by
  have hsrc : IsRedOrdered (appendRedLoading (appendBlackLoading i (θ + 0) s)) :=
    (appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered i (θ + 0) s hs)
  have htgt : IsRedOrdered (appendBlackLoading i (θ + 0) (appendRedLoading s)) :=
    appendBlackLoading_ordered i (θ + 0) _ ((appendRedLoading_ordered_iff _).2 hs)
  set G := firstG (stendhalQ QL Λ) (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
    (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
      (stendhalWeight 1 (0 : Multiset I))) (Sum.inl i : I ⊕ Fin (ℓ + 1)) with hG
  have := finiteDimensional_redFactorModule _ hR Λ θ s hs
  have hδ := firstIndDeltaInjective_of_rouquier (Λ := Λ) hR hQs i θ 0 (redFactorModule QL Λ θ s hs).carrier
  have : FiniteDimensional k (TensorProductAlgebra k QL Λ ({i} + (θ + 0))) :=
    tensorProductAlgebra_finite Λ _ hR
  obtain ⟨τ, hτ⟩ := redFirstIdem_pairing_nondegenerate hR hQs Λ ({i} + (θ + 0))
  have hq := isCornerFaithfulQuot_baseCrossing QL Λ i θ s hs hQs hδ
    (eq_zero_of_redFirstIdem_mul hR hQs Λ _)
    (eq_zero_of_redFirstIdem_smul_lastIndStandardT hR hQs Λ i θ s hs hsf) hsrc
  obtain ⟨n, g, -, hg⟩ := exists_isExactMulRight_of_isCornerFaithfulQuot hτ
    (finrank_leftCorner_redFirstIdem Λ _) (isIdempotentElem_redFirstIdem QL Λ _).eq hq
  refine ⟨hsrc, htgt, redLoadingIdem QL Λ _ _ hsrc * firstIndAffine QL Λ i θ 0 G, ?_, ?_, ?_,
    n, g, hg⟩
  · intro x hx h0
    refine redCross_eq_zero _ Λ i θ s hs hQs hδ x ?_ ?_
    · rw [redCrossIdem_eq]
      exact hx
    · calc x * firstIndAffine QL Λ i θ 0 G
          = x * redLoadingIdem QL Λ _ _ hsrc * firstIndAffine QL Λ i θ 0 G := by rw [hx]
        _ = 0 := by rw [mul_assoc]; exact h0
  · rw [redLoadingIdem_mul_firstG QL Λ i θ s hsrc htgt, mul_assoc,
      (isIdempotentElem_redLoadingIdem QL Λ _ _ htgt).eq]
  · rw [← mul_assoc, (isIdempotentElem_redLoadingIdem QL Λ _ _ hsrc).eq]

include hR hQs in
/-- The base crossings at red-first loadings are exact, for Rouquier parameters. -/
theorem exactBaseCrossing_of_rouquier : ExactBaseCrossing QL := by
  intro ℓ Λ i β u hu huf
  have key : ∀ (u : Seq (stendhalWeight ℓ (β + 0))), IsRedOrdered u → IsRedFirst u →
      ExactCrossPair QL Λ ({i} + (β + 0)) (appendRedLoading (appendBlackLoading i (β + 0) u))
        (appendBlackLoading i (β + 0) (appendRedLoading u)) :=
    fun u hu huf => exactCrossPair_base_of_rouquier hR hQs Λ i β u hu huf
  rw [add_zero] at key
  exact key u hu huf

include hR hQs in
/-- **Dominant dimension at least two** (Webster, arXiv:1309.3796v3, Corollary 5.32; v2:
Corollary 5.29): `T^λ` embeds into a sum of copies of `P⁰ = T^λ e⁰` with a cokernel that has no
nonzero submodule killed by `e⁰`. -/
theorem hasCornerCopresentation_redFirstIdem {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) : HasCornerCopresentation (redFirstIdem QL Λ ν) :=
  hasCornerCopresentation_redFirstIdem_of_exactBaseCrossing hR hQs (exactBaseCrossing_of_rouquier hR hQs)
    Λ ν

include hR hQs in
/-- **Webster, arXiv:1309.3796v3, Corollary 5.32** (v2: Corollary 5.29): every endomorphism of
`P⁰ = T^λ e⁰` commuting with the right action of `e⁰ T^λ e⁰` is left multiplication by a unique
element of `T^λ`. -/
theorem existsUnique_eq_mul_left_redFirst {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
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
    (finrank_leftCorner_redFirstIdem Λ ν) (isIdempotentElem_redFirstIdem QL Λ ν).eq
    (hasCornerCopresentation_redFirstIdem hR hQs Λ ν)
    (tensorFlipEquiv QL Λ ν) (fun x y => tensorFlip_mul x y) (fun x => tensorFlip_tensorFlip x)
    (tensorFlip_redFirstIdem QL Λ ν) f hfe hfb
  refine ⟨a, ha, fun a' ha' => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_mul_redFirstProjective hR hQs Λ ν _ fun c hc => ?_
  rw [sub_mul, ← ha' c hc, ← ha c hc, sub_self]

end Categorification.Stendhal
