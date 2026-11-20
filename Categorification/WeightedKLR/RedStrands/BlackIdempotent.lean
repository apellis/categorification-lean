/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Categorification.WeightedKLR.RedStrands.ParabolicLastStrand

/-!
# The black-strand idempotent of a tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6.
The idempotent `appendBlack 1` of `T^λ(i + ν)`, which cuts out the functor `E_i`, is the image
of the KLR idempotent `1_{ν,i}` of `R(μ + i)` (`appendBlack_one_eq_oneConcat`). Tensor product
algebras are transported along equalities of black weights by `castTensorProductAlgebra`.

## Main definitions

* `castTensorProductAlgebra`.

## Main results

* `castTensorProductAlgebra_mk`, `castKLR_castKLR`, `castKLR_oneConcat_eq`,
  `appendBlack_one_eq_oneConcat`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "S" => stendhalQ Q Λ

/-- The image of a KLR element in the tensor product algebra. -/
abbrev tensorOfKLR (ν : Multiset I) (z : KLRAlgebra k S (stendhalWeight ℓ ν)) :
    TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν z))

/-- Transport of tensor product algebras along an equality of black weights. -/
def castTensorProductAlgebra {ν ν' : Multiset I} (h : ν = ν') :
    TensorProductAlgebra k Q Λ ν ≃ₐ[k] TensorProductAlgebra k Q Λ ν' := by
  subst h; exact AlgEquiv.refl

theorem castTensorProductAlgebra_mk {ν ν' : Multiset I} (h : ν = ν')
    (z : KLRAlgebra k S (stendhalWeight ℓ ν)) :
    castTensorProductAlgebra Q Λ h (tensorOfKLR Q Λ ν z) =
      tensorOfKLR Q Λ ν' (castKLR S (congrArg (stendhalWeight ℓ) h) z) := by
  subst h; rfl

omit [DecidableEq I] in
theorem castKLR_castKLR {J : Type*} [DecidableEq J] {P : J → J → MvPolynomial (Fin 2) k}
    {a b c : Multiset J} (h₁ : a = b) (h₂ : b = c) (x : KLRAlgebra k P a) :
    castKLR P h₂ (castKLR P h₁ x) = castKLR P (h₁.trans h₂) x := by
  subst h₁ h₂; rfl

omit [DecidableEq I] in
/-- Two casts of `1_{μ,σ}` along equal weights agree. -/
theorem castKLR_oneConcat_eq {J : Type*} [DecidableEq J] {P : J → J → MvPolynomial (Fin 2) k}
    {μ₁ μ₂ σ τ : Multiset J} (h : μ₁ = μ₂) (h₁ : μ₁ + σ = τ) (h₂ : μ₂ + σ = τ) :
    castKLR P h₁ (oneConcat P μ₁ σ) = castKLR P h₂ (oneConcat P μ₂ σ) := by
  subst h; rfl

/-- **The black-strand idempotent** `appendBlack 1` of `T^λ(i + ν)` is the image of the KLR
idempotent `1_{μ,i}`, `μ` the weight of `ν`. -/
theorem appendBlack_one_eq_oneConcat (i : I) (ν : Multiset I) :
    appendBlack Q Λ i ν 1 = tensorOfKLR Q Λ ((Singleton.singleton i : Multiset I) + ν)
      (castKLR S (stendhalWeight_addBlack i ν)
        (oneConcat S (stendhalWeight ℓ ν) (Singleton.singleton (Sum.inl i)))) := by
  classical
  rw [← map_one (TensorProductAlgebra.mk Q Λ ν), appendBlack_mk]
  apply congrArg (TensorProductAlgebra.mk Q Λ _)
  apply Subtype.ext
  rw [appendBlackStendhal_val]
  change (appendBlackAllOrders Q Λ i ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν)).val =
    _ * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ _
  have h1 : StendhalAlgebraAllOrders.ofKLR k Q Λ _ (castKLR S (stendhalWeight_addBlack i ν)
      (oneConcat S (stendhalWeight ℓ ν) (Singleton.singleton (Sum.inl i)))) =
      (appendBlackAllOrders Q Λ i ν 1).val := by
    rw [← map_one (StendhalAlgebraAllOrders.ofKLR k Q Λ ν), appendBlackAllOrders_ofKLR_val,
      ← Algebra.TensorProduct.one_def, concat_one]
  have h2 : (1 : StendhalAlgebraAllOrders k Q Λ ν) = ∑ s, StendhalAlgebraAllOrders.e s := by
    rw [← map_one (StendhalAlgebraAllOrders.ofKLR k Q Λ ν), ← KLRAlgebra.sum_e, map_sum]; rfl
  rw [h1, h2, StendhalAlgebraAllOrders.redOrderedIdem, map_sum, map_sum, Corner.val_sum,
    Corner.val_sum, Finset.sum_mul]
  simp_rw [appendBlackAllOrders_e, StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr (Finset.ext fun s => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨appendBlackLoading_ordered i ν s, isRedOrdered_of_appendBlackLoading i ν s⟩

end Categorification.Stendhal
