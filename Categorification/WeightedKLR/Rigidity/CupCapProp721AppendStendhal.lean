/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721WindowIdem
import Categorification.WeightedKLR.RedStrands.ParabolicLastStrand

/-!
# Appending a black strand to the diagrams at the maximum in `T̃^{λ⁺}`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The map `T̃^{λ⁺}_{ν + ν₀} → T̃^{λ⁺}_{({i} + ν) + ν₀}` appending a black strand of
colour `i` at the right (`Stendhal.appendBlackStendhal`, transported to the weight of the cap
bimodule at the black weight `{i} + ν`, `CupCap.appendBlackPlus`) is the image of the KLR map
`CupCap.appendPlus` (`CupCap.appendBlackPlus_botMap`). Hence, for `j < ℓ`, appending the strand
to the diagrams at the maximum of the model at `ν` gives the diagrams at the maximum of the model
at `{i} + ν`, cut on the left by the window idempotents of the appended loadings
(`CupCap.appendBlackPlus_midBot`).

## Main definitions

* `CupCap.castPlusStendhal`: `T̃^{λ⁺}` at two equal black weights.
* `CupCap.appendBlackPlus`: appending a black strand to `T̃^{λ⁺}`.

## Main results

* `CupCap.appendBlackPlus_botMap`, `CupCap.appendBlackPlus_midBot`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ⁺" => plusLabels Λ Λc j hj

section Cast

variable {n : ℕ} (Λ' : Fin n → I →₀ ℕ)

/-- `T̃^{λ}` at two equal black weights. -/
def castPlusStendhal {μ μ' : Multiset I} (h : μ = μ') :
    StendhalAlgebra k Q Λ' μ ≃ₐ[k] StendhalAlgebra k Q Λ' μ' :=
  h ▸ AlgEquiv.refl

theorem castPlusStendhal_orderProjection {μ μ' : Multiset I} (h : μ = μ')
    (y : KLRAlgebra k (stendhalQ Q Λ') (stendhalWeight n μ)) :
    castPlusStendhal Q Λ' h (orderProjection Q Λ' μ (StendhalAlgebraAllOrders.ofKLR k Q Λ' μ y)) =
      orderProjection Q Λ' μ' (StendhalAlgebraAllOrders.ofKLR k Q Λ' μ'
        (castKLR (stendhalQ Q Λ') (congrArg (stendhalWeight n) h) y)) := by
  subst h; rfl

end Cast

omit [DecidableEq I] in
theorem plusWeight_assoc : (Singleton.singleton i : Multiset I) + (ν + ν₀) = νᵢ + ν₀ :=
  (add_assoc _ _ _).symm

/-- **Appending a black strand of colour `i` at the right** of a diagram of `T̃^{λ⁺}`, with the
target at the black weight `({i} + ν) + ν₀` of the cap bimodule at `{i} + ν`. -/
def appendBlackPlus :
    StendhalAlgebra k Q Λ⁺ (ν + ν₀) →ₙₐ[k] StendhalAlgebra k Q Λ⁺ (νᵢ + ν₀) :=
  (castPlusStendhal Q Λ⁺ (plusWeight_assoc ν ν₀ i)).toAlgHom.toNonUnitalAlgHom.comp
    (appendBlackStendhal Q Λ⁺ i (ν + ν₀))

/-- Appending the strand in `T̃^{λ⁺}` is the image of appending it to KLR diagrams. -/
theorem appendBlackPlus_botMap
    (y : KLRAlgebra k (stendhalQ Q Λ⁺) (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    appendBlackPlus Q Λ Λc j hj ν ν₀ i (botMap k Q Λ Λc j hj ν ν₀ y) =
      botMap k Q Λ Λc j hj νᵢ ν₀ (appendPlus Q Λ Λc j hj ν ν₀ i y) := by
  have h1 : appendBlackStendhal Q Λ⁺ i (ν + ν₀) (botMap k Q Λ Λc j hj ν ν₀ y) =
      orderProjection Q Λ⁺ _ (appendBlackAllOrders Q Λ⁺ i (ν + ν₀)
        (StendhalAlgebraAllOrders.ofKLR k Q Λ⁺ (ν + ν₀) y)).val :=
    appendBlackStendhal_orderProjection Q Λ⁺ id i (ν + ν₀) _
  have hc : concat (stendhalQ Q Λ⁺) (stendhalWeight (ℓ + 2) (ν + ν₀))
      {Sum.inl i} (y ⊗ₜ 1) = ((blockL _ _).hom (stendhalQ Q Λ⁺) y).val := by
    rw [concat_tmul, map_one, Corner.val_one, Corner.val_mul_E]
  change castPlusStendhal Q Λ⁺ (plusWeight_assoc ν ν₀ i)
    (appendBlackStendhal Q Λ⁺ i (ν + ν₀) (botMap k Q Λ Λc j hj ν ν₀ y)) = _
  rw [h1, appendBlackAllOrders_ofKLR_val, hc, castPlusStendhal_orderProjection, castKLR_castKLR,
    appendPlus_apply]
  rfl

/-- **Appending a black strand to the diagrams at the maximum** (arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21), for `j < ℓ`: in `T̃^{λ⁺}`, appending a black strand `i` at the right of the
image of `midMapKLR x` gives the image of `midMapKLR x` at the black weight `{i} + ν`, multiplied
on the left by the window idempotents of the appended loadings. -/
theorem appendBlackPlus_midBot (h : j < ℓ)
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    appendBlackPlus Q Λ Λc j hj ν ν₀ i (midBot j hj Q Λ Λc ν ν₀ x) =
      botMap k Q Λ Λc j hj νᵢ ν₀
          (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc νᵢ ν₀ (appendBlackLoading i ν s)) *
        midBot j hj Q Λ Λc νᵢ ν₀ x := by
  rw [midBot_apply, midBot_apply, appendBlackPlus_botMap, appendPlus_midMapKLR_eq_mul _ _ _ _ _ _ _
    _ h, map_mul]

end Categorification.Stendhal.CupCap
