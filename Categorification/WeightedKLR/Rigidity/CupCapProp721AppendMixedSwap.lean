/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedElem

/-!
# The crossing of two appended strands of different colours in `T̃^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the mixed crossing. Appending black strands `b`, then `a` to a diagram of
`T̃^λ` is the image of the KLR map `doubleLast` (`CupCap.appendBlackAllOrders_two_ofKLR`), so the
KLR intertwining relation of `doubleLast` gives, in `T̃^λ`,

`ψ · (append b, then a)(Z) = (append a, then b)(Z) · ψ`

for the crossing `ψ` of the two appended strands (`CupCap.orderProjection_ψ_mul_appendTwo`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite KLRAlgebra.AbsentColour.MixedCrossing

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

local notation "S" => stendhalQ Q Λ'

variable (Q) in
/-- The identification of `T̃^λ` at equal contents, on all orders of red strands. -/
def castAllOrders {μ μ' : Multiset I} (h : μ = μ') :
    StendhalAlgebraAllOrders k Q Λ' μ ≃ₐ[k] StendhalAlgebraAllOrders k Q Λ' μ' :=
  h ▸ AlgEquiv.refl

theorem castAllOrders_ofKLR {μ μ' : Multiset I} (h : μ = μ')
    (y : KLRAlgebra k S (stendhalWeight n μ)) :
    castAllOrders Q Λ' h (StendhalAlgebraAllOrders.ofKLR k Q Λ' μ y) =
      StendhalAlgebraAllOrders.ofKLR k Q Λ' μ' (castKLR S (congrArg (stendhalWeight n) h) y) := by
  subst h; rfl

theorem castPlusStendhal_val {μ μ' : Multiset I} (h : μ = μ') (z : StendhalAlgebra k Q Λ' μ) :
    (castPlusStendhal Q Λ' h z).val = castAllOrders Q Λ' h z.val := by
  subst h; rfl

omit [DecidableEq I] in
theorem stendhalWeight_cons' (a : I) (μ : Multiset I) :
    ({Sum.inl a} : Multiset (I ⊕ Fin n)) + stendhalWeight n μ =
      stendhalWeight n (({a} : Multiset I) + μ) :=
  (add_comm _ _).trans (stendhalWeight_addBlack a μ)

theorem cL_castKLR' {β β' : Multiset (I ⊕ Fin n)} (c : I ⊕ Fin n) (h : β = β')
    (y : KLRAlgebra k S β) :
    cL S c β' (castKLR S h y) = castKLR S (congrArg ({c} + ·) h) (cL S c β y) := by
  subst h; rfl

/-- Appending a black strand to a KLR diagram of `T̃^λ` is `cL`, cast. -/
theorem appendBlackAllOrders_ofKLR_cL (a : I) (μ : Multiset I)
    (u : KLRAlgebra k S (stendhalWeight n μ)) :
    (appendBlackAllOrders Q Λ' a μ (StendhalAlgebraAllOrders.ofKLR k Q Λ' μ u)).val =
      StendhalAlgebraAllOrders.ofKLR k Q Λ' _
        (castKLR S (stendhalWeight_cons' a μ) (cL S (Sum.inl a) (stendhalWeight n μ) u)) := by
  rw [appendBlackAllOrders_ofKLR_val, cL, castKLR_castKLR]

omit [DecidableEq I] in
theorem stendhalWeight_cons_two (a b : I) (μ : Multiset I) :
    ({Sum.inl a} : Multiset (I ⊕ Fin n)) + ({Sum.inl b} + stendhalWeight n μ) =
      stendhalWeight n (({a} : Multiset I) + (({b} : Multiset I) + μ)) :=
  (congrArg ({Sum.inl a} + ·) (stendhalWeight_cons' b μ)).trans
    (stendhalWeight_cons' a _)

/-- Appending black strands `b`, then `a` to a KLR diagram of `T̃^λ` is `doubleLast`, cast. -/
theorem appendBlackAllOrders_two_ofKLR (a b : I) (μ : Multiset I)
    (u : KLRAlgebra k S (stendhalWeight n μ)) :
    appendBlackValue Q Λ' a _ (appendBlackValue Q Λ' b μ
        (StendhalAlgebraAllOrders.ofKLR k Q Λ' μ u)) =
      StendhalAlgebraAllOrders.ofKLR k Q Λ' _ (castKLR S (stendhalWeight_cons_two a b μ)
        (doubleLast S (stendhalWeight n μ) (Sum.inl a) (Sum.inl b) u)) := by
  change (appendBlackAllOrders Q Λ' a _
    (appendBlackAllOrders Q Λ' b μ (StendhalAlgebraAllOrders.ofKLR k Q Λ' μ u)).val).val = _
  rw [appendBlackAllOrders_ofKLR_cL, appendBlackAllOrders_ofKLR_cL, cL_castKLR', castKLR_castKLR]
  rfl

/-- **The crossing of two appended strands intertwines the two orders of appending them**, on
all orders of red strands. -/
theorem ψ_mul_appendTwo_allOrders (a b : I) (μ : Multiset I)
    (z : StendhalAlgebraAllOrders k Q Λ' μ) :
    StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ)) *
        appendBlackValue Q Λ' a _ (appendBlackValue Q Λ' b μ z) =
      castAllOrders Q Λ' (mixedSwap μ a b)
          (appendBlackValue Q Λ' b _ (appendBlackValue Q Λ' a μ z)) *
        StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ)) := by
  obtain ⟨u, rfl⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ')
    (ν := μ) z
  rw [appendBlackAllOrders_two_ofKLR, appendBlackAllOrders_two_ofKLR, castAllOrders_ofKLR,
    StendhalAlgebraAllOrders.ψ, ← map_mul, ← map_mul, castKLR_castKLR]
  congr 1
  have key := congrArg (castKLR S (square (stendhalWeight n μ) (Sum.inl a) (Sum.inl b)))
    (doubleLast_intertwine S (stendhalWeight n μ) (Sum.inl b) (Sum.inl a) u)
  rw [map_mul, map_mul, castKLR_ψ, castKLR_castKLR, castKLR_rfl] at key
  have key' := congrArg (castKLR S (stendhalWeight_cons_two a b μ)) key
  rw [map_mul, map_mul, castKLR_ψ, castKLR_castKLR] at key'
  exact key'.symm

/-- **The crossing of two appended strands intertwines the two orders of appending them**, in
`T̃^λ`: `ψ · (append b, then a)(Z) = (append a, then b)(Z) · ψ`. -/
theorem orderProjection_ψ_mul_appendTwo (a b : I) (μ : Multiset I)
    (Z : StendhalAlgebra k Q Λ' μ) :
    orderProjection Q Λ' _ (StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ))) *
        appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ Z) =
      castPlusStendhal Q Λ' (mixedSwap μ a b)
          (appendBlackStendhal Q Λ' b _ (appendBlackStendhal Q Λ' a μ Z)) *
        orderProjection Q Λ' _
          (StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ))) := by
  apply Subtype.ext
  have hX := KLR.Corner.E_mul_val (appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ Z))
  have hX' := KLR.Corner.val_mul_E (appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ Z))
  have key := ψ_mul_appendTwo_allOrders Λ' a b μ Z.val
  change StendhalAlgebraAllOrders.ψ _ * _ *
      (appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ Z)).val =
    (castPlusStendhal Q Λ' (mixedSwap μ a b)
      (appendBlackStendhal Q Λ' b _ (appendBlackStendhal Q Λ' a μ Z))).val *
      (StendhalAlgebraAllOrders.ψ _ * _)
  rw [castPlusStendhal_val, mul_assoc, hX, ← hX', ← mul_assoc]
  change StendhalAlgebraAllOrders.ψ _ *
      appendBlackValue Q Λ' a _ (appendBlackValue Q Λ' b μ Z.val) * _ =
    castAllOrders Q Λ' (mixedSwap μ a b)
      (appendBlackValue Q Λ' b _ (appendBlackValue Q Λ' a μ Z.val)) * _
  rw [key, mul_assoc]

end Categorification.Stendhal.CupCap
