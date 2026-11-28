/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCut
import Categorification.WeightedKLR.Rigidity.CupCapMidGenerators
import Categorification.WeightedKLR.Rigidity.CupCapMidSlides
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeTower

/-!
# The dot on the appended strand at the maximum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with the dot, for a cap not at the
right end (`j < ℓ`). Since `j < ℓ`, the window at the maximum lies left of the last strand, so
the dot on the last strand of `λ`, placed above the maximum, is the dot `X` on the last strand of
`λ⁺` cut by the unit of the diagrams at the maximum (`CupCap.botMap_midDot_last`). The dot `X`
commutes with the window idempotents and with every diagram with a black strand appended
(`CupCap.commute_lastDotPlus_appendBlackPlus`).

## Main results

* `CupCap.botMap_midDot_last`, `CupCap.commute_lastDotPlus_appendBlackPlus`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I} (ν : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "ρᵢ" => stendhalWeight (ℓ + 2) (νᵢ + ν₀)

omit [DecidableEq I] in
theorem card_plusAppend_pos : 0 < Multiset.card ρᵢ := by
  simp [stendhalWeight]

omit [DecidableEq I] in
theorem card_appendLoading_pos : 0 < Multiset.card (stendhalWeight ℓ νᵢ) := by
  simp [stendhalWeight]

variable (ℓ ν₀) in
/-- The last strand of `λ⁺` at the black weight `({i} + ν) + ν₀`. -/
def lastPlus : Fin (Multiset.card ρᵢ) :=
  ⟨Multiset.card ρᵢ - 1, Nat.sub_lt (card_plusAppend_pos (ν₀ := ν₀) ν i) Nat.one_pos⟩

variable (ℓ) in
/-- The last strand of `λ` at the black weight `{i} + ν`. -/
def lastLoading : Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
  ⟨Multiset.card (stendhalWeight ℓ νᵢ) - 1,
    Nat.sub_lt (card_appendLoading_pos (ℓ := ℓ) ν i) Nat.one_pos⟩

variable (k Q Λ Λc j hj ν₀) in
/-- The dot `X` on the last strand of `λ⁺` in `T̃^{λ⁺}` at the black weight `({i} + ν) + ν₀`. -/
def lastDotPlus : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀) :=
  botMap k Q Λ Λc j hj νᵢ ν₀ (KLRAlgebra.x (lastPlus ℓ ν₀ ν i))

/-- **The dot on the last strand of `λ`, above the maximum**, for `j < ℓ`: it is the dot on the
last strand of `λ⁺`, cut by the unit of the diagrams at the maximum. -/
theorem botMap_midDot_last (h : j < ℓ) :
    botMap k Q Λ Λc j hj νᵢ ν₀ (midDot j hj Q Λ Λc νᵢ ν₀ (lastLoading ℓ ν i)) =
      lastDotPlus k Q Λ Λc j hj ν₀ ν i * midStendhal j hj Q Λ Λc νᵢ ν₀ 1 := by
  have hpos := card_appendLoading_pos (ℓ := ℓ) ν i
  have hpos' := card_plusAppend_pos (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hd : ∀ s : Seq (stendhalWeight ℓ νᵢ),
      dotPos (j := j) (hj := hj) (ν₀ := ν₀) ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩
        (lastLoading ℓ ν i) = lastPlus ℓ ν₀ ν i := fun s => Fin.ext (by
    have hc := card_plus' (I := I) (ℓ := ℓ) (ν := νᵢ) (ν₀ := ν₀)
    have hm := midPos_lt j (s := s) h
    rw [dotPos_val']
    change (if Multiset.card (stendhalWeight ℓ νᵢ) - 1 < midPos j s then _ else _) =
      Multiset.card ρᵢ - 1
    rw [ite_eq_right_iff.mpr (by omega)]
    change Multiset.card (stendhalWeight ℓ νᵢ) - 1 + _ = _
    omega)
  rw [midDot, Finset.sum_congr rfl fun s _ => by rw [hd s], ← Finset.mul_sum, map_mul,
    midStendhal_one_eq_botMap]
  rfl

/-- The dot `X` commutes with the unit of the diagrams at the maximum. -/
theorem commute_lastDotPlus_midStendhal_one :
    Commute (lastDotPlus k Q Λ Λc j hj ν₀ ν i) (midStendhal j hj Q Λ Λc νᵢ ν₀ 1) := by
  rw [midStendhal_one_eq_botMap]
  exact ((Commute.sum_right _ _ _ fun _ _ => commute_x_eSum _ _).map _)

/-- The dot `X` commutes with the idempotent `e'` of the appended loadings. -/
theorem commute_lastDotPlus_appendIdemPlus :
    Commute (lastDotPlus k Q Λ Λc j hj ν₀ ν i) (appendIdemPlus Q Λ Λc j hj ν ν₀ i) :=
  ((Commute.sum_right _ _ _ fun _ _ => commute_x_eSum _ _).map _)

/-- The dot `X` is the dot on the appended strand of `T̃^{λ⁺}`, cast to `({i} + ν) + ν₀`. -/
theorem lastDotPlus_eq :
    lastDotPlus k Q Λ Λc j hj ν₀ ν i =
      castPlusStendhal Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
        (orderProjection Q (plusLabels Λ Λc j hj) _
          (StendhalAlgebraAllOrders.newDot Q (plusLabels Λ Λc j hj) i (ν + ν₀))) := by
  change _ = castPlusStendhal Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
    (orderProjection Q (plusLabels Λ Λc j hj) _ (StendhalAlgebraAllOrders.ofKLR k Q _ _
      (KLRAlgebra.x _)))
  rw [castPlusStendhal_orderProjection, KLRAlgebra.castKLR_x]
  refine congrArg (fun a => orderProjection Q (plusLabels Λ Λc j hj) _
    (StendhalAlgebraAllOrders.ofKLR k Q _ _ (KLRAlgebra.x a))) (Fin.ext ?_)
  have h1 := congrArg Multiset.card (stendhalWeight_addBlack (ℓ := ℓ + 2) i (ν + ν₀))
  rw [Multiset.card_add, Multiset.card_singleton] at h1
  have h2 := congrArg Multiset.card
    (congrArg (stendhalWeight (ℓ + 2)) (plusWeight_assoc ν ν₀ i))
  change Multiset.card ρᵢ - 1 = Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
  omega

/-- In `T̃^λ`, the dot on the appended strand commutes with every diagram with a black strand
appended. -/
theorem commute_newDot_appendBlackStendhal {n : ℕ} (Λ' : Fin n → I →₀ ℕ) (μ : Multiset I)
    (W : StendhalAlgebra k Q Λ' μ) :
    Commute (orderProjection Q Λ' _ (StendhalAlgebraAllOrders.newDot Q Λ' i μ))
      (appendBlackStendhal Q Λ' i μ W) := by
  apply Subtype.ext
  have hc := (StendhalAlgebraAllOrders.newDot_commute Q Λ' i μ W.val).eq
  have hP := (redOrderedIdem_commute Q Λ'
    ((Singleton.singleton i : Multiset I) + μ) (StendhalAlgebraAllOrders.newDot Q Λ' i μ)).eq
  have hl := KLR.Corner.E_mul_val (appendBlackStendhal Q Λ' i μ W)
  have hr := KLR.Corner.val_mul_E (appendBlackStendhal Q Λ' i μ W)
  change StendhalAlgebraAllOrders.newDot Q Λ' i μ * _ * (appendBlackStendhal Q Λ' i μ W).val =
    (appendBlackStendhal Q Λ' i μ W).val * (StendhalAlgebraAllOrders.newDot Q Λ' i μ * _)
  rw [mul_assoc, hl, ← hP, ← mul_assoc, hr]
  exact hc

/-- **The dot `X` commutes with every diagram with a black strand appended.** -/
theorem commute_lastDotPlus_appendBlackPlus (W : StendhalAlgebra k Q (plusLabels Λ Λc j hj)
    (ν + ν₀)) :
    Commute (lastDotPlus k Q Λ Λc j hj ν₀ ν i) (appendBlackPlus Q Λ Λc j hj ν ν₀ i W) := by
  rw [lastDotPlus_eq]
  exact (commute_newDot_appendBlackStendhal i _ _ W).map _

end Categorification.Stendhal.CupCap
