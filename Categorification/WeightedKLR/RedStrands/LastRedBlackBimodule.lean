/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackSlide

/-!
# The bimodule map of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32: `IR^μ F_i I^μ ≅ F_i(-μ_i)`. Write `T₀` for the algebra of the first `ℓ` red
strands and `T` for the algebra with the last red strand `λ_ℓ` added. On bimodules the functor
`IR^μ F_i I^μ` is given by `e_ℓ T_{i+ν} ν_i(e_ℓ)`, and `F_i` on `T₀` by `T₀_{i+ν} ν_i(1)`.
Webster's map adds the red strand `λ_ℓ` to a diagram and lets it cross the new black strand at
the bottom. Here the crossing is the element `lastRedBlackCrossing`, and the map is
`g ↦ appendRed(g) · lastRedBlackCrossing`.

## Main results

* `lastRedBlackMap`: the map `T₀_{i+ν} → T_{i+ν}` of the proof of Proposition 4.32.
* `lastRedBlackMap_mul_left`, `lastRedBlackMap_mul_appendBlack`: it is a map of bimodules,
  for `T₀_{i+ν}` acting on the left through `appendRed` and `T₀_ν` acting on the right through
  `appendBlack ∘ appendRed`.
* `lastRedIdem_mul_lastRedBlackMap`, `lastRedBlackMap_mul_appendBlack_lastRedIdem`: its values
  lie in `e_ℓ T_{i+ν} ν_i(e_ℓ)`.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ
local notation "P'" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ
local notation "S₀" => StendhalAlgebra k Q Λ₀ ν
local notation "S" => StendhalAlgebra k Q Λ νᵢ

section Stendhal

/-- Append the black strand `i`, then the last red strand, to a red-ordered diagram. -/
def blackRedStendhal : S₀ →ₙ+* S :=
  (appendRedStendhalValue Q Λ νᵢ).comp (appendBlackStendhal Q Λ₀ i ν : S₀ →ₙ+* _)

/-- Append the last red strand, then the black strand `i`, to a red-ordered diagram. -/
def redBlackStendhal : S₀ →ₙ+* S :=
  (appendBlackStendhal Q Λ i ν : _ →ₙ+* S).comp (appendRedStendhalValue Q Λ ν)

theorem blackRedStendhal_val (z : S₀) :
    (blackRedStendhal Q Λ i ν z).val = blackRedValue Q Λ i ν z.val := rfl

theorem redBlackStendhal_val (z : S₀) :
    (redBlackStendhal Q Λ i ν z).val = redBlackValue Q Λ i ν z.val := rfl

private theorem sandwich_mem_corner (z : A) : P' * z * P' ∈ Subsemigroup.corner P' := by
  have h := (StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem (k := k) (Q := Q)
    (Λ := Λ) (ν := νᵢ)).eq
  apply (Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  exact ⟨by simp only [← mul_assoc, h], by simp only [mul_assoc, h]⟩

/-- The crossing of the last two strands, cut to red-ordered loadings. -/
def crossingStendhal : S :=
  ⟨P' * StendhalAlgebraAllOrders.ψ N₀ * P', sandwich_mem_corner Q Λ i ν _⟩

/-- Webster's crossing of the black strand `i` with the last red strand: from the loadings
`(s, λ_ℓ, i)` at the bottom to `(s, i, λ_ℓ)` at the top. -/
def crossingStendhalCut : S :=
  blackRedStendhal Q Λ i ν 1 * crossingStendhal Q Λ i ν * redBlackStendhal Q Λ i ν 1

private theorem corner_mul_P (z : S) : z.val * P' = z.val := KLR.Corner.val_mul_E z

private theorem P_mul_corner (z : S) : P' * z.val = z.val := KLR.Corner.E_mul_val z

private theorem val_mul_crossing (z w : S) :
    (z * crossingStendhal Q Λ i ν * w).val =
      z.val * StendhalAlgebraAllOrders.ψ N₀ * w.val := by
  rw [KLR.Corner.val_mul, KLR.Corner.val_mul]
  change z.val * (P' * _ * P') * w.val = _
  rw [show z.val * (P' * StendhalAlgebraAllOrders.ψ N₀ * P') * w.val =
      (z.val * P') * StendhalAlgebraAllOrders.ψ N₀ * (P' * w.val) by simp only [mul_assoc],
    corner_mul_P, P_mul_corner]

/-- The slide of Proposition 4.32 at the level of red-ordered diagrams. -/
theorem blackRedStendhal_mul_crossingStendhalCut (z : S₀) :
    blackRedStendhal Q Λ i ν z * crossingStendhalCut Q Λ i ν =
      crossingStendhalCut Q Λ i ν * redBlackStendhal Q Λ i ν z := by
  have hl : blackRedStendhal Q Λ i ν z * blackRedStendhal Q Λ i ν 1 =
      blackRedStendhal Q Λ i ν z := by rw [← map_mul, mul_one]
  have hl' : blackRedStendhal Q Λ i ν 1 * blackRedStendhal Q Λ i ν z =
      blackRedStendhal Q Λ i ν z := by rw [← map_mul, one_mul]
  have hr : redBlackStendhal Q Λ i ν 1 * redBlackStendhal Q Λ i ν z =
      redBlackStendhal Q Λ i ν z := by rw [← map_mul, one_mul]
  have hr' : redBlackStendhal Q Λ i ν z * redBlackStendhal Q Λ i ν 1 =
      redBlackStendhal Q Λ i ν z := by rw [← map_mul, mul_one]
  have e₁ : blackRedStendhal Q Λ i ν z * crossingStendhalCut Q Λ i ν =
      blackRedStendhal Q Λ i ν z * crossingStendhal Q Λ i ν * redBlackStendhal Q Λ i ν 1 := by
    rw [crossingStendhalCut, ← mul_assoc, ← mul_assoc, hl]
  have e₂ : crossingStendhalCut Q Λ i ν * redBlackStendhal Q Λ i ν z =
      blackRedStendhal Q Λ i ν 1 * crossingStendhal Q Λ i ν * redBlackStendhal Q Λ i ν z := by
    rw [crossingStendhalCut, mul_assoc _ (redBlackStendhal Q Λ i ν 1), hr]
  rw [e₁, e₂]
  apply Subtype.ext
  have h1 : (1 : S₀).val * z.val = z.val := KLR.Corner.E_mul_val z
  have h2 : z.val * (1 : S₀).val = z.val := KLR.Corner.val_mul_E z
  rw [val_mul_crossing, val_mul_crossing, blackRedStendhal_val, blackRedStendhal_val,
    redBlackStendhal_val, redBlackStendhal_val, slide_crossing, slide_crossing, mul_assoc,
    mul_assoc, ← redBlackValue_mul, ← redBlackValue_mul, h1, h2]

/-- The crossing cut to red-ordered loadings is the crossing followed by "red strand, then
black strand" at the bottom. -/
theorem crossingStendhalCut_val :
    (crossingStendhalCut Q Λ i ν).val =
      StendhalAlgebraAllOrders.ψ N₀ * redBlackValue Q Λ i ν (1 : S₀).val := by
  have h1 : (1 : S₀).val * (1 : S₀).val = (1 : S₀).val := KLR.Corner.E_mul_val 1
  rw [crossingStendhalCut, val_mul_crossing, blackRedStendhal_val, redBlackStendhal_val,
    slide_crossing, mul_assoc, ← redBlackValue_mul, h1]

end Stendhal

section Quotient

local notation "T₀'" => TensorProductAlgebra k Q Λ₀ νᵢ
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "π'" => TensorProductAlgebra.mk Q Λ νᵢ

theorem appendRed_mk_val (β : Multiset I) (z : StendhalAlgebra k Q Λ₀ β) :
    (appendRed Q Λ β (TensorProductAlgebra.mk Q Λ₀ β z)).val =
      TensorProductAlgebra.mk Q Λ β (appendRedStendhalValue Q Λ β z) := rfl

theorem appendRed_one_val (β : Multiset I) :
    (appendRed Q Λ β 1).val = TensorProductAlgebra.lastRedIdem Q Λ β := by
  rw [map_one]
  rfl

private theorem mk_surjective (β : Multiset I) (Λ' : Fin ℓ' → I →₀ ℕ) :
    Function.Surjective (TensorProductAlgebra.mk (k := k) Q Λ' β) :=
  (StendhalAlgebra.violatedIdeal k Q Λ' β).ringCon.mk'_surjective

/-- Webster's crossing of the black strand `i` with the last red strand, in the violating
quotient: the element `lastRedBlackCrossing` of the proof of Proposition 4.32. -/
def lastRedBlackCrossing : T' := π' (crossingStendhalCut Q Λ i ν)

private theorem blackRed_mk (z : S₀) :
    (appendRed Q Λ νᵢ (appendBlack Q Λ₀ i ν (TensorProductAlgebra.mk Q Λ₀ ν z))).val =
      π' (blackRedStendhal Q Λ i ν z) := rfl

private theorem redBlack_mk (z : S₀) :
    appendBlack Q Λ i ν (appendRed Q Λ ν (TensorProductAlgebra.mk Q Λ₀ ν z)).val =
      π' (redBlackStendhal Q Λ i ν z) := rfl

/-- The slide of Proposition 4.32 in the violating quotient: the crossing intertwines
"black strand, then red strand" with "red strand, then black strand". -/
theorem appendRed_appendBlack_mul_lastRedBlackCrossing (h : TensorProductAlgebra k Q Λ₀ ν) :
    (appendRed Q Λ νᵢ (appendBlack Q Λ₀ i ν h)).val * lastRedBlackCrossing Q Λ i ν =
      lastRedBlackCrossing Q Λ i ν * appendBlack Q Λ i ν (appendRed Q Λ ν h).val := by
  obtain ⟨z, rfl⟩ := mk_surjective Q ν Λ₀ h
  rw [blackRed_mk, redBlack_mk, lastRedBlackCrossing, ← map_mul, ← map_mul,
    blackRedStendhal_mul_crossingStendhalCut]

private theorem lastRedBlackCrossing_mul_redBlack_one :
    lastRedBlackCrossing Q Λ i ν * π' (redBlackStendhal Q Λ i ν 1) =
      lastRedBlackCrossing Q Λ i ν := by
  rw [lastRedBlackCrossing, ← map_mul, crossingStendhalCut, mul_assoc, ← map_mul, mul_one]

private theorem blackRed_one_mul_lastRedBlackCrossing :
    π' (blackRedStendhal Q Λ i ν 1) * lastRedBlackCrossing Q Λ i ν =
      lastRedBlackCrossing Q Λ i ν := by
  rw [lastRedBlackCrossing, ← map_mul, crossingStendhalCut, ← mul_assoc, ← mul_assoc,
    ← map_mul, one_mul]

/-- The bimodule map of the proof of Proposition 4.32: add the last red strand to a diagram
and let it cross the new black strand `i` at the bottom. -/
def lastRedBlackMap : T₀' →ₗ[k] T' where
  toFun g := (appendRed Q Λ νᵢ g).val * lastRedBlackCrossing Q Λ i ν
  map_add' g g' := by
    rw [map_add]
    exact add_mul (appendRed Q Λ νᵢ g).val (appendRed Q Λ νᵢ g').val _
  map_smul' c g := by
    rw [map_smul, KLR.Corner.val_smul]
    exact smul_mul_assoc c (appendRed Q Λ νᵢ g).val _

theorem lastRedBlackMap_apply (g : T₀') :
    lastRedBlackMap Q Λ i ν g = (appendRed Q Λ νᵢ g).val * lastRedBlackCrossing Q Λ i ν := rfl

/-- The map of Proposition 4.32 is left linear for `T₀_{i+ν}` acting through `appendRed`. -/
theorem lastRedBlackMap_mul_left (a g : T₀') :
    lastRedBlackMap Q Λ i ν (a * g) = (appendRed Q Λ νᵢ a).val * lastRedBlackMap Q Λ i ν g := by
  rw [lastRedBlackMap_apply, lastRedBlackMap_apply, map_mul, KLR.Corner.val_mul, mul_assoc]

/-- The map of Proposition 4.32 is right linear for `T₀_ν` acting on the source through
`appendBlack` and on the target through `appendBlack ∘ appendRed`. -/
theorem lastRedBlackMap_mul_appendBlack (g : T₀') (h : TensorProductAlgebra k Q Λ₀ ν) :
    lastRedBlackMap Q Λ i ν (g * appendBlack Q Λ₀ i ν h) =
      lastRedBlackMap Q Λ i ν g * appendBlack Q Λ i ν (appendRed Q Λ ν h).val := by
  rw [lastRedBlackMap_apply, lastRedBlackMap_apply, map_mul, KLR.Corner.val_mul, mul_assoc,
    appendRed_appendBlack_mul_lastRedBlackCrossing, mul_assoc]

/-- The values of the map of Proposition 4.32 lie in `e_ℓ T_{i+ν}`. -/
theorem lastRedIdem_mul_lastRedBlackMap (g : T₀') :
    TensorProductAlgebra.lastRedIdem Q Λ νᵢ * lastRedBlackMap Q Λ i ν g =
      lastRedBlackMap Q Λ i ν g := by
  rw [lastRedBlackMap_apply, ← mul_assoc, KLR.Corner.E_mul_val]

/-- The values of the map of Proposition 4.32 lie in `T_{i+ν} ν_i(e_ℓ)`. -/
theorem lastRedBlackMap_mul_appendBlack_lastRedIdem (g : T₀') :
    lastRedBlackMap Q Λ i ν g * appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν) =
      lastRedBlackMap Q Λ i ν g := by
  have h : appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν) =
      π' (redBlackStendhal Q Λ i ν 1) := by
    rw [TensorProductAlgebra.lastRedIdem, ← appendRedStendhalValue_one]
    rfl
  rw [h, lastRedBlackMap_apply, mul_assoc, lastRedBlackCrossing_mul_redBlack_one]

end Quotient

end Categorification.Stendhal
