/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendStendhal

/-!
# Appending a black strand to the model of the cap bimodule

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). On right modules over `T̃^{λ⁺}`,
appending a black strand of colour `i` at the right (`CupCap.appendBlackPlusOp`) induces the
functor `𝔉_i`. Applied to the model `L ⊗ e T̃^{λ⁺}_ν` of the cap bimodule (`CupCap.MidModel`) it
gives, by induction along a composite, the induction of `L` along the appended diagrams at the
maximum. These are the diagrams at the maximum at the black weight `{i} + ν` cut on the left by
the idempotent `e' = ∑_s e(s i)` of `T̃^λ` acting through the window idempotents
(`CupCap.appendBlackPlus_midStendhal`), and `e'` commutes with them
(`CupCap.commute_appendIdemPlus`). Hence the induced module is a retract of the model at `{i} + ν`
(`CupCap.fromAppendMid_comp_toAppendMid`), the composite the other way being the action of `e'`
(`CupCap.toAppendMid_comp_fromAppendMid`).

## Main definitions

* `CupCap.appendBlackPlusOp`: appending a black strand, on the opposite rings.
* `CupCap.appendIdemPlus`: the idempotent `e'` of the appended loadings in `T̃^{λ⁺}`.
* `CupCap.appendMidEquiv`: `𝔉_i` of the model as an induction along the appended diagrams.
* `CupCap.toAppendMid`, `CupCap.fromAppendMid`: the maps to and from the model at `{i} + ν`.

## Main results

* `CupCap.appendBlackPlus_midStendhal`, `CupCap.commute_appendIdemPlus`.
* `CupCap.fromAppendMid_comp_toAppendMid`, `CupCap.toAppendMid_comp_fromAppendMid`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "Tc" => StendhalAlgebra k Q Λc ν₀

/-- Appending a black strand of colour `i` at the right of `T̃^{λ⁺}`, on the opposite rings. -/
def appendBlackPlusOp :
    (StendhalAlgebra k Q Λ⁺ (ν + ν₀))ᵐᵒᵖ →ₙ+* (StendhalAlgebra k Q Λ⁺ (νᵢ + ν₀))ᵐᵒᵖ :=
  NonUnitalRingHom.op
    (NonUnitalRingHomClass.toNonUnitalRingHom (appendBlackPlus Q Λ Λc j hj ν ν₀ i))

theorem appendBlackPlusOp_op (z : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    appendBlackPlusOp Q Λ Λc j hj ν ν₀ i (op z) = op (appendBlackPlus Q Λ Λc j hj ν ν₀ i z) :=
  rfl

/-- The idempotent `e' = ∑_s e(s i)` of the appended loadings, through the window idempotents,
in `T̃^{λ⁺}` at the black weight `({i} + ν) + ν₀`. -/
def appendIdemPlus : StendhalAlgebra k Q Λ⁺ (νᵢ + ν₀) :=
  botMap k Q Λ Λc j hj νᵢ ν₀
    (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc νᵢ ν₀ (appendBlackLoading i ν s))

/-- The diagrams at the maximum, followed by appending a black strand, on the opposite rings. -/
def appendMidOp :
    Tcᵐᵒᵖ →ₙ+* (StendhalAlgebra k Q Λ⁺ (νᵢ + ν₀))ᵐᵒᵖ :=
  (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i).comp (midOp j hj Q Λ Λc ν ν₀)

variable {Q Λ Λc j hj ν₀}

/-- The diagrams at the maximum of `z`, at any black weight, are those of one KLR lift of `z`. -/
theorem midStendhal_eq_midBot (μ : Multiset I) {z : Tc}
    {x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)}
    (hx : StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x = z.val) :
    midStendhal j hj Q Λ Λc μ ν₀ z = midBot j hj Q Λ Λc μ ν₀ x := by
  rw [midStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]

/-- The window idempotents commute with the diagrams at the maximum. -/
theorem commute_appendIdemPlus (z : Tc) :
    Commute (appendIdemPlus Q Λ Λc j hj ν ν₀ i) (midStendhal j hj Q Λ Λc νᵢ ν₀ z) := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  rw [midStendhal_eq_midBot νᵢ hx, Commute, SemiconjBy, appendIdemPlus, midBot_apply, ← map_mul,
    ← map_mul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [midIdem, eSum_mul_midMapKLR, midMapKLR_mul_eSum]

/-- **Appending a black strand to the diagrams at the maximum** (arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21), for `j < ℓ`: the result is `e'` times the diagrams at the maximum at the
black weight `{i} + ν`. -/
theorem appendBlackPlus_midStendhal (h : j < ℓ) (z : Tc) :
    appendBlackPlus Q Λ Λc j hj ν ν₀ i (midStendhal j hj Q Λ Λc ν ν₀ z) =
      appendIdemPlus Q Λ Λc j hj ν ν₀ i * midStendhal j hj Q Λ Λc νᵢ ν₀ z := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  rw [midStendhal_eq_midBot ν hx, appendBlackPlus_midBot Q Λ Λc j hj ν ν₀ i h,
    midStendhal_eq_midBot νᵢ hx]
  rfl

local notation "ψA" => appendMidOp Q Λ Λc j hj ν ν₀ i
local notation "φB" => midOp j hj Q Λ Λc νᵢ ν₀
local notation "Tᵢ" => (StendhalAlgebra k Q Λ⁺ (νᵢ + ν₀))ᵐᵒᵖ
local notation "e'" => op (appendIdemPlus Q Λ Λc j hj ν ν₀ i)

theorem appendMidOp_apply (h : j < ℓ) (a : Tcᵐᵒᵖ) : ψA a = φB a * e' := by
  rw [appendMidOp, NonUnitalRingHom.comp_apply, midOp_apply, appendBlackPlusOp_op,
    appendBlackPlus_midStendhal ν i h, op_mul, midOp_apply]

theorem op_appendIdemPlus_mul (a : Tcᵐᵒᵖ) : e' * φB a = φB a * e' := by
  rw [midOp_apply, ← op_mul, ← op_mul, (commute_appendIdemPlus ν i a.unop).eq]

theorem intertwines_appendMid_mid (h : j < ℓ) : Intertwines ψA φB (ψA 1) := fun a => by
  rw [← map_mul, mul_one, appendMidOp_apply ν i h, appendMidOp_apply ν i h, mul_assoc,
    op_appendIdemPlus_mul, ← mul_assoc, ← map_mul, one_mul]

theorem intertwines_mid_appendMid (h : j < ℓ) : Intertwines φB ψA (ψA 1) := fun a => by
  rw [← map_mul (appendMidOp Q Λ Λc j hj ν ν₀ i) 1 a, one_mul, appendMidOp_apply ν i h,
    appendMidOp_apply ν i h, ← mul_assoc, ← map_mul, mul_one]

theorem intertwines_mid_mid (h : j < ℓ) : Intertwines φB φB (ψA 1) := fun a => by
  rw [appendMidOp_apply ν i h, ← mul_assoc, ← map_mul, mul_one, mul_assoc, op_appendIdemPlus_mul,
    ← mul_assoc, ← map_mul, one_mul]

variable (Q Λ Λc j hj ν₀)
variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **`𝔉_i` of the model of the cap bimodule**: induction along appending a black strand, applied
to `L ⊗ e T̃^{λ⁺}_ν`, is the induction of `L` along the appended diagrams at the maximum. -/
def appendMidEquiv :
    Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i) ≃ₗ[Tᵢ] Ind L ψA :=
  compEquiv L (midOp j hj Q Λ Λc ν ν₀) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)

/-- The map from the appended model to the model at `{i} + ν`: `z ⊗ v ↦ z ⊗ v`, `z` lying in
`e' e T̃^{λ⁺}`. -/
def toAppendMid (h : j < ℓ) : Ind L ψA →ₗ[Tᵢ] MidModel j hj Q Λ Λc νᵢ ν₀ L :=
  natMap (intertwines_appendMid_mid ν i h)

/-- The map from the model at `{i} + ν` to the appended model: `z ⊗ v ↦ e' z ⊗ v`. -/
def fromAppendMid (h : j < ℓ) : MidModel j hj Q Λ Λc νᵢ ν₀ L →ₗ[Tᵢ] Ind L ψA :=
  natMap (intertwines_mid_appendMid ν i h)

/-- The appended model is a retract of the model at `{i} + ν`. -/
theorem fromAppendMid_comp_toAppendMid (h : j < ℓ) :
    (fromAppendMid Q Λ Λc j hj ν ν₀ i L h).comp (toAppendMid Q Λ Λc j hj ν ν₀ i L h) =
      LinearMap.id := by
  rw [fromAppendMid, toAppendMid, natMap_comp, ← natMap_unit (N := L) ψA]
  exact natMap_eq_of_unit_mul _ _ (by rw [unit_mul_unit, unit_mul_unit])

/-- The composite through the appended model is the action of `e'` on the model at `{i} + ν`:
`z ⊗ v ↦ e' z ⊗ v`. -/
theorem toAppendMid_comp_fromAppendMid (h : j < ℓ) :
    (toAppendMid Q Λ Λc j hj ν ν₀ i L h).comp (fromAppendMid Q Λ Λc j hj ν ν₀ i L h) =
      natMap (intertwines_mid_mid ν i h) := by
  rw [fromAppendMid, toAppendMid, natMap_comp]
  exact natMap_eq_of_unit_mul _ _ (by rw [unit_mul_unit])

end Categorification.Stendhal.CupCap
