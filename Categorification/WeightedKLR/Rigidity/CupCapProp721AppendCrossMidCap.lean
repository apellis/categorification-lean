/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossMid
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapECross

/-!
# `K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` and the crossing, for a cap left of the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` with the crossing, for `j < ℓ`.
The map `ι₂ ∘ ι₁ : K_ν → K_{{i} + ({i} + ν)}` carries the left action of the crossing of the
two appended strands of `T^λ` to the right action of the crossing of the two appended strands of
`T^{λ⁺}` (`CupCap.capIota_two_appendedCross`, from `CupCap.appendIota_two_appendedCross` in the
model), so `CupCap.capECompIsoOfEq` for `CupCap.capAppendDataMid` carries the crossing on
`𝔈_i²` to the crossing on `𝔈⁺_i²` (`CupCap.capECompIsoOfEqMid_cross`).

Route hypotheses (tracked), as for `CupCap.capEEquivMid`: each piece `L e(t)` finitely
generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units (`hκ`) and the pull-off
identities (`hP`, `hPL`).

## Main results

* `CupCap.capIota_two_appendedCross`, `CupCap.capECompIsoOfEqMid_cross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) (μ : Multiset I)

/-- Minus the crossing of the two appended strands of `T^λ` is the image of minus the crossing of
`T̃^λ` times the unit of the appended strands. -/
theorem appendedCross_eq_mk_mul :
    appendedCross Q Λ' i μ = TensorProductAlgebra.mk Q Λ' _
      (orderProjection Q Λ' _ (-StendhalAlgebraAllOrders.newCross Q Λ' i μ) *
        appendBlackStendhal Q Λ' i _ (appendBlackStendhal Q Λ' i μ 1)) := by
  rw [← negCrossStendhal_eq_mul]
  rfl

end Generic

section Ring

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hR'' : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "aB₁" => appendBlackPlus Q Λ Λc j hj ν ν₀ i
local notation "aB₂" => appendBlackPlus Q Λ Λc j hj νᵢ ν₀ i
local notation "Y" => lastCrossPlus k Q Λ Λc j hj ν ν₀ i

/-- Minus the crossing of the two appended strands of `T^{λ⁺}`, cast to
`({i} + ({i} + ν)) + ν₀`, is the image of `-(Y · appendBlack(appendBlack(1)))`. -/
theorem castOp_appendedCross_plus :
    castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc_two ν i)
        (op (appendedCross Q (plusLabels Λ Λc j hj) i (ν + ν₀))) =
      plusQuotOp k Q Λ Λc j hj νᵢᵢ ν₀ (op (-(Y * aB₂ (aB₁ 1)))) := by
  rw [castOp_op, appendedCross_eq_mk_mul, castTensorProductAlgebra_mk_stendhal, map_mul,
    appendBlackPlus_two, map_neg, map_neg, ← lastCrossPlus_eq, ← appendBlackPlus_two]
  rw [neg_mul (Y) (aB₂ (aB₁ 1))]
  rfl

/-- **`ι₂ ∘ ι₁` carries the crossing to the crossing**, for `j < ℓ` (arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21): the left action of the crossing of the two appended strands of `T^λ`
on `ι₂(ι₁(c))` is the right action of the crossing of the two appended strands of `T^{λ⁺}`.
Route hypotheses (tracked): `hκ`, `hP`, `hPL`. -/
theorem capIota_two_appendedCross (h : j < ℓ) (c : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    appendedCross Q Λ i ν •
        capIota νᵢ i hR' hR'' hP hPL hκ h (capIota ν i hR hR' hP hPL hκ h c) =
      castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc_two ν i)
        (op (appendedCross Q (plusLabels Λ Λc j hj) i (ν + ν₀))) •
        capIota νᵢ i hR' hR'' hP hPL hκ h (capIota ν i hR hR' hP hPL hκ h c) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  have hι := capModelRightEquiv_capIota ν i hR hR' hP hPL hκ h c y hy.symm
  have hι' := capModelRightEquiv_capIota νᵢ i hR' hR'' hP hPL hκ h _ _ hι
  rw [castOp_appendedCross_plus, ← capStendhal_smul, appendedCross_eq_mk_mul]
  change capLeftLin (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) L
      (orderProjection Q Λ νᵢᵢ (-StendhalAlgebraAllOrders.newCross Q Λ i ν) *
        appendBlackStendhal Q Λ i νᵢ (appendBlackStendhal Q Λ i ν 1)) _ = _
  apply (capModelRightEquiv hR'' hP hPL hκ).injective
  rw [capModelRightEquiv_capLeftLin hR'' hP hPL hκ _ _ _ hι', LinearEquiv.map_smul, hι',
    ← Submodule.Quotient.mk_smul, appendIota_two_appendedCross ν i h hR hR' hR'']

end Ring

section Field

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hR'' : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢᵢ" => TensorProductAlgebra k Q Λ νᵢᵢ
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢᵢ + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢᵢ" => CapBimodule k Q Λ Λc j hj νᵢᵢ ν₀ L
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
local notation "OrdKᵢᵢ" => ordTensor TPpᵢᵢᵐᵒᵖ TAᵢᵢᵐᵒᵖ (OpBimodule TAᵢᵢ CBᵢᵢ)

open CategoryTheory in
/-- **`K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` carries the crossing to the crossing, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): `(K ∘ τ) ≫ φ = φ ≫ (τ ∘ K)` for
`φ = CupCap.capECompIsoOfEq` of `CupCap.capAppendDataMid` at `ν` and at `{i} + ν`, with `τ` the
crossing on `𝔈_i²` (`blackCross`) and on `𝔈⁺_i²` (`resCrossOfEq`). Route hypotheses (tracked):
`hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capECompIsoOfEqMid_cross (h : j < ℓ) :
    Functor.whiskerRight (blackCross Q Λ i ν) OrdK ≫
        (capECompIsoOfEq (capAppendDataMid ν i hR hR' hP hPL hκ hQ hfin h)
          (capAppendDataMid νᵢ i hR' hR'' hP hPL hκ hQ hfin h)).hom =
      (capECompIsoOfEq (capAppendDataMid ν i hR hR' hP hPL hκ hQ hfin h)
          (capAppendDataMid νᵢ i hR' hR'' hP hPL hκ hQ hfin h)).hom ≫
        Functor.whiskerLeft OrdKᵢᵢ
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
            (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) :=
  capECompIsoOfEq_cross hQ _ _ (capIota_two_appendedCross ν i hR hR' hR'' hP hPL hκ h)

end Field

end Categorification.Stendhal.CupCap
