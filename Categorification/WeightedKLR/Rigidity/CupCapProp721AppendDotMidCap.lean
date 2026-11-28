/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotMidModel
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDot

/-!
# `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` and the dot, for a cap left of the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with the dot, for `j < ℓ`. The map
`ι : K_ν → K_{{i} + ν}` carries the left action of the dot on the appended strand of `T^λ` to the
right action of the dot on the appended strand of `T^{λ⁺}` (`CupCap.capIota_appendedDot`, from
`CupCap.appendIota_appendedDot` in the model), so the natural isomorphism
`CupCap.capEOrdIsoOfEqMid` carries the dot on `𝔈_i` to the dot on `𝔈⁺_i`
(`CupCap.capEOrdIsoOfEqMid_dot`).

Route hypotheses (tracked), as for `CupCap.capEEquivMid`: each piece `L e(t)` finitely
generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units (`hκ`) and the pull-off
identities (`hP`, `hPL`).

## Main results

* `CupCap.capIota_appendedDot`, `CupCap.capEOrdIsoOfEqMid_dot`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) (μ : Multiset I)

/-- The dot on the appended strand of `T^λ` is the image of the dot of `T̃^λ` times the unit of
the appended strand. -/
theorem appendedDot_eq_mk_mul :
    appendedDot Q Λ' i μ = TensorProductAlgebra.mk Q Λ' _
      (orderProjection Q Λ' _ (StendhalAlgebraAllOrders.newDot Q Λ' i μ) *
        appendBlackStendhal Q Λ' i μ 1) := by
  rw [← newDotStendhal_eq_mul]
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
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L

/-- The dot on the appended strand of `T^{λ⁺}`, cast to `({i} + ν) + ν₀`, is the image of
`X · appendBlackPlus(1)`. -/
theorem castOp_appendedDot_plus :
    castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
        (op (appendedDot Q (plusLabels Λ Λc j hj) i (ν + ν₀))) =
      plusQuotOp k Q Λ Λc j hj νᵢ ν₀
        (op (lastDotPlus k Q Λ Λc j hj ν₀ ν i * appendBlackPlus Q Λ Λc j hj ν ν₀ i 1)) := by
  rw [castOp_op, appendedDot_eq_mk_mul, castTensorProductAlgebra_mk_stendhal, map_mul,
    ← lastDotPlus_eq]
  rfl

/-- **`ι` carries the dot to the dot**, for `j < ℓ` (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21): the left action of the dot on the appended strand of `T^λ` on `ι(c)` is the
right action of the dot on the appended strand of `T^{λ⁺}`. Route hypotheses (tracked): `hκ`,
`hP`, `hPL`. -/
theorem capIota_appendedDot (h : j < ℓ) (c : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    appendedDot Q Λ i ν • capIota ν i hR hR' hP hPL hκ h c =
      castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
        (op (appendedDot Q (plusLabels Λ Λc j hj) i (ν + ν₀))) •
        capIota ν i hR hR' hP hPL hκ h c := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  have hι := capModelRightEquiv_capIota ν i hR hR' hP hPL hκ h c y hy.symm
  rw [castOp_appendedDot_plus, ← capStendhal_smul, appendedDot_eq_mk_mul]
  change capLeftLin (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) L
      (orderProjection Q Λ νᵢ (StendhalAlgebraAllOrders.newDot Q Λ i ν) *
        appendBlackStendhal Q Λ i ν 1) _ = _
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  rw [capModelRightEquiv_capLeftLin hR' hP hPL hκ _ _ _ hι, LinearEquiv.map_smul, hι,
    ← Submodule.Quotient.mk_smul, appendIota_appendedDot ν i h hR hR']

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
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` carries the dot to the dot, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): `(K ∘ x) ≫ φ = φ ≫ (x ∘ K)` for
`φ = CupCap.capEOrdIsoOfEqMid`, with `x` the dot on `𝔈_i` (`blackDot`) and on `𝔈⁺_i`
(`resDotOfEq`). Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEOrdIsoOfEqMid_dot (h : j < ℓ) :
    Functor.whiskerRight (blackDot Q Λ i ν) OrdK ≫
        (capEOrdIsoOfEqMid ν i hR hR' hP hPL hκ hQ hfin h).hom =
      (capEOrdIsoOfEqMid ν i hR hR' hP hPL hκ hQ hfin h).hom ≫ Functor.whiskerLeft OrdKᵢ
        (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) :=
  capEOrdIsoOfEq_dot _ (capIota_appendedDot ν i hR hR' hP hPL hκ h)

end Field

end Categorification.Stendhal.CupCap
