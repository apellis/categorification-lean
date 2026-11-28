/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapInd
import Categorification.Algebra.InductionAlongTensor

/-!
# Webster's `Fᵢ` on `K^{λ⁺}_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for `j < ℓ`. Webster's `Fᵢ` (`Stendhal.blackF`) on `K^{λ⁺}_λ` lands at the black
weight `{i} + (ν + ν₀)`; transporting along `{i} + (ν + ν₀) = ({i} + ν) + ν₀` identifies it with
`e' · model_{{i} + ν}` modulo its violated part (`CupCap.blackFCapEquiv`).

## Main definitions

* `CupCap.plusWeightOp`: the transport `T^{λ⁺}` between the two black weights, on opposite rings.
* `CupCap.blackFCapEquiv`: `Fᵢ(K^{λ⁺}_λ) ≅ e' · model_{{i} + ν} / violated`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} {i : I}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "Tpᵢ" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "πᵢ" => plusQuotOp k Q Λ Λc j hj νᵢ ν₀
local notation "aB" => appendBlackOp Q (plusLabels Λ Λc j hj) i (ν + ν₀)

variable (k Q Λ Λc j hj ν ν₀ i) in
/-- `T^{λ⁺}` at the black weights `{i} + (ν + ν₀)` and `({i} + ν) + ν₀`, on the opposite rings. -/
def plusWeightOp :
    (TensorProductAlgebra k Q Λ⁺ ((Singleton.singleton i : Multiset I) + (ν + ν₀)))ᵐᵒᵖ ≃+*
      (TensorProductAlgebra k Q Λ⁺ (νᵢ + ν₀))ᵐᵒᵖ :=
  RingEquiv.op (castTensorProductAlgebra Q Λ⁺ (plusWeight_assoc ν ν₀ i)).toRingEquiv

theorem appendBlackTPAOp_eq (t : TPpᵐᵒᵖ) :
    appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i (RingEquiv.refl _ t) =
      plusWeightOp k Q Λ Λc j hj ν ν₀ i (aB t) := rfl

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L

/-- `Fᵢ(K^{λ⁺}_λ)` at the two black weights. -/
def blackFCapTransport : Ind CB aB ≃+ Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i) :=
  Ind.transport (RingEquiv.refl _) (plusWeightOp k Q Λ Λc j hj ν ν₀ i) appendBlackTPAOp_eq
    (AddEquiv.refl _) (fun _ _ => rfl)

theorem blackFCapTransport_smul
    (b : (TensorProductAlgebra k Q Λ⁺ ((Singleton.singleton i : Multiset I) + (ν + ν₀)))ᵐᵒᵖ)
    (x : Ind CB aB) :
    blackFCapTransport (b • x) = plusWeightOp k Q Λ Λc j hj ν ν₀ i b • blackFCapTransport x :=
  Ind.transport_smul _ _ _ _ _ b x

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (h : j < ℓ)

local notation "Rg" => LinearMap.range (toAppendMid Q Λ Λc j hj ν ν₀ i L h)

/-- **Webster's `Fᵢ` on `K^{λ⁺}_λ`** (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for
`j < ℓ`, under the hypotheses of Lemma 7.17: the underlying group of
`(blackF Q Λ⁺ i (ν + ν₀)).obj K^{λ⁺}_λ` is `e' · model_{{i} + ν}` modulo its violated part,
semilinearly along `T̃^{λ⁺} → T^{λ⁺}` and the weight transport (`CupCap.blackFCapEquiv_smul`). -/
def blackFCapEquiv : Ind CB aB ≃+ Rg ⧸ appendRangeViolSub ν i L h :=
  blackFCapTransport.trans (appendCapEquiv hR hP hPL hκ h)

theorem blackFCapEquiv_apply (x : Ind CB aB) :
    blackFCapEquiv hR hP hPL hκ h x = appendCapEquiv hR hP hPL hκ h (blackFCapTransport x) :=
  rfl

theorem blackFCapEquiv_smul (b : Tpᵢᵐᵒᵖ) (x : Ind CB aB) :
    blackFCapEquiv hR hP hPL hκ h ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm (πᵢ b) • x) =
      b • blackFCapEquiv hR hP hPL hκ h x := by
  rw [blackFCapEquiv_apply, blackFCapEquiv_apply, blackFCapTransport_smul,
    RingEquiv.apply_symm_apply, appendCapEquiv_smul]

end Categorification.Stendhal.CupCap
