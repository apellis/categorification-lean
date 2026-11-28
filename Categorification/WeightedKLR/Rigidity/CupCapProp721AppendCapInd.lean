/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendQuot
import Categorification.WeightedKLR.Rigidity.CupCapProp721Induced
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.Algebra.InductionAlongQuotientSup

/-!
# `𝔉_i(K^{λ⁺}_λ)` through the model

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for `j < ℓ`. Inducing the cap bimodule `K^{λ⁺}_λ` along the black-appending map
of `T^{λ⁺}` (with target at the black weight `({i} + ν) + ν₀`) gives `e' · model_{{i} + ν}` modulo
its violated part (`CupCap.appendCapEquiv`). The steps are: `T^{λ⁺}`-induction is
`T̃^{λ⁺}`-induction modulo the violated ideal (`InductionAlong.indQuotEquiv`); `K^{λ⁺}_λ` is the
model modulo its bottom-violated part (`CupCap.capModelRightEquiv`); induction of a quotient
(`InductionAlong.indQuotSupEquiv`); the two violated parts of `𝔉_i(model_ν)` agree
(`CupCap.indImageSub_sup_indKerSub_eq`); and the comparison of `𝔉_i(model_ν)` with
`e' · model_{{i} + ν}` (`CupCap.appendViolQuotEquiv`).

## Main definitions

* `CupCap.appendBlackTPAOp`: appending a black strand in `T^{λ⁺}`, on the opposite rings.
* `CupCap.appendCapEquiv`: `𝔉_i(K^{λ⁺}_λ) ≅ e' · model_{{i} + ν} / violated`, semilinear along
  `T̃^{λ⁺} → T^{λ⁺}` (`CupCap.appendCapEquiv_smul`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Cast

variable {I k : Type*} [DecidableEq I] [CommRing k] {n : ℕ} (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ' : Fin n → I →₀ ℕ)

theorem castTensorProductAlgebra_mk_stendhal {μ μ' : Multiset I} (h : μ = μ')
    (z : StendhalAlgebra k Q Λ' μ) :
    castTensorProductAlgebra Q Λ' h (TensorProductAlgebra.mk Q Λ' μ z) =
      TensorProductAlgebra.mk Q Λ' μ' (castPlusStendhal Q Λ' h z) := by
  subst h; rfl

end Cast

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} {i : I}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Tpᵢ" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "aBp" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
local notation "πᵢ" => plusQuotOp k Q Λ Λc j hj νᵢ ν₀

variable (k Q Λ Λc j hj ν ν₀ i) in
/-- **Appending a black strand of colour `i` in `T^{λ⁺}`**, with target at the black weight
`({i} + ν) + ν₀`, on the opposite rings. -/
def appendBlackTPAOp : TPpᵐᵒᵖ →ₙ+* TPpᵢᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom
    ((castTensorProductAlgebra Q Λ⁺ (plusWeight_assoc ν ν₀ i)).toAlgHom.toNonUnitalAlgHom.comp
      (appendBlack Q Λ⁺ i (ν + ν₀))))

/-- Appending in `T^{λ⁺}` is the image of appending in `T̃^{λ⁺}`. -/
theorem appendBlackTPAOp_plusQuotOp (a : Tpᵐᵒᵖ) :
    appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i (plusQuotOp k Q Λ Λc j hj ν ν₀ a) = πᵢ (aBp a) := by
  induction a using MulOpposite.rec' with
  | h a =>
  apply MulOpposite.unop_injective
  change castTensorProductAlgebra Q Λ⁺ (plusWeight_assoc ν ν₀ i)
      (appendBlack Q Λ⁺ i (ν + ν₀) (TensorProductAlgebra.mk Q Λ⁺ (ν + ν₀) a)) =
    TensorProductAlgebra.mk Q Λ⁺ (νᵢ + ν₀)
      (castPlusStendhal Q Λ⁺ (plusWeight_assoc ν ν₀ i) (appendBlackStendhal Q Λ⁺ i (ν + ν₀) a))
  rw [appendBlack_mk]
  exact castTensorProductAlgebra_mk_stendhal Q Λ⁺ _ _

theorem plusQuotOp_eq_zero_iff (b : Tpᵐᵒᵖ) :
    plusQuotOp k Q Λ Λc j hj ν ν₀ b = 0 ↔
      b.unop ∈ StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀) := by
  change op ((StendhalAlgebra.violatedIdeal k Q Λ⁺ (ν + ν₀)).ringCon.mk' b.unop) = op 0 ↔ _
  rw [op_inj, ← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L
local notation "MM" => MidModel j hj Q Λ Λc ν ν₀ L
local notation "ABV" => appendBotViolSub Q Λ Λc j hj ν ν₀ i L

/-- **Step (i)**: inducing `K^{λ⁺}_λ` along `T^{λ⁺}` is inducing it along `T̃^{λ⁺}` modulo the
violated ideal. -/
def capIndQuotEquiv :
    (Ind CB aBp ⧸ indKerSub aBp πᵢ CB) ≃+ Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i) :=
  indQuotEquiv (φ := aBp) (φ' := appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)
    (πA := plusQuotOp k Q Λ Λc j hj ν ν₀) (πB := πᵢ) (N := CB) plusQuotOp_surjective
    plusQuotOp_surjective appendBlackTPAOp_plusQuotOp (capStendhal_smul (L := L))

theorem capIndQuotEquiv_smul (b : Tpᵢᵐᵒᵖ) (q : Ind CB aBp ⧸ indKerSub aBp πᵢ CB) :
    capIndQuotEquiv (b • q) = πᵢ b • capIndQuotEquiv q :=
  indQuotEquiv_smul _ _ _ _ b q

/-- **The two violated parts of `𝔉_i(model_ν)` agree**: `ker(T̃^{λ⁺} → T^{λ⁺}) · 𝔉_i(model_ν)`
is the bottom-violated part. -/
theorem indKerSub_eq_appendBotViolSub : indKerSub aBp πᵢ MM = ABV := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, y, rfl⟩
    exact Submodule.subset_span ⟨b.unop, (plusQuotOp_eq_zero_iff b).1 hb, y, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, y, rfl⟩
    refine Submodule.subset_span ⟨op b, (plusQuotOp_eq_zero_iff (op b)).2 hb, y, rfl⟩

/-- `𝔉_i` of the bottom-violated part of the model, together with the kernel part, is the
bottom-violated part of `𝔉_i(model_ν)`. -/
theorem indImageSub_sup_indKerSub_eq : indImageSub aBp BV ⊔ indKerSub aBp πᵢ MM = ABV := by
  rw [indKerSub_eq_appendBotViolSub, sup_eq_right]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, w, hw, rfl⟩
  exact tmul_mem_appendBotViolSub ν i z hw

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **Steps (ii) and (iii)**: `𝔉̃_i(K^{λ⁺}_λ)` modulo the kernel part is `𝔉_i(model_ν)` modulo
its bottom-violated part. -/
def capIndModelEquiv :
    (Ind CB aBp ⧸ indKerSub aBp πᵢ CB) ≃ₗ[Tpᵢᵐᵒᵖ] (Ind MM aBp ⧸ ABV) :=
  ((Submodule.Quotient.equiv _ _ (indMapLinEquiv aBp (capModelRightEquiv hR hP hPL hκ))
      (map_indKerSub πᵢ (capModelRightEquiv hR hP hPL hκ).surjective)).trans
    (indQuotSupEquiv aBp πᵢ BV)).trans
    (Submodule.quotEquivOfEq _ _ indImageSub_sup_indKerSub_eq)

variable (h : j < ℓ)

local notation "Rg" => LinearMap.range (toAppendMid Q Λ Λc j hj ν ν₀ i L h)

/-- **`𝔉_i(K^{λ⁺}_λ)` is `e' · model_{{i} + ν}` modulo its violated part** (arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21), for `j < ℓ`, under the hypotheses of Lemma 7.17. It is
semilinear along `T̃^{λ⁺} → T^{λ⁺}` (`CupCap.appendCapEquiv_smul`). -/
def appendCapEquiv :
    Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i) ≃+ Rg ⧸ appendRangeViolSub ν i L h :=
  capIndQuotEquiv.symm.trans
    ((capIndModelEquiv hR hP hPL hκ).trans (appendViolQuotEquiv ν i L h)).toAddEquiv

theorem appendCapEquiv_apply (x : Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)) :
    appendCapEquiv hR hP hPL hκ h x = appendViolQuotEquiv ν i L h
      (capIndModelEquiv hR hP hPL hκ ((capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm x)) :=
  rfl

theorem capIndQuotEquiv_symm_smul (b : Tpᵢᵐᵒᵖ)
    (x : Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)) :
    (capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm (πᵢ b • x) =
      b • (capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm x := by
  obtain ⟨q, rfl⟩ := (capIndQuotEquiv (L := L) (hj := hj) (i := i)).surjective x
  rw [← capIndQuotEquiv_smul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

theorem appendCapEquiv_smul (b : Tpᵢᵐᵒᵖ) (x : Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)) :
    appendCapEquiv hR hP hPL hκ h (πᵢ b • x) = b • appendCapEquiv hR hP hPL hκ h x := by
  rw [appendCapEquiv_apply, appendCapEquiv_apply, capIndQuotEquiv_symm_smul, map_smul, map_smul]

end Categorification.Stendhal.CupCap
