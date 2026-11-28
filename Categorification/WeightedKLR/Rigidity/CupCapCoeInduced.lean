/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapViolated
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapE
import Categorification.Algebra.InductionAlongQuotient

/-!
# `K^{λ⁺}_λ` as a right `T^{λ⁺}`-module is induced from `L`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, for a
cap after `λ_j`, used in the proof of Lemma 7.19. The bimodule `K^{λ⁺}_λ` is the model
`L ⊗ e T̃^{λ⁺}` modulo its bottom-violated part `model · V_{λ⁺}` (`CupCap.capModelQuotEquiv`).
Since `model · V_{λ⁺}` is the kernel of `T̃^{λ⁺} → T^{λ⁺}` acting on the model, induction along a
map of quotient rings (`InductionAlong.indQuotEquiv`) identifies `K^{λ⁺}_λ` with `L ⊗ e T^{λ⁺}`,
the induction of `L` along the diagrams at the maximum followed by the quotient map onto
`T^{λ⁺}`, as right `T^{λ⁺}`-modules (`CupCap.capCoeEquiv`).

## Main definitions

* `CupCap.capQuotOp`: the quotient map `T̃^{λ⁺} → T^{λ⁺}` on the opposite rings.
* `CupCap.capCoeOp`: the diagrams at the maximum, followed by the quotient map.
* `CupCap.capCoeEquiv`: `K^{λ⁺}_λ ≅ L ⊗ e T^{λ⁺}` as right `T^{λ⁺}`-modules.

## Main results

* `CupCap.indKerSub_capQuotOp`: `ker(T̃^{λ⁺} → T^{λ⁺}) · model = model · V_{λ⁺}`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "Ev" => Env k Q Λ Λc j hj ν ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Tq" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Vp" => StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L

variable (k Q Λ Λc j hj ν ν₀) in
/-- The quotient map `T̃^{λ⁺} → T^{λ⁺}` by violated diagrams, on the opposite rings. -/
def capQuotOp : Tpᵐᵒᵖ →+* Tqᵐᵒᵖ :=
  RingHom.op (TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)).toRingHom

theorem capQuotOp_op (b : Tp) :
    capQuotOp k Q Λ Λc j hj ν ν₀ (op b) =
      op (TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀) b) := rfl

theorem capQuotOp_surjective : Function.Surjective (capQuotOp k Q Λ Λc j hj ν ν₀) := by
  intro t
  obtain ⟨b, hb⟩ := RingCon.mk'_surjective (Vp).ringCon t.unop
  exact ⟨op b, congrArg op hb⟩

theorem capQuotOp_eq_zero_iff (b : Tp) : capQuotOp k Q Λ Λc j hj ν ν₀ (op b) = 0 ↔ b ∈ Vp := by
  rw [capQuotOp_op, op_eq_zero_iff]
  change (Vp).ringCon.mk' b = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

variable (k Q Λ Λc j hj ν ν₀) in
/-- **The diagrams at the maximum followed by the quotient map onto `T^{λ⁺}`**: induction of `L`
along it is `L ⊗ e T^{λ⁺}`. -/
def capCoeOp : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ →ₙ+* Tqᵐᵒᵖ :=
  (capQuotOp k Q Λ Λc j hj ν ν₀ : Tpᵐᵒᵖ →ₙ+* Tqᵐᵒᵖ).comp (midOp j hj Q Λ Λc ν ν₀)

theorem capCoeOp_comm (c : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    capCoeOp k Q Λ Λc j hj ν ν₀ (RingHom.id _ c) =
      capQuotOp k Q Λ Λc j hj ν ν₀ (midOp j hj Q Λ Λc ν ν₀ c) := rfl

theorem capCoe_smul (c : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) (v : L) :
    c • v = RingHom.id _ c • v := rfl

variable (L) in
/-- **The kernel of `T̃^{λ⁺} → T^{λ⁺}` acting on the model is the bottom-violated part.** -/
theorem indKerSub_capQuotOp :
    indKerSub (midOp j hj Q Λ Λc ν ν₀) (capQuotOp k Q Λ Λc j hj ν ν₀) L = BV := by
  refine congrArg (Submodule.span Tpᵐᵒᵖ) (Set.ext fun x => ⟨?_, ?_⟩)
  · rintro ⟨b, hb, y, rfl⟩
    exact ⟨b.unop, (capQuotOp_eq_zero_iff b.unop).1 hb, y, rfl⟩
  · rintro ⟨b, hb, y, rfl⟩
    exact ⟨op b, (capQuotOp_eq_zero_iff b).2 hb, y, rfl⟩

/-- `L ⊗ e T^{λ⁺}`: the induction of `L` along `capCoeOp`. -/
local notation "IndQ" => Ind L (capCoeOp k Q Λ Λc j hj ν ν₀)

variable (L) in
/-- The model modulo its bottom-violated part is `L ⊗ e T^{λ⁺}`. -/
def midModelQuotEquiv : MidModel j hj Q Λ Λc ν ν₀ L ⧸ BV ≃+ IndQ :=
  (Submodule.quotEquivOfEq _ _ (indKerSub_capQuotOp L).symm).toAddEquiv.trans
    (indQuotEquiv (φ := midOp j hj Q Λ Λc ν ν₀) (φ' := capCoeOp k Q Λ Λc j hj ν ν₀)
      (πA := RingHom.id _) (πB := capQuotOp k Q Λ Λc j hj ν ν₀) (N := L)
      Function.surjective_id capQuotOp_surjective capCoeOp_comm capCoe_smul)

theorem midModelQuotEquiv_mk (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midModelQuotEquiv L (Submodule.Quotient.mk y) =
      indQuotHom (φ := midOp j hj Q Λ Λc ν ν₀) (φ' := capCoeOp k Q Λ Λc j hj ν ν₀)
        (πA := RingHom.id _) (πB := capQuotOp k Q Λ Λc j hj ν ν₀) (N := L)
        capCoeOp_comm capCoe_smul y := rfl

theorem midModelQuotEquiv_smul (b : Tpᵐᵒᵖ) (q : MidModel j hj Q Λ Λc ν ν₀ L ⧸ BV) :
    midModelQuotEquiv L (b • q) = capQuotOp k Q Λ Λc j hj ν ν₀ b • midModelQuotEquiv L q := by
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, midModelQuotEquiv_mk, midModelQuotEquiv_mk,
      indQuotHom_smul]

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)

variable (hL) in
/-- The bimodule quotient and the right-module quotient of the model have the same elements. -/
def midBimodQuotEquiv :
    MidBimod L hL hR ⧸ midBotViolEnv L hL hR ≃+ MidModel j hj Q Λ Λc ν ν₀ L ⧸ BV :=
  QuotientAddGroup.congr (midBotViolEnv L hL hR).toAddSubgroup (BV).toAddSubgroup
    (AddEquiv.refl (MidModel j hj Q Λ Λc ν ν₀ L))
    (by ext x; exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩)

theorem midBimodQuotEquiv_mk (y : MidBimod L hL hR) :
    midBimodQuotEquiv hL hR (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (ofMidBimod L hL hR y) := rfl

theorem midBimodQuotEquiv_smul (b : Tp) (q : MidBimod L hL hR ⧸ midBotViolEnv L hL hR) :
    midBimodQuotEquiv hL hR (envRight k Q Λ Λc j hj ν ν₀ (op b) • q) =
      (op b : Tpᵐᵒᵖ) • midBimodQuotEquiv hL hR q := by
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, midBimodQuotEquiv_mk, midBimodQuotEquiv_mk,
      ← Submodule.Quotient.mk_smul]
    congr 1
    have h := midEnvAlg_mk hR 1 b (ofMidBimod L hL hR y)
    rw [map_one, Module.End.one_apply] at h
    exact h

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

theorem capRightHom_op_mk (b : Tp) (x : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    (op (TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀) b) : Tqᵐᵒᵖ) • x =
      (envRight k Q Λ Λc j hj ν ν₀ (op b) • (show Cap k Q Λ Λc j hj ν ν₀ L from x) :
        Cap k Q Λ Λc j hj ν ν₀ L) := rfl

/-- The additive isomorphism underlying `CupCap.capCoeEquiv`. -/
def capCoeAddEquiv : CapBimodule k Q Λ Λc j hj ν ν₀ L ≃+ IndQ :=
  ((capModelQuotEquiv hP hPL hκ hR).toAddEquiv.trans (midBimodQuotEquiv hL hR)).trans
    (midModelQuotEquiv L)

theorem capCoeAddEquiv_smul (t : Tqᵐᵒᵖ) (x : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    capCoeAddEquiv hR hP hPL hκ (t • x) = t • capCoeAddEquiv hR hP hPL hκ x := by
  obtain ⟨b, rfl⟩ := capQuotOp_surjective t
  induction b using MulOpposite.rec' with
  | h b =>
    rw [capQuotOp_op, capRightHom_op_mk]
    change midModelQuotEquiv L (midBimodQuotEquiv hL hR (capModelQuotEquiv hP hPL hκ hR
      (envRight k Q Λ Λc j hj ν ν₀ (op b) • (show Cap k Q Λ Λc j hj ν ν₀ L from x)))) = _
    rw [LinearEquiv.map_smul, midBimodQuotEquiv_smul, midModelQuotEquiv_smul]
    rfl

/-- **`K^{λ⁺}_λ ≅ L ⊗ e T^{λ⁺}` as right `T^{λ⁺}`-modules** (arXiv:1309.3796v3, §7.3), for a cap
after `λ_j`, under the hypotheses of Lemma 7.17: the coevaluation bimodule is induced from `L`
along the diagrams at the maximum followed by the quotient map onto `T^{λ⁺}`. -/
def capCoeEquiv : CapBimodule k Q Λ Λc j hj ν ν₀ L ≃ₗ[Tqᵐᵒᵖ] IndQ where
  __ := capCoeAddEquiv hR hP hPL hκ
  map_smul' := capCoeAddEquiv_smul hR hP hPL hκ

end Categorification.Stendhal.CupCap
