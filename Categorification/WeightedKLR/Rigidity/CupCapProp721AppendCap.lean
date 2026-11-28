/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapViolated
import Categorification.WeightedKLR.Rigidity.CupCapFunctor
import Categorification.Algebra.InductionAlongQuotient
import Categorification.Algebra.InductionAlongQuotientModule

/-!
# `K^{λ⁺}_λ` as a right `T̃^{λ⁺}`-module, through the model

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The right action of `T^{λ⁺}` on `K^{λ⁺}_λ` restricts along the quotient map
`T̃^{λ⁺} → T^{λ⁺}` to a right `T̃^{λ⁺}`-module (`CupCap.capStendhalModule`), isomorphic to the model
modulo its bottom-violated part (`CupCap.capModelRightEquiv`). This is the input for comparing
`𝔉_i(K^{λ⁺}_λ)` with the model (`InductionAlong.indModQuotEquiv`,
`InductionAlong.indQuotEquiv`).

## Main definitions

* `CupCap.capStendhalModule`: `K^{λ⁺}_λ` as a right `T̃^{λ⁺}`-module.
* `CupCap.capModelRightEquiv`: `K^{λ⁺}_λ ≅ model / model · V_{λ⁺}` as right `T̃^{λ⁺}`-modules.
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

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L

variable (k Q Λ Λc j hj ν ν₀) in
/-- The quotient map `T̃^{λ⁺} → T^{λ⁺}` on the opposite rings. -/
def plusQuotOp : Tpᵐᵒᵖ →+* TPpᵐᵒᵖ :=
  RingHom.op (TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)).toRingHom

theorem plusQuotOp_surjective : Function.Surjective (plusQuotOp k Q Λ Λc j hj ν ν₀) := by
  intro b
  obtain ⟨a, ha⟩ := (StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj)
    (ν + ν₀)).ringCon.mkₐ_surjective (α := k) b.unop
  exact ⟨op a, congrArg op ha⟩

variable (L) in
/-- **`K^{λ⁺}_λ` as a right `T̃^{λ⁺}`-module**, through the quotient map. -/
instance capStendhalModule : Module Tpᵐᵒᵖ CB :=
  Module.compHom CB (plusQuotOp k Q Λ Λc j hj ν ν₀)

theorem capStendhal_smul (b : Tpᵐᵒᵖ) (x : CB) : b • x = plusQuotOp k Q Λ Λc j hj ν ν₀ b • x :=
  rfl

/-- The right action of `T̃^{λ⁺}` on `K^{λ⁺}_λ` is the action of `1 ⊗ b`. -/
theorem capStendhal_smul_eq (b : Tp) (x : Cap k Q Λ Λc j hj ν ν₀ L) :
    (op b • (show CB from x) : CB) =
      ((Env.mk 1 b : Env k Q Λ Λc j hj ν ν₀) • x : Cap k Q Λ Λc j hj ν ν₀ L) := by
  induction x using Submodule.Quotient.induction_on with
  | H y => rfl

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)

/-- The two quotients of the model by its bottom-violated part, as a bimodule and as a right
module, are the same. -/
def midBotViolQuotCongr :
    (MidBimod L hL hR ⧸ midBotViolEnv L hL hR) ≃+ (MidModel j hj Q Λ Λc ν ν₀ L ⧸ BV) where
  toFun q := q
  invFun q := q
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' q q' := by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      induction q' using Submodule.Quotient.induction_on with
      | H y => rfl

theorem midBotViolQuotCongr_mk (y : MidBimod L hL hR) :
    midBotViolQuotCongr hR (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (ofMidBimod L hL hR y) := rfl

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

theorem capModelQuot_envMk_one_smul (b : Tp) (x : Cap k Q Λ Λc j hj ν ν₀ L) :
    midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR
        ((Env.mk 1 b : Env k Q Λ Λc j hj ν ν₀) • x)) =
      op b • midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR x) := by
  rw [map_smul]
  generalize capModelQuotEquiv hP hPL hκ hR x = q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, midBotViolQuotCongr_mk, midBotViolQuotCongr_mk,
      ← Submodule.Quotient.mk_smul]
    congr 1
    have h := midEnvAlg_mk hR 1 b (ofMidBimod L hL hR y)
    rw [map_one, Module.End.one_apply] at h
    exact h

/-- **`K^{λ⁺}_λ` is the model modulo its bottom-violated part, as a right `T̃^{λ⁺}`-module**
(arXiv:1309.3796v3, §7.3), under the hypotheses of Lemma 7.17. -/
def capModelRightEquiv : CB ≃ₗ[Tpᵐᵒᵖ] MidModel j hj Q Λ Λc ν ν₀ L ⧸ BV where
  toFun x := midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR x)
  invFun q := (capModelQuotEquiv hP hPL hκ hR).symm ((midBotViolQuotCongr hR).symm q)
  left_inv x := by
    dsimp only
    rw [AddEquiv.symm_apply_apply]
    exact LinearEquiv.symm_apply_apply _ (show Cap k Q Λ Λc j hj ν ν₀ L from x)
  right_inv q := by
    dsimp only
    rw [LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  map_add' x y := by
    rw [← map_add]
    exact congrArg _ (map_add (capModelQuotEquiv hP hPL hκ hR) x y)
  map_smul' b x := by
    induction b using MulOpposite.rec' with
    | h b =>
    exact (congrArg (fun z => midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR z))
      (capStendhal_smul_eq b x)).trans (capModelQuot_envMk_one_smul hR hP hPL hκ b x)

theorem capModelRightEquiv_apply (x : Cap k Q Λ Λc j hj ν ν₀ L) :
    capModelRightEquiv hR hP hPL hκ x =
      midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR x) := rfl

end Categorification.Stendhal.CupCap
