/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapInd

/-!
# `e' · model` modulo violated diagrams is `e' · K^{λ⁺}_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for `j < ℓ`. The image of `e' · model_{{i} + ν}` in the cap bimodule at the
black weight `{i} + ν` is `e' · K^{λ⁺}_λ`, the image of the left action of the idempotent `e'` of
the loadings ending in `i` (`CupCap.appendRangeCapEquiv`). Together with
`CupCap.appendCapEquiv` this identifies `𝔉_i(K^{λ⁺}_λ)` with `e' · K^{λ⁺}_λ` at `{i} + ν`.

## Main definitions

* `CupCap.capLeftLin`: the left action of `a ∈ T̃^λ` on `K^{λ⁺}_λ`, right `T̃^{λ⁺}`-linear.
* `CupCap.appendRangeCapEquiv`: `e' · model_{{i} + ν} / violated ≅ e' · K^{λ⁺}_λ`.
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

section Weight

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L

variable (L) in
/-- **The left action of `a ∈ T̃^λ` on `K^{λ⁺}_λ`**, as a right `T̃^{λ⁺}`-linear map. -/
def capLeftLin (a : StendhalAlgebra k Q Λ ν) : CB →ₗ[Tpᵐᵒᵖ] CB where
  toFun c := (show CB from
    ((Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • (show Cap k Q Λ Λc j hj ν ν₀ L from c)))
  map_add' c c' := smul_add (Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀)
    (show Cap k Q Λ Λc j hj ν ν₀ L from c) (show Cap k Q Λ Λc j hj ν ν₀ L from c')
  map_smul' b c := by
    induction b using MulOpposite.rec' with
    | h b =>
    refine (congrArg (fun x : Cap k Q Λ Λc j hj ν ν₀ L => (Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • x)
      (capStendhal_smul_eq b c)).trans ?_
    refine Eq.trans ?_ (capStendhal_smul_eq b
      ((Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • (show Cap k Q Λ Λc j hj ν ν₀ L from c))).symm
    change ((Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • (Env.mk 1 b : Env k Q Λ Λc j hj ν ν₀) •
        (show Cap k Q Λ Λc j hj ν ν₀ L from c) : Cap k Q Λ Λc j hj ν ν₀ L) =
      (Env.mk 1 b : Env k Q Λ Λc j hj ν ν₀) • (Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) •
        (show Cap k Q Λ Λc j hj ν ν₀ L from c)
    rw [smul_smul, smul_smul, Env.mk_mul_mk, Env.mk_mul_mk, one_mul, one_mul, mul_one, mul_one]

theorem capLeftLin_apply (a : StendhalAlgebra k Q Λ ν) (c : CB) :
    (capLeftLin L a c : Cap k Q Λ Λc j hj ν ν₀ L) =
      (Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • (show Cap k Q Λ Λc j hj ν ν₀ L from c) := rfl

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- In the model, the left action of `a` on `K^{λ⁺}_λ` is the action of `a` on a lift. -/
theorem capModelRightEquiv_capLeftLin (a : StendhalAlgebra k Q Λ ν) (c : CB)
    (y : MidModel j hj Q Λ Λc ν ν₀ L)
    (hy : capModelRightEquiv hR hP hPL hκ c = Submodule.Quotient.mk y) :
    capModelRightEquiv hR hP hPL hκ (capLeftLin L a c) =
      Submodule.Quotient.mk (midLeftAlg L hL hR a y) := by
  change midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR
    (show Cap k Q Λ Λc j hj ν ν₀ L from c)) = _ at hy
  change midBotViolQuotCongr hR (capModelQuotEquiv hP hPL hκ hR
    ((Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • (show Cap k Q Λ Λc j hj ν ν₀ L from c))) = _
  rw [map_smul]
  revert hy
  generalize capModelQuotEquiv hP hPL hκ hR (show Cap k Q Λ Λc j hj ν ν₀ L from c) = q
  induction q using Submodule.Quotient.induction_on with
  | H y' =>
    intro hy
    rw [← Submodule.Quotient.mk_smul, midBotViolQuotCongr_mk]
    rw [midBotViolQuotCongr_mk, Submodule.Quotient.eq] at hy
    rw [Submodule.Quotient.eq]
    have h1 : ofMidBimod L hL hR ((Env.mk a 1 : Env k Q Λ Λc j hj ν ν₀) • y') =
        midLeftAlg L hL hR a (ofMidBimod L hL hR y') := by
      have h := midEnvAlg_mk hR a 1 (ofMidBimod L hL hR y')
      rw [op_one, one_smul] at h
      exact h
    rw [h1, ← map_sub]
    exact midLeftAlg_mem_midBotViolSub_of_mem hR a hy

end Weight

variable {i : I} (h : j < ℓ)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj νᵢ ν₀ L
local notation "BVᵢ" => midBotViolSub Q Λ Λc j hj νᵢ ν₀ L
local notation "Rg" => LinearMap.range (toAppendMid Q Λ Λc j hj ν ν₀ i L h)
local notation "aB1" => appendBlackStendhal Q Λ i ν 1
local notation "eK" => capLeftLin (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) L aB1

variable (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
variable (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- `e' · model_{{i} + ν}` mapped to the cap bimodule at `{i} + ν`. -/
def appendRangeCapHom : Rg →ₗ[Tᵢ] CBᵢ :=
  ((capModelRightEquiv hR' hP hPL hκ).symm.toLinearMap.comp (Submodule.mkQ BVᵢ)).comp
    (Submodule.subtype Rg)

theorem ker_appendRangeCapHom :
    LinearMap.ker (appendRangeCapHom h hR' hP hPL hκ) = appendRangeViolSub ν i L h := by
  ext y
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change (capModelRightEquiv hR' hP hPL hκ).symm (Submodule.Quotient.mk (y : _)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- The image of `e' · model_{{i} + ν}` is `e' · K^{λ⁺}_λ`. -/
theorem range_appendRangeCapHom :
    LinearMap.range (appendRangeCapHom h hR' hP hPL hκ) = LinearMap.range eK := by
  have hidem : aB1 * aB1 = aB1 := by rw [← map_mul, mul_one]
  ext c
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    have hfix := (mem_range_toAppendMid_iff ν i hL h hR' y).1 hy
    refine ⟨appendRangeCapHom h hR' hP hPL hκ ⟨y, hy⟩, ?_⟩
    apply (capModelRightEquiv hR' hP hPL hκ).injective
    have hc : capModelRightEquiv hR' hP hPL hκ (appendRangeCapHom h hR' hP hPL hκ ⟨y, hy⟩) =
        Submodule.Quotient.mk y :=
      LinearEquiv.apply_symm_apply _ _
    rw [capModelRightEquiv_capLeftLin hR' hP hPL hκ aB1 _ y hc, hfix, hc]
  · rintro ⟨d, rfl⟩
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR' hP hPL hκ d)
    have hmem : midLeftAlg L hL hR' aB1 y ∈ Rg := by
      rw [mem_range_toAppendMid_iff ν i hL h hR', ← Module.End.mul_apply, ← map_mul, hidem]
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply (capModelRightEquiv hR' hP hPL hκ).injective
    rw [capModelRightEquiv_capLeftLin hR' hP hPL hκ aB1 d y hy.symm]
    exact LinearEquiv.apply_symm_apply _ _

/-- **`e' · model_{{i} + ν}` modulo violated diagrams is `e' · K^{λ⁺}_λ`** (arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21), for `j < ℓ`, as right `T̃^{λ⁺}`-modules. -/
def appendRangeCapEquiv :
    (Rg ⧸ appendRangeViolSub ν i L h) ≃ₗ[Tᵢ] LinearMap.range eK :=
  (Submodule.quotEquivOfEq _ _ (ker_appendRangeCapHom h hR' hP hPL hκ).symm).trans
    ((appendRangeCapHom h hR' hP hPL hκ).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_appendRangeCapHom h hR' hP hPL hκ)))

theorem appendRangeCapEquiv_mk (y : Rg) :
    (appendRangeCapEquiv h hR' hP hPL hκ (Submodule.Quotient.mk y) : CBᵢ) =
      appendRangeCapHom h hR' hP hPL hκ y := rfl

end Categorification.Stendhal.CupCap
