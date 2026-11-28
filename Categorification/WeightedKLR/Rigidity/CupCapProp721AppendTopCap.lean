/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendTop
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendFixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapF
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapImage
import Categorification.Algebra.SpanSmulRetract

/-!
# Webster's `Fᵢ` on `K^{λ⁺}_λ` for a cap at the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap at the right end (`j = ℓ`), under the hypotheses of Lemma 7.17.
`𝔉_i(model_ν)` is `e' · model_{{i} + ν}` (`CupCap.appendTopModelEquiv`), and the isomorphism
matches the violated parts (`CupCap.map_appendTopModelEquiv_appendBotViolSub`). With the steps
shared with `j < ℓ` this identifies Webster's `Fᵢ` on `K^{λ⁺}_λ` with `e' · K^{λ⁺}_λ` at the
black weight `{i} + ν` (`CupCap.blackFCapTopImageEquiv`). For `j < ℓ` the same composite is
`CupCap.blackFCapImageEquiv`.

## Main definitions

* `CupCap.appendTopModelEquiv`: `𝔉_i(model_ν) ≅ e' · model_{{i} + ν}`, for `j = ℓ`.
* `CupCap.fixedCapEquiv`: the `e'`-fixed part of the model modulo violated diagrams is
  `e' · K^{λ⁺}_λ`.
* `CupCap.blackFCapTopImageEquiv`, `CupCap.blackFCapImageEquiv`: `Fᵢ(K^{λ⁺}_λ) ≅ e' · K^{λ⁺}_λ`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} {i : I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ
local notation "Vpᵢ" => StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "FM" => Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)
local notation "MMᵢ" => MidModel j hj Q Λ Λc νᵢ ν₀ L
local notation "BVᵢ" => midBotViolSub Q Λ Λc j hj νᵢ ν₀ L
local notation "Fx" => LinearMap.range (appendFixedIncl (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
  (hj := hj) (ν := ν) (ν₀ := ν₀) i L)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj νᵢ ν₀ L
local notation "aB1" => appendBlackStendhal Q Λ i ν 1
local notation "eK" => capLeftLin (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) L aB1
local notation "πᵢ" => plusQuotOp k Q Λ Λc j hj νᵢ ν₀
local notation "aB" => appendBlackOp Q (plusLabels Λ Λc j hj) i (ν + ν₀)

section Viol

variable (k Q Λ Λc j hj ν ν₀ i) in
/-- The scalars of the violated ideal of `T̃^{λ⁺}` at `{i} + ν`, on the opposite ring. -/
abbrev appendViolScalars : Set Tᵢ := {b | b.unop ∈ Vpᵢ}

local notation "Sᵢ" => appendViolScalars k Q Λ Λc j hj ν ν₀ i

theorem appendBotViolSub_eq_spanSmulOf :
    appendBotViolSub Q Λ Λc j hj ν ν₀ i L = spanSmulOf Sᵢ FM := by
  refine congrArg (Submodule.span Tᵢ) (Set.ext fun x => ⟨?_, ?_⟩)
  · rintro ⟨b, hb, w, rfl⟩
    exact ⟨op b, hb, w, rfl⟩
  · rintro ⟨b, hb, w, rfl⟩
    exact ⟨b.unop, hb, w, rfl⟩

theorem midBotViolSub_eq_spanSmulOf : BVᵢ = spanSmulOf Sᵢ MMᵢ := by
  refine congrArg (Submodule.span Tᵢ) (Set.ext fun x => ⟨?_, ?_⟩)
  · rintro ⟨b, hb, w, rfl⟩
    exact ⟨op b, hb, w, rfl⟩
  · rintro ⟨b, hb, w, rfl⟩
    exact ⟨b.unop, hb, w, rfl⟩

variable (i L) in
/-- The violated part of `e' · model_{{i} + ν}`, through the components of the appended
loadings. -/
abbrev appendTopViolSub : Submodule Tᵢ Fx := Submodule.comap (Submodule.subtype Fx) BVᵢ

variable (i L) in
/-- The retraction of the model at `{i} + ν` onto the components of the appended loadings. -/
def appendFixedRetract : MMᵢ →ₗ[Tᵢ] Fx :=
  (appendFixedEquiv i L).toLinearMap.comp (appendFixedProj i L)

theorem appendFixedRetract_apply (p : Fx) : appendFixedRetract i L (p : MMᵢ) = p := by
  rcases p with ⟨_, f, rfl⟩
  apply Subtype.ext
  change appendFixedIncl i L (appendFixedProj i L (appendFixedIncl i L f)) = appendFixedIncl i L f
  rw [← LinearMap.comp_apply (appendFixedProj i L), appendFixedProj_comp_appendFixedIncl,
    LinearMap.id_apply]

theorem appendTopViolSub_eq_spanSmulOf :
    appendTopViolSub i L (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) =
      spanSmulOf Sᵢ Fx := by
  rw [appendTopViolSub, midBotViolSub_eq_spanSmulOf]
  exact comap_subtype_spanSmulOf _ _ (appendFixedRetract i L) appendFixedRetract_apply

end Viol

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

section Top

variable (h : ¬ j < ℓ)

variable (hL) in
/-- **`𝔉_i(model_ν)` as `e' · model_{{i} + ν}`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j = ℓ`, under the hypotheses of Lemma 7.17. -/
def appendTopModelEquiv : FM ≃ₗ[Tᵢ] Fx :=
  (appendMidEquiv Q Λ Λc j hj ν ν₀ i L).trans
    ((appendTopPiEquiv L i hP hPL hL h hκ).trans (appendFixedEquiv i L))

variable (hL) in
theorem map_appendTopModelEquiv_appendBotViolSub :
    (appendBotViolSub Q Λ Λc j hj ν ν₀ i L).map (appendTopModelEquiv hL hP hPL hκ h).toLinearMap =
      appendTopViolSub i L := by
  rw [appendBotViolSub_eq_spanSmulOf, map_spanSmulOf _ (LinearEquiv.surjective _),
    appendTopViolSub_eq_spanSmulOf]

variable (hL) in
/-- **`𝔉_i` of the model modulo violated diagrams**, for `j = ℓ`. -/
def appendTopViolQuotEquiv :
    (FM ⧸ appendBotViolSub Q Λ Λc j hj ν ν₀ i L) ≃ₗ[Tᵢ] Fx ⧸ appendTopViolSub i L :=
  Submodule.Quotient.equiv _ _ (appendTopModelEquiv hL hP hPL hκ h)
    (map_appendTopModelEquiv_appendBotViolSub hL hP hPL hκ h)

/-- `𝔉_i(K^{λ⁺}_λ)` along `T^{λ⁺}` as `e' · model_{{i} + ν}` modulo its violated part, for
`j = ℓ`. -/
def appendCapTopEquiv :
    Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i) ≃+ Fx ⧸ appendTopViolSub i L :=
  capIndQuotEquiv.symm.trans
    ((capIndModelEquiv hR hP hPL hκ).trans (appendTopViolQuotEquiv hL hP hPL hκ h)).toAddEquiv

theorem appendCapTopEquiv_apply (x : Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)) :
    appendCapTopEquiv hR hP hPL hκ h x = appendTopViolQuotEquiv hL hP hPL hκ h
      (capIndModelEquiv hR hP hPL hκ ((capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm x)) :=
  rfl

theorem appendCapTopEquiv_smul (b : Tᵢ) (x : Ind CB (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)) :
    appendCapTopEquiv hR hP hPL hκ h (πᵢ b • x) = b • appendCapTopEquiv hR hP hPL hκ h x := by
  rw [appendCapTopEquiv_apply, appendCapTopEquiv_apply, capIndQuotEquiv_symm_smul, map_smul,
    map_smul]

/-- **Webster's `Fᵢ` on `K^{λ⁺}_λ`**, for `j = ℓ`: `e' · model_{{i} + ν}` modulo its violated
part. -/
def blackFCapTopEquiv : Ind CB aB ≃+ Fx ⧸ appendTopViolSub i L :=
  blackFCapTransport.trans (appendCapTopEquiv hR hP hPL hκ h)

theorem blackFCapTopEquiv_apply (x : Ind CB aB) :
    blackFCapTopEquiv hR hP hPL hκ h x = appendCapTopEquiv hR hP hPL hκ h (blackFCapTransport x) :=
  rfl

theorem blackFCapTopEquiv_smul (b : Tᵢ) (x : Ind CB aB) :
    blackFCapTopEquiv hR hP hPL hκ h ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm (πᵢ b) • x) =
      b • blackFCapTopEquiv hR hP hPL hκ h x := by
  rw [blackFCapTopEquiv_apply, blackFCapTopEquiv_apply, blackFCapTransport_smul,
    RingEquiv.apply_symm_apply, appendCapTopEquiv_smul]

end Top

section Fixed

variable (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (P : Submodule (StendhalAlgebra k Q (plusLabels Λ Λc j hj)
    ((Singleton.singleton i : Multiset I) + ν + ν₀))ᵐᵒᵖ
    (MidModel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L))
  (hPmem : ∀ y, y ∈ P ↔ midLeftAlg L hL hR' (appendBlackStendhal Q Λ i ν 1) y = y)

/-- The `e'`-fixed part of the model, mapped to the cap bimodule at `{i} + ν`. -/
def fixedCapHom : P →ₗ[Tᵢ] CBᵢ :=
  ((capModelRightEquiv hR' hP hPL hκ).symm.toLinearMap.comp (Submodule.mkQ BVᵢ)).comp
    (Submodule.subtype P)

theorem ker_fixedCapHom :
    LinearMap.ker (fixedCapHom hP hPL hκ hR' P) = Submodule.comap (Submodule.subtype P) BVᵢ := by
  ext y
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change (capModelRightEquiv hR' hP hPL hκ).symm (Submodule.Quotient.mk (y : _)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

include hPmem in
/-- The image of the `e'`-fixed part of the model is `e' · K^{λ⁺}_λ`. -/
theorem range_fixedCapHom :
    LinearMap.range (fixedCapHom hP hPL hκ hR' P) = LinearMap.range eK := by
  have hidem : aB1 * aB1 = aB1 := by rw [← map_mul, mul_one]
  ext c
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    have hfix := (hPmem y).1 hy
    refine ⟨fixedCapHom hP hPL hκ hR' P ⟨y, hy⟩, ?_⟩
    apply (capModelRightEquiv hR' hP hPL hκ).injective
    have hc : capModelRightEquiv hR' hP hPL hκ (fixedCapHom hP hPL hκ hR' P ⟨y, hy⟩) =
        Submodule.Quotient.mk y :=
      LinearEquiv.apply_symm_apply _ _
    rw [capModelRightEquiv_capLeftLin hR' hP hPL hκ aB1 _ y hc, hfix, hc]
  · rintro ⟨d, rfl⟩
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR' hP hPL hκ d)
    have hmem : midLeftAlg L hL hR' aB1 y ∈ P := by
      rw [hPmem, ← Module.End.mul_apply, ← map_mul, hidem]
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply (capModelRightEquiv hR' hP hPL hκ).injective
    rw [capModelRightEquiv_capLeftLin hR' hP hPL hκ aB1 d y hy.symm]
    exact LinearEquiv.apply_symm_apply _ _

/-- **The `e'`-fixed part of the model modulo violated diagrams is `e' · K^{λ⁺}_λ`**
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), as right `T̃^{λ⁺}`-modules. -/
def fixedCapEquiv : (P ⧸ Submodule.comap (Submodule.subtype P) BVᵢ) ≃ₗ[Tᵢ] LinearMap.range eK :=
  (Submodule.quotEquivOfEq _ _ (ker_fixedCapHom hP hPL hκ hR' P).symm).trans
    ((fixedCapHom hP hPL hκ hR' P).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_fixedCapHom hP hPL hκ hR' P hPmem)))

theorem fixedCapEquiv_mk (y : P) :
    (fixedCapEquiv hP hPL hκ hR' P hPmem (Submodule.Quotient.mk y) : CBᵢ) =
      fixedCapHom hP hPL hκ hR' P y := rfl

end Fixed

variable (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)

/-- **Webster's `Fᵢ` on `K^{λ⁺}_λ` is `e' · K^{λ⁺}_λ`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for a cap at the right end (`j = ℓ`), under the hypotheses of Lemma 7.17:
the underlying group of `(blackF Q Λ⁺ i (ν + ν₀)).obj K^{λ⁺}_λ` is the image of the idempotent
`e'` of the loadings ending in `i`, semilinearly (`CupCap.blackFCapTopImageEquiv_smul`). -/
def blackFCapTopImageEquiv (h : ¬ j < ℓ) : Ind CB aB ≃+ LinearMap.range eK :=
  (blackFCapTopEquiv hR hP hPL hκ h).trans
    (fixedCapEquiv hP hPL hκ hR' Fx (mem_range_appendFixedIncl_iff i hR')).toAddEquiv

theorem blackFCapTopImageEquiv_smul (h : ¬ j < ℓ) (b : Tᵢ) (x : Ind CB aB) :
    blackFCapTopImageEquiv hR hP hPL hκ hR' h
        ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm (πᵢ b) • x) =
      b • blackFCapTopImageEquiv hR hP hPL hκ hR' h x := by
  change fixedCapEquiv hP hPL hκ hR' Fx (mem_range_appendFixedIncl_iff i hR')
      (blackFCapTopEquiv hR hP hPL hκ h _) = _
  rw [blackFCapTopEquiv_smul, map_smul]
  rfl

/-- **Webster's `Fᵢ` on `K^{λ⁺}_λ` is `e' · K^{λ⁺}_λ`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`, under the hypotheses of Lemma 7.17. -/
def blackFCapImageEquiv (h : j < ℓ) : Ind CB aB ≃+ LinearMap.range eK :=
  (blackFCapEquiv hR hP hPL hκ h).trans (appendRangeCapEquiv h hR' hP hPL hκ).toAddEquiv

theorem blackFCapImageEquiv_smul (h : j < ℓ) (b : Tᵢ) (x : Ind CB aB) :
    blackFCapImageEquiv hR hP hPL hκ hR' h
        ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm (πᵢ b) • x) =
      b • blackFCapImageEquiv hR hP hPL hκ hR' h x := by
  change appendRangeCapEquiv h hR' hP hPL hκ (blackFCapEquiv hR hP hPL hκ h _) = _
  rw [blackFCapEquiv_smul, map_smul]
  rfl

end Categorification.Stendhal.CupCap
