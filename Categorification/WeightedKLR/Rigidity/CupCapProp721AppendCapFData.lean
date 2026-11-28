/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFFunctor

/-!
# The bimodule isomorphism `e' K_{{i} + ν} ≅ 𝔉_i(K_ν)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`, under the hypotheses of Lemma 7.17. The isomorphisms
`Φ : 𝔉_i(K_ν) ≅ e' K_{{i} + ν}` (`CupCap.appendCapEquiv` with `CupCap.appendRangeCapEquiv` for
`j < ℓ`, `CupCap.appendCapTopEquiv` with `CupCap.fixedCapEquiv` for `j = ℓ`) are built through
the model of the cap bimodule. They are right `T^{λ⁺}`-linear by construction. Here they are shown
to be left `T^λ_ν`-linear, `Φ(𝔉_i(a) w) = appendBlack(a) Φ(w)`, by tracing a generator `z ⊗ c`
through the model (`CupCap.capFModel_capLeftMul`), where the model maps intertwine the left
actions (`CupCap.appendMidMap_midLeftAlg`, `CupCap.appendTopModelEquiv_midLeftAlg`). This gives
the data `CupCap.CapFData` with `fwd = Φ⁻¹ ∘ (e' ·)` and `bwd = Φ`, and hence the natural
isomorphisms `𝔉_i ⋙ K ≅ K ⋙ 𝔉_i` on right modules.

Route hypotheses (tracked, as for the part for `𝔈_i`): `hL` (violated idempotents act by zero on
`L`), `hκ` (the cup scalars are units), `hP`, `hPL` (the pull-off identities), and `hR`, `hR'`
(the KLR relations on the model, which follow from `CupCap.midKLRRel`).

## Main definitions

* `CupCap.capFDataOfImage`: `CupCap.CapFData` from a bilinear `Φ : 𝔉_i(K_ν) ≅ e' K_{{i} + ν}`.
* `CupCap.capFImageEquivMid`, `CupCap.capFImageEquivTop`: `Φ` for `j < ℓ` and `j = ℓ`.
* `CupCap.capFDataMid`, `CupCap.capFDataTop`, `CupCap.capFOrdIsoMid`, `CupCap.capFOrdIsoTop`.

## Main results

* `CupCap.capFModel_capLeftMul`, `CupCap.capFImageEquivMid_capLeftMul`,
  `CupCap.capFImageEquivTop_capLeftMul`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} {i : I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "Tpᵢ" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj νᵢ ν₀ L
set_option hygiene false in
local notation "MM" => MidModel j hj Q Λ Λc ν ν₀ L
set_option hygiene false in
local notation "MMᵢ" => MidModel j hj Q Λ Λc νᵢ ν₀ L
set_option hygiene false in
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "aBp" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "ABV" => appendBotViolSub Q Λ Λc j hj ν ν₀ i L
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "πᵢ" => plusQuotOp k Q Λ Λc j hj νᵢ ν₀
set_option hygiene false in
local notation "aB" => appendBlackStendhal Q Λ i ν
set_option hygiene false in
local notation "aBl" => (appendBlack Q Λ i ν : TensorProductAlgebra k Q Λ ν →ₙ+*
  TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "eK" => capLeftLin (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) L (aB 1)

/-! ### The data from a bilinear isomorphism onto `e' K_{{i} + ν}` -/

section Data

/-- The idempotent `e'` acts on `K_{{i} + ν}` as `appendBlack(1)`. -/
theorem capLeftLin_appendBlack_one (c : CBᵢ) : eK c = (aBl 1 • c : CBᵢ) := by
  change (TensorProductAlgebra.mk Q Λ νᵢ (aB 1) • c : CBᵢ) = _
  rw [← appendBlack_mk Q Λ i ν 1, map_one]
  rfl

theorem capLeftLin_appendBlack_one_of_mem {x : CBᵢ} (hx : x ∈ LinearMap.range eK) :
    eK x = x := by
  obtain ⟨d, rfl⟩ := hx
  rw [capLeftLin_appendBlack_one, capLeftLin_appendBlack_one, smul_smul, ← map_mul, mul_one]

variable (Φ : Ind CB aT ≃+ LinearMap.range eK)
  (hl : ∀ (a : TA) (w : Ind CB aT),
    (Φ (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a) w) : CBᵢ) = aBl a • (Φ w : CBᵢ))
  (hr : ∀ (b : Tpᵢᵐᵒᵖ) (w : Ind CB aT), Φ (πᵢ b • w) = b • Φ w)

/-- **`e' K_{{i} + ν} ≅ 𝔉_i(K_ν)` as `CupCap.CapFData`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), from an isomorphism `Φ : 𝔉_i(K_ν) ≅ e' K_{{i} + ν}` that is left
`T^λ_ν`-linear along appending (`hl`) and right `T̃^{λ⁺}`-linear (`hr`): `fwd = Φ⁻¹ ∘ (e' ·)`,
`bwd = Φ`. -/
def capFDataOfImage : CapFData k Q Λ Λc j hj ν₀ L ν i where
  fwd := Φ.symm.toAddMonoidHom.comp (LinearMap.rangeRestrict eK).toAddMonoidHom
  bwd := (LinearMap.range eK).subtype.toAddMonoidHom.comp Φ.toAddMonoidHom
  fwd_smul_left a c := by
    apply Φ.injective
    apply Subtype.ext
    change (Φ (Φ.symm ((LinearMap.rangeRestrict eK) (aBl a • c))) : CBᵢ) =
      (Φ (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a)
        (Φ.symm ((LinearMap.rangeRestrict eK) c))) : CBᵢ)
    rw [hl, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    change eK (aBl a • c) = aBl a • eK c
    rw [capLeftLin_appendBlack_one, capLeftLin_appendBlack_one, smul_smul, smul_smul, ← map_mul,
      ← map_mul, one_mul, mul_one]
  fwd_smul_right b c := by
    obtain ⟨b, rfl⟩ := plusQuotOp_surjective (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
      (hj := hj) (ν := νᵢ) (ν₀ := ν₀) b
    apply Φ.injective
    change Φ (Φ.symm ((LinearMap.rangeRestrict eK) (πᵢ b • c))) =
      Φ (πᵢ b • Φ.symm ((LinearMap.rangeRestrict eK) c))
    rw [hr, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact Subtype.ext ((eK).map_smul b c)
  bwd_smul_left a w := hl a w
  bwd_smul_right b w := by
    obtain ⟨b, rfl⟩ := plusQuotOp_surjective (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
      (hj := hj) (ν := νᵢ) (ν₀ := ν₀) b
    change (Φ (πᵢ b • w) : CBᵢ) = πᵢ b • (Φ w : CBᵢ)
    rw [hr]
    rfl
  fwd_bwd w := by
    change Φ.symm ((LinearMap.rangeRestrict eK) (Φ w : CBᵢ)) = w
    have hw : (LinearMap.rangeRestrict eK) (Φ w : CBᵢ) = Φ w :=
      Subtype.ext (capLeftLin_appendBlack_one_of_mem (Φ w).2)
    rw [hw, AddEquiv.symm_apply_apply]
  bwd_fwd c := by
    change (Φ (Φ.symm ((LinearMap.rangeRestrict eK) c)) : CBᵢ) = aBl 1 • c
    rw [AddEquiv.apply_symm_apply]
    exact capLeftLin_appendBlack_one c

end Data

/-! ### Left linearity through the model -/

theorem capIndQuotEquiv_symm_tmul_exists (z : Corner aT) :
    ∃ z' : Corner aBp, ∀ c : CB,
      (capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm (Ind.tmul z c) =
        Submodule.Quotient.mk (Ind.tmul z' c) :=
  ⟨quotLiftCorner (φ := aBp) plusQuotOp_surjective z, fun _ => rfl⟩

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

theorem capIndModelEquiv_mk_tmul (z : Corner aBp) (c : CB) (y : MM)
    (hy : capModelRightEquiv hR hP hPL hκ c = Submodule.Quotient.mk y) :
    capIndModelEquiv hR hP hPL hκ (Submodule.Quotient.mk (Ind.tmul z c)) =
      Submodule.Quotient.mk (Ind.tmul z y) := by
  change Submodule.quotEquivOfEq _ _ indImageSub_sup_indKerSub_eq
    (indQuotSupEquiv aBp πᵢ BV (Submodule.Quotient.mk
      (Ind.tmul z (capModelRightEquiv hR hP hPL hκ c)))) = _
  rw [hy]
  change Submodule.quotEquivOfEq _ _ indImageSub_sup_indKerSub_eq
    (indQuotSupEquiv aBp πᵢ BV
      (Submodule.Quotient.mk (Ind.map (Submodule.mkQ BV) (Ind.tmul z y)))) = _
  rw [indQuotSupEquiv_mk]
  rfl

omit [DecidableEq I] in
/-- Additive maps out of an induced module agree once they agree on the generators `z ⊗ n`. -/
private theorem indAddHom_ext' {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B} {N : Type}
    [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] {f g : Ind N φ →+ P}
    (h : ∀ z n, f (Ind.tmul z n) = g (Ind.tmul z n)) : f = g :=
  AddMonoidHom.ext fun t => by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n => exact h z n
    | add s t hs ht => rw [map_add, map_add, hs, ht]

section Model

variable (Ψ : (Ind MM aBp ⧸ ABV) →+ CBᵢ) (G : Ind MM aBp →+ MMᵢ)
  (hΨ : ∀ x, capModelRightEquiv hR' hP hPL hκ (Ψ (Submodule.Quotient.mk x)) =
    Submodule.Quotient.mk (G x))
  (hG : ∀ (z : StendhalAlgebra k Q Λ ν) (x : Ind MM aBp),
    G (Ind.map (midLeftLin ν hL hR z) x) = midLeftAlg L hL hR' (aB z) (G x))

/-- `𝔉_i(K_ν) → K_{{i} + ν}` through `𝔉_i(model_ν)` and a map `Ψ` out of its quotient. -/
def capFModelHom : Ind CB aT →+ CBᵢ :=
  Ψ.comp ((capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm.trans
    (capIndModelEquiv hR hP hPL hκ).toAddEquiv).toAddMonoidHom

theorem capFModelHom_apply (x : Ind CB aT) :
    capFModelHom hR hP hPL hκ Ψ x =
      Ψ (capIndModelEquiv hR hP hPL hκ ((capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm x)) :=
  rfl

include hΨ hG in
theorem capFModelHom_capLeftMul_tmul (a : TA) (z : Corner aT) (c : CB) :
    capFModelHom hR hP hPL hκ Ψ (Ind.tmul z (a • c)) =
      (aBl a • capFModelHom hR hP hPL hκ Ψ (Ind.tmul z c) : CBᵢ) := by
  obtain ⟨z', hz'⟩ := capIndQuotEquiv_symm_tmul_exists (L := L) (hj := hj) z
  obtain ⟨a', ha'⟩ :=
    (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mkₐ_surjective (α := k) a
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  have hac : a • c = capLeftLin L a' c := by rw [← ha']; rfl
  have hm : aBl a = TensorProductAlgebra.mk Q Λ νᵢ (aB a') := by
    rw [← ha']; exact appendBlack_mk Q Λ i ν a'
  rw [capFModelHom_apply, capFModelHom_apply, hac, hz', hz', hm,
    capIndModelEquiv_mk_tmul hR hP hPL hκ z' _ _
      (capModelRightEquiv_capLeftLin hR hP hPL hκ a' c y hy.symm),
    capIndModelEquiv_mk_tmul hR hP hPL hκ z' c y hy.symm]
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  refine (hΨ _).trans ?_
  refine Eq.trans ?_ (capModelRightEquiv_capLeftLin hR' hP hPL hκ (aB a') _ _ (hΨ _)).symm
  rw [← hG]
  rfl

include hΨ hG in
/-- **Left linearity through the model** (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21):
if a map `Ψ` out of `𝔉_i(model_ν)` modulo its violated part lifts, in the model, a map of models
`G` that carries `𝔉_i` of the left action of `z` to the action of `appendBlack(z)`, then the
composite `𝔉_i(K_ν) → K_{{i} + ν}` through `CupCap.capIndModelEquiv` is left `T^λ_ν`-linear along
appending. -/
theorem capFModel_capLeftMul (a : TA) (w : Ind CB aT) :
    capFModelHom hR hP hPL hκ Ψ (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a) w) =
      (aBl a • capFModelHom hR hP hPL hκ Ψ w : CBᵢ) :=
  DFunLike.congr_fun (indAddHom_ext'
    (f := (capFModelHom hR hP hPL hκ Ψ).comp
      (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a)).toAddMonoidHom)
    (g := (AddMonoidHom.mk' (fun c : CBᵢ => aBl a • c) (smul_add (aBl a))).comp
      (capFModelHom hR hP hPL hκ Ψ))
    fun z c => capFModelHom_capLeftMul_tmul hR hR' hP hPL hκ Ψ G hΨ hG a z c) w

end Model

/-! ### `j < ℓ` -/

section Mid

variable (h : j < ℓ)

/-- **`𝔉_i(K_ν) ≅ e' K_{{i} + ν}`** for `j < ℓ` (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), at the black weight `({i} + ν) + ν₀` of `T^{λ⁺}`. -/
def capFImageEquivMid : Ind CB aT ≃+ LinearMap.range eK :=
  (appendCapEquiv hR hP hPL hκ h).trans (appendRangeCapEquiv h hR' hP hPL hκ).toAddEquiv

/-- `𝔉_i(model_ν)` modulo its violated part, to `K_{{i} + ν}`, for `j < ℓ`. -/
def capFPsiMid : (Ind MM aBp ⧸ ABV) →+ CBᵢ :=
  (LinearMap.range eK).subtype.toAddMonoidHom.comp
    ((appendViolQuotEquiv ν i L h).toAddEquiv.trans
      (appendRangeCapEquiv h hR' hP hPL hκ).toAddEquiv).toAddMonoidHom

theorem capFPsiMid_mk (x : Ind MM aBp) :
    capModelRightEquiv hR' hP hPL hκ (capFPsiMid hR' hP hPL hκ h (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (appendMidMap Q Λ Λc j hj ν ν₀ i L h x) :=
  LinearEquiv.apply_symm_apply (capModelRightEquiv hR' hP hPL hκ)
    (Submodule.Quotient.mk (appendMidMap Q Λ Λc j hj ν ν₀ i L h x))

theorem capFImageEquivMid_coe (w : Ind CB aT) :
    (capFImageEquivMid hR hR' hP hPL hκ h w : CBᵢ) =
      capFModelHom hR hP hPL hκ (capFPsiMid hR' hP hPL hκ h) w :=
  rfl

/-- **`Φ` is left `T^λ_ν`-linear along appending**, for `j < ℓ` (arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21). -/
theorem capFImageEquivMid_capLeftMul (a : TA) (w : Ind CB aT) :
    (capFImageEquivMid hR hR' hP hPL hκ h (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a) w) : CBᵢ) =
      aBl a • (capFImageEquivMid hR hR' hP hPL hκ h w : CBᵢ) := by
  rw [capFImageEquivMid_coe, capFImageEquivMid_coe]
  exact capFModel_capLeftMul hR hR' hP hPL hκ (capFPsiMid hR' hP hPL hκ h)
    (appendMidMap Q Λ Λc j hj ν ν₀ i L h).toAddMonoidHom (capFPsiMid_mk hR' hP hPL hκ h)
    (fun z x => appendMidMap_midLeftAlg ν i hL h hR hR' z x) a w

theorem capFImageEquivMid_smul (b : Tpᵢᵐᵒᵖ) (w : Ind CB aT) :
    capFImageEquivMid hR hR' hP hPL hκ h (πᵢ b • w) =
      b • capFImageEquivMid hR hR' hP hPL hκ h w :=
  (congrArg (appendRangeCapEquiv h hR' hP hPL hκ) (appendCapEquiv_smul hR hP hPL hκ h b w)).trans
    (map_smul _ _ _)

/-- **`e' K_{{i} + ν} ≅ 𝔉_i(K_ν)`** for `j < ℓ`, as `CupCap.CapFData`. Route hypotheses
(tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hR'`. -/
def capFDataMid : CapFData k Q Λ Λc j hj ν₀ L ν i :=
  capFDataOfImage (capFImageEquivMid hR hR' hP hPL hκ h)
    (capFImageEquivMid_capLeftMul hR hR' hP hPL hκ h) (capFImageEquivMid_smul hR hR' hP hPL hκ h)

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on right modules for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21). Route hypotheses (tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hR'`. -/
def capFOrdIsoMid :
    blackF Q Λ i ν ⋙ ordTensor
        (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ
        (TensorProductAlgebra k Q Λ νᵢ)ᵐᵒᵖ (OpBimodule (TensorProductAlgebra k Q Λ νᵢ) CBᵢ) ≅
      ordTensor (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ TAᵐᵒᵖ
          (OpBimodule TA CB) ⋙ InductionAlong.functor.{0, 0} aT :=
  capFOrdIso (capFDataMid hR hR' hP hPL hκ h)

end Mid

/-! ### `j = ℓ` -/

section Top

variable (h : ¬ j < ℓ)

/-- **`𝔉_i(K_ν) ≅ e' K_{{i} + ν}`** for a cap at the right end, `j = ℓ` (arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), at the black weight `({i} + ν) + ν₀` of `T^{λ⁺}`. -/
def capFImageEquivTop : Ind CB aT ≃+ LinearMap.range eK :=
  (appendCapTopEquiv hR hP hPL hκ h).trans
    (fixedCapEquiv hP hPL hκ hR' _ (mem_range_appendFixedIncl_iff i hR')).toAddEquiv

/-- `𝔉_i(model_ν)` modulo its violated part, to `K_{{i} + ν}`, for `j = ℓ`. -/
def capFPsiTop : (Ind MM aBp ⧸ ABV) →+ CBᵢ :=
  (LinearMap.range eK).subtype.toAddMonoidHom.comp
    ((appendTopViolQuotEquiv hL hP hPL hκ h).toAddEquiv.trans
      (fixedCapEquiv hP hPL hκ hR' _
        (mem_range_appendFixedIncl_iff i hR')).toAddEquiv).toAddMonoidHom

variable (hL) in
/-- The model map `𝔉_i(model_ν) → model_{{i} + ν}` for `j = ℓ`. -/
def capFModelMapTop : Ind MM aBp →+ MMᵢ :=
  AddMonoidHom.mk' (fun x => (appendTopModelEquiv hL hP hPL hκ h x : MMᵢ)) fun x y =>
    congrArg Subtype.val (LinearEquiv.map_add (appendTopModelEquiv hL hP hPL hκ h) x y)

theorem capFPsiTop_mk (x : Ind MM aBp) :
    capModelRightEquiv hR' hP hPL hκ (capFPsiTop hR' hP hPL hκ h (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (capFModelMapTop hL hP hPL hκ h x) :=
  LinearEquiv.apply_symm_apply (capModelRightEquiv hR' hP hPL hκ)
    (Submodule.Quotient.mk (capFModelMapTop hL hP hPL hκ h x))

theorem capFImageEquivTop_coe (w : Ind CB aT) :
    (capFImageEquivTop hR hR' hP hPL hκ h w : CBᵢ) =
      capFModelHom hR hP hPL hκ (capFPsiTop hR' hP hPL hκ h) w :=
  rfl

/-- **`Φ` is left `T^λ_ν`-linear along appending**, for `j = ℓ` (arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21). -/
theorem capFImageEquivTop_capLeftMul (a : TA) (w : Ind CB aT) :
    (capFImageEquivTop hR hR' hP hPL hκ h (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a) w) : CBᵢ) =
      aBl a • (capFImageEquivTop hR hR' hP hPL hκ h w : CBᵢ) := by
  rw [capFImageEquivTop_coe, capFImageEquivTop_coe]
  exact capFModel_capLeftMul hR hR' hP hPL hκ (capFPsiTop hR' hP hPL hκ h)
    (capFModelMapTop hL hP hPL hκ h) (capFPsiTop_mk hR' hP hPL hκ h)
    (fun z x => appendTopModelEquiv_midLeftAlg ν i hP hPL hκ h hR hR' z x) a w

theorem capFImageEquivTop_smul (b : Tpᵢᵐᵒᵖ) (w : Ind CB aT) :
    capFImageEquivTop hR hR' hP hPL hκ h (πᵢ b • w) =
      b • capFImageEquivTop hR hR' hP hPL hκ h w :=
  (congrArg (fixedCapEquiv hP hPL hκ hR' _ (mem_range_appendFixedIncl_iff i hR'))
    (appendCapTopEquiv_smul hR hP hPL hκ h b w)).trans (map_smul _ _ _)

/-- **`e' K_{{i} + ν} ≅ 𝔉_i(K_ν)`** for `j = ℓ`, as `CupCap.CapFData`. Route hypotheses
(tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hR'`. -/
def capFDataTop : CapFData k Q Λ Λc j hj ν₀ L ν i :=
  capFDataOfImage (capFImageEquivTop hR hR' hP hPL hκ h)
    (capFImageEquivTop_capLeftMul hR hR' hP hPL hκ h) (capFImageEquivTop_smul hR hR' hP hPL hκ h)

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on right modules for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21). Route hypotheses (tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hR'`. -/
def capFOrdIsoTop :
    blackF Q Λ i ν ⋙ ordTensor
        (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ
        (TensorProductAlgebra k Q Λ νᵢ)ᵐᵒᵖ (OpBimodule (TensorProductAlgebra k Q Λ νᵢ) CBᵢ) ≅
      ordTensor (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ TAᵐᵒᵖ
          (OpBimodule TA CB) ⋙ InductionAlong.functor.{0, 0} aT :=
  capFOrdIso (capFDataTop hR hR' hP hPL hκ h)

end Top

end Categorification.Stendhal.CupCap
