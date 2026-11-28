/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendLambda

/-!
# The comparison map and the action of `λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). The comparison
`𝔉_i(model_ν) → model_{{i} + ν}` (`CupCap.appendMidMap`) carries the action of a sliding diagram
`Y` at `ν` to the action of any sliding diagram `Z` at `{i} + ν` that agrees with `appendPlus Y`
between `σ(1)` and `e'` (`CupCap.appendMidMap_map_midEnd_of`). Taking for `Z` the diagrams of the
appended generators, the comparison intertwines the action of the KLR algebra of `λ` at `ν` with
the action at `{i} + ν` along `appendLam` (`CupCap.appendMidMap_midKLRAct`), and the action of
`T̃^λ_ν` with the action of `T̃^λ_{{i} + ν}` along appending the strand
(`CupCap.appendMidMap_midLeftAlg`).

## Main definitions

* `CupCap.midKLRActLin`, `CupCap.midLeftLin`: the left actions as right-module maps.

## Main results

* `CupCap.appendMidMap_map_midEnd_of`, `CupCap.appendMidMap_midFree`.
* `CupCap.appendMidMap_midKLRAct`, `CupCap.appendMidMap_midLeftAlg`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rpᵢ" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (νᵢ + ν₀))
local notation "e''" => appendIdemPlus Q Λ Λc j hj ν ν₀ i
local notation "σ'" => midStendhal j hj Q Λ Λc νᵢ ν₀ 1
local notation "e⁺" => appendBlackPlus Q Λ Λc j hj ν ν₀ i 1

omit [DecidableEq I] in
theorem sandwich_absorb' {R : Type*} [Ring R] {e s B C X : R} (h1 : e * s = e) (h2 : s * e = e)
    (h3 : e * e = e) (hBC : s * C * e = e * B * e) :
    e * s * (e * B * e * X) = s * C * s * (e * s * X) :=
  calc e * s * (e * B * e * X) = e * s * e * B * e * X := by simp only [mul_assoc]
    _ = e * B * e * X := by rw [h1, h3]
    _ = s * C * e * X := by rw [hBC]
    _ = s * C * (s * (e * s)) * X := by rw [h1, h2]
    _ = s * C * s * (e * s * X) := by simp only [mul_assoc]

theorem appendIdemPlus_mul_appendBlackPlus_one (h : j < ℓ) : e'' * e⁺ = e'' := by
  rw [← midStendhal_one_mul_appendBlackPlus_one ν i h, mul_assoc, ← map_mul, one_mul]

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
variable {L}
variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
  op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

/-- **The comparison and the sliding diagrams** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`: if `Z` slides at `{i} + ν` and `σ(1) Z e' = e' appendPlus(Y) e'`,
the comparison carries `𝔉_i` of the action of `Y` to the action of `Z`. -/
theorem appendMidMap_map_midEnd_of (h : j < ℓ) {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    {Z : Rpᵢ} (hZ : MidSlides j hj Q Λ Λc νᵢ ν₀ Z)
    (hYZ : σ' * botMap k Q Λ Λc j hj νᵢ ν₀ Z * e'' =
      e'' * botMap k Q Λ Λc j hj νᵢ ν₀ (appendPlus Q Λ Λc j hj ν ν₀ i Y) * e'')
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    appendMidMap Q Λ Λc j hj ν ν₀ i L h (Ind.map (midEnd L hL hY) x) =
      midEnd L hL hZ (appendMidMap Q Λ Λc j hj ν ν₀ i L h x) := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul z t =>
  induction t using Ind.induction_on with
  | zero => simp only [Ind.tmul_zero, map_zero]
  | add a b ha hb => simp only [Ind.tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
  | tmul w v =>
    have hA : ∀ x, (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i x).unop =
        appendBlackPlus Q Λ Λc j hj ν ν₀ i x.unop := fun _ => rfl
    have key : e'' * σ' * appendBlackPlus Q Λ Λc j hj ν ν₀ i
          (midStendhal j hj Q Λ Λc ν ν₀ 1 * botMap k Q Λ Λc j hj ν ν₀ Y *
            midStendhal j hj Q Λ Λc ν ν₀ 1 * w.1.unop) * z.1.unop =
        σ' * botMap k Q Λ Λc j hj νᵢ ν₀ Z * σ' *
          (e'' * σ' * appendBlackPlus Q Λ Λc j hj ν ν₀ i w.1.unop) * z.1.unop := by
      congr 1
      rw [map_mul, map_mul, map_mul, appendBlackPlus_midStendhal_one ν i h, appendBlackPlus_botMap]
      exact sandwich_absorb' (appendIdemPlus_mul_midStendhal_one ν i h)
        (midStendhal_one_mul_appendIdemPlus ν i h) (appendIdemPlus_mul_self ν i h) hYZ
    change Ind.tmul ⟨z.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
        (w.1 * midElt j hj Q Λ Λc ν ν₀ Y) * appendMidOp Q Λ Λc j hj ν ν₀ i 1, _⟩ v =
      Ind.tmul ⟨z.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i w.1 *
        appendMidOp Q Λ Λc j hj ν ν₀ i 1 * midElt j hj Q Λ Λc νᵢ ν₀ Z, _⟩ v
    congr 1
    apply Subtype.ext
    apply MulOpposite.unop_injective
    simp only [midElt, unop_mul, unop_op, hA, appendMidOp_apply ν i h, midOp_apply, unop_one]
    simp only [mul_assoc] at key ⊢
    exact key

local notation "Fν" => FreeAlgebra k (Gen (stendhalWeight ℓ ν))
local notation "Fνᵢ" => FreeAlgebra k (Gen (stendhalWeight ℓ νᵢ))
local notation "Ap" => appendPlus Q Λ Λc j hj ν ν₀ i
local notation "AL" => appendLam Q Λ ν i
local notation "mkν" => KLRAlgebra.mk k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "mkνᵢ" => KLRAlgebra.mk k (stendhalQ Q Λ) (stendhalWeight ℓ νᵢ)
local notation "bot'" => botMap k Q Λ Λc j hj νᵢ ν₀

theorem appendCut_of_eq (h : j < ℓ) (Y : Rp) :
    σ' * bot' (Ap Y) * e'' = e'' * bot' (Ap Y) * e'' := by
  have hB : bot' (Ap Y) = e⁺ * bot' (Ap Y) := by
    rw [← appendBlackPlus_botMap, ← map_mul, one_mul]
  rw [hB, ← mul_assoc σ', midStendhal_one_mul_appendBlackPlus_one ν i h, ← hB]

/-- The appended idempotent `∑_s e(s i)` on the free algebra of `λ` at `{i} + ν`. -/
abbrev appendIdemFree : Fνᵢ :=
  ∑ s : Seq (stendhalWeight ℓ ν), fe k _ (appendBlackLoading i ν s)

theorem midFree_appendIdemFree :
    (midFree j hj Q Λ Λc νᵢ ν₀ (appendIdemFree ν i)).val = appendIdemKLR (hj := hj) (ν₀ := ν₀)
      (Q := Q) (Λ := Λ) (Λc := Λc) ν i := by
  rw [appendIdemFree, map_sum, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun s _ => midFree_fe _

theorem appendLam_one_eq_mk : AL 1 = mkνᵢ (appendIdemFree ν i) := by
  rw [appendLam_one, appendIdemFree, map_sum]
  rfl

theorem botMap_appendIdemKLR :
    bot' (appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i) = e'' := rfl

/-- One step of the comparison of the actions of `λ`. -/
theorem appendMidMap_step (h : j < ℓ) (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (a : Fν)
    (a' : Fνᵢ) (happ : AL (mkν a) = mkνᵢ a')
    (hYZ : σ' * bot' (midFree j hj Q Λ Λc νᵢ ν₀ a').val * e'' =
      e'' * bot' (Ap (midFree j hj Q Λ Λc ν ν₀ a).val) * e'')
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    appendMidMap Q Λ Λc j hj ν ν₀ i L h
        (Ind.map (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2)) x) =
      midKLRAct hR' (AL (mkν a)) (appendMidMap Q Λ Λc j hj ν ν₀ i L h x) := by
  rw [happ, midKLRAct_mk, midEndAlg_apply]
  exact appendMidMap_map_midEnd_of ν i hL h _ _ hYZ x

theorem ind_map_add.{u, w} {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B} {N N' : Type w}
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N'] (f g : N →ₗ[A] N')
    (x : Ind N φ) : Ind.map (f + g) x = Ind.map f x + Ind.map g x := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul z n => simp only [Ind.map_tmul, LinearMap.add_apply, Ind.tmul_add]
  | add a b ha hb => simp only [map_add, ha, hb]; abel

/-- **The comparison intertwines the actions of `λ`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`, on the free algebra: `𝔉_i` of the action of a word `a` at `ν` is
carried to the action of its appended image `appendLam a` at `{i} + ν`. -/
theorem appendMidMap_midFree (h : j < ℓ) (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (a : Fν)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    appendMidMap Q Λ Λc j hj ν ν₀ i L h
        (Ind.map (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2)) x) =
      midKLRAct hR' (AL (mkν a)) (appendMidMap Q Λ Λc j hj ν ν₀ i L h x) := by
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 c =>
    refine appendMidMap_step ν i hL h hR' _ (algebraMap k Fνᵢ c * appendIdemFree ν i) ?_ ?_ x
    · rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, appendLam_one_eq_mk,
        map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    · have hl : (midFree j hj Q Λ Λc νᵢ ν₀ (algebraMap k Fνᵢ c * appendIdemFree ν i)).val =
          c • appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i := by
        rw [map_mul, AlgHom.commutes, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
          midFree_appendIdemFree, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      have hr : (midFree j hj Q Λ Λc ν ν₀ (algebraMap k Fν c)).val = c • (1 : Rp) := by
        rw [AlgHom.commutes, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]
      have he : bot' (Ap 1) = e⁺ := by rw [← appendBlackPlus_botMap, map_one]
      rw [hl, hr, map_smul, map_smul, map_smul, botMap_appendIdemKLR, he, mul_smul_comm,
        smul_mul_assoc, mul_smul_comm, smul_mul_assoc, midStendhal_one_mul_appendIdemPlus ν i h,
        appendIdemPlus_mul_self ν i h, appendIdemPlus_mul_appendBlackPlus_one ν i h,
        appendIdemPlus_mul_self ν i h]
  | grade1 g =>
    cases g with
    | idem t =>
      refine appendMidMap_step ν i hL h hR' _ (fe k _ (appendBlackLoading i ν t)) ?_ ?_ x
      · exact appendLam_e t
      · rw [midFree_fe, midFree_fe, ← appendPlus_midIdem ν i h]
        exact appendCut_of_eq ν i h _
    | dot a =>
      refine appendMidMap_step ν i hL h hR' _
        (fx k _ (appendStrand ν i a) * appendIdemFree ν i) ?_ ?_ x
      · change AL (KLRAlgebra.x a) = _
        rw [appendLam_x, appendLam_one_eq_mk, map_mul]
        congr 2
      · rw [map_mul, Subalgebra.coe_mul, midFree_fx, midFree_fx, midFree_appendIdemFree,
          ← appendPlus_midDot ν i h]
        exact appendCut_of_eq ν i h _
    | cross p =>
      by_cases hp : p + 1 < Multiset.card (stendhalWeight ℓ ν)
      · refine appendMidMap_step ν i hL h hR' _ (fψ k _ p * appendIdemFree ν i) ?_ ?_ x
        · change AL (KLRAlgebra.ψ p) = _
          rw [appendLam_ψ hp, appendLam_one_eq_mk, map_mul]
          rfl
        · rw [map_mul, Subalgebra.coe_mul, midFree_fψ, midFree_fψ, midFree_appendIdemFree,
            ← appendPlus_midCross ν i h hp]
          exact appendCut_of_eq ν i h _
      · refine appendMidMap_step ν i hL h hR' _ 0 ?_ ?_ x
        · change AL (KLRAlgebra.ψ p) = _
          rw [KLRAlgebra.ψ_eq_zero p (by omega), map_zero, map_zero]
        · have h0 : midCross j hj Q Λ Λc ν ν₀ p = 0 :=
            Finset.sum_eq_zero fun s _ => by simp [midCrossAt, hp]
          rw [midFree_fψ, h0, map_zero, map_zero, ZeroMemClass.coe_zero, map_zero, mul_zero,
            zero_mul, mul_zero, zero_mul]
  | mul a b ha hb =>
    have hab : midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ (a * b)).2) =
        (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2)).comp
          (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ b).2)) := by
      rw [← midEnd_mul]
      exact midEnd_eq_of_eq hL _ _ (by rw [map_mul, Subalgebra.coe_mul])
    rw [hab, Ind.map_comp, LinearMap.comp_apply, ha, hb, map_mul, map_mul, map_mul,
      Module.End.mul_apply]
  | add a b ha hb =>
    have hab : midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ (a + b)).2) =
        midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2) +
          midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ b).2) := by
      rw [← midEnd_add]
      exact midEnd_eq_of_eq hL _ _ (by rw [map_add, Subalgebra.coe_add])
    rw [hab, ind_map_add, map_add, ha, hb, map_add, map_add, map_add, LinearMap.add_apply]

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

/-- The action of a diagram of `λ` on the model, as a map of right `T̃^{λ⁺}`-modules. -/
def midKLRActLin (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (w : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    MidModel j hj Q Λ Λc ν ν₀ L →ₗ[Tpᵐᵒᵖ] MidModel j hj Q Λ Λc ν ν₀ L where
  toFun := midKLRAct hR w
  map_add' := map_add _
  map_smul' b y := midKLRAct_smul hR w b y

/-- The action of `T̃^λ` on the model, as a map of right `T̃^{λ⁺}`-modules. -/
def midLeftLin (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (z : StendhalAlgebra k Q Λ ν) :
    MidModel j hj Q Λ Λc ν ν₀ L →ₗ[Tpᵐᵒᵖ] MidModel j hj Q Λ Λc ν ν₀ L where
  toFun := midLeftAlg L hL hR z
  map_add' := map_add _
  map_smul' b y := midLeftAlg_smul hR z b y

/-- **The comparison intertwines the actions of the KLR algebra of `λ`**
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `j < ℓ`: `𝔉_i` of the action of `w`
at `ν` is carried to the action of `appendLam w` at `{i} + ν`. -/
theorem appendMidMap_midKLRAct (h : j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL)
    (w : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    appendMidMap Q Λ Λc j hj ν ν₀ i L h (Ind.map (midKLRActLin ν hL hR w) x) =
      midKLRAct hR' (AL w) (appendMidMap Q Λ Λc j hj ν ν₀ i L h x) := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective w
  have hw : midKLRActLin ν hL hR (mkν a) =
      midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2) :=
    LinearMap.ext fun y => by
      change midKLRAct hR (mkν a) y = _
      rw [midKLRAct_mk, midEndAlg_apply]
  rw [hw]
  exact appendMidMap_midFree ν i hL h hR' a x

/-- **The comparison intertwines the actions of `T̃^λ`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`: `𝔉_i` of the action of `z ∈ T̃^λ_ν` is carried to the action
of `z` with a black strand `i` appended at the right. -/
theorem appendMidMap_midLeftAlg (h : j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (z : StendhalAlgebra k Q Λ ν)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    appendMidMap Q Λ Λc j hj ν ν₀ i L h (Ind.map (midLeftLin ν hL hR z) x) =
      midLeftAlg L hL hR' (appendBlackStendhal Q Λ i ν z)
        (appendMidMap Q Λ Λc j hj ν ν₀ i L h x) := by
  obtain ⟨w, hw⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ)
    (ν := ν) z.val
  have hz : midLeftLin ν hL hR z = midKLRActLin ν hL hR w :=
    LinearMap.ext fun y => by
      change allOrdersLift (redRelations_midKLRAct hR) z.val y = _
      rw [← hw, allOrdersLift_ofKLR]
      rfl
  have hz' : midLeftAlg L hL hR' (appendBlackStendhal Q Λ i ν z) = midKLRAct hR' (AL w) := by
    change allOrdersLift (redRelations_midKLRAct hR') (appendBlackStendhal Q Λ i ν z).val = _
    rw [appendBlackStendhal_val, ← hw, appendBlackAllOrders_ofKLR_appendLam, allOrdersLift_ofKLR]
    rfl
  rw [hz, hz']
  exact appendMidMap_midKLRAct ν i hL h hR hR' w x

end Categorification.Stendhal.CupCap
