/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendImage
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KModelViolated

/-!
# The violated parts of the model and of `𝔉_i` of the model

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). The cap bimodule `K^{λ⁺}_λ` is the
quotient of `K̃^{λ⁺}_λ` by the violated diagrams. In the model `L ⊗ e T̃^{λ⁺}` the diagrams
violated above the cap act through diagrams violated below it
(`CupCap.midLeftAlg_mem_midBotViolSub`), so the violated part of the model is its
bottom-violated part `model · V_{λ⁺}` (`CupCap.midBotViolSub`).

Appending a black strand sends violated diagrams to violated diagrams
(`CupCap.appendBlackStendhal_mem_violatedIdeal`). Hence `𝔉_i` of the bottom-violated part at `ν`
lies in the bottom-violated part `𝔉_i(model_ν) · V_{λ⁺}` of `𝔉_i(model_ν)`
(`CupCap.tmul_mem_appendBotViolSub`), and the comparison with the model at `{i} + ν` matches the
two bottom-violated parts exactly (`CupCap.mem_appendBotViolSub_iff`).

## Main definitions

* `CupCap.midBotViolSub`: the bottom-violated part `model · V_{λ⁺}` of the model.
* `CupCap.appendBotViolSub`: the bottom-violated part of `𝔉_i(model_ν)`.

## Main results

* `CupCap.appendBlackStendhal_mem_violatedIdeal`, `CupCap.appendBlackPlus_mem_violatedIdeal`.
* `CupCap.midLeftAlg_mem_midBotViolSub`.
* `CupCap.tmul_mem_appendBotViolSub`, `CupCap.mem_appendBotViolSub_iff`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Append

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) (ν : Multiset I)

/-- **Appending a black strand sends violated diagrams to violated diagrams.** -/
theorem appendBlackStendhal_mem_violatedIdeal {x : StendhalAlgebra k Q Λ' ν}
    (hx : x ∈ StendhalAlgebra.violatedIdeal k Q Λ' ν) :
    appendBlackStendhal Q Λ' i ν x ∈
      StendhalAlgebra.violatedIdeal k Q Λ' ((Singleton.singleton i : Multiset I) + ν) := by
  have h : TensorProductAlgebra.mk Q Λ' ((Singleton.singleton i : Multiset I) + ν)
      (appendBlackStendhal Q Λ' i ν x) = 0 := by
    have h0 : TensorProductAlgebra.mk Q Λ' ν x = 0 := by
      rw [← map_zero (TensorProductAlgebra.mk Q Λ' ν)]
      exact (RingCon.eq _).2 (((StendhalAlgebra.violatedIdeal k Q Λ' ν).rel_iff x 0).2
        (by rwa [sub_zero]))
    rw [← appendBlack_mk, h0, map_zero]
  change (StendhalAlgebra.violatedIdeal k Q Λ' _).ringCon.mk' _ = 0 at h
  rwa [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk'] at h

theorem castPlusStendhal_mem_violatedIdeal {μ μ' : Multiset I} (h : μ = μ')
    {x : StendhalAlgebra k Q Λ' μ} (hx : x ∈ StendhalAlgebra.violatedIdeal k Q Λ' μ) :
    castPlusStendhal Q Λ' h x ∈ StendhalAlgebra.violatedIdeal k Q Λ' μ' := by
  subst h; exact hx

end Append

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Tpᵢ" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "Vp" => StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Vpᵢ" => StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "aBp" => appendBlackPlus Q Λ Λc j hj ν ν₀ i

theorem appendBlackPlus_mem_violatedIdeal {b : Tp} (hb : b ∈ Vp) : aBp b ∈ Vpᵢ :=
  castPlusStendhal_mem_violatedIdeal Q _ _
    (appendBlackStendhal_mem_violatedIdeal Q _ i (ν + ν₀) hb)

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (Q Λ Λc j hj ν₀) in
/-- **The bottom-violated part `model · V_{λ⁺}` of the model**: the span of the elements `y · b`
with `b` violated in `T̃^{λ⁺}`. -/
def midBotViolSub : Submodule Tpᵐᵒᵖ (MidModel j hj Q Λ Λc ν ν₀ L) :=
  Submodule.span Tpᵐᵒᵖ {y | ∃ b ∈ Vp, ∃ w : MidModel j hj Q Λ Λc ν ν₀ L, y = op b • w}

theorem op_smul_mem_midBotViolSub {b : Tp} (hb : b ∈ Vp) (w : MidModel j hj Q Λ Λc ν ν₀ L) :
    op b • w ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L :=
  Submodule.subset_span ⟨b, hb, w, rfl⟩

variable {L}

/-- A generator `X ⊗ v` with `X` violated is bottom-violated. -/
theorem tmul_midGen_mem_midBotViolSub {X : Tp} (hX : X ∈ Vp) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ X) v : MidModel j hj Q Λ Λc ν ν₀ L) ∈
      midBotViolSub Q Λ Λc j hj ν ν₀ L := by
  have h : midGen j hj Q Λ Λc ν ν₀ X = op X • midGen j hj Q Λ Λc ν ν₀ 1 := by
    apply Subtype.ext
    change op (midStendhal j hj Q Λ Λc ν ν₀ 1 * X) = op X * op (midStendhal j hj Q Λ Λc ν ν₀ 1 * 1)
    rw [mul_one, ← op_mul]
  rw [h, ← Ind.smul_tmul]
  exact op_smul_mem_midBotViolSub ν L hX _

theorem midGen_unop_eq (z : Corner (midOp j hj Q Λ Λc ν ν₀)) :
    midGen j hj Q Λ Λc ν ν₀ z.1.unop = z := by
  rcases z with ⟨w, hw⟩
  apply Subtype.ext
  change (midGen j hj Q Λ Λc ν ν₀ w.unop).1 = w
  have hz : w * midOp j hj Q Λ Λc ν ν₀ 1 = w := hw
  have hz' := congrArg MulOpposite.unop hz
  rw [unop_mul, midOp_apply, unop_op] at hz'
  apply MulOpposite.unop_injective
  rw [midGen_val, unop_op]
  exact hz'

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
  op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

/-- **Diagrams violated above the cap act through diagrams violated below it**
(arXiv:1309.3796v3, §7.3): in the model, `a · y` is bottom-violated for `a` violated in `T̃^λ`. -/
theorem midLeftAlg_mem_midBotViolSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    {a : StendhalAlgebra k Q Λ ν} (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ ν)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hR a y ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L := by
  obtain ⟨W, hW, hact⟩ := midLeftAlg_tmul_midGen_violated hR ha
  induction y using Ind.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
  | tmul z v =>
    rw [← midGen_unop_eq ν z, hact]
    exact tmul_midGen_mem_midBotViolSub ν (TwoSidedIdeal.mul_mem_right _ _ _ hW) v

local notation "Tᵢ" => Tpᵢᵐᵒᵖ
local notation "FM" => Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)

variable (Q Λ Λc j hj ν₀ L) in
/-- **The bottom-violated part of `𝔉_i(model_ν)`**: the span of the elements `x · b` with `b`
violated in `T̃^{λ⁺}` at the black weight `{i} + ν`. -/
def appendBotViolSub : Submodule Tᵢ FM :=
  Submodule.span Tᵢ {x | ∃ b ∈ Vpᵢ, ∃ w : FM, x = op b • w}

/-- **`𝔉_i` of the bottom-violated part is bottom-violated.** -/
theorem tmul_mem_appendBotViolSub (z : Corner (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i))
    {w : MidModel j hj Q Λ Λc ν ν₀ L} (hw : w ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L) :
    (Ind.tmul z w : FM) ∈ appendBotViolSub Q Λ Λc j hj ν ν₀ i L := by
  induction hw using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨b, hb, w, rfl⟩ := hx
    have hc : aBp b * z.1.unop ∈ Vpᵢ :=
      TwoSidedIdeal.mul_mem_right _ _ _ (appendBlackPlus_mem_violatedIdeal ν i hb)
    have h : (Ind.tmul z (op b • w) : FM) =
        op (aBp b * z.1.unop) • Ind.tmul (unitGen (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) w := by
      rw [← Ind.op_smul_tmul, Ind.smul_tmul]
      congr 1
      apply Subtype.ext
      change z.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i (op b) =
        op (aBp b * z.1.unop) * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i 1
      generalize z.1 = u
      rw [← op_one, appendBlackPlusOp_op, appendBlackPlusOp_op, ← op_mul, ← mul_assoc, ← map_mul,
        one_mul, ← op_unop u, ← op_mul, unop_op]
    rw [h]
    exact Submodule.subset_span ⟨_, hc, _, rfl⟩
  | zero => rw [Ind.tmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Ind.tmul_add]; exact add_mem (hx z) (hy z)
  | smul r x _ hx =>
    rw [← Ind.op_smul_tmul]
    exact hx _

variable (h : j < ℓ)

/-- **The comparison matches the bottom-violated parts** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`: an element of `𝔉_i(model_ν)` is bottom-violated if and only if
its image in the model at `{i} + ν` is. -/
theorem mem_appendBotViolSub_iff (x : FM) :
    x ∈ appendBotViolSub Q Λ Λc j hj ν ν₀ i L ↔
      appendMidMap Q Λ Λc j hj ν ν₀ i L h x ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L := by
  let E := appendMidEquiv Q Λ Λc j hj ν ν₀ i L
  have hft : ∀ u, fromAppendMid Q Λ Λc j hj ν ν₀ i L h (toAppendMid Q Λ Λc j hj ν ν₀ i L h u) =
      u := LinearMap.congr_fun (fromAppendMid_comp_toAppendMid Q Λ Λc j hj ν ν₀ i L h)
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, w, rfl⟩ := hx
      rw [map_smul]
      exact op_smul_mem_midBotViolSub νᵢ L hb _
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  · intro hy
    have key : ∀ y ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L,
        E.symm (fromAppendMid Q Λ Λc j hj ν ν₀ i L h y) ∈
          appendBotViolSub Q Λ Λc j hj ν ν₀ i L := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, w, rfl⟩ := hy
        rw [map_smul, map_smul]
        exact Submodule.subset_span ⟨b, hb, _, rfl⟩
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
      | smul r x _ hx => rw [map_smul, map_smul]; exact Submodule.smul_mem _ r hx
    have := key _ hy
    change E.symm (fromAppendMid Q Λ Λc j hj ν ν₀ i L h
      (toAppendMid Q Λ Λc j hj ν ν₀ i L h (E x))) ∈ _ at this
    rwa [hft, LinearEquiv.symm_apply_apply] at this

end Categorification.Stendhal.CupCap
