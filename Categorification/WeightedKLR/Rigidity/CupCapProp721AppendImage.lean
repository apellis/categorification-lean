/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendAct
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMap

/-!
# `𝔉_i` of the model as the cut `e' · model`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). The composite of the maps between
`𝔉_i(model_ν)` and `model_{{i} + ν}` is the action of `e' = appendBlack(1) ∈ T̃^λ_{{i} + ν}` on
the model at `{i} + ν` (`CupCap.toAppendMid_comp_fromAppendMid_eq`). Hence `𝔉_i(model_ν)` is
isomorphic to the image of `e'`, which is the left `T̃^λ_ν`-module `e' T̃^λ_{{i} + ν} ⊗ model`
(`CupCap.appendModelEquiv`), and the isomorphism carries the action of `z ∈ T̃^λ_ν` to the action
of `appendBlack(z)` (`CupCap.appendModelEquiv_midLeftAlg`).

## Main definitions

* `CupCap.appendModelEquiv`: `𝔉_i(model_ν) ≅ e' · model_{{i} + ν}`.

## Main results

* `CupCap.appendBlackStendhal_topMap`, `CupCap.toAppendMid_comp_fromAppendMid_eq`.
* `CupCap.appendModelEquiv_midLeftAlg`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "AL" => appendLam Q Λ ν i
local notation "aB" => appendBlackStendhal Q Λ i ν

/-- Appending the strand commutes with the quotient map onto `T̃^λ`. -/
theorem appendBlackStendhal_topMap (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    aB (topMap k Q Λ ν a) = topMap k Q Λ νᵢ (AL a) := by
  exact (appendBlackStendhal_orderProjection Q Λ id i ν _).trans
    (congrArg (orderProjection Q Λ νᵢ) (appendBlackAllOrders_ofKLR_appendLam a))

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
variable {L}
variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
  op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

/-- The appended idempotent `e'` acts on the model at `{i} + ν` through its diagrams. -/
theorem midLeftAlg_appendBlackStendhal_one (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL)
    (y : MidModel j hj Q Λ Λc νᵢ ν₀ L) :
    midLeftAlg L hL hR' (aB 1) y =
      midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc νᵢ ν₀ (appendIdemFree ν i)).2) y := by
  rw [← map_one (topMap k Q Λ ν), appendBlackStendhal_topMap, midLeftAlg_topMap,
    appendLam_one_eq_mk, midKLRAct_mk, midEndAlg_apply]

/-- **The composite through `𝔉_i(model_ν)` is the action of `e'`** (arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for `j < ℓ`. -/
theorem toAppendMid_comp_fromAppendMid_eq (h : j < ℓ) (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) :
    (toAppendMid Q Λ Λc j hj ν ν₀ i L h).comp (fromAppendMid Q Λ Λc j hj ν ν₀ i L h) =
      midLeftLin νᵢ hL hR' (aB 1) := by
  rw [toAppendMid_comp_fromAppendMid]
  refine Ind.ext fun z v => ?_
  change _ = midLeftAlg L hL hR' (aB 1) (Ind.tmul z v)
  rw [midLeftAlg_appendBlackStendhal_one, midEnd, natMapOn_tmul, natMap_tmul]
  congr 1
  apply Subtype.ext
  have hz : z.1 * midOp j hj Q Λ Λc νᵢ ν₀ 1 = z.1 := z.2
  change z.1 * appendMidOp Q Λ Λc j hj ν ν₀ i 1 = z.1 * midElt j hj Q Λ Λc νᵢ ν₀
    (midFree j hj Q Λ Λc νᵢ ν₀ (appendIdemFree ν i)).val
  generalize z.1 = w at hz ⊢
  apply MulOpposite.unop_injective
  have hz' := congrArg MulOpposite.unop hz
  rw [appendMidOp_apply ν i h, midOp_apply, midElt, midFree_appendIdemFree, botMap_appendIdemKLR]
  rw [midOp_apply] at hz'
  simp only [unop_mul, unop_op, unop_one, mul_assoc] at hz' ⊢
  rw [hz', ← mul_assoc, midStendhal_one_mul_appendIdemPlus ν i h]

local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ

variable (L) in
/-- **`𝔉_i` of the model as the cut `e' · model`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j < ℓ`: `𝔉_i(model_ν)` is isomorphic to the image of the comparison map,
which is the image of `e'` acting on the model at `{i} + ν`. -/
def appendModelEquiv (h : j < ℓ) :
    Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i) ≃ₗ[Tᵢ]
      LinearMap.range (toAppendMid Q Λ Λc j hj ν ν₀ i L h) :=
  (appendMidEquiv Q Λ Λc j hj ν ν₀ i L).trans
    (LinearEquiv.ofLeftInverse (g := fromAppendMid Q Λ Λc j hj ν ν₀ i L h)
      (fun x => LinearMap.congr_fun (fromAppendMid_comp_toAppendMid Q Λ Λc j hj ν ν₀ i L h) x))

theorem appendModelEquiv_apply (h : j < ℓ)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (appendModelEquiv ν i L h x : MidModel j hj Q Λ Λc νᵢ ν₀ L) =
      appendMidMap Q Λ Λc j hj ν ν₀ i L h x := rfl

/-- The image of the comparison is the image of `e'`: the elements fixed by `e'`. -/
theorem mem_range_toAppendMid_iff (h : j < ℓ) (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL)
    (y : MidModel j hj Q Λ Λc νᵢ ν₀ L) :
    y ∈ LinearMap.range (toAppendMid Q Λ Λc j hj ν ν₀ i L h) ↔
      midLeftAlg L hL hR' (aB 1) y = y := by
  have hP := LinearMap.congr_fun (toAppendMid_comp_fromAppendMid_eq ν i hL h hR')
  constructor
  · rintro ⟨x, rfl⟩
    have h1 := hP (toAppendMid Q Λ Λc j hj ν ν₀ i L h x)
    have h2 := LinearMap.congr_fun (fromAppendMid_comp_toAppendMid Q Λ Λc j hj ν ν₀ i L h) x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [h2] at h1
    exact h1.symm
  · intro hy
    exact ⟨fromAppendMid Q Λ Λc j hj ν ν₀ i L h y, (hP y).trans hy⟩

/-- **The isomorphism `𝔉_i(model_ν) ≅ e' · model` is one of `T̃^λ_ν`-modules**
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `j < ℓ`: it carries `𝔉_i` of the
action of `z` to the action of `z` with a black strand `i` appended at the right. -/
theorem appendModelEquiv_midLeftAlg (h : j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (z : StendhalAlgebra k Q Λ ν)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (appendModelEquiv ν i L h (Ind.map (midLeftLin ν hL hR z) x) :
        MidModel j hj Q Λ Λc νᵢ ν₀ L) =
      midLeftAlg L hL hR' (aB z) (appendModelEquiv ν i L h x) :=
  appendMidMap_midLeftAlg ν i hL h hR hR' z x

end Categorification.Stendhal.CupCap
