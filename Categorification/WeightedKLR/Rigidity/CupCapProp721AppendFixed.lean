/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendPos
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendImage

/-!
# `e' · model` window by window

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. Under the decomposition of the model at the black weight `{i} + ν` into the
staged modules of its loadings (`CupCap.midModelPiEquiv`), the idempotent `e'` of the loadings
ending in the black strand `i` keeps the components of the appended loadings `s i` and kills the
others (`CupCap.midModelPiEquiv_midLeftAlg_of_eq`, `CupCap.midModelPiEquiv_midLeftAlg_of_ne`).
So the product of the staged modules of the appended loadings at their windows is `e' · model`
(`CupCap.appendFixedEquiv`, `CupCap.mem_range_appendFixedIncl_iff`). This holds for every `j`.

## Main definitions

* `CupCap.appendFixedProj`, `CupCap.appendFixedIncl`: the projection onto, and the inclusion of,
  the components of the appended loadings.
* `CupCap.appendFixedEquiv`: `∏_s L ⊗ e_{s i, midPos (s i)} T̃^{λ⁺} ≅ e' · model_{{i} + ν}`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

section Idem

variable {μ : Multiset I}

theorem midIdem_mul_sum_midIdem (t : Seq (stendhalWeight ℓ μ)) :
    midIdem j hj Q Λ Λc μ ν₀ t * ∑ t', midIdem j hj Q Λ Λc μ ν₀ t' =
      midIdem j hj Q Λ Λc μ ν₀ t := by
  rw [Finset.mul_sum]
  simp only [midIdem_mul_midIdem, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The diagrams on the window at `midPos t` of the unit are the window idempotent of `t`. -/
theorem posStendhal_midPos_one (t : Seq (stendhalWeight ℓ μ)) :
    posStendhal j hj Q Λ Λc ν₀ t (midPos j t) (midPos_le j t) 1 =
      botMap k Q Λ Λc j hj μ ν₀ (midIdem j hj Q Λ Λc μ ν₀ t) := by
  rw [posStendhal_eq_posBot (x := redOrderedKLR k Q Λc ν₀)
    ((ofKLR_redOrderedKLR Q Λc ν₀).trans rfl), posBot_apply, botMap_insertMap_redOrderedKLR]
  rfl

end Idem

variable (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ
local notation "Mᵢ" => midIdem j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀
local notation "botᵢ" => botMap k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀

omit [DecidableEq I] in
theorem appendBlackLoading_injective' :
    Function.Injective (appendBlackLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply Subtype.ext
  funext a
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have h1 := appendBlackLoading_lbl_of_lt i ν s ⟨a.val, by omega⟩ a.2
  have h2 := appendBlackLoading_lbl_of_lt i ν t ⟨a.val, by omega⟩ a.2
  rw [h] at h1
  exact h1.symm.trans h2

theorem midIdem_mul_appendIdemKLR_of_eq (s₀ : Seq (stendhalWeight ℓ ν)) :
    Mᵢ (appendBlackLoading i ν s₀) * appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ)
      (Λc := Λc) ν i = Mᵢ (appendBlackLoading i ν s₀) := by
  rw [Finset.mul_sum]
  simp only [midIdem_mul_midIdem, (appendBlackLoading_injective' (ν := ν) i).eq_iff,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem midIdem_mul_appendIdemKLR_of_ne (t : Seq (stendhalWeight ℓ νᵢ))
    (ht : ∀ s, appendBlackLoading i ν s ≠ t) :
    Mᵢ t * appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i = 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun s _ => by
    rw [midIdem_mul_midIdem, ite_eq_right_iff]
    exact fun h' => absurd h'.symm (ht s)

local notation "Y" => Subtype.val (midFree j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν)
  ν₀ (appendIdemFree ν i))
local notation "Pᵢ" t => posOp j hj Q Λ Λc ν₀ t (midPos j t) (midPos_le j t) 1

/-- The action of `e'` keeps the window of an appended loading. -/
theorem midElt_mul_posOp_of_eq (s₀ : Seq (stendhalWeight ℓ ν)) :
    midElt j hj Q Λ Λc νᵢ ν₀ Y * (Pᵢ (appendBlackLoading i ν s₀)) =
      Pᵢ (appendBlackLoading i ν s₀) := by
  rw [midElt, posOp_apply, ← op_mul, unop_one, posStendhal_midPos_one,
    midStendhal_one_eq_botMap, midFree_appendIdemFree, ← map_mul, ← map_mul, ← map_mul,
    ← mul_assoc, ← mul_assoc, midIdem_mul_sum_midIdem, midIdem_mul_appendIdemKLR_of_eq,
    midIdem_mul_sum_midIdem]

/-- The action of `e'` kills the window of a loading that is not appended. -/
theorem midElt_mul_posOp_of_ne (t : Seq (stendhalWeight ℓ νᵢ))
    (ht : ∀ s, appendBlackLoading i ν s ≠ t) :
    midElt j hj Q Λ Λc νᵢ ν₀ Y * (Pᵢ t) = 0 := by
  rw [midElt, posOp_apply, ← op_mul, unop_one, posStendhal_midPos_one,
    midStendhal_one_eq_botMap, midFree_appendIdemFree, ← map_mul, ← map_mul, ← map_mul,
    ← mul_assoc, ← mul_assoc, midIdem_mul_sum_midIdem, midIdem_mul_appendIdemKLR_of_ne i t ht,
    zero_mul, map_zero, op_zero]

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)

local notation "Φ" => midModelPiEquiv j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "aB1" => appendBlackStendhal Q Λ i ν 1

/-- **`e'` keeps the components of the appended loadings.** -/
theorem midModelPiEquiv_midLeftAlg_of_eq (y : MidModel j hj Q Λ Λc νᵢ ν₀ L)
    (s₀ : Seq (stendhalWeight ℓ ν)) :
    Φ (midLeftAlg L hL hR' aB1 y) (appendBlackLoading i ν s₀) =
      Φ y (appendBlackLoading i ν s₀) := by
  rw [midLeftAlg_appendBlackStendhal_one]
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy']
  | tmul z v =>
    change Ind.tmul _ v = Ind.tmul _ v
    congr 1
    apply Subtype.ext
    change z.1 * midElt j hj Q Λ Λc νᵢ ν₀ Y * (Pᵢ (appendBlackLoading i ν s₀)) =
      z.1 * (Pᵢ (appendBlackLoading i ν s₀))
    rw [mul_assoc, midElt_mul_posOp_of_eq]

/-- **`e'` kills the components of the loadings that are not appended.** -/
theorem midModelPiEquiv_midLeftAlg_of_ne (y : MidModel j hj Q Λ Λc νᵢ ν₀ L)
    (t : Seq (stendhalWeight ℓ νᵢ)) (ht : ∀ s, appendBlackLoading i ν s ≠ t) :
    Φ (midLeftAlg L hL hR' aB1 y) t = 0 := by
  rw [midLeftAlg_appendBlackStendhal_one]
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, Pi.zero_apply]
  | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy', add_zero]
  | tmul z v =>
    change Ind.tmul _ v = 0
    have h0 : (cornerMul (intertwines_of_orthogonal_proj midOp_eq_sum_posOp
        (fun _ _ a a' h => posOp_mul_posOp_of_ne h a a') t)
        (cornerMulOf (intertwinesOn_midElt L hL
          (mem_midSlidesSub.1 (midFree j hj Q Λ Λc νᵢ ν₀ (appendIdemFree ν i)).2)).unit z)) =
        0 := by
      apply Subtype.ext
      change z.1 * midElt j hj Q Λ Λc νᵢ ν₀ Y * (Pᵢ t) = 0
      rw [mul_assoc, midElt_mul_posOp_of_ne i t ht, mul_zero]
    rw [h0]
    exact Ind.zero_tmul v

variable (L) in
/-- The projection of the model at `{i} + ν` onto the components of the appended loadings. -/
def appendFixedProj :
    MidModel j hj Q Λ Λc νᵢ ν₀ L →ₗ[Tᵢ]
      ((s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
          (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) :=
  LinearMap.pi fun s => (LinearMap.proj (appendBlackLoading i ν s)).comp (Φ).toLinearMap

variable (L) in
/-- The inclusion of the components of the appended loadings into the model at `{i} + ν`. -/
def appendFixedIncl :
    ((s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
          (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) →ₗ[Tᵢ]
      MidModel j hj Q Λ Λc νᵢ ν₀ L :=
  (Φ).symm.toLinearMap.comp
    (∑ s, (LinearMap.single Tᵢ (fun t : Seq (stendhalWeight ℓ νᵢ) =>
      PosModel j hj Q Λ Λc ν₀ t (midPos j t) (midPos_le j t) L) (appendBlackLoading i ν s)).comp
        (LinearMap.proj s))

theorem midModelPiEquiv_appendFixedIncl
    (f : (s : Seq (stendhalWeight ℓ ν)) →
      PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
        (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) :
    Φ (appendFixedIncl i L f) = ∑ s, Pi.single (appendBlackLoading i ν s) (f s) := by
  rw [appendFixedIncl, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.sum_apply]
  rfl

theorem appendFixedProj_comp_appendFixedIncl :
    (appendFixedProj i L).comp (appendFixedIncl i L) =
      LinearMap.id (R := Tᵢ) (M := (s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
          (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) := by
  refine LinearMap.ext fun f => funext fun s => ?_
  change Φ (appendFixedIncl i L f) (appendBlackLoading i ν s) = f s
  rw [midModelPiEquiv_appendFixedIncl, Finset.sum_apply, Finset.sum_eq_single s
    (fun s' _ h => Pi.single_eq_of_ne
      ((appendBlackLoading_injective' (ν := ν) i).ne h).symm _)
    (by simp), Pi.single_eq_same]

/-- **The composite through the components of the appended loadings is the action of `e'`.** -/
theorem appendFixedIncl_comp_appendFixedProj :
    (appendFixedIncl i L).comp (appendFixedProj i L) = midLeftLin νᵢ hL hR' aB1 := by
  refine LinearMap.ext fun y => (Φ).injective (funext fun t => ?_)
  change Φ (appendFixedIncl i L (appendFixedProj i L y)) t = Φ (midLeftAlg L hL hR' aB1 y) t
  rw [midModelPiEquiv_appendFixedIncl, Finset.sum_apply]
  by_cases ht : ∃ s₀, appendBlackLoading i ν s₀ = t
  · obtain ⟨s₀, rfl⟩ := ht
    rw [midModelPiEquiv_midLeftAlg_of_eq, Finset.sum_eq_single s₀
      (fun s' _ h => Pi.single_eq_of_ne
        ((appendBlackLoading_injective' (ν := ν) i).ne h).symm _)
      (by simp), Pi.single_eq_same]
    rfl
  · simp only [not_exists] at ht
    rw [midModelPiEquiv_midLeftAlg_of_ne i hR' y t ht]
    exact Finset.sum_eq_zero fun s _ => Pi.single_eq_of_ne (Ne.symm (ht s)) _

variable (L) in
/-- **`e' · model` window by window** (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the
product of the staged modules of the appended loadings at their windows is the image of the
inclusion, which is the image of `e'` (`CupCap.mem_range_appendFixedIncl_iff`). -/
def appendFixedEquiv :
    ((s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
          (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) ≃ₗ[Tᵢ]
      LinearMap.range (appendFixedIncl (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
        (ν := ν) (ν₀ := ν₀) i L) :=
  LinearEquiv.ofLeftInverse (g := appendFixedProj (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν := ν) (ν₀ := ν₀) i L)
    (fun f => LinearMap.congr_fun (appendFixedProj_comp_appendFixedIncl (Q := Q) (Λ := Λ)
      (Λc := Λc) (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) (L := L) i) f)

theorem appendFixedEquiv_apply
    (f : (s : Seq (stendhalWeight ℓ ν)) →
      PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
        (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) :
    (appendFixedEquiv i L f : MidModel j hj Q Λ Λc νᵢ ν₀ L) = appendFixedIncl i L f := rfl

/-- The image of the inclusion is the image of `e'`: the elements fixed by `e'`. -/
theorem mem_range_appendFixedIncl_iff (y : MidModel j hj Q Λ Λc νᵢ ν₀ L) :
    y ∈ LinearMap.range (appendFixedIncl (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
        (ν := ν) (ν₀ := ν₀) i L) ↔ midLeftAlg L hL hR' aB1 y = y := by
  have hP := LinearMap.congr_fun (appendFixedIncl_comp_appendFixedProj i hR')
  constructor
  · rintro ⟨f, rfl⟩
    have h1 := hP (appendFixedIncl i L f)
    have h2 := LinearMap.congr_fun (appendFixedProj_comp_appendFixedIncl (L := L) i) f
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [h2] at h1
    exact h1.symm
  · intro hy
    exact ⟨appendFixedProj i L y, (hP y).trans hy⟩

end Categorification.Stendhal.CupCap
