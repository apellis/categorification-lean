/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedUpRelations
import Categorification.WeightedKLR.RedStrands.BlackNewStrandProjection
import Categorification.KLR.CyclotomicAction.Braid

/-!
# Crossings of black strands as projected affine crossings

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Khovanov–Lauda I, §2.1 (the KLR relations).

The black strands appended to `T^λ_μ` are the images of the last-strand inclusions of the affine
KLR cover `R(stendhalWeight μ)` (`appendBlackAt_projection`): the cover equation of
`{a} + μ = β` is `stendhalWeight_cons_eq`. The crossing on restrictions
`resCrossOfEq a b h₁ h₂ h₃ h₄`, for every pair of colours `a, b`, is right multiplication by the
projection of `resCrossSign a b • ψ_n · ν_a(ν_b(1))` (`resCrossOfEq_val`), where `ψ_n` crosses the
two appended strands, `ν_a(ν_b(1))` is the unit of the target appending order and the sign is
`-1` for `a = b` and `+1` for `a ≠ b` (the sign convention of `resCrossOfEq`). This gives a
uniform description of the crossings for the three-strand relations (`BlackRouqMixedBraid`).

* `crossCoverElem`, `resCrossSign`: the cover element and the sign.
* `appendedCross_eq_cover`, `neg_mixedCrossElem_eq_cover`: the same-colour and the mixed
  crossing elements in this form.
* `resCrossOfEq_val`, `whiskerRight_resCrossOfEq_val`, `whiskerLeft_resCrossOfEq_val`: the
  crossing and its whiskerings acting elementwise.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR KLRAlgebra CyclotomicAction
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

local notation "S" => affineCoverQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ
local notation "π" => affineTensorProjection (Q := Q) Λ

/-- The cover equation of `{a} + μ = β`. -/
theorem stendhalWeight_cons_eq (a : I) {μ β : Multiset I} (h : ({a} : Multiset I) + μ = β) :
    ({Sum.inl a} : Multiset (I ⊕ Fin ℓ)) + stendhalWeight ℓ μ = stendhalWeight ℓ β := by
  subst h; simp [stendhalWeight]

theorem appendBlack_projection (a : I) (μ : Multiset I)
    (y : KLRAlgebra k S (stendhalWeight ℓ μ)) :
    appendBlack Q Λ a μ (π μ y) =
      π _ (lastIncl S (Sum.inl a) (stendhalWeight_cons_eq a rfl) y) :=
  appendBlack_affineTensorProjection (Q := Q) Λ a μ y

/-- **Appending a black strand is the last-strand inclusion of the affine cover.** -/
theorem appendBlackAt_projection (a : I) {μ β : Multiset I} (h : ({a} : Multiset I) + μ = β)
    (y : KLRAlgebra k S (stendhalWeight ℓ μ)) :
    appendBlackAt Λ a h (π μ y) =
      π β (lastIncl S (Sum.inl a) (stendhalWeight_cons_eq a h) y) := by
  subst h
  exact appendBlack_projection Λ a μ y

theorem castTensorProductAlgebra_projection {β β' : Multiset I} (h : β = β')
    (y : KLRAlgebra k S (stendhalWeight ℓ β)) :
    castTensorProductAlgebra Q Λ h (π β y) =
      π β' (castKLR S (congrArg (stendhalWeight ℓ) h) y) := by
  subst h; rfl

theorem castTensorProductAlgebra_appendBlack (a : I) {μ β : Multiset I}
    (h : ({a} : Multiset I) + μ = β) (y : T μ) :
    castTensorProductAlgebra Q Λ h (appendBlack Q Λ a μ y) = appendBlackAt Λ a h y := by
  subst h; rfl

variable (k) in
/-- The sign of the crossing on restrictions: `-1` for equal and `+1` for distinct colours. -/
def resCrossSign (a b : I) : k := if a = b then -1 else 1

theorem resCrossSign_self (a : I) : resCrossSign k a a = -1 := by simp [resCrossSign]

theorem resCrossSign_of_ne {a b : I} (h : a ≠ b) : resCrossSign k a b = 1 := by
  simp [resCrossSign, h]

variable (Q) in
/-- The affine cover element of the crossing `resCrossOfEq a b h₁ h₂ …`: the crossing `ψ_n` of
the two appended strands followed by the unit `ν_a(ν_b(1))` of the target appending order. -/
def crossCoverElem (a b : I) {μ β₁ δ : Multiset I} (h₁ : ({b} : Multiset I) + μ = β₁)
    (h₂ : ({a} : Multiset I) + β₁ = δ) : KLRAlgebra k S (stendhalWeight ℓ δ) :=
  ψ (Multiset.card (stendhalWeight ℓ μ)) *
    lastIncl S (Sum.inl a) (stendhalWeight_cons_eq a h₂)
      (lastIncl S (Sum.inl b) (stendhalWeight_cons_eq b h₁) 1)

theorem appendBlack_appendBlack_one (a b : I) (μ : Multiset I) :
    appendBlack Q Λ a ({b} + μ) (appendBlack Q Λ b μ 1) =
      π ({a} + ({b} + μ)) (lastIncl S (Sum.inl a) (stendhalWeight_cons_eq a rfl)
        (lastIncl S (Sum.inl b) (stendhalWeight_cons_eq b rfl) 1)) := by
  rw [← map_one (π μ), appendBlack_projection, appendBlack_projection]

/-- The same-colour crossing element in cover form. -/
theorem appendedCross_eq_cover (a : I) (μ : Multiset I) :
    appendedCross Q Λ a μ = π _ (resCrossSign k a a • crossCoverElem Q Λ a a
      (rfl : ({a} : Multiset I) + μ = _) rfl) := by
  rw [appendedCross_eq, appendBlack_appendBlack_one, resCrossSign_self, crossCoverElem,
    neg_one_smul, map_neg, map_mul]

theorem mixedBlackCrossing_eq (ν : Multiset I) (i j : I) :
    mixedBlackCrossing (Q := Q) Λ ν i j =
      -π ({i} + ({j} + ν)) (ψ (Multiset.card (stendhalWeight ℓ ν))) := by
  rw [← mixedProj_neg_psi]
  change π _ (castKLR S _ (-ψ _)) = _
  rw [map_neg, castKLR_ψ, map_neg]

/-- The mixed crossing element in cover form: for `a ≠ b`, minus `mixedCrossElem` (the action of
`resCrossOfEq a b` in its canonical frame) is the projection of `crossCoverElem a b`. -/
theorem neg_mixedCrossElem_eq_cover {a b : I} (hab : a ≠ b) (μ : Multiset I)
    (h : ({a} : Multiset I) + ({b} + μ) = {b} + ({a} + μ)) :
    -mixedCrossElem (Q := Q) Λ μ b a = π _ (resCrossSign k a b • crossCoverElem Q Λ a b
      (rfl : ({b} : Multiset I) + μ = _) h) := by
  have e1 : appendBlack Q Λ b ({a} + μ) (appendBlack Q Λ a μ 1) =
      π _ (doubleIncl S (Sum.inl b) (Sum.inl a) (stendhalWeight_cons_eq a rfl)
        (stendhalWeight_cons_eq b rfl) 1) := appendBlack_appendBlack_one Λ b a μ
  have e2 : appendBlackAt Λ a (mixedSwap μ b a) (appendBlack Q Λ b μ 1) =
      π _ (doubleIncl S (Sum.inl a) (Sum.inl b) (stendhalWeight_cons_eq b rfl)
        (stendhalWeight_cons_eq a h) 1) := by
    rw [← map_one (π μ)]
    exact (congrArg (appendBlackAt Λ a (mixedSwap μ b a))
      (appendBlackAt_projection Λ b rfl 1)).trans (appendBlackAt_projection Λ a _ _)
  have hc := double_cross S (Sum.inl b) (Sum.inl a) (stendhalWeight_cons_eq a rfl)
    (stendhalWeight_cons_eq b rfl) (stendhalWeight_cons_eq b rfl)
    (stendhalWeight_cons_eq a h) 1
  have hD : doubleIncl S (Sum.inl a) (Sum.inl b) (stendhalWeight_cons_eq b rfl)
      (stendhalWeight_cons_eq a h) 1 * doubleIncl S (Sum.inl a) (Sum.inl b)
        (stendhalWeight_cons_eq b rfl) (stendhalWeight_cons_eq a h) 1 =
      doubleIncl S (Sum.inl a) (Sum.inl b) (stendhalWeight_cons_eq b rfl)
        (stendhalWeight_cons_eq a h) 1 := by rw [← map_mul, mul_one]
  rw [mixedCrossElem, mixedBlackCrossing_eq, e1, e2, resCrossSign_of_ne hab, one_smul,
    mul_neg, neg_mul, neg_neg, ← map_mul, ← map_mul, hc, mul_assoc, hD]
  rfl

/-! ### The crossing on restrictions, elementwise -/

/-- **Every crossing on restrictions acts by its projected cover element**: on
`Eᵢ Eⱼ`-restrictions out of `T^λ_δ`-modules, `resCrossOfEq a b h₁ h₂ h₃ h₄` is right
multiplication by the projection of `resCrossSign a b • crossCoverElem a b h₁ h₂`. -/
theorem resCrossOfEq_val (hsym : KLRSymm Q) (a b : I) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (M : ModuleCat.{u} (T δ)ᵐᵒᵖ)
    (w : Res (appendBlackOpOfEq Q Λ a h₃) (Res (appendBlackOpOfEq Q Λ b h₄) M)) :
    ((((resCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄).app M).hom w).val.val : M) =
      op (π δ (resCrossSign k a b • crossCoverElem Q Λ a b h₁ h₂)) • (w.val.val : M) := by
  by_cases hab : a = b
  · subst hab h₃ h₁ h₄
    cases h₂
    rw [resCrossOfEq_self, ← appendedCross_eq_cover]
    rfl
  · subst h₃ h₁ h₄
    refine (congrArg (fun α => (((α.app M).hom w).val.val : M))
      (resCrossOfEq_of_ne Λ hsym hab rfl h₂ rfl rfl)).trans ?_
    change -(((((blackMixedCrossOfEq (i := b) (j := a) hsym (Ne.symm hab) rfl rfl rfl h₂).app
      M).hom w).val.val : M)) = _
    rw [blackMixedCrossOfEq_val Λ hsym (Ne.symm hab) rfl h₂ M w, ← neg_mixedCrossElem_eq_cover Λ
      hab μ h₂, MulOpposite.op_neg, neg_smul]
    rfl

/-- A crossing of the two outer restrictions of a triple restriction, elementwise. -/
theorem whiskerRight_resCrossOfEq_val (hsym : KLRSymm Q) (a b x : I)
    {ν μ β₁ β₂ δ : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (e : ({x} : Multiset I) + ν = μ) (M : ModuleCat.{u} (T δ)ᵐᵒᵖ)
    (w : Res (appendBlackOpOfEq Q Λ x e) (Res (appendBlackOpOfEq Q Λ a h₃)
      (Res (appendBlackOpOfEq Q Λ b h₄) M))) :
    ((((Functor.whiskerRight (resCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄)
        (blackEOfEq Q Λ x e)).app M).hom w).val.val.val : M) =
      op (π δ (resCrossSign k a b • crossCoverElem Q Λ a b h₁ h₂)) • (w.val.val.val : M) :=
  resCrossOfEq_val Λ hsym a b h₁ h₂ h₃ h₄ M w.val

theorem appendBlackOpOfEq_op (x : I) {μ β : Multiset I} (e : ({x} : Multiset I) + μ = β)
    (y : T μ) : appendBlackOpOfEq Q Λ x e (op y) = op (appendBlackAt Λ x e y) := by
  rw [appendBlackOpOfEq_apply, appendBlackOp_op, castOp_op,
    castTensorProductAlgebra_appendBlack]

/-- A crossing of the two inner restrictions of a triple restriction, elementwise. -/
theorem whiskerLeft_resCrossOfEq_val (hsym : KLRSymm Q) (a b x : I)
    {μ β₁ β₂ δ m : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (e : ({x} : Multiset I) + δ = m) (M : ModuleCat.{u} (T m)ᵐᵒᵖ)
    (w : Res (appendBlackOpOfEq Q Λ a h₃) (Res (appendBlackOpOfEq Q Λ b h₄)
      (Res (appendBlackOpOfEq Q Λ x e) M))) :
    ((((Functor.whiskerLeft (blackEOfEq Q Λ x e) (resCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄)).app
        M).hom w).val.val.val : M) =
      op (π m (lastIncl S (Sum.inl x) (stendhalWeight_cons_eq x e)
        (resCrossSign k a b • crossCoverElem Q Λ a b h₁ h₂))) • (w.val.val.val : M) := by
  have h := congrArg Res.val
    (resCrossOfEq_val Λ hsym a b h₁ h₂ h₃ h₄ ((blackEOfEq Q Λ x e).obj M) w)
  refine h.trans ?_
  rw [Res.val_smul, appendBlackOpOfEq_op, appendBlackAt_projection]

/-- Elements of a triple restriction are fixed by the unit of the appending order. -/
theorem res_three_val_fix (x y z : I) {l w w' m : Multiset I} (e₁ : ({x} : Multiset I) + l = w)
    (e₂ : ({y} : Multiset I) + w = w') (e₃ : ({z} : Multiset I) + w' = m)
    (M : ModuleCat.{u} (T m)ᵐᵒᵖ)
    (r : Res (appendBlackOpOfEq Q Λ x e₁) (Res (appendBlackOpOfEq Q Λ y e₂)
      (Res (appendBlackOpOfEq Q Λ z e₃) M))) :
    op (π m (tripleIncl S (Sum.inl x) (Sum.inl y) (Sum.inl z) (stendhalWeight_cons_eq x e₁)
      (stendhalWeight_cons_eq y e₂) (stendhalWeight_cons_eq z e₃) 1)) • (r.val.val.val : M) =
      r.val.val.val := by
  have h := congrArg (fun t => (Res.val (Res.val t) : M)) r.prop
  simp only [Res.val_smul] at h
  refine Eq.trans ?_ h
  rw [← op_one, appendBlackOpOfEq_op, appendBlackOpOfEq_op, appendBlackOpOfEq_op,
    ← map_one (π l), appendBlackAt_projection, appendBlackAt_projection,
    appendBlackAt_projection]
  rfl

end Categorification.Stendhal
