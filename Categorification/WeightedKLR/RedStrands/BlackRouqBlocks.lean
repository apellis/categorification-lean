/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackMixedCrossCast
import Categorification.WeightedKLR.RedStrands.BlackModuleSimpleHead

/-!
# Black induction functors between arbitrary contents, with dots and crossings

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6: the
functors `Fᵢ` (induction, adding a black strand) and `Eᵢ` (restriction) on right `T^λ`-modules,
with the dots and crossings of Rouquier's definition (Brundan, arXiv:1501.00350v1,
Definition 1.1), between contents given by equalities, as the blocks of a weight-indexed
Rouquier family (`TwoRep.RouqData`), in the shape of the cyclotomic blocks of
`KLR.CyclotomicAction.Global` (induction raises the weight).

* `blackFOfEq i h`, for `h : {i} + μ = β`, is induction along `appendBlackOpOfEq`, left adjoint
  to `blackEOfEq i h` (`blackAdjOfEq`).
* On restrictions, `resDotOfEq` is `blackDot` and `resCrossOfEq i j h₁ h₂ h₃ h₄` is the
  same-colour crossing `blackCross` (the action of `-ψ`) for `i = j` and minus the mixed
  crossing `blackMixedCrossOfEq` (Webster's signed terminal crossing of Lemma 4.35 is `-ψ`, so
  this is `+ψ`) for `i ≠ j`, transported along the equalities. This is the sign convention of
  the cyclotomic family `CyclotomicAction.signedCross`.
* On inductions, `indDotOfEq` and `indCrossOfEq` are their mates through `blackAdjOfEq`
  (`conjugateEquiv`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- `Fᵢ` into the content `β`, given by an equality `{i} + μ = β`: induction along
`appendBlackOpOfEq`. -/
def blackFOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    ModuleCat.{u} (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ :=
  InductionAlong.functor.{u, u} (appendBlackOpOfEq Q Λ i h)

/-- `Fᵢ ⊣ Eᵢ` between arbitrary contents. -/
def blackAdjOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    blackFOfEq Q Λ i h ⊣ blackEOfEq Q Λ i h :=
  InductionAlong.adjunction.{u, u} (appendBlackOpOfEq Q Λ i h)

theorem blackFOfEq_rfl (i : I) (μ : Multiset I) :
    blackFOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _) = blackF Q Λ i μ :=
  rfl

theorem blackAdjOfEq_rfl (i : I) (μ : Multiset I) :
    blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _) = blackAdjunction Q Λ i μ :=
  rfl

instance blackFOfEq_additive (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (blackFOfEq Q Λ i h).Additive :=
  inferInstanceAs (InductionAlong.functor _).Additive

instance blackEOfEq_additive (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (blackEOfEq Q Λ i h).Additive :=
  inferInstanceAs (InductionAlong.resFunctor _).Additive

instance blackFOfEq_linear (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (blackFOfEq Q Λ i h).Linear k := by
  subst h; exact blackF_linear Q Λ i μ

instance blackEOfEq_linear (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    (blackEOfEq Q Λ i h).Linear k := by
  subst h; exact blackE_linear Q Λ i μ

/-! ### Dots and crossings on restrictions -/

/-- The dot on `Eᵢ` between arbitrary contents (`blackDot`). -/
def resDotOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    blackEOfEq Q Λ i h ⟶ blackEOfEq Q Λ i h := by
  subst h; exact blackDot Q Λ i μ

variable {Q}

/-- The crossing on restrictions between arbitrary contents, `Eⱼ Eᵢ ⟶ Eᵢ Eⱼ` (restriction
along `h₄`, then `h₃`, to restriction along `h₂`, then `h₁`): the same-colour crossing
`blackCross` (action of `-ψ`) if `i = j`, and minus the mixed crossing `blackMixedCrossOfEq`
if `i ≠ j`. Webster's signed terminal crossing (Lemma 4.35) acts by `-ψ`, so for `i ≠ j` this
is the action of `+ψ`: the convention of the cyclotomic family (`CyclotomicAction.signedCross`,
`ψ` for distinct and `-ψ` for equal colours). -/
def resCrossOfEq (hsym : KLRSymm Q) (i j : I) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    blackEOfEq Q Λ j h₄ ⋙ blackEOfEq Q Λ i h₃ ⟶ blackEOfEq Q Λ i h₂ ⋙ blackEOfEq Q Λ j h₁ :=
  if hij : i = j then by
    subst hij h₁ h₂ h₃
    exact blackCross Q Λ i μ
  else -blackMixedCrossOfEq (i := j) (j := i) hsym (Ne.symm hij) h₃ h₄ h₁ h₂

theorem resCrossOfEq_self (hsym : KLRSymm Q) (i : I) (μ : Multiset I) :
    resCrossOfEq Λ hsym i i (rfl : ({i} : Multiset I) + μ = _) rfl rfl rfl =
      blackCross Q Λ i μ := by
  simp [resCrossOfEq]

/-! ### Dots and crossings on inductions, as mates -/

variable (Q) in
/-- **The dot on `Fᵢ`**: the mate of the dot on `Eᵢ` through `Fᵢ ⊣ Eᵢ`. -/
def indDotOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    blackFOfEq Q Λ i h ⟶ blackFOfEq Q Λ i h :=
  (conjugateEquiv (blackAdjOfEq Q Λ i h) (blackAdjOfEq Q Λ i h)).symm (resDotOfEq Q Λ i h)

/-- **The crossing on inductions** `Fⱼ Fᵢ ⟶ Fᵢ Fⱼ` (induction along `h₁`, then `h₂`, to
induction along `h₃`, then `h₄`): the mate of `resCrossOfEq` through the composite adjunctions. -/
def indCrossOfEq (hsym : KLRSymm Q) (i j : I) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    blackFOfEq Q Λ j h₁ ⋙ blackFOfEq Q Λ i h₂ ⟶ blackFOfEq Q Λ i h₃ ⋙ blackFOfEq Q Λ j h₄ :=
  (conjugateEquiv ((blackAdjOfEq Q Λ i h₃).comp (blackAdjOfEq Q Λ j h₄))
    ((blackAdjOfEq Q Λ j h₁).comp (blackAdjOfEq Q Λ i h₂))).symm
    (resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄)


/-! ### Single-colour relations -/

theorem resCrossOfEq_sq (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ ≫ resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ = 0 := by
  subst h₁ h₂
  rw [resCrossOfEq_self]
  exact blackCross_comp_blackCross Q Λ i μ

theorem resCrossOfEq_braid (hsym : KLRSymm Q) (i : I) {μ β γ δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = γ)
    (h₃ : ({i} : Multiset I) + γ = δ) :
    Functor.whiskerRight (resCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) (blackEOfEq Q Λ i h₁) ≫
        Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) ≫
          Functor.whiskerRight (resCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) (blackEOfEq Q Λ i h₁) =
      Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) ≫
        Functor.whiskerRight (resCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) (blackEOfEq Q Λ i h₁) ≫
          Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) := by
  subst h₁ h₂ h₃
  rw [resCrossOfEq_self, resCrossOfEq_self]
  exact blackCross_braid Q Λ i μ

omit [DecidableEq I] [Field k] in
private theorem comp_assoc_adj {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : B ⥤ C} {G₂ : C ⥤ B} {F₃ : C ⥤ D}
    {G₃ : D ⥤ C} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃) :
    (a₁.comp a₂).comp a₃ = a₁.comp (a₂.comp a₃) := by
  ext X
  simp [Adjunction.comp_unit_app]

theorem indCrossOfEq_sq (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ ≫ indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂ = 0 := by
  rw [indCrossOfEq, conjugateEquiv_symm_comp, resCrossOfEq_sq, Equiv.symm_apply_eq]
  ext X
  simp [conjugateEquiv_apply_app]

/-- **The braid relation on `Fᵢ³`** between arbitrary contents, from the braid relation on
restrictions (`blackCross_braid`) through mates. -/
theorem indCrossOfEq_braid (hsym : KLRSymm Q) (i : I) {μ β γ δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = γ)
    (h₃ : ({i} : Multiset I) + γ = δ) :
    Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) ≫
          Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) =
      Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) := by
  set a₁ := blackAdjOfEq Q Λ i h₁
  set a₂ := blackAdjOfEq Q Λ i h₂
  set a₃ := blackAdjOfEq Q Λ i h₃
  have hL : Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) =
      (conjugateEquiv (a₁.comp (a₂.comp a₃)) (a₁.comp (a₂.comp a₃))).symm
        (Functor.whiskerRight (resCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) (blackEOfEq Q Λ i h₁)) := by
    rw [Equiv.eq_symm_apply, indCrossOfEq, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]
  have hR : Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂) (blackFOfEq Q Λ i h₃) =
      (conjugateEquiv (a₁.comp (a₂.comp a₃)) (a₁.comp (a₂.comp a₃))).symm
        (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂)) := by
    refine (Equiv.eq_symm_apply _).mpr ?_
    have h := conjugateEquiv_whiskerRight (a₁.comp a₂) (a₁.comp a₂) a₃
      (indCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂)
    rw [comp_assoc_adj] at h
    exact h.trans (by rw [indCrossOfEq, Equiv.apply_symm_apply])
  set A := a₁.comp (a₂.comp a₃)
  set x := Functor.whiskerRight (resCrossOfEq Λ hsym i i h₂ h₃ h₂ h₃) (blackEOfEq Q Λ i h₁)
  set y := Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i i h₁ h₂ h₁ h₂)
  have braid : (x ≫ y) ≫ x = (y ≫ x) ≫ y := by
    simpa only [Category.assoc] using resCrossOfEq_braid Λ hsym i h₁ h₂ h₃
  rw [hL, hR]
  exact ((congrArg (_ ≫ ·) (conjugateEquiv_symm_comp A A A x y)).trans
    (conjugateEquiv_symm_comp A A A (x ≫ y) x)).trans ((congrArg _ braid).trans
      ((congrArg (_ ≫ ·) (conjugateEquiv_symm_comp A A A y x)).trans
        (conjugateEquiv_symm_comp A A A (y ≫ x) y)).symm)

end Categorification.Stendhal
