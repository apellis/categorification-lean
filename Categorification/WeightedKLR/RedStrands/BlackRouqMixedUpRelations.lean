/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleMixedInversion
import Categorification.WeightedKLR.RedStrands.BlackRouqSlides
import Categorification.WeightedKLR.RedStrands.BlackMixedRelations
import Categorification.KLR.NcEvalHom
import Categorification.Algebra.MapDerivedNatTransLinear

/-!
# The mixed quadratic relation and dot slides for black induction

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Brundan, arXiv:1501.00350v1, Definition 1.1, (1.2) and (1.3) for distinct labels (the
`square`, `slide_left` and `slide_right` fields of `TwoRep.RouqUpKLR`).

For colours `i ≠ j` the crossing on restrictions `resCrossOfEq` is minus the transported mixed
crossing `blackMixedCrossOfEq`, which acts by right multiplication by the cut terminal crossing
(`blackMixedCrossOfEq_val`). The module identities of `BlackMixedRelations`
(`blackMixedCross_comp_blackMixedCrossRev`, `blackDot_whiskerLeft_comp_blackMixedCross`,
`blackDot_whiskerRight_comp_blackMixedCross`) therefore give, between arbitrary contents,

* the quadratic relation `τ_{ji} τ_{ij} = Q_{ij}(y_i, y_j)` on restrictions
  (`resCrossOfEq_mixed_square`), and
* the two dot slides on restrictions (`resCrossOfEq_mixed_slide_left`,
  `resCrossOfEq_mixed_slide_right`).

Their mates through `Fᵢ ⊣ Eᵢ` are the corresponding relations for the induction crossing
`indCrossOfEq` (`indCrossOfEq_mixed_square`, `indCrossOfEq_mixed_slide_left`,
`indCrossOfEq_mixed_slide_right`). The mate is a unital `k`-linear antihomomorphism of
endomorphism algebras (`conjugateEquivSymmLinear`), so polynomial expressions in the dots are
transported with the variables reversed (`KLR.ncEval_antihom`).

They pass to the derived inductions (`derivedIndCrossOfEq_mixed_square`,
`derivedIndCrossOfEq_mixed_slide_left`, `derivedIndCrossOfEq_mixed_slide_right`) and to the
weight spaces of `blackRouqData` (`blackRouqCross_mixed_square`,
`blackRouqCross_mixed_slide_left`, `blackRouqCross_mixed_slide_right`), in the shapes of the
fields `square`, `slide_left` and `slide_right` of `TwoRep.RouqUpKLR` with the polynomial
`Q`. The braid fields `braid` and `braidQ` are not treated here.

The hypotheses are `KLRSymm Q` and `i ≠ j`; no route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u u₁

/-! ### Polynomials in two commuting variables -/

section Swap

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

/-- Evaluating at two commuting elements does not depend on the order of the variables. -/
theorem ncEval_swap_of_commute {x y : A} (hxy : Commute x y) (P : MvPolynomial (Fin 2) k) :
    KLR.ncEval ![x, y] P = KLR.ncEval ![y, x] (MvPolynomial.rename Fin.rev P) := by
  have hc : ∀ a b : Fin 2, Commute (![x, y] a) (![x, y] b) := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hxy, hxy.symm, Commute.refl]
  have hc' : ∀ a b : Fin 2, Commute (![y, x] a) (![y, x] b) := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hxy, hxy.symm, Commute.refl]
  obtain ⟨φ, hφX, hφ⟩ := exists_algHom_ncEval (k := k) ![x, y] hc
  obtain ⟨ψ, hψX, hψ⟩ := exists_algHom_ncEval (k := k) ![y, x] hc'
  rw [hφ, hψ]
  have hcomp : ψ.comp (MvPolynomial.rename Fin.rev) = φ := by
    apply MvPolynomial.algHom_ext
    intro a
    fin_cases a
    · simp [hψX, hφX]
    · simp [hψX, hφX]
  exact (congrArg (fun f : MvPolynomial (Fin 2) k →ₐ[k] A => f P) hcomp).symm

end Swap

/-! ### Mates as a linear antihomomorphism -/

section Mates

variable {k : Type*} [CommRing k] {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Preadditive 𝒜]
  [Preadditive ℬ] [Linear k 𝒜] [Linear k ℬ] {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} [L.Additive] [L.Linear k]

/-- The inverse mate `End R → End L` through `L ⊣ R`, as a `k`-linear map. -/
def conjugateEquivSymmLinear (adj : L ⊣ R) : End R →ₗ[k] End L where
  toFun α := (conjugateEquiv adj adj).symm α
  map_add' α β := by
    refine NatTrans.ext (funext fun X => ?_)
    erw [NatTrans.app_add, conjugateEquiv_symm_apply_app, NatTrans.app_add, Functor.map_add]
    simp [conjugateEquiv_symm_apply_app]
  map_smul' c α := by
    refine NatTrans.ext (funext fun X => ?_)
    erw [NatTrans.app_smul, conjugateEquiv_symm_apply_app, NatTrans.app_smul, Functor.map_smul]
    simp [conjugateEquiv_symm_apply_app]

theorem conjugateEquivSymmLinear_one (adj : L ⊣ R) :
    conjugateEquivSymmLinear (k := k) adj 1 = 1 :=
  conjugateEquiv_symm_id adj

theorem conjugateEquivSymmLinear_mul (adj : L ⊣ R) (α β : End R) :
    conjugateEquivSymmLinear (k := k) adj (α * β : End R) =
      (conjugateEquivSymmLinear (k := k) adj β *
        conjugateEquivSymmLinear (k := k) adj α : End L) := by
  change (conjugateEquiv adj adj).symm (β ≫ α) =
    (conjugateEquiv adj adj).symm α ≫ (conjugateEquiv adj adj).symm β
  rw [conjugateEquiv_symm_comp]

/-- Polynomials in endomorphisms of the right adjoint have mates given by the reversed
polynomial in the mates (`KLR.ncEval_antihom`). -/
theorem conjugateEquiv_symm_ncEval (adj : L ⊣ R) {n : ℕ} (y : Fin n → End R)
    (P : MvPolynomial (Fin n) k) :
    (conjugateEquiv adj adj).symm (KLR.ncEval (A := End R) y P) =
      KLR.ncEval (A := End L) (fun a => (conjugateEquiv adj adj).symm (y (Fin.rev a)))
        (MvPolynomial.rename Fin.rev P) :=
  KLR.ncEval_antihom (conjugateEquivSymmLinear (k := k) adj)
    (conjugateEquivSymmLinear_one adj) (conjugateEquivSymmLinear_mul adj) y P

end Mates

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

local notation "T" => TensorProductAlgebra k Q Λ

/-! ### The mixed crossing on restrictions, elementwise -/

/-- **The transported mixed crossing acts by the transported cut crossing**: on
`Eᵢ Eⱼ` out of an arbitrary content `δ`, `blackMixedCrossOfEq` is right multiplication by the
image of `mixedCrossElem` along `{i} + ({j} + μ) = δ`. -/
theorem blackMixedCrossOfEq_val (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j) {μ δ : Multiset I}
    (h₂ : ({i} : Multiset I) + ({j} + μ) = δ) (h₄ : ({j} : Multiset I) + ({i} + μ) = δ)
    (M : ModuleCat.{u} (T δ)ᵐᵒᵖ)
    (w : Res (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ))
      (Res (appendBlackOpOfEq Q Λ i h₂) M)) :
    let x : Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ))
        (Res (appendBlackOpOfEq Q Λ j h₄) M) :=
      ((blackMixedCrossOfEq (Λ := Λ) hsym hij rfl h₂ rfl h₄).app M).hom w
    (x.val.val : M) =
      op (castTensorProductAlgebra Q Λ h₂ (mixedCrossElem (Q := Q) Λ μ i j)) •
        (w.val.val : M) := by
  intro x
  subst h₂
  change Res.val (Res.val (((blackMixedCrossOfEq (Λ := Λ) hsym hij rfl rfl rfl h₄).app M).hom
    w)) = _
  rw [blackMixedCrossOfEq, NatTrans.comp_app, ModuleCat.comp_apply, eqToHom_app]
  exact res_eqToHom_val_val (appendBlackAtOp_eq (Q := Q) Λ μ i j) _ M _ _

/-- For distinct colours, the crossing on restrictions is minus the transported mixed
crossing. -/
theorem resCrossOfEq_of_ne (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ =
      -blackMixedCrossOfEq (i := j) (j := i) hsym (Ne.symm hij) h₃ h₄ h₁ h₂ := by
  simp only [resCrossOfEq, hij, dite_false]

/-! ### The quadratic relation on restrictions -/

/-- **The mixed quadratic relation on restrictions between arbitrary contents** (KL I, §2.1;
Brundan, arXiv:1501.00350v1, (1.3)): for `i ≠ j`, `τ_{ji} τ_{ij} = Q_{ij}` evaluated at the dot
on the `i` strand and the dot on the `j` strand. -/
theorem resCrossOfEq_mixed_square (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    resCrossOfEq Λ hsym j i h₃ h₄ h₁ h₂ ≫ resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ =
      KLR.ncEval (A := End (blackEOfEq Q Λ i h₂ ⋙ blackEOfEq Q Λ j h₁))
        ![Functor.whiskerRight (resDotOfEq Q Λ i h₂) (blackEOfEq Q Λ j h₁),
          Functor.whiskerLeft (blackEOfEq Q Λ i h₂) (resDotOfEq Q Λ j h₁)] (Q i j) := by
  subst h₁ h₃ h₂
  have e : resCrossOfEq Λ hsym j i rfl h₄ rfl rfl ≫ resCrossOfEq Λ hsym i j rfl rfl rfl h₄ =
      blackMixedCross hsym hij ≫ blackMixedCrossRev hsym hij := by
    rw [resCrossOfEq_of_ne Λ hsym (Ne.symm hij), resCrossOfEq_of_ne Λ hsym hij,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    ext M : 2
    refine ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext ?_))
    rw [NatTrans.comp_app, ModuleCat.comp_apply]
    refine (blackMixedCrossOfEq_val Λ hsym (Ne.symm hij) h₄ rfl M _).trans ?_
    have h1 := blackMixedCrossOfEq_val Λ hsym hij rfl h₄ M w
    refine (congrArg (fun z : M => op (castTensorProductAlgebra Q Λ h₄
      (mixedCrossElem (Q := Q) Λ μ j i)) • z) h1).trans ?_
    change _ = op (mixedCrossRevElem (Q := Q) Λ μ i j) • op (mixedCrossElem (Q := Q) Λ μ i j) •
      (w.val.val : M)
    rfl
  rw [e]
  exact blackMixedCross_comp_blackMixedCrossRev hsym hij

/-! ### Dot slides on restrictions -/

omit [Field k] in
/-- Left whiskering commutes with the identification of two equal functors. -/
theorem whiskerLeft_comp_eqToHom_of_eq {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    {F₁ F₂ : 𝒞 ⥤ 𝒟} (hF : F₁ = F₂) {G : 𝒟 ⥤ ℰ} (β : G ⟶ G) (e : F₁ ⋙ G = F₂ ⋙ G) :
    Functor.whiskerLeft F₁ β ≫ eqToHom e = eqToHom e ≫ Functor.whiskerLeft F₂ β := by
  subst hF
  simp

variable (Q) in
/-- The dot on `Eᵢ` out of an arbitrary content acts by the transported appended dot. -/
theorem resDotOfEq_val (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (M : ModuleCat.{u} (T β)ᵐᵒᵖ) (r : Res (appendBlackOpOfEq Q Λ i h) M) :
    ((((resDotOfEq Q Λ i h).app M).hom r).val : M) =
      op (castTensorProductAlgebra Q Λ h (appendedDot Q Λ i μ)) • (r.val : M) := by
  subst h
  rfl

/-- The transported dot `blackDotAt` is the dot on `Eᵢ` out of `j + (i + μ)`. -/
theorem whiskerRight_blackDotAt_eqToHom (i j : I) (μ : Multiset I)
    (h₂ : ({i} : Multiset I) + ({j} + μ) = {j} + ({i} + μ))
    (e : blackEAt (Q := Q) Λ μ j i ⋙ blackE Q Λ j μ =
      blackEOfEq Q Λ i h₂ ⋙ blackEOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = _)) :
    Functor.whiskerRight (blackDotAt Λ μ j i) (blackE Q Λ j μ) ≫ eqToHom e =
      eqToHom e ≫ Functor.whiskerRight (resDotOfEq Q Λ i h₂)
        (blackEOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = _)) := by
  ext M : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext ?_))
  rw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.comp_apply, ModuleCat.comp_apply,
    eqToHom_app]
  refine (res_eqToHom_val_val (appendBlackAtOp_eq (Q := Q) Λ μ j i) _ M _ _).trans ?_
  refine Eq.trans ?_ (resDotOfEq_val Q Λ i h₂ M _).symm
  refine Eq.trans ?_ (congrArg (fun z : M => op (castTensorProductAlgebra Q Λ h₂
    (appendedDot Q Λ i ({j} + μ))) • z)
      (res_eqToHom_val_val (appendBlackAtOp_eq (Q := Q) Λ μ j i) _ M _ _)).symm
  rfl

/-- Whiskering by the transported restriction `blackEAt` commutes with the identification
`blackEAt_eq`. -/
theorem whiskerLeft_blackEAt_eqToHom (i j : I) (μ : Multiset I)
    (h₂ : ({i} : Multiset I) + ({j} + μ) = {j} + ({i} + μ))
    (e : blackEAt (Q := Q) Λ μ j i ⋙ blackE Q Λ j μ =
      blackEOfEq Q Λ i h₂ ⋙ blackEOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = _)) :
    Functor.whiskerLeft (blackEAt Λ μ j i) (blackDot Q Λ j μ) ≫ eqToHom e =
      eqToHom e ≫ Functor.whiskerLeft (blackEOfEq Q Λ i h₂)
        (resDotOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = _)) := by
  exact whiskerLeft_comp_eqToHom_of_eq (blackEAt_eq (Q := Q) Λ μ j i) (blackDot Q Λ j μ) e

/-- **The left dot slide on restrictions for distinct colours** (KL I, §2.1, (2.4); Brundan,
arXiv:1501.00350v1, (1.2)): the dot on the `i` strand moves through the mixed crossing. -/
theorem resCrossOfEq_mixed_slide_left (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    Functor.whiskerLeft (blackEOfEq Q Λ j h₄) (resDotOfEq Q Λ i h₃) ≫
        resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ =
      resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ ≫
        Functor.whiskerRight (resDotOfEq Q Λ i h₂) (blackEOfEq Q Λ j h₁) := by
  subst h₃ h₄ h₁
  rw [resCrossOfEq_of_ne Λ hsym hij, Preadditive.comp_neg, Preadditive.neg_comp, neg_inj,
    blackMixedCrossOfEq_rfl]
  have k1 := blackDot_whiskerLeft_comp_blackMixedCross (Q := Q) (Λ := Λ) (ν := μ) (i := j)
    (j := i) hsym (Ne.symm hij)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eqToHom _) k1).trans
    ((Category.assoc _ _ _).trans ((congrArg (blackMixedCross hsym (Ne.symm hij) ≫ ·)
      (whiskerRight_blackDotAt_eqToHom Λ i j μ h₂ _)).trans (Category.assoc _ _ _).symm)))

/-- **The right dot slide on restrictions for distinct colours** (KL I, §2.1, (2.4); Brundan,
arXiv:1501.00350v1, (1.2)): the dot on the `j` strand moves through the mixed crossing. -/
theorem resCrossOfEq_mixed_slide_right (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    Functor.whiskerRight (resDotOfEq Q Λ j h₄) (blackEOfEq Q Λ i h₃) ≫
        resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ =
      resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ ≫
        Functor.whiskerLeft (blackEOfEq Q Λ i h₂) (resDotOfEq Q Λ j h₁) := by
  subst h₃ h₄ h₁
  rw [resCrossOfEq_of_ne Λ hsym hij, Preadditive.comp_neg, Preadditive.neg_comp, neg_inj,
    blackMixedCrossOfEq_rfl]
  have k1 := blackDot_whiskerRight_comp_blackMixedCross (Q := Q) (Λ := Λ) (ν := μ) (i := j)
    (j := i) hsym (Ne.symm hij)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eqToHom _) k1).trans
    ((Category.assoc _ _ _).trans ((congrArg (blackMixedCross hsym (Ne.symm hij) ≫ ·)
      (whiskerLeft_blackEAt_eqToHom Λ i j μ h₂ _)).trans (Category.assoc _ _ _).symm)))

/-! ### On inductions -/

variable (Q) in
/-- The dot on the second strand of `Fⱼ Fᵢ` is the mate of the dot on the first strand of
`Eᵢ Eⱼ`, for arbitrary colours. -/
theorem whiskerLeft_indDotOfEq_two (i j : I) {μ β δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerLeft (blackFOfEq Q Λ j h₁) (indDotOfEq Q Λ i h₂) =
      (conjugateEquiv ((blackAdjOfEq Q Λ j h₁).comp (blackAdjOfEq Q Λ i h₂))
        ((blackAdjOfEq Q Λ j h₁).comp (blackAdjOfEq Q Λ i h₂))).symm
        (Functor.whiskerRight (resDotOfEq Q Λ i h₂) (blackEOfEq Q Λ j h₁)) := by
  rw [Equiv.eq_symm_apply, indDotOfEq, CategoryTheory.conjugateEquiv_whiskerLeft,
    Equiv.apply_symm_apply]

variable (Q) in
/-- The dot on the first strand of `Fⱼ Fᵢ` is the mate of the dot on the second strand of
`Eᵢ Eⱼ`, for arbitrary colours. -/
theorem whiskerRight_indDotOfEq_two (i j : I) {μ β δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    Functor.whiskerRight (indDotOfEq Q Λ j h₁) (blackFOfEq Q Λ i h₂) =
      (conjugateEquiv ((blackAdjOfEq Q Λ j h₁).comp (blackAdjOfEq Q Λ i h₂))
        ((blackAdjOfEq Q Λ j h₁).comp (blackAdjOfEq Q Λ i h₂))).symm
        (Functor.whiskerLeft (blackEOfEq Q Λ i h₂) (resDotOfEq Q Λ j h₁)) := by
  rw [Equiv.eq_symm_apply, indDotOfEq, CategoryTheory.conjugateEquiv_whiskerRight,
    Equiv.apply_symm_apply]

omit [Field k] in
/-- Endomorphisms of the two factors of a composite commute. -/
theorem commute_whiskerLeft_whiskerRight {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟]
    [Category ℰ] [Preadditive ℰ] {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ ℰ} (α : F ⟶ F) (β : G ⟶ G) :
    @Commute (End (F ⋙ G)) _ (Functor.whiskerLeft F β) (Functor.whiskerRight α G) := by
  change Functor.whiskerRight α G ≫ Functor.whiskerLeft F β =
    Functor.whiskerLeft F β ≫ Functor.whiskerRight α G
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact β.naturality (α.app X)

/-- **The mixed quadratic relation on black inductions between arbitrary contents** (Brundan,
arXiv:1501.00350v1, (1.3), the block form of `TwoRep.RouqUpKLR.square`), the mate of
`resCrossOfEq_mixed_square`. -/
theorem indCrossOfEq_mixed_square (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ ≫ indCrossOfEq Λ hsym j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (blackFOfEq Q Λ j h₁ ⋙ blackFOfEq Q Λ i h₂))
        ![Functor.whiskerLeft (blackFOfEq Q Λ j h₁) (indDotOfEq Q Λ i h₂),
          Functor.whiskerRight (indDotOfEq Q Λ j h₁) (blackFOfEq Q Λ i h₂)] (Q i j) := by
  rw [indCrossOfEq, indCrossOfEq, conjugateEquiv_symm_comp, resCrossOfEq_mixed_square Λ hsym hij,
    conjugateEquiv_symm_ncEval, ncEval_swap_of_commute
      (commute_whiskerLeft_whiskerRight (indDotOfEq Q Λ j h₁) (indDotOfEq Q Λ i h₂))]
  congr 1
  funext a
  fin_cases a
  · exact (whiskerRight_indDotOfEq_two Q Λ i j h₁ h₂).symm
  · exact (whiskerLeft_indDotOfEq_two Q Λ i j h₁ h₂).symm

/-- **The left dot slide on black inductions for distinct colours** (Brundan,
arXiv:1501.00350v1, (1.2), the block form of `TwoRep.RouqUpKLR.slide_left`). -/
theorem indCrossOfEq_mixed_slide_left (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    Functor.whiskerLeft (blackFOfEq Q Λ j h₁) (indDotOfEq Q Λ i h₂) ≫
        indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ =
      indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ ≫
        Functor.whiskerRight (indDotOfEq Q Λ i h₃) (blackFOfEq Q Λ j h₄) := by
  rw [whiskerLeft_indDotOfEq_two, whiskerRight_indDotOfEq_two, indCrossOfEq,
    conjugateEquiv_symm_comp, conjugateEquiv_symm_comp,
    resCrossOfEq_mixed_slide_left Λ hsym hij]

/-- **The right dot slide on black inductions for distinct colours** (Brundan,
arXiv:1501.00350v1, (1.2), the block form of `TwoRep.RouqUpKLR.slide_right`). -/
theorem indCrossOfEq_mixed_slide_right (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    Functor.whiskerRight (indDotOfEq Q Λ j h₁) (blackFOfEq Q Λ i h₂) ≫
        indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ =
      indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i h₃) (indDotOfEq Q Λ j h₄) := by
  rw [whiskerLeft_indDotOfEq_two, whiskerRight_indDotOfEq_two, indCrossOfEq,
    conjugateEquiv_symm_comp, conjugateEquiv_symm_comp,
    resCrossOfEq_mixed_slide_right Λ hsym hij]

/-! ### On derived categories -/

section Derived

open QuantumGroup

variable {C : CartanDatum I} (hQ : IsRouquierQ C Q)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]

/-- **The mixed quadratic relation on derived black inductions** (Brundan, arXiv:1501.00350v1,
(1.3)). -/
theorem derivedIndCrossOfEq_mixed_square (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    derivedIndCrossOfEq Λ hQ hsym i j h₁ h₂ h₃ h₄ ≫
        derivedIndCrossOfEq Λ hQ hsym j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (derivedFOfEq Λ hQ j h₁ ⋙ derivedFOfEq Λ hQ i h₂))
        ![Functor.whiskerLeft (derivedFOfEq Λ hQ j h₁) (derivedIndDotOfEq Λ hQ i h₂),
          Functor.whiskerRight (derivedIndDotOfEq Λ hQ j h₁) (derivedFOfEq Λ hQ i h₂)]
        (Q i j) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₄
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₄
  unfold derivedIndCrossOfEq derivedIndDotOfEq derivedFOfEq
  rw [NatTrans.derivedComp_comp]
  change NatTrans.derivedCompAlgHom k (blackFOfEq Q Λ j h₁) (blackFOfEq Q Λ i h₂)
    (indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄ ≫ indCrossOfEq Λ hsym j i h₃ h₄ h₁ h₂) = _
  rw [indCrossOfEq_mixed_square Λ hsym hij, ncEval_map]
  congr 1
  funext a
  fin_cases a
  · exact (NatTrans.whiskerLeft_mapDerivedCategory _).symm
  · exact (NatTrans.whiskerRight_mapDerivedCategory _).symm

/-- **The left dot slide on derived black inductions for distinct colours** (Brundan,
arXiv:1501.00350v1, (1.2)). -/
theorem derivedIndCrossOfEq_mixed_slide_left (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    Functor.whiskerLeft (derivedFOfEq Λ hQ j h₁) (derivedIndDotOfEq Λ hQ i h₂) ≫
        derivedIndCrossOfEq Λ hQ hsym i j h₁ h₂ h₃ h₄ =
      derivedIndCrossOfEq Λ hQ hsym i j h₁ h₂ h₃ h₄ ≫
        Functor.whiskerRight (derivedIndDotOfEq Λ hQ i h₃) (derivedFOfEq Λ hQ j h₄) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₄
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₄
  unfold derivedIndCrossOfEq derivedIndDotOfEq derivedFOfEq
  rw [NatTrans.whiskerLeft_mapDerivedCategory, NatTrans.whiskerRight_mapDerivedCategory]
  change NatTrans.derivedComp _ ≫ NatTrans.derivedComp _ =
    NatTrans.derivedComp _ ≫ NatTrans.derivedComp _
  rw [NatTrans.derivedComp_comp, NatTrans.derivedComp_comp,
    indCrossOfEq_mixed_slide_left Λ hsym hij]

/-- **The right dot slide on derived black inductions for distinct colours** (Brundan,
arXiv:1501.00350v1, (1.2)). -/
theorem derivedIndCrossOfEq_mixed_slide_right (hsym : KLRSymm Q) {i j : I} (hij : i ≠ j)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    Functor.whiskerRight (derivedIndDotOfEq Λ hQ j h₁) (derivedFOfEq Λ hQ i h₂) ≫
        derivedIndCrossOfEq Λ hQ hsym i j h₁ h₂ h₃ h₄ =
      derivedIndCrossOfEq Λ hQ hsym i j h₁ h₂ h₃ h₄ ≫
        Functor.whiskerLeft (derivedFOfEq Λ hQ i h₃) (derivedIndDotOfEq Λ hQ j h₄) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₄
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₄
  unfold derivedIndCrossOfEq derivedIndDotOfEq derivedFOfEq
  rw [NatTrans.whiskerLeft_mapDerivedCategory, NatTrans.whiskerRight_mapDerivedCategory]
  change NatTrans.derivedComp _ ≫ NatTrans.derivedComp _ =
    NatTrans.derivedComp _ ≫ NatTrans.derivedComp _
  rw [NatTrans.derivedComp_comp, NatTrans.derivedComp_comp,
    indCrossOfEq_mixed_slide_right Λ hsym hij]

/-! ### On weight spaces -/

section Weight

open CategoryTheory.Bicategory TwoRep CyclotomicAction

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

/-- **The mixed quadratic relation on weight spaces** (Brundan, arXiv:1501.00350v1, (1.3), the
shape of `TwoRep.RouqUpKLR.square`). -/
theorem blackRouqCross_mixed_square (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j) {x y z t : X}
    (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (blackRouqE Λ hQ RD Λ₀ j h₁ ≫ blackRouqE Λ hQ RD Λ₀ i h₂))
        ![blackRouqE Λ hQ RD Λ₀ j h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂,
          blackRouqDot Λ hQ RD Λ₀ j h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂] (Q i j) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
    (derivedFBlock Λ hQ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ₀ j h₄ (blockSucc RD Λ₀ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  have hR := ncEval_compat (blackRouqE Λ hQ RD Λ₀ j h₁ ≫ blackRouqE Λ hQ RD Λ₀ i h₂)
    (derivedFOfEq Λ hQ j (blockSucc_eq RD Λ₀ j hb) ⋙
      derivedFOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hd)) (fun M => M γ)
    (Pi.eval _ δ) (fun M => gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂)
      (derivedFBlock Λ hQ RD Λ₀ j h₁) (derivedFBlock Λ hQ RD Λ₀ i h₂) M γ hb hd)
    ![blackRouqE Λ hQ RD Λ₀ j h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂,
      blackRouqDot Λ hQ RD Λ₀ j h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂]
    ![Functor.whiskerLeft (derivedFOfEq Λ hQ j (blockSucc_eq RD Λ₀ j hb))
        (derivedIndDotOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hd)),
      Functor.whiskerRight (derivedIndDotOfEq Λ hQ j (blockSucc_eq RD Λ₀ j hb))
        (derivedFOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hd))]
    (fun c M => by
      fin_cases c
      · exact gen₂_whiskerLeft_blackRouqDot Λ hQ RD Λ₀ i j h₁ h₂ M γ hb hd
      · exact gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ i j h₁ h₂ M γ hb hd) (Q i j) M
  refine Eq.trans ?_ hR.symm
  rw [← derivedIndCrossOfEq_mixed_square Λ hQ hsym hij (blockSucc_eq RD Λ₀ j hb)
    (blockSucc_eq RD Λ₀ i hd) (blockSucc_eq RD Λ₀ i (rfl : blockSucc RD Λ₀ i h₃ γ = _))
    (blockSucc_eq RD Λ₀ j e₁)]
  change gen₂ _ _ _ _ M γ hb hd ≫ ((blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄).hom.app M δ ≫
    (blackRouqCross Λ hQ RD Λ₀ hsym j i h₃ h₄ h₁ h₂).hom.app M δ) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym j i h₃ h₄ h₁ h₂ M γ rfl e₁ hb hd)).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The left dot slide for distinct colours on weight spaces** (Brundan, arXiv:1501.00350v1,
(1.2), the shape of `TwoRep.RouqUpKLR.slide_left`). -/
theorem blackRouqCross_mixed_slide_left (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    blackRouqE Λ hQ RD Λ₀ j h₁ ◁ blackRouqDot Λ hQ RD Λ₀ i h₂ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ =
      blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ ≫
        blackRouqDot Λ hQ RD Λ₀ i h₃ ▷ blackRouqE Λ hQ RD Λ₀ j h₄ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
    (derivedFBlock Λ hQ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ₀ j h₄ (blockSucc RD Λ₀ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  refine (gen_comp_comp (gen₂_whiskerLeft_blackRouqDot Λ hQ RD Λ₀ i j h₁ h₂ M γ hb hd)
    (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans
    (Eq.trans ?_ (gen_comp_comp
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)
      (gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ j i h₃ h₄ M γ rfl e₁)).symm)
  rw [← NatTrans.comp_app, ← NatTrans.comp_app,
    derivedIndCrossOfEq_mixed_slide_left Λ hQ hsym hij]

/-- **The right dot slide for distinct colours on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.2), the shape of `TwoRep.RouqUpKLR.slide_right`). -/
theorem blackRouqCross_mixed_slide_right (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    blackRouqDot Λ hQ RD Λ₀ j h₁ ▷ blackRouqE Λ hQ RD Λ₀ i h₂ ≫
        blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ =
      blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ ≫
        blackRouqE Λ hQ RD Λ₀ i h₃ ◁ blackRouqDot Λ hQ RD Λ₀ j h₄ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ j h₁)
    (derivedFBlock Λ hQ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ₀ j h₄ (blockSucc RD Λ₀ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  refine (gen_comp_comp (gen₂_blackRouqDot_whiskerRight Λ hQ RD Λ₀ i j h₁ h₂ M γ hb hd)
    (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans
    (Eq.trans ?_ (gen_comp_comp
      (gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)
      (gen₂_whiskerLeft_blackRouqDot Λ hQ RD Λ₀ j i h₃ h₄ M γ rfl e₁)).symm)
  rw [← NatTrans.comp_app, ← NatTrans.comp_app,
    derivedIndCrossOfEq_mixed_slide_right Λ hQ hsym hij]

end Weight

end Derived

end Categorification.Stendhal
