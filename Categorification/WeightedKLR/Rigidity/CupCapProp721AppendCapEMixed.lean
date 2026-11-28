/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapECross

/-!
# `K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` and the crossing of different colours

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈 ≅ 𝔈 ∘ K` with the crossing of two strands of
different colours `a ≠ b`. The crossing `resCrossOfEq` of `T^λ` acts on restrictions by minus the
mixed crossing of the two appended strands (`CupCap.resCrossOfEq_ne_app_val`). The two orders of
appending give the contents `{b} + ({a} + ν)` and `{a} + ({b} + ν)`; both are written along
equalities with a common content `δ` (`CupCap.capEOrdIsoOfEq'`, `CupCap.capECompIsoOfEq'`). The
isomorphisms carry the crossing of `T^λ` to the crossing of `T^{λ⁺}` as soon as the maps
`ι ∘ ι` for the two orders are intertwined by the two mixed crossings
(`CupCap.capECompIsoOfEq'_mixedCross`).

## Main results

* `CupCap.resCrossOfEq_ne_app_val`.
* `CupCap.capEOrdIsoOfEq'`, `CupCap.capECompIsoOfEq'`, `CupCap.capECompIsoOfEq'_mixedCross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

universe u

theorem eqToHom_res_res_val {A B C : Type u} [Ring A] [Ring B] [Ring C] {φ φ' : A →ₙ+* B}
    (e : φ = φ') (ψ : C →ₙ+* A)
    (h : resFunctor.{u, u} φ ⋙ resFunctor.{u, u} ψ = resFunctor.{u, u} φ' ⋙ resFunctor.{u, u} ψ)
    (M : ModuleCat.{u} B) (r : Res ψ (Res φ M)) :
    (((eqToHom h).app M).hom r).val.val = r.val.val := by
  subst e
  rw [eqToHom_refl]
  rfl

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

/-- The mixed crossing between contents acts by the mixed crossing of the two appended strands.
-/
theorem blackMixedCrossOfEq_app_val (hsym : KLRSymm Q) {a b : I} (hba : b ≠ a) {μ : Multiset I}
    (h : ({a} : Multiset I) + (({b} : Multiset I) + μ) =
      ({b} : Multiset I) + (({a} : Multiset I) + μ))
    (M : ModuleCat.{0}
      (TensorProductAlgebra k Q Λ' (({b} : Multiset I) + (({a} : Multiset I) + μ)))ᵐᵒᵖ)
    (r : Res (appendBlackOpOfEq Q Λ' a (rfl : ({a} : Multiset I) + μ = _))
      (Res (appendBlackOpOfEq Q Λ' b
        (rfl : ({b} : Multiset I) + (({a} : Multiset I) + μ) = _)) M)) :
    (((blackMixedCrossOfEq (Λ := Λ') (i := b) (j := a) hsym hba rfl rfl rfl h).app M).hom
      r).val.val =
      op (mixedCrossElem (Q := Q) Λ' μ b a) • r.val.val := by
  exact eqToHom_res_res_val (appendBlackAtOp_eq (Q := Q) Λ' μ b a) (appendBlackOp Q Λ' b μ)
    (congrArg (· ⋙ blackE Q Λ' b μ) (blackEAt_eq (Q := Q) Λ' μ b a)) M
    (((blackMixedCross (ν := μ) hsym hba).app M).hom r)

/-- The crossing of different colours on restrictions along content equalities acts by minus the
cast of the mixed crossing of the two appended strands. -/
theorem resCrossOfEq_ne_app_val (hsym : KLRSymm Q) {a b : I} (hab : a ≠ b)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (M : ModuleCat.{0} (TensorProductAlgebra k Q Λ' δ)ᵐᵒᵖ)
    (r : Res (appendBlackOpOfEq Q Λ' a h₃) (Res (appendBlackOpOfEq Q Λ' b h₄) M)) :
    (((resCrossOfEq Λ' hsym a b h₁ h₂ h₃ h₄).app M).hom r).val.val =
      -(castOp Q Λ' (h₃ ▸ h₄ : ({b} : Multiset I) + (({a} : Multiset I) + μ) = δ)
        (op (mixedCrossElem (Q := Q) Λ' μ b a)) • r.val.val) := by
  subst h₁ h₃ h₄
  unfold resCrossOfEq
  simp only [hab, ↓reduceDIte]
  rw [NatTrans.app_neg, ModuleCat.hom_neg]
  exact congrArg (fun z => -z) (blackMixedCrossOfEq_app_val Λ' hsym (Ne.symm hab) h₂ M r)

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))

/-- `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` (`CupCap.capEOrdIsoOfEq`) with the content `{i} + ν` of `T^λ` replaced
by an equal content `β`. -/
def capEOrdIsoOfEq' {ν : Multiset I} {i : I} (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    blackEOfEq Q Λ i h ⋙ OrdK ν ≅ OrdK β ⋙ blackEOfEq Q (plusLabels Λ Λc j hj) i hp := by
  subst h
  exact capEOrdIsoOfEq D

theorem capEOrdIsoOfEq'_hom_tmul {ν : Multiset I} {i : I}
    (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) (X : ModuleCat.{0} (TA β)ᵐᵒᵖ) (c : CB ν)
    (m : Res (appendBlackOpOfEq Q Λ i h) X) :
    Res.val (((capEOrdIsoOfEq' D h hp).hom.app X).hom
        (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
          (N := InDegreeZero ((blackEOfEq Q Λ i h).obj X)) (TA ν)ᵐᵒᵖ c m)) =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA β) (CB β))) (N := InDegreeZero X)
        (TA β)ᵐᵒᵖ (h ▸ D.iota c) m.val := by
  subst h
  rfl

/-- **`K ∘ 𝔈_b 𝔈_a ≅ 𝔈_b 𝔈_a ∘ K`** along a content equality `{b} + ({a} + ν) = δ`: two
applications of `CupCap.capEOrdIsoOfEq`, `c ⊗ m ↦ ι₂(ι₁(c)) ⊗ m`. -/
def capECompIsoOfEq' {ν : Multiset I} {a b : I} (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν a)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b) {δ : Multiset I}
    (h : ({b} : Multiset I) + (({a} : Multiset I) + ν) = δ)
    (hp : ({b} : Multiset I) + ((({a} : Multiset I) + ν) + ν₀) = δ + ν₀) :
    (blackEOfEq Q Λ b h ⋙ blackE Q Λ a ν) ⋙ OrdK ν ≅
      OrdK δ ⋙ (blackEOfEq Q (plusLabels Λ Λc j hj) b hp ⋙
        blackEOfEq Q (plusLabels Λ Λc j hj) a (plusWeight_assoc ν ν₀ a)) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (capEOrdIsoOfEq D₁) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (capEOrdIsoOfEq' D₂ h hp) _ ≪≫
    Functor.associator _ _ _

/-- **`K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` carries the crossing of different colours to the crossing**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): if the mixed crossing of the two
appended strands of `T^λ`, acting on the left of `ι(ι(c))` (first `b`, then `a` appended), equals
the mixed crossing of the two appended strands of `T^{λ⁺}`, acting on the right of `ι(ι(c))`
(first `a`, then `b` appended), then `(K ∘ τ) ≫ φ' = φ ≫ (τ ∘ K)`, with `τ` the crossing
`resCrossOfEq` of `T^λ` and of `T^{λ⁺}`. -/
theorem capECompIsoOfEq'_mixedCross (hQ : KLRSymm Q) {ν : Multiset I} {a b : I} (hab : a ≠ b)
    (Dₐ : CapAppendData k Q Λ Λc j hj ν₀ L ν a)
    (Dₐ_b : CapAppendData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b)
    (D_b : CapAppendData k Q Λ Λc j hj ν₀ L ν b)
    (D_bₐ : CapAppendData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a) {δ : Multiset I}
    (h₂ : ({a} : Multiset I) + (({b} : Multiset I) + ν) = δ)
    (h₄ : ({b} : Multiset I) + (({a} : Multiset I) + ν) = δ)
    (hp₂ : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = δ + ν₀)
    (hp₄ : ({b} : Multiset I) + ((({a} : Multiset I) + ν) + ν₀) = δ + ν₀)
    (hcross : ∀ c : CB ν,
      castTensorProductAlgebra Q Λ h₄ (mixedCrossElem (Q := Q) Λ ν b a) •
          (h₂ ▸ D_bₐ.iota (D_b.iota c) : CB δ) =
        castOp Q (plusLabels Λ Λc j hj)
          (plusWeight_assoc ν ν₀ a ▸ hp₄ :
            ({b} : Multiset I) + (({a} : Multiset I) + (ν + ν₀)) = δ + ν₀)
          (op (mixedCrossElem (Q := Q) (plusLabels Λ Λc j hj) (ν + ν₀) b a)) •
          (h₄ ▸ Dₐ_b.iota (Dₐ.iota c) : CB δ)) :
    Functor.whiskerRight (resCrossOfEq Λ hQ a b rfl h₂ rfl h₄) (OrdK ν) ≫
        (capECompIsoOfEq' D_b D_bₐ h₂ hp₂).hom =
      (capECompIsoOfEq' Dₐ Dₐ_b h₄ hp₄).hom ≫ Functor.whiskerLeft (OrdK δ)
        (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b) hp₂
          (plusWeight_assoc ν ν₀ a) hp₄) := by
  subst h₂
  refine NatTrans.ext (funext fun X => ?_)
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun c m => Res.ext (Res.ext ?_)))
  have hs : (((capECompIsoOfEq' Dₐ Dₐ_b h₄ hp₄).hom.app X).hom
      (DG.TensorProductOver.tmul (TA ν)ᵐᵒᵖ c m)).val.val =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA _) (CB _)))
        (N := InDegreeZero X) (TA _)ᵐᵒᵖ (h₄ ▸ Dₐ_b.iota (Dₐ.iota c)) m.val.val :=
    capEOrdIsoOfEq'_hom_tmul Dₐ_b h₄ hp₄ X (Dₐ.iota c) m.val
  change DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA _) (CB _)))
      (N := InDegreeZero X) (TA _)ᵐᵒᵖ (D_bₐ.iota (D_b.iota c))
        (((resCrossOfEq Λ hQ a b rfl rfl rfl h₄).app X).hom m).val.val =
    (((resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b) hp₂
      (plusWeight_assoc ν ν₀ a) hp₄).app ((OrdK _).obj X)).hom
        (((capECompIsoOfEq' Dₐ Dₐ_b h₄ hp₄).hom.app X).hom
          (DG.TensorProductOver.tmul (TA ν)ᵐᵒᵖ c m))).val.val
  erw [resCrossOfEq_ne_app_val Λ hQ hab, resCrossOfEq_ne_app_val (plusLabels Λ Λc j hj) hQ hab]
  erw [hs]
  refine (DG.TensorProductOver.tmul_neg (A := (TA _)ᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule (TA _) (CB _))) (N := InDegreeZero X)
    (D_bₐ.iota (D_b.iota (c : CB ν))) _).trans (congrArg Neg.neg ?_)
  erw [castOp_op, castOp_op]
  refine (DG.TensorProductOver.op_smul_tmul (A := (TA _)ᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule (TA _) (CB _))) (N := InDegreeZero X)
    (op (castTensorProductAlgebra Q Λ _ (mixedCrossElem (Q := Q) Λ ν b a)))
    (D_bₐ.iota (D_b.iota (c : CB ν))) m.val.val).symm.trans ?_
  have hc := hcross (c : CB ν)
  rw [castOp_op] at hc
  exact (congrArg (fun y : CB _ => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule (TA _) (CB _))) (N := InDegreeZero X) (TA _)ᵐᵒᵖ y m.val.val)
    hc).trans rfl

end Categorification.Stendhal.CupCap
