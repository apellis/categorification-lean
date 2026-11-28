/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MapDerivedNatTrans
import Categorification.WeightedKLR.RedStrands.BlackDerivedFunctors
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeTower

set_option backward.isDefEq.respectTransparency false

/-!
# Dots, crossings and adjunctions of `Eᵢ` and `Fᵢ` on derived categories

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1.
On right `T^λ`-modules the dot on the newest black strand acts on `Eᵢ` and minus the crossing of
the two newest black strands acts on `Eᵢ²` (`appendedDot`, `appendedCross`). They satisfy the
nilHecke relations, and `Fᵢ ⊣ Eᵢ` (`blackAdjunction`). Here these 2-morphisms are defined weight
by weight on modules (`blackDot`, `blackCross`, with the relations `blackCross_comp_blackCross`,
`blackCross_dot_sub`, `blackDot_cross_sub`), and lifted to the derived functors of the exact
functors `Eᵢ`, `Fᵢ` (`derivedBlackDot`, `derivedBlackCross`), where the same relations hold
(`derivedBlackCross_comp_derivedBlackCross`, `derivedBlackCross_dot_sub`,
`derivedBlackDot_cross_sub`).

Every adjunction between `Eᵢ` and `Fᵢ` on modules lifts to their derived functors:
`derivedBlackAdjunction` for `Fᵢ ⊣ Eᵢ`, and `derivedBlackResIndAdjunction` for an adjunction
`Eᵢ ⊣ Fᵢ` such as `clBlackResIndAdjunctionQ` (Theorem 4.31). The derived functors of `Eᵢ` and
`Fᵢ` are the dg derived tensor products `derivedBlackE`, `derivedBlackF` under the comparison of
derived categories (`derivedBlackEComparisonIso`, `derivedBlackFComparisonIso`).

`Fᵢ` is exact for Rouquier polynomials over a field (Theorem 4.31), the hypothesis `(C, hQ)` of
every statement involving `Fᵢ`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR

universe w u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "E" => blackE Q Λ i

private theorem blackE_additive'' (μ : Multiset I) : (blackE Q Λ i μ).Additive :=
  inferInstanceAs (resFunctor.{u, u} (appendBlackOp Q Λ i μ)).Additive

private theorem blackF_additive'' (μ : Multiset I) : (blackF Q Λ i μ).Additive :=
  inferInstanceAs (InductionAlong.functor.{u, u} (appendBlackOp Q Λ i μ)).Additive

attribute [local instance] blackE_additive'' blackF_additive''

/-! ### On modules -/

/-- **The dot on `Eᵢ`**: left multiplication by the dot on the newest black strand. -/
def blackDot : E ν ⟶ E ν where
  app M := ModuleCat.ofHom (resAct (op (appendedDot Q Λ i ν))
    (op_appendedDot_commute Q Λ i ν) M)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext
    (f.hom.map_smul (op (appendedDot Q Λ i ν)) r.val).symm)

/-- **The crossing on `Eᵢ²`**: left multiplication by minus the crossing of the two newest
black strands. -/
def blackCross : E (νᵢ) ⋙ E ν ⟶ E (νᵢ) ⋙ E ν where
  app M := ModuleCat.ofHom (resAct₂ (op (appendedCross Q Λ i ν))
    (op_appendedCross_fix Q Λ i ν) (op_appendedCross_commute Q Λ i ν) M)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext (Res.ext
    (f.hom.map_smul (op (appendedCross Q Λ i ν)) r.val.val).symm))

private theorem twoStep_ext {α β : E (νᵢ) ⋙ E ν ⟶ E (νᵢ) ⋙ E ν}
    (h : ∀ M r, ((α.app M).hom r).val.val = ((β.app M).hom r).val.val) : α = β :=
  NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun r =>
    Res.ext (Res.ext (h M r))))

private theorem smul_eq_add_of_sub' {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    {a b e : R} {w : N} (h : a - b = e) (hw : e • w = w) : a • w = w + b • w :=
  (eq_add_of_sub_eq' (by rw [← sub_smul, h, hw])).trans (add_comm _ _)

/-- The crossing squares to zero. -/
theorem blackCross_comp_blackCross : blackCross Q Λ i ν ≫ blackCross Q Λ i ν = 0 :=
  twoStep_ext Q Λ i ν fun M r => by
    change op (appendedCross Q Λ i ν) • op (appendedCross Q Λ i ν) • r.val.val = 0
    rw [smul_smul, op_appendedCross_sq, zero_smul]

/-- The nilHecke relation `y' τ - τ y = 1` on `Eᵢ²`, with `y'` the dot on the inner and `y` the
dot on the outer `Eᵢ`. -/
theorem blackCross_dot_sub :
    blackCross Q Λ i ν ≫ Functor.whiskerRight (blackDot Q Λ i (νᵢ)) (E ν) -
        Functor.whiskerLeft (E (νᵢ)) (blackDot Q Λ i ν) ≫ blackCross Q Λ i ν = 𝟙 _ := by
  refine sub_eq_of_eq_add (twoStep_ext Q Λ i ν fun M r => ?_)
  change op (appendedDot Q Λ i (νᵢ)) • op (appendedCross Q Λ i ν) • r.val.val =
    r.val.val + op (appendedCross Q Λ i ν) •
      appendBlackOp Q Λ i (νᵢ) (op (appendedDot Q Λ i ν)) • r.val.val
  rw [smul_smul, smul_smul]
  exact smul_eq_add_of_sub' (op_appendedCross_appendedDot Q Λ i ν) (congrArg Res.val r.prop)

/-- The nilHecke relation `τ y' - y τ = 1` on `Eᵢ²`. -/
theorem blackDot_cross_sub :
    Functor.whiskerRight (blackDot Q Λ i (νᵢ)) (E ν) ≫ blackCross Q Λ i ν -
        blackCross Q Λ i ν ≫ Functor.whiskerLeft (E (νᵢ)) (blackDot Q Λ i ν) = 𝟙 _ := by
  refine sub_eq_of_eq_add (twoStep_ext Q Λ i ν fun M r => ?_)
  change op (appendedCross Q Λ i ν) • op (appendedDot Q Λ i (νᵢ)) • r.val.val =
    r.val.val + appendBlackOp Q Λ i (νᵢ) (op (appendedDot Q Λ i ν)) •
      op (appendedCross Q Λ i ν) • r.val.val
  rw [smul_smul, smul_smul]
  exact smul_eq_add_of_sub' (op_appendedDot_appendedCross Q Λ i ν) (congrArg Res.val r.prop)

set_option hygiene false in
local notation "νᵢᵢ" => ((Singleton.singleton i : Multiset I) + νᵢ)

private theorem threeStep_ext {α β : E (νᵢᵢ) ⋙ E (νᵢ) ⋙ E ν ⟶ E (νᵢᵢ) ⋙ E (νᵢ) ⋙ E ν}
    (h : ∀ M r, ((α.app M).hom r).val.val.val = ((β.app M).hom r).val.val.val) : α = β :=
  NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun r =>
    Res.ext (Res.ext (Res.ext (h M r)))))

/-- The braid relation on `Eᵢ³`. -/
theorem blackCross_braid :
    Functor.whiskerRight (blackCross Q Λ i (νᵢ)) (E ν) ≫
        Functor.whiskerLeft (E (νᵢᵢ)) (blackCross Q Λ i ν) ≫
          Functor.whiskerRight (blackCross Q Λ i (νᵢ)) (E ν) =
      Functor.whiskerLeft (E (νᵢᵢ)) (blackCross Q Λ i ν) ≫
        Functor.whiskerRight (blackCross Q Λ i (νᵢ)) (E ν) ≫
          Functor.whiskerLeft (E (νᵢᵢ)) (blackCross Q Λ i ν) :=
  threeStep_ext Q Λ i ν fun M r => by
    change op (appendedCross Q Λ i (νᵢ)) •
        appendBlackOp Q Λ i (νᵢᵢ) (op (appendedCross Q Λ i ν)) •
          op (appendedCross Q Λ i (νᵢ)) • r.val.val.val =
      appendBlackOp Q Λ i (νᵢᵢ) (op (appendedCross Q Λ i ν)) •
        op (appendedCross Q Λ i (νᵢ)) •
          appendBlackOp Q Λ i (νᵢᵢ) (op (appendedCross Q Λ i ν)) • r.val.val.val
    rw [smul_smul, smul_smul, smul_smul, smul_smul, op_appendedCross_braid]

/-! ### On derived categories -/

variable [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ (νᵢ))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ
    ((Singleton.singleton i : Multiset I) + νᵢ))ᵐᵒᵖ)]

/-- **The dot on the derived `Eᵢ`.** -/
def derivedBlackDot : (E ν).mapDerivedCategory ⟶ (E ν).mapDerivedCategory :=
  (blackDot Q Λ i ν).mapDerivedCategory

/-- **The crossing on the derived `Eᵢ²`.** -/
def derivedBlackCross :
    (E (νᵢ)).mapDerivedCategory ⋙ (E ν).mapDerivedCategory ⟶
      (E (νᵢ)).mapDerivedCategory ⋙ (E ν).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (E (νᵢ)) (E ν)).hom ≫
    (blackCross Q Λ i ν).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso (E (νᵢ)) (E ν)).inv

/-- The derived crossing squares to zero. -/
theorem derivedBlackCross_comp_derivedBlackCross :
    derivedBlackCross Q Λ i ν ≫ derivedBlackCross Q Λ i ν = 0 := by
  simp only [derivedBlackCross, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← NatTrans.mapDerivedCategory_comp_assoc, blackCross_comp_blackCross,
    NatTrans.mapDerivedCategory_zero, Limits.zero_comp, Limits.comp_zero]

/-- The nilHecke relation `y' τ - τ y = 1` on the derived `Eᵢ²`. -/
theorem derivedBlackCross_dot_sub :
    derivedBlackCross Q Λ i ν ≫
        Functor.whiskerRight (derivedBlackDot Q Λ i (νᵢ)) (E ν).mapDerivedCategory -
      Functor.whiskerLeft (E (νᵢ)).mapDerivedCategory (derivedBlackDot Q Λ i ν) ≫
        derivedBlackCross Q Λ i ν = 𝟙 _ := by
  simp only [derivedBlackDot, derivedBlackCross, NatTrans.whiskerRight_mapDerivedCategory,
    NatTrans.whiskerLeft_mapDerivedCategory, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← NatTrans.mapDerivedCategory_comp_assoc, ← NatTrans.mapDerivedCategory_comp_assoc,
    ← Preadditive.comp_sub, ← Preadditive.sub_comp, ← NatTrans.mapDerivedCategory_sub,
    blackCross_dot_sub, NatTrans.mapDerivedCategory_id, Category.id_comp, Iso.hom_inv_id]

/-- The nilHecke relation `τ y' - y τ = 1` on the derived `Eᵢ²`. -/
theorem derivedBlackDot_cross_sub :
    Functor.whiskerRight (derivedBlackDot Q Λ i (νᵢ)) (E ν).mapDerivedCategory ≫
        derivedBlackCross Q Λ i ν -
      derivedBlackCross Q Λ i ν ≫
        Functor.whiskerLeft (E (νᵢ)).mapDerivedCategory (derivedBlackDot Q Λ i ν) = 𝟙 _ := by
  simp only [derivedBlackDot, derivedBlackCross, NatTrans.whiskerRight_mapDerivedCategory,
    NatTrans.whiskerLeft_mapDerivedCategory, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← NatTrans.mapDerivedCategory_comp_assoc, ← NatTrans.mapDerivedCategory_comp_assoc,
    ← Preadditive.comp_sub, ← Preadditive.sub_comp, ← NatTrans.mapDerivedCategory_sub,
    blackDot_cross_sub, NatTrans.mapDerivedCategory_id, Category.id_comp, Iso.hom_inv_id]

section Braid

variable [HasDerivedCategory.{w} (ModuleCat.{u} (TensorProductAlgebra k Q Λ
    ((Singleton.singleton i : Multiset I) + νᵢᵢ))ᵐᵒᵖ)]

/-- The identification of the derived `Eᵢ³` with the derived functor of `Eᵢ³`. -/
private def tripleIso :
    (E (νᵢᵢ)).mapDerivedCategory ⋙ (E (νᵢ)).mapDerivedCategory ⋙ (E ν).mapDerivedCategory ≅
      (E (νᵢᵢ) ⋙ E (νᵢ) ⋙ E ν).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso (E (νᵢ)) (E ν)) ≪≫
    Functor.mapDerivedCategoryCompIso (E (νᵢᵢ)) (E (νᵢ) ⋙ E ν)

private theorem tripleIso_hom_eq : (tripleIso Q Λ i ν).hom =
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIso (E (νᵢᵢ)) (E (νᵢ))).hom
        (E ν).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso (E (νᵢᵢ) ⋙ E (νᵢ)) (E ν)).hom :=
  (Functor.mapDerivedCategoryCompIso_assoc _ _ _).symm

@[reassoc]
private theorem whiskerRight_cross_tripleIso :
    Functor.whiskerRight (derivedBlackCross Q Λ i (νᵢ)) (E ν).mapDerivedCategory ≫
        (tripleIso Q Λ i ν).hom =
      (tripleIso Q Λ i ν).hom ≫
        (Functor.whiskerRight (blackCross Q Λ i (νᵢ)) (E ν)).mapDerivedCategory := by
  simp only [tripleIso_hom_eq, derivedBlackCross, Functor.whiskerRight_comp, Category.assoc]
  rw [← Functor.whiskerRight_comp_assoc
      (Functor.mapDerivedCategoryCompIso (E (νᵢᵢ)) (E (νᵢ))).inv, Iso.inv_hom_id,
    Functor.whiskerRight_id', Category.id_comp, ← NatTrans.mapDerivedCategory_whiskerRight]

@[reassoc]
private theorem whiskerLeft_cross_tripleIso :
    Functor.whiskerLeft (E (νᵢᵢ)).mapDerivedCategory (derivedBlackCross Q Λ i ν) ≫
        (tripleIso Q Λ i ν).hom =
      (tripleIso Q Λ i ν).hom ≫
        (Functor.whiskerLeft (E (νᵢᵢ)) (blackCross Q Λ i ν)).mapDerivedCategory := by
  simp only [tripleIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom, derivedBlackCross,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [← Functor.whiskerLeft_comp_assoc _ (Functor.mapDerivedCategoryCompIso (E (νᵢ)) (E ν)).inv,
    Iso.inv_hom_id, Functor.whiskerLeft_id', Category.id_comp,
    ← NatTrans.mapDerivedCategory_whiskerLeft]

/-- **The braid relation on the derived `Eᵢ³`.** -/
theorem derivedBlackCross_braid :
    Functor.whiskerRight (derivedBlackCross Q Λ i (νᵢ)) (E ν).mapDerivedCategory ≫
        Functor.whiskerLeft (E (νᵢᵢ)).mapDerivedCategory (derivedBlackCross Q Λ i ν) ≫
          Functor.whiskerRight (derivedBlackCross Q Λ i (νᵢ)) (E ν).mapDerivedCategory =
      Functor.whiskerLeft (E (νᵢᵢ)).mapDerivedCategory (derivedBlackCross Q Λ i ν) ≫
        Functor.whiskerRight (derivedBlackCross Q Λ i (νᵢ)) (E ν).mapDerivedCategory ≫
          Functor.whiskerLeft (E (νᵢᵢ)).mapDerivedCategory (derivedBlackCross Q Λ i ν) := by
  rw [← cancel_mono (tripleIso Q Λ i ν).hom]
  simp only [Category.assoc, whiskerRight_cross_tripleIso, whiskerLeft_cross_tripleIso,
    whiskerRight_cross_tripleIso_assoc, whiskerLeft_cross_tripleIso_assoc]
  simp only [← NatTrans.mapDerivedCategory_comp]
  rw [blackCross_braid]

end Braid

/-! ### Adjunctions -/

/-- **`Fᵢ ⊣ Eᵢ` on derived categories**, the lift of `blackAdjunction`. -/
def derivedBlackAdjunction (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
    letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
    (blackF Q Λ i ν).mapDerivedCategory ⊣ (E ν).mapDerivedCategory :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
  letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
  (blackAdjunction Q Λ i ν).mapDerivedCategory

/-- **An adjunction `Eᵢ ⊣ Fᵢ` on modules lifts to derived categories**; it applies to the
adjunction of Theorem 4.31 (`clBlackResIndAdjunctionQ`). -/
def derivedBlackResIndAdjunction (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (adj : E ν ⊣ blackF Q Λ i ν) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
    letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
    (E ν).mapDerivedCategory ⊣ (blackF Q Λ i ν).mapDerivedCategory :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
  letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
  adj.mapDerivedCategory

end Categorification.Stendhal
