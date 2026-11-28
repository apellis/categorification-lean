/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleRouqFamily
import Categorification.WeightedKLR.RedStrands.BlackModuleMixedInversion

/-!
# Brundan's mixed inversion for Webster's action on `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31
(`E_i F_j ≅ F_j E_i` for `i ≠ j`), in Brundan's form (arXiv:1501.00350v1, Definition 1.1,
(1.7), `TwoRep.BrundanMixedInversion`), for the Rouquier family `blackModuleRouqFamily` on the
weight spaces of all right `T^λ`-modules (the abelian counterpart of
`blackRouqFamily_mixedInversion`).

The mixed sideways crossing `E_i F_j ⟶ F_j E_i` on weight spaces is block diagonal
(`blackMod_mixedSigma_app`): on a block `{j} + γ` it is the mate of the crossing
`indCrossOfEq` of the block inductions, invertible by the module statement
`blackModuleMixedInversion`, and on a block without a strand of colour `j` its source and
target vanish (`blackModuleRouqFamily_mixedInversion`). No derived categories are involved.

The hypotheses are those of `blackModuleRouqFamily`; no route hypothesis is added.
-/


set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory MulOpposite InductionAlong
  QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram
  KL3.Diagram NatTrans

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w u₁

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}

set_option hygiene false in
local notation "D" β => ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

/-! ### The mixed inversion -/

theorem blackMod_gen₂_counit_of_eq (i j : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX j = z) (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x)
    {δ : WeightBlocks RD Λ₀ z} (hd : blockSucc RD Λ₀ j h₂ (blockSucc RD Λ₀ i h₁ γ) = δ) :
    Eq (gen₂ (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ j h₂) (moduleFBlock Q Λ RD Λ₀ i h₁)
        (moduleFBlock Q Λ RD Λ₀ j h₂)
        ((blockRes (blockSucc RD Λ₀ i h₁) (moduleEBlock Q Λ RD Λ₀ i h₁)).obj M) γ rfl hd ≫
      (TwoRep.blockSum (blockSucc RD Λ₀ j h₂) (moduleFBlock Q Λ RD Λ₀ j h₂)).map
        ((blockCounitNat (blockSucc RD Λ₀ i h₁)
          (fun _ _ hβ => blackAdjOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ))).app M) δ)
      ((moduleFBlock Q Λ RD Λ₀ j h₂ (blockSucc RD Λ₀ i h₁ γ) δ hd).map
          ((blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ)).counit.app
            (M (blockSucc RD Λ₀ i h₁ γ))) ≫
        blockι (blockSucc RD Λ₀ j h₂) (moduleFBlock Q Λ RD Λ₀ j h₂) M
          ⟨blockSucc RD Λ₀ i h₁ γ, hd⟩) := by
  subst hd
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact biproduct.ι_desc _ _

/-- **The mixed sideways crossing on weight spaces, blockwise**: on the generator of `Fᵢ Eⱼ`
at the block `{j} + γ`, it is the mate of the block crossing at `{i} + γ`, followed by
the generator of `Eⱼ Fᵢ`. -/
theorem blackMod_mixedSigma_app (hsym : KLRSymm Q) (i j : I) {x y z t : X}
    (hj : x + RD.iX j = y) (hi' : y + RD.iX i = t) (hi : x + RD.iX i = z)
    (hj' : z + RD.iX j = t) (M : ∀ β : WeightBlocks RD Λ₀ z, D β.1)
    (γ : WeightBlocks RD Λ₀ x) :
    Eq (blockι (blockSucc RD Λ₀ j hj) (moduleFBlock Q Λ RD Λ₀ j hj)
        ((blockRes (blockSucc RD Λ₀ i hi) (moduleEBlock Q Λ RD Λ₀ i hi)).obj M) ⟨γ, rfl⟩ ≫
      (mateEquiv (blackModAdj Q Λ RD Λ₀ i hi) (blackModAdj Q Λ RD Λ₀ i hi')
        (blackModCross Q Λ RD Λ₀ hsym i j hj hi' hi hj')).hom.app M
          (blockSucc RD Λ₀ j hj γ))
      ((mateNat
          (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ))).unit
          (indCrossOfEq Λ hsym i j (blockSucc_step RD Λ₀ j hj γ)
            (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ)) (blockSucc_step RD Λ₀ i hi γ)
            (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm))
          (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i hi γ)).counit).app
            (M (blockSucc RD Λ₀ i hi γ)) ≫
        (moduleEBlock Q Λ RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ) _ rfl).map
          (blockι (blockSucc RD Λ₀ j hj') (moduleFBlock Q Λ RD Λ₀ j hj') M
            ⟨blockSucc RD Λ₀ i hi γ, (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm⟩)) := by
  rw [LinearCat.mate_hom]
  have hU := (blackAdjOfEq Q Λ i
      (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ))).unit_naturality
    (blockι (blockSucc RD Λ₀ j hj) (moduleFBlock Q Λ RD Λ₀ j hj)
        ((blockRes (blockSucc RD Λ₀ i hi) (moduleEBlock Q Λ RD Λ₀ i hi)).obj M) ⟨γ, rfl⟩)
  have hT := gen₂_blackModCross Q Λ RD Λ₀ hsym i j hj hi' hi hj'
    ((blockRes (blockSucc RD Λ₀ i hi) (moduleEBlock Q Λ RD Λ₀ i hi)).obj M) γ rfl rfl rfl
    (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm
  have hC := blackMod_gen₂_counit_of_eq Q Λ RD Λ₀ i j hi hj' M γ
    (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm
  have key := (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))))
  simp only [mateNat, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    pi_comp_apply_blocks]
  rw [blackModAdj_unit_app Q Λ RD Λ₀ i hi'
    (((blackModF Q Λ RD Λ₀ i hi).obj ⋙ (blackModE Q Λ RD Λ₀ j hj).obj).obj M)
    (blockSucc RD Λ₀ j hj γ)]
  simp only [Category.assoc]
  erw [← reassoc_of% hU]
  have key' := congrArg
    (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ))).map key
  simp only [Functor.map_comp] at key'
  exact congrArg (_ ≫ ·) key'

/-! ### The family -/

section Family

variable {Q Λ RD Λ₀} {hQ : IsRouquierQ C Q} {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom) (hsym : KLRSymm Q)
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))

/-- **Brundan's mixed inversion for Webster's action on `T^λ`-modules** (Brundan,
arXiv:1501.00350v1, (1.7); Webster, arXiv:1309.3796v3, Theorem 4.31, `E_i F_j ≅ F_j E_i` for
`i ≠ j`), from the module statement `blackModuleMixedInversion`. -/
theorem blackModuleRouqFamily_mixedInversion :
    BrundanMixedInversion (blackModuleRouqFamily hP hwf hsym hΛ₀) := by
  have hM := blackModuleMixedInversion hP hwf hsym
  intro i j hij x y z t hj hi' hi hj'
  change IsIso (mateEquiv (blackModAdj Q Λ RD Λ₀ i hi) (blackModAdj Q Λ RD Λ₀ i hi')
    (blackModCross Q Λ RD Λ₀ hsym i j hj hi' hi hj'))
  suffices h : IsIso ((LinearCat.homForget _ _).map
      (mateEquiv (blackModAdj Q Λ RD Λ₀ i hi) (blackModAdj Q Λ RD Λ₀ i hi')
        (blackModCross Q Λ RD Λ₀ hsym i j hj hi' hi hj'))) from
    isIso_of_fully_faithful (LinearCat.homForget _ _) _
  rw [LinearCat.homForget_map]
  refine (NatTrans.isIso_iff_isIso_app _).2 fun M => ?_
  refine (isIso_pi_iff _).2 fun β => ?_
  by_cases hβ : j ∈ β.1
  · obtain ⟨γ, rfl⟩ := exists_blockSucc_of_mem RD Λ₀ j hj β hβ
    have e := blackMod_mixedSigma_app Q Λ RD Λ₀ hsym i j hj hi' hi hj' M γ
    have := hM i j hij (blockSucc_step RD Λ₀ j hj γ)
      (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ)) (blockSucc_step RD Λ₀ i hi γ)
      (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm)
    let e₁ := blockιIso (blockSucc RD Λ₀ j hj) (moduleFBlock Q Λ RD Λ₀ j hj)
      ((blockRes (blockSucc RD Λ₀ i hi) (moduleEBlock Q Λ RD Λ₀ i hi)).obj M) ⟨γ, rfl⟩
      (fun _ => Subsingleton.elim _ _)
    let e₂ := blockιIso (blockSucc RD Λ₀ j hj') (moduleFBlock Q Λ RD Λ₀ j hj') M
      ⟨blockSucc RD Λ₀ i hi γ, (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm⟩
      (fun _ => Subsingleton.elim _ _)
    have e' := (Iso.eq_inv_comp e₁).2 e
    erw [e']
    refine IsIso.comp_isIso' e₁.isIso_inv (IsIso.comp_isIso' ?_ ?_)
    · exact NatIso.isIso_app_of_isIso _ _
    · exact ((moduleEBlock Q Λ RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ) _ rfl).mapIso e₂).isIso_hom
  · refine isIso_of_source_target_iso_zero _
      (IsZero.isoZero (blockSum_obj_isZero (blockSucc RD Λ₀ j hj)
        (moduleFBlock Q Λ RD Λ₀ j hj) _ (isEmpty_of_not_mem RD Λ₀ j hj β hβ)))
      (IsZero.isoZero (Functor.map_isZero (moduleEBlock Q Λ RD Λ₀ i hi' β _ rfl)
        (blockSum_obj_isZero (blockSucc RD Λ₀ j hj') (moduleFBlock Q Λ RD Λ₀ j hj') M
          (isEmpty_of_not_mem RD Λ₀ j hj' _ ?_))))
    rw [blockSucc_val]
    intro hm
    rcases Multiset.mem_add.1 hm with h | h
    · exact hij.symm (Multiset.mem_singleton.1 h)
    · exact hβ h

end Family

end Categorification.Stendhal
