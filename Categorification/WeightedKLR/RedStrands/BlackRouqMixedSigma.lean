/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqLocQ
import Categorification.Algebra.MapDerivedMate
import Categorification.TwoRep.RouqFullCL

/-!
# Brundan's mixed inversion for Webster's derived action, reduced to modules

Brundan, arXiv:1501.00350v1, (1.7) (`TwoRep.BrundanMixedInversion`), for the weight-indexed
Rouquier family `blackRouqFamily` of Webster's derived action on `D(T^λ)`
(arXiv:1309.3796v3, §4.6, §5.1, Theorem 4.31).

As in the cyclotomic case (`KLR.CyclotomicAction.cyclotomicFamily_mixedInversion`), the mixed
sideways crossing `E_i F_j ⟶ F_j E_i` on weight spaces is block diagonal
(`blackRouq_mixedSigma_app`): on a block `{j} + γ` it is the mate of the derived crossing
`derivedIndCrossOfEq` of the block functors, and on a block without a strand of colour `j` its
source and target vanish. The mate of a derived crossing is the derived mate
(`NatTrans.derivedComp_mateNat`), so invertibility reduces to the module statement
`BlackModuleMixedInversion`: for `i ≠ j`, the mate of the crossing `indCrossOfEq` of
inductions of right `T^λ`-modules through `Fᵢ ⊣ Eᵢ` is invertible
(`blackRouqFamily_mixedInversion_of`). With Brundan's upward KLR relations as a further
hypothesis, `blackPresCLPseudofunctorOf` is the resulting action of Cautis–Lauda's `U_Q(g)`.

`BlackModuleMixedInversion` is an explicit hypothesis of the reductions here. It is the module
form of the relation `E_i F_j ≅ F_j E_i` (`i ≠ j`) of Webster's Theorem 4.31, and it is proved
in `BlackModuleMixedInversion.lean` (`blackModuleMixedInversion`), which also gives the
hypothesis-free `blackRouqFamily_mixedInversion`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory QuantumGroup
  QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram
  NatTrans

open scoped Classical

universe u w w₂ u₁

variable {I : Type u} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : IsRouquierQ C Q)

/-- **Brundan's mixed inversion on `T^λ`-modules** (the module form of Webster,
arXiv:1309.3796v3, Theorem 4.31, `E_i F_j ≅ F_j E_i` for `i ≠ j`): for `i ≠ j`, the mate
through `Fᵢ ⊣ Eᵢ` of the crossing `indCrossOfEq` of inductions is invertible. -/
def BlackModuleMixedInversion (hsym : KLRSymm Q) : Prop :=
  ∀ (i j : I), i ≠ j → ∀ {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ),
    IsIso (mateNat (blackAdjOfEq Q Λ i h₂).unit (indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄)
      (blackAdjOfEq Q Λ i h₃).counit)

variable [∀ β : Multiset I,
    HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]

/-- **The derived mixed mate on blocks is invertible**, from the module statement. -/
theorem derivedMixedMate_isIso {hsym : KLRSymm Q} (hM : BlackModuleMixedInversion Λ hsym)
    (i j : I) (hij : i ≠ j) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    IsIso (mateNat (derivedAdjOfEq Λ hQ i h₂).unit
      (derivedIndCrossOfEq Λ hQ hsym i j h₁ h₂ h₃ h₄) (derivedAdjOfEq Λ hQ i h₃).counit) := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₂
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₁
  have := blackFOfEq_preservesFiniteLimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteColimits Λ hQ i h₃
  have := blackFOfEq_preservesFiniteLimits Λ hQ j h₄
  have := blackFOfEq_preservesFiniteColimits Λ hQ j h₄
  have := hM i j hij h₁ h₂ h₃ h₄
  unfold derivedAdjOfEq derivedIndCrossOfEq
  exact isIso_mateNat_derived _ _ _

variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

set_option hygiene false in
local notation "D" β => DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

/-- The generator of `Fⱼ Fᵢ` on `Fᵢ Eᵢ` followed by the counit, for any target block. -/
theorem blackRouq_gen₂_counit_of_eq (i j : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX j = z) (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x)
    {δ : WeightBlocks RD Λ₀ z} (hd : blockSucc RD Λ₀ j h₂ (blockSucc RD Λ₀ i h₁ γ) = δ) :
    Eq (gen₂ (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ j h₂) (derivedFBlock Λ hQ RD Λ₀ i h₁)
        (derivedFBlock Λ hQ RD Λ₀ j h₂)
        ((blockRes (blockSucc RD Λ₀ i h₁) (derivedEBlock Q Λ RD Λ₀ i h₁)).obj M) γ rfl hd ≫
      (TwoRep.blockSum (blockSucc RD Λ₀ j h₂) (derivedFBlock Λ hQ RD Λ₀ j h₂)).map
        ((blockCounitNat (blockSucc RD Λ₀ i h₁)
          (fun _ _ hβ => derivedAdjOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ))).app M) δ)
      ((derivedFBlock Λ hQ RD Λ₀ j h₂ (blockSucc RD Λ₀ i h₁ γ) δ hd).map
          ((derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ)).counit.app
            (M (blockSucc RD Λ₀ i h₁ γ))) ≫
        blockι (blockSucc RD Λ₀ j h₂) (derivedFBlock Λ hQ RD Λ₀ j h₂) M
          ⟨blockSucc RD Λ₀ i h₁ γ, hd⟩) := by
  subst hd
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact biproduct.ι_desc _ _

/-- **The mixed sideways crossing on weight spaces, blockwise**: on the generator of `Fᵢ Eⱼ`
at the block `{j} + γ`, it is the mate of the derived block crossing at `{i} + γ`, followed by
the generator of `Eⱼ Fᵢ`. -/
theorem blackRouq_mixedSigma_app (hsym : KLRSymm Q) (i j : I) {x y z t : X}
    (hj : x + RD.iX j = y) (hi' : y + RD.iX i = t) (hi : x + RD.iX i = z)
    (hj' : z + RD.iX j = t) (M : ∀ β : WeightBlocks RD Λ₀ z, D β.1)
    (γ : WeightBlocks RD Λ₀ x) :
    Eq (blockι (blockSucc RD Λ₀ j hj) (derivedFBlock Λ hQ RD Λ₀ j hj)
        ((blockRes (blockSucc RD Λ₀ i hi) (derivedEBlock Q Λ RD Λ₀ i hi)).obj M) ⟨γ, rfl⟩ ≫
      (mateEquiv (blackRouqAdj Λ hQ RD Λ₀ i hi) (blackRouqAdj Λ hQ RD Λ₀ i hi')
        (blackRouqCross Λ hQ RD Λ₀ hsym i j hj hi' hi hj')).hom.app M
          (blockSucc RD Λ₀ j hj γ))
      ((mateNat
          (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ))).unit
          (derivedIndCrossOfEq Λ hQ hsym i j (blockSucc_step RD Λ₀ j hj γ)
            (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ)) (blockSucc_step RD Λ₀ i hi γ)
            (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm))
          (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i hi γ)).counit).app
            (M (blockSucc RD Λ₀ i hi γ)) ≫
        (derivedEBlock Q Λ RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ) _ rfl).map
          (blockι (blockSucc RD Λ₀ j hj') (derivedFBlock Λ hQ RD Λ₀ j hj') M
            ⟨blockSucc RD Λ₀ i hi γ, (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm⟩)) := by
  rw [LinearCat.mate_hom]
  have hU := (derivedAdjOfEq Λ hQ i
      (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ))).unit_naturality
    (blockι (blockSucc RD Λ₀ j hj) (derivedFBlock Λ hQ RD Λ₀ j hj)
        ((blockRes (blockSucc RD Λ₀ i hi) (derivedEBlock Q Λ RD Λ₀ i hi)).obj M) ⟨γ, rfl⟩)
  have hT := gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i j hj hi' hi hj'
    ((blockRes (blockSucc RD Λ₀ i hi) (derivedEBlock Q Λ RD Λ₀ i hi)).obj M) γ rfl rfl rfl
    (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm
  have hC := blackRouq_gen₂_counit_of_eq Λ hQ RD Λ₀ i j hi hj' M γ
    (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm
  have key := (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))))
  simp only [mateNat, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    pi_comp_apply_blocks]
  rw [blackRouqAdj_unit_app Λ hQ RD Λ₀ i hi'
    (((blackRouqF Q Λ RD Λ₀ i hi).obj ⋙ (blackRouqE Λ hQ RD Λ₀ j hj).obj).obj M)
    (blockSucc RD Λ₀ j hj γ)]
  simp only [Category.assoc]
  erw [← reassoc_of% hU]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  have key' := congrArg
    (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ))).map key
  erw [key']
  simp only [Functor.map_comp]
  rfl

section Family

variable {Λ hQ RD Λ₀} {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom) {hsym : KLRSymm Q}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))

/-- **Brundan's mixed inversion for Webster's derived action** (Brundan, arXiv:1501.00350v1,
(1.7); Webster, arXiv:1309.3796v3, Theorem 4.31), from the module statement
`BlackModuleMixedInversion` (proved as `blackModuleMixedInversion`). The family carries the
hypotheses of `blackRouqFamily`: Theorem 4.30 (`CoverRelsNegligible`, `WFDom`), exactness
(`hQ`), `KLRSymm Q` and the route hypothesis `hΛ₀`. -/
theorem blackRouqFamily_mixedInversion_of (hM : BlackModuleMixedInversion Λ hsym) :
    BrundanMixedInversion (blackRouqFamily.{u, w} hP hwf hsym hΛ₀) := by
  intro i j hij x y z t hj hi' hi hj'
  change IsIso (mateEquiv (blackRouqAdj Λ hQ RD Λ₀ i hi) (blackRouqAdj Λ hQ RD Λ₀ i hi')
    (blackRouqCross Λ hQ RD Λ₀ hsym i j hj hi' hi hj'))
  suffices h : IsIso ((LinearCat.homForget _ _).map
      (mateEquiv (blackRouqAdj Λ hQ RD Λ₀ i hi) (blackRouqAdj Λ hQ RD Λ₀ i hi')
        (blackRouqCross Λ hQ RD Λ₀ hsym i j hj hi' hi hj'))) from
    isIso_of_fully_faithful (LinearCat.homForget _ _) _
  rw [LinearCat.homForget_map]
  refine (NatTrans.isIso_iff_isIso_app _).2 fun M => ?_
  refine (isIso_pi_iff _).2 fun β => ?_
  by_cases hβ : j ∈ β.1
  · obtain ⟨γ, rfl⟩ := exists_blockSucc_of_mem RD Λ₀ j hj β hβ
    have e := blackRouq_mixedSigma_app Λ hQ RD Λ₀ hsym i j hj hi' hi hj' M γ
    have := derivedMixedMate_isIso Λ hQ hM i j hij (blockSucc_step RD Λ₀ j hj γ)
      (blockSucc_step RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ)) (blockSucc_step RD Λ₀ i hi γ)
      (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm)
    let e₁ := blockιIso (blockSucc RD Λ₀ j hj) (derivedFBlock Λ hQ RD Λ₀ j hj)
      ((blockRes (blockSucc RD Λ₀ i hi) (derivedEBlock Q Λ RD Λ₀ i hi)).obj M) ⟨γ, rfl⟩
      (fun _ => Subsingleton.elim _ _)
    let e₂ := blockιIso (blockSucc RD Λ₀ j hj') (derivedFBlock Λ hQ RD Λ₀ j hj') M
      ⟨blockSucc RD Λ₀ i hi γ, (blockSucc_comm RD Λ₀ i j hj hi' hi hj' γ).symm⟩
      (fun _ => Subsingleton.elim _ _)
    have e' := (Iso.eq_inv_comp e₁).2 e
    erw [e']
    refine IsIso.comp_isIso' e₁.isIso_inv (IsIso.comp_isIso' ?_ ?_)
    · exact NatIso.isIso_app_of_isIso _ _
    · exact ((derivedEBlock Q Λ RD Λ₀ i hi' (blockSucc RD Λ₀ j hj γ) _ rfl).mapIso e₂).isIso_hom
  · refine isIso_of_source_target_iso_zero _
      (IsZero.isoZero (blockSum_obj_isZero (blockSucc RD Λ₀ j hj)
        (derivedFBlock Λ hQ RD Λ₀ j hj) _ (isEmpty_of_not_mem RD Λ₀ j hj β hβ)))
      (IsZero.isoZero (Functor.map_isZero (derivedEBlock Q Λ RD Λ₀ i hi' β _ rfl)
        (blockSum_obj_isZero (blockSucc RD Λ₀ j hj') (derivedFBlock Λ hQ RD Λ₀ j hj') M
          (isEmpty_of_not_mem RD Λ₀ j hj' _ ?_))))
    rw [blockSucc_val]
    intro hm
    rcases Multiset.mem_add.1 hm with h | h
    · exact hij.symm (Multiset.mem_singleton.1 h)
    · exact hβ h

/-- **Cautis–Lauda's normalized `U_Q(g)` acts on Webster's derived categories** (Brundan,
arXiv:1501.00350v1, Theorem 1.2, through `RouqFamily.presCLPseudofunctor`; Webster,
arXiv:1309.3796v3, Theorem 4.31), from Brundan's upward KLR relations `H` for distinct colours
and the module mixed inversion `hM`, both explicit hypotheses of this assembly, with `r_i = 1`
and the homogeneity condition `hq` on the scalars. -/
def blackPresCLPseudofunctorOf (Sc : CL.CLScalars C k)
    (H : BrundanUpKLR (blackRouqFamily.{u, w} hP hwf hsym hΛ₀) Sc)
    (hM : BlackModuleMixedInversion Λ hsym) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    Pseudofunctor (RevBicat (CL.presCL RD k Sc).Bicat) (LinearCat k) :=
  (blackRouqFamily.{u, w} hP hwf hsym hΛ₀).presCLPseudofunctor Sc H
    (blackRouqFamily_mixedInversion_of hP hwf hΛ₀ hM) hr hq

end Family

end Categorification.Stendhal
