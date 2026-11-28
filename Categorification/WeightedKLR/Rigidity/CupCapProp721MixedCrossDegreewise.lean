/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CrossDegreewise
import Categorification.WeightedKLR.Rigidity.CupCapProp721TwoStepComparisonMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721MixedRightAdjoint
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftF
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEMixed
import Categorification.Algebra.RCornerTwoStepMixedCoefficient

/-!
# The crossing of different colours on the dg derived `𝔈_a 𝔈_b` commutes with the shift

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The crossing of two black strands of different colours `a ≠ b` on the dg
derived functors (`CupCap.dgMixedCross`) is the conjugate of the derived crossing `resCrossOfEq`
along the comparisons with Mathlib's derived categories. On dg modules it is left
multiplication by the crossing element `c` of `resCrossOfEq` (minus the cast of
`mixedCrossElem`, `CupCap.resCrossOfEq_ne_app_val`), from
`e' T^λ_{ν+a} ⊗ (e' T^λ_{ν+a+b} ⊗ -)` to `e' T^λ_{ν+b} ⊗ (e' T^λ_{ν+a+b} ⊗ -)`
(`Stendhal.mixedCrossTensorNat`). Degreewise both send `m ⊗ (n ⊗ x)` to `c φ(m) n x`
(`Stendhal.mixedCrossTensorNat_degreewise`), so `CupCap.dgMixedCross` commutes with the derived
tensor shift (`Stendhal.dgMixedCross_commShift`). The first functor `𝔈_b` is taken along the
content equality `mixedSwap`; it is the derived tensor product with the corner of
`appendBlackOpOfEq` (`CupCap.derivedBlackEOfEqTensorIso`).

## Main results

* `CupCap.derivedBlackEOfEq_commShift`.
* `CupCap.derivedBlackEOfEqTensorIso`, `CupCap.derivedBlackEOfEqComparisonIso_hom_app`.
* `CupCap.comparisonConj_eq_of_isComparisonConj`.
* `Stendhal.mixedCrossTensorNat`, `Stendhal.mixedCrossTensorNat_degreewise`.
* `Stendhal.dgMixedCross_commShift`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR DG DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local instance (X : Type) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

namespace CupCap

section Conj

variable {𝒟₁ 𝒟₂ D₁ D₂ : Type*} [Category* 𝒟₁] [Category* 𝒟₂] [Category* D₁] [Category* D₂]
  {Φ₁ : 𝒟₁ ⥤ D₁} {Φ₂ : 𝒟₂ ⥤ D₂} {X X' : 𝒟₁ ⥤ 𝒟₂} {Xh Xh' : D₁ ⥤ D₂}

/-- **The conjugate is characterised by the conjugacy identity.** -/
theorem comparisonConj_eq_of_isComparisonConj (hΦ : Φ₂.FullyFaithful)
    {cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh} {cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh'} {αh : Xh ⟶ Xh'} {α : X ⟶ X'}
    (h : IsComparisonConj cX cX' αh α) : comparisonConj hΦ cX cX' αh = α := by
  ext x
  apply hΦ.map_injective
  rw [isComparisonConj_comparisonConj hΦ cX cX' αh x, h x]

end Conj

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ

section OfEq

variable {μ β : Multiset I} {i : I} (h : ({i} : Multiset I) + μ = β)
  [DG.HasDerivedCategory.{0, 0} (TA μ)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA μ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]

/-- **`𝔈_i` along a content equality commutes with the shift**: the derived tensor shift
compatibility of `derivedBlackE` (`derivedBlackE_commShift`), transported along `h`. -/
instance derivedBlackEOfEq_commShift : (derivedBlackEOfEq.{0} Q Λ h).CommShift ℤ := by
  subst h
  exact derivedBlackE_commShift Q Λ i μ

variable (Q Λ) in
/-- **`𝔈_i` along a content equality is a derived tensor product**: with the corner of
`appendBlackOpOfEq`. -/
def derivedBlackEOfEqTensorIso :
    derivedBlackEOfEq.{0, 0} Q Λ h ≅
      derivedTensor.{0} (TA μ)ᵐᵒᵖ (TA β)ᵐᵒᵖ (RCorner (appendBlackOpOfEq Q Λ i h)) := by
  subst h
  exact Iso.refl _

/-- The shift compatibility of `CupCap.derivedBlackEOfEq` is that of the derived tensor
product. -/
instance derivedBlackEOfEqTensorIso_commShift :
    NatTrans.CommShift (derivedBlackEOfEqTensorIso Q Λ h).hom ℤ := by
  subst h
  exact NatTrans.CommShift.id _ ℤ

/-- **The comparison isomorphism of `CupCap.derivedBlackEOfEq`** through
`CupCap.derivedBlackEOfEqTensorIso`: the comparison of the derived tensor product with the
corner of `appendBlackOpOfEq`. -/
theorem derivedBlackEOfEqComparisonIso_hom_app (x : DG.DerivedCategory.{0} (TA β)ᵐᵒᵖ) :
    (derivedBlackEOfEqComparisonIso.{0, 0} Q Λ h).hom.app x =
      (derivedComparison.{0, 0} (TA μ)ᵐᵒᵖ).map
          ((derivedBlackEOfEqTensorIso Q Λ h).hom.app x) ≫
        (derivedTensorComparisonIso.{0, 0} (TA μ)ᵐᵒᵖ (TA β)ᵐᵒᵖ
          (RCorner (appendBlackOpOfEq Q Λ i h)) ≪≫
          Functor.isoWhiskerLeft _
            (mapDerivedCategoryIsoOfIso (resOrdIso (appendBlackOpOfEq Q Λ i h)))).hom.app x := by
  subst h
  change _ = (derivedComparison.{0, 0} (TA μ)ᵐᵒᵖ).map (𝟙 _) ≫ _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end OfEq

end CupCap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

/-- The crossing element of different colours acting on `Eₐ E_b` (`resCrossOfEq` for `a ≠ b`):
minus the cast of `mixedCrossElem`. -/
def mixedCrossCoeff : (TA νab)ᵐᵒᵖ :=
  -(castOp Q Λ ((rfl : ({a} : Multiset I) + ν = νa) ▸ mixedSwap ν a b :
      ({b} : Multiset I) + (({a} : Multiset I) + ν) = νab)
    (op (mixedCrossElem (Q := Q) Λ ν b a)))

variable {Q Λ ν a b}

/-- The crossing of different colours acts on `Eₐ E_b` by `mixedCrossCoeff`. -/
theorem resCrossOfEq_mixed_app_val (hQ : KLRSymm Q) (hab : a ≠ b)
    (X : ModuleCat.{0} (TA νab)ᵐᵒᵖ)
    (r : Res (appendBlackOp Q Λ a ν) (Res (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)) X)) :
    (((resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)).app X).hom r).val.val =
      mixedCrossCoeff Q Λ ν a b • r.val.val :=
  (CupCap.resCrossOfEq_ne_app_val Λ hQ hab rfl rfl rfl (mixedSwap ν a b) X r).trans
    (neg_smul _ _).symm

/-- `mixedCrossCoeff` intertwines the two orders of appending black strands. -/
theorem mixedCrossCoeff_intertwines (hQ : KLRSymm Q) (hab : a ≠ b) (z : (TA ν)ᵐᵒᵖ) :
    mixedCrossCoeff Q Λ ν a b *
        appendBlackOpOfEq Q Λ b (mixedSwap ν a b) (appendBlackOp Q Λ a ν z) =
      appendBlackOp Q Λ a νb (appendBlackOp Q Λ b ν z) *
        (mixedCrossCoeff Q Λ ν a b *
          appendBlackOpOfEq Q Λ b (mixedSwap ν a b) (appendBlackOp Q Λ a ν 1)) :=
  InductionAlong.RCorner.intertwines_of_res_app (mixedCrossCoeff Q Λ ν a b)
    (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) (resCrossOfEq_mixed_app_val hQ hab) z

variable (Q Λ ν a b)

/-- **The crossing of different colours on dg modules**: left multiplication by
`Stendhal.mixedCrossCoeff`, from `e' T^λ_{ν+a} ⊗ (e' T^λ_{ν+a+b} ⊗ -)` to
`e' T^λ_{ν+b} ⊗ (e' T^λ_{ν+a+b} ⊗ -)` (Webster, arXiv:1309.3796v3, §7.3). -/
def mixedCrossTensorNat (hQ : KLRSymm Q) (hab : a ≠ b) :
    DGModuleCat.tensorFunctor (B := (TA νab)ᵐᵒᵖ) (TA νa)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νa)ᵐᵒᵖ) (TA ν)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ a ν))) ⟶
    DGModuleCat.tensorFunctor (B := (TA νab)ᵐᵒᵖ) (TA νb)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ a νb))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νb)ᵐᵒᵖ) (TA ν)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ b ν))) :=
  RCorner.twoStepMixedLeftMulNat (mixedCrossCoeff Q Λ ν a b) (mixedCrossCoeff_intertwines hQ hab)

/-- **The dg crossing of different colours commutes with the shift.** -/
instance mixedCrossTensorNat_commShift (hQ : KLRSymm Q) (hab : a ≠ b) :
    NatTrans.CommShift (mixedCrossTensorNat Q Λ ν a b hQ hab) ℤ := by
  unfold mixedCrossTensorNat
  infer_instance

variable {Q Λ ν a b}

/-- **Degreewise, the dg crossing of different colours is the crossing `resCrossOfEq`**
(Webster, arXiv:1309.3796v3, §7.3): under `CupCap.tensorComplexTwoStep`,
`Stendhal.mixedCrossTensorNat` is `resCrossOfEq` applied degreewise. -/
theorem mixedCrossTensorNat_degreewise (hQ : KLRSymm Q) (hab : a ≠ b)
    (X : DGModuleCat.{0} (TA νab)ᵐᵒᵖ) :
    (complexFunctor (TA ν)ᵐᵒᵖ).map ((mixedCrossTensorNat Q Λ ν a b hQ hab).app X) ≫
        (CupCap.tensorComplexTwoStep (RCorner (appendBlackOp Q Λ b ν))
          (RCorner (appendBlackOp Q Λ a νb)) (resOrdIso (appendBlackOp Q Λ b ν))
          (resOrdIso (appendBlackOp Q Λ a νb))).hom.app X =
      (CupCap.tensorComplexTwoStep (RCorner (appendBlackOp Q Λ a ν))
          (RCorner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))
          (resOrdIso (appendBlackOp Q Λ a ν))
          (resOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))).hom.app X ≫
        (NatTrans.mapHomologicalComplex (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
          (ComplexShape.up ℤ)).app ((complexFunctor (TA νab)ᵐᵒᵖ).obj X) := by
  refine complexFunctor_tensorTwo_hom_ext _ _ X fun p m n x hx => ?_
  simp only [CupCap.tensorComplexTwoStep_hom_app, Category.assoc, HomologicalComplex.comp_f]
  have hn : (n : InDegreeZero (RCorner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))) ∈
      grading 0 :=
    (InDegreeZero.mem_grading_iff
      (M := RCorner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))).mpr (Or.inl rfl)
  have hnx : TensorProductOver.tmul (TA νab)ᵐᵒᵖ n x ∈ grading p := by
    simpa using TensorProductOver.tmul_mem_grading hn hx
  refine Eq.trans ?_ (hom_comp_apply_of_eq _ _
    (tensorComplexIsoOfIso_hom_f_tmul _ _ _ m _ hnx _)).symm
  let e := RCorner.twoStepMixedElem (mixedCrossCoeff Q Λ ν a b)
    (mixedCrossCoeff_intertwines hQ hab) m n
  have h1 : (((complexFunctor (TA ν)ᵐᵒᵖ).map
      ((mixedCrossTensorNat Q Λ ν a b hQ hab).app X)).f p).hom
      ⟨TensorProductOver.tmul (TA νa)ᵐᵒᵖ m (TensorProductOver.tmul (TA νab)ᵐᵒᵖ n x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading _ _ X m n hx)⟩ =
      ⟨TensorProductOver.tmul (TA νb)ᵐᵒᵖ
          (show InDegreeZero (RCorner (appendBlackOp Q Λ b ν)) from RCorner.gen _)
          (TensorProductOver.tmul (TA νab)ᵐᵒᵖ
            (show InDegreeZero (RCorner (appendBlackOp Q Λ a νb)) from e) x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading (RCorner (appendBlackOp Q Λ b ν))
          (RCorner (appendBlackOp Q Λ a νb)) X (RCorner.gen _) e hx)⟩ :=
    Subtype.ext rfl
  refine (hom_comp_apply_of_eq _ _ h1).trans ?_
  refine (hom_comp_apply_of_eq _ _ (tensorComplexIsoOfIso_hom_f_tmul _ _ _ _ _
    (tmul_mem_grading_of_inDegreeZero (B := (TA νb)ᵐᵒᵖ) X
      (show InDegreeZero (RCorner (appendBlackOp Q Λ a νb)) from e) hx) _)).trans ?_
  refine Res.ext (Res.ext (Subtype.ext ?_))
  have hR := resTwoStep_val (appendBlackOp Q Λ a ν) (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
    X m n x hx (mem_gradingSubmodule.mpr (tmul_mem_grading_of_inDegreeZero
      (B := (TA νa)ᵐᵒᵖ) X n hx))
  refine (resTwoStep_val _ _ X _ _ x hx _).trans ?_
  refine Eq.trans ?_ (Eq.trans (congrArg (fun y : X => mixedCrossCoeff Q Λ ν a b • y) hR.symm) ?_)
  rotate_left
  · exact (congrArg (fun y : gradingSubmodule (TA νab)ᵐᵒᵖ X p => (y : X))
      (resCrossOfEq_mixed_app_val (Λ := Λ) (ν := ν) hQ hab
        (((complexFunctor (TA νab)ᵐᵒᵖ).obj X).X p) _)).symm
  refine (congrArg (· • x) (RCorner.twoStepMixed_mul_eq (mixedCrossCoeff Q Λ ν a b)
    (mixedCrossCoeff_intertwines hQ hab) m n.1)).trans ?_
  rw [mul_assoc, mul_smul]

section Exact

variable {μ β : Multiset I} {i : I} (h : ({i} : Multiset I) + μ = β)

private theorem blackEOfEq_additive_mixedDeg : (blackEOfEq Q Λ i h).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ i h)).Additive

private theorem blackEOfEq_limits_mixedDeg :
    Limits.PreservesFiniteLimits (blackEOfEq Q Λ i h) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ i h)))

private theorem blackEOfEq_colimits_mixedDeg :
    Limits.PreservesFiniteColimits (blackEOfEq Q Λ i h) :=
  inferInstanceAs
    (Limits.PreservesFiniteColimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ i h)))

end Exact

attribute [local instance] blackEOfEq_additive_mixedDeg blackEOfEq_limits_mixedDeg
  blackEOfEq_colimits_mixedDeg

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νab)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]

/-- **The crossing of different colours on the dg derived `𝔈_a 𝔈_b`, with `𝔈_b` as a derived
tensor product**: `CupCap.dgMixedCross` is `CupCap.derivedBlackEOfEqTensorIso` followed by the
conjugate of the derived `resCrossOfEq` along the pasted comparisons of derived tensor
products. -/
theorem dgMixedCross_eq_comparisonConj (hQ : KLRSymm Q) :
    CupCap.dgMixedCross.{0, 0} (Q := Q) (Λ := Λ) ν a b hQ =
      Functor.whiskerRight (CupCap.derivedBlackEOfEqTensorIso Q Λ (mixedSwap ν a b)).hom
          (derivedBlackE.{0} Q Λ a ν) ≫
        CupCap.comparisonConj
          (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ))
          (CupCap.squarePaste (derivedTensorComparisonIso.{0, 0} (TA ν)ᵐᵒᵖ (TA νa)ᵐᵒᵖ
              (RCorner (appendBlackOp Q Λ a ν)) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νa)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso (resOrdIso (appendBlackOp Q Λ a ν))))
            (derivedTensorComparisonIso.{0, 0} (TA νa)ᵐᵒᵖ (TA νab)ᵐᵒᵖ
              (RCorner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νab)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso
                  (resOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))))))
          (CupCap.squarePaste (derivedTensorComparisonIso.{0, 0} (TA ν)ᵐᵒᵖ (TA νb)ᵐᵒᵖ
              (RCorner (appendBlackOp Q Λ b ν)) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νb)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso (resOrdIso (appendBlackOp Q Λ b ν))))
            (derivedTensorComparisonIso.{0, 0} (TA νb)ᵐᵒᵖ (TA νab)ᵐᵒᵖ
              (RCorner (appendBlackOp Q Λ a νb)) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νab)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso (resOrdIso (appendBlackOp Q Λ a νb)))))
          ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
            (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)).mapDerivedCategory ≫
            (Functor.mapDerivedCategoryCompIso
              (blackEOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))
              (blackE Q Λ b ν)).inv) := by
  refine CupCap.comparisonConj_eq_of_isComparisonConj _ (fun x => ?_)
  rw [NatTrans.comp_app, Functor.map_comp, CupCap.isComparisonConj_comparisonConj _ _ _ _ x,
    ← Category.assoc]
  congr 1
  simp only [CupCap.squarePaste_hom_app, Functor.whiskerRight_app,
    CupCap.derivedBlackEOfEqComparisonIso_hom_app, Functor.map_comp]
  exact (reassoc_of% ((derivedBlackEComparisonIso.{0, 0} Q Λ a ν).hom.naturality
    ((CupCap.derivedBlackEOfEqTensorIso Q Λ (mixedSwap ν a b)).hom.app x))) _

/-- **The crossing of different colours on the dg derived `𝔈_a 𝔈_b` commutes with the derived
tensor shift** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `a ≠ b`. -/
theorem dgMixedCross_commShift (hQ : KLRSymm Q) (hab : a ≠ b) :
    NatTrans.CommShift (CupCap.dgMixedCross.{0, 0} (Q := Q) (Λ := Λ) ν a b hQ) ℤ := by
  have hconj := CupCap.whiskerLeft_Q_comparisonConj_between_of_degreewise.{0, 0}
    (RCorner (appendBlackOp Q Λ a ν)) (RCorner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))
    (resOrdIso (appendBlackOp Q Λ a ν)) (resOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))
    (RCorner (appendBlackOp Q Λ b ν)) (RCorner (appendBlackOp Q Λ a νb))
    (resOrdIso (appendBlackOp Q Λ b ν)) (resOrdIso (appendBlackOp Q Λ a νb))
    (mixedCrossTensorNat Q Λ ν a b hQ hab) (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
    (mixedCrossTensorNat_degreewise hQ hab)
  have hc := derivedTensorTwo_commShift_between_of_QComp _ _ _ _ _ _ hconj
  have hw : NatTrans.CommShift (Functor.whiskerRight
      (CupCap.derivedBlackEOfEqTensorIso Q Λ (mixedSwap ν a b)).hom
      (derivedBlackE.{0} Q Λ a ν)) ℤ := inferInstance
  rw [dgMixedCross_eq_comparisonConj]
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ hw hc

end Categorification.Stendhal
