/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721FCrossDegreewise
import Categorification.WeightedKLR.Rigidity.CupCapProp721MixedCrossDegreewise
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDGCases
import Categorification.Algebra.CornerTwoStepMixedCoefficient

/-!
# The crossing of different colours on the dg derived `𝔉_a 𝔉_b` commutes with the shift

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The crossing of two black strands of different colours `a ≠ b` on the dg
derived `𝔉_a 𝔉_b` (`CupCap.dgBlackFMixedCross`) is the conjugate of the derived crossing
`indCrossOfEq` along the comparisons with Mathlib's derived categories. For `a ≠ b`,
`indCrossOfEq` sends `e ⊗ (e ⊗ x)` to `c (e ⊗ (e ⊗ x))`, with `c` the crossing element
`Stendhal.mixedCrossCoeff` of the `𝔈` side (`CupCap.indCrossOfEq_ne_unitGen`). On dg modules,
right multiplication by `c` from `T^λ_{ν+a+b} e' ⊗ (T^λ_{ν+b} e' ⊗ -)` to
`T^λ_{ν+a+b} e' ⊗ (T^λ_{ν+a} e' ⊗ -)` (`Stendhal.blackFMixedCrossTensorNat`) is degreewise
`indCrossOfEq` (`Stendhal.blackFMixedCrossTensorNat_degreewise`): both send `m ⊗ (n ⊗ x)` to
`m φ(n) c e' ⊗ (e' ⊗ x)`. Hence `CupCap.dgBlackFMixedCross` commutes with the derived tensor
shift (`Stendhal.dgBlackFMixedCross_commShift`). The second functor `𝔉_b` is taken along the
content equality `mixedSwap`; it is the derived tensor product with the corner of
`appendBlackOpOfEq` (`CupCap.derivedBlackFOfEqTensorIso`).

## Main results

* `Stendhal.twoStepMixedRightMulNat_degreewise` (generic).
* `CupCap.derivedBlackFOfEq_commShift`, `CupCap.derivedBlackFOfEqTensorIso`,
  `CupCap.derivedBlackFOfEqComparisonIso_hom_app`.
* `Stendhal.blackFMixedCrossTensorNat`, `Stendhal.blackFMixedCrossTensorNat_degreewise`.
* `Stendhal.dgBlackFMixedCross_eq_comparisonConj`, `Stendhal.dgBlackFMixedCross_commShift`.

Route hypotheses: `C`, `hRq : IsRouquierQ C Q` over a field (Webster's setting for
Theorem 4.31), under which the corners `T^λ_{ν+i} e'` are projective and `𝔉_i` is exact.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR DG DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local instance (X : Type) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

universe u

section Generic

variable {A₀ A₁ A₁' A₂ : Type u} [Ring A₀] [Ring A₁] [Ring A₁'] [Ring A₂] {φ₁ : A₀ →ₙ+* A₁}
  {φ₂ : A₁ →ₙ+* A₂} {φ₁' : A₀ →ₙ+* A₁'} {φ₂' : A₁' →ₙ+* A₂}

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

/-- **Degreewise, the two-step dg multiplication between two corners is any transformation of
inductions acting by `c` on generators**: under `CupCap.tensorComplexTwoStep`,
`InductionAlong.Corner.twoStepMixedRightMulNat c` is `θ₀` applied degreewise, for every
`θ₀ : Ind_{φ₂} Ind_{φ₁} ⟶ Ind_{φ₂'} Ind_{φ₁'}` sending `e₂ ⊗ (e₁ ⊗ n)` to
`c (e₂' ⊗ (e₁' ⊗ n))`. -/
theorem twoStepMixedRightMulNat_degreewise (c : A₂)
    (hc : ∀ a, c * φ₂' (φ₁' a) = φ₂ (φ₁ a) * (c * φ₂' (φ₁' 1)))
    (θ₀ : functor.{u, u} φ₁ ⋙ functor.{u, u} φ₂ ⟶ functor.{u, u} φ₁' ⋙ functor.{u, u} φ₂')
    (hθ : ∀ (N : ModuleCat.{u} A₀) (n : N),
      (θ₀.app N).hom (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n)) =
        c • Ind.tmul (unitGen φ₂') (Ind.tmul (unitGen φ₁') n))
    (X : DGModuleCat.{u} A₀) :
    (complexFunctor A₂).map ((Corner.twoStepMixedRightMulNat c hc).app X) ≫
        (CupCap.tensorComplexTwoStep (Corner φ₂') (Corner φ₁') (indOrdIso φ₂')
          (indOrdIso φ₁')).hom.app X =
      (CupCap.tensorComplexTwoStep (Corner φ₂) (Corner φ₁) (indOrdIso φ₂)
          (indOrdIso φ₁)).hom.app X ≫
        (NatTrans.mapHomologicalComplex θ₀ (ComplexShape.up ℤ)).app
          ((complexFunctor A₀).obj X) := by
  refine complexFunctor_tensorTwo_hom_ext _ _ X fun p m n x hx => ?_
  simp only [HomologicalComplex.comp_f]
  have h1 : (((complexFunctor A₂).map ((Corner.twoStepMixedRightMulNat c hc).app X)).f p).hom
      ⟨TensorProductOver.tmul A₁ m (TensorProductOver.tmul A₀ n x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading _ _ X m n hx)⟩ =
      ⟨TensorProductOver.tmul A₁'
          (show InDegreeZero (Corner φ₂') from Corner.twoStepMixedRightElem φ₁' φ₂' c m n)
          (TensorProductOver.tmul A₀ (show InDegreeZero (Corner φ₁') from unitGen φ₁') x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading (Corner φ₂') (Corner φ₁') X
          (show InDegreeZero (Corner φ₂') from Corner.twoStepMixedRightElem φ₁' φ₂' c m n)
          (show InDegreeZero (Corner φ₁') from unitGen φ₁') hx)⟩ :=
    Subtype.ext rfl
  refine (hom_comp_apply_of_eq _ _ h1).trans ?_
  refine (indTwoStep_f_tmul φ₁' φ₂' X _ _ x hx).trans ?_
  refine Eq.trans ?_ (hom_comp_apply_of_eq _ _ (indTwoStep_f_tmul φ₁ φ₂ X m n x hx)).symm
  have key := Corner.app_tmul_tmul_of_unitGen_mixed c θ₀ hθ (((complexFunctor A₀).obj X).X p)
    (m : Corner φ₂) (n : Corner φ₁) (⟨x, mem_gradingSubmodule.mpr hx⟩ : gradingSubmodule A₀ X p)
  exact key.symm

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ

namespace CupCap

section OfEq

variable {μ β : Multiset I} {i : I} (h : ({i} : Multiset I) + μ = β)

/-- The corner of `𝔉_i` along a content equality is projective (Webster, Theorem 4.31). -/
theorem projective_blackCornerOfEq (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) :
    Module.Projective (TA μ)ᵐᵒᵖᵐᵒᵖ (Corner (appendBlackOpOfEq Q Λ i h)) := by
  subst h
  exact projective_blackCorner (Q := Q) (Λ := Λ) i μ C hRq

variable [DG.HasDerivedCategory.{0, 0} (TA μ)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]

/-- **`𝔉_i` along a content equality commutes with the shift**: the derived tensor shift
compatibility of `derivedBlackF` (`derivedBlackF_commShift`), transported along `h`. -/
instance derivedBlackFOfEq_commShift : (derivedBlackFOfEq.{0} Q Λ h).CommShift ℤ := by
  subst h
  exact derivedBlackF_commShift Q Λ i μ

variable (Q Λ) in
/-- **`𝔉_i` along a content equality is a derived tensor product**: with the corner of
`appendBlackOpOfEq`. -/
def derivedBlackFOfEqTensorIso :
    derivedBlackFOfEq.{0} Q Λ h ≅
      derivedTensor.{0} (TA β)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (Corner (appendBlackOpOfEq Q Λ i h)) := by
  subst h
  exact Iso.refl _

/-- The shift compatibility of `CupCap.derivedBlackFOfEq` is that of the derived tensor
product. -/
instance derivedBlackFOfEqTensorIso_commShift :
    NatTrans.CommShift (derivedBlackFOfEqTensorIso Q Λ h).hom ℤ := by
  subst h
  exact NatTrans.CommShift.id _ ℤ

/-- The shift compatibility of `CupCap.derivedBlackFOfEq` is that of the derived tensor
product, for the inverse. -/
instance derivedBlackFOfEqTensorIso_inv_commShift :
    NatTrans.CommShift (derivedBlackFOfEqTensorIso Q Λ h).inv ℤ := by
  subst h
  exact NatTrans.CommShift.id _ ℤ

variable [HasDerivedCategory.{0} (ModuleCat.{0} (TA μ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]
  [Limits.PreservesFiniteLimits (blackFOfEq Q Λ i h)]
  [Limits.PreservesFiniteColimits (blackFOfEq Q Λ i h)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The comparison isomorphism of `CupCap.derivedBlackFOfEq`** through
`CupCap.derivedBlackFOfEqTensorIso`: the comparison of the derived tensor product with the
corner of `appendBlackOpOfEq`. -/
theorem derivedBlackFOfEqComparisonIso_hom_app (x : DG.DerivedCategory.{0} (TA μ)ᵐᵒᵖ) :
    haveI := projective_blackCornerOfEq (Λ := Λ) h C hRq
    letI := functor_preservesFiniteLimits (appendBlackOpOfEq Q Λ i h)
    letI := functor_preservesFiniteColimits (appendBlackOpOfEq Q Λ i h)
    (derivedBlackFOfEqComparisonIso.{0, 0} Q Λ h C hRq).hom.app x =
      (derivedComparison.{0, 0} (TA β)ᵐᵒᵖ).map
          ((derivedBlackFOfEqTensorIso Q Λ h).hom.app x) ≫
        (derivedTensorComparisonIso.{0, 0} (TA β)ᵐᵒᵖ (TA μ)ᵐᵒᵖ
          (Corner (appendBlackOpOfEq Q Λ i h)) ≪≫
          Functor.isoWhiskerLeft _
            (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOpOfEq Q Λ i h)))).hom.app x := by
  subst h
  change _ = (derivedComparison.{0, 0} (TA (({i} : Multiset I) + μ))ᵐᵒᵖ).map (𝟙 _) ≫ _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end OfEq

end CupCap

variable (Q Λ) (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

/-- **The crossing of different colours on dg modules, on the `𝔉` side**: right
multiplication by `Stendhal.mixedCrossCoeff`, from `T^λ_{ν+a+b} e' ⊗ (T^λ_{ν+b} e' ⊗ -)` to
`T^λ_{ν+a+b} e' ⊗ (T^λ_{ν+a} e' ⊗ -)` (Webster, arXiv:1309.3796v3, §7.3). -/
def blackFMixedCrossTensorNat (hQ : KLRSymm Q) (hab : a ≠ b) :
    DGModuleCat.tensorFunctor (B := (TA ν)ᵐᵒᵖ) (TA νb)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ b ν))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νb)ᵐᵒᵖ) (TA νab)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ a νb))) ⟶
    DGModuleCat.tensorFunctor (B := (TA ν)ᵐᵒᵖ) (TA νa)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ a ν))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νa)ᵐᵒᵖ) (TA νab)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))) :=
  Corner.twoStepMixedRightMulNat (mixedCrossCoeff Q Λ ν a b) (mixedCrossCoeff_intertwines hQ hab)

/-- **The dg crossing of different colours on `𝔉_a 𝔉_b` commutes with the shift.** -/
instance blackFMixedCrossTensorNat_commShift (hQ : KLRSymm Q) (hab : a ≠ b) :
    NatTrans.CommShift (blackFMixedCrossTensorNat Q Λ ν a b hQ hab) ℤ := by
  unfold blackFMixedCrossTensorNat
  infer_instance

variable {Q Λ ν a b}

/-- **Degreewise, the dg crossing of different colours on `𝔉_a 𝔉_b` is the crossing
`indCrossOfEq`** (Webster, arXiv:1309.3796v3, §7.3): under `CupCap.tensorComplexTwoStep`,
`Stendhal.blackFMixedCrossTensorNat` is `indCrossOfEq` applied degreewise. -/
theorem blackFMixedCrossTensorNat_degreewise (hQ : KLRSymm Q) (hab : a ≠ b)
    (X : DGModuleCat.{0} (TA ν)ᵐᵒᵖ) :
    (complexFunctor (TA νab)ᵐᵒᵖ).map ((blackFMixedCrossTensorNat Q Λ ν a b hQ hab).app X) ≫
        (CupCap.tensorComplexTwoStep (Corner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))
          (Corner (appendBlackOp Q Λ a ν))
          (indOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))
          (indOrdIso (appendBlackOp Q Λ a ν))).hom.app X =
      (CupCap.tensorComplexTwoStep (Corner (appendBlackOp Q Λ a νb))
          (Corner (appendBlackOp Q Λ b ν)) (indOrdIso (appendBlackOp Q Λ a νb))
          (indOrdIso (appendBlackOp Q Λ b ν))).hom.app X ≫
        (NatTrans.mapHomologicalComplex (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
          (ComplexShape.up ℤ)).app ((complexFunctor (TA ν)ᵐᵒᵖ).obj X) :=
  twoStepMixedRightMulNat_degreewise _ (mixedCrossCoeff_intertwines hQ hab) _
    (fun N x => CupCap.indCrossOfEq_ne_unitGen Λ hQ hab rfl rfl rfl (mixedSwap ν a b) N x) X

/-- If `e = g ≫ P` at `x` for natural isomorphisms `e`, `P` into the same functor and an
isomorphism `g`, then `P⁻¹ ≫ g⁻¹ = e⁻¹` at `x`. -/
private theorem inv_app_comp_inv_eq_of_hom_app {C D : Type*} [Category C] [Category D]
    {F F' G : C ⥤ D} (e : F ≅ G) (P : F' ≅ G) (x : C) (g : F.obj x ≅ F'.obj x)
    (h : e.hom.app x = g.hom ≫ P.hom.app x) : P.inv.app x ≫ g.inv = e.inv.app x :=
  calc P.inv.app x ≫ g.inv = (P.inv.app x ≫ g.inv) ≫ (e.hom.app x ≫ e.inv.app x) := by simp
    _ = e.inv.app x := by rw [h]; simp

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νab)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The crossing of different colours on the dg derived `𝔉_a 𝔉_b`, with `𝔉_b` as a derived
tensor product**: `CupCap.dgBlackFMixedCross` is the conjugate of the derived `indCrossOfEq`
along the pasted comparisons of derived tensor products, followed by
`CupCap.derivedBlackFOfEqTensorIso`. -/
theorem dgBlackFMixedCross_eq_comparisonConj (hQ : KLRSymm Q) :
    letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
    letI := CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a
      (rfl : ({a} : Multiset I) + νb = νab) C hRq
    letI := CupCap.blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a
      (rfl : ({a} : Multiset I) + νb = νab) C hRq
    letI := CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := CupCap.blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C
      hRq
    haveI := projective_blackCorner (Q := Q) (Λ := Λ) a ν C hRq
    haveI := projective_blackCorner (Q := Q) (Λ := Λ) b ν C hRq
    haveI := projective_blackCorner (Q := Q) (Λ := Λ) a νb C hRq
    haveI := CupCap.projective_blackCornerOfEq (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := functor_preservesFiniteLimits (appendBlackOp Q Λ a ν)
    letI := functor_preservesFiniteColimits (appendBlackOp Q Λ a ν)
    letI := functor_preservesFiniteLimits (appendBlackOp Q Λ b ν)
    letI := functor_preservesFiniteColimits (appendBlackOp Q Λ b ν)
    letI := functor_preservesFiniteLimits (appendBlackOp Q Λ a νb)
    letI := functor_preservesFiniteColimits (appendBlackOp Q Λ a νb)
    letI := functor_preservesFiniteLimits (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
    letI := functor_preservesFiniteColimits (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
    CupCap.dgBlackFMixedCross.{0, 0} ν a b C hRq hQ =
      CupCap.comparisonConj
          (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{0, 0} (TA νab)ᵐᵒᵖ))
          (CupCap.squarePaste (derivedTensorComparisonIso.{0, 0} (TA νab)ᵐᵒᵖ (TA νb)ᵐᵒᵖ
              (Corner (appendBlackOp Q Λ a νb)) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νb)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOp Q Λ a νb))))
            (derivedTensorComparisonIso.{0, 0} (TA νb)ᵐᵒᵖ (TA ν)ᵐᵒᵖ
              (Corner (appendBlackOp Q Λ b ν)) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOp Q Λ b ν)))))
          (CupCap.squarePaste (derivedTensorComparisonIso.{0, 0} (TA νab)ᵐᵒᵖ (TA νa)ᵐᵒᵖ
              (Corner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νa)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso
                  (indOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))))
            (derivedTensorComparisonIso.{0, 0} (TA νa)ᵐᵒᵖ (TA ν)ᵐᵒᵖ
              (Corner (appendBlackOp Q Λ a ν)) ≪≫
              Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ)
                (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOp Q Λ a ν)))))
          ((Functor.mapDerivedCategoryCompIso (blackF Q Λ b ν)
              (blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))).hom ≫
            NatTrans.mapDerivedCategory
              (F := blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))
              (G := blackF Q Λ a ν ⋙ blackFOfEq Q Λ b (mixedSwap ν a b))
              (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) ≫
            (Functor.mapDerivedCategoryCompIso (blackF Q Λ a ν)
              (blackFOfEq Q Λ b (mixedSwap ν a b))).inv) ≫
        Functor.whiskerLeft (derivedBlackF.{0} Q Λ a ν)
          (CupCap.derivedBlackFOfEqTensorIso Q Λ (mixedSwap ν a b)).inv := by
  have := blackF_preservesFiniteLimits Q Λ a ν C hRq
  have := blackF_preservesFiniteColimits Q Λ a ν C hRq
  have := CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have := CupCap.blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) a ν C hRq
  have := CupCap.projective_blackCornerOfEq (Λ := Λ) (mixedSwap ν a b) C hRq
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ a ν)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ a ν)
  have := functor_preservesFiniteLimits (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
  have := functor_preservesFiniteColimits (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
  refine CupCap.comparisonConj_eq_of_isComparisonConj _ (fun x => ?_)
  rw [NatTrans.comp_app, Functor.map_comp, CupCap.isComparisonConj_comparisonConj _ _ _ _ x]
  simp only [Category.assoc]
  congr 2
  refine inv_app_comp_inv_eq_of_hom_app
    (CupCap.squarePaste (CupCap.derivedBlackFOfEqComparisonIso.{0, 0} Q Λ (mixedSwap ν a b) C hRq)
      (derivedBlackFComparisonIso.{0, 0} Q Λ a ν C hRq))
    (CupCap.squarePaste (derivedTensorComparisonIso.{0, 0} (TA νab)ᵐᵒᵖ (TA νa)ᵐᵒᵖ
        (Corner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))) ≪≫
        Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA νa)ᵐᵒᵖ)
          (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b)))))
      (derivedTensorComparisonIso.{0, 0} (TA νa)ᵐᵒᵖ (TA ν)ᵐᵒᵖ
        (Corner (appendBlackOp Q Λ a ν)) ≪≫
        Functor.isoWhiskerLeft (derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ)
          (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOp Q Λ a ν))))) x
    ((derivedComparison.{0, 0} (TA νab)ᵐᵒᵖ).mapIso
      ((CupCap.derivedBlackFOfEqTensorIso Q Λ (mixedSwap ν a b)).app
        ((derivedBlackF.{0} Q Λ a ν).obj x))) ?_
  refine (CupCap.squarePaste_hom_app _ _ x).trans ?_
  refine Eq.trans (congrArg (· ≫ _) (CupCap.derivedBlackFOfEqComparisonIso_hom_app (Λ := Λ)
    (mixedSwap ν a b) C hRq ((derivedBlackF.{0} Q Λ a ν).obj x))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (_ ≫ ·) (CupCap.squarePaste_hom_app _ _ x).symm

/-- **The crossing of different colours on the dg derived `𝔉_a 𝔉_b` commutes with the derived
tensor shift** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `a ≠ b` and
Rouquier polynomials over a field (Webster's setting for Theorem 4.31). -/
theorem dgBlackFMixedCross_commShift (hQ : KLRSymm Q) (hab : a ≠ b) :
    letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
    letI := CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a
      (rfl : ({a} : Multiset I) + νb = νab) C hRq
    letI := CupCap.blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a
      (rfl : ({a} : Multiset I) + νb = νab) C hRq
    letI := CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := CupCap.blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C
      hRq
    NatTrans.CommShift (CupCap.dgBlackFMixedCross.{0, 0} (Λ := Λ) ν a b C hRq hQ) ℤ := by
  have := blackF_preservesFiniteLimits Q Λ a ν C hRq
  have := blackF_preservesFiniteColimits Q Λ a ν C hRq
  have := blackF_preservesFiniteLimits Q Λ b ν C hRq
  have := blackF_preservesFiniteColimits Q Λ b ν C hRq
  have := CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have := CupCap.blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) a ν C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) b ν C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) a νb C hRq
  have := CupCap.projective_blackCornerOfEq (Λ := Λ) (mixedSwap ν a b) C hRq
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ a ν)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ a ν)
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ b ν)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ b ν)
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ a νb)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ a νb)
  have := functor_preservesFiniteLimits (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
  have := functor_preservesFiniteColimits (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))
  have hconj := CupCap.whiskerLeft_Q_comparisonConj_between_of_degreewise.{0, 0}
    (Corner (appendBlackOp Q Λ a νb)) (Corner (appendBlackOp Q Λ b ν))
    (indOrdIso (appendBlackOp Q Λ a νb)) (indOrdIso (appendBlackOp Q Λ b ν))
    (Corner (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))) (Corner (appendBlackOp Q Λ a ν))
    (indOrdIso (appendBlackOpOfEq Q Λ b (mixedSwap ν a b))) (indOrdIso (appendBlackOp Q Λ a ν))
    (blackFMixedCrossTensorNat Q Λ ν a b hQ hab)
    (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
    (blackFMixedCrossTensorNat_degreewise hQ hab)
  have hc := derivedTensorTwo_commShift_between_of_QComp _ _ _ _ _ _ hconj
  have hw : NatTrans.CommShift (Functor.whiskerLeft (derivedBlackF.{0} Q Λ a ν)
      (CupCap.derivedBlackFOfEqTensorIso Q Λ (mixedSwap ν a b)).inv) ℤ := inferInstance
  rw [dgBlackFMixedCross_eq_comparisonConj (Q := Q) (Λ := Λ) (ν := ν) (a := a) (b := b) C hRq hQ]
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ hc hw

end Categorification.Stendhal
