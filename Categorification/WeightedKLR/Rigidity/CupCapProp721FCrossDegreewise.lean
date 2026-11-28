/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CrossDegreewise
import Categorification.Algebra.CornerTwoStepCoefficient

/-!
# The crossing on the dg derived `𝔉_i²` is Rouquier's crossing on dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. Degreewise, under `CupCap.tensorComplexTwoStep` along `indOrdIso`, the dg
crossing `Stendhal.blackFCrossTensorNat` on `T^λ_{ν+2i} e' ⊗ (T^λ_{ν+i} e' ⊗ -)`, `m ⊗ n ↦
m σ(n) ⊗ e'`, is the crossing `indCrossOfEq` on `𝔉_i²` (the mate of `-ψ` on restrictions)
applied degreewise: both send `m ⊗ (n ⊗ x)` to `m σ(n) ⊗ (e' ⊗ x)`
(`Stendhal.twoStepRightMulNat_degreewise`, with `CupCap.indCrossOfEq_self_tmul`). Hence the
crossing `CupCap.dgBlackFCross` on the dg derived `𝔉_i²` is induced on dg modules by
`Stendhal.blackFCrossTensorNat` (`Stendhal.dgBlackFCross_QComp`), and it commutes with the
derived tensor shift (`Stendhal.dgBlackFCross_commShift`).

## Main results

* `Stendhal.indTwoStep_f_tmul`, `Stendhal.twoStepRightMulNat_degreewise` (generic).
* `Stendhal.blackFCrossTensorNat`, `Stendhal.dgBlackFCross_QComp`,
  `Stendhal.dgBlackFCross_commShift`.

Route hypotheses: `C`, `hRq : IsRouquierQ C Q` over a field (Webster's setting for
Theorem 4.31), under which `T^λ_{ν+i} e'` is projective over `T^λ_ν` and `𝔉_i` is exact.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR DG DG.DegreeZero

local instance (X : Type) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

universe u

section Generic

variable {A₀ A₁ A₂ : Type u} [Ring A₀] [Ring A₁] [Ring A₂] (φ₁ : A₀ →ₙ+* A₁) (φ₂ : A₁ →ₙ+* A₂)

/-- **The two-step comparison for inductions on a generator**: degreewise,
`A₂e₂ ⊗ (A₁e₁ ⊗ X) → Ind_{φ₂} Ind_{φ₁} X` sends `m ⊗ (n ⊗ x)` to `m ⊗ (n ⊗ x)`. -/
theorem indTwoStep_f_tmul (X : DGModuleCat.{u} A₀) {p : ℤ} (m : InDegreeZero (Corner φ₂))
    (n : InDegreeZero (Corner φ₁)) (x : X) (hx : x ∈ grading p) :
    (((CupCap.tensorComplexTwoStep (Corner φ₂) (Corner φ₁) (indOrdIso φ₂)
        (indOrdIso φ₁)).hom.app X).f p).hom
      ⟨TensorProductOver.tmul A₁ m (TensorProductOver.tmul A₀ n x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading _ _ X m n hx)⟩ =
      Ind.tmul (m : Corner φ₂) (Ind.tmul (n : Corner φ₁)
        (⟨x, mem_gradingSubmodule.mpr hx⟩ : gradingSubmodule A₀ X p)) := by
  rw [CupCap.tensorComplexTwoStep_hom_app]
  simp only [HomologicalComplex.comp_f]
  refine (hom_comp_apply_of_eq _ _ (tensorComplexIsoOfIso_hom_f_tmul _ _ _ m _
    (tmul_mem_grading_of_inDegreeZero (B := A₁) X n hx) _)).trans ?_
  exact congrArg (Ind.tmul (m : Corner φ₂))
    (tensorComplexIsoOfIso_hom_f_tmul _ (indOrdIso φ₁) X n x hx _)

variable {φ₁ φ₂} in
/-- **Degreewise, the two-step dg crossing is any crossing on `Ind_{φ₂} Ind_{φ₁}` with
Rouquier's value on generators**: under `CupCap.tensorComplexTwoStep`,
`InductionAlong.Corner.twoStepRightMulNat c` is `θ₀` applied degreewise, for every `θ₀` sending
`e₂ ⊗ (z ⊗ n)` to `σ(z) ⊗ (e₁ ⊗ n)`. -/
theorem twoStepRightMulNat_degreewise (c : A₂) (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)
    (θ₀ : functor.{u, u} φ₁ ⋙ functor.{u, u} φ₂ ⟶ functor.{u, u} φ₁ ⋙ functor.{u, u} φ₂)
    (hθ : ∀ (N : ModuleCat.{u} A₀) (z : Corner φ₁) (n : N),
      (θ₀.app N).hom (Ind.tmul (unitGen φ₂) (Ind.tmul z n)) =
        Ind.tmul (sigmaElt φ₁ φ₂ c z) (Ind.tmul (unitGen φ₁) n))
    (X : DGModuleCat.{u} A₀) :
    (complexFunctor A₂).map ((Corner.twoStepRightMulNat c hc).app X) ≫
        (CupCap.tensorComplexTwoStep (Corner φ₂) (Corner φ₁) (indOrdIso φ₂)
          (indOrdIso φ₁)).hom.app X =
      (CupCap.tensorComplexTwoStep (Corner φ₂) (Corner φ₁) (indOrdIso φ₂)
          (indOrdIso φ₁)).hom.app X ≫
        (NatTrans.mapHomologicalComplex θ₀ (ComplexShape.up ℤ)).app
          ((complexFunctor A₀).obj X) := by
  refine complexFunctor_tensorTwo_hom_ext _ _ X fun p m n x hx => ?_
  simp only [HomologicalComplex.comp_f]
  have h1 : (((complexFunctor A₂).map ((Corner.twoStepRightMulNat c hc).app X)).f p).hom
      ⟨TensorProductOver.tmul A₁ m (TensorProductOver.tmul A₀ n x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading _ _ X m n hx)⟩ =
      ⟨TensorProductOver.tmul A₁
          (show InDegreeZero (Corner φ₂) from Corner.twoStepRightElem c m n)
          (TensorProductOver.tmul A₀ (show InDegreeZero (Corner φ₁) from unitGen φ₁) x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading (Corner φ₂) (Corner φ₁) X
          (show InDegreeZero (Corner φ₂) from Corner.twoStepRightElem c m n)
          (show InDegreeZero (Corner φ₁) from unitGen φ₁) hx)⟩ :=
    Subtype.ext rfl
  refine (hom_comp_apply_of_eq _ _ h1).trans ?_
  refine (indTwoStep_f_tmul φ₁ φ₂ X _ _ x hx).trans ?_
  refine Eq.trans ?_ (hom_comp_apply_of_eq _ _ (indTwoStep_f_tmul φ₁ φ₂ X m n x hx)).symm
  have key := Corner.app_tmul_tmul_of_unitGen c θ₀ hθ (((complexFunctor A₀).obj X).X p)
    (m : Corner φ₂) (n : Corner φ₁) (⟨x, mem_gradingSubmodule.mpr hx⟩ : gradingSubmodule A₀ X p)
  exact key.symm

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ

/-- **The crossing on `T^λ_{ν+2i} e' ⊗ (T^λ_{ν+i} e' ⊗ -)` on dg modules**: Rouquier's crossing
`m ⊗ n ↦ m σ(n) ⊗ e'`, with `σ` built from the crossing of the two newest black strands
(Webster, arXiv:1309.3796v3, §7.3). -/
def blackFCrossTensorNat :
    DGModuleCat.tensorFunctor (B := (TA ν)ᵐᵒᵖ) (TA νᵢ)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ i ν))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νᵢ)ᵐᵒᵖ) (TA νᵢᵢ)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ i νᵢ))) ⟶
    DGModuleCat.tensorFunctor (B := (TA ν)ᵐᵒᵖ) (TA νᵢ)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ i ν))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νᵢ)ᵐᵒᵖ) (TA νᵢᵢ)ᵐᵒᵖ
        (InDegreeZero (Corner (appendBlackOp Q Λ i νᵢ))) :=
  Corner.twoStepRightMulNat (op (appendedCross Q Λ i ν)) (op_appendedCross_commute Q Λ i ν)

/-- **The dg crossing on `𝔉_i²` commutes with the shift** (Webster, arXiv:1309.3796v3, §7.3). -/
instance blackFCrossTensorNat_commShift :
    NatTrans.CommShift (blackFCrossTensorNat Q Λ ν i) ℤ := by
  unfold blackFCrossTensorNat
  infer_instance

universe w w'

variable [DG.HasDerivedCategory.{w} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w} (TA νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The crossing on the dg derived `𝔉_i²` is induced on dg modules by Rouquier's crossing**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for Rouquier polynomials over a
field (Webster's setting for Theorem 4.31). -/
theorem dgBlackFCross_QComp (hQ : KLRSymm Q) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
    letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
    haveI := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hRq
    haveI := projective_blackCorner (Q := Q) (Λ := Λ) i νᵢ C hRq
    Functor.whiskerLeft DG.DerivedCategory.Q
        (CupCap.dgBlackFCross.{w, w'} (Q := Q) (Λ := Λ) ν i C hRq hQ) ≫
        (QCompDerivedTensorTwoIso.{w} (A := (TA νᵢᵢ)ᵐᵒᵖ) (B := (TA νᵢ)ᵐᵒᵖ)
          (C := (TA ν)ᵐᵒᵖ) (Corner (appendBlackOp Q Λ i νᵢ))
          (Corner (appendBlackOp Q Λ i ν))).hom =
      (QCompDerivedTensorTwoIso.{w} (A := (TA νᵢᵢ)ᵐᵒᵖ) (B := (TA νᵢ)ᵐᵒᵖ)
          (C := (TA ν)ᵐᵒᵖ) (Corner (appendBlackOp Q Λ i νᵢ))
          (Corner (appendBlackOp Q Λ i ν))).hom ≫
        Functor.whiskerRight (blackFCrossTensorNat Q Λ ν i) DG.DerivedCategory.Q := by
  have := blackF_preservesFiniteLimits Q Λ i ν C hRq
  have := blackF_preservesFiniteColimits Q Λ i ν C hRq
  have := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  have := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) i νᵢ C hRq
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ i ν)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ i ν)
  have := functor_preservesFiniteLimits (appendBlackOp Q Λ i νᵢ)
  have := functor_preservesFiniteColimits (appendBlackOp Q Λ i νᵢ)
  exact CupCap.whiskerLeft_Q_comparisonConj_of_degreewise.{w, w'} _ _
    (indOrdIso (appendBlackOp Q Λ i νᵢ)) (indOrdIso (appendBlackOp Q Λ i ν))
    (blackFCrossTensorNat Q Λ ν i) (indCrossOfEq Λ hQ i i rfl rfl rfl rfl)
    (twoStepRightMulNat_degreewise _ (op_appendedCross_commute Q Λ i ν) _
      (fun N z x => CupCap.indCrossOfEq_self_tmul Λ hQ i rfl rfl N z x))

/-- **The crossing on the dg derived `𝔉_i²` commutes with the derived tensor shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the hypothesis `hcross` of
`CupCap.capEQuantumTraceShiftIso_cross`, for Rouquier polynomials over a field. -/
theorem dgBlackFCross_commShift (hQ : KLRSymm Q) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
    letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
    NatTrans.CommShift (CupCap.dgBlackFCross.{w, w'} (Q := Q) (Λ := Λ) ν i C hRq hQ) ℤ := by
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hRq
  have := projective_blackCorner (Q := Q) (Λ := Λ) i νᵢ C hRq
  exact derivedTensorTwo_commShift_of_QComp _ _ _ (blackFCrossTensorNat Q Λ ν i)
    (dgBlackFCross_QComp Q Λ ν i C hRq hQ)

end Categorification.Stendhal
