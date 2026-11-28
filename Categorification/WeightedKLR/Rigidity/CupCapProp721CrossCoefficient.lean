/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftCross
import Categorification.Algebra.RCornerTwoStepCoefficient

/-!
# The crossing on the derived `𝔈_i²`: reduction of its shift compatibility to dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The crossing `CupCap.dgBlackCross` on the dg derived functor
`𝔈_i² = (- ⊗ᴸ e' T^λ_{ν+2i}) ⊗ᴸ e' T^λ_{ν+i}` is defined as the conjugate of the derived crossing
`derivedBlackCross` along the comparison with Mathlib's derived categories. On dg modules the
crossing is left multiplication by the crossing `ψ` of the two newest black strands on
`e' T^λ_{ν+i} ⊗ e' T^λ_{ν+2i}` (`Stendhal.blackCrossTensorNat`), which commutes with the shift.
Hence `CupCap.dgBlackCross` commutes with the derived tensor shift (the hypothesis `hcross` of
`CupCap.capFQuantumTraceShiftIso_cross`) as soon as it is induced by `Stendhal.blackCrossTensorNat`
through `QCompDerivedTensorTwoIso` (`Stendhal.dgBlackCross_commShift_of_QComp`).

## Main results

* `Stendhal.blackCrossTensorNat`, with its `NatTrans.CommShift` instance.
* `Stendhal.dgBlackCross_commShift_of_QComp`.

Route hypothesis (tracked): the identification `hQComp` of `CupCap.dgBlackCross` on dg modules.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR DG DG.DegreeZero

local instance (X : Type) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ

/-- **The crossing on `e' T^λ_{ν+i} ⊗ (e' T^λ_{ν+2i} ⊗ -)` on dg modules**: left multiplication
by the crossing of the two newest black strands (Webster, arXiv:1309.3796v3, §7.3). -/
def blackCrossTensorNat :
    DGModuleCat.tensorFunctor (B := (TA νᵢᵢ)ᵐᵒᵖ) (TA νᵢ)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ i νᵢ))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νᵢ)ᵐᵒᵖ) (TA ν)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ i ν))) ⟶
    DGModuleCat.tensorFunctor (B := (TA νᵢᵢ)ᵐᵒᵖ) (TA νᵢ)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ i νᵢ))) ⋙
      DGModuleCat.tensorFunctor (B := (TA νᵢ)ᵐᵒᵖ) (TA ν)ᵐᵒᵖ
        (InDegreeZero (RCorner (appendBlackOp Q Λ i ν))) :=
  RCorner.twoStepLeftMulNat (op (appendedCross Q Λ i ν)) (op_appendedCross_fix Q Λ i ν)
    (op_appendedCross_commute Q Λ i ν)

/-- **The dg crossing commutes with the shift** (Webster, arXiv:1309.3796v3, §7.3). -/
instance blackCrossTensorNat_commShift :
    NatTrans.CommShift (blackCrossTensorNat Q Λ ν i) ℤ := by
  unfold blackCrossTensorNat
  infer_instance

universe w w'

variable [DG.HasDerivedCategory.{w} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w} (TA νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]

/-- **The crossing on the dg derived `𝔈_i²` commutes with the derived tensor shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), provided it is induced on dg modules by the
dg crossing `Stendhal.blackCrossTensorNat` (route hypothesis `hQComp`, tracked). -/
theorem dgBlackCross_commShift_of_QComp
    (hQComp : Functor.whiskerLeft DG.DerivedCategory.Q
        (CupCap.dgBlackCross.{w, w'} (Q := Q) (Λ := Λ) ν i) ≫
        (QCompDerivedTensorTwoIso.{w} (A := (TA ν)ᵐᵒᵖ) (B := (TA νᵢ)ᵐᵒᵖ)
          (C := (TA νᵢᵢ)ᵐᵒᵖ) (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ))).hom =
      (QCompDerivedTensorTwoIso.{w} (A := (TA ν)ᵐᵒᵖ) (B := (TA νᵢ)ᵐᵒᵖ)
          (C := (TA νᵢᵢ)ᵐᵒᵖ) (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ))).hom ≫
        Functor.whiskerRight (blackCrossTensorNat Q Λ ν i) DG.DerivedCategory.Q) :
    NatTrans.CommShift (CupCap.dgBlackCross.{w, w'} (Q := Q) (Λ := Λ) ν i) ℤ :=
  derivedTensorTwo_commShift_of_QComp _ _ _ _ hQComp

end Categorification.Stendhal
