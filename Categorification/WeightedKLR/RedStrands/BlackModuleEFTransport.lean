/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportEquiv
import Categorification.WeightedKLR.RedStrands.DoubleBlackInduction
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecomp
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction

/-!
# The commutation relation of `Eᵢ` and `Fᵢ` on modules over `T^λ`

The commutation relation of the categorical action (Webster, arXiv:1309.3796v3, Thm 4.31) on
all right modules over the tensor product algebra `T^λ` at standard Khovanov–Lauda black
scalars, an input of the dimension count in the proof of Proposition 5.5 there. With
`n = ⟨i, λ⟩` for `λ` the right weight of content `i + ν`,

* `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` when `n ≥ 0` (`clBlackModuleEFEquiv`),
* `Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` when `n ≤ 0` (`clBlackModuleFEEquiv`),

as right `T^λ_{i+ν}`-modules, where `Fᵢ` is induction along the map adding a black strand
(`appendBlackOp`) and `Eᵢ` is restriction along it. Both come from the statements on the
all-down matrix ring (`blackModuleEFEquiv`, `blackModuleFEEquiv`), transported through the
repaired Lemma 4.29 (`clOpEquiv`) by `InductionAlong.resIndEquivTransport`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => TensorProductAlgebra k (CL.qCL KL) Λ

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "PD" => clDownwardBlock Λ C P

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({i} + ν))ᵐᵒᵖ M]

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapKLPresentation (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) P (clDownwardQ KL) Λ fun _ _ => 1)

/-- A right `T^λ_{i+ν}`-module `M`, viewed as a module over the all-down matrix ring through
the repaired Lemma 4.29 (`clOpEquiv`). -/
@[nolint unusedArguments]
def ClMatView (_ : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
    (_ : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
      (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
        I ⊕ Fin ℓ → ℤ) P)
    (_ : P.WFDom) (_ : I) (_ : Multiset I) (M : Type u) : Type u := M

instance : AddCommGroup (ClMatView hstd hP hwf i ν M) := inferInstanceAs (AddCommGroup M)

instance : Module (downwardMatrix (PD) ({i} + ν))ᵐᵒᵖ (ClMatView hstd hP hwf i ν M) :=
  Module.compHom M (clOpEquiv hstd hP hwf ({i} + ν)).symm.toRingHom

/-- The identity of `M`, from `T^λ` to its matrix-ring view. -/
def toClMatView : M ≃+ ClMatView hstd hP hwf i ν M := AddEquiv.refl M

theorem toClMatView_smul (t : (TensorProductAlgebra k (CL.qCL KL) Λ ({i} + ν))ᵐᵒᵖ) (m : M) :
    toClMatView hstd hP hwf i ν M (t • m) =
      clOpEquiv hstd hP hwf ({i} + ν) t • toClMatView hstd hP hwf i ν M m := by
  change t • m = (clOpEquiv hstd hP hwf ({i} + ν)).symm (clOpEquiv hstd hP hwf ({i} + ν) t) • m
  rw [RingEquiv.symm_apply_apply]

local notation "MV" => ClMatView hstd hP hwf i ν M

/-- **`Eᵢ Fᵢ` against `Fᵢ Eᵢ` on `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the proof
of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with `λ` the right weight of content `i + ν`,
`Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for every right `T^λ_{i+ν}`-module `M`. Transported from the
all-down matrix ring (`blackModuleEFEquiv`) through the repaired Lemma 4.29. -/
def clBlackModuleEFEquiv (hn : 0 ≤ ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))) :=
  resIndEquivTransport (clOpEquiv hstd hP hwf ν) (clOpEquiv hstd hP hwf ({i} + ν))
    (clOpEquiv hstd hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlack hstd hP hwf i ν)
    (clOpEquiv_appendBlack hstd hP hwf i ({i} + ν)) (toClMatView hstd hP hwf i ν M)
    (toClMatView_smul hstd hP hwf i ν M) _
    (blackModuleEFEquiv (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P) (MV) hn)

/-- **`Fᵢ Eᵢ` against `Eᵢ Fᵢ` on `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the proof
of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`, with `λ` the right weight of content `i + ν`,
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` for every right `T^λ_{i+ν}`-module `M`. Transported from the
all-down matrix ring (`blackModuleFEEquiv`) through the repaired Lemma 4.29. -/
def clBlackModuleFEEquiv (hn : ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)) ≤ 0) :=
  indResEquivTransport (clOpEquiv hstd hP hwf ν) (clOpEquiv hstd hP hwf ({i} + ν))
    (clOpEquiv hstd hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlack hstd hP hwf i ν)
    (clOpEquiv_appendBlack hstd hP hwf i ({i} + ν)) (toClMatView hstd hP hwf i ν M)
    (toClMatView_smul hstd hP hwf i ν M) _
    (blackModuleFEEquiv (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P) (MV) hn)

end CL

end Categorification.Stendhal
