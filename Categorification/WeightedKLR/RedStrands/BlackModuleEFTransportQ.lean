/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportEquiv
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackInductionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecompQ
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction

/-!
# The commutation relation of `Eᵢ` and `Fᵢ` on modules over `T^λ`

The commutation relation of the categorical action (Webster, arXiv:1309.3796v3, Thm 4.31) on
all right modules over the tensor product algebra `T^λ` at black scalars of a Kang–Kashiwara family, an input of the dimension count in the proof of Proposition 5.5 there. With
`n = ⟨i, λ⟩` for `λ` the right weight of content `i + ν`,

* `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` when `n ≥ 0` (`clBlackModuleEFEquivQ`),
* `Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` when `n ≤ 0` (`clBlackModuleFEEquivQ`),

as right `T^λ_{i+ν}`-modules, where `Fᵢ` is induction along the map adding a black strand
(`appendBlackOp`) and `Eᵢ` is restriction along it. Both come from the statements on the
all-down matrix ring (`blackModuleEFEquivQ`, `blackModuleFEEquivQ`), transported through the
repaired Lemma 4.29 (`clOpEquivQ`) by `InductionAlong.resIndEquivTransport`.

This is the version of `BlackModuleEFTransport` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
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
local notation "KL" => blackScalarsQ Λ C hQ
local notation "T" => TensorProductAlgebra k (Q) Λ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "PD" => clDownwardBlockQ Λ C hQ P

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ ({i} + ν))ᵐᵒᵖ M]

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))

/-- A right `T^λ_{i+ν}`-module `M`, viewed as a module over the all-down matrix ring through
the repaired Lemma 4.29 (`clOpEquivQ`). -/
@[nolint unusedArguments]
def ClMatViewQ (_ : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
      (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
        I ⊕ Fin ℓ → ℤ) P)
    (_ : P.WFDom) (_ : I) (_ : Multiset I) (M : Type u) : Type u := M

instance : AddCommGroup (ClMatViewQ hP hwf i ν M) := inferInstanceAs (AddCommGroup M)

instance : Module (downwardMatrix (PD) ({i} + ν))ᵐᵒᵖ (ClMatViewQ hP hwf i ν M) :=
  Module.compHom M (clOpEquivQ hP hwf ({i} + ν)).symm.toRingHom

/-- The identity of `M`, from `T^λ` to its matrix-ring view. -/
def toClMatViewQ : M ≃+ ClMatViewQ hP hwf i ν M := AddEquiv.refl M

theorem toClMatView_smulQ (t : (TensorProductAlgebra k (Q) Λ ({i} + ν))ᵐᵒᵖ) (m : M) :
    toClMatViewQ hP hwf i ν M (t • m) =
      clOpEquivQ hP hwf ({i} + ν) t • toClMatViewQ hP hwf i ν M m := by
  change t • m = (clOpEquivQ hP hwf ({i} + ν)).symm (clOpEquivQ hP hwf ({i} + ν) t) • m
  rw [RingEquiv.symm_apply_apply]

local notation "MV" => ClMatViewQ hP hwf i ν M

/-- **`Eᵢ Fᵢ` against `Fᵢ Eᵢ` on `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the proof
of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with `λ` the right weight of content `i + ν`,
`Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for every right `T^λ_{i+ν}`-module `M`. Transported from the
all-down matrix ring (`blackModuleEFEquivQ`) through the repaired Lemma 4.29. -/
def clBlackModuleEFEquivQ (hn : 0 ≤ ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν))) :=
  resIndEquivTransport (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf ({i} + ν))
    (clOpEquivQ hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlackQ hP hwf i ν)
    (clOpEquiv_appendBlackQ hP hwf i ({i} + ν)) (toClMatViewQ hP hwf i ν M)
    (toClMatView_smulQ hP hwf i ν M) _
    (blackModuleEFEquivQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) (MV) hn)

/-- **`Fᵢ Eᵢ` against `Eᵢ Fᵢ` on `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the proof
of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`, with `λ` the right weight of content `i + ν`,
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` for every right `T^λ_{i+ν}`-module `M`. Transported from the
all-down matrix ring (`blackModuleFEEquivQ`) through the repaired Lemma 4.29. -/
def clBlackModuleFEEquivQ (hn : ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + ν)) ≤ 0) :=
  indResEquivTransport (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf ({i} + ν))
    (clOpEquivQ hP hwf ({i} + ({i} + ν))) (clOpEquiv_appendBlackQ hP hwf i ν)
    (clOpEquiv_appendBlackQ hP hwf i ({i} + ν)) (toClMatViewQ hP hwf i ν M)
    (toClMatView_smulQ hP hwf i ν M) _
    (blackModuleFEEquivQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) (MV) hn)

end CL

end Categorification.Stendhal
