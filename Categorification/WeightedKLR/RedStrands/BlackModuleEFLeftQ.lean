/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeft
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportQ
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# The commutation relation of `Eᵢ` and `Fᵢ` on left modules over `T^λ`

The commutation relation of the categorical action (Webster, arXiv:1309.3796v3, Thm 4.31) on
all left modules over the tensor product algebra `T^λ` at black scalars of a Kang–Kashiwara family, an input of the dimension count in the proof of Proposition 5.5 there. A left module
is a right module through the horizontal reflection `tensorFlip` (`FlipView`), which commutes
with adding a black strand (`tensorFlip_appendBlack`); the statements on right modules
(`clBlackModuleEFEquivQ`, `clBlackModuleFEEquivQ`) transport along it. With `n = ⟨i, λ⟩` for `λ`
the right weight of content `i + ν`,

* `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` when `n ≥ 0` (`clLeftBlackModuleEFEquivQ`),
* `Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` when `n ≤ 0` (`clLeftBlackModuleFEEquivQ`),

as left `T^λ_{i+ν}`-modules, where `Fᵢ` is induction along `appendBlack` and `Eᵢ` is
restriction along it.

This is the version of `BlackModuleEFLeft` in which the black strands carry the relations of
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

universe u w

section Flip

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

variable (ν : Multiset I) (M : Type w) [AddCommGroup M] [Module (TensorProductAlgebra k Q Λ ν) M]

instance : AddCommGroup (FlipView Q Λ ν M) := inferInstanceAs (AddCommGroup M)

instance : Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (FlipView Q Λ ν M) :=
  Module.compHom M (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν).symm.toRingHom

variable (i : I)

end Flip

section Dimension

variable {k T : Type*} [Field k] [Ring T] [Algebra k T]
  {X Y M : Type*} [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module T Y]
  [AddCommGroup M] [Module T M] {ι : Type*} [Fintype ι]

end Dimension

section CL

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

local notation "Si" => (Singleton.singleton i : Multiset I)

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ ({i} + ν)) M]

local notation "FV" => FlipView (Q) Λ (Si + ν) M

/-- **`Eᵢ Fᵢ` against `Fᵢ Eᵢ` on left `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the
proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with `λ` the right weight of content `i + ν`,
`Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for every left `T^λ_{i+ν}`-module `M`. -/
def clLeftBlackModuleEFEquivQ (hn : 0 ≤ ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν))) :=
  resIndEquivTransport (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ (Si + ν) i)
    (toFlipView (Q) Λ (Si + ν) M) (toFlipView_smul (Q) Λ (Si + ν) M) _
    (clBlackModuleEFEquivQ hP hwf i ν FV hn)

/-- **`Fᵢ Eᵢ` against `Eᵢ Fᵢ` on left `T^λ`-modules** (Webster, arXiv:1309.3796v3, input of the
proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`, with `λ` the right weight of content `i + ν`,
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` for every left `T^λ_{i+ν}`-module `M`. -/
def clLeftBlackModuleFEEquivQ (hn : ip (RDc) i
      (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν)) ≤ 0) :=
  indResEquivTransport (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + ν))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + (Si + ν)))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ν i)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ (Si + ν) i)
    (toFlipView (Q) Λ (Si + ν) M) (toFlipView_smul (Q) Λ (Si + ν) M) _
    (clBlackModuleFEEquivQ hP hwf i ν FV hn)

local notation "T₁" => TensorProductAlgebra k (Q) Λ (Si + ν)
local notation "nᵢ" => ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) (Si + ν))
local notation "EF" => InductionAlong.Res (appendBlackNU (Q := Q) (Λ := Λ) i (Si + ν))
  (InductionAlong.Ind M (appendBlackNU (Q := Q) (Λ := Λ) i (Si + ν)))
local notation "FE" => InductionAlong.Ind
  (InductionAlong.Res (appendBlackNU (Q := Q) (Λ := Λ) i ν) M)
  (appendBlackNU (Q := Q) (Λ := Λ) i ν)

include hP hwf in
/-- **The dimension form of the `Eᵢ`/`Fᵢ` commutation relation** on finite-dimensional left
`T^λ`-modules (Webster, arXiv:1309.3796v3, input of the dimension count in the proof of
Proposition 5.5): `dim Eᵢ Fᵢ M = dim Fᵢ Eᵢ M + n dim M` with `n = ⟨i, λ⟩`, in both signs of `n`,
dimensions over `k`. -/
theorem finrank_clLeftEF_eqQ
    [FiniteDimensional k (RestrictScalars k T₁ EF)]
    [FiniteDimensional k (RestrictScalars k T₁ FE)]
    [FiniteDimensional k (RestrictScalars k T₁ M)] :
    (Module.finrank k (RestrictScalars k T₁ EF) : ℤ) =
      Module.finrank k (RestrictScalars k T₁ FE) +
        nᵢ * Module.finrank k (RestrictScalars k T₁ M) := by
  rcases le_total 0 nᵢ with h | h
  · have e := finrank_restrictScalars_eq_of_equiv_prod (k := k)
      (clLeftBlackModuleEFEquivQ hP hwf i ν M h)
    rw [e, Fintype.card_fin]
    push_cast
    rw [Int.toNat_of_nonneg h]
  · have e := congrArg (Nat.cast : ℕ → ℤ) (finrank_restrictScalars_eq_of_equiv_prod (k := k)
      (clLeftBlackModuleFEEquivQ hP hwf i ν M h))
    rw [Fintype.card_fin] at e
    push_cast at e
    rw [Int.toNat_of_nonneg (by omega)] at e
    linear_combination -e

end CL

end Categorification.Stendhal
