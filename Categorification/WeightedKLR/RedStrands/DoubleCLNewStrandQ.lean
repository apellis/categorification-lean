/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackInductionQ
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackNewStrandQ
import Categorification.WeightedKLR.RedStrands.BlackNewStrandProjection

/-!
# The new-strand dot and crossing of `T^λ` are the black-action dot and crossing

Webster, arXiv:1309.3796v3, §4.6 (Theorems 4.30, 4.31) and §5.1. Under the repaired Lemma 4.29
on opposite rings (`clOpEquivQ`), the dot `y = x_n · ν_i(1)` on the new strand of `T^λ`
(`appendedDot`) is the diagonal matrix of the dot of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3,
Definition 1.1, `r = 1`) acting on `Fᵢ` (`clOpEquivQ_appendedDot`), and `-τ = ψ_n · ν_i(ν_i(1))`
(`appendedCross`) is the diagonal matrix of the Cautis–Lauda crossing acting on `FᵢFᵢ`
(`clOpEquivQ_neg_appendedCross`). The sign is the convention of Khovanov–Lauda III by which the
same-colour crossing acts as `-ψ`.

The hypotheses on the presentation `P` are those of Webster's Theorem 4.30 in the library:
negligible cover relations (`CoverRelsNegligible`) and well-founded domains (`WFDom`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "PD" => clDownwardBlockQ Λ C hQ P
local notation "hPD" => clDownwardBlockQ_reflectedBlack P
local notation "PS" => signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C))
  (CLQ.pres (RDc) k (KL)) P (clDownwardQ (KL)) Λ fun i j => (CL.CLScalars.t (KL) i j : k)

/-- **The new-strand dot of `T^λ` is the black-action dot** (Webster, arXiv:1309.3796v3, §5.1,
through the repaired Lemma 4.29). -/
theorem clOpEquivQ_appendedDot :
    clOpEquivQ hP hwf ({i} + ν) (op (appendedDot Q Λ i ν)) =
      op (KLR.Diagram.MatEnd.natEmb (blackAct (PD) [(false, i)] (wt_downRightWeight i ν))
        (blackAct_downObj (PD) i)
        (blackMapQ (PD) (hPD) (wt_downRightWeight i ν) (wt_downRightWeight i ν)
          (dnDotQ i _))) := by
  refine congrArg op ?_
  rw [natEmb_blackMapQ_dot]
  change ordinaryToDownwardMatrix _ _ Λ _ (tensorRescale Λ _ _ _ (appendedDot Q Λ i ν)) = _
  rw [tensorRescale_appendedDot, appendedDot_eq_projection, map_mul, ordinaryToDownwardMatrix_x,
    ordinaryToDownwardMatrix_appendBlack, map_one]
  rfl

/-- **Minus the new-strand crossing of `T^λ` is the black-action crossing** (Webster,
arXiv:1309.3796v3, §5.1, through the repaired Lemma 4.29). -/
theorem clOpEquivQ_neg_appendedCross :
    clOpEquivQ hP hwf ({i} + ({i} + ν)) (op (-appendedCross Q Λ i ν)) =
      op (KLR.Diagram.MatEnd.natEmb (blackAct (PD) [(false, i)] (wt_downRightWeight i ν) ⋙
          blackAct (PD) [(false, i)] (wt_downRightWeight i ({i} + ν)))
        (KLR.Diagram.MatEnd.compEq _ _ (blackAct_downObj (PD) i) (blackAct_downObj (PD) i))
        (crossNatQ (PD) (hPD) i ν)) := by
  refine congrArg op ?_
  rw [natEmb_crossNatQ]
  change ordinaryToDownwardMatrix _ _ Λ _ (tensorRescale Λ _ _ _ (-appendedCross Q Λ i ν)) = _
  rw [map_neg, tensorRescale_appendedCross, appendedCross_eq, neg_neg, map_mul]
  have h1 := ordinaryToDownwardMatrix_ψ (RD := RDc) (Λ := coordinateRedWeights Λ C) (PS)
    (clDownwardQ (KL)) Λ (KL).t (ν := {i} + ({i} + ν)) (Multiset.card (stendhalWeight ℓ ν))
  have h2 := ordinaryToDownwardMatrix_appendBlack (RD := RDc) (Λ := coordinateRedWeights Λ C)
    (PS) (clDownwardQ (KL)) Λ (KL).t i ({i} + ν) (appendBlack (clDownwardQ (KL)) Λ i ν 1)
  have h3 := ordinaryToDownwardMatrix_appendBlack (RD := RDc) (Λ := coordinateRedWeights Λ C)
    (PS) (clDownwardQ (KL)) Λ (KL).t i ν 1
  refine congrArg₂ (· * ·) ?_ ?_
  · convert h1 using 2
  · refine (h2.trans (congrArg (blackMatrix _ i) h3)).trans ?_
    exact congrArg (fun z => blackMatrix (PD) i (blackMatrix (PD) i z)) (map_one _)

end Categorification.Stendhal
