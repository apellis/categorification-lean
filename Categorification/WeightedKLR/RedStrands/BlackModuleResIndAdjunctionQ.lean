/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleAdjunctionQ
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportQ
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.Diagrams.KLR.MatEndModuleAdjunctionNaturality
import Categorification.Algebra.InductionAlongTransportAdjunction

/-!
# `Eᵢ ⊣ Fᵢ` as an adjunction of functors on modules over `T^λ`

Webster, arXiv:1309.3796v3, Theorem 4.31: besides `Fᵢ ⊣ Eᵢ` (`blackAdjunction`), restriction
along the map adding a black strand is left adjoint to induction along it.

* `DoubleDiagram.blackResIndAdjunctionQ`: on the all-down matrix rings of the categorical
  action, from the natural bijection `blackResIndHomEquivQ`.
* `clBlackResIndAdjunctionQ`: `Eᵢ ⊣ Fᵢ` on right `T^λ`-modules at standard Khovanov–Lauda black
  scalars, transported through the repaired Lemma 4.29 (`clOpEquivQ`).

With `Fᵢ ⊣ Eᵢ`, this makes `Eᵢ` and `Fᵢ` biadjoint on ungraded modules, as Chuang–Rouquier's
`sl₂`-categorifications require (arXiv:math/0407205v2, §5.1.1); Webster uses this in §5.

This is the version of `BlackModuleResIndAdjunction` in which the black strands carry the relations of
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

namespace DoubleDiagram

section Block

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)
local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)

/-- **`Eᵢ ⊣ Fᵢ` on the all-down matrix rings** (Webster, arXiv:1309.3796v3, Theorem 4.31):
restriction along the matrix map of `Fᵢ` is left adjoint to induction along it. -/
def blackResIndAdjunctionQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0) :
    resFunctor.{max u v w, max u v w} (blackMatrixOp P t i ν) ⊣
      InductionAlong.functor.{max u v w, max u v w} (blackMatrixOp P t i ν) :=
  KLR.Diagram.MatEnd.resIndAdjunction F (appendDown_injective i) (blackAct_downObj (Q) i)
    (blackCompletedAdjunctionQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackCompletedAdjunctionOpQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec

end Block

end DoubleDiagram

section CL

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

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))

/-- **`Eᵢ ⊣ Fᵢ` on right `T^λ`-modules** (Webster, arXiv:1309.3796v3, Theorem 4.31), at
standard Khovanov–Lauda black scalars: restriction along the map adding a black strand of
colour `i` is left adjoint to induction along it. Transported from the all-down matrix rings
(`DoubleDiagram.blackResIndAdjunctionQ`) through the repaired Lemma 4.29 (`clOpEquivQ`). -/
def clBlackResIndAdjunctionQ :
    blackE (Q) Λ i ν ⊣ blackF (Q) Λ i ν :=
  resIndAdjunctionTransport.{u, u} (clOpEquivQ hP hwf ν)
    (clOpEquivQ hP hwf ({i} + ν)) (clOpEquiv_appendBlackQ hP hwf i ν)
    (DoubleDiagram.blackResIndAdjunctionQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P))

end CL

end Categorification.Stendhal
