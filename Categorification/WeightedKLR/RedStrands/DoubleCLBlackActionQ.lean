/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionPseudofunctorQ
import Categorification.WeightedKLR.RedStrands.DoubleCLMoritaQ
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction

/-!
# The categorical action on the tensor product algebras for every Kang–Kashiwara family

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31, over a field for every homogeneous Rouquier
(Kang–Kashiwara) family `Q`. The black strands carry the relations of Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1, `r = 1`) at the black scalars `Sb = blackScalarsQ`.

The black action of Theorem 4.28 for `U_Q(g)` (`blackActionPseudofunctorQ`) extends to the
additive idempotent completions of the violating quotients (`blackActionCompletedQ`). For the
presentation `clDownwardBlockQ` of Theorem 4.30 the reflected `U_Q(g)` relations hold
(`clDownwardBlockQ_reflectedBlack`), so `U_Q(g)` acts on these completions (`clBlackActionQ`).
At the weight `λ - ν` the value is the completion of `DT^λ_ν`, which by Theorem 4.30 is the
completion of the all-down boundaries, whose endomorphism ring is `T^λ_ν(Q)`
(`clBlackAction_tensorProductQ`).

As at the Khovanov–Lauda parameters (`clBlackAction_tensorProduct`), Webster states the action
on the categories of projective modules over the algebras `T^λ_ν`; here it acts on the additive
idempotent completions of the categories `DT^λ_ν`, which Theorem 4.30 identifies with them.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction DoubleDiagram KL3.Diagram

open scoped Classical

namespace DoubleDiagram

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]

/-- The black action of Theorem 4.28 for `U_Q(g)` on the additive idempotent completions of the
violating quotients. -/
abbrev blackActionCompletedQ (sc : CL.CLScalars C k)
    (P : Presentation (signature RD (fun r => (Λ r).val)) k)
    (hP : ∀ r : (CLQ.pres RD k sc).Rel,
      P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0) :=
  @StrictPseudofunctor.completion _ _ _ (blackActionPseudofunctorQ P hP)
    (fun a => inferInstanceAs (Preadditive (ViolatingCategory P a.as.region)))
    (fun _ _ f => blackAct_additive P _ (homWtQ f))

end DoubleDiagram

universe u v w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "wt₀" => (blockWeight Wgt (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
  I ⊕ Fin ℓ → ℤ)
local notation "RDc" => coordinateDatum Λ C
local notation "Sb" => blackScalarsQ Λ C hQ

/-- The reflected `U_Q(g)` relations hold in the presentation `clDownwardBlockQ` of
Theorem 4.30: they are imposed in its signed cap part. -/
theorem clDownwardBlockQ_reflectedBlack
    (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k)
    (r : (CLQ.pres (RDc) k (Sb)).Rel) :
    (clDownwardBlockQ Λ C hQ P).lin (blackMirrorLinear (RDc)
      (fun r => (coordinateRedWeights Λ C r).val) ((CLQ.pres (RDc) k (Sb)).rel r)) = 0 := by
  have h := signedCapKL_reflectedBlackQ (RDc) (redWeight Wgt) (Sb) P (clDownwardQ (Sb)) Λ
    (fun i j => ((Sb).t i j : k)) r
  refine Presentation.lin_eq_zero_of_relationsHold (Presentation.relationsHold_addRels _ _ _ _) ?_
  refine Presentation.lin_eq_zero_of_relationsHold (Presentation.relationsHold_addRels _ _ _ _) ?_
  exact Presentation.lin_eq_zero_of_relationsHold (Presentation.relationsHold_addRels _ _ _ _) h

variable (Λ C hQ) in
/-- The action of Cautis–Lauda's `U_Q(g)` on the additive idempotent completions of the
violating quotients of `clDownwardBlockQ` (Webster, arXiv:1309.3796v3, Theorem 4.31). -/
abbrev clBlackActionQ (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k) :=
  DoubleDiagram.blackActionCompletedQ (RD := RDc) (Λ := coordinateRedWeights Λ C) (Sb)
    (clDownwardBlockQ Λ C hQ P) (clDownwardBlockQ_reflectedBlack P)

/-- **Webster, arXiv:1309.3796v3, Theorem 4.31, for every Kang–Kashiwara family** over a
field. Cautis–Lauda's `U_Q(g)` at the black scalars `Sb` acts on the additive idempotent
completions of the categories `DT^λ_ν` by the strict pseudofunctor `clBlackActionQ`. Its value
at the weight `λ - ν` is the completion of `DT^λ_ν`; the all-down boundaries induce an
equivalence onto it from the completion of their full subcategory, whose sum has endomorphism
ring `T^λ_ν(Q)`. -/
theorem clBlackAction_tensorProductQ (ν : Multiset I)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P)
    (hwf : P.WFDom) :
    (clBlackActionQ Λ C hQ P).obj
        ⟨⟨(downRightWeight (RDc) (coordinateRedWeights Λ C) ν : I ⊕ Fin ℓ → ℤ)⟩⟩ =
        Cat.of (Karoubi (Mat_ (ViolatingCategory (clDownwardBlockQ Λ C hQ P)
          (downRightWeight (RDc) (coordinateRedWeights Λ C) ν)))) ∧
      Nonempty (TensorProductAlgebra k Q Λ ν ≃+*
        End (downSum (clDownwardBlockQ Λ C hQ P) ν)) ∧
      (allDownCompletionInclusion (clDownwardBlockQ Λ C hQ P)
        (right := downRightWeight (RDc) (coordinateRedWeights Λ C) ν)).IsEquivalence :=
  ⟨rfl, tensorProduct_moritaEquivalentQ ν hP hwf⟩

end Categorification.Stendhal
