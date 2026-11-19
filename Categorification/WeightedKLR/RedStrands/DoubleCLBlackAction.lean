/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionPseudofunctor
import Categorification.WeightedKLR.RedStrands.DoubleCLMorita
import Categorification.TwoRep.CompletionPseudofunctor

/-!
# The categorical action on the tensor product algebras

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31, at the standard Khovanov–Lauda black
parameters over a field.

The black action of Theorem 4.28 extends to the additive idempotent completions of the
violating quotients (`StrictPseudofunctor.completion`). For the presentation `clDownwardBlock`
of Theorem 4.30 the reflected black Khovanov–Lauda relations hold
(`clDownwardBlock_reflectedBlack`), so the Khovanov–Lauda 2-category acts on these completions
(`clBlackAction`). At the weight `λ - ν` the value is the completion of `DT^λ_ν`, which by
Theorem 4.30 is the completion of the all-down boundaries, whose endomorphism ring is `T^λ_ν`
(`clBlackAction_tensorProduct`).

Webster states the action on the categories of projective modules over the algebras `T^λ_ν`;
here it acts on the additive idempotent completions of the categories `DT^λ_ν`, which Theorem
4.30 identifies with them. The 1-cell dual records that the reflection reverses 1-morphisms.
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

instance violatingWhiskerRight_additive
    (P : Presentation (signature RD (fun r => (Λ r).val)) k) {μ ν : X}
    (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) :
    (violatingWhiskerRight P v hv hν).Additive := by
  unfold violatingWhiskerRight
  infer_instance

instance blackAct_additive (P : Presentation (signature RD (fun r => (Λ r).val)) k) {μ ν : X}
    (s : List (Letter I)) (hs : wt RD μ s = ν) : (blackAct P s hs).Additive := by
  unfold blackAct
  infer_instance

/-- The black action of Theorem 4.28 on the additive idempotent completions of the violating
quotients. -/
abbrev blackActionCompleted (P : Presentation (signature RD (fun r => (Λ r).val)) k)
    (hP : ∀ r : (pres RD k).Rel,
      P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0) :=
  @StrictPseudofunctor.completion _ _ _ (blackActionPseudofunctor P hP)
    (fun a => inferInstanceAs (Preadditive (ViolatingCategory P a.as.region)))
    (fun _ _ f => blackAct_additive P _ (homWt f))

end DoubleDiagram

theorem _root_.StringDiagrams.Presentation.lin_eq_zero_of_relationsHold {S : Signature}
    {R : Type*} [CommRing R] {P Q : Presentation S R} (h : P.RelationsHold Q) {a b : Obj S}
    {x : LinDiagram R a b} (hx : P.lin x = 0) : Q.lin x = 0 := by
  rw [← Presentation.extension_map_lin P Q ((P.relationsHold_iff_ideal_le Q).mp h), hx,
    Functor.map_zero]

universe u v w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "wt₀" => (blockWeight Wgt (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
  I ⊕ Fin ℓ → ℤ)
local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

/-- The reflected black Khovanov–Lauda relations hold in the presentation `clDownwardBlock` of
Theorem 4.30: they are imposed in its signed cap part. -/
theorem clDownwardBlock_reflectedBlack
    (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k) (r : (pres (RDc) k).Rel) :
    (clDownwardBlock Λ C P).lin (blackMirrorLinear (RDc)
      (fun r => (coordinateRedWeights Λ C r).val) ((pres (RDc) k).rel r)) = 0 := by
  have h := signedCapKL_reflectedBlack (RDc) (redWeight Wgt) P (clDownwardQ KL) Λ
    (fun _ _ => 1) r
  refine Presentation.lin_eq_zero_of_relationsHold (Presentation.relationsHold_addRels _ _ _ _) ?_
  refine Presentation.lin_eq_zero_of_relationsHold (Presentation.relationsHold_addRels _ _ _ _) ?_
  exact Presentation.lin_eq_zero_of_relationsHold (Presentation.relationsHold_addRels _ _ _ _) h

variable (Λ C) in
/-- The action of the Khovanov–Lauda 2-category on the additive idempotent completions of the
violating quotients of `clDownwardBlock` (Webster, arXiv:1309.3796v3, Theorem 4.31). -/
abbrev clBlackAction (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k) :=
  DoubleDiagram.blackActionCompleted (RD := RDc) (Λ := coordinateRedWeights Λ C)
    (clDownwardBlock Λ C P) (clDownwardBlock_reflectedBlack P)

/-- **Webster, arXiv:1309.3796v3, Theorem 4.31**, at the standard Khovanov–Lauda parameters
over a field, with the downward relations of the repaired Theorem 4.30. The Khovanov–Lauda
2-category acts on the additive idempotent completions of the categories `DT^λ_ν` by the strict
pseudofunctor `clBlackAction`. Its value at the weight `λ - ν` is the completion of `DT^λ_ν`;
the all-down boundaries induce an equivalence onto it from the completion of their full
subcategory, whose sum has endomorphism ring `T^λ_ν`. -/
theorem clBlackAction_tensorProduct (ν : Multiset I)
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P)
    (hwf : P.WFDom) :
    (clBlackAction Λ C P).obj
        ⟨⟨(downRightWeight (RDc) (coordinateRedWeights Λ C) ν : I ⊕ Fin ℓ → ℤ)⟩⟩ =
        Cat.of (Karoubi (Mat_ (ViolatingCategory (clDownwardBlock Λ C P)
          (downRightWeight (RDc) (coordinateRedWeights Λ C) ν)))) ∧
      Nonempty (TensorProductAlgebra k (CL.qCL KL) Λ ν ≃+*
        End (downSum (clDownwardBlock Λ C P) ν)) ∧
      (allDownCompletionInclusion (clDownwardBlock Λ C P)
        (right := downRightWeight (RDc) (coordinateRedWeights Λ C) ν)).IsEquivalence :=
  ⟨rfl, clTensorProduct_moritaEquivalent ν hstd hP hwf⟩

end Categorification.Stendhal
