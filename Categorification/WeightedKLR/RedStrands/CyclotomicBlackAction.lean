/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction
import Categorification.WeightedKLR.RedStrands.EraseRed

/-!
# The categorical action on cyclotomic KLR algebras

Webster, arXiv:1309.3796v3, §3, Theorem 3.17, at the standard Khovanov–Lauda black
parameters over a field, as the case of one red strand of Theorem 4.31.

For one red strand of label `λ` the action `clBlackAction` of Theorem 4.31 acts on the additive
idempotent completions of the categories `DT^λ_ν`. By Theorem 4.30 these are the completions of
the all-down boundaries, whose sum has endomorphism ring `T^λ_ν`, and by Theorem 4.18 (v2
Theorem 4.20, `SingleRed.cyclotomicEquiv`) this is the cyclotomic KLR algebra `R^λ_ν`. So the
Khovanov–Lauda 2-category acts on the categories of projective `R^λ_ν`-modules.

The same statement gives Corollary 3.20 in this realization: `DR^λ_ν` is `DT^λ_ν` for one red
strand, the all-down boundaries correspond to Webster's idempotent `e₋`, the corner `e₋ DR^λ e₋`
is `R^λ_ν`, and the inclusion of the all-down boundaries is an equivalence of additive idempotent
completions, that is, a Morita equivalence between `R^λ_ν` and `DR^λ_ν`.

Webster constructs the action directly from induction and restriction along the inclusions
`R^λ_ν → R^λ_{ν+i}` (Lemmas 3.7, 3.8 and Theorem 3.9 for one colour). Here it is obtained
from the action on tensor product algebras, as Webster's §4.6 indicates for general `λ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction DoubleDiagram KL3.Diagram

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v w

variable {I : Type u} {C : CartanDatum I} {k : Type v} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

/-- **Webster, arXiv:1309.3796v3, Theorem 3.17 and Corollary 3.20**, at the standard Khovanov–Lauda parameters
over a field. For one red strand of label `λ`, the Khovanov–Lauda 2-category acts by the strict
pseudofunctor `clBlackAction` of Theorem 4.31. Its value at the weight `λ - ν` is the additive
idempotent completion of `DT^λ_ν`; the all-down boundaries induce an equivalence onto it from the
completion of their full subcategory, whose sum has endomorphism ring the cyclotomic KLR algebra
`R^λ_ν`. -/
theorem clBlackAction_cyclotomic (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (coordinateDatum Λ C)
      (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ)
      (blockWeight (cyclotomicCoverWeightDatum Λ C)
        (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0) P)
    (hwf : P.WFDom) :
    (clBlackAction Λ C P).obj
        ⟨⟨(downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν :
          I ⊕ Fin 1 → ℤ)⟩⟩ =
        Cat.of (Karoubi (Mat_ (ViolatingCategory (clDownwardBlock Λ C P)
          (downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν)))) ∧
      Nonempty (CycKLR k (CL.qCL KL) (fun i => Polynomial.X ^ Λ 0 i) ν ≃+*
        End (downSum (clDownwardBlock Λ C P) ν)) ∧
      (allDownCompletionInclusion (clDownwardBlock Λ C P)
        (right := downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν)
        ).IsEquivalence := by
  obtain ⟨h₁, ⟨e⟩, h₃⟩ := clBlackAction_tensorProduct (hQ := hQ) ν hstd hP hwf
  refine ⟨h₁, ⟨RingEquiv.trans ?_ e⟩, h₃⟩
  exact RingEquiv.ofBijective (SingleRed.cyclotomicEquiv (CL.qCL KL) Λ ν).toRingHom
    (SingleRed.cyclotomicEquiv (CL.qCL KL) Λ ν).bijective

end Categorification.Stendhal
