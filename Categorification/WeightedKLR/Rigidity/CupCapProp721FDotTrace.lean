/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721FDotCyclic
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclicMat
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFAdjoint
import Categorification.WeightedKLR.RedStrands.DoubleCLNewStrandQ

/-!
# The conjugate of the dot along `𝔈_i ⊣ 𝔉_i` is the dot on `𝔉_i`, on modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31
and §5.1, as used in §7.3, proof of Proposition 7.21. On right `T^λ`-modules the dot on
`𝔉_i = Ind` is defined as the conjugate, along `𝔉_i ⊣ 𝔈_i` (induction ⊣ restriction), of the
dot on `𝔈_i = Res` (`indDotOfEq`). Its conjugate along the other adjunction `𝔈_i ⊣ 𝔉_i` of
Theorem 4.31 (`CupCap.blackEFAdjunction`) is the same
(`CupCap.blackEFAdjunction_conjugate_dot`).

The proof is the symmetry of the trace of `𝔈_i ⊣ 𝔉_i` against the dot
(`CupCap.conjugateEquiv_resAct_eq_of_trace`). That adjunction is transported, through the
repaired Lemma 4.29 (`clOpEquivQ`), from the adjunction along the matrix map of the downward
black strand (`DoubleDiagram.blackResIndAdjunctionQ`), and the transport carries the dot of
`T^λ` to the diagonal matrix of the black-action dot (`clOpEquivQ_appendedDot`); the trace of the
matrix adjunction is symmetric against it because the black-action dot is cyclic
(`KLR.Diagram.MatEnd.resIndTrace_cyclic`, `DoubleDiagram.blackCompleted_dot_isCyclicQ`).

## Main results

* `CupCap.resIndTrace_cyclic_of_eq`: symmetry of the trace against equal elements.
* `CupCap.clBlackResIndAdjunctionQ_trace_dot`,
  `CupCap.clBlackResIndAdjunctionQ_conjugate_blackDot`: the statements for the adjunction
  `clBlackResIndAdjunctionQ` of Theorem 4.31 with an auxiliary presentation `P`.
* `CupCap.blackEFAdjunction_trace_dot`: the trace of `CupCap.blackEFAdjunction` is symmetric
  against the dot.
* `CupCap.blackEFAdjunction_conjugate_dot`: the conjugate of `blackDot` along
  `CupCap.blackEFAdjunction` is `indDotOfEq rfl`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Congr

variable {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B}
  (adj : resFunctor.{0, 0} φ ⊣ InductionAlong.functor.{0, 0} φ)

/-- Symmetry of the trace against `c` follows from symmetry against an element equal to `c`. -/
theorem resIndTrace_cyclic_of_eq {c c' : B} (e : c = c') (hc : ∀ a, c * φ a = φ a * c)
    (hc' : ∀ a, c' * φ a = φ a * c')
    (h : ∀ (z : Corner φ) (hz : φ 1 * z.1 = z.1),
      resIndTrace adj (c' • z) (smul_corner_fixed hc' z hz) =
        resIndTrace adj (cornerMul (intertwines_of_commute hc') z)
          (cornerMul_fixed (intertwines_of_commute hc') z hz))
    (z : Corner φ) (hz : φ 1 * z.1 = z.1) :
    resIndTrace adj (c • z) (smul_corner_fixed hc z hz) =
      resIndTrace adj (cornerMul (intertwines_of_commute hc) z)
        (cornerMul_fixed (intertwines_of_commute hc) z hz) := by
  subst e
  exact h z hz

end Congr

section CL

open scoped Classical

-- `OrdSeq` carries a second `Fintype` instance; the matrix rings use `Subtype.fintype`.
attribute [-instance] Categorification.Stendhal.instFintypeOrdSeq

variable {I : Type} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

variable {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, 0} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ
local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ (KL)) Λ) (signedCapPresentationOf (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k (KL)) P (clDownwardQ (KL)) Λ
    fun i j => (CL.CLScalars.t (KL) i j : k))
local notation "PD" => clDownwardBlockQ Λ C hQ P
local notation "hPD" => clDownwardBlockQ_reflectedBlack P
local notation "νᵢ" => (Singleton.singleton i : Multiset I) + ν
local notation "Ma" => DoubleDiagram.blackResIndAdjunctionQ (Pin) (CL.CLScalars.t (KL)) i ν
  (clDownwardBlockQ_reflectedBlack P)

/-- **The trace of `𝔈_i ⊣ 𝔉_i` is symmetric against the dot** (Webster, arXiv:1309.3796v3,
Theorem 4.31), for the adjunction `clBlackResIndAdjunctionQ` with an auxiliary presentation `P`
as in Theorem 4.30: transported from the all-down matrix rings through the repaired Lemma 4.29. -/
theorem clBlackResIndAdjunctionQ_trace_dot (z : Corner (appendBlackOp Q Λ i ν))
    (hz : appendBlackOp Q Λ i ν 1 * z.1 = z.1) :
    resIndTrace (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν) (op (appendedDot Q Λ i ν) • z)
        (smul_corner_fixed (op_appendedDot_commute Q Λ i ν) z hz) =
      resIndTrace (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν)
        (cornerMul (intertwines_of_commute (op_appendedDot_commute Q Λ i ν)) z)
        (cornerMul_fixed (intertwines_of_commute (op_appendedDot_commute Q Λ i ν)) z hz) := by
  have h1 := blackCompleted_dot_isCyclicQ (PD) (hPD) i
    (wt_downRightWeight (Λ := coordinateRedWeights Λ C) i ν)
    (wt_upDownRightWeight i ν)
  have h2 := KLR.Diagram.MatEnd.resIndTrace_cyclic
    (blackAct (PD) [(false, i)] (wt_downRightWeight i ν)) (appendDown_injective i)
    (blackAct_downObj (PD) i)
    (blackCompletedAdjunctionQ (PD) (hPD) i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackCompletedAdjunctionOpQ (PD) (hPD) i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i ν).choose_spec.choose
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated (Pin) (CL.CLScalars.t (KL)) i ν).choose_spec.choose_spec.choose_spec
    _ h1
  have h3 := resIndTrace_cyclic_of_eq (Ma) (clOpEquivQ_appendedDot hP hwf i ν)
    (transport_commute (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf (νᵢ))
      (clOpEquiv_appendBlackQ hP hwf i ν) (op_appendedDot_commute Q Λ i ν))
    (KLR.Diagram.MatEnd.natEmb_commute (blackAct (PD) [(false, i)] (wt_downRightWeight i ν))
      (appendDown_injective i) (blackAct_downObj (PD) i)
      (blackMapQ (PD) (hPD) (wt_downRightWeight i ν) (wt_downRightWeight i ν) (dnDotQ i _))) h2
  exact resIndTrace_transport_cyclic (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf (νᵢ))
    (clOpEquiv_appendBlackQ hP hwf i ν) (Ma) (op_appendedDot_commute Q Λ i ν) h3 z hz

/-- **The conjugate of the dot along `𝔈_i ⊣ 𝔉_i` is the dot on `𝔉_i`** (Webster,
arXiv:1309.3796v3, Theorem 4.31 and §5.1), for the adjunction `clBlackResIndAdjunctionQ` with an
auxiliary presentation `P` as in Theorem 4.30. -/
theorem clBlackResIndAdjunctionQ_conjugate_blackDot :
    conjugateEquiv (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν)
        (clBlackResIndAdjunctionQ.{0, 0} hP hwf i ν) (blackDot Q Λ i ν) =
      indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) :=
  conjugateEquiv_resAct_eq_of_trace _ (op_appendedDot_commute Q Λ i ν) _
    (fun _ => rfl) (clBlackResIndAdjunctionQ_trace_dot hP hwf i ν)

end CL

section Black

variable {I : Type} [inst : DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

/-- **The conjugate of the dot along `𝔈_i ⊣ 𝔉_i` is the dot on `𝔉_i`** (Webster,
arXiv:1309.3796v3, Theorem 4.31 and §5.1): on right `T^λ`-modules, the conjugate along
`CupCap.blackEFAdjunction` of the dot `blackDot` on `𝔈_i` is the dot `indDotOfEq` on `𝔉_i`,
the conjugate of `blackDot` along `𝔉_i ⊣ 𝔈_i`. -/
theorem blackEFAdjunction_conjugate_dot (C : QuantumGroup.CartanDatum I)
    (hRq : IsRouquierQ C Q) :
    conjugateEquiv (blackEFAdjunction Q Λ i ν C hRq) (blackEFAdjunction Q Λ i ν C hRq)
        (blackDot Q Λ i ν) =
      indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  exact clBlackResIndAdjunctionQ_conjugate_blackDot (hQ := hRq)
    (P := ⟨PEmpty, PEmpty.elim, PEmpty.elim, fun r => r.elim⟩)
    (fun r => r.elim) (fun r => r.elim) i ν

/-- **The trace of `𝔈_i ⊣ 𝔉_i` is symmetric against the dot** (Webster, arXiv:1309.3796v3,
Theorem 4.31), for `CupCap.blackEFAdjunction`. -/
theorem blackEFAdjunction_trace_dot (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)
    (z : Corner (appendBlackOp Q Λ i ν)) (hz : appendBlackOp Q Λ i ν 1 * z.1 = z.1) :
    resIndTrace (blackEFAdjunction Q Λ i ν C hRq) (op (appendedDot Q Λ i ν) • z)
        (smul_corner_fixed (op_appendedDot_commute Q Λ i ν) z hz) =
      resIndTrace (blackEFAdjunction Q Λ i ν C hRq)
        (cornerMul (intertwines_of_commute (op_appendedDot_commute Q Λ i ν)) z)
        (cornerMul_fixed (intertwines_of_commute (op_appendedDot_commute Q Λ i ν)) z hz) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  exact clBlackResIndAdjunctionQ_trace_dot (hQ := hRq)
    (P := ⟨PEmpty, PEmpty.elim, PEmpty.elim, fun r => r.elim⟩)
    (fun r => r.elim) (fun r => r.elim) i ν z hz

end Black

end Categorification.Stendhal.CupCap
