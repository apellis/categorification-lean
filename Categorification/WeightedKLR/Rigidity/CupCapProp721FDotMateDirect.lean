/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721FDotTrace
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotMateDirect
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTraceTwo

/-!
# The conjugate dot on `𝔉_i` is the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the dots of the categorical action on derived categories, §4.6). On derived
categories of dg modules over `T^λ`, the dot on `𝔉_i` was defined in two ways: directly, as the
conjugate along the comparison isomorphism of the derived dot `indDotOfEq` on induction
(`CupCap.dgBlackFDot`), and as the conjugate along `𝔈_i ⊣ 𝔉_i` of the dot on `𝔈_i`
(`CupCap.dgBlackFDotMate`), which is the form used by the quantum trace statements. They agree
(`CupCap.dgBlackFDotMate_eq_dgBlackFDot`): on modules this is the symmetry of the trace of
Theorem 4.31 against the dot (`CupCap.blackEFAdjunction_conjugate_dot`), and conjugates pass to
derived categories (`CupCap.conjugateEquiv_mapDerivedCategory`) and along comparison functors
(`CupCap.conjugateEquiv_eq_of_comparison`).

## Main results

* `CupCap.dgBlackFDotMate_eq_dgBlackFDot`.

Route hypotheses: none beyond `C`, `hRq : IsRouquierQ C Q` (Webster's setting for
Theorem 4.31).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)

private theorem blackE_additive_fDotMateDirect : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive_fDotMateDirect : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive_fDotMateDirect blackF_additive_fDotMateDirect

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The conjugate dot on `𝔉_i` is the dot** (Webster, arXiv:1309.3796v3, Theorem 4.31, §4.6
and §7.3, proof of Proposition 7.21): on derived categories of dg modules over `T^λ`, the
conjugate along `𝔈_i ⊣ 𝔉_i` of the dot on `𝔈_i` is the dot on `𝔉_i`. -/
theorem dgBlackFDotMate_eq_dgBlackFDot :
    dgBlackFDotMate (Λ := Λ) ν i C hRq = dgBlackFDot.{0, 0} (Q := Q) (Λ := Λ) ν i C hRq := by
  let := blackF_preservesFiniteLimits Q Λ i ν C hRq
  let := blackF_preservesFiniteColimits Q Λ i ν C hRq
  have hder := conjugateEquiv_mapDerivedCategory (blackEFAdjunction Q Λ i ν C hRq)
    (blackEFAdjunction Q Λ i ν C hRq) (blackDot Q Λ i ν)
  rw [blackEFAdjunction_conjugate_dot] at hder
  exact conjugateEquiv_eq_of_comparison
    (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
    (adj' := derivedBlackResIndAdjunction.{0} Q Λ i ν C hRq (blackEFAdjunction Q Λ i ν C hRq))
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TAᵢᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TAᵐᵒᵖ)
      (derivedBlackResIndAdjunction.{0} Q Λ i ν C hRq (blackEFAdjunction Q Λ i ν C hRq))
      (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)
      d)
    _ _ hder _ _
    (isComparisonConj_comparisonConj _ _ _ _)
    (isComparisonConj_comparisonConj _ _ _ _)

end Categorification.Stendhal.CupCap
