/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ReducedCoevaluationWord
import LieLean.RepresentationTheory.Crystal.Extremal
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Multiplicity
import LieLean.Algebra.QuantumGroup.Character

/-!
# Multiplicity of a reduced coevaluation word

Webster, arXiv:1309.3796v2, §7.1, Proposition 7.2. The root content of the
divided-power word gives a Weyl translate of the highest classical weight.
Weyl invariance and the quantum character comparison identify the dimension
of the corresponding rational-function quantum weight space.
-/

noncomputable section

open Module
namespace Categorification.Stendhal
open Matrix.Realization.KacMoodyAlgebra

variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K]
  [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (P : Matrix.Realization A K H) (hA : A.IsGeneralizedCartan)
local notation "D" => P.cartanDatum hA
local notation "cs" => P.coxeterSystem hA

/-- The classical irreducible weight space at the content of any reduced coevaluation word has dimension one. -/
theorem finrank_classical_coevaluationWeight (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Dual K H)) (w : List I)
    (hw : (cs).IsReduced w.reverse) :
    finrank K (weightSpace P (IrreducibleModule P (weight : Dual K H))
      (weight - P.rootOf fun i => (((coevaluationWord D weight w : Multiset I).toFinsupp i : ℕ) : ℤ))) = 1 := by
  let g := (cs).wordProd w.reverse
  have hδ := rootSum_coevaluationWord_of_reduced P hA weight hweight w hw
  rw [P.coe_rootSum_cartanDatum hA] at hδ
  rw [hδ, sub_sub_cancel]
  have hI := (IrreducibleModule.isIntegrable_iff P hA).mpr hweight
  obtain ⟨e⟩ := nonempty_weightSpace_weylGroup_equiv hA hI g.property (weight : Dual K H)
  exact e.finrank_eq.trans (IrreducibleModule.finrank_weightSpace_self P _)

section Quantum
open LieLean
variable {Y : Type*} [AddCommGroup Y] {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
  (P' : Matrix.Realization Δ.cartanMatrix K H) [FiniteDimensional K H] (hR : R.IsXRegular)
  (hwgt : Y →+ ℤ)
local notation "v" => (RatFunc.X : RatFunc ℚ)
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "D'" => P'.cartanDatum hCartan

include hR in
/-- The quantum weight space at the same content has dimension one for a matching highest weight. -/
theorem finrank_quantum_coevaluationWeight (weight : P'.integralWeights)
    (hweight : P'.IsDominantIntegral (weight : Dual K H))
    (match_weight : ∀ i, (weight : Dual K H) (P'.coroot i) = (hwgt (R.coroot i) : K))
    (w : List I) (hw : (P'.coxeterSystem hCartan).IsReduced w.reverse) :
    finrank (RatFunc ℚ) (LieLean.QuantumGroup.weightSpace R v
      (LieLean.QuantumGroup.IrreducibleModule R v hwgt)
      (hwgt - R.rootSum (coevaluationWord D' weight w : Multiset I).toFinsupp)) = 1 := by
  have hdom (i : I) : 0 ≤ hwgt (R.coroot i) := by
    obtain ⟨n, hn⟩ := hweight i
    have he : (hwgt (R.coroot i) : K) = (n : K) := (match_weight i).symm.trans hn
    exact_mod_cast (he.ge.trans' (Nat.cast_nonneg n))
  rw [LieLean.QuantumGroup.IrreducibleModule.finrank_weightSpace_eq_ratFunc hR hdom P' match_weight]
  exact finrank_classical_coevaluationWeight P' hCartan weight hweight w hw

end Quantum
end Categorification.Stendhal
