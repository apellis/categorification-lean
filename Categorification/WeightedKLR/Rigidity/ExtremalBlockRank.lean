/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ExtremalWeightRank
import Categorification.WeightedKLR.RedStrands.SingleRedEulerAdjunction
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.SupIndep

/-!
# Ranks of cyclotomic projective blocks

For the rank calculation in Webster, arXiv:1309.3796v2, §7.1,
Proposition 7.2, the highest-weight isomorphism sends each content
summand into its quantum weight space. These inclusions are equalities
because the content summands span and the distinct weight spaces are
independent. This computes the Laurent rank at every content, including
the extremal multiplicity in a reduced coevaluation word.
-/

open Module DirectSum
open scoped TensorProduct
noncomputable section

namespace Categorification.Graded

private theorem finrank_of_baseChange_weight_decomposition
    {R S J V : Type*} [CommRing R] [StrongRankCondition R] [Field S] [Algebra R S]
    [DecidableEq J] [AddCommGroup V] [Module S V]
    (M : J → Type*) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] [∀ j, Module.Free R (M j)]
    (e : (S ⊗[R] ⨁ j, M j) ≃ₗ[S] V) (W : J → Submodule S V) (hind : iSupIndep W)
    (hmem : ∀ j x, e (1 ⊗ₜ[R] DirectSum.lof R J M j x) ∈ W j) (j : J) :
    finrank R (M j) = finrank S (W j) := by
  let F := fun i => S ⊗[R] M i
  let E := (TensorProduct.directSumRight R S S M).symm.trans e
  let φ (i : J) := E.toLinearMap.comp (DirectSum.lof S J F i)
  have hspan : ⨆ i, LinearMap.range (φ i) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨v, rfl⟩ := E.surjective x
    induction v using DirectSum.induction_on with
    | zero => simp
    | of i m => exact (le_iSup (fun s => LinearMap.range (φ s)) i) ⟨m, rfl⟩
    | add x y hx hy => simpa only [map_add] using add_mem hx hy
  have hle (i : J) : LinearMap.range (φ i) ≤ W i := by
    rintro _ ⟨m, rfl⟩
    induction m using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
    | tmul c x =>
      change e ((TensorProduct.directSumRight R S S M).symm (DirectSum.lof S J F i (c ⊗ₜ[R] x))) ∈ _
      rw [TensorProduct.directSumRight_symm_lof_tmul]
      have ht : c ⊗ₜ[R] (DirectSum.lof R J M i x) = c • (1 ⊗ₜ[R] DirectSum.lof R J M i x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul]
      exact (W i).smul_mem c (hmem i x)
  have hW := congrFun ((hind.le_iff_eq_of_iSup_eq_top hspan).mp hle) j
  have hinj : Function.Injective (φ j) := E.injective.comp (DirectSum.of_injective (β := F) j)
  rw [← hW, ← (LinearEquiv.ofInjective (φ j) hinj).finrank_eq]
  exact Module.finrank_baseChange.symm

end Categorification.Graded

namespace Categorification.KLR.CycKLR

open Categorification.Graded QuantumGroup QuantumGroup.UDot KLGamma LieLean LieLean.QuantumGroup
open Module
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra
local notation "v" => (RatFunc.X : RatFunc ℚ)
local notation "LP" => LaurentPolynomial ℤ
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {I k : Type*} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "𝒟" => projectiveRootDatum RD
local notation "λ₀" => RD.pair.flip highest
local notation "V" => IrreducibleModule 𝒟 v λ₀

omit [Fintype I] in
private theorem pair_flip_content (β : Multiset I) :
    RD.pair.flip (highest - (β.map RD.iX).sum) = λ₀ - (𝒟).rootSum β.toFinsupp := by
  rw [map_sub]
  congr 1
  induction β using Multiset.induction_on with
  | empty => simp
  | cons i β ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, (𝒟).rootSum_add,
      Multiset.toFinsupp_singleton, (𝒟).rootSum_single, one_smul, Multiset.map_add,
      Multiset.sum_add, map_add, ih, Multiset.map_singleton, Multiset.sum_singleton]
    rfl

include hΛ hR in
/-- The Laurent rank of the split projective Grothendieck group of one
cyclotomic content equals the dimension of its irreducible quantum weight space. -/
theorem finrank_projectiveBlock_eq_weightSpace (β : Multiset I) :
    finrank LP (K0 (grade G Λ β)) =
      finrank (RatFunc ℚ) (weightSpace 𝒟 v V (λ₀ - (𝒟).rootSum β.toFinsupp)) := by
  classical
  let (ν : Multiset I) := module_finite (Q := Q) (ν := ν) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ i))
  let (ν : Multiset I) := HasGdim.of_finiteDimensional (grade G Λ ν)
  let e := projectiveHighestWeightEquiv Λ RD highest hΛ hP hR
  let χ := fun ν : Multiset I => λ₀ - (𝒟).rootSum ν.toFinsupp
  have hχ : Function.Injective χ := fun _ _ h => Multiset.toFinsupp.injective
    ((𝒟).rootSum_injective hR (sub_right_injective h))
  apply finrank_of_baseChange_weight_decomposition (fun ν => K0 (grade G Λ ν)) e
    (fun ν => weightSpace 𝒟 v V (χ ν)) ?_ ?_ β
  · exact (iSupIndep_weightSpace (R := 𝒟) (M := V)
      (pow_ne_one_of_transcendental' LusztigF.transcendental_ratFunc_X)).comp hχ
  · intro ν x
    have h := projectiveIntegralEquiv_lof_mem_weightSpace hP Λ RD highest hΛ hR ν x
    rw [pair_flip_content] at h
    exact h

include hΛ hR in
/-- Webster, Proposition 7.2. For a reduced coevaluation word, the actual
cyclotomic projective block has Laurent rank one. -/
theorem finrank_coevaluation_projectiveBlock
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Dual K H))
    (match_weight : ∀ i, (weight : Dual K H) (P.coroot i) = (λ₀ ((𝒟).coroot i) : K))
    (w : List I) (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse) :
    finrank LP (K0 (grade G Λ (Stendhal.coevaluationWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w : Multiset I))) = 1 := by
  rw [finrank_projectiveBlock_eq_weightSpace hP Λ RD highest hΛ hR]
  exact Stendhal.finrank_quantum_coevaluationWeight P hR λ₀ weight hweight match_weight w hw

end Categorification.KLR.CycKLR
