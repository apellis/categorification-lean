/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CoevaluationDividedPower
import Categorification.WeightedKLR.Rigidity.ExtremalStringNorm
import Categorification.WeightedKLR.Rigidity.ExtremalRaising
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaIntegral

/-!
# The norm of a reduced coevaluation word

Webster, arXiv:1309.3796v2, §7.1, Proposition 7.2. Each reduced prefix
is extremal, so its divided power traverses the entire primitive string.
-/

noncomputable section
namespace Categorification.Stendhal
open LieLean Module

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} (R : Δ.RootDatum Y)
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan

omit [DecidableEq I] in
private theorem coroot_rootSum_match (i : I) (β : I →₀ ℕ) :
    (Dc).coroot i ((Dc).rootSum β) = R.rootSum β (R.coroot i) := by
  induction β using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [CartanDatum.rootSum_add, map_add, hf, hg, R.rootSum_add, AddMonoidHom.add_apply]
  | single j n =>
    rw [CartanDatum.rootSum_single, R.rootSum_single, map_nsmul, AddMonoidHom.nsmul_apply,
      R.root_coroot, ← CartanDatum.cartanMatrix_apply, P.cartanMatrix_cartanDatum]

/-- The current quantum coroot coordinate is the integer used to form the next nilHecke block. -/
theorem coevaluation_endpoint_pairing (L : Y →+ ℤ) (weight : P.integralWeights)
    (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (L (R.coroot j) : K))
    (w : List I) (hw : NonnegativeReflectionPath Dc weight w) (i : I) :
    (L - R.rootSum (coevaluationWord Dc weight w : Multiset I).toFinsupp) (R.coroot i) =
      (Dc).coroot i (w.foldl (fun μ j => (Dc).reflection j μ) weight) := by
  have ht := rootSum_coevaluationWord Dc weight w hw
  have h := coroot_rootSum_match R P i (coevaluationWord Dc weight w : Multiset I).toFinsupp
  rw [ht, map_sub] at h
  have he : (Dc).coroot i weight = L (R.coroot i) := by
    apply Int.cast_injective (α := K)
    rw [P.coroot_cartanDatum_cast, hm]
  rw [AddMonoidHom.sub_apply, ← h, he]
  abel

open KLR.KLRAlgebra KLR.CycKLR LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩

variable {R} (highest : Dom R) (hR : R.IsXRegular)

omit [Fintype I] in
private theorem loweringWord_snoc (d : List (I × ℕ)) (i : I) (n : ℕ) :
    dividedLoweringWord highest (d ++ [(i, n)]) =
      qDivPow (vQ ^ Δ.d i) n (F R vQ i) • dividedLoweringWord highest d := by
  simp [dividedLoweringWord, List.foldl_append]

private theorem bar_dividedLoweringWord (d : List (I × ℕ)) :
    hwBar hR highest (dividedLoweringWord highest d) = dividedLoweringWord highest d := by
  induction d using List.reverseRecOn with
  | nil => exact hwBar_hwv hR highest
  | append_singleton d a ih =>
    rcases a with ⟨i, n⟩
    rw [loweringWord_snoc, hwBar_smul_U, barHom_qDivPow, barHom_F, ih]

omit [Fintype I] in
private theorem dividedLoweringWord_mem_weight (d : List (I × ℕ)) :
    dividedLoweringWord highest d ∈ weightSpace R vQ _
      (highest.1 - R.rootSum (expandDiv d : Multiset I).toFinsupp) := by
  induction d using List.reverseRecOn with
  | nil => simpa [expandDiv, dividedLoweringWord] using (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := vQ) (Λ := highest.1))
  | append_singleton d a ih =>
    rcases a with ⟨i, n⟩
    have hν : (List.replicate n i : Multiset I).toFinsupp = Finsupp.single i n := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [loweringWord_snoc, expandDiv_append, ← Multiset.coe_add, Multiset.toFinsupp_add, R.rootSum_add, ← sub_sub]
    change _ ∈ weightSpace R vQ _ (_ - R.rootSum (List.replicate n i : Multiset I).toFinsupp)
    rw [hν, R.rootSum_single]
    exact qDivPow_F_smul_mem_weightSpace ih i n

variable [FiniteDimensional K H]

/-- The normalized quantum vector for any reduced coevaluation word has Shapovalov norm one. -/
theorem websterForm_coevaluationDividedWord (weight : P.integralWeights)
    (hdom : P.IsDominantIntegral (weight : Dual K H))
    (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (highest.1 (R.coroot j) : K))
    (w : List I) (hw : (P.coxeterSystem hCartan).IsReduced w.reverse) :
    SingleBlack.websterForm highest hR
      (dividedLoweringWord highest (coevaluationDividedWord Dc weight w))
      (dividedLoweringWord highest (coevaluationDividedWord Dc weight w)) = 1 := by
  induction w using List.reverseRecOn with
  | nil => exact SingleBlack.websterForm_hwv highest hR
  | append_singleton w i ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at hw
    have hpre : (P.coxeterSystem hCartan).IsReduced w.reverse := by simpa using hw.drop 1
    let d := coevaluationDividedWord Dc weight w
    let β := (coevaluationWord Dc weight w : Multiset I).toFinsupp
    let μ := highest.1 - R.rootSum β
    let g := (P.coxeterSystem hCartan).wordProd w.reverse
    let η := w.foldl (fun μ j => (Dc).reflection j μ) weight
    have hnd : ¬(P.coxeterSystem hCartan).IsLeftDescent g i := by
      apply (P.coxeterSystem hCartan).not_isLeftDescent_iff.mpr
      rw [← (P.coxeterSystem hCartan).wordProd_cons, hw.eq, hpre.eq, List.length_cons]
    have hcontent : (weight : Dual K H) - P.rootOf (fun j => (β j : ℤ)) = g.val weight := by
      have h := rootSum_coevaluationWord_of_reduced P hCartan weight hdom w hpre
      rw [P.coe_rootSum_cartanDatum hCartan] at h
      rw [show P.rootOf (fun j => (β j : ℤ)) = (weight : Dual K H) - g.val weight from h, sub_sub_cancel]
    have hpair := coevaluation_endpoint_pairing R P highest.1 weight hm w
      (nonnegativeReflectionPath_of_reduced P hCartan weight hdom w hpre) i
    have hx : dividedLoweringWord highest d ∈ weightSpace R vQ _ μ := by
      have h := dividedLoweringWord_mem_weight highest d
      dsimp only [d] at h
      rw [expand_coevaluationDividedWord] at h
      exact h
    have hbot := quantum_weightSpace_raise_extremal_eq_bot P hR highest.1 weight hdom hm g β hcontent i hnd
    have he := E_smul_mem_weightSpace hx i
    change _ ∈ weightSpace R vQ _ (highest.1 - R.rootSum β + R.root i) at he
    rw [hbot, Submodule.mem_bot] at he
    have hn : 0 ≤ (Dc).coroot i η := by
      have ha := Matrix.Realization.apply_coroot_nonneg_of_not_isLeftDescent hdom hnd
      have ht := rootSum_coevaluationWord Dc weight w
        (nonnegativeReflectionPath_of_reduced P hCartan weight hdom w hpre)
      have hc := congrArg (fun z : P.integralWeights => (z : Dual K H)) ht
      rw [P.coe_rootSum_cartanDatum hCartan] at hc
      have hg : (η : Dual K H) = g.val weight := by
        change P.rootOf (fun j => (β j : ℤ)) = (weight : Dual K H) - (η : Dual K H) at hc
        rw [hc, sub_sub_cancel] at hcontent
        exact hcontent
      exact_mod_cast (show (0 : K) ≤ (((Dc).coroot i η : ℤ) : K) by rwa [P.coroot_cartanDatum_cast, hg])
    rw [coevaluationDividedWord_snoc, loweringWord_snoc,
      SingleBlack.websterForm_saturated_dividedPower highest hR i _ μ _ hx
        (hpair.trans (Int.toNat_of_nonneg hn).symm) he (bar_dividedLoweringWord highest hR d)]
    exact ih hpre

end Categorification.Stendhal


namespace Categorification.KLR.CycKLR
open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot

variable {I k : Type*} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "dp" => dividedProjective hP.gradingDatum (fun i j => congrArg Neg.neg (C.symm i j)) C Λ

include hΛ hR in
/-- Webster, Proposition 7.2. The actual divided-power projective attached to a reduced
coevaluation path in the cyclotomic factor is simple after forgetting the grading. -/
theorem isSimple_coevaluationProjective
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [Module.Finite K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
        (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse) :
    let d := Stendhal.coevaluationDividedWord (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
    IsSimpleModule (CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ i) (expandDiv d : Multiset I))
      (dp (expandDiv d : Multiset I) d rfl).carrier := by
  apply isSimple_coevaluationProjective_of_websterNorm hP Λ RD highest hΛ hR P weight hweight match_weight w hw
  exact Stendhal.websterForm_coevaluationDividedWord P (dominantWeight Λ RD highest hΛ)
    hR weight hweight match_weight w hw

end Categorification.KLR.CycKLR
