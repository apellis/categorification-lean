/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ReducedDividedNorm
import Categorification.WeightedKLR.Rigidity.RigidityExtLowest
import Categorification.WeightedKLR.Rigidity.CoevaluationDualWord

/-!
# The lowest weight vector `v_l` and the dual weight `μ* = -w₀μ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1: for a
reduced expression `w` of the longest element `w₀`, the class of the extremal projective
`P⁰_{i^μ}` (Definition 7.1, Proposition 7.2) is the divided lowering word
`v_l = F_{i_k}^{(a_k)} ⋯ F_{i_1}^{(a_1)} v_h` of `V_μ`; Webster fixes this lowest weight vector
to normalize the pairing of `V_μ` with `V_{μ*}`.

Here (`w` given as in `Stendhal.subsingleton_of_isLeftDescent_coevaluationWord`, with `w.reverse`
reduced and every simple reflection a left descent of its product):

* `lowestVector`: `v_l`, of weight `μ - Σ β_j α_j = w₀μ` for the content `β = lowestContent` of the
  coevaluation word (`lowestVector_mem_weightSpace`);
* `F_smul_lowestVector`: `Fᵢ v_l = 0` for every `i` (Lemma 7.3 input
  `Stendhal.quantum_weightSpace_lower_extremal_eq_bot`);
* `form_lowestVector`: `(v_l, v_l) = 1` for Lusztig's contravariant form (from
  `Stendhal.websterForm_coevaluationDividedWord`);
* `dualWeight`: the dominant weight `μ* = Σ β_j α_j - μ = -w₀μ` (`dualWeight_coroot`).
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan
local notation "cs" => P.coxeterSystem hCartan

/-- The content `β` of the coevaluation word of `w`: `w₀μ = μ - Σ β_j α_j`. -/
def lowestContent (weight : P.integralWeights) (w : List I) : I →₀ ℕ :=
  (coevaluationWord Dc weight w : Multiset I).toFinsupp

/-- Webster's lowest weight vector `v_l = [P⁰_{i^μ}]` of `V_μ` (§7.1, after Proposition 7.2):
the divided lowering word of the reduced expression `w` of `w₀`. -/
def lowestVector (μ : Dom R) (weight : P.integralWeights) (w : List I) :
    IrreducibleModule R vQ μ.1 :=
  dividedLoweringWord μ (coevaluationDividedWord Dc weight w)

omit [Fintype I] in
open KLR.KLRAlgebra in
private theorem dividedLoweringWord_mem (μ : Dom R) (d : List (I × ℕ)) :
    dividedLoweringWord μ d ∈ weightSpace R vQ _
      (μ.1 - R.rootSum (expandDiv d : Multiset I).toFinsupp) := by
  induction d using List.reverseRecOn with
  | nil =>
    simpa [expandDiv, dividedLoweringWord] using
      (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := vQ) (Λ := μ.1))
  | append_singleton d a ih =>
    rcases a with ⟨i, n⟩
    have hν : (List.replicate n i : Multiset I).toFinsupp = Finsupp.single i n := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    have hex : expandDiv [(i, n)] = List.replicate n i := by simp [expandDiv]
    have hs : dividedLoweringWord μ (d ++ [(i, n)]) =
        qDivPow (vQ ^ Δ.d i) n (F R vQ i) • dividedLoweringWord μ d := by
      simp [dividedLoweringWord, List.foldl_append]
    rw [hs, Categorification.KLR.expandDiv_append, hex, ← Multiset.coe_add,
      Multiset.toFinsupp_add, R.rootSum_add, hν, R.rootSum_single, ← sub_sub]
    exact qDivPow_F_smul_mem_weightSpace ih i n

/-- `v_l` has weight `μ - Σ β_j α_j`. -/
theorem lowestVector_mem_weightSpace (μ : Dom R) (weight : P.integralWeights) (w : List I) :
    lowestVector P μ weight w ∈
      weightSpace R vQ _ (μ.1 - R.rootSum (lowestContent P weight w)) := by
  have h := dividedLoweringWord_mem μ (coevaluationDividedWord Dc weight w)
  rwa [expand_coevaluationDividedWord] at h

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

include hR hdom hm hw hlong in
/-- **`v_l` is a lowest weight vector**: `Fᵢ v_l = 0` for all `i`. -/
theorem F_smul_lowestVector (i : I) : F R vQ i • lowestVector P μ weight w = 0 := by
  have hx := F_smul_mem_weightSpace (R := R) (v := vQ)
    (lowestVector_mem_weightSpace P μ weight w) i
  have hβ : (weight : Dual K H) - P.rootOf (fun j => (lowestContent P weight w j : ℤ)) =
      ((cs).wordProd w.reverse).val weight := by
    have h := rootSum_coevaluationWord_of_reduced P hCartan weight hdom w hw
    rw [P.coe_rootSum_cartanDatum hCartan] at h
    change P.rootOf (fun j => (lowestContent P weight w j : ℤ)) = _ at h
    rw [h, sub_sub_cancel]
  have hbot := quantum_weightSpace_lower_extremal_eq_bot P hR μ.1 (weight : Dual K H) hdom hm
    _ (lowestContent P weight w) hβ i (hlong i)
  have he : μ.1 - R.rootSum (lowestContent P weight w) - R.root i =
      μ.1 - R.rootSum (lowestContent P weight w + Finsupp.single i 1) := by
    rw [R.rootSum_add, R.rootSum_single, one_smul, sub_sub]
  rw [he, hbot, Submodule.mem_bot] at hx
  exact hx

include hdom hm hw in
/-- **Normalization of `v_l`**: `(v_l, v_l) = 1` for Lusztig's contravariant form on `V_μ`. -/
theorem form_lowestVector :
    IrreducibleModule.form μ.1 hR hvn_ratFunc (lowestVector P μ weight w)
      (lowestVector P μ weight w) = 1 := by
  have h := websterForm_coevaluationDividedWord P μ hR weight hdom hm w hw
  have hb := bar_dividedLoweringWord μ hR (coevaluationDividedWord Dc weight w)
  rw [SingleBlack.websterForm, hb] at h
  have h' := congrArg RatFunc.bar h
  rwa [RatFunc.bar_bar, map_one] at h'

include hdom hm hw in
omit [FiniteDimensional K H] in
/-- The coroot pairings of the dual weight: `⟨i, Σ β_j α_j - μ⟩ = -⟨i, w₀μ⟩`. -/
theorem lowestContent_sub_coroot (i : I) :
    (R.rootSum (lowestContent P weight w) - μ.1) (R.coroot i) =
      -((Dc).coroot i (w.foldl (fun x j => (Dc).reflection j x) weight)) := by
  have h := coevaluation_endpoint_pairing R P μ.1 weight hm w
    (nonnegativeReflectionPath_of_reduced P hCartan weight hdom w hw) i
  change (μ.1 - R.rootSum (lowestContent P weight w)) (R.coroot i) = _ at h
  rw [← h, ← neg_sub, AddMonoidHom.neg_apply]

include hdom hm hw hlong in
omit [FiniteDimensional K H] in
theorem dualWeight_nonneg (i : I) :
    0 ≤ (R.rootSum (lowestContent P weight w) - μ.1) (R.coroot i) := by
  rw [lowestContent_sub_coroot P μ weight hdom hm w hw i]
  have h := apply_coroot_nonpos_of_isLeftDescent hdom (hlong i)
  rw [← coe_foldl_reflection_cartanDatum P hCartan, ← P.coroot_cartanDatum_cast hCartan] at h
  have : (Dc).coroot i (w.foldl (fun x j => (Dc).reflection j x) weight) ≤ 0 := by
    exact_mod_cast h
  omega

include hdom hm hw hlong in
/-- **The dual weight** `μ* = -w₀μ = Σ β_j α_j - μ` (Webster §7.1), dominant. -/
def dualWeight : Dom R :=
  ⟨R.rootSum (lowestContent P weight w) - μ.1, dualWeight_nonneg P μ weight hdom hm w hw hlong⟩

omit [FiniteDimensional K H] in
theorem dualWeight_val :
    (dualWeight P μ weight hdom hm w hw hlong).1 = R.rootSum (lowestContent P weight w) - μ.1 :=
  rfl

omit [FiniteDimensional K H] in
/-- `v_l` has weight `-μ*`. -/
theorem lowestVector_mem_weightSpace_neg :
    lowestVector P μ weight w ∈
      weightSpace R vQ _ (-(dualWeight P μ weight hdom hm w hw hlong).1) := by
  rw [dualWeight_val, neg_sub]
  exact lowestVector_mem_weightSpace P μ weight w

include hR hdom hm hw in
theorem lowestVector_ne_zero : lowestVector P μ weight w ≠ 0 := by
  intro h
  have := form_lowestVector P hR μ weight hdom hm w hw
  simp only [h, map_zero] at this
  exact zero_ne_one this

end Categorification.Stendhal.QuantumDual
