/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicTopTests
import Categorification.WeightedKLR.RedStrands.SingleRedEulerForm

set_option backward.isDefEq.respectTransparency false

/-!
# Word characters of cyclotomic word projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.4,
Corollary 3.22, used in the proof of Proposition 5.6. For the cyclotomic projective
`R^λ e(u)` of an ordinary word `u`, the graded dimension of its loading space at another
ordinary word `s` is Webster's form `⟨F_u v_λ, F_s v_λ⟩`. The form vanishes when the black
contents of `u` and `s` differ, since the two vectors then have different weights.

## Main results

* `cyclotomicWordModule_word`: the word character of `R^λ e(u)`.
* `websterForm_suffix_eq_zero`: orthogonality of ordinary lowering words of different content.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra QuantumGroup QuantumGroup.UDot Categorification.Graded GProj
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF KLGamma
open scoped TensorProduct RatFunc

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private local instance cyclotomicWordX_neZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
attribute [local instance] KLGamma.qToVAlgebra
local notation "series" => algebraMap L (LaurentSeries ℚ)

variable {I : Type} [DecidableEq I] [Finite I] {k Y : Type*} [Field k] [AddCommGroup Y]
    (C : CartanDatum I) {Q : I → I → MvPolynomial (Fin 2) k} (μ : I →₀ ℕ)
    (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} (wt : Dom R)
    (hwt : ∀ i, (μ i : ℤ) = wt.1 (R.coroot i)) (hR : R.IsXRegular)
local notation "G" => hQ.gradingDatum
local notation "D" => CycKLR.grade G μ
local notation "V" => IrreducibleModule R v (Subtype.val wt)
local notation "act" => fun i => Algebra.lsmul L L V (F R v i)
local notation "highest" => IrreducibleModule.hwv R v (Subtype.val wt)
local notation "π" => CycKLR.mk k Q (fun i => (Polynomial.X : Polynomial k) ^ μ i)
local notation "B" => SingleBlack.websterForm wt hR

omit [Finite I] in
/-- An ordinary lowering word lowers the weight by the roots of its letters. -/
theorem ordinarySuffixOp_mem_weightSpace (s : List I) {Λ : Y →+ ℤ} {x : V}
    (hx : x ∈ weightSpace R v V Λ) :
    ordinarySuffixOp act s x ∈
      weightSpace R v V (Λ - R.rootSum (s : Multiset I).toFinsupp) := by
  induction s generalizing Λ x with
  | nil => simpa [ordinarySuffixOp] using hx
  | cons i s ih =>
    have h := ih (F_smul_mem_weightSpace hx i)
    have he : Λ - R.root i - R.rootSum (s : Multiset I).toFinsupp =
        Λ - R.rootSum ((i :: s : List I) : Multiset I).toFinsupp := by
      rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton, R.rootSum_add, R.rootSum_single, one_smul,
        sub_add_eq_sub_sub]
    rw [he] at h
    exact h

/-- Webster's form vanishes on vectors of different weights. -/
theorem websterForm_eq_zero_of_weight_ne {Λ Λ' : Y →+ ℤ} (h : Λ ≠ Λ') {x y : V}
    (hx : x ∈ weightSpace R v V Λ) (hy : y ∈ weightSpace R v V Λ') : B x y = 0 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp h
  have ht := SingleBlack.websterForm_adjoint wt hR (LieLean.QuantumGroup.K R v a) x y
  simp only [rho_K, barHom_K] at ht
  rw [hx a, hy (-a), SingleBlack.websterForm_smul_left, SingleBlack.websterForm_smul_right,
    map_zpow₀, show RatFunc.bar v = v⁻¹ from RatFunc.bar_X, inv_zpow', map_neg] at ht
  by_contra hn
  exact ha (neg_injective (zpow_injective_of_not_root RatFunc.X_ne_zero hvn_ratFunc
    (mul_right_cancel₀ hn ht)))

/-- Ordinary lowering words of different black contents are orthogonal for Webster's form. -/
theorem websterForm_suffix_eq_zero (u s : List I) (h : (s : Multiset I) ≠ u) :
    B (ordinarySuffixOp act u highest) (ordinarySuffixOp act s highest) = 0 := by
  have hv := (IrreducibleModule.hwv_mem_weightSpace (R := R) (Λ := wt.1) :
    highest ∈ weightSpace R v V wt.1)
  refine websterForm_eq_zero_of_weight_ne C wt hR (fun he => h ?_)
    (ordinarySuffixOp_mem_weightSpace C wt u hv) (ordinarySuffixOp_mem_weightSpace C wt s hv)
  have := R.rootSum_injective hR (sub_right_injective he)
  simpa using congrArg Finsupp.toMultiset this.symm

/-- Webster's form with a fixed first vector, as a linear functional. -/
def websterFormRight (x : V) : V →ₗ[L] L where
  toFun := B x
  map_add' y y' := by
    simp only [SingleBlack.websterForm, map_add]
  map_smul' c y := SingleBlack.websterForm_smul_right wt hR c x y


private theorem expand_integralEval (p : LP) :
    lsCast (toLaurentSeries p) = series (integralLaurentEval p) := by
  rw [lsCast_toLaurentSeries, vToLS, RingHom.comp_apply, barQ_qToV, ← CycKLR.integralEval_invert]
  exact congrArg (fun t => series (integralLaurentEval t))
    (LaurentPolynomial.invert.symm_apply_apply _)

/-- The cyclotomic word projective `R^λ e(u)` as a finite-dimensional graded module. -/
abbrev cyclotomicWordModule {γ : Multiset I} (u : Seq γ) : GFin (D γ) :=
  let := lastRedFinal_finite hQ μ γ
  let := Module.Finite.trans (R := k)
    (A := CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ μ i) γ)
    (M := (cyclotomicWordProjective C μ hQ u).carrier)
  { toGMod := (cyclotomicWordProjective C μ hQ u).toGMod }

private local instance cyclotomicWordGdim (γ : Multiset I) : HasGdim (D γ) := by
  let := lastRedFinal_finite hQ μ γ
  exact HasGdim.of_finiteDimensional _

include hwt in
/-- **Word character of a cyclotomic word projective** (Webster, arXiv:1309.3796v2, §3.4,
Corollary 3.22). The graded dimension of `e(s) R^λ e(u)` at the indeterminate is Webster's form
`⟨F_u v_λ, F_s v_λ⟩`. -/
theorem cyclotomicWordModule_word (u s : List I) {γ : Multiset I}
    (hu : (u : Multiset I) = γ) (hs : (s : Multiset I) = γ) :
    integralLaurentEval (gdimPoly (Graded.idem
      (cyclotomicWordModule C μ hQ (Seq.ofList u hu)).grading (π γ (e (Seq.ofList s hs))))) =
      B (ordinarySuffixOp act u highest) (ordinarySuffixOp act s highest) := by
  let := lastRedFinal_finite hQ μ γ
  let Pu := cyclotomicWordProjective C μ hQ (Seq.ofList u hu)
  let Ps := cyclotomicWordProjective C μ hQ (Seq.ofList s hs)
  have h1 := projectiveHomPolynomial_ofIdempotent (D γ)
    (cyclotomicWordModule C μ hQ (Seq.ofList u hu))
    ((show IsIdempotentElem (e (Q := Q) (Seq.ofList s hs)) from e_mul_self _).map (π γ))
    (Graded.mem_map_of_mem _ (π γ).toLinearMap ((G).e_mem_grade _))
  rw [← h1]
  have h2 := projectiveHomPolynomial_of (D γ) (cyclotomicWordModule C μ hQ (Seq.ofList u hu)) Ps
  erw [h2]
  have h3 := CycKLR.homForm_eq_websterForm hQ μ (cyclotomicWeightDatum C (R := R)) wt.1 hwt hR γ
    (K0.of Ps) (K0.of Pu)
  rw [K0.homForm_of, ← GProj.toLaurentSeries_homGdimPoly (D γ) Ps Pu, expand_integralEval] at h3
  have hu' := cyclotomicWord_image C μ hQ wt hwt hR u
  have hs' := cyclotomicWord_image C μ hQ wt hwt hR s
  rw [cyclotomicSequenceClass_at C μ hQ u hu] at hu'
  rw [cyclotomicSequenceClass_at C μ hQ s hs] at hs'
  rw [← hu', ← hs']
  exact (algebraMap L (LaurentSeries ℚ)).injective h3

end Categorification.Stendhal.FirstWeight
