/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicHighestWeight
import Categorification.KLR.K0Free
import Categorification.QuantumGroup.GabberKacBridge
import Categorification.KLR.Rouquier.PolynomialDegree
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightIntegral

/-!
# Divided induction words and the integral highest-weight lattice

Kang–Kashiwara, arXiv:1102.4677v4, §6, Theorem 6.2 and Webster,
arXiv:1309.3796v2, §3.4, Proposition 3.21. The divided projective classes
correspond to products of divided lowering operators applied to the highest
vector. The grading shift acts by the inverse of the quantum-group variable.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot KLGamma LieLean
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

section Words
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} (wt : Dom R)
local notation "V" => IrreducibleModule R v (Subtype.val wt)

/-- Successive divided powers of the lowering generators on the highest vector,
in order of induction from left to right along the word. -/
def dividedLoweringWord (d : List (I × ℕ)) : V :=
  d.foldl (fun x a => qDivPow (v ^ D.d a.1) a.2 (F R v a.1) • x)
    (IrreducibleModule.hwv R v wt.1)

omit [Finite I] in
private theorem dividedLoweringWord_snoc (d : List (I × ℕ)) (i : I) (n : ℕ) :
    dividedLoweringWord wt (d ++ [(i,n)]) =
      qDivPow (v ^ D.d i) n (F R v i) • dividedLoweringWord wt d := by
  simp [dividedLoweringWord, List.foldl_append]

/-- The divided lowering words span Kashiwara's integral form
([Kas91], (6.1.12)), the target lattice of Webster, Proposition 3.21. -/
theorem span_dividedLoweringWord : Submodule.span LP (Set.range (dividedLoweringWord wt)) =
    hwIntegral wt := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    induction d using List.reverseRecOn with
    | nil => exact hwv_mem_hwIntegral wt
    | append_singleton d a ih =>
      rw [dividedLoweringWord_snoc]
      exact dF_smul_mem_hwIntegral wt _ _ ih
  rintro m ⟨x, hx, rfl⟩
  have hy : negativeQuotientEquiv D x ∈ Subalgebra.toSubmodule (quotientIntegralForm D) :=
    (mem_negIntegral D x).1 hx
  rw [quotientIntegralForm, Algebra.adjoin_eq_span] at hy
  rw [← (negativeQuotientEquiv D).symm_apply_apply x]
  generalize negativeQuotientEquiv D x = y at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    apply Submodule.subset_span
    induction hy using Submonoid.closure_induction_left with
    | one =>
      refine ⟨[], ?_⟩
      rw [← map_one (toQuotient D v), symm_toQuotient, evq_mk, ev_one]
      rfl
    | mul_left a ha y _ ih =>
      obtain ⟨d, hd⟩ := ih
      obtain ⟨i,n,rfl⟩ := ha
      refine ⟨d ++ [(i,n)], ?_⟩
      obtain ⟨z, rfl⟩ := toQuotient_surjective D v y
      rw [dividedLoweringWord_snoc, hd, ← toQuotient_qDivPow, ← map_mul, symm_toQuotient,
        symm_toQuotient, evq_mk, evq_mk, ev_qDivPow_mul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    change evq transcendental_ratFunc_X wt
      ((negativeQuotientEquiv D).symm (integralLaurentEval c • y)) ∈ _
    rw [map_smul, map_smul, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ _ hy

end Words

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
local notation "G" => hP.gradingDatum
local notation "P" => projectiveK0 G Λ
local notation "M" => L ⊗[LP] P

/-- The projective lattice embeds in its scalar extension by Laurent freeness
and injectivity of specialization at the inverse indeterminate. -/
theorem projectiveRationalization_injective :
    Function.Injective (TensorProduct.mk LP L P 1) := by
  have : Module.Free LP P := projectiveK0_free G Λ (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C)
  have : FaithfulSMul LP L := (faithfulSMul_iff_algebraMap_injective LP L).mpr qToV_injective
  exact Module.Flat.tensorProduct_mk_injective LP P L

private theorem rationalize_smul (c : LP) (x : P) :
    (1 : L) ⊗ₜ[LP] (c • x) = qToV c • ((1 : L) ⊗ₜ[LP] x) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    smul_eq_mul, mul_one]
  rfl

private theorem integralEval_invert (p : LP) :
    integralLaurentEval (LaurentPolynomial.invert p) = qToV p := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n a =>
    simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
      integralLaurentEval_T, qToV_T]
    congr 1
    have h (f : LP →+* L) : f (LaurentPolynomial.C a) = (a : L) :=
      DFunLike.congr_fun (RingHom.ext_int (f.comp LaurentPolynomial.C) (Int.castRingHom L)) a
    rw [h, h]
    exact (Units.val_zpow_eq_zpow_val vQ (-n)).symm

local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))

/-- The divided word as a class of the total integral projective group. -/
def dividedWordClass (d : List (I × ℕ)) : P :=
  ι (expandDiv d : Multiset I) (K0.of (dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j))
    C Λ _ d rfl))

private theorem span_dividedWordClass : Submodule.span LP (Set.range (dividedWordClass hP Λ)) = ⊤ := by
  apply top_unique
  rw [← span_total_dividedProjective C Λ hP]
  apply Submodule.span_le.mpr
  rintro _ ⟨β, d, rfl, rfl⟩
  exact Submodule.subset_span (Set.mem_range_self d)

private theorem lowerWordQ_factorial (d : List (I × ℕ)) :
    lowerWordQ hP Λ (expandDiv d) = qToV (KL2.divQFact2 C d) •
      ((1 : L) ⊗ₜ[LP] dividedWordClass hP Λ d) := by
  rw [lowerWordQ, word_eq_factorial hP Λ _ d rfl, rationalize_smul]
  rfl

private abbrev invertLP : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invertLP.toRingHom invertLP.toRingHom :=
  RingHomInvPair.of_ringEquiv invertLP

section Comparison
variable {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}
    (wt : Dom R)
local notation "V" => IrreducibleModule R v (Subtype.val wt)
local notation "B" => Module.End.baseChangeHom LP L P
variable (e : RatFunc ℚ ⊗[LaurentPolynomial ℤ] projectiveK0 hP.gradingDatum Λ
    ≃ₗ[RatFunc ℚ] IrreducibleModule R (RatFunc.X : RatFunc ℚ) wt.1)
variable (e₀ : e (lowerWordQ hP Λ []) = IrreducibleModule.hwv R (RatFunc.X : RatFunc ℚ) wt.1)
    (eF : ∀ i x, e (Module.End.baseChangeHom (LaurentPolynomial ℤ) (RatFunc ℚ)
      (projectiveK0 hP.gradingDatum Λ) (lower hP.gradingDatum Λ i) x) =
        F R (RatFunc.X : RatFunc ℚ) i • e x)

include eF in
private theorem lowerWordQ_replicate (w : List I) (i : I) (n : ℕ) :
    e (lowerWordQ hP Λ (w ++ List.replicate n i)) =
      F R v i ^ n • e (lowerWordQ hP Λ w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc, lowerWordQ_append, eF, ih, pow_succ', mul_smul]

include e₀ eF in
private theorem map_lowerWordQ_expanded (d : List (I × ℕ)) :
    e (lowerWordQ hP Λ (expandDiv d)) =
      qToV (KL2.divQFact2 C d) • dividedLoweringWord wt d := by
  induction d using List.reverseRecOn with
  | nil => simpa [expandDiv, KL2.divQFact2, dividedLoweringWord] using e₀
  | append_singleton d a ih =>
    obtain ⟨i,n⟩ := a
    rw [expandDiv_append, show expandDiv [(i,n)] = List.replicate n i by simp [expandDiv],
      lowerWordQ_replicate hP Λ wt e eF, ih, dividedLoweringWord_snoc, KL2.divQFact2_append,
      map_mul, smul_algebra_smul_comm, mul_smul]
    congr 1
    have hfac : qToV (KL2.divQFact2 C [(i,n)]) = qFactorial (v ^ C.toLusztig.d i) n := by
      rw [KL2Gamma.qToV_divQFact2]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← PreF.qFactorial_eq_qfact, PreF.val_vi]
      rfl
    rw [hfac, qDivPow, smul_assoc, smul_smul, mul_inv_cancel₀, one_smul]
    rw [← hfac]
    exact KL2Gamma.qToV_divQFact2_ne_zero C _

include e₀ eF in
private theorem map_dividedWordClass (d : List (I × ℕ)) :
    e ((1 : L) ⊗ₜ[LP] dividedWordClass hP Λ d) = dividedLoweringWord wt d := by
  have h := map_lowerWordQ_expanded hP Λ wt e e₀ eF d
  rw [lowerWordQ_factorial, map_smul] at h
  exact (smul_right_injective _ (KL2Gamma.qToV_divQFact2_ne_zero C d)) h

private def latticeMap : P →ₛₗ[invertLP.toRingHom] V where
  toFun x := e ((1 : L) ⊗ₜ[LP] x)
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]
  map_smul' c x := by
    rw [rationalize_smul, map_smul, hw_laurent_smul_eq]
    change _ = integralLaurentEval (LaurentPolynomial.invert c) • _
    rw [integralEval_invert]

variable [Finite I]

include e₀ eF in
private theorem range_latticeMap : LinearMap.range (latticeMap hP Λ wt e) = hwIntegral wt := by
  rw [← Submodule.map_top, ← span_dividedWordClass hP Λ, Submodule.map_span,
    ← span_dividedLoweringWord]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨d,rfl⟩, rfl⟩
    exact ⟨d,(map_dividedWordClass hP Λ wt e e₀ eF d).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨_, ⟨d,rfl⟩, map_dividedWordClass hP Λ wt e e₀ eF d⟩

end Comparison

section HighestWeight
variable [Finite I] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)
local notation "R" => projectiveRootDatum RD

/-- The dominant weight of the cyclotomic presentation. -/
def dominantWeight : Dom R :=
  ⟨RD.pair.flip highest, fun i => by
    change 0 ≤ RD.pair (RD.iY i) highest
    rw [← hΛ i]
    exact Nat.cast_nonneg _⟩

local notation "wt" => dominantWeight Λ RD highest hΛ
local notation "eQ" => projectiveHighestWeightEquiv Λ RD highest hΛ hP hR

/-- The integral highest-weight isomorphism on the full cyclotomic projective
Grothendieck group (Kang–Kashiwara, arXiv:1102.4677v4, Theorem 6.2; Webster,
arXiv:1309.3796v2, Proposition 3.21). Laurent inversion identifies the two
grading-shift conventions. -/
def projectiveIntegralEquiv : P ≃ₛₗ[invertLP.toRingHom] hwIntegral wt := by
  let f := latticeMap hP Λ wt eQ
  have hf : Function.Injective f :=
    (eQ).injective.comp (projectiveRationalization_injective hP Λ)
  have h₀ : eQ (lowerWordQ hP Λ []) = IrreducibleModule.hwv R v (RD.pair.flip highest) := by
    rw [lowerWordQ_nil]
    exact projectiveHighestWeightEquiv_vacuum Λ RD highest hΛ hP hR
  exact (LinearEquiv.ofInjective f hf).trans
    (LinearEquiv.ofEq _ _ (range_latticeMap hP Λ wt eQ h₀
      (projectiveHighestWeightEquiv_F Λ RD highest hΛ hP hR)))

/-- The integral comparison is the restriction of the rational representation
isomorphism under the injection into the scalar extension. -/
theorem projectiveIntegralEquiv_val (x : P) :
    (projectiveIntegralEquiv hP Λ RD highest hΛ hR x).val =
      eQ ((1 : L) ⊗ₜ[LP] x) := rfl

/-- A divided projective word is sent to the corresponding product of divided
lowering operators on the highest vector (Webster, proof of Proposition 3.21). -/
theorem projectiveIntegralEquiv_dividedWordClass (d : List (I × ℕ)) :
    (projectiveIntegralEquiv hP Λ RD highest hΛ hR (dividedWordClass hP Λ d)).val =
      dividedLoweringWord wt d := by
  rw [projectiveIntegralEquiv_val]
  refine map_dividedWordClass hP Λ wt eQ ?_ ?_ d
  · rw [lowerWordQ_nil]
    exact projectiveHighestWeightEquiv_vacuum Λ RD highest hΛ hP hR
  · exact projectiveHighestWeightEquiv_F Λ RD highest hΛ hP hR

/-- Graded induction acts by the Chevalley lowering generator under the
integral isomorphism of Kang–Kashiwara, Theorem 6.2. -/
theorem projectiveIntegralEquiv_lower (i : I) (x : P) :
    (projectiveIntegralEquiv hP Λ RD highest hΛ hR (lower G Λ i x)).val =
      F R v i • (projectiveIntegralEquiv hP Λ RD highest hΛ hR x).val :=
  projectiveHighestWeightEquiv_F Λ RD highest hΛ hP hR i ((1 : L) ⊗ₜ[LP] x)

/-- Normalized graded restriction acts by the Chevalley raising generator
under the integral isomorphism of Kang–Kashiwara, Theorem 6.2. -/
theorem projectiveIntegralEquiv_raise (i : I) (x : P) :
    (projectiveIntegralEquiv hP Λ RD highest hΛ hR (raise G Λ i hP.klrSymm hP.polyInY_leading C x)).val =
      E R v i • (projectiveIntegralEquiv hP Λ RD highest hΛ hR x).val := by
  have h := projectiveHighestWeightEquiv_action Λ RD highest hΛ hP hR (E R v i) ((1 : L) ⊗ₜ[LP] x)
  rw [projectiveRepresentationX_E] at h
  exact h

end HighestWeight

end Categorification.KLR.CycKLR
