/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedFrobenius
import Categorification.KLR.CyclotomicRationalAction
import Categorification.Algebra.Graded.Duality
import Categorification.KLR.CyclotomicGradedCharacter
import Categorification.KLR.Prop31G0
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Strings

/-!
# Cyclotomic dimensions for repeated strands of a single colour

Hu–Shi, arXiv:2108.05508v5, Theorem 1.1 and (3.16). In content `n αᵢ`
there is one sequence, so its diagonal corner is the entire algebra.
Normalized restriction of the ordinary induction word has coefficient
`[n]ᵢ [Λᵢ-n+1]ᵢ`. Raw restriction also has the grading shift from
Kang–Kashiwara, arXiv:1102.4677v4, §6.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot KLGamma
open LieLean.QuantumGroup

local notation "LP" => LaurentPolynomial ℤ
local notation "T" => LaurentPolynomial.T (R := ℤ)
/-- The Laurent quantum integer specializes at the grading-shift parameter. -/
theorem qIntU_eval {d : ℤ} (hd : 0 < d) (n : ℤ) :
    qToV (qIntU (qUnitLP ^ d) n) = qIntZ (projectiveParameter ^ d) n := by
  let v := projectiveParameter ^ d
  have hv : v ≠ 0 := zpow_ne_zero _ (Units.ne_zero (vQ⁻¹ : (RatFunc ℚ)ˣ))
  have hpow : ∀ j : ℕ, 0 < j → v ^ j ≠ 1 := by
    intro j hj
    change (projectiveParameter ^ d) ^ j ≠ 1
    rw [← zpow_natCast (_ ^ d), ← zpow_mul]
    exact zpow_ne_one_of_pow_ne_one parameter_pow_ne_one (ne_of_gt (mul_pos hd (by exact_mod_cast hj)))
  have hs := sub_inv_ne_zero_of_pow_ne_one hv hpow
  have h := sub_mul_map_qIntU (qUnitLP ^ d) qToV n
  rw [val_qUnitLP_zpow,parameter_eval_T] at h
  change qToV _ = (_ - _) / (v - v⁻¹)
  rw [eq_div_iff hs,mul_comm]
  exact h

private theorem qIntU_step {d : ℤ} (hd : 0 < d) (m : ℤ) (b : ℕ) :
    qIntU (qUnitLP ^ d) (b+1) * qIntU (qUnitLP ^ d) (m-b) + qIntU (qUnitLP ^ d) (m-2*b-2) =
      qIntU (qUnitLP ^ d) (b+2) * qIntU (qUnitLP ^ d) (m-b-1) := by
  apply qToV_injective
  simp only [map_add,map_mul,qIntU_eval hd]
  exact qIntZ_succ_mul_add (zpow_ne_zero _ (Units.ne_zero (vQ⁻¹ : (RatFunc ℚ)ˣ))) m b

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X) (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (hdot : G.degX i = 2 * di C i)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "u" => (qUnitLP ^ di C i)
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))
local notation "E" => raise G Λ i hsym hQ C
local notation "lowering" => lower G Λ i

/-- The black content for `n` repeated strands, recursively in induction order. -/
def repeatedContent (i : I) : ℕ → Multiset I
  | 0 => 0
  | n+1 => {i} + repeatedContent i n

omit [DecidableEq I] in
theorem repeatedContent_eq_replicate (n : ℕ) : repeatedContent i n = Multiset.replicate n i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatedContent,ih,Multiset.replicate_succ, Multiset.singleton_add]

/-- Inducing the vacuum `n` times in colour `i`, as an integral weight-block class. -/
def repeatedInduction : (n : ℕ) → K0 (grade G Λ (repeatedContent i n))
  | 0 => K0.of (GProj.regular (grade G Λ 0))
  | n+1 => indK0 G Λ i _ (repeatedInduction n)

omit [DecidableEq I] in
include hΛ in
private theorem repeated_pair (n : ℕ) : RD.pair (RD.iY i)
    (highest - ((repeatedContent i n).map RD.iX).sum) = Λ i - 2*(n : ℤ) := by
  have hsum : RD.pair (RD.iY i) ((repeatedContent i n).map RD.iX).sum = 2*(n : ℤ) := by
    induction n with
    | zero => simp [repeatedContent]
    | succ n ih =>
      simp only [repeatedContent,Multiset.map_add,Multiset.map_singleton,Multiset.sum_add,
        Multiset.sum_singleton,map_add,RD.pair_iY_iX_self,ih,Nat.cast_succ]
      ring
  rw [map_sub,← hΛ,hsum]

local notation "W" => repeatedInduction G Λ i
local notation "β" => repeatedContent i

private theorem lower_repeated (n : ℕ) :
    lowering (ι (β n) (W n)) = ι (β (n+1)) (W (n+1)) := lower_lof ..

include hΛ hdeg hdot in
/-- Integral action of normalized restriction on the repeated-colour word. -/
theorem raise_repeatedInduction (n : ℕ) :
    E (ι (β (n+1)) (W (n+1))) =
      (qIntU u ((n : ℤ)+1) * qIntU u ((Λ i : ℤ)-n)) • ι (β n) (W n) := by
  have hc (r : ℕ) := raise_lower_sub_lower_raise G Λ i (β r) hsym hQ RD highest hΛ hdeg hdot (W r)
  simp_rw [repeated_pair Λ i RD highest hΛ] at hc
  induction n with
  | zero =>
    have h := hc 0
    rw [lower_repeated, raise_lof_of_notMem (ν := β 0) (h := by simp [repeatedContent]), map_zero,
      sub_zero] at h
    simpa [qIntU, qNatU] using h
  | succ n ih =>
    have h := hc (n+1)
    rw [lower_repeated, ih, map_smul, lower_repeated] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h,add_comm,← add_smul]
    congr 1
    push_cast
    have h := qIntU_step (di_pos C i) (Λ i) n
    convert h using 1 <;> congr 2 <;> omega

/-- The raw restriction coefficient for adding strand `r+1` to a pure string. -/
def repeatedFactor (r : ℕ) : LP :=
  T (-raiseShift Λ i (β r) C) *
    (qIntU u ((r : ℤ)+1) * qIntU u ((Λ i : ℤ)-r))

include hΛ hdeg hdot in
theorem res_repeatedInduction (r : ℕ) :
    resK0 G Λ i (β r) hsym hQ (W (r+1)) = repeatedFactor Λ i (C := C) r • W r := by
  have h := raise_repeatedInduction G Λ i hsym hQ RD highest hΛ hdeg hdot r
  have hr := raise_lof G Λ i (β r) hsym hQ C (W (r+1))
  have h := hr.symm.trans h
  rw [← map_smul] at h
  have he := congrArg (fun z : projectiveK0 G Λ => z (β r)) h
  simp only [DirectSum.lof_apply] at he
  change T _ • resK0 G Λ i (β r) hsym hQ (W (r+1)) = _ at he
  rw [repeatedFactor,mul_smul,← he,smul_smul,← LaurentPolynomial.T_add,neg_add_cancel,
    LaurentPolynomial.T_zero,one_smul]

omit [DecidableEq I] in
private theorem repeated_mem (n : ℕ) : ∀ j ∈ β n, j = i := by
  induction n with
  | zero => simp [repeatedContent]
  | succ n ih => simpa [repeatedContent] using ih

private theorem lastIdem_eq_one (n : ℕ) :
    lastIdem Q i (fun j => (Polynomial.X : Polynomial k) ^ Λ j) (β n) = 1 := by
  let := Seq.uniqueOfForall (repeated_mem i n)
  let : Unique (Seq (Si + β n)) := Seq.uniqueOfForall (repeated_mem i (n+1))
  rw [lastIdem,AbsentColour.cyclotomicLast_one,cL_one,Fintype.sum_unique,e_eq_one,map_one]

/-- Because there is only one word of pure content, ordinary iterated induction
of the vacuum is the left regular projective of the pure cyclotomic block. -/
theorem repeatedInduction_eq_regular (n : ℕ) :
    W n = K0.of (GProj.regular (grade G Λ (β n))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change indK0 G Λ i (β n) (W n) = _
    rw [ih,indK0_regular]
    exact (K0.of_ofIdempotent_congr (lastIdem_eq_one (Q := Q) Λ i n) _ IsIdempotentElem.one _
      SetLike.GradedOne.one_mem).trans (K0.of_eq_of_iso GProj.ofIdempotentOneIso)

include hQ in
private theorem repeated_finite (n : ℕ) :
    Module.Finite k (CycKLR k Q (fun j => (Polynomial.X : Polynomial k)^Λ j) (β n)) :=
  module_finite (fun a b hab => by
    obtain ⟨c,hc,he⟩ := hQ a b hab
    rw [he]
    exact hc.map Polynomial.C) (fun _ => Polynomial.monic_X_pow _)

private def regularHomEquiv {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
    [GradedAlgebra 𝒜] (d : ℤ) : homGrade A 𝒜 𝒜 d ≃ₗ[k] 𝒜 d where
  toFun f := ⟨f.1 1, by simpa using (mem_homGrade.mp f.2) (SetLike.one_mem_graded 𝒜)⟩
  invFun a := ⟨LinearMap.toSpanSingleton A A a, mem_homGrade.mpr fun j x hx => by
    change x * (a : A) ∈ 𝒜 (j + d)
    exact SetLike.GradedMul.mul_mem hx a.2⟩
  left_inv f := Subtype.ext (LinearMap.ext fun r => by
    change r • f.1 1 = f.1 r
    rw [← map_smul]
    exact congrArg f.1 (mul_one r))
  right_inv a := Subtype.ext (one_smul A (a : A))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The regular projective Euler norm recovers the graded dimension of the
whole pure block. -/
theorem homForm_repeatedInduction (n : ℕ) [HasGdim (grade G Λ (β n))] :
    K0.homForm (grade G Λ (β n)) (W n) (W n) = gdim (grade G Λ (β n)) := by
  rw [repeatedInduction_eq_regular,K0.homForm_of]
  exact gdim_eq_of_finrank_eq fun d => (regularHomEquiv (grade G Λ (β n)) d).finrank_eq

include hsym hQ hΛ hdeg hdot in
private theorem repeated_gdim_succ (n : ℕ) :
    gdim (grade G Λ (β (n+1))) =
      toLaurentSeries (repeatedFactor Λ i (C := C) n) * gdim (grade G Λ (β n)) := by
  let := repeated_finite Λ i hQ n
  let := repeated_finite Λ i hQ (n+1)
  let := HasGdim.of_finiteDimensional (grade G Λ (β n))
  let hn := HasGdim.of_finiteDimensional (grade G Λ (β (n+1)))
  let : HasGdim (grade G Λ (Si + β n)) := hn
  rw [←homForm_repeatedInduction G Λ i (n+1), ←homForm_repeatedInduction G Λ i n]
  change K0.homForm (grade G Λ (Si + β n)) (indK0 G Λ i (β n) (W n)) (W (n+1)) = _
  rw [homForm_ind_res G Λ i (β n) hsym hQ (W n) (W (n+1)),
    res_repeatedInduction G Λ i hsym hQ RD highest hΛ hdeg hdot]
  exact K0.map_smul_of_T (F := K0.homForm (grade G Λ (β n)) (W n))
    (fun a x => K0.homForm_T_smul_right a (W n) x) _ _

omit [DecidableEq I] in
private theorem repeatedFactor_eq (r : ℕ) :
    repeatedFactor Λ i (C := C) r = T (di C i * ((Λ i : ℤ)-2*r-1)) *
      (qIntU u ((r : ℤ)+1) * qIntU u ((Λ i : ℤ)-r)) := by
  have hsum : ((β r).map (A C i)).sum = 2 * (r : ℤ) := by
    induction r with
    | zero => simp [repeatedContent]
    | succ n ih =>
      simp only [repeatedContent,Multiset.map_add,Multiset.map_singleton,Multiset.sum_add,
        Multiset.sum_singleton,A_self,ih,Nat.cast_succ]
      ring
  rw [repeatedFactor,raiseShift,hsum]
  congr 2
  ring

include hsym hQ hΛ hdeg hdot in
/-- Hu–Shi's pure-colour graded dimension formula (arXiv:2108.05508v5,
Theorems 1.1 and 3.17). The `r`th factor contributes the grade shift
`dᵢ(Λᵢ-2r-1)` and the two quantum integers `[r+1]ᵢ [Λᵢ-r]ᵢ`.
It applies to every multiplicity, including the zero algebra above level. -/
theorem gdimPoly_repeated (n : ℕ) :
    gdimPoly (grade G Λ (β n)) = ∏ r ∈ Finset.range n,
      T (di C i * ((Λ i : ℤ)-2*r-1)) *
        (qIntU u ((r : ℤ)+1) * qIntU u ((Λ i : ℤ)-r)) := by
  let := repeated_finite Λ i hQ n
  apply toLaurentSeries_injective
  rw [toLaurentSeries_gdimPoly]
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, ←LaurentPolynomial.T_zero, K0.toLaurentSeries_T]
    ext d
    let := repeated_finite Λ i hQ 0
    let := HasGdim.of_finiteDimensional (grade G Λ (β 0))
    rw [coeff_gdim]
    change (Module.finrank k (grade G Λ 0 d) : ℤ) = _
    rw [finrank_emptyGrade,HahnSeries.coeff_single]
    split_ifs <;> simp_all
  | succ n ih =>
    rw [repeated_gdim_succ G Λ i hsym hQ RD highest hΛ hdeg hdot,Finset.prod_range_succ,
      toLaurentSeries_mul, ←repeatedFactor_eq, mul_comm]
    rw [← ih]

end Categorification.KLR.CycKLR
