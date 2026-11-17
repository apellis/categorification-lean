/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRepeatedDimension
import Categorification.KLR.CyclotomicDividedProjectives
import Categorification.KLR.KL2.Prop320KL2

/-!
# Quantum binomials in pure cyclotomic content

Hu–Shi, arXiv:2108.05508v5, Theorem 3.17 for one block of repeated labels.
The two ordinary-word quantum factorials are exactly the multiplicities of
the nilHecke divided projective on the two sides of its endomorphism space.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot KL2
open LieLean.QuantumGroup
local notation "LP" => LaurentPolynomial ℤ
local notation "T" => LaurentPolynomial.T (R := ℤ)

private abbrev regularProduct (h : ℤ) (m n : ℕ) : LP :=
  ∏ r ∈ Finset.range n, T (h * ((m : ℤ)-2*r-1)) *
    (qIntU (tUnit h) ((r : ℤ)+1) * qIntU (tUnit h) ((m : ℤ)-r))

private theorem fact_ne_zero (h : ℤ) (n : ℕ) : qfact (tUnit h) n ≠ 0 := by
  intro hz
  have hh := KL2Gamma.evalOne_qfact_tUnit h n
  rw [hz,map_zero] at hh
  exact Nat.factorial_ne_zero n (by exact_mod_cast hh.symm)

private theorem regularProduct_mul_fact (h : ℤ) (m n : ℕ) (hn : n ≤ m) :
    regularProduct h m n * qfact (tUnit h) (m-n) =
      T (h * n * ((m : ℤ)-n)) * qfact (tUnit h) n * qfact (tUnit h) m := by
  induction n with
  | zero => simp [regularProduct,qfact]
  | succ n ih =>
    have hn' : n ≤ m := by omega
    let u := tUnit h
    have hq₁ : qIntU u ((n : ℤ)+1) = qint u (n+1) := qNatU_eq_qint u (n+1)
    have hq₂ : qIntU u ((m : ℤ)-n) = qint u (m-n) := by
      rw [← Nat.cast_sub hn']
      exact qNatU_eq_qint u (m-n)
    have hf : qint u (m-n) * qfact u (m-(n+1)) = qfact u (m-n) := by
      have he : m-(n+1)+1 = m-n := by omega
      conv_rhs => rw [← he, qfact_succ,he]
      rw [mul_comm]
    rw [show regularProduct h m (n+1) = regularProduct h m n *
      (T (h*((m : ℤ)-2*n-1)) * (qint u (n+1) * qint u (m-n))) by
        simp only [regularProduct,Finset.prod_range_succ,hq₁,hq₂,u]]
    calc
      _ = (regularProduct h m n * (qint u (m-n) * qfact u (m-(n+1)))) *
          (T (h*((m : ℤ)-2*n-1)) * qint u (n+1)) := by ring
      _ = _ := by
        rw [hf,ih hn',qfact_succ,show h * (n+1 : ℕ) * ((m : ℤ)-(n+1 : ℕ)) =
            h * n * ((m : ℤ)-n) + h*((m : ℤ)-2*n-1) by push_cast;ring, LaurentPolynomial.T_add]
        dsimp [u]
        ring

/-- The product for the ordinary regular block is the square of the quantum
factorial times the shifted symmetric quantum binomial. -/
private theorem regularProduct_eq (h : ℤ) (m n : ℕ) :
    regularProduct h m n = qfact (tUnit h) n ^ 2 *
      (T (h*n*((m : ℤ)-n)) * qbinom (tUnit h) m n) := by
  let u := tUnit h
  by_cases hn : n ≤ m
  · apply mul_right_cancel₀ (fact_ne_zero h (m-n))
    rw [regularProduct_mul_fact h m n hn]
    have hb := qbinom_mul_qfact u (m-n) n
    rw [Nat.sub_add_cancel hn] at hb
    conv_lhs => rw [← hb]
    ring
  · have hlt : m < n := by omega
    rw [qbinom_eq_zero_of_lt _ hlt,mul_zero,mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hlt)
    simp [qIntU,qNatU]

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X) (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (hdot : G.degX i = 2 * di C i)

include hsym hQ hΛ hdeg hdot in
/-- For type A₁ content `n αᵢ`, the full cyclotomic algebra has graded
dimension `[n]!² qᵢ^(n(Λᵢ-n)) [Λᵢ choose n]`. -/
theorem gdimPoly_repeated_qbinom (n : ℕ) :
    gdimPoly (grade G Λ (repeatedContent i n)) = qfact (tUnit (di C i)) n ^ 2 *
      (T (di C i * n * ((Λ i : ℤ)-n)) * qbinom (tUnit (di C i)) (Λ i) n) := by
  rw [gdimPoly_repeated G Λ i hsym hQ RD highest hΛ hdeg hdot]
  exact regularProduct_eq _ _ _

private theorem invert_fact (h : ℤ) (n : ℕ) :
    LaurentPolynomial.invert (qfact (tUnit h) n) = qfact (tUnit h) n := by
  rw [qfact,map_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [qint_tUnit,map_sum, ←Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [LaurentPolynomial.invert_T]
  have hj' := Finset.mem_range.mp hj
  congr 1
  push_cast [Nat.cast_sub (by omega : j ≤ m)]
  ring

private theorem homForm_smul_left_invert {A : Type*} [Ring A] [Algebra k A]
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [HasGdim 𝒜] (p : LP) (x y : K0 𝒜) :
    K0.homForm 𝒜 (p • x) y = toLaurentSeries (LaurentPolynomial.invert p) * K0.homForm 𝒜 x y := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp only [zero_smul,map_zero,AddMonoidHom.zero_apply,zero_mul]
  | add p q hp hq => rw [add_smul,map_add,AddMonoidHom.add_apply,hp,hq,map_add,map_add,add_mul]
  | single n m =>
    have hT : (AddMonoidAlgebra.single n m : LP) = m • T n := by
      rw [LaurentPolynomial.single_eq_C_mul_T,LaurentPolynomial.smul_eq_C_mul]
    rw [hT,smul_assoc,map_zsmul,AddMonoidHom.zsmul_apply,K0.homForm_T_smul_left,map_zsmul,
      LaurentPolynomial.invert_T,map_zsmul,K0.toLaurentSeries_T,smul_mul_assoc]

omit [DecidableEq I] in
private theorem expand_repeated (n : ℕ) : (expandDiv [(i,n)] : Multiset I) = repeatedContent i n := by
  simp [expandDiv,repeatedContent_eq_replicate,Multiset.coe_replicate]

variable (hs : ∀ a b, G.degΨ a b = G.degΨ b a) (hX : ∀ a, G.degX a = C.dot a a)

local notation "νₙ" => repeatedContent i
local notation "pₙ" => fun n : ℕ => dividedProjective G hs C Λ (νₙ n) [(i,n)] (expand_repeated i n)

include hX in
private theorem repeated_eq_divided (n : ℕ) :
    repeatedInduction G Λ i n = qfact (tUnit (di C i)) n • K0.of (pₙ n) := by
  let : Unique (Seq (νₙ n)) := Seq.uniqueOfForall (i := i) (fun a ha => by
    rw [repeatedContent_eq_replicate] at ha
    exact Multiset.eq_of_mem_replicate ha)
  have H := of_expanded_eq_factorial G hs C Λ (νₙ n) hX [(i,n)] (expand_repeated i n)
  rw [repeatedInduction_eq_regular]
  have he : (mk k Q (fun j => (Polynomial.X : Polynomial k)^Λ j) (νₙ n))
      (e (Seq.ofList _ (expand_repeated i n))) = 1 := by rw [e_eq_one,map_one]
  have H' := (K0.of_ofIdempotent_congr (𝒜 := grade G Λ (νₙ n)) he
    (IsIdempotentElem.map (e_mul_self _) _) IsIdempotentElem.one
    (Graded.mem_map_of_mem _ _ (G.e_mem_grade _)) SetLike.GradedOne.one_mem).trans
      (K0.of_eq_of_iso GProj.ofIdempotentOneIso)
  rw [← H']
  simpa [divQFact2,di] using H

include hsym hQ hΛ hdeg hdot hX in
/-- The graded endomorphism dimension of the actual pure nilHecke divided
projective in the cyclotomic quotient is the shifted quantum binomial.
The formula includes the vanishing for `n > Λᵢ`. -/
theorem homGdim_repeated_dividedProjective (n : ℕ) :
    GProj.homGdim (pₙ n) (pₙ n) = toLaurentSeries
      (T (di C i * n * ((Λ i : ℤ)-n)) * qbinom (tUnit (di C i)) (Λ i) n) := by
  let t := qfact (tUnit (di C i)) n
  let : Module.Finite k (CycKLR k Q (fun j => (Polynomial.X : Polynomial k)^Λ j) (νₙ n)) :=
    module_finite (fun a b hab => by obtain ⟨c,hc,h⟩ := hQ a b hab; rw [h]; exact hc.map Polynomial.C)
      (fun _ => Polynomial.monic_X_pow _)
  let := HasGdim.of_finiteDimensional (grade G Λ (νₙ n))
  have h := homForm_repeatedInduction G Λ i n
  rw [repeated_eq_divided G Λ i hs hX,homForm_smul_left_invert, invert_fact,
    K0.map_smul_of_T (F := K0.homForm _ _) (fun a x => K0.homForm_T_smul_right a _ x),
    K0.homForm_of, ←toLaurentSeries_gdimPoly,gdimPoly_repeated_qbinom G Λ i hsym hQ RD highest hΛ hdeg hdot,
    pow_two, toLaurentSeries_mul, toLaurentSeries_mul, mul_assoc] at h
  have ht : toLaurentSeries t ≠ 0 :=
    fun h => fact_ne_zero _ n (toLaurentSeries_injective (h.trans (map_zero _).symm))
  exact (mul_left_cancel₀ ht (mul_left_cancel₀ ht h))

end Categorification.KLR.CycKLR
