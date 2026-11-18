/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentEquivalence
import Categorification.KLR.CyclotomicPolynomialTrace

/-!
# The opposite cap when the added colour is absent

Brundan, arXiv:1501.00350v1, (1.17), and Kang–Kashiwara,
arXiv:1102.4677v4, Theorem 5.2. On the absent-colour corner the inverse
commutator has only dot-unit coordinates. Its last coordinate is the
top coefficient of the polynomial remainder, including the empty block.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour

open Polynomial
variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
    (i : I) (β : Multiset I) (a : I → Polynomial k)
local notation "R" => CycKLR k Q a β
local notation "F" => aMonicL Q i β a

/-- Polynomial evaluation by the ordinary two-sided dot-unit terms in every block. -/
def cornerEval : Polynomial R →ₗ[k] Corner Q i a β :=
  Polynomial.lsum (dotUnitTerm Q i a β)

theorem cornerEval_monomial (n : ℕ) (r : R) :
    cornerEval Q i β a (monomial n r) = dotUnitTerm Q i a β n r := by
  rw [cornerEval, lsum_apply, sum_monomial_index]
  exact map_zero _

private theorem cornerEval_eq (hβ : 0 < β.card) (p : Polynomial R) :
    cornerEval Q i β a p = polynomialToCorner Q i β a hβ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial d r =>
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective r
    rw [cornerEval_monomial, polynomialToCorner_monomial]

private theorem cornerEval_small (n : ℕ) (p : degreeLT R n) :
    cornerEval Q i β a p = dotUnitSum Q i a β n (degreeLTEquiv R n p) := by
  have he := congrArg Subtype.val ((degreeLTEquiv R n).symm_apply_apply p)
  change ∑ d : Fin n, monomial (d : ℕ) ((degreeLTEquiv R n p) d) = (p : Polynomial R) at he
  rw [← he, map_sum]
  simp only [cornerEval_monomial, dotUnitSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- The defining modulus over the coefficient algebra, with the singleton
polynomial at empty content. -/
def cornerModulus : Polynomial R :=
  if β = 0 then (a i).map (algebraMap k R) else F

variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
  (ha : ∀ j, (a j).Monic)

include hsym hQ ha in
theorem cornerModulus_monic : (cornerModulus Q i β a).Monic := by
  unfold cornerModulus
  split
  · exact (ha i).map _
  · exact monic_aMonicL i β a hsym hQ (ha i)

private theorem zeroCornerEval (p : Polynomial (CycKLR k Q a 0)) :
    zeroCornerEquiv Q i a (cornerEval Q i 0 a p) =
      PolynomialTrace.eval Q i a (p.map (cyclotomicZeroEquiv Q a).toRingEquiv.toRingHom) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, map_add, hp, hq]
  | monomial n r =>
    rw [cornerEval_monomial, zeroCornerEquiv_dotUnitTerm, Polynomial.map_monomial,
      ← C_mul_X_pow_eq_monomial, map_mul, map_pow, PolynomialTrace.eval_C, PolynomialTrace.eval_X,
      Algebra.smul_def]
    rfl

include hsym hQ ha in
private theorem cornerEval_mod (hi : i ∉ β) (p : Polynomial R) :
    cornerEval Q i β a (p %ₘ cornerModulus Q i β a) = cornerEval Q i β a p := by
  by_cases hb : β = 0
  · subst β
    apply (zeroCornerEquiv Q i a).injective
    rw [zeroCornerEval, zeroCornerEval, map_modByMonic _ (cornerModulus_monic Q i 0 a hsym hQ ha)]
    have hcomp : (cyclotomicZeroEquiv Q a).toRingEquiv.toRingHom.comp
        (algebraMap k (CycKLR k Q a 0)) = RingHom.id k := by ext c; exact (cyclotomicZeroEquiv Q a).commutes c
    rw [cornerModulus, ite_eq_left rfl, Polynomial.map_map, hcomp, Polynomial.map_id,
      PolynomialTrace.eval_eq, PolynomialTrace.eval_eq]
    congr 1
    exact AdjoinRoot.mk_leftInverse (ha i) (AdjoinRoot.mk (a i) _)
  · let hβ := Multiset.card_pos.mpr hb
    have h1 : 1 < ({i} + β : Multiset I).card := by simp only [Multiset.card_add, Multiset.card_singleton]; omega
    rw [cornerModulus, ite_eq_right hb, cornerEval_eq Q i β a hβ, cornerEval_eq Q i β a hβ,
      ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_polynomialToCorner Q i β hsym a hβ h1 hi]
    rcases subsingleton_or_nontrivial R with hs | hn
    · exact ⟨0, Subsingleton.elim _ _⟩
    have hS : sPoly (Q := Q) i β a = 1 := eq_one_of_monic_natDegree_zero (sPoly_monic i β a)
      (by rw [sPoly_natDegree, Multiset.count_eq_zero.mpr hi, mul_zero])
    let A := aMap i β a h1 hβ hsym
    have he (q : Polynomial R) : A q = lamA Q i β • (F * q) := by
      induction q using Polynomial.induction_on' with
      | add q r hq hr => rw [map_add, hq, hr, mul_add, smul_add]
      | monomial n r =>
        have h := aMap_sPoly_mul_X_pow_monic i β a hsym hβ hQ ha h1 n
        rw [hS, one_mul] at h
        change aMap i β a h1 hβ hsym _ = _
        rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul_C, aMap_mul_C, h, smul_mul_assoc, mul_assoc]
    refine ⟨-(Ring.inverse (lamA Q i β) • (p /ₘ F)), ?_⟩
    change A _ = _
    rw [map_neg, map_smul, he, smul_smul, Ring.inverse_mul_cancel _ (isUnit_lamA i β hQ),
      one_smul, modByMonic_eq_sub_mul_div]
    abel

variable {C₀ : QuantumGroup.CartanDatum I} {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
  (RD : QuantumGroup.UDot.WeightDatum C₀ W Z) (Λ : W)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))

include hsym hQ ha hΛ hdeg in
private theorem modulus_degree [Nontrivial R] (hi : i ∉ β) :
    ((cornerModulus Q i β a).natDegree : ℤ) = wt := by
  unfold cornerModulus
  split_ifs with hb
  · subst β; simp [Polynomial.Monic.natDegree_map (ha i), hΛ]
  · have h := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    simpa only [sPoly_natDegree, Multiset.count_eq_zero.mpr hi, mul_zero, Nat.cast_zero, sub_zero] using h

include hsym hQ ha hΛ hdeg in
/-- Every absent-colour corner element is an evaluated dot polynomial. -/
theorem cornerEval_surjective (hi : i ∉ β) : Function.Surjective (cornerEval Q i β a) := by
  intro z
  obtain ⟨v, hv⟩ := (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).surjective z
  let p := (degreeLTEquiv R (wt).toNat).symm v
  refine ⟨p.val, ?_⟩
  rw [cornerEval_small, LinearEquiv.apply_symm_apply]
  exact hv

/-- The last inverse dot-unit coordinate for positive weight, and the zero
map from the zero corner at weight zero. -/
def oppositeCap (hi : i ∉ β) : Corner Q i a β →ₗ[k] R :=
  if hw : 0 < wt then
    LinearMap.proj (Fin.mk ((wt).toNat - 1) (by omega)) ∘ₗ
      (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm.toLinearMap
  else 0

/-- The absent-colour cap of Brundan (1.17) on an arbitrary dot polynomial
is the monic remainder trace. This includes the singleton edge over the empty block. -/
theorem oppositeCap_eval (hi : i ∉ β) (p : Polynomial R) :
    oppositeCap Q i β a hsym hQ ha RD Λ hΛ hdeg hi (cornerEval Q i β a p) =
      MonicTrace.trace (cornerModulus Q i β a) p := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact Subsingleton.elim _ _
  have hm := cornerModulus_monic Q i β a hsym hQ ha
  have hd := modulus_degree Q i β a hsym hQ ha RD Λ hΛ hdeg hi
  let rem := p %ₘ cornerModulus Q i β a
  have hdegRem : rem.degree < ↑(wt).toNat := by
    have he : (cornerModulus Q i β a).natDegree = (wt).toNat := by omega
    rw [← he, ← degree_eq_natDegree hm.ne_zero]
    exact degree_modByMonic_lt p hm
  let r : degreeLT R (wt).toNat := ⟨rem, mem_degreeLT.mpr hdegRem⟩
  rw [← cornerEval_mod Q i β a hsym hQ ha hi p]
  change oppositeCap Q i β a hsym hQ ha RD Λ hΛ hdeg hi (cornerEval Q i β a r) = _
  rw [cornerEval_small, oppositeCap]
  split_ifs with hw
  · change ((finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm
      (dotUnitSum Q i a β _ (degreeLTEquiv R _ r))) _ = _
    rw [finEquiv_inverse_forward]
    change rem.coeff ((wt).toNat - 1) = rem.coeff ((cornerModulus Q i β a).natDegree - 1)
    congr 2
    omega
  · change 0 = rem.coeff _
    exact ((degree_lt_iff_coeff_zero _ _).mp hdegRem _ (by omega)).symm

end Categorification.KLR.KLRAlgebra.AbsentColour
