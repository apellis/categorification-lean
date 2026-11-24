/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree
import Categorification.KLR.CyclotomicFinite

/-!
# Polynomial matrix of the affine interval exit equations

For Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21),
fix the bottom loading of the intervening interval. Expanding at that loading
in the top-dotted PBW basis gives one polynomial equation for each permutation.
-/

namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial
noncomputable section

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I} (hQ : KLRSymm Q)
local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν
local notation "S" => Perm (Fin m)
local notation "P" => MvPolynomial (Fin m) k
variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
local notation "B" => lbasis (μ := ν) hQ ρ hρ

/-- The polynomial at a prescribed bottom loading and permutation in the
PBW basis with dots on top. -/
def exitPolynomial (s : Seq ν) (t : S) : R →ₗ[k] P :=
  (B).constr k fun a => if a.1 = s ∧ a.2.1 = t then monomial a.2.2 1 else 0

private theorem read_monomial (s r : Seq ν) (t w : S) (d : Fin m →₀ ℕ) :
    exitPolynomial hQ ρ hρ s t (pol (monomial d 1) * ψw (ρ w) * e r) =
      if r = s ∧ w = t then monomial d 1 else 0 := by
  calc
    _ = exitPolynomial hQ ρ hρ s t ((B) (r, w, d)) :=
      congrArg _ (lbasis_apply _ _ _ (r, w, d)).symm
    _ = _ := (B).constr_basis k _ (r, w, d)

/-- Reading a normalized PBW row recovers its entire polynomial. -/
theorem exitPolynomial_normal (s r : Seq ν) (t w : S) (f : P) :
    exitPolynomial hQ ρ hρ s t (pol f * ψw (ρ w) * e r) =
      if r = s ∧ w = t then f else 0 := by
  let atWord := (LinearMap.mulRight k (e r : R)).comp
    ((LinearMap.mulRight k (ψw (ρ w) : R)).comp pol.toLinearMap)
  by_cases ht : r = s ∧ w = t
  · rw [ite_eq_left ht]
    have eq : (exitPolynomial hQ ρ hρ s t).comp atWord = LinearMap.id := by
      apply (basisMonomials (Fin m) k).ext
      intro d
      exact (read_monomial hQ ρ hρ s r t w d).trans (ite_eq_left ht)
    exact LinearMap.congr_fun eq f
  · rw [ite_eq_right ht]
    have eq : (exitPolynomial hQ ρ hρ s t).comp atWord = 0 := by
      apply (basisMonomials (Fin m) k).ext
      intro d
      exact (read_monomial hQ ρ hρ s r t w d).trans (ite_eq_right ht)
    exact LinearMap.congr_fun eq f

/-- Upper dot polynomials multiply every PBW component. -/
theorem exitPolynomial_pol_mul (s : Seq ν) (t : S) (f : P) (x : R) :
    exitPolynomial hQ ρ hρ s t (pol f * x) = f * exitPolynomial hQ ρ hρ s t x := by
  have eq : (exitPolynomial hQ ρ hρ s t).comp (LinearMap.mulLeft k (pol f : R)) =
      (LinearMap.mulLeft k f).comp (exitPolynomial hQ ρ hρ s t) := by
    apply (B).ext
    rintro ⟨r, w, d⟩
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, lbasis_apply]
    rw [← mul_assoc, ← mul_assoc, ← map_mul, exitPolynomial_normal, exitPolynomial_normal]
    split_ifs <;> simp
  exact LinearMap.congr_fun eq x

/-- At fixed bottom loading, the PBW polynomial tuple reconstructs the whole
column, including lower crossing degrees. -/
theorem sum_exitPolynomials (s : Seq ν) (x : R) :
    ∑ t : S, pol (exitPolynomial hQ ρ hρ s t x) * ψw (ρ t) * e s = x * e s := by
  classical
  let row (t : S) : P →ₗ[k] R := (LinearMap.mulRight k (e s : R)).comp
    ((LinearMap.mulRight k (ψw (ρ t) : R)).comp pol.toLinearMap)
  have eq : (∑ t : S, (row t).comp (exitPolynomial hQ ρ hρ s t)) = LinearMap.mulRight k (e s : R) := by
    apply (B).ext
    rintro ⟨r, w, d⟩
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, lbasis_apply,
      read_monomial]
    rw [mul_assoc _ (e r), e_mul_e]
    by_cases hr : r = s
    · subst r
      simp only [true_and, ite_true]
      rw [Finset.sum_eq_single w]
      · simp [row]
      · intro a _ ha; rw [ite_eq_right (Ne.symm ha), map_zero]
      · simp
    · simp [hr]
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, row,
    AlgHom.toLinearMap_apply] using LinearMap.congr_fun eq x

private theorem support_word (s : Seq ν) (l : List ℕ) :
    (e (wordProd m l • s) * (ψw l * e s) : R) = ψw l * e s := by
  rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

/-- The affine exit equation at a fixed bottom loading holds precisely when its
polynomial matrix annihilates the tuple of upper coefficients. This is the local
relation problem in Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after
(6.21), before passage to the marked quotient. -/
theorem exit_polynomial_matrix_iff {η : Type*} (A : Finset η) (s : Seq ν)
    (upper leg : η → List ℕ) (f : η → P) :
    (∑ a ∈ A, (pol (f a) * ψw (upper a) * e (wordProd m (leg a) • s)) * (ψw (leg a) * e s) : R) = 0 ↔
      ∀ t : S, (∑ a ∈ A, f a * exitPolynomial hQ ρ hρ s t (ψw (upper a ++ leg a) * e s)) = 0 := by
  let x : R := ∑ a ∈ A, pol (f a) * (ψw (upper a ++ leg a) * e s)
  have row (a : η) : (pol (f a) * ψw (upper a) * e (wordProd m (leg a) • s)) * (ψw (leg a) * e s : R) =
      pol (f a) * (ψw (upper a ++ leg a) * e s) := by
    rw [mul_assoc _ (e _), support_word s (leg a), ψw_append]
    simp only [mul_assoc]
  rw [Finset.sum_congr rfl (fun a _ => row a)]
  have read (t : S) : exitPolynomial hQ ρ hρ s t x =
      ∑ a ∈ A, f a * exitPolynomial hQ ρ hρ s t (ψw (upper a ++ leg a) * e s) := by
    simp only [x, map_sum, exitPolynomial_pol_mul]
  change x = 0 ↔ _
  constructor
  · intro hx t
    rw [← read, hx, map_zero]
  · intro allz
    have hz := sum_exitPolynomials hQ ρ hρ s x
    simp only [read, allz, map_zero, zero_mul, Finset.sum_const_zero] at hz
    rw [← show x * e s = x by simp only [x, Finset.sum_mul, mul_assoc, e_mul_self], ← hz]

/-- For arbitrary upper algebra elements, the local affine exit equation in
Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21) is a finite
polynomial system indexed by upper permutations and exits. The input polynomial
at `(a,u)` is read at the top loading of the exit `a`. -/
theorem exit_relation_polynomial_matrix_iff {η : Type*} (A : Finset η) (s : Seq ν)
    (leg : η → List ℕ) (upper : η → R) :
    (∑ a ∈ A, upper a * (ψw (leg a) * e s)) = 0 ↔
      ∀ t : S, (∑ a ∈ A, ∑ u : S,
        exitPolynomial hQ ρ hρ (wordProd m (leg a) • s) u (upper a) *
          exitPolynomial hQ ρ hρ s t (ψw (ρ u ++ leg a) * e s)) = 0 := by
  classical
  let coefficient (a : η) (u : S) := exitPolynomial hQ ρ hρ (wordProd m (leg a) • s) u (upper a)
  have eqs := exit_polynomial_matrix_iff hQ ρ hρ (A ×ˢ (Finset.univ : Finset S)) s
    (fun z => ρ z.2) (fun z => leg z.1) (fun z => coefficient z.1 z.2)
  simp only [Finset.sum_product] at eqs
  have expand (a : η) : (∑ u : S, (pol (coefficient a u) * ψw (ρ u) * e (wordProd m (leg a) • s)) *
      (ψw (leg a) * e s) : R) = upper a * (ψw (leg a) * e s) := by
    rw [← Finset.sum_mul, sum_exitPolynomials, mul_assoc, support_word]
  simpa only [expand, coefficient] using eqs

/-- Polynomial of a crossing followed by its reverse at the top loading of a leg. -/
def exitSquarePolynomial (Q : I → I → MvPolynomial (Fin 2) k) (r : Seq ν)
    (j : ℕ) (hj : j + 1 < m) : P :=
  let a : Fin m := ⟨j, by omega⟩
  let b : Fin m := ⟨j + 1, hj⟩
  if r.lbl a = r.lbl b then 0 else rename ![a, b] (Q (r.lbl a) (r.lbl b))

private theorem square_above (s : Seq ν) (leg : List ℕ) (j : ℕ) (hj : j + 1 < m) :
    (ψw (j :: j :: leg) * e s : R) =
      pol (exitSquarePolynomial Q (wordProd m leg • s) j hj) * (ψw leg * e s) := by
  let r := wordProd m leg • s
  have hr := support_word (Q := Q) s leg
  have hs : (ψ j * ψ j * e r : R) = pol (exitSquarePolynomial Q r j hj) * e r := by
    rw [ψ_sq j hj, exitSquarePolynomial]
    split_ifs
    · rw [map_zero, zero_mul]
    · rw [ncEval_x₂]
  calc
    _ = (ψ j * ψ j) * (ψw leg * e s) := by simp only [ψw_cons, mul_assoc]
    _ = (ψ j * ψ j * e r) * (ψw leg * e s) := by rw [mul_assoc _ (e r), hr]
    _ = _ := by rw [hs, mul_assoc _ (e r), hr]

private theorem slide_above (s : Seq ν) (l : List ℕ) (j : ℕ) (hj : j + 1 < m) (f : P)
    (hne : (wordProd m l • s).lbl ⟨j, by omega⟩ ≠ (wordProd m l • s).lbl ⟨j + 1, hj⟩) :
    (ψ j * (pol f * (ψw l * e s)) : R) = pol (swapPol j hj f) * (ψw (j :: l) * e s) := by
  let r := wordProd m l • s
  have hr := support_word (Q := Q) s l
  have slide := ψ_mul_pol_mul_e (Q := Q) j hj r f
  rw [ite_eq_right hne, add_zero] at slide
  calc
    _ = (ψ j * pol f * e r) * (ψw l * e s) := by rw [mul_assoc _ (e r), hr, mul_assoc]
    _ = _ := by rw [slide, mul_assoc _ (e r), hr]; simp only [ψw_cons, mul_assoc]

/-- The square polynomial of the first black strand and the right red strand,
transported to the joint loading of the extreme and middle exits. -/
def twoBlackExitPolynomial (Q : I → I → MvPolynomial (Fin 2) k) (s : Seq ν)
    (p : ℕ) (hp : p + 3 < m) : P :=
  swapPol (p + 1) (by omega) (swapPol p (by omega)
    (exitSquarePolynomial Q (wordProd m [p + 2] • s) (p + 1) (by omega)))

/-- For two intervening black strands, the reduced upper word `[p, p + 1]` on the
extreme exit equals the square polynomial times the middle exit. The three
colour inequalities are the ones used in the braid and two dot slides. For a
red–black–black–red loading they hold even when the black colours agree.
Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem twoBlack_extreme_middle (s : Seq ν) (p : ℕ) (hp : p + 3 < m)
    (hb : (wordProd m [p + 1, p + 2] • s).lbl ⟨p, by omega⟩ ≠
      (wordProd m [p + 1, p + 2] • s).lbl ⟨p + 2, by omega⟩)
    (ha : (wordProd m [p + 2] • s).lbl ⟨p, by omega⟩ ≠
      (wordProd m [p + 2] • s).lbl ⟨p + 1, by omega⟩)
    (hc : (wordProd m [p, p + 2] • s).lbl ⟨p + 1, by omega⟩ ≠
      (wordProd m [p, p + 2] • s).lbl ⟨p + 2, by omega⟩) :
    (ψw ([p, p + 1] ++ [p, p + 1, p + 2]) * e s : R) =
      pol (twoBlackExitPolynomial Q s p hp) * (ψw [p + 1, p, p + 2] * e s) := by
  let r := wordProd m [p + 1, p + 2] • s
  have bra := braid (Q := Q) p (by omega) r
  rw [ite_eq_right (fun h => hb h.1), sub_mul, sub_eq_zero] at bra
  have hr := support_word (Q := Q) s [p + 1, p + 2]
  have bra' := congrArg (· * (ψw [p + 1, p + 2] * e s)) bra
  rw [mul_assoc _ (e r), hr, mul_assoc _ (e r), hr] at bra'
  let q := exitSquarePolynomial Q (wordProd m [p + 2] • s) (p + 1) (by omega)
  calc
    _ = ψw [p + 1, p, p + 1, p + 1, p + 2] * e s := by simpa only [List.cons_append, List.nil_append, ψw_cons, mul_assoc] using bra'
    _ = ψ (p + 1) * (ψ p * (ψw [p + 1, p + 1, p + 2] * e s)) := by simp only [ψw_cons, mul_assoc]
    _ = ψ (p + 1) * (ψ p * (pol q * (ψw [p + 2] * e s))) := by rw [square_above s [p + 2] (p + 1) (by omega)]
    _ = _ := by
      rw [slide_above s [p + 2] p (by omega) q ha, slide_above s [p, p + 2] (p + 1) (by omega) _ hc]
      rfl

end
end Categorification.KLR.KLRAlgebra
