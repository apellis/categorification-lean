/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree
import Categorification.KLR.CyclotomicFinite
import Mathlib.Algebra.MvPolynomial.Division

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

/-- A square on top of a supported crossing word multiplies by its local KLR square polynomial. -/
theorem exit_square_word (s : Seq ν) (leg : List ℕ) (j : ℕ) (hj : j + 1 < m) :
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
    _ = ψ (p + 1) * (ψ p * (pol q * (ψw [p + 2] * e s))) := by rw [exit_square_word s [p + 2] (p + 1) (by omega)]
    _ = _ := by
      rw [slide_above s [p + 2] p (by omega) q ha, slide_above s [p, p + 2] (p + 1) (by omega) _ hc]
      rfl

/-- Choose PBW words containing a prescribed reduced word and its reduced
extension by one crossing. Their product permutations are distinct. -/
theorem exists_pbw_words_for_crossing {N : ℕ} {l : List ℕ} (hl : IsReduced N l)
    (j : ℕ) (hj : IsReduced N (j :: l)) :
    let u := wordProd N l
    let v := wordProd N (j :: l)
    u ≠ v ∧ ∃ rep : Perm (Fin N) → List ℕ, rep u = l ∧ rep v = j :: l ∧
      ∀ t, IsReduced N (rep t) ∧ wordProd N (rep t) = t := by
  intro u v
  classical
  have huv : u ≠ v := by
    intro he
    have h₁ : l.length = length N u := hl.2
    have h₂ : l.length + 1 = length N v := hj.2
    rw [he] at h₁
    omega
  let rep (t : Perm (Fin N)) := if t = u then l else if t = v then j :: l else TypeA.canWord N t
  have repU : rep u = l := ite_eq_left rfl
  have repV : rep v = j :: l := by simp [rep, huv.symm]
  have hrep (t : Perm (Fin N)) : IsReduced N (rep t) ∧ wordProd N (rep t) = t := by
    by_cases hu : t = u
    · subst t; rw [repU]; exact ⟨hl, rfl⟩
    by_cases hv : t = v
    · subst t; rw [repV]; exact ⟨hj, rfl⟩
    · simpa only [rep, ite_eq_right hu, ite_eq_right hv] using
        And.intro (isReduced_canWord N t) (wordProd_canWord N t)
  exact ⟨huv, rep, repU, repV, hrep⟩

include hQ in
/-- Top polynomial coefficients at two reduced PBW rows separated by a crossing are independent. -/
theorem top_polynomial_pair_eq_zero_iff_of_reduced {l : List ℕ} (hl : IsReduced m l) (j : ℕ)
    (hj : IsReduced m (j :: l)) (s : Seq ν) (f g : P) :
    (pol f * (ψw l * e s) + pol g * (ψw (j :: l) * e s) : R) = 0 ↔ f = 0 ∧ g = 0 := by
  classical
  let u := wordProd m l
  let v := wordProd m (j :: l)
  obtain ⟨huv, rep, repU, repV, hrep⟩ := exists_pbw_words_for_crossing hl j hj
  change u ≠ v at huv
  change rep u = l at repU
  change rep v = j :: l at repV
  constructor
  · intro eq
    have eq' : (pol f * ψw (rep u) * e s + pol g * ψw (rep v) * e s : R) = 0 := by
      simpa only [repU, repV, mul_assoc] using eq
    have read (t : S) := congrArg (exitPolynomial hQ rep hrep s t) eq'
    constructor
    · simpa only [map_add, exitPolynomial_normal, true_and, ite_true,
        ite_eq_right huv.symm, add_zero, map_zero] using read u
    · simpa only [map_add, exitPolynomial_normal, true_and, ite_true,
        ite_eq_right huv, zero_add, map_zero] using read v
  · rintro ⟨rfl, rfl⟩; simp

/-- The two PBW rows of the right-extreme return sum, including the divided
difference at the crossing of the two equal black strands. -/
theorem equalBlack_return_expansion (s : Seq ν) (l : List ℕ) (b j : ℕ)
    (hb : b + 1 < m) (hj : j + 1 < m)
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (f g h : P) :
    let q := exitSquarePolynomial Q (wordProd m l • s) b hb
    (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s) : R) =
      pol (f * q + g * NilHecke.dd k m j q) * (ψw l * e s) +
        pol (g * swapPol j hj q + h * q) * (ψw (j :: l) * e s) := by
  intro q
  let y : R := ψw l * e s
  let z : R := ψw (j :: l) * e s
  let r := wordProd m l • s
  have fix := sadj_smul_eq_self hj he
  have same : wordProd m (j :: l) • s = r := by rw [wordProd_cons, mul_smul, fix]
  have c₀ : (ψw (b :: b :: l) * e s : R) = pol q * y := exit_square_word s l b hb
  have c₂ : (ψw (b :: b :: j :: l) * e s : R) = pol q * z := by
    rw [exit_square_word s (j :: l) b hb, same]
  have hr : e r * y = y := support_word s l
  have cross := ψ_mul_pol_mul_e (Q := Q) j hj r q
  rw [ite_eq_left he] at cross
  have c₁ : (ψw (j :: b :: b :: l) * e s : R) =
      pol (swapPol j hj q) * z + pol (NilHecke.dd k m j q) * y := by
    calc
      _ = ψ j * (pol q * y) := by rw [ψw_cons, mul_assoc, c₀]
      _ = (ψ j * pol q * e r) * y := by rw [mul_assoc _ (e r), hr, mul_assoc]
      _ = _ := by
        rw [cross, add_mul, mul_assoc _ (e r), hr, mul_assoc _ (e r), hr]
        simp only [z, y, ψw_cons, mul_assoc]
  rw [c₀, c₁, c₂]
  simp only [map_add, map_mul, add_mul, mul_add, mul_assoc, y, z]
  abel

include hQ in
/-- Polynomial matrix of three return columns of the two outgoing arms at the
right extreme of a two-black interval in Webster, arXiv:1309.3796v2, §6.1,
proof of Lemma 6.8 after (6.21). At the extreme the outgoing arms are `ψ b` and
`ψ b ψ j`. The black crossing `ψ j` has equal colours. A return by `ψ b`,
with `ψ j` before or after the return, produces both the divided difference
of the square polynomial and the transposed square polynomial. The two equations
are exact whenever the extreme word and its black crossing are reduced. -/
theorem equalBlack_return_matrix_iff (s : Seq ν) (l : List ℕ) (b j : ℕ)
    (hb : b + 1 < m) (hj : j + 1 < m) (hl : IsReduced m l) (hjl : IsReduced m (j :: l))
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (f g h : P) :
    let q := exitSquarePolynomial Q (wordProd m l • s) b hb
    (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s) : R) = 0 ↔
      f * q + g * NilHecke.dd k m j q = 0 ∧ g * swapPol j hj q + h * q = 0 := by
  intro q
  have expansion := equalBlack_return_expansion (Q := Q) s l b j hb hj he f g h
  dsimp only at expansion
  rw [expansion]
  exact top_polynomial_pair_eq_zero_iff_of_reduced hQ hl j hjl s _ _

/-- Divisibility by a variable power is unaffected by multiplication with a power of a distinct variable. -/
theorem X_pow_dvd_of_dvd_mul_other {σ : Type*} {a b : σ} (hab : a ≠ b) (n : ℕ)
    {g : MvPolynomial σ k} (h : X a ^ n ∣ g * X b ^ n) : X a ^ n ∣ g := by
  classical
  simp only [X_pow_eq_monomial] at h ⊢
  obtain ⟨z, hz⟩ := h
  rw [monomial_one_dvd_iff_modMonomial_eq_zero]
  ext d
  change (g.modMonomial (Finsupp.single a n)).coeff d = 0
  by_cases ha : Finsupp.single a n ≤ d
  · exact coeff_modMonomial_of_le _ ha
  rw [coeff_modMonomial_of_not_le _ ha]
  have hab' : ¬ Finsupp.single a n ≤ d + Finsupp.single b n := by
    simpa only [Finsupp.single_le_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hab, add_zero] using ha
  have eq := congrArg (fun x : MvPolynomial σ k => x.coeff (d + Finsupp.single b n)) hz
  rw [coeff_mul_monomial, mul_one, coeff_monomial_mul', ite_eq_right hab'] at eq
  exact eq

include hQ in
/-- For the black-dot power `q = X_j^n` of a right-red bigon, all relations
among the three equal-black return columns are multiples of
`(∂_j q, -q, s_j q)`. This computes the interaction of the ordinary and
reversed-middle arms at the extreme in Webster, arXiv:1309.3796v2, §6.1,
proof of Lemma 6.8 after (6.21). It also covers `n = 0` and base rings with
zero divisors. -/
theorem equalBlack_return_kernel (s : Seq ν) (l : List ℕ) (b j n : ℕ)
    (hb : b + 1 < m) (hj : j + 1 < m) (hl : IsReduced m l) (hjl : IsReduced m (j :: l))
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (hweight : exitSquarePolynomial Q (wordProd m l • s) b hb = X (⟨j, by omega⟩ : Fin m) ^ n)
    (f g h : P) :
    (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s) : R) = 0 ↔
      ∃ z : P, f = z * NilHecke.dd k m j (X (⟨j, by omega⟩ : Fin m) ^ n) ∧
        g = -(z * X (⟨j, by omega⟩ : Fin m) ^ n) ∧ h = z * X (⟨j + 1, hj⟩ : Fin m) ^ n := by
  let a : Fin m := ⟨j, by omega⟩
  let b' : Fin m := ⟨j + 1, hj⟩
  let d := NilHecke.dd k m j ((X a : P) ^ n)
  have hne : a ≠ b' := by
    intro e
    have h := congrArg Fin.val e
    change j = j + 1 at h
    omega
  have swap : swapPol j hj ((X a : P) ^ n) = X b' ^ n := by
    rw [map_pow]; simp only [swapPol, rename_X, a, b', swap_apply_left]
  have equations := equalBlack_return_matrix_iff hQ s l b j hb hj hl hjl he f g h
  dsimp only at equations
  rw [equations, hweight, swap]
  change (f * X a ^ n + g * d = 0 ∧ g * X b' ^ n + h * X a ^ n = 0) ↔
    ∃ z : P, f = z * d ∧ g = -(z * X a ^ n) ∧ h = z * X b' ^ n
  constructor
  · rintro ⟨h₀, h₁⟩
    have hdiv : X a ^ n ∣ (-g) * X b' ^ n := ⟨h, by linear_combination -h₁⟩
    obtain ⟨z, hz⟩ := X_pow_dvd_of_dvd_mul_other hne n hdiv
    have hg : g = -(z * X a ^ n) := by linear_combination -hz
    subst g
    have reg : IsRegular ((X a : P) ^ n) := isRegular_X_pow n
    refine ⟨z, reg.right ?_, rfl, reg.right ?_⟩
    · linear_combination h₀
    · linear_combination h₁
  · rintro ⟨z, rfl, rfl, rfl⟩
    constructor <;> ring

/-- The full two-black joint completes the ordinary and reversed-middle arms by
`[b,b+1]` and `[b+1]`, respectively. Returning from that joint by `[b,b+1]`
produces the two components of the generator in `equalBlack_return_kernel`,
with opposite signs on the two arms. The joint loading has the colour pattern
`i,r,i`, and its right-hand square has the standard power on the black dot.
Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem equalBlack_cycle_components (t : Seq ν) (b n : ℕ) (hp : b + 2 < m)
    (he : t.lbl ⟨b, by omega⟩ = t.lbl ⟨b + 2, hp⟩)
    (hn : t.lbl ⟨b, by omega⟩ ≠ t.lbl ⟨b + 1, by omega⟩)
    (hsq : exitSquarePolynomial Q t (b + 1) hp = X (⟨b + 2, hp⟩ : Fin m) ^ n) :
    let j := b + 1
    let q : P := X (⟨j, by omega⟩ : Fin m) ^ n
    let q' : P := X (⟨j + 1, hp⟩ : Fin m) ^ n
    (ψw [b, j] * (ψw [b, j] * e t) : R) =
        pol q * (ψw [j, b] * e t) - pol (NilHecke.dd k m j q) * (ψw [b] * e t) ∧
      (ψw [b, j] * (ψw [j] * e t) : R) = pol q' * (ψw [b] * e t) := by
  intro j q q'
  let L : Fin m := ⟨j, by omega⟩
  let H : Fin m := ⟨j + 1, hp⟩
  have hb : b + 1 < m := by omega
  have diff : L ≠ H := by intro e; have h := congrArg Fin.val e; change j = j + 1 at h; omega
  have across : (sadj m j • t).lbl ⟨b, by omega⟩ ≠ (sadj m j • t).lbl ⟨b + 2, hp⟩ := by
    change (sadj m j • t).1 _ ≠ (sadj m j • t).1 _
    rw [sadj_smul_apply, sadj_smul_apply, sadj_apply_right hp,
      sadj_apply_of_ne _ (by dsimp [j]; omega) (by dsimp [j]; omega)]
    exact hn
  have same : (sadj m b • t).lbl L = (sadj m b • t).lbl H := by
    change (sadj m b • t).1 _ = (sadj m b • t).1 _
    rw [sadj_smul_apply, sadj_smul_apply, show L = ⟨b + 1, hb⟩ from rfl, sadj_apply_right hb,
      sadj_apply_of_ne _ (by dsimp [H, j]; omega) (by dsimp [H, j]; omega)]
    exact he
  have braid₀ := braid (Q := Q) b hp (sadj m j • t)
  rw [ite_eq_right (fun h => across h.1), sub_mul, sub_eq_zero] at braid₀
  have loaded : (e (sadj m j • t) * (ψ j * e t) : R) = ψ j * e t := by
    rw [← mul_assoc, ← ψ_mul_e, mul_assoc, e_mul_self]
  have bra := congrArg (· * (ψ j * e t)) braid₀
  rw [mul_assoc _ (e _), loaded, mul_assoc _ (e _), loaded] at bra
  have sq : (ψ j * (ψ j * e t) : R) = pol q' * e t := by
    have eq := exit_square_word (Q := Q) t [] j hp
    have hh : exitSquarePolynomial Q t j hp = q' := hsq
    simpa only [ψw_cons, ψw_nil, mul_one, one_mul, wordProd_nil, one_smul, mul_assoc, hh] using eq
  have comm : Commute (ψ b : R) (pol q') := by
    change Commute _ (pol ((X H : P) ^ n))
    rw [map_pow, pol_X]
    exact (show Commute (ψ b : R) (x H) from (x_mul_ψ H b
      (by dsimp [H, j]; omega) (by dsimp [H, j]; omega)).symm).pow_right n
  have ret : (ψ b * (ψ j * (ψ j * e t)) : R) = pol q' * (ψ b * e t) := by
    rw [sq, comm.left_comm]
  have sw : swapPol j hp q = q' := by
    change rename (Equiv.swap L H) ((X L : P) ^ n) = X H ^ n
    rw [map_pow, rename_X, Equiv.swap_apply_left]
  have sw' : swapPol j hp q' = q := by
    change rename (Equiv.swap L H) ((X H : P) ^ n) = X L ^ n
    rw [map_pow, rename_X, Equiv.swap_apply_right]
  have dd : NilHecke.dd k m j q' = -NilHecke.dd k m j q := by
    rw [← sw, NilHecke.dd_of_lt hp]
    exact ddiff_rename_swap diff q
  have ds := ψ_mul_pol_mul_e (Q := Q) j hp (sadj m b • t) q'
  rw [ite_eq_left same, sw', dd, map_neg, neg_mul, ← sub_eq_add_neg] at ds
  have support : (e (sadj m b • t) * (ψ b * e t) : R) = ψ b * e t := by
    rw [← mul_assoc, ← ψ_mul_e, mul_assoc, e_mul_self]
  have ds' := congrArg (· * (ψ b * e t)) ds
  rw [sub_mul, mul_assoc _ (e _), support, mul_assoc _ (e _), support, mul_assoc _ (e _), support] at ds'
  constructor
  · simp only [ψw_cons, ψw_nil, mul_one, mul_assoc] at bra ds' ⊢
    rw [bra, ret, ds']
  · simpa only [ψw_cons, ψw_nil, mul_one, mul_assoc] using ret

include hQ in
/-- Each polynomial relation among the three equal-black return columns is
induced by one coefficient supported at the full two-black joint. In the
notation of `equalBlack_return_kernel` this coefficient is `pol z` times
the return `[b,b+1]`, cut by the idempotent of the full joint at its bottom.
The ordinary and reversed-middle components have opposite signs. This is an
affine instance of the common-coefficient lifting step in Webster,
arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem exists_equalBlack_cycle_coefficient (s : Seq ν) (l : List ℕ) (b n : ℕ) (hp : b + 2 < m)
    (hl : IsReduced m l) (hjl : IsReduced m ((b + 1) :: l))
    (he : (wordProd m l • s).lbl ⟨b + 1, by omega⟩ = (wordProd m l • s).lbl ⟨b + 2, hp⟩)
    (hn : (wordProd m l • s).lbl ⟨b, by omega⟩ ≠ (wordProd m l • s).lbl ⟨b + 1, by omega⟩)
    (hw : Q ((wordProd m l • s).lbl ⟨b, by omega⟩) ((wordProd m l • s).lbl ⟨b + 1, by omega⟩) = X 1 ^ n)
    (f g h : P)
    (relation : (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw ((b + 1) :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: (b + 1) :: l) * e s) : R) = 0) :
    let t := sadj m b • (wordProd m l • s)
    let j := b + 1
    ∃ c : R, c * e (sadj m j • t) = c ∧
      c * (ψw [b, j] * e t) = -(pol f * (ψw [b] * e t) + pol g * (ψw [j, b] * e t)) ∧
      c * (ψw [j] * e t) = pol h * (ψw [b] * e t) := by
  intro t j
  let r := wordProd m l • s
  let p₀ : Fin m := ⟨b, by omega⟩
  let p₁ : Fin m := ⟨b + 1, by omega⟩
  let p₂ : Fin m := ⟨b + 2, hp⟩
  let q : P := X p₁ ^ n
  let q' : P := X p₂ ^ n
  have hb : b + 1 < m := by omega
  have t₀ : t.lbl p₀ = r.lbl p₁ := by
    change (sadj m b • r).1 _ = r.1 _
    rw [sadj_smul_apply, sadj_apply_left hb]
  have t₁ : t.lbl p₁ = r.lbl p₀ := by
    change (sadj m b • r).1 _ = r.1 _
    rw [sadj_smul_apply, sadj_apply_right hb]
  have t₂ : t.lbl p₂ = r.lbl p₂ := by
    change (sadj m b • r).1 _ = r.1 _
    rw [sadj_smul_apply, sadj_apply_of_ne _ (by dsimp [p₂]; omega) (by dsimp [p₂]; omega)]
  have te : t.lbl p₀ = t.lbl p₂ := t₀.trans (he.trans t₂.symm)
  have tn : t.lbl p₀ ≠ t.lbl p₁ := by rw [t₀, t₁]; exact Ne.symm hn
  have weight : exitSquarePolynomial Q r b hb = q := by
    unfold exitSquarePolynomial
    dsimp only
    rw [ite_eq_right hn, hw, map_pow, rename_X]
    rfl
  have tw : exitSquarePolynomial Q t j hp = q' := by
    change (if t.lbl p₁ = t.lbl p₂ then 0 else rename ![p₁, p₂] (Q (t.lbl p₁) (t.lbl p₂))) = q'
    rw [t₁, t₂, ← he, ite_eq_right hn, hw, map_pow, rename_X]
    rfl
  obtain ⟨z, hf, hg, hh⟩ := (equalBlack_return_kernel hQ s l b j n hb hp hl hjl he weight f g h).1 relation
  obtain ⟨armB, armD⟩ := equalBlack_cycle_components (Q := Q) t b n hp te tn tw
  let F := sadj m j • t
  have fe : F.lbl p₀ = F.lbl p₁ := by
    change (sadj m j • t).1 _ = (sadj m j • t).1 _
    rw [sadj_smul_apply j t p₀, sadj_smul_apply j t p₁,
      show sadj m j p₁ = p₂ from sadj_apply_left hp,
      sadj_apply_of_ne _ (by dsimp [p₀, j]; omega) (by dsimp [p₀, j]; omega)]
    exact te
  have fixed : sadj m b • F = F := sadj_smul_eq_self hb fe
  have fullB : wordProd m [b, j] • t = F := by
    simp only [wordProd_cons, wordProd_nil, mul_one, mul_smul]
    exact fixed
  have cutB := support_word (Q := Q) t [b, j]
  have cutD := support_word (Q := Q) t [j]
  rw [fullB] at cutB
  simp only [wordProd_cons, wordProd_nil, mul_one] at cutD
  refine ⟨pol z * ψw [b, j] * e F, ?_, ?_, ?_⟩
  · rw [mul_assoc _ (e F), e_mul_self]
  · rw [mul_assoc _ (e F), cutB, mul_assoc, armB, hf, hg]
    simp only [map_mul, map_neg, neg_mul, mul_assoc, neg_add_rev, neg_neg, sub_eq_add_neg, mul_add, mul_neg]
    rfl
  · rw [mul_assoc _ (e F), cutD, mul_assoc, armD, hh, map_mul, mul_assoc]

end
end Categorification.KLR.KLRAlgebra
