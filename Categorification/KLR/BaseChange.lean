/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Change of base ring for KLR algebras; universal KLR data

A ring homomorphism `φ : k → k'` carrying the KLR polynomials `Q` to `Q'` (off the diagonal)
induces a ring homomorphism `R_k(ν) → R_{k'}(ν)` sending each generator `e(𝐢)`, `x_a`, `ψ_j` to the
generator of the same name (`KLRAlgebra.mapRingHom`). The relations of `R(ν)` only involve
`Q_{ab}` for `a ≠ b`.

**Universal data.** For symmetric KLR data `Q` over an arbitrary commutative ring `k`
(`Q_{ba}(u, v) = Q_{ab}(v, u)` for `a ≠ b`) we construct an integral domain `UnivRing I`
(a polynomial ring over `ℤ`), KLR data `univQ Q` over it, a factorization
`univQ Q a b = P_{ba}(u, v) P_{ab}(v, u)` with all `P_{ab} ≠ 0` (`univP Q`), and a ring
homomorphism `univMap Q : UnivRing I → k` carrying `univQ Q` to `Q` off the diagonal. Over
`UnivRing I` the polynomial representation is faithful (KL I Cor. 2.6, `polyRep_injective`), so an
identity between expressions in the generators that is proved there by computing with
polynomials holds over every commutative ring, for every symmetric `Q`, by applying
`mapRingHom`. This is how the identities of Kang–Kashiwara §4.2 are proved over an arbitrary
base ring (as Kang–Kashiwara do) in `Categorification.KLR.Intertwiner`.
-/

namespace Categorification.KLR

open MvPolynomial

variable {I : Type*} [DecidableEq I] {k k' : Type*} [CommRing k] [CommRing k']

/-! ### `ncEval` and `qbar` under a change of rings -/

section ncEvalMap

variable {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k' B]

theorem ncEval_add {n : ℕ} (y : Fin n → A) (p q : MvPolynomial (Fin n) k) :
    ncEval y (p + q) = ncEval y p + ncEval y q := by
  unfold ncEval
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem ncEval_monomial {n : ℕ} (y : Fin n → A) (s : Fin n →₀ ℕ) (c : k) :
    ncEval y (monomial s c) = algebraMap k A c * (List.ofFn fun a => y a ^ s a).prod := by
  unfold ncEval
  exact Finsupp.sum_single_index (by simp)

/-- A ring homomorphism compatible with `φ` on scalars commutes with `ncEval`. -/
theorem map_ncEval (φ : k →+* k') (F : A →+* B)
    (hF : ∀ c, F (algebraMap k A c) = algebraMap k' B (φ c)) {n : ℕ} (y : Fin n → A)
    (p : MvPolynomial (Fin n) k) :
    F (ncEval y p) = ncEval (fun a => F (y a)) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ncEval_monomial, map_monomial, ncEval_monomial, map_mul, hF, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, map_pow]
  | add p q hp hq => rw [ncEval_add, map_add, hp, hq, map_add, ncEval_add]

theorem map_qbar (φ : k →+* k') (P : MvPolynomial (Fin 2) k) :
    MvPolynomial.map φ (qbar P) = qbar (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [qbar_monomial, map_monomial, qbar_monomial]
    simp [map_sum]
  | add p q hp hq => rw [qbar_add, map_add, hp, hq, map_add, qbar_add]

end ncEvalMap

/-! ### The base-change homomorphism -/

namespace KLRAlgebra

section mapRingHom

variable (φ : k →+* k') {Q : I → I → MvPolynomial (Fin 2) k}
  {Q' : I → I → MvPolynomial (Fin 2) k'}
  (hQ : ∀ a b, a ≠ b → MvPolynomial.map φ (Q a b) = Q' a b) {ν : Multiset I}

variable (Q' ν) in
/-- `R_{k'}(ν)` regarded as a `k`-algebra through `φ` (used only to lift from the free
algebra). -/
noncomputable abbrev algOf : Algebra k (KLRAlgebra k' Q' ν) :=
  Algebra.compHom (KLRAlgebra k' Q' ν) φ

/-- The images of the generators. -/
noncomputable def genImg : Gen ν → KLRAlgebra k' Q' ν
  | .idem i => e i
  | .dot a => x a
  | .cross j => ψ j

variable (Q' ν) in
/-- The free algebra on the generators maps to `R_{k'}(ν)`. -/
noncomputable def freeToKLR : FreeAlgebra k (Gen ν) →+* KLRAlgebra k' Q' ν :=
  letI := algOf φ Q' ν
  (FreeAlgebra.lift k (genImg (Q' := Q'))).toRingHom

theorem freeToKLR_ι (g : Gen ν) :
    freeToKLR φ Q' ν (FreeAlgebra.ι k g) = genImg g := by
  let _ := algOf φ Q' ν
  exact FreeAlgebra.lift_ι_apply _ _

theorem freeToKLR_algebraMap (c : k) :
    freeToKLR φ Q' ν (algebraMap k _ c) = algebraMap k' _ (φ c) := by
  let _ := algOf φ Q' ν
  exact (FreeAlgebra.lift k (genImg (Q' := Q'))).commutes c

theorem freeToKLR_ncEval {n : ℕ} (y : Fin n → FreeAlgebra k (Gen ν))
    (p : MvPolynomial (Fin n) k) :
    freeToKLR φ Q' ν (ncEval y p) =
      ncEval (fun a => freeToKLR φ Q' ν (y a)) (MvPolynomial.map φ p) :=
  map_ncEval φ _ (freeToKLR_algebraMap φ) y p

include hQ in
theorem freeToKLR_rel ⦃u v : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν u v) :
    freeToKLR φ Q' ν u = freeToKLR φ Q' ν v := by
  have hfe : ∀ i, freeToKLR φ Q' ν (fe k ν i) = e i := fun i => freeToKLR_ι φ _
  have hfx : ∀ a, freeToKLR φ Q' ν (fx k ν a) = x a := fun a => freeToKLR_ι φ _
  have hfψ : ∀ j, freeToKLR φ Q' ν (fψ k ν j) = ψ j := fun j => freeToKLR_ι φ _
  cases h with
  | idem_mul i j =>
    rw [map_mul, hfe, hfe, e_mul_e]
    split_ifs <;> simp [hfe]
  | idem_sum => rw [map_sum, map_one]; simp only [hfe]; exact sum_e
  | dot_idem a i => rw [map_mul, map_mul, hfe, hfx]; exact x_mul_e a i
  | cross_idem j i => rw [map_mul, map_mul, hfe, hfe, hfψ]; exact ψ_mul_e j i
  | cross_zero j h => rw [map_zero, hfψ]; exact ψ_eq_zero j h
  | dot_dot a b => rw [map_mul, map_mul, hfx, hfx]; exact x_mul_x a b
  | cross_cross j l h => rw [map_mul, map_mul, hfψ, hfψ]; exact ψ_mul_ψ j l h
  | dot_cross a j h₁ h₂ => rw [map_mul, map_mul, hfx, hfψ]; exact x_mul_ψ a j h₁ h₂
  | dot_cross_left j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, dot_cross_left]
    split_ifs <;> simp [hfe]
  | dot_cross_right j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, dot_cross_right]
    split_ifs <;> simp [hfe]
  | cross_sq j h i =>
    rw [map_mul, map_mul, hfψ, hfe, ψ_sq j h i]
    split_ifs with hc
    · simp
    · rw [map_mul, hfe, freeToKLR_ncEval, hQ _ _ hc]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
  | braid j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, map_mul, map_mul, hfψ, hfψ, hfe, braid j h i]
    split_ifs with hc
    · rw [map_mul, hfe, freeToKLR_ncEval, map_qbar, hQ _ _ hc.2]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
    · simp

/-- **Change of base ring**: `φ : k → k'` with `φ(Q_{ab}) = Q'_{ab}` for `a ≠ b` induces a ring
homomorphism `R_k(ν) → R_{k'}(ν)` on generators. -/
noncomputable def mapRingHom : KLRAlgebra k Q ν →+* KLRAlgebra k' Q' ν :=
  RingQuot.lift ⟨freeToKLR φ Q' ν, freeToKLR_rel φ hQ⟩

theorem mapRingHom_mk (u : FreeAlgebra k (Gen ν)) :
    mapRingHom φ hQ (mk k Q ν u) = freeToKLR φ Q' ν u := by
  have := RingQuot.lift_mkRingHom_apply (freeToKLR φ Q' ν) (freeToKLR_rel φ hQ) u
  rw [← RingQuot.mkAlgHom_coe k] at this
  exact this

@[simp] theorem mapRingHom_e (i : Seq ν) : mapRingHom φ hQ (e i) = e i := by
  rw [e, mapRingHom_mk]; exact freeToKLR_ι φ _

@[simp] theorem mapRingHom_x (a : Fin (Multiset.card ν)) : mapRingHom φ hQ (x a) = x a := by
  rw [x, mapRingHom_mk]; exact freeToKLR_ι φ _

@[simp] theorem mapRingHom_ψ (j : ℕ) : mapRingHom φ hQ (ψ j : KLRAlgebra k Q ν) = ψ j := by
  rw [ψ, mapRingHom_mk]; exact freeToKLR_ι φ _

@[simp] theorem mapRingHom_algebraMap (c : k) :
    mapRingHom φ hQ (algebraMap k (KLRAlgebra k Q ν) c) = algebraMap k' _ (φ c) := by
  rw [← (mk k Q ν).commutes c, mapRingHom_mk]
  exact freeToKLR_algebraMap φ c

@[simp] theorem mapRingHom_pol (p : MvPolynomial (Fin (Multiset.card ν)) k) :
    mapRingHom φ hQ (pol p) = pol (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [algHom_C, map_C, mapRingHom_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp => simp only [map_mul, hp, pol_X, mapRingHom_x, MvPolynomial.map_X]

end mapRingHom

end KLRAlgebra

/-! ### Universal symmetric KLR data -/

section univ

omit [DecidableEq I]

/-- The index set of the universal coefficients: a pair of colours and a monomial exponent. -/
abbrev UnivIdx (I : Type*) : Type _ := I × I × (Fin 2 →₀ ℕ)

/-- The universal coefficient ring, an integral domain. -/
abbrev UnivRing (I : Type*) : Type _ := MvPolynomial (UnivIdx I) ℤ

variable (Q : I → I → MvPolynomial (Fin 2) k)

/-- The generic polynomial with the support of `Q_{ab}` (and the constant term), with one
indeterminate coefficient per monomial. -/
noncomputable def univQ₀ (a b : I) : MvPolynomial (Fin 2) (UnivRing I) :=
  ∑ s ∈ insert 0 (Q a b).support, monomial s (X (a, b, s))

theorem univQ₀_ne_zero (a b : I) : univQ₀ Q a b ≠ 0 := by
  classical
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp [univQ₀, MvPolynomial.coeff_monomial] at this

/-- The specialization `UnivRing I → k` sending each indeterminate coefficient to the
corresponding coefficient of `Q`. -/
noncomputable def univMap : UnivRing I →+* k :=
  eval₂Hom (Int.castRingHom k) fun t => (Q t.1 t.2.1).coeff t.2.2

theorem map_univQ₀ (a b : I) : MvPolynomial.map (univMap Q) (univQ₀ Q a b) = Q a b := by
  classical
  rw [univQ₀, map_sum]
  simp only [map_monomial, univMap, eval₂Hom_X']
  by_cases h0 : (0 : Fin 2 →₀ ℕ) ∈ (Q a b).support
  · rw [Finset.insert_eq_of_mem h0]; exact (as_sum _).symm
  · rw [Finset.sum_insert h0, MvPolynomial.notMem_support_iff.mp h0, monomial_zero, zero_add]
    exact (as_sum _).symm

/-- The orientation used to split the universal polynomials (a well-order on `I`). -/
def univLt : I → I → Prop := WellOrderingRel

open Classical in
/-- The universal KLR data: `univQ₀ Q a b` when `a < b`, and its transpose when `b < a`. -/
noncomputable def univQ (a b : I) : MvPolynomial (Fin 2) (UnivRing I) :=
  if univLt a b then univQ₀ Q a b else rename ![1, 0] (univQ₀ Q b a)

open Classical in
/-- The factorization of `univQ`: `P_{ab} = (univQ₀ Q a b)(v, u)` when `a < b`, and `1`
otherwise. -/
noncomputable def univP (a b : I) : MvPolynomial (Fin 2) (UnivRing I) :=
  if univLt a b then rename ![1, 0] (univQ₀ Q a b) else 1

theorem rename_swap_rename_swap {R : Type*} [CommRing R] (p : MvPolynomial (Fin 2) R) :
    rename ![1, 0] (rename ![1, 0] p) = p := by
  rw [rename_rename]
  convert rename_id_apply p
  funext t; fin_cases t <;> rfl

theorem univLt_asymm {a b : I} (h : univLt a b) : ¬ univLt b a :=
  _root_.asymm (r := (WellOrderingRel : I → I → Prop)) h

theorem univLt_total {a b : I} (h : a ≠ b) : univLt a b ∨ univLt b a := by
  rcases trichotomous_of (WellOrderingRel : I → I → Prop) a b with h' | h' | h'
  · exact Or.inl h'
  · exact absurd h' h
  · exact Or.inr h'

theorem univQ_factor (a b : I) (hab : a ≠ b) :
    univQ Q a b = univP Q b a * rename ![1, 0] (univP Q a b) := by
  rcases univLt_total hab with h | h
  · simp only [univQ, univP, h, univLt_asymm h, ↓reduceIte, one_mul, rename_swap_rename_swap]
  · simp only [univQ, univP, h, univLt_asymm h, ↓reduceIte, map_one, mul_one]

theorem univP_ne_zero (a b : I) : univP Q a b ≠ 0 := by
  unfold univP
  split_ifs
  · exact fun h => univQ₀_ne_zero Q a b
      (rename_injective _ (fun s t hst => by fin_cases s <;> fin_cases t <;> simp_all)
        (h.trans (map_zero _).symm))
  · exact one_ne_zero

theorem map_univQ (hsym : ∀ a b, a ≠ b → Q b a = rename ![1, 0] (Q a b)) (a b : I)
    (hab : a ≠ b) : MvPolynomial.map (univMap Q) (univQ Q a b) = Q a b := by
  unfold univQ
  split_ifs
  · exact map_univQ₀ Q a b
  · rw [map_rename, map_univQ₀, hsym a b hab, rename_swap_rename_swap]

end univ

end Categorification.KLR
