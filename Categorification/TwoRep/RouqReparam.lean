/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCoproductNeg
import Categorification.TwoRep.RouqKLRAction
import Categorification.TwoRep.RouqAdjunction
import Categorification.Algebra.DividedDifference
import Categorification.KLR.NcEvalHom

/-!
# Reparametrizing the dots of a Rouquier pair

B. Webster, *Unfurling Khovanov-Lauda-Rouquier algebras*, arXiv:1603.06311v3, §2.3, the
automorphism of equation `(a-auto)`: replacing the dot `y` by `ϖ(y)` and the crossing `ψ` by
`ψ` composed with `(y_k - y_{k+1}) / (ϖ(y_k) - ϖ(y_{k+1}))`. Here, for Rouquier's data at one
weight (`RouqLoc`) with nilpotent dots `x₁, x₂` and crossing `τ`, and a polynomial `f` with
`f(0) = 0` and `f'(0) ≠ 0`: the dots `f(x₁), f(x₂)` and the crossing
`τ ∘ ∂f(E₁ ◁ x₂, x₁ ▷ E₂)⁻¹`, with `∂f = (f(X₀) - f(X₁)) / (X₀ - X₁)`, are again Rouquier's data
at the same weight (`RouqLoc.reparam`). Webster's `ϖ` has a nonzero constant term; it is `u + f`
with a scalar `u`, and the scalar shift is the coproduct of `RouqCoproduct`.

* The dot slides: if `τ x - y τ = 1` then `τ g(x) - g(y) τ = ∂g(x, y)`
  (`mul_aeval_sub_aeval_mul`, `aeval_mul_sub_mul_aeval`).
* The inverses (Brundan, arXiv:1501.00350v1, (1.8), (1.9)): the rightward crossing of
  `τ ∘ p(E₁ ◁ x₂, x₁ ▷ E₂)` is `σ ∘ p(x₂ ▷ R₂, E₂ ◁ x₂')`, and also `p(R₁ ◁ x₁, x₁' ▷ E₁) ∘ σ`,
  up to the span of the closed diagrams `capD i ≫ cupD j` (`sigma_upEval_sub_mem`,
  `sigma_upEval_sub_mem'`); the caps and cups with dots `f(x)ᵗ` are the caps and cups with dots
  `xᵐ` through the lower triangular matrix `[Xᵐ] fᵗ` with diagonal `f'(0)ᵗ`
  (`det_powCoeffMatrix`). The Schur-complement criteria `isIso_lift_of_schur`,
  `isIso_desc_of_schur` with one label then give the inverses (`isIso_reparam_lift`,
  `isIso_reparam_desc`), converted to `SumInvTo`/`SumInvFrom` by `SumInvTo.ofIsIsoLift`,
  `SumInvFrom.ofIsIsoDesc`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Finset MvPolynomial

universe w v u

/-! ## Polynomials at nilpotent elements -/

section Algebra

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {σ : Type*}

/-- A polynomial without constant term, evaluated at nilpotent elements, is nilpotent. -/
theorem isNilpotent_sub_constantCoeff (φ : MvPolynomial σ k →ₐ[k] A)
    (hφ : ∀ i, IsNilpotent (φ (X i))) (p : MvPolynomial σ k) :
    IsNilpotent (φ (p - C (constantCoeff p))) := by
  have hc : ∀ x y : MvPolynomial σ k, Commute (φ x) (φ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm, map_add]
    exact (hc _ _).isNilpotent_add hp hq
  | mul_X p i _ =>
    rw [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero, map_mul]
    exact (hc _ _).isNilpotent_mul_left (hφ i)

/-- A polynomial with nonzero constant term, evaluated at nilpotent elements, has a two-sided
inverse which is again a polynomial with nonzero constant term (the geometric series). -/
theorem exists_inv_of_constantCoeff_ne_zero (φ : MvPolynomial σ k →ₐ[k] A)
    (hφ : ∀ i, IsNilpotent (φ (X i))) (p : MvPolynomial σ k) (hp : constantCoeff p ≠ 0) :
    ∃ p' : MvPolynomial σ k, φ p * φ p' = 1 ∧ φ p' * φ p = 1 ∧ constantCoeff p' ≠ 0 := by
  set c := constantCoeff p
  obtain ⟨m, hm⟩ := isNilpotent_sub_constantCoeff φ hφ p
  replace hm : φ (p - C c) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]
  set r : MvPolynomial σ k := -(C c⁻¹ * (p - C c))
  have hr : φ (r ^ (m + 1)) = 0 := by
    rw [show r ^ (m + 1) = (-C c⁻¹) ^ (m + 1) * (p - C c) ^ (m + 1) by
        simp only [r, ← mul_pow, neg_mul],
      map_mul, map_pow (f := φ) (p - C c), hm, mul_zero]
  have e : p * (C c⁻¹ * ∑ i ∈ range (m + 1), r ^ i) = 1 - r ^ (m + 1) := by
    rw [← mul_neg_geom_sum]
    have : p = C c * (1 - r) := by
      simp only [r, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, ← C_mul,
        mul_inv_cancel₀ hp, C_1, one_mul]
      ring
    rw [this, ← mul_assoc, mul_comm (C c), mul_assoc (1 - r), ← C_mul, mul_inv_cancel₀ hp, C_1,
      mul_one]
  refine ⟨C c⁻¹ * ∑ i ∈ range (m + 1), r ^ i, ?_, ?_, ?_⟩
  · rw [← map_mul, e, map_sub, hr, map_one, sub_zero]
  · rw [← map_mul, mul_comm, e, map_sub, hr, map_one, sub_zero]
  · rw [map_mul, constantCoeff_C, map_sum]
    have hr0 : constantCoeff r = 0 := by simp [r, c]
    rw [sum_range_succ', pow_zero, map_one]
    simp only [map_pow, hr0, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, sum_const_zero, zero_add, mul_one, inv_eq_zero]
    exact hp

variable [DecidableEq σ]

omit [Ring A] [Algebra k A] [DecidableEq σ] in
/-- The linear coefficient of a polynomial is the constant term of its divided difference. -/
theorem constantCoeff_ddiff_aeval (f : Polynomial k) :
    constantCoeff (ddiff 0 1 (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) f)) = f.coeff 1 := by
  let ev : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k := aeval ![Polynomial.X, 0]
  have hs : rename (Equiv.swap (0 : Fin 2) 1) (Polynomial.aeval (X 0) f) =
      Polynomial.aeval (X 1 : MvPolynomial (Fin 2) k) f := by
    rw [← Polynomial.aeval_algHom_apply, rename_X, Equiv.swap_apply_left]
  have hD := ddiff_spec (k := k) (σ := Fin 2) (a := 0) (b := 1) (by decide)
    (Polynomial.aeval (X 0) f)
  rw [hs] at hD
  have e0 : ev (Polynomial.aeval (X 0) f) = f := by
    rw [← Polynomial.aeval_algHom_apply]; simp [ev]
  have e1 : ev (Polynomial.aeval (X 1) f) = Polynomial.C (f.coeff 0) := by
    rw [← Polynomial.aeval_algHom_apply]
    simp [ev, Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  have h1 := congrArg ev hD
  rw [map_mul, map_sub, map_sub, e0, e1] at h1
  generalize ddiff 0 1 (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) f) = D at h1 ⊢
  have h2 := congrArg (fun q => Polynomial.coeff q 1) h1
  simp only [ev, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero,
    Polynomial.coeff_X_mul, Polynomial.coeff_sub, Polynomial.coeff_C, one_ne_zero, ite_false,
    sub_zero] at h2
  rw [← h2]
  have hc : (Polynomial.constantCoeff (R := k)).comp (ev : MvPolynomial (Fin 2) k →+* _) =
      constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun r => by simp [ev]) (fun i => ?_)
    fin_cases i <;> simp [ev]
  have := congrArg (fun F : MvPolynomial (Fin 2) k →+* k => F D) hc
  exact this.symm.trans (Polynomial.constantCoeff_apply _)

omit [Ring A] [Algebra k A] [DecidableEq σ] in
/-- The powers of a polynomial without constant term are lower triangular in the monomial basis. -/
theorem coeff_pow_of_lt {f : Polynomial k} (hf : f.coeff 0 = 0) {t p : ℕ} (hp : p < t) :
    (f ^ t).coeff p = 0 := by
  obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.mpr hf
  rw [mul_pow, Polynomial.coeff_X_pow_mul']
  simp [show ¬t ≤ p by omega]

omit [Ring A] [Algebra k A] [DecidableEq σ] in
/-- The diagonal coefficients of the powers of a polynomial without constant term. -/
theorem coeff_pow_self {f : Polynomial k} (hf : f.coeff 0 = 0) (t : ℕ) :
    (f ^ t).coeff t = f.coeff 1 ^ t := by
  obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.mpr hf
  rw [mul_pow, Polynomial.coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte]
  rw [Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_X_mul]

omit [DecidableEq σ] in
theorem aeval_eq_sum_range_of_pow_eq_zero {a : A} {n : ℕ} (ha : a ^ n = 0) (g : Polynomial k) :
    Polynomial.aeval a g = ∑ m ∈ range n, g.coeff m • a ^ m := by
  rw [Polynomial.aeval_eq_sum_range' (n := n + (g.natDegree + 1)) (by omega), sum_range_add,
    add_eq_left]
  exact sum_eq_zero fun m _ => by rw [pow_add, ha, zero_mul, smul_zero]

omit [Ring A] [Algebra k A] [DecidableEq σ] in
theorem rename_swap_X_zero_pow (m : ℕ) :
    rename (Equiv.swap (0 : Fin 2) 1) (X 0 ^ m : MvPolynomial (Fin 2) k) = X 1 ^ m := by
  rw [map_pow, rename_X, Equiv.swap_apply_left]

omit [Ring A] [Algebra k A] [DecidableEq σ] in
theorem ddiff_X_zero_pow_zero : ddiff 0 1 (X 0 ^ 0 : MvPolynomial (Fin 2) k) = 0 := by
  rw [pow_zero, ← C_1, ddiff_C (by decide : (0 : Fin 2) ≠ 1)]

omit [DecidableEq σ] in
/-- **Dots through a crossing**, powers: if `τ x - y τ = 1`, then `τ xᵐ - yᵐ τ = ∂(xᵐ)`. -/
theorem mul_pow_sub_pow_mul (φ : MvPolynomial (Fin 2) k →ₐ[k] A) {τ : A}
    (hτ : τ * φ (X 0) - φ (X 1) * τ = 1) (m : ℕ) :
    τ * φ (X 0 ^ m) - φ (X 1 ^ m) * τ = φ (ddiff 0 1 (X 0 ^ m)) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  induction m with
  | zero => rw [ddiff_X_zero_pow_zero, pow_zero, pow_zero, map_one, map_zero, mul_one, one_mul,
      sub_self]
  | succ m ih =>
    rw [pow_succ, pow_succ, ddiff_mul h01, ddiff_X_left h01, rename_swap_X_zero_pow, mul_one]
    simp only [map_add, map_mul]
    rw [← ih]
    have e : ∀ a b x0 x1 : A, τ * (a * x0) - b * x1 * τ =
        (τ * a - b * τ) * x0 + b * (τ * x0 - x1 * τ) := by intros; noncomm_ring
    rw [e, hτ, mul_one]

omit [DecidableEq σ] in
/-- **Dots through a crossing**, powers, other side: if `x τ - τ y = 1`, then
`xᵐ τ - τ yᵐ = ∂(xᵐ)`. -/
theorem pow_mul_sub_mul_pow (φ : MvPolynomial (Fin 2) k →ₐ[k] A) {τ : A}
    (hτ : φ (X 0) * τ - τ * φ (X 1) = 1) (m : ℕ) :
    φ (X 0 ^ m) * τ - τ * φ (X 1 ^ m) = φ (ddiff 0 1 (X 0 ^ m)) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hc : ∀ x y : MvPolynomial (Fin 2) k, φ x * φ y = φ y * φ x := fun x y => by
    rw [← map_mul, ← map_mul, mul_comm]
  induction m with
  | zero => rw [ddiff_X_zero_pow_zero, pow_zero, pow_zero, map_one, map_zero, mul_one, one_mul,
      sub_self]
  | succ m ih =>
    rw [pow_succ', pow_succ', ddiff_mul h01, ddiff_X_left h01, one_mul, rename_X,
      Equiv.swap_apply_left]
    simp only [map_add, map_mul]
    have e : ∀ a b x0 x1 : A, a * x0 * τ - τ * (b * x1) =
        a * (x0 * τ - τ * x1) + (a * τ - τ * b) * x1 := by intros; noncomm_ring
    rw [hc (X 0) (X 0 ^ m), hc (X 1) (X 1 ^ m), e, hτ, mul_one, ih,
      hc (ddiff 0 1 (X 0 ^ m)) (X 1)]

omit [DecidableEq σ] in
/-- **Dots through a crossing**: if `τ x - y τ = 1`, then `τ g(x) - g(y) τ = ∂g(x, y)` for every
polynomial `g`, where `∂g = (g(x) - g(y)) / (x - y)` is the divided difference. -/
theorem mul_aeval_sub_aeval_mul (φ : MvPolynomial (Fin 2) k →ₐ[k] A) {τ : A}
    (hτ : τ * φ (X 0) - φ (X 1) * τ = 1) (g : Polynomial k) :
    τ * φ (Polynomial.aeval (X 0) g) - φ (Polynomial.aeval (X 1) g) * τ =
      φ (ddiff 0 1 (Polynomial.aeval (X 0) g)) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul]
    rw [← hp, ← hq]
    abel
  | monomial m r =>
    rw [← Polynomial.smul_X_eq_monomial]
    simp only [map_smul, Polynomial.aeval_X_pow, mul_smul_comm, smul_mul_assoc]
    rw [← smul_sub, mul_pow_sub_pow_mul φ hτ]

omit [DecidableEq σ] in
/-- **Dots through a crossing**, other side: if `x τ - τ y = 1`, then
`g(x) τ - τ g(y) = ∂g(x, y)`. -/
theorem aeval_mul_sub_mul_aeval (φ : MvPolynomial (Fin 2) k →ₐ[k] A) {τ : A}
    (hτ : φ (X 0) * τ - τ * φ (X 1) = 1) (g : Polynomial k) :
    φ (Polynomial.aeval (X 0) g) * τ - τ * φ (Polynomial.aeval (X 1) g) =
      φ (ddiff 0 1 (Polynomial.aeval (X 0) g)) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul]
    rw [← hp, ← hq]
    abel
  | monomial m r =>
    rw [← Polynomial.smul_X_eq_monomial]
    simp only [map_smul, Polynomial.aeval_X_pow, mul_smul_comm, smul_mul_assoc]
    rw [← smul_sub, pow_mul_sub_mul_pow φ hτ]

end Algebra

/-! ## Evaluation at two commuting elements -/

section EvalTwo

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

theorem commute_vecTwo {y z : A} (hyz : Commute y z) (i j : Fin 2) :
    Commute ((![y, z] : Fin 2 → A) i) (![y, z] j) := by
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact hyz
  · exact hyz.symm
  · exact Commute.refl _

variable (k) in
/-- Evaluation of polynomials in two variables at two commuting elements, as an algebra
homomorphism. It agrees with `KLR.ncEval` (`ncEval_eq_evalTwo`). -/
def evalTwo (y z : A) (hyz : Commute y z) : MvPolynomial (Fin 2) k →ₐ[k] A :=
  (KLR.exists_algHom_ncEval ![y, z] (commute_vecTwo hyz)).choose

theorem evalTwo_X_zero (y z : A) (hyz : Commute y z) : evalTwo k y z hyz (X 0) = y :=
  (KLR.exists_algHom_ncEval (k := k) ![y, z] (commute_vecTwo hyz)).choose_spec.1 0

theorem evalTwo_X_one (y z : A) (hyz : Commute y z) : evalTwo k y z hyz (X 1) = z :=
  (KLR.exists_algHom_ncEval (k := k) ![y, z] (commute_vecTwo hyz)).choose_spec.1 1

theorem ncEval_eq_evalTwo (y z : A) (hyz : Commute y z) (p : MvPolynomial (Fin 2) k) :
    KLR.ncEval ![y, z] p = evalTwo k y z hyz p :=
  (KLR.exists_algHom_ncEval (k := k) ![y, z] (commute_vecTwo hyz)).choose_spec.2 p

theorem isNilpotent_evalTwo_X {y z : A} (hyz : Commute y z) (hy : IsNilpotent y)
    (hz : IsNilpotent z) (i : Fin 2) : IsNilpotent (evalTwo k y z hyz (X i)) := by
  fin_cases i
  · simpa [evalTwo_X_zero] using hy
  · simpa [evalTwo_X_one] using hz

theorem evalTwo_comm (y z : A) (hyz : Commute y z) (p q : MvPolynomial (Fin 2) k) :
    evalTwo k y z hyz p * evalTwo k y z hyz q = evalTwo k y z hyz q * evalTwo k y z hyz p := by
  rw [← map_mul, ← map_mul, mul_comm]

end EvalTwo

/-! ## Inverses from isomorphisms of matrices with one summand -/

section SumInvMat

variable {D : Type*} [Category D] [Preadditive D]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- A morphism as a morphism of `Mat_ D` between objects with one summand. -/
def matOne {X Y : D} (f : X ⟶ Y) : (⟨Unit, fun _ => X⟩ : Mat_ D) ⟶ ⟨Unit, fun _ => Y⟩ :=
  fun _ _ => f

/-- The morphisms `g m : X ⟶ Z`, `m < n`, as one morphism `X ⟶ Z^{⊕ n}` of `Mat_ D`. -/
def matRow {X Z : D} (g : ℕ → (X ⟶ Z)) (n : ℕ) :
    (⟨Unit, fun _ => X⟩ : Mat_ D) ⟶ oMat Z (Fin n) :=
  fun _ m => g m

/-- The morphisms `g m : Z ⟶ X`, `m < n`, as one morphism `Z^{⊕ n} ⟶ X` of `Mat_ D`. -/
def matCol {X Z : D} (g : ℕ → (Z ⟶ X)) (n : ℕ) :
    oMat Z (Fin n) ⟶ (⟨Unit, fun _ => X⟩ : Mat_ D) :=
  fun m _ => g m

theorem matOne_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    matOne f ≫ matOne g = matOne (f ≫ g) := by
  refine Mat_.hom_ext _ _ fun i j => ?_
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

theorem matOne_id (X : D) : matOne (𝟙 X) = 𝟙 (⟨Unit, fun _ => X⟩ : Mat_ D) := by
  refine Mat_.hom_ext _ _ fun i j => ?_
  rw [Subsingleton.elim i j, Mat_.id_apply_self]
  rfl

theorem isIso_matOne {X Y : D} (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X)
    (hgf : g ≫ f = 𝟙 Y) : IsIso (matOne f) :=
  ⟨⟨matOne g, by rw [matOne_comp, hfg, matOne_id], by rw [matOne_comp, hgf, matOne_id]⟩⟩

theorem mat_zero_apply {M N : Mat_ D} (i : M.ι) (j : N.ι) : (0 : M ⟶ N) i j = 0 := rfl

theorem matOne_comp_apply {X Y : D} {N : Mat_ D} (f : X ⟶ Y)
    (P : (⟨Unit, fun _ => Y⟩ : Mat_ D) ⟶ N) (j : N.ι) : (matOne f ≫ P) () j = f ≫ P () j := by
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

theorem comp_matOne_apply {X Y : D} {M : Mat_ D} (P : M ⟶ (⟨Unit, fun _ => X⟩ : Mat_ D))
    (f : X ⟶ Y) (i : M.ι) : (P ≫ matOne f) i () = P i () ≫ f := by
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

theorem comp_matRow_apply {X Z : D} {M : Mat_ D} (P : M ⟶ (⟨Unit, fun _ => X⟩ : Mat_ D))
    (g : ℕ → (X ⟶ Z)) (n : ℕ) (i : M.ι) (m : Fin n) :
    (P ≫ matRow g n) i m = P i () ≫ g m := by
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

theorem matRow_comp_apply {X Z : D} {N : Mat_ D} (g : ℕ → (X ⟶ Z)) (n : ℕ)
    (Q : oMat Z (Fin n) ⟶ N) (j : N.ι) :
    (matRow g n ≫ Q) () j = ∑ m : Fin n, g m ≫ Q m j :=
  Mat_.comp_apply _ _ _ _

theorem matCol_comp_apply {X Z : D} {N : Mat_ D} (g : ℕ → (Z ⟶ X)) (n : ℕ)
    (P : (⟨Unit, fun _ => X⟩ : Mat_ D) ⟶ N) (m : Fin n) (j : N.ι) :
    (matCol g n ≫ P) m j = g m ≫ P () j := by
  rw [Mat_.comp_apply, Fintype.sum_unique]
  rfl

theorem comp_matCol_apply {X Z : D} {M : Mat_ D} (g : ℕ → (Z ⟶ X)) (n : ℕ)
    (P : M ⟶ oMat Z (Fin n)) (i : M.ι) :
    (P ≫ matCol g n) i () = ∑ m : Fin n, P i m ≫ g m :=
  Mat_.comp_apply _ _ _ _

theorem oMat_id_apply {Z : D} {n : ℕ} (m m' : ℕ) (hm : m < n) (hm' : m' < n) :
    (𝟙 (oMat Z (Fin n)) : oMat Z (Fin n) ⟶ oMat Z (Fin n)) ⟨m, hm⟩ ⟨m', hm'⟩ =
      if m = m' then 𝟙 Z else 0 := by
  by_cases hmm : m = m'
  · subst hmm
    rw [Mat_.id_apply_self]
    simp
  · rw [Mat_.id_apply_of_ne _ _ _ (fun h => hmm (congrArg Fin.val h))]
    simp [hmm]

/-- **A sum inverse from an isomorphism in `Mat_`**: if `(f, g) : X ⟶ Y ⊕ Z^{⊕ n}` is invertible
in the additive envelope, then `f` has a sum inverse with respect to `g` (`SumInvTo`). -/
def SumInvTo.ofIsIsoLift {X Y Z : D} (f : X ⟶ Y) (g : ℕ → (X ⟶ Z)) (n : ℕ)
    (hI : IsIso (biprod.lift (matOne f) (matRow g n))) : SumInvTo f g n :=
  let K := inv (biprod.lift (matOne f) (matRow g n))
  have h1 : biprod.lift (matOne f) (matRow g n) ≫ K = 𝟙 _ := IsIso.hom_inv_id _
  have h2 : K ≫ biprod.lift (matOne f) (matRow g n) = 𝟙 _ := IsIso.inv_hom_id _
  have e0 : matOne f ≫ (biprod.inl ≫ K) + matRow g n ≫ (biprod.inr ≫ K) = 𝟙 _ := by
    rw [← h1, biprod.lift_eq, Preadditive.add_comp, Category.assoc, Category.assoc]
  have eF : (biprod.inl ≫ K) ≫ matOne f = 𝟙 _ := by
    have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.fst) h2
    simpa only [Category.assoc, biprod.lift_fst, Category.id_comp, biprod.inl_fst] using this
  have eG : (biprod.inl ≫ K) ≫ matRow g n = 0 := by
    have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.snd) h2
    simpa only [Category.assoc, biprod.lift_snd, Category.id_comp, biprod.inl_snd] using this
  have eF' : (biprod.inr ≫ K) ≫ matOne f = 0 := by
    have := congrArg (fun φ => biprod.inr ≫ φ ≫ biprod.fst) h2
    simpa only [Category.assoc, biprod.lift_fst, Category.id_comp, biprod.inr_fst] using this
  have eG' : (biprod.inr ≫ K) ≫ matRow g n = 𝟙 _ := by
    have := congrArg (fun φ => biprod.inr ≫ φ ≫ biprod.snd) h2
    simpa only [Category.assoc, biprod.lift_snd, Category.id_comp, biprod.inr_snd] using this
  { f' := (biprod.inl ≫ K) () ()
    g' := fun m => if hm : m < n then (biprod.inr ≫ K) ⟨m, hm⟩ () else 0
    total := by
      have e := congrArg (fun φ => φ () ()) e0
      simp only [Mat_.add_apply, matOne_comp_apply, matRow_comp_apply, Mat_.id_apply_self] at e
      rw [← e, ← Fin.sum_univ_eq_sum_range]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [m.2, ↓reduceDIte]
    ff := by
      have e := congrArg (fun φ => φ () ()) eF
      simp only [comp_matOne_apply, Mat_.id_apply_self] at e
      exact e
    fg := fun m hm => by
      have e := congrArg (fun φ => φ () ⟨m, hm⟩) eG
      simp only [comp_matRow_apply] at e
      exact e
    gf := fun m hm => by
      have e := congrArg (fun φ => φ ⟨m, hm⟩ ()) eF'
      simp only [comp_matOne_apply] at e
      simp only [hm, ↓reduceDIte]
      exact e
    gg := fun m m' hm hm' => by
      have e := congrArg (fun φ => φ ⟨m, hm⟩ ⟨m', hm'⟩) eG'
      simp only [comp_matRow_apply] at e
      simp only [hm, ↓reduceDIte]
      exact e.trans (oMat_id_apply m m' hm hm') }

/-- **A sum inverse from an isomorphism in `Mat_`**: if `(f, g) : Y ⊕ Z^{⊕ n} ⟶ X` is invertible
in the additive envelope, then `f` has a sum inverse with respect to `g` (`SumInvFrom`). -/
def SumInvFrom.ofIsIsoDesc {X Y Z : D} (f : Y ⟶ X) (g : ℕ → (Z ⟶ X)) (n : ℕ)
    (hI : IsIso (biprod.desc (matOne f) (matCol g n))) : SumInvFrom f g n :=
  let K := inv (biprod.desc (matOne f) (matCol g n))
  have h1 : biprod.desc (matOne f) (matCol g n) ≫ K = 𝟙 _ := IsIso.hom_inv_id _
  have h2 : K ≫ biprod.desc (matOne f) (matCol g n) = 𝟙 _ := IsIso.inv_hom_id _
  have e0 : (K ≫ biprod.fst) ≫ matOne f + (K ≫ biprod.snd) ≫ matCol g n = 𝟙 _ := by
    rw [← h2, biprod.desc_eq, Preadditive.comp_add, Category.assoc, Category.assoc]
  have eF : matOne f ≫ K ≫ biprod.fst = 𝟙 _ := by
    have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.fst) h1
    simpa only [Category.assoc, biprod.inl_desc_assoc, Category.id_comp, biprod.inl_fst]
      using this
  have eG : matOne f ≫ K ≫ biprod.snd = 0 := by
    have := congrArg (fun φ => biprod.inl ≫ φ ≫ biprod.snd) h1
    simpa only [Category.assoc, biprod.inl_desc_assoc, Category.id_comp, biprod.inl_snd]
      using this
  have eF' : matCol g n ≫ K ≫ biprod.fst = 0 := by
    have := congrArg (fun φ => biprod.inr ≫ φ ≫ biprod.fst) h1
    simpa only [Category.assoc, biprod.inr_desc_assoc, Category.id_comp, biprod.inr_fst]
      using this
  have eG' : matCol g n ≫ K ≫ biprod.snd = 𝟙 _ := by
    have := congrArg (fun φ => biprod.inr ≫ φ ≫ biprod.snd) h1
    simpa only [Category.assoc, biprod.inr_desc_assoc, Category.id_comp, biprod.inr_snd]
      using this
  { f' := (K ≫ biprod.fst) () ()
    g' := fun m => if hm : m < n then (K ≫ biprod.snd) () ⟨m, hm⟩ else 0
    total := by
      have e := congrArg (fun φ => φ () ()) e0
      simp only [Mat_.add_apply, comp_matOne_apply, comp_matCol_apply, Mat_.id_apply_self] at e
      rw [← e, ← Fin.sum_univ_eq_sum_range]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [m.2, ↓reduceDIte]
    ff := by
      have e := congrArg (fun φ => φ () ()) eF
      simp only [matOne_comp_apply, Mat_.id_apply_self] at e
      exact e
    fg := fun m hm => by
      have e := congrArg (fun φ => φ () ⟨m, hm⟩) eG
      simp only [matOne_comp_apply] at e
      simp only [hm, ↓reduceDIte]
      exact e
    gf := fun m hm => by
      have e := congrArg (fun φ => φ ⟨m, hm⟩ ()) eF'
      simp only [matCol_comp_apply] at e
      exact e
    gg := fun m m' hm hm' => by
      have e := congrArg (fun φ => φ ⟨m, hm⟩ ⟨m', hm'⟩) eG'
      simp only [matCol_comp_apply] at e
      simp only [hm', ↓reduceDIte]
      exact e.trans (oMat_id_apply m m' hm hm') }

end SumInvMat

/-! ## Matrices of coefficients of powers -/

section PowCoeff

variable {k : Type*} [Field k]

/-- The matrix `(m, t) ↦ [Xᵐ] fᵗ`, `m, t < N`. -/
def powCoeffMatrix (f : Polynomial k) (N : ℕ) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun m t => (f ^ (t : ℕ)).coeff m

/-- For `f(0) = 0`, `(m, t) ↦ [Xᵐ] fᵗ` is lower triangular with diagonal `f'(0)ᵗ`. -/
theorem det_powCoeffMatrix {f : Polynomial k} (hf0 : f.coeff 0 = 0) (N : ℕ) :
    (powCoeffMatrix f N).det = ∏ t : Fin N, f.coeff 1 ^ (t : ℕ) := by
  rw [Matrix.det_of_isLowerTriangular (powCoeffMatrix f N) (fun i j hij => coeff_pow_of_lt hf0 hij)]
  exact Finset.prod_congr rfl fun t _ => coeff_pow_self hf0 t

theorem isUnit_det_powCoeffMatrix {f : Polynomial k} (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 ≠ 0)
    (N : ℕ) : IsUnit (powCoeffMatrix f N).det := by
  rw [det_powCoeffMatrix hf0, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ hf1

/-- An invertible square matrix, reindexed along two equivalences and mapped to a semiring. -/
theorem map_submatrix_mul_inv {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {S : Type*} [Semiring S] (φ : k →+* S) (V : Matrix (Fin N) (Fin N) k)
    (hV : IsUnit V.det) (e₁ : ι ≃ Fin N) (e₂ : κ ≃ Fin N) :
    (V.submatrix e₁ e₂).map φ * (V⁻¹.submatrix e₂ e₁).map φ = 1 ∧
      (V⁻¹.submatrix e₂ e₁).map φ * (V.submatrix e₁ e₂).map φ = 1 := by
  constructor
  · rw [← Matrix.map_mul, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hV,
      Matrix.submatrix_one_equiv, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [← Matrix.map_mul, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hV,
      Matrix.submatrix_one_equiv, Matrix.map_one _ (map_zero φ) (map_one φ)]

end PowCoeff

/-! ## The reparametrized Rouquier datum -/

section Reparam

open RouqCoproduct RouqSl2Generic

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

section Nil

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C}

theorem powComp_eq_zero_of_le {D : Type*} [Category D] [Preadditive D] {X : D} {x : X ⟶ X}
    {n m : ℕ} (hx : powComp x n = 0) (hm : n ≤ m) : powComp x m = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [← powComp_comp_powComp, hx, Limits.zero_comp]

theorem isNilpotent_whiskerLeft (f : a ⟶ b) {g : b ⟶ c} (x : g ⟶ g) {n : ℕ}
    (hx : powComp x n = 0) : IsNilpotent (show End (f ≫ g) from f ◁ x) :=
  ⟨n, by
    rw [← powComp_eq_pow', ← RightwardCrossing.whiskerLeft_powComp, hx]
    exact AdditiveWhiskering.whiskerLeft_zero _ _ _⟩

theorem isNilpotent_whiskerRight {f : a ⟶ b} (x : f ⟶ f) (g : b ⟶ c) {n : ℕ}
    (hx : powComp x n = 0) : IsNilpotent (show End (f ≫ g) from x ▷ g) :=
  ⟨n, by
    rw [← powComp_eq_pow', ← RightwardCrossing.powComp_whiskerRight, hx]
    exact AdditiveWhiskering.zero_whiskerRight _ _ _⟩

end Nil

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {k : Type*} [Field k] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (f : b ⟶ c), (postcomp a f).Linear k]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}

namespace RouqLoc

variable (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

variable (k) in
/-- Polynomials in the dots `E₁ ◁ x₂` (`X 0`) and `x₁ ▷ E₂` (`X 1`) of `E₁ ≫ E₂`. -/
def upEval (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) : MvPolynomial (Fin 2) k →ₐ[k] End (E₁ ≫ E₂) :=
  evalTwo k (E₁ ◁ x₂ : End (E₁ ≫ E₂)) (x₁ ▷ E₂) (whisker_exchange x₁ x₂).symm

variable (k) in
/-- Polynomials in the dots `x₂ ▷ R₂` (`X 0`) and `E₂ ◁ x₂'` (`X 1`) of `E₂ ≫ R₂`, where `x₂'` is
the downward dot. -/
def dnEval : MvPolynomial (Fin 2) k →ₐ[k] End (E₂ ≫ R₂) :=
  evalTwo k (x₂ ▷ R₂ : End (E₂ ≫ R₂)) (E₂ ◁ L.dotD₂) (whisker_exchange x₂ L.dotD₂)

variable (k) in
/-- Polynomials in the dots `R₁ ◁ x₁` (`X 0`) and `x₁' ▷ E₁` (`X 1`) of `R₁ ≫ E₁`, where `x₁'` is
the downward dot. -/
def dnEval' : MvPolynomial (Fin 2) k →ₐ[k] End (R₁ ≫ E₁) :=
  evalTwo k (R₁ ◁ x₁ : End (R₁ ≫ E₁)) (L.dotD₁ ▷ E₁) (whisker_exchange L.dotD₁ x₁).symm

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem upEval_X_zero : L.upEval k (X 0) = E₁ ◁ x₂ := evalTwo_X_zero _ _ _
omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem upEval_X_one : L.upEval k (X 1) = x₁ ▷ E₂ := evalTwo_X_one _ _ _
omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem dnEval_X_zero : L.dnEval k (X 0) = x₂ ▷ R₂ := evalTwo_X_zero _ _ _
omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem dnEval_X_one : L.dnEval k (X 1) = E₂ ◁ L.dotD₂ := evalTwo_X_one _ _ _
omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem dnEval'_X_zero : L.dnEval' k (X 0) = R₁ ◁ x₁ := evalTwo_X_zero _ _ _
omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem dnEval'_X_one : L.dnEval' k (X 1) = L.dotD₁ ▷ E₁ := evalTwo_X_one _ _ _

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem upEval_comm (p q : MvPolynomial (Fin 2) k) :
    L.upEval k p * L.upEval k q = L.upEval k q * L.upEval k p := evalTwo_comm _ _ _ p q

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem dnEval_comm (p q : MvPolynomial (Fin 2) k) :
    L.dnEval k p * L.dnEval k q = L.dnEval k q * L.dnEval k p := evalTwo_comm _ _ _ p q

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem dnEval'_comm (p q : MvPolynomial (Fin 2) k) :
    L.dnEval' k p * L.dnEval' k q = L.dnEval' k q * L.dnEval' k p := evalTwo_comm _ _ _ p q

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem ncEval_eq_upEval (p : MvPolynomial (Fin 2) k) :
    KLR.ncEval (![E₁ ◁ x₂, x₁ ▷ E₂] : Fin 2 → End (E₁ ≫ E₂)) p = L.upEval k p :=
  ncEval_eq_evalTwo _ _ _ p

/-! ### The closed diagrams -/

variable (k) in
/-- The span of the closed diagrams `capD i ≫ cupD j`, `i, j < n`. -/
def capCup (n : ℕ) : Submodule k (R₁ ≫ E₁ ⟶ E₂ ≫ R₂) :=
  Submodule.span k (Set.range fun ij : Fin n × Fin n => L.capD ij.1 ≫ L.cupD ij.2)

omit [AdditiveWhiskering C] in
theorem cupD_dotD₂ (j : ℕ) : L.cupD j ≫ E₂ ◁ L.dotD₂ = L.cupD (j + 1) := by
  rw [cupD, cupD, Category.assoc, ← whisker_exchange, ← Category.assoc, L.unit_dotD₂,
    Category.assoc, ← comp_whiskerRight, comp_powComp]

omit [AdditiveWhiskering C] in
theorem dotD₁_capD (i : ℕ) : L.dotD₁ ▷ E₁ ≫ L.capD i = L.capD (i + 1) := by
  rw [capD, capD, ← Category.assoc, ← whisker_exchange, Category.assoc, L.dotD₁_counit,
    ← Category.assoc, ← whiskerLeft_comp, ← powComp_succ]

theorem isNilpotent_dotD₂ {n : ℕ} (hx₂ : powComp x₂ n = 0) :
    powComp L.dotD₂ n = 0 := by
  rw [dotD₂, ← rightMate_pow, hx₂]
  exact (rightMateAddEquiv adj₂).map_zero

theorem isNilpotent_dotD₁ {n : ℕ} (hx₁ : powComp x₁ n = 0) :
    powComp L.dotD₁ n = 0 := by
  rw [dotD₁, ← rightMate_pow, hx₁]
  exact (rightMateAddEquiv adj₁).map_zero

variable {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0)

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ hx₂ in
theorem capD_cupD_mem (i j : ℕ) : L.capD i ≫ L.cupD j ∈ L.capCup k n := by
  by_cases hi : i < n
  · by_cases hj : j < n
    · exact Submodule.subset_span ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
    · have : L.cupD j = 0 := by
        rw [cupD, powComp_eq_zero_of_le hx₂ (not_lt.mp hj), AdditiveWhiskering.zero_whiskerRight,
          Limits.comp_zero]
      rw [this, Limits.comp_zero]
      exact zero_mem _
  · have : L.capD i = 0 := by
      rw [capD, powComp_eq_zero_of_le hx₁ (not_lt.mp hi), AdditiveWhiskering.whiskerLeft_zero,
        Limits.zero_comp]
    rw [this, Limits.zero_comp]
    exact zero_mem _

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem mem_capCup_of_map {Λ : (R₁ ≫ E₁ ⟶ E₂ ≫ R₂) →ₗ[k] (R₁ ≫ E₁ ⟶ E₂ ≫ R₂)}
    (hΛ : ∀ i j : ℕ, Λ (L.capD i ≫ L.cupD j) ∈ L.capCup k n) {u : R₁ ≫ E₁ ⟶ E₂ ≫ R₂}
    (hu : u ∈ L.capCup k n) : Λ u ∈ L.capCup k n :=
  (Submodule.span_le (p := (L.capCup k n).comap Λ)).mpr
    (by rintro _ ⟨ij, rfl⟩; exact hΛ ij.1 ij.2) hu

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ hx₂ in
theorem comp_dnEval_X_mem (i : Fin 2) {u : R₁ ≫ E₁ ⟶ E₂ ≫ R₂} (hu : u ∈ L.capCup k n) :
    u ≫ L.dnEval k (X i) ∈ L.capCup k n := by
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · rw [dnEval_X_zero]
    refine L.mem_capCup_of_map (Λ := Linear.rightComp k _ (x₂ ▷ R₂)) (fun i j => ?_) hu
    rw [Linear.rightComp_apply, Category.assoc, L.cupD_dot]
    exact L.capD_cupD_mem hx₁ hx₂ i (j + 1)
  · rw [dnEval_X_one]
    refine L.mem_capCup_of_map (Λ := Linear.rightComp k _ (E₂ ◁ L.dotD₂)) (fun i j => ?_) hu
    rw [Linear.rightComp_apply, Category.assoc, L.cupD_dotD₂]
    exact L.capD_cupD_mem hx₁ hx₂ i (j + 1)

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ hx₂ in
theorem dnEval'_X_comp_mem (i : Fin 2) {u : R₁ ≫ E₁ ⟶ E₂ ≫ R₂} (hu : u ∈ L.capCup k n) :
    L.dnEval' k (X i) ≫ u ∈ L.capCup k n := by
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · rw [dnEval'_X_zero]
    refine L.mem_capCup_of_map (Λ := Linear.leftComp k _ (R₁ ◁ x₁)) (fun i j => ?_) hu
    rw [Linear.leftComp_apply, ← Category.assoc, L.dot_capD]
    exact L.capD_cupD_mem hx₁ hx₂ (i + 1) j
  · rw [dnEval'_X_one]
    refine L.mem_capCup_of_map (Λ := Linear.leftComp k _ (L.dotD₁ ▷ E₁)) (fun i j => ?_) hu
    rw [Linear.leftComp_apply, ← Category.assoc, L.dotD₁_capD]
    exact L.capD_cupD_mem hx₁ hx₂ (i + 1) j

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ hx₂ in
theorem comp_dnEval_mem (p : MvPolynomial (Fin 2) k) :
    ∀ u ∈ L.capCup k n, u ≫ L.dnEval k p ∈ L.capCup k n := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    intro u hu
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    change u ≫ (r • 𝟙 _) ∈ _
    rw [Linear.comp_smul, Category.comp_id]
    exact Submodule.smul_mem _ r hu
  | add p q hp hq =>
    intro u hu
    rw [map_add]
    change u ≫ ((L.dnEval k p : E₂ ≫ R₂ ⟶ E₂ ≫ R₂) + L.dnEval k q) ∈ _
    rw [Preadditive.comp_add]
    exact add_mem (hp u hu) (hq u hu)
  | mul_X p i hp =>
    intro u hu
    rw [map_mul, End.mul_def, ← Category.assoc]
    exact hp _ (L.comp_dnEval_X_mem hx₁ hx₂ i hu)

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ hx₂ in
theorem dnEval'_comp_mem (p : MvPolynomial (Fin 2) k) :
    ∀ u ∈ L.capCup k n, L.dnEval' k p ≫ u ∈ L.capCup k n := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    intro u hu
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    change (r • 𝟙 _) ≫ u ∈ _
    rw [Linear.smul_comp, Category.id_comp]
    exact Submodule.smul_mem _ r hu
  | add p q hp hq =>
    intro u hu
    rw [map_add]
    change ((L.dnEval' k p : R₁ ≫ E₁ ⟶ R₁ ≫ E₁) + L.dnEval' k q) ≫ u ∈ _
    rw [Preadditive.add_comp]
    exact add_mem (hp u hu) (hq u hu)
  | mul_X p i hp =>
    intro u hu
    rw [map_mul, End.mul_def, Category.assoc]
    exact L.dnEval'_X_comp_mem hx₁ hx₂ i (hp u hu)

/-! ### The rightward crossing of `τ ∘ φ(p)` -/

include hx₁ hx₂ in
/-- `σ(τ ∘ p(E₁ ◁ x₂, x₁ ▷ E₂)) ≡ σ ∘ p(x₂ ▷ R₂, E₂ ◁ x₂')` modulo closed diagrams. -/
theorem sigma_upEval_sub_mem (p : MvPolynomial (Fin 2) k) :
    RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit - L.sig ≫ L.dnEval k p ∈
      L.capCup k n := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change RightwardCrossing.sigma adj₂.unit (τ ≫ (r • 𝟙 _)) adj₁.counit - L.sig ≫ (r • 𝟙 _) ∈ _
    rw [Linear.comp_smul, Linear.comp_smul, Category.comp_id, Category.comp_id, sigma_smul, sig,
      sub_self]
    exact zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add]
    change RightwardCrossing.sigma adj₂.unit
        (τ ≫ ((L.upEval k p : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) + L.upEval k q)) adj₁.counit -
      L.sig ≫ ((L.dnEval k p : E₂ ≫ R₂ ⟶ E₂ ≫ R₂) + L.dnEval k q) ∈ _
    rw [Preadditive.comp_add, Preadditive.comp_add, sigma_add]
    convert add_mem hp hq using 1
    abel
  | mul_X p i hp =>
    rw [mul_comm, map_mul, map_mul, End.mul_def, End.mul_def, ← Category.assoc τ]
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · rw [upEval_X_zero, dnEval_X_zero, sigma_comp_right, ← Category.assoc,
        ← Preadditive.sub_comp]
      have := L.comp_dnEval_X_mem hx₁ hx₂ 0 hp
      rwa [dnEval_X_zero] at this
    · rw [upEval_X_one, dnEval_X_one, ← conj_comp_sigma,
        show conjugateEquiv adj₁ adj₁ x₁ = L.dotD₁ from rfl]
      have hc : L.dnEval k p ≫ E₂ ◁ L.dotD₂ = E₂ ◁ L.dotD₂ ≫ L.dnEval k p := by
        rw [← L.dnEval_X_one (k := k)]; exact L.dnEval_comm (X 1) p
      have e : L.dotD₁ ▷ E₁ ≫
            RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit -
          L.sig ≫ L.dnEval k p ≫ E₂ ◁ L.dotD₂ =
          L.dotD₁ ▷ E₁ ≫ (RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit -
            L.sig ≫ L.dnEval k p) -
          (L.sig ≫ E₂ ◁ L.dotD₂ - L.dotD₁ ▷ E₁ ≫ L.sig) ≫ L.dnEval k p := by
        rw [hc]
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
        abel
      have h00 := L.capD_cupD_mem (k := k) hx₁ hx₂ 0 0
      rw [capD_zero, cupD_zero] at h00
      rw [e, L.sig_dotD_sub]
      refine sub_mem ?_ (L.comp_dnEval_mem hx₁ hx₂ p _ h00)
      have := L.dnEval'_X_comp_mem hx₁ hx₂ 1 hp
      rwa [dnEval'_X_one] at this

include hx₁ hx₂ in
/-- `σ(τ ∘ p(E₁ ◁ x₂, x₁ ▷ E₂)) ≡ p(R₁ ◁ x₁, x₁' ▷ E₁) ∘ σ` modulo closed diagrams. -/
theorem sigma_upEval_sub_mem' (p : MvPolynomial (Fin 2) k) :
    RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit - L.dnEval' k p ≫ L.sig ∈
      L.capCup k n := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change RightwardCrossing.sigma adj₂.unit (τ ≫ (r • 𝟙 _)) adj₁.counit - (r • 𝟙 _) ≫ L.sig ∈ _
    rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp, sigma_smul, sig,
      sub_self]
    exact zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add]
    change RightwardCrossing.sigma adj₂.unit
        (τ ≫ ((L.upEval k p : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) + L.upEval k q)) adj₁.counit -
      ((L.dnEval' k p : R₁ ≫ E₁ ⟶ R₁ ≫ E₁) + L.dnEval' k q) ≫ L.sig ∈ _
    rw [Preadditive.comp_add, Preadditive.add_comp, sigma_add]
    convert add_mem hp hq using 1
    abel
  | mul_X p i hp =>
    rw [mul_comm, map_mul, map_mul, End.mul_def, End.mul_def, ← Category.assoc τ]
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · rw [upEval_X_zero, dnEval'_X_zero, sigma_comp_right]
      have e : RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit ≫ x₂ ▷ R₂ -
          (L.dnEval' k p ≫ R₁ ◁ x₁) ≫ L.sig =
          (RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit -
            L.dnEval' k p ≫ L.sig) ≫ x₂ ▷ R₂ +
          L.dnEval' k p ≫ L.capD 0 ≫ L.cupD 0 := by
        rw [Category.assoc, L.dot_sig]
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
        abel
      rw [e]
      refine add_mem ?_ (L.dnEval'_comp_mem hx₁ hx₂ p _ (L.capD_cupD_mem hx₁ hx₂ 0 0))
      have := L.comp_dnEval_X_mem hx₁ hx₂ 0 hp
      rwa [dnEval_X_zero] at this
    · rw [upEval_X_one, dnEval'_X_one, ← conj_comp_sigma,
        show conjugateEquiv adj₁ adj₁ x₁ = L.dotD₁ from rfl]
      have hc : L.dnEval' k p ≫ L.dotD₁ ▷ E₁ = L.dotD₁ ▷ E₁ ≫ L.dnEval' k p := by
        rw [← L.dnEval'_X_one (k := k)]; exact L.dnEval'_comm (X 1) p
      have e : L.dotD₁ ▷ E₁ ≫
            RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit -
          (L.dnEval' k p ≫ L.dotD₁ ▷ E₁) ≫ L.sig =
          L.dotD₁ ▷ E₁ ≫ (RightwardCrossing.sigma adj₂.unit (τ ≫ L.upEval k p) adj₁.counit -
            L.dnEval' k p ≫ L.sig) := by
        rw [hc, Preadditive.comp_sub, Category.assoc]
      rw [e]
      have := L.dnEval'_X_comp_mem hx₁ hx₂ 1 hp
      rwa [dnEval'_X_one] at this

/-! ### Dots and caps under reparametrization -/

omit [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ in
theorem whiskerLeft_aeval_counit (g : Polynomial k) :
    R₁ ◁ (Polynomial.aeval (show End E₁ from x₁) g) ≫ adj₁.counit =
      ∑ m ∈ range n, g.coeff m • L.capD m := by
  rw [aeval_eq_sum_range_of_pow_eq_zero (n := n) (by rw [← powComp_eq_pow']; exact hx₁),
    show R₁ ◁ (∑ m ∈ range n, g.coeff m • (show End E₁ from x₁) ^ m) =
      ∑ m ∈ range n, R₁ ◁ (g.coeff m • (show End E₁ from x₁) ^ m) from
      map_sum (AdditiveWhiskering.whiskerLeftAddHom R₁ E₁ E₁) _ _, Preadditive.sum_comp]
  refine sum_congr rfl fun m _ => ?_
  change R₁ ◁ (_ • _) ≫ _ = _
  rw [whiskerLeft_smul', Linear.smul_comp, ← powComp_eq_pow']
  rfl

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)] in
include hx₂ in
theorem unit_aeval_whiskerRight (g : Polynomial k) :
    adj₂.unit ≫ (Polynomial.aeval (show End E₂ from x₂) g) ▷ R₂ =
      ∑ m ∈ range n, g.coeff m • L.cupD m := by
  rw [aeval_eq_sum_range_of_pow_eq_zero (n := n) (by rw [← powComp_eq_pow']; exact hx₂),
    show (∑ m ∈ range n, g.coeff m • (show End E₂ from x₂) ^ m) ▷ R₂ =
      ∑ m ∈ range n, (g.coeff m • (show End E₂ from x₂) ^ m) ▷ R₂ from
      map_sum (AdditiveWhiskering.whiskerRightAddHom E₂ E₂ R₂) _ _, Preadditive.comp_sum]
  refine sum_congr rfl fun m _ => ?_
  change _ ≫ (_ • _) ▷ R₂ = _
  rw [smul_whiskerRight', Linear.comp_smul, ← powComp_eq_pow']
  rfl

omit [AdditiveWhiskering C] [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem powComp_aeval {X : C} {Y : C} {E : X ⟶ Y} (x : E ⟶ E) (g : Polynomial k) (t : ℕ) :
    powComp (Polynomial.aeval (show End E from x) g) t =
      Polynomial.aeval (show End E from x) (g ^ t) := by
  rw [powComp_eq_pow', map_pow]

/-! ### The reparametrized crossing -/

/-- The crossing `τ ∘ ∂f(E₁ ◁ x₂, x₁ ▷ E₂)⁻¹` of the reparametrized datum, with
`∂f = (f(X₀) - f(X₁)) / (X₀ - X₁)`. -/
def reparamCross (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (f : Polynomial k) : E₁ ≫ E₂ ⟶ E₁ ≫ E₂ :=
  τ ≫ Ring.inverse (M₀ := End (E₁ ≫ E₂))
    (KLR.ncEval (![E₁ ◁ x₂, x₁ ▷ E₂] : Fin 2 → End (E₁ ≫ E₂))
      (ddiff 0 1 (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) f)))

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)]
  [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
include hx₁ hx₂ in
theorem exists_reparamCross {f : Polynomial k} (hf1 : f.coeff 1 ≠ 0) :
    ∃ p' : MvPolynomial (Fin 2) k,
      L.upEval k (ddiff 0 1 (Polynomial.aeval (X 0) f)) * L.upEval k p' = 1 ∧
      L.upEval k p' * L.upEval k (ddiff 0 1 (Polynomial.aeval (X 0) f)) = 1 ∧
      L.reparamCross f = τ ≫ L.upEval k p' ∧ constantCoeff p' ≠ 0 := by
  obtain ⟨p', h1, h2, h3⟩ := exists_inv_of_constantCoeff_ne_zero (L.upEval k)
    (isNilpotent_evalTwo_X _ (isNilpotent_whiskerLeft E₁ x₂ hx₂)
      (isNilpotent_whiskerRight x₁ E₂ hx₁)) _
    (by rw [constantCoeff_ddiff_aeval]; exact hf1)
  refine ⟨p', h1, h2, ?_, h3⟩
  rw [reparamCross, ncEval_eq_upEval]
  congr 1
  exact Ring.inverse_unit ⟨_, _, h1, h2⟩

omit [∀ (a b c : C) (f : b ⟶ c), Functor.Linear k (postcomp a f)] in
theorem whiskerLeft_aeval_eq (f : Polynomial k) :
    (E₁ ◁ (Polynomial.aeval (show End E₂ from x₂) f) : End (E₁ ≫ E₂)) =
      L.upEval k (Polynomial.aeval (X 0) f) := by
  calc (E₁ ◁ (Polynomial.aeval (show End E₂ from x₂) f) : End (E₁ ≫ E₂)) =
        endWL k E₁ E₂ (Polynomial.aeval (show End E₂ from x₂) f) := rfl
    _ = Polynomial.aeval (endWL k E₁ E₂ x₂) f := (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = Polynomial.aeval (L.upEval k (X 0)) f := by rw [upEval_X_zero]; rfl
    _ = L.upEval k (Polynomial.aeval (X 0) f) := Polynomial.aeval_algHom_apply _ _ _

omit [∀ (a b c : C) (f : a ⟶ b), Functor.Linear k (precomp c f)] in
theorem aeval_whiskerRight_eq (f : Polynomial k) :
    ((Polynomial.aeval (show End E₁ from x₁) f) ▷ E₂ : End (E₁ ≫ E₂)) =
      L.upEval k (Polynomial.aeval (X 1) f) := by
  calc ((Polynomial.aeval (show End E₁ from x₁) f) ▷ E₂ : End (E₁ ≫ E₂)) =
        endWR k E₁ E₂ (Polynomial.aeval (show End E₁ from x₁) f) := rfl
    _ = Polynomial.aeval (endWR k E₁ E₂ x₁) f := (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = Polynomial.aeval (L.upEval k (X 1)) f := by rw [upEval_X_one]; rfl
    _ = L.upEval k (Polynomial.aeval (X 1) f) := Polynomial.aeval_algHom_apply _ _ _

/-! ### Rouquier's map for the reparametrized datum -/

/-- The one-label family of `L`. -/
abbrev single (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) :
    ∀ _ : Unit, RouqLoc adj₁ adj₂ x₁ x₂ τ h := fun _ => _L

omit [AdditiveWhiskering C] in
theorem sigD_single (i j : Unit) : sigD L.single i j = L.sig := by
  cases i; cases j; simp [sigD, diagMat]

include hx₁ hx₂ in
/-- Brundan (1.8) for the reparametrized datum, as an isomorphism in `Mat_`. -/
theorem isIso_reparam_lift {f : Polynomial k} (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 ≠ 0)
    (hh : 0 ≤ h) :
    IsIso (biprod.lift (matOne (RightwardCrossing.sigma adj₂.unit (L.reparamCross f) adj₁.counit))
      (matRow (fun t => R₁ ◁ powComp (Polynomial.aeval (show End E₁ from x₁) f) t ≫ adj₁.counit)
        h.toNat)) := by
  set N := h.toNat
  set n' := n + h.natAbs
  set capsF := fun t => R₁ ◁ powComp (Polynomial.aeval (show End E₁ from x₁) f) t ≫ adj₁.counit
    with hcapsF
  have hx₁' : powComp x₁ n' = 0 := powComp_eq_zero_of_le hx₁ (by omega)
  have hx₂' : powComp x₂ n' = 0 := powComp_eq_zero_of_le hx₂ (by omega)
  obtain ⟨p', -, -, hp', hc'⟩ := L.exists_reparamCross hx₁' hx₂' hf1
  obtain ⟨q, hq1, hq2, -⟩ := exists_inv_of_constantCoeff_ne_zero (L.dnEval k)
    (isNilpotent_evalTwo_X _ (isNilpotent_whiskerRight x₂ R₂ hx₂')
      (isNilpotent_whiskerLeft E₂ L.dotD₂ (L.isNilpotent_dotD₂ hx₂'))) p' hc'
  set σ' := RightwardCrossing.sigma adj₂.unit (L.reparamCross f) adj₁.counit with hσ'
  have hmem : σ' ≫ L.dnEval k q - L.sig ∈ L.capCup k n' := by
    have h0 := L.comp_dnEval_mem hx₁' hx₂' q _ (L.sigma_upEval_sub_mem hx₁' hx₂' p')
    convert h0 using 1
    rw [hσ', hp', Preadditive.sub_comp, Category.assoc L.sig]
    congr 1
    rw [show L.dnEval k p' ≫ L.dnEval k q = 𝟙 _ from hq2, Category.comp_id]
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hmem
  let T : oMat (𝟙 b) (Unit × Fin n') ⟶ oMat (𝟙 b) (Unit × Fin n') :=
    fun q q' => cf (q.2, q'.2) • 𝟙 (𝟙 b)
  let W : oMat (𝟙 b) (Unit × Fin n') ⟶ oMat (𝟙 b) (Fin N) :=
    fun q t => (f ^ (t : ℕ)).coeff q.2 • 𝟙 (𝟙 b)
  have hn : ∀ _ : Unit, h.natAbs ≤ n' := fun _ => by omega
  have : IsEmpty (Neg (fun _ : Unit => h)) :=
    ⟨fun r => by have h' := r.2.isLt; change r.2.val < (-h).toNat at h'; omega⟩
  let e₁ : Pos (fun _ : Unit => h) ≃ Fin N :=
    { toFun := fun p => p.2, invFun := fun m => ⟨(), m⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl }
  let e₂ : Fin N ⊕ Neg (fun _ : Unit => h) ≃ Fin N := Equiv.sumEmpty _ _
  have hS : schurPos b hn T W =
      ((powCoeffMatrix f N).submatrix e₁ e₂).map (algebraMap k (End (𝟙 b))) := by
    simp only [schurPos, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
    ext p y
    rcases y with t | r
    · simp only [Matrix.sub_apply, Matrix.fromCols_apply_inl, Matrix.zero_apply, sub_zero,
        matB0_mul_apply, Matrix.map_apply, Matrix.submatrix_apply, Algebra.algebraMap_eq_smul_one]
      rfl
    · exact isEmptyElim r
  obtain ⟨hCD, hDC⟩ := map_submatrix_mul_inv (algebraMap k (End (𝟙 b))) _
    (isUnit_det_powCoeffMatrix hf0 hf1 N) e₁ e₂
  rw [← hS] at hCD hDC
  have hiso := isIso_lift_of_schur L.single (fun _ => hx₁') (fun _ => hx₂') hn T W hCD hDC
  have e2 : biprod.lift (matOne (σ' ≫ L.dnEval k q)) (matRow capsF N) =
      biprod.lift (sigD L.single + capAll L.single n' ≫ T ≫ cupAll L.single n')
        (capAll L.single n' ≫ W) := by
    congr 1
    · refine Mat_.hom_ext _ _ fun i j => ?_
      rw [Mat_.add_apply, capAll_comp_apply, sigD_single]
      simp_rw [comp_cupAll_apply]
      change σ' ≫ L.dnEval k q = _
      rw [← sub_eq_iff_eq_add', ← hcf, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [T, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    · refine Mat_.hom_ext _ _ fun i t => ?_
      rw [capAll_comp_apply]
      change R₁ ◁ powComp (Polynomial.aeval (show End E₁ from x₁) f) t ≫ adj₁.counit = _
      rw [powComp_aeval, L.whiskerLeft_aeval_counit hx₁',
        ← Fin.sum_univ_eq_sum_range (α := R₁ ≫ E₁ ⟶ 𝟙 b)]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [W, Linear.comp_smul, Category.comp_id]
  have e1 : biprod.lift (matOne σ') (matRow capsF N) =
      biprod.lift (matOne (σ' ≫ L.dnEval k q)) (matRow capsF N) ≫
        biprod.map (matOne (L.dnEval k p')) (𝟙 _) := by
    apply biprod.hom_ext
    · rw [biprod.lift_fst, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, matOne_comp,
        Category.assoc, show L.dnEval k q ≫ L.dnEval k p' = 𝟙 _ from hq1, Category.comp_id]
    · rw [biprod.lift_snd, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
        Category.comp_id]
  rw [e1, e2]
  have : IsIso (matOne (L.dnEval k p')) := isIso_matOne _ (L.dnEval k q) hq2 hq1
  have : IsIso (biprod.map (matOne (L.dnEval k p')) (𝟙 (oMat (𝟙 b) (Fin N)))) :=
    (biprod.mapIso (asIso (matOne (L.dnEval k p'))) (Iso.refl _)).isIso_hom
  infer_instance

include hx₁ hx₂ in
/-- Brundan (1.9) for the reparametrized datum, as an isomorphism in `Mat_`. -/
theorem isIso_reparam_desc {f : Polynomial k} (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 ≠ 0)
    (hh : h ≤ 0) :
    IsIso (biprod.desc (matOne (RightwardCrossing.sigma adj₂.unit (L.reparamCross f) adj₁.counit))
      (matCol (fun t => adj₂.unit ≫ powComp (Polynomial.aeval (show End E₂ from x₂) f) t ▷ R₂)
        (-h).toNat)) := by
  set M := (-h).toNat
  set n' := n + h.natAbs
  set cupsF := fun t => adj₂.unit ≫ powComp (Polynomial.aeval (show End E₂ from x₂) f) t ▷ R₂
    with hcupsF
  have hx₁' : powComp x₁ n' = 0 := powComp_eq_zero_of_le hx₁ (by omega)
  have hx₂' : powComp x₂ n' = 0 := powComp_eq_zero_of_le hx₂ (by omega)
  obtain ⟨p', -, -, hp', hc'⟩ := L.exists_reparamCross hx₁' hx₂' hf1
  obtain ⟨q, hq1, hq2, -⟩ := exists_inv_of_constantCoeff_ne_zero (L.dnEval' k)
    (isNilpotent_evalTwo_X _ (isNilpotent_whiskerLeft R₁ x₁ hx₁')
      (isNilpotent_whiskerRight L.dotD₁ E₁ (L.isNilpotent_dotD₁ hx₁'))) p' hc'
  set σ' := RightwardCrossing.sigma adj₂.unit (L.reparamCross f) adj₁.counit with hσ'
  have hmem : L.dnEval' k q ≫ σ' - L.sig ∈ L.capCup k n' := by
    have h0 := L.dnEval'_comp_mem hx₁' hx₂' q _ (L.sigma_upEval_sub_mem' hx₁' hx₂' p')
    convert h0 using 1
    rw [hσ', hp', Preadditive.comp_sub, ← Category.assoc (L.dnEval' k q)]
    congr 1
    rw [show L.dnEval' k q ≫ L.dnEval' k p' = 𝟙 _ from hq1, Category.id_comp]
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hmem
  let T : oMat (𝟙 b) (Unit × Fin n') ⟶ oMat (𝟙 b) (Unit × Fin n') :=
    fun q q' => cf (q.2, q'.2) • 𝟙 (𝟙 b)
  let W : oMat (𝟙 b) (Fin M) ⟶ oMat (𝟙 b) (Unit × Fin n') :=
    fun t q => (f ^ (t : ℕ)).coeff q.2 • 𝟙 (𝟙 b)
  have hn : ∀ _ : Unit, h.natAbs ≤ n' := fun _ => by omega
  have : IsEmpty (Pos (fun _ : Unit => h)) :=
    ⟨fun r => by have h' := r.2.isLt; change r.2.val < h.toNat at h'; omega⟩
  let e₁ : Neg (fun _ : Unit => h) ≃ Fin M :=
    { toFun := fun p => p.2, invFun := fun m => ⟨(), m⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl }
  let e₂ : Fin M ⊕ Pos (fun _ : Unit => h) ≃ Fin M := Equiv.sumEmpty _ _
  have hS : schurNeg b hn T W =
      ((powCoeffMatrix f M).transpose.submatrix e₂ e₁).map (algebraMap k (End (𝟙 b))) := by
    simp only [schurNeg, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    ext y r
    rcases y with t | p
    · simp only [Matrix.sub_apply, Matrix.fromRows_apply_inl, Matrix.zero_apply, sub_zero,
        mul_matE0_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Algebra.algebraMap_eq_smul_one]
      rfl
    · exact isEmptyElim p
  obtain ⟨hCD, hDC⟩ := map_submatrix_mul_inv (algebraMap k (End (𝟙 b))) _
    (by rw [Matrix.det_transpose]; exact isUnit_det_powCoeffMatrix hf0 hf1 M) e₂ e₁
  rw [← hS] at hCD hDC
  have hiso := isIso_desc_of_schur L.single (fun _ => hx₁') (fun _ => hx₂') hn T W hCD hDC
  have e2 : biprod.desc (matOne (L.dnEval' k q ≫ σ')) (matCol cupsF M) =
      biprod.desc (sigD L.single + capAll L.single n' ≫ T ≫ cupAll L.single n')
        (W ≫ cupAll L.single n') := by
    congr 1
    · refine Mat_.hom_ext _ _ fun i j => ?_
      rw [Mat_.add_apply, capAll_comp_apply, sigD_single]
      simp_rw [comp_cupAll_apply]
      change L.dnEval' k q ≫ σ' = _
      rw [← sub_eq_iff_eq_add', ← hcf, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [T, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    · refine Mat_.hom_ext _ _ fun t j => ?_
      rw [comp_cupAll_apply]
      change adj₂.unit ≫ powComp (Polynomial.aeval (show End E₂ from x₂) f) t ▷ R₂ = _
      rw [powComp_aeval, L.unit_aeval_whiskerRight hx₂',
        ← Fin.sum_univ_eq_sum_range (α := 𝟙 b ⟶ E₂ ≫ R₂)]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [W, Linear.smul_comp, Category.id_comp]
  have e1 : biprod.desc (matOne σ') (matCol cupsF M) =
      biprod.map (matOne (L.dnEval' k p')) (𝟙 _) ≫
        biprod.desc (matOne (L.dnEval' k q ≫ σ')) (matCol cupsF M) := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc, ← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc,
        matOne_comp, ← Category.assoc, show L.dnEval' k p' ≫ L.dnEval' k q = 𝟙 _ from hq2,
        Category.id_comp]
    · rw [biprod.inr_desc, ← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc,
        Category.id_comp]
  rw [e1, e2]
  have : IsIso (matOne (L.dnEval' k p')) := isIso_matOne _ (L.dnEval' k q) hq2 hq1
  have : IsIso (biprod.map (matOne (L.dnEval' k p')) (𝟙 (oMat (𝟙 b) (Fin M)))) :=
    (biprod.mapIso (asIso (matOne (L.dnEval' k p'))) (Iso.refl _)).isIso_hom
  infer_instance

include hx₁ hx₂ in
/-- **Reparametrizing the dots** (Webster, arXiv:1603.06311v3, §2.3, the automorphism of
equation `(a-auto)`, for a polynomial with `f(0) = 0` and `f'(0) ≠ 0`): the dots `f(x₁), f(x₂)`
with the crossing `τ ∘ ∂f(E₁ ◁ x₂, x₁ ▷ E₂)⁻¹` are Rouquier's data at the same weight. -/
def reparam {f : Polynomial k} (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 ≠ 0) :
    RouqLoc adj₁ adj₂ (Polynomial.aeval (show End E₁ from x₁) f)
      (Polynomial.aeval (show End E₂ from x₂) f) (L.reparamCross f) h where
  slide_left := by
    obtain ⟨p', h1, h2, hp', -⟩ := L.exists_reparamCross hx₁ hx₂ hf1
    let t : End (E₁ ≫ E₂) := τ
    have hτ : t * L.upEval k (X 0) - L.upEval k (X 1) * t = 1 := by
      rw [upEval_X_zero, upEval_X_one]; exact L.slide_left
    rw [hp']
    rw [L.whiskerLeft_aeval_eq, L.aeval_whiskerRight_eq]
    change (L.upEval k p' * t) * L.upEval k (Polynomial.aeval (X 0) f) -
      L.upEval k (Polynomial.aeval (X 1) f) * (L.upEval k p' * t) = 1
    rw [← mul_assoc, L.upEval_comm (Polynomial.aeval (X 1) f) p', mul_assoc, mul_assoc, ← mul_sub,
      mul_aeval_sub_aeval_mul _ hτ, h2]
  slide_right := by
    obtain ⟨p', h1, h2, hp', -⟩ := L.exists_reparamCross hx₁ hx₂ hf1
    let t : End (E₁ ≫ E₂) := τ
    have hτ : L.upEval k (X 0) * t - t * L.upEval k (X 1) = 1 := by
      rw [upEval_X_zero, upEval_X_one]; exact L.slide_right
    rw [hp']
    rw [L.whiskerLeft_aeval_eq, L.aeval_whiskerRight_eq]
    change L.upEval k (Polynomial.aeval (X 0) f) * (L.upEval k p' * t) -
      (L.upEval k p' * t) * L.upEval k (Polynomial.aeval (X 1) f) = 1
    rw [← mul_assoc, L.upEval_comm (Polynomial.aeval (X 0) f) p', mul_assoc, mul_assoc, ← mul_sub,
      aeval_mul_sub_mul_aeval _ hτ, h2]
  invPos hh := SumInvTo.ofIsIsoLift _ _ _ (L.isIso_reparam_lift hx₁ hx₂ hf0 hf1 hh)
  invNeg hh := SumInvFrom.ofIsIsoDesc _ _ _ (L.isIso_reparam_desc hx₁ hx₂ hf0 hf1 hh)

end RouqLoc

end Reparam

end Categorification.TwoRep
