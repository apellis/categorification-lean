/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL1

/-!
# Symmetries of KLR algebras

Khovanov–Lauda I (arXiv:0803.4121v2), end of §2.1, observes that flipping diagrams about
a horizontal axis gives a grading-preserving antiinvolution `ψ` of `R(ν)` taking
`1_j R(ν) 1_i` to `1_i R(ν) 1_j` and fixing each `1_i`, and that flipping about a vertical
axis while negating every crossing of two equally labelled strands gives an involution `σ`
of `R(ν)` commuting with `ψ`. We construct both maps from the presentation and verify
these claims.

## Main definitions and results

* `KLRAlgebra.flipH : R(ν) ≃ₐ[k] R(ν)ᵐᵒᵖ` — the horizontal flip, fixing the generators
  `e i`, `x a`, `ψ j`; `KLRAlgebra.hflip a = (flipH a).unop` is the corresponding
  anti-automorphism, with `hflip_mul`, `hflip_hflip` (it has order two) and
  `hflip_e_mul_mul_e` (it takes `e j * a * e i` to `e i * hflip a * e j`).
  This holds for arbitrary data `Q`.
* `KLRAlgebra.sigma : R(ν) ≃ₐ[k] R(ν)` — the vertical flip, sending
  `e i ↦ e (rev i)`, `x a ↦ x (Fin.rev a)` and
  `ψ j * e i ↦ ε • ψ (m - 2 - j) * e (rev i)` with `ε = -1` exactly when `i_j = i_{j+1}`
  (`sigma_ψ_mul_e`). It needs the symmetry hypothesis `hQ : KLRSymm Q`, i.e.
  `Q_{ba}(u, v) = Q_{ab}(v, u)` for `a ≠ b`. We prove `sigma_sigma` (it is an involution)
  and `hflip_sigma` (it commutes with the horizontal flip).
* `klQ_symm` : the simply-laced KL I data satisfy `KLRSymm`.

The (grading-preserving) statement for the flip is not addressed here, as the grading
is defined elsewhere; both maps visibly send generators to homogeneous elements of the
same degree.

Our `ψ j` is the paper's `δ_{j+1}` (the paper uses `ψ` for the antiinvolution); positions
are zero-indexed, so the vertical flip sends position `a` to `m - 1 - a` and the crossing
of strands `j, j + 1` to the crossing of strands `m - 2 - j, m - 1 - j`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite

variable {I : Type*} {k : Type*} [CommRing k]

/-! ### Generalities on `ncEval` and `qbar` -/

section ncEval

theorem ncEval_map {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (φ : A →ₐ[k] B) {n : ℕ} (y : Fin n → A) (p : MvPolynomial (Fin n) k) :
    φ (ncEval y p) = ncEval (fun a => φ (y a)) p := by
  simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow]

theorem ncEval_X_comp {n m : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    ncEval (fun a => (X (f a) : MvPolynomial (Fin m) k)) p = rename f p := by
  conv_rhs => rw [p.as_sum]
  simp only [ncEval, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rename_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_fintype _ _
    (fun _ => pow_zero _), ← List.prod_ofFn, algebraMap_eq]
  rfl

theorem ncEval_algHom_X {B : Type*} [Ring B] [Algebra k B] {n m : ℕ}
    (φ : MvPolynomial (Fin m) k →ₐ[k] B) (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    ncEval (fun a => φ (X (f a))) p = φ (rename f p) := by
  rw [← ncEval_X_comp, ncEval_map]

end ncEval

/-- `Q̄(a, b, c)` is symmetric in `a` and `c`. -/
theorem qbar_rename_rev (Q : MvPolynomial (Fin 2) k) : rename ![2, 1, 0] (qbar Q) = qbar Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [qbar_monomial]
    simp only [map_mul, map_pow, map_sum, rename_C, rename_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [mul_comm]
    congr 2
    omega
  | add p q hp hq => rw [qbar_add, map_add, hp, hq]

/-! ### Reversal of sequences -/

namespace Seq

variable {ν : Multiset I}

/-- The reversed sequence `i_m ⋯ i_1`, i.e. `(rev i)_a = i_{m-1-a}`. -/
def rev (i : Seq ν) : Seq ν := (Fin.revPerm : Perm (Fin (Multiset.card ν))) • i

@[simp] theorem rev_apply (i : Seq ν) (a : Fin (Multiset.card ν)) : i.rev.1 a = i.1 a.rev := rfl

@[simp] theorem rev_rev (i : Seq ν) : i.rev.rev = i :=
  Subtype.ext (funext fun a => by simp)

theorem rev_injective : Function.Injective (rev : Seq ν → Seq ν) :=
  Function.LeftInverse.injective rev_rev

@[simp] theorem rev_inj {i j : Seq ν} : i.rev = j.rev ↔ i = j := rev_injective.eq_iff

theorem rev_bijective : Function.Bijective (rev : Seq ν → Seq ν) :=
  Function.Involutive.bijective rev_rev

end Seq

/-- The symmetry condition `Q_{ba}(u, v) = Q_{ab}(v, u)` for `a ≠ b` on KLR data, needed
for the vertical flip. -/
def KLRSymm (Q : I → I → MvPolynomial (Fin 2) k) : Prop :=
  ∀ a b, a ≠ b → Q b a = rename ![1, 0] (Q a b)

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-! ### Adjacent transpositions acting on sequences -/

theorem sadj_symm (n j : ℕ) : (sadj n j).symm = sadj n j := by
  unfold sadj; split_ifs <;> simp

theorem sadj_mul_self (n j : ℕ) : sadj n j * sadj n j = 1 := by
  unfold sadj; split_ifs <;> simp

theorem sadj_apply_val {n j : ℕ} (h : j + 1 < n) (a : Fin n) :
    (sadj n j a).val = if a.val = j then j + 1 else if a.val = j + 1 then j else a.val := by
  simp only [sadj, dif_pos h, swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

theorem sadj_smul_smul (j : ℕ) (i : Seq ν) : sadj m j • sadj m j • i = i := by
  rw [smul_smul, sadj_mul_self, one_smul]

theorem sadj_smul_apply (j : ℕ) (i : Seq ν) (a : Fin m) :
    (sadj m j • i).1 a = i.1 (sadj m j a) := by
  rw [Seq.smul_apply, sadj_symm]

theorem lbl_congr (i : Seq ν) {a b : Fin m} (h : a.val = b.val) : i.1 a = i.1 b :=
  congrArg i.1 (Fin.ext h)

theorem sadj_smul_eq_self {j : ℕ} (h : j + 1 < m) {i : Seq ν}
    (hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩) : sadj m j • i = i := by
  apply Subtype.ext; funext a
  rw [sadj_smul_apply]
  have hv := sadj_apply_val h a
  split_ifs at hv with h1 h2
  · rw [lbl_congr i (b := ⟨j + 1, h⟩) hv, lbl_congr i (b := ⟨j, by omega⟩) h1]; exact hi.symm
  · rw [lbl_congr i (b := ⟨j, by omega⟩) hv, lbl_congr i (b := ⟨j + 1, h⟩) h2]; exact hi
  · exact lbl_congr i hv

theorem vec2_fx (a b : Fin m) :
    ![fx k ν a, fx k ν b] = fun c => fx k ν (![a, b] c) := by
  funext c; fin_cases c <;> rfl

theorem vec3_fx (a b c : Fin m) :
    ![fx k ν a, fx k ν b, fx k ν c] = fun d => fx k ν (![a, b, c] d) := by
  funext d; fin_cases d <;> rfl

variable [DecidableEq I]

/-! ### Basic consequences of the relations -/

theorem e_mul_ψ (j : ℕ) (i : Seq ν) : (e i * ψ j : A) = ψ j * e (sadj m j • i) := by
  rw [ψ_mul_e, sadj_smul_smul]

theorem ext_e {a b : A} (h : ∀ i, a * e i = b * e i) : a = b := by
  rw [← mul_one a, ← mul_one b, ← sum_e, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

theorem pol_commute (p q : MvPolynomial (Fin m) k) : Commute (pol p : A) (pol q) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem ncEval_x_comp {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    ncEval (fun c => (x (f c) : A)) p = pol (rename f p) := by
  simp_rw [← pol_X]; exact ncEval_algHom_X _ _ _

theorem e_mul_ψ_mul_ψ (j : ℕ) (i : Seq ν) : (e i * (ψ j * ψ j) : A) = ψ j * ψ j * e i := by
  rw [← mul_assoc, e_mul_ψ, mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc]

theorem e_mul_x (a : Fin m) (i : Seq ν) : (e i * x a : A) = x a * e i := (x_mul_e a i).symm

theorem moves_mul {a b : A} {i i' i'' : Seq ν} (h1 : e i * a = a * e i')
    (h2 : e i' * b = b * e i'') : e i * (a * b) = a * b * e i'' := by
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem moves_sub {a b : A} {i i' : Seq ν} (h1 : e i * a = a * e i')
    (h2 : e i * b = b * e i') : e i * (a - b) = (a - b) * e i' := by
  rw [mul_sub, sub_mul, h1, h2]

theorem e_mul_dot_cross_right (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (e i * (ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) : A) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i else 0 := by
  have key : (e i * (ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) : A) =
      (ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) * e (sadj m j • i) := by
    exact moves_sub (moves_mul (e_mul_ψ j i) (e_mul_x _ _))
      (moves_mul (e_mul_x _ _) (e_mul_ψ j i))
  rw [key, dot_cross_right]
  by_cases hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩
  · simp [sadj_smul_eq_self h hi, Seq.lbl, hi]
  · have h1 : (sadj m j • i).1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ := by
      rw [sadj_smul_apply]; exact lbl_congr i (by rw [sadj_apply_val h]; simp)
    have h2 : (sadj m j • i).1 ⟨j + 1, h⟩ = i.1 ⟨j, by omega⟩ := by
      rw [sadj_smul_apply]; exact lbl_congr i (by rw [sadj_apply_val h]; simp)
    simp only [Seq.lbl, h1, h2, hi, if_false]
    rw [if_neg (Ne.symm hi)]

theorem e_mul_dot_cross_left (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (e i * (x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) : A) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i else 0 := by
  have key : (e i * (x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) : A) =
      (x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) * e (sadj m j • i) := by
    exact moves_sub (moves_mul (e_mul_x _ _) (e_mul_ψ j i))
      (moves_mul (e_mul_ψ j i) (e_mul_x _ _))
  rw [key, dot_cross_left]
  by_cases hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩
  · simp [sadj_smul_eq_self h hi, Seq.lbl, hi]
  · have h1 : (sadj m j • i).1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ := by
      rw [sadj_smul_apply]; exact lbl_congr i (by rw [sadj_apply_val h]; simp)
    have h2 : (sadj m j • i).1 ⟨j + 1, h⟩ = i.1 ⟨j, by omega⟩ := by
      rw [sadj_smul_apply]; exact lbl_congr i (by rw [sadj_apply_val h]; simp)
    simp only [Seq.lbl, h1, h2, hi, if_false]
    rw [if_neg (Ne.symm hi)]

theorem ncEval_x2 (a b : Fin m) (p : MvPolynomial (Fin 2) k) :
    ncEval ![(x a : A), x b] p = pol (rename ![a, b] p) := by
  rw [← ncEval_x_comp]; congr 1; funext c; fin_cases c <;> rfl

theorem ncEval_x3 (a b c : Fin m) (p : MvPolynomial (Fin 3) k) :
    ncEval ![(x a : A), x b, x c] p = pol (rename ![a, b, c] p) := by
  rw [← ncEval_x_comp]; congr 1; funext d; fin_cases d <;> rfl

theorem e_mul_ψ_sq (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (e i * (ψ j * ψ j) : A) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
        e i * pol (rename ![⟨j, by omega⟩, ⟨j + 1, h⟩]
          (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩))) := by
  rw [e_mul_ψ_mul_ψ, ψ_sq]
  split_ifs
  · rfl
  · rw [ncEval_x2, (e_commute_pol i _).eq]

theorem braid_perm_val {n j : ℕ} (h : j + 2 < n) (a : Fin n) :
    (sadj n j (sadj n (j + 1) (sadj n j a))).val =
      if a.val = j then j + 2 else if a.val = j + 2 then j else a.val := by
  simp only [sadj_apply_val (show j + 1 < n by omega), sadj_apply_val h]
  split_ifs <;> omega

theorem braid_perm_val' {n j : ℕ} (h : j + 2 < n) (a : Fin n) :
    (sadj n (j + 1) (sadj n j (sadj n (j + 1) a))).val =
      if a.val = j then j + 2 else if a.val = j + 2 then j else a.val := by
  simp only [sadj_apply_val (show j + 1 < n by omega), sadj_apply_val h]
  split_ifs <;> omega

omit [DecidableEq I] in
theorem braid_smul {j : ℕ} (h : j + 2 < m) (i : Seq ν) :
    sadj m j • sadj m (j + 1) • sadj m j • i = sadj m (j + 1) • sadj m j • sadj m (j + 1) • i := by
  apply Subtype.ext; funext a
  simp only [sadj_smul_apply]
  exact lbl_congr i (by rw [braid_perm_val h, braid_perm_val' h])

omit [DecidableEq I] in
theorem braid_smul_apply_zero {j : ℕ} (h : j + 2 < m) (i : Seq ν) :
    (sadj m j • sadj m (j + 1) • sadj m j • i).1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩ := by
  simp only [sadj_smul_apply]
  exact lbl_congr i (by rw [braid_perm_val h]; simp)

omit [DecidableEq I] in
theorem braid_smul_apply_one {j : ℕ} (h : j + 2 < m) (i : Seq ν) :
    (sadj m j • sadj m (j + 1) • sadj m j • i).1 ⟨j + 1, by omega⟩ = i.1 ⟨j + 1, by omega⟩ := by
  simp only [sadj_smul_apply]
  exact lbl_congr i (by rw [braid_perm_val h]; simp)

omit [DecidableEq I] in
theorem braid_smul_apply_two {j : ℕ} (h : j + 2 < m) (i : Seq ν) :
    (sadj m j • sadj m (j + 1) • sadj m j • i).1 ⟨j + 2, h⟩ = i.1 ⟨j, by omega⟩ := by
  simp only [sadj_smul_apply]
  exact lbl_congr i (by rw [braid_perm_val h]; simp)

omit [DecidableEq I] in
theorem braid_smul_eq_self {j : ℕ} (h : j + 2 < m) {i : Seq ν}
    (hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩) : sadj m j • sadj m (j + 1) • sadj m j • i = i := by
  apply Subtype.ext; funext a
  simp only [sadj_smul_apply]
  have hv := braid_perm_val h a
  split_ifs at hv with h1 h2
  · rw [lbl_congr i (b := ⟨j + 2, h⟩) hv, lbl_congr i (b := ⟨j, by omega⟩) h1]; exact hi.symm
  · rw [lbl_congr i (b := ⟨j, by omega⟩) hv, lbl_congr i (b := ⟨j + 2, h⟩) h2]; exact hi
  · exact lbl_congr i hv

theorem e_mul_braid (j : ℕ) (h : j + 2 < m) (i : Seq ν) :
    (e i * (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) : A) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
        e i * pol (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩))))
      else 0 := by
  have key : (e i * (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) : A) =
      (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) *
        e (sadj m j • sadj m (j + 1) • sadj m j • i) := by
    refine moves_sub (moves_mul (moves_mul (e_mul_ψ _ _) (e_mul_ψ _ _)) (e_mul_ψ _ _)) ?_
    rw [braid_smul h]
    exact moves_mul (moves_mul (e_mul_ψ _ _) (e_mul_ψ _ _)) (e_mul_ψ _ _)
  rw [key, braid j h]
  simp only [Seq.lbl]
  rw [braid_smul_apply_zero h, braid_smul_apply_one h, braid_smul_apply_two h]
  by_cases hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩
  · rw [braid_smul_eq_self h hi]
    by_cases hb : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, by omega⟩
    · rw [if_neg (fun hc => hc.2 (hi ▸ hb)), if_neg (fun hc => hc.2 hb)]
    · rw [if_pos ⟨hi.symm, hi ▸ hb⟩, if_pos ⟨hi, hb⟩, ← hi, ncEval_x3, (e_commute_pol i _).eq]
  · rw [if_neg (fun hc => hi hc.1.symm), if_neg (fun hc => hi hc.1)]

/-! ### The horizontal flip -/

variable (k Q ν) in
/-- The horizontal flip on the free algebra: the anti-homomorphism fixing the generators. -/
noncomputable def flipFree : FreeAlgebra k (Gen ν) →ₐ[k] Aᵐᵒᵖ :=
  FreeAlgebra.lift k fun g => op (mk k Q ν (FreeAlgebra.ι k g))

@[simp] theorem flipFree_fe (i : Seq ν) : flipFree k Q ν (fe k ν i) = op (e i) :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem flipFree_fx (a : Fin m) : flipFree k Q ν (fx k ν a) = op (x a) :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem flipFree_fψ (j : ℕ) : flipFree k Q ν (fψ k ν j) = op (ψ j) :=
  FreeAlgebra.lift_ι_apply _ _

theorem flipFree_ncEval {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    flipFree k Q ν (ncEval (fun c => fx k ν (f c)) p) = op (pol (rename f p)) := by
  rw [ncEval_map]
  simp only [flipFree_fx]
  have := ncEval_algHom_X ((pol : MvPolynomial (Fin m) k →ₐ[k] A).toOpposite pol_commute) f p
  simpa using this

theorem flipFree_rel ⦃a b : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν a b) :
    flipFree k Q ν a = flipFree k Q ν b := by
  apply MulOpposite.unop_injective
  cases h with
  | idem_mul i j =>
    simp only [map_mul, unop_mul, flipFree_fe, unop_op, e_mul_e]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  | idem_sum => simp [map_sum, sum_e]
  | dot_idem a i => simp [x_mul_e]
  | cross_idem j i => simp [e_mul_ψ]
  | cross_zero j h => simp [ψ_eq_zero j h]
  | dot_dot a b => simp [x_mul_x]
  | cross_cross j l h => simp [ψ_mul_ψ j l h]
  | dot_cross a j h1 h2 => simp [x_mul_ψ a j h1 h2]
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, unop_mul, unop_sub, flipFree_fe, flipFree_fx, flipFree_fψ,
      unop_op]
    rw [e_mul_dot_cross_right]; split_ifs <;> simp
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, unop_mul, unop_sub, flipFree_fe, flipFree_fx, flipFree_fψ,
      unop_op]
    rw [e_mul_dot_cross_left]; split_ifs <;> simp
  | cross_sq j h i =>
    simp only [map_mul, unop_mul, flipFree_fe, flipFree_fψ, unop_op, ← mul_assoc]
    rw [mul_assoc, e_mul_ψ_sq]
    split_ifs
    · simp
    · rw [map_mul, unop_mul, flipFree_fe, unop_op, vec2_fx, flipFree_ncEval, unop_op]
  | braid j h i =>
    simp only [map_mul, map_sub, unop_mul, unop_sub, flipFree_fe, flipFree_fψ, unop_op,
      ← mul_assoc]
    rw [e_mul_braid]
    split_ifs
    · rw [map_mul, unop_mul, flipFree_fe, unop_op, vec3_fx, flipFree_ncEval, unop_op]
    · simp

variable (k Q ν) in
/-- The horizontal flip as an algebra homomorphism `R(ν) → R(ν)ᵐᵒᵖ`. -/
noncomputable def flipAlgHom : A →ₐ[k] Aᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨flipFree k Q ν, flipFree_rel⟩

theorem flipAlgHom_mk (a : FreeAlgebra k (Gen ν)) :
    flipAlgHom k Q ν (mk k Q ν a) = flipFree k Q ν a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

/-- The horizontal flip of `R(ν)` (the paper's antiinvolution `ψ`): the anti-automorphism
fixing `e i`, `x a` and `ψ j`, reversing products. -/
noncomputable def hflip (a : A) : A := (flipAlgHom k Q ν a).unop

@[simp] theorem hflip_e (i : Seq ν) : hflip (e i : A) = e i := by
  rw [hflip, e, flipAlgHom_mk, flipFree_fe]; rfl

@[simp] theorem hflip_x (a : Fin m) : hflip (x a : A) = x a := by
  rw [hflip, x, flipAlgHom_mk, flipFree_fx]; rfl

@[simp] theorem hflip_ψ (j : ℕ) : hflip (ψ j : A) = ψ j := by
  rw [hflip, ψ, flipAlgHom_mk, flipFree_fψ]; rfl

@[simp] theorem hflip_mul (a b : A) : hflip (a * b) = hflip b * hflip a := by
  simp [hflip]

@[simp] theorem hflip_add (a b : A) : hflip (a + b) = hflip a + hflip b := by
  simp [hflip]

@[simp] theorem hflip_sub (a b : A) : hflip (a - b) = hflip a - hflip b := by
  simp [hflip]

@[simp] theorem hflip_one : hflip (1 : A) = 1 := by
  simp [hflip]

@[simp] theorem hflip_zero : hflip (0 : A) = 0 := by
  simp [hflip]

@[simp] theorem hflip_smul (c : k) (a : A) : hflip (c • a) = c • hflip a := by
  simp [hflip]

@[simp] theorem hflip_algebraMap (c : k) : hflip (algebraMap k A c) = algebraMap k A c := by
  simp [hflip]

@[simp] theorem hflip_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    hflip (∑ t ∈ s, f t) = ∑ t ∈ s, hflip (f t) := by
  simp [hflip]

theorem hflip_pol (p : MvPolynomial (Fin m) k) : hflip (pol p : A) = pol p := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [algHom_C, hflip_algebraMap]
  | add p q hp hq => rw [map_add, hflip_add, hp, hq]
  | mul_X p a hp => rw [map_mul, hflip_mul, hp, pol_X, hflip_x, ← pol_X, pol_commute]

/-- The flip applied twice, as an algebra endomorphism. -/
private noncomputable def flipFlip : A →ₐ[k] A :=
  (AlgEquiv.opOp k A).symm.toAlgHom.comp ((AlgHom.op (flipAlgHom k Q ν)).comp (flipAlgHom k Q ν))

private theorem flipFlip_apply (a : A) : flipFlip a = hflip (hflip a) := rfl

private theorem flipFlip_eq : (flipFlip : A →ₐ[k] A) = AlgHom.id k A := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  simp only [Function.comp_apply, AlgHom.comp_toLinearMap, LinearMap.coe_comp,
    AlgHom.toLinearMap_apply, AlgHom.id_comp]
  change flipFlip (mk k Q ν (FreeAlgebra.ι k g)) = mk k Q ν (FreeAlgebra.ι k g)
  rw [flipFlip_apply]
  cases g with
  | idem i => exact (congrArg hflip (hflip_e i)).trans (hflip_e i)
  | dot a => exact (congrArg hflip (hflip_x a)).trans (hflip_x a)
  | cross j => exact (congrArg hflip (hflip_ψ j)).trans (hflip_ψ j)

/-- The flip is an involution. -/
@[simp] theorem hflip_hflip (a : A) : hflip (hflip a) = a := by
  rw [← flipFlip_apply, flipFlip_eq]; rfl

theorem hflip_injective : Function.Injective (hflip : A → A) :=
  Function.LeftInverse.injective hflip_hflip

variable (k Q ν) in
/-- **KL I, §2.1.** The horizontal flip is an anti-automorphism of `R(ν)`, i.e. an
isomorphism `R(ν) ≃ₐ[k] R(ν)ᵐᵒᵖ`, fixing the generators `e i`, `x a`, `ψ j`
(`flipH_e`, `flipH_x`, `flipH_ψ`); its inverse is again the flip (`flipH_symm_apply`). -/
noncomputable def flipH : A ≃ₐ[k] Aᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (flipAlgHom k Q ν)
    ((AlgEquiv.opOp k A).symm.toAlgHom.comp (AlgHom.op (flipAlgHom k Q ν)))
    (AlgHom.ext fun a => unop_injective (hflip_hflip a.unop))
    (AlgHom.ext fun a => hflip_hflip a)

theorem flipH_apply (a : A) : flipH k Q ν a = op (hflip a) := rfl

theorem flipH_symm_apply (a : Aᵐᵒᵖ) : (flipH k Q ν).symm a = hflip a.unop := rfl

@[simp] theorem flipH_e (i : Seq ν) : flipH k Q ν (e i) = op (e i) := by
  rw [flipH_apply, hflip_e]

@[simp] theorem flipH_x (a : Fin m) : flipH k Q ν (x a) = op (x a) := by
  rw [flipH_apply, hflip_x]

@[simp] theorem flipH_ψ (j : ℕ) : flipH k Q ν (ψ j) = op (ψ j) := by
  rw [flipH_apply, hflip_ψ]

/-- The flip is an involution: applying `flipH` twice (through `unop`) is the identity. -/
theorem flipH_flipH (a : A) : (flipH k Q ν ((flipH k Q ν a).unop)).unop = a :=
  hflip_hflip a

/-- The flip takes `1_j R(ν) 1_i` to `1_i R(ν) 1_j`. -/
theorem hflip_e_mul_mul_e (i j : Seq ν) (a : A) :
    hflip (e j * a * e i) = e i * hflip a * e j := by
  simp [mul_assoc]

/-! ### The vertical flip: signs -/

theorem sadj_rev {n j : ℕ} (h : j + 1 < n) (a : Fin n) :
    sadj n (n - 2 - j) a.rev = (sadj n j a).rev := by
  apply Fin.ext
  rw [sadj_apply_val (by omega), Fin.val_rev, Fin.val_rev, sadj_apply_val h]
  split_ifs <;> omega

omit [DecidableEq I] in
theorem rev_sadj_smul {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    sadj m (m - 2 - j) • i.rev = (sadj m j • i).rev := by
  apply Subtype.ext; funext a
  rw [sadj_smul_apply, Seq.rev_apply, Seq.rev_apply, sadj_smul_apply]
  have := sadj_rev h a.rev
  rw [Fin.rev_rev] at this
  rw [this, Fin.rev_rev]

theorem ext_e_rev {a b : A} (h : ∀ i : Seq ν, a * e i.rev = b * e i.rev) : a = b :=
  ext_e fun i => by simpa using h i.rev

variable (k) in
/-- The sign attached to a crossing of the strands at positions `j, j + 1` with bottom
sequence `i`: `-1` if `i_j = i_{j+1}`, and `1` otherwise (or if `j` is out of range). -/
def sgn (j : ℕ) (i : Seq ν) : k :=
  if h : j + 1 < m then (if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ then -1 else 1) else 1

theorem sgn_of_lt {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    sgn k j i = if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ then -1 else 1 := dif_pos h

@[simp] theorem sgn_mul_self (j : ℕ) (i : Seq ν) : sgn k j i * sgn k j i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem sgn_sadj (j : ℕ) (i : Seq ν) : sgn k j (sadj m j • i) = sgn k j i := by
  by_cases h : j + 1 < m
  · rw [sgn_of_lt h, sgn_of_lt h, sadj_smul_apply, sadj_smul_apply]
    have h1 : i.1 (sadj m j ⟨j, by omega⟩) = i.1 ⟨j + 1, h⟩ :=
      lbl_congr i (by rw [sadj_apply_val h]; simp)
    have h2 : i.1 (sadj m j ⟨j + 1, h⟩) = i.1 ⟨j, by omega⟩ :=
      lbl_congr i (by rw [sadj_apply_val h]; simp)
    rw [h1, h2]; simp only [eq_comm]
  · simp [sgn, h]

theorem sgn_sadj_of_far {j l : ℕ} (hjl : j + 1 < l ∨ l + 1 < j) (i : Seq ν) :
    sgn k j (sadj m l • i) = sgn k j i := by
  by_cases h : j + 1 < m
  · rw [sgn_of_lt h, sgn_of_lt h, sadj_smul_apply, sadj_smul_apply]
    by_cases hl : l + 1 < m
    · have h1 : i.1 (sadj m l ⟨j, by omega⟩) = i.1 ⟨j, by omega⟩ :=
        lbl_congr i (by rw [sadj_apply_val hl]; simp only [Fin.val_mk]; split_ifs <;> omega)
      have h2 : i.1 (sadj m l ⟨j + 1, h⟩) = i.1 ⟨j + 1, h⟩ :=
        lbl_congr i (by rw [sadj_apply_val hl]; simp only [Fin.val_mk]; split_ifs <;> omega)
      rw [h1, h2]
    · simp [sadj, hl]
  · simp [sgn, h]

theorem sgn_rev {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    sgn k (m - 2 - j) i.rev = sgn k j i := by
  rw [sgn_of_lt (by omega), sgn_of_lt h, Seq.rev_apply, Seq.rev_apply]
  have h1 : i.1 (Fin.rev ⟨m - 2 - j, by omega⟩) = i.1 ⟨j + 1, h⟩ :=
    lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have h2 : i.1 (Fin.rev ⟨m - 2 - j + 1, by omega⟩) = i.1 ⟨j, by omega⟩ :=
    lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  rw [h1, h2]
  simp only [eq_comm]

variable (Q) in
/-- The diagonal element `∑_i sgn_j(i) e_{rev i}`; the vertical flip of `ψ j` is
`ψ (m - 2 - j) * sgnE j`. -/
noncomputable def sgnE (j : ℕ) : A := ∑ i, sgn k j i • e i.rev

theorem sgnE_mul_e_rev (j : ℕ) (i : Seq ν) :
    (sgnE Q j * e i.rev : A) = sgn k j i • e i.rev := by
  simp only [sgnE, Finset.sum_mul, smul_mul_assoc, e_mul_e, Seq.rev_inj, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem e_rev_mul_sgnE (j : ℕ) (i : Seq ν) :
    (e i.rev * sgnE Q j : A) = sgn k j i • e i.rev := by
  simp only [sgnE, Finset.mul_sum, mul_smul_comm, e_mul_e, Seq.rev_inj, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem x_mul_sgnE (a : Fin m) (j : ℕ) : (x a * sgnE Q j : A) = sgnE Q j * x a := by
  simp only [sgnE, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, x_mul_e]

theorem ψ_rev_mul_e_rev {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    (ψ (m - 2 - j) * e i.rev : A) = e (sadj m j • i).rev * ψ (m - 2 - j) := by
  rw [ψ_mul_e, rev_sadj_smul h]

theorem ψ_rev_mul_sgnE {j : ℕ} (h : j + 1 < m) :
    (ψ (m - 2 - j) * sgnE Q j : A) = sgnE Q j * ψ (m - 2 - j) := by
  refine ext_e_rev fun i => ?_
  rw [mul_assoc, sgnE_mul_e_rev, mul_smul_comm, mul_assoc, ψ_rev_mul_e_rev h, ← mul_assoc,
    sgnE_mul_e_rev, sgn_sadj, smul_mul_assoc, ← ψ_rev_mul_e_rev h]

theorem hflip_sgnE (j : ℕ) : hflip (sgnE Q j : A) = sgnE Q j := by
  simp [sgnE]

/-! ### The vertical flip: images of the crossings -/

variable (Q) in
/-- The vertical flip of the crossing `ψ j`: `ψ (m - 2 - j) * sgnE j` if `j + 1 < m`
(and `0` otherwise, like `ψ j` itself). -/
noncomputable def sigmaψ (j : ℕ) : A := if j + 1 < m then ψ (m - 2 - j) * sgnE Q j else 0

theorem sigmaψ_of_lt {j : ℕ} (h : j + 1 < m) : (sigmaψ Q j : A) = ψ (m - 2 - j) * sgnE Q j :=
  if_pos h

theorem sigmaψ_of_le {j : ℕ} (h : m ≤ j + 1) : (sigmaψ Q j : A) = 0 := if_neg (by omega)

theorem sigmaψ_mul_e_rev {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    (sigmaψ Q j * e i.rev : A) = sgn k j i • (ψ (m - 2 - j) * e i.rev) := by
  rw [sigmaψ_of_lt h, mul_assoc, sgnE_mul_e_rev, mul_smul_comm]

theorem sigmaψ_mul_of_e {j : ℕ} (h : j + 1 < m) {z : A} {i : Seq ν} (hz : e i.rev * z = z) :
    sigmaψ Q j * z = sgn k j i • (ψ (m - 2 - j) * z) := by
  rw [← hz, ← mul_assoc, sigmaψ_mul_e_rev h, smul_mul_assoc, mul_assoc]

theorem e_rev_mul_ψ_rev {j : ℕ} (h : j + 1 < m) {z : A} {i : Seq ν} (hz : e i.rev * z = z) :
    e (sadj m j • i).rev * (ψ (m - 2 - j) * z) = ψ (m - 2 - j) * z := by
  rw [← hz, ← mul_assoc, ← mul_assoc, ← ψ_rev_mul_e_rev h, mul_assoc, mul_assoc, ← mul_assoc (e _),
    e_mul_self]

theorem sigma_cross_idem (j : ℕ) (i : Seq ν) :
    (sigmaψ Q j * e i.rev : A) = e (sadj m j • i).rev * sigmaψ Q j := by
  by_cases h : j + 1 < m
  · rw [sigmaψ_mul_e_rev h, sigmaψ_of_lt h, ← mul_assoc, ← ψ_rev_mul_e_rev h, mul_assoc,
      e_rev_mul_sgnE, mul_smul_comm]
  · simp [sigmaψ_of_le (show m ≤ j + 1 by omega)]

theorem sigma_cross_cross (j l : ℕ) (hjl : j + 1 < l) :
    (sigmaψ Q j * sigmaψ Q l : A) = sigmaψ Q l * sigmaψ Q j := by
  by_cases hl : l + 1 < m
  · have hj : j + 1 < m := by omega
    refine ext_e_rev fun i => ?_
    rw [mul_assoc, mul_assoc, sigmaψ_mul_e_rev hl, sigmaψ_mul_e_rev hj, mul_smul_comm,
      mul_smul_comm, sigmaψ_mul_of_e hj (i := sadj m l • i) (e_rev_mul_ψ_rev hl (e_mul_self _)),
      sigmaψ_mul_of_e hl (i := sadj m j • i) (e_rev_mul_ψ_rev hj (e_mul_self _)),
      sgn_sadj_of_far (Or.inl hjl), sgn_sadj_of_far (Or.inr hjl), smul_smul, smul_smul,
      mul_comm (sgn k j i), ← mul_assoc, ← mul_assoc, ψ_mul_ψ (m - 2 - l) (m - 2 - j) (by omega)]
  · simp [sigmaψ_of_le (show m ≤ l + 1 by omega)]

theorem sigma_dot_cross (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (x a.rev * sigmaψ Q j : A) = sigmaψ Q j * x a.rev := by
  by_cases h : j + 1 < m
  · rw [sigmaψ_of_lt h, ← mul_assoc, x_mul_ψ _ _ (by rw [Fin.val_rev]; omega)
      (by rw [Fin.val_rev]; omega), mul_assoc, x_mul_sgnE, mul_assoc]
  · simp [sigmaψ_of_le (show m ≤ j + 1 by omega)]

omit [DecidableEq I] in
theorem rev_lbl_left {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    i.rev.1 ⟨m - 2 - j, by omega⟩ = i.1 ⟨j + 1, h⟩ := by
  rw [Seq.rev_apply]; exact lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)

omit [DecidableEq I] in
theorem rev_lbl_right {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    i.rev.1 ⟨m - 2 - j + 1, by omega⟩ = i.1 ⟨j, by omega⟩ := by
  rw [Seq.rev_apply]; exact lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)

theorem sigma_dot_cross_left (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    ((x (Fin.rev ⟨j, by omega⟩) * sigmaψ Q j - sigmaψ Q j * x (Fin.rev ⟨j + 1, h⟩)) * e i.rev
      : A) = if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i.rev else 0 := by
  have h' : m - 2 - j + 1 < m := by omega
  have r0 : (Fin.rev ⟨j, by omega⟩ : Fin m) = ⟨m - 2 - j + 1, h'⟩ :=
    Fin.ext (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have r1 : (Fin.rev ⟨j + 1, h⟩ : Fin m) = ⟨m - 2 - j, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have key : ((x ⟨m - 2 - j + 1, h'⟩ * sigmaψ Q j - sigmaψ Q j * x ⟨m - 2 - j, by omega⟩) *
      e i.rev : A) = -sgn k j i • ((ψ (m - 2 - j) * x ⟨m - 2 - j, by omega⟩ -
        x ⟨m - 2 - j + 1, h'⟩ * ψ (m - 2 - j)) * e i.rev) := by
    rw [sub_mul, mul_assoc, mul_assoc, x_mul_e, ← mul_assoc (sigmaψ Q j), sigmaψ_mul_e_rev h,
      mul_smul_comm, smul_mul_assoc, ← smul_sub, neg_smul, ← smul_neg]
    congr 1
    rw [mul_assoc (ψ _), ← x_mul_e]
    noncomm_ring
  rw [r0, r1, key, dot_cross_right (m - 2 - j) h' i.rev]
  simp only [Seq.lbl, rev_lbl_left h, rev_lbl_right h, sgn_of_lt h]
  by_cases hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩
  · simp [hi]
  · simp [hi, Ne.symm hi]

theorem sigma_dot_cross_right (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    ((sigmaψ Q j * x (Fin.rev ⟨j, by omega⟩) - x (Fin.rev ⟨j + 1, h⟩) * sigmaψ Q j) * e i.rev
      : A) = if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i.rev else 0 := by
  have h' : m - 2 - j + 1 < m := by omega
  have r0 : (Fin.rev ⟨j, by omega⟩ : Fin m) = ⟨m - 2 - j + 1, h'⟩ :=
    Fin.ext (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have r1 : (Fin.rev ⟨j + 1, h⟩ : Fin m) = ⟨m - 2 - j, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have key : ((sigmaψ Q j * x ⟨m - 2 - j + 1, h'⟩ - x ⟨m - 2 - j, by omega⟩ * sigmaψ Q j) *
      e i.rev : A) = -sgn k j i • ((x ⟨m - 2 - j, by omega⟩ * ψ (m - 2 - j) -
        ψ (m - 2 - j) * x ⟨m - 2 - j + 1, h'⟩) * e i.rev) := by
    rw [sub_mul, mul_assoc, mul_assoc, x_mul_e, ← mul_assoc (sigmaψ Q j), sigmaψ_mul_e_rev h,
      mul_smul_comm, smul_mul_assoc, ← smul_sub, neg_smul, ← smul_neg]
    congr 1
    rw [mul_assoc (ψ _), ← x_mul_e]
    noncomm_ring
  rw [r0, r1, key, dot_cross_left (m - 2 - j) h' i.rev]
  simp only [Seq.lbl, rev_lbl_left h, rev_lbl_right h, sgn_of_lt h]
  by_cases hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩
  · simp [hi]
  · simp [hi, Ne.symm hi]

omit [DecidableEq I] in
theorem sadj_smul_apply_of {l : ℕ} (hl : l + 1 < m) (i : Seq ν) (a b : Fin m)
    (hv : (if a.val = l then l + 1 else if a.val = l + 1 then l else a.val) = b.val := by
      simp only [Fin.val_mk]; split_ifs <;> omega) :
    (sadj m l • i).1 a = i.1 b := by
  rw [sadj_smul_apply]; exact lbl_congr i (by rw [sadj_apply_val hl, hv])

theorem sigma_cross_sq (hQ : KLRSymm Q) (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (sigmaψ Q j * sigmaψ Q j * e i.rev : A) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
        pol (rename (fun c => (![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩] c).rev)
          (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩))) * e i.rev := by
  have h' : m - 2 - j + 1 < m := by omega
  rw [mul_assoc, sigmaψ_mul_e_rev h, mul_smul_comm,
    sigmaψ_mul_of_e h (i := sadj m j • i) (e_rev_mul_ψ_rev h (e_mul_self _)), sgn_sadj, smul_smul,
    sgn_mul_self, one_smul, ← mul_assoc, ψ_sq (m - 2 - j) h' i.rev]
  simp only [Seq.lbl, rev_lbl_left h, rev_lbl_right h]
  by_cases hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩
  · simp [hi]
  · rw [if_neg (Ne.symm hi), if_neg hi, ncEval_x2, hQ _ _ hi, rename_rename]
    congr 3
    congr 1
    funext c; fin_cases c <;> exact Fin.ext (by simp; omega)

theorem sigma_braid (j : ℕ) (h : j + 2 < m) (i : Seq ν) :
    ((sigmaψ Q j * sigmaψ Q (j + 1) * sigmaψ Q j
        - sigmaψ Q (j + 1) * sigmaψ Q j * sigmaψ Q (j + 1)) * e i.rev : A) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
        pol (rename (fun d => (![(⟨j, by omega⟩ : Fin m), ⟨j + 1, by omega⟩, ⟨j + 2, h⟩] d).rev)
          (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩)))) * e i.rev
      else 0 := by
  have h0 : j + 1 < m := by omega
  have h1 : j + 1 + 1 < m := by omega
  -- the six signs, in terms of the labels `a b c` at positions `j, j + 1, j + 2`
  have s1 : sgn k j i = if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h0⟩ then -1 else 1 := sgn_of_lt h0 i
  have s2 : sgn k (j + 1) (sadj m j • i) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩ then -1 else 1 := by
    rw [sgn_of_lt h1, sadj_smul_apply_of h0 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 2, h⟩]
  have s3 : sgn k j (sadj m (j + 1) • sadj m j • i) =
      if i.1 ⟨j + 1, h0⟩ = i.1 ⟨j + 2, h⟩ then -1 else 1 := by
    rw [sgn_of_lt h0, sadj_smul_apply_of h1 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h1 _ _ ⟨j + 2, h⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 1, h0⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 2, h⟩]
  have s4 : sgn k (j + 1) i = if i.1 ⟨j + 1, h0⟩ = i.1 ⟨j + 2, h⟩ then -1 else 1 :=
    sgn_of_lt h1 i
  have s5 : sgn k j (sadj m (j + 1) • i) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩ then -1 else 1 := by
    rw [sgn_of_lt h0, sadj_smul_apply_of h1 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h1 _ _ ⟨j + 2, h⟩]
  have s6 : sgn k (j + 1) (sadj m j • sadj m (j + 1) • i) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h0⟩ then -1 else 1 := by
    rw [sgn_of_lt h1, sadj_smul_apply_of h0 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 2, h⟩,
      sadj_smul_apply_of h1 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h1 _ _ ⟨j + 1, h0⟩]
  -- expand both products
  rw [sub_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
    sigmaψ_mul_e_rev h0, mul_smul_comm, mul_smul_comm,
    sigmaψ_mul_of_e h1 (i := sadj m j • i) (e_rev_mul_ψ_rev h0 (e_mul_self _)), mul_smul_comm,
    sigmaψ_mul_of_e h0 (i := sadj m (j + 1) • sadj m j • i)
      (e_rev_mul_ψ_rev h1 (e_rev_mul_ψ_rev h0 (e_mul_self _))),
    sigmaψ_mul_e_rev h1, mul_smul_comm, mul_smul_comm,
    sigmaψ_mul_of_e h0 (i := sadj m (j + 1) • i) (e_rev_mul_ψ_rev h1 (e_mul_self _)), mul_smul_comm,
    sigmaψ_mul_of_e h1 (i := sadj m j • sadj m (j + 1) • i)
      (e_rev_mul_ψ_rev h0 (e_rev_mul_ψ_rev h1 (e_mul_self _))),
    s1, s2, s3, s4, s5, s6, smul_smul, smul_smul, smul_smul, smul_smul]
  -- rename the crossing indices
  obtain ⟨l, hl⟩ : ∃ l, l = m - 3 - j := ⟨_, rfl⟩
  have hl2 : l + 2 < m := by omega
  rw [show m - 2 - j = l + 1 by omega, show m - 2 - (j + 1) = l by omega]
  have hbr := braid (k := k) (Q := Q) l hl2 i.rev
  have ra : i.rev.1 ⟨l, by omega⟩ = i.1 ⟨j + 2, h⟩ := by
    rw [Seq.rev_apply]; exact lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have rb : i.rev.1 ⟨l + 1, by omega⟩ = i.1 ⟨j + 1, h0⟩ := by
    rw [Seq.rev_apply]; exact lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  have rc : i.rev.1 ⟨l + 2, hl2⟩ = i.1 ⟨j, by omega⟩ := by
    rw [Seq.rev_apply]; exact lbl_congr i (by simp only [Fin.val_rev, Fin.val_mk]; omega)
  simp only [Seq.lbl, ra, rb, rc] at hbr
  rw [sub_mul, sub_eq_iff_eq_add] at hbr
  simp only [Seq.lbl]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hbr]
  by_cases hac : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩
  · by_cases hab : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h0⟩
    · have hbc : i.1 ⟨j + 1, h0⟩ = i.1 ⟨j + 2, h⟩ := hab ▸ hac
      simp [hab, hac, hbc]
    · have hbc : i.1 ⟨j + 1, h0⟩ ≠ i.1 ⟨j + 2, h⟩ := fun hbc => hab (hac.trans hbc.symm)
      have hf : (fun d => (![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h0⟩, ⟨j + 2, h⟩] d).rev) =
          (![(⟨l, by omega⟩ : Fin m), ⟨l + 1, by omega⟩, ⟨l + 2, hl2⟩] ∘ ![2, 1, 0]) := by
        funext d; fin_cases d <;> exact Fin.ext (by simp; omega)
      have key : ncEval ![(x ⟨l, by omega⟩ : A), x ⟨l + 1, by omega⟩, x ⟨l + 2, hl2⟩]
          (qbar (Q (i.1 ⟨j + 2, h⟩) (i.1 ⟨j + 1, h0⟩))) =
          pol (rename (fun d => (![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h0⟩, ⟨j + 2, h⟩] d).rev)
            (qbar (Q (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, h0⟩)))) := by
        rw [← hac, ncEval_x3, hf, ← rename_rename, qbar_rename_rev]
      have hc1 : i.1 ⟨j + 2, h⟩ = i.1 ⟨j, by omega⟩ ∧ i.1 ⟨j + 2, h⟩ ≠ i.1 ⟨j + 1, h0⟩ :=
        ⟨hac.symm, fun h' => hab (hac.trans h')⟩
      have hc2 : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩ ∧ i.1 ⟨j, by omega⟩ ≠ i.1 ⟨j + 1, h0⟩ :=
        ⟨hac, hab⟩
      rw [if_pos hc1, if_pos hc2, key]
      rw [if_pos hac, if_neg hab, if_neg hbc]
      simp only [mul_one, one_mul, neg_smul, one_smul, smul_add, neg_add, sub_neg_eq_add]
      abel
  · have hc1 : ¬ (i.1 ⟨j + 2, h⟩ = i.1 ⟨j, by omega⟩ ∧ i.1 ⟨j + 2, h⟩ ≠ i.1 ⟨j + 1, h0⟩) :=
      fun hc => hac hc.1.symm
    have hc2 : ¬ (i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩ ∧ i.1 ⟨j, by omega⟩ ≠ i.1 ⟨j + 1, h0⟩) :=
      fun hc => hac hc.1
    rw [if_neg hc1, if_neg hc2, zero_add]
    by_cases hab : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h0⟩ <;>
    by_cases hbc : i.1 ⟨j + 1, h0⟩ = i.1 ⟨j + 2, h⟩ <;>
    simp [hab, hac, hbc]

/-! ### The vertical flip -/

variable (Q) in
/-- The vertical flip on generators. -/
noncomputable def sigmaGen : Gen ν → A
  | .idem i => e i.rev
  | .dot a => x a.rev
  | .cross j => sigmaψ Q j

variable (k Q ν) in
/-- The vertical flip on the free algebra. -/
noncomputable def sigmaFree : FreeAlgebra k (Gen ν) →ₐ[k] A :=
  FreeAlgebra.lift k (sigmaGen Q)

@[simp] theorem sigmaFree_fe (i : Seq ν) : sigmaFree k Q ν (fe k ν i) = e i.rev :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem sigmaFree_fx (a : Fin m) : sigmaFree k Q ν (fx k ν a) = x a.rev :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem sigmaFree_fψ (j : ℕ) : sigmaFree k Q ν (fψ k ν j) = sigmaψ Q j :=
  FreeAlgebra.lift_ι_apply _ _

theorem sigmaFree_ncEval {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    sigmaFree k Q ν (ncEval (fun c => fx k ν (f c)) p) = pol (rename (fun c => (f c).rev) p) := by
  rw [ncEval_map]
  simp only [sigmaFree_fx]
  exact ncEval_x_comp _ _

theorem sigmaFree_rel (hQ : KLRSymm Q) ⦃a b : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν a b) :
    sigmaFree k Q ν a = sigmaFree k Q ν b := by
  cases h with
  | idem_mul i j =>
    simp only [map_mul, sigmaFree_fe, e_mul_e, Seq.rev_inj]
    split_ifs <;> simp
  | idem_sum =>
    simp only [map_sum, sigmaFree_fe, map_one]
    rw [← sum_e]
    exact Fintype.sum_bijective _ Seq.rev_bijective _ _ (fun _ => rfl)
  | dot_idem a i => simp [x_mul_e]
  | cross_idem j i => simp [sigma_cross_idem]
  | cross_zero j h => simp [sigmaψ_of_le h]
  | dot_dot a b => simp [x_mul_x]
  | cross_cross j l h => simp [sigma_cross_cross j l h]
  | dot_cross a j h1 h2 => simp [sigma_dot_cross a j h1 h2]
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, sigmaFree_fe, sigmaFree_fx, sigmaFree_fψ]
    rw [sigma_dot_cross_left]; split_ifs <;> simp
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, sigmaFree_fe, sigmaFree_fx, sigmaFree_fψ]
    rw [sigma_dot_cross_right]; split_ifs <;> simp
  | cross_sq j h i =>
    simp only [map_mul, sigmaFree_fe, sigmaFree_fψ]
    rw [sigma_cross_sq hQ]
    split_ifs
    · simp
    · rw [map_mul, sigmaFree_fe, vec2_fx, sigmaFree_ncEval]
  | braid j h i =>
    simp only [map_mul, map_sub, sigmaFree_fe, sigmaFree_fψ]
    rw [sigma_braid]
    split_ifs
    · rw [map_mul, sigmaFree_fe, vec3_fx, sigmaFree_ncEval]
    · simp

/-- The vertical flip as an algebra endomorphism of `R(ν)`; see `sigma`. -/
noncomputable def sigmaHom (hQ : KLRSymm Q) : A →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨sigmaFree k Q ν, sigmaFree_rel hQ⟩

section sigma

variable (hQ : KLRSymm Q)

include hQ

theorem sigmaHom_mk (a : FreeAlgebra k (Gen ν)) :
    sigmaHom hQ (mk k Q ν a) = sigmaFree k Q ν a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem sigmaHom_e (i : Seq ν) : sigmaHom hQ (e i : A) = e i.rev := by
  rw [e, sigmaHom_mk, sigmaFree_fe]

@[simp] theorem sigmaHom_x (a : Fin m) : sigmaHom hQ (x a : A) = x a.rev := by
  rw [x, sigmaHom_mk, sigmaFree_fx]

@[simp] theorem sigmaHom_ψ (j : ℕ) : sigmaHom hQ (ψ j : A) = sigmaψ Q j := by
  rw [ψ, sigmaHom_mk, sigmaFree_fψ]

omit hQ in
theorem sgnE_rev {j : ℕ} (h : j + 1 < m) : (sgnE Q (m - 2 - j) : A) = ∑ i, sgn k j i • e i := by
  unfold sgnE
  exact Fintype.sum_bijective _ Seq.rev_bijective _ _
    (fun i => by rw [← sgn_rev h i.rev, Seq.rev_rev])

omit hQ in
theorem sum_sgn_e_mul_e (j : ℕ) (i : Seq ν) :
    ((∑ i', sgn k j i' • e i') * e i : A) = sgn k j i • e i := by
  simp only [Finset.sum_mul, smul_mul_assoc, e_mul_e, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

omit hQ in
theorem sum_sgn_e_mul_self (j : ℕ) :
    ((∑ i, sgn k j i • e i) * (∑ i, sgn k j i • e i) : A) = 1 := by
  refine ext_e fun i => ?_
  rw [mul_assoc, sum_sgn_e_mul_e, mul_smul_comm, sum_sgn_e_mul_e, smul_smul, sgn_mul_self,
    one_smul, one_mul]

theorem sigmaHom_sgnE (j : ℕ) : sigmaHom hQ (sgnE Q j : A) = ∑ i, sgn k j i • e i := by
  simp [sgnE, map_sum]

theorem sigmaHom_sigmaψ (j : ℕ) : sigmaHom hQ (sigmaψ Q j : A) = ψ j := by
  by_cases h : j + 1 < m
  · rw [sigmaψ_of_lt h, map_mul, sigmaHom_ψ, sigmaHom_sgnE, sigmaψ_of_lt (by omega),
      show m - 2 - (m - 2 - j) = j by omega, sgnE_rev h, mul_assoc, sum_sgn_e_mul_self, mul_one]
  · rw [sigmaψ_of_le (by omega), map_zero, ψ_eq_zero j (by omega)]

private theorem sigmaHom_comp_self : (sigmaHom hQ).comp (sigmaHom hQ) = AlgHom.id k A := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  change sigmaHom hQ (sigmaHom hQ (mk k Q ν (FreeAlgebra.ι k g))) = mk k Q ν (FreeAlgebra.ι k g)
  cases g with
  | idem i =>
    change sigmaHom hQ (sigmaHom hQ (e i)) = e i
    rw [sigmaHom_e, sigmaHom_e, Seq.rev_rev]
  | dot a =>
    change sigmaHom hQ (sigmaHom hQ (x a)) = x a
    rw [sigmaHom_x, sigmaHom_x, Fin.rev_rev]
  | cross j =>
    change sigmaHom hQ (sigmaHom hQ (ψ j)) = ψ j
    rw [sigmaHom_ψ, sigmaHom_sigmaψ]

theorem sigmaHom_sigmaHom (a : A) : sigmaHom hQ (sigmaHom hQ a) = a :=
  AlgHom.congr_fun (sigmaHom_comp_self hQ) a

omit hQ in
/-- **KL I, §2.1.** The vertical flip `σ` of `R(ν)`: the algebra automorphism with
`σ (e i) = e (rev i)`, `σ (x a) = x (Fin.rev a)` and
`σ (ψ j * e i) = sgn_j(i) • ψ (m - 2 - j) * e (rev i)`, where `sgn_j(i) = -1` if `i_j = i_{j+1}`
and `1` otherwise (see `sigma_ψ_mul_e`). It is an involution (`sigma_symm`,
`sigma_sigma`). It requires `Q_{ba}(u, v) = Q_{ab}(v, u)` (`KLRSymm Q`). -/
noncomputable def sigma (hQ : KLRSymm Q) : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (sigmaHom hQ) (sigmaHom hQ) (sigmaHom_comp_self hQ) (sigmaHom_comp_self hQ)

theorem sigma_apply (a : A) : sigma hQ a = sigmaHom hQ a := rfl

@[simp] theorem sigma_e (i : Seq ν) : sigma hQ (e i : A) = e i.rev := sigmaHom_e hQ i

@[simp] theorem sigma_x (a : Fin m) : sigma hQ (x a : A) = x a.rev := sigmaHom_x hQ a

theorem sigma_ψ {j : ℕ} (h : j + 1 < m) :
    sigma hQ (ψ j : A) = ∑ i, sgn k j i • (ψ (m - 2 - j) * e i.rev) := by
  rw [sigma_apply, sigmaHom_ψ, sigmaψ_of_lt h, sgnE, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem sigma_ψ_of_le {j : ℕ} (h : m ≤ j + 1) : sigma hQ (ψ j : A) = 0 := by
  rw [sigma_apply, sigmaHom_ψ, sigmaψ_of_le h]

/-- The vertical flip of a crossing with bottom sequence `i`: it is the mirror crossing with
bottom sequence `rev i`, multiplied by `-1` exactly when the two strands have equal labels. -/
theorem sigma_ψ_mul_e {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    sigma hQ (ψ j * e i : A) =
      (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then -1 else 1 : k) •
        (ψ (m - 2 - j) * e i.rev) := by
  rw [map_mul, sigma_apply, sigmaHom_ψ, sigma_e, sigmaψ_mul_e_rev h, sgn_of_lt h]

/-- `σ` is an involution. -/
@[simp] theorem sigma_sigma (a : A) : sigma hQ (sigma hQ a) = a := sigmaHom_sigmaHom hQ a

theorem sigma_symm : (sigma hQ : A ≃ₐ[k] A).symm = sigma hQ := rfl

omit hQ in
theorem hflip_sigmaψ (j : ℕ) : hflip (sigmaψ Q j : A) = sigmaψ Q j := by
  by_cases h : j + 1 < m
  · rw [sigmaψ_of_lt h, hflip_mul, hflip_sgnE, hflip_ψ, ψ_rev_mul_sgnE h]
  · rw [sigmaψ_of_le (by omega), hflip_zero]

private theorem flip_comp_sigma :
    (flipAlgHom k Q ν).comp (sigmaHom hQ) = (AlgHom.op (sigmaHom hQ)).comp (flipAlgHom k Q ν) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  apply unop_injective
  change hflip (sigmaHom hQ (mk k Q ν (FreeAlgebra.ι k g))) =
    sigmaHom hQ (hflip (mk k Q ν (FreeAlgebra.ι k g)))
  cases g with
  | idem i =>
    change hflip (sigmaHom hQ (e i)) = sigmaHom hQ (hflip (e i))
    rw [sigmaHom_e, hflip_e, hflip_e, sigmaHom_e]
  | dot a =>
    change hflip (sigmaHom hQ (x a)) = sigmaHom hQ (hflip (x a))
    rw [sigmaHom_x, hflip_x, hflip_x, sigmaHom_x]
  | cross j =>
    change hflip (sigmaHom hQ (ψ j)) = sigmaHom hQ (hflip (ψ j))
    rw [sigmaHom_ψ, hflip_ψ, sigmaHom_ψ, hflip_sigmaψ]

/-- **KL I, §2.1.** The vertical flip `σ` commutes with the horizontal flip. -/
theorem hflip_sigma (a : A) : hflip (sigma hQ a) = sigma hQ (hflip a) :=
  congrArg unop (AlgHom.congr_fun (flip_comp_sigma hQ) a)

/-- `σ` commutes with the horizontal flip, stated with `flipH`. -/
theorem flipH_sigma (a : A) :
    flipH k Q ν (sigma hQ a) = op (sigma hQ ((flipH k Q ν a).unop)) := by
  rw [flipH_apply, hflip_sigma]; rfl

end sigma

end KLRAlgebra

/-! ### The simply-laced data of KL I -/

/-- The simply-laced KL I data `Q_{ab} = u + v` (if `a — b` is an edge) and `Q_{ab} = 1`
(otherwise) satisfy the symmetry hypothesis of the vertical flip. -/
theorem klQ_symm (Γ : SimpleGraph I) [DecidableRel Γ.Adj] :
    KLRSymm (klQ (k := k) Γ) := by
  intro a b _
  simp only [klQ, Γ.adj_comm b a]
  split_ifs
  · simp [add_comm]
  · simp

end Categorification.KLR
