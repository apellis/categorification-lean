/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Defs

/-!
# The polynomial representation of `R(ν)`

KL I, Proposition 2.3 (arXiv:0803.4121v2, §2.3): the operators `opE`, `opX`, `opΨ P`
of `Categorification.KLR.PolyRep.Defs` satisfy the defining relations of `R(ν)`, and
hence define an algebra homomorphism `polyRep : R(ν) → End_k(Pol_ν)`.

We work in the generality of arbitrary polynomials `P i j ∈ k[u, v]` defining the
action of crossings, subject to the compatibility

  `Q i j (u, v) = P j i (u, v) * P i j (v, u)` for `i ≠ j`

(`hPQ` below). The KL I case (`P i j = u + v` for an edge oriented `i → j`, and `1`
otherwise) is in `Categorification.KLR.KL1`. The value of `Q i i` is irrelevant.

## Proof outline

On the component of a sequence, a crossing acts through the "local" operator
`crossOp P a b p q` (labels `a b` at positions `p q`): the divided difference `∂_{pq}`
if `a = b`, and `f ↦ P a b (x_p, x_q) · s_{pq} f` otherwise. All relations reduce to
identities between these operators, which follow from the theory of divided
differences in `Categorification.Algebra.DividedDifference`. For the braid relation on a
sequence `a b a` (positions `x, y, z`), using `s₁ ∂₂ = ∂₁₃ s₁`, `s₂ ∂₁ = ∂₁₃ s₂` and the
twisted Leibniz rule one finds that `ψ₁ψ₂ψ₁ - ψ₂ψ₁ψ₂` acts by multiplication by
`(P_ba(x,y) P_ab(y,x) - P_ab(y,z) P_ba(z,y)) / (x - z) = Q̄_ab(x, y, z)`.

## Main definitions and results

* `PolyRep.opMul` : multiplication by a polynomial, as an algebra map to `End(Pol_ν)`.
* `PolyRep.polyRep hPQ : KLRAlgebra k Q ν →ₐ[k] Module.End k (Pol k ν)`, with
  `polyRep_e`, `polyRep_x`, `polyRep_ψ`.
-/

namespace Categorification.KLR.PolyRep

open MvPolynomial TypeA Equiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-! ### Renaming helpers -/

section rename

variable {n n' : ℕ}

theorem rename_rename_vec2 (g : Fin n → Fin n') (p q : Fin n) (F : MvPolynomial (Fin 2) k) :
    rename g (rename ![p, q] F) = rename ![g p, g q] F := by
  have : g ∘ ![p, q] = ![g p, g q] := by funext c; fin_cases c <;> rfl
  rw [rename_rename, this]

theorem rename_vec2_rename_swap (p q : Fin n) (F : MvPolynomial (Fin 2) k) :
    rename ![p, q] (rename ![1, 0] F) = rename ![q, p] F := by
  have : ![p, q] ∘ ![(1 : Fin 2), 0] = ![q, p] := by funext c; fin_cases c <;> rfl
  rw [rename_rename, this]

theorem rename_vec3_rename_vec2 (p₀ p₁ p₂ : Fin n) (u v : Fin 3) (F : MvPolynomial (Fin 2) k) :
    rename ![p₀, p₁, p₂] (rename ![u, v] F) = rename ![![p₀, p₁, p₂] u, ![p₀, p₁, p₂] v] F :=
  rename_rename_vec2 _ _ _ _

/-- Renaming by a transposition commutes with divided differences (conjugation). -/
theorem rename_swap_ddiff_conj {p q a b : Fin n} (hab : a ≠ b) (f : MvPolynomial (Fin n) k) :
    rename (swap p q) (ddiff a b f) = ddiff (swap p q a) (swap p q b) (rename (swap p q) f) :=
  rename_ddiff (swap p q).injective hab f

theorem swap_mul_swap_comm {p q p' q' : Fin n} (h₁ : p' ≠ p) (h₂ : p' ≠ q) (h₃ : q' ≠ p)
    (h₄ : q' ≠ q) : swap p q * swap p' q' = swap p' q' * swap p q := by
  have h : swap p q * swap p' q' * (swap p q)⁻¹ = swap p' q' := by
    rw [← swap_apply_apply, swap_apply_of_ne_of_ne h₁ h₂, swap_apply_of_ne_of_ne h₃ h₄]
  rwa [mul_inv_eq_iff_eq_mul] at h

theorem rename_swap_rename_swap_comm {p q p' q' : Fin n} (h₁ : p' ≠ p) (h₂ : p' ≠ q)
    (h₃ : q' ≠ p) (h₄ : q' ≠ q) (f : MvPolynomial (Fin n) k) :
    rename (swap p q) (rename (swap p' q') f) = rename (swap p' q') (rename (swap p q) f) := by
  rw [rename_rename, rename_rename, ← Perm.coe_mul, ← Perm.coe_mul,
    swap_mul_swap_comm h₁ h₂ h₃ h₄]

end rename

/-! ### Local crossing operators -/

section crossOp

variable {n : ℕ} (P : I → I → MvPolynomial (Fin 2) k)

/-- The action of a crossing of strands labelled `a, b` at positions `p, q`: the divided
difference `∂_{pq}` if `a = b`, and `f ↦ P a b (x_p, x_q) · s_{pq} f` otherwise. -/
noncomputable def crossOp (a b : I) (p q : Fin n) :
    MvPolynomial (Fin n) k →ₗ[k] MvPolynomial (Fin n) k :=
  if a = b then ddiff p q else
    (LinearMap.mulLeft k (rename ![p, q] (P a b))).comp (rename (swap p q)).toLinearMap

theorem crossOp_self (a : I) (p q : Fin n) (g : MvPolynomial (Fin n) k) :
    crossOp P a a p q g = ddiff p q g := by
  simp [crossOp]

theorem crossOp_of_ne {a b : I} (hab : a ≠ b) (p q : Fin n) (g : MvPolynomial (Fin n) k) :
    crossOp P a b p q g = rename ![p, q] (P a b) * rename (swap p q) g := by
  simp [crossOp, hab]

variable {p q : Fin n}

/-- Dots on other strands commute with crossings. -/
theorem crossOp_X_mul (hpq : p ≠ q) (a b : I) {c : Fin n} (hcp : c ≠ p) (hcq : c ≠ q)
    (g : MvPolynomial (Fin n) k) :
    crossOp P a b p q (X c * g) = X c * crossOp P a b p q g := by
  by_cases hab : a = b
  · subst hab
    rw [crossOp_self, crossOp_self, ddiff_mul_of_rename_eq hpq]
    rw [rename_X, swap_apply_of_ne_of_ne hcp hcq]
  · rw [crossOp_of_ne P hab, crossOp_of_ne P hab, map_mul, rename_X,
      swap_apply_of_ne_of_ne hcp hcq]
    ring

/-- KL I (2.4)–(2.5): `x_p ψ - ψ x_q = [a = b]`. -/
theorem crossOp_dot_left (hpq : p ≠ q) (a b : I) (g : MvPolynomial (Fin n) k) :
    X p * crossOp P a b p q g - crossOp P a b p q (X q * g) = if a = b then g else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [crossOp_self, crossOp_self, ddiff_mul hpq, ddiff_X_right hpq, rename_X,
      swap_apply_right, if_pos rfl]
    ring
  · rw [crossOp_of_ne P hab, crossOp_of_ne P hab, if_neg hab, map_mul, rename_X,
      swap_apply_right]
    ring

/-- KL I (2.4), (2.6): `ψ x_p - x_q ψ = [a = b]`. -/
theorem crossOp_dot_right (hpq : p ≠ q) (a b : I) (g : MvPolynomial (Fin n) k) :
    crossOp P a b p q (X p * g) - X q * crossOp P a b p q g = if a = b then g else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [crossOp_self, crossOp_self, ddiff_mul hpq, ddiff_X_left hpq, rename_X,
      swap_apply_left, if_pos rfl]
    ring
  · rw [crossOp_of_ne P hab, crossOp_of_ne P hab, if_neg hab, map_mul, rename_X,
      swap_apply_left]
    ring

/-- The quadratic relation: `ψ² = 0` on equal labels and `Q a b (x_p, x_q)` otherwise. -/
theorem crossOp_sq {Q : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) (hpq : p ≠ q) (a b : I)
    (g : MvPolynomial (Fin n) k) :
    crossOp P b a p q (crossOp P a b p q g) =
      if a = b then 0 else rename ![p, q] (Q a b) * g := by
  by_cases hab : a = b
  · subst hab
    rw [crossOp_self, crossOp_self, ddiff_ddiff hpq, if_pos rfl]
  · rw [crossOp_of_ne P hab, crossOp_of_ne P (Ne.symm hab), if_neg hab, hPQ a b hab, map_mul,
      map_mul, rename_swap_rename_swap, rename_rename_vec2, swap_apply_left, swap_apply_right,
      rename_vec2_rename_swap]
    ring

/-- Crossings at disjoint pairs of positions commute. -/
theorem crossOp_comm {p' q' : Fin n} (hpq : p ≠ q) (hpq' : p' ≠ q') (h₁ : p' ≠ p)
    (h₂ : p' ≠ q) (h₃ : q' ≠ p) (h₄ : q' ≠ q) (a b a' b' : I) (g : MvPolynomial (Fin n) k) :
    crossOp P a b p q (crossOp P a' b' p' q' g) = crossOp P a' b' p' q' (crossOp P a b p q g) := by
  have hR : ∀ (F : MvPolynomial (Fin 2) k), rename (swap p q) (rename ![p', q'] F) =
      rename ![p', q'] F := fun F => by
    rw [rename_rename_vec2, swap_apply_of_ne_of_ne h₁ h₂, swap_apply_of_ne_of_ne h₃ h₄]
  have hR' : ∀ (F : MvPolynomial (Fin 2) k), rename (swap p' q') (rename ![p, q] F) =
      rename ![p, q] F := fun F => by
    rw [rename_rename_vec2, swap_apply_of_ne_of_ne (Ne.symm h₁) (Ne.symm h₃),
      swap_apply_of_ne_of_ne (Ne.symm h₂) (Ne.symm h₄)]
  by_cases hab : a = b <;> by_cases hab' : a' = b'
  · subst hab hab'
    simp only [crossOp_self]
    exact ddiff_ddiff_comm hpq hpq' h₁.symm h₃.symm h₂.symm h₄.symm g
  · subst hab
    rw [crossOp_self, crossOp_self, crossOp_of_ne P hab', crossOp_of_ne P hab',
      ddiff_mul_of_rename_eq hpq (hR _), rename_swap_ddiff_conj hpq,
      swap_apply_of_ne_of_ne (Ne.symm h₁) (Ne.symm h₃),
      swap_apply_of_ne_of_ne (Ne.symm h₂) (Ne.symm h₄)]
  · subst hab'
    rw [crossOp_self, crossOp_self, crossOp_of_ne P hab, crossOp_of_ne P hab,
      ddiff_mul_of_rename_eq hpq' (hR' _), rename_swap_ddiff_conj hpq',
      swap_apply_of_ne_of_ne h₁ h₂, swap_apply_of_ne_of_ne h₃ h₄]
  · rw [crossOp_of_ne P hab, crossOp_of_ne P hab, crossOp_of_ne P hab', crossOp_of_ne P hab',
      map_mul, map_mul, hR, hR', rename_swap_rename_swap_comm h₁ h₂ h₃ h₄]
    ring

omit [DecidableEq I] in
/-- The correction term of the braid relation: for `a ≠ b`, `Q̄_{ab}(x_{p₀}, x_{p₁}, x_{p₂})`
equals `P_ba(x₀, x₁) ∂₀₂ P_ab(x₁, x₀) - P_ab(x₁, x₂) ∂₀₂ P_ba(x₂, x₁)`. -/
theorem rename_qbar {Q : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) {a b : I} (hab : a ≠ b)
    {p₀ p₁ p₂ : Fin n} (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) (h01 : p₀ ≠ p₁) :
    rename ![p₀, p₁, p₂] (qbar (Q a b)) =
      rename ![p₀, p₁] (P b a) * ddiff p₀ p₂ (rename ![p₁, p₀] (P a b)) -
        rename ![p₁, p₂] (P a b) * ddiff p₀ p₂ (rename ![p₂, p₁] (P b a)) := by
  apply X_sub_X_mul_left_cancel h02
  have hq := congrArg (rename ![p₀, p₁, p₂]) (qbar_spec (Q a b))
  rw [map_mul, map_sub, map_sub, rename_vec3_rename_vec2, rename_vec3_rename_vec2, rename_X,
    rename_X] at hq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hq
  rw [hq, hPQ a b hab, map_mul, map_mul, rename_vec2_rename_swap, rename_vec2_rename_swap]
  have e1 := ddiff_spec h02 (rename ![p₁, p₀] (P a b))
  have e2 := ddiff_spec h02 (rename ![p₂, p₁] (P b a))
  rw [rename_rename_vec2, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm h01) h12] at e1
  rw [rename_rename_vec2, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm h01) h12] at e2
  linear_combination -rename ![p₀, p₁] (P b a) * e1 + rename ![p₁, p₂] (P a b) * e2

/-- The braid relation for local crossing operators on labels `a b c` at positions
`p₀ p₁ p₂`: `ψ₁ψ₂ψ₁ - ψ₂ψ₁ψ₂` acts by `Q̄_{ab}(x_{p₀}, x_{p₁}, x_{p₂})` if `a = c ≠ b` and
by `0` otherwise. (Operators are composed right to left.) -/
theorem crossOp_braid {Q : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) {p₀ p₁ p₂ : Fin n}
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) (a b c : I) (g : MvPolynomial (Fin n) k) :
    crossOp P b c p₀ p₁ (crossOp P a c p₁ p₂ (crossOp P a b p₀ p₁ g)) -
      crossOp P a b p₁ p₂ (crossOp P a c p₀ p₁ (crossOp P b c p₁ p₂ g)) =
      if a = c ∧ a ≠ b then rename ![p₀, p₁, p₂] (qbar (Q a b)) * g else 0 := by
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h21 := Ne.symm h12
  by_cases hab : a = b
  · subst hab
    by_cases hac : a = c
    · subst hac
      simp only [crossOp_self, ne_eq, not_true_eq_false, and_false, if_false]
      rw [ddiff_braid h01 h12 h02, sub_self]
    · rw [if_neg (by tauto)]
      simp only [crossOp_self, crossOp_of_ne P hac, map_mul, rename_rename_vec2,
        swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne, rename_swap_ddiff_conj, h01, h02,
        h12, h10, h20, h21, ne_eq, not_false_eq_true]
      have hsym : rename (swap p₁ p₂) (rename ![p₀, p₁] (P a c) * rename ![p₀, p₂] (P a c)) =
          rename ![p₀, p₁] (P a c) * rename ![p₀, p₂] (P a c) := by
        rw [map_mul, rename_rename_vec2, rename_rename_vec2, swap_apply_left, swap_apply_right,
          swap_apply_of_ne_of_ne h01 h02, mul_comm]
      rw [← mul_assoc _ _ (rename (swap p₀ p₁) _), ddiff_mul_of_rename_eq h12 hsym]
      ring
  · by_cases hbc : b = c
    · subst hbc
      rw [if_neg (by tauto)]
      simp only [crossOp_self, crossOp_of_ne P hab, map_mul, rename_rename_vec2,
        swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne, rename_swap_ddiff_conj, h01, h02,
        h12, h10, h20, h21, ne_eq, not_false_eq_true]
      have hsym : rename (swap p₀ p₁) (rename ![p₁, p₂] (P a b) * rename ![p₀, p₂] (P a b)) =
          rename ![p₁, p₂] (P a b) * rename ![p₀, p₂] (P a b) := by
        rw [map_mul, rename_rename_vec2, rename_rename_vec2, swap_apply_left, swap_apply_right,
          swap_apply_of_ne_of_ne h20 h21, mul_comm]
      rw [← mul_assoc _ _ (rename (swap p₁ p₂) _), ddiff_mul_of_rename_eq h01 hsym]
      ring
    · by_cases hac : a = c
      · subst hac
        rw [if_pos ⟨rfl, hab⟩]
        simp only [crossOp_self, crossOp_of_ne P hab, crossOp_of_ne P (Ne.symm hab), map_mul,
          rename_rename_vec2, swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne,
          rename_swap_ddiff_conj, rename_swap_rename_swap, h01, h02, h12, h10, h20, h21, ne_eq,
          not_false_eq_true]
        rw [ddiff_mul h02, ddiff_mul h02, rename_qbar P hPQ hab h02 h12 h01, rename_rename_vec2,
          rename_rename_vec2, swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne h10 h12]
        ring
      · rw [if_neg (by tauto)]
        simp only [crossOp_of_ne P hab, crossOp_of_ne P hbc, crossOp_of_ne P hac, map_mul,
          rename_rename_vec2, swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne, h01, h02,
          h12, h10, h20, h21, ne_eq, not_false_eq_true]
        rw [rename_swap_braid h01 h12 h02]
        ring

end crossOp

/-! ### Sequences and the operators on `Pol_ν` -/

section Seq

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

omit [DecidableEq I] in
theorem swap_smul_apply (p q : Fin m) (t : Seq ν) (c : Fin m) :
    (swap p q • t).1 c = t.1 (swap p q c) := by
  rw [Seq.smul_apply, symm_swap]

omit [DecidableEq I] in
@[simp] theorem swap_smul_swap_smul (p q : Fin m) (t : Seq ν) : swap p q • swap p q • t = t := by
  rw [smul_smul, swap_mul_self, one_smul]

omit [DecidableEq I] in
/-- Swapping two equal labels does not change a sequence. -/
theorem swap_smul_eq_self {p q : Fin m} {t : Seq ν} (h : t.1 p = t.1 q) : swap p q • t = t := by
  apply Subtype.ext
  funext c
  rw [swap_smul_apply, swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

omit [DecidableEq I] in
theorem sadj_eq {j : ℕ} (h : j + 1 < m) : sadj m j = swap ⟨j, by omega⟩ ⟨j + 1, h⟩ := dif_pos h

theorem crossComp_eq (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (h : j + 1 < m) (t : Seq ν) :
    crossComp P j h t =
      crossOp P (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, h⟩) ⟨j, by omega⟩ ⟨j + 1, h⟩ := by
  simp only [crossComp, crossOp, sadj_eq h, Seq.lbl]

/-- The crossing `ψ_j` in terms of `crossOp`, for positions `p = j`, `q = j + 1`: the
component `t` of `ψ_j f` is `crossOp` (for the labels of `s_j t`) applied to `f (s_j t)`. -/
theorem opΨ_apply_of_eq (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ} {p q : Fin m}
    (hp : p.val = j) (hq : q.val = j + 1) (f : Pol k ν) (t : Seq ν) :
    opΨ P j f t = crossOp P (t.1 q) (t.1 p) p q (f (swap p q • t)) := by
  obtain ⟨p, hp'⟩ := p
  obtain ⟨q, hq'⟩ := q
  simp only at hp hq
  subst hp hq
  rw [opΨ_apply P p hq', crossComp_eq, sadj_eq hq', swap_smul_apply, swap_smul_apply,
    swap_apply_left, swap_apply_right]

omit [DecidableEq I] in
theorem sadj_eq_swap {j : ℕ} {p q : Fin m} (hp : p.val = j) (hq : q.val = j + 1) :
    sadj m j = swap p q := by
  have h : j + 1 < m := hq ▸ q.2
  rw [sadj_eq h]
  congr 1 <;> exact Fin.ext (by simp [hp, hq])

theorem opΨ_eq_zero (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ} (h : m ≤ j + 1) :
    (opΨ P j : Module.End k (Pol k ν)) = 0 := by
  simp [opΨ, show ¬ j + 1 < m by omega]

variable (ν) in
/-- Multiplication by a polynomial, acting on every component of `Pol_ν`. -/
noncomputable def opMul : MvPolynomial (Fin m) k →ₐ[k] Module.End k (Pol k ν) :=
  Algebra.lsmul k k (Pol k ν)

omit [DecidableEq I] in
@[simp] theorem opMul_apply (g : MvPolynomial (Fin m) k) (f : Pol k ν) (t : Seq ν) :
    opMul ν g f t = g * f t := rfl

omit [DecidableEq I] in
theorem opX_eq_opMul (a : Fin m) : (opX a : Module.End k (Pol k ν)) = opMul ν (X a) := rfl

/-! #### The relations -/

theorem opE_mul_opE (i j : Seq ν) :
    (opE i * opE j : Module.End k (Pol k ν)) = if i = j then opE i else 0 := by
  apply LinearMap.ext; intro f; funext t
  split_ifs with hij
  · subst hij; simp only [Module.End.mul_apply, opE_apply]; split_ifs <;> rfl
  · simp only [Module.End.mul_apply, opE_apply, LinearMap.zero_apply, Pi.zero_apply]
    split_ifs <;> rfl

theorem sum_opE : (∑ i, opE i : Module.End k (Pol k ν)) = 1 := by
  apply LinearMap.ext; intro f; funext t
  simp [LinearMap.coeFn_sum, Finset.sum_apply, opE_apply]

theorem opX_mul_opE (a : Fin m) (i : Seq ν) :
    (opX a * opE i : Module.End k (Pol k ν)) = opE i * opX a := by
  apply LinearMap.ext; intro f; funext t
  simp only [Module.End.mul_apply, opE_apply, opX_apply]
  split_ifs <;> simp

theorem opΨ_mul_opE (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (i : Seq ν) :
    (opΨ P j * opE i : Module.End k (Pol k ν)) = opE (sadj m j • i) * opΨ P j := by
  by_cases h : j + 1 < m
  · obtain ⟨p, hp⟩ : ∃ p : Fin m, p.val = j := ⟨⟨j, by omega⟩, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : Fin m, q.val = j + 1 := ⟨⟨j + 1, h⟩, rfl⟩
    apply LinearMap.ext; intro f; funext t
    simp only [Module.End.mul_apply, opE_apply, opΨ_apply_of_eq P hp hq, sadj_eq_swap hp hq]
    by_cases ht : t = swap p q • i
    · subst ht; simp
    · rw [if_neg ht, if_neg, map_zero]
      rintro rfl; exact ht (swap_smul_swap_smul _ _ _).symm
  · rw [opΨ_eq_zero P (j := j) (by omega), zero_mul, mul_zero]

omit [DecidableEq I] in
theorem opX_mul_opX (a b : Fin m) :
    (opX a * opX b : Module.End k (Pol k ν)) = opX b * opX a := by
  apply LinearMap.ext; intro f; funext t
  simp only [Module.End.mul_apply, opX_apply]; ring

theorem opΨ_mul_opΨ (P : I → I → MvPolynomial (Fin 2) k) {j l : ℕ} (hjl : j + 1 < l) :
    (opΨ P j * opΨ P l : Module.End k (Pol k ν)) = opΨ P l * opΨ P j := by
  by_cases hl : l + 1 < m
  · apply LinearMap.ext; intro f; funext t
    obtain ⟨pj, hpj⟩ : ∃ p : Fin m, p.val = j := ⟨⟨j, by omega⟩, rfl⟩
    obtain ⟨qj, hqj⟩ : ∃ q : Fin m, q.val = j + 1 := ⟨⟨j + 1, by omega⟩, rfl⟩
    obtain ⟨pl, hpl⟩ : ∃ p : Fin m, p.val = l := ⟨⟨l, by omega⟩, rfl⟩
    obtain ⟨ql, hql⟩ : ∃ q : Fin m, q.val = l + 1 := ⟨⟨l + 1, hl⟩, rfl⟩
    have h₁ : pl ≠ pj := fun e => by have := congrArg Fin.val e; omega
    have h₂ : pl ≠ qj := fun e => by have := congrArg Fin.val e; omega
    have h₃ : ql ≠ pj := fun e => by have := congrArg Fin.val e; omega
    have h₄ : ql ≠ qj := fun e => by have := congrArg Fin.val e; omega
    have hj : pj ≠ qj := fun e => by have := congrArg Fin.val e; omega
    have hl' : pl ≠ ql := fun e => by have := congrArg Fin.val e; omega
    simp only [Module.End.mul_apply, opΨ_apply_of_eq P hpj hqj,
      opΨ_apply_of_eq P hpl hql, swap_smul_apply,
      swap_apply_of_ne_of_ne h₁ h₂, swap_apply_of_ne_of_ne h₃ h₄,
      swap_apply_of_ne_of_ne h₁.symm h₃.symm, swap_apply_of_ne_of_ne h₂.symm h₄.symm]
    rw [smul_smul, smul_smul, swap_mul_swap_comm h₁ h₂ h₃ h₄]
    exact crossOp_comm P hj hl' h₁ h₂ h₃ h₄ _ _ _ _ _
  · rw [opΨ_eq_zero P (j := l) (by omega), zero_mul, mul_zero]

theorem opX_mul_opΨ (P : I → I → MvPolynomial (Fin 2) k) (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j)
    (h₂ : a.val ≠ j + 1) : (opX a * opΨ P j : Module.End k (Pol k ν)) = opΨ P j * opX a := by
  by_cases h : j + 1 < m
  · obtain ⟨p, hp⟩ : ∃ p : Fin m, p.val = j := ⟨⟨j, by omega⟩, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : Fin m, q.val = j + 1 := ⟨⟨j + 1, h⟩, rfl⟩
    apply LinearMap.ext; intro f; funext t
    simp only [Module.End.mul_apply, opX_apply, opΨ_apply_of_eq P hp hq]
    rw [crossOp_X_mul P (fun e => by have := congrArg Fin.val e; omega) _ _
      (fun e => h₁ (by rw [e, hp])) (fun e => h₂ (by rw [e, hq]))]
  · rw [opΨ_eq_zero P (j := j) (by omega), zero_mul, mul_zero]

/-- KL I (2.4)/(2.5): `(x_j ψ_j - ψ_j x_{j+1}) 1_i = [i_j = i_{j+1}] 1_i`. -/
theorem opX_opΨ_sub (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ} {p q : Fin m}
    (hp : p.val = j) (hq : q.val = j + 1) (i : Seq ν) :
    ((opX p * opΨ P j - opΨ P j * opX q) * opE i : Module.End k (Pol k ν)) =
      if i.1 p = i.1 q then opE i else 0 := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  apply LinearMap.ext; intro f; funext t
  simp only [LinearMap.sub_apply, Module.End.mul_apply, opX_apply, opΨ_apply_of_eq P hp hq,
    opE_apply, Pi.sub_apply]
  by_cases hst : swap p q • t = i
  · obtain rfl : t = swap p q • i := by rw [← hst, swap_smul_swap_smul]
    simp only [swap_smul_swap_smul, if_true, swap_smul_apply, swap_apply_left, swap_apply_right]
    rw [crossOp_dot_left P hpq]
    split_ifs with he
    · rw [opE_apply, swap_smul_eq_self he, if_pos rfl]
    · rfl
  · rw [if_neg hst, mul_zero, map_zero, mul_zero, sub_self]
    split_ifs with he
    · rw [opE_apply, if_neg]
      rintro rfl; exact hst (swap_smul_eq_self he)
    · rfl

/-- KL I (2.4)/(2.6): `(ψ_j x_j - x_{j+1} ψ_j) 1_i = [i_j = i_{j+1}] 1_i`. -/
theorem opΨ_opX_sub (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ} {p q : Fin m}
    (hp : p.val = j) (hq : q.val = j + 1) (i : Seq ν) :
    ((opΨ P j * opX p - opX q * opΨ P j) * opE i : Module.End k (Pol k ν)) =
      if i.1 p = i.1 q then opE i else 0 := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  apply LinearMap.ext; intro f; funext t
  simp only [LinearMap.sub_apply, Module.End.mul_apply, opX_apply, opΨ_apply_of_eq P hp hq,
    opE_apply, Pi.sub_apply]
  by_cases hst : swap p q • t = i
  · obtain rfl : t = swap p q • i := by rw [← hst, swap_smul_swap_smul]
    simp only [swap_smul_swap_smul, if_true, swap_smul_apply, swap_apply_left, swap_apply_right]
    rw [crossOp_dot_right P hpq]
    split_ifs with he
    · rw [opE_apply, swap_smul_eq_self he, if_pos rfl]
    · rfl
  · rw [if_neg hst, mul_zero, map_zero, mul_zero, sub_self]
    split_ifs with he
    · rw [opE_apply, if_neg]
      rintro rfl; exact hst (swap_smul_eq_self he)
    · rfl

/-- KL I (2.3): `ψ_j² 1_i = 0` if `i_j = i_{j+1}`, and `Q_{i_j i_{j+1}}(x_j, x_{j+1}) 1_i`
otherwise. -/
theorem opΨ_sq (P : I → I → MvPolynomial (Fin 2) k) {Q : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) {j : ℕ} {p q : Fin m}
    (hp : p.val = j) (hq : q.val = j + 1) (i : Seq ν) :
    (opΨ P j * opΨ P j * opE i : Module.End k (Pol k ν)) =
      if i.1 p = i.1 q then 0 else opMul ν (rename ![p, q] (Q (i.1 p) (i.1 q))) * opE i := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  apply LinearMap.ext; intro f; funext t
  simp only [Module.End.mul_apply, opΨ_apply_of_eq P hp hq, opE_apply, swap_smul_apply,
    swap_apply_left, swap_apply_right, swap_smul_swap_smul]
  by_cases ht : t = i
  · subst ht
    rw [if_pos rfl, crossOp_sq P hPQ hpq]
    split_ifs <;> simp
  · rw [if_neg ht, map_zero, map_zero]
    split_ifs <;> simp [ht]

omit [DecidableEq I] in
theorem swap_smul_braid {p₀ p₁ p₂ : Fin m} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂)
    (t : Seq ν) :
    swap p₁ p₂ • swap p₀ p₁ • swap p₁ p₂ • t = swap p₀ p₁ • swap p₁ p₂ • swap p₀ p₁ • t := by
  simp only [smul_smul]
  rw [← mul_assoc, ← mul_assoc, swap_braid h01 h12 h02]

omit [DecidableEq I] in
theorem swap_smul_braid_eq_self {p₀ p₁ p₂ : Fin m} (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) {t : Seq ν} (h : t.1 p₀ = t.1 p₂) :
    swap p₀ p₁ • swap p₁ p₂ • swap p₀ p₁ • t = t := by
  simp only [smul_smul]
  rw [← mul_assoc, swap_mul_swap_mul_swap_eq h12 h02, swap_smul_eq_self h]

/-- KL I (2.7)/(2.8): the braid relation
`(ψ_j ψ_{j+1} ψ_j - ψ_{j+1} ψ_j ψ_{j+1}) 1_i = Q̄_{i_j i_{j+1}}(x_j, x_{j+1}, x_{j+2}) 1_i`
if `i_j = i_{j+2} ≠ i_{j+1}`, and `0` otherwise. -/
theorem opΨ_braid (P : I → I → MvPolynomial (Fin 2) k) {Q : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) {j : ℕ} {p₀ p₁ p₂ : Fin m}
    (h0 : p₀.val = j) (h1 : p₁.val = j + 1) (h2 : p₂.val = j + 2) (i : Seq ν) :
    ((opΨ P j * opΨ P (j + 1) * opΨ P j - opΨ P (j + 1) * opΨ P j * opΨ P (j + 1)) * opE i :
        Module.End k (Pol k ν)) =
      if i.1 p₀ = i.1 p₂ ∧ i.1 p₀ ≠ i.1 p₁ then
        opMul ν (rename ![p₀, p₁, p₂] (qbar (Q (i.1 p₀) (i.1 p₁)))) * opE i
      else 0 := by
  have h01 : p₀ ≠ p₁ := fun e => by have := congrArg Fin.val e; omega
  have h02 : p₀ ≠ p₂ := fun e => by have := congrArg Fin.val e; omega
  have h12 : p₁ ≠ p₂ := fun e => by have := congrArg Fin.val e; omega
  have h2' : p₂.val = j + 1 + 1 := h2
  apply LinearMap.ext; intro f; funext t
  simp only [LinearMap.sub_apply, Module.End.mul_apply, opΨ_apply_of_eq P h0 h1,
    opΨ_apply_of_eq P h1 h2', opE_apply, Pi.sub_apply, swap_smul_apply, swap_apply_left,
    swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12),
    swap_apply_of_ne_of_ne h01 h02]
  rw [swap_smul_braid h01 h02 h12, crossOp_braid P hPQ h01 h02 h12]
  by_cases hw : swap p₀ p₁ • swap p₁ p₂ • swap p₀ p₁ • t = i
  · obtain rfl : t = swap p₀ p₁ • swap p₁ p₂ • swap p₀ p₁ • i := by
      rw [← hw]; simp only [swap_smul_swap_smul]
    simp only [swap_smul_swap_smul, if_true, swap_smul_apply, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12), swap_apply_of_ne_of_ne h01 h02]
    split_ifs with hc
    · rw [Module.End.mul_apply, opMul_apply, opE_apply, swap_smul_braid_eq_self h02 h12 hc.1,
        if_pos rfl]
    · rfl
  · rw [if_neg hw, mul_zero, ite_self]
    split_ifs with hc
    · rw [Module.End.mul_apply, opMul_apply, opE_apply, if_neg, mul_zero]
      rintro rfl; exact hw (swap_smul_braid_eq_self h02 h12 hc.1)
    · rfl

end Seq

section Rep

variable {n : ℕ} {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

omit [DecidableEq I] in
theorem algHom_ncEval (F : A →ₐ[k] B) (y : Fin n → A) (p : MvPolynomial (Fin n) k) :
    F (ncEval y p) = ncEval (fun a => F (y a)) p := by
  simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow]

omit [DecidableEq I] in
/-- Evaluating at the images of variables under an algebra map is renaming. -/
theorem ncEval_algHom_X {n' : ℕ} (φ : MvPolynomial (Fin n') k →ₐ[k] B) (v : Fin n → Fin n')
    (p : MvPolynomial (Fin n) k) : ncEval (fun a => φ (X (v a))) p = φ (rename v p) := by
  conv_rhs => rw [p.as_sum]
  simp only [ncEval, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rename_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_fintype _ _
    (fun _ => pow_zero _), ← List.prod_ofFn, map_mul, algHom_C, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow]
  rfl

end Rep

/-! ### The representation -/

section polyRep

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

variable (ν) in
/-- The operators attached to the generators of `R(ν)`. -/
noncomputable def genOp (P : I → I → MvPolynomial (Fin 2) k) : Gen ν → Module.End k (Pol k ν)
  | .idem i => opE i
  | .dot a => opX a
  | .cross j => opΨ P j

variable (ν) in
/-- The action of the free algebra on the generators. -/
noncomputable def freeRep (P : I → I → MvPolynomial (Fin 2) k) :
    FreeAlgebra k (Gen ν) →ₐ[k] Module.End k (Pol k ν) :=
  FreeAlgebra.lift k (genOp ν P)

variable (P : I → I → MvPolynomial (Fin 2) k)

@[simp] theorem freeRep_fe (i : Seq ν) : freeRep ν P (fe k ν i) = opE i :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeRep_fx (a : Fin m) : freeRep ν P (fx k ν a) = opX a :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeRep_fψ (j : ℕ) : freeRep ν P (fψ k ν j) = opΨ P j :=
  FreeAlgebra.lift_ι_apply _ _

theorem freeRep_ncEval {n : ℕ} (v : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    freeRep ν P (ncEval (fun c => fx k ν (v c)) p) = opMul ν (rename v p) := by
  rw [algHom_ncEval]
  simp only [freeRep_fx, opX_eq_opMul]
  exact ncEval_algHom_X _ _ _

variable {P} {Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))

include hPQ in
/-- KL I, Proposition 2.3 (general form): the operators respect the defining relations. -/
theorem freeRep_rel ⦃x y : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν x y) :
    freeRep ν P x = freeRep ν P y := by
  cases h with
  | idem_mul i j =>
    rw [map_mul, freeRep_fe, freeRep_fe, opE_mul_opE]
    split_ifs <;> simp
  | idem_sum =>
    rw [map_sum, map_one]
    simp only [freeRep_fe]
    exact sum_opE
  | dot_idem a i =>
    simp only [map_mul, freeRep_fe, freeRep_fx]; exact opX_mul_opE a i
  | cross_idem j i =>
    simp only [map_mul, freeRep_fe, freeRep_fψ]; exact opΨ_mul_opE P j i
  | cross_zero j h =>
    rw [freeRep_fψ, opΨ_eq_zero P h, map_zero]
  | dot_dot a b =>
    simp only [map_mul, freeRep_fx]; exact opX_mul_opX a b
  | cross_cross j l h =>
    simp only [map_mul, freeRep_fψ]; exact opΨ_mul_opΨ P h
  | dot_cross a j h₁ h₂ =>
    simp only [map_mul, freeRep_fx, freeRep_fψ]; exact opX_mul_opΨ P a j h₁ h₂
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, freeRep_fx, freeRep_fψ, freeRep_fe, Seq.lbl]
    rw [opX_opΨ_sub P (p := ⟨j, by omega⟩) (q := ⟨j + 1, h⟩) rfl rfl]
    split_ifs <;> simp
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, freeRep_fx, freeRep_fψ, freeRep_fe, Seq.lbl]
    rw [opΨ_opX_sub P (p := ⟨j, by omega⟩) (q := ⟨j + 1, h⟩) rfl rfl]
    split_ifs <;> simp
  | cross_sq j h i =>
    simp only [map_mul, freeRep_fψ, freeRep_fe, Seq.lbl]
    rw [opΨ_sq P hPQ (p := ⟨j, by omega⟩) (q := ⟨j + 1, h⟩) rfl rfl]
    split_ifs
    · simp
    · have hv : ![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, h⟩] =
          fun c => fx k ν (![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩] c) := by
        funext c; fin_cases c <;> rfl
      rw [map_mul, freeRep_fe, hv, freeRep_ncEval]
  | braid j h i =>
    simp only [map_mul, map_sub, freeRep_fψ, freeRep_fe, Seq.lbl]
    rw [opΨ_braid P hPQ (p₀ := ⟨j, by omega⟩) (p₁ := ⟨j + 1, by omega⟩) (p₂ := ⟨j + 2, h⟩)
      rfl rfl rfl]
    split_ifs
    · have hv : ![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, by omega⟩, fx k ν ⟨j + 2, h⟩] =
          fun c => fx k ν (![(⟨j, by omega⟩ : Fin m), ⟨j + 1, by omega⟩, ⟨j + 2, h⟩] c) := by
        funext c; fin_cases c <;> rfl
      rw [map_mul, freeRep_fe, hv, freeRep_ncEval]
    · simp

/-- **KL I, Proposition 2.3** (in the generality of KL II): the polynomial representation
`R(ν) → End_k(Pol_ν)`, for any `P` with `Q i j (u, v) = P j i (u, v) P i j (v, u)`
(`i ≠ j`). -/
noncomputable def polyRep : KLRAlgebra k Q ν →ₐ[k] Module.End k (Pol k ν) :=
  RingQuot.liftAlgHom k ⟨freeRep ν P, fun _ _ h => freeRep_rel hPQ h⟩

theorem polyRep_mk (x : FreeAlgebra k (Gen ν)) :
    polyRep hPQ (KLRAlgebra.mk k Q ν x) = freeRep ν P x := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply k (freeRep ν P) _ x

@[simp] theorem polyRep_e (i : Seq ν) : polyRep hPQ (KLRAlgebra.e i) = opE i := by
  rw [KLRAlgebra.e, polyRep_mk, freeRep_fe]

@[simp] theorem polyRep_x (a : Fin m) : polyRep hPQ (KLRAlgebra.x a) = opX a := by
  rw [KLRAlgebra.x, polyRep_mk, freeRep_fx]

@[simp] theorem polyRep_ψ (j : ℕ) :
    polyRep hPQ (KLRAlgebra.ψ j : KLRAlgebra k Q ν) = opΨ P j := by
  rw [KLRAlgebra.ψ, polyRep_mk, freeRep_fψ]

end polyRep

end Categorification.KLR.PolyRep
