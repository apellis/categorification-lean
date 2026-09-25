/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Sound

/-!
# The simply-laced rings `R(ν)` of Khovanov–Lauda I

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.1 and §2.3.

For a graph `Γ` (no loops or multiple edges: a `SimpleGraph`) with vertex set `I`, KL I
defines `R(ν)` by diagrams modulo the local relations (2.3)–(2.8) (TeX labels `eq_UUzero`,
`eq_ijslide`, `eq_iislide1`, `eq_iislide2`, `eq_r3_easy`, `eq_r3_hard`). This is the
KLR algebra `KLRAlgebra k Q ν` for

  `Q i j (u, v) = u + v` if `i` and `j` are joined by an edge, and `Q i j = 1` otherwise

(`klQ`); KL I works over `k = ℤ`, and we allow any commutative ring `k`.

## Main definitions and results

* `klQ Γ`, `R1 k Γ ν` : the KL I data and algebra.
* `KL1.ψ_sq`, `KL1.x_ψ_of_ne`, `KL1.ψ_x_of_ne`, `KL1.x_ψ_sub_of_eq`, `KL1.ψ_x_sub_of_eq`,
  `KL1.braid_easy`, `KL1.braid_hard`, `KL1.braid` : the relations (2.3)–(2.8) of KL I, in the
  algebraic form of KL I §2.1 (`x_{k,i} = x_k 1_i`, `δ_{k,i} = ψ_k 1_i`), hold in `R1 k Γ ν`.
* `klP Γ o` : the crossing polynomials of KL I §2.3 for an orientation `o` of the edges,
  `klQ_eq_klP` : the compatibility `Q_ij(u, v) = P_ji(u, v) P_ij(v, u)`, and
* `polyRepKL1` : **KL I, Proposition 2.3**, the polynomial representation of `R(ν)` on
  `Pol_ν`, for every orientation of `Γ`.

Positions are zero-indexed: the paper's `x_k`, `δ_k` are `x ⟨k - 1, _⟩`, `ψ (k - 1)`.
-/

namespace Categorification.KLR

open MvPolynomial KLRAlgebra

variable {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]
  {k : Type*} [CommRing k]

/-- The polynomials `Q_ij` of KL I: `Q_ij(u, v) = u + v` if `i` and `j` are joined by an
edge of `Γ`, and `1` otherwise. (The value on the diagonal is never used.) -/
noncomputable def klQ : I → I → MvPolynomial (Fin 2) k :=
  fun a b => if Γ.Adj a b then X 0 + X 1 else 1

/-- The ring `R(ν)` of KL I §2.1 for the graph `Γ`, over the commutative ring `k`
(the paper takes `k = ℤ`). -/
abbrev R1 (k : Type*) [CommRing k] {I : Type*} [DecidableEq I] (Γ : SimpleGraph I)
    [DecidableRel Γ.Adj] (ν : Multiset I) : Type _ :=
  KLRAlgebra k (klQ (k := k) Γ) ν

/-! ### Auxiliary evaluations -/

section aux

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

theorem ncEval_x_two (a b : Fin (Multiset.card ν)) (p : MvPolynomial (Fin 2) k) :
    ncEval ![(x a : KLRAlgebra k Q ν), x b] p = pol (rename ![a, b] p) := by
  have : ![(x a : KLRAlgebra k Q ν), x b] = fun c => x (![a, b] c) := by
    funext c; fin_cases c <;> rfl
  rw [this, ncEval_eq_pol]

theorem ncEval_x_three (a b c : Fin (Multiset.card ν)) (p : MvPolynomial (Fin 3) k) :
    ncEval ![(x a : KLRAlgebra k Q ν), x b, x c] p = pol (rename ![a, b, c] p) := by
  have : ![(x a : KLRAlgebra k Q ν), x b, x c] = fun d => x (![a, b, c] d) := by
    funext d; fin_cases d <;> rfl
  rw [this, ncEval_eq_pol]

omit [DecidableEq I] in
/-- `Q̄` for `Q = u + v` is `1`. -/
theorem qbar_X_add_X : qbar (X 0 + X 1 : MvPolynomial (Fin 2) k) = 1 := by
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [qbar_spec]
  simp

omit [DecidableEq I] in
/-- `Q̄` for `Q = 1` is `0`. -/
theorem qbar_one : qbar (1 : MvPolynomial (Fin 2) k) = 0 := by
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [qbar_spec]
  simp

end aux

/-! ### The relations of KL I §2.1 -/

namespace KL1

variable {Γ} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- KL I (2.3) (`eq_UUzero`), algebraic form (KL I, end of §2.1):
`δ_{k, s_k i} δ_{k, i}` is `0` if `i_k = i_{k+1}`, `1_i` if `i_k · i_{k+1} = 0`, and
`x_{k,i} + x_{k+1,i}` if `i_k · i_{k+1} = -1`. -/
theorem ψ_sq (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (ψ j * ψ j * e i : R1 k Γ ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0
      else if Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) then
        (x ⟨j, by omega⟩ + x ⟨j + 1, h⟩) * e i
      else e i := by
  rw [KLRAlgebra.ψ_sq]
  by_cases h₁ : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩
  · rw [if_pos h₁, if_pos h₁]
  · rw [if_neg h₁, if_neg h₁, ncEval_x_two]
    by_cases h₂ : Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)
    · rw [if_pos h₂]; simp [klQ, h₂]
    · rw [if_neg h₂]; simp [klQ, h₂]

theorem ψ_sq_of_eq (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) : (ψ j * ψ j * e i : R1 k Γ ν) = 0 := by
  rw [ψ_sq, if_pos hi]

theorem ψ_sq_of_not_adj (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) :
    (ψ j * ψ j * e i : R1 k Γ ν) = e i := by
  rw [ψ_sq, if_neg hi, if_neg hadj]

theorem ψ_sq_of_adj (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hadj : Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) :
    (ψ j * ψ j * e i : R1 k Γ ν) = (x ⟨j, by omega⟩ + x ⟨j + 1, h⟩) * e i := by
  rw [ψ_sq, if_neg (Γ.ne_of_adj hadj), if_pos hadj]

/-- KL I (2.4) (`eq_ijslide`), left: for `i_k ≠ i_{k+1}` a dot slides from the top left to the
bottom right of a crossing, `x_k δ_{k,i} = δ_{k,i} x_{k+1,i}`. -/
theorem x_ψ_of_ne (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩) :
    (x ⟨j, by omega⟩ * ψ j * e i : R1 k Γ ν) = ψ j * x ⟨j + 1, h⟩ * e i := by
  have := KLRAlgebra.dot_cross_left (Q := klQ (k := k) Γ) j h i
  rw [if_neg hi, sub_mul, sub_eq_zero] at this
  exact this

/-- KL I (2.4) (`eq_ijslide`), right: for `i_k ≠ i_{k+1}` a dot slides from the bottom left to
the top right of a crossing, `δ_{k,i} x_{k,i} = x_{k+1} δ_{k,i}`. -/
theorem ψ_x_of_ne (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩) :
    (ψ j * x ⟨j, by omega⟩ * e i : R1 k Γ ν) = x ⟨j + 1, h⟩ * ψ j * e i := by
  have := KLRAlgebra.dot_cross_right (Q := klQ (k := k) Γ) j h i
  rw [if_neg hi, sub_mul, sub_eq_zero] at this
  exact this

/-- KL I (2.5) (`eq_iislide1`): for `i_k = i_{k+1}`,
`x_k δ_{k,i} - δ_{k,i} x_{k+1,i} = 1_i`. -/
theorem x_ψ_sub_of_eq (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) :
    (x ⟨j, by omega⟩ * ψ j * e i - ψ j * x ⟨j + 1, h⟩ * e i : R1 k Γ ν) = e i := by
  rw [← sub_mul, KLRAlgebra.dot_cross_left, if_pos hi]

/-- KL I (2.6) (`eq_iislide2`): for `i_k = i_{k+1}`,
`δ_{k,i} x_{k,i} - x_{k+1} δ_{k,i} = 1_i`. -/
theorem ψ_x_sub_of_eq (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) :
    (ψ j * x ⟨j, by omega⟩ * e i - x ⟨j + 1, h⟩ * ψ j * e i : R1 k Γ ν) = e i := by
  rw [← sub_mul, KLRAlgebra.dot_cross_right, if_pos hi]

/-- KL I (2.7)–(2.8) combined: `(δ_k δ_{k+1} δ_k - δ_{k+1} δ_k δ_{k+1}) 1_i` is `1_i` if
`i_k = i_{k+2}` and `i_k · i_{k+1} = -1`, and `0` otherwise. -/
theorem braid (j : ℕ) (h : j + 2 < m) (i : Seq ν) :
    ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e i : R1 k Γ ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩) then e i
      else 0 := by
  rw [KLRAlgebra.braid, ncEval_x_three]
  by_cases h₁ : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩
  · by_cases hadj : Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩)
    · rw [if_pos ⟨h₁, Γ.ne_of_adj hadj⟩, if_pos ⟨h₁, hadj⟩]
      simp [klQ, hadj, qbar_X_add_X]
    · rw [if_neg (show ¬ (_ ∧ Γ.Adj _ _) from fun hc => hadj hc.2)]
      split_ifs
      · simp [klQ, hadj, qbar_one]
      · rfl
  · rw [if_neg (fun hc => h₁ hc.1), if_neg (fun hc => h₁ hc.1)]

/-- KL I (2.7) (`eq_r3_easy`): the triple crossing relation holds on `1_i` unless
`i_k = i_{k+2}` and `i_k · i_{k+1} = -1`. -/
theorem braid_easy (j : ℕ) (h : j + 2 < m) (i : Seq ν)
    (hi : ¬ (i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
      Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩))) :
    (ψ j * ψ (j + 1) * ψ j * e i : R1 k Γ ν) = ψ (j + 1) * ψ j * ψ (j + 1) * e i := by
  have := braid (k := k) (Γ := Γ) j h i
  rw [if_neg hi, sub_mul, sub_eq_zero] at this
  exact this

/-- KL I (2.8) (`eq_r3_hard`): if `i_k = i_{k+2}` and `i_k · i_{k+1} = -1`, then
`δ_k δ_{k+1} δ_k 1_i - δ_{k+1} δ_k δ_{k+1} 1_i = 1_i`. -/
theorem braid_hard (j : ℕ) (h : j + 2 < m) (i : Seq ν)
    (h₁ : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩)) :
    (ψ j * ψ (j + 1) * ψ j * e i - ψ (j + 1) * ψ j * ψ (j + 1) * e i : R1 k Γ ν) = e i := by
  rw [← sub_mul, braid, if_pos ⟨h₁, hadj⟩]

end KL1

/-! ### The polynomial representation (KL I §2.3) -/

section polyRep

variable (o : I → I → Prop) [DecidableRel o]

/-- The crossing polynomials of KL I §2.3 for an orientation `o` of the edges of `Γ`
(`o a b` meaning the edge is oriented `a → b`): `P_ab(u, v) = u + v` if `a → b`, and
`P_ab = 1` otherwise. A crossing of strands labelled `i_k → i_{k+1}` acts on `Pol_i` by
`f ↦ (x_k + x_{k+1}) s_k f`, other crossings of distinct labels by `f ↦ s_k f`. -/
noncomputable def klP : I → I → MvPolynomial (Fin 2) k :=
  fun a b => if Γ.Adj a b ∧ o a b then X 0 + X 1 else 1

variable {Γ o}

omit [DecidableEq I] in
theorem rename_klP {n : ℕ} (p q : Fin n) (a b : I) :
    rename ![p, q] (klP Γ o a b : MvPolynomial (Fin 2) k) =
      if Γ.Adj a b ∧ o a b then X p + X q else 1 := by
  unfold klP
  split_ifs <;> simp

omit [DecidableEq I] in
/-- The compatibility `Q_ab(u, v) = P_ba(u, v) P_ab(v, u)` (`a ≠ b`) for any orientation. -/
theorem klQ_eq_klP (ho : ∀ a b, Γ.Adj a b → (o a b ↔ ¬ o b a)) (a b : I) (_ : a ≠ b) :
    (klQ Γ a b : MvPolynomial (Fin 2) k) = klP Γ o b a * rename ![1, 0] (klP Γ o a b) := by
  unfold klQ klP
  by_cases hadj : Γ.Adj a b
  · have hba := hadj.symm
    by_cases hab : o a b
    · have hnba : ¬ o b a := (ho a b hadj).1 hab
      simp [hadj, hba, hab, hnba, add_comm]
    · have hba' : o b a := by
        by_contra hc; exact hab ((ho a b hadj).2 hc)
      simp [hadj, hba, hab, hba']
  · have hba : ¬ Γ.Adj b a := fun h => hadj h.symm
    simp [hadj, hba]

variable (ho : ∀ a b, Γ.Adj a b → (o a b ↔ ¬ o b a))

/-- **KL I, Proposition 2.3**: for every orientation `o` of the edges of `Γ`, the rules of
KL I §2.3 define a left action of `R(ν)` on `Pol_ν = ⊕_i k[x_1(i), …, x_m(i)]`. -/
noncomputable def polyRepKL1 (ν : Multiset I) :
    R1 k Γ ν →ₐ[k] Module.End k (PolyRep.Pol k ν) :=
  PolyRep.polyRep (P := klP Γ o) (klQ_eq_klP (Γ := Γ) ho)

@[simp] theorem polyRepKL1_e {ν : Multiset I} (i : Seq ν) :
    polyRepKL1 ho ν (e i : R1 k Γ ν) = PolyRep.opE i :=
  PolyRep.polyRep_e _ i

@[simp] theorem polyRepKL1_x {ν : Multiset I} (a : Fin (Multiset.card ν)) :
    polyRepKL1 ho ν (x a : R1 k Γ ν) = PolyRep.opX a :=
  PolyRep.polyRep_x _ a

@[simp] theorem polyRepKL1_ψ {ν : Multiset I} (j : ℕ) :
    polyRepKL1 ho ν (ψ j : R1 k Γ ν) = PolyRep.opΨ (klP Γ o) j :=
  PolyRep.polyRep_ψ _ j

end polyRep

end Categorification.KLR
