/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL1Basis
import Categorification.KLR.Grading
import Categorification.QuantumGroup.Cartan

/-!
# The rings `R(ν)` of Khovanov–Lauda II

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, "Algebras `R(ν)`" (TeX lines ~323–440, labels `new_eq_UUzero`,
`new_eq_ijslide`, `new_eq_iislide1`, `eq_iislide2`, `new_eq_r3_easy`, `eq_r3_hard`).

For a Cartan datum `(I, ·)` (`QuantumGroup.CartanDatum`: `i · i ∈ {2, 4, …}` and
`d_ij = -2 (i · j) / (i · i) ∈ ℕ` for `i ≠ j`) KL II defines `R(ν)` by braid-like diagrams
modulo the local relations

* `ψ² 1_{ij} = 0` if `i = j`, `= 1_{ij}` if `i · j = 0`, and `= (x_1^{d_ij} + x_2^{d_ji}) 1_{ij}`
  if `i · j ≠ 0` (`new_eq_UUzero`);
* dots slide through crossings of distinct labels (`new_eq_ijslide`) and satisfy the
  nilHecke relations on equal labels (`new_eq_iislide1`, `eq_iislide2`);
* the triple-crossing relation `(ψ_1 ψ_2 ψ_1 - ψ_2 ψ_1 ψ_2) 1_{iji} = ∑_{a=0}^{d_ij - 1}
  x_1^a x_3^{d_ij - 1 - a} 1_{iji}` if `i · j ≠ 0`, and `0` for all other sequences
  (`new_eq_r3_easy`, `eq_r3_hard`),

graded by `deg x_{a,i} = i_a · i_a` and `deg ψ_{k,i} = - i_k · i_{k+1}`. This is the KLR
algebra `KLRAlgebra k Q ν` for

  `Q i j (u, v) = u^{d_ij} + v^{d_ji}` if `i · j ≠ 0`, and `Q i j = 1` if `i · j = 0`

(`klQ2`); KL II works over `ℤ` or a field, and we allow any commutative ring `k`.

## Main definitions and results

* `CartanDatum.dij`, `dij_mul` : `d_ij ∈ ℕ` with `d_ij (i · i) = -2 (i · j)` (`i ≠ j`).
* `klQ2 C`, `R2 k C ν` : the KL II data and rings.
* `KL2.ψ_sq_of_eq`, `KL2.ψ_sq_of_dot_eq_zero`, `KL2.ψ_sq_of_dot_ne_zero`, `KL2.x_ψ_of_ne`,
  `KL2.ψ_x_of_ne`, `KL2.x_ψ_sub_of_eq`, `KL2.ψ_x_sub_of_eq`, `KL2.braid_easy`,
  `KL2.braid_hard` : the relations of KL II §3 hold in `R2 k C ν`.
* `klGradingDatum2 k C` : the KL II grading (`deg x = i · i`, `deg ψ = - i · j`).
* `klP2 C o`, `klQ2_eq_klP2` : the crossing polynomials of the KL II polynomial representation
  for an orientation `o` (a crossing `i_k → i_{k+1}` acts by
  `f ↦ (x_k^{d_{i_{k+1} i_k}} + x_{k+1}^{d_{i_k i_{k+1}}}) s_k f`), and the factorisation
  `Q_ij(u, v) = P_ji(u, v) P_ij(v, u)`; `polyRepKL2` is the polynomial representation.
* `KL2.cornerBasis`, `KL2.basis`, `KL2.polyRepKL2_injective` : the basis theorem and
  faithfulness of the polynomial representation for an arbitrary Cartan datum (KL II §3:
  "Proposition 2.3 … and Corollary 2.6 in [KL] hold for an arbitrary Cartan datum").

Positions are zero-indexed: the paper's `x_k`, `δ_k` are `x ⟨k - 1, _⟩`, `ψ (k - 1)`.
-/

namespace Categorification

namespace QuantumGroup.CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- `d_ij = -2 (i · j) / (i · i)`, a natural number for `i ≠ j` (KL II §1). -/
def dij (i j : I) : ℕ := ((-2 * C.dot i j) / C.dot i i).toNat

theorem dij_mul {i j : I} (h : i ≠ j) : (C.dij i j : ℤ) * C.dot i i = -2 * C.dot i j := by
  have hpos := C.dot_self_pos i
  have hdvd : C.dot i i ∣ -2 * C.dot i j := by
    rw [neg_mul]; exact (C.dvd_two_mul i j).neg_right
  have hnn : 0 ≤ (-2 * C.dot i j) / C.dot i i :=
    Int.ediv_nonneg (by have := C.dot_nonpos i j h; omega) hpos.le
  rw [dij, Int.toNat_of_nonneg hnn, Int.ediv_mul_cancel hdvd]

theorem dij_eq_zero_iff {i j : I} (h : i ≠ j) : C.dij i j = 0 ↔ C.dot i j = 0 := by
  have := C.dij_mul h
  have hpos := C.dot_self_pos i
  constructor
  · intro h0; rw [h0] at this; push_cast at this; omega
  · intro h0
    rw [h0, mul_zero] at this
    have : (C.dij i j : ℤ) = 0 := by
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · omega
    exact_mod_cast this

theorem dij_pos {i j : I} (h : i ≠ j) (hd : C.dot i j ≠ 0) : 0 < C.dij i j :=
  Nat.pos_of_ne_zero fun h0 => hd ((C.dij_eq_zero_iff h).1 h0)

end QuantumGroup.CartanDatum

namespace KLR

open MvPolynomial KLRAlgebra QuantumGroup

variable {k : Type*} [CommRing k] {I : Type*} (C : CartanDatum I)

variable (k) in
/-- The polynomials `Q_ij` of KL II: `Q_ij(u, v) = u^{d_ij} + v^{d_ji}` if `i · j ≠ 0`, and
`Q_ij = 1` if `i · j = 0`. (The value on the diagonal is never used.) -/
noncomputable def klQ2 : I → I → MvPolynomial (Fin 2) k :=
  fun a b => if C.dot a b = 0 then 1 else X 0 ^ C.dij a b + X 1 ^ C.dij b a

/-- The ring `R(ν)` of KL II §3 for the Cartan datum `C`, over the commutative ring `k`. -/
abbrev R2 (k : Type*) [CommRing k] {I : Type*} [DecidableEq I] (C : CartanDatum I)
    (ν : Multiset I) : Type _ :=
  KLRAlgebra k (klQ2 k C) ν

/-- `Q̄` for `Q = u^d + v^{d'}` is `∑_{t < d} a^t c^{d - 1 - t}`. -/
theorem qbar_X_pow_add_X_pow (d d' : ℕ) :
    qbar (X 0 ^ d + X 1 ^ d' : MvPolynomial (Fin 2) k) =
      ∑ t ∈ Finset.range d, X 0 ^ t * X 2 ^ (d - 1 - t) := by
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [qbar_spec]
  simp only [map_add, map_pow, rename_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have := geom_sum₂_mul (X 0 : MvPolynomial (Fin 3) k) (X 2) d
  rw [mul_comm] at this
  rw [this]; ring

namespace KL2

variable [DecidableEq I] {C} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ### The relations of KL II §3 -/

/-- KL II `new_eq_UUzero`, case `i = j`: `ψ² 1_{ii} = 0`. -/
theorem ψ_sq_of_eq (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) : (ψ j * ψ j * e i : R2 k C ν) = 0 := by
  rw [KLRAlgebra.ψ_sq, if_pos hi]

/-- KL II `new_eq_UUzero`, case `i · j = 0`: `ψ² 1_{ij} = 1_{ij}`. -/
theorem ψ_sq_of_dot_eq_zero (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩)
    (hd : C.dot (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) = 0) :
    (ψ j * ψ j * e i : R2 k C ν) = e i := by
  rw [KLRAlgebra.ψ_sq, if_neg hi, ncEval_x_two, klQ2, if_pos hd, map_one, map_one, one_mul]

/-- KL II `new_eq_UUzero`, case `i · j ≠ 0`: `ψ² 1_{ij} = (x_1^{d_ij} + x_2^{d_ji}) 1_{ij}`. -/
theorem ψ_sq_of_dot_ne_zero (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩)
    (hd : C.dot (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) ≠ 0) :
    (ψ j * ψ j * e i : R2 k C ν) =
      (x ⟨j, by omega⟩ ^ C.dij (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) +
        x ⟨j + 1, h⟩ ^ C.dij (i.lbl ⟨j + 1, h⟩) (i.lbl ⟨j, by omega⟩)) * e i := by
  rw [KLRAlgebra.ψ_sq, if_neg hi, ncEval_x_two, klQ2, if_neg hd]
  simp

/-- KL II `new_eq_ijslide`, left: `x_k δ_{k,i} = δ_{k,i} x_{k+1}` for `i_k ≠ i_{k+1}`. -/
theorem x_ψ_of_ne (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩) :
    (x ⟨j, by omega⟩ * ψ j * e i : R2 k C ν) = ψ j * x ⟨j + 1, h⟩ * e i := by
  have := KLRAlgebra.dot_cross_left (Q := klQ2 k C) j h i
  rw [if_neg hi, sub_mul, sub_eq_zero] at this
  exact this

/-- KL II `new_eq_ijslide`, right: `δ_{k,i} x_k = x_{k+1} δ_{k,i}` for `i_k ≠ i_{k+1}`. -/
theorem ψ_x_of_ne (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩) :
    (ψ j * x ⟨j, by omega⟩ * e i : R2 k C ν) = x ⟨j + 1, h⟩ * ψ j * e i := by
  have := KLRAlgebra.dot_cross_right (Q := klQ2 k C) j h i
  rw [if_neg hi, sub_mul, sub_eq_zero] at this
  exact this

/-- KL II `new_eq_iislide1`: `x_k δ_{k,i} - δ_{k,i} x_{k+1} = 1_i` for `i_k = i_{k+1}`. -/
theorem x_ψ_sub_of_eq (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) :
    (x ⟨j, by omega⟩ * ψ j * e i - ψ j * x ⟨j + 1, h⟩ * e i : R2 k C ν) = e i := by
  rw [← sub_mul, KLRAlgebra.dot_cross_left, if_pos hi]

/-- KL II `eq_iislide2`: `δ_{k,i} x_k - x_{k+1} δ_{k,i} = 1_i` for `i_k = i_{k+1}`. -/
theorem ψ_x_sub_of_eq (j : ℕ) (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) :
    (ψ j * x ⟨j, by omega⟩ * e i - x ⟨j + 1, h⟩ * ψ j * e i : R2 k C ν) = e i := by
  rw [← sub_mul, KLRAlgebra.dot_cross_right, if_pos hi]

/-- KL II `new_eq_r3_easy`: the triple-crossing relation holds on `1_i` unless `i_k = i_{k+2}`,
`i_k ≠ i_{k+1}` and `i_k · i_{k+1} ≠ 0`. -/
theorem braid_easy (j : ℕ) (h : j + 2 < m) (i : Seq ν)
    (hi : ¬ (i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
      i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ ∧
      C.dot (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩) ≠ 0)) :
    (ψ j * ψ (j + 1) * ψ j * e i : R2 k C ν) = ψ (j + 1) * ψ j * ψ (j + 1) * e i := by
  have := KLRAlgebra.braid (Q := klQ2 k C) j h i
  rw [← sub_eq_zero, ← sub_mul, this]
  split_ifs with h1
  · rw [ncEval_x_three, klQ2, if_pos, qbar_one, map_zero, map_zero, zero_mul]
    by_contra hd
    exact hi ⟨h1.1, h1.2, hd⟩
  · rfl

/-- KL II `eq_r3_hard`: if `i_k = i_{k+2} ≠ i_{k+1}` and `i_k · i_{k+1} ≠ 0`, then
`(δ_k δ_{k+1} δ_k - δ_{k+1} δ_k δ_{k+1}) 1_i = ∑_{a=0}^{d-1} x_k^a x_{k+2}^{d-1-a} 1_i` with
`d = d_{i_k i_{k+1}}`. -/
theorem braid_hard (j : ℕ) (h : j + 2 < m) (i : Seq ν)
    (h₁ : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩)
    (h₂ : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩)
    (hd : C.dot (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩) ≠ 0) :
    (ψ j * ψ (j + 1) * ψ j * e i - ψ (j + 1) * ψ j * ψ (j + 1) * e i : R2 k C ν) =
      (∑ t ∈ Finset.range (C.dij (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩)),
        x ⟨j, by omega⟩ ^ t * x ⟨j + 2, h⟩ ^
          (C.dij (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩) - 1 - t)) * e i := by
  rw [← sub_mul, KLRAlgebra.braid, if_pos ⟨h₁, h₂⟩, ncEval_x_three, klQ2, if_neg hd,
    qbar_X_pow_add_X_pow]
  simp [map_sum]

end KL2

/-! ### The grading -/

variable (k) in
/-- The KL II grading: `deg x_{a,i} = i_a · i_a` and `deg ψ_{k,i} = - i_k · i_{k+1}`. -/
noncomputable def klGradingDatum2 : GradingDatum (klQ2 k C) where
  degX a := C.dot a a
  degΨ a b := -C.dot a b
  degΨ_self _ := rfl
  isWeightedHomogeneous a b hab := by
    unfold klQ2
    split_ifs with hd
    · have : -C.dot a b + -C.dot b a = 0 := by rw [C.symm b a, hd]; ring
      rw [this]; exact isWeightedHomogeneous_one k _
    · refine IsWeightedHomogeneous.add ?_ ?_
      · convert (isWeightedHomogeneous_X k ![C.dot a a, C.dot b b] 0).pow (C.dij a b) using 1
        simp only [Matrix.cons_val_zero, nsmul_eq_mul]
        have := C.dij_mul hab
        rw [C.symm b a]; linarith
      · convert (isWeightedHomogeneous_X k ![C.dot a a, C.dot b b] 1).pow (C.dij b a) using 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, nsmul_eq_mul]
        have := C.dij_mul (Ne.symm hab)
        rw [C.symm b a] at this ⊢; linarith

/-! ### The polynomial representation (KL II §3) -/

section polyRep

variable (o : I → I → Prop) [DecidableRel o]

/-- The crossing polynomials of the KL II polynomial representation for an orientation `o` of
the edges (`o a b`: the edge is oriented `a → b`): `P_ab(u, v) = u^{d_ba} + v^{d_ab}` if
`a · b ≠ 0` and `a → b`, and `P_ab = 1` otherwise. A crossing of strands labelled
`i_k → i_{k+1}` acts on `Pol_i` by `f ↦ (x_k^{d_{i_{k+1} i_k}} + x_{k+1}^{d_{i_k i_{k+1}}}) s_k f`
(KL II §3), other crossings of distinct labels by `f ↦ s_k f`. -/
noncomputable def klP2 : I → I → MvPolynomial (Fin 2) k :=
  fun a b => if C.dot a b ≠ 0 ∧ o a b then X 0 ^ C.dij b a + X 1 ^ C.dij a b else 1

variable {C o}

/-- The compatibility `Q_ab(u, v) = P_ba(u, v) P_ab(v, u)` (`a ≠ b`) for any orientation. -/
theorem klQ2_eq_klP2 (ho : ∀ a b, a ≠ b → C.dot a b ≠ 0 → (o a b ↔ ¬ o b a)) (a b : I)
    (hab : a ≠ b) :
    (klQ2 k C a b : MvPolynomial (Fin 2) k) = klP2 C o b a * rename ![1, 0] (klP2 C o a b) := by
  unfold klQ2 klP2
  by_cases hd : C.dot a b = 0
  · have hd' : C.dot b a = 0 := by rw [C.symm]; exact hd
    simp [hd, hd']
  · have hd' : C.dot b a ≠ 0 := by rw [C.symm]; exact hd
    by_cases hab' : o a b
    · have hba : ¬ o b a := (ho a b hab hd).1 hab'
      simp [hd, hd', hab', hba, add_comm]
    · have hba : o b a := by
        by_contra hc; exact hab' ((ho a b hab hd).2 hc)
      simp [hd, hd', hab', hba]

theorem klP2_ne_zero [Nontrivial k] (a b : I) (hab : a ≠ b) :
    (klP2 C o a b : MvPolynomial (Fin 2) k) ≠ 0 := by
  unfold klP2
  split_ifs with h
  · intro h0
    have hpos := C.dij_pos (Ne.symm hab) (by rw [C.symm]; exact h.1)
    have := congrArg (MvPolynomial.coeff (Finsupp.single 0 (C.dij b a))) h0
    rw [coeff_add, coeff_X_pow, coeff_X_pow, if_pos rfl, if_neg, coeff_zero, add_zero] at this
    · exact one_ne_zero this
    · rw [Finsupp.single_eq_single_iff]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact absurd h1 (by decide)
      · omega
  · exact one_ne_zero

variable [DecidableEq I] (ho : ∀ a b, a ≠ b → C.dot a b ≠ 0 → (o a b ↔ ¬ o b a))

/-- **KL II §3** (KL I, Proposition 2.3, for an arbitrary Cartan datum): for every orientation
`o`, the rules of KL II §3 define a left action of `R(ν)` on `Pol_ν`. -/
noncomputable def polyRepKL2 (ν : Multiset I) :
    R2 k C ν →ₐ[k] Module.End k (PolyRep.Pol k ν) :=
  PolyRep.polyRep (P := klP2 C o) (klQ2_eq_klP2 ho)

@[simp] theorem polyRepKL2_e {ν : Multiset I} (i : Seq ν) :
    polyRepKL2 ho ν (e i : R2 k C ν) = PolyRep.opE i :=
  PolyRep.polyRep_e _ i

@[simp] theorem polyRepKL2_x {ν : Multiset I} (a : Fin (Multiset.card ν)) :
    polyRepKL2 ho ν (x a : R2 k C ν) = PolyRep.opX a :=
  PolyRep.polyRep_x _ a

@[simp] theorem polyRepKL2_ψ {ν : Multiset I} (j : ℕ) :
    polyRepKL2 ho ν (ψ j : R2 k C ν) = PolyRep.opΨ (klP2 C o) j :=
  PolyRep.polyRep_ψ _ j

end polyRep

/-! ### The basis theorem (KL II §3) -/

namespace KL2

open Equiv TypeA

variable {C} [DecidableEq I] [IsDomain k] {ν : Multiset I}

omit [DecidableEq I] in
theorem stdOrient_spec : ∀ a b : I, a ≠ b → C.dot a b ≠ 0 →
    (KL1.stdOrient a b ↔ ¬ KL1.stdOrient b a) := by
  intro a b hne _
  constructor
  · intro h h'; exact asymm (r := WellOrderingRel) h h'
  · intro h
    rcases (WellOrderingRel.isWellOrder (α := I)).trichotomous a b with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hne
    · exact absurd h1 h

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

/-- **KL II §3** (KL I, Theorem 2.5, for an arbitrary Cartan datum): for any choice `ρ` of
minimal presentations of permutations, `_jR(ν)_i` is a free `k`-module with basis
`ψ_{ρ w} x^u e_i` (`w • i = j`, `u ∈ ℕ^m`), over any integral domain `k`. -/
noncomputable def cornerBasis (j i : Seq ν) :
    Basis (CornerIdx j i) k (corner (Q := klQ2 k C) j i) :=
  KLRAlgebra.cornerBasis (klQ2_eq_klP2 (o := KL1.stdOrient) stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) ρ hρ j i

theorem cornerBasis_apply (j i : Seq ν) (b : CornerIdx j i) :
    (KL2.cornerBasis (k := k) (C := C) ρ hρ j i b : R2 k C ν) =
      ψw (ρ b.1.1) * pol (monomial b.2 1) * e i :=
  KLRAlgebra.cornerBasis_apply _ _ ρ hρ j i b

/-- **KL II §3** (KL I, Theorem 2.5): `R(ν)` has basis `ψ_{ρ w} x^u e_i` (all `i, w, u`). -/
noncomputable def basis :
    Basis (Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) k
      (R2 k C ν) :=
  KLRAlgebra.basis (klQ2_eq_klP2 (o := KL1.stdOrient) stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) ρ hρ

theorem basis_apply (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    (KL2.basis (k := k) (C := C) ρ hρ b : R2 k C ν) =
      ψw (ρ b.2.1) * pol (monomial b.2.2 1) * e b.1 :=
  KLRAlgebra.basis_apply _ _ ρ hρ b

/-- **KL II §3** (KL I, Corollary 2.6, for an arbitrary Cartan datum): for every orientation,
`Pol_ν` is a faithful `R(ν)`-module. -/
theorem polyRepKL2_injective (o : I → I → Prop) [DecidableRel o]
    (ho : ∀ a b, a ≠ b → C.dot a b ≠ 0 → (o a b ↔ ¬ o b a)) :
    Function.Injective (polyRepKL2 (k := k) ho ν) :=
  polyRep_injective _ (fun a b hab => klP2_ne_zero a b hab)

end KL2

end KLR

end Categorification
