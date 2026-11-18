/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Symmetries
import Categorification.KLR.BaseChange

/-!
# Rescaling the crossings of a KLR algebra

Let `s : I → I → kˣ` with `s a a = 1`, and let `Q, Q'` be KLR data with
`Q_{ab} = s_{ab} s_{ba} Q'_{ab}` for `a ≠ b`. Then `R(ν)` for `Q` and `R(ν)` for `Q'` are
isomorphic: the isomorphism fixes the idempotents and dots and multiplies the crossing
`ψ_j e_i` by `s_{i_j i_{j+1}}`. Both sides of the braid relation pick up the same scalar
`s_{ab} s_{ac} s_{bc}`, and the quadratic relation picks up `s_{ab} s_{ba}`.

This is the comparison used for the normalized crossings of Cautis–Lauda,
*Categorical quantum groups and their categorifications*, arXiv:1111.1431v3, §2.2: the
downward KLR relations there use the polynomial `(t_{ij} t_{ji})⁻¹ Q_{ij}`, and the
rescaling by `t` identifies the resulting KLR algebra with the one for `Q`. It is used for
the corrected form of Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, Lemma 4.28 (v3, Lemma 4.29); see `DoubleDownScalars`.

## Main definitions and results

* `KLRAlgebra.crossScale s j i`: the scalar `s_{i_j i_{j+1}}` of the crossing `ψ_j e_i`.
* `KLRAlgebra.rescale hs hQ : KLRAlgebra k Q ν ≃ₐ[k] KLRAlgebra k Q' ν`, with `rescale_e`,
  `rescale_x` and `rescale_ψ_mul_e`.
-/

namespace Categorification.KLR

open MvPolynomial Equiv TypeA

variable {I : Type*} {k : Type*} [CommRing k]

theorem ncEval_C_mul' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) (c : k)
    (p : MvPolynomial (Fin n) k) : ncEval y (C c * p) = c • ncEval y p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s d =>
    rw [C_mul_monomial, ncEval_monomial, ncEval_monomial, map_mul, Algebra.smul_def, mul_assoc]
  | add p q hp hq => rw [mul_add, ncEval_add, hp, hq, ncEval_add, smul_add]

theorem qbar_C_mul' (c : k) (P : MvPolynomial (Fin 2) k) :
    qbar (C c * P) = C c * qbar P := by
  induction P using MvPolynomial.induction_on' with
  | monomial s d =>
    rw [C_mul_monomial, qbar_monomial, qbar_monomial, map_mul]
    ring
  | add p q hp hq => rw [mul_add, qbar_add, hp, hq, qbar_add, mul_add]

namespace KLRAlgebra

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ### The crossing scalars -/

/-- The scalar `s_{i_j i_{j+1}}` attached to the crossing `ψ_j e_i` (and `1` if `j` is out of
range). -/
def crossScale (s : I → I → kˣ) (j : ℕ) (i : Seq ν) : k :=
  if h : j + 1 < m then (s (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, h⟩) : k) else 1

theorem crossScale_of_lt (s : I → I → kˣ) {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    crossScale s j i = (s (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, h⟩) : k) := dite_eq_left h

theorem crossScale_sadj_of_far (s : I → I → kˣ) {j l : ℕ} (hjl : j + 1 < l ∨ l + 1 < j)
    (i : Seq ν) : crossScale s j (sadj m l • i) = crossScale s j i := by
  by_cases h : j + 1 < m
  · rw [crossScale_of_lt s h, crossScale_of_lt s h, sadj_smul_apply, sadj_smul_apply]
    by_cases hl : l + 1 < m
    · have h1 : i.1 (sadj m l ⟨j, by omega⟩) = i.1 ⟨j, by omega⟩ :=
        lbl_congr i (by rw [sadj_apply_val hl]; simp only []; split_ifs <;> omega)
      have h2 : i.1 (sadj m l ⟨j + 1, h⟩) = i.1 ⟨j + 1, h⟩ :=
        lbl_congr i (by rw [sadj_apply_val hl]; simp only []; split_ifs <;> omega)
      rw [h1, h2]
    · simp [sadj, hl]
  · simp [crossScale, h]

theorem crossScale_mul_eq_one {t s : I → I → kˣ} (hts : ∀ a b, t a b * s a b = 1) (j : ℕ)
    (i : Seq ν) : crossScale t j i * crossScale s j i = 1 := by
  unfold crossScale
  split_ifs
  · rw [← Units.val_mul, hts, Units.val_one]
  · rw [mul_one]

variable [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}

/-- The diagonal element `∑_i s_{i_j i_{j+1}} e_i`. -/
noncomputable def scaleE (Q : I → I → MvPolynomial (Fin 2) k) (s : I → I → kˣ) (j : ℕ) :
    KLRAlgebra k Q ν :=
  ∑ i, crossScale s j i • e i

theorem scaleE_mul_e (s : I → I → kˣ) (j : ℕ) (i : Seq ν) :
    (scaleE Q s j * e i : KLRAlgebra k Q ν) = crossScale s j i • e i := by
  simp only [scaleE, Finset.sum_mul, smul_mul_assoc, e_mul_e, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem e_mul_scaleE (s : I → I → kˣ) (j : ℕ) (i : Seq ν) :
    (e i * scaleE Q s j : KLRAlgebra k Q ν) = crossScale s j i • e i := by
  simp only [scaleE, Finset.mul_sum, mul_smul_comm, e_mul_e, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem x_mul_scaleE (s : I → I → kˣ) (a : Fin m) (j : ℕ) :
    (x a * scaleE Q s j : KLRAlgebra k Q ν) = scaleE Q s j * x a := by
  simp only [scaleE, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, x_mul_e]

theorem scaleE_mul_eq_one {t s : I → I → kˣ} (hts : ∀ a b, t a b * s a b = 1) (j : ℕ) :
    (scaleE Q t j * scaleE Q s j : KLRAlgebra k Q ν) = 1 := by
  refine ext_e fun i => ?_
  rw [mul_assoc, scaleE_mul_e, mul_smul_comm, scaleE_mul_e, smul_smul,
    mul_comm (crossScale s j i), crossScale_mul_eq_one hts, one_smul, one_mul]

/-- The rescaled crossing `ψ_j ∑_i s_{i_j i_{j+1}} e_i`. -/
noncomputable def rescaleψ (Q : I → I → MvPolynomial (Fin 2) k) (s : I → I → kˣ) (j : ℕ) :
    KLRAlgebra k Q ν :=
  ψ j * scaleE Q s j

theorem rescaleψ_mul_e (s : I → I → kˣ) (j : ℕ) (i : Seq ν) :
    (rescaleψ Q s j * e i : KLRAlgebra k Q ν) = crossScale s j i • (ψ j * e i) := by
  rw [rescaleψ, mul_assoc, scaleE_mul_e, mul_smul_comm]

theorem rescaleψ_mul_of_e (s : I → I → kˣ) (j : ℕ) {z : KLRAlgebra k Q ν} {i : Seq ν}
    (hz : e i * z = z) : rescaleψ Q s j * z = crossScale s j i • (ψ j * z) := by
  rw [← hz, ← mul_assoc, rescaleψ_mul_e, smul_mul_assoc, mul_assoc]

theorem e_sadj_mul_ψ_mul {j : ℕ} {z : KLRAlgebra k Q ν} {i : Seq ν} (hz : e i * z = z) :
    e (sadj m j • i) * (ψ j * z) = ψ j * z := by
  rw [← hz, ← mul_assoc, ← mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc, mul_assoc,
    ← mul_assoc (e i), e_mul_self]

/-! ### The KLR relations for the rescaled crossings -/

section Relations

variable {Q' : I → I → MvPolynomial (Fin 2) k} (s : I → I → kˣ)

theorem rescale_cross_idem (j : ℕ) (i : Seq ν) :
    (rescaleψ Q' s j * e i : KLRAlgebra k Q' ν) = e (sadj m j • i) * rescaleψ Q' s j := by
  rw [rescaleψ_mul_e, rescaleψ, ← mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc, e_mul_scaleE,
    mul_smul_comm]

theorem rescale_cross_cross (j l : ℕ) (hjl : j + 1 < l) :
    (rescaleψ Q' s j * rescaleψ Q' s l : KLRAlgebra k Q' ν) =
      rescaleψ Q' s l * rescaleψ Q' s j := by
  refine ext_e fun i => ?_
  rw [mul_assoc, mul_assoc, rescaleψ_mul_e, rescaleψ_mul_e, mul_smul_comm, mul_smul_comm,
    rescaleψ_mul_of_e s j (i := sadj m l • i) (e_sadj_mul_ψ_mul (e_mul_self _)),
    rescaleψ_mul_of_e s l (i := sadj m j • i) (e_sadj_mul_ψ_mul (e_mul_self _)),
    crossScale_sadj_of_far s (Or.inl hjl), crossScale_sadj_of_far s (Or.inr hjl), smul_smul,
    smul_smul, mul_comm (crossScale s j i), ← mul_assoc, ← mul_assoc, ψ_mul_ψ j l hjl]

theorem rescale_dot_cross (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (x a * rescaleψ Q' s j : KLRAlgebra k Q' ν) = rescaleψ Q' s j * x a := by
  rw [rescaleψ, ← mul_assoc, x_mul_ψ a j h₁ h₂, mul_assoc, x_mul_scaleE, mul_assoc]

theorem x_mul_rescaleψ_mul_e (a : Fin m) (j : ℕ) (i : Seq ν) :
    (x a * rescaleψ Q' s j * e i : KLRAlgebra k Q' ν) = crossScale s j i • (x a * ψ j * e i) := by
  rw [mul_assoc, rescaleψ_mul_e, mul_smul_comm, ← mul_assoc]

theorem rescaleψ_mul_x_mul_e (a : Fin m) (j : ℕ) (i : Seq ν) :
    (rescaleψ Q' s j * x a * e i : KLRAlgebra k Q' ν) = crossScale s j i • (ψ j * x a * e i) := by
  rw [mul_assoc, x_mul_e, ← mul_assoc, rescaleψ_mul_e, smul_mul_assoc, mul_assoc, ← x_mul_e,
    ← mul_assoc]

omit [DecidableEq I] in
theorem crossScale_of_lbl_eq (hs : ∀ a, s a a = 1) {j : ℕ} (h : j + 1 < m) (i : Seq ν)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) : crossScale s j i = 1 := by
  rw [crossScale_of_lt s h]
  change (s (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) : k) = 1
  rw [hi, hs, Units.val_one]

theorem rescale_dot_cross_left (hs : ∀ a, s a a = 1) (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    ((x ⟨j, by omega⟩ * rescaleψ Q' s j - rescaleψ Q' s j * x ⟨j + 1, h⟩) * e i
      : KLRAlgebra k Q' ν) = if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i else 0 := by
  have key : ((x ⟨j, by omega⟩ * rescaleψ Q' s j - rescaleψ Q' s j * x ⟨j + 1, h⟩) * e i
      : KLRAlgebra k Q' ν) = crossScale s j i •
        ((x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) * e i) := by
    rw [sub_mul, sub_mul, x_mul_rescaleψ_mul_e, rescaleψ_mul_x_mul_e, smul_sub]
  rw [key, dot_cross_left j h i]
  split_ifs with hi
  · rw [crossScale_of_lbl_eq s hs h i hi, one_smul]
  · rw [smul_zero]

theorem rescale_dot_cross_right (hs : ∀ a, s a a = 1) (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    ((rescaleψ Q' s j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * rescaleψ Q' s j) * e i
      : KLRAlgebra k Q' ν) = if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i else 0 := by
  have key : ((rescaleψ Q' s j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * rescaleψ Q' s j) * e i
      : KLRAlgebra k Q' ν) = crossScale s j i •
        ((ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) * e i) := by
    rw [sub_mul, sub_mul, x_mul_rescaleψ_mul_e, rescaleψ_mul_x_mul_e, smul_sub]
  rw [key, dot_cross_right j h i]
  split_ifs with hi
  · rw [crossScale_of_lbl_eq s hs h i hi, one_smul]
  · rw [smul_zero]

theorem rescale_cross_sq (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)
    (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (rescaleψ Q' s j * rescaleψ Q' s j * e i : KLRAlgebra k Q' ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
        ncEval ![x ⟨j, by omega⟩, x ⟨j + 1, h⟩]
          (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) * e i := by
  rw [mul_assoc, rescaleψ_mul_e, mul_smul_comm,
    rescaleψ_mul_of_e s j (i := sadj m j • i) (e_sadj_mul_ψ_mul (e_mul_self _)), smul_smul,
    ← mul_assoc, ψ_sq j h i]
  split_ifs with hi
  · rw [smul_zero]
  · rw [hQ _ _ hi, ncEval_C_mul', smul_mul_assoc, crossScale_of_lt s h,
      crossScale_of_lt s h, sadj_smul_apply_of h _ _ ⟨j + 1, h⟩,
      sadj_smul_apply_of h _ _ ⟨j, by omega⟩, Units.val_mul]

theorem rescale_braid (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)
    (j : ℕ) (h : j + 2 < m) (i : Seq ν) :
    ((rescaleψ Q' s j * rescaleψ Q' s (j + 1) * rescaleψ Q' s j
        - rescaleψ Q' s (j + 1) * rescaleψ Q' s j * rescaleψ Q' s (j + 1)) * e i
          : KLRAlgebra k Q' ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
        ncEval ![x ⟨j, by omega⟩, x ⟨j + 1, by omega⟩, x ⟨j + 2, h⟩]
          (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩))) * e i
      else 0 := by
  have h0 : j + 1 < m := by omega
  have h1 : j + 1 + 1 < m := by omega
  set a := i.1 ⟨j, by omega⟩ with ha
  set b := i.1 ⟨j + 1, h0⟩ with hb
  set c := i.1 ⟨j + 2, h⟩ with hc
  have s1 : crossScale s j i = (s a b : k) := crossScale_of_lt s h0 i
  have s2 : crossScale s (j + 1) (sadj m j • i) = (s a c : k) := by
    rw [crossScale_of_lt s h1, sadj_smul_apply_of h0 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 2, h⟩]
  have s3 : crossScale s j (sadj m (j + 1) • sadj m j • i) = (s b c : k) := by
    rw [crossScale_of_lt s h0, sadj_smul_apply_of h1 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h1 _ _ ⟨j + 2, h⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 1, h0⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 2, h⟩]
  have s4 : crossScale s (j + 1) i = (s b c : k) := crossScale_of_lt s h1 i
  have s5 : crossScale s j (sadj m (j + 1) • i) = (s a c : k) := by
    rw [crossScale_of_lt s h0, sadj_smul_apply_of h1 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h1 _ _ ⟨j + 2, h⟩]
  have s6 : crossScale s (j + 1) (sadj m j • sadj m (j + 1) • i) = (s a b : k) := by
    rw [crossScale_of_lt s h1, sadj_smul_apply_of h0 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h0 _ _ ⟨j + 2, h⟩,
      sadj_smul_apply_of h1 _ _ ⟨j, by omega⟩,
      sadj_smul_apply_of h1 _ _ ⟨j + 1, h0⟩]
  have key : ((rescaleψ Q' s j * rescaleψ Q' s (j + 1) * rescaleψ Q' s j
        - rescaleψ Q' s (j + 1) * rescaleψ Q' s j * rescaleψ Q' s (j + 1)) * e i
          : KLRAlgebra k Q' ν) = ((s a b : k) * (s a c : k) * (s b c : k)) •
        ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e i) := by
    rw [sub_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
      rescaleψ_mul_e, mul_smul_comm, mul_smul_comm,
      rescaleψ_mul_of_e s (j + 1) (i := sadj m j • i) (e_sadj_mul_ψ_mul (e_mul_self _)),
      mul_smul_comm,
      rescaleψ_mul_of_e s j (i := sadj m (j + 1) • sadj m j • i)
        (e_sadj_mul_ψ_mul (e_sadj_mul_ψ_mul (e_mul_self _))),
      rescaleψ_mul_e, mul_smul_comm, mul_smul_comm,
      rescaleψ_mul_of_e s j (i := sadj m (j + 1) • i) (e_sadj_mul_ψ_mul (e_mul_self _)),
      mul_smul_comm,
      rescaleψ_mul_of_e s (j + 1) (i := sadj m j • sadj m (j + 1) • i)
        (e_sadj_mul_ψ_mul (e_sadj_mul_ψ_mul (e_mul_self _))),
      s1, s2, s3, s4, s5, s6, smul_smul, smul_smul, smul_smul, smul_smul, sub_mul, smul_sub,
      ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    congr 2
    ring
  rw [key, braid j h i]
  split_ifs with hi
  · obtain ⟨hac, hab⟩ := hi
    simp only [Seq.lbl, ← ha, ← hb, ← hc] at hac hab ⊢
    have hcs : (s a b : k) * (s a c : k) * (s b c : k) = ((s a b * s b a : kˣ) : k) := by
      rw [← hac, hs, Units.val_one, mul_one, Units.val_mul]
    rw [hcs, hQ a b hab, qbar_C_mul', ncEval_C_mul', smul_mul_assoc]
  · rw [smul_zero]

end Relations

/-! ### The isomorphism -/

section Hom

variable {Q' : I → I → MvPolynomial (Fin 2) k} (s : I → I → kˣ)

variable (Q' ν) in
/-- The rescaling on generators. -/
noncomputable def rescaleGen : Gen ν → KLRAlgebra k Q' ν
  | .idem i => e i
  | .dot a => x a
  | .cross j => rescaleψ Q' s j

variable (Q' ν) in
/-- The rescaling on the free algebra. -/
noncomputable def rescaleFree : FreeAlgebra k (Gen ν) →ₐ[k] KLRAlgebra k Q' ν :=
  FreeAlgebra.lift k (rescaleGen ν Q' s)

@[simp] theorem rescaleFree_fe (i : Seq ν) : rescaleFree ν Q' s (fe k ν i) = e i :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem rescaleFree_fx (a : Fin m) : rescaleFree ν Q' s (fx k ν a) = x a :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem rescaleFree_fψ (j : ℕ) : rescaleFree ν Q' s (fψ k ν j) = rescaleψ Q' s j :=
  FreeAlgebra.lift_ι_apply _ _

theorem rescaleFree_ncEval {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    rescaleFree ν Q' s (ncEval (fun c => fx k ν (f c)) p) = ncEval (fun c => x (f c)) p := by
  rw [ncEval_map]
  simp only [rescaleFree_fx]

theorem rescaleFree_rel (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)
    ⦃u v : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν u v) :
    rescaleFree ν Q' s u = rescaleFree ν Q' s v := by
  cases h with
  | idem_mul i j =>
    simp only [map_mul, rescaleFree_fe, e_mul_e]
    split_ifs <;> simp
  | idem_sum =>
    simp only [map_sum, rescaleFree_fe, map_one]
    exact sum_e
  | dot_idem a i => simp [x_mul_e]
  | cross_idem j i => simp [rescale_cross_idem]
  | cross_zero j h => simp [rescaleψ, ψ_eq_zero j h]
  | dot_dot a b => simp [x_mul_x]
  | cross_cross j l h => simp [rescale_cross_cross s j l h]
  | dot_cross a j h1 h2 => simp [rescale_dot_cross s a j h1 h2]
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, rescaleFree_fe, rescaleFree_fx, rescaleFree_fψ]
    rw [rescale_dot_cross_left s hs]; split_ifs <;> simp
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, rescaleFree_fe, rescaleFree_fx, rescaleFree_fψ]
    rw [rescale_dot_cross_right s hs]; split_ifs <;> simp
  | cross_sq j h i =>
    simp only [map_mul, rescaleFree_fe, rescaleFree_fψ]
    rw [rescale_cross_sq s hQ]
    split_ifs
    · simp
    · rw [map_mul, rescaleFree_fe, vec2_fx, rescaleFree_ncEval]
      congr 2; funext c; fin_cases c <;> rfl
  | braid j h i =>
    simp only [map_mul, map_sub, rescaleFree_fe, rescaleFree_fψ]
    rw [rescale_braid s hs hQ]
    split_ifs
    · rw [map_mul, rescaleFree_fe, vec3_fx, rescaleFree_ncEval]
      congr 2; funext d; fin_cases d <;> rfl
    · simp

/-- The rescaling as an algebra map `R(ν)_Q → R(ν)_{Q'}`; see `rescale`. -/
noncomputable def rescaleHom (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    KLRAlgebra k Q ν →ₐ[k] KLRAlgebra k Q' ν :=
  RingQuot.liftAlgHom k ⟨rescaleFree ν Q' s, rescaleFree_rel s hs hQ⟩

variable {s}

theorem rescaleHom_mk (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)
    (u : FreeAlgebra k (Gen ν)) : rescaleHom s hs hQ (mk k Q ν u) = rescaleFree ν Q' s u :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem rescaleHom_e (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) (i : Seq ν) :
    rescaleHom s hs hQ (e i : KLRAlgebra k Q ν) = e i := by
  rw [e, rescaleHom_mk, rescaleFree_fe]

@[simp] theorem rescaleHom_x (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) (a : Fin m) :
    rescaleHom s hs hQ (x a : KLRAlgebra k Q ν) = x a := by
  rw [x, rescaleHom_mk, rescaleFree_fx]

@[simp] theorem rescaleHom_ψ (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) (j : ℕ) :
    rescaleHom s hs hQ (ψ j : KLRAlgebra k Q ν) = rescaleψ Q' s j := by
  rw [ψ, rescaleHom_mk, rescaleFree_fψ]

theorem rescaleHom_scaleE (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) (t : I → I → kˣ)
    (j : ℕ) : rescaleHom s hs hQ (scaleE Q t j : KLRAlgebra k Q ν) = scaleE Q' t j := by
  simp [scaleE, map_sum]

omit [DecidableEq I] in
theorem inv_self_eq_one (hs : ∀ a, s a a = 1) (a : I) : s⁻¹ a a = 1 := by
  rw [Pi.inv_apply, Pi.inv_apply, hs, inv_one]

omit [DecidableEq I] in
theorem symm_hQ (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    ∀ a b, a ≠ b → Q' a b = C ((s⁻¹ a b * s⁻¹ b a : kˣ) : k) * Q a b := by
  intro a b hab
  have h1 : (s⁻¹ a b * s⁻¹ b a * (s a b * s b a) : kˣ) = 1 := by
    simp only [Pi.inv_apply]
    rw [mul_mul_mul_comm, inv_mul_cancel, inv_mul_cancel, one_mul]
  rw [hQ a b hab, ← mul_assoc, ← map_mul, ← Units.val_mul, h1, Units.val_one, map_one, one_mul]

theorem rescaleHom_comp {t : I → I → kˣ} (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) (ht : ∀ a, t a a = 1)
    (hQ' : ∀ a b, a ≠ b → Q' a b = C ((t a b * t b a : kˣ) : k) * Q a b)
    (hts : ∀ a b, t a b * s a b = 1) :
    (rescaleHom t ht hQ').comp (rescaleHom s hs hQ) = AlgHom.id k (KLRAlgebra k Q ν) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  change rescaleHom t ht hQ' (rescaleHom s hs hQ (mk k Q ν (FreeAlgebra.ι k g))) =
    mk k Q ν (FreeAlgebra.ι k g)
  cases g with
  | idem i =>
    change rescaleHom t ht hQ' (rescaleHom s hs hQ (e i)) = e i
    rw [rescaleHom_e, rescaleHom_e]
  | dot a =>
    change rescaleHom t ht hQ' (rescaleHom s hs hQ (x a)) = x a
    rw [rescaleHom_x, rescaleHom_x]
  | cross j =>
    change rescaleHom t ht hQ' (rescaleHom s hs hQ (ψ j)) = ψ j
    rw [rescaleHom_ψ, rescaleψ, map_mul, rescaleHom_ψ, rescaleHom_scaleE, rescaleψ, mul_assoc,
      scaleE_mul_eq_one hts, mul_one]

end Hom

variable {Q' : I → I → MvPolynomial (Fin 2) k} {s : I → I → kˣ}

/-- **Rescaling the crossings.** If `s a a = 1` and `Q_{ab} = s_{ab} s_{ba} Q'_{ab}` for
`a ≠ b`, then `R(ν)_Q ≅ R(ν)_{Q'}` by an isomorphism fixing the idempotents and dots and sending
`ψ_j e_i` to `s_{i_j i_{j+1}} ψ_j e_i` (`rescale_ψ_mul_e`). -/
noncomputable def rescale (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    KLRAlgebra k Q ν ≃ₐ[k] KLRAlgebra k Q' ν :=
  AlgEquiv.ofAlgHom (rescaleHom s hs hQ) (rescaleHom s⁻¹ (inv_self_eq_one hs) (symm_hQ hQ))
    (rescaleHom_comp _ _ hs hQ fun a b => by simp only [Pi.inv_apply]; exact mul_inv_cancel _)
    (rescaleHom_comp hs hQ _ _ fun a b => by simp only [Pi.inv_apply]; exact inv_mul_cancel _)

section rescale

variable (hs : ∀ a, s a a = 1)
  (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)

@[simp] theorem rescale_e (i : Seq ν) : rescale hs hQ (e i : KLRAlgebra k Q ν) = e i := rescaleHom_e hs hQ i

@[simp] theorem rescale_x (a : Fin m) : rescale hs hQ (x a : KLRAlgebra k Q ν) = x a := rescaleHom_x hs hQ a

theorem rescale_ψ (j : ℕ) : rescale hs hQ (ψ j : KLRAlgebra k Q ν) = rescaleψ Q' s j := rescaleHom_ψ hs hQ j

theorem rescale_ψ_mul_e (j : ℕ) (i : Seq ν) :
    rescale hs hQ (ψ j * e i : KLRAlgebra k Q ν) = crossScale s j i • (ψ j * e i) := by
  rw [map_mul, rescale_ψ, rescale_e, rescaleψ_mul_e]

theorem rescale_symm_e (i : Seq ν) : (rescale hs hQ).symm (e i : KLRAlgebra k Q' ν) = e i := by
  rw [AlgEquiv.symm_apply_eq, rescale_e]

theorem rescale_symm_x (a : Fin m) : (rescale hs hQ).symm (x a : KLRAlgebra k Q' ν) = x a := by
  rw [AlgEquiv.symm_apply_eq, rescale_x]

end rescale

end KLRAlgebra

end Categorification.KLR
