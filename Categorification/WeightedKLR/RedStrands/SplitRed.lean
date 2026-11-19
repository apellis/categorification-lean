/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedLoading
import Categorification.KLR.Concat

/-!
# Splitting a red strand: the algebra map

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. Let `λ'_1, …, λ'_{ℓ+1}` be dominant weights and let `λ` be the sequence of
`ℓ` weights obtained by merging `λ'_c` and `λ'_{c+1}` into `λ'_c + λ'_{c+1}`. Replacing the red
strand `λ'_c + λ'_{c+1}` of a Stendhal diagram by two parallel red strands `λ'_c`, `λ'_{c+1}`
defines an algebra map from the Stendhal algebra of `λ` into the corner of the Stendhal algebra
of `λ'` cut out by the loadings in which the two red strands are adjacent.

This file constructs the generators of that corner and the relations they satisfy.

## Main definitions

* `mergeWeights Λ' c` : the weights `λ` with `λ'_c` and `λ'_{c+1}` merged.
* `splitIdem` : the sum of the idempotents of the split loadings.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv MvPolynomial

/-! ### Generic facts about Stendhal algebras -/

section Generic

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {L : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin L → I →₀ ℕ} {ν : Multiset I}

local notation "B" => StendhalAlgebraAllOrders k Q Λ ν
local notation "n" => Multiset.card (stendhalWeight L ν)

open StendhalAlgebraAllOrders

theorem aSum_e : (∑ s : Seq (stendhalWeight L ν), e s : B) = 1 := by
  simp only [e, ← map_sum, KLRAlgebra.sum_e, map_one]

theorem aψ_mul_e (j : ℕ) (s : Seq (stendhalWeight L ν)) :
    (ψ j * e s : B) = e (sadj n j • s) * ψ j := by
  rw [ψ, e, e, ← map_mul, KLRAlgebra.ψ_mul_e, map_mul]

theorem aψ_eq_zero (j : ℕ) (h : n ≤ j + 1) : (ψ j : B) = 0 := by
  rw [ψ, KLRAlgebra.ψ_eq_zero j h, map_zero]

theorem aψ_mul_ψ (j l : ℕ) (h : j + 1 < l) : (ψ j * ψ l : B) = ψ l * ψ j := by
  rw [ψ, ψ, ← map_mul, KLRAlgebra.ψ_mul_ψ j l h, map_mul]

theorem ax_mul_ψ (a : Fin n) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (x a * ψ j : B) = ψ j * x a := by
  rw [x, ψ, ← map_mul, KLRAlgebra.x_mul_ψ a j h₁ h₂, map_mul]

theorem ae_mul_e (s t : Seq (stendhalWeight L ν)) :
    (e s * e t : B) = if s = t then e s else 0 := e_mul_e s t

variable (k Q Λ ν) in
/-- Polynomials in the dots. -/
def polA : MvPolynomial (Fin n) k →ₐ[k] B :=
  (ofKLR k Q Λ ν).comp KLRAlgebra.pol

theorem polA_X (a : Fin n) : polA k Q Λ ν (X a) = x a := by
  simp [polA, x]

theorem e_commute_polA (s : Seq (stendhalWeight L ν)) (p : MvPolynomial (Fin n) k) :
    Commute (e s : B) (polA k Q Λ ν p) := by
  have := (KLRAlgebra.e_commute_pol (Q := stendhalQ Q Λ) s p).map (ofKLR k Q Λ ν)
  simpa [polA, e] using this

theorem ncEval_x_eq_polA {r : ℕ} (f : Fin r → Fin n) (p : MvPolynomial (Fin r) k) :
    ncEval (fun a => (x (f a) : B)) p = polA k Q Λ ν (rename f p) := by
  simp_rw [← polA_X]
  exact ncEval_algHom_X _ f p

/-- The quadratic relation in a Stendhal algebra. -/
theorem aψ_sq (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν)) :
    (ψ j * ψ j * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩ then 0 else
        polA k Q Λ ν (rename ![⟨j, by omega⟩, ⟨j + 1, h⟩]
          (stendhalQ Q Λ (s.lbl ⟨j, by omega⟩) (s.lbl ⟨j + 1, h⟩))) * e s := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) j h s)
  have hv : (![KLRAlgebra.x ⟨j, by omega⟩, KLRAlgebra.x ⟨j + 1, h⟩] :
      Fin 2 → KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight L ν)) =
      fun a => KLRAlgebra.x (![⟨j, by omega⟩, ⟨j + 1, h⟩] a) := by
    funext a; fin_cases a <;> rfl
  rw [hv, KLRAlgebra.ncEval_eq_pol] at key
  split_ifs at key ⊢ <;> simpa [ψ, e, polA] using key

/-- The braid relation in a Stendhal algebra. -/
theorem aBraid (j : ℕ) (h : j + 2 < n) (s : Seq (stendhalWeight L ν)) :
    ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 2, h⟩ ∧
          s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, by omega⟩ then
        polA k Q Λ ν (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (stendhalQ Q Λ (s.lbl ⟨j, by omega⟩) (s.lbl ⟨j + 1, by omega⟩)))) * e s
      else 0 := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.braid (Q := stendhalQ Q Λ) j h s)
  have hv : (![KLRAlgebra.x ⟨j, by omega⟩, KLRAlgebra.x ⟨j + 1, by omega⟩,
      KLRAlgebra.x ⟨j + 2, h⟩] : Fin 3 → KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight L ν)) =
      fun a => KLRAlgebra.x (![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩] a) := by
    funext a; fin_cases a <;> rfl
  rw [hv, KLRAlgebra.ncEval_eq_pol] at key
  split_ifs at key ⊢ <;> simpa [ψ, e, polA] using key

theorem aDotCrossLeft (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν)) :
    ((x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩ then e s else 0 := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.dot_cross_left (Q := stendhalQ Q Λ) j h s)
  split_ifs at key ⊢ <;> simpa [ψ, e, x] using key

theorem aDotCrossRight (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν)) :
    ((ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩ then e s else 0 := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.dot_cross_right (Q := stendhalQ Q Λ) j h s)
  split_ifs at key ⊢ <;> simpa [ψ, e, x] using key

theorem ax_mul_e (a : Fin n) (s : Seq (stendhalWeight L ν)) : (x a * e s : B) = e s * x a := by
  rw [← polA_X]; exact (e_commute_polA s _).symm.eq

/-- A dot slides through a crossing of strands with different labels, from the right strand
to the left one. -/
theorem slideL (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν))
    (hs : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, h⟩) (r : ℕ) :
    (ψ j * x ⟨j + 1, h⟩ ^ r * e s : B) = x ⟨j, by omega⟩ ^ r * ψ j * e s := by
  have h1 : (ψ j * x ⟨j + 1, h⟩ * e s : B) = x ⟨j, by omega⟩ * ψ j * e s := by
    have := aDotCrossLeft (Q := Q) (Λ := Λ) j h s
    simp only [hs, ↓reduceIte, sub_mul, sub_eq_zero] at this
    exact this.symm
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, mul_assoc _ (x _) (e s), ax_mul_e, ← mul_assoc, ih,
      mul_assoc _ (e s), ← ax_mul_e, mul_assoc, mul_assoc, ← mul_assoc (ψ j), h1]
    simp only [pow_succ, mul_assoc]

/-- A dot slides through a crossing of strands with different labels, from the left strand
to the right one. -/
theorem slideR (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν))
    (hs : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, h⟩) (r : ℕ) :
    (ψ j * x ⟨j, by omega⟩ ^ r * e s : B) = x ⟨j + 1, h⟩ ^ r * ψ j * e s := by
  have h1 : (ψ j * x ⟨j, by omega⟩ * e s : B) = x ⟨j + 1, h⟩ * ψ j * e s := by
    have := aDotCrossRight (Q := Q) (Λ := Λ) j h s
    simp only [hs, ↓reduceIte, sub_mul, sub_eq_zero] at this
    exact this
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, mul_assoc _ (x _) (e s), ax_mul_e, ← mul_assoc, ih,
      mul_assoc _ (e s), ← ax_mul_e, mul_assoc, mul_assoc, ← mul_assoc (ψ j), h1]
    simp only [pow_succ, mul_assoc]

end Generic

end Categorification.Stendhal.SplitRed
