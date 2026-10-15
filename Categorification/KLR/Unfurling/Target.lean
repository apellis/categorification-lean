/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Grading

/-!
# Unfurling: the KLR data of the unfurled index set

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras* (arXiv:1603.06311v3), §3.3: the unfurled
index set `J` (Def. label `def:tilde-I`) is a quiver with `arrows j j'` arrows from `j` to `j'`,
and its KLR algebra `𝖱` is taken with the geometric polynomials
`𝖯_{j,j'}(x, y) = (x - y)^{#(j → j')}`.

In this library the crossing with bottom labels `(a, b)` acts on the polynomial representation
by multiplication with `P a b`, the variable of the left output strand (labelled `b`) in the
first slot. Webster's `𝖯_{b,a}` is therefore `unfP arrows a b = (X 0 - X 1)^(arrows b a)`, and
`Q a b = P b a(u, v) · P a b(v, u)` gives `unfQ`.

We grade `𝖱` with dots of degree `2` and the crossing with bottom labels `a ≠ b` of degree
`2 · arrows b a` (same-label crossings have degree `-2`). This differs from the symmetric
grading `#(a → b) + #(b → a)` by the shift `Σ_{p < q} (arrows t_q t_p - arrows t_p t_q)` on the
idempotent `e_t`, and makes the polynomial representation graded without shifts.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial

variable {J : Type*} {k : Type*} [CommRing k] (arrows : J → J → ℕ)

/-- Webster's geometric polynomials, in this library's convention for `P`. -/
noncomputable def unfP (a b : J) : MvPolynomial (Fin 2) k := (X 0 - X 1) ^ arrows b a

/-- The parameters `Q` of the unfurled KLR algebra. -/
noncomputable def unfQ (a b : J) : MvPolynomial (Fin 2) k :=
  unfP arrows b a * rename ![1, 0] (unfP arrows a b)

theorem unfQ_eq (a b : J) : unfQ (k := k) arrows a b = unfP arrows b a * rename ![1, 0] (unfP arrows a b) :=
  rfl

theorem isWeightedHomogeneous_X_sub_X_pow (i j : Fin 2) (n : ℕ) :
    ((X i - X j : MvPolynomial (Fin 2) k) ^ n).IsWeightedHomogeneous ![(2 : ℤ), 2] (2 * n) := by
  have h1 : (X i - X j : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![(2 : ℤ), 2] 2 := by
    have hw : ∀ c : Fin 2, (![(2 : ℤ), 2] : Fin 2 → ℤ) c = 2 := by
      intro c; fin_cases c <;> rfl
    have hi := isWeightedHomogeneous_X k ![(2 : ℤ), 2] i
    have hj := isWeightedHomogeneous_X k ![(2 : ℤ), 2] j
    rw [hw] at hi hj
    exact hi.sub hj
  convert h1.pow n using 1
  ring

theorem unfP_isWeightedHomogeneous (a b : J) :
    (unfP (k := k) arrows a b).IsWeightedHomogeneous ![(2 : ℤ), 2] (2 * arrows b a) :=
  isWeightedHomogeneous_X_sub_X_pow _ _ _

theorem unfP_ne_zero [IsDomain k] (a b : J) : unfP (k := k) arrows a b ≠ 0 := by
  refine pow_ne_zero _ (sub_ne_zero.2 fun h => ?_)
  exact absurd (X_injective h) (by decide)

variable [DecidableEq J]

/-- The grading of the unfurled KLR algebra: dots of degree `2`, a crossing with bottom labels
`a ≠ b` of degree `2 · arrows b a`. -/
noncomputable def unfGrading : GradingDatum (unfQ (k := k) arrows) where
  degX _ := 2
  degΨ a b := if a = b then -2 else 2 * arrows b a
  degΨ_self a := by simp
  isWeightedHomogeneous a b hab := by
    simp only [hab, Ne.symm hab, ite_false]
    have h2 : (rename ![(1 : Fin 2), 0] (unfP (k := k) arrows a b)).IsWeightedHomogeneous
        ![(2 : ℤ), 2] (2 * arrows b a) := by
      rw [unfP, map_pow, map_sub, rename_X, rename_X]
      exact isWeightedHomogeneous_X_sub_X_pow _ _ _
    rw [unfQ]
    convert (unfP_isWeightedHomogeneous (k := k) arrows b a).mul h2 using 1
    ring

end Categorification.KLR.Unfurling
