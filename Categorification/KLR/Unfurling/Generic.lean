/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Cover
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Unfurling along generic spectra

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: the strands of the representations used in the proof
carry only the labels `(i, z_{i,±k})`, where the `z_{i,±k}` are independent indeterminates.
No two of these labels are joined by an arrow of the unfurled graph, because `P_{ij}` is
nonzero and the `z`'s are algebraically independent.

This file builds the unfurling datum on such labels directly, with the series
`ϖ_j(x) = z_j + x` and no arrows: the factorization (equation with label `eq:factorize`)
then holds with exponent zero and unit `P_{π j', π j}(z_j + x, z_{j'} + y)`, whose constant
term is `P_{π j', π j}(z_j, z_{j'}) ≠ 0`. Webster's series `u (1 + x)^{d_i}` would need
`d_i` invertible in the ground field; the linear series need nothing.

## Main definitions and results

* `KLR.Unfurling.UnfurlingDatum.ofGeneric` : the datum on `J` from values `z : J → k`
  that separate the fibres of `π` and do not annihilate `P_{π j', π j}` for `π j ≠ π j'`.
* `KLR.Unfurling.UnfurlingDatum.ofGeneric_arrows` : it has no arrows.
* `KLR.Unfurling.aeval_ne_zero_of_algebraicIndependent` : independent values do not
  annihilate a nonzero polynomial with coefficients in the subfield.
* `KLR.Unfurling.UnfurlingDatum.ofIndependent` : the datum for the base change of a datum
  over `k` to a field `L` containing algebraically independent values.
-/

open MvPolynomial

namespace Categorification.KLR.Unfurling

variable {I J : Type*} {k : Type*} [Field k]

namespace UnfurlingDatum

variable {P : I → I → MvPolynomial (Fin 2) k}

/-- The constant term of `F(z + x, z' + y)` is `F(z, z')`. -/
theorem constantCoeff_aeval_add_X (F : MvPolynomial (Fin 2) k) (z z' : k) :
    constantCoeff (aeval (![C z + X 0, C z' + X 1] : Fin 2 → MvPolynomial (Fin 2) k) F) =
      aeval ![z, z'] F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, aeval_X, aeval_X]
    fin_cases i <;> simp

/-- The unfurling datum on `J` for generic values `z : J → k`: `ϖ_j(x) = z_j + x`, no
arrows, and unit `P°_{jj'} = P_{π j', π j}(z_j + x, z_{j'} + y)` (Webster, arXiv:1603.06311v3,
the choice of labels in the proof of the theorem with label `nondegenerate`, with linear
series). -/
noncomputable def ofGeneric (π : J → I) (z : J → k)
    (hz : ∀ j j', π j = π j' → z j = z j' → j = j')
    (hP : ∀ j j', π j ≠ π j' → aeval ![z j, z j'] (P (π j') (π j)) ≠ 0) :
    UnfurlingDatum k P J where
  π := π
  pw j := Polynomial.C (z j) + Polynomial.X
  pw_coeff_one j := by simp
  pw_coeff_zero_inj j j' h h0 := hz j j' h (by simpa using h0)
  arrows _ _ := 0
  arrows_of_eq _ _ _ := rfl
  unit j j' := aeval ![C (z j) + X 0, C (z j') + X 1] (P (π j') (π j))
  unit_constantCoeff j j' h := by
    have := constantCoeff_aeval_add_X (P (π j') (π j)) (z j) (z j')
    exact fun h0 => hP j j' h (this.symm.trans h0)
  factor j j' _ := by
    rw [pow_zero, one_mul]
    congr 2
    funext i
    fin_cases i <;> simp

@[simp] theorem ofGeneric_π (π : J → I) (z : J → k) (hz) (hP) :
    (ofGeneric (P := P) π z hz hP).π = π := rfl

@[simp] theorem ofGeneric_pw (π : J → I) (z : J → k) (hz) (hP) (j : J) :
    (ofGeneric (P := P) π z hz hP).pw j = Polynomial.C (z j) + Polynomial.X := rfl

@[simp] theorem ofGeneric_arrows (π : J → I) (z : J → k) (hz) (hP) (j j' : J) :
    (ofGeneric (P := P) π z hz hP).arrows j j' = 0 := rfl

end UnfurlingDatum

/-- Algebraically independent values do not annihilate a nonzero polynomial with
coefficients in the subfield. -/
theorem aeval_ne_zero_of_algebraicIndependent {L : Type*} [Field L] [Algebra k L]
    {z : J → L} (hz : AlgebraicIndependent k z) {j j' : J} (hjj' : j ≠ j')
    {F : MvPolynomial (Fin 2) k} (hF : F ≠ 0) : aeval ![z j, z j'] F ≠ 0 := by
  have hinj : Function.Injective ![j, j'] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h2 := hz.comp _ hinj
  have hc : z ∘ ![j, j'] = ![z j, z j'] := by funext i; fin_cases i <;> rfl
  rw [hc] at h2
  intro h0
  exact hF (h2 (by rw [map_zero]; exact h0))

namespace UnfurlingDatum

/-- The generic datum over a field `L ⊇ k` with algebraically independent values `z : J → L`,
for the base change of polynomials `P` over `k` that are nonzero off the diagonal. -/
noncomputable def ofIndependent {L : Type*} [Field L] [Algebra k L]
    {P : I → I → MvPolynomial (Fin 2) k} (hP : ∀ i i', i ≠ i' → P i i' ≠ 0)
    (π : J → I) {z : J → L} (hz : AlgebraicIndependent k z) :
    UnfurlingDatum L (fun i i' => MvPolynomial.map (algebraMap k L) (P i i')) J :=
  ofGeneric π z (fun j j' _ h => hz.injective h) fun j j' h => by
    rw [MvPolynomial.aeval_map_algebraMap L]
    exact aeval_ne_zero_of_algebraicIndependent hz (fun e => h (congrArg π e))
      (hP _ _ (Ne.symm h))

end UnfurlingDatum

end Categorification.KLR.Unfurling
