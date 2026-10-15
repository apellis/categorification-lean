/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverDatum
import Categorification.KLR.CyclotomicAction.PresCL
import Categorification.TwoRep.RouqProductKLR

/-!
# The cyclotomic families of the unfurled graph and their product

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: the representation used there is a generalized cyclotomic
quotient of the KLR algebra of the unfurled graph `g̃`, highest weight on one part `Ĩ₊` of the
labels and lowest weight on the other part `Ĩ₋`, with no arrows between the parts.

For an arrow count `n : J → J → ℕ` and a dominant weight `Λ : J → ℕ` of `g̃`, `coverFamily n Λ`
is the weight-indexed cyclotomic Rouquier family (Kang–Kashiwara, arXiv:1102.4677v4, §4.2 and
Theorem 5.2) of the parameters `unfQ n` with cyclotomic polynomials `a_j = x^{Λ_j}`, over the
weight datum `coverWeight n` of infinite rank. It satisfies Brundan's upward relations
(arXiv:1501.00350v1, (1.2)–(1.4)) with Brundan's scalars, and the mixed inversion (1.7).

`coverProduct` is the Rouquier family on the categories `Hom(T(-μ₊), W(μ₋))` for the cyclotomic
families `W` of `Ĩ₋` and `T` of `Ĩ₊`, with its upward relations and mixed inversion
(`TwoRep.RouqFamily.homProduct`).

## Main definitions and results

* `KLR.Unfurling.coverFamily`, `coverFamily_brundanUpKLR`, `coverFamily_mixedInversion`.
* `KLR.Unfurling.coverProduct`, `coverProduct_upKLR`, `coverProduct_mixedInversion`.
-/

open MvPolynomial CategoryTheory

noncomputable section

namespace Categorification.KLR.Unfurling

open QuantumGroup QuantumGroup.UDot TwoRep CyclotomicAction

universe u v w

variable {J : Type u} [DecidableEq J] (n : J → J → ℕ) {L : Type v} [Field L] (Λ : J → ℕ)

omit [DecidableEq J] in
theorem cover_hlead : ∀ j l : J, j ≠ l →
    ∃ c : L, IsUnit c ∧ (polyInY (unfQ (k := L) n j l)).leadingCoeff = Polynomial.C c :=
  fun j l _ => unfQ_leadingCoeff n j l

omit [DecidableEq J] in
theorem cover_hmonic : ∀ j : J, (Polynomial.X ^ Λ j : Polynomial L).Monic :=
  fun _ => Polynomial.monic_X_pow _

theorem cover_hΛ : ∀ j : J, (((Polynomial.X ^ Λ j : Polynomial L)).natDegree : ℤ) =
    (coverWeight n).pair ((coverWeight n).iY j) ((fun j => (Λ j : ℤ)), 0) := by
  intro j
  rw [Polynomial.natDegree_X_pow, coverWeight_pair_iY]

theorem cover_hdeg : ∀ i j : J, j ≠ i →
    ((polyInY (unfQ (k := L) n j i)).natDegree : ℤ) =
      -(coverWeight n).pair ((coverWeight n).iY i) ((coverWeight n).iX j) :=
  fun _ _ h => unfQ_natDegree_eq_neg_pair n h

/-- **The cyclotomic Rouquier family of the unfurled graph** with dominant weight `Λ`
(Webster, arXiv:1603.06311v3, proof of `nondegenerate`; Kang–Kashiwara, arXiv:1102.4677v4,
Theorem 5.2), on the root-graded weight datum of infinite rank `coverWeight n`: each weight space is the module
category of a single cyclotomic block `R^Λ(β)` (or zero). -/
def coverFamily :
    RouqFamily (B := LinearCat.{v, max (max u v) w, max (max u v) w + 1} L) (coverWeight n) :=
  cyclotomicFamily.{u, v, w} (unfQ_klrSymm n) (cover_hlead n) (cover_hmonic (L := L) Λ)
    (coverWeight n) ((fun j => (Λ j : ℤ)), 0) (cover_hΛ n Λ) (cover_hdeg n)

theorem coverFamily_upKLR : RouqUpKLR (coverFamily.{u, v, w} n (L := L) Λ) (unfQ (k := L) n) :=
  cyclotomicFamily_upKLR _ _ _ _ _ _ _

theorem coverFamily_mixedInversion :
    BrundanMixedInversion (coverFamily.{u, v, w} n (L := L) Λ) :=
  cyclotomicFamily_mixedInversion _ _ _ _ _ _ _

omit [DecidableEq J] in
/-- `unfQ a b` is homogeneous of degree `2 (n_{ab} + n_{ba})` for the weights `(2, 2)`. -/
theorem unfQ_isWeightedHomogeneous (a b : J) :
    (unfQ (k := L) n a b).IsWeightedHomogeneous ![(2 : ℤ), 2] (2 * n a b + 2 * n b a) := by
  simp only [unfQ, unfP, map_pow, map_sub, rename_X]
  exact (isWeightedHomogeneous_X_sub_X_pow 0 1 _).mul (isWeightedHomogeneous_X_sub_X_pow _ _ _)

/-- The coefficients of `unfQ` above the line vanish (the hypothesis of `KLR.eq_brundanQ`). -/
theorem cover_hsupp : ∀ i j : J, i ≠ j → ∀ p q : ℕ,
    -2 * (coverCartan n).dot i j < (coverCartan n).dot i i * p + (coverCartan n).dot j j * q →
      (unfQ (k := L) n i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0 := by
  intro i j hij p q hlt
  by_contra hne
  have h := unfQ_isWeightedHomogeneous n (L := L) i j hne
  rw [map_add, Finsupp.weight_single, Finsupp.weight_single] at h
  rw [coverCartan_dot_self, coverCartan_dot_self, coverCartan_dot_of_ne n hij] at hlt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul] at h
  push_cast at hlt h
  omega

/-- **Brundan's upward relations for the cyclotomic family of the unfurled graph**, with the
Cautis–Lauda scalars of `unfQ` (Brundan, arXiv:1501.00350v1, (1.2)–(1.4)). -/
theorem coverFamily_brundanUpKLR :
    BrundanUpKLR (coverFamily.{u, v, w} n (L := L) Λ)
      (cyclotomicScalars (unfQ_klrSymm (k := L) n) (cover_hlead n) (coverWeight n)
        (cover_hdeg n)) :=
  cyclotomicFamily_brundanUpKLR _ _ _ _ _ _ _ (cover_hsupp n)

variable {J₂ : Type u} [DecidableEq J₂] (n₂ : J₂ → J₂ → ℕ) (Λ₂ : J₂ → ℕ)

/-- **The product of the lowest weight family of `Ĩ₋` and the highest weight family of `Ĩ₊`**
(Webster, arXiv:1603.06311v3, proof of `nondegenerate`): the Rouquier family on the categories
`Hom(T(-μ₊), W(μ₋))`, `W = coverFamily n Λ`, `T = coverFamily n₂ Λ₂`. -/
def coverProduct :=
  RouqFamily.homProduct L (coverFamily.{u, v, w} n (L := L) Λ) (coverFamily.{u, v, w} n₂ Λ₂)

theorem coverProduct_upKLR :
    RouqUpKLR (coverProduct.{u, v, w} n (L := L) Λ n₂ Λ₂)
      (RouqFamily.prodQ (unfQ (k := L) n) (unfQ (k := L) n₂)) :=
  RouqFamily.homProduct_upKLR _ _ (coverFamily_upKLR n Λ) (coverFamily_upKLR n₂ Λ₂)
    (unfQ_klrSymm n₂)

theorem coverProduct_mixedInversion :
    BrundanMixedInversion (coverProduct.{u, v, w} n (L := L) Λ n₂ Λ₂) :=
  RouqFamily.homProduct_mixedInversion _ _ (coverFamily_mixedInversion n Λ) _
    (coverFamily_brundanUpKLR n₂ Λ₂) (coverFamily_mixedInversion n₂ Λ₂)

end Categorification.KLR.Unfurling

end
