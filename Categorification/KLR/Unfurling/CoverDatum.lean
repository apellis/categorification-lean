/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Target
import Categorification.KLR.CyclotomicFinite
import Categorification.KLR.Symmetries
import Categorification.QuantumGroup.UDotBlock

/-!
# The Cartan and weight data of the unfurled graph

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §3.3: the
unfurled index set `J` carries the KLR parameters `unfQ`, whose factors are powers of `x - y`,
one for each arrow. This file records the Kac–Moody data of `g̃` that these parameters define:

* the symmetric Cartan datum `a · a = 2` and `a · b = -(n_{ab} + n_{ba})` for `a ≠ b`,
  where `n_{ab}` is the number of arrows from `a` to `b` (`coverCartan`);
* a weight datum on `(J → ℤ) × (J →₀ ℤ)`, graded by the root lattice, with coweights the
  finitely supported functions (`coverWeight`); `J` is in general infinite, so this weight
  datum has infinite rank;
* the hypotheses of Kang–Kashiwara (arXiv:1102.4677v4, §3) on `unfQ` for this Cartan datum:
  symmetry `unfQ_klrSymm`, unit leading coefficient `unfQ_leadingCoeff`, and the degree
  `unfQ_natDegree_eq_neg_pair`.
-/

open MvPolynomial

noncomputable section

namespace Categorification.KLR.Unfurling

open QuantumGroup QuantumGroup.UDot

variable {J : Type*}

/-- The pairing of a finitely supported coweight `y` with a weight `x : J → ℤ`. -/
def coverPair : (J →₀ ℤ) →+ (J → ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun a => zmultiplesHom _ (Pi.evalAddMonoidHom (fun _ => ℤ) a)

@[simp] theorem coverPair_single (a : J) (n : ℤ) (x : J → ℤ) :
    coverPair (Finsupp.single a n) x = n * x a := by
  simp [coverPair]

section Cartan

variable [DecidableEq J] (arrows : J → J → ℕ)

/-- The Cartan datum of the unfurled graph (Webster, arXiv:1603.06311v3, §3.3):
`a · a = 2` and `a · b = -(n_{ab} + n_{ba})` for `a ≠ b`. -/
def coverCartan : CartanDatum J where
  dot a b := if a = b then 2 else -((arrows a b + arrows b a : ℕ) : ℤ)
  symm a b := by
    by_cases h : a = b
    · subst h; rfl
    · simp only [h, Ne.symm h, ↓reduceIte, add_comm]
  dot_self_pos a := by simp
  dot_self_even a := by simp
  dot_nonpos a b h := by simp [h]
  dvd_two_mul a b := by simp; split_ifs <;> omega

@[simp] theorem coverCartan_dot_self (a : J) : (coverCartan arrows).dot a a = 2 := by
  simp [coverCartan]

theorem coverCartan_dot_of_ne {a b : J} (h : a ≠ b) :
    (coverCartan arrows).dot a b = -((arrows a b + arrows b a : ℕ) : ℤ) := by
  simp [coverCartan, h]

/-- The weight datum of the unfurled graph, graded by the root lattice. A weight is a pair
`(x, γ)` of a function `x : J → ℤ` and a finitely supported `γ : J →₀ ℤ`. The coweights are
the finitely supported functions `J →₀ ℤ`, `a_Y` is the indicator of `a`, and
`a_X = (b ↦ b · a, single a 1)`; the pairing only sees `x`. The second component records the
root-lattice degree, so the cyclotomic weight space of a weight is the module category of at
most one block `R^Λ(β)`, also when `g̃` has imaginary roots. -/
def coverWeight : WeightDatum (coverCartan arrows) ((J → ℤ) × (J →₀ ℤ)) (J →₀ ℤ) where
  pair := AddMonoidHom.flip (coverPair.flip.comp (AddMonoidHom.fst _ _))
  iX b := (fun a => (coverCartan arrows).dot a b, Finsupp.single b 1)
  iY a := Finsupp.single a 1
  pair_iY_iX a b := by
    change coverPair (Finsupp.single a 1) (fun a' => (coverCartan arrows).dot a' b) = _
    rw [coverPair_single, one_mul, coverCartan_dot_self]
    omega

@[simp] theorem coverWeight_pair (y : J →₀ ℤ) (x : (J → ℤ) × (J →₀ ℤ)) :
    (coverWeight arrows).pair y x = coverPair y x.1 := rfl

@[simp] theorem coverWeight_pair_iY (a : J) (x : (J → ℤ) × (J →₀ ℤ)) :
    (coverWeight arrows).pair ((coverWeight arrows).iY a) x = x.1 a := by
  simp [coverWeight]

@[simp] theorem coverWeight_iX (b : J) :
    (coverWeight arrows).iX b =
      (fun a => (coverCartan arrows).dot a b, Finsupp.single b 1) := rfl

end Cartan

variable (arrows : J → J → ℕ) {k : Type*} [CommRing k]

/-- The unfurled parameters are symmetric: `Q_{ba}(u, v) = Q_{ab}(v, u)`. -/
theorem unfQ_klrSymm : KLRSymm (unfQ (k := k) arrows) := by
  intro a b _
  simp only [unfQ, map_mul, rename_rename]
  rw [mul_comm]
  congr 1
  · conv_rhs => rw [show (![1, 0] : Fin 2 → Fin 2) ∘ ![1, 0] = id by
      funext i; fin_cases i <;> rfl]
    rw [rename_id_apply]

/-- In the second variable, `unfQ a b` is `±(y - x)^{n_{ab} + n_{ba}}`. -/
theorem polyInY_unfQ (a b : J) :
    polyInY (unfQ (k := k) arrows a b) =
      Polynomial.C ((-1) ^ arrows a b) *
        (Polynomial.X - Polynomial.C Polynomial.X) ^ (arrows b a + arrows a b) := by
  simp only [unfQ, unfP, polyInY, map_mul, map_pow, map_sub, aeval_rename, aeval_X,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (Polynomial.C Polynomial.X - Polynomial.X : Polynomial (Polynomial k)) =
    Polynomial.C (-1) * (Polynomial.X - Polynomial.C Polynomial.X) by
      rw [map_neg, map_one]; ring, mul_pow, ← map_pow]
  ring

theorem polyInY_unfQ_monic_part (a b : J) :
    ((Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial k)) ^
      (arrows b a + arrows a b)).Monic :=
  (Polynomial.monic_X_sub_C _).pow _

/-- The leading coefficient of `unfQ a b` in the second variable is the unit `±1`. -/
theorem unfQ_leadingCoeff [IsDomain k] (a b : J) :
    ∃ c : k, IsUnit c ∧ (polyInY (unfQ (k := k) arrows a b)).leadingCoeff = Polynomial.C c := by
  refine ⟨(-1) ^ arrows a b, (isUnit_neg_one (α := k)).pow _, ?_⟩
  rw [polyInY_unfQ, Polynomial.leadingCoeff_mul, (polyInY_unfQ_monic_part arrows a b).leadingCoeff,
    mul_one, Polynomial.leadingCoeff_C, map_pow, map_neg, map_one]

/-- The degree of `unfQ b a` in the second variable is `-⟨a, b_X⟩ = n_{ab} + n_{ba}`
(Kang–Kashiwara, arXiv:1102.4677v4, §3, for the Cartan datum `coverCartan`). -/
theorem unfQ_natDegree_eq_neg_pair [DecidableEq J] [IsDomain k] {a b : J} (h : b ≠ a) :
    ((polyInY (unfQ (k := k) arrows b a)).natDegree : ℤ) =
      -(coverWeight arrows).pair ((coverWeight arrows).iY a) ((coverWeight arrows).iX b) := by
  rw [polyInY_unfQ,
    Polynomial.natDegree_C_mul (((isUnit_neg_one (α := Polynomial k)).pow _).ne_zero),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
    coverWeight_pair_iY, coverWeight_iX]
  dsimp only
  rw [coverCartan_dot_of_ne arrows (Ne.symm h)]
  push_cast
  ring

end Categorification.KLR.Unfurling

end
