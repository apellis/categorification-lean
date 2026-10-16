/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverLabels
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Generic fields for the two parts of the unfurled graph

The field construction in the proof of the theorem labelled `nondegenerate` in
B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3.
We implement the algebraic closures successively: `K` is an algebraic closure of
`k(z⁻)`, and `L` an algebraic closure of `K(z⁺)`. This realizes both alphabets in
one algebraically closed extension, with `K` integrally closed in `L` and every
positive indeterminate outside `K`. Their union is algebraically independent over `k`.

`neg` and `pos` supply the subtype-valued labels of `coverWeightNeg` and
`coverWeightPos`; their injectivity discharges the distinctness assumptions of
the weight evaluation lemmas. No hypotheses on chosen fields or spectral values
are required.
-/

noncomputable section

namespace Categorification.KLR.Unfurling.GenericFields

variable (k : Type*) [Field k] (A B : Type*)

/-- An algebraic closure of the rational function field on an alphabet. -/
abbrev Closure := AlgebraicClosure (FractionRing (MvPolynomial A k))

/-- The indeterminate in the algebraic closure of the rational function field. -/
def indeterminate (a : A) : Closure k A :=
  algebraMap (MvPolynomial A k) (Closure k A) (MvPolynomial.X a)

/-- Passing from the polynomial ring to its fraction field and algebraic closure
preserves algebraic independence. -/
theorem independent_indeterminate : AlgebraicIndependent k (indeterminate k A) :=
  (MvPolynomial.algebraicIndependent_X A k).map'
    (f := IsScalarTower.toAlgHom k (MvPolynomial A k) (Closure k A))
    ((algebraMap (FractionRing (MvPolynomial A k)) (Closure k A)).injective.comp
      (IsFractionRing.injective _ _))

/-- The algebraically closed field generated algebraically by the negative indeterminates. -/
abbrev K := Closure k A

/-- The ambient algebraically closed field, adjoining the positive indeterminates after `K`. -/
abbrev L := Closure (K k A) B

instance integrallyClosedIn : IsIntegrallyClosedIn (K k A) (L k A B) where
  algebraMap_injective := (algebraMap (K k A) (L k A B)).injective
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact hx.mem_range_algebraMap_of_minpoly_splits (K := K k A) (IsAlgClosed.splits _)
    · rintro ⟨y, rfl⟩
      exact isIntegral_algebraMap

/-- Negative generic scalars, embedded in the ambient field. -/
def zNeg (a : A) : L k A B := algebraMap (K k A) (L k A B) (indeterminate k A a)

/-- Positive generic scalars. -/
def zPos (b : B) : L k A B := indeterminate (K k A) B b

/-- The two alphabets are jointly algebraically independent over the ground field. -/
theorem independent : AlgebraicIndependent k (Sum.elim (zNeg k A B) (zPos k A B)) := by
  have h := ((independent_indeterminate k A).sumElim_comp
    (independent_indeterminate (K k A) B)).comp Sum.swap (Equiv.sumComm A B).injective
  have he : (Sum.elim (indeterminate (K k A) B)
      (algebraMap (K k A) (L k A B) ∘ indeterminate k A) ∘ Sum.swap) =
      Sum.elim (zNeg k A B) (zPos k A B) := by
    funext x
    cases x <;> rfl
  exact he ▸ h

/-- In particular, negative indeterminates remain independent after embedding in `L`. -/
theorem independent_neg : AlgebraicIndependent k (zNeg k A B) :=
  (independent k A B).comp Sum.inl Sum.inl_injective

/-- Positive indeterminates are independent even over `K`. -/
theorem independent_pos : AlgebraicIndependent (K k A) (zPos k A B) :=
  independent_indeterminate (K k A) B

/-- A positive indeterminate does not belong to the image of `K`. -/
theorem zPos_not_mem (b : B) : zPos k A B b ∉ Set.range (algebraMap (K k A) (L k A B)) := by
  rintro ⟨x, hx⟩
  exact (independent_pos k A B).transcendental b (hx ▸ isAlgebraic_algebraMap x)

/-- Negative scalar labels in the subtype expected by `coverWeightNeg`. -/
def neg (a : A) : {u : L k A B // u ≠ 0 ∧ u ∈ Set.range (algebraMap (K k A) (L k A B))} :=
  ⟨zNeg k A B a, (independent_neg k A B).ne_zero a, ⟨indeterminate k A a, rfl⟩⟩

/-- Positive scalar labels in the subtype expected by `coverWeightPos`. -/
def pos (b : B) : {u : L k A B // u ≠ 0 ∧ u ∉ Set.range (algebraMap (K k A) (L k A B))} :=
  ⟨zPos k A B b, (independent_pos k A B).ne_zero b, zPos_not_mem k A B b⟩

theorem neg_injective : Function.Injective (neg k A B) := fun _ _ h =>
  (independent_neg k A B).injective (congrArg Subtype.val h)

theorem pos_injective : Function.Injective (pos k A B) := fun _ _ h =>
  (independent_pos k A B).injective (congrArg Subtype.val h)

section Weights

variable (I Q : Type*)

/-- Negative labels over each colour. -/
def zm (i : I) (q : Q) := neg k (I × Q) (I × Q) (i, q)

/-- Positive labels over each colour. -/
def zp (i : I) (q : Q) := pos k (I × Q) (I × Q) (i, q)

theorem zm_injective (i : I) : Function.Injective (zm k I Q i) := fun _ _ h =>
  (Prod.mk.inj ((neg_injective k (I × Q) (I × Q)) h)).2

theorem zp_injective (i : I) : Function.Injective (zp k I Q i) := fun _ _ h =>
  (Prod.mk.inj ((pos_injective k (I × Q) (I × Q)) h)).2

variable [Fintype Q]

/-- The negative weight with prescribed multiplicities at the generic labels. -/
def weightNeg (nm : I → Q → ℕ) := coverWeightNeg (zm k I Q) nm

/-- The positive weight with prescribed multiplicities at the generic labels. -/
def weightPos (np : I → Q → ℕ) := coverWeightPos (zp k I Q) np

@[simp] theorem weightNeg_mk (nm : I → Q → ℕ) (i : I) (q : Q) :
    weightNeg k I Q nm ⟨i, zm k I Q i q⟩ = nm i q :=
  coverWeightNeg_mk (zm k I Q) nm (zm_injective k I Q i) q

@[simp] theorem weightPos_mk (np : I → Q → ℕ) (i : I) (q : Q) :
    weightPos k I Q np ⟨i, zp k I Q i q⟩ = np i q :=
  coverWeightPos_mk (zp k I Q) np (zp_injective k I Q i) q

theorem weightNeg_finite [Finite I] (nm : I → Q → ℕ) :
    (Function.support (weightNeg k I Q nm)).Finite :=
  coverWeightNeg_finite (zm k I Q) nm (Set.toFinite _)

theorem weightPos_finite [Finite I] (np : I → Q → ℕ) :
    (Function.support (weightPos k I Q np)).Finite :=
  coverWeightPos_finite (zp k I Q) np (Set.toFinite _)

end Weights

end Categorification.KLR.Unfurling.GenericFields
