/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.RightTwist
import Categorification.WeightedKLR.RedStrands.RightBoundaryProjectives
import Categorification.WeightedKLR.RedStrands.TensorHomForm

/-!
# Theorem 4.38 for right projectives

Webster, arXiv:1309.3796v2, works with right modules over the tensor product algebra `T^λ`:
Theorem 4.38 identifies the graded Grothendieck group of finitely generated graded right
projective `T^λ`-modules with the integral form of `V_λ = V_{λ₁} ⊗ ⋯ ⊗ V_{λ_ℓ}`, and Lemma 4.36
computes graded Hom spaces between projectives by the repaired form preceding Proposition 4.33.

The comparison in `TensorModuleIdentification` and `TensorHomForm` is built with graded left
projectives. Horizontal reflection `tensorReflection` is a degree-preserving anti-involution of
`T^λ`, so twisting by it identifies left and right graded projectives (`K0.rightTwistEquiv`),
preserving shifts, direct sums and graded Hom spaces. This file transports Theorem 4.38 and
Lemma 4.36 along that identification.

Conventions.
* The identification is semilinear along `q ↦ q⁻¹`: Webster's shift is `A(i)_n = A_{i+n}`,
  while `GMod.shift` is the opposite shift.
* The word projectives are the right twists of the left divided-word projectives. For sequence
  words these are the right ideals `e A` (`sequenceProj_rightEquiv`).
* In the Euler pairing, the target of a Hom occupies the first slot of the corrected tensor
  form: `gdim HOM(P, Q) = B(η Q, η P)`. This comes from the repair of the form preceding
  Proposition 4.33, not from the choice of side.

## Main definitions and results

* `rightTensorProjectiveGroup` : `K₀` of graded right projective `T^λ`-modules in a black content.
* `tensorReflectionK0` : `K₀` of left projectives `≃` `K₀` of right projectives.
* `rightTensorModuleEquiv`, `rightTensorModuleEquiv_word`, `rightTensorModuleEquiv_unique` :
  Theorem 4.38 for right projectives.
* `rightTensorModuleEquiv_homForm`, `rightTensorModuleEquiv_homForm_of` : the Euler pairing,
  Theorem 4.38 and Lemma 4.36 for right projectives.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra Categorification.Graded QuantumGroup LieLean LieLean.QuantumGroup
open scoped RatFunc
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local notation "series" => algebraMap L (LaurentSeries ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair inversion.toRingHom inversion.toRingHom :=
  RingHomInvPair.of_ringEquiv inversion

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "M" => DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

omit [Finite I] in
/-- The crossing degrees of the standard Stendhal grading are symmetric. -/
theorem stendhalGradingDatum_degΨ_symm :
    ∀ a b, (G).degΨ a b = (G).degΨ b a := by
  rintro (a|a) (b|b) <;> try rfl
  exact congrArg Neg.neg (C.symm a b)

/-- Horizontal reflection of `T^λ` in black content `β`. -/
abbrev tensorReflectionG (β : Multiset I) : GradedAntiInvolution (tensorProductGrade G β) :=
  tensorReflection (ν := β) G (stendhalGradingDatum_degΨ_symm C hQ Λ)

/-- The graded Grothendieck group of graded right projective `T^λ`-modules in black content
`β`, the group of Webster, arXiv:1309.3796v2, Theorem 4.38. -/
abbrev rightTensorProjectiveGroup (β : Multiset I) :=
  K0 (oppositeGrade (tensorProductGrade G β))

local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "Mr" => DirectSum (Multiset I) (rightTensorProjectiveGroup C hQ Λ)

omit [Finite I] in
/-- Right twisting by horizontal reflection, summed over all black contents. -/
def tensorReflectionK0 : M ≃ₗ[LP] Mr :=
  DFinsupp.mapRange.linearEquiv fun β => K0.rightTwistEquiv (tensorReflectionG C hQ Λ β)

omit [Finite I] in
@[simp] theorem tensorReflectionK0_lof (β : Multiset I) (x : K β) :
    tensorReflectionK0 C hQ Λ (DirectSum.lof LP _ K β x) =
      DirectSum.lof LP _ Kr β (K0.rightTwistEquiv (tensorReflectionG C hQ Λ β) x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)

/-- The shifted divided-word projective of `w`, as a graded right projective: the right twist
of the left word projective by horizontal reflection. -/
def rightTensorWordProjective (w : TensorWord I ℓ) :
    GProj (oppositeGrade (tensorProductGrade G w.content.toMultiset)) :=
  (tensorWordProjective Λ C hQ w).rightTwist (tensorReflectionG C hQ Λ _)

/-- The total class of the right word projective. -/
def rightTensorWordProjectiveClass (w : TensorWord I ℓ) : Mr :=
  DirectSum.lof LP _ Kr w.content.toMultiset (K0.of (rightTensorWordProjective C hQ Λ w))

omit [Finite I] in
theorem tensorReflectionK0_wordClass (w : TensorWord I ℓ) :
    tensorReflectionK0 C hQ Λ (tensorWordProjectiveClass Λ C hQ w) =
      rightTensorWordProjectiveClass C hQ Λ w := by
  rw [tensorWordProjectiveClass, tensorReflectionK0_lof, K0.rightTwistEquiv_of]
  rfl

/-- **Webster, arXiv:1309.3796v2, Theorem 4.38, for right projectives.** The canonical
identification of `K₀` of graded right projective `T^λ`-modules with the integral form of the
tensor product. The grading shift maps to `v⁻¹`. -/
def rightTensorModuleEquiv : Mr ≃ₛₗ[inversion.toRingHom] integralTensor wt :=
  (tensorReflectionK0 C hQ Λ).symm.trans η

local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt

/-- Theorem 4.38 on every shifted divided-word right projective. -/
@[simp] theorem rightTensorModuleEquiv_word (w : TensorWord I ℓ) :
    η' (rightTensorWordProjectiveClass C hQ Λ w) = integralWordVector (C := C) wt w := by
  rw [rightTensorModuleEquiv, LinearEquiv.trans_apply, ← tensorReflectionK0_wordClass,
    LinearEquiv.symm_apply_apply, tensorModuleEquiv_word]

/-- Webster, §4.7, Lemma 4.37 and Theorem 4.38, for right projectives: the values on the word
projectives determine the semilinear map. -/
theorem rightTensorModuleEquiv_unique (g : Mr →ₛₗ[inversion.toRingHom] integralTensor wt)
    (hw : ∀ w, g (rightTensorWordProjectiveClass C hQ Λ w) = integralWordVector (C := C) wt w) :
    g = (η').toLinearMap := by
  have h := tensorModuleEquiv_unique C hQ hR Λ wt hwt (g.comp (tensorReflectionK0 C hQ Λ).toLinearMap)
    fun w => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorReflectionK0_wordClass, hw]
  ext x
  obtain ⟨y, rfl⟩ := (tensorReflectionK0 C hQ Λ).surjective x
  have hy := LinearMap.congr_fun h y
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe] at hy
  rw [hy, LinearEquiv.coe_coe, LinearEquiv.coe_coe, rightTensorModuleEquiv,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

private local instance blockGdimRight (ν : Multiset I) :
    HasGdim (tensorProductGrade G ν) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  exact HasGdim.of_finiteDimensional _

/-- Graded Hom on `K₀` of graded right projective `T^λ`-modules, summing the blockwise
Euler forms over the finitely many supported black contents. -/
def rightTensorProjectiveHomForm : Mr →+ Mr →+ LaurentSeries ℤ :=
  DirectSum.toAddMonoid fun ν =>
    { toFun := fun x => (K0.homForm (oppositeGrade (tensorProductGrade G ν)) x).comp
        (DirectSum.component LP _ Kr ν).toAddMonoidHom
      map_zero' := by ext z; simp only [map_zero, AddMonoidHom.zero_apply, AddMonoidHom.comp_apply]
      map_add' := fun x y => by
        ext z
        simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.comp_apply] }

omit [Finite I] in
private theorem rightHomForm_lof (ν : Multiset I) (x : Kr ν) (y : Mr) :
    rightTensorProjectiveHomForm C hQ Λ (DirectSum.lof LP _ Kr ν x) y =
      K0.homForm (oppositeGrade (tensorProductGrade G ν)) x (y ν) := by
  unfold rightTensorProjectiveHomForm
  dsimp only [DirectSum.lof_eq_of]
  rw [DirectSum.toAddMonoid_of]
  rfl

omit [Finite I] in
private theorem leftHomForm_lof (ν : Multiset I) (x : K ν) (y : M) :
    tensorProjectiveHomForm C hQ Λ (DirectSum.lof LP _ K ν x) y =
      K0.homForm (tensorProductGrade G ν) x (y ν) := by
  unfold tensorProjectiveHomForm
  dsimp only [DirectSum.lof_eq_of]
  rw [DirectSum.toAddMonoid_of]
  rfl

omit [Finite I] in
/-- Right twisting by horizontal reflection carries the graded Hom form on left projectives to
the graded Hom form on right projectives. -/
theorem rightTensorProjectiveHomForm_tensorReflectionK0 (x y : M) :
    rightTensorProjectiveHomForm C hQ Λ (tensorReflectionK0 C hQ Λ x)
      (tensorReflectionK0 C hQ Λ y) = tensorProjectiveHomForm C hQ Λ x y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x z hx hz => simp only [map_add, AddMonoidHom.add_apply, hx, hz]
  | of β x =>
    change rightTensorProjectiveHomForm C hQ Λ (tensorReflectionK0 C hQ Λ
      (DirectSum.lof LP _ K β x)) _ = tensorProjectiveHomForm C hQ Λ (DirectSum.lof LP _ K β x) y
    rw [tensorReflectionK0_lof, rightHomForm_lof, leftHomForm_lof]
    change K0.homForm _ _ (DFinsupp.mapRange _ _ y β) = _
    rw [DFinsupp.mapRange_apply]
    exact K0.homForm_rightTwistEquiv _ x (y β)

/-- **Webster, arXiv:1309.3796v2, Theorem 4.38 and Lemma 4.36, for right projectives**, with
the corrected tensor form: the graded Hom form on arbitrary virtual graded right projectives
is the ordered tensor form on their images, the target of the Hom in the first slot. -/
theorem rightTensorModuleEquiv_homForm (x y : Mr) :
    lsCast (rightTensorProjectiveHomForm C hQ Λ x y) = series (B (η' y).val (η' x).val) := by
  obtain ⟨x, rfl⟩ := (tensorReflectionK0 C hQ Λ).surjective x
  obtain ⟨y, rfl⟩ := (tensorReflectionK0 C hQ Λ).surjective y
  rw [rightTensorProjectiveHomForm_tensorReflectionK0, rightTensorModuleEquiv,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]
  exact tensorModuleEquiv_homForm C hQ hR Λ wt hwt x y

/-- Lemma 4.36 for graded right projectives in one block: `gdim HOM(P, Q)` is the corrected
form `B(η Q, η P)`. -/
theorem rightTensorModuleEquiv_homForm_of (ν : Multiset I)
    (P Q' : GProj (oppositeGrade (tensorProductGrade G ν))) :
    lsCast (K0.homForm _ (K0.of P) (K0.of Q')) =
      series (B (η' (DirectSum.lof LP _ Kr ν (K0.of Q'))).val
        (η' (DirectSum.lof LP _ Kr ν (K0.of P))).val) := by
  rw [← rightTensorModuleEquiv_homForm, rightHomForm_lof, DirectSum.lof_apply]

end Categorification.Stendhal.FirstWeight
