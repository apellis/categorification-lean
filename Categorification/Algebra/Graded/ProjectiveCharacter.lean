/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.G0Basis
import Categorification.Algebra.Graded.HomFormPolynomial

/-!
# Coordinates from graded finite-dimensional modules

Graded Hom into a finite module gives Laurent-polynomial coordinates on
projective classes. Inverting the variable compensates for the shift in
the source of Hom. These are the coordinates used to test diagram
projectives on the standard modules of Webster, arXiv:1309.3796v2, §5.
-/

noncomputable section
namespace Categorification.Graded

universe u v
variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A]
    [Module.Finite k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

private theorem exists_charPolynomial (M : GFin 𝒜) (x : K0 𝒜) :
    ∃ p : LaurentPolynomial ℤ, toLaurentSeries p = pairingRight M x := by
  let S := (toLaurentSeries (R := ℤ)).range
  change pairingRight M x ∈ S
  induction x using K0.induction_on with
  | of P =>
    let := Module.Finite.trans (R := k) (A := A) (M := P.carrier)
    let := (isInternal_homGrade 𝒜 P.grading M.grading).chooseDecomposition
    rw [pairingRight_of]
    exact ⟨_, toLaurentSeries_gdimPoly _⟩
  | zero => simpa only [map_zero] using S.zero_mem
  | add _ _ h h' => simpa only [map_add] using S.add_mem h h'
  | neg _ h => simpa only [map_neg] using S.neg_mem h

/-- Laurent polynomial recording graded Hom from a virtual projective
into a finite-dimensional module. -/
def projectiveHomPolynomial (M : GFin 𝒜) : K0 𝒜 →+ LaurentPolynomial ℤ where
  toFun x := (exists_charPolynomial 𝒜 M x).choose
  map_zero' := toLaurentSeries_injective (by rw [(exists_charPolynomial 𝒜 M 0).choose_spec, map_zero, map_zero])
  map_add' x y := toLaurentSeries_injective (by
    rw [(exists_charPolynomial 𝒜 M _).choose_spec, map_add, map_add,
      (exists_charPolynomial 𝒜 M x).choose_spec, (exists_charPolynomial 𝒜 M y).choose_spec])

theorem toLaurentSeries_projectiveHomPolynomial (M : GFin 𝒜) (x : K0 𝒜) :
    toLaurentSeries (projectiveHomPolynomial 𝒜 M x) = pairingRight M x :=
  (exists_charPolynomial 𝒜 M x).choose_spec

theorem projectiveHomPolynomial_of (M : GFin 𝒜) (P : GProj 𝒜) :
    projectiveHomPolynomial 𝒜 M (K0.of P) = gdimPoly (homGrade A P.grading M.grading) := by
  let := Module.Finite.trans (R := k) (A := A) (M := P.carrier)
  let := (isInternal_homGrade 𝒜 P.grading M.grading).chooseDecomposition
  apply toLaurentSeries_injective
  rw [toLaurentSeries_projectiveHomPolynomial, pairingRight_of, toLaurentSeries_gdimPoly]
  rfl

private theorem projectiveHomPolynomial_T (M : GFin 𝒜) (a : ℤ) (x : K0 𝒜) :
    projectiveHomPolynomial 𝒜 M ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) =
      LaurentPolynomial.T (-a) * projectiveHomPolynomial 𝒜 M x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0.T_smul_of]
    apply toLaurentSeries_injective
    rw [toLaurentSeries_projectiveHomPolynomial, toLaurentSeries_T_mul, toLaurentSeries_projectiveHomPolynomial,
      pairingRight_of, pairingRight_of]
    unfold pairingGdim
    rw [← GProj.gdim_comp_add]
    congr 1
    funext d
    exact homGrade_shift_left a d
  | zero => simp
  | add _ _ hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
  | neg _ hx => rw [smul_neg, map_neg, map_neg, hx, mul_neg]

/-- Inverse-variable graded Hom into a module, linear for the convention
that multiplication by the variable shifts projectives up by one. -/
def projectiveCharacter (M : GFin 𝒜) : K0 𝒜 →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ where
  toFun x := LaurentPolynomial.invert (projectiveHomPolynomial 𝒜 M x)
  map_add' _ _ := by simp
  map_smul' p x := by
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [add_smul, map_add, RingHom.id_apply, hp, hq]
    | single a m =>
      have he : (AddMonoidAlgebra.single a m : LaurentPolynomial ℤ) = m • LaurentPolynomial.T a := by
        rw [LaurentPolynomial.T, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      simp only [he, smul_assoc, map_zsmul, projectiveHomPolynomial_T, map_mul,
        LaurentPolynomial.invert_T, neg_neg, RingHom.id_apply, smul_eq_mul, smul_mul_assoc]

/-- On a principal diagram projective, the Hom polynomial is the
graded dimension of the fixed loading in the target module. -/
theorem projectiveHomPolynomial_ofIdempotent (M : GFin 𝒜) {e : A}
    (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    projectiveHomPolynomial 𝒜 M (K0.of (GProj.ofIdempotent e he he0)) =
      gdimPoly (idem M.grading e) := by
  let := idemDecomposition M.grading he0
  apply toLaurentSeries_injective
  rw [toLaurentSeries_projectiveHomPolynomial, pairingRight_of, toLaurentSeries_gdimPoly]
  exact gdim_homGrade_ofIdempotent he he0

open GProj
variable [HasGdim 𝒜]

/-- Graded Hom into a split simple reads off its indecomposable-projective
coefficient, with the projective shift convention. -/
theorem projectiveCharacter_topFin (hfd : ∀ b : IndecClass 𝒜, FiniteDimensional k b.top)
    (hk : ∀ b : IndecClass 𝒜, Module.finrank k (endZero A b.top.grading) = 1)
    (c : IndecClass 𝒜) (x : K0 𝒜) :
    projectiveCharacter 𝒜 (IndecClass.topFin hfd c) x = (K0.indecBasis 𝒜).repr x c := by
  classical
  let B := K0.indecBasis 𝒜
  suffices h : projectiveCharacter 𝒜 (IndecClass.topFin hfd c) = B.coord c from LinearMap.congr_fun h x
  apply B.ext
  intro b
  have e := pairing_indecBasis_topBasis_of_finrank_eq_one hfd hk b c
  rw [G0.topBasis_apply, pairing, AddMonoidHom.flip_apply, G0.lift_of] at e
  have hp : projectiveHomPolynomial 𝒜 (IndecClass.topFin hfd c) (B b) = if b = c then 1 else 0 := by
    apply toLaurentSeries_injective
    rw [toLaurentSeries_projectiveHomPolynomial, e]
    split_ifs <;> rfl
  change LaurentPolynomial.invert (projectiveHomPolynomial 𝒜 (IndecClass.topFin hfd c) (B b)) = _
  rw [hp, B.coord_apply, B.repr_self]
  split_ifs with h
  · subst b
    simp
  · simp [h]

end Categorification.Graded
