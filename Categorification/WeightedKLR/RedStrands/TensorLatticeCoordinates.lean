/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop318
import Categorification.Algebra.Graded.ProjectiveCharacter
import Categorification.KLR.CyclotomicIntegralLattice

/-!
# Rational coordinates for projective tests on an integral tensor lattice

In the comparison of tensor words in Webster, arXiv:1309.3796v2,
Theorem 4.38, simple tops give Laurent-polynomial coordinates on a
projective basis. Each coordinate of a lattice basis extends to a
rational functional on the ambient tensor representation.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open Module

variable {R K V J : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {L : Submodule R V} (b : Basis J R L)

include b in
/-- Over the fraction field, any functional on a free lattice with values in
the field extends to the ambient vector space. -/
theorem exists_rationalLatticeFunctional (f : L →ₗ[R] K) :
    ∃ g : V →ₗ[K] K, ∀ x : L, g x = f x := by
  classical
  let v : J → V := fun i => b i
  have h : LinearIndependent K v :=
    (b.linearIndependent.map' L.subtype L.ker_subtype).localization K (nonZeroDivisors R)
  let B := Basis.span h
  let p := B.constr K (fun i => f (b i))
  obtain ⟨g,hg⟩ := p.exists_extend
  refine ⟨g, ?_⟩
  have he : (g.restrictScalars R).comp L.subtype = f := by
    apply b.ext
    intro i
    have hi := LinearMap.congr_fun hg (B i)
    rw [LinearMap.comp_apply, Submodule.subtype_apply, Basis.coe_span_apply,
      Basis.constr_basis] at hi
    exact hi
  exact LinearMap.congr_fun he

/-- The rational extensions of all basis coordinates separate the points
of the integral lattice. -/
theorem exists_separatingLatticeCoordinates :
    ∃ t : J → V →ₗ[K] K,
      (∀ j (x : L), t j x = algebraMap R K (b.repr x j)) ∧
      Function.Injective (fun x : L => fun j => t j x) := by
  choose t ht using fun j => exists_rationalLatticeFunctional b ((Algebra.linearMap R K).comp (b.coord j))
  refine ⟨t,ht,?_⟩
  intro x y h
  apply b.repr.injective
  ext j
  exact IsFractionRing.injective R K (((ht j x).symm.trans (congrFun h j)).trans (ht j y))

section TensorTests

open scoped TensorProduct
variable {F X Y A B : Type*} [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (p : A → X) (q : B → Y) (f : A → X →ₗ[F] F) (g : B → Y →ₗ[F] F)

/-- Product of two rational coordinate tests on independent tensor factors. -/
def factorTensorTest (a : A) (b : B) : X ⊗[F] Y →ₗ[F] F :=
  (TensorProduct.lid F F).toLinearMap.comp (TensorProduct.map (f a) (g b))

@[simp] theorem factorTensorTest_tmul (a : A) (b : B) (x : X) (y : Y) :
    factorTensorTest f g a b (x ⊗ₜ[F] y) = f a x * g b y := by
  simp [factorTensorTest]

open scoped Classical in
/-- Products of dual tests separate the span of any selected collection of
factor pairs. The collection can impose a total black content. -/
theorem factorTensorTest_separates {Z : Type*} (j : Z ↪ A × B)
    (hf : ∀ a i, f a (p i) = if a = i then 1 else 0)
    (hg : ∀ b i, g b (q i) = if b = i then 1 else 0) :
    Function.Injective (fun x : Submodule.span F (Set.range (fun z => p (j z).1 ⊗ₜ[F] q (j z).2)) =>
      fun z => factorTensorTest f g (j z).1 (j z).2 x) := by
  classical
  let v := fun z => p (j z).1 ⊗ₜ[F] q (j z).2
  let t := fun z => factorTensorTest f g (j z).1 (j z).2
  have ht (z w) : t z (v w) = if z = w then 1 else 0 := by
    simp only [t,v,factorTensorTest_tmul, hf,hg]
    by_cases e : z = w
    · simp [e]
    · have ne : ¬ ((j z).1 = (j w).1 ∧ (j z).2 = (j w).2) :=
        fun h => e (j.injective (Prod.ext h.1 h.2))
      by_cases h : (j z).1 = (j w).1 <;> simp_all
  have coeff (c : Z →₀ F) (z : Z) : t z (Finsupp.linearCombination F v c) = c z := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    simp only [map_smul, ht, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp +contextual
  intro x y h
  have repr (w : Submodule.span F (Set.range v)) : ∃ c, Finsupp.linearCombination F v c = w.val := by
    exact (SetLike.ext_iff.mp (Finsupp.range_linearCombination (v := v) F) w.val).mpr w.property
  obtain ⟨c,hc⟩ := repr x
  obtain ⟨d,hd⟩ := repr y
  have e : c = d := by
    ext z
    rw [← coeff c z, ← coeff d z, hc, hd]
    exact congrFun h z
  exact Subtype.ext (hc.symm.trans (e ▸ hd))

end TensorTests

section Projectives
open Categorification.Graded GProj KLR
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion
local instance : Algebra LP 𝕂 := KLGamma.vAlgebra
local instance : IsFractionRing LP 𝕂 := KLGamma.isFractionRing_vAlgebra

variable {k A U : Type*} [Field k] [Ring A] [Algebra k A] [Module.Finite k A]
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [HasGdim 𝒜]
    [AddCommGroup U] [Module 𝕂 U] [Module LP U] [IsScalarTower LP 𝕂 U] {W : Submodule LP U}

/-- Given the semilinear identification of an earlier tensor lattice, each
basis coefficient gives a rational test on its ambient tensor space. -/
theorem exists_invertedBasisTests {P J : Type*} [AddCommGroup P] [Module LP P]
    (b : Basis J LP P) (e : P ≃ₛₗ[inversion.toRingHom] W) :
    ∃ t : J → U →ₗ[𝕂] 𝕂,
      (∀ j x, t j (e x) = algebraMap LP 𝕂 (LaurentPolynomial.invert (b.repr x j))) ∧
      Function.Injective (fun x : W => fun j => t j x) := by
  let σ : (J →₀ LP) ≃ₛₗ[inversion.toRingHom] (J →₀ LP) :=
    Finsupp.mapRange.linearEquiv inversion.toSemilinearEquiv
  let B : Basis J LP W := ⟨e.symm.trans (b.repr.trans σ)⟩
  obtain ⟨t,ht,hinj⟩ := exists_separatingLatticeCoordinates (K := 𝕂) B
  refine ⟨t,fun j x => ?_,hinj⟩
  rw [ht]
  change algebraMap LP 𝕂 (LaurentPolynomial.invert (b.repr (e.symm (e x)) j)) = _
  rw [e.symm_apply_apply]

/-- For an identified projective lattice, rational tensor functionals recover
the graded Hom polynomials into its simple tops. The Laurent inversion of the
identification cancels the source shift in Hom. -/
theorem exists_rationalTopTests (e : K0 𝒜 ≃ₛₗ[inversion.toRingHom] W)
    (hfd : ∀ b : IndecClass 𝒜, FiniteDimensional k b.top)
    (hk : ∀ b : IndecClass 𝒜, Module.finrank k (endZero A b.top.grading) = 1) :
    ∃ t : IndecClass 𝒜 → U →ₗ[𝕂] 𝕂,
      (∀ j x, t j (e x) = algebraMap LP 𝕂 (projectiveHomPolynomial 𝒜 (IndecClass.topFin hfd j) x)) ∧
      Function.Injective (fun x : W => fun j => t j x) := by
  obtain ⟨t,ht,hinj⟩ := exists_invertedBasisTests (K0.indecBasis 𝒜) e
  refine ⟨t,fun j x => ?_,hinj⟩
  rw [ht, ← projectiveCharacter_topFin 𝒜 hfd hk]
  apply congrArg (algebraMap LP 𝕂)
  exact LaurentPolynomial.invert.symm_apply_apply _

/-- For a direct sum of identified projective blocks, the test indexed by
a simple in block `i` reads the Hom polynomial of the `i`-component.
Consequently it vanishes on all other weight blocks. -/
theorem exists_totalTopTests {D : Type*} {A : D → Type*} [∀ i, Ring (A i)] [∀ i, Algebra k (A i)]
    [∀ i, Module.Finite k (A i)] (s : ∀ i, ℤ → Submodule k (A i)) [∀ i, GradedAlgebra (s i)]
    [∀ i, HasGdim (s i)] (e : DirectSum D (fun i => K0 (s i)) ≃ₛₗ[inversion.toRingHom] W)
    (hfd : ∀ i (b : IndecClass (s i)), FiniteDimensional k b.top)
    (hk : ∀ i (b : IndecClass (s i)), Module.finrank k (endZero (A i) b.top.grading) = 1) :
    ∃ t : (Σ i, IndecClass (s i)) → U →ₗ[𝕂] 𝕂,
      (∀ i j x, t ⟨i,j⟩ (e x) = algebraMap LP 𝕂
        (projectiveHomPolynomial (s i) (IndecClass.topFin (hfd i) j) (x i))) ∧
      Function.Injective (fun x : W => fun j => t j x) := by
  let B := DFinsupp.basis (fun i => K0.indecBasis (s i))
  obtain ⟨t,ht,hinj⟩ := exists_invertedBasisTests B e
  refine ⟨t,fun i j x => ?_,hinj⟩
  rw [ht]
  apply congrArg (algebraMap LP 𝕂)
  change LaurentPolynomial.invert ((K0.indecBasis (s i)).repr (x i) j) = _
  rw [← projectiveCharacter_topFin (s i) (hfd i) (hk i)]
  exact LaurentPolynomial.invert.symm_apply_apply _

end Projectives

end Categorification.Stendhal.FirstWeight
