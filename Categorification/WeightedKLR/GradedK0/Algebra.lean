/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Induction
import Categorification.WeightedKLR.Induction.ModuleMonoidal
import Mathlib.Algebra.DirectSum.Algebra
import Categorification.WeightedKLR.GradedK0.AssociatorGrading
import Categorification.WeightedKLR.GradedK0.Units

/-!
# The graded Grothendieck algebra of weighted KLR algebras

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Definition 2.17 and Theorem 2.19: induction gives an associative unital
product on the direct sum of the graded Grothendieck groups. This supporting
algebra for roadmap C is defined for every grading datum over every commutative
coefficient ring. Its scalars are `ℤ[q,q⁻¹]`, with `q` acting by grading shift.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra Juxtapose Categorification.Graded Categorification.InductionAlong
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}


namespace GradingDatum

/-- The graded Grothendieck groups indexed by dimension vectors. -/
abbrev K0fam (G : GradingDatum Γ) : (I →₀ ℕ) → Type _ := fun ν => K0 (G.klrGrade ν)

/-- The direct sum underlying the graded Grothendieck algebra of weighted KLR
algebras (Webster arXiv:1209.2463v4, Theorem 2.19). -/
abbrev K0W (G : GradingDatum Γ) : Type _ := DirectSum (I →₀ ℕ) G.K0fam


variable (G : GradingDatum Γ)

section Associativity

variable {ν ν' ν'' : I →₀ ℕ}

/-- The graded module associator identifies the two iterated induction classes
(Webster arXiv:1209.2463v4, §2.4, Theorem 2.19). -/
theorem K0cast_indProj_assoc (P : GProj (G.klrGrade ν)) (Q : GProj (G.klrGrade ν'))
    (R : GProj (G.klrGrade ν'')) :
    G.K0cast (add_assoc ν ν' ν'') (K0.of (G.indProj (G.indProj P Q) R)) =
      K0.of (G.indProj P (G.indProj Q R)) := by
  let X := G.indProj (G.indProj P Q) R
  let Y := G.indProj P (G.indProj Q R)
  let e : X.carrier ≃ₗ[k] Y.carrier :=
    gradedIndAssocEquiv (k := k) (Γ := Γ) ν ν' ν'' P.carrier Q.carrier R.carrier
  refine G.K0cast_of_linearEquiv (add_assoc ν ν' ν'') X Y e ?_ ?_
  · intro b x
    exact gradedIndAssocEquiv_smul (k := k) (Γ := Γ)
      ν ν' ν'' P.carrier Q.carrier R.carrier b x
  · intro d x hx
    exact G.gradedIndAssocEquiv_mem_grading P Q R hx

/-- **Associativity of `[Ind]`** (Webster arXiv:1209.2463v4, §2.4, Theorem 2.19): for all `x ∈ K₀(W(ν))`,
`y ∈ K₀(W(ν'))`, `z ∈ K₀(W(ν''))`, `(x y) z = x (y z)` (after identifying
`K₀(W((ν + ν') + ν'')) = K₀(W(ν + (ν' + ν'')))`). -/
theorem indK0_assoc (x : K0 (G.klrGrade ν)) (y : K0 (G.klrGrade ν')) (z : K0 (G.klrGrade ν'')) :
    G.K0cast (add_assoc ν ν' ν'') (G.indK0 (ν + ν') ν'' (G.indK0 ν ν' x y) z) =
      G.indK0 ν (ν' + ν'') x (G.indK0 ν' ν'' y z) := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of P' =>
      induction z using K0.induction_on with
      | of P'' =>
        rw [indK0_of, indK0_of, indK0_of, indK0_of]
        exact G.K0cast_indProj_assoc P P' P''
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | neg z hz => simp only [map_neg, hz]
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | neg y hy => simp only [map_neg, LinearMap.neg_apply, hy]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

end Associativity

instance gMulK0 : GradedMonoid.GMul G.K0fam where
  mul {ν ν'} x y := G.indK0 ν ν' x y

instance gOneK0 : GradedMonoid.GOne G.K0fam where
  one := G.K0one

theorem gMul_def {ν ν' : I →₀ ℕ} (x : K0 (G.klrGrade ν)) (y : K0 (G.klrGrade ν')) :
    GradedMonoid.GMul.mul (A := G.K0fam) x y = G.indK0 ν ν' x y :=
  rfl

theorem mk_mul_mk {ν ν' : I →₀ ℕ} (x : K0 (G.klrGrade ν)) (y : K0 (G.klrGrade ν')) :
    GradedMonoid.mk (A := G.K0fam) ν x * GradedMonoid.mk ν' y =
      GradedMonoid.mk (A := G.K0fam) (ν + ν') (G.indK0 ν ν' x y) := rfl

theorem mk_K0cast {μ μ' : I →₀ ℕ} (h : μ = μ') (x : K0 (G.klrGrade μ)) :
    GradedMonoid.mk (A := G.K0fam) μ x = GradedMonoid.mk (A := G.K0fam) μ' (G.K0cast h x) :=
  G.gradedMonoid_mk_K0cast h x

theorem one_mk_mul {ν : I →₀ ℕ} (x : K0 (G.klrGrade ν)) :
    (1 : GradedMonoid G.K0fam) * GradedMonoid.mk ν x = GradedMonoid.mk ν x := by
  show GradedMonoid.mk (A := G.K0fam) (0 + ν) (G.indK0 0 ν G.K0one x) = _
  rw [G.mk_K0cast (zero_add ν), indK0_one_left]

theorem mk_mul_one {ν : I →₀ ℕ} (x : K0 (G.klrGrade ν)) :
    GradedMonoid.mk (A := G.K0fam) ν x * (1 : GradedMonoid G.K0fam) = GradedMonoid.mk ν x := by
  show GradedMonoid.mk (A := G.K0fam) (ν + 0) (G.indK0 ν 0 x G.K0one) = _
  rw [G.mk_K0cast (add_zero ν), indK0_one_right]

instance gMonoidK0 : GradedMonoid.GMonoid G.K0fam where
  one_mul a := by obtain ⟨ν, x⟩ := a; exact G.one_mk_mul x
  mul_one a := by obtain ⟨ν, x⟩ := a; exact G.mk_mul_one x
  mul_assoc a b c := by
    obtain ⟨ν, x⟩ := a
    obtain ⟨ν', y⟩ := b
    obtain ⟨ν'', z⟩ := c
    show GradedMonoid.mk (A := G.K0fam) ν x * GradedMonoid.mk ν' y * GradedMonoid.mk ν'' z =
      GradedMonoid.mk (A := G.K0fam) ν x * (GradedMonoid.mk ν' y * GradedMonoid.mk ν'' z)
    rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, G.mk_K0cast (add_assoc ν ν' ν''),
      indK0_assoc]

instance gRingK0 : DirectSum.GRing G.K0fam where
  mul_zero {ν ν'} x := by rw [gMul_def, map_zero]
  zero_mul {ν ν'} y := by rw [gMul_def, map_zero, LinearMap.zero_apply]
  mul_add {ν ν'} x y y' := by rw [gMul_def, gMul_def, gMul_def, map_add]
  add_mul {ν ν'} x x' y := by rw [gMul_def, gMul_def, gMul_def, map_add, LinearMap.add_apply]
  natCast n := n • G.K0one
  natCast_zero := zero_smul _ _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • G.K0one
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

instance gAlgebraK0 : DirectSum.GAlgebra (LaurentPolynomial ℤ) G.K0fam where
  toFun :=
    { toFun := fun p => p • G.K0one
      map_zero' := zero_smul _ _
      map_add' := fun p p' => add_smul _ _ _ }
  map_one := one_smul _ _
  map_mul r s := by
    show GradedMonoid.mk (A := G.K0fam) 0 ((r * s) • G.K0one) = GradedMonoid.mk (0 + 0)
      (G.indK0 0 0 (r • G.K0one) (s • G.K0one))
    rw [G.mk_K0cast (zero_add (0 : I →₀ ℕ))]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, K0cast_smul]
    rw [indK0_one_left, mul_smul]
  commutes r x := by
    obtain ⟨ν, x⟩ := x
    show GradedMonoid.mk (A := G.K0fam) (0 + ν) (G.indK0 0 ν (r • G.K0one) x) =
      GradedMonoid.mk (ν + 0) (G.indK0 ν 0 x (r • G.K0one))
    rw [G.mk_K0cast (zero_add ν), G.mk_K0cast (add_zero ν)]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, K0cast_smul]
    rw [indK0_one_left, indK0_one_right]
  smul_def r x := by
    obtain ⟨ν, x⟩ := x
    show GradedMonoid.mk (A := G.K0fam) ν (r • x) =
      GradedMonoid.mk (0 + ν) (G.indK0 0 ν (r • G.K0one) x)
    rw [G.mk_K0cast (zero_add ν)]
    simp only [LinearMap.map_smul₂, K0cast_smul]
    rw [indK0_one_left]

example : Ring G.K0W := inferInstance

example : Algebra (LaurentPolynomial ℤ) G.K0W := inferInstance

/-- The product on `K₀(W)` of homogeneous elements is `[Ind]`. -/
theorem K0W_of_mul_of {ν ν' : I →₀ ℕ} (x : K0 (G.klrGrade ν)) (y : K0 (G.klrGrade ν')) :
    (DirectSum.of G.K0fam ν x * DirectSum.of G.K0fam ν' y : G.K0W) =
      DirectSum.of G.K0fam (ν + ν') (G.indK0 ν ν' x y) :=
  DirectSum.of_mul_of (A := G.K0fam) x y

/-- The homogeneous inclusion respects the Laurent-polynomial scalar action. -/
theorem K0W_of_smul (p : LaurentPolynomial ℤ) {ν : I →₀ ℕ} (x : K0 (G.klrGrade ν)) :
    DirectSum.of G.K0fam ν (p • x) = p • (DirectSum.of G.K0fam ν x : G.K0W) := by
  rw [← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
    ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), map_smul]

/-- The unit of `K₀(W)` is `[W(0)]`. -/
theorem K0W_one : (1 : G.K0W) = DirectSum.of G.K0fam 0 (K0.of (GProj.regular (G.klrGrade 0))) :=
  rfl

/-- `[P] [P'] = [Ind (P ⊠ P')]` in `K₀(W)`. -/
theorem K0W_of_of_mul_of_of {ν ν' : I →₀ ℕ} (P : GProj (G.klrGrade ν))
    (P' : GProj (G.klrGrade ν')) :
    (DirectSum.of G.K0fam ν (K0.of P) * DirectSum.of G.K0fam ν' (K0.of P') : G.K0W) =
      DirectSum.of G.K0fam (ν + ν') (K0.of (G.indProj P P')) := by
  rw [K0W_of_mul_of, indK0_of]

/-- The `ℤ[q, q⁻¹]`-algebra structure: `p • x = (p • [W(0)]) * x`. -/
theorem K0W_algebraMap (p : LaurentPolynomial ℤ) :
    algebraMap (LaurentPolynomial ℤ) G.K0W p =
      DirectSum.of G.K0fam 0 (p • K0.of (GProj.regular (G.klrGrade 0))) :=
  rfl


end GradingDatum

end Categorification.WeightedKLR
