/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.ScalarComparison

/-!
# Graded induction units

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Definition 2.17 and the unit of the multiplication in Theorem 2.19.
The regular module of `W_0` is a two-sided unit for induction. The existing
module isomorphisms preserve grading: their inverses insert the degree-zero
juxtaposition idempotent and the degree-zero element `1 ∈ W_0`. Thus the
regular class of `W_0` acts as a unit on every graded projective class, over
any commutative coefficient ring.
-/

noncomputable section

namespace Categorification.WeightedKLR

open scoped TensorProduct
open MulOpposite Categorification.Graded GalleryAlgebra Juxtapose Categorification.InductionAlong

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GradingDatum

variable (G : GradingDatum Γ)

/-- Transport of the graded Grothendieck group along equality of dimension vectors. -/
def K0cast {ν μ : I →₀ ℕ} (h : ν = μ) : K0 (G.klrGrade ν) →+ K0 (G.klrGrade μ) := by
  subst h
  exact AddMonoidHom.id _

@[simp] theorem K0cast_rfl {ν : I →₀ ℕ} (x : K0 (G.klrGrade ν)) :
    G.K0cast rfl x = x := rfl

theorem K0cast_trans {ν μ τ : I →₀ ℕ} (h : ν = μ) (h' : μ = τ) (x : K0 (G.klrGrade ν)) :
    G.K0cast h' (G.K0cast h x) = G.K0cast (h.trans h') x := by
  subst h
  subst h'
  rfl

@[simp] theorem K0cast_smul {ν μ : I →₀ ℕ} (h : ν = μ) (c : LaurentPolynomial ℤ)
    (x : K0 (G.klrGrade ν)) : G.K0cast h (c • x) = c • G.K0cast h x := by
  subst h
  rfl

/-- Equal dimension vectors identify the corresponding elements of the graded monoid. -/
theorem gradedMonoid_mk_K0cast {ν μ : I →₀ ℕ} (h : ν = μ) (x : K0 (G.klrGrade ν)) :
    (GradedMonoid.mk ν x : GradedMonoid fun τ => K0 (G.klrGrade τ)) =
      GradedMonoid.mk μ (G.K0cast h x) := by
  subst h
  rfl

/-- A degree-preserving isomorphism semilinear along `castW` computes transport on classes. -/
theorem K0cast_of_linearEquiv {ν μ : I →₀ ℕ} (h : ν = μ)
    (X : GProj (G.klrGrade ν)) (Y : GProj (G.klrGrade μ))
    (φ : X.carrier ≃ₗ[k] Y.carrier)
    (hφ : ∀ (b : WeightedKLRAlgebra k Γ ν) (x : X.carrier),
      φ (b • x) = castW k Γ h b • φ x)
    (hgr : ∀ ⦃d : ℤ⦄ ⦃x : X.carrier⦄, x ∈ X.grading d → φ x ∈ Y.grading d) :
    G.K0cast h (K0.of X) = K0.of Y := by
  subst h
  rw [K0cast_rfl]
  exact K0.of_eq_of_iso (GradedEquiv.ofPreserves
    (φ.toAddEquiv.toLinearEquiv fun b x => hφ b x) (fun _ _ hx => hgr hx))

end GradingDatum

namespace Juxtapose

section UnitModules

variable (ν : I →₀ ℕ) (M : Type*) [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]

/-- Scalar-linear comparison for the left unit, with tensor actions fixed at module level. -/
def gradedUnitLeftLinear :
    GradedInd k Γ 0 ν (ExtTensor k (WeightedKLRAlgebra k Γ 0) M) ≃ₗ[k] M := by
  let E := gradedIndScalarEquiv (k := k) (Γ := Γ) 0 ν
    (ExtTensor k (WeightedKLRAlgebra k Γ 0) M)
  let U := indUnitLeftEquiv k Γ ν M
  exact
    { E.toAddEquiv.trans U.toAddEquiv with
      map_smul' := fun c x => by
        change U (E (c • x)) = c • U (E x)
        rw [← algebraMap_smul (WeightedKLRAlgebra k Γ (0 + ν)) c x, map_smul]
        exact (indUnitLeftEquiv_smul ν M _ _).trans (by
          rw [AlgEquiv.commutes, algebraMap_smul]) }

/-- Scalar-linear comparison for the right unit, with tensor actions fixed at module level. -/
def gradedUnitRightLinear :
    GradedInd k Γ ν 0 (ExtTensor k M (WeightedKLRAlgebra k Γ 0)) ≃ₗ[k] M := by
  let E := gradedIndScalarEquiv (k := k) (Γ := Γ) ν 0
    (ExtTensor k M (WeightedKLRAlgebra k Γ 0))
  let U := indUnitRightEquiv k Γ ν M
  exact
    { E.toAddEquiv.trans U.toAddEquiv with
      map_smul' := fun c x => by
        change U (E (c • x)) = c • U (E x)
        rw [← algebraMap_smul (WeightedKLRAlgebra k Γ (ν + 0)) c x, map_smul]
        exact (indUnitRightEquiv_smul ν M _ _).trans (by
          rw [AlgEquiv.commutes, algebraMap_smul]) }

theorem gradedUnitLeftLinear_smul (b : WeightedKLRAlgebra k Γ (0 + ν))
    (x : GradedInd k Γ 0 ν (ExtTensor k (WeightedKLRAlgebra k Γ 0) M)) :
    gradedUnitLeftLinear ν M (b • x) =
      castW k Γ (zero_add ν) b • gradedUnitLeftLinear ν M x := by
  change indUnitLeftEquiv k Γ ν M ((gradedIndScalarEquiv 0 ν _) (b • x)) = _
  rw [map_smul, indUnitLeftEquiv_smul]
  rfl

theorem gradedUnitRightLinear_smul (b : WeightedKLRAlgebra k Γ (ν + 0))
    (x : GradedInd k Γ ν 0 (ExtTensor k M (WeightedKLRAlgebra k Γ 0))) :
    gradedUnitRightLinear ν M (b • x) =
      castW k Γ (add_zero ν) b • gradedUnitRightLinear ν M x := by
  change indUnitRightEquiv k Γ ν M ((gradedIndScalarEquiv ν 0 _) (b • x)) = _
  rw [map_smul, indUnitRightEquiv_smul]
  rfl

@[simp] theorem gradedUnitLeftLinear_symm_apply (x : M) :
    (gradedUnitLeftLinear ν M).symm x =
      BalancedTensor.tmul (k := k) (B := WeightedKLRAlgebra k Γ (0 + ν))
        (A := TensorW k Γ 0 ν) (M := GradedIndBimod k Γ 0 ν) (unitGen (inductionRingHom k Γ 0 ν))
        (ExtTensor.tmul (1 : WeightedKLRAlgebra k Γ 0) x) := by
  apply (gradedUnitLeftLinear ν M).injective
  refine ((gradedUnitLeftLinear ν M).apply_symm_apply x).trans ?_
  have h := gradedIndScalarEquiv_tmul 0 ν _
    (show GradedIndBimod k Γ 0 ν from unitGen (inductionRingHom k Γ 0 ν))
    (ExtTensor.tmul (k := k) (1 : WeightedKLRAlgebra k Γ 0) x)
  exact ((indUnitLeftEquiv k Γ ν M).apply_symm_apply x).symm.trans
    (congrArg (indUnitLeftEquiv k Γ ν M) h.symm)

@[simp] theorem gradedUnitRightLinear_symm_apply (x : M) :
    (gradedUnitRightLinear ν M).symm x =
      BalancedTensor.tmul (k := k) (B := WeightedKLRAlgebra k Γ (ν + 0))
        (A := TensorW k Γ ν 0) (M := GradedIndBimod k Γ ν 0) (unitGen (inductionRingHom k Γ ν 0))
        (ExtTensor.tmul x (1 : WeightedKLRAlgebra k Γ 0)) := by
  apply (gradedUnitRightLinear ν M).injective
  refine ((gradedUnitRightLinear ν M).apply_symm_apply x).trans ?_
  have h := gradedIndScalarEquiv_tmul ν 0 _
    (show GradedIndBimod k Γ ν 0 from unitGen (inductionRingHom k Γ ν 0))
    (ExtTensor.tmul (k := k) x (1 : WeightedKLRAlgebra k Γ 0))
  exact ((indUnitRightEquiv k Γ ν M).apply_symm_apply x).symm.trans
    (congrArg (indUnitRightEquiv k Γ ν M) h.symm)

variable (G : GradingDatum Γ) (𝒩 : ℤ → Submodule k M)

theorem gradedUnitLeftLinear_symm_mem_grading {d : ℤ} {x : M} (hx : x ∈ 𝒩 d) :
    (gradedUnitLeftLinear ν M).symm x ∈
      G.gradedIndGrading 0 ν (ExtTensor.grading (G.klrGrade 0) 𝒩) d := by
  rw [gradedUnitLeftLinear_symm_apply]
  have hu : unitGen (inductionRingHom k Γ 0 ν) ∈ G.indBimodGrading 0 ν 0 :=
    G.inductionMap_one_mem_klrGrade
  have ht := ExtTensor.tmul_mem_grading (SetLike.GradedOne.one_mem (A := G.klrGrade 0)) hx
  simpa only [zero_add] using tmul_mem_balancedGrading (M := GradedIndBimod k Γ 0 ν) hu ht

theorem gradedUnitRightLinear_symm_mem_grading {d : ℤ} {x : M} (hx : x ∈ 𝒩 d) :
    (gradedUnitRightLinear ν M).symm x ∈
      G.gradedIndGrading ν 0 (ExtTensor.grading 𝒩 (G.klrGrade 0)) d := by
  rw [gradedUnitRightLinear_symm_apply]
  have hu : unitGen (inductionRingHom k Γ ν 0) ∈ G.indBimodGrading ν 0 0 :=
    G.inductionMap_one_mem_klrGrade
  have ht := ExtTensor.tmul_mem_grading hx (SetLike.GradedOne.one_mem (A := G.klrGrade 0))
  simpa only [zero_add, add_zero] using tmul_mem_balancedGrading (M := GradedIndBimod k Γ ν 0) hu ht

end UnitModules

end Juxtapose

namespace GradingDatum

variable (G : GradingDatum Γ) {ν : I →₀ ℕ}

/-- The left induction unit as a scalar-linear isomorphism, semilinear for `castW`. -/
def indUnitLeftLinearEquiv (P : GProj (G.klrGrade ν)) :
    (G.indProj (GProj.regular (G.klrGrade 0)) P).carrier ≃ₗ[k] P.carrier :=
  gradedUnitLeftLinear ν P.carrier

/-- The right induction unit as a scalar-linear isomorphism, semilinear for `castW`. -/
def indUnitRightLinearEquiv (P : GProj (G.klrGrade ν)) :
    (G.indProj P (GProj.regular (G.klrGrade 0))).carrier ≃ₗ[k] P.carrier :=
  gradedUnitRightLinear ν P.carrier

theorem indUnitLeftLinearEquiv_smul (P : GProj (G.klrGrade ν))
    (b : WeightedKLRAlgebra k Γ (0 + ν))
    (x : (G.indProj (GProj.regular (G.klrGrade 0)) P).carrier) :
    G.indUnitLeftLinearEquiv P (b • x) =
      castW k Γ (zero_add ν) b • G.indUnitLeftLinearEquiv P x :=
  gradedUnitLeftLinear_smul ν P.carrier b x

theorem indUnitRightLinearEquiv_smul (P : GProj (G.klrGrade ν))
    (b : WeightedKLRAlgebra k Γ (ν + 0))
    (x : (G.indProj P (GProj.regular (G.klrGrade 0))).carrier) :
    G.indUnitRightLinearEquiv P (b • x) =
      castW k Γ (add_zero ν) b • G.indUnitRightLinearEquiv P x :=
  gradedUnitRightLinear_smul ν P.carrier b x

/-- The graded left unit of induction, with no grading shift. -/
def indUnitLeftGradedEquiv (P : GProj (G.klrGrade ν)) :
    (G.indProj (GProj.regular (G.klrGrade 0)) P).grading ≃ᵍ[k] P.grading :=
  (GradedEquiv.ofPreserves (ℳ := P.grading)
    (𝒩 := (G.indProj (GProj.regular (G.klrGrade 0)) P).grading)
    (G.indUnitLeftLinearEquiv P).symm (fun _ _ hx => gradedUnitLeftLinear_symm_mem_grading ν P.carrier G P.grading hx)).symm

/-- The graded right unit of induction, with no grading shift. -/
def indUnitRightGradedEquiv (P : GProj (G.klrGrade ν)) :
    (G.indProj P (GProj.regular (G.klrGrade 0))).grading ≃ᵍ[k] P.grading :=
  (GradedEquiv.ofPreserves (ℳ := P.grading)
    (𝒩 := (G.indProj P (GProj.regular (G.klrGrade 0))).grading)
    (G.indUnitRightLinearEquiv P).symm (fun _ _ hx => gradedUnitRightLinear_symm_mem_grading ν P.carrier G P.grading hx)).symm

/-- The regular class of the algebra of zero strands. -/
def K0one : K0 (G.klrGrade 0) := K0.of (GProj.regular (G.klrGrade 0))

/-- The regular zero-strand class is the left unit for graded induction. -/
theorem indK0_one_left (x : K0 (G.klrGrade ν)) :
    G.K0cast (zero_add ν) (G.indK0 0 ν G.K0one x) = x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0one, indK0_of]
    exact G.K0cast_of_linearEquiv _ _ _ (G.indUnitLeftLinearEquiv P)
      (G.indUnitLeftLinearEquiv_smul P)
      (fun _ _ hx => (G.indUnitLeftGradedEquiv P).map_mem hx)
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

/-- The regular zero-strand class is the right unit for graded induction. -/
theorem indK0_one_right (x : K0 (G.klrGrade ν)) :
    G.K0cast (add_zero ν) (G.indK0 ν 0 x G.K0one) = x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0one, indK0_of]
    exact G.K0cast_of_linearEquiv _ _ _ (G.indUnitRightLinearEquiv P)
      (G.indUnitRightLinearEquiv_smul P)
      (fun _ _ hx => (G.indUnitRightGradedEquiv P).map_mem hx)
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

end GradingDatum

end Categorification.WeightedKLR
