/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRepresentation
import Categorification.KLR.CyclotomicIntegrable
import LieLean.Algebra.QuantumGroup.HighestWeightMaps

/-!
# The irreducible highest-weight module on cyclotomic projectives

Kang–Kashiwara, arXiv:1102.4677v4, §6, Theorem 6.2, projective side after
scalar extension. The empty projective satisfies the defining highest-weight
power relations. The resulting module map is injective by simplicity and
surjective by generation under induction. We use LieLean’s highest-weight
presentation for a finite simple-root index set and an X-regular root datum.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot KLGamma LieLean
open LieLean.QuantumGroup
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (Λ : I → ℕ) {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest) (hP : IsRouquierQ C Q)

local notation "G" => hP.gradingDatum
local notation "R" => projectiveRootDatum RD
local notation "λ₀" => RD.pair.flip highest
local notation "M" => projectiveK0Q G Λ
local notation "U" => LieLean.QuantumGroup R v
local notation "V" => IrreducibleModule R v λ₀
local notation "B" => Module.End.baseChangeHom LP L (projectiveK0 G Λ)
local notation "w" => projectiveVacuum G Λ

private theorem lowerQ_pow_vacuum (i : I) : (B (lower G Λ i) ^ (Λ i + 1)) w = 0 := by
  rw [← map_pow, projectiveVacuum_eq]
  change (1 : L) ⊗ₜ[LP] (lower G Λ i ^ (Λ i + 1)) (DirectSum.lof LP _ _ 0 _) = 0
  rw [lower_pow_vacuum_eq_zero, TensorProduct.tmul_zero]

variable [Finite I] (hR : (projectiveRootDatum RD).IsXRegular)

local notation "ρ" => projectiveRepresentationX Λ RD highest hΛ hP
local notation "vΛ" => IrreducibleModule.hwv R v λ₀

include hR in
private theorem exists_highestWeightEquiv :
    ∃ e : M ≃ₗ[L] V, e w = IrreducibleModule.hwv R v λ₀ ∧
      ∀ (u : U) (x : M), e (ρ u x) = u • e x := by
  let : Module U M := Module.compHom M (ρ).toRingHom
  let : IsScalarTower L U M := ⟨fun c u x => by
    change ρ (c • u) x = c • ρ u x
    rw [map_smul, LinearMap.smul_apply]⟩
  have hv := pow_ne_one_of_transcendental' LusztigF.transcendental_ratFunc_X
  have hdom (i : I) : 0 ≤ λ₀ ((R).coroot i) := by
    change 0 ≤ RD.pair (RD.iY i) highest
    rw [← hΛ i]
    exact Nat.cast_nonneg _
  have hweight : w ∈ weightSpace R v M λ₀ := by
    intro y
    exact projectiveRepresentationX_K_vacuum Λ RD highest hΛ hP y
  have hE (i : I) : E R v i • w = 0 := by
    change ρ (E R v i) w = 0
    rw [projectiveRepresentationX_E]
    exact raiseQ_vacuum G Λ hP.klrSymm hP.polyInY_leading i
  have hF (i : I) : F R v i ^ ((λ₀ ((R).coroot i)).toNat + 1) • w = 0 := by
    change ρ (F R v i ^ ((RD.pair (RD.iY i) highest).toNat + 1)) w = 0
    rw [← hΛ i, Int.toNat_natCast, map_pow, projectiveRepresentationX_F, lowerQ_pow_vacuum]
  let j : V →ₗ[U] M :=
    IrreducibleModule.liftOfFPow LusztigF.transcendental_ratFunc_X hR hv hdom w hweight hE hF
  have hj : j (IrreducibleModule.hwv R v λ₀) = w := IrreducibleModule.liftOfFPow_hwv ..
  have := IrreducibleModule.isSimpleModule hR hv λ₀
  have hji : Function.Injective j := LinearMap.injective_of_ne_zero fun h => projectiveVacuum_ne_zero G Λ
    (by rw [← hj, h, LinearMap.zero_apply])
  have hjs : Function.Surjective j := by
    apply (LinearMap.range_eq_top (f := j.restrictScalars L)).mp
    apply eq_top_of_lower_stable hP Λ
    · exact ⟨_, hj⟩
    · rintro i _ ⟨x, rfl⟩
      refine ⟨F R v i • x, ?_⟩
      change j (F R v i • x) = _
      rw [map_smul]
      change ρ (F R v i) (j x) = B (lower G Λ i) (j x)
      rw [projectiveRepresentationX_F]
  let e := (LinearEquiv.ofBijective j ⟨hji, hjs⟩).symm
  refine ⟨e.restrictScalars L, ?_, fun u x => e.map_smul u x⟩
  exact (e.symm_apply_eq.mp hj).symm

/-- The rational projective highest-weight isomorphism of Kang–Kashiwara,
arXiv:1102.4677v4, §6, Theorem 6.2. The quantum group uses the parameter
`RatFunc.X`, and the grading shift acts by its inverse. -/
def projectiveHighestWeightEquiv : M ≃ₗ[L] V :=
  (exists_highestWeightEquiv Λ RD highest hΛ hP hR).choose

@[simp] theorem projectiveHighestWeightEquiv_vacuum :
    projectiveHighestWeightEquiv Λ RD highest hΛ hP hR w = vΛ :=
  (exists_highestWeightEquiv Λ RD highest hΛ hP hR).choose_spec.1

/-- The highest-weight isomorphism intertwines the action of every quantum group element. -/
theorem projectiveHighestWeightEquiv_action (u : U) (x : M) :
    projectiveHighestWeightEquiv Λ RD highest hΛ hP hR (ρ u x) =
      u • projectiveHighestWeightEquiv Λ RD highest hΛ hP hR x :=
  (exists_highestWeightEquiv Λ RD highest hΛ hP hR).choose_spec.2 u x

/-- The highest-weight isomorphism as a linear equivalence over the quantum
group, with the source module structure induced by cyclotomic functors
(Kang–Kashiwara, arXiv:1102.4677v4, Theorem 6.2). -/
def projectiveQuantumModuleEquiv :
    letI : Module U M := Module.compHom M (ρ).toRingHom
    M ≃ₗ[U] V := by
  letI : Module U M := Module.compHom M (ρ).toRingHom
  let e := projectiveHighestWeightEquiv Λ RD highest hΛ hP hR
  exact { e.toEquiv with
    map_add' := e.map_add
    map_smul' := projectiveHighestWeightEquiv_action Λ RD highest hΛ hP hR }

@[simp] theorem projectiveHighestWeightEquiv_F (i : I) (x : M) :
    projectiveHighestWeightEquiv Λ RD highest hΛ hP hR (B (lower G Λ i) x) =
      F R v i • projectiveHighestWeightEquiv Λ RD highest hΛ hP hR x := by
  simpa only [projectiveRepresentationX_F] using
    projectiveHighestWeightEquiv_action Λ RD highest hΛ hP hR (F R v i) x

end Categorification.KLR.CycKLR
