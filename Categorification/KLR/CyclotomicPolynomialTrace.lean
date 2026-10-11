/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.MonicTrace
import Categorification.KLR.CyclotomicAbsentColour

/-!
# Polynomial trace and duality on every singleton cyclotomic KLR algebra

For any commutative ground ring, arbitrary KLR parameters, and any monic `a i`,
we transfer the uniform monic remainder trace to the actual algebra
`CycKLR k Q a {i}`. `dot` is the actual singleton dot and `eval` is the actual
cyclotomic quotient of polynomial evaluation. The trace-dual family is recursive,
not assumed. Both reconstructions and an explicit equivalence with the linear
dual are proved, including degree zero and ground rings with zero divisors.

This supplies the entire polynomial trace prerequisite for the rank-zero edge,
not another fixed-degree example. It does not construct the opposite cap/cup
on modules, prove a general nonzero-beta relative trace, identify prescribed
mixed maps, or address grading. In the conventions of Kang–Kashiwara §4.2,
restriction is E and induction is F; this file does not relabel F-left/E-right
as the E-left/F-right adjunction required by Webster's (KM1).
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.PolynomialTrace
open Polynomial
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k)
  (ha : (a i).Monic)
local notation "S" => CycKLR k Q a (Singleton.singleton i : Multiset I)

def eval : Polynomial k →ₐ[k] S :=
  (CycKLR.mk k Q a {i}).comp (singleEquiv k Q i).symm.toAlgHom

def dot : S := CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)

@[simp] theorem eval_X : eval Q i a X = dot Q i a := by
  simp only [eval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, singleEquiv_symm_X, dot]

@[simp] theorem eval_C (c : k) : eval Q i a (C c) = algebraMap k S c :=
  (eval Q i a).commutes c

theorem eval_eq (p : Polynomial k) :
    eval Q i a p = (cyclotomicSingleEquiv Q i a).symm (AdjoinRoot.mk (a i) p) :=
  (cyclotomicRootToSingle_mk Q i a p).symm

theorem eval_surjective : Function.Surjective (eval Q i a) := by
  intro z
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective ((cyclotomicSingleEquiv Q i a) z)
  exact ⟨p, by rw [eval_eq, hp, AlgEquiv.symm_apply_apply]⟩

def trace : S →ₗ[k] k :=
  (Polynomial.lcoeff k ((a i).natDegree - 1)).comp
    ((AdjoinRoot.modByMonicHom ha).comp (cyclotomicSingleEquiv Q i a).toLinearMap)

@[simp] theorem trace_eval (p : Polynomial k) :
    trace Q i a ha (eval Q i a p) = MonicTrace.trace (a i) p := by
  change (AdjoinRoot.modByMonicHom ha ((cyclotomicSingleEquiv Q i a) (eval Q i a p))).coeff _ = _
  rw [eval_eq, AlgEquiv.apply_symm_apply]
  rfl

def dual (s : ℕ) : S := eval Q i a (MonicTrace.dual (a i) s)

@[simp] theorem dual_zero : dual Q i a 0 = 1 := by simp [dual, MonicTrace.dual]

theorem dual_succ (s : ℕ) : dual Q i a (s + 1) =
    dual Q i a s * dot Q i a + algebraMap k S ((a i).coeff ((a i).natDegree - 1 - s)) := by
  simp [dual, MonicTrace.dual, map_add, map_mul]

theorem mul_comm (z w : S) : z * w = w * z := by
  apply (cyclotomicSingleEquiv Q i a).injective
  simp only [map_mul, _root_.mul_comm]

theorem dual_basis (z : S) :
    ∑ j : Fin (a i).natDegree,
      trace Q i a ha (dual Q i a ((a i).natDegree - 1 - j) * z) • dot Q i a ^ (j : ℕ) = z := by
  obtain ⟨p, rfl⟩ := eval_surjective Q i a z
  have h := congrArg (eval Q i a)
    (MonicTrace.dual_basis (a i) ha (fun q => Commute.all q (a i)) p)
  have he : eval Q i a (p %ₘ a i) = eval Q i a p := by
    rw [eval_eq, eval_eq]
    congr 1
    exact AdjoinRoot.mk_leftInverse ha (AdjoinRoot.mk (a i) p)
  rw [he] at h
  simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, eval_X,
    eval_C, ← Algebra.smul_def] at h
  simpa only [dual, ← map_mul, trace_eval] using h

theorem dual_basis_right (z : S) :
    ∑ j : Fin (a i).natDegree,
      trace Q i a ha (z * dual Q i a ((a i).natDegree - 1 - j)) • dot Q i a ^ (j : ℕ) = z := by
  simp_rw [mul_comm Q i a z]
  exact dual_basis Q i a ha z

def toDual : S →ₗ[k] Module.Dual k S :=
  LinearMap.mk₂ k (fun z w => trace Q i a ha (w * z))
    (fun z z' w => by simp [mul_add])
    (fun c z w => by simp)
    (fun z w w' => by simp [add_mul])
    (fun c z w => by simp)

def fromDual : Module.Dual k S →ₗ[k] S where
  toFun f := ∑ j : Fin (a i).natDegree, f (dot Q i a ^ (j : ℕ)) • dual Q i a ((a i).natDegree - 1 - j)
  map_add' f g := by simp only [LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp only [LinearMap.smul_apply, RingHom.id_apply, smul_smul, Finset.smul_sum, smul_eq_mul]

theorem toDual_injective : Function.Injective (toDual Q i a ha) := by
  intro z w h
  have he (t : S) : trace Q i a ha (t * z) = trace Q i a ha (t * w) :=
    DFunLike.congr_fun h t
  rw [← dual_basis Q i a ha z, ← dual_basis Q i a ha w]
  simp_rw [he]

theorem toDual_fromDual (f : Module.Dual k S) : toDual Q i a ha (fromDual Q i a f) = f := by
  ext z
  change trace Q i a ha (z * ∑ j : Fin (a i).natDegree,
    f (dot Q i a ^ (j : ℕ)) • dual Q i a ((a i).natDegree - 1 - j)) = f z
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, smul_eq_mul]
  conv_rhs => rw [← dual_basis_right Q i a ha z]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact _root_.mul_comm _ _

theorem fromDual_toDual (z : S) : fromDual Q i a (toDual Q i a ha z) = z := by
  apply toDual_injective Q i a ha
  exact toDual_fromDual Q i a ha (toDual Q i a ha z)

def dualEquiv : S ≃ₗ[k] Module.Dual k S :=
  LinearEquiv.ofLinearMap (toDual Q i a ha) (fromDual Q i a)
    (LinearMap.ext (toDual_fromDual Q i a ha)) (LinearMap.ext (fromDual_toDual Q i a ha))

/-- The other dual-basis identity, now obtained from the proved duality equivalence. -/
theorem dual_basis_swapped (z : S) :
    ∑ j : Fin (a i).natDegree,
      trace Q i a ha (dot Q i a ^ (j : ℕ) * z) • dual Q i a ((a i).natDegree - 1 - j) = z :=
  fromDual_toDual Q i a ha z

theorem trace_nondegenerate (z : S) (hz : ∀ w, trace Q i a ha (w * z) = 0) : z = 0 := by
  rw [← dual_basis Q i a ha z]
  simp only [hz, zero_smul, Finset.sum_const_zero]

end Categorification.KLR.KLRAlgebra.PolynomialTrace
