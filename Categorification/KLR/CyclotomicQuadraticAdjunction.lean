/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAdjunction

/-!
# An actual opposite cyclotomic adjunction: the quadratic rank-zero edge

For the actual cyclotomic KLR algebras at `β = 0` and `β + α_i`, with
`a i = X²`, we prove `restrictionFunctor ⊣ inductionFunctor`. These are the
original module functors of `CyclotomicAdjunction`, not an action transported
from a model category and not a relabelling of the ordinary adjunction.

Over any nontrivial commutative ground ring, and arbitrary KLR parameters Q,
the singleton quotient has basis `(1,x)`, `x² = 0`, and trace `tr(c+dx)=d`.
We prove the coefficient formula `tr(zw)=z₀w₁+z₁w₀`, both dual-basis identities,
and an explicit linear equivalence with the dual. This trace, not a Frobenius
hypothesis, constructs the opposite cap and cup on all actual modules:
`cap(z ⊗ n)=tr(z)n`, `cup(m)=1 ⊗ xm + x ⊗ m`.
Both triangles, naturality, the opposite Hom bijection, and the bundled
adjunction are proved.

In Kang–Kashiwara §4.2, E is restriction and F is induction. Thus this is the
E-left/F-right orientation required by Webster, Unfurling, categorical-action axiom
(KM1), on the highest-weight-two rank-zero edge (upper weight zero in type A1).
It does not establish KM1 for other ranks or cyclotomic polynomials, graded
shifts, or compatibility with the prescribed mixed maps. It does not complete
a Kac–Moody categorical action. Those remain separate open obligations.
-/

noncomputable section
universe u v w
namespace Categorification.KLR.KLRAlgebra.QuadraticTrace
open Polynomial
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k)
  (ha : a i = X ^ 2)
local notation "S" => CycKLR k Q a (Singleton.singleton i : Multiset I)

def dot : S := CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)

include ha in
omit [Nontrivial k] in
theorem dot_sq : dot Q i a * dot Q i a = 0 := by
  have h := CycKLR.mk_aeval_x_mul_e (Q := Q) (a := a)
    (default : Seq ({i} : Multiset I)) (by simp)
  have hi : (default : Seq ({i} : Multiset I)).lbl ⟨0, by simp⟩ = i :=
    Multiset.mem_singleton.mp ((default : Seq ({i} : Multiset I)).mem _)
  simpa [hi, ha, e_eq_one, dot, pow_two] using h

def coordinates : (Fin 2 → k) ≃ₗ[k] S :=
  (LinearEquiv.funCongrLeft k k (finCongr (show (a i).natDegree = 2 by simp [ha]))).trans
    (cyclotomicSingleFinEquiv Q i a (by rw [ha]; exact monic_X_pow 2))

theorem coordinates_apply (c : Fin 2 → k) :
    coordinates Q i a ha c = c 0 • (1 : S) + c 1 • dot Q i a := by
  unfold coordinates
  rw [LinearEquiv.trans_apply, cyclotomicSingleFinEquiv_apply]
  have hd : (a i).natDegree = 2 := by simp [ha]
  rw [← (finCongr hd.symm).sum_comp]
  simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, Fin.sum_univ_two, dot]

def constantCoeff : S →ₗ[k] k :=
  (LinearMap.proj (0 : Fin 2)).comp (coordinates Q i a ha).symm.toLinearMap

def trace : S →ₗ[k] k :=
  (LinearMap.proj (1 : Fin 2)).comp (coordinates Q i a ha).symm.toLinearMap

theorem expansion (z : S) :
    constantCoeff Q i a ha z • (1 : S) + trace Q i a ha z • dot Q i a = z := by
  exact (coordinates_apply Q i a ha _).symm.trans ((coordinates Q i a ha).apply_symm_apply z)

@[simp] theorem constantCoeff_coordinates (c : Fin 2 → k) :
    constantCoeff Q i a ha (coordinates Q i a ha c) = c 0 :=
  congrFun ((coordinates Q i a ha).symm_apply_apply c) 0

@[simp] theorem trace_coordinates (c : Fin 2 → k) :
    trace Q i a ha (coordinates Q i a ha c) = c 1 :=
  congrFun ((coordinates Q i a ha).symm_apply_apply c) 1

@[simp] theorem trace_one : trace Q i a ha (1 : S) = 0 := by
  have h := trace_coordinates Q i a ha ![1, 0]
  simpa [coordinates_apply] using h

@[simp] theorem trace_dot : trace Q i a ha (dot Q i a) = 1 := by
  have h := trace_coordinates Q i a ha ![0, 1]
  simpa [coordinates_apply] using h

@[simp] theorem constantCoeff_one : constantCoeff Q i a ha (1 : S) = 1 := by
  have h := constantCoeff_coordinates Q i a ha ![1, 0]
  simpa [coordinates_apply] using h

@[simp] theorem constantCoeff_dot : constantCoeff Q i a ha (dot Q i a) = 0 := by
  have h := constantCoeff_coordinates Q i a ha ![0, 1]
  simpa [coordinates_apply] using h

theorem trace_dot_mul (z : S) : trace Q i a ha (dot Q i a * z) = constantCoeff Q i a ha z := by
  conv_lhs => rw [← expansion Q i a ha z]
  simp [mul_add, dot_sq Q i a ha]

theorem trace_mul_dot (z : S) : trace Q i a ha (z * dot Q i a) = constantCoeff Q i a ha z := by
  conv_lhs => rw [← expansion Q i a ha z]
  simp [add_mul, dot_sq Q i a ha]

theorem dual_basis (z : S) :
    trace Q i a ha (dot Q i a * z) • (1 : S) + trace Q i a ha z • dot Q i a = z := by
  rw [trace_dot_mul, expansion]

theorem dual_basis_right (z : S) :
    trace Q i a ha (z * dot Q i a) • (1 : S) + trace Q i a ha z • dot Q i a = z := by
  rw [trace_mul_dot, expansion]

theorem trace_mul (z w : S) :
    trace Q i a ha (z * w) =
      constantCoeff Q i a ha z * trace Q i a ha w + trace Q i a ha z * constantCoeff Q i a ha w := by
  conv_lhs => rw [← expansion Q i a ha z]
  simp only [add_mul, smul_mul_assoc, one_mul, map_add, map_smul, trace_dot_mul, smul_eq_mul]

/-- The relative pairing is computed, not assumed. -/
def toDual : S →ₗ[k] Module.Dual k S :=
  LinearMap.mk₂ k (fun z w => trace Q i a ha (w * z))
    (fun z z' w => by simp [mul_add])
    (fun c z w => by simp)
    (fun z w w' => by simp [add_mul])
    (fun c z w => by simp)

/-- The inverse uses the explicitly proved dual bases `(1,x)` and `(x,1)`. -/
def fromDual : Module.Dual k S →ₗ[k] S where
  toFun f := f (dot Q i a) • (1 : S) + f 1 • dot Q i a
  map_add' f g := by simp only [LinearMap.add_apply, add_smul]; abel
  map_smul' c f := by simp only [LinearMap.smul_apply, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

theorem fromDual_toDual (z : S) : fromDual Q i a (toDual Q i a ha z) = z := by
  change trace Q i a ha (dot Q i a * z) • (1 : S) +
    trace Q i a ha (1 * z) • dot Q i a = z
  rw [one_mul, dual_basis]

theorem toDual_fromDual (f : Module.Dual k S) : toDual Q i a ha (fromDual Q i a f) = f := by
  ext z
  change trace Q i a ha (z * (f (dot Q i a) • 1 + f 1 • dot Q i a)) = f z
  rw [mul_add, map_add]
  simp only [mul_smul_comm, mul_one, map_smul, trace_mul_dot, smul_eq_mul]
  conv_rhs => rw [← expansion Q i a ha z]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

def dualEquiv : S ≃ₗ[k] Module.Dual k S :=
  LinearEquiv.ofLinearMap (toDual Q i a ha) (fromDual Q i a)
    (LinearMap.ext (toDual_fromDual Q i a ha)) (LinearMap.ext (fromDual_toDual Q i a ha))

theorem trace_nondegenerate (z : S) (hz : ∀ w, trace Q i a ha (w * z) = 0) : z = 0 := by
  have h := dual_basis Q i a ha z
  rw [hz, show trace Q i a ha z = 0 by simpa using hz 1, zero_smul, zero_smul, zero_add] at h
  exact h.symm

end Categorification.KLR.KLRAlgebra.QuadraticTrace

namespace Categorification.KLR.KLRAlgebra.ZeroQuadratic
open Polynomial MulOpposite AbsentColour
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k)
  (ha : a i = X ^ 2)
local notation "R" => CycKLR k Q a (0 : Multiset I)
local notation "U" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + 0)
local notation "S" => CycKLR k Q a (Singleton.singleton i : Multiset I)

def upperEquiv : U ≃ₐ[k] S where
  toFun z := by simpa only [add_zero] using z
  invFun z := by simpa only [add_zero] using z
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def dot : U := (upperEquiv Q i a).symm (QuadraticTrace.dot Q i a)

def trace : U →ₗ[k] k := (QuadraticTrace.trace Q i a ha).comp (upperEquiv Q i a).toLinearMap

def constantCoeff : U →ₗ[k] k :=
  (QuadraticTrace.constantCoeff Q i a ha).comp (upperEquiv Q i a).toLinearMap

theorem expansion (z : U) : constantCoeff Q i a ha z • (1 : U) + trace Q i a ha z • dot Q i a = z := by
  apply (upperEquiv Q i a).injective
  simpa only [constantCoeff, trace, dot, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_add, map_smul, map_one, AlgEquiv.apply_symm_apply] using
    QuadraticTrace.expansion Q i a ha (upperEquiv Q i a z)

include ha in
omit [Nontrivial k] in
theorem dot_sq : dot Q i a * dot Q i a = 0 := by
  apply (upperEquiv Q i a).injective
  simpa only [dot, map_mul, map_zero, AlgEquiv.apply_symm_apply] using QuadraticTrace.dot_sq Q i a ha

@[simp] theorem trace_one : trace Q i a ha (1 : U) = 0 := by
  simp only [trace, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one, QuadraticTrace.trace_one]
@[simp] theorem trace_dot : trace Q i a ha (dot Q i a) = 1 := by
  simp only [trace, dot, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply, QuadraticTrace.trace_dot]

theorem trace_mul_dot (z : U) : trace Q i a ha (z * dot Q i a) = constantCoeff Q i a ha z := by
  simpa only [trace, dot, constantCoeff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, AlgEquiv.apply_symm_apply] using QuadraticTrace.trace_mul_dot Q i a ha (upperEquiv Q i a z)

omit [Nontrivial k] in
theorem lastIdem_eq_one : lastIdem Q i a 0 = 1 := by
  rw [lastIdem, cyclotomicLast_one, cL_zero_one, map_one]

/-- The actual one-sided corner is the full upper algebra at rank zero. -/
def corner (z : U) : IndCorner Q i a 0 := ⟨z, by
  change z * lastIdem Q i a 0 = z
  rw [lastIdem_eq_one, mul_one]⟩

theorem corner_expansion (z : IndCorner Q i a 0) :
    constantCoeff Q i a ha z.1 • corner Q i a 1 + trace Q i a ha z.1 • corner Q i a (dot Q i a) = z :=
  Subtype.ext (expansion Q i a ha z.1)

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (CycKLR k Q a (0 : Multiset I)) N]
  [IsScalarTower k (CycKLR k Q a (0 : Multiset I)) N]

/-- The counit coefficient on the actual induction tensor. -/
def capTensor : AbsentColour.Ind Q i a 0 N →ₗ[k] N :=
  BalancedTensor.lift
    (LinearMap.mk₂ k (fun z n => trace Q i a ha z.1 • n)
      (fun z w n => by simp only [Submodule.coe_add, map_add, add_smul])
      (fun c z n => by
        change trace Q i a ha (c • z.1) • n = c • (trace Q i a ha z.1 • n)
        rw [map_smul, smul_eq_mul, smul_smul])
      (fun z n n' => smul_add _ _ _)
      (fun c z n => smul_comm _ _ _))
    (fun z r n => by
      change trace Q i a ha (z.1 * cyclotomicLast Q i a 0 r) • n = trace Q i a ha z.1 • (r • n)
      rw [cyclotomicLast_zero_eq, mul_smul_comm, mul_one, map_smul]
      have hr : r = cyclotomicZeroEquiv Q a r • (1 : R) := by
        apply (cyclotomicZeroEquiv Q a).injective
        simp
      conv_rhs => rw [hr]
      simp only [smul_assoc, one_smul, smul_eq_mul, smul_smul, mul_comm])

@[simp] theorem capTensor_tmul (z : IndCorner Q i a 0) (n : N) :
    capTensor Q i a ha (BalancedTensor.tmul z n) = trace Q i a ha z.1 • n := rfl

omit [Nontrivial k] in
theorem lower_smul (r : R) (n : N) : r • n = cyclotomicZeroEquiv Q a r • n := by
  have hr : r = cyclotomicZeroEquiv Q a r • (1 : R) := by
    apply (cyclotomicZeroEquiv Q a).injective
    simp
  conv_lhs => rw [hr]
  rw [smul_assoc, one_smul]

/-- The actual cap `E F N → N`, linear over the lower cyclotomic algebra. -/
def cap : AbsentColour.Res Q i a 0 (AbsentColour.Ind Q i a 0 N) →ₗ[R] N where
  toFun z := capTensor Q i a ha z.1
  map_add' z w := (capTensor Q i a ha).map_add z.1 w.1
  map_smul' r z := by
    rw [lower_smul Q a r z, RingHom.id_apply, lower_smul Q a r]
    change capTensor Q i a ha (cyclotomicZeroEquiv Q a r • z.1) = _
    exact (capTensor Q i a ha).map_smul _ _

variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a (({i} : Multiset I) + 0)) M]
  [IsScalarTower k (CycKLR k Q a (({i} : Multiset I) + 0)) M]

/-- At rank zero every vector lies in the original restriction summand. -/
def resOf : M →ₗ[k] AbsentColour.Res Q i a 0 M where
  toFun m := ⟨m, by change lastIdem Q i a 0 • m = m; rw [lastIdem_eq_one, one_smul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Nontrivial k] in
@[simp] theorem resOf_val (m : M) : (resOf Q i a m).1 = m := rfl
omit [Nontrivial k] in
@[simp] theorem resOf_coe (m : AbsentColour.Res Q i a 0 M) : resOf Q i a m.1 = m := rfl

omit [Nontrivial k] in
theorem dot_corner_one : dot Q i a • corner Q i a 1 = corner Q i a (dot Q i a) :=
  Subtype.ext (mul_one _)

include ha in
omit [Nontrivial k] in
theorem dot_corner_dot : dot Q i a • corner Q i a (dot Q i a) = 0 :=
  Subtype.ext (dot_sq Q i a ha)

/-- The cup `m ↦ 1 ⊗ x m + x ⊗ m`, in the original induction tensor. -/
def cupLinear : M →ₗ[k] AbsentColour.Ind Q i a 0 (AbsentColour.Res Q i a 0 M) where
  toFun m := BalancedTensor.tmul (corner Q i a 1) (resOf Q i a (dot Q i a • m)) +
    BalancedTensor.tmul (corner Q i a (dot Q i a)) (resOf Q i a m)
  map_add' m n := by
    simp only [smul_add, map_add, BalancedTensor.tmul_add]; abel
  map_smul' c m := by
    simp only [smul_comm (dot Q i a) c m, map_smul, BalancedTensor.tmul_smul, smul_add,
      RingHom.id_apply]

include ha in
omit [Nontrivial k] in
theorem cupLinear_dot (m : M) : cupLinear Q i a (dot Q i a • m) = dot Q i a • cupLinear Q i a m := by
  change BalancedTensor.tmul _ (resOf Q i a (dot Q i a • dot Q i a • m)) +
    BalancedTensor.tmul _ (resOf Q i a (dot Q i a • m)) = _
  rw [← mul_smul, dot_sq Q i a ha, zero_smul, map_zero, BalancedTensor.tmul_zero, zero_add]
  simp only [cupLinear, LinearMap.coe_mk, AddHom.coe_mk, smul_add, BalancedTensor.smul_tmul',
    dot_corner_one, dot_corner_dot Q i a ha, BalancedTensor.zero_tmul, add_zero]

/-- The cup is linear over the actual upper cyclotomic algebra. -/
def cup : M →ₗ[U] AbsentColour.Ind Q i a 0 (AbsentColour.Res Q i a 0 M) where
  toFun := cupLinear Q i a
  map_add' := (cupLinear Q i a).map_add
  map_smul' z m := by
    change cupLinear Q i a (z • m) = z • cupLinear Q i a m
    rw [← expansion Q i a ha z]
    simp only [add_smul, smul_assoc, one_smul, map_add, map_smul, cupLinear_dot Q i a ha]

/-- One triangle on the original restriction module. -/
theorem cap_cup (m : AbsentColour.Res Q i a 0 M) :
    cap Q i a ha (AbsentColour.resMap Q i a 0 M (cup Q i a ha) m) = m := by
  change capTensor Q i a ha (cupLinear Q i a m.1) = m
  simp only [cupLinear, LinearMap.coe_mk, AddHom.coe_mk, map_add, capTensor_tmul, corner,
    trace_one, trace_dot, zero_smul, one_smul, zero_add, resOf_coe]

theorem trace_dot_mul (z : U) : trace Q i a ha (dot Q i a * z) = constantCoeff Q i a ha z := by
  simpa only [trace, dot, constantCoeff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, AlgEquiv.apply_symm_apply] using QuadraticTrace.trace_dot_mul Q i a ha (upperEquiv Q i a z)

@[simp] theorem cup_apply (m : M) :
    cup Q i a ha m = BalancedTensor.tmul (corner Q i a 1) (resOf Q i a (dot Q i a • m)) +
      BalancedTensor.tmul (corner Q i a (dot Q i a)) (resOf Q i a m) := rfl

@[simp] theorem cap_resOf_tmul (z : IndCorner Q i a 0) (n : N) :
    cap Q i a ha (resOf Q i a (BalancedTensor.tmul z n)) = trace Q i a ha z.1 • n := rfl

theorem cap_resOf_dot_tmul (z : IndCorner Q i a 0) (n : N) :
    cap Q i a ha (resOf Q i a (dot Q i a • BalancedTensor.tmul z n)) = constantCoeff Q i a ha z.1 • n := by
  change capTensor Q i a ha (dot Q i a • BalancedTensor.tmul z n) = _
  rw [BalancedTensor.smul_tmul', capTensor_tmul]
  change trace Q i a ha (dot Q i a * z.1) • n = _
  rw [trace_dot_mul]

theorem cup_cap_tmul (z : IndCorner Q i a 0) (n : N) :
    AbsentColour.indMap Q i a 0 _ (cap Q i a ha) (cup Q i a ha (BalancedTensor.tmul z n)) =
      BalancedTensor.tmul z n := by
  simp only [cup_apply, AbsentColour.indMap, map_add, BalancedTensor.mapRight_tmul,
    cap_resOf_tmul, cap_resOf_dot_tmul]
  rw [BalancedTensor.tmul_smul, BalancedTensor.tmul_smul,
    ← BalancedTensor.smul_tmul, ← BalancedTensor.smul_tmul, ← BalancedTensor.add_tmul,
    corner_expansion]

/-- The other triangle, on the original induction tensor. -/
theorem cup_cap (t : AbsentColour.Ind Q i a 0 N) :
    AbsentColour.indMap Q i a 0 _ (cap Q i a ha) (cup Q i a ha t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t u ht hu => rw [map_add, map_add, ht, hu]
  | tmul z n => exact cup_cap_tmul Q i a ha z n

variable {M' : Type*} [AddCommGroup M'] [Module k M']
  [Module (CycKLR k Q a (({i} : Multiset I) + 0)) M']
  [IsScalarTower k (CycKLR k Q a (({i} : Multiset I) + 0)) M']

omit [Nontrivial k] in
theorem resMap_resOf (f : M →ₗ[U] M') (m : M) :
    AbsentColour.resMap Q i a 0 M f (resOf Q i a m) = resOf Q i a (f m) := rfl

theorem cup_natural (f : M →ₗ[U] M') (m : M) :
    AbsentColour.indMap Q i a 0 _ (AbsentColour.resMap Q i a 0 M f) (cup Q i a ha m) =
      cup Q i a ha (f m) := by
  change BalancedTensor.mapRight _ (cupLinear Q i a m) = cupLinear Q i a (f m)
  simp only [cupLinear, LinearMap.coe_mk, AddHom.coe_mk, map_add, BalancedTensor.mapRight_tmul,
    resMap_resOf, map_smul]

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (CycKLR k Q a (0 : Multiset I)) N']
  [IsScalarTower k (CycKLR k Q a (0 : Multiset I)) N']

theorem capTensor_natural (f : N →ₗ[R] N') (t : AbsentColour.Ind Q i a 0 N) :
    capTensor Q i a ha (AbsentColour.indMap Q i a 0 N f t) = f (capTensor Q i a ha t) := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add t u ht hu => rw [map_add, map_add, map_add, map_add, ht, hu]
  | tmul z n =>
    change capTensor Q i a ha (BalancedTensor.mapRight f (BalancedTensor.tmul z n)) = _
    rw [BalancedTensor.mapRight_tmul, capTensor_tmul, capTensor_tmul]
    exact ((f.restrictScalars k).map_smul _ _).symm

/-- Opposite Frobenius reciprocity, constructed from the proved cup. -/
def homToInd (f : AbsentColour.Res Q i a 0 M →ₗ[R] N) : M →ₗ[U] AbsentColour.Ind Q i a 0 N :=
  (AbsentColour.indMap Q i a 0 _ f).comp (cup Q i a ha)

theorem homToInd_apply (f : AbsentColour.Res Q i a 0 M →ₗ[R] N) (m : M) :
    homToInd Q i a ha f m =
      BalancedTensor.tmul (corner Q i a 1) (f (resOf Q i a (dot Q i a • m))) +
      BalancedTensor.tmul (corner Q i a (dot Q i a)) (f (resOf Q i a m)) := by
  simp only [homToInd, LinearMap.comp_apply, cup_apply, AbsentColour.indMap,
    map_add, BalancedTensor.mapRight_tmul]

/-- Opposite Frobenius reciprocity in the cap direction. -/
def homFromInd (g : M →ₗ[U] AbsentColour.Ind Q i a 0 N) : AbsentColour.Res Q i a 0 M →ₗ[R] N :=
  (cap Q i a ha).comp (AbsentColour.resMap Q i a 0 M g)

theorem homFromInd_homToInd (f : AbsentColour.Res Q i a 0 M →ₗ[R] N) :
    homFromInd Q i a ha (homToInd Q i a ha f) = f := by
  ext m
  change capTensor Q i a ha (AbsentColour.indMap Q i a 0 _ f (cup Q i a ha m.1)) = f m
  rw [capTensor_natural]
  exact congrArg f (cap_cup Q i a ha m)

theorem homToInd_homFromInd (g : M →ₗ[U] AbsentColour.Ind Q i a 0 N) :
    homToInd Q i a ha (homFromInd Q i a ha g) = g := by
  ext m
  change BalancedTensor.mapRight ((cap Q i a ha).comp (AbsentColour.resMap Q i a 0 M g))
    (cup Q i a ha m) = g m
  rw [BalancedTensor.mapRight_comp]
  change AbsentColour.indMap Q i a 0 _ (cap Q i a ha)
    (AbsentColour.indMap Q i a 0 _ (AbsentColour.resMap Q i a 0 M g) (cup Q i a ha m)) = g m
  rw [cup_natural, cup_cap]

theorem homToInd_natural_right (f : AbsentColour.Res Q i a 0 M →ₗ[R] N) (g : N →ₗ[R] N') :
    homToInd Q i a ha (g.comp f) = (AbsentColour.indMap Q i a 0 N g).comp (homToInd Q i a ha f) := by
  ext m
  exact congrArg (fun h => h (cup Q i a ha m)) (BalancedTensor.mapRight_comp f g)

section Bundled
open CategoryTheory
open scoped ModuleCat.Algebra

/-- Genuine opposite adjunction at rank zero and `a_i = X²`: restriction is left,
induction is right. No relative Frobenius identity is a hypothesis. -/
def oppositeAdjunction : restrictionFunctor.{u, v, w} Q i a 0 ⊣ inductionFunctor Q i a 0 :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun f => ModuleCat.ofHom (homToInd Q i a ha f.hom)
          invFun := fun g => ModuleCat.ofHom (homFromInd Q i a ha g.hom)
          left_inv := fun f => ModuleCat.hom_ext (homFromInd_homToInd Q i a ha f.hom)
          right_inv := fun g => ModuleCat.hom_ext (homToInd_homFromInd Q i a ha g.hom) }
      homEquiv_naturality_left_symm := fun f g => by ext m; rfl
      homEquiv_naturality_right := fun f g =>
        ModuleCat.hom_ext (homToInd_natural_right Q i a ha f.hom g.hom) }

/-- The bundled unit is exactly the explicit opposite cup. -/
@[simp] theorem oppositeAdjunction_unit (M : ModuleCat.{max u v w} U) (m : M) :
    (oppositeAdjunction Q i a ha).unit.app M m =
      BalancedTensor.tmul (k := k) (B := U) (A := R) (N := (restrictionFunctor Q i a 0).obj M)
        (corner Q i a 1) (resOf Q i a (dot Q i a • m)) +
      BalancedTensor.tmul (k := k) (B := U) (A := R) (N := (restrictionFunctor Q i a 0).obj M)
        (corner Q i a (dot Q i a)) (resOf Q i a m) := by
  exact @homToInd_apply I _ k _ _ Q i a ha ((restrictionFunctor Q i a 0).obj M)
    inferInstance ModuleCat.Algebra.instModuleCarrier inferInstance inferInstance
    M inferInstance ModuleCat.Algebra.instModuleCarrier inferInstance inferInstance
    LinearMap.id m

/-- The bundled counit is exactly the trace coefficient on actual tensors. -/
@[simp] theorem oppositeAdjunction_counit (N : ModuleCat.{max u v w} R)
    (z : IndCorner Q i a 0) (n : N) :
    (oppositeAdjunction Q i a ha).counit.app N (resOf Q i a (BalancedTensor.tmul z n)) =
      trace Q i a ha z.1 • n := rfl

end Bundled
end Categorification.KLR.KLRAlgebra.ZeroQuadratic
