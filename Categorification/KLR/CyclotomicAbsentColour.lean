/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDegree
import Categorification.KLR.CyclotomicProjective
import Categorification.KLR.Examples.Small
import Mathlib.RingTheory.AdjoinRoot

/-!
# Rank-zero cyclotomic commutator and absent-colour cuts

The rank-zero case of the dot-unit summands in Kang–Kashiwara, §5.2, is
`AbsentColour.zeroFinEquiv`: the actual two-cut corner is a finite family of
copies of `R^Λ(0)`. Its map is the canonical finite dot sum, with both
roundtrips and both canonical outer-action identities. It holds over any
commutative ring, for arbitrary parameters `Q`, assuming only that `a i` is
monic. Degree zero and zero quotients are included.

For arbitrary `β`, this file defines the actual last-colour inclusion, corner,
canonical outer actions, and finite dot-unit map. When `i ∉ β`, it proves the
vanishing of every lower positional colour cut and nonnegativity of the Cartan
weight under the parameter-degree conditions. Bijectivity of the dot-unit map
for nonzero `β` is not asserted here. No grading or functor is constructed.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open Polynomial
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k)

def cyclotomicZeroEquiv : CycKLR k Q a (0 : Multiset I) ≃ₐ[k] k :=
  AlgEquiv.ofAlgHom
    (CycKLR.lift (zeroEquiv I k Q).toAlgHom (fun s => by simp [cycElt]))
    (Algebra.ofId k _)
    (AlgHom.ext fun c => by simp)
    (CycKLR.algHom_ext (by
      ext r
      obtain ⟨c, rfl⟩ := (zeroEquiv I k Q).symm.surjective r
      simp [zeroEquiv_symm_apply]))

private theorem single_cycElt (s : Seq ({i} : Multiset I)) :
    cycElt Q a s = (singleEquiv k Q i).symm (a i) := by
  rw [cycElt_of_pos Q a s (by simp), e_eq_one, mul_one]
  have h : s.lbl ⟨0, by simp⟩ = i := Multiset.mem_singleton.mp (s.mem _)
  rw [h]
  rfl

private instance singleCommRing : CommRing (CycKLR k Q a ({i} : Multiset I)) where
  __ := (inferInstance : Ring (CycKLR k Q a ({i} : Multiset I)))
  mul_comm u v := by
      obtain ⟨u, rfl⟩ := CycKLR.mk_surjective u
      obtain ⟨v, rfl⟩ := CycKLR.mk_surjective v
      rw [← map_mul, ← map_mul]
      congr 1
      apply (singleEquiv k Q i).injective
      simp only [map_mul, mul_comm]

def cyclotomicSingleToRoot : CycKLR k Q a ({i} : Multiset I) →ₐ[k] AdjoinRoot (a i) :=
  CycKLR.lift ((aeval (AdjoinRoot.root (a i))).comp (singleEquiv k Q i).toAlgHom)
    (fun s => by
      rw [AlgHom.comp_apply, single_cycElt, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
        AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])

def cyclotomicRootToSingle : AdjoinRoot (a i) →ₐ[k] CycKLR k Q a ({i} : Multiset I) :=
  AdjoinRoot.liftAlgHom (a i) (Algebra.ofId k _)
    (CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)) (by
      change aeval (CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)) (a i) = 0
      rw [aeval_algHom_apply]
      have h := CycKLR.mk_cycElt (Q := Q) (a := a) (default : Seq ({i} : Multiset I))
      rw [single_cycElt] at h
      exact h)

theorem cyclotomicRootToSingle_mk (p : Polynomial k) :
    cyclotomicRootToSingle Q i a (AdjoinRoot.mk (a i) p) =
      CycKLR.mk k Q a {i} ((singleEquiv k Q i).symm p) := by
  change aeval (CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)) p = _
  rw [aeval_algHom_apply]
  rfl

def cyclotomicSingleEquiv : CycKLR k Q a ({i} : Multiset I) ≃ₐ[k] AdjoinRoot (a i) :=
  AlgEquiv.ofAlgHom (cyclotomicSingleToRoot Q i a) (cyclotomicRootToSingle Q i a)
    (by
      apply AlgHom.ext
      intro z
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
      rw [AlgHom.comp_apply, cyclotomicRootToSingle_mk]
      change CycKLR.lift _ _ (CycKLR.mk k Q a {i} _) = _
      rw [CycKLR.lift_mk, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
        AdjoinRoot.aeval_eq]
      rfl)
    (CycKLR.algHom_ext (by
      ext r
      change cyclotomicRootToSingle Q i a
        (CycKLR.lift _ _ (CycKLR.mk k Q a {i} r)) = _
      rw [CycKLR.lift_mk, AlgHom.comp_apply, AdjoinRoot.aeval_eq,
        cyclotomicRootToSingle_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
      rfl))

def cyclotomicSingleFinEquiv (ha : (a i).Monic) :
    (Fin (a i).natDegree → k) ≃ₗ[k] CycKLR k Q a ({i} : Multiset I) :=
  (AdjoinRoot.powerBasisAux' ha).equivFun.symm.trans
    (cyclotomicSingleEquiv Q i a).symm.toLinearEquiv

theorem cyclotomicSingleFinEquiv_apply (ha : (a i).Monic)
    (r : Fin (a i).natDegree → k) :
    cyclotomicSingleFinEquiv Q i a ha r =
      ∑ d : Fin (a i).natDegree, r d • (CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)) ^ (d : ℕ) := by
  change cyclotomicRootToSingle Q i a
    (AdjoinRoot.mk (a i) (∑ d : Fin (a i).natDegree, monomial (d : ℕ) (r d))) = _
  rw [cyclotomicRootToSingle_mk]
  simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
    show ∀ c, (singleEquiv k Q i).symm (C c) = algebraMap k _ c from
      fun c => (singleEquiv k Q i).symm.commutes c,
    singleEquiv_symm_X, AlgHom.commutes, Algebra.smul_def]

theorem cyclotomicSingleFinEquiv_inverse_forward (ha : (a i).Monic)
    (r : Fin (a i).natDegree → k) :
    (cyclotomicSingleFinEquiv Q i a ha).symm (cyclotomicSingleFinEquiv Q i a ha r) = r :=
  (cyclotomicSingleFinEquiv Q i a ha).symm_apply_apply r

theorem cyclotomicSingleFinEquiv_forward_inverse (ha : (a i).Monic)
    (z : CycKLR k Q a ({i} : Multiset I)) :
    cyclotomicSingleFinEquiv Q i a ha ((cyclotomicSingleFinEquiv Q i a ha).symm z) = z :=
  (cyclotomicSingleFinEquiv Q i a ha).apply_symm_apply z


namespace AbsentColour
open MulOpposite
variable (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "Rl" => CycKLR k Q a β
local notation "S" => CycKLR k Q a (Si + β)

/-- Last-strand concatenation descends through the actual cyclotomic ideal. -/
def cyclotomicLastLinear : Rl →ₗ[k] S :=
  (LinearMap.ker (CycKLR.mk k Q a β).toLinearMap).liftQ
    ((CycKLR.mk k Q a (Si + β)).toLinearMap.comp
      ({ toFun := cL Q i β
         map_add' := cL_add i β
         map_smul' := fun c r => cL_smul i β c r } : Rb →ₗ[k] KLRAlgebra k Q (Si + β)))
    (by
      intro r hr
      exact (CycKLR.mk_eq_zero_iff _).2
        (cL_mem_cycIdeal i β a ((CycKLR.mk_eq_zero_iff r).1 hr))) ∘ₗ
    ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
      CycKLR.mk_surjective).symm.toLinearMap

theorem cyclotomicLastLinear_mk (r : Rb) :
    cyclotomicLastLinear Q i a β (CycKLR.mk k Q a β r) =
      CycKLR.mk k Q a (Si + β) (cL Q i β r) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (CycKLR.mk k Q a β).toLinearMap CycKLR.mk_surjective r
  change ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
    CycKLR.mk_surjective).symm (CycKLR.mk k Q a β r) = _ at he
  rw [cyclotomicLastLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
  rfl

/-- The nonunital inclusion has the actual colour-cut idempotent as unit image. -/
def cyclotomicLast : Rl →ₙₐ[k] S where
  toFun := cyclotomicLastLinear Q i a β
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' r s := by
    obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
    obtain ⟨s, rfl⟩ := CycKLR.mk_surjective s
    rw [← map_mul, cyclotomicLastLinear_mk, cL_mul, map_mul,
      cyclotomicLastLinear_mk, cyclotomicLastLinear_mk]

@[simp] theorem cyclotomicLast_mk (r : Rb) :
    cyclotomicLast Q i a β (CycKLR.mk k Q a β r) =
      CycKLR.mk k Q a (Si + β) (cL Q i β r) := cyclotomicLastLinear_mk Q i a β r

theorem cyclotomicLast_one : cyclotomicLast Q i a β 1 =
    CycKLR.mk k Q a (Si + β) (cL Q i β 1) := by
  rw [← map_one (CycKLR.mk k Q a β), cyclotomicLast_mk]

/-- The actual two-cut last-colour corner, at arbitrary rank. -/
def cornerSub : Submodule k S where
  carrier := {z | CycKLR.mk k Q a (Si + β) (cL Q i β 1) * z = z ∧
    z * CycKLR.mk k Q a (Si + β) (cL Q i β 1) = z}
  zero_mem' := ⟨mul_zero _, zero_mul _⟩
  add_mem' hz hw := ⟨by rw [mul_add, hz.1, hw.1], by rw [add_mul, hz.2, hw.2]⟩
  smul_mem' c z hz := ⟨by rw [mul_smul_comm, hz.1], by rw [smul_mul_assoc, hz.2]⟩
abbrev Corner := ↥(cornerSub Q i a β)

instance cornerModule : Module Rl (Corner Q i a β) where
  smul r z := ⟨cyclotomicLast Q i a β r * z.1, by
    constructor
    · rw [← cyclotomicLast_one, ← mul_assoc, ← map_mul, one_mul]
    · rw [mul_assoc, z.2.2]⟩
  one_smul z := Subtype.ext (by
    change cyclotomicLast Q i a β 1 * z.1 = z.1
    rw [cyclotomicLast_one]
    exact z.2.1)
  mul_smul r s z := Subtype.ext (by
    change cyclotomicLast Q i a β (r * s) * z.1 =
      cyclotomicLast Q i a β r * (cyclotomicLast Q i a β s * z.1)
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (mul_zero _)
  smul_add r z w := Subtype.ext (mul_add _ _ _)
  add_smul r s z := Subtype.ext (by
    change cyclotomicLast Q i a β (r + s) * z.1 =
      cyclotomicLast Q i a β r * z.1 + cyclotomicLast Q i a β s * z.1
    rw [map_add, add_mul])
  zero_smul z := Subtype.ext (by change cyclotomicLast Q i a β 0*z.1 = 0; rw [map_zero, zero_mul])

instance cornerOpModule : Module Rlᵐᵒᵖ (Corner Q i a β) where
  smul r z := ⟨z.1 * cyclotomicLast Q i a β r.unop, by
    constructor
    · rw [← mul_assoc, z.2.1]
    · rw [← cyclotomicLast_one, mul_assoc, ← map_mul, mul_one]⟩
  one_smul z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i a β 1 = z.1
    rw [cyclotomicLast_one]
    exact z.2.2)
  mul_smul r s z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i a β (s.unop * r.unop) =
      (z.1 * cyclotomicLast Q i a β s.unop) * cyclotomicLast Q i a β r.unop
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (zero_mul _)
  smul_add r z w := Subtype.ext (add_mul _ _ _)
  add_smul r s z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i a β (r.unop + s.unop) =
      z.1 * cyclotomicLast Q i a β r.unop + z.1 * cyclotomicLast Q i a β s.unop
    rw [map_add, mul_add])
  zero_smul z := Subtype.ext (by change z.1*cyclotomicLast Q i a β 0 = 0; rw [map_zero, mul_zero])

instance cornerComm : SMulCommClass Rl Rlᵐᵒᵖ (Corner Q i a β) where
  smul_comm r s z := Subtype.ext (mul_assoc (cyclotomicLast Q i a β r) z.1 (cyclotomicLast Q i a β s.unop)).symm

instance cornerTower : IsScalarTower k Rl (Corner Q i a β) where
  smul_assoc c r z := Subtype.ext (by
    change cyclotomicLast Q i a β (c • r) * z.1 = c • (cyclotomicLast Q i a β r * z.1)
    rw [map_smul, smul_mul_assoc])

instance cornerOpTower : IsScalarTower k Rlᵐᵒᵖ (Corner Q i a β) where
  smul_assoc c r z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i a β (c • r.unop) = c • (z.1 * cyclotomicLast Q i a β r.unop)
    rw [map_smul, mul_smul_comm])

/-- The left action is actual multiplication by the descended last-strand inclusion. -/
theorem corner_smul_val (r : Rl) (z : Corner Q i a β) :
    ((r • z : Corner Q i a β) : S) = cyclotomicLast Q i a β r * (z : S) := rfl

/-- The right action is actual right multiplication, not transport along a decomposition. -/
theorem corner_op_smul_val (r : Rlᵐᵒᵖ) (z : Corner Q i a β) :
    ((r • z : Corner Q i a β) : S) = (z : S) * cyclotomicLast Q i a β r.unop := rfl

def dotUnitTerm (d : ℕ) : Rl →ₗ[k] Corner Q i a β where
  toFun r := ⟨cyclotomicLast Q i a β r *
    (CycKLR.mk k Q a (Si + β) (x ⟨Multiset.card β, lastPos_lt i β⟩)) ^ d *
    cyclotomicLast Q i a β 1, by
    constructor
    · rw [← cyclotomicLast_one, ← mul_assoc, ← mul_assoc, ← map_mul, one_mul]
    · rw [← cyclotomicLast_one, mul_assoc, mul_assoc, ← map_mul, one_mul, ← mul_assoc]⟩
  map_add' r s := Subtype.ext (by
    change cyclotomicLast Q i a β (r + s) * _ * _ = _ * _ * _ + _ * _ * _
    rw [map_add, add_mul, add_mul])
  map_smul' c r := Subtype.ext (by
    change cyclotomicLast Q i a β (c • r) * _ * _ = c • (_ * _ * _)
    rw [map_smul, smul_mul_assoc, smul_mul_assoc])

/-- The finite dot-unit map uses genuine quotient coefficients and both cuts. -/
def dotUnitSum (h : ℕ) : (Fin h → Rl) →ₗ[k] Corner Q i a β :=
  ∑ d : Fin h, (dotUnitTerm Q i a β d).comp (LinearMap.proj d)

theorem dotUnitSum_apply (h : ℕ) (r : Fin h → Rl) :
    (dotUnitSum Q i a β h r : S) =
      ∑ d : Fin h, cyclotomicLast Q i a β (r d) *
        (CycKLR.mk k Q a (Si + β) (x ⟨Multiset.card β, lastPos_lt i β⟩)) ^ (d : ℕ) *
        CycKLR.mk k Q a (Si + β) (cL Q i β 1) := by
  simp only [dotUnitSum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro d _
  change _ * _ * cyclotomicLast Q i a β 1 = _
  rw [cyclotomicLast_one]

theorem weight_nonneg_of_absent
    {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
    (hi : i ∉ β)
    (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
      -RD.pair (RD.iY i) (RD.iX j)) :
    0 ≤ RD.pair (RD.iY i) (Λ - (β.map RD.iX).sum) := by
  have h := degA_sub_count_eq_pair i β a RD Λ hΛ hdeg
  rw [Multiset.count_eq_zero.mpr hi, Nat.cast_zero, mul_zero, sub_zero] at h
  rw [← h]
  exact Nat.cast_nonneg _

/-- An absent colour has no idempotent at any position of the lower block. -/
theorem colour_cut_eq_zero (hi : i ∉ β) (p : Fin (Multiset.card β)) :
    (∑ s : Seq β, if s.lbl p = i then e s else 0 : KLRAlgebra k Q β) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [ite_eq_right]
  intro h
  exact hi (h ▸ s.mem p)

theorem cL_zero_one : cL Q i (0 : Multiset I) 1 = 1 := by
  rw [cL_one, Fintype.sum_unique]
  let : Unique (Seq (({i} : Multiset I) + 0)) :=
    Seq.uniqueOfForall (i := i) (fun j hj => by simpa using hj)
  exact e_eq_one _

def zeroCornerEquiv : Corner Q i a 0 ≃ₗ[k] CycKLR k Q a ({i} : Multiset I) where
  toFun z := by simpa only [add_zero] using z.1
  invFun z := ⟨by simpa only [add_zero] using z, by
    constructor <;> change _ * _ = _
    · rw [cL_zero_one, map_one, one_mul]
    · rw [cL_zero_one, map_one, mul_one]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem cyclotomicLast_zero_eq (r : CycKLR k Q a (0 : Multiset I)) :
    cyclotomicLast Q i a 0 r = (cyclotomicZeroEquiv Q a r) • 1 := by
  have hr : r = (cyclotomicZeroEquiv Q a r) • (1 : CycKLR k Q a 0) := by
    apply (cyclotomicZeroEquiv Q a).injective
    simp
  conv_lhs => rw [hr]
  rw [map_smul, cyclotomicLast_one, cL_zero_one, map_one]

theorem zeroCornerEquiv_dotUnitTerm (d : ℕ) (r : CycKLR k Q a (0 : Multiset I)) :
    zeroCornerEquiv Q i a (dotUnitTerm Q i a 0 d r) =
      (cyclotomicZeroEquiv Q a r) •
        (CycKLR.mk k Q a {i} (x ⟨0, by simp⟩)) ^ d := by
  change cast (congrArg (fun ν => CycKLR k Q a ν) (add_zero ({i} : Multiset I)))
    (cyclotomicLast Q i a 0 r *
      (CycKLR.mk k Q a (({i} : Multiset I) + 0)
        (x ⟨Multiset.card 0, lastPos_lt i 0⟩)) ^ d * cyclotomicLast Q i a 0 1) = _
  rw [cyclotomicLast_zero_eq, cyclotomicLast_zero_eq, map_one, one_smul,
    mul_one, smul_mul_assoc, one_mul]
  simp only [Multiset.card_zero]
  rfl

/-- The actual rank-zero coefficient algebra, not a substitute base field. -/
def zeroFinEquiv (ha : (a i).Monic) :
    (Fin (a i).natDegree → CycKLR k Q a (0 : Multiset I)) ≃ₗ[k] Corner Q i a 0 :=
  (LinearEquiv.piCongrRight fun _ => (cyclotomicZeroEquiv Q a).toLinearEquiv).trans
    ((cyclotomicSingleFinEquiv Q i a ha).trans (zeroCornerEquiv Q i a).symm)

/-- At rank zero the equivalence is exactly the canonical finite dot-unit sum. -/
theorem zeroFinEquiv_apply (ha : (a i).Monic)
    (r : Fin (a i).natDegree → CycKLR k Q a (0 : Multiset I)) :
    zeroFinEquiv Q i a ha r = dotUnitSum Q i a 0 (a i).natDegree r := by
  apply (zeroCornerEquiv Q i a).injective
  change zeroCornerEquiv Q i a ((zeroCornerEquiv Q i a).symm
    (cyclotomicSingleFinEquiv Q i a ha (fun d => cyclotomicZeroEquiv Q a (r d)))) = _
  rw [LinearEquiv.apply_symm_apply, cyclotomicSingleFinEquiv_apply]
  simp only [dotUnitSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    map_sum, zeroCornerEquiv_dotUnitTerm]

theorem zeroFinEquiv_inverse_forward (ha : (a i).Monic)
    (r : Fin (a i).natDegree → CycKLR k Q a (0 : Multiset I)) :
    (zeroFinEquiv Q i a ha).symm (dotUnitSum Q i a 0 (a i).natDegree r) = r := by
  rw [← zeroFinEquiv_apply]
  exact (zeroFinEquiv Q i a ha).symm_apply_apply r

theorem zeroFinEquiv_forward_inverse (ha : (a i).Monic) (z : Corner Q i a 0) :
    dotUnitSum Q i a 0 (a i).natDegree ((zeroFinEquiv Q i a ha).symm z) = z := by
  rw [← zeroFinEquiv_apply]
  exact (zeroFinEquiv Q i a ha).apply_symm_apply z

theorem zero_left_smul (r : CycKLR k Q a (0 : Multiset I)) (z : Corner Q i a 0) :
    r • z = (cyclotomicZeroEquiv Q a r) • z := by
  apply Subtype.ext
  change cyclotomicLast Q i a 0 r * z.1 = _
  rw [cyclotomicLast_zero_eq, smul_mul_assoc, one_mul]
  rfl

theorem zero_right_smul (r : CycKLR k Q a (0 : Multiset I)) (z : Corner Q i a 0) :
    op r • z = (cyclotomicZeroEquiv Q a r) • z := by
  apply Subtype.ext
  change z.1 * cyclotomicLast Q i a 0 r = _
  rw [cyclotomicLast_zero_eq, mul_smul_comm, mul_one]
  rfl

theorem zeroFinEquiv_left (ha : (a i).Monic) (r : CycKLR k Q a (0 : Multiset I))
    (v : Fin (a i).natDegree → CycKLR k Q a (0 : Multiset I)) :
    zeroFinEquiv Q i a ha (fun d => r * v d) = r • zeroFinEquiv Q i a ha v := by
  rw [zero_left_smul]
  have h : (fun d => r * v d) = (cyclotomicZeroEquiv Q a r) • v := by
    funext d
    apply (cyclotomicZeroEquiv Q a).injective
    simp [Algebra.smul_def]
  rw [h, map_smul]

theorem zeroFinEquiv_right (ha : (a i).Monic) (r : CycKLR k Q a (0 : Multiset I))
    (v : Fin (a i).natDegree → CycKLR k Q a (0 : Multiset I)) :
    zeroFinEquiv Q i a ha (fun d => v d * r) = op r • zeroFinEquiv Q i a ha v := by
  rw [zero_right_smul]
  have h : (fun d => v d * r) = (cyclotomicZeroEquiv Q a r) • v := by
    funext d
    apply (cyclotomicZeroEquiv Q a).injective
    simp [Algebra.smul_def, mul_comm]
  rw [h, map_smul]

omit [DecidableEq I] in
/-- Rank-zero degree is the nonnegative Cartan weight, without a dominance premise. -/
theorem zero_degree_eq_weight
    {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
    (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ) :
    (a i).natDegree = (RD.pair (RD.iY i) (Λ - ((0 : Multiset I).map RD.iX).sum)).toNat := by
  simp only [Multiset.map_zero, Multiset.sum_zero, sub_zero, ← hΛ, Int.toNat_natCast]

end AbsentColour
end Categorification.KLR.KLRAlgebra
