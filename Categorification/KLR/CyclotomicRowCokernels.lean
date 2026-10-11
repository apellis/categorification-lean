/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerSnake

/-!
# Cyclotomic horizontal cokernels

`lowerPCokerEquiv` identifies the existing lower horizontal cokernel with
`R^Λ(β)e(γ,i) ⊗_{R(γ)} e(γ,i)R^Λ(β)` by quotienting the first factor.
`eiPCokerEquiv` identifies the existing middle cokernel with the actual
cyclotomic corner, by restricting the ambient quotient projection to both
colour cuts. The representative formulas and both roundtrips are proved;
`cyclotomicSigma_tmul` identifies the transported crossing with `x τ_n y`.

These supply the source module identifications needed to use the connecting
segment in Kang–Kashiwara, arXiv:1102.4677v4, §5.2. The assertions here are
k-linear, over any commutative base ring and arbitrary cyclotomic polynomials,
including the constant-one family. For `β={i}+γ`, the case `γ=0` uses the
actual `R(0)` action and the one-strand algebra, not positive-rank exactness.
The source's grading and bimodule statements, absent-colour blocks, and the
final inverse of Theorem 5.2 are not asserted here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "Rb" => KLRAlgebra k Q β
local notation "Rl" => CycKLR k Q a β
local notation "N" => LowerCoefficient Q i γ a

/-- The actual cyclotomic inclusion on the last-colour cut. -/
def lowerLastCyc : KLRAlgebra k Q γ →ₙₐ[k] Rl where
  toFun r := CycKLR.mk k Q a β (cL Q i γ r)
  map_zero' := by rw [cL_zero, map_zero]
  map_add' r s := by rw [cL_add, map_add]
  map_mul' r s := by rw [cL_mul, map_mul]
  map_smul' c r := by rw [cL_smul, map_smul]; rfl

/-- `R^Λ(β)e(γ,i) ⊗_{R(γ)} e(γ,i)R^Λ(β)`. -/
abbrev LowerCyclotomic : Type _ :=
  BalancedTensor k Rl (KLRAlgebra k Q γ)
    (CornerTensor.Left (lowerLastCyc Q i γ a)) N

/-- The actual cyclotomic quotient on the left ideal. -/
def lowerLeftQuotient : CornerTensor.Left (lowerLast Q i γ) →ₗ[k]
    CornerTensor.Left (lowerLastCyc Q i γ a) where
  toFun x := ⟨CycKLR.mk k Q a β (x : Rb), by
    change CycKLR.mk k Q a β (x : Rb) * CycKLR.mk k Q a β (cL Q i γ 1) = _
    rw [← map_mul]
    exact congrArg (CycKLR.mk k Q a β) (CornerTensor.left_mem (lowerLast Q i γ) x)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

/-- The canonical quotient projection on the genuine balanced tensor. -/
def lowerCyclotomicProj : KZeroPrime Q i γ a →ₗ[k] LowerCyclotomic Q i γ a :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k Rl (KLRAlgebra k Q γ)
      (CornerTensor.Left (lowerLastCyc Q i γ a)) N).comp (lowerLeftQuotient Q i γ a))
    (by
      intro x r y
      change BalancedTensor.tmul (lowerLeftQuotient Q i γ a (op r • x)) y =
        BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) (r • y)
      rw [← BalancedTensor.op_smul_tmul]
      congr 1
      apply Subtype.ext
      exact map_mul (CycKLR.mk k Q a β) _ _)

theorem lowerCyclotomicProj_tmul (x : CornerTensor.Left (lowerLast Q i γ)) (y : N) :
    lowerCyclotomicProj Q i γ a (BalancedTensor.tmul x y) =
      BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) y := rfl

/-- The source-normalized multiplier dies in the actual cyclotomic quotient. -/
theorem lowerCyclotomicProj_lowerP (t : KOnePrime Q i γ a) :
    lowerCyclotomicProj Q i γ a (lowerP Q i γ a t) = 0 := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t u ht hu => rw [map_add, map_add, ht, hu, add_zero]
  | tmul x y =>
    rw [lowerP_tmul, map_smul]
    have hx : lowerLeftQuotient Q i γ a
        (lowerLastProj Q i γ ((x : Rb) * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ))) = 0 := by
      apply Subtype.ext
      change CycKLR.mk k Q a β _ = 0
      rw [lowerP_factor_val]
      apply (CycKLR.mk_eq_zero_iff _).2
      apply TwoSidedIdeal.mul_mem_left
      exact TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a _)
    change ((-1 : k) ^ Multiset.card γ) • BalancedTensor.tmul
      (lowerLeftQuotient Q i γ a (lowerLastProj Q i γ _)) y = 0
    rw [hx, BalancedTensor.zero_tmul, smul_zero]

/-- Forward map out of the existing, unchanged cokernel. -/
def lowerPCokerToCyclotomic : LowerPCoker Q i γ a →ₗ[k] LowerCyclotomic Q i γ a :=
  (LinearMap.range (lowerP Q i γ a)).liftQ (lowerCyclotomicProj Q i γ a)
    (by rintro _ ⟨t, rfl⟩; exact lowerCyclotomicProj_lowerP Q i γ a t)

/-- Representatives for the inverse, before the cyclotomic quotient. -/
def lowerCokerRep : Rb →ₗ[k] N →ₗ[k] LowerPCoker Q i γ a :=
  ((BalancedTensor.mkBil k Rb (KLRAlgebra k Q γ)
    (CornerTensor.Left (lowerLast Q i γ)) N).comp
      ((lowerLastProj Q i γ).restrictScalars k)).compr₂
        (LinearMap.range (lowerP Q i γ a)).mkQ

private theorem sign_square (n : ℕ) : ((-1 : k) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- The multiplier relation in the actual lower cokernel, with its sign intact. -/
theorem lowerCokerRep_tau (r : Rb) (y : N) :
    lowerCokerRep Q i γ a (r * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ)) y = 0 := by
  let x : CornerTensor.Left (lowerFirst Q i γ) :=
    Graded.leftIdealProj (by change cR Q i γ 1 * cR Q i γ 1 = _; rw [← cR_mul, one_mul]; rfl) r
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨((-1 : k) ^ Multiset.card γ) • BalancedTensor.tmul x y, ?_⟩
  rw [map_smul, lowerP_tmul, smul_smul, sign_square, one_smul]
  unfold lowerZeroElem
  congr 1
  apply Subtype.ext
  change ((r * cR Q i γ 1) * _) * cL Q i γ 1 = (r * _) * cL Q i γ 1
  rw [mul_assoc r, lower_tauW_cut, ← mul_assoc, mul_assoc (r * _), ← cL_mul, one_mul]

/-- The cyclotomic relation vanishes after passage to the lower cokernel.
The empty lower rank is treated by the genuine one-strand algebra `R(i)=k[x]`. -/
theorem lowerCokerRep_cyc (r : Rb) (hr : r ∈ cycIdeal Q a β) (y : N) :
    lowerCokerRep Q i γ a r y = 0 := by
  obtain ⟨l, hl, s, hs, rfl⟩ := Submodule.mem_sup.1
    (cycIdeal_le a (zero_lt_card_single_add i γ) (Multiset.card γ) (card_single_add i γ).symm hr)
  rw [map_add, LinearMap.add_apply]
  have hs0 : lowerCokerRep Q i γ a s y = 0 := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
    exact lowerCokerRep_tau Q i γ a c y
  rw [hs0, add_zero]
  by_cases hγ : 0 < Multiset.card γ
  · change Submodule.Quotient.mk (lowerZeroElem Q i γ a l y) = 0
    rw [lowerZeroElem_cycL0 Q i γ a hγ l hl y]
    rfl
  · have hg : γ = 0 := Multiset.card_eq_zero.mp (by omega)
    subst γ
    have comm (u v : KLRAlgebra k Q (Si + 0)) : u * v = v * u := by
      apply (castKLR Q (add_zero Si)).injective
      apply (singleEquiv k Q i).injective
      simp only [map_mul]
      exact mul_comm _ _
    have hle : cycL0 (Q := Q) a (zero_lt_card_single_add i 0) ≤
        Submodule.span (KLRAlgebra k Q (Si + 0)) {tauW a (zero_lt_card_single_add i 0) 0} := by
      apply Submodule.span_le.2
      rintro z ⟨w, _, rfl⟩
      apply Submodule.mem_span_singleton.2
      refine ⟨w, ?_⟩
      change w * tauW a _ 0 = _
      simp only [tauW, tauProd_zero, mul_one]
      exact comm _ _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hle hl)
    rw [← hc]
    exact lowerCokerRep_tau Q i 0 a c y

/-- Descend the tensor representative through the actual cyclotomic algebra. -/
def lowerCokerRepBar : Rl →ₗ[k] N →ₗ[k] LowerPCoker Q i γ a :=
  (LinearMap.ker (CycKLR.mk k Q a β).toLinearMap).liftQ (lowerCokerRep Q i γ a)
    (by
      intro r hr
      ext y
      exact lowerCokerRep_cyc Q i γ a r ((CycKLR.mk_eq_zero_iff r).1 hr) y) ∘ₗ
    ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
      CycKLR.mk_surjective).symm.toLinearMap

theorem lowerCokerRepBar_mk (r : Rb) (y : N) :
    lowerCokerRepBar Q i γ a (CycKLR.mk k Q a β r) y = lowerCokerRep Q i γ a r y := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (CycKLR.mk k Q a β).toLinearMap CycKLR.mk_surjective r
  change ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
    CycKLR.mk_surjective).symm (CycKLR.mk k Q a β r) = _ at he
  rw [lowerCokerRepBar, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
  rfl

theorem lowerLeftQuotient_surjective : Function.Surjective (lowerLeftQuotient Q i γ a) := by
  intro x
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (x : Rl)
  refine ⟨lowerLastProj Q i γ r, ?_⟩
  apply Subtype.ext
  change CycKLR.mk k Q a β (r * cL Q i γ 1) = (x : Rl)
  rw [map_mul, hr]
  exact CornerTensor.left_mem (lowerLastCyc Q i γ a) x

/-- Canonical inverse: lift the first cyclotomic factor and take its cokernel class. -/
def cyclotomicToLowerPCoker : LowerCyclotomic Q i γ a →ₗ[k] LowerPCoker Q i γ a :=
  BalancedTensor.lift
    ((lowerCokerRepBar Q i γ a).comp
      ((Graded.leftIdeal ((lowerLastCyc Q i γ a) 1)).subtype.restrictScalars k))
    (by
      intro x r y
      obtain ⟨x, rfl⟩ := lowerLeftQuotient_surjective Q i γ a x
      change lowerCokerRepBar Q i γ a
        (CycKLR.mk k Q a β (x : Rb) * CycKLR.mk k Q a β (cL Q i γ r)) y =
        lowerCokerRepBar Q i γ a (CycKLR.mk k Q a β (x : Rb)) (r • y)
      rw [← map_mul, lowerCokerRepBar_mk, lowerCokerRepBar_mk]
      change Submodule.Quotient.mk (lowerZeroElem Q i γ a ((x : Rb) * cL Q i γ r) y) =
        Submodule.Quotient.mk (lowerZeroElem Q i γ a (x : Rb) (r • y))
      rw [lowerZeroElem_balance])

/-- The inverse uses the given tensor representative, not an arbitrary isomorphism. -/
theorem cyclotomicToLowerPCoker_tmul (x : CornerTensor.Left (lowerLast Q i γ)) (y : N) :
    cyclotomicToLowerPCoker Q i γ a
      (BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) y) =
      Submodule.Quotient.mk (BalancedTensor.tmul x y) := by
  change lowerCokerRepBar Q i γ a (CycKLR.mk k Q a β (x : Rb)) y = _
  rw [lowerCokerRepBar_mk]
  have hx : lowerLastProj Q i γ (x : Rb) = x := Subtype.ext (CornerTensor.left_mem _ x)
  change Submodule.Quotient.mk (BalancedTensor.tmul (lowerLastProj Q i γ (x : Rb)) y) = _
  rw [hx]

theorem lowerPCoker_inverse_forward (z : LowerPCoker Q i γ a) :
    cyclotomicToLowerPCoker Q i γ a (lowerPCokerToCyclotomic Q i γ a z) = z := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change cyclotomicToLowerPCoker Q i γ a (lowerCyclotomicProj Q i γ a t) = _
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | add t u ht hu => rw [map_add, map_add, ht, hu, Submodule.Quotient.mk_add]
  | tmul x y => rw [lowerCyclotomicProj_tmul, cyclotomicToLowerPCoker_tmul]

theorem lowerPCoker_forward_inverse (z : LowerCyclotomic Q i γ a) :
    lowerPCokerToCyclotomic Q i γ a (cyclotomicToLowerPCoker Q i γ a z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t u ht hu => rw [map_add, map_add, ht, hu]
  | tmul x y =>
    obtain ⟨x, rfl⟩ := lowerLeftQuotient_surjective Q i γ a x
    rw [cyclotomicToLowerPCoker_tmul]
    rfl

/-- The lower horizontal cokernel is the genuine cyclotomic balanced tensor. -/
def lowerPCokerEquiv : LowerPCoker Q i γ a ≃ₗ[k] LowerCyclotomic Q i γ a :=
  LinearEquiv.ofLinearMap (lowerPCokerToCyclotomic Q i γ a) (cyclotomicToLowerPCoker Q i γ a)
    (LinearMap.ext (lowerPCoker_forward_inverse Q i γ a))
    (LinearMap.ext (lowerPCoker_inverse_forward Q i γ a))

local notation "R" => KLRAlgebra k Q (Si + β)
local notation "S" => CycKLR k Q a (Si + β)
local notation "K0" => KZero Q (Si + β) a (zero_lt_card_single_add i β)
local notation "K1" => KOne Q (Si + β) a (by simp)

/-- The genuine cyclotomic corner `e(β,i)R^Λ(β+i)e(β,i)`. -/
def MiddleCyclotomicSub : Submodule k S where
  carrier := {x | CycKLR.mk k Q a (Si + β) (cL Q i β 1) * x = x ∧
    x * CycKLR.mk k Q a (Si + β) (cL Q i β 1) = x}
  zero_mem' := ⟨mul_zero _, zero_mul _⟩
  add_mem' hx hy := ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  smul_mem' c x hx := ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩

abbrev MiddleCyclotomic : Type _ := ↥(MiddleCyclotomicSub Q i γ a)

/-- Cyclotomic projection from the existing ambient quotient presentation. -/
def middleQuotient : K0 →ₗ[k] S :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ
    (CycKLR.mk k Q a (Si + β)).toLinearMap
    (by intro r hr; exact (CycKLR.mk_eq_zero_iff r).2 (cycL0_le a _ hr)) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a (zero_lt_card_single_add i β))).symm.toLinearMap

@[simp] theorem middleQuotient_mk (r : R) :
    middleQuotient Q i γ a (Submodule.Quotient.mk r) = CycKLR.mk k Q a (Si + β) r := rfl

theorem middleQuotient_left (r : R) (z : K0) :
    middleQuotient Q i γ a (r • z) = CycKLR.mk k Q a (Si + β) r * middleQuotient Q i γ a z := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact map_mul (CycKLR.mk k Q a (Si + β)) r z

theorem middleQuotient_right (z : K0) :
    middleQuotient Q i γ a (act0 Q i β a 1 z) =
      middleQuotient Q i γ a z * CycKLR.mk k Q a (Si + β) (cL Q i β 1) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact map_mul (CycKLR.mk k Q a (Si + β)) z _

/-- The middle row's canonical projection, retaining both genuine colour cuts. -/
def middleCyclotomicProj : EIKZero Q i β a →ₗ[k] MiddleCyclotomic Q i γ a :=
  ((middleQuotient Q i γ a).comp (eiZeroCoordinates Q i γ a)).codRestrict _ (by
    intro z
    constructor
    · change CycKLR.mk k Q a (Si + β) (cL Q i β 1) *
        middleQuotient Q i γ a (eiZeroCoordinates Q i γ a z) = _
      rw [← middleQuotient_left, eiZeroCoordinates_leftCut]
      rfl
    · change middleQuotient Q i γ a (eiZeroCoordinates Q i γ a z) *
        CycKLR.mk k Q a (Si + β) (cL Q i β 1) = _
      rw [← middleQuotient_right, eiZeroCoordinates_rightCut]
      rfl)

/-- Canonical cut lift of an ambient quotient representative. -/
def middleTensorLift : K0 →ₗ[k] EIKZero Q i β a where
  toFun z := ⟨oneConcat Q β Si • lowerZeroDecode Q i γ a z, by
    change oneConcat Q β Si • (oneConcat Q β Si • _) = _
    rw [smul_smul, oneConcat_idem.eq]⟩
  map_add' z u := Subtype.ext (by simp only [map_add, smul_add]; rfl)
  map_smul' c z := Subtype.ext (by
    change oneConcat Q β Si • lowerZeroDecode Q i γ a (c • z) =
      c • (oneConcat Q β Si • lowerZeroDecode Q i γ a z)
    rw [map_smul, smul_comm])

theorem middleTensorLift_coordinates (z : K0) :
    eiZeroCoordinates Q i γ a (middleTensorLift Q i γ a z) =
      cL Q i β 1 • act0 Q i β a 1 z := by
  change lowerQuotientCast Q i γ a
    (tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ)
      (oneConcat Q β Si • kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ)
        (lowerQuotientUncast Q i γ a z))) = _
  rw [map_smul, lowerQuotientCast_leftCut, tensorToKZero_kZeroToTensor,
    lowerQuotientCast_rightCut, lowerQuotientCast_uncast]

theorem middleTensorLift_coordinates_inverse (z : EIKZero Q i β a) :
    middleTensorLift Q i γ a (eiZeroCoordinates Q i γ a z) = z := by
  apply eiZeroCoordinates_injective Q i γ a
  rw [middleTensorLift_coordinates, eiZeroCoordinates_rightCut, eiZeroCoordinates_leftCut]

/-- The actual quotient projection sends a cut representative to `e [r] e`. -/
theorem middleCyclotomicProj_representative (r : R) :
    (middleCyclotomicProj Q i γ a (middleTensorLift Q i γ a (Submodule.Quotient.mk r)) : S) =
      CycKLR.mk k Q a (Si + β) (cL Q i β 1 * r * cL Q i β 1) := by
  change middleQuotient Q i γ a (eiZeroCoordinates Q i γ a (middleTensorLift Q i γ a _)) = _
  rw [middleTensorLift_coordinates, middleQuotient_left, middleQuotient_right, middleQuotient_mk]
  simp only [map_mul, mul_assoc]

theorem middleCyclotomicProj_surjective : Function.Surjective (middleCyclotomicProj Q i γ a) := by
  intro z
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (z : S)
  refine ⟨middleTensorLift Q i γ a (Submodule.Quotient.mk r), ?_⟩
  apply Subtype.ext
  rw [middleCyclotomicProj_representative, map_mul, map_mul, hr, z.2.1, z.2.2]

/-- The normalization sign and the right cut in the actual middle horizontal map. -/
theorem eiP_coordinates (z : EIKOne Q i β a) :
    eiZeroCoordinates Q i γ a (eiP Q i γ a z) =
      ((-1 : k) ^ Multiset.card β) • act0 Q i β a 1
        (pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β)
          (card_single_add i β).symm
          (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) z)) := by
  change lowerQuotientCast Q i γ a (tensorToKZero Q i β a (by simp)
    (zero_lt_card_single_add i γ) (((-1 : k) ^ Multiset.card β) •
      kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ)
        (lowerQuotientUncast Q i γ a _))) = _
  rw [LinearMap.map_smul_of_tower, map_smul, tensorToKZero_kZeroToTensor,
    lowerQuotientCast_rightCut, lowerQuotientCast_uncast]
  rfl

theorem middleQuotient_pMap (z : K1) :
    middleQuotient Q i γ a (pMap a (zero_lt_card_single_add i β) (by simp)
      (Multiset.card β) (card_single_add i β).symm z) = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [pMap_mk, middleQuotient_mk]
  apply (CycKLR.mk_eq_zero_iff _).2
  exact TwoSidedIdeal.mul_mem_left _ _ _
    (TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a _))

theorem middleCyclotomicProj_eiP (z : EIKOne Q i β a) :
    middleCyclotomicProj Q i γ a (eiP Q i γ a z) = 0 := by
  apply Subtype.ext
  change middleQuotient Q i γ a (eiZeroCoordinates Q i γ a (eiP Q i γ a z)) = 0
  rw [eiP_coordinates, map_smul, middleQuotient_right, middleQuotient_pMap, zero_mul, smul_zero]

/-- A genuine left-cut tensor lift on the source of the middle horizontal arrow. -/
def middleOneLift : K1 →ₗ[k] EIKOne Q i β a where
  toFun z := ⟨cL Q i β 1 • kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) z, by
    change cL Q i β 1 • (cL Q i β 1 • _) = _
    rw [smul_smul, ← cL_mul, one_mul]⟩
  map_add' z u := Subtype.ext (by simp only [map_add, smul_add]; rfl)
  map_smul' c z := Subtype.ext (by
    change cL Q i β 1 • kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) (c • z) =
      c • (cL Q i β 1 • kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) z)
    rw [LinearMap.map_smul_of_tower, smul_comm])

theorem middleOneLift_coordinates (z : K1) :
    tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) (middleOneLift Q i γ a z) =
      cL Q i β 1 • act1 Q i β a (by simp) 1 z := by
  change tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)
    (cL Q i β 1 • kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) z) = _
  rw [map_smul, tensorToKOne_kOneToTensor]
  congr 1
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [kOneRightCut_mk, act1_mk, cR_one]

theorem middle_eiP_lift (z : K1) :
    eiP Q i γ a (((-1 : k) ^ Multiset.card β) • middleOneLift Q i γ a z) =
      middleTensorLift Q i γ a (pMap a (zero_lt_card_single_add i β) (by simp)
        (Multiset.card β) (card_single_add i β).symm z) := by
  apply eiZeroCoordinates_injective Q i γ a
  rw [map_smul, map_smul, eiP_coordinates, smul_smul, sign_square, one_smul,
    middleOneLift_coordinates, map_smul, pMap_act, middleTensorLift_coordinates, map_smul,
    act0_act0, one_mul]

/-- Exactness is proved on the actual cuts, using the ambient quotient sequence. -/
theorem ker_middleCyclotomicProj :
    LinearMap.ker (middleCyclotomicProj Q i γ a) = LinearMap.range (eiP Q i γ a) := by
  ext z
  constructor
  · intro hz
    have hzero : middleQuotient Q i γ a (eiZeroCoordinates Q i γ a z) = 0 :=
      congrArg Subtype.val hz
    have hpi : piMap a (zero_lt_card_single_add i β) (eiZeroCoordinates Q i γ a z) = 0 := by
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (eiZeroCoordinates Q i γ a z)
      rw [← hr, middleQuotient_mk] at hzero
      rw [← hr]
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact (CycKLR.mk_eq_zero_iff r).1 hzero
    have hrange : eiZeroCoordinates Q i γ a z ∈ LinearMap.range
        (pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β) (card_single_add i β).symm) := by
      rw [range_pMap]
      exact hpi
    obtain ⟨u, hu⟩ := hrange
    refine ⟨((-1 : k) ^ Multiset.card β) • middleOneLift Q i γ a u, ?_⟩
    rw [middle_eiP_lift, hu, middleTensorLift_coordinates_inverse]
  · rintro ⟨u, rfl⟩
    exact middleCyclotomicProj_eiP Q i γ a u

/-- The actual middle cokernel, identified by its cyclotomic projection. -/
def eiPCokerEquiv : EIPCoker Q i γ a ≃ₗ[k] MiddleCyclotomic Q i γ a :=
  (Submodule.quotEquivOfEq _ _ (ker_middleCyclotomicProj Q i γ a).symm).trans
    ((middleCyclotomicProj Q i γ a).quotKerEquivOfSurjective
      (middleCyclotomicProj_surjective Q i γ a))

/-- The equivalence is the prescribed quotient projection on every representative. -/
theorem eiPCokerEquiv_mk (z : EIKZero Q i β a) :
    eiPCokerEquiv Q i γ a (Submodule.Quotient.mk z) = middleCyclotomicProj Q i γ a z := by
  rw [eiPCokerEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

/-- Conversely, any representative of the canonical projection gives the inverse class. -/
theorem eiPCokerEquiv_symm_proj (z : EIKZero Q i β a) :
    (eiPCokerEquiv Q i γ a).symm (middleCyclotomicProj Q i γ a z) = Submodule.Quotient.mk z := by
  rw [← eiPCokerEquiv_mk, LinearEquiv.symm_apply_apply]

theorem eiPCoker_inverse_forward (z : EIPCoker Q i γ a) :
    (eiPCokerEquiv Q i γ a).symm (eiPCokerEquiv Q i γ a z) = z :=
  (eiPCokerEquiv Q i γ a).symm_apply_apply z

theorem eiPCoker_forward_inverse (z : MiddleCyclotomic Q i γ a) :
    eiPCokerEquiv Q i γ a ((eiPCokerEquiv Q i γ a).symm z) = z :=
  (eiPCokerEquiv Q i γ a).apply_symm_apply z

/-- Canonical generator formula for the lower cokernel equivalence. -/
theorem lowerPCokerEquiv_mk_tmul (x : CornerTensor.Left (lowerLast Q i γ)) (y : N) :
    lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk (BalancedTensor.tmul x y)) =
      BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) y := rfl

/-- Canonical inverse formula for the lower cokernel equivalence. -/
theorem lowerPCokerEquiv_symm_tmul (x : CornerTensor.Left (lowerLast Q i γ)) (y : N) :
    (lowerPCokerEquiv Q i γ a).symm
      (BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) y) =
      Submodule.Quotient.mk (BalancedTensor.tmul x y) :=
  cyclotomicToLowerPCoker_tmul Q i γ a x y

/-- The induced crossing between the two genuine cyclotomic modules. -/
def cyclotomicSigma : LowerCyclotomic Q i γ a →ₗ[k] MiddleCyclotomic Q i γ a :=
  (eiPCokerEquiv Q i γ a).toLinearMap.comp
    ((lowerFCoker Q i γ a).comp (cyclotomicToLowerPCoker Q i γ a))

/-- Transport of the actual cokernel crossing is `x τ_n y`, with `τ=-ψ`.
Every cyclotomic tensor has representatives of this form. -/
theorem cyclotomicSigma_tmul (x : CornerTensor.Left (lowerLast Q i γ))
    (y : N) (b : Rb) (hy : (y : Rl) = CycKLR.mk k Q a β b) :
    (cyclotomicSigma Q i γ a (BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) y) : S) =
      CycKLR.mk k Q a (Si + β)
        (cL Q i β (x : Rb) * -ψ (Multiset.card γ) * cL Q i β b) := by
  change (eiPCokerEquiv Q i γ a (lowerFCoker Q i γ a
    (cyclotomicToLowerPCoker Q i γ a (BalancedTensor.tmul (lowerLeftQuotient Q i γ a x) y))) : S) = _
  rw [cyclotomicToLowerPCoker_tmul, lowerFCoker_mk, eiPCokerEquiv_mk]
  change middleQuotient Q i γ a (eiZeroCoordinates Q i γ a
    (lowerF Q i γ a (BalancedTensor.tmul x y))) = _
  rw [eiZeroCoordinates_lowerF, lowerFCoordinates_tmul Q i γ a x y b hy, middleQuotient_mk]

/-- The comparison intertwines the specified maps, not merely their isomorphism classes. -/
theorem cyclotomicSigma_lowerPCoker (z : LowerPCoker Q i γ a) :
    cyclotomicSigma Q i γ a (lowerPCokerEquiv Q i γ a z) =
      eiPCokerEquiv Q i γ a (lowerFCoker Q i γ a z) := by
  change eiPCokerEquiv Q i γ a (lowerFCoker Q i γ a
    (cyclotomicToLowerPCoker Q i γ a (lowerPCokerToCyclotomic Q i γ a z))) = _
  rw [lowerPCoker_inverse_forward]

end Categorification.KLR.KLRAlgebra
