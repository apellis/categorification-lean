/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicTensor

/-!
# The balanced tensor presentation of the left-added induction module

Kang–Kashiwara, arXiv:1102.4677v4, §4.2 uses
`R(β + α_i)e(i,β) ⊗_{R(β)} R^Λ(β)`. Here the tensor product is balanced
over the noncommutative algebra `R(β)`, with its actual concatenation action.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (β : Multiset I)
  (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Ri" => KLRAlgebra k Q Si
local notation "M" => IndBimod Q Si β
local notation "Rl" => CycKLR k Q a β

/-- Restrict the right concatenation action to `R(β)`. -/
local instance : Module Rbᵐᵒᵖ M :=
  Module.compHom M (Algebra.TensorProduct.includeRight : Rb →ₐ[k] Ri ⊗[k] Rb).toRingHom.op

local instance : IsScalarTower k Rbᵐᵒᵖ M where
  smul_assoc c b m := Subtype.ext (by
    change (m : R) * concat Q Si β (1 ⊗ₜ (c • b.unop)) =
      c • ((m : R) * concat Q Si β (1 ⊗ₜ b.unop))
    rw [TensorProduct.tmul_smul, map_smul, mul_smul_comm])

local instance : SMulCommClass R Rbᵐᵒᵖ M where
  smul_comm r b m := Subtype.ext (by
    change r * ((m : R) * concat Q Si β (1 ⊗ₜ b.unop)) =
      (r * m) * concat Q Si β (1 ⊗ₜ b.unop)
    rw [mul_assoc])

local instance : Module Rb Rl := Module.compHom Rl (CycKLR.mk k Q a β).toRingHom

local instance : IsScalarTower k Rb Rl where
  smul_assoc c b z := by
    change (CycKLR.mk k Q a β (c • b)) * z = c • (CycKLR.mk k Q a β b * z)
    rw [map_smul, smul_mul_assoc]

/-- The source's actual balanced induction tensor, before the left colour cut. -/
abbrev KOneTensor : Type _ := BalancedTensor k R Rb M Rl

/-- The elementary tensor represented by a corner element and a cyclotomic coefficient. -/
def kOneTensorElem (m : M) (z : Rl) : KOneTensor Q i β a := BalancedTensor.tmul m z

/-- The unit tensor `r e(i,β) ⊗ 1`. -/
def kOneTensorUnit : R →ₗ[R] KOneTensor Q i β a :=
  { toFun r := kOneTensorElem Q i β a (Graded.leftIdealProj oneConcat_idem r) 1
    map_add' r s := by
      change BalancedTensor.tmul ((Graded.leftIdealProj
        (oneConcat_idem (Q := Q) (ν := Si) (ν' := β))) (r + s)) (1 : Rl) = _
      rw [map_add, BalancedTensor.add_tmul]
      rfl
    map_smul' r s := by
      rw [map_smul]
      exact (BalancedTensor.smul_tmul' r _ _).symm }

/-- Balancing uses precisely the concatenation action on the corner. -/
theorem kOneTensor_balance (m : M) (b : Rb) (z : Rl) :
    kOneTensorElem Q i β a
        ⟨(m : R) * concat Q Si β (1 ⊗ₜ b), mul_concat_mem m _⟩ z =
      kOneTensorElem Q i β a m (CycKLR.mk k Q a β b * z) :=
  BalancedTensor.op_smul_tmul m b z

/-- Every elementary tensor is a unit tensor after lifting its cyclotomic coefficient. -/
theorem kOneTensorElem_mk (m : M) (b : Rb) :
    kOneTensorElem Q i β a m (CycKLR.mk k Q a β b) =
      kOneTensorUnit Q i β a ((m : R) * concat Q Si β (1 ⊗ₜ b)) := by
  rw [← mul_one (CycKLR.mk k Q a β b), ← kOneTensor_balance]
  congr 1
  apply Subtype.ext
  exact (mul_concat_mem m _).symm

/-- The unit-tensor map ignores the complementary right idempotent. -/
theorem kOneTensorUnit_cut (r : R) :
    kOneTensorUnit Q i β a (r * oneConcat Q Si β) = kOneTensorUnit Q i β a r := by
  change kOneTensorElem Q i β a _ 1 = kOneTensorElem Q i β a _ 1
  congr 1
  apply Subtype.ext
  change (r * oneConcat Q Si β) * oneConcat Q Si β = r * oneConcat Q Si β
  rw [mul_assoc, oneConcat_idem.eq]

/-- An elementary concatenation transfers its `R(β)` coefficient across the tensor. -/
theorem kOneTensorUnit_concat_tmul (b : Rb) (c : Ri) :
    kOneTensorUnit Q i β a (concat Q Si β (c ⊗ₜ b)) =
      kOneTensorElem Q i β a
        ⟨concat Q Si β (c ⊗ₜ 1), concat_mul_oneConcat _⟩ (CycKLR.mk k Q a β b) := by
  rw [kOneTensorElem_mk, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- A cyclotomic coefficient vanishes by balancing, rather than by choosing a linear inverse. -/
theorem kOneTensorUnit_concat_eq_zero {t : Ri ⊗[k] Rb}
    (ht : t ∈ tJ (Q := Q) i β a) :
    kOneTensorUnit Q i β a (concat Q Si β t) = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨c, b, hb, rfl⟩ := ht
    rw [kOneTensorUnit_concat_tmul, (CycKLR.mk_eq_zero_iff _).2 hb]
    exact BalancedTensor.tmul_zero _
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.map_smul_of_tower, hx, smul_zero]

/-- The genuine tensor relation kills the left-ideal presentation of `K₁`. -/
theorem kOneTensorUnit_eq_zero (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) {r : R} (hr : r ∈ cycL1 a h1) :
    kOneTensorUnit Q i β a r = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨w, hw, rfl⟩ := hr
    obtain ⟨t, ht⟩ := exists_concat_of_subR1 (Q := Q) i β hw
    rw [← kOneTensorUnit_cut, mul_assoc, ht,
      ← oneConcat_mul_concat (Q := Q) (t := t), ← mul_assoc,
      cycAt_one_mul_oneConcat i β a h1 hβ, ← concat_mul]
    apply kOneTensorUnit_concat_eq_zero
    apply tJ_mul_mem
    exact Submodule.subset_span ⟨1, cycAt a ⟨0, hβ⟩, cycAt_mem_cycIdeal a hβ, rfl⟩
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- The canonical map from the quotient presentation to the source's balanced tensor. -/
def kOneToTensor (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    KOne Q (Si + β) a h1 →ₗ[R] KOneTensor Q i β a :=
  (cycL1 a h1).liftQ (kOneTensorUnit Q i β a)
    (fun _ hr => LinearMap.mem_ker.mpr (kOneTensorUnit_eq_zero Q i β a h1 hβ hr))

theorem kOneToTensor_mk (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (r : R) :
    kOneToTensor Q i β a h1 hβ (Submodule.Quotient.mk r) = kOneTensorUnit Q i β a r := rfl

/-- Multiplication on the original corner, with coefficients before quotienting. -/
def kOneTensorCoeff (h1 : 1 < Multiset.card (Si + β)) (m : M) :
    Rb →ₗ[k] KOne Q (Si + β) a h1 where
  toFun b := Submodule.Quotient.mk ((m : R) * concat Q Si β (1 ⊗ₜ b))
  map_add' b c := by simp only [TensorProduct.tmul_add, map_add, mul_add, Submodule.Quotient.mk_add]
  map_smul' c b := by
    simp only [TensorProduct.tmul_smul, map_smul, mul_smul_comm, RingHom.id_apply]
    rfl

private theorem cycMkLin_surjective : Function.Surjective (CycKLR.mk k Q a β).toLinearMap :=
  CycKLR.mk_surjective

/-- Descend multiplication through the actual cyclotomic quotient. -/
def kOneTensorCoeffBar (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (m : M) :
    Rl →ₗ[k] KOne Q (Si + β) a h1 :=
  (LinearMap.ker (CycKLR.mk k Q a β).toLinearMap).liftQ (kOneTensorCoeff Q i β a h1 m)
    (by
      intro b hb
      change Submodule.Quotient.mk ((m : R) * concat Q Si β (1 ⊗ₜ b)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      apply Submodule.smul_mem (cycL1 a h1) (m : R)
      apply concat_mem_cycL1 i β a h1 hβ
      exact Submodule.subset_span ⟨1, b, (CycKLR.mk_eq_zero_iff b).1 hb, rfl⟩) ∘ₗ
    ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
      (cycMkLin_surjective Q β a)).symm.toLinearMap

theorem kOneTensorCoeffBar_mk (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) (m : M) (b : Rb) :
    kOneTensorCoeffBar Q i β a h1 hβ m (CycKLR.mk k Q a β b) =
      Submodule.Quotient.mk ((m : R) * concat Q Si β (1 ⊗ₜ b)) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (CycKLR.mk k Q a β).toLinearMap (cycMkLin_surjective Q β a) b
  change ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
    (cycMkLin_surjective Q β a)).symm (CycKLR.mk k Q a β b) = _ at he
  rw [kOneTensorCoeffBar, LinearMap.comp_apply, LinearEquiv.coe_coe, he,
    Submodule.liftQ_apply]
  rfl

/-- The descended bilinear multiplication map. -/
def kOneTensorBil (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    M →ₗ[k] Rl →ₗ[k] KOne Q (Si + β) a h1 where
  toFun := kOneTensorCoeffBar Q i β a h1 hβ
  map_add' m n := by
    ext z
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
    simp only [LinearMap.add_apply, kOneTensorCoeffBar_mk, Submodule.coe_add,
      add_mul, Submodule.Quotient.mk_add]
  map_smul' c m := by
    ext z
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
    simp only [LinearMap.smul_apply, RingHom.id_apply, kOneTensorCoeffBar_mk]
    change Submodule.Quotient.mk ((c • (m : R)) * concat Q Si β (1 ⊗ₜ b)) = _
    rw [smul_mul_assoc]
    rfl

/-- The canonical multiplication from the source's balanced tensor to its quotient model. -/
def tensorToKOne (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    KOneTensor Q i β a →ₗ[R] KOne Q (Si + β) a h1 :=
  BalancedTensor.liftB (kOneTensorBil Q i β a h1 hβ)
    (by
      intro m b z
      obtain ⟨c, rfl⟩ := CycKLR.mk_surjective z
      change kOneTensorCoeffBar Q i β a h1 hβ _ _ =
        kOneTensorCoeffBar Q i β a h1 hβ m (CycKLR.mk k Q a β b * CycKLR.mk k Q a β c)
      rw [← map_mul, kOneTensorCoeffBar_mk, kOneTensorCoeffBar_mk]
      change Submodule.Quotient.mk (((m : R) * concat Q Si β (1 ⊗ₜ b)) *
        concat Q Si β (1 ⊗ₜ c)) = _
      rw [mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul])
    (by
      intro r m z
      obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
      change kOneTensorCoeffBar Q i β a h1 hβ (r • m) _ =
        r • kOneTensorCoeffBar Q i β a h1 hβ m _
      rw [kOneTensorCoeffBar_mk, kOneTensorCoeffBar_mk]
      change Submodule.Quotient.mk ((r * (m : R)) * concat Q Si β (1 ⊗ₜ b)) =
        Submodule.Quotient.mk (r * ((m : R) * concat Q Si β (1 ⊗ₜ b)))
      rw [mul_assoc])

theorem tensorToKOne_elem_mk (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) (m : M) (b : Rb) :
    tensorToKOne Q i β a h1 hβ (kOneTensorElem Q i β a m (CycKLR.mk k Q a β b)) =
      Submodule.Quotient.mk ((m : R) * concat Q Si β (1 ⊗ₜ b)) := by
  exact kOneTensorCoeffBar_mk Q i β a h1 hβ m b

/-- The comparison returns precisely the original elementary tensor. -/
theorem kOneToTensor_tensorToKOne (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) (t : KOneTensor Q i β a) :
    kOneToTensor Q i β a h1 hβ (tensorToKOne Q i β a h1 hβ t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m z =>
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
    rw [show BalancedTensor.tmul m (CycKLR.mk k Q a β b) =
      kOneTensorElem Q i β a m (CycKLR.mk k Q a β b) from rfl,
      tensorToKOne_elem_mk, kOneToTensor_mk, ← kOneTensorElem_mk]

/-- Right multiplication by the source idempotent on the uncut quotient. -/
def kOneRightCut (h1 : 1 < Multiset.card (Si + β)) :
    KOne Q (Si + β) a h1 →ₗ[R] KOne Q (Si + β) a h1 :=
  (cycL1 a h1).mapQ (cycL1 a h1) (LinearMap.toSpanSingleton R R (oneConcat Q Si β))
    (fun _ hr => mul_mem_cycL1 a hr (by
      rw [← concat_one]
      exact concat_mem_subR1 i β 1))

theorem kOneRightCut_mk (h1 : 1 < Multiset.card (Si + β)) (r : R) :
    kOneRightCut Q i β a h1 (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (r * oneConcat Q Si β) := rfl

/-- The other composite is the required right colour cut, not the identity on the uncut quotient. -/
theorem tensorToKOne_kOneToTensor (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) (z : KOne Q (Si + β) a h1) :
    tensorToKOne Q i β a h1 hβ (kOneToTensor Q i β a h1 hβ z) =
      kOneRightCut Q i β a h1 z := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [kOneToTensor_mk, kOneRightCut_mk]
  change tensorToKOne Q i β a h1 hβ
    (kOneTensorElem Q i β a (Graded.leftIdealProj oneConcat_idem r) 1) = _
  rw [← map_one (CycKLR.mk k Q a β), tensorToKOne_elem_mk,
    ← Algebra.TensorProduct.one_def, concat_one]
  change Submodule.Quotient.mk ((r * oneConcat Q Si β) * oneConcat Q Si β) = _
  rw [mul_assoc, oneConcat_idem.eq]

/-- The quotient-side presentation of the source's right idempotent summand. -/
abbrev KOneCorner (h1 : 1 < Multiset.card (Si + β)) : Type _ :=
  LinearMap.range (kOneRightCut Q i β a h1)

/-- A genuine balanced-tensor identification, with multiplication forward and `r e ⊗ 1` backward.
No domain, factorization or nontriviality assumption is needed for this presentation. -/
def kOneTensorEquiv (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) :
    KOneTensor Q i β a ≃ₗ[R] KOneCorner Q i β a h1 where
  toFun t := ⟨tensorToKOne Q i β a h1 hβ t,
    ⟨tensorToKOne Q i β a h1 hβ t, by
      rw [← tensorToKOne_kOneToTensor Q i β a h1 hβ,
        kOneToTensor_tensorToKOne]⟩⟩
  invFun z := kOneToTensor Q i β a h1 hβ z
  left_inv := kOneToTensor_tensorToKOne Q i β a h1 hβ
  right_inv z := by
    apply Subtype.ext
    change tensorToKOne Q i β a h1 hβ (kOneToTensor Q i β a h1 hβ z) = z
    rw [tensorToKOne_kOneToTensor]
    obtain ⟨w, hw⟩ := z.2
    rw [← hw, ← tensorToKOne_kOneToTensor Q i β a h1 hβ w,
      ← tensorToKOne_kOneToTensor Q i β a h1 hβ, kOneToTensor_tensorToKOne]
  map_add' t u := Subtype.ext (map_add _ _ _)
  map_smul' c t := Subtype.ext (map_smul _ _ _)

/-- The isomorphism has the prescribed multiplication on elementary tensors. -/
theorem kOneTensorEquiv_elem_mk (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) (m : M) (b : Rb) :
    (kOneTensorEquiv Q i β a h1 hβ
      (kOneTensorElem Q i β a m (CycKLR.mk k Q a β b)) : KOne Q (Si + β) a h1) =
      Submodule.Quotient.mk ((m : R) * concat Q Si β (1 ⊗ₜ b)) :=
  tensorToKOne_elem_mk Q i β a h1 hβ m b

/-- Right multiplication on the cyclotomic tensor coefficient. -/
def kOneTensorRight (z : Rl) : KOneTensor Q i β a →ₗ[R] KOneTensor Q i β a :=
  BalancedTensor.mapRight
    { toFun := fun w : Rl => w * z
      map_add' := fun u v => add_mul u v z
      map_smul' := fun b w => by
        change (CycKLR.mk k Q a β b * w) * z = CycKLR.mk k Q a β b * (w * z)
        rw [mul_assoc] }

theorem kOneTensorRight_elem (z w : Rl) (m : M) :
    kOneTensorRight Q i β a z (kOneTensorElem Q i β a m w) =
      kOneTensorElem Q i β a m (w * z) := rfl

/-- Actual right multiplication by a coefficient on the quotient presentation. -/
def kOneQuotientRight (h1 : 1 < Multiset.card (Si + β)) (b : Rb) :
    KOne Q (Si + β) a h1 →ₗ[R] KOne Q (Si + β) a h1 :=
  (cycL1 a h1).mapQ (cycL1 a h1)
    (LinearMap.toSpanSingleton R R (concat Q Si β (1 ⊗ₜ b)))
    (fun _ hr => mul_mem_cycL1 a hr (concat_mem_subR1 i β _))

theorem kOneQuotientRight_mk (h1 : 1 < Multiset.card (Si + β)) (b : Rb) (r : R) :
    kOneQuotientRight Q i β a h1 b (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (r * concat Q Si β (1 ⊗ₜ b)) := rfl

/-- The tensor comparison respects the specified right coefficient action, not just left linearity. -/
theorem tensorToKOne_right (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) (b : Rb) (t : KOneTensor Q i β a) :
    tensorToKOne Q i β a h1 hβ (kOneTensorRight Q i β a (CycKLR.mk k Q a β b) t) =
      kOneQuotientRight Q i β a h1 b (tensorToKOne Q i β a h1 hβ t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m z =>
    obtain ⟨c, rfl⟩ := CycKLR.mk_surjective z
    change tensorToKOne Q i β a h1 hβ
      (kOneTensorElem Q i β a m (CycKLR.mk k Q a β c * CycKLR.mk k Q a β b)) =
        kOneQuotientRight Q i β a h1 b (tensorToKOne Q i β a h1 hβ
          (kOneTensorElem Q i β a m (CycKLR.mk k Q a β c)))
    rw [← map_mul, tensorToKOne_elem_mk, tensorToKOne_elem_mk, kOneQuotientRight_mk,
      mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Categorification.KLR.KLRAlgebra
