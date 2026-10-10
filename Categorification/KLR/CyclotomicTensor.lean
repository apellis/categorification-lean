/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicK0

/-!
# The balanced tensor presentation of the cyclotomic induction module

Kang–Kashiwara, arXiv:1102.4677v4, §4.2 uses
`R(β + α_i)e(β,i) ⊗_{R(β)} R^Λ(β)`. Here the tensor product is balanced
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
local notation "R" => KLRAlgebra k Q (β + Si)
local notation "Ri" => KLRAlgebra k Q Si
local notation "M" => IndBimod Q β Si
local notation "Rl" => CycKLR k Q a β

/-- Restrict the right concatenation action to `R(β)`. -/
local instance : Module Rbᵐᵒᵖ M :=
  Module.compHom M (Algebra.TensorProduct.includeLeft : Rb →ₐ[k] Rb ⊗[k] Ri).toRingHom.op

local instance : IsScalarTower k Rbᵐᵒᵖ M where
  smul_assoc c b m := Subtype.ext (by
    change (m : R) * concat Q β Si ((c • b.unop) ⊗ₜ 1) =
      c • ((m : R) * concat Q β Si (b.unop ⊗ₜ 1))
    rw [← TensorProduct.smul_tmul', map_smul, mul_smul_comm])

local instance : SMulCommClass R Rbᵐᵒᵖ M where
  smul_comm r b m := Subtype.ext (by
    change r * ((m : R) * concat Q β Si (b.unop ⊗ₜ 1)) =
      (r * m) * concat Q β Si (b.unop ⊗ₜ 1)
    rw [mul_assoc])

local instance : Module Rb Rl := Module.compHom Rl (CycKLR.mk k Q a β).toRingHom

local instance : IsScalarTower k Rb Rl where
  smul_assoc c b z := by
    change (CycKLR.mk k Q a β (c • b)) * z = c • (CycKLR.mk k Q a β b * z)
    rw [map_smul, smul_mul_assoc]

/-- The source's actual balanced induction tensor, before the left colour cut. -/
abbrev KZeroTensor : Type _ := BalancedTensor k R Rb M Rl

/-- The elementary tensor represented by a corner element and a cyclotomic coefficient. -/
def kZeroTensorElem (m : M) (z : Rl) : KZeroTensor Q i β a := BalancedTensor.tmul m z

/-- The unit tensor `r e(β,i) ⊗ 1`. -/
def kZeroTensorUnit : R →ₗ[R] KZeroTensor Q i β a :=
  { toFun r := kZeroTensorElem Q i β a (Graded.leftIdealProj oneConcat_idem r) 1
    map_add' r s := by simp [kZeroTensorElem, map_add, BalancedTensor.add_tmul]
    map_smul' r s := by
      rw [map_smul]
      exact (BalancedTensor.smul_tmul' r _ _).symm }

/-- Balancing uses precisely the concatenation action on the corner. -/
theorem kZeroTensor_balance (m : M) (b : Rb) (z : Rl) :
    kZeroTensorElem Q i β a
        ⟨(m : R) * concat Q β Si (b ⊗ₜ 1), mul_concat_mem m _⟩ z =
      kZeroTensorElem Q i β a m (CycKLR.mk k Q a β b * z) :=
  BalancedTensor.op_smul_tmul m b z

/-- Every elementary tensor is a unit tensor after lifting its cyclotomic coefficient. -/
theorem kZeroTensorElem_mk (m : M) (b : Rb) :
    kZeroTensorElem Q i β a m (CycKLR.mk k Q a β b) =
      kZeroTensorUnit Q i β a ((m : R) * concat Q β Si (b ⊗ₜ 1)) := by
  rw [← mul_one (CycKLR.mk k Q a β b), ← kZeroTensor_balance]
  congr 1
  apply Subtype.ext
  exact (mul_concat_mem m _).symm

/-- The unit-tensor map ignores the complementary right idempotent. -/
theorem kZeroTensorUnit_cut (r : R) :
    kZeroTensorUnit Q i β a (r * oneConcat Q β Si) = kZeroTensorUnit Q i β a r := by
  change kZeroTensorElem Q i β a _ 1 = kZeroTensorElem Q i β a _ 1
  congr 1
  apply Subtype.ext
  change (r * oneConcat Q β Si) * oneConcat Q β Si = r * oneConcat Q β Si
  rw [mul_assoc, oneConcat_idem.eq]

/-- An elementary concatenation transfers its `R(β)` coefficient across the tensor. -/
theorem kZeroTensorUnit_concat_tmul (b : Rb) (c : Ri) :
    kZeroTensorUnit Q i β a (concat Q β Si (b ⊗ₜ c)) =
      kZeroTensorElem Q i β a
        ⟨concat Q β Si (1 ⊗ₜ c), concat_mul_oneConcat _⟩ (CycKLR.mk k Q a β b) := by
  rw [kZeroTensorElem_mk, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- A cyclotomic coefficient vanishes by balancing, rather than by choosing a linear inverse. -/
theorem kZeroTensorUnit_concat_eq_zero {t : Rb ⊗[k] Ri}
    (ht : t ∈ tJ0 (Q := Q) i β a) :
    kZeroTensorUnit Q i β a (concat Q β Si t) = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨b, c, hb, rfl⟩ := ht
    rw [kZeroTensorUnit_concat_tmul, (CycKLR.mk_eq_zero_iff _).2 hb]
    exact BalancedTensor.tmul_zero _
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.map_smul_of_tower, hx, smul_zero]

/-- The genuine tensor relation kills the left-ideal presentation of `K₀`. -/
theorem kZeroTensorUnit_eq_zero (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) {r : R} (hr : r ∈ cycL0 a h0) :
    kZeroTensorUnit Q i β a r = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨w, hw, rfl⟩ := hr
    obtain ⟨t, ht⟩ := exists_concat_of_subR0 (Q := Q) i β hw
    rw [← kZeroTensorUnit_cut, mul_assoc, ht,
      ← oneConcat_mul_concat (Q := Q) (t := t), ← mul_assoc,
      cycAt_zero_mul_oneConcat i β a h0 hβ, ← concat_mul]
    apply kZeroTensorUnit_concat_eq_zero
    apply tJ0_mul_mem
    exact Submodule.subset_span ⟨cycAt a ⟨0, hβ⟩, 1, cycAt_mem_cycIdeal a hβ, rfl⟩
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- The canonical map from the quotient presentation to the source's balanced tensor. -/
def kZeroToTensor (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) :
    KZero Q (β + Si) a h0 →ₗ[R] KZeroTensor Q i β a :=
  (cycL0 a h0).liftQ (kZeroTensorUnit Q i β a)
    (fun _ hr => LinearMap.mem_ker.mpr (kZeroTensorUnit_eq_zero Q i β a h0 hβ hr))

theorem kZeroToTensor_mk (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) (r : R) :
    kZeroToTensor Q i β a h0 hβ (Submodule.Quotient.mk r) = kZeroTensorUnit Q i β a r := rfl

/-- Multiplication on the original corner, with coefficients before quotienting. -/
def kZeroTensorCoeff (h0 : 0 < Multiset.card (β + Si)) (m : M) :
    Rb →ₗ[k] KZero Q (β + Si) a h0 where
  toFun b := Submodule.Quotient.mk ((m : R) * concat Q β Si (b ⊗ₜ 1))
  map_add' b c := by simp only [TensorProduct.add_tmul, map_add, mul_add, Submodule.Quotient.mk_add]
  map_smul' c b := by
    simp only [← TensorProduct.smul_tmul', map_smul, mul_smul_comm, RingHom.id_apply]
    rfl

private theorem cycMkLin_surjective : Function.Surjective (CycKLR.mk k Q a β).toLinearMap :=
  CycKLR.mk_surjective

/-- Descend multiplication through the actual cyclotomic quotient. -/
def kZeroTensorCoeffBar (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) (m : M) :
    Rl →ₗ[k] KZero Q (β + Si) a h0 :=
  (LinearMap.ker (CycKLR.mk k Q a β).toLinearMap).liftQ (kZeroTensorCoeff Q i β a h0 m)
    (by
      intro b hb
      change Submodule.Quotient.mk ((m : R) * concat Q β Si (b ⊗ₜ 1)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      apply Submodule.smul_mem (cycL0 a h0) (m : R)
      apply concat_mem_cycL0 i β a h0 hβ
      exact Submodule.subset_span ⟨b, 1, (CycKLR.mk_eq_zero_iff b).1 hb, rfl⟩) ∘ₗ
    ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
      (cycMkLin_surjective Q β a)).symm.toLinearMap

theorem kZeroTensorCoeffBar_mk (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) (m : M) (b : Rb) :
    kZeroTensorCoeffBar Q i β a h0 hβ m (CycKLR.mk k Q a β b) =
      Submodule.Quotient.mk ((m : R) * concat Q β Si (b ⊗ₜ 1)) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (CycKLR.mk k Q a β).toLinearMap (cycMkLin_surjective Q β a) b
  change ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
    (cycMkLin_surjective Q β a)).symm (CycKLR.mk k Q a β b) = _ at he
  rw [kZeroTensorCoeffBar, LinearMap.comp_apply, LinearEquiv.coe_coe, he,
    Submodule.liftQ_apply]
  rfl

/-- The descended bilinear multiplication map. -/
def kZeroTensorBil (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) :
    M →ₗ[k] Rl →ₗ[k] KZero Q (β + Si) a h0 where
  toFun := kZeroTensorCoeffBar Q i β a h0 hβ
  map_add' m n := by
    ext z
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
    simp only [LinearMap.add_apply, kZeroTensorCoeffBar_mk, Submodule.coe_add,
      add_mul, Submodule.Quotient.mk_add]
  map_smul' c m := by
    ext z
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
    simp only [LinearMap.smul_apply, RingHom.id_apply, kZeroTensorCoeffBar_mk]
    change Submodule.Quotient.mk ((c • (m : R)) * concat Q β Si (b ⊗ₜ 1)) = _
    rw [smul_mul_assoc]
    rfl

/-- The canonical multiplication from the source's balanced tensor to its quotient model. -/
def tensorToKZero (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) :
    KZeroTensor Q i β a →ₗ[R] KZero Q (β + Si) a h0 :=
  BalancedTensor.liftB (kZeroTensorBil Q i β a h0 hβ)
    (by
      intro m b z
      obtain ⟨c, rfl⟩ := CycKLR.mk_surjective z
      change kZeroTensorCoeffBar Q i β a h0 hβ _ _ =
        kZeroTensorCoeffBar Q i β a h0 hβ m (CycKLR.mk k Q a β b * CycKLR.mk k Q a β c)
      rw [← map_mul, kZeroTensorCoeffBar_mk, kZeroTensorCoeffBar_mk]
      change Submodule.Quotient.mk (((m : R) * concat Q β Si (b ⊗ₜ 1)) *
        concat Q β Si (c ⊗ₜ 1)) = _
      rw [mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul])
    (by
      intro r m z
      obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
      change kZeroTensorCoeffBar Q i β a h0 hβ (r • m) _ =
        r • kZeroTensorCoeffBar Q i β a h0 hβ m _
      rw [kZeroTensorCoeffBar_mk, kZeroTensorCoeffBar_mk]
      change Submodule.Quotient.mk ((r * (m : R)) * concat Q β Si (b ⊗ₜ 1)) =
        Submodule.Quotient.mk (r * ((m : R) * concat Q β Si (b ⊗ₜ 1)))
      rw [mul_assoc])

theorem tensorToKZero_elem_mk (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) (m : M) (b : Rb) :
    tensorToKZero Q i β a h0 hβ (kZeroTensorElem Q i β a m (CycKLR.mk k Q a β b)) =
      Submodule.Quotient.mk ((m : R) * concat Q β Si (b ⊗ₜ 1)) := by
  exact kZeroTensorCoeffBar_mk Q i β a h0 hβ m b

/-- The comparison returns precisely the original elementary tensor. -/
theorem kZeroToTensor_tensorToKZero (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) (t : KZeroTensor Q i β a) :
    kZeroToTensor Q i β a h0 hβ (tensorToKZero Q i β a h0 hβ t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m z =>
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective z
    rw [show BalancedTensor.tmul m (CycKLR.mk k Q a β b) =
      kZeroTensorElem Q i β a m (CycKLR.mk k Q a β b) from rfl,
      tensorToKZero_elem_mk, kZeroToTensor_mk, ← kZeroTensorElem_mk]

/-- Right multiplication by the source idempotent on the uncut quotient. -/
def kZeroRightCut (h0 : 0 < Multiset.card (β + Si)) :
    KZero Q (β + Si) a h0 →ₗ[R] KZero Q (β + Si) a h0 :=
  (cycL0 a h0).mapQ (cycL0 a h0) (LinearMap.toSpanSingleton R R (oneConcat Q β Si))
    (fun _ hr => mul_mem_cycL0 a hr (by
      rw [← concat_one]
      exact concat_mem_subR0 i β 1))

theorem kZeroRightCut_mk (h0 : 0 < Multiset.card (β + Si)) (r : R) :
    kZeroRightCut Q i β a h0 (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (r * oneConcat Q β Si) := rfl

/-- The other composite is the required right colour cut, not the identity on the uncut quotient. -/
theorem tensorToKZero_kZeroToTensor (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) (z : KZero Q (β + Si) a h0) :
    tensorToKZero Q i β a h0 hβ (kZeroToTensor Q i β a h0 hβ z) =
      kZeroRightCut Q i β a h0 z := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [kZeroToTensor_mk, kZeroRightCut_mk]
  change tensorToKZero Q i β a h0 hβ
    (kZeroTensorElem Q i β a (Graded.leftIdealProj oneConcat_idem r) 1) = _
  rw [← map_one (CycKLR.mk k Q a β), tensorToKZero_elem_mk,
    ← Algebra.TensorProduct.one_def, concat_one]
  change Submodule.Quotient.mk ((r * oneConcat Q β Si) * oneConcat Q β Si) = _
  rw [mul_assoc, oneConcat_idem.eq]

/-- The quotient-side presentation of the source's right idempotent summand. -/
abbrev KZeroCorner (h0 : 0 < Multiset.card (β + Si)) : Type _ :=
  LinearMap.range (kZeroRightCut Q i β a h0)

/-- A genuine balanced-tensor identification, with multiplication forward and `r e ⊗ 1` backward.
No domain, factorization or nontriviality assumption is needed for this presentation. -/
def kZeroTensorEquiv (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) :
    KZeroTensor Q i β a ≃ₗ[R] KZeroCorner Q i β a h0 where
  toFun t := ⟨tensorToKZero Q i β a h0 hβ t,
    ⟨tensorToKZero Q i β a h0 hβ t, by
      rw [← tensorToKZero_kZeroToTensor Q i β a h0 hβ,
        kZeroToTensor_tensorToKZero]⟩⟩
  invFun z := kZeroToTensor Q i β a h0 hβ z
  left_inv := kZeroToTensor_tensorToKZero Q i β a h0 hβ
  right_inv z := by
    apply Subtype.ext
    change tensorToKZero Q i β a h0 hβ (kZeroToTensor Q i β a h0 hβ z) = z
    rw [tensorToKZero_kZeroToTensor]
    obtain ⟨w, hw⟩ := z.2
    rw [← hw, ← tensorToKZero_kZeroToTensor Q i β a h0 hβ w,
      ← tensorToKZero_kZeroToTensor Q i β a h0 hβ, kZeroToTensor_tensorToKZero]
  map_add' t u := Subtype.ext (map_add _ _ _)
  map_smul' c t := Subtype.ext (map_smul _ _ _)

/-- The isomorphism has the prescribed multiplication on elementary tensors. -/
theorem kZeroTensorEquiv_elem_mk (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) (m : M) (b : Rb) :
    (kZeroTensorEquiv Q i β a h0 hβ
      (kZeroTensorElem Q i β a m (CycKLR.mk k Q a β b)) : KZero Q (β + Si) a h0) =
      Submodule.Quotient.mk ((m : R) * concat Q β Si (b ⊗ₜ 1)) :=
  tensorToKZero_elem_mk Q i β a h0 hβ m b

/-- Right multiplication on the cyclotomic tensor coefficient. -/
def kZeroTensorRight (z : Rl) : KZeroTensor Q i β a →ₗ[R] KZeroTensor Q i β a :=
  BalancedTensor.mapRight
    { toFun := fun w : Rl => w * z
      map_add' := fun u v => add_mul u v z
      map_smul' := fun b w => by
        change (CycKLR.mk k Q a β b * w) * z = CycKLR.mk k Q a β b * (w * z)
        rw [mul_assoc] }

theorem kZeroTensorRight_elem (z w : Rl) (m : M) :
    kZeroTensorRight Q i β a z (kZeroTensorElem Q i β a m w) =
      kZeroTensorElem Q i β a m (w * z) := rfl

/-- Actual right multiplication by a coefficient on the quotient presentation. -/
def kZeroQuotientRight (h0 : 0 < Multiset.card (β + Si)) (b : Rb) :
    KZero Q (β + Si) a h0 →ₗ[R] KZero Q (β + Si) a h0 :=
  (cycL0 a h0).mapQ (cycL0 a h0)
    (LinearMap.toSpanSingleton R R (concat Q β Si (b ⊗ₜ 1)))
    (fun _ hr => mul_mem_cycL0 a hr (concat_mem_subR0 i β _))

theorem kZeroQuotientRight_mk (h0 : 0 < Multiset.card (β + Si)) (b : Rb) (r : R) :
    kZeroQuotientRight Q i β a h0 b (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (r * concat Q β Si (b ⊗ₜ 1)) := rfl

/-- The tensor comparison respects the specified right coefficient action, not just left linearity. -/
theorem tensorToKZero_right (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) (b : Rb) (t : KZeroTensor Q i β a) :
    tensorToKZero Q i β a h0 hβ (kZeroTensorRight Q i β a (CycKLR.mk k Q a β b) t) =
      kZeroQuotientRight Q i β a h0 b (tensorToKZero Q i β a h0 hβ t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m z =>
    obtain ⟨c, rfl⟩ := CycKLR.mk_surjective z
    change tensorToKZero Q i β a h0 hβ
      (kZeroTensorElem Q i β a m (CycKLR.mk k Q a β c * CycKLR.mk k Q a β b)) =
        kZeroQuotientRight Q i β a h0 b (tensorToKZero Q i β a h0 hβ
          (kZeroTensorElem Q i β a m (CycKLR.mk k Q a β c)))
    rw [← map_mul, tensorToKZero_elem_mk, tensorToKZero_elem_mk, kZeroQuotientRight_mk,
      mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Categorification.KLR.KLRAlgebra
