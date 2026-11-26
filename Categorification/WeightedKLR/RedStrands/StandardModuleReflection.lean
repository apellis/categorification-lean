/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardViolatedDescent
import Categorification.WeightedKLR.RedStrands.AppendStrandReflection

/-!
# Webster's right standard modules and the left standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Definition 5.1. Webster's standard module `S_s = e(s) T̃^λ / U_s` is a right `T̃^λ`-module
(`StendhalAlgebra.standardModule`); the filtrations of §5 in this library use the left standard
module `T^λ e(s) / U_s` (`leftStandard`). For a sequence `s` whose first strand is red, the two
are exchanged by the horizontal reflection: `[y] ↦ [flip(y)]` is a `k`-linear isomorphism
`S_s ≅ leftStandard s` with `[y a] ↦ flip(a) [flip(y)]` (`standardModuleReflect`,
`standardModuleReflect_op_smul`). Injectivity uses that the violating ideal acts by zero on
`S_s` (`e_mul_mem_upperSubmodule_of_mem_violatedIdeal`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "A" => StendhalAlgebra k Q Λ ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "mk" => TensorProductAlgebra.mk Q Λ ν

namespace StendhalAlgebra

variable (s : KLR.Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)

theorem tensorProductAlgebra_mk_surjective :
    Function.Surjective (TensorProductAlgebra.mk (k := k) Q Λ ν) :=
  (violatedIdeal k Q Λ ν).ringCon.mk'_surjective

theorem tensorFlip_mk_mul_seqIdem (y : A) :
    tensorFlip (mk (StendhalAlgebra.e s hs * y)) * seqIdem Q Λ s hs = tensorFlip (mk (StendhalAlgebra.e s hs * y)) := by
  rw [map_mul, tensorFlip_mul, tensorFlip_mk_e, mul_assoc, seqIdem_mul_self]

/-- `y ↦ flip(e(s) y)`, a `k`-linear map `T̃^λ → T^λ e(s)`. -/
def reflectToLIdeal : A →ₗ[k] lIdeal (seqIdem Q Λ s hs) where
  toFun y := ⟨tensorFlip (mk (StendhalAlgebra.e s hs * y)), tensorFlip_mk_mul_seqIdem s hs y⟩
  map_add' y y' := Subtype.ext (by
    change tensorFlip (mk (StendhalAlgebra.e s hs * (y + y'))) = tensorFlip (mk (StendhalAlgebra.e s hs * y)) +
      tensorFlip (mk (StendhalAlgebra.e s hs * y'))
    rw [mul_add, map_add, map_add])
  map_smul' c y := Subtype.ext
    ((tensorFlip ∘ₗ (TensorProductAlgebra.mk Q Λ ν).toLinearMap ∘ₗ
      LinearMap.mulLeft k (StendhalAlgebra.e s hs)).map_smul c y)

/-- Elements of `leftUpper` reflect into the image of `U_s`. -/
theorem exists_mem_upperSubmodule_of_mem_leftUpper {x : T} (hx : x ∈ leftUpper Q Λ s hs) :
    ∃ y ∈ upperSubmodule Q Λ s hs, mk y = tensorFlip x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, a, hlt, rfl⟩ := hx
    obtain ⟨a', ha'⟩ := tensorProductAlgebra_mk_surjective (tensorFlip a)
    refine ⟨StendhalAlgebra.e s hs * a' * StendhalAlgebra.e t ht, Submodule.subset_span ⟨t, ht, a', hlt, rfl⟩, ?_⟩
    rw [tensorFlip_mul, tensorFlip_mul, tensorFlip_mk_e, tensorFlip_mk_e, map_mul, map_mul, ha',
      mul_assoc]
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨y', hy', hxy'⟩ := hx'
    exact ⟨y + y', add_mem hy hy', by rw [map_add, map_add, hxy, hxy']⟩
  | smul c x _ hx =>
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨c', hc'⟩ := tensorProductAlgebra_mk_surjective (tensorFlip c)
    refine ⟨y * c', ?_, ?_⟩
    · exact Submodule.smul_mem _ (op c') hy
    · rw [smul_eq_mul, tensorFlip_mul, map_mul, hxy, hc']

theorem tensorMk_eq_zero_iff (x : A) : mk x = 0 ↔ x ∈ violatedIdeal k Q Λ ν := by
  change (violatedIdeal k Q Λ ν).ringCon.mk' x = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

theorem e_mul_of_mem_seqProj {y : A} (hy : y ∈ seqProj Q Λ s hs) :
    StendhalAlgebra.e s hs * y = y := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [← MulOpposite.op_unop a, op_smul_eq_mul, ← mul_assoc, e_mul_e_self]

theorem e_mul_of_mem_upperSubmodule {y : A} (hy : y ∈ upperSubmodule Q Λ s hs) :
    StendhalAlgebra.e s hs * y = y :=
  e_mul_of_mem_seqProj s hs (upperSubmodule_le_seqProj s hs hy)

/-- `U_s` reflects into `leftUpper`. -/
theorem tensorFlip_mk_mem_leftUpper {y : A} (hy : y ∈ upperSubmodule Q Λ s hs) :
    tensorFlip (mk y) ∈ leftUpper Q Λ s hs := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, a, hlt, rfl⟩ := hy
    refine Submodule.subset_span ⟨t, ht, tensorFlip (mk a), hlt, ?_⟩
    rw [map_mul, tensorFlip_mul, map_mul, tensorFlip_mul, tensorFlip_mk_e, tensorFlip_mk_e,
      mul_assoc]
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [map_add, map_add]; exact add_mem hy hy'
  | smul c y _ hy =>
    rw [← MulOpposite.op_unop c, op_smul_eq_mul, map_mul, tensorFlip_mul]
    exact Submodule.smul_mem _ _ hy

/-- `y ↦ [flip(e(s) y)]`, a `k`-linear map `T̃^λ → S^L_s`. -/
def reflectToLeftStandard : A →ₗ[k] leftStandard Q Λ s hs :=
  ((leftUpper Q Λ s hs).comap (lIdeal (seqIdem Q Λ s hs)).subtype).mkQ.restrictScalars k ∘ₗ
    reflectToLIdeal s hs

theorem reflectToLeftStandard_apply (y : A) :
    reflectToLeftStandard s hs y = Submodule.Quotient.mk (reflectToLIdeal s hs y) := rfl

theorem upperSubmodule_le_ker_reflectToLeftStandard :
    (upperSubmodule Q Λ s hs).restrictScalars k ≤
      LinearMap.ker (reflectToLeftStandard s hs) := by
  intro y hy
  rw [LinearMap.mem_ker, reflectToLeftStandard_apply, Submodule.Quotient.mk_eq_zero]
  change tensorFlip (mk (StendhalAlgebra.e s hs * y)) ∈ leftUpper Q Λ s hs
  rw [e_mul_of_mem_upperSubmodule s hs hy]
  exact tensorFlip_mk_mem_leftUpper s hs hy

/-- The reflection `T̃^λ / U_s → S^L_s`, `[y] ↦ [flip(e(s) y)]`. -/
def reflectQuotient : (A ⧸ upperSubmodule Q Λ s hs) →ₗ[k] leftStandard Q Λ s hs :=
  ((upperSubmodule Q Λ s hs).restrictScalars k).liftQ (reflectToLeftStandard s hs)
      (upperSubmodule_le_ker_reflectToLeftStandard s hs) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (upperSubmodule Q Λ s hs)).symm.toLinearMap

theorem reflectQuotient_mk (y : A) :
    reflectQuotient s hs (Submodule.Quotient.mk y) = reflectToLeftStandard s hs y := rfl

/-- **Webster's right standard module and the left standard module.** The horizontal
reflection `[y] ↦ [flip(y)]`, as a `k`-linear map `S_s → T^λ e(s) / U_s`. -/
def standardModuleReflect :
    standardModule Q Λ s hs →ₗ[k] leftStandard Q Λ s hs :=
  reflectQuotient s hs ∘ₗ (standardModule Q Λ s hs).subtype.restrictScalars k

theorem standardModuleReflect_mk (y : A) (hy : (Submodule.Quotient.mk y :
    A ⧸ upperSubmodule Q Λ s hs) ∈ standardModule Q Λ s hs) :
    standardModuleReflect s hs ⟨_, hy⟩ = reflectToLeftStandard s hs y := rfl

theorem exists_mk_of_mem_standardModule (v : standardModule Q Λ s hs) :
    ∃ y ∈ seqProj Q Λ s hs, (v : A ⧸ upperSubmodule Q Λ s hs) = Submodule.Quotient.mk y := by
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := v
  exact ⟨y, hy, rfl⟩

theorem reflectToLeftStandard_mul (y a : A) :
    reflectToLeftStandard s hs (y * a) = tensorFlip (mk a) • reflectToLeftStandard s hs y := by
  rw [reflectToLeftStandard_apply, reflectToLeftStandard_apply, ← Submodule.Quotient.mk_smul]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  change tensorFlip (mk (StendhalAlgebra.e s hs * (y * a))) =
    tensorFlip (mk a) * tensorFlip (mk (StendhalAlgebra.e s hs * y))
  rw [← mul_assoc, map_mul, tensorFlip_mul]

theorem standardModuleReflect_apply (v : standardModule Q Λ s hs) :
    standardModuleReflect s hs v = reflectQuotient s hs (v : A ⧸ upperSubmodule Q Λ s hs) := rfl

/-- The reflection is twisted linear: `[y a] ↦ flip(a) [flip(y)]`. -/
theorem standardModuleReflect_op_smul (a : A) (v : standardModule Q Λ s hs) :
    standardModuleReflect s hs (op a • v) = tensorFlip (mk a) • standardModuleReflect s hs v := by
  obtain ⟨y, -, hv⟩ := exists_mk_of_mem_standardModule s hs v
  have hv' : ((op a • v : standardModule Q Λ s hs) : A ⧸ upperSubmodule Q Λ s hs) =
      Submodule.Quotient.mk (y * a) := by
    rw [Submodule.coe_smul, hv, ← Submodule.Quotient.mk_smul, op_smul_eq_mul]
  rw [standardModuleReflect_apply, standardModuleReflect_apply, hv', hv, reflectQuotient_mk,
    reflectQuotient_mk, reflectToLeftStandard_mul]

/-- The class `[e(s)]` of Webster's standard module. -/
def standardModuleUnit : standardModule Q Λ s hs :=
  ⟨Submodule.Quotient.mk (StendhalAlgebra.e s hs), Submodule.mem_map_of_mem
    (Submodule.subset_span rfl)⟩

theorem standardModuleReflect_unit :
    standardModuleReflect s hs (standardModuleUnit s hs) = leftStandardUnit Q Λ s hs := by
  change reflectToLeftStandard s hs _ = _
  rw [reflectToLeftStandard_apply, leftStandardUnit]
  congr 1
  apply Subtype.ext
  change tensorFlip (mk (StendhalAlgebra.e s hs * StendhalAlgebra.e s hs)) = seqIdem Q Λ s hs
  rw [e_mul_e_self, tensorFlip_mk_e]

theorem standardModuleReflect_surjective :
    Function.Surjective (standardModuleReflect (Q := Q) (Λ := Λ) s hs) := by
  intro w
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨y, hy⟩ := tensorProductAlgebra_mk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    (tensorFlip (z : T))
  have hmem : (Submodule.Quotient.mk (StendhalAlgebra.e s hs * y) :
      A ⧸ upperSubmodule Q Λ s hs) ∈ standardModule Q Λ s hs := by
    refine Submodule.mem_map_of_mem ?_
    rw [← op_smul_eq_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [standardModuleReflect_mk, reflectToLeftStandard_apply]
  congr 1
  apply Subtype.ext
  change tensorFlip (mk (StendhalAlgebra.e s hs * (StendhalAlgebra.e s hs * y))) = z
  rw [← mul_assoc, e_mul_e_self, map_mul, tensorFlip_mul, hy, tensorFlip_tensorFlip,
    tensorFlip_mk_e]
  exact (mem_lIdeal.1 z.2)

/-- Injectivity: the violating ideal acts by zero on `S_s` when the first strand of `s` is
red (`e_mul_mem_upperSubmodule_of_mem_violatedIdeal`). -/
theorem standardModuleReflect_injective (hsv : ¬ IsViolated s) :
    Function.Injective (standardModuleReflect (Q := Q) (Λ := Λ) s hs) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨y, hy, hvy⟩ := exists_mk_of_mem_standardModule s hs v
  apply Subtype.ext
  rw [Submodule.coe_zero, hvy, Submodule.Quotient.mk_eq_zero]
  have h0 : reflectToLeftStandard s hs y = 0 := by
    rw [← hv]; change _ = reflectQuotient s hs (v : A ⧸ upperSubmodule Q Λ s hs); rw [hvy]; rfl
  rw [reflectToLeftStandard_apply, Submodule.Quotient.mk_eq_zero] at h0
  change tensorFlip (mk (StendhalAlgebra.e s hs * y)) ∈ leftUpper Q Λ s hs at h0
  rw [e_mul_of_mem_seqProj s hs hy] at h0
  obtain ⟨y', hy', hyy'⟩ := exists_mem_upperSubmodule_of_mem_leftUpper s hs h0
  rw [tensorFlip_tensorFlip] at hyy'
  have hK : y - y' ∈ violatedIdeal k Q Λ ν := by
    rw [← tensorMk_eq_zero_iff, map_sub, hyy', sub_self]
  have := e_mul_mem_upperSubmodule_of_mem_violatedIdeal hs hsv hK
  rw [mul_sub, e_mul_of_mem_seqProj s hs hy, e_mul_of_mem_upperSubmodule s hs hy'] at this
  simpa using add_mem this hy'

/-- **Webster's standard module as the reflected left standard module**: for `s` whose first
strand is red, the horizontal reflection is a `k`-linear isomorphism `S_s ≅ T^λ e(s) / U_s`
sending `[e(s)]` to `[e(s)]` and `[y a]` to `flip(a) [flip(y)]`. -/
def standardModuleReflectEquiv (hsv : ¬ IsViolated s) :
    standardModule Q Λ s hs ≃ₗ[k] leftStandard Q Λ s hs :=
  LinearEquiv.ofBijective (standardModuleReflect s hs)
    ⟨standardModuleReflect_injective s hs hsv, standardModuleReflect_surjective s hs⟩

end StendhalAlgebra

end Categorification.Stendhal
