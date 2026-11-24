/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleCap

/-!
# The simple head at the fundamental cut (0,1)

Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3. The projective with its black
strand between the two red strands has a unique simple quotient. Its kernel
is the sum of the images from the projective at the smaller cut (0,0).
The scalar dual of the left middle character realizes this right quotient.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open Coevaluation MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "p" => terminalIdem
local notation "q" => middleIdem

private theorem middle_idempotent : IsIdempotentElem q :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, StendhalAlgebraAllOrders.e_mul_e]) project

/-- On the middle corner the character is the coefficient of its loading idempotent. -/
theorem middle_mul_middle (x : rIdeal q) : x.val * q = middleCharacter x.val • q := by
  obtain ⟨c, hc⟩ := (fundamental_middle_corner_coordinates x.val).1
  change q * x.val * q = c • q at hc
  rw [x.property] at hc
  have h := congrArg middleCharacter hc
  simp only [map_mul, middleCharacter_middleIdem, mul_one, map_smul, smul_eq_mul] at h
  rw [hc, h]

/-- The trace of the smaller cut in the projective at (0,1). -/
abbrev middleCutTrace : Submodule Tᵐᵒᵖ (rIdeal q) := coevaluationTrace (fun _ : Unit => p)

theorem mem_middleCutTrace_iff (x : rIdeal q) :
    x ∈ middleCutTrace ↔ middleCharacter x.val = 0 := by
  constructor
  · intro hx
    exact coevaluationTrace_le_characterKernel _ middleCharacter.toRingHom (fun _ => middleCharacter_terminalIdem) hx
  · intro hx
    apply Submodule.subset_span
    refine ⟨(), ?_⟩
    have hq : x.val * q = 0 := by rw [middle_mul_middle, hx, zero_smul]
    calc
      x.val * p = x.val * p + x.val * q := by rw [hq, add_zero]
      _ = x.val := by rw [← mul_add, terminalIdem_add_middleIdem, mul_one]

/-- The displayed trace is exactly the unique simple-quotient kernel at the cut (0,1). -/
theorem middleCutTrace_eq_iff_simpleQuotient (N : Submodule Tᵐᵒᵖ (rIdeal q)) :
    N = middleCutTrace ↔ IsSimpleModule Tᵐᵒᵖ (rIdeal q ⧸ N) := by
  apply coevaluationTrace_eq_iff_simpleQuotient middle_idempotent _ middleCharacter.toRingHom
    middleCharacter_middleIdem (fun _ => middleCharacter_terminalIdem) (fun x => (mem_middleCutTrace_iff x).mpr)
  intro x hx
  change middleCharacter x.val ≠ 0 at hx
  refine ⟨(middleCharacter x.val)⁻¹ • q, ?_⟩
  rw [mul_smul_comm, middle_mul_middle, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- The coefficient of the middle generator in the simple quotient. -/
def middleCoefficient : rIdeal q →ₗ[ℚ] ℚ where
  toFun z := middleCharacter z.val
  map_add' x y := middleCharacter.map_add x.val y.val
  map_smul' c x := middleCharacter.toLinearMap.map_smul c x.val

/-- The coefficient of the middle generating vector is one. -/
@[simp] theorem middleCoefficient_generator :
    middleCoefficient (⟨q, middle_idempotent.eq⟩ : rIdeal q) = 1 :=
  middleCharacter_middleIdem

/-- The coefficient map is surjective onto the ground field. -/
theorem middleCoefficient_surjective : Function.Surjective middleCoefficient := by
  intro c
  refine ⟨c • (⟨q, middle_idempotent.eq⟩ : rIdeal q), ?_⟩
  rw [map_smul, middleCoefficient_generator, smul_eq_mul, mul_one]

/-- The dual coefficient carries the right action by the same character. -/
theorem middleDual_smul_apply (a : T)
    (f : CupCoefficient ℚ MiddleCoefficient) (x : MiddleCoefficient) :
    (show Module.Dual ℚ MiddleCoefficient from op a • f) x =
      middleCharacter a * (show Module.Dual ℚ MiddleCoefficient from f) x := by
  rw [cup_op_smul_apply]
  exact map_smul (show Module.Dual ℚ MiddleCoefficient from f) (middleCharacter a) x

private def scalarFunctional : CupCoefficient ℚ MiddleCoefficient :=
  LinearMap.id

private def middleToDual : rIdeal middleIdem →ₗ[Tᵐᵒᵖ]
    CupCoefficient ℚ MiddleCoefficient where
  toFun x := middleCoefficient x • scalarFunctional
  map_add' x y := by
    change (middleCoefficient (x+y)) • scalarFunctional = _
    rw [map_add, add_smul]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change (middleCoefficient (a • x) • (show Module.Dual ℚ MiddleCoefficient from
      scalarFunctional)) y = (show Module.Dual ℚ MiddleCoefficient from
      a • (middleCoefficient x • scalarFunctional)) y
    rw [← op_unop a, middleDual_smul_apply]
    change middleCharacter (x.val * a.unop) * (show ℚ from y) =
      middleCharacter a.unop * (middleCharacter x.val * (show ℚ from y))
    rw [map_mul]
    ring

private theorem middleToDual_ker : LinearMap.ker middleToDual = middleCutTrace := by
  ext x
  rw [LinearMap.mem_ker, mem_middleCutTrace_iff]
  constructor
  · intro h
    have he := congrArg (fun f : CupCoefficient ℚ MiddleCoefficient =>
      (show Module.Dual ℚ MiddleCoefficient from f) (1 : ℚ)) h
    change middleCoefficient x * (1 : ℚ) = 0 at he
    change middleCoefficient x = 0
    simpa only [mul_one] using he
  · intro h
    change middleCoefficient x • scalarFunctional = 0
    change middleCoefficient x = 0 at h
    rw [h, zero_smul]

private theorem middleToDual_surjective : Function.Surjective middleToDual := by
  intro f
  let f' : Module.Dual ℚ MiddleCoefficient := f
  obtain ⟨x, hx⟩ := middleCoefficient_surjective (f' (1 : ℚ))
  refine ⟨x, ?_⟩
  apply LinearMap.ext
  intro y
  change middleCoefficient x * (show ℚ from y) = f' y
  rw [hx, mul_comm]
  have hy : (show ℚ from y) • (show MiddleCoefficient from (1 : ℚ)) = y := by
    change (show ℚ from y) * 1 = (show ℚ from y)
    exact mul_one _
  exact (map_smul f' (show ℚ from y) (show MiddleCoefficient from (1 : ℚ))).symm.trans
    (congrArg f' hy)

/-- The dual coefficient of the cup is the simple right quotient from
Webster's Lemma 7.3, expressed using the middle character. -/
def middleQuotientDualEquiv :
    (rIdeal middleIdem ⧸ middleCutTrace) ≃ₗ[Tᵐᵒᵖ]
      CupCoefficient ℚ MiddleCoefficient :=
  (Submodule.quotEquivOfEq _ _ middleToDual_ker.symm).trans
    (LinearMap.quotKerEquivOfSurjective middleToDual middleToDual_surjective)

end Categorification.Stendhal.FundamentalCorner
