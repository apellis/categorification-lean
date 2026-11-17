/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstWeightTensor
import Categorification.QuantumGroup.DividedCoproduct

/-!
# The quantum group action on the ordered tensor of highest-weight modules

For Webster, arXiv:1309.3796v2, §4.7 and (5.10), the tensor factors occur
in red-strand order. At each step the coproduct acts on the preceding tensor
and the last factor. The tensor with zero factors carries the counit action.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ}

private abbrev Factor (wt : Dom R) := IrreducibleModule R 𝕍 wt.1

/-- Separate the final red strand from the ordered tensor product. -/
def tensorSplitLast (wt : Fin (ℓ + 1) → Dom R) :
    TensorSpace wt ≃ₗ[𝕂] (TensorSpace (fun j => wt (Fin.castSucc j)) ⊗[𝕂] Factor (wt (Fin.last ℓ))) :=
  (PiTensorProduct.reindex 𝕂 (fun j => Factor (wt j)) (finSumFinEquiv (m := ℓ) (n := 1)).symm).trans
    ((PiTensorProduct.tmulEquivDep 𝕂 (fun j : Fin ℓ ⊕ Fin 1 => Factor (wt (finSumFinEquiv j)))).symm.trans
      (LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv (0 : Fin 1))))

theorem tensorSplitLast_tprod (wt : Fin (ℓ + 1) → Dom R) (x : ∀ j, Factor (wt j)) :
    tensorSplitLast wt (PiTensorProduct.tprod 𝕂 x) =
      (PiTensorProduct.tprod 𝕂 (fun j => x (Fin.castSucc j))) ⊗ₜ[𝕂] x (Fin.last ℓ) := by
  erw [tensorSplitLast, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    LinearEquiv.trans_apply, PiTensorProduct.tmulEquivDep_symm_apply, LinearEquiv.lTensor_tmul,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-- Append one red strand, acting on the ordered product through the coproduct.
The parameter is the indeterminate of the highest-weight factors. -/
def tensorRepresentation : {n : ℕ} → (wt : Fin n → Dom R) →
    LieLean.QuantumGroup R 𝕍 →ₐ[𝕂] Module.End 𝕂 (TensorSpace wt)
  | 0, wt => (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wt))).comp (counit R 𝕍)
  | n+1, wt =>
    let t := tensorSplitLast wt
    let left := tensorRepresentation (fun j => wt (Fin.castSucc j))
    let right : LieLean.QuantumGroup R 𝕍 →ₐ[𝕂] Module.End 𝕂 (Factor (wt (Fin.last n))) :=
      Algebra.lsmul 𝕂 𝕂 _
    ((t.symm.conjAlgEquiv 𝕂).toAlgHom).comp <|
      (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp <|
        (Algebra.TensorProduct.map left right).comp (comul R 𝕍)

variable (wt : Fin (ℓ + 1) → Dom R)
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => Factor (wt (Fin.last ℓ))
local notation "𝕌" => LieLean.QuantumGroup R 𝕍

/-- Append a vector in the last factor to a vector in the prefix. -/
def appendTensor (x : V₀) (y : V₁) : TensorSpace wt :=
  (tensorSplitLast wt).symm (x ⊗ₜ[𝕂] y)

private def tensorPairAction : 𝕌 ⊗[𝕂] 𝕌 →ₐ[𝕂] Module.End 𝕂 (V₀ ⊗[𝕂] V₁) :=
  (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp
    (Algebra.TensorProduct.map (tensorRepresentation wt₀) (Algebra.lsmul 𝕂 𝕂 V₁))

private theorem tensorPairAction_tmul (a b : 𝕌) (x : V₀) (y : V₁) :
    tensorPairAction wt (a ⊗ₜ[𝕂] b) (x ⊗ₜ[𝕂] y) =
      tensorRepresentation wt₀ a x ⊗ₜ[𝕂] (b • y) := by
  simp [tensorPairAction, Module.endTensorEndAlgHom_apply]

private theorem tensorRepresentation_append (u : 𝕌) (x : V₀) (y : V₁) :
    tensorRepresentation wt u (appendTensor wt x y) =
      (tensorSplitLast wt).symm (tensorPairAction wt (comul R 𝕍 u) (x ⊗ₜ[𝕂] y)) := by
  change (tensorSplitLast wt).symm (tensorPairAction wt (comul R 𝕍 u)
    (tensorSplitLast wt ((tensorSplitLast wt).symm (x ⊗ₜ[𝕂] y)))) = _
  rw [LinearEquiv.apply_symm_apply]

theorem tensorRepresentation_F_append (i : I) (x : V₀) (y : V₁) :
    tensorRepresentation wt (F R 𝕍 i) (appendTensor wt x y) =
      appendTensor wt (tensorRepresentation wt₀ (F R 𝕍 i) x) (K R 𝕍 (-ktilde R i) • y) +
      appendTensor wt x (F R 𝕍 i • y) := by
  rw [tensorRepresentation_append, comul_F, map_add, LinearMap.add_apply,
    tensorPairAction_tmul, tensorPairAction_tmul, map_one, Module.End.one_apply, map_add]
  rfl

theorem tensorRepresentation_E_append (i : I) (x : V₀) (y : V₁) :
    tensorRepresentation wt (E R 𝕍 i) (appendTensor wt x y) =
      appendTensor wt (tensorRepresentation wt₀ (E R 𝕍 i) x) y +
      appendTensor wt (tensorRepresentation wt₀ (Kt R 𝕍 i) x) (E R 𝕍 i • y) := by
  rw [tensorRepresentation_append, comul_E, map_add, LinearMap.add_apply,
    tensorPairAction_tmul, tensorPairAction_tmul, one_smul, map_add]
  rfl

theorem tensorRepresentation_K_append (μ : Y) (x : V₀) (y : V₁) :
    tensorRepresentation wt (K R 𝕍 μ) (appendTensor wt x y) =
      appendTensor wt (tensorRepresentation wt₀ (K R 𝕍 μ) x) (K R 𝕍 μ • y) := by
  rw [tensorRepresentation_append, comul_K, tensorPairAction_tmul]
  rfl

private theorem tensorRepresentation_K_tprod (μ : Y) : ∀ {n : ℕ} (wts : Fin n → Dom R)
    (x : ∀ j, Factor (wts j)),
    tensorRepresentation wts (K R 𝕍 μ) (PiTensorProduct.tprod 𝕂 x) =
      PiTensorProduct.tprod 𝕂 (fun j => K R 𝕍 μ • x j)
  | 0, wts, x => by
    change (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wts))) (counit R 𝕍 (K R 𝕍 μ)) _ = _
    rw [counit_K, map_one, Module.End.one_apply]
    exact congrArg (PiTensorProduct.tprod 𝕂) (funext (fun j => j.elim0))
  | n+1, wts, x => by
    have h (z : ∀ j, Factor (wts j)) :
        PiTensorProduct.tprod 𝕂 z = appendTensor wts
          (PiTensorProduct.tprod 𝕂 (fun j : Fin n => z j.castSucc)) (z (Fin.last n)) :=
      ((tensorSplitLast wts).eq_symm_apply).mpr (tensorSplitLast_tprod wts z)
    rw [h x, tensorRepresentation_K_append, tensorRepresentation_K_tprod, h (fun j => K R 𝕍 μ • x j)]

/-- The torus of the iterated coproduct acts factor by factor. -/
theorem tensorRepresentation_K (wts : Fin ℓ → Dom R) (μ : Y) :
    tensorRepresentation wts (K R 𝕍 μ) = tensorTorus wts μ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change tensorRepresentation wts (K R 𝕍 μ) (PiTensorProduct.tprod 𝕂 x) =
    tensorTorus wts μ (PiTensorProduct.tprod 𝕂 x)
  rw [tensorRepresentation_K_tprod, tensorTorus, PiTensorProduct.map_tprod]
  rfl

local notation "divF" => fun (i : I) (n : ℕ) => qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)
local notation "LP" => LaurentPolynomial ℤ

/-- Laurent coefficient for splitting a divided lowering power between the
final factor and the prefix in the coproduct (Webster, (5.10)). -/
def dividedCoefficient (μ : Y →+ ℤ) (i : I) (r s : ℕ) : LP :=
  LaurentPolynomial.T ((D.d i : ℤ) * (r * s) + μ (s • (-ktilde R i)))

omit [DecidableEq I] in
@[simp] theorem dividedCoefficient_zero_right (μ : Y →+ ℤ) (i : I) (n : ℕ) :
    dividedCoefficient (R := R) μ i n 0 = 1 := by simp [dividedCoefficient]

/-- Divided lowering on an appended tensor is triangular in the height reached
in the last factor. The term lowering the last factor alone has coefficient one. -/
theorem tensorRepresentation_dividedF_append (i : I) (n : ℕ) (x : V₀) (y : V₁)
    {μ : Y →+ ℤ} (hy : y ∈ weightSpace R 𝕍 V₁ μ) :
    tensorRepresentation wt (divF i n) (appendTensor wt x y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, dividedCoefficient (R := R) μ i p.1 p.2 •
        appendTensor wt (tensorRepresentation wt₀ (divF i p.2) x) (divF i p.1 • y) := by
  rw [tensorRepresentation_append, Categorification.QuantumGroup.comul_dividedF, map_sum,
    LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r,s⟩ _
  have hpow : K R 𝕍 (-ktilde R i) ^ s = K R 𝕍 (s • (-ktilde R i)) :=
    (map_pow (KHom R 𝕍) (Multiplicative.ofAdd (-ktilde R i)) s).symm
  change (tensorSplitLast wt).symm ((tensorPairAction wt
    ((𝕍 ^ D.d i) ^ (r*s) • (divF i s ⊗ₜ[𝕂] (divF i r * K R 𝕍 (-ktilde R i) ^ s)))) (x ⊗ₜ[𝕂] y)) = _
  rw [map_smul, LinearMap.smul_apply, tensorPairAction_tmul, mul_smul, hpow,
    (mem_weightSpace.mp hy) _, smul_comm (divF i r), TensorProduct.tmul_smul, map_smul, map_smul,
    tensor_laurent_smul, dividedCoefficient, LusztigF.integralLaurentEval_T, zpow_add₀ RatFunc.X_ne_zero,
    smul_smul, ← pow_mul]
  congr 2

end Categorification.Stendhal.FirstWeight
