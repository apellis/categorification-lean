/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumCupCapTensor
import Categorification.WeightedKLR.RedStrands.AdjacentBraidingLattice

/-!
# `id ⊗ coev_μ ⊗ id` and `id ⊗ qtr_μ ⊗ id` on pure tensors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 7.20. On a pure tensor `x₀ ⊗ ⋯ ⊗ x_{k+m+1}` of `V^{λ⁺}`, the map `id ⊗ qtr_μ ⊗ id`
contracts the factors `k`, `k + 1`:

`(id ⊗ qtr_μ ⊗ id)(⋯ ⊗ x_k ⊗ x_{k+1} ⊗ ⋯) = qtr_μ(x_k ⊗ x_{k+1}) (⋯ ⊗ x_{k-1} ⊗ x_{k+2} ⊗ ⋯)`
(`tensorQuantumTrace_tprod`),

and `id ⊗ coev_μ ⊗ id` inserts the canonical element `coev_μ(1) ∈ V_μ ⊗ V_{μ*}` between the
factors `k - 1` and `k` (`tensorCoevaluation_tprod`, with `adjacentInsert`). The identifications
of the factors use the weight hypotheses `h₁ … h₄` of `tensorQuantumTrace`.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module
open Categorification.Stendhal.FirstWeight
open scoped TensorProduct

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

local notation "Fac" w => IrreducibleModule R vQ (Subtype.val w)
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))

variable (w₀ : Fin 0 → Dom R)
variable {k m : ℕ} (wt : Fin (k + 2 + m) → Dom R) (wt' : Fin (k + m) → Dom R)
  (h₁ : ∀ i : Fin k, wt' (Fin.castAdd m i) = wt (Fin.castAdd m (Fin.castAdd 2 i)))
  (h₂ : wt (Fin.castAdd m (Fin.natAdd k 0)) = μ)
  (h₃ : wt (Fin.castAdd m (Fin.natAdd k 1)) = dualWeight P μ weight hdom hm w hw hlong)
  (h₄ : ∀ i : Fin m, wt' (Fin.natAdd k i) = wt (Fin.natAdd (k + 2) i))

omit [Fintype I] in
private theorem emptyRid_tmul {A : Type*} [AddCommGroup A] [Module 𝕂 A] (a : A) (c : 𝕂) :
    emptyRid (A := A) w₀ (a ⊗ₜ[𝕂] (c • (PiTensorProduct.isEmptyEquiv (Fin 0)).symm 1)) =
      c • a := by
  simp [emptyRid, TensorProduct.rid_tmul]

omit [Fintype I] in
private theorem emptyRid_symm_apply {A : Type*} [AddCommGroup A] [Module 𝕂 A] (a : A) :
    (emptyRid (A := A) w₀).symm a = a ⊗ₜ[𝕂] (PiTensorProduct.isEmptyEquiv (Fin 0)).symm 1 := by
  rw [LinearEquiv.symm_apply_eq]
  simp [emptyRid, TensorProduct.rid_tmul]

include hR in
private theorem coevaluationEmpty_symm_one
    [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] :
    coevaluationEmpty P hR μ weight hdom hm w hw hlong w₀
        ((PiTensorProduct.isEmptyEquiv (Fin 0)).symm 1) =
      (TensorModule.mk Vμ Vμs).symm (coevaluationElement P hR μ weight hdom hm w hw hlong) := by
  simp [coevaluationEmpty, coevaluation_apply]

include hR in
/-- **`id ⊗ qtr_μ ⊗ id` on pure tensors**: the factors `k`, `k + 1` are contracted by `qtr_μ`,
and the remaining factors are kept (`y` is `x` with these two factors removed). -/
theorem tensorQuantumTrace_tprod (x : ∀ j, Fac (wt j)) (y : ∀ j, Fac (wt' j))
    (hy₁ : ∀ i : Fin k, HEq (y (Fin.castAdd m i)) (x (Fin.castAdd m (Fin.castAdd 2 i))))
    (hy₄ : ∀ i : Fin m, HEq (y (Fin.natAdd k i)) (x (Fin.natAdd (k + 2) i))) :
    tensorQuantumTrace P hR μ weight hdom hm w hw hlong w₀ wt wt' h₁ h₂ h₃ h₄
        (PiTensorProduct.tprod 𝕂 x) =
      quantumTrace P hR μ weight hdom hm w hw hlong
          (TensorModule.mk Vμ Vμs (facCongr h₂ (x (Fin.castAdd m (Fin.natAdd k 0))) ⊗ₜ[𝕂]
            facCongr h₃ (x (Fin.castAdd m (Fin.natAdd k 1))))) •
        PiTensorProduct.tprod 𝕂 y := by
  simp only [tensorQuantumTrace, LinearMap.comp_apply, LinearEquiv.coe_coe, adjacentDecomp_tprod,
    TensorProduct.map_tmul, LinearMap.lTensor_tmul, quantumTraceEmpty,
    LinearMap.toSpanSingleton_apply, LinearMap.id_apply]
  rw [emptyRid_tmul, ← TensorProduct.smul_tmul', map_smul, map_smul, TensorProduct.congr_tmul,
    tensorCongr_tprod _ _ _ fun i => (hy₁ i).symm, tensorCongr_tprod _ _ _ fun i => (hy₄ i).symm]
  congr 1
  rw [LinearEquiv.symm_apply_eq, tensorSplit_tprod]

include hR in
/-- **`id ⊗ coev_μ ⊗ id` on pure tensors**: the canonical element `coev_μ(1)` is inserted at the
factors `k`, `k + 1` (`x` is `y` with the factors identified along `h₁`, `h₄`). -/
theorem tensorCoevaluation_tprod [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)]
    (y : ∀ j, Fac (wt' j)) :
    tensorCoevaluation P hR μ weight hdom hm w hw hlong w₀ wt wt' h₁ h₂ h₃ h₄
        (PiTensorProduct.tprod 𝕂 y) =
      adjacentInsert wt
        (PiTensorProduct.tprod 𝕂 fun i => facCongr (h₁ i) (y (Fin.castAdd m i)))
        (PiTensorProduct.tprod 𝕂 fun i => facCongr (h₄ i) (y (Fin.natAdd k i)))
        (TensorProduct.map (facCongr h₂).symm.toLinearMap (facCongr h₃).symm.toLinearMap
          ((TensorModule.mk Vμ Vμs).symm
            (coevaluationElement P hR μ weight hdom hm w hw hlong))) := by
  simp only [tensorCoevaluation, LinearMap.comp_apply, LinearEquiv.coe_coe, tensorSplit_tprod,
    TensorProduct.congr_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [tensorCongr_tprod _ _ _ fun i => heq_facCongr (h₁ i) _,
    tensorCongr_tprod _ _ _ fun i => heq_facCongr (h₄ i) _]
  rw [emptyRid_symm_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply,
    coevaluationEmpty_symm_one]
  rfl

end Categorification.Stendhal.QuantumDual
