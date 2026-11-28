/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumCoevaluation
import Categorification.WeightedKLR.RedStrands.TensorBraiding

/-!
# `id ⊗ coev_μ ⊗ id` and `id ⊗ qtr_μ ⊗ id` on the ordered tensor product

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 7.20: the maps `id ⊗ coev_μ ⊗ id` and `id ⊗ qtr_μ ⊗ id` between the ordered tensor
products `V^{λ_1} ⊗ ⋯ ⊗ V^{λ_ℓ}` with and without two adjacent factors `V_μ ⊗ V_{μ*}` at the
positions `k`, `k + 1` (counted from `0`).

* `quantumTraceEmpty`, `coevaluationEmpty`: `qtr_μ`, `coev_μ` with the trivial representation
  realized as the empty ordered tensor product (counit action), as maps of representations
  (`intertwines_quantumTraceEmpty`, `intertwines_coevaluationEmpty`).
* `tensorQuantumTrace`, `tensorCoevaluation`: the insertions, built from `adjacentDecomp`; both are
  maps of `U_q(g)`-representations for `tensorRepresentation`
  (`intertwines_tensorQuantumTrace`, `intertwines_tensorCoevaluation`).

The weights of the factors are matched by hypotheses `h₁ … h₄`, as for `adjacentBraiding`.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module
open Categorification.Stendhal.FirstWeight
open scoped TensorProduct

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩

/-! ### The trivial representation as the empty tensor product -/

section Empty

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {Δ : LusztigCartanDatum I}
  {R : Δ.RootDatum Y}

local notation "𝕌" => QuantumGroup R vQ
local notation "ρ" => tensorRepresentation

variable {A : Type*} [AddCommGroup A] [Module (RatFunc ℚ) A]
  (ρA : QuantumGroup R (RatFunc.X : RatFunc ℚ) →ₐ[RatFunc ℚ] Module.End (RatFunc ℚ) A)
  (w₀ : Fin 0 → Dom R)

/-- `A ⊗ ⨂_∅ ≃ A`. -/
def emptyRid : A ⊗[𝕂] TensorSpace w₀ ≃ₗ[𝕂] A :=
  (TensorProduct.congr (LinearEquiv.refl 𝕂 A) (PiTensorProduct.isEmptyEquiv (Fin 0))).trans
    (TensorProduct.rid 𝕂 A)

theorem intertwines_emptyRid :
    Intertwines ((pairRep ρA (ρ w₀)).comp (comul R vQ)) ρA (emptyRid w₀).toLinearMap := by
  intro u z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x e =>
    simp only [AlgHom.comp_apply, LinearEquiv.coe_coe]
    rw [pairRep_comul_empty]
    simp [emptyRid]

end Empty

/-! ### `qtr_μ` and `coev_μ` as maps of representations -/

section Maps

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "𝕌" => QuantumGroup R vQ
local notation "ρ" => tensorRepresentation

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

include hR hdom hm hw hlong

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))

variable (w₀ : Fin 0 → Dom R)

/-- `qtr_μ` with values in the empty tensor product `⨂_∅ = ℚ(q)` (the trivial representation). -/
def quantumTraceEmpty : Vμ ⊗[𝕂] Vμs →ₗ[𝕂] TensorSpace w₀ :=
  LinearMap.toSpanSingleton 𝕂 _ ((PiTensorProduct.isEmptyEquiv (Fin 0)).symm 1) ∘ₗ
    quantumTrace P hR μ weight hdom hm w hw hlong ∘ₗ (TensorModule.mk Vμ Vμs).toLinearMap

theorem intertwines_quantumTraceEmpty :
    Intertwines (facPairRep μ μs) (ρ w₀)
      (quantumTraceEmpty P hR μ weight hdom hm w hw hlong w₀) := by
  intro u z
  have h : TensorModule.mk Vμ Vμs (facPairRep μ μs u z) = u • TensorModule.mk Vμ Vμs z := rfl
  simp only [quantumTraceEmpty, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.toSpanSingleton_apply, h, quantumTrace_smul, tensorRepresentation_zero, smul_smul]

/-- `coev_μ` from the empty tensor product `⨂_∅ = ℚ(q)`. -/
def coevaluationEmpty [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] :
    TensorSpace w₀ →ₗ[𝕂] Vμ ⊗[𝕂] Vμs :=
  (TensorModule.mk Vμ Vμs).symm.toLinearMap ∘ₗ coevaluation P hR μ weight hdom hm w hw hlong ∘ₗ
    (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap

theorem intertwines_coevaluationEmpty [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] :
    Intertwines (ρ w₀) (facPairRep μ μs)
      (coevaluationEmpty P hR μ weight hdom hm w hw hlong w₀) := by
  intro u e
  change (TensorModule.mk Vμ Vμs).symm (coevaluation P hR μ weight hdom hm w hw hlong
      (PiTensorProduct.isEmptyEquiv (Fin 0) (counit R vQ u • e))) =
    (TensorModule.mk Vμ Vμs).symm (u • TensorModule.mk Vμ Vμs ((TensorModule.mk Vμ Vμs).symm
      (coevaluation P hR μ weight hdom hm w hw hlong (PiTensorProduct.isEmptyEquiv (Fin 0) e))))
  rw [LinearEquiv.apply_symm_apply, coevaluation_smul, map_smul, smul_eq_mul]

variable {k m : ℕ} (wt : Fin (k + 2 + m) → Dom R) (wt' : Fin (k + m) → Dom R)
  (h₁ : ∀ i : Fin k, wt' (Fin.castAdd m i) = wt (Fin.castAdd m (Fin.castAdd 2 i)))
  (h₂ : wt (Fin.castAdd m (Fin.natAdd k 0)) = μ)
  (h₃ : wt (Fin.castAdd m (Fin.natAdd k 1)) = dualWeight P μ weight hdom hm w hw hlong)
  (h₄ : ∀ i : Fin m, wt' (Fin.natAdd k i) = wt (Fin.natAdd (k + 2) i))

/-- **`id ⊗ qtr_μ ⊗ id`** on the ordered tensor product (Webster, Proposition 7.20): contract the
factors `k`, `k + 1` (weights `μ`, `μ*`) of `wt`, landing in the tensor product `wt'` of the
remaining factors. -/
def tensorQuantumTrace : TensorSpace wt →ₗ[𝕂] TensorSpace wt' :=
  (tensorSplit (a := k) (b := m) wt').symm.toLinearMap ∘ₗ
    (TensorProduct.congr (tensorCongr (funext h₁).symm)
      (tensorCongr (funext h₄).symm)).toLinearMap ∘ₗ
    TensorProduct.map ((emptyRid w₀).toLinearMap ∘ₗ
      LinearMap.lTensor _ (quantumTraceEmpty P hR μ weight hdom hm w hw hlong w₀ ∘ₗ
        TensorProduct.map (facCongr h₂).toLinearMap (facCongr h₃).toLinearMap)) LinearMap.id ∘ₗ
    (adjacentDecomp wt).toLinearMap

/-- **`id ⊗ qtr_μ ⊗ id` is a map of `U_q(g)`-representations.** -/
theorem intertwines_tensorQuantumTrace :
    Intertwines (ρ wt) (ρ wt')
      (tensorQuantumTrace P hR μ weight hdom hm w hw hlong w₀ wt wt' h₁ h₂ h₃ h₄) := by
  have hmid := (Intertwines.restrict (Intertwines.tensorMap (Intertwines.id
    (ρ fun i : Fin k ↦ wt (Fin.castAdd m (Fin.castAdd 2 i))))
    ((Intertwines.restrict (Intertwines.tensorMap (intertwines_facCongr h₂)
      (intertwines_facCongr h₃)) (comul R vQ)).comp
      (intertwines_quantumTraceEmpty P hR μ weight hdom hm w hw hlong w₀))) (comul R vQ)).comp
    (intertwines_emptyRid _ w₀)
  exact (((intertwines_adjacentDecomp wt).comp
    (Intertwines.restrict (Intertwines.tensorMap hmid
      (Intertwines.id (ρ fun i : Fin m ↦ wt (Fin.natAdd (k + 2) i)))) (comul R vQ))).comp
    (Intertwines.restrict (intertwines_congr (intertwines_tensorCongr _)
      (intertwines_tensorCongr _)) (comul R vQ))).comp
    (intertwines_tensorSplit (a := k) (b := m) wt').symm

/-- **`id ⊗ coev_μ ⊗ id`** on the ordered tensor product (Webster, Proposition 7.20): insert the
factors `k`, `k + 1` (weights `μ`, `μ*`) into the tensor product `wt'`, landing in `wt`. -/
def tensorCoevaluation [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] :
    TensorSpace wt' →ₗ[𝕂] TensorSpace wt :=
  (adjacentDecomp wt).symm.toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.lTensor _ (TensorProduct.map (facCongr h₂).symm.toLinearMap
        (facCongr h₃).symm.toLinearMap ∘ₗ coevaluationEmpty P hR μ weight hdom hm w hw hlong w₀) ∘ₗ
      (emptyRid w₀).symm.toLinearMap) LinearMap.id ∘ₗ
    (TensorProduct.congr (tensorCongr (funext h₁)) (tensorCongr (funext h₄))).toLinearMap ∘ₗ
    (tensorSplit (a := k) (b := m) wt').toLinearMap

/-- **`id ⊗ coev_μ ⊗ id` is a map of `U_q(g)`-representations.** -/
theorem intertwines_tensorCoevaluation [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] :
    Intertwines (ρ wt') (ρ wt)
      (tensorCoevaluation P hR μ weight hdom hm w hw hlong w₀ wt wt' h₁ h₂ h₃ h₄) := by
  have hmid := (intertwines_emptyRid
      (ρ fun i : Fin k ↦ wt (Fin.castAdd m (Fin.castAdd 2 i))) w₀).symm.comp
    (Intertwines.restrict (Intertwines.tensorMap (Intertwines.id
      (ρ fun i : Fin k ↦ wt (Fin.castAdd m (Fin.castAdd 2 i))))
      ((intertwines_coevaluationEmpty P hR μ weight hdom hm w hw hlong w₀).comp
        (Intertwines.restrict (Intertwines.tensorMap (intertwines_facCongr h₂).symm
          (intertwines_facCongr h₃).symm) (comul R vQ)))) (comul R vQ))
  exact (((intertwines_tensorSplit (a := k) (b := m) wt').comp
    (Intertwines.restrict (intertwines_congr (intertwines_tensorCongr _)
      (intertwines_tensorCongr _)) (comul R vQ))).comp
    (Intertwines.restrict (Intertwines.tensorMap hmid
      (Intertwines.id (ρ fun i : Fin m ↦ wt (Fin.natAdd (k + 2) i)))) (comul R vQ))).comp
    (intertwines_adjacentDecomp wt).symm

end Maps

end Categorification.Stendhal.QuantumDual
