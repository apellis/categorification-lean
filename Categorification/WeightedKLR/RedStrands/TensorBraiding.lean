/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorSplit
import LieLean.Algebra.QuantumGroup.QuasiR.BraidingHighestWeight

/-!
# The braiding of two adjacent factors of the ordered tensor product

For dominant weights `λ_1, …, λ_ℓ`, the braiding `σ : V^{λ} ⊗ V^{μ} ≅ V^{μ} ⊗ V^{λ}` of
Webster, arXiv:1309.3796v3, (1.1) (`LieLean.QuantumGroup.IrreducibleModule.braidingEquiv`),
placed at the factors `k + 1` and `k + 2` of the ordered tensor product
`V^{λ_1} ⊗ ⋯ ⊗ V^{λ_ℓ}`, is an isomorphism of representations onto the ordered tensor product
with those two weights exchanged (`adjacentBraiding`, `intertwines_adjacentBraiding`). On a
pure tensor whose factor `k + 2` is the highest weight vector, it exchanges the two factors up
to the scalar `v^{-(ν, λ_{k+2})}`, where `λ_{k+1} - ν` is the weight of factor `k + 1`
(`adjacentBraiding_tprod_hwv`). This is the input of Webster, arXiv:1309.3796v2,
Corollary 6.10 (v3: Corollary 6.11), where the braiding functor categorifies `σ`.

## Main definitions and results

* `facBraiding`: the braiding `V^{λ} ⊗ V^{μ} ≃ V^{μ} ⊗ V^{λ}` as a linear equivalence.
* `adjacentDecomp`: `⨂_j V_j ≃ ((⨂_{j < k} V_j) ⊗ (V_k ⊗ V_{k+1})) ⊗ ⨂_{j < m} V_{k+2+j}`.
* `adjacentBraiding`: the braiding at the factors `k`, `k + 1` (counted from `0`).
* `intertwines_adjacentBraiding`, `adjacentBraiding_tprod_hwv`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance tensorBraidingInst1 : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "𝕌" => LieLean.QuantumGroup R 𝕍
local notation "Δ" => comul R 𝕍
local notation "ρ" => tensorRepresentation

private abbrev Fac (w : Dom R) := IrreducibleModule R 𝕍 w.1

/-! ### Intertwining equivalences -/

section Equiv

variable {B M M' M'' N N' : Type*} [Ring B] [Algebra 𝕂 B] [AddCommMonoid M] [Module 𝕂 M]
  [AddCommMonoid M'] [Module 𝕂 M'] [AddCommMonoid M''] [Module 𝕂 M''] [AddCommMonoid N]
  [Module 𝕂 N] [AddCommMonoid N'] [Module 𝕂 N']

theorem intertwines_refl (τ : B →ₐ[𝕂] Module.End 𝕂 M) :
    Intertwines τ τ (LinearEquiv.refl 𝕂 M).toLinearMap :=
  Intertwines.id τ

theorem intertwines_trans {τ : B →ₐ[𝕂] Module.End 𝕂 M} {τ' : B →ₐ[𝕂] Module.End 𝕂 M'}
    {τ'' : B →ₐ[𝕂] Module.End 𝕂 M''} {e : M ≃ₗ[𝕂] M'} {e' : M' ≃ₗ[𝕂] M''}
    (h : Intertwines τ τ' e.toLinearMap) (h' : Intertwines τ' τ'' e'.toLinearMap) :
    Intertwines τ τ'' (e.trans e').toLinearMap :=
  h.comp h'

theorem intertwines_congr {A : Type*} [Ring A] [Algebra 𝕂 A] {τ₁ : A →ₐ[𝕂] Module.End 𝕂 M}
    {τ₁' : A →ₐ[𝕂] Module.End 𝕂 M'} {τ₂ : A →ₐ[𝕂] Module.End 𝕂 N}
    {τ₂' : A →ₐ[𝕂] Module.End 𝕂 N'} {e : M ≃ₗ[𝕂] M'} {f : N ≃ₗ[𝕂] N'}
    (he : Intertwines τ₁ τ₁' e.toLinearMap) (hf : Intertwines τ₂ τ₂' f.toLinearMap) :
    Intertwines (pairRep τ₁ τ₂) (pairRep τ₁' τ₂') (TensorProduct.congr e f).toLinearMap :=
  Intertwines.tensorMap he hf

end Equiv

/-! ### Two factors -/

/-- The highest weight modules of two equal dominant weights. -/
def facCongr {w w' : Dom R} (h : w = w') : Fac w ≃ₗ[𝕂] Fac w' := by
  subst h; exact LinearEquiv.refl _ _

theorem intertwines_facCongr {w w' : Dom R} (h : w = w') :
    Intertwines (Algebra.lsmul 𝕂 𝕂 (Fac w) : 𝕌 →ₐ[𝕂] _) (Algebra.lsmul 𝕂 𝕂 (Fac w'))
      (facCongr h).toLinearMap := by
  subst h; exact Intertwines.id _

theorem facCongr_apply {w w' : Dom R} (h : w = w') (y : Fac w) (y' : Fac w')
    (hy : HEq y y') : facCongr h y = y' := by
  subst h; exact eq_of_heq hy

/-- The action of `U` on `V^{w₁} ⊗ V^{w₂}` through the coproduct. -/
abbrev facPairRep (w₁ w₂ : Dom R) : 𝕌 →ₐ[𝕂] Module.End 𝕂 (Fac w₁ ⊗[𝕂] Fac w₂) :=
  (pairRep (Algebra.lsmul 𝕂 𝕂 (Fac w₁)) (Algebra.lsmul 𝕂 𝕂 (Fac w₂))).comp Δ

section Braid

variable [Finite I] (hR : R.IsXRegular)

/-- The braiding `σ : V^{w₁} ⊗ V^{w₂} ≃ V^{w₂} ⊗ V^{w₁}` of Webster, arXiv:1309.3796v3, (1.1),
as a linear equivalence. -/
def facBraiding (w₁ w₂ : Dom R) : Fac w₁ ⊗[𝕂] Fac w₂ ≃ₗ[𝕂] Fac w₂ ⊗[𝕂] Fac w₁ :=
  ((TensorModule.mk (Fac w₁) (Fac w₂)).trans
    ((IrreducibleModule.braidingEquiv hR w₁.1 w₂.1).restrictScalars 𝕂)).trans
    (TensorModule.mk (Fac w₂) (Fac w₁)).symm

theorem intertwines_facBraiding (w₁ w₂ : Dom R) :
    Intertwines (facPairRep w₁ w₂) (facPairRep w₂ w₁) (facBraiding hR w₁ w₂).toLinearMap :=
  fun u z ↦ (IrreducibleModule.braidingEquiv hR w₁.1 w₂.1).map_smul u
    (TensorModule.mk (Fac w₁) (Fac w₂) z)

theorem facBraiding_tmul_hwv (w₁ w₂ : Dom R) {ν : I →₀ ℕ} {x : Fac w₁}
    (hx : x ∈ depthSpace R (Fac w₁) w₁.1 ν) :
    facBraiding hR w₁ w₂ (x ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 w₂.1) =
      (𝕍 ^ (-pairDepth R w₂.1 ν) : 𝕂) • (IrreducibleModule.hwv R 𝕍 w₂.1 ⊗ₜ[𝕂] x) :=
  IrreducibleModule.braidingEquiv_tmul_hwv hR w₁.1 w₂.1 hx

end Braid

/-! ### Isolating two adjacent factors -/

variable {k m : ℕ}

/-- The ordered tensor product with the factors `k` and `k + 1` isolated:
`⨂_j V_j ≃ ((⨂_{j < k} V_j) ⊗ (V_k ⊗ V_{k+1})) ⊗ ⨂_{j < m} V_{k+2+j}`. -/
def adjacentDecomp (wt : Fin (k + 2 + m) → Dom R) :
    TensorSpace wt ≃ₗ[𝕂]
      (TensorSpace (fun i : Fin k ↦ wt (Fin.castAdd m (Fin.castAdd 2 i))) ⊗[𝕂]
        (Fac (wt (Fin.castAdd m (Fin.natAdd k 0))) ⊗[𝕂]
          Fac (wt (Fin.castAdd m (Fin.natAdd k 1))))) ⊗[𝕂]
        TensorSpace (fun i : Fin m ↦ wt (Fin.natAdd (k + 2) i)) :=
  (tensorSplit (a := k + 2) (b := m) wt).trans
    (TensorProduct.congr
      ((tensorSplit (a := k) (b := 2) fun i ↦ wt (Fin.castAdd m i)).trans
        (TensorProduct.congr (LinearEquiv.refl _ _) (tensorPair _)))
      (LinearEquiv.refl _ _))

theorem adjacentDecomp_tprod (wt : Fin (k + 2 + m) → Dom R) (x : ∀ j, Fac (wt j)) :
    adjacentDecomp wt (PiTensorProduct.tprod 𝕂 x) =
      (PiTensorProduct.tprod 𝕂 (fun i : Fin k ↦ x (Fin.castAdd m (Fin.castAdd 2 i))) ⊗ₜ[𝕂]
          (x (Fin.castAdd m (Fin.natAdd k 0)) ⊗ₜ[𝕂] x (Fin.castAdd m (Fin.natAdd k 1)))) ⊗ₜ[𝕂]
        PiTensorProduct.tprod 𝕂 (fun i : Fin m ↦ x (Fin.natAdd (k + 2) i)) := by
  rw [adjacentDecomp, LinearEquiv.trans_apply, tensorSplit_tprod, TensorProduct.congr_tmul,
    LinearEquiv.trans_apply, tensorSplit_tprod, TensorProduct.congr_tmul, tensorPair_tprod]
  rfl

theorem intertwines_adjacentDecomp (wt : Fin (k + 2 + m) → Dom R) :
    Intertwines (ρ wt)
      ((pairRep ((pairRep (ρ fun i : Fin k ↦ wt (Fin.castAdd m (Fin.castAdd 2 i)))
          (facPairRep (wt (Fin.castAdd m (Fin.natAdd k 0)))
            (wt (Fin.castAdd m (Fin.natAdd k 1))))).comp Δ)
        (ρ fun i : Fin m ↦ wt (Fin.natAdd (k + 2) i))).comp Δ)
      (adjacentDecomp wt).toLinearMap :=
  intertwines_trans (intertwines_tensorSplit (a := k + 2) (b := m) wt)
    (Intertwines.restrict (intertwines_congr
      (intertwines_trans (intertwines_tensorSplit (a := k) (b := 2) fun i ↦ wt (Fin.castAdd m i))
        (Intertwines.restrict (intertwines_congr (intertwines_refl _)
          (intertwines_tensorPair _)) Δ))
      (intertwines_refl _)) Δ)

/-! ### The braiding at two adjacent factors -/

variable [Finite I] (hR : R.IsXRegular)

variable (wt wt' : Fin (k + 2 + m) → Dom R)
  (h₁ : ∀ i : Fin k, wt' (Fin.castAdd m (Fin.castAdd 2 i)) = wt (Fin.castAdd m (Fin.castAdd 2 i)))
  (h₂ : wt' (Fin.castAdd m (Fin.natAdd k 0)) = wt (Fin.castAdd m (Fin.natAdd k 1)))
  (h₃ : wt' (Fin.castAdd m (Fin.natAdd k 1)) = wt (Fin.castAdd m (Fin.natAdd k 0)))
  (h₄ : ∀ i : Fin m, wt' (Fin.natAdd (k + 2) i) = wt (Fin.natAdd (k + 2) i))

/-- The braiding of the factors `k` and `k + 1` of the ordered tensor product with weights
`wt`, onto the ordered tensor product with weights `wt'`, where `wt'` is `wt` with the weights
at `k` and `k + 1` exchanged (Webster, arXiv:1309.3796v3, (1.1) and Corollary 6.11). -/
def adjacentBraiding : TensorSpace wt ≃ₗ[𝕂] TensorSpace wt' :=
  (adjacentDecomp wt).trans
    ((TensorProduct.congr
      (TensorProduct.congr (tensorCongr (funext h₁).symm)
        ((facBraiding hR _ _).trans
          (TensorProduct.congr (facCongr h₂.symm) (facCongr h₃.symm))))
      (tensorCongr (funext h₄).symm)).trans
    (adjacentDecomp wt').symm)

theorem intertwines_adjacentBraiding :
    Intertwines (ρ wt) (ρ wt') (adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄).toLinearMap :=
  intertwines_trans (intertwines_adjacentDecomp wt)
    (intertwines_trans
      (Intertwines.restrict (intertwines_congr
        (Intertwines.restrict (intertwines_congr (intertwines_tensorCongr _)
          (intertwines_trans (intertwines_facBraiding hR _ _)
            (Intertwines.restrict (intertwines_congr (intertwines_facCongr _)
              (intertwines_facCongr _)) Δ))) Δ)
        (intertwines_tensorCongr _)) Δ)
      (intertwines_adjacentDecomp wt').symm)

/-- On a pure tensor whose factor `k + 1` is the highest weight vector and whose factor `k`
has weight `λ_k - ν`, the braiding exchanges the two factors up to `v^{-(ν, λ_{k+1})}`. -/
theorem adjacentBraiding_tprod_hwv (x : ∀ j, Fac (wt j)) (y : ∀ j, Fac (wt' j)) {ν : I →₀ ℕ}
    (hx₀ : x (Fin.castAdd m (Fin.natAdd k 0)) ∈
      depthSpace R (Fac (wt (Fin.castAdd m (Fin.natAdd k 0))))
        (wt (Fin.castAdd m (Fin.natAdd k 0))).1 ν)
    (hx₁ : x (Fin.castAdd m (Fin.natAdd k 1)) =
      IrreducibleModule.hwv R 𝕍 (wt (Fin.castAdd m (Fin.natAdd k 1))).1)
    (hy₁ : ∀ i : Fin k, HEq (y (Fin.castAdd m (Fin.castAdd 2 i)))
      (x (Fin.castAdd m (Fin.castAdd 2 i))))
    (hy₂ : HEq (y (Fin.castAdd m (Fin.natAdd k 0))) (x (Fin.castAdd m (Fin.natAdd k 1))))
    (hy₃ : HEq (y (Fin.castAdd m (Fin.natAdd k 1))) (x (Fin.castAdd m (Fin.natAdd k 0))))
    (hy₄ : ∀ i : Fin m, HEq (y (Fin.natAdd (k + 2) i)) (x (Fin.natAdd (k + 2) i))) :
    adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ (PiTensorProduct.tprod 𝕂 x) =
      (𝕍 ^ (-pairDepth R (wt (Fin.castAdd m (Fin.natAdd k 1))).1 ν) : 𝕂) •
        PiTensorProduct.tprod 𝕂 y := by
  rw [adjacentBraiding, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, map_smul, adjacentDecomp_tprod, adjacentDecomp_tprod,
    TensorProduct.congr_tmul, TensorProduct.congr_tmul, LinearEquiv.trans_apply, hx₁,
    facBraiding_tmul_hwv hR _ _ hx₀, map_smul, TensorProduct.congr_tmul,
    tensorCongr_tprod _ _ _ fun i ↦ (hy₁ i).symm, tensorCongr_tprod _ _ _ fun i ↦ (hy₄ i).symm,
    facCongr_apply _ _ _ (by rw [← hx₁]; exact hy₂.symm), facCongr_apply _ _ _ hy₃.symm,
    TensorProduct.tmul_smul]
  simp only [TensorProduct.smul_tmul']

end Categorification.Stendhal.FirstWeight
