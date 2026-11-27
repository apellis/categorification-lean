/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorSplit

/-!
# Separating the first factor of the ordered tensor product

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
proof of Proposition 4.39. The map `𝔮_N(u ⊗ w) = u v_{Nλ₀} ⊗ w` lands in the tensor
product whose first factor is `V_{Nλ₀}`. This file separates the first factor of the
ordered tensor product, `V_{λ₀} ⊗ ⋯ ⊗ V_{λ_ℓ} ≅ V_{λ₀} ⊗ (V_{λ₁} ⊗ ⋯ ⊗ V_{λ_ℓ})`, and
computes the action of `F_i` and `K_μ` through it: with the coproduct
`Δ(F_i) = F_i ⊗ K_{-ĩ} + 1 ⊗ F_i`, `F_i (v ⊗ w) = F_i v ⊗ K_{-ĩ} w + v ⊗ F_i w`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance instNeZeroXTensorSplitFirst : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y}

private abbrev Factor (wt : Dom R) := IrreducibleModule R 𝕍 wt.1

/-- `Fin (n + 1) ≃ Fin 1 ⊕ Fin n`, separating `0`; its inverse is `0` on the left summand and
`Fin.succ` on the right one, so that the factors agree definitionally. -/
def finFirstEquiv (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun := Fin.cases (Sum.inl 0) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv j := by cases j using Fin.cases <;> rfl
  right_inv s := by
    rcases s with s | s
    · rw [Subsingleton.elim s 0]; rfl
    · rfl

/-- Separate the first red strand from the ordered tensor product. -/
def tensorSplitFirst {n : ℕ} (wt : Fin (n + 1) → Dom R) :
    TensorSpace wt ≃ₗ[𝕂] Factor (wt 0) ⊗[𝕂] TensorSpace (fun j : Fin n => wt j.succ) :=
  (PiTensorProduct.reindex 𝕂 (fun j => Factor (wt j)) (finFirstEquiv n)).trans
    ((PiTensorProduct.tmulEquivDep 𝕂
      (fun j : Fin 1 ⊕ Fin n => Factor (wt ((finFirstEquiv n).symm j)))).symm.trans
      (LinearEquiv.rTensor _ (PiTensorProduct.subsingletonEquiv (0 : Fin 1))))

theorem tensorSplitFirst_tprod {n : ℕ} (wt : Fin (n + 1) → Dom R) (x : ∀ j, Factor (wt j)) :
    tensorSplitFirst wt (PiTensorProduct.tprod 𝕂 x) =
      x 0 ⊗ₜ[𝕂] PiTensorProduct.tprod 𝕂 (fun j : Fin n => x j.succ) := by
  erw [tensorSplitFirst, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    LinearEquiv.trans_apply, PiTensorProduct.tmulEquivDep_symm_apply, LinearEquiv.rTensor_tmul,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-- Put a vector in front of a tensor. -/
def prependTensor {n : ℕ} (wt : Fin (n + 1) → Dom R) (v : Factor (wt 0))
    (z : TensorSpace (fun j : Fin n => wt j.succ)) : TensorSpace wt :=
  (tensorSplitFirst wt).symm (v ⊗ₜ[𝕂] z)

theorem prependTensor_tprod {n : ℕ} (wt : Fin (n + 1) → Dom R) (x : ∀ j, Factor (wt j)) :
    prependTensor wt (x 0) (PiTensorProduct.tprod 𝕂 (fun j : Fin n => x j.succ)) =
      PiTensorProduct.tprod 𝕂 x :=
  ((tensorSplitFirst wt).symm_apply_eq).mpr (tensorSplitFirst_tprod wt x).symm

theorem prependTensor_add_right {n : ℕ} (wt : Fin (n + 1) → Dom R) (v : Factor (wt 0))
    (z z' : TensorSpace (fun j : Fin n => wt j.succ)) :
    prependTensor wt v (z + z') = prependTensor wt v z + prependTensor wt v z' := by
  simp [prependTensor, TensorProduct.tmul_add]

theorem prependTensor_smul_right {n : ℕ} (wt : Fin (n + 1) → Dom R) (v : Factor (wt 0)) (c : 𝕂)
    (z : TensorSpace (fun j : Fin n => wt j.succ)) :
    prependTensor wt v (c • z) = c • prependTensor wt v z := by
  simp [prependTensor, TensorProduct.tmul_smul]

theorem prependTensor_add_left {n : ℕ} (wt : Fin (n + 1) → Dom R) (v v' : Factor (wt 0))
    (z : TensorSpace (fun j : Fin n => wt j.succ)) :
    prependTensor wt (v + v') z = prependTensor wt v z + prependTensor wt v' z := by
  simp [prependTensor, TensorProduct.add_tmul]

theorem appendTensor_add_left {n : ℕ} (wt : Fin (n + 1) → Dom R)
    (x x' : TensorSpace (fun j : Fin n => wt j.castSucc)) (y : Factor (wt (Fin.last n))) :
    appendTensor wt (x + x') y = appendTensor wt x y + appendTensor wt x' y := by
  simp [appendTensor, TensorProduct.add_tmul]

theorem appendTensor_smul_left {n : ℕ} (wt : Fin (n + 1) → Dom R) (c : 𝕂)
    (x : TensorSpace (fun j : Fin n => wt j.castSucc)) (y : Factor (wt (Fin.last n))) :
    appendTensor wt (c • x) y = c • appendTensor wt x y := by
  rw [appendTensor, appendTensor, ← TensorProduct.smul_tmul', map_smul]

theorem appendTensor_tprod {n : ℕ} (wt : Fin (n + 1) → Dom R)
    (x : ∀ j : Fin n, Factor (wt j.castSucc)) (y : Factor (wt (Fin.last n))) :
    appendTensor wt (PiTensorProduct.tprod 𝕂 x) y =
      PiTensorProduct.tprod 𝕂 (Fin.snoc (α := fun j => Factor (wt j)) x y) := by
  have h := ((tensorSplitLast wt).eq_symm_apply).mpr
    (tensorSplitLast_tprod wt (Fin.snoc (α := fun j => Factor (wt j)) x y))
  rw [h]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

private theorem cons_snoc {n : ℕ} (wt : Fin (n + 2) → Dom R) (v : Factor (wt 0))
    (x : ∀ j : Fin n, Factor (wt j.castSucc.succ)) (y : Factor (wt (Fin.last (n + 1)))) :
    Fin.cons (α := fun j => Factor (wt j)) v
        (Fin.snoc (α := fun j : Fin (n + 1) => Factor (wt j.succ)) x y) =
      Fin.snoc (α := fun j => Factor (wt j))
        (Fin.cons (α := fun j : Fin (n + 1) => Factor (wt j.castSucc)) v x) y := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    show Fin.snoc (α := fun j : Fin (n + 1) => Factor (wt j.succ)) x y (Fin.last n) = y
    exact Fin.snoc_last (α := fun j : Fin (n + 1) => Factor (wt j.succ)) _ _
  | cast j =>
    rw [Fin.snoc_castSucc]
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      show Fin.snoc (α := fun j : Fin (n + 1) => Factor (wt j.succ)) x y (Fin.castSucc j) = x j
      exact Fin.snoc_castSucc (α := fun j : Fin (n + 1) => Factor (wt j.succ)) _ _ _

/-- Prepending a first factor commutes with appending a last factor. -/
theorem prependTensor_appendTensor {n : ℕ} (wt : Fin (n + 2) → Dom R) (v : Factor (wt 0))
    (z : TensorSpace (fun j : Fin n => wt j.castSucc.succ)) (y : Factor (wt (Fin.last (n + 1)))) :
    prependTensor wt v (appendTensor (fun j : Fin (n + 1) => wt j.succ) z y) =
      appendTensor wt (prependTensor (fun j : Fin (n + 1) => wt j.castSucc) v z) y := by
  let L₁ : TensorSpace (fun j : Fin n => wt j.castSucc.succ) →ₗ[𝕂] TensorSpace wt :=
    (tensorSplitFirst wt).symm.toLinearMap ∘ₗ TensorProduct.mk 𝕂 _ _ v ∘ₗ
      (tensorSplitLast (fun j : Fin (n + 1) => wt j.succ)).symm.toLinearMap ∘ₗ
        (TensorProduct.mk 𝕂 _ _).flip y
  let L₂ : TensorSpace (fun j : Fin n => wt j.castSucc.succ) →ₗ[𝕂] TensorSpace wt :=
    (tensorSplitLast wt).symm.toLinearMap ∘ₗ (TensorProduct.mk 𝕂 _ _).flip y ∘ₗ
      (tensorSplitFirst (fun j : Fin (n + 1) => wt j.castSucc)).symm.toLinearMap ∘ₗ
        TensorProduct.mk 𝕂 _ _ v
  have key : L₁ = L₂ := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    change prependTensor wt v (appendTensor (fun j : Fin (n + 1) => wt j.succ)
        (PiTensorProduct.tprod 𝕂 x) y) =
      appendTensor wt (prependTensor (fun j : Fin (n + 1) => wt j.castSucc) v
        (PiTensorProduct.tprod 𝕂 x)) y
    rw [appendTensor_tprod]
    have h1 := prependTensor_tprod wt (Fin.cons (α := fun j => Factor (wt j)) v
      (Fin.snoc (α := fun j : Fin (n + 1) => Factor (wt j.succ)) x y))
    have h2 := prependTensor_tprod (fun j : Fin (n + 1) => wt j.castSucc)
      (Fin.cons (α := fun j : Fin (n + 1) => Factor (wt j.castSucc)) v x)
    simp only [Fin.cons_zero, Fin.cons_succ] at h1
    rw [h1, show prependTensor (fun j : Fin (n + 1) => wt j.castSucc) v
      (PiTensorProduct.tprod 𝕂 x) = PiTensorProduct.tprod 𝕂
        (Fin.cons (α := fun j : Fin (n + 1) => Factor (wt j.castSucc)) v x) from h2,
      appendTensor_tprod, cons_snoc]
  exact LinearMap.congr_fun key z

local notation "ρ" => tensorRepresentation
local notation "Δ" => comul R 𝕍

/-- Splitting off the first of one factor leaves the empty tensor product. -/
theorem tensorSplitFirst_one (w : Fin 1 → Dom R) (z : TensorSpace w) :
    tensorSplitFirst w z =
      tensorOne w z ⊗ₜ[𝕂] PiTensorProduct.tprod 𝕂 (fun i : Fin 0 ↦ i.elim0) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul, tensorSplitFirst_tprod, tensorOne_tprod, TensorProduct.smul_tmul']
    congr 2
    exact funext fun i : Fin 0 ↦ i.elim0
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', TensorProduct.add_tmul]

/-- The action of `n + 1` factors is the coproduct action on the first factor and the
remaining `n`; this is coassociativity of `Δ`. -/
theorem intertwines_tensorSplitFirst : ∀ {n : ℕ} (wt : Fin (n + 1) → Dom R),
    Intertwines (ρ wt)
      ((pairRep (Algebra.lsmul 𝕂 𝕂 (Factor (wt 0))) (ρ fun j : Fin n ↦ wt j.succ)).comp Δ)
      (tensorSplitFirst wt).toLinearMap
  | 0, wt => fun u z ↦ by
    simp only [LinearEquiv.coe_coe, AlgHom.comp_apply]
    rw [tensorSplitFirst_one, tensorSplitFirst_one, pairRep_comul_empty]
    congr 1
    exact intertwines_tensorOne wt u z
  | n + 1, wt => by
    have ih := intertwines_tensorSplitFirst (n := n) (fun j : Fin (n + 1) ↦ wt j.castSucc)
    have hG : (tensorSplitFirst wt).toLinearMap =
        (TensorProduct.map LinearMap.id
            (tensorSplitLast (fun j : Fin (n + 1) ↦ wt j.succ)).symm.toLinearMap) ∘ₗ
          (TensorProduct.assoc 𝕂 _ _ _).toLinearMap ∘ₗ
          (TensorProduct.map (tensorSplitFirst (fun j : Fin (n + 1) ↦ wt j.castSucc)).toLinearMap
            LinearMap.id) ∘ₗ (tensorSplitLast wt).toLinearMap := by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x ↦ ?_)
      change tensorSplitFirst wt (PiTensorProduct.tprod 𝕂 x) =
        TensorProduct.map LinearMap.id
          (tensorSplitLast (fun j : Fin (n + 1) ↦ wt j.succ)).symm.toLinearMap
          (TensorProduct.assoc 𝕂 _ _ _ (TensorProduct.map
            (tensorSplitFirst (fun j : Fin (n + 1) ↦ wt j.castSucc)).toLinearMap LinearMap.id
            (tensorSplitLast wt (PiTensorProduct.tprod 𝕂 x))))
      have a2 : TensorProduct.map LinearMap.id
          (tensorSplitLast (fun j : Fin (n + 1) ↦ wt j.succ)).symm.toLinearMap
          (TensorProduct.assoc 𝕂 _ _ _ (TensorProduct.map
            (tensorSplitFirst (fun j : Fin (n + 1) ↦ wt j.castSucc)).toLinearMap LinearMap.id
            (tensorSplitLast wt (PiTensorProduct.tprod 𝕂 x)))) =
          x (Fin.castSucc 0) ⊗ₜ[𝕂] PiTensorProduct.tprod 𝕂 (fun j : Fin (n + 1) => x j.succ) := by
        rw [tensorSplitLast_tprod, TensorProduct.map_tmul, LinearMap.id_apply,
          LinearEquiv.coe_coe, tensorSplitFirst_tprod, TensorProduct.assoc_tmul,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 1
        rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, tensorSplitLast_tprod]
        rfl
      exact (tensorSplitFirst_tprod wt x).trans a2.symm
    have hint := (((intertwines_tensorSplitLast wt).comp
      (Intertwines.restrict (Intertwines.tensorMap ih (Intertwines.id _)) Δ)).comp
      (intertwines_assoc _ _ _)).comp
      (Intertwines.restrict (Intertwines.tensorMap (Intertwines.id _)
        (intertwines_tensorSplitLast (fun j : Fin (n + 1) ↦ wt j.succ)).symm) Δ)
    intro u z
    have e := LinearMap.congr_fun hG
    exact (e _).trans ((hint u z).trans (congrArg _ (e z).symm))

end Categorification.Stendhal.FirstWeight
