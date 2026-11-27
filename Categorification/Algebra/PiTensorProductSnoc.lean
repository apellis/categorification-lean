/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Splitting off the last factor of a tensor product of algebras

For algebras `A 0, …, A n` over a commutative ring `k`, the tensor product `⨂_{r ≤ n} A r` is
isomorphic, as an algebra, to `(⨂_{r < n} A r) ⊗ A n`, by `⊗ f ↦ (⊗_{r < n} f r) ⊗ f n`
(`PiTensorProduct.snocAlgEquiv`). In B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, proof of Proposition 5.5, this writes the block algebra of `ℓ + 1`
red strands as that of the first `ℓ` tensored with the last cyclotomic factor.
-/

noncomputable section

namespace PiTensorProduct

open scoped TensorProduct

variable (k : Type*) [CommRing k] {n : ℕ} (A : Fin (n + 1) → Type*) [∀ r, Ring (A r)]
  [∀ r, Algebra k (A r)]

/-- **`⨂_{r ≤ n} A r ≅ (⨂_{r < n} A r) ⊗ A n`** as `k`-modules. -/
def snocLinearEquiv :
    (⨂[k] r, A r) ≃ₗ[k] (⨂[k] j : Fin n, A j.castSucc) ⊗[k] A (Fin.last n) :=
  ((PiTensorProduct.reindex k A finSumFinEquiv.symm).trans
    (PiTensorProduct.tmulEquivDep k (fun j : Fin n ⊕ Fin 1 => A (finSumFinEquiv j))).symm).trans
    (TensorProduct.congr (LinearEquiv.refl k _) (PiTensorProduct.subsingletonEquiv 0))

variable {k A} in
theorem snocLinearEquiv_tprod (f : ∀ r, A r) :
    snocLinearEquiv k A (tprod k f) =
      tprod k (fun j : Fin n => f j.castSucc) ⊗ₜ f (Fin.last n) := by
  erw [snocLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
    TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

theorem snocLinearEquiv_mul (x y : ⨂[k] r, A r) :
    snocLinearEquiv k A (x * y) = snocLinearEquiv k A x * snocLinearEquiv k A y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s g =>
      rw [smul_mul_smul_comm, tprod_mul_tprod, map_smul, map_smul, map_smul,
        snocLinearEquiv_tprod, snocLinearEquiv_tprod, snocLinearEquiv_tprod, smul_mul_smul_comm,
        Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod]
      rfl
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

/-- **`⨂_{r ≤ n} A r ≅ (⨂_{r < n} A r) ⊗ A n`** as `k`-algebras. -/
def snocAlgEquiv :
    (⨂[k] r, A r) ≃ₐ[k] (⨂[k] j : Fin n, A j.castSucc) ⊗[k] A (Fin.last n) :=
  AlgEquiv.ofLinearEquiv (snocLinearEquiv k A)
    (by rw [one_def, snocLinearEquiv_tprod]; rfl) (snocLinearEquiv_mul k A)

variable {k A} in
@[simp] theorem snocAlgEquiv_tprod (f : ∀ r, A r) :
    snocAlgEquiv k A (tprod k f) = tprod k (fun j : Fin n => f j.castSucc) ⊗ₜ f (Fin.last n) :=
  snocLinearEquiv_tprod f

end PiTensorProduct
