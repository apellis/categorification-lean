/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Splitting off the first factor of a tensor product of algebras

For algebras `A 0, …, A n` over a commutative ring `k`, the tensor product `⨂_{r ≤ n} A r` is
isomorphic, as an algebra, to `A 0 ⊗ (⨂_{0 < r ≤ n} A r)`, by `⊗ f ↦ f 0 ⊗ (⊗_{r > 0} f r)`
(`PiTensorProduct.consAlgEquiv`). In B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, proof of Proposition 5.26, this writes the block algebra after
adding a red strand on the left as the first cyclotomic factor tensored with the others.
-/

noncomputable section

namespace PiTensorProduct

open scoped TensorProduct

/-- `Fin 1 ⊕ Fin n ≃ Fin (n + 1)`, sending `inl 0` to `0` and `inr j` to `j.succ`. -/
def sumFinSuccEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (.inl 0) .inr
  left_inv := by
    rintro (i | j)
    · rw [Subsingleton.elim i 0]; rfl
    · rfl
  right_inv := fun r => by cases r using Fin.cases <;> rfl

variable (k : Type*) [CommRing k] {n : ℕ} (A : Fin (n + 1) → Type*) [∀ r, Ring (A r)]
  [∀ r, Algebra k (A r)]

/-- **`⨂_{r ≤ n} A r ≅ A 0 ⊗ (⨂_{j < n} A (j + 1))`** as `k`-modules. -/
def consLinearEquiv :
    (⨂[k] r, A r) ≃ₗ[k] A 0 ⊗[k] (⨂[k] j : Fin n, A j.succ) :=
  ((PiTensorProduct.reindex k A (sumFinSuccEquiv n).symm).trans
    (PiTensorProduct.tmulEquivDep k (fun j : Fin 1 ⊕ Fin n => A (sumFinSuccEquiv n j))).symm).trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv 0) (LinearEquiv.refl k _))

variable {k A} in
theorem consLinearEquiv_tprod (f : ∀ r, A r) :
    consLinearEquiv k A (tprod k f) = f 0 ⊗ₜ tprod k (fun j : Fin n => f j.succ) := by
  erw [consLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
    TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

theorem consLinearEquiv_mul (x y : ⨂[k] r, A r) :
    consLinearEquiv k A (x * y) = consLinearEquiv k A x * consLinearEquiv k A y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s g =>
      rw [smul_mul_smul_comm, tprod_mul_tprod, map_smul, map_smul, map_smul,
        consLinearEquiv_tprod, consLinearEquiv_tprod, consLinearEquiv_tprod, smul_mul_smul_comm,
        Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod]
      rfl
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

/-- **`⨂_{r ≤ n} A r ≅ A 0 ⊗ (⨂_{j < n} A (j + 1))`** as `k`-algebras. -/
def consAlgEquiv :
    (⨂[k] r, A r) ≃ₐ[k] A 0 ⊗[k] (⨂[k] j : Fin n, A j.succ) :=
  AlgEquiv.ofLinearEquiv (consLinearEquiv k A)
    (by rw [one_def, consLinearEquiv_tprod]; rfl) (consLinearEquiv_mul k A)

variable {k A} in
@[simp] theorem consAlgEquiv_tprod (f : ∀ r, A r) :
    consAlgEquiv k A (tprod k f) = f 0 ⊗ₜ tprod k (fun j : Fin n => f j.succ) :=
  consLinearEquiv_tprod f

variable {k A}

/-- The first factor `x` sits in `⨂_{r ≤ n} A r` as `x ⊗ 1 ⊗ ⋯ ⊗ 1`. -/
theorem consAlgEquiv_symm_tmul_one (x : A 0) :
    (consAlgEquiv k A).symm (x ⊗ₜ 1) = singleAlgHom (R := k) (A := A) 0 x := by
  apply (consAlgEquiv k A).injective
  rw [AlgEquiv.apply_symm_apply, singleAlgHom_apply, consAlgEquiv_tprod]
  simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rw [one_def]
  congr 2

/-- The factor `j + 1` of `⨂_{r ≤ n} A r` is the factor `j` of `⨂_{j < n} A (j + 1)`. -/
theorem consAlgEquiv_symm_one_tmul_single (j : Fin n) (y : A j.succ) :
    (consAlgEquiv k A).symm (1 ⊗ₜ singleAlgHom (R := k) (A := fun j : Fin n => A j.succ) j y) =
      singleAlgHom (R := k) (A := A) j.succ y := by
  apply (consAlgEquiv k A).injective
  rw [AlgEquiv.apply_symm_apply, singleAlgHom_apply, singleAlgHom_apply, consAlgEquiv_tprod]
  simp only [MonoidHom.mulSingle_apply]
  rw [Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j).symm]
  congr 2
  funext i
  by_cases hi : i = j
  · subst hi
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne (fun h => hi (Fin.succ_injective _ h))]

end PiTensorProduct
