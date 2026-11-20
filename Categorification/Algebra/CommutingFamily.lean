/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.PiTensorProduct

/-!
# Algebra maps out of a finite tensor product from commuting families

A family of algebra maps `φ_i : A_i → S`, `i : Fin n`, whose images commute pairwise induces an
algebra map `⨂_i A_i → S` sending `a_0 ⊗ ⋯ ⊗ a_{n-1}` to the ordered product
`φ_0(a_0) ⋯ φ_{n-1}(a_{n-1})` (`PiTensorProduct.liftCommuting`). This is the universal property of
the tensor product of algebras used to assemble block actions, for instance in
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Proposition 5.3.

## Main definitions

* `PiTensorProduct.liftCommuting`: the algebra map induced by a commuting family.
-/

namespace Categorification

/-- The ordered product of `u_i v_i` is the product of the ordered products, when each `v_i`
commutes with the `u_j` for `j > i`. -/
theorem prod_ofFn_mul_of_commute {S : Type*} [Monoid S] :
    ∀ {n : ℕ} (u v : Fin n → S), (∀ i j, i < j → Commute (v i) (u j)) →
      (List.ofFn fun i => u i * v i).prod = (List.ofFn u).prod * (List.ofFn v).prod
  | 0, _, _, _ => by simp
  | n + 1, u, v, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [prod_ofFn_mul_of_commute (fun i => u i.succ) (fun i => v i.succ)
      (fun i j hij => h _ _ (Fin.succ_lt_succ_iff.2 hij))]
    have hc : Commute (v 0) (List.ofFn fun i => u i.succ).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact h _ _ (Fin.succ_pos i)
    rw [mul_assoc, ← mul_assoc (v 0), hc.eq]
    simp only [mul_assoc]

end Categorification

namespace PiTensorProduct

open Categorification
open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {n : ℕ} {A : Fin n → Type*} [∀ i, Semiring (A i)]
  [∀ i, Algebra R (A i)] {S : Type*} [Semiring S] [Algebra R S]

/-- **The algebra map induced by a commuting family** `φ_i : A_i → S`: it sends
`a_0 ⊗ ⋯ ⊗ a_{n-1}` to `φ_0(a_0) ⋯ φ_{n-1}(a_{n-1})`. -/
noncomputable def liftCommuting (φ : ∀ i, A i →ₐ[R] S)
    (h : ∀ i j, i < j → ∀ a b, Commute (φ i a) (φ j b)) : (⨂[R] i, A i) →ₐ[R] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebraFin R n S).compLinearMap fun i => (φ i).toLinearMap)
    (by simp [MultilinearMap.mkPiAlgebraFin_apply])
    (fun x y => by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
        Pi.mul_apply, AlgHom.toLinearMap_apply, map_mul]
      exact prod_ofFn_mul_of_commute _ _ fun i j hij => h i j hij _ _)

@[simp] theorem liftCommuting_tprod (φ : ∀ i, A i →ₐ[R] S)
    (h : ∀ i j, i < j → ∀ a b, Commute (φ i a) (φ j b)) (a : ∀ i, A i) :
    liftCommuting φ h (tprod R a) = (List.ofFn fun i => φ i (a i)).prod := by
  simp [liftCommuting, MultilinearMap.mkPiAlgebraFin_apply]

/-- An element commuting with every `φ_i(a)` commutes with the image of `liftCommuting`. -/
theorem commute_liftCommuting (φ : ∀ i, A i →ₐ[R] S)
    (h : ∀ i j, i < j → ∀ a b, Commute (φ i a) (φ j b)) {s : S}
    (hs : ∀ i a, Commute s (φ i a)) (t : ⨂[R] i, A i) : Commute s (liftCommuting φ h t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [map_smul, liftCommuting_tprod]
    refine (Commute.list_prod_right _ _ fun x hx => ?_).smul_right r
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hs i _
  | add x y hx hy => rw [map_add]; exact hx.add_right hy

end PiTensorProduct
