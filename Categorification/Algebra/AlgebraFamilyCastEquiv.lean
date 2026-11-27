/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.AlgebraFamilyCast

/-!
# Composing transports of modules along equalities of indices

For a family of algebras `A x`, transporting an `A x`-module along `x = x'` and then along
`x' = x''` is transporting it along `x = x''` (`FamilyCast.transEquiv`, the identity on
elements), and transport is functorial on isomorphisms (`FamilyCast.congr`). Used in
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, to compare the standardizations along the weights of the blocks.
-/

set_option linter.unusedSectionVars false

namespace Categorification

variable {k : Type*} [CommRing k] {X : Type*} (A : X → Type*) [∀ x, Ring (A x)]
  [∀ x, Algebra k (A x)]

namespace FamilyCast

variable {x x' x'' : X} (h : x = x') (h' : x' = x'') (N : Type*) [AddCommGroup N] [Module k N]
  [Module (A x) N] [IsScalarTower k (A x) N]

theorem familyRingCast_trans_symm (a : A x'') :
    (familyRingCast A (h.trans h')).symm a =
      (familyRingCast A h).symm ((familyRingCast A h').symm a) := by
  subst h h'
  rfl

/-- **Transport along `x = x'` and then `x' = x''` is transport along `x = x''`.** -/
def transEquiv : FamilyCast A h' (FamilyCast A h N) ≃ₗ[A x''] FamilyCast A (h.trans h') N where
  toFun n := n
  invFun n := n
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a n := by
    change (familyRingCast A h).symm ((familyRingCast A h').symm a) • (show N from n) =
      (familyRingCast A (h.trans h')).symm a • (show N from n)
    rw [familyRingCast_trans_symm A h h' a]

@[simp] theorem transEquiv_apply (n : N) :
    transEquiv A h h' N (show FamilyCast A h' (FamilyCast A h N) from n) =
      (show FamilyCast A (h.trans h') N from n) := rfl

@[simp] theorem transEquiv_symm_apply (n : N) :
    (transEquiv A h h' N).symm (show FamilyCast A (h.trans h') N from n) =
      (show FamilyCast A h' (FamilyCast A h N) from n) := rfl

variable {N} {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (A x) N']
  [IsScalarTower k (A x) N']

/-- **Transport of an isomorphism.** -/
def congr (e : N ≃ₗ[A x] N') : FamilyCast A h N ≃ₗ[A x'] FamilyCast A h N' :=
  { map A h e.toLinearMap with
    invFun := map A h e.symm.toLinearMap
    left_inv := fun n => e.symm_apply_apply (show N from n)
    right_inv := fun n => e.apply_symm_apply (show N' from n) }

@[simp] theorem congr_apply (e : N ≃ₗ[A x] N') (n : N) :
    congr A h e (show FamilyCast A h N from n) = (show FamilyCast A h N' from e n) := rfl

@[simp] theorem congr_symm_apply (e : N ≃ₗ[A x] N') (n : N') :
    (congr A h e).symm (show FamilyCast A h N' from n) = (show FamilyCast A h N from e.symm n) :=
  rfl

end FamilyCast

end Categorification
