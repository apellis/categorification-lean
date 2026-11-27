/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.PiTensorProduct

/-!
# Nonunital maps of finite tensor products of algebras

For nonunital algebra maps `f i : A i →ₙₐ B i`, the tensor product map
`⨂ f i : ⨂ A i → ⨂ B i` is multiplicative (`PiTensorProduct.nonUnitalMap`). This is used for
the black-strand restriction functors on the block algebras of B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, Proposition 5.5.
-/

namespace PiTensorProduct

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A B : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]

/-- A nonunital algebra map as a linear map. -/
def _root_.NonUnitalAlgHom.linear {C D : Type*} [Semiring C] [Algebra R C] [Semiring D]
    [Algebra R D] (f : C →ₙₐ[R] D) : C →ₗ[R] D where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smul f

/-- **`⨂ f i` for nonunital algebra maps `f i`.** -/
noncomputable def nonUnitalMap (f : ∀ i, A i →ₙₐ[R] B i) :
    (⨂[R] i, A i) →ₙₐ[R] ⨂[R] i, B i where
  toFun := map fun i => (f i).linear
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s c =>
        simp only [smul_mul_smul_comm, tprod_mul_tprod, map_smul, map_tprod]
        congr 2
        exact funext fun i => map_mul (f i) (a i) (c i)
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem nonUnitalMap_tprod (f : ∀ i, A i →ₙₐ[R] B i) (a : ∀ i, A i) :
    nonUnitalMap f (tprod R a) = tprod R fun i => f i (a i) :=
  map_tprod (fun i => (f i).linear) a

end PiTensorProduct
