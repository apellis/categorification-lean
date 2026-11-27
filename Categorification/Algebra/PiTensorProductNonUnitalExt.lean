/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.PiTensorProductNonUnitalMap
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Nonunital algebra maps out of `A ⊗ ⨂ᵢ Bᵢ` are determined on generators

Two nonunital algebra maps out of `A ⊗[R] ⨂[R] i, B i` agree once they agree on the elements
`a ⊗ 1` and `1 ⊗ (1 ⊗ ⋯ ⊗ b ⊗ ⋯ ⊗ 1)` (`NonUnitalAlgHom.tensorPi_ext`). This is used for the
block algebras `R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯` of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §5.1, whose maps between different block families
(the functors `ₖEᵢ` before Proposition 5.5) are nonunital.
-/

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ι → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]

omit [Fintype ι] in
/-- `tprod` of a family that is `1` outside `s`, as a product of single factors. -/
theorem tprod_piecewise_insert (c : ∀ i, B i) {j : ι} {s : Finset ι} (hj : j ∉ s) :
    tprod R (fun i => if i ∈ insert j s then c i else 1) =
      tprod R (fun i => if i ∈ s then c i else 1) * singleAlgHom (R := R) (A := B) j (c j) := by
  rw [singleAlgHom_apply, tprod_mul_tprod]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi
    simp [hj]
  · simp [Finset.mem_insert, hi, MonoidHom.mulSingle_apply]

section NonUnitalMap

variable {C : ι → Type*} [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)]
  (f : ∀ i, B i →ₙₐ[R] C i) (κ : ι) (hf : ∀ s, s ≠ κ → f s 1 = 1)
include hf

omit [Fintype ι] in
/-- A tensor product of nonunital maps, unital away from `κ`, on `1`. -/
theorem nonUnitalMap_one_of_ne :
    nonUnitalMap f 1 = singleAlgHom (R := R) (A := C) κ (f κ 1) := by
  rw [one_def, nonUnitalMap_tprod, singleAlgHom_apply]
  congr 1
  funext s
  by_cases hs : s = κ
  · subst hs
    simp
  · simp [hs, hf s hs]

omit [Fintype ι] in
/-- A tensor product of nonunital maps, unital away from `κ`, on a single factor at `κ`. -/
theorem nonUnitalMap_single_self (c : B κ) :
    nonUnitalMap f (singleAlgHom (R := R) (A := B) κ c) =
      singleAlgHom (R := R) (A := C) κ (f κ c) := by
  rw [singleAlgHom_apply, nonUnitalMap_tprod, singleAlgHom_apply]
  congr 1
  funext s
  by_cases hs : s = κ
  · subst hs
    simp
  · simp [hs, hf s hs]

omit [Fintype ι] in
/-- A tensor product of nonunital maps, unital away from `κ`, on a single factor away from
`κ`. -/
theorem nonUnitalMap_single_of_ne {j : ι} (hj : j ≠ κ) (c : B j) :
    nonUnitalMap f (singleAlgHom (R := R) (A := B) j c) =
      singleAlgHom (R := R) (A := C) j (f j c) * singleAlgHom (R := R) (A := C) κ (f κ 1) := by
  rw [singleAlgHom_apply, nonUnitalMap_tprod, singleAlgHom_apply, singleAlgHom_apply,
    tprod_mul_tprod]
  congr 1
  funext s
  by_cases hs : s = j
  · subst hs
    simp [hj]
  · by_cases hsκ : s = κ
    · subst hsκ
      simp [hs]
    · simp [hs, hsκ, hf s hsκ]

end NonUnitalMap

end PiTensorProduct

namespace NonUnitalAlgHom

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ι → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
  {S : Type*} [Semiring S] [Algebra R S]

/-- **Nonunital algebra maps out of `A ⊗ ⨂ᵢ Bᵢ` agree if they agree on generators.** -/
theorem tensorPi_ext {f g : A ⊗[R] (⨂[R] i, B i) →ₙₐ[R] S}
    (h₁ : ∀ a : A, f (a ⊗ₜ 1) = g (a ⊗ₜ 1))
    (h₂ : ∀ (i : ι) (b : B i),
      f (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := R) (A := B) i b) =
        g (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := R) (A := B) i b)) :
    f = g := by
  have hone : ∀ y : ⨂[R] i, B i, ∀ a : A, a ⊗ₜ[R] y = (a ⊗ₜ 1) * (1 ⊗ₜ y) := fun y a => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have htprod : ∀ c : ∀ i, B i, f (1 ⊗ₜ PiTensorProduct.tprod R c) =
      g (1 ⊗ₜ PiTensorProduct.tprod R c) := by
    intro c
    have key : ∀ s : Finset ι, f (1 ⊗ₜ PiTensorProduct.tprod R
        (fun i => if i ∈ s then c i else 1)) =
        g (1 ⊗ₜ PiTensorProduct.tprod R (fun i => if i ∈ s then c i else 1)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have : (fun i => if i ∈ (∅ : Finset ι) then c i else (1 : B i)) = 1 := by
          funext i; simp
        rw [this, ← PiTensorProduct.one_def, ← Algebra.TensorProduct.one_def]
        exact h₁ 1
      | insert j s hj ih =>
        rw [PiTensorProduct.tprod_piecewise_insert c hj,
          show (1 : A) ⊗ₜ[R] (PiTensorProduct.tprod R (fun i => if i ∈ s then c i else 1) *
              PiTensorProduct.singleAlgHom (R := R) (A := B) j (c j)) =
            (1 ⊗ₜ PiTensorProduct.tprod R (fun i => if i ∈ s then c i else 1)) *
              (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := R) (A := B) j (c j)) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
          map_mul, map_mul, ih, h₂]
    have := key Finset.univ
    simpa using this
  refine NonUnitalAlgHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
    rw [hone y a, map_mul, map_mul, h₁]
    congr 1
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r c =>
      rw [TensorProduct.tmul_smul, map_smul, map_smul, htprod]
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end NonUnitalAlgHom
