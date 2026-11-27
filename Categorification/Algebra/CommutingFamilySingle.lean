/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.CommutingFamily
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Generators of a tensor product of algebras

The factor inclusions `a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1` of a finite tensor product of algebras commute
pairwise, `liftCommuting` restricts to `φ_i` on the `i`-th factor
(`PiTensorProduct.liftCommuting_singleAlgHom`), and the factor inclusions generate: a subalgebra
of `A₀ ⊗ (A_0 ⊗ ⋯ ⊗ A_{n-1})` containing every `a ⊗ 1` and every `1 ⊗ (1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1)` is
everything (`PiTensorProduct.tensor_subalgebra_eq_top`). These are used for the block algebra
of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.3.
-/

namespace Categorification

theorem prod_ofFn_mulSingle {S : Type*} [Monoid S] :
    ∀ {n : ℕ} (i : Fin n) (x : S), (List.ofFn (Pi.mulSingle i x : Fin n → S)).prod = x
  | 0, i, _ => i.elim0
  | n + 1, i, x => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      have : (fun j : Fin n => (Pi.mulSingle (0 : Fin (n + 1)) x : Fin (n + 1) → S) j.succ) =
          fun _ => 1 := funext fun j => Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j) x
      rw [this, Pi.mulSingle_eq_same, List.ofFn_const, List.prod_replicate, one_pow, mul_one]
    | succ i =>
      have : (fun j : Fin n => (Pi.mulSingle i.succ x : Fin (n + 1) → S) j.succ) =
          Pi.mulSingle i x := funext fun j => by
        by_cases h : j = i
        · subst h
          rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
        · rw [Pi.mulSingle_eq_of_ne (fun h' => h (Fin.succ_injective _ h')),
            Pi.mulSingle_eq_of_ne h]
      rw [this, prod_ofFn_mulSingle i x, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i).symm,
        one_mul]

end Categorification

namespace PiTensorProduct

open Categorification
open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {n : ℕ} {A : Fin n → Type*} [∀ i, Semiring (A i)]
  [∀ i, Algebra R (A i)] {S : Type*} [Semiring S] [Algebra R S]

theorem commute_singleAlgHom {i j : Fin n} (h : i ≠ j) (a : A i) (b : A j) :
    Commute (singleAlgHom (R := R) (A := A) i a) (singleAlgHom (R := R) (A := A) j b) :=
  (Pi.mulSingle_commute h a b).tprod

/-- `liftCommuting` restricts to `φ_i` on the `i`-th factor. -/
theorem liftCommuting_singleAlgHom (φ : ∀ i, A i →ₐ[R] S)
    (h : ∀ i j, i < j → ∀ a b, Commute (φ i a) (φ j b)) (i : Fin n) (a : A i) :
    liftCommuting φ h (singleAlgHom i a) = φ i a := by
  rw [singleAlgHom_apply, liftCommuting_tprod]
  have : (fun j => φ j (MonoidHom.mulSingle A i a j)) = Pi.mulSingle i (φ i a) := funext fun j => by
    by_cases hj : j = i
    · subst hj
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]
  rw [this, prod_ofFn_mulSingle]

/-- The factor inclusions assemble to the identity. -/
theorem liftCommuting_singleAlgHom_eq_id :
    liftCommuting (singleAlgHom (R := R) (A := A))
        (fun _ _ h a b => commute_singleAlgHom (ne_of_lt h) a b) = AlgHom.id R _ :=
  algHom_ext fun i => AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, liftCommuting_singleAlgHom, AlgHom.comp_apply, AlgHom.id_apply]

/-- A pure tensor is the ordered product of its factors. -/
theorem tprod_eq_prod_singleAlgHom (a : ∀ i, A i) :
    tprod R a = (List.ofFn fun i => singleAlgHom (R := R) (A := A) i (a i)).prod := by
  rw [← liftCommuting_tprod (singleAlgHom (R := R) (A := A))
    (fun _ _ h a b => commute_singleAlgHom (ne_of_lt h) a b), liftCommuting_singleAlgHom_eq_id,
    AlgHom.id_apply]

end PiTensorProduct

namespace PiTensorProduct

open scoped TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
  [∀ i, Algebra R (A i)] {A₀ : Type*} [Ring A₀] [Algebra R A₀]

/-- **The factor inclusions generate** `A₀ ⊗ (A_0 ⊗ ⋯ ⊗ A_{n-1})`. -/
theorem tensor_subalgebra_eq_top (P : Subalgebra R (A₀ ⊗[R] (⨂[R] i, A i)))
    (h₀ : ∀ a : A₀, a ⊗ₜ[R] (1 : ⨂[R] i, A i) ∈ P)
    (h : ∀ i (a : A i), (1 : A₀) ⊗ₜ[R] singleAlgHom (R := R) (A := A) i a ∈ P) : P = ⊤ := by
  have hr : ∀ t : ⨂[R] i, A i, (1 : A₀) ⊗ₜ[R] t ∈ P := by
    intro t
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      rw [TensorProduct.tmul_smul, tprod_eq_prod_singleAlgHom]
      refine P.smul_mem ?_ r
      have hmap := map_list_prod (Algebra.TensorProduct.includeRight (R := R) (A := A₀)
        (B := ⨂[R] i, A i)) (List.ofFn fun i => singleAlgHom (R := R) (A := A) i (a i))
      rw [Algebra.TensorProduct.includeRight_apply] at hmap
      rw [hmap]
      refine P.list_prod_mem fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
      exact h i (a i)
    | add x y hx hy => rw [TensorProduct.tmul_add]; exact P.add_mem hx hy
  refine eq_top_iff.2 fun x _ => ?_
  clear ‹x ∈ ⊤›
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    have : a ⊗ₜ[R] t = (a ⊗ₜ[R] (1 : ⨂[R] i, A i)) * ((1 : A₀) ⊗ₜ[R] t) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact P.mul_mem (h₀ a) (hr t)
  | add x y hx hy => exact P.add_mem hx hy

/-- Two algebra maps out of `A₀ ⊗ (A_0 ⊗ ⋯ ⊗ A_{n-1})` agree when they agree on the factors. -/
theorem tensor_algHom_ext {S : Type*} [Ring S] [Algebra R S]
    {f g : (A₀ ⊗[R] (⨂[R] i, A i)) →ₐ[R] S}
    (h₀ : ∀ a : A₀, f (a ⊗ₜ 1) = g (a ⊗ₜ 1))
    (h : ∀ i (a : A i), f (1 ⊗ₜ singleAlgHom i a) = g (1 ⊗ₜ singleAlgHom i a)) : f = g := by
  have := tensor_subalgebra_eq_top (AlgHom.equalizer f g) h₀ h
  exact AlgHom.ext fun x => (this ▸ Algebra.mem_top : x ∈ AlgHom.equalizer f g)

end PiTensorProduct
