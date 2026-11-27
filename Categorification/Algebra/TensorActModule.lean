/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Exact.Basic

/-!
# Modules with a commuting algebra action as modules over a tensor product

A left `A`-module `X` together with a map of `k`-algebras `ρ : C → End_A(X)` is a module over
`A ⊗[k] C`, with `(a ⊗ c) • x = a • ρ(c)(x)` (`TensorAct`). Maps of `A`-modules intertwining the
actions of `C` are `A ⊗ C`-linear (`TensorAct.map`). This is the form in which the filtrations of
Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, are carried through the induction on the number of red strands: the filtration
of a module with an extra commuting action is one of modules over the tensor product.

## Main definitions

* `TensorAct`: `X` as an `A ⊗[k] C`-module.
* `TensorAct.map`, `TensorAct.equiv`: intertwining maps as `A ⊗[k] C`-linear maps.
-/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Categorification

variable (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] (C : Type*) [Ring C]
  [Algebra k C]

section

variable {X : Type*} [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]

/-- The action of `C` on `X` as `k`-linear endomorphisms. -/
def tensorActEnd (ρ : C →ₐ[k] Module.End A X) : C →ₐ[k] Module.End k X where
  toFun c := (ρ c).restrictScalars k
  map_one' := by rw [map_one]; rfl
  map_mul' c c' := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' c c' := by rw [map_add]; rfl
  commutes' c := by
    rw [AlgHom.commutes]
    ext x
    simp

/-- The action of `A ⊗ C` on `X`. -/
noncomputable def tensorActHom (ρ : C →ₐ[k] Module.End A X) : A ⊗[k] C →ₐ[k] Module.End k X :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k X) (tensorActEnd k A C ρ)
    fun a c => LinearMap.ext fun x => ((ρ c).map_smul a x).symm

end

variable {X : Type*} [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]

/-- **`X` as a module over `A ⊗[k] C`**, for a map of algebras `ρ : C → End_A(X)`. -/
@[nolint unusedArguments]
def TensorAct (_ρ : C →ₐ[k] Module.End A X) : Type _ := X

variable (ρ : C →ₐ[k] Module.End A X)

instance : AddCommGroup (TensorAct k A C ρ) := inferInstanceAs (AddCommGroup X)

noncomputable instance : Module (A ⊗[k] C) (TensorAct k A C ρ) :=
  Module.compHom X (tensorActHom k A C ρ).toRingHom

noncomputable instance : Module k (TensorAct k A C ρ) := inferInstanceAs (Module k X)

namespace TensorAct

variable {k A C ρ}

/-- The identity `X → TensorAct ρ`. -/
def of : X ≃ₗ[k] TensorAct k A C ρ := LinearEquiv.refl k X

theorem tmul_smul_of (a : A) (c : C) (x : X) :
    ((a ⊗ₜ[k] c : A ⊗[k] C) • of (ρ := ρ) x : TensorAct k A C ρ) = of (a • ρ c x) := rfl

theorem smul_def (z : A ⊗[k] C) (x : TensorAct k A C ρ) :
    z • x = tensorActHom k A C ρ z (show X from x) := rfl

instance : IsScalarTower k (A ⊗[k] C) (TensorAct k A C ρ) where
  smul_assoc c z x := by
    rw [smul_def, smul_def, map_smul]
    rfl

variable {Y : Type*} [AddCommGroup Y] [Module k Y] [Module A Y] [IsScalarTower k A Y]
  {ρ' : C →ₐ[k] Module.End A Y}

/-- An `A`-linear map intertwining the actions of `C` as an `A ⊗ C`-linear map. -/
noncomputable def map (f : X →ₗ[A] Y) (hf : ∀ c x, f (ρ c x) = ρ' c (f x)) :
    TensorAct k A C ρ →ₗ[A ⊗[k] C] TensorAct k A C ρ' where
  toFun x := f x
  map_add' x y := map_add f x y
  map_smul' z x := by
    induction z using TensorProduct.inductionOn with
    | tmul a c => exact (f.map_smul a _).trans (congrArg (a • ·) (hf c x))
    | add z z' hz hz' =>
      rw [add_smul, RingHom.id_apply, add_smul, ← RingHom.id_apply (α := A ⊗[k] C) z, ← hz,
        ← RingHom.id_apply (α := A ⊗[k] C) z', ← hz']
      exact map_add f _ _

theorem map_of (f : X →ₗ[A] Y) (hf : ∀ c x, f (ρ c x) = ρ' c (f x)) (x : X) :
    map f hf (of x) = of (f x) := rfl

theorem map_injective {f : X →ₗ[A] Y} (hf : ∀ c x, f (ρ c x) = ρ' c (f x))
    (h : Function.Injective f) : Function.Injective (map f hf) := h

theorem map_surjective {f : X →ₗ[A] Y} (hf : ∀ c x, f (ρ c x) = ρ' c (f x))
    (h : Function.Surjective f) : Function.Surjective (map f hf) := h

theorem map_exact {Z : Type*} [AddCommGroup Z] [Module k Z] [Module A Z] [IsScalarTower k A Z]
    {ρ'' : C →ₐ[k] Module.End A Z} {f : X →ₗ[A] Y} {g : Y →ₗ[A] Z}
    (hf : ∀ c x, f (ρ c x) = ρ' c (f x)) (hg : ∀ c y, g (ρ' c y) = ρ'' c (g y))
    (h : Function.Exact f g) : Function.Exact (map f hf) (map g hg) := h

/-- An `A`-linear equivalence intertwining the actions of `C` as an `A ⊗ C`-linear one. -/
noncomputable def equiv (e : X ≃ₗ[A] Y) (he : ∀ c x, e (ρ c x) = ρ' c (e x)) :
    TensorAct k A C ρ ≃ₗ[A ⊗[k] C] TensorAct k A C ρ' :=
  LinearEquiv.ofBijective (map e.toLinearMap he) e.bijective

theorem equiv_of (e : X ≃ₗ[A] Y) (he : ∀ c x, e (ρ c x) = ρ' c (e x)) (x : X) :
    equiv e he (of x) = of (e x) := rfl

end TensorAct

end Categorification
