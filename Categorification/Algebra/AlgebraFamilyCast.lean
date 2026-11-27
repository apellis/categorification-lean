/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Algebra.Equiv

/-!
# Modules over a family of algebras, transported along an equality of indices

For a family of `k`-algebras `A x` and an equality `h : x = x'`, the algebras are isomorphic
(`familyCast`), and an `A x`-module is an `A x'`-module (`FamilyCast`). Maps of `A x`-modules
are `A x'`-linear on the transported modules (`FamilyCast.map`). This is how the tensor product
algebras `T^λ(ν)` and the factor algebras `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` are compared along equalities
of black weights in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5, where the weights of the blocks of a module agree
with `i + θ₀` only up to equality.
-/

namespace Categorification

variable {k : Type*} [CommRing k] {X : Type*} (A : X → Type*) [∀ x, Ring (A x)]
  [∀ x, Algebra k (A x)]

/-- The algebras of a family at equal indices. -/
def familyCast {x x' : X} (h : x = x') : A x ≃ₐ[k] A x' := by
  subst h
  exact AlgEquiv.refl

/-- The rings of a family at equal indices. -/
def familyRingCast {x x' : X} (h : x = x') : A x ≃+* A x' := by
  subst h
  exact RingEquiv.refl _

theorem familyCast_apply {x x' : X} (h : x = x') (a : A x) :
    familyCast (k := k) A h a = familyRingCast A h a := by
  subst h
  rfl

theorem familyCast_symm_apply {x x' : X} (h : x = x') (a : A x') :
    (familyCast (k := k) A h).symm a = (familyRingCast A h).symm a := by
  subst h
  rfl

@[simp] theorem familyCast_rfl {x : X} (a : A x) : familyCast (k := k) A (rfl : x = x) a = a :=
  rfl

/-- An `A x`-module regarded as an `A x'`-module, for `x = x'`. -/
@[nolint unusedArguments]
def FamilyCast (_A : X → Type*) {x x' : X} (_h : x = x') (N : Type*) : Type _ := N

variable {x x' : X} (h : x = x') (N : Type*) [AddCommGroup N] [Module k N] [Module (A x) N]
  [IsScalarTower k (A x) N]

instance : AddCommGroup (FamilyCast A h N) := inferInstanceAs (AddCommGroup N)
instance : Module k (FamilyCast A h N) := inferInstanceAs (Module k N)
instance : Module (A x') (FamilyCast A h N) :=
  Module.compHom N (familyRingCast A h).symm.toRingHom
instance : IsScalarTower k (A x') (FamilyCast A h N) where
  smul_assoc c a n := by
    subst h
    exact smul_assoc c a (show N from n)

namespace FamilyCast

variable {A h N}

/-- The identity `N → FamilyCast A h N`. -/
def of : N ≃ₗ[k] FamilyCast A h N := LinearEquiv.refl k N

omit [IsScalarTower k (A x) N] in
theorem smul_of (a : A x') (n : N) :
    a • (of (k := k) (A := A) (h := h) n : FamilyCast A h N) =
      of (k := k) ((familyCast (k := k) A h).symm a • n) := by
  rw [familyCast_symm_apply]
  rfl

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (A x) N'] [IsScalarTower k (A x) N']

omit [IsScalarTower k (A x) N] [IsScalarTower k (A x) N'] in
variable (A h) in
/-- A map of `A x`-modules as a map of the transported `A x'`-modules. -/
def map (g : N →ₗ[A x] N') : FamilyCast A h N →ₗ[A x'] FamilyCast A h N' where
  toFun n := (g (show N from n) : N')
  map_add' n n' := g.map_add (show N from n) (show N from n')
  map_smul' a n := g.map_smul ((familyRingCast A h).symm a) (show N from n)

omit [∀ x, Algebra k (A x)] [Module k N] [IsScalarTower k (A x) N] [Module k N']
  [IsScalarTower k (A x) N'] in
@[simp] theorem map_apply (g : N →ₗ[A x] N') (n : N) :
    map A h g (show FamilyCast A h N from n) = (show FamilyCast A h N' from g n) := rfl

omit [IsScalarTower k (A x) N] in
variable (A h N) in
/-- At `rfl`, the transported module is the module itself. -/
def rflEquiv : N ≃ₗ[A x] FamilyCast A (rfl : x = x) N where
  toFun n := n
  invFun n := n
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (A h N) in
/-- `A x`-linear endomorphisms as `A x'`-linear endomorphisms of the transported module. -/
def endHom : Module.End (A x) N →ₐ[k] Module.End (A x') (FamilyCast A h N) where
  toFun := map A h
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    refine LinearMap.ext fun n => ?_
    change (algebraMap k (Module.End (A x) N) c (show N from n) : N) =
      algebraMap k (Module.End (A x') (FamilyCast A h N)) c n
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    rfl

@[simp] theorem endHom_apply (g : Module.End (A x) N) (n : N) :
    endHom (k := k) A h N g (show FamilyCast A h N from n) = (show FamilyCast A h N from g n) :=
  rfl

end FamilyCast

end Categorification
