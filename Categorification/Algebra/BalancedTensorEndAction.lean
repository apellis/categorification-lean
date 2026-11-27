/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Endomorphisms of the right factor of a balanced tensor product

For a `(B, A)`-bimodule `M` and a left `A`-module `N`, `M ⊗_A -` is additive and `k`-linear on
maps, so a map of algebras `ρ : C → End_A(N)` gives one `C → End_B(M ⊗_A N)`
(`BalancedTensor.endAction`). A retract `P` of `N` (maps `i : P → N`, `r : N → P` with
`r ∘ i = 1`) gives a retract `M ⊗_A P` of `M ⊗_A N`, identified with the fixed part of the
idempotent `M ⊗ (i ∘ r)` (`BalancedTensor.mapRight_retract_injective`,
`BalancedTensor.mem_range_mapRight_retract`). These are used in Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5, where the functors
`ₖEᵢ` cut a module over the block algebra by an idempotent of one tensor factor.
-/

namespace Categorification

open scoped TensorProduct
open MulOpposite

noncomputable section

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]
  {A : Type*} [Ring A] [Algebra k A]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [SMulCommClass B Aᵐᵒᵖ M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

namespace BalancedTensor

theorem mapRight_add (g g' : N →ₗ[A] N) :
    mapRight (k := k) (B := B) (M := M) (g + g') = mapRight g + mapRight g' :=
  extB fun m n => tmul_add m (g n) (g' n)

theorem mapRight_smul (c : k) (g : N →ₗ[A] N) :
    mapRight (k := k) (B := B) (M := M) (c • g) = c • mapRight g :=
  extB fun m n => tmul_smul c m (g n)

variable (k B M) in
/-- `M ⊗_A -` on `A`-linear endomorphisms, as a map of `k`-algebras. -/
def endMapRight : Module.End A N →ₐ[k] Module.End B (BalancedTensor k B A M N) where
  toFun g := mapRight g
  map_one' := mapRight_id
  map_mul' g g' := mapRight_comp g' g
  map_zero' := extB fun m n => by
    change tmul m (0 : N) = 0
    rw [← zero_smul k (0 : N), tmul_smul, zero_smul]
  map_add' := mapRight_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (mapRight_smul c 1).trans (congrArg (c • ·) mapRight_id)

@[simp] theorem endMapRight_tmul (g : Module.End A N) (m : M) (n : N) :
    endMapRight k B M g (tmul m n) = tmul m (g n) := rfl

variable {C : Type*} [Ring C] [Algebra k C]

variable (k B M) in
/-- **The induced action** `C → End_B(M ⊗_A N)` of `ρ : C → End_A(N)`. -/
def endAction (ρ : C →ₐ[k] Module.End A N) : C →ₐ[k] Module.End B (BalancedTensor k B A M N) :=
  (endMapRight k B M).comp ρ

@[simp] theorem endAction_tmul (ρ : C →ₐ[k] Module.End A N) (c : C) (m : M) (n : N) :
    endAction k B M ρ c (tmul m n) = tmul m (ρ c n) := rfl

section Retract

variable {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  {i : P →ₗ[A] N} {r : N →ₗ[A] P}

theorem mapRight_retract_injective (h : r.comp i = LinearMap.id) :
    Function.Injective (mapRight (k := k) (B := B) (M := M) i) := by
  intro x y hxy
  have hid : (mapRight (k := k) (B := B) (M := M) r).comp (mapRight i) = LinearMap.id := by
    rw [← mapRight_comp, h, mapRight_id]
  have := congrArg (mapRight (k := k) (B := B) (M := M) r) hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hid] at this

theorem mem_range_mapRight_retract (h : r.comp i = LinearMap.id) (x : BalancedTensor k B A M N) :
    x ∈ LinearMap.range (mapRight (k := k) (B := B) (M := M) i) ↔
      mapRight (k := k) (B := B) (M := M) (i.comp r) x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [mapRight_comp, LinearMap.comp_apply, ← LinearMap.comp_apply (mapRight r), ← mapRight_comp,
      h, mapRight_id, LinearMap.id_apply]
  · intro hx
    refine ⟨mapRight r x, ?_⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp, hx]

end Retract

end BalancedTensor

end

end Categorification
