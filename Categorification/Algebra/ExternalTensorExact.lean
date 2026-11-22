/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExternalTensor

/-!
# Exactness of the external tensor product over a field

Over a field `k`, the external tensor product `- ⊠ Q` with a fixed module `Q` over `B` is exact:
it preserves injections, surjections and exactness at the middle of a short exact sequence. This
is the exactness of `⊠` used in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Proposition 5.20.

## Main results

* `ExtTensor.map_id_injective`, `ExtTensor.map_id_surjective`, `ExtTensor.map_id_exact`.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

namespace ExtTensor

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
  {B : Type*} [Ring B] [Algebra k B]
  {P P' P'' : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  [AddCommGroup P'] [Module k P'] [Module A P'] [IsScalarTower k A P']
  [AddCommGroup P''] [Module k P''] [Module A P''] [IsScalarTower k A P'']
  {Q : Type*} [AddCommGroup Q] [Module k Q] [Module B Q] [IsScalarTower k B Q]

theorem map_id_eq_rTensor (f : P →ₗ[A] P') (x : ExtTensor k P Q) :
    map (k := k) f (LinearMap.id : Q →ₗ[B] Q) x = (f.restrictScalars k).rTensor Q x := rfl

/-- `f ⊠ Q` is injective for injective `f`, over a field. -/
theorem map_id_injective {f : P →ₗ[A] P'} (hf : Function.Injective f) :
    Function.Injective (map (k := k) f (LinearMap.id : Q →ₗ[B] Q)) := by
  intro x y h
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := Q) (f.restrictScalars k) hf h

/-- `f ⊠ Q` is surjective for surjective `f`. -/
theorem map_id_surjective {f : P →ₗ[A] P'} (hf : Function.Surjective f) :
    Function.Surjective (map (k := k) f (LinearMap.id : Q →ₗ[B] Q)) :=
  map_surjective hf Function.surjective_id

/-- `- ⊠ Q` is exact at the middle of a sequence `P → P' → P''` exact at `P'` with surjective
second map. -/
theorem map_id_exact {f : P →ₗ[A] P'} {g : P' →ₗ[A] P''} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (map (k := k) f (LinearMap.id : Q →ₗ[B] Q))
      (map (k := k) g (LinearMap.id : Q →ₗ[B] Q)) :=
  rTensor_exact Q (f := f.restrictScalars k) (g := g.restrictScalars k) hfg hg

end ExtTensor

end Categorification
