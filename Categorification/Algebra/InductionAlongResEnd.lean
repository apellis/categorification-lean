/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes

/-!
# Restriction on endomorphisms

For a nonunital map `φ : A → B` of `k`-algebras and a `B`-module `N`, restriction `Res φ` carries
`B`-linear endomorphisms of `N` to `A`-linear endomorphisms of `Res φ N` multiplicatively
(`Res.endAlg`), so an action of an algebra `C` on `N` by `B`-linear maps restricts to an action
on `Res φ N`.
-/

open scoped TensorProduct

noncomputable section

namespace Categorification.InductionAlong

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A] {B : Type*} [Ring B]
  [Algebra k B] (f : A →ₙₐ[k] B)
  {N : Type*} [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]
  [Module k (Res (NonUnitalRingHomClass.toNonUnitalRingHom f) N)]
  [IsScalarTower k A (Res (NonUnitalRingHomClass.toNonUnitalRingHom f) N)]

/-- `k` acts on the restriction as on the module: `(c • m).val = c • m.val`, for the `k`-module
structure through `A`. -/
theorem Res.val_smul_k (c : k) (m : Res (NonUnitalRingHomClass.toNonUnitalRingHom f) N) :
    (c • m).val = c • m.val := by
  rw [← one_smul A m, ← smul_assoc, Res.val_smul, Res.val_smul]
  change f (c • 1) • m.val = c • (f 1 • m.val)
  rw [map_smul, smul_assoc]

/-- **Restriction on endomorphisms**, as a map of algebras. -/
def Res.endAlg : Module.End B N →ₐ[k]
    Module.End A (Res (NonUnitalRingHomClass.toNonUnitalRingHom f) N) where
  toFun := Res.map
  map_one' := LinearMap.ext fun _ => Res.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Res.ext rfl
  map_zero' := LinearMap.ext fun _ => Res.ext rfl
  map_add' _ _ := LinearMap.ext fun _ => Res.ext rfl
  commutes' c := LinearMap.ext fun m => Res.ext (by
    rw [Res.val_map, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Res.val_smul_k f c m])

@[simp] theorem Res.endAlg_apply (g : Module.End B N) :
    Res.endAlg f g = Res.map (φ := NonUnitalRingHomClass.toNonUnitalRingHom f) g := rfl

end Categorification.InductionAlong
