/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Injectivity from a dimension count

For an exact sequence `A → B → C → 0` of finite-dimensional vector spaces, the first map is
injective exactly when `dim B = dim A + dim C` (`injective_iff_finrank_eq_add`); the same holds
for modules over a `k`-algebra `T`, with dimensions over `k`
(`injective_iff_finrank_restrictScalars`). This is the form in which a dimension count proves
left exactness, as in the proof of Webster, arXiv:1309.3796v3, Proposition 5.5.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification

/-- For `A → B → C → 0` exact with `A`, `B` finite-dimensional, `A → B` is injective iff
`dim B = dim A + dim C`. -/
theorem injective_iff_finrank_eq_add {k A B C : Type*} [Field k] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k A]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [FiniteDimensional k B] :
    Function.Injective f ↔ Module.finrank k B = Module.finrank k A + Module.finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hfg.linearMap_ker_eq] at h1
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

section

variable {k T : Type*} [Field k] [Ring T] [Algebra k T]

/-- A `T`-linear map as a `k`-linear map between the restricted-scalar modules. -/
def restrictScalarsLinearMap {X Y : Type*} [AddCommGroup X] [Module T X] [AddCommGroup Y]
    [Module T Y] (f : X →ₗ[T] Y) :
    RestrictScalars k T X →ₗ[k] RestrictScalars k T Y where
  toFun x := (RestrictScalars.addEquiv k T Y).symm (f (RestrictScalars.addEquiv k T X x))
  map_add' x y := by simp
  map_smul' c x := by
    change f (algebraMap k T c • (RestrictScalars.addEquiv k T X) x) = _
    rw [f.map_smul]; rfl

end

/-- `injective_iff_finrank_eq_add` for modules over a `k`-algebra `T`, with dimensions over
`k`. -/
theorem injective_iff_finrank_restrictScalars (k : Type*) {T : Type*} [Field k] [Ring T]
    [Algebra k T] {X Y Z : Type*} [AddCommGroup X] [Module T X]
    [AddCommGroup Y] [Module T Y] [AddCommGroup Z] [Module T Z]
    (f : X →ₗ[T] Y) (g : Y →ₗ[T] Z) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [FiniteDimensional k (RestrictScalars k T X)] [FiniteDimensional k (RestrictScalars k T Y)] :
    Function.Injective f ↔ Module.finrank k (RestrictScalars k T Y) =
      Module.finrank k (RestrictScalars k T X) + Module.finrank k (RestrictScalars k T Z) :=
  injective_iff_finrank_eq_add (restrictScalarsLinearMap (k := k) (T := T) f)
    (restrictScalarsLinearMap (k := k) (T := T) g) hfg hg

end Categorification
