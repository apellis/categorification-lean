/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TensorActModule
import Categorification.Algebra.TensorProductLinearGenerators
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Restricting `A ⊗ C`-modules along an isomorphism of the first factor

For an isomorphism of `k`-algebras `e : A' ≅ A`, an `A`-module `V` with an action `ρ` of `C`,
and an `A'`-module `V'` identified with `V` along `e` compatibly with an action `ρ'` of `C`, the
`A' ⊗ C`-module defined by `ρ'` is the restriction of the `A ⊗ C`-module defined by `ρ` along
`e ⊗ 1` (`TensorAct.restrictEquiv`). In B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, proof of Proposition 5.5, this transports filtrations along the
identification of weights `(i + θ) + β = i + (θ + β)`.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

namespace TensorAct

variable {k : Type*} [CommRing k] {A' A C : Type*} [Ring A'] [Ring A] [Ring C] [Algebra k A']
  [Algebra k A] [Algebra k C] (e : A' ≃ₐ[k] A)

/-- The ring map `e ⊗ 1 : A' ⊗ C → A ⊗ C`. -/
abbrev firstFactorHom : A' ⊗[k] C →+* A ⊗[k] C :=
  (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id k C)).toRingHom

variable {V V' : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup V'] [Module k V'] [Module A' V'] [IsScalarTower k A' V']
  {ρ : C →ₐ[k] Module.End A V} {ρ' : C →ₐ[k] Module.End A' V'}
  (f : V' ≃+ V) (hf : ∀ (a : A') (v : V'), f (a • v) = e a • f v)
  (hρ : ∀ (c : C) (v : V'), f (ρ' c v) = ρ c (f v))

/-- The underlying additive map of `restrictEquiv`. -/
def restrictAdd : TensorAct k A' C ρ' →+
    (ModuleCat.restrictScalars (firstFactorHom e)).obj
      (ModuleCat.of (A ⊗[k] C) (TensorAct k A C ρ)) where
  toFun x := (show TensorAct k A C ρ from of (f (of.symm x)))
  map_zero' := map_zero f
  map_add' x y := map_add f (show V' from x) (show V' from y)

include hf hρ in
theorem restrictAdd_tmul_smul (a : A') (c : C) (x : TensorAct k A' C ρ') :
    restrictAdd e f (ρ := ρ) ((a ⊗ₜ c : A' ⊗[k] C) • x) =
      (a ⊗ₜ c : A' ⊗[k] C) • restrictAdd e f (ρ := ρ) x := by
  change f (a • ρ' c (show V' from x)) =
    firstFactorHom e (a ⊗ₜ c) • (show TensorAct k A C ρ from of (f (show V' from x)))
  rw [hf, hρ]
  rfl

/-- The underlying linear map of `restrictEquiv`. -/
def restrictHom : TensorAct k A' C ρ' →ₗ[A' ⊗[k] C]
    (ModuleCat.restrictScalars (firstFactorHom e)).obj
      (ModuleCat.of (A ⊗[k] C) (TensorAct k A C ρ)) :=
  tensorLinearOfGenerators (restrictAdd e f (ρ := ρ))
    (fun a x => restrictAdd_tmul_smul e f hf hρ a 1 x)
    (fun c x => restrictAdd_tmul_smul e f hf hρ 1 c x)

/-- **Restriction along `e ⊗ 1`**: the `A' ⊗ C`-module of `ρ'` is the restriction of the
`A ⊗ C`-module of `ρ`. -/
def restrictEquiv : TensorAct k A' C ρ' ≃ₗ[A' ⊗[k] C]
    (ModuleCat.restrictScalars (firstFactorHom e)).obj
      (ModuleCat.of (A ⊗[k] C) (TensorAct k A C ρ)) :=
  LinearEquiv.ofBijective (restrictHom e f hf hρ) f.bijective

theorem restrictEquiv_of (v : V') :
    restrictEquiv e f hf hρ (of v) = (show TensorAct k A C ρ from of (f v)) := rfl

end TensorAct

end Categorification
