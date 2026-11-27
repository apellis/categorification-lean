/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TensorActModule

/-!
# Splitting off a commuting action from a module over a triple tensor product

A module `Y` over `A₁ ⊗[k] (A₂ ⊗[k] C)` is a module over `A₁ ⊗[k] A₂` (`SplitLeft`), through
`a₁ ⊗ a₂ ↦ a₁ ⊗ (a₂ ⊗ 1)`, with a commuting action of `C` through `c ↦ 1 ⊗ (1 ⊗ c)`
(`splitAction`). Maps of modules give maps of the split modules intertwining the actions of
`C` (`SplitLeft.map`). In B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5, the induction on red strands produces filtrations of
modules over `T^{λ'}(θ) ⊗ (R^{λ_ℓ}(β) ⊗ C)`; split this way, they are filtrations of modules over
the factor algebra `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` with an extra commuting action, to which
standardization applies.
-/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Categorification

noncomputable section

variable (k : Type*) [CommRing k] (A₁ : Type*) [Ring A₁] [Algebra k A₁] (A₂ : Type*) [Ring A₂]
  [Algebra k A₂] (C : Type*) [Ring C] [Algebra k C]

/-- `a₁ ⊗ a₂ ↦ a₁ ⊗ (a₂ ⊗ 1)`. -/
def splitLeftHom : A₁ ⊗[k] A₂ →ₐ[k] A₁ ⊗[k] (A₂ ⊗[k] C) :=
  Algebra.TensorProduct.map (AlgHom.id k A₁) Algebra.TensorProduct.includeLeft

/-- `c ↦ 1 ⊗ (1 ⊗ c)`. -/
def splitRightHom : C →ₐ[k] A₁ ⊗[k] (A₂ ⊗[k] C) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

variable {k A₁ A₂ C}

@[simp] theorem splitLeftHom_tmul (a₁ : A₁) (a₂ : A₂) :
    splitLeftHom k A₁ A₂ C (a₁ ⊗ₜ a₂) = a₁ ⊗ₜ (a₂ ⊗ₜ 1) := rfl

@[simp] theorem splitRightHom_apply (c : C) :
    splitRightHom k A₁ A₂ C c = 1 ⊗ₜ (1 ⊗ₜ c) := rfl

theorem splitLeftHom_commute (z : A₁ ⊗[k] A₂) (c : C) :
    Commute (splitLeftHom k A₁ A₂ C z) (splitRightHom k A₁ A₂ C c) := by
  induction z using TensorProduct.inductionOn with
  | tmul a₁ a₂ =>
    change (a₁ ⊗ₜ (a₂ ⊗ₜ 1)) * (1 ⊗ₜ (1 ⊗ₜ c)) = (1 ⊗ₜ (1 ⊗ₜ c)) * (a₁ ⊗ₜ (a₂ ⊗ₜ 1))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add z z' hz hz' =>
    rw [map_add]
    exact hz.add_left hz'

variable (k A₁ A₂ C) in
/-- **A module over `A₁ ⊗ (A₂ ⊗ C)` as a module over `A₁ ⊗ A₂`.** -/
@[nolint unusedArguments]
def SplitLeft (Y : Type*) [AddCommGroup Y] [Module (A₁ ⊗[k] (A₂ ⊗[k] C)) Y] : Type _ := Y

variable (Y : Type*) [AddCommGroup Y] [Module (A₁ ⊗[k] (A₂ ⊗[k] C)) Y]

namespace SplitLeft

instance : AddCommGroup (SplitLeft k A₁ A₂ C Y) := inferInstanceAs (AddCommGroup Y)

instance : Module (A₁ ⊗[k] A₂) (SplitLeft k A₁ A₂ C Y) :=
  Module.compHom Y (splitLeftHom k A₁ A₂ C).toRingHom

instance : Module k (SplitLeft k A₁ A₂ C Y) :=
  Module.compHom Y (algebraMap k (A₁ ⊗[k] (A₂ ⊗[k] C)))

theorem splitLeftHom_smul_smul (c : k) (z : A₁ ⊗[k] A₂) (y : Y) :
    splitLeftHom k A₁ A₂ C (c • z) • y =
      algebraMap k (A₁ ⊗[k] (A₂ ⊗[k] C)) c • splitLeftHom k A₁ A₂ C z • y := by
  rw [map_smul]
  exact (congrArg (· • y) (Algebra.smul_def c _)).trans
    (mul_smul (algebraMap k (A₁ ⊗[k] (A₂ ⊗[k] C)) c) (splitLeftHom k A₁ A₂ C z) y)

instance : IsScalarTower k (A₁ ⊗[k] A₂) (SplitLeft k A₁ A₂ C Y) where
  smul_assoc c z y := splitLeftHom_smul_smul Y c z y

variable {Y}

/-- The identity `Y → SplitLeft Y`. -/
def of : Y ≃+ SplitLeft k A₁ A₂ C Y := AddEquiv.refl Y

theorem smul_of (z : A₁ ⊗[k] A₂) (y : Y) :
    z • of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) y = of (splitLeftHom k A₁ A₂ C z • y) := rfl

theorem splitRightHom_smul_comm (c : C) (z : A₁ ⊗[k] A₂) (y : Y) :
    splitRightHom k A₁ A₂ C c • splitLeftHom k A₁ A₂ C z • y =
      splitLeftHom k A₁ A₂ C z • splitRightHom k A₁ A₂ C c • y := by
  rw [smul_smul, smul_smul, (splitLeftHom_commute z c).eq]

/-- The action of `c` on the split module. -/
def actionHom (c : C) : SplitLeft k A₁ A₂ C Y →ₗ[A₁ ⊗[k] A₂] SplitLeft k A₁ A₂ C Y where
  toFun y := of (splitRightHom k A₁ A₂ C c • of.symm y)
  map_add' y y' := smul_add (splitRightHom k A₁ A₂ C c) (of.symm y) (of.symm y')
  map_smul' z y := splitRightHom_smul_comm c z (of.symm y)

theorem actionHom_of (c : C) (y : Y) :
    actionHom c (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) y) =
      of (splitRightHom k A₁ A₂ C c • y) := rfl

variable (Y) in
/-- **The action of `C`** on the split module, by `A₁ ⊗ A₂`-linear maps. -/
def action : C →ₐ[k] Module.End (A₁ ⊗[k] A₂) (SplitLeft k A₁ A₂ C Y) where
  toFun c := actionHom c
  map_one' := LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C)).surjective y
    rw [actionHom_of, map_one, one_smul]
    rfl
  map_mul' c c' := LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C)).surjective y
    rw [Module.End.mul_apply, actionHom_of, actionHom_of, actionHom_of, map_mul, mul_smul]
  map_zero' := LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C)).surjective y
    rw [actionHom_of, map_zero, LinearMap.zero_apply, zero_smul (A₁ ⊗[k] (A₂ ⊗[k] C)) y,
      map_zero]
  map_add' c c' := LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C)).surjective y
    rw [LinearMap.add_apply, actionHom_of, actionHom_of, actionHom_of, map_add, add_smul,
      map_add]
  commutes' c := LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C)).surjective y
    rw [Module.algebraMap_end_apply]
    change of (splitRightHom k A₁ A₂ C (algebraMap k C c) • y) =
      of (algebraMap k (A₁ ⊗[k] (A₂ ⊗[k] C)) c • y)
    rw [AlgHom.commutes]

theorem action_of (c : C) (y : Y) :
    action Y c (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) y) =
      of (splitRightHom k A₁ A₂ C c • y) := rfl

variable {Y' : Type*} [AddCommGroup Y'] [Module (A₁ ⊗[k] (A₂ ⊗[k] C)) Y']

/-- A map of modules over `A₁ ⊗ (A₂ ⊗ C)` as a map of the split modules. -/
def map (f : Y →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y') :
    SplitLeft k A₁ A₂ C Y →ₗ[A₁ ⊗[k] A₂] SplitLeft k A₁ A₂ C Y' where
  toFun y := of (f (of.symm y))
  map_add' y y' := f.map_add (of.symm y) (of.symm y')
  map_smul' z y := f.map_smul (splitLeftHom k A₁ A₂ C z) (of.symm y)

theorem map_of (f : Y →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y') (y : Y) :
    map f (of (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) y) = of (f y) := rfl

theorem map_action (f : Y →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y') (c : C) (y : SplitLeft k A₁ A₂ C Y) :
    map f (action Y c y) = action Y' c (map f y) :=
  congrArg of (f.map_smul (splitRightHom k A₁ A₂ C c) (of.symm y))

theorem map_injective {f : Y →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y'} (hf : Function.Injective f) :
    Function.Injective (map (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) f) := hf

theorem map_surjective {f : Y →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y'} (hf : Function.Surjective f) :
    Function.Surjective (map (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) f) := hf

theorem map_exact {Y'' : Type*} [AddCommGroup Y''] [Module (A₁ ⊗[k] (A₂ ⊗[k] C)) Y'']
    {f : Y →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y'} {g : Y' →ₗ[A₁ ⊗[k] (A₂ ⊗[k] C)] Y''}
    (h : Function.Exact f g) :
    Function.Exact (map (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) f)
      (map (k := k) (A₁ := A₁) (A₂ := A₂) (C := C) g) := h

end SplitLeft

end

end Categorification
