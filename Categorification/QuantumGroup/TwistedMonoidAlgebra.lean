/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Twisted monoid algebras

For a commutative ring `K`, a monoid `M` and a normalised `K`-valued 2-cocycle
`τ : M → M → K`, i.e.

* `τ 1 a = τ a 1 = 1`, and
* `τ a b * τ (a * b) c = τ b c * τ a (b * c)`,

the *twisted monoid algebra* `K^τ[M]` is the free `K`-module on `M` with multiplication
`[a] * [b] = τ a b • [a * b]`. For `τ = 1` this is the monoid algebra `K[M]`.

This is the (purely algebraic) device used for the twisted tensor square
`'f ⊗ 'f` of Lusztig's free algebra `'f` (Lusztig, *Introduction to quantum groups*,
§1.2.2; Khovanov–Lauda, arXiv:0803.4121v2, eq. (3.1) = `eq_quasi_commute`): the
multiplication `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = v^{|x₂|·|y₁|} x₁y₁ ⊗ x₂y₂` on basis tensors of words
is the twisted monoid algebra of `FreeMonoid I × FreeMonoid I` for the cocycle
`((u₁, u₂), (w₁, w₂)) ↦ v^{|u₂|·|w₁|}`; see `Categorification.QuantumGroup.PreF`.

## Main definitions

* `TwistCocycle K M` — a normalised `K`-valued 2-cocycle on `M`.
* `TwistedMonoidAlgebra σ` — the twisted monoid algebra, with its `Ring` and
  `Algebra K` instances.
* `TwistedMonoidAlgebra.single`, `TwistedMonoidAlgebra.lift`,
  `TwistedMonoidAlgebra.lhom_ext`, `TwistedMonoidAlgebra.induction_linear` — the
  module-level API (the underlying module is `M →₀ K`).
-/

noncomputable section

namespace Categorification.QuantumGroup

/-- A normalised `K`-valued 2-cocycle on a monoid `M`. -/
structure TwistCocycle (K : Type*) (M : Type*) [CommRing K] [Monoid M] where
  /-- The cocycle. -/
  τ : M → M → K
  one_left : ∀ a, τ 1 a = 1
  one_right : ∀ a, τ a 1 = 1
  assoc : ∀ a b c, τ a b * τ (a * b) c = τ b c * τ a (b * c)

variable {K : Type*} {M : Type*} [CommRing K] [Monoid M]

/-- The twisted monoid algebra `K^τ[M]` of a normalised 2-cocycle `σ`. As a `K`-module it
is `M →₀ K`; the product is `[a] * [b] = τ a b • [a * b]`. -/
def TwistedMonoidAlgebra (_σ : TwistCocycle K M) : Type _ := M →₀ K

namespace TwistedMonoidAlgebra

variable (σ : TwistCocycle K M)

instance instAddCommGroup : AddCommGroup (TwistedMonoidAlgebra σ) :=
  inferInstanceAs (AddCommGroup (M →₀ K))

instance instModule : Module K (TwistedMonoidAlgebra σ) :=
  inferInstanceAs (Module K (M →₀ K))

variable {σ}

/-- The basis vector `r • [m]`. -/
def single (m : M) (r : K) : TwistedMonoidAlgebra σ := Finsupp.single m r

@[simp] theorem single_zero (m : M) : (single m 0 : TwistedMonoidAlgebra σ) = 0 :=
  Finsupp.single_zero m

theorem single_add (m : M) (r s : K) :
    (single m (r + s) : TwistedMonoidAlgebra σ) = single m r + single m s :=
  Finsupp.single_add m r s

theorem smul_single (c : K) (m : M) (r : K) :
    c • (single m r : TwistedMonoidAlgebra σ) = single m (c * r) :=
  Finsupp.smul_single c m r

theorem single_eq_smul (m : M) (r : K) :
    (single m r : TwistedMonoidAlgebra σ) = r • single m 1 := by
  rw [smul_single, mul_one]

/-- Linear-combination induction on the twisted monoid algebra. -/
@[elab_as_elim]
theorem induction_linear {motive : TwistedMonoidAlgebra σ → Prop} (x : TwistedMonoidAlgebra σ)
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (single : ∀ m r, motive (single m r)) : motive x :=
  Finsupp.induction_linear (motive := motive) x zero add single

/-- Two linear maps out of `K^τ[M]` agreeing on the basis vectors `[m]` are equal. -/
theorem lhom_ext {N : Type*} [AddCommMonoid N] [Module K N]
    ⦃φ ψ : TwistedMonoidAlgebra σ →ₗ[K] N⦄ (h : ∀ m, φ (single m 1) = ψ (single m 1)) :
    φ = ψ :=
  Finsupp.lhom_ext (φ := φ) (ψ := ψ) fun m r => by
    have := h m
    change φ (single m r) = ψ (single m r)
    rw [single_eq_smul, map_smul, map_smul, this]

/-- The linear map out of `K^τ[M]` sending `[m]` to `f m`. -/
noncomputable def lift {N : Type*} [AddCommMonoid N] [Module K N] (f : M → N) :
    TwistedMonoidAlgebra σ →ₗ[K] N :=
  Finsupp.linearCombination K f

@[simp] theorem lift_single {N : Type*} [AddCommMonoid N] [Module K N] (f : M → N)
    (m : M) (r : K) : lift (σ := σ) f (single m r) = r • f m :=
  Finsupp.linearCombination_single K r m

variable (σ)

/-- The multiplication of `K^τ[M]` as a bilinear map. -/
noncomputable def mulL :
    TwistedMonoidAlgebra σ →ₗ[K] TwistedMonoidAlgebra σ →ₗ[K] TwistedMonoidAlgebra σ :=
  lift fun a => lift fun b => single (a * b) (σ.τ a b)

variable {σ}

theorem mulL_single (a b : M) (r s : K) :
    mulL σ (single a r) (single b s) = single (a * b) (σ.τ a b * r * s) := by
  simp only [mulL, lift_single, LinearMap.smul_apply, smul_single]
  congr 1
  ring

instance instRing : Ring (TwistedMonoidAlgebra σ) where
  __ := instAddCommGroup σ
  mul x y := mulL σ x y
  one := single 1 1
  left_distrib x y z := map_add (mulL σ x) y z
  right_distrib x y z := by
    change mulL σ (x + y) z = mulL σ x z + mulL σ y z
    rw [map_add, LinearMap.add_apply]
  zero_mul x := by
    change mulL σ 0 x = 0
    rw [map_zero, LinearMap.zero_apply]
  mul_zero x := map_zero (mulL σ x)
  mul_assoc x y z := by
    change mulL σ (mulL σ x y) z = mulL σ x (mulL σ y z)
    induction x using induction_linear with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single a r =>
      induction y using induction_linear with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single b s =>
        induction z using induction_linear with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
        | single c t =>
          simp only [mulL_single, mul_assoc]
          congr 1
          have := σ.assoc a b c
          linear_combination (r * s * t) * this
  one_mul x := by
    change mulL σ (single 1 1) x = x
    induction x using induction_linear with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy]
    | single m r => rw [mulL_single, one_mul, σ.one_left, one_mul, one_mul]
  mul_one x := by
    change mulL σ x (single 1 1) = x
    induction x using induction_linear with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy]
    | single m r => rw [mulL_single, mul_one, σ.one_right, one_mul, mul_one]

theorem mul_def (x y : TwistedMonoidAlgebra σ) : x * y = mulL σ x y := rfl

theorem one_def : (1 : TwistedMonoidAlgebra σ) = single 1 1 := rfl

theorem single_mul_single (a b : M) (r s : K) :
    (single a r : TwistedMonoidAlgebra σ) * single b s = single (a * b) (σ.τ a b * r * s) :=
  mulL_single a b r s

noncomputable instance instAlgebra : Algebra K (TwistedMonoidAlgebra σ) :=
  Algebra.ofModule
    (fun c x y => by
      change mulL σ (c • x) y = c • mulL σ x y
      rw [map_smul, LinearMap.smul_apply])
    (fun c x y => map_smul (mulL σ x) c y)

theorem algebraMap_apply (c : K) :
    algebraMap K (TwistedMonoidAlgebra σ) c = single 1 c := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, smul_single, mul_one]

end TwistedMonoidAlgebra

end Categorification.QuantumGroup

end
