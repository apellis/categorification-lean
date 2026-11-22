/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.CategoryTheory.PiShift
import Categorification.Sl2Categorification.NilHeckeAction
import Categorification.CategoryTheory.PiAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# NilHecke actions on restriction along a tower of rings

Let `B 0, B 1, …` be rings with nonunital maps `φ m : B m → B (m + 1)`. Restriction along the
`φ m` assembles to an endofunctor `E` of `∀ m, ModuleCat (B m)` which lowers the level by one
(`resTower`). Elements `y m ∈ B (m + 1)` commuting with the image of `φ m`, and `t m ∈ B (m + 2)`
commuting with the image of `φ (m + 1) ∘ φ m`, act on `E` and on `E²` by left multiplication. If
they satisfy the nilHecke relations in the rings, these actions satisfy the nilHecke relations of
Chuang–Rouquier (arXiv:math/0407205v2, §5.2.1) in the endomorphism rings (`resTowerNilHecke`).

This is how the dot and the crossing of the black strands act on Webster's `Eᵢ` along an
`i`-string (arXiv:1309.3796v2, §4.6 and §5): the rightmost black strands carry them.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory Sl2

universe u

section Act

variable {A₀ A₁ A₂ : Type u} [Ring A₀] [Ring A₁] [Ring A₂] {ψ₀ : A₀ →ₙ+* A₁} {ψ₁ : A₁ →ₙ+* A₂}

/-- Left multiplication by an element commuting with the image of `ψ₀`, on `Res ψ₀ M`. -/
def resAct (c : A₁) (hc : ∀ a, c * ψ₀ a = ψ₀ a * c) (M : Type u) [AddCommGroup M]
    [Module A₁ M] : Res ψ₀ M →ₗ[A₀] Res ψ₀ M where
  toFun r := Res.mk (c • r.val) (by rw [smul_smul, ← hc, mul_smul, r.prop])
  map_add' r r' := Res.ext (smul_add c r.val r'.val)
  map_smul' a r := Res.ext (by
    change c • (ψ₀ a • r.val) = ψ₀ a • (c • r.val)
    rw [smul_smul, smul_smul, hc])

@[simp] theorem resAct_val (c : A₁) (hc : ∀ a, c * ψ₀ a = ψ₀ a * c) (M : Type u)
    [AddCommGroup M] [Module A₁ M] (r : Res ψ₀ M) : (resAct c hc M r).val = c • r.val := rfl

/-- Left multiplication on `Res ψ₀ (Res ψ₁ M)` by an element fixed by `ψ₁ 1` and commuting with
the image of `ψ₁ ∘ ψ₀`. -/
def resAct₂ (c : A₂) (hfix : ψ₁ 1 * c = c) (hc : ∀ a, c * ψ₁ (ψ₀ a) = ψ₁ (ψ₀ a) * c)
    (M : Type u) [AddCommGroup M] [Module A₂ M] :
    Res ψ₀ (Res ψ₁ M) →ₗ[A₀] Res ψ₀ (Res ψ₁ M) where
  toFun r := Res.mk (Res.mk (c • r.val.val) (by rw [smul_smul, hfix])) (Res.ext (by
    change ψ₁ (ψ₀ 1) • c • r.val.val = c • r.val.val
    rw [smul_smul, ← hc, mul_smul]
    exact congrArg (c • ·) (congrArg Res.val r.prop)))
  map_add' r r' := Res.ext (Res.ext (smul_add c r.val.val r'.val.val))
  map_smul' a r := Res.ext (Res.ext (by
    change c • (ψ₁ (ψ₀ a) • r.val.val) = ψ₁ (ψ₀ a) • (c • r.val.val)
    rw [smul_smul, smul_smul, hc]))

@[simp] theorem resAct₂_val_val (c : A₂) (hfix : ψ₁ 1 * c = c)
    (hc : ∀ a, c * ψ₁ (ψ₀ a) = ψ₁ (ψ₀ a) * c) (M : Type u) [AddCommGroup M] [Module A₂ M]
    (r : Res ψ₀ (Res ψ₁ M)) : (resAct₂ c hfix hc M r).val.val = c • r.val.val := rfl

end Act

variable {B : ℕ → Type u} [∀ m, Ring (B m)] (φ : ∀ m, B m →ₙ+* B (m + 1))

/-- Restriction along a tower of rings, lowering the level by one. -/
abbrev resTower : (∀ m, ModuleCat.{u} (B m)) ⥤ (∀ m, ModuleCat.{u} (B m)) :=
  PiShift.down fun m => resFunctor.{u, u} (φ m)

/-- The action of `y m ∈ B (m + 1)` on `E` at level `m`. -/
def resTowerX (y : ∀ m, B (m + 1)) (hy : ∀ m a, y m * φ m a = φ m a * y m) :
    End (resTower φ) where
  app M m := ModuleCat.ofHom (resAct (y m) (hy m) (M (m + 1)))
  naturality _ _ f := funext fun m => ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext
    ((f (m + 1)).hom.map_smul (y m) r.val).symm)

/-- The action of `t m ∈ B (m + 2)` on `E²` at level `m`. -/
def resTowerT (t : ∀ m, B (m + 2)) (hfix : ∀ m, φ (m + 1) 1 * t m = t m)
    (ht : ∀ m a, t m * φ (m + 1) (φ m a) = φ (m + 1) (φ m a) * t m) :
    End (resTower φ ⋙ resTower φ) where
  app M m := ModuleCat.ofHom (resAct₂ (t m) (hfix m) (ht m) (M (m + 2)))
  naturality _ _ f := funext fun m => ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext
    (Res.ext ((f (m + 2)).hom.map_smul (t m) r.val.val).symm))

variable {φ}

theorem resTower_ext {F : (∀ m, ModuleCat.{u} (B m)) ⥤ (∀ m, ModuleCat.{u} (B m))}
    {a b : End F} (h : ∀ M m r, (a.app M m).hom r = (b.app M m).hom r) : a = b :=
  NatTrans.ext (funext fun M => funext fun m => ModuleCat.hom_ext (LinearMap.ext (h M m)))

theorem resTower_add_app {F : (∀ m, ModuleCat.{u} (B m)) ⥤ (∀ m, ModuleCat.{u} (B m))}
    (a b : End F) M m r : ((a + b).app M m).hom r = (a.app M m).hom r + (b.app M m).hom r :=
  rfl

theorem resTower_mul_app {F : (∀ m, ModuleCat.{u} (B m)) ⥤ (∀ m, ModuleCat.{u} (B m))}
    (a b : End F) M m r : ((a * b).app M m).hom r = (a.app M m).hom ((b.app M m).hom r) :=
  rfl

theorem resTower_one_app {F : (∀ m, ModuleCat.{u} (B m)) ⥤ (∀ m, ModuleCat.{u} (B m))}
    M m r : (((1 : End F)).app M m).hom r = r :=
  rfl

theorem resTower_zero_app {F : (∀ m, ModuleCat.{u} (B m)) ⥤ (∀ m, ModuleCat.{u} (B m))}
    M m r : (((0 : End F)).app M m).hom r = 0 :=
  rfl

private theorem smul_eq_add_of_sub {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    {a b e : R} {w : N} (h : a - b = e) (hw : e • w = w) : a • w = w + b • w :=
  (eq_add_of_sub_eq' (by rw [← sub_smul, h, hw])).trans (add_comm _ _)

variable (φ)

/-- **NilHecke action on restriction along a tower.** If `y m` and `t m` satisfy the nilHecke
relations in the rings, their actions on `E` and `E²` satisfy the nilHecke relations of
Chuang–Rouquier (arXiv:math/0407205v2, §5.2.1). The ring relations hold modulo the idempotent
`φ (m + 1) (φ m 1)`, which acts as the identity on `E²`. -/
def resTowerNilHecke (y : ∀ m, B (m + 1)) (hy : ∀ m a, y m * φ m a = φ m a * y m)
    (t : ∀ m, B (m + 2)) (hfix : ∀ m, φ (m + 1) 1 * t m = t m)
    (ht : ∀ m a, t m * φ (m + 1) (φ m a) = φ (m + 1) (φ m a) * t m)
    (htt : ∀ m, t m * t m = 0)
    (hbraid : ∀ m, t (m + 1) * φ (m + 2) (t m) * t (m + 1) =
      φ (m + 2) (t m) * t (m + 1) * φ (m + 2) (t m))
    (hyt : ∀ m, y (m + 1) * t m - t m * φ (m + 1) (y m) = φ (m + 1) (φ m 1))
    (hty : ∀ m, t m * y (m + 1) - φ (m + 1) (y m) * t m = φ (m + 1) (φ m 1)) :
    NilHeckeData (resTower φ) where
  X := resTowerX φ y hy
  T := resTowerT φ t hfix ht
  T_mul_T := resTower_ext fun M m r => Res.ext (Res.ext (by
    change t m • t m • r.val.val = 0
    rw [smul_smul, htt, zero_smul]))
  braid := resTower_ext fun M m r => Res.ext (Res.ext (Res.ext (by
    change t (m + 1) • φ (m + 2) (t m) • t (m + 1) • r.val.val.val =
      φ (m + 2) (t m) • t (m + 1) • φ (m + 2) (t m) • r.val.val.val
    rw [smul_smul, smul_smul, smul_smul, smul_smul, hbraid])))
  x_T_sub := by
    refine sub_eq_of_eq_add (resTower_ext fun M m r => Res.ext (Res.ext ?_))
    change y (m + 1) • t m • r.val.val = r.val.val + t m • φ (m + 1) (y m) • r.val.val
    rw [smul_smul, smul_smul]
    exact smul_eq_add_of_sub (hyt m) (congrArg Res.val r.prop)
  T_x_sub := by
    refine sub_eq_of_eq_add (resTower_ext fun M m r => Res.ext (Res.ext ?_))
    change t m • y (m + 1) • r.val.val = r.val.val + φ (m + 1) (y m) • t m • r.val.val
    rw [smul_smul, smul_smul]
    exact smul_eq_add_of_sub (hty m) (congrArg Res.val r.prop)

end Categorification.InductionAlong
