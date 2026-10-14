/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Restriction along a nonunital ring map, and the induction–restriction adjunction

Let `φ : A →ₙ+* B` be a nonunital ring map, so that `e = φ 1` is an idempotent of `B`.
Restriction along `φ` sends a `B`-module `M` to `e M = {m | e m = m}`, an `A`-module through
`φ` (`Res φ M`). It is right adjoint to induction `Ind N φ = B e ⊗_A N`
(`adjunction : functor φ ⊣ resFunctor φ`), with unit `n ↦ e ⊗ n` and counit
`z ⊗ m ↦ z m`. This is the induction/restriction adjunction of Khovanov–Lauda I
(arXiv:0803.4121v2, §2.6) and Kang–Kashiwara (arXiv:1102.4677v4, §4.2) for the nonunital
inclusions of (cyclotomic) KLR algebras. Ungraded; no flatness is needed.
-/

namespace Categorification

open MulOpposite CategoryTheory

noncomputable section

namespace InductionAlong

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B)

section Res

variable (M : Type w) [AddCommGroup M] [Module B M]

/-- The `φ(1)`-fixed part of a `B`-module. -/
def fixedSub : AddSubgroup M where
  carrier := {m | φ 1 • m = m}
  add_mem' {x y} hx hy := by
    change φ 1 • (x + y) = x + y
    rw [smul_add, hx, hy]
  zero_mem' := smul_zero _
  neg_mem' {x} hx := by
    change φ 1 • -x = -x
    rw [smul_neg, hx]

/-- **Restriction along `φ`**: `φ(1) M`, an `A`-module through `φ`. -/
def Res : Type w := fixedSub φ M

instance : AddCommGroup (Res φ M) := inferInstanceAs (AddCommGroup (fixedSub φ M))

namespace Res

variable {φ M}

/-- The underlying element. -/
def val (m : Res φ M) : M := (show fixedSub φ M from m).1

theorem prop (m : Res φ M) : φ 1 • m.val = m.val := (show fixedSub φ M from m).2

/-- An element fixed by `φ(1)`. -/
def mk (m : M) (h : φ 1 • m = m) : Res φ M := (⟨m, h⟩ : fixedSub φ M)

@[simp] theorem val_mk (m : M) (h : φ 1 • m = m) : (mk m h : Res φ M).val = m := rfl

theorem ext {m m' : Res φ M} (h : m.val = m'.val) : m = m' :=
  Subtype.ext (p := fun x => x ∈ fixedSub φ M) h

@[simp] theorem val_add (m m' : Res φ M) : (m + m').val = m.val + m'.val := rfl

@[simp] theorem val_zero : (0 : Res φ M).val = 0 := rfl

instance : Module A (Res φ M) where
  smul a m := mk (φ a • m.val) (by rw [smul_smul, ← map_mul, one_mul])
  one_smul m := ext m.prop
  mul_smul a b m := ext (by
    change φ (a * b) • m.val = φ a • φ b • m.val
    rw [map_mul, mul_smul])
  smul_zero a := ext (smul_zero (φ a))
  smul_add a m m' := ext (smul_add (φ a) m.val m'.val)
  add_smul a b m := ext (by
    change φ (a + b) • m.val = φ a • m.val + φ b • m.val
    rw [map_add, add_smul])
  zero_smul m := ext (by
    change φ 0 • m.val = 0
    rw [map_zero, zero_smul])

@[simp] theorem val_smul (a : A) (m : Res φ M) : (a • m).val = φ a • m.val := rfl

variable {M' M'' : Type w} [AddCommGroup M'] [Module B M'] [AddCommGroup M''] [Module B M'']

/-- Functoriality of restriction. -/
def map (f : M →ₗ[B] M') : Res φ M →ₗ[A] Res φ M' where
  toFun m := mk (f m.val) (by rw [← map_smul, m.prop])
  map_add' m m' := ext (map_add f m.val m'.val)
  map_smul' a m := ext (map_smul f (φ a) m.val)

@[simp] theorem val_map (f : M →ₗ[B] M') (m : Res φ M) : (map f m).val = f m.val := rfl

end Res

end Res

/-- Restriction along `φ` as a functor between module categories. -/
def resFunctor : ModuleCat.{max u w} B ⥤ ModuleCat.{max u w} A where
  obj M := ModuleCat.of A (Res φ M)
  map f := ModuleCat.ofHom (Res.map f.hom)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ => Res.ext rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => Res.ext rfl)

variable {φ}

/-- The unit `n ↦ φ(1) ⊗ n`. -/
def unitMap (N : Type w) [AddCommGroup N] [Module A N] : N →ₗ[A] Res φ (Ind N φ) where
  toFun n := Res.mk (Ind.tmul (unitGen φ) n) (by
    rw [Ind.smul_tmul]
    congr 1
    exact Subtype.ext (unit_mul_unit φ))
  map_add' n n' := Res.ext (Ind.tmul_add _ n n')
  map_smul' a n := Res.ext (by
    change Ind.tmul (unitGen φ) (a • n) = φ a • Ind.tmul (unitGen φ) n
    rw [← Ind.op_smul_tmul, Ind.smul_tmul]
    congr 1
    refine Subtype.ext ?_
    change φ 1 * φ a = φ a * φ 1
    rw [← map_mul, ← map_mul, mul_one, one_mul])

@[simp] theorem unitMap_val (N : Type w) [AddCommGroup N] [Module A N] (n : N) :
    (unitMap (φ := φ) N n).val = Ind.tmul (unitGen φ) n := rfl

/-- The counit `z ⊗ m ↦ z m`. -/
def counitMap (M : Type w) [AddCommGroup M] [Module B M] : Ind (Res φ M) φ →ₗ[B] M :=
  Ind.lift (fun z m => z.1 • m.val) (fun z z' m => add_smul z.1 z'.1 m.val)
    (fun z m m' => smul_add z.1 m.val m'.val)
    (fun z a m => by
      change (z.1 * φ a) • m.val = z.1 • φ a • m.val
      rw [mul_smul])
    (fun b z m => by
      change (b * z.1) • m.val = b • z.1 • m.val
      rw [mul_smul])

@[simp] theorem counitMap_tmul (M : Type w) [AddCommGroup M] [Module B M] (z : Corner φ)
    (m : Res φ M) : counitMap M (Ind.tmul z m) = z.1 • m.val := rfl

variable (φ)

/-- **Induction is left adjoint to restriction** along a nonunital ring map. -/
def adjunction : functor.{u, w} φ ⊣ resFunctor.{u, w} φ :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app N := ModuleCat.ofHom (unitMap N)
          naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => Res.ext rfl) }
      counit :=
        { app M := ModuleCat.ofHom (counitMap M)
          naturality _ _ f := ModuleCat.hom_ext (Ind.ext fun z m =>
            (map_smul f.hom z.1 m.val).symm) }
      left_triangle := by
        ext N : 2
        refine ModuleCat.hom_ext (Ind.ext fun z n => ?_)
        change z.1 • Ind.tmul (unitGen φ) n = Ind.tmul z n
        rw [Ind.smul_tmul]
        congr 1
        exact Subtype.ext z.2
      right_triangle := by
        ext M : 2
        refine ModuleCat.hom_ext (LinearMap.ext fun m => Res.ext ?_)
        exact m.prop }

@[simp] theorem adjunction_unit_app_val (N : ModuleCat.{max u w} A) (n : N) :
    ((adjunction.{u, w} φ).unit.app N n).val = Ind.tmul (unitGen φ) n := rfl

@[simp] theorem adjunction_counit_app_tmul (M : ModuleCat.{max u w} B) (z : Corner φ)
    (m : Res φ M) : (adjunction.{u, w} φ).counit.app M (Ind.tmul z m) = z.1 • m.val := rfl

instance : (functor.{u, w} φ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (Ind.ext fun z n => Ind.tmul_add z (f n) (g n))

instance : (resFunctor.{u, w} φ).Additive where
  map_add := ModuleCat.hom_ext (LinearMap.ext fun _ => Res.ext rfl)

end InductionAlong

end

end Categorification
