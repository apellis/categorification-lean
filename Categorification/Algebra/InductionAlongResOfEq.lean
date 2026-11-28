/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes

/-!
# Restriction along pointwise equal ring maps

Two nonunital ring maps `φ, φ' : A →ₙ+* B` with `φ a = φ' a` for all `a` give the same fixed part
`φ 1 M = φ' 1 M` with the same `A`-action, so restriction along them gives isomorphic functors
(`InductionAlong.resFunctorIsoOfEq`), with identity components on underlying elements. This is
used to compare restriction along a composite with a cast to restriction along a map written
differently.
-/

namespace Categorification

open CategoryTheory

noncomputable section

namespace InductionAlong

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {φ φ' : A →ₙ+* B}

/-- `Res φ M ≃ Res φ' M` for pointwise equal `φ`, `φ'`, the identity on underlying elements. -/
def resLinearEquivOfEq (h : ∀ a, φ a = φ' a) (M : Type w) [AddCommGroup M] [Module B M] :
    Res φ M ≃ₗ[A] Res φ' M where
  toFun m := Res.mk m.val (by rw [← h]; exact m.prop)
  invFun m := Res.mk m.val (by rw [h]; exact m.prop)
  map_add' _ _ := Res.ext rfl
  map_smul' a m := Res.ext (by
    change φ a • m.val = φ' a • m.val
    rw [h])
  left_inv _ := Res.ext rfl
  right_inv _ := Res.ext rfl

@[simp] theorem resLinearEquivOfEq_val (h : ∀ a, φ a = φ' a) (M : Type w) [AddCommGroup M]
    [Module B M] (m : Res φ M) : (resLinearEquivOfEq h M m).val = m.val :=
  rfl

/-- **Restriction along pointwise equal maps**: `resFunctor φ ≅ resFunctor φ'`. -/
def resFunctorIsoOfEq (h : ∀ a, φ a = φ' a) :
    resFunctor.{u, w} φ ≅ resFunctor.{u, w} φ' :=
  NatIso.ofComponents (fun M => (resLinearEquivOfEq h M).toModuleIso) fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => Res.ext rfl)

theorem resFunctorIsoOfEq_hom_app_val (h : ∀ a, φ a = φ' a) (M : ModuleCat.{max u w} B)
    (m : Res φ M) : (((resFunctorIsoOfEq.{u, w} h).hom.app M).hom m).val = m.val :=
  rfl

end InductionAlong

end

end Categorification
