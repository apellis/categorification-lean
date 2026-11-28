/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.ModuleCatLinear
import Categorification.KLR.BaseChange
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Endomorphisms of a two-step restriction of right modules given by elements

Let `φ₁ : A →ₙ+* B` and `φ₂ : B →ₙ+* Dᵐᵒᵖ` be nonunital ring maps, so that the two-step
restriction `G = Res_{φ₁} ∘ Res_{φ₂}` takes right `D`-modules (left `Dᵐᵒᵖ`-modules) to
`A`-modules. An element `z : D` whose right action commutes with the image of `A`
(`twoResInt`) acts on `G` by right multiplication (`twoResEnd`). This is `k`-linear and
reverses products (`twoResEnd_mul`), so polynomials in such endomorphisms are the polynomials
in the elements with the variables reversed (`twoResEnd_ncEval`). It is the form in which the
KLR relations for two appended strands, which hold in `D`, become relations between natural
transformations, as in `TwoRep.RouqUpKLR`.
-/

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite

universe u

noncomputable section

variable (k : Type u) [CommRing k] {A B D : Type u} [Ring A] [Ring B] [Ring D]
  [Algebra k D] (φ₁ : A →ₙ+* B) (φ₂ : B →ₙ+* Dᵐᵒᵖ)

/-- The elements of `D` whose right action commutes with the image of `A`. -/
def twoResInt : Subalgebra k D where
  carrier := {z | ∀ a, op z * φ₂ (φ₁ a) = φ₂ (φ₁ a) * op z}
  mul_mem' {z z'} hz hz' a := by
    change op z' * op z * _ = _ * (op z' * op z)
    rw [mul_assoc, hz a, ← mul_assoc, hz' a, mul_assoc]
  add_mem' {z z'} hz hz' a := by
    change (op z + op z') * _ = _ * (op z + op z')
    rw [add_mul, mul_add, hz a, hz' a]
  algebraMap_mem' c a := by
    change algebraMap k Dᵐᵒᵖ c * _ = _ * algebraMap k Dᵐᵒᵖ c
    exact Algebra.commutes c _

/-- The two-step restriction of right `D`-modules. -/
abbrev twoRes : ModuleCat.{u} Dᵐᵒᵖ ⥤ ModuleCat.{u} A := resFunctor.{u, u} φ₂ ⋙ resFunctor.{u, u} φ₁

variable {k φ₁ φ₂}

theorem twoRes_fixed {M : ModuleCat.{u} Dᵐᵒᵖ} (w : (twoRes φ₁ φ₂).obj M) :
    φ₂ (φ₁ 1) • w.val.val = w.val.val :=
  congrArg Res.val w.prop

/-- Endomorphisms of the two-step restriction agree once they agree on underlying elements. -/
theorem twoRes_end_ext {α β : twoRes φ₁ φ₂ ⟶ twoRes φ₁ φ₂}
    (h : ∀ M w, ((α.app M).hom w).val.val = ((β.app M).hom w).val.val) : α = β :=
  NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun w =>
    Res.ext (Res.ext (h M w))))

variable (z : twoResInt k φ₁ φ₂)

private theorem fix_inner {M : Type u} [AddCommGroup M] [Module Dᵐᵒᵖ M] (m : M)
    (h : φ₂ (φ₁ 1) • m = m) : φ₂ 1 • (op z.1 • m) = op z.1 • m := by
  have hz := z.2 1
  calc φ₂ 1 • (op z.1 • m) = (φ₂ 1 * (op z.1 * φ₂ (φ₁ 1))) • m := by
        rw [mul_smul, mul_smul, h]
    _ = (φ₂ (1 * φ₁ 1) * op z.1) • m := by
        rw [show op z.1 * φ₂ (φ₁ 1) = _ from hz, ← mul_assoc, ← map_mul]
    _ = op z.1 • m := by rw [one_mul, ← hz, mul_smul, h]

private theorem fix_outer {M : Type u} [AddCommGroup M] [Module Dᵐᵒᵖ M] (m : M)
    (h : φ₂ (φ₁ 1) • m = m) : φ₂ (φ₁ 1) • (op z.1 • m) = op z.1 • m := by
  rw [smul_smul, ← show op z.1 * φ₂ (φ₁ 1) = _ from z.2 1, mul_smul, h]

/-- The components of `twoResEnd`: right multiplication by `z`. -/
def twoResEndApp (M : ModuleCat.{u} Dᵐᵒᵖ) :
    (twoRes φ₁ φ₂).obj M ⟶ (twoRes φ₁ φ₂).obj M :=
  ModuleCat.ofHom
    { toFun := fun w => (Res.mk (Res.mk (op z.1 • (w.val.val : M))
          (fix_inner z _ (twoRes_fixed w)) : Res φ₂ M)
          (Res.ext (fix_outer z _ (twoRes_fixed w))) : Res φ₁ (Res φ₂ M))
      map_add' := fun w w' => Res.ext (Res.ext (smul_add _ (w.val.val : M) w'.val.val))
      map_smul' := fun a w => Res.ext (Res.ext (by
        change op z.1 • φ₂ (φ₁ a) • (w.val.val : M) = φ₂ (φ₁ a) • op z.1 • (w.val.val : M)
        rw [smul_smul, smul_smul, z.2 a])) }

/-- **Right multiplication by a self-intertwining element** as an endomorphism of the two-step
restriction. -/
def twoResEnd : End (twoRes φ₁ φ₂) :=
  show twoRes φ₁ φ₂ ⟶ twoRes φ₁ φ₂ from
  { app M := twoResEndApp z M
    naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext
      (f.hom.map_smul (op z.1) w.val.val).symm)) }

theorem twoResEnd_app_val (M : ModuleCat.{u} Dᵐᵒᵖ) (w : (twoRes φ₁ φ₂).obj M) :
    (((twoResEnd z).app M).hom w).val.val = op z.1 • w.val.val := rfl

variable (φ₁ φ₂) in
theorem twoResEnd_one : twoResEnd (1 : twoResInt k φ₁ φ₂) = 1 :=
  twoRes_end_ext fun _ w => one_smul _ w.val.val

theorem twoResEnd_mul (z' : twoResInt k φ₁ φ₂) :
    twoResEnd (z * z') = twoResEnd z ≫ twoResEnd z' :=
  twoRes_end_ext fun _ w => by
    change op (z.1 * z'.1) • w.val.val = op z'.1 • op z.1 • w.val.val
    rw [MulOpposite.op_mul, mul_smul]

theorem twoResEnd_add (z' : twoResInt k φ₁ φ₂) :
    twoResEnd (z + z') = twoResEnd z + twoResEnd z' :=
  twoRes_end_ext fun _ w => by
    change op (z.1 + z'.1) • w.val.val = op z.1 • w.val.val + op z'.1 • w.val.val
    rw [MulOpposite.op_add, add_smul]

variable [Algebra k A] (hΦ : ∀ c : k, φ₂ (φ₁ (algebraMap k A c)) = algebraMap k Dᵐᵒᵖ c * φ₂ (φ₁ 1))
include hΦ

theorem twoResEnd_smul (c : k) : twoResEnd (c • z) = c • twoResEnd z :=
  twoRes_end_ext fun M w => by
    rw [NatTrans.app_smul, ModuleCat.smul_hom_apply]
    change op (c • z.1) • w.val.val = φ₂ (φ₁ (algebraMap k A c)) • op z.1 • w.val.val
    rw [hΦ, MulOpposite.op_smul, Algebra.smul_def, mul_smul, mul_smul, smul_smul (φ₂ (φ₁ 1)),
      ← show op z.1 * φ₂ (φ₁ 1) = _ from z.2 1, mul_smul, twoRes_fixed]

variable (φ₁ φ₂) in
/-- `twoResEnd` as a `k`-linear map. -/
def twoResEndLinear : twoResInt k φ₁ φ₂ →ₗ[k] End (twoRes φ₁ φ₂) where
  toFun := twoResEnd
  map_add' := twoResEnd_add
  map_smul' c z := twoResEnd_smul z hΦ c

omit hΦ in
variable (φ₁ φ₂) in
/-- Polynomials in endomorphisms given by elements are given by the polynomials in the
elements, with the variables read in the opposite order. -/
theorem twoResEnd_ncEval {n : ℕ} (hΦ : ∀ c : k,
      φ₂ (φ₁ (algebraMap k A c)) = algebraMap k Dᵐᵒᵖ c * φ₂ (φ₁ 1))
    (y : Fin n → twoResInt k φ₁ φ₂) (P : MvPolynomial (Fin n) k) :
    twoResEnd (KLR.ncEval y P) =
      KLR.ncEval (fun a => twoResEnd (y (Fin.rev a))) (MvPolynomial.rename Fin.rev P) :=
  KLR.ncEval_antihom (twoResEndLinear φ₁ φ₂ hΦ) (twoResEnd_one φ₁ φ₂)
    (fun z z' => twoResEnd_mul z z') y P

end

end Categorification.InductionAlong
