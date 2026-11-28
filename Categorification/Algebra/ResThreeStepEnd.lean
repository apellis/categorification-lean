/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ResTwoStepEnd
import Categorification.KLR.Symmetries

/-!
# Polynomials in endomorphisms of a three-step restriction given by elements

Let `φ₁ : A →ₙ+* B`, `φ₂ : B →ₙ+* C` and `φ₃ : C →ₙ+* Dᵐᵒᵖ` be nonunital ring maps, so that the
three-step restriction `G = Res_{φ₁} ∘ Res_{φ₂} ∘ Res_{φ₃}` takes right `D`-modules to
`A`-modules. An endomorphism `α` of `G` *acts by* `z : D` (`ThreeResActs α z`) when it is right
multiplication by `z` on underlying elements. Elements by which some endomorphism acts form a
`k`-subalgebra, on which acting is a `k`-linear antihomomorphism to `End G`; hence a polynomial
in endomorphisms acting by elements acts by the polynomial in the elements with the variables
read in the opposite order (`ThreeResActs.ncEval`). This is the three-strand form of
`InductionAlong.twoResEnd_ncEval`, for the polynomial right-hand side of the braid relation with
equal outer labels (Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4)).
-/

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite

universe u

noncomputable section

variable (k : Type u) [CommRing k] {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra k A] [Algebra k D] (φ₁ : A →ₙ+* B) (φ₂ : B →ₙ+* C) (φ₃ : C →ₙ+* Dᵐᵒᵖ)

/-- The three-step restriction of right `D`-modules. -/
abbrev threeRes : ModuleCat.{u} Dᵐᵒᵖ ⥤ ModuleCat.{u} A :=
  resFunctor.{u, u} φ₃ ⋙ resFunctor.{u, u} φ₂ ⋙ resFunctor.{u, u} φ₁

variable {k φ₁ φ₂ φ₃} {B' C' B'' C'' : Type u} [Ring B'] [Ring C'] [Ring B''] [Ring C'']
  {ψ₁ : A →ₙ+* B'} {ψ₂ : B' →ₙ+* C'} {ψ₃ : C' →ₙ+* Dᵐᵒᵖ}
  {χ₁ : A →ₙ+* B''} {χ₂ : B'' →ₙ+* C''} {χ₃ : C'' →ₙ+* Dᵐᵒᵖ}

/-- `α` is right multiplication by `z` on underlying elements. -/
def ThreeResActs (α : threeRes φ₁ φ₂ φ₃ ⟶ threeRes ψ₁ ψ₂ ψ₃) (z : D) : Prop :=
  ∀ (M : ModuleCat.{u} Dᵐᵒᵖ) (w : (threeRes φ₁ φ₂ φ₃).obj M),
    (((α.app M).hom w).val.val.val : M) = op z • (w.val.val.val : M)

theorem threeRes_fixed {M : ModuleCat.{u} Dᵐᵒᵖ} (w : (threeRes φ₁ φ₂ φ₃).obj M) :
    φ₃ (φ₂ (φ₁ 1)) • (w.val.val.val : M) = w.val.val.val :=
  congrArg (fun t => (Res.val (Res.val t) : M)) w.prop

/-- Endomorphisms of the three-step restriction agree once they agree on underlying elements. -/
theorem threeRes_end_ext {α β : threeRes φ₁ φ₂ φ₃ ⟶ threeRes φ₁ φ₂ φ₃}
    (h : ∀ (M : ModuleCat.{u} Dᵐᵒᵖ) (w : (threeRes φ₁ φ₂ φ₃).obj M),
      (((α.app M).hom w).val.val.val : M) = ((β.app M).hom w).val.val.val) :
    α = β :=
  NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun w =>
    Res.ext (Res.ext (Res.ext (h M w)))))

theorem ThreeResActs.unique {α β : threeRes φ₁ φ₂ φ₃ ⟶ threeRes φ₁ φ₂ φ₃} {z : D}
    (hα : ThreeResActs α z) (hβ : ThreeResActs β z) : α = β :=
  threeRes_end_ext fun M w => (hα M w).trans (hβ M w).symm

theorem ThreeResActs.id : ThreeResActs (𝟙 (threeRes φ₁ φ₂ φ₃)) 1 :=
  fun _ w => (one_smul _ (w.val.val.val)).symm

theorem ThreeResActs.comp {α : threeRes φ₁ φ₂ φ₃ ⟶ threeRes ψ₁ ψ₂ ψ₃}
    {β : threeRes ψ₁ ψ₂ ψ₃ ⟶ threeRes χ₁ χ₂ χ₃} {z z' : D}
    (hα : ThreeResActs α z) (hβ : ThreeResActs β z') : ThreeResActs (α ≫ β) (z * z') :=
  fun M w => by
    change (((β.app M).hom ((α.app M).hom w)).val.val.val : M) = _
    rw [hβ, hα, MulOpposite.op_mul, mul_smul]

theorem ThreeResActs.add {α β : threeRes φ₁ φ₂ φ₃ ⟶ threeRes ψ₁ ψ₂ ψ₃} {z z' : D}
    (hα : ThreeResActs α z) (hβ : ThreeResActs β z') : ThreeResActs (α + β) (z + z') :=
  fun M w => by
    change (((α.app M).hom w).val.val.val : M) + ((β.app M).hom w).val.val.val = _
    rw [hα, hβ, MulOpposite.op_add, add_smul]

theorem ThreeResActs.sub {α β : threeRes φ₁ φ₂ φ₃ ⟶ threeRes ψ₁ ψ₂ ψ₃} {z z' : D}
    (hα : ThreeResActs α z) (hβ : ThreeResActs β z') : ThreeResActs (α - β) (z - z') :=
  fun M w => by
    change (((α.app M).hom w).val.val.val : M) - ((β.app M).hom w).val.val.val = _
    rw [hα, hβ, MulOpposite.op_sub, sub_smul]

variable (hΦ : ∀ c : k, φ₃ (φ₂ (φ₁ (algebraMap k A c))) = algebraMap k Dᵐᵒᵖ c * φ₃ (φ₂ (φ₁ 1)))
include hΦ

theorem ThreeResActs.smul {α : threeRes φ₁ φ₂ φ₃ ⟶ threeRes φ₁ φ₂ φ₃} {z : D}
    (hα : ThreeResActs α z) (c : k) : ThreeResActs (c • α) (c • z) :=
  fun M w => by
    rw [NatTrans.app_smul, ModuleCat.smul_hom_apply]
    change φ₃ (φ₂ (φ₁ (algebraMap k A c))) • (((α.app M).hom w).val.val.val : M) = _
    rw [hΦ, mul_smul, threeRes_fixed, hα, MulOpposite.op_smul, Algebra.smul_def, mul_smul]

variable (φ₁ φ₂ φ₃ k) in
/-- The elements by which some endomorphism of the three-step restriction acts. -/
def threeResActSub : Subalgebra k D where
  carrier := {z | ∃ α : threeRes φ₁ φ₂ φ₃ ⟶ threeRes φ₁ φ₂ φ₃, ThreeResActs α z}
  mul_mem' := by
    rintro z z' ⟨α, hα⟩ ⟨β, hβ⟩
    exact ⟨α ≫ β, hα.comp hβ⟩
  add_mem' := by
    rintro z z' ⟨α, hα⟩ ⟨β, hβ⟩
    exact ⟨α + β, hα.add hβ⟩
  algebraMap_mem' c := ⟨c • 𝟙 _, by
    have h := ThreeResActs.id.smul hΦ c
    rwa [Algebra.smul_def, mul_one] at h⟩

/-- The endomorphism acting by an element of `threeResActSub`. -/
def threeResActEnd (z : threeResActSub k φ₁ φ₂ φ₃ hΦ) : End (threeRes φ₁ φ₂ φ₃) :=
  Classical.choose z.2

theorem threeResActEnd_acts (z : threeResActSub k φ₁ φ₂ φ₃ hΦ) :
    ThreeResActs (threeResActEnd hΦ z) z.1 :=
  Classical.choose_spec z.2

variable (φ₁ φ₂ φ₃ k) in
/-- Acting by elements, as a `k`-linear map. -/
def threeResActLinear : threeResActSub k φ₁ φ₂ φ₃ hΦ →ₗ[k] End (threeRes φ₁ φ₂ φ₃) where
  toFun := threeResActEnd hΦ
  map_add' z z' := (threeResActEnd_acts hΦ (z + z')).unique
    ((threeResActEnd_acts hΦ z).add (threeResActEnd_acts hΦ z'))
  map_smul' c z := (threeResActEnd_acts hΦ (c • z)).unique
    ((threeResActEnd_acts hΦ z).smul hΦ c)

/-- **Polynomials in endomorphisms acting by elements** act by the polynomial in the elements,
with the variables read in the opposite order. -/
theorem ThreeResActs.ncEval {n : ℕ} {α : Fin n → End (threeRes φ₁ φ₂ φ₃)} {z : Fin n → D}
    (h : ∀ a, ThreeResActs (α a) (z a)) (P : MvPolynomial (Fin n) k) :
    ThreeResActs (KLR.ncEval (A := End (threeRes φ₁ φ₂ φ₃)) α P)
      (KLR.ncEval (fun a => z (Fin.rev a)) (MvPolynomial.rename Fin.rev P)) := by
  let y : Fin n → threeResActSub k φ₁ φ₂ φ₃ hΦ := fun a => ⟨z (Fin.rev a), α (Fin.rev a), h _⟩
  have hy : ∀ a, threeResActEnd hΦ (y (Fin.rev a)) = α a := fun a =>
    (threeResActEnd_acts hΦ _).unique (by simpa only [y, Fin.rev_rev] using h a)
  have key := KLR.ncEval_antihom (threeResActLinear k φ₁ φ₂ φ₃ hΦ)
    ((threeResActEnd_acts hΦ 1).unique ThreeResActs.id)
    (fun x x' => (threeResActEnd_acts hΦ (x * x')).unique
      ((threeResActEnd_acts hΦ x).comp (threeResActEnd_acts hΦ x')))
    y (MvPolynomial.rename Fin.rev P)
  have hP : MvPolynomial.rename Fin.rev (MvPolynomial.rename Fin.rev P) = P := by
    rw [MvPolynomial.rename_rename]
    have : (Fin.rev ∘ Fin.rev : Fin n → Fin n) = _root_.id := funext Fin.rev_rev
    rw [this, MvPolynomial.rename_id_apply]
  change threeResActEnd hΦ _ = KLR.ncEval (fun a => threeResActEnd hΦ (y (Fin.rev a))) _ at key
  simp only [hy, hP] at key
  rw [← key]
  have hv := KLR.ncEval_map (threeResActSub k φ₁ φ₂ φ₃ hΦ).val y (MvPolynomial.rename Fin.rev P)
  have ha := threeResActEnd_acts hΦ (KLR.ncEval y (MvPolynomial.rename Fin.rev P))
  rwa [show ((KLR.ncEval y (MvPolynomial.rename Fin.rev P) : threeResActSub k φ₁ φ₂ φ₃ hΦ) : D) =
    _ from hv] at ha

end

end Categorification.InductionAlong
