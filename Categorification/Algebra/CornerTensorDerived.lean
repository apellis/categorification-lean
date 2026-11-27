/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTensorCutLift
import Categorification.Algebra.DerivedTensorCompComparison
import Categorification.Algebra.DerivedTensorDegreeZero

set_option backward.isDefEq.respectTransparency false

/-!
# Composing derived tensor products with corner bimodules

For idempotents `e₂, e₁, e₀` of a ring `R`, when the multiplication
`e₂Re₁ ⊗_{e₁Re₁} e₁Re₀ → e₂Re₀` is bijective (`CornerTensor.mult`), the balanced tensor
product of the corner bimodules is `e₂Re₀` (`cornerTensorProductEquiv`). If moreover
`Tor^{e₁Re₁}_{>0}(e₂Re₁, e₁Re₀) = 0`, the derived tensor products on right modules compose:
`(- ⊗ᴸ e₂Re₁) ⊗ᴸ e₁Re₀ ≅ - ⊗ᴸ e₂Re₀` (`derivedRightTensorCornerCompIso`).

This is the form of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 6.12 (`𝔅_w ≅ 𝔅_{ws_i} ⊗ᴸ 𝔅_i`) for the bimodules `B_w = e_κ' T e_κ`
of red orders in one algebra: Lemma 6.5 gives the bijectivity of the multiplication.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits DG DG.DerivedCategory MulOpposite CornerEndomorphism
open scoped DG.DegreeZero

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R] {e₂ e₁ e₀ : R}
  (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁) (h₀ : IsIdempotentElem e₀)

/-- The right `e₁Re₁`-module `e₁Re₀` as a dg bimodule over `((e₀Re₀)ᵒᵖ, (e₁Re₁)ᵒᵖ)`. -/
abbrev cornerOpDZ (h : IsIdempotentElem e₁) (e₀ : R) : Type u :=
  InDegreeZero (OpBimodule h.Corner (cornerBimodule e₁ e₀))

/-- The underlying element of `R`. -/
abbrev cornerOpDZ.val {h : IsIdempotentElem e₁} (x : cornerOpDZ h e₀) : R :=
  (show cornerBimodule e₁ e₀ from x).1

/-- The product `m ⊗ n ↦ n m` from the tensor product of the corner bimodules. -/
def cornerTensorProductMul :
    TensorProductOver h₁.Cornerᵐᵒᵖ (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁) →+ cornerOpDZ h₂ e₀ :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun m : cornerOpDZ h₁ e₀ =>
      AddMonoidHom.mk' (fun n : cornerOpDZ h₂ e₁ =>
        (⟨(n : cornerBimodule e₂ e₁).1 * (m : cornerBimodule e₁ e₀).1,
          mem_cornerBimodule.mpr ⟨by rw [← mul_assoc, (n : cornerBimodule e₂ e₁).2.1],
            by rw [mul_assoc, (m : cornerBimodule e₁ e₀).2.2]⟩⟩ : cornerBimodule e₂ e₀))
        fun n n' => Subtype.ext (add_mul _ _ _))
      fun m m' => by ext n; exact Subtype.ext (mul_add _ _ _))
    fun b m n => Subtype.ext (show (n : cornerBimodule e₂ e₁).1 *
      (b.unop.1 * (m : cornerBimodule e₁ e₀).1) =
        ((n : cornerBimodule e₂ e₁).1 * b.unop.1) * (m : cornerBimodule e₁ e₀).1
      from (mul_assoc _ _ _).symm)

theorem cornerTensorProductMul_tmul (m : cornerOpDZ h₁ e₀) (n : cornerOpDZ h₂ e₁) :
    cornerOpDZ.val (cornerTensorProductMul h₂ h₁ (TensorProductOver.tmul _ m n)) =
      cornerOpDZ.val n * cornerOpDZ.val m := rfl

/-- The comparison `e₂Re₁ ⊗_k e₁Re₀ ⧸ balancing → e₂Re₁ ⊗_{e₁Re₁} e₁Re₀`. -/
def cornerTensorToTensorProduct :
    CornerTensor k R e₂ e₁ e₀ →+
      TensorProductOver h₁.Cornerᵐᵒᵖ (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁) :=
  cornerTensorCutLift (k := k) h₂ h₁ h₀
    (AddMonoidHom.mk' (fun m : cornerBimodule e₁ e₀ =>
      AddMonoidHom.mk' (fun n : cornerBimodule e₂ e₁ =>
        TensorProductOver.tmul h₁.Cornerᵐᵒᵖ (show cornerOpDZ h₁ e₀ from m)
          (show cornerOpDZ h₂ e₁ from n))
        fun n n' => TensorProductOver.tmul_add _ _ _)
      fun m m' => by ext n; exact TensorProductOver.add_tmul _ _ _)
    fun b m n => TensorProductOver.op_smul_tmul (op b) (show cornerOpDZ h₁ e₀ from m)
      (show cornerOpDZ h₂ e₁ from n)

theorem cornerTensorToTensorProduct_tmul (x : cornerBimodule e₂ e₁) (y : cornerBimodule e₁ e₀) :
    cornerTensorToTensorProduct (k := k) h₂ h₁ h₀ (CornerTensor.tmul x.val y.val) =
      TensorProductOver.tmul h₁.Cornerᵐᵒᵖ (show cornerOpDZ h₁ e₀ from y)
        (show cornerOpDZ h₂ e₁ from x) :=
  cornerTensorCutLift_tmul (k := k) h₂ h₁ h₀ _ _ x y

theorem cornerTensorProductMul_cornerTensorToTensorProduct (t : CornerTensor k R e₂ e₁ e₀) :
    cornerOpDZ.val (cornerTensorProductMul h₂ h₁ (cornerTensorToTensorProduct (k := k) h₂ h₁ h₀ t))
      = CornerTensor.mult (k := k) h₂ h₁ h₀ t := by
  induction t using CornerTensor.induction_on with
  | tmul x y =>
    rw [CornerTensor.tmul_corner, CornerTensor.mult_tmul]
    let x' := cornerSandwichAdd h₂ h₁ x
    let y' := cornerSandwichAdd h₁ h₀ y
    change cornerOpDZ.val (cornerTensorProductMul h₂ h₁ (cornerTensorToTensorProduct (k := k)
      h₂ h₁ h₀ (CornerTensor.tmul x'.val y'.val))) = _
    rw [cornerTensorToTensorProduct_tmul, cornerTensorProductMul_tmul]
    change e₂ * x * e₁ * (e₁ * y * e₀) = e₂ * (e₂ * x * e₁) * e₁ * (e₁ * y * e₀) * e₀
    simp only [← mul_assoc, h₂.eq]
    simp only [mul_assoc, h₁.eq, h₀.eq]
  | add s t hs ht => rw [map_add, map_add, map_add, ← hs, ← ht]; rfl

theorem cornerTensorToTensorProduct_surjective :
    Function.Surjective (cornerTensorToTensorProduct (k := k) h₂ h₁ h₀) := by
  intro t
  induction t using TensorProductOver.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m n =>
    exact ⟨CornerTensor.tmul (n : cornerBimodule e₂ e₁).val (m : cornerBimodule e₁ e₀).val,
      cornerTensorToTensorProduct_tmul (k := k) h₂ h₁ h₀ _ _⟩
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    exact ⟨s + t, map_add _ _ _⟩

theorem cornerOpDZ.val_injective {h : IsIdempotentElem e₁} :
    Function.Injective (cornerOpDZ.val (h := h) (e₀ := e₀)) :=
  fun _ _ hxy => Subtype.ext hxy

variable (hinj : Function.Injective (CornerTensor.mult (k := k) h₂ h₁ h₀))
  (hsurj : ∀ y, ∃ t, CornerTensor.mult (k := k) h₂ h₁ h₀ t = e₂ * y * e₀)

include hinj hsurj in
/-- **The tensor product of corner bimodules is the corner** when the multiplication is
bijective. -/
theorem cornerTensorProductMul_bijective :
    Function.Bijective (cornerTensorProductMul h₂ h₁ (e₀ := e₀)) := by
  constructor
  · intro x y hxy
    obtain ⟨s, rfl⟩ := cornerTensorToTensorProduct_surjective (k := k) h₂ h₁ h₀ x
    obtain ⟨t, rfl⟩ := cornerTensorToTensorProduct_surjective (k := k) h₂ h₁ h₀ y
    have := congrArg cornerOpDZ.val hxy
    rw [cornerTensorProductMul_cornerTensorToTensorProduct,
      cornerTensorProductMul_cornerTensorToTensorProduct] at this
    rw [hinj this]
  · intro z
    obtain ⟨t, ht⟩ := hsurj (cornerOpDZ.val z)
    refine ⟨cornerTensorToTensorProduct (k := k) h₂ h₁ h₀ t, cornerOpDZ.val_injective ?_⟩
    rw [cornerTensorProductMul_cornerTensorToTensorProduct, ht,
      (show cornerBimodule e₂ e₀ from z).2.1, (show cornerBimodule e₂ e₀ from z).2.2]

theorem cornerTensorProductMul_smul (a : h₀.Cornerᵐᵒᵖ)
    (t : TensorProductOver h₁.Cornerᵐᵒᵖ (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁)) :
    cornerTensorProductMul h₂ h₁ (a • t) = a • cornerTensorProductMul h₂ h₁ t := by
  induction t using TensorProductOver.induction_on with
  | zero =>
    have h1 := smul_zero (M := h₀.Cornerᵐᵒᵖ) (A := TensorProductOver h₁.Cornerᵐᵒᵖ
      (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁)) a
    have h2 := smul_zero (M := h₀.Cornerᵐᵒᵖ) (A := cornerOpDZ h₂ e₀) a
    rw [h1, map_zero, h2]
  | tmul m n =>
    rw [TensorProductOver.smul_tmul]
    exact cornerOpDZ.val_injective (mul_assoc _ _ _).symm
  | add x y hx hy =>
    have h1 := smul_add (M := h₀.Cornerᵐᵒᵖ) (A := TensorProductOver h₁.Cornerᵐᵒᵖ
      (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁)) a x y
    have h2 := smul_add (M := h₀.Cornerᵐᵒᵖ) (A := cornerOpDZ h₂ e₀) a
      (cornerTensorProductMul h₂ h₁ x) (cornerTensorProductMul h₂ h₁ y)
    rw [h1, map_add, map_add, hx, hy, h2]

open TensorProductOver.RightAction in
theorem cornerTensorProductMul_op_smul (b : h₂.Cornerᵐᵒᵖ)
    (t : TensorProductOver h₁.Cornerᵐᵒᵖ (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁)) :
    cornerTensorProductMul h₂ h₁ (op b • t) = op b • cornerTensorProductMul h₂ h₁ t := by
  induction t using TensorProductOver.induction_on with
  | zero =>
    have h1 := smul_zero (M := h₂.Cornerᵐᵒᵖᵐᵒᵖ) (A := TensorProductOver h₁.Cornerᵐᵒᵖ
      (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁)) (op b)
    have h2 := smul_zero (M := h₂.Cornerᵐᵒᵖᵐᵒᵖ) (A := cornerOpDZ h₂ e₀) (op b)
    rw [h1, map_zero, h2]
  | tmul m n =>
    rw [TensorProductOver.op_smul_tmul_right]
    exact cornerOpDZ.val_injective (mul_assoc _ _ _)
  | add x y hx hy =>
    have h1 := smul_add (M := h₂.Cornerᵐᵒᵖᵐᵒᵖ) (A := TensorProductOver h₁.Cornerᵐᵒᵖ
      (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁)) (op b) x y
    have h2 := smul_add (M := h₂.Cornerᵐᵒᵖᵐᵒᵖ) (A := cornerOpDZ h₂ e₀) (op b)
      (cornerTensorProductMul h₂ h₁ x) (cornerTensorProductMul h₂ h₁ y)
    rw [h1, map_add, map_add, hx, hy, h2]

include hinj hsurj in
/-- **The tensor product of corner bimodules is the corner**, as dg modules in degree zero. -/
def cornerTensorProductEquiv :
    TensorProductOver h₁.Cornerᵐᵒᵖ (cornerOpDZ h₁ e₀) (cornerOpDZ h₂ e₁) ≃ᵈᵍ[h₀.Cornerᵐᵒᵖ]
      cornerOpDZ h₂ e₀ :=
  DGModuleEquiv.ofDegreeZero
    (LinearEquiv.ofBijective
      { toFun := cornerTensorProductMul h₂ h₁
        map_add' := map_add _
        map_smul' := cornerTensorProductMul_smul h₂ h₁ h₀ }
      (cornerTensorProductMul_bijective (k := k) h₂ h₁ h₀ hinj hsurj))
    (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
    TensorProductOver.d_inDegreeZero
    (fun _ => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl)) (fun y => InDegreeZero.d_apply _ y)

variable [HasDerivedCategory.{u, u} h₂.Cornerᵐᵒᵖ] [HasDerivedCategory.{u, u} h₁.Cornerᵐᵒᵖ]
  [HasDerivedCategory.{u, u} h₀.Cornerᵐᵒᵖ]

open TensorProductOver.RightAction in
include hinj hsurj in
/-- **Derived tensor products with corner bimodules compose** when the multiplication
`e₂Re₁ ⊗_{e₁Re₁} e₁Re₀ → e₂Re₀` is bijective and `Tor^{e₁Re₁}_{>0}(e₂Re₁, e₁Re₀) = 0`:
`(- ⊗ᴸ e₂Re₁) ⊗ᴸ e₁Re₀ ≅ - ⊗ᴸ e₂Re₀` on right modules. -/
def derivedRightTensorCornerCompIso
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := h₀.Cornerᵐᵒᵖ) ℤ n).obj
      ((derivedRightTensor.{u} h₁.Corner h₀.Corner (cornerBimodule e₁ e₀)).obj
        (Q.obj (DGModuleCat.of h₁.Cornerᵐᵒᵖ (cornerOpDZ h₂ e₁)))))) :
    derivedRightTensor.{u} h₂.Corner h₁.Corner (cornerBimodule e₂ e₁) ⋙
        derivedRightTensor.{u} h₁.Corner h₀.Corner (cornerBimodule e₁ e₀) ≅
      derivedRightTensor.{u} h₂.Corner h₀.Corner (cornerBimodule e₂ e₀) :=
  derivedTensorCompIsoOfTorVanishing h₀.Cornerᵐᵒᵖ h₁.Cornerᵐᵒᵖ h₂.Cornerᵐᵒᵖ
      (OpBimodule h₁.Corner (cornerBimodule e₁ e₀))
      (OpBimodule h₂.Corner (cornerBimodule e₂ e₁)) hv ≪≫
    dgDerivedTensorIsoOfEquiv (cornerTensorProductEquiv (k := k) h₂ h₁ h₀ hinj hsurj)
      (cornerTensorProductMul_op_smul h₂ h₁ (e₀ := e₀))

end Categorification
