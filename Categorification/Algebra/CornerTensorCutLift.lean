/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTensorAdditive
import Categorification.Algebra.CornerBimodule

/-!
# Lifting an additive product of rectangular corners

A balanced family acting on the two rectangular coefficients gives an
additive map from their ordinary corner tensor. The ground-scalar
relation follows from balancing against the scalar in the middle corner.
-/

noncomputable section

namespace Categorification

open CornerEndomorphism

variable {A : Type*} [Ring A] {e f g : A}
  (he : IsIdempotentElem e) (hf : IsIdempotentElem f)

/-- Sandwich an ambient element to get a rectangular coefficient. -/
def cornerSandwichAdd : A →+ cornerBimodule e f where
  toFun x := ⟨e * x * f, mem_cornerBimodule.mpr
    ⟨by simp only [← mul_assoc, he.eq], by rw [mul_assoc _ f f, hf.eq]⟩⟩
  map_zero' := Subtype.ext (show e * 0 * f = 0 by rw [mul_zero, zero_mul])
  map_add' x y := Subtype.ext (show e * (x + y) * f = e * x * f + e * y * f by
    simp only [mul_add, add_mul])

theorem cornerSandwichAdd_of_corner (x : cornerBimodule e f) :
    cornerSandwichAdd he hf x.val = x := by
  apply Subtype.ext
  change e * x.val * f = x.val
  rw [(mem_cornerBimodule.mp x.property).1, (mem_cornerBimodule.mp x.property).2]

theorem coe_cornerSandwichAdd_mul_right (b : hf.Corner) (x : A) :
    (cornerSandwichAdd he hf (x * b.val)).val = (cornerSandwichAdd he hf x).val * b.val := by
  change e * (x * b.val) * f = (e * x * f) * b.val
  rw [← mul_assoc e, mul_assoc (e*x) b.val f, corner_mul_right hf,
    mul_assoc (e*x) f b.val, corner_mul_left hf]

theorem coe_cornerSandwichAdd_mul_left (b : he.Corner) (x : A) :
    (cornerSandwichAdd he hf (b.val * x)).val = b.val * (cornerSandwichAdd he hf x).val := by
  change e * (b.val * x) * f = b.val * (e * x * f)
  calc e * (b.val * x) * f = b.val * x * f := by rw [← mul_assoc e, corner_mul_left he]
    _ = b.val * e * x * f := by rw [corner_mul_right he]
    _ = b.val * (e * x * f) := by simp only [mul_assoc]

section CornerLift

open MulOpposite

variable {k P : Type*} [CommRing k] [Algebra k A] [AddCommGroup P]
  {e₂ e₁ e₀ : A} (h₂ : IsIdempotentElem e₂) (h₁ : IsIdempotentElem e₁)
  (h₀ : IsIdempotentElem e₀)
  (F : cornerBimodule e₁ e₀ →+ cornerBimodule e₂ e₁ →+ P)
  (hF : ∀ (b : h₁.Corner) (m : cornerBimodule e₁ e₀) (n : cornerBimodule e₂ e₁),
    F (b • m) n = F m (op b • n))

local notation "cut₁" => cornerSandwichAdd h₁ h₀
local notation "cut₂" => cornerSandwichAdd h₂ h₁
local notation "F₀" => AddMonoidHom.comp (AddMonoidHom.compl₂ (AddMonoidHom.flip F) cut₁) cut₂

private def middleScalar (r : k) : h₁.Corner :=
  ⟨r • e₁, ⟨r • (1 : A), by
    change e₁ * (r • (1 : A)) * e₁ = r • e₁
    rw [mul_smul_comm, mul_one, smul_mul_assoc, h₁.eq]⟩⟩

include hF in
private theorem cut_scalar (r : k) (x y : A) :
    F₀ (r • x) y = F₀ x (r • y) := by
  let b := middleScalar h₁ r
  have hx : cut₂ (r • x) = op b • cut₂ x := by
    apply Subtype.ext
    change e₂ * (r • x) * e₁ = (e₂ * x * e₁) * (r • e₁)
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc, h₁.eq]
  have hy : cut₁ (r • y) = b • cut₁ y := by
    apply Subtype.ext
    change e₁ * (r • y) * e₀ = (r • e₁) * (e₁ * y * e₀)
    simp only [mul_smul_comm, smul_mul_assoc, ← mul_assoc, h₁.eq]
  change F (cut₁ y) (cut₂ (r • x)) = F (cut₁ (r • y)) (cut₂ x)
  rw [hx, hy]
  exact (hF b _ _).symm

include hF in
private theorem cut_balance (x c y : A) :
    F₀ (x * (e₁ * c * e₁)) y = F₀ x ((e₁ * c * e₁) * y) := by
  let b : h₁.Corner := ⟨e₁ * c * e₁, ⟨c, rfl⟩⟩
  have hx : cut₂ (x * b.val) = op b • cut₂ x :=
    Subtype.ext (coe_cornerSandwichAdd_mul_right h₂ h₁ b x)
  have hy : cut₁ (b.val * y) = b • cut₁ y :=
    Subtype.ext (coe_cornerSandwichAdd_mul_left h₁ h₀ b y)
  change F (cut₁ y) (cut₂ (x * b.val)) = F (cut₁ (b.val * y)) (cut₂ x)
  rw [hx, hy]
  exact (hF b _ _).symm

/-- Descend a balanced additive family of rectangular coefficients to the field corner tensor. -/
def cornerTensorCutLift : CornerTensor k A e₂ e₁ e₀ →+ P :=
  CornerTensor.liftAdd e₂ e₁ e₀ F₀ (cut_scalar h₂ h₁ h₀ F hF)
    (fun x y => by
      change F (cut₁ y) (cut₂ x) = F (cut₁ (e₁ * y * e₀)) (cut₂ (e₂ * x * e₁))
      have hx := cornerSandwichAdd_of_corner h₂ h₁ (cut₂ x)
      have hy := cornerSandwichAdd_of_corner h₁ h₀ (cut₁ y)
      exact congrArg₂ (fun a b => F a b) hy.symm hx.symm)
    (cut_balance h₂ h₁ h₀ F hF)

theorem cornerTensorCutLift_tmul (x : cornerBimodule e₂ e₁) (y : cornerBimodule e₁ e₀) :
    cornerTensorCutLift (k := k) h₂ h₁ h₀ F hF (CornerTensor.tmul x.val y.val) = F y x := by
  rw [cornerTensorCutLift, CornerTensor.liftAdd_tmul]
  change F (cut₁ y.val) (cut₂ x.val) = F y x
  rw [cornerSandwichAdd_of_corner, cornerSandwichAdd_of_corner]

end CornerLift

end Categorification
