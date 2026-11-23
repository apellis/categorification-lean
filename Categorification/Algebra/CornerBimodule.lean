/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerEndomorphism

set_option backward.isDefEq.respectTransparency false

/-!
# The bimodule `e A e'` between two corner rings

For a ring `A` with idempotents `e`, `e'`, the subgroup `e A e' = {x | e x = x, x e' = x}` is a
bimodule over the corner rings `e A e` (on the left) and `e' A e'` (on the right). The right
action is a left action of the opposite ring.

## Main definitions

* `Categorification.cornerBimodule e e'`: the subgroup `e A e'`.
* its `(e A e, e' A e')`-bimodule structure.
-/

namespace Categorification

open MulOpposite CornerEndomorphism

variable {A : Type*} [Ring A] {e e' : A}

/-- The subgroup `e A e' = {x | e x = x, x e' = x}` of a ring. -/
def cornerBimodule (e e' : A) : AddSubgroup A where
  carrier := {x | e * x = x ∧ x * e' = x}
  add_mem' {x y} hx hy := ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  zero_mem' := ⟨mul_zero e, zero_mul e'⟩
  neg_mem' {x} hx := ⟨by rw [mul_neg, hx.1], by rw [neg_mul, hx.2]⟩

theorem mem_cornerBimodule {x : A} : x ∈ cornerBimodule e e' ↔ e * x = x ∧ x * e' = x :=
  Iff.rfl

namespace cornerBimodule

/-- The left action of the corner `e A e` on `e A e'`. -/
instance instModuleLeft (he : IsIdempotentElem e) : Module he.Corner (cornerBimodule e e') where
  smul b x := ⟨b.1 * x.1, by rw [← mul_assoc, corner_mul_left he], by rw [mul_assoc, x.2.2]⟩
  one_smul x := Subtype.ext x.2.1
  mul_smul b c x := Subtype.ext (mul_assoc _ _ _)
  smul_zero b := Subtype.ext (mul_zero _)
  smul_add b x y := Subtype.ext (mul_add _ _ _)
  add_smul b c x := Subtype.ext (add_mul _ _ _)
  zero_smul x := Subtype.ext (zero_mul _)

theorem coe_smul_left (he : IsIdempotentElem e) (b : he.Corner) (x : cornerBimodule e e') :
    ((b • x : cornerBimodule e e') : A) = b.1 * x.1 := rfl

/-- The right action of the corner `e' A e'` on `e A e'`. -/
instance instModuleRight (he' : IsIdempotentElem e') :
    Module he'.Cornerᵐᵒᵖ (cornerBimodule e e') where
  smul b x := ⟨x.1 * b.unop.1, by rw [← mul_assoc, x.2.1], by
    rw [mul_assoc, corner_mul_right he']⟩
  one_smul x := Subtype.ext x.2.2
  mul_smul b c x := Subtype.ext (show x.1 * (c.unop.1 * b.unop.1) = x.1 * c.unop.1 * b.unop.1
    from (mul_assoc _ _ _).symm)
  smul_zero b := Subtype.ext (zero_mul _)
  smul_add b x y := Subtype.ext (add_mul _ _ _)
  add_smul b c x := Subtype.ext (mul_add _ _ _)
  zero_smul x := Subtype.ext (mul_zero _)

theorem coe_smul_right (he' : IsIdempotentElem e') (b : he'.Cornerᵐᵒᵖ)
    (x : cornerBimodule e e') : ((b • x : cornerBimodule e e') : A) = x.1 * b.unop.1 := rfl

instance instSMulCommClass (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    SMulCommClass he.Corner he'.Cornerᵐᵒᵖ (cornerBimodule e e') where
  smul_comm _ _ _ := Subtype.ext (mul_assoc _ _ _).symm

end cornerBimodule

end Categorification
