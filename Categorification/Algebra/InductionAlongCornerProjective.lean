/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Projectivity of the corner `B φ(1)` of an induction

For a nonunital ring map `φ : A →ₙ+* B`, the corner `B φ(1)` of induction along `φ` is a
`(B, A)`-bimodule.

* `InductionAlong.projective_corner_left`: it is a projective left `B`-module, being a direct
  summand of `B`.
* `InductionAlong.cornerCongr`: ring isomorphisms `A ≃ A'`, `B ≃ B'` intertwining `φ` and `φ'`
  identify `B φ(1)` with `B' φ'(1)`, semilinearly for the right actions.
* `InductionAlong.projective_corner_of_ringEquiv`: projectivity of `B' φ'(1)` as a right
  `A'`-module transfers to `B φ(1)` as a right `A`-module.

These are used to transport Webster's Theorem 4.31 (arXiv:1309.3796v2) from the tensor product
algebras to the corners of the braided Stendhal algebras at every red order (§6.1).
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u

variable {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B)

/-- The corner `B φ(1)` is a projective left `B`-module. -/
theorem projective_corner_left : Module.Projective B (Corner φ) :=
  Module.Projective.of_split (lIdeal (φ 1)).subtype
    { toFun := fun b => ⟨b * φ 1, by
        change b * φ 1 * φ 1 = b * φ 1
        rw [mul_assoc, unit_mul_unit]⟩
      map_add' := fun a b => Subtype.ext (add_mul a b _)
      map_smul' := fun a b => Subtype.ext (mul_assoc a b _) }
    (by ext y; exact y.2)

variable {A' B' : Type u} [Ring A'] [Ring B'] {φ} {φ' : A' →ₙ+* B'}

/-- Ring isomorphisms intertwining `φ` and `φ'` identify the corners `B φ(1)` and `B' φ'(1)`,
semilinearly for the right actions. -/
def cornerCongr (α : A ≃+* A') (β : B ≃+* B') (h : ∀ a, β (φ a) = φ' (α a)) :
    Corner φ ≃ₛₗ[((RingEquiv.op α : Aᵐᵒᵖ ≃+* A'ᵐᵒᵖ) : Aᵐᵒᵖ →+* A'ᵐᵒᵖ)] Corner φ' where
  toFun z := ⟨β z.1, by
    change β z.1 * φ' 1 = β z.1
    have hz : z.1 * φ 1 = z.1 := z.2
    rw [← map_one α, ← h, ← map_mul, hz]⟩
  invFun z := ⟨β.symm z.1, by
    change β.symm z.1 * φ 1 = β.symm z.1
    have hz : z.1 * φ' 1 = z.1 := z.2
    apply β.injective
    have h1 : φ' (α 1) = φ' 1 := by rw [map_one]
    rw [map_mul, β.apply_symm_apply, h, h1, hz]⟩
  map_add' a b := Subtype.ext (map_add β a.1 b.1)
  map_smul' r z := Subtype.ext (by
    change β (z.1 * φ r.unop) = β z.1 * φ' (α r.unop)
    rw [map_mul, h])
  left_inv z := Subtype.ext (β.symm_apply_apply z.1)
  right_inv z := Subtype.ext (β.apply_symm_apply z.1)

@[simp] theorem cornerCongr_apply_val (α : A ≃+* A') (β : B ≃+* B')
    (h : ∀ a, β (φ a) = φ' (α a)) (z : Corner φ) : (cornerCongr α β h z).1 = β z.1 := rfl

/-- Projectivity of the right `A'`-module `B' φ'(1)` transfers along ring isomorphisms
intertwining `φ` and `φ'`. -/
theorem projective_corner_of_ringEquiv (α : A ≃+* A') (β : B ≃+* B')
    (h : ∀ a, β (φ a) = φ' (α a)) [Module.Projective A'ᵐᵒᵖ (Corner φ')] :
    Module.Projective Aᵐᵒᵖ (Corner φ) :=
  Module.Projective.of_equiv (cornerCongr α β h).symm

end InductionAlong

end

end Categorification
