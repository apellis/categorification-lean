/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotBlock

/-!
# Direct sums of Cartan data and root data

The Cartan datum on `I₁ ⊕ I₂` whose form is the orthogonal sum of the two forms
(`CartanDatum.sum`), and the root datum on `X₁ × X₂`, `Y₁ × Y₂` with the sum pairing
(`RootDatum.prod`). Colours of different summands have `i · j = 0`.

This is the Kac–Moody datum of the product of a lowest-weight and a highest-weight
representation in the test representations of B. Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3 (proof of Theorem `nondegenerate`); there the two sets of labels
`Ĩ_-` and `Ĩ_+` are orthogonal.
-/

namespace Categorification.QuantumGroup

namespace CartanDatum

variable {I₁ I₂ : Type*}

/-- The orthogonal sum of two Cartan data. -/
def sum (C₁ : CartanDatum I₁) (C₂ : CartanDatum I₂) : CartanDatum (I₁ ⊕ I₂) where
  dot
    | .inl i, .inl j => C₁.dot i j
    | .inr i, .inr j => C₂.dot i j
    | _, _ => 0
  symm
    | .inl i, .inl j => C₁.symm i j
    | .inr i, .inr j => C₂.symm i j
    | .inl _, .inr _ => rfl
    | .inr _, .inl _ => rfl
  dot_self_pos
    | .inl i => C₁.dot_self_pos i
    | .inr i => C₂.dot_self_pos i
  dot_self_even
    | .inl i => C₁.dot_self_even i
    | .inr i => C₂.dot_self_even i
  dot_nonpos
    | .inl i, .inl j, h => C₁.dot_nonpos i j fun e => h (congrArg _ e)
    | .inr i, .inr j, h => C₂.dot_nonpos i j fun e => h (congrArg _ e)
    | .inl _, .inr _, _ => le_rfl
    | .inr _, .inl _, _ => le_rfl
  dvd_two_mul
    | .inl i, .inl j => C₁.dvd_two_mul i j
    | .inr i, .inr j => C₂.dvd_two_mul i j
    | .inl _, .inr _ => dvd_mul_of_dvd_right (dvd_zero _) _
    | .inr _, .inl _ => dvd_mul_of_dvd_right (dvd_zero _) _

variable (C₁ : CartanDatum I₁) (C₂ : CartanDatum I₂)

@[simp] theorem sum_dot_inl_inl (i j : I₁) : (C₁.sum C₂).dot (.inl i) (.inl j) = C₁.dot i j :=
  rfl

@[simp] theorem sum_dot_inr_inr (i j : I₂) : (C₁.sum C₂).dot (.inr i) (.inr j) = C₂.dot i j :=
  rfl

@[simp] theorem sum_dot_inl_inr (i : I₁) (j : I₂) : (C₁.sum C₂).dot (.inl i) (.inr j) = 0 :=
  rfl

@[simp] theorem sum_dot_inr_inl (i : I₂) (j : I₁) : (C₁.sum C₂).dot (.inr i) (.inl j) = 0 :=
  rfl

end CartanDatum

namespace UDot

namespace RootDatum

variable {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type*} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂] [AddCommGroup Y₂]

/-- The sum pairing `⟨(y₁, y₂), (x₁, x₂)⟩ = ⟨y₁, x₁⟩ + ⟨y₂, x₂⟩`. -/
def prodPair (p₁ : Y₁ →+ X₁ →+ ℤ) (p₂ : Y₂ →+ X₂ →+ ℤ) : Y₁ × Y₂ →+ X₁ × X₂ →+ ℤ where
  toFun y := (p₁ y.1).comp (AddMonoidHom.fst X₁ X₂) + (p₂ y.2).comp (AddMonoidHom.snd X₁ X₂)
  map_zero' := by ext x; simp
  map_add' y y' := by
    ext x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, Prod.fst_add, Prod.snd_add, map_add]
    abel

@[simp] theorem prodPair_apply (p₁ : Y₁ →+ X₁ →+ ℤ) (p₂ : Y₂ →+ X₂ →+ ℤ) (y : Y₁ × Y₂)
    (x : X₁ × X₂) : prodPair p₁ p₂ y x = p₁ y.1 x.1 + p₂ y.2 x.2 := rfl

/-- A sum of perfect pairings is perfect. -/
theorem prodPair_bijective {p₁ : Y₁ →+ X₁ →+ ℤ} {p₂ : Y₂ →+ X₂ →+ ℤ}
    (h₁ : Function.Bijective p₁) (h₂ : Function.Bijective p₂) :
    Function.Bijective (prodPair p₁ p₂) := by
  refine ⟨fun y y' hy => ?_, fun φ => ?_⟩
  · have e₁ : p₁ y.1 = p₁ y'.1 := by
      ext x
      simpa using DFunLike.congr_fun hy (x, 0)
    have e₂ : p₂ y.2 = p₂ y'.2 := by
      ext x
      simpa using DFunLike.congr_fun hy (0, x)
    exact Prod.ext (h₁.1 e₁) (h₂.1 e₂)
  · obtain ⟨y₁, hy₁⟩ := h₁.2 (φ.comp (AddMonoidHom.inl X₁ X₂))
    obtain ⟨y₂, hy₂⟩ := h₂.2 (φ.comp (AddMonoidHom.inr X₁ X₂))
    refine ⟨(y₁, y₂), ?_⟩
    ext x
    rw [prodPair_apply, hy₁, hy₂, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      ← map_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero,
      zero_add]

theorem prodPair_flip (p₁ : Y₁ →+ X₁ →+ ℤ) (p₂ : Y₂ →+ X₂ →+ ℤ) :
    (prodPair p₁ p₂).flip = prodPair p₁.flip p₂.flip := by
  ext x y
  simp

/-- **The product root datum** on `X₁ × X₂`, `Y₁ × Y₂`, for the orthogonal sum of the Cartan
data, with `(i₁)_X = (i_X, 0)` and `(i₂)_X = (0, i_X)`. -/
def prod (RD₁ : RootDatum C₁ X₁ Y₁) (RD₂ : RootDatum C₂ X₂ Y₂) :
    RootDatum (C₁.sum C₂) (X₁ × X₂) (Y₁ × Y₂) where
  pair := prodPair RD₁.pair RD₂.pair
  perfect_left := prodPair_bijective RD₁.perfect_left RD₂.perfect_left
  perfect_right := by
    rw [prodPair_flip]
    exact prodPair_bijective RD₁.perfect_right RD₂.perfect_right
  free_X := by
    have := RD₁.free_X
    have := RD₂.free_X
    infer_instance
  finite_X := by
    have := RD₁.finite_X
    have := RD₂.finite_X
    infer_instance
  free_Y := by
    have := RD₁.free_Y
    have := RD₂.free_Y
    infer_instance
  finite_Y := by
    have := RD₁.finite_Y
    have := RD₂.finite_Y
    infer_instance
  iX := Sum.elim (fun i => (RD₁.iX i, 0)) (fun i => (0, RD₂.iX i))
  iY := Sum.elim (fun i => (RD₁.iY i, 0)) (fun i => (0, RD₂.iY i))
  pair_iY_iX
    | .inl i, .inl j => by simp [RD₁.pair_iY_iX]
    | .inr i, .inr j => by simp [RD₂.pair_iY_iX]
    | .inl _, .inr _ => by simp
    | .inr _, .inl _ => by simp

variable (RD₁ : RootDatum C₁ X₁ Y₁) (RD₂ : RootDatum C₂ X₂ Y₂)

@[simp] theorem prod_iX_inl (i : I₁) : (RD₁.prod RD₂).iX (.inl i) = (RD₁.iX i, 0) := rfl

@[simp] theorem prod_iX_inr (i : I₂) : (RD₁.prod RD₂).iX (.inr i) = (0, RD₂.iX i) := rfl

@[simp] theorem prod_iY_inl (i : I₁) : (RD₁.prod RD₂).iY (.inl i) = (RD₁.iY i, 0) := rfl

@[simp] theorem prod_iY_inr (i : I₂) : (RD₁.prod RD₂).iY (.inr i) = (0, RD₂.iY i) := rfl

@[simp] theorem prod_pair (y : Y₁ × Y₂) (x : X₁ × X₂) :
    (RD₁.prod RD₂).pair y x = RD₁.pair y.1 x.1 + RD₂.pair y.2 x.2 := rfl

end RootDatum

end UDot

end Categorification.QuantumGroup
