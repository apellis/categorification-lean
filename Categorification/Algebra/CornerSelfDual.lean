/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Self-duality of `y e C` through a symmetric corner trace

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. Let `C` be a finite-dimensional algebra over a field `k`, `e ∈ C` an idempotent
and `τ : C → k` a linear form which is symmetric on `e C e` and nondegenerate between `e C` and
`C e`: every nonzero `a ∈ e C` has some `b ∈ C e` with `τ (a b) ≠ 0`, and every nonzero
`b ∈ C e` has some `a ∈ e C` with `τ (a b) ≠ 0`. For `y ∈ e C e`, the pairing
`⟨y a, b y⟩ = τ (y a b) = τ (a b y)` identifies the right module `y C` with the dual of the left
module `C y` (`rangeMulLeftDualEquiv`). Webster's pairing `⟨π a, π b⟩ = tr(ȧ b y)` on
`𝔅_τ P^κ_i ≅ y P⁰` is this one, written with the anti-involution.

## Main results

* `rangeMulLeftDualEquiv`: `y C ≃ Hom_k(C y, k)`, with `x ↦ (b y ↦ τ (x b))`.
* `rangeMulLeftDualEquiv_mul`: it is right `C`-linear: the image of `x c` is
  `z ↦ (image of x) (c z)`.
* `selfDualEquiv`, `selfDualEquiv_mul`: for an anti-involution `s` with `s y = y`, the form
  `⟨y a, y b⟩ = τ (e a s(b) y)` identifies `y C` with its dual, and `⟨x c, x'⟩ = ⟨x, x' s(c)⟩`.
-/

noncomputable section

namespace Categorification.CornerSelfDual

variable {k C : Type*} [Field k] [Ring C] [Algebra k C]
  (e y : C) (τ : C →ₗ[k] k)

variable (k) in
/-- The right module `y C`. -/
abbrev Left : Submodule k C := LinearMap.range (LinearMap.mulLeft k y)

variable (k) in
/-- The left module `C y`. -/
abbrev Right : Submodule k C := LinearMap.range (LinearMap.mulRight k y)

/-- The pairing with `C y` of an element `a` of `C`: `z ↦ τ (e a z)`. -/
def pairLeft : C →ₗ[k] Module.Dual k (Right k y) where
  toFun a :=
    { toFun := fun z => τ (e * a * z.1)
      map_add' := fun z z' => by simp [mul_add]
      map_smul' := fun c z => by simp }
  map_add' a a' := by ext z; simp [mul_add, add_mul]
  map_smul' c a := by ext z; simp

/-- The pairing with `y C` of an element `b` of `C`: `x ↦ τ (x b e)`. -/
def pairRight : C →ₗ[k] Module.Dual k (Left k y) where
  toFun b :=
    { toFun := fun x => τ (x.1 * b * e)
      map_add' := fun x x' => by simp [add_mul]
      map_smul' := fun c x => by simp }
  map_add' b b' := by ext x; simp [mul_add, add_mul]
  map_smul' c b := by ext x; simp

variable (he : IsIdempotentElem e) (hy : e * y * e = y)
  (hsymm : ∀ a b, e * a * e = a → e * b * e = b → τ (a * b) = τ (b * a))
  (hl : ∀ a, e * a = a → a ≠ 0 → ∃ b, b * e = b ∧ τ (a * b) ≠ 0)
  (hr : ∀ b, b * e = b → b ≠ 0 → ∃ a, e * a = a ∧ τ (a * b) ≠ 0)

include he hy in
theorem y_mul_e : y * e = y := by
  rw [← hy, mul_assoc, he.eq]

include he hy in
theorem e_mul_y : e * y = y := by
  rw [← hy, ← mul_assoc, ← mul_assoc, he.eq]

include he hy hsymm in
/-- `τ (e a (b y)) = τ (y a (b e))`. -/
theorem trace_swap (a b : C) : τ (e * a * (b * y)) = τ (y * a * (b * e)) := by
  have hye := y_mul_e e y he hy
  have hey := e_mul_y e y he hy
  have hm : e * (e * a * (b * e)) * e = e * a * (b * e) := by
    simp only [← mul_assoc, he.eq]
    rw [mul_assoc _ e e, he.eq]
  have hs := hsymm _ y hm hy
  calc τ (e * a * (b * y)) = τ (e * a * (b * e) * y) := by
        conv_lhs => rw [← hey]
        simp only [mul_assoc]
    _ = τ (y * (e * a * (b * e))) := hs
    _ = τ (y * a * (b * e)) := by
        rw [show y * (e * a * (b * e)) = y * e * a * (b * e) by simp only [mul_assoc], hye]

include he hy hsymm hl in
/-- The kernel of `pairLeft` is the kernel of left multiplication by `y`. -/
theorem ker_pairLeft : LinearMap.ker (pairLeft e y τ) = LinearMap.ker (LinearMap.mulLeft k y) := by
  have hey := e_mul_y e y he hy
  ext a
  simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply]
  constructor
  · intro h
    by_contra hya
    obtain ⟨b, hb, hτ⟩ := hl (y * a) (by rw [← mul_assoc, hey]) hya
    apply hτ
    have h₁ := LinearMap.congr_fun h ⟨b * y, b, rfl⟩
    change τ (e * a * (b * y)) = 0 at h₁
    rwa [trace_swap e y τ he hy hsymm, hb] at h₁
  · intro h
    ext ⟨_, b, rfl⟩
    change τ (e * a * (b * y)) = 0
    rw [trace_swap e y τ he hy hsymm, h, zero_mul, map_zero]

include he hy hsymm hr in
/-- The kernel of `pairRight` is the kernel of right multiplication by `y`. -/
theorem ker_pairRight :
    LinearMap.ker (pairRight e y τ) = LinearMap.ker (LinearMap.mulRight k y) := by
  have hye := y_mul_e e y he hy
  ext b
  simp only [LinearMap.mem_ker, LinearMap.mulRight_apply]
  constructor
  · intro h
    by_contra hby
    obtain ⟨a, ha, hτ⟩ := hr (b * y) (by rw [mul_assoc, hye]) hby
    apply hτ
    have h₁ := LinearMap.congr_fun h ⟨y * a, a, rfl⟩
    change τ (y * a * b * e) = 0 at h₁
    rw [mul_assoc (y * a), ← trace_swap e y τ he hy hsymm, ha] at h₁
    exact h₁
  · intro h
    ext ⟨_, a, rfl⟩
    change τ (y * a * b * e) = 0
    rw [mul_assoc (y * a), ← trace_swap e y τ he hy hsymm, h, mul_zero, map_zero]

/-- The map `y C → Hom_k(C y, k)`, `y a ↦ (z ↦ τ (e a z))`. -/
def leftToDual : Left k y →ₗ[k] Module.Dual k (Right k y) :=
  (LinearMap.ker (pairLeft e y τ)).liftQ (pairLeft e y τ) le_rfl ∘ₗ
    (Submodule.quotEquivOfEq _ _ (ker_pairLeft e y τ he hy hsymm hl).symm).toLinearMap ∘ₗ
    (LinearMap.quotKerEquivRange (LinearMap.mulLeft k y)).symm.toLinearMap

/-- The map `C y → Hom_k(y C, k)`, `b y ↦ (x ↦ τ (x b e))`. -/
def rightToDual : Right k y →ₗ[k] Module.Dual k (Left k y) :=
  (LinearMap.ker (pairRight e y τ)).liftQ (pairRight e y τ) le_rfl ∘ₗ
    (Submodule.quotEquivOfEq _ _ (ker_pairRight e y τ he hy hsymm hr).symm).toLinearMap ∘ₗ
    (LinearMap.quotKerEquivRange (LinearMap.mulRight k y)).symm.toLinearMap

theorem leftToDual_apply (a : C) :
    leftToDual e y τ he hy hsymm hl ⟨y * a, a, rfl⟩ = pairLeft e y τ a := by
  simp only [leftToDual, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  have h : (LinearMap.quotKerEquivRange (LinearMap.mulLeft k y)).symm ⟨y * a, a, rfl⟩ =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [h]
  rfl

theorem leftToDual_injective : Function.Injective (leftToDual e y τ he hy hsymm hl) := by
  simp only [leftToDual, LinearMap.coe_comp, LinearEquiv.coe_coe]
  refine Function.Injective.comp ?_ (LinearEquiv.injective _ |>.comp (LinearEquiv.injective _))
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot]
  exact le_rfl

theorem rightToDual_injective : Function.Injective (rightToDual e y τ he hy hsymm hr) := by
  simp only [rightToDual, LinearMap.coe_comp, LinearEquiv.coe_coe]
  refine Function.Injective.comp ?_ (LinearEquiv.injective _ |>.comp (LinearEquiv.injective _))
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot]
  exact le_rfl

variable [FiniteDimensional k C]

/-- **Self-duality of `y e C`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14): for a
symmetric corner trace `τ`, nondegenerate between `e C` and `C e`, and `y ∈ e C e`, the
pairing `⟨y a, b y⟩ = τ (y a b)` identifies `y C` with `Hom_k(C y, k)`. -/
def rangeMulLeftDualEquiv : Left k y ≃ₗ[k] Module.Dual k (Right k y) :=
  LinearEquiv.ofBijective (leftToDual e y τ he hy hsymm hl) (by
    refine ⟨leftToDual_injective e y τ he hy hsymm hl, ?_⟩
    have h₁ := LinearMap.finrank_le_finrank_of_injective (leftToDual_injective e y τ he hy hsymm hl)
    have h₂ := LinearMap.finrank_le_finrank_of_injective
      (rightToDual_injective e y τ he hy hsymm hr)
    rw [Subspace.dual_finrank_eq] at h₁ h₂
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq]; omega)).1
      (leftToDual_injective e y τ he hy hsymm hl))

theorem rangeMulLeftDualEquiv_apply (a : C) (z : Right k y) :
    rangeMulLeftDualEquiv e y τ he hy hsymm hl hr ⟨y * a, a, rfl⟩ z = τ (e * a * z.1) := by
  change leftToDual e y τ he hy hsymm hl ⟨y * a, a, rfl⟩ z = _
  rw [leftToDual_apply]
  rfl

/-- The right action: the image of `(y a) c` is the image of `y a` composed with left
multiplication by `c` on `C y`. -/
theorem rangeMulLeftDualEquiv_mul (a c : C) (b : C) :
    rangeMulLeftDualEquiv e y τ he hy hsymm hl hr ⟨y * (a * c), a * c, rfl⟩ ⟨b * y, b, rfl⟩ =
      rangeMulLeftDualEquiv e y τ he hy hsymm hl hr ⟨y * a, a, rfl⟩
        ⟨c * (b * y), c * b, by simp [mul_assoc]⟩ := by
  rw [rangeMulLeftDualEquiv_apply, rangeMulLeftDualEquiv_apply]
  simp only [mul_assoc]

section Star

variable (s : C →ₗ[k] C) (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
  (hsy : s y = y)

omit [FiniteDimensional k C] in
include hs hsy in
theorem star_mem_right (x : Left k y) : s x.1 ∈ Right k y := by
  obtain ⟨_, a, rfl⟩ := x
  exact ⟨s a, by simp [hs, hsy]⟩

omit [FiniteDimensional k C] in
include hs hsy in
theorem star_mem_left (z : Right k y) : s z.1 ∈ Left k y := by
  obtain ⟨_, b, rfl⟩ := z
  exact ⟨s b, by simp [hs, hsy]⟩

/-- The anti-involution `s` maps `y C` onto `C y` when `s y = y`. -/
def starLeftEquiv : Left k y ≃ₗ[k] Right k y where
  toFun x := ⟨s x.1, star_mem_right y s hs hsy x⟩
  invFun z := ⟨s z.1, star_mem_left y s hs hsy z⟩
  map_add' x x' := Subtype.ext (map_add s x.1 x'.1)
  map_smul' c x := Subtype.ext (map_smul s c x.1)
  left_inv x := Subtype.ext (hss x.1)
  right_inv z := Subtype.ext (hss z.1)

/-- **Self-duality of `y C` for an anti-involution** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14): if moreover `s y = y`, the form `⟨y a, y b⟩ = τ (e a s(b) y)` identifies `y C`
with its dual. -/
def selfDualEquiv : Left k y ≃ₗ[k] Module.Dual k (Left k y) :=
  (rangeMulLeftDualEquiv e y τ he hy hsymm hl hr).trans
    (starLeftEquiv y s hs hss hsy).dualMap

theorem selfDualEquiv_apply (a b : C) :
    selfDualEquiv e y τ he hy hsymm hl hr s hs hss hsy ⟨y * a, a, rfl⟩ ⟨y * b, b, rfl⟩ =
      τ (e * a * (s b * y)) := by
  change rangeMulLeftDualEquiv e y τ he hy hsymm hl hr ⟨y * a, a, rfl⟩
    ⟨s (y * b), star_mem_right y s hs hsy ⟨y * b, b, rfl⟩⟩ = _
  rw [rangeMulLeftDualEquiv_apply]
  change τ (e * a * s (y * b)) = _
  rw [hs, hsy]

/-- The form of `selfDualEquiv` is contravariant for the right action, through `s`:
`⟨x c, x'⟩ = ⟨x, x' s(c)⟩`. -/
theorem selfDualEquiv_mul (a b c : C) :
    selfDualEquiv e y τ he hy hsymm hl hr s hs hss hsy ⟨y * (a * c), a * c, rfl⟩
        ⟨y * b, b, rfl⟩ =
      selfDualEquiv e y τ he hy hsymm hl hr s hs hss hsy ⟨y * a, a, rfl⟩
        ⟨y * (b * s c), b * s c, rfl⟩ := by
  rw [selfDualEquiv_apply, selfDualEquiv_apply, hs, hss]
  simp only [mul_assoc]

end Star

end Categorification.CornerSelfDual
