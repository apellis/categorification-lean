/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.NoncommRing

/-!
# Equivalent idempotents

Background for M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum
groups I*, arXiv:0803.4121v2, §2.5, Proposition 2.13 and Corollary 2.14.

Two idempotents `f, f'` of a ring `A` are *equivalent* if `f = a b` and `f' = b a` for some
`a, b` with `a b a = a` and `b a b = b` (then `a ∈ f A f'` and `b ∈ f' A f`). Equivalent
idempotents give isomorphic projective modules:

* right ideals `f A ≅ f' A` (right `A`-modules, i.e. `Aᵐᵒᵖ`-modules), `y ↦ b y`;
* left ideals `A f ≅ A f'` (left `A`-modules), `y ↦ y a`;
* for every left `A`-module `M`, `f M ≅ f' M` (as `k`-modules if `A` is a `k`-algebra),
  `m ↦ b m`.

An orthogonal decomposition `e = f₁ + f₂` (`f₁, f₂` idempotents with `f₁ f₂ = f₂ f₁ = 0`)
gives `e A ≅ f₁ A ⊕ f₂ A`, `A e ≅ A f₁ ⊕ A f₂` and `e M ≅ f₁ M ⊕ f₂ M`.

These are the forms in which KL I, Proposition 2.13 (isomorphisms of projective modules
`₍…iji…₎P ≅ ₍…i⁽²⁾j…₎P ⊕ ₍…ji⁽²⁾…₎P`) and Corollary 2.14 (isomorphisms `1_{…iji…} M ≅
1_{…i⁽²⁾j…} M ⊕ 1_{…ji⁽²⁾…} M`) are stated in `Categorification.KLR.Prop213`
(gradings are recorded separately there).

## Main definitions

* `IsEquivPair a b f f'` : `a b = f`, `b a = f'`, `a b a = a`, `b a b = b`.
* `IdemEquiv f f'` : `∃ a b, IsEquivPair a b f f'`.
* `IsOrthDecomp e f₁ f₂` : `e = f₁ + f₂` with `f₁, f₂` orthogonal idempotents.
* `fixSub f M`, `lIdeal f`, `rIdeal f` : the submodules `f M`, `A f`, `f A`.
-/

namespace Categorification

variable {A : Type*} [Ring A]

/-- `(a, b)` exhibits `f = a b` and `f' = b a` as equivalent idempotents. -/
def IsEquivPair (a b f f' : A) : Prop :=
  a * b = f ∧ b * a = f' ∧ a * b * a = a ∧ b * a * b = b

/-- Equivalence of idempotents: `f = a b` and `f' = b a` with `a b a = a`, `b a b = b`. -/
def IdemEquiv (f f' : A) : Prop := ∃ a b : A, IsEquivPair a b f f'

/-- An orthogonal decomposition `e = f₁ + f₂` into idempotents with `f₁ f₂ = f₂ f₁ = 0`. -/
def IsOrthDecomp (e f₁ f₂ : A) : Prop :=
  IsIdempotentElem f₁ ∧ IsIdempotentElem f₂ ∧ f₁ * f₂ = 0 ∧ f₂ * f₁ = 0 ∧ f₁ + f₂ = e

namespace IsEquivPair

variable {a b f f' : A}

theorem mk' (h₁ : a * b = f) (h₂ : b * a = f') (h₃ : a * b * a = a) (h₄ : b * a * b = b) :
    IsEquivPair a b f f' := ⟨h₁, h₂, h₃, h₄⟩

/-- A pair with `a b = f`, `b a = f'`, `f a = a` and `b f = b` (e.g. `a ∈ f A`, `b ∈ A f`). -/
theorem of_mul_left (h₁ : a * b = f) (h₂ : b * a = f') (h₃ : f * a = a) (h₄ : b * f = b) :
    IsEquivPair a b f f' := ⟨h₁, h₂, by rw [h₁, h₃], by rw [mul_assoc, h₁, h₄]⟩

theorem idem_left (h : IsEquivPair a b f f') : IsIdempotentElem f := by
  obtain ⟨h₁, -, h₃, -⟩ := h
  rw [IsIdempotentElem, ← h₁, ← mul_assoc, h₃]

theorem idem_right (h : IsEquivPair a b f f') : IsIdempotentElem f' := by
  obtain ⟨-, h₂, -, h₄⟩ := h
  rw [IsIdempotentElem, ← h₂, ← mul_assoc, h₄]

theorem symm (h : IsEquivPair a b f f') : IsEquivPair b a f' f :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem left_mul (h : IsEquivPair a b f f') : f * a = a := by rw [← h.1, h.2.2.1]
theorem mul_right (h : IsEquivPair a b f f') : a * f' = a := by
  rw [← h.2.1, ← mul_assoc, h.2.2.1]
theorem left_mul' (h : IsEquivPair a b f f') : f' * b = b := h.symm.left_mul
theorem mul_right' (h : IsEquivPair a b f f') : b * f = b := h.symm.mul_right

theorem trans {c d f'' : A} (h : IsEquivPair a b f f') (h' : IsEquivPair c d f' f'') :
    IsEquivPair (a * c) (d * b) f f'' := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨h₁', h₂', h₃', h₄'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show a * c * (d * b) = a * (c * d) * b by noncomm_ring, h₁', ← h₂,
      show a * (b * a) * b = a * b * a * b by noncomm_ring, h₃, h₁]
  · rw [show d * b * (a * c) = d * (b * a) * c by noncomm_ring, h₂, ← h₁',
      show d * (c * d) * c = d * c * d * c by noncomm_ring, ← h₂', h₄']
  · rw [show a * c * (d * b) * (a * c) = a * (c * d) * (b * a) * c by noncomm_ring, h₁', h₂,
      ← h₂, show a * (b * a) * (b * a) * c = (a * b * a) * b * a * c by noncomm_ring, h₃, h₃]
  · rw [show d * b * (a * c) * (d * b) = d * (b * a) * (c * d) * b by noncomm_ring, h₂, ← h₁',
      show d * (c * d) * (c * d) * b = (d * c * d) * c * d * b by noncomm_ring, h₄', h₄']

/-- Left multiplication by an idempotent `F` commuting with `a` and `b`: the pair
`(F a, F b)` exhibits `F f ~ F f'`. -/
theorem mul_of_commute {F : A} (h : IsEquivPair a b f f') (hF : IsIdempotentElem F)
    (ha : Commute F a) (hb : Commute F b) : IsEquivPair (F * a) (F * b) (F * f) (F * f') := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h₁, mul_assoc, ← mul_assoc a, ← ha.eq, mul_assoc, ← mul_assoc, hF.eq]
  · rw [← h₂, mul_assoc, ← mul_assoc b, ← hb.eq, mul_assoc, ← mul_assoc, hF.eq]
  · rw [show F * a * (F * b) * (F * a) = F * (a * F) * b * F * a by noncomm_ring, ← ha.eq,
      show F * (F * a) * b * F * a = (F * F) * a * (b * F) * a by noncomm_ring, ← hb.eq, hF.eq,
      show F * a * (F * b) * a = F * (a * F) * (b * a) by noncomm_ring, ← ha.eq,
      show F * (F * a) * (b * a) = (F * F) * (a * b * a) by noncomm_ring, hF.eq, h₃]
  · rw [show F * b * (F * a) * (F * b) = F * (b * F) * a * F * b by noncomm_ring, ← hb.eq,
      show F * (F * b) * a * F * b = (F * F) * b * (a * F) * b by noncomm_ring, ← ha.eq, hF.eq,
      show F * b * (F * a) * b = F * (b * F) * (a * b) by noncomm_ring, ← hb.eq,
      show F * (F * b) * (a * b) = (F * F) * (b * a * b) by noncomm_ring, hF.eq, h₄]

/-- Left multiplication by an element `F` commuting with `a` and `b` with `F² f = F f` and
`F² f' = F f'` (e.g. `F` commuting with the idempotents `F f`, `F f'`): the pair
`(F a, F b)` exhibits `F f ~ F f'`. -/
theorem mul_of_commute' {F : A} (h : IsEquivPair a b f f') (hf : F * F * f = F * f)
    (hf' : F * F * f' = F * f') (ha : Commute F a) (hb : Commute F b) :
    IsEquivPair (F * a) (F * b) (F * f) (F * f') := by
  have hab : F * a * (F * b) = F * f := by
    rw [mul_assoc, ← mul_assoc a, ← ha.eq, mul_assoc, ← mul_assoc F, h.1, hf]
  have hba : F * b * (F * a) = F * f' := by
    rw [mul_assoc, ← mul_assoc b, ← hb.eq, mul_assoc, ← mul_assoc F, h.2.1, hf']
  have hFf : Commute F f := h.1 ▸ ha.mul_right hb
  have hFf' : Commute F f' := h.2.1 ▸ hb.mul_right ha
  refine ⟨hab, hba, ?_, ?_⟩
  · rw [hab, mul_assoc, ← mul_assoc f, ← hFf.eq, mul_assoc, ← mul_assoc F, ← mul_assoc, hf,
      mul_assoc, h.left_mul]
  · rw [hba, mul_assoc, ← mul_assoc f', ← hFf'.eq, mul_assoc, ← mul_assoc F, ← mul_assoc, hf',
      mul_assoc, h.left_mul']

/-- Images under a ring homomorphism. -/
theorem map {B : Type*} [Ring B] {F : Type*} [FunLike F A B] [MulHomClass F A B] (φ : F)
    (h : IsEquivPair a b f f') : IsEquivPair (φ a) (φ b) (φ f) (φ f') := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨by rw [← map_mul, h₁], by rw [← map_mul, h₂], by rw [← map_mul, ← map_mul, h₃],
    by rw [← map_mul, ← map_mul, h₄]⟩

/-- Images under an anti-homomorphism `φ (x y) = φ y φ x` (such as the antiinvolution `ψ` of
KL I): the pair `(φ b, φ a)` exhibits `φ f ~ φ f'`. -/
theorem map_anti {B : Type*} [Ring B] (φ : A → B) (hφ : ∀ x y, φ (x * y) = φ y * φ x)
    (h : IsEquivPair a b f f') : IsEquivPair (φ b) (φ a) (φ f) (φ f') := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨by rw [← hφ, h₁], by rw [← hφ, h₂], by rw [← hφ, ← hφ, ← mul_assoc, h₄],
    by rw [← hφ, ← hφ, ← mul_assoc, h₃]⟩

end IsEquivPair

namespace IdemEquiv

variable {f f' f'' : A}

theorem idem_left (h : IdemEquiv f f') : IsIdempotentElem f :=
  let ⟨_, _, h⟩ := h; h.idem_left

theorem idem_right (h : IdemEquiv f f') : IsIdempotentElem f' :=
  let ⟨_, _, h⟩ := h; h.idem_right

theorem refl (hf : IsIdempotentElem f) : IdemEquiv f f :=
  ⟨f, f, hf.eq, hf.eq, by rw [hf.eq, hf.eq], by rw [hf.eq, hf.eq]⟩

theorem symm (h : IdemEquiv f f') : IdemEquiv f' f :=
  let ⟨a, b, h⟩ := h; ⟨b, a, h.symm⟩

theorem trans (h : IdemEquiv f f') (h' : IdemEquiv f' f'') : IdemEquiv f f'' :=
  let ⟨_, _, h⟩ := h; let ⟨_, _, h'⟩ := h'; ⟨_, _, h.trans h'⟩

theorem map_anti {B : Type*} [Ring B] (φ : A → B) (hφ : ∀ x y, φ (x * y) = φ y * φ x)
    (h : IdemEquiv f f') : IdemEquiv (φ f) (φ f') :=
  let ⟨_, _, h⟩ := h; ⟨_, _, h.map_anti φ hφ⟩

end IdemEquiv

namespace IsOrthDecomp

variable {e f₁ f₂ : A}

theorem idem (h : IsOrthDecomp e f₁ f₂) : IsIdempotentElem e := by
  obtain ⟨h₁, h₂, h₁₂, h₂₁, rfl⟩ := h
  rw [IsIdempotentElem, add_mul, mul_add, mul_add, h₁.eq, h₂.eq, h₁₂, h₂₁, zero_add, add_zero]

theorem mul_left₁ (h : IsOrthDecomp e f₁ f₂) : e * f₁ = f₁ := by
  obtain ⟨h₁, -, -, h₂₁, rfl⟩ := h; rw [add_mul, h₁.eq, h₂₁, add_zero]
theorem mul_left₂ (h : IsOrthDecomp e f₁ f₂) : e * f₂ = f₂ := by
  obtain ⟨-, h₂, h₁₂, -, rfl⟩ := h; rw [add_mul, h₂.eq, h₁₂, zero_add]
theorem mul_right₁ (h : IsOrthDecomp e f₁ f₂) : f₁ * e = f₁ := by
  obtain ⟨h₁, -, h₁₂, -, rfl⟩ := h; rw [mul_add, h₁.eq, h₁₂, add_zero]
theorem mul_right₂ (h : IsOrthDecomp e f₁ f₂) : f₂ * e = f₂ := by
  obtain ⟨-, h₂, -, h₂₁, rfl⟩ := h; rw [mul_add, h₂.eq, h₂₁, zero_add]

/-- Left multiplication by an idempotent `F` commuting with `f₁` and `f₂`. -/
theorem mul_of_commute {F : A} (h : IsOrthDecomp e f₁ f₂) (hF : IsIdempotentElem F)
    (h₁ : Commute F f₁) (h₂ : Commute F f₂) : IsOrthDecomp (F * e) (F * f₁) (F * f₂) := by
  obtain ⟨i₁, i₂, h₁₂, h₂₁, rfl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, (mul_add _ _ _).symm⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc f₁, ← h₁.eq, mul_assoc, ← mul_assoc F, hF.eq,
      i₁.eq]
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc f₂, ← h₂.eq, mul_assoc, ← mul_assoc F, hF.eq,
      i₂.eq]
  · rw [mul_assoc, ← mul_assoc f₁, ← h₁.eq, mul_assoc, h₁₂, mul_zero, mul_zero]
  · rw [mul_assoc, ← mul_assoc f₂, ← h₂.eq, mul_assoc, h₂₁, mul_zero, mul_zero]

/-- Left multiplication by an element `F` commuting with `f₁, f₂` with `F² fᵢ = F fᵢ`. -/
theorem mul_of_commute' {F : A} (h : IsOrthDecomp e f₁ f₂) (hF₁ : F * F * f₁ = F * f₁)
    (hF₂ : F * F * f₂ = F * f₂) (h₁ : Commute F f₁) (h₂ : Commute F f₂) :
    IsOrthDecomp (F * e) (F * f₁) (F * f₂) := by
  obtain ⟨i₁, i₂, h₁₂, h₂₁, rfl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, (mul_add _ _ _).symm⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc f₁, ← h₁.eq, mul_assoc, i₁.eq, ← mul_assoc,
      hF₁]
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc f₂, ← h₂.eq, mul_assoc, i₂.eq, ← mul_assoc,
      hF₂]
  · rw [mul_assoc, ← mul_assoc f₁, ← h₁.eq, mul_assoc, h₁₂, mul_zero, mul_zero]
  · rw [mul_assoc, ← mul_assoc f₂, ← h₂.eq, mul_assoc, h₂₁, mul_zero, mul_zero]

/-- A decomposition `e = f₁ + f₂` with `f₁, f₂` idempotents, `f₁ e = f₁` and `f₂ e = f₂` is
orthogonal. -/
theorem of_add {e f₁ f₂ : A} (h₁ : IsIdempotentElem f₁) (h₂ : IsIdempotentElem f₂)
    (he : f₁ + f₂ = e) (h₁e : f₁ * e = f₁) (h₂e : f₂ * e = f₂) : IsOrthDecomp e f₁ f₂ := by
  refine ⟨h₁, h₂, ?_, ?_, he⟩
  · have := h₁e; rw [← he, mul_add, h₁.eq] at this
    exact (add_eq_left.1 this)
  · have := h₂e; rw [← he, mul_add, h₂.eq] at this
    exact (add_eq_right.1 this)

theorem map_anti {B : Type*} [Ring B] (φ : A →+ B) (hφ : ∀ x y, φ (x * y) = φ y * φ x)
    (h : IsOrthDecomp e f₁ f₂) : IsOrthDecomp (φ e) (φ f₁) (φ f₂) := by
  obtain ⟨i₁, i₂, h₁₂, h₂₁, rfl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, (map_add _ _ _).symm⟩
  · rw [IsIdempotentElem, ← hφ, i₁.eq]
  · rw [IsIdempotentElem, ← hφ, i₂.eq]
  · rw [← hφ, h₂₁, map_zero]
  · rw [← hφ, h₁₂, map_zero]

end IsOrthDecomp

/-! ### Modules -/

section modules

variable (k : Type*) [CommRing k] [Algebra k A] (M : Type*) [AddCommGroup M] [Module A M]
  [Module k M] [IsScalarTower k A M]

/-- The subspace `f M = {m | f m = m}` of a left `A`-module (for `f` idempotent it is the image
of `f`). -/
def fixSub (f : A) : Submodule k M where
  carrier := {m | f • m = m}
  add_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, smul_add] at *; rw [hx, hy]
  zero_mem' := smul_zero f
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_comm, hx]

variable {k M}

theorem mem_fixSub {f : A} {m : M} : m ∈ fixSub k M f ↔ f • m = m := Iff.rfl

theorem smul_mem_fixSub {f : A} (hf : IsIdempotentElem f) (m : M) : f • m ∈ fixSub k M f := by
  rw [mem_fixSub, smul_smul, hf.eq]

/-- **Equivalent idempotents give isomorphic subspaces** `f M ≅ f' M`, `m ↦ b m`
(KL I, Corollary 2.14, ungraded). -/
def IsEquivPair.fixSubEquiv {a b f f' : A} (h : IsEquivPair a b f f') :
    fixSub k M f ≃ₗ[k] fixSub k M f' where
  toFun m := ⟨b • (m : M), by rw [mem_fixSub, smul_smul, ← h.2.1, h.2.2.2]⟩
  invFun m := ⟨a • (m : M), by rw [mem_fixSub, smul_smul, ← h.1, h.2.2.1]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext (smul_comm b c (x : M))
  left_inv m := Subtype.ext (by
    change a • b • (m : M) = m
    rw [smul_smul, h.1]; exact m.2)
  right_inv m := Subtype.ext (by
    change b • a • (m : M) = m
    rw [smul_smul, h.2.1]; exact m.2)

theorem IsEquivPair.fixSubEquiv_apply {a b f f' : A} (h : IsEquivPair a b f f')
    (m : fixSub k M f) : (h.fixSubEquiv m : M) = b • (m : M) := rfl

theorem IdemEquiv.nonempty_fixSubEquiv {f f' : A} (h : IdemEquiv f f') :
    Nonempty (fixSub k M f ≃ₗ[k] fixSub k M f') :=
  let ⟨_, _, h⟩ := h; ⟨h.fixSubEquiv⟩

/-- **An orthogonal decomposition `e = f₁ + f₂` splits `e M = f₁ M ⊕ f₂ M`**
(KL I, Corollary 2.14, ungraded), `m ↦ (f₁ m, f₂ m)`. -/
def IsOrthDecomp.fixSubEquivProd {e f₁ f₂ : A} (h : IsOrthDecomp e f₁ f₂) :
    fixSub k M e ≃ₗ[k] fixSub k M f₁ × fixSub k M f₂ where
  toFun m := (⟨f₁ • (m : M), smul_mem_fixSub h.1 _⟩, ⟨f₂ • (m : M), smul_mem_fixSub h.2.1 _⟩)
  invFun p := ⟨(p.1 : M) + p.2, by
    rw [mem_fixSub, smul_add, ← p.1.2, ← p.2.2, smul_smul, smul_smul, h.mul_left₁, h.mul_left₂]⟩
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_comm _ c]
  left_inv m := Subtype.ext (by
    change f₁ • (m : M) + f₂ • (m : M) = m
    rw [← add_smul, h.2.2.2.2]; exact m.2)
  right_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
    rw [mem_fixSub] at hu hv
    ext
    · change f₁ • (u + v) = u
      rw [smul_add, hu, ← hv, smul_smul, h.2.2.1, zero_smul, add_zero]
    · change f₂ • (u + v) = v
      rw [smul_add, hv, ← hu, smul_smul, h.2.2.2.1, zero_smul, zero_add]

end modules

/-! ### Left and right ideals -/

section ideals

open MulOpposite

/-- The left ideal `A f = {y | y f = y}` (for `f` idempotent), a left `A`-module. -/
def lIdeal (f : A) : Submodule A A where
  carrier := {y | y * f = y}
  add_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, add_mul] at *; rw [hx, hy]
  zero_mem' := zero_mul f
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    rw [mul_assoc, hx]

theorem mem_lIdeal {f y : A} : y ∈ lIdeal f ↔ y * f = y := Iff.rfl

/-- The right ideal `f A = {y | f y = y}` (for `f` idempotent), a right `A`-module, i.e. an
`Aᵐᵒᵖ`-module. -/
def rIdeal (f : A) : Submodule Aᵐᵒᵖ A where
  carrier := {y | f * y = y}
  add_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, mul_add] at *; rw [hx, hy]
  zero_mem' := mul_zero f
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, op_smul_eq_mul, smul_eq_mul_unop] at *
    rw [← mul_assoc, hx]

theorem mem_rIdeal {f y : A} : y ∈ rIdeal f ↔ f * y = y := Iff.rfl

variable {a b f f' : A}

/-- Equivalent idempotents give isomorphic left projectives `A f ≅ A f'`, `y ↦ y a`. -/
def IsEquivPair.lIdealEquiv (h : IsEquivPair a b f f') : lIdeal f ≃ₗ[A] lIdeal f' where
  toFun y := ⟨(y : A) * a, by rw [mem_lIdeal, mul_assoc, h.mul_right]⟩
  invFun y := ⟨(y : A) * b, by rw [mem_lIdeal, mul_assoc, h.mul_right']⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' c x := Subtype.ext (by simp [mul_assoc])
  left_inv y := Subtype.ext (by
    change (y : A) * a * b = y
    rw [mul_assoc, h.1]; exact y.2)
  right_inv y := Subtype.ext (by
    change (y : A) * b * a = y
    rw [mul_assoc, h.2.1]; exact y.2)

/-- Equivalent idempotents give isomorphic right projectives `f A ≅ f' A`, `y ↦ b y`
(KL I, proof of Proposition 2.13). -/
def IsEquivPair.rIdealEquiv (h : IsEquivPair a b f f') : rIdeal f ≃ₗ[Aᵐᵒᵖ] rIdeal f' where
  toFun y := ⟨b * (y : A), by rw [mem_rIdeal, ← mul_assoc, h.left_mul']⟩
  invFun y := ⟨a * (y : A), by rw [mem_rIdeal, ← mul_assoc, h.left_mul]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (by
    simp only [SetLike.val_smul, smul_eq_mul_unop, RingHom.id_apply, mul_assoc])
  left_inv y := Subtype.ext (by
    change a * (b * (y : A)) = y
    rw [← mul_assoc, h.1]; exact y.2)
  right_inv y := Subtype.ext (by
    change b * (a * (y : A)) = y
    rw [← mul_assoc, h.2.1]; exact y.2)

variable {e f₁ f₂ : A}

/-- `A e ≅ A f₁ ⊕ A f₂` for an orthogonal decomposition `e = f₁ + f₂`, `y ↦ (y f₁, y f₂)`. -/
def IsOrthDecomp.lIdealEquivProd (h : IsOrthDecomp e f₁ f₂) :
    lIdeal e ≃ₗ[A] lIdeal f₁ × lIdeal f₂ where
  toFun y := (⟨(y : A) * f₁, by rw [mem_lIdeal, mul_assoc, h.1.eq]⟩,
    ⟨(y : A) * f₂, by rw [mem_lIdeal, mul_assoc, h.2.1.eq]⟩)
  invFun p := ⟨(p.1 : A) + p.2, by
    rw [mem_lIdeal, add_mul, ← p.1.2, ← p.2.2, mul_assoc, mul_assoc, h.mul_right₁,
      h.mul_right₂]⟩
  map_add' x y := by ext <;> simp [add_mul]
  map_smul' c x := by ext <;> simp [mul_assoc]
  left_inv y := Subtype.ext (by
    change (y : A) * f₁ + (y : A) * f₂ = y
    rw [← mul_add, h.2.2.2.2]; exact y.2)
  right_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
    rw [mem_lIdeal] at hu hv
    ext
    · change (u + v) * f₁ = u
      rw [add_mul, hu, ← hv, mul_assoc, h.2.2.2.1, mul_zero, add_zero]
    · change (u + v) * f₂ = v
      rw [add_mul, hv, ← hu, mul_assoc, h.2.2.1, mul_zero, zero_add]

/-- `e A ≅ f₁ A ⊕ f₂ A` for an orthogonal decomposition `e = f₁ + f₂`, `y ↦ (f₁ y, f₂ y)`. -/
def IsOrthDecomp.rIdealEquivProd (h : IsOrthDecomp e f₁ f₂) :
    rIdeal e ≃ₗ[Aᵐᵒᵖ] rIdeal f₁ × rIdeal f₂ where
  toFun y := (⟨f₁ * (y : A), by rw [mem_rIdeal, ← mul_assoc, h.1.eq]⟩,
    ⟨f₂ * (y : A), by rw [mem_rIdeal, ← mul_assoc, h.2.1.eq]⟩)
  invFun p := ⟨(p.1 : A) + p.2, by
    rw [mem_rIdeal, mul_add, ← p.1.2, ← p.2.2, ← mul_assoc, ← mul_assoc, h.mul_left₁,
      h.mul_left₂]⟩
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' c x := by ext <;> simp [smul_eq_mul_unop, mul_assoc]
  left_inv y := Subtype.ext (by
    change f₁ * (y : A) + f₂ * (y : A) = y
    rw [← add_mul, h.2.2.2.2]; exact y.2)
  right_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
    rw [mem_rIdeal] at hu hv
    ext
    · change f₁ * (u + v) = u
      rw [mul_add, hu, ← hv, ← mul_assoc, h.2.2.1, zero_mul, add_zero]
    · change f₂ * (u + v) = v
      rw [mul_add, hv, ← hu, ← mul_assoc, h.2.2.2.1, zero_mul, zero_add]

end ideals

end Categorification
