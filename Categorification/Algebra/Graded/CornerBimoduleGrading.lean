/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.BalancedInduction

/-!
# A rectangular corner as a graded bimodule over two algebras

Let `A` be a graded `k`-algebra and let `f : T → A`, `g : T' → A` be degree-preserving
multiplicative `k`-linear maps (for instance, identifications of `T` and `T'` with the corner
rings `e A e` and `e' A e'`, where `e = f 1` and `e' = g 1`). Then the rectangular corner
`e A e' = {x | e x = x, x e' = x}` is a graded `(T, T')`-bimodule, acting through `f` on the left
and through `g` on the right, graded by the grading of `A` when `e` and `e'` have degree zero
(`RectBimod f g`).

Right `T'`-modules are left `T'ᵐᵒᵖ`-modules, so for the functor `N ↦ N ⊗_T e A e'` on right
modules (`GFin.induce` over the opposite algebras) `e A e'` is a left `T'ᵐᵒᵖ`-module and a left
`Tᵐᵒᵖᵐᵒᵖ`-module. In B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, §6.1, the bimodules `B_w` of Definition 6.6 are of this form.

## Main definitions

* `rectCorner e e'` : the `k`-submodule `e A e'`.
* `RectBimod f g` : `f(1) A g(1)` with the actions of `T` and `T'`.
* `RectBimod.grading 𝒢 f g` : its grading, a decomposition for idempotents of degree zero.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum MulOpposite

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

variable (e e' : A) in
/-- The rectangular corner `e A e'` as a `k`-submodule. -/
def rectCorner : Submodule k A where
  carrier := {x | e * x = x ∧ x * e' = x}
  add_mem' {x y} hx hy := ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  zero_mem' := ⟨mul_zero e, zero_mul e'⟩
  smul_mem' c x hx := ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩

theorem mem_rectCorner {e e' x : A} : x ∈ rectCorner (k := k) e e' ↔ e * x = x ∧ x * e' = x :=
  Iff.rfl

variable {T T' : Type*} [Ring T] [Algebra k T] [Ring T'] [Algebra k T']

/-- The rectangular corner `f(1) A g(1)`, a bimodule over `T` (through `f`) and `T'` (through
`g`). -/
def RectBimod (f : T →ₙₐ[k] A) (g : T' →ₙₐ[k] A) : Type _ := rectCorner (k := k) (f 1) (g 1)

namespace RectBimod

variable (f : T →ₙₐ[k] A) (g : T' →ₙₐ[k] A)

instance : AddCommGroup (RectBimod f g) :=
  inferInstanceAs (AddCommGroup (rectCorner (k := k) (f 1) (g 1)))

instance : Module k (RectBimod f g) := inferInstanceAs (Module k (rectCorner (k := k) (f 1) (g 1)))

/-- The underlying element of `A`. -/
def val : RectBimod f g →ₗ[k] A := (rectCorner (k := k) (f 1) (g 1)).subtype

variable {f g}

theorem val_injective : Function.Injective (val f g) := Subtype.val_injective

@[ext] theorem ext {x y : RectBimod f g} (h : val f g x = val f g y) : x = y := Subtype.ext h

theorem mem (x : RectBimod f g) : f 1 * val f g x = val f g x ∧ val f g x * g 1 = val f g x :=
  (x : rectCorner (k := k) (f 1) (g 1)).2

/-- Build an element from an element of `f(1) A g(1)`. -/
def mk (x : A) (hx : f 1 * x = x ∧ x * g 1 = x) : RectBimod f g :=
  (⟨x, hx⟩ : rectCorner (k := k) (f 1) (g 1))

@[simp] theorem val_mk (x : A) (hx : f 1 * x = x ∧ x * g 1 = x) : val f g (mk x hx) = x := rfl

theorem left_mem (t : T) (x : RectBimod f g) :
    f 1 * (f t * val f g x) = f t * val f g x ∧ (f t * val f g x) * g 1 = f t * val f g x := by
  have h : f 1 * f t = f t := by rw [← map_mul, one_mul]
  exact ⟨by rw [← mul_assoc, h], by rw [mul_assoc, (mem x).2]⟩

theorem right_mem (u : T') (x : RectBimod f g) :
    f 1 * (val f g x * g u) = val f g x * g u ∧ (val f g x * g u) * g 1 = val f g x * g u := by
  have h : g u * g 1 = g u := by rw [← map_mul, mul_one]
  exact ⟨by rw [← mul_assoc, (mem x).1], by rw [mul_assoc, h]⟩

/-- The left action of `T` through `f`, as a left `Tᵐᵒᵖᵐᵒᵖ`-module. -/
instance moduleLeft : Module Tᵐᵒᵖᵐᵒᵖ (RectBimod f g) where
  smul t x := mk (f t.unop.unop * val f g x) (left_mem t.unop.unop x)
  one_smul x := ext (by
    change f 1 * val f g x = val f g x
    rw [(mem x).1])
  mul_smul t s x := ext (by
    change f (t.unop.unop * s.unop.unop) * val f g x =
      f t.unop.unop * (f s.unop.unop * val f g x)
    rw [map_mul, mul_assoc])
  smul_zero t := ext (mul_zero (f t.unop.unop))
  smul_add t x y := ext (mul_add (f t.unop.unop) (val f g x) (val f g y))
  add_smul t s x := ext (by
    change f (t.unop.unop + s.unop.unop) * val f g x =
      f t.unop.unop * val f g x + f s.unop.unop * val f g x
    rw [map_add, add_mul])
  zero_smul x := ext (by
    change f 0 * val f g x = 0
    rw [map_zero, zero_mul])

/-- The right action of `T'` through `g`, as a left `T'ᵐᵒᵖ`-module. -/
instance moduleRight : Module T'ᵐᵒᵖ (RectBimod f g) where
  smul u x := mk (val f g x * g u.unop) (right_mem u.unop x)
  one_smul x := ext (by
    change val f g x * g 1 = val f g x
    rw [(mem x).2])
  mul_smul u w x := ext (by
    change val f g x * g (w.unop * u.unop) = val f g x * g w.unop * g u.unop
    rw [map_mul, mul_assoc])
  smul_zero u := ext (zero_mul (g u.unop))
  smul_add u x y := ext (add_mul (val f g x) (val f g y) (g u.unop))
  add_smul u w x := ext (by
    change val f g x * g (u.unop + w.unop) = val f g x * g u.unop + val f g x * g w.unop
    rw [map_add, mul_add])
  zero_smul x := ext (by
    change val f g x * g 0 = 0
    rw [map_zero, mul_zero])

theorem val_smul_left (t : Tᵐᵒᵖᵐᵒᵖ) (x : RectBimod f g) :
    val f g (t • x) = f t.unop.unop * val f g x := rfl

theorem val_smul_right (u : T'ᵐᵒᵖ) (x : RectBimod f g) :
    val f g (u • x) = val f g x * g u.unop := rfl

instance : SMulCommClass T'ᵐᵒᵖ Tᵐᵒᵖᵐᵒᵖ (RectBimod f g) :=
  ⟨fun u t x => ext (mul_assoc (f t.unop.unop) (val f g x) (g u.unop))⟩

instance : SMulCommClass Tᵐᵒᵖᵐᵒᵖ T'ᵐᵒᵖ (RectBimod f g) := SMulCommClass.symm _ _ _

instance : IsScalarTower k Tᵐᵒᵖᵐᵒᵖ (RectBimod f g) :=
  ⟨fun c t x => ext (by
    change f (c • t.unop.unop) * val f g x = c • (f t.unop.unop * val f g x)
    rw [map_smul, smul_mul_assoc])⟩

instance : IsScalarTower k T'ᵐᵒᵖ (RectBimod f g) :=
  ⟨fun c u x => ext (by
    change val f g x * g (c • u.unop) = c • (val f g x * g u.unop)
    rw [map_smul, mul_smul_comm])⟩

/-! ### The grading -/

/-- The grading of `f(1) A g(1)` induced by that of `A`. -/
def grading (𝒢 : ℤ → Submodule k A) (f : T →ₙₐ[k] A) (g : T' →ₙₐ[k] A) :
    ℤ → Submodule k (RectBimod f g) :=
  comap 𝒢 (val f g)

variable (𝒢 : ℤ → Submodule k A)

theorem mem_grading {d : ℤ} {x : RectBimod f g} : x ∈ grading 𝒢 f g d ↔ val f g x ∈ 𝒢 d :=
  Iff.rfl

variable {𝒯 : ℤ → Submodule k T} {𝒯' : ℤ → Submodule k T'}

/-- `T` acts by degree-preserving maps, as a graded right module over `Tᵐᵒᵖ`. -/
theorem gradedSMul_left [SetLike.GradedMonoid 𝒢]
    (hf : ∀ ⦃d : ℤ⦄ ⦃t : T⦄, t ∈ 𝒯 d → f t ∈ 𝒢 d) :
    SetLike.GradedSMul (oppositeGrade (oppositeGrade 𝒯)) (grading 𝒢 f g) :=
  ⟨fun {_ _} _ _ ht hx => SetLike.GradedMul.mul_mem (A := 𝒢) (hf ht) hx⟩

/-- `T'` acts on the right by degree-preserving maps. -/
theorem gradedSMul_right [SetLike.GradedMonoid 𝒢]
    (hg : ∀ ⦃d : ℤ⦄ ⦃u : T'⦄, u ∈ 𝒯' d → g u ∈ 𝒢 d) :
    SetLike.GradedSMul (oppositeGrade 𝒯') (grading 𝒢 f g) :=
  ⟨fun {l d} u x hu hx => by
    change val f g x * g u.unop ∈ 𝒢 (l + d)
    rw [add_comm l d]
    exact SetLike.GradedMul.mul_mem (A := 𝒢) hx (hg hu)⟩

variable [GradedAlgebra 𝒢]

theorem isInternal_grading (he0 : f 1 ∈ 𝒢 0) (he'0 : g 1 ∈ 𝒢 0) :
    IsInternal (grading 𝒢 f g) := by
  apply isInternal_comap _ _ val_injective
  intro x j
  have hx := mem x
  refine ⟨mk (decompose 𝒢 (val f g x) j : A) ⟨?_, ?_⟩, rfl⟩
  · rw [← coe_decompose_mul_of_left_mem_zero 𝒢 he0, hx.1]
  · rw [← coe_decompose_mul_of_right_mem_zero 𝒢 he'0, hx.2]

/-- The decomposition into homogeneous pieces, for `f 1` and `g 1` of degree zero. -/
@[instance_reducible] def decomposition (he0 : f 1 ∈ 𝒢 0) (he'0 : g 1 ∈ 𝒢 0) :
    Decomposition (grading 𝒢 f g) :=
  (isInternal_grading 𝒢 he0 he'0).chooseDecomposition

/-! ### Cutting by idempotents on both sides -/

section Cut

variable {S : Type*} [Ring S] [Algebra k S]

omit [GradedAlgebra 𝒢] in
private theorem mem_of_cut {f' : S →ₙₐ[k] A} {t : T} {s : S} {u : T'} (h : f t = f' s)
    (x : idemSubspace k (idemSubspace k (RectBimod f g) (op u)) (op (op t))) :
    f' 1 * val f g x.1.1 = val f g x.1.1 ∧ val f g x.1.1 * g 1 = val f g x.1.1 := by
  have ht : f t * val f g x.1.1 = val f g x.1.1 :=
    congrArg (fun y => val f g y.1) x.2
  have h1 : f' 1 * f' s = f' s := by rw [← map_mul, one_mul]
  refine ⟨?_, (mem x.1.1).2⟩
  rw [← ht, h, ← mul_assoc, h1]

/-- The comparison of cuts `f(t) X g(u)` along an equality `f t = f' s`. -/
private def cutTransfer {f' : S →ₙₐ[k] A} {t : T} {s : S} {u : T'} (h : f t = f' s) :
    idemSubspace k (idemSubspace k (RectBimod f g) (op u)) (op (op t)) →ₗ[k]
      idemSubspace k (idemSubspace k (RectBimod f' g) (op u)) (op (op s)) where
  toFun x := ⟨⟨mk (val f g x.1.1) (mem_of_cut h x), ext (by
      change val f g x.1.1 * g u = val f g x.1.1
      exact congrArg (val f g) x.1.2)⟩, Subtype.ext (ext (by
      change f' s * val f g x.1.1 = val f g x.1.1
      rw [← h]
      exact congrArg (fun y => val f g y.1) x.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [GradedAlgebra 𝒢] in
/-- **Cuts only depend on the cutting elements**: if `f t = f' s` in `A`, then
`f(t) (f(1) A g(1)) g(u)` and `f'(s) (f'(1) A g(1)) g(u)` have the same graded dimension. -/
theorem gdimPoly_idem_idem_grading_eq {f' : S →ₙₐ[k] A} {t : T} {s : S} {u : T'}
    (h : f t = f' s) :
    gdimPoly (idem (idem (grading 𝒢 f g) (op u)) (op (op t))) =
      gdimPoly (idem (idem (grading 𝒢 f' g) (op u)) (op (op s))) :=
  gdimPoly_congr (A := k)
    { toLinearEquiv :=
        LinearEquiv.ofLinearMap (cutTransfer (g := g) h) (cutTransfer (g := g) h.symm) rfl rfl
      map_mem' := fun _ _ hx => hx
      symm_map_mem' := fun _ _ hy => hy }

end Cut

end RectBimod

end Categorification.Graded
