/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Maps of induced modules given by elements intertwining modulo the annihilator

For non-unital ring maps `φ ψ : A → B` and an `A`-module `N`, an element `x ∈ B` with
`φ a x = x ψ a` gives the map `Ind N φ → Ind N ψ`, `z ⊗ n ↦ z x ⊗ n`
(`InductionAlong.natMap`). This file weakens the intertwining condition to what the map needs:
`z φ(a) x ⊗ n = z x ⊗ a n` in `Ind N ψ` (`InductionAlong.IntertwinesOn`). It holds as soon as
`φ a x - x ψ a` lies in the left ideal of `B` spanned by the `w ψ(b)` with `b` killing `N`
(`InductionAlong.nullIdeal`), and it is preserved by products.

This is used for Webster's cap bimodule (arXiv:1309.3796v3, §7.3, proof of Lemma 7.17): a strand
passing under the maximum of the cap commutes with the diagrams at the maximum only up to
diagrams in which a strand leaves the cap, and those act by zero on the coefficient module.

## Main definitions

* `InductionAlong.nullIdeal`: the left ideal spanned by the `w ψ(b)` with `b • N = 0`.
* `InductionAlong.IntertwinesOn`: the intertwining condition on `N`.
* `InductionAlong.natMapOn`: the induced map.
-/

namespace Categorification.InductionAlong

open MulOpposite

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B]
  {N : Type w} [AddCommGroup N] [Module A N] {φ ψ χ : A →ₙ+* B}

section Null

variable (N ψ) in
/-- The left ideal of `B` spanned by the `w ψ(b)` with `b` killing `N`: its elements `y` give
`y ⊗ n = 0` in the induced module. -/
def nullIdeal : Submodule B B :=
  Submodule.span B {y | ∃ (w : B) (b : A), (∀ n : N, b • n = 0) ∧ y = w * ψ b}

theorem mem_lIdeal_of_mem_nullIdeal {y : B} (hy : y ∈ nullIdeal N ψ) : y ∈ lIdeal (ψ 1) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, b, -, rfl⟩ := hy
    exact mul_mem_corner ψ w b
  | zero => exact (lIdeal (ψ 1)).zero_mem
  | add y y' _ _ hy hy' => exact (lIdeal (ψ 1)).add_mem hy hy'
  | smul c y _ hy => exact (lIdeal (ψ 1)).smul_mem c hy

theorem tmul_eq_zero_of_mem_nullIdeal {y : B} (hy : y ∈ nullIdeal N ψ) (n : N) :
    (Ind.tmul ⟨y, mem_lIdeal_of_mem_nullIdeal hy⟩ n : Ind N ψ) = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, b, hb, rfl⟩ := hy
    have : (⟨w * ψ b, mem_lIdeal_of_mem_nullIdeal (Submodule.subset_span ⟨w, b, hb, rfl⟩)⟩ :
        Corner ψ) = op b • ⟨w * ψ 1, mul_mem_corner ψ w 1⟩ :=
      Subtype.ext (by rw [op_smul_val, mul_assoc, ← map_mul, one_mul])
    rw [this, Ind.op_smul_tmul, hb, Ind.tmul_zero]
  | zero => exact Ind.zero_tmul n
  | add y y' hy hy' ih ih' =>
    have : (⟨y + y', mem_lIdeal_of_mem_nullIdeal (add_mem hy hy')⟩ : Corner ψ) =
        ⟨y, mem_lIdeal_of_mem_nullIdeal hy⟩ + ⟨y', mem_lIdeal_of_mem_nullIdeal hy'⟩ := rfl
    rw [this, Ind.add_tmul, ih, ih', add_zero]
  | smul c y hy ih =>
    have : (⟨c • y, mem_lIdeal_of_mem_nullIdeal (Submodule.smul_mem _ c hy)⟩ : Corner ψ) =
        c • (⟨y, mem_lIdeal_of_mem_nullIdeal hy⟩ : Corner ψ) := rfl
    rw [this, ← Ind.smul_tmul, ih, smul_zero]

theorem mul_mem_nullIdeal (z : B) {y : B} (hy : y ∈ nullIdeal N ψ) : z * y ∈ nullIdeal N ψ :=
  Submodule.smul_mem _ z hy

theorem mul_map_mem_nullIdeal (w : B) {b : A} (hb : ∀ n : N, b • n = 0) :
    w * ψ b ∈ nullIdeal N ψ :=
  Submodule.subset_span ⟨w, b, hb, rfl⟩

end Null

section IntertwinesOn

/-- Right multiplication by `x` with `x ψ(1) = x`, on corners. -/
def cornerMulOf {x : B} (hx : x * ψ 1 = x) (z : Corner φ) : Corner ψ :=
  ⟨z.1 * x, by change z.1 * x * ψ 1 = z.1 * x; rw [mul_assoc, hx]⟩

@[simp] theorem cornerMulOf_val {x : B} (hx : x * ψ 1 = x) (z : Corner φ) :
    (cornerMulOf (φ := φ) hx z).1 = z.1 * x := rfl

variable (N φ ψ) in
/-- **`x` intertwines `φ` and `ψ` on `N`**: `z φ(a) x ⊗ n = z x ⊗ a n` in `Ind N ψ` for all `z` in
the corner of `φ`. This is what the map `z ⊗ n ↦ z x ⊗ n` needs to be well defined. -/
structure IntertwinesOn (x : B) : Prop where
  unit : x * ψ 1 = x
  slide : ∀ (a : A) (z : Corner φ) (n : N),
    (Ind.tmul (cornerMulOf unit (op a • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf unit z) (a • n)

/-- **The map of induced modules** `z ⊗ n ↦ z x ⊗ n` given by an element intertwining on `N`. -/
def natMapOn {x : B} (hx : IntertwinesOn N φ ψ x) : Ind N φ →ₗ[B] Ind N ψ :=
  Ind.lift (fun z n => Ind.tmul (cornerMulOf hx.unit z) n)
    (fun z z' n => by
      rw [← Ind.add_tmul]; congr 1; exact Subtype.ext (add_mul _ _ _))
    (fun z n n' => Ind.tmul_add _ n n')
    (fun z a n => hx.slide a z n)
    (fun b z n => by
      rw [Ind.smul_tmul]; congr 1; exact Subtype.ext (mul_assoc b z.1 x))

@[simp] theorem natMapOn_tmul {x : B} (hx : IntertwinesOn N φ ψ x) (z : Corner φ) (n : N) :
    natMapOn hx (Ind.tmul z n) = Ind.tmul (cornerMulOf hx.unit z) n := rfl

namespace IntertwinesOn

/-- An exactly intertwining element intertwines on every module. -/
theorem of_intertwines {x : B} (hx : Intertwines φ ψ x) (h1 : x * ψ 1 = x) :
    IntertwinesOn N φ ψ x where
  unit := h1
  slide a z n := by
    rw [← Ind.op_smul_tmul]
    congr 1
    exact Subtype.ext (by
      change z.1 * φ a * x = z.1 * x * ψ a
      rw [mul_assoc, hx a, mul_assoc])

/-- **Products** of intertwining elements intertwine. -/
theorem mul {x y : B} (hx : IntertwinesOn N φ ψ x) (hy : IntertwinesOn N ψ χ y) :
    IntertwinesOn N φ χ (x * y) where
  unit := by rw [mul_assoc, hy.unit]
  slide a z n := by
    have h := congrArg (natMapOn hy) (hx.slide a z n)
    rw [natMapOn_tmul, natMapOn_tmul] at h
    convert h using 2 <;> exact Subtype.ext (by simp [mul_assoc])

/-- The criterion for a single `a`, through the null ideal. -/
theorem slide_of_mem_nullIdeal {x : B} (h1 : x * ψ 1 = x) {a : A}
    (ha : φ a * x - x * ψ a ∈ nullIdeal N ψ) (z : Corner φ) (n : N) :
    (Ind.tmul (cornerMulOf h1 (op a • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf h1 z) (a • n) := by
  have hz := mul_mem_nullIdeal z.1 ha
  have hsplit : cornerMulOf h1 (op a • z) =
      ⟨z.1 * (φ a * x - x * ψ a), mem_lIdeal_of_mem_nullIdeal hz⟩ + op a • cornerMulOf h1 z :=
    Subtype.ext (by simp [mul_sub, mul_assoc])
  rw [hsplit, Ind.add_tmul, tmul_eq_zero_of_mem_nullIdeal hz, zero_add, Ind.op_smul_tmul]

/-- An exact intertwining relation for a single `a`. -/
theorem slide_of_eq {x : B} (h1 : x * ψ 1 = x) {a : A} (ha : φ a * x = x * ψ a)
    (z : Corner φ) (n : N) :
    (Ind.tmul (cornerMulOf h1 (op a • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf h1 z) (a • n) :=
  slide_of_mem_nullIdeal h1 (by rw [ha, sub_self]; exact zero_mem _) z n

/-- The set of `a` satisfying the intertwining condition is closed under products. -/
theorem slide_mul {x : B} (h1 : x * ψ 1 = x) {a b : A}
    (ha : ∀ (z : Corner φ) (n : N),
      (Ind.tmul (cornerMulOf h1 (op a • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf h1 z) (a • n))
    (hb : ∀ (z : Corner φ) (n : N),
      (Ind.tmul (cornerMulOf h1 (op b • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf h1 z) (b • n))
    (z : Corner φ) (n : N) :
    (Ind.tmul (cornerMulOf h1 (op (a * b) • z)) n : Ind N ψ) =
      Ind.tmul (cornerMulOf h1 z) ((a * b) • n) := by
  rw [op_mul, mul_smul, hb, ha, mul_smul]

/-- The set of `a` satisfying the intertwining condition is closed under sums. -/
theorem slide_add {x : B} (h1 : x * ψ 1 = x) {a b : A}
    (ha : ∀ (z : Corner φ) (n : N),
      (Ind.tmul (cornerMulOf h1 (op a • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf h1 z) (a • n))
    (hb : ∀ (z : Corner φ) (n : N),
      (Ind.tmul (cornerMulOf h1 (op b • z)) n : Ind N ψ) = Ind.tmul (cornerMulOf h1 z) (b • n))
    (z : Corner φ) (n : N) :
    (Ind.tmul (cornerMulOf h1 (op (a + b) • z)) n : Ind N ψ) =
      Ind.tmul (cornerMulOf h1 z) ((a + b) • n) := by
  have : cornerMulOf h1 (op (a + b) • z) = cornerMulOf h1 (op a • z) + cornerMulOf h1 (op b • z) :=
    Subtype.ext (by
      change (op (a + b) • z).1 * x = (op a • z).1 * x + (op b • z).1 * x
      rw [op_smul_val, op_smul_val, op_smul_val, map_add, mul_add, add_mul])
  rw [this, Ind.add_tmul, ha, hb, add_smul, Ind.tmul_add]

end IntertwinesOn

/-- Products of intertwining elements give composites of maps. -/
theorem natMapOn_comp {x y : B} (hx : IntertwinesOn N φ ψ x) (hy : IntertwinesOn N ψ χ y) :
    (natMapOn hy).comp (natMapOn hx) = natMapOn (hx.mul hy) :=
  Ind.ext fun z n => by
    rw [LinearMap.comp_apply, natMapOn_tmul, natMapOn_tmul, natMapOn_tmul]
    congr 1
    exact Subtype.ext (mul_assoc _ _ _)

end IntertwinesOn

end Categorification.InductionAlong
