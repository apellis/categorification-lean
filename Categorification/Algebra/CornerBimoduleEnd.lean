/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerBimodule

/-!
# Endomorphisms of a corner bimodule from its blocks

For idempotents `e, e'` of a ring `A` and a finite family of orthogonal idempotents `fᵢ` with
`∑ fᵢ = e`, the left action of the corner `e A e` on the right `e' A e'`-module `e A e'` is
bijective onto its endomorphisms (`bijective_toModuleEnd_cornerBimodule`) as soon as, for every
pair `i, j`, left multiplication by `fⱼ A fᵢ` is injective on `fᵢ A e'` and every right-linear
map `fᵢ A e' → fⱼ A e'` is left multiplication by an element of `fⱼ A fᵢ`.

This is the form in which B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Corollary 6.19, identifies the endomorphisms of a tilting generator.
-/

namespace Categorification

open MulOpposite

attribute [local instance] cornerBimodule.instModuleLeft cornerBimodule.instModuleRight

variable {A : Type*} [Ring A] {e e' : A} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
  {ι : Type*} [Fintype ι] (f : ι → A)

include he in
theorem corner_val_mem_cornerBimodule (c : he.Corner) : c.1 ∈ cornerBimodule e e := by
  obtain ⟨h1, h2⟩ := (Subsemigroup.mem_corner_iff he).1 c.2
  exact ⟨h1, h2⟩

/-- **Endomorphisms of a corner bimodule from its blocks**: if `e = ∑ fᵢ` for orthogonal
idempotents `fᵢ`, and for all `i, j` left multiplication by `fⱼ A fᵢ` on `fᵢ A e'` is injective
and onto the right-linear maps `fᵢ A e' → fⱼ A e'`, then the corner `e A e` acts on `e A e'` by
all of its right-linear endomorphisms, faithfully. -/
theorem bijective_toModuleEnd_cornerBimodule (hidem : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (hsum : ∑ i, f i = e)
    (hinj : ∀ i j, ∀ x ∈ cornerBimodule (f j) (f i),
      (∀ y ∈ cornerBimodule (f i) e', x * y = 0) → x = 0)
    (hsurj : ∀ i j, ∀ φ : cornerBimodule (f i) e' →ₗ[he'.Cornerᵐᵒᵖ] cornerBimodule (f j) e',
      ∃ x ∈ cornerBimodule (f j) (f i), ∀ y, (φ y).1 = x * y.1) :
    Function.Bijective
      (Module.toModuleEnd he'.Cornerᵐᵒᵖ (S := he.Corner) (cornerBimodule e e')) := by
  have hef : ∀ i, e * f i = f i := fun i => by
    rw [← hsum, Finset.sum_mul, Finset.sum_eq_single i (fun j _ hj => horth j i hj)
      (by simp), hidem]
  have hfe : ∀ i, f i * e = f i := fun i => by
    rw [← hsum, Finset.mul_sum, Finset.sum_eq_single i (fun j _ hj => horth i j (Ne.symm hj))
      (by simp), hidem]
  -- an element of `fᵢ A e'` lies in `e A e'`
  have hmem : ∀ i, ∀ y ∈ cornerBimodule (f i) e', y ∈ cornerBimodule e e' := fun i y hy =>
    ⟨by rw [← hy.1, ← mul_assoc, hef], hy.2⟩
  -- the block decomposition of an element of `e A e`
  have hdec : ∀ c : A, e * c = c → c * e = c → c = ∑ i, ∑ j, f j * c * f i := fun c h1 h2 => by
    conv_lhs => rw [← h2, ← h1, ← hsum]
    simp only [Finset.sum_mul, Finset.mul_sum]
  -- an element of `e A e` killing `e A e'` vanishes
  have hkey : ∀ d : A, e * d = d → d * e = d → (∀ y ∈ cornerBimodule e e', d * y = 0) →
      d = 0 := fun d h1 h2 h0 => by
    rw [hdec d h1 h2]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    refine hinj i j _ ⟨by rw [← mul_assoc, ← mul_assoc, hidem], by rw [mul_assoc, hidem]⟩
      fun y hy => ?_
    calc f j * d * f i * y = f j * (d * (f i * y)) := by simp only [mul_assoc]
      _ = 0 := by rw [hy.1, h0 y (hmem i y hy), mul_zero]
  constructor
  · intro c c' hcc'
    rw [← sub_eq_zero]
    have h0 : ∀ y ∈ cornerBimodule e e', (c - c').1 * y = 0 := fun y hy => by
      have := congrArg (fun φ : Module.End he'.Cornerᵐᵒᵖ (cornerBimodule e e') =>
        ((φ ⟨y, hy⟩ : cornerBimodule e e') : A)) hcc'
      simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply,
        cornerBimodule.coe_smul_left] at this
      change (c.1 - c'.1) * y = 0
      rw [sub_mul, this, sub_self]
    have hc := (Subsemigroup.mem_corner_iff he).1 (c - c').2
    apply Subtype.ext
    exact hkey _ hc.1 hc.2 h0
  · intro φ
    have hx := fun i j => hsurj i j
      { toFun := fun y => ⟨f j * (φ ⟨y.1, hmem i y.1 y.2⟩).1,
          by rw [← mul_assoc, hidem], by rw [mul_assoc, (φ _).2.2]⟩
        map_add' := fun y y' => Subtype.ext (by
          change f j * (φ ⟨y.1 + y'.1, _⟩).1 = f j * (φ ⟨y.1, _⟩).1 + f j * (φ ⟨y'.1, _⟩).1
          rw [← mul_add]
          congr 1
          exact congrArg Subtype.val (map_add φ ⟨y.1, hmem i y.1 y.2⟩ ⟨y'.1, hmem i y'.1 y'.2⟩))
        map_smul' := fun a y => Subtype.ext (by
          change f j * (φ ⟨y.1 * a.unop.1, _⟩).1 = f j * (φ ⟨y.1, _⟩).1 * a.unop.1
          rw [mul_assoc]
          congr 1
          exact congrArg Subtype.val (map_smul φ a ⟨y.1, hmem i y.1 y.2⟩)) }
    choose x hxmem hxφ using hx
    let c : A := ∑ i, ∑ j, x i j
    have hc : c ∈ Subsemigroup.corner e := (Subsemigroup.mem_corner_iff he).2 ⟨by
      simp only [c, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [← (hxmem i j).1, ← mul_assoc, hef], by
      simp only [c, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [← (hxmem i j).2, mul_assoc, hfe]⟩
    refine ⟨⟨c, hc⟩, LinearMap.ext fun y => Subtype.ext ?_⟩
    change c * y.1 = (φ y).1
    have hy : ∀ i, f i * y.1 ∈ cornerBimodule (f i) e' := fun i =>
      ⟨by rw [← mul_assoc, hidem], by rw [mul_assoc, y.2.2]⟩
    have hφi : ∀ i, (φ ⟨f i * y.1, hmem i _ (hy i)⟩).1 =
        ∑ j, f j * (φ ⟨f i * y.1, hmem i _ (hy i)⟩).1 := fun i => by
      rw [← Finset.sum_mul, hsum, (φ _).2.1]
    calc c * y.1 = ∑ i, ∑ j, x i j * (f i * y.1) := by
          simp only [c, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, (hxmem i j).2]
      _ = ∑ i, (φ ⟨f i * y.1, hmem i _ (hy i)⟩).1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hφi i]
          exact Finset.sum_congr rfl fun j _ => (hxφ i j ⟨_, hy i⟩).symm
      _ = (φ y).1 := by
          rw [← AddSubgroup.val_finsetSum (H := cornerBimodule e e'), ← map_sum]
          congr 2
          apply Subtype.ext
          rw [AddSubgroup.val_finsetSum, ← Finset.sum_mul, hsum, y.2.1]

end Categorification
