/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Vanishing of Ext along short exact sequences

Dimension shifting for the vanishing of `Ext` in an abelian category, in either variable, along a
short exact sequence `0 → X₁ → X₂ → X₃ → 0`. Background for B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, §7.1, proof of Proposition 7.8, which shifts
along a coresolution of a dual standard module and along the resolution of `L_λ` being built.

## Main results

* `Ext.subsingleton_X₁_succ`: `Extⁿ(X, X₃) = 0` and `Extⁿ⁺¹(X, X₂) = 0` give `Extⁿ⁺¹(X, X₁) = 0`.
* `Ext.subsingleton_X₁_zero`: `Hom(X, X₂) = 0` gives `Hom(X, X₁) = 0`.
* `Ext.subsingleton_X₁_of_X₃`: `Extⁿ(X₂, Y) = 0` and `Extⁿ⁺¹(X₃, Y) = 0` give `Extⁿ(X₁, Y) = 0`.
* `Ext.subsingleton_X₃_succ`: `Extⁿ(X₁, Y) = 0` and `Extⁿ⁺¹(X₂, Y) = 0` give
  `Extⁿ⁺¹(X₃, Y) = 0`.
-/

universe w

open CategoryTheory Abelian Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}
  (hS : S.ShortExact)

include hS in
/-- `Extⁿ(X, X₃) = 0` and `Extⁿ⁺¹(X, X₂) = 0` give `Extⁿ⁺¹(X, X₁) = 0`. -/
theorem subsingleton_X₁_succ (X : C) (n : ℕ) [Subsingleton (Ext X S.X₃ n)]
    [Subsingleton (Ext X S.X₂ (n + 1))] : Subsingleton (Ext X S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) rfl
  rw [Subsingleton.elim y 0, zero_comp]

include hS in
/-- `Hom(X, X₂) = 0` gives `Hom(X, X₁) = 0`, in degree zero of `Ext`. -/
theorem subsingleton_X₁_zero (X : C) [Subsingleton (Ext X S.X₂ 0)] :
    Subsingleton (Ext X S.X₁ 0) := by
  have := hS.mono_f
  refine subsingleton_of_forall_eq 0 fun x => ?_
  apply postcomp_mk₀_injective_of_mono X S.f
  rw [Subsingleton.elim ((mk₀ S.f).postcomp X (add_zero 0) x)
    ((mk₀ S.f).postcomp X (add_zero 0) 0)]

include hS in
/-- `Extⁿ(X₂, Y) = 0` and `Extⁿ⁺¹(X₃, Y) = 0` give `Extⁿ(X₁, Y) = 0`. -/
theorem subsingleton_X₁_of_X₃ (Y : C) (n : ℕ) [Subsingleton (Ext S.X₂ Y n)]
    [Subsingleton (Ext S.X₃ Y (1 + n))] : Subsingleton (Ext S.X₁ Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := contravariant_sequence_exact₁ hS Y x rfl (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, comp_zero]

include hS in
/-- `Extⁿ(X₁, Y) = 0` and `Extⁿ⁺¹(X₂, Y) = 0` give `Extⁿ⁺¹(X₃, Y) = 0`. -/
theorem subsingleton_X₃_succ (Y : C) (n : ℕ) [Subsingleton (Ext S.X₁ Y n)]
    [Subsingleton (Ext S.X₂ Y (1 + n))] : Subsingleton (Ext S.X₃ Y (1 + n)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := contravariant_sequence_exact₃ hS Y x (Subsingleton.elim _ _) rfl
  rw [Subsingleton.elim y 0, comp_zero]

end CategoryTheory.Abelian.Ext
