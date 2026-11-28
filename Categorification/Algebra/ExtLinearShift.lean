/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Categorification.Algebra.ExtVanishingShift

/-!
# Dimension shifting for `Ext`, linearly

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` in an `R`-linear abelian category and an
object `Y` with `Extⁿ(X₂, Y) = Ext^{1+n}(X₂, Y) = 0`, the connecting map is an `R`-linear
isomorphism `Extⁿ(X₁, Y) ≅ Ext^{1+n}(X₃, Y)`. Background for B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, §7.1, proofs of Proposition 7.8 and
Corollary 7.9.

## Main results

* `Ext.linearEquivOfShortExact`: the connecting isomorphism.
* `Ext.linearEquivOfIso`: `Ext` is invariant under isomorphism in the first variable.
* `Ext.exists_linearEquiv_of_chain`: along spliced short exact sequences
  `0 → K_{n+1} → M_n → K_n → 0` with `Ext^*(M_n, Y) = 0` for `n < N`,
  `Extⁱ(K_n, Y) ≅ Ext^{n+i}(K_0, Y)` for `n ≤ N`, and `Extⁱ(K_0, Y) = 0` for `i < N`.
-/

universe w

open CategoryTheory Abelian Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] (R : Type*) [CommRing R]
  [Linear R C]

/-- `Ext` is invariant under isomorphism in the first variable, `R`-linearly. -/
noncomputable def linearEquivOfIso {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ) :
    Ext.{w} X' Y n ≃ₗ[R] Ext.{w} X Y n where
  toFun x := (mk₀ e.hom).comp x (zero_add n)
  invFun x := (mk₀ e.inv).comp x (zero_add n)
  map_add' x y := by simp
  map_smul' c x := by simp
  left_inv x := by
    simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.inv_hom_id, mk₀_id_comp]
  right_inv x := by
    simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.hom_inv_id, mk₀_id_comp]

variable {S : ShortComplex C} (hS : S.ShortExact)

include hS in
/-- **Dimension shifting**: `Extⁿ(X₁, Y) ≅ Ext^{1+n}(X₃, Y)`, `R`-linearly, when
`Extⁿ(X₂, Y)` and `Ext^{1+n}(X₂, Y)` vanish. -/
noncomputable def linearEquivOfShortExact (Y : C) (n : ℕ) [Subsingleton (Ext.{w} S.X₂ Y n)]
    [Subsingleton (Ext.{w} S.X₂ Y (1 + n))] : Ext.{w} S.X₁ Y n ≃ₗ[R] Ext.{w} S.X₃ Y (1 + n) :=
  LinearEquiv.ofBijective (precompOfLinear hS.extClass R Y rfl) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨x₂, rfl⟩ := contravariant_sequence_exact₁ hS Y x rfl hx
    rw [Subsingleton.elim x₂ 0, comp_zero], fun x₃ => by
    obtain ⟨x₁, hx₁⟩ := contravariant_sequence_exact₃ hS Y x₃ (Subsingleton.elim _ _) rfl
    exact ⟨x₁, hx₁⟩⟩

include hS in
/-- **Dimension shifting in the second variable**: `Extⁿ(X, X₃) ≅ Ext^{n+1}(X, X₁)`,
`R`-linearly, when `Extⁿ(X, X₂)` and `Ext^{n+1}(X, X₂)` vanish. -/
noncomputable def linearEquivOfShortExactRight (X : C) (n : ℕ) [Subsingleton (Ext.{w} X S.X₂ n)]
    [Subsingleton (Ext.{w} X S.X₂ (n + 1))] : Ext.{w} X S.X₃ n ≃ₗ[R] Ext.{w} X S.X₁ (n + 1) :=
  LinearEquiv.ofBijective (postcompOfLinear hS.extClass R X rfl) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨x₂, rfl⟩ := covariant_sequence_exact₃ X hS x rfl hx
    rw [Subsingleton.elim x₂ 0, zero_comp], fun x₁ => by
    obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ X hS x₁ (Subsingleton.elim _ _) rfl
    exact ⟨x₃, hx₃⟩⟩

/-- `Ext` is invariant under isomorphism in the second variable, `R`-linearly. -/
noncomputable def linearEquivOfIsoRight (X : C) {Y Y' : C} (e : Y ≅ Y') (n : ℕ) :
    Ext.{w} X Y n ≃ₗ[R] Ext.{w} X Y' n where
  toFun x := x.comp (mk₀ e.hom) (add_zero n)
  invFun x := x.comp (mk₀ e.inv) (add_zero n)
  map_add' x y := by simp
  map_smul' c x := by simp
  left_inv x := by
    simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, e.hom_inv_id, comp_mk₀_id]
  right_inv x := by
    simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, e.inv_hom_id, comp_mk₀_id]

omit [HasExt.{w} C] in
/-- **Dimension shifting along a resolution.** Let `S n` be short exact sequences
`0 → K_{n+1} → M_n → K_n → 0` (with `K_{n+1}` the cokernel term of `S (n + 1)`) and let
`Extⁱ(M_n, Y) = 0` for all `i` and `n < N`. Then `Extⁱ(K_n, Y) ≅ Ext^{n+i}(K_0, Y)` for
`n ≤ N`, and `Extⁱ(K_0, Y) = 0` for `i < N`. -/
theorem exists_linearEquiv_of_chain [HasExt.{w} C] (S : ℕ → ShortComplex C)
    (hs : ∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) (he : ∀ n, (S n).ShortExact) (Y : C)
    (N : ℕ) (hY : ∀ n < N, ∀ i, Subsingleton (Ext.{w} (S n).X₂ Y i)) :
    (∀ n ≤ N, ∀ i, Nonempty (Ext.{w} (S n).X₃ Y i ≃ₗ[R] Ext.{w} (S 0).X₃ Y (n + i))) ∧
      ∀ i < N, Subsingleton (Ext.{w} (S 0).X₃ Y i) := by
  have key : ∀ n ≤ N, ∀ i, Nonempty (Ext.{w} (S n).X₃ Y i ≃ₗ[R] Ext.{w} (S 0).X₃ Y (n + i)) := by
    intro n
    induction n with
    | zero => exact fun _ i => ⟨by rw [zero_add]⟩
    | succ n ih =>
      intro hn i
      have := hY n (by omega) i
      have := hY n (by omega) (1 + i)
      obtain ⟨e⟩ := hs n
      obtain ⟨f⟩ := ih (by omega) (1 + i)
      rw [show n + 1 + i = n + (1 + i) by omega]
      exact ⟨(linearEquivOfIso R e Y i).symm.trans
        ((linearEquivOfShortExact R (he n) Y i).trans f)⟩
  refine ⟨key, fun i hi => ?_⟩
  obtain ⟨f⟩ := key i hi.le 0
  have := hY i hi 0
  have := subsingleton_X₃_zero (he i) Y
  exact f.symm.toEquiv.subsingleton

end CategoryTheory.Abelian.Ext
