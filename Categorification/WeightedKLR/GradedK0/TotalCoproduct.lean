/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.CoproductK0
import Categorification.WeightedKLR.TensorSimple
import Categorification.WeightedKLR.GradedK0.Algebra
import Mathlib.Data.Finsupp.Antidiagonal

/-!
# The total restriction coproduct

Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19. On a homogeneous class the
coproduct is the sum of restrictions over the decompositions of its weight.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ) (hD : Γ.Dagger) (hS : Γ.Standing)
  (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
  [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)]

local notation "L" => LaurentPolynomial ℤ

/-- Restriction to a pair of weights, using their sum to identify the source. -/
def splitCoproduct {ν : I →₀ ℕ} (a b : I →₀ ℕ) (h : a + b = ν) :
    G.K0fam ν →ₗ[L] G.K0fam a ⊗[L] G.K0fam b := by
  subst ν
  exact G.coproductK0 hD (fun e he => (hne e he).elim) hS a b
    (G.tensorK0Hyp hD hS hne hl a b)

/-- The restriction coproduct on the direct sum in Webster's Theorem 2.19. -/
def totalCoproduct : G.K0W →ₗ[L] G.K0W ⊗[L] G.K0W :=
  DirectSum.toModule L _ _ fun ν =>
    ∑ s ∈ (Finset.HasAntidiagonal.antidiagonal ν).attach,
      TensorProduct.map (DirectSum.lof L _ G.K0fam s.1.1)
        (DirectSum.lof L _ G.K0fam s.1.2) ∘ₗ
        G.splitCoproduct hD hS hne hl s.1.1 s.1.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp s.2)

/-- On a homogeneous class the total coproduct sums the finitely many restrictions. -/
theorem totalCoproduct_lof (ν : I →₀ ℕ) (x : G.K0fam ν) :
    G.totalCoproduct hD hS hne hl (DirectSum.lof L _ G.K0fam ν x) =
      ∑ s ∈ (Finset.HasAntidiagonal.antidiagonal ν).attach,
        TensorProduct.map (DirectSum.lof L _ G.K0fam s.1.1)
          (DirectSum.lof L _ G.K0fam s.1.2)
          (G.splitCoproduct hD hS hne hl s.1.1 s.1.2
            (Finset.HasAntidiagonal.mem_antidiagonal.mp s.2) x) := by
  simp only [totalCoproduct, DirectSum.toModule_lof, LinearMap.sum_apply, LinearMap.comp_apply]

/-- Projecting the total coproduct to a pair of weights recovers its restriction map. -/
theorem component_totalCoproduct_lof (a b : I →₀ ℕ) (x : G.K0fam (a + b)) :
    TensorProduct.map (DirectSum.component L _ G.K0fam a)
      (DirectSum.component L _ G.K0fam b)
      (G.totalCoproduct hD hS hne hl (DirectSum.lof L _ G.K0fam (a + b) x)) =
        G.splitCoproduct hD hS hne hl a b rfl x := by
  classical
  rw [totalCoproduct_lof, map_sum]
  let ab : ↥(Finset.HasAntidiagonal.antidiagonal (a + b)) :=
    ⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  rw [Finset.sum_eq_single ab]
  · simp only [ab, TensorProduct.map_map,
      DirectSum.component_comp_lof_same, TensorProduct.map_id, LinearMap.id_apply]
  · intro s _ hs
    rcases s with ⟨⟨c, d⟩, hcd⟩
    have hne' : c ≠ a ∨ d ≠ b := by
      by_contra! h
      exact hs (Subtype.ext (Prod.ext h.1 h.2))
    rcases hne' with hc | hd
    · simp [TensorProduct.map_map, DirectSum.component_comp_lof, hc]
    · simp [TensorProduct.map_map, DirectSum.component_comp_lof, hd]
  · simp

/-- The component of the total coproduct at `(a,b)` depends only on the input
of weight `a+b`. -/
theorem component_totalCoproduct (a b : I →₀ ℕ) :
    TensorProduct.map (DirectSum.component L _ G.K0fam a)
      (DirectSum.component L _ G.K0fam b) ∘ₗ G.totalCoproduct hD hS hne hl =
      G.splitCoproduct hD hS hne hl a b rfl ∘ₗ DirectSum.component L _ G.K0fam (a + b) := by
  classical
  apply DirectSum.linearMap_ext
  intro ν
  ext x
  by_cases h : ν = a + b
  · subst ν
    simp only [LinearMap.comp_apply, DirectSum.component.lof_self, component_totalCoproduct_lof]
  · simp only [LinearMap.comp_apply, DirectSum.component.of, dite_eq_right h, map_zero,
      totalCoproduct_lof, map_sum]
    apply Finset.sum_eq_zero
    intro s _
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp s.2
    have hne' : s.1.1 ≠ a ∨ s.1.2 ≠ b := by
      by_contra! he
      exact h (hs.symm.trans (congrArg₂ (· + ·) he.1 he.2))
    rcases hne' with hc | hd
    · simp [TensorProduct.map_map, DirectSum.component_comp_lof, hc]
    · simp [TensorProduct.map_map, DirectSum.component_comp_lof, hd]

end Categorification.WeightedKLR.GradingDatum
