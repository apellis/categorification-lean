/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.TotalCoproduct
import Categorification.WeightedKLR.GradedK0.Coassociativity
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Coassociativity of the total coproduct

Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19. The projection to each triple of
weights identifies total coassociativity with the coassociativity of the
graded restriction components.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded
open scoped TensorProduct

section Projections

variable {L : Type*} [CommSemiring L]
  {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  (M : ι → Type*) (N : κ → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ j, AddCommMonoid (N j)]
  [∀ i, Module L (M i)] [∀ j, Module L (N j)]

private theorem component_tensorDirectSum (i : ι) (j : κ) :
    DirectSum.component L _ (fun p : ι × κ => M p.1 ⊗[L] N p.2) (i, j) ∘ₗ
      (TensorProduct.directSum L L M N).toLinearMap =
    TensorProduct.map (DirectSum.component L _ M i) (DirectSum.component L _ N j) := by
  ext i' x j' y : 5
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      simp
    · simp [DirectSum.component.of, hj]
  · simp [DirectSum.component.of, hi]

private theorem component_tensorDirectSumTriple {η : Type*} [DecidableEq η]
    (Q : η → Type*) [∀ a, AddCommMonoid (Q a)] [∀ a, Module L (Q a)]
    {x y : DirectSum η Q ⊗[L] (DirectSum ι M ⊗[L] DirectSum κ N)}
    (h : ∀ (a : η) (i : ι) (j : κ), TensorProduct.map (DirectSum.component L _ Q a)
        (TensorProduct.map (DirectSum.component L _ M i) (DirectSum.component L _ N j)) x =
      TensorProduct.map (DirectSum.component L _ Q a)
        (TensorProduct.map (DirectSum.component L _ M i) (DirectSum.component L _ N j)) y) :
    x = y := by
  let F := (TensorProduct.directSum L L M N).lTensor (DirectSum η Q)
  apply F.injective
  apply (TensorProduct.directSum L L Q (fun p : ι × κ => M p.1 ⊗[L] N p.2)).injective
  apply DFinsupp.ext
  rintro ⟨a, i, j⟩
  change (DirectSum.component L _ _ (a, i, j) ∘ₗ
    (TensorProduct.directSum L L Q (fun p : ι × κ => M p.1 ⊗[L] N p.2)).toLinearMap) (F x) =
    (DirectSum.component L _ _ (a, i, j) ∘ₗ
      (TensorProduct.directSum L L Q (fun p : ι × κ => M p.1 ⊗[L] N p.2)).toLinearMap) (F y)
  rw [component_tensorDirectSum Q (fun p : ι × κ => M p.1 ⊗[L] N p.2) a (i, j)]
  change TensorProduct.map (DirectSum.component L _ Q a)
    (DirectSum.component L _ _ (i, j))
    (TensorProduct.map LinearMap.id (TensorProduct.directSum L L M N).toLinearMap x) =
    TensorProduct.map (DirectSum.component L _ Q a)
      (DirectSum.component L _ _ (i, j))
      (TensorProduct.map LinearMap.id (TensorProduct.directSum L L M N).toLinearMap y)
  rw [TensorProduct.map_map, TensorProduct.map_map, LinearMap.comp_id, component_tensorDirectSum M N i j]
  exact h a i j

end Projections

section Coproduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ) (hD : Γ.Dagger) (hS : Γ.Standing)
  (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
  [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)]

local notation "L" => LaurentPolynomial ℤ

omit [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)] in
private theorem component_cast {μ ν : I →₀ ℕ} (h : μ = ν) (x : G.K0W) :
    DirectSum.component L _ G.K0fam ν x =
      G.K0cast h (DirectSum.component L _ G.K0fam μ x) := by
  subst h
  rfl

private theorem totalCoproduct_coassoc_of_components
    (hcoassoc : ∀ a b c (x : G.K0fam (a + b + c)),
      TensorProduct.assoc L _ _ _
        (TensorProduct.map (G.splitCoproduct hD hS hne hl a b rfl) LinearMap.id
          (G.splitCoproduct hD hS hne hl (a + b) c rfl x)) =
        TensorProduct.map LinearMap.id (G.splitCoproduct hD hS hne hl b c rfl)
          (G.splitCoproduct hD hS hne hl a (b + c) rfl (G.K0cast (add_assoc a b c) x))) :
    (TensorProduct.assoc L G.K0W G.K0W G.K0W).toLinearMap ∘ₗ
        (G.totalCoproduct hD hS hne hl).rTensor G.K0W ∘ₗ G.totalCoproduct hD hS hne hl =
      (G.totalCoproduct hD hS hne hl).lTensor G.K0W ∘ₗ G.totalCoproduct hD hS hne hl := by
  apply LinearMap.ext
  intro x
  apply component_tensorDirectSumTriple G.K0fam G.K0fam G.K0fam
  intro a b c
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_def, LinearMap.lTensor_def,
    TensorProduct.map_map_assoc, TensorProduct.map_map, LinearMap.comp_id, component_totalCoproduct]
  rw [← LinearMap.rTensor_map G.K0W (G.splitCoproduct hD hS hne hl a b rfl),
    ← LinearMap.lTensor_map G.K0W (G.splitCoproduct hD hS hne hl b c rfl)]
  simp only [LinearMap.rTensor_def, LinearMap.lTensor_def]
  rw [show TensorProduct.map (DirectSum.component L _ G.K0fam (a + b))
      (DirectSum.component L _ G.K0fam c) (G.totalCoproduct hD hS hne hl x) =
      G.splitCoproduct hD hS hne hl (a + b) c rfl (DirectSum.component L _ G.K0fam (a + b + c) x) from
    LinearMap.congr_fun (G.component_totalCoproduct hD hS hne hl (a + b) c) x]
  rw [show TensorProduct.map (DirectSum.component L _ G.K0fam a)
      (DirectSum.component L _ G.K0fam (b + c)) (G.totalCoproduct hD hS hne hl x) =
      G.splitCoproduct hD hS hne hl a (b + c) rfl (DirectSum.component L _ G.K0fam (a + (b + c)) x) from
    LinearMap.congr_fun (G.component_totalCoproduct hD hS hne hl a (b + c)) x]
  rw [G.component_cast (add_assoc a b c) x]
  exact hcoassoc a b c (DirectSum.component L _ G.K0fam (a + b + c) x)

/-- The restriction coproduct on the graded Grothendieck algebra is coassociative
(Webster, arXiv:1209.2463v4, §2.4, Proposition 2.18 and Theorem 2.19). -/
theorem totalCoproduct_coassoc :
    (TensorProduct.assoc L G.K0W G.K0W G.K0W).toLinearMap ∘ₗ
        (G.totalCoproduct hD hS hne hl).rTensor G.K0W ∘ₗ G.totalCoproduct hD hS hne hl =
      (G.totalCoproduct hD hS hne hl).lTensor G.K0W ∘ₗ G.totalCoproduct hD hS hne hl := by
  apply G.totalCoproduct_coassoc_of_components hD hS hne hl
  intro a b c x
  exact G.coproductK0_coassoc_of_tensorK0Hyp hD (fun e he => (hne e he).elim) hS a b c
    (G.tensorK0Hyp hD hS hne hl a b) (G.tensorK0Hyp hD hS hne hl b c)
    (G.tensorK0Hyp hD hS hne hl (a + b) c) (G.tensorK0Hyp hD hS hne hl a (b + c)) x

end Coproduct

end Categorification.WeightedKLR.GradingDatum
