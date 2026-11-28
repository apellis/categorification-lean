/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForgetDerived

/-!
# Forgetting the weights reflects quasi-isomorphisms

A morphism `φ` of dg modules over the weight category of an internally graded dg ring is a
quasi-isomorphism iff its weight sum `⨁ k, φ⟨k⟩` is (`DG.CatModule.isQuasiIso_iff_weightSumMap`):
the cohomology of the weight sum is the direct sum of the cohomologies of the weights. This is
used to compare the graded braiding functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Definition 6.6, with the ungraded ones.
-/

open CategoryTheory DirectSum

universe v u

namespace DG

namespace CatModule

open WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-- **A morphism whose weight sum is a quasi-isomorphism is a quasi-isomorphism.** -/
theorem IsQuasiIso.of_weightSumMap {M M' : CatModule.{v} (WeightCategory A)} {φ : M ⟶ M'}
    (hφ : (CatModule.weightSumMap φ).IsQuasiIso) : IsQuasiIso φ := by
  intro X n
  obtain ⟨k₀⟩ := X
  let f : ∀ k : ℤ, cohomology (M.obj ⟨k⟩) n →+ cohomology (M'.obj ⟨k⟩) n :=
    fun k => cohomologyMap φ ⟨k⟩ n
  let F : (⨁ k, cohomology (M.obj ⟨k⟩) n) →+ ⨁ k, cohomology (M'.obj ⟨k⟩) n :=
    DFinsupp.mapRange.addMonoidHom f
  have key : ∀ x, cohomology.map (CatModule.weightSumMap φ) n
      (cohomology.fromDirectSum (fun k => M.obj ⟨k⟩) n x) =
        cohomology.fromDirectSum (fun k => M'.obj ⟨k⟩) n (F x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of k y =>
      have hF : F (DirectSum.of _ k y) = DirectSum.of _ k (f k y) :=
        DFinsupp.mapRange_single (hf := fun i => (f i).map_zero)
      rw [hF, cohomology.fromDirectSum_of, cohomology.fromDirectSum_of]
      induction y using cohomology.induction_on with
      | h z =>
        change _ = cohomology.ofSummand (fun k => M'.obj ⟨k⟩) k n
          (cohomologyMap φ ⟨k⟩ n (cohomology.mk _ n z))
        rw [cohomology.ofSummand_mk, cohomology.map_mk, cohomologyMap_mk,
          cohomology.ofSummand_mk]
        congr 1
        exact Subtype.ext (weightSumMap_of φ k z)
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hinj' := cohomology.fromDirectSum_injective (M := fun k => M'.obj ⟨k⟩) n
  have hF : Function.Bijective F := by
    constructor
    · intro x x' h
      apply cohomology.fromDirectSum_injective (M := fun k => M.obj ⟨k⟩) n
      apply (hφ n).1
      rw [key, key, h]
    · intro y
      obtain ⟨x, hx⟩ := ((hφ n).2.comp
        (cohomology.fromDirectSum_surjective (M := fun k => M.obj ⟨k⟩) n))
          (cohomology.fromDirectSum (fun k => M'.obj ⟨k⟩) n y)
      exact ⟨x, hinj' ((key x).symm.trans hx)⟩
  constructor
  · intro y y' h
    have h' : F (DirectSum.of _ k₀ y) = F (DirectSum.of _ k₀ y') := by
      rw [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange.addMonoidHom_apply]
      exact (DFinsupp.mapRange_single (hf := fun i => (f i).map_zero)).trans
        ((congrArg (DirectSum.of _ k₀) h).trans
          (DFinsupp.mapRange_single (hf := fun i => (f i).map_zero)).symm)
    exact DirectSum.of_injective k₀ (hF.1 h')
  · intro z
    obtain ⟨x, hx⟩ := hF.2 (DirectSum.of _ k₀ z)
    refine ⟨x k₀, ?_⟩
    have := congrArg (fun t : ⨁ k, cohomology (M'.obj ⟨k⟩) n => t k₀) hx
    rw [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply, DirectSum.of_eq_same]
      at this
    exact this

/-- A morphism is a quasi-isomorphism iff its weight sum is. -/
theorem isQuasiIso_iff_weightSumMap {M M' : CatModule.{v} (WeightCategory A)} (φ : M ⟶ M') :
    IsQuasiIso φ ↔ (CatModule.weightSumMap φ).IsQuasiIso :=
  ⟨IsQuasiIso.weightSumMap, IsQuasiIso.of_weightSumMap⟩

end CatModule

end DG
