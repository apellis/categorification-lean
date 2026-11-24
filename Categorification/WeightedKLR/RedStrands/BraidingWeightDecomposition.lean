/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentRedSwapNormalization

/-!
# Direct sum decomposition of normalized braid coefficients

Sandwiching by degree-zero elements preserves the ambient homogeneous
pieces. Their direct sum on the rectangular corner reindexes to the
Webster degree coset for an adjacent swap.
-/

noncomputable section

namespace Categorification

open DirectSum

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
  (G : ℤ → Submodule k A) [GradedAlgebra G] {e e' : A}

private def cornerSubmodule (e e' : A) : Submodule k A where
  carrier := cornerBimodule e e'
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    change e * x = x ∧ x * e' = x at hx
    change e * (c • x) = c • x ∧ (c • x) * e' = c • x
    rw [mul_smul_comm, smul_mul_assoc, hx.1, hx.2]
    exact ⟨rfl, rfl⟩

/-- The rectangular corner cut out by two homogeneous degree-zero elements
decomposes as the direct sum of its homogeneous pieces. -/
theorem diagramCornerWeight_isInternal (he0 : e ∈ G 0) (he'0 : e' ∈ G 0) :
    IsInternal (diagramCornerWeight (e := e) (e' := e') G) := by
  let U := cornerSubmodule (k := k) e e'
  have hU : IsInternal (Graded.comap G U.subtype) := by
    apply Graded.isInternal_comap _ _ Subtype.val_injective
    intro x j
    have hx := mem_cornerBimodule.mp x.property
    refine ⟨⟨(decompose G x.val j : A), ?_⟩, rfl⟩
    change _ * (decompose G x.val j : A) = _ ∧ (decompose G x.val j : A) * _ = _
    constructor
    · rw [← coe_decompose_mul_of_left_mem_zero G he0, hx.1]
    · rw [← coe_decompose_mul_of_right_mem_zero G he'0, hx.2]
  exact hU

end Categorification

namespace Categorification.Graded

open DirectSum

/-- Extend an additive decomposition along an injective relabelling of its degrees. -/
theorem isInternal_addSubgroup_extend_bot {M ι κ : Type*} [AddCommGroup M]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) (hf : Function.Injective f)
    (A : ι → AddSubgroup M) (hA : IsInternal A) :
    IsInternal (Function.extend f A ⊥) := by
  let B : ι → Submodule ℤ M := fun i => (A i).toIntSubmodule
  have hB : IsInternal B := hA
  have hExt : IsInternal (Function.extend f B ⊥) := by
    refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · intro d
      by_cases hd : ∃ i, f i = d
      · obtain ⟨i, rfl⟩ := hd
        rw [hf.extend_apply]
        apply (hB.submodule_iSupIndep i).mono_right
        refine iSup₂_le fun e he => ?_
        by_cases h' : ∃ j, f j = e
        · obtain ⟨j, rfl⟩ := h'
          rw [hf.extend_apply]
          exact le_iSup₂_of_le j (fun h => he (congrArg f h)) le_rfl
        · rw [Function.extend_apply' _ _ _ h']
          exact bot_le
      · rw [Function.extend_apply' _ _ _ hd]
        exact disjoint_bot_left
    · rw [iSup_extend_bot hf]
      exact hB.submodule_iSup_eq_top
  have hEq : (fun d => (Function.extend f B ⊥ d).toAddSubgroup) = Function.extend f A ⊥ := by
    funext d
    by_cases hd : ∃ i, f i = d
    · obtain ⟨i, rfl⟩ := hd
      rw [hf.extend_apply, hf.extend_apply]
      exact AddSubgroup.toIntSubmodule_toAddSubgroup _
    · rw [Function.extend_apply' _ _ _ hd, Function.extend_apply' _ _ _ hd]
      rfl
  exact hEq ▸ (show IsInternal (fun d => (Function.extend f B ⊥ d).toAddSubgroup) from hExt)

end Categorification.Graded

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR QuantumGroup DirectSum

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {H : Type*} [AddCommGroup H] [Module ℂ H]
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)

omit [DecidableEq I] in
private theorem dotDegree (i : I) : hQ.gradingDatum.degX i = 2 * UDot.di C i :=
  (hQ.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm

/-- The normalized pieces of the actual swap coefficient form a direct sum. -/
theorem adjacentRedSwapWeight_isInternal (L M : List (Fin ℓ)) (r d : Fin ℓ) :
    IsInternal (adjacentRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η L M r d) := by
  let G := stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C) (dotDegree C hQ)
  let f : ℤ → ℂ := fun j => (j : ℂ) + (2 - B (η r) (η d))
  have hf : Function.Injective f := fun _ _ h => Int.cast_injective (add_right_cancel h)
  have hL := redProj_mem_violAuxiliaryGrade (ν := ν) G (L ++ d :: r :: M)
  have hR := redProj_mem_violAuxiliaryGrade (ν := ν) G (L ++ r :: d :: M)
  exact Graded.isInternal_addSubgroup_extend_bot f hf _ (diagramCornerWeight_isInternal _ hL hR)

end Categorification.Stendhal.BraidedStendhalAlgebra
