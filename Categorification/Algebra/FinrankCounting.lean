/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting dimensions of the subquotients of a family of submodules

The dimension argument of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.21. Let `N φ` be submodules of a finite-dimensional
module `M`, indexed by a finite set with a strict order `≺`, which together span a submodule
`P`. Put `P_{>φ} = ⨆_{φ ≺ φ'} N φ'` and `P_{≥φ} = P_{>φ} + N φ`. If `dim P_{≥φ}/P_{>φ} ≤ d φ`
for every `φ` and `∑ d φ = dim P`, then `dim P_{≥φ}/P_{>φ} = d φ` for every `φ`.

The submodules may be submodules over a `k`-algebra `R`; dimensions are taken over `k`.

## Main results

* `Submodule.finrankK_iSup_le`, `Submodule.layerRank_eq_of_sum_eq`.
-/

namespace Submodule

open Module

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R] [AddCommGroup M] [Module k M]
  [Module R M] [IsScalarTower k R M] [FiniteDimensional k M]

omit [FiniteDimensional k M] in
theorem restrictScalars_sup' (s t : Submodule R M) :
    (s ⊔ t).restrictScalars k = s.restrictScalars k ⊔ t.restrictScalars k := by
  ext x
  simp only [restrictScalars_mem, mem_sup]

/-- The dimension over `k` of a submodule over `R`. -/
noncomputable abbrev finrankK (k : Type*) [Field k] [Algebra k R] [Module k M]
    [IsScalarTower k R M] (N : Submodule R M) : ℕ :=
  finrank k (N.restrictScalars k)

omit [FiniteDimensional k M] in
theorem finrankK_le_of_le [FiniteDimensional k M] {N N' : Submodule R M} (h : N ≤ N') :
    finrankK k N ≤ finrankK k N' :=
  Submodule.finrank_mono (restrictScalars_mono k h)

theorem finrankK_sup_add_inf (N N' : Submodule R M) :
    finrankK k (N ⊔ N') + finrankK k (N ⊓ N') = finrankK k N + finrankK k N' := by
  unfold finrankK
  rw [restrictScalars_sup', restrictScalars_inf]
  exact Submodule.finrank_sup_add_finrank_inf_eq _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (rel : ι → ι → Prop)
  (N : ι → Submodule R M)

/-- `P_{>φ}`: the sum of the `N φ'` with `φ ≺ φ'`. -/
def above (φ : ι) : Submodule R M := ⨆ (φ' : ι) (_ : rel φ φ'), N φ'

/-- The dimension of `P_{≥φ}/P_{>φ}`. -/
noncomputable def layerRank (φ : ι) : ℕ :=
  finrankK k (N φ ⊔ above rel N φ) - finrankK k (above rel N φ)

/-- The sum over an upward closed set has dimension at most the sum of the layer dimensions. -/
theorem finrankK_iSup_le (hirr : ∀ φ, ¬ rel φ φ) (htr : ∀ a b c, rel a b → rel b c → rel a c) :
    ∀ S : Finset ι, (∀ φ ∈ S, ∀ φ', rel φ φ' → φ' ∈ S) →
      finrankK k (⨆ φ ∈ S, N φ) ≤ ∑ φ ∈ S, layerRank (k := k) rel N φ := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hup
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [finrankK]
    -- a minimal element: the most elements above it
    let h : ι → ℕ := fun φ => (Finset.univ.filter fun φ' => rel φ φ').card
    obtain ⟨φ, hφ, hmax⟩ := S.exists_max_image h hne
    have hmin : ∀ ψ ∈ S, ¬ rel ψ φ := by
      intro ψ hψ hrel
      have hlt : h φ < h ψ := by
        refine Finset.card_lt_card ⟨fun a ha => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact htr _ _ _ hrel ha
        · have := hsub (show φ ∈ Finset.univ.filter fun φ' => rel ψ φ' by simp [hrel])
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact hirr φ this
      exact absurd (hmax ψ hψ) (not_le.2 hlt)
    set S' := S.erase φ
    have hS' : S' ⊂ S := Finset.erase_ssubset hφ
    have hup' : ∀ ψ ∈ S', ∀ ψ', rel ψ ψ' → ψ' ∈ S' := by
      intro ψ hψ ψ' hrel
      refine Finset.mem_erase.2 ⟨?_, hup ψ (Finset.mem_of_mem_erase hψ) ψ' hrel⟩
      rintro rfl
      exact hmin ψ (Finset.mem_of_mem_erase hψ) hrel
    have hIH := ih S' hS' hup'
    have hD : (⨆ ψ ∈ S, N ψ) = (⨆ ψ ∈ S', N ψ) ⊔ N φ := by
      rw [← Finset.insert_erase hφ, Finset.iSup_insert, sup_comm]
    have habove : above rel N φ ≤ ⨆ ψ ∈ S', N ψ := by
      refine iSup₂_le fun ψ hrel => ?_
      exact le_biSup N (Finset.mem_erase.2 ⟨fun h => hirr φ (h ▸ hrel), hup φ hφ ψ hrel⟩)
    have hinf : above rel N φ ⊓ N φ ≤ (⨆ ψ ∈ S', N ψ) ⊓ N φ := inf_le_inf_right _ habove
    have e₁ := finrankK_sup_add_inf (k := k) (⨆ ψ ∈ S', N ψ) (N φ)
    have e₂ := finrankK_sup_add_inf (k := k) (above rel N φ) (N φ)
    have e₃ := finrankK_le_of_le (k := k) hinf
    have hl : layerRank (k := k) rel N φ =
        finrankK k (above rel N φ ⊔ N φ) - finrankK k (above rel N φ) := by
      unfold layerRank
      rw [sup_comm]
    rw [hD, ← Finset.add_sum_erase S _ hφ, hl, show S.erase φ = S' from rfl]
    omega

/-- **Equality in the dimension count** (Webster, arXiv:1309.3796v3, proof of Proposition
5.21): if the `N φ` span `P`, each `P_{≥φ}/P_{>φ}` has dimension at most `d φ`, and the `d φ` add
up to the dimension of `P`, then `P_{≥φ}/P_{>φ}` has dimension exactly `d φ`. -/
theorem layerRank_eq_of_sum_eq (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) {P : Submodule R M} (hspan : (⨆ φ, N φ) = P)
    (d : ι → ℕ) (hle : ∀ φ, layerRank (k := k) rel N φ ≤ d φ)
    (hsum : ∑ φ, d φ = finrankK k P) (φ : ι) :
    layerRank (k := k) rel N φ = d φ := by
  classical
  have h := finrankK_iSup_le (k := k) rel N hirr htr Finset.univ (by simp)
  simp only [Finset.mem_univ, iSup_pos, hspan] at h
  rw [← hsum] at h
  exact (Finset.sum_eq_sum_iff_of_le fun φ _ => hle φ).1
    (le_antisymm (Finset.sum_le_sum fun φ _ => hle φ) h) φ (Finset.mem_univ _)

end Submodule
