/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR

universe u v w

attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ)

local notation "μ" => stendhalWeight 2 ν

private theorem twoRed_adjacentBlockRoot_eq_zero_of_not_violated
    (s : Seq μ) (hs : ¬ IsViolated s) : adjacentBlockRoot 0 1 s = 0 := by
  have hpos : 0 < Multiset.card μ := by
    obtain ⟨j, _⟩ := exists_lbl_eq_inr s 0
    exact Nat.zero_lt_of_lt j.isLt
  rcases hc : s.lbl ⟨0, hpos⟩ with c | c
  · exact (hs ⟨hpos, by rw [hc]; rfl⟩).elim
  · funext r i
    have hr : r = (0 : Fin 2) ∨ r = 1 := by fin_cases r <;> decide
    have hh : c ∈ ({0, 1} : Finset (Fin 2)) := by fin_cases c <;> decide
    have hempty : (Finset.univ.filter fun x : Fin (Multiset.card μ) =>
      s.lbl x = .inl i ∧ ∀ y r, r ∈ ({0, 1} : Finset (Fin 2)) →
        s.lbl y = .inr r → x < y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      exact (Nat.not_lt_zero x.val) (hx.2 ⟨0, hpos⟩ c hh hc)
    simp only [adjacentBlockRoot, hr, ↓reduceIte, blockBlackCount, hempty, Finset.card_empty,
      Pi.zero_apply]

/-- With one retained red block, every higher cut is globally violated. -/
theorem blockUpperIdeal_twoRed_eq_bot (α : Fin 2 → I → ℕ) (κ : List (Fin 2)) :
    blockUpperIdeal k Q Λ ν 0 1 α κ = ⊥ := by
  unfold blockUpperIdeal
  refine le_antisymm (TwoSidedIdeal.span_le.mpr ?_) bot_le
  rintro _ ⟨t, _, ht, rfl⟩
  have hv : IsViolated t := by
    by_contra h
    rw [twoRed_adjacentBlockRoot_eq_zero_of_not_violated t h] at ht
    exact not_lt_of_ge (fun a i => Nat.zero_le _) ht
  rw [AlgHom.comp_apply, violMk_e hv]
  exact (⊥ : TwoSidedIdeal _).zero_mem

/-- With only the paired reds, the kernel of the partial-standard
presentation vanishes. -/
theorem blockLoadingKernel_twoRed_eq_bot (s : Seq μ) :
    blockLoadingKernel Q Λ s 0 1 = ⊥ := by
  ext x
  change x.val.val ∈ blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 s) (redWord s) ↔ _
  rw [blockUpperIdeal_twoRed_eq_bot, Submodule.mem_bot]
  constructor
  · intro hx
    rw [TwoSidedIdeal.mem_bot] at hx
    exact Subtype.ext (Subtype.ext hx)
  · rintro rfl
    exact (⊥ : TwoSidedIdeal _).zero_mem

local notation "C" => fun order : List (Fin 2) =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν order)

/-- The initial one-block case of Webster's (6.21) for arbitrary black
content. The braid of the two-red partial standard is concentrated in
degree zero. -/
theorem blockPartialStandard_twoRed_braid_homology_vanish (s : KLR.Seq μ) (κ : List (Fin 2))
    [sourceDerived : HasDerivedCategory.{w, max u v} (C (redWord s))ᵐᵒᵖ]
    [targetDerived : HasDerivedCategory.{w, max u v} (C κ)ᵐᵒᵖ] (n : ℤ) (hn : n ≠ 0) :
    let F := @braidingFunctor.{w, u, v} I _ k _ 2 Q Λ ν (redWord s) κ sourceDerived targetDerived
    let H := @DG.DerivedCategory.homologyFunctor.{w, max u v, max u v, 0}
      (C κ)ᵐᵒᵖ _ _ _ targetDerived ℤ _ _ _ n
    let q := @DG.DerivedCategory.Q.{w, max u v, max u v} (C (redWord s))ᵐᵒᵖ _ _ _ sourceDerived
    IsZero (H.obj (F.obj (q.obj
      ((degreeZeroModuleFunctor (C (redWord s))ᵐᵒᵖ).obj (blockLoadingShortComplex Q Λ s 0 1).X₃)))) :=
  @blockPartialStandard_braid_homology_vanish_of_bot.{w, u, v} I k _ _ 2 ν Q Λ s 0 1 κ
    sourceDerived targetDerived (blockLoadingKernel_twoRed_eq_bot Q Λ s) n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
