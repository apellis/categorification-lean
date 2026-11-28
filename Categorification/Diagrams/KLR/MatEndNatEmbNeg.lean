/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndNatEmb

/-!
# The diagonal matrix of a natural endomorphism is additive in it

`MatEnd.natEmb_neg`: the diagonal matrix (`MatEnd.natEmb`) of `-α₀` is minus that of `α₀`. With
the repaired Webster Lemma 4.29 (arXiv:1309.3796v3) this identifies the image of the crossing
`appendedCross` (the action of `-ψ`) with the diagonal matrix of minus the completed crossing.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong

namespace MatEnd

universe v w

variable {C : Type*} [Category.{v} C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))

omit [DecidableEq ι] in
include he in
/-- The diagonal matrix of `-α₀` is minus that of `α₀`. -/
theorem natEmb_neg (α₀ : F ⟶ F) : natEmb F h (-α₀) = -natEmb F h α₀ := by
  funext a b
  change _ = -(natEmb F h α₀ a b)
  by_cases hab : a = b
  · subst hab
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [natEmb_apply_emb F he h, natEmb_apply_emb F he h,
        natEntry, natEntry, NatTrans.app_neg, Preadditive.neg_comp, Preadditive.comp_neg]
    · push Not at ha
      rw [natEmb_apply_of_not F h _ ha,
        natEmb_apply_of_not F h _ ha, neg_zero]
  · rw [natEmb_apply_of_ne F h _ hab, natEmb_apply_of_ne F h _ hab,
      neg_zero]

end MatEnd

end Categorification.KLR.Diagram
