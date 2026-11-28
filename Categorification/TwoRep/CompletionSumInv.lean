/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.TwoRep.CompletionSumDecomp
import Categorification.TwoRep.RouqSl2

/-!
# Explicit inverses pass to additive idempotent completions

Rouquier's invertibility conditions (Brundan, arXiv:1501.00350v1, (1.8), (1.9)) are recorded by
explicit inverse components (`SumInvTo`, `SumInvFrom`). For natural transformations between
additive functors, such data pass to the induced natural transformations on additive idempotent
completions (`SumInvTo.completion`, `SumInvFrom.completion`), since `completionMap₂` is
functorial and additive (`completionMap₂_comp`, `completionMap₂_add`, ...). The negation
lemma `completionMap₂_neg` is included.
-/

namespace Categorification.TwoRep

noncomputable section

open CategoryTheory CategoryTheory.Idempotents

universe v u₁ u₂

variable {A : Type u₁} [Category.{v} A] [Preadditive A] {B : Type u₂} [Category.{v} B]
  [Preadditive B]

theorem completionMap₂_neg {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    completionMap₂ (-α) = -completionMap₂ α := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← completionMap₂_add, neg_add_cancel, completionMap₂_zero]

variable {X Y Z : A ⥤ B} [X.Additive] [Y.Additive] [Z.Additive] {n : ℕ}

/-- The image of an explicit inverse on additive idempotent completions. -/
def SumInvTo.completion {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} (S : SumInvTo f g n) :
    SumInvTo (completionMap₂ f) (fun m => completionMap₂ (g m)) n where
  f' := completionMap₂ S.f'
  g' m := completionMap₂ (S.g' m)
  total := by
    rw [← completionMap₂_id, ← S.total, completionMap₂_add, completionMap₂_comp,
      completionMap₂_sum]
    simp only [completionMap₂_comp]
  ff := by rw [← completionMap₂_comp, S.ff, completionMap₂_id]
  fg m hm := by rw [← completionMap₂_comp, S.fg m hm, completionMap₂_zero]
  gf m hm := by rw [← completionMap₂_comp, S.gf m hm, completionMap₂_zero]
  gg m m' hm hm' := by
    rw [← completionMap₂_comp, S.gg m m' hm hm']
    split_ifs
    · exact completionMap₂_id _
    · exact completionMap₂_zero

/-- The image of an explicit inverse on additive idempotent completions. -/
def SumInvFrom.completion {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} (S : SumInvFrom f g n) :
    SumInvFrom (completionMap₂ f) (fun m => completionMap₂ (g m)) n where
  f' := completionMap₂ S.f'
  g' m := completionMap₂ (S.g' m)
  total := by
    rw [← completionMap₂_id, ← S.total, completionMap₂_add, completionMap₂_comp,
      completionMap₂_sum]
    simp only [completionMap₂_comp]
  ff := by rw [← completionMap₂_comp, S.ff, completionMap₂_id]
  fg m hm := by rw [← completionMap₂_comp, S.fg m hm, completionMap₂_zero]
  gf m hm := by rw [← completionMap₂_comp, S.gf m hm, completionMap₂_zero]
  gg m m' hm hm' := by
    rw [← completionMap₂_comp, S.gg m m' hm hm']
    split_ifs
    · exact completionMap₂_id _
    · exact completionMap₂_zero

end

end Categorification.TwoRep
