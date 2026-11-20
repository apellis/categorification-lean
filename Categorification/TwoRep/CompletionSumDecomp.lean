/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.TwoRep.CompletionPseudofunctor
import Categorification.Diagrams.KL3.Karoubi

/-!
# Decompositions of functors pass to additive idempotent completions

The natural transformation `completionMap₂ α` induced by `α : F ⟶ G` on additive idempotent
completions is additive in `α` (`completionMap₂_add`, `completionMap₂_zero`,
`completionMap₂_sum`). With `completionMap₂_id` and `completionMap₂_comp`, a decomposition
`F ≅ G ⊕ ⨁_s H_s` by natural transformations (`SumDecomp` in the functor category) gives the
decomposition of the induced functors on completions (`completionSumDecomp`).

This passes the commutation relations of a categorical action, stated on a preadditive
category, to its additive idempotent completion, as used in Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, §5.
-/

namespace Categorification.TwoRep

noncomputable section

open CategoryTheory CategoryTheory.Idempotents

universe v u₁ u₂

variable {A : Type u₁} [Category.{v} A] [Preadditive A] {B : Type u₂} [Category.{v} B]
  [Preadditive B] {F G : A ⥤ B} [F.Additive] [G.Additive]

theorem matNatTrans_add (α β : F ⟶ G) :
    matNatTrans (α + β) = matNatTrans α + matNatTrans β := by
  ext M i j
  revert i j
  intro (i : M.ι) (j : M.ι)
  change F.map ((𝟙 M : M ⟶ M) i j) ≫ (α + β).app (M.X j) =
    F.map ((𝟙 M : M ⟶ M) i j) ≫ α.app (M.X j) + F.map ((𝟙 M : M ⟶ M) i j) ≫ β.app (M.X j)
  rw [NatTrans.app_add, Preadditive.comp_add]

theorem completionMap₂_add (α β : F ⟶ G) :
    completionMap₂ (α + β) = completionMap₂ α + completionMap₂ β := by
  refine NatTrans.ext (funext fun P => Karoubi.hom_ext _ _ ?_)
  rw [NatTrans.app_add]
  change (matNatTrans (α + β)).app P.X ≫ G.mapMat_.map P.p =
    (matNatTrans α).app P.X ≫ G.mapMat_.map P.p + (matNatTrans β).app P.X ≫ G.mapMat_.map P.p
  rw [matNatTrans_add, NatTrans.app_add, Preadditive.add_comp]

theorem completionMap₂_zero : completionMap₂ (0 : F ⟶ G) = 0 := by
  have h := completionMap₂_add (0 : F ⟶ G) 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem completionMap₂_sum {ι : Type*} (s : Finset ι) (α : ι → (F ⟶ G)) :
    completionMap₂ (∑ j ∈ s, α j) = ∑ j ∈ s, completionMap₂ (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, completionMap₂_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, completionMap₂_add, ih]

/-- An isomorphism of additive functors induces an isomorphism on completions. -/
@[simps]
def completionIso (e : F ≅ G) : completionMap F ≅ completionMap G where
  hom := completionMap₂ e.hom
  inv := completionMap₂ e.inv
  hom_inv_id := by rw [← completionMap₂_comp, e.hom_inv_id, completionMap₂_id]
  inv_hom_id := by rw [← completionMap₂_comp, e.inv_hom_id, completionMap₂_id]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Hs : ι → A ⥤ B} [∀ s, (Hs s).Additive]

/-- **A decomposition of functors gives a decomposition on completions**: a `SumDecomp` of `F`
as `G ⊕ ⨁_s H_s` by natural transformations gives a `SumDecomp` of `completionMap F` as
`completionMap G ⊕ ⨁_s completionMap H_s`. -/
def completionSumDecomp (Dc : SumDecomp F G Hs) :
    SumDecomp (completionMap F) (completionMap G) (fun s => completionMap (Hs s)) where
  a0 := completionMap₂ Dc.a0
  b0 := completionMap₂ Dc.b0
  a s := completionMap₂ (Dc.a s)
  b s := completionMap₂ (Dc.b s)
  total := by
    rw [← completionMap₂_id, ← Dc.total, completionMap₂_add, completionMap₂_comp,
      completionMap₂_sum]
    simp only [completionMap₂_comp]
  b0_a0 := by rw [← completionMap₂_comp, Dc.b0_a0, completionMap₂_id]
  b_a0 s := by rw [← completionMap₂_comp, Dc.b_a0, completionMap₂_zero]
  b_a_self s := by rw [← completionMap₂_comp, Dc.b_a_self, completionMap₂_id]
  b_a_ne s t h := by rw [← completionMap₂_comp, Dc.b_a_ne s t h, completionMap₂_zero]

end

end Categorification.TwoRep
