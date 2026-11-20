/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensorNat
import Categorification.Diagrams.KL3.Karoubi
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Decompositions of functors pass to their module functors

For additive functors `F : C ⥤ D` and objects `O` of `C`, `O'` of `D`, `HomTensor` gives the
module functor `M ↦ (O' ⟶ F O) ⊗_{End O} M` from right `End O`-modules to right
`End O'`-modules, and a natural transformation `α : F ⟶ G` gives a natural map of module functors
(`HomTensor.natModuleMap`). Since this assignment respects identities, composition and sums, a
decomposition `F ≅ G ⊕ ⨁_s H_s` of functors, given by natural transformations
(`SumDecomp` in the functor category), gives the decomposition
`(O' ⟶ F O) ⊗ M ≅ (O' ⟶ G O) ⊗ M ⊕ ⨁_s (O' ⟶ H_s O) ⊗ M` of right modules, for every module `M`
(`HomTensor.sumDecompModule`).

This passes the commutation relations `E_i F_i ≅ F_i E_i ⊕ 1^{⊕ n}` of a categorical action
on categories of projectives to the action on module categories, as in Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, Proposition 5.5. The ring of scalars is
`ℤ`, so no linearity hypothesis is needed beyond additivity.
-/

namespace Categorification.HomTensor

open CategoryTheory MulOpposite

noncomputable section

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (O : C) (O' : D) (M : Type w) [AddCommGroup M] [Module (End O)ᵐᵒᵖ M]

attribute [local instance] bimodule

/-- The value `(O' ⟶ F O) ⊗_{End O} M` of the module functor of `F`, as a right
`End O'`-module. -/
abbrev tensorObj (F : C ⥤ D) [F.Additive] : ModuleCat.{max v₂ w} (End O')ᵐᵒᵖ :=
  ModuleCat.of _ (BalancedTensor ℤ (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ F.obj O) M)

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

/-- The map of module functors of a natural transformation, as a morphism of modules. -/
def natModuleHom (α : F ⟶ G) : tensorObj O O' M F ⟶ tensorObj O O' M G :=
  ModuleCat.ofHom (natModuleMap ℤ O O' M α)

theorem natModuleHom_id : natModuleHom O O' M (𝟙 F) = 𝟙 _ := by
  ext1
  exact natModuleMap_id ℤ O O' (M := M)

theorem natModuleHom_comp (α : F ⟶ G) (β : G ⟶ H) :
    natModuleHom O O' M (α ≫ β) = natModuleHom O O' M α ≫ natModuleHom O O' M β := by
  ext1
  exact natModuleMap_comp ℤ O O' (M := M) α β

theorem natModuleHom_add (α β : F ⟶ G) :
    natModuleHom O O' M (α + β) = natModuleHom O O' M α + natModuleHom O O' M β := by
  ext1
  exact natModuleMap_add ℤ O O' (M := M) α β

theorem natModuleHom_zero : natModuleHom O O' M (0 : F ⟶ G) = 0 := by
  ext1
  exact natModuleMap_zero ℤ O O' (M := M)

theorem natModuleHom_sum {ι : Type*} (s : Finset ι) (α : ι → (F ⟶ G)) :
    natModuleHom O O' M (∑ j ∈ s, α j) = ∑ j ∈ s, natModuleHom O O' M (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, natModuleHom_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, natModuleHom_add, ih]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Hs : ι → C ⥤ D} [∀ s, (Hs s).Additive]

/-- **A decomposition of functors gives a decomposition of their module functors**: a
`SumDecomp` of `F` as `G ⊕ ⨁_s H_s` by natural transformations gives a `SumDecomp` of
`(O' ⟶ F O) ⊗ M` as `(O' ⟶ G O) ⊗ M ⊕ ⨁_s (O' ⟶ H_s O) ⊗ M`, for every right
`End O`-module `M`. -/
def sumDecompModule (Dc : SumDecomp F G Hs) :
    SumDecomp (tensorObj O O' M F) (tensorObj O O' M G) (fun s => tensorObj O O' M (Hs s)) where
  a0 := natModuleHom O O' M Dc.a0
  b0 := natModuleHom O O' M Dc.b0
  a s := natModuleHom O O' M (Dc.a s)
  b s := natModuleHom O O' M (Dc.b s)
  total := by
    rw [← natModuleHom_id, ← Dc.total, natModuleHom_add, natModuleHom_comp, natModuleHom_sum]
    simp only [natModuleHom_comp]
  b0_a0 := by rw [← natModuleHom_comp, Dc.b0_a0, natModuleHom_id]
  b_a0 s := by rw [← natModuleHom_comp, Dc.b_a0, natModuleHom_zero]
  b_a_self s := by rw [← natModuleHom_comp, Dc.b_a_self, natModuleHom_id]
  b_a_ne s t h := by rw [← natModuleHom_comp, Dc.b_a_ne s t h, natModuleHom_zero]

end

end Categorification.HomTensor
