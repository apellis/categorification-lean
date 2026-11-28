/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensorComp
import Categorification.Algebra.HomTensorNat

/-!
# Naturality of the composition of module functors

The composition isomorphism of module functors
`(O₂ ⟶ G O₁) ⊗ ((O₁ ⟶ F O₀) ⊗ M) ≅ (O₂ ⟶ G F O₀) ⊗ M` (`HomTensor.compModuleEquiv`) is natural
in both functors: a natural transformation `α : G ⟶ G'` of the outer functor gives the module
map of `F ◁ α` (`compModuleEquiv_natModuleMap`), and one `α : F ⟶ F'` of the inner functor gives
the module map of `α ▷ G` (`compModuleEquiv_mapRight_natModuleMap`).

These identify the module maps of the whiskered dots and crossings of the categorical action
of Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 4.31, on composites of Webster's functors on modules (§4.6 there).
-/

namespace Categorification.HomTensor

open CategoryTheory MulOpposite

noncomputable section

variable (k : Type*) [CommRing k] {C₀ : Type*} [Category C₀] [Preadditive C₀] [Linear k C₀]
  {C₁ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
  {C₂ : Type*} [Category C₂] [Preadditive C₂] [Linear k C₂]
  (F : C₀ ⥤ C₁) [F.Additive] [F.Linear k] (G : C₁ ⥤ C₂) [G.Additive] [G.Linear k]
  (O₀ : C₀) (O₁ : C₁) (O₂ : C₂)

attribute [local instance] bimodule

variable {J : Type*} [Fintype J] (π : J → (F.obj O₀ ⟶ O₁)) (ι : J → (O₁ ⟶ F.obj O₀))
  (h : ∑ j, π j ≫ ι j = 𝟙 (F.obj O₀))

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (End O₀)ᵐᵒᵖ M]
  [IsScalarTower k (End O₀)ᵐᵒᵖ M]

omit [Linear k C₀] [F.Linear k] in
/-- **Naturality in the outer functor**: for `α : G ⟶ G'`, the module map of `α` on the outer
factor is the module map of `F ◁ α` on the composite. -/
theorem compModuleEquiv_natModuleMap {G' : C₁ ⥤ C₂} [G'.Additive] [G'.Linear k] (α : G ⟶ G')
    (x : BalancedTensor k (End O₂)ᵐᵒᵖ (End O₁)ᵐᵒᵖ (O₂ ⟶ G.obj O₁)
      (BalancedTensor k (End O₁)ᵐᵒᵖ (End O₀)ᵐᵒᵖ (O₁ ⟶ F.obj O₀) M)) :
    compModuleEquiv k F G' O₀ O₁ O₂ π ι h M (natModuleMap k O₁ O₂ _ α x) =
      natModuleMap k O₀ O₂ M (Functor.whiskerLeft F α)
        (compModuleEquiv k F G O₀ O₁ O₂ π ι h M x) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul β y =>
    induction y using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | add s t hs ht => simp only [BalancedTensor.tmul_add, map_add, hs, ht]
    | tmul φ m =>
      rw [natModuleMap_tmul, compModuleEquiv_tmul, compModuleEquiv_tmul, natModuleMap_tmul]
      congr 1
      change (β ≫ α.app O₁) ≫ G'.map φ = (β ≫ G.map φ) ≫ α.app (F.obj O₀)
      rw [Category.assoc, Category.assoc, α.naturality]

omit [Linear k C₀] [F.Linear k] in
/-- **Naturality in the inner functor**: for `α : F ⟶ F'`, the module map of `α` on the inner
factor is the module map of `α ▷ G` on the composite. -/
theorem compModuleEquiv_mapRight_natModuleMap {F' : C₀ ⥤ C₁} [F'.Additive] (α : F ⟶ F')
    {J' : Type*} [Fintype J'] (π' : J' → (F'.obj O₀ ⟶ O₁)) (ι' : J' → (O₁ ⟶ F'.obj O₀))
    (h' : ∑ j, π' j ≫ ι' j = 𝟙 (F'.obj O₀))
    (x : BalancedTensor k (End O₂)ᵐᵒᵖ (End O₁)ᵐᵒᵖ (O₂ ⟶ G.obj O₁)
      (BalancedTensor k (End O₁)ᵐᵒᵖ (End O₀)ᵐᵒᵖ (O₁ ⟶ F.obj O₀) M)) :
    compModuleEquiv k F' G O₀ O₁ O₂ π' ι' h' M
        (BalancedTensor.mapRight (natModuleMap k O₀ O₁ M α) x) =
      natModuleMap k O₀ O₂ M (Functor.whiskerRight α G)
        (compModuleEquiv k F G O₀ O₁ O₂ π ι h M x) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul β y =>
    induction y using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | add s t hs ht => simp only [BalancedTensor.tmul_add, map_add, hs, ht]
    | tmul φ m =>
      rw [BalancedTensor.mapRight_tmul, natModuleMap_tmul, compModuleEquiv_tmul,
        compModuleEquiv_tmul, natModuleMap_tmul]
      congr 1
      change β ≫ G.map (φ ≫ α.app O₀) = (β ≫ G.map φ) ≫ G.map (α.app O₀)
      rw [G.map_comp, Category.assoc]

end

end Categorification.HomTensor
