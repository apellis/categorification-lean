/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossing

/-!
# Naturality of block crossings for blockwise endomorphisms

If the blockwise crossings `P ⋙ L' ⟶ L ⋙ P'` commute with blockwise endomorphisms of `L` and
`L'`, the assembled crossing commutes with their block sums
(`blockResCross_blockSumMap_app`). If the blockwise reverse crossings `L ⋙ P' ⟶ P ⋙ L'`
commute with endomorphisms of `P` and `P'`, so does the assembled reverse crossing
(`blockResCrossRev_natural_app`).

In the weight-space form of Webster's 2-representation (arXiv:1309.3796v3, §4.6, proof of
Theorem 4.25) these say that dots on a black strand slide through its crossings with a red
line.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

variable {A : Type w₁} {Dd : Type w₂} {A' : Type w₃} {Dd' : Type w₄}
  (s : A → Dd) (s' : A' → Dd') (r : A' → A) (r' : Dd' → Dd)
  (hc : ∀ a', s (r a') = r' (s' a'))
  {C : A → Type u₁} [∀ a, Category.{v₁} (C a)]
  {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)]
  {C' : A' → Type u₃} [∀ a, Category.{v₃} (C' a)]
  {D' : Dd' → Type u₄} [∀ d, Category.{v₄} (D' d)]
  [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]
  [∀ d, Finite {a // s' a = d}] [∀ d, Preadditive (D' d)] [∀ d, HasFiniteBiproducts (D' d)]
  (L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d)
  (L' : ∀ (a : A') (d : Dd'), s' a = d → C' a ⥤ D' d)
  (P : ∀ (a' : A') (a : A), r a' = a → C a ⥤ C' a')
  (P' : ∀ (d' : Dd') (d : Dd), r' d' = d → D d ⥤ D' d')

/-- **The crossing commutes with block sums of blockwise endomorphisms** of `L` and `L'` when
the blockwise crossings do. -/
theorem blockResCross_blockSumMap_app
    (α : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
      P a' (r a') rfl ⋙ L' a' d' h ⟶
        L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl)
    (γ : ∀ a d h, L a d h ⟶ L a d h) (γ' : ∀ a' d' h, L' a' d' h ⟶ L' a' d' h)
    (hγ : ∀ a' d' h, Functor.whiskerLeft (P a' (r a') rfl) (γ' a' d' h) ≫ α a' d' h =
      α a' d' h ≫ Functor.whiskerRight (γ (r a') (r' d') ((hc a').trans (congrArg r' h)))
        (P' d' (r' d') rfl))
    (N : ∀ a, C a) (d' : Dd') :
    (blockSumMap s' γ').app ((blockRes r P).obj N) d' ≫
        blockResCrossApp s s' r r' hc L L' P P' α N d' =
      blockResCrossApp s s' r r' hc L L' P P' α N d' ≫
        (P' d' (r' d') rfl).map ((blockSumMap s γ).app N (r' d')) := by
  refine biproduct.hom_ext' _ _ fun p => ?_
  have key := NatTrans.congr_app (hγ p.1 d' p.2) (N (r p.1))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at key
  rw [← Category.assoc, blockι_blockSumMap, Category.assoc, blockι_blockResCrossApp,
    blockι_blockResCrossApp_assoc, ← Functor.map_comp, blockι_blockSumMap, Functor.map_comp,
    reassoc_of% key]

/-- **The reverse crossing commutes with blockwise endomorphisms** of `P` and `P'` when the
blockwise reverse crossings do. -/
theorem blockResCrossRev_natural_app
    (β : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
      L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl ⟶
        P a' (r a') rfl ⋙ L' a' d' h)
    (δ : ∀ a', P a' (r a') rfl ⟶ P a' (r a') rfl)
    (δ' : ∀ d', P' d' (r' d') rfl ⟶ P' d' (r' d') rfl)
    (hδ : ∀ a' d' h,
      Functor.whiskerLeft (L (r a') (r' d') ((hc a').trans (congrArg r' h))) (δ' d') ≫
        β a' d' h = β a' d' h ≫ Functor.whiskerRight (δ a') (L' a' d' h))
    (N : ∀ a, C a) (d' : Dd') :
    (δ' d').app ((blockSum s L).obj N (r' d')) ≫
        blockResCrossRevApp s s' r r' hc L L' P P' β N d' =
      blockResCrossRevApp s s' r r' hc L L' P P' β N d' ≫
        biproduct.map fun p : {a' // s' a' = d'} =>
          (L' p.1 d' p.2).map ((δ p.1).app (N (r p.1))) := by
  refine biproduct.hom_ext _ _ fun p => ?_
  have key := NatTrans.congr_app (hδ p.1 d' p.2) (N (r p.1))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at key
  rw [Category.assoc, blockResCrossRevApp_π, Category.assoc, biproduct.map_π,
    blockResCrossRevApp_π_assoc, ← (δ' d').naturality_assoc, key]

end

end Categorification.TwoRep
