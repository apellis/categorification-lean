/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossing

/-!
# Bigons of block crossings with a dot on the restriction side

A companion of `blockResCrossRev_blockResCross_app`: if the blockwise reverse crossing followed
by the blockwise crossing is an endomorphism `δ` of the restriction functor `P'`, whiskered by
`L`, and the map of fibres is bijective, the assembled crossings compose to `δ` applied to the
block sum. In the weight-space form of Webster's 2-representation (arXiv:1309.3796v3, §4.6,
Theorem 4.25) this is the bigon (4.2) on the higher-weight side of a red line, with the dots on
the black strand.
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
  (α : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
    P a' (r a') rfl ⋙ L' a' d' h ⟶
      L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl)
  (β : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
    L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl ⟶
      P a' (r a') rfl ⋙ L' a' d' h)
  [∀ d' d h, (P' d' d h).Additive]

/-- **Bigon through the block sum, dot on the restriction side**: if the blockwise crossings
compose to an endomorphism `δ` of `P'` whiskered by `L` and the map of fibres is bijective, the
crossings compose to `δ` at the block sum. -/
theorem blockResCrossRev_blockResCross_app_of_whiskerLeft
    (hbij : ∀ d', Function.Bijective (fibreMap s s' r r' hc (d' := d')))
    (δ : ∀ d', P' d' (r' d') rfl ⟶ P' d' (r' d') rfl)
    (hγ : ∀ a' d' h, β a' d' h ≫ α a' d' h =
      Functor.whiskerLeft (L (r a') (r' d') ((hc a').trans (congrArg r' h))) (δ d'))
    (N : ∀ a, C a) (d' : Dd') :
    blockResCrossRevApp s s' r r' hc L L' P P' β N d' ≫
      blockResCrossApp s s' r r' hc L L' P P' α N d' =
      (δ d').app ((blockSum s L).obj N (r' d')) := by
  refine map_biproduct_hom_ext (P' d' (r' d') rfl) _ fun q => ?_
  obtain ⟨p, rfl⟩ := (hbij d').2 q
  rw [map_ι_blockResCrossRevApp_assoc s s' r r' hc L L' P P' β (fun d' => (hbij d').1),
    blockι_blockResCrossApp, ← NatTrans.comp_app_assoc, hγ]
  exact ((δ d').naturality _).symm

end

end Categorification.TwoRep
