/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossing
import Categorification.TwoRep.MateNat

/-!
# Mates of crossings between block sums and block restrictions

For block-sum adjunctions `blockSum s L ⊣ blockRes s R` (`blockAdjunction`), the mate
(`mateNat`) of a crossing `blockResCross` assembled from blockwise transformations is computed
block by block: on the block `a'` it is the blockwise mate, read with the counit of the block
`r a'` over `r' (s' a')` (`mateNat_blockResCross_app`).

This identifies the red/down crossings of Webster's 2-representation (arXiv:1309.3796v3, §4.6,
Thm. 4.25) with the mates of the red/up crossings on weight spaces.
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
  {L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
  {L' : ∀ (a : A') (d : Dd'), s' a = d → C' a ⥤ D' d}
  {RL : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a}
  {RL' : ∀ (a : A') (d : Dd'), s' a = d → D' d ⥤ C' a}
  (adj : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⊣ RL a d h)
  (adj' : ∀ (a : A') (d : Dd') (h : s' a = d), L' a d h ⊣ RL' a d h)
  (P : ∀ (a' : A') (a : A), r a' = a → C a ⥤ C' a')
  (P' : ∀ (d' : Dd') (d : Dd), r' d' = d → D d ⥤ D' d')
  (α : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
    P a' (r a') rfl ⋙ L' a' d' h ⟶
      L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl)

/-- The mate of a block crossing along block-sum adjunctions, block by block: the unit, the
blockwise crossing, and the counit of the block `r a'` over `r' (s' a')`. -/
theorem mateNat_blockResCross_app (N : ∀ d, D d) (a' : A') :
    (mateNat (blockAdjunction s' adj').unit (blockResCross s s' r r' hc L L' P P' α)
        (blockAdjunction s adj).counit).app N a' =
      (adj' a' (s' a') rfl).unit.app _ ≫
        (RL' a' (s' a') rfl).map ((α a' (s' a') rfl).app _) ≫
        (RL' a' (s' a') rfl).map ((P' (s' a') (r' (s' a')) rfl).map
          (blockCounit s adj (hc a') N)) := by
  rw [mateNat_app]
  change ((adj' a' (s' a') rfl).unit.app _ ≫
      (RL' a' (s' a') rfl).map (blockι s' L' _ ⟨a', rfl⟩)) ≫
    (RL' a' (s' a') rfl).map (blockResCrossApp s s' r r' hc L L' P P' α _ (s' a')) ≫
    (RL' a' (s' a') rfl).map ((P' (s' a') (r' (s' a')) rfl).map
      ((blockAdjunction s adj).counit.app N (r' (s' a')))) = _
  rw [Category.assoc, ← Functor.map_comp_assoc, blockι_blockResCrossApp, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  erw [biproduct.ι_desc]
  rw [Functor.map_comp]

section Pointwise

variable {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
  {C : A → Type u₁} [∀ a, Category.{v₁} (C a)]
  {C' : A → Type u₃} [∀ a, Category.{v₃} (C' a)]
  {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)]
  {D' : Dd → Type u₄} [∀ d, Category.{v₄} (D' d)]
  [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]
  [∀ d, Preadditive (D' d)] [∀ d, HasFiniteBiproducts (D' d)]
  (L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d)
  (L' : ∀ (a : A) (d : Dd), s a = d → C' a ⥤ D' d)
  (P : ∀ (a' a : A), id a' = a → C a ⥤ C' a')
  (P' : ∀ (d' d : Dd), id d' = d → D d ⥤ D' d')
  (G : ∀ (a' a : A), id a' = a → C' a ⥤ C a')
  (G' : ∀ (d' d : Dd), id d' = d → D' d ⥤ D d')
  [∀ d' d h, (P' d' d h).Additive]
  (adjP : ∀ a, P a a rfl ⊣ G a a rfl) (adjP' : ∀ d, P' d d rfl ⊣ G' d d rfl)
  (β : ∀ (a : A) (d : Dd) (h : s a = d),
    L (id a) (id d) h ⋙ P' d (id d) rfl ⟶ P a (id a) rfl ⋙ L' a d h)
  (e : ∀ (a : A) (d : Dd) (h : s a = d),
    G a (id a) rfl ⋙ L a d h ⟶ L' (id a) (id d) h ⋙ G' d (id d) rfl)

/-- **Mates of reverse block crossings along pointwise adjunctions**: when the block restrictions
along the identity carry adjunctions block by block, the mate of the reverse crossing
`blockResCrossRev` is the crossing `blockResCross` of the blockwise mates. -/
theorem mateNat_blockResCrossRev
    (η : 𝟭 (∀ d, D d) ⟶ blockRes id P' ⋙ blockRes id G')
    (hη : ∀ N d, η.app N d = (adjP' d).unit.app (N d))
    (ε : blockRes id G ⋙ blockRes id P ⟶ 𝟭 (∀ a, C' a))
    (hε : ∀ M a, ε.app M a = (adjP a).counit.app (M a))
    (hβ : ∀ (a : A) (d : Dd) (h : s a = d) (X : C' a),
      (adjP' d).unit.app ((L a d h).obj ((G a a rfl).obj X)) ≫
        (G' d d rfl).map ((β a d h).app ((G a a rfl).obj X)) ≫
        (G' d d rfl).map ((L' a d h).map ((adjP a).counit.app X)) = (e a d h).app X) :
    mateNat η (blockResCrossRev s s id id (fun _ => rfl) L L' P P' β) ε =
      blockResCross s s id id (fun _ => rfl) L' L G G' e := by
  refine NatTrans.ext (funext fun M => funext fun d => biproduct.hom_ext' _ _ fun p => ?_)
  rw [mateNat_app]
  change blockι s L ((blockRes id G).obj M) p ≫
      η.app ((blockSum s L).obj ((blockRes id G).obj M)) d ≫ (G' d d rfl).map
      (blockResCrossRevApp s s id id (fun _ => rfl) L L' P P' β _ d) ≫
      (G' d d rfl).map ((blockSum s L').map (ε.app M) d) =
    blockι s L _ p ≫ blockResCrossApp s s id id (fun _ => rfl) L' L G G' e M d
  rw [blockι_blockResCrossApp, hη]
  erw [(adjP' d).unit.naturality_assoc]
  rw [← Functor.map_comp]
  erw [Functor.comp_map]
  rw [← Functor.map_comp]
  erw [map_ι_blockResCrossRevApp_assoc s s id id (fun _ => rfl) L L' P P' β
      (fun _ _ _ h => Subtype.ext (congrArg Subtype.val h))]
  rw [blockι_map, hε, Functor.map_comp,
    Functor.map_comp, ← hβ]
  simp only [Category.assoc]
  rfl

end Pointwise

end
end Categorification.TwoRep
