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

A transformation whose counit transpose agrees with that of a mate is that mate
(`mateNat_eq_of_counit`); blockwise, this identifies the mate of a reverse crossing along
pointwise adjunctions of block restrictions (`mateNat_blockResCrossRev_eq_of_counit`).

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

section Counit

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  {L₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} {G : 𝒜 ⥤ 𝒞} {L₂ : 𝒞 ⥤ 𝒟} {R₂ : 𝒟 ⥤ 𝒞} {H : ℬ ⥤ 𝒟}

/-- **A mate is determined by its counit identity**: a transformation `β : R₁ ⋙ G ⟶ H ⋙ R₂`
whose transpose along `L₂ ⊣ R₂` is `τ` followed by the counit of `L₁ ⊣ R₁` is the mate of
`τ`. -/
theorem mateNat_eq_of_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : ∀ Y, L₂.map (β.app Y) ≫ adj₂.counit.app (H.obj Y) =
      τ.app (R₁.obj Y) ≫ H.map (adj₁.counit.app Y)) :
    mateNat adj₂.unit τ adj₁.counit = β := by
  ext Y
  rw [mateNat_app]
  have h := congrArg R₂.map (hβ Y)
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [← h]
  simp only [Functor.comp_obj, Functor.id_obj]
  erw [← adj₂.unit.naturality_assoc]
  erw [adj₂.right_triangle_components]
  exact Category.comp_id _

end Counit

section PointwiseCounit

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
  [∀ d' d h, (G' d' d h).Additive]
  (c : ∀ a, P a a rfl ⋙ G a a rfl ⟶ 𝟭 (C a)) (c' : ∀ d, P' d d rfl ⋙ G' d d rfl ⟶ 𝟭 (D d))
  (β : ∀ (a : A) (d : Dd) (h : s a = d),
    P a (id a) rfl ⋙ L' a d h ⟶ L (id a) (id d) h ⋙ P' d (id d) rfl)
  (e : ∀ (a : A) (d : Dd) (h : s a = d),
    L' (id a) (id d) h ⋙ G' d (id d) rfl ⟶ G a (id a) rfl ⋙ L a d h)

/-- **Mates of block crossings along pointwise left adjunctions**: if the block restrictions
along the identity form adjunctions `blockRes G ⊣ blockRes P`, `blockRes G' ⊣ blockRes P'`
whose counits are blockwise, and the blockwise crossings `β` satisfy the counit identity for the
blockwise transformations `e`, then the crossing `blockResCross β` is the mate of the reverse
crossing `blockResCrossRev e`. -/
theorem mateNat_blockResCrossRev_eq_of_counit
    (adj : blockRes id G ⊣ blockRes id P) (adj' : blockRes id G' ⊣ blockRes id P')
    (hc : ∀ Y a, adj.counit.app Y a = (c a).app (Y a))
    (hc' : ∀ Y d, adj'.counit.app Y d = (c' d).app (Y d))
    (hβ : ∀ (a : A) (d : Dd) (h : s a = d) (X : C a),
      (G' d d rfl).map ((β a d h).app X) ≫ (c' d).app ((L a d h).obj X) =
        (e a d h).app ((P a a rfl).obj X) ≫ (L a d h).map ((c a).app X)) :
    mateNat adj'.unit (blockResCrossRev s s id id (fun _ => rfl) L' L G G' e) adj.counit =
      blockResCross s s id id (fun _ => rfl) L L' P P' β := by
  refine mateNat_eq_of_counit adj adj' _ _ fun Y => funext fun d => ?_
  refine map_biproduct_hom_ext (G' d d rfl) _ fun q => ?_
  change (G' d d rfl).map (blockι s L' ((blockRes id P).obj Y) q) ≫
      (G' d d rfl).map (blockResCrossApp s s id id (fun _ => rfl) L L' P P' β Y d) ≫
        adj'.counit.app ((blockSum s L).obj Y) d =
    (G' d d rfl).map (blockι s L' ((blockRes id P).obj Y) q) ≫
      blockResCrossRevApp s s id id (fun _ => rfl) L' L G G' e ((blockRes id P).obj Y) d ≫
        (blockSum s L).map (adj.counit.app Y) d
  rw [← Functor.map_comp_assoc]
  erw [blockι_blockResCrossApp]
  erw [map_ι_blockResCrossRevApp_assoc s s id id
    (fun _ => rfl) L' L G G' e (fun _ _ _ h => Subtype.ext (congrArg Subtype.val h))]
  erw [blockι_map, hc', hc, Functor.map_comp, Category.assoc, (c' d).naturality]
  erw [← Category.assoc, hβ]
  rw [Category.assoc, Functor.id_map]
  rfl

end PointwiseCounit

end
end Categorification.TwoRep
