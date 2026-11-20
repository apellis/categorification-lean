/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCross

/-!
# Crossings between block sums and block restrictions

Let `blockSum s L` and `blockSum s' L'` be two block-sum functors, compared along maps of
index sets `r : A' → A` and `r' : Dd' → Dd` with `s ∘ r = r' ∘ s'`, and let `P`, `P'` be
blockwise restriction functors along `r`, `r'`. Blockwise natural transformations
`P ⋙ L' ⟶ L ⋙ P'` and `L ⋙ P' ⟶ P ⋙ L'` assemble to natural transformations
`blockRes r P ⋙ blockSum s' L' ⟶ blockSum s L ⋙ blockRes r' P'` and back
(`blockResCross`, `blockResCrossRev`). When the induced maps of fibres are injective, respectively
bijective, blockwise bigon relations assemble to bigon relations of the crossings
(`blockResCross_blockResCrossRev_app`, `blockResCrossRev_blockResCross_app`).

This is the bookkeeping behind the crossings of a black strand with a red strand in the
weight-space form of Webster's 2-representation (Webster, arXiv:1309.3796v3, §4.6,
Thm. 4.25): on each block the crossing is a cyclotomic quotient or its dotted reverse.
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

/-- The map of fibres induced by `r` over `r'`. -/
abbrev fibreMap {d' : Dd'} (p : {a' // s' a' = d'}) : {a // s a = r' d'} :=
  ⟨r p.1, (hc p.1).trans (congrArg r' p.2)⟩

section Cross

variable (α : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
  P a' (r a') rfl ⋙ L' a' d' h ⟶
    L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl)

/-- The component of the crossing at `N` and `d'`. -/
def blockResCrossApp (N : ∀ a, C a) (d' : Dd') :
    (blockSum s' L').obj ((blockRes r P).obj N) d' ⟶
      (P' d' (r' d') rfl).obj ((blockSum s L).obj N (r' d')) :=
  biproduct.desc fun p => (α p.1 d' p.2).app (N (r p.1)) ≫
    (P' d' (r' d') rfl).map (blockι s L N (fibreMap s s' r r' hc p))

@[reassoc]
theorem blockι_blockResCrossApp (N : ∀ a, C a) {d' : Dd'} (p : {a' // s' a' = d'}) :
    blockι s' L' ((blockRes r P).obj N) p ≫ blockResCrossApp s s' r r' hc L L' P P' α N d' =
      (α p.1 d' p.2).app (N (r p.1)) ≫
        (P' d' (r' d') rfl).map (blockι s L N (fibreMap s s' r r' hc p)) :=
  biproduct.ι_desc _ _

/-- **The crossing of a block sum with a block restriction**, assembled from blockwise
transformations `P ⋙ L' ⟶ L ⋙ P'`. -/
def blockResCross : blockRes r P ⋙ blockSum s' L' ⟶ blockSum s L ⋙ blockRes r' P' where
  app N d' := blockResCrossApp s s' r r' hc L L' P P' α N d'
  naturality N N' f := funext fun d' => biproduct.hom_ext' _ _ fun p => by
    change blockι s' L' _ p ≫ (blockSum s' L').map ((blockRes r P).map f) d' ≫
        blockResCrossApp s s' r r' hc L L' P P' α N' d' =
      blockι s' L' _ p ≫ blockResCrossApp s s' r r' hc L L' P P' α N d' ≫
        (P' d' (r' d') rfl).map ((blockSum s L).map f (r' d'))
    rw [← Category.assoc, blockι_map, Category.assoc, blockι_blockResCrossApp,
      blockι_blockResCrossApp_assoc]
    erw [← (P' d' (r' d') rfl).map_comp, blockι_map, (P' d' (r' d') rfl).map_comp]
    exact (α p.1 d' p.2).naturality_assoc (f (r p.1)) _

theorem blockResCross_app (N : ∀ a, C a) (d' : Dd') :
    (blockResCross s s' r r' hc L L' P P' α).app N d' =
      blockResCrossApp s s' r r' hc L L' P P' α N d' :=
  rfl

end Cross

section CrossRev

variable (β : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
  L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl ⟶
    P a' (r a') rfl ⋙ L' a' d' h)

/-- The component of the reverse crossing at `N` and `d'`. -/
def blockResCrossRevApp (N : ∀ a, C a) (d' : Dd') :
    (P' d' (r' d') rfl).obj ((blockSum s L).obj N (r' d')) ⟶
      (blockSum s' L').obj ((blockRes r P).obj N) d' :=
  biproduct.lift fun p =>
    (P' d' (r' d') rfl).map (biproduct.π _ (fibreMap s s' r r' hc p)) ≫
      (β p.1 d' p.2).app (N (r p.1))

@[reassoc]
theorem blockResCrossRevApp_π (N : ∀ a, C a) {d' : Dd'} (p : {a' // s' a' = d'}) :
    blockResCrossRevApp s s' r r' hc L L' P P' β N d' ≫
        biproduct.π (fun p : {a' // s' a' = d'} =>
          (L' p.1 d' p.2).obj ((blockRes r P).obj N p.1)) p =
      (P' d' (r' d') rfl).map (biproduct.π _ (fibreMap s s' r r' hc p)) ≫
        (β p.1 d' p.2).app (N (r p.1)) :=
  biproduct.lift_π _ _

/-- **The reverse crossing**, assembled from blockwise transformations `L ⋙ P' ⟶ P ⋙ L'`. -/
def blockResCrossRev : blockSum s L ⋙ blockRes r' P' ⟶ blockRes r P ⋙ blockSum s' L' where
  app N d' := blockResCrossRevApp s s' r r' hc L L' P P' β N d'
  naturality N N' f := funext fun d' => biproduct.hom_ext _ _ fun p => by
    change ((P' d' (r' d') rfl).map ((blockSum s L).map f (r' d')) ≫
        blockResCrossRevApp s s' r r' hc L L' P P' β N' d') ≫ biproduct.π _ p =
      (blockResCrossRevApp s s' r r' hc L L' P P' β N d' ≫
        biproduct.map (fun p => (L' p.1 d' p.2).map ((P p.1 (r p.1) rfl).map (f (r p.1))))) ≫
          biproduct.π _ p
    rw [Category.assoc, Category.assoc, blockResCrossRevApp_π, biproduct.map_π,
      blockResCrossRevApp_π_assoc, ← Functor.map_comp_assoc]
    rw [blockSum_map, biproduct.map_π, Functor.map_comp, Category.assoc]
    exact ((β p.1 d' p.2).naturality (f (r p.1))).symm ▸ rfl

/-- On the image of the block `fibreMap p`, the reverse crossing is the blockwise one. -/
@[reassoc]
theorem map_ι_blockResCrossRevApp [∀ d' d h, (P' d' d h).Additive]
    (hinj : ∀ d', Function.Injective (fibreMap s s' r r' hc (d' := d')))
    (N : ∀ a, C a) {d' : Dd'} (p : {a' // s' a' = d'}) :
    (P' d' (r' d') rfl).map (blockι s L N (fibreMap s s' r r' hc p)) ≫
        blockResCrossRevApp s s' r r' hc L L' P P' β N d' =
      (β p.1 d' p.2).app (N (r p.1)) ≫ blockι s' L' ((blockRes r P).obj N) p := by
  refine biproduct.hom_ext _ _ fun q => ?_
  rw [Category.assoc, blockResCrossRevApp_π, ← Functor.map_comp_assoc, Category.assoc]
  by_cases hpq : p = q
  · subst hpq
    rw [biproduct.ι_π_self, biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  · have hne : fibreMap s s' r r' hc p ≠ fibreMap s s' r r' hc q := fun h => hpq (hinj d' h)
    rw [biproduct.ι_π_ne _ hne, biproduct.ι_π_ne _ hpq, Functor.map_zero, Limits.zero_comp,
      Limits.comp_zero]

theorem blockResCrossRev_app (N : ∀ a, C a) (d' : Dd') :
    (blockResCrossRev s s' r r' hc L L' P P' β).app N d' =
      blockResCrossRevApp s s' r r' hc L L' P P' β N d' :=
  rfl

end CrossRev

section Bigons

variable (α : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
  P a' (r a') rfl ⋙ L' a' d' h ⟶
    L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl)
  (β : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
  L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl ⟶
    P a' (r a') rfl ⋙ L' a' d' h)
  [∀ d' d h, (P' d' d h).Additive]

/-- **Bigon through the block restriction**: if the blockwise crossings compose to `γ` and the
map of fibres is injective, the crossings compose to the blockwise action of `γ`. -/
theorem blockResCross_blockResCrossRev_app
    (hinj : ∀ d', Function.Injective (fibreMap s s' r r' hc (d' := d')))
    (γ : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
      P a' (r a') rfl ⋙ L' a' d' h ⟶ P a' (r a') rfl ⋙ L' a' d' h)
    (hγ : ∀ a' d' h, α a' d' h ≫ β a' d' h = γ a' d' h) (N : ∀ a, C a) (d' : Dd') :
    blockResCrossApp s s' r r' hc L L' P P' α N d' ≫
      blockResCrossRevApp s s' r r' hc L L' P P' β N d' =
      biproduct.map fun p : {a' // s' a' = d'} => (γ p.1 d' p.2).app (N (r p.1)) := by
  refine biproduct.hom_ext' _ _ fun p => biproduct.hom_ext _ _ fun q => ?_
  simp only [Category.assoc]
  rw [blockι_blockResCrossApp_assoc, blockResCrossRevApp_π, ← Functor.map_comp_assoc,
    biproduct.ι_map_assoc]
  by_cases hpq : p = q
  · subst hpq
    rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [biproduct.ι_π_self]
    rw [Category.comp_id, ← hγ]
    rfl
  · have hne : fibreMap s s' r r' hc p ≠ fibreMap s s' r r' hc q := fun h => hpq (hinj d' h)
    rw [biproduct.ι_π_ne _ hne, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
    erw [biproduct.ι_π_ne _ hpq]
    rw [Limits.comp_zero]

/-- **Bigon through the block sum**: if the blockwise crossings compose to `γ'` whiskered by
`P'` and the map of fibres is bijective, the crossings compose to `P'` applied to the
blockwise action of `γ'`. -/
theorem blockResCrossRev_blockResCross_app
    (hbij : ∀ d', Function.Bijective (fibreMap s s' r r' hc (d' := d')))
    (γ' : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⟶ L a d h)
    (hγ : ∀ a' d' h, β a' d' h ≫ α a' d' h =
      Functor.whiskerRight (γ' (r a') (r' d') ((hc a').trans (congrArg r' h)))
        (P' d' (r' d') rfl))
    (N : ∀ a, C a) (d' : Dd') :
    blockResCrossRevApp s s' r r' hc L L' P P' β N d' ≫
      blockResCrossApp s s' r r' hc L L' P P' α N d' =
      (P' d' (r' d') rfl).map ((blockSumMap s γ').app N (r' d')) := by
  refine map_biproduct_hom_ext (P' d' (r' d') rfl) _ fun q => ?_
  obtain ⟨p, rfl⟩ := (hbij d').2 q
  rw [← Functor.map_comp, blockι_blockSumMap, Functor.map_comp,
    map_ι_blockResCrossRevApp_assoc s s' r r' hc L L' P P' β (fun d' => (hbij d').1),
    blockι_blockResCrossApp, ← NatTrans.comp_app_assoc, hγ]
  rfl

end Bigons

section Iso

variable [∀ d' d h, (P' d' d h).Additive]

/-- **The crossing is invertible** when the blockwise crossings are invertible and the map of
fibres is bijective; the inverse is the reverse crossing. -/
def blockResCrossIso
    (hbij : ∀ d', Function.Bijective (fibreMap s s' r r' hc (d' := d')))
    (e : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
      P a' (r a') rfl ⋙ L' a' d' h ≅
        L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl) :
    blockRes r P ⋙ blockSum s' L' ≅ blockSum s L ⋙ blockRes r' P' where
  hom := blockResCross s s' r r' hc L L' P P' fun a' d' h => (e a' d' h).hom
  inv := blockResCrossRev s s' r r' hc L L' P P' fun a' d' h => (e a' d' h).inv
  hom_inv_id := NatTrans.ext <| funext fun N => funext fun d' => by
    change blockResCrossApp s s' r r' hc L L' P P' (fun a' d' h => (e a' d' h).hom) N d' ≫
      blockResCrossRevApp s s' r r' hc L L' P P' (fun a' d' h => (e a' d' h).inv) N d' = 𝟙 _
    rw [blockResCross_blockResCrossRev_app s s' r r' hc L L' P P' _ _
      (fun d' => (hbij d').1) (fun _ _ _ => 𝟙 _) (fun a' d' h => (e a' d' h).hom_inv_id)]
    exact biproduct.hom_ext _ _ fun p => by simp
  inv_hom_id := NatTrans.ext <| funext fun N => funext fun d' => by
    change blockResCrossRevApp s s' r r' hc L L' P P' (fun a' d' h => (e a' d' h).inv) N d' ≫
      blockResCrossApp s s' r r' hc L L' P P' (fun a' d' h => (e a' d' h).hom) N d' = 𝟙 _
    rw [blockResCrossRev_blockResCross_app s s' r r' hc L L' P P' _ _ hbij
      (fun _ _ _ => 𝟙 _) (fun a' d' h => (e a' d' h).inv_hom_id.trans
        (Functor.whiskerRight_id _).symm)]
    rw [← (P' d' (r' d') rfl).map_id]
    congr 1
    exact biproduct.hom_ext _ _ fun p => by simp [blockSumMap]

end Iso

end

end Categorification.TwoRep
