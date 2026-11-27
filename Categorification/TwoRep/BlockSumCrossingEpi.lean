/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossing

/-!
# Epimorphic crossings of block sums and block restrictions

The crossings `blockResCross` and `blockResCrossRev` of a block sum with a block restriction
are componentwise epimorphisms when their blockwise transformations are, provided the induced
map of fibres is surjective, respectively injective, and the restriction functors are additive.

This is used to cancel the quotient crossing `a′` of Webster's 2-representation (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25), which on each cyclotomic block is the
surjection induced by a cyclotomic quotient.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

/-- A morphism of a product of categories whose components are epimorphisms is an
epimorphism. -/
theorem pi_epi_of_epi {A : Type w₁} {C : A → Type u₁} [∀ a, Category.{v₁} (C a)]
    {M N : ∀ a, C a} (f : M ⟶ N) (hf : ∀ a, Epi (f a)) : Epi f :=
  ⟨fun _ _ e => funext fun a => (cancel_epi (f a)).1 (congrFun e a)⟩

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
  [∀ d' d h, (P' d' d h).Additive]

/-- **The crossing `blockResCross` is an epimorphism** in each component when the blockwise
transformations are and the map of fibres is surjective. -/
theorem blockResCrossApp_epi
    (α : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
      P a' (r a') rfl ⋙ L' a' d' h ⟶
        L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl)
    (hsurj : ∀ d', Function.Surjective (fibreMap s s' r r' hc (d' := d')))
    (hα : ∀ a' d' h N, Epi ((α a' d' h).app N)) (N : ∀ a, C a) (d' : Dd') :
    Epi (blockResCrossApp s s' r r' hc L L' P P' α N d') := by
  constructor
  intro Z g h e
  have key : ∀ q : {a // s a = r' d'}, (P' d' (r' d') rfl).map (blockι s L N q) ≫ g =
      (P' d' (r' d') rfl).map (blockι s L N q) ≫ h := by
    intro q
    obtain ⟨p, rfl⟩ := hsurj d' q
    have e' := congrArg (fun t => blockι s' L' ((blockRes r P).obj N) p ≫ t) e
    simp only [blockι_blockResCrossApp_assoc] at e'
    exact (cancel_epi _).1 e'
  have := Fintype.ofFinite {a // s a = r' d'}
  have htot : 𝟙 ((P' d' (r' d') rfl).obj ((blockSum s L).obj N (r' d'))) =
      ∑ q : {a // s a = r' d'}, (P' d' (r' d') rfl).map (biproduct.π _ q) ≫
        (P' d' (r' d') rfl).map (blockι s L N q) := by
    have ht : 𝟙 (⨁ fun q : {a // s a = r' d'} => (L q.1 (r' d') q.2).obj (N q.1)) =
        ∑ q : {a // s a = r' d'}, biproduct.π _ q ≫ biproduct.ι _ q :=
      (IsBilimit.total (biproduct.isBilimit _)).symm
    rw [← (P' d' (r' d') rfl).map_id]
    erw [ht]
    rw [Functor.map_sum]
    simp only [Functor.map_comp]
  rw [← Category.id_comp g, ← Category.id_comp h, htot, Preadditive.sum_comp,
    Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun q _ => by rw [Category.assoc, Category.assoc, key q]

/-- **The reverse crossing `blockResCrossRev` is an epimorphism** in each component when the
blockwise transformations are and the map of fibres is injective. -/
theorem blockResCrossRevApp_epi
    (β : ∀ (a' : A') (d' : Dd') (h : s' a' = d'),
      L (r a') (r' d') ((hc a').trans (congrArg r' h)) ⋙ P' d' (r' d') rfl ⟶
        P a' (r a') rfl ⋙ L' a' d' h)
    (hinj : ∀ d', Function.Injective (fibreMap s s' r r' hc (d' := d')))
    (hβ : ∀ a' d' h N, Epi ((β a' d' h).app N)) (N : ∀ a, C a) (d' : Dd') :
    Epi (blockResCrossRevApp s s' r r' hc L L' P P' β N d') := by
  constructor
  intro Z g h e
  refine biproduct.hom_ext' _ _ fun p => ?_
  have e' := congrArg (fun t => (P' d' (r' d') rfl).map
    (blockι s L N (fibreMap s s' r r' hc p)) ≫ t) e
  simp only [map_ι_blockResCrossRevApp_assoc s s' r r' hc L L' P P' β hinj] at e'
  exact (cancel_epi _).1 e'

end

end Categorification.TwoRep
