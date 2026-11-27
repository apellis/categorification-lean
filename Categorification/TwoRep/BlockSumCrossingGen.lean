/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossing

/-!
# Two successive block crossings on generators

Let `blockSum s₁ L₁ ⋙ blockSum s₂ L₂` and `blockSum s₁' L₁' ⋙ blockSum s₂' L₂'` be composites of
two block sums, compared along maps of index sets `r₀, r₁, r₂` by blockwise restrictions
`P₀, P₁, P₂`. Crossing the restriction through the two block sums, one after the other, acts on
the generators `gen₂` of the composite as the two blockwise crossings followed by the image of
the generator (`gen₂_blockResCross_two`).

In Webster's 2-representation (arXiv:1309.3796v3, §4.6, proof of Theorem 4.25) this moves a
red line through two downward black strands on the weight spaces of the cyclotomic family.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

variable {A B Dd A' B' Dd' : Type*} (s₁ : A → B) (s₂ : B → Dd) (s₁' : A' → B') (s₂' : B' → Dd')
  (r₀ : A' → A) (r₁ : B' → B) (r₂ : Dd' → Dd)
  (hc₁ : ∀ a', s₁ (r₀ a') = r₁ (s₁' a')) (hc₂ : ∀ b', s₂ (r₁ b') = r₂ (s₂' b'))
  [∀ b, Finite {a // s₁ a = b}] [∀ d, Finite {b // s₂ b = d}]
  [∀ b, Finite {a // s₁' a = b}] [∀ d, Finite {b // s₂' b = d}]
  {C : A → Type*} [∀ a, Category (C a)]
  {Mid : B → Type*} [∀ b, Category (Mid b)] [∀ b, Preadditive (Mid b)]
  [∀ b, HasFiniteBiproducts (Mid b)]
  {D : Dd → Type*} [∀ d, Category (D d)] [∀ d, Preadditive (D d)]
  [∀ d, HasFiniteBiproducts (D d)]
  {C' : A' → Type*} [∀ a, Category (C' a)]
  {Mid' : B' → Type*} [∀ b, Category (Mid' b)] [∀ b, Preadditive (Mid' b)]
  [∀ b, HasFiniteBiproducts (Mid' b)]
  {D' : Dd' → Type*} [∀ d, Category (D' d)] [∀ d, Preadditive (D' d)]
  [∀ d, HasFiniteBiproducts (D' d)]
  (L₁ : ∀ (a : A) (b : B), s₁ a = b → C a ⥤ Mid b) (L₂ : ∀ (b : B) (d : Dd), s₂ b = d → Mid b ⥤ D d)
  (L₁' : ∀ (a : A') (b : B'), s₁' a = b → C' a ⥤ Mid' b)
  (L₂' : ∀ (b : B') (d : Dd'), s₂' b = d → Mid' b ⥤ D' d)
  (P₀ : ∀ (a' : A') (a : A), r₀ a' = a → C a ⥤ C' a')
  (P₁ : ∀ (b' : B') (b : B), r₁ b' = b → Mid b ⥤ Mid' b')
  (P₂ : ∀ (d' : Dd') (d : Dd), r₂ d' = d → D d ⥤ D' d')
  (α : ∀ (a' : A') (b' : B') (h : s₁' a' = b'),
    P₀ a' (r₀ a') rfl ⋙ L₁' a' b' h ⟶
      L₁ (r₀ a') (r₁ b') ((hc₁ a').trans (congrArg r₁ h)) ⋙ P₁ b' (r₁ b') rfl)
  (α' : ∀ (b' : B') (d' : Dd') (h : s₂' b' = d'),
    P₁ b' (r₁ b') rfl ⋙ L₂' b' d' h ⟶
      L₂ (r₁ b') (r₂ d') ((hc₂ b').trans (congrArg r₂ h)) ⋙ P₂ d' (r₂ d') rfl)

/-- **Two successive block crossings on generators.** -/
theorem gen₂_blockResCross_two (N : ∀ a, C a) (a' : A') {b' : B'} {d' : Dd'}
    (e₁ : s₁' a' = b') (e₂ : s₂' b' = d') :
    gen₂ s₁' s₂' L₁' L₂' ((blockRes r₀ P₀).obj N) a' e₁ e₂ ≫
        (blockSum s₂' L₂').map ((blockResCross s₁ s₁' r₀ r₁ hc₁ L₁ L₁' P₀ P₁ α).app N) d' ≫
        (blockResCross s₂ s₂' r₁ r₂ hc₂ L₂ L₂' P₁ P₂ α').app ((blockSum s₁ L₁).obj N) d' =
      (L₂' b' d' e₂).map ((α a' b' e₁).app (N (r₀ a'))) ≫
        (α' b' d' e₂).app ((L₁ (r₀ a') (r₁ b') ((hc₁ a').trans (congrArg r₁ e₁))).obj
          (N (r₀ a'))) ≫
        (P₂ d' (r₂ d') rfl).map (gen₂ s₁ s₂ L₁ L₂ N (r₀ a') ((hc₁ a').trans (congrArg r₁ e₁))
          ((hc₂ b').trans (congrArg r₂ e₂))) := by
  rw [gen₂, Category.assoc, ← Category.assoc (blockι _ _ _ _), blockι_map, Category.assoc,
    ← Category.assoc, ← Functor.map_comp]
  erw [blockι_blockResCrossApp]
  erw [blockι_blockResCrossApp]
  rw [Functor.map_comp, Category.assoc]
  erw [(α' b' d' e₂).naturality_assoc]
  rw [gen₂, Functor.map_comp]
  rfl

end

end Categorification.TwoRep
