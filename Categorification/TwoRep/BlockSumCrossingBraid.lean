/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossingGen

/-!
# Block restrictions passing through a crossing of block sums

Let `blockCross τ : blockSum s₁ L₁ ⋙ blockSum s₂ L₂ ⟶ blockSum t₁ K₁ ⋙ blockSum t₂ K₂` be a
crossing of two composites of block sums, assembled from blockwise transformations `τ`, and let
`blockCross τ'` be a second one on blocks indexed by `A'`. Blockwise restrictions `P₀, …, P₃`
along maps of index sets, together with blockwise crossings `α₁, α₂` (along the route `s`) and
`β₁, β₂` (along the route `t`), give two ways of moving a block restriction through the
crossing. They agree when they agree on each block (`blockResCross_blockCross_app`).

In Webster's 2-representation (arXiv:1309.3796v3, §4.6, proof of Theorem 4.25) this moves a
red line through a crossing of two downward black strands on the weight spaces of the
cyclotomic family, relation (4.4d) read downward.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

section Hexagon

variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category C₃] [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁} {P₂ : C₂ ⥤ D₂} {P₃ : C₃ ⥤ D₃}
  {A₁ : C₀ ⥤ C₁} {A₂ : C₁ ⥤ C₂} {A₃ : C₀ ⥤ C₃} {A₄ : C₃ ⥤ C₂}
  {B₁ : D₀ ⥤ D₁} {B₂ : D₁ ⥤ D₂} {B₃ : D₀ ⥤ D₃} {B₄ : D₃ ⥤ D₂}

/-- The hexagon moving a functor `P` through the crossings `cA`, `cB` by the crossings
`q₁, …, q₄`, at an object `N`: the two ways of passing `P` through two strands and their
crossing agree. -/
def CrossHexagon (q₁ : P₀ ⋙ B₁ ⟶ A₁ ⋙ P₁) (q₂ : P₁ ⋙ B₂ ⟶ A₂ ⋙ P₂)
    (q₃ : P₀ ⋙ B₃ ⟶ A₃ ⋙ P₃) (q₄ : P₃ ⋙ B₄ ⟶ A₄ ⋙ P₂) (cA : A₁ ⋙ A₂ ⟶ A₃ ⋙ A₄)
    (cB : B₁ ⋙ B₂ ⟶ B₃ ⋙ B₄) (N : C₀) : Prop :=
  B₂.map (q₁.app N) ≫ q₂.app (A₁.obj N) ≫ P₂.map (cA.app N) =
    cB.app (P₀.obj N) ≫ B₄.map (q₃.app N) ≫ q₄.app (A₃.obj N)

end Hexagon

variable {A B B₂ Dd A' B' B₂' Dd' : Type*}
  (s₁ : A → B) (s₂ : B → Dd) (t₁ : A → B₂) (t₂ : B₂ → Dd)
  (s₁' : A' → B') (s₂' : B' → Dd') (t₁' : A' → B₂') (t₂' : B₂' → Dd')
  (r₀ : A' → A) (r₁ : B' → B) (r₃ : B₂' → B₂) (r₂ : Dd' → Dd)
  (hs₁ : ∀ a', s₁ (r₀ a') = r₁ (s₁' a')) (hs₂ : ∀ b', s₂ (r₁ b') = r₂ (s₂' b'))
  (ht₁ : ∀ a', t₁ (r₀ a') = r₃ (t₁' a')) (ht₂ : ∀ c', t₂ (r₃ c') = r₂ (t₂' c'))
  (hc : ∀ a, s₂ (s₁ a) = t₂ (t₁ a)) (hc' : ∀ a', s₂' (s₁' a') = t₂' (t₁' a'))
  [∀ b, Finite {a // s₁ a = b}] [∀ d, Finite {b // s₂ b = d}]
  [∀ c, Finite {a // t₁ a = c}] [∀ d, Finite {c // t₂ c = d}]
  [∀ b, Finite {a // s₁' a = b}] [∀ d, Finite {b // s₂' b = d}]
  [∀ c, Finite {a // t₁' a = c}] [∀ d, Finite {c // t₂' c = d}]
  {C : A → Type*} [∀ a, Category (C a)]
  {Mid : B → Type*} [∀ b, Category (Mid b)] [∀ b, Preadditive (Mid b)]
  [∀ b, HasFiniteBiproducts (Mid b)]
  {Mid₂ : B₂ → Type*} [∀ c, Category (Mid₂ c)] [∀ c, Preadditive (Mid₂ c)]
  [∀ c, HasFiniteBiproducts (Mid₂ c)]
  {D : Dd → Type*} [∀ d, Category (D d)] [∀ d, Preadditive (D d)]
  [∀ d, HasFiniteBiproducts (D d)]
  {C' : A' → Type*} [∀ a, Category (C' a)]
  {Mid' : B' → Type*} [∀ b, Category (Mid' b)] [∀ b, Preadditive (Mid' b)]
  [∀ b, HasFiniteBiproducts (Mid' b)]
  {Mid₂' : B₂' → Type*} [∀ c, Category (Mid₂' c)] [∀ c, Preadditive (Mid₂' c)]
  [∀ c, HasFiniteBiproducts (Mid₂' c)]
  {D' : Dd' → Type*} [∀ d, Category (D' d)] [∀ d, Preadditive (D' d)]
  [∀ d, HasFiniteBiproducts (D' d)]
  (L₁ : ∀ (a : A) (b : B), s₁ a = b → C a ⥤ Mid b) (L₂ : ∀ (b : B) (d : Dd), s₂ b = d → Mid b ⥤ D d)
  (K₁ : ∀ (a : A) (c : B₂), t₁ a = c → C a ⥤ Mid₂ c)
  (K₂ : ∀ (c : B₂) (d : Dd), t₂ c = d → Mid₂ c ⥤ D d)
  (L₁' : ∀ (a : A') (b : B'), s₁' a = b → C' a ⥤ Mid' b)
  (L₂' : ∀ (b : B') (d : Dd'), s₂' b = d → Mid' b ⥤ D' d)
  (K₁' : ∀ (a : A') (c : B₂'), t₁' a = c → C' a ⥤ Mid₂' c)
  (K₂' : ∀ (c : B₂') (d : Dd'), t₂' c = d → Mid₂' c ⥤ D' d)
  (P₀ : ∀ (a' : A') (a : A), r₀ a' = a → C a ⥤ C' a')
  (P₁ : ∀ (b' : B') (b : B), r₁ b' = b → Mid b ⥤ Mid' b')
  (P₃ : ∀ (c' : B₂') (c : B₂), r₃ c' = c → Mid₂ c ⥤ Mid₂' c')
  (P₂ : ∀ (d' : Dd') (d : Dd), r₂ d' = d → D d ⥤ D' d')
  (τ : ∀ (a : A) (b : B) (c : B₂) (d : Dd) (h₁ : s₁ a = b) (h₂ : s₂ b = d) (h₁' : t₁ a = c)
    (h₂' : t₂ c = d), L₁ a b h₁ ⋙ L₂ b d h₂ ⟶ K₁ a c h₁' ⋙ K₂ c d h₂')
  (τ' : ∀ (a : A') (b : B') (c : B₂') (d : Dd') (h₁ : s₁' a = b) (h₂ : s₂' b = d)
    (h₁' : t₁' a = c) (h₂' : t₂' c = d), L₁' a b h₁ ⋙ L₂' b d h₂ ⟶ K₁' a c h₁' ⋙ K₂' c d h₂')
  (α₁ : ∀ (a' : A') (b' : B') (h : s₁' a' = b'),
    P₀ a' (r₀ a') rfl ⋙ L₁' a' b' h ⟶
      L₁ (r₀ a') (r₁ b') ((hs₁ a').trans (congrArg r₁ h)) ⋙ P₁ b' (r₁ b') rfl)
  (α₂ : ∀ (b' : B') (d' : Dd') (h : s₂' b' = d'),
    P₁ b' (r₁ b') rfl ⋙ L₂' b' d' h ⟶
      L₂ (r₁ b') (r₂ d') ((hs₂ b').trans (congrArg r₂ h)) ⋙ P₂ d' (r₂ d') rfl)
  (β₁ : ∀ (a' : A') (c' : B₂') (h : t₁' a' = c'),
    P₀ a' (r₀ a') rfl ⋙ K₁' a' c' h ⟶
      K₁ (r₀ a') (r₃ c') ((ht₁ a').trans (congrArg r₃ h)) ⋙ P₃ c' (r₃ c') rfl)
  (β₂ : ∀ (c' : B₂') (d' : Dd') (h : t₂' c' = d'),
    P₃ c' (r₃ c') rfl ⋙ K₂' c' d' h ⟶
      K₂ (r₃ c') (r₂ d') ((ht₂ c').trans (congrArg r₂ h)) ⋙ P₂ d' (r₂ d') rfl)

omit [∀ b, Finite {a // s₁ a = b}] [∀ d, Finite {b // s₂ b = d}]
  [∀ b, HasFiniteBiproducts (Mid b)] [∀ b, Preadditive (Mid b)] in
/-- The crossing `τ` followed by a generator does not depend on the name of the intermediate
index. -/
theorem crossing_gen₂_index (M : ∀ a, C a) (a : A) {b : B} {c : B₂} {d : Dd} (h₁ : s₁ a = b)
    (h₂ : s₂ b = d) (h₁' : t₁ a = c) (h₂' : t₂ c = d) :
    (τ a b c d h₁ h₂ h₁' h₂').app (M a) ≫ gen₂ t₁ t₂ K₁ K₂ M a h₁' h₂' =
      (τ a b (t₁ a) d h₁ h₂ rfl ((congrArg t₂ h₁').trans h₂')).app (M a) ≫
        gen₂ t₁ t₂ K₁ K₂ M a rfl ((congrArg t₂ h₁').trans h₂') := by
  subst h₁'
  rfl

variable [∀ b d h, (L₂ b d h).Additive] [∀ b d h, (L₂' b d h).Additive]

/-- **A block restriction passes through a crossing of block sums**, on components: the two
ways of moving the restrictions `P` through the crossings `τ`, `τ'` agree when they agree on
each block. -/
theorem blockResCross_blockCross_app
    (H : ∀ (a' : A') (b' : B') (c' : B₂') (d' : Dd') (e₁ : s₁' a' = b') (e₂ : s₂' b' = d')
      (e₃ : t₁' a' = c') (e₄ : t₂' c' = d') (Z : C (r₀ a')),
      (L₂' b' d' e₂).map ((α₁ a' b' e₁).app Z) ≫
          (α₂ b' d' e₂).app ((L₁ (r₀ a') (r₁ b') ((hs₁ a').trans (congrArg r₁ e₁))).obj Z) ≫
          (P₂ d' (r₂ d') rfl).map ((τ (r₀ a') (r₁ b') (r₃ c') (r₂ d')
            ((hs₁ a').trans (congrArg r₁ e₁)) ((hs₂ b').trans (congrArg r₂ e₂))
            ((ht₁ a').trans (congrArg r₃ e₃)) ((ht₂ c').trans (congrArg r₂ e₄))).app Z) =
        (τ' a' b' c' d' e₁ e₂ e₃ e₄).app ((P₀ a' (r₀ a') rfl).obj Z) ≫
          (K₂' c' d' e₄).map ((β₁ a' c' e₃).app Z) ≫
          (β₂ c' d' e₄).app ((K₁ (r₀ a') (r₃ c') ((ht₁ a').trans (congrArg r₃ e₃))).obj Z))
    (N : ∀ a, C a) :
    (blockSum s₂' L₂').map ((blockResCross s₁ s₁' r₀ r₁ hs₁ L₁ L₁' P₀ P₁ α₁).app N) ≫
        (blockResCross s₂ s₂' r₁ r₂ hs₂ L₂ L₂' P₁ P₂ α₂).app ((blockSum s₁ L₁).obj N) ≫
        (blockRes r₂ P₂).map ((blockCross s₁ s₂ L₁ L₂ t₁ t₂ K₁ K₂ hc τ).app N) =
      (blockCross s₁' s₂' L₁' L₂' t₁' t₂' K₁' K₂' hc' τ').app ((blockRes r₀ P₀).obj N) ≫
        (blockSum t₂' K₂').map ((blockResCross t₁ t₁' r₀ r₃ ht₁ K₁ K₁' P₀ P₃ β₁).app N) ≫
        (blockResCross t₂ t₂' r₃ r₂ ht₂ K₂ K₂' P₃ P₂ β₂).app ((blockSum t₁ K₁).obj N) := by
  refine gen₂_ext s₁' s₂' L₁' L₂' fun a' b' d' e₁ e₂ => ?_
  have hL := gen₂_blockResCross_two s₁ s₂ s₁' s₂' r₀ r₁ r₂ hs₁ hs₂ L₁ L₂ L₁' L₂' P₀ P₁ P₂ α₁ α₂
    N a' e₁ e₂
  have hR := gen₂_blockResCross_two t₁ t₂ t₁' t₂' r₀ r₃ r₂ ht₁ ht₂ K₁ K₂ K₁' K₂' P₀ P₃ P₂ β₁ β₂
    N a' rfl (cross_target s₁' s₂' t₁' t₂' hc' e₁ e₂)
  have hC := gen₂_blockCrossApp s₁ s₂ L₁ L₂ t₁ t₂ K₁ K₂ hc τ N (r₀ a')
    ((hs₁ a').trans (congrArg r₁ e₁)) ((hs₂ b').trans (congrArg r₂ e₂))
  have hC' := gen₂_blockCrossApp s₁' s₂' L₁' L₂' t₁' t₂' K₁' K₂' hc' τ' ((blockRes r₀ P₀).obj N)
    a' e₁ e₂
  change gen₂ s₁' s₂' L₁' L₂' _ a' e₁ e₂ ≫
      (blockSum s₂' L₂').map ((blockResCross s₁ s₁' r₀ r₁ hs₁ L₁ L₁' P₀ P₁ α₁).app N) d' ≫
        (blockResCross s₂ s₂' r₁ r₂ hs₂ L₂ L₂' P₁ P₂ α₂).app ((blockSum s₁ L₁).obj N) d' ≫
        (P₂ d' (r₂ d') rfl).map ((blockCross s₁ s₂ L₁ L₂ t₁ t₂ K₁ K₂ hc τ).app N (r₂ d')) =
    gen₂ s₁' s₂' L₁' L₂' _ a' e₁ e₂ ≫
      (blockCross s₁' s₂' L₁' L₂' t₁' t₂' K₁' K₂' hc' τ').app ((blockRes r₀ P₀).obj N) d' ≫
        (blockSum t₂' K₂').map ((blockResCross t₁ t₁' r₀ r₃ ht₁ K₁ K₁' P₀ P₃ β₁).app N) d' ≫
        (blockResCross t₂ t₂' r₃ r₂ ht₂ K₂ K₂' P₃ P₂ β₂).app ((blockSum t₁ K₁).obj N) d'
  erw [reassoc_of% hL]
  rw [← Category.assoc (gen₂ s₁' s₂' L₁' L₂' _ a' e₁ e₂)]
  erw [hC']
  rw [crossAt, Category.assoc, hR, ← Functor.map_comp]
  erw [hC]
  have hI := crossing_gen₂_index s₁ s₂ t₁ t₂ L₁ L₂ K₁ K₂ τ N (r₀ a')
    ((hs₁ a').trans (congrArg r₁ e₁)) ((hs₂ b').trans (congrArg r₂ e₂))
    ((ht₁ a').trans (congrArg r₃ (rfl : t₁' a' = t₁' a')))
    ((ht₂ (t₁' a')).trans (congrArg r₂ (cross_target s₁' s₂' t₁' t₂' hc' e₁ e₂)))
  rw [crossAt]
  erw [← hI]
  rw [Functor.map_comp, reassoc_of% (H a' b' (t₁' a') d' e₁ e₂ rfl
    (cross_target s₁' s₂' t₁' t₂' hc' e₁ e₂) (N (r₀ a')))]

end

section Rev

variable {A Dd : Type*} (s : A → Dd) [∀ d, Finite {a // s a = d}]
  {C₀ C₁ C₂ C₃ : A → Type*} [∀ a, Category (C₀ a)] [∀ a, Category (C₁ a)]
  [∀ a, Category (C₂ a)] [∀ a, Category (C₃ a)]
  {D₀ D₁ D₂ D₃ : Dd → Type*} [∀ d, Category (D₀ d)] [∀ d, Category (D₁ d)]
  [∀ d, Category (D₂ d)] [∀ d, Category (D₃ d)]
  [∀ d, Preadditive (D₀ d)] [∀ d, Preadditive (D₁ d)] [∀ d, Preadditive (D₂ d)]
  [∀ d, Preadditive (D₃ d)] [∀ d, HasFiniteBiproducts (D₀ d)] [∀ d, HasFiniteBiproducts (D₁ d)]
  [∀ d, HasFiniteBiproducts (D₂ d)] [∀ d, HasFiniteBiproducts (D₃ d)]
  (L₀ : ∀ (a : A) (d : Dd), s a = d → C₀ a ⥤ D₀ d) (L₁ : ∀ (a : A) (d : Dd), s a = d → C₁ a ⥤ D₁ d)
  (L₂ : ∀ (a : A) (d : Dd), s a = d → C₂ a ⥤ D₂ d) (L₃ : ∀ (a : A) (d : Dd), s a = d → C₃ a ⥤ D₃ d)
  (E₁ : ∀ (a' a : A), id a' = a → C₀ a ⥤ C₁ a') (E₂ : ∀ (a' a : A), id a' = a → C₁ a ⥤ C₂ a')
  (E₃ : ∀ (a' a : A), id a' = a → C₀ a ⥤ C₃ a') (E₄ : ∀ (a' a : A), id a' = a → C₃ a ⥤ C₂ a')
  (F₁ : ∀ (d' d : Dd), id d' = d → D₀ d ⥤ D₁ d') (F₂ : ∀ (d' d : Dd), id d' = d → D₁ d ⥤ D₂ d')
  (F₃ : ∀ (d' d : Dd), id d' = d → D₀ d ⥤ D₃ d') (F₄ : ∀ (d' d : Dd), id d' = d → D₃ d ⥤ D₂ d')
  (q₁ : ∀ (a : A) (d : Dd) (h : s a = d), L₀ a d h ⋙ F₁ d d rfl ⟶ E₁ a a rfl ⋙ L₁ a d h)
  (q₂ : ∀ (a : A) (d : Dd) (h : s a = d), L₁ a d h ⋙ F₂ d d rfl ⟶ E₂ a a rfl ⋙ L₂ a d h)
  (q₃ : ∀ (a : A) (d : Dd) (h : s a = d), L₀ a d h ⋙ F₃ d d rfl ⟶ E₃ a a rfl ⋙ L₃ a d h)
  (q₄ : ∀ (a : A) (d : Dd) (h : s a = d), L₃ a d h ⋙ F₄ d d rfl ⟶ E₄ a a rfl ⋙ L₂ a d h)
  (σ : ∀ a, E₁ a a rfl ⋙ E₂ a a rfl ⟶ E₃ a a rfl ⋙ E₄ a a rfl)
  (σ' : ∀ d, F₁ d d rfl ⋙ F₂ d d rfl ⟶ F₃ d d rfl ⋙ F₄ d d rfl)

/-- Blockwise crossings `σ` assembled on block restrictions along the identity. -/
def blockResIdCross : blockRes id E₁ ⋙ blockRes id E₂ ⟶ blockRes id E₃ ⋙ blockRes id E₄ where
  app N a := (σ a).app (N a)
  naturality _ _ f := funext fun a => (σ a).naturality (f a)

/-- **A reverse block crossing passes through blockwise crossings**, on components: when the
blockwise reverse crossings `q` move a block sum through the crossings `σ`, `σ'` on each
block, the assembled reverse crossings do too. -/
private theorem blockResCrossRev_cross_app
    (H : ∀ (a : A) (d : Dd) (h : s a = d) (Z : C₀ a),
      CrossHexagon (q₁ a d h) (q₂ a d h) (q₃ a d h) (q₄ a d h) (σ a) (σ' d) Z)
    (N : ∀ a, C₀ a) (d : Dd) :
    (F₂ d d rfl).map (blockResCrossRevApp s s id id (fun _ => rfl) L₀ L₁ E₁ F₁ q₁ N d) ≫
        blockResCrossRevApp s s id id (fun _ => rfl) L₁ L₂ E₂ F₂ q₂ ((blockRes id E₁).obj N) d ≫
        biproduct.map (fun p : {a // s a = d} => (L₂ p.1 d p.2).map ((σ p.1).app (N p.1))) =
      (σ' d).app ((blockSum s L₀).obj N d) ≫
        (F₄ d d rfl).map (blockResCrossRevApp s s id id (fun _ => rfl) L₀ L₃ E₃ F₃ q₃ N d) ≫
        blockResCrossRevApp s s id id (fun _ => rfl) L₃ L₂ E₄ F₄ q₄ ((blockRes id E₃).obj N) d := by
  refine biproduct.hom_ext _ _ fun p => ?_
  have key := H p.1 d p.2 (N p.1)
  unfold CrossHexagon at key
  simp only [Category.assoc, biproduct.map_π]
  rw [blockResCrossRevApp_π_assoc]
  erw [← Functor.map_comp_assoc, blockResCrossRevApp_π, Functor.map_comp_assoc]
  erw [blockResCrossRevApp_π]
  erw [key]
  erw [(σ' d).naturality_assoc]
  have hq := blockResCrossRevApp_π s s id id (fun _ => rfl) L₀ L₃ E₃ F₃ q₃ N p
  erw [← Functor.map_comp_assoc (F₄ d d rfl), ← Functor.map_comp_assoc (F₄ d d rfl), hq]
  rfl

/-- **A reverse block crossing passes through blockwise crossings**: when the blockwise reverse
crossings `q` move a block sum through the crossings `σ`, `σ'` on each block, the assembled
reverse crossings move it through the assembled crossings. -/
theorem blockResCrossRev_crossHexagon
    (H : ∀ (a : A) (d : Dd) (h : s a = d) (Z : C₀ a),
      CrossHexagon (q₁ a d h) (q₂ a d h) (q₃ a d h) (q₄ a d h) (σ a) (σ' d) Z)
    (N : ∀ a, C₀ a) :
    CrossHexagon (blockResCrossRev s s id id (fun _ => rfl) L₀ L₁ E₁ F₁ q₁)
      (blockResCrossRev s s id id (fun _ => rfl) L₁ L₂ E₂ F₂ q₂)
      (blockResCrossRev s s id id (fun _ => rfl) L₀ L₃ E₃ F₃ q₃)
      (blockResCrossRev s s id id (fun _ => rfl) L₃ L₂ E₄ F₄ q₄)
      (blockResIdCross E₁ E₂ E₃ E₄ σ) (blockResIdCross F₁ F₂ F₃ F₄ σ') N := by
  unfold CrossHexagon
  funext d
  exact blockResCrossRev_cross_app s L₀ L₁ L₂ L₃ E₁ E₂ E₃ E₄ F₁ F₂ F₃ F₄ q₁ q₂ q₃ q₄ σ σ' H N d

end Rev

end Categorification.TwoRep
