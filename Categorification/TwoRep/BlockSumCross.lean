/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSum

/-!
# Composites of block-sum functors and blockwise transformations between them

For index maps `s₁ : A → B`, `s₂ : B → D`, the composite `blockSum s₁ L₁ ⋙ blockSum s₂ L₂`
has, on the block `a`, an intermediate index `b` with `s₁ a = b` and a target `d` with
`s₂ b = d`, the generator `gen₂ : L₂ (L₁ (M a)) ⟶ (blockSum s₁ L₁ ⋙ blockSum s₂ L₂).obj M d`.
Maps out of the composite are determined by their restrictions to these generators when `L₂` is
additive (`gen₂_ext`).

Given a second factorization with `s₂' ∘ s₁' = s₂ ∘ s₁` and blockwise natural transformations
`τ : L₁ ⋙ L₂ ⟶ L₁' ⋙ L₂'` (for all intermediate indices on both sides), `blockCross τ` is the
transformation of composites that is `τ` on each generator (`gen₂_blockCross`). This assembles
the crossings of the weight-indexed cyclotomic Rouquier family of KL III Thm. 1.2 from the
crossings of cyclotomic induction functors.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

section Comparison

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] (F : C ⥤ D) [F.Additive] {J : Type*} [Finite J]
  (f : J → C)

theorem map_ι_biproductComparison (j : J) :
    F.map (biproduct.ι f j) ≫ F.biproductComparison f = biproduct.ι (F.obj ∘ f) j := by
  classical
  refine biproduct.hom_ext _ _ fun j' => ?_
  rw [Category.assoc, Functor.biproductComparison_π, ← F.map_comp, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h
  · subst h
    simp
  · simp

omit [HasFiniteBiproducts D] in
theorem map_biproduct_hom_ext {X : D} {g g' : F.obj (⨁ f) ⟶ X}
    (h : ∀ j, F.map (biproduct.ι f j) ≫ g = F.map (biproduct.ι f j) ≫ g') : g = g' := by
  classical
  have := Fintype.ofFinite J
  have ht : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
    IsBilimit.total (biproduct.isBilimit _)
  rw [← Category.id_comp g, ← Category.id_comp g', ← F.map_id, ← ht, F.map_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [F.map_comp, Category.assoc, Category.assoc, h j]

end Comparison

section Two

variable {A B Dd : Type*} (s₁ : A → B) (s₂ : B → Dd) [∀ b, Finite {a // s₁ a = b}]
  [∀ d, Finite {b // s₂ b = d}]
  {C : A → Type*} [∀ a, Category (C a)]
  {Mid : B → Type*} [∀ b, Category (Mid b)] [∀ b, Preadditive (Mid b)]
  [∀ b, HasFiniteBiproducts (Mid b)]
  {D : Dd → Type*} [∀ d, Category (D d)] [∀ d, Preadditive (D d)]
  [∀ d, HasFiniteBiproducts (D d)]
  (L₁ : ∀ (a : A) (b : B), s₁ a = b → C a ⥤ Mid b) (L₂ : ∀ (b : B) (d : Dd), s₂ b = d → Mid b ⥤ D d)

/-- The generator of the composite of two block sums on the block `a`, through the intermediate
index `b = s₁ a`, at a target `d = s₂ b`. -/
def gen₂ (M : ∀ a, C a) (a : A) {b : B} {d : Dd} (h₁ : s₁ a = b) (h₂ : s₂ b = d) :
    (L₂ b d h₂).obj ((L₁ a b h₁).obj (M a)) ⟶ (blockSum s₁ L₁ ⋙ blockSum s₂ L₂).obj M d :=
  (L₂ b d h₂).map (blockι s₁ L₁ M (⟨a, h₁⟩ : {a' // s₁ a' = b})) ≫
    blockι s₂ L₂ ((blockSum s₁ L₁).obj M) (⟨b, h₂⟩ : {b' // s₂ b' = d})

/-- Maps out of a composite of two block sums are determined on generators. -/
theorem gen₂_ext [∀ b d h, (L₂ b d h).Additive] {M : ∀ a, C a} {N : ∀ d, D d}
    {f g : (blockSum s₁ L₁ ⋙ blockSum s₂ L₂).obj M ⟶ N}
    (H : ∀ (a : A) (b : B) (d : Dd) (h₁ : s₁ a = b) (h₂ : s₂ b = d),
      gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ f d = gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ g d) : f = g := by
  funext d
  refine biproduct.hom_ext' _ _ fun p => ?_
  obtain ⟨b, hb⟩ := p
  refine map_biproduct_hom_ext (L₂ b d hb) _ fun q => ?_
  obtain ⟨a, ha⟩ := q
  have := H a b d ha hb
  simp only [gen₂, Category.assoc] at this
  exact this

theorem gen₂_map {M M' : ∀ a, C a} (f : M ⟶ M') (a : A) {b : B} {d : Dd} (h₁ : s₁ a = b)
    (h₂ : s₂ b = d) :
    gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ (blockSum s₁ L₁ ⋙ blockSum s₂ L₂).map f d =
      (L₂ b d h₂).map ((L₁ a b h₁).map (f a)) ≫ gen₂ s₁ s₂ L₁ L₂ M' a h₁ h₂ := by
  change ((L₂ b d h₂).map (blockι s₁ L₁ M ⟨a, h₁⟩) ≫ blockι s₂ L₂ _ ⟨b, h₂⟩) ≫
      (blockSum s₂ L₂).map ((blockSum s₁ L₁).map f) d = _
  rw [Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  erw [blockι_map]
  rw [Functor.map_comp, Category.assoc]
  rfl

section Cross

variable {B' : Type*} (s₁' : A → B') (s₂' : B' → Dd) [∀ b, Finite {a // s₁' a = b}]
  [∀ d, Finite {b // s₂' b = d}]
  {Mid' : B' → Type*} [∀ b, Category (Mid' b)] [∀ b, Preadditive (Mid' b)]
  [∀ b, HasFiniteBiproducts (Mid' b)]
  (L₁' : ∀ (a : A) (b : B'), s₁' a = b → C a ⥤ Mid' b)
  (L₂' : ∀ (b : B') (d : Dd), s₂' b = d → Mid' b ⥤ D d)
  (hc : ∀ a, s₂ (s₁ a) = s₂' (s₁' a))
  (τ : ∀ (a : A) (b : B) (b' : B') (d : Dd) (h₁ : s₁ a = b) (h₂ : s₂ b = d) (h₁' : s₁' a = b')
    (h₂' : s₂' b' = d), L₁ a b h₁ ⋙ L₂ b d h₂ ⟶ L₁' a b' h₁' ⋙ L₂' b' d h₂')

include hc in
omit [∀ b, Finite {a // s₁ a = b}] [∀ d, Finite {b // s₂ b = d}]
  [∀ b, Finite {a // s₁' a = b}] [∀ d, Finite {b // s₂' b = d}] in
theorem cross_target {a : A} {b : B} {d : Dd} (h₁ : s₁ a = b) (h₂ : s₂ b = d) :
    s₂' (s₁' a) = d :=
  (hc a).symm.trans ((congrArg s₂ h₁).trans h₂)

/-- The image of the block `a` under the blockwise transformation. -/
def crossAt (M : ∀ a, C a) (b : B) (d : Dd) (h₂ : s₂ b = d) (a : A) (h₁ : s₁ a = b) :
    (L₂ b d h₂).obj ((L₁ a b h₁).obj (M a)) ⟶ (blockSum s₁' L₁' ⋙ blockSum s₂' L₂').obj M d :=
  (τ a b (s₁' a) d h₁ h₂ rfl (cross_target s₁ s₂ s₁' s₂' hc h₁ h₂)).app (M a) ≫
    gen₂ s₁' s₂' L₁' L₂' M a rfl (cross_target s₁ s₂ s₁' s₂' hc h₁ h₂)

variable [∀ b d h, (L₂ b d h).Additive]

/-- The components of `blockCross`. -/
def blockCrossApp (M : ∀ a, C a) (d : Dd) :
    (blockSum s₁ L₁ ⋙ blockSum s₂ L₂).obj M d ⟶ (blockSum s₁' L₁' ⋙ blockSum s₂' L₂').obj M d :=
  biproduct.desc fun p => (L₂ p.1 d p.2).biproductComparison _ ≫
    biproduct.desc fun q => crossAt s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M p.1 d p.2 q.1 q.2

theorem gen₂_blockCrossApp (M : ∀ a, C a) (a : A) {b : B} {d : Dd} (h₁ : s₁ a = b)
    (h₂ : s₂ b = d) :
    gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ blockCrossApp s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M d =
      crossAt s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M b d h₂ a h₁ := by
  rw [gen₂, blockCrossApp, Category.assoc]
  erw [biproduct.ι_desc]
  rw [← Category.assoc]
  erw [map_ι_biproductComparison (L₂ b d h₂)
    (fun q : {a' // s₁ a' = b} => (L₁ q.1 b q.2).obj (M q.1))]
  erw [biproduct.ι_desc]

/-- **Blockwise transformations of composites of block sums assemble.** -/
def blockCross : blockSum s₁ L₁ ⋙ blockSum s₂ L₂ ⟶ blockSum s₁' L₁' ⋙ blockSum s₂' L₂' where
  app M := blockCrossApp s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M
  naturality M M' f := gen₂_ext s₁ s₂ L₁ L₂ fun a b d h₁ h₂ => by
    change gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ (blockSum s₁ L₁ ⋙ blockSum s₂ L₂).map f d ≫
        blockCrossApp s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M' d =
      gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ blockCrossApp s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M d ≫
        (blockSum s₁' L₁' ⋙ blockSum s₂' L₂').map f d
    rw [← Category.assoc, gen₂_map, Category.assoc, gen₂_blockCrossApp,
      ← Category.assoc (gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂), gen₂_blockCrossApp, crossAt, crossAt,
      Category.assoc, gen₂_map, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (τ a b (s₁' a) d h₁ h₂ rfl _).naturality (f a)

/-- **`blockCross` is `τ` on generators**, for any intermediate indices on both sides. -/
@[simp] theorem gen₂_blockCross (M : ∀ a, C a) (a : A) {b : B} {b' : B'} {d : Dd}
    (h₁ : s₁ a = b) (h₂ : s₂ b = d) (h₁' : s₁' a = b') (h₂' : s₂' b' = d) :
    gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ (blockCross s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ).app M d =
      (τ a b b' d h₁ h₂ h₁' h₂').app (M a) ≫ gen₂ s₁' s₂' L₁' L₂' M a h₁' h₂' := by
  subst h₁'
  exact gen₂_blockCrossApp s₁ s₂ L₁ L₂ s₁' s₂' L₁' L₂' hc τ M a h₁ h₂

end Cross

end Two

end

end Categorification.TwoRep
