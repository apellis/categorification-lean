/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Symmetries
import Categorification.TwoRep.BlockSumCross

/-!
# Whiskered blockwise transformations on generators

For composites of two block sums, whiskering a blockwise transformation (`blockSumMap`) on
either side acts on the generators `gen₂` as the corresponding whiskering of the blocks
(`gen₂_whiskerLeft`, `gen₂_whiskerRight`).

`compatSubalgebra` is the subalgebra of pairs `(f, g) ∈ End G × End L` of endomorphisms of a
`k`-linear functor `G` (a 1-cell of `LinearCat k`) and of a functor `L` that are intertwined by a
fixed family of maps `ι M : L (e M) ⟶ π (G M)`. Consequently noncommutative polynomial
evaluations in compatible endomorphisms are compatible (`ncEval_compat`). This reduces the
polynomial relations of the weight-indexed cyclotomic Rouquier family (KL III Thm. 1.2;
Brundan, arXiv:1501.00350v1, (1.3), (1.4)) to the corresponding relations on blocks.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

section Whisker

variable {A B Dd : Type*} (s₁ : A → B) (s₂ : B → Dd) [∀ b, Finite {a // s₁ a = b}]
  [∀ d, Finite {b // s₂ b = d}]
  {C : A → Type*} [∀ a, Category (C a)]
  {Mid : B → Type*} [∀ b, Category (Mid b)] [∀ b, Preadditive (Mid b)]
  [∀ b, HasFiniteBiproducts (Mid b)]
  {D : Dd → Type*} [∀ d, Category (D d)] [∀ d, Preadditive (D d)]
  [∀ d, HasFiniteBiproducts (D d)]

/-- Whiskering a blockwise transformation of the outer block sum, on generators. -/
theorem gen₂_whiskerLeft (L₁ : ∀ (a : A) (b : B), s₁ a = b → C a ⥤ Mid b)
    {L₂ L₂' : ∀ (b : B) (d : Dd), s₂ b = d → Mid b ⥤ D d}
    (α : ∀ (b : B) (d : Dd) (h : s₂ b = d), L₂ b d h ⟶ L₂' b d h) (M : ∀ a, C a) (a : A)
    {b : B} {d : Dd} (h₁ : s₁ a = b) (h₂ : s₂ b = d) :
    gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ (blockSumMap s₂ α).app ((blockSum s₁ L₁).obj M) d =
      (α b d h₂).app ((L₁ a b h₁).obj (M a)) ≫ gen₂ s₁ s₂ L₁ L₂' M a h₁ h₂ := by
  rw [gen₂, Category.assoc, blockι_blockSumMap, ← Category.assoc, (α b d h₂).naturality,
    Category.assoc]
  rfl

/-- Whiskering a blockwise transformation of the inner block sum, on generators. -/
theorem gen₂_whiskerRight {L₁ L₁' : ∀ (a : A) (b : B), s₁ a = b → C a ⥤ Mid b}
    (L₂ : ∀ (b : B) (d : Dd), s₂ b = d → Mid b ⥤ D d)
    (α : ∀ (a : A) (b : B) (h : s₁ a = b), L₁ a b h ⟶ L₁' a b h) (M : ∀ a, C a) (a : A)
    {b : B} {d : Dd} (h₁ : s₁ a = b) (h₂ : s₂ b = d) :
    gen₂ s₁ s₂ L₁ L₂ M a h₁ h₂ ≫ (blockSum s₂ L₂).map ((blockSumMap s₁ α).app M) d =
      (L₂ b d h₂).map ((α a b h₁).app (M a)) ≫ gen₂ s₁ s₂ L₁' L₂ M a h₁ h₂ := by
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp,
    blockι_blockSumMap, Functor.map_comp, Category.assoc]
  rfl

end Whisker

section Compat

variable {k : Type*} [CommRing k] {𝒞 𝒟 : LinearCat k} (G : 𝒞 ⟶ 𝒟)
  {P R : Type*} [Category P] [Category R] [Preadditive R]
  [Linear k R] (L : P ⥤ R) (e : 𝒞 → P) (π : (𝒟 : Type _) ⥤ R) [π.Additive] [π.Linear k]
  (ι : ∀ M : 𝒞, L.obj (e M) ⟶ π.obj (G.obj.obj M))

/-- Pairs of endomorphisms of `G` and of `L` intertwined by `ι`. -/
def compatSubalgebra : Subalgebra k (End G × End L) where
  carrier := {x | ∀ M, ι M ≫ π.map (x.1.hom.app M) = x.2.app (e M) ≫ ι M}
  mul_mem' {x y} hx hy M := by
    change ι M ≫ π.map ((y.1 ≫ x.1).hom.app M) = (y.2 ≫ x.2).app (e M) ≫ ι M
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, π.map_comp,
      ← Category.assoc, hy M, Category.assoc, hx M, NatTrans.comp_app, Category.assoc]
  add_mem' {x y} hx hy M := by
    change ι M ≫ π.map ((x.1 + y.1).hom.app M) = (x.2 + y.2).app (e M) ≫ ι M
    rw [show (x.1 + y.1).hom = x.1.hom + y.1.hom from rfl, NatTrans.app_add, π.map_add,
      Preadditive.comp_add, hx M, hy M, NatTrans.app_add, Preadditive.add_comp]
  algebraMap_mem' c M := by
    change ι M ≫ π.map ((c • 𝟙 G : G ⟶ G).hom.app M) = (c • 𝟙 L : L ⟶ L).app (e M) ≫ ι M
    rw [LinearCat.smul_hom, NatTrans.app_smul, π.map_smul, Linear.comp_smul, NatTrans.app_smul,
      Linear.smul_comp, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, NatTrans.id_app,
      π.map_id, Category.comp_id, Category.id_comp]

/-- **Polynomial evaluations in compatible endomorphisms are compatible.** -/
theorem ncEval_compat {n : ℕ} (y : Fin n → End G) (z : Fin n → End L)
    (h : ∀ c M, ι M ≫ π.map ((y c).hom.app M) = (z c).app (e M) ≫ ι M)
    (p : MvPolynomial (Fin n) k) (M : 𝒞) :
    ι M ≫ π.map ((KLR.ncEval y p).hom.app M) = (KLR.ncEval z p).app (e M) ≫ ι M := by
  let S := compatSubalgebra G L e π ι
  let w : Fin n → S := fun c => ⟨(y c, z c), h c⟩
  have h₁ : KLR.ncEval y p = ((AlgHom.fst k _ _).comp S.val) (KLR.ncEval w p) := by
    rw [KLR.ncEval_map]
    rfl
  have h₂ : KLR.ncEval z p = ((AlgHom.snd k _ _).comp S.val) (KLR.ncEval w p) := by
    rw [KLR.ncEval_map]
    rfl
  rw [h₁, h₂]
  exact (KLR.ncEval w p).2 M

end Compat

end

end Categorification.TwoRep
