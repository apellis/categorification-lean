/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Categorification.TwoRep.PiLinear

/-!
# Block-sum functors between product categories

Let `s : A → D` be a map of index sets with finite fibres, `C a` and `D d` families of
preadditive categories, and `L a d h : C a ⥤ D d` a family of functors indexed by proofs
`h : s a = d`. The block-sum functor `blockSum s L : (∀ a, C a) ⥤ (∀ d, D d)` sends `M` to
`d ↦ ⨁_{a, s a = d} L (M a)`; the block-restriction functor `blockRes s R` sends `N` to
`a ↦ R (N (s a))`. Blockwise adjunctions `L ⊣ R` assemble to `blockSum s L ⊣ blockRes s R`
(`blockAdjunction`).

This is how the weight-indexed cyclotomic Rouquier family of KL III Thm. 1.2 is assembled:
`E_i` from cyclotomic inductions `R^Λ(β)-mod → R^Λ({i} + β)-mod` and `F_i` from the
corresponding restrictions, the weight space at `x` being the product of the blocks of weight `x`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
  {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)]

section Restriction

variable (R : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a)

/-- **The block-restriction functor** `N ↦ (a ↦ R (N (s a)))`. -/
abbrev blockRes : (∀ d, D d) ⥤ (∀ a, C a) where
  obj N a := (R a (s a) rfl).obj (N (s a))
  map f a := (R a (s a) rfl).map (f (s a))
  map_id N := funext fun a => (R a (s a) rfl).map_id (N (s a))
  map_comp f g := funext fun a => (R a (s a) rfl).map_comp (f (s a)) (g (s a))

@[simp] theorem blockRes_obj (N : ∀ d, D d) (a : A) :
    (blockRes s R).obj N a = (R a (s a) rfl).obj (N (s a)) := rfl

@[simp] theorem blockRes_map {N N' : ∀ d, D d} (f : N ⟶ N') (a : A) :
    (blockRes s R).map f a = (R a (s a) rfl).map (f (s a)) := rfl

end Restriction

variable [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]

section Sum

variable (L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d)

/-- **The block-sum functor** `M ↦ (d ↦ ⨁_{a, s a = d} L (M a))`. -/
abbrev blockSum : (∀ a, C a) ⥤ (∀ d, D d) where
  obj M d := ⨁ fun p : {a // s a = d} => (L p.1 d p.2).obj (M p.1)
  map f d := biproduct.map fun p => (L p.1 d p.2).map (f p.1)
  map_id M := funext fun d => biproduct.hom_ext' _ _ fun p => by simp
  map_comp f g := funext fun d => biproduct.hom_ext' _ _ fun p => by simp

@[simp] theorem blockSum_obj (M : ∀ a, C a) (d : Dd) :
    (blockSum s L).obj M d = ⨁ fun p : {a // s a = d} => (L p.1 d p.2).obj (M p.1) := rfl

@[simp] theorem blockSum_map {M M' : ∀ a, C a} (f : M ⟶ M') (d : Dd) :
    (blockSum s L).map f d =
      (biproduct.map fun p : {a // s a = d} => (L p.1 d p.2).map (f p.1) :
        (⨁ fun p : {a // s a = d} => (L p.1 d p.2).obj (M p.1)) ⟶
          ⨁ fun p : {a // s a = d} => (L p.1 d p.2).obj (M' p.1)) := rfl

/-- The inclusion of the block `p` into the `d`-component of `blockSum s L`. -/
abbrev blockι (M : ∀ a, C a) {d : Dd} (p : {a // s a = d}) :
    (L p.1 d p.2).obj (M p.1) ⟶ (blockSum s L).obj M d :=
  biproduct.ι (fun p : {a // s a = d} => (L p.1 d p.2).obj (M p.1)) p

@[simp]
theorem blockι_map {M M' : ∀ a, C a} (f : M ⟶ M') {d : Dd} (p : {a // s a = d}) :
    blockι s L M p ≫ (blockSum s L).map f d = (L p.1 d p.2).map (f p.1) ≫ blockι s L M' p :=
  biproduct.ι_map (fun p : {a // s a = d} => (L p.1 d p.2).map (f p.1)) p

variable [∀ a, Preadditive (C a)]

instance blockSum_additive [∀ a d h, (L a d h).Additive] : (blockSum s L).Additive where
  map_add := funext fun d => biproduct.hom_ext' _ _ fun p => by
    simp [Preadditive.comp_add]

instance blockSum_linear (K : Type*) [Semiring K] [∀ a, Linear K (C a)]
    [∀ d, Linear K (D d)] [∀ a d h, (L a d h).Linear K] : (blockSum s L).Linear K where
  map_smul _ _ := funext fun d => biproduct.hom_ext' _ _ fun p => by
    simp [Linear.comp_smul]

instance blockRes_additive {R : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a}
    [∀ a d h, (R a d h).Additive] : (blockRes s R).Additive where
  map_add := funext fun _ => Functor.map_add _

instance blockRes_linear (K : Type*) [Semiring K] [∀ a, Linear K (C a)]
    [∀ d, Linear K (D d)] {R : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a}
    [∀ a d h, (R a d h).Linear K] : (blockRes s R).Linear K where
  map_smul _ _ := funext fun _ => Functor.map_smul _ _ _

end Sum

section Map

variable {L L' : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
  (α : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⟶ L' a d h)

/-- **Blockwise natural transformations assemble** to a transformation of block-sum functors. -/
def blockSumMap : blockSum s L ⟶ blockSum s L' where
  app M d := biproduct.map fun p => (α p.1 d p.2).app (M p.1)
  naturality M M' f := funext fun d => biproduct.hom_ext' _ _ fun p => by
    change blockι s L M p ≫ (blockSum s L).map f d ≫
        biproduct.map (fun p => (α p.1 d p.2).app (M' p.1)) =
      blockι s L M p ≫ biproduct.map (fun p => (α p.1 d p.2).app (M p.1)) ≫
        (blockSum s L').map f d
    rw [← Category.assoc, blockι_map, Category.assoc, biproduct.ι_map, ← Category.assoc,
      (α p.1 d p.2).naturality, ← Category.assoc]
    erw [biproduct.ι_map]
    rw [Category.assoc, Category.assoc]
    erw [blockι_map]

theorem blockι_blockSumMap (M : ∀ a, C a) {d : Dd} (p : {a // s a = d}) :
    blockι s L M p ≫ (blockSumMap s α).app M d = (α p.1 d p.2).app (M p.1) ≫ blockι s L' M p :=
  biproduct.ι_map (fun p : {a // s a = d} => (α p.1 d p.2).app (M p.1)) p

end Map


section Adjunction

variable {L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
  {R : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a}
  (adj : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⊣ R a d h)

omit [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]

/-- The counit on the block `a` of `d`, for `s a = d`. -/
def blockCounit : ∀ {a : A} {d : Dd} (h : s a = d) (N : ∀ d, D d),
    (L a d h).obj ((R a (s a) rfl).obj (N (s a))) ⟶ N d
  | a, _, rfl, N => (adj a (s a) rfl).counit.app (N (s a))

@[simp] theorem blockCounit_rfl (a : A) (N : ∀ d, D d) :
    blockCounit s adj (rfl : s a = s a) N = (adj a (s a) rfl).counit.app (N (s a)) := rfl

theorem blockCounit_natural {a : A} {d : Dd} (h : s a = d) {N N' : ∀ d, D d} (f : N ⟶ N') :
    (L a d h).map ((R a (s a) rfl).map (f (s a))) ≫ blockCounit s adj h N' =
      blockCounit s adj h N ≫ f d := by
  subst h
  exact (adj a (s a) rfl).counit.naturality (f (s a))

include adj

/-- The unit of the block-sum adjunction. -/
def blockUnit : 𝟭 (∀ a, C a) ⟶ blockSum s L ⋙ blockRes s R where
  app M a := (adj a (s a) rfl).unit.app (M a) ≫
    (R a (s a) rfl).map (blockι s L M (⟨a, rfl⟩ : {a' // s a' = s a}))
  naturality M M' f := funext fun a => by
    change f a ≫ (adj a (s a) rfl).unit.app (M' a) ≫ (R a (s a) rfl).map (blockι s L M' ⟨a, rfl⟩) =
      ((adj a (s a) rfl).unit.app (M a) ≫ (R a (s a) rfl).map (blockι s L M ⟨a, rfl⟩)) ≫
        (R a (s a) rfl).map ((blockSum s L).map f (s a))
    rw [Category.assoc, ← Functor.map_comp, blockι_map, Functor.map_comp,
      ← Category.assoc, ← Category.assoc]
    congr 1
    exact (adj a (s a) rfl).unit.naturality (f a)

/-- The counit of the block-sum adjunction. -/
def blockCounitNat : blockRes s R ⋙ blockSum s L ⟶ 𝟭 (∀ d, D d) where
  app N d := biproduct.desc fun p => blockCounit s adj p.2 N
  naturality N N' f := funext fun d => biproduct.hom_ext' _ _ fun p => by
    change blockι s L _ p ≫ (blockSum s L).map ((blockRes s R).map f) d ≫
        biproduct.desc (fun p => blockCounit s adj p.2 N') =
      blockι s L _ p ≫ biproduct.desc (fun p => blockCounit s adj p.2 N) ≫ f d
    rw [← Category.assoc, blockι_map, Category.assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
    exact blockCounit_natural s adj p.2 f

/-- **Blockwise adjunctions assemble to an adjunction of block-sum and block-restriction
functors.** -/
def blockAdjunction : blockSum s L ⊣ blockRes s R :=
  Adjunction.mkOfUnitCounit
    { unit := blockUnit s adj
      counit := blockCounitNat s adj
      left_triangle := by
        ext M : 2
        funext d
        refine biproduct.hom_ext' _ _ fun p => ?_
        obtain ⟨a, rfl⟩ := p
        change blockι s L M ⟨a, rfl⟩ ≫ (blockSum s L).map ((blockUnit s adj).app M) (s a) ≫
            𝟙 _ ≫ biproduct.desc (fun p => blockCounit s adj p.2 ((blockSum s L).obj M)) =
          blockι s L M ⟨a, rfl⟩ ≫ 𝟙 _
        rw [Category.id_comp, ← Category.assoc, blockι_map, Category.assoc, biproduct.ι_desc,
          Category.comp_id]
        change (L a (s a) rfl).map ((adj a (s a) rfl).unit.app (M a) ≫
            (R a (s a) rfl).map (blockι s L M ⟨a, rfl⟩)) ≫
            (adj a (s a) rfl).counit.app ((blockSum s L).obj M (s a)) = blockι s L M ⟨a, rfl⟩
        rw [Functor.map_comp, Category.assoc]
        erw [(adj a (s a) rfl).counit.naturality]
        rw [← Category.assoc]
        erw [(adj a (s a) rfl).left_triangle_components]
        exact Category.id_comp _
      right_triangle := by
        ext N : 2
        funext a
        change ((adj a (s a) rfl).unit.app _ ≫
            (R a (s a) rfl).map (blockι s L ((blockRes s R).obj N) ⟨a, rfl⟩)) ≫
            𝟙 _ ≫ (R a (s a) rfl).map (biproduct.desc fun p => blockCounit s adj p.2 N) = 𝟙 _
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp, biproduct.ι_desc, blockCounit_rfl]
        exact (adj a (s a) rfl).right_triangle_components (N (s a)) }

end Adjunction

end

end Categorification.TwoRep
