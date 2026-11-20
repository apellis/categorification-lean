/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensorComp

/-!
# Natural transformations and the bimodules of additive functors

For a `k`-linear functor `F : C ⥤ D` and objects `O` of `C`, `O'` of `D`, `HomTensor` makes
`O' ⟶ F O` an `(End O', End O)`-bimodule, and `M ↦ (O' ⟶ F O) ⊗_{End O} M` a functor from right
`End O`-modules to right `End O'`-modules. A natural transformation `α : F ⟶ G` gives the map of
bimodules `β ↦ β ≫ α_O` (`HomTensor.natMap`), and hence a natural map of these module functors
(`HomTensor.natModuleMap`). It is compatible with identities, composition and sums of natural
transformations, so a decomposition of a functor by natural transformations (for instance the
decompositions `E F ≅ F E ⊕ 1^{⊕ n}` of a categorical action) passes to the module functors. The
bimodule of the identity functor acts as the identity (`HomTensor.unitModuleEquiv`).

This is used to pass from the categorical action of Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Theorem 4.31, on categories of projectives to its
action on module categories (§5 there).

## Main definitions

* `HomTensor.natMap`, `HomTensor.natMap_isBimoduleHom`: the bimodule map of `α : F ⟶ G`.
* `HomTensor.natModuleMap`: `(O' ⟶ F O) ⊗ M → (O' ⟶ G O) ⊗ M`, with `natModuleMap_id`,
  `natModuleMap_comp`, `natModuleMap_add`, `natModuleMap_zero`.
* `HomTensor.unitModuleEquiv`: `(O ⟶ O) ⊗_{End O} M ≅ M`.
-/

namespace Categorification.HomTensor

open CategoryTheory MulOpposite

noncomputable section

variable (k : Type*) [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {D : Type*} [Category D] [Preadditive D] [Linear k D]
  (O : C) (O' : D)

attribute [local instance] bimodule

section NatMap

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

/-- The map `β ↦ β ≫ α_O` of a natural transformation `α : F ⟶ G`, linear for the left action
of `End O'`. -/
def natMap (α : F ⟶ G) : (O' ⟶ F.obj O) →ₗ[(End O')ᵐᵒᵖ] (O' ⟶ G.obj O) where
  toFun β := β ≫ α.app O
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' _ _ := Category.assoc _ _ _

omit [Preadditive C] [Linear k C] [Linear k D] [F.Additive] [G.Additive] in
@[simp] theorem natMap_apply (α : F ⟶ G) (β : O' ⟶ F.obj O) : natMap O O' α β = β ≫ α.app O :=
  rfl

omit [Linear k C] [Linear k D] in
/-- `natMap α` commutes with the right actions of `End O` through `F` and `G`. -/
theorem natMap_isBimoduleHom (α : F ⟶ G) :
    BalancedTensor.IsBimoduleHom (A := (End O)ᵐᵒᵖ) (natMap O O' α) := by
  intro a β
  change (β ≫ F.map a.unop) ≫ α.app O = (β ≫ α.app O) ≫ G.map a.unop
  rw [Category.assoc, α.naturality, Category.assoc]

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (End O)ᵐᵒᵖ M]
  [IsScalarTower k (End O)ᵐᵒᵖ M]

variable (M) in
/-- The natural map `(O' ⟶ F O) ⊗_{End O} M → (O' ⟶ G O) ⊗_{End O} M` of a natural
transformation `α : F ⟶ G`. -/
def natModuleMap (α : F ⟶ G) :
    BalancedTensor k (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ F.obj O) M →ₗ[(End O')ᵐᵒᵖ]
      BalancedTensor k (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ G.obj O) M :=
  BalancedTensor.mapLeftBimodule k M (natMap O O' α) (natMap_isBimoduleHom O O' α)

omit [Linear k C] [IsScalarTower k (End O)ᵐᵒᵖ M] in
theorem natModuleMap_tmul (α : F ⟶ G) (β : O' ⟶ F.obj O) (m : M) :
    natModuleMap k O O' M α (BalancedTensor.tmul β m) =
      BalancedTensor.tmul (k := k) (B := (End O')ᵐᵒᵖ) (A := (End O)ᵐᵒᵖ)
        (show O' ⟶ G.obj O from β ≫ α.app O) m :=
  rfl

omit [Linear k C] [IsScalarTower k (End O)ᵐᵒᵖ M] in
theorem natModuleMap_id : natModuleMap k O O' M (𝟙 F) = LinearMap.id := by
  refine BalancedTensor.extB fun β m => ?_
  change BalancedTensor.tmul (β ≫ 𝟙 (F.obj O)) m = _
  rw [Category.comp_id]
  rfl

omit [Linear k C] [IsScalarTower k (End O)ᵐᵒᵖ M] in
theorem natModuleMap_comp (α : F ⟶ G) (α' : G ⟶ H) :
    natModuleMap k O O' M (α ≫ α') =
      (natModuleMap k O O' M α').comp (natModuleMap k O O' M α) := by
  refine BalancedTensor.extB fun β m => ?_
  change BalancedTensor.tmul (β ≫ (α ≫ α').app O) m =
    BalancedTensor.tmul ((β ≫ α.app O) ≫ α'.app O) m
  rw [NatTrans.comp_app, Category.assoc]

omit [Linear k C] [IsScalarTower k (End O)ᵐᵒᵖ M] in
theorem natModuleMap_add (α α' : F ⟶ G) :
    natModuleMap k O O' M (α + α') = natModuleMap k O O' M α + natModuleMap k O O' M α' := by
  refine BalancedTensor.extB fun β m => ?_
  change BalancedTensor.tmul (β ≫ (α + α').app O) m =
    BalancedTensor.tmul (β ≫ α.app O) m + BalancedTensor.tmul (β ≫ α'.app O) m
  rw [NatTrans.app_add, Preadditive.comp_add, BalancedTensor.add_tmul]

omit [Linear k C] [IsScalarTower k (End O)ᵐᵒᵖ M] in
theorem natModuleMap_zero : natModuleMap k O O' M (0 : F ⟶ G) = 0 := by
  refine BalancedTensor.extB fun β m => ?_
  change BalancedTensor.tmul (β ≫ (0 : F ⟶ G).app O) m = 0
  rw [NatTrans.app_zero, Limits.comp_zero, BalancedTensor.zero_tmul]

omit [Linear k C] [IsScalarTower k (End O)ᵐᵒᵖ M] in
theorem natModuleMap_sum {ι : Type*} (s : Finset ι) (α : ι → (F ⟶ G)) :
    natModuleMap k O O' M (∑ j ∈ s, α j) = ∑ j ∈ s, natModuleMap k O O' M (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, natModuleMap_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, natModuleMap_add, ih]

end NatMap

section Unit

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (End O)ᵐᵒᵖ M]
  [IsScalarTower k (End O)ᵐᵒᵖ M]

/-- An endomorphism of `O` viewed as an element of `(End O)ᵐᵒᵖ`. -/
abbrev opEnd (φ : O ⟶ (𝟭 C).obj O) : (End O)ᵐᵒᵖ := op (show End O from φ)

variable (M) in
/-- The bimodule of the identity functor acts as the identity:
`(O ⟶ O) ⊗_{End O} M ≅ M`, `φ ⊗ m ↦ m φ`. -/
def unitModuleEquiv :
    BalancedTensor k (End O)ᵐᵒᵖ (End O)ᵐᵒᵖ (O ⟶ (𝟭 C).obj O) M ≃ₗ[(End O)ᵐᵒᵖ] M :=
  LinearEquiv.ofLinearMap
    (BalancedTensor.liftB
      (LinearMap.mk₂ k (fun (φ : O ⟶ (𝟭 C).obj O) m => opEnd O φ • m)
        (fun φ φ' m => add_smul (opEnd O φ) (opEnd O φ') m)
        (fun c φ m => smul_assoc c (opEnd O φ) m)
        (fun φ m m' => smul_add _ _ _)
        (fun c φ m => (smul_comm c (opEnd O φ) m).symm))
      (fun φ a m => mul_smul (opEnd O φ) a m)
      (fun b φ m => mul_smul b (opEnd O φ) m))
    { toFun := fun m => BalancedTensor.tmul (M := O ⟶ (𝟭 C).obj O) (𝟙 O) m
      map_add' := fun m m' => BalancedTensor.tmul_add _ m m'
      map_smul' := fun b m => by
        rw [RingHom.id_apply, BalancedTensor.smul_tmul', ← BalancedTensor.op_smul_tmul]
        congr 1
        change 𝟙 O ≫ b.unop = b.unop ≫ 𝟙 O
        rw [Category.id_comp, Category.comp_id] }
    (by
      ext m
      exact one_smul (End O)ᵐᵒᵖ m)
    (BalancedTensor.extB fun φ m => by
      change BalancedTensor.tmul (M := O ⟶ (𝟭 C).obj O) (𝟙 O) (opEnd O φ • m) =
        BalancedTensor.tmul (M := O ⟶ (𝟭 C).obj O) φ m
      rw [← BalancedTensor.op_smul_tmul]
      congr 1
      change 𝟙 O ≫ φ = φ
      rw [Category.id_comp])

@[simp] theorem unitModuleEquiv_tmul (φ : O ⟶ (𝟭 C).obj O) (m : M) :
    unitModuleEquiv k O M (BalancedTensor.tmul φ m) = opEnd O φ • m :=
  rfl

end Unit

end

end Categorification.HomTensor
