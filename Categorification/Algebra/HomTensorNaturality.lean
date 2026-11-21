/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensorIndModule
import Categorification.Algebra.HomTensorNat

/-!
# Naturality of the module functors of additive functors

The identifications of `HomTensor` between induction, restriction and composites of the module
functors `M ↦ (O' ⟶ F O) ⊗_{End O} M` are natural in the module `M`: they commute with the maps
`id ⊗ g` (`BalancedTensor.mapRight`) of a module map `g`, and with `Ind.map` and `Res.map`
(`natModuleMap_mapRight`, `unitModuleEquiv_mapRight`, `compModuleEquiv_mapRight`,
`indTensorEquiv_map`, `resTensorEquiv_map`).

Naturality is what makes the commutation relations of Webster's functors `Eᵢ` and `Fᵢ` on
modules (arXiv:1309.3796v3, Theorem 4.31, on all modules) compatible with any further action
commuting with the algebra, as needed for the tensor factors in the proof of Proposition 5.5
there.
-/

namespace Categorification

open CategoryTheory MulOpposite

noncomputable section

universe u w

namespace BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  [Algebra k A] {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M]
  {N₁ N₂ N₃ N₄ : Type*} [AddCommGroup N₁] [Module k N₁] [Module A N₁] [IsScalarTower k A N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A N₂] [IsScalarTower k A N₂]
  [AddCommGroup N₃] [Module k N₃] [Module A N₃] [IsScalarTower k A N₃]
  [AddCommGroup N₄] [Module k N₄] [Module A N₄] [IsScalarTower k A N₄]

/-- `congrRight` commutes with `mapRight` along a commuting square. -/
theorem congrRight_mapRight (e₁ : N₁ ≃ₗ[A] N₃) (e₂ : N₂ ≃ₗ[A] N₄) (g : N₁ →ₗ[A] N₂)
    (g' : N₃ →ₗ[A] N₄) (hg : ∀ n, e₂ (g n) = g' (e₁ n)) (x : BalancedTensor k B A M N₁) :
    congrRight e₂ (mapRight g x) = mapRight g' (congrRight e₁ x) := by
  induction x using induction_on with
  | zero => simp only [map_zero]
  | tmul m n => simp only [mapRight_tmul, congrRight_tmul, hg]
  | add x y hx hy => simp only [map_add, hx, hy]

end BalancedTensor

namespace HomTensor

attribute [local instance] bimodule

section Transfer

variable {C : Type*} [Category C] [Preadditive C] {O : C} {A : Type*} [Ring A]
  (σ : A ≃+* (End O)ᵐᵒᵖ)
  {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

/-- An `A`-linear map as a map of right `End O`-modules along `σ`. -/
def transferLinearMap (g : N →ₗ[A] N') :
    letI := transferModule σ N
    letI := transferModule σ N'
    N →ₗ[(End O)ᵐᵒᵖ] N' :=
  letI := transferModule σ N
  letI := transferModule σ N'
  { toFun := g
    map_add' := g.map_add
    map_smul' := fun a n => g.map_smul (σ.symm a) n }

@[simp] theorem transferLinearMap_apply (g : N →ₗ[A] N') (n : N) :
    letI := transferModule σ N
    letI := transferModule σ N'
    transferLinearMap σ g n = g n :=
  rfl

end Transfer

section Nat

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  (O : C) (O' : D) {F G : C ⥤ D} [F.Additive] [G.Additive]
  {M M' : Type*} [AddCommGroup M] [Module (End O)ᵐᵒᵖ M] [AddCommGroup M']
  [Module (End O)ᵐᵒᵖ M']

/-- `natModuleMap` is natural in the module. -/
theorem natModuleMap_mapRight (α : F ⟶ G) (g : M →ₗ[(End O)ᵐᵒᵖ] M')
    (x : BalancedTensor ℤ (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ F.obj O) M) :
    natModuleMap ℤ O O' M' α (BalancedTensor.mapRight g x) =
      BalancedTensor.mapRight g (natModuleMap ℤ O O' M α x) :=
  BalancedTensor.mapLeftBimodule_mapRight _ _ g x

/-- `unitModuleEquiv` is natural in the module. -/
theorem unitModuleEquiv_mapRight (g : M →ₗ[(End O)ᵐᵒᵖ] M')
    (x : BalancedTensor ℤ (End O)ᵐᵒᵖ (End O)ᵐᵒᵖ (O ⟶ (𝟭 C).obj O) M) :
    unitModuleEquiv ℤ O M' (BalancedTensor.mapRight g x) = g (unitModuleEquiv ℤ O M x) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul φ m =>
    rw [BalancedTensor.mapRight_tmul, unitModuleEquiv_tmul, unitModuleEquiv_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Nat

section Comp

variable {C₀ : Type*} [Category C₀] [Preadditive C₀] {C₁ : Type*} [Category C₁]
  [Preadditive C₁] {C₂ : Type*} [Category C₂] [Preadditive C₂]
  (F : C₀ ⥤ C₁) [F.Additive] (G : C₁ ⥤ C₂) [G.Additive] (O₀ : C₀) (O₁ : C₁) (O₂ : C₂)
  {J : Type*} [Fintype J] (π : J → (F.obj O₀ ⟶ O₁)) (ι : J → (O₁ ⟶ F.obj O₀))
  (h : ∑ j, π j ≫ ι j = 𝟙 (F.obj O₀))
  {M M' : Type*} [AddCommGroup M] [Module (End O₀)ᵐᵒᵖ M] [AddCommGroup M']
  [Module (End O₀)ᵐᵒᵖ M']

/-- `compModuleEquiv` is natural in the module. -/
theorem compModuleEquiv_mapRight (g : M →ₗ[(End O₀)ᵐᵒᵖ] M')
    (x : BalancedTensor ℤ (End O₂)ᵐᵒᵖ (End O₁)ᵐᵒᵖ (O₂ ⟶ G.obj O₁)
      (BalancedTensor ℤ (End O₁)ᵐᵒᵖ (End O₀)ᵐᵒᵖ (O₁ ⟶ F.obj O₀) M)) :
    compModuleEquiv ℤ F G O₀ O₁ O₂ π ι h M'
        (BalancedTensor.mapRight (BalancedTensor.mapRight g) x) =
      BalancedTensor.mapRight g (compModuleEquiv ℤ F G O₀ O₁ O₂ π ι h M x) := by
  induction x using BalancedTensor.induction_on with
  | zero => repeat erw [map_zero]
  | tmul β y =>
    induction y using BalancedTensor.induction_on with
    | zero => erw [BalancedTensor.tmul_zero]; repeat erw [map_zero]
    | tmul φ m => rfl
    | add y y' hy hy' =>
      erw [BalancedTensor.tmul_add, map_add, map_add, hy, hy', map_add, map_add]
  | add x y hx hy => erw [map_add, map_add, hx, hy, map_add, map_add]

end Comp

section Induction

open InductionAlong

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  {F : C ⥤ D} [F.Additive] {O : C} {O' : D}
  {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B} {σ : A ≃+* (End O)ᵐᵒᵖ}
  (c : Corner φ ≃+ (O' ⟶ F.obj O))
  (hc : ∀ (a : A) (z : Corner φ), c (op a • z) = c z ≫ F.map (σ a).unop)
  {N : Type w} [AddCommGroup N] [Module A N]
  {N' : Type w} [AddCommGroup N'] [Module (End O)ᵐᵒᵖ N']
  (g : N ≃+ N') (hg : ∀ (a : A) (n : N), g (a • n) = σ a • g n)
  {N₂ : Type w} [AddCommGroup N₂] [Module A N₂]
  {N₂' : Type w} [AddCommGroup N₂'] [Module (End O)ᵐᵒᵖ N₂']
  (g₂ : N₂ ≃+ N₂') (hg₂ : ∀ (a : A) (n : N₂), g₂ (a • n) = σ a • g₂ n)

/-- `indTensorEquiv` is natural in the module: it carries `Ind.map f` to `id ⊗ f'` when `f'`
corresponds to `f`. -/
theorem indTensorEquiv_map (f : N →ₗ[A] N₂) (f' : N' →ₗ[(End O)ᵐᵒᵖ] N₂')
    (hf : ∀ n, g₂ (f n) = f' (g n)) (x : Ind N φ) :
    indTensorEquiv c hc g₂ hg₂ (Ind.map f x) =
      BalancedTensor.mapRight f' (indTensorEquiv c hc g hg x) := by
  induction x using Ind.induction_on with
  | zero => repeat erw [map_zero]
  | tmul z n =>
    rw [Ind.map_tmul, indTensorEquiv_tmul, indTensorEquiv_tmul, BalancedTensor.mapRight_tmul,
      hf]
  | add x y hx hy => erw [map_add, map_add, hx, hy, map_add, map_add]

variable {A' : Type u} [Ring A'] {ψ : A' →ₙ+* A}
  (r : Res ψ A ≃+ (O' ⟶ F.obj O))
  (hr : ∀ (a : A) (x : Res ψ A), r (op a • x) = r x ≫ F.map (σ a).unop)
  (M : Type u) [AddCommGroup M] [Module A M] (M₂ : Type u) [AddCommGroup M₂] [Module A M₂]

/-- `resTensorEquiv` is natural in the module. -/
theorem resTensorEquiv_map (f : M →ₗ[A] M₂) (m : Res ψ M) :
    letI := transferModule σ M
    letI := transferModule σ M₂
    resTensorEquiv r hr M₂ (Res.map f m) =
      BalancedTensor.mapRight (transferLinearMap σ f) (resTensorEquiv r hr M m) :=
  rfl

end Induction

end HomTensor

end

end Categorification
