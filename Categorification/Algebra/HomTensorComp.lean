/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensor
import Categorification.Algebra.BalancedTensorAssoc
import Categorification.Algebra.BalancedTensorExact

/-!
# Composition of the bimodules of additive functors

Let `F : C₀ ⥤ C₁` and `G : C₁ ⥤ C₂` be `k`-linear functors and `Oₙ` an object of `Cₙ`. The
bimodules `O₁ ⟶ F O₀` and `O₂ ⟶ G O₁` of `HomTensor` compose: composition gives an isomorphism

`(O₂ ⟶ G O₁) ⊗_{End O₁} (O₁ ⟶ F O₀) ≅ (O₂ ⟶ G F O₀)`,   `β ⊗ φ ↦ β ≫ G φ`,

of `(End O₂, End O₀)`-bimodules whenever the identity of `F O₀` factors through finitely many
copies of `O₁` (`HomTensor.compEquiv`). With the associativity of balanced tensor products, the
functors `M ↦ (O₁ ⟶ F O₀) ⊗ M` on modules over `End O₀` then compose like the functors `F`.
This is how the categorical action of Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, Theorem 4.31, on categories of projectives gives an action on module
categories, as used in §5 there.

## Main definitions

* `BalancedTensor.congrLeftBimodule`: `M ⊗_A N ≅ M' ⊗_A N` for an isomorphism of bimodules.
* `HomTensor.compEquiv`: the composition isomorphism, a map of bimodules
  (`HomTensor.compEquiv_isBimoduleHom`).
* `HomTensor.compModuleEquiv`: `(O₂ ⟶ G O₁) ⊗ ((O₁ ⟶ F O₀) ⊗ M) ≅ (O₂ ⟶ G F O₀) ⊗ M`.
-/

namespace Categorification

open MulOpposite

namespace BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M]
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M']
  [Module Aᵐᵒᵖ M'] [SMulCommClass B Aᵐᵒᵖ M']
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N]

variable (k N) in
/-- An isomorphism of `(B, A)`-bimodules `M ≅ M'` induces `M ⊗_A N ≅ M' ⊗_A N`. -/
noncomputable def congrLeftBimodule (e : M ≃ₗ[B] M') (he : IsBimoduleHom (A := A) e.toLinearMap) :
    BalancedTensor k B A M N ≃ₗ[B] BalancedTensor k B A M' N :=
  have he' : IsBimoduleHom (A := A) e.symm.toLinearMap := fun a m => by
    apply e.injective
    change e (e.symm (op a • m)) = e (op a • e.symm m)
    rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.coe_toLinearMap, he a,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapLeftBimodule k N e.toLinearMap he)
    (mapLeftBimodule k N e.symm.toLinearMap he')
    (extB fun m n => by simp)
    (extB fun m n => by simp)

@[simp] theorem congrLeftBimodule_tmul (e : M ≃ₗ[B] M')
    (he : IsBimoduleHom (A := A) e.toLinearMap) (m : M) (n : N) :
    congrLeftBimodule k N e he (tmul m n) = tmul (e m) n :=
  rfl

end BalancedTensor

end Categorification

namespace Categorification.HomTensor

open CategoryTheory MulOpposite

noncomputable section

variable (k : Type*) [CommRing k] {C₀ : Type*} [Category C₀] [Preadditive C₀] [Linear k C₀]
  {C₁ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
  {C₂ : Type*} [Category C₂] [Preadditive C₂] [Linear k C₂]
  (F : C₀ ⥤ C₁) [F.Additive] [F.Linear k] (G : C₁ ⥤ C₂) [G.Additive] [G.Linear k]
  (O₀ : C₀) (O₁ : C₁) (O₂ : C₂)

attribute [local instance] bimodule

variable {J : Type*} [Fintype J] (π : J → (F.obj O₀ ⟶ O₁)) (ι : J → (O₁ ⟶ F.obj O₀))
  (h : ∑ j, π j ≫ ι j = 𝟙 (F.obj O₀))

/-- **Composition of bimodules**: `(O₂ ⟶ G O₁) ⊗_{End O₁} (O₁ ⟶ F O₀) ≅ (O₂ ⟶ G F O₀)` when
`𝟙 (F O₀) = ∑ⱼ πⱼ ≫ ιⱼ` with `πⱼ : F O₀ ⟶ O₁`, `ιⱼ : O₁ ⟶ F O₀`. -/
def compEquiv : BalancedTensor k (End O₂)ᵐᵒᵖ (End O₁)ᵐᵒᵖ (O₂ ⟶ G.obj O₁) (O₁ ⟶ F.obj O₀)
    ≃ₗ[(End O₂)ᵐᵒᵖ] (O₂ ⟶ (F ⋙ G).obj O₀) :=
  equiv k G O₁ O₂ π ι h

omit [Preadditive C₀] [Linear k C₀] [F.Additive] [F.Linear k] in
@[simp] theorem compEquiv_tmul (β : O₂ ⟶ G.obj O₁) (φ : O₁ ⟶ F.obj O₀) :
    compEquiv k F G O₀ O₁ O₂ π ι h (BalancedTensor.tmul β φ) = β ≫ G.map φ := rfl

omit [Linear k C₀] [F.Linear k] in
/-- The composition isomorphism is a map of `(End O₂, End O₀)`-bimodules. -/
theorem compEquiv_isBimoduleHom :
    BalancedTensor.IsBimoduleHom (A := (End O₀)ᵐᵒᵖ)
      (compEquiv k F G O₀ O₁ O₂ π ι h).toLinearMap := by
  intro a t
  induction t using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul β φ =>
    change (β ≫ G.map (φ ≫ F.map a.unop)) = (β ≫ G.map φ) ≫ G.map (F.map a.unop)
    rw [G.map_comp, Category.assoc]
  | add s t hs ht => simp only [smul_add, map_add, hs, ht]

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (End O₀)ᵐᵒᵖ M]
  [IsScalarTower k (End O₀)ᵐᵒᵖ M]

variable (M) in
/-- The module functors of `F` and `G` compose to the module functor of `F ⋙ G`:
`(O₂ ⟶ G O₁) ⊗ ((O₁ ⟶ F O₀) ⊗ M) ≅ (O₂ ⟶ G F O₀) ⊗ M`, naturally in the `End O₀`-module `M`. -/
def compModuleEquiv :
    BalancedTensor k (End O₂)ᵐᵒᵖ (End O₁)ᵐᵒᵖ (O₂ ⟶ G.obj O₁)
        (BalancedTensor k (End O₁)ᵐᵒᵖ (End O₀)ᵐᵒᵖ (O₁ ⟶ F.obj O₀) M) ≃ₗ[(End O₂)ᵐᵒᵖ]
      BalancedTensor k (End O₂)ᵐᵒᵖ (End O₀)ᵐᵒᵖ (O₂ ⟶ (F ⋙ G).obj O₀) M :=
  (BalancedTensor.assoc k (End O₂)ᵐᵒᵖ (End O₁)ᵐᵒᵖ (End O₀)ᵐᵒᵖ (O₂ ⟶ G.obj O₁)
      (O₁ ⟶ F.obj O₀) M).symm.trans
    (BalancedTensor.congrLeftBimodule k M (compEquiv k F G O₀ O₁ O₂ π ι h)
      (compEquiv_isBimoduleHom k F G O₀ O₁ O₂ π ι h))

omit [Linear k C₀] [F.Linear k] in
theorem compModuleEquiv_tmul (β : O₂ ⟶ G.obj O₁) (φ : O₁ ⟶ F.obj O₀) (m : M) :
    compModuleEquiv k F G O₀ O₁ O₂ π ι h M (BalancedTensor.tmul β (BalancedTensor.tmul φ m)) =
      BalancedTensor.tmul (k := k) (B := (End O₂)ᵐᵒᵖ) (A := (End O₀)ᵐᵒᵖ)
        (show O₂ ⟶ (F ⋙ G).obj O₀ from β ≫ G.map φ) m :=
  rfl

end

end Categorification.HomTensor
