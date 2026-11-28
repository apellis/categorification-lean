/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForgetAdjunctionDerived
import Categorification.Algebra.CompactRetraction

/-!
# Forgetting the weights reflects isomorphisms, zero objects and compactness

The derived functor forgetting the weights, `Φ = DG.CatModule.weightForgetDerived A`, is a left
adjoint (`DG.CatModule.weightForgetDerivedAdjunction`), so it is additive and preserves
coproducts. The derived weight-preserving part is an additive retraction of `Φ` on morphisms,
natural on both sides (`DG.CatModule.weightPartDerivedRetraction`). Hence `Φ` reflects
isomorphisms and zero objects, and an object `X` of `D(C_A)` is compact as soon as `Φ X` is
compact in `D(A)` (`DG.CatModule.isCompact_of_isCompact_weightForgetDerived_obj`).

This is used for the graded braiding functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Definition 6.6 and Theorem 6.15.
-/

open CategoryTheory Limits

universe w w₁ w₂ u

noncomputable section

namespace DG

namespace CatModule

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] [CatModule.HasDerivedCategory.{w₁, u} (WeightCategory A)]
  [DG.HasDerivedCategory.{w₂, u} A]

instance weightForgetDerived_isLeftAdjoint : (weightForgetDerived A).IsLeftAdjoint :=
  (weightForgetDerivedAdjunction A).isLeftAdjoint

instance weightConstDerived_isRightAdjoint : (weightConstDerived A).IsRightAdjoint :=
  (weightForgetDerivedAdjunction A).isRightAdjoint

instance weightConstDerived_additive : (weightConstDerived A).Additive :=
  Functor.additive_of_preserves_binary_products _

instance weightForgetDerived_additive : (weightForgetDerived A).Additive :=
  (weightForgetDerivedAdjunction A).left_adjoint_additive

/-- **The derived weight-preserving part, as a retraction of forgetting the weights.** -/
def weightPartDerivedRetraction : MapRetraction (weightForgetDerived A) where
  r {X Y} :=
    { toFun := weightPartDerived
      map_zero' := by
        rw [← (weightForgetDerived A).map_zero X Y, weightPartDerived_map]
      map_add' f g := by
        simp only [weightPartDerived, ← Adjunction.homAddEquiv_apply, map_add,
          Preadditive.add_comp] }
  r_map g := weightPartDerived_map g
  r_map_comp a f := weightPartDerived_map_comp a f
  r_comp_map f b := weightPartDerived_comp_map f b

instance weightForgetDerived_reflectsIsomorphisms :
    (weightForgetDerived A).ReflectsIsomorphisms :=
  (weightPartDerivedRetraction A).reflectsIsomorphisms

variable {A}

/-- Forgetting the weights reflects zero objects. -/
theorem isZero_of_isZero_weightForgetDerived_obj
    {X : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)}
    (h : IsZero ((weightForgetDerived.{w₁, w₂} A).obj X)) : IsZero X :=
  (weightPartDerivedRetraction A).isZero_of_isZero_obj h

/-- **Compactness is detected after forgetting the weights.** -/
theorem isCompact_of_isCompact_weightForgetDerived_obj
    {X : CatModule.DerivedCategory.{w₁, u} (WeightCategory A)}
    (h : IsCompact.{w} ((weightForgetDerived.{w₁, w₂} A).obj X)) : IsCompact.{w} X :=
  (weightPartDerivedRetraction A).isCompact (fun _ => inferInstance) h

end CatModule

end DG
