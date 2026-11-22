/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.CategoryTheory.PiAbelian
import Categorification.Algebra.InductionAlongRes
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finitely generated modules over a tower of rings

Let `A 0, A 1, …` be a sequence of rings. The family `(M m)ₘ` of modules `M m` over `A m`
form the product category `∀ m, ModuleCat (A m)`, which is abelian
(`CategoryTheory.Pi.abelian`). When every `A m` is left noetherian, the families of finitely
generated modules form a Serre subcategory (`towerFinite.isSerreClass`), hence an abelian
category `FGTower A`.

This is the ambient category of the weak `𝔰𝔩₂`-categorification on the modules over the
tensor product algebras of Webster, arXiv:1309.3796v2, §5, along one `i`-string
(Chuang–Rouquier, arXiv:math/0407205v2, §5.1.1): level `m` carries the modules over the algebra
with `m` black strands of colour `i` adjoined.

## Main definitions

* `ModuleTower.towerFinite`: the property of being finitely generated at every level.
* `ModuleTower.FGTower`: the abelian category of such families.
* `ModuleTower.FGTower.eval`: the exact functor to the modules at one level.
-/

universe u

namespace Categorification.ModuleTower

open CategoryTheory Limits ObjectProperty

section Products

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)

/-- A property of objects of an abelian category closed under isomorphisms and extensions is
closed under binary products. -/
theorem isClosedUnderBinaryProducts_of_extensions [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderExtensions] : P.IsClosedUnderBinaryProducts where
  limitsOfShape_le X := by
    rintro ⟨h⟩
    have e : X ≅ h.diag.obj ⟨.left⟩ ⊞ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫
        HasLimit.isoOfNatIso (diagramIsoPair _) ≪≫ (biprod.isoProd _ _).symm
    exact P.prop_of_iso e.symm (P.prop_biprod (h.prop_diag_obj _) (h.prop_diag_obj _))

/-- A Serre class of an abelian category is closed under finite products. -/
theorem isClosedUnderFiniteProducts_of_isSerreClass [P.IsSerreClass] :
    P.IsClosedUnderFiniteProducts :=
  have := isClosedUnderBinaryProducts_of_extensions P
  IsClosedUnderFiniteProducts.mk'

end Products

variable (A : ℕ → Type u) [∀ m, Ring (A m)]

/-- Families of modules over a tower of rings that are finitely generated at every level. -/
def towerFinite : ObjectProperty (∀ m, ModuleCat.{u} (A m)) :=
  fun M => ∀ m, Module.Finite (A m) (M m)

variable [∀ m, IsNoetherianRing (A m)]

instance towerFinite.isSerreClass : (towerFinite A).IsSerreClass where
  exists_zero := ⟨fun m => ModuleCat.of (A m) PUnit.{u + 1},
    ⟨fun Y => ⟨⟨⟨fun m => 0⟩, fun f => funext fun m =>
        (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _⟩⟩,
      fun Y => ⟨⟨⟨fun m => 0⟩, fun f => funext fun m =>
        (ModuleCat.isZero_of_subsingleton _).eq_of_tgt _ _⟩⟩⟩,
    fun m => inferInstanceAs (Module.Finite (A m) PUnit.{u + 1})⟩
  prop_of_mono {X Y} f _ hY m := by
    have : Mono (f m) := (Pi.eval _ m).map_mono f
    have hf : Function.Injective (f m).hom := (ModuleCat.mono_iff_injective _).mp this
    have : Module.Finite (A m) (Y m) := hY m
    exact Module.Finite.of_injective (f m).hom hf
  prop_of_epi {X Y} f _ hX m := by
    have : Epi (f m) := (Pi.eval _ m).map_epi f
    have hf : Function.Surjective (f m).hom := (ModuleCat.epi_iff_surjective _).mp this
    have : Module.Finite (A m) (X m) := hX m
    exact Module.Finite.of_surjective (f m).hom hf
  prop_X₂_of_shortExact {S} hS h₁ h₃ m := by
    have hm := Pi.shortExact_eval hS m
    have : Module.Finite (A m) (S.map (Pi.eval _ m)).X₁ := h₁ m
    have : Module.Finite (A m) (S.map (Pi.eval _ m)).X₃ := h₃ m
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hm.exact)
      hm.moduleCat_surjective_g

instance : (towerFinite A).IsClosedUnderFiniteProducts :=
  isClosedUnderFiniteProducts_of_isSerreClass _

/-- The abelian category of families of finitely generated modules over a tower of left
noetherian rings. -/
abbrev FGTower := (towerFinite A).FullSubcategory

example : Abelian (FGTower A) := inferInstance

/-- Evaluation at level `m`. -/
abbrev FGTower.eval (m : ℕ) : FGTower A ⥤ ModuleCat.{u} (A m) :=
  (towerFinite A).ι ⋙ Pi.eval _ m

instance (m : ℕ) : (FGTower.eval A m).Additive := by
  dsimp only [FGTower.eval]; infer_instance

instance : (towerFinite A).ι.PreservesHomology :=
  have := (towerFinite A).preservesCokernels_ι
  have := (towerFinite A).preservesMonomorphisms_ι_of_isNormalEpiCategory
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance (m : ℕ) : (FGTower.eval A m).PreservesHomology where
  preservesKernels _ _ f :=
    have := Functor.PreservesHomology.preservesKernel (towerFinite A).ι f
    comp_preservesLimit _ _
  preservesCokernels _ _ f :=
    have := Functor.PreservesHomology.preservesCokernel (towerFinite A).ι f
    comp_preservesColimit _ _

end Categorification.ModuleTower
