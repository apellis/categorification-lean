/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration
import DG.Category.Weight
import DG.Category.Comparison
import DG.Category.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Rat

/-!
# Comparing graded braid cuts with the ordinary target module

In Webster, arXiv:1309.3796v2, §7.2, Proposition 7.11, the target
module action is read by including the homogeneous braid complex into
its ordinary right-module complex. Pointwise boundary reflection
ensures that the resulting homology map is injective.
-/
noncomputable section
namespace Categorification
open CategoryTheory DG
open scoped DG.DegreeZero
universe u
variable (R : Type u) [Ring R] [InternalGrading R] [BigradedDGRing R]

/-- The functor sending a homogeneous morphism to its underlying ring element. -/
def weightToSingleObject : WeightCategory R ⥤ SingleObj R where
  obj _ := SingleObj.star R
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (weightToSingleObject R).Additive where
instance : (weightToSingleObject R).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

/-- The weight module evaluating to the same ordinary module at each weight. -/
def ordinaryModuleAtEveryWeight : ModuleCat.{u} R ⥤ CatModule.{u} (WeightCategory R) :=
  degreeZeroModuleFunctor R ⋙ DGModuleCat.toCatModule R ⋙ CatModule.precomp (weightToSingleObject R)

instance : (ordinaryModuleAtEveryWeight R).Additive where
  map_add := by intros; apply CatModule.Hom.ext; intros; rfl

instance : (ordinaryModuleAtEveryWeight R).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact (CatModule.exact_iff_function_exact _).mpr
    (fun _ => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS)

end Categorification

noncomputable section
namespace Categorification
open CategoryTheory DG CatModule
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

/-- The underlying additive group of a weight module at a single object. -/
def weightUnderlyingGroup (X : C) : CatModule.{w} C ⥤ ModuleCat.{w} ℤ where
  obj M := ModuleCat.of ℤ (M.obj X)
  map φ := ModuleCat.ofHom (φ.app X).toIntLinearMap

instance (X : C) : (weightUnderlyingGroup.{u,v,w} X).Additive where

instance (X : C) : (weightUnderlyingGroup.{u,v,w} X).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    ((CatModule.exact_iff_function_exact _).mp hS X)

variable {S T : ShortComplex (CatModule.{w} C)} (φ : S ⟶ T)
theorem mono_homologyMap_of_weightwise_mono
    (h : ∀ X : C, Mono (ShortComplex.homologyMap (((weightUnderlyingGroup X).mapShortComplex).map φ))) :
    Mono (ShortComplex.homologyMap φ) := by
  apply (CatModule.mono_iff_injective _).mpr
  intro X
  let E := weightUnderlyingGroup.{u,v,w} X
  have hf : E.map (ShortComplex.homologyMap φ) = (S.mapHomologyIso E).inv ≫
      (ShortComplex.homologyMap ((E.mapShortComplex).map φ)) ≫ (T.mapHomologyIso E).hom := by
    rw [ShortComplex.mapHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  have hh : Mono (E.map (ShortComplex.homologyMap φ)) := by
    rw [hf]
    have := h X
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp hh
end Categorification

noncomputable section
namespace Categorification
open CategoryTheory
universe u v
variable {R : Type u} [Ring R] {S T : ShortComplex (ModuleCat.{v} R)}
/-- A map of short complexes induces an injection on homology when boundaries of represented cycles have preimages in the source. -/
theorem homologyMap_injective_of_reflects_boundaries (φ : S ⟶ T)
    (h : ∀ z : S.X₂, S.g z = 0 → (∃ y : T.X₁, T.f y = φ.τ₂ z) → ∃ x : S.X₁, S.f x = z) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  apply (injective_iff_map_eq_zero (ShortComplex.homologyMap φ).hom).mpr
  intro x hx
  obtain ⟨c,rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  have e := congrArg (fun q : S.cycles ⟶ T.opcycles => q c) (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι ((ShortComplex.homologyMap φ) (S.homologyπ c)) = T.pOpcycles (φ.τ₂ (S.iCycles c)) at e
  have hc : S.g (S.iCycles c) = 0 := congrArg (fun q : S.cycles ⟶ S.X₃ => q c) S.iCycles_g
  have hz : T.pOpcycles (φ.τ₂ (S.iCycles c)) = 0 := e.symm.trans ((congrArg T.homologyι hx).trans (map_zero _))
  have src := (S.moduleCat_pOpcycles_eq_zero_iff _).mpr (h _ hc ((T.moduleCat_pOpcycles_eq_zero_iff _).mp hz))
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  have idem := congrArg (fun q : S.cycles ⟶ S.opcycles => q c) S.homology_π_ι
  exact idem.trans (src.trans (map_zero _).symm)

/-- An injective additive endomorphism of the rational line is surjective. -/
theorem surjective_rat_end_of_injective (f : ℚ →+ ℚ) (hf : Function.Injective f) :
    Function.Surjective f := by
  have ho : f 1 ≠ 0 := fun h => one_ne_zero (hf (h.trans (map_zero f).symm))
  intro q
  refine ⟨(q / f 1) • (1 : ℚ),?_⟩
  rw [map_rat_smul,smul_eq_mul,div_mul_cancel₀ _ ho]
end Categorification
