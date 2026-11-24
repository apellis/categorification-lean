/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Derived Hom from a graded scalar coefficient

For the scalar field in internal degree zero, the left modules of the graded
coefficient are K-projective. A homotopy can be chosen separately at each
weight, since scalar morphisms between distinct weights vanish. This supplies
a graded derived Hom model for the coefficient in Webster's Definition 7.4.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v
variable (k : Type u) [Field k]

local instance : InternalGrading k := scalarInternalGrading k
local instance : BigradedDGRing k := scalarBigradedDGRing k
local notation "W" => WeightCategory k

private def scalarAt (X : W) : SingleObj k ⥤ W where
  obj _ := X
  map f := WeightCategory.homMk f (by
    change (f : k) ∈ grading (X.as-X.as)
    rw [sub_self]
    exact InDegreeZero.ring_mem_grading_iff.mpr (Or.inl rfl))
  map_id _ := rfl
  map_comp _ _ := rfl

private instance (X : W) : (scalarAt k X).Additive where
  map_add := rfl

private instance (X : W) : (scalarAt k X).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

private def scalarEval (X : W) : CatModule.{u} W ⥤ DGModuleCat.{u} k :=
  CatModule.precomp (scalarAt k X) ⋙ CatModule.toDGModuleCat k

variable {B M : Type u} [Ring B] [InternalGrading B] [BigradedDGRing B] [AddCommGroup M]
  [Module k M] [Module Bᵐᵒᵖ M] [SMulCommClass k Bᵐᵒᵖ M]

variable (G : ℤ → Submodule k M)
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))

local notation "G₀" => fun j => Submodule.toAddSubgroup (G j)

private theorem scalarWeightLeft {i j : ℤ} {a : k} {x : M}
    (ha : a ∈ wgrading i) (hx : x ∈ G j) : a • x ∈ G (i+j) := by
  rcases InDegreeZero.ring_mem_grading_iff.mp ha with rfl | rfl
  · rw [zero_add]
    exact (G j).smul_mem _ hx
  · rw [zero_smul]; exact zero_mem _

/-- For a coefficient over a scalar field, each left weight module
is K-projective. This gives a derived Hom without a further resolution
of the homogeneous coefficient. -/
theorem diagramWeightScalar_isKProjective (Y : WeightCategory B) :
    CatModule.IsKProjective ((diagramWeightBimodule G₀ (scalarWeightLeft k G) hr).left Y) := by
  let P := (diagramWeightBimodule G₀ (scalarWeightLeft k G) hr).left Y
  intro N hN f
  let localMap (X : W) : InDegreeZero (G (X.as - Y.as)) →ᵈᵍ[k] (scalarEval k X).obj N :=
    { toFun := f.app X
      map_add' := map_add (f.app X)
      map_smul' := fun c x => f.map_smul ((scalarAt k X).map (X := SingleObj.star k) (Y := SingleObj.star k) c) x
      map_mem' := fun hx => f.map_mem hx
      map_d' := fun x => f.map_d x }
  have hex (X : W) : DG.Homotopic (localMap X) 0 := by
    exact (InDegreeZero.isKProjective (A := k) (M := G (X.as - Y.as)))
      _ (show DG.IsAcyclic ((scalarEval k X).obj N) from hN X) (localMap X)
  let h (X : W) := (hex X).some
  let app (X : W) : P.obj X →+ N.obj X := (h X).hom.toAddMonoidHom
  refine ⟨CatModule.DGHomotopy.mk' (hom := {
    app := app
    map_mem' := fun hx => (h _).hom.map_mem hx
    map_smul' := ?_ }) ?_⟩
  · intro X X' i a ha x
    have hw : (a.val : k) ∈ DG.grading (X'.as-X.as) := a.property
    rcases InDegreeZero.ring_mem_grading_iff.mp hw with he | hz
    · have hXX' : X' = X := by
        cases X'; cases X
        congr
        exact sub_eq_zero.mp he
      subst X'
      rcases InDegreeZero.ring_mem_grading_iff.mp (WeightCategory.mem_grading_iff.mp ha) with rfl | hz
      · rw [mul_zero, koszulSign_zero, one_smul]
        have hs := (h X).hom.map_smul (InDegreeZero.ring_mem_grading_zero a.val) x
        rw [mul_zero, koszulSign_zero, one_smul] at hs
        exact hs
      · rw [show a = 0 from WeightCategory.hom_ext hz, CatModule.zero_smul,
          CatModule.zero_smul, smul_zero]
        exact map_zero (app _)
    · rw [show a = 0 from WeightCategory.hom_ext hz, CatModule.zero_smul,
        CatModule.zero_smul, smul_zero]
      exact map_zero (app _)
  · intro X x
    exact (h X).comm x

variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory k)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

/-- Derived Hom from a graded coefficient over a field, defined on the weight
categories. The left modules of the coefficient are already K-projective. -/
def diagramWeightScalarDerivedHom :
    CatModule.DerivedCategory.{v,u} W ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory B) :=
  diagramWeightDerivedHom G₀ (scalarWeightLeft k G) hr
    (diagramWeightScalar_isKProjective k G hr)

end Categorification
