/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrdinaryProjectiveResolutionDG
import DG.Category.Derived.QuasiIso
import DG.Category.Weight
import DG.Category.Module
import DG.Homotopy.Comparison

/-!
# Complexes of diagram weight modules

Realize a diagram of complexes over the degree-zero weight category as
a dg module. This lets a homogeneous projective resolution give the
pointwise dg complex used in Webster, arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG
open scoped DG.DegreeZero

universe u v

variable {R : Type u} [Ring R] [InternalGrading R] [BigradedDGRing R]
  {S : Type v} [Ring S]

abbrev WeightComplexDiagram (R : Type u) [Ring R] [InternalGrading R] [BigradedDGRing R]
    (S : Type v) [Ring S] :=
  WeightCategory R ⥤ CochainComplex (ModuleCat.{v} S) ℤ

variable (F : WeightComplexDiagram R S) [F.Additive]

private theorem termMap_add {X Y : WeightCategory R} (a b : X ⟶ Y)
    (x : ComplexSum (F.obj X)) :
    ComplexSum.map (F.map (a + b)) x =
      ComplexSum.map (F.map a) x + ComplexSum.map (F.map b) x := by
  rw [F.map_add]
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of n x =>
    simp only [ComplexSum.map_of, HomologicalComplex.add_f_apply]
    change ComplexSum.of (F.obj Y) n ((F.map a).f n x + (F.map b).f n x) = _
    exact map_add _ _ _
  | add x y hx hy => simp only [map_add, hx, hy, add_add_add_comm]

private theorem termMap_zero {X Y : WeightCategory R} (x : ComplexSum (F.obj X)) :
    ComplexSum.map (F.map (0 : X ⟶ Y)) x = 0 := by
  rw [F.map_zero]
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of n x => simp
  | add x y hx hy => simp [hx, hy]

/-- Assemble a diagram of ordinary complexes on the degree-zero weight category
into one dg module, using the pointwise direct sum of cochain components. -/
def diagramWeightModuleOfComplex : CatModule.{v} (WeightCategory R) where
  obj X := ComplexSum (F.obj X)
  act := {
    toFun := fun f => (ComplexSum.map (F.map f)).toAddMonoidHom
    map_zero' := AddMonoidHom.ext (termMap_zero F)
    map_add' := fun a b => AddMonoidHom.ext (termMap_add F a b) }
  act_mem' {X Y i j f m} hf hm := by
    change ComplexSum.map (F.map f) m ∈ DG.grading (i + j)
    rcases (InDegreeZero.ring_mem_grading_iff (R := R)).mp (WeightCategory.mem_grading_iff.mp hf) with h | h
    · subst i
      simpa only [zero_add] using ComplexSum.map_mem (F.map f) hm
    · have hf₀ : f = 0 := WeightCategory.hom_ext h
      rw [hf₀, termMap_zero]
      exact zero_mem _
  act_id' X m := by
    change ComplexSum.map (F.map (𝟙 X)) m = m
    rw [F.map_id, ComplexSum.map_id]
  act_comp' f g m := by
    change ComplexSum.map (F.map (f ≫ g)) m =
      ComplexSum.map (F.map g) (ComplexSum.map (F.map f) m)
    rw [F.map_comp, ComplexSum.map_comp]
  d_act' {X Y i f} hf m := by
    change d (ComplexSum.map (F.map f) m) = ComplexSum.map (F.map (d f)) m +
      koszulSign i • ComplexSum.map (F.map f) (d m)
    have hd : d f = 0 := WeightCategory.hom_ext (InDegreeZero.ring_d_apply f.val)
    rw [hd, termMap_zero, zero_add]
    rcases (InDegreeZero.ring_mem_grading_iff (R := R)).mp (WeightCategory.mem_grading_iff.mp hf) with h | h
    · subst i
      rw [koszulSign_zero, one_smul]
      exact (ComplexSum.map_d (F.map f) m).symm
    · have hf₀ : f = 0 := WeightCategory.hom_ext h
      rw [hf₀, termMap_zero, termMap_zero, map_zero, smul_zero]

/-- At a pure cochain component the dg action is the ordinary chain action. -/
theorem diagramWeightModuleOfComplex_act_of {X Y : WeightCategory R}
    (a : X ⟶ Y) (n : ℤ) (x : (F.obj X).X n) :
    (diagramWeightModuleOfComplex F).act a (ComplexSum.of (F.obj X) n x) =
      ComplexSum.of (F.obj Y) n ((F.map a).f n x) :=
  ComplexSum.map_of (F.map a) n x

theorem diagramWeightModuleOfComplex_mem_grading_iff (X : WeightCategory R) (n : ℤ)
    (x : (diagramWeightModuleOfComplex F).obj X) :
    x ∈ DG.grading n ↔ ∃ y : (F.obj X).X n, ComplexSum.of (F.obj X) n y = x :=
  ComplexSum.mem_grading_iff

variable {F} {G : WeightComplexDiagram R S} [G.Additive]

/-- A natural transformation of diagrams of complexes induces a dg map with
the ordinary chain maps as its cohomological components. -/
def diagramWeightModuleOfComplexMap (α : F ⟶ G) :
    diagramWeightModuleOfComplex F ⟶ diagramWeightModuleOfComplex G where
  app X := (ComplexSum.map (α.app X)).toAddMonoidHom
  map_mem' := fun h => ComplexSum.map_mem _ h
  map_d' := ComplexSum.map_d _
  map_smul' {X Y} a x := by
    let x' : ComplexSum (F.obj X) := x
    change ComplexSum.map (α.app Y) (ComplexSum.map (F.map a) x') =
      ComplexSum.map (G.map a) (ComplexSum.map (α.app X) x')
    calc
      _ = ComplexSum.map (F.map a ≫ α.app Y) x' :=
        (ComplexSum.map_comp (F.map a) (α.app Y) x').symm
      _ = ComplexSum.map (α.app X ≫ G.map a) x' := by rw [α.naturality]
      _ = _ := ComplexSum.map_comp (α.app X) (G.map a) x'

/-- A pointwise quasi-isomorphism of ordinary diagrams realizes a dg
quasi-isomorphism on the weight category. -/
theorem diagramWeightModuleOfComplexMap_isQuasiIso (α : F ⟶ G)
    (h : ∀ X, QuasiIso (α.app X)) :
    CatModule.IsQuasiIso (diagramWeightModuleOfComplexMap α) := by
  intro X n
  let _ := h X
  exact dgModule_ofComplex_map_isQuasiIso (α.app X) n

end Categorification
