/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import DG.Category.Abelian

/-!
# Exactness on the weight category

Homogeneous short exact sequences restrict to short exact sequences of dg
weight modules. This is the degreewise step in the standard-filtration
argument of Webster, arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section
namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u

variable {A B M N : Type u} [Ring A] [Ring B]
  [InternalGrading A] [InternalGrading B] [BigradedDGRing A] [BigradedDGRing B]
  [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module A N] [Module Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {a : A} {x : N}, a ∈ wgrading i → x ∈ H j → a • x ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {b : B} {x : N}, b ∈ wgrading i → x ∈ H j → op b • x ∈ H (j + i))
  (Z : WeightCategory B) (f : M →ₗ[A] N)
  (hf : ∀ i {x : M}, x ∈ G i → f x ∈ H i)

local notation "D₀" => diagramWeightBimodule G hgL hgR
local notation "D₁" => diagramWeightBimodule H hhL hhR

/-- A weight-preserving linear map restricts to a map of the left dg weight modules. -/
def diagramWeightLeftLinearMap : (D₀).left Z ⟶ (D₁).left Z where
  app X :=
    { toFun := fun x => ⟨f x.val, hf _ x.property⟩
      map_zero' := Subtype.ext (f.map_zero)
      map_add' x y := Subtype.ext (f.map_add x.val y.val) }
  map_mem' {X n x} hx := by
    rcases (InDegreeZero.mem_grading_iff (M := G (X.as - Z.as))).mp hx with rfl | rfl
    · exact InDegreeZero.mem_grading_zero _
    · exact (InDegreeZero.mem_grading_iff (M := H (X.as - Z.as))).mpr
        (Or.inr (Subtype.ext f.map_zero))
  map_d' {X} x := by
    have h : d x = 0 := InDegreeZero.d_apply (G (X.as - Z.as)) x
    rw [h, map_zero]
    exact (InDegreeZero.d_apply (H (X.as - Z.as)) _).symm
  map_smul' a x := Subtype.ext (f.map_smul a.val x.val)

theorem diagramWeightLeftLinearMap_injective (hi : Function.Injective f) (X : WeightCategory A) :
    Function.Injective ((diagramWeightLeftLinearMap G H hgL hgR hhL hhR Z f hf).app X) := by
  intro x y h
  exact Subtype.ext (hi (congrArg Subtype.val h))

include hf in
omit [InternalGrading A] [BigradedDGRing A] in
private theorem weightLinearMap_homogeneous_preimage
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    {i : ℤ} {y : N} (hy : y ∈ H i) (h : ∃ x, f x = y) : ∃ x ∈ G i, f x = y := by
  let _ : DGAddCommGroup M := {
    grading := G
    d := 0
    d_mem' := fun _ => zero_mem _
    d_d' := fun _ => rfl }
  let _ : DGAddCommGroup N := {
    grading := H
    d := 0
    d_mem' := fun _ => zero_mem _
    d_d' := fun _ => rfl }
  obtain ⟨x, hx⟩ := h
  refine ⟨(DirectSum.decompose G x i).val, (DirectSum.decompose G x i).property, ?_⟩
  have hmap : ((DirectSum.decompose H (f x) i).val : N) =
      f (DirectSum.decompose G x i).val :=
    coe_decompose_map_of_map_mem f.toAddMonoidHom (fun h => hf _ h) x i
  rw [← hmap, hx, DirectSum.decompose_of_mem_same _ hy]

theorem diagramWeightLeftLinearMap_surjective
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    (hs : Function.Surjective f) (X : WeightCategory A) :
    Function.Surjective ((diagramWeightLeftLinearMap G H hgL hgR hhL hhR Z f hf).app X) := by
  intro y
  obtain ⟨x, hx, hfx⟩ := weightLinearMap_homogeneous_preimage G H f hf y.property (hs y.val)
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

variable {P : Type u} [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P]
  [SMulCommClass A Bᵐᵒᵖ P]
  (J : ℤ → AddSubgroup P)
  (hjL : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ J j → a • x ∈ J (i + j))
  (hjR : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ J j → op b • x ∈ J (j + i))
  (g : N →ₗ[A] P) (hg : ∀ i {x : N}, x ∈ H i → g x ∈ J i)

/-- Homogeneous maps exact on the underlying modules are exact at each weight. -/
theorem diagramWeightLeftLinearMap_exact
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    (hfg : Function.Exact f g) (X : WeightCategory A) :
    Function.Exact ((diagramWeightLeftLinearMap G H hgL hgR hhL hhR Z f hf).app X)
      ((diagramWeightLeftLinearMap H J hhL hhR hjL hjR Z g hg).app X) := by
  intro y
  constructor
  · intro hy
    have hgy : g y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx, hfx⟩ := weightLinearMap_homogeneous_preimage G H f hf y.property ((hfg y.val).mp hgy)
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (hfg.apply_apply_eq_zero x.val)

/-- The homogeneous short exact sequence defines a short exact sequence at a fixed
source weight. -/
theorem diagramWeightLeftLinearMap_shortExact
    [DirectSum.Decomposition G] [DirectSum.Decomposition H] [DirectSum.Decomposition J]
    (hi : Function.Injective f) (hfg : Function.Exact f g) (hs : Function.Surjective g) :
    let f' := diagramWeightLeftLinearMap G H hgL hgR hhL hhR Z f hf
    let g' := diagramWeightLeftLinearMap H J hhL hhR hjL hjR Z g hg
    let S := ShortComplex.mk f' g'
      (CatModule.Hom.ext fun _ x => Subtype.ext (hfg.apply_apply_eq_zero x.val))
    S.ShortExact := by
  apply (CatModule.shortExact_iff _).mpr
  intro X
  exact ⟨diagramWeightLeftLinearMap_injective G H hgL hgR hhL hhR Z f hf hi X,
    diagramWeightLeftLinearMap_exact G H hgL hgR hhL hhR Z f hf J hjL hjR g hg hfg X,
    diagramWeightLeftLinearMap_surjective H J hhL hhR hjL hjR Z g hg hs X⟩

end Categorification
