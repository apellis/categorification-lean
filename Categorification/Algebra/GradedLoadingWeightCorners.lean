/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.GradedLoadingCovers
import DG.Category.Resolution.KProjective
import DG.Category.Weight

/-!
# Weight slices of the graded loading covers

Each internal weight of a shifted loading ideal is the corresponding
representable corner in the weight category. The direct-sum comparison
intertwines the homogeneous scalar actions. This identifies the projective
terms used in the graded resolution from Webster's Lemma 6.11.
-/

noncomputable section

open DirectSum

namespace Categorification.ModuleFiltration

variable {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]
variable (G : ℤ → AddSubgroup X) {ι : Type*} (e : ι → R) (A : ℤ → AddSubgroup R)

set_option quotPrecheck false in
local notation "J" => HomogeneousLoadingGenerators G e
set_option quotPrecheck false in
local notation "L" => fun t : J => ↥(lIdeal (e t.1))
set_option quotPrecheck false in
local notation "T" => fun n (t : J) => ↥(loadingIdealGrading A (e t.1) (n-t.2.1))
set_option quotPrecheck false in
local notation "W" => homogeneousLoadingCoverGrade G e A

/-- In each output weight, the shifted direct sum is the direct sum of the
individual loading-ideal slices. -/
def homogeneousLoadingCoverGrade_sumEquiv (n : ℤ) :
    (⨁ t : J, T n t) ≃+ W n := by
  classical
  let F : (⨁ t : J, T n t) →+ ⨁ t : J, L t :=
    DirectSum.map fun t => (loadingIdealGrading A (e t.1) (n-t.2.1)).subtype
  have hF : ∀ x, F x ∈ W n := by
    intro x t
    change ((F x) t).val ∈ A (n-t.2.1)
    unfold F
    rw [DirectSum.map_apply]
    exact (x t).property
  refine AddEquiv.ofBijective (F.codRestrict (W n) hF) ⟨?_, ?_⟩
  · intro a b eq
    have h := congrArg Subtype.val eq
    change F a = F b at h
    apply DFinsupp.ext
    intro t
    apply Subtype.ext
    have h' := congrArg (fun x : ⨁ t : J, L t => x t) h
    dsimp [F] at h'
    simpa only [DirectSum.map_apply, AddSubgroup.subtype_apply] using h'
  · intro x
    let y : ⨁ t : J, L t := x.val
    have hy : ∀ t : J, (y t).val ∈ A (n-t.2.1) := x.property
    let z : ⨁ t : J, T n t := DFinsupp.mk y.support (fun t => ⟨y t, hy t⟩)
    refine ⟨z, Subtype.ext ?_⟩
    change F z = y
    apply DFinsupp.ext
    intro t
    change (F z) t = y t
    simp only [F, DirectSum.map_apply, AddSubgroup.subtype_apply, z, DFinsupp.mk_apply]
    split_ifs with ht
    · rfl
    · exact (DFinsupp.notMem_support_iff.mp ht).symm


section Corner

open DG CategoryTheory

variable [DGAddCommGroup R] [DGRing R] [InternalGrading R] [BigradedDGRing R]

/-- The weight slice of a shifted loading ideal is the corresponding representable corner. -/
def loadingIdealGrading_cornerEquiv {X : WeightCategory R} (f : DGCategory.Idempotent X)
    {a : R} (ha : f.val.val = a) (Y : WeightCategory R) :
    (CatModule.corner f).obj Y ≃+
      ↥(loadingIdealGrading (wgrading (M := R)) a (Y.as-X.as)) where
  toFun h :=
    ⟨⟨h.val.val, by
      change h.val.val * a = h.val.val
      rw [← ha]
      exact congrArg Subtype.val h.property⟩, h.val.property⟩
  invFun x :=
    ⟨⟨x.val.val, x.property⟩, WeightCategory.hom_ext (by
      change x.val.val * f.val.val = x.val.val
      rw [ha]
      exact x.val.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl


end Corner

end Categorification.ModuleFiltration

namespace Categorification.ModuleFiltration
open DG CategoryTheory DirectSum

set_option autoImplicit false

universe u v w

variable {R : Type u} [Ring R] [DGAddCommGroup R] [DGRing R] [InternalGrading R]
  [BigradedDGRing R] {X : Type v} [AddCommGroup X] [Module R X]
  {ι : Type w} (G : ℤ → AddSubgroup X) (e : ι → R)

abbrev WeightGenerators := HomogeneousLoadingGenerators G e
abbrev generatorWeight (t : WeightGenerators G e) : WeightCategory R := ⟨t.2.1⟩

variable (projector : ∀ t : WeightGenerators G e, DGCategory.Idempotent (generatorWeight G e t))
variable (fixedEq : ∀ t : WeightGenerators G e, (projector t).val.val = e t.1)

def higherWeightCornerSumEquiv (Y : WeightCategory R) :
    (⨁ t : WeightGenerators G e, (CatModule.corner (projector t)).obj Y) ≃+
      ↥(homogeneousLoadingCoverGrade G e (wgrading (M := R)) Y.as) := by
  let E : (⨁ t : WeightGenerators G e, (CatModule.corner (projector t)).obj Y) ≃+
      (⨁ t : WeightGenerators G e, ↥(loadingIdealGrading (wgrading (M := R))
        (e t.1) (Y.as - t.2.1))) :=
    DFinsupp.mapRange.addEquiv (fun t => loadingIdealGrading_cornerEquiv (projector t) (fixedEq t) Y)
  exact E.trans (homogeneousLoadingCoverGrade_sumEquiv G e (wgrading (M := R)) Y.as)


theorem higherWeightCornerSumEquiv_coeff (Y : WeightCategory R)
    (x : ⨁ t : WeightGenerators G e, (CatModule.corner (projector t)).obj Y)
    (t : WeightGenerators G e) :
    ((higherWeightCornerSumEquiv G e projector fixedEq Y x).val t).val =
      (x t).val.val := by
  let F : ∀ t' : WeightGenerators G e, (CatModule.corner (projector t')).obj Y ≃+
        ↥(loadingIdealGrading (wgrading (M := R)) (e t'.1) (Y.as - t'.2.1)) :=
    fun t' => loadingIdealGrading_cornerEquiv (projector t') (fixedEq t') Y
  let coeff : (⨁ t' : WeightGenerators G e,
      ↥(loadingIdealGrading (wgrading (M := R)) (e t'.1) (Y.as - t'.2.1))) →+
      (⨁ t' : WeightGenerators G e, ↥(lIdeal (e t'.1))) :=
    DirectSum.map (fun t' => (loadingIdealGrading (wgrading (M := R))
      (e t'.1) (Y.as - t'.2.1)).subtype)
  change ((coeff ((DFinsupp.mapRange.addEquiv F) x) t).val) = _
  unfold coeff
  rw [DirectSum.map_apply]
  change ((((DFinsupp.mapRange.addEquiv F) x t).val) : R) = _
  rw [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply]
  rfl

theorem higherWeightCornerSumEquiv_act {Y Z : WeightCategory R} (a : Y ⟶ Z)
    (x : ⨁ t : WeightGenerators G e, (CatModule.corner (projector t)).obj Y) :
    (higherWeightCornerSumEquiv G e projector fixedEq Z
      (DirectSum.map (fun t => (CatModule.corner (projector t)).act a) x)).val =
        a.val • (higherWeightCornerSumEquiv G e projector fixedEq Y x).val := by
  apply DFinsupp.ext
  intro t
  apply Subtype.ext
  rw [higherWeightCornerSumEquiv_coeff, DirectSum.smul_apply, DirectSum.map_apply]
  change a.val * (x t).val.val =
    a.val * ((higherWeightCornerSumEquiv G e projector fixedEq Y x).val t).val
  rw [higherWeightCornerSumEquiv_coeff]

end Categorification.ModuleFiltration
