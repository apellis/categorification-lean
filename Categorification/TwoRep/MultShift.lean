/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.KrullSchmidt
import Categorification.TwoRep.BSum

/-!
# Multiplicities of indecomposables: shifts, isomorphic tests, finite sums

The multiplicity `mult k hZ X = dim Hom(Z, X) - dim rad(Z, X)` of an indecomposable `Z` in `X`
(`Categorification.KrullSchmidtCat`) is used in the proof of CL Lemma 3.6 (`LemXind.lean`) to count
the summands `E 1_{n-2} ⟨a⟩` of `E^{(2)} F 1_{n-2}` without the rigidity hypothesis of the second
cancellation law (`cancel_shiftSum`). This file collects the needed invariance properties:

* `isIndec_shift`, `mult_congr_left`, `mult_shift`: `Z⟨t⟩` is indecomposable, `mult` only depends on
  `Z` up to isomorphism, and `mult_{Z⟨t⟩}(X⟨t⟩) = mult_Z(X)`;
* `mult_eq_zero_of_finrank_eq_zero`, `mult_le_finrank`;
* `mult_bsum`: additivity over `bsum`, and the whiskering isomorphisms `whiskerLeftBsumIso`,
  `whiskerRightBsumIso` in a graded bicategory.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module
open KrullSchmidtCat

section Cat

variable (k : Type*) [Field k] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  [HomFinite k 𝒞]

theorem rad_map_homCongr {Z Z' : 𝒞} (hZ : IsIndec Z) (hZ' : IsIndec Z') (e : Z ≅ Z') (X : 𝒞) :
    (rad k hZ X).map (Linear.homCongr k e (Iso.refl X)).toLinearMap = rad k hZ' X := by
  ext f
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, Linear.homCongr_apply, Iso.refl_hom,
    Category.comp_id, mem_rad, Category.assoc]
  constructor
  · rintro ⟨f₀, hf₀, rfl⟩ g hu
    refine hf₀ (g ≫ e.inv) ?_
    rw [Category.assoc] at hu
    have hi : IsIso (e.inv ≫ f₀ ≫ g) := (isUnit_iff_isIso _).1 hu
    have : f₀ ≫ g ≫ e.inv = e.hom ≫ (e.inv ≫ f₀ ≫ g) ≫ e.inv := by simp
    rw [isUnit_iff_isIso, this]
    infer_instance
  · intro hf
    refine ⟨e.hom ≫ f, fun g hu => hf (g ≫ e.hom) ?_, by simp⟩
    rw [Category.assoc] at hu
    have hi : IsIso (e.hom ≫ f ≫ g) := (isUnit_iff_isIso _).1 hu
    have : f ≫ g ≫ e.hom = e.inv ≫ (e.hom ≫ f ≫ g) ≫ e.hom := by simp
    rw [isUnit_iff_isIso, this]
    infer_instance

/-- `mult` only depends on the indecomposable up to isomorphism. -/
theorem mult_congr_left {Z Z' : 𝒞} (hZ : IsIndec Z) (hZ' : IsIndec Z') (e : Z ≅ Z') (X : 𝒞) :
    mult k hZ X = mult k hZ' X := by
  have h1 := (Linear.homCongr k e (Iso.refl X)).finrank_eq
  have h2 := LinearEquiv.finrank_map_eq (Linear.homCongr k e (Iso.refl X)) (rad k hZ X)
  rw [rad_map_homCongr k hZ hZ' e X] at h2
  unfold mult
  rw [h1, h2]

theorem mult_eq_zero_of_finrank_eq_zero {Z X : 𝒞} (hZ : IsIndec Z) (h : finrank k (Z ⟶ X) = 0) :
    mult k hZ X = 0 := by
  unfold mult
  have : finrank k (rad k hZ X) = 0 := by
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro f _
    haveI := Module.finrank_zero_iff.1 h
    exact Subsingleton.elim _ _
  rw [h, this]; rfl

theorem mult_le_finrank {Z X : 𝒞} (hZ : IsIndec Z) : mult k hZ X ≤ finrank k (Z ⟶ X) := by
  unfold mult; omega

variable [HasShift 𝒞 ℤ] [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒞 n).Linear k]

omit [Linear k 𝒞] [HomFinite k 𝒞] [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Linear k] in
/-- Shifts of indecomposables are indecomposable (the shift functor is fully faithful). -/
theorem isIndec_shift {Z : 𝒞} (hZ : IsIndec Z) (t : ℤ) : IsIndec (Z⟦t⟧) := by
  refine ⟨fun h => hZ.1 ?_, fun e' he' => ?_⟩
  · exact (((shiftFunctor 𝒞 (-t)).map_isZero h).of_iso
      ((shiftFunctorCompIsoId 𝒞 t (-t) (by ring)).app Z).symm)
  · obtain ⟨e, rfl⟩ := (shiftFunctor 𝒞 t).map_surjective e'
    rw [← Functor.map_comp] at he'
    have he : e ≫ e = e := (shiftFunctor 𝒞 t).map_injective he'
    rcases hZ.2 e he with h | h
    · left; rw [h, Functor.map_zero]
    · right; rw [h, CategoryTheory.Functor.map_id]

theorem rad_map_shift {Z : 𝒞} (hZ : IsIndec Z) (t : ℤ) (X : 𝒞) :
    (rad k hZ X).map (shiftHomEquiv k Z X t).toLinearMap = rad k (isIndec_shift hZ t) (X⟦t⟧) := by
  ext f'
  constructor
  · rintro ⟨f, hf, rfl⟩ g' hu
    obtain ⟨g, rfl⟩ := (shiftFunctor 𝒞 t).map_surjective g'
    refine hf g ((isUnit_iff_isIso _).2 ?_)
    have hi : IsIso ((shiftFunctor 𝒞 t).map (f ≫ g)) := by
      rw [Functor.map_comp]
      exact (isUnit_iff_isIso _).1 hu
    exact isIso_of_reflects_iso (f ≫ g) (shiftFunctor 𝒞 t)
  · intro hf'
    obtain ⟨f, rfl⟩ := (shiftFunctor 𝒞 t).map_surjective f'
    refine ⟨f, fun g hu => hf' ((shiftFunctor 𝒞 t).map g) ((isUnit_iff_isIso _).2 ?_), rfl⟩
    haveI : IsIso (f ≫ g) := (isUnit_iff_isIso _).1 hu
    change IsIso ((shiftFunctor 𝒞 t).map f ≫ (shiftFunctor 𝒞 t).map g)
    rw [← Functor.map_comp]
    infer_instance

/-- **Shift invariance of multiplicities**: `mult_{Z⟨t⟩}(X⟨t⟩) = mult_Z(X)`. -/
theorem mult_shift {Z : 𝒞} (hZ : IsIndec Z) (t : ℤ) (X : 𝒞) :
    mult k (isIndec_shift hZ t) (X⟦t⟧) = mult k hZ X := by
  unfold mult
  rw [finrank_hom_shift, ← rad_map_shift k hZ t X, LinearEquiv.finrank_map_eq]

end Cat

section BSum

variable (k : Type*) [Field k] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  [HomFinite k 𝒞] [HasZeroObject 𝒞] [HasBinaryBiproducts 𝒞]

/-- Additivity of `mult` over `bsum`. -/
theorem mult_bsum {Z : 𝒞} (hZ : IsIndec Z) (f : ℕ → 𝒞) :
    ∀ n : ℕ, mult k hZ (bsum f n) = ∑ j ∈ Finset.range n, mult k hZ (f j)
  | 0 => by
    rw [Finset.sum_range_zero, bsum_zero]
    exact mult_eq_zero_of_finrank_eq_zero k hZ (finrank_hom_of_isZero_right k _ (isZero_zero 𝒞))
  | n + 1 => by
    rw [Finset.sum_range_succ, bsum_succ, mult_biprod, mult_bsum hZ f n, add_comm]

end BSum

section Whisker

open CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [∀ a b : B, HasZeroObject (a ⟶ b)]
  [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

/-- `X ≫ bsum f n ≅ bsum (X ≫ f ·) n`. -/
def whiskerLeftBsumIso {a b c : B} (X : a ⟶ b) (f : ℕ → (b ⟶ c)) :
    ∀ n : ℕ, X ≫ bsum f n ≅ bsum (fun j => X ≫ f j) n
  | 0 => ((precomp c X).map_isZero (isZero_zero _)).isoZero
  | n + 1 => whiskerLeftBiprodIso X _ _ ≪≫ biprod.mapIso (Iso.refl _) (whiskerLeftBsumIso X f n)

/-- `bsum f n ≫ Y ≅ bsum (f · ≫ Y) n`. -/
def whiskerRightBsumIso {a b c : B} (f : ℕ → (a ⟶ b)) (Y : b ⟶ c) :
    ∀ n : ℕ, bsum f n ≫ Y ≅ bsum (fun j => f j ≫ Y) n
  | 0 => ((postcomp a Y).map_isZero (isZero_zero _)).isoZero
  | n + 1 => whiskerRightBiprodIso _ _ Y ≪≫ biprod.mapIso (Iso.refl _) (whiskerRightBsumIso f Y n)

end Whisker

end Categorification.TwoRep
