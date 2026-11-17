/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.SpacedGrading
import Categorification.WeightedKLR.Induction.Generation

/-!
# Entries of the evenly spaced loading family

Supporting the map from the positive quantum group to graded projective `K₀` in B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19,
roadmap C. Proposition 2.14 identifies the ordinary KLR algebra with a matrix corner indexed
by sequences. Entries transport composable maps between individual sequence projectives to
Webster's rank-ordered algebra. Distinct sequences remain separate matrix indices even if
their evenly spaced loadings define the same weighted chamber. Thus composition does not
require distinct weighted chamber idempotents.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : Multiset I}

namespace SpacedAlgebra

private theorem entry_mem_rankCorner (a : SpacedAlgebra k Γ ν) (i j : KLR.Seq ν) :
    a.1 i j ∈ Subsemigroup.corner (rankIdem k Γ ν.toFinsupp) := by
  apply cornerSpace_mem_corner (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered
    (KLR.Seq.spacedChamber Γ j).toFull_isRankOrdered (x := ⟨a.1 i j, ?_⟩)
  rw [mem_cornerSpace_iff, SpacedAlgebra.e_mul, SpacedAlgebra.mul_e]

/-- A matrix entry of the evenly spaced loading algebra, in Webster's weighted algebra. -/
def entry (a : SpacedAlgebra k Γ ν) (i j : KLR.Seq ν) :
    WeightedKLRAlgebra k Γ ν.toFinsupp := ⟨a.1 i j, entry_mem_rankCorner a i j⟩

@[simp] theorem entry_val (a : SpacedAlgebra k Γ ν) (i j : KLR.Seq ν) :
    (a.entry i j).1 = a.1 i j := rfl

/-- The entry operation is linear over the coefficient ring. -/
def entryLinearMap (i j : KLR.Seq ν) :
    SpacedAlgebra k Γ ν →ₗ[k] WeightedKLRAlgebra k Γ ν.toFinsupp where
  toFun a := a.entry i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem entryLinearMap_apply (i j : KLR.Seq ν) (a : SpacedAlgebra k Γ ν) :
    entryLinearMap i j a = a.entry i j := rfl

/-- Multiplication of family entries is matrix multiplication. -/
theorem entry_mul (a b : SpacedAlgebra k Γ ν) (i l : KLR.Seq ν) :
    (a * b).entry i l = ∑ j, a.entry i j * b.entry j l := by
  apply Subtype.ext
  change (∑ j, a.1 i j * b.1 j l) = (∑ j, a.entry i j * b.entry j l).1
  exact (map_sum (IsIdempotentElem.cornerVal (R := k)
    (isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := ν.toFinsupp)))
      (fun j => a.entry i j * b.entry j l) Finset.univ).symm

end SpacedAlgebra

/-- The matrix of an ordinary sequence idempotent is supported only on its own sequence index. -/
theorem spacedHom_idem_val (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none) (i : KLR.Seq ν) :
    (spacedHom k hS hD hne hl (KLR.KLRAlgebra.e i)).1 =
      Matrix.single i i (e (spacedFull Γ i)) := by
  rw [KLR.KLRAlgebra.e, KLR.fe, spacedHom_mk, spacedFreeHom, FreeAlgebra.lift_ι_apply,
    genImg_idem, cornerLin_val, e_mul_e_self, e_mul_e_self]

/-- The ordinary KLR matrix entry between two fixed evenly spaced loadings. -/
def spacedEntryMap (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none) (i j : KLR.Seq ν) :
    KLR.KLRAlgebra k Γ.klrQ ν →ₗ[k] WeightedKLRAlgebra k Γ ν.toFinsupp :=
  (SpacedAlgebra.entryLinearMap i j).comp (spacedHom k hS hD hne hl).toLinearMap

@[simp] theorem spacedEntryMap_val (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    (i j : KLR.Seq ν) (a : KLR.KLRAlgebra k Γ.klrQ ν) :
    (spacedEntryMap hS hD hne hl i j a).1 = (spacedHom k hS hD hne hl a).1 i j := rfl

/-- Right sequence-idempotent support forces all other family columns to vanish. -/
theorem spacedEntryMap_eq_zero_of_right_support (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    {a : KLR.KLRAlgebra k Γ.klrQ ν} {j : KLR.Seq ν}
    (ha : a * KLR.KLRAlgebra.e j = a) (i l : KLR.Seq ν) (hlj : l ≠ j) :
    spacedEntryMap hS hD hne hl i l a = 0 := by
  apply Subtype.ext
  change (spacedHom k hS hD hne hl a).1 i l = 0
  conv_lhs => rw [← ha, map_mul]
  change ((spacedHom k hS hD hne hl a).1 *
    (spacedHom k hS hD hne hl (KLR.KLRAlgebra.e j)).1) i l = 0
  rw [spacedHom_idem_val, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  simp only [Matrix.single_apply, Ne.symm hlj, and_false, ite_false, mul_zero]

/-- Entries preserve composition of maps supported on a common sequence idempotent.
The weighted loading chambers need not be distinct. -/
theorem spacedEntryMap_mul_of_right_support (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    {a : KLR.KLRAlgebra k Γ.klrQ ν} (b : KLR.KLRAlgebra k Γ.klrQ ν)
    {j : KLR.Seq ν} (ha : a * KLR.KLRAlgebra.e j = a) (i l : KLR.Seq ν) :
    spacedEntryMap hS hD hne hl i l (a * b) =
      spacedEntryMap hS hD hne hl i j a * spacedEntryMap hS hD hne hl j l b := by
  change ((spacedHom k hS hD hne hl) (a * b)).entry i l = _
  rw [map_mul, SpacedAlgebra.entry_mul, Finset.sum_eq_single j]
  · rfl
  · intro t _ htj
    change spacedEntryMap hS hD hne hl i t a * spacedEntryMap hS hD hne hl t l b = 0
    rw [spacedEntryMap_eq_zero_of_right_support hS hD hne hl ha i t htj, zero_mul]
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

/-- The diagonal entry of a sequence idempotent is its spaced weighted chamber idempotent. -/
theorem spacedEntryMap_idem_self (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none) (i : KLR.Seq ν) :
    spacedEntryMap hS hD hne hl i i (KLR.KLRAlgebra.e i) = spacedW k Γ i := by
  apply Subtype.ext
  rw [spacedEntryMap_val, spacedHom_idem_val, Matrix.single_apply_same]
  rfl

/-- An idempotent supported on one ordinary sequence maps to an idempotent weighted entry. -/
theorem isIdempotentElem_spacedEntryMap (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    {a : KLR.KLRAlgebra k Γ.klrQ ν} (ha : IsIdempotentElem a) {i : KLR.Seq ν}
    (hi : a * KLR.KLRAlgebra.e i = a) :
    IsIdempotentElem (spacedEntryMap hS hD hne hl i i a) := by
  show spacedEntryMap hS hD hne hl i i a * spacedEntryMap hS hD hne hl i i a = _
  rw [← spacedEntryMap_mul_of_right_support hS hD hne hl a hi i i, ha.eq]

/-- Matrix entries preserve the ordinary KLR grading in Webster's weighted rank corner. -/
theorem GradingDatum.spacedEntryMap_mem_klrGrade (G : GradingDatum Γ)
    (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ i, Γ.loop i = none) {a : KLR.KLRAlgebra k Γ.klrQ ν} {d : ℤ}
    (ha : a ∈ (G.toKLRGrading hne hl).grade ν d) (i j : KLR.Seq ν) :
    spacedEntryMap hS hD hne hl i j a ∈ G.klrGrade ν.toFinsupp d :=
  G.spacedHom_entry_mem_grade hS hD hne hl ha i j

end Categorification.WeightedKLR
