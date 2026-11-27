/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration
import DG.Derived.Heart

set_option backward.isDefEq.respectTransparency false

/-!
# Modules in degree zero inside the derived category

For an ordinary ring `B`, regarded as a dg ring concentrated in degree `0`, the functor
`ModuleCat B ⥤ D(B)` sending a module to itself in degree `0` is fully faithful
(`degreeZeroModuleFunctor_comp_Q_full`, `degreeZeroModuleFunctor_comp_Q_faithful`). This is
the heart of the standard t-structure (`DG.DerivedCategory.heartFunctor`): here `B` has no
negative part and zero differential, so `H⁰B = B` (`truncGEZeroRingEquiv`).

It is used for Webster, arXiv:1309.3796v3, Theorem 6.15, to compute morphisms in degree `0`
between the tilting modules `𝔅_τ P` as module maps.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DG.DerivedCategory
open scoped DG.DegreeZero

variable (B : Type) [Ring B]

/-- A ring in degree `0` is concentrated in non-positive degrees. -/
theorem isNonposGraded_degreeZero : IsNonposGraded B :=
  isNonposGraded_iff.mpr fun n hn r hr => by
    rcases (InDegreeZero.ring_mem_grading_iff (R := B)).1 hr with h | h
    · exact absurd h hn.ne'
    · exact h

/-- `H⁰B = B` for a ring in degree `0`. -/
def truncGEZeroRingEquiv : B ≃+* B ⧸ truncGEZeroIdeal (isNonposGraded_degreeZero B) :=
  RingEquiv.ofBijective (DGIdeal.Quotient.mkRingHom _)
    ⟨fun a b hab => by
      rw [← sub_eq_zero, ← map_sub, DGIdeal.Quotient.mkRingHom_eq_zero_iff_mem,
        mem_truncGEZeroIdeal_iff_of_mem_grading _
          ((InDegreeZero.ring_mem_grading_iff (R := B)).2 (Or.inl rfl))] at hab
      obtain ⟨c, -, hc⟩ := hab rfl
      rw [← sub_eq_zero, ← hc]
      rfl,
     DGIdeal.Quotient.mkRingHom_surjective _⟩

local notation "H" => B ⧸ truncGEZeroIdeal (isNonposGraded_degreeZero B)

/-- A `B`-module as an `H⁰B`-module, along `H⁰B ≃ B`. -/
abbrev toHeartModule : ModuleCat.{0} B ⥤ ModuleCat.{0} H :=
  ModuleCat.restrictScalars (truncGEZeroRingEquiv B).symm.toRingHom

variable {B} in
/-- A module in degree `0` over `B` is the corresponding `H⁰B`-module in degree `0`. -/
def degreeZeroHeartEquiv (M : ModuleCat.{0} B) :
    InDegreeZero M ≃ᵈᵍ[B] DegreeZeroModule (isNonposGraded_degreeZero B)
      ((toHeartModule B).obj M) where
  toFun m := DegreeZeroModule.mk (show (toHeartModule B).obj M from (InDegreeZero.equiv M m))
  invFun m := (InDegreeZero.equiv M).symm (show M from DegreeZeroModule.mk.symm m)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' b m :=
    (congrArg (fun c : B => c • (show M from m)) ((truncGEZeroRingEquiv B).symm_apply_apply b)).symm
  map_mem' {n m} hm := by
    rcases (InDegreeZero.mem_grading_iff _).1 hm with rfl | rfl
    · exact DegreeZeroModule.mem_grading_zero _
    · exact zero_mem _
  map_d' _ := rfl

variable [HasDerivedCategory.{0, 0} B]

/-- The degree-`0` embedding of `B`-modules is the heart functor along `H⁰B ≃ B`. -/
def degreeZeroHeartIso :
    degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q ≅
      toHeartModule B ⋙ heartFunctor.{0, 0} (isNonposGraded_degreeZero B) :=
  NatIso.ofComponents
    (fun M => DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv (degreeZeroHeartEquiv M)))
    fun f => by
      dsimp only [Functor.comp_map, Functor.mapIso_hom, heartFunctor]
      rw [← Functor.map_comp]
      change DG.DerivedCategory.Q.map _ = DG.DerivedCategory.Q.map _ ≫ DG.DerivedCategory.Q.map _
      rw [← Functor.map_comp]
      rfl

instance degreeZeroModuleFunctor_comp_Q_full :
    (degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q).Full :=
  Functor.Full.of_iso (degreeZeroHeartIso B).symm

instance degreeZeroModuleFunctor_comp_Q_faithful :
    (degreeZeroModuleFunctor B ⋙ DG.DerivedCategory.Q).Faithful :=
  Functor.Faithful.of_iso (degreeZeroHeartIso B).symm

end Categorification
