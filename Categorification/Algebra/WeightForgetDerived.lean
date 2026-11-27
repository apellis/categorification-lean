/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForget
import DG.Category.Derived.KProjective
import DG.Derived.KProjective
import DG.Module.CohomologyDirectSum

/-!
# The derived functor forgetting the weight grading

For a dg ring `A` with an internal grading, forgetting the weights of dg modules over
`C_A = DG.WeightCategory A` (`M ↦ ⨁ k, M⟨k⟩`, `DG.CatModule.weightForget`) preserves
quasi-isomorphisms, since cohomology commutes with direct sums
(`DG.CatModule.IsQuasiIso.weightSumMap`), and homotopies (`DG.CatModule.Homotopic.weightSumMap`).
It therefore induces a functor of homotopy categories and, computed on K-projective
representatives, a functor of derived categories
`DG.CatModule.weightForgetDerived A : D(C_A) ⥤ D(A)`. On every dg module `N` over `C_A` it is
the weight sum: `weightForgetDerived A (Q N) ≅ Q (⨁ k, N⟨k⟩)`
(`DG.CatModule.weightForgetDerivedQObjIso`).

This is the functor along which the graded braiding functors (B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, Definition 6.6) are compared with the
ungraded ones.
-/

open CategoryTheory DirectSum

universe w₁ w₂ v u

noncomputable section

namespace DG

namespace CatModule

open WeightCategory

section QuasiIso

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-- **Forgetting the weights preserves quasi-isomorphisms**: the cohomology of `⨁ k, M⟨k⟩` is
`⨁ k, Hⁿ(M⟨k⟩)`. -/
theorem IsQuasiIso.weightSumMap {M M' : CatModule.{v} (WeightCategory A)} {φ : M ⟶ M'}
    (hφ : IsQuasiIso φ) : (CatModule.weightSumMap φ).IsQuasiIso := by
  intro n
  let e : ∀ k : ℤ, cohomology (M.obj ⟨k⟩) n ≃+ cohomology (M'.obj ⟨k⟩) n :=
    fun k => AddEquiv.ofBijective (cohomologyMap φ ⟨k⟩ n) (hφ ⟨k⟩ n)
  let E : (⨁ k, cohomology (M.obj ⟨k⟩) n) ≃+ ⨁ k, cohomology (M'.obj ⟨k⟩) n :=
    DFinsupp.mapRange.addEquiv e
  have key : ∀ x, cohomology.map (CatModule.weightSumMap φ) n
      (cohomology.fromDirectSum (fun k => M.obj ⟨k⟩) n x) =
        cohomology.fromDirectSum (fun k => M'.obj ⟨k⟩) n (E x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of k y =>
      have hE : E (DirectSum.of _ k y) = DirectSum.of _ k (e k y) :=
        DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
      rw [hE, cohomology.fromDirectSum_of, cohomology.fromDirectSum_of]
      induction y using cohomology.induction_on with
      | h z =>
        change _ = cohomology.ofSummand (fun k => M'.obj ⟨k⟩) k n
          (cohomologyMap φ ⟨k⟩ n (cohomology.mk _ n z))
        rw [cohomology.ofSummand_mk, cohomology.map_mk, cohomologyMap_mk,
          cohomology.ofSummand_mk]
        congr 1
        exact Subtype.ext (weightSumMap_of φ k z)
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have h : ⇑(cohomology.map (CatModule.weightSumMap φ) n) =
      ⇑(((cohomology.directSumAddEquiv (fun k => M.obj ⟨k⟩) n).trans E).trans
        (cohomology.directSumAddEquiv (fun k => M'.obj ⟨k⟩) n).symm) :=
    funext fun z => by
      have hz := key (cohomology.directSumAddEquiv (fun k => M.obj ⟨k⟩) n z)
      rwa [← cohomology.directSumAddEquiv_symm_apply, AddEquiv.symm_apply_apply] at hz
  rw [h]
  exact AddEquiv.bijective _

end QuasiIso

section Functor

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

/-- Forgetting the weights: a dg module `M` over `C_A` goes to the dg `A`-module
`⨁ k, M⟨k⟩`. -/
abbrev weightForget : CatModule.{u} (WeightCategory A) ⥤ DGModuleCat.{u} A :=
  toBigraded A ⋙ BigradedDGModuleCat.toDGModuleCat A

omit [DGRing A] in
theorem weightForget_map_hom {M M' : CatModule.{u} (WeightCategory A)} (φ : M ⟶ M') :
    ((weightForget A).map φ).hom = CatModule.weightSumMap φ := rfl

/-- Forgetting the weights on homotopy categories. -/
def weightForgetHomotopy :
    HomotopyCategory.{u} (WeightCategory A) ⥤ DG.HomotopyCategory.{u} A :=
  CategoryTheory.Quotient.lift _ (weightForget A ⋙ DG.HomotopyCategory.quotient A)
    (fun _ _ _ _ h => DG.HomotopyCategory.eq_of_homotopy _ _ h.weightSumMap.some)

/-- The functor `weightForgetHomotopy A` is induced by `weightForget A`. -/
def weightForgetHomotopyFactors :
    HomotopyCategory.quotient (WeightCategory A) ⋙ weightForgetHomotopy A ≅
      weightForget A ⋙ DG.HomotopyCategory.quotient A :=
  CategoryTheory.Quotient.lift.isLift _ _ _

variable [CatModule.HasDerivedCategory.{w₁, u} (WeightCategory A)]
  [DG.HasDerivedCategory.{w₂, u} A]

/-- **The derived functor forgetting the weights**, `D(C_A) ⥤ D(A)`, computed on K-projective
representatives. -/
def weightForgetDerived :
    CatModule.DerivedCategory.{w₁, u} (WeightCategory A) ⥤ DG.DerivedCategory.{w₂, u} A :=
  (CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory A)).inverse ⋙
    (HomotopyCategory.subcategoryKProjective (WeightCategory A)).ι ⋙
    weightForgetHomotopy A ⋙ DG.DerivedCategory.Qh

variable {A}

/-- On a K-projective dg module the derived forgetful functor is the weight sum. -/
def weightForgetDerivedObjIso {P : CatModule.{u} (WeightCategory A)} (hP : IsKProjective P) :
    (weightForgetDerived A).obj (CatModule.DerivedCategory.Q.obj P) ≅
      DG.DerivedCategory.Q.obj ((weightForget A).obj P) := by
  let H := HomotopyCategory.subcategoryKProjective.{u} (WeightCategory A)
  let p : H.FullSubcategory := ⟨(HomotopyCategory.quotient _).obj P,
    (HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  let E := CatModule.DerivedCategory.kProjectiveEquivalence (WeightCategory A)
  exact (weightForgetHomotopy A ⋙ DG.DerivedCategory.Qh).mapIso
      (H.ι.mapIso (E.unitIso.symm.app p)) ≪≫
    DG.DerivedCategory.Qh.mapIso ((weightForgetHomotopyFactors A).app P)

/-- **The derived forgetful functor is the weight sum on every dg module**, through a
K-projective resolution. -/
def weightForgetDerivedObjIsoOfResolution {K N : CatModule.{u} (WeightCategory A)} (f : K ⟶ N)
    (hK : IsKProjective K) (hf : IsQuasiIso f) :
    (weightForgetDerived A).obj (CatModule.DerivedCategory.Q.obj N) ≅
      DG.DerivedCategory.Q.obj ((weightForget A).obj N) := by
  letI : IsIso (CatModule.DerivedCategory.Q.map f) :=
    (CatModule.DerivedCategory.isIso_Q_map_iff f).mpr hf
  letI : IsIso (DG.DerivedCategory.Q.map ((weightForget A).map f)) :=
    (DG.DerivedCategory.isIso_Q_map_iff _).mpr (IsQuasiIso.weightSumMap hf)
  exact ((weightForgetDerived A).mapIso (asIso (CatModule.DerivedCategory.Q.map f))).symm ≪≫
    weightForgetDerivedObjIso hK ≪≫ asIso (DG.DerivedCategory.Q.map ((weightForget A).map f))

/-- The derived forgetful functor on the image of an arbitrary dg module over `C_A`. -/
def weightForgetDerivedQObjIso (N : CatModule.{u} (WeightCategory A)) :
    (weightForgetDerived A).obj (CatModule.DerivedCategory.Q.obj N) ≅
      DG.DerivedCategory.Q.obj ((weightForget A).obj N) :=
  weightForgetDerivedObjIsoOfResolution (exists_kProjective_resolution N).choose_spec.choose
    (exists_kProjective_resolution N).choose_spec.choose_spec.1
    (exists_kProjective_resolution N).choose_spec.choose_spec.2.1

end Functor

end CatModule

end DG
