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
It therefore induces a functor of homotopy categories and
a functor of derived categories `DG.CatModule.weightForgetDerived A : D(C_A) ⥤ D(A)`, induced
by the universal property of the localization. On every dg module `N` over `C_A` it is
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

variable {A} in
/-- Forgetting the weights on homotopy categories preserves quasi-isomorphisms. -/
theorem weightForgetHomotopy_map_mem_quasiIso {M N : HomotopyCategory.{u} (WeightCategory A)}
    {f : M ⟶ N} (hf : HomotopyCategory.quasiIso (WeightCategory A) f) :
    DG.HomotopyCategory.quasiIso A ((weightForgetHomotopy A).map f) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective N
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _).map_surjective f
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
  change DG.HomotopyCategory.quasiIso A
    ((DG.HomotopyCategory.quotient A).map ((weightForget A).map f))
  rw [DG.HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact IsQuasiIso.weightSumMap hf

variable {A} in
/-- Forgetting the weights preserves K-projective objects of the homotopy category. -/
theorem weightForgetHomotopy_obj_mem_subcategoryKProjective
    {X : HomotopyCategory.{u} (WeightCategory A)}
    (hX : HomotopyCategory.subcategoryKProjective (WeightCategory A) X) :
    DG.HomotopyCategory.subcategoryKProjective A ((weightForgetHomotopy A).obj X) :=
  (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff
    ((weightForget A).obj X.as)).mpr
    ((HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff X.as).mp hX).weightSum

variable [CatModule.HasDerivedCategory.{w₁, u} (WeightCategory A)]
  [DG.HasDerivedCategory.{w₂, u} A]

/-- **The derived functor forgetting the weights**, `D(C_A) ⥤ D(A)`: forgetting the weights
preserves quasi-isomorphisms, so it descends to derived categories. -/
def weightForgetDerived :
    CatModule.DerivedCategory.{w₁, u} (WeightCategory A) ⥤ DG.DerivedCategory.{w₂, u} A :=
  Localization.lift (W := HomotopyCategory.quasiIso (WeightCategory A))
    (weightForgetHomotopy A ⋙ DG.DerivedCategory.Qh)
    (fun _ _ _ hf => Localization.inverts DG.DerivedCategory.Qh (DG.HomotopyCategory.quasiIso A)
      _ (weightForgetHomotopy_map_mem_quasiIso hf))
    CatModule.DerivedCategory.Qh

instance weightForgetDerivedLifting :
    Localization.Lifting CatModule.DerivedCategory.Qh
      (HomotopyCategory.quasiIso (WeightCategory A))
      (weightForgetHomotopy A ⋙ DG.DerivedCategory.Qh) (weightForgetDerived A) :=
  Localization.liftingLift _ _ _

/-- The derived forgetful functor is induced by forgetting the weights on homotopy
categories. -/
def QhCompWeightForgetDerivedIso :
    CatModule.DerivedCategory.Qh ⋙ weightForgetDerived A ≅
      weightForgetHomotopy A ⋙ DG.DerivedCategory.Qh :=
  Localization.Lifting.iso CatModule.DerivedCategory.Qh
    (HomotopyCategory.quasiIso (WeightCategory A)) _ _

/-- The derived forgetful functor is induced by forgetting the weights of dg modules. -/
def QCompWeightForgetDerivedIso :
    CatModule.DerivedCategory.Q ⋙ weightForgetDerived A ≅
      weightForget A ⋙ DG.DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (QhCompWeightForgetDerivedIso A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (weightForgetHomotopyFactors A) _ ≪≫ Functor.associator _ _ _

variable {A}

/-- **The derived forgetful functor is the weight sum on every dg module**. -/
def weightForgetDerivedQObjIso (N : CatModule.{u} (WeightCategory A)) :
    (weightForgetDerived A).obj (CatModule.DerivedCategory.Q.obj N) ≅
      DG.DerivedCategory.Q.obj ((weightForget A).obj N) :=
  (QCompWeightForgetDerivedIso A).app N

end Functor

end CatModule

end DG
