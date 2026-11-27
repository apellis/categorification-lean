/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ResolutionAdjunction
import Categorification.Algebra.DerivedTensorHomology
import Categorification.Algebra.DerivedTensorRegular
import Categorification.Algebra.DerivedTensorCoproducts
import Categorification.Algebra.CompactGeneratorIsIso
import Categorification.Algebra.DerivedTensorComp
import DG.Derived.Perfect

set_option backward.isDefEq.respectTransparency false

/-!
# Comparing a composite of derived tensor products with a single one

For ordinary bimodules `M` over `(A, B)` and `N` over `(B, C)`, the composite
`M ⊗ᴸ_B (N ⊗ᴸ_C -)` maps to `M ⊗_B (N ⊗_C p(-))`, with `p` a K-projective resolution, by the
resolution map `p(N ⊗_C p X) ⟶ N ⊗_C p X` (`derivedTensorCompComparison`). On an ordinary
module `S` the resolution map tensored with `M` is the comparison of `M ⊗ᴸ_B S` with the ordinary
tensor product (`derivedTensorToOrdinary_eq`), so it is an isomorphism when the higher `Tor`
vanish; hence the comparison is an isomorphism at the regular module `C` when
`Tor^B_{>0}(M, N) = 0` (`isIso_derivedTensorCompComparison_app_regular`).

This is used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 6.12 (`𝔅_w ≅ 𝔅_{ws_i} ⊗ᴸ 𝔅_i`).
-/

open CategoryTheory Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w u

noncomputable section

namespace Categorification

section Resolution

variable {B : Type u} [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{w, u} B]

/-- On a K-projective object the resolution map is the unit of the K-projective equivalence. -/
theorem resolutionAdjunction_counit_app_ι (V : KProjective B) :
    (resolutionAdjunction.{w} B).counit.app ((HomotopyCategory.subcategoryKProjective B).ι.obj V) =
      (HomotopyCategory.subcategoryKProjective B).ι.map
        ((kProjectiveEquivalence.{w} B).unitIso.inv.app V) := by
  apply (ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    ((kProjectiveEquivalence.{w} B).inverse.obj
      (Qh.obj ((HomotopyCategory.subcategoryKProjective B).ι.obj V))).property Qh _).injective
  rw [Qh_map_resolutionAdjunction_counit_app]
  exact (kProjectiveEquivalence.{w} B).counit_app_functor V

end Resolution

section Comparison

variable {A B : Type u} [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

/-- The resolution map tensored with `M`, on an ordinary module `S`:
`M ⊗ᴸ_B S ⟶ M ⊗_B S`. -/
def derivedTensorResolutionMap (S : DGModuleCat.{u} B) :
    (derivedTensor.{w} A B M).obj (Q.obj S) ⟶
      Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj S) :=
  Qh.map ((DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)).map
      ((resolutionAdjunction.{w} B).counit.app ((DG.HomotopyCategory.quotient B).obj S))) ≫
    Qh.map ((DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom.app S)

variable {M} in
theorem derivedTensorObjIso_hom_comp {P S : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P)
    (f : P ⟶ S) :
    (derivedTensorObjIso (A := A) (M := M) hP).hom ≫
        Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f) =
      (derivedTensor.{w} A B M).map (Q.map f) ≫ derivedTensorResolutionMap.{w} (A := A) M S := by
  let q := DG.HomotopyCategory.quotient B
  let V : KProjective B :=
    ⟨q.obj P, (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  have h₁ := (resolutionAdjunction.{w} B).counit.naturality (q.map f)
  have h₂ := (DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A (InDegreeZero M)).hom.naturality f
  have h₃ := resolutionAdjunction_counit_app_ι.{w} V
  simp only [derivedTensorObjIso, derivedTensorResolutionMap, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv]
  rw [← h₃]
  change Qh.map (_ ≫ _) ≫ Qh.map ((DG.HomotopyCategory.quotient A).map
      ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)) =
    Qh.map ((DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)).map
      ((Qh ⋙ resolutionFunctor.{w} B).map (q.map f))) ≫ _
  rw [← Qh.map_comp, ← Qh.map_comp, ← Qh.map_comp]
  congr 1
  rw [← Category.assoc ((DG.HomotopyCategory.tensorFunctor A (InDegreeZero M)).map _),
    ← Functor.map_comp, h₁, Functor.map_comp, Category.assoc, Category.assoc, Functor.id_map]
  congr 1

/-- The comparison of `M ⊗ᴸ_B X` with `M ⊗_B X` for an ordinary module `X` is the resolution map
tensored with `M`. -/
theorem derivedTensorToOrdinary_eq (X : Type u) [AddCommGroup X] [Module B X] :
    derivedTensorToOrdinary.{w} (A := A) (B := B) (M := M) X =
      derivedTensorResolutionMap.{w} (A := A) M (DGModuleCat.of B (InDegreeZero X)) := by
  unfold derivedTensorToOrdinary
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    derivedTensorObjIso_hom_comp, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
  exact (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)

/-- **The resolution map tensored with `M` is an isomorphism** on an ordinary module `X` with
`Tor^B_{>0}(M, X) = 0`. -/
theorem isIso_derivedTensorResolutionMap (X : Type u) [AddCommGroup X] [Module B X]
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{w} A B M).obj (Q.obj (DGModuleCat.of B (InDegreeZero X)))))) :
    IsIso (derivedTensorResolutionMap.{w} (A := A) M (DGModuleCat.of B (InDegreeZero X))) := by
  rw [← derivedTensorToOrdinary_eq, ← derivedTensorIsoOrdinaryOfVanishing_hom.{w} X hv]
  infer_instance

end Comparison

section Composite

variable (A B C : Type u) [Ring A] [Ring B] [Ring C] (M N : Type u) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module B N]
  [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B] [HasDerivedCategory.{w, u} C]

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

local notation "TN" => DG.HomotopyCategory.tensorFunctor (B := C) B (InDegreeZero N)
local notation "TM" => DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M)

/-- The composite `M ⊗ᴸ_B (N ⊗ᴸ_C -)`, written as `M ⊗_B p(N ⊗_C p(-))`. -/
abbrev derivedTensorCompSource : DerivedCategory.{w, u} C ⥤ DerivedCategory.{w, u} A :=
  (resolutionFunctor.{w} C ⋙ TN) ⋙ (Qh ⋙ resolutionFunctor.{w} B) ⋙ (TM ⋙ Qh)

/-- The functor `M ⊗_B (N ⊗_C p(-))`. -/
abbrev derivedTensorCompTarget : DerivedCategory.{w, u} C ⥤ DerivedCategory.{w, u} A :=
  (resolutionFunctor.{w} C ⋙ TN) ⋙ 𝟭 _ ⋙ (TM ⋙ Qh)

/-- **The comparison** `M ⊗ᴸ_B (N ⊗ᴸ_C -) ⟶ M ⊗_B (N ⊗_C p(-))`, by the resolution map of
`N ⊗_C p(-)`. -/
def derivedTensorCompComparison :
    derivedTensorCompSource.{w} A B C M N ⟶ derivedTensorCompTarget.{w} A B C M N :=
  Functor.whiskerLeft (resolutionFunctor.{w} C ⋙ TN)
    (Functor.whiskerRight (resolutionAdjunction.{w} B).counit (TM ⋙ Qh))

instance : NatTrans.CommShift (derivedTensorCompComparison.{w} A B C M N) ℤ := by
  unfold derivedTensorCompComparison
  infer_instance

instance : (derivedTensorCompSource.{w} A B C M N).IsTriangulated := by
  have : (resolutionFunctor.{w} C ⋙ TN).IsTriangulated := inferInstance
  have : (Qh ⋙ resolutionFunctor.{w} B).IsTriangulated := inferInstance
  have : (TM ⋙ Qh).IsTriangulated := inferInstance
  infer_instance

instance : (derivedTensorCompTarget.{w} A B C M N).IsTriangulated := by
  have : (resolutionFunctor.{w} C ⋙ TN).IsTriangulated := inferInstance
  have : (TM ⋙ Qh).IsTriangulated := inferInstance
  infer_instance

variable {A B C M N} in
/-- The resolution map tensored with `M` is invertible on `Y` iff it is on an isomorphic `Y'`. -/
theorem isIso_map_counit_of_iso {Y Y' : DG.HomotopyCategory.{u} B} (e : Y ≅ Y')
    (h : IsIso ((TM ⋙ Qh).map ((resolutionAdjunction.{w} B).counit.app Y'))) :
    IsIso ((TM ⋙ Qh).map ((resolutionAdjunction.{w} B).counit.app Y)) := by
  have hn := (resolutionAdjunction.{w} B).counit.naturality e.hom
  have : (resolutionAdjunction.{w} B).counit.app Y =
      (Qh ⋙ resolutionFunctor.{w} B).map e.hom ≫ (resolutionAdjunction.{w} B).counit.app Y' ≫
        e.inv := by
    rw [← Category.assoc, hn, Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- `N ⊗_C p(C) ≅ N` in the homotopy category of `B`. -/
def resolutionTensorRegularIso :
    (resolutionFunctor.{w} C ⋙ TN).obj (Q.obj (DGModuleCat.of C C)) ≅
      (DG.HomotopyCategory.quotient B).obj (DGModuleCat.of B (InDegreeZero N)) :=
  let V : KProjective C := ⟨(DG.HomotopyCategory.quotient C).obj (DGModuleCat.of C C),
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff _).mpr
      (isKProjective_self (A := C))⟩
  Functor.mapIso TN ((HomotopyCategory.subcategoryKProjective C).ι.mapIso
      ((kProjectiveEquivalence.{w} C).unitIso.app V).symm) ≪≫
    (DG.HomotopyCategory.tensorFunctorQuotientIso B (InDegreeZero N)).app _ ≪≫
    (DG.HomotopyCategory.quotient B).mapIso (tensorRegularCoefficientIso B C N)

/-- **The comparison is invertible at the regular module** `C` when `Tor^B_{>0}(M, N) = 0`. -/
theorem isIso_derivedTensorCompComparison_app_regular
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{w} A B M).obj (Q.obj (DGModuleCat.of B (InDegreeZero N)))))) :
    IsIso ((derivedTensorCompComparison.{w} A B C M N).app (Q.obj (DGModuleCat.of C C))) := by
  refine isIso_map_counit_of_iso (resolutionTensorRegularIso.{w} B C N) ?_
  have h : IsIso ((TM ⋙ Qh).map ((resolutionAdjunction.{w} B).counit.app
      ((DG.HomotopyCategory.quotient B).obj (DGModuleCat.of B (InDegreeZero N)))) ≫
      Qh.map ((DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom.app
        (DGModuleCat.of B (InDegreeZero N)))) :=
    isIso_derivedTensorResolutionMap.{w} (A := A) M N hv
  exact IsIso.of_isIso_comp_right _
    (Qh.map ((DG.HomotopyCategory.tensorFunctorQuotientIso A (InDegreeZero M)).hom.app
      (DGModuleCat.of B (InDegreeZero N))))

end Composite

section Generation

variable (A B C : Type u) [Ring A] [Ring B] [Ring C] (M N : Type u) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module B N]
  [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B] [HasDerivedCategory.{u, u} C]

local instance (X : Type u) [AddCommGroup X] : Fact (∀ m : InDegreeZero X, m ∈ grading 0) :=
  ⟨fun _ => (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩

/-- A functor preserving coproducts indexed by `Type u` preserves those indexed by `ℕ`. -/
theorem preservesColimitsOfShape_discrete_nat {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete ℕ) F :=
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{u}) F

instance (J : Type u) : PreservesColimitsOfShape (Discrete J)
    (derivedTensorCompSource.{u} A B C M N) := by
  unfold derivedTensorCompSource
  infer_instance

instance (J : Type u) : PreservesColimitsOfShape (Discrete J)
    (derivedTensorCompTarget.{u} A B C M N) := by
  unfold derivedTensorCompTarget
  infer_instance

/-- **The comparison is invertible** when `Tor^B_{>0}(M, N) = 0`: then
`M ⊗ᴸ_B (N ⊗ᴸ_C -) ≅ M ⊗_B (N ⊗_C p(-))`. The regular module compactly generates `D(C)`. -/
theorem isIso_derivedTensorCompComparison
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{u} A B M).obj (Q.obj (DGModuleCat.of B (InDegreeZero N)))))) :
    IsIso (derivedTensorCompComparison.{u} A B C M N) := by
  have := preservesColimitsOfShape_discrete_nat.{u} (derivedTensorCompSource.{u} A B C M N)
  have := preservesColimitsOfShape_discrete_nat.{u} (derivedTensorCompTarget.{u} A B C M N)
  exact isIso_of_compactlyGenerates _ (compactlyGenerates (A := C))
    fun _ => isIso_derivedTensorCompComparison_app_regular.{u} A B C M N hv

open TensorProductOver.RightAction in
/-- **Derived tensor products compose when the higher `Tor` vanish**: if
`Tor^B_{>0}(M, N) = 0`, then `M ⊗ᴸ_B (N ⊗ᴸ_C -) ≅ (M ⊗_B N) ⊗ᴸ_C -`. No projectivity of `M` or
`N` is assumed. -/
def derivedTensorCompIsoOfTorVanishing
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{u} A B M).obj (Q.obj (DGModuleCat.of B (InDegreeZero N)))))) :
    derivedTensor.{u} B C N ⋙ derivedTensor.{u} A B M ≅
      dgDerivedTensor.{u} A C (TensorProductOver B (InDegreeZero M) (InDegreeZero N)) :=
  have := isIso_derivedTensorCompComparison A B C M N hv
  (asIso (derivedTensorCompComparison.{u} A B C M N) :
      derivedTensorCompSource.{u} A B C M N ≅ derivedTensorCompTarget.{u} A B C M N) ≪≫
    (Functor.isoWhiskerLeft (resolutionFunctor.{u} C)
      (Functor.isoWhiskerRight (homotopyTensorFunctorCompIso (InDegreeZero M) (InDegreeZero N))
        Qh) :
      resolutionFunctor.{u} C ⋙
          (DG.HomotopyCategory.tensorFunctor (B := C) B (InDegreeZero N) ⋙
            DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M)) ⋙ Qh ≅
        resolutionFunctor.{u} C ⋙
          DG.HomotopyCategory.tensorFunctor (B := C) A
            (TensorProductOver B (InDegreeZero M) (InDegreeZero N)) ⋙ Qh)

end Generation

end Categorification
