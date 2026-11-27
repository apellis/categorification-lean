/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentEquiv
import DG.Homotopy.ComparisonRing
import DG.Derived.KProjective
import Categorification.Algebra.DerivedTensor
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Ordinary projective resolutions as dg models

The ordinary projective resolution in Webster, arXiv:1309.3796v2, §6.1, p. 65,
gives a K-projective dg model by putting the chain terms in nonpositive
cochain degrees. This construction retains the loading support of each term.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG ComplexShape
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe u

variable {R : Type u} [Ring R]

private theorem dg_ofComplex_kProjective (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [K.IsKProjective] : IsKProjective.{u} R ((DGModuleCat.ofComplex R).obj K) := by
  intro N _ _ _ _ hN f
  let P := (DGModuleCat.ofComplex R).obj K
  let Y := DGModuleCat.of R N
  let g : P ⟶ Y := DGModuleCat.ofHom f
  let G := DegreeZero.complexFunctor.{u} R
  have hY : (G.obj Y).Acyclic := by
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := hN n
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((DegreeZero.cohomologyAddEquiv Y n).symm.injective.subsingleton)
  let iso : G.obj P ≅ K := (DegreeZero.ofComplexCompIso R).app K
  let : (G.obj P).IsKProjective := CochainComplex.isKProjective_of_iso iso.symm
  apply (DegreeZero.homotopic_iff g 0).mpr
  rw [Functor.map_zero]
  exact CochainComplex.IsKProjective.nonempty_homotopy_zero _ hY

/-- The dg realization of a quasi-isomorphism of ordinary cochain complexes
is a quasi-isomorphism. -/
theorem dgModule_ofComplex_map_isQuasiIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    ((DGModuleCat.ofComplex R).map f).hom.IsQuasiIso := by
  let F := DGModuleCat.ofComplex R
  let G := DegreeZero.complexFunctor.{u} R
  apply (DegreeZero.homotopyFunctor_map_quotient_map_mem_quasiIso_iff (F.map f)).mp
  rw [DegreeZero.homotopyFunctor_map_quotient_map]
  change _root_.HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
    ((_root_.HomotopyCategory.quotient _ _).map ((F ⋙ G).map f))
  rw [_root_.HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  exact (quasiIso_iff_of_arrow_mk_iso _ f
    (Arrow.isoOfNatIso (DegreeZero.ofComplexCompIso R) (Arrow.mk f))).mpr inferInstance

variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)

abbrev projectiveResolutionDGModel := (DGModuleCat.ofComplex R).obj
  (P.complex.extend embeddingDownNat)

abbrev projectiveResolutionDGTarget := (DGModuleCat.ofComplex R).obj
  (((ChainComplex.single₀ _).obj X).extend embeddingDownNat)

/-- The projective resolution augmentation transported from the chain model to DG modules. -/
def projectiveResolutionDGAug : projectiveResolutionDGModel P ⟶ projectiveResolutionDGTarget (X := X) :=
  (DGModuleCat.ofComplex R).map (HomologicalComplex.extendMap P.π embeddingDownNat)

theorem projectiveResolutionDGAug_quasiIso : (projectiveResolutionDGAug P).hom.IsQuasiIso :=
  dgModule_ofComplex_map_isQuasiIso _

theorem projectiveResolutionDGModel_kProjective :
    IsKProjective.{u} R (projectiveResolutionDGModel P) := by
  let K : CochainComplex (ModuleCat.{u} R) ℤ := P.complex.extend embeddingDownNat
  have : ∀ n, Projective (K.X n) := by
    intro n
    by_cases hn : n ≤ 0
    · let j := (-n).toNat
      have hj : embeddingDownNat.f j = n := by
        change -(j : ℤ) = n
        dsimp [j]
        omega
      exact Projective.of_iso (P.complex.extendXIso embeddingDownNat hj).symm (P.projective j)
    · exact IsZero.projective (P.complex.isZero_extend_X embeddingDownNat n (by
        intro j hj
        change -(j : ℤ) = n at hj
        omega))
  let : K.IsKProjective := CochainComplex.isKProjective_of_projective K 0
  exact dg_ofComplex_kProjective K


/-- Higher loading support in a projective resolution gives off-zero homogeneous loading
support in its DG realization. -/
theorem projectiveResolutionDGModel_loading_support {ι : Type*} (e : ι → R) (good : ι → Prop)
    (hs : ∀ n : ℕ, ∃ (J : Type) (label : J → ι)
      (inc : ∀ i, lIdeal (e (label i)) →ₗ[R] P.complex.X (n + 1)),
      (∀ i, good (label i)) ∧ ∀ x : P.complex.X (n+1),
        x ∈ Submodule.span R {y | ∃ i z, inc i z = y})
    (j : ℤ) (hj : j ≠ 0) :
    ∃ (J : Type) (label : J → ι) (inc : ∀ i, lIdeal (e (label i)) →ₗ[R] projectiveResolutionDGModel P),
      (∀ i, good (label i)) ∧ ∀ x : projectiveResolutionDGModel P, x ∈ grading j →
        x ∈ Submodule.span R {y | ∃ i z, inc i z = y} := by
  let K : CochainComplex (ModuleCat.{u} R) ℤ := P.complex.extend embeddingDownNat
  let M := projectiveResolutionDGModel P
  let E : DegreeZero.gradingSubmodule R M j ≃ₗ[R] K.X j := DegreeZero.ofComplexXEquiv K j
  by_cases hz : 0 < j
  · refine ⟨Empty, Empty.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    intro x hx
    let x' : DegreeZero.gradingSubmodule R M j := ⟨x,hx⟩
    have hK : IsZero (K.X j) := P.complex.isZero_extend_X embeddingDownNat j (by
      intro n hn
      change -(n : ℤ) = j at hn
      omega)
    have := ModuleCat.isZero_iff_subsingleton.mp hK
    have hxz : x' = 0 := E.injective (Subsingleton.elim _ _)
    have he : x = 0 := congrArg Subtype.val hxz
    rw [he]
    exact Submodule.zero_mem _
  · have hn : j < 0 := by omega
    let n := (-j).toNat - 1
    have hjn : embeddingDownNat.f (n+1) = j := by
      change -((n+1 : ℕ) : ℤ) = j
      dsimp [n]
      omega
    obtain ⟨J,label,inc,hl,hspan⟩ := hs n
    let EI : K.X j ≃ₗ[R] P.complex.X (n+1) :=
      (P.complex.extendXIso embeddingDownNat hjn).toLinearEquiv
    let V := E.trans EI
    let v : P.complex.X (n+1) →ₗ[R] M :=
      (DegreeZero.gradingSubmodule R M j).subtype.comp V.symm.toLinearMap
    let W (i : J) := v.comp (inc i)
    refine ⟨J,label,W,hl,?_⟩
    intro x hx
    let x' : DegreeZero.gradingSubmodule R M j := ⟨x,hx⟩
    have hmap : (Submodule.span R {y | ∃ i z, inc i z = y}).map v ≤
        Submodule.span R {y | ∃ i z, W i z = y} := by
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro y ⟨_,⟨i,z,rfl⟩,rfl⟩
      exact Submodule.subset_span ⟨i,z,rfl⟩
    apply hmap
    exact ⟨V x', hspan (V x'), congrArg Subtype.val (V.symm_apply_apply x')⟩

/-- The cochain complex underlying a module placed in degree `0` is the module placed in degree
`0`. -/
def complexFunctorInDegreeZeroIso (X : ModuleCat.{u} R) :
    (DegreeZero.complexFunctor R).obj (DGModuleCat.of R (InDegreeZero X)) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj X := by
  let M := DGModuleCat.of R (InDegreeZero X)
  let K := (DegreeZero.complexFunctor R).obj M
  let L := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj X
  let e₀ : K.X 0 ≃ₗ[R] X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl)⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  let e (n : ℤ) : K.X n ≅ L.X n := by
    by_cases h : n = 0
    · subst n
      exact e₀.toModuleIso ≪≫ (HomologicalComplex.singleObjXSelf _ _ _).symm
    · have hK : IsZero (K.X n) := ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => by
        have hx : x.1 = 0 := ((InDegreeZero.mem_grading_iff _).mp x.2).resolve_left h
        have hy : y.1 = 0 := ((InDegreeZero.mem_grading_iff _).mp y.2).resolve_left h
        exact Subtype.ext (hx.trans hy.symm)⟩
      exact hK.iso (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  rintro i _ rfl
  have hd : K.d i (i+1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((DegreeZero.toComplex R M).d i (i+1) x).1 = 0
    exact (DegreeZero.toComplex_d_apply M (i := i) rfl x).trans (InDegreeZero.d_apply _ _)
  rw [hd, HomologicalComplex.single_obj_d, zero_comp, comp_zero]

/-- The DG realization of the degree-zero augmentation target is the ordinary module
concentrated in degree zero. -/
def projectiveResolutionDGTargetIso (X : ModuleCat.{u} R) :
    projectiveResolutionDGTarget (X := X) ≅ DGModuleCat.of R (InDegreeZero X) := by
  let G := DegreeZero.complexFunctor.{u} R
  let K := ((ChainComplex.single₀ _).obj X).extend embeddingDownNat
  let e : G.obj (projectiveResolutionDGTarget (X := X)) ≅ K :=
    (DegreeZero.ofComplexCompIso R).app K
  exact DegreeZero.complexFunctorFullyFaithful.preimageIso
    (e ≪≫ HomologicalComplex.extendSingleIso embeddingDownNat X 0 0 rfl ≪≫
      (complexFunctorInDegreeZeroIso X).symm)

/-- The chain resolution gives a DG augmentation to the ordinary module. -/
def projectiveResolutionDGAugToOrdinary :
    projectiveResolutionDGModel P ⟶ DGModuleCat.of R (InDegreeZero X) :=
  projectiveResolutionDGAug P ≫ (projectiveResolutionDGTargetIso X).hom

theorem projectiveResolutionDGAugToOrdinary_quasiIso :
    (projectiveResolutionDGAugToOrdinary P).hom.IsQuasiIso := by
  let := DG.HasDerivedCategory.standard.{u, u} R
  apply (DG.DerivedCategory.isIso_Q_map_iff (projectiveResolutionDGAugToOrdinary P)).mp
  rw [projectiveResolutionDGAugToOrdinary, Functor.map_comp]
  let := (DG.DerivedCategory.isIso_Q_map_iff (projectiveResolutionDGAug P)).mpr (projectiveResolutionDGAug_quasiIso P)
  infer_instance

end Categorification
