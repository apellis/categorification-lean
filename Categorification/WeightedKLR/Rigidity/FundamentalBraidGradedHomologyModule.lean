/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedDerivedHomology
import DG.Category.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
/-!
# The homology module of the fundamental graded braid

For Webster, arXiv:1309.3796v2, §7.1, Proposition 7.11, the two tensor
differentials have injective and surjective ends. The image of the
derived braid is therefore the shifted middle homology in the abelian
category of modules on the target weight category.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.CatModule
universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  [CatModule.HasDerivedCategory.{z,w} C] (S : ShortComplex (CatModule.{w} C)) [Mono S.f] [Epi S.g]

omit [CatModule.HasDerivedCategory C] [Epi S.g] in
private theorem leftStep :
    (ShortComplex.mk S.f S.pOpcycles S.f_pOpcycles).ShortExact := by
  let T := ShortComplex.mk S.f S.pOpcycles S.f_pOpcycles
  let : Mono T.f := inferInstanceAs (Mono S.f)
  let : Epi T.g := inferInstanceAs (Epi S.pOpcycles)
  exact ⟨T.exact_of_g_is_cokernel S.opcyclesIsCokernel⟩

omit [CatModule.HasDerivedCategory C] [Mono S.f] in
private theorem rightStep :
    (ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles).ShortExact := by
  let T := ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles
  let : Mono T.f := inferInstanceAs (Mono S.homologyι)
  let : Epi T.g := epi_of_epi_fac S.p_fromOpcycles
  exact ⟨T.exact_of_f_is_kernel S.homologyIsKernel⟩

/-- A length-two complex of dg modules which is exact at both ends
represents its abelian middle homology shifted by one. -/
def weightTwoStageHomologyModuleIso :
    CatModule.DerivedCategory.Q.obj (cone (coneDescent S.f S.g S.zero)) ≅
      (CatModule.DerivedCategory.Q.obj S.homology)⟦(1 : ℤ)⟧ := by
  let Q := CatModule.DerivedCategory.Q (C := C)
  let k := coneDescent S.f S.pOpcycles S.f_pOpcycles
  let h := coneDescent S.f S.g S.zero
  have h1 := (CatModule.shortExact_iff _).mp (leftStep S)
  have kqi : IsQuasiIso k := coneDescent_quasiIso _ _ _ (fun X => (h1 X).1)
    (fun X => (h1 X).2.1) (fun X => (h1 X).2.2)
  have hk : IsIso (Q.map k) := (CatModule.DerivedCategory.isIso_Q_map_iff _).mpr kqi
  let e := @asIso _ _ _ _ (Q.map k) hk
  have sq : h = k ≫ S.fromOpcycles := by
    apply CatModule.Hom.ext
    intro X x
    exact (congrArg (fun j : S.X₂ ⟶ S.X₃ => j.app X (cone.sndAddHom S.f X x)) S.p_fromOpcycles).symm
  let a := Q.mapTriangle.obj (cone.triangle h)
  let b := Q.mapTriangle.obj (cone.triangle S.fromOpcycles)
  have hd {M N : CatModule.{w} C} (t : M ⟶ N) : Q.mapTriangle.obj (cone.triangle t) ∈ distTriang _ :=
    (CatModule.DerivedCategory.mem_distTriang_iff _).mpr ⟨_,_,t,⟨Iso.refl _⟩⟩
  have ab : a.mor₁ ≫ (Iso.refl _).hom = e.hom ≫ b.mor₁ := by
    change Q.map h ≫ 𝟙 _ = Q.map k ≫ Q.map S.fromOpcycles
    rw [Category.comp_id,← Q.map_comp,sq]
  let e1 := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ a b (hd h) (hd S.fromOpcycles) e (Iso.refl _) ab)
  have h2 := (CatModule.shortExact_iff _).mp (rightStep S)
  have t := exists_distinguished_weightTriangle_of_exact S.homologyι S.fromOpcycles
    S.homologyι_comp_fromOpcycles (fun X => (h2 X).1) (fun X => (h2 X).2.1) (fun X => (h2 X).2.2)
  let δ := t.choose
  have hδ := t.choose_spec
  let d := Triangle.mk (Q.map S.homologyι) (Q.map S.fromOpcycles) δ
  have hrot : d.rotate ∈ distTriang _ := rot_of_distTriang _ hδ
  have cmp : b.mor₁ ≫ (Iso.refl _).hom = (Iso.refl _).hom ≫ d.rotate.mor₁ := by
    change Q.map S.fromOpcycles ≫ 𝟙 _ = 𝟙 _ ≫ Q.map S.fromOpcycles
    rw [Category.comp_id, Category.id_comp]
  exact e1 ≪≫ Triangle.π₃.mapIso (isoTriangleOfIso₁₂ b d.rotate (hd S.fromOpcycles) hrot
    (Iso.refl _) (Iso.refl _) cmp)
end Categorification.Stendhal.FundamentalCorner

namespace Categorification.Stendhal.FundamentalCorner
open DG CategoryTheory BraidedStendhalAlgebra CatModule
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded

local notation "ν" => ({()} : Multiset Unit)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₀
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "he" => isIdempotentElem_violMk_redProj ℚ Q wt ν
local notation "h₀" => redProj_mem_violAuxiliaryGrade grading
local notation "DF" => diagramCornerWeightDerivedRightTensor V (he κ₀) (he κ₁) (h₀ κ₀) (h₀ κ₁)

local notation "SC" => fundamentalBraidTensorWeightModules
private theorem first_mono : Mono (SC).f := by
  apply (CatModule.mono_iff_injective _).mpr
  rintro ⟨n⟩
  exact (fundamentalBraidGradedTensorComplex_ends n).1

private theorem last_epi : Epi (SC).g := by
  apply (CatModule.epi_iff_surjective _).mpr
  rintro ⟨n⟩
  exact (fundamentalBraidGradedTensorComplex_ends n).2

universe z
variable [CatModule.HasDerivedCategory.{z,0} (WeightCategory Kᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{z,0} (WeightCategory Uᵐᵒᵖ)]

/-- Webster v2, Proposition 7.11 for two fundamental labels. As a module on
the target weight category, the derived braid on the middle head is the
middle homology of the two tensor crossings in cohomological degree minus one. -/
def fundamentalBraidGradedDerivedHomologyModuleIso :
    (DF).obj (CatModule.DerivedCategory.Q.obj fundamentalBraidSourceGradedHead) ≅
      (CatModule.DerivedCategory.Q.obj (SC).homology)⟦(1 : ℤ)⟧ := by
  let := first_mono
  let := last_epi
  exact fundamentalBraidGradedDerivedConeIso ≪≫ weightTwoStageHomologyModuleIso SC
end Categorification.Stendhal.FundamentalCorner
