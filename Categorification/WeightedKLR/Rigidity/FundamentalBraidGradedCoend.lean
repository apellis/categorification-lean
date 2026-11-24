/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.LoadingProjectiveCoend
import Categorification.WeightedKLR.Rigidity.FundamentalBraidGradedSource
import Categorification.WeightedKLR.Rigidity.FundamentalBraidWeightComplex

/-!
# The native graded tensor on the fundamental loading projectives

For Webster, arXiv:1309.3796v2, Proposition 7.11, at each target weight the
coend with a shifted fundamental loading projective is the homogeneous
component of the corresponding crossed loading cut.
-/
noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open BraidedStendhalAlgebra DG CategoryTheory CatModule DGOpposite QuantumGroup
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν" => ({()} : Multiset Unit)
local notation "κ₀" => List.finRange 2
local notation "κ₁" => ([1,0] : List (Fin 2))
local notation "μ" => stendhalWeight 2 ν
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₀
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) κ₁
local notation "V" => violAuxiliaryGrade («ν» := ν) grading
local notation "hE" => isIdempotentElem_violMk_redProj ℚ Q wt ν
local notation "S" κ:arg => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))
local instance fundamentalBraidCoendSourceCornerGrades : GradedAlgebra (Graded.cornerGrading V (hE κ₀)) :=
  Graded.cornerGradedAlgebra V (hE κ₀) (redProj_mem_violAuxiliaryGrade grading κ₀)
local instance fundamentalBraidCoendTargetCornerGrades : GradedAlgebra (Graded.cornerGrading V (hE κ₁)) :=
  Graded.cornerGradedAlgebra V (hE κ₁) (redProj_mem_violAuxiliaryGrade grading κ₁)
local instance fundamentalBraidCoendSourceInternal : InternalGrading Kᵐᵒᵖ := gradedAlgebraInternalGrading (S κ₀)
local instance fundamentalBraidCoendTargetInternal : InternalGrading Uᵐᵒᵖ := gradedAlgebraInternalGrading (S κ₁)
local instance fundamentalBraidCoendSourceBigraded : BigradedDGRing Kᵐᵒᵖ := gradedAlgebraBigradedDGRing (S κ₀)
local instance fundamentalBraidCoendTargetBigraded : BigradedDGRing Uᵐᵒᵖ := gradedAlgebraBigradedDGRing (S κ₁)
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "cut" s:arg => violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters s κ₁
local notation "B" => diagramCornerWeightRightBimodule V (hE κ₀) (hE κ₁)
  (redProj_mem_violAuxiliaryGrade grading κ₀) (redProj_mem_violAuxiliaryGrade grading κ₁)
local notation "A" => ViolQuotient ℚ Q wt ν
local notation "v" => violMk ℚ Q wt ν

variable (s : KLR.Seq μ) (hs : IsRedOrdered s) (j : ℤ) (Z : WeightCategory Uᵐᵒᵖ)
local notation "p" => fundamentalBraidSourceLoadingAt s hs j
local notation "pool" => CatBimodule.obj B Z (WeightCategory.mk j : WeightCategory Kᵐᵒᵖ)
local notation "Es" => v (ofKLR ℚ Q wt ν (KLR.KLRAlgebra.e s))
local notation "P₀" => v (redProj ℚ Q wt ν κ₀)
private theorem fixed_iff (x : pool) :
    x ∈ coendLoadingCut ((B).right Z) p ↔ Es * x.val.val = x.val.val := by
  change ((B).right Z).ract (p).val x = x ↔ _
  rw [CatBimodule.right_ract]
  exact ⟨fun h => congrArg (fun m : pool => m.val.val) h,
    fun h => Subtype.ext (Subtype.ext h)⟩

private def fixedLoadingIso :
    coendLoadingCut ((B).right Z) p ≃+ (cut s) (Z.as-j) where
  toFun x := ⟨⟨x.val.val.val,mem_violCorner_iff.mpr ⟨(fixed_iff s hs j Z x.val).mp x.property,
    (mem_cornerBimodule.mp x.val.val.property).2⟩⟩,x.val.property⟩
  invFun y := by
    have hc := mem_violCorner_iff.mp y.val.property
    have hleft : P₀ * Es = Es := by
      rw [← map_mul,redProj_mul_e,ite_eq_left ((redWord_eq_finRange_iff s).mpr hs)]
    have hcorner : P₀ * y.val.val = y.val.val :=
      (congrArg (P₀ * ·) hc.1.symm).trans
        ((mul_assoc _ _ _).symm.trans ((congrArg (· * y.val.val) hleft).trans hc.1))
    let x : pool := ⟨⟨y.val.val,mem_cornerBimodule.mpr ⟨hcorner,hc.2⟩⟩,y.property⟩
    exact ⟨x,(fixed_iff s hs j Z x).mpr hc.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The braid tensor of the native shifted loading projective, evaluated in
target weight Z, is its crossed loading cut in auxiliary degree Z−j. -/
def fundamentalBraidGradedCutIso :
    ((B).tensorFunctor.obj (corner p)).obj Z ≃+ (cut s) (Z.as-j) :=
  (coendLoadingIso ((B).right Z) p).trans (fixedLoadingIso s hs j Z)


/-- Tensoring a morphism of loading projectives acts on its crossed loading
cut by left multiplication by the image of the diagram generator. -/
theorem fundamentalBraidGradedCutIso_map (t : KLR.Seq μ) (ht : IsRedOrdered t) (k : ℤ)
    (g : corner p ⟶ corner (fundamentalBraidSourceLoadingAt t ht k))
    (z : ((B).tensorFunctor.obj (corner p)).obj Z) :
    ((fundamentalBraidGradedCutIso t ht k Z (((B).tensorFunctor.map g).app Z z)).val).val =
      (g.app ⟨j⟩ (cornerGen p)).val.val.unop.val * ((fundamentalBraidGradedCutIso s hs j Z z).val).val := by
  have h := coendLoadingEval_map ((B).right Z) p (fundamentalBraidSourceLoadingAt t ht k) g z
  have hact := (B).right_ract Z (g.app ⟨j⟩ (cornerGen p)).val (coendLoadingEval ((B).right Z) p z)
  exact congrArg (fun m : (B).obj Z (⟨k⟩ : WeightCategory Kᵐᵒᵖ) => m.val.val) (h.trans hact)


/-- A homogeneous target diagram acts on the loading coend by right multiplication. -/
theorem fundamentalBraidGradedCutIso_lact {Z' : WeightCategory Uᵐᵒᵖ} (f : Z ⟶ Z')
    (z : ((B).tensorFunctor.obj (corner p)).obj Z) :
    (fundamentalBraidGradedCutIso s hs j Z' ((B).tensorAct (corner p) f z)).val.val =
      (fundamentalBraidGradedCutIso s hs j Z z).val.val * f.val.unop.val :=
  congrArg (fun m : (B).obj Z' (⟨j⟩ : WeightCategory Kᵐᵒᵖ) => m.val.val)
    (coendLoadingEval_lact B p f z)
private theorem orderedMiddle : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel

/-- The coend on a fundamental loading is concentrated in cohomological degree
zero. Its degree-zero group is the auxiliary weight cut. -/
def fundamentalBraidGradedCutDGEquiv :
    DGAddEquiv (((B).tensorFunctor.obj (corner p)).obj Z) (InDegreeZero ((cut s) (Z.as-j))) where
  __ := fundamentalBraidGradedCutIso s hs j Z
  map_mem' {i z} hz := by
    have he := (coendLoadingEval_mem_grading ((B).right Z) p z i).mpr hz
    have hh : i = 0 ∨ coendLoadingEval ((B).right Z) p z = 0 :=
      (InDegreeZero.mem_grading_iff (M := diagramCornerWeight V (Z.as-j))).mp he
    apply (InDegreeZero.mem_grading_iff (M := (cut s) (Z.as-j))).mpr
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Subtype.ext (Subtype.ext (congrArg (fun m : pool => m.val.val) hh)))
  map_d' z := by
    have he := coendLoadingEval_d ((B).right Z) p z
    have hh : coendLoadingEval ((B).right Z) p (d z) = 0 := he.trans (InDegreeZero.d_apply _ _)
    exact Subtype.ext (Subtype.ext (congrArg (fun m : pool => m.val.val) hh))

/-- The first mixed crossing of the native braid tensor resolution gives the
diagrammatic differential on the middle cut at every target weight. -/
theorem fundamentalBraidGradedCutIso_d₂
    (z : ((B).tensorFunctor.obj (corner (fundamentalBraidSourceLoadingAt middle orderedMiddle 2))).obj Z) :
    (fundamentalBraidGradedCutIso terminal terminal_ordered 1 Z
      (((B).tensorFunctor.map fundamentalBraidGradedSourceD₂).app Z z)).val.val =
    braidProject (KLR.KLRAlgebra.ψ 1) * (fundamentalBraidGradedCutIso middle orderedMiddle 2 Z z).val.val := by
  have h := fundamentalBraidGradedCutIso_map middle orderedMiddle 2 Z terminal terminal_ordered 1
    fundamentalBraidGradedSourceD₂ z
  let x := (fundamentalBraidGradedCutIso middle orderedMiddle 2 Z z).val
  have hc := (congrArg Subtype.val fundamentalBraidGradedSourceD₂_generator).trans
    (diagonalMixed_val middle ((redWord_eq_finRange_iff _).mpr orderedMiddle) (by decide +kernel))
  exact h.trans ((congrArg (· * x.val) hc).trans ((mul_assoc _ _ _).trans
    (congrArg (braidProject (KLR.KLRAlgebra.ψ 1) * ·) (mem_violCorner_iff.mp x.property).1)))

/-- The second mixed crossing gives the diagrammatic differential on the
terminal cut at every target weight. -/
theorem fundamentalBraidGradedCutIso_d₁
    (z : ((B).tensorFunctor.obj (corner (fundamentalBraidSourceLoadingAt terminal terminal_ordered 1))).obj Z) :
    (fundamentalBraidGradedCutIso middle orderedMiddle 0 Z
      (((B).tensorFunctor.map fundamentalBraidGradedSourceD₁).app Z z)).val.val =
    braidProject (KLR.KLRAlgebra.ψ 1) * (fundamentalBraidGradedCutIso terminal terminal_ordered 1 Z z).val.val := by
  have h := fundamentalBraidGradedCutIso_map terminal terminal_ordered 1 Z middle orderedMiddle 0
    fundamentalBraidGradedSourceD₁ z
  let x := (fundamentalBraidGradedCutIso terminal terminal_ordered 1 Z z).val
  have hc := (congrArg Subtype.val fundamentalBraidGradedSourceD₁_generator).trans
    (diagonalMixed_val terminal ((redWord_eq_finRange_iff _).mpr terminal_ordered) (by decide +kernel))
  exact h.trans ((congrArg (· * x.val) hc).trans ((mul_assoc _ _ _).trans
    (congrArg (braidProject (KLR.KLRAlgebra.ψ 1) * ·) (mem_violCorner_iff.mp x.property).1)))

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]
  (P : Matrix.Realization (UDot.A C) ℂ H)
/-- Auxiliary target weight n corresponds to the physical resolution weight
n+3/2 in Webster v2, Proposition 7.11. -/
theorem fundamentalBraidCut_physicalWeight (s : KLR.Seq (stendhalWeight 2 ν)) (j n : ℤ) :
    Graded.shift (figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
      (weightPairing C P) (fun _ => braidFundamentalWeight P) s 1 0) (j : ℂ) ((n : ℂ) + 3 / 2) =
      violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters s [1,0] (n-j) := by
  let f := fun a : ℤ => (a : ℂ) + (2-weightPairing C P (braidFundamentalWeight P) (braidFundamentalWeight P))
  have hf : Function.Injective f := fun _ _ h => Int.cast_injective (add_right_cancel h)
  have he : f (n-j) = (n : ℂ) + 3 / 2 - (j : ℂ) := by
    dsimp [f]
    rw [braidFundamentalWeight_norm,Int.cast_sub]
    ring
  change Function.extend f _ ⊥ _ = _
  rw [← he,hf.extend_apply]

end Categorification.Stendhal.FundamentalCorner
