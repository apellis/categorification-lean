/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTargetCharacter
import Categorification.WeightedKLR.Rigidity.FundamentalBraidTensorHomology

/-!
# Right-module homology of the fundamental braid

For the fundamental type A₁ case of Webster, arXiv:1309.3796v2,
Proposition 7.11, the middle homology of the braid-cut complex is the
middle head over the reversed order ring. Its cycle is supported on
the middle loading and the opposite-order middle character describes
the action there.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra MulOpposite CategoryTheory Coevaluation
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "ν" => ({()} : Multiset Unit)
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
local notation "Cut" s:arg => violCorner ℚ Q wt ν s [1,0]
local notation "S" => fundamentalBraidCutComplex
local notation "G" => fundamentalBraidCycle
local notation "E" => braidProject (e crossedMiddle)
local notation "C" => braidProject (ψ 1)
local notation "T" => TensorProductAlgebra ℚ Q wt ν

/-- The middle coevaluation head viewed over the reversed target order. -/
def braidTargetMiddleHead : ModuleCat Uᵐᵒᵖ :=
  (ModuleCat.restrictScalars fundamentalBraidTargetEquiv.toRingHom.op).obj
    (ModuleCat.of Tᵐᵒᵖ (rIdeal middleIdem ⧸ middleCutTrace))

private def dualEval : CupCoefficient ℚ MiddleCoefficient ≃+ ℚ where
  toFun f := (show Module.Dual ℚ MiddleCoefficient from f) (1 : ℚ)
  invFun c := c • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
  left_inv f := by
    apply LinearMap.ext
    intro a
    let f₀ : ℚ →ₗ[ℚ] ℚ := f
    change ℚ at a
    change f₀ 1 * a = f₀ a
    calc f₀ 1 * a = a * f₀ 1 := mul_comm _ _
         _ = f₀ (a • (1 : ℚ)) := (f₀.map_smul a 1).symm
         _ = f₀ a := congrArg f₀ (mul_one a)
  right_inv c := mul_one c
  map_add' _ _ := rfl

private def readHead : braidTargetMiddleHead ≃+ ℚ := middleQuotientDualEquiv.toAddEquiv.trans dualEval

private theorem readHead_smul (r : Uᵐᵒᵖ) (x : braidTargetMiddleHead) :
    readHead (r • x) = fundamentalBraidTargetCharacter r.unop * readHead x := by
  change (show Module.Dual ℚ MiddleCoefficient from middleQuotientDualEquiv
    (fundamentalBraidTargetEquiv.toRingHom.op r • (show rIdeal middleIdem ⧸ middleCutTrace from x))) (1 : ℚ) = _
  rw [map_smul]
  exact middleDual_smul_apply _ _ _

private abbrev scalarF : Cut middle →ₗ[ℚ] Cut terminal := (S).f.hom
private abbrev scalarG : Cut terminal →ₗ[ℚ] Cut middle := (S).g.hom
private theorem scalarG_zero : scalarG G = 0 := fundamentalBraidCycle_closed

private def rightF : Cut middle →ₗ[Uᵐᵒᵖ] Cut terminal where
  toFun z := (S).f z
  map_add' _ _ := (S).f.hom.map_add _ _
  map_smul' r z := Subtype.ext (mul_assoc (C) z.val r.unop.val).symm

private def rightG : Cut terminal →ₗ[Uᵐᵒᵖ] Cut middle where
  toFun z := (S).g z
  map_add' _ _ := (S).g.hom.map_add _ _
  map_smul' r z := Subtype.ext (mul_assoc (C) z.val r.unop.val).symm

/-- The mixed-crossing braid-cut complex with its right target action. -/
def fundamentalBraidRightCutComplex : ShortComplex (ModuleCat Uᵐᵒᵖ) :=
  ShortComplex.mk (ModuleCat.ofHom rightF) (ModuleCat.ofHom rightG) (by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun z => (S).moduleCat_zero_apply z)

private theorem cycle_action (r : U) :
    ∃ y : Cut middle, (S).f y = fundamentalBraidTargetCharacter r • G - op r • G := by
  let z := fundamentalBraidTargetCharacter r • G - op r • G
  have hz : (S).g z = 0 := by
    change rightG (fundamentalBraidTargetCharacter r • G - op r • G) = 0
    rw [map_sub,map_smul rightG]
    have hg : rightG G = 0 := fundamentalBraidCycle_closed
    rw [hg,smul_zero,sub_zero]
    change scalarG (fundamentalBraidTargetCharacter r • G) = 0
    rw [map_smul scalarG,scalarG_zero,smul_zero]
  apply (fundamentalBraidCycle_boundary_iff z hz).mpr
  have he : (G).val * r.val * E = fundamentalBraidTargetCharacter r • (G).val := by
    calc (G).val * r.val * E = (G).val * (E * r.val * E) := by
          rw [← mul_assoc,← mul_assoc,fundamentalBraidCycle_supported]
         _ = _ := by rw [fundamentalBraidTargetCorner_scalar,mul_smul_comm,fundamentalBraidCycle_supported]
  change (fundamentalBraidTargetCharacter r • (G).val - (G).val * r.val) * E = 0
  rw [sub_mul,smul_mul_assoc,fundamentalBraidCycle_supported,he,sub_self]

private def homologyOfRepresentatives {R : Type} [Ring R] (D : ShortComplex (ModuleCat.{0} R))
    (N : ModuleCat.{0} R) (rep : N →+ D.X₂) (hc : ∀ x, D.g (rep x) = 0)
    (hr : ∀ (a : R) (x : N), ∃ m : D.X₁, D.f m = rep (a • x) - a • rep x)
    (hi : ∀ (x : N) (m : D.X₁), D.f m = rep x → x = 0)
    (hs : ∀ z : D.X₂, D.g z = 0 → ∃ (x : N) (m : D.X₁), D.f m = rep x - z) :
    D.homology ≅ N := by
  let g : N →+ LinearMap.ker D.g.hom :=
    { toFun := fun x => ⟨rep x,hc x⟩
      map_zero' := Subtype.ext rep.map_zero
      map_add' := fun x y => Subtype.ext (rep.map_add x y) }
  let f : N →ₗ[R] (D.g.hom.ker ⧸ D.moduleCatToCycles.range) :=
    { D.moduleCatToCycles.range.mkQ.toAddMonoidHom.comp g with
      map_smul' := fun a x => by
        change D.moduleCatToCycles.range.mkQ (g (a • x)) = a • D.moduleCatToCycles.range.mkQ (g x)
        rw [← map_smul]
        apply (Submodule.Quotient.eq _).mpr
        obtain ⟨m,hm⟩ := hr a x
        exact ⟨m,Subtype.ext hm⟩ }
  have hin : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    change Submodule.Quotient.mk (p := D.moduleCatToCycles.range) (g x) = 0 at hx
    obtain ⟨m,hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact hi x m (congrArg Subtype.val hm)
  have hsur : Function.Surjective f := by
    intro z
    obtain ⟨y,rfl⟩ := D.moduleCatToCycles.range.mkQ_surjective z
    obtain ⟨x,m,hm⟩ := hs y.val y.property
    refine ⟨x,(Submodule.Quotient.eq _).mpr ?_⟩
    exact ⟨m,Subtype.ext hm⟩
  exact D.moduleCatHomologyIso ≪≫ (LinearEquiv.ofBijective f ⟨hin,hsur⟩).symm.toModuleIso

private def representative : braidTargetMiddleHead →+ Cut terminal :=
  (LinearMap.toSpanSingleton ℚ (Cut terminal) (G)).toAddMonoidHom.comp readHead.toAddMonoidHom

/-- The middle homology of the fundamental braid-cut complex, with the
right action of every diagram in the reversed order, is Webster's middle
coevaluation head (v2, Proposition 7.11, type A₁). -/
def fundamentalBraidRightCutHomologyIso : fundamentalBraidRightCutComplex.homology ≅ braidTargetMiddleHead := by
  apply homologyOfRepresentatives fundamentalBraidRightCutComplex braidTargetMiddleHead representative
  · intro x
    change scalarG (readHead x • G) = 0
    rw [map_smul scalarG,scalarG_zero,smul_zero]
  · intro r x
    obtain ⟨y,hy⟩ := cycle_action r.unop
    refine ⟨readHead x • y,?_⟩
    change scalarF (readHead x • y) = readHead (r • x) • G - r • (readHead x • G)
    rw [map_smul scalarF,show scalarF y = _ from hy,smul_sub,smul_smul,readHead_smul,mul_comm (readHead x)]
    apply Subtype.ext
    change _ - readHead x • ((G).val * r.unop.val) = _ - (readHead x • (G).val) * r.unop.val
    rw [smul_mul_assoc]
  · intro x m hm
    change (S).f m = readHead x • G at hm
    have hz : (S).g (readHead x • G) = 0 := by rw [← hm]; exact (S).moduleCat_zero_apply _
    have he := (fundamentalBraidCycle_boundary_iff _ hz).mp ⟨m,hm⟩
    change (readHead x • (G).val) * E = 0 at he
    rw [smul_mul_assoc,fundamentalBraidCycle_supported] at he
    exact readHead.injective ((smul_eq_zero.mp he).resolve_right fundamentalBraidCycle_ne_zero |>.trans readHead.map_zero.symm)
  · intro z hz
    obtain ⟨a,m,hm⟩ := fundamentalBraidCycle_mod_boundaries z hz
    obtain ⟨x,rfl⟩ := readHead.surjective a
    exact ⟨x,m,hm⟩

private theorem tensorF_apply (z : braidTensorMiddle) :
    braidTensorTerminalEquiv (braidTensorD₂ z) = rightF (braidTensorMiddleEquiv z) :=
  Subtype.ext (fundamentalBraidSourceResolution_tensor.1 z)

private theorem tensorG_apply (z : braidTensorTerminal) :
    braidTensorMiddleEquiv (braidTensorD₁ z) = rightG (braidTensorTerminalEquiv z) :=
  Subtype.ext (fundamentalBraidSourceResolution_tensor.2 z)

private def tensorRightF : braidTensorMiddle →ₗ[Uᵐᵒᵖ] braidTensorTerminal where
  __ := braidTensorD₂
  map_smul' r x := by
    change braidTensorD₂ (r • x) = r • braidTensorD₂ x
    apply braidTensorTerminalEquiv.injective
    rw [tensorF_apply,map_smul braidTensorTerminalEquiv,tensorF_apply,map_smul braidTensorMiddleEquiv,map_smul rightF]

private def tensorRightG : braidTensorTerminal →ₗ[Uᵐᵒᵖ] braidTensorMiddle where
  __ := braidTensorD₁
  map_smul' r x := by
    change braidTensorD₁ (r • x) = r • braidTensorD₁ x
    apply braidTensorMiddleEquiv.injective
    rw [tensorG_apply,map_smul braidTensorMiddleEquiv,tensorG_apply,map_smul braidTensorTerminalEquiv,map_smul rightG]

/-- The ordinary balanced tensor of the projective resolution of the source middle
head with the braid bimodule, retaining its target right action. -/
def fundamentalBraidRightTensorComplex : ShortComplex (ModuleCat Uᵐᵒᵖ) :=
  ShortComplex.mk (ModuleCat.ofHom tensorRightF) (ModuleCat.ofHom tensorRightG) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact fundamentalBraidTensorComplex.moduleCat_zero_apply z)

/-- The loading-cut comparison intertwines both induced tensor maps over the
target corner ring. -/
def fundamentalBraidRightTensorCutIso :
    fundamentalBraidRightTensorComplex ≅ fundamentalBraidRightCutComplex :=
  ShortComplex.isoMk braidTensorMiddleEquiv.toModuleIso braidTensorTerminalEquiv.toModuleIso
    braidTensorMiddleEquiv.toModuleIso
    (by apply ModuleCat.hom_ext; exact LinearMap.ext fun z => (tensorF_apply z).symm)
    (by apply ModuleCat.hom_ext; exact LinearMap.ext fun z => (tensorG_apply z).symm)

/-- In resolution degree one the homology of the balanced tensor with the braid
is the actual middle simple of the reversed order (Webster v2, Proposition 7.11,
fundamental type A₁). -/
def fundamentalBraidRightTensorHomologyIso :
    fundamentalBraidRightTensorComplex.homology ≅ braidTargetMiddleHead :=
  (ShortComplex.homologyFunctor _).mapIso fundamentalBraidRightTensorCutIso ≪≫ fundamentalBraidRightCutHomologyIso

theorem fundamentalBraidRightTensorComplex_ends :
    Function.Injective fundamentalBraidRightTensorComplex.f ∧ Function.Surjective fundamentalBraidRightTensorComplex.g :=
  fundamentalBraidTensorComplex_ends

end Categorification.Stendhal.FundamentalCorner
