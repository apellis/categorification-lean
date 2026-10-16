/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpWords
import Categorification.TwoRep.LinearCat
import Categorification.KLR.BaseChange

/-!
# Restriction of scalars for the positive-word evaluation

Supporting Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action` and Theorem `nondegenerate`: evaluate the presentation over `k`
in a Rouquier family in the actual bicategory `LinearCat L`, for a commutative
`k`-algebra `L`. The source presentation and its scalars are unchanged.

The category and whiskering restrictions are local, not global instances.
`RouqUpKLR.restrictScalars` proves compatibility of polynomial evaluation, including
the braid divided difference. `RouqUpKLR.brundan_kl_restrictScalars` therefore derives
the required Brundan relations over `k` from the KL relations over `L`, without a
scalar-compatibility hypothesis. `RouqFamily.upEvalSemilinear` and its component
`upEvalAtSemilinear` supply the semilinear evaluation needed to construct `UnfurledEval.Θ`.
Mixed inversion is still the separate input of the existing `upEval` construction.
No field, algebraic closure or characteristic hypothesis enters this scalar step.
-/

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
namespace Categorification.TwoRep
open KL3.Diagram
namespace ScalarRestriction
variable (k L : Type*) [CommRing k] [CommRing L] [Algebra k L]
variable (C : Type*) [Category C] [Preadditive C] [Linear L C]
/-- Restrict the Hom modules and their bilinear composition along `k → L`.
Use locally, to avoid introducing competing scalar structures. -/
@[instance_reducible] def linear : Linear k C where
  homModule X Y := Module.compHom (X ⟶ Y) (algebraMap k L)
  smul_comp X Y Z r f g := by
    exact Linear.smul_comp X Y Z (algebraMap k L r) f g
  comp_smul X Y Z f r g := by
    exact Linear.comp_smul X Y Z f (algebraMap k L r) g

variable {C}
/-- The restricted Hom action is the scalar action of the algebra tower. -/
theorem tower (X Y : C) : letI := linear k L C; IsScalarTower k L (X ⟶ Y) := by
  let _ := linear k L C
  refine ⟨fun r s f => ?_⟩
  change (r • s) • f = algebraMap k L r • (s • f)
  rw [Algebra.smul_def, mul_smul]

variable {k L}
/-- An L-linear functor is linear for the two restricted category structures. -/
theorem functor {D : Type*} [Category D] [Preadditive D] [Linear L D]
    (F : C ⥤ D) [F.Linear L] :
    letI := linear k L C; letI := linear k L D; F.Linear k := by
  let _ := linear k L C
  let _ := linear k L D
  exact ⟨fun f r => F.map_smul (algebraMap k L r) f⟩
end ScalarRestriction

universe wk wL v u ux
section Transfer
variable {k : Type wk} {L : Type wL} [CommRing k] [CommRing L] [Algebra k L]
  {I : Type*} {C : QuantumGroup.CartanDatum I} {X Y : Type ux}
  [AddCommGroup X] [AddCommGroup Y] {RD : QuantumGroup.UDot.WeightDatum C X Y}

local instance ScalarRestriction.linearCatHom (a b : LinearCat.{wL, v, u} L) :
    Linear k (a ⟶ b) := ScalarRestriction.linear k L _

private theorem ncEval_restrict {a b : LinearCat.{wL, v, u} L} (f : a ⟶ b) {n : ℕ}
    (y : Fin n → End f) (p : MvPolynomial (Fin n) k) :
    KLR.ncEval y p = KLR.ncEval y (MvPolynomial.map (algebraMap k L) p) := by
  exact KLR.map_ncEval (algebraMap k L) (RingHom.id (End f)) (fun _ => rfl) y p

/-- KLR relations descend along coefficient extension on the actual L-linear action. -/
theorem RouqUpKLR.restrictScalars {S : RouqFamily (B := LinearCat.{wL, v, u} L) RD}
    {Q : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S (fun i j => MvPolynomial.map (algebraMap k L) (Q i j))) :
    RouqUpKLR S Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ := by
    rw [ncEval_restrict]
    exact H.square i j hij h₁ h₂ h₃ h₄
  slide_left := H.slide_left
  slide_right := H.slide_right
  braid := H.braid
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ := by
    rw [ncEval_restrict, KLR.map_qbar]
    exact H.braidQ i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇

/-- The KL relations over L give Brundan's KL-scalar relations over k. -/
theorem RouqUpKLR.brundan_kl_restrictScalars {S : RouqFamily (B := LinearCat.{wL, v, u} L) RD}
    (H : RouqUpKLR S (KLR.klQ2 L C)) :
    BrundanUpKLR S (CL.CLScalars.kl : CL.CLScalars C k) := by
  apply RouqUpKLR.restrictScalars (L := L)
  apply H.of_eq
  intro i j _
  rw [brundanQ_eq_qCL _ (fun _ _ _ _ _ _ _ => rfl), CL.qCL_kl]
  simp only [KLR.klQ2]
  split_ifs <;> simp

local instance ScalarRestriction.precompLinear (a b c : LinearCat.{wL, v, u} L)
    (f : a ⟶ b) : (precomp c f).Linear k :=
  ScalarRestriction.functor (precomp c f)
local instance ScalarRestriction.postcompLinear (a b c : LinearCat.{wL, v, u} L)
    (g : b ⟶ c) : (postcomp a g).Linear k :=
  ScalarRestriction.functor (postcomp a g)

namespace RouqFamily
variable (S : RouqFamily (B := LinearCat.{wL, v, u} L) RD) (H : RouqUpKLR S (KLR.klQ2 L C))
  (M : BrundanMixedInversion S) (μ : X) {ν : Multiset I}

/-- Evaluation of the unchanged k-presentation in the L-linear action. -/
def upEvalSemilinear {t t' : KLR.Seq ν} :
    ((pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) →ₛₗ[algebraMap k L]
      (S.wordCell μ t ⟶ S.wordCell μ t') where
  toFun := S.upEval H.brundan_kl_restrictScalars M μ
  map_add' := S.upEval_add H.brundan_kl_restrictScalars M μ
  map_smul' r f := S.upEval_smul H.brundan_kl_restrictScalars M μ r f

/-- Evaluation at an object, with scalar extension still explicit. -/
def upEvalAtSemilinear (V : S.obj μ) {t t' : KLR.Seq ν} :
    ((pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) →ₛₗ[algebraMap k L]
      ((S.wordCell μ t).obj.obj V ⟶ (S.wordCell μ t').obj.obj V) where
  toFun f := (S.upEvalSemilinear H M μ f).hom.app V
  map_add' f g := by rw [map_add]; rfl
  map_smul' r f := by simp [map_smulₛₗ]

@[simp] theorem upEvalSemilinear_apply {t t' : KLR.Seq ν}
    (f : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.upEvalSemilinear H M μ f = S.upEval H.brundan_kl_restrictScalars M μ f := rfl

@[simp] theorem upEvalAtSemilinear_apply (V : S.obj μ) {t t' : KLR.Seq ν}
    (f : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.upEvalAtSemilinear H M μ V f =
      (S.upEval H.brundan_kl_restrictScalars M μ f).hom.app V := rfl

end RouqFamily
end Transfer
end Categorification.TwoRep
