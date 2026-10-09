/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongMixed
import Categorification.Diagrams.CL.Rescale

/-!
# CL Theorem 1.1: a `Q`-strong 2-representation is a 2-representation of `U_Q(g)`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 1.1, for every (symmetrizable) Cartan datum: if the KLR action of a
`Q`-strong 2-representation (Definition 1.2) is given by CL's polynomials `Q = qCL S₀` and scalars
`r_i` for a choice of scalars `S₀ = (t, s, r)` (CL §2.3), the model of the 2-representation
(`Categorification.TwoRep.ModelQStrong`) descends to `U_{S₀}(g)` (`presCL RD k S₀`).

The model normalizes the dots (`r_i = 1`), so it respects `U_{Sc}(g)` for the rescaled scalars
`Sc` (`QStrong.respects_presCL_of_QStrong`, all relations including the mixed ones,
`Categorification.TwoRep.ModelQStrongMixed`); the rescaling isomorphism `U_{Sc}(g) ≅ U_{S₀}(g)`
(CL's Remark in §2.3, `RescaleDatum.equiv`) dividing the dots by `r_i` identifies the two.

## Main declarations

* `QStrong.clRescale`, `QStrong.clRescale_r`, `QStrong.clRescale_qCL`;
* `QStrong.interpUQ`: the 2-representation of `U_{S₀}(g)` on hom categories.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open KrullSchmidtCat (HomFinite)

universe w v u u₁

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : RootDatum C X Y}

namespace QStrong

/-- The weighted homogeneity of CL's polynomials, coefficientwise. -/
theorem qCL_support (S₀ : CL.CLScalars C k) {c d : I} (h : c ≠ d) :
    ∀ m ∈ (CL.qCL S₀ c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d := by
  intro m hm
  have := CL.qCL_isWeightedHomogeneous S₀ h (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm] using this

theorem qbar_qCL_support (S₀ : CL.CLScalars C k) {c d : I} (h : c ≠ d) :
    ∀ m ∈ (KLR.qbar (CL.qCL S₀ c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c) := by
  intro m hm
  have := CL.qbar_qCL_isWeightedHomogeneous S₀ h (MvPolynomial.mem_support_iff.1 hm)
  rw [C.symm d c]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_three, mul_comm] at this
  linarith

variable (RD) in
/-- The rescaling datum multiplying every dot on a strand `i` by `r_i` (crossings unchanged;
cups of upward strands rescaled as forced by the bubble relations). -/
def clRescale (S₀ : CL.CLScalars C k) : CL.RescaleDatum RD k where
  dot i := S₀.r i
  cross _ _ := 1
  cup c := if c.l.1 then S₀.r c.l.2 ^ (-1 - ip RD c.l.2 c.r) else 1
  cup_up i x := by simp

theorem clRescale_r (S₀ : CL.CLScalars C k) (i : I) :
    ((clRescale RD S₀).mapScalars S₀).r i = 1 := by
  simp [clRescale]

theorem clRescale_qCL (S₀ : CL.CLScalars C k) {c d : I} (h : c ≠ d) :
    CL.qCL ((clRescale RD S₀).mapScalars S₀) c d =
      CL.Rescale.scaleP ![(S₀.r c : k), (S₀.r d : k)] (CL.qCL S₀ c d) := by
  have := (clRescale RD S₀).scaleP_qCL S₀ h
  simp only [clRescale, mul_one, Units.val_one, map_one, one_mul] at this
  exact this.symm

theorem clRescale_presCL (S₀ : CL.CLScalars C k) :
    CL.presCL RD k ((clRescale RD S₀).inv.mapScalars ((clRescale RD S₀).mapScalars S₀)) =
      CL.presCL RD k S₀ := by
  rw [CL.RescaleDatum.mapScalars_inv]

variable (S₀ : CL.CLScalars C k) (S : QStrong B C RD k (CL.qCL S₀))
  (hrQ : ∀ i, S.rQ i = S₀.r i)

include hrQ in
theorem respects_clRescale (s₀ t₀ : X) :
    (CL.presCL RD k ((clRescale RD S₀).mapScalars S₀)).Respects
      (interp (S.genImg ((clRescale RD S₀).mapScalars S₀)) s₀ t₀).functor :=
  S.respects_presCL_of_QStrong _ (clRescale_r S₀)
    (fun c d h => by rw [clRescale_qCL S₀ h, hrQ c, hrQ d])
    (fun c d h => qCL_support S₀ h) (fun c d h => qbar_qCL_support S₀ h) s₀ t₀

include hrQ in
/-- **CL Theorem 1.1** (on hom categories, any Cartan datum): a `Q`-strong 2-representation whose
KLR action is given by CL's polynomials `Q = qCL S₀` and scalars `r_i = S₀.r i` defines a
2-representation of `U_{S₀}(g)`: the linear functor from the 2-morphisms of `U_{S₀}(g)` between
1-morphisms `t₀ → s₀` to `K^•(obj t₀, obj s₀)`, given by the rescaling isomorphism
`U_{S₀}(g) ≅ U_{Sc}(g)` and the model. -/
def interpUQ (s₀ t₀ : X) :
    (CL.presCL RD k S₀).Presented ⥤
      (S.model.lift.obj (fo (S := psig RD) t₀) ⟶ S.model.lift.obj (fo (S := psig RD) s₀)) :=
  ((clRescale RD S₀).inv.equiv ((clRescale RD S₀).mapScalars S₀) (clRescale_presCL S₀)).inverse ⋙
    (CL.presCL RD k _).lift (respects_clRescale S₀ S hrQ s₀ t₀)

end QStrong

end Model

end Categorification.TwoRep
