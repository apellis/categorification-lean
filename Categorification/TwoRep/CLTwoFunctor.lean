/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongCL
import Categorification.Diagrams.BicatInterpPseudo
import Categorification.Diagrams.CL.RescaleBicat

/-!
# CL Theorem 1.1 as a 2-functor on the 2-category of all-degree diagrams

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §1.2 ("Main results"), Theorem 1.1: a `Q`-strong 2-representation of `g` on
a graded additive `k`-linear 2-category `K` (Definition 1.2) extends to a 2-representation of
`U̇_Q(g)`, i.e. to a graded additive `k`-linear 2-functor `U̇_Q(g) → K` (the definition preceding
Theorem 1.1; "2-functor" is a weak 2-functor, §2.1.2).

`QStrong.interpUQ` (`Categorification.TwoRep.ModelQStrongCL`) proves the theorem one hom category
at a time. This file assembles these functors into **one pseudofunctor** compatible with
horizontal composition, on the 2-category `U_Q(g)^*` whose 2-morphisms are the diagrams of all
degrees (KL III's `HOM_U`, the presented bicategory of `presCL`), with values in the graded-Hom
bicategory `K^•` of the target (`GradedHomBicat B`, 2-morphisms of all degrees):

* `QStrong.twoFunctorHOM`: the composite of the rescaling 2-functor `U_{S₀}(g) → U_{Sc}(g)`
  (dots divided by `r_i`, a strict 2-functor, `CL.Rescale.pseudofunctor`) and the pseudofunctor of
  the model of the 2-representation (`Diagrams.BicatInterp.presPseudofunctor`, the universal
  property of the presented 2-category);
* `QStrong.twoFunctorHOM_obj`, `QStrong.twoFunctorHOM_map`: a weight `λ` goes to `obj λ`, a word to
  the composite of the images `E_i`, `F_i⟨…⟩` of its strands;
* `QStrong.twoFunctorHOM_map₂`: on 2-morphisms between 1-morphisms `t₀ → s₀` it is `interpUQ s₀ t₀`
  (up to the identification of the images of words).

The 1-morphisms of `RevBicat (presCL RD k S₀).Bicat` go from the weight on the right of a diagram
to the weight on its left, as in CL (`E_i 1_λ : λ → λ + α_i`). Grading shifts, formal direct sums
and the Karoubi completion (`U̇_Q(g)` itself, with target `K`) are added on top of this
pseudofunctor.
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

variable (S₀ : CL.CLScalars C k) (S : QStrong B C RD k (CL.qCL S₀))
  (hrQ : ∀ i, S.rQ i = S₀.r i)

/-- The rescaling 2-functor `U_{S₀}(g) → U_{Sc}(g)` dividing the dots by `r_i` (the inverse of
`(clRescale RD S₀).inv.equiv`, as in `interpUQ`). -/
abbrev clRescale₂ :
    Pseudofunctor (RevBicat (CL.presCL RD k S₀).Bicat)
      (RevBicat (CL.presCL RD k ((clRescale RD S₀).mapScalars S₀)).Bicat) :=
  CL.Rescale.pseudofunctor
    ((clRescale RD S₀).inv.lin_scL_rel_inv ((clRescale RD S₀).mapScalars S₀)
      (clRescale_presCL S₀))

include hrQ in
/-- **CL Theorem 1.1 on `HOM`** (arXiv:1111.1431v3, Theorem 1.1, any symmetrizable Cartan datum,
CL's hypotheses only): a `Q`-strong 2-representation (Definition 1.2) whose KLR action is given
by CL's polynomials `Q = qCL S₀` and scalars `r_i = S₀.r i` defines a pseudofunctor from the
2-category `U_{S₀}(g)` with 2-morphisms of all degrees (the presented bicategory of
`presCL RD k S₀`, 1-morphisms from right to left weights) to the graded-Hom bicategory `K^•`
of the target. It is compatible with horizontal composition (a pseudofunctor: the composition
constraints are the canonical isomorphisms between composites of the images of strands). -/
def twoFunctorHOM : Pseudofunctor (RevBicat (CL.presCL RD k S₀).Bicat) (GradedHomBicat B) :=
  (clRescale₂ S₀).comp
    (presPseudofunctor (S.genImg ((clRescale RD S₀).mapScalars S₀))
      (CL.presCL RD k ((clRescale RD S₀).mapScalars S₀)) (respects_clRescale S₀ S hrQ))

theorem twoFunctorHOM_obj (a : RevBicat (CL.presCL RD k S₀).Bicat) :
    (twoFunctorHOM S₀ S hrQ).obj a = S.model.lift.obj (fo (S := psig RD) a.as.region) := rfl

theorem twoFunctorHOM_map {a b : RevBicat (CL.presCL RD k S₀).Bicat} (x : a ⟶ b) :
    (twoFunctorHOM S₀ S hrQ).map x = PresPseudo.map₁ S.model
      ((clRescale₂ S₀).map x) := rfl

/-- On 2-morphisms, `twoFunctorHOM` is the rescaling followed by the interpretation of the model,
transported to the images of the words (`PresPseudo.map₂`). -/
theorem twoFunctorHOM_map₂ {a b : RevBicat (CL.presCL RD k S₀).Bicat} {x y : a ⟶ b}
    (η : x ⟶ y) :
    (twoFunctorHOM S₀ S hrQ).map₂ η =
      PresPseudo.map₂ (S.genImg ((clRescale RD S₀).mapScalars S₀)) (respects_clRescale S₀ S hrQ)
        ((clRescale₂ S₀).map₂ η) := rfl

/-- `interpUQ` is the same rescaling followed by the same interpretation, so that on the
2-morphisms between 1-morphisms with outer weights `s₀` (left) and `t₀` (right), `twoFunctorHOM`
is `interpUQ s₀ t₀` up to the identifications `objI_pos` of the images of the two words. -/
theorem interpUQ_map (s₀ t₀ : X) {a b : Obj (psig RD)}
    (f : (CL.presCL RD k S₀).obj a ⟶ (CL.presCL RD k S₀).obj b) :
    (interpUQ S₀ S hrQ s₀ t₀).map f =
      ((CL.presCL RD k ((clRescale RD S₀).mapScalars S₀)).lift
        (respects_clRescale S₀ S hrQ s₀ t₀)).map
        ((CL.Rescale.functor _ ((clRescale RD S₀).inv.lin_scL_rel_inv
          ((clRescale RD S₀).mapScalars S₀) (clRescale_presCL S₀))).map f) := rfl

end QStrong

end Model

end Categorification.TwoRep
