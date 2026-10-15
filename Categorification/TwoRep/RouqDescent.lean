/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissiblePseudo
import Categorification.TwoRep.RouqSoundness

/-!
# Normalized `presNM` quotient action

The unchanged `RouqFamily.genImg` annihilates the entire original horizontal
ideal and descends to a linear functor on each admissible component and a
pseudofunctor on `RevBicat (CL.presNM RD k Sc).Bicat`.

The hypotheses remain `RouqUpKLR S (CL.qCL Sc)`, global `Sc.r i = 1`, and
linear pre- and postwhiskering over the commutative coefficient ring. The Brundan
variant retains the explicit off-weight coefficient vanishing. No zero objects,
grading, Hom-finiteness or endomorphism dimension bounds are imposed.

This is descent for `presNM`, not for the full CL presentation: precisely the
distinct-colour left crossing cyclicities and distinct-colour down-up relations
are still excluded. The remaining mixed relations are included.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}
namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

/-- The whole original horizontal ideal of normalized `presNM` is annihilated. -/
theorem presNM_ideal (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram k a b) (hf : f ∈ (CL.presNM RD k Sc).ideal a b) :
    admissibleMap (S.genImg Sc) ha hb f = 0 :=
  admissibleMap_ideal (S.genImg Sc) (CL.presNM RD k Sc)
    (fun r {_ _} ha hb => S.presNM_rel Sc H hr r ha hb) Signature.IsEven.odd_eq_false ha hb f hf

/-- A linear functor on each admissible component of the original quotient. -/
def presNMFunctor (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1) (s t : X) :
    PresentedAdmissible (CL.presNM RD k Sc) s t ⥤ (S.model.obj t ⟶ S.model.obj s) :=
  admissiblePresentedInterp (S.genImg Sc) (CL.presNM RD k Sc)
    (fun r {_ _} ha hb => S.presNM_rel Sc H hr r ha hb) Signature.IsEven.odd_eq_false s t

instance presNMFunctor_additive (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    (s t : X) : (S.presNMFunctor Sc H hr s t).Additive :=
  admissiblePresentedInterp_additive (S.genImg Sc) (CL.presNM RD k Sc)
    (fun r {_ _} ha hb => S.presNM_rel Sc H hr r ha hb) Signature.IsEven.odd_eq_false s t

instance presNMFunctor_linear (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    (s t : X) : (S.presNMFunctor Sc H hr s t).Linear k :=
  admissiblePresentedInterp_linear (S.genImg Sc) (CL.presNM RD k Sc)
    (fun r {_ _} ha hb => S.presNM_rel Sc H hr r ha hb) Signature.IsEven.odd_eq_false s t

/-- Normalized `presNM` acts by a pseudofunctor in the original target bicategory. -/
def presNMPseudofunctor (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1) :
    Pseudofunctor (RevBicat (CL.presNM RD k Sc).Bicat) B :=
  admissiblePseudofunctor (S.genImg Sc) (fun r {_ _} ha hb => S.presNM_rel Sc H hr r ha hb)

/-- Descent preserves the original interpretation on every linear representative. -/
@[simp] theorem presNMPseudofunctor_map₂_lin
    (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    {a b : RevBicat (CL.presNM RD k Sc).Bicat} {x y : a ⟶ b}
    (f : LinDiagram k x.obj y.obj) :
    (S.presNMPseudofunctor Sc H hr).map₂ ((CL.presNM RD k Sc).lin f : x ⟶ y) =
      admissibleMap (S.genImg Sc) (PresPseudo.condW x) (PresPseudo.condW y) f := rfl

/-- The Brundan polynomial gives the same original quotient descent under the
explicit off-weight coefficient compatibility and global normalization. -/
def presNMPseudofunctorOfBrundan (H : BrundanUpKLR S Sc) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    Pseudofunctor (RevBicat (CL.presNM RD k Sc).Bicat) B :=
  S.presNMPseudofunctor Sc (H.toCL hq) hr

end RouqFamily
end Categorification.TwoRep