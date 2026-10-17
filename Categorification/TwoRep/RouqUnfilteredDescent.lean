/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUnfilteredSoundness

/-!
# Unfiltered Rouquier quotient action

Brundan, arXiv:1501.00350v1, Definition 1.1 and (1.26), in the
relation-preserving direction of the Main Theorem. The existing generator model
descends through the entire horizontal ideal of `CL.presUnfiltered` to linear
component functors and a pseudofunctor. The representative formulas identify
these with the original admissible interpretation. Rectangular parameters are
unrestricted, with source normalization `r_i = 1` and independent mixed inversion.
No homogeneity or zero-object hypothesis is imposed. This is before additive
completion and does not assert redundancy of the separately added downward
relations or the additive equivalence of presentations.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
variable [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

/-- The whole horizontal ideal of normalized `presUnfiltered` is annihilated. -/
theorem presUnfiltered_ideal (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram k a b) (hf : f ∈ (CL.presUnfiltered RD k Sc).ideal a b) :
    admissibleMap (S.genImg Sc) ha hb f = 0 :=
  admissibleMap_ideal (S.genImg Sc) (CL.presUnfiltered RD k Sc)
    (fun r {_ _} ha hb => S.presUnfiltered_rel Sc H M hr r ha hb) Signature.IsEven.odd_eq_false ha hb f hf

/-- A linear functor on each admissible component of the original quotient. -/
def presUnfilteredFunctor (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (s t : X) :
    PresentedAdmissible (CL.presUnfiltered RD k Sc) s t ⥤ (S.model.obj t ⟶ S.model.obj s) :=
  admissiblePresentedInterp (S.genImg Sc) (CL.presUnfiltered RD k Sc)
    (fun r {_ _} ha hb => S.presUnfiltered_rel Sc H M hr r ha hb) Signature.IsEven.odd_eq_false s t

instance presUnfilteredFunctor_additive (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (s t : X) : (S.presUnfilteredFunctor Sc H M hr s t).Additive :=
  admissiblePresentedInterp_additive (S.genImg Sc) (CL.presUnfiltered RD k Sc)
    (fun r {_ _} ha hb => S.presUnfiltered_rel Sc H M hr r ha hb) Signature.IsEven.odd_eq_false s t

instance presUnfilteredFunctor_linear (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (s t : X) : (S.presUnfilteredFunctor Sc H M hr s t).Linear k :=
  admissiblePresentedInterp_linear (S.genImg Sc) (CL.presUnfiltered RD k Sc)
    (fun r {_ _} ha hb => S.presUnfiltered_rel Sc H M hr r ha hb) Signature.IsEven.odd_eq_false s t

/-- The component functor agrees with the original map on every linear representative. -/
@[simp] theorem presUnfilteredFunctor_map_lin
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram k a b) :
    (S.presUnfilteredFunctor Sc H M hr s t).map
      (ObjectProperty.homMk
        (X := (⟨(CL.presUnfiltered RD k Sc).obj a, ha⟩ : PresentedAdmissible (CL.presUnfiltered RD k Sc) s t))
        (Y := (⟨(CL.presUnfiltered RD k Sc).obj b, hb⟩ : PresentedAdmissible (CL.presUnfiltered RD k Sc) s t))
        ((CL.presUnfiltered RD k Sc).lin f)) =
      admissibleMap (S.genImg Sc) (s := s) (t := t) ha hb f := rfl

/-- Normalized `presUnfiltered` acts by a pseudofunctor in the original target bicategory. -/
def presUnfilteredPseudofunctor (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (hr : ∀ i, Sc.r i = 1) :
    Pseudofunctor (RevBicat (CL.presUnfiltered RD k Sc).Bicat) B :=
  admissiblePseudofunctor (S.genImg Sc) (fun r {_ _} ha hb => S.presUnfiltered_rel Sc H M hr r ha hb)

/-- Descent preserves the original interpretation on every linear representative. -/
@[simp] theorem presUnfilteredPseudofunctor_map₂_lin
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    {a b : RevBicat (CL.presUnfiltered RD k Sc).Bicat} {x y : a ⟶ b}
    (f : LinDiagram k x.obj y.obj) :
    (S.presUnfilteredPseudofunctor Sc H M hr).map₂ ((CL.presUnfiltered RD k Sc).lin f : x ⟶ y) =
      admissibleMap (S.genImg Sc) (PresPseudo.condW x) (PresPseudo.condW y) f := rfl

end RouqFamily
end Categorification.TwoRep
