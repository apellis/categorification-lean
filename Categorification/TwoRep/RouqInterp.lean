/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqModel
import Categorification.Diagrams.BicatInterpAdmissible

/-!
# Ungraded interpretation on admissible Rouquier words

The free-diagram interpretation of `RouqFamily` takes values in the original bicategory.
Admissibility is part of the source object, so no target zero objects are required.
This is not yet the quotient by `presNM` or the full CL presentation.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory StringDiagrams
open QuantumGroup UDot KL3.Diagram Diagrams.BicatInterp

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B]

namespace AdditiveWhiskering

/-- The bicategorical additivity assumption gives an additive precomposition functor. -/
instance precomp_additive (a : B) {b c : B} (f : b ⟶ c) : (precomp a f).Additive where
  map_add := by intro X Y g h; exact whiskerLeft_add f g h

/-- The bicategorical additivity assumption gives an additive postcomposition functor. -/
instance postcomp_additive {a b : B} (c : B) (f : a ⟶ b) : (postcomp c f).Additive where
  map_add := by intro X Y g h; exact add_whiskerRight g h f

end AdditiveWhiskering

namespace RouqFamily

variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : RootDatum C X Y}
  (S : RouqFamily (B := B) RD)
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (Sc : CL.CLScalars C k)

/-- The ungraded functor on admissible free diagrams, with no zero-object hypothesis. -/
def interp (s t : X) : Admissible (S := psig RD) s t ⥤ (S.obj t ⟶ S.obj s) :=
  admissibleInterp (S.genImg Sc) s t

/-- Each admissible layer acts by the prescribed generator image and its whiskerings. -/
theorem interp_layer {s t : X} (L : Layer (psig RD)) (hv : L.Valid)
    (ha : Cond s t L.dom) :
    (S.interp Sc s t).map (ObjectProperty.homMk (P := Cond s t)
      (X := ⟨L.dom, ha⟩) (Y := ⟨L.cod, ha.cod hv⟩) (Diagram.ofLayer L hv)) =
      coreC (S.genImg Sc) (s₀ := s) (t₀ := t) hv ha :=
  admissibleInterp_layer (S.genImg Sc) L hv ha

/-- The linear free-diagram interpretation, still without zero objects. -/
def linearInterp (s t : X) : LinearAdmissible (S := psig RD) k s t ⥤
    (S.obj t ⟶ S.obj s) :=
  admissibleLinearInterp (S.genImg Sc) s t

instance linearInterp_additive (s t : X) : (S.linearInterp Sc s t).Additive :=
  admissibleLinearInterp_additive (M := S.model) (k := k) (S.genImg Sc) s t

instance linearInterp_linear (s t : X) : (S.linearInterp Sc s t).Linear k :=
  admissibleLinearInterp_linear (M := S.model) (k := k) (S.genImg Sc) s t

end RouqFamily
end Categorification.TwoRep
