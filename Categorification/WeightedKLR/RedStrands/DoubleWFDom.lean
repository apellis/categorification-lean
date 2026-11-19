/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleMixedRelations

/-!
# Well-formed relation domains of the double Stendhal presentations

The interpretation of a presentation through a layer map needs the domain of every relation to
be a well-formed object (`Presentation.WFDom`). Every family of relations adjoined in Webster,
arXiv:1309.3796v3, §4.5, Definition 4.24, has its boundaries given by region-labelled words
(`DoubleDiagram.obj`), which are well formed. This file records `WFDom` for each step of the
construction and for the downward block presentation used in the proof of Lemma 4.29.
-/

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe u v w

theorem _root_.StringDiagrams.Presentation.addRels_wfDom {S : StringDiagrams.Signature}
    {k : Type*} [CommRing k] {P : Presentation S k} (hP : P.WFDom) (ι : Type _)
    (dom cod : ι → Obj S) (rel : ∀ i, LinDiagram k (dom i) (cod i)) (h : ∀ i, (dom i).WF) :
    (P.addRels ι dom cod rel).WFDom
  | .inl r => hP r
  | .inr i => h i

theorem _root_.Categorification.KL3.Diagram.pres_wfDom {I : Type u} {C : CartanDatum I}
    {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (k : Type w)
    [CommRing k] : (KL3.Diagram.pres RD k).WFDom
  | .inl (.inl r) => r.elim
  | .inl (.inr (.inl c)) => Pivotal.colourObj_wf _ c
  | .inl (.inr (.inr c)) => Pivotal.dualObj_wf _ c
  | .inr r => by cases r <;> exact KL3.Diagram.ob_wf ..

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k]

theorem obj_wf (μ : X) (w : List (DoubleStrand I ℓ)) : (obj RD Λ μ w).WF := colours_ok ..

variable {RD Λ} {P P' : Presentation.{w, max u v} (signature RD Λ) k}

theorem union_wfDom (hP : P.WFDom) (hP' : P'.WFDom) : (P.union P').WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ hP'

theorem addDownRelations_wfDom (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hP : P.WFDom) : (addDownRelations RD Λ Q P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun _ => obj_wf ..

theorem addMixedBlackRelations_wfDom (t : I → I → kˣ) (hP : P.WFDom) :
    (addMixedBlackRelations RD Λ k t P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun a => by cases a <;> exact obj_wf ..

theorem addRedUpRelations_wfDom (hP : P.WFDom) : (addRedUpRelations RD Λ k P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun _ => obj_wf ..

theorem addRedCapRelations_wfDom (hP : P.WFDom) : (addRedCapRelations RD Λ P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun _ => obj_wf ..

theorem addRedCupRelations_wfDom (hP : P.WFDom) : (addRedCupRelations RD Λ P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun _ => obj_wf ..

theorem addRedUpSlideRelations_wfDom (hP : P.WFDom) : (addRedUpSlideRelations RD Λ P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun _ => obj_wf ..

theorem addMixedCupPitchforkRelations_wfDom (t : I → I → k) (hP : P.WFDom) :
    (addMixedCupPitchforkRelations RD Λ P t).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun _ => obj_wf ..

theorem addBlackAdjunctionRelations_wfDom (hP : P.WFDom) :
    (addBlackAdjunctionRelations RD Λ P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun a => by
    rcases a with ⟨kind, _, _, _, _⟩
    cases kind <;> exact obj_wf ..

theorem addBlackKLRelations_wfDom (hP : P.WFDom) : (addBlackKLRelations RD Λ P).WFDom :=
  Presentation.addRels_wfDom hP _ _ _ _ fun r =>
    ((blackMirror RD Λ).ok_word (KL3.Diagram.pres_wfDom RD k r)).1

theorem signedCapKLPresentation_wfDom (hP : P.WFDom) (Q : I → I → MvPolynomial (Fin 2) k)
    (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k) :
    (signedCapKLPresentation RD Λ P Q exponents t).WFDom :=
  union_wfDom (union_wfDom
    (addDownRelations_wfDom _ (addBlackAdjunctionRelations_wfDom
      (addMixedCupPitchforkRelations_wfDom _ (addRedUpRelations_wfDom
        (addRedUpSlideRelations_wfDom (addRedCapRelations_wfDom (addRedCupRelations_wfDom hP)))))))
    (addRedCapRelations_wfDom (addDownRelations_wfDom _ (addRedUpRelations_wfDom hP))))
    (addDownRelations_wfDom _ (addRedUpRelations_wfDom (addRedCapRelations_wfDom
      (addRedCupRelations_wfDom (addBlackKLRelations_wfDom hP)))))

end Categorification.Stendhal.DoubleDiagram
