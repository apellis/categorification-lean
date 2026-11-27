/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationOf
import Categorification.Diagrams.CLQ.SymmetrySigma

/-!
# Well-founded domains of the `U_Q(g)` relations

The relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`;
`CLQ.pres RD k sc`) have well-founded domains. This is the input that the generic mirror
functor `blackMirrorIntoOf` needs, recorded as a named term of `Presentation.WFDom`.
-/

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type*) [CommRing k] (sc : CL.CLScalars C k)

/-- Every relation of `U_Q(g)` has a well-founded domain. -/
theorem clqPres_wfDomQ : (CLQ.pres RD k sc).WFDom := fun r => CLQ.pres_dom_wfQ r

end Categorification.Stendhal.DoubleDiagram
