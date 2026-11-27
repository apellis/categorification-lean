/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionComp
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionQ
import Categorification.WeightedKLR.RedStrands.DoubleRightWhiskerComp

/-!
# The action of a composite Khovanov–Lauda word

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. The action of a concatenation `s ++ t` of
Khovanov–Lauda words on the violating quotient is the action of `t` followed by the action
of `s`: the mirror word of `s ++ t` is the mirror word of `t` followed by that of `s`.

This is the version of `DoubleBlackActionComp` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

end Categorification.Stendhal.DoubleDiagram
