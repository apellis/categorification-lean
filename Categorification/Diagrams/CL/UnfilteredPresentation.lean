/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Presentation
import Categorification.TwoRep.RouqUpKLR

/-!
# The CL presentation with unfiltered Brundan parameters

Brundan, arXiv:1501.00350v1, Definition 1.1, (1.2)–(1.4): the square and braid
use every coefficient in the rectangle, without a weighted-degree restriction.
We replace only the upward KLR clause of `relationCL`, reusing its signature,
relation indices, pivotal base and all other equations. The source normalization
is `r_i = 1`; retaining `r` makes specialization to the existing CL API literal.

`presUnfiltered_eq_presCL` identifies the presentations when the off-weight
coefficients vanish. No such hypothesis enters `presUnfiltered` itself. The
additional downward family uses the dual parameters; its redundancy and the
full unfiltered Rouquier interpretation are not asserted here. In particular,
this is not yet the equivalence with the additive category of Definition 1.1.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation TwoRep

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- The CL relation family with the rectangular polynomial of Brundan (1.3),
including its divided difference in (1.4). Non-KLR relations are unchanged. -/
def relationUnfiltered (Sc : CLScalars C k) : (r : Rel RD) → LinDiagram k r.dom r.cod
  | .klr μ r => upLin RD k μ (relationR k (brundanQ Sc) (fun i => (Sc.r i : k)) r)
  | r => relationCL RD k Sc r

/-- The unfiltered presentation on the existing pivotal signature, before
additive completion. -/
def presUnfiltered (Sc : CLScalars C k) : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels (Rel RD) Rel.dom Rel.cod
    (relationUnfiltered RD k Sc)

/-- Biadjointness is retained from the pivotal base. -/
theorem presUnfiltered_zigzags (Sc : CLScalars C k) :
    (presUnfiltered RD k Sc).PivotalZigzags (inv RD).toColourDuality :=
  Presentation.pivotal_addRels_zigzags (inv RD).toColourDuality (pres0 RD k) _ _ _ _

/-- Every unfiltered defining relation vanishes in the presented category. -/
theorem presUnfiltered_lin_rel (Sc : CLScalars C k) (r : Rel RD) :
    (presUnfiltered RD k Sc).lin (relationUnfiltered RD k Sc r) = 0 :=
  (presUnfiltered RD k Sc).lin_rel_self (.inr r)

variable (Sc : CLScalars C k)
  (hhom : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)

include hhom in
/-- Specialization of every relation, not merely of its square polynomial. -/
theorem relationUnfiltered_eq_relationCL :
    relationUnfiltered RD k Sc = relationCL RD k Sc := by
  funext r
  cases r with
  | klr μ r =>
    change upLin RD k μ (relationR k (brundanQ Sc) _ r) =
      upLin RD k μ (relationR k (qCL Sc) _ r)
    rw [brundanQ_eq_qCL Sc hhom]
  | _ => rfl

include hhom in
/-- The homogeneous specialization is the existing presentation, with identical
relation indices and generators. -/
theorem presUnfiltered_eq_presCL : presUnfiltered RD k Sc = presCL RD k Sc := by
  unfold presUnfiltered presCL
  rw [relationUnfiltered_eq_relationCL RD k Sc hhom]

/-- The dual downward KLR family, retaining the entire rectangular sum. -/
def relationDownUnfiltered : (r : RelDown RD) → LinDiagram k r.dom r.cod
  | .klr μ r => dnLin RD k μ
      (relationR k (brundanQ Sc.dual) (fun i => (Sc.dual.r i : k)) r)

/-- The presentation with the dual downward equations explicitly added.
No redundancy theorem is part of this definition. -/
def presUnfilteredDown : Presentation.{w, max u v} (psig RD) k :=
  (presUnfiltered RD k Sc).addRels (RelDown RD) RelDown.dom RelDown.cod
    (relationDownUnfiltered RD k Sc)

include hhom in
/-- The dual downward family also specializes to the existing one. -/
theorem relationDownUnfiltered_eq_relationDown :
    relationDownUnfiltered RD k Sc = relationDown k Sc := by
  have hd : brundanQ Sc.dual = qCL Sc.dual := brundanQ_eq_qCL Sc.dual (by
    intro i j p q hp hq hdeg
    rw [CLScalars.dual_s, hhom i j p q hp hq hdeg, mul_zero])
  funext r
  cases r with
  | klr μ r =>
    change dnLin RD k μ (relationR k (brundanQ Sc.dual) _ r) =
      dnLin RD k μ (relationR k (qCL Sc.dual) _ r)
    rw [hd]

include hhom in
/-- Homogeneous specialization, including explicitly added downward relations. -/
theorem presUnfilteredDown_eq_presCLDown :
    presUnfilteredDown RD k Sc = presCLDown RD k Sc := by
  unfold presUnfilteredDown presCLDown
  rw [presUnfiltered_eq_presCL RD k Sc hhom,
    relationDownUnfiltered_eq_relationDown RD k Sc hhom]

end Categorification.KL3.Diagram.CL
