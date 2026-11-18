/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.CycMixed

/-!
# Closing Webster's cup pitchforks

Webster, arXiv:1309.3796v2, §2.2, (2.1a)–(2.1b), and v3, (2.2a)–(2.2b).
After vertical reflection into the CL convention, the cup pitchforks have
source one downward strand and target two downward strands and one upward
strand. A spectator downward strand and a cap give a relation between the
downward crossing and the rotated upward crossing. The straight branch
uses one interchange and a biadjunction identity. The mixed branch is the
rotated crossing when the sideways crossing is expressed as the upward mate.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (psig RD) k)

/-- The straight branch of the reflected mirror of Webster's downward cup pitchfork.
The through strand has colour `i` and the cup has colour `j`. -/
def cupPitchforkStraightR (j i : I) : List (LayerData I) :=
  [([], .cup (up j), [dn i]), ([up j], .cross false j i, [])]

/-- The mixed branch of the same pitchfork, with the sideways crossing written as
the corresponding mate of an upward crossing. -/
def cupPitchforkMateR (j i : I) : List (LayerData I) :=
  [([dn i], .cup (up j), [])] ++ (crossrL j i).map (whL [] [dn j])

/-- Closing the mirrored downward cup pitchfork gives the right rotation
normalization, with the same scalar. The hypothesis uses the mixed branch
with its upward mate, as supplied by Webster's next pitchfork family. -/
theorem rotCrossR_of_cupPitchfork
    (hz : P.PivotalZigzags (inv RD).toColourDuality) (j i : I) (μ : X) (t : k)
    (hp : t • dgC P μ [dn i] [up j, dn i, dn j] (cupPitchforkStraightR j i) =
      dgC P μ [dn i] [up j, dn i, dn j] (cupPitchforkMateR j i)) :
    P.diag (rotCrossR RD j i μ) = t • P.diag (downCross RD j i μ) := by
  let post : List (LayerData I) := [([], .cap (up j), [dn i, dn j])]
  let F := ctxLC P μ [dn j, dn i] [dn i, dn j] [] [dn j] [] post [dn i] [up j, dn i, dn j]
  have hc := congrArg F hp
  have hpre : SChain [dn j, dn i] [] ([dn j] ++ [dn i] ++ []) := rfl
  have hpost : SChain ([dn j] ++ [up j, dn i, dn j] ++ []) post [dn i, dn j] := ⟨rfl, rfl⟩
  rw [show F (t • dgC P μ [dn i] [up j, dn i, dn j] (cupPitchforkStraightR j i)) =
    t • F (dgC P μ [dn i] [up j, dn i, dn j] (cupPitchforkStraightR j i)) from map_smul F _ _] at hc
  simp only [F, ctxLC_dg_nil P μ hpre hpost] at hc
  have hstraight :
      dgC P μ [dn j, dn i] [dn i, dn j]
        [([dn j], .cup (up j), [dn i]), ([dn j, up j], .cross false j i, []),
          ([], .cap (up j), [dn i, dn j])] = P.diag (downCross RD j i μ) := by
    have hcross : dgC P μ [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])] =
        P.diag (downCross RD j i μ) := dgC_of (by schain)
    rw [← hcross]
    dswapC 1
    datC 0 [] [dn i] (dgC_zigR' P hz (wt RD μ [dn i]) (up j))
  change t • dgC P μ [dn j, dn i] [dn i, dn j]
        [([dn j], .cup (up j), [dn i]), ([dn j, up j], .cross false j i, []),
          ([], .cap (up j), [dn i, dn j])] =
      dgC P μ [dn j, dn i] [dn i, dn j]
        [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
          ([dn j, dn i], .cross true j i, [dn i, dn j]),
          ([dn j], .cap (up i), [up j, dn i, dn j]), ([], .cap (up j), [dn i, dn j])] at hc
  rw [hstraight, dgC_of (by schain)] at hc
  exact hc.symm

end Categorification.KL3.Diagram.CL
