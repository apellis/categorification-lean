/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Rewriting
import Categorification.Diagrams.KL3.Pitchfork
import Categorification.Diagrams.KL3.BubbleSlidesEq

/-!
# Dots sliding through the sideways crossings of `E_i F_i`

A dot on the downward strand of a sideways crossing of `E_i` and `F_i` slides through the
crossing up to a correction term that factors through `1_λ`. This follows from the cyclicity of
dots (M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, (3.3))
and the nilHecke dot slide `eq_nil_dotslide`; it is the identity used by Webster
(arXiv:1309.3796v2, (3.26) in the proof of Proposition 3.30) for the decomposition relations
under the weight shift of `U′`.

## Main results

* `dg_dot_crossr_self`: `x ≫ crossr = crossr ≫ x + cap ≫ cup` on `F_i E_i`;
* `dg_dot_crossl_self`: `x ≫ crossl = crossl ≫ x - cap ≫ cup` on `E_i F_i`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- A dot on the downward input strand of `crossr_{ii}` slides through it to the downward
output strand, up to the correction `cap ≫ cup`. -/
theorem dg_dot_crossr_self (ν : X) (i : I) :
    dg RD k ν [dn i, up i] [up i, dn i] (([], .dot (dn i), [up i]) :: crossrL i i) =
      dg RD k ν [dn i, up i] [up i, dn i] (crossrL i i ++ [([up i], .dot (dn i), [])]) +
        dg RD k ν [dn i, up i] [up i, dn i] [([], .cap (up i), []), ([], .cup (up i), [])] := by
  simp only [crossrL, List.cons_append, List.nil_append]
  dswap 0
  dswap 1
  dat 2 [] [up i, dn i] (dg_dot_cap_up RD k _ i)
  rw [dg_stepL_at _ 1 [dn i] [dn i] (dg_slideLEq RD k _ i) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  rw [map_add, ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain),
    ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain)]
  dnorm
  congr 1
  · dat 0 [dn i, up i] [] (dg_dot_cupUp RD k i _).symm
    dswap 1
    dswap 2
  · dswap 0

/-- `eq_nil_dotslide` solved for the crossing followed by a dot on its right output. -/
theorem dg_slideREq' (μ : X) (c : I) :
    dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([up c], .dot (up c), [])] =
      dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c]), ([], .cross true c c, [])] -
        dg RD k μ [up c, up c] [up c, up c] [] := by
  rw [dg_slideREq]; abel

/-- A dot on the downward input strand of `crossl_{ii}` slides through it to the downward
output strand, up to the correction `-(cap ≫ cup)`. -/
theorem dg_dot_crossl_self (ν : X) (i : I) :
    dg RD k ν [up i, dn i] [dn i, up i] (([up i], .dot (dn i), []) :: crosslL i i) =
      dg RD k ν [up i, dn i] [dn i, up i] (crosslL i i ++ [([], .dot (dn i), [up i])]) -
        dg RD k ν [up i, dn i] [dn i, up i] [([], .cap (dn i), []), ([], .cup (dn i), [])] := by
  simp only [crosslL, List.cons_append, List.nil_append]
  dswap 0
  dswap 1
  dat 2 [dn i, up i] [] (dg_dot_cap_dn RD k _ i)
  rw [dg_stepL_at _ 1 [dn i] [dn i] (dg_slideREq' RD k _ i) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  rw [map_sub, ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain),
    ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain)]
  dnorm
  congr 1
  · dat 0 [] [up i, dn i] (dg_dot_cupDn RD k i _)
    dswap 1
    dswap 2
  · dswap 0

end Categorification.KL3.Diagram
