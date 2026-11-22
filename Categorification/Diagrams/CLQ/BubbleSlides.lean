/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SlideCalculus
import Categorification.Diagrams.KL3.BubbleSlides

/-!
# Bubble slides in `U`: the case `i ≠ j`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.3 (TeX label `prop_bubble_slide1`), case `i ≠ j`.

KL III's proof: "For `i ≠ j` the equation follows from decomposing [a bubble next to a strand]
using the relations `eq_downup_ij-gen` and `eq_r2_ij-gen`." We give this argument as a
certificate chain of local moves (`dstepQ`): insert the identity `crossr ∘ crossl` (resp.
`crossl ∘ crossr`) of `eq_downup_ij-gen` between the strand and the bubble, pull the strand
through the bubble by the interchange law and two zigzag relations (`NF.dg_pull_ccw`,
`NF.dg_pull_cw`; these steps are valid for all `i, j` and are reused for `i = j`), and evaluate the
double crossing of upward strands with the dot slides `eq_dot_slide_ij-gen` and `eq_r2_ij-gen`.

The statements hold for an arbitrary Cartan datum, with the KL II polynomials
`Q_ij = u^{d_ij} + v^{d_ji}` (`1` if `i · j = 0`):

* `bubble_slide_ccw_ne`: a counterclockwise `i`-bubble with `m` dots to the right of an upward
  `j`-strand equals `(bubble with m + d_ij dots) + (bubble with m dots) x_j^{d_ji}` on the left
  (the bubble alone if `i · j = 0`);
* `bubble_slide_cw_ne`: the same for a clockwise bubble moved from left to right.

Auxiliary: `NF.dg_swap_rep`, `NF.dg_swap_rep'`, `NF.dg_swap_dots` (blocks of dots commute with
generators on other strands), `dg_dot_cap_dn`, `dg_dots_cap_dn`, `dg_cw_dots` (dots move around
a clockwise bubble, KL III (3.3)), `dg_slide_rep`, `dg_cross_dots_cross` (upward
computations), `NF.lin_bubR_ccwReal` etc. (the bubbles `bubR`, `bubL` of `Relations.lean` in normal
form).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Dots around caps -/

/-- A downward dot on the right strand of the cap `E_i F_i ⟶ 1` equals an upward dot on its left
strand (KL III (3.3) and a zigzag relation). -/
theorem dg_dot_cap_dn (ν : X) (i : I) :
    NF.dg (pres RD k sc) ν [up i, dn i] [] [([up i], .dot (dn i), []), ([], .cap (dn i), [])] =
      NF.dg (pres RD k sc) ν [up i, dn i] [] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] := by
  dstepQ [] [([], .cap (dn i), [])] [up i] [] (dg_cycDotL RD k sc i ν)
  dstepQ [([up i], .cup (dn i), [dn i]), ([up i, dn i], .dot (up i), [dn i])] [] [] []
    (NF.dg_swap' (pres RD k sc) ν [] [] [] (.cap (dn i)) (.cap (dn i))).symm
  dstepQ [([up i], .cup (dn i), [dn i])] [([], .cap (dn i), [])] [] []
    (NF.dg_swap' (pres RD k sc) ν [] [] [dn i] (.cap (dn i)) (.dot (up i))).symm
  dstepQ [] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] [] [dn i]
    (NF.dg_zigR' (pres RD k sc) (wt RD ν [dn i]) (dn i))
  simp

/-- `m` downward dots on the right strand of the cap `E_i F_i ⟶ 1` equal `m` upward dots on its
left strand. -/
theorem dg_dots_cap_dn (ν : X) (i : I) (m : ℕ) :
    NF.dg (pres RD k sc) ν [up i, dn i] [] (List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]) =
      NF.dg (pres RD k sc) ν [up i, dn i] [] (List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    dstepQ [([up i], .dot (dn i), [])] [] [] [] ih
    dstepQ [] [([], .cap (dn i), [])] [] []
      (NF.dg_swap_rep' (pres RD k sc) ν [] [] [] (.dot (dn i)) (.dot (up i)) rfl m).symm
    simp only [whL, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil]
    dstepQ (List.replicate m ([], .dot (up i), [dn i])) [] [] [] (dg_dot_cap_dn RD k sc ν i)
    simp [whL, List.replicate_succ']

/-- A clockwise bubble with `m` dots on its downward strand equals the clockwise bubble with `m`
dots on its upward strand. -/
theorem dg_cw_dots (ν : X) (i : I) (m : ℕ) :
    NF.dg (pres RD k sc) ν [] [] ([([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), []) ++
        [([], .cap (dn i), [])]) =
      NF.dg (pres RD k sc) ν [] [] ([([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i]) ++
        [([], .cap (dn i), [])]) := by
  dstepQ [([], .cup (up i), [])] [] [] [] (dg_dots_cap_dn RD k sc ν i m)
  simp [whL]

/-! ## Upward computations -/

/-- Dots on the right strand of `E_i E_j` (`i ≠ j`) slide down through the crossing to the
left strand (KL III `eq_dot_slide_ij-gen`, iterated). -/
theorem dg_slide_rep (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    NF.dg (pres RD k sc) ν [up i, up j] [up j, up i]
        ([([], .cross true i j, [])] ++ List.replicate m ([up j], .dot (up i), [])) =
      NF.dg (pres RD k sc) ν [up i, up j] [up j, up i]
        (List.replicate m ([], .dot (up i), [up j]) ++ [([], .cross true i j, [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ']
    refine (NF.dg_step (pres RD k sc) ν [] [([up j], .dot (up i), [])] [] [] ih (by schain) (by schain)
      (by simp [whL]) rfl).trans ?_
    refine (NF.dg_step (pres RD k sc) ν (List.replicate m ([], .dot (up i), [up j])) [] [] []
      (dg_slideRNe RD k sc ν i j h).symm (by schain) (by schain) (by simp [whL]) rfl).trans ?_
    simp [whL, List.replicate_succ']

/-- Dots on the upper left strand of the crossing `E_j E_i ⟶ E_i E_j` (`i ≠ j`) slide down to
the lower right strand (KL III `eq_dot_slide_ij-gen`, iterated). -/
theorem dg_slide_rep' (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    NF.dg (pres RD k sc) ν [up j, up i] [up i, up j]
        ([([], .cross true j i, [])] ++ List.replicate m ([], .dot (up i), [up j])) =
      NF.dg (pres RD k sc) ν [up j, up i] [up i, up j]
        (List.replicate m ([up j], .dot (up i), []) ++ [([], .cross true j i, [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ']
    refine (NF.dg_step (pres RD k sc) ν [] [([], .dot (up i), [up j])] [] [] ih (by schain) (by schain)
      (by simp [whL]) rfl).trans ?_
    refine (NF.dg_step (pres RD k sc) ν (List.replicate m ([up j], .dot (up i), [])) [] [] []
      (dg_slideLNe RD k sc ν j i h.symm) (by schain) (by schain) (by simp [whL]) rfl).trans ?_
    simp [whL, List.replicate_succ']

end Categorification.KL3.Diagram.CLQ
