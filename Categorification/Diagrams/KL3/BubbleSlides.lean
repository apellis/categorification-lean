/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# Bubble slides in `U`: the case `i ≠ j`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.3 (TeX label `prop_bubble_slide1`), case `i ≠ j`.

KL III's proof: "For `i ≠ j` the equation follows from decomposing [a bubble next to a strand]
using the relations `eq_downup_ij-gen` and `eq_r2_ij-gen`." We give this argument as a
certificate chain of local moves (`dstep`): insert the identity `crossr ∘ crossl` (resp.
`crossl ∘ crossr`) of `eq_downup_ij-gen` between the strand and the bubble, pull the strand
through the bubble by the interchange law and two zigzag relations (`dg_pull_ccw`,
`dg_pull_cw`; these steps are valid for all `i, j` and are reused for `i = j`), and evaluate the
double crossing of upward strands with the dot slides `eq_dot_slide_ij-gen` and `eq_r2_ij-gen`.

The statements hold for an arbitrary Cartan datum, with the KL II polynomials
`Q_ij = u^{d_ij} + v^{d_ji}` (`1` if `i · j = 0`):

* `bubble_slide_ccw_ne`: a counterclockwise `i`-bubble with `m` dots to the right of an upward
  `j`-strand equals `(bubble with m + d_ij dots) + (bubble with m dots) x_j^{d_ji}` on the left
  (the bubble alone if `i · j = 0`);
* `bubble_slide_cw_ne`: the same for a clockwise bubble moved from left to right.

Auxiliary: `dg_swap_rep`, `dg_swap_rep'`, `dg_swap_dots` (blocks of dots commute with
generators on other strands), `dg_dot_cap_dn`, `dg_dots_cap_dn`, `dg_cw_dots` (dots move around
a clockwise bubble, KL III (3.3)), `dg_slide_rep`, `dg_cross_dots_cross` (upward
computations), `lin_bubR_ccwReal` etc. (the bubbles `bubR`, `bubL` of `Relations.lean` in normal
form).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Moving blocks of dots -/

/-- A block of `n` copies of a generator `h` with equal source and target (a dot) to the right
of a generator `g` slides below `g`. -/
theorem dg_swap_rep (μ : X) (a m b : List (Letter I)) (g h : Shape I) (hh : h.dom = h.cod)
    (n : ℕ) :
    dg RD k μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        (List.replicate n (a ++ g.dom ++ m, h, b) ++ [(a, g, m ++ h.cod ++ b)]) =
      dg RD k μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        ([(a, g, m ++ h.dom ++ b)] ++ List.replicate n (a ++ g.cod ++ m, h, b)) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    refine (dg_step RD k μ [(a ++ g.dom ++ m, h, b)] [] [] [] ih
      (by simp [hh]) (by simp) (by simp [whL, List.replicate_succ]) rfl).trans ?_
    refine (dg_step RD k μ [] (List.replicate n (a ++ g.cod ++ m, h, b)) [] []
      (dg_swap' RD k μ a m b g h).symm (by simp) (by
        simp only [List.nil_append, List.append_nil]
        exact SChain.replicate_of (by simp [hh]) n) (by simp [whL, hh]) rfl).trans ?_
    simp [whL, List.replicate_succ, hh]

/-- A block of `n` copies of a generator `h` with equal source and target (a dot) to the left
of a generator `g` slides below `g`. -/
theorem dg_swap_rep' (μ : X) (a m b : List (Letter I)) (g h : Shape I) (hh : h.dom = h.cod)
    (n : ℕ) :
    dg RD k μ (a ++ h.dom ++ m ++ g.dom ++ b) (a ++ h.cod ++ m ++ g.cod ++ b)
        (List.replicate n (a, h, m ++ g.dom ++ b) ++ [(a ++ h.cod ++ m, g, b)]) =
      dg RD k μ (a ++ h.dom ++ m ++ g.dom ++ b) (a ++ h.cod ++ m ++ g.cod ++ b)
        ([(a ++ h.dom ++ m, g, b)] ++ List.replicate n (a, h, m ++ g.cod ++ b)) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    refine (dg_step RD k μ [(a, h, m ++ g.dom ++ b)] [] [] [] ih
      (by simp [hh]) (by simp) (by simp [whL, List.replicate_succ]) rfl).trans ?_
    refine (dg_step RD k μ [] (List.replicate n (a, h, m ++ g.cod ++ b)) [] []
      (dg_swap' RD k μ a m b h g) (by simp) (by
        simp only [List.nil_append, List.append_nil]
        exact SChain.replicate_of (by simp [hh]) n) (by simp [whL, hh]) rfl).trans ?_
    simp [whL, List.replicate_succ, hh]

/-- Two blocks of dots on different strands commute. -/
theorem dg_swap_dots (μ : X) (a m b : List (Letter I)) (l l' : Letter I) (p q : ℕ) :
    dg RD k μ (a ++ [l] ++ m ++ [l'] ++ b) (a ++ [l] ++ m ++ [l'] ++ b)
        (List.replicate p (a ++ [l] ++ m, .dot l', b) ++ List.replicate q (a, .dot l, m ++ [l'] ++ b)) =
      dg RD k μ (a ++ [l] ++ m ++ [l'] ++ b) (a ++ [l] ++ m ++ [l'] ++ b)
        (List.replicate q (a, .dot l, m ++ [l'] ++ b) ++ List.replicate p (a ++ [l] ++ m, .dot l', b)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.replicate_succ]
    refine (dg_step RD k μ [] (List.replicate q (a, .dot l, m ++ [l'] ++ b)) [] []
      (dg_swap_rep RD k μ a m b (.dot l) (.dot l') rfl p) (by simp) (by
        simp only [List.nil_append, List.append_nil]
        exact SChain.replicate_of (by simp) q) (by simp [whL]) rfl).trans ?_
    refine (dg_step RD k μ [(a, .dot l, m ++ [l'] ++ b)] [] [] [] ih (by simp) (by simp)
      (by simp [whL]) rfl).trans ?_
    simp [whL]

/-! ## Dots around caps -/

/-- A downward dot on the right strand of the cap `E_i F_i ⟶ 1` equals an upward dot on its left
strand (KL III (3.3) and a zigzag relation). -/
theorem dg_dot_cap_dn (ν : X) (i : I) :
    dg RD k ν [up i, dn i] [] [([up i], .dot (dn i), []), ([], .cap (dn i), [])] =
      dg RD k ν [up i, dn i] [] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] := by
  dstep [] [([], .cap (dn i), [])] [up i] [] (dg_cycDotL RD k i ν)
  dstep [([up i], .cup (dn i), [dn i]), ([up i, dn i], .dot (up i), [dn i])] [] [] []
    (dg_swap' RD k ν [] [] [] (.cap (dn i)) (.cap (dn i))).symm
  dstep [([up i], .cup (dn i), [dn i])] [([], .cap (dn i), [])] [] []
    (dg_swap' RD k ν [] [] [dn i] (.cap (dn i)) (.dot (up i))).symm
  dstep [] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] [] [dn i]
    (dg_zigR' RD k (wt RD ν [dn i]) (dn i))
  simp [whL]

/-- `m` downward dots on the right strand of the cap `E_i F_i ⟶ 1` equal `m` upward dots on its
left strand. -/
theorem dg_dots_cap_dn (ν : X) (i : I) (m : ℕ) :
    dg RD k ν [up i, dn i] [] (List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]) =
      dg RD k ν [up i, dn i] [] (List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    dstep [([up i], .dot (dn i), [])] [] [] [] ih
    dstep [] [([], .cap (dn i), [])] [] []
      (dg_swap_rep' RD k ν [] [] [] (.dot (dn i)) (.dot (up i)) rfl m).symm
    simp only [whL, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.singleton_append]
    dstep (List.replicate m ([], .dot (up i), [dn i])) [] [] [] (dg_dot_cap_dn RD k ν i)
    simp [whL, List.replicate_succ']

/-- A clockwise bubble with `m` dots on its downward strand equals the clockwise bubble with `m`
dots on its upward strand. -/
theorem dg_cw_dots (ν : X) (i : I) (m : ℕ) :
    dg RD k ν [] [] ([([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), []) ++
        [([], .cap (dn i), [])]) =
      dg RD k ν [] [] ([([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i]) ++
        [([], .cap (dn i), [])]) := by
  dstep [([], .cup (up i), [])] [] [] [] (dg_dots_cap_dn RD k ν i m)
  simp [whL]

/-! ## Upward computations -/

/-- Dots on the right strand of `E_i E_j` (`i ≠ j`) slide down through the crossing to the
left strand (KL III `eq_dot_slide_ij-gen`, iterated). -/
theorem dg_slide_rep (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k ν [up i, up j] [up j, up i]
        ([([], .cross true i j, [])] ++ List.replicate m ([up j], .dot (up i), [])) =
      dg RD k ν [up i, up j] [up j, up i]
        (List.replicate m ([], .dot (up i), [up j]) ++ [([], .cross true i j, [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ']
    refine (dg_step RD k ν [] [([up j], .dot (up i), [])] [] [] ih (by schain) (by schain)
      (by simp [whL]) rfl).trans ?_
    refine (dg_step RD k ν (List.replicate m ([], .dot (up i), [up j])) [] [] []
      (dg_slideRNe RD k ν i j h).symm (by schain) (by schain) (by simp [whL]) rfl).trans ?_
    simp [whL, List.replicate_succ']

/-- The upward computation in the `i ≠ j` bubble slide: a crossing `E_i E_j ⟶ E_j E_i`, `m`
dots on the `i` strand, and the crossing back equal `x_i^m Q_ij(x_i, x_j)`. -/
theorem dg_cross_dots_cross (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k ν [up i, up j] [up i, up j]
        ([([], .cross true i j, [])] ++ List.replicate m ([up j], .dot (up i), []) ++
          [([], .cross true j i, [])]) =
      if C.dot i j = 0 then
        dg RD k ν [up i, up j] [up i, up j] (List.replicate m ([], .dot (up i), [up j]))
      else dg RD k ν [up i, up j] [up i, up j]
          (List.replicate (m + C.dij i j) ([], .dot (up i), [up j])) +
        dg RD k ν [up i, up j] [up i, up j]
          (List.replicate m ([], .dot (up i), [up j]) ++
            List.replicate (C.dij j i) ([up i], .dot (up j), [])) := by
  refine (dg_step RD k ν [] [([], .cross true j i, [])] [] [] (dg_slide_rep RD k ν i j h m)
    (by schain) (by schain) (by simp [whL]) rfl).trans ?_
  refine (dg_stepL RD k ν (List.replicate m ([], .dot (up i), [up j])) [] [] []
    (dg_sqNe RD k ν i j h) (by schain) (by schain) (by simp [whL])).trans ?_
  split_ifs
  · rw [ctxL_dg_nil RD k ν (by schain) (by schain)]
    simp [whL]
  · rw [map_add, ctxL_dg_nil RD k ν (by schain) (by schain),
      ctxL_dg_nil RD k ν (by schain) (by schain)]
    simp only [whL, List.map_replicate, List.nil_append, List.append_nil, List.replicate_add]

/-- Dots on the upper left strand of the crossing `E_j E_i ⟶ E_i E_j` (`i ≠ j`) slide down to
the lower right strand (KL III `eq_dot_slide_ij-gen`, iterated). -/
theorem dg_slide_rep' (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k ν [up j, up i] [up i, up j]
        ([([], .cross true j i, [])] ++ List.replicate m ([], .dot (up i), [up j])) =
      dg RD k ν [up j, up i] [up i, up j]
        (List.replicate m ([up j], .dot (up i), []) ++ [([], .cross true j i, [])]) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ']
    refine (dg_step RD k ν [] [([], .dot (up i), [up j])] [] [] ih (by schain) (by schain)
      (by simp [whL]) rfl).trans ?_
    refine (dg_step RD k ν (List.replicate m ([up j], .dot (up i), [])) [] [] []
      (dg_slideLNe RD k ν j i h.symm) (by schain) (by schain) (by simp [whL]) rfl).trans ?_
    simp [whL, List.replicate_succ']

/-- The upward computation in the clockwise `i ≠ j` bubble slide: a crossing
`E_j E_i ⟶ E_i E_j`, `m` dots on the `i` strand, and the crossing back equal
`x_i^m Q_ij(x_i, x_j)`. -/
theorem dg_cross_dots_cross' (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k ν [up j, up i] [up j, up i]
        ([([], .cross true j i, [])] ++ List.replicate m ([], .dot (up i), [up j]) ++
          [([], .cross true i j, [])]) =
      if C.dot i j = 0 then
        dg RD k ν [up j, up i] [up j, up i] (List.replicate m ([up j], .dot (up i), []))
      else dg RD k ν [up j, up i] [up j, up i]
          (List.replicate (m + C.dij i j) ([up j], .dot (up i), [])) +
        dg RD k ν [up j, up i] [up j, up i]
          (List.replicate m ([up j], .dot (up i), []) ++
            List.replicate (C.dij j i) ([], .dot (up j), [up i])) := by
  refine (dg_step RD k ν [] [([], .cross true i j, [])] [] [] (dg_slide_rep' RD k ν i j h m)
    (by schain) (by schain) (by simp [whL]) rfl).trans ?_
  refine (dg_stepL RD k ν (List.replicate m ([up j], .dot (up i), [])) [] [] []
    (dg_sqNe RD k ν j i h.symm) (by schain) (by schain) (by simp [whL])).trans ?_
  rw [C.symm j i]
  split_ifs
  · rw [ctxL_dg_nil RD k ν (by schain) (by schain)]
    simp [whL]
  · rw [map_add, ctxL_dg_nil RD k ν (by schain) (by schain),
      ctxL_dg_nil RD k ν (by schain) (by schain), add_comm]
    simp only [whL, List.map_replicate, List.nil_append, List.append_nil, List.replicate_add]

/-! ## Bubble slides for `i ≠ j` -/

set_option maxHeartbeats 1000000 in
/-- **Pulling a strand through a counterclockwise bubble.** After inserting `crossr ∘ crossl`
between an upward `j`-strand and a counterclockwise `i`-bubble on its right, the interchange law
and two zigzag relations turn the diagram into the left closure of `ψ_{ji} x^m ψ_{ij}` (the
strand crosses the upward arc of the bubble twice). Valid for all `i, j`. -/
theorem dg_pull_ccw (lam : X) (i j : I) (m : ℕ) :
    dg RD k lam [up j] [up j]
        ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
          (crosslL j i ++ crossrL j i).map (whL [] [up i]) ++ [([up j], .cap (up i), [])]) =
      dg RD k lam [up j] [up j]
        ([([], .cup (dn i), [up j]), ([dn i], .cross true i j, [])] ++
          List.replicate m ([dn i, up j], .dot (up i), []) ++
          [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) := by
  simp only [crosslL, crossrL]
  -- 2., 3. interchange: move the bubble's cap below the crossing of `crossr`
  dstep ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
      [([], .cup (dn i), [up j, dn i, up i]), ([dn i], .cross true i j, [dn i, up i]),
        ([dn i, up j], .cap (dn i), [up i]), ([dn i, up j], .cup (up i), [up i]),
        ([dn i], .cross true j i, [dn i, up i])]) [] [] []
    (dg_swap' RD k lam [] [up j] [] (.cap (up i)) (.cap (up i)))
  dstep ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
      [([], .cup (dn i), [up j, dn i, up i]), ([dn i], .cross true i j, [dn i, up i]),
        ([dn i, up j], .cap (dn i), [up i]), ([dn i, up j], .cup (up i), [up i])])
    [([], .cap (up i), [up j])] [] []
    (dg_swap' RD k lam [dn i] [] [] (.cross true j i) (.cap (up i)))
  -- 4. zigzag
  dstep ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
      [([], .cup (dn i), [up j, dn i, up i]), ([dn i], .cross true i j, [dn i, up i]),
        ([dn i, up j], .cap (dn i), [up i])])
    [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [dn i, up j] []
    (dg_zigL' RD k lam (up i))
  -- 5. slide the cup of `crossl` below the dots of the bubble
  dstep [([up j], .cup (dn i), [])]
    [([dn i], .cross true i j, [dn i, up i]), ([dn i, up j], .cap (dn i), [up i]),
      ([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [] []
    (dg_swap_rep RD k lam [] [up j, dn i] [] (.cup (dn i)) (.dot (up i)) rfl m)
  -- 6. and below the cup of the bubble
  dstep [] (List.replicate m ([dn i, up i, up j, dn i], .dot (up i), []) ++
      [([dn i], .cross true i j, [dn i, up i]), ([dn i, up j], .cap (dn i), [up i]),
        ([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) [] []
    (dg_swap' RD k lam [] [up j] [] (.cup (dn i)) (.cup (dn i))).symm
  -- 7. slide the crossing of `crossl` below the dots
  dstep [([], .cup (dn i), [up j]), ([dn i, up i, up j], .cup (dn i), [])]
    [([dn i, up j], .cap (dn i), [up i]), ([dn i], .cross true j i, []),
      ([], .cap (up i), [up j])] [] []
    (dg_swap_rep RD k lam [dn i] [dn i] [] (.cross true i j) (.dot (up i)) rfl m)
  -- 8. and below the cup of the bubble
  dstep [([], .cup (dn i), [up j])]
    (List.replicate m ([dn i, up j, up i, dn i], .dot (up i), []) ++
      [([dn i, up j], .cap (dn i), [up i]), ([dn i], .cross true j i, []),
        ([], .cap (up i), [up j])]) [] []
    (dg_swap' RD k lam [dn i] [] [] (.cross true i j) (.cup (dn i))).symm
  -- 9. slide the cap of `crossl` below the dots
  dstep [([], .cup (dn i), [up j]), ([dn i], .cross true i j, []),
      ([dn i, up j, up i], .cup (dn i), [])]
    [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [] []
    (dg_swap_rep RD k lam [dn i, up j] [] [] (.cap (dn i)) (.dot (up i)) rfl m)
  -- 10. zigzag
  dstep [([], .cup (dn i), [up j]), ([dn i], .cross true i j, [])]
    (List.replicate m ([dn i, up j], .dot (up i), []) ++
      [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) [dn i, up j] []
    (dg_zigR' RD k lam (dn i))
  lnf

set_option maxHeartbeats 1000000 in
/-- **Bubble slide, counterclockwise, `i ≠ j`** (KL III Proposition 3.3, first display, cases
`i · j = -1` and `i · j = 0`, for an arbitrary Cartan datum): a counterclockwise `i`-bubble with
`m` dots to the right of an upward `j`-strand (outer region `λ`) equals, with `Q_ij` the KL II
polynomial, the bubble with `m + d_ij` dots to the left of the strand plus the bubble with `m`
dots to the left and `d_ji` dots on the strand (if `i · j ≠ 0`), resp. the bubble with `m` dots
to the left of the strand (if `i · j = 0`).

Proof (KL III, proof of Proposition 3.3): insert `1 = crossr ∘ crossl` (`eq_downup_ij-gen`)
between the strand and the bubble, pull the strand through the bubble by the interchange law and
two zigzag relations, and evaluate the resulting double crossing of upward strands with the dot
slide and `eq_r2_ij-gen`. -/
theorem dg_ccw_slide_ne (lam : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k lam [up j] [up j]
        ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
          [([up j], .cap (up i), [])]) =
      if C.dot i j = 0 then
        dg RD k lam [up j] [up j]
          ([([], .cup (dn i), [up j])] ++ List.replicate m ([dn i], .dot (up i), [up j]) ++
            [([], .cap (up i), [up j])])
      else
        dg RD k lam [up j] [up j]
          ([([], .cup (dn i), [up j])] ++
            List.replicate (m + C.dij i j) ([dn i], .dot (up i), [up j]) ++
            [([], .cap (up i), [up j])]) +
        dg RD k lam [up j] [up j]
          ([([], .cup (dn i), [up j])] ++ List.replicate m ([dn i], .dot (up i), [up j]) ++
            [([], .cap (up i), [up j])] ++ List.replicate (C.dij j i) ([], .dot (up j), [])) := by
  -- 1. insert `1 = crossr ∘ crossl` (eq_downup_ij-gen) between the strand and the bubble
  dstep ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []))
    [([up j], .cap (up i), [])] [] [up i]
    (dg_downupEF RD k j i h.symm (wt RD lam [up i])).symm
  rw [dg_pull_ccw]
  -- 11. the upward double crossing with dots
  refine (dg_stepL RD k lam [([], .cup (dn i), [up j])] [([], .cap (up i), [up j])] [dn i] []
    (dg_cross_dots_cross RD k lam i j h m) (by schain) (by schain) (by simp [whL])).trans ?_
  split_ifs
  · rw [ctxL_dg_nil RD k lam (by schain) (by schain)]
    simp [whL]
  · rw [map_add, ctxL_dg_nil RD k lam (by schain) (by schain),
      ctxL_dg_nil RD k lam (by schain) (by schain)]
    congr 1
    · simp [whL]
    -- 12. move the dots on the `j` strand above the cap of the bubble
    dstep ([([], .cup (dn i), [up j])] ++ List.replicate m ([dn i], .dot (up i), [up j])) [] [] []
      (dg_swap_rep RD k lam [] [] [] (.cap (up i)) (.dot (up j)) rfl (C.dij j i))
    simp [whL]

set_option maxHeartbeats 1000000 in
/-- **Pulling a strand through a clockwise bubble.** After inserting `crossl ∘ crossr` between
a clockwise `i`-bubble (dots on its upward strand) and an upward `j`-strand on its right, the
interchange law and two zigzag relations turn the diagram into the right closure of
`ψ_{ij} x^m ψ_{ji}`. Valid for all `i, j`. -/
theorem dg_pull_cw (lam : X) (i j : I) (m : ℕ) :
    dg RD k lam [up j] [up j]
        ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
          (crossrL j i ++ crosslL j i).map (whL [up i] []) ++ [([], .cap (dn i), [up j])]) =
      dg RD k lam [up j] [up j]
        ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
          List.replicate m ([], .dot (up i), [up j, dn i]) ++
          [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) := by
  simp only [crosslL, crossrL]
  -- 2., 3. interchange: move the bubble's cap below the crossing of `crossl`
  dstep ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
      [([up i, dn i, up j], .cup (up i), []), ([up i, dn i], .cross true j i, [dn i]),
        ([up i], .cap (up i), [up j, dn i]), ([up i], .cup (dn i), [up j, dn i]),
        ([up i, dn i], .cross true i j, [dn i])]) [] [] []
    (dg_swap' RD k lam [] [up j] [] (.cap (dn i)) (.cap (dn i))).symm
  dstep ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
      [([up i, dn i, up j], .cup (up i), []), ([up i, dn i], .cross true j i, [dn i]),
        ([up i], .cap (up i), [up j, dn i]), ([up i], .cup (dn i), [up j, dn i])])
    [([up j], .cap (dn i), [])] [] []
    (dg_swap' RD k lam [] [] [dn i] (.cap (dn i)) (.cross true i j)).symm
  -- 4. zigzag
  dstep ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
      [([up i, dn i, up j], .cup (up i), []), ([up i, dn i], .cross true j i, [dn i]),
        ([up i], .cap (up i), [up j, dn i])])
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] [up j, dn i]
    (dg_zigR' RD k (wt RD lam [up j, dn i]) (dn i))
  -- 5. slide the cup of `crossr` below the dots of the bubble
  dstep [([], .cup (up i), [up j])]
    [([up i, dn i], .cross true j i, [dn i]), ([up i], .cap (up i), [up j, dn i]),
      ([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] []
    (dg_swap_rep' RD k lam [] [dn i, up j] [] (.cup (up i)) (.dot (up i)) rfl m)
  -- 6. and below the cup of the bubble
  dstep [] (List.replicate m ([], .dot (up i), [dn i, up j, up i, dn i]) ++
      [([up i, dn i], .cross true j i, [dn i]), ([up i], .cap (up i), [up j, dn i]),
        ([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) [] []
    (dg_swap' RD k lam [] [up j] [] (.cup (up i)) (.cup (up i)))
  -- 7. slide the crossing of `crossr` below the dots
  dstep [([up j], .cup (up i), []), ([], .cup (up i), [up j, up i, dn i])]
    [([up i], .cap (up i), [up j, dn i]), ([], .cross true i j, [dn i]),
      ([up j], .cap (dn i), [])] [] []
    (dg_swap_rep' RD k lam [] [dn i] [dn i] (.cross true j i) (.dot (up i)) rfl m)
  -- 8. and below the cup of the bubble
  dstep [([up j], .cup (up i), [])]
    (List.replicate m ([], .dot (up i), [dn i, up i, up j, dn i]) ++
      [([up i], .cap (up i), [up j, dn i]), ([], .cross true i j, [dn i]),
        ([up j], .cap (dn i), [])]) [] []
    (dg_swap' RD k lam [] [] [dn i] (.cup (up i)) (.cross true j i))
  -- 9. slide the cap of `crossr` below the dots
  dstep [([up j], .cup (up i), []), ([], .cross true j i, [dn i]),
      ([], .cup (up i), [up i, up j, dn i])]
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] []
    (dg_swap_rep' RD k lam [] [] [up j, dn i] (.cap (up i)) (.dot (up i)) rfl m)
  -- 10. zigzag
  dstep [([up j], .cup (up i), []), ([], .cross true j i, [dn i])]
    (List.replicate m ([], .dot (up i), [up j, dn i]) ++
      [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) [] [up j, dn i]
    (dg_zigL' RD k (wt RD lam [up j, dn i]) (up i))
  lnf

set_option maxHeartbeats 1000000 in
/-- **Bubble slide, clockwise, `i ≠ j`**, with the dots on the upward strand of the bubble: a
clockwise `i`-bubble with `m` dots to the left of an upward `j`-strand (outer region `λ` to the
right of the strand) equals the bubble with `m + d_ij` dots to the right of the strand plus the
bubble with `m` dots to the right and `d_ji` dots on the strand (if `i · j ≠ 0`), resp. the
bubble with `m` dots to the right of the strand (if `i · j = 0`). -/
theorem dg_cw_slide_ne_up (lam : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k lam [up j] [up j]
        ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
          [([], .cap (dn i), [up j])]) =
      if C.dot i j = 0 then
        dg RD k lam [up j] [up j]
          ([([up j], .cup (up i), [])] ++ List.replicate m ([up j], .dot (up i), [dn i]) ++
            [([up j], .cap (dn i), [])])
      else
        dg RD k lam [up j] [up j]
          ([([up j], .cup (up i), [])] ++
            List.replicate (m + C.dij i j) ([up j], .dot (up i), [dn i]) ++
            [([up j], .cap (dn i), [])]) +
        dg RD k lam [up j] [up j]
          ([([up j], .cup (up i), [])] ++ List.replicate m ([up j], .dot (up i), [dn i]) ++
            [([up j], .cap (dn i), [])] ++ List.replicate (C.dij j i) ([], .dot (up j), [])) := by
  -- 1. insert `1 = crossl ∘ crossr` (eq_downup_ij-gen) between the bubble and the strand
  dstep ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]))
    [([], .cap (dn i), [up j])] [up i] []
    (dg_downupFE RD k i j h lam).symm
  rw [dg_pull_cw]
  -- 11. the upward double crossing with dots
  refine (dg_stepL RD k lam [([up j], .cup (up i), [])] [([up j], .cap (dn i), [])] [] [dn i]
    (dg_cross_dots_cross' RD k (wt RD lam [dn i]) i j h m) (by schain) (by schain)
    (by simp [whL])).trans ?_
  split_ifs
  · rw [ctxL_dg RD k lam (by schain) (by schain)]
    simp [whL]
  · rw [map_add, ctxL_dg RD k lam (by schain) (by schain),
      ctxL_dg RD k lam (by schain) (by schain)]
    congr 1
    · simp [whL]
    -- 12. move the dots on the `j` strand above the cap of the bubble
    dstep ([([up j], .cup (up i), [])] ++ List.replicate m ([up j], .dot (up i), [dn i])) [] [] []
      (dg_swap_rep' RD k lam [] [] [] (.cap (dn i)) (.dot (up j)) rfl (C.dij j i))
    simp [whL]

/-- **Bubble slide, clockwise, `i ≠ j`**, in the normal form of `cwReal` (dots on the downward
strand of the bubble). -/
theorem dg_cw_slide_ne (lam : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k lam [up j] [up j]
        ([([], .cup (up i), [up j])] ++ List.replicate m ([up i], .dot (dn i), [up j]) ++
          [([], .cap (dn i), [up j])]) =
      if C.dot i j = 0 then
        dg RD k lam [up j] [up j]
          ([([up j], .cup (up i), [])] ++ List.replicate m ([up j, up i], .dot (dn i), []) ++
            [([up j], .cap (dn i), [])])
      else
        dg RD k lam [up j] [up j]
          ([([up j], .cup (up i), [])] ++
            List.replicate (m + C.dij i j) ([up j, up i], .dot (dn i), []) ++
            [([up j], .cap (dn i), [])]) +
        dg RD k lam [up j] [up j]
          ([([up j], .cup (up i), [])] ++ List.replicate m ([up j, up i], .dot (dn i), []) ++
            [([up j], .cap (dn i), [])] ++ List.replicate (C.dij j i) ([], .dot (up j), [])) := by
  dstep [] [] [] [up j] (dg_cw_dots RD k (wt RD lam [up j]) i m)
  refine ((congrArg _ (by simp [whL])).trans (dg_cw_slide_ne_up RD k lam i j h m)).trans ?_
  split_ifs
  · dstep [] [] [up j] [] (dg_cw_dots RD k lam i m).symm
    simp [whL]
  · congr 1
    · dstep [] [] [up j] [] (dg_cw_dots RD k lam i (m + C.dij i j)).symm
      simp [whL]
    · dstep [] (List.replicate (C.dij j i) ([], .dot (up j), [])) [up j] []
        (dg_cw_dots RD k lam i m).symm
      simp [whL]

/-! ## Proposition 3.3 for `i ≠ j`, real bubbles -/



theorem lin_bubR_ccwReal (lam : X) (l : Letter I) (i : I) (m : ℕ) :
    (pres RD k).lin (bubR RD k lam [l] (LinDiagram.of (ccwReal RD lam i m))) =
      dg RD k lam [l] [l] ([([l], .cup (dn i), [])] ++ List.replicate m ([l, dn i], .dot (up i), []) ++
        [([l], .cap (up i), [])]) := by
  rw [lin_bubR, ccwReal, lin_of_mkD, plcL_dg_nil]
  show dg RD k lam [l] [l] _ = _
  congr 1; lnf

theorem lin_bubL_ccwReal (μ : X) (l : Letter I) (i : I) (m : ℕ) :
    (pres RD k).lin (bubL RD k μ [l] (LinDiagram.of (ccwReal RD (wt RD μ [l]) i m))) =
      dg RD k μ [l] [l] ([([], .cup (dn i), [l])] ++ List.replicate m ([dn i], .dot (up i), [l]) ++
        [([], .cap (up i), [l])]) := by
  rw [lin_bubL, ccwReal, lin_of_mkD, plcL_dg]
  show dg RD k μ [l] [l] _ = _
  congr 1; lnf

theorem lin_bubR_cwReal (lam : X) (l : Letter I) (i : I) (m : ℕ) :
    (pres RD k).lin (bubR RD k lam [l] (LinDiagram.of (cwReal RD lam i m))) =
      dg RD k lam [l] [l] ([([l], .cup (up i), [])] ++ List.replicate m ([l, up i], .dot (dn i), []) ++
        [([l], .cap (dn i), [])]) := by
  rw [lin_bubR, cwReal, lin_of_mkD, plcL_dg_nil]
  show dg RD k lam [l] [l] _ = _
  congr 1; lnf

theorem lin_bubL_cwReal (μ : X) (l : Letter I) (i : I) (m : ℕ) :
    (pres RD k).lin (bubL RD k μ [l] (LinDiagram.of (cwReal RD (wt RD μ [l]) i m))) =
      dg RD k μ [l] [l] ([([], .cup (up i), [l])] ++ List.replicate m ([up i], .dot (dn i), [l]) ++
        [([], .cap (dn i), [l])]) := by
  rw [lin_bubL, cwReal, lin_of_mkD, plcL_dg]
  show dg RD k μ [l] [l] _ = _
  congr 1; lnf

/-- **KL III Proposition 3.3 (first display), `i ≠ j`, real bubbles.** For `i ≠ j`, a
counterclockwise `i`-bubble with `m ≥ 0` dots to the right of an upward `j`-strand, in the
region `λ`, slides to the left of the strand (region `λ + j_X`):
`ccw_m ⊗ 1 = 1 ⊗ ccw_{m + d_ij} + (1 ⊗ ccw_m) x_j^{d_ji}` if `i · j ≠ 0`, and
`ccw_m ⊗ 1 = 1 ⊗ ccw_m` if `i · j = 0`. For `i · j = -1` (`d_ij = d_ji = 1`) this is the printed
case `i · j = -1` (with label `-⟨i,λ⟩-1+α = m`, since `⟨i, λ+j_X⟩ = ⟨i,λ⟩ - 1`). -/
theorem bubble_slide_ccw_ne (lam : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    (pres RD k).lin (bubR RD k lam [up j] (LinDiagram.of (ccwReal RD lam i m))) =
      if C.dot i j = 0 then
        (pres RD k).lin (bubL RD k lam [up j] (LinDiagram.of (ccwReal RD (wt RD lam [up j]) i m)))
      else
        (pres RD k).lin (bubL RD k lam [up j]
            (LinDiagram.of (ccwReal RD (wt RD lam [up j]) i (m + C.dij i j)))) +
          (pres RD k).lin (bubL RD k lam [up j]
            (LinDiagram.of (ccwReal RD (wt RD lam [up j]) i m))) ≫
            dotsU RD k lam (up j) (C.dij j i) := by
  simp only [lin_bubR_ccwReal, lin_bubL_ccwReal, dotsU]
  rw [dg_comp (by schain) (by schain)]
  exact dg_ccw_slide_ne RD k lam i j h m

/-- **KL III Proposition 3.3 (second display), `i ≠ j`, real bubbles.** For `i ≠ j`, a
clockwise `i`-bubble with `m ≥ 0` dots to the left of an upward `j`-strand (region `λ + j_X`)
slides to the right of the strand (region `λ`):
`1 ⊗ cw_m = cw_{m + d_ij} ⊗ 1 + (cw_m ⊗ 1) x_j^{d_ji}` if `i · j ≠ 0`, and
`1 ⊗ cw_m = cw_m ⊗ 1` if `i · j = 0`. -/
theorem bubble_slide_cw_ne (lam : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    (pres RD k).lin (bubL RD k lam [up j] (LinDiagram.of (cwReal RD (wt RD lam [up j]) i m))) =
      if C.dot i j = 0 then
        (pres RD k).lin (bubR RD k lam [up j] (LinDiagram.of (cwReal RD lam i m)))
      else
        (pres RD k).lin (bubR RD k lam [up j] (LinDiagram.of (cwReal RD lam i (m + C.dij i j)))) +
          (pres RD k).lin (bubR RD k lam [up j] (LinDiagram.of (cwReal RD lam i m))) ≫
            dotsU RD k lam (up j) (C.dij j i) := by
  simp only [lin_bubL_cwReal, lin_bubR_cwReal, dotsU]
  rw [dg_comp (by schain) (by schain)]
  exact dg_cw_slide_ne RD k lam i j h m

end Categorification.KL3.Diagram
