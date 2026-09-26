/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Rewriting
import Categorification.Diagrams.KL3.BubbleSlides

/-!
# Pitchfork moves and dots on cups in `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1 (biadjointness (3.1), (3.2), cyclicity of dots (3.3), and the definition of the
sideways crossings `eq_crossl-gen`, `eq_crossr-gen`).

The sideways crossings `crossl RD i j` and `crossr RD i j` are defined as rotations of upward
crossings by a cup and a cap. Consequently an upward strand may be pulled through a cup or a cap
whose legs it crosses, turning an upward crossing into a sideways crossing or back, by the
interchange law and one zigzag relation only (no cyclicity relation is needed); these are the
*pitchfork* moves used in the proof of KL III Proposition 3.5:

* `dg_pf_cupUp` (cup `1 ⟶ E_j F_j`): cup to the left of `E_i`, then `crossr_{ij}` =
  cup to the right of `E_i`, then `ψ_{ij}`;
* `dg_pf_capUp` (cap `F_j E_j ⟶ 1`): `crossr_{ij}`, then the cap on the right =
  `ψ_{ij}`, then the cap on the left;
* `dg_pf_capDn` (cap `E_j F_j ⟶ 1`): `crossl_{ij}`, then the cap on the left =
  `ψ_{ji}`, then the cap on the right;
* `dg_pf_cupDn` (cup `1 ⟶ F_j E_j`): cup to the right of `E_i`, then `crossl_{ij}` =
  cup to the left of `E_i`, then `ψ_{ji}`.

The cyclicity relations `eq_cyclic_cross-gen` in normal form are `dg_cycCrossR`, `dg_cycCrossL`;
with them a downward strand can be pulled through a cup, turning a downward crossing into a
sideways crossing (`dg_pf_cupUp_down`).

Dots move around cups (KL III (3.3) and a zigzag relation): `dg_dot_cupUp`, `dg_dots_cupUp`
(the cup `1 ⟶ E_i F_i`) and `dg_dot_cupDn`, `dg_dots_cupDn` (the cup `1 ⟶ F_i E_i`); for caps
see `dg_dots_cap_dn` and `dg_dots_cap_up`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Pitchfork moves -/

/-- **Pitchfork through the cup `1 ⟶ E_j F_j`**: the cup to the left of `E_i` followed by
`crossr_{ij}` (the strand `E_i` crossing the leg `F_j`) equals the cup to the right of `E_i`
followed by the upward crossing `ψ_{ij}` (the strand `E_i` crossing the leg `E_j`). -/
theorem dg_pf_cupUp (i j : I) (μ : X) :
    dg RD k μ [up i] [up j, up i, dn j]
        ([([], .cup (up j), [up i])] ++ (crossrL i j).map (whL [up j] [])) =
      dg RD k μ [up i] [up j, up i, dn j]
        [([up i], .cup (up j), []), ([], .cross true i j, [dn j])] := by
  dnorm
  dswap 0; dswap 1
  dat 2 [] [up i, dn j] (dg_zigL' RD k _ (up j))

/-- **Pitchfork through the cap `F_j E_j ⟶ 1`**: `crossr_{ij}` on the left two strands of
`F_j E_i E_j`, followed by the cap on the right two strands, equals the upward crossing `ψ_{ij}`
on the right two strands followed by the cap on the left two strands. -/
theorem dg_pf_capUp (i j : I) (μ : X) :
    dg RD k μ [dn j, up i, up j] [up i]
        ((crossrL i j).map (whL [] [up j]) ++ [([up i], .cap (up j), [])]) =
      dg RD k μ [dn j, up i, up j] [up i]
        [([dn j], .cross true i j, []), ([], .cap (up j), [up i])] := by
  dnorm
  dswap 2; dswap 1
  dat 0 [dn j, up i] [] (dg_zigL' RD k _ (up j))

/-- **Pitchfork through the cap `E_j F_j ⟶ 1`**: `crossl_{ij}` on the right two strands of
`E_j E_i F_j`, followed by the cap on the left two strands, equals the upward crossing `ψ_{ji}`
on the left two strands followed by the cap on the right two strands. -/
theorem dg_pf_capDn (i j : I) (μ : X) :
    dg RD k μ [up j, up i, dn j] [up i]
        ((crosslL i j).map (whL [up j] []) ++ [([], .cap (dn j), [up i])]) =
      dg RD k μ [up j, up i, dn j] [up i]
        [([], .cross true j i, [dn j]), ([up i], .cap (dn j), [])] := by
  dnorm
  dswap 2; dswap 1
  dat 0 [] [up i, dn j] (dg_zigR' RD k _ (dn j))

/-- **Pitchfork through the cup `1 ⟶ F_j E_j`**: the cup to the right of `E_i` followed by
`crossl_{ij}` (the strand `E_i` crossing the leg `F_j`) equals the cup to the left of `E_i`
followed by the upward crossing `ψ_{ji}` (the leg `E_j` crossing the strand `E_i`). -/
theorem dg_pf_cupDn (i j : I) (μ : X) :
    dg RD k μ [up i] [dn j, up i, up j]
        ([([up i], .cup (dn j), [])] ++ (crosslL i j).map (whL [] [up j])) =
      dg RD k μ [up i] [dn j, up i, up j]
        [([], .cup (dn j), [up i]), ([dn j], .cross true j i, [])] := by
  dnorm
  dswap 0; dswap 1
  dat 2 [dn j, up i] [] (dg_zigR' RD k _ (dn j))

/-! ## Dots on cups -/

/-- A downward dot on the right leg of the cup `1 ⟶ E_i F_i` equals an upward dot on its left
leg (KL III (3.3) and a zigzag relation). -/
theorem dg_dot_cupUp (i : I) (μ : X) :
    dg RD k μ [] [up i, dn i] [([], .cup (up i), []), ([up i], .dot (dn i), [])] =
      dg RD k μ [] [up i, dn i] [([], .cup (up i), []), ([], .dot (up i), [dn i])] := by
  dat 1 [up i] [] (dg_cycDotR RD k i _)
  dswap 0; dswap 1
  dat 2 [] [dn i] (dg_zigL' RD k _ (up i))

/-- An upward dot on the right leg of the cup `1 ⟶ F_i E_i` equals a downward dot on its left
leg (KL III (3.3) and a zigzag relation). -/
theorem dg_dot_cupDn (i : I) (μ : X) :
    dg RD k μ [] [dn i, up i] [([], .cup (dn i), []), ([dn i], .dot (up i), [])] =
      dg RD k μ [] [dn i, up i] [([], .cup (dn i), []), ([], .dot (dn i), [up i])] := by
  symm
  dat 1 [] [up i] (dg_cycDotL RD k i _)
  dswap 0; dswap 1
  dat 2 [dn i] [] (dg_zigR' RD k _ (dn i))

/-- `m` downward dots on the right leg of the cup `1 ⟶ E_i F_i` equal `m` upward dots on its
left leg. -/
theorem dg_dots_cupUp (i : I) (μ : X) (m : ℕ) :
    dg RD k μ [] [up i, dn i]
        ([([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), [])) =
      dg RD k μ [] [up i, dn i]
        ([([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i])) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.replicate_succ']
    dstep [] (List.replicate m ([up i], .dot (dn i), [])) [] [] (dg_dot_cupUp RD k i μ)
    dstep [([], .cup (up i), [])] [] [] []
      (dg_swap_dots RD k μ [] [] [] (up i) (dn i) m 1).symm
    lnf
    dstep [] [([], .dot (up i), [dn i])] [] [] ih
    lnf

/-- `m` upward dots on the right leg of the cup `1 ⟶ F_i E_i` equal `m` downward dots on its
left leg. -/
theorem dg_dots_cupDn (i : I) (μ : X) (m : ℕ) :
    dg RD k μ [] [dn i, up i]
        ([([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), [])) =
      dg RD k μ [] [dn i, up i]
        ([([], .cup (dn i), [])] ++ List.replicate m ([], .dot (dn i), [up i])) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.replicate_succ']
    dstep [] (List.replicate m ([dn i], .dot (up i), [])) [] [] (dg_dot_cupDn RD k i μ)
    dstep [([], .cup (dn i), [])] [] [] []
      (dg_swap_dots RD k μ [] [] [] (dn i) (up i) m 1).symm
    lnf
    dstep [] [([], .dot (dn i), [up i])] [] [] ih
    lnf

/-! ## The cyclicity of crossings and a pitchfork move for a downward strand -/

/-- **KL III `eq_cyclic_cross-gen`**, first equality, in normal form: the downward crossing
`F_j F_i 1_μ ⟶ F_i F_j 1_μ` is the upward crossing rotated by nested cups on the right and
nested caps on the left (`rotCrossR`). -/
theorem dg_cycCrossR (j i : I) (μ : X) :
    dg RD k μ [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])] =
      dg RD k μ [dn j, dn i] [dn i, dn j]
        [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
          ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
          ([], .cap (up j), [dn i, dn j])] := by
  rw [dg_of (by schain), dg_of (by schain)]
  exact ((pres RD k).diag_eq_of_rel (.inr (.cycCrossR j i μ)) rfl).symm

/-- **KL III `eq_cyclic_cross-gen`**, second equality, in normal form: the downward crossing is
the upward crossing rotated by nested cups on the left and nested caps on the right
(`rotCrossL`). -/
theorem dg_cycCrossL (j i : I) (μ : X) :
    dg RD k μ [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])] =
      dg RD k μ [dn j, dn i] [dn i, dn j]
        [([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
          ([dn i, dn j], .cross true j i, [dn j, dn i]), ([dn i, dn j, up i], .cap (dn j), [dn i]),
          ([dn i, dn j], .cap (dn i), [])] := by
  rw [dg_of (by schain), dg_of (by schain)]
  exact ((pres RD k).diag_eq_of_rel (.inr (.cycCrossL j i μ)) rfl).symm

/-- **Pitchfork move for a downward strand** (uses the cyclicity of the crossing): the cup
`1 ⟶ E_j F_j` to the left of `F_i` followed by the downward crossing of its leg `F_j` with `F_i`
equals the cup to the right of `F_i` followed by the sideways crossing `crossr_{ji}` of `F_i`
with its leg `E_j`. -/
theorem dg_pf_cupUp_down (i j : I) (μ : X) :
    dg RD k μ [dn i] [up j, dn i, dn j]
        [([], .cup (up j), [dn i]), ([up j], .cross false j i, [])] =
      dg RD k μ [dn i] [up j, dn i, dn j]
        ([([dn i], .cup (up j), [])] ++ (crossrL j i).map (whL [] [dn j])) := by
  dat 1 [up j] [] (dg_cycCrossR RD k j i _)
  dswap 0; dswap 1; dswap 2; dswap 3
  dat 4 [] [dn i, dn j] (dg_zigL' RD k _ (up j))

end Categorification.KL3.Diagram
