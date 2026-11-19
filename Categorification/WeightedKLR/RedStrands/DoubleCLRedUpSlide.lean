/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedUpNaturality
import Categorification.Diagrams.CL.NoMix
import Categorification.Diagrams.CL.DownKLR

/-!
# The red/upward slide relations after the cover functor

Webster, arXiv:1309.3796v3, §4.5, Definition 4.24, relations (4.4c), (4.4d), and §4.6, proof
of Lemma 4.29. A black dot or crossing on upward strands slides through a red strand. After
reflection the black strands point downward and the red strand passes through them by sideways
crossings, written as mates of upward crossings. The slide then follows from the dot cyclicity
and `Q`-cyclicity of `U_Q(g)`, the zigzag identities and the KLR relations on upward strands.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (S : CLScalars C k)

/-- Dot cyclicity in `U_Q(g)`, rotation with the cup on the right. -/
theorem dgCL_cycDotR (i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dgC (presCL RD k S) μ [dn i] [dn i]
        [([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]), ([], .cap (up i), [dn i])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  exact ((presCL RD k S).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl).symm

/-- A downward dot on the left strand of the cap `F_i E_i ⟶ 1` equals an upward dot on its
right strand. -/
theorem dgCL_dot_cap_up (ν : X) (i : I) :
    dgC (presCL RD k S) ν [dn i, up i] [] [([], .dot (dn i), [up i]), ([], .cap (up i), [])] =
      dgC (presCL RD k S) ν [dn i, up i] [] [([dn i], .dot (up i), []), ([], .cap (up i), [])] := by
  datC 0 [] [up i] (dgCL_cycDotR RD k S i _)
  dswapC 2
  dswapC 1
  datC 0 [dn i] [] (dgC_zigL' _ (zigzags RD k S) _ (up i))

/-- A downward dot on the right leg of the cup `1 ⟶ E_i F_i` equals an upward dot on its left
leg. -/
theorem dgCL_dot_cupUp (i : I) (μ : X) :
    dgC (presCL RD k S) μ [] [up i, dn i] [([], .cup (up i), []), ([up i], .dot (dn i), [])] =
      dgC (presCL RD k S) μ [] [up i, dn i] [([], .cup (up i), []), ([], .dot (up i), [dn i])] := by
  datC 1 [up i] [] (dgCL_cycDotR RD k S i _)
  dswapC 0; dswapC 1
  datC 2 [] [dn i] (dgC_zigL' _ (zigzags RD k S) _ (up i))

/-- Dot cyclicity in `U_Q(g)`, rotation with the cup on the left. -/
theorem dgCL_cycDotL (i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dgC (presCL RD k S) μ [dn i] [dn i]
        [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  exact ((presCL RD k S).diag_eq_of_rel (.inr (.cycDotL i μ)) rfl).symm

/-- A downward dot on the right strand of the cap `E_i F_i ⟶ 1` equals an upward dot on its
left strand. -/
theorem dgCL_dot_cap_dn (ν : X) (i : I) :
    dgC (presCL RD k S) ν [up i, dn i] [] [([up i], .dot (dn i), []), ([], .cap (dn i), [])] =
      dgC (presCL RD k S) ν [up i, dn i] [] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] := by
  datC 0 [up i] [] (dgCL_cycDotL RD k S i _)
  dswapC 2
  dswapC 1
  datC 0 [] [dn i] (dgC_zigR' _ (zigzags RD k S) _ (dn i))

/-- An upward dot on the right leg of the cup `1 ⟶ F_i E_i` equals a downward dot on its left
leg. -/
theorem dgCL_dot_cupDn (i : I) (μ : X) :
    dgC (presCL RD k S) μ [] [dn i, up i] [([], .cup (dn i), []), ([dn i], .dot (up i), [])] =
      dgC (presCL RD k S) μ [] [dn i, up i] [([], .cup (dn i), []), ([], .dot (dn i), [up i])] := by
  symm
  datC 1 [] [up i] (dgCL_cycDotL RD k S i _)
  dswapC 0; dswapC 1
  datC 2 [dn i] [] (dgC_zigR' _ (zigzags RD k S) _ (dn i))

/-- The downward crossing is `t_{ij}⁻¹` times the upward crossing rotated by nested cups on the
right and caps on the left (`presCL_rotCrossR`). -/
theorem dgCL_downCross (j i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])] =
      (((S.t i j)⁻¹ : kˣ) : k) • dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j]
        [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
          ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
          ([], .cap (up j), [dn i, dn j])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  change _ = _ • (presCL RD k S).diag (rotCrossR RD j i μ)
  rw [presCL_rotCrossR, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rfl

variable {Q : I → I → MvPolynomial (Fin 2) k} (hK : KLRHolds (presCL RD k S) Q)
include hK

/-- A downward dot passes through the sideways crossing `F_j E_c ⟶ E_c F_j` for `c ≠ j`. -/
theorem dgCL_dot_crossrL (μ : X) (c j : I) (h : c ≠ j) :
    dgC (presCL RD k S) μ [dn j, up c] [up c, dn j] (([], .dot (dn j), [up c]) :: crossrL c j) =
      dgC (presCL RD k S) μ [dn j, up c] [up c, dn j]
        (crossrL c j ++ [([up c], .dot (dn j), [])]) := by
  simp only [crossrL, List.cons_append, List.nil_append]
  dswapC 0; dswapC 1
  datC 2 [] [up c, dn j] (dgCL_dot_cap_up RD k S _ j)
  datC 1 [dn j] [dn j] (dgC_slideLNe (hK := hK) _ c j h)
  datC 0 [dn j, up c] [] (dgCL_dot_cupUp RD k S j _).symm
  dswapC 1
  dswapC 2

/-- A downward dot passes through the sideways crossing `E_c F_j ⟶ F_j E_c` for `c ≠ j`. -/
theorem dgCL_dot_crosslL (μ : X) (c j : I) (h : c ≠ j) :
    dgC (presCL RD k S) μ [up c, dn j] [dn j, up c] (([up c], .dot (dn j), []) :: crosslL c j) =
      dgC (presCL RD k S) μ [up c, dn j] [dn j, up c]
        (crosslL c j ++ [([], .dot (dn j), [up c])]) := by
  simp only [crosslL, List.cons_append, List.nil_append]
  dswapC 0; dswapC 1
  datC 2 [dn j, up c] [] (dgCL_dot_cap_dn RD k S _ j)
  datC 1 [dn j] [dn j] (dgC_slideRNe (hK := hK) _ j c h.symm).symm
  datC 0 [] [up c, dn j] (dgCL_dot_cupDn RD k S j _)
  dswapC 1
  dswapC 2

/-- An upward strand of colour `c` passes a downward crossing of colours `j`, `i` (`c ≠ i`)
by the sideways crossings `crossrL`. -/
theorem dgCL_downCross_crossrL (μ : X) (c j i : I) (hi : c ≠ i) :
    dgC (presCL RD k S) μ [dn j, dn i, up c] [up c, dn i, dn j]
      ([([], .cross false j i, [up c])] ++ (crossrL c j).map (whL [dn i] []) ++
        (crossrL c i).map (whL [] [dn j])) =
    dgC (presCL RD k S) μ [dn j, dn i, up c] [up c, dn i, dn j]
      ((crossrL c i).map (whL [dn j] []) ++ (crossrL c j).map (whL [] [dn i]) ++
        [([up c], .cross false j i, [])]) := by
  rw [dgC_stepL_at _ 0 [] [up c] (dgCL_downCross RD k S j i _) (by schain) (by schain) rfl,
    map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  conv_rhs => rw [dgC_stepL_at _ 6 [up c] [] (dgCL_downCross RD k S j i _) (by schain)
    (by schain) rfl, map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  congr 1
  dswapC 4; dswapC 3; dswapC 2; dswapC 1; dswapC 0
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  dswapC 6; dswapC 5; dswapC 4; dswapC 3
  datC 2 [dn j, dn i] [up c, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up j))
  dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 6; dswapC 5; dswapC 4; dswapC 3
  dswapC 7; dswapC 6; dswapC 5
  datC 4 [dn j, dn i, up j] [up c, dn i, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up i))
  dswapC 1
  datC 2 [dn j, dn i] [dn i, dn j] (dgC_braid (hK := hK) _ c j i (fun h => hi h.1))
  symm
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1; dswapC 0
  dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  dswapC 7; dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 8; dswapC 7; dswapC 6; dswapC 5; dswapC 4
  datC 3 [dn j, dn i, up c] [up j, dn i, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up i))
  dswapC 7; dswapC 6
  datC 5 [dn j, up c] [dn i, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up j))
  dswapC 4

end Categorification.KL3.Diagram.CL
