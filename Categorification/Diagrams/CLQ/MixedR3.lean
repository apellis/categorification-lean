/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Rewriting
import Categorification.Diagrams.KL3.MixedR3

/-!
# Reidemeister 3 moves with one downward strand in `U_Q(g)` (KL III Proposition 3.5, (3.22))

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.5, equation (3.22), for the Cautis–Lauda scalars (S. Cautis, A. D. Lauda,
arXiv:1111.1431v3, Definition 1.1, with `r = 1`).

The diagrams `r3mixL`, `r3mixR` are those of `Categorification.Diagrams.KL3.MixedR3`. The outer
moves `dg_r3outR`, `dg_r3outL` are rotations of the braid relation and are proved exactly as
for KL III. For distinct labels the sideways crossings are inverse to each other only up to the
unit `t_{ji}` (CL `sec:mixedrels`, `dg_downupEF`, `dg_downupFE`); in the proof of (3.22) the
sideways crossing inserted above and the one removed below carry the same unit, so (3.22) holds
with coefficient `1`, as in KL III.

## Main results

* `dg_r3outR`, `dg_r3outL`: the outer mixed Reidemeister 3 moves.
* `prop35_a`: **KL III Proposition 3.5, (3.22)** in `U_Q(g)`: unless `i = j = k`,
  `r3mixL i j k' = r3mixR i j k'`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-- **Outer mixed Reidemeister 3 move, downward strand from bottom left to top right**
(`F_j E_i E_k 1_μ ⟶ E_k E_i F_j 1_μ`), the rotation of the braid relation on `E_i E_k E_j`;
it holds unless `i = j ≠ k`. -/
theorem dg_r3outR (i k' j : I) (h : ¬ (i = j ∧ i ≠ k')) (μ : X) :
    NF.dg (pres RD k sc) μ [dn j, up i, up k'] [up k', up i, dn j]
      ([([dn j], .cross true i k', [])] ++ (crossrL k' j).map (whL [] [up i]) ++
        (crossrL i j).map (whL [up k'] [])) =
    NF.dg (pres RD k sc) μ [dn j, up i, up k'] [up k', up i, dn j]
      ((crossrL i j).map (whL [] [up k']) ++ (crossrL k' j).map (whL [up i] []) ++
        [([], .cross true i k', [dn j])]) := by
  dnorm
  dswapQ 3; dswapQ 4; dswapQ 2; dswapQ 3; dswapQ 1; dswapQ 2; dswapQ 5; dswapQ 4
  datQ 3 [dn j, up k'] [up i, dn j] (NF.dg_zigL' (pres RD k sc) _ (up j))
  dswapQ 0
  datQ 1 [dn j] [dn j] (dg_braid RD k sc _ i k' j h)
  symm
  dswapQ 2; dswapQ 3; dswapQ 1; dswapQ 2; dswapQ 0; dswapQ 1; dswapQ 4; dswapQ 3
  datQ 2 [dn j, up i] [up k', dn j] (NF.dg_zigL' (pres RD k sc) _ (up j))
  dswapQ 3

/-- **Outer mixed Reidemeister 3 move, downward strand from bottom right to top left**
(`E_i E_k F_j 1_μ ⟶ F_j E_k E_i 1_μ`), the rotation of the braid relation on `E_j E_i E_k`;
it holds unless `j = k ≠ i`. -/
theorem dg_r3outL (i k' j : I) (h : ¬ (j = k' ∧ j ≠ i)) (μ : X) :
    NF.dg (pres RD k sc) μ [up i, up k', dn j] [dn j, up k', up i]
      ((crosslL k' j).map (whL [up i] []) ++ (crosslL i j).map (whL [] [up k']) ++
        [([dn j], .cross true i k', [])]) =
    NF.dg (pres RD k sc) μ [up i, up k', dn j] [dn j, up k', up i]
      ([([], .cross true i k', [dn j])] ++ (crosslL i j).map (whL [up k'] []) ++
        (crosslL k' j).map (whL [] [up i])) := by
  dnorm
  dswapQ 2; dswapQ 3; dswapQ 1; dswapQ 2; dswapQ 0; dswapQ 1; dswapQ 4; dswapQ 3
  datQ 2 [dn j, up i] [up k', dn j] (NF.dg_zigR' (pres RD k sc) _ (dn j))
  dswapQ 3
  datQ 1 [dn j] [dn j] (dg_braid RD k sc _ j i k' h)
  symm
  dswapQ 3; dswapQ 4; dswapQ 2; dswapQ 3; dswapQ 1; dswapQ 2; dswapQ 0; dswapQ 5; dswapQ 4
  datQ 3 [dn j, up k'] [up i, dn j] (NF.dg_zigR' (pres RD k sc) _ (dn j))

/-- `crossr_{ij} ≫ crossl_{ij} = t_{ji} · 1` on `F_j E_i`, solved for the identity. -/
theorem dg_nil_eq_inv_smul_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    NF.dg (pres RD k sc) μ [dn j, up i] [dn j, up i] [] =
      (((sc.t j i)⁻¹ : kˣ) : k) •
        NF.dg (pres RD k sc) μ [dn j, up i] [dn j, up i] (crossrL i j ++ crosslL i j) := by
  rw [dg_downupFE RD k sc j i h.symm μ, smul_smul, Units.inv_mul, one_smul]

theorem smul_cancel_unit {M : Type*} [AddCommGroup M] [Module k M] (c : kˣ) {x y : M}
    (h : (c : k) • x = (c : k) • y) : x = y := by
  have := congrArg (fun z => ((c⁻¹ : kˣ) : k) • z) h
  simpa only [smul_smul, Units.inv_mul, one_smul] using this

/-- (3.22) when `i ≠ j`. -/
theorem prop35_a_of_ne_left (i j k' : I) (hij : i ≠ j) (μ : X) :
    NF.dg (pres RD k sc) μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixL i j k') =
      NF.dg (pres RD k sc) μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixR i j k') := by
  simp only [r3mixL, r3mixR]
  dnorm
  refine Eq.trans (NF.dg_step_at_smul _ 7 [up k'] [] _
    (dg_nil_eq_inv_smul_downupFE RD k sc i j hij _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm
  refine smul_cancel_unit k (sc.t j i) ?_
  rw [smul_smul, Units.mul_inv, one_smul]
  datQ 3 [] [] (dg_r3outR RD k sc i k' j (fun h => hij h.1) _)
  refine Eq.trans (NF.dg_step_at_smul _ 0 [] [up k'] _ (dg_downupEF RD k sc i j hij _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm

/-- (3.22) when `j ≠ k`. -/
theorem prop35_a_of_ne_right (i j k' : I) (hjk : j ≠ k') (μ : X) :
    NF.dg (pres RD k sc) μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixL i j k') =
      NF.dg (pres RD k sc) μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixR i j k') := by
  simp only [r3mixL, r3mixR]
  dnorm
  refine Eq.trans (NF.dg_step_at_smul _ 0 [up i] [] _
    (dg_nil_eq_inv_smul_downupFE RD k sc k' j hjk.symm _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm
  refine smul_cancel_unit k (sc.t j k') ?_
  rw [smul_smul, Units.mul_inv, one_smul]
  datQ 3 [] [] (dg_r3outL RD k sc i k' j (fun h => hjk h.1) _)
  refine Eq.trans (NF.dg_step_at_smul _ 7 [] [up i] _ (dg_downupEF RD k sc k' j hjk.symm _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm

/-- **KL III Proposition 3.5, equation (3.22)** in `U_Q(g)` (CL scalars, `r = 1`): unless
`i = j = k`, `crossl_{ij} ⊗ 1, 1 ⊗ ψ_{ik}, crossr_{kj} ⊗ 1` equals `1 ⊗ crossr_{kj},
ψ_{ik} ⊗ 1, 1 ⊗ crossl_{ij}` as 2-morphisms `E_i F_j E_k 1_μ ⟶ E_k F_j E_i 1_μ`. -/
theorem prop35_a (i j k' : I) (h : ¬ (i = j ∧ j = k')) (μ : X) :
    NF.dg (pres RD k sc) μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixL i j k') =
      NF.dg (pres RD k sc) μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixR i j k') := by
  by_cases hij : i = j
  · exact prop35_a_of_ne_right RD k sc i j k' (fun hjk => h ⟨hij, hjk⟩) μ
  · exact prop35_a_of_ne_left RD k sc i j k' hij μ

end Categorification.KL3.Diagram.CLQ
