/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackBraidClosure
import Categorification.Diagrams.CLQ.SpanningSetLocal

/-!
# The pure black closures adjoining a red braid, in `U_Q(g)`

Khovanov–Lauda III, arXiv:0807.3250v1, Definition 3.1(iv) and §3.3.2, for the Cautis–Lauda
2-category `U_Q(g)` (`CLQ.pres RD k sc`, arXiv:1111.1431v3, Definition 1.1, `r = 1`). The
closed same-colour downward crossing `blackBraidClosureLayers` vanishes in positive and in
negative coroot weight. The upward closure `upBraidClosureLayers` vanishes by a left curl in
negative weight and by a right curl in positive weight; the symmetry `ω̃` (which exchanges
`U_{sc}` and `U_{sc^θ}`, with `sc^{θθ}` presenting the same 2-category as `sc`) sends it to the downward closure, up to sign.
This is the pure black step of closing the black–red–black relation in Webster,
arXiv:1309.3796v3, Definitions 4.5 and 4.24.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe u v w

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-- The closed same-colour upward crossing between two oppositely oriented cups and caps. -/
def upBraidClosureLayers (i : I) : List (LayerData I) :=
  [([], .cup (up i), []),
    ([], .cup (dn i), [up i, dn i]),
    ([dn i], .cross true i i, [dn i]),
    ([dn i, up i], .cap (dn i), []),
    ([], .cap (up i), [])]

/-- The closed upward crossing vanishes in negative coroot weight: interchanging the caps
exposes a left curl whose bubble sum is empty. -/
theorem dg_upBraidClosure_neg (ν : X) (i : I) (hν : ip RD i ν ≤ -1) :
    NF.dg (pres RD k sc) ν [] [] (upBraidClosureLayers i) = 0 := by
  have hcurlIndex : ip RD i (wt RD (wt RD ν [dn i]) [up i]) = ip RD i ν := by
    simp [ip, wt, sh, sgn]
  unfold upBraidClosureLayers
  dswapQ 3
  have h := dg_curlL RD k sc i (wt RD ν [dn i])
  rw [hcurlIndex, show (ip RD i ν + 1).toNat = 0 by omega, Finset.sum_range_zero] at h
  rw [NF.dg_stepL_at _ 1 [] [dn i] h (by (try dnorm); schain) (by (try dnorm); schain)
    (by dnorm), map_zero]

/-- The closed upward crossing vanishes in positive coroot weight: interchanging the cups
exposes a right curl whose bubble sum is empty. -/
theorem dg_upBraidClosure_pos (ν : X) (i : I) (hν : 1 ≤ ip RD i ν) :
    NF.dg (pres RD k sc) ν [] [] (upBraidClosureLayers i) = 0 := by
  unfold upBraidClosureLayers
  dswapQ 0
  have h := dg_curlR RD k sc i ν
  rw [show (-ip RD i ν + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero] at h
  rw [NF.dg_stepL_at _ 1 [dn i] [] h (by (try dnorm); schain) (by (try dnorm); schain)
    (by dnorm)]
  exact map_zero _


theorem wls_upBraidClosureLayers (i : I) :
    Omega.wls (upBraidClosureLayers i) = blackBraidClosureLayers i := by
  simp [upBraidClosureLayers, blackBraidClosureLayers, Omega.wls, Omega.ld, Omega.shape]

variable [DecidableEq I]

/-- The downward closure is the image of the upward closure under `ω̃`, up to sign. -/
theorem dg_blackBraidClosure_eq_zero_of_up (μ : X) (i : I)
    (h : NF.dg (pres RD k (CLQ.thetaScalars RD sc)) (-μ) [] [] (upBraidClosureLayers i) = 0) :
    NF.dg (pres RD k sc) μ [] [] (blackBraidClosureLayers i) = 0 := by
  have e := congrArg (omegaHom (CLQ.thetaScalars RD sc) (ob_wf RD (-μ) [])) h
  rw [map_zero, omegaHom_dg (-μ) _ (by unfold upBraidClosureLayers; schain),
    CLQ.thetaScalars_thetaScalars_withRone, wls_upBraidClosureLayers] at e
  have hs : Sig.sgnS (upBraidClosureLayers i) = -1 := by
    simp [upBraidClosureLayers, Sig.sgnS, Sig.sgnSh]
  rw [hs, Int.cast_neg, Int.cast_one, neg_smul, one_smul, neg_eq_zero, TRQ_eq_zero] at e
  rwa [List.map_nil, neg_neg] at e

/-- Khovanov–Lauda III, Definition 3.1(iv) and §3.3.2, in `U_Q(g)`: the closed downward
crossing vanishes in positive coroot weight. -/
theorem dg_blackBraidClosure_posQ (μ : X) (i : I) (hμ : 1 ≤ ip RD i μ) :
    NF.dg (pres RD k sc) μ [] [] (blackBraidClosureLayers i) = 0 :=
  dg_blackBraidClosure_eq_zero_of_up RD k sc μ i
    (dg_upBraidClosure_neg RD k _ _ i (by rw [ip_neg']; omega))

/-- Khovanov–Lauda III, Definition 3.1(iv) and §3.3.2, in `U_Q(g)`: the closed downward
crossing vanishes in negative coroot weight. -/
theorem dg_blackBraidClosure_negQ (μ : X) (i : I) (hμ : ip RD i μ ≤ -1) :
    NF.dg (pres RD k sc) μ [] [] (blackBraidClosureLayers i) = 0 :=
  dg_blackBraidClosure_eq_zero_of_up RD k sc μ i
    (dg_upBraidClosure_pos RD k _ _ i (by rw [ip_neg']; omega))

end Categorification.KL3.Diagram.CLQ
