/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackBraidClosure
import Categorification.Diagrams.KL3.MixedR3Sl2

/-!
# The closed black crossing with marked dots

In the capped black–red–black braid of Webster, arXiv:1309.3796v2,
Definitions 4.5 and 4.24, assign the extra dots to the outer upward
strand on the physical left. In raw KL order this is the rightmost leg.
The dots are on the whisker of the left curl in positive coroot weight.
In negative coroot weight they are on the right curl. Its sum is empty
in the needed degrees by the dotted curl relation (Lauda,
arXiv:0803.3652v2, Proposition 5.4, and KL III, arXiv:0807.3250v1,
§3.3.2).
-/

noncomputable section
namespace Categorification.KL3.Diagram

open CategoryTheory QuantumGroup QuantumGroup.UDot

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- The two black cups, extra dots on the rightmost upright leg, the
downward crossing and the two caps, in raw KL word order. -/
def pointedBlackClosureLayers (i : I) (N : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), []), ([], .cup (up i), [dn i, up i])] ++
  List.replicate N ([up i, dn i, dn i], .dot (up i), []) ++
  [([up i], .cross false i i, [up i]),
    ([up i, dn i], .cap (up i), []), ([], .cap (dn i), [])]

private def upPointedClosureLayers (i : I) (N : ℕ) : List (LayerData I) :=
  [([], .cup (up i), []), ([], .cup (dn i), [up i, dn i])] ++
  List.replicate N ([dn i, up i, up i], .dot (dn i), []) ++
  [([dn i], .cross true i i, [dn i]),
    ([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])]

private theorem upPointedClosure_of_nonpositive (ν : X) (i : I) (N : ℕ) (hν : ip RD i ν ≤ -1) :
    dg RD k ν [] [] (upPointedClosureLayers i N) = 0 := by
  unfold upPointedClosureLayers
  dstep ([([], .cup (up i), []), ([], .cup (dn i), [up i, dn i])] ++
    List.replicate N ([dn i, up i, up i], .dot (dn i), []) ++
    [([dn i], .cross true i i, [dn i])]) [] [] []
    (dg_swap' RD k ν [] [] [] (.cap (up i)) (.cap (dn i))).symm
  have hd := dg_dotsR_comm RD k (μ := ν) (dn i)
    (A := [([dn i], .cross true i i, []), ([], .cap (up i), [up i])])
    (s := [dn i, up i, up i]) (t := [up i]) (by schain) N
  dstep [([], .cup (up i), []), ([], .cup (dn i), [up i, dn i])]
    [([], .cap (dn i), [])] [] [] hd
  have h := dg_curlL RD k i (wt RD ν [dn i])
  have hindex : ip RD i (wt RD (wt RD ν [dn i]) [up i]) = ip RD i ν := by simp [ip, wt, sh, sgn]
  rw [hindex, show (ip RD i ν + 1).toNat = 0 by omega, Finset.sum_range_zero] at h
  let ls : List (LayerData I) :=
    [([], .cup (up i), []), ([], .cup (dn i), [up i, dn i]),
      ([dn i], .cross true i i, [dn i]), ([], .cap (up i), [up i, dn i])] ++
        List.replicate N ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]
  have hstep := dg_stepL RD k ν (s₀ := []) (t₀ := []) (L := ls)
    [([], .cup (up i), [])] (List.replicate N ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])])
    [] [dn i] h (by schain) (by schain) (by simp [ls, whL])
  rw [map_zero] at hstep
  simpa [ls, whL, List.append_assoc] using hstep

private theorem rightCurlDotted_zero (ν : X) (i : I) (N : ℕ) (hN : (N : ℤ) < ip RD i ν) :
    dg RD k ν [up i] [up i]
      ([([up i], .cup (up i), [])] ++ List.replicate N ([up i], .dot (up i), [dn i]) ++
        [([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])]) = 0 := by
  have h := ptrR_nhDotR_nhCross RD k ν i N
  rw [show ((N : ℤ) + -ip RD i ν + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero] at h
  rw [nhDotR, nhCross, dg_comp (by schain) (by schain), ptrR_dg] at h
  simpa [whL, List.append_assoc] using h

private theorem upPointedClosure_of_positive (ν : X) (i : I) (N : ℕ) (hN : (N : ℤ) < ip RD i ν) :
    dg RD k ν [] [] (upPointedClosureLayers i N) = 0 := by
  unfold upPointedClosureLayers
  dswap 0
  dstep [([], .cup (dn i), [])]
    [([dn i], .cross true i i, [dn i]), ([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])]
    [dn i, up i] [] (dg_dots_cupUp RD k i ν N)
  let ls : List (LayerData I) :=
    [([], .cup (dn i), []), ([dn i, up i], .cup (up i), [])] ++
      List.replicate N ([dn i, up i], .dot (up i), [dn i]) ++
      [([dn i], .cross true i i, [dn i]),
        ([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])]
  have h := dg_stepL RD k ν (s₀ := []) (t₀ := []) (L := ls) [([], .cup (dn i), [])]
    [([], .cap (up i), [])] [dn i] [] (rightCurlDotted_zero RD k ν i N hN)
    (by schain) (by schain) (by simp [ls, whL])
  have hzero := h.trans (map_zero (ctxL RD k ν [] [] [([], .cup (dn i), [])] [dn i] []
    [([], .cap (up i), [])] [up i] [up i]))
  simpa [ls, whL, List.append_assoc] using hzero

variable [DecidableEq I]

private theorem omega_upPointedClosure (ν : X) (i : I) (N : ℕ)
    (h : dg RD k ν [] [] (upPointedClosureLayers i N) = 0) :
    dg RD k (-ν) [] [] (pointedBlackClosureLayers i N) = 0 := by
  have h' := congrArg (omegaU RD k).map h
  rw [Functor.map_zero, omegaU_dg_nil ν _ (by unfold upPointedClosureLayers; schain)] at h'
  have hs : Sig.sgnS (upPointedClosureLayers i N) = -1 := by
    simp [upPointedClosureLayers, Sig.sgnS, Sig.sgnSh]
  rw [hs, Int.cast_neg, Int.cast_one, neg_smul, one_smul] at h'
  have hw : Omega.wls (upPointedClosureLayers i N) = pointedBlackClosureLayers i N := by
    simp [Omega.wls, Omega.ld, Omega.shape, upPointedClosureLayers, pointedBlackClosureLayers]
  change -dg RD k (-ν) [] [] (Omega.wls (upPointedClosureLayers i N)) = 0 at h'
  rw [hw] at h'
  exact neg_eq_zero.mp h'

/-- The marked dots lie on the strand whiskering a vanishing curl. The
positive-side closure vanishes at every dot count. -/
theorem dg_pointedBlackClosure_pos (μ : X) (i : I) (N : ℕ) (hμ : 1 ≤ ip RD i μ) :
    dg RD k μ [] [] (pointedBlackClosureLayers i N) = 0 := by
  obtain ⟨ν, rfl⟩ : ∃ ν : X, μ = -ν := ⟨-μ, (neg_neg μ).symm⟩
  rw [ip_neg'] at hμ
  exact omega_upPointedClosure RD k ν i N (upPointedClosure_of_nonpositive RD k ν i N (by omega))

/-- Moving the marked dots around the cup puts them on the vanishing
right curl when `N + 1 ≤ -⟨i, μ⟩`. -/
theorem dg_pointedBlackClosure_neg (μ : X) (i : I) (N : ℕ) (hμ : (N : ℤ) + 1 ≤ -ip RD i μ) :
    dg RD k μ [] [] (pointedBlackClosureLayers i N) = 0 := by
  obtain ⟨ν, rfl⟩ : ∃ ν : X, μ = -ν := ⟨-μ, (neg_neg μ).symm⟩
  rw [ip_neg', neg_neg] at hμ
  exact omega_upPointedClosure RD k ν i N (upPointedClosure_of_positive RD k ν i N (by omega))

end Categorification.KL3.Diagram
