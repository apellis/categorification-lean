/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.Diagrams.KL3.BubbleSlidesGen

/-!
# The pure black closures adjoining a red braid

Khovanov–Lauda III, arXiv:0807.3250v1, Definition 3.1(iv) and §3.3.2.
The same-colour downward crossing between two oppositely oriented cups
and caps is a closed left curl after interchanging the caps, or a
closed right curl after interchanging the cups. The left-curl sum is
empty in positive coroot weight by orientation reversal. The downward
right-curl sum is empty in negative coroot weight. This is the pure
black step of closing the black–red–black relation in Webster,
arXiv:1309.3796v2, Definitions 4.5 and 4.24.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe u v w

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

/-- The pure black cap closure with the two downward legs crossing, in
raw KL word order with the outer region on the right. -/
def blackBraidClosureLayers (i : I) : List (LayerData I) :=
  [([], .cup (dn i), []),
    ([], .cup (up i), [dn i, up i]),
    ([up i], .cross false i i, [up i]),
    ([up i, dn i], .cap (up i), []),
    ([], .cap (dn i), [])]

/-- Khovanov–Lauda III, Definition 3.1(iv) and §3.3.2. The closed downward
crossing vanishes in positive coroot weight by the left curl relation.
Under orientation reversal, the right whisker is downward and the
left-curl sum has upper index given by the negated outer coroot. -/
theorem dg_blackBraidClosure_pos (μ : X) (i : I) (hμ : 1 ≤ ip RD i μ) :
    dg RD k μ [] [] (blackBraidClosureLayers i) = 0 := by
  obtain ⟨ν, rfl⟩ : ∃ ν : X, μ = -ν := ⟨-μ, (neg_neg μ).symm⟩
  rw [ip_neg'] at hμ
  let ls : List (LayerData I) :=
    [([], .cup (up i), []),
      ([], .cup (dn i), [up i, dn i]),
      ([dn i], .cross true i i, [dn i]),
      ([dn i, up i], .cap (dn i), []),
      ([], .cap (up i), [])]
  have hcurlIndex : ip RD i (wt RD (wt RD ν [dn i]) [up i]) = ip RD i ν := by
    simp [ip, wt, sh, sgn]
  have hv : dg RD k ν [] [] ls = 0 := by
    dsimp only [ls]
    dswap 3
    have h := dg_curlL RD k i (wt RD ν [dn i])
    rw [hcurlIndex, show (ip RD i ν + 1).toNat = 0 by omega, Finset.sum_range_zero] at h
    rw [dg_stepL_at _ 1 [] [dn i] h (by (try dnorm); schain) (by (try dnorm); schain)
      (by dnorm), map_zero]
  have h := congrArg (omegaU RD k).map hv
  rw [Functor.map_zero, omegaU_dg_nil ν ls (by dsimp only [ls]; schain)] at h
  have hs : Sig.sgnS ls = -1 := by simp [ls, Sig.sgnS, Sig.sgnSh]
  rw [hs, Int.cast_neg, Int.cast_one, neg_smul, one_smul] at h
  change -dg RD k (-ν) [] [] (blackBraidClosureLayers i) = 0 at h
  exact neg_eq_zero.mp h

/-- Khovanov–Lauda III, Definition 3.1(iv) and §3.3.2. At negative coroot
weight, interchanging the cups exposes the downward right curl with an
upward strand on its left. Its right region is unchanged, so the curl
sum is empty. -/
theorem dg_blackBraidClosure_neg (μ : X) (i : I) (hμ : ip RD i μ ≤ -1) :
    dg RD k μ [] [] (blackBraidClosureLayers i) = 0 := by
  unfold blackBraidClosureLayers
  dswap 0
  have h := dg_curlR_down (RD := RD) (k := k) i μ
  rw [show (ip RD i μ + 1).toNat = 0 by omega, Finset.sum_range_zero] at h
  rw [dg_stepL_at _ 1 [up i] [] h (by (try dnorm); schain) (by (try dnorm); schain)
    (by dnorm)]
  exact map_zero (ctxL RD k μ [] [] _ [up i] [] _ [dn i] [dn i])

end Categorification.KL3.Diagram
