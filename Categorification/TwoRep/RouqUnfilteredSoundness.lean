/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.UnfilteredNoMix
import Categorification.TwoRep.RouqFullCL

/-!
# Unfiltered Rouquier generator soundness

Brundan, arXiv:1501.00350v1, Definition 1.1 (1.2)–(1.9) and (1.26).
The unchanged generator model kills every relation of `CL.presUnfiltered`,
including pivotal zigzags and scalar cyclicity. Only the upward KLR case changes
from the homogeneous presentation; all other equations use their existing proofs.
The hypotheses are the rectangular upward equations, independent mixed inversion
and `r_i = 1`. No coefficient homogeneity, target grading, zero objects or
assumed vanishing of target relations is used. Quotient descent is separate.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
variable [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
private theorem unfiltered_zero_transport {s t s' t' : X} {a b : Obj (psig RD)}
    (ha : Cond s t a) (hb : Cond s t b) (ha' : Cond s' t' a) (hb' : Cond s' t' b)
    (f : LinDiagram k a b) (h : admissibleMap (S.genImg Sc) ha' hb' f = 0) :
    admissibleMap (S.genImg Sc) ha hb f = 0 := by
  have hs : s = s' := ha.2.2.symm.trans ha'.2.2
  subst s'
  have ht : t = t' := ha.2.1.symm.trans ha'.2.1
  subst t'
  exact h

/-- Every non-mixed unfiltered relation vanishes in the original generator model. -/
theorem unfiltered_nonMixed_rel (H : BrundanUpKLR S Sc) (hr : ∀ i, Sc.r i = 1)
    (r : Rel RD) (hn : CL.nonMixed RD r) {s t : X}
    (ha : Cond s t r.dom) (hb : Cond s t r.cod) :
    admissibleMap (S.genImg Sc) ha hb (CL.relationUnfiltered RD k Sc r) = 0 := by
  cases r with
  | cycDotR i μ => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.cycDotR_rel Sc i μ)
  | cycDotL i μ => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.cycDotL_rel Sc i μ)
  | cwNeg i μ n h => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.cwNeg_rel Sc i μ n h)
  | ccwNeg i μ n h => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.ccwNeg_rel Sc i μ n h)
  | cwOne i μ h => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.cwOne_rel Sc i μ h)
  | ccwOne i μ h => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.ccwOne_rel Sc i μ h)
  | curlR i μ =>
    exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.curlR_rel Sc i μ (by rw [hr, Units.val_one]))
  | curlL i μ =>
    exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.curlL_rel Sc i μ (by rw [hr, Units.val_one]))
  | decompEF i μ => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.decompEF_rel Sc i μ (hr i))
  | decompFE i μ => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.decompFE_rel Sc i μ (hr i))
  | cycCrossR j i μ => exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.mixed_cycCrossR_rel Sc j i μ)
  | cycCrossL j i μ =>
    change j = i at hn
    subst j
    exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.cycCrossL_rel Sc i μ)
  | downupEF _ _ _ _ | downupFE _ _ _ _ => exact hn.elim
  | klr μ r => exact S.unfiltered_klr_rel Sc H hr μ r ha hb

/-- Every unfiltered relation is annihilated by the original generator images.
The three mixed constructors are proved using the independent source inversion
relation, not assumed as soundness hypotheses. -/
theorem unfiltered_rel (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (hr : ∀ i, Sc.r i = 1)
    (r : Rel RD) {s t : X} (ha : Cond s t r.dom) (hb : Cond s t r.cod) :
    admissibleMap (S.genImg Sc) ha hb (CL.relationUnfiltered RD k Sc r) = 0 := by
  classical
  by_cases hn : CL.nonMixed RD r
  · exact S.unfiltered_nonMixed_rel Sc H hr r hn ha hb
  cases r with
  | cycCrossL j i μ =>
    change j ≠ i at hn
    let {a b c d : X} (hj : a + RD.iX j = b) (hi' : b + RD.iX i = d)
        (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d) :
        IsIso (S.mixedSigma i j hj hi' hi hj') := M i j hn.symm hj hi' hi hj'
    let {a b c d : X} (hi : a + RD.iX i = b) (hj' : b + RD.iX j = d)
        (hj : a + RD.iX j = c) (hi' : c + RD.iX i = d) :
        IsIso (S.mixedSigma j i hi hj' hj hi') := M j i hn hi hj' hj hi'
    exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.mixed_cycCrossL_rel Sc H j i hn.symm μ)
  | downupEF i j hij μ =>
    let {a b c d : X} (hi : a + RD.iX i = b) (hj' : b + RD.iX j = d)
        (hj : a + RD.iX j = c) (hi' : c + RD.iX i = d) :
        IsIso (S.mixedSigma j i hi hj' hj hi') := M j i hij.symm hi hj' hj hi'
    exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.mixed_downupEF_rel Sc H i j hij μ)
  | downupFE i j hij μ =>
    let {a b c d : X} (hj : a + RD.iX j = b) (hi' : b + RD.iX i = d)
        (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d) :
        IsIso (S.mixedSigma i j hj hi' hi hj') := M i j hij hj hi' hi hj'
    exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.mixed_downupFE_rel Sc H i j hij μ)
  | _ => exact (hn trivial).elim

/-- All defining generators of the normalized unfiltered presentation, including
both pivotal zigzags, vanish under the unchanged admissible interpretation. -/
theorem presUnfiltered_rel (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (hr : ∀ i, Sc.r i = 1)
    (r : (CL.presUnfiltered RD k Sc).Rel) {s t : X}
    (ha : Cond s t ((CL.presUnfiltered RD k Sc).dom r))
    (hb : Cond s t ((CL.presUnfiltered RD k Sc).cod r)) :
    admissibleMap (S.genImg Sc) ha hb ((CL.presUnfiltered RD k Sc).rel r) = 0 := by
  rcases r with (r | c | c) | r
  · exact r.elim
  · exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.zigL_rel Sc c)
  · exact unfiltered_zero_transport S Sc ha hb _ _ _ (S.zigR_rel Sc c)
  · exact S.unfiltered_rel Sc H M hr r ha hb

end RouqFamily
end Categorification.TwoRep
