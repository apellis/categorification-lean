/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpEqual
import Categorification.TwoRep.RouqDecomp
import Categorification.TwoRep.RouqCurls

/-!
# Normalized generator soundness for `presNM`

Every defining generator relation of the original `CL.presNM` has zero image
under the unchanged `RouqFamily.genImg`, on each admissible outer-region component.
This includes both pivotal zigzags, every upward KLR constructor, both dot
cyclicities, all right crossing cyclicities, the retained left crossing cyclicities,
real bubble evaluations, curls and EF/FE decompositions.

The scalar hypotheses are explicit: `Sc.r i = 1` for every colour, and the source
mixed KLR equations for exactly `CL.qCL Sc`. The Brundan variant instead assumes
his rectangular polynomial and the stated vanishing of off-weight coefficients.
Whiskering is linear over `k`. No zero objects, grading, Hom-finiteness or scalar
endomorphism bound are required. This is generator soundness, not descent through
the horizontally generated ideal: admissible interchange and horizontal closure
remain separate obligations.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}
namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)

private theorem map_zero_transport {s t s' t' : X} {a b : Obj (psig RD)}
    (ha : Cond s t a) (hb : Cond s t b) (ha' : Cond s' t' a) (hb' : Cond s' t' b)
    (f : LinDiagram k a b) (h : admissibleMap (S.genImg Sc) ha' hb' f = 0) :
    admissibleMap (S.genImg Sc) ha hb f = 0 := by
  have hs : s = s' := ha.2.2.symm.trans ha'.2.2
  subst s'
  have ht : t = t' := ha.2.1.symm.trans ha'.2.1
  subst t'
  exact h

/-- All actual upward CL relation constructors, including the all-equal braid. -/
theorem klr_rel (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    (μ : X) (r : KLR.Diagram.Rel I) {s t : X}
    (ha : Cond s t (Rel.dom (.klr (RD := RD) μ r)))
    (hb : Cond s t (Rel.cod (.klr (RD := RD) μ r))) :
    admissibleMap (S.genImg Sc) ha hb (CL.relationCL RD k Sc (.klr μ r)) = 0 := by
  cases r with
  | sqEq i => exact map_zero_transport S Sc ha hb _ _ _ (S.klr_sqEq_rel Sc i μ)
  | sqNe i j h => exact map_zero_transport S Sc ha hb _ _ _ (S.klr_sqNe_rel Sc H i j h μ)
  | slideLEq i => exact map_zero_transport S Sc ha hb _ _ _ (S.klr_slideLEq_rel Sc i μ (hr i))
  | slideREq i => exact map_zero_transport S Sc ha hb _ _ _ (S.klr_slideREq_rel Sc i μ (hr i))
  | slideLNe i j h => exact map_zero_transport S Sc ha hb _ _ _ (S.klr_slideLNe_rel Sc H i j h μ)
  | slideRNe i j h => exact map_zero_transport S Sc ha hb _ _ _ (S.klr_slideRNe_rel Sc H i j h μ)
  | braid i j l h =>
    classical
    by_cases hil : i = l
    · subst l
      have hij : i = j := by simpa using h
      subst j
      exact map_zero_transport S Sc ha hb _ _ _ (S.klr_braid_self_rel Sc i μ)
    · exact map_zero_transport S Sc ha hb _ _ _ (S.klr_braid_rel Sc H i j l hil μ)
  | braidQ i j h =>
    exact map_zero_transport S Sc ha hb _ _ _ (S.klr_braidQ_rel Sc H i j h (hr i) μ)

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

/-- All CL relation constructors retained by `nonMixed`, in the original target. -/
theorem nonMixed_rel (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    (r : Rel RD) (hn : CL.nonMixed RD r) {s t : X}
    (ha : Cond s t r.dom) (hb : Cond s t r.cod) :
    admissibleMap (S.genImg Sc) ha hb (CL.relationCL RD k Sc r) = 0 := by
  cases r with
  | cycDotR i μ => exact map_zero_transport S Sc ha hb _ _ _ (S.cycDotR_rel Sc i μ)
  | cycDotL i μ => exact map_zero_transport S Sc ha hb _ _ _ (S.cycDotL_rel Sc i μ)
  | cwNeg i μ n h => exact map_zero_transport S Sc ha hb _ _ _ (S.cwNeg_rel Sc i μ n h)
  | ccwNeg i μ n h => exact map_zero_transport S Sc ha hb _ _ _ (S.ccwNeg_rel Sc i μ n h)
  | cwOne i μ h => exact map_zero_transport S Sc ha hb _ _ _ (S.cwOne_rel Sc i μ h)
  | ccwOne i μ h => exact map_zero_transport S Sc ha hb _ _ _ (S.ccwOne_rel Sc i μ h)
  | curlR i μ =>
    exact map_zero_transport S Sc ha hb _ _ _ (S.curlR_rel Sc i μ (by rw [hr, Units.val_one]))
  | curlL i μ =>
    exact map_zero_transport S Sc ha hb _ _ _ (S.curlL_rel Sc i μ (by rw [hr, Units.val_one]))
  | decompEF i μ => exact map_zero_transport S Sc ha hb _ _ _ (S.decompEF_rel Sc i μ (hr i))
  | decompFE i μ => exact map_zero_transport S Sc ha hb _ _ _ (S.decompFE_rel Sc i μ (hr i))
  | cycCrossR j i μ => exact map_zero_transport S Sc ha hb _ _ _ (S.mixed_cycCrossR_rel Sc j i μ)
  | cycCrossL j i μ =>
    change j = i at hn
    subst j
    exact map_zero_transport S Sc ha hb _ _ _ (S.cycCrossL_rel Sc i μ)
  | downupEF _ _ _ _ | downupFE _ _ _ _ => exact hn.elim
  | klr μ r => exact S.klr_rel Sc H hr μ r ha hb

/-- **Normalized `presNM` generator soundness.** Every defining relation, including
both pivotal zigzags, is killed by the unchanged admissible interpretation.
This does not assert interchange or closure under horizontal contexts. -/
theorem presNM_rel (H : RouqUpKLR S (CL.qCL Sc)) (hr : ∀ i, Sc.r i = 1)
    (r : (CL.presNM RD k Sc).Rel) {s t : X}
    (ha : Cond s t ((CL.presNM RD k Sc).dom r))
    (hb : Cond s t ((CL.presNM RD k Sc).cod r)) :
    admissibleMap (S.genImg Sc) ha hb ((CL.presNM RD k Sc).rel r) = 0 := by
  rcases r with (r | c | c) | ⟨r, hn⟩
  · exact r.elim
  · exact map_zero_transport S Sc ha hb _ _ _ (S.zigL_rel Sc c)
  · exact map_zero_transport S Sc ha hb _ _ _ (S.zigR_rel Sc c)
  · exact S.nonMixed_rel Sc H hr r hn ha hb

/-- Brundan source equations imply normalized CL generator soundness under precisely
stated coefficient compatibility; target grading is not required. -/
theorem presNM_rel_of_brundan (H : BrundanUpKLR S Sc) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (r : (CL.presNM RD k Sc).Rel) {s t : X}
    (ha : Cond s t ((CL.presNM RD k Sc).dom r))
    (hb : Cond s t ((CL.presNM RD k Sc).cod r)) :
    admissibleMap (S.genImg Sc) ha hb ((CL.presNM RD k Sc).rel r) = 0 :=
  S.presNM_rel Sc (H.toCL hq) hr r ha hb

end RouqFamily
end Categorification.TwoRep
