/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqDescent
import Categorification.TwoRep.RouqMixedCycLeft
import Categorification.TwoRep.RouqMixedDownup

/-!
# Full normalized CL soundness and quotient action

Brundan, arXiv:1501.00350v1, Definition 1.1, (1.7), requires the original
right-adjunction mixed mates to be invertible. `BrundanMixedInversion` states
exactly this independent source input on every distinct ordered pair and region
square. It does not change `RouqFamily` or the weaker `presNM` results.

`RouqFamily.fullCL_rel` proves every original CL relation: the previously
excluded left crossing cyclicities use both ordered inversion instances, and
the two down-up relations use their corresponding, correctly reindexed square.
The maps are the unchanged `genImg`, with the original derived `adjL`.
`presCL_ideal` annihilates the entire horizontal ideal; `presCLFunctor` and
`presCLPseudofunctor` give the actual quotient action and representative formulas.

The coefficient compatibility is explicit: the rectangular Brundan polynomial
agrees with `CL.qCL` only under the displayed off-weight vanishing condition.
The normalization is `r_i = 1`; `t_ij` remains arbitrary. The target has linear
Hom categories and linear whiskering over any commutative ring, with no grading,
zero objects, Hom-finiteness or scalar endomorphism bound. A concrete action
must separately establish the source equations and mixed inversion; neither
that construction nor nondegeneracy nor arbitrary-r rescaling is asserted here.
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

/-- Brundan's mixed inversion relation (1.7), on the actual right-adjunction
mates for every distinct ordered pair and every region square. This is separate
source data, not a consequence of `RouqFamily` or upward KLR equations. -/
def BrundanMixedInversion (S : RouqFamily (B := B) RD) : Prop :=
  ∀ (i j : I), i ≠ j → ∀ {a b c d : X}
    (hj : a + RD.iX j = b) (hi' : b + RD.iX i = d)
    (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d),
    IsIso (S.mixedSigma i j hj hi' hi hj')

namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
variable [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
private theorem cl_map_zero_transport {s t s' t' : X} {a b : Obj (psig RD)}
    (ha : Cond s t a) (hb : Cond s t b) (ha' : Cond s' t' a) (hb' : Cond s' t' b)
    (f : LinDiagram k a b) (h : admissibleMap (S.genImg Sc) ha' hb' f = 0) :
    admissibleMap (S.genImg Sc) ha hb f = 0 := by
  have hs : s = s' := ha.2.2.symm.trans ha'.2.2
  subst s'
  have ht : t = t' := ha.2.1.symm.trans ha'.2.1
  subst t'
  exact h

/-- Every original CL relation is annihilated by the original generator images.
The three mixed constructors are proved using the independent source inversion
relation, not assumed as soundness hypotheses. -/
theorem fullCL_rel (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (r : Rel RD) {s t : X} (ha : Cond s t r.dom) (hb : Cond s t r.cod) :
    admissibleMap (S.genImg Sc) ha hb (CL.relationCL RD k Sc r) = 0 := by
  classical
  by_cases hn : CL.nonMixed RD r
  · exact S.nonMixed_rel Sc (H.toCL hq) hr r hn ha hb
  cases r with
  | cycCrossL j i μ =>
    change j ≠ i at hn
    let {a b c d : X} (hj : a + RD.iX j = b) (hi' : b + RD.iX i = d)
        (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d) :
        IsIso (S.mixedSigma i j hj hi' hi hj') := M i j hn.symm hj hi' hi hj'
    let {a b c d : X} (hi : a + RD.iX i = b) (hj' : b + RD.iX j = d)
        (hj : a + RD.iX j = c) (hi' : c + RD.iX i = d) :
        IsIso (S.mixedSigma j i hi hj' hj hi') := M j i hn hi hj' hj hi'
    exact cl_map_zero_transport S Sc ha hb _ _ _ (S.mixed_cycCrossL_rel Sc H j i hn.symm μ)
  | downupEF i j hij μ =>
    let {a b c d : X} (hi : a + RD.iX i = b) (hj' : b + RD.iX j = d)
        (hj : a + RD.iX j = c) (hi' : c + RD.iX i = d) :
        IsIso (S.mixedSigma j i hi hj' hj hi') := M j i hij.symm hi hj' hj hi'
    exact cl_map_zero_transport S Sc ha hb _ _ _ (S.mixed_downupEF_rel Sc H i j hij μ)
  | downupFE i j hij μ =>
    let {a b c d : X} (hj : a + RD.iX j = b) (hi' : b + RD.iX i = d)
        (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d) :
        IsIso (S.mixedSigma i j hj hi' hi hj') := M i j hij hj hi' hi hj'
    exact cl_map_zero_transport S Sc ha hb _ _ _ (S.mixed_downupFE_rel Sc H i j hij μ)
  | _ => exact (hn trivial).elim

/-- All defining generators of the full normalized CL presentation, including
both pivotal zigzags, vanish under the unchanged admissible interpretation. -/
theorem presCL_rel (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (r : (CL.presCL RD k Sc).Rel) {s t : X}
    (ha : Cond s t ((CL.presCL RD k Sc).dom r))
    (hb : Cond s t ((CL.presCL RD k Sc).cod r)) :
    admissibleMap (S.genImg Sc) ha hb ((CL.presCL RD k Sc).rel r) = 0 := by
  rcases r with (r | c | c) | r
  · exact r.elim
  · exact cl_map_zero_transport S Sc ha hb _ _ _ (S.zigL_rel Sc c)
  · exact cl_map_zero_transport S Sc ha hb _ _ _ (S.zigR_rel Sc c)
  · exact S.fullCL_rel Sc H M hr hq r ha hb

/-- The whole original horizontal ideal of normalized `presCL` is annihilated. -/
theorem presCL_ideal (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram k a b) (hf : f ∈ (CL.presCL RD k Sc).ideal a b) :
    admissibleMap (S.genImg Sc) ha hb f = 0 :=
  admissibleMap_ideal (S.genImg Sc) (CL.presCL RD k Sc)
    (fun r {_ _} ha hb => S.presCL_rel Sc H M hr hq r ha hb) Signature.IsEven.odd_eq_false ha hb f hf

/-- A linear functor on each admissible component of the original quotient. -/
def presCLFunctor (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) (s t : X) :
    PresentedAdmissible (CL.presCL RD k Sc) s t ⥤ (S.model.obj t ⟶ S.model.obj s) :=
  admissiblePresentedInterp (S.genImg Sc) (CL.presCL RD k Sc)
    (fun r {_ _} ha hb => S.presCL_rel Sc H M hr hq r ha hb) Signature.IsEven.odd_eq_false s t

instance presCLFunctor_additive (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (s t : X) : (S.presCLFunctor Sc H M hr hq s t).Additive :=
  admissiblePresentedInterp_additive (S.genImg Sc) (CL.presCL RD k Sc)
    (fun r {_ _} ha hb => S.presCL_rel Sc H M hr hq r ha hb) Signature.IsEven.odd_eq_false s t

instance presCLFunctor_linear (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (s t : X) : (S.presCLFunctor Sc H M hr hq s t).Linear k :=
  admissiblePresentedInterp_linear (S.genImg Sc) (CL.presCL RD k Sc)
    (fun r {_ _} ha hb => S.presCL_rel Sc H M hr hq r ha hb) Signature.IsEven.odd_eq_false s t

/-- The component functor agrees with the original map on every linear representative. -/
@[simp] theorem presCLFunctor_map_lin
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b)
    (f : LinDiagram k a b) :
    (S.presCLFunctor Sc H M hr hq s t).map
      (ObjectProperty.homMk
        (X := (⟨(CL.presCL RD k Sc).obj a, ha⟩ : PresentedAdmissible (CL.presCL RD k Sc) s t))
        (Y := (⟨(CL.presCL RD k Sc).obj b, hb⟩ : PresentedAdmissible (CL.presCL RD k Sc) s t))
        ((CL.presCL RD k Sc).lin f)) =
      admissibleMap (S.genImg Sc) (s := s) (t := t) ha hb f := rfl

/-- Normalized `presCL` acts by a pseudofunctor in the original target bicategory. -/
def presCLPseudofunctor (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    Pseudofunctor (RevBicat (CL.presCL RD k Sc).Bicat) B :=
  admissiblePseudofunctor (S.genImg Sc) (fun r {_ _} ha hb => S.presCL_rel Sc H M hr hq r ha hb)

/-- Descent preserves the original interpretation on every linear representative. -/
@[simp] theorem presCLPseudofunctor_map₂_lin
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    {a b : RevBicat (CL.presCL RD k Sc).Bicat} {x y : a ⟶ b}
    (f : LinDiagram k x.obj y.obj) :
    (S.presCLPseudofunctor Sc H M hr hq).map₂ ((CL.presCL RD k Sc).lin f : x ⟶ y) =
      admissibleMap (S.genImg Sc) (PresPseudo.condW x) (PresPseudo.condW y) f := rfl

end RouqFamily
end Categorification.TwoRep
