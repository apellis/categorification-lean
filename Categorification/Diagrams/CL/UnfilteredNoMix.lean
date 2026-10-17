/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.UnfilteredPresentation
import Categorification.Diagrams.CL.NoMix
import Categorification.TwoRep.RouqUpEqual

/-!
# Unfiltered upward KLR relations and their interpretation

Brundan, arXiv:1501.00350v1, Definition 1.1, (1.2)–(1.4). The non-mixed
presentation uses the existing `nonMixed` predicate and `relationUnfiltered`.
Its upward KLR functor is an instance of `upFunctorC`, not a new diagram calculus.
`RouqFamily.unfiltered_klr_rel` verifies every upward relation in the existing
bicategorical generator interpretation under `BrundanUpKLR`, with no coefficient
homogeneity. Full non-mixed soundness and quotient descent remain separate.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation TwoRep

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (Sc : CLScalars C k)

/-- Omit exactly the same mixed relations as `presNM`, without discarding any
rectangular coefficient in the upward equations. -/
def presUnfilteredNM : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels {r : Rel RD // nonMixed RD r}
    (fun r => r.1.dom) (fun r => r.1.cod) (fun r => relationUnfiltered RD k Sc r.1)

/-- The non-mixed presentation retains biadjointness. -/
theorem presUnfilteredNM_zigzags :
    (presUnfilteredNM RD k Sc).PivotalZigzags (inv RD).toColourDuality :=
  Presentation.pivotal_addRels_zigzags (inv RD).toColourDuality (pres0 RD k) _ _ _ _

/-- The specified non-mixed relations hold in the quotient. -/
theorem presUnfilteredNM_lin_rel (r : Rel RD) (h : nonMixed RD r) :
    (presUnfilteredNM RD k Sc).lin (relationUnfiltered RD k Sc r) = 0 :=
  (presUnfilteredNM RD k Sc).lin_rel_self (.inr ⟨r, h⟩)

/-- Homogeneous specialization of the non-mixed presentation. -/
theorem presUnfilteredNM_eq_presNM
    (hhom : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    presUnfilteredNM RD k Sc = presNM RD k Sc := by
  unfold presUnfilteredNM presNM
  rw [relationUnfiltered_eq_relationCL RD k Sc hhom]

variable (hr : ∀ i, Sc.r i = 1)

include hr in
/-- All unfiltered KLR relations hold on upward strands in the full presentation. -/
theorem presUnfiltered_klr : KLRHolds (presUnfiltered RD k Sc) (brundanQ Sc) := by
  intro μ r
  have hr' : (fun i => (Sc.r i : k)) = fun _ => 1 := by
    funext i
    rw [hr i, Units.val_one]
  have h := presUnfiltered_lin_rel RD k Sc (.klr μ r)
  change (presUnfiltered RD k Sc).lin
    (upLin RD k μ (relationR k (brundanQ Sc) (fun i => (Sc.r i : k)) r)) = 0 at h
  rwa [hr', relationR_one] at h

include hr in
/-- The same upward relations already hold before imposing mixed equations. -/
theorem presUnfilteredNM_klr : KLRHolds (presUnfilteredNM RD k Sc) (brundanQ Sc) := by
  intro μ r
  have hr' : (fun i => (Sc.r i : k)) = fun _ => 1 := by
    funext i
    rw [hr i, Units.val_one]
  have h := presUnfilteredNM_lin_rel RD k Sc (.klr μ r) trivial
  change (presUnfilteredNM RD k Sc).lin
    (upLin RD k μ (relationR k (brundanQ Sc) (fun i => (Sc.r i : k)) r)) = 0 at h
  rwa [hr', relationR_one] at h

/-- A linear functor from the KLR category with all rectangular coefficients
into the unfiltered non-mixed presentation, at any rightmost weight. -/
abbrev unfilteredUpFunctor (μ : X) :
    (KLR.Diagram.pres k (brundanQ Sc)).Presented ⥤ (presUnfilteredNM RD k Sc).Presented :=
  upFunctorC _ _ (presUnfilteredNM_klr RD k Sc hr) μ

/-- The upward functor sends each diagram to that diagram on upward strands. -/
theorem unfilteredUpFunctor_diag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (unfilteredUpFunctor RD k Sc hr μ).map ((KLR.Diagram.pres k (brundanQ Sc)).diag d) =
      (presUnfilteredNM RD k Sc).diag (upDiag RD μ d) :=
  upFunctorC_diag (presUnfilteredNM_klr RD k Sc hr) μ d

/-- At the KL scalars the specialization is literal equality with `presNM`. -/
theorem presUnfilteredNM_kl :
    presUnfilteredNM RD k (CLScalars.kl : CLScalars C k) = presNM RD k CLScalars.kl :=
  presUnfilteredNM_eq_presNM RD k _ (by intros; rfl)

end Categorification.KL3.Diagram.CL

namespace Categorification.TwoRep.RouqFamily

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)

private theorem unfiltered_map_zero_transport {s t s' t' : X} {a b : Obj (psig RD)}
    (ha : Cond s t a) (hb : Cond s t b) (ha' : Cond s' t' a) (hb' : Cond s' t' b)
    (f : LinDiagram k a b) (h : admissibleMap (S.genImg Sc) ha' hb' f = 0) :
    admissibleMap (S.genImg Sc) ha hb f = 0 := by
  have hs : s = s' := ha.2.2.symm.trans ha'.2.2
  subst s'
  have ht : t = t' := ha.2.1.symm.trans ha'.2.1
  subst t'
  exact h

/-- Brundan Definition 1.1 (1.2)–(1.4) kills every upward constructor of the
unfiltered presentation in the existing generator interpretation. Only the
source normalization `r_i = 1` is required; there is no homogeneity premise. -/
theorem unfiltered_klr_rel (H : BrundanUpKLR S Sc) (hr : ∀ i, Sc.r i = 1)
    (μ : X) (r : KLR.Diagram.Rel I) {s t : X}
    (ha : Cond s t (Rel.dom (.klr (RD := RD) μ r)))
    (hb : Cond s t (Rel.cod (.klr (RD := RD) μ r))) :
    admissibleMap (S.genImg Sc) ha hb (CL.relationUnfiltered RD k Sc (.klr μ r)) = 0 := by
  cases r with
  | sqEq i =>
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.klr_sqEq_rel Sc i μ)
  | sqNe i j h =>
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.brundan_sqNe Sc H i j h μ)
  | slideLEq i =>
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.klr_slideLEq_rel Sc i μ (hr i))
  | slideREq i =>
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.klr_slideREq_rel Sc i μ (hr i))
  | slideLNe i j h =>
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.up_slideLNe Sc H i j h μ)
  | slideRNe i j h =>
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.up_slideRNe Sc H i j h μ)
  | braid i j l h =>
    classical
    by_cases hil : i = l
    · subst l
      have hij : i = j := by simpa using h
      subst j
      exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.klr_braid_self_rel Sc i μ)
    · exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.up_braid Sc H i j l hil μ)
  | braidQ i j h =>
    change admissibleMap (S.genImg Sc) ha hb (upLin RD k μ
      (LinDiagram.of (KLR.Diagram.braidL i j i) - LinDiagram.of (KLR.Diagram.braidR i j i) -
        (Sc.r i : k) • KLR.Diagram.lpoly k
          ![KLR.Diagram.E0 i j i, KLR.Diagram.E1 i j i, KLR.Diagram.E2 i j i]
          (KLR.qbar (brundanQ Sc i j)))) = 0
    rw [hr i, Units.val_one, one_smul]
    exact unfiltered_map_zero_transport S Sc ha hb _ _ _ (S.brundan_braidQ Sc H i j h μ)

end Categorification.TwoRep.RouqFamily
