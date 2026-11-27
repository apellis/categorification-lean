/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRelationFamilies
import Categorification.WeightedKLR.RedStrands.DoubleCLMixedPitchforkQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationOf
import Categorification.WeightedKLR.RedStrands.DoubleDownCLComparison

/-!
# Families of relations with general parameters whose reflected images are red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for every Kang–Kashiwara family `Q`.
The black strands carry the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3,
Definition 1.1, `r = 1`) for the black scalars `Sb = blackScalarsQ` (the reflection of the
Cautis–Lauda scalars of `Q`). Adjoining the following families preserves `CoverRelsNegligible`:
the reflected black relations of `U_{Sb}(g)` (`addBlackRelationsOf`), the mixed black relations
and the cup pitchfork relations at the scalars `Sb.t`, the black biadjunction relations, and the
downward KLR relations at the Cautis–Lauda dual parameters of `Sb`, which are `Q` itself on
distinct colours (`clDownwardQ_blackScalarsQ`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open QuantumGroup UDot MvPolynomial

universe u₀ v₀

variable {I : Type*} {C : CartanDatum I} {k : Type*} [CommRing k]

variable [DecidableEq I] {X Y : Type v₀} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

/-- The Cautis–Lauda polynomial of `S^θ` is that of the dual scalars. -/
theorem CLQ.qCL_thetaScalars (S : CL.CLScalars C k) {i j : I} (h : i ≠ j) :
    CL.qCL (CLQ.thetaScalars RD S) i j = CL.qCL S.dual i j :=
  CL.qCL_congr (fun _ _ h => by rw [CLQ.thetaScalars_t_of_ne _ h, CL.CLScalars.dual_t])
    (fun _ _ _ _ _ => by rw [CLQ.thetaScalars_s, CL.CLScalars.dual_s, mul_inv]) h

/-- **The Cautis–Lauda downward parameters of `S^θ` are the parameters of `S`** (`r = 1`). -/
theorem CLQ.clDownwardQ_thetaScalars (S : CL.CLScalars C k) (hr : ∀ i, S.r i = 1) {i j : I}
    (h : i ≠ j) :
    Stendhal.DoubleDiagram.clDownwardQ (CLQ.thetaScalars RD S) i j = CL.qCL S i j := by
  rw [Stendhal.DoubleDiagram.clDownwardQ, ← CLQ.qCL_thetaScalars RD _ (Ne.symm h),
    CLQ.thetaScalars_thetaScalars _ hr, CL.rename_swap_qCL]

end Categorification.KL3.Diagram

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w v₁

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "RDc" => coordinateDatum Λ C
local notation "Sb" => blackScalarsQ Λ C hQ

/-- **The downward parameters of the black scalars are `Q`** on distinct colours. -/
theorem clDownwardQ_blackScalarsQ {i j : I} (h : i ≠ j) :
    DoubleDiagram.clDownwardQ (Sb) i j = Q i j := by
  rw [CLQ.clDownwardQ_thetaScalars _ _ (fun _ => rfl) h]
  have hij : (Sum.inl i : I ⊕ Fin ℓ) ≠ Sum.inl j := fun e => h (Sum.inl_injective e)
  have e := qCL_cyclotomicScalars Λ C hQ hij
  simp only [cyclotomicCoverQ] at e
  rw [← e]
  unfold CL.qCL
  simp only [coverBlackScalars, extendedCartanDatum_dot_inl,
    dij_inl (extendedCartanDatum_dot_inl Λ C)]

variable {Λ C hQ hc} {o : I ⊕ Fin ℓ → ℤ}

/-- **Downward KLR relations at the black scalars.** Adjoining the downward translations of the
KLR relations of the affine cover of the Cautis–Lauda dual of the black scalars preserves
`CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addDownRelationsQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (DoubleDiagram.addDownRelations (RDc) (redWeight Wgt)
      (affineCoverQ (DoubleDiagram.clDownwardQ (Sb)) Λ) P) :=
  hP.addRels fun _ =>
    coverRedNegligible_downRelation_of_empty Λ C hQ hc o _
      (coverRedNegligible_downRelation_affineCover Λ C hQ hc o _
        fun _ _ h => clDownwardQ_blackScalarsQ Λ C hQ h) _ _ _ _ _ _ _

variable (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)

include ho

/-- Adjoining the mixed black relations (2.4a), (2.3c) at the black scalars preserves
`CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addMixedBlackRelationsQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (DoubleDiagram.addMixedBlackRelations (RDc) (redWeight Wgt) k (Sb).t P) :=
  hP.addRels fun a => coverRedNegligible_mixedBlackRelationQ Λ C hQ hc o ho a

/-- Adjoining the reflected black relations of `U_{Sb}(g)` preserves `CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addBlackRelationsQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (addBlackRelationsOf (RDc) (redWeight Wgt) (CLQ.pres (RDc) k (Sb)) P) :=
  hP.addRels fun r => coverRedNegligible_blackRelQ Λ C hQ hc o ho r

/-- Adjoining the black biadjunction and dot cyclicity relations preserves
`CoverRelsNegligible` (general parameters). -/
theorem CoverRelsNegligible.addBlackAdjunctionRelationsQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (DoubleDiagram.addBlackAdjunctionRelations (RDc) (redWeight Wgt) P) :=
  hP.addRels fun r => coverRedNegligible_blackAdjunctionQ Λ C hQ hc o ho P r

/-- Adjoining the cup pitchfork relations at the scalars `Sb.t` preserves
`CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addMixedCupPitchforkRelationsQ
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (DoubleDiagram.addMixedCupPitchforkRelations (RDc) (redWeight Wgt) P
        fun i j => ((Sb).t i j : k)) :=
  hP.addRels fun a => coverRedNegligible_mixedCupPitchforkQ Λ C hQ hc o ho P a

end Categorification.Stendhal
