/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownInjectiveOrdinary
import Categorification.WeightedKLR.RedStrands.DoubleCLDownwardBlockQ
import Categorification.WeightedKLR.RedStrands.DoubleCLDownInjective
import Categorification.WeightedKLR.RedStrands.DoubleWFDom
import Categorification.WeightedKLR.RedStrands.DoubleCLDownwardBlock
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverReflection
import Categorification.Diagrams.KL3.SymmetrySigmaMatrix
import Categorification.KLR.KKScalarsStandard
import Categorification.WeightedKLR.RedStrands.DoubleCapSurjectivity
import Categorification.WeightedKLR.RedStrands.DoubleDownCLComparison
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverDotCentral

/-!
# Injectivity of the map from `T^λ` to the downward block, for every Kang–Kashiwara family

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for every Kang–Kashiwara family `Q`
(no restriction to the Khovanov–Lauda parameters). The black strands of the downward block
carry the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`) at
the black scalars `Sb = blackScalarsQ`, the downward KLR relations use the Cautis–Lauda dual
parameters of `Sb`, which are `Q` on distinct colours (`clDownwardQ_blackScalarsQ`), and the
mixed black relations use `Sb.t`. The map `ordinaryToDownwardMatrix` from `T^λ` to the all-down
block is injective (`ordinaryToDownwardMatrix_injectiveQ`): an element of `T^λ` is detected by
the vacuum evaluations of the cyclotomic Cautis–Lauda action, and these factor through the
downward block.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp KLRAlgebra

universe u v w

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q} {ν : Multiset I}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
local notation "wt₀" => (blockWeight Wgt L 0 : I ⊕ Fin ℓ → ℤ)
local notation "RDc" => coordinateDatum Λ C
local notation "Sb" => blackScalarsQ Λ C hQ
local notation "μ" => stendhalWeight ℓ ν
local notation "rt" => downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν

section Main

/-- **Injectivity of the comparison with the downward block for every Kang–Kashiwara family**
(Webster, arXiv:1309.3796v3, Lemma 4.29, the injectivity of the map to the all-down block): the
black strands carry `U_Q(g)` at the black scalars `Sb`, and the downward relations use the
Cautis–Lauda dual parameters of `Sb`, which are `Q`. -/
theorem ordinaryToDownwardMatrix_injectiveQ (hc : CoverDotCentral Λ C Q)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom) :
    Function.Injective (ordinaryToDownwardMatrix (Λ := coordinateRedWeights Λ C)
      (signedCapPresentationOf (RDc) (redWeight Wgt) (CLQ.pres (RDc) k (Sb)) P
        (clDownwardQ (Sb)) Λ fun i j => ((Sb).t i j : k))
      (clDownwardQ (Sb)) Λ (Sb).t (ν := ν)) := by
  have ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
      ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) (blockWeight Wgt L 0) = 0 := by
    intro i
    simp [blockWeight, cyclotomicCoverHighest, cyclotomicCoverWeightDatum]
  have hP₁ := CoverRelsNegligible.downwardBlock_signedCapQ ho hP
  have hwf₁ := addRedUpRelations_wfDom (addMixedBlackRelations_wfDom (Sb).t
    (addDownRelations_wfDom (affineCoverQ (clDownwardQ (Sb)) Λ)
      (signedCapPresentationOf_wfDom (clDownwardQ (Sb)) Λ (fun i j => ((Sb).t i j : k))
        (𝔅 := CLQ.pres (RDc) k (Sb)) (fun r => CLQ.pres_dom_wfQ r) hwf)))
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := affineTensorProjection_surjective (Q := clDownwardQ (Sb)) Λ ν x
  obtain ⟨u, rfl⟩ := KLRAlgebra.mk_surjective y
  rw [tensorProjection_mk_eq_zero_iff (Q' := Q) Λ ν
    (fun a b h => clDownwardQ_blackScalarsQ Λ C hQ h) u,
    affineTensorProjection_mk Λ ν C u, ← cyclotomicCoverToTensor_hflip_eq_zero_iff,
    ← KLRAlgebra.sigma_sigma sym (KLRAlgebra.mk _ _ _ u)]
  refine projectedCoverVacuum_detects.{u, v, w} Λ ν C hQ _ fun t s => ?_
  have hν := blockWeight_stendhalWeight Λ C ν
  have hs' : wtop Wgt wt₀ μ = wt₀ - rt :=
    (blockWeight_wtop (RD := Wgt) (Λ := L) (h0 := rfl)).symm.trans hν
  have hup (t : Seq μ) : Cond (wt₀ - rt) wt₀ ((PCL).toObj ((upCover Λ C hQ wt₀ 0).obj
      (KLR.Diagram.ob (KLR.Diagram.word t.rev)))) := by
    change Cond _ _ (ob Wgt (wt₀ - 0) (ups (KLR.Diagram.word t.rev).reverse))
    rw [sub_zero, Categorification.KL3.Diagram.KSig.word_rev, List.reverse_reverse]
    exact hs' ▸ RouqFamily.cond_word wt₀ t
  by_cases hts : IsRedOrdered t.rev ∧ IsRedOrdered s.rev
  · obtain ⟨ht', hs''⟩ := hts
    have hmk : KLRAlgebra.mk k (affineCoverQ (clDownwardQ (Sb)) Λ) μ u =
        (KLR.Diagram.diagREquiv k _ μ).symm (fun a b => (KLR.Diagram.pres k _).lin
          (KLR.Diagram.freeDiagMat k μ u a b)) := by
      apply (KLR.Diagram.diagREquiv k _ μ).injective
      rw [AlgEquiv.apply_symm_apply, KLR.Diagram.diagREquiv_apply, KLR.Diagram.toDiagR_mk]
      funext a b
      exact (KLR.Diagram.lin_freeDiagMat _ u a b).symm
    rw [hmk] at hx
    have he := congrArg (fun M => M ⟨t.rev, ht'⟩ ⟨s.rev, hs''⟩) hx
    simp only [ordinaryToDownwardMatrix_raw_entries] at he
    have he2 := congrArg (downVacuumQuotientFunctor (ν := ν) hc hP₁ hwf₁).map he
    have : (downVacuumQuotientFunctor (ν := ν) hc hP₁ hwf₁).Additive := by
      unfold downVacuumQuotientFunctor; infer_instance
    replace he2 := he2.trans (Functor.map_zero _ _ _)
    change presentedVacuumEval hc hν hP₁ hwf₁ (cond_downBoundary _) (cond_downBoundary _) _ = 0
      at he2
    rw [InducedCategory.homMk_hom] at he2
    replace he2 := (presentedVacuumEval_castHom_eq_zero_iff hc hν hP₁ hwf₁ _ _ ?ha ?hb _ _ _).mp he2
    rotate_left
    · rw [downContextObj_word]
      exact cond_downBoundary (P := P) (downTriple _ _ ⟨t.rev, ht'⟩)
    · rw [downContextObj_word]
      exact cond_downBoundary (P := P) (downTriple _ _ ⟨s.rev, hs''⟩)
    change vacuumEval.{u, v, w} Λ C hQ ν hν _ _ (coverCL Λ C hQ wt₀
      (downLinear RDc (redWeight Wgt) k 0 [] [] _)) = 0 at he2
    rw [coverCL_downLinear] at he2
    exact (vacuumEval_upCover_freeDiagMat_eq_zero_iff hν u t s (hup t) (hup s)).mp
      ((vacuumEval_downCover_eq_zero_iff hc hν wt₀ 0 _ (Stendhal.ob_wf _) (Stendhal.ob_wf _) _ _
        (hup t) (hup s)).mp he2)
  · rw [← vacuumEval_upCover_freeDiagMat_eq_zero_iff hν u t s (hup t) (hup s)]
    rcases not_and_or.mp hts with h | h
    · refine vacuumEval_eq_zero_of_dom (e := wt₀ - 0) hν _ _ _ (KLR.Diagram.word t)
        ((isRedOrdered_ofList_word_rev_iff t).not.mpr h) ?_
      change (ob Wgt (wt₀ - 0) (ups (KLR.Diagram.word t.rev).reverse)).word = _
      rw [Categorification.KL3.Diagram.KSig.word_rev, List.reverse_reverse]
      rfl
    · refine vacuumEval_eq_zero_of_cod (e := wt₀ - 0) hν _ _ _ (KLR.Diagram.word s)
        ((isRedOrdered_ofList_word_rev_iff s).not.mpr h) ?_
      change (ob Wgt (wt₀ - 0) (ups (KLR.Diagram.word s.rev).reverse)).word = _
      rw [Categorification.KL3.Diagram.KSig.word_rev, List.reverse_reverse]
      rfl

end Main

end Categorification.Stendhal
