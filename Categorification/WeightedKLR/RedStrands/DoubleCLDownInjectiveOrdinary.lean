/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# Injectivity of the map from `T^λ` to the downward block

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, at the standard Khovanov–Lauda black
parameters. With the downward KLR relations at the Cautis–Lauda dual parameters (the repair of
Lemma 4.29 recorded in the README), the map `ordinaryToDownwardMatrix` from Webster's `T^λ` to
the all-down block is injective (`ordinaryToDownwardMatrix_clDownward_injective`): an element of
`T^λ` is detected by the vacuum evaluations of the cyclotomic Cautis–Lauda action, and these
factor through the downward block.
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
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "μ" => stendhalWeight ℓ ν
local notation "rt" => downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν

/-- Red-orderedness of a reversed sequence is read off from its word. -/
theorem isRedOrdered_ofList_word_rev_iff (t : Seq μ) :
    IsRedOrdered (Seq.ofList (KLR.Diagram.word t) rfl).rev ↔ IsRedOrdered t.rev := by
  have hm : Multiset.card (↑(KLR.Diagram.word t) : Multiset (I ⊕ Fin ℓ)) =
      Multiset.card μ := by simp
  have hl (a : Fin (Multiset.card μ)) :
      (Seq.ofList (KLR.Diagram.word t) rfl).rev.lbl (Fin.cast hm.symm a) = t.rev.lbl a := by
    simp only [Seq.lbl, Seq.rev_apply]
    rw [← Seq.lbl, Seq.ofList_lbl, KLR.Diagram.getElem_word]
    exact congrArg _ (Fin.ext (by simp))
  constructor
  · intro H a b r r' hab ha hb
    exact H (Fin.cast hm.symm a) (Fin.cast hm.symm b) r r' hab ((hl a).trans ha) ((hl b).trans hb)
  · intro H a b r r' hab ha hb
    refine H (Fin.cast hm a) (Fin.cast hm b) r r' hab ?_ ?_
    · rw [← hl]; exact ha
    · rw [← hl]; exact hb

section Main

/-- **Injectivity of the comparison with the downward block** (Webster, arXiv:1309.3796v3,
Lemma 4.29, the injectivity of the map to the all-down block, at the standard Khovanov–Lauda
black parameters and with the Cautis–Lauda dual downward parameters). -/
theorem ordinaryToDownwardMatrix_clDownward_injective (hc : CoverDotCentral Λ C Q)
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom) :
    Function.Injective (ordinaryToDownwardMatrix (Λ := coordinateRedWeights Λ C)
      (signedCapKLPresentation (RDc) (redWeight Wgt) P (clDownwardQ KL) Λ fun _ _ => 1)
      (clDownwardQ KL) Λ (KL).t (ν := ν)) := by
  have ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
      ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) (blockWeight Wgt L 0) = 0 := by
    intro i
    simp [blockWeight, cyclotomicCoverHighest, cyclotomicCoverWeightDatum]
  have hstd' (i j : I) : Sum.inl (β := Fin ℓ) i ≠ Sum.inl j →
      cyclotomicCoverQ C Λ Q (Sum.inl i) (Sum.inl j) =
        CL.qCL (CL.CLScalars.kl : CL.CLScalars (extendedCartanDatum C Λ) k)
          (Sum.inl i) (Sum.inl j) :=
    fun h => hstd i j fun e => h (congrArg Sum.inl e)
  have ht : ∀ i j : I, (Sc).t (Sum.inl i) (Sum.inl j) = 1 := fun i j =>
    KLR.kkScalars_t_eq_one _ _ (hstd' i j)
  have hs : ∀ (i j : I) (p q : ℕ), p < C.dij i j → q < C.dij j i →
      (Sc).s (Sum.inl i) (Sum.inl j) p q = 0 := fun i j _ _ hp hq =>
    KLR.kkScalars_s_eq_zero_of_kl _ _ (hstd' i j) hp hq
  have hP₁ := CoverRelsNegligible.downwardBlock_signedCapKL ho ht hs hstd hP
  have hwf₁ := addRedUpRelations_wfDom (addMixedBlackRelations_wfDom (KL).t
    (addDownRelations_wfDom (affineCoverQ (clDownwardQ KL) Λ)
      (signedCapKLPresentation_wfDom hwf (clDownwardQ KL) Λ fun _ _ => 1)))
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := affineTensorProjection_surjective (Q := clDownwardQ KL) Λ ν x
  obtain ⟨u, rfl⟩ := KLRAlgebra.mk_surjective y
  rw [tensorProjection_mk_eq_zero_iff (Q' := Q) Λ ν
    (fun a b h => (clDownwardQ_kl (C := C) (k := k) a b).trans (hstd a b h).symm) u,
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
    have hmk : KLRAlgebra.mk k (affineCoverQ (clDownwardQ KL) Λ) μ u =
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

/-- **Injectivity of the repaired comparison of arXiv:1309.3796v3, Lemma 4.29**, at the
standard Khovanov–Lauda parameters: `clToDownwardMatrix` is the crossing rescaling, an
isomorphism, followed by `ordinaryToDownwardMatrix` at the Cautis–Lauda dual parameters. -/
theorem clToDownwardMatrix_kl_injective (hc : CoverDotCentral Λ C Q)
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom) :
    Function.Injective (clToDownwardMatrix (Λ := coordinateRedWeights Λ C)
      (signedCapKLPresentation (RDc) (redWeight Wgt) P (clDownwardQ KL) Λ fun _ _ => 1)
      Λ (KL).t KL (ν := ν)) :=
  (ordinaryToDownwardMatrix_clDownward_injective hc hstd hP hwf).comp
    (AlgEquiv.injective _)

/-- **Webster, arXiv:1309.3796v3, Lemma 4.29, repaired**, at the standard Khovanov–Lauda
parameters over a field: the comparison `clToDownwardMatrix`, from `T^λ` to the all-down
block whose downward relations use the Cautis–Lauda dual parameters, is bijective. -/
theorem clToDownwardMatrix_kl_bijective (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P) (hwf : P.WFDom) :
    Function.Bijective (clToDownwardMatrix (Λ := coordinateRedWeights Λ C)
      (signedCapKLPresentation (RDc) (redWeight Wgt) P (clDownwardQ KL) Λ fun _ _ => 1)
      Λ (KL).t KL (ν := ν)) := by
  refine ⟨clToDownwardMatrix_kl_injective _ hstd hP hwf, ?_⟩
  have hsurj := DoubleDiagram.signedCapKL_ordinaryToDownwardMatrix_surjective
    (weights := coordinateRedWeights Λ C) (ν := ν) P (clDownwardQ KL) Λ (fun _ _ => 1) (KL).t
    fun r i => (coordinateRedWeights_pair Λ C r i).symm
  exact hsurj.comp (AlgEquiv.surjective _)

/-- The algebra isomorphism of the repaired Lemma 4.29 (arXiv:1309.3796v3) between `T^λ` and
the all-down block, at the standard Khovanov–Lauda parameters over a field. -/
noncomputable def clToDownwardMatrixKLEquiv (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ) wt₀ P) (hwf : P.WFDom) :=
  AlgEquiv.ofBijective _ (clToDownwardMatrix_kl_bijective (ν := ν) hstd hP hwf)

end Main

end Categorification.Stendhal
