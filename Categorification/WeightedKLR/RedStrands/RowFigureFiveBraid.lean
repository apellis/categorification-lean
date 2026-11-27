/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RowFigureFiveLoading
import Categorification.WeightedKLR.RedStrands.BraidRowConcentrated
import Categorification.WeightedKLR.RedStrands.BraidRowStandard
import Categorification.WeightedKLR.RedStrands.RightRowStandardClass
import Categorification.WeightedKLR.RedStrands.BlockStackedStandard
import Categorification.WeightedKLR.RedStrands.BlockPartialStandardFiltration

/-!
# The braid of a right row standard module

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10, using Proposition 6.9.
For `n + 2 + m` red strands and words `u` with `u_{n+2}` empty, let `S(u)` be the right standard
module at the row loading `λ_1 u_1 ⋯ λ_{n+2+m} u_{n+2+m}` (`rightRowStandard`), and `π` the
transposition of `λ_{n+1}` and `λ_{n+2}`. Then the derived braid `𝔅_π S(u)` is concentrated in
degree zero (`braidConcentrated_rightRowStandard`), and `𝔅_π S(u)` is the standard module at the
row loading of the swapped words, relabelled by `π`, shifted by `⟨|u_{n+1}|, λ_{n+2}⟩ - 2` in
the auxiliary grading (`rightRowStandardBraidIso`).

`StackedStandard` holds at the row of `u` (`stackedStandard_rowFigureFive`, from
`stackedStandard_setPairLoading`). Braid concentration carries the injectivity hypothesis of
Lemma 6.8 at the row of `u` (`RowFigureFiveHypotheses`) and `AllFiniteDeltaInjective`; the
graded isomorphism carries none.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR RedBlock BraidedStendhalAlgebra Categorification.Graded DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {I : Type} {k : Type} [DecidableEq I] [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    {n m : ℕ} (Λ : Fin (n + 2 + m) → I →₀ ℕ)

/-- The spectators left of the distinguished pair, as red blocks. -/
abbrev rowL (u : Fin (n + 2 + m) → List I) : List (Fin (n + 2 + m) × Multiset I) :=
  (leftWords u).map wordSpec

/-- The spectators right of the distinguished pair, as red blocks. -/
abbrev rowM (u : Fin (n + 2 + m) → List I) : List (Fin (n + 2 + m) × Multiset I) :=
  (rightWords u).map wordSpec

/-- The black content of the distinguished pair. -/
abbrev rowβ (u : Fin (n + 2 + m) → List I) : Multiset I := (u (leftPos n m) : Multiset I)

/-- The crossed Figure 5 row loading of `u`. -/
abbrev rowCrossed (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    Seq (stendhalWeight (n + 2 + m) (blockContent u)) :=
  KLR.Seq.cast (weightSum_rowBlocks u hu) (place _ (setPairLoading (rowM u) (pairEmb n m) (rowβ u)
    (crossedLoading _) (rowL u) (rowBlockLoadings u (crossedLoading _))))

/-- **The route hypothesis of Lemma 6.8 at the row of `u`**: injectivity on the kernel of the
loading projective onto its partial standard module. It is an explicit hypothesis tracked for
removal; the filtration of that kernel by partial standards is proved
(`exists_hasFiltration_blockLoadingKernelAt`). -/
structure RowFigureFiveHypotheses (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (Λ : Fin (n + 2 + m) → I →₀ ℕ) (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    Prop where
  injective : ∀ s : Seq (stendhalWeight (n + 2 + m) (blockContent u)),
      redWord s = redWord (rowCrossed u hu) →
      Function.Injective (blockKernelTensorInclusion Q Λ s (pairEmb n m 0) (pairEmb n m 1)
        ((rowL u).map Prod.fst ++ pairEmb n m 0 :: pairEmb n m 1 :: (rowM u).map Prod.fst))

omit [DecidableEq I] in
theorem rowLoading_eq_rowCrossed (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    rowLoading (n + 2 + m) u = rowCrossed u hu := by
  rw [rowLoading_eq_place u hu, rowCrossed]
  congr 2
  exact (setPairLoading_rowLoadings _ _ _ _ _ _).symm

omit [DecidableEq I] in
theorem redWord_rowCrossed (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    redWord (rowCrossed u hu) =
      (rowL u).map Prod.fst ++ pairEmb n m 1 :: pairEmb n m 0 :: (rowM u).map Prod.fst := by
  rw [← rowLoading_eq_rowCrossed u hu, (redWord_eq_finRange_iff _).2 (isRedOrdered_rowLoading _ u)]
  exact finRange_eq_rowBlocks u

omit [DecidableEq I] in
theorem redWord_rowCrossed_eq_finRange (u : Fin (n + 2 + m) → List I)
    (hu : u (rightPos n m) = []) : redWord (rowCrossed u hu) = List.finRange (n + 2 + m) := by
  rw [← rowLoading_eq_rowCrossed u hu]
  exact (redWord_eq_finRange_iff _).2 (isRedOrdered_rowLoading _ u)

omit [DecidableEq I] in
theorem not_violated_rowCrossed (u : Fin (n + 2 + m) → List I) :
    ¬ Violated _ (setPairLoading (rowM u) (pairEmb n m) (rowβ u) (crossedLoading _) (rowL u)
      (rowBlockLoadings u (crossedLoading _))) := by
  have he : setPairLoading (rowM u) (pairEmb n m) (rowβ u) (crossedLoading _) (rowL u)
      (rowBlockLoadings u (crossedLoading _)) = rowBlockLoadings u (crossedLoading _) :=
    setPairLoading_rowLoadings _ _ _ _ _ _
  rw [he]
  exact not_violated_rowBlockLoadings u

theorem blackCount_uncrossedLoading (w : List I) (r : Fin 2) (i : I) :
    blackCount (uncrossedLoading w) r i = 0 := by
  rw [blackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hlt⟩
  fin_cases r
  · exact Nat.not_lt_zero _ (hlt _ (uncrossedLoading_lbl_zero w))
  · have h1 := hlt _ (uncrossedLoading_lbl_one w)
    have hx0 : x = ⟨0, by simp [stendhalWeight]⟩ := Fin.ext (Nat.lt_one_iff.1 h1)
    subst hx0
    rw [uncrossedLoading_lbl_zero] at hx
    exact Sum.inl_ne_inr hx.symm

omit [DecidableEq I] in
theorem not_isViolated_uncrossedLoading (w : List I) : ¬ IsViolated (uncrossedLoading w) :=
  not_isViolated_of_ofFn _ (by rw [uncrossedLoading, ofFn_seqOfList])

/-- **`StackedStandard` at the Figure 5 row** (Webster, arXiv:1309.3796v2, §6.1, Proposition
6.9): partial standardization of the local uncrossed standard module is the global standard
module at the row of `u`. -/
theorem stackedStandard_rowFigureFive (u : Fin (n + 2 + m) → List I)
    (hu : u (rightPos n m) = []) :
    StackedStandard hQ.klrSymm (weightSum_rowBlocks u hu) (rowRelations Q Λ hQ.klrSymm
      (rowM u) (pairEmb n m) (rowβ u)
      (tensorOfKLR Q (Λ ∘ pairEmb n m) (rowβ u) (KLRAlgebra.e (uncrossedLoading _)))
      (pairRelations Q Λ hQ.klrSymm (pairEmb n m) (rowβ u) (uncrossedLoading _)) (rowL u)
        (rowBlockLoadings u (crossedLoading _)))
      (setPairLoading (rowM u) (pairEmb n m) (rowβ u) (uncrossedLoading _) (rowL u)
        (rowBlockLoadings u (crossedLoading _))) :=
  stackedStandard_setPairLoading (hQ := hQ.klrSymm) (h := weightSum_rowBlocks u hu)
    (rowBlockLoadings u (crossedLoading _)) (uncrossedLoading _)
    ((redWord_uncrossedLoading _).trans (show [0, 1] = List.finRange 2 by decide))
    (blackCount_uncrossedLoading _)
    (not_violated_setPairLoading (rowM u) (pairEmb n m) (rowβ u) (crossedLoading _)
      (uncrossedLoading _) (not_isViolated_uncrossedLoading _) _ _ (not_violated_rowCrossed u))

/-- Braid concentration of a right standard module only depends on its loading. -/
theorem braidConcentrated_rightStandard_congr {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
    {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (hS : KLRSymm Q) (π : Equiv.Perm (Fin ℓ))
    {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)
    [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
    [DG.HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      (List.finRange ℓ)))ᵐᵒᵖ]
    [DG.HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      ((List.finRange ℓ).map π)))ᵐᵒᵖ]
    {t t' : Seq (stendhalWeight ℓ ν)} (h : t = t') (ht : redWord t = List.finRange ℓ)
    (ht' : redWord t' = List.finRange ℓ)
    (H : BraidConcentrated.{w} Λ ν hρ hS π hR (rightStandard hρ hS t (rouquierGrading Q hR Λ) ht)) :
    BraidConcentrated.{w} Λ ν hρ hS π hR (rightStandard hρ hS t' (rouquierGrading Q hR Λ) ht') := by
  subst h
  exact H

variable [∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- **The derived braid of a right row standard module is concentrated in degree zero**
(Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 and proof of Corollary 6.10): for words `u`
with `u_{n+2}` empty, `𝔅_π S(u)` has no cohomology outside degree zero, where `π` swaps
`λ_{n+1}` and `λ_{n+2}`. Route hypotheses: `AllFiniteDeltaInjective` (Lemma 5.19, for the
filtration of the partial standard kernel) and `RowFigureFiveHypotheses`, the injectivity
hypothesis of Lemma 6.8. -/
theorem braidConcentrated_rightRowStandard
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (u : Fin (n + 2 + m) → List I)
    (hu : u (rightPos n m) = []) (H : RowFigureFiveHypotheses C hQ Λ u hu)
    [DG.HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ
      (blockContent u) (List.finRange (n + 2 + m))))ᵐᵒᵖ]
    [DG.HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ
      (blockContent u) ((List.finRange (n + 2 + m)).map (pairSwap n m))))ᵐᵒᵖ] :
    BraidConcentrated.{w} Λ (blockContent u) (isReducedChoice_canChoice _) hQ.klrSymm
      (pairSwap n m) hQ (rightRowStandard C hQ Λ u) := by
  have key := braidConcentrated_rowStandard.{w} Q Λ hQ.klrSymm (rowM u) (pairEmb n m) (rowβ u) hQ
    (isReducedChoice_canChoice _) (one_lt_card_stendhalWeight_two _)
    (uncrossedLoading_lbl_zero _) (uncrossedLoading_lbl_one _) (edgeBraid_crossedLoading _)
    (redWord_crossedLoading _) (redWord_uncrossedLoading _) (rowL u) (weightSum_rowBlocks u hu)
    (rowBlockLoadings u (crossedLoading _)) (not_violated_rowCrossed u) (redWord_rowCrossed u hu)
    (stackedStandard_rowFigureFive C hQ Λ u hu) (isReducedChoice_canChoice _) (pairSwap n m)
    (finRange_eq_rowBlocks u)
    (map_pairSwap_finRange u)
    (fun s hs => exists_hasFiltration_blockLoadingKernelAt hQ.klrSymm hQ hall
      (show pairEmb n m 1 < pairEmb n m 0 from Fin.lt_def.2 (by simp))
      (redWord_rowCrossed_eq_finRange u hu) s hs) H.injective
  exact braidConcentrated_rightStandard_congr.{w} _ hQ.klrSymm _ hQ
    (rowLoading_eq_rowCrossed u hu).symm _ _ key

/-- A right standard module only depends on its loading. -/
theorem rightStandard_congr {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
    {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (hS : KLRSymm Q) (G : GradingDatum (stendhalQ Q Λ))
    [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
    {t t' : Seq (stendhalWeight ℓ ν)} (h : t = t') (ht : redWord t = List.finRange ℓ)
    (ht' : redWord t' = List.finRange ℓ) :
    rightStandard hρ hS t G ht = rightStandard hρ hS t' G ht' := by
  subst h
  rfl

omit [DecidableEq I] in
theorem redPerm_swappedRowLoading_eq (u : Fin (n + 2 + m) → List I)
    (hu : u (rightPos n m) = []) :
    Seq.redPerm (pairSwap n m) (swappedRowLoading u) = KLR.Seq.cast (weightSum_rowBlocks u hu)
      (place _ (setPairLoading (rowM u) (pairEmb n m) (rowβ u) (uncrossedLoading _) (rowL u)
        (rowBlockLoadings u (crossedLoading _)))) := by
  rw [redPerm_swappedRowLoading u hu]
  congr 2
  exact (setPairLoading_rowLoadings _ _ _ _ _ _).symm

/-- **The braid of a right row standard module, graded** (Webster, arXiv:1309.3796v2, §6.1,
Proposition 6.9 and proof of Corollary 6.10): for words `u` with `u_{n+2}` empty,
`𝔅_π S(u) ≅ S'⟨⟨|u_{n+1}|, λ_{n+2}⟩ - 2⟩` as graded right `T^{λ ∘ π}`-modules with the auxiliary
gradings, where `π` swaps `λ_{n+1}` and `λ_{n+2}` and `S'` is the right standard module at the row
loading of the swapped words. -/
def rightRowStandardBraidIso (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    (rightStandard (Λ := Λ ∘ pairSwap n m) (isReducedChoice_canChoice _) hQ.klrSymm
        (swappedRowLoading u) (rouquierGrading Q hQ (Λ ∘ pairSwap n m))
        (redWord_swappedRowLoading u)).Iso
      ((braidF C hQ Λ (pairSwap n m) (blockContent u) (rightRowStandard C hQ Λ u)).shift
        (-(Multiset.sum (Multiset.map (fun i => QuantumGroup.UDot.di C i *
          (Λ (rightPos n m) i : ℤ)) (u (leftPos n m) : Multiset I)) - 2))) := by
  rw [show rightRowStandard C hQ Λ u = rightStandard (isReducedChoice_canChoice _) hQ.klrSymm
      (rowCrossed u hu) (rouquierGrading Q hQ Λ)
      ((redWord_rowCrossed u hu).trans (finRange_eq_rowBlocks u).symm) from
    rightStandard_congr _ hQ.klrSymm _ (rowLoading_eq_rowCrossed u hu) _ _]
  exact rowBraidStandardIso Q Λ hQ.klrSymm (rowM u) (pairEmb n m) (rowβ u) hQ
    (isReducedChoice_canChoice _) (one_lt_card_stendhalWeight_two _)
    (uncrossedLoading_lbl_zero _) (uncrossedLoading_lbl_one _) (edgeBraid_crossedLoading _)
    (redWord_crossedLoading _) (redWord_uncrossedLoading _) (rowL u) (weightSum_rowBlocks u hu)
    (rowBlockLoadings u (crossedLoading _)) (not_violated_rowCrossed u) (redWord_rowCrossed u hu)
    (stackedStandard_rowFigureFive C hQ Λ u hu) (isReducedChoice_canChoice _) (pairSwap n m)
    (finRange_eq_rowBlocks u)
    (map_pairSwap_finRange u) (redWord_swappedRowLoading u) (redPerm_swappedRowLoading_eq u hu)

end Categorification.Stendhal.FirstWeight
