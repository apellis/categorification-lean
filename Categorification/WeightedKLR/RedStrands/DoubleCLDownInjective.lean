/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLVacuumUpWords
import Categorification.WeightedKLR.RedStrands.DoubleCLVacuumViolated
import Categorification.WeightedKLR.RedStrands.DoubleCLDownUpVacuum
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Categorification.WeightedKLR.RedStrands.TensorProjectionParameters
import Categorification.Diagrams.KL3.FreeDiagMat

/-!
# Injectivity of the comparison with the downward block

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong

universe u v w v₁

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  [DecidableEq I] {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
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

section Generic

omit [DecidableEq I] in
theorem matEndMap_entry {𝒞 𝒟 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] [Category 𝒟]
    [Preadditive 𝒟] [Linear k 𝒟] {ι : Type*} [Fintype ι] [DecidableEq ι] (F : 𝒞 ⥤ 𝒟)
    [F.Additive] [F.Linear k] (Z : ι → 𝒞) (M : KLR.Diagram.MatEnd Z) (i j : ι) :
    matEndMap k F Z M i j = F.map (M i j) := rfl

/-- The vacuum evaluation does not depend on the name of the left region. -/
theorem vacuumEval_eq_zero_iff_region {s s' : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    (hν' : blockWeight Wgt L (stendhalWeight ℓ ν) = s') {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (ha' : Cond s' wt₀ c) (hb' : Cond s' wt₀ d)
    (φ : (PCL).obj c ⟶ (PCL).obj d) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = 0 ↔
      vacuumEval.{u, v, w} Λ C hQ ν hν' ha' hb' φ = 0 := by
  subst hν hν'
  rfl

/-- Conjugating by identifications of objects does not change whether the vacuum evaluation
vanishes. -/
theorem vacuumEval_eqToHom_conj_eq_zero_iff {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c c' d d' : Obj (psig Wgt)}
    (e₁ : (PCL).obj c' = (PCL).obj c) (e₂ : (PCL).obj d = (PCL).obj d')
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (ha' : Cond s wt₀ c') (hb' : Cond s wt₀ d')
    (φ : (PCL).obj c ⟶ (PCL).obj d) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha' hb' (eqToHom e₁ ≫ φ ≫ eqToHom e₂) = 0 ↔
      vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = 0 := by
  obtain rfl := (PCL).obj_injective e₁
  obtain rfl := (PCL).obj_injective e₂
  simp

omit [Field k] [DecidableEq I] in
theorem ob_wf (l : List (I ⊕ Fin ℓ)) : (KLR.Diagram.ob l).WF := by
  change (KLR.Diagram.sig (I ⊕ Fin ℓ)).ok () l
  induction l with
  | nil => trivial
  | cons _ _ ih => exact ⟨rfl, ih⟩

/-- Retyping a morphism of a presentation along equalities of its boundaries does not change
whether its vacuum evaluation vanishes. -/
theorem presentedVacuumEval_castHom_eq_zero_iff (hc : CoverDotCentral Λ C Q)
    {s : I ⊕ Fin ℓ → ℤ} (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom)
    {a a' b b' : Obj (signature (coordinateDatum Λ C) (redWeight Wgt))}
    (h₁ : a = a') (h₂ : b = b') (ha : Cond s wt₀ (coverObj a)) (hb : Cond s wt₀ (coverObj b))
    (ha' : Cond s wt₀ (coverObj a')) (hb' : Cond s wt₀ (coverObj b'))
    (f : P.obj a ⟶ P.obj b) :
    presentedVacuumEval.{u, v, w} hc hν hP hwf ha' hb' (P.castHom h₁ h₂ f) = 0 ↔
      presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb f = 0 := by
  subst h₁ h₂
  rw [Presentation.castHom_rfl]

theorem vacuumEval_eq_of_sub_eq_zero {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) {φ ψ : (PCL).obj c ⟶ (PCL).obj d}
    (h : vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (φ - ψ) = 0) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = vacuumEval.{u, v, w} Λ C hQ ν hν ha hb ψ := by
  have h' := vacuumEval_add (hQ := hQ) hν ha hb (φ - ψ) ψ
  rwa [sub_add_cancel, h, zero_add] at h'

/-- **Downward and upward KLR diagrams have the same vacuum evaluation up to negligible
terms.** -/
theorem vacuumEval_downCover_eq_zero_iff (hc : CoverDotCentral Λ C Q) {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) (o μ : I ⊕ Fin ℓ → ℤ)
    {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : LinDiagram k a b) (hwa : a.WF) (hwb : b.WF)
    (ha : Cond s wt₀ ((PCL).toObj ((downCover Λ C hQ o μ).obj a)))
    (hb : Cond s wt₀ ((PCL).toObj ((downCover Λ C hQ o μ).obj b)))
    (ha' : Cond s wt₀ ((PCL).toObj ((upCover Λ C hQ o μ).obj a)))
    (hb' : Cond s wt₀ ((PCL).toObj ((upCover Λ C hQ o μ).obj b))) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb ((freeLift k (downCover Λ C hQ o μ)).map f) = 0 ↔
      vacuumEval.{u, v, w} Λ C hQ ν hν ha' hb' ((freeLift k (upCover Λ C hQ o μ)).map f) = 0 := by
  have hn := vacuumNegligible_downCover_sub_upCover Λ C hQ hc ν o μ f hwa hwb hν ha hb
  rw [vacuumEval_eq_of_sub_eq_zero hν ha hb hn]
  exact vacuumEval_eqToHom_conj_eq_zero_iff hν _ _ ha' hb' ha hb _

/-- The vacuum evaluation of a diagram on upward strands does not depend on how the rightmost
region is written. -/
theorem vacuumEval_upFunctorC_eq_zero_iff {m m' : I ⊕ Fin ℓ → ℤ} (hm : m = m')
    {s : I ⊕ Fin ℓ → ℤ} (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    {x y : (KLR.Diagram.pres k (CL.qCL Sc)).Presented} (g : x ⟶ y)
    (ha : Cond s wt₀ ((PCL).toObj
      ((CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) m).obj x)))
    (hb : Cond s wt₀ ((PCL).toObj
      ((CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) m).obj y)))
    (ha' : Cond s wt₀ ((PCL).toObj
      ((CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) m').obj x)))
    (hb' : Cond s wt₀ ((PCL).toObj
      ((CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) m').obj y))) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb
        ((CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) m).map g) = 0 ↔
      vacuumEval.{u, v, w} Λ C hQ ν hν ha' hb'
        ((CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) m').map g) = 0 := by
  subst hm
  rfl

/-- **Upward entries of the reflected diagram.** -/
theorem vacuumEval_upCover_freeDiagMat_eq_zero_iff {s₁ : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s₁)
    (a : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν))) (t s : Seq (stendhalWeight ℓ ν))
    (ha : Cond s₁ wt₀ ((PCL).toObj
      ((upCover Λ C hQ wt₀ 0).obj (KLR.Diagram.ob (KLR.Diagram.word t.rev)))))
    (hb : Cond s₁ wt₀ ((PCL).toObj
      ((upCover Λ C hQ wt₀ 0).obj (KLR.Diagram.ob (KLR.Diagram.word s.rev))))) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb ((freeLift k (upCover Λ C hQ wt₀ 0)).map
        (KLR.Diagram.freeDiagMat k _ a t.rev s.rev)) = 0 ↔
      projectedCoverVacuumEntry.{u, v, w} Λ ν C hQ
        (KLRAlgebra.sigma sym (KLRAlgebra.mk k (cyclotomicCoverQ C Λ Q) _ a)) t s = 0 := by
  rw [← vacuumEval_ksMat_eq_zero_iff]
  unfold upCover
  rw [freeLift_comp_map]
  have e : (freeLift k (KSig.ksFree (CL.qCL Sc))).map
      (KLR.Diagram.freeDiagMat k _ a t.rev s.rev) =
      (KSig.ksP (CL.qCL Sc) (fun a b _ => (CL.rename_swap_qCL Sc b a).symm)).map
        (KLR.Diagram.toDiagFree k (CL.qCL Sc) _ a t.rev s.rev) := by
    rw [← KLR.Diagram.lin_freeDiagMat]
    rfl
  have ha'' : Cond s₁ wt₀ ((PCL).toObj ((CL.upFunctorC PCL (CL.qCL Sc)
      (presCL_cover_klr Λ C hQ) wt₀).obj
        ((KSig.ksFree (CL.qCL Sc)).obj (KLR.Diagram.ob (KLR.Diagram.word t.rev))))) := by
    have h := ha
    unfold upCover at h
    rw [sub_zero] at h
    exact h
  have hb'' : Cond s₁ wt₀ ((PCL).toObj ((CL.upFunctorC PCL (CL.qCL Sc)
      (presCL_cover_klr Λ C hQ) wt₀).obj
        ((KSig.ksFree (CL.qCL Sc)).obj (KLR.Diagram.ob (KLR.Diagram.word s.rev))))) := by
    have h := hb
    unfold upCover at h
    rw [sub_zero] at h
    exact h
  rw [e]
  rw [matEndMap_entry, KSig.ksMat, matEndReindex_apply]
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  have hs : wtop Wgt wt₀ (stendhalWeight ℓ ν) = s₁ :=
    (blockWeight_wtop (RD := Wgt) (Λ := L) (μ := wt₀) rfl).symm.trans hν
  have hta : Cond s₁ wt₀ (ob Wgt wt₀ (ups (KLR.Diagram.word t))) :=
    hs ▸ RouqFamily.cond_word wt₀ t
  have htb : Cond s₁ wt₀ (ob Wgt wt₀ (ups (KLR.Diagram.word s))) :=
    hs ▸ RouqFamily.cond_word wt₀ s
  refine (vacuumEval_upFunctorC_eq_zero_iff (sub_zero _) hν _ ha hb ha'' hb'').trans ?_
  refine Iff.trans ?_ (vacuumEval_eq_zero_iff_region hν (blockWeight_wtop rfl) hta htb
    (RouqFamily.cond_word wt₀ t) (RouqFamily.cond_word wt₀ s) _)
  exact (vacuumEval_eqToHom_conj_eq_zero_iff hν _ _ ha'' hb'' hta htb _).symm

end Generic

end Categorification.Stendhal
