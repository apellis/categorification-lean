/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleFarLeftBlackCut
import Categorification.WeightedKLR.RedStrands.DoubleSignedBubbleSweep
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleRedCutBubbles

/-!
# Evaluation of a signed bubble sweep in the violating quotient

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28. After moving a
bubble to the far left, the violating quotient reduces it to a scalar.
The resulting span of dot diagrams is preserved under composition with
arbitrary exterior diagrams and subsequent linear evaluation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k]

local notation "lab" => (Subtype.val ∘ weights)
local notation "K" => pres RD k
local notation "B" => DoubleStrand I ℓ

section Projection

variable (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ weights)) k)
  (kl : ∀ j : (pres RD k).Rel, P.lin (blackMirrorLinear RD (Subtype.val ∘ weights) ((pres RD k).rel j)) = 0)
  {η : X} (b : BoundaryCategory (Λ := weights) P η)
local notation "V" => violatingFunctor P η
local notation "Bd" => BoundaryCategory (Λ := weights) P η

local notation "bw" => DoubleBoundary.word (Subtype.val b)
local notation "cut" => blackCutHom RD lab P kl 0
local notation "ev" => signedDg RD lab P 0 bw bw
local notation "endB" => End (P.obj (obj RD lab 0 bw))

/-- Scalar evaluation at the far-left cut commutes with pre- and
post-composition and with linear evaluation after projection. -/
theorem farLeftBlackCut_exterior_scalar {M : Type*} [AddCommGroup M] [Module k M]
    (a c : Bd) (pre : (V).obj a ⟶ (V).obj b) (post : (V).obj b ⟶ (V).obj c)
    (eval : ((V).obj a ⟶ (V).obj c) →ₗ[k] M)
    (β : End ((K).obj (ob RD (endWeight RD lab 0 []) []))) :
    ∃ r : k, ∀ f : endB,
      eval (pre ≫ cutProjection P b (f ≫ cut [] bw bw rfl β) ≫ post) =
        r • eval (pre ≫ cutProjection P b f ≫ post) := by
  obtain ⟨r, hr⟩ := farLeftBlackCut_comp_scalar P kl b β
  exact ⟨r, fun f => by rw [hr, Linear.smul_comp, Linear.comp_smul, map_smul]⟩

/-- Scalar evaluation also commutes with exterior morphisms in the signed
presentation, after projecting their composite to the violating quotient. -/
theorem farLeftBlackCut_project_comp_scalar {M : Type*} [AddCommGroup M] [Module k M]
    (a c : Bd) (pre : a ⟶ b) (post : b ⟶ c)
    (eval : ((V).obj a ⟶ (V).obj c) →ₗ[k] M)
    (β : End ((K).obj (ob RD (endWeight RD lab 0 []) []))) :
    ∃ r : k, ∀ f : endB,
      eval ((V).map (pre ≫ InducedCategory.homMk (X := b) (Y := b)
        (f ≫ cut [] bw bw rfl β) ≫ post)) =
      r • eval ((V).map (pre ≫ InducedCategory.homMk (X := b) (Y := b) f ≫ post)) := by
  obtain ⟨r, hr⟩ := farLeftBlackCut_exterior_scalar P kl b a c ((V).map pre) ((V).map post) eval β
  refine ⟨r, fun f => ?_⟩
  simp only [Functor.map_comp]
  exact hr f

/-- At any cut of a signed boundary, bubble insertion lies in the span of
signed dot diagrams in the violating quotient. -/
theorem cutProjection_mem_signedDotSpan
    (hred : RedBubbleSlidesLeft RD lab P kl 0 bw)
    (L R : List B) (hw : L ++ R = bw)
    (β : End ((K).obj (ob RD (endWeight RD lab 0 L) [])))
    (hβ : IsBub RD k (endWeight RD lab 0 L) β) :
    cutProjection P b (cut L R bw hw β) ∈ Submodule.span k
      {g | ∃ A, signedChain bw A bw ∧ (∀ x ∈ A, IsBlackDotLayer x) ∧
        g = cutProjection P b (ev A)} :=
  blackCutHom_project_mem_signedDotSpan RD lab P kl 0 bw (cutProjection P b) hred
    (fun γ _ => farLeftBlackCut_comp_scalar P kl b γ) L R hw β hβ

/-- The bubble exit for arbitrary exterior morphisms and linear evaluation
on the resulting Hom of the violating quotient. -/
theorem cutProjection_exterior_mem_signedDotSpan {M : Type*} [AddCommGroup M] [Module k M]
    (hred : RedBubbleSlidesLeft RD lab P kl 0 bw)
    (a c : Bd) (pre : (V).obj a ⟶ (V).obj b) (post : (V).obj b ⟶ (V).obj c)
    (eval : ((V).obj a ⟶ (V).obj c) →ₗ[k] M)
    (L R : List B) (hw : L ++ R = bw)
    (β : End ((K).obj (ob RD (endWeight RD lab 0 L) [])))
    (hβ : IsBub RD k (endWeight RD lab 0 L) β) :
    eval (pre ≫ cutProjection P b (cut L R bw hw β) ≫ post) ∈ Submodule.span k
      {g | ∃ A, signedChain bw A bw ∧ (∀ x ∈ A, IsBlackDotLayer x) ∧
        g = eval (pre ≫ cutProjection P b (ev A) ≫ post)} := by
  let E : endB →ₗ[k] M := eval.comp
    ((Linear.leftComp k ((V).obj c) pre).comp
      ((Linear.rightComp k ((V).obj b) post).comp (cutProjection P b)))
  exact blackCutHom_project_mem_signedDotSpan RD lab P kl 0 bw E hred
    (fun γ _ => farLeftBlackCut_exterior_scalar P kl b a c pre post eval γ) L R hw β hβ

end Projection

section SignedCap

variable (RD : WeightDatum C X Y) (labels : Fin ℓ → X)
  (P : Presentation.{w, max u v} (signature RD labels) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)

local notation "Cap" => signedCapKLPresentation RD labels P Q exponents t
local notation "KLCap" => signedCapKL_reflectedBlack RD labels P Q exponents t
local notation "N" => addDownRelations RD labels (affineCoverQ Q exponents)
    (addRedUpRelations RD labels k (addRedCapRelations RD labels (addRedCupRelations RD labels
      (addBlackKLRelations RD labels (addRedUpSlideRelations RD labels P)))))

private theorem normalizedBubble_ideal_le_signedCapKL (a b : Obj (signature RD labels)) :
    (N).ideal a b ≤ (Cap).ideal a b := by
  apply ((N).relationsHold_iff_ideal_le (Cap)).mp ?_ a b
  intro j
  rcases j with ((((((j | j) | j) | j) | j) | j) | j)
  · exact (Cap).lin_rel_self (.inr (.inl (.inl (.inl (.inl (.inl j))))))
  · exact (Cap).lin_rel_self (.inl (.inl (.inl (.inl (.inl (.inl (.inr j)))))))
  · exact (Cap).lin_rel_self (.inr (.inl (.inl (.inl (.inl (.inr j))))))
  · exact (Cap).lin_rel_self (.inr (.inl (.inl (.inl (.inr j)))))
  · exact (Cap).lin_rel_self (.inr (.inl (.inl (.inr j))))
  · exact (Cap).lin_rel_self (.inr (.inl (.inr j)))
  · exact (Cap).lin_rel_self (.inr (.inr j))

/-- The common signed cap presentation contains all the red bubble slides
needed by the leftward sweep. -/
theorem signedCapKL_redBubbleSlidesLeft (μ : X) (W : List B)
    (hshift : ∀ r i, (exponents r i : ℤ) = ip RD i (labels r)) :
    RedBubbleSlidesLeft RD labels (Cap) (KLCap) μ W :=
  redBubbleSlidesLeft_of_ideal_le RD labels P μ W Q exponents (Cap)
    (normalizedBubble_ideal_le_signedCapKL RD labels P Q exponents t) (KLCap) hshift

end SignedCap

end Categorification.Stendhal.DoubleDiagram
