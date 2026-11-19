/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackNegligible
import Categorification.WeightedKLR.RedStrands.DoubleDownContextIdeal
import Categorification.WeightedKLR.RedStrands.DoubleCLRepeatedRedCover

/-!
# Downward KLR relations under the cover functor

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The downward KLR relations of
`addDownRelations`, placed in arbitrary signed contexts, are cover red-negligible as soon as
their translations in the empty context are (`coverRedNegligible_downRelation_of_empty`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "RDc" => coordinateDatum Λ C

variable (o : I ⊕ Fin ℓ → ℤ) (Qd : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

/-- **Reduction to the empty context.** If the downward translations of the KLR relations in
the empty signed context are cover red-negligible for every left region, so are their
whiskered translations in every signed context. -/
theorem coverRedNegligible_downRelation_of_empty
    (hempty : ∀ (μ : I ⊕ Fin ℓ → ℤ) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)),
      CoverRedNegligible.{u, v, w} Λ C hQ hc
        (coverCL Λ C hQ o (downLinear (RDc) (redWeight Wgt) k μ [] []
          (KLR.Diagram.relation k Qd r))))
    (μ : I ⊕ Fin ℓ → ℤ) (u' v' : List (DoubleStrand I ℓ)) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ))
    (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) (b : List (I ⊕ Fin ℓ)) (h : r.dom.WhiskerOK a b) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (downLinear (RDc) (redWeight Wgt) k μ u' v'
        (LinDiagram.whisker (KLR.Diagram.relation k Qd r) a b h))) :=
  coverRedNegligible_of_mem_ideal Λ C hQ hc o (emptyDownPres (RDc) (redWeight Wgt) k Qd)
    (emptyDownPres_wfDom (RDc) (redWeight Wgt) k Qd) (fun i _ => hempty i.1 i.2)
    (downLinear_whisker_relation_mem_ideal (RDc) (redWeight Wgt) k Qd μ u' v' r a b h)

omit [DecidableEq I] in
theorem map_snd_colours {X : Type*} [AddCommGroup X] {Y : Type*} [AddCommGroup Y]
    (RD : WeightDatum C X Y) (Λ' : Fin ℓ → X) (μ : X) (w : List (DoubleStrand I ℓ)) :
    (colours RD Λ' μ w).map Prod.snd = w := by
  induction w generalizing μ with
  | nil => rfl
  | cons a w ih => simp [colours, ih]

/-- **A double diagram into a word with a red strand of one colour twice is cover
red-negligible.** Red strands are reflected to upward red strands. -/
theorem coverRedNegligible_of_count_red {x : Obj (signature (RDc) (redWeight Wgt))}
    {ν : I ⊕ Fin ℓ → ℤ} {w : List (DoubleStrand I ℓ)}
    (f : LinDiagram k x (obj (RDc) (redWeight Wgt) ν w)) (s : Fin ℓ)
    (h : 2 ≤ w.countP (· = .inr s)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o f) := by
  refine coverRedNegligible_of_repeated_red Λ C hQ hc _ s ?_ ?_
  · change 2 ≤ (((colours (RDc) (redWeight Wgt) ν w).map (coverColour o)).reverse).countP _
    rw [List.countP_reverse, List.countP_map]
    have e : ∀ c : (I ⊕ Fin ℓ → ℤ) × DoubleStrand I ℓ,
        (decide ((coverColour o c).l = (true, Sum.inr s))) =
          (decide (c.2 = Sum.inr s)) := by
      rintro ⟨_, (⟨_, _⟩ | _)⟩ <;> simp [coverColour, coverLetter]
    have : (colours (RDc) (redWeight Wgt) ν w).countP
        (fun c => decide ((coverColour o c).l = (true, Sum.inr s))) =
        ((colours (RDc) (redWeight Wgt) ν w).map Prod.snd).countP (· = Sum.inr s) := by
      rw [List.countP_map]; exact List.countP_congr fun c _ => by simpa using e c
    rw [Function.comp_def, this, map_snd_colours]
    exact h
  · intro col hcol
    change col ∈ ((colours (RDc) (redWeight Wgt) ν w).map (coverColour o)).reverse at hcol
    obtain ⟨⟨_, (⟨_, _⟩ | _)⟩, _, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hcol) <;>
      simp [coverColour, coverLetter]

end Categorification.Stendhal
