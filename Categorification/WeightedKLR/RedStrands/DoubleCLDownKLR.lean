/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackNegligible
import Categorification.WeightedKLR.RedStrands.DoubleDownContextIdeal

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

end Categorification.Stendhal
