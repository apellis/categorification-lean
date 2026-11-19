/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedNegligibleIdeal
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverVacuumEvaluation

/-!
# The vacuum evaluation of the downward block

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The downward block acts on the
tensor-product algebra through the Cautis–Lauda action of the extended datum on its cyclotomic
weight spaces, evaluated at the Stendhal block and projected to the tensor-product algebra.
Red-negligible 2-morphisms vanish under this evaluation
(`CoverRed.project_eq_zero`), so the evaluation factors through the relations of the downward
block, all of whose reflected images are cover red-negligible.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram InductionAlong

universe u v w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} {hQ : IsRouquierQ C Q}
  {hc : CoverDotCentral Λ C Q}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)

/-- Each red colour occurs once in a Stendhal weight. -/
theorem count_inr_stendhalWeight (ν : Multiset I) (r : Fin ℓ) :
    (stendhalWeight ℓ ν).count (Sum.inr r) = 1 := by
  classical
  have hred : Multiset.count (Sum.inr r : I ⊕ Fin ℓ) (ν.map Sum.inl) = 0 :=
    Multiset.count_eq_zero_of_notMem (by simp)
  rw [stendhalWeight, Multiset.count_add, hred, zero_add, Multiset.count_map_eq_count'
    _ _ Sum.inr_injective]
  exact Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ r)

/-- **Red-negligible 2-morphisms vanish at the Stendhal block.** The component of a cover
red-negligible 2-morphism at a Stendhal block is killed by the projection to the
tensor-product algebra. -/
theorem CoverRed.project_eq_zero {s t : I ⊕ Fin ℓ → ℤ}
    {F F' : (cyclotomicFamily.{u, v, w} (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
      (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
      (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
      (cyclotomicCoverPolynomial_natDegree (k := k) Λ C)
      (IsRouquierQ.polyInY_degree_pair (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) Wgt)).model.lift.obj
        (fo t) ⟶ (cyclotomicFamily.{u, v, w}
      (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
      (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
      (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
      (cyclotomicCoverPolynomial_natDegree (k := k) Λ C)
      (IsRouquierQ.polyInY_degree_pair (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) Wgt)).model.lift.obj
        (fo s)} {θ : F ⟶ F'} (h : CoverRed.{u, v, w} Λ C hQ hc θ) (ν : Multiset I)
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) (M : (cyclotomicFamily.{u, v, w}
      (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
      (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
      (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
      (cyclotomicCoverPolynomial_natDegree (k := k) Λ C)
      (IsRouquierQ.polyInY_degree_pair (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) Wgt)).model.lift.obj
        (fo t)) :
    (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom
      (cyclotomicCoverToTensor (Q := Q) Λ ν C)))).map
        ((θ.hom.app M) ⟨stendhalWeight ℓ ν, hν⟩) = 0 := by
  have hb : RedBounded (Set.range Sum.inr) (stendhalWeight ℓ ν) := by
    rintro c ⟨r, rfl⟩
    rw [count_inr_stendhalWeight]
  exact cyclotomicCover_project_eq_zero_of_mem_negligible Λ ν C
    (fun c hc' => hc'.1) (h M ⟨stendhalWeight ℓ ν, hν⟩ hb)

end Categorification.Stendhal
