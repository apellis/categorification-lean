/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendIdentity
import Categorification.WeightedKLR.RedStrands.BraidedStandardGrading

set_option backward.isDefEq.respectTransparency false

/-!
# Appending a black strand preserves the auxiliary degree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Proposition 6.7. Appending a straight black strand at the right of a braided diagram
(`appendBlackAlg`) and of its class modulo violated idempotents (`appendViol`) preserves the
auxiliary grading induced by a KLR grading datum, since a straight strand has degree zero.

## Main results

* `appendBlackAlg_mem_auxiliaryGrade`
* `appendViol_mem_violAuxiliaryGrade`
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv Categorification.Graded

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} (i : I) {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

/-- Appending a black strand preserves the auxiliary degree of braided diagrams. -/
theorem appendBlackAlg_mem_auxiliaryGrade {d : ℤ} {x : BraidedStendhalAlgebra k Q Λ ν}
    (hx : x ∈ auxiliaryGrade (ν := ν) G d) :
    appendBlackAlg Q Λ i ν x ∈ auxiliaryGrade (ν := νᵢ) G d := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  change appendBlackAlg Q Λ i ν (ofKLR k Q Λ ν a) ∈ _
  rw [appendBlackAlg_ofKLR]
  apply Graded.mem_map_of_mem
  have h1 := G.concat_tmul_mem_grade (ν' := ({Sum.inl i} : Multiset (I ⊕ Fin ℓ))) ha
    (SetLike.GradedOne.one_mem (A := G.grade _))
  rw [add_zero] at h1
  exact G.castKLR_mem_grade _ h1

/-- Appending a black strand preserves the auxiliary degree modulo violated idempotents. -/
theorem appendViol_mem_violAuxiliaryGrade {d : ℤ} {x : ViolQuotient k Q Λ ν}
    (hx : x ∈ violAuxiliaryGrade (ν := ν) G d) :
    appendViol Q Λ i ν x ∈ violAuxiliaryGrade (ν := νᵢ) G d := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  change appendViol Q Λ i ν (violMk k Q Λ ν a) ∈ _
  rw [appendViol_violMk]
  exact Graded.mem_map_of_mem _ _ (appendBlackAlg_mem_auxiliaryGrade i G ha)

end Categorification.Stendhal.BraidedStendhalAlgebra
