/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardizedResolution
import Categorification.WeightedKLR.RedStrands.LastRedStandardCut
import Categorification.Algebra.Graded.UpResolutionHead

/-!
# Simple heads of standard modules in `C↑`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 5.28 (step for several red strands). The simple module at a cut `θ + β` with factor
class `b` is the head of the standardization `S(b)`: it is a subquotient of `S(b)`
(`exists_headAtCut_isUngradedSubquotient`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra Categorification.Graded DirectSum GProj
open scoped TensorProduct Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)

local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "𝓓" => tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)

/-- The top of a factor class, as a finite graded module. -/
def factorTop (b : IndecClass 𝓓) (hb : FiniteDimensional k b.top) : GFin 𝓓 :=
  { toGMod := b.top
    finiteDimensional := hb }

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
include hR

/-- The head of the standardization of a factor class at its cut is a subquotient of it. -/
theorem exists_headAtCut_isUngradedSubquotient (b : IndecClass 𝓓)
    (hb : FiniteDimensional k b.top) :
    ∃ s, HeadAtCut Λ (θ+β) G ⟨(θ,β),rfl⟩ b s ∧
      GFin.IsUngradedSubquotient T s.top
        (standardizationGFin Λ G θ β hsym (factorTop Λ G θ β b hb)).carrier := by
  obtain ⟨s, hs, X, g, hg, hgq⟩ := exists_headAtCut_subquotient Λ (θ+β) G hR ⟨(θ,β),rfl⟩ b
    (lastRedStandardInducedCut Λ G hsym θ β b)
  refine ⟨s, hs, ⟨{ carrier := (X : Set (lastRedStandardInducedCut Λ G hsym θ β b).carrier)
                    add_mem' := X.add_mem
                    zero_mem' := X.zero_mem
                    smul_mem' := fun t _ hx => X.smul_mem ((smallerSuffixIdeal Q Λ
                      (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)).ringCon.mkₐ k t) hx },
    { toFun := fun x => g ⟨x.1, x.2⟩
      map_add' := fun x y => map_add g ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_smul' := fun t x => hgq t ⟨x.1, x.2⟩ }, fun y => ?_⟩⟩
  obtain ⟨x, rfl⟩ := hg y
  exact ⟨⟨x.1, x.2⟩, rfl⟩

end Categorification.Stendhal
