/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55CountRed
import Categorification.WeightedKLR.RedStrands.Prop55CountRedEmpty

/-!
# The last-red piece of the dimension count of Proposition 5.5, any `β`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. The count compares `Fᵢ S(N)` with `S(₁Fᵢ N)` and `S(₂Fᵢ N)`
summand by summand according to the last strand. On the summand cut out by the idempotent
`e_ℓ` whose last strand is the red strand `λ_ℓ`, the count holds for every `β`: when `β = ∅`
the pieces of `Fᵢ S(N)` and `S(₁Fᵢ N)` agree, and when `β ≠ ∅` all three pieces vanish; the
piece of `S(₂Fᵢ N)` always vanishes.

## Main results

* `finrank_lastRed_firstIndF_eq_add`: the `e_ℓ`-piece of `Fᵢ S(N)` has dimension the sum of
  the dimensions of the `e_ℓ`-pieces of `S(₁Fᵢ N)` and `S(₂Fᵢ N)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The fixed vectors of an element acting by zero form the zero space. -/
theorem finrank_fixSub_eq_zero_of_smul {K : Type*} [CommRing K] [Nontrivial K]
    {A : Type*} [Ring A] [Algebra K A] {Y : Type*} [AddCommGroup Y] [Module K Y] [Module A Y]
    [IsScalarTower K A Y] (e : A) (he : ∀ y : Y, e • y = 0) :
    Module.finrank K (fixSub K Y e) = 0 := by
  have : fixSub K Y e = ⊥ := by
    ext y
    simp only [Submodule.mem_bot]
    constructor
    · intro hy
      have h : e • y = y := hy
      rw [← h, he]
    · rintro rfl
      exact (mem_fixSub (k := K)).2 (smul_zero e)
  rw [this, finrank_bot]

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [Field k]
  {C : QuantumGroup.CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)

section TowerLast

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (hQ : KLRSymm Q)

instance lastIndStandardT_isScalarTower :
    IsScalarTower k (TensorProductAlgebra k Q Λ ((Si i) + (θ + β)))
      (LastIndStandardT Q Λ i θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul ((parabolicStandardAction Q Λ θ ((Si i) + β)
    (LastIndRight Q Λ i θ β N) hQ).comp
      (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).toAlgHom) c t) y⟩

end TowerLast

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (hQ : KLRSymm Q)

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- The `e_ℓ`-piece of `S(₂Fᵢ N)` is zero. -/
theorem finrank_lastRed_lastIndStandardT :
    Module.finrank k (fixSub k (LastIndStandardT Q Λ i θ β N hQ)
      (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)))) = 0 :=
  finrank_fixSub_eq_zero_of_smul _ (lastRedIdem_smul_lastIndStandardT Q Λ i θ β N hQ)

/-- **The last-red piece of the dimension count of Proposition 5.5** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.5): for every `β`,
`dim e_ℓ Fᵢ S(N) = dim e_ℓ S(₁Fᵢ N) + dim e_ℓ S(₂Fᵢ N)`. -/
theorem finrank_lastRed_firstIndF_eq_add (hR : IsRouquierQ C Q) :
    Module.finrank k (fixSub k (FirstIndF Q Λ i θ β N hQ)
        (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)))) =
      Module.finrank k (fixSub k (FirstIndStandardT Q Λ i θ β N hQ)
          (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)))) +
        Module.finrank k (fixSub k (LastIndStandardT Q Λ i θ β N hQ)
          (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)))) := by
  rw [finrank_lastRed_lastIndStandardT, add_zero]
  by_cases hβ : β = 0
  · subst hβ
    exact finrank_lastRed_firstIndF_eq Q Λ i θ N hQ hR
  · rw [finrank_fixSub_eq_zero_of_smul _ (lastRedIdem_smul_firstIndF Q Λ i θ β N hQ hβ),
      finrank_fixSub_eq_zero_of_smul _ (lastRedIdem_smul_firstIndStandardT Q Λ i θ β N hQ hβ)]

end Categorification.Stendhal
