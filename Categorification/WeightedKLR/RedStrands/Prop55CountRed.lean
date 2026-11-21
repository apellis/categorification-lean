/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndShortExact
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastRedVanish

/-!
# The last-red piece in the dimension count of Proposition 5.5

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. The dimension count splits each of `S(₁Fᵢ N)`, `Fᵢ S(N)` and
`S(₂Fᵢ N)` according to the last strand. This file treats the summand cut out by the
idempotent `e_ℓ` whose last strand is the red strand `λ_ℓ`.

## Main results

* `lastRedIdem_smul_lastIndStandardT`: `e_ℓ` kills `S(₂Fᵢ N)`.
* `lastRedIdem_smul_firstIndStandardT`, `lastRedIdem_smul_firstIndF`: if `β ≠ 0`, `e_ℓ` kills
  `S(₁Fᵢ N)` and `Fᵢ S(N)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + β))

omit [Field k] in
/-- The cast between Stendhal algebras of equal weights preserves `e_ℓ`. -/
theorem castTensorProductAlgebra_lastRedIdem {k : Type*} [CommRing k]
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν ν' : Multiset I}
    (h : ν = ν') :
    castTensorProductAlgebra Q Λ h (TensorProductAlgebra.lastRedIdem Q Λ ν) =
      TensorProductAlgebra.lastRedIdem Q Λ ν' := by
  subst h; rfl

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- **`e_ℓ` kills `S(₂Fᵢ N)`**: its last block `i + β` is nonempty. -/
theorem lastRedIdem_smul_lastIndStandardT (y : LastIndStandardT Q Λ i θ β N hQ) :
    TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)) • y = 0 := by
  change parabolicStandardAction Q Λ θ ((Si i) + β) (LastIndRight Q Λ i θ β N) hQ
    (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β) _) y = 0
  rw [castTensorProductAlgebra_lastRedIdem]
  exact lastRedIdem_smul_parabolicStandardT Q Λ θ ((Si i) + β) (LastIndRight Q Λ i θ β N) hQ
    (by simp) y

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- **`e_ℓ` kills `S(₁Fᵢ N)` when `β ≠ 0`.** -/
theorem lastRedIdem_smul_firstIndStandardT (hβ : β ≠ 0)
    (y : FirstIndStandardT Q Λ i θ β N hQ) :
    TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)) • y = 0 := by
  change parabolicStandardAction Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ
    (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β) _) y = 0
  rw [castTensorProductAlgebra_lastRedIdem]
  exact lastRedIdem_smul_parabolicStandardT Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ
    hβ y

/-- **`e_ℓ` kills `Fᵢ S(N)` when `β ≠ 0`**, by right exactness of
`S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N)`. -/
theorem lastRedIdem_smul_firstIndF (hβ : β ≠ 0) (y : FirstIndF Q Λ i θ β N hQ) :
    TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β)) • y = 0 := by
  set e := TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + β))
  have he : IsIdempotentElem e := TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ _
  have hg : lastIndQuotientMap Q Λ i θ β N hQ (e • y) = 0 := by
    rw [map_smul]
    exact lastRedIdem_smul_lastIndStandardT Q Λ i θ β N hQ _
  obtain ⟨x, hx⟩ := (firstIndDeltaT_exact Q Λ i θ β N hQ (e • y)).mp hg
  have : e • y = e • (e • y) := by rw [← mul_smul, he.eq]
  rw [this, ← hx, ← map_smul, lastRedIdem_smul_firstIndStandardT Q Λ i θ β N hQ hβ, map_zero]

end Categorification.Stendhal
