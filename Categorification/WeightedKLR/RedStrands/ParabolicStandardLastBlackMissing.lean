/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastLeft
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndMap
import Categorification.WeightedKLR.RedStrands.LastStrandPieceDimension

/-!
# The `E`-part of standardization when the colour is missing from a block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For a module `N` over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)`, let `S N` be its
standardization, a module over `T(θ + β)`. The piece of `S N` on which the last strand is black
of colour `i` (`lastStrandIdem (some i)`) is `E_i(S N)`. When `i` occurs in both blocks, its
dimension is `dim S(₁E_i N) + dim S(₂E_i N)`
(`finrank_fixSub_lastStrandIdem_parabolicStandardT_eq`). This file records the remaining cases
in dimension form, where one or both terms vanish.

* `finrank_fixSub_lastStrandIdem_parabolicStandardT_left`: for `θ = i + θ₀` and `i ∉ β`,
  `dim E_i(S N) = dim S(₁E_i N)` (from `leftBlackResEquiv`);
* `finrank_fixSub_lastStrandIdem_parabolicStandardT_right`: for `β = i + β₀` and `i ∉ θ`,
  `dim E_i(S N) = dim S(₂E_i N)` (from `rightBlackResEquiv`);
* `lastStrandIdem_some_eq_zero`, `finrank_fixSub_lastStrandIdem_some_eq_zero`: for `i ∉ ν`,
  the idempotent `1_{-,i}` of `T(ν)` is zero and so is the corresponding piece of every module;
  in particular `finrank_fixSub_lastStrandIdem_parabolicStandardT_of_notMem` for `i ∉ θ + β`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Absent

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

/-- **No last black strand of an absent colour**: for `i ∉ ν` the idempotent of `T(ν)`
selecting the loadings whose last strand is black of colour `i` is zero. -/
theorem lastStrandIdem_some_eq_zero {i : I} (hi : i ∉ ν) :
    lastStrandIdem Q Λ ν (some i) = 0 := by
  have hempty : (Finset.univ.filter fun s : Seq (stendhalWeight (ℓ + 1) ν) =>
      lastBlackColour ν s = some i) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun s _ hs => hi ?_
    have hm := Seq.mem s (lastRedPosition ℓ ν)
    simp only [lastBlackColour] at hs
    rcases hc : s.1 (lastRedPosition ℓ ν) with c | r
    · rw [hc] at hs hm
      cases hs
      simpa [stendhalWeight] using hm
    · rw [hc] at hs; cases hs
  rw [lastStrandIdem, hempty]
  simp [eSum, tensorOfKLR]

/-- For `i ∉ ν`, the piece of a `T(ν)`-module on which the last strand is black of colour `i`
is zero. -/
theorem finrank_fixSub_lastStrandIdem_some_eq_zero {i : I} (hi : i ∉ ν)
    (Y : Type*) [AddCommGroup Y] [Module k Y] [Module (TensorProductAlgebra k Q Λ ν) Y]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ν) Y] :
    Module.finrank k (fixSub k Y (lastStrandIdem Q Λ ν (some i))) = 0 := by
  have : Subsingleton (fixSub k Y (lastStrandIdem Q Λ ν (some i))) := by
    refine ⟨fun ⟨y, hy⟩ ⟨z, hz⟩ => Subtype.ext ?_⟩
    change y = z
    rw [mem_fixSub, lastStrandIdem_some_eq_zero Q Λ ν hi, zero_smul] at hy hz
    rw [← hy, ← hz]
  exact Module.finrank_zero_of_subsingleton

end Absent

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)

local notation "Si" j => (Singleton.singleton j : Multiset I)

/-- The scalar tower `k → T(θ + β) → S N` (a local instance). -/
local instance parabolicStandardT_isScalarTower_missing (hQ : KLRSymm Q) (θ' β' : Multiset I)
    (M : Type*) [AddCommGroup M] [Module k M] [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] :
    IsScalarTower k (TensorProductAlgebra k Q Λ (θ' + β'))
      (ParabolicStandardT Q Λ θ' β' M hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ' β' M hQ) c t) y⟩

section Left

variable (θ₀ β : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  (hQ : KLRSymm Q)

/-- **Webster, Prop 5.5, `E`-part, `i ∉ β`, in dimension form** (arXiv:1309.3796v3, proof of
Proposition 5.5): for `θ = i + θ₀` and `i ∉ β`, `dim E_i(S N) = dim S(₁E_i N)`. -/
theorem finrank_blackRes_leftStandardT_eq (hi : i ∉ β) :
    Module.finrank k
        (BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ)) =
      Module.finrank k (ParabolicStandard Q Λ θ₀ β (LeftResLeft Q Λ i θ₀ β N)) :=
  (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).finrank_eq

/-- **The black-last piece of `S N`, `i ∉ β`** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): for `θ = i + θ₀` and `i ∉ β`, the piece of `S N` over `T(θ + β)` whose
last strand is black of colour `i` has dimension `dim S(₁E_i N)`. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_left (hi : i ∉ β) :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ ((Si i) + θ₀) β N hQ)
        (lastStrandIdem Q Λ ((Si i) + θ₀ + β) (some i))) =
      Module.finrank k (ParabolicStandard Q Λ θ₀ β (LeftResLeft Q Λ i θ₀ β N)) := by
  rw [lastStrandIdem_some Q Λ ((Si i) + θ₀ + β) i (θ₀ + β) (leftBlack_weight i θ₀ β),
    ← finrank_blackRes_leftStandardT_eq Q Λ i θ₀ β N hQ hi]
  rfl

end Left

section Right

variable (θ β₀ : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  (hQ : KLRSymm Q)

/-- **Webster, Prop 5.5, `E`-part, `i ∉ θ`, in dimension form** (arXiv:1309.3796v3, proof of
Proposition 5.5): for `β = i + β₀` and `i ∉ θ`, `dim E_i(S N) = dim S(₂E_i N)`. -/
theorem finrank_blackRes_rightStandardT_eq (hi : i ∉ θ) :
    Module.finrank k
        (BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ)) =
      Module.finrank k (ParabolicStandard Q Λ θ β₀ (RightResRight Q Λ i θ β₀ N)) :=
  (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).finrank_eq

/-- **The black-last piece of `S N`, `i ∉ θ`** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): for `β = i + β₀` and `i ∉ θ`, the piece of `S N` over `T(θ + β)` whose
last strand is black of colour `i` has dimension `dim S(₂E_i N)`. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_right (hi : i ∉ θ) :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ θ ((Si i) + β₀) N hQ)
        (lastStrandIdem Q Λ (θ + ((Si i) + β₀)) (some i))) =
      Module.finrank k (ParabolicStandard Q Λ θ β₀ (RightResRight Q Λ i θ β₀ N)) := by
  rw [lastStrandIdem_some Q Λ (θ + ((Si i) + β₀)) i (θ + β₀) (rightBlack_weight i θ β₀),
    ← finrank_blackRes_rightStandardT_eq Q Λ i θ β₀ N hQ hi]
  rfl

end Right

section Neither

variable (θ β : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (hQ : KLRSymm Q)

/-- **The black-last piece of `S N`, `i ∉ θ + β`** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): if `i` occurs in neither block, the piece of `S N` whose last strand is
black of colour `i` is zero. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_of_notMem (hi : i ∉ θ + β) :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ θ β N hQ)
        (lastStrandIdem Q Λ (θ + β) (some i))) = 0 :=
  finrank_fixSub_lastStrandIdem_some_eq_zero Q Λ (θ + β) hi _

end Neither

end Categorification.Stendhal
