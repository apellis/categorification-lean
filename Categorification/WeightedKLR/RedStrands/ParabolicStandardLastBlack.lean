/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastSequence
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.BlackRestriction

/-!
# Standardization and the functor `E_i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Proposition
5.5. Write `θ = i + θ₀` and `β = i + β₀`. The idempotent `1_{-,i}` of `T(θ + β)` is the image,
under the identification of weights `i + (θ₀ + β) = θ + β`, of Webster's idempotent
`appendBlack 1` cutting out `E_i` (`castTensorProductAlgebra_appendBlack_one`). Hence the middle
term of the last-strand sequence of standardization is `E_i(S N)`, the restriction `BlackRes` of
`S N` viewed as a module over `T(i + (θ₀ + β))`, and there is a short exact sequence

`0 → S(₂E_i N) → E_i(S N) → S(₁E_i N) → 0`

of `k`-modules (`lastBlackResTwo_injective`, `lastBlackRes_exact`,
`lastBlackResOne_surjective`). Gradings are not modelled.

## Main definitions

* `LastStandardT`: standardization `S N` as a module over `T(i + (θ₀ + β))`.
* `lastBlackResEquiv`: `E_i(S N)` is the `1_{-,i}`-fixed part of `S N`.

## Main results

* `castTensorProductAlgebra_appendBlack_one`.
* `lastBlackResTwo_injective`, `lastBlackRes_exact`, `lastBlackResOne_surjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ₀ β₀ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "θ" => ((Si i) + θ₀)
local notation "β" => ((Si i) + β₀)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))

omit [DecidableEq I] in
/-- The weights `i + (θ₀ + β)` and `θ + β` agree. -/
theorem lastBlack_weight : (Si i) + (θ₀ + β) = θ + β := (add_assoc _ _ _).symm

omit [DecidableEq I] in
/-- The weight `ν₀ + i + ν₀'` of the KLR algebra before the last strand is that of `θ₀ + β`. -/
theorem lastBlack_klrWeight : Aₚ + {j} + Aₗ = stendhalWeight (ℓ + 1) (θ₀ + β) := by
  rw [← parabolicInputWeights_add (ℓ := ℓ) θ₀ β, ← lastWeight_addBlack (ℓ := ℓ) i β₀]
  ac_rfl

/-- **The idempotent `1_{-,i}` is Webster's `E_i` idempotent** `appendBlack 1` of
`T(i + (θ₀ + β))`, transported to `T(θ + β)`. -/
theorem castTensorProductAlgebra_appendBlack_one :
    castTensorProductAlgebra Q Λ (lastBlack_weight i θ₀ β₀) (appendBlack Q Λ i (θ₀ + β) 1) =
      lastBlackIdem Q Λ i θ₀ β₀ := by
  rw [appendBlack_one_eq_oneConcat, castTensorProductAlgebra_mk, lastBlackIdem, lastIdem,
    castKLR_castKLR, castKLR_castKLR, castKLR_castKLR]
  exact congrArg (tensorOfKLR Q Λ _)
    (castKLR_oneConcat_eq (lastBlack_klrWeight (ℓ := ℓ) i θ₀ β₀).symm _ _)

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  (hQ : KLRSymm Q)

/-- The action of `T(i + (θ₀ + β))` on standardization `S N`. -/
def lastStandardTAction :
    TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β)) →ₐ[k]
      Module.End k (ParabolicStandard Q Λ θ β N) :=
  (parabolicStandardAction Q Λ θ β N hQ).comp
    (castTensorProductAlgebra Q Λ (lastBlack_weight i θ₀ β₀)).toAlgHom

/-- Standardization `S N` viewed as a module over `T(i + (θ₀ + β))`. -/
def LastStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ β N

instance : AddCommGroup (LastStandardT Q Λ i θ₀ β₀ N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ β N))
instance : Module k (LastStandardT Q Λ i θ₀ β₀ N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β N))
instance : Module (TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β)))
    (LastStandardT Q Λ i θ₀ β₀ N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ β N) (lastStandardTAction Q Λ i θ₀ β₀ N hQ).toRingHom
instance : IsScalarTower k (TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β)))
    (LastStandardT Q Λ i θ₀ β₀ N hQ) :=
  ⟨fun c t m => by
    change lastStandardTAction Q Λ i θ₀ β₀ N hQ (c • t) m =
      c • lastStandardTAction Q Λ i θ₀ β₀ N hQ t m
    rw [map_smul]
    rfl⟩

theorem appendBlack_one_smul_lastStandardT (m : ParabolicStandard Q Λ θ β N) :
    (appendBlack Q Λ i (θ₀ + β) 1 • (show LastStandardT Q Λ i θ₀ β₀ N hQ from m) :
        ParabolicStandard Q Λ θ β N) =
      parabolicStandardAction Q Λ θ β N hQ (lastBlackIdem Q Λ i θ₀ β₀) m := by
  change parabolicStandardAction Q Λ θ β N hQ
    (castTensorProductAlgebra Q Λ (lastBlack_weight i θ₀ β₀) (appendBlack Q Λ i (θ₀ + β) 1)) m = _
  rw [castTensorProductAlgebra_appendBlack_one]

theorem mem_lastStandardFixed_iff (m : ParabolicStandard Q Λ θ β N) :
    m ∈ LastStandardFixed Q Λ i θ₀ β₀ N hQ ↔
      parabolicStandardAction Q Λ θ β N hQ (lastBlackIdem Q Λ i θ₀ β₀) m = m := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]

/-- **`E_i(S N)` is the `1_{-,i}`-fixed part of `S N`.** -/
def lastBlackResEquiv :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ) ≃ₗ[k]
      LastStandardFixed Q Λ i θ₀ β₀ N hQ where
  toFun m := ⟨show ParabolicStandard Q Λ θ β N from m.1,
    (mem_lastStandardFixed_iff Q Λ i θ₀ β₀ N hQ _).2
      ((appendBlack_one_smul_lastStandardT Q Λ i θ₀ β₀ N hQ m.1).symm.trans m.2)⟩
  invFun m := ⟨show LastStandardT Q Λ i θ₀ β₀ N hQ from m.1,
    (appendBlack_one_smul_lastStandardT Q Λ i θ₀ β₀ N hQ m.1).trans
      ((mem_lastStandardFixed_iff Q Λ i θ₀ β₀ N hQ _).1 m.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

local notation "Er" => LastResRight Q Λ i θ₀ β₀ N
local notation "El" => LastResLeft Q Λ i θ₀ β₀ N

/-- **The inclusion** `S(₂E_i N) → E_i(S N)`. -/
def lastBlackResTwo :
    ParabolicStandard Q Λ θ β₀ Er →ₗ[k]
      BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ) :=
  (lastBlackResEquiv Q Λ i θ₀ β₀ N hQ).symm.toLinearMap ∘ₗ lastFixedTwo Q Λ i θ₀ β₀ N hQ

/-- **The projection** `E_i(S N) → S(₁E_i N)`. -/
def lastBlackResOne :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ) →ₗ[k]
      ParabolicStandard Q Λ θ₀ β El :=
  lastFixedOne Q Λ i θ₀ β₀ N hQ ∘ₗ (lastBlackResEquiv Q Λ i θ₀ β₀ N hQ).toLinearMap

theorem lastBlackResTwo_injective : Function.Injective (lastBlackResTwo Q Λ i θ₀ β₀ N hQ) :=
  (lastBlackResEquiv Q Λ i θ₀ β₀ N hQ).symm.injective.comp
    (lastFixedTwo_injective Q Λ i θ₀ β₀ N hQ)

theorem lastBlackResOne_surjective : Function.Surjective (lastBlackResOne Q Λ i θ₀ β₀ N hQ) :=
  (lastFixedOne_surjective Q Λ i θ₀ β₀ N hQ).comp
    (lastBlackResEquiv Q Λ i θ₀ β₀ N hQ).surjective

/-- **Webster, Prop 5.5, `E`-part:** for `θ = i + θ₀`, `β = i + β₀` the sequence
`0 → S(₂E_i N) → E_i(S N) → S(₁E_i N) → 0` is exact. -/
theorem lastBlackRes_exact :
    Function.Exact (lastBlackResTwo Q Λ i θ₀ β₀ N hQ) (lastBlackResOne Q Λ i θ₀ β₀ N hQ) :=
  (lastFixed_exact Q Λ i θ₀ β₀ N hQ).conj_linearEquiv (LinearEquiv.refl k _)
    (lastBlackResEquiv Q Λ i θ₀ β₀ N hQ).symm (LinearEquiv.refl k _)

end Categorification.Stendhal
