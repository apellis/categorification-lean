/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastStrand
import Categorification.KLR.IndCast

/-!
# The parabolic shuffle module as an induced module with a last black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For `θ = i + θ₀` and `β = i + β₀`, the weights of the two tensor factors of
parabolic induction are `ν₀ + i` and `ν₀' + i`, but only up to an equality of multisets. The
module `LastInput` is the input module viewed over `R(ν₀ + i) ⊗ R(ν₀' + i)`, and
`lastShuffleEquiv` identifies its induced module with the parabolic shuffle module. Under this
identification the red-ordered idempotent is the idempotent cutting out standardization.

## Main results

* `lastShuffleEquiv`, `lastShuffleEquiv_smul`;
* `castKLR_eSum_redOrderedSet_eq_parabolicOrderedLoadings`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ₀ β₀ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "hA" => prefixWeight_addBlack (ℓ := ℓ) i θ₀
local notation "hD" => lastWeight_addBlack (ℓ := ℓ) i β₀

omit [DecidableEq I] in
/-- The weights `ν₀ + i + ν₀' + i` of the two factors with their last black strands, equal to
the weight of parabolic induction for `θ = i + θ₀`, `β = i + β₀`. -/
theorem lastShuffle_weight :
    Aₚ + {Sum.inl i} + (Aₗ + {Sum.inl i}) =
      Multiset.map (addRedColor ℓ) (stendhalWeight ℓ ((Si i) + θ₀)) +
        Multiset.map lastColour (stendhalWeight 1 ((Si i) + β₀)) :=
  add_eq_add_of_eq hA hD

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]

/-- The input module of parabolic induction, viewed over `R(ν₀ + i) ⊗ R(ν₀' + i)`. -/
def LastInput := ParabolicInput Q Λ ((Si i) + θ₀) ((Si i) + β₀) N

local notation "N₁" => LastInput Q Λ i θ₀ β₀ N
local notation "N₀" => ParabolicInput Q Λ ((Si i) + θ₀) ((Si i) + β₀) N

instance : AddCommGroup N₁ := inferInstanceAs (AddCommGroup N₀)
instance : Module k N₁ := inferInstanceAs (Module k N₀)
instance : Module (TensorKLR S (Aₚ + {Sum.inl i}) (Aₗ + {Sum.inl i})) N₁ :=
  Module.compHom N₀ (castTensor S hA hD).toRingEquiv.toRingHom
instance : IsScalarTower k (TensorKLR S (Aₚ + {Sum.inl i}) (Aₗ + {Sum.inl i})) N₁ :=
  ⟨fun c t n => by
    change castTensor S hA hD (c • t) • (show N₀ from n) =
      c • (castTensor S hA hD t • (show N₀ from n))
    rw [map_smul, smul_assoc]⟩

/-- `LastInput` is the input module. -/
def lastInputEquiv : N₁ ≃ₗ[k] N₀ := LinearEquiv.refl k N₀

/-- **The parabolic shuffle module as an induced module from `R(ν₀ + i) ⊗ R(ν₀' + i)`.** -/
def lastShuffleEquiv :
    Ind S (Aₚ + {Sum.inl i}) (Aₗ + {Sum.inl i}) N₁ ≃ₗ[k]
      ParabolicShuffle Q Λ ((Si i) + θ₀) ((Si i) + β₀) N :=
  indCast hA hD (lastInputEquiv Q Λ i θ₀ β₀ N) fun _ _ => rfl

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
/-- `lastShuffleEquiv` is semilinear along the transport of weights. -/
theorem lastShuffleEquiv_smul (a : KLRAlgebra k S (Aₚ + {Sum.inl i} + (Aₗ + {Sum.inl i})))
    (y : Ind S (Aₚ + {Sum.inl i}) (Aₗ + {Sum.inl i}) N₁) :
    lastShuffleEquiv Q Λ i θ₀ β₀ N (a • y) =
      castKLR S (lastShuffle_weight i θ₀ β₀) a • lastShuffleEquiv Q Λ i θ₀ β₀ N y :=
  indCast_smul (h := hA) (h' := hD) (g := lastInputEquiv Q Λ i θ₀ β₀ N) (hg := fun _ _ => rfl) a y

omit [DecidableEq I] in
/-- The red-ordered loadings of parabolic induction. -/
theorem parabolicOrderedLoadings_eq_redOrderedSet (θ β : Multiset I) :
    parabolicOrderedLoadings (ℓ := ℓ) θ β = redOrderedSet _ := by
  ext s
  simp [parabolicOrderedLoadings, mem_redOrderedSet]

/-- **The red-ordered idempotent is the standardization idempotent.** -/
theorem castKLR_eSum_redOrderedSet_eq_parabolicOrderedLoadings :
    castKLR S (lastShuffle_weight i θ₀ β₀)
        (eSum S (redOrderedSet (Aₚ + {Sum.inl i} + (Aₗ + {Sum.inl i})))) =
      eSum S (parabolicOrderedLoadings (ℓ := ℓ) ((Si i) + θ₀) ((Si i) + β₀)) := by
  rw [castKLR_eSum_redOrderedSet, parabolicOrderedLoadings_eq_redOrderedSet]

end Categorification.Stendhal
