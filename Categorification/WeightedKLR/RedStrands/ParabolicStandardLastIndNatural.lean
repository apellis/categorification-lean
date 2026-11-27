/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndShortExact
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact
import Categorification.WeightedKLR.RedStrands.TwoPieceRootStandard
import Categorification.Algebra.InductionAlongTensorFactorAction

/-!
# Naturality of the last-strand sequence of `Fᵢ(S N)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For a map `g : N → N'` of modules over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)`, the
maps `δ₁ : S(₁Fᵢ N) → Fᵢ(S N)` and `Fᵢ(S N) → S(₂Fᵢ N)` commute with the maps induced by `g`
(`firstIndDeltaT_natural`, `lastIndQuotientMap_natural`). This carries an extra commuting
action on `N` through the sequence in the induction on the number of red strands.

## Main definitions

* `lastIndFMap`: `Fᵢ(S g)`.
* `firstIndStandardMap`, `lastIndStandardMap`: `S(₁Fᵢ g)` and `S(₂Fᵢ g)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)
  {N N' : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'] (hQ : KLRSymm Q)
  (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N')

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + β))

/-- **`Fᵢ(S g)`.** -/
def lastIndFMap : LastIndF Q Λ i θ β N hQ →ₗ[T′] LastIndF Q Λ i θ β N' hQ :=
  Ind.map (parabolicStandardMapT Q Λ hQ g)

@[simp] theorem lastIndFMap_tmul (z : Corner (appendBlackHom Q Λ i θ β))
    (m : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndFMap Q Λ i θ β hQ g (Ind.tmul z m) =
      Ind.tmul z (parabolicStandardMapT Q Λ hQ g m) := rfl

/-- **`₁Fᵢ g`.** -/
abbrev firstIndLeftHom :
    FirstIndLeft Q Λ i θ β N →ₗ[parabolicFactorAlgebra Q Λ ((Si i) + θ) β]
      FirstIndLeft Q Λ i θ β N' :=
  IndK.map g

/-- **`₂Fᵢ g`.** -/
abbrev lastIndRightHom :
    LastIndRight Q Λ i θ β N →ₗ[parabolicFactorAlgebra Q Λ θ ((Si i) + β)]
      LastIndRight Q Λ i θ β N' :=
  IndK.map g

/-- **`S(₁Fᵢ g)`** over `T(i + (θ + β))`. -/
def firstIndStandardMap :
    FirstIndStandardT Q Λ i θ β N hQ →ₗ[T′] FirstIndStandardT Q Λ i θ β N' hQ where
  toFun := parabolicStandardMap Q Λ ((Si i) + θ) β (firstIndLeftHom Q Λ i θ β g)
  map_add' := map_add _
  map_smul' _ z := parabolicStandardMap_action Q Λ ((Si i) + θ) β hQ
    (firstIndLeftHom Q Λ i θ β g) _ z

/-- **`S(₂Fᵢ g)`** over `T(i + (θ + β))`. -/
def lastIndStandardMap :
    LastIndStandardT Q Λ i θ β N hQ →ₗ[T′] LastIndStandardT Q Λ i θ β N' hQ where
  toFun := parabolicStandardMap Q Λ θ ((Si i) + β) (lastIndRightHom Q Λ i θ β g)
  map_add' := map_add _
  map_smul' _ z := parabolicStandardMap_action Q Λ θ ((Si i) + β) hQ
    (lastIndRightHom Q Λ i θ β g) _ z

/-- `S N → S(₂Fᵢ N)` is natural. -/
theorem lastIndStandard_natural (m : ParabolicStandard Q Λ θ β N) :
    lastIndStandard Q Λ i θ β N' (parabolicStandardMap Q Λ θ β g m) =
      parabolicStandardMap Q Λ θ ((Si i) + β) (lastIndRightHom Q Λ i θ β g)
        (lastIndStandard Q Λ i θ β N m) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ m
  refine congrArg (Submodule.mkQ _) ?_
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- **`Fᵢ(S N) → S(₂Fᵢ N)` is natural.** -/
theorem lastIndQuotientMap_natural (x : LastIndF Q Λ i θ β N hQ) :
    lastIndQuotientMap Q Λ i θ β N' hQ (lastIndFMap Q Λ i θ β hQ g x) =
      lastIndStandardMap Q Λ i θ β hQ g (lastIndQuotientMap Q Λ i θ β N hQ x) := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero]
  | tmul z m =>
    rw [lastIndFMap_tmul, lastIndQuotientMap_tmul, lastIndQuotientMap_tmul, map_smul]
    exact congrArg (z.1 • ·) (lastIndStandard_natural Q Λ i θ β g m)
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add (lastIndQuotientMap Q Λ i θ β N hQ),
      map_add (lastIndStandardMap Q Λ i θ β hQ g)]

section First

local notation "T₁" => TensorProductAlgebra k Q Λ (((Si i) + θ) + β)
local notation "p₁" => LastRedWeightSplit.position (((Si i) + θ) + β) (firstIndSplit i θ β) ℓ
local notation "I₁" => smallerSuffixIdeal Q Λ p₁

/-- `Fᵢ(S g)` on `F_i(S N)` with its `k`-module structure. -/
abbrev firstIndFMap : FirstIndF Q Λ i θ β N hQ →ₗ[T′] FirstIndF Q Λ i θ β N' hQ :=
  lastIndFMap Q Λ i θ β hQ g

theorem firstIndFMap_action (a : T₁) (x : FirstIndF Q Λ i θ β N hQ) :
    firstIndFMap Q Λ i θ β hQ g (firstIndAction Q Λ i θ β N hQ a x) =
      firstIndAction Q Λ i θ β N' hQ a (firstIndFMap Q Λ i θ β hQ g x) :=
  (firstIndFMap Q Λ i θ β hQ g).map_smul _ x

theorem firstIndFMap_layerAction (c : (I₁).ringCon.Quotient) (x : FirstIndF Q Λ i θ β N hQ) :
    firstIndFMap Q Λ i θ β hQ g (firstIndLayerAction Q Λ i θ β N hQ c x) =
      firstIndLayerAction Q Λ i θ β N' hQ c (firstIndFMap Q Λ i θ β hQ g x) := by
  obtain ⟨a, rfl⟩ := RingCon.mk'_surjective _ c
  exact firstIndFMap_action Q Λ i θ β hQ g a x

theorem firstIndFMap_unitGen (n : N) :
    firstIndFMap Q Λ i θ β hQ g (firstIndUnitGen Q Λ i θ β N hQ n) =
      firstIndUnitGen Q Λ i θ β N' hQ (g n) := rfl

theorem firstIndFMap_gen (n : N) :
    firstIndFMap Q Λ i θ β hQ g (firstIndGen Q Λ i θ β N hQ n) =
      firstIndGen Q Λ i θ β N' hQ (g n) := by
  rw [firstIndGen, map_smul, firstIndFMap_unitGen]

theorem firstIndLeftMap_natural (y : Ind N (leftAppendHom Q Λ i θ β)) :
    firstIndLeftMap Q Λ i θ β N' hQ (Ind.map g y) =
      firstIndFMap Q Λ i θ β hQ g (firstIndLeftMap Q Λ i θ β N hQ y) := by
  induction y using Ind.induction_on with
  | zero => simp only [map_zero]
  | tmul z n =>
    rw [Ind.map_tmul, firstIndLeftMap_tmul, firstIndLeftMap_tmul, firstIndFMap_layerAction,
      firstIndFMap_gen]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add (firstIndLeftMap Q Λ i θ β N hQ),
      map_add (firstIndFMap Q Λ i θ β hQ g)]

theorem firstIndShuffle_natural
    (x : ParabolicShuffle Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N)) :
    firstIndShuffle Q Λ i θ β N' hQ
        (parabolicShuffleMap Q Λ ((Si i) + θ) β (firstIndLeftHom Q Λ i θ β g) x) =
      firstIndFMap Q Λ i θ β hQ g (firstIndShuffle Q Λ i θ β N hQ x) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r y =>
    change firstIndKLRAction Q Λ i θ β N' hQ r.1
        (firstIndLeftMap Q Λ i θ β N' hQ (Ind.map g y)) =
      firstIndFMap Q Λ i θ β hQ g (firstIndKLRAction Q Λ i θ β N hQ r.1
        (firstIndLeftMap Q Λ i θ β N hQ y))
    rw [firstIndLeftMap_natural, firstIndKLRAction_apply, firstIndKLRAction_apply,
      firstIndFMap_action]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add (firstIndShuffle Q Λ i θ β N hQ),
      map_add (firstIndFMap Q Λ i θ β hQ g)]

/-- **`δ₁ : S(₁Fᵢ N) → Fᵢ(S N)` is natural.** -/
theorem firstIndDeltaT_natural (x : FirstIndStandardT Q Λ i θ β N hQ) :
    firstIndDeltaT Q Λ i θ β N' hQ (firstIndStandardMap Q Λ i θ β hQ g x) =
      firstIndFMap Q Λ i θ β hQ g (firstIndDeltaT Q Λ i θ β N hQ x) := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ x
  exact firstIndShuffle_natural Q Λ i θ β hQ g w

end First

end Categorification.Stendhal
