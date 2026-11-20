/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastInduction

/-!
# The map `F_i(S N) → S(₂F_i N)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. The functor `F_i` on modules over `T(θ + β)` is induction along
Webster's map `appendBlack`, which adds a black strand labelled `i` on the right. The map
`S N → S(₂F_i N)` of `lastIndStandard` intertwines `t` with `appendBlack t`
(`lastIndStandard_smul`), so it induces a map of `T(i + (θ + β))`-modules
`F_i(S N) → S(₂F_i N)`, `z ⊗ m ↦ z · g(m)` (`lastIndQuotientMap`).

## Main definitions

* `ParabolicStandardT`: standardization `S N` as a module over `T(θ + β)`.
* `LastIndStandardT`: `S(₂F_i N)` as a module over `T(i + (θ + β))`.
* `lastIndQuotientMap`: the map `F_i(S N) → S(₂F_i N)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "Fr" => LastIndRight Q Λ i θ β N

/-- Standardization `S N` viewed as a module over `T(θ + β)`. -/
def ParabolicStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ β N

instance : AddCommGroup (ParabolicStandardT Q Λ θ β N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ β N))
instance : Module k (ParabolicStandardT Q Λ θ β N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β N))
instance : Module (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ β N) (parabolicStandardAction Q Λ θ β N hQ).toRingHom

/-- `S(₂F_i N)` viewed as a module over `T(i + (θ + β))`. -/
def LastIndStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ ((Si i) + β) Fr

instance : AddCommGroup (LastIndStandardT Q Λ i θ β N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ ((Si i) + β) Fr))
instance : Module k (LastIndStandardT Q Λ i θ β N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ ((Si i) + β) Fr))
instance : Module (TensorProductAlgebra k Q Λ ((Si i) + (θ + β)))
    (LastIndStandardT Q Λ i θ β N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ ((Si i) + β) Fr)
    ((parabolicStandardAction Q Λ θ ((Si i) + β) Fr hQ).comp
      (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).toAlgHom).toRingHom

/-- Webster's `appendBlack` as a nonunital ring map. -/
abbrev appendBlackHom :
    TensorProductAlgebra k Q Λ (θ + β) →ₙ+* TensorProductAlgebra k Q Λ ((Si i) + (θ + β)) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (appendBlack Q Λ i (θ + β))

/-- **`F_i(S N)`**: induction of `S N` along `appendBlack`. -/
abbrev LastIndF := Ind (ParabolicStandardT Q Λ θ β N hQ) (appendBlackHom Q Λ i θ β)

/-- The map `S N → S(₂F_i N)` between the module wrappers. -/
def lastIndStandardT :
    ParabolicStandardT Q Λ θ β N hQ → LastIndStandardT Q Λ i θ β N hQ :=
  fun m => lastIndStandard Q Λ i θ β N m

theorem lastIndStandardT_add (m m' : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndStandardT Q Λ i θ β N hQ (m + m') =
      lastIndStandardT Q Λ i θ β N hQ m + lastIndStandardT Q Λ i θ β N hQ m' :=
  map_add (lastIndStandard Q Λ i θ β N) m m'

theorem lastIndStandardT_smul (t : TensorProductAlgebra k Q Λ (θ + β))
    (m : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndStandardT Q Λ i θ β N hQ (t • m) =
      appendBlack Q Λ i (θ + β) t • lastIndStandardT Q Λ i θ β N hQ m :=
  lastIndStandard_smul Q Λ i θ β N hQ t m

/-- **The map `F_i(S N) → S(₂F_i N)`**, `z ⊗ m ↦ z · g(m)`. -/
def lastIndQuotientMap :
    LastIndF Q Λ i θ β N hQ →ₗ[TensorProductAlgebra k Q Λ ((Si i) + (θ + β))]
      LastIndStandardT Q Λ i θ β N hQ :=
  Ind.lift (fun z m => z.1 • lastIndStandardT Q Λ i θ β N hQ m)
    (fun z z' m => add_smul _ _ _)
    (fun z m m' => by rw [lastIndStandardT_add, smul_add])
    (fun z a m => by
      rw [op_smul_val, lastIndStandardT_smul, mul_smul]
      rfl)
    (fun b z m => mul_smul _ _ _)

@[simp] theorem lastIndQuotientMap_tmul (z : Corner (appendBlackHom Q Λ i θ β))
    (m : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndQuotientMap Q Λ i θ β N hQ (Ind.tmul z m) =
      z.1 • lastIndStandardT Q Λ i θ β N hQ m := rfl

end Categorification.Stendhal
