/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicInputAppend
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleAction
import Categorification.KLR.IndLastStrandQuot
import Categorification.KLR.IndCast

/-!
# The parabolic input map and the last black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. Write `θ = i + θ₀` and `β = i + β₀`. The input of standardization is a module
over `D(θ, β) = T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)`, reached from `R(α(θ)) ⊗ R(δ(β))` by
`parabolicInputMap`. Appending a black strand `i` on the right of either tensor factor of the
KLR algebra corresponds, through `parabolicInputMap`, to the map `D(θ₀, β) → D(θ, β)`
(`appendBlack ⊗ 1`) or `D(θ, β₀) → D(θ, β)` (`1 ⊗ cyclotomicLast`).

## Main definitions

* `NonUnitalAlgHom.tensorMap`: the tensor product of two non-unital algebra maps.

## Main results

* `parabolicInputMap_tensorAppendL`, `parabolicInputMap_tensorAppendR`.
-/

noncomputable section

namespace NonUnitalAlgHom

open scoped TensorProduct

variable {R A A' B B' : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring A']
  [Algebra R A'] [Semiring B] [Algebra R B] [Semiring B'] [Algebra R B']

/-- `f` as a linear map. -/
def toLinearMap' (f : A →ₙₐ[R] A') : A →ₗ[R] A' where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smul f

/-- The tensor product `f ⊗ g` of two non-unital algebra maps. -/
def tensorMap (f : A →ₙₐ[R] A') (g : B →ₙₐ[R] B') : A ⊗[R] B →ₙₐ[R] A' ⊗[R] B' where
  toFun := TensorProduct.map f.toLinearMap' g.toLinearMap'
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' s t := by
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' => simp only [add_mul, map_add, hs, hs']
    | tmul a b =>
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' => simp only [mul_add, map_add, ht, ht']
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
        exact congrArg₂ _ (map_mul f a a') (map_mul g b b')

@[simp] theorem tensorMap_tmul (f : A →ₙₐ[R] A') (g : B →ₙₐ[R] B') (a : A) (b : B) :
    tensorMap f g (a ⊗ₜ b) = f a ⊗ₜ g b := rfl

end NonUnitalAlgHom

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (wt : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ₀ β₀ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q wt
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ wt (Fin.last ℓ) j
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)

/-- Appending a black strand to the left tensor factor: `appendBlack ⊗ 1`,
`D(θ₀, β) → D(i + θ₀, β)`. -/
def parabolicAppendLeft (β : Multiset I) :
    parabolicFactorAlgebra Q wt θ₀ β →ₙₐ[k] parabolicFactorAlgebra Q wt ((Si i) + θ₀) β :=
  NonUnitalAlgHom.tensorMap (appendBlack Q (wt ∘ Fin.castSucc) i θ₀) (NonUnitalAlgHom.id k _)

/-- Appending a black strand to the right tensor factor: `1 ⊗ cyclotomicLast`,
`D(θ, β₀) → D(θ, i + β₀)`. -/
def parabolicAppendRight (θ : Multiset I) :
    parabolicFactorAlgebra Q wt θ β₀ →ₙₐ[k] parabolicFactorAlgebra Q wt θ ((Si i) + β₀) :=
  NonUnitalAlgHom.tensorMap (NonUnitalAlgHom.id k _) (AbsentColour.cyclotomicLast Q i aΛ β₀)

/-- `parabolicInputMap` intertwines appending a black strand to the first tensor factor with
`appendBlack ⊗ 1`. -/
theorem parabolicInputMap_tensorAppendL (t : TensorKLR S Aₚ (Aₗ + {Sum.inl i})) :
    parabolicInputMap Q wt ((Si i) + θ₀) ((Si i) + β₀)
        (castTensor S (prefixWeight_addBlack i θ₀) (lastWeight_addBlack i β₀)
          (tensorAppendL S Aₚ _ (Sum.inl i) t)) =
      parabolicAppendLeft Q wt i θ₀ ((Si i) + β₀)
        (parabolicInputMap Q wt θ₀ ((Si i) + β₀)
          (castTensor S rfl (lastWeight_addBlack i β₀) t)) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [tensorAppendL_tmul, castTensor_tmul, castTensor_tmul, castKLR_rfl]
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul, parabolicAppendLeft,
      NonUnitalAlgHom.tensorMap_tmul]
    rw [parabolicPrefixProjection_appendR]
    rfl

/-- `parabolicInputMap` intertwines appending a black strand to the second tensor factor with
`1 ⊗ cyclotomicLast`. -/
theorem parabolicInputMap_tensorAppendR (t : TensorKLR S (Aₚ + {Sum.inl i}) Aₗ) :
    parabolicInputMap Q wt ((Si i) + θ₀) ((Si i) + β₀)
        (castTensor S (prefixWeight_addBlack i θ₀) (lastWeight_addBlack i β₀)
          (tensorAppendR S _ Aₗ (Sum.inl i) t)) =
      parabolicAppendRight Q wt i β₀ ((Si i) + θ₀)
        (parabolicInputMap Q wt ((Si i) + θ₀) β₀
          (castTensor S (prefixWeight_addBlack i θ₀) rfl t)) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [tensorAppendR_tmul, castTensor_tmul, castTensor_tmul, castKLR_rfl]
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul, parabolicAppendRight,
      NonUnitalAlgHom.tensorMap_tmul]
    rw [parabolicLastCyclotomic_appendR]
    rfl

end Categorification.Stendhal
