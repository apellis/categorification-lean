/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastInput

/-!
# The outer terms of the last-strand sequence of standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For `θ = i + θ₀` and `β = i + β₀`, the functors `₁E_i` and `₂E_i` on modules
over `D(θ, β) = T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` are restriction along `appendBlack ⊗ 1 : D(θ₀, β) →
D(θ, β)` and `1 ⊗ cyclotomicLast : D(θ, β₀) → D(θ, β)`. Restricting `LastInput` to the
factors with one last strand removed gives these restrictions, transported along the input map.

## Main definitions

* `LastResRight`, `LastResLeft`: the modules `₂E_i N` and `₁E_i N`.
* `lastOuterRightEquiv`, `lastOuterLeftEquiv`: the outer terms of the last-strand sequence of
  `Ind (LastInput)` are the parabolic shuffle modules of `₂E_i N` and `₁E_i N`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong
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
local notation "θ" => ((Si i) + θ₀)
local notation "β" => ((Si i) + β₀)

/-- `1 ⊗ cyclotomicLast` as a nonunital ring map. -/
abbrev parabolicAppendRightHom :
    parabolicFactorAlgebra Q Λ θ β₀ →ₙ+* parabolicFactorAlgebra Q Λ θ β :=
  NonUnitalRingHomClass.toNonUnitalRingHom (parabolicAppendRight Q Λ i β₀ θ)

/-- `appendBlack ⊗ 1` as a nonunital ring map. -/
abbrev parabolicAppendLeftHom :
    parabolicFactorAlgebra Q Λ θ₀ β →ₙ+* parabolicFactorAlgebra Q Λ θ β :=
  NonUnitalRingHomClass.toNonUnitalRingHom (parabolicAppendLeft Q Λ i θ₀ β)

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]

/-- **`₂E_i N`**: restriction along `1 ⊗ cyclotomicLast`. -/
abbrev LastResRight := Res (parabolicAppendRightHom Q Λ i θ₀ β₀) N

/-- **`₁E_i N`**: restriction along `appendBlack ⊗ 1`. -/
abbrev LastResLeft := Res (parabolicAppendLeftHom Q Λ i θ₀ β₀) N

local notation "N₁" => LastInput Q Λ i θ₀ β₀ N
local notation "Er" => LastResRight Q Λ i θ₀ β₀ N
local notation "El" => LastResLeft Q Λ i θ₀ β₀ N

instance : Module k Er := Module.compHom _ (algebraMap k (parabolicFactorAlgebra Q Λ θ β₀))
instance : IsScalarTower k (parabolicFactorAlgebra Q Λ θ β₀) Er where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (parabolicFactorAlgebra Q Λ θ β₀) c) • (t • n)
    exact (congrArg (· • n) (Algebra.smul_def c t)).trans (mul_smul _ _ _)
instance : Module k El := Module.compHom _ (algebraMap k (parabolicFactorAlgebra Q Λ θ₀ β))
instance : IsScalarTower k (parabolicFactorAlgebra Q Λ θ₀ β) El where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (parabolicFactorAlgebra Q Λ θ₀ β) c) • (t • n)
    exact (congrArg (· • n) (Algebra.smul_def c t)).trans (mul_smul _ _ _)

omit [Module k N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
theorem tensorAppendR_smul_lastInput (t : TensorKLR S (Aₚ + {Sum.inl i}) Aₗ) (n : N₁) :
    (show N from (tensorAppendR S (Aₚ + {Sum.inl i}) Aₗ (Sum.inl i) t • n)) =
      parabolicAppendRight Q Λ i β₀ θ (parabolicInputMap Q Λ θ β₀ (castTensor S hA rfl t)) •
        (show N from n) := by
  change parabolicInputMap Q Λ θ β (castTensor S hA hD _) • (show N from n) = _
  rw [parabolicInputMap_tensorAppendR]

omit [Module k N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
theorem tensorAppendL_smul_lastInput (t : TensorKLR S Aₚ (Aₗ + {Sum.inl i})) (n : N₁) :
    (show N from (tensorAppendL S Aₚ (Aₗ + {Sum.inl i}) (Sum.inl i) t • n)) =
      parabolicAppendLeft Q Λ i θ₀ β (parabolicInputMap Q Λ θ₀ β (castTensor S rfl hD t)) •
        (show N from n) := by
  change parabolicInputMap Q Λ θ β (castTensor S hA hD _) • (show N from n) = _
  rw [parabolicInputMap_tensorAppendL]

/-- `₂(LastInput) ≅ ₂E_i N` as modules over `R(ν₀ + i) ⊗ R(ν₀')`, along the input map. -/
def lastResRightEquiv :
    ResRight S (Aₚ + {Sum.inl i}) Aₗ (Sum.inl i) N₁ ≃ₗ[k] ParabolicInput Q Λ θ β₀ Er where
  toFun m := Res.mk (show N from m.val) (by
    have h := tensorAppendR_smul_lastInput Q Λ i θ₀ β₀ N 1 m.val
    rw [map_one (castTensor S _ _), map_one (parabolicInputMap Q Λ θ β₀)] at h
    exact h.symm.trans m.prop)
  invFun m := Res.mk (show N₁ from m.val) (by
    have h := tensorAppendR_smul_lastInput Q Λ i θ₀ β₀ N 1 (show N₁ from m.val)
    rw [map_one (castTensor S _ _), map_one (parabolicInputMap Q Λ θ β₀)] at h
    exact h.trans m.prop)
  left_inv _ := Res.ext rfl
  right_inv _ := Res.ext rfl
  map_add' _ _ := Res.ext rfl
  map_smul' c m := Res.ext ((tensorAppendR_smul_lastInput Q Λ i θ₀ β₀ N (algebraMap k _ c) m.val).trans
    (by rw [AlgEquiv.commutes, AlgHom.commutes]; rfl))

omit [Module k N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
theorem lastResRightEquiv_smul (t : TensorKLR S (Aₚ + {Sum.inl i}) Aₗ)
    (m : ResRight S (Aₚ + {Sum.inl i}) Aₗ (Sum.inl i) N₁) :
    lastResRightEquiv Q Λ i θ₀ β₀ N (t • m) =
      castTensor S hA rfl t • lastResRightEquiv Q Λ i θ₀ β₀ N m :=
  Res.ext (tensorAppendR_smul_lastInput Q Λ i θ₀ β₀ N t m.val)

/-- `₁(LastInput) ≅ ₁E_i N` as modules over `R(ν₀) ⊗ R(ν₀' + i)`, along the input map. -/
def lastResLeftEquiv :
    ResAppendL S Aₚ Aₗ (Sum.inl i) N₁ ≃ₗ[k] ParabolicInput Q Λ θ₀ β El where
  toFun m := Res.mk (show N from m.val) (by
    have h := tensorAppendL_smul_lastInput Q Λ i θ₀ β₀ N 1 m.val
    rw [map_one (castTensor S _ _), map_one (parabolicInputMap Q Λ θ₀ β)] at h
    exact h.symm.trans m.prop)
  invFun m := Res.mk (show N₁ from m.val) (by
    have h := tensorAppendL_smul_lastInput Q Λ i θ₀ β₀ N 1 (show N₁ from m.val)
    rw [map_one (castTensor S _ _), map_one (parabolicInputMap Q Λ θ₀ β)] at h
    exact h.trans m.prop)
  left_inv _ := Res.ext rfl
  right_inv _ := Res.ext rfl
  map_add' _ _ := Res.ext rfl
  map_smul' c m := Res.ext ((tensorAppendL_smul_lastInput Q Λ i θ₀ β₀ N (algebraMap k _ c) m.val).trans
    (by rw [AlgEquiv.commutes, AlgHom.commutes]; rfl))

omit [Module k N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
theorem lastResLeftEquiv_smul (t : TensorKLR S Aₚ (Aₗ + {Sum.inl i}))
    (m : ResAppendL S Aₚ Aₗ (Sum.inl i) N₁) :
    lastResLeftEquiv Q Λ i θ₀ β₀ N (t • m) =
      castTensor S rfl hD t • lastResLeftEquiv Q Λ i θ₀ β₀ N m :=
  Res.ext (tensorAppendL_smul_lastInput Q Λ i θ₀ β₀ N t m.val)

/-- **The submodule term**: `Ind_{ν₀+i, ν₀'} ₂(LastInput)` is the parabolic shuffle module of
`₂E_i N`. -/
def lastOuterRightEquiv :
    Ind S (Aₚ + {Sum.inl i}) Aₗ (ResRight S (Aₚ + {Sum.inl i}) Aₗ (Sum.inl i) N₁) ≃ₗ[k]
      ParabolicShuffle Q Λ θ β₀ Er :=
  indCast hA rfl (lastResRightEquiv Q Λ i θ₀ β₀ N) (lastResRightEquiv_smul Q Λ i θ₀ β₀ N)

/-- **The quotient term**: `Ind_{ν₀, ν₀'+i} ₁(LastInput)` is the parabolic shuffle module of
`₁E_i N`. -/
def lastOuterLeftEquiv :
    Ind S Aₚ (Aₗ + {Sum.inl i}) (ResAppendL S Aₚ Aₗ (Sum.inl i) N₁) ≃ₗ[k]
      ParabolicShuffle Q Λ θ₀ β El :=
  indCast rfl hD (lastResLeftEquiv Q Λ i θ₀ β₀ N) (lastResLeftEquiv_smul Q Λ i θ₀ β₀ N)

end Categorification.Stendhal
