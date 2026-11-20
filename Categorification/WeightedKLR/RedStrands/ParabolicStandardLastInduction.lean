/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlack
import Categorification.Algebra.InductionAlongTensor

/-!
# Induction along the last black strand and standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For a module `N` over `D(θ, β) = T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)`, the functor
`₂F_i` is induction along `1 ⊗ cyclotomicLast : D(θ, β) → D(θ, i + β)`. This file constructs
the map `S N → S(₂F_i N)` adjoining a black strand on the right: `r ⊗ n ↦ ι(r ⊗ 1_i) ⊗ (1 ⊗ n)`.
It descends to standardization and intertwines `t ∈ T(θ + β)` with `appendBlack t`.

## Main definitions

* `LastIndRight`: the module `₂F_i N`.
* `lastIndShuffle`: the map `Ind N → Ind (₂F_i N)` of parabolic shuffle modules.
* `lastIndStandard`: the induced map `S N → S(₂F_i N)` of standardizations.

## Main results

* `parabolicInputMap_tensorAppendR_right`.
* `lastIndShuffle_smul`, `lastIndStandard_smul`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β)
local notation "hD" => lastWeight_addBlack (ℓ := ℓ) i β
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))

/-- `parabolicInputMap` intertwines appending a black strand to the second tensor factor with
`1 ⊗ cyclotomicLast`, for an arbitrary first weight. -/
theorem parabolicInputMap_tensorAppendR_right (t : TensorKLR S Aₚ Aₗ) :
    parabolicInputMap Q Λ θ ((Si i) + β) (castTensor S rfl hD (tensorAppendR S Aₚ Aₗ j t)) =
      parabolicAppendRight Q Λ i β θ (parabolicInputMap Q Λ θ β t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [tensorAppendR_tmul, castTensor_tmul, castKLR_rfl]
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul, parabolicAppendRight,
      NonUnitalAlgHom.tensorMap_tmul]
    rw [parabolicLastCyclotomic_appendR]
    rfl

/-- `1 ⊗ cyclotomicLast` as a nonunital ring map, for an arbitrary first weight. -/
abbrev parabolicRightHom :
    parabolicFactorAlgebra Q Λ θ β →ₙ+* parabolicFactorAlgebra Q Λ θ ((Si i) + β) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (parabolicAppendRight Q Λ i β θ)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

/-- **`₂F_i N`**: induction along `1 ⊗ cyclotomicLast`. -/
abbrev LastIndRight := IndK k N (parabolicRightHom Q Λ i θ β)

local notation "Fr" => LastIndRight Q Λ i θ β N
local notation "N₀" => ParabolicInput Q Λ θ β N

/-- The input module `₂F_i N` of standardization, viewed over `R(ν₀) ⊗ R(ν₀' + i)`. -/
def LastIndInput := ParabolicInput Q Λ θ ((Si i) + β) Fr

local notation "N₁" => LastIndInput Q Λ i θ β N
local notation "N₂" => ParabolicInput Q Λ θ ((Si i) + β) Fr

instance : AddCommGroup N₁ := inferInstanceAs (AddCommGroup N₂)
instance : Module k N₁ := inferInstanceAs (Module k N₂)
instance : Module (TensorKLR S Aₚ (Aₗ + {j})) N₁ :=
  Module.compHom N₂ (castTensor S rfl hD).toRingEquiv.toRingHom
instance : IsScalarTower k (TensorKLR S Aₚ (Aₗ + {j})) N₁ :=
  ⟨fun c t n => by
    change castTensor S rfl hD (c • t) • (show N₂ from n) =
      c • (castTensor S rfl hD t • (show N₂ from n))
    rw [map_smul, smul_assoc]⟩

/-- `LastIndInput` is the input module of `₂F_i N`. -/
def lastIndInputEquiv : N₁ ≃ₗ[k] N₂ := LinearEquiv.refl k N₂

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem tensorAppendR_smul_lastIndInput (t : TensorKLR S Aₚ Aₗ) (x : N₁) :
    (show Fr from (tensorAppendR S Aₚ Aₗ j t • x)) =
      parabolicAppendRight Q Λ i β θ (parabolicInputMap Q Λ θ β t) • (show Fr from x) := by
  change parabolicInputMap Q Λ θ ((Si i) + β) (castTensor S rfl hD _) • (show Fr from x) = _
  rw [parabolicInputMap_tensorAppendR_right]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- The unit `n ↦ 1 ⊗ n` into the right-restricted input module. -/
def lastIndUnit : N₀ →ₗ[TensorKLR S Aₚ Aₗ] ResRight S Aₚ Aₗ j N₁ where
  toFun n := Res.mk (show N₁ from (unitMap (φ := parabolicRightHom Q Λ i θ β) N n).val) (by
    have h := tensorAppendR_smul_lastIndInput Q Λ i θ β N 1
      (show N₁ from (unitMap (φ := parabolicRightHom Q Λ i θ β) N n).val)
    rw [map_one (parabolicInputMap Q Λ θ β)] at h
    exact h.trans (unitMap (φ := parabolicRightHom Q Λ i θ β) N n).prop)
  map_add' n n' := Res.ext (Ind.tmul_add _ n n')
  map_smul' t n := Res.ext (by
    refine (congrArg (fun x : Res (parabolicRightHom Q Λ i θ β) (Ind N _) => x.val)
      ((unitMap (φ := parabolicRightHom Q Λ i θ β) N).map_smul
        (parabolicInputMap Q Λ θ β t) n)).trans ?_
    exact (tensorAppendR_smul_lastIndInput Q Λ i θ β N t _).symm)

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
@[simp] theorem lastIndUnit_val (n : N₀) :
    (show Fr from (lastIndUnit Q Λ i θ β N n).val) =
      Ind.tmul (unitGen (parabolicRightHom Q Λ i θ β)) (show N from n) := rfl

/-- **The map `Ind N → Ind (₂F_i N)` of parabolic shuffle modules**,
`r ⊗ n ↦ ι(r ⊗ 1_i) ⊗ (1 ⊗ n)`. -/
def lastIndShuffle :
    ParabolicShuffle Q Λ θ β N →ₗ[k] ParabolicShuffle Q Λ θ ((Si i) + β) Fr :=
  (indCast (Q := S) rfl hD (lastIndInputEquiv Q Λ i θ β N) (fun _ _ => rfl)).toLinearMap ∘ₗ
    indAppend ∘ₗ
      ((BalancedTensor.mapRight (lastIndUnit Q Λ i θ β N)).restrictScalars k)

omit [DecidableEq I] in
/-- The weight `ν₀ + ν₀' + i` of the target, as the weight `ν₀ + (ν₀' + i)`. -/
theorem lastInd_weight : Aₚ + Aₗ + {j} = Aₚ + Multiset.map lastColour (stendhalWeight 1
    ((Si i) + β)) :=
  (add_assoc _ _ _).trans (add_eq_add_of_eq rfl hD)

/-- `lastIndShuffle` intertwines `a` with `ι(a ⊗ 1_i)`. -/
theorem lastIndShuffle_smul (a : KLRAlgebra k S (Aₚ + Aₗ)) (x : ParabolicShuffle Q Λ θ β N) :
    lastIndShuffle Q Λ i θ β N (a • x) =
      castKLR S (lastInd_weight i θ β) (appendR S (Aₚ + Aₗ) j a) •
        lastIndShuffle Q Λ i θ β N x := by
  have h1 : (BalancedTensor.mapRight (lastIndUnit Q Λ i θ β N)).restrictScalars k (a • x) =
      a • (BalancedTensor.mapRight (lastIndUnit Q Λ i θ β N)).restrictScalars k x :=
    (BalancedTensor.mapRight (lastIndUnit Q Λ i θ β N)).map_smul a x
  have h2 := indCast_smul (Q := S) (h := rfl) (h' := hD) (g := lastIndInputEquiv Q Λ i θ β N)
    (hg := fun _ _ => rfl) (castKLR S (add_assoc _ _ _) (appendR S (Aₚ + Aₗ) j a))
    (indAppend ((BalancedTensor.mapRight (lastIndUnit Q Λ i θ β N)).restrictScalars k x))
  simp only [lastIndShuffle, LinearMap.coe_comp, Function.comp_apply, h1, indAppend_smul,
    LinearEquiv.coe_coe]
  rw [h2, castKLR_castKLR]

end Categorification.Stendhal
