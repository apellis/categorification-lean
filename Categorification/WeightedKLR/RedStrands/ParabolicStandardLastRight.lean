/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlack
import Categorification.KLR.IndLastStrandOneSidedDescent

/-!
# `E_i` of standardization when `i` occurs only in the last block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, the case where `i` occurs in `β = i + β₀` but not in `θ`. Then the first term
`S(₁E_i N)` of the exact sequence vanishes, and `E_i(S N) ≅ S(₂E_i N)`
(`rightBlackResEquiv`). The KLR input is the one-sided case of Khovanov–Lauda I
(arXiv:0803.4121v2), Proposition 2.18 (`KLRAlgebra.oneSidedDescendEquiv`). Gradings are not
modelled.

## Main definitions

* `RightResRight`: the module `₂E_i N`, restriction along `1 ⊗ cyclotomicLast`.
* `rightBlackResEquiv`: `E_i(S N) ≅ S(₂E_i N)` when `i ∉ θ`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Idempotents

variable {I k : Type*} [DecidableEq I] [CommRing k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin n → I →₀ ℕ}
  (ν₀ ν₀' : Multiset (I ⊕ Fin n)) (c : I)

local notation "S" => stendhalQ Q Λ
local notation "j" => (Sum.inl c : I ⊕ Fin n)

/-- **`P 1_{-,i} = ι(P₂ ⊗ 1_i)`** for the red-ordered idempotents of `R(ν₀ + ν₀' + i)` and
`R(ν₀ + ν₀')`, for an arbitrary first weight `ν₀`. -/
theorem eSum_redOrderedSet_mul_lastIdemOf :
    eSum S (redOrderedSet (ν₀ + (ν₀' + {j}))) * lastIdemOf S ν₀ ν₀' j =
      castKLR S (add_assoc ν₀ ν₀' {j})
        (appendR S (ν₀ + ν₀') j (eSum S (redOrderedSet (ν₀ + ν₀')))) := by
  rw [← castKLR_eSum_redOrderedSet (add_assoc ν₀ ν₀' {j}), lastIdemOf, ← map_mul,
    appendR_apply, eSum_mul_oneConcat_singleton]
  intro a
  rw [mem_redOrderedSet, mem_redOrderedSet, isRedOrdered_append_black]

theorem commute_eSum_redOrderedSet_lastIdemOf :
    Commute (eSum S (redOrderedSet (ν₀ + (ν₀' + {j})))) (lastIdemOf S ν₀ ν₀' j) := by
  rw [← castKLR_eSum_redOrderedSet (add_assoc ν₀ ν₀' {j}), lastIdemOf, oneConcat]
  exact (commute_eSum_eSum _ _).map _

end Idempotents

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β₀ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aθ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "hD" => lastWeight_addBlack (ℓ := ℓ) i β₀
local notation "β" => ((Si i) + β₀)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))
local notation "P" => eSum S (redOrderedSet (Aθ + (Aₗ + {j})))
local notation "P₂" => eSum S (redOrderedSet (Aθ + Aₗ))
local notation "e₁" => lastIdemOf S Aθ Aₗ j

omit [DecidableEq I] in
/-- A colour not in `θ` is not a black colour of the first block. -/
theorem inl_notMem_prefixWeight (hi : i ∉ θ) : j ∉ Aθ := by
  simp [stendhalWeight, addRedColor, hi]

/-- `parabolicInputMap` intertwines appending a black strand to the second tensor factor with
`1 ⊗ cyclotomicLast`, for an arbitrary first block. -/
theorem parabolicInputMap_tensorAppendR_right (t : TensorKLR S Aθ Aₗ) :
    parabolicInputMap Q Λ θ β (castTensor S rfl hD (tensorAppendR S Aθ Aₗ j t)) =
      parabolicAppendRight Q Λ i β₀ θ (parabolicInputMap Q Λ θ β₀ t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [tensorAppendR_tmul, castTensor_tmul, castKLR_rfl]
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul, parabolicAppendRight,
      NonUnitalAlgHom.tensorMap_tmul]
    rw [parabolicLastCyclotomic_appendR]
    rfl

omit [DecidableEq I] in
/-- The weights `ν + ν₀' + i` of the two factors with the last black strand. -/
theorem rightShuffle_weight :
    Aθ + (Aₗ + {j}) = Aθ + Multiset.map lastColour (stendhalWeight 1 β) :=
  add_eq_add_of_eq rfl hD

/-- `1 ⊗ cyclotomicLast` as a nonunital ring map, `D(θ, β₀) → D(θ, i + β₀)`. -/
abbrev rightAppendHom :
    parabolicFactorAlgebra Q Λ θ β₀ →ₙ+* parabolicFactorAlgebra Q Λ θ β :=
  NonUnitalRingHomClass.toNonUnitalRingHom (parabolicAppendRight Q Λ i β₀ θ)

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]

/-- The input module of parabolic induction, viewed over `R(ν) ⊗ R(ν₀' + i)`. -/
def RightInput := ParabolicInput Q Λ θ ((Si i) + β₀) N

/-- **`₂E_i N`**: restriction along `1 ⊗ cyclotomicLast`. -/
abbrev RightResRight := Res (rightAppendHom Q Λ i θ β₀) N

local notation "N₁" => RightInput Q Λ i θ β₀ N
local notation "N₀" => ParabolicInput Q Λ θ ((Si i) + β₀) N
local notation "Er" => RightResRight Q Λ i θ β₀ N

instance : AddCommGroup N₁ := inferInstanceAs (AddCommGroup N₀)
instance : Module k N₁ := inferInstanceAs (Module k N₀)
instance : Module (TensorKLR S Aθ (Aₗ + {Sum.inl i})) N₁ :=
  Module.compHom N₀ (castTensor S rfl hD).toRingEquiv.toRingHom
instance : IsScalarTower k (TensorKLR S Aθ (Aₗ + {Sum.inl i})) N₁ :=
  ⟨fun c t n => by
    change castTensor S rfl hD (c • t) • (show N₀ from n) =
      c • (castTensor S rfl hD t • (show N₀ from n))
    rw [map_smul, smul_assoc]⟩

instance : Module k Er := Module.compHom _ (algebraMap k (parabolicFactorAlgebra Q Λ θ β₀))
instance : IsScalarTower k (parabolicFactorAlgebra Q Λ θ β₀) Er where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (parabolicFactorAlgebra Q Λ θ β₀) c) • (t • n)
    exact (congrArg (· • n) (Algebra.smul_def c t)).trans (mul_smul _ _ _)

/-- `RightInput` is the input module. -/
def rightInputEquiv : N₁ ≃ₗ[k] N₀ := LinearEquiv.refl k N₀

/-- **The parabolic shuffle module as an induced module from `R(ν) ⊗ R(ν₀' + i)`.** -/
def rightShuffleEquiv :
    Ind S Aθ (Aₗ + {Sum.inl i}) N₁ ≃ₗ[k] ParabolicShuffle Q Λ θ β N :=
  indCast rfl hD (rightInputEquiv Q Λ i θ β₀ N) fun _ _ => rfl

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N] in
theorem rightShuffleEquiv_smul (a : KLRAlgebra k S (Aθ + (Aₗ + {Sum.inl i})))
    (y : Ind S Aθ (Aₗ + {Sum.inl i}) N₁) :
    rightShuffleEquiv Q Λ i θ β₀ N (a • y) =
      castKLR S (rightShuffle_weight i θ β₀) a • rightShuffleEquiv Q Λ i θ β₀ N y :=
  indCast_smul (h := rfl) (h' := hD) (g := rightInputEquiv Q Λ i θ β₀ N) (hg := fun _ _ => rfl) a y

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N] in
theorem tensorAppendR_smul_rightInput (t : TensorKLR S Aθ Aₗ) (n : N₁) :
    (show N from (tensorAppendR S Aθ Aₗ (Sum.inl i) t • n)) =
      parabolicAppendRight Q Λ i β₀ θ (parabolicInputMap Q Λ θ β₀ t) • (show N from n) := by
  change parabolicInputMap Q Λ θ β (castTensor S rfl hD _) • (show N from n) = _
  rw [parabolicInputMap_tensorAppendR_right]

/-- `₂(RightInput) ≅ ₂E_i N` as modules over `R(ν) ⊗ R(ν₀')`, along the input map. -/
def rightResRightEquiv :
    ResRight S Aθ Aₗ (Sum.inl i) N₁ ≃ₗ[k] ParabolicInput Q Λ θ β₀ Er where
  toFun m := Res.mk (show N from m.val) (by
    have h := tensorAppendR_smul_rightInput Q Λ i θ β₀ N 1 m.val
    rw [map_one (parabolicInputMap Q Λ θ β₀)] at h
    exact h.symm.trans m.prop)
  invFun m := Res.mk (show N₁ from m.val) (by
    have h := tensorAppendR_smul_rightInput Q Λ i θ β₀ N 1 (show N₁ from m.val)
    rw [map_one (parabolicInputMap Q Λ θ β₀)] at h
    exact h.trans m.prop)
  left_inv _ := Res.ext rfl
  right_inv _ := Res.ext rfl
  map_add' _ _ := Res.ext rfl
  map_smul' c m := Res.ext
    ((tensorAppendR_smul_rightInput Q Λ i θ β₀ N (algebraMap k _ c) m.val).trans
      (by rw [AlgHom.commutes]; rfl))

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N] in
theorem rightResRightEquiv_smul (t : TensorKLR S Aθ Aₗ) (m : ResRight S Aθ Aₗ (Sum.inl i) N₁) :
    rightResRightEquiv Q Λ i θ β₀ N (t • m) =
      castTensor S rfl rfl t • rightResRightEquiv Q Λ i θ β₀ N m :=
  Res.ext (tensorAppendR_smul_rightInput Q Λ i θ β₀ N t m.val)

local notation "L" => Algebra.lsmul k k (Ind S Aθ (Aₗ + {j}) N₁)
local notation "Lt" => Algebra.lsmul k k (Ind S Aθ Aₗ (ResRight S Aθ Aₗ j N₁))

/-- The image of `1_{-,i}` in the parabolic shuffle module. -/
abbrev rightShuffleIdem : Module.End k (ParabolicShuffle Q Λ θ β N) :=
  parabolicShuffleAction Q Λ θ β N (castKLR S (rightShuffle_weight i θ β₀) e₁)

/-- **The middle term**, transported to the parabolic shuffle module. -/
def rightMiddleEquiv :
    (Ind S Aθ (Aₗ + {j}) N₁ ⧸ LinearMap.ker (L P * L e₁)) ≃ₗ[k]
      (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * rightShuffleIdem Q Λ i θ β₀ N)) :=
  descendLinearEquiv _ _ (rightShuffleEquiv Q Λ i θ β₀ N) fun y => by
    simp only [Module.End.mul_apply, Algebra.lsmul_coe, rightShuffleEquiv_smul,
      castKLR_eSum_redOrderedSet, parabolicOrderedLoadings_eq_redOrderedSet]

/-- **The submodule term** `S(₂E_i N)`. -/
def rightTwoEquiv :
    (Ind S Aθ Aₗ (ResRight S Aθ Aₗ j N₁) ⧸ LinearMap.ker (Lt P₂)) ≃ₗ[k]
      ParabolicStandard Q Λ θ β₀ Er :=
  descendLinearEquiv _ _
    (indCast rfl rfl (rightResRightEquiv Q Λ i θ β₀ N) (rightResRightEquiv_smul Q Λ i θ β₀ N))
    fun y => by
      simp only [Algebra.lsmul_coe, indCast_smul, castKLR_eSum_redOrderedSet,
        parabolicOrderedLoadings_eq_redOrderedSet]

variable (hQ : KLRSymm Q)

/-- `S(₂E_i N)` is the middle term of the last-strand sequence when `i ∉ θ`. -/
def rightStandardTwoEquiv (hi : i ∉ θ) :
    ParabolicStandard Q Λ θ β₀ Er ≃ₗ[k]
      (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * rightShuffleIdem Q Λ i θ β₀ N)) :=
  (rightTwoEquiv Q Λ i θ β₀ N).symm.trans
    ((oneSidedDescendEquiv (N := N₁) (eSum_idem _)
      (commute_eSum_redOrderedSet_lastIdemOf Aθ Aₗ i)
      (eSum_redOrderedSet_mul_lastIdemOf Aθ Aₗ i) (stendhalQ_swap_symm Q Λ hQ)
      (inl_notMem_prefixWeight i θ hi)).trans (rightMiddleEquiv Q Λ i θ β₀ N))

theorem rightShuffle_commute :
    Commute (lastShuffleOrdered Q Λ θ β N) (rightShuffleIdem Q Λ i θ β₀ N) := by
  have h := (commute_eSum_redOrderedSet_lastIdemOf (Q := Q) (Λ := Λ) Aθ Aₗ i).map
    (castKLR S (rightShuffle_weight i θ β₀))
  rw [castKLR_eSum_redOrderedSet, ← parabolicOrderedLoadings_eq_redOrderedSet] at h
  exact h.map _

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N] in
theorem rightShuffleIdem_idem : IsIdempotentElem (rightShuffleIdem Q Λ i θ β₀ N) := by
  unfold IsIdempotentElem
  rw [rightShuffleIdem, ← map_mul, ← map_mul, lastIdemOf_mul_self]

/-- The element `1_{-,i}` of `T(θ + β)`. -/
def rightBlackIdem : TensorProductAlgebra k Q Λ (θ + β) :=
  TensorProductAlgebra.mk Q Λ (θ + β) (orderProjection Q Λ (θ + β)
    (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)
      (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β)
        (castKLR S (rightShuffle_weight i θ β₀) e₁))))

/-- On standardization, `1_{-,i}` acts by the operator induced by `e`. -/
theorem rightInducedOp_eq :
    (inducedOp _ _ (rightShuffle_commute Q Λ i θ β₀ N) :
        Module.End k (ParabolicStandard Q Λ θ β N)) =
      parabolicStandardAction Q Λ θ β N hQ (rightBlackIdem Q Λ i θ β₀) := by
  rw [rightBlackIdem, parabolicStandardAction_affine]
  exact Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The `1_{-,i}`-fixed part of standardization `S N`. -/
abbrev RightStandardFixed : Submodule k (ParabolicStandard Q Λ θ β N) :=
  LinearMap.ker (parabolicStandardAction Q Λ θ β N hQ (rightBlackIdem Q Λ i θ β₀) -
    LinearMap.id)

/-- **The middle term is the `1_{-,i}`-fixed part of `S N`.** -/
def rightStandardMiddleEquiv :
    (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * rightShuffleIdem Q Λ i θ β₀ N)) ≃ₗ[k]
      RightStandardFixed Q Λ i θ β₀ N hQ :=
  (rangeEquiv _ _ (rightShuffleIdem_idem Q Λ i θ β₀ N)
    (rightShuffle_commute Q Λ i θ β₀ N)).trans
    (LinearEquiv.ofEq _ _ (congrArg (fun f => LinearMap.ker (f - LinearMap.id))
      (rightInducedOp_eq Q Λ i θ β₀ N hQ)))

omit [DecidableEq I] in
/-- The weights `i + (θ + β₀)` and `θ + β` agree. -/
theorem rightBlack_weight : (Si i) + (θ + β₀) = θ + β := add_left_comm _ _ _

/-- **The idempotent `1_{-,i}` is Webster's `E_i` idempotent** `appendBlack 1` of
`T(i + (θ + β₀))`, transported to `T(θ + β)`. -/
theorem castTensorProductAlgebra_appendBlack_one_right :
    castTensorProductAlgebra Q Λ (rightBlack_weight i θ β₀) (appendBlack Q Λ i (θ + β₀) 1) =
      rightBlackIdem Q Λ i θ β₀ := by
  rw [appendBlack_one_eq_oneConcat, castTensorProductAlgebra_mk, rightBlackIdem, lastIdemOf,
    castKLR_castKLR, castKLR_castKLR, castKLR_castKLR]
  exact congrArg (tensorOfKLR Q Λ _)
    (castKLR_oneConcat_eq (parabolicInputWeights_add (ℓ := ℓ) θ β₀).symm _ _)

/-- The action of `T(i + (θ + β₀))` on standardization `S N`. -/
def rightStandardTAction :
    TensorProductAlgebra k Q Λ ((Si i) + (θ + β₀)) →ₐ[k]
      Module.End k (ParabolicStandard Q Λ θ β N) :=
  (parabolicStandardAction Q Λ θ β N hQ).comp
    (castTensorProductAlgebra Q Λ (rightBlack_weight i θ β₀)).toAlgHom

/-- Standardization `S N` viewed as a module over `T(i + (θ + β₀))`. -/
def RightStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ β N

instance : AddCommGroup (RightStandardT Q Λ i θ β₀ N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ β N))
instance : Module k (RightStandardT Q Λ i θ β₀ N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β N))
instance : Module (TensorProductAlgebra k Q Λ ((Si i) + (θ + β₀)))
    (RightStandardT Q Λ i θ β₀ N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ β N) (rightStandardTAction Q Λ i θ β₀ N hQ).toRingHom
instance : IsScalarTower k (TensorProductAlgebra k Q Λ ((Si i) + (θ + β₀)))
    (RightStandardT Q Λ i θ β₀ N hQ) :=
  ⟨fun c t m => by
    change rightStandardTAction Q Λ i θ β₀ N hQ (c • t) m =
      c • rightStandardTAction Q Λ i θ β₀ N hQ t m
    rw [map_smul]
    rfl⟩

theorem appendBlack_one_smul_rightStandardT (m : ParabolicStandard Q Λ θ β N) :
    (appendBlack Q Λ i (θ + β₀) 1 • (show RightStandardT Q Λ i θ β₀ N hQ from m) :
        ParabolicStandard Q Λ θ β N) =
      parabolicStandardAction Q Λ θ β N hQ (rightBlackIdem Q Λ i θ β₀) m := by
  change parabolicStandardAction Q Λ θ β N hQ
    (castTensorProductAlgebra Q Λ (rightBlack_weight i θ β₀) (appendBlack Q Λ i (θ + β₀) 1)) m = _
  rw [castTensorProductAlgebra_appendBlack_one_right]

theorem mem_rightStandardFixed_iff (m : ParabolicStandard Q Λ θ β N) :
    m ∈ RightStandardFixed Q Λ i θ β₀ N hQ ↔
      parabolicStandardAction Q Λ θ β N hQ (rightBlackIdem Q Λ i θ β₀) m = m := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]

/-- `E_i(S N)` is the `1_{-,i}`-fixed part of `S N`. -/
def rightBlackFixedEquiv :
    BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ) ≃ₗ[k]
      RightStandardFixed Q Λ i θ β₀ N hQ where
  toFun m := ⟨show ParabolicStandard Q Λ θ β N from m.1,
    (mem_rightStandardFixed_iff Q Λ i θ β₀ N hQ _).2
      ((appendBlack_one_smul_rightStandardT Q Λ i θ β₀ N hQ m.1).symm.trans m.2)⟩
  invFun m := ⟨show RightStandardT Q Λ i θ β₀ N hQ from m.1,
    (appendBlack_one_smul_rightStandardT Q Λ i θ β₀ N hQ m.1).trans
      ((mem_rightStandardFixed_iff Q Λ i θ β₀ N hQ _).1 m.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Webster, Prop 5.5, `E`-part, `i ∉ θ`:** for `β = i + β₀` and `i ∉ θ`,
`E_i(S N) ≅ S(₂E_i N)`. -/
def rightBlackResEquiv (hi : i ∉ θ) :
    BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ) ≃ₗ[k]
      ParabolicStandard Q Λ θ β₀ Er :=
  (rightBlackFixedEquiv Q Λ i θ β₀ N hQ).trans
    ((rightStandardMiddleEquiv Q Λ i θ β₀ N hQ).symm.trans
      (rightStandardTwoEquiv Q Λ i θ β₀ N hQ hi).symm)

end Categorification.Stendhal
