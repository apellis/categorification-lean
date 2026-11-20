/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastRight

/-!
# `E_i` of standardization when `i` occurs only in the first block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, the case where `i` occurs in `θ = i + θ₀` but not in `β`. Then the last term
`S(₂E_i N)` of the exact sequence vanishes, and `E_i(S N) ≅ S(₁E_i N)`
(`leftBlackResEquiv`). The KLR input is the first-factor one-sided case of Khovanov–Lauda I
(arXiv:0803.4121v2), Proposition 2.18 (`KLRAlgebra.firstSidedDescendEquiv`). Gradings are not
modelled.

## Main definitions

* `LeftResLeft`: the module `₁E_i N`, restriction along `appendBlack ⊗ 1`.
* `leftBlackResEquiv`: `E_i(S N) ≅ S(₁E_i N)` when `i ∉ β`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Idempotents

variable {I k : Type*} [DecidableEq I] [CommRing k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin n → I →₀ ℕ}
  (ν₀ ν' : Multiset (I ⊕ Fin n)) (c : I)

local notation "S" => stendhalQ Q Λ
local notation "j" => (Sum.inl c : I ⊕ Fin n)

/-- **`P 1_{-,i} = ι(P₁ ⊗ 1_i)`** for the red-ordered idempotents of `R(ν₀ + i + ν')` and
`R(ν₀ + ν')`. -/
theorem eSum_redOrderedSet_mul_firstIdem :
    eSum S (redOrderedSet (ν₀ + {j} + ν')) * firstIdem S ν₀ ν' j =
      firstAppend j (eSum S (redOrderedSet (ν₀ + ν'))) := by
  rw [← castKLR_eSum_redOrderedSet (firstQuad_h ν₀ ν' j).symm, firstIdem, ← map_mul,
    firstAppend, appendR_apply, eSum_mul_oneConcat_singleton]
  intro a
  rw [mem_redOrderedSet, mem_redOrderedSet, isRedOrdered_append_black]

theorem commute_eSum_redOrderedSet_firstIdem :
    Commute (eSum S (redOrderedSet (ν₀ + {j} + ν'))) (firstIdem S ν₀ ν' j) := by
  rw [← castKLR_eSum_redOrderedSet (firstQuad_h ν₀ ν' j).symm, firstIdem, oneConcat]
  exact (commute_eSum_eSum _ _).map _

end Idempotents

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ₀ β : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aβ" => Multiset.map lastColour (stendhalWeight 1 β)
local notation "hA" => prefixWeight_addBlack (ℓ := ℓ) i θ₀
local notation "θ" => ((Si i) + θ₀)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))
local notation "P" => eSum S (redOrderedSet (Aₚ + {j} + Aβ))
local notation "P₁" => eSum S (redOrderedSet (Aₚ + Aβ))
local notation "e₁" => firstIdem S Aₚ Aβ j

omit [DecidableEq I] in
/-- A colour not in `β` is not a black colour of the last block. -/
theorem inl_notMem_lastWeight (hi : i ∉ β) : j ∉ Aβ := by
  simp [stendhalWeight, hi]

/-- `parabolicInputMap` intertwines appending a black strand to the first tensor factor with
`appendBlack ⊗ 1`, for an arbitrary last block. -/
theorem parabolicInputMap_tensorAppendL_left (t : TensorKLR S Aₚ Aβ) :
    parabolicInputMap Q Λ θ β (castTensor S hA rfl (tensorAppendL S Aₚ Aβ j t)) =
      parabolicAppendLeft Q Λ i θ₀ β (parabolicInputMap Q Λ θ₀ β t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [tensorAppendL_tmul, castTensor_tmul, castKLR_rfl]
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul, parabolicAppendLeft,
      NonUnitalAlgHom.tensorMap_tmul]
    rw [parabolicPrefixProjection_appendR]
    rfl

omit [DecidableEq I] in
/-- The weights `ν₀ + i + ν'` of the two factors with the last black strand. -/
theorem leftShuffle_weight :
    Aₚ + {j} + Aβ = Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ) + Aβ :=
  add_eq_add_of_eq hA rfl

/-- `appendBlack ⊗ 1` as a nonunital ring map, `D(θ₀, β) → D(i + θ₀, β)`. -/
abbrev leftAppendHom :
    parabolicFactorAlgebra Q Λ θ₀ β →ₙ+* parabolicFactorAlgebra Q Λ θ β :=
  NonUnitalRingHomClass.toNonUnitalRingHom (parabolicAppendLeft Q Λ i θ₀ β)

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]

/-- The input module of parabolic induction, viewed over `R(ν₀ + i) ⊗ R(ν')`. -/
def LeftInput := ParabolicInput Q Λ ((Si i) + θ₀) β N

/-- **`₁E_i N`**: restriction along `appendBlack ⊗ 1`. -/
abbrev LeftResLeft := Res (leftAppendHom Q Λ i θ₀ β) N

local notation "N₁" => LeftInput Q Λ i θ₀ β N
local notation "N₀" => ParabolicInput Q Λ ((Si i) + θ₀) β N
local notation "El" => LeftResLeft Q Λ i θ₀ β N

instance : AddCommGroup N₁ := inferInstanceAs (AddCommGroup N₀)
instance : Module k N₁ := inferInstanceAs (Module k N₀)
instance : Module (TensorKLR S (Aₚ + {Sum.inl i}) Aβ) N₁ :=
  Module.compHom N₀ (castTensor S hA rfl).toRingEquiv.toRingHom
instance : IsScalarTower k (TensorKLR S (Aₚ + {Sum.inl i}) Aβ) N₁ :=
  ⟨fun c t n => by
    change castTensor S hA rfl (c • t) • (show N₀ from n) =
      c • (castTensor S hA rfl t • (show N₀ from n))
    rw [map_smul, smul_assoc]⟩

instance : Module k El := Module.compHom _ (algebraMap k (parabolicFactorAlgebra Q Λ θ₀ β))
instance : IsScalarTower k (parabolicFactorAlgebra Q Λ θ₀ β) El where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (parabolicFactorAlgebra Q Λ θ₀ β) c) • (t • n)
    exact (congrArg (· • n) (Algebra.smul_def c t)).trans (mul_smul _ _ _)

/-- `LeftInput` is the input module. -/
def leftInputEquiv : N₁ ≃ₗ[k] N₀ := LinearEquiv.refl k N₀

/-- **The parabolic shuffle module as an induced module from `R(ν₀ + i) ⊗ R(ν')`.** -/
def leftShuffleEquiv :
    Ind S (Aₚ + {Sum.inl i}) Aβ N₁ ≃ₗ[k] ParabolicShuffle Q Λ θ β N :=
  indCast hA rfl (leftInputEquiv Q Λ i θ₀ β N) fun _ _ => rfl

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
theorem leftShuffleEquiv_smul (a : KLRAlgebra k S (Aₚ + {Sum.inl i} + Aβ))
    (y : Ind S (Aₚ + {Sum.inl i}) Aβ N₁) :
    leftShuffleEquiv Q Λ i θ₀ β N (a • y) =
      castKLR S (leftShuffle_weight i θ₀ β) a • leftShuffleEquiv Q Λ i θ₀ β N y :=
  indCast_smul (h := hA) (h' := rfl) (g := leftInputEquiv Q Λ i θ₀ β N) (hg := fun _ _ => rfl) a y

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
theorem tensorAppendL_smul_leftInput (t : TensorKLR S Aₚ Aβ) (n : N₁) :
    (show N from (tensorAppendL S Aₚ Aβ (Sum.inl i) t • n)) =
      parabolicAppendLeft Q Λ i θ₀ β (parabolicInputMap Q Λ θ₀ β t) • (show N from n) := by
  change parabolicInputMap Q Λ θ β (castTensor S hA rfl _) • (show N from n) = _
  rw [parabolicInputMap_tensorAppendL_left]

/-- `₁(LeftInput) ≅ ₁E_i N` as modules over `R(ν₀) ⊗ R(ν')`, along the input map. -/
def leftResLeftEquiv :
    ResFirst S Aₚ Aβ (Sum.inl i) N₁ ≃ₗ[k] ParabolicInput Q Λ θ₀ β El where
  toFun m := Res.mk (show N from m.val) (by
    have h := tensorAppendL_smul_leftInput Q Λ i θ₀ β N 1 m.val
    rw [map_one (parabolicInputMap Q Λ θ₀ β)] at h
    exact h.symm.trans m.prop)
  invFun m := Res.mk (show N₁ from m.val) (by
    have h := tensorAppendL_smul_leftInput Q Λ i θ₀ β N 1 (show N₁ from m.val)
    rw [map_one (parabolicInputMap Q Λ θ₀ β)] at h
    exact h.trans m.prop)
  left_inv _ := Res.ext rfl
  right_inv _ := Res.ext rfl
  map_add' _ _ := Res.ext rfl
  map_smul' c m := Res.ext
    ((tensorAppendL_smul_leftInput Q Λ i θ₀ β N (algebraMap k _ c) m.val).trans
      (by rw [AlgHom.commutes]; rfl))

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
theorem leftResLeftEquiv_smul (t : TensorKLR S Aₚ Aβ) (m : ResFirst S Aₚ Aβ (Sum.inl i) N₁) :
    leftResLeftEquiv Q Λ i θ₀ β N (t • m) =
      castTensor S rfl rfl t • leftResLeftEquiv Q Λ i θ₀ β N m :=
  Res.ext (tensorAppendL_smul_leftInput Q Λ i θ₀ β N t m.val)

local notation "Lf" => Algebra.lsmul k k (Ind S (Aₚ + {j}) Aβ N₁)
local notation "Lo" => Algebra.lsmul k k (Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁))

/-- The image of `1_{-,i}` in the parabolic shuffle module. -/
abbrev leftShuffleIdem : Module.End k (ParabolicShuffle Q Λ θ β N) :=
  parabolicShuffleAction Q Λ θ β N (castKLR S (leftShuffle_weight i θ₀ β) e₁)

/-- **The middle term**, transported to the parabolic shuffle module. -/
def leftMiddleEquiv :
    (Ind S (Aₚ + {j}) Aβ N₁ ⧸ LinearMap.ker (Lf P * Lf e₁)) ≃ₗ[k]
      (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * leftShuffleIdem Q Λ i θ₀ β N)) :=
  descendLinearEquiv _ _ (leftShuffleEquiv Q Λ i θ₀ β N) fun y => by
    simp only [Module.End.mul_apply, Algebra.lsmul_coe, leftShuffleEquiv_smul,
      castKLR_eSum_redOrderedSet, parabolicOrderedLoadings_eq_redOrderedSet]

/-- **The quotient term** `S(₁E_i N)`. -/
def leftOneEquiv :
    (Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁) ⧸ LinearMap.ker (Lo P₁)) ≃ₗ[k]
      ParabolicStandard Q Λ θ₀ β El :=
  descendLinearEquiv _ _
    (indCast rfl rfl (leftResLeftEquiv Q Λ i θ₀ β N) (leftResLeftEquiv_smul Q Λ i θ₀ β N))
    fun y => by
      simp only [Algebra.lsmul_coe, indCast_smul, castKLR_eSum_redOrderedSet,
        parabolicOrderedLoadings_eq_redOrderedSet]

variable (hQ : KLRSymm Q)

/-- `S(₁E_i N)` is the middle term of the last-strand sequence when `i ∉ β`. -/
def leftStandardOneEquiv (hi : i ∉ β) :
    ParabolicStandard Q Λ θ₀ β El ≃ₗ[k]
      (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * leftShuffleIdem Q Λ i θ₀ β N)) :=
  (leftOneEquiv Q Λ i θ₀ β N).symm.trans
    ((firstSidedDescendEquiv (N := N₁) (eSum_idem _)
      (commute_eSum_redOrderedSet_firstIdem Aₚ Aβ i)
      (eSum_redOrderedSet_mul_firstIdem Aₚ Aβ i) (inl_notMem_lastWeight i β hi)
      (stendhalQ_swap_symm Q Λ hQ)).trans (leftMiddleEquiv Q Λ i θ₀ β N))

theorem leftShuffle_commute :
    Commute (lastShuffleOrdered Q Λ θ β N) (leftShuffleIdem Q Λ i θ₀ β N) := by
  have h := (commute_eSum_redOrderedSet_firstIdem (Q := Q) (Λ := Λ) Aₚ Aβ i).map
    (castKLR S (leftShuffle_weight i θ₀ β))
  rw [castKLR_eSum_redOrderedSet, ← parabolicOrderedLoadings_eq_redOrderedSet] at h
  exact h.map _

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
theorem leftShuffleIdem_idem : IsIdempotentElem (leftShuffleIdem Q Λ i θ₀ β N) := by
  unfold IsIdempotentElem
  rw [leftShuffleIdem, ← map_mul, ← map_mul, firstIdem_mul_self]

/-- The element `1_{-,i}` of `T(θ + β)`. -/
def leftBlackIdem : TensorProductAlgebra k Q Λ (θ + β) :=
  TensorProductAlgebra.mk Q Λ (θ + β) (orderProjection Q Λ (θ + β)
    (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)
      (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β)
        (castKLR S (leftShuffle_weight i θ₀ β) e₁))))

/-- On standardization, `1_{-,i}` acts by the operator induced by `e`. -/
theorem leftInducedOp_eq :
    (inducedOp _ _ (leftShuffle_commute Q Λ i θ₀ β N) :
        Module.End k (ParabolicStandard Q Λ θ β N)) =
      parabolicStandardAction Q Λ θ β N hQ (leftBlackIdem Q Λ i θ₀ β) := by
  rw [leftBlackIdem, parabolicStandardAction_affine]
  exact Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The `1_{-,i}`-fixed part of standardization `S N`. -/
abbrev LeftStandardFixed : Submodule k (ParabolicStandard Q Λ θ β N) :=
  LinearMap.ker (parabolicStandardAction Q Λ θ β N hQ (leftBlackIdem Q Λ i θ₀ β) -
    LinearMap.id)

/-- **The middle term is the `1_{-,i}`-fixed part of `S N`.** -/
def leftStandardMiddleEquiv :
    (ParabolicShuffle Q Λ θ β N ⧸
        LinearMap.ker (lastShuffleOrdered Q Λ θ β N * leftShuffleIdem Q Λ i θ₀ β N)) ≃ₗ[k]
      LeftStandardFixed Q Λ i θ₀ β N hQ :=
  (rangeEquiv _ _ (leftShuffleIdem_idem Q Λ i θ₀ β N)
    (leftShuffle_commute Q Λ i θ₀ β N)).trans
    (LinearEquiv.ofEq _ _ (congrArg (fun f => LinearMap.ker (f - LinearMap.id))
      (leftInducedOp_eq Q Λ i θ₀ β N hQ)))

omit [DecidableEq I] in
/-- The weights `i + (θ₀ + β)` and `θ + β` agree. -/
theorem leftBlack_weight : (Si i) + (θ₀ + β) = θ + β := (add_assoc _ _ _).symm

/-- **The idempotent `1_{-,i}` is Webster's `E_i` idempotent** `appendBlack 1` of
`T(i + (θ₀ + β))`, transported to `T(θ + β)`. -/
theorem castTensorProductAlgebra_appendBlack_one_left :
    castTensorProductAlgebra Q Λ (leftBlack_weight i θ₀ β) (appendBlack Q Λ i (θ₀ + β) 1) =
      leftBlackIdem Q Λ i θ₀ β := by
  rw [appendBlack_one_eq_oneConcat, castTensorProductAlgebra_mk, leftBlackIdem, firstIdem,
    castKLR_castKLR, castKLR_castKLR, castKLR_castKLR]
  exact congrArg (tensorOfKLR Q Λ _)
    (castKLR_oneConcat_eq (parabolicInputWeights_add (ℓ := ℓ) θ₀ β).symm _ _)

/-- The action of `T(i + (θ₀ + β))` on standardization `S N`. -/
def leftStandardTAction :
    TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β)) →ₐ[k]
      Module.End k (ParabolicStandard Q Λ θ β N) :=
  (parabolicStandardAction Q Λ θ β N hQ).comp
    (castTensorProductAlgebra Q Λ (leftBlack_weight i θ₀ β)).toAlgHom

/-- Standardization `S N` viewed as a module over `T(i + (θ₀ + β))`. -/
def LeftStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ β N

instance : AddCommGroup (LeftStandardT Q Λ i θ₀ β N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ β N))
instance : Module k (LeftStandardT Q Λ i θ₀ β N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β N))
instance : Module (TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β)))
    (LeftStandardT Q Λ i θ₀ β N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ β N) (leftStandardTAction Q Λ i θ₀ β N hQ).toRingHom
instance : IsScalarTower k (TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β)))
    (LeftStandardT Q Λ i θ₀ β N hQ) :=
  ⟨fun c t m => by
    change leftStandardTAction Q Λ i θ₀ β N hQ (c • t) m =
      c • leftStandardTAction Q Λ i θ₀ β N hQ t m
    rw [map_smul]
    rfl⟩

theorem appendBlack_one_smul_leftStandardT (m : ParabolicStandard Q Λ θ β N) :
    (appendBlack Q Λ i (θ₀ + β) 1 • (show LeftStandardT Q Λ i θ₀ β N hQ from m) :
        ParabolicStandard Q Λ θ β N) =
      parabolicStandardAction Q Λ θ β N hQ (leftBlackIdem Q Λ i θ₀ β) m := by
  change parabolicStandardAction Q Λ θ β N hQ
    (castTensorProductAlgebra Q Λ (leftBlack_weight i θ₀ β) (appendBlack Q Λ i (θ₀ + β) 1)) m = _
  rw [castTensorProductAlgebra_appendBlack_one_left]

theorem mem_leftStandardFixed_iff (m : ParabolicStandard Q Λ θ β N) :
    m ∈ LeftStandardFixed Q Λ i θ₀ β N hQ ↔
      parabolicStandardAction Q Λ θ β N hQ (leftBlackIdem Q Λ i θ₀ β) m = m := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]

/-- `E_i(S N)` is the `1_{-,i}`-fixed part of `S N`. -/
def leftBlackFixedEquiv :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ) ≃ₗ[k]
      LeftStandardFixed Q Λ i θ₀ β N hQ where
  toFun m := ⟨show ParabolicStandard Q Λ θ β N from m.1,
    (mem_leftStandardFixed_iff Q Λ i θ₀ β N hQ _).2
      ((appendBlack_one_smul_leftStandardT Q Λ i θ₀ β N hQ m.1).symm.trans m.2)⟩
  invFun m := ⟨show LeftStandardT Q Λ i θ₀ β N hQ from m.1,
    (appendBlack_one_smul_leftStandardT Q Λ i θ₀ β N hQ m.1).trans
      ((mem_leftStandardFixed_iff Q Λ i θ₀ β N hQ _).1 m.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Webster, Prop 5.5, `E`-part, `i ∉ β`:** for `θ = i + θ₀` and `i ∉ β`,
`E_i(S N) ≅ S(₁E_i N)`. -/
def leftBlackResEquiv (hi : i ∉ β) :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ) ≃ₗ[k]
      ParabolicStandard Q Λ θ₀ β El :=
  (leftBlackFixedEquiv Q Λ i θ₀ β N hQ).trans
    ((leftStandardMiddleEquiv Q Λ i θ₀ β N hQ).symm.trans
      (leftStandardOneEquiv Q Λ i θ₀ β N hQ hi).symm)

end Categorification.Stendhal
