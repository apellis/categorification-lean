/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackLinear
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackMissing

/-!
# `E_i` of standardization over the tensor product algebra, one block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part, in the cases where the colour `i` occurs in one block only.

* For `θ = i + θ₀` and `i ∉ β`, the isomorphism `E_i(S N) ≅ S(₁E_i N)` of
  `ParabolicStandardLastLeft.lean` is `T(θ₀ + β)`-linear (`leftBlackResEquivT`).
* For `β = i + β₀` and `i ∉ θ`, the isomorphism `E_i(S N) ≅ S(₂E_i N)` of
  `ParabolicStandardLastRight.lean` is `T(θ + β₀)`-linear (`rightBlackResEquivT`).

Here `E_i(S N)` carries the action of `BlackRes` (through `appendBlack`), and the
standardizations carry the standardization action (`ParabolicStandardT`). As in
`ParabolicStandardLastBlackLinear.lean`, the proof reduces to images of KLR diagrams `c`, on
which `Ψ` (resp. `Φ`) intertwines `c` with `ι(c ⊗ 1_i)` (`indFirst_smul`, `indAppend_smul`).
Linearity is checked on the inverse maps, which are explicit on classes. Gradings are not
modelled.

## Main definitions

* `leftBlackResEquivT`, `rightBlackResEquivT`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))

section Left

variable (θ₀ β : Multiset I)

local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aβ" => Multiset.map lastColour (stendhalWeight 1 β)
local notation "θ" => ((Si i) + θ₀)
local notation "hW" => parabolicInputWeights_add (ℓ := ℓ) θ₀ β

/-- The idempotent `1_{-,i}` of `R(ν₀ + i + ν')` commutes with `ι(c ⊗ 1_i)`. -/
theorem firstIdem_commute_firstAppend (c : KLRAlgebra k S (Aₚ + Aβ)) :
    firstIdem S Aₚ Aβ j * firstAppend j c = firstAppend j c * firstIdem S Aₚ Aβ j := by
  rw [firstIdem, firstAppend, ← map_mul, ← map_mul, ← appendR_one, ← map_mul, ← map_mul,
    one_mul, mul_one]

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  (hQ : KLRSymm Q)

local notation "N₁" => LeftInput Q Λ i θ₀ β N
local notation "El" => LeftResLeft Q Λ i θ₀ β N
local notation "Tl" => TensorProductAlgebra k Q Λ (θ₀ + β)
local notation "Jl" => indCast rfl rfl (leftResLeftEquiv Q Λ i θ₀ β N)
  (leftResLeftEquiv_smul Q Λ i θ₀ β N)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
/-- The image of `1_{-,i}` in the parabolic shuffle module commutes with `ι(c ⊗ 1_i)`. -/
theorem leftShuffleIdem_smul_firstAppend (c : KLRAlgebra k S (Aₚ + Aβ))
    (w : ParabolicShuffle Q Λ θ β N) :
    leftShuffleIdem Q Λ i θ₀ β N (castKLR S (leftShuffle_weight i θ₀ β) (firstAppend j c) • w) =
      castKLR S (leftShuffle_weight i θ₀ β) (firstAppend j c) •
        leftShuffleIdem Q Λ i θ₀ β N w := by
  change castKLR S (leftShuffle_weight i θ₀ β) (firstIdem S Aₚ Aβ j) •
      castKLR S (leftShuffle_weight i θ₀ β) (firstAppend j c) • w =
    castKLR S (leftShuffle_weight i θ₀ β) (firstAppend j c) •
      castKLR S (leftShuffle_weight i θ₀ β) (firstIdem S Aₚ Aβ j) • w
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, firstIdem_commute_firstAppend]

/-- On `E_i(S N)`, `i ∉ β`, the image of a diagram `c` acts as `ι(c ⊗ 1_i)`. -/
theorem leftBlackRes_smul_val (c : KLRAlgebra k S (Aₚ + Aβ))
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ))
    (x : ParabolicShuffle Q Λ θ β N)
    (hx : (m.1 : ParabolicStandard Q Λ θ β N) = Submodule.Quotient.mk x) :
    ((tensorOfKLR Q Λ (θ₀ + β) (castKLR S hW c) • m).1 : ParabolicStandard Q Λ θ β N) =
      Submodule.Quotient.mk (castKLR S (leftShuffle_weight i θ₀ β) (firstAppend j c) • x) := by
  have h' : Aₚ + Aβ + {j} = stendhalWeight (ℓ + 1) ((Si i) + (θ₀ + β)) :=
    (congrArg (· + {j}) hW).trans (stendhalWeight_addBlack i (θ₀ + β))
  change parabolicStandardAction Q Λ θ β N hQ (castTensorProductAlgebra Q Λ
    (leftBlack_weight i θ₀ β) (appendBlack Q Λ i (θ₀ + β) (tensorOfKLR Q Λ (θ₀ + β)
      (castKLR S hW c)))) m.1 = _
  rw [hx, appendBlack_tensorOfKLR_castKLR Q Λ i (θ₀ + β) _ h',
    castTensorProductAlgebra_tensorOfKLR_castKLR Q Λ (leftBlack_weight i θ₀ β) h'
      (h'.trans (congrArg (stendhalWeight (ℓ + 1)) (leftBlack_weight i θ₀ β))),
    parabolicStandardAction_tensorOfKLR Q Λ θ β N hQ _
      ((firstQuad_h Aₚ Aβ j).symm.trans (leftShuffle_weight i θ₀ β)),
    firstAppend, castKLR_castKLR]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
/-- On `S(₁E_i N)`, the image of a diagram `c` acts as `c`. -/
theorem leftStandardT_smul_mk (c : KLRAlgebra k S (Aₚ + Aβ))
    (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    (tensorOfKLR Q Λ (θ₀ + β) (castKLR S hW c) •
        (show ParabolicStandardT Q Λ θ₀ β El hQ from Submodule.Quotient.mk (Jl y))) =
      (Submodule.Quotient.mk (Jl (c • y)) : ParabolicStandard Q Λ θ₀ β El) := by
  change parabolicStandardAction Q Λ θ₀ β El hQ
    (tensorOfKLR Q Λ (θ₀ + β) (castKLR S hW c)) _ = _
  rw [parabolicStandardAction_tensorOfKLR Q Λ θ₀ β El hQ _ rfl, indCast_smul]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N] in
/-- The isomorphism `Ind_{ν₀,ν'} ₁N / ker P₁ ≅ S(₁E_i N)` on a class. -/
theorem leftOneEquiv_mk (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    leftOneEquiv Q Λ i θ₀ β N (Submodule.Quotient.mk y) =
      (Submodule.Quotient.mk (Jl y) : ParabolicStandard Q Λ θ₀ β El) :=
  descendLinearEquiv_mk _ _ _ _ y

/-- The isomorphism `S(₁E_i N) ≅ Ind_{ν,ν'} N / ker (P e)`, `i ∉ β`, on a class. -/
theorem leftStandardOneEquiv_mk (hi : i ∉ β) (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    leftStandardOneEquiv Q Λ i θ₀ β N hQ hi (Submodule.Quotient.mk (Jl y)) =
      Submodule.Quotient.mk (leftShuffleEquiv Q Λ i θ₀ β N
        (indFirst N₁ (inl_notMem_lastWeight i β hi) y)) := by
  rw [← leftOneEquiv_mk]
  exact congrArg ((firstSidedDescendEquiv (N := N₁) (eSum_idem _)
      (commute_eSum_redOrderedSet_firstIdem Aₚ Aβ i)
      (eSum_redOrderedSet_mul_firstIdem Aₚ Aβ i) (inl_notMem_lastWeight i β hi)
      (stendhalQ_swap_symm Q Λ hQ)).trans (leftMiddleEquiv Q Λ i θ₀ β N))
    ((leftOneEquiv Q Λ i θ₀ β N).symm_apply_apply (Submodule.Quotient.mk y))

/-- The inverse of `E_i(S N) ≅ S(₁E_i N)` on a class. -/
theorem leftBlackResEquiv_symm_mk (hi : i ∉ β) (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    (((leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm (Submodule.Quotient.mk (Jl y))).1 :
        ParabolicStandard Q Λ θ β N) =
      Submodule.Quotient.mk (leftShuffleIdem Q Λ i θ₀ β N (leftShuffleEquiv Q Λ i θ₀ β N
        (indFirst N₁ (inl_notMem_lastWeight i β hi) y))) := by
  change ((leftBlackFixedEquiv Q Λ i θ₀ β N hQ).symm (leftStandardMiddleEquiv Q Λ i θ₀ β N hQ
    (leftStandardOneEquiv Q Λ i θ₀ β N hQ hi (Submodule.Quotient.mk (Jl y))))).1 = _
  rw [leftStandardOneEquiv_mk]
  rfl

/-- `S(₁E_i N) → S N` on shuffle modules intertwines `c` with `ι(c ⊗ 1_i)`. -/
theorem leftShuffleEquiv_indFirst_smul (hi : i ∉ β) (c : KLRAlgebra k S (Aₚ + Aβ))
    (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    leftShuffleEquiv Q Λ i θ₀ β N (indFirst N₁ (inl_notMem_lastWeight i β hi) (c • y)) =
      castKLR S (leftShuffle_weight i θ₀ β) (firstAppend j c) •
        leftShuffleEquiv Q Λ i θ₀ β N (indFirst N₁ (inl_notMem_lastWeight i β hi) y) := by
  rw [indFirst_smul]
  exact leftShuffleEquiv_smul Q Λ i θ₀ β N _ _

/-- The inverse of `E_i(S N) ≅ S(₁E_i N)` is `T(θ₀ + β)`-linear. -/
theorem leftBlackResEquiv_symm_smul (hi : i ∉ β) (t : Tl)
    (z : ParabolicStandardT Q Λ θ₀ β El hQ) :
    (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm (t • z) =
      t • (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm z := by
  obtain ⟨c, rfl⟩ := exists_tensorOfKLR_castKLR_eq Q Λ (θ₀ + β) hW t
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _
    (show ParabolicStandard Q Λ θ₀ β El from z)
  obtain ⟨y, rfl⟩ := (Jl).surjective w
  rw [leftStandardT_smul_mk]
  apply Subtype.ext
  rw [leftBlackRes_smul_val Q Λ i θ₀ β N hQ c _ _
      (leftBlackResEquiv_symm_mk Q Λ i θ₀ β N hQ hi y),
    leftBlackResEquiv_symm_mk, leftShuffleEquiv_indFirst_smul Q Λ i θ₀ β N hi]
  exact congrArg Submodule.Quotient.mk (leftShuffleIdem_smul_firstAppend Q Λ i θ₀ β N c _)

/-- **Webster, Prop 5.5, `E`-part, `i ∉ β`, over `T(θ₀ + β)`** (arXiv:1309.3796v3, proof of
Proposition 5.5): for `θ = i + θ₀` and `i ∉ β`, `E_i(S N) ≅ S(₁E_i N)` as `T(θ₀ + β)`-modules.
The underlying map is `leftBlackResEquiv`. -/
def leftBlackResEquivT (hi : i ∉ β) :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ) ≃ₗ[Tl]
      ParabolicStandardT Q Λ θ₀ β El hQ where
  toFun := leftBlackResEquiv Q Λ i θ₀ β N hQ hi
  invFun := (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm
  left_inv := (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).left_inv
  right_inv := (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).right_inv
  map_add' := map_add (leftBlackResEquiv Q Λ i θ₀ β N hQ hi)
  map_smul' t m := by
    apply (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm.injective
    change _ = (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm
      (t • (show ParabolicStandardT Q Λ θ₀ β El hQ from leftBlackResEquiv Q Λ i θ₀ β N hQ hi m))
    rw [leftBlackResEquiv_symm_smul, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]

@[simp]
theorem leftBlackResEquivT_apply (hi : i ∉ β)
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ)) :
    (leftBlackResEquivT Q Λ i θ₀ β N hQ hi m : ParabolicStandard Q Λ θ₀ β El) =
      leftBlackResEquiv Q Λ i θ₀ β N hQ hi m := rfl

@[simp]
theorem leftBlackResEquivT_symm_apply (hi : i ∉ β) (z : ParabolicStandardT Q Λ θ₀ β El hQ) :
    (leftBlackResEquivT Q Λ i θ₀ β N hQ hi).symm z =
      (leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm z := rfl

end Left

section Right

variable (θ β₀ : Multiset I)

local notation "Aθ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "β" => ((Si i) + β₀)
local notation "hW" => parabolicInputWeights_add (ℓ := ℓ) θ β₀

/-- The idempotent `1_{-,i}` of `R(ν + ν₀' + i)` commutes with `ι(c ⊗ 1_i)`. -/
theorem lastIdemOf_commute_appendR (c : KLRAlgebra k S (Aθ + Aₗ)) :
    lastIdemOf S Aθ Aₗ j * castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c) =
      castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c) * lastIdemOf S Aθ Aₗ j := by
  rw [lastIdemOf, ← map_mul, ← map_mul, ← appendR_one, ← map_mul, ← map_mul, one_mul,
    mul_one]

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  (hQ : KLRSymm Q)

local notation "N₁" => RightInput Q Λ i θ β₀ N
local notation "Er" => RightResRight Q Λ i θ β₀ N
local notation "Tr" => TensorProductAlgebra k Q Λ (θ + β₀)
local notation "Jr" => indCast rfl rfl (rightResRightEquiv Q Λ i θ β₀ N)
  (rightResRightEquiv_smul Q Λ i θ β₀ N)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N] in
/-- The image of `1_{-,i}` in the parabolic shuffle module commutes with `ι(c ⊗ 1_i)`. -/
theorem rightShuffleIdem_smul_appendR (c : KLRAlgebra k S (Aθ + Aₗ))
    (w : ParabolicShuffle Q Λ θ β N) :
    rightShuffleIdem Q Λ i θ β₀ N (castKLR S (rightShuffle_weight i θ β₀)
        (castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c)) • w) =
      castKLR S (rightShuffle_weight i θ β₀)
        (castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c)) •
          rightShuffleIdem Q Λ i θ β₀ N w := by
  change castKLR S (rightShuffle_weight i θ β₀) (lastIdemOf S Aθ Aₗ j) •
      castKLR S (rightShuffle_weight i θ β₀)
        (castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c)) • w =
    castKLR S (rightShuffle_weight i θ β₀)
        (castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c)) •
      castKLR S (rightShuffle_weight i θ β₀) (lastIdemOf S Aθ Aₗ j) • w
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, lastIdemOf_commute_appendR]

/-- On `E_i(S N)`, `i ∉ θ`, the image of a diagram `c` acts as `ι(c ⊗ 1_i)`. -/
theorem rightBlackRes_smul_val (c : KLRAlgebra k S (Aθ + Aₗ))
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ))
    (x : ParabolicShuffle Q Λ θ β N)
    (hx : (m.1 : ParabolicStandard Q Λ θ β N) = Submodule.Quotient.mk x) :
    ((tensorOfKLR Q Λ (θ + β₀) (castKLR S hW c) • m).1 : ParabolicStandard Q Λ θ β N) =
      Submodule.Quotient.mk (castKLR S (rightShuffle_weight i θ β₀)
        (castKLR S (add_assoc Aθ Aₗ {j}) (appendR S _ j c)) • x) := by
  have h' : Aθ + Aₗ + {j} = stendhalWeight (ℓ + 1) ((Si i) + (θ + β₀)) :=
    (congrArg (· + {j}) hW).trans (stendhalWeight_addBlack i (θ + β₀))
  change parabolicStandardAction Q Λ θ β N hQ (castTensorProductAlgebra Q Λ
    (rightBlack_weight i θ β₀) (appendBlack Q Λ i (θ + β₀) (tensorOfKLR Q Λ (θ + β₀)
      (castKLR S hW c)))) m.1 = _
  rw [hx, appendBlack_tensorOfKLR_castKLR Q Λ i (θ + β₀) _ h',
    castTensorProductAlgebra_tensorOfKLR_castKLR Q Λ (rightBlack_weight i θ β₀) h'
      (h'.trans (congrArg (stendhalWeight (ℓ + 1)) (rightBlack_weight i θ β₀))),
    parabolicStandardAction_tensorOfKLR Q Λ θ β N hQ _
      ((add_assoc _ _ _).trans (rightShuffle_weight i θ β₀)),
    castKLR_castKLR]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N] in
/-- On `S(₂E_i N)`, the image of a diagram `c` acts as `c`. -/
theorem rightStandardT_smul_mk (c : KLRAlgebra k S (Aθ + Aₗ))
    (y : Ind S Aθ Aₗ (ResRight S Aθ Aₗ j N₁)) :
    (tensorOfKLR Q Λ (θ + β₀) (castKLR S hW c) •
        (show ParabolicStandardT Q Λ θ β₀ Er hQ from Submodule.Quotient.mk (Jr y))) =
      (Submodule.Quotient.mk (Jr (c • y)) : ParabolicStandard Q Λ θ β₀ Er) := by
  change parabolicStandardAction Q Λ θ β₀ Er hQ
    (tensorOfKLR Q Λ (θ + β₀) (castKLR S hW c)) _ = _
  rw [parabolicStandardAction_tensorOfKLR Q Λ θ β₀ Er hQ _ rfl, indCast_smul]

/-- The inverse of `E_i(S N) ≅ S(₂E_i N)` on a class. -/
theorem rightBlackResEquiv_symm_mk (hi : i ∉ θ) (y : Ind S Aθ Aₗ (ResRight S Aθ Aₗ j N₁)) :
    (((rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm (Submodule.Quotient.mk (Jr y))).1 :
        ParabolicStandard Q Λ θ β N) =
      Submodule.Quotient.mk (rightShuffleIdem Q Λ i θ β₀ N (rightShuffleEquiv Q Λ i θ β₀ N
        (indAppend (Q := S) (ν := Aθ) (ν₀' := Aₗ) (i := j) (N := N₁) y))) := by
  have h : (rightTwoEquiv Q Λ i θ β₀ N).symm (Submodule.Quotient.mk (Jr y)) =
      Submodule.Quotient.mk y := (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [rightBlackResEquiv, rightStandardTwoEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, h]
  rfl

/-- The inverse of `E_i(S N) ≅ S(₂E_i N)` is `T(θ + β₀)`-linear. -/
theorem rightBlackResEquiv_symm_smul (hi : i ∉ θ) (t : Tr)
    (z : ParabolicStandardT Q Λ θ β₀ Er hQ) :
    (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm (t • z) =
      t • (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm z := by
  obtain ⟨c, rfl⟩ := exists_tensorOfKLR_castKLR_eq Q Λ (θ + β₀) hW t
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _
    (show ParabolicStandard Q Λ θ β₀ Er from z)
  obtain ⟨y, rfl⟩ := (Jr).surjective w
  rw [rightStandardT_smul_mk]
  apply Subtype.ext
  rw [rightBlackRes_smul_val Q Λ i θ β₀ N hQ c _ _
      (rightBlackResEquiv_symm_mk Q Λ i θ β₀ N hQ hi y),
    rightBlackResEquiv_symm_mk, indAppend_smul, rightShuffleEquiv_smul,
    rightShuffleIdem_smul_appendR]

/-- **Webster, Prop 5.5, `E`-part, `i ∉ θ`, over `T(θ + β₀)`** (arXiv:1309.3796v3, proof of
Proposition 5.5): for `β = i + β₀` and `i ∉ θ`, `E_i(S N) ≅ S(₂E_i N)` as `T(θ + β₀)`-modules.
The underlying map is `rightBlackResEquiv`. -/
def rightBlackResEquivT (hi : i ∉ θ) :
    BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ) ≃ₗ[Tr]
      ParabolicStandardT Q Λ θ β₀ Er hQ where
  toFun := rightBlackResEquiv Q Λ i θ β₀ N hQ hi
  invFun := (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm
  left_inv := (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).left_inv
  right_inv := (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).right_inv
  map_add' := map_add (rightBlackResEquiv Q Λ i θ β₀ N hQ hi)
  map_smul' t m := by
    apply (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm.injective
    change _ = (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm
      (t • (show ParabolicStandardT Q Λ θ β₀ Er hQ from
        rightBlackResEquiv Q Λ i θ β₀ N hQ hi m))
    rw [rightBlackResEquiv_symm_smul, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]

@[simp]
theorem rightBlackResEquivT_apply (hi : i ∉ θ)
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ)) :
    (rightBlackResEquivT Q Λ i θ β₀ N hQ hi m : ParabolicStandard Q Λ θ β₀ Er) =
      rightBlackResEquiv Q Λ i θ β₀ N hQ hi m := rfl

@[simp]
theorem rightBlackResEquivT_symm_apply (hi : i ∉ θ) (z : ParabolicStandardT Q Λ θ β₀ Er hQ) :
    (rightBlackResEquivT Q Λ i θ β₀ N hQ hi).symm z =
      (rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm z := rfl

end Right

end Categorification.Stendhal
