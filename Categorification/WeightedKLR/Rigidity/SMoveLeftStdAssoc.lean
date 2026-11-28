/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveCutParabolic
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorAssoc

/-!
# The left module of the S-move as a standardization of the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, with the partial standardizations of §5.1. Let `M` be a module over
`T^{λ_2}(β_1) ⊗ T^{λ_3}(β_2)`. The module `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M))` of the
S-move (`SMove.leftStd`) is the partial standardization with three blocks `{1}, {2}, {3}` of
`P_∅ ⊠ M`, standardized at the inner cut first. By the independence of the order of the cuts
(`blocksStandardAssocEquiv`) it is the standardization at the last red strand of the module
`𝕊^{λ_1; λ_2}(P_∅ ⊠ M)` over `T^{λ_1, λ_2}(β_1) ⊗ T^{λ_3}(β_2)`, that is, a standard layer
`S(−)` over `T^λ` (`SMove.leftStdCutLayerIso`). This is the form in which the left module
enters the Tor lemmas for standardizations.

Since `P_∅ = T^{λ_1}(0)` is the ground field (`tensorProductAlgebraZeroEquiv`), the factor
`P_∅ ⊠ −` is removed by its augmentation (`extTensorScalarEquiv`, `blocksMidScalarEquiv`).

## Main definitions

* `extTensorScalarEquiv`: `A ⊠ X ≅ X` for an algebra `A ≅ k`.
* `blocksMidScalarEquiv`: the inner standardization of `A ⊠ M` is that of `M`, when `A ≅ k`.
* `SMove.leftStdBlocksEquiv`: `SMove.leftStd (𝕊(M))` is the partial standardization with three
  blocks of `P_∅ ⊠ M`.
* `SMove.leftStdCutEquiv`: `SMove.leftStd (𝕊(M)) ≅ 𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ M))`.
* `SMove.leftStdCutLayerIso`: `SMove.leftStd (𝕊(M)) ≅ S(𝕊^{λ_1; λ_2}(P_∅ ⊠ M))`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-! ### Removing a factor isomorphic to the ground field -/

section Scalar

variable {k A : Type} [Field k] [Ring A] [Algebra k A] (ε : A ≃ₐ[k] k)
  (X : Type) [AddCommGroup X] [Module k X]

/-- **`A ⊠ X ≅ X`** for an algebra `A ≅ k`: `a ⊗ x ↦ ε(a) x`. -/
def extTensorScalarEquiv : ExtTensor k A X ≃ₗ[k] X :=
  (TensorProduct.congr ε.toLinearEquiv (LinearEquiv.refl k X)).trans (TensorProduct.lid k X)

theorem extTensorScalarEquiv_tmul (a : A) (x : X) :
    extTensorScalarEquiv ε X (ExtTensor.tmul a x) = ε a • x := rfl

theorem extTensorScalarEquiv_smul {B : Type} [Ring B] [Algebra k B] [Module B X]
    [IsScalarTower k B X] (a : A) (b : B) (x : ExtTensor k A X) :
    extTensorScalarEquiv ε X ((a ⊗ₜ[k] b : A ⊗[k] B) • x) =
      ε a • b • extTensorScalarEquiv ε X x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero, smul_zero]
  | tmul p q =>
    rw [ExtTensor.smul_tmul, extTensorScalarEquiv_tmul, extTensorScalarEquiv_tmul,
      smul_eq_mul, map_mul, mul_smul, smul_comm b (ε p) q]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

end Scalar

/-! ### The inner standardization of `A ⊠ M` for `A ≅ k` -/

section Blocks

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {a m r : ℕ} (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)
  (ε : blocksHeadAlgebra Q Λ θ ≃ₐ[k] k)
  (M : Type) [AddCommGroup M] [Module k M]
  [Module (cutFactorAlgebra Q (blocksTailLabels Λ) β γ) M]
  [IsScalarTower k (cutFactorAlgebra Q (blocksTailLabels Λ) β γ) M]

local notation "A₀" => blocksHeadAlgebra Q Λ θ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksTailLabels Λ) β γ
local notation "Tᵢ" => TensorProductAlgebra k Q (blocksTailLabels Λ) (β + γ)

/-- The augmentation `A ⊠ M ≅ M`, as a map of modules over the last two blocks. -/
def blocksInnerScalarEquiv :
    BlocksInner Q Λ θ β γ (ExtTensor k A₀ M) ≃ₗ[Dᵢ] M where
  toFun n := extTensorScalarEquiv ε M n
  invFun n := (extTensorScalarEquiv ε M).symm n
  left_inv n := (extTensorScalarEquiv ε M).symm_apply_apply n
  right_inv n := (extTensorScalarEquiv ε M).apply_symm_apply n
  map_add' n n' := map_add (extTensorScalarEquiv ε M) n n'
  map_smul' d n := by
    change extTensorScalarEquiv ε M (((1 : A₀) ⊗ₜ[k] d : A₀ ⊗[k] Dᵢ) •
      (show ExtTensor k A₀ M from n)) = d • extTensorScalarEquiv ε M n
    rw [extTensorScalarEquiv_smul, map_one, one_smul]

theorem blocksInnerScalarEquiv_head (t : A₀) (n : BlocksInner Q Λ θ β γ (ExtTensor k A₀ M)) :
    blocksInnerScalarEquiv Q Λ θ β γ ε M (blocksHeadEnd Q Λ θ β γ _ t n) =
      ε t • blocksInnerScalarEquiv Q Λ θ β γ ε M n := by
  change extTensorScalarEquiv ε M ((t ⊗ₜ[k] (1 : Dᵢ) : A₀ ⊗[k] Dᵢ) •
    (show ExtTensor k A₀ M from n)) = _
  rw [extTensorScalarEquiv_smul, one_smul]
  rfl

variable (hQ : KLRSymm Q)

/-- **The inner standardization of `A ⊠ M` is that of `M`**, for `A ≅ k`. -/
def blocksMidScalarEquiv :
    BlocksMid Q Λ θ β γ (ExtTensor k A₀ M) hQ ≃ₗ[k]
      CutStandard Q (blocksTailLabels Λ) β γ M :=
  cutStandardMapEquiv Q (blocksTailLabels Λ) β γ (blocksInnerScalarEquiv Q Λ θ β γ ε M)

theorem blocksMidScalarEquiv_smul (t : A₀) (u : Tᵢ)
    (z : BlocksMid Q Λ θ β γ (ExtTensor k A₀ M) hQ) :
    blocksMidScalarEquiv Q Λ θ β γ ε M hQ
        ((t ⊗ₜ[k] u : cutFactorAlgebra Q Λ θ (β + γ)) • z) =
      ε t • cutStandardAction Q (blocksTailLabels Λ) β γ M hQ u
        (blocksMidScalarEquiv Q Λ θ β γ ε M hQ z) := by
  let h := (blocksInnerScalarEquiv Q Λ θ β γ ε M).toLinearMap
  let w := cutStandardAction Q (blocksTailLabels Λ) β γ _ hQ u z
  have hcomp : h ∘ₗ blocksHeadEnd Q Λ θ β γ _ t =
      (ε t • (LinearMap.id : M →ₗ[Dᵢ] M)) ∘ₗ h :=
    LinearMap.ext fun n => blocksInnerScalarEquiv_head Q Λ θ β γ ε M t n
  change cutStandardMap Q (blocksTailLabels Λ) β γ h
      (cutStandardMap Q (blocksTailLabels Λ) β γ (blocksHeadEnd Q Λ θ β γ _ t) w) = _
  refine (cutStandardMap_comp Q (blocksTailLabels Λ) β γ
    (blocksHeadEnd Q Λ θ β γ _ t) h w).symm.trans ?_
  refine (congrArg (fun g => cutStandardMap Q (blocksTailLabels Λ) β γ g w) hcomp).trans ?_
  refine (cutStandardMap_comp Q (blocksTailLabels Λ) β γ h _ w).trans ?_
  refine (cutStandardMap_smul_id Q (blocksTailLabels Λ) β γ (ε t) _).trans ?_
  exact congrArg (ε t • ·) (cutStandardMap_action Q (blocksTailLabels Λ) β γ hQ h u z)

variable {X : Type} [AddCommGroup X] [Module k X]
  [Module (TensorProductAlgebra k Q (blocksTailLabels Λ) (β + γ)) X]
  [IsScalarTower k (TensorProductAlgebra k Q (blocksTailLabels Λ) (β + γ)) X]
  (ψ : X ≃ₗ[k] CutStandard Q (blocksTailLabels Λ) β γ M)
  (hψ : ∀ (u : TensorProductAlgebra k Q (blocksTailLabels Λ) (β + γ)) (x : X),
    ψ (u • x) = cutStandardAction Q (blocksTailLabels Λ) β γ M hQ u (ψ x))

/-- The underlying map of `blocksMidRegularEquiv`. -/
def blocksMidRegularLinear :
    ExtTensor k A₀ X ≃ₗ[k] BlocksMid Q Λ θ β γ (ExtTensor k A₀ M) hQ :=
  (extTensorScalarEquiv ε X).trans (ψ.trans (blocksMidScalarEquiv Q Λ θ β γ ε M hQ).symm)

include hψ in
theorem blocksMidRegularLinear_smul (d : cutFactorAlgebra Q Λ θ (β + γ)) (x : ExtTensor k A₀ X) :
    blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ (d • x) =
      d • blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ x := by
  let φ := blocksMidScalarEquiv Q Λ θ β γ ε M hQ
  refine ExtTensor.smul_eq_induction (A := A₀) (B := Tᵢ)
    (F := blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ) (map_add _) (map_zero _) ?_ d x
  intro t u p q
  apply φ.injective
  change φ (φ.symm (ψ (extTensorScalarEquiv ε X ((t ⊗ₜ[k] u : A₀ ⊗[k] Tᵢ) •
      ExtTensor.tmul p q)))) =
    φ ((t ⊗ₜ[k] u : cutFactorAlgebra Q Λ θ (β + γ)) •
      φ.symm (ψ (extTensorScalarEquiv ε X (ExtTensor.tmul p q))))
  rw [blocksMidScalarEquiv_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    extTensorScalarEquiv_smul, map_smul, hψ]

/-- **`A ⊠ 𝕊(M) ≅ 𝕊(A ⊠ M)` at the inner cut**, for `A ≅ k`, as modules over the factor
algebra `T^A(θ) ⊗ T^{MR}(β + γ)` of the outer cut; here `X ≅ 𝕊(M)` over `T^{MR}(β + γ)`. -/
def blocksMidRegularEquiv :
    ExtTensor k A₀ X ≃ₗ[cutFactorAlgebra Q Λ θ (β + γ)]
      BlocksMid Q Λ θ β γ (ExtTensor k A₀ M) hQ where
  toFun := blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ
  invFun := (blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ).symm
  left_inv := (blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ).symm_apply_apply
  right_inv := (blocksMidRegularLinear Q Λ θ β γ ε M hQ ψ).apply_symm_apply
  map_add' := map_add _
  map_smul' := blocksMidRegularLinear_smul Q Λ θ β γ ε M hQ ψ hψ

end Blocks

/-! ### The left module of the S-move -/

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β₁ β₂ : Multiset I)
  (M : ModuleCat.{0} (cutFactorAlgebra (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ β₂))

/-- `𝕊^{λ_2; λ_3}(M)`, a module over `T^{λ_2, λ_3}(β_1 + β_2)`. -/
abbrev innerStd : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) (β₁ + β₂)) :=
  (cutStandardFunctor (a := 1) (r := 1) Q hQ (Λ ∘ Fin.natAdd 1) β₁ β₂ (AlgHom.id k _)).obj M

/-- `P_∅ ⊠ M`, a module over the algebra of the three blocks `{1}, {2}, {3}`. -/
abbrev EmptyBlocksInput : Type :=
  ExtTensor k (blocksHeadAlgebra (a := 1) (m := 1) (r := 1) Q Λ 0) M

/-- `P_∅ = T^{λ_1}(0)` is the ground field. -/
abbrev emptyAug : blocksHeadAlgebra (a := 1) (m := 1) (r := 1) Q Λ 0 ≃ₐ[k] k :=
  tensorProductAlgebraZeroEquiv Q (Λ ∘ Fin.castAdd (1 + 1))

/-- `𝕊^{λ_2; λ_3}(M)` is the partial standardization of `M`, as a vector space. -/
def innerStdEquiv :
    innerStd Q hQ Λ β₁ β₂ M ≃ₗ[k]
      CutStandard Q (blocksTailLabels (a := 1) (m := 1) (r := 1) Λ) β₁ β₂ M where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z :=
    LinearMap.congr_fun ((cutStandardAction (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ β₂ M
      hQ).commutes c) z

/-- `P_∅ ⊠ 𝕊^{λ_2; λ_3}(M) ≅ 𝕊^{λ_2; λ_3}(P_∅ ⊠ M)` over `T^{λ_1}(0) ⊗ T^{λ_2, λ_3}`. -/
def leftStdMidEquiv :
    (emptyLeftTensor Q Λ (β₁ + β₂)).obj (innerStd Q hQ Λ β₁ β₂ M)
      ≃ₗ[cutFactorAlgebra (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂)]
      BlocksMid (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂ (EmptyBlocksInput Q Λ β₁ β₂ M) hQ :=
  blocksMidRegularEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂ (emptyAug Q Λ) M hQ
    (innerStdEquiv Q hQ Λ β₁ β₂ M) (fun _ _ => rfl)

/-- **`SMove.leftStd (𝕊^{λ_2; λ_3}(M))` is the partial standardization with three blocks
`{1}, {2}, {3}` of `P_∅ ⊠ M`** (Webster, arXiv:1309.3796v3, §5.1), standardized at the inner
cut first. -/
def leftStdBlocksEquiv :
    CutStandard (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂)
        ((emptyLeftTensor Q Λ (β₁ + β₂)).obj (innerStd Q hQ Λ β₁ β₂ M))
      ≃ₗ[k] BlocksStandard (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
        (EmptyBlocksInput Q Λ β₁ β₂ M) hQ :=
  cutStandardMapEquiv (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂) (leftStdMidEquiv Q hQ Λ β₁ β₂ M)

omit [DecidableEq I] in
/-- The split `(0 + β_1) + β_2 = β_1 + β_2` of the black weight. -/
theorem leftStdSplit : (0 + β₁) + β₂ = β₁ + β₂ := by rw [zero_add]

/-- **`𝕊^{λ_1; λ_2}(P_∅ ⊠ M)`**, the standardization of `P_∅ ⊠ M` at the first cut, a module
over `T^{λ_1, λ_2}(β_1) ⊗ T^{λ_3}(β_2)`. -/
abbrev LeftStdMidL : Type :=
  BlocksMidL (a := 1) (m := 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
    0 β₁ β₂ (BlocksAssocInput (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
      (EmptyBlocksInput Q Λ β₁ β₂ M)) hQ

/-- `𝕊^{λ_1; λ_2}(P_∅ ⊠ M)` as an object of `ModuleCat`. -/
def leftStdMidModule : ModuleCat.{0} (cutFactorAlgebra (a := 1 + 1) (r := 1) Q
    (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂) :=
  ModuleCat.of _ (LeftStdMidL Q hQ Λ β₁ β₂ M)

/-- The identity of `𝕊^{λ_1; λ_2}(P_∅ ⊠ M)` onto its object of `ModuleCat`. -/
def leftStdMidModuleEquiv :
    LeftStdMidL Q hQ Λ β₁ β₂ M ≃ₗ[cutFactorAlgebra (a := 1 + 1) (r := 1) Q
      (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂] leftStdMidModule Q hQ Λ β₁ β₂ M where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem castTensorProductAlgebra_trans' {ℓ : ℕ} (Λ' : Fin ℓ → I →₀ ℕ)
    {ν₁ ν₂ ν₃ : Multiset I} (h₁ : ν₁ = ν₂) (h₂ : ν₂ = ν₃) (t : TensorProductAlgebra k Q Λ' ν₁) :
    castTensorProductAlgebra Q Λ' h₂ (castTensorProductAlgebra Q Λ' h₁ t) =
      castTensorProductAlgebra Q Λ' (h₁.trans h₂) t := by
  subst h₁ h₂
  rfl

/-- The inverse of `blocksStandardAssocEquiv` intertwines the actions of all strands. -/
theorem blocksStandardAssocEquiv_symm_action_one
    (u : TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ((0 + β₁) + β₂))
    (y : BlocksStandard (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
      (EmptyBlocksInput Q Λ β₁ β₂ M) hQ) :
    (blocksStandardAssocEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
        (EmptyBlocksInput Q Λ β₁ β₂ M) hQ).symm
      (blocksStandardAction (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
        (EmptyBlocksInput Q Λ β₁ β₂ M) hQ
        (castTensorProductAlgebra Q Λ (add_assoc 0 β₁ β₂) u) y) =
      blocksStandardActionL Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) 0 β₁ β₂ _ hQ u
        ((blocksStandardAssocEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
          (EmptyBlocksInput Q Λ β₁ β₂ M) hQ).symm y) := by
  let e := blocksStandardAssocEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
    (EmptyBlocksInput Q Λ β₁ β₂ M) hQ
  have h := blocksStandardAssocEquiv_action_one (a := 1) (m := 1) Q Λ 0 β₁ β₂
    (EmptyBlocksInput Q Λ β₁ β₂ M) hQ u (e.symm y)
  refine (congrArg e.symm ((congrArg (blocksStandardAction (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
    (EmptyBlocksInput Q Λ β₁ β₂ M) hQ (castTensorProductAlgebra Q Λ (add_assoc 0 β₁ β₂) u))
    (e.apply_symm_apply y)).symm.trans h.symm)).trans (e.symm_apply_apply _)

/-- The underlying map of `leftStdCutEquiv`. -/
def leftStdCutLinear :
    CutStandard (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂)
        ((emptyLeftTensor Q Λ (β₁ + β₂)).obj (innerStd Q hQ Λ β₁ β₂ M)) ≃ₗ[k]
      CutStandard (a := 1 + 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂
        (leftStdMidModule Q hQ Λ β₁ β₂ M) :=
  ((leftStdBlocksEquiv Q hQ Λ β₁ β₂ M).trans
    (blocksStandardAssocEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
      (EmptyBlocksInput Q Λ β₁ β₂ M) hQ).symm).trans
    (cutStandardMapEquiv (a := 1 + 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂
      (leftStdMidModuleEquiv Q hQ Λ β₁ β₂ M))

/-- `leftStdCutLinear` intertwines the actions of all strands. -/
theorem leftStdCutLinear_action
    (u : TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ((0 + β₁) + β₂))
    (z : CutStandard (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂)
        ((emptyLeftTensor Q Λ (β₁ + β₂)).obj (innerStd Q hQ Λ β₁ β₂ M))) :
    leftStdCutLinear Q hQ Λ β₁ β₂ M
        (cutStandardAction (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂) _ hQ
          (castTensorProductAlgebra Q Λ (add_assoc 0 β₁ β₂) u) z) =
      cutStandardAction (a := 1 + 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂
        (leftStdMidModule Q hQ Λ β₁ β₂ M) hQ u (leftStdCutLinear Q hQ Λ β₁ β₂ M z) := by
  change cutStandardMap (a := 1 + 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
      (0 + β₁) β₂ (leftStdMidModuleEquiv Q hQ Λ β₁ β₂ M).toLinearMap
    ((blocksStandardAssocEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
      (EmptyBlocksInput Q Λ β₁ β₂ M) hQ).symm
    (cutStandardMap (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂)
      (leftStdMidEquiv Q hQ Λ β₁ β₂ M).toLinearMap
      (cutStandardAction (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂) _ hQ
        (castTensorProductAlgebra Q Λ (add_assoc 0 β₁ β₂) u) z))) = _
  refine (congrArg (fun w => cutStandardMap (a := 1 + 1) (r := 1) Q
      (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂
      (leftStdMidModuleEquiv Q hQ Λ β₁ β₂ M).toLinearMap
      ((blocksStandardAssocEquiv (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂
        (EmptyBlocksInput Q Λ β₁ β₂ M) hQ).symm w))
    (cutStandardMap_action (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂) hQ
      (leftStdMidEquiv Q hQ Λ β₁ β₂ M).toLinearMap
      (castTensorProductAlgebra Q Λ (add_assoc 0 β₁ β₂) u) z)).trans ?_
  refine (congrArg (fun w => cutStandardMap (a := 1 + 1) (r := 1) Q
      (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂
      (leftStdMidModuleEquiv Q hQ Λ β₁ β₂ M).toLinearMap w)
    (blocksStandardAssocEquiv_symm_action_one Q hQ Λ β₁ β₂ M u _)).trans ?_
  exact cutStandardMap_action (a := 1 + 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
    (0 + β₁) β₂ hQ (leftStdMidModuleEquiv Q hQ Λ β₁ β₂ M).toLinearMap u _

/-- **`𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M)) ≅ 𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ M))`**
(Webster, arXiv:1309.3796v3, §5.1, independence of the order of the cuts; §7.3, proof of
Proposition 7.22), as modules over `T^λ(β_1 + β_2)`. -/
def leftStdCutEquiv :
    (leftStd Q hQ Λ (β₁ + β₂)).obj (innerStd Q hQ Λ β₁ β₂ M) ≃ₗ[
      TensorProductAlgebra k Q Λ (β₁ + β₂)]
      (cutStandardFunctor (a := 1 + 1) (r := 1) Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
        (0 + β₁) β₂ (castTensorProductAlgebra Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
          (leftStdSplit β₁ β₂).symm).toAlgHom).obj (leftStdMidModule Q hQ Λ β₁ β₂ M) where
  toFun z := leftStdCutLinear Q hQ Λ β₁ β₂ M z
  invFun z := (leftStdCutLinear Q hQ Λ β₁ β₂ M).symm z
  left_inv z := (leftStdCutLinear Q hQ Λ β₁ β₂ M).symm_apply_apply z
  right_inv z := (leftStdCutLinear Q hQ Λ β₁ β₂ M).apply_symm_apply z
  map_add' x y := (leftStdCutLinear Q hQ Λ β₁ β₂ M).map_add x y
  map_smul' t z := by
    have hcast : castTensorProductAlgebra Q Λ (zero_add (β₁ + β₂)).symm t =
        castTensorProductAlgebra Q Λ (add_assoc 0 β₁ β₂)
          (castTensorProductAlgebra Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
            (leftStdSplit β₁ β₂).symm t) :=
      (castTensorProductAlgebra_trans' Q Λ _ _ t).symm
    change leftStdCutLinear Q hQ Λ β₁ β₂ M
        (cutStandardAction (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂) _ hQ
          (castTensorProductAlgebra Q Λ (zero_add (β₁ + β₂)).symm t) z) = _
    exact (congrArg (fun u => leftStdCutLinear Q hQ Λ β₁ β₂ M
      (cutStandardAction (a := 1) (r := 1 + 1) Q Λ 0 (β₁ + β₂) _ hQ u z)) hcast).trans
      (leftStdCutLinear_action Q hQ Λ β₁ β₂ M _ z)

/-- **`𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M))` is the standard layer
`S(𝕊^{λ_1; λ_2}(P_∅ ⊠ M))`** at the last red strand (Webster, arXiv:1309.3796v3, §5.1;
§7.3, proof of Proposition 7.22): the form in which the left module of the S-move enters the
Tor lemmas for standardizations. -/
def leftStdCutLayerIso :
    (leftStd Q hQ Λ (β₁ + β₂)).obj (innerStd Q hQ Λ β₁ β₂ M) ≅
      stdLayerModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ
        ⟨0 + β₁, β₂, leftStdSplit β₁ β₂,
          parabolicOfCutModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
            (leftStdMidModule Q hQ Λ β₁ β₂ M)⟩ :=
  (leftStdCutEquiv Q hQ Λ β₁ β₂ M).toModuleIso ≪≫
    cutStandardParabolicIso Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (leftStdSplit β₁ β₂)
      (leftStdMidModule Q hQ Λ β₁ β₂ M)

end SMove

end Categorification.Stendhal
