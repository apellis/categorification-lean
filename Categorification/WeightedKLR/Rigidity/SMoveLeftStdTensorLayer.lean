/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdAssoc
import Categorification.WeightedKLR.Rigidity.SMoveRightStdTensorLayer

/-!
# The first term of the left side of the S-move as `S(Z ⊠ R e(∅))`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. Let `M` be a module over `T^{λ_2}(β_1) ⊗ T^{λ_3}(0)`, with no black strand
on the last red strand. By `SMove.leftStdCutLayerIso` the S-move module
`𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M))` is the standard layer of `𝕊^{λ_1; λ_2}(P_∅ ⊠ M)`
at the last red strand. Here this standard layer is put in the form `S(Z ⊠ R e(∅))`
(`tensorLayer`), with `Z` the standardization of the last red strand of `λ_1 λ_2` applied to
`P_∅ ⊠ M`: the factor `T^{λ_3}(0) ≅ k` is split off, and the cut at the second red strand is the
standardization of the second red strand (`parabolicCutStandardEquiv` at two strands).

## Main definitions

* `extTensorScalarFactorEquiv`: a `k`-linear identification `X ≅ Y ⊠ P` compatible with
  `D ⊗ 1` is linear over `D ⊗ C`, for `C ≅ k`.
* `SMove.leftStdInnerFactor`: `P_∅ ⊠ M` as a factor module over the first two red strands.
* `SMove.leftStdInnerLayer`: its standardization `Z` over `λ_1 λ_2`.
* `SMove.leftEmptyFactorEquiv`: `𝕊^{λ_1; λ_2}(P_∅ ⊠ M) ≅ Z ⊠ R^{λ_3}(0) e(∅)` over the parabolic
  factor algebra.
* `SMove.leftStdTensorLayerIso`: `SMove.leftStd (𝕊(M)) ≅ S(Z ⊠ R e(∅))`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-! ### Splitting off a factor isomorphic to the ground field -/

section ScalarFactor

variable {k D C : Type} [Field k] [Ring D] [Algebra k D] [Ring C] [Algebra k C]
  (εC : C ≃ₐ[k] k)

/-- For `C ≅ k`, `d ⊗ c = ε(c) (d ⊗ 1)`. -/
theorem tmul_eq_augmentation_smul (d : D) (c : C) :
    (d ⊗ₜ[k] c : D ⊗[k] C) = εC c • (d ⊗ₜ[k] (1 : C)) := by
  have hc : c = εC c • (1 : C) := by
    rw [Algebra.smul_def, mul_one]
    conv_lhs => rw [← εC.symm_apply_apply c]
    exact εC.symm.commutes (εC c)
  conv_lhs => rw [hc]
  rw [TensorProduct.tmul_smul]

variable {X Y P : Type}
  [AddCommGroup X] [Module k X] [Module (D ⊗[k] C) X] [IsScalarTower k (D ⊗[k] C) X]
  [AddCommGroup Y] [Module k Y] [Module D Y] [IsScalarTower k D Y]
  [AddCommGroup P] [Module k P] [Module C P] [IsScalarTower k C P]
  (ψ : X ≃ₗ[k] ExtTensor k Y P)
  (hψ : ∀ (d : D) (x : X), ψ ((d ⊗ₜ[k] (1 : C)) • x) = (d ⊗ₜ[k] (1 : C)) • ψ x)

/-- **A `k`-linear identification `X ≅ Y ⊠ P` compatible with `D ⊗ 1` is linear over
`D ⊗ C`**, when `C ≅ k`: the factor `C` acts by its augmentation on both sides. -/
def extTensorScalarFactorEquiv : X ≃ₗ[D ⊗[k] C] ExtTensor k Y P where
  toFun := ψ
  invFun := ψ.symm
  left_inv := ψ.left_inv
  right_inv := ψ.right_inv
  map_add' := map_add ψ
  map_smul' t x := by
    rw [RingHom.id_apply]
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => rw [add_smul, map_add, hs, ht, add_smul]
    | tmul d c =>
      rw [tmul_eq_augmentation_smul εC, smul_assoc, map_smul, hψ, smul_assoc]

end ScalarFactor

/-! ### The cyclotomic quotient with no black strands -/

section CycZero

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- `R^{λ_{ℓ+1}}(0) ≅ k`. -/
def cycZeroAugmentation :
    CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) 0 ≃ₐ[k] k :=
  (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last ℓ)) 0).trans
    (tensorProductAlgebraZeroEquiv Q (fun _ : Fin 1 => Λ (Fin.last ℓ)))

/-- `R^{λ_{ℓ+1}}(0) e(∅) ≅ k` as vector spaces. -/
def cycProjZeroLinearEquiv (u : Seq (0 : Multiset I)) :
    KMod (k := k) (cycProj Q Λ 0 u) ≃ₗ[k] k :=
  ((cycProjZeroEquiv Q Λ u).symm.restrictScalars k).trans
    (cycZeroAugmentation Q Λ).toLinearEquiv

end CycZero

/-! ### The first factor of the cut algebras -/

section FirstFactor

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- `parabolicCutFactorEquiv` is the identity on the first factor. -/
theorem parabolicCutFactorEquiv_tmul_one {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)
    (d : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ) :
    parabolicCutFactorEquiv Q Λ θ β (d ⊗ₜ[k] 1) = d ⊗ₜ[k] 1 := by
  change Algebra.TensorProduct.map _ _ (d ⊗ₜ[k] 1) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- On the standardization at the first cut, `d ⊗ 1` acts by the action of `d`. -/
theorem blocksMidActionL_tmul_one {a m r : ℕ} (Λ : Fin ((a + m) + r) → I →₀ ℕ)
    (θ β γ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
    [Module (blocksFactorAlgebraL Q Λ θ β γ) N] [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N]
    (hQ : KLRSymm Q) (d : TensorProductAlgebra k Q (blocksLeftLabels Λ) (θ + β)) :
    blocksMidActionL Q Λ θ β γ N hQ (d ⊗ₜ[k] 1) =
      cutStandardAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N) hQ d := by
  rw [blocksMidActionL, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

end FirstFactor

/-! ### The left module of the S-move with no black strand on the last red strand -/

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β₁ : Multiset I)
  (M : ModuleCat.{0} (cutFactorAlgebra (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ 0))

/-- `P_∅ ⊠ M`, as a module over the first two blocks `T^{λ_1}(0) ⊗ T^{λ_2}(β_1)`. -/
abbrev LeftStdInner : Type :=
  BlocksInnerL (a := 1) (m := 1) (r := 1) Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) 0 β₁ 0
    (BlocksAssocInput (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ 0 (EmptyBlocksInput Q Λ β₁ 0 M))

/-- **`P_∅ ⊠ M` as a factor module of the second red strand**, over
`T^{λ_1}(0) ⊗ R^{λ_2}(β_1)`. -/
def leftStdInnerFactor :
    FactorModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) 0 β₁ where
  carrier := ParabolicOfCut Q (blocksLeftLabels (a := 1) (m := 1) (r := 1)
    (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) 0 β₁ (LeftStdInner Q Λ β₁ M)
  moduleFactor := (inferInstance : Module (parabolicFactorAlgebra Q
    (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) 0 β₁) _)
  tower := (inferInstance : IsScalarTower k (parabolicFactorAlgebra Q
    (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) 0 β₁) _)

/-- **`Z = S_{λ_1 λ_2}(P_∅ ⊠ M)`**, the standardization of the second red strand, a module over
`T^{λ_1, λ_2}(0 + β_1)`. -/
abbrev leftStdInnerLayer :
    ModuleCat.{0} (TensorProductAlgebra k Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘
      Fin.castSucc) (0 + β₁)) :=
  stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
    ⟨0, β₁, rfl, leftStdInnerFactor Q Λ β₁ M⟩

local notation "Λ₂" => Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)

/-- The standardization at the first cut, with its own `k`-module structure. -/
abbrev LeftStdMid : Type := LeftStdMidL Q hQ Λ β₁ 0 M

/-- The `k`-structure of `𝕊^{λ_1; λ_2}(P_∅ ⊠ M)` through `T^{λ_1, λ_2} ⊗ T^{λ_3}` is its own. -/
def leftStdMidScalarEquiv :
    (parabolicOfCutModule Q (Λ₂) (leftStdMidModule Q hQ Λ β₁ 0 M)).carrier ≃ₗ[k]
      LeftStdMid Q hQ Λ β₁ M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x :=
    algebraMap_smul (cutFactorAlgebra (a := 1 + 1) (r := 1) Q (Λ₂) (0 + β₁) 0) c
      (show LeftStdMid Q hQ Λ β₁ M from x)

/-- The `k`-structure of `Z` through `T^{λ_1, λ_2}` is its own. -/
def leftStdInnerLayerScalarEquiv :
    ParabolicStandard Q ((Λ₂) ∘ Fin.castSucc) 0 β₁ (leftStdInnerFactor Q Λ β₁ M).carrier ≃ₗ[k]
      KMod (k := k) (leftStdInnerLayer Q hQ Λ β₁ M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change c • x = parabolicStandardAction Q ((Λ₂) ∘ Fin.castSucc) 0 β₁ _ hQ
      ((castTensorProductAlgebra Q ((Λ₂) ∘ Fin.castSucc) (rfl : 0 + β₁ = 0 + β₁).symm)
        (algebraMap k _ c)) x
    rw [AlgEquiv.commutes, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The underlying `k`-linear map of `leftEmptyFactorEquiv`. -/
def leftEmptyLinearEquiv (u : Seq (0 : Multiset I)) :
    (parabolicOfCutModule Q (Λ₂) (leftStdMidModule Q hQ Λ β₁ 0 M)).carrier ≃ₗ[k]
      ExtTensor k (KMod (k := k) (leftStdInnerLayer Q hQ Λ β₁ M))
        (KMod (k := k) (cycProj Q (Λ₂) 0 u)) :=
  (((leftStdMidScalarEquiv Q hQ Λ β₁ M).trans
    ((parabolicCutStandardEquiv Q (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂)) 0 β₁
      (LeftStdInner Q Λ β₁ M)).symm.trans
      (leftStdInnerLayerScalarEquiv Q hQ Λ β₁ M))).trans
    (TensorProduct.rid k _).symm).trans
    (TensorProduct.congr (LinearEquiv.refl k _) (cycProjZeroLinearEquiv Q (Λ₂) u).symm)


local notation "Cyc₀" =>
  CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ (Λ₂) (Fin.last (1 + 1)) j) 0

/-- `leftEmptyLinearEquiv` sends `x` to `x ⊗ e(∅)`. -/
theorem leftEmptyLinearEquiv_apply (u : Seq (0 : Multiset I))
    (x : (parabolicOfCutModule Q (Λ₂) (leftStdMidModule Q hQ Λ β₁ 0 M)).carrier) :
    leftEmptyLinearEquiv Q hQ Λ β₁ M u x =
      ExtTensor.tmul (k := k)
        (@id (KMod (k := k) (leftStdInnerLayer Q hQ Λ β₁ M))
          ((parabolicCutStandardEquiv Q (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂)) 0 β₁
            (LeftStdInner Q Λ β₁ M)).symm (@id (LeftStdMid Q hQ Λ β₁ M) x)))
        ((cycProjZeroLinearEquiv Q (Λ₂) u).symm 1) := by
  simp only [leftEmptyLinearEquiv, LinearEquiv.trans_apply, TensorProduct.rid_symm_apply]
  rfl

/-- The action of `T^{λ_1, λ_2}` on `Z`. -/
theorem leftStdInnerLayer_smul
    (d : TensorProductAlgebra k Q ((Λ₂) ∘ Fin.castSucc) (0 + β₁))
    (z : KMod (k := k) (leftStdInnerLayer Q hQ Λ β₁ M)) :
    d • z = @id (KMod (k := k) (leftStdInnerLayer Q hQ Λ β₁ M))
      (parabolicStandardAction Q ((Λ₂) ∘ Fin.castSucc) 0 β₁
        (leftStdInnerFactor Q Λ β₁ M).carrier hQ d z) :=
  rfl

/-- The action on `Z` is the parabolic action of the two-strand cut. -/
theorem leftStdInnerFactor_action :
    HEq (parabolicStandardAction Q ((Λ₂) ∘ Fin.castSucc) 0 β₁
        (leftStdInnerFactor Q Λ β₁ M).carrier hQ)
      (parabolicStandardAction Q (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂)) 0 β₁
        (ParabolicOfCut Q (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂)) 0 β₁
          (LeftStdInner Q Λ β₁ M)) hQ) :=
  HEq.rfl

/-- `leftEmptyLinearEquiv` is linear over the first factor `T^{λ_1, λ_2}(0 + β_1) ⊗ 1`. -/
theorem leftEmptyLinearEquiv_smul (u : Seq (0 : Multiset I))
    (d : TensorProductAlgebra k Q ((Λ₂) ∘ Fin.castSucc) (0 + β₁))
    (x : (parabolicOfCutModule Q (Λ₂) (leftStdMidModule Q hQ Λ β₁ 0 M)).carrier) :
    leftEmptyLinearEquiv Q hQ Λ β₁ M u
        ((d ⊗ₜ[k] (1 : Cyc₀) : parabolicFactorAlgebra Q (Λ₂) (0 + β₁) 0) • x) =
      (d ⊗ₜ[k] (1 : Cyc₀) : parabolicFactorAlgebra Q (Λ₂) (0 + β₁) 0) •
        leftEmptyLinearEquiv Q hQ Λ β₁ M u x := by
  let E := (parabolicCutStandardEquiv Q (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂)) 0 β₁
    (LeftStdInner Q Λ β₁ M)).symm
  let p₀ := (cycProjZeroLinearEquiv Q (Λ₂) u).symm 1
  have hx : ((d ⊗ₜ[k] (1 : Cyc₀) : parabolicFactorAlgebra Q (Λ₂) (0 + β₁) 0) • x) =
      cutStandardAction (a := 1) (r := 1) Q (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂))
        0 β₁ (LeftStdInner Q Λ β₁ M) hQ d (@id (LeftStdMid Q hQ Λ β₁ M) x) := by
    change blocksMidActionL (a := 1) (m := 1) (r := 1) Q (Λ₂) 0 β₁ 0 _ hQ
      (parabolicCutFactorEquiv Q (Λ₂) (0 + β₁) 0 (d ⊗ₜ[k] 1))
      (@id (LeftStdMid Q hQ Λ β₁ M) x) = _
    refine (congrArg (fun t => blocksMidActionL (a := 1) (m := 1) (r := 1) Q (Λ₂) 0 β₁ 0 _ hQ t
      (@id (LeftStdMid Q hQ Λ β₁ M) x))
      (parabolicCutFactorEquiv_tmul_one Q (Λ₂) (0 + β₁) 0 d)).trans ?_
    exact LinearMap.congr_fun (blocksMidActionL_tmul_one (a := 1) (m := 1) (r := 1) Q (Λ₂) 0 β₁ 0
      _ hQ d) _
  refine (congrArg (leftEmptyLinearEquiv Q hQ Λ β₁ M u) hx).trans ?_
  refine (leftEmptyLinearEquiv_apply Q hQ Λ β₁ M u _).trans ?_
  refine Eq.trans ?_ (congrArg (fun y => (d ⊗ₜ[k] (1 : Cyc₀) :
    parabolicFactorAlgebra Q (Λ₂) (0 + β₁) 0) • y)
    (leftEmptyLinearEquiv_apply Q hQ Λ β₁ M u x)).symm
  refine Eq.trans ?_ (ExtTensor.smul_tmul (k := k) _ _ _ _).symm
  refine Eq.trans ?_ (congrArg (ExtTensor.tmul (k := k) _) (one_smul Cyc₀ p₀).symm)
  refine Eq.trans ?_ (congrArg (fun z => ExtTensor.tmul (k := k) z p₀)
    (leftStdInnerLayer_smul Q hQ Λ β₁ M d _)).symm
  refine congrArg (fun z => ExtTensor.tmul (k := k)
    (@id (KMod (k := k) (leftStdInnerLayer Q hQ Λ β₁ M)) z) p₀) ?_
  refine (parabolicCutStandardEquiv_symm_action Q hQ
    (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ₂)) (LeftStdInner Q Λ β₁ M) d _).trans ?_
  exact (LinearMap.congr_fun (DFunLike.congr_fun
    (eq_of_heq (leftStdInnerFactor_action Q hQ Λ β₁ M)) d) _).symm

/-- **`𝕊^{λ_1; λ_2}(P_∅ ⊠ M) ≅ Z ⊠ R^{λ_3}(0) e(∅)`** as modules over the parabolic factor
algebra `T^{λ_1, λ_2}(0 + β_1) ⊗ R^{λ_3}(0)`, with `Z = S_{λ_1 λ_2}(P_∅ ⊠ M)`. -/
def leftEmptyFactorEquiv (u : Seq (0 : Multiset I)) :
    (parabolicOfCutModule Q (Λ₂) (leftStdMidModule Q hQ Λ β₁ 0 M)).carrier ≃ₗ[
      parabolicFactorAlgebra Q (Λ₂) (0 + β₁) 0]
      (tensorFactor Q (Λ₂) (leftStdInnerLayer Q hQ Λ β₁ M) (cycProj Q (Λ₂) 0 u)).carrier :=
  extTensorScalarFactorEquiv (cycZeroAugmentation Q (Λ₂)) (leftEmptyLinearEquiv Q hQ Λ β₁ M u)
    (leftEmptyLinearEquiv_smul Q hQ Λ β₁ M u)

/-- **`𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M)) ≅ S(Z ⊠ R e(∅))`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22) for `M` over `T^{λ_2}(β_1) ⊗ T^{λ_3}(0)`,
with `Z = S_{λ_1 λ_2}(P_∅ ⊠ M)`: the left module of the S-move with no black strand on the
last red strand, in the form `tensorLayer`. -/
def leftStdTensorLayerIso (u : Seq (0 : Multiset I)) :
    (leftStd Q hQ Λ (β₁ + 0)).obj (innerStd Q hQ Λ β₁ 0 M) ≅
      stdLayerModule Q (Λ₂) hQ (tensorLayer Q (Λ₂) (leftStdSplit β₁ 0)
        (leftStdInnerLayer Q hQ Λ β₁ M) (cycProj Q (Λ₂) 0 u)) :=
  leftStdCutLayerIso Q hQ Λ β₁ 0 M ≪≫
    stdLayerIso Q (Λ₂) hQ (leftStdSplit β₁ 0) (leftEmptyFactorEquiv Q hQ Λ β₁ M u)

end SMove

end Categorification.Stendhal
