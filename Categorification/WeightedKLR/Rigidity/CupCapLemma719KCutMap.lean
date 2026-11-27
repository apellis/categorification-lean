/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutData
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCapSum
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KInputHomGen
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KTransport

/-!
# The comparison map of Lemma 7.19 (K) at the cut, on the input

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the map
`Φ : S_+(Y ⊠ L') → K^σ(S_cut Y)` is induced by `y ⊠ v ↦ cap(|h|, v) ⊗ (1 ⊗ y)`, the sum of the
cap generators at the cut `|h| = j + |θ|` tensored with the unit of the partial standardization
of `Y` (`kCutInputMap`). This file sets up that map and the two actions it has to intertwine:
the blocks of `λ⁺` acting on the input (`plusInput_tmul_smul`) and on the target through all
strands (`kCutOneStepRep_apply`).

## Main definitions

* `Stendhal.CupCap.kCutUnit`: the unit `Y → S_cut Y`.
* `Stendhal.CupCap.kCutInputMap`: the map `Y ⊠ L' → K^σ(S_cut Y)` on the input.

## Main results

* `Stendhal.CupCap.castLabels_cutAffineMap_concat_smul_kCutUnit`: the juxtaposed affine
  diagrams of the two blocks of `λ` act on the unit through `Y`.
* `Stendhal.CupCap.kCutOneStepRep_apply`: the affine diagrams of `λ⁺` act on the target
  through `T^{λ⁺}`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)

/-! ### The cut side -/

/-- **The unit of the partial standardization of `Y` at the cut.** -/
abbrev kCutUnit : Y →ₗ[k] KCutStd j hj Q Λ θ γ Y hQ :=
  cutStandardUnit Q (cutLabels j hj Λ) θ γ Y

set_option hygiene false in
local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
set_option hygiene false in
local notation "αc" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
  (stendhalWeight j θ)
set_option hygiene false in
local notation "δc" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (ℓ - j) γ)
set_option hygiene false in
local notation "cast_c" => castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)

/-- **The juxtaposed affine diagrams of the two blocks of `λ` act on the unit through `Y`.** -/
theorem castLabels_cutAffineMap_concat_smul_kCutUnit (t : TensorKLR Sc αc δc) (y : Y) :
    cast_c (cutAffineMap Q (cutLabels j hj Λ) θ γ (concat Sc αc δc t)) •
        kCutUnit j hj Q Λ θ γ Y hQ y =
      kCutUnit j hj Q Λ θ γ Y hQ (cutInputMap Q (cutLabels j hj Λ) θ γ t • y) := by
  rw [kCutStd_smul_def]
  change cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ ((cast_c).symm (cast_c _)) _ = _
  rw [AlgEquiv.symm_apply_apply, cutAffineMap_apply]
  exact cutStandardAction_concat_unit Q (cutLabels j hj Λ) θ γ Y hQ t y

/-- A generator `g` whose juxtaposition is `g · 1_{α,δ}` acts on the unit through `Y`. -/
theorem castLabels_cutAffineMap_smul_kCutUnit (t : TensorKLR Sc αc δc)
    (g : KLRAlgebra k Sc (αc + δc)) (hg : concat Sc αc δc t = g * oneConcat Sc αc δc) (y : Y) :
    cast_c (cutAffineMap Q (cutLabels j hj Λ) θ γ g) • kCutUnit j hj Q Λ θ γ Y hQ y =
      kCutUnit j hj Q Λ θ γ Y hQ (cutInputMap Q (cutLabels j hj Λ) θ γ t • y) := by
  have h1 := castLabels_cutAffineMap_concat_smul_kCutUnit j hj Q Λ θ γ Y hQ 1 y
  rw [concat_one, map_one, one_smul] at h1
  rw [← castLabels_cutAffineMap_concat_smul_kCutUnit, hg, map_mul, map_mul, mul_smul, h1]

/-- The scalars act on the partial standardization at the cut through `T^λ(θ + γ)`. -/
theorem algebraMap_smul_kCutStd (c : k) (u : KCutStd j hj Q Λ θ γ Y hQ) :
    algebraMap k (TensorProductAlgebra k Q Λ (θ + γ)) c • u = c • u := by
  rw [kCutStd_smul_def, AlgHom.commutes, Module.algebraMap_end_apply]

/-! ### The plus side -/

variable (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Λp" => plusBlockLabels Λ Λc j hj
set_option hygiene false in
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)
set_option hygiene false in
local notation "Xt" => KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L'

/-- The affine diagrams of all strands of `λ⁺` acting on the target. -/
abbrev kCutOneStepRep :=
  blocksOneStepRep Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
    (plusBlocksRep (ρ := kCutRep j hj Q Λ Λc θ γ ν₀ Y hQ L'))

omit [DecidableEq I] in
/-- The weights of all strands of the one-step model of `λ⁺`. -/
theorem kCutOneStepWeight_eq :
    Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)) +
          Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
            (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))) =
      stendhalWeight (j + (2 + (ℓ - j))) (θ + (ν₀ + γ)) :=
  (blocksAllWeight_eq (a := j) (m := 2) (r := ℓ - j) θ ν₀ γ).symm.trans
    (cutInputWeights_add (a := j) (r := 2 + (ℓ - j)) θ (ν₀ + γ))

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- **The affine diagrams of `λ⁺` act on the target through `T^{λ⁺}`.** -/
theorem kCutOneStepRep_apply (z : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)) +
          Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
            (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))))
    (X : Xt) :
    kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' z X =
      castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)
        (castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
          (θ + (ν₀ + γ)) (tensorOfKLR Q (plusLabels Λ Λc j hj ∘ Fin.cast (plusBlock_card j hj))
            (θ + (ν₀ + γ)) (castKLR _ (kCutOneStepWeight_eq j θ γ ν₀) z))) • X := by
  rw [blocksOneStepRep_apply, castKLR_symm_eq, cutAffineMap_apply, castKLR_castKLR]
  rfl

/-! ### The map on the input -/

omit [DecidableEq I] in
include hj in
theorem cutPos_lt :
    Multiset.card (stendhalWeight j θ) < Multiset.card (stendhalWeight ℓ (θ + γ)) + 1 := by
  rw [card_stendhalWeight, card_stendhalWeight, Multiset.card_add]
  omega

include hj in
/-- The position `|h| = j + |θ|` of the cut among the strands of `λ`. -/
abbrev cutPos : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)) + 1) :=
  ⟨Multiset.card (stendhalWeight j θ), cutPos_lt j hj θ γ⟩

/-- The map on the input, as a bilinear map: `y ⊗ v ↦ cap(|h|, v) ⊗ (1 ⊗ y)`. -/
def kCutInputBil : Y →ₗ[k] L' →ₗ[k] Xt :=
  LinearMap.mk₂ k (fun y v => BalancedTensor.tmul
      (capSum j hj Q Λ Λc (θ + γ) ν₀ (cutPos j hj θ γ) (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v))
      (kCutUnit j hj Q Λ θ γ Y hQ y))
    (fun y y' v => by rw [map_add, BalancedTensor.tmul_add])
    (fun c y v => by
      rw [map_smul, ← algebraMap_smul_kCutStd, ← BalancedTensor.op_smul_tmul,
        op_algebraMap_smul_capSum, ← BalancedTensor.smul_tmul']
      rfl)
    (fun y v v' => by
      change BalancedTensor.tmul (capSum j hj Q Λ Λc (θ + γ) ν₀ (cutPos j hj θ γ)
        (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v +
          toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v')) _ = _
      rw [capSum_add, BalancedTensor.add_tmul])
    (fun c y v => by
      change BalancedTensor.tmul (capSum j hj Q Λ Λc (θ + γ) ν₀ (cutPos j hj θ γ)
        (c • toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v)) _ = _
      rw [capSum_smul, ← BalancedTensor.smul_tmul']
      rfl)

set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))

/-- **The map `Y ⊠ L' → K^σ(S_cut Y)` on the input** of the partial standardization of `λ⁺`. -/
def kCutInputMap : Np →ₗ[k] Xt :=
  TensorProduct.lift (kCutInputBil j hj Q Λ Λc θ γ ν₀ Y hQ L')

theorem kCutInputMap_tmul (y : Y) (v : L') :
    kCutInputMap j hj Q Λ Λc θ γ ν₀ Y hQ L' (midSpectTmul (k := k) y v) =
      BalancedTensor.tmul
        (capSum j hj Q Λ Λc (θ + γ) ν₀ (cutPos j hj θ γ)
          (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v))
        (kCutUnit j hj Q Λ θ γ Y hQ y) := rfl

/-! ### The blocks of `λ⁺` acting on the input -/

set_option hygiene false in
local notation "Λt" => blocksTailLabels (plusBlockLabels Λ Λc j hj)

/-- The affine KLR algebra of the first block of `λ⁺` in the alphabet of all its strands. -/
abbrev plusHeadEmb :=
  (relabelEquiv (redSubfamilyRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.castAdd (2 + (ℓ - j)))
    (Fin.castAdd_injective _ _) θ)).toAlgHom

/-- The affine KLR algebra of the middle block of `λ⁺` in the alphabet of its last two
blocks. -/
abbrev plusMidEmb₀ :=
  relabelEquiv (redSubfamilyRelabel Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
    (Fin.castAdd (ℓ - j)) (Fin.castAdd_injective _ _) ν₀)

/-- The affine KLR algebra of the last block of `λ⁺` in the alphabet of its last two blocks. -/
abbrev plusTailEmb₀ :=
  relabelEquiv (redSubfamilyRelabel Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
    (Fin.natAdd 2) (Fin.natAdd_injective _ _) γ)

/-- The affine KLR algebra of the middle block of `λ⁺` in the alphabet of all its strands. -/
abbrev plusMidEmb :=
  (relabelEquiv (stendhalRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.natAdd j)
    (Fin.natAdd_injective _ _)
    (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
      (stendhalWeight 2 ν₀)))).toAlgHom.comp
    (plusMidEmb₀ j hj Q Λ Λc ν₀).toAlgHom

/-- The affine KLR algebra of the last block of `λ⁺` in the alphabet of all its strands. -/
abbrev plusTailEmb :=
  (relabelEquiv (stendhalRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.natAdd j)
    (Fin.natAdd_injective _ _)
    (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))).toAlgHom.comp
    (plusTailEmb₀ j hj Q Λ Λc γ).toAlgHom

/-- **The blocks of `λ⁺` act on `Y ⊠ L'`**: the outer ones on `Y` and the middle one on `L'`. -/
theorem plusInput_tmul_smul
    (a : KLRAlgebra k (stendhalQ Q (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))))
      (stendhalWeight j θ))
    (b : KLRAlgebra k (stendhalQ Q (Λt ∘ Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀))
    (c : KLRAlgebra k (stendhalQ Q (Λt ∘ Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))
    (y : Y) (v : L') :
    (plusHeadEmb j hj Q Λ Λc θ a ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ b ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ c)) •
        (show Np from midSpectTmul (k := k) y v) =
      (show Np from midSpectTmul (k := k)
        ((relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ
            (tensorOfKLR Q _ θ a) ⊗ₜ[k]
          relabelTensorProductAlgebra Q (plusBlockLabels_tail Λ Λc j hj) γ
            (tensorOfKLR Q _ γ c) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y)
        (relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) ν₀
          (tensorOfKLR Q _ ν₀ b) • v)) := by
  have ht : (blocksTailTensor Q (plusBlockLabels Λ Λc j hj) ν₀ γ).symm
      (plusMidEmb j hj Q Λ Λc ν₀ b ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ c) =
      plusMidEmb₀ j hj Q Λ Λc ν₀ b ⊗ₜ[k] plusTailEmb₀ j hj Q Λ Λc γ c := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  change plusFactorEquiv Q Λ Λc j hj θ ν₀ γ (blocksOneStepMap Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
    _) • (midSpectTmul (k := k) y v : MidSpect (k := k) Y L') = _
  rw [blocksOneStepMap_tmul, ht, cutInputMap, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, redSubfamilyProjection_relabelEquiv,
    redSubfamilyProjection_relabelEquiv, redSubfamilyProjection_relabelEquiv, plusFactorEquiv,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact midSpect_tmul_smul _ _ _ y v

/-! ### Generators on both sides -/

theorem cast_c_cutAffineMap_x (b : Fin (Multiset.card (αc + δc)))
    (b' : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)))) (hb : b'.val = b.val) :
    cast_c (cutAffineMap Q (cutLabels j hj Λ) θ γ (x b)) =
      TensorProductAlgebra.mk Q Λ (θ + γ) (topMap k Q Λ (θ + γ) (x b')) := by
  rw [cutAffineMap_apply]
  exact castLabels_tensorOfKLR_x Q (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ) Λ rfl b b' hb

theorem cast_c_cutAffineMap_ψ (p : ℕ) :
    cast_c (cutAffineMap Q (cutLabels j hj Λ) θ γ (ψ p : KLRAlgebra k Sc (αc + δc))) =
      TensorProductAlgebra.mk Q Λ (θ + γ) (topMap k Q Λ (θ + γ) (ψ p)) := by
  rw [cutAffineMap_apply]
  exact castLabels_tensorOfKLR_ψ Q (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ) Λ rfl p

theorem cast_c_cutAffineMap_e (s : Seq (αc + δc)) (s' : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ (p : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))))
      (q : Fin (Multiset.card (αc + δc))),
      p.val = q.val → s'.lbl p = Sum.map id (Fin.cast (Nat.add_sub_of_le hj)) (s.lbl q)) :
    cast_c (cutAffineMap Q (cutLabels j hj Λ) θ γ (e s)) =
      TensorProductAlgebra.mk Q Λ (θ + γ) (topMap k Q Λ (θ + γ) (e s')) := by
  rw [cutAffineMap_apply]
  exact castLabels_tensorOfKLR_e Q (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ) Λ rfl s s' hs

set_option hygiene false in
local notation "Ap" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
    (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))
set_option hygiene false in
local notation "Mp" => Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kCutOneStepRep_x (p : Fin (Multiset.card Ap)) (p' : Fin Mp) (hp : p'.val = p.val)
    (X : Xt) : kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (x p) X = mkp (botp (x p')) • X := by
  rw [kCutOneStepRep_apply, castLabels_tensorOfKLR_x Q (plusBlock_card j hj)
    (kCutOneStepWeight_eq j θ γ ν₀) (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) p p' hp]
  rfl

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kCutOneStepRep_ψ (p : ℕ) (X : Xt) :
    kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (ψ p) X = mkp (botp (ψ p)) • X := by
  rw [kCutOneStepRep_apply, castLabels_tensorOfKLR_ψ Q (plusBlock_card j hj)
    (kCutOneStepWeight_eq j θ γ ν₀) (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) p]
  rfl

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kCutOneStepRep_e (s : Seq Ap) (s' : Seq (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)))
    (hs : ∀ (p : Fin Mp) (q : Fin (Multiset.card Ap)),
      p.val = q.val → s'.lbl p = Sum.map id (Fin.cast (plusBlock_card j hj)) (s.lbl q))
    (X : Xt) : kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (e s) X = mkp (botp (e s')) • X := by
  rw [kCutOneStepRep_apply, castLabels_tensorOfKLR_e Q (plusBlock_card j hj)
    (kCutOneStepWeight_eq j θ γ ν₀) (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) s s' hs]
  rfl

/-! ### Reduction to pure tensors -/

set_option hygiene false in
local notation "σK" => kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "fK" => kCutInputMap j hj Q Λ Λc θ γ ν₀ Y hQ L'

/-- The intertwining condition at an element holds if it holds on the pure tensors `y ⊠ v`. -/
theorem isInd3At_of_tmul (t : TensorKLR3 Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))
    (ht : ∀ y v, fK (t • (show Np from midSpectTmul (k := k) y v)) =
      σK (concat3 _ _ _ _ t) (fK (show Np from midSpectTmul (k := k) y v))) :
    IsInd3At σK fK t := by
  intro n
  refine TensorProduct.inductionOn (motive := fun z : Y ⊗[k] L' =>
    fK (t • (show Np from z)) = σK (concat3 _ _ _ _ t) (fK (show Np from z))) n ?_ ?_
  · exact ht
  · intro z z' hz hz'
    change fK (t • ((show Np from z) + (show Np from z'))) =
      σK (concat3 _ _ _ _ t) (fK ((show Np from z) + (show Np from z')))
    rw [smul_add, map_add, map_add, map_add, hz, hz']

/-- The unit acts on the image through the idempotent of the one-step model. -/
theorem kCut_oneConcat3 (h1 : IsInd3At σK fK 1) (n : Np) :
    σK (oneConcat3 _ _ _ _) (fK n) = fK n := by
  have h := h1 n
  rw [one_smul] at h
  exact h.symm

/-- The intertwining condition at a generator `t` whose concatenation is `g · 1_{α,β,γ}`. -/
theorem isInd3At_of_concat3_eq (h1 : IsInd3At σK fK 1) (t : TensorKLR3 Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))
    (g : KLRAlgebra k Sp Ap) (hg : concat3 _ _ _ _ t = g * oneConcat3 _ _ _ _)
    (ht : ∀ y v, fK (t • (show Np from midSpectTmul (k := k) y v)) =
      σK g (fK (show Np from midSpectTmul (k := k) y v))) :
    IsInd3At σK fK t :=
  isInd3At_of_tmul j hj Q Λ Λc θ γ ν₀ Y hQ L' t fun y v => by
    rw [hg, map_mul, Module.End.mul_apply, kCut_oneConcat3 j hj Q Λ Λc θ γ ν₀ Y hQ L' h1]
    exact ht y v

/-- The affine KLR algebra of the first block of `λ` in the alphabet of all its strands. -/
abbrev cutHeadEmb :=
  relabelEquiv (redSubfamilyRelabel Q (cutLabels j hj Λ) (Fin.castAdd (ℓ - j))
    (Fin.castAdd_injective _ _) θ)

/-- The affine KLR algebra of the last block of `λ` in the alphabet of all its strands. -/
abbrev cutTailEmb :=
  relabelEquiv (redSubfamilyRelabel Q (cutLabels j hj Λ) (Fin.natAdd j)
    (Fin.natAdd_injective _ _) γ)

theorem cutInputMap_emb
    (a : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
    (c : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :
    cutInputMap Q (cutLabels j hj Λ) θ γ (cutHeadEmb j hj Q Λ θ a ⊗ₜ[k] cutTailEmb j hj Q Λ γ c) =
      tensorOfKLR Q _ θ a ⊗ₜ[k] tensorOfKLR Q _ γ c := by
  rw [cutInputMap, Algebra.TensorProduct.map_tmul, redSubfamilyProjection_relabelEquiv,
    redSubfamilyProjection_relabelEquiv]

/-- **The dots of the first block.** -/
theorem kCut_head_x (h1 : IsInd3At σK fK 1) (a : Fin (Multiset.card (stendhalWeight j θ))) :
    IsInd3At σK fK (plusHeadEmb j hj Q Λ Λc θ (x a) ⊗ₜ[k] (1 : TensorKLR Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))) := by
  have hφ : plusHeadEmb j hj Q Λ Λc θ (x a) = x (Fin.cast (Multiset.card_map _ _).symm a) := by
    rw [AlgEquiv.coe_toAlgHom, relabelEquiv_apply, relabelHom_x]
  refine isInd3At_of_concat3_eq j hj Q Λ Λc θ γ ν₀ Y hQ L' h1 _ _
    (by rw [hφ, concat3_x_tmul_one]) fun y v => ?_
  have h1' : (1 : TensorKLR Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))) =
      plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1 := by
    rw [map_one, map_one, Algebra.TensorProduct.one_def]
  have hc := castLabels_cutAffineMap_smul_kCutUnit j hj Q Λ θ γ Y hQ
    (cutHeadEmb j hj Q Λ θ (x a) ⊗ₜ[k] cutTailEmb j hj Q Λ γ 1)
    (x (Seq.posL _ (Fin.cast (Multiset.card_map _ _).symm a)))
    (by rw [map_one, relabelEquiv_apply, relabelHom_x, concat_x_tmul_one]) y
  rw [cutInputMap_emb, tensorOfKLR_one] at hc
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_x Q (Λ₂ := cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))
      (plusBlockLabels_head Λ Λc j hj) θ a, relabel_tensorOfKLR_one, relabel_tensorOfKLR_one,
    one_smul, kCutInputMap_tmul, kCutInputMap_tmul]
  have hb : a.val < Multiset.card (stendhalWeight ℓ (θ + γ)) :=
    lt_of_lt_of_le a.2 (Nat.lt_succ_iff.1 (cutPos_lt j hj θ γ))
  rw [← hc, cast_c_cutAffineMap_x j hj Q Λ θ γ _ ⟨a.val, hb⟩ rfl, ← BalancedTensor.op_smul_tmul,
    op_x_smul_capSum, ← BalancedTensor.smul_tmul', kCutOneStepRep_x _ _ _ _ _ _ _ _ _ _ _ _
      (dotPos (j := j) (hj := hj) (ν₀ := ν₀) (cutPos j hj θ γ) ⟨a.val, hb⟩)]
  simp [dotPos, a.2]

/-- **The crossings of the first block.** -/
theorem kCut_head_ψ (h1 : IsInd3At σK fK 1) (p : ℕ) :
    IsInd3At σK fK (plusHeadEmb j hj Q Λ Λc θ (ψ p) ⊗ₜ[k] (1 : TensorKLR Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))) := by
  have hφ : plusHeadEmb j hj Q Λ Λc θ (ψ p) = ψ p := by
    rw [AlgEquiv.coe_toAlgHom, relabelEquiv_apply, relabelHom_ψ]
  by_cases hp : p + 1 < Multiset.card (stendhalWeight j θ)
  swap
  · rw [hφ, ψ_eq_zero p (by rw [Multiset.card_map]; omega), TensorProduct.zero_tmul]
    exact IsInd3At.zero _ _
  refine isInd3At_of_concat3_eq j hj Q Λ Λc θ γ ν₀ Y hQ L' h1 _ _
    (by rw [hφ, concat3_ψ_tmul_one (by rw [Multiset.card_map]; exact hp)]) fun y v => ?_
  have h1' : (1 : TensorKLR Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))) =
      plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1 := by
    rw [map_one, map_one, Algebra.TensorProduct.one_def]
  have hc := castLabels_cutAffineMap_smul_kCutUnit j hj Q Λ θ γ Y hQ
    (cutHeadEmb j hj Q Λ θ (ψ p) ⊗ₜ[k] cutTailEmb j hj Q Λ γ 1) (ψ p)
    (by rw [map_one, relabelEquiv_apply, relabelHom_ψ,
      KLRAlgebra.concat_ψ_tmul_one (by rw [Multiset.card_map]; exact hp)]) y
  rw [cutInputMap_emb, tensorOfKLR_one] at hc
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_ψ Q (Λ₂ := cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))
      (plusBlockLabels_head Λ Λc j hj) θ p, relabel_tensorOfKLR_one, relabel_tensorOfKLR_one,
    one_smul, kCutInputMap_tmul, kCutInputMap_tmul]
  have hpc : crossPos (cutPos j hj θ γ).val (Multiset.card (stendhalWeight 2 ν₀)) p = p := by
    simp only [crossPos]
    split_ifs <;> omega
  rw [← hc, cast_c_cutAffineMap_ψ, ← BalancedTensor.op_smul_tmul,
    op_ψ_smul_capSum _ _ p (Or.inl hp), ← BalancedTensor.smul_tmul', kCutOneStepRep_ψ, hpc]

/-- **The dots of the last block.** -/
theorem kCut_tail_x (h1 : IsInd3At σK fK 1) (c : Fin (Multiset.card (stendhalWeight (ℓ - j) γ))) :
    IsInd3At σK fK ((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      ((1 : KLRAlgebra k Sp (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))) ⊗ₜ[k]
        plusTailEmb j hj Q Λ Λc γ (x c))) := by
  have hφ : plusTailEmb j hj Q Λ Λc γ (x c) =
      x (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _).symm c)) := by
    simp only [plusTailEmb, plusTailEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_x]
  refine isInd3At_of_concat3_eq j hj Q Λ Λc θ γ ν₀ Y hQ L' h1 _ _
    (by rw [hφ, concat3_one_tmul_one_tmul_x]) fun y v => ?_
  have h1' : ((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      ((1 : KLRAlgebra k Sp (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))) ⊗ₜ[k]
        plusTailEmb j hj Q Λ Λc γ (x c))) =
      plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (x c)) := by
    rw [map_one, map_one]
  have hc := castLabels_cutAffineMap_smul_kCutUnit j hj Q Λ θ γ Y hQ
    (cutHeadEmb j hj Q Λ θ 1 ⊗ₜ[k] cutTailEmb j hj Q Λ γ (x c))
    (x (Seq.posR _ (Fin.cast (Multiset.card_map _ _).symm c)))
    (by rw [map_one, relabelEquiv_apply, relabelHom_x, KLRAlgebra.concat_one_tmul_x]) y
  rw [cutInputMap_emb, tensorOfKLR_one] at hc
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_x Q (Λ₂ := cutLabels j hj Λ ∘ Fin.natAdd j)
      (plusBlockLabels_tail Λ Λc j hj) γ c, relabel_tensorOfKLR_one, relabel_tensorOfKLR_one,
    one_smul, kCutInputMap_tmul, kCutInputMap_tmul]
  have hb : Multiset.card (stendhalWeight j θ) + c.val <
      Multiset.card (stendhalWeight ℓ (θ + γ)) := by
    have := c.2
    simp only [card_stendhalWeight, Multiset.card_add] at this ⊢
    omega
  rw [← hc, cast_c_cutAffineMap_x j hj Q Λ θ γ _ ⟨_, hb⟩ (by simp),
    ← BalancedTensor.op_smul_tmul, op_x_smul_capSum, ← BalancedTensor.smul_tmul',
    kCutOneStepRep_x _ _ _ _ _ _ _ _ _ _ _ _
      (dotPos (j := j) (hj := hj) (ν₀ := ν₀) (cutPos j hj θ γ) ⟨_, hb⟩)]
  simp [dotPos]
  omega

/-- **The crossings of the last block.** -/
theorem kCut_tail_ψ (h1 : IsInd3At σK fK 1) (r : ℕ) :
    IsInd3At σK fK ((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      ((1 : KLRAlgebra k Sp (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))) ⊗ₜ[k]
        plusTailEmb j hj Q Λ Λc γ (ψ r))) := by
  have hφ : plusTailEmb j hj Q Λ Λc γ (ψ r) = ψ r := by
    simp only [plusTailEmb, plusTailEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_ψ]
  by_cases hr : r + 1 < Multiset.card (stendhalWeight (ℓ - j) γ)
  swap
  · rw [hφ, ψ_eq_zero r (by simp only [Multiset.card_map]; omega), TensorProduct.tmul_zero,
      TensorProduct.tmul_zero]
    exact IsInd3At.zero _ _
  refine isInd3At_of_concat3_eq j hj Q Λ Λc θ γ ν₀ Y hQ L' h1 _ _
    (by rw [hφ, concat3_one_tmul_one_tmul_ψ (by simp only [Multiset.card_map]; exact hr)])
    fun y v => ?_
  have h1' : ((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      ((1 : KLRAlgebra k Sp (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))) ⊗ₜ[k]
        plusTailEmb j hj Q Λ Λc γ (ψ r))) =
      plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (ψ r)) := by
    rw [map_one, map_one]
  have hc := castLabels_cutAffineMap_smul_kCutUnit j hj Q Λ θ γ Y hQ
    (cutHeadEmb j hj Q Λ θ 1 ⊗ₜ[k] cutTailEmb j hj Q Λ γ (ψ r))
    (ψ (Multiset.card (stendhalWeight j θ) + r))
    (by rw [map_one, relabelEquiv_apply, relabelHom_ψ,
      KLRAlgebra.concat_one_tmul_ψ (by simp only [Multiset.card_map]; exact hr),
      Multiset.card_map]) y
  rw [cutInputMap_emb, tensorOfKLR_one] at hc
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_ψ Q (Λ₂ := cutLabels j hj Λ ∘ Fin.natAdd j)
      (plusBlockLabels_tail Λ Λc j hj) γ r, relabel_tensorOfKLR_one, relabel_tensorOfKLR_one,
    one_smul, kCutInputMap_tmul, kCutInputMap_tmul]
  have hpc : crossPos (cutPos j hj θ γ).val (Multiset.card (stendhalWeight 2 ν₀))
      (Multiset.card (stendhalWeight j θ) + r) =
      Multiset.card (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))))
        (stendhalWeight j θ)) + (Multiset.card (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀))) +
            r) := by
    simp only [crossPos, Multiset.card_map]
    split_ifs <;> omega
  rw [← hc, cast_c_cutAffineMap_ψ, ← BalancedTensor.op_smul_tmul,
    op_ψ_smul_capSum _ _ (Multiset.card (stendhalWeight j θ) + r)
      (Or.inr (Nat.le_add_right _ _)), ← BalancedTensor.smul_tmul',
    kCutOneStepRep_ψ, hpc]

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- A diagram at the maximum acting on `L'` acts on the coefficients of the cap. -/
theorem toCapCoef_tensorOfKLR_smul
    (a : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) (v : L') :
    toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) (tensorOfKLR Q Λc ν₀ (hflip a) • v) =
      op (cupMap k Q Λc ν₀ a) • toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v :=
  (op_smul_capCoef a v).symm

/-- **The dots of the middle block.** -/
theorem kCut_mid_x (h1 : IsInd3At σK fK 1) (b : Fin (Multiset.card (stendhalWeight 2 ν₀))) :
    IsInd3At σK fK ((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ (x b) ⊗ₜ[k] (1 : KLRAlgebra k Sp
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))))) := by
  have hφ : plusMidEmb j hj Q Λ Λc ν₀ (x b) =
      x (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _).symm b)) := by
    simp only [plusMidEmb, plusMidEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_x]
  refine isInd3At_of_concat3_eq j hj Q Λ Λc θ γ ν₀ Y hQ L' h1 _ _
    (by rw [hφ, concat3_one_tmul_x_tmul_one]) fun y v => ?_
  have h1' : (1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ (x b) ⊗ₜ[k] (1 : KLRAlgebra k Sp
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))) =
      plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ (x b) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1) := by
    rw [map_one, map_one]
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_x Q (Λ₂ := Λc) (plusBlockLabels_cup Λ Λc j hj) ν₀ b,
    relabel_tensorOfKLR_one, relabel_tensorOfKLR_one, ← Algebra.TensorProduct.one_def, one_smul,
    kCutInputMap_tmul, kCutInputMap_tmul]
  rw [← hflip_x, toCapCoef_tensorOfKLR_smul, capSum_box_x, ← BalancedTensor.smul_tmul',
    kCutOneStepRep_x _ _ _ _ _ _ _ _ _ _ _ _ ⟨(cutPos j hj θ γ).val + b.val,
      add_lt_M (Nat.lt_succ_iff.1 (cutPos j hj θ γ).2) b⟩]
  simp

/-- **The crossings of the middle block.** -/
theorem kCut_mid_ψ (h1 : IsInd3At σK fK 1) (q : ℕ) :
    IsInd3At σK fK ((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ (ψ q) ⊗ₜ[k] (1 : KLRAlgebra k Sp
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))))) := by
  have hφ : plusMidEmb j hj Q Λ Λc ν₀ (ψ q) = ψ q := by
    simp only [plusMidEmb, plusMidEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_ψ]
  by_cases hq : q + 1 < Multiset.card (stendhalWeight 2 ν₀)
  swap
  · rw [hφ, ψ_eq_zero q (by simp only [Multiset.card_map]; omega), TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]
    exact IsInd3At.zero _ _
  refine isInd3At_of_concat3_eq j hj Q Λ Λc θ γ ν₀ Y hQ L' h1 _ _
    (by rw [hφ, concat3_one_tmul_ψ_tmul_one (by simp only [Multiset.card_map]; exact hq)])
    fun y v => ?_
  have h1' : (1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ (ψ q) ⊗ₜ[k] (1 : KLRAlgebra k Sp
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))) =
      plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ (ψ q) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1) := by
    rw [map_one, map_one]
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_ψ Q (Λ₂ := Λc) (plusBlockLabels_cup Λ Λc j hj) ν₀ q,
    relabel_tensorOfKLR_one, relabel_tensorOfKLR_one, ← Algebra.TensorProduct.one_def, one_smul,
    kCutInputMap_tmul, kCutInputMap_tmul]
  rw [← hflip_ψ, toCapCoef_tensorOfKLR_smul, capSum_box_ψ _ _ hq, ← BalancedTensor.smul_tmul',
    kCutOneStepRep_ψ, Multiset.card_map]

end Categorification.Stendhal.CupCap
