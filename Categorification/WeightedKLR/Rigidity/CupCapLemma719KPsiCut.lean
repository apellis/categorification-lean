/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiDescent

/-!
# The family of maps `f_y` out of the reflected cap

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the maps
`f_y : K^{λ⁺}_λ → S_+(Y ⊠ L')` depend `k`-linearly on `y ∈ Y`.

## Main definitions

* `Stendhal.CupCap.kCapFamily`: the `k`-linear map `y ↦ f_y`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "fM" => kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L'

theorem kSrcU_add_left (y y' : Y) (v : L') : U (y + y') v = U y v + U y' v := by
  rw [← map_add]
  exact congrArg (kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L') (TensorProduct.add_tmul y y' v)

theorem kSrcU_smul_left (c : k) (y : Y) (v : L') : U (c • y) v = c • U y v := by
  rw [← map_smul]
  exact congrArg (kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L') (TensorProduct.smul_tmul' c y v).symm

theorem kModelMap_add_left (y y' : Y) (t : MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    fM (y + y') t = fM y t + fM y' t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul z v =>
    rw [kModelMap_tmul, kModelMap_tmul, kModelMap_tmul, kSrcU_add_left, smul_add]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]; abel

theorem kModelMap_smul_left (c : k) (y : Y) (t : MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    fM (c • y) t = c • fM y t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z v =>
    rw [kModelMap_tmul, kModelMap_tmul, kSrcU_smul_left, smul_comm]
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

variable {j hj Q Λ Λc θ γ ν₀ L'}
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

theorem kCapLin_add (y y' : Y) :
    kCapLin Y hQ hR hP hPL hκ (y + y') =
      kCapLin Y hQ hR hP hPL hκ y + kCapLin Y hQ hR hP hPL hκ y' := by
  refine LinearMap.ext fun r => ?_
  obtain ⟨c, rfl⟩ := toRefl_surjective r
  exact kModelMap_add_left j hj Q Λ Λc θ γ ν₀ Y hQ L' y y' _

theorem kCapLin_smul (c : k) (y : Y) :
    kCapLin Y hQ hR hP hPL hκ (c • y) = c • kCapLin Y hQ hR hP hPL hκ y := by
  refine LinearMap.ext fun r => ?_
  obtain ⟨d, rfl⟩ := toRefl_surjective r
  exact kModelMap_smul_left j hj Q Λ Λc θ γ ν₀ Y hQ L' c y _

/-- **The family `y ↦ f_y`**, `k`-linear in `y`. -/
def kCapFamily : Y →ₗ[k] (ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc →ₗ[TensorProductAlgebra k Q
    (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)] KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') where
  toFun := kCapLin Y hQ hR hP hPL hκ
  map_add' := kCapLin_add Y hQ hR hP hPL hκ
  map_smul' := kCapLin_smul Y hQ hR hP hPL hκ

end Categorification.Stendhal.CupCap
