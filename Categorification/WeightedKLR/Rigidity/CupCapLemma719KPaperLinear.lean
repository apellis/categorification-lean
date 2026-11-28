/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaper

/-!
# Lemma 7.19 (K) as an isomorphism of `T^{λ⁺}`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19 (K).
The isomorphism `kPaperEquiv : K^σ(S(Z)) ≅ S_+(Z ⊠ L)` is linear over `T^{λ⁺}`, along the
identification `T^{λ⁺}(θ_h + (ν₀ + θ_t)) ≅ T^{λ⁺}((θ_h + θ_t) + ν₀)` of the weights
(`kPaperEquiv_smul`). With `K^σ(S(Z))` regarded over `T^{λ⁺}(θ_h + (ν₀ + θ_t))` through this
identification (`KPaperLeftPlus`), it is an isomorphism of modules (`kPaperModuleEquiv`).

## Main definitions

* `Stendhal.CupCap.KPaperLeftPlus`: `K^σ(S(Z))` over `T^{λ⁺}(θ_h + (ν₀ + θ_t))`.
* `Stendhal.CupCap.kPaperModuleEquiv`: **Lemma 7.19 (K)** as an isomorphism of modules.

## Main results

* `Stendhal.CupCap.kCutPhiEquiv_symm_rep`: the inverse of the lemma at the cut is linear.
* `Stendhal.CupCap.kPaperEquiv_smul`: `kPaperEquiv` is linear over `T^{λ⁺}`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

section Cut

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  {L' : Type} [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **The inverse of the lemma at the cut is linear over `T^{λ⁺}`.** -/
theorem kCutPhiEquiv_symm_rep
    (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
    (z : KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    (kCutPhiEquiv Y hQ hR hP hPL hκ).symm (kCutRep j hj Q Λ Λc θ γ ν₀ Y hQ L' t z) =
      plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ t
        ((kCutPhiEquiv Y hQ hR hP hPL hκ).symm z) := by
  refine (kCutPhiEquiv Y hQ hR hP hPL hκ).injective ?_
  rw [LinearEquiv.apply_symm_apply, kCutPhiEquiv_apply, kCutPhi_action,
    ← kCutPhiEquiv_apply Y hQ hR hP hPL hκ, LinearEquiv.apply_symm_apply]

end Cut

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (θ : Fin (j + (ℓ - j)) → Multiset I) (hQ : KLRSymm Q)
  (Z : ModuleCat (kPaperAlg j hj Q Λ θ))
  (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "w₁" => singWeight j (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "w₂" => singWeight (ℓ - j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "Tq" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (w₁ + (ν₀ + w₂))
set_option hygiene false in
local notation "cast_w" =>
  castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq w₁ w₂ ν₀)

/-- **The right side is linear over `T^{λ⁺}`.** -/
theorem kPaperRightEquiv_action (t : Tq)
    (y : KCutSource j hj Q Λ Λc w₁ w₂ ν₀ (KPaperY j hj Q Λ θ hQ Z) hQ L') :
    kPaperRightEquiv j hj Q Λ θ hQ Z Λc ν₀ L'
        (plusStandardAction Q Λ Λc j hj w₁ ν₀ w₂ _ hQ t y) =
      t • kPaperRightEquiv j hj Q Λ θ hQ Z Λc ν₀ L' y :=
  plusStandardMap_action Q Λ Λc j hj w₁ ν₀ w₂ hQ _ t y

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (w₁ + w₂) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **Lemma 7.19 (K) is linear over `T^{λ⁺}`**, along the identification of the weights
`θ_h + (ν₀ + θ_t) = (θ_h + θ_t) + ν₀`. -/
theorem kPaperEquiv_smul (t : Tq) (x : KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L') :
    kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ (cast_w t • x) =
      t • kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ x := by
  have h1 : kPaperLeftEquiv j hj Q Λ θ hQ Z Λc ν₀ L' (cast_w t • x) =
      kCutRep j hj Q Λ Λc w₁ w₂ ν₀ (KPaperY j hj Q Λ θ hQ Z) hQ L' t
        (kPaperLeftEquiv j hj Q Λ θ hQ Z Λc ν₀ L' x) :=
    (kPaperLeftEquiv j hj Q Λ θ hQ Z Λc ν₀ L').map_smul _ x
  have h2 := kCutPhiEquiv_symm_rep (KPaperY j hj Q Λ θ hQ Z) hQ hR hP hPL hκ t
    (kPaperLeftEquiv j hj Q Λ θ hQ Z Λc ν₀ L' x)
  exact (congrArg (fun z => kPaperRightEquiv j hj Q Λ θ hQ Z Λc ν₀ L'
      ((kCutPhiEquiv (KPaperY j hj Q Λ θ hQ Z) hQ hR hP hPL hκ).symm z)) h1).trans
    ((congrArg (kPaperRightEquiv j hj Q Λ θ hQ Z Λc ν₀ L') h2).trans
      (kPaperRightEquiv_action j hj Q Λ θ hQ Z Λc ν₀ L' t _))

/-- `K^σ(S(Z))` as a module over `T^{λ⁺}(θ_h + (ν₀ + θ_t))`, through the identification of the
weights. -/
@[nolint unusedArguments]
def KPaperLeftPlus : Type := KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L'

instance : AddCommGroup (KPaperLeftPlus j hj Q Λ θ hQ Z Λc ν₀ L') :=
  inferInstanceAs (AddCommGroup (KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L'))

instance : Module Tq (KPaperLeftPlus j hj Q Λ θ hQ Z Λc ν₀ L') :=
  Module.compHom (KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L') (cast_w).toAlgHom.toRingHom

/-- **Webster, arXiv:1309.3796v3, Lemma 7.19 (K), as an isomorphism of modules**:
`K S(Z) ≅ S_+(Z ⊠ L)` over `T^{λ⁺}(θ_h + (ν₀ + θ_t))`, with the conventions and the route
hypotheses of `kPaperEquiv`. -/
def kPaperModuleEquiv :
    KPaperLeftPlus j hj Q Λ θ hQ Z Λc ν₀ L' ≃ₗ[Tq]
      (plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).obj
        (plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L') where
  toFun x := kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ x
  invFun z := (kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ).symm z
  left_inv x := (kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ).symm_apply_apply x
  right_inv z := (kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ).apply_symm_apply z
  map_add' x x' := map_add (kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ) x x'
  map_smul' t x := kPaperEquiv_smul j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ t x

theorem kPaperModuleEquiv_apply (x : KPaperLeftPlus j hj Q Λ θ hQ Z Λc ν₀ L') :
    kPaperModuleEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ x =
      kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ x := rfl

end Categorification.Stendhal.CupCap
