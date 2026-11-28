/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaperLeft
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPhiPsi
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusOuterCut

/-!
# Lemma 7.19 (K): `K S(Z) ≅ S_+(Z ⊠ L)`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19 (K)
(subscripts as corrected in Definition 7.18). For a module `Z` over the singleton blocks
`T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_ℓ}(θ_ℓ)` of `λ`, split at the `j`-th red strand, and a module `L`
over `T^{μ μ*}(ν₀)`, the reflected coevaluation of the standardization in stages `S(Z)` is the
partial standardization `S_+` of `Z ⊠ L` (`kPaperEquiv`).

The proof composes three identifications:

* `K^σ(S(Z)) ≅ K^σ(S_cut Y)` for the standardizations `Y` of the two blocks of `Z`
  (`kPaperLeftEquiv`, the staged associativity `singCutEquiv`);
* `K^σ(S_cut Y) ≅ PlusStandard(Y ⊠ L)`, the lemma at the cut (`kCutPhiEquiv`);
* `PlusStandard(Y ⊠ L) ≅ S_+(Z ⊠ L)` (`kPaperRightEquiv`): `Y` is `plusOuterPair Z`
  (`cutPairEquiv`) and the outer standardizations of `S_+` commute with `⊠ L`
  (`plusOuterTensorEquiv`).

## Conventions and hypotheses

Webster does not distinguish left and right modules. `K` is read through the horizontal
reflections (`CoeTensor`, `ReflectedCap`), and the coefficients of the cap are `CapCoef L`.
`S(Z)` is regarded over `T^λ(θ_h + θ_t)` through `θ_1 + ⋯ + θ_ℓ = θ_h + θ_t` and the
reindexing of the labels (`KPaperS`). The route hypotheses are those of `kCutPhiEquiv`:
`hL` (violated idempotents act by zero on `L`), `hR` (`MidKLRRel`), `hP`, `hPL` (`PullOff`,
`PullOffLeft`) and `hκ` (the cup scalars are units).

## Main definitions

* `Stendhal.CupCap.plusStandardEquiv`: partial standardization of `λ⁺` of an isomorphism.
* `Stendhal.CupCap.kPaperRightEquiv`: `PlusStandard(Y ⊠ L) ≅ S_+(Z ⊠ L)`.
* `Stendhal.CupCap.kPaperEquiv`: **Lemma 7.19 (K)**, `K^σ(S(Z)) ≅ S_+(Z ⊠ L)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-! ### Partial standardization of `λ⁺` of an isomorphism -/

section PlusEquiv

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ) (θ β γ : Multiset I)
  (hQ : KLRSymm Q)
  {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
  [AddCommGroup N'] [Module k N'] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N']
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N']
  [AddCommGroup N''] [Module k N''] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N'']
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N'']

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev plusFactorNonAssocSemiring :
    NonAssocSemiring (PlusFactorAlgebra Q Λ Λc j hj θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] plusFactorNonAssocSemiring

theorem plusStandardMap_id :
    plusStandardMap Q Λ Λc j hj θ β γ hQ
      (LinearMap.id : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N) = LinearMap.id := by
  have h : blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
      (plusInputHom Q Λ Λc j hj θ β γ
        (LinearMap.id : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N)) = LinearMap.id :=
    LinearMap.ext fun z => LinearMap.congr_fun (cutStandardMap_id Q _ β γ) z
  exact (congrArg (cutStandardMap Q _ θ (β + γ)) h).trans (cutStandardMap_id Q _ θ (β + γ))

theorem plusStandardMap_comp (g : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (g' : N' →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N'')
    (z : PlusStandard Q Λ Λc j hj θ β γ N hQ) :
    plusStandardMap Q Λ Λc j hj θ β γ hQ (g' ∘ₗ g) z =
      plusStandardMap Q Λ Λc j hj θ β γ hQ g' (plusStandardMap Q Λ Λc j hj θ β γ hQ g z) := by
  have h : blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
      (plusInputHom Q Λ Λc j hj θ β γ (g' ∘ₗ g)) =
      blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ (plusInputHom Q Λ Λc j hj θ β γ g') ∘ₗ
        blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ (plusInputHom Q Λ Λc j hj θ β γ g) :=
    LinearMap.ext fun w => cutStandardMap_comp Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ (plusInputHom Q Λ Λc j hj θ β γ g))
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ (plusInputHom Q Λ Λc j hj θ β γ g')) w
  exact (congrArg (fun f => cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ) f z) h).trans
    (cutStandardMap_comp Q (plusBlockLabels Λ Λc j hj) θ (β + γ) _ _ z)

theorem plusStandardMap_comp_eq_self (g : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (g' : N' →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N) (h : g' ∘ₗ g = LinearMap.id)
    (z : PlusStandard Q Λ Λc j hj θ β γ N hQ) :
    plusStandardMap Q Λ Λc j hj θ β γ hQ g' (plusStandardMap Q Λ Λc j hj θ β γ hQ g z) = z := by
  rw [← plusStandardMap_comp, h, plusStandardMap_id]
  rfl

/-- **The partial standardization of `λ⁺` of an isomorphism** of modules over the three
blocks. -/
def plusStandardEquiv (e : N ≃ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N') :
    PlusStandard Q Λ Λc j hj θ β γ N hQ ≃ₗ[k] PlusStandard Q Λ Λc j hj θ β γ N' hQ where
  toFun := plusStandardMap Q Λ Λc j hj θ β γ hQ e.toLinearMap
  invFun := plusStandardMap Q Λ Λc j hj θ β γ hQ e.symm.toLinearMap
  left_inv z := plusStandardMap_comp_eq_self Q Λ Λc j hj θ β γ hQ e.toLinearMap
    e.symm.toLinearMap (LinearEquiv.symm_comp e) z
  right_inv z := plusStandardMap_comp_eq_self Q Λ Λc j hj θ β γ hQ e.symm.toLinearMap
    e.toLinearMap (LinearEquiv.comp_symm e) z
  map_add' := map_add _
  map_smul' := map_smul _

theorem plusStandardEquiv_apply (e : N ≃ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (z : PlusStandard Q Λ Λc j hj θ β γ N hQ) :
    plusStandardEquiv Q Λ Λc j hj θ β γ hQ e z =
      plusStandardMap Q Λ Λc j hj θ β γ hQ e.toLinearMap z := rfl

end PlusEquiv

/-! ### The right side -/

section Right

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
local notation "PF" => PlusFactorAlgebra Q Λ Λc j hj w₁ ν₀ w₂

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev pfNonAssocSemiring : NonAssocSemiring PF := Semiring.toNonAssocSemiring

attribute [local instance high] pfNonAssocSemiring

/-- The standardizations of the two blocks, as `plusOuterPair` (`cutPairEquiv`). -/
abbrev kPaperPair :
    KPaperY j hj Q Λ θ hQ Z ≃ₗ[cutFactorAlgebra Q (cutLabels j hj Λ) w₁ w₂]
      cutPairTarget Q hQ Λ j hj θ Z :=
  cutPairEquiv Q hQ Λ j hj θ Z

/-- `Y ⊠ L ≅ plusOuterPair Z ⊠ L` over the three blocks of `λ⁺`. -/
def kPaperMidEquiv :
    MidSpect (k := k) (KPaperY j hj Q Λ θ hQ Z) L' ≃ₗ[PF]
      MidSpect (k := k) (cutPairTarget Q hQ Λ j hj θ Z) L' :=
  LinearEquiv.ofLinearMap (midSpectMap (B := TensorProductAlgebra k Q Λc ν₀)
      (kPaperPair j hj Q Λ θ hQ Z).toLinearMap)
    (midSpectMap (B := TensorProductAlgebra k Q Λc ν₀)
      (kPaperPair j hj Q Λ θ hQ Z).symm.toLinearMap)
    (LinearMap.ext fun z => by
      induction (show cutPairTarget Q hQ Λ j hj θ Z ⊗[k] L' from z) using
        TensorProduct.inductionOn with
      | tmul y v =>
        exact congrArg (fun y' => midSpectTmul (k := k) y' v)
          ((kPaperPair j hj Q Λ θ hQ Z).apply_symm_apply y)
      | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy))
    (LinearMap.ext fun z => by
      induction (show KPaperY j hj Q Λ θ hQ Z ⊗[k] L' from z) using
        TensorProduct.inductionOn with
      | tmul y v =>
        exact congrArg (fun y' => midSpectTmul (k := k) y' v)
          ((kPaperPair j hj Q Λ θ hQ Z).symm_apply_apply y)
      | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy))

/-- `plusOuterPair Z ⊠ L ≅ plusOuterStd (Z ⊠ L)` (`plusOuterTensorEquiv`), over the three blocks
of `λ⁺`. -/
def kPaperOuterEquiv :
    MidSpect (k := k) (cutPairTarget Q hQ Λ j hj θ Z) L' ≃ₗ[PF]
      PlusWrap Q Λ Λc j hj w₁ ν₀ w₂
        ((plusOuterStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).obj
          (plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L')) :=
  plusOuterTensorEquiv Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L'

set_option hygiene false in
local notation "PO" => (plusOuterStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j))
  (θ ∘ Fin.natAdd j)).obj
    (plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L')

/-- The underlying group of `S_+(Z ⊠ L)`, with its `k`-module structure through `T^{λ⁺}`. -/
def kPaperStagedCarrier :
    PlusStandard Q Λ Λc j hj w₁ ν₀ w₂ (PlusWrap Q Λ Λc j hj w₁ ν₀ w₂ PO) hQ ≃ₗ[k]
      (plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).obj
        (plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L') where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := (LinearMap.congr_fun ((plusStandardAction Q Λ Λc j hj w₁ ν₀ w₂
    (PlusWrap Q Λ Λc j hj w₁ ν₀ w₂ PO) hQ).commutes c) z).symm

/-- **The right side of Lemma 7.19 (K)**: `PlusStandard(Y ⊠ L) ≅ S_+(Z ⊠ L)`. -/
def kPaperRightEquiv :
    KCutSource j hj Q Λ Λc w₁ w₂ ν₀ (KPaperY j hj Q Λ θ hQ Z) hQ L' ≃ₗ[k]
      (plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).obj
        (plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L') :=
  (plusStandardEquiv Q Λ Λc j hj w₁ ν₀ w₂ hQ
    ((kPaperMidEquiv j hj Q Λ θ hQ Z Λc ν₀ L').trans
      (kPaperOuterEquiv j hj Q Λ θ hQ Z Λc ν₀ L'))).trans
    (kPaperStagedCarrier j hj Q Λ θ hQ Z Λc ν₀ L')

end Right

/-! ### Lemma 7.19 (K) -/

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

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (w₁ + w₂) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **Webster, arXiv:1309.3796v3, Lemma 7.19 (K)**: `K S(Z) ≅ S_+(Z ⊠ L)`, for a module `Z`
over the singleton blocks of `λ` split at the `j`-th red strand. `K` is the reflected
coevaluation `K^σ` with the cap coefficients `CapCoef L` and `S(Z)` the standardization in
stages over `T^λ(θ_h + θ_t)` (`KPaperS`); the route hypotheses `hL`, `hR`, `hP`, `hPL`, `hκ`
are those of the lemma at the cut (`kCutPhiEquiv`). -/
def kPaperEquiv :
    KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L' ≃ₗ[k]
      (plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).obj
        (plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L') :=
  (((kPaperLeftEquiv j hj Q Λ θ hQ Z Λc ν₀ L').restrictScalars k).trans
    (kCutPhiEquiv (KPaperY j hj Q Λ θ hQ Z) hQ hR hP hPL hκ).symm).trans
    (kPaperRightEquiv j hj Q Λ θ hQ Z Λc ν₀ L')

end Categorification.Stendhal.CupCap
