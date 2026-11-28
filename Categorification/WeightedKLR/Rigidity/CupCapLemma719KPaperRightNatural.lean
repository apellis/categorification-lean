/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaper
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaperLeftNatural
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusOuterNatural

/-!
# Naturality of Lemma 7.19 (K)

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19 (K),
for the derived form of the lemma: the identification `PlusStandard(Y ⊠ L) ≅ S_+(Z ⊠ L)`
(`kPaperRightEquiv`), and with it `K^σ(S(Z)) ≅ S_+(Z ⊠ L)` (`kPaperEquiv`), commutes with the
maps induced by a map `g : Z → Z'` of modules over the singleton blocks.

## Main results

* `Stendhal.CupCap.kPaperRightEquiv_natural`: `PlusStandard(Y ⊠ L) ≅ S_+(Z ⊠ L)` is natural.
* `Stendhal.CupCap.kPaperEquiv_natural`: **Lemma 7.19 (K) is natural in `Z`**.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (θ : Fin (j + (ℓ - j)) → Multiset I) (hQ : KLRSymm Q)
  {Z Z' : ModuleCat (kPaperAlg j hj Q Λ θ)} (g : Z ⟶ Z')
  (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "w₁" => singWeight j (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "w₂" => singWeight (ℓ - j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "PF" => PlusFactorAlgebra Q Λ Λc j hj w₁ ν₀ w₂
set_option hygiene false in
local notation "Cp" => TensorProductAlgebra k Q Λc ν₀
set_option hygiene false in
local notation "inMap" => plusTensorInputMap Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j))
  (θ ∘ Fin.natAdd j) g L'
set_option hygiene false in
local notation "outMap" => (plusOuterStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j))
  (θ ∘ Fin.natAdd j)).map inMap

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev pfNonAssocSemiringR : NonAssocSemiring PF := Semiring.toNonAssocSemiring

attribute [local instance high] pfNonAssocSemiringR

/-- `Y ⊠ L ≅ plusOuterStd (Z ⊠ L)` is natural on pure tensors. -/
theorem kPaperMidOuter_natural_tmul (y : KPaperY j hj Q Λ θ hQ Z) (v : L') :
    kPaperOuterEquiv j hj Q Λ θ hQ Z' Λc ν₀ L' (kPaperMidEquiv j hj Q Λ θ hQ Z' Λc ν₀ L'
        (midSpectMap (B := Cp) (kPaperYMap j hj Q Λ θ hQ g) (midSpectTmul (k := k) y v))) =
      plusWrapHom Q Λ Λc j hj w₁ ν₀ w₂ outMap
        (kPaperOuterEquiv j hj Q Λ θ hQ Z Λc ν₀ L'
          (kPaperMidEquiv j hj Q Λ θ hQ Z Λc ν₀ L' (midSpectTmul (k := k) y v))) :=
  (congrArg (fun y' => plusOuterTensorEquiv Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j))
      (θ ∘ Fin.natAdd j) Z' L' (midSpectTmul (k := k) y' v))
    (cutPairEquiv_natural Q hQ Λ j hj θ g y)).trans
    (plusOuterTensorEquiv_natural_tmul Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j))
      (θ ∘ Fin.natAdd j) g L' (cutPairEquiv Q hQ Λ j hj θ Z y) v)

/-- **`Y ⊠ L ≅ plusOuterStd (Z ⊠ L)` is natural in `Z`**, as linear maps over the three
blocks of `λ⁺`. -/
theorem kPaperMidOuter_natural :
    ((kPaperMidEquiv j hj Q Λ θ hQ Z' Λc ν₀ L').trans
        (kPaperOuterEquiv j hj Q Λ θ hQ Z' Λc ν₀ L')).toLinearMap ∘ₗ
        midSpectMap (B := Cp) (kPaperYMap j hj Q Λ θ hQ g) =
      plusWrapHom Q Λ Λc j hj w₁ ν₀ w₂ outMap ∘ₗ
        ((kPaperMidEquiv j hj Q Λ θ hQ Z Λc ν₀ L').trans
          (kPaperOuterEquiv j hj Q Λ θ hQ Z Λc ν₀ L')).toLinearMap := by
  refine LinearMap.ext fun z => ?_
  induction (show KPaperY j hj Q Λ θ hQ Z ⊗[k] L' from z) using TensorProduct.inductionOn with
  | tmul y v => exact kPaperMidOuter_natural_tmul j hj Q Λ θ hQ g Λc ν₀ L' y v
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

/-- **`PlusStandard(Y ⊠ L) ≅ S_+(Z ⊠ L)` is natural in `Z`.** -/
theorem kPaperRightEquiv_natural
    (y : KCutSource j hj Q Λ Λc w₁ w₂ ν₀ (KPaperY j hj Q Λ θ hQ Z) hQ L') :
    kPaperRightEquiv j hj Q Λ θ hQ Z' Λc ν₀ L'
        (kCutSourceMap j hj Q Λ Λc w₁ w₂ ν₀ hQ L' (kPaperYMap j hj Q Λ θ hQ g) y) =
      ((plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).map
        inMap).hom (kPaperRightEquiv j hj Q Λ θ hQ Z Λc ν₀ L' y) :=
  (plusStandardMap_comp Q Λ Λc j hj w₁ ν₀ w₂ hQ _ _ y).symm.trans
    ((congrArg (fun f => plusStandardMap Q Λ Λc j hj w₁ ν₀ w₂ hQ f y)
      (kPaperMidOuter_natural j hj Q Λ θ hQ g Λc ν₀ L')).trans
      (plusStandardMap_comp Q Λ Λc j hj w₁ ν₀ w₂ hQ _ _ y))

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : CapCoef Q Λc ν₀ L'), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (w₁ + w₂) ν₀ (CapCoef Q Λc ν₀ L') hL)
  (hP : PullOff k Q Λc ν₀ (CapCoef Q Λc ν₀ L'))
  (hPL : PullOffLeft k Q Λc ν₀ (CapCoef Q Λc ν₀ L'))
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **Webster, arXiv:1309.3796v3, Lemma 7.19 (K), naturality**: the isomorphism
`K S(Z) ≅ S_+(Z ⊠ L)` (`kPaperEquiv`) is natural in the module `Z` over the singleton blocks,
for the route hypotheses `hL`, `hR`, `hP`, `hPL`, `hκ` of `kPaperEquiv`. -/
theorem kPaperEquiv_natural (x : KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L') :
    kPaperEquiv j hj Q Λ θ hQ Z' Λc ν₀ L' hR hP hPL hκ
        (kPaperLeftMap j hj Q Λ θ hQ g Λc ν₀ L' x) =
      ((plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).map
        inMap).hom (kPaperEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ x) :=
  (congrArg (fun t => kPaperRightEquiv j hj Q Λ θ hQ Z' Λc ν₀ L'
      ((kCutPhiEquiv (KPaperY j hj Q Λ θ hQ Z') hQ hR hP hPL hκ).symm t))
    (kPaperLeftEquiv_natural j hj Q Λ θ hQ g Λc ν₀ L' x)).trans
    ((congrArg (kPaperRightEquiv j hj Q Λ θ hQ Z' Λc ν₀ L')
      (kCutPhiEquiv_symm_natural j hj Q Λ Λc w₁ w₂ ν₀ hQ L' (kPaperYMap j hj Q Λ θ hQ g)
        hR hP hPL hκ _)).trans
      (kPaperRightEquiv_natural j hj Q Λ θ hQ g Λc ν₀ L' _))

end Categorification.Stendhal.CupCap
