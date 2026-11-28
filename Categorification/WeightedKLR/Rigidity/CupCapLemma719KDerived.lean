/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KDerivedCoe
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaperLinear
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaperRightNatural
import Categorification.WeightedKLR.RedStrands.PartialStandardizationDerived

/-!
# Lemma 7.19 (K) on derived categories

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19 (K)
(subscripts as corrected in Definition 7.18): `𝕂 𝕊(Z) ≅ 𝕊_+(Z ⊠ L)` naturally in `Z`, on the
derived categories.

* `S` (`kPaperSFunctor`, the standardization in stages of the singleton blocks, regarded over
  `T^λ(θ_h + θ_t)`), `Z ↦ Z ⊠ L` (`plusTensorFunctor`) and `S_+` (`plusStagedStd`) are exact,
  so they induce functors on derived categories (`Functor.mapDerivedCategory`), computed
  degreewise.
* On modules, Lemma 7.19 (K) is a natural isomorphism `K^σ ∘ S ≅ S_+ ∘ (- ⊠ L)`
  (`kModuleIso`, from `kPaperModuleEquiv` and `kPaperEquiv_natural`).
* `𝕂` on derived categories of left modules is the derived functor of `K^σ`
  (`leftCoevaluationIso`), and the module isomorphism passes to derived categories
  (`kDerivedIso`).

## Conventions and route hypotheses

`𝕂` is read on left modules through the horizontal reflections (`leftCoevaluationFunctor`),
and the comparison of derived categories of dg modules over a ring with Mathlib's derived
categories of modules (`DG.DegreeZero.derivedComparisonEquivalence`). The coefficients of the
cap are `CapCoef L`, and the weights are identified along `θ_h + (ν₀ + θ_t) = (θ_h + θ_t) + ν₀`.
The route hypotheses are those of `kPaperEquiv` (`hL`, `hP`, `hPL`, `hκ`; `hR` follows from
them by `midKLRRel`) and, for the projectivity of `K^{λ⁺}_λ` that makes `𝕂` the derived functor
of `K^σ`, those of `projective_midCapBimodule` (`hQ`, `hfin`, `hproj`).
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite DG.DegreeZero
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (θ : Fin (j + (ℓ - j)) → Multiset I) (hQ : KLRSymm Q)
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

/-! ### The standardization `S` -/

/-- **The standardization in stages `S`** of the singleton blocks of `λ`, regarded over
`T^λ(θ_h + θ_t)`. -/
abbrev kPaperSFunctor :
    ModuleCat (kPaperAlg j hj Q Λ θ) ⥤ ModuleCat (TensorProductAlgebra k Q Λ (w₁ + w₂)) :=
  kPaperStdFunctor j hj Q Λ θ hQ ⋙ ModuleCat.restrictScalars (kPaperRho j hj Q Λ θ).toRingHom

theorem moduleExactFunctor_kPaperSFunctor : ModuleExactFunctor (kPaperSFunctor j hj Q Λ θ hQ) :=
  (ModuleExactFunctor.restrictScalars _).comp ((ModuleExactFunctor.restrictScalars _).comp
    ((moduleExactFunctor_singStd Q hQ _ _ _ _).comp (ModuleExactFunctor.restrictScalars _)))

instance : (kPaperSFunctor j hj Q Λ θ hQ).Additive :=
  additive_comp' (additive_comp' inferInstance (additive_comp' inferInstance
    (singStd_additive Q hQ _ _ _ _))) inferInstance

instance : Limits.PreservesFiniteLimits (kPaperSFunctor j hj Q Λ θ hQ) :=
  (moduleExactFunctor_kPaperSFunctor j hj Q Λ θ hQ).preservesFiniteLimits

instance : Limits.PreservesFiniteColimits (kPaperSFunctor j hj Q Λ θ hQ) :=
  (moduleExactFunctor_kPaperSFunctor j hj Q Λ θ hQ).preservesFiniteColimits

/-! ### The external tensor product `- ⊠ L` -/

/-- **`Z ↦ Z ⊠ L`**, from modules over the singleton blocks to modules over the blocks of
`S_+`. -/
def plusTensorFunctor :
    ModuleCat (kPaperAlg j hj Q Λ θ) ⥤
      ModuleCat (plusSingAlg Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)) where
  obj Z := plusTensorInput Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z L'
  map g := plusTensorInputMap Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) g L'
  map_id Z := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (LinearMap.rTensor_id L' Z) (show Z ⊗[k] L' from z))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (LinearMap.rTensor_comp L' (g.hom.restrictScalars k)
      (f.hom.restrictScalars k)) (show _ ⊗[k] L' from z))

instance : (plusTensorFunctor j hj Q Λ θ Λc ν₀ L').Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (LinearMap.rTensor_add L' (f.hom.restrictScalars k)
      (g.hom.restrictScalars k)) (show _ ⊗[k] L' from z))

theorem moduleExactFunctor_plusTensorFunctor :
    ModuleExactFunctor (plusTensorFunctor j hj Q Λ θ Λc ν₀ L') :=
  ⟨fun f g h => Module.Flat.rTensor_exact L' (f := f.hom.restrictScalars k)
      (g := g.hom.restrictScalars k) h,
    fun f h => Module.Flat.rTensor_preserves_injective_linearMap (f.hom.restrictScalars k) h,
    fun f h => LinearMap.rTensor_surjective L' (g := f.hom.restrictScalars k) h⟩

instance : Limits.PreservesFiniteLimits (plusTensorFunctor j hj Q Λ θ Λc ν₀ L') :=
  (moduleExactFunctor_plusTensorFunctor j hj Q Λ θ Λc ν₀ L').preservesFiniteLimits

instance : Limits.PreservesFiniteColimits (plusTensorFunctor j hj Q Λ θ Λc ν₀ L') :=
  (moduleExactFunctor_plusTensorFunctor j hj Q Λ θ Λc ν₀ L').preservesFiniteColimits

/-! ### Lemma 7.19 (K) as a natural isomorphism of functors on modules -/

section Module

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (w₁ + w₂) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- The component of `kModuleIso` at `Z`: `kPaperModuleEquiv`. -/
def kModuleIsoApp (Z : ModuleCat (kPaperAlg j hj Q Λ θ)) :
    (kPaperSFunctor j hj Q Λ θ hQ ⋙ coeTensorFunctor j hj Q Λ Λc (w₁ + w₂) ν₀ Lc ⋙
        ModuleCat.restrictScalars (cast_w).toAlgHom.toRingHom).obj Z ≅
      (plusTensorFunctor j hj Q Λ θ Λc ν₀ L' ⋙
        plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).obj Z :=
  (kPaperModuleEquiv j hj Q Λ θ hQ Z Λc ν₀ L' hR hP hPL hκ).toModuleIso

/-- **Webster, arXiv:1309.3796v3, Lemma 7.19 (K), on modules, naturally in `Z`**:
`K^σ ∘ S ≅ S_+ ∘ (- ⊠ L)` as functors to modules over `T^{λ⁺}(θ_h + (ν₀ + θ_t))`, with the
route hypotheses `hL`, `hR`, `hP`, `hPL`, `hκ` of `kPaperEquiv`. -/
def kModuleIso :
    kPaperSFunctor j hj Q Λ θ hQ ⋙ coeTensorFunctor j hj Q Λ Λc (w₁ + w₂) ν₀ Lc ⋙
        ModuleCat.restrictScalars (cast_w).toAlgHom.toRingHom ≅
      plusTensorFunctor j hj Q Λ θ Λc ν₀ L' ⋙
        plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) :=
  NatIso.ofComponents
    (kModuleIsoApp j hj Q Λ θ hQ Λc ν₀ L' hR hP hPL hκ)
    fun g => ModuleCat.hom_ext (LinearMap.ext fun x => by
      have key := kPaperEquiv_natural j hj Q Λ θ hQ g Λc ν₀ L' hR hP hPL hκ x
      exact key)

end Module

/-! ### Lemma 7.19 (K) on derived categories -/

section Derived

set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ (w₁ + w₂)
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((w₁ + w₂) + ν₀)
set_option hygiene false in
local notation "Splus" =>
  plusStagedStd Q hQ Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)

variable [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Tpᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (kPaperAlg j hj Q Λ θ))]
  [HasDerivedCategory.{w'} (ModuleCat.{0} T)] [HasDerivedCategory.{w'} (ModuleCat.{0} Tᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} Tp)] [HasDerivedCategory.{w'} (ModuleCat.{0} Tpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} Tq)]
  [HasDerivedCategory.{w'} (ModuleCat.{0}
    (plusSingAlg Q Λ Λc j hj ν₀ (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)))]

/-- **Webster, arXiv:1309.3796v3, Lemma 7.19 (K)**: `𝕂 𝕊(Z) ≅ 𝕊_+(Z ⊠ L)`, naturally in `Z` in
the derived category of modules over the singleton blocks of `λ`. Here `𝕂` is the coevaluation
functor `coevaluationFunctor` read on left modules (`leftCoevaluationFunctor`), followed by the
identification of the weights `(θ_h + θ_t) + ν₀ = θ_h + (ν₀ + θ_t)`; `𝕊`, `- ⊠ L` and `𝕊_+` are
the functors induced by the exact functors `kPaperSFunctor`, `plusTensorFunctor` and
`plusStagedStd`.

Route hypotheses (beyond Webster's setting): `hL`, `hP`, `hPL`, `hκ` (those of `kPaperEquiv`),
`hQ` (symmetric `Q`), and `hfin`, `hproj` (the pieces `L e(t)` are finitely generated projective
`k`-modules), which give the projectivity of `K^{λ⁺}_λ` as a left `T^λ`-module. -/
def kDerivedIso
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ Lc)
    (hPL : PullOffLeft k Q Λc ν₀ Lc)
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k Lc (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
    (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
      (BalancedTensor.idemPart k Lc (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)))) :
    (kPaperSFunctor j hj Q Λ θ hQ).mapDerivedCategory ⋙
        leftCoevaluationFunctor.{w, w'} j hj Q Λ Λc (w₁ + w₂) ν₀ Lc ⋙
        (ModuleCat.restrictScalars (cast_w).toAlgHom.toRingHom).mapDerivedCategory ≅
      (plusTensorFunctor j hj Q Λ θ Λc ν₀ L').mapDerivedCategory ⋙ (Splus).mapDerivedCategory :=
  have := projective_reflectedCap (j := j) (hj := hj) (Λ := Λ) (ν := w₁ + w₂) hL hQ hκ hP hPL
    hfin hproj
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (leftCoevaluationIso j hj Q Λ Λc (w₁ + w₂) ν₀ Lc hL hQ hκ hP hPL hfin hproj) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    mapDerivedCategoryIsoOfIso (kModuleIso j hj Q Λ θ hQ Λc ν₀ L' (hL := hL)
      (midKLRRel hκ hP hPL) hP hPL hκ) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end Derived

end Categorification.Stendhal.CupCap
