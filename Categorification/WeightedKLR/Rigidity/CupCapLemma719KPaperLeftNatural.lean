/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaperLeft
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutNatural
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingCutNaturalStep

/-!
# Naturality of the left side of Lemma 7.19 (K)

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19 (K),
for the derived form of the lemma: the identifications `S(Z) ≅ S_cut Y` (`kPaperSEquiv`) and
`K^σ(S(Z)) ≅ K^σ(S_cut Y)` (`kPaperLeftEquiv`) commute with the maps induced by a map
`g : Z → Z'` of modules over the singleton blocks.

## Main definitions

* `Stendhal.CupCap.kPaperSMap`: `S` on maps, linearly over `T^λ(θ_h + θ_t)`.
* `Stendhal.CupCap.kPaperYMap`: the standardizations of the two blocks on maps.
* `Stendhal.CupCap.kPaperLeftMap`: `K^σ(S(-))` on maps.

## Main results

* `Stendhal.CupCap.kPaperSEquiv_natural`: `S(Z) ≅ S_cut Y` is natural in `Z`.
* `Stendhal.CupCap.kPaperLeftEquiv_natural`: `K^σ(S(Z)) ≅ K^σ(S_cut Y)` is natural in `Z`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (θ : Fin (j + (ℓ - j)) → Multiset I) (hQ : KLRSymm Q)

set_option hygiene false in
local notation "Λ'" => cutLabels j hj Λ
set_option hygiene false in
local notation "w₁" => singWeight j (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "w₂" => singWeight (ℓ - j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "Kk" => AlgCat.of k k

/-- Adding the trivial spectator, as a functor. -/
abbrev kPaperZFunctor :
    ModuleCat (kPaperAlg j hj Q Λ θ) ⥤
      ModuleCat (singAlg Q j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j)) ⊗[k]
        (AlgCat.of k (singAlg Q (ℓ - j) (Λ' ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j) ⊗[k] k) :
          AlgCat k)) :=
  ModuleCat.restrictScalars (kPaperRid j hj Q Λ θ).toRingHom

/-- The standardization in stages, as a functor. -/
abbrev kPaperStdFunctor :
    ModuleCat (kPaperAlg j hj Q Λ θ) ⥤
      ModuleCat (TensorProductAlgebra k Q Λ' (singWeight (j + (ℓ - j)) θ) ⊗[k] Kk) :=
  kPaperZFunctor j hj Q Λ θ ⋙ ModuleCat.restrictScalars (singSplit Q j (ℓ - j) Λ' θ Kk).toRingHom ⋙
    singStd Q hQ (j + (ℓ - j)) Λ' θ Kk

variable {Z Z' : ModuleCat (kPaperAlg j hj Q Λ θ)} (g : Z ⟶ Z')

/-- `kPaperZ` on maps. -/
def kPaperZMap : kPaperZ j hj Q Λ θ Z ⟶ kPaperZ j hj Q Λ θ Z' := (kPaperZFunctor j hj Q Λ θ).map g

/-- **The standardization in stages on maps**, linearly over `T^λ(θ_h + θ_t)`. -/
def kPaperSMap :
    KPaperS j hj Q Λ θ hQ Z →ₗ[TensorProductAlgebra k Q Λ (w₁ + w₂)] KPaperS j hj Q Λ θ hQ Z' where
  toFun m := ((kPaperStdFunctor j hj Q Λ θ hQ).map g).hom m
  map_add' := map_add _
  map_smul' t m := ((kPaperStdFunctor j hj Q Λ θ hQ).map g).hom.map_smul (kPaperRho j hj Q Λ θ t) m

/-- **The standardizations of the two blocks on maps.** -/
def kPaperYMap :
    KPaperY j hj Q Λ θ hQ Z →ₗ[cutFactorAlgebra Q Λ' w₁ w₂] KPaperY j hj Q Λ θ hQ Z' :=
  cutSpectInputHom (a := j) (r := ℓ - j) Q Λ' w₁ w₂
    ((singOuter Q hQ j (ℓ - j) Λ' θ Kk).map (kPaperZMap j hj Q Λ θ g)).hom

/-- **`S(Z) ≅ S_cut Y` is natural in `Z`.** -/
theorem kPaperCutAdd_natural (m : KPaperS j hj Q Λ θ hQ Z) :
    kPaperCutAdd j hj Q Λ θ hQ Z' (kPaperSMap j hj Q Λ θ hQ g m) =
      kCutStdMap j hj Q Λ w₁ w₂ hQ (kPaperYMap j hj Q Λ θ hQ g) (kPaperCutAdd j hj Q Λ θ hQ Z m) :=
  singCutEquiv_natural Q hQ j (ℓ - j) Λ' θ Kk (kPaperZMap j hj Q Λ θ g) m

theorem kPaperSEquiv_natural :
    (kPaperSEquiv j hj Q Λ θ hQ Z').toLinearMap ∘ₗ kPaperSMap j hj Q Λ θ hQ g =
      kCutStdMap j hj Q Λ w₁ w₂ hQ (kPaperYMap j hj Q Λ θ hQ g) ∘ₗ
        (kPaperSEquiv j hj Q Λ θ hQ Z).toLinearMap :=
  LinearMap.ext fun m => kPaperCutAdd_natural j hj Q Λ θ hQ g m

variable (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((w₁ + w₂) + ν₀)

/-- **`K^σ(S(-))` on maps.** -/
def kPaperLeftMap :
    KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L' →ₗ[Tp] KPaperLeft j hj Q Λ θ hQ Z' Λc ν₀ L' :=
  coeTensorMap (kPaperSMap j hj Q Λ θ hQ g)

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- **`K^σ(S(Z)) ≅ K^σ(S_cut Y)` is natural in `Z`.** -/
theorem kPaperLeftEquiv_natural (x : KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L') :
    kPaperLeftEquiv j hj Q Λ θ hQ Z' Λc ν₀ L' (kPaperLeftMap j hj Q Λ θ hQ g Λc ν₀ L' x) =
      kCutTargetMap j hj Q Λ Λc w₁ w₂ ν₀ hQ L' (kPaperYMap j hj Q Λ θ hQ g)
        (kPaperLeftEquiv j hj Q Λ θ hQ Z Λc ν₀ L' x) := by
  have h := congrArg (coeTensorMap (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀)
    (L := CapCoef Q Λc ν₀ L')) (kPaperSEquiv_natural j hj Q Λ θ hQ g)
  rw [coeTensorMap_comp, coeTensorMap_comp] at h
  exact LinearMap.congr_fun h x

end Categorification.Stendhal.CupCap
