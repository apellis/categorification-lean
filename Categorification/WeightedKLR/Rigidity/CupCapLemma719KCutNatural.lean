/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPhiPsi

/-!
# Naturality of Lemma 7.19 (K) at the cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19 (K),
for the derived form of the lemma: the comparison `Φ : S_+(Y ⊠ L') → K^σ(S_cut Y)` of the lemma at
the cut commutes with the maps induced by a map `f : Y → Y'` of modules over the two blocks
(`kCutPhi_natural`), and so does its inverse (`kCutPhiEquiv_symm_natural`).

## Main definitions

* `Stendhal.CupCap.kCutStdMap`: `S_cut` on maps, linearly over `T^λ`.
* `Stendhal.CupCap.kCutTargetMap`: `K^σ(S_cut -)` on maps.
* `Stendhal.CupCap.kCutSourceMap`: `S_+(- ⊠ L')` on maps.

## Main results

* `Stendhal.CupCap.kCutPhi_natural`: `Φ` is natural in `Y`.
* `Stendhal.CupCap.kCutPhiEquiv_symm_natural`: the isomorphism of the lemma at the cut is
  natural in `Y`.
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
  {Y : Type} [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  {Y' : Type} [AddCommGroup Y'] [Module k Y']
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y']
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y'] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']
  (f : Y →ₗ[cutFactorAlgebra Q (cutLabels j hj Λ) θ γ] Y')

set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "PF" => PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev pfNonAssocSemiringN : NonAssocSemiring PF := Semiring.toNonAssocSemiring

attribute [local instance high] pfNonAssocSemiringN

/-- **The partial standardization at the cut on maps**, linearly over `T^λ(θ + γ)`. -/
def kCutStdMap :
    KCutStd j hj Q Λ θ γ Y hQ →ₗ[TensorProductAlgebra k Q Λ (θ + γ)]
      KCutStd j hj Q Λ θ γ Y' hQ where
  toFun := cutStandardMap Q (cutLabels j hj Λ) θ γ f
  map_add' := map_add _
  map_smul' _ z := cutStandardMap_action Q (cutLabels j hj Λ) θ γ hQ f _ z

theorem kCutStdMap_unit (y : Y) :
    kCutStdMap j hj Q Λ θ γ hQ f (kCutUnit j hj Q Λ θ γ Y hQ y) =
      kCutUnit j hj Q Λ θ γ Y' hQ (f y) := rfl

/-- **`K^σ(S_cut -)` on maps.** -/
def kCutTargetMap :
    KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L' →ₗ[Tp] KCutTarget j hj Q Λ Λc θ γ ν₀ Y' hQ L' :=
  coeTensorMap (kCutStdMap j hj Q Λ θ γ hQ f)

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kCutTargetMap_rep (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
    (x : KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f (kCutRep j hj Q Λ Λc θ γ ν₀ Y hQ L' t x) =
      kCutRep j hj Q Λ Λc θ γ ν₀ Y' hQ L' t (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f x) :=
  (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f).map_smul _ x

/-- **`S_+(- ⊠ L')` on maps.** -/
def kCutSourceMap :
    KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L' →ₗ[k] KCutSource j hj Q Λ Λc θ γ ν₀ Y' hQ L' :=
  plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ
    (midSpectMap (B := TensorProductAlgebra k Q Λc ν₀) (L := L') f)

/-- `K^σ(S_cut f) ∘ Φ`, as a `k`-linear map. -/
def kCutTargetMapPhi :
    KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L' →ₗ[k] KCutTarget j hj Q Λ Λc θ γ ν₀ Y' hQ L' where
  toFun u := kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' u)
  map_add' u u' := by rw [map_add, map_add]
  map_smul' c u := by
    rw [map_smul]
    exact (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f).map_smul (algebraMap k Tp c) _

theorem kCutSourceMap_unit (y : Y) (v : L') :
    kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' f (plusStandardUnit hQ (midSpectTmul (k := k) y v)) =
      plusStandardUnit hQ (midSpectTmul (k := k) (f y) v) := rfl

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kCutTargetMap_tmul (r : ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L'))
    (y : Y) :
    kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f
        (BalancedTensor.tmul r (kCutUnit j hj Q Λ θ γ Y hQ y)) =
      BalancedTensor.tmul r (kCutUnit j hj Q Λ θ γ Y' hQ (f y)) := rfl

theorem kCutPhi_natural_unit (y : Y) (v : L') :
    kCutPhi j hj Q Λ Λc θ γ ν₀ Y' hQ L' (kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' f
        (plusStandardUnit hQ (midSpectTmul (k := k) y v))) =
      kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f
        (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' (plusStandardUnit hQ (midSpectTmul (k := k) y v))) :=
  (congrArg (kCutPhi j hj Q Λ Λc θ γ ν₀ Y' hQ L')
    (kCutSourceMap_unit j hj Q Λ Λc θ γ ν₀ hQ L' f y v)).trans
    ((kCutPhi_unit j hj Q Λ Λc θ γ ν₀ Y' hQ L' (f y) v).trans
      ((kCutTargetMap_tmul j hj Q Λ Λc θ γ ν₀ hQ L' f _ y).symm.trans
        (congrArg (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f)
          (kCutPhi_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' y v).symm)))

/-- **`Φ` is natural in `Y`**: `Φ_{Y'} ∘ S_+(f ⊠ L') = K^σ(S_cut f) ∘ Φ_Y`. -/
theorem kCutPhi_natural (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kCutPhi j hj Q Λ Λc θ γ ν₀ Y' hQ L' (kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' f u) =
      kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' u) := by
  have h : (kCutPhi j hj Q Λ Λc θ γ ν₀ Y' hQ L').comp
      (kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' f) =
      kCutTargetMapPhi j hj Q Λ Λc θ γ ν₀ hQ L' f := by
    refine plusStandardLift_unique hQ (ρ := kCutRep j hj Q Λ Λc θ γ ν₀ Y' hQ L')
      (fun t v => ?_) (fun t v => ?_) (fun n => ?_)
    · change kCutPhi j hj Q Λ Λc θ γ ν₀ Y' hQ L' (plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ _
        (plusStandardAction Q Λ Λc j hj θ ν₀ γ _ hQ t v)) = _
      rw [plusStandardMap_action]
      exact kCutPhi_action j hj Q Λ Λc θ γ ν₀ Y' hQ L' t _
    · change kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L'
        (plusStandardAction Q Λ Λc j hj θ ν₀ γ _ hQ t v)) = _
      rw [kCutPhi_action]
      exact kCutTargetMap_rep j hj Q Λ Λc θ γ ν₀ hQ L' f t _
    · have hu : ((kCutPhi j hj Q Λ Λc θ γ ν₀ Y' hQ L').comp
          (kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' f)).comp
            (plusStandardUnit (N := MidSpect (k := k) Y L') hQ) =
          (kCutTargetMapPhi j hj Q Λ Λc θ γ ν₀ hQ L' f).comp
            (plusStandardUnit (N := MidSpect (k := k) Y L') hQ) :=
        TensorProduct.ext' (R := k) fun y v => kCutPhi_natural_unit j hj Q Λ Λc θ γ ν₀ hQ L' f y v
      exact LinearMap.congr_fun hu n
  exact LinearMap.congr_fun h u

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : CapCoef Q Λc ν₀ L'), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L') hL)
  (hP : PullOff k Q Λc ν₀ (CapCoef Q Λc ν₀ L')) (hPL : PullOffLeft k Q Λc ν₀ (CapCoef Q Λc ν₀ L'))
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **The isomorphism of Lemma 7.19 (K) at the cut is natural in `Y`**, in the direction
`K^σ(S_cut Y) → S_+(Y ⊠ L')` used by the lemma. -/
theorem kCutPhiEquiv_symm_natural (z : KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    (kCutPhiEquiv Y' hQ hR hP hPL hκ).symm (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f z) =
      kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' f ((kCutPhiEquiv Y hQ hR hP hPL hκ).symm z) := by
  refine (kCutPhiEquiv Y' hQ hR hP hPL hκ).injective ?_
  exact ((kCutPhiEquiv Y' hQ hR hP hPL hκ).apply_symm_apply _).trans
    ((congrArg (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' f)
      ((kCutPhiEquiv Y hQ hR hP hPL hκ).apply_symm_apply z)).symm.trans
      (kCutPhi_natural j hj Q Λ Λc θ γ ν₀ hQ L' f _).symm)

end Categorification.Stendhal.CupCap
