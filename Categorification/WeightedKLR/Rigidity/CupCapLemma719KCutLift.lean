/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutIdem

/-!
# The comparison map of Lemma 7.19 (K) at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the map `y ⊠ v ↦ cap(|h|, v) ⊗ (1 ⊗ y)`
on the input intertwines the three blocks of `λ⁺` with their action on the target through all
strands (`kCutInputMap_isInd3InputHom`), so it induces a `T^{λ⁺}`-linear map
`Φ : S_+(Y ⊠ L') → K^σ(S_cut Y)` out of the partial standardization of `λ⁺` (`kCutPhi`).

## Main definitions

* `Stendhal.CupCap.kCutPhi`: the map `KCutSource → KCutTarget`.

## Main results

* `Stendhal.CupCap.kCutInputMap_isInd3InputHom`: the intertwining condition.
* `Stendhal.CupCap.kCutPhi_action`: `Φ` is linear over `T^{λ⁺}`.
* `Stendhal.CupCap.kCutPhi_unit`: `Φ` extends the map on the input.
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
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

/-- **The map on the input intertwines the three blocks of `λ⁺`** with their action on the
target through all strands. -/
theorem kCutInputMap_isInd3InputHom :
    IsInd3InputHom (kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L')
      (kCutInputMap j hj Q Λ Λc θ γ ν₀ Y hQ L') := by
  have hE := kCut_e j hj Q Λ Λc θ γ ν₀ Y hQ L'
  have h1 := isInd3At_one_of_e _ _ hE
  have hB : Function.Surjective (plusMidEmb j hj Q Λ Λc ν₀) := fun b => by
    obtain ⟨b, rfl⟩ := (relabelEquiv (stendhalRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.natAdd j)
      (Fin.natAdd_injective _ _) _)).surjective b
    obtain ⟨b, rfl⟩ := (plusMidEmb₀ j hj Q Λ Λc ν₀).surjective b
    exact ⟨b, rfl⟩
  have hC : Function.Surjective (plusTailEmb j hj Q Λ Λc γ) := fun c => by
    obtain ⟨c, rfl⟩ := (relabelEquiv (stendhalRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.natAdd j)
      (Fin.natAdd_injective _ _) _)).surjective c
    obtain ⟨c, rfl⟩ := (plusTailEmb₀ j hj Q Λ Λc γ).surjective c
    exact ⟨c, rfl⟩
  exact isInd3InputHom_of_gens _ _ (AlgEquiv.surjective _) hB hC hE
    (kCut_head_x j hj Q Λ Λc θ γ ν₀ Y hQ L' h1) (kCut_head_ψ j hj Q Λ Λc θ γ ν₀ Y hQ L' h1)
    (kCut_mid_x j hj Q Λ Λc θ γ ν₀ Y hQ L' h1) (kCut_mid_ψ j hj Q Λ Λc θ γ ν₀ Y hQ L' h1)
    (kCut_tail_x j hj Q Λ Λc θ γ ν₀ Y hQ L' h1) (kCut_tail_ψ j hj Q Λ Λc θ γ ν₀ Y hQ L' h1)

/-- **The comparison map `Φ : S_+(Y ⊠ L') → K^σ(S_cut Y)`** of Lemma 7.19 (K) at the cut. -/
def kCutPhi :
    KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L' →ₗ[k] KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L' :=
  plusStandardLift hQ (kCutInputMap j hj Q Λ Λc θ γ ν₀ Y hQ L')
    (kCutInputMap_isInd3InputHom j hj Q Λ Λc θ γ ν₀ Y hQ L')

/-- **`Φ` is linear over `T^{λ⁺}`.** -/
theorem kCutPhi_action (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
    (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L'
        (plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ t u) =
      kCutRep j hj Q Λ Λc θ γ ν₀ Y hQ L' t (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' u) :=
  plusStandardLift_action hQ _ _ t u

/-- **`Φ` extends the map on the input.** -/
theorem kCutPhi_unit (y : Y) (v : L') :
    kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' (plusStandardUnit hQ (midSpectTmul (k := k) y v)) =
      BalancedTensor.tmul
        (capSum j hj Q Λ Λc (θ + γ) ν₀ (cutPos j hj θ γ)
          (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v))
        (kCutUnit j hj Q Λ θ γ Y hQ y) :=
  plusStandardLift_unit hQ _ _ _

end Categorification.Stendhal.CupCap
