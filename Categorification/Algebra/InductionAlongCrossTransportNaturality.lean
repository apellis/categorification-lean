/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportNaturality

/-!
# Naturality of the transported cross commutation

The transported isomorphism `Res_{ψ₁} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) ψ₂`
(`resIndCrossEquivTransport`) is natural in the module whenever the isomorphism it transports
is (`resIndCrossEquivTransport_map`). This carries the naturality of Webster's relation
`Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`, arXiv:1309.3796v3, Theorem 4.31) from the all-down matrix ring to the
tensor product algebra, as used in the proof of Proposition 5.5 there.
-/

noncomputable section

namespace Categorification.InductionAlong

universe u w

variable {A₀ A A₂ B A₀' A' A₂' B' : Type u} [Ring A₀] [Ring A] [Ring A₂] [Ring B] [Ring A₀']
  [Ring A'] [Ring A₂'] [Ring B']
  {φ₂ : A₀ →ₙ+* A} {φ₁ : A →ₙ+* B} {ψ₂ : A₀ →ₙ+* A₂} {ψ₁ : A₂ →ₙ+* B}
  {φ₂' : A₀' →ₙ+* A'} {φ₁' : A' →ₙ+* B'} {ψ₂' : A₀' →ₙ+* A₂'} {ψ₁' : A₂' →ₙ+* B'}
  (a₀ : A₀ ≃+* A₀') (a : A ≃+* A') (a₂ : A₂ ≃+* A₂') (b : B ≃+* B')
  (hφ₂ : ∀ t, φ₂' (a₀ t) = a (φ₂ t)) (hφ₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  (hψ₂ : ∀ t, ψ₂' (a₀ t) = a₂ (ψ₂ t)) (hψ₁ : ∀ t, ψ₁' (a₂ t) = b (ψ₁ t))
  {M M' M₂ M₂' : Type w} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₂'] [Module A' M₂']
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m)
  (e₂ : M₂ ≃+ M₂') (he₂ : ∀ (t : A) m, e₂ (t • m) = a t • e₂ m)
  (g : M →ₗ[A] M₂) (g' : M' →ₗ[A'] M₂') (hg : ∀ m, e₂ (g m) = g' (e m))

include hg

theorem resIndCrossTransport_map (x : Res ψ₁ (Ind M φ₁)) :
    resIndCrossTransport a a₂ b hφ₁ hψ₁ e₂ he₂ (Res.map (Ind.map g) x) =
      Res.map (Ind.map g') (resIndCrossTransport a a₂ b hφ₁ hψ₁ e he x) :=
  Res.transport_map a₂ b hψ₁ _ _ _ _ _ _
    (fun y => Ind.transport_map a b hφ₁ e he e₂ he₂ g g' hg y) x

theorem indResCrossTransport_map (x : Ind (Res φ₂ M) ψ₂) :
    indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e₂ he₂ (Ind.map (Res.map g) x) =
      Ind.map (Res.map g') (indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e he x) :=
  Ind.transport_map a₀ a₂ hψ₂ _ _ _ _ _ _
    (fun y => Res.transport_map a₀ a hφ₂ e he e₂ he₂ g g' hg y) x

/-- **Naturality of `resIndCrossEquivTransport`**: if the transported isomorphisms `L`, `L₂`
carry `Res (Ind g')` to `Ind (Res g')`, the transports carry `Res (Ind g)` to `Ind (Res g)`. -/
theorem resIndCrossEquivTransport_map
    (L : Res ψ₁' (Ind M' φ₁') ≃ₗ[A₂'] Ind (Res φ₂' M') ψ₂')
    (L₂ : Res ψ₁' (Ind M₂' φ₁') ≃ₗ[A₂'] Ind (Res φ₂' M₂') ψ₂')
    (hL : ∀ y, L₂ (Res.map (Ind.map g') y) = Ind.map (Res.map g') (L y))
    (x : Res ψ₁ (Ind M φ₁)) :
    resIndCrossEquivTransport a₀ a a₂ b hφ₂ hφ₁ hψ₂ hψ₁ e₂ he₂ L₂ (Res.map (Ind.map g) x) =
      Ind.map (Res.map g) (resIndCrossEquivTransport a₀ a a₂ b hφ₂ hφ₁ hψ₂ hψ₁ e he L x) := by
  apply (indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e₂ he₂).injective
  change (indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e₂ he₂)
      ((indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e₂ he₂).symm
        (L₂ (resIndCrossTransport a a₂ b hφ₁ hψ₁ e₂ he₂ (Res.map (Ind.map g) x)))) =
    (indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e₂ he₂) (Ind.map (Res.map g)
      ((indResCrossTransport a₀ a a₂ hφ₂ hψ₂ e he).symm
        (L (resIndCrossTransport a a₂ b hφ₁ hψ₁ e he x))))
  rw [AddEquiv.apply_symm_apply, resIndCrossTransport_map a a₂ b hφ₁ hψ₁ e he e₂ he₂ g g' hg,
    hL, indResCrossTransport_map a₀ a a₂ hφ₂ hψ₂ e he e₂ he₂ g g' hg, AddEquiv.apply_symm_apply]

end Categorification.InductionAlong
