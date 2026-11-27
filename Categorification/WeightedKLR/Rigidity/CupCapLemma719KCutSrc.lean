/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutLift
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiSetup

/-!
# The right side of Lemma 7.19 (K) at the cut as a `T^{λ⁺}((θ + γ) + ν₀)`-module

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the inverse `Ψ` of the comparison map is
linear over `T^{λ⁺}`, with the black weight `(θ + γ) + ν₀` of the reflected coevaluation. This
file puts that module structure on the partial standardization of `λ⁺` (`KCutSrc`), through
`plusStandardAction` and the equality of weights `θ + (ν₀ + γ) = (θ + γ) + ν₀`, and records the
`T^λ`-action on the maps out of the reflected cap into it (`kCutHomRep`).

## Main definitions

* `Stendhal.CupCap.KCutSrc`: the right side, a `T^{λ⁺}((θ + γ) + ν₀)`-module.
* `Stendhal.CupCap.kCutHomRep`: `T^λ(θ + γ)` acting on `Hom_{T^{λ⁺}}(K^σ, KCutSrc)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite

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
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)

/-- The action of `T^{λ⁺}((θ + γ) + ν₀)` on the right side of Lemma 7.19 (K) at the cut. -/
def kCutSrcAction : Tp →ₐ[k] Module.End k (KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  (plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ).comp
    (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm.toAlgHom

/-- **The right side of Lemma 7.19 (K) at the cut**, as a `T^{λ⁺}((θ + γ) + ν₀)`-module. -/
def KCutSrc : Type := KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L'

instance : AddCommGroup (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  inferInstanceAs (AddCommGroup (KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L'))

instance : Module k (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  inferInstanceAs (Module k (KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L'))

instance : Module Tp (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  Module.compHom (KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L')
    (kCutSrcAction j hj Q Λ Λc θ γ ν₀ Y hQ L').toRingHom

variable {j hj Q Λ Λc θ γ ν₀ Y hQ L'} in
/-- The identity of the underlying group, into the right side as a `T^{λ⁺}`-module. -/
def toKCutSrc (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') : KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L' := u

theorem smul_toKCutSrc (t : Tp) (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    t • toKCutSrc u = toKCutSrc (kCutSrcAction j hj Q Λ Λc θ γ ν₀ Y hQ L' t u) := rfl

theorem algebraMap_smul_kCutSrc (c : k) (u : KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    algebraMap k Tp c • u = c • u := by
  change kCutSrcAction j hj Q Λ Λc θ γ ν₀ Y hQ L' (algebraMap k Tp c) u = c • u
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

instance : IsScalarTower k Tp (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  IsScalarTower.of_algebraMap_smul (algebraMap_smul_kCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L')

instance : SMulCommClass Tp k (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') where
  smul_comm t c u := (kCutSrcAction j hj Q Λ Λc θ γ ν₀ Y hQ L' t).map_smul c u

instance : SMulCommClass k Tp (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  SMulCommClass.symm _ _ _

set_option hygiene false in
local notation "Kσ" => ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L')

/-- **`T^λ(θ + γ)` acting on the maps `K^σ → KCutSrc`** by precomposition with its right action
on `K^σ`. -/
def kCutHomRep : TensorProductAlgebra k Q Λ (θ + γ) →ₐ[k]
    Module.End k (Kσ →ₗ[Tp] KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  BalancedTensor.precompRep Tp Kσ (KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L')
    (fun c z => reflectedCap_op_algebraMap_smul c z)

end Categorification.Stendhal.CupCap
