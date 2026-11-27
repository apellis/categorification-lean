/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndNatural
import Categorification.WeightedKLR.RedStrands.EiStandardChain
import Categorification.Algebra.InductionAlongEndAlg

/-!
# The last-strand sequence of `Fᵢ S N` with a commuting action

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For a module `N` over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` with an action `τ` of
an algebra `C`, the sequence `S(₁Fᵢ N) → Fᵢ(S N) → S(₂Fᵢ N) → 0` is an exact sequence of
modules over `T(i + (θ + β)) ⊗ C` (`fiSeqOne`, `fiSeqTwo`, `fiSeq_exact`,
`fiSeqTwo_surjective`), and the first map is injective whenever `δ₁` is
(`fiSeqOne_injective`, under the route hypothesis `FirstIndDeltaInjective`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (θ β : Multiset I) (C : Type) [Ring C] [Algebra k C]
  {N : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (τ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ β) N)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + β))

instance firstIndStandardT_isScalarTower :
    IsScalarTower k T′ (FirstIndStandardT Q Λ i θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul ((parabolicStandardAction Q Λ ((Si i) + θ) β
    (FirstIndLeft Q Λ i θ β N) hQ).comp
      (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)).toAlgHom) c t) y⟩

instance firstIndStandardT_smulCommClass :
    SMulCommClass T′ k (FirstIndStandardT Q Λ i θ β N hQ) :=
  ⟨fun t c y => map_smul ((parabolicStandardAction Q Λ ((Si i) + θ) β
    (FirstIndLeft Q Λ i θ β N) hQ)
      (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β) t)) c y⟩

instance lastIndStandardT_isScalarTower :
    IsScalarTower k T′ (LastIndStandardT Q Λ i θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul ((parabolicStandardAction Q Λ θ ((Si i) + β)
    (LastIndRight Q Λ i θ β N) hQ).comp
      (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).toAlgHom) c t) y⟩

instance lastIndStandardT_smulCommClass :
    SMulCommClass T′ k (LastIndStandardT Q Λ i θ β N hQ) :=
  ⟨fun t c y => map_smul ((parabolicStandardAction Q Λ θ ((Si i) + β)
    (LastIndRight Q Λ i θ β N) hQ)
      (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β) t)) c y⟩

theorem appendBlackHom_smul (c : k) (t : TensorProductAlgebra k Q Λ (θ + β)) :
    appendBlackHom Q Λ i θ β (c • t) = c • appendBlackHom Q Λ i θ β t :=
  map_smul (appendBlack Q Λ i (θ + β)) c t

theorem leftAppendHom_smul (c : k) (t : parabolicFactorAlgebra Q Λ θ β) :
    leftAppendHom Q Λ i θ β (c • t) = c • leftAppendHom Q Λ i θ β t :=
  map_smul (parabolicAppendLeft Q Λ i θ β) c t

theorem parabolicRightHom_smul (c : k) (t : parabolicFactorAlgebra Q Λ θ β) :
    parabolicRightHom Q Λ i θ β (c • t) = c • parabolicRightHom Q Λ i θ β t :=
  map_smul (parabolicAppendRight Q Λ i β θ) c t

/-- The action of `C` on `Fᵢ(S N)`. -/
abbrev fiMidAction : C →ₐ[k] Module.End T′ (FirstIndF Q Λ i θ β N hQ) :=
  (IndK.endAlg (appendBlackHom Q Λ i θ β) (ParabolicStandardT Q Λ θ β N hQ)
    (appendBlackHom_smul Q Λ i θ β)).comp (standardActionT Q Λ hQ C τ)

/-- The action of `C` on `₁Fᵢ N`. -/
abbrev fiLeftAction :
    C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ ((Si i) + θ) β) (FirstIndLeft Q Λ i θ β N) :=
  (IndK.endAlg (leftAppendHom Q Λ i θ β) N (leftAppendHom_smul Q Λ i θ β)).comp τ

/-- The action of `C` on `₂Fᵢ N`. -/
abbrev fiRightAction :
    C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ ((Si i) + β)) (LastIndRight Q Λ i θ β N) :=
  (IndK.endAlg (parabolicRightHom Q Λ i θ β) N (parabolicRightHom_smul Q Λ i θ β)).comp τ

/-- The action of `C` on `S(₁Fᵢ N)` over `T(i + (θ + β))`. -/
def fiSubAction : C →ₐ[k] Module.End T′ (FirstIndStandardT Q Λ i θ β N hQ) where
  toFun c := firstIndStandardMap Q Λ i θ β hQ (τ c)
  map_one' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_one (standardActionT Q Λ hQ C (fiLeftAction Q Λ i θ β C τ))) x
  map_mul' c c' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_mul (standardActionT Q Λ hQ C (fiLeftAction Q Λ i θ β C τ)) c c') x
  map_zero' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_zero (standardActionT Q Λ hQ C (fiLeftAction Q Λ i θ β C τ))) x
  map_add' c c' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_add (standardActionT Q Λ hQ C (fiLeftAction Q Λ i θ β C τ)) c c') x
  commutes' c := LinearMap.ext fun x =>
    LinearMap.congr_fun ((standardActionT Q Λ hQ C (fiLeftAction Q Λ i θ β C τ)).commutes c) x

/-- The action of `C` on `S(₂Fᵢ N)` over `T(i + (θ + β))`. -/
def fiQuotAction : C →ₐ[k] Module.End T′ (LastIndStandardT Q Λ i θ β N hQ) where
  toFun c := lastIndStandardMap Q Λ i θ β hQ (τ c)
  map_one' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_one (standardActionT Q Λ hQ C (fiRightAction Q Λ i θ β C τ))) x
  map_mul' c c' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_mul (standardActionT Q Λ hQ C (fiRightAction Q Λ i θ β C τ)) c c') x
  map_zero' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_zero (standardActionT Q Λ hQ C (fiRightAction Q Λ i θ β C τ))) x
  map_add' c c' := LinearMap.ext fun x =>
    LinearMap.congr_fun (map_add (standardActionT Q Λ hQ C (fiRightAction Q Λ i θ β C τ)) c c') x
  commutes' c := LinearMap.ext fun x =>
    LinearMap.congr_fun ((standardActionT Q Λ hQ C (fiRightAction Q Λ i θ β C τ)).commutes c) x

/-- `Fᵢ(S N)` over `T(i + (θ + β)) ⊗ C`. -/
abbrev FiMid : Type := TensorAct k T′ C (fiMidAction Q Λ hQ i θ β C τ)

/-- `S(₁Fᵢ N)` over `T(i + (θ + β)) ⊗ C`. -/
abbrev FiSub : Type := TensorAct k T′ C (fiSubAction Q Λ hQ i θ β C τ)

/-- `S(₂Fᵢ N)` over `T(i + (θ + β)) ⊗ C`. -/
abbrev FiQuot : Type := TensorAct k T′ C (fiQuotAction Q Λ hQ i θ β C τ)

/-- **The map `S(₁Fᵢ N) → Fᵢ(S N)` over `T(i + (θ + β)) ⊗ C`.** -/
def fiSeqOne : FiSub Q Λ hQ i θ β C τ →ₗ[T′ ⊗[k] C] FiMid Q Λ hQ i θ β C τ :=
  TensorAct.map (firstIndDeltaT Q Λ i θ β N hQ)
    (fun c x => firstIndDeltaT_natural Q Λ i θ β hQ (τ c) x)

/-- **The map `Fᵢ(S N) → S(₂Fᵢ N)` over `T(i + (θ + β)) ⊗ C`.** -/
def fiSeqTwo : FiMid Q Λ hQ i θ β C τ →ₗ[T′ ⊗[k] C] FiQuot Q Λ hQ i θ β C τ :=
  TensorAct.map (lastIndQuotientMap Q Λ i θ β N hQ)
    (fun c x => lastIndQuotientMap_natural Q Λ i θ β hQ (τ c) x)

theorem fiSeqOne_injective (hinj : FirstIndDeltaInjective Q Λ i θ β N hQ) :
    Function.Injective (fiSeqOne Q Λ hQ i θ β C τ) :=
  TensorAct.map_injective _ hinj

theorem fiSeq_exact : Function.Exact (fiSeqOne Q Λ hQ i θ β C τ) (fiSeqTwo Q Λ hQ i θ β C τ) :=
  TensorAct.map_exact _ _ (firstIndDeltaT_exact Q Λ i θ β N hQ)

theorem fiSeqTwo_surjective : Function.Surjective (fiSeqTwo Q Λ hQ i θ β C τ) :=
  TensorAct.map_surjective _ (lastIndQuotientMap_surjective Q Λ i θ β N hQ)

end StendhalAlgebra

end Categorification.Stendhal
