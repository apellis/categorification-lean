/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardizationNatural
import Categorification.Algebra.AlgebraFamilyCast
import Categorification.WeightedKLR.RedStrands.GradedTwoPieceStandard

/-!
# Modules over the factor algebras along equal weights

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For `θ = θ'` and `β = β'` the factor algebras `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` are
isomorphic (`castFactor`), and a module over the first is one over the second (`FactorCast`).
Standardization commutes with this transport (`parabolicStandardCast`), compatibly with
endomorphisms (`parabolicStandardCast_endHom`). In the proof of Proposition 5.5 the weights
`θ, β` of the first `ℓ` red strands and of the last block of a module agree with `i + θ₀`,
`i + β₀` only up to equality.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra StendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)
  {θ θ' β β' : Multiset I}

local notation "Cyc" β => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β

/-- The factor algebras at equal weights. -/
def castFactor (hθ : θ = θ') (hβ : β = β') :
    parabolicFactorAlgebra Q Λ θ β ≃ₐ[k] parabolicFactorAlgebra Q Λ θ' β' := by
  subst hθ hβ
  exact AlgEquiv.refl

theorem castFactor_tmul (hθ : θ = θ') (hβ : β = β')
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ) (c : Cyc β) :
    castFactor Q Λ hθ hβ (t ⊗ₜ c) =
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ t ⊗ₜ
        CyclotomicAction.castCyc Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
          hβ c := by
  subst hθ hβ
  rfl

theorem castFactor_symm_tmul (hθ : θ = θ') (hβ : β = β')
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ') (c : Cyc β') :
    (castFactor Q Λ hθ hβ).symm (t ⊗ₜ c) =
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hθ.symm t ⊗ₜ
        CyclotomicAction.castCyc Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
          hβ.symm c := by
  subst hθ hβ
  rfl

/-- A module over `D(θ, β)` regarded as a module over `D(θ', β')`. -/
@[nolint unusedArguments]
def FactorCast (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (_hθ : θ = θ') (_hβ : β = β') (N : Type*) : Type _ := N

variable (hθ : θ = θ') (hβ : β = β') (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

instance : AddCommGroup (FactorCast Q Λ hθ hβ N) := inferInstanceAs (AddCommGroup N)
instance : Module k (FactorCast Q Λ hθ hβ N) := inferInstanceAs (Module k N)
instance : Module (parabolicFactorAlgebra Q Λ θ' β') (FactorCast Q Λ hθ hβ N) :=
  Module.compHom N (castFactor Q Λ hθ hβ).symm.toRingEquiv.toRingHom
instance : IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') (FactorCast Q Λ hθ hβ N) where
  smul_assoc c a n := by
    subst hθ hβ
    exact smul_assoc c a (show N from n)

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem factorCast_smul (d : parabolicFactorAlgebra Q Λ θ' β') (n : N) :
    d • (show FactorCast Q Λ hθ hβ N from n) =
      (show FactorCast Q Λ hθ hβ N from (castFactor Q Λ hθ hβ).symm d • n) := rfl

variable {N} {N' : Type} [AddCommGroup N'] [Module k N']
  [Module (parabolicFactorAlgebra Q Λ θ β) N'] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

/-- A map of `D(θ, β)`-modules as a map of `D(θ', β')`-modules. -/
def factorCastMap (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') :
    FactorCast Q Λ hθ hβ N →ₗ[parabolicFactorAlgebra Q Λ θ' β'] FactorCast Q Λ hθ hβ N' where
  toFun n := (g (show N from n) : N')
  map_add' n n' := g.map_add (show N from n) (show N from n')
  map_smul' d n := g.map_smul ((castFactor Q Λ hθ hβ).symm d) (show N from n)

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] [Module k N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'] in
theorem factorCastMap_apply (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') (n : N) :
    factorCastMap Q Λ hθ hβ g (show FactorCast Q Λ hθ hβ N from n) =
      (show FactorCast Q Λ hθ hβ N' from g n) := rfl

variable (N) in
/-- Endomorphisms of a `D(θ, β)`-module as endomorphisms of the transported module. -/
def factorCastEnd : Module.End (parabolicFactorAlgebra Q Λ θ β) N →ₐ[k]
    Module.End (parabolicFactorAlgebra Q Λ θ' β') (FactorCast Q Λ hθ hβ N) where
  toFun := factorCastMap Q Λ hθ hβ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    refine LinearMap.ext fun n => ?_
    change (algebraMap k (Module.End (parabolicFactorAlgebra Q Λ θ β) N) c (show N from n) : N) =
      algebraMap k (Module.End (parabolicFactorAlgebra Q Λ θ' β') (FactorCast Q Λ hθ hβ N)) c n
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]

variable (N) in
/-- At `rfl`, the transported module is the module itself. -/
def factorCastRfl :
    N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] FactorCast Q Λ (rfl : θ = θ) (rfl : β = β) N where
  toFun n := n
  invFun n := n
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hQ : KLRSymm Q)

/-- The scalar tower `k → T(θ + β) → S N`. -/
instance parabolicStandardT_isScalarTower_factorCast {θ β : Multiset I} (N : Type*)
    [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] :
    IsScalarTower k (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ β N hQ) c t) y⟩

local notation "Tfam" => TensorProductAlgebra k Q Λ

variable (N) in
/-- **Standardization commutes with the transport along equal weights.** -/
def parabolicStandardCast :
    ParabolicStandardT Q Λ θ' β' (FactorCast Q Λ hθ hβ N) hQ ≃ₗ[Tfam (θ' + β')]
      FamilyCast Tfam (congrArg₂ (· + ·) hθ hβ) (ParabolicStandardT Q Λ θ β N hQ) := by
  subst hθ hβ
  exact (parabolicStandardEquiv Λ hQ (factorCastRfl Q Λ N).symm).trans
    (FamilyCast.rflEquiv Tfam _)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'] in
/-- **Naturality of `parabolicStandardCast`.** -/
theorem parabolicStandardCast_map [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']
    (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N')
    (z : ParabolicStandard Q Λ θ' β' (FactorCast Q Λ hθ hβ N)) :
    (parabolicStandardCast Q Λ hθ hβ N' hQ
        (parabolicStandardMap Q Λ θ' β' (factorCastMap Q Λ hθ hβ g) z) :
      ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g (parabolicStandardCast Q Λ hθ hβ N hQ z) := by
  subst hθ hβ
  have key : (parabolicStandardMap Q Λ θ β (factorCastRfl Q Λ N').symm.toLinearMap).comp
      (parabolicStandardMap Q Λ θ β (factorCastMap Q Λ rfl rfl g)) =
      (parabolicStandardMap Q Λ θ β g).comp
        (parabolicStandardMap Q Λ θ β (factorCastRfl Q Λ N).symm.toLinearMap) := by
    rw [← parabolicStandardMap_comp, ← parabolicStandardMap_comp]
    rfl
  exact LinearMap.congr_fun key z

end Categorification.Stendhal
