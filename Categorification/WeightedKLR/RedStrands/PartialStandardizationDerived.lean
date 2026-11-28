/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusStaged

/-!
# Standardization functors on derived categories

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Proposition 5.7 and Lemma 7.19: the standardization functors are exact, so they induce
functors on (unbounded) derived categories, applied degreewise to complexes. This file
supplies what Mathlib's `Functor.mapDerivedCategory` needs: the standardization in stages
`singStd`, its form with singleton blocks `singStandard`, the outer standardizations
`plusOuterStd` and the partial standardization `S_+ = plusStagedStd` of `λ⁺` are additive and
preserve finite limits and colimits.

## Main results

* `Stendhal.ModuleExactFunctor.preservesHomology`: an additive functor of module categories
  that preserves exact pairs preserves homology.
* `Additive`, `PreservesFiniteLimits` and `PreservesFiniteColimits` instances for
  `cutSpectFunctor`, `singStd`, `singStandard`, `plusStandardFunctor`, `plusOuterStd` and
  `plusStagedStd`.
-/

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- **An additive exact functor of module categories preserves homology.** -/
theorem ModuleExactFunctor.preservesHomology {R S : Type u} [Ring R] [Ring S]
    {F : ModuleCat.{u} R ⥤ ModuleCat.{u} S} [F.Additive] (hF : ModuleExactFunctor F) :
    F.PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS => by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact hF.exact S.f S.g hS

/-- An additive exact functor of module categories preserves finite limits. -/
theorem ModuleExactFunctor.preservesFiniteLimits {R S : Type u} [Ring R] [Ring S]
    {F : ModuleCat.{u} R ⥤ ModuleCat.{u} S} [F.Additive] (hF : ModuleExactFunctor F) :
    Limits.PreservesFiniteLimits F :=
  have := hF.preservesHomology
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- An additive exact functor of module categories preserves finite colimits. -/
theorem ModuleExactFunctor.preservesFiniteColimits {R S : Type u} [Ring R] [Ring S]
    {F : ModuleCat.{u} R ⥤ ModuleCat.{u} S} [F.Additive] (hF : ModuleExactFunctor F) :
    Limits.PreservesFiniteColimits F :=
  have := hF.preservesHomology
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- A composite of additive functors is additive (with explicit arguments, for composites whose
middle categories agree only up to unfolding). -/
theorem additive_comp' {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive C]
    [Preadditive D] [Preadditive E] {F : C ⥤ D} {G : D ⥤ E} (hF : F.Additive)
    (hG : G.Additive) : (F ⋙ G).Additive :=
  inferInstance

/-! ### Partial standardization at a cut with a spectator -/

section Cut

variable {I k : Type u} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ)
  (θ β : Multiset I) (E : AlgCat.{u} k) (hQ : KLRSymm Q)

instance cutSpectFunctor_additive : (cutSpectFunctor Q Λ θ β E hQ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun z =>
    (congrArg (fun h => cutStandardMap Q Λ θ β h z)
      (LinearMap.ext fun _ => rfl : cutSpectInputHom Q Λ θ β (f.hom + g.hom) =
        cutSpectInputHom Q Λ θ β f.hom + cutSpectInputHom Q Λ θ β g.hom)).trans
      (cutStandardMap_add Q Λ θ β _ _ z))

end Cut

/-! ### Standardization in stages -/

section Singletons

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- The standardization in stages is additive. -/
theorem singStd_additive : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (singStd Q hQ n Λ θ E).Additive
  | 0, _, _, _ => inferInstanceAs (𝟭 _).Additive
  | n + 1, Λ, θ, E =>
    have := singStd_additive n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E))
    additive_comp' inferInstance (additive_comp' this (additive_comp' inferInstance
      (cutSpectFunctor_additive (a := n) (r := 1) Q Λ _ _ E hQ)))

instance (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) (E : AlgCat.{u} k) :
    (singStd Q hQ n Λ θ E).Additive :=
  singStd_additive Q hQ n Λ θ E

instance (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) :
    (singStandard Q hQ n Λ θ).Additive :=
  additive_comp' inferInstance (additive_comp' (singStd_additive Q hQ _ _ _ _) inferInstance)

instance (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) :
    Limits.PreservesFiniteLimits (singStandard Q hQ n Λ θ) :=
  (moduleExactFunctor_singStandard Q hQ n Λ θ).preservesFiniteLimits

instance (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) :
    Limits.PreservesFiniteColimits (singStandard Q hQ n Λ θ) :=
  (moduleExactFunctor_singStandard Q hQ n Λ θ).preservesFiniteColimits

end Singletons

/-! ### The partial standardization `S_+` of `λ⁺` -/

namespace CupCap

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)

section Plus

variable (θ β γ : Multiset I)

theorem plusStandardMap_add {N N' : Type*} [AddCommGroup N] [Module k N]
    [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
    [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N] [AddCommGroup N'] [Module k N']
    [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N']
    [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N']
    (g g' : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (z : PlusStandard Q Λ Λc j hj θ β γ N hQ) :
    plusStandardMap Q Λ Λc j hj θ β γ hQ (g + g') z =
      plusStandardMap Q Λ Λc j hj θ β γ hQ g z + plusStandardMap Q Λ Λc j hj θ β γ hQ g' z := by
  have hin : plusInputHom Q Λ Λc j hj θ β γ (g + g') =
      plusInputHom Q Λ Λc j hj θ β γ g + plusInputHom Q Λ Λc j hj θ β γ g' :=
    LinearMap.ext fun _ => rfl
  have hmid : blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
      (plusInputHom Q Λ Λc j hj θ β γ g + plusInputHom Q Λ Λc j hj θ β γ g') =
      blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ (plusInputHom Q Λ Λc j hj θ β γ g) +
        blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ (plusInputHom Q Λ Λc j hj θ β γ g') :=
    LinearMap.ext fun w => cutStandardMap_add Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
      β γ (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ (plusInputHom Q Λ Λc j hj θ β γ g))
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ (plusInputHom Q Λ Λc j hj θ β γ g')) w
  change cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
      (blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
        (plusInputHom Q Λ Λc j hj θ β γ (g + g'))) z = _
  rw [hin, hmid]
  exact cutStandardMap_add Q (plusBlockLabels Λ Λc j hj) θ (β + γ) _ _ z

instance plusStandardFunctor_additive :
    (plusStandardFunctor Q hQ Λ Λc j hj θ β γ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun z =>
    plusStandardMap_add Q hQ Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ f)
      (plusWrapHom Q Λ Λc j hj θ β γ g) z)

end Plus

variable (β : Multiset I) (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

instance : (plusOuterStd Q hQ Λ Λc j hj β θh θt).Additive :=
  additive_comp' (singStd_additive Q hQ _ _ _ _) (additive_comp' inferInstance
    (additive_comp' (singStd_additive Q hQ _ _ _ _) inferInstance))

instance : (plusStagedStd Q hQ Λ Λc j hj β θh θt).Additive :=
  additive_comp' inferInstance (plusStandardFunctor_additive Q hQ Λ Λc j hj _ β _)

instance : Limits.PreservesFiniteLimits (plusStagedStd Q hQ Λ Λc j hj β θh θt) :=
  (moduleExactFunctor_plusStagedStd Q hQ Λ Λc j hj β θh θt).preservesFiniteLimits

instance : Limits.PreservesFiniteColimits (plusStagedStd Q hQ Λ Λc j hj β θh θt) :=
  (moduleExactFunctor_plusStagedStd Q hQ Λ Λc j hj β θh θt).preservesFiniteColimits

end CupCap

end Categorification.Stendhal
