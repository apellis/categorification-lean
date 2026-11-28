/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PlusStagedTensorRepresented
import Categorification.WeightedKLR.RedStrands.CutStandardProjective

/-!
# The standard bimodules are finitely generated projective over the block algebras

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 and §7.3
(proof of Lemma 7.19). The standardization with singleton blocks (`singStd`, `singStandard`)
and the partial standardization `S_+ = plusStagedStd` of `λ⁺` are tensoring with their values
on the regular module, and these bimodules are finitely generated projective as right modules
over the block algebras (`isFinProj_singStd`, `isFinProj_singStandard`,
`isFinProj_plusStagedStd`). This is the projectivity part of the standard basis of a partial
standardization: each stage is a restriction of scalars along a ring map, whose bimodule is free
of rank one, or a partial standardization at a cut, whose bimodule is `⊕_u ε_u D` by the
shuffle decomposition (`CutStandardPresented.isFinProj`), and finite projectivity is closed
under composition (`TensorRepresented.IsFinProj.comp`).

## Main results

* `Stendhal.cutSpectPresented`: the partial standardization at a cut with a spectator is
  presented by a partial standardization at a cut.
* `Stendhal.isFinProj_singStd`, `Stendhal.isTensorRepresented_singStandard`,
  `Stendhal.isFinProj_singStandard`.
* `Stendhal.CupCap.isFinProj_plusStandardFunctor`, `Stendhal.CupCap.isFinProj_plusStagedStd`.
-/

universe u

noncomputable section

namespace Categorification

open CategoryTheory TensorRepresented

/-- `IsFinProj.comp`, with the additivity of the factors given explicitly. -/
theorem isFinProj_comp {A B C : Type u} [Ring A] [Ring B] [Ring C]
    {F : ModuleCat.{u} B ⥤ ModuleCat.{u} A} {G : ModuleCat.{u} A ⥤ ModuleCat.{u} C}
    (iF : F.Additive) (iG : G.Additive) (hG : IsTensorRepresented G) (hFp : IsFinProj F)
    (hGp : IsFinProj G) :
    @IsFinProj _ _ _ _ (F ⋙ G) (Stendhal.additive_comp' iF iG) :=
  IsFinProj.comp hG hFp hGp

/-- Finite projectivity of the representing bimodule, transported along an equality of
functors. -/
theorem isFinProj_of_eq {A B : Type u} [Ring A] [Ring B]
    {F G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [G.Additive] (h : G = F) (hFa : F.Additive)
    (hF : IsFinProj F) : IsFinProj G := by
  subst h
  exact hF

namespace Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-! ### The partial standardization at a cut with a spectator -/

section Spect

variable {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I) (E : AlgCat.{u} k)

/-- The inclusion `D → D ⊗ E` of the factor algebra of the cut. -/
def cutSpectIncl :=
  cutAlgHom Q Λ θ β (R := cutSpectAlgebra Q Λ θ β E)
    (show cutFactorAlgebra Q Λ θ β →ₐ[k] cutSpectAlgebra Q Λ θ β E from
      Algebra.TensorProduct.includeLeft)

/-- The input of the partial standardization with a spectator, as a restriction along the
inclusion `D → D ⊗ E`. -/
def cutSpectRestrEquiv (Z : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E)) :
    CutSpectInput Q Λ θ β E Z ≃ₗ[cutFactorAlgebra Q Λ θ β]
      CutRestr (R := cutSpectAlgebra Q Λ θ β E) Q Λ θ β (cutSpectIncl Q Λ θ β E) Z where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem cutSpect_smul_aux (Z : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E)) (c : k)
    (x : CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E Z)) :
    cutStandardMap Q Λ θ β (cutSpectRestrEquiv Q Λ θ β E Z).toLinearMap
      (cutSpectStandardAction Q Λ θ β E Z hQ
        (algebraMap k (TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E) c) x) =
      c • cutStandardMap Q Λ θ β (cutSpectRestrEquiv Q Λ θ β E Z).toLinearMap x := by
  rw [AlgHom.commutes]
  exact map_smul (cutStandardMap Q Λ θ β (cutSpectRestrEquiv Q Λ θ β E Z).toLinearMap) c x

/-- **The partial standardization at a cut with a spectator is presented by the partial
standardization at the cut** of the restriction along `D → D ⊗ E`. -/
def cutSpectPresented :
    CutStandardPresented (R := cutSpectAlgebra Q Λ θ β E) Q Λ θ β (cutSpectIncl Q Λ θ β E)
      (cutSpectFunctor Q Λ θ β E hQ) where
  equiv Z := (cutStandardMapEquiv Q Λ θ β (cutSpectRestrEquiv Q Λ θ β E Z)).toAddEquiv
  map {Z Z'} g x := by
    have h : (cutSpectRestrEquiv Q Λ θ β E Z').toLinearMap ∘ₗ cutSpectInputHom Q Λ θ β g.hom =
        cutRestrHom (R := cutSpectAlgebra Q Λ θ β E) Q Λ θ β (cutSpectIncl Q Λ θ β E) g.hom ∘ₗ
          (cutSpectRestrEquiv Q Λ θ β E Z).toLinearMap := LinearMap.ext fun _ => rfl
    exact (cutStandardMap_comp Q Λ θ β _ (cutSpectRestrEquiv Q Λ θ β E Z').toLinearMap
      x).symm.trans ((congrArg (fun f => cutStandardMap Q Λ θ β f x) h).trans
        (cutStandardMap_comp Q Λ θ β (cutSpectRestrEquiv Q Λ θ β E Z).toLinearMap _ x))
  smul Z c x := cutSpect_smul_aux Q hQ Λ θ β E Z c x

/-- The bimodule of the partial standardization at a cut with a spectator is finitely
generated projective over `D ⊗ E`. -/
theorem isFinProj_cutSpectFunctor : IsFinProj (cutSpectFunctor Q Λ θ β E hQ) :=
  (cutSpectPresented Q hQ Λ θ β E).isFinProj hQ

end Spect

/-! ### The standardization with singleton blocks -/

/-- **The bimodule of the standardization in stages is finitely generated projective** over
the algebra of the singleton blocks and the spectator. -/
theorem isFinProj_singStd : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) →
    (θ : Fin n → Multiset I) → (E : AlgCat.{u} k) →
    IsFinProj (singStd Q hQ n Λ θ E)
  | 0, _, _, _ => isFinProj_id
  | n + 1, Λ, θ, E => by
    refine isFinProj_of_eq (singStd.eq_2 Q hQ E n Λ θ) ?a ?b
    case b =>
      exact isFinProj_comp _ _
        (isTensorRepresented_comp (singStd_additive Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
            (AlgCat.of k (singLast Q Λ θ ⊗[k] E))) _
          (isTensorRepresented_singStd Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
            (AlgCat.of k (singLast Q Λ θ ⊗[k] E)))
          (isTensorRepresented_comp _ (cutSpectFunctor_additive (a := n) (r := 1) Q Λ
              (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ)
            (isTensorRepresented_restrictScalars _)
            (isTensorRepresented_cutSpectFunctor _ _ _ _ _ hQ)))
        (isFinProj_restrictScalars _)
        (isFinProj_comp (singStd_additive Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
            (AlgCat.of k (singLast Q Λ θ ⊗[k] E))) _
          (isTensorRepresented_comp _ (cutSpectFunctor_additive (a := n) (r := 1) Q Λ
              (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ)
            (isTensorRepresented_restrictScalars _)
            (isTensorRepresented_cutSpectFunctor _ _ _ _ _ hQ))
          (isFinProj_singStd n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
            (AlgCat.of k (singLast Q Λ θ ⊗[k] E)))
          (isFinProj_comp _ (cutSpectFunctor_additive (a := n) (r := 1) Q Λ
              (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ)
            (isTensorRepresented_cutSpectFunctor _ _ _ _ _ hQ)
            (isFinProj_restrictScalars _)
            (isFinProj_cutSpectFunctor Q hQ Λ _ _ E)))

/-- **The standardization with singleton blocks is tensoring with a bimodule.** -/
theorem isTensorRepresented_singStandard (n : ℕ) (Λ : Fin n → I →₀ ℕ)
    (θ : Fin n → Multiset I) : IsTensorRepresented (singStandard Q hQ n Λ θ) :=
  isTensorRepresented_comp _ (additive_comp' (singStd_additive Q hQ _ _ _ _) inferInstance)
    (isTensorRepresented_restrictScalars _)
    (isTensorRepresented_comp (singStd_additive Q hQ _ _ _ _) _
      (isTensorRepresented_singStd Q hQ _ _ _ _) (isTensorRepresented_restrictScalars _))

/-- **The bimodule `S_α` of the standardization with singleton blocks is finitely generated
projective** over the algebra `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n)` of the blocks. -/
theorem isFinProj_singStandard (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) :
    IsFinProj (singStandard Q hQ n Λ θ) :=
  isFinProj_comp _ (additive_comp' (singStd_additive Q hQ _ _ _ _) inferInstance)
    (isTensorRepresented_comp (singStd_additive Q hQ _ _ _ _) _
      (isTensorRepresented_singStd Q hQ _ _ _ _) (isTensorRepresented_restrictScalars _))
    (isFinProj_restrictScalars _)
    (isFinProj_comp (singStd_additive Q hQ _ _ _ _) _ (isTensorRepresented_restrictScalars _)
      (isFinProj_singStd Q hQ _ _ _ _) (isFinProj_restrictScalars _))

/-! ### The partial standardization `S_+` of `λ⁺` -/

namespace CupCap

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)

/-- The bimodule of the partial standardization of `λ⁺` with three blocks is finitely
generated projective over the algebra of the three blocks. -/
theorem isFinProj_plusStandardFunctor (θ β γ : Multiset I) :
    IsFinProj (plusStandardFunctor Q hQ Λ Λc j hj θ β γ) :=
  IsFinProj.of_iso (plusStandardFunctorIso Q hQ Λ Λc j hj θ β γ).symm
    (isFinProj_comp (plusMidFunctor_additive Q hQ Λ Λc j hj θ β γ)
      (cutStandardFunctor_additive Q hQ (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusRelabel Q Λ Λc j hj θ β γ))
      (isTensorRepresented_cutStandardFunctor Q hQ (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusRelabel Q Λ Λc j hj θ β γ))
      ((plusMidPresented Q hQ Λ Λc j hj θ β γ).isFinProj hQ)
      ((cutStandardFunctorPresented Q hQ (plusBlockLabels Λ Λc j hj) θ (β + γ)
        (plusRelabel Q Λ Λc j hj θ β γ)).isFinProj hQ))

variable (β : Multiset I) (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

/-- The bimodule of the standardizations of the first and of the last block of `S_+` is finitely
generated projective. -/
theorem isFinProj_plusOuterStd : IsFinProj (plusOuterStd Q hQ Λ Λc j hj β θh θt) :=
  isFinProj_comp (singStd_additive Q hQ _ _ _ _) _
    (isTensorRepresented_comp _ (additive_comp' (singStd_additive Q hQ _ _ _ _) inferInstance)
      (isTensorRepresented_restrictScalars _)
      (isTensorRepresented_comp (singStd_additive Q hQ _ _ _ _) _
        (isTensorRepresented_singStd Q hQ _ _ _ _) (isTensorRepresented_restrictScalars _)))
    (isFinProj_singStd Q hQ _ _ _ _)
    (isFinProj_comp _ (additive_comp' (singStd_additive Q hQ _ _ _ _) inferInstance)
      (isTensorRepresented_comp (singStd_additive Q hQ _ _ _ _) _
        (isTensorRepresented_singStd Q hQ _ _ _ _) (isTensorRepresented_restrictScalars _))
      (isFinProj_restrictScalars _)
      (isFinProj_comp (singStd_additive Q hQ _ _ _ _) _ (isTensorRepresented_restrictScalars _)
        (isFinProj_singStd Q hQ _ _ _ _) (isFinProj_restrictScalars _)))

/-- **The bimodule `S^+` of the partial standardization `S_+` of `λ⁺` is finitely generated
projective** over the algebra of its blocks. -/
theorem isFinProj_plusStagedStd : IsFinProj (plusStagedStd Q hQ Λ Λc j hj β θh θt) :=
  isFinProj_comp inferInstance
    (plusStandardFunctor_additive Q hQ Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt))
    (isTensorRepresented_plusStandardFunctor Q hQ Λ Λc j hj _ β _)
    (isFinProj_plusOuterStd Q hQ Λ Λc j hj β θh θt)
    (isFinProj_plusStandardFunctor Q hQ Λ Λc j hj _ β _)

end CupCap

end Stendhal

end Categorification
