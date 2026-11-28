/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqBlocks
import Categorification.TwoRep.MateNat

/-!
# The mixed mate of the induction crossing as a Beck–Chevalley map of restrictions

Brundan, arXiv:1501.00350v1, (1.7), for Webster's functors on right `T^λ`-modules
(arXiv:1309.3796v3, §4.6, Theorem 4.31). The crossing `indCrossOfEq : Fⱼ Fᵢ ⟶ Fᵢ Fⱼ` of
inductions is the conjugate of the crossing `resCrossOfEq` of restrictions through the composite
adjunctions. Its mate through `Fᵢ ⊣ Eᵢ`, the mixed sideways crossing `Eᵢ Fⱼ ⟶ Fⱼ Eᵢ` of
`BlackModuleMixedInversion`, is therefore the mate of `resCrossOfEq` through `Fⱼ ⊣ Eⱼ` in the
other direction (`indCrossOfEq_mixedMate`, from Mathlib's
`iterated_mateEquiv_conjugateEquiv`): the Beck–Chevalley map
`Fⱼ Eᵢ ⟶ Fⱼ Eᵢ EⱼFⱼ ⟶ Fⱼ Eⱼ Eᵢ Fⱼ ⟶ Eᵢ Fⱼ` built from the unit of `Fⱼ ⊣ Eⱼ`, the restriction
crossing (right multiplication by the mixed crossing element for `i ≠ j`) and the counit.

`mateNat_eq_mateEquiv` identifies the library's `TwoRep.mateNat` with Mathlib's `mateEquiv`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR TwoRep

section Generic

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  {L₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} {G : 𝒜 ⥤ 𝒞} {L₂ : 𝒞 ⥤ 𝒟} {R₂ : 𝒟 ⥤ 𝒞} {H : ℬ ⥤ 𝒟}

/-- `TwoRep.mateNat` is Mathlib's `mateEquiv`. -/
theorem mateNat_eq_mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H) :
    mateNat adj₂.unit τ adj₁.counit = (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ τ)).natTrans := by
  ext Y
  simp [mateNat_app]

end Generic

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

/-- **The mixed mate of the induction crossing is the Beck–Chevalley map of the restriction
crossing**: the mate through `Fᵢ ⊣ Eᵢ` of `indCrossOfEq` is the inverse mate through `Fⱼ ⊣ Eⱼ`
of `resCrossOfEq`. -/
theorem indCrossOfEq_mixedMate (hsym : KLRSymm Q) (i j : I) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    mateNat (blackAdjOfEq Q Λ i h₂).unit (indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄)
        (blackAdjOfEq Q Λ i h₃).counit =
      ((mateEquiv (blackAdjOfEq Q Λ j h₄) (blackAdjOfEq Q Λ j h₁)).symm
        (TwoSquare.mk _ _ _ _ (resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄))).natTrans := by
  rw [mateNat_eq_mateEquiv]
  congr 1
  rw [Equiv.eq_symm_apply]
  ext1
  rw [iterated_mateEquiv_conjugateEquiv, indCrossOfEq, Equiv.apply_symm_apply]

/-- **Mixed inversion on modules from the restriction crossing**: the mate of `indCrossOfEq` is
invertible as soon as the Beck–Chevalley map of `resCrossOfEq` through `Fⱼ ⊣ Eⱼ` is. -/
theorem isIso_indCrossOfEq_mixedMate (hsym : KLRSymm Q) (i j : I) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ)
    (h : IsIso ((mateEquiv (blackAdjOfEq Q Λ j h₄) (blackAdjOfEq Q Λ j h₁)).symm
        (TwoSquare.mk _ _ _ _ (resCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄))).natTrans) :
    IsIso (mateNat (blackAdjOfEq Q Λ i h₂).unit (indCrossOfEq Λ hsym i j h₁ h₂ h₃ h₄)
        (blackAdjOfEq Q Λ i h₃).counit) := by
  rw [indCrossOfEq_mixedMate]
  exact h

end Categorification.Stendhal
